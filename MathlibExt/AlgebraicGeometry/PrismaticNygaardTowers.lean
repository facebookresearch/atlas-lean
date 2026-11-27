/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PrismaticNygaardModels
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Actual Nygaard quotients, signed module powers and their Milnor fibers

Discrete Nygaard is the literal inverse image of the actual ideal power
under delta Frobenius. Every finite quotient and transition is native.
Signed powers use ordinary tensor powers and the native module dual.

A completed tower is the actual Milnor fiber of its adjacent quotient
maps. Its filtration is the actual fiber of the finite-level projection.
Invertibility is a finite Nygaard-quotient property; no unfiltered inverse
of the inverse-limit object is inferred from it.

References: Bhatt--Scholze, arXiv:1905.08229v4, Sections 12 and 15;
Bhatt--Morrow--Scholze, arXiv:1802.03261v2, Theorem 1.12(3),
including footnote 3, and Sections 6.2 and 7.4.
The twist seed and divided Frobenius normalization are separate outputs.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrismaticNygaardTowers

open CategoryTheory CategoryTheory.Limits
open MathlibExt.RingTheory MathlibExt.RingTheory.BoundedPrisms
open PrismaticNygaardModels
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime]
variable (A : Type) [CommRing A] [DeltaRing p A] (I : Ideal A)

/-- The actual absolute Nygaard ideal in the fixed delta ring. -/
abbrev nygaardIdeal (n : ℕ) : Ideal A := absoluteNygaard p A I n

/-- Nygaard is genuinely decreasing, including its zero boundary. -/
theorem nygaard_antitone : Antitone (nygaardIdeal p A I) := by
  intro i j hij x hx
  exact I.pow_le_pow_right hij hx

/-- Every finite quotient starts at N >= 1, as in the filtered-invertibility statement. -/
abbrev QuotientRing (n : ℕ) := A ⧸ nygaardIdeal p A I (n + 1)

/-- The adjacent quotient map is induced by the actual ideal inclusion. -/
def quotientTransition (n : ℕ) : QuotientRing p A I (n + 1) →+* QuotientRing p A I n :=
  Ideal.Quotient.factor (nygaard_antitone p A I (Nat.le_succ (n + 1)))

@[simp] theorem quotientTransition_mk (n : ℕ) (a : A) :
    quotientTransition p A I n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl

variable {p A I}
variable (R : Type) [CommRing R] [Algebra R A]
variable (p A I)

/-- The quotient carries the actual displayed base coefficient map. -/
def quotientScalars (n : ℕ) : R →+* QuotientRing p A I n :=
  (Ideal.Quotient.mk _).comp (algebraMap R A)

/-- Coefficient restriction of the real adjacent quotient map. -/
def quotientTransitionLinear (n : ℕ) :
    QuotientRing p A I (n + 1) →ₗ[R] QuotientRing p A I n where
  toFun := quotientTransition p A I n
  map_add' := map_add _
  map_smul' a x := by
    simp only [RingHom.id_apply, Algebra.smul_def, map_mul]
    rfl

/-- The actual ordered tensor word of an ordinary module. -/
def tensorPower (M : ModuleCat.{0} R) : ℕ → ModuleCat.{0} R
  | 0 => ModuleCat.of R R
  | n + 1 => ModuleCat.of R (M ⊗[R] tensorPower M n)

/-- Signed weights use the native dual, rather than truncated natural subtraction. -/
def signedPower (M : ModuleCat.{0} R) (i : ℤ) : ModuleCat.{0} R :=
  if 0 ≤ i then tensorPower R M i.toNat
    else tensorPower R (ModuleCat.of R (Module.Dual R M)) (-i).toNat

/-- The literal scalar extension of the signed seed to the actual finite Nygaard quotient. -/
abbrev FiniteTwist (M : ModuleCat.{0} R) (n : ℕ) (i : ℤ) :=
  (QuotientRing p A I n) ⊗[R] signedPower R M i

/-- Adjacent twist maps retain every coefficient and every signed seed element. -/
def twistTransition (M : ModuleCat.{0} R) (n : ℕ) (i : ℤ) :
    FiniteTwist p A I R M (n + 1) i →ₗ[R]
      FiniteTwist p A I R M n i :=
  TensorProduct.map (quotientTransitionLinear p A I R n) LinearMap.id

@[simp] theorem twistTransition_tmul (M : ModuleCat.{0} R) (n : ℕ) (i : ℤ)
    (a : QuotientRing p A I (n + 1)) (x : signedPower R M i) :
    twistTransition p A I R M n i (a ⊗ₜ[R] x) =
      (quotientTransition p A I n a) ⊗ₜ[R] x := by
  simp [twistTransition, quotientTransitionLinear]

/-- The actual finite twist as an integer module in the site universe. -/
def twistModule (M : ModuleCat.{0} R) (n : ℕ) (i : ℤ) : ModuleCat.{1} ℤ :=
  (ModuleCat.uliftFunctor.{1, 0} ℤ).obj
    (ModuleCat.of ℤ (FiniteTwist p A I R M n i))

/-- The same actual transition after fixed integer-scalar restriction and universe lift. -/
def twistModuleTransition (M : ModuleCat.{0} R) (n : ℕ) (i : ℤ) :
    twistModule p A I R M (n + 1) i ⟶ twistModule p A I R M n i :=
  (ModuleCat.uliftFunctor.{1, 0} ℤ).map
    (ModuleCat.ofHom ((twistTransition p A I R M n i).restrictScalars ℤ))

/-- Finite quotient complexes, genuinely concentrated in cohomological degree zero. -/
def levelComplex (M : ModuleCat.{0} R) (i : ℤ) (n : ℕ) :
    CochainComplex (ModuleCat.{1} ℤ) ℤ :=
  (HomologicalComplex.single (ModuleCat.{1} ℤ) (ComplexShape.up ℤ) 0).obj
    (twistModule p A I R M n i)

/-- Adjacent cochain maps retain the actual finite quotient transition. -/
def levelTransition (M : ModuleCat.{0} R) (i : ℤ) (n : ℕ) :
    levelComplex p A I R M i (n + 1) ⟶ levelComplex p A I R M i n :=
  (HomologicalComplex.single (ModuleCat.{1} ℤ) (ComplexShape.up ℤ) 0).map
    (twistModuleTransition p A I R M n i)

/-- The literal product complex of the actual quotient tower. -/
abbrev productComplex (M : ModuleCat.{0} R) (i : ℤ) :=
  ∏ᶜ (levelComplex p A I R M i)

/-- The Milnor difference is projection n minus transition after projection n+1. -/
def difference (M : ModuleCat.{0} R) (i : ℤ) :
    productComplex p A I R M i ⟶ productComplex p A I R M i :=
  Pi.lift (fun n ↦ Pi.π (levelComplex p A I R M i) n -
    Pi.π (levelComplex p A I R M i) (n + 1) ≫ levelTransition p A I R M i n)

@[simp] theorem difference_projection (M : ModuleCat.{0} R) (i : ℤ) (n : ℕ) :
    difference p A I R M i ≫ Pi.π (levelComplex p A I R M i) n =
      Pi.π (levelComplex p A I R M i) n -
        Pi.π (levelComplex p A I R M i) (n + 1) ≫ levelTransition p A I R M i n :=
  Pi.lift_comp_π _ _

/-- The actual complete signed twist; mappingCocone is cone(difference)[-1]. -/
def completeComplex (M : ModuleCat.{0} R) (i : ℤ) :
    CochainComplex (ModuleCat.{1} ℤ) ℤ :=
  CochainComplex.mappingCocone (difference p A I R M i)

/-- Its canonical finite-quotient projection, with the native fiber sign. -/
def projection (M : ModuleCat.{0} R) (i : ℤ) (n : ℕ) :
    completeComplex p A I R M i ⟶ levelComplex p A I R M i n :=
  CochainComplex.mappingCocone.fst (difference p A I R M i) ≫
    Pi.π (levelComplex p A I R M i) n

/-- N >= n+1 of the completed twist is the literal homotopy fiber of the quotient projection. -/
def filteredComplex (M : ModuleCat.{0} R) (i : ℤ) (n : ℕ) :
    CochainComplex (ModuleCat.{1} ℤ) ℤ :=
  CochainComplex.mappingCocone (projection p A I R M i n)

/-- The actual filtration inclusion, never an unrelated filtered group map. -/
def filteredInclusion (M : ModuleCat.{0} R) (i : ℤ) (n : ℕ) :
    filteredComplex p A I R M i n ⟶ completeComplex p A I R M i :=
  CochainComplex.mappingCocone.fst (projection p A I R M i n)

/-- Signed Nygaard boundaries retain the whole complex at all nonpositive levels. -/
def nygaardComplex (M : ModuleCat.{0} R) (i n : ℤ) :
    CochainComplex (ModuleCat.{1} ℤ) ℤ :=
  if 0 < n then filteredComplex p A I R M i (n.toNat - 1)
    else completeComplex p A I R M i

/-- The canonical map from a signed Nygaard step to its actual complete twist. -/
def nygaardInclusion (M : ModuleCat.{0} R) (i n : ℤ) :
    nygaardComplex p A I R M i n ⟶ completeComplex p A I R M i :=
by
  by_cases h : 0 < n
  · simp only [nygaardComplex, ite_eq_left h]
    exact filteredInclusion p A I R M i (n.toNat - 1)
  · simp only [nygaardComplex, ite_eq_right h]
    exact 𝟙 _

end MathlibExt.AlgebraicGeometry.PrismaticNygaardTowers
