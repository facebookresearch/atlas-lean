/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicGeometricClassifyingSpaces
public import MathlibExt.AlgebraicGeometry.MotivicBocksteinModels
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Actual unit, minus-one and root classes

A unit defines the original character of the exponent lattice, its
native group-algebra evaluation and the corresponding Spec point of
G_m. Its motivic class is the pullback of the already fixed sigma_t.
Rho is this actual minus-one class followed by coefficient reduction.

The low-weight root comparison has the fixed native integral Bockstein
and the same unit-class map. Tau is the inverse image of the actual
root -1 in mu_2; it is not a freely chosen scalar coefficient.

Source: Voevodsky, arXiv:math/0107109v1, Theorem 6.16 and Section 9;
the canonical unit class follows the native torus-cycle source.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicUnitRootClasses

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels NisnevichTransferModels
open MotivicStandardSchemes EffectiveMotivicComplexModels PointedMotivicModels
open PointedMotivicQuotients ReducedMotivicCohomologyModels MotivicTorusClassModels
open MotivicBocksteinModels

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
  {P : SmoothProductSystem k} (A : StandardSchemes P)
  {E : ExternalSystem P} {C : CorrespondenceProductModel D G P E}
  {R₀ : RepresentableSystem D G} {S₀ : TransferSheafificationModel D G}

/-- The original exponent-lattice character of a genuine unit. -/
def unitExponentCharacter (u : kˣ) : Multiplicative (Fin 1 → ℤ) →* kˣ where
  toFun v := u ^ (Multiplicative.toAdd v) 0
  map_one' := by change u ^ (0 : ℤ) = 1; simp
  map_mul' v w := by
    change u ^ ((Multiplicative.toAdd v) 0 + (Multiplicative.toAdd w) 0) = _
    rw [zpow_add]

/-- Native coefficient-preserving group-algebra evaluation on that same unit. -/
def unitTorusEvaluation (u : kˣ) : torusRing k 1 →ₐ[k] k :=
  AddMonoidAlgebra.lift k k (Fin 1 → ℤ) ((Units.coeHom k).comp (unitExponentCharacter u))

/-- The actual G_m point, transported through the original standard-torus source iso. -/
def unitTorusPoint (u : kˣ) : P.unit ⟶ A.torus 1 :=
  Over.homMk (P.unitIso.hom ≫ Spec.map (CommRingCat.ofHom (unitTorusEvaluation u).toRingHom) ≫
    (A.torusIso 1).inv) (by
      rw [A.torus_base]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      have hc : CommRingCat.ofHom (algebraMap k (torusRing k 1)) ≫
          CommRingCat.ofHom (unitTorusEvaluation u).toRingHom = 𝟙 (CommRingCat.of k) := by
        ext c
        exact (unitTorusEvaluation u).commutes c
      rw [← Spec.map_comp, hc, Spec.map_id, Category.comp_id, P.unit_base])

/-- The same point in G_m with its original point-one quotient. -/
def unitPointedMap (u : kˣ) : representedPointed P.unit ⟶ pointedTorus (P := P) (A := A) :=
  representedMap (unitTorusPoint A u) ≫
    cofiberQuotient (representedMap (torusPoint (P := P) (A := A)))

variable {T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R₀)}
  (N : NisTensorSystem k) [N.functor.Additive] [∀ H, (N.functor.obj H).Additive]
  (B : CoefficientComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R₀) (S := S₀) T N)
  (F : ReducedFreeNisSystem k)
  (L : TorusCycleLinearization (S := S₀) T F)
  (Z : IntegerCoefficientInclusions (N := N) (T := T) (B := B))

/-- The actual unit class is native pullback of the canonical sigma_t. -/
def unitClass (u : kˣ) :
    ReducedCohomology B F (representedPointed P.unit) 1 1 integerCoefficients :=
  ReducedMotivicCohomologyModels.pullback B F (unitPointedMap A u) 1 1 integerCoefficients
    (torusClass T F N B L Z)

/-- Integral rho is the actual class of minus one. -/
def integralRho : ReducedCohomology B F (representedPointed P.unit) 1 1 integerCoefficients :=
  unitClass A N B F L Z (-1)

/-- Mod-ell rho is its original integer coefficient reduction. -/
def rho (ell : ℕ) : ReducedCohomology B F (representedPointed P.unit) 1 1 (ModCoefficients ell) :=
  ReducedMotivicCohomologyModels.coefficientMap B F (representedPointed P.unit) 1 1
    (integralReduction ell) (integralRho A N B F L Z)

/-- The root carrier consists of actual units whose original ell-th power is one. -/
abbrev UnitRoots (ell : ℕ) := {u : kˣ // u ^ ell = 1}

/-- The low-weight dictionary uses this same coefficient boundary and native unit-class map. -/
structure RootClassSource (ell : ℕ)
    (I : CoefficientConeSource B (integralSequence ell) (1 : ℤ)) where
  roots : ReducedCohomology B F (representedPointed P.unit) 0 1 (ModCoefficients ell) ≃
    UnitRoots (k := k) ell
  boundary : ∀ x : ReducedCohomology B F (representedPointed P.unit) 0 1 (ModCoefficients ell),
    integralBockstein B ell F (representedPointed P.unit) 0 1 I x =
      unitClass A N B F L Z (roots x).val

/-- Tau is the actual minus-one root through the source-normalized low-weight dictionary. -/
def tau (I : CoefficientConeSource B (integralSequence 2) (1 : ℤ))
    (C : RootClassSource A N B F L Z 2 I) :
    ReducedCohomology B F (representedPointed P.unit) 0 1 (ModCoefficients 2) :=
  C.roots.symm ⟨-1, by simp⟩

omit [N.functor.Additive] [∀ H, (N.functor.obj H).Additive] in
/-- Its integral boundary is proved to be the native minus-one unit class. -/
theorem tau_boundary (I : CoefficientConeSource B (integralSequence 2) (1 : ℤ))
    (C : RootClassSource A N B F L Z 2 I) :
    integralBockstein B 2 F (representedPointed P.unit) 0 1 I (tau A N B F L Z I C) =
      integralRho A N B F L Z := by
  simpa only [tau, integralRho, Equiv.apply_symm_apply] using C.boundary (tau A N B F L Z I C)

end MathlibExt.AlgebraicGeometry.MotivicUnitRootClasses
