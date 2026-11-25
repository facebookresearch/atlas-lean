/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LocalWittCoefficientFields
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Lemmas

/-!
# Actual residue-degree Frobenius on relative ramified Witt coefficients

Prime Frobenius is literal p-th power on each actual perfect residue
test, including the zero ring. Its residue-degree iterate is q-th power,
where q is the actual cardinality of E's residue field. Thus it fixes
that residue field, and its Witt lift is linear over W(k). Ramified
coefficient restriction applies this actual Witt lift and fixes O_E.

Source: Fargues--Scholze, arXiv:2102.13459v4, Sections I.2 and II.1.
This is the q-Frobenius of the relative curve, with the actual coefficient
field and uniformizer retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.RelativeWittFrobenius

open _root_.CategoryTheory
open LocalWittCoefficientFields RelativeWittLoopTests

variable (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]

/-- Actual prime Frobenius, retaining the empty test-ring boundary. -/
@[irreducible]
def primeFrobenius (R : PerfectAlgebra p k) : R.obj →+* R.obj := by
  classical
  by_cases h : Subsingleton R.obj
  · exact RingHom.id _
  · letI : Nontrivial R.obj := not_subsingleton_iff_nontrivial.mp h
    letI : CharP R.obj p :=
      (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr R.property.1
    exact frobenius R.obj p

/-- Every original ring element has its actual p-th power. -/
theorem primeFrobenius_apply (R : PerfectAlgebra p k) (a : R.obj) :
    primeFrobenius p k R a = a ^ p := by
  unfold primeFrobenius
  split
  · exact Subsingleton.elim _ _
  · rfl

/-- The actual residue-degree iterate, prior to choosing a local-field dictionary. -/
def iteratedFrobenius (R : PerfectAlgebra p k) (f : ℕ) : R.obj →+* R.obj :=
  (primeFrobenius p k R) ^ f

/-- The whole iterate is literal p-power-degree Frobenius. -/
theorem iteratedFrobenius_apply (R : PerfectAlgebra p k) (f : ℕ) (a : R.obj) :
    iteratedFrobenius p k R f a = a ^ (p ^ f) := by
  induction f generalizing a with
  | zero => simp [iteratedFrobenius]
  | succ n ih =>
    rw [iteratedFrobenius, pow_succ]
    change (primeFrobenius p k R ^ n) (primeFrobenius p k R a) = a ^ (p ^ (n+1))
    change iteratedFrobenius p k R n (primeFrobenius p k R a) = _
    rw [ih, primeFrobenius_apply, ← pow_mul, Nat.pow_succ, Nat.mul_comm p]

/-- Every iterate is bijective on the actual perfect residue test. -/
theorem iteratedFrobenius_bijective (R : PerfectAlgebra p k) (f : ℕ) :
    Function.Bijective (iteratedFrobenius p k R f) := by
  have h : Function.Bijective (primeFrobenius p k R) := by
    convert R.property.2 using 1
    ext a
    exact primeFrobenius_apply p k R a
  induction f with
  | zero => exact Function.bijective_id
  | succ n ih =>
    change Function.Bijective (((primeFrobenius p k R) ^ (n+1) : R.obj →+* R.obj) :
      R.obj → R.obj)
    rw [pow_succ]
    exact ih.comp h

variable {k}
variable {E : MixedField p} (C : CoefficientData p E)
  (R : PerfectAlgebra p (Residue p E))

/-- The q-Frobenius fixes every actual base-residue coefficient. -/
theorem residue_scalar_fixed (a : Residue p E) :
    iteratedFrobenius p (Residue p E) R C.residueDegree (algebraMap _ _ a) =
      algebraMap _ _ a := by
  let : Fintype (Residue p E) := Fintype.ofFinite _
  rw [iteratedFrobenius_apply, ← C.residue_card, ← map_pow]
  exact congrArg (algebraMap _ _) (by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card a)

/-- The actual scalar-linear q-Frobenius morphism of the residue test. -/
def frobeniusTest : R ⟶ R :=
  ObjectProperty.homMk (CommAlgCat.ofHom
    { __ := iteratedFrobenius p (Residue p E) R C.residueDegree
      commutes' := residue_scalar_fixed p C R })

/-- The actual residue-degree Frobenius algebra equivalence. -/
def frobeniusAlgebraEquiv : R.obj ≃ₐ[Residue p E] R.obj where
  __ := RingEquiv.ofBijective (iteratedFrobenius p (Residue p E) R C.residueDegree)
    (iteratedFrobenius_bijective p (Residue p E) R C.residueDegree)
  commutes' := residue_scalar_fixed p C R

/-- Its genuine isomorphism of the original perfect residue test. -/
def frobeniusTestIso : R ≅ R :=
  ObjectProperty.isoMk _ (CommAlgCat.isoMk (frobeniusAlgebraEquiv p C R))

/-- The original ramified Witt q-Frobenius fixes the actual O_E factor. -/
def ramifiedFrobenius : RamifiedWitt p C R →+* RamifiedWitt p C R :=
  ramifiedMap p C (frobeniusTest p C R)

/-- The ramified period Frobenius equivalence applies the actual Witt functor to the test iso. -/
def ramifiedFrobeniusEquiv : RamifiedWitt p C R ≃+* RamifiedWitt p C R := by
  letI := coefficientAlgebra p C
  let e := frobeniusTestIso p C R
  exact
    { __ := integralMap p (Residue p E) (Integers p E) e.hom
      invFun := integralMap p (Residue p E) (Integers p E) e.inv
      left_inv := by
        intro a
        have h := integralMap_comp p (Residue p E) (Integers p E) e.hom e.inv
        rw [e.hom_inv_id, integralMap_id] at h
        exact (RingHom.congr_fun h a).symm
      right_inv := by
        intro a
        have h := integralMap_comp p (Residue p E) (Integers p E) e.inv e.hom
        rw [e.inv_hom_id, integralMap_id] at h
        exact (RingHom.congr_fun h a).symm }

/-- Frobenius retains every original local-field integer coefficient. -/
theorem ramifiedFrobenius_coefficient (b : Integers p E) :
    letI := coefficientAlgebra p C
    ramifiedFrobenius p C R (coefficient p (Residue p E) (Integers p E) R b) =
      coefficient p (Residue p E) (Integers p E) R b := by
  let := coefficientAlgebra p C
  exact integralMap_coefficient p (Residue p E) (Integers p E) (frobeniusTest p C R) b

end MathlibExt.AlgebraicGeometry.RelativeWittFrobenius
