/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvFormalGroup.Hom

import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tests for homomorphisms of multivariate formal group laws

A matrix `A` gives a homomorphism `linHom A` of additive formal group laws. The tests check that
`Hom.id`, `Hom.comp`, the zero homomorphism and the sum of homomorphisms act on these as the
identity matrix, the matrix product (in this order), the zero matrix and the matrix sum, and
that `linearPart` recovers `A`.
-/

@[expose] public section

noncomputable section

namespace MvFormalGroupHomTest

open MvPowerSeries MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]

/-- Substitution into a linear form. -/
theorem subst_sum_smul_X {τ : Type*} {n : ℕ} {b : Fin n → MvPowerSeries τ R} (hb : HasSubst b)
    (c : Fin n → R) :
    subst b (∑ j, c j • (X j : MvPowerSeries (Fin n) R)) = ∑ j, c j • b j := by
  rw [← coe_substAlgHom hb, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, coe_substAlgHom hb, subst_X hb]

/-- The homomorphism of additive formal group laws given by a matrix. -/
def linHom (A : Matrix (Fin h) (Fin g) R) : Hom (addMv g R) (addMv h R) where
  toPowerSeries i := ∑ j, A i j • X j
  constantCoeff_eq_zero i := by simp
  subst_eq i := by
    have hXl : HasSubst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hXr : HasSubst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    change subst (fun j => (X (Sum.inl j) + X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (∑ j, A i j • X j) =
      subst (Sum.elim
          (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (∑ l, A j l • X l))
          fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (∑ l, A j l • X l))
        (X (Sum.inl i) + X (Sum.inr i))
    rw [subst_sum_smul_X (hasSubst_of_constantCoeff_zero fun j => by simp),
      subst_X_add_X (by rintro (j | j) <;> simp [subst_sum_smul_X hXl, subst_sum_smul_X hXr])]
    simp only [Sum.elim_inl, Sum.elim_inr, subst_sum_smul_X hXl, subst_sum_smul_X hXr, smul_add,
      Finset.sum_add_distrib]

@[simp]
theorem toPowerSeries_linHom (A : Matrix (Fin h) (Fin g) R) (i : Fin h) :
    (linHom A).toPowerSeries i = ∑ j, A i j • (X j : MvPowerSeries (Fin g) R) :=
  rfl

/-- `linearPart` reads off the matrix, with rows indexed by the target coordinates. -/
theorem linearPart_linHom (A : Matrix (Fin h) (Fin g) R) :
    linearPart (linHom A).toPowerSeries = A := by
  ext i j
  simp [linearPart, coeff_X, Finsupp.single_left_inj one_ne_zero]

/-- `Hom.id` is the homomorphism of the identity matrix. -/
theorem id_eq_linHom : Hom.id (addMv g R) = linHom 1 := by
  apply Hom.ext
  funext i
  change (X i : MvPowerSeries (Fin g) R) = ∑ j, (1 : Matrix (Fin g) (Fin g) R) i j • X j
  simp [Matrix.one_apply]

/-- `Hom.comp ψ φ` is `ψ ∘ φ`: it multiplies the matrices in this order. -/
theorem comp_linHom (A : Matrix (Fin k) (Fin h) R) (B : Matrix (Fin h) (Fin g) R) :
    (linHom A).comp (linHom B) = linHom (A * B) := by
  apply Hom.ext
  funext i
  change subst (linHom B).toPowerSeries (∑ j, A i j • (X j : MvPowerSeries (Fin h) R)) = _
  rw [subst_sum_smul_X (linHom B).hasSubst_toPowerSeries, toPowerSeries_linHom]
  simp only [toPowerSeries_linHom, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/-- The zero homomorphism is the homomorphism of the zero matrix. -/
theorem zero_eq_linHom : (0 : Hom (addMv g R) (addMv h R)) = linHom 0 := by
  apply Hom.ext
  funext i
  simp

/-- The sum of homomorphisms into the additive law adds the matrices. -/
theorem linHom_add (A A' : Matrix (Fin h) (Fin g) R) :
    linHom A + linHom A' = linHom (A + A') := by
  apply Hom.ext
  funext i
  change subst (Sum.elim (linHom A).toPowerSeries (linHom A').toPowerSeries)
      (X (Sum.inl i) + X (Sum.inr i)) = _
  rw [subst_X_add_X (by rintro (j | j) <;> exact Hom.constantCoeff_eq_zero _ j)]
  simp [Matrix.add_apply, add_smul, Finset.sum_add_distrib]

/-- The homomorphisms into a commutative law form an additive commutative monoid. -/
example : AddCommMonoid (Hom (addMv g R) (addMv h R)) := inferInstance

example (A : Matrix (Fin h) (Fin g) R) : 2 • linHom A = linHom (2 • A) := by
  rw [two_nsmul, linHom_add, two_nsmul]

/-- Composition and sums together: `(A + A') * B`. -/
example (A A' : Matrix (Fin k) (Fin h) R) (B : Matrix (Fin h) (Fin g) R) :
    linearPart ((linHom A + linHom A').comp (linHom B)).toPowerSeries = (A + A') * B := by
  rw [linHom_add, comp_linHom, linearPart_linHom]

/-- `comp_linHom` pins the order of the factors: swapping them changes the composite. -/
example : (linHom (R := ℤ) !![1, 1; 0, 1]).comp (linHom !![1, 0; 1, 1]) ≠
    linHom (!![1, 0; 1, 1] * !![1, 1; 0, 1]) := by
  rw [comp_linHom]
  intro hc
  have := congrFun (congrFun (congrArg (fun φ => linearPart (Hom.toPowerSeries φ)) hc) 0) 0
  simp [linearPart_linHom] at this

end MvFormalGroupHomTest

end
