/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Positive matrix quadratic forms and completely positive finite Gram sums

A positive C-star matrix has a nonnegative coefficient quadratic form in any
lawful coefficient order. Applying an ordinary completely positive map to
the actual Gram matrix yields the source-shaped finite Gram inequality.

No coefficient unit, nonempty index, norm bound, separability, replacement
matrix cone or tensor model is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators CStarAlgebra

namespace CStarMatrix

universe uB uI

section Algebraic

variable {B : Type uB} [NonUnitalSemiring B] [StarRing B]
variable {I : Type uI} [Fintype I]

private theorem quadraticForm_star_mul_self (R : CStarMatrix I I B) (b : I → B) :
    (∑ i, ∑ j, star (b i) * (star R * R) i j * b j) =
      ∑ k, star (∑ i, R k i * b i) * (∑ j, R k j * b j) := by
  classical
  have hentry (i j : I) :
      star (b i) * (star R * R) i j * b j =
        ∑ k, star (b i) * (star (R k i) * R k j) * b j := by
    rw [CStarMatrix.mul_apply]
    simp only [CStarMatrix.star_apply]
    rw [Finset.mul_sum, Finset.sum_mul]
  have hrow (k : I) :
      (∑ i, ∑ j, star (b i) * (star (R k i) * R k j) * b j) =
        star (∑ i, R k i * b i) * (∑ j, R k j * b j) := by
    rw [star_sum, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [star_mul, mul_assoc]
  calc
    (∑ i, ∑ j, star (b i) * (star R * R) i j * b j) =
        ∑ i, ∑ j, ∑ k, star (b i) * (star (R k i) * R k j) * b j :=
      Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => hentry i j
    _ = ∑ i, ∑ k, ∑ j, star (b i) * (star (R k i) * R k j) * b j :=
      Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, star (b i) * (star (R k i) * R k j) * b j :=
      Finset.sum_comm
    _ = ∑ k, star (∑ i, R k i * b i) * (∑ j, R k j * b j) :=
      Finset.sum_congr rfl fun k _ => hrow k

end Algebraic

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder B] [StarOrderedRing B]
variable {I : Type uI} [Fintype I]

/-- **Positive matrix quadratic form.** Let `B` be a nonunital complex C*-algebra with a star-compatible
partial order, let `I` be finite, let `P` be a positive `I × I` C*-matrix over `B`, and let `b : I →
B`. Then `∑ i j, bᵢ* Pᵢⱼ bⱼ ≥ 0`. The empty index type is allowed. -/
theorem quadraticForm_nonneg (P : CStarMatrix I I B) (hP : 0 ≤ P) (b : I → B) :
    0 ≤ ∑ i, ∑ j, star (b i) * P i j * b j := by
  classical
  rw [StarOrderedRing.nonneg_iff] at hP
  refine AddSubmonoid.closure_induction (fun Q hQ => ?_) ?_
    (fun P Q _ _ ihP ihQ => ?_) hP
  · obtain ⟨R, rfl⟩ := hQ
    rw [quadraticForm_star_mul_self]
    exact Finset.sum_nonneg fun k _ => star_mul_self_nonneg _
  · simp only [CStarMatrix.zero_apply, mul_zero, zero_mul,
      Finset.sum_const_zero, le_refl]
  · have hsum : (∑ i, ∑ j, star (b i) * (P + Q) i j * b j) =
        (∑ i, ∑ j, star (b i) * P i j * b j) +
          (∑ i, ∑ j, star (b i) * Q i j * b j) := by
      simp only [CStarMatrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
    rw [hsum]
    exact add_nonneg ihP ihQ

/-- **Positivity of a finite Gram matrix.** For a nonunital complex C*-algebra `B` with a
star-compatible partial order, a finite index type `I`, and `a : I → B`, the C*-matrix with entries
`aᵢ* aⱼ` is positive. No unit or nonempty index is required. -/
theorem gram_nonneg (a : I → B) :
    0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * a j) := by
  classical
  rcases isEmpty_or_nonempty I with hI | hI
  · apply le_of_eq
    apply CStarMatrix.ext
    intro i j
    exact (hI.false i).elim
  · obtain ⟨i0⟩ := hI
    let R : CStarMatrix I I B :=
      CStarMatrix.ofMatrix (Matrix.of fun k j => if k = i0 then a j else 0)
    have hRR :
        star R * R = CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * a j) := by
      apply CStarMatrix.ext
      intro i j
      simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, R,
        CStarMatrix.ofMatrix_apply, Matrix.of_apply]
      have hterm (k : I) :
          star (if k = i0 then a i else 0) * (if k = i0 then a j else 0) =
            if k = i0 then star (a i) * a j else 0 := by
        by_cases hk : k = i0 <;> simp [hk]
      rw [Finset.sum_congr rfl (fun k _ => hterm k)]
      rw [Finset.sum_ite_eq' _ i0 (fun _ => star (a i) * a j)]
      simp
    rw [← hRR]
    exact star_mul_self_nonneg R

end CStarMatrix

namespace CompletelyPositiveMap

universe uA uB uI

variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder B] [StarOrderedRing B]
variable {I : Type uI} [Fintype I]

/-- **Finite Gram inequality for CP maps.** For nonunital complex C*-algebras `A,B` with star-compatible
partial orders, a completely positive map `φ : A → B`, a finite index type `I`, and families `a : I
→ A`, `b : I → B`, `∑ i j, bᵢ* φ(aᵢ* aⱼ) bⱼ ≥ 0` in `B`. This includes the empty family. -/
theorem finite_gram_nonneg (phi : A →CP B) (a : I → A) (b : I → B) :
    0 ≤ ∑ i, ∑ j, star (b i) * phi (star (a i) * a j) * b j := by
  let G : CStarMatrix I I A :=
    CStarMatrix.ofMatrix (Matrix.of fun i j => star (a i) * a j)
  have hG : 0 ≤ G := CStarMatrix.gram_nonneg a
  have hP : 0 ≤ G.map phi := phi.map_cstarMatrix_nonneg G hG
  have h := CStarMatrix.quadraticForm_nonneg (G.map phi) hP b
  simpa only [G, CStarMatrix.map_apply, CStarMatrix.ofMatrix_apply, Matrix.of_apply] using h

end CompletelyPositiveMap
