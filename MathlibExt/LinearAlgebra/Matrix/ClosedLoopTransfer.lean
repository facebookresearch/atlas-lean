/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Closed-loop transfer maps of negative feedback

At a fixed frequency outside the plant and controller poles, regard the evaluated transfer
matrices `G` and `K` as rectangular matrices with opposite shapes. For unit negative feedback,
the loop equations reduce to `(1 + G * K) *ᵥ e = r`. The algebra works over any commutative
ring, in particular over `ℂ`; no claim is made about stability as the frequency varies.

## References

* K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and
  Engineers*, 2nd ed., electronic version v3.1.5 (2020-07-24), §12.1, equation (12.2),
  [official chapter](https://www.cds.caltech.edu/~murray/books/AM05/pdf/fbs-loopsyn_24Jul2020.pdf).
  Equation (12.2) gives the SISO maps `S`, `T` and `CS`, and Table 12.1 gives their roles in the
  response to the reference input. The theorem below derives the rectangular extension.
-/

public section

open Matrix

namespace MetaMathlibExt.Matrix

variable {p m R : Type*} [Fintype p] [DecidableEq p] [Fintype m] [CommRing R]

/-- At a fixed frequency, let `G` and `K` be the evaluated plant and controller matrices.
If `1 + G * K` is invertible, then for each reference `r` the negative-feedback equations
`e = r - y`, `u = K *ᵥ e`, `y = G *ᵥ u` have exactly one solution `(e, u, y)`. Its components
are `S *ᵥ r`, `(K * S) *ᵥ r`, and `T *ᵥ r`, with sensitivity `S = (1 + G * K)⁻¹` and
complementary sensitivity `T = (G * K) * S = S * (G * K)`. They satisfy `S + T = 1`.
This is the rectangular version of the `S`, `CS`, and `T` maps in Åström–Murray, §12.1,
equation (12.2). -/
theorem closed_loop_transfer_existsUnique (G : Matrix p m R) (K : Matrix m p R)
    (h : IsUnit (1 + G * K)) (r : p → R) :
    let S := (1 + G * K)⁻¹
    let T := (G * K) * S
    let solves : ((p → R) × (m → R) × (p → R)) → Prop := fun x =>
      x.1 = r - x.2.2 ∧ x.2.1 = K *ᵥ x.1 ∧ x.2.2 = G *ᵥ x.2.1
    (∃! x, solves x) ∧ solves (S *ᵥ r, (K * S) *ᵥ r, T *ᵥ r) ∧
      T = S * (G * K) ∧ S + T = 1 := by
  dsimp only
  let S := (1 + G * K)⁻¹
  let T := (G * K) * S
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp h
  have hleft : S * (1 + G * K) = 1 := Matrix.nonsing_inv_mul _ hd
  have hST : S + T = 1 := calc
    S + T = (1 + G * K) * S := by rw [Matrix.add_mul, Matrix.one_mul]
    _ = 1 := Matrix.mul_nonsing_inv _ hd
  have hTS : T = S * (G * K) := by
    apply add_left_cancel (a := S)
    calc
      S + T = 1 := hST
      _ = S * (1 + G * K) := hleft.symm
      _ = S + S * (G * K) := by rw [Matrix.mul_add, Matrix.mul_one]
  have herr : S *ᵥ r = r - T *ᵥ r := by
    apply eq_sub_of_add_eq
    rw [← Matrix.add_mulVec, hST, Matrix.one_mulVec]
  have hcontrol : (K * S) *ᵥ r = K *ᵥ (S *ᵥ r) := (Matrix.mulVec_mulVec r K S).symm
  have hout : T *ᵥ r = G *ᵥ ((K * S) *ᵥ r) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
  refine ⟨⟨(S *ᵥ r, (K * S) *ᵥ r, T *ᵥ r), ⟨herr, hcontrol, hout⟩, ?_⟩,
    ⟨herr, hcontrol, hout⟩, hTS, hST⟩
  rintro ⟨e, u, y⟩ ⟨he, hu, hy⟩
  change e = r - y at he
  change u = K *ᵥ e at hu
  change y = G *ᵥ u at hy
  have heq : (1 + G * K) *ᵥ e = r := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← hu, ← hy]
    exact eq_sub_iff_add_eq.mp he
  have he' : e = S *ᵥ r := by
    rw [← heq, Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  have hu' : u = (K * S) *ᵥ r := by rw [hcontrol, ← he', hu]
  have hy' : y = T *ᵥ r := by rw [hout, ← hu', hy]
  exact Prod.ext he' (Prod.ext hu' hy')

end MetaMathlibExt.Matrix
