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

public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Square-summable vector coefficients of bounded operators

Let `H` be a complex normed inner-product space, possibly incomplete, and `x,y ∈ ℓ²(ℕ,H)`. A
bounded operator `T` acts diagonally by `(D_T x)_n=T(x_n)`, with `‖D_T‖≤‖T‖` and `‖D_T
x‖₂≤‖x‖₂‖T‖`.

The matrix-coefficient series `ω_(x,y)(T)=Σ_n ⟨y_n,T x_n⟩` converges and defines a bounded
complex-linear functional of `T`, with `|ω_(x,y)(T)|≤‖y‖₂‖x‖₂‖T‖`. Its expression is the inner
product `⟨y,D_T x⟩` on the square-summable sequence space. Neither separability nor nonzero
vectors or a nontrivial space is required.
-/

@[expose] public section
noncomputable section
open scoped ENNReal InnerProductSpace
namespace OperatorUltraweak
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Square-summable sequences in a normed group.** For a normed additive commutative group
`H`, `VectorSequence H = lp (fun _ : ℕ => H) 2` consists of sequences with summable
squared norms, equipped with the ℓ² norm. No inner product, scalar action or completeness
is required for this carrier. -/
abbrev VectorSequence (H : Type u) [NormedAddCommGroup H] := lp (fun _ : ℕ => H) 2

/-- **Diagonal action of a bounded Hilbert operator.** Let `H` be a complex normed
inner-product space, with no completeness assumption. Write `ℓ²(H)=lp (fun _ : ℕ => H) 2`
for its square-summable vector sequences. for `T : H →L[ℂ] H`, `diagonal T : ℓ²(H) →L[ℂ]
ℓ²(H)` has coordinate `(diagonal T x)_n=T(x_n)` and operator norm at most `‖T‖`. -/
def diagonal (T : H →L[ℂ] H) : VectorSequence H →L[ℂ] VectorSequence H :=
  lp.mapCLM 2 (fun _ : ℕ => T) (norm_nonneg T) (fun _ => le_rfl)

/-- **Coordinates of a diagonal operator action.** Let `H` be a complex normed inner-product
space, with no completeness assumption. Write `ℓ²(H)=lp (fun _ : ℕ => H) 2` for its
square-summable vector sequences. for `T : H →L[ℂ] H`, `x ∈ ℓ²(H)` and `n : ℕ`, `(diagonal
T x)_n=T(x_n)`. -/
theorem diagonal_apply (T : H →L[ℂ] H) (x : VectorSequence H) (n : ℕ) :
    diagonal T x n = T (x n) := rfl

/-- **Operator norm bound for the diagonal action.** Let `H` be a complex normed inner-product
space, with no completeness assumption. Write `ℓ²(H)=lp (fun _ : ℕ => H) 2` for its
square-summable vector sequences. for every bounded complex-linear `T : H →L[ℂ] H`,
`‖diagonal T‖≤‖T‖`, with the ℓ² norm on the sequence space and operator norms on both
maps. -/
theorem diagonal_norm_le (T : H →L[ℂ] H) : ‖diagonal T‖ ≤ ‖T‖ :=
  lp.norm_mapCLM_le 2 (fun _ : ℕ => T) (norm_nonneg T) (fun _ => le_rfl)

/-- **Additivity of diagonal action on a vector sequence.** Let `H` be a complex normed
inner-product space, with no completeness assumption. Write `ℓ²(H)=lp (fun _ : ℕ => H) 2`
for its square-summable vector sequences. for `x ∈ ℓ²(H)` and bounded `T,U : H →L[ℂ] H`,
`diagonal (T+U) x=diagonal T x+diagonal U x`. -/
theorem action_add (x : VectorSequence H) (T U : H →L[ℂ] H) :
    diagonal (T + U) x = diagonal T x + diagonal U x := by
  apply lp.ext
  funext n
  change (T + U) (x n) = T (x n) + U (x n)
  rfl

/-- **Complex scaling of diagonal sequence action.** Let `H` be a complex normed inner-product
space, with no completeness assumption. Write `ℓ²(H)=lp (fun _ : ℕ => H) 2` for its
square-summable vector sequences. for `x ∈ ℓ²(H)`, `c : ℂ` and bounded `T`, `diagonal (c •
T) x=c • diagonal T x`. -/
theorem action_smul (x : VectorSequence H) (c : ℂ) (T : H →L[ℂ] H) :
    diagonal (c • T) x = c • diagonal T x := by
  apply lp.ext
  funext n
  change (c • T) (x n) = c • T (x n)
  rfl

/-- **Norm of a bounded operator acting on a vector sequence.** Let `H` be a complex normed
inner-product space, with no completeness assumption. Write `ℓ²(H)=lp (fun _ : ℕ => H) 2`
for its square-summable vector sequences. for `x ∈ ℓ²(H)` and `T : H →L[ℂ] H`, `‖diagonal
T x‖₂≤‖x‖₂*‖T‖`. -/
theorem action_norm_le (x : VectorSequence H) (T : H →L[ℂ] H) :
    ‖diagonal T x‖ ≤ ‖x‖ * ‖T‖ := by
  have h := ((diagonal T).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (diagonal_norm_le T) (norm_nonneg x))
  exact h.trans_eq (mul_comm _ _)

/-- **Bounded operator evaluation on a vector sequence.** Let `H` be a complex normed
inner-product space, with no completeness assumption. Write `ℓ²(H)=lp (fun _ : ℕ => H) 2`
for its square-summable vector sequences. for fixed `x ∈ ℓ²(H)`, `action x : B(H) →L[ℂ]
ℓ²(H)` sends `T` to `(T x_n)_n`, with bound `‖action x T‖₂≤‖x‖₂‖T‖`. -/
def action (x : VectorSequence H) : (H →L[ℂ] H) →L[ℂ] VectorSequence H :=
  ({ toFun := fun T => diagonal T x
     map_add' := action_add x
     map_smul' := action_smul x } : (H →L[ℂ] H) →ₗ[ℂ] VectorSequence H).mkContinuous
    ‖x‖ (action_norm_le x)

/-- **Coordinates of operator evaluation on a sequence.** Let `H` be a complex normed
inner-product space, with no completeness assumption. Write `ℓ²(H)=lp (fun _ : ℕ => H) 2`
for its square-summable vector sequences. for `x ∈ ℓ²(H)`, bounded `T` and `n : ℕ`,
`(action x T)_n=T(x_n)`. -/
theorem action_apply (x : VectorSequence H) (T : H →L[ℂ] H) (n : ℕ) :
    action x T n = T (x n) := rfl

/-- **Bounded functional of square-summable matrix coefficients.** Let `H` be a complex normed
inner-product space, with no completeness assumption. Write `ℓ²(H)=lp (fun _ : ℕ => H) 2`
for its square-summable vector sequences. for `x,y ∈ ℓ²(H)`, `coefficient x y : B(H) →L[ℂ]
ℂ` sends `T` to `⟨y,diagonal T x⟩=Σ_n ⟨y_n,T x_n⟩`; the pairing is linear in `T`. -/
def coefficient (x y : VectorSequence H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ y).comp (action x)

/-- **Convergence of a square-summable matrix-coefficient series.** Let `H` be a complex
normed inner-product space, with no completeness assumption. Write `ℓ²(H)=lp (fun _ : ℕ =>
H) 2` for its square-summable vector sequences. for `x,y ∈ ℓ²(H)` and bounded `T : H →L[ℂ]
H`, the series `Σ_n ⟨y_n,T x_n⟩` is summable in `ℂ`. -/
theorem coefficient_summable (x y : VectorSequence H) (T : H →L[ℂ] H) :
    Summable (fun n : ℕ => ⟪y n, T (x n)⟫_ℂ) := by
  simpa only [diagonal_apply] using (lp.summable_inner y (diagonal T x))

/-- **Series formula for a bounded operator coefficient.** Let `H` be a complex normed
inner-product space, with no completeness assumption. Write `ℓ²(H)=lp (fun _ : ℕ => H) 2`
for its square-summable vector sequences. for `x,y ∈ ℓ²(H)` and bounded `T`, `coefficient
x y T=Σ' n : ℕ, ⟨y_n,T x_n⟩`, with the complex inner product linear in its second
argument. -/
theorem coefficient_apply (x y : VectorSequence H) (T : H →L[ℂ] H) :
    coefficient x y T = ∑' n : ℕ, ⟪y n, T (x n)⟫_ℂ := by
  change ⟪y, diagonal T x⟫_ℂ = _
  exact (lp.inner_eq_tsum y (diagonal T x)).trans (tsum_congr (fun n => rfl))

/-- **Norm estimate for an infinite matrix coefficient.** Let `H` be a complex normed
inner-product space, with no completeness assumption. Write `ℓ²(H)=lp (fun _ : ℕ => H) 2`
for its square-summable vector sequences. for `x,y ∈ ℓ²(H)` and bounded `T`, `‖coefficient
x y T‖≤‖y‖₂*‖x‖₂*‖T‖`. -/
theorem coefficient_bound (x y : VectorSequence H) (T : H →L[ℂ] H) :
    ‖coefficient x y T‖ ≤ ‖y‖ * ‖x‖ * ‖T‖ := by
  change ‖⟪y, diagonal T x⟫_ℂ‖ ≤ _
  exact (norm_inner_le_norm y (diagonal T x)).trans
    ((mul_le_mul_of_nonneg_left (action_norm_le x T) (norm_nonneg y)).trans_eq (mul_assoc _ _ _).symm)

end OperatorUltraweak
