/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Rademacher type and cotype 2 of Hilbert spaces

For vectors `x₀, …, xₙ₋₁` in a Hilbert space (real or complex), the
average of `‖∑ᵢ εᵢ xᵢ‖²` over all sign choices `ε ∈ {±1}ⁿ` is exactly
`∑ᵢ ‖xᵢ‖²`: cross terms cancel pairwise. In the language of Banach-space
geometry this says every Hilbert space has Rademacher type 2 and cotype 2,
both with the sharp constant `1`. The proof is by induction on `n`, using
the parallelogram law to combine the two values of the last sign.

Companion to the Hilbert-space material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean`.
Not one of the 72 v1 targets. Classical background: see e.g.
J. Lindenstrauss and L. Tzafriri, *Classical Banach Spaces II*,
Springer, 1979, Chapter 1, or G. Pisier, *Martingales in Banach Spaces*,
Cambridge University Press, 2016, Chapter 4.

This is distinct from the scalar Khintchine inequality in base MathlibExt
(`MathlibExt/Probability/KhintchineInequality.lean`): that file works with
real coefficients, a probability measure, and independent Rademacher
variables, and gives non-sharp constants for general `p`-moments. Here the
vectors live in an arbitrary Hilbert space, the average is the finite
uniform average over sign vectors, and the second moment is exact.
-/

namespace MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype

open Finset

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The Rademacher sign attached to a coordinate: `1` for `true`, `-1`
for `false`. -/
def rademacherSign (𝕜 : Type*) [RCLike 𝕜] {n : ℕ} (ε : Fin n → Bool) (i : Fin n) : 𝕜 :=
  if ε i then 1 else -1

/-- The sign is `1` on a `true` coordinate. -/
theorem rademacherSign_eq_one_of {n : ℕ} {ε : Fin n → Bool} {i : Fin n}
    (h : ε i = true) : rademacherSign 𝕜 ε i = (1 : 𝕜) := by
  simp [rademacherSign, h]

/-- The sign is `-1` on a `false` coordinate. -/
theorem rademacherSign_eq_neg_one_of {n : ℕ} {ε : Fin n → Bool} {i : Fin n}
    (h : ε i = false) : rademacherSign 𝕜 ε i = (-1 : 𝕜) := by
  simp [rademacherSign, h]

/-- Every Rademacher sign has norm `1`. -/
theorem norm_rademacherSign {n : ℕ} (ε : Fin n → Bool) (i : Fin n) :
    ‖rademacherSign 𝕜 ε i‖ = 1 := by
  unfold rademacherSign
  split <;> simp

/-- Number of sign vectors: `Fin n → Bool` has `2 ^ n` elements. -/
theorem card_sign_vectors (n : ℕ) :
    Fintype.card (Fin n → Bool) = 2 ^ n := by
  rw [Fintype.card_pi_const, Fintype.card_bool]

/-- Exact second moment of a Rademacher sum in a Hilbert space:
the sum over all sign vectors of `‖∑ᵢ εᵢ • xᵢ‖²` equals
`2 ^ n * ∑ᵢ ‖xᵢ‖²`. Cross terms cancel: the induction step pairs the
two values of the last sign and applies the parallelogram law. -/
theorem sum_rademacher_sq_norm_eq (n : ℕ) (x : Fin n → E) :
    ∑ ε : Fin n → Bool, ‖∑ i, rademacherSign 𝕜 ε i • x i‖ ^ 2
      = (2 : ℝ) ^ n * ∑ i, ‖x i‖ ^ 2 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    classical
    -- Split the sum over sign vectors by the last coordinate.
    have hsplit : ∑ ε : Fin (n + 1) → Bool,
          ‖∑ i, rademacherSign 𝕜 ε i • x i‖ ^ 2
        = ∑ b : Bool, ∑ ε' : Fin n → Bool,
          ‖∑ i, rademacherSign 𝕜 (Fin.snoc ε' b) i • x i‖ ^ 2 := by
      have h := (Fin.snocEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp
        (fun ε : Fin (n + 1) → Bool => ‖∑ i, rademacherSign 𝕜 ε i • x i‖ ^ 2)
      rw [← h]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro p _
      simp [Fin.snocEquiv]
    rw [hsplit]
    -- Evaluate the sum over the last sign `b : Bool`.
    have hbool : ∀ g : Bool → ℝ, (∑ b : Bool, g b) = g true + g false := by
      intro g
      simp [Fintype.univ_bool]
    rw [hbool]
    -- For each fixed initial sign vector, the two values of the last
    -- sign combine by the parallelogram law.
    have hinner : ∀ ε' : Fin n → Bool,
        ‖∑ i, rademacherSign 𝕜 (Fin.snoc ε' true) i • x i‖ ^ 2
          + ‖∑ i, rademacherSign 𝕜 (Fin.snoc ε' false) i • x i‖ ^ 2
        = 2 * (‖∑ i, rademacherSign 𝕜 ε' i • x i.castSucc‖ ^ 2
          + ‖x (Fin.last n)‖ ^ 2) := by
      intro ε'
      have hsum_true : ∑ i, rademacherSign 𝕜 (Fin.snoc ε' true) i • x i
          = (∑ i, rademacherSign 𝕜 ε' i • x i.castSucc) + x (Fin.last n) := by
        rw [Fin.sum_univ_castSucc]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          congr 1
          simp [rademacherSign, Fin.snoc_castSucc]
        · simp [rademacherSign, Fin.snoc_last]
      have hsum_false : ∑ i, rademacherSign 𝕜 (Fin.snoc ε' false) i • x i
          = (∑ i, rademacherSign 𝕜 ε' i • x i.castSucc) - x (Fin.last n) := by
        rw [Fin.sum_univ_castSucc, sub_eq_add_neg]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          congr 1
          simp [rademacherSign, Fin.snoc_castSucc]
        · simp [rademacherSign, Fin.snoc_last]
      rw [hsum_true, hsum_false]
      have hpar := parallelogram_law_with_norm 𝕜
        (∑ i, rademacherSign 𝕜 ε' i • x i.castSucc) (x (Fin.last n))
      linarith [hpar]
    rw [← Finset.sum_add_distrib]
    -- Sum the parallelogram identity over the initial sign vectors.
    have hsum_par : ∑ ε' : Fin n → Bool,
          (‖∑ i, rademacherSign 𝕜 (Fin.snoc ε' true) i • x i‖ ^ 2
            + ‖∑ i, rademacherSign 𝕜 (Fin.snoc ε' false) i • x i‖ ^ 2)
        = ∑ ε' : Fin n → Bool,
          2 * (‖∑ i, rademacherSign 𝕜 ε' i • x i.castSucc‖ ^ 2
            + ‖x (Fin.last n)‖ ^ 2) :=
      Finset.sum_congr rfl (fun ε' _ => hinner ε')
    rw [hsum_par]
    have hstep : ∑ ε' : Fin n → Bool,
          2 * (‖∑ i, rademacherSign 𝕜 ε' i • x i.castSucc‖ ^ 2
            + ‖x (Fin.last n)‖ ^ 2)
        = 2 * ((2 : ℝ) ^ n * ∑ i : Fin n, ‖x i.castSucc‖ ^ 2
          + (2 : ℝ) ^ n * ‖x (Fin.last n)‖ ^ 2) := by
      have h1 : ∑ ε' : Fin n → Bool,
            (‖∑ i, rademacherSign 𝕜 ε' i • x i.castSucc‖ ^ 2
              + ‖x (Fin.last n)‖ ^ 2)
          = (2 : ℝ) ^ n * ∑ i : Fin n, ‖x i.castSucc‖ ^ 2
            + (2 : ℝ) ^ n * ‖x (Fin.last n)‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ih (fun i => x i.castSucc),
          Finset.sum_const, Finset.card_univ, card_sign_vectors]
        ring
      rw [← Finset.mul_sum, h1]
    rw [hstep]
    -- Reassemble the right-hand side over `Fin (n + 1)`.
    have htotal : ∑ i : Fin (n + 1), ‖x i‖ ^ 2
        = ∑ i : Fin n, ‖x i.castSucc‖ ^ 2 + ‖x (Fin.last n)‖ ^ 2 :=
      Fin.sum_univ_castSucc _
    rw [htotal, pow_succ]
    ring

/-- The average (uniform over sign vectors) of `‖∑ᵢ εᵢ • xᵢ‖²` is exactly
`∑ᵢ ‖xᵢ‖²`. -/
theorem average_rademacher_sq_norm_eq (n : ℕ) (x : Fin n → E) :
    ((2 : ℝ) ^ n) ⁻¹ * ∑ ε : Fin n → Bool, ‖∑ i, rademacherSign 𝕜 ε i • x i‖ ^ 2
      = ∑ i, ‖x i‖ ^ 2 := by
  rw [sum_rademacher_sq_norm_eq, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero n (two_ne_zero : (2 : ℝ) ≠ 0)), one_mul]

/-- Rademacher type 2 with constant `1`: the average of the squared
Rademacher sums is at most `∑ᵢ ‖xᵢ‖²`. -/
theorem rademacher_type_two (n : ℕ) (x : Fin n → E) :
    ((2 : ℝ) ^ n) ⁻¹ * ∑ ε : Fin n → Bool, ‖∑ i, rademacherSign 𝕜 ε i • x i‖ ^ 2
      ≤ ∑ i, ‖x i‖ ^ 2 :=
  le_of_eq (average_rademacher_sq_norm_eq n x)

/-- Rademacher cotype 2 with constant `1`: `∑ᵢ ‖xᵢ‖²` is at most the
average of the squared Rademacher sums. -/
theorem rademacher_cotype_two (n : ℕ) (x : Fin n → E) :
    ∑ i, ‖x i‖ ^ 2
      ≤ ((2 : ℝ) ^ n) ⁻¹ * ∑ ε : Fin n → Bool, ‖∑ i, rademacherSign 𝕜 ε i • x i‖ ^ 2 :=
  le_of_eq (average_rademacher_sq_norm_eq n x).symm

/-- Square-root form of the exact second moment. -/
theorem sqrt_average_rademacher_sq_norm_eq (n : ℕ) (x : Fin n → E) :
    Real.sqrt (((2 : ℝ) ^ n) ⁻¹ *
        ∑ ε : Fin n → Bool, ‖∑ i, rademacherSign 𝕜 ε i • x i‖ ^ 2)
      = Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
  rw [average_rademacher_sq_norm_eq]

/-- The average Rademacher norm is at most `(∑ᵢ ‖xᵢ‖²)^{1/2}`
(Cauchy–Schwarz for the finite average, plus the exact second moment). -/
theorem average_rademacher_norm_le (n : ℕ) (x : Fin n → E) :
    ((2 : ℝ) ^ n) ⁻¹ * ∑ ε : Fin n → Bool, ‖∑ i, rademacherSign 𝕜 ε i • x i‖
      ≤ Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hnonneg : 0 ≤ ((2 : ℝ) ^ n) ⁻¹ *
      ∑ ε : Fin n → Bool, ‖∑ i, rademacherSign 𝕜 ε i • x i‖ := by
    positivity
  rw [Real.le_sqrt hnonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  have hcs : (∑ ε : Fin n → Bool, ‖∑ i, rademacherSign 𝕜 ε i • x i‖) ^ 2
      ≤ (Finset.univ : Finset (Fin n → Bool)).card
        * ∑ ε : Fin n → Bool, ‖∑ i, rademacherSign 𝕜 ε i • x i‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun ε : Fin n → Bool => ‖∑ i, rademacherSign 𝕜 ε i • x i‖)
    simpa using h
  rw [Finset.card_univ, card_sign_vectors] at hcs
  rw [sum_rademacher_sq_norm_eq] at hcs
  have hcs' : (∑ ε : Fin n → Bool, ‖∑ i, rademacherSign 𝕜 ε i • x i‖) ^ 2
      ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ n * ∑ i, ‖x i‖ ^ 2) := by
    push_cast at hcs
    exact hcs
  calc (((2 : ℝ) ^ n) ⁻¹ * ∑ ε : Fin n → Bool, ‖∑ i, rademacherSign 𝕜 ε i • x i‖) ^ 2
      = ((2 : ℝ) ^ n) ⁻¹ * (((2 : ℝ) ^ n) ⁻¹ *
        (∑ ε : Fin n → Bool, ‖∑ i, rademacherSign 𝕜 ε i • x i‖) ^ 2) := by
        rw [mul_pow]
        ring
    _ ≤ ((2 : ℝ) ^ n) ⁻¹ * (((2 : ℝ) ^ n) ⁻¹ *
        ((2 : ℝ) ^ n * ((2 : ℝ) ^ n * ∑ i, ‖x i‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hcs' (inv_nonneg.mpr h2n.le)) (inv_nonneg.mpr h2n.le)
    _ = ∑ i, ‖x i‖ ^ 2 := by
        field_simp

/-- For unit vectors, the average squared Rademacher sum equals `n`. -/
theorem average_rademacher_sq_norm_eq_of_norm_eq_one {n : ℕ} {x : Fin n → E}
    (hx : ∀ i, ‖x i‖ = 1) :
    ((2 : ℝ) ^ n) ⁻¹ * ∑ ε : Fin n → Bool, ‖∑ i, rademacherSign 𝕜 ε i • x i‖ ^ 2
      = n := by
  rw [average_rademacher_sq_norm_eq]
  simp [hx]

/-- Scalar real form: the second moment of `∑ᵢ ±aᵢ` over all sign choices
is `2 ^ n * ∑ᵢ aᵢ²`. -/
theorem sum_rademacher_sq_real (n : ℕ) (a : Fin n → ℝ) :
    ∑ ε : Fin n → Bool, (∑ i, (if ε i then a i else -a i)) ^ 2
      = (2 : ℝ) ^ n * ∑ i, (a i) ^ 2 := by
  have h := sum_rademacher_sq_norm_eq (𝕜 := ℝ) (E := ℝ) n a
  have hterm : ∀ ε : Fin n → Bool,
      ‖∑ i, rademacherSign ℝ ε i • a i‖ ^ 2
        = (∑ i, (if ε i then a i else -a i)) ^ 2 := by
    intro ε
    have hsum : (∑ i, rademacherSign ℝ ε i • a i)
        = ∑ i, (if ε i then a i else -a i) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold rademacherSign
      split
      · simp
      · simp [smul_eq_mul]
    rw [hsum, Real.norm_eq_abs, sq_abs]
  calc ∑ ε : Fin n → Bool, (∑ i, (if ε i then a i else -a i)) ^ 2
      = ∑ ε : Fin n → Bool, ‖∑ i, rademacherSign ℝ ε i • a i‖ ^ 2 :=
        Finset.sum_congr rfl (fun ε _ => (hterm ε).symm)
    _ = (2 : ℝ) ^ n * ∑ i, ‖a i‖ ^ 2 := h
    _ = (2 : ℝ) ^ n * ∑ i, (a i) ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [Real.norm_eq_abs, sq_abs]

end MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype
