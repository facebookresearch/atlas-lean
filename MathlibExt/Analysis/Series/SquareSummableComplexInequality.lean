/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ZetaValues

/-!
# An inequality for square-summable complex sequences

Every positive integer is uniquely `2 ^ k * (2 * l + 1)` with `k l : ℕ`. For complex numbers
`(αₙ)_{n ≥ 1}` with `∑ₙ |αₙ|² < ∞`, put `βₖ = ∑_{l ≥ 0} α_{2ᵏ(2l+1)} / (l + 1)` for `k ≥ 0`.
Then each series defining `βₖ` converges absolutely, `∑ₖ |βₖ|² < ∞`, and
`∑_{n ≥ 1} |αₙ|² ≥ (6 / π²) ∑_{k ≥ 0} |βₖ|²`.

The proof is the Cauchy–Schwarz inequality. Since `∑_{l ≥ 0} 1 / (l + 1)² = π² / 6`
(`hasSum_zeta_two`), Hölder's inequality with exponents `2` and `2`
(`Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg`) shows that the series defining `βₖ` converges
absolutely and that `|βₖ|² ≤ (π² / 6) ∑_{l ≥ 0} |α_{2ᵏ(2l+1)}|²`. Summing over `k` and
regrouping the terms `|αₙ|²` along the bijection `(k, l) ↦ 2ᵏ(2l + 1)` from `ℕ × ℕ` onto the
positive integers gives the inequality.

## Main results

* `conjecture`: the statement, for a sequence `α : ℕ → ℂ` whose `n`th term is `α n` for `n ≥ 1`;
  the value `α 0` is not used.
* `conjecture_holds`: the statement holds.

The statement comes from the Open Problem Garden entry recorded in the comment below.
-/

@[expose] public section

namespace MathlibExt.Analysis.SquareSummableComplexInequalityWanted

/-! Source record `OPG-41335`, ported from the Open Problem Garden entry
"Inequality for square summable complex series"
(http://www.openproblemgarden.org/op/inequality_for_square_summable_complex_series).

For `α = (α₁, α₂, …) ∈ ℓ²(ℂ)` the result asserts
`∑ₙ |αₙ|² ≥ (6/π²) ∑ₖ |∑ₗ α_{2ᵏ(2l+1)} / (l+1)|²`,
where every `n ≥ 1` is uniquely written `n = 2ᵏ(2l+1)`.

The sequence is represented by a function on `ℕ`. The sum `∑' n, ‖α (n + 1)‖ ^ 2` is indexed
by `n : ℕ`; its summand at `n` uses the one-based sequence entry `α (n + 1)`. The value `α 0`
is unused. The two summability conclusions are included explicitly so totalized `tsum` cannot
make the inequality vacuous. -/

/-- If `∑_{n ≥ 1} ‖α n‖²` converges, then for every `k` the series
`βₖ = ∑_{l ≥ 0} α (2 ^ k * (2 * l + 1)) / (l + 1)` converges (absolutely, as `ℂ` is finite
dimensional), `∑ₖ ‖βₖ‖²` converges, and `∑_{n ≥ 1} ‖α n‖² ≥ 6 / π ^ 2 * ∑ₖ ‖βₖ‖²`. -/
def conjecture : Prop :=
  ∀ α : ℕ → ℂ, Summable (fun n => ‖α (n + 1)‖ ^ 2) →
    (∀ k : ℕ, Summable (fun l => α (2 ^ k * (2 * l + 1)) / (l + 1 : ℂ))) ∧
    Summable (fun k => ‖∑' l, α (2 ^ k * (2 * l + 1)) / (l + 1 : ℂ)‖ ^ 2) ∧
      ∑' n, ‖α (n + 1)‖ ^ 2 ≥
        6 / Real.pi ^ 2 * ∑' k, ‖∑' l, α (2 ^ k * (2 * l + 1)) / (l + 1 : ℂ)‖ ^ 2

/-- The exponent of `2` and the odd part of a positive integer are unique. -/
private lemma two_pow_mul_odd_injective :
    Function.Injective fun p : ℕ × ℕ => 2 ^ p.1 * (2 * p.2 + 1) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  dsimp only at h
  -- `ordCompl[2]` recovers the odd part `2 * l + 1` of `2 ^ k * (2 * l + 1)`.
  have hodd (k l : ℕ) : ordCompl[2] (2 ^ k * (2 * l + 1)) = 2 * l + 1 :=
    Nat.ordCompl_pow_mul_of_not_dvd k Nat.prime_two (by omega)
  have hbd : 2 * b + 1 = 2 * d + 1 := by rw [← hodd a b, ← hodd c d, h]
  rw [hbd] at h
  exact Prod.ext (Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_right (by omega) h))
    (by omega)

/-- Every positive integer `n + 1` is `2 ^ k * (2 * l + 1)` for some `k l : ℕ`. -/
private lemma two_pow_mul_odd_sub_one_surjective :
    Function.Surjective fun p : ℕ × ℕ => 2 ^ p.1 * (2 * p.2 + 1) - 1 := by
  intro n
  obtain ⟨k, m, ⟨l, rfl⟩, h⟩ := Nat.exists_eq_two_pow_mul_odd n.succ_ne_zero
  exact ⟨(k, l), by dsimp only; omega⟩

/-- A series over the positive integers, regrouped along `n = 2 ^ k * (2 * l + 1)`. -/
private lemma hasSum_two_pow_mul_odd {f : ℕ → ℝ} {a : ℝ} (hf : HasSum (fun n => f (n + 1)) a) :
    HasSum (fun p : ℕ × ℕ => f (2 ^ p.1 * (2 * p.2 + 1))) a := by
  have hbij : Function.Bijective fun p : ℕ × ℕ => 2 ^ p.1 * (2 * p.2 + 1) - 1 := by
    refine ⟨fun p q h => two_pow_mul_odd_injective ?_, two_pow_mul_odd_sub_one_surjective⟩
    have hp : 0 < 2 ^ p.1 * (2 * p.2 + 1) := by positivity
    have hq : 0 < 2 ^ q.1 * (2 * q.2 + 1) := by positivity
    dsimp only at h ⊢
    omega
  convert (Equiv.ofBijective _ hbij).hasSum_iff.mpr hf using 2 with p
  simp only [Function.comp_apply, Equiv.ofBijective_apply]
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (by positivity))]

/-- `∑_{l ≥ 0} 1 / (l + 1) ^ 2 = π ^ 2 / 6`. -/
private lemma hasSum_one_div_succ_sq :
    HasSum (fun l : ℕ => (1 / ((l : ℝ) + 1)) ^ 2) (Real.pi ^ 2 / 6) := by
  simpa [div_pow] using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two

/-- The Cauchy–Schwarz step: for a square-summable `x`, the series `∑ₗ x l / (l + 1)` converges
and `‖∑ₗ x l / (l + 1)‖ ^ 2 ≤ π ^ 2 / 6 * ∑ₗ ‖x l‖ ^ 2`. -/
private lemma summable_div_succ_and_norm_tsum_sq_le (x : ℕ → ℂ)
    (hx : Summable fun l => ‖x l‖ ^ 2) :
    Summable (fun l => x l / (l + 1 : ℂ)) ∧
      ‖∑' l, x l / (l + 1 : ℂ)‖ ^ 2 ≤ Real.pi ^ 2 / 6 * ∑' l, ‖x l‖ ^ 2 := by
  have hc : 0 ≤ ∑' l, ‖x l‖ ^ 2 := tsum_nonneg fun l => by positivity
  have hpi : (0 : ℝ) ≤ Real.pi ^ 2 / 6 := by positivity
  obtain ⟨C, -, hCle, hC⟩ := Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg
    Real.HolderConjugate.two_two (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (A := √(∑' l, ‖x l‖ ^ 2)) (B := √(Real.pi ^ 2 / 6))
    (f := fun l => ‖x l‖) (g := fun l : ℕ => 1 / ((l : ℝ) + 1))
    (fun l => norm_nonneg _) (fun l => by positivity)
    (by simpa only [Real.rpow_two, Real.sq_sqrt hc] using hx.hasSum)
    (by simpa only [Real.rpow_two, Real.sq_sqrt hpi] using hasSum_one_div_succ_sq)
  have hnorm : (fun l => ‖x l / (l + 1 : ℂ)‖) = fun l => ‖x l‖ * (1 / ((l : ℝ) + 1)) := by
    ext l
    rw [norm_div, ← div_eq_mul_one_div]
    congr 1
    exact_mod_cast Complex.norm_natCast (l + 1)
  have hsum : Summable fun l => ‖x l / (l + 1 : ℂ)‖ := by
    rw [hnorm]
    exact hC.summable
  refine ⟨hsum.of_norm, ?_⟩
  have h1 : ‖∑' l, x l / (l + 1 : ℂ)‖ ≤ C := by
    calc _ ≤ ∑' l, ‖x l / (l + 1 : ℂ)‖ := norm_tsum_le_tsum_norm hsum
      _ = C := by rw [hnorm]; exact hC.tsum_eq
  calc ‖∑' l, x l / (l + 1 : ℂ)‖ ^ 2
      ≤ (√(∑' l, ‖x l‖ ^ 2) * √(Real.pi ^ 2 / 6)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (h1.trans hCle) 2
    _ = Real.pi ^ 2 / 6 * ∑' l, ‖x l‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hc, Real.sq_sqrt hpi, mul_comm]

/--
Resolved true: The source page records a Cauchy–Schwarz proof of the displayed inequality.
Source: Open Problem Garden solution comment 73221,
https://www.openproblemgarden.org/op/inequality_for_square_summable_complex_series#comment-73221.
Moved from `OpenConjectures/Analysis/SquareSummableComplexInequality`.
-/
theorem conjecture_holds : conjecture := by
  intro α hα
  -- Regroup `∑_{n ≥ 1} ‖α n‖ ^ 2` along `n = 2 ^ k * (2 * l + 1)`, first over `l`, then over `k`.
  have hS : HasSum (fun p : ℕ × ℕ => ‖α (2 ^ p.1 * (2 * p.2 + 1))‖ ^ 2)
      (∑' n, ‖α (n + 1)‖ ^ 2) :=
    hasSum_two_pow_mul_odd (f := fun n => ‖α n‖ ^ 2) hα.hasSum
  have hfib (k : ℕ) : Summable fun l => ‖α (2 ^ k * (2 * l + 1))‖ ^ 2 :=
    hS.summable.prod_factor k
  have hc : HasSum (fun k => ∑' l, ‖α (2 ^ k * (2 * l + 1))‖ ^ 2) (∑' n, ‖α (n + 1)‖ ^ 2) :=
    hS.prod_fiberwise fun k => (hfib k).hasSum
  -- Cauchy–Schwarz for each `βₖ`.
  have key (k : ℕ) :=
    summable_div_succ_and_norm_tsum_sq_le (fun l => α (2 ^ k * (2 * l + 1))) (hfib k)
  have hβ : Summable fun k => ‖∑' l, α (2 ^ k * (2 * l + 1)) / (l + 1 : ℂ)‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => by positivity) (fun k => (key k).2)
      (hc.summable.mul_left _)
  refine ⟨fun k => (key k).1, hβ, ?_⟩
  have hle : ∑' k, ‖∑' l, α (2 ^ k * (2 * l + 1)) / (l + 1 : ℂ)‖ ^ 2 ≤
      Real.pi ^ 2 / 6 * ∑' n, ‖α (n + 1)‖ ^ 2 := by
    rw [← hc.tsum_eq, ← tsum_mul_left]
    exact hβ.tsum_le_tsum (fun k => (key k).2) (hc.summable.mul_left _)
  calc 6 / Real.pi ^ 2 * ∑' k, ‖∑' l, α (2 ^ k * (2 * l + 1)) / (l + 1 : ℂ)‖ ^ 2
      ≤ 6 / Real.pi ^ 2 * (Real.pi ^ 2 / 6 * ∑' n, ‖α (n + 1)‖ ^ 2) := by gcongr
    _ = ∑' n, ‖α (n + 1)‖ ^ 2 := by field_simp

end MathlibExt.Analysis.SquareSummableComplexInequalityWanted
