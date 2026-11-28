/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import MathlibExt.NumberTheory.DoublyExponentialReciprocalSumExistsTailEqPseudoGreedyExpansion

/-!
# Countable exceptions for doubly exponential reciprocal sums

For real bases `α > 1`, consider sequences of positive integers whose ratio to
`⌊α ^ 2 ^ (n + 1)⌋₊` tends to `1`. The bases admitting such a sequence with rational
reciprocal sum form a countable set. The index starts at `0`, and `HasSum` records
convergence to the rational value.

## References

* Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
  Sequences*, *INTEGERS* 26 (2026), Article A28, pp. 1–17, Theorem 2 (pp. 3 and 8)
  and Corollary 3 (p. 9).
  <https://math.colgate.edu/~integers/aa28/aa28.pdf>
* The proof uses `MetaMathlibExt.exists_tail_eq_pseudoGreedyExpansion` from
  `MathlibExt.NumberTheory.DoublyExponentialReciprocalSumExistsTailEqPseudoGreedyExpansion`.
-/

open Filter Topology

namespace MetaMathlibExt

/-- **Doubly exponential floors are Type 2 irrationality sequences for all but countably many
bases.** For all real numbers $\alpha > 1$ outside a countable set, the sequence
$(\lfloor \alpha^{2^{n+1}} \rfloor)_{n \ge 0}$ is a Type 2 irrationality sequence: for every
sequence $(b_n)_{n \ge 0}$ of positive integers with $b_n / \lfloor \alpha^{2^{n+1}} \rfloor \to 1$,
the series $\sum_n 1 / b_n$ does not converge to a rational number.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Theorem 2 and the definition of Type 2
irrationality sequences preceding it (`integers-2026-A28-thm-2`). -/
public theorem countable_not_type2IrrationalitySequence_floor_pow_two_pow :
    Set.Countable {α : ℝ | 1 < α ∧ ¬∀ b : ℕ → ℕ, (∀ n, 0 < b n) →
      Tendsto (fun n => (b n : ℝ) / ⌊α ^ 2 ^ (n + 1)⌋₊) atTop (𝓝 1) →
        ∀ q : ℚ, ¬HasSum (fun n => 1 / (b n : ℝ)) q} := by
  have hpowTop : Tendsto (fun n : ℕ => (2 : ℕ) ^ (n + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ))).comp
      (tendsto_add_atTop_nat 1)
  -- A given tail can be asymptotic to the powers of at most one base greater than one.
  have base_le {u : ℕ → ℝ} {N : ℕ} {α β : ℝ} (hα : 1 < α) (hβ : 1 < β)
      (ha : Tendsto (fun n => u n / α ^ 2 ^ (N + n + 1)) atTop (𝓝 1))
      (hb : Tendsto (fun n => u n / β ^ 2 ^ (N + n + 1)) atTop (𝓝 1)) : β ≤ α := by
    by_contra! hlt
    have hu : ∀ᶠ n in atTop, 0 < u n / α ^ 2 ^ (N + n + 1) :=
      ha.eventually (eventually_gt_nhds zero_lt_one)
    have hquot : Tendsto (fun n : ℕ => (α / β) ^ 2 ^ (N + n + 1)) atTop (𝓝 1) := by
      have h := hb.div ha one_ne_zero
      rw [div_one] at h
      apply h.congr'
      filter_upwards [hu] with n hn
      have hne : u n ≠ 0 := by
        intro hz
        simp [hz] at hn
      exact (div_div_div_cancel_left₀ _ _ hne).trans (div_pow ..).symm
    have he : Tendsto (fun n : ℕ => (2 : ℕ) ^ (N + n + 1)) atTop atTop := by
      simpa only [Function.comp_def, Nat.add_comm N] using hpowTop.comp (tendsto_add_atTop_nat N)
    have hzero := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ α / β)
      ((div_lt_one (zero_lt_one.trans hβ)).mpr hlt)).comp he
    exact zero_ne_one (tendsto_nhds_unique hzero hquot)
  let bases : ℕ × ℚ → Set ℝ := fun p => {α | 1 < α ∧ Tendsto
    (fun n => (pseudoGreedyExpansion (p.2 : ℝ) n : ℝ) / α ^ 2 ^ (p.1 + n + 1)) atTop (𝓝 1)}
  have hcount (p : ℕ × ℚ) : (bases p).Countable := by
    refine Set.Subsingleton.countable ?_
    rintro α ⟨hα, ha⟩ β ⟨hβ, hb⟩
    exact le_antisymm (base_le hβ hα hb ha) (base_le hα hβ ha hb)
  refine (Set.countable_iUnion hcount).mono ?_
  intro α h
  simp only [Set.mem_ofPred_eq, not_forall, not_not] at h
  obtain ⟨hα, b, hpos, hfloor, q, hsum⟩ := h
  have htop : Tendsto (fun n : ℕ => α ^ 2 ^ (n + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hα).comp hpowTop
  have hpow : Tendsto (fun n => (b n : ℝ) / α ^ 2 ^ (n + 1)) atTop (𝓝 1) := by
    have h := hfloor.mul (tendsto_nat_floor_div_atTop.comp htop)
    rw [mul_one] at h
    refine h.congr fun n => ?_
    change _ / (⌊α ^ 2 ^ (n + 1)⌋₊ : ℝ) * (⌊α ^ 2 ^ (n + 1)⌋₊ / _) = _
    have hfloorPos : 0 < ⌊α ^ 2 ^ (n + 1)⌋₊ := Nat.floor_pos.mpr (one_le_pow₀ hα.le)
    exact div_mul_div_cancel₀ (by exact_mod_cast hfloorPos.ne')
  have hratio : Tendsto (fun n => (b n : ℝ) ^ 2 / b (n + 1)) atTop (𝓝 1) := by
    have h := (hpow.pow 2).div (hpow.comp (tendsto_add_atTop_nat 1)) one_ne_zero
    rw [one_pow, div_one] at h
    refine h.congr fun n => ?_
    change ((b n : ℝ) / α ^ 2 ^ (n + 1)) ^ 2 / ((b (n + 1) : ℝ) / α ^ 2 ^ (n + 1 + 1)) = _
    rw [pow_succ (2 : ℕ) (n + 1), pow_mul, div_pow, div_div_div_cancel_right₀ (by positivity)]
  obtain ⟨N, htail, -⟩ := exists_tail_eq_pseudoGreedyExpansion hpos hratio hsum.summable
  -- Subtract the finite prefix in ℚ so that the parameter of the expansion is rational.
  let r : ℚ := q - ∑ k ∈ Finset.range N, 1 / (b k : ℚ)
  have hr : (r : ℝ) = ∑' k, 1 / (b (N + k) : ℝ) := by
    have h := ((hasSum_nat_add_iff' N).mpr hsum).tsum_eq
    simpa only [r, Rat.cast_sub, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
      Nat.add_comm N] using h.symm
  rw [← hr] at htail
  refine Set.mem_iUnion.mpr ⟨(N, r), hα, ?_⟩
  refine (hpow.comp (tendsto_add_atTop_nat N)).congr fun n => ?_
  change (b (n + N) : ℝ) / α ^ 2 ^ (n + N + 1) = _
  rw [Nat.add_comm n N]
  exact congrArg (fun x : ℝ => x / α ^ 2 ^ (N + n + 1)) (by exact_mod_cast htail n)

end MetaMathlibExt
