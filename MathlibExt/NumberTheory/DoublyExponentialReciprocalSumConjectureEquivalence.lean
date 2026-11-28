/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DoublyExponentialReciprocalSum
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import MathlibExt.NumberTheory.DoublyExponentialReciprocalSumExistsTailEqPseudoGreedyExpansion

/-!
# Equivalence of Koizumi's conjecture and the Erdős–Graham question

For positive rational inputs whose pseudo-greedy gaps tend to zero, eventual vanishing
of the gaps is equivalent to an eventual Sylvester recurrence for every sequence of
positive integers whose square ratio tends to one and whose reciprocal series converges
to a rational number. This equivalence does not assert either of the two statements.

In the forward direction, subtract the finite reciprocal prefix to obtain a positive
rational tail sum and apply the pseudo-greedy expansion recurrence with zero gaps.
In the reverse direction, compare the two recurrences: once the Sylvester recurrence
holds, the absolute gaps are eventually nondecreasing, so convergence to zero forces
them to vanish. This uses the recurrence from the paper without the integer remainder
estimates used there in the reverse direction. Indices start at zero.

## References

* Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential Sequences*,
  *INTEGERS* 26 (2026), Article A28, pp. 1–17, Theorem 3 (pp. 12–13), with Conjecture 1
  and Question 1; the proof uses Corollary 3 and Lemmas 1–2.
  <https://math.colgate.edu/~integers/aa28/aa28.pdf>
* P. Erdős and R. L. Graham, *Old and new problems and results in combinatorial number theory*,
  Université de Genève, L’Enseignement Mathématique, Geneva, 1980, cited for Question 1.
-/

open Filter Topology

namespace MetaMathlibExt

/-- **Koizumi's conjecture is equivalent to the Erdős–Graham question.** The following are
equivalent. (1) For every positive rational number $r$ whose pseudo-greedy gap sequence
$(\varepsilon_n)_{n \ge 0}$ tends to $0$, we have $\varepsilon_n = 0$ for all sufficiently large
$n$. (2) Every sequence $(a_n)_{n \ge 0}$ of positive integers with $a_n^2 / a_{n+1} \to 1$ such
that $\sum_n 1 / a_n$ converges to a rational number satisfies $a_{n+1} = a_n^2 - a_n + 1$ for
all sufficiently large $n$.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Theorem 3, with Conjecture 1 and Question 1
(`integers-2026-A28-thm-3`). -/
public theorem pseudoGreedy_conjecture_iff_erdos_graham_question :
    (∀ r : ℚ, 0 < r → Tendsto (pseudoGreedyGap r) atTop (𝓝 0) →
        ∀ᶠ n in atTop, pseudoGreedyGap r n = 0) ↔
      ∀ a : ℕ → ℕ, (∀ n, 0 < a n) →
        Tendsto (fun n => (a n : ℝ) ^ 2 / a (n + 1)) atTop (𝓝 1) →
        (∃ q : ℚ, HasSum (fun n => 1 / (a n : ℝ)) q) →
        ∀ᶠ n in atTop, a (n + 1) = a n ^ 2 - a n + 1 := by
  constructor
  · rintro hconj a hpos hratio ⟨q, hsum⟩
    obtain ⟨N, hexp, hgap⟩ := exists_tail_eq_pseudoGreedyExpansion hpos hratio hsum.summable
    let r : ℚ := q - ∑ k ∈ Finset.range N, 1 / (a k : ℚ)
    have htail : HasSum (fun k => 1 / (a (N + k) : ℝ)) (r : ℝ) := by
      simpa only [r, Rat.cast_sub, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
        Nat.add_comm N] using (hasSum_nat_add_iff' N).mpr hsum
    have hr : 0 < (r : ℝ) := by
      rw [← htail.tsum_eq]
      exact htail.summable.tsum_pos (fun k => by positivity) 0
        (one_div_pos.mpr (Nat.cast_pos.mpr (hpos _)))
    rw [htail.tsum_eq] at hexp hgap
    have hzero := hconj r (by exact_mod_cast hr) hgap
    obtain ⟨M, hM⟩ := eventually_atTop.mp hzero
    refine eventually_atTop.mpr ⟨N + M, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show N ≤ n by omega)
    have hk : M ≤ k := by omega
    have h := pseudoGreedyExpansion_succ_eq hr k
    rw [hM k hk, hM (k + 1) (by omega), sub_zero, div_one, one_mul,
      ← hexp k, ← hexp (k + 1), Int.cast_natCast, Int.cast_natCast, ← Nat.add_assoc] at h
    apply (Nat.cast_inj (R := ℝ)).mp
    simpa only [Nat.cast_add, Nat.cast_sub (Nat.le_self_pow two_ne_zero _), Nat.cast_pow,
      Nat.cast_one] using h
  · intro hquestion r hr he
    have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
    let a (n : ℕ) := (pseudoGreedyExpansion (r : ℝ) n).toNat
    let e := pseudoGreedyGap (r : ℝ)
    have ha (n : ℕ) : 0 < a n := by
      dsimp only [a]
      have := pseudoGreedyExpansion_pos hr' n
      omega
    have hcast (n : ℕ) : (a n : ℝ) = (pseudoGreedyExpansion (r : ℝ) n : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (pseudoGreedyExpansion_pos hr' n).le]
    have hsum : HasSum (fun n => 1 / (a n : ℝ)) (r : ℝ) := by
      simpa only [hcast] using hasSum_one_div_pseudoGreedyExpansion hr'
    have hrec (n : ℕ) : (a (n + 1) : ℝ) = (a n : ℝ) ^ 2 / (1 - e n) - a n +
        (1 - e (n + 1)) := by
      simpa only [hcast, e, one_div_mul_eq_div] using pseudoGreedyExpansion_succ_eq hr' n
    have hu := hsum.summable.tendsto_atTop_zero
    have hden : Tendsto (fun n => 1 - e n) atTop (𝓝 1) := by
      simpa only [sub_zero] using he.const_sub 1
    have hdenPos : ∀ᶠ n in atTop, 0 < 1 - e n := hden.eventually (eventually_gt_nhds zero_lt_one)
    have hnormalized : Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1) := by
      have h := ((hden.inv₀ one_ne_zero).sub hu).add
        ((hden.comp (tendsto_add_atTop_nat 1)).mul (hu.pow 2))
      simp only [inv_one, sub_zero, zero_pow two_ne_zero, mul_zero, add_zero] at h
      refine h.congr' ?_
      filter_upwards [hdenPos] with n hn
      change (1 - e n)⁻¹ - 1 / (a n : ℝ) + (1 - e (n + 1)) * (1 / (a n : ℝ)) ^ 2 = _
      rw [hrec]
      have hane : (a n : ℝ) ≠ 0 := (Nat.cast_pos.mpr (ha n)).ne'
      field_simp [hane, hn.ne']
    have hratio : Tendsto (fun n => (a n : ℝ) ^ 2 / a (n + 1)) atTop (𝓝 1) := by
      simpa only [Function.comp_apply, inv_div, inv_one] using hnormalized.inv₀ one_ne_zero
    have hsyl := hquestion a ha hratio ⟨r, hsum⟩
    have hstep : ∀ᶠ n in atTop, |e n| ≤ |e (n + 1)| := by
      have hbig := hu.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
      have hsmall := hden.eventually (eventually_lt_nhds (one_lt_two : (1 : ℝ) < 2))
      filter_upwards [hsyl, hdenPos, hbig, hsmall] with n hn hd hbn hen
      have hapos : (0 : ℝ) < a n := Nat.cast_pos.mpr (ha n)
      have htwo : (2 : ℝ) < a n := (one_div_lt_one_div hapos zero_lt_two).mp hbn
      have hfactor : 1 ≤ (a n : ℝ) ^ 2 / (1 - e n) :=
        (le_div_iff₀ hd).mpr (by nlinarith only [htwo, hen, sq_nonneg ((a n : ℝ) - 2)])
      have hsylReal : (a (n + 1) : ℝ) = (a n : ℝ) ^ 2 - a n + 1 := by
        simpa only [Nat.cast_add, Nat.cast_sub (Nat.le_self_pow two_ne_zero _), Nat.cast_pow,
          Nat.cast_one] using congrArg (fun x : ℕ => (x : ℝ)) hn
      have heq : e (n + 1) = ((a n : ℝ) ^ 2 / (1 - e n)) * e n := by
        have hx : (a n : ℝ) ^ 2 / (1 - e n) - (a n : ℝ) ^ 2 =
            ((a n : ℝ) ^ 2 / (1 - e n)) * e n := by
          field_simp [hd.ne']
          ring
        linarith only [hrec n, hsylReal, hx]
      rw [heq, abs_mul, abs_of_nonneg (zero_le_one.trans hfactor)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor (abs_nonneg (e n))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hstep
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have hmono : Monotone (fun k : ℕ => |e (k + n)|) := monotone_nat_of_le_succ fun k => by
      rw [Nat.succ_add]
      exact hN (k + n) (by omega)
    have hshift : Tendsto (fun k : ℕ => e (k + n)) atTop (𝓝 0) :=
      he.comp (tendsto_add_atTop_nat n)
    have habs : Tendsto (fun k : ℕ => |e (k + n)|) atTop (𝓝 0) := by
      simpa only [abs_zero] using hshift.abs
    have hle : |e n| ≤ 0 := ge_of_tendsto' habs fun k => by
      simpa only [Nat.zero_add] using hmono (Nat.zero_le k)
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))

end MetaMathlibExt
