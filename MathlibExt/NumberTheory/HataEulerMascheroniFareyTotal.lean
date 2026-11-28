/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import MathlibExt.NumberTheory.HataEulerMascheroniFarey
import all MathlibExt.NumberTheory.HataEulerMascheroniFareySum

/-!
# Hata's Farey formula for Euler's constant

For natural numbers $a, b, c, d$ with $bc = ad + 1$, $a > 0$, and $c \le d$, the interval
$[a/b, c/d]$ lies in a unique $[1/(n+1), 1/n]$ with $n \ge 1$. We sum the Farey terms in each
reciprocal interval, then telescope the sums over $n$ to obtain the formula for Euler's constant.

## References

* Nikita Kalinin, *A Short Telescoping Proof of Hata’s Formula for the Euler-Mascheroni
  Constant*, INTEGERS 25 (2025), Article A90, pp. 1–6, §2, Corollary 2, Lemma 3, and Theorem 1.
* Masayoshi Hata, *Farey fractions and sums over coprime pairs*, Acta Arithmetica 70 (1995),
  no. 2, pp. 149–159, Theorem 4.1.
* `MathlibExt.NumberTheory.HataEulerMascheroniFarey` supplies
  `farey_interval_subset_reciprocal_interval`; `MathlibExt.NumberTheory.HataEulerMascheroniFareySum`
  supplies `hasSum_farey_subintervals_reciprocal_interval` and its helpers `numerators_pos`,
  `inner_bounds` and `defect_nonneg`.
-/

namespace MetaMathlibExt

open Filter
open scoped BigOperators Topology

private abbrev PositiveFarey :=
  {(a, b, c, d) : Quad | b * c = a * d + 1 ∧ 0 < a ∧ c ≤ d}

private noncomputable def reciprocalPartition : (Σ k : ℕ, FareyNode (k + 1)) ≃ PositiveFarey := by
  let forget : (Σ k : ℕ, FareyNode (k + 1)) → PositiveFarey := fun ⟨k, q⟩ ↦
    ⟨q.val, by
      obtain ⟨⟨a, b, c, d⟩, h⟩ := q
      exact ⟨h.1, (numerators_pos h).1, (Nat.le_mul_of_pos_left c (Nat.succ_pos k)).trans h.2.2⟩⟩
  refine Equiv.ofBijective forget ⟨?_, ?_⟩
  · rintro ⟨k, ⟨⟨a, b, c, d⟩, hk⟩⟩ ⟨l, ⟨⟨a', b', c', d'⟩, hl⟩⟩ h
    have hv := congrArg Subtype.val h
    change (a, b, c, d) = (a', b', c', d') at hv
    simp only [Prod.mk.injEq] at hv
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hv
    have index {n : ℕ} (hn : InReciprocal n (a, b, c, d)) : d / c = n :=
      Nat.div_eq_of_lt_le hn.2.2 (inner_bounds hn).2
    obtain rfl : k = l := Nat.succ.inj ((index hk).symm.trans (index hl))
    rfl
  · rintro ⟨⟨a, b, c, d⟩, hdet, ha, hcd⟩
    obtain ⟨n, hn, h₁, h₂⟩ := farey_interval_subset_reciprocal_interval ha hcd hdet
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hbc : 0 < b * c := hdet ▸ Nat.succ_pos _
    have hb : 0 < b := Nat.pos_of_mul_pos_right hbc
    have hd : 0 < d := (Nat.pos_of_mul_pos_left hbc).trans_le hcd
    rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hb), one_mul] at h₁
    rw [div_le_div_iff₀ (by exact_mod_cast hd) (by positivity), one_mul] at h₂
    refine ⟨⟨k, ⟨(a, b, c, d), hdet, ?_, ?_⟩⟩, rfl⟩
    · rw [mul_comm] at h₁
      exact_mod_cast h₁
    · rw [mul_comm] at h₂
      exact_mod_cast h₂

private noncomputable def reciprocalSum (k : ℕ) : ℝ :=
  1 / (k + 1) + 1 / (k + 1 + 1) - 2 * Real.log ((k + 1 + 1) / (k + 1))

private theorem hasSum_defect_reciprocalSum (k : ℕ) :
    HasSum (@defect (k + 1)) (reciprocalSum k) := by
  have h := hasSum_farey_subintervals_reciprocal_interval (n := k + 1) (Nat.succ_pos k)
  change HasSum (@defect (k + 1)) _ at h
  simpa only [reciprocalSum, Nat.cast_add, Nat.cast_one] using h

private theorem hasSum_reciprocalSum :
    HasSum reciprocalSum (2 * Real.eulerMascheroniConstant - 1) := by
  have hnonneg (k : ℕ) : 0 ≤ reciprocalSum k := (hasSum_defect_reciprocalSum k).nonneg defect_nonneg
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  let g (k : ℕ) : ℝ := 2 * ((harmonic k : ℝ) - Real.log ((k : ℝ) + 1)) + 1 / ((k : ℝ) + 1)
  have hg (k : ℕ) : reciprocalSum k = g (k + 1) - g k := by
    simp only [reciprocalSum, g, harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast,
      Nat.cast_add, Nat.cast_one]
    rw [Real.log_div (by positivity) (by positivity), one_div]
    ring
  simp only [hg, Finset.sum_range_sub]
  have hg₀ : g 0 = 1 := by simp [g]
  rw [hg₀]
  have h := (Real.tendsto_harmonic_sub_log_add_one.const_mul 2).add
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [g, add_zero] using h.sub_const 1

/-- **Hata's formula for Euler's constant.** Let $S$ be the set of quadruples $(a, b, c, d)$ of
natural numbers with $bc = ad + 1$, $a > 0$ and $c \le d$; these are the Farey intervals
$[a/b, c/d] \subseteq [0, 1]$ with positive left endpoint. The family
$1/(abcd(a + c)(b + d))$, indexed by $(a, b, c, d) \in S$, is summable, and Euler's constant
$\gamma$ satisfies
$$
\gamma = \frac{1}{2} + \frac{1}{2} \sum_{(a, b, c, d) \in S} \frac{1}{abcd(a + c)(b + d)}.
$$

The set $S$ is the source's $F \setminus F^*$, where $F^*$ consists of the intervals $[0/1, 1/n]$.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Theorem 1, attributed there to
Hata. -/
public theorem euler_mascheroni_eq_hata_farey_sum :
    Summable
        (fun q : {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | b * c = a * d + 1 ∧ 0 < a ∧ c ≤ d} =>
          match q.1 with
          | (a, b, c, d) => (1 : ℝ) / (a * b * c * d * (a + c) * (b + d))) ∧
      Real.eulerMascheroniConstant =
        1 / 2 + 1 / 2 * ∑' q : {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | b * c = a * d + 1 ∧ 0 < a ∧ c ≤ d},
          match q.1 with
          | (a, b, c, d) => (1 : ℝ) / (a * b * c * d * (a + c) * (b + d)) := by
  let f : PositiveFarey → ℝ := fun q ↦ match q.1 with
    | (a, b, c, d) => (1 : ℝ) / (a * b * c * d * (a + c) * (b + d))
  let totalTerm (q : Σ k : ℕ, FareyNode (k + 1)) := defect q.2
  have hsum : HasSum totalTerm (2 * Real.eulerMascheroniConstant - 1) :=
    hasSum_reciprocalSum.sigma_of_hasSum (f := totalTerm) hasSum_defect_reciprocalSum <|
      (summable_sigma_of_nonneg (f := totalTerm) (fun q ↦ defect_nonneg q.2)).mpr
        ⟨fun k ↦ (hasSum_defect_reciprocalSum k).summable,
          by simpa only [totalTerm, (hasSum_defect_reciprocalSum _).tsum_eq] using
            hasSum_reciprocalSum.summable⟩
  have htotal : HasSum f (2 * Real.eulerMascheroniConstant - 1) := by
    apply (reciprocalPartition.hasSum_iff (f := f)).mp
    have hcomp : f ∘ reciprocalPartition = totalTerm := by
      funext q
      obtain ⟨k, ⟨⟨a, b, c, d⟩, h⟩⟩ := q
      rfl
    rwa [hcomp]
  refine ⟨htotal.summable, ?_⟩
  simp only [Nat.cast_one, Nat.cast_ofNat]
  change Real.eulerMascheroniConstant = (1 : ℝ) / 2 + (1 : ℝ) / 2 * ∑' q, f q
  rw [htotal.tsum_eq]
  ring

end MetaMathlibExt
