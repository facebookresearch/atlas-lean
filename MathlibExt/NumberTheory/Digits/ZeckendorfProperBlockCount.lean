/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.ZeckendorfBlockCountRecurrence

/-!
# Counting proper Zeckendorf blocks

A proper block on a fixed interval is determined by its last digit.
The theorem `ncard_properLStarBlock` counts the possible values of this digit.

## References

* Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
  pp. 1–45, Definition 17 and Lemma 15.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Proper $L^*$-blocks.** Let $L$ be a list of natural numbers. Lean's zero-based interval
$[s, k]$ corresponds to Chang's $[s+1, k+1]$. Let $B$ be the maximal block starting at Lean index
$s$, so $B_i$ is the entry of Chang's $\bar\beta^{s+1}$ at index $i+1$.
A function $\zeta : \mathbb N \to \mathbb N$ is a proper $L^*$-block with support interval $[s, k]$
when $s \le k$, $\zeta_i = B_i$ for all $i < k$, $\zeta_k < B_k$, and $\zeta_i = 0$ for all
$i > k$. Since $B$ vanishes below $s$, so does $\zeta$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Section 2 (arXiv:2308.12872v1, Section 2.3). -/
public def IsProperLStarBlock (L : List ℕ) (ζ : ℕ → ℕ) (s k : ℕ) : Prop :=
  s ≤ k ∧ (∀ i, i < k → ζ i = maxLStarBlock L s i) ∧ ζ k < maxLStarBlock L s k ∧
    ∀ i, k < i → ζ i = 0

/-- **Proper blocks by their support and digits.** A proper $L^*$-block on `[s, k]` has
ordered endpoints, support contained in `[s, k]`, the maximal block's digits on `[s, k)`,
and a strictly smaller digit at `k`; these conditions also suffice. -/
public theorem isProperLStarBlock_iff {L : List ℕ} {ζ : ℕ → ℕ} {s k : ℕ} :
    IsProperLStarBlock L ζ s k ↔
      s ≤ k ∧ Set.EqOn ζ (maxLStarBlock L s) (Set.Ico s k) ∧ ζ k < maxLStarBlock L s k ∧
        Function.support ζ ⊆ Set.Icc s k := by
  constructor
  · rintro ⟨hsk, hbefore, hdigit, hafter⟩
    refine ⟨hsk, fun _ h => hbefore _ h.2, hdigit, fun i hi => ⟨?_, ?_⟩⟩
    · exact le_of_not_gt fun h => hi ((hbefore i (h.trans_le hsk)).trans (maxLStarBlock_of_lt h))
    · exact le_of_not_gt fun h => hi (hafter i h)
  · rintro ⟨hsk, hprefix, hdigit, hsupport⟩
    have hzero : ∀ i ∉ Set.Icc s k, ζ i = 0 :=
      fun i hi => not_not.mp fun hn => hi (hsupport hn)
    refine ⟨hsk, fun i hi => ?_, hdigit, fun i hi => hzero i fun h => hi.not_ge h.2⟩
    by_cases hs : s ≤ i
    · exact hprefix ⟨hs, hi⟩
    · exact (hzero i fun h => hs h.1).trans (maxLStarBlock_of_lt (lt_of_not_ge hs)).symm

-- The source's length and leading-digit hypotheses are unnecessary for counting a single block.
set_option linter.unusedVariables false in
/-- **Number of proper $L^*$-blocks with a given support interval.** Let
$L = (e_1, \dots, e_N)$ be a list of natural numbers with $N \ge 2$ and $e_1 \ne 0$, let $s \le k$
be natural numbers, and let $j$ be the integer with $1 \le j \le N$ and
$k - s + 1 \equiv j \pmod N$. Then there are exactly $e_j$ proper $L^*$-blocks with support
interval $[s, k]$ in Lean's zero-based indexing, corresponding to $[s+1, k+1]$ in Chang's indexing.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 15 (`integers-2025-A25-lem-15`; arXiv:2308.12872v1, Section 4.1). -/
public theorem ncard_properLStarBlock (L : List ℕ) (hL : 2 ≤ L.length)
    (he : L.getD 0 0 ≠ 0) {s k : ℕ} (hsk : s ≤ k) :
    {ζ : ℕ → ℕ | IsProperLStarBlock L ζ s k}.ncard = L.getD ((k - s) % L.length) 0 := by
  have hk : maxLStarBlock L s k = L.getD ((k - s) % L.length) 0 := by
    simp [maxLStarBlock, Nat.not_lt.mpr hsk]
  rw [← hk]
  let block (d i : ℕ) := if i < k then maxLStarBlock L s i else if i = k then d else 0
  apply Set.ncard_eq_of_bijective (fun d _ => block d)
  · rintro ζ ⟨_, hbefore, hd, hafter⟩
    refine ⟨ζ k, hd, ?_⟩
    funext i
    rcases lt_trichotomy i k with hi | rfl | hi
    · simp [block, hi, hbefore i hi]
    · simp [block]
    · simp [block, Nat.not_lt.mpr hi.le, hi.ne', hafter i hi]
  · intro d hd
    exact ⟨hsk, fun i hi => by simp [block, hi], by simpa [block] using hd,
      fun i hi => by simp [block, Nat.not_lt.mpr hi.le, hi.ne']⟩
  · intro d e _ _ h
    simpa [block] using congrFun h k

end

end MetaMathlibExt
