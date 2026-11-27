/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ExactSlowNimRemoteness
import all MathlibExt.GameTheory.ExactSlowNimRemoteness

/-!
# Critical positions of Exact Slow Nim

Critical positions are precisely the basic vectors: the sum bounds fix their remoteness,
and parity rules out an all-even basic vector below a type (B) vector of the same level.

## References

* Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi,
  *On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024),
  Article G1, pp. 1–21, Theorem 1 and Lemma 4 (Section 2).
* C. A. B. Smith, *Graphs and composite games*, Journal of Combinatorial Theory 1 (1966),
  pp. 51–81. The remoteness function used here is credited to Smith in Section 1.3 of the
  preceding article.
* Vladimir Gurvich and Nhan Bao Ho, *Slow k-Nim*, RUTCOR Research Report 3 (2015),
  arXiv:1508.05777, Section 2. The preceding article credits this report for introducing the game.
-/

namespace MetaMathlibExt

open exactSlowNim_critical_of_even

-- The token mass of a basic vector falls strictly below the threshold for the next level.
private theorem basicValue_eq_of_basic {k m : ℕ} (hk : 0 < k) {x : Fin (k + 1) → ℕ}
    (hx : Basic k m x) : exactSlowNimBasicValue k x = m := by
  refine le_antisymm ?_ (le_value hk le_rfl hx)
  have hsum : ∑ i, x i < k * (m + 1) := by
    rw [Nat.mul_succ]
    rcases hx with hx | hx | hx <;> have := hx.1 <;> omega
  by_contra! h
  exact (not_lt_of_ge ((Nat.mul_le_mul_left k (Nat.succ_le_of_lt h)).trans
    (exactSlowNimBasicValue_of_supports_basicB.mul_value_le_sum hk x))) hsum

/-- **$m$-critical positions of exact slow $k$-NIM with $k + 1$ piles (Theorem 1).** Let $k \ge 1$
and $m$ be natural numbers, and let $x = (x_0, \dots, x_k)$ be a position of
$\mathrm{NIM}(k + 1, k)$, the game on $k + 1$ piles in which a move removes one stone from each
of exactly $k$ nonempty piles. Call $x$ $m$-critical when its Smith remoteness is $m$ and no
position $y < x$ (that is, $y_i \le x_i$ for every $i$ and $y \ne x$) has remoteness $m$. Then
$x$ is $m$-critical if and only if either
(A) $x_0 + \dots + x_k = km$, $x_i \le m$ for every $i$, every $x_i$ is even if $m$ is even,
and exactly one $x_i$ is even if $m$ is odd; or
(B) $x_0 + \dots + x_k = km + k - 1$, $x_i < m$ for every $i$, $m$ is even, and every $x_i$ is
odd.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 1. -/
public theorem isExactSlowNimCritical_iff {k : ℕ} (hk : 0 < k) (m : ℕ)
    (x : Fin (k + 1) → ℕ) :
    IsExactSlowNimCritical k m x ↔
      (∑ i, x i = k * m ∧ (∀ i, x i ≤ m) ∧ (Even m → ∀ i, Even (x i)) ∧
          (Odd m → ∃! i, Even (x i))) ∨
        (∑ i, x i = k * m + k - 1 ∧ (∀ i, x i < m) ∧ Even m ∧ ∀ i, Odd (x i)) := by
  have hbasic : Basic k m x ↔
      (∑ i, x i = k * m ∧ (∀ i, x i ≤ m) ∧ (Even m → ∀ i, Even (x i)) ∧
          (Odd m → ∃! i, Even (x i))) ∨ IsExactSlowNimBasicB k m x := by
    constructor
    · rintro (h | h | h)
      · exact Or.inl ⟨h.1, h.2.1, fun _ => h.2.2.2,
          fun hm => (Nat.not_even_iff_odd.mpr hm h.2.2.1).elim⟩
      · exact Or.inl ⟨h.1, h.2.1, fun hm => (Nat.not_even_iff_odd.mpr h.2.2.1 hm).elim,
          fun _ => h.2.2.2⟩
      · exact Or.inr h
    · rintro (⟨hsum, hcap, he, ho⟩ | h)
      · rcases Nat.even_or_odd m with hm | hm
        · exact Or.inl ⟨hsum, hcap, hm, he hm⟩
        · exact Or.inr (Or.inl ⟨hsum, hcap, hm, ho hm⟩)
      · exact Or.inr (Or.inr h)
  change IsExactSlowNimCritical k m x ↔ _ ∨ IsExactSlowNimBasicB k m x
  rw [← hbasic]
  constructor
  · intro hx
    obtain ⟨z, hzx, hz⟩ := exists_supports_exactSlowNimBasicValue k x
    rw [exactSlowNimBasicValue_eq_smithRemoteness hk, hx.1] at hz
    have hzx' : z = x := by
      by_contra hne
      have hzR := (exactSlowNimBasicValue_eq_smithRemoteness hk z).symm.trans
        (basicValue_eq_of_basic hk hz)
      exact hx.2 z (lt_of_le_of_ne hzx hne) hzR
    rwa [hzx'] at hz
  · intro hx
    refine ⟨(exactSlowNimBasicValue_eq_smithRemoteness hk x).symm.trans
      (basicValue_eq_of_basic hk hx), ?_⟩
    intro y hy hyR
    have hyv : exactSlowNimBasicValue k y = m :=
      (exactSlowNimBasicValue_eq_smithRemoteness hk y).trans hyR
    have hmass : k * m ≤ ∑ i, y i := by
      simpa only [hyv] using exactSlowNimBasicValue_of_supports_basicB.mul_value_le_sum hk y
    have hyx : ∑ i, y i < ∑ i, x i := by
      obtain ⟨i, hi⟩ := (Pi.lt_def.mp hy).2
      exact Finset.sum_lt_sum (fun j _ => hy.le j) ⟨i, Finset.mem_univ i, hi⟩
    rcases hx with ha | ha | hb
    · exact (not_lt_of_ge hmass) (hyx.trans_eq ha.1)
    · exact (critical_of_a1 hk ha).2 y hy hyR
    · obtain ⟨z, hzy, hz⟩ := exists_supports_exactSlowNimBasicValue k y
      rw [hyv] at hz
      rcases hz with ha | ha | hc
      · have hgap : ∑ i, (z i + 1) ≤ ∑ i, x i := by
          apply Finset.sum_le_sum
          intro i _
          apply lt_of_le_of_ne ((hzy.trans hy.le) i)
          intro heq
          exact Nat.not_even_iff_odd.mpr (hb.2.2.2 i) (heq ▸ ha.2.2.2 i)
        have hsum : k * m + (k + 1) ≤ k * m + k - 1 := by
          simpa [Finset.sum_add_distrib, ha.1, hb.1] using hgap
        omega
      · exact Nat.not_even_iff_odd.mpr ha.2.2.1 hb.2.2.1
      · have hsum := hyx.trans_eq (hb.1.trans hc.1.symm)
        exact (not_lt_of_ge (Finset.sum_le_sum fun i _ => hzy i)) hsum

end MetaMathlibExt
