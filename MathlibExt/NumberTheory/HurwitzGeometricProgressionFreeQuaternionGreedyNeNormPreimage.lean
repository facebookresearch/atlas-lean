/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Quaternion
import Mathlib.Data.Nat.Squarefree
import MathlibExt.NumberTheory.HurwitzQuaternionGreedy
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The quaternion greedy set is not determined by norms

The scalar quaternion `7` and the square of `2 + i + j + k` have the same norm,
but only the former belongs to the quaternion greedy set. Hence this set is not
the norm preimage of any set of positive integers.

Source: Megumi Asada, Bruce Fang, Eva Fourakis, Sarah Manski, Nathan McNew, Steven J. Miller,
Gwyneth Moreland, Ajmain Yamin, and Sindy Xin Zhang, *Avoiding 3-Term Geometric Progressions
in Hurwitz Quaternions*, Journal of Integer Sequences 27 (2024), Article 24.7.7
(arXiv:1807.07605), Proposition 18.
-/

namespace MetaMathlibExt

set_option quotPrecheck false in
local notation "𝐇" => Set.ofPred fun q : Quaternion ℚ =>
  (∃ a b c d : ℤ,
    q.re = (a : ℚ) ∧ q.imI = (b : ℚ) ∧ q.imJ = (c : ℚ) ∧ q.imK = (d : ℚ)) ∨
  (∃ a b c d : ℤ,
    q.re = (a : ℚ) + 1 / 2 ∧ q.imI = (b : ℚ) + 1 / 2 ∧
      q.imJ = (c : ℚ) + 1 / 2 ∧ q.imK = (d : ℚ) + 1 / 2)

set_option quotPrecheck false in
/-- Hurwitz quaternions whose norms lie in a set of natural numbers. -/
local notation "𝐒ᴳ" G:max => Set.ofPred fun q : Quaternion ℚ =>
  q ∈ 𝐇 ∧ ∃ n ∈ G, Quaternion.normSq q = ((n : ℕ) : ℚ)

set_option quotPrecheck false in
local notation "IsQuaternionGreedy" Gq:max => ∀ q : Quaternion ℚ, q ∈ Gq ↔
  (q ∈ 𝐇 ∧ q ≠ 0 ∧ ¬ ∃ a ∈ Gq, ∃ r ∈ 𝐇, r ≠ 0 ∧ Quaternion.normSq r ≠ 1 ∧
    a * r ∈ Gq ∧ q = a * r ^ 2)

private theorem twice_re_int (q : Quaternion ℚ) (hq : q ∈ 𝐇) :
    ∃ a : ℤ, 2 * q.re = (a : ℚ) := by
  rcases hq with ⟨a, b, c, d, ha, hb, hc, hd⟩ | ⟨a, b, c, d, ha, hb, hc, hd⟩
  · exact ⟨2 * a, by simp [ha]⟩
  · refine ⟨2 * a + 1, ?_⟩
    push_cast
    rw [ha]
    ring

private theorem three_sq_ne_seven (a b c : ℤ) : a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by
  intro h
  have ha : -2 ≤ a ∧ a ≤ 2 := by
    constructor <;> nlinarith [sq_nonneg b, sq_nonneg c]
  have hb : -2 ≤ b ∧ b ≤ 2 := by
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg c]
  have hc : -2 ≤ c ∧ c ≤ 2 := by
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  obtain ⟨ha₁, ha₂⟩ := ha
  obtain ⟨hb₁, hb₂⟩ := hb
  obtain ⟨hc₁, hc₂⟩ := hc
  interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num at h

private theorem seven_not_unit_mul_sq :
    ¬ ∃ U ∈ 𝐇, Quaternion.normSq U = 1 ∧
      ∃ R ∈ 𝐇, Quaternion.normSq R = ((7 : ℕ) : ℚ) ∧
        (7 : Quaternion ℚ) = U * R ^ 2 := by
  rintro ⟨U, hU, hUn, R, hR, hRn, heq⟩
  have hs : R ^ 2 = star U * (7 : Quaternion ℚ) := by
    calc
      R ^ 2 = (star U * U) * R ^ 2 := by
        rw [Quaternion.star_mul_self, hUn]
        simp
      _ = star U * (U * R ^ 2) := mul_assoc _ _ _
      _ = star U * 7 := by rw [← heq]
  have hreal := congrArg (fun q : Quaternion ℚ => q.re) hs
  simp only [pow_two, Quaternion.re_mul, Quaternion.re_star, QuaternionAlgebra.re_ofNat,
    QuaternionAlgebra.imI_star, QuaternionAlgebra.imI_ofNat, mul_zero, sub_zero,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_star,
    QuaternionAlgebra.imK_ofNat] at hreal
  have hn := hRn
  rw [Quaternion.normSq_def'] at hn
  norm_num at hn
  have hu := hUn
  rw [Quaternion.normSq_def'] at hu
  obtain ⟨k, hk⟩ := twice_re_int U hU
  obtain ⟨t, ht⟩ := twice_re_int R hR
  have hid : t ^ 2 = 7 * (k + 2) := by
    have h : (t : ℚ) ^ 2 = 7 * ((k : ℚ) + 2) := by
      nlinarith [congrArg (fun x : ℚ => x ^ 2) ht]
    exact_mod_cast h
  have hkb : -2 ≤ k ∧ k ≤ 2 := by
    have h : (-2 : ℚ) ≤ k ∧ (k : ℚ) ≤ 2 := by
      constructor <;> nlinarith [sq_nonneg U.imI, sq_nonneg U.imJ, sq_nonneg U.imK]
    exact_mod_cast h
  have htb : -5 ≤ t ∧ t ≤ 5 := by
    constructor <;> nlinarith
  obtain ⟨hk₁, hk₂⟩ := hkb
  obtain ⟨ht₁, ht₂⟩ := htb
  have ht0 : t = 0 := by
    interval_cases t <;> first | rfl | (interval_cases k <;> norm_num at hid)
  have hr0 : R.re = 0 := by
    rw [ht0] at ht
    norm_num at ht
    linarith
  rcases hR with ⟨a, b, c, d, ha, hb, hc, hd⟩ | ⟨a, b, c, d, ha, hb, hc, hd⟩
  · have h : b ^ 2 + c ^ 2 + d ^ 2 = 7 := by
      have hq : (b : ℚ) ^ 2 + (c : ℚ) ^ 2 + (d : ℚ) ^ 2 = 7 := by
        simpa [hr0, hb, hc, hd] using hn
      exact_mod_cast hq
    exact three_sq_ne_seven b c d h
  · have h : (2 * a + 1 : ℤ) = 0 := by
      have hq : (2 * a + 1 : ℤ) = (0 : ℚ) := by
        push_cast
        linarith
      exact_mod_cast hq
    omega

private theorem mem_of_squarefree_norm (Gq : Set (Quaternion ℚ)) (hGq : IsQuaternionGreedy Gq)
    (q : Quaternion ℚ) (hq : q ∈ 𝐇) (n : ℕ) (hn : Squarefree n)
    (hqn : Quaternion.normSq q = (n : ℚ)) : q ∈ Gq := by
  refine (hGq q).2 ⟨hq, ?_, ?_⟩
  · apply Quaternion.normSq_ne_zero.mp
    rw [hqn]
    exact_mod_cast hn.ne_zero
  · rintro ⟨a, ha, r, hr, _, hr1, _, heq⟩
    obtain ⟨m, k, -, hk, hnk⟩ := hurwitz_normSq_eq_mul_sq heq hqn ((hGq a).1 ha).1 hr
    have hdvd : k * k ∣ n := ⟨m, by simpa [pow_two, mul_comm] using hnk⟩
    have hk1 : k = 1 := Nat.isUnit_iff.mp (hn k hdvd)
    exact hr1 (by simpa [hk1] using hk)

/-- **The quaternion greedy set is not determined by norms.** A Hurwitz quaternion is a quaternion
whose four rational coordinates are either all integers or all halves of odd integers; the norm
$\mathrm{Nm}(q)$ of a quaternion $q$ is the sum of the squares of its coordinates. Let
$\mathcal{G}$ be a set of quaternions such that a quaternion $q$ lies in $\mathcal{G}$ if and only
if $q$ is a nonzero Hurwitz quaternion and there are no $a \in \mathcal{G}$ and Hurwitz quaternion
$r \ne 0$ with norm $\mathrm{Nm}(r) \ne 1$, $ar \in \mathcal{G}$ and $q = ar^2$ (this recursion on
the norm characterizes the quaternion greedy set). Then for every set $G$ of positive integers,
$\mathcal{G}$ is not the set of Hurwitz quaternions whose norm lies in $G$.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Proposition 18. -/
public theorem quaternionGreedy_ne_norm_preimage
    (Gq : Set (Quaternion ℚ)) (hGq : IsQuaternionGreedy Gq) (G : Set ℕ)
    (hG : ∀ n ∈ G, 0 < n) :
    Gq ≠ 𝐒ᴳ G := by
  intro heq
  have hSeven : (7 : Quaternion ℚ) ∈ 𝐇 := Or.inl ⟨7, 0, 0, 0, rfl, rfl, rfl, rfl⟩
  have hSevenNorm : Quaternion.normSq (7 : Quaternion ℚ) = ((7 ^ 2 : ℕ) : ℚ) := by
    norm_num [Quaternion.normSq_def', QuaternionAlgebra.re_ofNat,
      QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
  have hSevenG := (quaternionGreedy_mem_of_not_unit_mul_sq Gq hGq 7 (by decide)
    7 hSeven hSevenNorm seven_not_unit_mul_sq).1.1
  obtain ⟨_, n, hn, hnorm⟩ := heq ▸ hSevenG
  let R : Quaternion ℚ := ⟨2, 1, 1, 1⟩
  have hR : R ∈ 𝐇 := Or.inl ⟨2, 1, 1, 1, rfl, rfl, rfl, rfl⟩
  have hRn : Quaternion.normSq R = (7 : ℚ) := by
    norm_num [Quaternion.normSq_def', R]
  have hR2 : R ^ 2 ∈ 𝐇 := Or.inl ⟨1, 4, 4, 4, by
    norm_num [pow_two, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, R]⟩
  have hR2norm : Quaternion.normSq (R ^ 2) = Quaternion.normSq (7 : Quaternion ℚ) := by
    rw [map_pow, hRn, hSevenNorm]
    norm_num
  have hR2G : R ^ 2 ∈ Gq := by
    rw [heq]
    exact ⟨hR2, n, hn, hR2norm.trans hnorm⟩
  have hR0 : R ≠ 0 := by
    intro h
    have hzero : (n : ℚ) = 0 := by
      simpa [h] using (hR2norm.trans hnorm).symm
    exact (hG n hn).ne' (by exact_mod_cast hzero)
  have hOneG : (1 : Quaternion ℚ) ∈ Gq :=
    mem_of_squarefree_norm Gq hGq 1 (Or.inl ⟨1, 0, 0, 0, by simp⟩)
      1 squarefree_one (by simp)
  have hRG : R ∈ Gq :=
    mem_of_squarefree_norm Gq hGq R hR 7 (by decide : Nat.Prime 7).squarefree hRn
  exact ((hGq (R ^ 2)).1 hR2G).2.2
    ⟨1, hOneG, R, hR, hR0, by norm_num [hRn],
      by simpa using hRG, (one_mul _).symm⟩

end MetaMathlibExt
