/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.Ring

/-!
# The quaternion greedy set and Rankin's greedy set

A Hurwitz quaternion of prime-square norm that has no expression as a Hurwitz
unit times a square of the appropriate norm separates the quaternion greedy
set from the norm preimage of Rankin's greedy set. Its square separates the
sets in the other direction.
-/

namespace MetaMathlibExt

set_option quotPrecheck false in
/-- The Hurwitz order: quaternions with all coordinates in `ℤ` or all in `ℤ + 1/2`. -/
local notation "𝐇" => Set.ofPred fun q : Quaternion ℚ =>
  (∃ a b c d : ℤ,
    q.re = (a : ℚ) ∧ q.imI = (b : ℚ) ∧ q.imJ = (c : ℚ) ∧ q.imK = (d : ℚ)) ∨
  (∃ a b c d : ℤ,
    q.re = (a : ℚ) + 1 / 2 ∧ q.imI = (b : ℚ) + 1 / 2 ∧
      q.imJ = (c : ℚ) + 1 / 2 ∧ q.imK = (d : ℚ) + 1 / 2)

set_option quotPrecheck false in
/-- `S(G)`: Hurwitz quaternions whose norm lies in `G ⊆ ℕ`. -/
local notation "𝐒ᴳ" G:max => Set.ofPred fun q : Quaternion ℚ =>
  q ∈ 𝐇 ∧ ∃ n ∈ G, Quaternion.normSq q = ((n : ℕ) : ℚ)

set_option quotPrecheck false in
/-- Rankin's greedy set `G₃*(ℕ₊)`: positive integers whose prime valuations have no
ternary digit `2`. -/
local notation "𝐆ʳ" => Set.ofPred fun n : ℕ =>
  0 < n ∧ ∀ p : ℕ, p.Prime → 2 ∉ Nat.digits 3 (n.factorization p)

set_option quotPrecheck false in
/-- `Gq` is the quaternion greedy set `G₃*(Q_Hur ∖ {0})`, pinned by its defining recursion. -/
local notation "IsQuaternionGreedy" Gq:max => ∀ q : Quaternion ℚ, q ∈ Gq ↔
  (q ∈ 𝐇 ∧ q ≠ 0 ∧ ¬ ∃ a ∈ Gq, ∃ r ∈ 𝐇, r ≠ 0 ∧ Quaternion.normSq r ≠ 1 ∧
    a * r ∈ Gq ∧ q = a * r ^ 2)

set_option quotPrecheck false in
/-- `Q = U R²` for a unit `U ∈ Q_Hur` and some `R ∈ Q_Hur` of norm `r`. -/
local notation "IsUnitMulSq" Q:max r:max => ∃ U ∈ 𝐇, Quaternion.normSq U = 1 ∧
  ∃ R ∈ 𝐇, Quaternion.normSq R = ((r : ℕ) : ℚ) ∧ Q = U * R ^ 2

/-- **The norm of a Hurwitz quaternion is a natural number.** If the four rational coordinates of a
quaternion $q$ are either all integers or all halves of odd integers, then its norm
$\mathrm{Nm}(q)$, the sum of the squares of its coordinates, equals some natural number $n$. -/
public theorem hurwitz_normSq_nat {q : Quaternion ℚ} (hq : q ∈ 𝐇) :
    ∃ n : ℕ, Quaternion.normSq q = (n : ℚ) := by
  have hInt : ∃ z : ℤ, Quaternion.normSq q = (z : ℚ) := by
    rcases hq with ⟨a, b, c, d, ha, hb, hc, hd⟩ | ⟨a, b, c, d, ha, hb, hc, hd⟩
    · exact ⟨a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2, by
        simp [Quaternion.normSq_def', ha, hb, hc, hd]⟩
    · refine ⟨a ^ 2 + a + (b ^ 2 + b) + (c ^ 2 + c) + (d ^ 2 + d) + 1, ?_⟩
      push_cast
      rw [Quaternion.normSq_def', ha, hb, hc, hd]
      ring
  obtain ⟨z, hz⟩ := hInt
  have hz0 : 0 ≤ z := by exact_mod_cast hz ▸ Quaternion.normSq_nonneg (a := q)
  exact ⟨z.toNat, by rw [hz, ← Int.cast_natCast, Int.toNat_of_nonneg hz0]⟩

private theorem sq_mem {q : Quaternion ℚ} (hq : q ∈ 𝐇) : q ^ 2 ∈ 𝐇 := by
  rcases hq with ⟨a, b, c, d, ha, hb, hc, hd⟩ | ⟨a, b, c, d, ha, hb, hc, hd⟩
  · refine Or.inl ⟨a * a - b * b - c * c - d * d, 2 * a * b, 2 * a * c, 2 * a * d,
      ?_, ?_, ?_, ?_⟩ <;>
      simp only [pow_two, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul, ha, hb, hc, hd, Int.cast_sub, Int.cast_mul, Int.cast_ofNat] <;>
      ring
  · refine Or.inr ⟨a * a + a - (b * b + b) - (c * c + c) - (d * d + d) - 1,
      2 * a * b + a + b, 2 * a * c + a + c, 2 * a * d + a + d, ?_, ?_, ?_, ?_⟩ <;>
      simp only [pow_two, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul, ha, hb, hc, hd, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_one,
        Int.cast_ofNat] <;>
      ring

/-- **The norm of $ar^2$ factors as $\mathrm{Nm}(a)\,\mathrm{Nm}(r)^2$ in the natural numbers.** Let
$a$ and $r$ be Hurwitz quaternions (quaternions whose four rational coordinates are either all
integers or all halves of odd integers), and let $q = ar^2$ have norm $\mathrm{Nm}(q) = k$ for a
natural number $k$. Then there are natural numbers $m$ and $n$ with $\mathrm{Nm}(a) = m$,
$\mathrm{Nm}(r) = n$ and $k = mn^2$. -/
public theorem hurwitz_normSq_eq_mul_sq {q a r : Quaternion ℚ} {k : ℕ}
    (hq : q = a * r ^ 2) (hqk : Quaternion.normSq q = (k : ℚ)) (ha : a ∈ 𝐇) (hr : r ∈ 𝐇) :
    ∃ m n : ℕ, Quaternion.normSq a = (m : ℚ) ∧ Quaternion.normSq r = (n : ℚ) ∧
      k = m * n ^ 2 := by
  obtain ⟨m, hm⟩ := hurwitz_normSq_nat ha
  obtain ⟨n, hn⟩ := hurwitz_normSq_nat hr
  refine ⟨m, n, hm, hn, ?_⟩
  rw [hq, map_mul, map_pow, hm, hn] at hqk
  exact_mod_cast hqk.symm

/-- **Quaternions of prime-square norm separating the greedy set from Rankin's set.** A Hurwitz
quaternion is a quaternion whose four rational coordinates are either all integers or all halves
of odd integers; its norm $\mathrm{Nm}(q)$ is the sum of the squares of its coordinates, and a
Hurwitz unit is a Hurwitz quaternion of norm $1$. Let $\mathcal{G}$ be a set of quaternions such
that a quaternion $q$ lies in $\mathcal{G}$ if and only if $q$ is a nonzero Hurwitz quaternion
and there are no $a \in \mathcal{G}$ and Hurwitz quaternion $r \ne 0$ with $\mathrm{Nm}(r) \ne 1$,
$ar \in \mathcal{G}$ and $q = ar^2$ (this recursion on the norm characterizes the quaternion
greedy set). Let $G^*_3$ be Rankin's greedy set, the set of positive integers $n$ such that for
every prime $\ell$ the base-$3$ digits of the exponent of $\ell$ in $n$ include no digit $2$, and
let $S(G^*_3)$ be the set of Hurwitz quaternions whose norm lies in $G^*_3$. Let $p$ be a prime
and $Q$ a Hurwitz quaternion of norm $p^2$ that cannot be written as $Q = UR^2$ with $U$ a
Hurwitz unit and $R$ a Hurwitz quaternion of norm $p$. Then
$Q \in \mathcal{G} \setminus S(G^*_3)$ and $Q^2 \in S(G^*_3) \setminus \mathcal{G}$.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Proposition 21. -/
public theorem quaternionGreedy_mem_of_not_unit_mul_sq
    (Gq : Set (Quaternion ℚ)) (hGq : IsQuaternionGreedy Gq) (p : ℕ) (hp : p.Prime)
    (Q : Quaternion ℚ) (hQ : Q ∈ 𝐇) (hQn : Quaternion.normSq Q = ((p ^ 2 : ℕ) : ℚ))
    (hQU : ¬ IsUnitMulSq Q p) :
    Q ∈ Gq \ 𝐒ᴳ 𝐆ʳ ∧ Q ^ 2 ∈ 𝐒ᴳ 𝐆ʳ \ Gq := by
  have hpSq : ((p ^ 2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hp.ne_zero
  have hQ0 : Q ≠ 0 := by
    apply Quaternion.normSq_ne_zero.mp
    rwa [hQn]
  have hQ1 : Quaternion.normSq Q ≠ 1 := by
    rw [hQn]
    exact_mod_cast (show p ^ 2 ≠ 1 by
      simpa only [one_pow] using (Nat.pow_lt_pow_left hp.one_lt (by decide : 2 ≠ 0)).ne')
  have hQg : Q ∈ Gq := by
    refine (hGq Q).2 ⟨hQ, hQ0, ?_⟩
    rintro ⟨a, ha, r, hr, _, hr1, _, heq⟩
    have haH := ((hGq a).1 ha).1
    obtain ⟨m, n, hm, hn, hmn⟩ := hurwitz_normSq_eq_mul_sq heq hQn haH hr
    have hndvd : n ^ 2 ∣ p ^ 2 := ⟨m, hmn.trans (mul_comm _ _)⟩
    have hnp : n ∣ p := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp hndvd
    rcases (Nat.dvd_prime hp).mp hnp with h | h
    · exact hr1 (by simpa [h] using hn)
    · subst n
      have hm1 : m = 1 := Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2)
        (by simpa only [one_mul] using hmn.symm)
      exact hQU ⟨a, haH, by simpa [hm1] using hm, r, hr, hn, heq⟩
  have hOne : (1 : Quaternion ℚ) ∈ Gq := by
    have hOneH : (1 : Quaternion ℚ) ∈ 𝐇 := Or.inl ⟨1, 0, 0, 0, by simp⟩
    refine (hGq 1).2 ⟨hOneH, one_ne_zero, ?_⟩
    rintro ⟨a, ha, r, hr, _, hr1, _, heq⟩
    have hOneNorm : Quaternion.normSq (1 : Quaternion ℚ) = ((1 : ℕ) : ℚ) := by simp
    obtain ⟨m, n, _, hn, hmn⟩ := hurwitz_normSq_eq_mul_sq heq hOneNorm ((hGq a).1 ha).1 hr
    have hdvd : n ^ 2 ∣ 1 := ⟨m, hmn.trans (mul_comm _ _)⟩
    have hn1 : n ∣ 1 := (dvd_pow_self _ (by decide : 2 ≠ 0)).trans hdvd
    exact hr1 (by simpa [Nat.dvd_one.mp hn1] using hn)
  refine ⟨⟨hQg, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨_, n, hn, hnorm⟩
    have hnp : n = p ^ 2 := by exact_mod_cast hnorm.symm.trans hQn
    have hdigits := hn.2 p hp
    rw [hnp, hp.factorization_pow, Finsupp.single_eq_same] at hdigits
    exact hdigits (by decide)
  · refine ⟨sq_mem hQ, p ^ 4, ⟨pow_pos hp.pos 4, ?_⟩, ?_⟩
    · intro ℓ _
      rw [hp.factorization_pow, Finsupp.single_apply]
      split <;> decide
    · rw [map_pow, hQn, Nat.cast_pow, ← pow_mul]
      norm_cast
  · intro h
    exact ((hGq (Q ^ 2)).1 h).2.2
      ⟨1, hOne, Q, hQ, hQ0, hQ1, by simpa using hQg, (one_mul _).symm⟩

end MetaMathlibExt
