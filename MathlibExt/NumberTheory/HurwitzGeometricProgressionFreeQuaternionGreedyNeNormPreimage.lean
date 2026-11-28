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
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Int.NatPrime
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.HurwitzQuaternionGreedy
import MathlibExt.NumberTheory.QuadraticForms.LegendreThreeSquareConverse

/-!
# The quaternion greedy set and norm preimages

The scalar quaternion `7` and the square of `2 + i + j + k` have the same norm,
but only the former belongs to any set satisfying the quaternion greedy recursion.
Hence such a set is not the norm preimage of any set of positive integers.

For each prime `p ≡ 7 (mod 8)`, the scalars `p` and `p²` also lie in the two opposite
set differences between that set and the Hurwitz norm preimage of Rankin's greedy set.
Dirichlet's theorem supplies infinitely many such primes.

## References

* Megumi Asada, Bruce Fang, Eva Fourakis, Sarah Manski, Nathan McNew, Steven J. Miller,
  Gwyneth Moreland, Ajmain Yamin, and Sindy Xin Zhang, *Avoiding 3-Term Geometric
  Progressions in Hurwitz Quaternions*, Journal of Integer Sequences 27 (2024),
  Article 24.7.7, pp. 14–16, Propositions 18 and 19, using Propositions 20 and 21.
* Fabián Arias, Jerson Borja, and Luis Rubio, *Counting Integers Representable as Images of
  Polynomials Modulo n*, Journal of Integer Sequences 22 (2019), Article 19.6.7, p. 3, Theorem 2
  (the Gauss–Legendre three-square theorem; only the obstruction is used).
* The real-part argument extends the former `seven_not_unit_mul_sq` proof in this module.
  The specialization `scalar_seven_not_unit_mul_sq` in
  `MathlibExtTest.NumberTheory.HurwitzQuaternionGreedy` uses the same
  three-square obstruction. The separation step is
  `quaternionGreedy_mem_of_not_unit_mul_sq` in `MathlibExt.NumberTheory.HurwitzQuaternionGreedy`.
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
/-- Rankin's greedy set `G₃*(ℕ₊)`: positive integers whose prime valuations have no
ternary digit `2`. -/
local notation "𝐆ʳ" => Set.ofPred fun n : ℕ =>
  0 < n ∧ ∀ p : ℕ, p.Prime → 2 ∉ Nat.digits 3 (n.factorization p)

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

private theorem prime_mod_eight_not_unit_mul_sq {p : ℕ} (hp : p.Prime)
    (hmod : p ≡ 7 [MOD 8]) :
    ¬ ∃ U ∈ 𝐇, Quaternion.normSq U = 1 ∧
      ∃ R ∈ 𝐇, Quaternion.normSq R = (p : ℚ) ∧
        (p : Quaternion ℚ) = U * R ^ 2 := by
  rintro ⟨U, hU, hUn, R, hR, hRn, heq⟩
  have hs : R ^ 2 = star U * (p : Quaternion ℚ) := by
    calc
      R ^ 2 = (star U * U) * R ^ 2 := by simp [Quaternion.star_mul_self, hUn]
      _ = star U * (U * R ^ 2) := mul_assoc _ _ _
      _ = star U * (p : Quaternion ℚ) := by rw [← heq]
  have hreal := congrArg (fun q : Quaternion ℚ => q.re) hs
  simp only [pow_two, Quaternion.re_mul, Quaternion.re_star, Quaternion.re_natCast,
    Quaternion.imI_natCast, Quaternion.imJ_natCast, Quaternion.imK_natCast,
    mul_zero, sub_zero] at hreal
  rw [Quaternion.normSq_def'] at hRn
  obtain ⟨k, hk⟩ := twice_re_int U hU
  obtain ⟨t, ht⟩ := twice_re_int R hR
  -- The real part of the square gives divisibility of `t²` by `p`.
  have hid : t ^ 2 = (p : ℤ) * (k + 2) := by
    exact_mod_cast (show (t : ℚ) ^ 2 = (p : ℚ) * ((k : ℚ) + 2) by
      rw [← ht, ← hk]
      nlinarith)
  have hpdvd : p ∣ t.natAbs := Int.Prime.dvd_natAbs_of_coe_dvd_sq hp t ⟨k + 2, hid⟩
  -- The norm bounds `t²` by `4p`, too small for a nonzero multiple of `p`.
  have ht0 : t = 0 := by
    by_contra hne
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hpdvd
    have htSq : t ^ 2 ≤ 4 * (p : ℤ) := by
      exact_mod_cast (show (t : ℚ) ^ 2 ≤ 4 * (p : ℚ) by
        rw [← ht]
        nlinarith [sq_nonneg R.imI, sq_nonneg R.imJ, sq_nonneg R.imK])
    have hb : t.natAbs ^ 2 ≤ 4 * p := by
      exact_mod_cast (show (t.natAbs : ℤ) ^ 2 ≤ 4 * (p : ℤ) by
        simpa only [Int.natCast_natAbs, sq_abs] using htSq)
    have hp4 : 4 < p := by
      have hrem : p % 8 = 7 := hmod
      omega
    have hpSq : 4 * p < p ^ 2 := by
      simpa only [pow_two] using Nat.mul_lt_mul_of_pos_right hp4 hp.pos
    exact (not_lt_of_ge ((Nat.pow_le_pow_left hle 2).trans hb)) hpSq
  have hr0 : R.re = 0 := by
    rw [ht0, Int.cast_zero] at ht
    linarith
  rcases hR with ⟨_, b, c, d, _, hb, hc, hd⟩ | ⟨a, _, _, _, ha, _⟩
  · have hsum : b ^ 2 + c ^ 2 + d ^ 2 = (p : ℤ) := by
      exact_mod_cast (show (b : ℚ) ^ 2 + (c : ℚ) ^ 2 + (d : ℚ) ^ 2 = (p : ℚ) by
        simpa [hr0, hb, hc, hd] using hRn)
    have hnat : b.natAbs ^ 2 + c.natAbs ^ 2 + d.natAbs ^ 2 = p := by
      exact_mod_cast (show
        (b.natAbs : ℤ) ^ 2 + (c.natAbs : ℤ) ^ 2 + (d.natAbs : ℤ) ^ 2 = (p : ℤ) by
        simpa only [Int.natCast_natAbs, sq_abs] using hsum)
    apply Nat.not_exists_four_pow_mul_eight_mul_add_seven_of_exists_three_squares p
      ⟨b.natAbs, c.natAbs, d.natAbs, hnat⟩
    refine ⟨0, p / 8, ?_⟩
    have hrem : p % 8 = 7 := hmod
    simp only [pow_zero, one_mul]
    omega
  · have h : (2 * a + 1 : ℤ) = 0 := by
      exact_mod_cast (show 2 * (a : ℚ) + 1 = 0 by rw [ha] at hr0; linarith)
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
    7 hSeven hSevenNorm (prime_mod_eight_not_unit_mul_sq Nat.prime_seven (by decide))).1.1
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

/-- **The quaternion greedy set and the norm preimage of Rankin's set differ infinitely.** A
Hurwitz quaternion is a quaternion whose four rational coordinates are either all integers or all
halves of odd integers; the norm $\mathrm{Nm}(q)$ of a quaternion $q$ is the sum of the squares of
its coordinates. Let $\mathcal{G}$ be a set of quaternions such that a quaternion $q$ lies in
$\mathcal{G}$ if and only if $q$ is a nonzero Hurwitz quaternion and there are no
$a \in \mathcal{G}$ and Hurwitz quaternion $r \ne 0$ with norm $\mathrm{Nm}(r) \ne 1$,
$ar \in \mathcal{G}$ and $q = ar^2$ (this recursion on the norm characterizes the quaternion
greedy set). Let $G^*_3$ be Rankin's greedy set, the set of positive integers $n$ such that for
every prime $p$ the base-$3$ digits of the exponent of $p$ in $n$ include no digit $2$, and let
$S(G^*_3)$ be the set of Hurwitz quaternions whose norm lies in $G^*_3$. Then both
$\mathcal{G} \setminus S(G^*_3)$ and $S(G^*_3) \setminus \mathcal{G}$ are infinite.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Proposition 19. -/
public theorem quaternionGreedy_diff_rankin_infinite
    (Gq : Set (Quaternion ℚ)) (hGq : IsQuaternionGreedy Gq) :
    (Gq \ 𝐒ᴳ 𝐆ʳ).Infinite ∧ (𝐒ᴳ 𝐆ʳ \ Gq).Infinite := by
  let P : Set ℕ := {p | p.Prime ∧ p ≡ 7 [MOD 8]}
  have hP : P.Infinite := Nat.infinite_setOfPred_prime_and_modEq (by decide) (by decide)
  let f : ℕ → Quaternion ℚ := fun p => (p : Quaternion ℚ)
  have hf : Function.Injective f := Quaternion.coe_injective.comp Nat.cast_injective
  have hfSq : Function.Injective (fun p => f p ^ 2) := by
    simpa only [Function.comp_def, f, Nat.cast_pow] using
      hf.comp (Nat.pow_left_injective (n := 2) (by decide))
  have hmem (p : ℕ) (hp : p ∈ P) : f p ∈ Gq \ 𝐒ᴳ 𝐆ʳ ∧ f p ^ 2 ∈ 𝐒ᴳ 𝐆ʳ \ Gq := by
    apply quaternionGreedy_mem_of_not_unit_mul_sq Gq hGq p hp.1
    · exact Or.inl ⟨p, 0, 0, 0, rfl, rfl, rfl, rfl⟩
    · change Quaternion.normSq (p : Quaternion ℚ) = ((p ^ 2 : ℕ) : ℚ)
      rw [Nat.cast_pow, Quaternion.normSq_natCast]
    · exact prime_mod_eight_not_unit_mul_sq hp.1 hp.2
  exact ⟨Set.infinite_of_injOn_mapsTo hf.injOn (fun p hp => (hmem p hp).1) hP,
    Set.infinite_of_injOn_mapsTo hfSq.injOn (fun p hp => (hmem p hp).2) hP⟩

end MetaMathlibExt
