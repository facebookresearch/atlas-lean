/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Legendre's theorem on the equation $a x^2 + b y^2 + c z^2 = 0$

Let $a, b, c$ be nonzero, square free, pairwise relatively prime integers that are neither all
positive nor all negative. Then $a x^2 + b y^2 + c z^2 = 0$ has a solution in integers other than
$(0, 0, 0)$ if and only if $-ab$ is a square modulo $c$, $-ac$ is a square modulo $b$ and $-bc$ is
a square modulo $a$ (K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*,
2nd ed., Chapter 17, §3, Proposition 17.3.1, p. 273).

The conditions are necessary. If a prime $p$ divides both $y$ and $c$ in a solution, then $p$
divides $a x^2$, hence $x$, as $c$ is prime to $a$; then $p^2$ divides $c z^2$, hence $p$ divides
$z$, as $c$ is square free. Dividing $x, y, z$ by $p$ gives a smaller solution, so by descent on
$|x| + |y| + |z|$ some solution has $y$ prime to $c$, and there
$(a x y')^2 \equiv -ab \pmod{c}$ for an inverse $y'$ of $y$ modulo $c$.

Sufficiency is proved by the pigeonhole principle instead of the source's descent. Take $r, s, t$
with $r^2 \equiv -bc \pmod{a}$, $s^2 \equiv -ac \pmod{b}$ and $t^2 \equiv -ab \pmod{c}$. The linear
congruences $b y \equiv r z \pmod{a}$, $c z \equiv s x \pmod{b}$ and $a x \equiv t y \pmod{c}$
make $a x^2 + b y^2 + c z^2$ divisible by $abc$. The points $(x, y, z)$ with
$0 \le x \le \sqrt{|bc|}$, $0 \le y \le \sqrt{|ac|}$ and $0 \le z \le \sqrt{|ab|}$ outnumber the
$|abc|$ triples of residues modulo $a$, $b$ and $c$, so two of them give $b y - r z$, $c z - s x$
and $a x - t y$ the same residues. Their difference is a solution $(x, y, z) \neq (0, 0, 0)$ of the
congruences with $x^2 \le |bc|$, $y^2 \le |ac|$ and $z^2 \le |ab|$.

Let $a, b > 0 > c$. Then $abc \le a x^2 + b y^2 + c z^2 \le -2abc$. Equality on the left forces
$z^2 = ab$, and on the right $x^2 = b |c|$ and $y^2 = a |c|$; these products are square free, so
they are squares only when they are $1$, and either equality forces $a = b = 1$. Unless
$a = b = 1$, the value of the form is therefore $0$ or $-abc$. In the second case
$(xz + by, yz - ax, z^2 + ab)$ is a solution, by the identity

$$a (xz + by)^2 + b (yz - ax)^2 + c (z^2 + ab)^2 = (z^2 + ab) (a x^2 + b y^2 + c z^2 + abc).$$

If $a = b = 1$, then $-1$ is a square modulo $|c|$, so $|c| = u^2 + v^2$ for some integers $u, v$
(`Nat.eq_sq_add_sq_of_isSquare_mod_neg_one`) and $(u, v, 1)$ is a solution. The other signs
reduce to $a, b > 0 > c$ by permuting $a, b, c$ and changing all their signs.
-/

@[expose] public section

namespace Int

/-- A squarefree integer that is a perfect square is `1`. -/
private theorem eq_one_of_squarefree_of_eq_sq {n k : ℤ} (hn : Squarefree n) (h : n = k ^ 2) :
    n = 1 := by
  have hk : IsUnit k := hn k ⟨1, by rw [h]; ring⟩
  rw [h, Int.isUnit_sq hk]

private theorem squarefree_neg_of_squarefree {n : ℤ} (hn : Squarefree n) : Squarefree (-n) := by
  rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.squarefree_natAbs]
  exact hn

private theorem squarefree_mul_of_isCoprime {m n : ℤ} (hmn : IsCoprime m n) (hm : Squarefree m)
    (hn : Squarefree n) : Squarefree (m * n) :=
  squarefree_mul_iff.mpr ⟨hmn.isRelPrime, hm, hn⟩

/-- Necessity of the condition modulo `c`, by descent on `|x| + |y| + |z|`: a common prime
factor of `y` and `c` divides `x` and `z`. -/
private theorem exists_sq_modEq_of_ternary {a b c : ℤ} (hc0 : c ≠ 0) (hc : Squarefree c)
    (hac : IsCoprime a c) :
    ∀ n : ℕ, ∀ x y z : ℤ, x.natAbs + y.natAbs + z.natAbs = n → ¬(x = 0 ∧ y = 0 ∧ z = 0) →
      a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 → ∃ t : ℤ, t ^ 2 ≡ -(a * b) [ZMOD c] := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x y z hn hne hQ
  by_cases hyc : IsCoprime y c
  · obtain ⟨u, v, huv⟩ := hyc
    refine ⟨a * x * u, Int.modEq_iff_dvd.mpr ⟨a * u ^ 2 * z ^ 2 - a * b * v * (2 - v * c), ?_⟩⟩
    linear_combination (-a * u ^ 2) * hQ + (a * b * (u * y + 1 - v * c)) * huv
  · obtain ⟨p, hp, hpy, hpc⟩ : ∃ p : ℤ, Prime p ∧ p ∣ y ∧ p ∣ c := by
      by_contra h
      push Not at h
      exact hyc (isCoprime_of_prime_dvd (fun h' => hc0 h'.2) fun p hp hpy hpc => h p hp hpy hpc)
    have hpa : ¬p ∣ a := fun hpa => hp.not_isUnit (hac.isUnit_of_dvd' hpa hpc)
    have hpx : p ∣ x := by
      have hax : p ∣ a * x ^ 2 := by
        have e : a * x ^ 2 = -(b * y ^ 2 + c * z ^ 2) := by linear_combination hQ
        rw [e]
        exact (dvd_add ((hpy.trans (dvd_pow_self y two_ne_zero)).mul_left b)
          (hpc.mul_right _)).neg_right
      exact hp.dvd_of_dvd_pow ((hp.dvd_or_dvd hax).resolve_left hpa)
    obtain ⟨x₁, rfl⟩ := hpx
    obtain ⟨y₁, rfl⟩ := hpy
    obtain ⟨c₁, rfl⟩ := hpc
    have hpc₁ : ¬p ∣ c₁ := by
      rintro ⟨c₂, rfl⟩
      exact hp.not_isUnit (hc p ⟨c₂, by ring⟩)
    have hp0 : p ≠ 0 := hp.ne_zero
    have hpz : p ∣ z := by
      have h1 : p * (a * p * x₁ ^ 2 + b * p * y₁ ^ 2 + c₁ * z ^ 2) = 0 := by
        linear_combination hQ
      have h2 := (mul_eq_zero.mp h1).resolve_left hp0
      have h3 : p ∣ c₁ * z ^ 2 := ⟨-(a * x₁ ^ 2 + b * y₁ ^ 2), by linear_combination h2⟩
      exact hp.dvd_of_dvd_pow ((hp.dvd_or_dvd h3).resolve_left hpc₁)
    obtain ⟨z₁, rfl⟩ := hpz
    have hQ₁ : a * x₁ ^ 2 + b * y₁ ^ 2 + p * c₁ * z₁ ^ 2 = 0 := by
      have h1 : p ^ 2 * (a * x₁ ^ 2 + b * y₁ ^ 2 + p * c₁ * z₁ ^ 2) = 0 := by
        linear_combination hQ
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 hp0)
    have hne₁ : ¬(x₁ = 0 ∧ y₁ = 0 ∧ z₁ = 0) := by
      rintro ⟨rfl, rfl, rfl⟩
      exact hne ⟨by simp, by simp, by simp⟩
    have hp2 : 2 ≤ p.natAbs := (Int.prime_iff_natAbs_prime.mp hp).two_le
    have hpos : 0 < x₁.natAbs + y₁.natAbs + z₁.natAbs := by
      by_contra h0
      apply hne₁
      omega
    have hlt : x₁.natAbs + y₁.natAbs + z₁.natAbs < n := by
      rw [← hn, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]
      nlinarith
    exact ih _ hlt x₁ y₁ z₁ rfl hne₁ hQ₁

/-- Pigeonhole step: a nonzero small `(x, y, z)` satisfying three linear congruences. -/
private theorem exists_small_of_dvd {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (r s t : ℤ) :
    ∃ x y z : ℤ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ a ∣ b * y - r * z ∧ b ∣ c * z - s * x ∧
      c ∣ a * x - t * y ∧ x ^ 2 ≤ |b| * |c| ∧ y ^ 2 ≤ |a| * |c| ∧ z ^ 2 ≤ |a| * |b| := by
  set A := a.natAbs with hA
  set B := b.natAbs with hB
  set C := c.natAbs with hC
  have : NeZero A := ⟨Int.natAbs_ne_zero.mpr ha⟩
  have : NeZero B := ⟨Int.natAbs_ne_zero.mpr hb⟩
  have : NeZero C := ⟨Int.natAbs_ne_zero.mpr hc⟩
  set X := Nat.sqrt (B * C) with hX
  set Y := Nat.sqrt (A * C) with hY
  set Z := Nat.sqrt (A * B) with hZ
  let f : Fin (X + 1) × Fin (Y + 1) × Fin (Z + 1) → ZMod A × ZMod B × ZMod C := fun q =>
    (((b * (q.2.1 : ℕ) - r * (q.2.2 : ℕ) : ℤ) : ZMod A),
      ((c * (q.2.2 : ℕ) - s * (q.1 : ℕ) : ℤ) : ZMod B),
      ((a * (q.1 : ℕ) - t * (q.2.1 : ℕ) : ℤ) : ZMod C))
  have hcard : Fintype.card (ZMod A × ZMod B × ZMod C) <
      Fintype.card (Fin (X + 1) × Fin (Y + 1) × Fin (Z + 1)) := by
    simp only [Fintype.card_prod, ZMod.card, Fintype.card_fin]
    have h1 := Nat.lt_succ_sqrt' (B * C)
    have h2 := Nat.lt_succ_sqrt' (A * C)
    have h3 := Nat.lt_succ_sqrt' (A * B)
    rw [← hX] at h1
    rw [← hY] at h2
    rw [← hZ] at h3
    by_contra hle
    push Not at hle
    have hsq : ((X + 1) * ((Y + 1) * (Z + 1))) ^ 2 ≤ (A * (B * C)) ^ 2 :=
      Nat.pow_le_pow_left hle 2
    have hlt : (A * (B * C)) ^ 2 < ((X + 1) * ((Y + 1) * (Z + 1))) ^ 2 := by
      calc (A * (B * C)) ^ 2 = B * C * (A * C) * (A * B) := by ring
        _ < X.succ ^ 2 * Y.succ ^ 2 * Z.succ ^ 2 :=
          Nat.mul_lt_mul'' (Nat.mul_lt_mul'' h1 h2) h3
        _ = ((X + 1) * ((Y + 1) * (Z + 1))) ^ 2 := by simp only [Nat.succ_eq_add_one]; ring
    exact absurd hsq (not_le.mpr hlt)
  obtain ⟨p, q, hpq, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  simp only [f, Prod.mk.injEq] at hf
  obtain ⟨hf1, hf2, hf3⟩ := hf
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, Int.natAbs_dvd] at hf1 hf2 hf3
  have hpX := p.1.isLt
  have hqX := q.1.isLt
  have hpY := p.2.1.isLt
  have hqY := q.2.1.isLt
  have hpZ := p.2.2.isLt
  have hqZ := q.2.2.isLt
  refine ⟨((p.1 : ℕ) : ℤ) - (q.1 : ℕ), ((p.2.1 : ℕ) : ℤ) - (q.2.1 : ℕ),
    ((p.2.2 : ℕ) : ℤ) - (q.2.2 : ℕ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h1, h2, h3⟩
    apply hpq
    refine Prod.ext (Fin.ext (by omega)) (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
  · have := hf1.neg_right
    convert this using 1
    ring
  · have := hf2.neg_right
    convert this using 1
    ring
  · have := hf3.neg_right
    convert this using 1
    ring
  · have hb' : |b| = (B : ℤ) := Int.abs_eq_natAbs b
    have hc' : |c| = (C : ℤ) := Int.abs_eq_natAbs c
    have hX2 : (X : ℤ) ^ 2 ≤ (B : ℤ) * C := by exact_mod_cast Nat.sqrt_le' (B * C)
    rw [hb', hc']
    have h1 : ((p.1 : ℕ) : ℤ) - (q.1 : ℕ) ≤ X := by omega
    have h2 : -(X : ℤ) ≤ ((p.1 : ℕ) : ℤ) - (q.1 : ℕ) := by omega
    nlinarith
  · have ha' : |a| = (A : ℤ) := Int.abs_eq_natAbs a
    have hc' : |c| = (C : ℤ) := Int.abs_eq_natAbs c
    have hY2 : (Y : ℤ) ^ 2 ≤ (A : ℤ) * C := by exact_mod_cast Nat.sqrt_le' (A * C)
    rw [ha', hc']
    have h1 : ((p.2.1 : ℕ) : ℤ) - (q.2.1 : ℕ) ≤ Y := by omega
    have h2 : -(Y : ℤ) ≤ ((p.2.1 : ℕ) : ℤ) - (q.2.1 : ℕ) := by omega
    nlinarith
  · have ha' : |a| = (A : ℤ) := Int.abs_eq_natAbs a
    have hb' : |b| = (B : ℤ) := Int.abs_eq_natAbs b
    have hZ2 : (Z : ℤ) ^ 2 ≤ (A : ℤ) * B := by exact_mod_cast Nat.sqrt_le' (A * B)
    rw [ha', hb']
    have h1 : ((p.2.2 : ℕ) : ℤ) - (q.2.2 : ℕ) ≤ Z := by omega
    have h2 : -(Z : ℤ) ≤ ((p.2.2 : ℕ) : ℤ) - (q.2.2 : ℕ) := by omega
    nlinarith

/-- The three linear congruences make `a x ^ 2 + b y ^ 2 + c z ^ 2` divisible by `a b c`. -/
private theorem mul_dvd_of_dvd {a b c r s t x y z : ℤ} (hab : IsCoprime a b)
    (hbc : IsCoprime b c) (hac : IsCoprime a c) (hr : a ∣ -(b * c) - r ^ 2)
    (hs : b ∣ -(a * c) - s ^ 2) (ht : c ∣ -(a * b) - t ^ 2) (hx : a ∣ b * y - r * z)
    (hy : b ∣ c * z - s * x) (hz : c ∣ a * x - t * y) :
    a * b * c ∣ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 := by
  obtain ⟨k₁, hk₁⟩ := hx
  obtain ⟨k₂, hk₂⟩ := hr
  obtain ⟨k₃, hk₃⟩ := hy
  obtain ⟨k₄, hk₄⟩ := hs
  obtain ⟨k₅, hk₅⟩ := hz
  obtain ⟨k₆, hk₆⟩ := ht
  have hA : a ∣ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 := by
    have h : a ∣ b * (b * y ^ 2 + c * z ^ 2) :=
      ⟨2 * k₁ * r * z + a * k₁ ^ 2 - k₂ * z ^ 2, by
        linear_combination (b * y + r * z + a * k₁) * hk₁ - z ^ 2 * hk₂⟩
    have h' := hab.dvd_of_dvd_mul_left h
    have e : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = a * x ^ 2 + (b * y ^ 2 + c * z ^ 2) := by ring
    rw [e]
    exact dvd_add (dvd_mul_right a _) h'
  have hB : b ∣ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 := by
    have h : b ∣ c * (c * z ^ 2 + a * x ^ 2) :=
      ⟨2 * k₃ * s * x + b * k₃ ^ 2 - k₄ * x ^ 2, by
        linear_combination (c * z + s * x + b * k₃) * hk₃ - x ^ 2 * hk₄⟩
    have h' := hbc.dvd_of_dvd_mul_left h
    have e : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = b * y ^ 2 + (c * z ^ 2 + a * x ^ 2) := by ring
    rw [e]
    exact dvd_add (dvd_mul_right b _) h'
  have hC : c ∣ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 := by
    have h : c ∣ a * (a * x ^ 2 + b * y ^ 2) :=
      ⟨2 * k₅ * t * y + c * k₅ ^ 2 - k₆ * y ^ 2, by
        linear_combination (a * x + t * y + c * k₅) * hk₅ - y ^ 2 * hk₆⟩
    have h' := hac.symm.dvd_of_dvd_mul_left h
    exact dvd_add h' (dvd_mul_right c _)
  exact (hac.mul_left hbc).mul_dvd (hab.mul_dvd hA hB) hC

/-- Sufficiency when `a` and `b` are positive and `c` is negative. -/
private theorem exists_ternary_of_pos_pos_neg {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : c < 0)
    (ha' : Squarefree a) (hb' : Squarefree b) (hc' : Squarefree c) (hab : IsCoprime a b)
    (hbc : IsCoprime b c) (hac : IsCoprime a c) (h1 : ∃ t : ℤ, t ^ 2 ≡ -(a * b) [ZMOD c])
    (h2 : ∃ s : ℤ, s ^ 2 ≡ -(a * c) [ZMOD b]) (h3 : ∃ r : ℤ, r ^ 2 ≡ -(b * c) [ZMOD a]) :
    ∃ x y z : ℤ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 := by
  obtain ⟨t, ht⟩ := h1
  obtain ⟨s, hs⟩ := h2
  obtain ⟨r, hr⟩ := h3
  by_cases h11 : a = 1 ∧ b = 1
  · obtain ⟨rfl, rfl⟩ := h11
    have hsq : IsSquare (-1 : ZMod c.natAbs) := by
      refine ⟨(t : ZMod c.natAbs), ?_⟩
      have h := ht.dvd
      have h' : (c.natAbs : ℤ) ∣ t * t - (-1) := by
        rw [Int.natAbs_dvd]
        have e : t * t - (-1) = -(-(1 * 1) - t ^ 2) := by ring
        rw [e]
        exact h.neg_right
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub (-1) (t * t) c.natAbs).mpr h'
      push_cast at this
      exact this
    obtain ⟨u, v, huv⟩ := Nat.eq_sq_add_sq_of_isSquare_mod_neg_one hsq
    refine ⟨u, v, 1, fun h => one_ne_zero h.2.2, ?_⟩
    have hcabs : (c.natAbs : ℤ) = -c := by
      rw [Int.natCast_natAbs, abs_of_neg hc]
    have : ((c.natAbs : ℕ) : ℤ) = (u : ℤ) ^ 2 + (v : ℤ) ^ 2 := by exact_mod_cast huv
    linear_combination hcabs - this
  · obtain ⟨x, y, z, hne, hx, hy, hz, hbx, hby, hbz⟩ :=
      exists_small_of_dvd ha.ne' hb.ne' hc.ne r s t
    obtain ⟨k, hk⟩ := mul_dvd_of_dvd hab hbc hac hr.dvd hs.dvd ht.dvd hx hy hz
    rw [abs_of_pos hb, abs_of_neg hc] at hbx
    rw [abs_of_pos ha, abs_of_neg hc] at hby
    rw [abs_of_pos ha, abs_of_pos hb] at hbz
    have hab0 : 0 < a * b := mul_pos ha hb
    have hlow : a * b * c < a * x ^ 2 + b * y ^ 2 + c * z ^ 2 := by
      by_contra hle
      push Not at hle
      have e1 : a * b * c ≤ c * z ^ 2 := by nlinarith
      have e2 : 0 ≤ a * x ^ 2 := by positivity
      have e3 : 0 ≤ b * y ^ 2 := by positivity
      have e4 : c * z ^ 2 = c * (a * b) := by linarith
      have hz2 : a * b = z ^ 2 := (mul_left_cancel₀ hc.ne e4).symm
      have h1 := eq_one_of_squarefree_of_eq_sq (squarefree_mul_of_isCoprime hab ha' hb') hz2
      exact h11 ⟨Int.eq_one_of_mul_eq_one_right ha.le h1, Int.eq_one_of_mul_eq_one_left hb.le h1⟩
    have hupp : a * x ^ 2 + b * y ^ 2 + c * z ^ 2 < -(2 * (a * b * c)) := by
      by_contra hle
      push Not at hle
      have e1 : a * x ^ 2 ≤ a * (b * -c) := by nlinarith
      have e2 : b * y ^ 2 ≤ b * (a * -c) := by nlinarith
      have e3 : c * z ^ 2 ≤ 0 := by nlinarith [sq_nonneg z]
      have e4 : a * x ^ 2 = a * (b * -c) := by linarith
      have e5 : b * y ^ 2 = b * (a * -c) := by linarith
      have hx2 : b * -c = x ^ 2 := (mul_left_cancel₀ ha.ne' e4).symm
      have hy2 : a * -c = y ^ 2 := (mul_left_cancel₀ hb.ne' e5).symm
      have k1 := eq_one_of_squarefree_of_eq_sq
        (squarefree_mul_of_isCoprime hbc.neg_right hb' (squarefree_neg_of_squarefree hc')) hx2
      have k2 := eq_one_of_squarefree_of_eq_sq
        (squarefree_mul_of_isCoprime hac.neg_right ha' (squarefree_neg_of_squarefree hc')) hy2
      exact h11 ⟨Int.eq_one_of_mul_eq_one_right ha.le k2, Int.eq_one_of_mul_eq_one_right hb.le k1⟩
    have hm : a * b * c < 0 := mul_neg_of_pos_of_neg hab0 hc
    have hk1 : k < 1 := by
      by_contra hk1
      push Not at hk1
      nlinarith
    have hk2 : -2 < k := by
      by_contra hk2
      push Not at hk2
      nlinarith
    interval_cases k
    · refine ⟨x * z + b * y, y * z - a * x, z ^ 2 + a * b, fun h => ?_, ?_⟩
      · have := h.2.2
        nlinarith [sq_nonneg z]
      · linear_combination (z ^ 2 + a * b) * hk
    · exact ⟨x, y, z, hne, by linear_combination hk⟩

/-- Sufficiency in general, by symmetry from the case of signs `+, +, -`. -/
private theorem exists_ternary_of_conditions {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ha' : Squarefree a) (hb' : Squarefree b) (hc' : Squarefree c) (hab : IsCoprime a b)
    (hbc : IsCoprime b c) (hac : IsCoprime a c) (hpos : ¬(0 < a ∧ 0 < b ∧ 0 < c))
    (hneg : ¬(a < 0 ∧ b < 0 ∧ c < 0)) (h1 : ∃ t : ℤ, t ^ 2 ≡ -(a * b) [ZMOD c])
    (h2 : ∃ s : ℤ, s ^ 2 ≡ -(a * c) [ZMOD b]) (h3 : ∃ r : ℤ, r ^ 2 ≡ -(b * c) [ZMOD a]) :
    ∃ x y z : ℤ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 := by
  have na := squarefree_neg_of_squarefree ha'
  have nb := squarefree_neg_of_squarefree hb'
  have nc := squarefree_neg_of_squarefree hc'
  rcases ha.lt_or_gt with ha0 | ha0 <;> rcases hb.lt_or_gt with hb0 | hb0 <;>
    rcases hc.lt_or_gt with hc0 | hc0
  · exact absurd ⟨ha0, hb0, hc0⟩ hneg
  · -- `-a, -b > 0 > -c`
    obtain ⟨x, y, z, hne, h⟩ := exists_ternary_of_pos_pos_neg (neg_pos.mpr ha0)
      (neg_pos.mpr hb0) (neg_lt_zero.mpr hc0) na nb nc hab.neg_neg hbc.neg_neg hac.neg_neg
      (by simpa [Int.modEq_neg] using h1) (by simpa [Int.modEq_neg] using h2)
      (by simpa [Int.modEq_neg] using h3)
    exact ⟨x, y, z, hne, by linear_combination -h⟩
  · -- `-a, -c > 0 > -b`
    obtain ⟨x, z, y, hne, h⟩ := exists_ternary_of_pos_pos_neg (neg_pos.mpr ha0)
      (neg_pos.mpr hc0) (neg_lt_zero.mpr hb0) na nc nb hac.neg_neg hbc.symm.neg_neg hab.neg_neg
      (by simpa [Int.modEq_neg] using h2) (by simpa [Int.modEq_neg] using h1)
      (by simpa [Int.modEq_neg, mul_comm] using h3)
    exact ⟨x, y, z, by tauto, by linear_combination -h⟩
  · -- `b, c > 0 > a`
    obtain ⟨y, z, x, hne, h⟩ := exists_ternary_of_pos_pos_neg hb0 hc0 ha0 hb' hc' ha' hbc
      hac.symm hab.symm (by simpa [mul_comm] using h3) (by simpa [mul_comm] using h1)
      (by simpa [mul_comm] using h2)
    exact ⟨x, y, z, by tauto, by linear_combination h⟩
  · -- `-b, -c > 0 > -a`
    obtain ⟨y, z, x, hne, h⟩ := exists_ternary_of_pos_pos_neg (neg_pos.mpr hb0)
      (neg_pos.mpr hc0) (neg_lt_zero.mpr ha0) nb nc na hbc.neg_neg hac.symm.neg_neg
      hab.symm.neg_neg (by simpa [Int.modEq_neg, mul_comm] using h3)
      (by simpa [Int.modEq_neg, mul_comm] using h1) (by simpa [Int.modEq_neg, mul_comm] using h2)
    exact ⟨x, y, z, by tauto, by linear_combination -h⟩
  · -- `a, c > 0 > b`
    obtain ⟨x, z, y, hne, h⟩ := exists_ternary_of_pos_pos_neg ha0 hc0 hb0 ha' hc' hb' hac
      hbc.symm hab h2 h1 (by simpa [mul_comm] using h3)
    exact ⟨x, y, z, by tauto, by linear_combination h⟩
  · exact exists_ternary_of_pos_pos_neg ha0 hb0 hc0 ha' hb' hc' hab hbc hac h1 h2 h3
  · exact absurd ⟨ha0, hb0, hc0⟩ hpos

/-- **Legendre's theorem on $a x^2 + b y^2 + c z^2 = 0$.** Let $a, b, c$ be nonzero integers,
square free, pairwise relatively prime and not all positive nor all negative. Then
$a x^2 + b y^2 + c z^2 = 0$ has a nontrivial integral solution, one with $(x, y, z) \neq (0, 0, 0)$,
if and only if $-ab$ is a square modulo $c$, $-ac$ is a square modulo $b$ and $-bc$ is a square
modulo $a$. Here an integer $m$ is a square modulo a nonzero integer $n$ when
$x^2 \equiv m \pmod{n}$ for some integer $x$; a congruence modulo $n$ is one modulo $|n|$.

Source: K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed.,
Graduate Texts in Mathematics 84, Springer, 1990, Chapter 17, §3, Proposition 17.3.1, p. 273. -/
theorem exists_ternary_eq_zero_iff {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ha' : Squarefree a) (hb' : Squarefree b) (hc' : Squarefree c) (hab : IsCoprime a b)
    (hbc : IsCoprime b c) (hac : IsCoprime a c) (hpos : ¬(0 < a ∧ 0 < b ∧ 0 < c))
    (hneg : ¬(a < 0 ∧ b < 0 ∧ c < 0)) :
    (∃ x y z : ℤ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) ↔
      (∃ x : ℤ, x ^ 2 ≡ -(a * b) [ZMOD c]) ∧ (∃ x : ℤ, x ^ 2 ≡ -(a * c) [ZMOD b]) ∧
        ∃ x : ℤ, x ^ 2 ≡ -(b * c) [ZMOD a] := by
  constructor
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨exists_sq_modEq_of_ternary hc hc' hac _ x y z rfl hne h,
      exists_sq_modEq_of_ternary hb hb' hab _ x z y rfl (by tauto) (by linear_combination h),
      exists_sq_modEq_of_ternary ha ha' hab.symm _ y z x rfl (by tauto)
        (by linear_combination h)⟩
  · rintro ⟨h1, h2, h3⟩
    exact exists_ternary_of_conditions ha hb hc ha' hb' hc' hab hbc hac hpos hneg h1 h2 h3

end Int
