/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Hasse–Minkowski theorem for diagonal ternary forms over `ℚ`

Let $a, b, c$ be nonzero rationals. If $a x^2 + b y^2 + c z^2 = 0$ has a solution other than
$(0, 0, 0)$ over $\mathbb{R}$ and over $\mathbb{Q}_p$ for every prime $p$, then it has one over
$\mathbb{Q}$ (`Rat.exists_ternary_eq_zero_of_forall_local`). This is the case $n = 3$ of the
Hasse–Minkowski theorem, and the proof follows A. V. Sutherland, *18.782 Introduction to
Arithmetic Geometry*, MIT, Fall 2013, Lecture 11, §11.3, proof of Theorem 11.12, case $n = 3$,
pp. 4–5, <https://math.mit.edu/classes/18.782/2013fa/LectureNotes11.pdf>.

Dividing by $-c$ and absorbing square factors into the variables, the form becomes
$z^2 - a x^2 - b y^2$ with $a, b$ nonzero squarefree integers. We argue by strong induction on
$|a| + |b|$, after swapping $a$ and $b$ so that $|a| \le |b|$.

* If $a = 1$, then $(1, 1, 0)$ is a zero. If $|b| = 1$, then $a, b \in \{\pm 1\}$; the case
  $a = b = -1$ is excluded by the real solution, and if $b = 1$ then $(1, 0, 1)$ is a zero.
* Otherwise $|b| \ge 2$. For a prime $p \mid b$, rescale a $\mathbb{Q}_p$-zero to a primitive
  zero $(z_0, x_0, y_0)$ over $\mathbb{Z}_p$. If $p \mid x_0$, then $p \mid z_0$, so
  $p^2 \mid b y_0^2$ and, $b$ being squarefree, $p \mid y_0$, contradicting primitivity; hence
  $a \equiv (z_0/x_0)^2$ modulo $p$. By the Chinese remainder theorem $a \equiv t^2 \pmod b$ for
  some integer $t$ with $|t| \le |b|/2$. Write $t^2 - a = b b'$; then $b' \ne 0$, as a squarefree
  $a \ne 1$ is not a square, and $|b'| \le |b|/4 + 1 < |b|$.
* Over any field, if $t^2 - a = b b'$ with $b \ne 0$, a zero $(z, x, y)$ of $z^2 - a x^2 - b y^2$
  gives the zero $(t z + a x, t x + z, b y)$ of $z^2 - a x^2 - b' y^2$ when $y \ne 0$, by the
  identity $(t z + a x)^2 - a (t x + z)^2 = (t^2 - a)(z^2 - a x^2)$, and $(z, x, 0)$ is itself a
  zero when $y = 0$. As the hypothesis is symmetric in $b$ and $b'$, the form with $b$ has a
  nontrivial zero over $\mathbb{R}$, $\mathbb{Q}_p$ or $\mathbb{Q}$ exactly when the form with $b'$
  does. Here the source argues with the Hilbert symbol instead.
* Writing $b' = c s^2$ with $c$ squarefree, $|a| + |c| < |a| + |b|$, and the induction hypothesis
  applies to $z^2 - a x^2 - c y^2$.
-/

set_option autoImplicit false

@[expose] public section

namespace Rat

/-- The form `z ^ 2 - a x ^ 2 - b y ^ 2` has a zero other than `(0, 0, 0)` over `K`. -/
private def HasZero (K : Type*) [Field K] (a b : K) : Prop :=
  ∃ z x y : K, ¬(z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0

section Field

variable {K : Type*} [Field K]

private theorem HasZero.swap {a b : K} (h : HasZero K a b) : HasZero K b a := by
  obtain ⟨z, x, y, hne, h⟩ := h
  exact ⟨z, y, x, by tauto, by linear_combination h⟩

private theorem HasZero.of_mul_sq_right {a b c : K} (hc : c ≠ 0) (h : HasZero K a (b * c ^ 2)) :
    HasZero K a b := by
  obtain ⟨z, x, y, hne, h⟩ := h
  refine ⟨z, x, c * y, ?_, by linear_combination h⟩
  rintro ⟨rfl, rfl, h3⟩
  exact hne ⟨rfl, rfl, (mul_eq_zero.1 h3).resolve_left hc⟩

private theorem hasZero_mul_sq_right {a b c : K} (hc : c ≠ 0) :
    HasZero K a (b * c ^ 2) ↔ HasZero K a b := by
  refine ⟨HasZero.of_mul_sq_right hc, fun h => HasZero.of_mul_sq_right (inv_ne_zero hc) ?_⟩
  rwa [mul_assoc, ← mul_pow, mul_inv_cancel₀ hc, one_pow, mul_one]

private theorem hasZero_mul_sq_left {a b c : K} (hc : c ≠ 0) :
    HasZero K (a * c ^ 2) b ↔ HasZero K a b :=
  ⟨fun h => (hasZero_mul_sq_right hc).1 h.swap |>.swap,
    fun h => ((hasZero_mul_sq_right hc).2 h.swap).swap⟩

/-- If `t ^ 2 - a = b b'` with `b ≠ 0`, a zero of `z ^ 2 - a x ^ 2 - b y ^ 2` gives one of
`z ^ 2 - a x ^ 2 - b' y ^ 2`, as `z ^ 2 - a x ^ 2` is multiplicative. -/
private theorem HasZero.transfer {a b b' t : K} (hb : b ≠ 0) (ht : t ^ 2 - a = b * b')
    (h : HasZero K a b) : HasZero K a b' := by
  obtain ⟨z, x, y, hne, h⟩ := h
  by_cases hy : y = 0
  · subst hy
    exact ⟨z, x, 0, hne, by linear_combination h⟩
  · refine ⟨t * z + a * x, t * x + z, b * y,
      fun h' => hy ((mul_eq_zero.1 h'.2.2).resolve_left hb), ?_⟩
    linear_combination (t ^ 2 - a) * h + b * y ^ 2 * ht

private theorem ternary_iff {a b c : K} (hc : c ≠ 0) :
    (∃ x y z : K, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) ↔
      HasZero K (-a / c) (-b / c) := by
  constructor
  · rintro ⟨x, y, z, hne, h⟩
    exact ⟨z, x, y, by tauto, by linear_combination c⁻¹ * h - z ^ 2 * mul_inv_cancel₀ hc⟩
  · rintro ⟨z, x, y, hne, h⟩
    exact ⟨x, y, z, by tauto,
      by linear_combination c * h - (a * x ^ 2 + b * y ^ 2) * mul_inv_cancel₀ hc⟩

end Field

/-- Every nonzero integer is a squarefree integer times a nonzero square. -/
private theorem exists_squarefree_mul_sq_int (n : ℤ) (hn : n ≠ 0) :
    ∃ m s : ℤ, Squarefree m ∧ s ≠ 0 ∧ n = m * s ^ 2 := by
  obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.2 hn)
  have hsq' : Squarefree (a : ℤ) := Int.squarefree_natCast.2 hsq
  rcases Int.natAbs_eq n with h | h
  · refine ⟨a, b, hsq', by exact_mod_cast hb.ne', ?_⟩
    rw [h, ← hab]; push_cast; ring
  · refine ⟨-a, b, ?_, by exact_mod_cast hb.ne', ?_⟩
    · rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.squarefree_natAbs]; exact hsq'
    · rw [h, ← hab]; push_cast; ring

/-- Every nonzero rational is a squarefree integer times a nonzero square. -/
private theorem exists_squarefree_mul_sq (q : ℚ) (hq : q ≠ 0) :
    ∃ m : ℤ, Squarefree m ∧ ∃ r : ℚ, r ≠ 0 ∧ q = m * r ^ 2 := by
  have hd : (q.den : ℚ) ≠ 0 := by positivity
  obtain ⟨m, s, hm, hs, h⟩ := exists_squarefree_mul_sq_int (q.num * q.den)
    (mul_ne_zero (Rat.num_ne_zero.2 hq) (by exact_mod_cast q.den_ne_zero))
  refine ⟨m, hm, s / q.den, div_ne_zero (by exact_mod_cast hs) hd, ?_⟩
  have h' : (q.num : ℚ) * q.den = m * s ^ 2 := by exact_mod_cast h
  have hq' : q * q.den = q.num := Rat.mul_den_eq_num q
  rw [div_pow, mul_div_assoc', eq_div_iff (pow_ne_zero 2 hd), ← h', ← hq']
  ring

/-- A squarefree integer that is a square is `1`. -/
private theorem eq_one_of_squarefree_of_sq_eq {a t : ℤ} (ha : Squarefree a) (h : t ^ 2 = a) :
    a = 1 := by
  have : IsUnit t := ha t ⟨1, by rw [← h]; ring⟩
  rw [← h]
  rcases Int.isUnit_iff.1 this with rfl | rfl <;> simp

/-- A nonzero triple in `ℚ_[p]` can be rescaled so that all entries have norm at most `1` and one
has norm `1`. -/
private theorem exists_primitive_rescale {p : ℕ} [Fact p.Prime] (u v w : ℚ_[p])
    (h : ¬(u = 0 ∧ v = 0 ∧ w = 0)) :
    ∃ c : ℚ_[p], ‖c * u‖ ≤ 1 ∧ ‖c * v‖ ≤ 1 ∧ ‖c * w‖ ≤ 1 ∧
      (‖c * u‖ = 1 ∨ ‖c * v‖ = 1 ∨ ‖c * w‖ = 1) := by
  have key : ∀ m : ℚ_[p], ‖u‖ ≤ ‖m‖ → ‖v‖ ≤ ‖m‖ → ‖w‖ ≤ ‖m‖ → (m = u ∨ m = v ∨ m = w) →
      ∃ c : ℚ_[p], ‖c * u‖ ≤ 1 ∧ ‖c * v‖ ≤ 1 ∧ ‖c * w‖ ≤ 1 ∧
        (‖c * u‖ = 1 ∨ ‖c * v‖ = 1 ∨ ‖c * w‖ = 1) := by
    intro m hu hv hw hmem
    have hm : m ≠ 0 := by
      rintro rfl
      simp only [norm_zero, norm_le_zero_iff] at hu hv hw
      exact h ⟨hu, hv, hw⟩
    have hm' : 0 < ‖m‖ := norm_pos_iff.2 hm
    have hle : ∀ x : ℚ_[p], ‖x‖ ≤ ‖m‖ → ‖m⁻¹ * x‖ ≤ 1 := fun x hx => by
      rw [norm_mul, norm_inv, inv_mul_le_iff₀ hm', mul_one]; exact hx
    refine ⟨m⁻¹, hle u hu, hle v hv, hle w hw, ?_⟩
    rcases hmem with rfl | rfl | rfl <;> simp [hm]
  rcases le_total ‖u‖ ‖v‖ with h1 | h1 <;> rcases le_total ‖v‖ ‖w‖ with h2 | h2 <;>
    rcases le_total ‖u‖ ‖w‖ with h3 | h3 <;>
    first
    | exact key u le_rfl (by linarith) (by linarith) (Or.inl rfl)
    | exact key v (by linarith) le_rfl (by linarith) (Or.inr (Or.inl rfl))
    | exact key w (by linarith) (by linarith) le_rfl (Or.inr (Or.inr rfl))

private theorem toZMod_eq_zero_iff {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) :
    PadicInt.toZMod x = 0 ↔ (p : ℤ_[p]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

/-- If `p ∣ b` with `b` squarefree and `z ^ 2 - a x ^ 2 - b y ^ 2` has a nontrivial zero over
`ℚ_[p]`, then `a` is a square modulo `p`. -/
private theorem exists_sq_sub_dvd_of_padic {a b : ℤ} (hb : Squarefree b) {p : ℕ} [hp : Fact p.Prime]
    (hpb : (p : ℤ) ∣ b) (h : HasZero ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p])) :
    ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - a := by
  obtain ⟨z, x, y, hne, h⟩ := h
  obtain ⟨c, hzc, hxc, hyc, hone⟩ := exists_primitive_rescale z x y hne
  set z0 : ℤ_[p] := ⟨c * z, hzc⟩
  set x0 : ℤ_[p] := ⟨c * x, hxc⟩
  set y0 : ℤ_[p] := ⟨c * y, hyc⟩
  have heq : z0 ^ 2 - (a : ℤ_[p]) * x0 ^ 2 - (b : ℤ_[p]) * y0 ^ 2 = 0 := by
    apply Subtype.ext
    change (c * z) ^ 2 - (a : ℚ_[p]) * (c * x) ^ 2 - (b : ℚ_[p]) * (c * y) ^ 2 = 0
    linear_combination c ^ 2 * h
  -- one of `z0, x0, y0` is a unit, so not all reduce to `0` modulo `p`
  have hnot : ¬((p : ℤ_[p]) ∣ z0 ∧ (p : ℤ_[p]) ∣ x0 ∧ (p : ℤ_[p]) ∣ y0) := by
    rintro ⟨h1, h2, h3⟩
    rw [← PadicInt.norm_lt_one_iff_dvd] at h1 h2 h3
    rcases hone with h4 | h4 | h4
    · exact absurd h4 h1.ne
    · exact absurd h4 h2.ne
    · exact absurd h4 h3.ne
  have hbp : (b : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd b p).2 hpb
  have hZ : (PadicInt.toZMod z0) ^ 2 = (a : ZMod p) * (PadicInt.toZMod x0) ^ 2 := by
    have := congrArg PadicInt.toZMod heq
    simp only [map_sub, map_mul, map_pow, map_intCast, map_zero, hbp, zero_mul, sub_zero] at this
    linear_combination this
  by_cases hX : PadicInt.toZMod x0 = 0
  · exfalso
    have hZ0 : PadicInt.toZMod z0 = 0 := by
      rw [hX] at hZ; simpa using hZ
    obtain ⟨x1, hx1⟩ := (toZMod_eq_zero_iff x0).1 hX
    obtain ⟨z1, hz1⟩ := (toZMod_eq_zero_iff z0).1 hZ0
    obtain ⟨b1, hb1⟩ := hpb
    have hpb1 : ¬(p : ℤ) ∣ b1 := by
      rintro ⟨b2, rfl⟩
      have := hb (p : ℤ) ⟨b2, by rw [hb1]; ring⟩
      have h1 := Int.isUnit_iff_natAbs_eq.1 this
      rw [Int.natAbs_natCast] at h1
      exact hp.out.one_lt.ne' h1
    have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have heq' : (p : ℤ_[p]) * ((p : ℤ_[p]) * z1 ^ 2 - (a : ℤ_[p]) * (p : ℤ_[p]) * x1 ^ 2 -
        (b1 : ℤ_[p]) * y0 ^ 2) = 0 := by
      rw [hx1, hz1, hb1] at heq
      push_cast at heq
      linear_combination heq
    have heq'' := congrArg PadicInt.toZMod ((mul_eq_zero.1 heq').resolve_left hp0)
    simp only [map_sub, map_mul, map_pow, map_intCast, map_natCast, ZMod.natCast_self,
      zero_mul, mul_zero, zero_sub, map_zero] at heq''
    have hb1p : (b1 : ZMod p) ≠ 0 := fun h0 =>
      hpb1 ((ZMod.intCast_zmod_eq_zero_iff_dvd b1 p).1 h0)
    have hY : PadicInt.toZMod y0 = 0 := by
      have := (mul_eq_zero.1 (by linear_combination -heq'' :
        (b1 : ZMod p) * PadicInt.toZMod y0 ^ 2 = 0)).resolve_left hb1p
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    exact hnot ⟨(toZMod_eq_zero_iff z0).1 hZ0, (toZMod_eq_zero_iff x0).1 hX,
      (toZMod_eq_zero_iff y0).1 hY⟩
  · obtain ⟨r, hr⟩ := ZMod.intCast_surjective (PadicInt.toZMod z0 / PadicInt.toZMod x0)
    refine ⟨r, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 ?_⟩
    push_cast
    rw [hr, div_pow, hZ]
    field_simp
    ring

/-- Chinese remaindering for square roots modulo coprime moduli. -/
private theorem exists_sq_sub_dvd_mul {a m n r s : ℤ} (hmn : IsCoprime m n)
    (hr : m ∣ r ^ 2 - a) (hs : n ∣ s ^ 2 - a) : ∃ u : ℤ, m * n ∣ u ^ 2 - a := by
  obtain ⟨α, β, hab⟩ := hmn
  have key : ∀ (k v : ℤ), k ∣ (r * β * n + s * α * m) - v → k ∣ v ^ 2 - a →
      k ∣ (r * β * n + s * α * m) ^ 2 - a := fun k v h1 h2 => by
    have := (h1.mul_right ((r * β * n + s * α * m) + v)).add h2
    convert this using 1; ring
  refine ⟨r * β * n + s * α * m, IsCoprime.mul_dvd ⟨α, β, hab⟩ (key m r ?_ hr) (key n s ?_ hs)⟩
  · exact ⟨α * (s - r), by linear_combination r * hab⟩
  · exact ⟨β * (r - s), by linear_combination s * hab⟩

/-- If `b` is squarefree and `a` is a square modulo every prime factor of `b`, then `a` is a
square modulo `b`. -/
private theorem exists_sq_sub_dvd_of_squarefree {a b : ℤ} (hb : Squarefree b)
    (hloc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ b → ∃ r : ℤ, (p : ℤ) ∣ r ^ 2 - a) :
    ∃ r : ℤ, b ∣ r ^ 2 - a := by
  suffices h : ∀ n : ℕ, n ∣ b.natAbs → ∃ r : ℤ, (n : ℤ) ∣ r ^ 2 - a by
    obtain ⟨r, hr⟩ := h b.natAbs dvd_rfl
    exact ⟨r, Int.natAbs_dvd.1 hr⟩
  have hb' : Squarefree b.natAbs := Int.squarefree_natAbs.2 hb
  have hb0 : b.natAbs ≠ 0 := by simpa using hb.ne_zero
  intro n
  induction n using Nat.recOnPrimeCoprime with
  | zero => intro h; exact absurd (Nat.eq_zero_of_zero_dvd h) hb0
  | prime_pow p k hp =>
    intro h
    rcases k with _ | _ | k
    · exact ⟨0, by simp⟩
    · rw [pow_one] at h ⊢
      exact hloc p hp (Int.natCast_dvd.2 h)
    · exfalso
      have : p * p ∣ b.natAbs := (Dvd.intro (p ^ k) (by ring)).trans h
      exact (Nat.squarefree_iff_prime_squarefree.1 hb') p hp this
  | coprime m n _ _ hmn ihm ihn =>
    intro h
    obtain ⟨r, hr⟩ := ihm ((Dvd.intro n rfl).trans h)
    obtain ⟨s, hs⟩ := ihn ((Dvd.intro_left m rfl).trans h)
    obtain ⟨u, hu⟩ := exists_sq_sub_dvd_mul (Nat.isCoprime_iff_coprime.2 hmn) hr hs
    exact ⟨u, by exact_mod_cast hu⟩

/-- A square root modulo `b` can be taken with absolute value at most `|b| / 2`. -/
private theorem exists_sq_sub_dvd_small {a b : ℤ} (hb : b ≠ 0) (h : ∃ r : ℤ, b ∣ r ^ 2 - a) :
    ∃ t : ℤ, b ∣ t ^ 2 - a ∧ 2 * |t| ≤ |b| := by
  obtain ⟨r, hr⟩ := h
  have hm : 0 < |b| := abs_pos.2 hb
  have key : ∀ t, b ∣ t - r → b ∣ t ^ 2 - a := fun t ht => by
    have := (ht.mul_right (t + r)).add hr
    convert this using 1; ring
  have h0 : 0 ≤ r % |b| := Int.emod_nonneg _ hm.ne'
  have h1 : r % |b| < |b| := Int.emod_lt_of_pos _ hm
  have hd : b ∣ r % |b| - r := by
    have : |b| ∣ r % |b| - r := ⟨-(r / |b|), by linear_combination Int.emod_def r |b|⟩
    exact (abs_dvd _ _).1 this
  by_cases h2 : 2 * (r % |b|) ≤ |b|
  · exact ⟨r % |b|, key _ hd, by rwa [abs_of_nonneg h0]⟩
  · refine ⟨r % |b| - |b|, key _ ?_, ?_⟩
    · have := hd.sub ((dvd_abs b b).2 dvd_rfl)
      convert this using 1; ring
    · rw [abs_of_neg (by linarith)]; linarith

/-- The case `n = 3` of the Hasse–Minkowski theorem for `z ^ 2 - a x ^ 2 - b y ^ 2` with `a, b`
squarefree integers, by induction on `|a| + |b|`. -/
private theorem hasZero_of_forall_local (n : ℕ) : ∀ a b : ℤ, a.natAbs + b.natAbs = n →
    Squarefree a → Squarefree b → HasZero ℝ (a : ℝ) (b : ℝ) →
    (∀ (p : ℕ) [Fact p.Prime], HasZero ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p])) →
    HasZero ℚ (a : ℚ) (b : ℚ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have step : ∀ a b : ℤ, a.natAbs ≤ b.natAbs → a.natAbs + b.natAbs = n →
      Squarefree a → Squarefree b → HasZero ℝ (a : ℝ) (b : ℝ) →
      (∀ (p : ℕ) [Fact p.Prime], HasZero ℚ_[p] (a : ℚ_[p]) (b : ℚ_[p])) →
      HasZero ℚ (a : ℚ) (b : ℚ) := by
    intro a b hle hn ha hb hR hP
    have ha0 := ha.ne_zero
    have hb0 := hb.ne_zero
    by_cases ha1 : a = 1
    · subst ha1
      exact ⟨1, 1, 0, by simp, by push_cast; ring⟩
    by_cases hb1 : b.natAbs = 1
    · have haabs : a.natAbs = 1 := by have := Int.natAbs_pos.2 ha0; omega
      rcases Int.natAbs_eq_iff.1 haabs with rfl | rfl
      · exact absurd rfl ha1
      rcases Int.natAbs_eq_iff.1 hb1 with rfl | rfl
      · exact ⟨1, 0, 1, by simp, by push_cast; ring⟩
      · exfalso
        obtain ⟨z, x, y, hne, h⟩ := hR
        push_cast at h
        have hz : z ^ 2 = 0 := by nlinarith [sq_nonneg z, sq_nonneg x, sq_nonneg y]
        have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg z, sq_nonneg x, sq_nonneg y]
        have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg z, sq_nonneg x, sq_nonneg y]
        exact hne ⟨pow_eq_zero_iff two_ne_zero |>.1 hz, pow_eq_zero_iff two_ne_zero |>.1 hx,
          pow_eq_zero_iff two_ne_zero |>.1 hy⟩
    have hb2 : 2 ≤ b.natAbs := by have := Int.natAbs_pos.2 hb0; omega
    obtain ⟨t, ⟨b', hb'⟩, htb⟩ := exists_sq_sub_dvd_small hb0
      (exists_sq_sub_dvd_of_squarefree hb fun p hp hpb => by
        have := Fact.mk hp
        exact exists_sq_sub_dvd_of_padic hb hpb (hP p))
    have hb'0 : b' ≠ 0 := by
      rintro rfl
      exact ha1 (eq_one_of_squarefree_of_sq_eq (t := t) ha (by linarith))
    obtain ⟨c, s, hc, hs, hbc⟩ := exists_squarefree_mul_sq_int b' hb'0
    have hcb' : c.natAbs ≤ b'.natAbs := by
      rw [hbc, Int.natAbs_mul, Int.natAbs_pow]
      exact Nat.le_mul_of_pos_right _ (pow_pos (Int.natAbs_pos.2 hs) 2)
    have hlt : b'.natAbs < b.natAbs := by
      zify at hle hb2 ⊢
      have e1 : |b| * |b'| = |t ^ 2 - a| := by rw [← abs_mul, hb']
      have e2 : |t ^ 2 - a| ≤ t ^ 2 + |a| := by
        have := abs_sub (t ^ 2) a
        rwa [abs_of_nonneg (sq_nonneg t)] at this
      have e3 : 4 * t ^ 2 ≤ |b| ^ 2 := by
        have : (2 * |t|) ^ 2 ≤ |b| ^ 2 := pow_le_pow_left₀ (by positivity) htb 2
        nlinarith [sq_abs t]
      have e4 : |b| * (4 * |b'|) ≤ |b| * (|b| + 4) := by nlinarith
      have e5 : 4 * |b'| ≤ |b| + 4 := le_of_mul_le_mul_left e4 (by positivity)
      linarith
    have hK : ∀ (K : Type) [Field K] [CharZero K], HasZero K (a : K) (b : K) →
        HasZero K (a : K) (c : K) := by
      intro K _ _ h
      refine (hasZero_mul_sq_right (c := (s : K)) (by exact_mod_cast hs)).1 ?_
      have := h.transfer (t := (t : K)) (b' := (b' : K)) (by exact_mod_cast hb0)
        (by exact_mod_cast hb')
      rwa [hbc, Int.cast_mul, Int.cast_pow] at this
    have hQ := ih (a.natAbs + c.natAbs) (by omega) a c rfl ha hc (hK ℝ hR)
      (fun p _ => hK ℚ_[p] (hP p))
    refine ((hasZero_mul_sq_right (c := (s : ℚ)) (by exact_mod_cast hs)).2 hQ).transfer
      (t := (t : ℚ)) ?_ ?_
    · rw [← Int.cast_pow, ← Int.cast_mul, ← hbc]; exact_mod_cast hb'0
    · have h' : t ^ 2 - a = c * s ^ 2 * b := by rw [hb', hbc]; ring
      exact_mod_cast h'
  intro a b hn ha hb hR hP
  rcases le_total a.natAbs b.natAbs with h | h
  · exact step a b h hn ha hb hR hP
  · exact (step b a h (by omega) hb ha hR.swap (fun p _ => (hP p).swap)).swap

end Rat

open Rat in
/-- **Hasse–Minkowski theorem for diagonal ternary forms over `ℚ`.** Let `a`, `b`, `c` be nonzero
rationals. If `a x ^ 2 + b y ^ 2 + c z ^ 2 = 0` has a solution `(x, y, z) ≠ (0, 0, 0)` in `ℝ` and
in `ℚ_[p]` for every prime `p`, then it has a solution `(x, y, z) ≠ (0, 0, 0)` in `ℚ`.

This is the case `n = 3` of A. V. Sutherland, *18.782 Introduction to Arithmetic Geometry*, MIT,
Fall 2013, Lecture 11, Theorem 11.12, following the proof of that case given there, pp. 4–5. -/
theorem Rat.exists_ternary_eq_zero_of_forall_local {a b c : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hreal : ∃ x y z : ℝ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ (a : ℝ) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0)
    (hpadic : ∀ (p : ℕ) [Fact p.Prime], ∃ x y z : ℚ_[p], ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
      (a : ℚ_[p]) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) :
    ∃ x y z : ℚ, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ a * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0 := by
  obtain ⟨a1, ha1, qa, hqa, hA⟩ :=
    exists_squarefree_mul_sq (-a / c) (div_ne_zero (neg_ne_zero.2 ha) hc)
  obtain ⟨b1, hb1, qb, hqb, hB⟩ :=
    exists_squarefree_mul_sq (-b / c) (div_ne_zero (neg_ne_zero.2 hb) hc)
  have red : ∀ (K : Type) [Field K] [CharZero K],
      (∃ x y z : K, ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧ (a : K) * x ^ 2 + b * y ^ 2 + c * z ^ 2 = 0) ↔
        HasZero K (a1 : K) (b1 : K) := by
    intro K _ _
    have hcK : (c : K) ≠ 0 := by exact_mod_cast hc
    have hAK : -(a : K) / c = (a1 : K) * (qa : K) ^ 2 := by exact_mod_cast hA
    have hBK : -(b : K) / c = (b1 : K) * (qb : K) ^ 2 := by exact_mod_cast hB
    rw [ternary_iff hcK, hAK, hBK, hasZero_mul_sq_left (by exact_mod_cast hqa),
      hasZero_mul_sq_right (by exact_mod_cast hqb)]
  have hQ := hasZero_of_forall_local _ a1 b1 rfl ha1 hb1 ((red ℝ).1 hreal)
    (fun p _ => (red ℚ_[p]).1 (hpadic p))
  simpa only [Rat.cast_id] using (red ℚ).2 hQ
