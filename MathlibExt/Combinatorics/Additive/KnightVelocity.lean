/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.KnightDistance
public import Mathlib.Data.Int.Interval
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Velocity formula for the (a, b)-knight

For natural numbers $1 \le a < b$ with $\gcd(a, b) = 1$ and $a + b$ odd, this file proves
Táfula's velocity formula `knight_velocity_formula`: the quotient of $2h/3$ by the average
piece distance of the $(a,b)$-knight over the max-norm ball $B_h$ tends to
$2(a+b)b^2/(a^2+3b^2)$. It also defines the max-norm ball `maxNormBall` and counts its points
(`card_maxNormBall`).

The proof follows Sections 2.1 and 2.3 of the source. Write
$F(x, y) = \max(\max(|x|, |y|)/b, (|x| + |y|)/(a + b))$. Each knight move changes $|x|$ and
$|y|$ by at most $b$ and $|x| + |y|$ by at most $a + b$, so the piece distance is at least $F$.
The moves $(b, a)$ and $(b, -a)$ below the slope $a/b$, or $(b, a)$ and $(a, b)$ above it, reach
a point within max-norm distance $a + b$ of the target, and `exists_knight_path_on_box`
(Lemma 2.1) finishes the path, so the piece distance is at most $F + 13b$. The lattice sum of
$F$ over $B_h$ is then evaluated up to an error $O(h^2)$ by telescoping.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), Definition 1.2, Theorem 1.3 and Section 2.
-/

namespace MetaMathlibExt

open Pointwise

@[expose] public section

/--
**Max-norm ball.** For a natural number $h$, the max-norm ball $B_h \subset \mathbb{Z}^2$ is the
product of two copies of the integer interval $\{-h, \dots, h\}$, that is, the set of lattice
points $(x, y)$ with $\max(|x|, |y|) \le h$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definition of `B_h`.
-/
public def maxNormBall (h : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(h : ℤ)) h ×ˢ Finset.Icc (-(h : ℤ)) h

/--
**Number of points in the max-norm ball.** For every natural number $h$, the max-norm ball
$B_h = \{(x, y) \in \mathbb{Z}^2 : \max(|x|, |y|) \le h\}$ has exactly $(2h+1)^2$ points.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definition of `B_h`.
-/
public theorem card_maxNormBall (h : ℕ) : (maxNormBall h).card = (2 * h + 1) ^ 2 := by
  have hcard : (Finset.Icc (-(h : ℤ)) h).card = 2 * h + 1 := by
    rw [Int.card_Icc]
    omega
  simp [maxNormBall, Finset.card_product, hcard, pow_two]

end

namespace KnightVelocity

/-- The gauge `b |x| + b |y| + max 0 (a |x| - b |y|) + max 0 (a |y| - b |x|)`. For
`0 ≤ a ≤ b` it equals `max ((a + b) max(|x|, |y|), b (|x| + |y|))`, which is `b (a + b)` times
the asymptotic knight distance. -/
private def gauge (a b : ℤ) (p : ℤ × ℤ) : ℤ :=
  b * |p.1| + b * |p.2| + max 0 (a * |p.1| - b * |p.2|) + max 0 (a * |p.2| - b * |p.1|)

private theorem move_bounds {a b : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) {m : ℤ × ℤ}
    (hm : m ∈ knightMoves a b) : |m.1| ≤ b ∧ |m.2| ≤ b ∧ |m.1| + |m.2| ≤ a + b := by
  have hb : 0 ≤ b := ha.trans hab
  simp only [knightMoves, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [abs_neg, abs_of_nonneg ha, abs_of_nonneg hb] <;> omega

private theorem nsmul_bounds {a b : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ (n : ℕ) {p : ℤ × ℤ}, p ∈ n • knightMoves a b →
      |p.1| ≤ n * b ∧ |p.2| ≤ n * b ∧ |p.1| + |p.2| ≤ n * (a + b)
  | 0, p, hp => by
      rw [zero_nsmul, Finset.mem_zero] at hp
      subst hp
      simp
  | n + 1, p, hp => by
      rw [succ_nsmul, Finset.mem_add] at hp
      obtain ⟨u, hu, m, hm, rfl⟩ := hp
      obtain ⟨h1, h2, h3⟩ := nsmul_bounds ha hab n hu
      obtain ⟨k1, k2, k3⟩ := move_bounds ha hab hm
      have e1 := abs_add_le u.1 m.1
      have e2 := abs_add_le u.2 m.2
      simp only [Prod.fst_add, Prod.snd_add]
      push_cast
      refine ⟨by linarith, by linarith, by linarith⟩

/-- Lower bound: a sum of `n` knight moves has gauge at most `b (a + b) n`. -/
private theorem gauge_le_of_mem {a b : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) {n : ℕ} {p : ℤ × ℤ}
    (hp : p ∈ n • knightMoves a b) : gauge a b p ≤ b * (a + b) * n := by
  obtain ⟨h1, h2, h3⟩ := nsmul_bounds ha hab n hp
  have hX : 0 ≤ |p.1| := abs_nonneg _
  have hY : 0 ≤ |p.2| := abs_nonneg _
  have hn : (0 : ℤ) ≤ n := by positivity
  unfold gauge
  rcases le_total (a * |p.1| - b * |p.2|) 0 with c1 | c1 <;>
    rcases le_total (a * |p.2| - b * |p.1|) 0 with c2 | c2
  · rw [max_eq_left c1, max_eq_left c2]
    nlinarith
  · rw [max_eq_left c1, max_eq_right c2]
    nlinarith
  · rw [max_eq_right c1, max_eq_left c2]
    nlinarith
  · rw [max_eq_right c1, max_eq_right c2]
    nlinarith

private theorem map_mem_nsmul {A : Finset (ℤ × ℤ)} (f : ℤ × ℤ → ℤ × ℤ)
    (f0 : f 0 = 0) (fadd : ∀ u v, f (u + v) = f u + f v) (hf : ∀ m ∈ A, f m ∈ A) :
    ∀ (n : ℕ) {p : ℤ × ℤ}, p ∈ n • A → f p ∈ n • A
  | 0, p, hp => by
      rw [zero_nsmul, Finset.mem_zero] at hp ⊢
      rw [hp, f0]
  | n + 1, p, hp => by
      rw [succ_nsmul, Finset.mem_add] at hp ⊢
      obtain ⟨u, hu, m, hm, rfl⟩ := hp
      exact ⟨f u, map_mem_nsmul f f0 fadd hf n hu, f m, hf m hm, (fadd u m).symm⟩

private theorem negFst_mem_nsmul {a b : ℤ} {n : ℕ} {p : ℤ × ℤ}
    (hp : p ∈ n • knightMoves a b) : (-p.1, p.2) ∈ n • knightMoves a b := by
  refine map_mem_nsmul (fun q => (-q.1, q.2)) (by simp) (fun u v => ?_) (fun m hm => ?_) n hp
  · ext <;> simp [add_comm]
  · simp only [knightMoves, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem negSnd_mem_nsmul {a b : ℤ} {n : ℕ} {p : ℤ × ℤ}
    (hp : p ∈ n • knightMoves a b) : (p.1, -p.2) ∈ n • knightMoves a b := by
  refine map_mem_nsmul (fun q => (q.1, -q.2)) (by simp) (fun u v => ?_) (fun m hm => ?_) n hp
  · ext <;> simp [add_comm]
  · simp only [knightMoves, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem swap_mem_nsmul {a b : ℤ} {n : ℕ} {p : ℤ × ℤ}
    (hp : p ∈ n • knightMoves a b) : (p.2, p.1) ∈ n • knightMoves a b := by
  refine map_mem_nsmul (fun q => (q.2, q.1)) (by simp) (fun u v => rfl) (fun m hm => ?_) n hp
  simp only [knightMoves, Finset.mem_insert, Finset.mem_singleton] at hm ⊢
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- Below the slope `a / b`, use the moves `(b, a)` and `(b, -a)`. -/
private theorem exists_path_flat {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hc : Nat.Coprime a b) (ho : Odd (a + b)) {x y : ℤ} (hy : 0 ≤ y)
    (hyx : (b : ℤ) * y ≤ a * x) :
    ∃ n : ℕ, (x, y) ∈ n • knightMoves (a : ℤ) (b : ℤ) ∧ (b : ℤ) * n ≤ x + 13 * b * b := by
  set A : ℤ := ((a : ℕ) : ℤ) with hAdef
  set B : ℤ := ((b : ℕ) : ℤ) with hBdef
  have hA : 0 < A := by omega
  have hAB : A < B := by omega
  have hB : 0 < B := by omega
  have hx : 0 ≤ x := by nlinarith
  set N := x / B with hNdef
  set s := (A * x + B * y) / (2 * A * B) with hsdef
  have hq : 0 < 2 * A * B := by positivity
  have hN1 : B * N ≤ x := Int.mul_ediv_self_le hB.ne'
  have hN2 : x < B * N + B := Int.lt_mul_ediv_self_add hB
  have hs1 : 2 * A * B * s ≤ A * x + B * y := Int.mul_ediv_self_le hq.ne'
  have hs2 : A * x + B * y < 2 * A * B * s + 2 * A * B := Int.lt_mul_ediv_self_add hq
  have hs0 : 0 ≤ s := Int.ediv_nonneg (by positivity) hq.le
  have hBs : B * s ≤ x := by
    have : 2 * A * (B * s) ≤ 2 * A * x := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hsN : s ≤ N := by
    have : B * s < B * (N + 1) := by linarith
    have := lt_of_mul_lt_mul_left this hB.le
    omega
  set t := N - s with htdef
  have ht0 : 0 ≤ t := by omega
  have hAN1 : A * (B * N) ≤ A * x := mul_le_mul_of_nonneg_left hN1 hA.le
  have hAN2 : A * x < A * (B * N + B) := mul_lt_mul_of_pos_left hN2 hA
  have hr2a : y - A * (s - t) < A + B := by
    have : B * (y - A * (s - t)) < B * (A + B) := by nlinarith
    exact lt_of_mul_lt_mul_left this hB.le
  have hr2b : -(A + B) < y - A * (s - t) := by
    have : B * (-(A + B)) < B * (y - A * (s - t)) := by nlinarith
    exact lt_of_mul_lt_mul_left this hB.le
  have hr : max |x - B * N| |y - A * (s - t)| ≤ ((a + b : ℕ) : ℤ) := by
    push_cast
    rw [max_le_iff, abs_le, abs_le]
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨m, hm, hrmem⟩ := exists_knight_path_on_box ha hab hc ho (p := (x - B * N,
    y - A * (s - t))) hr
  have hsmem : s.toNat • ((B, A) : ℤ × ℤ) ∈ s.toNat • knightMoves A B :=
    Finset.nsmul_mem_nsmul (by simp [knightMoves])
  have htmem : t.toNat • ((B, -A) : ℤ × ℤ) ∈ t.toNat • knightMoves A B :=
    Finset.nsmul_mem_nsmul (by simp [knightMoves])
  have hmem := Finset.add_mem_add (Finset.add_mem_add hrmem hsmem) htmem
  rw [← add_nsmul, ← add_nsmul] at hmem
  refine ⟨m + s.toNat + t.toNat, ?_, ?_⟩
  · convert hmem using 1
    ext <;> simp [Int.toNat_of_nonneg hs0, Int.toNat_of_nonneg ht0] <;> ring
  · push_cast [Int.toNat_of_nonneg hs0, Int.toNat_of_nonneg ht0]
    have : (m : ℤ) ≤ 13 * B := by rw [hBdef]; exact_mod_cast hm
    nlinarith

/-- Above the slope `a / b`, use the moves `(b, a)` and `(a, b)`. -/
private theorem exists_path_steep {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hc : Nat.Coprime a b) (ho : Odd (a + b)) {x y : ℤ} (hyx : y ≤ x)
    (hxy : (a : ℤ) * x < b * y) :
    ∃ n : ℕ, (x, y) ∈ n • knightMoves (a : ℤ) (b : ℤ) ∧
      ((a : ℤ) + b) * n ≤ x + y + 13 * b * (a + b) := by
  set A : ℤ := ((a : ℕ) : ℤ) with hAdef
  set B : ℤ := ((b : ℕ) : ℤ) with hBdef
  have hA : 0 < A := by omega
  have hAB : A < B := by omega
  have hB : 0 < B := by omega
  set q := B * B - A * A with hqdef
  have hq : 0 < q := by nlinarith
  set s := (B * x - A * y) / q with hsdef
  set t := (B * y - A * x) / q with htdef
  have hs1 : q * s ≤ B * x - A * y := Int.mul_ediv_self_le hq.ne'
  have hs2 : B * x - A * y < q * s + q := Int.lt_mul_ediv_self_add hq
  have ht1 : q * t ≤ B * y - A * x := Int.mul_ediv_self_le hq.ne'
  have ht2 : B * y - A * x < q * t + q := Int.lt_mul_ediv_self_add hq
  have hs0 : 0 ≤ s := Int.ediv_nonneg (by nlinarith) hq.le
  have ht0 : 0 ≤ t := Int.ediv_nonneg (by nlinarith) hq.le
  have hr1a : 0 ≤ x - B * s - A * t := by
    have : q * 0 ≤ q * (x - B * s - A * t) := by nlinarith
    exact le_of_mul_le_mul_left this hq
  have hr1b : x - B * s - A * t < A + B := by
    have : q * (x - B * s - A * t) < q * (A + B) := by nlinarith
    exact lt_of_mul_lt_mul_left this hq.le
  have hr2a : 0 ≤ y - A * s - B * t := by
    have : q * 0 ≤ q * (y - A * s - B * t) := by nlinarith
    exact le_of_mul_le_mul_left this hq
  have hr2b : y - A * s - B * t < A + B := by
    have : q * (y - A * s - B * t) < q * (A + B) := by nlinarith
    exact lt_of_mul_lt_mul_left this hq.le
  have hst : (A + B) * (s + t) ≤ x + y := by
    have : (B - A) * ((A + B) * (s + t)) ≤ (B - A) * (x + y) := by nlinarith
    exact le_of_mul_le_mul_left this (by omega)
  have hr : max |x - B * s - A * t| |y - A * s - B * t| ≤ ((a + b : ℕ) : ℤ) := by
    push_cast
    rw [max_le_iff, abs_le, abs_le]
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨m, hm, hrmem⟩ := exists_knight_path_on_box ha hab hc ho (p := (x - B * s - A * t,
    y - A * s - B * t)) hr
  have hsmem : s.toNat • ((B, A) : ℤ × ℤ) ∈ s.toNat • knightMoves A B :=
    Finset.nsmul_mem_nsmul (by simp [knightMoves])
  have htmem : t.toNat • ((A, B) : ℤ × ℤ) ∈ t.toNat • knightMoves A B :=
    Finset.nsmul_mem_nsmul (by simp [knightMoves])
  have hmem := Finset.add_mem_add (Finset.add_mem_add hrmem hsmem) htmem
  rw [← add_nsmul, ← add_nsmul] at hmem
  refine ⟨m + s.toNat + t.toNat, ?_, ?_⟩
  · convert hmem using 1
    ext <;> simp [Int.toNat_of_nonneg hs0, Int.toNat_of_nonneg ht0] <;> ring
  · push_cast [Int.toNat_of_nonneg hs0, Int.toNat_of_nonneg ht0]
    have : (m : ℤ) ≤ 13 * B := by rw [hBdef]; exact_mod_cast hm
    nlinarith

private theorem gauge_ge_left (a b : ℤ) (p : ℤ × ℤ) : (a + b) * |p.1| ≤ gauge a b p := by
  unfold gauge
  have := le_max_right 0 (a * |p.1| - b * |p.2|)
  have := le_max_left 0 (a * |p.2| - b * |p.1|)
  linarith

private theorem gauge_ge_sum (a b : ℤ) (p : ℤ × ℤ) : b * (|p.1| + |p.2|) ≤ gauge a b p := by
  unfold gauge
  have := le_max_left 0 (a * |p.1| - b * |p.2|)
  have := le_max_left 0 (a * |p.2| - b * |p.1|)
  linarith

private theorem exists_path_canonical {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hc : Nat.Coprime a b) (ho : Odd (a + b)) {x y : ℤ} (hy : 0 ≤ y) (hyx : y ≤ x) :
    ∃ n : ℕ, (x, y) ∈ n • knightMoves (a : ℤ) (b : ℤ) ∧
      (b : ℤ) * (a + b) * n ≤ gauge a b (x, y) + 13 * b * b * (a + b) := by
  have hx : 0 ≤ x := hy.trans hyx
  have hab0 : (0 : ℤ) ≤ a + b := by positivity
  by_cases h : (b : ℤ) * y ≤ a * x
  · obtain ⟨n, hn, hbound⟩ := exists_path_flat ha hab hc ho hy h
    refine ⟨n, hn, ?_⟩
    have hg := gauge_ge_left (a : ℤ) b (x, y)
    simp only [abs_of_nonneg hx] at hg
    have := mul_le_mul_of_nonneg_left hbound hab0
    nlinarith
  · push Not at h
    obtain ⟨n, hn, hbound⟩ := exists_path_steep ha hab hc ho hyx h
    refine ⟨n, hn, ?_⟩
    have hg := gauge_ge_sum (a : ℤ) b (x, y)
    simp only [abs_of_nonneg hx, abs_of_nonneg hy] at hg
    have := mul_le_mul_of_nonneg_left hbound (by positivity : (0 : ℤ) ≤ b)
    nlinarith

/-- Upper bound: every lattice point is a sum of at most `gauge / (b (a + b)) + 13 b` moves. -/
private theorem exists_path {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hc : Nat.Coprime a b) (ho : Odd (a + b)) (p : ℤ × ℤ) :
    ∃ n : ℕ, p ∈ n • knightMoves (a : ℤ) (b : ℤ) ∧
      (b : ℤ) * (a + b) * n ≤ gauge a b p + 13 * b * b * (a + b) := by
  have habs : ∃ n : ℕ, (|p.1|, |p.2|) ∈ n • knightMoves (a : ℤ) (b : ℤ) ∧
      (b : ℤ) * (a + b) * n ≤ gauge a b p + 13 * b * b * (a + b) := by
    rcases le_total |p.2| |p.1| with h | h
    · obtain ⟨n, hn, hb⟩ := exists_path_canonical ha hab hc ho (abs_nonneg _) h
      refine ⟨n, hn, ?_⟩
      have e : gauge a b (|p.1|, |p.2|) = gauge a b p := by simp [gauge]
      rwa [e] at hb
    · obtain ⟨n, hn, hb⟩ := exists_path_canonical ha hab hc ho (abs_nonneg _) h
      refine ⟨n, swap_mem_nsmul hn, ?_⟩
      have e : gauge a b (|p.2|, |p.1|) = gauge a b p := by simp only [gauge, abs_abs]; ring
      rwa [e] at hb
  obtain ⟨n, hn, hb⟩ := habs
  refine ⟨n, ?_, hb⟩
  have h1 : (p.1, |p.2|) ∈ n • knightMoves (a : ℤ) (b : ℤ) := by
    rcases abs_choice p.1 with h | h
    · rwa [h] at hn
    · have := negFst_mem_nsmul hn
      simpa only [h, neg_neg] using this
  rcases abs_choice p.2 with h | h
  · rw [h] at h1
    exact h1
  · have := negSnd_mem_nsmul h1
    simpa only [h, neg_neg] using this

/-- The knight distance is within `13 b` of `gauge / (b (a + b))`. -/
private theorem distance_bounds {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hc : Nat.Coprime a b) (ho : Odd (a + b)) (p : ℤ × ℤ) :
    gauge a b p ≤ (b : ℤ) * (a + b) * (pieceDistance (knightMoves (a : ℤ) (b : ℤ)) p : ℤ) ∧
      (b : ℤ) * (a + b) * (pieceDistance (knightMoves (a : ℤ) (b : ℤ)) p : ℤ) ≤
        gauge a b p + 13 * b * b * (a + b) := by
  by_cases hp : p = 0
  · subst hp
    simp only [pieceDistance, ↓reduceIte, gauge]
    constructor
    · simp
    · simp only [Prod.fst_zero, Prod.snd_zero, abs_zero, mul_zero, sub_self, max_self,
        add_zero, CharP.cast_eq_zero, zero_add]
      positivity
  obtain ⟨n, hn, hbound⟩ := exists_path ha hab hc ho p
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      rw [zero_nsmul, Finset.mem_zero] at hn
      exact absurd hn hp
    · exact h0
  have hS : ({h : ℕ | 1 ≤ h ∧ p ∈ h • knightMoves (a : ℤ) (b : ℤ)} : Set ℕ).Nonempty :=
    ⟨n, hn1, hn⟩
  have hd : pieceDistance (knightMoves (a : ℤ) (b : ℤ)) p =
      sInf {h : ℕ | 1 ≤ h ∧ p ∈ h • knightMoves (a : ℤ) (b : ℤ)} := by
    simp [pieceDistance, hp]
  have hmem := (Nat.sInf_mem hS).2
  have hle : pieceDistance (knightMoves (a : ℤ) (b : ℤ)) p ≤ n := by
    rw [hd]
    exact Nat.sInf_le ⟨hn1, hn⟩
  rw [← hd] at hmem
  refine ⟨gauge_le_of_mem (by positivity) (by exact_mod_cast hab.le) hmem, ?_⟩
  have : ((pieceDistance (knightMoves (a : ℤ) (b : ℤ)) p : ℕ) : ℤ) ≤ n := by exact_mod_cast hle
  have hpos : (0 : ℤ) ≤ (b : ℤ) * (a + b) := by positivity
  nlinarith

/-! ### Lattice sums over the max-norm ball -/

private theorem sum_Icc_succ (f : ℤ → ℝ) (h : ℕ) :
    ∑ x ∈ Finset.Icc (-((h + 1 : ℕ) : ℤ)) ((h + 1 : ℕ) : ℤ), f x =
      f (-((h : ℤ) + 1)) + f ((h : ℤ) + 1) + ∑ x ∈ Finset.Icc (-(h : ℤ)) h, f x := by
  have hset : Finset.Icc (-((h + 1 : ℕ) : ℤ)) ((h + 1 : ℕ) : ℤ) =
      insert (-((h : ℤ) + 1)) (insert ((h : ℤ) + 1) (Finset.Icc (-(h : ℤ)) h)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    push_cast
    omega
  rw [hset, Finset.sum_insert, Finset.sum_insert, add_assoc]
  · simp only [Finset.mem_Icc]
    omega
  · simp only [Finset.mem_insert, Finset.mem_Icc]
    omega

private theorem card_Icc_neg (h : ℕ) : (Finset.Icc (-(h : ℤ)) h).card = 2 * h + 1 := by
  rw [Int.card_Icc]
  omega

private theorem sum_Icc_abs (h : ℕ) :
    ∑ x ∈ Finset.Icc (-(h : ℤ)) h, |(x : ℝ)| = h * (h + 1) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [sum_Icc_succ, ih]
    push_cast
    rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ h + 1)]
    ring

private theorem sum_Icc_sq (h : ℕ) :
    ∑ x ∈ Finset.Icc (-(h : ℤ)) h, (x : ℝ) ^ 2 = h * (h + 1) * (2 * h + 1) / 3 := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [sum_Icc_succ, ih]
    push_cast
    ring

private theorem sum_Icc_telescope (g : ℤ → ℝ) (h : ℕ) :
    ∑ y ∈ Finset.Icc (-(h : ℤ)) h, (g (y + 1) - g y) = g (h + 1) - g (-h) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [sum_Icc_succ, ih]
    have e : -((h : ℤ) + 1) + 1 = -(h : ℤ) := by ring
    rw [e]
    push_cast
    ring

private theorem step_sq (v b : ℝ) (hb : 0 ≤ b) :
    0 ≤ max 0 (v + b) ^ 2 - max 0 v ^ 2 - 2 * b * max 0 v ∧
      max 0 (v + b) ^ 2 - max 0 v ^ 2 - 2 * b * max 0 v ≤ b ^ 2 := by
  rcases le_total 0 v with hv | hv
  · rw [max_eq_right hv, max_eq_right (by linarith : (0 : ℝ) ≤ v + b)]
    constructor <;> nlinarith
  · rw [max_eq_left hv]
    rcases le_total 0 (v + b) with hvb | hvb
    · rw [max_eq_right hvb]
      constructor <;> nlinarith
    · rw [max_eq_left hvb]
      constructor <;> nlinarith

private theorem tent_eq (b c y : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    max 0 (c - b * |y|) = max 0 (c + b * y) - 2 * max 0 (b * y) + max 0 (b * y - c) := by
  rcases le_total 0 y with hy | hy
  · have hby : 0 ≤ b * y := mul_nonneg hb hy
    rw [abs_of_nonneg hy, max_eq_right (by linarith : (0 : ℝ) ≤ c + b * y), max_eq_right hby]
    rcases le_total (b * y) c with h | h
    · rw [max_eq_right (by linarith : (0 : ℝ) ≤ c - b * y),
        max_eq_left (by linarith : b * y - c ≤ 0)]
      ring
    · rw [max_eq_left (by linarith : c - b * y ≤ 0),
        max_eq_right (by linarith : (0 : ℝ) ≤ b * y - c)]
      ring
  · have hby : b * y ≤ 0 := by nlinarith
    rw [abs_of_nonpos hy, max_eq_left hby, max_eq_left (by linarith : b * y - c ≤ 0),
      show c - b * -y = c + b * y by ring]
    ring

/-- A tent of height `c` and slopes `± b` has lattice sum `c ^ 2 / b` up to `(2h + 1) b`. -/
private theorem tent_sum (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : ℕ) (hch : c ≤ b * h) :
    |b * ∑ y ∈ Finset.Icc (-(h : ℤ)) h, max 0 (c - b * |(y : ℝ)|) - c ^ 2| ≤
      (2 * h + 1) * b ^ 2 := by
  let Φ : ℤ → ℝ := fun y => max 0 (c + b * y) ^ 2 - 2 * max 0 (b * y) ^ 2 +
    max 0 (b * y - c) ^ 2
  have hstep : ∀ y : ℤ,
      |(Φ (y + 1) - Φ y) - 2 * b * max 0 (c - b * |(y : ℝ)|)| ≤ 2 * b ^ 2 := by
    intro y
    have e1 := step_sq (c + b * y) b hb
    have e2 := step_sq (b * y) b hb
    have e3 := step_sq (b * y - c) b hb
    rw [tent_eq b c y hb hc]
    simp only [Φ]
    push_cast
    rw [show c + b * ((y : ℝ) + 1) = c + b * y + b by ring,
      show b * ((y : ℝ) + 1) = b * y + b by ring,
      show b * (y : ℝ) + b - c = b * y - c + b by ring, abs_le]
    constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]
  have htop : Φ (h + 1) = 2 * c ^ 2 := by
    simp only [Φ]
    push_cast
    have hh : (0 : ℝ) ≤ h := by positivity
    rw [max_eq_right (by nlinarith : (0 : ℝ) ≤ c + b * (h + 1)),
      max_eq_right (by nlinarith : (0 : ℝ) ≤ b * (h + 1)),
      max_eq_right (by nlinarith : (0 : ℝ) ≤ b * (h + 1) - c)]
    ring
  have hbot : Φ (-h) = 0 := by
    simp only [Φ]
    push_cast
    have hh : (0 : ℝ) ≤ h := by positivity
    rw [max_eq_left (by nlinarith : c + b * -(h : ℝ) ≤ 0),
      max_eq_left (by nlinarith : b * -(h : ℝ) ≤ 0),
      max_eq_left (by nlinarith : b * -(h : ℝ) - c ≤ 0)]
    ring
  have hsum : |∑ y ∈ Finset.Icc (-(h : ℤ)) h,
      ((Φ (y + 1) - Φ y) - 2 * b * max 0 (c - b * |(y : ℝ)|))| ≤ (2 * h + 1) * (2 * b ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun y _ => hstep y).trans ?_
    rw [Finset.sum_const, card_Icc_neg, nsmul_eq_mul]
    push_cast
    exact le_rfl
  rw [Finset.sum_sub_distrib, sum_Icc_telescope Φ h, htop, hbot, ← Finset.mul_sum] at hsum
  rw [abs_le] at hsum ⊢
  constructor <;> linarith [hsum.1, hsum.2]

/-- The real gauge summed over the max-norm ball is `h (h + 1) (2h + 1) (2b² + 2a²/3) / b`
up to an error of order `h ^ 2`. -/
private theorem gauge_sum (A B : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B) (h : ℕ) :
    |B * ∑ p ∈ maxNormBall h, (B * |(p.1 : ℝ)| + B * |(p.2 : ℝ)| +
        max 0 (A * |(p.1 : ℝ)| - B * |(p.2 : ℝ)|) + max 0 (A * |(p.2 : ℝ)| - B * |(p.1 : ℝ)|)) -
      h * (h + 1) * (2 * h + 1) * (2 * B ^ 2 + 2 * A ^ 2 / 3)| ≤
      2 * (2 * h + 1) ^ 2 * B ^ 2 := by
  have hB : 0 ≤ B := hA.trans hAB
  have hcard : ((Finset.Icc (-(h : ℤ)) h).card : ℝ) = 2 * h + 1 := by
    rw [card_Icc_neg]
    push_cast
    ring
  have hsplit : ∑ p ∈ maxNormBall h, (B * |(p.1 : ℝ)| + B * |(p.2 : ℝ)| +
        max 0 (A * |(p.1 : ℝ)| - B * |(p.2 : ℝ)|) + max 0 (A * |(p.2 : ℝ)| - B * |(p.1 : ℝ)|)) =
      2 * (2 * h + 1) * (B * (h * (h + 1))) +
        2 * ∑ x ∈ Finset.Icc (-(h : ℤ)) h, ∑ y ∈ Finset.Icc (-(h : ℤ)) h,
          max 0 (A * |(x : ℝ)| - B * |(y : ℝ)|) := by
    rw [maxNormBall, Finset.sum_product]
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun x y : ℤ => max 0 (A * |(y : ℝ)| - B * |(x : ℝ)|))]
    simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, sum_Icc_abs, hcard]
    ring
  have hQ : |B * ∑ x ∈ Finset.Icc (-(h : ℤ)) h, ∑ y ∈ Finset.Icc (-(h : ℤ)) h,
          max 0 (A * |(x : ℝ)| - B * |(y : ℝ)|) - A ^ 2 * (h * (h + 1) * (2 * h + 1) / 3)| ≤
      (2 * h + 1) ^ 2 * B ^ 2 := by
    rw [← sum_Icc_sq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ x ∈ Finset.Icc (-(h : ℤ)) h,
          |B * ∑ y ∈ Finset.Icc (-(h : ℤ)) h, max 0 (A * |(x : ℝ)| - B * |(y : ℝ)|) -
            A ^ 2 * (x : ℝ) ^ 2|
        ≤ ∑ x ∈ Finset.Icc (-(h : ℤ)) h, (2 * h + 1) * B ^ 2 := by
          apply Finset.sum_le_sum
          intro x hx
          have hxh : |(x : ℝ)| ≤ h := by
            have h' : |x| ≤ (h : ℤ) := abs_le.2 (Finset.mem_Icc.1 hx)
            exact_mod_cast h'
          have h1 := mul_le_mul_of_nonneg_left hxh hA
          have h2 := mul_le_mul_of_nonneg_right hAB (by positivity : (0 : ℝ) ≤ h)
          have := tent_sum B (A * |(x : ℝ)|) hB (by positivity) h (by linarith)
          rwa [mul_pow, sq_abs] at this
      _ = (2 * h + 1) ^ 2 * B ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
          ring
  rw [hsplit]
  rw [abs_le] at hQ ⊢
  constructor <;> nlinarith [hQ.1, hQ.2]

/-- If `E D(h)` is `h (h + 1) (2h + 1) M` up to `C (2h + 1) ^ 2`, then
`(2h / 3) (D(h) / (2h + 1) ^ 2)⁻¹` tends to `(4 / 3) E / M`. -/
private theorem tendsto_of_estimate (D : ℕ → ℝ) {E M C : ℝ} (hE : 0 < E) (hM : 0 < M)
    (hest : ∀ h : ℕ, |E * D h - h * (h + 1) * (2 * h + 1) * M| ≤ C * (2 * h + 1) ^ 2) :
    Filter.Tendsto (fun h : ℕ => (2 * (h : ℝ) / 3) * ((D h / (2 * (h : ℝ) + 1) ^ 2)⁻¹))
      Filter.atTop (nhds (4 / 3 * E / M)) := by
  have hε : Filter.Tendsto (fun h : ℕ => ((h : ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hlim1 : Filter.Tendsto (fun h : ℕ => M / E * ((1 + (h : ℝ)⁻¹) * (2 + (h : ℝ)⁻¹)))
      Filter.atTop (nhds (M / E * ((1 + 0) * (2 + 0)))) :=
    tendsto_const_nhds.mul ((tendsto_const_nhds.add hε).mul (tendsto_const_nhds.add hε))
  have hlim2 : Filter.Tendsto (fun h : ℕ => C / E * ((2 + (h : ℝ)⁻¹) ^ 2 * (h : ℝ)⁻¹))
      Filter.atTop (nhds (C / E * ((2 + 0) ^ 2 * 0))) :=
    tendsto_const_nhds.mul (((tendsto_const_nhds.add hε).pow 2).mul hε)
  rw [show M / E * ((1 + 0) * (2 + 0)) = 2 * M / E by ring] at hlim1
  rw [show C / E * ((2 + 0) ^ 2 * 0) = (0 : ℝ) by ring] at hlim2
  have hD : Filter.Tendsto (fun h : ℕ => D h / (h : ℝ) ^ 3) Filter.atTop
      (nhds (2 * M / E)) := by
    refine hlim1.congr_dist ?_
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_ hlim2
    filter_upwards [Filter.eventually_ge_atTop 1] with h hh
    have hpos : (0 : ℝ) < h := by exact_mod_cast hh
    rw [Real.dist_eq]
    have e : M / E * ((1 + (h : ℝ)⁻¹) * (2 + (h : ℝ)⁻¹)) - D h / (h : ℝ) ^ 3 =
        -(E * D h - h * (h + 1) * (2 * h + 1) * M) / (E * (h : ℝ) ^ 3) := by
      field_simp
      ring
    rw [e, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < E * (h : ℝ) ^ 3),
      div_le_iff₀ (by positivity)]
    calc |E * D h - h * (h + 1) * (2 * h + 1) * M| ≤ C * (2 * h + 1) ^ 2 := hest h
      _ = C / E * ((2 + (h : ℝ)⁻¹) ^ 2 * (h : ℝ)⁻¹) * (E * (h : ℝ) ^ 3) := by
        field_simp
  have hnum : Filter.Tendsto (fun h : ℕ => 2 / 3 * (2 + (h : ℝ)⁻¹) ^ 2) Filter.atTop
      (nhds (2 / 3 * (2 + 0) ^ 2)) :=
    tendsto_const_nhds.mul ((tendsto_const_nhds.add hε).pow 2)
  have hlim := hnum.div hD (by positivity)
  rw [show (2 : ℝ) / 3 * (2 + 0) ^ 2 / (2 * M / E) = 4 / 3 * E / M by
    field_simp
    ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with h hh
  have hpos : (0 : ℝ) < h := by exact_mod_cast hh
  rw [Pi.div_apply, div_div_eq_mul_div, inv_div, ← mul_div_assoc]
  congr 1
  field_simp

end KnightVelocity

/--
**Velocity formula for the (a, b)-knight.** Let $a$ and $b$ be natural numbers with
$1 \le a < b$, $\gcd(a, b) = 1$ and $a + b$ odd, let
$N_{a,b} = \{(\pm a, \pm b), (\pm b, \pm a)\}$ be the $(a,b)$-knight's move set, and for
$p \in \mathbb{Z}^2$ let $d_{a,b}(p)$ be the piece distance of $p$ for $N_{a,b}$. For a natural
number $h$, let $B_h = \{(x, y) \in \mathbb{Z}^2 : \max(|x|, |y|) \le h\}$ be the max-norm
ball and let $\bar{d}(h) = |B_h|^{-1} \sum_{p \in B_h} d_{a,b}(p)$ be the average of $d_{a,b}$
over $B_h$. Then
$$\lim_{h \to \infty} \frac{2h}{3} \, \bar{d}(h)^{-1} = \frac{2(a+b)b^2}{a^2 + 3b^2}.$$

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), Theorem 1.3.
-/
public theorem knight_velocity_formula (a b : ℕ)
    (ha : 1 ≤ a) (hab : a < b) (hcoprime : Nat.Coprime a b)
    (hodd : Odd (a + b)) :
    Filter.Tendsto
      (fun h : ℕ =>
        (2 * (h : ℝ) / 3) *
          (((∑ p ∈ maxNormBall h,
              (pieceDistance (knightMoves (a : ℤ) (b : ℤ)) p : ℝ)) /
            ((maxNormBall h).card : ℝ))⁻¹))
      Filter.atTop
      (nhds
        (2 * ((a : ℝ) + (b : ℝ)) * (b : ℝ) ^ 2 /
          ((a : ℝ) ^ 2 + 3 * (b : ℝ) ^ 2))) := by
  have hA : (0 : ℝ) < a := by exact_mod_cast ha
  have hAB : (a : ℝ) < b := by exact_mod_cast hab
  have hB : (0 : ℝ) < b := hA.trans hAB
  have hpt : ∀ p : ℤ × ℤ,
      (b : ℝ) * |(p.1 : ℝ)| + b * |(p.2 : ℝ)| + max 0 (a * |(p.1 : ℝ)| - b * |(p.2 : ℝ)|) +
          max 0 (a * |(p.2 : ℝ)| - b * |(p.1 : ℝ)|) ≤
        b * (a + b) * (pieceDistance (knightMoves (a : ℤ) (b : ℤ)) p : ℝ) ∧
      (b : ℝ) * (a + b) * (pieceDistance (knightMoves (a : ℤ) (b : ℤ)) p : ℝ) ≤
        b * |(p.1 : ℝ)| + b * |(p.2 : ℝ)| + max 0 (a * |(p.1 : ℝ)| - b * |(p.2 : ℝ)|) +
          max 0 (a * |(p.2 : ℝ)| - b * |(p.1 : ℝ)|) + 13 * b * b * (a + b) := by
    intro p
    obtain ⟨h1, h2⟩ := KnightVelocity.distance_bounds ha hab hcoprime hodd p
    have h1' := (Int.cast_le (R := ℝ)).2 h1
    have h2' := (Int.cast_le (R := ℝ)).2 h2
    push_cast [KnightVelocity.gauge] at h1' h2'
    exact ⟨h1', h2'⟩
  have hest : ∀ h : ℕ, |(b : ℝ) ^ 2 * (a + b) * (∑ p ∈ maxNormBall h,
        (pieceDistance (knightMoves (a : ℤ) (b : ℤ)) p : ℝ)) -
      h * (h + 1) * (2 * h + 1) * (2 * (b : ℝ) ^ 2 + 2 * (a : ℝ) ^ 2 / 3)| ≤
      (13 * (b : ℝ) * b * b * (a + b) + 2 * b ^ 2) * (2 * h + 1) ^ 2 := by
    intro h
    have hG := KnightVelocity.gauge_sum (a : ℝ) b hA.le hAB.le h
    have hcardR : ((maxNormBall h).card : ℝ) = (2 * h + 1) ^ 2 := by
      rw [card_maxNormBall]
      push_cast
      ring
    have hlow := Finset.sum_le_sum fun p (_ : p ∈ maxNormBall h) => (hpt p).1
    have hupp := Finset.sum_le_sum fun p (_ : p ∈ maxNormBall h) => (hpt p).2
    rw [← Finset.mul_sum] at hlow hupp
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcardR] at hupp
    have hlow' := mul_le_mul_of_nonneg_left hlow hB.le
    have hupp' := mul_le_mul_of_nonneg_left hupp hB.le
    rw [abs_le] at hG ⊢
    constructor <;> nlinarith [hG.1, hG.2, hlow', hupp']
  have hlim := KnightVelocity.tendsto_of_estimate _ (by positivity) (by positivity) hest
  have hval : 4 / 3 * ((b : ℝ) ^ 2 * (a + b)) / (2 * (b : ℝ) ^ 2 + 2 * (a : ℝ) ^ 2 / 3) =
      2 * ((a : ℝ) + b) * b ^ 2 / (a ^ 2 + 3 * b ^ 2) := by
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' (Filter.Eventually.of_forall fun h => ?_)
  simp only [card_maxNormBall]
  push_cast
  ring

end MetaMathlibExt
