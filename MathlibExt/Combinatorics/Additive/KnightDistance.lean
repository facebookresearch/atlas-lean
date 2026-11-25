/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Distance for generalized knights

A pair of knight moves travels along a coordinate axis. Bounded Bézout
coefficients then give short paths for points with even coordinates. At most
two additional moves correct the parities of an arbitrary point in the box.

For the asymptotics, round the coefficients of the two adjacent moves in
each sector and use the box bound to correct the residual. The maximum
horizontal and diagonal advances of a single move give the lower bounds.
-/

namespace MetaMathlibExt

open Pointwise

@[expose] public section

/--
**Knight moves.** For integers $a$ and $b$, the $(a,b)$-knight's move set is
$$N_{a,b} = \{(\pm a, \pm b), (\pm b, \pm a)\} \subset \mathbb{Z}^2,$$
the finite set of the points $(a, b)$, $(-a, b)$, $(a, -b)$, $(-a, -b)$, $(b, a)$, $(-b, a)$,
$(b, -a)$ and $(-b, -a)$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definition of `N_{a,b}`.
-/
public def knightMoves (a b : ℤ) : Finset (ℤ × ℤ) :=
  {(b, a), (a, b), (-a, b), (-b, a), (-b, -a), (-a, -b), (a, -b), (b, -a)}

/--
**Piece distance on the integer lattice.** Let $A \subseteq \mathbb{Z}^2$ be a finite set of
moves and, for $h \ge 1$, let $hA = \{a_1 + \dots + a_h : a_1, \dots, a_h \in A\}$ be its
$h$-fold sumset. The piece distance of a point $p \in \mathbb{Z}^2$ for $A$ is the natural
number that is $0$ if $p = (0,0)$ and otherwise the infimum of the set of integers $h \ge 1$
with $p \in hA$, where the infimum of the empty set is taken to be $0$.

Points other than the origin that are not a sum of moves from $A$ therefore have distance $0$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), definition of `A(x,y)`.
-/
public noncomputable def pieceDistance (A : Finset (ℤ × ℤ)) (p : ℤ × ℤ) : ℕ :=
  if p = 0 then 0 else sInf {h : ℕ | 1 ≤ h ∧ p ∈ h • A}

private theorem distance_le_of_mem {A : Finset (ℤ × ℤ)} {p : ℤ × ℤ} {n : ℕ}
    (hp : p ∈ n • A) : pieceDistance A p ≤ n := by
  by_cases hzero : p = 0
  · simp [pieceDistance, hzero]
  · have hn : 1 ≤ n := by
      cases n with
      | zero => exact (hzero (by simpa using hp)).elim
      | succ n => exact Nat.succ_le_succ (Nat.zero_le n)
    rw [pieceDistance, ite_eq_right hzero]
    exact Nat.sInf_le ⟨hn, hp⟩

private theorem mem_fold_add {A : Finset (ℤ × ℤ)} {p q : ℤ × ℤ} {m n : ℕ}
    (hp : p ∈ m • A) (hq : q ∈ n • A) : p + q ∈ (m + n) • A := by
  rw [add_nsmul]
  exact Finset.add_mem_add hp hq

private theorem mem_twofold {A : Finset (ℤ × ℤ)} {p q : ℤ × ℤ}
    (hp : p ∈ A) (hq : q ∈ A) : p + q ∈ 2 • A := by
  rw [two_nsmul]
  exact Finset.add_mem_add hp hq

private theorem mem_fold_zsmul {A : Finset (ℤ × ℤ)} {p : ℤ × ℤ}
    (hp : p ∈ (2 : ℕ) • A) (hn : -p ∈ (2 : ℕ) • A) (k : ℤ) :
    k • p ∈ (2 * k.natAbs) • A := by
  by_cases hk : 0 ≤ k
  · have hpoint : k.natAbs • p = k • p := by
      rw [← natCast_zsmul, Int.natCast_natAbs, abs_of_nonneg hk]
    simpa only [hpoint, smul_smul, Nat.mul_comm k.natAbs 2] using
      (Finset.nsmul_mem_nsmul (n := k.natAbs) hp)
  · have hpoint : k.natAbs • (-p) = k • p := by
      rw [← natCast_zsmul, Int.ofNat_natAbs_of_nonpos (le_of_not_ge hk),
        neg_zsmul, zsmul_neg, neg_neg]
    simpa only [hpoint, smul_smul, Nat.mul_comm k.natAbs 2] using
      (Finset.nsmul_mem_nsmul (n := k.natAbs) hn)

private theorem knight_neg_mem {a b : ℤ} {p : ℤ × ℤ}
    (hp : p ∈ knightMoves a b) : -p ∈ knightMoves a b := by
  simp only [knightMoves, Finset.mem_insert, Finset.mem_singleton] at hp ⊢
  rcases hp with h | h | h | h | h | h | h | h <;>
    rw [h, Prod.neg_mk] <;> simp only [neg_neg, eq_self, true_or, or_true]

private theorem knight_neg_mem_twofold {a b : ℤ} {p : ℤ × ℤ}
    (hp : p ∈ (2 : ℕ) • knightMoves a b) : -p ∈ (2 : ℕ) • knightMoves a b := by
  rw [two_nsmul, Finset.mem_add] at hp ⊢
  obtain ⟨u, hu, v, hv, rfl⟩ := hp
  exact ⟨-u, knight_neg_mem hu, -v, knight_neg_mem hv, (neg_add u v).symm⟩

private theorem horizontal_mem_twofold (a b : ℤ) :
    (2 * a, 0) ∈ (2 : ℕ) • knightMoves a b := by
  have h₁ : (a, b) ∈ knightMoves a b := by simp [knightMoves]
  have h₂ : (a, -b) ∈ knightMoves a b := by simp [knightMoves]
  have heq : (a, b) + (a, -b) = (2 * a, 0) := by
    simp [Prod.add_def, two_mul]
  exact heq ▸ mem_twofold h₁ h₂

private theorem vertical_mem_twofold (a b : ℤ) :
    (0, 2 * a) ∈ (2 : ℕ) • knightMoves a b := by
  have h₁ : (b, a) ∈ knightMoves a b := by simp [knightMoves]
  have h₂ : (-b, a) ∈ knightMoves a b := by simp [knightMoves]
  have heq : (b, a) + (-b, a) = (0, 2 * a) := by
    simp [Prod.add_def, two_mul]
  exact heq ▸ mem_twofold h₁ h₂

-- The explicit move list is only unfolded for membership and symmetry.
attribute [local irreducible] knightMoves

private theorem knight_mem_fold_zsmul {a b : ℤ} {p : ℤ × ℤ}
    (hp : p ∈ (2 : ℕ) • knightMoves a b) (k : ℤ) :
    k • p ∈ (2 * k.natAbs) • knightMoves a b :=
  @mem_fold_zsmul (knightMoves a b) p hp (@knight_neg_mem_twofold a b p hp) k

private theorem horizontal_mem_fold (a b k : ℤ) :
    k • (2 * a, (0 : ℤ)) ∈ (2 * k.natAbs) • knightMoves a b :=
  @knight_mem_fold_zsmul a b (2 * a, 0) (horizontal_mem_twofold a b) k

private theorem knightMoves_comm (a b : ℤ) :
    knightMoves a b = knightMoves b a := by
  ext p
  simp only [knightMoves, Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem vertical_mem_fold (a b k : ℤ) :
    k • ((0 : ℤ), 2 * a) ∈ (2 * k.natAbs) • knightMoves a b :=
  @knight_mem_fold_zsmul a b (0, 2 * a) (vertical_mem_twofold a b) k

/-- Reduce one Bézout coefficient modulo `b` to bound both coefficients. -/
private theorem exists_bounded_coefficients {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hc : Nat.Coprime a b) {t : ℤ} (ht : |t| ≤ (a : ℤ) + b) :
    ∃ u v : ℤ, (a : ℤ) * u + b * v = t ∧ u.natAbs + v.natAbs ≤ 3 * b := by
  have hb : (0 : ℤ) < b := by omega
  have hbez := Nat.gcd_eq_gcd_ab a b
  rw [hc.gcd_eq_one, Nat.cast_one] at hbez
  let w := t * a.gcdA b
  let u := w % (b : ℤ)
  let v := t * a.gcdB b + (w / (b : ℤ)) * a
  have hw : u + (b : ℤ) * (w / (b : ℤ)) = w := Int.emod_add_mul_ediv w b
  have huv : (a : ℤ) * u + b * v = t := by
    dsimp [v]
    linear_combination (a : ℤ) * hw - t * hbez
  have hu0 : 0 ≤ u := Int.emod_nonneg _ (ne_of_gt hb)
  have huB : u < b := Int.emod_lt_of_pos _ hb
  have hua : 0 ≤ (a : ℤ) * u := mul_nonneg (by omega) hu0
  have huab : (a : ℤ) * u ≤ a * b :=
    mul_le_mul_of_nonneg_left (le_of_lt huB) (by omega)
  obtain ⟨ht₁, ht₂⟩ := abs_le.mp ht
  have hv_hi : v ≤ 2 := Int.le_of_mul_le_mul_left (by linarith) hb
  have hv_lo : -(a : ℤ) - 2 ≤ v := Int.le_of_mul_le_mul_left (by linarith) hb
  have hu_abs : u.natAbs ≤ b := by
    rw [← Int.ofNat_le, Int.natCast_natAbs, abs_of_nonneg hu0]
    omega
  have hv_abs : v.natAbs ≤ 2 * b := by
    rw [← Int.ofNat_le, Int.natCast_natAbs, abs_le]
    push_cast
    omega
  exact ⟨u, v, huv, by omega⟩

private theorem parity_step {A : Finset (ℤ × ℤ)} (t : ℤ) {p : ℤ × ℤ}
    (hp : p ∈ A) :
    (if t % 2 = 0 then 0 else p) ∈ (if t % 2 = 0 then 0 else 1 : ℕ) • A := by
  by_cases ht : t % 2 = 0 <;> simp [ht, hp]

/-- Correct the two coordinate parities with at most two moves. -/
private theorem exists_parity_correction {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpar : (a + b) % 2 = 1) (p : ℤ × ℤ) :
    ∃ (q : ℤ × ℤ) (n : ℕ), q ∈ n • knightMoves a b ∧ n ≤ 2 ∧
      0 ≤ q.1 ∧ q.1 ≤ a + b ∧ 0 ≤ q.2 ∧ q.2 ≤ a + b ∧
      (p.1 - q.1) % 2 = 0 ∧ (p.2 - q.2) % 2 = 0 := by
  let xStep : ℤ × ℤ := if a % 2 = 0 then (b, a) else (a, b)
  let yStep : ℤ × ℤ := if a % 2 = 0 then (a, b) else (b, a)
  have hx : xStep ∈ knightMoves a b := by
    by_cases h : a % 2 = 0 <;> simp [xStep, h, knightMoves]
  have hy : yStep ∈ knightMoves a b := by
    by_cases h : a % 2 = 0 <;> simp [yStep, h, knightMoves]
  refine ⟨_, _, mem_fold_add (parity_step p.1 hx) (parity_step p.2 hy), ?_⟩
  by_cases hx0 : p.1 % 2 = 0 <;> by_cases hy0 : p.2 % 2 = 0 <;>
    by_cases ha0 : a % 2 = 0 <;>
    simp [hx0, hy0, ha0, xStep, yStep, Prod.add_def] <;> omega

/--
**Bounded reachability for generalized knights.** Let $a$ and $b$ be natural numbers with
$1 \le a < b$, $\gcd(a,b)=1$, and $a+b$ odd. Every integer point $(x,y)$ with
$\max(|x|,|y|) \le a+b$ is a sum of at most $13b$ moves from the $(a,b)$-knight's move set.
A sum of zero moves is the origin.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), Lemma 2.1.
-/
public theorem exists_knight_path_on_box {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    (hc : Nat.Coprime a b) (ho : Odd (a + b)) {p : ℤ × ℤ}
    (hp : max |p.1| |p.2| ≤ ((a + b : ℕ) : ℤ)) :
    ∃ n : ℕ, n ≤ 13 * b ∧ p ∈ n • knightMoves (a : ℤ) (b : ℤ) := by
  have hpar : ((a : ℤ) + b) % 2 = 1 := by
    obtain ⟨k, hk⟩ := ho
    omega
  obtain ⟨q, n, hq, hn, hqx0, hqx, hqy0, hqy, hpx, hpy⟩ :=
    exists_parity_correction (a := (a : ℤ)) (b := (b : ℤ))
      (by omega) (by omega) hpar p
  let x := (p.1 - q.1) / 2
  let y := (p.2 - q.2) / 2
  have hx : |x| ≤ (a : ℤ) + b := by
    have h := abs_le.mp ((le_max_left |p.1| |p.2|).trans hp)
    rw [abs_le]
    dsimp [x]
    omega
  have hy : |y| ≤ (a : ℤ) + b := by
    have h := abs_le.mp ((le_max_right |p.1| |p.2|).trans hp)
    rw [abs_le]
    dsimp [y]
    omega
  obtain ⟨u, v, hxu, hxuv⟩ := exists_bounded_coefficients ha hab hc hx
  obtain ⟨s, t, hys, hyst⟩ := exists_bounded_coefficients ha hab hc hy
  have hxmem := mem_fold_add (horizontal_mem_fold (a : ℤ) b u)
    (by simpa only [knightMoves_comm (b : ℤ) (a : ℤ)] using
      horizontal_mem_fold (b : ℤ) a v)
  have hymem := mem_fold_add (vertical_mem_fold (a : ℤ) b s)
    (by simpa only [knightMoves_comm (b : ℤ) (a : ℤ)] using
      vertical_mem_fold (b : ℤ) a t)
  have hmem := mem_fold_add hq (mem_fold_add hxmem hymem)
  have heq : q + ((u • (2 * (a : ℤ), (0 : ℤ)) + v • (2 * (b : ℤ), (0 : ℤ))) +
      (s • ((0 : ℤ), 2 * (a : ℤ)) + t • ((0 : ℤ), 2 * (b : ℤ)))) = p := by
    apply Prod.ext
    · change q.1 + ((u • (2 * (a : ℤ)) + v • (2 * (b : ℤ))) +
        (s • (0 : ℤ) + t • (0 : ℤ))) = p.1
      simp only [zsmul_eq_mul, mul_zero, add_zero]
      have h : q.1 + 2 * x = p.1 := by dsimp [x]; omega
      linear_combination h + 2 * hxu
    · change q.2 + ((u • (0 : ℤ) + v • (0 : ℤ)) +
        (s • (2 * (a : ℤ)) + t • (2 * (b : ℤ)))) = p.2
      simp only [zsmul_eq_mul, mul_zero, add_zero, zero_add]
      have h : q.2 + 2 * y = p.2 := by dsimp [y]; omega
      linear_combination h + 2 * hys
  rw [heq] at hmem
  refine ⟨_, ?_, hmem⟩
  omega

/--
**Uniform bound for knight distance on a box.** There is an absolute constant $M \in \mathbb{R}$
such that for all natural numbers $a$ and $b$ with $1 \le a < b$, $\gcd(a, b) = 1$ and $a + b$
odd, every lattice point $(x, y) \in \mathbb{Z}^2$ with $\max(|x|, |y|) \le a + b$ has piece
distance at most $Mb$ for the $(a,b)$-knight's move set
$N_{a,b} = \{(\pm a, \pm b), (\pm b, \pm a)\}$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), Lemma 2.1.
-/
public theorem knight_distance_uniform_on_box :
    ∃ M : ℝ, ∀ a b : ℕ,
      1 ≤ a → a < b → Nat.Coprime a b → Odd (a + b) →
      ∀ p : ℤ × ℤ,
        max |p.1| |p.2| ≤ ((a + b : ℕ) : ℤ) →
        (pieceDistance (knightMoves (a : ℤ) (b : ℤ)) p : ℝ) ≤ M * b := by
  refine ⟨13, fun a b ha hab hc ho p hp => ?_⟩
  obtain ⟨n, hn, hmem⟩ := exists_knight_path_on_box ha hab hc ho hp
  have hbnd : pieceDistance (knightMoves (a : ℤ) b) p ≤ 13 * b :=
    (distance_le_of_mem hmem).trans hn
  exact_mod_cast hbnd

-- A path witness rules out the empty infimum in the definition of the distance.
private theorem mem_distance_fold {A : Finset (ℤ × ℤ)} {p : ℤ × ℤ} {n : ℕ}
    (hp : p ∈ n • A) : p ∈ pieceDistance A p • A := by
  by_cases hzero : p = 0
  · subst p
    simp [pieceDistance]
  · have hn : 1 ≤ n := by
      cases n with
      | zero => exact (hzero (by simpa using hp)).elim
      | succ n => exact Nat.succ_le_succ (Nat.zero_le n)
    have hs : ({h : ℕ | 1 ≤ h ∧ p ∈ h • A} : Set ℕ).Nonempty := ⟨n, hn, hp⟩
    rw [pieceDistance, ite_eq_right hzero]
    exact (Nat.sInf_mem hs).2

private theorem knight_move_bounds {a b : ℕ} (hab : a ≤ b) {u : ℤ × ℤ}
    (hu : u ∈ knightMoves (a : ℤ) (b : ℤ)) :
    |u.1| ≤ (b : ℤ) ∧ |u.2| ≤ (b : ℤ) ∧ u.1 + u.2 ≤ (a : ℤ) + (b : ℤ) := by
  simp only [knightMoves, Finset.mem_insert, Finset.mem_singleton] at hu
  have ha' : (0 : ℤ) ≤ a := Int.natCast_nonneg a
  have hb' : (0 : ℤ) ≤ b := Int.natCast_nonneg b
  have hab' : (a : ℤ) ≤ b := by exact_mod_cast hab
  rcases hu with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [abs_neg, abs_of_nonneg ha', abs_of_nonneg hb'] <;> omega

private theorem knight_fold_bounds {a b : ℕ} (hab : a ≤ b) {p : ℤ × ℤ} {n : ℕ}
    (hp : p ∈ n • knightMoves (a : ℤ) (b : ℤ)) :
    p.1 ≤ (n : ℤ) * (b : ℤ) ∧ p.1 + p.2 ≤ (n : ℤ) * ((a : ℤ) + (b : ℤ)) := by
  induction n generalizing p with
  | zero =>
    have hp0 : p = 0 := by simpa using hp
    subst p
    simp
  | succ n ih =>
    rw [succ_nsmul] at hp
    obtain ⟨q, hq, u, hu, rfl⟩ := Finset.mem_add.mp hp
    obtain ⟨hq₁, hq₂⟩ := ih hq
    obtain ⟨hu₁, _, hu₂⟩ := knight_move_bounds hab hu
    have hu' := (le_abs_self u.1).trans hu₁
    push_cast
    constructor
    · change q.1 + u.1 ≤ _
      nlinarith only [hq₁, hu']
    · change (q.1 + u.1) + (q.2 + u.2) ≤ _
      nlinarith only [hq₂, hu₂]

private theorem rounded_bounds {s : ℝ} (hs : 0 ≤ s) :
    (⌊s + 1 / 2⌋₊ : ℝ) ≤ s + 1 / 2 ∧ |s - (⌊s + 1 / 2⌋₊ : ℝ)| ≤ 1 / 2 := by
  have hs' : 0 ≤ s + 1 / 2 := by linarith
  refine ⟨Nat.floor_le hs', abs_le.mpr ⟨?_, ?_⟩⟩
  · linarith [Nat.floor_le hs']
  · linarith [Nat.lt_floor_add_one (s + 1 / 2)]

-- Rounding both coefficients costs at most one move and leaves each residual
-- coordinate at most b in absolute value.
private theorem rounded_knight_path {a b : ℕ} (hab : a ≤ b) {x y : ℤ} {u v : ℤ × ℤ}
    (hu : u ∈ knightMoves (a : ℤ) (b : ℤ))
    (hv : v ∈ knightMoves (a : ℤ) (b : ℤ)) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hx : (x : ℝ) = s * (u.1 : ℝ) + t * (v.1 : ℝ))
    (hy : (y : ℝ) = s * (u.2 : ℝ) + t * (v.2 : ℝ)) :
    ∃ (n : ℕ) (q : ℤ × ℤ), q ∈ n • knightMoves (a : ℤ) (b : ℤ) ∧
      (n : ℝ) ≤ s + t + 1 ∧
      max |((x, y) - q).1| |((x, y) - q).2| ≤ ((a + b : ℕ) : ℤ) := by
  let i := ⌊s + 1 / 2⌋₊
  let j := ⌊t + 1 / 2⌋₊
  have hi : (i : ℝ) ≤ s + 1 / 2 := (rounded_bounds hs).1
  have hj : (j : ℝ) ≤ t + 1 / 2 := (rounded_bounds ht).1
  have hcoord {z u' v' : ℤ} (hz : (z : ℝ) = s * (u' : ℝ) + t * (v' : ℝ))
      (hu' : |u'| ≤ (b : ℤ)) (hv' : |v'| ≤ (b : ℤ)) :
      |z - ((i : ℤ) * u' + (j : ℤ) * v')| ≤ ((a + b : ℕ) : ℤ) := by
    have h₁ : |(u' : ℝ)| ≤ (b : ℝ) := by exact_mod_cast hu'
    have h₂ : |(v' : ℝ)| ≤ (b : ℝ) := by exact_mod_cast hv'
    have heq : (z : ℝ) - ((i : ℝ) * (u' : ℝ) + (j : ℝ) * (v' : ℝ)) =
        (s - (i : ℝ)) * (u' : ℝ) + (t - (j : ℝ)) * (v' : ℝ) := by
      rw [hz]
      ring
    have hbound : |(z : ℝ) - ((i : ℝ) * (u' : ℝ) + (j : ℝ) * (v' : ℝ))| ≤
        (b : ℝ) := by
      rw [heq]
      calc
        _ ≤ |(s - (i : ℝ)) * (u' : ℝ)| + |(t - (j : ℝ)) * (v' : ℝ)| := abs_add_le _ _
        _ ≤ (1 / 2 : ℝ) * b + (1 / 2 : ℝ) * b := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul (rounded_bounds hs).2 h₁ (abs_nonneg _) (by norm_num))
            (mul_le_mul (rounded_bounds ht).2 h₂ (abs_nonneg _) (by norm_num))
        _ = _ := by ring
    exact (show |z - ((i : ℤ) * u' + (j : ℤ) * v')| ≤ (b : ℤ) by exact_mod_cast hbound).trans
      (by omega)
  refine ⟨i + j, i • u + j • v, ?_, ?_, max_le ?_ ?_⟩
  · exact mem_fold_add (Finset.nsmul_mem_nsmul hu) (Finset.nsmul_mem_nsmul hv)
  · push_cast
    linarith
  · simpa [nsmul_eq_mul] using hcoord hx (knight_move_bounds hab hu).1 (knight_move_bounds hab hv).1
  · simpa [nsmul_eq_mul] using
      hcoord hy (knight_move_bounds hab hu).2.1 (knight_move_bounds hab hv).2.1

/--
**Knight distance asymptotics.** There is an absolute constant $M \in \mathbb{R}$ with the
following property. Let $a$ and $b$ be natural numbers with $1 \le a < b$, $\gcd(a, b) = 1$ and
$a + b$ odd, let $N_{a,b} = \{(\pm a, \pm b), (\pm b, \pm a)\}$ be the $(a,b)$-knight's move set,
and for $p \in \mathbb{Z}^2$ let $d_{a,b}(p)$ be the piece distance of $p$ for $N_{a,b}$. Then
for all integers $x$ and $y$ with $0 \le y \le x$: if $by \le ax$, then
$|d_{a,b}(x, y) - x/b| \le Mb$; and if $ax < by$, then
$|d_{a,b}(x, y) - (x + y)/(a + b)| \le Mb$.

Source: Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly
62(3) (2024), Theorem 1.1.
-/
public theorem knight_distance_asymptotics :
    ∃ M : ℝ, ∀ (a b : ℕ) (x y : ℤ),
      1 ≤ a → a < b → Nat.Coprime a b → Odd (a + b) →
      0 ≤ y → y ≤ x →
      (((b : ℤ) * y ≤ (a : ℤ) * x →
          |(pieceDistance (knightMoves (a : ℤ) (b : ℤ)) (x, y) : ℝ) -
              (x : ℝ) / (b : ℝ)| ≤ M * b) ∧
        ((a : ℤ) * x < (b : ℤ) * y →
          |(pieceDistance (knightMoves (a : ℤ) (b : ℤ)) (x, y) : ℝ) -
              ((x : ℝ) + (y : ℝ)) / ((a : ℝ) + (b : ℝ))| ≤ M * b)) := by
  refine ⟨14, fun a b x y ha hab hc ho hy hyx => ?_⟩
  have hap : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hb : (0 : ℝ) < b := hap.trans hab'
  have hb₁ : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
  have hyx' : (y : ℝ) ≤ x := by exact_mod_cast hyx
  have hx' := hy'.trans hyx'
  have finish {u v : ℤ × ℤ} (hu : u ∈ knightMoves (a : ℤ) (b : ℤ))
      (hv : v ∈ knightMoves (a : ℤ) (b : ℤ)) {s t L : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
      (hx : (x : ℝ) = s * (u.1 : ℝ) + t * (v.1 : ℝ))
      (hy : (y : ℝ) = s * (u.2 : ℝ) + t * (v.2 : ℝ)) (hL : s + t = L)
      (hlower : ∀ m : ℕ, (x, y) ∈ m • knightMoves (a : ℤ) (b : ℤ) → L ≤ (m : ℝ)) :
      |(pieceDistance (knightMoves (a : ℤ) (b : ℤ)) (x, y) : ℝ) - L| ≤ 14 * b := by
    obtain ⟨n, q, hq, hn, hres⟩ := rounded_knight_path hab.le hu hv hs ht hx hy
    obtain ⟨k, hk, hkmem⟩ := exists_knight_path_on_box ha hab hc ho hres
    have hp : (x, y) ∈ (n + k) • knightMoves (a : ℤ) (b : ℤ) := by
      simpa only [add_sub_cancel] using mem_fold_add hq hkmem
    rw [abs_of_nonneg (sub_nonneg.mpr (hlower _ (mem_distance_fold hp)))]
    have hdist : (pieceDistance (knightMoves (a : ℤ) (b : ℤ)) (x, y) : ℝ) ≤ n + k := by
      exact_mod_cast distance_le_of_mem hp
    have hkr : (k : ℝ) ≤ 13 * b := by exact_mod_cast hk
    linarith only [hn, hkr, hb₁, hdist, hL]
  constructor
  · intro h
    have h' : (b : ℝ) * y ≤ (a : ℝ) * x := by exact_mod_cast h
    have hratio : (y : ℝ) / a ≤ (x : ℝ) / b := by
      apply (div_le_div_iff₀ hap hb).2
      linarith only [h']
    let s := ((x : ℝ) / b + (y : ℝ) / a) / 2
    let t := ((x : ℝ) / b - (y : ℝ) / a) / 2
    refine finish (u := ((b : ℤ), (a : ℤ))) (v := ((b : ℤ), -(a : ℤ))) (s := s) (t := t)
      (by simp [knightMoves]) (by simp [knightMoves]) (by dsimp [s]; positivity)
      (by dsimp [t]; linarith only [hratio]) ?_ ?_ ?_ ?_
    · push_cast; dsimp [s, t]; field_simp; ring
    · push_cast; dsimp [s, t]; field_simp; ring
    · dsimp [s, t]; ring
    · intro m hm
      have hl : (x : ℝ) ≤ (m : ℝ) * (b : ℝ) := by
        exact_mod_cast (knight_fold_bounds hab.le hm).1
      exact (div_le_iff₀ hb).2 hl
  · intro h
    have h' : (a : ℝ) * x < (b : ℝ) * y := by exact_mod_cast h
    let D := (b : ℝ) ^ 2 - (a : ℝ) ^ 2
    have hD : 0 < D := by
      dsimp [D]
      nlinarith only [mul_pos (sub_pos.mpr hab') (add_pos hb hap)]
    let s := ((b : ℝ) * y - (a : ℝ) * x) / D
    let t := ((b : ℝ) * x - (a : ℝ) * y) / D
    have hfactor : D = ((b : ℝ) - a) * ((a : ℝ) + b) := by dsimp [D]; ring
    refine finish (u := ((a : ℤ), (b : ℤ))) (v := ((b : ℤ), (a : ℤ))) (s := s) (t := t)
      (by simp [knightMoves]) (by simp [knightMoves])
      (div_nonneg (sub_pos.mpr h').le hD.le) ?_ ?_ ?_ ?_ ?_
    · apply div_nonneg _ hD.le
      exact sub_nonneg.mpr ((mul_le_mul_of_nonneg_left hyx' hap.le).trans
        (mul_le_mul_of_nonneg_right hab'.le hx'))
    · push_cast; dsimp [s, t]; field_simp; dsimp [D]; ring
    · push_cast; dsimp [s, t]; field_simp; dsimp [D]; ring
    · dsimp [s, t]; field_simp; rw [hfactor]; ring
    · intro m hm
      have hl : (x : ℝ) + (y : ℝ) ≤ (m : ℝ) * ((a : ℝ) + (b : ℝ)) := by
        exact_mod_cast (knight_fold_bounds hab.le hm).2
      exact (div_le_iff₀ (add_pos hap hb)).2 hl

end

end MetaMathlibExt
