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
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# A uniform bound for generalized knight distance

A pair of knight moves travels along a coordinate axis. Bounded Bézout
coefficients then give short paths for points with even coordinates. At most
two additional moves correct the parities of an arbitrary point in the box.
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

end

end MetaMathlibExt
