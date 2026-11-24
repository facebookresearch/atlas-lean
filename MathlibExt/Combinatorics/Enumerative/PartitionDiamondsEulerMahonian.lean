/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.Ring

/-!
# Recursion for the Euler–Mahonian polynomials

Inserting the smallest letter into a permutation gives the recurrence for the joint generating
polynomial of its descent number and major index. We also define the bivariate generating
series that counts multifold partition diamonds by fold sum and link sum.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Value of a permutation at a natural position.** For a permutation $\tau$ of
$\{0, 1, \dots, d - 1\}$ and a natural number $j$, this is the natural number $\tau(j)$ when
$j < d$, and $0$ when $j \ge d$. It is used to read off descents.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 1 (descent statistics). -/
public def permValueAt {d : ℕ} (τ : Equiv.Perm (Fin d)) (j : ℕ) : ℕ :=
  if h : j < d then τ ⟨j, h⟩ else 0

/-- **Descent set of a permutation.** For a permutation $\tau$ of $\{0, 1, \dots, d - 1\}$, the
descent set is $\mathrm{Des}(\tau) = \{p \in \{1, \dots, d - 1\} : \tau(p - 1) > \tau(p)\}$. If
$\tau$ is read as the permutation $p \mapsto \tau(p - 1) + 1$ of $\{1, \dots, d\}$, this is the
usual descent set: the positions $p$, numbered from $1$, where the value at $p$ exceeds the
value at $p + 1$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 1. -/
public def permDescentSet {d : ℕ} (τ : Equiv.Perm (Fin d)) : Finset ℕ :=
  ((Finset.range (d - 1)).filter fun j => permValueAt τ (j + 1) < permValueAt τ j).map
    ⟨(· + 1), add_left_injective 1⟩

/-- **Number of descents from the descent set.** For a permutation $\tau$ of
$\{0, 1, \dots, d - 1\}$, the number of descents $\mathrm{des}(\tau) = |\mathrm{Des}(\tau)|$ is the
number of elements of the descent set $\mathrm{Des}(\tau)$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 1. -/
public def permDes {d : ℕ} (τ : Equiv.Perm (Fin d)) : ℕ := (permDescentSet τ).card

/-- **Major index of a permutation.** For a permutation $\tau$ of $\{0, 1, \dots, d - 1\}$, the
major index is $\mathrm{maj}(\tau) = \sum_{p \in \mathrm{Des}(\tau)} p$, the sum of the
positions, numbered from $1$, in the descent set $\mathrm{Des}(\tau)$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 1. -/
public def permMaj {d : ℕ} (τ : Equiv.Perm (Fin d)) : ℕ := ∑ j ∈ permDescentSet τ, j

/-- **Euler–Mahonian polynomial.** For a natural number $d$ and elements $x, y$ of a commutative
ring, the Euler–Mahonian polynomial evaluated at $(x, y)$ is
$E_d(x, y) = \sum_{\tau \in S_d} x^{\operatorname{des}(\tau)} y^{\operatorname{maj}(\tau)}$,
where $\operatorname{des}(\tau)$ is the number of descents and $\operatorname{maj}(\tau)$ the
major index of the permutation $\tau$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 1. -/
public def eulerMahonian (R : Type*) [CommRing R] (d : ℕ) (x y : R) : R :=
  ∑ τ : Equiv.Perm (Fin d), x ^ permDes τ * y ^ permMaj τ

/-- **The first Euler–Mahonian polynomial is $1$.** For every commutative ring $R$ and all
$x, y \in R$, the Euler–Mahonian polynomial $E_1$ satisfies $E_1(x, y) = 1$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 1 (`F_1 = 1` in recursion (1)). -/
public theorem eulerMahonian_one (R : Type*) [CommRing R] (x y : R) :
    eulerMahonian R 1 x y = 1 := by
  simp [eulerMahonian, permDes, permMaj, permDescentSet]

/-- **Euler–Mahonian polynomial $E_3$ at $(2, 3)$.** Over the integers, the Euler–Mahonian
polynomial $E_3$ takes the value $E_3(2, 3) = 157$.

This agrees with $E_3(x, y) = 1 + 2xy + 2xy^2 + x^2y^3$: the six permutations of $S_3$ have
$(\operatorname{des}, \operatorname{maj})$ equal to $(0, 0)$, $(1, 1)$, $(1, 1)$, $(1, 2)$,
$(1, 2)$ and $(2, 3)$. Only the value at $x = 2$, $y = 3$ is checked, not the polynomial
identity.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 1. -/
public theorem eulerMahonian_three_two_three : eulerMahonian ℤ 3 2 3 = 157 := by decide

/-- **Permutations of $S_3$ with descent set $\{1\}$.** Exactly two permutations $\tau \in S_3$
have exactly one descent and major index $1$, that is, $\operatorname{des}(\tau) = 1$ and
$\operatorname{maj}(\tau) = 1$; equivalently, their descent set is $\{1\}$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 1. -/
public theorem card_perm_three_des_one_maj_one :
    ((Finset.univ : Finset (Equiv.Perm (Fin 3))).filter
      fun τ => permDes τ = 1 ∧ permMaj τ = 1).card = 2 := by decide

namespace eulerMahonian_succ_recursion

open Equiv.Perm

variable {n : ℕ}

/-- Insert zero at position `i` and increment each old letter. -/
private noncomputable def insertMin (i : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :=
  (decomposeFin'Symm i τ.symm).symm

private theorem value_at_slot (i : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    permValueAt (insertMin i τ) i = 0 := by
  simp [permValueAt, insertMin]

private theorem value_before (i : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1)))
    (j : ℕ) (hj : j < i) : permValueAt (insertMin i τ) j = permValueAt τ j + 1 := by
  have hj' : j < n + 1 := by omega
  let a : Fin (n + 1) := ⟨j, hj'⟩
  have h : (insertMin i τ) (i.succAbove a) = (τ a).succ := by
    simpa [insertMin] using decomposeFin'Symm_symm_succAbove i τ.symm (τ a)
  rw [Fin.succAbove_of_castSucc_lt _ _ hj] at h
  simpa [permValueAt, hj', show j < n + 2 by omega, a] using congrArg Fin.val h

private theorem value_after (i : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1)))
    (j : ℕ) (hij : i ≤ j) (hj : j < n + 1) :
    permValueAt (insertMin i τ) (j + 1) = permValueAt τ j + 1 := by
  let a : Fin (n + 1) := ⟨j, hj⟩
  have h : (insertMin i τ) (i.succAbove a) = (τ a).succ := by
    simpa [insertMin] using decomposeFin'Symm_symm_succAbove i τ.symm (τ a)
  rw [Fin.succAbove_of_le_castSucc _ _ hij] at h
  simpa [permValueAt, hj, show j + 1 < n + 2 by omega, a] using congrArg Fin.val h

/-- Include the initial position as a sentinel in the descent set. -/
private def breaks {d : ℕ} (τ : Equiv.Perm (Fin d)) := insert 0 (permDescentSet τ)

private theorem mem_breaks_succ {d : ℕ} (τ : Equiv.Perm (Fin d)) (j : ℕ) :
    j + 1 ∈ breaks τ ↔ j + 1 < d ∧ permValueAt τ (j + 1) < permValueAt τ j := by
  simp [breaks, permDescentSet]
  omega

private theorem zero_not_descent {d : ℕ} (τ : Equiv.Perm (Fin d)) :
    0 ∉ permDescentSet τ := by
  simp [permDescentSet]

/-- A descent strictly after the insertion slot moves one place to the right. -/
private def shift (i : ℕ) : ℕ ↪ ℕ where
  toFun p := if i < p then p + 1 else p
  inj' := by
    intro p q h
    dsimp at h
    split at h <;> split at h <;> omega

private theorem shift_apply (i p : ℕ) : shift i p = (if i < p then p + 1 else p) := rfl

private theorem mem_shift_of_le {i p : ℕ} (h : p ≤ i) (s : Finset ℕ) :
    p ∈ s.map (shift i) ↔ p ∈ s := by
  simpa [shift_apply, h.not_gt] using (Finset.mem_map' (shift i) (s := s) (a := p))

private theorem breaks_insertMin (i : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    breaks (insertMin i τ) = insert i.val ((breaks τ).map (shift i)) := by
  ext p
  cases p with
  | zero => simp [breaks, shift_apply]
  | succ j =>
    rw [mem_breaks_succ, Finset.mem_insert]
    rcases lt_trichotomy (j + 1) i.val with h | h | h
    · rw [mem_shift_of_le h.le, mem_breaks_succ, value_before i τ _ h,
        value_before i τ j (by omega)]
      omega
    · rw [h, value_at_slot, value_before i τ j (by omega)]
      simp [i.isLt]
    · rw [or_iff_right (by omega : j + 1 ≠ i.val)]
      rcases eq_or_lt_of_le (show i.val ≤ j by omega) with he | he
      · subst j
        have hgap : i.val + 1 ∉ (breaks τ).map (shift i.val) := by
          rintro hj
          obtain ⟨k, _, hk⟩ := Finset.mem_map.mp hj
          rw [shift_apply] at hk
          split at hk <;> omega
        simp only [hgap, iff_false, not_and]
        intro hi
        rw [value_after i τ _ le_rfl (by omega), value_at_slot]
        omega
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
        have hmap := Finset.mem_map' (shift i.val) (s := breaks τ) (a := k + 1)
        rw [shift_apply, ite_eq_left he] at hmap
        rw [hmap, mem_breaks_succ]
        by_cases hk : k + 1 < n + 1
        · rw [value_after i τ _ he.le hk, value_after i τ k (by omega) (by omega)]
          simp only [Nat.succ_eq_add_one, Nat.add_lt_add_iff_right]
        · omega

private def rightCount (s : Finset ℕ) (i : ℕ) := (s.filter (i < ·)).card

private theorem card_breaks {d : ℕ} (τ : Equiv.Perm (Fin d)) :
    (breaks τ).card = permDes τ + 1 := by
  simp [breaks, permDes, zero_not_descent]

private theorem sum_breaks {d : ℕ} (τ : Equiv.Perm (Fin d)) :
    ∑ p ∈ breaks τ, p = permMaj τ := by
  simp [breaks, permMaj, zero_not_descent]

private theorem des_insertMin (i : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    permDes (insertMin i τ) = permDes τ + (if i.val ∈ breaks τ then 0 else 1) := by
  have h := congrArg Finset.card (breaks_insertMin i τ)
  by_cases hi : i.val ∈ breaks τ
  · simpa [card_breaks, Finset.insert_eq_of_mem ((mem_shift_of_le le_rfl _).mpr hi), hi] using h
  · have hi' := (mem_shift_of_le le_rfl _).not.mpr hi
    simpa [Finset.card_insert_of_notMem hi', card_breaks, hi] using h

private theorem maj_insertMin (i : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) :
    permMaj (insertMin i τ) = permMaj τ + rightCount (breaks τ) i +
      (if i.val ∈ breaks τ then 0 else i.val) := by
  have hs : ∑ p ∈ (breaks τ).map (shift i.val), p = permMaj τ + rightCount (breaks τ) i := by
    simp only [Finset.sum_map, shift_apply]
    simp_rw [show ∀ p : ℕ, (if i.val < p then p + 1 else p) =
        p + (if i.val < p then 1 else 0) from fun p => by split <;> simp_all]
    simp [Finset.sum_add_distrib, sum_breaks, rightCount, Finset.sum_boole]
  rw [← sum_breaks, breaks_insertMin]
  by_cases hi : i.val ∈ breaks τ
  · simp [Finset.insert_eq_of_mem ((mem_shift_of_le le_rfl _).mpr hi), hs, hi]
  · have hi' := (mem_shift_of_le le_rfl _).not.mpr hi
    simp [Finset.sum_insert hi', hs, hi, add_comm]

private theorem rightCount_step (s : Finset ℕ) (i : ℕ) :
    rightCount s i = rightCount s (i + 1) + (if i + 1 ∈ s then 1 else 0) := by
  unfold rightCount
  by_cases h : i + 1 ∈ s
  · have he : s.filter (i < ·) = insert (i + 1) (s.filter (i + 1 < ·)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      grind
    simp [he, h]
  · have he : s.filter (i < ·) = s.filter (i + 1 < ·) := by
      apply Finset.filter_congr
      grind
    simp [he, h]

variable {R : Type*} [CommRing R]

/-- The factor gained by inserting at `i`, after removing the weight of the old permutation. -/
private def slotWeight (s : Finset ℕ) (x y : R) (i : ℕ) : R :=
  if i ∈ s then y ^ rightCount s i else x * y ^ (i + rightCount s i)

private theorem weight_insertMin (i : Fin (n + 2)) (τ : Equiv.Perm (Fin (n + 1))) (x y : R) :
    x ^ permDes (insertMin i τ) * y ^ permMaj (insertMin i τ) =
      (x ^ permDes τ * y ^ permMaj τ) * slotWeight (breaks τ) x y i := by
  rw [des_insertMin, maj_insertMin]
  by_cases hi : i.val ∈ breaks τ <;> simp [slotWeight, hi, pow_add] <;> ring

/-- As the slot moves right, descent slots and the other slots each telescope. -/
private theorem sum_slotWeight (s : Finset ℕ) (h₀ : 0 ∈ s) (x y : R) (m : ℕ) :
    (1 - y) * ∑ i ∈ Finset.range (m + 1), slotWeight s x y i =
      y ^ rightCount s m - y ^ (rightCount s 0 + 1) +
        x * (y ^ (rightCount s 0 + 1) - y ^ (m + rightCount s m + 1)) := by
  induction m with
  | zero => simp [slotWeight, h₀, pow_succ, sub_mul, mul_comm]
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h := rightCount_step s m
    by_cases hm : m + 1 ∈ s <;> simp [hm] at h <;>
      simp only [slotWeight, hm, h, ↓reduceIte, pow_add, pow_one] <;> ring

private theorem sum_insertMin (τ : Equiv.Perm (Fin (n + 1))) (x y : R) :
    (1 - y) * ∑ i : Fin (n + 2), x ^ permDes (insertMin i τ) * y ^ permMaj (insertMin i τ) =
      (1 - x * y ^ (n + 2)) * (x ^ permDes τ * y ^ permMaj τ) -
        y * (1 - x) * ((x * y) ^ permDes τ * y ^ permMaj τ) := by
  have h₀ : rightCount (breaks τ) 0 = permDes τ := by
    unfold rightCount breaks
    rw [Finset.filter_insert]
    simp only [lt_irrefl, ↓reduceIte]
    rw [Finset.filter_true_of_mem]
    · rfl
    · exact fun p hp => Nat.pos_of_ne_zero (fun he => zero_not_descent τ (he ▸ hp))
  have hn : rightCount (breaks τ) (n + 1) = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_false_of_mem
    intro p hp
    cases p with
    | zero => omega
    | succ j =>
      have := ((mem_breaks_succ ..).mp hp).1
      omega
  simp_rw [weight_insertMin]
  rw [← Finset.mul_sum, mul_left_comm, Fin.sum_univ_eq_sum_range,
    sum_slotWeight (breaks τ) (Finset.mem_insert_self ..), h₀, hn]
  simp only [pow_zero, add_zero, pow_succ, mul_pow]
  ring

private theorem eulerMahonian_eq_sum_insertMin (n : ℕ) (x y : R) :
    eulerMahonian R (n + 2) x y = ∑ τ : Equiv.Perm (Fin (n + 1)), ∑ i : Fin (n + 2),
      x ^ permDes (insertMin i τ) * y ^ permMaj (insertMin i τ) := by
  let e : Fin (n + 2) × Equiv.Perm (Fin (n + 1)) ≃ Equiv.Perm (Fin (n + 2)) :=
    ((Equiv.refl _).prodCongr (Equiv.symmEquiv _ _)).trans
      (decomposeFin'.symm.trans (Equiv.symmEquiv _ _))
  rw [eulerMahonian, ← e.sum_comp, Fintype.sum_prod_type_right]
  rfl

end eulerMahonian_succ_recursion

open eulerMahonian_succ_recursion in
/-- **Recursion for the Euler–Mahonian polynomials.** For every commutative ring $R$, every
natural number $d \ge 1$ and all $x, y \in R$, the Euler–Mahonian polynomials $E_d$ and
$E_{d+1}$ satisfy

$$(1 - y) E_{d+1}(x, y) = (1 - x y^{d+1}) E_d(x, y) - y (1 - x) E_d(xy, y).$$

Together with $E_1 = 1$, this says that the Euler–Mahonian polynomials are the
Dockery–Jameson–Sellers–Wilson polynomials $F_d$, defined by $F_1 = 1$ and
$F_d(q_0, w) = \bigl((1 - q_0 w^d) F_{d-1}(q_0, w) - w (1 - q_0) F_{d-1}(q_0 w, w)\bigr)/(1 - w)$
for $d \ge 2$: since $1 - w$ is a nonzerodivisor in $\mathbb{Z}[q_0, w]$, the recursion is
stated multiplied by $1 - w$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Theorem 1 (`integers-2026-A13-thm-1`) with
recursion (1). -/
public theorem eulerMahonian_succ_recursion (R : Type*) [CommRing R] (d : ℕ)
    (hd : 1 ≤ d) (x y : R) :
    (1 - y) * eulerMahonian R (d + 1) x y =
      (1 - x * y ^ (d + 1)) * eulerMahonian R d x y -
        y * (1 - x) * eulerMahonian R d (x * y) y := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  rw [eulerMahonian_eq_sum_insertMin, Finset.mul_sum]
  simp_rw [sum_insertMin]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

/-- **Position of the $k$th link of a multifold partition diamond.** For natural numbers
$d_1, \dots, d_M$ (the numbers of folds of the $M$ diamonds) and a natural number $k$, the
position of the $k$th link, counting positions from $0$, is
$L_k = \sum_{m=1}^{\min(k, M)} (d_m + 1)$. In particular $L_0 = 0$, and
$L_k = d_1 + \dots + d_M + M$ for every $k \ge M$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Figure 3 and Section 3. -/
public def diamondLinkPos (ds : List ℕ) (k : ℕ) : ℕ := ((ds.take k).map (· + 1)).sum

/-- **Number of parts of a multifold partition diamond.** The multifold partition diamond whose
$M$ diamonds have $d_1, \dots, d_M$ folds has $c = d_1 + \dots + d_M + M + 1$ parts.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Figure 3 (`c = M(d + 1) + 1`). -/
public def diamondSize (ds : List ℕ) : ℕ := diamondLinkPos ds ds.length + 1

/-- **The set of link positions of a multifold partition diamond.** For natural numbers
$d_1, \dots, d_M$, the set of link positions is $\{L_0, L_1, \dots, L_M\}$, where
$L_k = \sum_{m=1}^{k} (d_m + 1)$ is the position of the $k$th link. These positions satisfy
$0 = L_0 < L_1 < \dots < L_M = c - 1$, where $c = d_1 + \dots + d_M + M + 1$ is the number of
parts.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Figure 3. -/
public def diamondLinks (ds : List ℕ) : Finset ℕ :=
  (Finset.range (ds.length + 1)).image (diamondLinkPos ds)

/-- **Multifold partition diamonds with given fold and link sums.** Let $d_1, \dots, d_M$ be
natural numbers, let $L_k = \sum_{m=1}^{k} (d_m + 1)$ for $0 \le k \le M$ be the link
positions, let $c = L_M + 1$, and let $i$ and $j$ be natural numbers. A function
$b : \mathbb{N} \to \mathbb{N}$ is a multifold partition diamond with fold sum $i$ and link sum
$j$ when the following hold: for every $k$ with $0 \le k < M$ and every $f$ with
$1 \le f \le d_{k+1}$, we have $b(L_k) \le b(L_k + f) \le b(L_{k+1})$; the sum of $b(p)$ over
the positions $p < c$ different from $L_0, \dots, L_M$ is $i$; and
$b(L_0) + \dots + b(L_M) = j$.

This models the paper's $P$-partitions (order-preserving maps to $\mathbb{Z}_{\ge 0}$) of the
poset in which, for each $k < M$, the folds at positions $L_k + 1, \dots, L_k + d_{k+1}$ lie
above the link at $L_k$ and below the link at $L_{k+1}$. In particular, when every
$d_k \ge 1$, $b(0)$ is the smallest of $b(0), \dots, b(c - 1)$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Sections 2-3. -/
public def IsMultifoldDiamond (ds : List ℕ) (i j : ℕ) (b : ℕ → ℕ) : Prop :=
  (∀ k ∈ Finset.range ds.length, ∀ f ∈ Finset.Icc 1 (ds.getD k 0),
      b (diamondLinkPos ds k) ≤ b (diamondLinkPos ds k + f) ∧
        b (diamondLinkPos ds k + f) ≤ b (diamondLinkPos ds (k + 1))) ∧
    (∑ p ∈ (Finset.range (diamondSize ds)).filter (· ∉ diamondLinks ds), b p) = i ∧
    (∑ p ∈ diamondLinks ds, b p) = j

/-- Decidability of `IsMultifoldDiamond`.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Sections 2-3. -/
public instance (ds : List ℕ) (i j : ℕ) : DecidablePred (IsMultifoldDiamond ds i j) :=
  fun b => by unfold IsMultifoldDiamond; infer_instance

/-- **Extending a part vector by zero.** Let $c = d_1 + \dots + d_M + M + 1$ be the number of
parts of the multifold partition diamond whose diamonds have $d_1, \dots, d_M$ folds, and let
$n$ be a natural number. A vector $(a_0, \dots, a_{c-1})$ with entries in $\{0, \dots, n - 1\}$
is read as the function $\mathbb{N} \to \mathbb{N}$ that sends $p$ to $a_p$ for $p < c$ and to
$0$ for $p \ge c$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Section 2. -/
public def diamondPart {ds : List ℕ} {n : ℕ} (a : Fin (diamondSize ds) → Fin n) (p : ℕ) : ℕ :=
  if h : p < diamondSize ds then (a ⟨p, h⟩ : ℕ) else 0

/-- **Number of multifold partition diamonds.** Let $d_1, \dots, d_M$ be natural numbers. Put
$L_k = \sum_{m=1}^{k} (d_m + 1)$ for $0 \le k \le M$ and $c = L_M + 1$. A multifold partition
diamond of shape $(d_1, \dots, d_M)$ is a sequence $(b_0, \dots, b_{c-1})$ of nonnegative integers
such that $b_{L_{k-1}} \le b_{L_{k-1} + f} \le b_{L_k}$ for all $1 \le k \le M$ and
$1 \le f \le d_k$. The parts $b_{L_0}, \dots, b_{L_M}$ are its links and the other parts are its
folds; its link sum is $\sum_{k=0}^{M} b_{L_k}$ and its fold sum is the sum of its folds. This is
the number of multifold partition diamonds of shape $(d_1, \dots, d_M)$ with fold sum $i$ and
link sum $j$.

Every part of such a diamond is at most $i + j$, so this number is finite.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, equation (2) and Section 3. -/
public def multifoldDiamondCount (ds : List ℕ) (i j : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (diamondSize ds) → Fin (i + j + 1))).filter fun a =>
    IsMultifoldDiamond ds i j (diamondPart a)).card

/-- **Single-fold diamonds with fold sum 1 and link sum 1.** There is exactly one multifold
partition diamond of shape $(1)$ with fold sum $1$ and link sum $1$. Equivalently, there is exactly
one triple of nonnegative integers $b_0 \le b_1 \le b_2$ with $b_1 = 1$ and $b_0 + b_2 = 1$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, equation (2). -/
public theorem multifoldDiamondCount_one_one_one : multifoldDiamondCount [1] 1 1 = 1 := by
  decide

/-- **Two-fold diamonds with fold sum 1 and link sum 2.** There are exactly two multifold
partition diamonds of shape $(2)$ with fold sum $1$ and link sum $2$. Equivalently, there are
exactly two quadruples $(b_0, b_1, b_2, b_3)$ of nonnegative integers with $b_0 \le b_f \le b_3$
for $f = 1, 2$, $b_1 + b_2 = 1$ and $b_0 + b_3 = 2$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, equation (2). -/
public theorem multifoldDiamondCount_two_one_two : multifoldDiamondCount [2] 1 2 = 2 := by
  decide

/-- **The bivariate series of multifold partition diamonds.** For natural numbers
$d_1, \dots, d_M$, $\sigma_{d_1, \dots, d_M}(a, b)$ is the formal power series in
$\mathbb{Z}[[a, b]]$ whose coefficient of $a^i b^j$ is the number of multifold partition diamonds
of shape $(d_1, \dots, d_M)$ with fold sum $i$ and link sum $j$. That is,
$\sigma_{d_1, \dots, d_M}(a, b) = \sum a^{\text{fold sum}} b^{\text{link sum}}$, summed over all
such diamonds. We write $\sigma_{d,M}$ for the case $d_1 = \dots = d_M = d$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, equation (2) and Section 3. -/
public def multifoldDiamondSeries (ds : List ℕ) : MvPowerSeries (Fin 2) ℤ :=
  fun e => (multifoldDiamondCount ds (e 0) (e 1) : ℤ)

end

end MetaMathlibExt
