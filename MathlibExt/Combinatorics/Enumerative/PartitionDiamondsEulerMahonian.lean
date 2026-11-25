/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.RingTheory.MvPowerSeries.PiTopology
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


section WeightEnum

open scoped MvPowerSeries.WithPiTopology

private abbrev Weight := Fin 2 →₀ ℕ
private abbrev WeightSeries := MvPowerSeries (Fin 2) ℤ

/-- Each given bidegree is attained finitely often. -/
private def FiniteWeightFibers {α : Type*} (w : α → Weight) : Prop :=
  ∀ e, Finite {x // w x = e}

/-- The coefficientwise sum of the monomials contributed by the weighted objects. -/
private noncomputable def weightEnum {α : Type*} (w : α → Weight) : WeightSeries :=
  ∑' x, MvPowerSeries.monomial (w x) (1 : ℤ)

private theorem hasSum_weightEnum {α : Type*} (w : α → Weight) (hw : FiniteWeightFibers w) :
    HasSum (fun x ↦ MvPowerSeries.monomial (w x) (1 : ℤ))
      (fun e ↦ (Nat.card {x // w x = e} : ℤ) : WeightSeries) := by
  classical
  refine MvPowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff.mpr fun e ↦ ?_
  change HasSum (fun x ↦ MvPowerSeries.coeff e (MvPowerSeries.monomial (w x) (1 : ℤ)))
    (Nat.card {x // w x = e} : ℤ)
  let _ := hw e
  let _ := Fintype.ofFinite {x // w x = e}
  have h : HasSum (fun _ : {x // w x = e} ↦ (1 : ℤ)) (Nat.card {x // w x = e} : ℤ) := by
    rw [Nat.card_eq_fintype_card]
    simpa using (hasSum_fintype (fun _ : {x // w x = e} ↦ (1 : ℤ)))
  apply ((hasSum_subtype_iff_indicator (s := {x | w x = e}) (f := fun _ ↦ (1 : ℤ))).mp h).congr_fun
  intro x
  simp [Set.indicator_apply, MvPowerSeries.coeff_monomial, eq_comm]

private theorem summable_weightEnum {α : Type*} (w : α → Weight) (hw : FiniteWeightFibers w) :
    Summable (fun x ↦ MvPowerSeries.monomial (w x) (1 : ℤ)) :=
  (hasSum_weightEnum w hw).summable

private theorem coeff_weightEnum {α : Type*} (w : α → Weight) (hw : FiniteWeightFibers w)
    (e : Weight) : MvPowerSeries.coeff e (weightEnum w) = (Nat.card {x // w x = e} : ℤ) := by
  rw [weightEnum, (hasSum_weightEnum w hw).tsum_eq]
  rfl

private theorem weightEnum_equiv {α β : Type*} (E : α ≃ β) {w : α → Weight} {v : β → Weight}
    (hw : ∀ x, w x = v (E x)) : weightEnum w = weightEnum v := by
  simp only [weightEnum, hw]
  exact E.tsum_eq (fun x ↦ MvPowerSeries.monomial (v x) (1 : ℤ))

private theorem weightEnum_fintype {α : Type*} [Fintype α] (w : α → Weight) :
    weightEnum w = ∑ x, MvPowerSeries.monomial (w x) (1 : ℤ) :=
  tsum_fintype (fun x ↦ MvPowerSeries.monomial (w x) (1 : ℤ))

private theorem finiteWeightFibers_le {α : Type*} {w : α → Weight} (hw : FiniteWeightFibers w)
    (e : Weight) : Finite {x // w x ≤ e} := by
  classical
  let _ : Finite {d : Weight // d ≤ e} := (Set.finite_Iic e).to_subtype
  let _ (d : {d : Weight // d ≤ e}) : Finite {x // w x = d.val} := hw d.val
  exact Finite.of_injective
    (fun x : {x // w x ≤ e} ↦
      (⟨⟨w x.val, x.property⟩, ⟨x.val, rfl⟩⟩ : Σ d : {d : Weight // d ≤ e}, {x // w x = d.val}))
    (fun x y h ↦ Subtype.ext (congrArg (fun z ↦ z.2.val) h))

private theorem finiteWeightFibers_prod {α β : Type*} (w : α → Weight) (v : β → Weight)
    (hw : FiniteWeightFibers w) (hv : FiniteWeightFibers v) :
    FiniteWeightFibers (fun p : α × β ↦ w p.1 + v p.2) := by
  intro e
  let _ := finiteWeightFibers_le hw e
  let _ := finiteWeightFibers_le hv e
  exact Finite.of_injective
    (fun p : {p : α × β // w p.1 + v p.2 = e} ↦
      ((⟨p.val.1, (le_add_of_nonneg_right zero_le).trans_eq p.property⟩,
        ⟨p.val.2, (le_add_of_nonneg_left zero_le).trans_eq p.property⟩) :
        {a // w a ≤ e} × {b // v b ≤ e}))
    (fun p q h ↦ Subtype.ext (congrArg (fun z ↦ (z.1.val, z.2.val)) h))

private theorem weightEnum_prod {α β : Type*} (w : α → Weight) (v : β → Weight)
    (hw : FiniteWeightFibers w) (hv : FiniteWeightFibers v) :
    weightEnum (fun p : α × β ↦ w p.1 + v p.2) = weightEnum w * weightEnum v := by
  have h := summable_weightEnum _ (finiteWeightFibers_prod w v hw hv)
  have hmul (p : α × β) :
      MvPowerSeries.monomial (w p.1) (1 : ℤ) * MvPowerSeries.monomial (v p.2) (1 : ℤ) =
        MvPowerSeries.monomial (w p.1 + v p.2) (1 : ℤ) := by
    rw [MvPowerSeries.monomial_mul_monomial, one_mul]
  have hprod : Summable (fun p : α × β ↦
      MvPowerSeries.monomial (w p.1) (1 : ℤ) * MvPowerSeries.monomial (v p.2) (1 : ℤ)) := by
    simpa only [hmul] using h
  simpa only [weightEnum, hmul] using
    ((summable_weightEnum w hw).tsum_mul_tsum (summable_weightEnum v hv) hprod).symm

private theorem finiteWeightFibers_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    (w : ∀ i, α i → Weight) (hw : ∀ i, FiniteWeightFibers (w i)) :
    FiniteWeightFibers (fun x : ∀ i, α i ↦ ∑ i, w i (x i)) := by
  classical
  intro e
  let _ (i : ι) := finiteWeightFibers_le (hw i) e
  exact Finite.of_injective
    (fun x : {x : ∀ i, α i // ∑ i, w i (x i) = e} ↦ fun i ↦
      (⟨x.val i, (Finset.single_le_sum (f := fun j ↦ w j (x.val j))
        (fun _ _ ↦ zero_le) (Finset.mem_univ i)).trans_eq x.property⟩ : {a // w i a ≤ e}))
    (fun x y h ↦ Subtype.ext (congrArg (fun z i ↦ (z i).val) h))

universe u in
private theorem weightEnum_pi {ι : Type*} [Fintype ι] {α : ι → Type u}
    (w : ∀ i, α i → Weight) (hw : ∀ i, FiniteWeightFibers (w i)) :
    weightEnum (fun x : ∀ i, α i ↦ ∑ i, w i (x i)) = ∏ i, weightEnum (w i) := by
  classical
  refine Fintype.induction_empty_option (P := fun ι _ ↦
    ∀ (α : ι → Type u) (w : ∀ i, α i → Weight),
      (∀ i, FiniteWeightFibers (w i)) →
        weightEnum (fun x : ∀ i, α i ↦ ∑ i, w i (x i)) = ∏ i, weightEnum (w i))
    ?_ ?_ ?_ ι α w hw
  · intro ι κ _ E ih α w hw
    let _ := Fintype.ofEquiv κ E.symm
    have he (x : ∀ i, α (E i)) :
        (∑ i, w (E i) (x i)) = ∑ k, w k ((Equiv.piCongrLeft α E) x k) := by
      rw [← E.sum_comp]
      simp
    rw [← weightEnum_equiv (Equiv.piCongrLeft α E) he,
      ih _ (fun i ↦ w (E i)) (fun i ↦ hw (E i))]
    exact E.prod_comp (fun k ↦ weightEnum (w k))
  · intro α w hw
    let _ : Unique (∀ i, α i) :=
      ⟨⟨fun i ↦ PEmpty.elim i⟩, fun x ↦ funext fun i ↦ PEmpty.elim i⟩
    simp [weightEnum_fintype, MvPowerSeries.monomial_zero_one]
  · intro ι _ ih α w hw
    rw [← weightEnum_equiv Equiv.piOptionEquivProd.symm
      (w := fun p : α none × (∀ i : ι, α (some i)) ↦ w none p.1 + ∑ i, w (some i) (p.2 i))
      (by intro p; simp [Fintype.sum_option])]
    rw [weightEnum_prod _ _ (hw none) (finiteWeightFibers_pi _ (fun i ↦ hw (some i))),
      ih _ (fun i ↦ w (some i)) (fun i ↦ hw (some i)), Fintype.prod_option]

private theorem finiteWeightFibers_nsmul (e : Weight) (he : 0 < e 1) :
    FiniteWeightFibers (fun n : ℕ ↦ n • e) := by
  intro d
  have hinj : Function.Injective (fun n : ℕ ↦ n • e) := by
    intro a b h
    apply Nat.eq_of_mul_eq_mul_right he
    simpa [Finsupp.nsmul_apply, nsmul_eq_mul] using congrArg (fun v : Weight ↦ v 1) h
  exact Finite.of_injective (fun _ : {n : ℕ // n • e = d} ↦ ())
    (fun a b _ ↦ Subtype.ext (hinj (a.property.trans b.property.symm)))

private theorem one_sub_monomial_mul_weightEnum_nsmul (e : Weight) (he : 0 < e 1) :
    (1 - MvPowerSeries.monomial e (1 : ℤ)) * weightEnum (fun n : ℕ ↦ n • e) = 1 := by
  have hne : (0 : Weight) ≠ e := by
    intro h
    simp [← h] at he
  have hc : MvPowerSeries.constantCoeff (MvPowerSeries.monomial e (1 : ℤ)) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.coeff_monomial_ne hne]
  simpa only [weightEnum, MvPowerSeries.monomial_pow, one_pow] using
    MvPowerSeries.WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero hc

private theorem monomial_eq_X_pow_mul (e : Weight) :
    MvPowerSeries.monomial e (1 : ℤ) =
      (MvPowerSeries.X (0 : Fin 2) : WeightSeries) ^ e 0 * MvPowerSeries.X 1 ^ e 1 := by
  classical
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod_of_support_subset e (Finset.subset_univ _) _
    (fun _ _ ↦ pow_zero _), Fin.prod_univ_two]

end WeightEnum

/-- A block normalized so that its lower link is zero. -/
private abbrev LocalBlock (d : ℕ) := {p : ℕ × (Fin d → ℕ) // ∀ i, p.2 i ≤ p.1}

private theorem block_descent_bounds {d : ℕ} {τ : Equiv.Perm (Fin d)} {j : ℕ}
    (hj : j ∈ permDescentSet τ) : 0 < j ∧ j < d := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
  have h := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  change 0 < k + 1 ∧ k + 1 < d
  omega

private theorem block_mem_descent_step {d : ℕ} (τ : Equiv.Perm (Fin d)) (k : ℕ)
    (hk : k + 1 < d) :
    k + 1 ∈ permDescentSet τ ↔ τ ⟨k + 1, hk⟩ < τ ⟨k, by omega⟩ := by
  have hk' : k < d := by omega
  simp [permDescentSet]
  simp [permValueAt, hk, hk', show k < d - 1 by omega]

/-- A descent receives one unit of extra gap to force the adjacent values to differ. -/
private def blockBump {d : ℕ} (τ : Equiv.Perm (Fin d)) (j : ℕ) : ℕ :=
  if j ∈ permDescentSet τ then 1 else 0

/-- Heights in sorted order, starting at the upper link and ending at zero. -/
private def blockLevel {d : ℕ} (p : LocalBlock d) (τ : Equiv.Perm (Fin d)) : ℕ → ℕ
  | 0 => p.1.1
  | k + 1 => if h : k < d then p.1.2 (τ ⟨k, h⟩) else 0

private theorem block_level_step {d : ℕ} (p : LocalBlock d) (τ : Equiv.Perm (Fin d))
    (hτ : Antitone (p.1.2 ∘ τ)) (j : ℕ) : blockLevel p τ (j + 1) ≤ blockLevel p τ j := by
  cases j with
  | zero =>
    by_cases h : 0 < d
    · simpa [blockLevel, h] using p.2 (τ ⟨0, h⟩)
    · simp [blockLevel, h]
  | succ k =>
    by_cases h : k + 1 < d
    · have hk : k < d := by omega
      simpa [blockLevel, h, hk] using
        hτ (show (⟨k, hk⟩ : Fin d) ≤ ⟨k + 1, h⟩ from Nat.le_succ k)
    · simp [blockLevel, h]

private def blockRaw {d : ℕ} (p : LocalBlock d) (τ : Equiv.Perm (Fin d)) (j : Fin (d + 1)) : ℕ :=
  blockLevel p τ j.val - blockLevel p τ (j.val + 1)

private theorem block_bump_le_raw {d : ℕ} (p : LocalBlock d) (j : Fin (d + 1)) :
    let τ := Tuple.sortDesc p.1.2
    blockBump τ j.val ≤ blockRaw p τ j := by
  let τ := Tuple.sortDesc p.1.2
  change blockBump τ j.val ≤ blockRaw p τ j
  obtain ⟨j, hj⟩ := j
  by_cases h : j ∈ permDescentSet τ
  · have hb := block_descent_bounds h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb.1)
    have hk : k < d := by omega
    have hdesc := (block_mem_descent_step τ k hb.2).mp h
    obtain ⟨ha, hs⟩ := Tuple.eq_sortDesc_iff.mp (show τ = Tuple.sortDesc p.1.2 from rfl)
    have hkk : (⟨k, hk⟩ : Fin d) ≤ ⟨k + 1, hb.2⟩ := Nat.le_succ k
    have hlt : p.1.2 (τ ⟨k + 1, hb.2⟩) < p.1.2 (τ ⟨k, hk⟩) :=
      lt_of_le_of_ne (ha hkk) fun he => (not_le_of_gt hdesc) (hs hkk he.symm)
    simp only [blockBump, h, ↓reduceIte, blockRaw, blockLevel, hk, hb.2, ↓reduceDIte,
      Nat.succ_eq_add_one]
    omega
  · simp [blockBump, h]

/-- The height at rank `k` is the sum of the gaps with index at least `k`. -/
private def blockSuffix {d : ℕ} (r : Fin (d + 1) → ℕ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (d + 1) => k ≤ j.val), r j

private theorem block_suffix_anti {d : ℕ} (r : Fin (d + 1) → ℕ) : Antitone (blockSuffix r) := by
  intro k l h
  apply Finset.sum_le_sum_of_subset
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans (Finset.mem_filter.mp hj).2⟩

private theorem block_suffix_zero {d : ℕ} (r : Fin (d + 1) → ℕ) : blockSuffix r 0 = ∑ j, r j := by
  simp [blockSuffix]

private theorem block_suffix_end {d : ℕ} (r : Fin (d + 1) → ℕ) (k : ℕ) (hk : d < k) :
    blockSuffix r k = 0 := by
  unfold blockSuffix
  rw [Finset.filter_false_of_mem]
  · simp
  · intro j _
    have := j.isLt
    omega

private theorem block_suffix_step {d : ℕ} (r : Fin (d + 1) → ℕ) (j : Fin (d + 1)) :
    blockSuffix r j.val = blockSuffix r (j.val + 1) + r j := by
  have h : Finset.univ.filter (fun i : Fin (d + 1) => j.val ≤ i.val) =
      insert j (Finset.univ.filter (fun i => j.val + 1 ≤ i.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    rw [← Fin.val_inj]
    omega
  unfold blockSuffix
  rw [h, Finset.sum_insert]
  · exact Nat.add_comm _ _
  · simp

private theorem block_suffix_raw {d : ℕ} (p : LocalBlock d) (τ : Equiv.Perm (Fin d))
    (hτ : Antitone (p.1.2 ∘ τ)) (k : ℕ) (hk : k ≤ d + 1) :
    blockSuffix (blockRaw p τ) k = blockLevel p τ k := by
  refine Nat.decreasingInduction
    (motive := fun k _ => blockSuffix (blockRaw p τ) k = blockLevel p τ k) ?_ ?_ hk
  · intro j hj ih
    rw [block_suffix_step (j := ⟨j, hj⟩), ih]
    exact Nat.add_sub_of_le (block_level_step p τ hτ j)
  · simp [block_suffix_end, blockLevel]

private def blockPadded {d : ℕ} (τ : Equiv.Perm (Fin d)) (g : Fin (d + 1) → ℕ)
    (j : Fin (d + 1)) : ℕ :=
  blockBump τ j.val + g j

private def blockRebuild {d : ℕ} (τ : Equiv.Perm (Fin d)) (g : Fin (d + 1) → ℕ) : LocalBlock d :=
  let r := blockPadded τ g
  ⟨(blockSuffix r 0, fun i => blockSuffix r ((τ.symm i).val + 1)),
    fun _ => block_suffix_anti r (Nat.zero_le _)⟩

private theorem block_level_rebuild {d : ℕ} (τ : Equiv.Perm (Fin d)) (g : Fin (d + 1) → ℕ)
    (k : ℕ) : blockLevel (blockRebuild τ g) τ k = blockSuffix (blockPadded τ g) k := by
  cases k with
  | zero => rfl
  | succ k =>
    by_cases h : k < d
    · simp [blockLevel, blockRebuild, h]
    · rw [block_suffix_end _ _ (by omega)]
      simp [blockLevel, h]

private theorem block_sort_rebuild {d : ℕ} (τ : Equiv.Perm (Fin d)) (g : Fin (d + 1) → ℕ) :
    Tuple.sortDesc (blockRebuild τ g).1.2 = τ := by
  symm
  apply Tuple.eq_sortDesc_iff.mpr
  let r := blockPadded τ g
  have hv (i : Fin d) : (blockRebuild τ g).1.2 (τ i) = blockSuffix r (i.val + 1) := by
    simp [blockRebuild, r]
  refine ⟨?_, ?_⟩
  · intro i j hij
    simpa only [Function.comp_apply, hv] using
      block_suffix_anti r (Nat.succ_le_succ (show i.val ≤ j.val from hij))
  · intro i j hij he
    change (blockRebuild τ g).1.2 (τ i) = (blockRebuild τ g).1.2 (τ j) at he
    rw [hv, hv] at he
    let key (i : Fin d) : (OrderDual ℕ) ×ₗ Fin d :=
      toLex (OrderDual.toDual (blockSuffix r (i.val + 1)), τ i)
    have hm : Monotone key := by
      cases d with
      | zero => exact fun {i} => i.elim0
      | succ n =>
        apply Fin.monotone_iff_le_succ.mpr
        intro k
        have hk : k.val + 1 < n + 1 := Nat.succ_lt_succ k.isLt
        have hstep := block_suffix_step r ⟨k.val + 1, by omega⟩
        change toLex (OrderDual.toDual (blockSuffix r (k.val + 1)), τ k.castSucc) ≤
          toLex (OrderDual.toDual (blockSuffix r (k.val + 2)), τ k.succ)
        rw [Prod.Lex.toLex_le_toLex]
        change blockSuffix r (k.val + 2) < blockSuffix r (k.val + 1) ∨
          blockSuffix r (k.val + 1) = blockSuffix r (k.val + 2) ∧ τ k.castSucc ≤ τ k.succ
        by_cases h : τ k.succ < τ k.castSucc
        · left
          have hd := (block_mem_descent_step τ k.val hk).mpr h
          change blockSuffix r (k.val + 1) = blockSuffix r (k.val + 2) +
            (blockBump τ (k.val + 1) + g ⟨k.val + 1, by omega⟩) at hstep
          simp only [blockBump, hd, ↓reduceIte] at hstep
          omega
        · rcases lt_or_eq_of_le (block_suffix_anti r (Nat.le_succ (k.val + 1))) with hlt | heq
          · exact Or.inl hlt
          · exact Or.inr ⟨heq.symm, le_of_not_gt h⟩
    have h := Prod.Lex.toLex_le_toLex.mp (hm hij)
    change blockSuffix r (j.val + 1) < blockSuffix r (i.val + 1) ∨
      blockSuffix r (i.val + 1) = blockSuffix r (j.val + 1) ∧ τ i ≤ τ j at h
    exact (h.resolve_left he.not_gt).2

/-- Sort folds by decreasing height, breaking ties by increasing original index.
Gap `j` has `j` folds above it; remove one unit at each descent to obtain free gaps. -/
private noncomputable def blockGaps (d : ℕ) :
    LocalBlock d ≃ Equiv.Perm (Fin d) × (Fin (d + 1) → ℕ) where
  toFun p :=
    let τ := Tuple.sortDesc p.1.2
    (τ, fun j => blockRaw p τ j - blockBump τ j.val)
  invFun a := blockRebuild a.1 a.2
  left_inv p := by
    let τ := Tuple.sortDesc p.1.2
    let g (j : Fin (d + 1)) := blockRaw p τ j - blockBump τ j.val
    have hpad : blockPadded τ g = blockRaw p τ := by
      funext j
      exact Nat.add_sub_of_le (block_bump_le_raw p j)
    have hτ := Tuple.antitone_sortDesc p.1.2
    apply Subtype.ext
    apply Prod.ext
    · change blockSuffix (blockPadded τ g) 0 = p.1.1
      rw [hpad, block_suffix_raw p τ hτ 0 (Nat.zero_le _)]
      rfl
    · funext i
      change blockSuffix (blockPadded τ g) ((τ.symm i).val + 1) = p.1.2 i
      have hi := (τ.symm i).isLt
      rw [hpad, block_suffix_raw p τ hτ _ (by omega)]
      simp [blockLevel, hi]
  right_inv := by
    rintro ⟨τ, g⟩
    have hsort := block_sort_rebuild τ g
    apply Prod.ext
    · exact hsort
    · change (fun j => blockRaw (blockRebuild τ g) (Tuple.sortDesc (blockRebuild τ g).1.2) j -
          blockBump (Tuple.sortDesc (blockRebuild τ g).1.2) j.val) = g
      rw [hsort]
      funext j
      rw [blockRaw, block_level_rebuild, block_level_rebuild, block_suffix_step _ j]
      simp [blockPadded]

private theorem block_sum_bump {d : ℕ} (τ : Equiv.Perm (Fin d)) (w : ℕ → ℕ) :
    (∑ j : Fin (d + 1), w j.val * blockBump τ j.val) = ∑ j ∈ permDescentSet τ, w j := by
  have h : (Finset.univ.filter (fun j : Fin (d + 1) => j.val ∈ permDescentSet τ)).map
      Fin.valEmbedding = permDescentSet τ := by
    ext j
    constructor
    · rintro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
      exact (Finset.mem_filter.mp hi).2
    · intro hj
      have hlt := (block_descent_bounds hj).2
      exact Finset.mem_map.mpr ⟨⟨j, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩
  simp_rw [blockBump, mul_ite, mul_one, mul_zero]
  conv_rhs => rw [← h, Finset.sum_map, Finset.sum_filter]
  rfl

private theorem block_sum_suffix {d : ℕ} (r : Fin (d + 1) → ℕ) :
    (∑ i : Fin d, blockSuffix r (i.val + 1)) = ∑ j : Fin (d + 1), j.val * r j := by
  simp_rw [blockSuffix, Finset.sum_filter, Nat.succ_le_iff]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < j.val then r j else 0), ← Finset.sum_filter]
  have h : (Finset.range d).filter (· < j.val) = Finset.range j.val := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    have := j.isLt
    omega
  simp [h]

private theorem blockGaps_symm_upper {d : ℕ} (τ : Equiv.Perm (Fin d)) (g : Fin (d + 1) → ℕ) :
    let p := (blockGaps d).symm (τ, g)
    p.1.1 = permDes τ + ∑ j, g j := by
  change blockSuffix (blockPadded τ g) 0 = _
  simp only [block_suffix_zero, blockPadded, Finset.sum_add_distrib]
  have h := block_sum_bump τ (fun _ => 1)
  simpa [permDes] using congrArg (· + ∑ j, g j) h

private theorem blockGaps_symm_fold_sum {d : ℕ} (τ : Equiv.Perm (Fin d))
    (g : Fin (d + 1) → ℕ) :
    let p := (blockGaps d).symm (τ, g)
    (∑ i, p.1.2 i) = permMaj τ + ∑ j : Fin (d + 1), j.val * g j := by
  change (∑ i, blockSuffix (blockPadded τ g) ((τ.symm i).val + 1)) = _
  rw [τ.symm.sum_comp (fun i => blockSuffix (blockPadded τ g) (i.val + 1)), block_sum_suffix]
  simp only [blockPadded, Nat.mul_add, Finset.sum_add_distrib]
  simpa [permMaj] using congrArg (· + ∑ j : Fin (d + 1), j.val * g j)
    (block_sum_bump τ (fun j => j))

/-- A diamond as an array supported on its part positions. -/
private structure Diamond (d M : ℕ) where
  part : ℕ → ℕ
  outside : ∀ p, M * (d + 1) < p → part p = 0
  ordered : ∀ (k : Fin M) (f : Fin d),
    part (k.val * (d + 1)) ≤ part (k.val * (d + 1) + (f.val + 1)) ∧
      part (k.val * (d + 1) + (f.val + 1)) ≤ part ((k.val + 1) * (d + 1))

private theorem diamond_ext {d M : ℕ} {a b : Diamond d M} (h : ∀ p, a.part p = b.part p) :
    a = b := by
  cases a
  cases b
  cases funext h
  rfl

private theorem replicate_linkPos (d M k : ℕ) :
    diamondLinkPos (List.replicate M d) k = min k M * (d + 1) := by
  simp [diamondLinkPos, List.take_replicate]

private theorem replicate_size (d M : ℕ) :
    diamondSize (List.replicate M d) = M * (d + 1) + 1 := by
  simp [diamondSize, replicate_linkPos]

private theorem replicate_links (d M : ℕ) :
    diamondLinks (List.replicate M d) = (Finset.range (M + 1)).image (· * (d + 1)) := by
  unfold diamondLinks
  simp only [List.length_replicate]
  apply Finset.image_congr
  intro k hk
  rw [replicate_linkPos, min_eq_left (by simpa using (Finset.mem_range.mp hk : k < M + 1))]

private theorem replicate_ordered {d M : ℕ} (b : ℕ → ℕ) :
    (∀ k ∈ Finset.range (List.replicate M d).length,
      ∀ f ∈ Finset.Icc 1 ((List.replicate M d).getD k 0),
      b (diamondLinkPos (List.replicate M d) k) ≤ b (diamondLinkPos (List.replicate M d) k + f) ∧
        b (diamondLinkPos (List.replicate M d) k + f) ≤
          b (diamondLinkPos (List.replicate M d) (k + 1))) ↔
    ∀ (k : Fin M) (f : Fin d),
      b (k.val * (d + 1)) ≤ b (k.val * (d + 1) + (f.val + 1)) ∧
        b (k.val * (d + 1) + (f.val + 1)) ≤ b ((k.val + 1) * (d + 1)) := by
  simp only [List.length_replicate, Finset.mem_range, Finset.mem_Icc]
  have getD (k : ℕ) (hk : k < M) : (List.replicate M d).getD k 0 = d := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left hk]
    rfl
  constructor
  · intro h k f
    simpa only [replicate_linkPos, min_eq_left k.isLt.le, min_eq_left (Nat.succ_le_of_lt k.isLt)]
      using h k k.isLt (f.val + 1) (by rw [getD _ k.isLt]; exact ⟨by omega, f.isLt⟩)
  · intro h k hk f hf
    rw [getD _ hk] at hf
    simpa only [replicate_linkPos, min_eq_left hk.le, min_eq_left (Nat.succ_le_of_lt hk),
      show (f - 1) + 1 = f by omega] using h ⟨k, hk⟩ ⟨f - 1, by omega⟩

private def profilePrefix {M : ℕ} (h : Fin M → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, if hi : i < M then h ⟨i, hi⟩ else 0

private theorem profilePrefix_succ {M : ℕ} (h : Fin M → ℕ) (k : Fin M) :
    profilePrefix h (k.val + 1) = profilePrefix h k + h k := by
  simp [profilePrefix, Finset.sum_range_succ, k.isLt]

private def profileLink {d M : ℕ} (a : ℕ × (Fin M → LocalBlock d)) (k : ℕ) : ℕ :=
  a.1 + profilePrefix (fun i => (a.2 i).1.1) k

private theorem profileLink_succ {d M : ℕ} (a : ℕ × (Fin M → LocalBlock d)) (k : Fin M) :
    profileLink a (k.val + 1) = profileLink a k + (a.2 k).1.1 := by
  rw [profileLink, profilePrefix_succ, ← Nat.add_assoc, profileLink]

/-- A relative fold is added to its lower link. Quotient and remainder locate the part. -/
private def profilePart {d M : ℕ} (a : ℕ × (Fin M → LocalBlock d)) (p : ℕ) : ℕ :=
  if M * (d + 1) < p then 0 else
    let k := p / (d + 1)
    let f := p % (d + 1)
    if hf : f = 0 then profileLink a k else
      if hk : k < M then profileLink a k + (a.2 ⟨k, hk⟩).1.2
        ⟨f - 1, by
          have hlt : f < d + 1 := Nat.mod_lt p (Nat.succ_pos d)
          omega⟩ else 0

private theorem profilePart_link {d M : ℕ} (a : ℕ × (Fin M → LocalBlock d))
    (k : ℕ) (hk : k ≤ M) : profilePart a (k * (d + 1)) = profileLink a k := by
  simp [profilePart, (Nat.mul_le_mul_right (d + 1) hk).not_gt,
    Nat.mul_div_cancel k (Nat.succ_pos d)]

private theorem fold_pos_div_mod {d M : ℕ} (k : Fin M) (f : Fin d) :
    (k.val * (d + 1) + (f.val + 1)) / (d + 1) = k.val ∧
      (k.val * (d + 1) + (f.val + 1)) % (d + 1) = f.val + 1 := by
  have hf : f.val + 1 < d + 1 := Nat.succ_lt_succ f.isLt
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos d), Nat.div_eq_of_lt hf, zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hf]
  exact ⟨rfl, rfl⟩

private theorem fold_pos_lt {d M : ℕ} (k : Fin M) (f : Fin d) :
    k.val * (d + 1) + (f.val + 1) < M * (d + 1) + 1 := by
  have hh := Nat.mul_le_mul_right (d + 1) (Nat.succ_le_of_lt k.isLt)
  change (k.val + 1) * (d + 1) ≤ _ at hh
  rw [Nat.add_mul, one_mul] at hh
  have := f.isLt
  omega

private theorem profilePart_fold {d M : ℕ} (a : ℕ × (Fin M → LocalBlock d))
    (k : Fin M) (f : Fin d) :
    profilePart a (k.val * (d + 1) + (f.val + 1)) = profileLink a k + (a.2 k).1.2 f := by
  obtain ⟨hdiv, hmod⟩ := fold_pos_div_mod k f
  have hp := Nat.le_of_lt_succ (fold_pos_lt k f)
  simp [profilePart, hp.not_gt, hdiv, hmod, k.isLt]

private def profileDiamond {d M : ℕ} (a : ℕ × (Fin M → LocalBlock d)) : Diamond d M where
  part := profilePart a
  outside p hp := ite_eq_left hp
  ordered k f := by
    rw [profilePart_link a _ k.isLt.le, profilePart_link a _ k.isLt,
      profilePart_fold, profileLink_succ a k]
    exact ⟨Nat.le_add_right .., Nat.add_le_add_left ((a.2 k).2 f) _⟩

private theorem diamond_link_le {d M : ℕ} (hd : 1 ≤ d) (b : Diamond d M) (k : Fin M) :
    b.part (k.val * (d + 1)) ≤ b.part ((k.val + 1) * (d + 1)) :=
  ((b.ordered k ⟨0, hd⟩).1).trans (b.ordered k ⟨0, hd⟩).2

private def diamondProfile {d M : ℕ} (b : Diamond d M) : ℕ × (Fin M → LocalBlock d) :=
  (b.part 0, fun k => ⟨(b.part ((k.val + 1) * (d + 1)) - b.part (k.val * (d + 1)),
    fun f => b.part (k.val * (d + 1) + (f.val + 1)) - b.part (k.val * (d + 1))),
    fun f => Nat.sub_le_sub_right (b.ordered k f).2 _⟩)

private theorem profileDiamond_leftInverse {d M : ℕ} :
    Function.LeftInverse (@diamondProfile d M) (@profileDiamond d M) := by
  intro a
  apply Prod.ext
  · simp [diamondProfile, profileDiamond, profilePart, profileLink, profilePrefix]
  · funext k
    apply Subtype.ext
    apply Prod.ext
    · simp only [diamondProfile, profileDiamond]
      rw [profilePart_link a _ k.isLt, profilePart_link a _ k.isLt.le, profileLink_succ,
        Nat.add_sub_cancel_left]
    · funext f
      simp only [diamondProfile, profileDiamond]
      rw [profilePart_fold, profilePart_link a _ k.isLt.le, Nat.add_sub_cancel_left]

private theorem profileLink_diamondProfile {d M : ℕ} (hd : 1 ≤ d) (b : Diamond d M) :
    ∀ k ≤ M, profileLink (diamondProfile b) k = b.part (k * (d + 1)) := by
  intro k
  induction k with
  | zero => simp [diamondProfile, profileLink, profilePrefix]
  | succ k ih =>
    intro hk
    let k' : Fin M := ⟨k, by omega⟩
    rw [show k + 1 = k'.val + 1 from rfl, profileLink_succ (diamondProfile b) k', ih k'.isLt.le]
    exact Nat.add_sub_of_le (diamond_link_le hd b k')

private theorem profileDiamond_rightInverse {d M : ℕ} (hd : 1 ≤ d) :
    Function.RightInverse (@diamondProfile d M) (@profileDiamond d M) := by
  intro b
  apply diamond_ext
  intro p
  change profilePart (diamondProfile b) p = b.part p
  by_cases hp : M * (d + 1) < p
  · rw [b.outside p hp, profilePart, ite_eq_left hp]
  let k := p / (d + 1)
  let r := p % (d + 1)
  have hsplit : k * (d + 1) + r = p := by
    simpa [k, r, Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div p (d + 1)
  have hr : r < d + 1 := Nat.mod_lt _ (by omega)
  have hk : k ≤ M := by
    by_contra! h
    have hh := Nat.mul_le_mul_right (d + 1) (show M + 1 ≤ k by omega)
    rw [Nat.add_mul, one_mul] at hh
    omega
  by_cases hr0 : r = 0
  · rw [hr0, add_zero] at hsplit
    rw [← hsplit, profilePart_link _ _ hk, profileLink_diamondProfile hd b _ hk]
  · have hkM : k < M := by
      by_contra! h
      have he : k = M := by omega
      rw [he] at hsplit
      omega
    let k' : Fin M := ⟨k, hkM⟩
    let f : Fin d := ⟨r - 1, by omega⟩
    have hf : f.val + 1 = r := by dsimp [f]; omega
    rw [← hsplit, ← hf, profilePart_fold (k := k') (f := f),
      profileLink_diamondProfile hd b _ hk]
    exact Nat.add_sub_of_le (b.ordered k' f).1

/-- The initial link and each diamond measured from its lower link. -/
private def diamondProfileEquiv {d M : ℕ} (hd : 1 ≤ d) :
    Diamond d M ≃ ℕ × (Fin M → LocalBlock d) where
  toFun := diamondProfile
  invFun := profileDiamond
  left_inv := profileDiamond_rightInverse hd
  right_inv := profileDiamond_leftInverse

private noncomputable def degree (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

@[local simp] private theorem degree_zero (i j : ℕ) : degree i j 0 = i := by simp [degree]
@[local simp] private theorem degree_one (i j : ℕ) : degree i j 1 = j := by simp [degree]

private theorem degree_eq_iff {i j : ℕ} {e : Fin 2 →₀ ℕ} :
    degree i j = e ↔ i = e 0 ∧ j = e 1 := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (· 0) h, by simpa using congrArg (· 1) h⟩
  · rintro ⟨hi, hj⟩
    ext a
    fin_cases a <;> simp [hi, hj]

private noncomputable def diamondWeight {d M : ℕ} (b : Diamond d M) : Fin 2 →₀ ℕ :=
  let ds := List.replicate M d
  degree (∑ p ∈ (Finset.range (diamondSize ds)).filter (· ∉ diamondLinks ds), b.part p)
    (∑ p ∈ diamondLinks ds, b.part p)

private theorem diamondWeight_eq {d M : ℕ} (b : Diamond d M) (e : Fin 2 →₀ ℕ) :
    diamondWeight b = e ↔ IsMultifoldDiamond (List.replicate M d) (e 0) (e 1) b.part := by
  simp only [diamondWeight, degree_eq_iff, IsMultifoldDiamond, replicate_ordered, b.ordered,
    forall_true_iff, true_and]

private theorem part_le_weight {d M : ℕ} (b : Diamond d M) (e : Fin 2 →₀ ℕ)
    (hb : diamondWeight b = e) (p : ℕ) (hp : p < diamondSize (List.replicate M d)) :
    b.part p ≤ e 0 + e 1 := by
  have hw := (diamondWeight_eq b e).mp hb
  by_cases h : p ∈ diamondLinks (List.replicate M d)
  · have hl := Finset.single_le_sum (f := b.part) (fun i _ => Nat.zero_le (b.part i)) h
    rw [hw.2.2] at hl
    omega
  · have hm : p ∈ (Finset.range (diamondSize (List.replicate M d))).filter
        (· ∉ diamondLinks (List.replicate M d)) := by simp [hp, h]
    have hf := Finset.single_le_sum (f := b.part) (fun i _ => Nat.zero_le (b.part i)) hm
    rw [hw.2.1] at hf
    omega

/-- The coefficient fiber is the same finite set used by the bounded vector count. -/
private def boundedDiamondEquiv (d M : ℕ) (e : Fin 2 →₀ ℕ) :
    ↥((Finset.univ : Finset (Fin (diamondSize (List.replicate M d)) → Fin (e 0 + e 1 + 1))).filter
        (fun a => IsMultifoldDiamond (List.replicate M d) (e 0) (e 1) (diamondPart a))) ≃
      {b : Diamond d M // diamondWeight b = e} where
  toFun a := by
    have ha := (Finset.mem_filter.mp a.2).2
    exact ⟨⟨diamondPart a.1,
      fun p hp => dite_eq_right (by rw [replicate_size]; omega),
      (replicate_ordered _).mp ha.1⟩, (diamondWeight_eq ..).mpr ha⟩
  invFun b := by
    let a : Fin (diamondSize (List.replicate M d)) → Fin (e 0 + e 1 + 1) := fun p =>
      ⟨b.1.part p, Nat.lt_succ_of_le (part_le_weight b.1 e b.2 p p.isLt)⟩
    have ha : diamondPart a = b.1.part := by
      funext p
      by_cases hp : p < diamondSize (List.replicate M d)
      · exact dite_eq_left hp
      · rw [diamondPart, dite_eq_right hp, b.1.outside]
        rw [replicate_size] at hp
        omega
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha ▸ (diamondWeight_eq ..).mp b.2⟩⟩
  left_inv a := by
    apply Subtype.ext
    funext p
    apply Fin.ext
    exact dite_eq_left p.isLt
  right_inv b := by
    apply Subtype.ext
    apply diamond_ext
    intro p
    by_cases hp : p < diamondSize (List.replicate M d)
    · exact dite_eq_left hp
    · change diamondPart _ p = _
      rw [diamondPart, dite_eq_right hp, b.1.outside]
      rw [replicate_size] at hp
      omega

private theorem finite_diamondWeight (d M : ℕ) (e : Fin 2 →₀ ℕ) :
    Finite {b : Diamond d M // diamondWeight b = e} :=
  Finite.of_equiv _ (boundedDiamondEquiv d M e)

private theorem count_eq_card_fiber (d M : ℕ) (e : Fin 2 →₀ ℕ) :
    multifoldDiamondCount (List.replicate M d) (e 0) (e 1) =
      Nat.card {b : Diamond d M // diamondWeight b = e} := by
  rw [← Nat.card_congr (boundedDiamondEquiv d M e), Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

private theorem sum_fold_positions (d M : ℕ) (b : ℕ → ℕ) :
    ∑ p ∈ (Finset.range (diamondSize (List.replicate M d))).filter
      (· ∉ diamondLinks (List.replicate M d)), b p =
    ∑ k : Fin M, ∑ f : Fin d, b (k.val * (d + 1) + (f.val + 1)) := by
  rw [replicate_size, replicate_links, ← Finset.sum_product Finset.univ Finset.univ
    (fun a : Fin M × Fin d => b (a.1.val * (d + 1) + (a.2.val + 1))),
    Finset.univ_product_univ]
  symm
  apply Finset.sum_bij (fun (a : Fin M × Fin d) _ => a.1.val * (d + 1) + (a.2.val + 1))
  · intro a _
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (fold_pos_lt a.1 a.2), ?_⟩
    intro hm
    obtain ⟨k, _, he⟩ := Finset.mem_image.mp hm
    have h := congrArg (· % (d + 1)) he
    simp [(fold_pos_div_mod a.1 a.2).2] at h
  · intro a _ b _ he
    have hq := congrArg (· / (d + 1)) he
    have hr := congrArg (· % (d + 1)) he
    rw [(fold_pos_div_mod a.1 a.2).1, (fold_pos_div_mod b.1 b.2).1] at hq
    rw [(fold_pos_div_mod a.1 a.2).2, (fold_pos_div_mod b.1 b.2).2] at hr
    exact Prod.ext (Fin.ext hq) (Fin.ext (by omega))
  · intro p hp
    obtain ⟨hp, hlink⟩ := Finset.mem_filter.mp hp
    have hp' := Finset.mem_range.mp hp
    let k := p / (d + 1)
    let r := p % (d + 1)
    have hsplit : k * (d + 1) + r = p := by
      simpa [k, r, Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div p (d + 1)
    have hr : r < d + 1 := Nat.mod_lt _ (Nat.succ_pos d)
    have hk : k ≤ M := by
      by_contra! h
      have hh := Nat.mul_le_mul_right (d + 1) (show M + 1 ≤ k by omega)
      rw [Nat.add_mul, one_mul] at hh
      omega
    have hr0 : r ≠ 0 := by
      intro he
      rw [he, Nat.add_zero] at hsplit
      exact hlink (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), hsplit⟩)
    have hkM : k < M := by
      by_contra! h
      have he : k = M := by omega
      rw [he] at hsplit
      omega
    exact ⟨(⟨k, hkM⟩, ⟨r - 1, by omega⟩), Finset.mem_univ _, by
      change k * (d + 1) + (r - 1 + 1) = p
      rw [show r - 1 + 1 = r by omega, hsplit]⟩
  · intro a _
    rfl

private theorem sum_link_positions (d M : ℕ) (b : ℕ → ℕ) :
    ∑ p ∈ diamondLinks (List.replicate M d), b p =
      ∑ k ∈ Finset.range (M + 1), b (k * (d + 1)) := by
  rw [replicate_links, Finset.sum_image]
  intro p _ q _ h
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos d) h

/-- Summing initial segments gives each entry a multiplicity equal to the number of later links. -/
private theorem sum_range_prefix (h : ℕ → ℕ) (n : ℕ) :
    ∑ k ∈ Finset.range n, ∑ i ∈ Finset.range k, h i =
      ∑ i ∈ Finset.range n, (n - 1 - i) * h i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ (fun k => ∑ i ∈ Finset.range k, h i), ih,
      Finset.sum_range_succ (fun i => (n + 1 - 1 - i) * h i), ← Finset.sum_add_distrib]
    simp only [Nat.add_sub_cancel, Nat.sub_self, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    have hlt := Finset.mem_range.mp hi
    rw [show n - i = (n - 1 - i) + 1 by omega, Nat.add_mul, one_mul]

private theorem sum_profileLink {d M : ℕ} (a : ℕ × (Fin M → LocalBlock d))
    (n : ℕ) (hn : n = M ∨ n = M + 1) :
    ∑ k ∈ Finset.range n, profileLink a k =
      n * a.1 + ∑ k : Fin M, (n - 1 - k.val) * (a.2 k).1.1 := by
  simp only [profileLink, profilePrefix, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, sum_range_prefix]
  congr 1
  let g (k : ℕ) : ℕ := (n - 1 - k) * (if hk : k < M then (a.2 ⟨k, hk⟩).1.1 else 0)
  change (∑ i ∈ Finset.range n, g i) = ∑ k : Fin M, (n - 1 - k.val) * (a.2 k).1.1
  have hg : (∑ k : Fin M, g k) = ∑ k : Fin M, (n - 1 - k.val) * (a.2 k).1.1 := by
    simp [g]
  rw [← hg, Fin.sum_univ_eq_sum_range]
  rcases hn with he | he
  · rw [he]
  · rw [he, Finset.sum_range_succ]
    simp [g]

private noncomputable def baseWeight (d M t : ℕ) : Fin 2 →₀ ℕ := degree (M * d * t) ((M + 1) * t)

private noncomputable def blockWeight (n : ℕ) {d : ℕ} (a : LocalBlock d) : Fin 2 →₀ ℕ :=
  degree ((n - 1) * d * a.1.1 + ∑ f, a.1.2 f) (n * a.1.1)

private theorem diamondWeight_profile {d M : ℕ} (a : ℕ × (Fin M → LocalBlock d)) :
    diamondWeight (profileDiamond a) =
      baseWeight d M a.1 + ∑ k : Fin M, blockWeight (M - k.val) (a.2 k) := by
  apply Finsupp.ext
  intro c
  have hc : c = 0 ∨ c = 1 := by fin_cases c <;> decide
  rcases hc with rfl | rfl
  · simp only [diamondWeight, degree_zero, profileDiamond, baseWeight, blockWeight,
      Finsupp.add_apply, Finset.sum_apply', sum_fold_positions, profilePart_fold,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (profileLink a),
      sum_profileLink _ _ (Or.inl rfl), Nat.mul_add, Finset.mul_sum]
    have h : (∑ k : Fin M, d * ((M - 1 - k.val) * (a.2 k).1.1)) =
        ∑ k : Fin M, (M - k.val - 1) * d * (a.2 k).1.1 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [show M - 1 - k.val = M - k.val - 1 by omega]
      ring
    simp only [Nat.cast_id]
    rw [h]
    ring
  · simp only [diamondWeight, degree_one, profileDiamond, baseWeight, blockWeight,
      Finsupp.add_apply, Finset.sum_apply', sum_link_positions]
    have hlink (k : ℕ) (hk : k ∈ Finset.range (M + 1)) :=
      profilePart_link a k (by simpa using Finset.mem_range.mp hk)
    rw [Finset.sum_congr rfl hlink, sum_profileLink _ _ (Or.inr rfl)]
    simp

open MvPowerSeries

private theorem degree_nsmul (i j k : ℕ) : k • degree i j = degree (i * k) (j * k) := by
  apply Finsupp.ext
  intro c
  have hc : c = 0 ∨ c = 1 := by fin_cases c <;> decide
  rcases hc with rfl | rfl <;> simp [Finsupp.nsmul_apply, Nat.mul_comm]

private noncomputable def gapDegree (d n : ℕ) (j : Fin (d + 1)) : Fin 2 →₀ ℕ :=
  degree ((n - 1) * d + j.val) n

private noncomputable def permWeight (n : ℕ) {d : ℕ} (τ : Equiv.Perm (Fin d)) : Fin 2 →₀ ℕ :=
  degree ((n - 1) * d * permDes τ + permMaj τ) (n * permDes τ)

private theorem blockWeight_gaps {d : ℕ} (n : ℕ) (τ : Equiv.Perm (Fin d))
    (g : Fin (d + 1) → ℕ) :
    blockWeight n ((blockGaps d).symm (τ, g)) =
      permWeight n τ + ∑ j : Fin (d + 1), g j • gapDegree d n j := by
  apply Finsupp.ext
  intro c
  have hc : c = 0 ∨ c = 1 := by fin_cases c <;> decide
  rcases hc with rfl | rfl
  · simp only [blockWeight, degree_zero, blockGaps_symm_upper, blockGaps_symm_fold_sum,
      Finsupp.add_apply, permWeight, Finset.sum_apply', gapDegree, degree_nsmul]
    simp only [Nat.add_mul, Finset.sum_add_distrib, Nat.mul_add, Finset.mul_sum]
    ring
  · simp only [blockWeight, degree_one, blockGaps_symm_upper, Finsupp.add_apply, permWeight,
      Finset.sum_apply', gapDegree, degree_nsmul]
    rw [Nat.mul_add, Finset.mul_sum]

private theorem finite_blockWeight {d n : ℕ} (hn : 0 < n) :
    FiniteWeightFibers (@blockWeight n d) := by
  intro e
  have hH (x : {x : LocalBlock d // blockWeight n x = e}) : x.val.1.1 ≤ e 1 := by
    have he := congrArg (fun f : Fin 2 →₀ ℕ => f 1) x.property
    rw [blockWeight, degree_one] at he
    calc x.val.1.1 ≤ n * x.val.1.1 := by simpa using Nat.mul_le_mul_right x.val.1.1 hn
         _ = e 1 := he
  apply Finite.of_injective (fun x : {x : LocalBlock d // blockWeight n x = e} =>
    (⟨x.val.1.1, Nat.lt_succ_of_le (hH x)⟩, fun j =>
      ⟨x.val.1.2 j, Nat.lt_succ_of_le ((x.val.2 j).trans (hH x))⟩) :
      {x : LocalBlock d // blockWeight n x = e} → Fin (e 1 + 1) × (Fin d → Fin (e 1 + 1)))
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (congrArg (fun a => a.1.val) he)
    (funext fun j => congrArg (fun a => (a.2 j).val) he)

private theorem series_of_permWeight (d n : ℕ) :
    weightEnum (permWeight (d := d) n) = eulerMahonian (MvPowerSeries (Fin 2) ℤ) d
      (X 0 ^ ((n - 1) * d) * X 1 ^ n) (X 0) := by
  rw [weightEnum_fintype, eulerMahonian]
  apply Finset.sum_congr rfl
  intro τ _
  rw [monomial_eq_X_pow_mul]
  simp only [permWeight, degree_zero, degree_one, mul_pow, ← pow_mul, pow_add]
  ac_rfl

private theorem series_of_blockWeight (d n : ℕ) (hn : 0 < n) :
    weightEnum (blockWeight (d := d) n) = eulerMahonian (MvPowerSeries (Fin 2) ℤ) d
        (X 0 ^ ((n - 1) * d) * X 1 ^ n) (X 0) *
      ∏ j : Fin (d + 1), weightEnum (fun k : ℕ => k • gapDegree d n j) := by
  have he (j : Fin (d + 1)) : FiniteWeightFibers (fun k : ℕ => k • gapDegree d n j) :=
    finiteWeightFibers_nsmul _ (by simpa [gapDegree] using hn)
  rw [← series_of_permWeight d n, ← weightEnum_pi _ he,
    ← weightEnum_prod _ _ (fun _ => inferInstance) (finiteWeightFibers_pi _ he)]
  apply weightEnum_equiv (blockGaps d)
  intro p
  simpa using blockWeight_gaps n ((blockGaps d) p).1 ((blockGaps d) p).2

private theorem series_of_diamondWeight (d M : ℕ) (hd : 1 ≤ d) :
    multifoldDiamondSeries (List.replicate M d) =
      weightEnum (fun t : ℕ => t • degree (M * d) (M + 1)) *
        ∏ k : Fin M, weightEnum (blockWeight (d := d) (M - k.val)) := by
  have he (k : Fin M) : FiniteWeightFibers (blockWeight (d := d) (M - k.val)) :=
    finite_blockWeight (Nat.sub_pos_of_lt k.isLt)
  have hf : FiniteWeightFibers (baseWeight d M) := by
    change FiniteWeightFibers (fun n : ℕ => degree (M * d * n) ((M + 1) * n))
    simp_rw [← degree_nsmul]
    exact finiteWeightFibers_nsmul _ (by simp)
  have hseries : multifoldDiamondSeries (List.replicate M d) = weightEnum (@diamondWeight d M) := by
    ext e
    rw [coeff_weightEnum _ (finite_diamondWeight d M), ← count_eq_card_fiber]
    rfl
  rw [hseries, ← weightEnum_pi _ he]
  simp_rw [degree_nsmul]
  change weightEnum (@diamondWeight d M) = weightEnum (baseWeight d M) * _
  rw [← weightEnum_prod _ _ hf (finiteWeightFibers_pi _ he)]
  apply weightEnum_equiv (diamondProfileEquiv hd)
  intro b
  have h := diamondWeight_profile ((diamondProfileEquiv hd) b)
  rw [show profileDiamond ((diamondProfileEquiv hd) b) = b from
    profileDiamond_rightInverse hd b] at h
  exact h

private theorem gap_product (d n : ℕ) (hn : 1 ≤ n) :
    ∏ j : Fin (d + 1), (1 - monomial (gapDegree d n j) (1 : ℤ)) =
      ∏ j ∈ Finset.range (d + 1), (1 - X (0 : Fin 2) ^ (n * d - j) * X 1 ^ n) := by
  apply Finset.prod_bij (fun (j : Fin (d + 1)) _ => d - j.val)
  · intro j _
    exact Finset.mem_range.mpr (by omega)
  · intro i _ j _ he
    apply Fin.ext
    have := i.isLt
    have := j.isLt
    omega
  · intro j hj
    have h := Finset.mem_range.mp hj
    exact ⟨⟨d - j, by omega⟩, Finset.mem_univ _, by
      change d - (d - j) = j
      omega⟩
  · intro j _
    rw [monomial_eq_X_pow_mul]
    simp only [gapDegree, degree_zero, degree_one]
    have hh : n * d = (n - 1) * d + d := by
      conv_lhs => rw [show n = n - 1 + 1 by omega, Nat.add_mul, one_mul]
    rw [hh, show (n - 1) * d + d - (d - j.val) = (n - 1) * d + j.val by have := j.isLt; omega]

private theorem prod_fin_reverse {R : Type*} [CommMonoid R] (M : ℕ) (f : ℕ → R) :
    ∏ k : Fin M, f (M - k.val) = ∏ n ∈ Finset.Icc 1 M, f n := by
  apply Finset.prod_bij (fun (k : Fin M) _ => M - k.val)
  · intro k _
    exact Finset.mem_Icc.mpr ⟨Nat.sub_pos_of_lt k.isLt, Nat.sub_le ..⟩
  · intro k _ l _ h
    apply Fin.ext
    have := k.isLt
    have := l.isLt
    omega
  · intro n hn
    obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hn
    exact ⟨⟨M - n, by omega⟩, Finset.mem_univ _, by
      change M - (M - n) = n
      omega⟩
  · intro k _
    rfl

private theorem base_cancel (d M : ℕ) (hM : 1 ≤ M) :
    (1 - X (0 : Fin 2) ^ (M * d) * X 1 ^ (M + 1)) *
      weightEnum (fun t : ℕ => t • degree (M * d) (M + 1)) = 1 := by
  simpa only [monomial_eq_X_pow_mul, degree_zero, degree_one] using
    one_sub_monomial_mul_weightEnum_nsmul (degree (M * d) (M + 1))
      (by rw [degree_one]; exact (show 0 < M from hM).trans (Nat.lt_succ_self M))

private theorem block_cancel (d n : ℕ) (hn : 1 ≤ n) :
    (∏ j ∈ Finset.range (d + 1), (1 - X (0 : Fin 2) ^ (n * d - j) * X 1 ^ n)) *
      weightEnum (blockWeight (d := d) n) = eulerMahonian (MvPowerSeries (Fin 2) ℤ) d
        (X 0 ^ ((n - 1) * d) * X 1 ^ n) (X 0) := by
  rw [series_of_blockWeight d n hn, ← gap_product d n hn, mul_left_comm,
    ← Finset.prod_mul_distrib]
  have h (j : Fin (d + 1)) := one_sub_monomial_mul_weightEnum_nsmul (gapDegree d n j)
    (by rw [gapDegree, degree_one]; exact hn)
  simp only [h, Finset.prod_const_one, mul_one]

/-- **Product formula for equal-fold partition diamonds.** Let $d$ and $M$ be positive integers.
Let $\sigma_{d,M}(a, b)$ be the generating function of multifold partition diamonds of shape
$(d, \dots, d)$ ($M$ copies), where $a$ marks the fold sum and $b$ marks the link sum, and let
$E_d(x, y) = \sum_{\tau} x^{\mathrm{des}(\tau)} y^{\mathrm{maj}(\tau)}$ be the Euler–Mahonian
polynomial, summed over the permutations $\tau$ of $\{1, \dots, d\}$. Then the following
identity holds in $\mathbb{Z}[[a, b]]$:

$$\left(1 - a^{Md} b^{M+1}\right) \prod_{n=1}^{M} \prod_{j=0}^{d} \left(1 - a^{nd-j} b^{n}\right)
\cdot \sigma_{d,M}(a, b) = \prod_{n=1}^{M} E_d\left(a^{(n-1)d} b^{n}, a\right).$$

Equivalently, $\sigma_{d,M}(a, b)$ is the product of the $E_d(a^{(n-1)d} b^n, a)$ divided by
$(1 - a^{Md} b^{M+1}) \prod_{n=1}^{M} \prod_{j=0}^{d} (1 - a^{nd-j} b^n)$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Theorem 2 (`integers-2026-A13-thm-2`). -/
public theorem partitionDiamond_genFun (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) :
    (1 - MvPowerSeries.X 0 ^ (M * d) * MvPowerSeries.X 1 ^ (M + 1)) *
        (∏ n ∈ Finset.Icc 1 M, ∏ j ∈ Finset.range (d + 1),
          (1 - MvPowerSeries.X 0 ^ (n * d - j) * MvPowerSeries.X 1 ^ n)) *
        multifoldDiamondSeries (List.replicate M d) =
      ∏ n ∈ Finset.Icc 1 M, eulerMahonian (MvPowerSeries (Fin 2) ℤ) d
        (MvPowerSeries.X 0 ^ ((n - 1) * d) * MvPowerSeries.X 1 ^ n) (MvPowerSeries.X 0) := by
  let D (n : ℕ) : MvPowerSeries (Fin 2) ℤ :=
    ∏ j ∈ Finset.range (d + 1), (1 - MvPowerSeries.X 0 ^ (n * d - j) * MvPowerSeries.X 1 ^ n)
  let E (n : ℕ) : MvPowerSeries (Fin 2) ℤ :=
    eulerMahonian (MvPowerSeries (Fin 2) ℤ) d
      (MvPowerSeries.X 0 ^ ((n - 1) * d) * MvPowerSeries.X 1 ^ n) (MvPowerSeries.X 0)
  let S (n : ℕ) := weightEnum (blockWeight (d := d) n)
  let A : MvPowerSeries (Fin 2) ℤ := 1 - MvPowerSeries.X 0 ^ (M * d) * MvPowerSeries.X 1 ^ (M + 1)
  let B := weightEnum (fun t : ℕ => t • degree (M * d) (M + 1))
  change A * (∏ n ∈ Finset.Icc 1 M, D n) * multifoldDiamondSeries (List.replicate M d) =
    ∏ n ∈ Finset.Icc 1 M, E n
  rw [← prod_fin_reverse M D, ← prod_fin_reverse M E, series_of_diamondWeight d M hd]
  change A * (∏ k : Fin M, D (M - k.val)) * (B * ∏ k : Fin M, S (M - k.val)) =
    ∏ k : Fin M, E (M - k.val)
  calc
    _ = (A * B) * ∏ k : Fin M, D (M - k.val) * S (M - k.val) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      rw [show A * B = 1 from base_cancel d M hM, one_mul]
      exact Finset.prod_congr rfl fun k _ => block_cancel d (M - k.val) (Nat.sub_pos_of_lt k.isLt)

end

end MetaMathlibExt
