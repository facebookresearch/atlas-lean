/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Engel expansion trajectories

Remainder trajectories and length functions for Engel expansions of rationals, after
Erdős–Shallit ("New bounds on the length of finite Pierce and Engel series").
For `1 ≤ a ≤ n`, the Engel trajectory starts at `a` and iterates `t ↦ (-n) % t`
until reaching `0`; its length is the length of the Engel expansion of `a / n`.
-/

@[expose] public section

namespace EngelExpansion

/-- **Negated remainder.** For natural numbers $n$ and $k$ with $k \ge 1$, the negated remainder
of $n$ modulo $k$ is the unique $u$ with $0 \le u < k$ and $u \equiv -n \pmod{k}$: it equals $0$
when $k$ divides $n$ and $k - (n \bmod k)$ otherwise. For $k = 0$ it is defined to be $0$. -/
def negRem (n k : ℕ) : ℕ :=
  (k - n % k) % k

theorem negRem_lt {n k : ℕ} (hk : k ≠ 0) : negRem n k < k := by
  simp only [negRem]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero hk)

/-- **Characterization of the negated remainder.** For natural numbers $n$, $k$ and $u$ with
$k \ne 0$, the negated remainder of $n$ modulo $k$ equals $u$ if and only if $u < k$ and $k$
divides $n + u$.

This is the natural-number form of $u \equiv -n \pmod{k}$. -/
theorem negRem_eq_iff {n k u : ℕ} (hk : k ≠ 0) :
    negRem n k = u ↔ u < k ∧ k ∣ n + u := by
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hr_lt : n % k < k := Nat.mod_lt n hkpos
  set r := n % k with hr_def
  simp only [negRem, hr_def.symm]
  constructor
  · intro h
    have huk : u < k := by
      rw [← h]
      exact Nat.mod_lt _ hkpos
    refine ⟨huk, ?_⟩
    rw [Nat.dvd_iff_mod_eq_zero]
    conv_lhs => rw [← h, Nat.add_mod, Nat.mod_mod, ← hr_def]
    by_cases hr0 : r = 0
    · rw [hr0]
      simp
    · have hkr : k - r < k := by omega
      rw [Nat.mod_eq_of_lt hkr]
      have hsum : r + (k - r) = k := by omega
      rw [hsum]
      exact Nat.mod_self k
  · rintro ⟨huk, hdvd⟩
    have hmod : (r + u) % k = 0 := by
      have h1 : (n + u) % k = 0 := Nat.mod_eq_zero_of_dvd hdvd
      rwa [Nat.add_mod, Nat.mod_eq_of_lt huk, ← hr_def] at h1
    have hdvd2 : k ∣ r + u := Nat.dvd_iff_mod_eq_zero.mpr hmod
    rcases hdvd2 with ⟨q, hq⟩
    have hlt : r + u < 2 * k := by omega
    have hq_le : q ≤ 1 := by
      by_contra hc
      have hc' : 1 < q := by omega
      have hle : k * 2 ≤ k * q := Nat.mul_le_mul_left k hc'
      omega
    have hq01 : q = 0 ∨ q = 1 := by omega
    rcases hq01 with rfl | rfl
    · rw [Nat.mul_zero] at hq
      have hr0 : r = 0 := by omega
      have hu0 : u = 0 := by omega
      rw [hr0, hu0]
      simp
    · have hrr : r = k - u := by omega
      rw [hrr, Nat.sub_sub_self (le_of_lt huk), Nat.mod_eq_of_lt huk]

/-- **Engel remainder trajectory.** For natural numbers $n$ and $a$, the Engel remainder
trajectory of $a$ with respect to $n$ is the sequence $t_0, t_1, t_2, \dots$ of natural
numbers with $t_0 = a$ and, for every $j \ge 0$, $t_{j+1} = 0$ if $t_j = 0$, while if
$t_j \ne 0$ then $t_{j+1}$ is the negated remainder of $n$ modulo $t_j$: the unique natural
number $u < t_j$ with $u \equiv -n \pmod{t_j}$. Once the trajectory reaches $0$ it stays there. -/
def traj (n a : ℕ) : ℕ → ℕ
  | 0 => a
  | j + 1 => if traj n a j = 0 then 0 else negRem n (traj n a j)

/-- **Initial term of the Engel trajectory.** For all natural numbers $n$ and $a$, the Engel
remainder trajectory of $a$ with respect to $n$ has value $a$ at step $0$. -/
theorem traj_zero (n a : ℕ) : traj n a 0 = a :=
  rfl

/-- **Zero is absorbing for the Engel trajectory.** Let $n$, $a$ and $j$ be natural numbers
and let $t_0, t_1, \dots$ be the Engel remainder trajectory of $a$ with respect to $n$. If
$t_j = 0$, then $t_{j+1} = 0$. -/
theorem traj_succ_of_eq_zero {n a j : ℕ} (h : traj n a j = 0) :
    traj n a (j + 1) = 0 := by
  simp only [traj, ite_eq_left h]

/-- **Step of the Engel trajectory at a nonzero term.** Let $n$, $a$ and $j$ be natural
numbers and let $t_0, t_1, \dots$ be the Engel remainder trajectory of $a$ with respect to
$n$. If $t_j \ne 0$, then $t_{j+1}$ is the negated remainder of $n$ modulo $t_j$: the unique
natural number $u < t_j$ with $u \equiv -n \pmod{t_j}$. -/
theorem traj_succ_of_ne_zero {n a j : ℕ} (h : traj n a j ≠ 0) :
    traj n a (j + 1) = negRem n (traj n a j) := by
  simp only [traj, ite_eq_right h]

/-- **First step of the Engel trajectory.** Let $n$ and $t$ be natural numbers with
$t \ne 0$. Then the Engel remainder trajectory of $t$ with respect to $n$ is, at step $1$,
the negated remainder of $n$ modulo $t$: the unique natural number $u < t$ with
$u \equiv -n \pmod{t}$. -/
theorem traj_one {n t : ℕ} (ht : t ≠ 0) : traj n t 1 = negRem n t := by
  have h01 : (1 : ℕ) = 0 + 1 := rfl
  have h0 : traj n t 0 ≠ 0 := by
    rw [traj_zero]
    exact ht
  rw [h01, traj_succ_of_ne_zero h0, traj_zero]

/-- **An Engel trajectory started at $a$ vanishes within $a + 1$ steps.** Let $n$ and $a$ be
natural numbers and let $t_0 = a, t_1, t_2, \dots$ be the Engel trajectory of $a$ with respect to
$n$. Then $t_i = 0$ for some $i \le a + 1$. -/
theorem exists_traj_eq_zero (n a : ℕ) : ∃ i ≤ a + 1, traj n a i = 0 := by
  have key : ∀ j, traj n a j ≤ a - j ∨ ∃ i ≤ j, traj n a i = 0 := by
    intro j
    induction j with
    | zero => exact Or.inl (by simp [traj])
    | succ j ih =>
        rcases ih with hle | ⟨i, hij, hi0⟩
        · by_cases hj0 : traj n a j = 0
          · exact Or.inr ⟨j, Nat.le_succ j, hj0⟩
          · have hlt : negRem n (traj n a j) < traj n a j :=
              negRem_lt hj0
            have hle2 : negRem n (traj n a j) ≤ a - (j + 1) := by
              revert hlt
              generalize negRem n (traj n a j) = m
              intro hlt
              omega
            have hstep : traj n a (j + 1) = negRem n (traj n a j) := by
              simp only [traj, ite_eq_right hj0]
            have hfin : traj n a (j + 1) ≤ a - (j + 1) := by
              rw [hstep]
              exact hle2
            exact Or.inl hfin
        · exact Or.inr ⟨i, le_trans hij (Nat.le_succ j), hi0⟩
  rcases key (a + 1) with hle | hex
  · have h0 : traj n a (a + 1) = 0 := by omega
    exact ⟨a + 1, le_refl _, h0⟩
  · exact hex

/-- **Engel trajectories vanish at a positive step.** Let $n$ and $a$ be natural numbers and let
$t_0 = a, t_1, t_2, \dots$ be the Engel trajectory of $a$ with respect to $n$. Then $t_j = 0$ for
some $j \ge 1$. -/
theorem exists_traj_eq_zero_pos (n a : ℕ) : ∃ j ≥ 1, traj n a j = 0 := by
  rcases exists_traj_eq_zero n a with ⟨i, _, hi0⟩
  refine ⟨i + 1, Nat.succ_le_succ (Nat.zero_le i), ?_⟩
  simp [traj, hi0]

/-- **Engel length.** For natural numbers $n$ and $a$, let $t_0 = a, t_1, t_2, \dots$ be the Engel
trajectory of $a$ with respect to $n$. The Engel length $L(n, a)$ is the least $j \ge 1$ with
$t_j = 0$.

For $1 \le a \le n$ this is the number of terms of the Engel expansion of $a / n$. -/
noncomputable def length (n a : ℕ) : ℕ :=
  Nat.find (exists_traj_eq_zero_pos n a)

/-- **The Engel length is positive.** For all natural numbers $n$ and $a$, the Engel length
$L(n, a)$ of $a$ with respect to $n$ satisfies $L(n, a) \ge 1$. -/
theorem length_pos (n a : ℕ) : 1 ≤ length n a :=
  (Nat.find_spec (exists_traj_eq_zero_pos n a)).1

/-- **Engel trajectory vanishes at the Engel length.** For all natural numbers $n$ and $a$,
let $L$ be the Engel length of $a$ with respect to $n$. Then the Engel remainder trajectory
of $a$ with respect to $n$ is $0$ at step $L$. -/
theorem traj_length_eq_zero (n a : ℕ) : traj n a (length n a) = 0 :=
  (Nat.find_spec (exists_traj_eq_zero_pos n a)).2

/-- **The Engel length is at most any positive vanishing step.** Let $n$, $a$ and $j$ be natural
numbers with $j \ge 1$, and let $t_0 = a, t_1, t_2, \dots$ be the Engel trajectory of $a$ with
respect to $n$. If $t_j = 0$, then the Engel length $L(n, a)$ satisfies $L(n, a) \le j$. -/
theorem length_le_of_traj_eq_zero {n a j : ℕ} (hj : 1 ≤ j)
    (h : traj n a j = 0) : length n a ≤ j :=
  Nat.find_min' _ ⟨hj, h⟩

/-- **Engel trajectory is nonzero at positive steps before the Engel length.** Let $n$, $a$
and $j$ be natural numbers and let $L$ be the Engel length of $a$ with respect to $n$. If
$1 \le j < L$, then the Engel remainder trajectory of $a$ with respect to $n$ is nonzero at
step $j$. -/
theorem traj_ne_zero_of_lt_length {n a j : ℕ} (hj : 1 ≤ j)
    (hlt : j < length n a) : traj n a j ≠ 0 := by
  have hneg := Nat.find_min _ hlt
  intro h0
  exact hneg ⟨hj, h0⟩

/-- **Maximal Engel length.** For a natural number $n$, the maximal Engel length is
$M(n) = \max_{1 \le a \le n} L(n, a)$, where $L(n, a)$ is the Engel length of $a$ with respect
to $n$; for $n = 0$ the maximum is over the empty set and $M(0) = 0$. -/
noncomputable def maxLength (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sup (length n)

/-- **Each Engel length is at most the maximal Engel length.** Let $n$ and $a$ be natural numbers
with $1 \le a \le n$. Then the Engel length $L(n, a)$ of $a$ with respect to $n$ is at most the
maximal Engel length $M(n) = \max_{1 \le b \le n} L(n, b)$. -/
theorem length_le_maxLength {n a : ℕ} (ha : a ∈ Finset.Icc 1 n) :
    length n a ≤ maxLength n :=
  Finset.le_sup ha

/-- **A uniform bound on Engel lengths bounds the maximal Engel length.** Let $n$ and $B$ be
natural numbers. If the Engel length $L(n, a)$ of $a$ with respect to $n$ satisfies
$L(n, a) \le B$ for every $a$ with $1 \le a \le n$, then the maximal Engel length
$M(n) = \max_{1 \le a \le n} L(n, a)$ (with $M(0) = 0$) satisfies $M(n) \le B$. -/
theorem maxLength_le_of_forall {n L : ℕ}
    (h : ∀ a ∈ Finset.Icc 1 n, length n a ≤ L) : maxLength n ≤ L :=
  Finset.sup_le h

end EngelExpansion
