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
# Pierce expansion trajectories

Remainder trajectories and length functions for Pierce expansions of rationals, after
Erdős–Shallit ("New bounds on the length of finite Pierce and Engel series").
For `1 ≤ a ≤ n`, the Pierce trajectory starts at `a` and iterates `t ↦ n % t`
until reaching `0`; its length is the length of the Pierce expansion of `a / n`.
-/

@[expose] public section

namespace PierceExpansion

/-- **Pierce remainder trajectory.** For natural numbers $n$ and $a$, the Pierce remainder
trajectory of $a$ with respect to $n$ is the sequence $t_0, t_1, t_2, \dots$ of natural numbers
with $t_0 = a$ and, for every $j \ge 0$, $t_{j+1} = 0$ if $t_j = 0$, while if $t_j \ne 0$ then
$t_{j+1} = n \bmod t_j$ is the remainder of $n$ modulo $t_j$. Once the trajectory reaches $0$ it
stays there. -/
def traj (n a : ℕ) : ℕ → ℕ
  | 0 => a
  | j + 1 => if traj n a j = 0 then 0 else n % traj n a j

/-- **Initial term of the Pierce trajectory.** For all natural numbers $n$ and $a$, the Pierce
remainder trajectory of $a$ with respect to $n$ has value $a$ at step $0$. -/
theorem traj_zero (n a : ℕ) : traj n a 0 = a :=
  rfl

/-- **Step of the Pierce trajectory at a zero term.** Let $n$, $a$ and $j$ be natural numbers and
let $t_0, t_1, \dots$ be the Pierce remainder trajectory of $a$ with respect to $n$. If $t_j = 0$,
then $t_{j+1} = 0$. -/
theorem traj_succ_of_eq_zero {n a j : ℕ} (h : traj n a j = 0) :
    traj n a (j + 1) = 0 := by
  simp only [traj, ite_eq_left h]

/-- **Step of the Pierce trajectory at a nonzero term.** Let $n$, $a$ and $j$ be natural numbers
and let $t_0, t_1, \dots$ be the Pierce remainder trajectory of $a$ with respect to $n$. If
$t_j \ne 0$, then $t_{j+1} = n \bmod t_j$, the remainder of $n$ modulo $t_j$. -/
theorem traj_succ_of_ne_zero {n a j : ℕ} (h : traj n a j ≠ 0) :
    traj n a (j + 1) = n % traj n a j := by
  simp only [traj, ite_eq_right h]

/-- **First step of the Pierce trajectory.** Let $n$ and $t$ be natural numbers with $t \ne 0$.
Then the Pierce remainder trajectory of $t$ with respect to $n$ is, at step $1$, equal to
$n \bmod t$, the remainder of $n$ modulo $t$. -/
theorem traj_one {n t : ℕ} (ht : t ≠ 0) : traj n t 1 = n % t := by
  have h01 : (1 : ℕ) = 0 + 1 := rfl
  have h0 : traj n t 0 ≠ 0 := by
    rw [traj_zero]
    exact ht
  rw [h01, traj_succ_of_ne_zero h0, traj_zero]

/-- **A bound on when a Pierce trajectory vanishes.** For natural numbers $n$ and $a$, let
$(t_j)_{j \ge 0}$ be the Pierce remainder trajectory: $t_0 = a$, and $t_{j+1} = n \bmod t_j$ if
$t_j \ne 0$, $t_{j+1} = 0$ if $t_j = 0$. Then $t_i = 0$ for some $i \le a + 1$. -/
theorem exists_traj_eq_zero (n a : ℕ) : ∃ i ≤ a + 1, traj n a i = 0 := by
  have key : ∀ j, traj n a j ≤ a - j ∨ ∃ i ≤ j, traj n a i = 0 := by
    intro j
    induction j with
    | zero => exact Or.inl (by simp [traj])
    | succ j ih =>
        rcases ih with hle | ⟨i, hij, hi0⟩
        · by_cases hj0 : traj n a j = 0
          · exact Or.inr ⟨j, Nat.le_succ j, hj0⟩
          · have hlt : n % traj n a j < traj n a j :=
              Nat.mod_lt n (Nat.pos_of_ne_zero hj0)
            have hle2 : n % traj n a j ≤ a - (j + 1) := by
              revert hlt
              generalize n % traj n a j = m
              intro hlt
              omega
            have hstep : traj n a (j + 1) = n % traj n a j := by
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

/-- **Pierce trajectories vanish at a positive step.** For all natural numbers $n$ and $a$, the
Pierce remainder trajectory $(t_j)_{j \ge 0}$ of $n$ and $a$ (with $t_0 = a$) satisfies $t_j = 0$
for some $j \ge 1$. -/
theorem exists_traj_eq_zero_pos (n a : ℕ) : ∃ j ≥ 1, traj n a j = 0 := by
  rcases exists_traj_eq_zero n a with ⟨i, _, hi0⟩
  refine ⟨i + 1, Nat.succ_le_succ (Nat.zero_le i), ?_⟩
  simp [traj, hi0]

/-- **Pierce length.** For natural numbers $n$ and $a$, let $(t_j)_{j \ge 0}$ be the Pierce
remainder trajectory, with $t_0 = a$, $t_{j+1} = n \bmod t_j$ if $t_j \ne 0$ and $t_{j+1} = 0$ if
$t_j = 0$. The Pierce length $\ell(n, a)$ is the least $j \ge 1$ with $t_j = 0$; such a $j$
always exists.

For $1 \le a \le n$ this is the length of the Pierce expansion of $a / n$. -/
noncomputable def length (n a : ℕ) : ℕ :=
  Nat.find (exists_traj_eq_zero_pos n a)

/-- **The Pierce length is positive.** For all natural numbers $n$ and $a$, the Pierce length
$\ell(n, a)$ satisfies $\ell(n, a) \ge 1$. -/
theorem length_pos (n a : ℕ) : 1 ≤ length n a :=
  (Nat.find_spec (exists_traj_eq_zero_pos n a)).1

/-- **The Pierce trajectory vanishes at the Pierce length.** For all natural numbers $n$ and $a$,
the Pierce remainder trajectory $(t_j)_{j \ge 0}$ of $n$ and $a$ satisfies $t_{\ell(n, a)} = 0$,
where $\ell(n, a)$ is the Pierce length. -/
theorem traj_length_eq_zero (n a : ℕ) : traj n a (length n a) = 0 :=
  (Nat.find_spec (exists_traj_eq_zero_pos n a)).2

/-- **The Pierce length is at most any positive vanishing step.** For natural numbers $n$, $a$ and
$j$ with $j \ge 1$, if the Pierce remainder trajectory $(t_i)_{i \ge 0}$ of $n$ and $a$ satisfies
$t_j = 0$, then the Pierce length $\ell(n, a)$ satisfies $\ell(n, a) \le j$. -/
theorem length_le_of_traj_eq_zero {n a j : ℕ} (hj : 1 ≤ j)
    (h : traj n a j = 0) : length n a ≤ j :=
  Nat.find_min' _ ⟨hj, h⟩

/-- **The Pierce trajectory is nonzero before the Pierce length.** For natural numbers $n$, $a$ and
$j$ with $1 \le j < \ell(n, a)$, where $\ell(n, a)$ is the Pierce length, the Pierce remainder
trajectory $(t_i)_{i \ge 0}$ of $n$ and $a$ satisfies $t_j \ne 0$. -/
theorem traj_ne_zero_of_lt_length {n a j : ℕ} (hj : 1 ≤ j)
    (hlt : j < length n a) : traj n a j ≠ 0 := by
  have hneg := Nat.find_min _ hlt
  intro h0
  exact hneg ⟨hj, h0⟩

/-- **Maximal Pierce length.** For a natural number $n$, the maximal Pierce length $P(n)$ is the
maximum of the Pierce lengths $\ell(n, a)$ over $1 \le a \le n$, with $P(0) = 0$. -/
noncomputable def maxLength (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sup (length n)

/-- **Each Pierce length is at most the maximal Pierce length.** For natural numbers $n$ and $a$
with $1 \le a \le n$, the Pierce length $\ell(n, a)$ satisfies $\ell(n, a) \le P(n)$, where
$P(n) = \max_{1 \le b \le n} \ell(n, b)$ is the maximal Pierce length. -/
theorem length_le_maxLength {n a : ℕ} (ha : a ∈ Finset.Icc 1 n) :
    length n a ≤ maxLength n :=
  Finset.le_sup ha

/-- **A uniform bound on Pierce lengths bounds the maximal Pierce length.** Let $n$ and $L$ be
natural numbers. If the Pierce length $\ell(n, a)$ satisfies $\ell(n, a) \le L$ for every $a$ with
$1 \le a \le n$, then the maximal Pierce length $P(n) = \max_{1 \le a \le n} \ell(n, a)$ (which is
$0$ when $n = 0$) satisfies $P(n) \le L$. -/
theorem maxLength_le_of_forall {n L : ℕ}
    (h : ∀ a ∈ Finset.Icc 1 n, length n a ≤ L) : maxLength n ≤ L :=
  Finset.sup_le h

end PierceExpansion
