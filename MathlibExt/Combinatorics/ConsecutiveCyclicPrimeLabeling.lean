/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.GCD.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Cyclic labeling of the ladder perimeter.** Let $n$ and $s$ be natural numbers. Number the
vertices of the ladder $P_n \times P_2$ along its perimeter by $0, 1, \dots, 2n - 1$, with $v_k$ at
position $k - 1$ and $u_k$ at position $2n - k$ for $1 \le k \le n$. The cyclic label with offset
$s$ of the position $i \in \{0, \dots, 2n - 1\}$ is $((i + s) \bmod 2n) + 1$.

Following Mbirika et al., JIS Vol. 19, the ladder has horizontal adjacency within each row and
vertical adjacency between $v_k$ and $u_k$. -/
def cyclicLabel (n : ℕ) (offset : ℕ) (i : Fin (2 * n)) : ℕ :=
  ((i.val + offset) % (2 * n)) + 1

/-- **Adjacency in the ladder graph.** Number the vertices of the ladder $P_n \times P_2$ along
its perimeter by $0, 1, \dots, 2n-1$, with $v_k$ at position $k - 1$ and $u_k$ at position
$2n - k$ for $1 \le k \le n$. Two positions $i, j \in \{0, \dots, 2n-1\}$ are adjacent when
$j \equiv i + 1 \pmod{2n}$ or $i \equiv j + 1 \pmod{2n}$ (neighbours along the perimeter
cycle), or when $i + j = 2n - 1$ (the rung joining $v_k$ and $u_k$).

The two end rungs $v_1 u_1$ and $v_n u_n$ are also perimeter edges. -/
def LadderAdj (n : ℕ) (i j : Fin (2 * n)) : Prop :=
  (((i.val + 1) % (2 * n) = j.val ∨ (j.val + 1) % (2 * n) = i.val) ∨
    i.val + j.val = 2 * n - 1)

instance decidableLadderAdj (n : ℕ) (i j : Fin (2 * n)) :
    Decidable (LadderAdj n i j) := by
  unfold LadderAdj
  infer_instance

/-- **Consecutive cyclic prime labeling of the ladder.** Let $n$ and $s$ be natural numbers.
Number the vertices of the ladder $P_n \times P_2$ along its perimeter by $0, 1, \dots, 2n - 1$,
with $v_k$ at position $k - 1$ and $u_k$ at position $2n - k$ for $1 \le k \le n$. The offset $s$
gives a consecutive cyclic prime labeling of the ladder when $n > 0$ and, for all positions
$i, j \in \{0, \dots, 2n - 1\}$ that are adjacent in the ladder graph, the cyclic labels of $i$
and $j$ with offset $s$ are relatively prime.

The cyclic labels place $1, \dots, 2n$ consecutively along the perimeter order: if $1$ is on $v_k$
the order runs $v_k, \dots, v_n, u_n, \dots, u_1, v_1, \dots, v_{k - 1}$ (and analogously from
$u_k$). -/
def IsConsecutiveCyclicPrimeLabeling (n offset : ℕ) : Prop :=
  0 < n ∧
    ∀ i j : Fin (2 * n),
      LadderAdj n i j → Nat.Coprime (cyclicLabel n offset i) (cyclicLabel n offset j)

instance decidableIsConsecutiveCyclicPrimeLabeling (n offset : ℕ) :
    Decidable (IsConsecutiveCyclicPrimeLabeling n offset) := by
  unfold IsConsecutiveCyclicPrimeLabeling LadderAdj Nat.Coprime
  infer_instance

/-- **Cyclic labels are positive.** For all natural numbers $n$ and $s$ and every position
$i \in \{0, \dots, 2n-1\}$, the cyclic label of $i$ with offset $s$ is at least $1$. -/
theorem cyclicLabel_pos (n offset : ℕ) (i : Fin (2 * n)) :
    1 ≤ cyclicLabel n offset i := by
  unfold cyclicLabel
  exact Nat.succ_pos _

/-- **Cyclic labels do not exceed the number of vertices.** For all natural numbers $n > 0$ and
$s$ and every position $i \in \{0, \dots, 2n-1\}$, the cyclic label of $i$ with offset $s$ is at
most $2n$. -/
theorem cyclicLabel_le_size (n offset : ℕ) (hn : 0 < n) (i : Fin (2 * n)) :
    cyclicLabel n offset i ≤ 2 * n := by
  unfold cyclicLabel
  have hpos : 0 < 2 * n := Nat.mul_pos (by decide) hn
  have hmod := Nat.mod_lt (i.val + offset) hpos
  exact Nat.succ_le_of_lt hmod

/-- **Range of the cyclic labels.** For all natural numbers $n > 0$ and $s$ and every position
$i \in \{0, \dots, 2n-1\}$, the cyclic label $c$ of $i$ with offset $s$ satisfies
$1 \le c \le 2n$. -/
theorem cyclicLabel_mem_range (n offset : ℕ) (hn : 0 < n) (i : Fin (2 * n)) :
    1 ≤ cyclicLabel n offset i ∧ cyclicLabel n offset i ≤ 2 * n :=
  ⟨cyclicLabel_pos n offset i, cyclicLabel_le_size n offset hn i⟩

/-- **The cyclic label of the first position with offset zero.** Let $n > 0$ be a natural number
and number the vertices of the ladder $P_n \times P_2$ along its perimeter by $0, 1, \dots, 2n - 1$,
with $v_k$ at position $k - 1$ and $u_k$ at position $2n - k$ for $1 \le k \le n$. Then the cyclic
label with offset $0$ of the position $0$ (the vertex $v_1$) is $1$. -/
theorem cyclicLabel_zero_offset_zero (n : ℕ) (hn : 0 < n) :
    cyclicLabel n 0 ⟨0, Nat.mul_pos (by decide) hn⟩ = 1 := by
  unfold cyclicLabel
  simp

end

end MetaMathlibExt
