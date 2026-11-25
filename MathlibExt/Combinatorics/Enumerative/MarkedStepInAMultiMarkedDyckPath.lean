/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Steps of a multi-marked Dyck path.** A step of a multi-marked Dyck path is one of the
horizontal step $E = (1, 0)$, the plain vertical step $N = (0, 1)$, or, for an integer
$t \ge 2$, the marked vertical step $N^*_t = (0, 1)$ of index $t$. There are no marked steps
of index less than $2$.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`,
source statement `jis_54a13fcd4eb84116f24d6935`. -/
inductive MultiMarkedStep where
  | E : MultiMarkedStep
  | N : MultiMarkedStep
  | marked : (t : Nat) → 2 ≤ t → MultiMarkedStep

/-- **Number of horizontal steps in a multi-marked step sequence.** For a finite sequence $P$ of
multi-marked steps (horizontal steps $E$, plain vertical steps $N$ and marked vertical steps
$N^*_t$ with index $t \ge 2$), $E(P)$ is the number of horizontal steps $E$ in $P$.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`; source statement
`jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedCountE : List MultiMarkedStep → Nat
  | [] => 0
  | .E :: xs => multiMarkedCountE xs + 1
  | .N :: xs => multiMarkedCountE xs
  | .marked _ _ :: xs => multiMarkedCountE xs

/-- **Number of plain vertical steps.** For a finite sequence $P$ of multi-marked steps
(horizontal steps $E$, plain vertical steps $N$ and marked vertical steps $N^*_t$ with index
$t \ge 2$), $N(P)$ is the number of plain (unmarked) vertical steps $N$ in $P$.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`; source statement
`jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedCountPlainN : List MultiMarkedStep → Nat
  | [] => 0
  | .E :: xs => multiMarkedCountPlainN xs
  | .N :: xs => multiMarkedCountPlainN xs + 1
  | .marked _ _ :: xs => multiMarkedCountPlainN xs

/-- **Number of vertical steps.** For a finite sequence $P$ of multi-marked steps (horizontal
steps $E$, plain vertical steps $N$ and marked vertical steps $N^*_t$ with index $t \ge 2$),
this is the number of vertical steps in $P$, plain steps $N$ and marked steps $N^*_t$ counted
together.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`; source statement
`jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedCountVert : List MultiMarkedStep → Nat
  | [] => 0
  | .E :: xs => multiMarkedCountVert xs
  | .N :: xs => multiMarkedCountVert xs + 1
  | .marked _ _ :: xs => multiMarkedCountVert xs + 1

/-- **Number of steps.** For a finite sequence $P$ of multi-marked steps (horizontal steps $E$,
plain vertical steps $N$ and marked vertical steps $N^*_t$ with index $t \ge 2$), this is the
total number of steps in $P$, that is, the length of $P$.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`; source statement
`jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedCountTotal : List MultiMarkedStep → Nat
  | [] => 0
  | _ :: xs => multiMarkedCountTotal xs + 1

/-- **Index sum of a multi-marked step sequence.** For a finite sequence $s$ of steps of a
multi-marked Dyck path, the index sum of $s$ is the sum of the indices $t$ over all occurrences
of marked steps $N^*_t$ in $s$, each occurrence counted separately; the steps $E$ and $N$
contribute nothing.

Grouping the occurrences by index, the index sum equals $\sum_t t \cdot N^*_t(s)$, where
$N^*_t(s)$ is the number of marked steps of index $t$ in $s$.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`,
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedIndexSum : List MultiMarkedStep → Nat
  | [] => 0
  | .E :: xs => multiMarkedIndexSum xs
  | .N :: xs => multiMarkedIndexSum xs
  | .marked t _ :: xs => t + multiMarkedIndexSum xs

/-- **Shifted index sum of a multi-marked step sequence.** For a finite sequence $s$ of steps of
a multi-marked Dyck path, the shifted index sum of $s$ is the sum of $t - 1$ over all
occurrences of marked steps $N^*_t$ in $s$, each occurrence counted separately; the steps $E$
and $N$ contribute nothing.

Grouping the occurrences by index, the shifted index sum equals
$\sum_t (t - 1) \cdot N^*_t(s)$, where $N^*_t(s)$ is the number of marked steps of index $t$ in $s$.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`,
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedShiftedIndexSum : List MultiMarkedStep → Nat
  | [] => 0
  | .E :: xs => multiMarkedShiftedIndexSum xs
  | .N :: xs => multiMarkedShiftedIndexSum xs
  | .marked t _ :: xs => (t - 1) + multiMarkedShiftedIndexSum xs

/-- **Number of marked steps of a given index.** For a finite sequence $P$ of multi-marked steps
(horizontal steps $E$, plain vertical steps $N$ and marked vertical steps $N^*_s$ with index
$s \ge 2$) and a natural number $t$, $N^*_t(P)$ is the number of marked steps in $P$ whose index
is exactly $t$.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`; source statement
`jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedCountMarkedT : List MultiMarkedStep → Nat → Nat
  | [], _ => 0
  | .marked s _ :: xs, t => (if s == t then 1 else 0) + multiMarkedCountMarkedT xs t
  | _ :: xs, t => multiMarkedCountMarkedT xs t

/-- **Size of a multi-marked step sequence.** The size of a finite sequence $s$ of steps of a
multi-marked Dyck path is $E(s) + \sum (t - 1)$, where $E(s)$ is the number of horizontal steps
$E$ in $s$ and the sum runs over all occurrences of marked steps $N^*_t$ in $s$.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`,
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedSize (l : List MultiMarkedStep) : Nat :=
  multiMarkedCountE l + multiMarkedShiftedIndexSum l

/-- **Multi-marked Dyck path.** A multi-marked Dyck path is a finite sequence $P$ of steps, each
a horizontal step $E = (1,0)$, a plain vertical step $N = (0,1)$ or a marked vertical step
$N^*_t = (0,1)$ carrying an index $t \ge 2$, such that every prefix of $P$, including the empty
prefix and $P$ itself, has at most as many vertical steps (plain and marked) as horizontal
steps, and $P$ has exactly as many vertical steps as horizontal steps.

Read as a lattice path from $(0,0)$, $P$ never rises above the diagonal and ends on it.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`; source statement
`jis_54a13fcd4eb84116f24d6935`. -/
structure MultiMarkedDyckPath where
  steps : List MultiMarkedStep
  underdiagonal :
    ∀ k, k ≤ steps.length →
      multiMarkedCountVert (steps.take k) ≤ multiMarkedCountE (steps.take k)
  diagonal_endpoint : multiMarkedCountE steps = multiMarkedCountVert steps

/-- **Equal horizontal and vertical step counts.** For every multi-marked Dyck path $P$, the
number $E(P)$ of horizontal steps of $P$ equals the number of vertical steps of $P$, plain steps
$N$ and marked steps $N^*_t$ counted together.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`; source statement
`jis_54a13fcd4eb84116f24d6935`. -/
theorem multiMarkedCountEq (P : MultiMarkedDyckPath) :
    multiMarkedCountE P.steps = multiMarkedCountVert P.steps :=
  P.diagonal_endpoint

/-- **Vertical count plus shifted index sum.** For every finite sequence $s$ of steps of a
multi-marked Dyck path, the number of vertical steps of $s$ plus the shifted index sum of $s$
equals the number of plain vertical steps $N$ of $s$ plus the index sum of $s$.

Each marked step $N^*_t$ contributes $1 + (t - 1)$ to the left side and $t$ to the right side.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`,
source statement `jis_54a13fcd4eb84116f24d6935`. -/
theorem multiMarkedVertShifted_eq (l : List MultiMarkedStep) :
    multiMarkedCountVert l + multiMarkedShiftedIndexSum l =
      multiMarkedCountPlainN l + multiMarkedIndexSum l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | E =>
      simp only [multiMarkedCountVert, multiMarkedShiftedIndexSum,
        multiMarkedCountPlainN, multiMarkedIndexSum]
      exact ih
    | N =>
      simp only [multiMarkedCountVert, multiMarkedShiftedIndexSum,
        multiMarkedCountPlainN, multiMarkedIndexSum]
      omega
    | marked t h =>
      simp only [multiMarkedCountVert, multiMarkedShiftedIndexSum,
        multiMarkedCountPlainN, multiMarkedIndexSum]
      omega

/-- **Two expressions for the size of a multi-marked Dyck path.** For every multi-marked Dyck
path $P$, the size $E(P) + \sum (t - 1)$ of $P$ equals $N(P) + \sum t$, where $E(P)$ is the
number of horizontal steps $E$ of $P$, $N(P)$ is the number of plain vertical steps $N$ of $P$,
and both sums run over all occurrences of marked steps $N^*_t$ in $P$.

Grouped by index, this reads
$E(P) + \sum_t (t - 1) N^*_t(P) = N(P) + \sum_t t N^*_t(P)$, where $N^*_t(P)$ is the number of
marked steps of index $t$ in $P$.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`,
source statement `jis_54a13fcd4eb84116f24d6935`. -/
theorem multiMarkedSizeEq (P : MultiMarkedDyckPath) :
    multiMarkedSize P.steps =
      multiMarkedCountPlainN P.steps + multiMarkedIndexSum P.steps := by
  unfold multiMarkedSize
  have h := multiMarkedVertShifted_eq P.steps
  have he := multiMarkedCountEq P
  omega

/-- **Vertical steps of a multi-marked Dyck path.** A step of a multi-marked Dyck path is
vertical when it is the plain step $N$ or a marked step $N^*_t$; the horizontal step $E$ is not
vertical. This test delimits the final run of vertical steps of a step sequence.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`,
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedIsVert : MultiMarkedStep → Bool
  | .E => false
  | .N => true
  | .marked _ _ => true

/-- **Final run of vertical steps.** The final run of vertical steps of a finite sequence $s$
of steps of a multi-marked Dyck path is the longest suffix of $s$ consisting of vertical steps
($N$ or $N^*_t$): the part of $s$ after its last horizontal step $E$, or all of $s$ if $s$ has
no step $E$.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`,
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedTrailingVert (l : List MultiMarkedStep) : List MultiMarkedStep :=
  (l.reverse.takeWhile multiMarkedIsVert).reverse

/-- **Marked tail.** A multi-marked Dyck path $P$ has a marked tail when its final run of
vertical steps (the steps after its last horizontal step $E$, or all of $P$ if $P$ has no step
$E$) contains a marked vertical step $N^*_t$ for some index $t \ge 2$.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`; source statement
`jis_54a13fcd4eb84116f24d6935`. -/
def MultiMarkedDyckPath.HasMarkedTail (P : MultiMarkedDyckPath) : Prop :=
  ∃ (t : Nat) (h : 2 ≤ t),
    MultiMarkedStep.marked t h ∈ multiMarkedTrailingVert P.steps

/-- **Unmarked tail.** A multi-marked Dyck path $P$ has an unmarked tail when it does not
have a marked tail, that is, when its final run of vertical steps (the steps after its last
horizontal step $E$, or all of $P$ if $P$ has no step $E$) contains no marked vertical step.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`; source statement
`jis_54a13fcd4eb84116f24d6935`. -/
def MultiMarkedDyckPath.HasUnmarkedTail (P : MultiMarkedDyckPath) : Prop :=
  ¬ P.HasMarkedTail

/-- **Multi-marked Dyck paths of a given size.** For a natural number $n$, $\tilde P_n$ is the
set of multi-marked Dyck paths $P$ of size $n$. Here the size of $P$ is $E(P) + \sum (t - 1)$,
where $E(P)$ is the number of horizontal steps of $P$ and the sum runs over the marked steps
$N^*_t$ of $P$, each occurrence counted separately.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`; source statement
`jis_54a13fcd4eb84116f24d6935`. -/
def MultiMarkedDyckPathOfSize (n : Nat) : Type :=
  { P : MultiMarkedDyckPath // multiMarkedSize P.steps = n }

/-- **Multi-marked Dyck paths with an unmarked tail.** For a natural number $n$, $\tilde R_n$ is
the set of multi-marked Dyck paths of size $n$ with an unmarked tail, that is, whose final
run of vertical steps contains no marked step.

Source: concept `jis_sem_ee7327c841ed4326952fd4fb`,
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def MultiMarkedUnmarkedTail (n : Nat) : Type :=
  { P : MultiMarkedDyckPath //
    multiMarkedSize P.steps = n ∧ P.HasUnmarkedTail }

end

end MetaMathlibExt
