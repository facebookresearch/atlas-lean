/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Scheduling.SingleMachine.CompletionTime
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.WithBot

/-!
# Maximum lateness on a single machine

Jobs of a finite type `J`, all available at time `0`, are processed on one machine in the order
of a list, one after another without preemption or idle time
(`CSLibExt.Scheduling.SingleMachine.CompletionTime`). Job `j` has a due date `d j`, and its
lateness is its completion time minus `d j`, negative when the job finishes early. The maximum
lateness `maxLateness` of the objective `1 ‖ L_max` is the largest lateness over the jobs. It is
taken in `WithBot`, so that the maximum over no jobs is `⊥`, standing for `-∞`.

Processing times and due dates take values in any additive commutative group with a linear
order, so that integer, rational and real data are all covered.

## References

* D. Chakrabarty, *Lecture 5: Single Machine Environments (Maximum Lateness)*, Scheduling Theory
  CO 454 lecture notes, University of Waterloo, May 19, 2009.
-/

@[expose] public section

namespace Cslib.Scheduling.SingleMachine

variable {J R : Type*} [Fintype J] [DecidableEq J] [AddCommGroup R] [LinearOrder R]

/-- **Maximum lateness on a single machine.** Let finitely many jobs $j$ have processing times
$p_j$ and due dates $d_j$ in an additive commutative group with a linear order, such as
$\mathbb{Z}$ or $\mathbb{R}$. The maximum lateness of a list $\sigma$ of jobs is
$L_{\max} = \max_j (C_j - d_j)$ over all jobs $j$, where $C_j$ is the completion time of job $j$
when the machine processes the jobs of $\sigma$ one after another from time $0$. The lateness
$C_j - d_j$ is negative when job $j$ completes before its due date. The maximum is taken in
`WithBot`, so that it is `⊥`, standing for $-\infty$, when there are no jobs. -/
def maxLateness (p d : J → R) (σ : List J) : WithBot R :=
  Finset.univ.sup fun j => ((completionTime p σ j - d j : R) : WithBot R)

theorem le_maxLateness (p d : J → R) (σ : List J) (j : J) :
    ((completionTime p σ j - d j : R) : WithBot R) ≤ maxLateness p d σ :=
  Finset.le_sup (f := fun j => ((completionTime p σ j - d j : R) : WithBot R))
    (Finset.mem_univ j)

theorem maxLateness_le_iff {p d : J → R} {σ : List J} {L : WithBot R} :
    maxLateness p d σ ≤ L ↔ ∀ j, ((completionTime p σ j - d j : R) : WithBot R) ≤ L := by
  simp [maxLateness, Finset.sup_le_iff]

theorem maxLateness_of_isEmpty [IsEmpty J] (p d : J → R) (σ : List J) :
    maxLateness p d σ = ⊥ := by
  simp [maxLateness, Finset.univ_eq_empty]

end Cslib.Scheduling.SingleMachine
