/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# Marked step in a marked Dyck path

Formalizes the required clauses for the concept "marked step in a marked Dyck
path" (alias: N* step): in a marked Dyck path `P`, a marked step is a vertical
step of kind `N*` (as opposed to kind `N`); with `E(P)`, `N(P)`, `N*(P)` the
numbers of `E`, `N` and `N*` steps, the size of `P` is
`N*(P) + E(P) = N(P) + 2 * N*(P)`.

Source: Sergi Elizalde, *Patterns in Inversion Sequences II*:
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Elizalde/eli14.tex>.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Steps of a marked Dyck path.** A step of a marked Dyck path is one of three kinds: a
horizontal step $E = (1, 0)$, an unmarked vertical step $N = (0, 1)$, or a marked vertical step
$N^* = (0, 1)$.

Source: statement `jis_f51c1ff9625da95f812ce507`;
concept `jis_sem_1ec0710af356bb3047cb9588`. -/
inductive MarkedDyckStep : Type where
  | E : MarkedDyckStep
  | N : MarkedDyckStep
  | Nstar : MarkedDyckStep

/-- **Number of horizontal steps in a marked Dyck step sequence.** For a finite sequence $P$ of
marked Dyck steps, $E(P)$ is the number of horizontal steps $E$ in $P$.

Source: statement `jis_f51c1ff9625da95f812ce507`;
concept `jis_sem_1ec0710af356bb3047cb9588`. -/
def markedDyckCountE : List MarkedDyckStep → Nat
  | [] => 0
  | .E :: t => markedDyckCountE t + 1
  | _ :: t => markedDyckCountE t

/-- **Number of unmarked vertical steps.** For a finite sequence $P$ of marked Dyck steps,
$N(P)$ is the number of unmarked vertical steps $N$ in $P$.

Source: statement `jis_f51c1ff9625da95f812ce507`;
concept `jis_sem_1ec0710af356bb3047cb9588`. -/
def markedDyckCountN : List MarkedDyckStep → Nat
  | [] => 0
  | .N :: t => markedDyckCountN t + 1
  | _ :: t => markedDyckCountN t

/-- **Number of marked vertical steps.** For a finite sequence $P$ of marked Dyck steps,
$N^*(P)$ is the number of marked vertical steps $N^*$ in $P$.

Source: statement `jis_f51c1ff9625da95f812ce507`;
concept `jis_sem_1ec0710af356bb3047cb9588`. -/
def markedDyckCountNstar : List MarkedDyckStep → Nat
  | [] => 0
  | .Nstar :: t => markedDyckCountNstar t + 1
  | _ :: t => markedDyckCountNstar t

/-- **Marked Dyck path.** Let $E(Q)$, $N(Q)$ and $N^*(Q)$ denote the numbers of horizontal steps
$E$, unmarked vertical steps $N$ and marked vertical steps $N^*$ in a finite sequence $Q$ of
marked Dyck steps. A marked Dyck path is a finite sequence $P$ of marked Dyck steps such that
$E(P) = N(P) + N^*(P)$ and every prefix $Q$ of $P$ satisfies $N(Q) + N^*(Q) \le E(Q)$: a
lattice path from $(0, 0)$ that ends on the diagonal and never goes above it.

Source: statement `jis_f51c1ff9625da95f812ce507`;
concept `jis_sem_1ec0710af356bb3047cb9588`. -/
structure MarkedDyckPath : Type where
  steps : List MarkedDyckStep
  balanced : markedDyckCountE steps = markedDyckCountN steps + markedDyckCountNstar steps
  staysUnder : ∀ n, markedDyckCountN (steps.take n) + markedDyckCountNstar (steps.take n) ≤
    markedDyckCountE (steps.take n)

/-- **Marked step of a marked Dyck path.** Let $P$ be a marked Dyck path with $\ell$ steps. For a
position $i$ with $0 \le i < \ell$, the step of $P$ at position $i$ is marked when it is the
marked vertical step $N^*$ (rather than an unmarked vertical step $N$ or a horizontal step $E$).

Source: statement `jis_f51c1ff9625da95f812ce507`;
concept `jis_sem_1ec0710af356bb3047cb9588`. -/
def IsMarkedStep (P : MarkedDyckPath) (i : Fin P.steps.length) : Prop :=
  P.steps.get i = MarkedDyckStep.Nstar

/-- **Size of a marked Dyck path.** The size of a marked Dyck path $P$ is $N^*(P) + E(P)$,
where $N^*(P)$ is the number of marked vertical steps of $P$ and $E(P)$ the number of its
horizontal steps.

Source: statement `jis_f51c1ff9625da95f812ce507`;
concept `jis_sem_1ec0710af356bb3047cb9588`. -/
def MarkedDyckPath.pathSize (P : MarkedDyckPath) : Nat :=
  markedDyckCountNstar P.steps + markedDyckCountE P.steps

/-- **Size of a marked Dyck path in vertical steps.** For every marked Dyck path $P$, the size of
$P$ equals $N(P) + 2N^*(P)$, where $N(P)$ and $N^*(P)$ are the numbers of unmarked and marked
vertical steps of $P$.

Source: statement `jis_f51c1ff9625da95f812ce507`;
concept `jis_sem_1ec0710af356bb3047cb9588`. -/
theorem MarkedDyckPath.size_eq (P : MarkedDyckPath) :
    P.pathSize = markedDyckCountN P.steps + 2 * markedDyckCountNstar P.steps := by
  unfold MarkedDyckPath.pathSize
  have h := P.balanced
  omega

end

end MetaMathlibExt
