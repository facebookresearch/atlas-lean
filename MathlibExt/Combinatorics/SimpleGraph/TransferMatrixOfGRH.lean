/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Transfer matrices for relational graph sums

This file formalizes the transfer-matrix definition of Bautista-Ramos and
Guillén-Galván, *Fibonacci Numbers of Generalized Zykov Sums*:
<https://cs.uwaterloo.ca/journals/JIS/VOL15/Bautista/bautista4.tex>.

The source permits graphs with loops and notes that a loop prevents its vertex
from belonging to an independent set. Mathlib's `SimpleGraph` is irreflexive,
so the API below intentionally covers only the loopless specialization of the
source construction. It makes no claim about the source's looped-graph case.
-/

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

/-- **Zero indicator of a natural number.** For a natural number $z$, the zero indicator of $z$ is
the Boolean value that is true if $z = 0$ and false otherwise. -/
def zykovZeroIndicator (z : ℕ) : Bool :=
  decide (z = 0)

/-- **Characteristic vector of an independent set.** Let $G$ be a simple graph on a vertex type
$V$ and let $A$ be a finite independent set of $G$. The characteristic vector of $A$ is the
Boolean function on $V$ that sends a vertex $v$ to true if $v \in A$ and to false otherwise. -/
def independentSetCharacteristic {V : Type*} (G : SimpleGraph V) [DecidableEq V]
    (A : {s : Finset V // G.IsIndepSet (↑s : Set V)}) : V → Bool :=
  fun v => decide (v ∈ A.val)

/-- **Pairing of Boolean vectors along a relation.** Let $V$ and $W$ be finite types, let $R$ be a
relation between $V$ and $W$, and let $a$ and $b$ be Boolean functions on $V$ and on $W$. The
pairing of $a$ and $b$ along $R$ is the natural number of pairs $(v, w) \in V \times W$ such that
$R(v, w)$ holds and both $a(v)$ and $b(w)$ are true. -/
def relationPairing {V W : Type*} [Fintype V] [Fintype W]
    (R : V → W → Prop) [∀ v w, Decidable (R v w)]
    (a : V → Bool) (b : W → Bool) : ℕ :=
  ∑ v : V, ∑ w : W, if R v w then if a v && b w then 1 else 0 else 0

/-- **Transfer matrix of a generalized Zykov sum.** Let $G$ and $H$ be simple graphs on finite
vertex types $V$ and $W$, and let $R$ be a relation between $V$ and $W$. The transfer matrix of
$G$ and $H$ along $R$ is indexed by pairs $(A, B)$ where $A$ is a finite independent set of $G$
and $B$ is a finite independent set of $H$. Its entry at $(A, B)$ is the Boolean value that is
true exactly when the pairing along $R$ of the characteristic vectors of $A$ and $B$ is zero,
that is, when there are no $v \in A$ and $w \in B$ with $R(v, w)$.

Only the loopless case is covered: $G$ and $H$ are simple graphs, whereas the source construction
of Bautista-Ramos and Guillén-Galván also allows loops. -/
def zykovTransferMatrix {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (R : V → W → Prop) [∀ v w, Decidable (R v w)]
    (p : {s : Finset V // G.IsIndepSet (↑s : Set V)} ×
      {t : Finset W // H.IsIndepSet (↑t : Set W)}) : Bool :=
  zykovZeroIndicator
    (relationPairing R (independentSetCharacteristic G p.1) (independentSetCharacteristic H p.2))

end MetaMathlibExt
