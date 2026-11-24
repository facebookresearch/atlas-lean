/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Cycle lengths and circumference

Ported from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Circumference.lean`
in google-deepmind/formal-conjectures (cycle-length fragment only).
-/

namespace SimpleGraph

/-- **Cycle lengths.** For a simple graph $G$, the set of cycle lengths of $G$ is the set of
natural numbers $m$ such that $G$ contains a cycle of length $m$. -/
def cycleLengths {α : Type*} (G : SimpleGraph α) : Set ℕ :=
  {m | ∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ w.length = m}

@[simp] theorem mem_cycleLengths {α : Type*} {G : SimpleGraph α} {m : ℕ} :
    m ∈ G.cycleLengths ↔ ∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ w.length = m :=
  Iff.rfl

/-- **Odd cycle lengths.** For a simple graph $G$, the set of odd cycle lengths of $G$ is the set
of those cycle lengths of $G$ that are odd, that is, the odd natural numbers $m$ such that $G$
contains a cycle of length $m$. -/
def oddCycleLengths {α : Type*} (G : SimpleGraph α) : Set ℕ :=
  {m ∈ G.cycleLengths | Odd m}

@[simp] theorem mem_oddCycleLengths {α : Type*} {G : SimpleGraph α} {m : ℕ} :
    m ∈ G.oddCycleLengths ↔ m ∈ G.cycleLengths ∧ Odd m :=
  Iff.rfl

end SimpleGraph
