/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 847
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Combinatorics.Additive.AP.Three.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem847Wanted

/-! Source record `FC-ErdosProblem847`, ported from FormalConjectures
`ErdosProblems/847.lean` and checked against erdosproblems.com/847.
`ThreeAPFree` is reused from `Mathlib.Combinatorics.Additive.AP.Three.Defs`.
The source proposition is preserved; its external disproof by
Reiher–Rödl–Sales [RRS24] and a pinned external Lean proof are recorded in the
registry. This module states the proposition but does not refute it. -/

/-- **Sets with uniformly large 3AP-free subsets.** A set $A$ of natural numbers has this property
if there is a real number $\varepsilon > 0$ such that every finite subset $B \subseteq A$ contains
a subset $C \subseteq B$ with $|C| \ge \varepsilon |B|$ that contains no nontrivial three-term
arithmetic progression, that is, no $a, b, c \in C$ with $a + c = 2b$ and $a \ne b$. -/
def HasFew3APs (A : Set ℕ) := ∃ (ε : ℝ), ε > 0 ∧
  ∀ (B : Set ℕ), B ⊆ A → Finite B →
  ∃ (C : Set ℕ), C ⊆ B ∧ C.ncard ≥ ε * B.ncard ∧ ThreeAPFree C

/-- **Erdős Problem 847.** Call a set of natural numbers 3AP-free if it contains no $a, b, c$ with
$a + c = 2b$ and $a \ne b$. The proposition asserts that every infinite set $A$ of natural numbers
such that, for some real number $\varepsilon > 0$, every finite subset $B \subseteq A$ has a
3AP-free subset of size at least $\varepsilon |B|$, is a finite union of 3AP-free sets: there are
a natural number $n$ and 3AP-free sets $S_0, \dots, S_{n-1}$ of natural numbers with
$A = S_0 \cup \dots \cup S_{n-1}$. -/
def conjecture : Prop :=
  ∀ (A : Set ℕ), Infinite A → HasFew3APs A →
    ∃ n, ∃ (S : Fin n → Set ℕ), (∀ i, ThreeAPFree (S i)) ∧ A = ⋃ i : Fin n, S i

/--
**Erdős Problem 847 is false.** Call a set of natural numbers 3AP-free if it contains no
$a, b, c$ with $a + c = 2b$ and $a \ne b$. There is an infinite set $A$ of natural numbers such
that, for some real number $\varepsilon > 0$, every finite subset $B \subseteq A$ has a 3AP-free
subset of size at least $\varepsilon |B|$, but $A$ is not the union of finitely many 3AP-free sets
of natural numbers.

Source: Christian Reiher, Vojtěch Rödl, and Marcelo
Sales, Colouring versus density in integers and Hales–Jewett cubes, Journal of the London
Mathematical Society (2024), e12987, https://doi.org/10.1112/jlms.12987. Moved from
`OpenConjectures/NumberTheory/ErdosProblem847`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.ErdosProblem847Wanted
