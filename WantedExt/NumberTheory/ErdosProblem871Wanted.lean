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

/-
# Erdős Problem 871
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic

@[expose] public section

open Filter

namespace MathlibExt.NumberTheory.ErdosProblem871Wanted

/-! Source record `FC-ErdosProblem871`, ported from FormalConjectures
`ErdosProblems/871.lean` and checked against erdosproblems.com/871.
Status: resolved false (Larsen; formalized in Lean). The historical
positive proposition is preserved as `conjecture`; its disproof is the
unregistered companion `disprovedForm`. -/

/-- **Erdős Problem 871 (splitting rich bases of order 2).** The statement that for every set $A$
of natural numbers such that every sufficiently large $n$ is $a + b$ with $a, b \in A$ and, for
every natural number $t$, every sufficiently large $n$ has at least $t$ representations
$n = a + b$ with $a, b \in A$ and $a \le b$, the set $A$ is the disjoint union of two sets $B$ and
$C$ such that every sufficiently large $n$ is $a + b$ with $a, b \in B$ and every sufficiently
large $n$ is $a + b$ with $a, b \in C$. -/
def conjecture : Prop :=
  ∀ (A : Set ℕ),
    (∀ᶠ n in Filter.atTop, ∃ a ∈ A, ∃ b ∈ A, a + b = n) ∧
    (∀ t, ∀ᶠ n in Filter.atTop, ∃ pairs : Finset (ℕ × ℕ),
      pairs.card ≥ t ∧
        ∀ p ∈ pairs, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2) →
    ∃ (B C : Set ℕ),
      (∀ x, x ∈ A ↔ x ∈ B ∨ x ∈ C) ∧
      Disjoint B C ∧
      (∀ᶠ n in Filter.atTop, ∃ a ∈ B, ∃ b ∈ B, a + b = n) ∧
      (∀ᶠ n in Filter.atTop, ∃ a ∈ C, ∃ b ∈ C, a + b = n)

/-- **Negation of the Erdős Problem 871 statement.** This is the proposition that there is a set
$A$ of natural numbers such that every sufficiently large $n$ is $a + b$ with $a, b \in A$ and,
for every natural number $t$, every sufficiently large $n$ has at least $t$ representations
$n = a + b$ with $a, b \in A$ and $a \le b$, but $A$ is not the disjoint union of two sets $B$
and $C$ such that every sufficiently large $n$ is $a + b$ with $a, b \in B$ and every
sufficiently large $n$ is $a + b$ with $a, b \in C$. -/
def disprovedForm : Prop := ¬ conjecture

/-- **Erdős Problem 871 is false (Larsen).** There is a set $A$ of natural numbers such that every
sufficiently large $n$ is $a + b$ with $a, b \in A$ and, for every natural number $t$, every
sufficiently large $n$ has at least $t$ representations $n = a + b$ with $a, b \in A$ and
$a \le b$, but $A$ is not the disjoint union of two sets $B$ and $C$ such that every sufficiently
large $n$ is $a + b$ with $a, b \in B$ and every sufficiently large $n$ is $a + b$ with
$a, b \in C$.

Source:
Larsen (formalized in Lean), per erdosproblems.com/871, https://www.erdosproblems.com/871; Lean
disproof of Erdos Problem 871 (Larsen with Claude Opus 4.5), plby/lean-proofs at commit
dfe2d78128b493c572cf525b1b8edf4897fb7664,
https://github.com/plby/lean-proofs/blob/dfe2d78128b493c572cf525b1b8edf4897fb7664/src/latest/ErdosProblems/Erdos871.lean#L2388.
Moved from `OpenConjectures/NumberTheory/ErdosProblem871`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.ErdosProblem871Wanted
