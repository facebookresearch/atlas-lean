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

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Order.Filter.Cofinite

@[expose] public section

/-!
# Asymptotic additive bases

Ported from `FormalConjecturesForMathlib/Combinatorics/Additive/Basis.lean`
in google-deepmind/formal-conjectures (asymptotic-basis fragment only; the
source states the multiplicative version with `@[to_additive]`, here the
additive version is written directly).
-/

open Filter
open scoped Pointwise

namespace Set

variable {M : Type*} [AddCommMonoid M]

/-- **Asymptotic additive basis of order $n$.** Let $M$ be an additive commutative monoid,
$A \subseteq M$ and $n$ a natural number. $A$ is an asymptotic additive basis of order $n$ if all
but finitely many elements of $M$ are sums of exactly $n$ (not necessarily distinct) elements of
$A$, that is, $M \setminus nA$ is finite, where $nA = \{a_1 + \dots + a_n : a_1, \dots, a_n \in A\}$
and $0A = \{0\}$.

For $M = \mathbb{N}$ this means that every sufficiently large natural number is such a sum. -/
def IsAsymptoticAddBasisOfOrder (A : Set M) (n : ℕ) : Prop :=
  ∀ᶠ a in cofinite, a ∈ n • A

/-- **Exact additive basis of order $n$.** Let $M$ be an additive commutative monoid,
$A \subseteq M$ and $n$ a natural number. $A$ is an exact additive basis of order $n$ if every
element of $M$ is a sum of exactly $n$ (not necessarily distinct) elements of $A$, that is,
$M = nA$, where $nA = \{a_1 + \dots + a_n : a_1, \dots, a_n \in A\}$ and $0A = \{0\}$. -/
def IsAddBasisOfOrder (A : Set M) (n : ℕ) : Prop := ∀ a, a ∈ n • A

/-- **Asymptotic additive basis.** A subset $A$ of an additive commutative monoid $M$ is an
asymptotic additive basis if there is a natural number $n$ such that $A$ is an asymptotic additive
basis of order $n$, that is, all but finitely many elements of $M$ are sums of exactly $n$ (not
necessarily distinct) elements of $A$. -/
def IsAsymptoticAddBasis (A : Set M) : Prop := ∃ n, A.IsAsymptoticAddBasisOfOrder n

/-- **Weak additive basis of order $n$.** Let $M$ be an additive commutative monoid,
$A \subseteq M$ and $n$ a natural number. $A$ is a weak additive basis of order $n$ if every
element of $M$ is a sum of at most $n$ (not necessarily distinct) elements of $A$, that is, lies
in $mA$ for some $m \le n$, where $mA = \{a_1 + \dots + a_m : a_1, \dots, a_m \in A\}$ and
$0A = \{0\}$. -/
def IsWeakAddBasisOfOrder (A : Set M) (n : ℕ) : Prop := ∀ a, ∃ m ≤ n, a ∈ m • A

/-- **Weak additive basis.** A subset $A$ of an additive commutative monoid $M$ is a weak additive
basis if there is a natural number $n$ such that $A$ is a weak additive basis of order $n$, that
is, every element of $M$ is a sum of at most $n$ (not necessarily distinct) elements of $A$. -/
def IsWeakAddBasis (A : Set M) : Prop := ∃ n, A.IsWeakAddBasisOfOrder n

end Set
