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
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Order.Filter.Cofinite

@[expose] public section

/-!
# Asymptotic additive bases

Ported from `FormalConjecturesForMathlib/Combinatorics/Additive/Basis.lean`
in google-deepmind/formal-conjectures (asymptotic-basis fragment only; the
source states the multiplicative version with `@[to_additive]`, here the
additive version is written directly).

## Main statements

- `Set.isAsymptoticAddBasisOfOrder_iff_sum`: the order-`n` asymptotic basis
  property, unfolded to an explicit `n`-term decomposition.
-/

open Filter
open scoped Pointwise

namespace Set

variable {M : Type*} [AddCommMonoid M]

/-- `A` is an asymptotic additive basis of order `n` if every sufficiently large
element is a sum of `n` elements of `A`. -/
def IsAsymptoticAddBasisOfOrder (A : Set M) (n : ℕ) : Prop :=
  ∀ᶠ a in cofinite, a ∈ n • A

/-- `A` is an exact additive basis of order `n` if every element is a sum of
`n` elements of `A`. -/
def IsAddBasisOfOrder (A : Set M) (n : ℕ) : Prop := ∀ a, a ∈ n • A

/-- `A` is an asymptotic additive basis (of some finite order). -/
def IsAsymptoticAddBasis (A : Set M) : Prop := ∃ n, A.IsAsymptoticAddBasisOfOrder n

/-- `A` is a weak additive basis of order `n` if every element is a sum of at
most `n` elements of `A`. -/
def IsWeakAddBasisOfOrder (A : Set M) (n : ℕ) : Prop := ∀ a, ∃ m ≤ n, a ∈ m • A

/-- A weak additive basis of some order. -/
def IsWeakAddBasis (A : Set M) : Prop := ∃ n, A.IsWeakAddBasisOfOrder n

/-- `A` is an asymptotic additive basis of order `n` exactly when a cofinite set
of `a : M` can be written as `a = a₁ + ... + aₙ` with every `aᵢ ∈ A`.

Ported from `isAsymptoticMulBasisOfOrder_iff_prod` of the same source file
(stated there multiplicatively with `@[to_additive]`). -/
lemma isAsymptoticAddBasisOfOrder_iff_sum {A : Set M} {n : ℕ} :
    IsAsymptoticAddBasisOfOrder A n ↔ ∀ᶠ a in cofinite, ∃ (f : Fin n → M) (_ : ∀ i, f i ∈ A),
      ∑ i, f i = a := by
  have := Set.mem_finsetSum (t := .univ) (f := fun _ : Fin n ↦ A)
  simp_all [IsAsymptoticAddBasisOfOrder]

end Set
