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

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Prod
public import MathlibExt.Combinatorics.Additive.RestrictedSignedSumset

@[expose] public section

/-!
# The restricted sumset `S +̂ S`

Ported from `FormalConjecturesForMathlib/Combinatorics/Additive/RestrictedSumset.lean`
in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures).
The definition is unchanged.

`Finset.restrictedSumset` is the binary restricted sumset. It agrees with
`MetaMathlibExt.restrictedSumset 2`, the `h`-fold restricted sumset already in
this library, by `Finset.restrictedSumset_eq_metaMathlibExt_two`; the binary
form is kept because it is the form in which the Green problem statements that
use it are posed, and because it needs only `[Add α]`.
-/

namespace Finset

variable {α : Type*} [Add α] [DecidableEq α]

/--
The restricted sumset of a finite set $S$, denoted $S \hat{+} S$, is the finite set
$\lbrace s_1 + s_2 : s_1, s_2 \in S, s_1 \neq s_2 \rbrace$ of sums of two distinct
elements of $S$.
-/
def restrictedSumset (S : Finset α) : Finset α :=
  S.offDiag.image (fun p => p.1 + p.2)

/-- Membership in the restricted sumset. -/
lemma mem_restrictedSumset {S : Finset α} {x : α} :
    x ∈ S.restrictedSumset ↔ ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a + b = x := by
  simp only [restrictedSumset, Finset.mem_image, Finset.mem_offDiag, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩
    exact ⟨a, ha, b, hb, hab, rfl⟩
  · rintro ⟨a, ha, b, hb, hab, rfl⟩
    exact ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩

end Finset

namespace Finset

variable {α : Type*} [AddCommMonoid α] [DecidableEq α]

/-- In an additive commutative monoid with decidable equality, the binary restricted sumset
is the `h = 2` case of the `h`-fold restricted sumset `MetaMathlibExt.restrictedSumset`. -/
lemma restrictedSumset_eq_metaMathlibExt_two (S : Finset α) :
    S.restrictedSumset = MetaMathlibExt.restrictedSumset 2 S := by
  ext x
  rw [mem_restrictedSumset, MetaMathlibExt.restrictedSumset, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, b, hb, hab, rfl⟩
    refine ⟨{a, b}, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact ha
        · exact hb, Finset.card_pair hab⟩
    · exact Finset.sum_pair hab
  · rintro ⟨B, hB, rfl⟩
    rw [Finset.mem_powersetCard] at hB
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hB.2
    exact ⟨a, hB.1 (by simp), b, hB.1 (by simp), hab,
      (Finset.sum_pair (f := fun x : α => x) hab).symm⟩

end Finset
