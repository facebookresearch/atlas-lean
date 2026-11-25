/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

@[expose] public section

namespace MathlibExt.InformationTheory

/-- **Prefix-free code.** A code $c$ assigning to each source symbol a finite word over an
alphabet is prefix-free if for all distinct symbols $a_1 \ne a_2$ the word $c(a_1)$ is not a
prefix of $c(a_2)$. Since the condition covers all ordered pairs of distinct symbols, both
prefix directions are forbidden. -/
def IsPrefixFree {α β : Type*} (code : α → List β) : Prop :=
  ∀ ⦃a₁ a₂ : α⦄, a₁ ≠ a₂ → ¬ code a₁ <+: code a₂

/-- **Prefix-related codewords come from the same symbol.** If $c$ is a prefix-free code and the
codeword $c(a_1)$ is a prefix of $c(a_2)$, then $a_1 = a_2$. -/
theorem IsPrefixFree.eq_of_isPrefix {α β : Type*} {code : α → List β}
    (h : IsPrefixFree code) {a₁ a₂ : α} (hpre : code a₁ <+: code a₂) :
    a₁ = a₂ := by
  by_contra hne
  exact h hne hpre

/-- **Prefix-free codes are injective.** If $c$ is a prefix-free code and $c(a_1) = c(a_2)$,
then $a_1 = a_2$.

Equal codewords are mutually prefix, hence come from equal symbols. -/
theorem IsPrefixFree.injective {α β : Type*} {code : α → List β}
    (h : IsPrefixFree code) : Function.Injective code := by
  intro a₁ a₂ heq
  by_contra hne
  exact h hne ⟨[], by simp [heq]⟩

/-- **A prefix-free code with an empty codeword has one symbol.** If a prefix-free code $c$
assigns the empty word to a symbol $a_0$, then every symbol $a$ equals $a_0$.

This holds because the empty word is a prefix of every word. -/
theorem IsPrefixFree.eq_of_mem_nil {α β : Type*} {code : α → List β}
    (h : IsPrefixFree code) {a₀ : α} (ha₀ : code a₀ = []) (a : α) :
    a = a₀ := by
  by_contra hne
  apply h (fun heq => hne heq.symm) _
  rw [ha₀]
  exact ⟨_, rfl⟩

end MathlibExt.InformationTheory
