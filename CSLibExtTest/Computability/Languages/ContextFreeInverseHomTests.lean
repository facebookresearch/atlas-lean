/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.InverseHom

/-!
# Tests for closure under inverse homomorphisms

* Right letters of a word over `Bool ⊕ Bool`, and the grammar `insGrammar` instantiated.
* The preimage of the context-free language `{[true, true]}` under the doubling homomorphism
  `b ↦ [b, b]` is context-free, and contains `[true]` but not `[false]`.
* Blocks: the word built from `[true, false]` projects to its image and erases back.
* The same doubling as a free-monoid morphism: `preimage_wordMorphism` for
  `wordMorphismPreimage`, and `toList_wordMorphism_ofList` on a concrete word.
-/

@[expose] public section

namespace Cslib.Language.InverseHomTests

example : projRight ([.inl true, .inr false, .inl false, .inr true] : List (Bool ⊕ Bool)) =
    [false, true] := rfl

/-- The doubling homomorphism. -/
def double (b : Bool) : List Bool := [b, b]

example : Language.IsContextFree {w : List Bool | (w.map double).flatten ∈
    ({[true, true]} : Language Bool)} :=
  IsContextFree.preimage_hom (IsContextFree.singleton_word _) double

example : [true] ∈ {w : List Bool | (w.map double).flatten ∈ ({[true, true]} : Language Bool)} :=
  rfl

example : [false] ∉ {w : List Bool | (w.map double).flatten ∈ ({[true, true]} : Language Bool)} :=
  by simp [double]

example : Language.IsContextFree
    {u : List (Bool ⊕ Bool) | projRight u ∈ ({[true]} : Language Bool)} :=
  IsContextFree.preimage_projRight (IsContextFree.singleton_word _)

example : projRight (([true, false].map (block double)).flatten) = [true, true, false, false] :=
  projRight_flatten_block double _

example : ((([true, false].map (block double)).flatten).map eraseRight).flatten = [true, false] :=
  eraseRight_flatten_block double _

/-- Doubling as a free-monoid morphism. -/
def doubleMorphism : FreeMonoid Bool →* FreeMonoid Bool :=
  FreeMonoid.lift fun b => FreeMonoid.ofList [b, b]

example : (wordMorphismPreimage doubleMorphism ({[true, true]} : Language Bool)).IsContextFree :=
  IsContextFree.preimage_wordMorphism (IsContextFree.singleton_word _) doubleMorphism

example : FreeMonoid.toList (doubleMorphism (FreeMonoid.ofList [true, false])) =
    [true, true, false, false] := by
  rw [toList_wordMorphism_ofList]
  rfl

end Cslib.Language.InverseHomTests
