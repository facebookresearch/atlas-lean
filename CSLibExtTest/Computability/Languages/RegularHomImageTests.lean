/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.RegularHomImage

/-!
# Tests for homomorphic images of regular languages

* `endsTrueDFA` accepts the words ending in `true`. Under `true ↦ [0, 0]`, `false ↦ []` (an
  erasing homomorphism, so the construction uses ε-moves), its image is regular and contains
  `[0, 0]` and `[0, 0, 0, 0]`.
* The ε-NFA of the construction accepts exactly the image (`HomImage.accepts_εnfa`).
-/

@[expose] public section

namespace Cslib.Language.RegularHomImageTests

/-- The last letter read; accepts the words ending in `true`. -/
def endsTrueDFA : DFA Bool Bool :=
  ⟨fun _ b => b, false, {true}⟩

/-- `true ↦ [0, 0]`, `false ↦ []`. -/
def double : Bool → List ℕ
  | true => [0, 0]
  | false => []

example : Language.IsRegular ((fun w => (w.map double).flatten) '' endsTrueDFA.accepts) :=
  IsRegular.homImage ⟨Bool, inferInstance, endsTrueDFA, rfl⟩ double

example : [0, 0] ∈ (fun w => (w.map double).flatten) '' endsTrueDFA.accepts :=
  ⟨[true], rfl, rfl⟩

example : [0, 0, 0, 0] ∈ (fun w => (w.map double).flatten) '' endsTrueDFA.accepts :=
  ⟨[true, false, true], rfl, rfl⟩

example : (HomImage.εnfa double endsTrueDFA).accepts =
    {y | ∃ w ∈ endsTrueDFA.accepts, (w.map double).flatten = y} :=
  HomImage.accepts_εnfa double endsTrueDFA

example {T T' : Type} [Finite T] {L : Language T} (hL : L.IsRegular) (φ : T → List T') :
    Language.IsRegular ((fun w => (w.map φ).flatten) '' L) :=
  IsRegular.homImage hL φ

end Cslib.Language.RegularHomImageTests
