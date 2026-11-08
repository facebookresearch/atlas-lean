/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Hom

/-!
# Ordinary-client tests for word-valued homomorphisms
-/

public section

namespace Cslib.Language.ContextFreeHomTests

/-- Expanding each Boolean letter to a two-letter code keeps a singleton
language context-free. -/
theorem hom_cf :
    Language.IsContextFree
      ((fun w => (w.map fun b => if b then [0, 1] else [1, 0]).flatten) ''
        ({[true, false]} : Language Bool)) :=
  IsContextFree.homImage (IsContextFree.singleton_word [true, false]) _

/-- The empty word expansion (erasing homomorphism) also applies. -/
theorem erase_cf :
    Language.IsContextFree
      ((fun w => (w.map fun _ : Bool => ([] : List ℕ)).flatten) ''
        ({[true]} : Language Bool)) :=
  IsContextFree.homImage (IsContextFree.singleton_word [true]) _

end Cslib.Language.ContextFreeHomTests
