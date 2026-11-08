/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Closure

/-!
# Ordinary-client tests for context-free closure

Each closure operation is applied to concrete singleton languages over `ℕ`
from outside the defining namespace.
-/

public section

namespace Cslib.Language.ContextFreeClosureTests

open scoped Computability

theorem union_cf : (({[1]} + {[2, 2]}) : Language ℕ).IsContextFree :=
  IsContextFree.add (IsContextFree.singleton_word [1]) (IsContextFree.singleton_word [2, 2])

theorem concat_cf : (({[1]} * {[2, 2]}) : Language ℕ).IsContextFree :=
  IsContextFree.mul (IsContextFree.singleton_word [1]) (IsContextFree.singleton_word [2, 2])

theorem star_cf : (({[0, 1]} : Language ℕ)∗).IsContextFree :=
  IsContextFree.kstar (IsContextFree.singleton_word [0, 1])

theorem pow_cf : (({[7]} : Language ℕ) ^ 3).IsContextFree :=
  IsContextFree.pow (IsContextFree.singleton_word [7]) 3

theorem finite_cf :
    Language.IsContextFree (({[], [1], [2, 2]} : Set (List ℕ)) : Language ℕ) :=
  IsContextFree.of_finite (Set.toFinite _)

end Cslib.Language.ContextFreeClosureTests
