/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.InterRegular
public import CSLibExt.Computability.Languages.Finite

/-!
# Ordinary-client tests for intersection with regular languages

Both entry points are applied from outside the defining namespace. The
first example is over the infinite alphabet `ℕ`: intersecting with a
regular language needs no finite-alphabet assumption.
-/

public section

namespace Cslib.Language.ContextFreeInterRegularTests

/-- Intersecting a singleton CFL with a singleton regular language over an
infinite alphabet. -/
theorem inf_singleton_cf :
    (({[1, 2]} : Language ℕ) ⊓ {[1, 2]}).IsContextFree :=
  IsContextFree.inf_isRegular
    (IsContextFree.singleton_word [1, 2]) (IsRegular.singleton_word [1, 2])

/-- The one-state DFA over `Bool` accepting every word. -/
def acceptAll : DFA Bool Unit where
  step _ _ := ()
  start := ()
  accept := {()}

/-- Intersecting a singleton CFL with this DFA's language. -/
theorem inf_accept_all_cf :
    (({[true, false]} : Language Bool) ⊓ acceptAll.accepts).IsContextFree :=
  IsContextFree.inf_dfa_accepts (IsContextFree.singleton_word [true, false]) acceptAll

end Cslib.Language.ContextFreeInterRegularTests
