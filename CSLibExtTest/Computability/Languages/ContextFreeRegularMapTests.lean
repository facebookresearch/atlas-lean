/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Map
public import CSLibExt.Computability.Languages.ContextFree.Regular
public import CSLibExt.Computability.Languages.Finite

/-!
# Ordinary-client tests for regular-to-CFL and letter maps
-/

public section

namespace Cslib.Language.ContextFreeRegularMapTests

/-- A singleton regular language over a finite alphabet is context-free. -/
theorem regular_cf : (({[true]} : Language Bool)).IsContextFree :=
  IsRegular.isContextFree (IsRegular.singleton_word [true])

/-- Mapping a singleton language by Boolean negation stays context-free. -/
theorem map_cf : (Language.map (fun b => !b) ({[true, false]} : Language Bool)).IsContextFree :=
  IsContextFree.map (IsContextFree.singleton_word [true, false]) (fun b => !b)

end Cslib.Language.ContextFreeRegularMapTests
