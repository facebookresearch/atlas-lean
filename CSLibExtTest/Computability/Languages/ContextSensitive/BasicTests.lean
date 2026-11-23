/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Languages.ContextSensitive.Basic

/-!
# Client tests for the context-sensitive `aⁿbⁿcⁿ` grammar

The public grammar API derives the literal words `abc` and `aabbcc` and
rejects `aabbc`, whose terminal counts differ.
-/

namespace Cslib.Language.ContextSensitiveTests

/-- The imported grammar satisfies the context-sensitive production conditions. -/
example : IsContextSensitive abcGrammar := abcGrammar_contextSensitive

/-- The smallest positive case is generated. -/
example : [ABC.a, ABC.b, ABC.c] ∈ language abcGrammar := abc_mem

/-- A two-letter block case exercises the grammar's shuttle and conversion rules. -/
example : [ABC.a, ABC.a, ABC.b, ABC.b, ABC.c, ABC.c] ∈ language abcGrammar := aabbcc_mem

/-- A word with unequal terminal counts is rejected. -/
example : [ABC.a, ABC.a, ABC.b, ABC.b, ABC.c] ∉ language abcGrammar := aabbc_not_mem

end Cslib.Language.ContextSensitiveTests
