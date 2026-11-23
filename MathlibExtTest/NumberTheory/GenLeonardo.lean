/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GenLeonardo

namespace MetaMathlibExt

-- A negative parameter gives a zero term followed by a negative term.
example : genLeonardo (-2) 2 = 0 ∧ genLeonardo (-2) 3 = -1 := by decide

example : genLeonardoCompanion (-2) 0 = 3 ∧ genLeonardoCompanion (-2) 2 = 0 := by decide

end MetaMathlibExt
