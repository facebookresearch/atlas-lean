/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ExtraTribReversal

open MetaMathlibExt

-- The start of the positive tail is allowed to be a negative integer.
example (S : ℤ → ℤ) (hRec : ∀ n, S (n + 3) = S (n + 2) + S (n + 1) + S n)
    (hPos : ∀ n ≥ (-2 : ℤ), 0 < S n) : ¬ IsExtraTrib (fun n => |S (-n)|) :=
  not_isExtraTrib_reversal S ⟨hRec, -2, hPos⟩
