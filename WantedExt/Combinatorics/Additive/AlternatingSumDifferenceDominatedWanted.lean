/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Alternating sequences of sum- and difference-dominated sets

Statements from Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller
and Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference
Dominated Sets*, INTEGERS 26 (2026), Article A88 (arXiv:2509.12829). Journal labels: Lemma 1,
Theorems 1-3 are arXiv Lemma 2.4 and Theorems 2.1, 2.3, 2.5.

A finite set `A ⊆ ℤ` is MSTD (sum-dominated) when `|A + A| > |A - A|` and MDTS
(difference-dominated) when `|A - A| > |A + A|`; both are written out with Mathlib's pointwise
`Finset` operations.
-/
module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Additive.IntervalEraseAddSub
public import MathlibExt.Combinatorics.Additive.NathansonMSTD
public import MathlibExt.Combinatorics.Additive.AlternatingSumDifferenceDominated

namespace MetaMathlibExt

@[expose] public section

open Pointwise


end

end MetaMathlibExt
