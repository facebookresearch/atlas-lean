/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Rayleigh
public import Mathlib.Data.Set.Card
public import MathlibExt.NumberTheory.Beatty.ComplBetween
public import MathlibExt.NumberTheory.Beatty.ComplementaryIff
public import MathlibExt.NumberTheory.Beatty.CountIncrement
public import MathlibExt.NumberTheory.Beatty.FloorFiber
public import MathlibExt.NumberTheory.Beatty.FloorFiberIndicator
public import MathlibExt.NumberTheory.Beatty.FloorFiberSets
public import MathlibExt.NumberTheory.Beatty.FloorSubTwoIdentity
public import MathlibExt.NumberTheory.Beatty.FloorTwoSubIdentity
public import MathlibExt.NumberTheory.Beatty.SelfBetween
public import MathlibExt.NumberTheory.Beatty.SelfBetweenIncrement
public import MathlibExt.NumberTheory.Beatty.SkippingFiberIndicator
public import MathlibExt.NumberTheory.BeattyDecompositionBeattyFloorFiberCardEqOrEqSucc
public import MathlibExt.NumberTheory.BeattyDecompositionBeattyCardComplBetweenIsBeatty

/-! # Decomposition of Beatty and complementary sequences (Polanco)

Statements from G. Polanco, *Decomposition of Beatty and Complementary Sequences*,
INTEGERS 25 (2025), Article A104 (arXiv:2305.15361). Beatty sets are written with
Mathlib's `beattySeq r k = ⌊k * r⌋` over positive indices `k`. For complementary
Beatty sequences `A = {⌊nα⌋}` and `B = {⌊nβ⌋}`, the paper's sequences `r n` and `c n`
count the elements of `B`, respectively `A`, strictly between `a n = ⌊nα⌋` and
`b n = ⌊nβ⌋`; by part (3) of the paper's main theorem these are the auxiliary and
skipping sequences of its MES algorithm. "Complementary Beatty sequences" is
encoded through Beatty's theorem as `Irrational α`, `1 < α` and `α⁻¹ + β⁻¹ = 1`.
-/

namespace MetaMathlibExt

@[expose] public section

open Set

end

end MetaMathlibExt
