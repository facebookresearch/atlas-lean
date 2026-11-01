/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentE8SrcData

/-! # Materialized Eighth source: the octad Fourier blocks

The octad blocks of the triality image (`twTriOct`, `264` blocks of `64` terms) are the literal
blocks `e8SrcOctLit` (one kernel check, ~80 s). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The literal octad blocks are the octad blocks of the triality image. -/
theorem e8SrcOct_eq : twTriOct 256 (srcEighthYL 64).sh.oct srcEighthOs = e8SrcOctLit := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
