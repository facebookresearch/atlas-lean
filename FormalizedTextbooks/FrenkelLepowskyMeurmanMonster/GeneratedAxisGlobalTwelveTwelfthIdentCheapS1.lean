/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentCheapS0

/-! # The second source stage of the incoming Twelfth vector, in compact checkpoints

The kernel checks that the monomial letters of the second stage map the widened `twelfthS0Lit`
to `twelfthS1mLit` and that its Xi and code sign letters map the widened `twelfthS1mLit` to
`twelfthS1Lit` (packed comparisons at field widths `4` and `16`). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveTwelfthIdent
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The monomial letters of the second stage map the widened `twelfthS0Lit` to `twelfthS1mLit`. -/
theorem twelfthS1m_check :
    twColCheck 4 2 1 (tensorWordAll 4 ((twelfthYStage 1).drop 2) (twWidenT 2 4 twelfthS0Lit))
      twelfthS1mLit = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Xi and the code sign of the second stage map the widened `twelfthS1mLit` to `twelfthS1Lit`. -/
theorem twelfthS1_check :
    twColCheck 16 3 8 (tensorWordAll 16 ((twelfthYStage 1).take 2) (twWidenT 2 16 twelfthS1mLit))
      twelfthS1Lit = true := by
  decide +kernel

end GeneratedAxisGlobalTwelveTwelfthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
