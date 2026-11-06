/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWTwelfthLitData
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentFlatData

/-! # The literal octad blocks of the Twelfth short block (r8f)

The flat octad terms of `twelfthLitOct` are gtwelfth's octad table `twelfthOctLit`, by one Boolean
comparison (`twLBEq`) in the kernel. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

open GeneratedAxisGlobalTwelveTwelfthIdent
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The flat octad terms of the literal blocks agree with the octad table (Boolean check). -/
theorem twelfthLitOct_check : twLBEq (octsFlat twelfthLitOct) twelfthOctLit = true := by
  decide +kernel

/-- The flat octad terms of the literal blocks are gtwelfth's octad terms. -/
theorem twelfthLitOct_flat : octsFlat twelfthLitOct = twelfthOctLit :=
  twLBEq_eq _ _ twelfthLitOct_check

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
