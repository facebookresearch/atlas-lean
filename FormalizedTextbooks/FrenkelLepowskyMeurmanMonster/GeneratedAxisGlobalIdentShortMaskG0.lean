/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentShortMaskG

/-! # Certification of the grouped mask table on the labels `0` to `24575` -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent

set_option maxRecDepth 100000 in
/-- The grouped mask table agrees with `shortMaskF` on the labels `0` to `24575`. -/
theorem identMaskG_ok0 : ∀ c : Fin 384, ∀ e : Fin 64,
    identMaskG (64 * c.val + e.val) = shortMaskF (64 * c.val + e.val) := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
