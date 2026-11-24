/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Topology.Compactification.OnePoint.QuotientComplement

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set
open scoped OnePoint

namespace OnePoint

/-- The standard copy of `Bool` is the complement of infinity in its one-point
compactification. -/
noncomputable def boolComplementHomeomorph :
    Bool ≃ₜ ({(∞ : OnePoint Bool)}ᶜ : Set (OnePoint Bool)) :=
  OnePoint.isOpenEmbedding_coe.toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr OnePoint.compl_infty.symm)

noncomputable def boolIdentityQuotientHomeomorph :
    OnePoint Bool ≃ₜ OnePoint Bool :=
  OnePoint.homeomorphOfQuotientComplement
    ({(∞ : OnePoint Bool)} : Set (OnePoint Bool)) id ∞ OnePoint.isClosed_infty
    Topology.IsQuotientMap.id (by rfl) boolComplementHomeomorph
    boolComplementHomeomorph (fun _ ↦ rfl)

example : boolIdentityQuotientHomeomorph ∞ = ∞ := by
  simp [boolIdentityQuotientHomeomorph]

example (x : Bool) : boolIdentityQuotientHomeomorph x = x := by
  change (boolComplementHomeomorph x).1 = (x : OnePoint Bool)
  rfl

end OnePoint
