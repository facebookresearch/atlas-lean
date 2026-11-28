/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralMarkedRegularizers

/-!
# Inverses of native marked regularizer arrows

These are direct construction/proof requests for the displayed actual
schemes, modules, torsors and normalized maps. Their definitions and
completed source ports remain in MathlibExt.
Source: DG arXiv:math/0005132v3, Sections 2 and 4.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.CameralMarkedRegularizersWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages ExpansionParameterModels
open CameralCoverDescentModels CameralMarkedRegularizers CameralRamificationReindexing
attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction

theorem_wanted nativeMarkedIsGroupoid (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) (I : IncidenceAction F)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) : IsGroupoid (Object F I C)

end WantedExt.AlgebraicGeometry.CameralMarkedRegularizersWanted
