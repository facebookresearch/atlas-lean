/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralBorelAbelianizationCore

/-!
# The native standard-Borel reduction family

These are direct construction/proof requests for the displayed actual
schemes, modules, torsors and normalized maps. Their definitions and
completed source ports remain in MathlibExt.
Source: DG arXiv:math/0005132v3, Sections 7.2 and 16.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.CameralBorelAbelianizationCoreWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages ExpansionParameterModels
open CameralCoverDescentModels CameralBorelReductionModels CameralBorelAbelianizationCore
open CameralRamificationReindexing
attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction
attribute [local instance] CameralBorelReductionModels.borelGroup
attribute [local instance] CameralBorelReductionModels.quotientHom

def_wanted nativeReductionFamily (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) (B : BorelGeometry F)
    (I : IncidenceAction F)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) : ReductionFamily F B I C

end WantedExt.AlgebraicGeometry.CameralBorelAbelianizationCoreWanted
