/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralCartanValueModels

/-!
# Native Cartan value and section correspondence

These are direct construction/proof requests for the displayed actual
schemes, modules, torsors and normalized maps. Their definitions and
completed source ports remain in MathlibExt.
Source: DG arXiv:math/0005132v3, Proposition 12.5 and Sections 17.3--17.8.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.CameralCartanValueModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages ExpansionParameterModels
open CameralRegularizedHiggsModels CameralCoverDescentModels CameralCartanValueModels
open CameralRamificationReindexing RelativeLambdaReindexing LineBundleTaskContracts
open AlgebraicLineBundleFamilies
attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction

def_wanted nativeCartanDescent (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) (I : IncidenceAction F)
    (X : Over (Spec (.of ℂ))) (K : TwistLine X) (H : RegularizedBundle F X K)
    (D : CoverDescent F I H.regularizer) : CartanDescent F I H D

def_wanted nativeCartanSectionSpace (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (X : Over (Spec (.of ℂ))) (K : TwistLine X) : SectionSpace X (cartanKModule F X K)

def_wanted nativeCartanWeylAction (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) (X : Over (Spec (.of ℂ)))
    (K : TwistLine X)
    (S : SectionSpace X (cartanKModule F X K)) : CartanWeylAction F X K S

theorem_wanted nativeValueWeylEquivariant (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) (I : IncidenceAction F)
    (X : Over (Spec (.of ℂ))) (K : TwistLine X) (H : RegularizedBundle F X K)
    (D : CoverDescent F I H.regularizer) (Q : CartanDescent F I H D)
    (T : TensorPullbackComparison (projection F D.cameral).left)
    (S : SectionSpace X (cartanKModule F X K)) (W : CartanWeylAction F X K S)
    (s : Section (moduleTensor X.left H.centralizer.module K.module)) (w : F.Weyl) :
    (CameralRamificationTensorModels.coverIso F D.cameral w).hom ≫
      valueMapOf F I H D Q T S s = valueMapOf F I H D Q T S s ≫ (W.action w).asIso.hom

def_wanted nativeValueCorrespondence (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) (I : IncidenceAction F)
    (X : Over (Spec (.of ℂ))) (K : TwistLine X) (H : RegularizedBundle F X K)
    (D : CoverDescent F I H.regularizer) (Q : CartanDescent F I H D)
    (T : TensorPullbackComparison (projection F D.cameral).left)
    (S : SectionSpace X (cartanKModule F X K)) (W : CartanWeylAction F X K S) :
    ValueCorrespondence F I H D Q T S W

end WantedExt.AlgebraicGeometry.CameralCartanValueModelsWanted
