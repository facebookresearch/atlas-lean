/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeModuliStackModels

/-!
# Actual target gluing along the two distinguished divisors

The original singular target is the scheme quotient Y1 union_D Y2.
Two expanded relative families are joined by identifying their actual
distinguished-divisor families. The entire quotient universal property
and contractions are equations of native scheme maps over the parameter.
Normal lines are compared to inverse lines under the actual divisor iso.
Source: Jun Li arXiv:math/0009097v1, Section4.2;
arXiv:math/0110113v1, Section3.1, pp30--32.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ExpandedTargetGluingModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open ExpandedTargetChainGeometry ExpandedRelativeFamilies StandardRelativeExpansionModels
open RelativeProjectiveLineModels NativeLineDuals

variable {k : Type} [Field k]
  (P Q : RelativePair (k := k))
  (R : ProjectiveLine P.divisor.left (normalLineModule P))
  (R' : ProjectiveLine Q.divisor.left (normalLineModule Q))
  (S : StandardSystem P R) (S' : StandardSystem Q R')

structure SingularTarget where
  divisor : P.divisor ≅ Q.divisor
  normal : normalLineModule P ≅
    (Scheme.Modules.pullback divisor.hom.left).obj (dualModule Q.divisor.left (normalLineModule Q))
  scheme : Over (Spec (.of k))
  left : P.target ⟶ scheme
  right : Q.target ⟶ scheme
  joins : P.inclusion ≫ left = divisor.hom ≫ Q.inclusion ≫ right
  universal : ∀ (Z : Over (Spec (.of k))) (f : P.target ⟶ Z) (g : Q.target ⟶ Z),
    P.inclusion ≫ f = divisor.hom ≫ Q.inclusion ≫ g →
      ∃! h : scheme ⟶ Z, left ≫ h = f ∧ right ≫ h = g

variable (W : SingularTarget P Q)
  (T : Over (Spec (.of k))) (F : ExpandedFamily P R S T) (H : ExpandedFamily Q R' S' T)

structure TargetJoin where
  scheme : Over (Spec (.of k))
  projection : scheme ⟶ T
  left : F.scheme ⟶ scheme
  right : H.scheme ⟶ scheme
  left_projection : left ≫ projection = F.projection
  right_projection : right ≫ projection = H.projection
  boundary : F.boundary ≫ left = prod.map W.divisor.hom (𝟙 T) ≫ H.boundary ≫ right
  contraction : scheme ⟶ W.scheme
  left_contraction : left ≫ contraction = F.contraction ≫ W.left
  right_contraction : right ≫ contraction = H.contraction ≫ W.right
  universal : ∀ (Z : Over (Spec (.of k))) (z : Z ⟶ T) (f : F.scheme ⟶ Z) (g : H.scheme ⟶ Z),
    f ≫ z = F.projection → g ≫ z = H.projection →
    F.boundary ≫ f = prod.map W.divisor.hom (𝟙 T) ≫ H.boundary ≫ g →
      ∃! h : scheme ⟶ Z, h ≫ z = projection ∧ left ≫ h = f ∧ right ≫ h = g

end MathlibExt.AlgebraicGeometry.ExpandedTargetGluingModels
