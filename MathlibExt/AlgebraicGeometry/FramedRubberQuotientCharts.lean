/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FramedRubberModuliModels
public import MathlibExt.AlgebraicGeometry.GroupTorsorGeometry
public import MathlibExt.AlgebraicGeometry.StackBundleCones

/-!
# Actual torus quotient charts for rubber moduli

The framed-to-quotient morphism has actual scheme fibres with the native
fppf Gm^(m+1) torsor action. Every universal fibre point is fixed by the
full CoGrothendieck/scheme-fibre comparison. Its action is normalized to
the actual standard-target frame scaling on families. The quotient chart
maps etale to rubber moduli and retains the based forgetful2-cell.
Source: Jun Li arXiv:math/0009097v1, Sections1 and4;
JPPZ arXiv:1602.04705v2, Section0.2.4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.FramedRubberQuotientCharts

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeProjectiveLineModels ExpandedTargetChainGeometry
open StandardRelativeExpansionModels ExpansionParameterModels RubberMapFamilies RubberModuliStackModels
open StackCycleGeometry StackCycleRelations StackFibreModels StackBundleCones

variable {k : Type} [Field k]
  (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
  (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
  (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
  (m : ℕ) (G : TorusTheory k (m + 1))
  (A : RubberStandardScalingModels.StandardAction O P D R S m G)
  {g n : ℕ} (a : Fin n → ℤ)
  (H : FramedRubberModuliModels.Model O P D R S m (g := g) a)
  (B : RubberModuliModel O P D R S (g := g) a)
  (F : FramedRubberModuliModels.Forget O P D R S m a H B)

structure PrincipalFibre {Q : Stack (Spec (.of k))} (p : StackHom H.stack Q)
    (T : Over (Spec (.of k))) (q : Q.Fibre T) where
  scheme : SchemeFibreModel p T q
  torsor : letI := G.group; GroupTorsorGeometry.Torsor (torusScheme k (m + 1)) T
  iso : letI := G.group; scheme.scheme.left ≅ torsor.total.left
  over : letI := G.group; iso.hom ≫ torsor.projection.left = scheme.scheme.hom
  point : letI := G.group; H.stack.Fibre torsor.total
  arrow : letI := G.group;
    (totalMap p).obj (StackFibreModels.point torsor.total point) ⟶ StackFibreModels.point T q
  arrow_base : letI := G.group; arrow.base = torsor.projection
  represented : letI := G.group;
    scheme.comparison.functor.obj (CostructuredArrow.mk arrow) ≅ Over.mk iso.inv
  scaling : letI := G.group; letI := torsor.action;
    FramedRubberFamilies.ScalingRelation O P D R S m a G A
      (CartesianMonoidalCategory.fst (torusScheme k (m + 1)) torsor.total)
      (((H.family ((torusScheme k (m + 1)) ⊗ torsor.total)).obj
        ((pull H.stack (CartesianMonoidalCategory.snd (torusScheme k (m + 1)) torsor.total)).obj point)).obj)
      (((H.family ((torusScheme k (m + 1)) ⊗ torsor.total)).obj
        ((pull H.stack γ[torusScheme k (m + 1),torsor.total]).obj point)).obj)

structure Model where
  stack : Stack (Spec (.of k))
  dm : stack.IsDeligneMumfordStack
  finiteType : FiniteTypeArtin k stack
  projection : StackHom H.stack stack
  principal : ∀ (T : Over (Spec (.of k))) (q : stack.Fibre T),
    PrincipalFibre O P D R S m G A a H projection T q
  forget : StackHom stack B.stack
  etale : ∀ (T : Over (Spec (.of k))) (q : B.stack.Fibre T),
    ∃ c : SchemeFibreModel forget T q, Etale c.scheme.hom
  based : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp projection forget) F.map

end MathlibExt.AlgebraicGeometry.FramedRubberQuotientCharts
