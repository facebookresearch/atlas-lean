/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.CompletedZeroCommaRealizationNaturality
public import MathlibExt.KTheory.Exact.Extension.CompletedZeroLiteralProjection
public import MathlibExt.KTheory.Exact.Extension.CompletedCoreOriginalCarriedPath
public import MathlibExt.KTheory.Ring.StableGeneralLinear.MixedOriginalQRealizationTransport
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# The actual mixed map of the original full zero homotopy fibers

The original stabilized functor and Quillen functor have their proved
literal target square. The full mixed fiber map sends its total coordinate
through that stabilized functor and maps its entire ending path before
appending the original canonical mapped-zero root. The original category
worlds and compact-open fibers remain independent.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory ContinuousMap Simplicial

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uA uB uC vC uD vD

namespace AlgebraicKTheory.OriginalQZeroComparison

private theorem actualProductPointExt {X Y : TopCat.{uB}}
    {a b : (X ⨯ Y : TopCat.{uB})}
    (hX : (prod.fst : X ⨯ Y ⟶ X) a = (prod.fst : X ⨯ Y ⟶ X) b)
    (hY : (prod.snd : X ⨯ Y ⟶ Y) a = (prod.snd : X ⨯ Y ⟶ Y) b) : a = b := by
  apply (TopCat.homeoOfIso (TopCat.prodIsoProd X Y)).injective
  change (TopCat.prodIsoProd X Y).hom a = (TopCat.prodIsoProd X Y).hom b
  rw [TopCat.prodIsoProd_hom_apply, TopCat.prodIsoProd_hom_apply]
  exact Prod.ext hX hY

private theorem actualProductInverseFirst {X Y : TopCat.{uB}} (x : X) (y : Y) :
    (prod.fst : X ⨯ Y ⟶ X) ((TopCat.prodIsoProd X Y).inv (x, y)) = x :=
  (TopCat.comp_app (TopCat.prodIsoProd X Y).inv (prod.fst : X ⨯ Y ⟶ X) (x, y)).symm.trans
    (ConcreteCategory.congr_hom (TopCat.prodIsoProd_inv_fst X Y) (x, y))

private theorem actualProductMapFirst {X Y B : TopCat.{uB}}
    (f : X ⟶ B) (g : Y ⟶ B) (z : (X ⨯ Y : TopCat.{uB})) :
    (prod.fst : B ⨯ B ⟶ B) (prod.map f g z) = f ((prod.fst : X ⨯ Y ⟶ X) z) :=
  (TopCat.comp_app (prod.map f g) (prod.fst : B ⨯ B ⟶ B) z).symm.trans
    ((ConcreteCategory.congr_hom (prod.map_fst f g) z).trans
      (TopCat.comp_app (prod.fst : X ⨯ Y ⟶ X) f z))

private theorem actualProductMapSecond {X Y B : TopCat.{uB}}
    (f : X ⟶ B) (g : Y ⟶ B) (z : (X ⨯ Y : TopCat.{uB})) :
    (prod.snd : B ⨯ B ⟶ B) (prod.map f g z) = g ((prod.snd : X ⨯ Y ⟶ Y) z) :=
  (TopCat.comp_app (prod.map f g) (prod.snd : B ⨯ B ⟶ B) z).symm.trans
    ((ConcreteCategory.congr_hom (prod.map_snd f g) z).trans
      (TopCat.comp_app (prod.snd : X ⨯ Y ⟶ Y) g z))

private theorem actualPathEndpointsFirst (B : TopCat.{uB}) (q : TopCat.pathObject B) :
    (prod.fst : B ⨯ B ⟶ B) (TopCat.pathEndpoints B q) = q 0 :=
  (TopCat.comp_app (TopCat.pathEndpoints B) (prod.fst : B ⨯ B ⟶ B) q).symm.trans
    (ConcreteCategory.congr_hom
      (prod.lift_fst (TopCat.pathEvalZero B) (TopCat.pathEvalOne B)) q)

private theorem actualPathEndpointsSecond (B : TopCat.{uB}) (q : TopCat.pathObject B) :
    (prod.snd : B ⨯ B ⟶ B) (TopCat.pathEndpoints B q) = q 1 :=
  (TopCat.comp_app (TopCat.pathEndpoints B) (prod.snd : B ⨯ B ⟶ B) q).symm.trans
    (ConcreteCategory.congr_hom
      (prod.lift_snd (TopCat.pathEvalZero B) (TopCat.pathEvalOne B)) q)

private theorem actualFiberCoordinatesCondition {E B : TopCat.{uB}}
    (p : E ⟶ B) (b : B) (e : E) (q : TopCat.pathObject B)
    (h0 : q 0 = p e) (h1 : q 1 = b) :
    prod.map p (TopCat.const b : TopCat.of PUnit ⟶ B)
        ((TopCat.prodIsoProd E (TopCat.of PUnit)).inv (e, PUnit.unit)) =
      TopCat.pathEndpoints B q := by
  apply actualProductPointExt
  · exact (actualProductMapFirst p (TopCat.const b) _).trans
      ((congrArg p (actualProductInverseFirst (X := E) (Y := TopCat.of PUnit) e PUnit.unit)).trans
        (h0.symm.trans (actualPathEndpointsFirst B q).symm))
  · exact (actualProductMapSecond p (TopCat.const b) _).trans
      (h1.symm.trans (actualPathEndpointsSecond B q).symm)

private def actualFiberPoint {E B : TopCat.{uB}}
    (p : E ⟶ B) (b : B) (e : E) (q : TopCat.pathObject B)
    (h0 : q 0 = p e) (h1 : q 1 = b) : TopCat.homotopyFiber p b :=
  (TopCat.pullbackIsoProdSubtype
    (prod.map p (TopCat.const b : TopCat.of PUnit ⟶ B)) (TopCat.pathEndpoints B)).inv
      ⟨((TopCat.prodIsoProd E (TopCat.of PUnit)).inv (e, PUnit.unit), q),
        actualFiberCoordinatesCondition p b e q h0 h1⟩

private theorem actualFiberPointTotal {E B : TopCat.{uB}}
    (p : E ⟶ B) (b : B) (e : E) (q : TopCat.pathObject B)
    (h0 : q 0 = p e) (h1 : q 1 = b) :
    TopCat.homotopyFiberToTotal p b (actualFiberPoint p b e q h0 h1) = e := by
  change (prod.fst : E ⨯ TopCat.of PUnit ⟶ E)
    (pullback.fst (prod.map p (TopCat.const b : TopCat.of PUnit ⟶ B))
      (TopCat.pathEndpoints B) (actualFiberPoint p b e q h0 h1)) = e
  rw [actualFiberPoint, TopCat.pullbackIsoProdSubtype_inv_fst_apply]
  exact actualProductInverseFirst (X := E) (Y := TopCat.of PUnit) e PUnit.unit

private theorem actualFiberPointPath {E B : TopCat.{uB}}
    (p : E ⟶ B) (b : B) (e : E) (q : TopCat.pathObject B)
    (h0 : q 0 = p e) (h1 : q 1 = b) :
    TopCat.homotopyFiberPath p b (actualFiberPoint p b e q h0 h1) = q := by
  exact TopCat.pullbackIsoProdSubtype_inv_snd_apply
    (prod.map p (TopCat.const b : TopCat.of PUnit ⟶ B)) (TopCat.pathEndpoints B) _

private theorem actualFiberPointExt {E B : TopCat.{uB}}
    (p : E ⟶ B) (b : B) {z z' : TopCat.homotopyFiber p b}
    (hTotal : TopCat.homotopyFiberToTotal p b z = TopCat.homotopyFiberToTotal p b z')
    (hPath : TopCat.homotopyFiberPath p b z = TopCat.homotopyFiberPath p b z') : z = z' := by
  let f := prod.map p (TopCat.const b : TopCat.of PUnit ⟶ B)
  let g := TopCat.pathEndpoints B
  apply (TopCat.homeoOfIso (TopCat.pullbackIsoProdSubtype f g)).injective
  change (TopCat.pullbackIsoProdSubtype f g).hom z =
    (TopCat.pullbackIsoProdSubtype f g).hom z'
  apply Subtype.ext
  change (pullback.fst f g z, pullback.snd f g z) =
    (pullback.fst f g z', pullback.snd f g z')
  apply Prod.ext
  · exact actualProductPointExt hTotal (Subsingleton.elim _ _)
  · exact hPath

private def actualMixedFiberLift {A : Type uA} [TopologicalSpace A]
    {E B : TopCat.{uB}} (p : E ⟶ B) (b : B)
    (l : C(A, E)) (q : C(A, TopCat.pathObject B))
    (h0 : ∀ a, q a 0 = p (l a)) (h1 : ∀ a, q a 1 = b) :
    C(A, TopCat.homotopyFiber p b) where
  toFun a := actualFiberPoint p b (l a) (q a) (h0 a) (h1 a)
  continuous_toFun := by
    dsimp only [actualFiberPoint]
    apply (TopCat.pullbackIsoProdSubtype
      (prod.map p (TopCat.const b : TopCat.of PUnit ⟶ B))
      (TopCat.pathEndpoints B)).inv.hom.continuous.comp
    apply Continuous.subtype_mk
    exact ((TopCat.prodIsoProd E (TopCat.of PUnit)).inv.hom.continuous.comp
      (l.continuous.prodMk continuous_const)).prodMk q.continuous

private def actualOriginalEndingPath {E B : TopCat.{uA}}
    (p : E ⟶ B) (b : B) (z : TopCat.homotopyFiber p b) :
    Path (p (TopCat.homotopyFiberToTotal p b z)) b where
  toFun t := TopCat.homotopyFiberPath p b z (TopCat.I.homeomorph.{uA}.symm t)
  continuous_toFun := (TopCat.homotopyFiberPath p b z).continuous.comp
    TopCat.I.homeomorph.symm.continuous
  source' := by
    have h0 : TopCat.I.homeomorph.{uA}.symm (0 : unitInterval) = 0 := by
      apply TopCat.I.homeomorph.injective
      simp
    rw [h0]
    exact ConcreteCategory.congr_hom
      (TopCat.homotopyPullbackPath_evalZero p
        (TopCat.const b : TopCat.of PUnit ⟶ B)) z
  target' := by
    have h1 : TopCat.I.homeomorph.{uA}.symm (1 : unitInterval) = 1 := by
      apply TopCat.I.homeomorph.injective
      simp
    rw [h1]
    exact ConcreteCategory.congr_hom
      (TopCat.homotopyPullbackPath_evalOne p
        (TopCat.const b : TopCat.of PUnit ⟶ B)) z

private theorem actualOriginalEndingPathContinuous {E B : TopCat.{uA}}
    (p : E ⟶ B) (b : B) :
    Continuous (fun z : TopCat.homotopyFiber p b × unitInterval =>
      actualOriginalEndingPath p b z.1 z.2) :=
  continuous_eval.comp
    (((TopCat.homotopyFiberPath p b).hom.continuous.comp continuous_fst).prodMk
      (TopCat.I.homeomorph.symm.continuous.comp continuous_snd))

private def actualMixedMappedEndingPath
    {E B : TopCat.{uA}} {E' B' : TopCat.{uB}}
    (p : E ⟶ B) (b : B) (p' : E' ⟶ B') (b' : B')
    (l : C(E, E')) (h : C(B, B'))
    (hp : ∀ e, p' (l e) = h (p e)) (q : Path (h b) b')
    (z : TopCat.homotopyFiber p b) :
    Path (p' (l (TopCat.homotopyFiberToTotal p b z))) b' :=
  (((actualOriginalEndingPath p b z).map h.continuous).trans q).cast
    (hp (TopCat.homotopyFiberToTotal p b z)) rfl

private theorem actualMixedMappedEndingPathContinuous
    {E B : TopCat.{uA}} {E' B' : TopCat.{uB}}
    (p : E ⟶ B) (b : B) (p' : E' ⟶ B') (b' : B')
    (l : C(E, E')) (h : C(B, B'))
    (hp : ∀ e, p' (l e) = h (p e)) (q : Path (h b) b') :
    Continuous (fun z : TopCat.homotopyFiber p b × unitInterval =>
      actualMixedMappedEndingPath p b p' b' l h hp q z.1 z.2) :=
  Path.trans_continuous_family
    (fun z => (actualOriginalEndingPath p b z).map h.continuous)
    (h.continuous.comp (actualOriginalEndingPathContinuous p b))
    (fun _ => q) (q.continuous.comp continuous_snd)

private def actualMixedFiberMap
    {E B : TopCat.{uA}} {E' B' : TopCat.{uB}}
    (p : E ⟶ B) (b : B) (p' : E' ⟶ B') (b' : B')
    (l : C(E, E')) (h : C(B, B'))
    (hp : ∀ e, p' (l e) = h (p e)) (q : Path (h b) b') :
    C(TopCat.homotopyFiber p b, TopCat.homotopyFiber p' b') := by
  let a : C(TopCat.homotopyFiber p b × unitInterval, B') :=
    { toFun := fun z => actualMixedMappedEndingPath p b p' b' l h hp q z.1 z.2
      continuous_toFun := actualMixedMappedEndingPathContinuous p b p' b' l h hp q }
  let s : C(TopCat.homotopyFiber p b × TopCat.I.{uB},
      TopCat.homotopyFiber p b × unitInterval) :=
    { toFun := fun z => (z.1, TopCat.I.homeomorph.{uB} z.2)
      continuous_toFun := continuous_fst.prodMk
        (TopCat.I.homeomorph.{uB}.continuous.comp continuous_snd) }
  let k : C(TopCat.homotopyFiber p b, TopCat.pathObject B') :=
    ContinuousMap.curry (a.comp s)
  have h0 (z : TopCat.homotopyFiber p b) :
      k z (0 : TopCat.I.{uB}) = p' (l (TopCat.homotopyFiberToTotal p b z)) := by
    change actualMixedMappedEndingPath p b p' b' l h hp q z
      (TopCat.I.homeomorph.{uB} (0 : TopCat.I.{uB})) =
        p' (l (TopCat.homotopyFiberToTotal p b z))
    exact (congrArg (actualMixedMappedEndingPath p b p' b' l h hp q z)
      TopCat.I.homeomorph_zero.{uB}).trans (actualMixedMappedEndingPath p b p' b' l h hp q z).source
  have h1 (z : TopCat.homotopyFiber p b) : k z (1 : TopCat.I.{uB}) = b' := by
    change actualMixedMappedEndingPath p b p' b' l h hp q z
      (TopCat.I.homeomorph.{uB} (1 : TopCat.I.{uB})) = b'
    exact (congrArg (actualMixedMappedEndingPath p b p' b' l h hp q z)
      TopCat.I.homeomorph_one.{uB}).trans (actualMixedMappedEndingPath p b p' b' l h hp q z).target
  exact actualMixedFiberLift p' b' (l.comp (TopCat.homotopyFiberToTotal p b).hom) k h0 h1

private theorem actualMixedFiberMapTotal
    {E B : TopCat.{uA}} {E' B' : TopCat.{uB}}
    (p : E ⟶ B) (b : B) (p' : E' ⟶ B') (b' : B')
    (l : C(E, E')) (h : C(B, B'))
    (hp : ∀ e, p' (l e) = h (p e)) (q : Path (h b) b')
    (z : TopCat.homotopyFiber p b) :
    TopCat.homotopyFiberToTotal p' b' (actualMixedFiberMap p b p' b' l h hp q z) =
      l (TopCat.homotopyFiberToTotal p b z) := by
  dsimp only [actualMixedFiberMap, actualMixedFiberLift, ContinuousMap.coe_mk]
  exact actualFiberPointTotal p' b' _ _ _ _

private theorem actualMixedFiberMapPath
    {E B : TopCat.{uA}} {E' B' : TopCat.{uB}}
    (p : E ⟶ B) (b : B) (p' : E' ⟶ B') (b' : B')
    (l : C(E, E')) (h : C(B, B'))
    (hp : ∀ e, p' (l e) = h (p e)) (q : Path (h b) b')
    (z : TopCat.homotopyFiber p b) (t : TopCat.I.{uB}) :
    TopCat.homotopyFiberPath p' b' (actualMixedFiberMap p b p' b' l h hp q z) t =
      actualMixedMappedEndingPath p b p' b' l h hp q z (TopCat.I.homeomorph t) := by
  dsimp only [actualMixedFiberMap, actualMixedFiberLift, ContinuousMap.coe_mk]
  rw [actualFiberPointPath]
  rfl

private abbrev actualOriginalBase
    (C : Type uC) [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] : TopCat.{max uC vC} :=
  SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max uC vC})

private abbrev actualOriginalProjection
    (C : Type uC) [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :=
  SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0}
    (ExtensionCategory.localizedTarget (C := C)))

private abbrev actualOriginalZero
    (C : Type uC) [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] : actualOriginalBase C :=
  SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : C)⟩ : QuillenQ C))

private theorem actualOriginalProjectionValue
    (C : Type uC) [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :
    realizedNerveFunctorMap (ExtensionCategory.localizedTarget (C := C)) =
      (actualOriginalProjection C).hom :=
  realizedNerveFunctorMap_commonDownFrame.{uC, max uC vC}
    (ExtensionCategory.localizedTarget (C := C))

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem actualMixedOriginalTargetSquare :
    (actualOriginalProjection D).hom.comp
        (realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap F)) =
      (QuillenMixedUniverseTransport.mixedNQRealMap F).comp
        (actualOriginalProjection C).hom := by
  let T := ExtensionCategory.stabilizedFunctorMap F
  let PC := ExtensionCategory.localizedTarget (C := C)
  let PD := ExtensionCategory.localizedTarget (C := D)
  let Q := QuillenQ.map F
  have hL : realizedNerveFunctorMap (T ⋙ PD) =
      (actualOriginalProjection D).hom.comp (realizedNerveFunctorMap T) :=
    (realizedNerveFunctorMap_comp_independent T PD).trans
      (congrArg (fun m => m.comp (realizedNerveFunctorMap T)) (actualOriginalProjectionValue D))
  have hR : realizedNerveFunctorMap (PC ⋙ Q) =
      (QuillenMixedUniverseTransport.mixedNQRealMap F).comp (actualOriginalProjection C).hom :=
    (realizedNerveFunctorMap_comp_independent PC Q).trans
      ((congrArg (fun m => (realizedNerveFunctorMap Q).comp m) (actualOriginalProjectionValue
          C)).trans
        (congrArg (fun m => m.comp (actualOriginalProjection C).hom)
          (QuillenMixedUniverseTransport.mixedNQRealMap_value F).symm))
  exact hL.symm.trans
    ((congrArg realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap_target F)).trans hR)

private def actualOriginalCanonicalRoot :
    Path (QuillenMixedUniverseTransport.mixedNQRealMap F (actualOriginalZero C))
      (actualOriginalZero D) :=
  (QuillenMixedUniverseTransport.mixedNQRootPath F).cast
    (congrArg (QuillenMixedUniverseTransport.mixedNQRealMap F)
      (NQReal.basepoint_eq_realizedVertex C).symm)
    (NQReal.basepoint_eq_realizedVertex D).symm

/-- The actual map of BOTH original full compact-open zero fibers retains the
original total map, base map, whole ending path, and canonical zero root. -/
public def mixedOriginalZeroFiberMap :
    C(TopCat.homotopyFiber
        (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0}
          (ExtensionCategory.localizedTarget (C := C))))
        (SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : C)⟩ : QuillenQ C))),
      TopCat.homotopyFiber
        (SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
          (ExtensionCategory.localizedTarget (C := D))))
        (SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : D)⟩ : QuillenQ D)))) :=
  actualMixedFiberMap (actualOriginalProjection C) (actualOriginalZero C)
    (actualOriginalProjection D) (actualOriginalZero D)
    (realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap F))
    (QuillenMixedUniverseTransport.mixedNQRealMap F)
    (fun e => congrArg (fun m => m e) (actualMixedOriginalTargetSquare F))
    (actualOriginalCanonicalRoot F)

/-- EVERY full original fiber point keeps its literal original stabilized-functor total image. -/
public theorem mixedOriginalZeroFiberMap_toTotal
    (z : TopCat.homotopyFiber
      (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0}
        (ExtensionCategory.localizedTarget (C := C))))
      (SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : C)⟩ : QuillenQ C)))) :
    TopCat.homotopyFiberToTotal
        (SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
          (ExtensionCategory.localizedTarget (C := D))))
        (SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : D)⟩ : QuillenQ D)))
        (mixedOriginalZeroFiberMap F z) =
      realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap F)
        (TopCat.homotopyFiberToTotal
          (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0}
            (ExtensionCategory.localizedTarget (C := C))))
          (SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : C)⟩ : QuillenQ C))) z) :=
  actualMixedFiberMapTotal (actualOriginalProjection C) (actualOriginalZero C)
    (actualOriginalProjection D) (actualOriginalZero D)
    (realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap F))
    (QuillenMixedUniverseTransport.mixedNQRealMap F)
    (fun e => congrArg (fun m => m e) (actualMixedOriginalTargetSquare F))
    (actualOriginalCanonicalRoot F) z

/-- EVERY time of the full original mixed fiber path uses the actual mapped old
path and the SAME canonical root, with the original concatenation clock. -/
public theorem mixedOriginalZeroFiberMap_path
    (z : TopCat.homotopyFiber
      (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0}
        (ExtensionCategory.localizedTarget (C := C))))
      (SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : C)⟩ : QuillenQ C))))
    (t : TopCat.I.{max uD vD}) :
    TopCat.homotopyFiberPath
        (SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
          (ExtensionCategory.localizedTarget (C := D))))
        (SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : D)⟩ : QuillenQ D)))
        (mixedOriginalZeroFiberMap F z) t =
      if ht : (TopCat.I.homeomorph.{max uD vD} t : ℝ) ≤ 1 / 2 then
        QuillenMixedUniverseTransport.mixedNQRealMap F
          (TopCat.homotopyFiberPath
            (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0}
              (ExtensionCategory.localizedTarget (C := C))))
            (SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : C)⟩ : QuillenQ C))) z
            (TopCat.I.homeomorph.{max uC vC}.symm
              ⟨2 * TopCat.I.homeomorph.{max uD vD} t,
                (unitInterval.mul_pos_mem_iff zero_lt_two).2
                  ⟨(TopCat.I.homeomorph.{max uD vD} t).2.1, ht⟩⟩))
      else
        QuillenMixedUniverseTransport.mixedNQRootPath F
          ⟨2 * TopCat.I.homeomorph.{max uD vD} t - 1,
            unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 ht).le, (TopCat.I.homeomorph.{max uD vD} t).2.2⟩⟩ := by
  rw [mixedOriginalZeroFiberMap, actualMixedFiberMapPath]
  change (((actualOriginalEndingPath (actualOriginalProjection C) (actualOriginalZero C) z).map
      (QuillenMixedUniverseTransport.mixedNQRealMap F).continuous).trans
    (actualOriginalCanonicalRoot F)) (TopCat.I.homeomorph t) = _
  rw [Path.trans_apply]
  split <;> rfl

end AlgebraicKTheory.OriginalQZeroComparison

end


/-!
# The original total family and its entire uniform base trace

The original whole total family is attached to the literal original
comparison maps. Its uniform projected trace is evaluated at the original
completed unit, and the original vertex-path theorem identifies that
entire trace with the SAME canonical mapped-zero edge up to an
endpoint-fixed path homotopy.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory ContinuousMap Simplicial

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uA uB uC vC uD vD

namespace AlgebraicKTheory.OriginalQZeroComparison

private theorem actualMixedFiberLiftTotal {A : Type uA} [TopologicalSpace A]
    {E B : TopCat.{uB}} (p : E ⟶ B) (b : B)
    (l : C(A, E)) (q : C(A, TopCat.pathObject B))
    (h0 : ∀ a, q a 0 = p (l a)) (h1 : ∀ a, q a 1 = b) (a : A) :
    TopCat.homotopyFiberToTotal p b (actualMixedFiberLift p b l q h0 h1 a) = l a :=
  actualFiberPointTotal p b (l a) (q a) (h0 a) (h1 a)

private theorem actualMixedFiberLiftPath {A : Type uA} [TopologicalSpace A]
    {E B : TopCat.{uB}} (p : E ⟶ B) (b : B)
    (l : C(A, E)) (q : C(A, TopCat.pathObject B))
    (h0 : ∀ a, q a 0 = p (l a)) (h1 : ∀ a, q a 1 = b) (a : A) :
    TopCat.homotopyFiberPath p b (actualMixedFiberLift p b l q h0 h1 a) = q a :=
  actualFiberPointPath p b (l a) (q a) (h0 a) (h1 a)

private abbrev actualCompletedUnit
    (C : Type uC) [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] : SInverse (Core C) (Core C) :=
  (SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))

private abbrev actualCompletedUnitVertex
    (C : Type uC) [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    SSet.toTop.obj (nerve (SInverse (Core C) (Core C)) : SSet.{max uC vC}) :=
  SSet.realizedVertex (ComposableArrows.mk₀ (actualCompletedUnit C))

private theorem actualOriginalZeroTotalRealization
    (C : Type uC) [Category.{vC} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    (TopCat.homotopyFiberToTotal (actualOriginalProjection C) (actualOriginalZero C)).hom.comp
        (completedCoreToOriginalHomotopyFiber (C := C)).hom =
      realizedNerveFunctorMap (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
        FixedTargetExtension.localizedForget (0 : C)) := by
  let k := completedCoreToOriginalHomotopyFiber (C := C)
  let p := TopCat.homotopyFiberToTotal (actualOriginalProjection C) (actualOriginalZero C)
  have h := congrArg (fun m => m.hom) (completedCoreToOriginalHomotopyFiber_toTotal (C := C))
  exact (TopCat.hom_comp k p).symm.trans
    (h.trans (realizedNerveFunctorMap_commonUpFrame
      (FixedTargetExtension.zeroLocalizedFunctor (C := C) ⋙
        FixedTargetExtension.localizedForget (0 : C))).symm)

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

private theorem actualOriginalForwardTotalSource
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMapHomotopy (FixedTargetExtension.completedZeroTotalNaturalityIso F).hom
        (0, x) =
      realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap F)
        (TopCat.homotopyFiberToTotal (actualOriginalProjection C) (actualOriginalZero C)
          (completedCoreToOriginalHomotopyFiber (C := C) x)) := by
  let Z := FixedTargetExtension.zeroLocalizedFunctor (C := C)
  let Y := FixedTargetExtension.localizedForget (0 : C)
  let T := ExtensionCategory.stabilizedFunctorMap F
  have hAssoc : (Z ⋙ Y) ⋙ T = Z ⋙ Y ⋙ T := by
    refine Functor.hext (fun _ => rfl) ?_
    intro a b f
    exact heq_of_eq rfl
  have hMap : realizedNerveFunctorMap (Z ⋙ Y ⋙ T) =
      (realizedNerveFunctorMap T).comp
        ((TopCat.homotopyFiberToTotal (actualOriginalProjection C) (actualOriginalZero C)).hom.comp
          (completedCoreToOriginalHomotopyFiber (C := C)).hom) :=
    (congrArg realizedNerveFunctorMap hAssoc.symm).trans
      ((realizedNerveFunctorMap_comp_independent (Z ⋙ Y) T).trans
        (congrArg (fun m => (realizedNerveFunctorMap T).comp m)
          (actualOriginalZeroTotalRealization C).symm))
  exact ((realizedNerveFunctorMapHomotopy
    (FixedTargetExtension.completedZeroTotalNaturalityIso F).hom).map_zero_left x).trans
      (congrArg (fun m => m x) hMap)

private theorem actualOriginalForwardTotalTarget
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    realizedNerveFunctorMapHomotopy (FixedTargetExtension.completedZeroTotalNaturalityIso F).hom
        (1, x) =
      TopCat.homotopyFiberToTotal (actualOriginalProjection D) (actualOriginalZero D)
        (completedCoreToOriginalHomotopyFiber (C := D)
          (realizedNerveFunctorMap (CategoryTheory.CoreLocalizationComparison.completedCoreFunctor
              F) x)) := by
  let K := CategoryTheory.CoreLocalizationComparison.completedCoreFunctor F
  let Z := FixedTargetExtension.zeroLocalizedFunctor (C := D)
  let Y := FixedTargetExtension.localizedForget (0 : D)
  have hMap : realizedNerveFunctorMap (K ⋙ Z ⋙ Y) =
      ((TopCat.homotopyFiberToTotal (actualOriginalProjection D) (actualOriginalZero D)).hom.comp
        (completedCoreToOriginalHomotopyFiber (C := D)).hom).comp (realizedNerveFunctorMap K) :=
    (realizedNerveFunctorMap_comp_independent K (Z ⋙ Y)).trans
      (congrArg (fun m => m.comp (realizedNerveFunctorMap K))
        (actualOriginalZeroTotalRealization D).symm)
  exact ((realizedNerveFunctorMapHomotopy
    (FixedTargetExtension.completedZeroTotalNaturalityIso F).hom).map_one_left x).trans
      (congrArg (fun m => m x) hMap)

private theorem actualMixedZeroVertex :
    QuillenMixedUniverseTransport.mixedNQRealMap F (actualOriginalZero C) =
      SSet.realizedVertex
        (ComposableArrows.mk₀ ((QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C))) :=
  (congrArg (QuillenMixedUniverseTransport.mixedNQRealMap F)
    (NQReal.basepoint_eq_realizedVertex C).symm).trans
      (QuillenMixedUniverseTransport.mixedNQRealMap_zeroVertex F)

private def actualOriginalProjectedTrace :
    Path (QuillenMixedUniverseTransport.mixedNQRealMap F (actualOriginalZero C))
      (actualOriginalZero D) := by
  let T := SInverse (Core C) (Core C)
  let L := (Functor.const T).obj ((QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C))
  let R := (Functor.const T).obj (⟨(0 : D)⟩ : QuillenQ D)
  let H := realizedNerveFunctorMapHomotopy (FixedTargetExtension.completedZeroUniformBaseIso F).hom
  have hL : QuillenMixedUniverseTransport.mixedNQRealMap F (actualOriginalZero C) =
      realizedNerveFunctorMap L (actualCompletedUnitVertex C) :=
    (actualMixedZeroVertex F).trans
      (realizedNerveFunctorMap_vertex L (actualCompletedUnit C)).symm
  have hR : actualOriginalZero D = realizedNerveFunctorMap R (actualCompletedUnitVertex C) :=
    (realizedNerveFunctorMap_vertex R (actualCompletedUnit C)).symm
  exact (H.evalAt (actualCompletedUnitVertex C)).cast hL hR

private theorem actualOriginalProjectedTraceValue (t : unitInterval) :
    actualOriginalProjectedTrace F t =
      realizedNerveFunctorMapHomotopy (FixedTargetExtension.completedZeroUniformBaseIso F).hom
        (t, actualCompletedUnitVertex C) := rfl

private theorem actualOriginalForwardTotalBaseTrace (t : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    actualOriginalProjection D
        (realizedNerveFunctorMapHomotopy (FixedTargetExtension.completedZeroTotalNaturalityIso
            F).hom
          (t, x)) = actualOriginalProjectedTrace F t :=
  (FixedTargetExtension.completedZeroTotalFamily_forward_literal_target F t x).trans
    ((FixedTargetExtension.completedZeroProjectedOriginalFamily_forward_value F t x).trans
      ((FixedTargetExtension.completedZeroUniformBaseHomotopy_forward_uniform F t x
        (actualCompletedUnitVertex C)).trans (actualOriginalProjectedTraceValue F t).symm))

private theorem actualOriginalProjectedTraceCanonical :
    (actualOriginalProjectedTrace F).Homotopic (actualOriginalCanonicalRoot F) := by
  let T := SInverse (Core C) (Core C)
  let a := actualCompletedUnit C
  let x := actualCompletedUnitVertex C
  let L := (Functor.const T).obj ((QuillenQ.map F).obj (⟨(0 : C)⟩ : QuillenQ C))
  let R := (Functor.const T).obj (⟨(0 : D)⟩ : QuillenQ D)
  let alpha : L ⟶ R := (FixedTargetExtension.completedZeroUniformBaseIso F).hom
  let H := realizedNerveFunctorMapHomotopy alpha
  let e := TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (alpha.app a)))
  let hm := actualMixedZeroVertex F
  have hActual := (realizedNerveFunctorMapHomotopy_vertex alpha a).pathCast hm rfl
  have hTrace : (((H.evalAt x).cast (realizedNerveFunctorMap_vertex L a).symm
      (realizedNerveFunctorMap_vertex R a).symm).cast hm rfl) =
      actualOriginalProjectedTrace F := by
    apply Path.ext
    funext t
    exact (actualOriginalProjectedTraceValue F t).symm
  have hEdge : e.cast hm rfl = actualOriginalCanonicalRoot F := by
    apply Path.ext
    funext t
    have hApp : alpha.app a = (QuillenQ.zeroComparisonIso F).hom :=
      FixedTargetExtension.completedZeroUniformBaseIso_hom_app F a
    have hE := congrArg (fun f => TopCat.pathEquiv
      (SSet.realizedEdgePath (nerve.edgeMk f)) t) hApp
    exact hE.trans (QuillenMixedUniverseTransport.mixedNQRootPath_value F t).symm
  exact hTrace ▸ hEdge ▸ hActual

private def actualOriginalInitialRootHomotopy :
    ((Path.refl (QuillenMixedUniverseTransport.mixedNQRealMap F (actualOriginalZero C))).trans
      (actualOriginalCanonicalRoot F)).Homotopy (actualOriginalProjectedTrace F) :=
  (Path.Homotopy.reflTrans (actualOriginalCanonicalRoot F)).trans
    (actualOriginalProjectedTraceCanonical F).symm.some

private theorem actualOriginalSourceFullPathValue
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C))))
    (t : TopCat.I.{max uD vD}) :
    TopCat.homotopyFiberPath (actualOriginalProjection D) (actualOriginalZero D)
      (mixedOriginalZeroFiberMap F (completedCoreToOriginalHomotopyFiber (C := C) x)) t =
    ((Path.refl (QuillenMixedUniverseTransport.mixedNQRealMap F (actualOriginalZero C))).trans
      (actualOriginalCanonicalRoot F)) (TopCat.I.homeomorph t) := by
  rw [mixedOriginalZeroFiberMap, actualMixedFiberMapPath]
  change (((actualOriginalEndingPath (actualOriginalProjection C) (actualOriginalZero C)
      (completedCoreToOriginalHomotopyFiber (C := C) x)).map
        (QuillenMixedUniverseTransport.mixedNQRealMap F).continuous).trans
      (actualOriginalCanonicalRoot F)) (TopCat.I.homeomorph t) = _
  rw [Path.trans_apply, Path.trans_apply]
  split
  · exact congrArg (QuillenMixedUniverseTransport.mixedNQRealMap F)
      (completedCoreToOriginalHomotopyFiber_path_const (C := C) x _)
  · rfl

private abbrev actualOriginalInitialTotalMap :
    C(SSet.toTop.obj (nerve (SInverse (Core C) (Core C))),
      SSet.toTop.obj (nerve (SInverse (Core D) (ExtensionCategory D)))) :=
  (realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap F)).comp
    ((TopCat.homotopyFiberToTotal (actualOriginalProjection C) (actualOriginalZero C)).hom.comp
      (completedCoreToOriginalHomotopyFiber (C := C)).hom)

private theorem actualOriginalInitialTotalBase
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    actualOriginalProjection D (actualOriginalInitialTotalMap F x) =
      QuillenMixedUniverseTransport.mixedNQRealMap F (actualOriginalZero C) :=
  (congrArg (actualOriginalProjection D) (actualOriginalForwardTotalSource F x)).symm.trans
    ((actualOriginalForwardTotalBaseTrace F 0 x).trans (actualOriginalProjectedTrace F).source)

private def actualOriginalInitialTracePathMap :
    C(SSet.toTop.obj (nerve (SInverse (Core C) (Core C))),
      TopCat.pathObject (actualOriginalBase D)) := by
  let k : C(SSet.toTop.obj (nerve (SInverse (Core C) (Core C))) ×
      TopCat.I.{max uD vD}, actualOriginalBase D) :=
    { toFun := fun z => actualOriginalProjectedTrace F
        (TopCat.I.homeomorph.{max uD vD} z.2)
      continuous_toFun := (actualOriginalProjectedTrace F).continuous.comp
        (TopCat.I.homeomorph.{max uD vD}.continuous.comp continuous_snd) }
  exact ContinuousMap.curry k

private def actualOriginalInitialTraceFiberMap :
    C(SSet.toTop.obj (nerve (SInverse (Core C) (Core C))),
      TopCat.homotopyFiber (actualOriginalProjection D) (actualOriginalZero D)) := by
  let p : SSet.toTop.obj (nerve (SInverse (Core D) (ExtensionCategory D))) ⟶
      actualOriginalBase D := actualOriginalProjection D
  let b : actualOriginalBase D := actualOriginalZero D
  let l : C(SSet.toTop.obj (nerve (SInverse (Core C) (Core C))),
      SSet.toTop.obj (nerve (SInverse (Core D) (ExtensionCategory D)))) :=
    actualOriginalInitialTotalMap F
  let q : C(SSet.toTop.obj (nerve (SInverse (Core C) (Core C))),
      TopCat.pathObject (actualOriginalBase D)) := actualOriginalInitialTracePathMap F
  have h0 (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
      q x (0 : TopCat.I.{max uD vD}) = p (l x) := by
    calc
      q x (0 : TopCat.I.{max uD vD}) = actualOriginalProjectedTrace F
          (TopCat.I.homeomorph.{max uD vD} (0 : TopCat.I.{max uD vD})) := rfl
      _ = QuillenMixedUniverseTransport.mixedNQRealMap F (actualOriginalZero C) :=
        (congrArg (actualOriginalProjectedTrace F)
          TopCat.I.homeomorph_zero.{max uD vD}).trans (actualOriginalProjectedTrace F).source
      _ = p (l x) := (actualOriginalInitialTotalBase F x).symm
  have h1 (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
      q x (1 : TopCat.I.{max uD vD}) = b := by
    calc
      q x (1 : TopCat.I.{max uD vD}) = actualOriginalProjectedTrace F
          (TopCat.I.homeomorph.{max uD vD} (1 : TopCat.I.{max uD vD})) := rfl
      _ = b := (congrArg (actualOriginalProjectedTrace F)
        TopCat.I.homeomorph_one.{max uD vD}).trans (actualOriginalProjectedTrace F).target
  exact actualMixedFiberLift p b l q h0 h1

private theorem actualOriginalInitialTraceFiberTotal
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    TopCat.homotopyFiberToTotal (actualOriginalProjection D) (actualOriginalZero D)
      (actualOriginalInitialTraceFiberMap F x) = actualOriginalInitialTotalMap F x := by
  dsimp only [actualOriginalInitialTraceFiberMap]
  exact actualMixedFiberLiftTotal (actualOriginalProjection D) (actualOriginalZero D) _ _ _ _ x

private theorem actualOriginalInitialTraceFiberPath
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C))))
    (t : TopCat.I.{max uD vD}) :
    TopCat.homotopyFiberPath (actualOriginalProjection D) (actualOriginalZero D)
      (actualOriginalInitialTraceFiberMap F x) t =
        actualOriginalProjectedTrace F (TopCat.I.homeomorph t) := by
  rw [actualOriginalInitialTraceFiberMap, actualMixedFiberLiftPath]
  rfl

private def actualOriginalRootCorrectionPathFamily :
    C(unitInterval × SSet.toTop.obj (nerve (SInverse (Core C) (Core C))),
      TopCat.pathObject (actualOriginalBase D)) := by
  let k : C((unitInterval × SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) ×
      TopCat.I.{max uD vD}, actualOriginalBase D) :=
    { toFun := fun z => actualOriginalInitialRootHomotopy F
        (z.1.1, TopCat.I.homeomorph.{max uD vD} z.2)
      continuous_toFun := (actualOriginalInitialRootHomotopy F).toHomotopy.continuous.comp
        ((continuous_fst.comp continuous_fst).prodMk
          (TopCat.I.homeomorph.{max uD vD}.continuous.comp continuous_snd)) }
  exact ContinuousMap.curry k

private def actualOriginalRootCorrectionFamily :
    ContinuousMap.Homotopy
      ((mixedOriginalZeroFiberMap F).comp (completedCoreToOriginalHomotopyFiber (C := C)).hom)
      (actualOriginalInitialTraceFiberMap F) := by
  let p : SSet.toTop.obj (nerve (SInverse (Core D) (ExtensionCategory D))) ⟶
      actualOriginalBase D := actualOriginalProjection D
  let b : actualOriginalBase D := actualOriginalZero D
  let l : C(unitInterval × SSet.toTop.obj (nerve (SInverse (Core C) (Core C))),
      SSet.toTop.obj (nerve (SInverse (Core D) (ExtensionCategory D)))) :=
    (actualOriginalInitialTotalMap F).comp ContinuousMap.snd
  let q : C(unitInterval × SSet.toTop.obj (nerve (SInverse (Core C) (Core C))),
      TopCat.pathObject (actualOriginalBase D)) := actualOriginalRootCorrectionPathFamily F
  have h0 (z : unitInterval × SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
      q z (0 : TopCat.I.{max uD vD}) = p (l z) := by
    calc
      q z (0 : TopCat.I.{max uD vD}) = actualOriginalInitialRootHomotopy F
          (z.1, TopCat.I.homeomorph.{max uD vD} (0 : TopCat.I.{max uD vD})) := rfl
      _ = QuillenMixedUniverseTransport.mixedNQRealMap F (actualOriginalZero C) :=
        (congrArg (fun t => actualOriginalInitialRootHomotopy F (z.1, t))
          TopCat.I.homeomorph_zero.{max uD vD}).trans
            (Path.Homotopy.source (actualOriginalInitialRootHomotopy F) z.1)
      _ = p (l z) := (actualOriginalInitialTotalBase F z.2).symm
  have h1 (z : unitInterval × SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
      q z (1 : TopCat.I.{max uD vD}) = b := by
    calc
      q z (1 : TopCat.I.{max uD vD}) = actualOriginalInitialRootHomotopy F
          (z.1, TopCat.I.homeomorph.{max uD vD} (1 : TopCat.I.{max uD vD})) := rfl
      _ = b := (congrArg (fun t => actualOriginalInitialRootHomotopy F (z.1, t))
        TopCat.I.homeomorph_one.{max uD vD}).trans
          (Path.Homotopy.target (actualOriginalInitialRootHomotopy F) z.1)
  let m : C(unitInterval × SSet.toTop.obj (nerve (SInverse (Core C) (Core C))),
      TopCat.homotopyFiber p b) := actualMixedFiberLift p b l q h0 h1
  refine { toContinuousMap := m, map_zero_left := ?_, map_one_left := ?_ }
  · intro x
    apply actualFiberPointExt p b
    · exact (actualMixedFiberLiftTotal p b l q h0 h1 (0, x)).trans
        (mixedOriginalZeroFiberMap_toTotal F (completedCoreToOriginalHomotopyFiber (C := C) x)).symm
    · apply ContinuousMap.ext
      intro t
      have hPath := congrArg (fun r : TopCat.pathObject (actualOriginalBase D) => r t)
        (actualMixedFiberLiftPath p b l q h0 h1 (0, x))
      exact hPath.trans
        (((actualOriginalInitialRootHomotopy F).toHomotopy.map_zero_left
          (TopCat.I.homeomorph t)).trans (actualOriginalSourceFullPathValue F x t).symm)
  · intro x
    apply actualFiberPointExt p b
    · exact (actualMixedFiberLiftTotal p b l q h0 h1 (1, x)).trans
        (actualOriginalInitialTraceFiberTotal F x).symm
    · apply ContinuousMap.ext
      intro t
      have hPath := congrArg (fun r : TopCat.pathObject (actualOriginalBase D) => r t)
        (actualMixedFiberLiftPath p b l q h0 h1 (1, x))
      exact hPath.trans
        (((actualOriginalInitialRootHomotopy F).toHomotopy.map_one_left
          (TopCat.I.homeomorph t)).trans (actualOriginalInitialTraceFiberPath F x t).symm)

private def actualOriginalTailTime (s t : unitInterval) : unitInterval :=
  ⟨(s : ℝ) + (1 - (s : ℝ)) * (t : ℝ),
    ⟨add_nonneg s.2.1 (mul_nonneg (sub_nonneg.mpr s.2.2) t.2.1),
      by
        calc
          (s : ℝ) + (1 - (s : ℝ)) * (t : ℝ) ≤ (s : ℝ) + (1 - (s : ℝ)) * 1 :=
            add_le_add le_rfl
              (mul_le_mul_of_nonneg_left t.2.2 (sub_nonneg.mpr s.2.2))
          _ = 1 := by ring⟩⟩

private theorem actualOriginalTailTimeContinuous :
    Continuous (fun st : unitInterval × unitInterval => actualOriginalTailTime st.1 st.2) := by
  apply Continuous.subtype_mk
  fun_prop

private theorem actualOriginalTailTimeLeft (s : unitInterval) :
    actualOriginalTailTime s 0 = s := by
  apply Subtype.ext
  simp [actualOriginalTailTime]

private theorem actualOriginalTailTimeRight (s : unitInterval) :
    actualOriginalTailTime s 1 = 1 := by
  apply Subtype.ext
  simp [actualOriginalTailTime]

private theorem actualOriginalTailTimeZero (t : unitInterval) :
    actualOriginalTailTime 0 t = t := by
  apply Subtype.ext
  simp [actualOriginalTailTime]

private theorem actualOriginalTailTimeOne (t : unitInterval) :
    actualOriginalTailTime 1 t = 1 := by
  apply Subtype.ext
  simp [actualOriginalTailTime]

private def actualOriginalFullTailPathFamily :
    C(unitInterval × SSet.toTop.obj (nerve (SInverse (Core C) (Core C))),
      TopCat.pathObject (actualOriginalBase D)) := by
  let k : C((unitInterval × SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) ×
      TopCat.I.{max uD vD}, actualOriginalBase D) :=
    { toFun := fun z => actualOriginalProjectedTrace F
        (actualOriginalTailTime z.1.1 (TopCat.I.homeomorph.{max uD vD} z.2))
      continuous_toFun := (actualOriginalProjectedTrace F).continuous.comp
        (actualOriginalTailTimeContinuous.comp
          ((continuous_fst.comp continuous_fst).prodMk
            (TopCat.I.homeomorph.{max uD vD}.continuous.comp continuous_snd))) }
  exact ContinuousMap.curry k

private def actualOriginalFullTailFiberFamily :
    ContinuousMap.Homotopy (actualOriginalInitialTraceFiberMap F)
      ((completedCoreToOriginalHomotopyFiber (C := D)).hom.comp
        (realizedNerveFunctorMap (CategoryTheory.CoreLocalizationComparison.completedCoreFunctor
            F))) := by
  let p : SSet.toTop.obj (nerve (SInverse (Core D) (ExtensionCategory D))) ⟶
      actualOriginalBase D := actualOriginalProjection D
  let b : actualOriginalBase D := actualOriginalZero D
  let H := realizedNerveFunctorMapHomotopy (FixedTargetExtension.completedZeroTotalNaturalityIso
      F).hom
  let l : C(unitInterval × SSet.toTop.obj (nerve (SInverse (Core C) (Core C))),
      SSet.toTop.obj (nerve (SInverse (Core D) (ExtensionCategory D)))) := H.toContinuousMap
  let q : C(unitInterval × SSet.toTop.obj (nerve (SInverse (Core C) (Core C))),
      TopCat.pathObject (actualOriginalBase D)) := actualOriginalFullTailPathFamily F
  have h0 (z : unitInterval × SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
      q z (0 : TopCat.I.{max uD vD}) = p (l z) := by
    calc
      q z (0 : TopCat.I.{max uD vD}) = actualOriginalProjectedTrace F
          (actualOriginalTailTime z.1
            (TopCat.I.homeomorph.{max uD vD} (0 : TopCat.I.{max uD vD}))) := rfl
      _ = actualOriginalProjectedTrace F z.1 := congrArg (actualOriginalProjectedTrace F)
        ((congrArg (actualOriginalTailTime z.1)
          TopCat.I.homeomorph_zero.{max uD vD}).trans (actualOriginalTailTimeLeft z.1))
      _ = p (l z) := (actualOriginalForwardTotalBaseTrace F z.1 z.2).symm
  have h1 (z : unitInterval × SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
      q z (1 : TopCat.I.{max uD vD}) = b := by
    calc
      q z (1 : TopCat.I.{max uD vD}) = actualOriginalProjectedTrace F
          (actualOriginalTailTime z.1
            (TopCat.I.homeomorph.{max uD vD} (1 : TopCat.I.{max uD vD}))) := rfl
      _ = actualOriginalProjectedTrace F 1 := congrArg (actualOriginalProjectedTrace F)
        ((congrArg (actualOriginalTailTime z.1)
          TopCat.I.homeomorph_one.{max uD vD}).trans (actualOriginalTailTimeRight z.1))
      _ = b := (actualOriginalProjectedTrace F).target
  let m : C(unitInterval × SSet.toTop.obj (nerve (SInverse (Core C) (Core C))),
      TopCat.homotopyFiber p b) := actualMixedFiberLift p b l q h0 h1
  refine { toContinuousMap := m, map_zero_left := ?_, map_one_left := ?_ }
  · intro x
    apply actualFiberPointExt p b
    · exact (actualMixedFiberLiftTotal p b l q h0 h1 (0, x)).trans
        ((actualOriginalForwardTotalSource F x).trans (actualOriginalInitialTraceFiberTotal F
            x).symm)
    · apply ContinuousMap.ext
      intro t
      have hPath := congrArg (fun r : TopCat.pathObject (actualOriginalBase D) => r t)
        (actualMixedFiberLiftPath p b l q h0 h1 (0, x))
      exact hPath.trans
        ((congrArg (actualOriginalProjectedTrace F)
          (actualOriginalTailTimeZero (TopCat.I.homeomorph t))).trans
            (actualOriginalInitialTraceFiberPath F x t).symm)
  · intro x
    apply actualFiberPointExt p b
    · exact (actualMixedFiberLiftTotal p b l q h0 h1 (1, x)).trans
        (actualOriginalForwardTotalTarget F x)
    · apply ContinuousMap.ext
      intro t
      have hPath := congrArg (fun r : TopCat.pathObject (actualOriginalBase D) => r t)
        (actualMixedFiberLiftPath p b l q h0 h1 (1, x))
      exact hPath.trans
        ((congrArg (actualOriginalProjectedTrace F)
          (actualOriginalTailTimeOne (TopCat.I.homeomorph t))).trans
            ((actualOriginalProjectedTrace F).target.trans
              (completedCoreToOriginalHomotopyFiber_path_const (C := D)
                (realizedNerveFunctorMap
                    (CategoryTheory.CoreLocalizationComparison.completedCoreFunctor F) x) t).symm))

/-- The SAME original completed-Core maps satisfy the whole mixed full-fiber
square, with internally constructed total, full-path and canonical-root families. -/
public def completedCoreOriginalFiberNaturalityHomotopy :
    ContinuousMap.Homotopy
      ((mixedOriginalZeroFiberMap F).comp (completedCoreToOriginalHomotopyFiber (C := C)).hom)
      ((completedCoreToOriginalHomotopyFiber (C := D)).hom.comp
        (realizedNerveFunctorMap (CategoryTheory.CoreLocalizationComparison.completedCoreFunctor
            F))) :=
  (actualOriginalRootCorrectionFamily F).trans (actualOriginalFullTailFiberFamily F)

end AlgebraicKTheory.OriginalQZeroComparison

end


/-!
# Whole actual root family and every original fiber-homotopy value

The getters retain the exact chosen initial root-path homotopy used by the
original full fiber family. Every total and full carried-path time keeps
that same family and the original half-interval clock. No choice is
normalized, replaced, or assumed stationary.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalActionCategory
open CategoryTheory.CoreLocalizationComparison
open scoped ZeroObject CategoryTheory.Limits.CoreBiprodMonoidal
  CategoryTheory.MonoidalCategory ContinuousMap Simplicial

attribute [local instance] AlgebraicKTheory.ExtensionCategory.leftSumAction
attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

universe uA uB uC vC uD vD

namespace AlgebraicKTheory.OriginalQZeroComparison

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- The WHOLE actual uniform trace used by the SAME original full fiber family. -/
public def completedCoreOriginalFiberProjectedTrace :
    Path (QuillenMixedUniverseTransport.mixedNQRealMap F
        (SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : C)⟩ : QuillenQ C))))
      (SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : D)⟩ : QuillenQ D))) :=
  actualOriginalProjectedTrace F

/-- EVERY time is the original whole projected-family value at the SAME original unit. -/
public theorem completedCoreOriginalFiberProjectedTrace_value (t : unitInterval) :
    completedCoreOriginalFiberProjectedTrace F t =
      realizedNerveFunctorMapHomotopy (FixedTargetExtension.completedZeroUniformBaseIso F).hom
        (t, SSet.realizedVertex (ComposableArrows.mk₀
          ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))) :=
  actualOriginalProjectedTraceValue F t

/-- The proper getter retains the EXACT chosen initial root-path family of
the SAME full fiber homotopy, including every original witness value. -/
public def completedCoreOriginalFiberInitialRootFamily :
    ((Path.refl (QuillenMixedUniverseTransport.mixedNQRealMap F
        (SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : C)⟩ : QuillenQ C))))).trans
      ((QuillenMixedUniverseTransport.mixedNQRootPath F).cast
        (congrArg (QuillenMixedUniverseTransport.mixedNQRealMap F)
          (NQReal.basepoint_eq_realizedVertex C).symm)
        (NQReal.basepoint_eq_realizedVertex D).symm)).Homotopy
      (completedCoreOriginalFiberProjectedTrace F) := actualOriginalInitialRootHomotopy F

private theorem actualOriginalRootCorrectionTotalValue (s : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    TopCat.homotopyFiberToTotal (actualOriginalProjection D) (actualOriginalZero D)
      (actualOriginalRootCorrectionFamily F (s, x)) = actualOriginalInitialTotalMap F x := by
  dsimp only [actualOriginalRootCorrectionFamily]
  exact actualMixedFiberLiftTotal (actualOriginalProjection D) (actualOriginalZero D) _ _ _ _ (s, x)

private theorem actualOriginalRootCorrectionPathValue (s : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) (t : TopCat.I.{max uD vD}) :
    TopCat.homotopyFiberPath (actualOriginalProjection D) (actualOriginalZero D)
      (actualOriginalRootCorrectionFamily F (s, x)) t =
      actualOriginalInitialRootHomotopy F (s, TopCat.I.homeomorph t) := by
  have hPath :
      TopCat.homotopyFiberPath (actualOriginalProjection D) (actualOriginalZero D)
        ((actualOriginalRootCorrectionFamily F).toContinuousMap (s, x)) =
      actualOriginalRootCorrectionPathFamily F (s, x) := by
    dsimp only [actualOriginalRootCorrectionFamily]
    exact actualMixedFiberLiftPath (actualOriginalProjection D) (actualOriginalZero D)
      _ _ _ _ (s, x)
  exact (congrArg (fun r : TopCat.pathObject (actualOriginalBase D) => r t) hPath).trans rfl

private theorem actualOriginalFullTailFiberTotalValue (s : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    TopCat.homotopyFiberToTotal (actualOriginalProjection D) (actualOriginalZero D)
      (actualOriginalFullTailFiberFamily F (s, x)) =
      realizedNerveFunctorMapHomotopy (FixedTargetExtension.completedZeroTotalNaturalityIso F).hom
        (s, x) := by
  dsimp only [actualOriginalFullTailFiberFamily]
  exact actualMixedFiberLiftTotal (actualOriginalProjection D) (actualOriginalZero D) _ _ _ _ (s, x)

private theorem actualOriginalFullTailFiberPathValue (s : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) (t : TopCat.I.{max uD vD}) :
    TopCat.homotopyFiberPath (actualOriginalProjection D) (actualOriginalZero D)
      (actualOriginalFullTailFiberFamily F (s, x)) t =
      actualOriginalProjectedTrace F (actualOriginalTailTime s (TopCat.I.homeomorph t)) := by
  change TopCat.homotopyFiberPath (actualOriginalProjection D) (actualOriginalZero D)
    ((actualOriginalFullTailFiberFamily F).toContinuousMap (s, x)) t = _
  dsimp only [actualOriginalFullTailFiberFamily]
  rw [actualMixedFiberLiftPath]
  rfl

private theorem actualOriginalTailTimeConvex (s t : unitInterval) :
    actualOriginalTailTime s t = Set.Icc.convexComb s 1 t := by
  apply Subtype.ext
  dsimp only [actualOriginalTailTime]
  rw [Set.Icc.coe_convexComb, Set.Icc.coe_one]
  ring

/-- EVERY source point and time uses the SAME literal total coordinate of
the original root correction or original152 total family, on the original clock. -/
public theorem completedCoreOriginalFiberNaturalityHomotopy_total_value (s : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) :
    TopCat.homotopyFiberToTotal
        (SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
          (ExtensionCategory.localizedTarget (C := D))))
        (SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : D)⟩ : QuillenQ D)))
        (completedCoreOriginalFiberNaturalityHomotopy F (s, x)) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        realizedNerveFunctorMap (ExtensionCategory.stabilizedFunctorMap F)
          (TopCat.homotopyFiberToTotal
            (SSet.toTop.map (nerveMapCommonHom.{uC, max uC vC, 0}
              (ExtensionCategory.localizedTarget (C := C))))
            (SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : C)⟩ : QuillenQ C)))
            (completedCoreToOriginalHomotopyFiber (C := C) x))
      else
        realizedNerveFunctorMapHomotopy (FixedTargetExtension.completedZeroTotalNaturalityIso F).hom
          (⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 hs).le, s.2.2⟩⟩, x) := by
  rw [completedCoreOriginalFiberNaturalityHomotopy, ContinuousMap.Homotopy.trans_apply]
  split
  · exact actualOriginalRootCorrectionTotalValue F _ x
  · exact actualOriginalFullTailFiberTotalValue F _ x

/-- EVERY full carried-path time retains the EXACT original chosen root
family or original projected tail, with the original homotopy and path clocks. -/
public theorem completedCoreOriginalFiberNaturalityHomotopy_path_value (s : unitInterval)
    (x : SSet.toTop.obj (nerve (SInverse (Core C) (Core C)))) (t : TopCat.I.{max uD vD}) :
    TopCat.homotopyFiberPath
        (SSet.toTop.map (nerveMapCommonHom.{uD, max uD vD, 0}
          (ExtensionCategory.localizedTarget (C := D))))
        (SSet.realizedVertex (ComposableArrows.mk₀ (⟨(0 : D)⟩ : QuillenQ D)))
        (completedCoreOriginalFiberNaturalityHomotopy F (s, x)) t =
      if hs : (s : ℝ) ≤ 1 / 2 then
        completedCoreOriginalFiberInitialRootFamily F
          (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩,
            TopCat.I.homeomorph t)
      else
        completedCoreOriginalFiberProjectedTrace F
          (Set.Icc.convexComb
            ⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 hs).le, s.2.2⟩⟩ 1 (TopCat.I.homeomorph t)) := by
  rw [completedCoreOriginalFiberNaturalityHomotopy, ContinuousMap.Homotopy.trans_apply]
  split
  · exact actualOriginalRootCorrectionPathValue F _ x t
  · exact (actualOriginalFullTailFiberPathValue F _ x t).trans
      (congrArg (completedCoreOriginalFiberProjectedTrace F) (actualOriginalTailTimeConvex _ _))

end AlgebraicKTheory.OriginalQZeroComparison

end
