/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceCoefficientSourceGEN
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceCoefficientSourceData
import MathlibExt.CategoryTheory.Monoidal.Mod.ClosedComponents
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.NativeSelectedUnitTransport
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceCoefficientFirstSource

/-!
# Balanced action of the actual free-module source

The original module tensor/internal-Hom adjunction sends every map to the
regular coefficient module to its full target action. Its free-at-index
projection retains the Day generator and final index braid. These ordinary
category and adjunction laws support the native first-source GEN proof.
-/

set_option autoImplicit false
noncomputable section
universe uC vC uI vI uV vV uD vD u v uT vT uD' vD'
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed CategoryTheory.MonObj ExternalProduct

private theorem tensor_unit_source_comp
    {W : Type uC} [Category.{vC} W] [MonoidalCategory W] {M M' : W}
    (f : M ⟶ M') (q : M' ⟶ (𝟙_ W)) (N : W) :
    ((f ≫ q) ⊗ₘ 𝟙 N) ≫ (λ_ N).hom =
      (f ⊗ₘ 𝟙 N) ≫ ((q ⊗ₘ 𝟙 N) ≫ (λ_ N).hom) := by
  rw [tensorHom_id, tensorHom_id, tensorHom_id, comp_whiskerRight, Category.assoc]

private theorem day_comp_component
    {J : Type uI} [Category.{vI} J] [MonoidalCategory J]
    {W : Type uV} [Category.{vV} W] [MonoidalCategory W]
    {P Q R : DayFunctor J W} (f : P ⟶ Q) (g : Q ⟶ R) (n : J) :
    (f ≫ g).natTrans.app n = f.natTrans.app n ≫ g.natTrans.app n := rfl


namespace NativeOmegaRecovery.NativeSymmetricSourceGEN.BalancedSourceAction
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]
  (A : CommMon C)
/-- The original whole tensor record on modules over the given coefficient. -/
local instance sourceModuleMonoidal : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
/-- The original whole internal-Hom record on those same modules. -/
local instance sourceModuleClosed : MonoidalClosed (Mod C A.X) := Mod.instMonoidalClosed A

private theorem balanced_curry_projection (M N K : Mod C A.X)
    (p : ((Mod.relativeTensor A).obj M).obj N ⟶ K) :
    ((Mod.relativeTensorInternalHomAdjunction A M).homEquiv N K p).hom ≫
      Mod.internalHomι A M K = MonoidalClosed.curry (Mod.relativeTensorπ A M N ≫ p.hom) := by
  rw [Adjunction.homEquiv_unit]
  change (((Mod.coevaluation A M).app N).hom ≫ ((Mod.internalHom A M).map p).hom) ≫
    Mod.internalHomι A M K = _
  rw [Category.assoc, Mod.internalHomMap, ← Category.assoc, Mod.coevaluation_ι]
  exact (MonoidalClosed.curry_natural_right _ _).symm

/-- The same given module map and original module unitor are transposed by
exactly the original balanced tensor/internal-Hom adjunction. -/
def action (M : Mod C A.X) (q : M ⟶ Mod.regular A.X) (N : Mod C A.X) :
    N ⟶ (Mod.internalHom A M).obj N :=
  (Mod.relativeTensorInternalHomAdjunction A M).homEquiv N N
    (Mod.relativeTensorMap A q (𝟙 N) ≫ (λ_ N).hom)

/-- Every original source parameter map retains that same full balanced adjunct. -/
theorem action_pre {M M' : Mod C A.X} (f : M ⟶ M') (q : M' ⟶ Mod.regular A.X)
    (N : Mod C A.X) :
    action A M (f ≫ q) N = action A M' q N ≫ (MonoidalClosed.pre f).app N := by
  let p := Mod.relativeTensorMap A q (𝟙 N) ≫ (λ_ N).hom
  have ht : Mod.relativeTensorMap A (f ≫ q) (𝟙 N) ≫ (λ_ N).hom =
      Mod.relativeTensorMap A f (𝟙 N) ≫ p := by
    let qUnit : M' ⟶ (𝟙_ (Mod C A.X)) := q
    exact tensor_unit_source_comp f qUnit N
  have hp : (Mod.relativeTensorInternalHomAdjunction A M).homEquiv N N
      (Mod.relativeTensorMap A f (𝟙 N) ≫ p) =
    (Mod.relativeTensorInternalHomAdjunction A M').homEquiv N N p ≫
      (MonoidalClosed.pre f).app N := by
    change MonoidalClosed.curry ((f ⊗ₘ 𝟙 N) ≫ p) =
      MonoidalClosed.curry p ≫ (MonoidalClosed.pre f).app N
    rw [tensorHom_id]
    exact (MonoidalClosed.curry_pre_app f p).symm
  exact (congrArg ((Mod.relativeTensorInternalHomAdjunction A M).homEquiv N N) ht).trans hp

/-- The original quotient and original module unitor give the transpose of
the SAME original target structure action under its entire equalizer inclusion. -/
theorem action_ι (M : Mod C A.X) (q : M ⟶ Mod.regular A.X) (N : Mod C A.X) :
    (action A M q N).hom ≫ Mod.internalHomι A M N =
      MonoidalClosed.curry ((q.hom ▷ N.X) ≫ N.mod.smul) := by
  let p := Mod.relativeTensorMap A q (𝟙 N) ≫ (λ_ N).hom
  have hc := balanced_curry_projection A M N N p
  have hm : Mod.relativeTensorπ A M N ≫ (Mod.relativeTensorMap A q (𝟙 N)).hom =
      (q.hom ▷ N.X) ≫ Mod.relativeTensorπ A (Mod.regular A.X) N := by
    simpa only [Mod.id_hom', tensorHom_id] using (Mod.relativeTensorMap_π A q (𝟙 N))
  have hu : Mod.relativeTensorπ A (Mod.regular A.X) N ≫ (λ_ N).hom.hom =
      N.mod.smul := Mod.relativeTensorLeftUnitor_hom_π A N
  have ht : Mod.relativeTensorπ A M N ≫ p.hom = (q.hom ▷ N.X) ≫ N.mod.smul := by
    change Mod.relativeTensorπ A M N ≫ (Mod.relativeTensorMap A q (𝟙 N)).hom ≫
      (λ_ N).hom.hom = _
    exact (Category.assoc (Mod.relativeTensorπ A M N)
      (Mod.relativeTensorMap A q (𝟙 N)).hom (λ_ N).hom.hom).symm.trans
      ((congrArg (fun h => h ≫ (λ_ N).hom.hom) hm).trans
        ((Category.assoc (q.hom ▷ N.X) (Mod.relativeTensorπ A (Mod.regular A.X) N)
          (λ_ N).hom.hom).trans (congrArg (fun h => (q.hom ▷ N.X) ≫ h) hu)))
  exact hc.trans (congrArg MonoidalClosed.curry ht)

/-- The original free internal-Hom evaluates the full balanced adjunct at
its same original free-adjunction unit and original target structure action. -/
theorem free_action_forward (P : C) (q : (Mod.free A.X).obj P ⟶ Mod.regular A.X)
    (N : Mod C A.X) :
    (action A ((Mod.free A.X).obj P) q N).hom ≫ Mod.FreeInternalHom.forward A P N =
      MonoidalClosed.curry
        ((((Mod.freeForgetAdjunction A.X).unit.app P ≫ q.hom) ▷ N.X) ≫ N.mod.smul) := by
  let F := (Mod.free A.X).obj P
  let c := action A F q N
  let j := Mod.internalHomι A F N
  let g : P ⟶ F.X := (Mod.freeForgetAdjunction A.X).unit.app P
  let t : F.X ⊗ N.X ⟶ N.X := (q.hom ▷ N.X) ≫ N.mod.smul
  have hc : c.hom ≫ j = MonoidalClosed.curry t := action_ι A F q N
  have ht : (g ▷ N.X) ≫ t = ((g ≫ q.hom) ▷ N.X) ≫ N.mod.smul :=
    (Category.assoc (g ▷ N.X) (q.hom ▷ N.X) N.mod.smul).symm.trans
      (congrArg (fun h => h ≫ N.mod.smul) (comp_whiskerRight g q.hom N.X).symm)
  change c.hom ≫ (j ≫ (MonoidalClosed.pre g).app N.X) = _
  exact (Category.assoc c.hom j ((MonoidalClosed.pre g).app N.X)).symm.trans
    ((congrArg (fun h => h ≫ (MonoidalClosed.pre g).app N.X) hc).trans
      ((MonoidalClosed.curry_pre_app g t).trans (congrArg MonoidalClosed.curry ht)))

end NativeOmegaRecovery.NativeSymmetricSourceGEN.BalancedSourceAction

namespace NativeOmegaRecovery.NativeSymmetricSourceGEN.BalancedSourceAction.Day

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]
  [∀ (F G : I ⥤ V), (tensor I).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ I)).HasPointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorRight v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((𝟭 I).prod (Functor.fromPUnit.{0} (𝟙_ I))) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((tensor I).prod (𝟭 I)) d) (tensorRight v)]
  [∀ (F G : I ⥤ V) (c : I), HasEnd
    ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)]
  [HasEqualizers (DayFunctor I V)] [HasCoequalizers (DayFunctor I V)]
  (A : CommMon (DayFunctor I V))

private abbrev P (r : I) (K : V) : DayFunctor I V :=
  .mk ((evaluationLeftAdjoint V r).obj K)

private theorem scalar_projection_pre
    {W : Type uC} [Category.{vC} W] [MonoidalCategory W] [MonoidalClosed W]
    {X Y K H T : W} (c : X ⟶ H) (π : H ⟶ (ihom Y).obj T) (g : K ⟶ Y)
    (p : Y ⊗ X ⟶ T) (hp : c ≫ π = MonoidalClosed.curry p) :
    c ≫ π ≫ (MonoidalClosed.pre g).app T = MonoidalClosed.curry ((g ▷ X) ≫ p) :=
  (Category.assoc c π ((MonoidalClosed.pre g).app T)).symm.trans
    ((congrArg (fun h => h ≫ (MonoidalClosed.pre g).app T) hp).trans
      (MonoidalClosed.curry_pre_app g p))

private theorem source_day_join
    {W : Type uC} [Category.{vC} W] {X J D Z U T : W}
    {k : X ⟶ J} {u : J ⟶ D} {d : D ⟶ T} {π : J ⟶ Z}
    {g : Z ⟶ U} {b : U ⟶ T} {a : X ⟶ U}
    (hd : u ≫ d = π ≫ g ≫ b) (hp : k ≫ π ≫ g = a) :
    k ≫ u ≫ d = a ≫ b := by
  rw [hd]
  exact (Category.assoc k π (g ≫ b)).symm.trans
    ((Category.assoc (k ≫ π) g b).symm.trans
      ((congrArg (fun h => h ≫ b) (Category.assoc k π g)).trans
        (congrArg (fun h => h ≫ b) hp)))

omit [HasEqualizers (DayFunctor I V)] [HasCoequalizers (DayFunctor I V)] in
/-- Original Day currying and its given coefficient source retain the whole
identity-index generator and final original index braid. -/
theorem curry_source_pair_projection (r : I) (K : V) (F G H : DayFunctor I V)
    (g : P r K ⟶ F) (q : F ⊗ G ⟶ H) (n : I) :
    (MonoidalClosed.curry q).natTrans.app n ≫
      ((MonoidalClosed.pre g).app H).natTrans.app n ≫
      ((NativeOmegaPreparation.DayFreeEnd.comparison r K ≪≫
        NativeOmegaPreparation.DayIndexOrder.comparison r K).app H).hom.natTrans.app n =
    MonoidalClosed.curry
      (((Sigma.ι (fun _ : r ⟶ r => K) (𝟙 r) ≫ g.natTrans.app r) ▷ G.functor.obj n) ≫
        (DayFunctor.η F G).app (r, n) ≫ q.natTrans.app (r ⊗ n)) ≫
      (ihom K).map (H.functor.map (β_ r n).hom) := by
  let k := (MonoidalClosed.curry q).natTrans.app n
  let u := ((MonoidalClosed.pre g).app H).natTrans.app n
  let d := (NativeOmegaPreparation.DayFreeEnd.comparison r K ≪≫
    NativeOmegaPreparation.DayIndexOrder.comparison r K).app H
  let π := end_.π ((dayConvolutionInternalHomDiagramFunctor F.functor).obj
    H.functor |>.obj n) r
  let v := Sigma.ι (fun _ : r ⟶ r => K) (𝟙 r) ≫ g.natTrans.app r
  let t : F.functor.obj r ⊗ G.functor.obj n ⟶ H.functor.obj (r ⊗ n) :=
    (DayFunctor.η F G).app (r, n) ≫ q.natTrans.app (r ⊗ n)
  let b := (ihom K).map (H.functor.map (β_ r n).hom)
  have hd : u ≫ d.hom.natTrans.app n = π ≫ (MonoidalClosed.pre v).app
      (H.functor.obj (r ⊗ n)) ≫ b :=
    FreeFunctionSourceEvaluation.day_source_projection r K g H n
  have hπ : k ≫ π = MonoidalClosed.curry t :=
    NativeOmegaPreparation.DayClosedProjection.curry_π F G H q n r
  have hp := scalar_projection_pre k π v t hπ
  exact source_day_join hd hp

private theorem forward_pair_join
    {W : Type uC} [Category.{vC} W] {X Y H T : W}
    {c : X ⟶ H} {f : H ⟶ Y} {d : Y ⟶ T} {p : H ⟶ T} {k : X ⟶ Y}
    (hp : p = f ≫ d) (hc : c ≫ f = k) : c ≫ p = k ≫ d :=
  (congrArg (fun h => c ≫ h) hp).trans
    ((Category.assoc c f d).symm.trans (congrArg (fun h => h ≫ d) hc))

omit [HasCoequalizers (DayFunctor I V)] in
/-- The complete original free forward map retains its original entire pair
comparison before any output coordinate is selected. -/
theorem source_pair_whole (r : I) (K : V) (N : Mod (DayFunctor I V) A.X)
    (c : N.X ⟶ ((Mod.internalHom A ((Mod.free A.X).obj (P r K))).obj N).X)
    (g : P r K ⟶ A.X)
    (hc : c ≫ Mod.FreeInternalHom.forward A (P r K) N =
      MonoidalClosed.curry N.mod.smul ≫ (MonoidalClosed.pre g).app N.X) :
    c ≫ (FullFreeFunctionPair.comparison A r K N).hom =
      (MonoidalClosed.curry N.mod.smul ≫ (MonoidalClosed.pre g).app N.X) ≫
        ((NativeOmegaPreparation.DayFreeEnd.comparison r K ≪≫
          NativeOmegaPreparation.DayIndexOrder.comparison r K).app N.X).hom := by
  let d := (NativeOmegaPreparation.DayFreeEnd.comparison r K ≪≫
    NativeOmegaPreparation.DayIndexOrder.comparison r K).app N.X
  have hp : (FullFreeFunctionPair.comparison A r K N).hom =
      Mod.FreeInternalHom.forward A (P r K) N ≫ d.hom := by
    change (Mod.FreeInternalHom.iso A (P r K) N ≪≫ d).hom = _
    exact Iso.trans_hom (Mod.FreeInternalHom.iso A (P r K) N) d
  exact forward_pair_join hp hc

/-- The original balanced adjunct and same original free unit give the
entire coefficient generator of the SAME original target structure action. -/
theorem free_action_pair_projection (r : I) (K : V)
    (q : (Mod.free A.X).obj (P r K) ⟶ Mod.regular A.X)
    (N : Mod (DayFunctor I V) A.X) (n : I) :
    (action A ((Mod.free A.X).obj (P r K)) q N).hom.natTrans.app n ≫
      (FullFreeFunctionPair.comparison A r K N).hom.natTrans.app n =
    MonoidalClosed.curry
      (((Sigma.ι (fun _ : r ⟶ r => K) (𝟙 r) ≫
          ((Mod.freeForgetAdjunction A.X).unit.app (P r K)).natTrans.app r ≫
          q.hom.natTrans.app r) ▷ N.X.functor.obj n) ≫
        (DayFunctor.η A.X N.X).app (r, n) ≫ N.mod.smul.natTrans.app (r ⊗ n)) ≫
      (ihom K).map (N.X.functor.map (β_ r n).hom) := by
  let c := (action A ((Mod.free A.X).obj (P r K)) q N).hom
  let g : P r K ⟶ A.X := (Mod.freeForgetAdjunction A.X).unit.app (P r K) ≫ q.hom
  let d := (NativeOmegaPreparation.DayFreeEnd.comparison r K ≪≫
    NativeOmegaPreparation.DayIndexOrder.comparison r K).app N.X
  have hc := (free_action_forward A (P r K) q N).trans
    (MonoidalClosed.curry_pre_app g N.mod.smul).symm
  have hWhole := source_pair_whole A r K N c g hc
  have hWholeApp := congrArg (fun h => h.natTrans.app n) hWhole
  have hLeft := day_comp_component c (FullFreeFunctionPair.comparison A r K N).hom n
  have hRight := day_comp_component (MonoidalClosed.curry N.mod.smul ≫
    (MonoidalClosed.pre g).app N.X) d.hom n
  have hPre := day_comp_component (MonoidalClosed.curry N.mod.smul)
    ((MonoidalClosed.pre g).app N.X) n
  have hRaw := hLeft.symm.trans (hWholeApp.trans hRight)
  have hExpand := congrArg
    (fun h : N.X.functor.obj n ⟶ ((ihom (P r K)).obj N.X).functor.obj n =>
      h ≫ d.hom.natTrans.app n) hPre
  have hPoint : c.natTrans.app n ≫ (FullFreeFunctionPair.comparison A r K N).hom.natTrans.app n =
      (MonoidalClosed.curry N.mod.smul).natTrans.app n ≫
        ((MonoidalClosed.pre g).app N.X).natTrans.app n ≫ d.hom.natTrans.app n :=
    hRaw.trans (hExpand.trans (Category.assoc ((MonoidalClosed.curry N.mod.smul).natTrans.app n)
      (((MonoidalClosed.pre g).app N.X).natTrans.app n) (d.hom.natTrans.app n)))
  have hResult := hPoint.trans (curry_source_pair_projection r K A.X N.X N.X g N.mod.smul n)
  let ι : K ⟶ (P r K).functor.obj r := Sigma.ι (fun _ : r ⟶ r => K) (𝟙 r)
  have hGenerator : (ι ≫ g.natTrans.app r) = ι ≫
      ((Mod.freeForgetAdjunction A.X).unit.app (P r K)).natTrans.app r ≫
        q.hom.natTrans.app r :=
    congrArg (fun h : (P r K).functor.obj r ⟶ A.X.functor.obj r => ι ≫ h)
      (day_comp_component ((Mod.freeForgetAdjunction A.X).unit.app (P r K)) q.hom r)
  have hAction := congrArg (fun h : K ⟶ A.X.functor.obj r =>
    MonoidalClosed.curry ((h ▷ N.X.functor.obj n) ≫ (DayFunctor.η A.X N.X).app (r, n) ≫
      N.mod.smul.natTrans.app (r ⊗ n)) ≫
        (ihom K).map (N.X.functor.map (β_ r n).hom)) hGenerator
  exact hResult.trans hAction

end NativeOmegaRecovery.NativeSymmetricSourceGEN.BalancedSourceAction.Day

namespace NativeOmegaRecovery.NativeSymmetricSourceGEN.BalancedTarget
open BalancedSourceAction
variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]
  [∀ (F G : I ⥤ V), (tensor I).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ I)).HasPointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorRight v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((𝟭 I).prod (Functor.fromPUnit.{0} (𝟙_ I))) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((tensor I).prod (𝟭 I)) d) (tensorRight v)]
  [∀ (F G : I ⥤ V) (c : I), HasEnd
    ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)]
  [HasEqualizers (DayFunctor I V)] [HasCoequalizers (DayFunctor I V)]
  (A : CommMon (DayFunctor I V))

private abbrev P (r : I) (M : V) : DayFunctor I V :=
  .mk ((evaluationLeftAdjoint V r).obj M)

/-- The actual original target comparison keeps its whole target sequence
map after the original balanced source action, for every original parameter. -/
theorem action_target_component (r : I) (M : V)
    (K : Mod (DayFunctor I V) A.X ⥤ Mod (DayFunctor I V) A.X)
    (t : Mod.forget (D := DayFunctor I V) A.X ⋙
      NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M ≅
        K ⋙ Mod.forget (D := DayFunctor I V) A.X)
    (hPair : ∀ N a n,
      FullFreeFunctionPair.targetAction A r M N a n ≫ (t.app N).hom.natTrans.app (a ⊗ n) =
        (A.X.functor.obj a ◁ (t.app N).hom.natTrans.app n) ≫
          FullFreeFunctionModuleComparison.pairAction (A := A) (K.obj N) a n)
    (q : (Mod.free A.X).obj (P r M) ⟶ Mod.regular A.X)
    (N : Mod (DayFunctor I V) A.X) (n : I) :
    ((action A ((Mod.free A.X).obj (P r M)) q N ≫
      (FullFreeFunctionTargetNaturality.comparison A r M K t hPair).hom.app N).hom).natTrans.app n =
    (MonoidalClosed.curry
      (((Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r) ≫
          ((Mod.freeForgetAdjunction A.X).unit.app (P r M)).natTrans.app r ≫
          q.hom.natTrans.app r) ▷ N.X.functor.obj n) ≫
        (DayFunctor.η A.X N.X).app (r, n) ≫ N.mod.smul.natTrans.app (r ⊗ n)) ≫
      (ihom M).map (N.X.functor.map (β_ r n).hom)) ≫ (t.app N).hom.natTrans.app n := by
  let c := action A ((Mod.free A.X).obj (P r M)) q N
  let e := FullFreeFunctionTargetNaturality.comparison A r M K t hPair
  let p := (FullFreeFunctionPair.comparison A r M N).hom
  let z := (t.app N).hom
  have he : (e.hom.app N).hom = p ≫ z :=
    FullFreeFunctionTargetNaturality.hom_app_hom A r M K t hPair N
  have h₀ := congrArg (fun f => (c.hom ≫ f).natTrans.app n) he
  have h₁ := congrArg (fun f => f.natTrans.app n) (Category.assoc c.hom p z).symm
  have hAction := BalancedSourceAction.Day.free_action_pair_projection A r M q N n
  change (c.hom ≫ (e.hom.app N).hom).natTrans.app n = _
  exact h₀.trans (h₁.trans (congrArg (fun f => f ≫ z.natTrans.app n) hAction))

/-- Entire actual source-functor, source-map and comparison data are eliminated
before selecting an original target module or output coordinate. -/
theorem action_target_component_of_whole_data (r : I) (M : V)
    (K : Mod (DayFunctor I V) A.X ⥤ Mod (DayFunctor I V) A.X)
    (t : Mod.forget (D := DayFunctor I V) A.X ⋙
      NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M ≅
        K ⋙ Mod.forget (D := DayFunctor I V) A.X)
    (hPair : ∀ N a n,
      FullFreeFunctionPair.targetAction A r M N a n ≫ (t.app N).hom.natTrans.app (a ⊗ n) =
        (A.X.functor.obj a ◁ (t.app N).hom.natTrans.app n) ≫
          FullFreeFunctionModuleComparison.pairAction (A := A) (K.obj N) a n)
    (q : (Mod.free A.X).obj (P r M) ⟶ Mod.regular A.X)
    {F : Mod (DayFunctor I V) A.X ⥤ Mod (DayFunctor I V) A.X}
    (hF : F = Mod.internalHom A ((Mod.free A.X).obj (P r M)))
    (c : 𝟭 (Mod (DayFunctor I V) A.X) ⟶ F)
    (hc : ∀ N, HEq (c.app N) (action A ((Mod.free A.X).obj (P r M)) q N))
    (e : F ≅ K)
    (he : HEq e (FullFreeFunctionTargetNaturality.comparison A r M K t hPair))
    (N : Mod (DayFunctor I V) A.X) (n : I) :
    (((c ≫ e.hom).app N).hom).natTrans.app n =
    (MonoidalClosed.curry
      (((Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r) ≫
          ((Mod.freeForgetAdjunction A.X).unit.app (P r M)).natTrans.app r ≫
          q.hom.natTrans.app r) ▷ N.X.functor.obj n) ≫
        (DayFunctor.η A.X N.X).app (r, n) ≫ N.mod.smul.natTrans.app (r ⊗ n)) ≫
      (ihom M).map (N.X.functor.map (β_ r n).hom)) ≫ (t.app N).hom.natTrans.app n := by
  cases hF
  cases he
  have hcN : c.app N = action A ((Mod.free A.X).obj (P r M)) q N := eq_of_heq (hc N)
  have hArrow := congrArg (fun f => (f ≫
    (FullFreeFunctionTargetNaturality.comparison A r M K t hPair).hom.app N).hom.natTrans.app n) hcN
  exact hArrow.trans (action_target_component A r M K t hPair q N n)

end NativeOmegaRecovery.NativeSymmetricSourceGEN.BalancedTarget

namespace NativeOmegaRecovery.NativeSymmetricSourceGEN.CoefficientActionTransport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]

/-- A proved original coefficient equation is transported through the same
original curry, target action and final target map as a single arrow. -/
theorem curry_action_of_coefficient {K R X Y Z W : V}
    {g₀ g₁ : K ⟶ R} {insert : R ⊗ X ⟶ Y} {a : Y ⟶ Z} {t : Z ⟶ W}
    {f : X ⟶ (ihom K).obj W}
    (hAction : f = MonoidalClosed.curry ((g₀ ▷ X) ≫ insert ≫ a) ≫ (ihom K).map t)
    (hCoefficient : g₀ = g₁) :
    f = MonoidalClosed.curry ((g₁ ▷ X) ≫ insert ≫ a) ≫ (ihom K).map t := by
  exact hAction.trans (congrArg
    (fun g : K ⟶ R => MonoidalClosed.curry ((g ▷ X) ≫ insert ≫ a) ≫ (ihom K).map t)
    hCoefficient)

end NativeOmegaRecovery.NativeSymmetricSourceGEN.CoefficientActionTransport


namespace NativeOmegaRecovery.NativeSymmetricSourceGEN.NativeBalancedAction

attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  PointedCGWH.EnrichedMapping.hasSmallLimits
  NativeOmegaPreparation.SymmetricFunction.sequenceCoequalizers
  NativeOmegaPreparation.SymmetricFunction.sequenceEqualizers
  NativeOmegaPreparation.SymmetricFunction.sequenceClosed
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.SymmetricFunctionFactories.indexedCoproducts
  PointedCGWH.SymmetricFunctionFactories.tensorExtensions
  PointedCGWH.SymmetricFunctionFactories.unitExtensions
  PointedCGWH.SymmetricFunctionFactories.tensorLeftTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTensorShape
  PointedCGWH.SymmetricFunctionFactories.tensorLeftUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightMixedUnitShape
  PointedCGWH.SymmetricFunctionFactories.tensorRightTripleShape
  PointedCGWH.SymmetricFunctionFactories.internalHomEnds

/-- Every original module map retains its original balanced action and free
unit in the complete original pair comparison, at every output index. -/
theorem original_balanced_pair_projection (r : Operad.SmallFinBijGroupoid)
    (K : PointedCGWH.{u, v})
    (q : NativeSymmetricFreeSource.freeModule.{u, v} r K ⟶
      Mod.regular PointedCGWH.sphereSequence.{u, v})
    (N : NativeSymmetricFreeFunction.OriginalModule.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    type_of% (BalancedSourceAction.Day.free_action_pair_projection
      (I := Operad.SmallFinBijGroupoid) (V := PointedCGWH.{u, v})
      PointedCGWH.sphereSequenceCommMon.{u, v} r K
      (NativeAdjointData.canonicalMap.{u, v} r K q) N n) :=
  BalancedSourceAction.Day.free_action_pair_projection
    (I := Operad.SmallFinBijGroupoid) (V := PointedCGWH.{u, v})
    PointedCGWH.sphereSequenceCommMon.{u, v} r K
    (NativeAdjointData.canonicalMap.{u, v} r K q) N n

/-- The coefficient in the same original target action is the original
Day free adjunct of the same given original module map. -/
theorem original_day_adjunct_action_pair (r : Operad.SmallFinBijGroupoid)
    (K : PointedCGWH.{u, v})
    (q : NativeSymmetricFreeSource.freeModule.{u, v} r K ⟶
      Mod.regular PointedCGWH.sphereSequence.{u, v})
    (N : NativeSymmetricFreeFunction.OriginalModule.{u, v}) (n : Operad.SmallFinBijGroupoid) :
    type_of% (CoefficientActionTransport.curry_action_of_coefficient (V := PointedCGWH.{u, v})
      (original_balanced_pair_projection.{u, v} r K q N n)
      (NativeAdjointData.canonical_generator_eq_original_day_adjunct.{u, v} r K q)) :=
  CoefficientActionTransport.curry_action_of_coefficient (V := PointedCGWH.{u, v})
    (original_balanced_pair_projection.{u, v} r K q N n)
    (NativeAdjointData.canonical_generator_eq_original_day_adjunct.{u, v} r K q)

end NativeOmegaRecovery.NativeSymmetricSourceGEN.NativeBalancedAction

noncomputable section SourceImageCore01

set_option autoImplicit false
open CategoryTheory

namespace NativeOmegaRecovery.OriginalCarrierZeroSourceUnit

/-- Naturality transports the entire original source image word while both given
carrier unit maps and the actual inverse-carrier object are still present. -/
theorem source_image_tail_naturality
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    (E : C ≌ D) {F G : C ⥤ C} {R R' : D ⥤ D}
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse)
    (e' : G ≅ E.functor ⋙ R' ⋙ E.inverse) (u : R ≅ 𝟭 D)
    (p : F ⟶ G) (N : C) :
    E.functor.map
        (E.unitIso.hom.app N ≫ E.inverse.map (u.inv.app (E.functor.obj N)) ≫
          e.inv.app N ≫ F.map (E.unitIso.hom.app N) ≫
          p.app (E.inverse.obj (E.functor.obj N)) ≫
          e'.hom.app (E.inverse.obj (E.functor.obj N))) ≫
      E.counitIso.hom.app (R'.obj (E.functor.obj (E.inverse.obj (E.functor.obj N)))) ≫
      R'.map (E.counitIso.hom.app (E.functor.obj N)) =
    E.functor.map
        (E.unitIso.hom.app N ≫ E.inverse.map (u.inv.app (E.functor.obj N)) ≫
          e.inv.app N ≫ p.app N ≫ e'.hom.app N) ≫
      E.counitIso.hom.app (R'.obj (E.functor.obj N)) := by
  let X := E.functor.obj N
  let K := E.inverse.obj X
  let δ : N ⟶ K := E.unitIso.hom.app N
  let a := δ ≫ E.inverse.map (u.inv.app X) ≫ e.inv.app N
  let b : R'.obj X ⟶ R'.obj (E.functor.obj K) := R'.map (E.functor.map δ)
  have hp : F.map δ ≫ p.app K = p.app N ≫ G.map δ := p.naturality δ
  have he : G.map δ ≫ e'.hom.app K = e'.hom.app N ≫ E.inverse.map b :=
    e'.hom.naturality δ
  have h : F.map δ ≫ p.app K ≫ e'.hom.app K =
      p.app N ≫ e'.hom.app N ≫ E.inverse.map b := by
    calc
      _ = (F.map δ ≫ p.app K) ≫ e'.hom.app K := (Category.assoc _ _ _).symm
      _ = (p.app N ≫ G.map δ) ≫ e'.hom.app K := congrArg (fun z => z ≫ e'.hom.app K) hp
      _ = p.app N ≫ (G.map δ ≫ e'.hom.app K) := Category.assoc _ _ _
      _ = p.app N ≫ (e'.hom.app N ≫ E.inverse.map b) := congrArg (fun z => p.app N ≫ z) he
  have hc : E.functor.map (E.inverse.map b) ≫
      E.counitIso.hom.app (R'.obj (E.functor.obj K)) =
      E.counitIso.hom.app (R'.obj X) ≫ b :=
    E.counitIso.hom.naturality b
  have hgoal : E.functor.map (a ≫ F.map δ ≫ p.app K ≫ e'.hom.app K) ≫
      E.counitIso.hom.app (R'.obj (E.functor.obj K)) ≫
      R'.map (E.counitIso.hom.app X) =
    E.functor.map (a ≫ p.app N ≫ e'.hom.app N) ≫
      E.counitIso.hom.app (R'.obj X) := by
    rw [h]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hc]
    dsimp only [b, δ, X]
    rw [← R'.map_comp, E.functor_unit_comp N, R'.map_id, Category.comp_id]
  simpa only [a, δ, K, X, Category.assoc] using hgoal

end NativeOmegaRecovery.OriginalCarrierZeroSourceUnit

end SourceImageCore01

noncomputable section SourceImageCore02

set_option autoImplicit false
open CategoryTheory MonoidalCategory Limits
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.SourceImageWord
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- The complete original module unit, scalar inverse and source-comparison word. -/
def moduleWord (E : C ≌ D) {F G : C ⥤ C} {R R' : D ⥤ D}
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse)
    (e' : G ≅ E.functor ⋙ R' ⋙ E.inverse) (u : R ≅ 𝟭 D) (p : F ⟶ G) :
    𝟭 C ⟶ E.functor ⋙ R' ⋙ E.inverse :=
  E.unitIso.hom ≫
    Functor.whiskerLeft E.functor (Functor.whiskerRight u.inv E.inverse) ≫
    e.inv ≫ p ≫ e'.hom

/-- Both original carrier functors and the final whole counit carry that same module word. -/
def carrierWord (E : C ≌ D) {F G : C ⥤ C} {R R' : D ⥤ D}
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse)
    (e' : G ≅ E.functor ⋙ R' ⋙ E.inverse) (u : R ≅ 𝟭 D) (p : F ⟶ G) :
    E.functor ⟶ E.functor ⋙ R' :=
  Functor.whiskerRight (moduleWord E e e' u p) E.functor ≫
    Functor.whiskerLeft (E.functor ⋙ R') E.counitIso.hom

/-- Every full carrier-word component retains all original units and comparisons. -/
theorem carrierWord_app (E : C ≌ D) {F G : C ⥤ C} {R R' : D ⥤ D}
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse)
    (e' : G ≅ E.functor ⋙ R' ⋙ E.inverse) (u : R ≅ 𝟭 D) (p : F ⟶ G) (N : C) :
    (carrierWord E e e' u p).app N =
      E.functor.map (E.unitIso.hom.app N ≫
        E.inverse.map (u.inv.app (E.functor.obj N)) ≫
        e.inv.app N ≫ p.app N ≫ e'.hom.app N) ≫
      E.counitIso.hom.app (R'.obj (E.functor.obj N)) := rfl
/-- Identity source transports cancel around a fixed already typed source arrow. -/
theorem cancel_identity_transports {T : Type uT} [Category.{vT} T] {A B : T}
    (i : A ⟶ A) (q : A ⟶ B) (j : B ⟶ B)
    (hi : i = 𝟙 A) (hj : j = 𝟙 B) : i ≫ q ≫ j = q := by
  rw [hi, hj, Category.id_comp, Category.comp_id]

section Modules
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] [HasCoequalizers V] [HasEqualizers V]
  (A : CommMon V) {D : Type uD'} [Category.{vD'} D] (E : Mod V A.X ≌ D)
/-- The tensor on modules over the commutative monoid `A`, used by the source-image word. -/
local instance instMonoidalCategoryModXMathlibExt : MonoidalCategory (Mod V A.X) := Mod.instMonoidalCategory A
/-- The closed tensor on modules over `A`, used for the original source precomposition maps. -/
local instance instMonoidalClosedModXMathlibExt : MonoidalClosed (Mod V A.X) := Mod.instMonoidalClosed A

/-- A bound original module arrow gives the actual transported source pre-map. -/
theorem module_precompose_app (M M' : Mod V A.X) (g : M' ⟶ M) (X : D) :
    ((NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E).map g.op).app X =
      E.functor.map ((MonoidalClosed.pre g).app (E.inverse.obj X)) := rfl
end Modules

/-- The original unit inverse, source map and full recovery tail yield the same image word. -/
theorem compose_source_image_word (E : C ≌ D) {F G : C ⥤ C} {R R' S T : D ⥤ D}
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse)
    (e' : G ≅ E.functor ⋙ R' ⋙ E.inverse) (u : R ≅ 𝟭 D) (p : F ⟶ G)
    (w : S ≅ 𝟭 D) (s : S ≅ E.inverse ⋙ F ⋙ E.functor)
    (s' : T ≅ E.inverse ⋙ G ⋙ E.functor) (q : S ⟶ T) (c : T ≅ R')
    (N : C)
    (hu : w.inv.app (E.functor.obj N) =
      E.functor.map (E.unitIso.hom.app N ≫
        E.inverse.map (u.inv.app (E.functor.obj N)) ≫ e.inv.app N ≫
        F.map (E.unitIso.hom.app N)) ≫ s.inv.app (E.functor.obj N))
    (hc : c.hom.app (E.functor.obj N) =
      s'.hom.app (E.functor.obj N) ≫
        E.functor.map (e'.hom.app (E.inverse.obj (E.functor.obj N))) ≫
        E.counitIso.hom.app (R'.obj (E.functor.obj (E.inverse.obj (E.functor.obj N)))) ≫
        R'.map (E.counitIso.hom.app (E.functor.obj N)))
    (hq : s.inv.app (E.functor.obj N) ≫ q.app (E.functor.obj N) ≫
      s'.hom.app (E.functor.obj N) =
      E.functor.map (p.app (E.inverse.obj (E.functor.obj N)))) :
    w.inv.app (E.functor.obj N) ≫ q.app (E.functor.obj N) ≫ c.hom.app (E.functor.obj N) =
      (carrierWord E e e' u p).app N := by
  rw [hu, hc, carrierWord_app]
  simp only [Category.assoc]
  rw [reassoc_of% hq]
  simpa only [Functor.map_comp, Category.assoc] using
    OriginalCarrierZeroSourceUnit.source_image_tail_naturality E e e' u p N

end NativeOmegaRecovery.SourceImageWord

end SourceImageCore02

noncomputable section SourceImageCore03

set_option autoImplicit false
open CategoryTheory

namespace NativeOmegaRecovery.SourceImageWord
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- Rebasing the entire original source comparison also rebases its complete carrier tail. -/
theorem sourceTail_rebase (E : C ≌ D) {F F' : C ⥤ C} {R S : D ⥤ D}
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse)
    (h : F = F') (hS : S = E.inverse ⋙ F ⋙ E.functor)
    (hS' : S = E.inverse ⋙ F' ⋙ E.functor) :
    eqToIso hS ≪≫ SourceEquality.moduleTail E e =
      eqToIso hS' ≪≫ SourceEquality.moduleTail E
        (NativeSelectedUnitTransport.rebaseComparison e h) := by
  cases h
  have hs : hS = hS' := Subsingleton.elim _ _
  cases hs
  have he : NativeSelectedUnitTransport.rebaseComparison e rfl = e := by
    apply Iso.ext
    change 𝟙 _ ≫ e.hom = e.hom
    exact Category.id_comp e.hom
  rw [he]

/-- A whole original comparison equality exposes its two complete carrier-counit factors. -/
theorem sourceTail_hom_app (E : C ≌ D) {F : C ⥤ C} {R S : D ⥤ D}
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse)
    (s : S ≅ E.inverse ⋙ F ⋙ E.functor) (c : S ≅ R)
    (hc : c = s ≪≫ SourceEquality.moduleTail E e) (X : D) :
    c.hom.app X =
      s.hom.app X ≫ E.functor.map (e.hom.app (E.inverse.obj X)) ≫
        E.counitIso.hom.app (R.obj (E.functor.obj (E.inverse.obj X))) ≫
          R.map (E.counitIso.hom.app X) := by
  rw [hc]
  simp only [SourceEquality.moduleTail, SourceEquality.normalizedTail,
    FreeFunctionCarrierComparison.collapse, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Category.assoc]
  exact congrArg
    (fun z => s.hom.app X ≫ E.functor.map (e.hom.app (E.inverse.obj X)) ≫
      E.counitIso.hom.app (R.obj (E.functor.obj (E.inverse.obj X))) ≫ z)
    (Category.comp_id (R.map (E.counitIso.hom.app X)))

end NativeOmegaRecovery.SourceImageWord

end SourceImageCore03

noncomputable section SourceImageCore04

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.SourceImageWord
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] [HasCoequalizers V] [HasEqualizers V] (A : CommMon V)

/-- The module tensor used to read precomposition on the fixed original module objects. -/
local instance boundPreModuleMonoidal : MonoidalCategory (Mod V A.X) := Mod.instMonoidalCategory A
/-- The module internal Hom structure used to read the original contravariant pre-map. -/
local instance boundPreModuleClosed : MonoidalClosed (Mod V A.X) := Mod.instMonoidalClosed A

/-- Both original module objects are fixed before reading the actual whole source pre-map. -/
def boundModulePre (M M' : Mod V A.X) (g : M' ⟶ M) :
    Mod.internalHom A M ⟶ Mod.internalHom A M' := MonoidalClosed.pre g

/-- The bound whole module pre-map is precisely the same original closed pre-map. -/
theorem bound_module_pre_eq_original (M M' : Mod V A.X) (g : M' ⟶ M) :
    boundModulePre A M M' g = MonoidalClosed.pre g := rfl

/-- Both original carrier functors retain that bound module pre-map at every actual source object. -/
theorem bound_module_source_pre_app {D : Type uD} [Category.{vD} D] (E : Mod V A.X ≌ D)
    (M M' : Mod V A.X) (g : M' ⟶ M) (X : D) :
    ((NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E).map g.op).app X =
      E.functor.map ((boundModulePre A M M' g).app (E.inverse.obj X)) := rfl

end NativeOmegaRecovery.SourceImageWord

end SourceImageCore04

noncomputable section SourceImageCore05

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj

namespace NativeOmegaRecovery.SourceImageWord
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- The whole given comparison arrow is bound using its actual original source and target types. -/
def isoArrow {F G : C ⥤ D} (e : F ≅ G) : Arrow (C ⥤ D) := Arrow.mk e.hom

/-- This bound complete arrow is the original comparison arrow, including its original map. -/
theorem isoArrow_eq_original {F G : C ⥤ D} (e : F ≅ G) : isoArrow e = Arrow.mk e.hom := rfl

section Modules
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] [HasCoequalizers V] [HasEqualizers V] (A : CommMon V)
  {D' : Type uD'} [Category.{vD'} D'] (E : Mod V A.X ≌ D')

/-- The two entire source equalities surround the same bound original module pre-map. -/
def rawSourcePre (M M' : Mod V A.X) (g : M' ⟶ M) {F F' : Mod V A.X ⥤ Mod V A.X}
    (hF : F = Mod.internalHom A M) (hF' : F' = Mod.internalHom A M') : F ⟶ F' :=
  (eqToIso hF).hom ≫ boundModulePre A M M' g ≫ (eqToIso hF').inv

/-- Both whole source transports retain the complete original contravariant module source map. -/
theorem raw_source_square (M M' : Mod V A.X) (g : M' ⟶ M)
    {F F' : Mod V A.X ⥤ Mod V A.X}
    (hF : F = Mod.internalHom A M) (hF' : F' = Mod.internalHom A M')
    (hS : (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E).obj (.op M) =
      E.inverse ⋙ F ⋙ E.functor)
    (hS' : (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E).obj (.op M') =
      E.inverse ⋙ F' ⋙ E.functor) :
    (eqToIso hS).inv ≫ (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E).map g.op ≫
        (eqToIso hS').hom =
      Functor.whiskerLeft E.inverse (Functor.whiskerRight (rawSourcePre A M M' g hF hF') E.functor) := by
  cases hF
  cases hF'
  have h₀ : hS = NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj A E M :=
    Subsingleton.elim _ _
  have h₁ : hS' = NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj A E M' :=
    Subsingleton.elim _ _
  cases h₀
  cases h₁
  apply NatTrans.ext
  funext X
  simp only [NatTrans.comp_app, rawSourcePre, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hi := OriginalSourceInverse.inverse A E M X
  have hj : (eqToIso (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj A E M')).hom.app X =
      𝟙 _ := rfl
  exact (cancel_identity_transports
    ((eqToIso (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj A E M)).inv.app X)
    (((NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor A E).map g.op).app X)
    ((eqToIso (NativeOmegaPreparation.ModuleFunctionTransport.sourceFunctor_obj A E M')).hom.app X)
    hi hj).trans (bound_module_source_pre_app A E M M' g X)

end Modules

/-- Actual original inverse, tail and whole source-map values determine the complete image transformation. -/
theorem compose_source_image_word_nat {E : C ≌ D} {F G : C ⥤ C} {R R' S T : D ⥤ D}
    {e : F ≅ E.functor ⋙ R ⋙ E.inverse} {e' : G ≅ E.functor ⋙ R' ⋙ E.inverse}
    {u : R ≅ 𝟭 D} {p : F ⟶ G} {w : S ≅ 𝟭 D}
    {s : S ≅ E.inverse ⋙ F ⋙ E.functor} {s' : T ≅ E.inverse ⋙ G ⋙ E.functor}
    {q : S ⟶ T} {c : T ≅ R'}
    (hu : ∀ N : C, w.inv.app (E.functor.obj N) =
      E.functor.map (E.unitIso.hom.app N ≫ E.inverse.map (u.inv.app (E.functor.obj N)) ≫
        e.inv.app N ≫ F.map (E.unitIso.hom.app N)) ≫ s.inv.app (E.functor.obj N))
    (hc : ∀ N : C, c.hom.app (E.functor.obj N) = s'.hom.app (E.functor.obj N) ≫
      E.functor.map (e'.hom.app (E.inverse.obj (E.functor.obj N))) ≫
        E.counitIso.hom.app (R'.obj (E.functor.obj (E.inverse.obj (E.functor.obj N)))) ≫
          R'.map (E.counitIso.hom.app (E.functor.obj N)))
    (hq : ∀ N : C, s.inv.app (E.functor.obj N) ≫ q.app (E.functor.obj N) ≫
      s'.hom.app (E.functor.obj N) = E.functor.map (p.app (E.inverse.obj (E.functor.obj N)))) :
    Functor.whiskerLeft E.functor (w.inv ≫ q ≫ c.hom) = carrierWord E e e' u p := by
  apply NatTrans.ext
  funext N
  exact compose_source_image_word E e e' u p w s s' q c N (hu N) (hc N) (hq N)

end NativeOmegaRecovery.SourceImageWord

end SourceImageCore05
