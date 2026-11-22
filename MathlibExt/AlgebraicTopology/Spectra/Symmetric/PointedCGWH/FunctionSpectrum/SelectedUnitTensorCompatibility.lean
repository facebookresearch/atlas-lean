/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceCoefficientSourceGEN
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.SourceCoefficientZeroUnit
import MathlibExt.CategoryTheory.Monoidal.Mod.EquivalenceFunction
import Mathlib.CategoryTheory.Monoidal.Transport
import MathlibExt.CategoryTheory.Monoidal.Mod.FreeInternalHom
import MathlibExt.CategoryTheory.Monoidal.Mod.ClosedComponents

/-!
# Original source equations for selected native unit compatibility

The original balanced contraction, complete free internal-Hom projection,
actual scalar/index unit and full source data are identified before the native
unit transport. All arrows use the original module and carrier constructions.
-/

set_option autoImplicit false
noncomputable section
universe uC vC
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed CategoryTheory.MonObj ExternalProduct

namespace NativeOmegaRecovery.SelectedUnitTensorCompatibility

private theorem tensor_generator_source_word
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    {P F U N T L : C} (g : P ⟶ F) (f : F ⟶ U)
    (p : F ⊗ N ⟶ T) (m : T ⟶ L) (l : L ⟶ N) (pU : U ⊗ N ⟶ L)
    (u : P ⟶ (𝟙_ C)) (unitInsert : (𝟙_ C) ⟶ U) (s : U ⊗ N ⟶ N)
    (hπ : p ≫ m = (f ▷ N) ≫ pU) (hg : g ≫ f = u ≫ unitInsert)
    (hUnit : pU ≫ l = s) (hOne : (unitInsert ▷ N) ≫ s = (λ_ N).hom) :
    (g ▷ N) ≫ p ≫ m ≫ l = (u ▷ N) ≫ (λ_ N).hom := by
  have h₁ : (g ▷ N) ≫ p ≫ m ≫ l = (g ▷ N) ≫ (f ▷ N) ≫ pU ≫ l := by
    have h := congrArg (fun q => (g ▷ N) ≫ q ≫ l) hπ
    simpa only [Category.assoc] using h
  have h₂ : (g ▷ N) ≫ (f ▷ N) = (u ≫ unitInsert) ▷ N :=
    (comp_whiskerRight g f N).symm.trans (congrArg (fun q => q ▷ N) hg)
  have h₃ : (g ▷ N) ≫ (f ▷ N) ≫ pU ≫ l = ((u ≫ unitInsert) ▷ N) ≫ s := by
    have h := congrArg (fun q => q ≫ pU ≫ l) h₂
    have h' := congrArg (fun q => ((u ≫ unitInsert) ▷ N) ≫ q) hUnit
    simpa only [Category.assoc] using h.trans h'
  have h₄ : ((u ≫ unitInsert) ▷ N) ≫ s = (u ▷ N) ≫ (λ_ N).hom := by
    have h := congrArg (fun q => q ≫ s) (comp_whiskerRight u unitInsert N)
    have h' := congrArg (fun q => (u ▷ N) ≫ q) hOne
    simpa only [Category.assoc] using
      h.trans ((Category.assoc (u ▷ N) (unitInsert ▷ N) s).trans h')
  exact h₁.trans (h₃.trans h₄)

end NativeOmegaRecovery.SelectedUnitTensorCompatibility

namespace NativeOmegaRecovery.SelectedUnitTensorCompatibility
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]
  (A : CommMon C)

/-- The original whole module tensor record for the unchanged coefficient. -/
local instance originalModuleMonoidal : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
/-- The original whole module internal-Hom record for the same coefficient. -/
local instance originalModuleClosed : MonoidalClosed (Mod C A.X) := Mod.instMonoidalClosed A

/-- The original free-forgetful adjunction contracts the whole free source. -/
def freeUnitContraction (P : C) (u : P ⟶ (𝟙_ C)) :
    (Mod.free A.X).obj P ⟶ Mod.regular A.X :=
  ((Mod.freeForgetAdjunction A.X).homEquiv P (Mod.regular A.X)).symm (u ≫ η[A.X])

omit [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C] in
/-- The actual selected free generator recovers its given whole coefficient arrow. -/
theorem freeUnitContraction_generator (P : C) (u : P ⟶ (𝟙_ C)) :
    (Mod.freeForgetAdjunction A.X).unit.app P ≫ (freeUnitContraction A P u).hom = u ≫ η[A.X] := by
  have h := ((Mod.freeForgetAdjunction A.X).homEquiv P (Mod.regular A.X)).apply_symm_apply
    (u ≫ η[A.X])
  rw [Adjunction.homEquiv_unit] at h
  exact h

/-- Every original balanced transpose retains its entire equalizer inclusion. -/
theorem curry_projection (M N K : Mod C A.X)
    (q : ((Mod.relativeTensor A).obj M).obj N ⟶ K) :
    ((Mod.relativeTensorInternalHomAdjunction A M).homEquiv N K q).hom ≫
        Mod.internalHomι A M K =
      MonoidalClosed.curry (Mod.relativeTensorπ A M N ≫ q.hom) := by
  rw [Adjunction.homEquiv_unit]
  change (((Mod.coevaluation A M).app N).hom ≫ ((Mod.internalHom A M).map q).hom) ≫
    Mod.internalHomι A M K = _
  rw [Category.assoc, Mod.internalHomMap, ← Category.assoc, Mod.coevaluation_ι]
  exact (MonoidalClosed.curry_natural_right _ _).symm

omit [HasEqualizers C] in
/-- The same complete contraction and original left unitor recover their unchanged
coefficient tensor action after the original free generator. -/
theorem freeUnitContraction_tensor_generator (P : C) (u : P ⟶ (𝟙_ C))
    (N : Mod C A.X) :
    (((Mod.freeForgetAdjunction A.X).unit.app P) ▷ N.X) ≫
        Mod.relativeTensorπ A ((Mod.free A.X).obj P) N ≫
          ((Mod.relativeTensorMap A (freeUnitContraction A P u) (𝟙 N)) ≫
            (λ_ N).hom).hom =
      (u ▷ N.X) ≫ (λ_ N.X).hom := by
  let F : Mod C A.X := (Mod.free A.X).obj P
  let U : Mod C A.X := ((Mod.relativeTensor A).obj (Mod.regular A.X)).obj N
  let T : Mod C A.X := ((Mod.relativeTensor A).obj F).obj N
  let g : P ⟶ F.X := (Mod.freeForgetAdjunction A.X).unit.app P
  let t : F ⟶ Mod.regular A.X := freeUnitContraction A P u
  let tH : F.X ⟶ A.X := t.hom
  let p : F.X ⊗ N.X ⟶ T.X := Mod.relativeTensorπ A F N
  let pU : A.X ⊗ N.X ⟶ U.X := Mod.relativeTensorπ A (Mod.regular A.X) N
  let m : T.X ⟶ U.X := (Mod.relativeTensorMap A t (𝟙 N)).hom
  let l : U.X ⟶ N.X := (λ_ N).hom.hom
  have hπ : p ≫ m = (tH ▷ N.X) ≫ pU := by
    have h := Mod.relativeTensorMap_π A t (𝟙 N)
    simp only [Mod.id_hom', tensorHom_id] at h
    exact h
  have hUnit : pU ≫ l = N.mod.smul := Mod.relativeTensorLeftUnitor_hom_π A N
  have hG : g ≫ tH = u ≫ η[A.X] := freeUnitContraction_generator A P u
  change (g ▷ N.X) ≫ p ≫ m ≫ l = _
  have hOne : (η[A.X] ▷ N.X) ≫ N.mod.smul = (λ_ N.X).hom := N.mod.one_smul
  exact tensor_generator_source_word g tH p m l pU u η[A.X] N.mod.smul hπ hG hUnit hOne

/-- The original balanced transpose is the actual coefficient-unit transpose
under the original free internal-Hom comparison. -/
theorem freeUnitContraction_curry_forward (P : C) (u : P ⟶ (𝟙_ C))
    (N : Mod C A.X) :
    ((Mod.relativeTensorInternalHomAdjunction A ((Mod.free A.X).obj P)).homEquiv N N
      ((Mod.relativeTensorMap A (freeUnitContraction A P u) (𝟙 N)) ≫
        (λ_ N).hom)).hom ≫
      Mod.FreeInternalHom.forward A P N =
    MonoidalClosed.curry ((u ▷ N.X) ≫ (λ_ N.X).hom) := by
  let q := (Mod.relativeTensorMap A (freeUnitContraction A P u) (𝟙 N)) ≫
    (λ_ N).hom
  let c := (Mod.relativeTensorInternalHomAdjunction A ((Mod.free A.X).obj P)).homEquiv N N q
  let j := Mod.internalHomι A ((Mod.free A.X).obj P) N
  let g := (Mod.freeForgetAdjunction A.X).unit.app P
  let π := Mod.relativeTensorπ A ((Mod.free A.X).obj P) N
  have hC : c.hom ≫ j = MonoidalClosed.curry (π ≫ q.hom) := curry_projection A _ _ _ q
  have hPre := MonoidalClosed.curry_pre_app g (π ≫ q.hom)
  have hGenerator := freeUnitContraction_tensor_generator A P u N
  change c.hom ≫ (j ≫ (MonoidalClosed.pre g).app N.X) = _
  exact (Category.assoc c.hom j ((MonoidalClosed.pre g).app N.X)).symm.trans
    ((congrArg (fun z => z ≫ (MonoidalClosed.pre g).app N.X) hC).trans
      (hPre.trans (congrArg MonoidalClosed.curry hGenerator)))

end NativeOmegaRecovery.SelectedUnitTensorCompatibility

namespace NativeOmegaRecovery.SelectedUnitTensorCompatibility.Day
universe uI vI uV vV
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

/-- The original Day-module tensor record for all original indices and values. -/
local instance originalDayModuleMonoidal : MonoidalCategory (Mod (DayFunctor I V) A.X) :=
  Mod.instMonoidalCategory A

private abbrev P₀ : DayFunctor I V :=
  .mk ((evaluationLeftAdjoint V (𝟙_ I)).obj (𝟙_ V))

omit [HasCoequalizers (DayFunctor I V)] in
/-- The entire original arrow and its genuine free-unit projection retain
both original end maps and both selected scalar/index unit components. -/
theorem zero_unit_pair_of_projection (N : Mod (DayFunctor I V) A.X)
    (c : N ⟶ (Mod.internalHom A ((Mod.free A.X).obj P₀)).obj N)
    (hc : c.hom ≫ Mod.FreeInternalHom.forward A P₀ N =
      MonoidalClosed.curry ((FreeFunctionSourceEvaluation.originalZeroDiagramUnit ▷ N.X) ≫
        (λ_ N.X).hom)) (n : I) :
    (c.hom ≫ (FullFreeFunctionPair.comparison A (𝟙_ I) (𝟙_ V) N).hom).natTrans.app n =
      N.X.functor.map (ρ_ n).inv ≫
        MonoidalClosed.unitNatIso.hom.app (N.X.functor.obj (n ⊗ (𝟙_ I))) := by
  let P : DayFunctor I V := P₀
  let u : P ⟶ (𝟙_ (DayFunctor I V)) :=
    FreeFunctionSourceEvaluation.originalZeroDiagramUnit
  let p : ((Mod.internalHom A ((Mod.free A.X).obj P)).obj N).X ⟶
      (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor (𝟙_ I) (𝟙_ V)).obj N.X :=
    (FullFreeFunctionPair.comparison A (𝟙_ I) (𝟙_ V) N).hom
  let d : (ihom P).obj N.X ≅
      (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor (𝟙_ I) (𝟙_ V)).obj N.X :=
    (NativeOmegaPreparation.DayFreeEnd.comparison (𝟙_ I) (𝟙_ V) ≪≫
      NativeOmegaPreparation.DayIndexOrder.comparison (𝟙_ I) (𝟙_ V)).app N.X
  let q₀ := (u ▷ N.X) ≫ (λ_ N.X).hom
  have hp : c.hom ≫ p = MonoidalClosed.curry q₀ ≫ d.hom := by
    change c.hom ≫ (Mod.FreeInternalHom.forward A P N ≫ d.hom) = _
    exact (Category.assoc c.hom (Mod.FreeInternalHom.forward A P N) d.hom).symm.trans
      (congrArg (fun f => f ≫ d.hom) hc)
  let z := N.X.functor.map (ρ_ n).inv ≫
    MonoidalClosed.unitNatIso.hom.app (N.X.functor.obj (n ⊗ (𝟙_ I)))
  have hz : z ≫ d.inv.natTrans.app n = (MonoidalClosed.curry q₀).natTrans.app n :=
    FreeFunctionSourceEvaluation.original_zero_end_inverse_unit N.X n
  have hi : d.inv.natTrans.app n ≫ d.hom.natTrans.app n = 𝟙 _ :=
    congrArg (fun f => f.natTrans.app n) d.inv_hom_id
  have hLevel := congrArg (fun f => f.natTrans.app n) hp
  change (c.hom ≫ p).natTrans.app n = z
  exact hLevel.trans ((congrArg (fun f => f ≫ d.hom.natTrans.app n) hz.symm).trans
    ((Category.assoc z (d.inv.natTrans.app n) (d.hom.natTrans.app n)).trans
      ((congrArg (fun f => z ≫ f) hi).trans (Category.comp_id z))))

end NativeOmegaRecovery.SelectedUnitTensorCompatibility.Day

namespace NativeOmegaRecovery.SelectedUnitTensorCompatibility
universe uD vD
variable {D : Type uD} [Category.{vD} D]

/-- The original three adjunctions transpose the same whole carrier image. -/
theorem transported_homEquiv_image {C : Type uC} [Category.{vC} C]
    (E : C ≌ D) {F G : C ⥤ C} (a : F ⊣ G) (X Y : D)
    (q : F.obj (E.inverse.obj X) ⟶ E.inverse.obj Y) :
    (((E.symm.toAdjunction.comp a).comp E.toAdjunction).homEquiv X Y)
        (E.functor.map q ≫ E.counitIso.hom.app Y) =
      E.counitIso.inv.app X ≫ E.functor.map
        (a.homEquiv (E.inverse.obj X) (E.inverse.obj Y) q) := by
  have hE : E.toAdjunction.homEquiv (F.obj (E.inverse.obj X)) Y
      (E.functor.map q ≫ E.counitIso.hom.app Y) = q := by
    rw [Adjunction.homEquiv_unit, E.inverse.map_comp]
    change E.unitIso.hom.app (F.obj (E.inverse.obj X)) ≫
      E.inverse.map (E.functor.map q) ≫ E.inverse.map (E.counitIso.hom.app Y) = q
    have hn := E.unitIso.hom.naturality q
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    rw [← Category.assoc, ← hn, Category.assoc, E.unit_inverse_comp]
    exact Category.comp_id q
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change E.symm.toAdjunction.homEquiv X (G.obj (E.inverse.obj Y))
    (a.homEquiv (E.inverse.obj X) (E.inverse.obj Y)
      (E.toAdjunction.homEquiv (F.obj (E.inverse.obj X)) Y
        (E.functor.map q ≫ E.counitIso.hom.app Y))) = _
  rw [hE, Adjunction.homEquiv_unit]
  rfl

/-- The unchanged source and carrier triangles recover every original full arrow. -/
theorem inverseImage_unit_arrow {C : Type uC} [Category.{vC} C]
    (E : C ≌ D) (X : D) (U : C) (f : E.inverse.obj X ⟶ U) :
    E.inverse.map (E.counitIso.inv.app X ≫ E.functor.map f) ≫
      E.unitIso.inv.app U = f := by
  rw [E.inverse.map_comp]
  have hUnit : E.inverse.map (E.counitIso.inv.app X) =
      E.unitIso.hom.app (E.inverse.obj X) := (E.unit_app_inverse X).symm
  have hn := E.unitIso.hom.naturality f
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [hUnit, ← hn]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

end NativeOmegaRecovery.SelectedUnitTensorCompatibility

namespace NativeOmegaRecovery.SelectedUnitTensorCompatibility
universe uD vD
variable {D : Type uD} [Category.{vD} D]

/-- The source equation is identified before the entire original unit inverse
is read on any complete original module image. -/
theorem function_unit_inv_of_module_mate {C : Type uC} [Category.{vC} C]
    (E : C ≌ D) {F : C ⥤ C} {R : D ⥤ D}
    (e : F ≅ E.functor ⋙ R ⋙ E.inverse) (u : R ≅ 𝟭 D)
    (τ : 𝟭 C ⟶ F)
    (h : ∀ N : C, τ.app N ≫ e.hom.app N =
      E.unitIso.hom.app N ≫ E.inverse.map (u.inv.app (E.functor.obj N))) (N : C) :
    (OriginalCarrierZeroSourceUnit.functionUnitIso E e u).inv.app (E.functor.obj N) =
      E.counitIso.inv.app (E.functor.obj N) ≫
        E.functor.map (τ.app (E.inverse.obj (E.functor.obj N))) := by
  let k := E.unitIso.hom.app N
  let p := E.inverse.map (u.inv.app (E.functor.obj N))
  let b := e.inv.app N
  have hm : k ≫ p ≫ b = τ.app N := by
    have h₁ := congrArg (fun z => z ≫ b) (h N).symm
    change (k ≫ p) ≫ b = (τ.app N ≫ e.hom.app N) ≫ b at h₁
    have hCancel : e.hom.app N ≫ b = 𝟙 (F.obj N) := e.hom_inv_id_app N
    simpa only [Category.assoc, hCancel, Category.comp_id] using h₁
  have hw : k ≫ p ≫ b ≫ F.map k = k ≫ τ.app (E.inverse.obj (E.functor.obj N)) := by
    have h₁ := congrArg (fun z => z ≫ F.map k) hm
    have hn := τ.naturality k
    change k ≫ τ.app (E.inverse.obj (E.functor.obj N)) = τ.app N ≫ F.map k at hn
    simpa only [Category.assoc] using h₁.trans hn.symm
  have hUnit : E.functor.map k = E.counitIso.inv.app (E.functor.obj N) :=
    (E.counitInv_app_functor N).symm
  have hRecipe := OriginalCarrierZeroSourceUnit.functionUnitIso_inv_on_image E e u N
  change (OriginalCarrierZeroSourceUnit.functionUnitIso E e u).inv.app (E.functor.obj N) =
    E.functor.map (k ≫ p ≫ b ≫ F.map k) at hRecipe
  exact hRecipe.trans ((congrArg E.functor.map hw).trans
    ((E.functor.map_comp k (τ.app (E.inverse.obj (E.functor.obj N)))).trans
      (congrArg (fun z => z ≫ E.functor.map (τ.app (E.inverse.obj (E.functor.obj N)))) hUnit)))

/-- The original transported tensor and left unitor keep the actual whole
carrier action of any genuine source map into the same tensor unit. -/
theorem transported_unit_action {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    (E : C ≌ D) (X Y : D) (f : E.inverse.obj X ⟶ (𝟙_ C)) :
    let _ : MonoidalCategory D := Monoidal.transport E
    ((E.counitIso.inv.app X ≫ E.functor.map f) ▷ Y) ≫ (λ_ Y).hom =
      E.functor.map ((f ▷ E.inverse.obj Y) ≫ (λ_ (E.inverse.obj Y)).hom) ≫
        E.counitIso.hom.app Y := by
  let _ : MonoidalCategory D := Monoidal.transport E
  let t := E.counitIso.inv.app X ≫ E.functor.map f
  let q := E.inverse.map t
  let N := E.inverse.obj Y
  let k := E.unitIso.inv.app (𝟙_ C)
  have ht : q ≫ k = f := inverseImage_unit_arrow E X (𝟙_ C) f
  change E.functor.map (q ▷ N) ≫
      (E.functor.map ((k ▷ N) ≫ (λ_ N).hom) ≫ E.counitIso.hom.app Y) = _
  rw [← Category.assoc, ← E.functor.map_comp]
  rw [← comp_whiskerRight_assoc, ht]

/-- The same chosen component at the tensor unit identifies its original
right-unitor source map with the given whole tensor action. -/
theorem selected_unit_map_eq {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
    (A : C) (s : A ⊗ (𝟙_ C) ⟶ (𝟙_ C)) (t : A ⟶ (𝟙_ C))
    (h : s = (t ▷ (𝟙_ C)) ≫ (λ_ (𝟙_ C)).hom) :
    (ρ_ A).inv ≫ s = t := by
  rw [h, unitors_equal, rightUnitor_naturality, Iso.inv_hom_id_assoc]

end NativeOmegaRecovery.SelectedUnitTensorCompatibility

namespace NativeOmegaRecovery.NativeSymmetricSelectedUnit
universe u v
open CategoryTheory.EnrichedFunctorCat
private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev Sequence := PointedCGWH.SymmetricSequence.{u, v}
private abbrev A := PointedCGWH.sphereSequenceCommMon.{u, v}
private abbrev S := PointedCGWH.sphereSequence.{u, v}
private abbrev Modules := NativeSymmetricFreeFunction.OriginalModule.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev E := PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}
private abbrev P₀ : Sequence.{u, v} :=
  .mk ((evaluationLeftAdjoint V.{u, v} (𝟙_ I)).obj (𝟙_ V.{u, v}))

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

open PointedCGWH.SymmetricModulePresentation
open NativeSymmetricFreeFunction

/-- The same actual scalar/index unit inverse retains the original scalar
closed unit and original index right-unitor inverse at every native output. -/
theorem zeroScalarIndexUnit_inv_component (N : Modules.{u, v}) (n : I) :
    component (zeroScalarIndexUnit.{u, v}.inv.app (E.{u, v}.functor.obj N))
        (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      N.X.functor.map (ρ_ n).inv ≫
        MonoidalClosed.unitNatIso.hom.app (N.X.functor.obj (n ⊗ (𝟙_ I))) := by
  let X : Carrier.{u, v} := E.{u, v}.functor.obj N
  let F := PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ I)
  let a : X ⟶ F.obj X := NativeSymmetricShiftUnit.comparison.inv.app X
  let b : F.obj X ⟶ F.obj X := (Functor.rightUnitor F).inv.app X
  let c : F.obj X ⟶ (F ⋙ cotensor (𝟙_ V.{u, v})).obj X :=
    (Functor.isoWhiskerLeft F OriginalCotensorUnit.comparison).inv.app X
  let rhs : X ⟶ (F ⋙ cotensor (𝟙_ V.{u, v})).obj X := a ≫ b ≫ c
  have hWhole : zeroScalarIndexUnit.{u, v}.inv.app X = rhs :=
    EvaluatedComparisonMaps.triple_inv_app
      (Functor.isoWhiskerLeft F OriginalCotensorUnit.comparison)
      (Functor.rightUnitor F) NativeSymmetricShiftUnit.comparison X
  have ha : component a (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      NativeSymmetricShiftUnit.ordinaryMap X (ρ_ n).inv := NativeSymmetricShiftUnit.comparison_inv_component X n
  have hb : b = 𝟙 (F.obj X) := rfl
  have hc : component c (PointedCGWH.symmetricOperatorObj.{u, v} n) =
      MonoidalClosed.unitNatIso.hom.app (N.X.functor.obj (n ⊗ (𝟙_ I))) :=
    OriginalCotensorUnit.unitMap_component (F.obj X) (PointedCGWH.symmetricOperatorObj.{u, v} n)
  have hOrd : NativeSymmetricShiftUnit.ordinaryMap X (ρ_ n).inv = N.X.functor.map (ρ_ n).inv :=
    symmetricSequenceRestriction_forward_map N (ρ_ n).inv
  have hLevel := congrArg (fun f => component f (PointedCGWH.symmetricOperatorObj.{u, v} n)) hWhole
  change component (zeroScalarIndexUnit.{u, v}.inv.app X)
    (PointedCGWH.symmetricOperatorObj.{u, v} n) = _
  exact hLevel.trans ((component_comp a (b ≫ c) (PointedCGWH.symmetricOperatorObj.{u, v} n)).trans
    ((congrArg₂ (fun f g => f ≫ g) ha
      ((congrArg (fun f => component f (PointedCGWH.symmetricOperatorObj.{u, v} n))
        ((congrArg (fun f => f ≫ c) hb).trans (Category.id_comp c))).trans hc)).trans
      (congrArg (fun f => f ≫ MonoidalClosed.unitNatIso.hom.app
        (N.X.functor.obj (n ⊗ (𝟙_ I)))) hOrd)))

end NativeOmegaRecovery.NativeSymmetricSelectedUnit

namespace NativeOmegaRecovery.SelectedUnitTensorCompatibility
universe uD vD
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]
  (A : CommMon C)

/-- The original whole module tensor record used by the source contraction. -/
local instance contractionModuleMonoidal : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
/-- The original whole internal-Hom record used by that source contraction. -/
local instance contractionModuleClosed : MonoidalClosed (Mod C A.X) := Mod.instMonoidalClosed A

/-- The entire actual contraction and selected module unitor retain every
original target module map. -/
def contractionAction (P : C) (u : P ⟶ (𝟙_ C)) :
    (Mod.relativeTensor A).obj ((Mod.free A.X).obj P) ⟶ 𝟭 (Mod C A.X) where
  app N := Mod.relativeTensorMap A (freeUnitContraction A P u) (𝟙 N) ≫ (λ_ N).hom
  naturality {N N'} f := by
    let F : Mod C A.X := (Mod.free A.X).obj P
    let t : F ⟶ (𝟙_ (Mod C A.X)) := freeUnitContraction A P u
    let l : (𝟙_ (Mod C A.X)) ⊗ N ⟶ N := (λ_ N).hom
    let l' : (𝟙_ (Mod C A.X)) ⊗ N' ⟶ N' := (λ_ N').hom
    have hw : (F ◁ f) ≫ (t ▷ N') = (t ▷ N) ≫ ((𝟙_ (Mod C A.X)) ◁ f) :=
      whisker_exchange t f
    have hl : ((𝟙_ (Mod C A.X)) ◁ f) ≫ l' = l ≫ f := leftUnitor_naturality f
    change (F ◁ f) ≫ ((t ⊗ₘ 𝟙 N') ≫ l') = ((t ⊗ₘ 𝟙 N) ≫ l) ≫ f
    rw [tensorHom_id, tensorHom_id]
    exact (Category.assoc (F ◁ f) (t ▷ N') l').symm.trans
      ((congrArg (fun q => q ≫ l') hw).trans
        ((Category.assoc (t ▷ N) ((𝟙_ (Mod C A.X)) ◁ f) l').trans
          ((congrArg (fun q => (t ▷ N) ≫ q) hl).trans
            (Category.assoc (t ▷ N) l f).symm)))

/-- The original balanced adjunction transposes that entire natural action. -/
def contractionCurry (P : C) (u : P ⟶ (𝟙_ C)) :
    𝟭 (Mod C A.X) ⟶ Mod.internalHom A ((Mod.free A.X).obj P) where
  app N := (Mod.relativeTensorInternalHomAdjunction A ((Mod.free A.X).obj P)).homEquiv N N
    ((contractionAction A P u).app N)
  naturality {N N'} f := by
    let adj := Mod.relativeTensorInternalHomAdjunction A ((Mod.free A.X).obj P)
    have hs := (contractionAction A P u).naturality f
    change f ≫ adj.homEquiv N' N' ((contractionAction A P u).app N') =
      adj.homEquiv N N ((contractionAction A P u).app N) ≫
        (Mod.internalHom A ((Mod.free A.X).obj P)).map f
    exact (adj.homEquiv_naturality_left f ((contractionAction A P u).app N')).symm.trans
      ((congrArg (adj.homEquiv N N') hs).trans
        (adj.homEquiv_naturality_right ((contractionAction A P u).app N) f))

/-- Each complete original component remains its selected balanced adjunct. -/
theorem contractionCurry_app (P : C) (u : P ⟶ (𝟙_ C)) (N : Mod C A.X) :
    (contractionCurry A P u).app N =
      (Mod.relativeTensorInternalHomAdjunction A ((Mod.free A.X).obj P)).homEquiv N N
        (Mod.relativeTensorMap A (freeUnitContraction A P u) (𝟙 N) ≫ (λ_ N).hom) := rfl

/-- The original selected module adjunct is natural under every whole source
arrow, retaining its actual relative-tensor map and internal-Hom pre-map. -/
theorem module_curry_pre {M M' : Mod C A.X} (f : M ⟶ M') (N K : Mod C A.X)
    (q : ((Mod.relativeTensor A).obj M').obj N ⟶ K) :
    (Mod.relativeTensorInternalHomAdjunction A M).homEquiv N K
        (Mod.relativeTensorMap A f (𝟙 N) ≫ q) =
      (Mod.relativeTensorInternalHomAdjunction A M').homEquiv N K q ≫
        (MonoidalClosed.pre f).app K := by
  change MonoidalClosed.curry ((f ⊗ₘ 𝟙 N) ≫ q) =
    MonoidalClosed.curry q ≫ (MonoidalClosed.pre f).app K
  rw [tensorHom_id]
  exact (MonoidalClosed.curry_pre_app f q).symm

/-- The whole original free source comparison retains its actual pre-map
before any native target or enriched coordinate is projected. -/
theorem original_sourceComparison_hom
    {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D)
    (M : Mod C A.X) (X Y : D) (e : M ≅ E.inverse.obj X) :
    (Mod.EquivalenceFunctionTransport.sourceComparison A E M X e).hom.app Y =
      E.functor.map ((MonoidalClosed.pre e.inv).app (E.inverse.obj Y)) := rfl

/-- The same actual transported adjunction maps every whole original carrier
image through its original balanced adjunction and carrier counit. -/
theorem original_adjunction_homEquiv_image
    {D : Type uD} [Category.{vD} D] (E : Mod C A.X ≌ D) (S X Y : D)
    (q : ((Mod.relativeTensor A).obj (E.inverse.obj S)).obj (E.inverse.obj X) ⟶ E.inverse.obj Y) :
    (Mod.EquivalenceFunctionTransport.adjunction A E S).homEquiv X Y
        (E.functor.map q ≫ E.counitIso.hom.app Y) =
      E.counitIso.inv.app X ≫ E.functor.map
        ((Mod.relativeTensorInternalHomAdjunction A (E.inverse.obj S)).homEquiv
          (E.inverse.obj X) (E.inverse.obj Y) q) := by
  let a := Mod.relativeTensorInternalHomAdjunction A (E.inverse.obj S)
  let b := (E.symm.toAdjunction.comp a).comp E.toAdjunction
  let e := (eqToIso (Mod.EquivalenceFunctionTransport.sourceFunctor_obj A E (E.inverse.obj S))).symm
  have he : e.hom.app Y = 𝟙 _ := rfl
  change (b.ofNatIsoRight e).homEquiv X Y (E.functor.map q ≫ E.counitIso.hom.app Y) = _
  have h₀ := Adjunction.homEquiv_ofNatIsoRight_apply b e
    (E.functor.map q ≫ E.counitIso.hom.app Y)
  exact h₀.trans
    ((congrArg (fun f => b.homEquiv X Y (E.functor.map q ≫ E.counitIso.hom.app Y) ≫ f) he).trans
      ((Category.comp_id (b.homEquiv X Y (E.functor.map q ≫ E.counitIso.hom.app Y))).trans
        (transported_homEquiv_image E a X Y q)))

end NativeOmegaRecovery.SelectedUnitTensorCompatibility

namespace NativeOmegaRecovery.NativeSymmetricSelectedUnit
universe u v
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.SymmetricModulePresentation
open NativeSymmetricFreeFunction
open SelectedUnitTensorCompatibility

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

/-- The same inverse-carrier image keeps the original whole scalar/index
unit arrow before its actual original output coordinate is selected. -/
theorem inverse_zeroScalarIndexUnit_component (N : Modules.{u, v}) (n : I) :
    (E.{u, v}.inverse.map (zeroScalarIndexUnit.{u, v}.inv.app (E.{u, v}.functor.obj N))).hom.natTrans.app n =
      N.X.functor.map (ρ_ n).inv ≫
        MonoidalClosed.unitNatIso.hom.app (N.X.functor.obj (n ⊗ (𝟙_ I))) := by
  let X : Carrier.{u, v} := E.{u, v}.functor.obj N
  let t : X ⟶ (PointedCGWH.SymmetricShift.functor.{u, v} (𝟙_ I) ⋙ cotensor (𝟙_ V.{u, v})).obj X :=
    zeroScalarIndexUnit.{u, v}.inv.app X
  let m := E.{u, v}.inverse.map t
  have hm := reconstructedModuleMap_hom t
  have hr := PointedCGWH.symmetricSequenceRestriction_component t n
  have hz := zeroScalarIndexUnit_inv_component N n
  change m.hom.natTrans.app n = _
  exact (congrArg (fun f => f.natTrans.app n) hm).trans (hr.trans hz)


end NativeOmegaRecovery.NativeSymmetricSelectedUnit

namespace NativeOmegaRecovery.SelectedUnitTensorCompatibility
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C]
  (A : CommMon C)
/-- The original whole module tensor record used by the given source word. -/
local instance sourceModuleMonoidal : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A

/-- The same whole original source map and module unitor form a natural action. -/
def contractionActionSource (M : Mod C A.X) (t : M ⟶ Mod.regular A.X) :
    (Mod.relativeTensor A).obj M ⟶ 𝟭 (Mod C A.X) where
  app N := Mod.relativeTensorMap A t (𝟙 N) ≫ (λ_ N).hom
  naturality {N N'} f := by
    let t' : M ⟶ (𝟙_ (Mod C A.X)) := t
    let l : (𝟙_ (Mod C A.X)) ⊗ N ⟶ N := (λ_ N).hom
    let l' : (𝟙_ (Mod C A.X)) ⊗ N' ⟶ N' := (λ_ N').hom
    have hw : (M ◁ f) ≫ (t' ▷ N') = (t' ▷ N) ≫ ((𝟙_ (Mod C A.X)) ◁ f) :=
      whisker_exchange t' f
    have hl : ((𝟙_ (Mod C A.X)) ◁ f) ≫ l' = l ≫ f := leftUnitor_naturality f
    change (M ◁ f) ≫ ((t' ⊗ₘ 𝟙 N') ≫ l') = ((t' ⊗ₘ 𝟙 N) ≫ l) ≫ f
    rw [tensorHom_id, tensorHom_id]
    exact (Category.assoc (M ◁ f) (t' ▷ N') l').symm.trans
      ((congrArg (fun q => q ≫ l') hw).trans
        ((Category.assoc (t' ▷ N) ((𝟙_ (Mod C A.X)) ◁ f) l').trans
          ((congrArg (fun q => (t' ▷ N) ≫ q) hl).trans (Category.assoc (t' ▷ N) l f).symm)))

/-- The original balanced adjunction transposes the same given whole source action. -/
def contractionCurrySource (M : Mod C A.X) (t : M ⟶ Mod.regular A.X) :
    𝟭 (Mod C A.X) ⟶ Mod.internalHom A M where
  app N := (Mod.relativeTensorInternalHomAdjunction A M).homEquiv N N
    ((contractionActionSource A M t).app N)
  naturality {N N'} f := by
    let adj := Mod.relativeTensorInternalHomAdjunction A M
    have hs := (contractionActionSource A M t).naturality f
    change f ≫ adj.homEquiv N' N' ((contractionActionSource A M t).app N') =
      adj.homEquiv N N ((contractionActionSource A M t).app N) ≫ (Mod.internalHom A M).map f
    exact (adj.homEquiv_naturality_left f ((contractionActionSource A M t).app N')).symm.trans
      ((congrArg (adj.homEquiv N N') hs).trans
        (adj.homEquiv_naturality_right ((contractionActionSource A M t).app N) f))

omit [BraidedCategory C] [MonoidalClosed C] [HasCoequalizers C] [HasEqualizers C] in
/-- Equality of the complete original monoid data retains every free object. -/
theorem free_obj_monObj_heq (R : C) (m m' : MonObj R) (h : m = m') (P : C) :
    HEq (letI : MonObj R := m; (Mod.free R).obj P)
      (letI : MonObj R := m'; (Mod.free R).obj P) := by
  cases h
  rfl

end NativeOmegaRecovery.SelectedUnitTensorCompatibility

namespace NativeOmegaRecovery.NativeSymmetricSelectedUnit
universe u v
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.SymmetricModulePresentation
open NativeSymmetricFreeFunction
open SelectedUnitTensorCompatibility
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

/-- The original given free-zero module and its original contraction determine
this entire actual balanced adjunct, with no reconstructed source object. -/
def originalContractionCurry :=
  contractionCurrySource A.{u, v}
    (NativeSymmetricFreeSource.freeModule.{u, v} (𝟙_ I) (𝟙_ V.{u, v}))
    NativeSymmetricSourceGEN.actualZeroFreeContraction.{u, v}

/-- Equality of the complete original monoid data identifies the actual two
free constructors before their complete internal Homs are formed. -/
theorem original_free_source_heq :
    HEq ((Mod.free S.{u, v}).obj P₀.{u, v}) ((Mod.free A.{u, v}.X).obj P₀.{u, v}) := by
  exact free_obj_monObj_heq S.{u, v}
    PointedCGWH.sphereSequenceMonObj.{u, v} A.{u, v}.mon
    (NativeScalarCoefficient.sphereCoefficient_mon_eq.{u, v}).symm P₀.{u, v}

end NativeOmegaRecovery.NativeSymmetricSelectedUnit

namespace NativeOmegaRecovery.SelectedUnitTensorCompatibility
universe uI vI uV vV
variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [MonoidalCategory (DayFunctor I V)] (S : DayFunctor I V) [MonObj S]
  [∀ (r a : I), HasCoproductsOfShape (r ⟶ a) V]

/-- The original Day free object retains the actual free/evaluation composite. -/
theorem dayFreeAt_obj_original (r : I) (M : V) :
    (Mod.dayFreeAt S r).obj M =
      (Mod.free S).obj (.mk ((evaluationLeftAdjoint V r).obj M)) := rfl

end NativeOmegaRecovery.SelectedUnitTensorCompatibility

namespace NativeOmegaRecovery.NativeSymmetricSelectedUnit
universe u v
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.SymmetricModulePresentation
open NativeSymmetricFreeFunction
open SelectedUnitTensorCompatibility
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

/-- The original complete source equality is obtained before applying IH. -/
theorem original_day_free_source :
    NativeSymmetricFreeSource.freeModule.{u, v} (𝟙_ I) (𝟙_ V.{u, v}) =
      (Mod.free S.{u, v}).obj P₀.{u, v} :=
  dayFreeAt_obj_original S.{u, v} (𝟙_ I) (𝟙_ V.{u, v})

/-- This is the same whole internal-Hom functor source, with the actual
free/evaluation equality retained before object application. -/
theorem original_contraction_functor_source :
    Mod.internalHom A.{u, v}
      (NativeSymmetricFreeSource.freeModule.{u, v} (𝟙_ I) (𝟙_ V.{u, v})) =
    Mod.internalHom A.{u, v} ((Mod.free S.{u, v}).obj P₀.{u, v}) :=
  congrArg (Mod.internalHom A.{u, v}) original_day_free_source.{u, v}

end NativeOmegaRecovery.NativeSymmetricSelectedUnit
