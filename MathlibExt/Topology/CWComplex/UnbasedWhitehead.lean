/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.BasedWhiteheadUniverseLift
public import Mathlib.Topology.Homotopy.Equiv
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CellFamilyModel
import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.ContinuousWhitehead
public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homotopy.Path

/-!
# Whitehead for genuine unbased classical CW types

The existing classical-subcomplex lifting theorem supplies cofibrancy. The
ordinary compact-open path object interprets model right homotopies as actual
continuous homotopies. The independently sized model transport retains the
literal original forward map, without requiring calibrated model points.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat.modelCategory ContinuousMap

universe u v w

namespace Topology.CWComplex

namespace UnbasedWhiteheadConstruction

private theorem constantPath_weak (X : TopCat.{u}) :
    TopCat.weakHomotopyEquivalences (TopCat.pathConstant X) := by
  have hc : TopCat.weakHomotopyEquivalences
      (TopCat.pathConstant X ≫ TopCat.pathEvalZero X) := by
    rw [TopCat.pathConstant_evalZero]
    exact TopCat.weakHomotopyEquivalences.of_isIso _
  exact TopCat.weakHomotopyEquivalences.of_postcomp _ _
    (TopCat.pathEvalZero_mem_weakHomotopyEquivalences X) hc

private def actualContinuousPathObject (X : TopCat.{u}) : PathObject X where
  P := TopCat.pathObject X
  p₀ := TopCat.pathEvalZero X
  p₁ := TopCat.pathEvalOne X
  ι := TopCat.pathConstant X
  ι_p₀ := TopCat.pathConstant_evalZero X
  ι_p₁ := TopCat.pathConstant_evalOne X
  weakEquivalence_ι := (weakEquivalence_iff _).mpr (constantPath_weak X)

private theorem actualContinuousPathObject_good (X : TopCat.{u}) :
    (actualContinuousPathObject X).IsGood := by
  constructor
  have hp : (actualContinuousPathObject X).p = TopCat.pathEndpoints X := rfl
  rw [hp]
  exact TopCat.modelCategory.pathEndpoints_fibration X

private def continuousHomotopyOfActualRightHomotopy
    {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (H : (actualContinuousPathObject Y).RightHomotopy f g) : TopCat.Homotopy f g := by
  let h : C(X, C(TopCat.I.{u}, Y)) := H.h.hom
  have h₀ : H.h ≫ TopCat.pathEvalZero Y = f := H.h₀
  have h₁ : H.h ≫ TopCat.pathEvalOne Y = g := H.h₁
  refine
    { toFun := fun z => h z.2 ((TopCat.I.homeomorph.{u}).symm z.1)
      continuous_toFun := continuous_eval.comp
        ((h.continuous.comp continuous_snd).prodMk
          ((TopCat.I.homeomorph.{u}).symm.continuous.comp continuous_fst))
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro z
    have ht : (TopCat.I.homeomorph.{u}).symm (0 : unitInterval) =
        (0 : TopCat.I.{u}) := by
      apply (TopCat.I.homeomorph.{u}).injective
      simp
    exact (congrArg (fun t : TopCat.I.{u} => h z t) ht).trans
      (ConcreteCategory.congr_hom h₀ z)
  · intro z
    have ht : (TopCat.I.homeomorph.{u}).symm (1 : unitInterval) =
        (1 : TopCat.I.{u}) := by
      apply (TopCat.I.homeomorph.{u}).injective
      simp
    exact (congrArg (fun t : TopCat.I.{u} => h z t) ht).trans
      (ConcreteCategory.congr_hom h₁ z)

/-- A weak map between actual cofibrant topological spaces has a continuous
homotopy inverse. All topological objects are fibrant; the original forward
map and BOTH inverse homotopies are retained. -/
public def _root_.TopCat.cofibrantWeakHomotopyEquiv
    (X Y : TopCat.{u}) [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) (hf : TopCat.weakHomotopyEquivalences f) :
    {e : X ≃ₕ Y // e.toFun = f.hom} := by
  letI : IsFibrant X := SSet.RealizationCWUpgrade.allTopCatObjectsFibrant X
  letI : IsFibrant Y := SSet.RealizationCWUpgrade.allTopCatObjectsFibrant Y
  letI : WeakEquivalence f := (weakEquivalence_iff _).mpr hf
  let h := RightHomotopyClass.whitehead f
  let g : Y ⟶ X := Classical.choose h
  have hL : RightHomotopyRel (f ≫ g) (𝟙 X) := (Classical.choose_spec h).1
  have hR : RightHomotopyRel (g ≫ f) (𝟙 Y) := (Classical.choose_spec h).2
  letI : (actualContinuousPathObject X).IsGood := actualContinuousPathObject_good X
  letI : (actualContinuousPathObject Y).IsGood := actualContinuousPathObject_good Y
  let HL := continuousHomotopyOfActualRightHomotopy
    (hL.rightHomotopy (actualContinuousPathObject X))
  let HR := continuousHomotopyOfActualRightHomotopy
    (hR.rightHomotopy (actualContinuousPathObject Y))
  exact
    ⟨{ toFun := f.hom
       invFun := g.hom
       left_inv := ⟨HL.cast (TopCat.hom_comp f g) (TopCat.hom_id (X := X))⟩
       right_inv := ⟨HR.cast (TopCat.hom_comp g f) (TopCat.hom_id (X := Y))⟩ }, rfl⟩

/-- The generic cofibrant constructor uses the literal original map. -/
public theorem _root_.TopCat.cofibrantWeakHomotopyEquiv_toFun
    (X Y : TopCat.{u}) [IsCofibrant X] [IsCofibrant Y]
    (f : X ⟶ Y) (hf : TopCat.weakHomotopyEquivalences f) :
    (TopCat.cofibrantWeakHomotopyEquiv X Y f hf).val.toFun = f.hom :=
  (TopCat.cofibrantWeakHomotopyEquiv X Y f hf).property

private def classicalCWWeakHomotopyEquiv
    (X Y : TopCat.{u}) [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : TopCat.weakHomotopyEquivalences f) :
    {e : X ≃ₕ Y // e.toFun = f.hom} := by
  letI : IsCofibrant X := AlgebraicTopology.CellFamilySimplicialModel.isCofibrant_of_classicalCW X
  letI : IsCofibrant Y := AlgebraicTopology.CellFamilySimplicialModel.isCofibrant_of_classicalCW Y
  exact TopCat.cofibrantWeakHomotopyEquiv X Y f hf

private def replaceForwardMap {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (f : C(X, Y))
    (h : e.toFun.Homotopic f) : X ≃ₕ Y where
  toFun := f
  invFun := e.invFun
  left_inv := ((ContinuousMap.Homotopic.refl e.invFun).comp h.symm).trans e.left_inv
  right_inv := (h.symm.comp (ContinuousMap.Homotopic.refl e.invFun)).trans e.right_inv

end UnbasedWhiteheadConstruction

public section

/-- A weak map between actual Hausdorff classical CW spaces admits an actual
homotopy equivalence with the SAME forward map. Both inverse families are retained. -/
theorem unbasedCWWhitehead
    (X Y : TopCat.{u}) [T2Space X] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : X ⟶ Y) (hf : TopCat.weakHomotopyEquivalences f) :
    ∃ e : X ≃ₕ Y, e.toFun = f.hom := by
  let e := UnbasedWhiteheadConstruction.classicalCWWeakHomotopyEquiv X Y f hf
  exact ⟨e.val, e.property⟩

/-- Genuine unbased CW models may have independent universes. Their actual
homotopy equivalences are transported without extra based-model data, and the
original `f` is the literal forward map of the returned equivalence. -/
theorem unbasedCWTypeWhiteheadIndependentModels
    {X Y : TopCat.{u}} (CX : TopCat.{v}) (CY : TopCat.{w})
    [T2Space CX] [T2Space CY]
    [Topology.CWComplex (Set.univ : Set CX)] [Topology.CWComplex (Set.univ : Set CY)]
    (ex : CX ≃ₕ X) (ey : CY ≃ₕ Y) (f : X ⟶ Y)
    (hf : TopCat.weakHomotopyEquivalences f) :
    ∃ e : X ≃ₕ Y, e.toFun = f.hom := by
  let F := TopCat.uliftFunctor.{max v w, u}
  let XU : TopCat.{max u v w} := F.obj X
  let YU : TopCat.{max u v w} := F.obj Y
  let CXU : TopCat.{max u v w} := TopCat.uliftFunctor.{max u w, v}.obj CX
  let CYU : TopCat.{max u v w} := TopCat.uliftFunctor.{max u v, w}.obj CY
  let ux : X ≃ₜ XU := X.uliftFunctorObjHomeo
  let uy : Y ≃ₜ YU := Y.uliftFunctorObjHomeo
  let ucx : CX ≃ₜ CXU := CX.uliftFunctorObjHomeo
  let ucy : CY ≃ₜ CYU := CY.uliftFunctorObjHomeo
  let : T2Space CXU := by change T2Space (ULift.{max u w} CX); infer_instance
  let : T2Space CYU := by change T2Space (ULift.{max u v} CY); infer_instance
  let : Topology.CWComplex (Set.univ : Set CXU) := Topology.CWComplex.uliftCWComplex CX
  let : Topology.CWComplex (Set.univ : Set CYU) := Topology.CWComplex.uliftCWComplex CY
  let exU : CXU ≃ₕ XU := ucx.symm.toHomotopyEquiv.trans (ex.trans ux.toHomotopyEquiv)
  let eyU : CYU ≃ₕ YU := ucy.symm.toHomotopyEquiv.trans (ey.trans uy.toHomotopyEquiv)
  let fU : XU ⟶ YU := F.map f
  have hfU : TopCat.weakHomotopyEquivalences fU :=
    TopCat.uliftFunctor_map_mem_weakHomotopyEquivalences.{u, max v w} f hf
  let sx : CXU ⟶ XU := TopCat.ofHom exU.toFun
  let ry : YU ⟶ CYU := TopCat.ofHom eyU.invFun
  let m : CXU ⟶ CYU := sx ≫ fU ≫ ry
  have hm : TopCat.weakHomotopyEquivalences m :=
    TopCat.weakHomotopyEquivalences.comp_mem sx (fU ≫ ry)
      (TopCat.homotopyEquiv_toFun_mem exU)
      (TopCat.weakHomotopyEquivalences.comp_mem fU ry hfU
        (TopCat.homotopyEquiv_invFun_mem eyU))
  obtain ⟨em, hem⟩ := unbasedCWWhitehead CXU CYU m hm
  have hm_hom : (TopCat.Hom.hom m : C(CXU, CYU)) =
      eyU.invFun.comp (fU.hom.comp exU.toFun) := by
    calc
      (TopCat.Hom.hom m : C(CXU, CYU)) =
          (TopCat.Hom.hom (fU ≫ ry)).comp (TopCat.Hom.hom sx) :=
        TopCat.hom_comp sx (fU ≫ ry)
      _ = ((TopCat.Hom.hom ry).comp (TopCat.Hom.hom fU)).comp
          (TopCat.Hom.hom sx) :=
        congrArg (fun h : C(XU, CYU) => h.comp (TopCat.Hom.hom sx))
          (TopCat.hom_comp fU ry)
      _ = eyU.invFun.comp (fU.hom.comp exU.toFun) := by
        rw [ContinuousMap.comp_assoc]
        rfl
  let q : XU ≃ₕ YU := exU.symm.trans (em.trans eyU)
  have hq : q.toFun.Homotopic fU.hom := by
    have h₁ := eyU.right_inv.comp (ContinuousMap.Homotopic.refl
      (fU.hom.comp (exU.toFun.comp exU.invFun)))
    have h₂ := (ContinuousMap.Homotopic.refl fU.hom).comp exU.right_inv
    change (eyU.toFun.comp (em.toFun.comp exU.invFun)).Homotopic fU.hom
    rw [hem, hm_hom]
    simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp,
      ContinuousMap.comp_id] using h₁.trans h₂
  let q' : XU ≃ₕ YU := UnbasedWhiteheadConstruction.replaceForwardMap q fU.hom hq
  let e : X ≃ₕ Y := ux.toHomotopyEquiv.trans (q'.trans uy.symm.toHomotopyEquiv)
  have he : e.toFun = f.hom := by
    ext x
    change uy.symm (fU (ux x)) = f x
    rw [TopCat.uliftFunctorObjHomeo_naturality_apply]
    exact uy.symm_apply_apply (f x)
  exact ⟨e, he⟩

end

namespace ActualConnectedCWTypePaths

open Set Topology
open scoped ContinuousMap

/-- A set invariant under actual paths meets each closed characteristic cell
in all or nothing. The STOCK weak topology then gives a closed preimage. -/
private theorem isClosed_preimage_of_joined_invariant
    {C : Type v} [TopologicalSpace C] [T2Space C]
    [Topology.CWComplex (Set.univ : Set C)]
    {Y : Type u} [TopologicalSpace Y] (f : C(C, Y)) (S : Set Y)
    (hS : ∀ a b : Y, Joined a b → (a ∈ S ↔ b ∈ S)) :
    IsClosed (f ⁻¹' S) := by
  apply (Topology.CWComplex.closed (Set.univ : Set C) (f ⁻¹' S)
    (Set.subset_univ _)).mpr
  intro n j
  let c : Set C := Topology.CWComplex.closedCell n j
  have hpath : IsPathConnected c :=
    (Metric.isPathConnected_closedBall (x := (0 : Fin n → ℝ)) (r := 1)
      (by norm_num)).image' (Topology.CWComplex.continuousOn n j)
  have hc : IsClosed c := Topology.CWComplex.isClosed_closedCell
  by_cases h : ((f ⁻¹' S) ∩ c).Nonempty
  · obtain ⟨a, haS, hac⟩ := h
    have he : (f ⁻¹' S) ∩ c = c := by
      apply Set.Subset.antisymm Set.inter_subset_right
      intro b hbc
      refine ⟨?_, hbc⟩
      have hab : Joined (f a) (f b) :=
        ((hpath.joinedIn a hac b hbc).joined).map f.continuous
      exact (hS (f a) (f b) hab).mp haS
    exact he.symm ▸ hc
  · have he : (f ⁻¹' S) ∩ c = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    exact he.symm ▸ isClosed_empty

/-- A genuine original CW-type homotopy equivalence supplies the two path
component preimage equalities, using its actual right inverse homotopy. -/
private theorem homotopyEquiv_preimage_pathComponent
    {C : Type v} [TopologicalSpace C] {Y : Type u} [TopologicalSpace Y]
    (e : C ≃ₕ Y) (y : Y) :
    e.symm ⁻¹' (e ⁻¹' pathComponent y) = pathComponent y := by
  ext z
  have hp : Joined (e (e.symm z)) z := ⟨e.right_inv.some.evalAt z⟩
  change Joined y (e (e.symm z)) ↔ Joined y z
  exact ⟨fun h => h.trans hp, fun h => h.trans hp.symm⟩

/-- Connectedness plus the ORIGINAL Hausdorff classical-CW-type qualifier
implies path connectedness of the original target. Its topology is retained;
no Hausdorff assumption on that target or replacement fiber is used. -/
public theorem _root_.Topology.CWComplex.pathConnectedSpace_of_connected_CWType
    {C : Type v} [TopologicalSpace C] [T2Space C]
    [Topology.CWComplex (Set.univ : Set C)]
    {Y : Type u} [TopologicalSpace Y] [ConnectedSpace Y]
    (e : C ≃ₕ Y) : PathConnectedSpace Y := by
  let y : Y := Classical.arbitrary Y
  let S := pathComponent y
  have hS : ∀ a b : Y, Joined a b → (a ∈ S ↔ b ∈ S) := by
    intro a b hab
    change Joined y a ↔ Joined y b
    exact ⟨fun h => h.trans hab, fun h => h.trans hab.symm⟩
  have hSc : ∀ a b : Y, Joined a b → (a ∈ Sᶜ ↔ b ∈ Sᶜ) :=
    fun a b hab => not_congr (hS a b hab)
  have hc : IsClosed (e ⁻¹' S) :=
    isClosed_preimage_of_joined_invariant e.toFun S hS
  have hcc : IsClosed (e ⁻¹' Sᶜ) :=
    isClosed_preimage_of_joined_invariant e.toFun Sᶜ hSc
  have he : e.symm ⁻¹' (e ⁻¹' S) = S :=
    homotopyEquiv_preimage_pathComponent e y
  have hce : e.symm ⁻¹' (e ⁻¹' Sᶜ) = Sᶜ := by
    ext z
    change (¬ e (e.symm z) ∈ S) ↔ (¬ z ∈ S)
    exact not_congr (Set.ext_iff.mp he z)
  have hclosed : IsClosed S := he ▸ hc.preimage e.symm.continuous
  have hclosedc : IsClosed Sᶜ := hce ▸ hcc.preimage e.symm.continuous
  have hopen : IsOpen S := (isClosed_compl_iff (s := S)).mp hclosedc
  have hfull : S = Set.univ := (IsClopen.eq_univ ⟨hclosed, hopen⟩
    (pathComponent.nonempty y))
  exact pathConnectedSpace_iff_eq.mpr ⟨y, hfull⟩


end ActualConnectedCWTypePaths

end Topology.CWComplex

end
