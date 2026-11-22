/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.SmallObject.CellularRetractsClosure
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHCofibrantlyGenerated
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHHornTensorPushout
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHTensorClosedEmbedding
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHWeakHomotopyTransfiniteClosed
import MathlibExt.Topology.Category.PointedCGWH.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# The monoid axiom for the original pointed CGWH model

Actual horn tensor pushouts are weak and closed. The original horn small-object
history is mapped through the actual right tensor functor, including its
original Arrow retract. Derived cellular retract stability then handles the
whole cellular closure of tensors of arbitrary trivial cofibrations.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra Topology
open CategoryTheory.MorphismProperty
open CategoryTheory.SmallObject.CellularRetractsClosure
open CategoryTheory.SmallObject.CellularNormalization
open scoped CGWH.modelCategory CGWH.limits Simplicial

namespace PointedCGWH

private def hornTensorMap (n : ℕ) (i : Fin (n + 2)) (K : PointedCGWH.{u, v}) :
    (Under.costar CGWH.point).obj
      (SSet.toCGWHOfFinite (SSet.horn.{v} (n + 1) i)) ⊗ K ⟶
        (Under.costar CGWH.point).obj
          (SSet.toCGWHOfFinite (Δ[n + 1] : SSet.{v})) ⊗ K :=
  ((Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} n i)) ▷ K

/-- The literal original pointed horn maps smashed with arbitrary pointed factors. -/
def hornTensorGenerators : MorphismProperty PointedCGWH.{u, v} :=
  .ofHoms (fun p : (Σ n : ℕ, Fin (n + 2)) × PointedCGWH.{u, v} =>
    hornTensorMap p.1.1 p.1.2 p.2)

/-- Retracts of actual cellular histories of the original horn tensors. -/
abbrev hornTensorCellularRetracts : MorphismProperty PointedCGWH.{u, v} :=
  (cellularClosure.{v, v} hornTensorGenerators.{u, v}).retracts

private theorem hornTensorGenerators_pushouts_coproducts_le :
    (hornTensorGenerators.{u, v}.coproducts.{v}).pushouts ≤
      (CGWH.weakHomotopyEquivalences ⊓
        TopCat.closedEmbeddings.inverseImage CGWH.cgwhToTop).inverseImage
          pointedToCGWH := by
  intro X Y q hq
  obtain ⟨A, B, m, a, b, hm, sq⟩ := hq
  obtain ⟨L, hm⟩ := (coproducts_iff _ m).1 hm
  obtain ⟨F₁, F₂, c₁, c₂, h₁, h₂, φ, hφ⟩ := hm
  have hIndices (j : L) :
      ∃ p : (Σ n : ℕ, Fin (n + 2)) × PointedCGWH.{u, v},
        CategoryTheory.Arrow.mk (φ.app ⟨j⟩) =
          CategoryTheory.Arrow.mk (hornTensorMap p.1.1 p.1.2 p.2) := by
    exact (ofHoms_iff _ _).1 (hφ ⟨j⟩)
  choose p hp using hIndices
  let n : L → ℕ := fun j => (p j).1.1
  let i : ∀ j, Fin (n j + 2) := fun j => (p j).1.2
  let K : L → PointedCGWH.{u, v} := fun j => (p j).2
  let e (j : L) :
      CategoryTheory.Arrow.mk (hornTensorMap (n j) (i j) (K j)) ≅
        CategoryTheory.Arrow.mk (φ.app ⟨j⟩) :=
    eqToIso (hp j).symm
  let e₁ : Discrete.functor (fun j => (CategoryTheory.Arrow.mk
      (hornTensorMap (n j) (i j) (K j))).left) ≅ F₁ :=
    Discrete.natIso (fun j : Discrete L => CategoryTheory.Arrow.leftFunc.mapIso (e j.as))
  let e₂ : Discrete.functor (fun j => (CategoryTheory.Arrow.mk
      (hornTensorMap (n j) (i j) (K j))).right) ≅ F₂ :=
    Discrete.natIso (fun j : Discrete L => CategoryTheory.Arrow.rightFunc.mapIso (e j.as))
  let cA : Cofan (fun j : L => (Under.costar CGWH.point).obj
      (SSet.toCGWHOfFinite (SSet.horn.{v} (n j + 1) (i j))) ⊗ K j) :=
    (Cocone.precompose e₁.hom).obj c₁
  let cB : Cofan (fun j : L => (Under.costar CGWH.point).obj
      (SSet.toCGWHOfFinite (Δ[n j + 1] : SSet.{v})) ⊗ K j) :=
    (Cocone.precompose e₂.hom).obj c₂
  let hA : IsColimit cA := (IsColimit.precomposeHomEquiv e₁ c₁).symm h₁
  let hB : IsColimit cB := (IsColimit.precomposeHomEquiv e₂ c₂).symm h₂
  have hfac (j : L) :
      cA.inj j ≫ h₁.desc (Cocone.mk c₂.pt (φ ≫ c₂.ι)) =
        hornTensorMap (n j) (i j) (K j) ≫ cB.inj j := by
    have hComm : (e j).hom.left ≫ φ.app ⟨j⟩ =
        hornTensorMap (n j) (i j) (K j) ≫ (e j).hom.right := (e j).hom.w
    change ((e j).hom.left ≫ c₁.ι.app ⟨j⟩) ≫
      h₁.desc (Cocone.mk c₂.pt (φ ≫ c₂.ι)) =
        hornTensorMap (n j) (i j) (K j) ≫ ((e j).hom.right ≫ c₂.ι.app ⟨j⟩)
    rw [Category.assoc, h₁.fac]
    change (e j).hom.left ≫ (φ.app ⟨j⟩ ≫ c₂.ι.app ⟨j⟩) =
      hornTensorMap (n j) (i j) (K j) ≫ ((e j).hom.right ≫ c₂.ι.app ⟨j⟩)
    rw [← Category.assoc, hComm, Category.assoc]
  have hfacRaw (j : L) :
      cA.inj j ≫ h₁.desc (Cocone.mk c₂.pt (φ ≫ c₂.ι)) =
        (((Under.costar CGWH.point).map
          (CGWH.realizedHornInclusion.{v, u} (n j) (i j))) ⊗ₘ 𝟙 (K j)) ≫ cB.inj j := by
    simpa only [hornTensorMap, tensorHom_id] using hfac j
  constructor
  · exact freePointHornTensorCofan_cobaseChange_mem_weakHomotopyEquivalences
      L n i K cA cB hA hB _ hfacRaw sq.flip
  · exact freePointHornTensorCofan_cobaseChange_isClosedEmbedding
      L n i K cA cB hA hB _ hfacRaw sq.flip

private theorem hornTensorCellular_le_weakEquivalences :
    cellularClosure.{v, v} hornTensorGenerators.{u, v} ≤
      weakEquivalences PointedCGWH.{u, v} := by
  intro X Y f hf
  obtain ⟨J, _, _, _, _, hc⟩ := (transfiniteCompositions_iff _ f).1 hf
  let c := Classical.choice hc
  let U := pointedToCGWH.{u, v}
  let _ : IsConnected J := IsFiltered.isConnected J
  let _ : PreservesWellOrderContinuousOfShape J U :=
    { preservesColimitsOfShape j hj := by
        let _ : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
        let _ : IsConnected (Set.Iio j) := IsFiltered.isConnected (Set.Iio j)
        infer_instance }
  let d := c.ofLE hornTensorGenerators_pushouts_coproducts_le
  change CGWH.weakHomotopyEquivalences f.right
  exact CGWH.weakHomotopyEquivalences.of_transfiniteComposition_closed.{u, v, v} d.map

private theorem hornTensorCellularRetracts_le_weakEquivalences :
    hornTensorCellularRetracts.{u, v} ≤ weakEquivalences PointedCGWH.{u, v} :=
  (retracts_monotone hornTensorCellular_le_weakEquivalences).trans
    (weakEquivalences PointedCGWH.{u, v}).retracts_le

private theorem horn_whiskerRight_mem_cellularRetracts
    {A B : PointedCGWH.{u, v}} (f : A ⟶ B)
    (hf : cofibrantGenerationData.{u, v}.J f) (K : PointedCGWH.{u, v}) :
    hornTensorCellularRetracts.{u, v} (f ▷ K) := by
  change (CGWH.realizedHornInclusions.{u, v}.strictMap
    (Under.costar CGWH.point.{u, v})) f at hf
  cases hf with
  | @map A B g hg =>
    unfold CGWH.realizedHornInclusions at hg
    rw [MorphismProperty.iSup_iff] at hg
    obtain ⟨n, ⟨i⟩⟩ := hg
    have hGen : hornTensorGenerators.{u, v} (hornTensorMap.{u, v} n i K) := by
      exact MorphismProperty.ofHoms.mk (C := PointedCGWH.{u, v})
        (f := fun p : (Σ n : ℕ, Fin (n + 2)) × PointedCGWH.{u, v} =>
          hornTensorMap.{u, v} p.1.1 p.1.2 p.2) (⟨⟨n, i⟩, K⟩)
    exact le_cellularRetracts.{v, v} hornTensorGenerators.{u, v}
      (hornTensorMap n i K) hGen

/-- Right tensor carries each original selected trivial cofibration and its
original horn small-object Arrow retract into actual cellular horn tensors. -/
theorem trivialCofibration_whiskerRight_mem_hornTensorCellularRetracts
    {A B : PointedCGWH.{u, v}} (f : A ⟶ B)
    (hf : trivialCofibrations PointedCGWH.{u, v} f) (K : PointedCGWH.{u, v}) :
    hornTensorCellularRetracts.{u, v} (f ▷ K) := by
  let P := cofibrantGenerationData.{u, v}.J
  let R := hornTensorCellularRetracts.{u, v}
  let F : PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} := tensorRight K
  let _ : R.IsStableUnderCobaseChange :=
    cellularRetractsIsStableUnderCobaseChange.{v, v} hornTensorGenerators.{u, v}
  let _ : R.IsStableUnderCoproducts.{v} :=
    cellularRetractsIsStableUnderCoproducts.{v, v} hornTensorGenerators.{u, v}
  let _ : IsStableUnderTransfiniteComposition.{v} R :=
    cellularRetractsIsStableUnderTransfiniteComposition.{v, v} hornTensorGenerators.{u, v}
  have hGenerators : P ≤ R.inverseImage F := by
    intro X Y g hg
    exact horn_whiskerRight_mem_cellularRetracts g hg K
  have hCoproducts : P.coproducts.{v} ≤ R.inverseImage F := by
    intro X Y m hm
    obtain ⟨L, hm⟩ := (coproducts_iff _ m).1 hm
    obtain ⟨F₁, F₂, c₁, c₂, h₁, h₂, φ, hφ⟩ := hm
    let m' : F.obj c₁.pt ⟶ F.obj c₂.pt :=
      F.map (X := c₁.pt) (Y := c₂.pt) (h₁.desc (Cocone.mk c₂.pt (φ ≫ c₂.ι)))
    have hF₁ : IsColimit (F.mapCocone c₁) := isColimitOfPreserves F h₁
    have hF₂ : IsColimit (F.mapCocone c₂) := isColimitOfPreserves F h₂
    let τ : F₁ ⋙ F ⟶ F₂ ⋙ F := Functor.whiskerRight φ F
    have hComponents : R.functorCategory (Discrete L) τ := by
      intro j
      change R (F.map (φ.app j))
      exact hGenerators (φ.app j) (hφ j)
    change R m'
    exact MorphismProperty.IsStableUnderColimitsOfShape.condition
        (C := PointedCGWH.{u, v}) (W := R) (J := Discrete L) (F₁ ⋙ F) (F₂ ⋙ F)
        (F.mapCocone c₁) (F.mapCocone c₂)
        hF₁ hF₂ τ hComponents
        m' (by
          intro j
          change F.map (c₁.ι.app j) ≫ F.map (h₁.desc (Cocone.mk c₂.pt (φ ≫ c₂.ι))) =
            F.map (φ.app j) ≫ F.map (c₂.ι.app j)
          rw [← F.map_comp, ← F.map_comp, h₁.fac]
          rfl)
  have hSteps : (P.coproducts.{v}).pushouts ≤ R.inverseImage F := by
    intro X Y m hm
    obtain ⟨S, T, p, a, b, hp, sq⟩ := hm
    exact MorphismProperty.of_isPushout (P := R) (sq.map F) (hCoproducts _ hp)
  let _ := cofibrantGenerationData.{u, v}.J_smallObject
  have hLeft : P.rlp.llp f := by
    change cofibrantGenerationData.{u, v}.J.rlp.llp f
    rw [cofibrantGenerationData.J_rlp, fibrations_llp]
    exact hf
  rw [SmallObject.llp_rlp_of_isCardinalForSmallObjectArgument'
    P realizedGeneratorCardinal.{v}] at hLeft
  obtain ⟨X, Y, g, ret, hg⟩ := hLeft
  let c := Classical.choice hg
  let _ : PreservesWellOrderContinuousOfShape realizedGeneratorCardinal.{v}.ord.ToType F :=
    { preservesColimitsOfShape _ _ := inferInstance }
  let mapped := (c.ofLE hSteps).map
  have hMapped : R (F.map g) :=
    R.transfiniteCompositionsOfShape_le realizedGeneratorCardinal.{v}.ord.ToType _ mapped.mem
  exact MorphismProperty.of_retract (P := R) (ret.map F) hMapped

/-- The actual pointed CGWH model and native smash satisfy the monoid axiom
at the original carrier/chain universe, with the compact probe universe independent. -/
theorem monoid_axiom : MonoidAxiom.{v} PointedCGWH.{u, v} := by
  let R := hornTensorCellularRetracts.{u, v}
  let _ : R.IsStableUnderCobaseChange :=
    cellularRetractsIsStableUnderCobaseChange.{v, v} hornTensorGenerators.{u, v}
  let _ : R.IsStableUnderCoproducts.{v} :=
    cellularRetractsIsStableUnderCoproducts.{v, v} hornTensorGenerators.{u, v}
  let _ : IsStableUnderTransfiniteComposition.{v} R :=
    cellularRetractsIsStableUnderTransfiniteComposition.{v, v} hornTensorGenerators.{u, v}
  have hTensor : tensorTrivialCofibrationsRight PointedCGWH.{u, v} ≤ R :=
    (tensorTrivialCofibrationsRight_le_iff _ R).2
      (fun f hf K => trivialCofibration_whiskerRight_mem_hornTensorCellularRetracts f hf K)
  have hCoproducts : (tensorTrivialCofibrationsRight PointedCGWH.{u, v}).coproducts.{v} ≤ R :=
    (coproducts_monotone hTensor).trans R.coproducts_le
  have hPushouts :
      ((tensorTrivialCofibrationsRight PointedCGWH.{u, v}).coproducts.{v}).pushouts ≤ R :=
    (pushouts_monotone hCoproducts).trans R.pushouts_le
  exact ⟨((transfiniteCompositions_monotone hPushouts).trans
    (transfiniteCompositions_le R)).trans hornTensorCellularRetracts_le_weakEquivalences⟩

end PointedCGWH

namespace CGWH.modelCategory

/-- The selected native pointed model carries its proved monoid axiom. -/
scoped instance pointedCGWHMonoidAxiom : MonoidAxiom.{v} PointedCGWH.{u, v} :=
  PointedCGWH.monoid_axiom

end CGWH.modelCategory

namespace PointedCGWH

universe w

/-- The entire cellular and retract closure of arbitrary right tensor
trivial cofibrations consists of actual Arrow retracts of horn-cellular maps.
The original carrier and small-object cardinal remain v; the original outer
shape and coproduct universe may be any w no larger than v. -/
theorem tensorTrivialCofibrationsRight_cellularReduction [UnivLE.{w, v}] :
    (cellularClosure.{w, w} (tensorTrivialCofibrationsRight PointedCGWH.{u, v})).retracts ≤
      hornTensorCellularRetracts.{u, v} := by
  let R := hornTensorCellularRetracts.{u, v}
  let S := tensorTrivialCofibrationsRight PointedCGWH.{u, v}
  let _ : R.IsStableUnderCobaseChange :=
    cellularRetractsIsStableUnderCobaseChange.{v, v} hornTensorGenerators.{u, v}
  let _ : R.IsStableUnderCoproducts.{v} :=
    cellularRetractsIsStableUnderCoproducts.{v, v} hornTensorGenerators.{u, v}
  let _ : IsStableUnderTransfiniteComposition.{v} R :=
    cellularRetractsIsStableUnderTransfiniteComposition.{v, v} hornTensorGenerators.{u, v}
  let _ : IsStableUnderTransfiniteComposition.{w} R :=
    IsStableUnderTransfiniteComposition.shrink.{w, v} R
  have hTensor : S ≤ R :=
    (tensorTrivialCofibrationsRight_le_iff _ R).2
      (fun f hf M => trivialCofibration_whiskerRight_mem_hornTensorCellularRetracts f hf M)
  have hCoproductsV : S.coproducts.{v} ≤ R :=
    (coproducts_monotone hTensor).trans R.coproducts_le
  have hCoproductsW : S.coproducts.{w} ≤ R := by
    intro A B f hf
    obtain ⟨L, hL⟩ := (coproducts_iff _ f).1 hf
    exact hCoproductsV f (coproducts_of_small.{v, w} S f hL)
  have hPushouts : (S.coproducts.{w}).pushouts ≤ R :=
    (pushouts_monotone hCoproductsW).trans R.pushouts_le
  have hCellular : cellularClosure.{w, w} S ≤ R :=
    (transfiniteCompositions_monotone.{w} hPushouts).trans
      (transfiniteCompositions_le.{w} R)
  exact (retracts_monotone hCellular).trans R.retracts_le

/-- The actual generated class contains its original right tensor generators,
is closed under coproducts, cobase change, transfinite composition and Arrow
retracts, and consists of native weak homotopy equivalences. -/
theorem monoid_axiom_weaklySaturatedClosure [UnivLE.{w, v}] :
    let S := tensorTrivialCofibrationsRight PointedCGWH.{u, v}
    let R := (cellularClosure.{w, w} S).retracts
    S ≤ R ∧ R.IsStableUnderCoproducts.{w} ∧ R.IsStableUnderCobaseChange ∧
      IsStableUnderTransfiniteComposition.{w} R ∧ R.IsStableUnderRetracts ∧
        R ≤ weakEquivalences PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{w, w} PointedCGWH.{u, v} :=
    hasColimitsOfSizeOfUnivLE.{v, v} PointedCGWH.{u, v}
  let S := tensorTrivialCofibrationsRight PointedCGWH.{u, v}
  let R := (cellularClosure.{w, w} S).retracts
  have hWeak : R ≤ weakEquivalences PointedCGWH.{u, v} :=
    tensorTrivialCofibrationsRight_cellularReduction.{u, v, w}.trans
      hornTensorCellularRetracts_le_weakEquivalences
  exact ⟨le_cellularRetracts.{w, w} S,
    cellularRetractsIsStableUnderCoproducts.{w, w} S,
    cellularRetractsIsStableUnderCobaseChange.{w, w} S,
    cellularRetractsIsStableUnderTransfiniteComposition.{w, w} S,
    inferInstance, hWeak⟩

end PointedCGWH
