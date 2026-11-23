/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.ClassicalExistence
public import MathlibExt.CategoryTheory.Groupoid.FullOfMapEnd
public import MathlibExt.CategoryTheory.Groupoid.BasedFunctor
public import MathlibExt.AlgebraicTopology.PlusConstruction.FundamentalGroup
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PathTransportNaturality
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PiOneMapComposition
public import MathlibExt.Topology.Category.TopCat.TrivialCofibrationExtension
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CellFamilyModel

/-!
# Original geometric and subgroup inputs for plus-map extension

The actual two/three-cell inclusion is a cofibration, derived from its
original cell squares. A subgroup-preserving source map followed by the
independently constructed target plus map kills the prescribed subgroup
at the actual image point. These are inputs to the forthcoming derived
pushout argument, not a claim of coefficient cobase change or extension.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomotopicalAlgebra
open scoped TopCat.modelCategory ContinuousMap

universe u

namespace AlgebraicTopology.LoopCellIndependentPlus

/-- The same original two/three-cell composite is a genuine model
cofibration; no cofibration or replacement model is supplied. -/
public theorem originalInclusion_cofibration
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    Cofibration (LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P) := by
  let : PathConnectedSpace X :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType
      (ContinuousMap.HomotopyEquiv.refl X)
  let b₂ := CellFamilyAttachment.boundaryToDisks P 1
  let b₃ := CellFamilyAttachment.boundaryToDisks P 2
  let i₂ := LoopCellAttachment.inclusion X x P
  let i₃ := LoopCellRegularThreeComparison.originalThreeInclusion X x P
  let : Cofibration b₂ := CellFamilySimplicialModel.classicalBoundary_cofibration 1 P
  let : Cofibration b₃ := CellFamilySimplicialModel.classicalBoundary_cofibration 2 P
  let : Cofibration i₂ := by
    apply (cofibration_iff _).mpr
    exact (cofibrations TopCat.{u}).of_isPushout
      (CellFamilyAttachment.isPushout X 1 (LoopCellAttachment.attachingMap X x P)).flip
      ((cofibration_iff b₂).mp inferInstance)
  let : Cofibration i₃ := by
    apply (cofibration_iff _).mpr
    exact (cofibrations TopCat.{u}).of_isPushout
      (CellFamilyAttachment.isPushout (LoopCellAttachment.space X x P) 2
        (LoopCellSphericalGenerators.sphericalGenerator X x P)).flip
      ((cofibration_iff b₃).mp inferInstance)
  change Cofibration (i₂ ≫ i₃)
  infer_instance

/-- Subgroup preservation followed by the actual independent target
plus map annihilates P, using its exact induced-map kernel and the public
ordinary fundamental-group composition law. -/
public theorem subgroupPreserving_composite_kills
    (X Y : TopCat.{u}) [T2Space Y] [Topology.CWComplex (Set.univ : Set Y)]
    [ConnectedSpace Y] (x : X) (y : Y) (f : X ⟶ Y) (hxy : f x = y)
    (P : Subgroup (FundamentalGroup X x)) (Q : Subgroup (FundamentalGroup Y y))
    [Q.Normal] [Group.IsPerfect Q]
    (hPQ : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom hxy p ∈ Q) :
    letI : PathConnectedSpace Y :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl Y)
    let i := LoopCellAttachment.inclusion Y y Q ≫
      LoopCellRegularThreeComparison.originalThreeInclusion Y y Q
    P ≤ MonoidHom.ker (FundamentalGroup.mapOfEq (f ≫ i).hom (congrArg i hxy)) := by
  let : PathConnectedSpace Y :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType
      (ContinuousMap.HomotopyEquiv.refl Y)
  let i := LoopCellAttachment.inclusion Y y Q ≫
    LoopCellRegularThreeComparison.originalThreeInclusion Y y Q
  let m₁ := FundamentalGroup.mapOfEq f.hom hxy
  let m₂ := FundamentalGroup.mapOfEq i.hom (rfl : i.hom y = i y)
  have hker : MonoidHom.ker m₂ = Q :=
    (original_connected_CW_plus_construction_full Y y Q).2.2.2.1
  have hcomp : FundamentalGroup.mapOfEq (f ≫ i).hom (congrArg i hxy) = m₂.comp m₁ := by
    exact FundamentalGroup.mapOfEq_comp f.hom i.hom hxy rfl (congrArg i hxy)
  change P ≤ MonoidHom.ker (FundamentalGroup.mapOfEq (f ≫ i).hom (congrArg i hxy))
  intro p hp
  have hmp : m₁ p ∈ MonoidHom.ker m₂ := by
    rw [hker]
    exact hPQ p hp
  change FundamentalGroup.mapOfEq (f ≫ i).hom (congrArg i hxy) p = 1
  rw [hcomp, MonoidHom.comp_apply]
  exact MonoidHom.mem_ker.mp hmp

/-- The actual original plus inclusion is full and essentially
surjective on its ordinary fundamental groupoid. The source connectors
and target paths are constructed from the two derived path-connected
spaces, and the based surjection is the accepted literal public output. -/
public theorem originalInclusion_groupoid_full_essSurj
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    (FundamentalGroupoid.map i.hom).Full ∧
      (FundamentalGroupoid.map i.hom).EssSurj := by
  let : PathConnectedSpace X :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType
      (ContinuousMap.HomotopyEquiv.refl X)
  let Z := LoopCellRegularThreeComparison.originalThree X x P
  let i := LoopCellAttachment.inclusion X x P ≫
    LoopCellRegularThreeComparison.originalThreeInclusion X x P
  let F := FundamentalGroupoid.map i.hom
  rcases original_connected_CW_plus_construction_full X x P with
    ⟨_, _, _, _, hs, hpc, _, _, _⟩
  let : PathConnectedSpace Z := hpc
  have hsEnd : Function.Surjective (F.mapEnd (FundamentalGroupoid.mk x)) := by
    change Function.Surjective (FundamentalGroup.map i.hom x)
    simpa only [FundamentalGroup.mapOfEq_rfl] using hs
  refine ⟨Functor.full_of_surjective_mapEnd F (FundamentalGroupoid.mk x)
    (fun c => Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x c.as)) hsEnd, ?_⟩
  constructor
  intro c
  exact ⟨FundamentalGroupoid.mk x,
    ⟨(Groupoid.isoEquivHom _ _).symm
      (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (i x) c.as))⟩⟩

/-- For EVERY actual point h of an arbitrary target H, the given map
killing P produces the quotient-valued functor needed by the van Kampen
construction. BasedFunctor handles components outside h internally.
No functor, quotient comparison, target path or map factorization is input. -/
public theorem originalInclusion_basedFunctor_end_desc
    (X : TopCat.{u}) [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [ConnectedSpace X] (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] (H : TopCat.{u}) (f : X ⟶ H)
    (hkill : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom rfl p = 1) (h : H) :
    letI : PathConnectedSpace X :=
      Topology.CWComplex.pathConnectedSpace_of_connected_CWType
        (ContinuousMap.HomotopyEquiv.refl X)
    let Z := LoopCellRegularThreeComparison.originalThree X x P
    let i := LoopCellAttachment.inclusion X x P ≫
      LoopCellRegularThreeComparison.originalThreeInclusion X x P
    let B := Groupoid.basedFunctor (FundamentalGroupoid.mk h)
      (MonoidHom.id (FundamentalGroup H h))
    ∃ F : FundamentalGroupoid Z ⥤ SingleObj (FundamentalGroup H h),
      ∀ q : FundamentalGroup X x,
        ((FundamentalGroupoid.map i.hom ⋙ F).map q.asHom : FundamentalGroup H h) =
          ((FundamentalGroupoid.map f.hom ⋙ B).map q.asHom : FundamentalGroup H h) := by
  let : PathConnectedSpace X :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType
      (ContinuousMap.HomotopyEquiv.refl X)
  let Z := LoopCellRegularThreeComparison.originalThree X x P
  let i := LoopCellAttachment.inclusion X x P ≫
    LoopCellRegularThreeComparison.originalThreeInclusion X x P
  let y := LoopCellRegularThreeComparison.originalThreeBasePoint X x P
  let G := FundamentalGroup H h
  let B := Groupoid.basedFunctor (FundamentalGroupoid.mk h) (MonoidHom.id G)
  let F₀ := FundamentalGroupoid.map f.hom ⋙ B
  let φ₀ : FundamentalGroup X x →* G :=
    (SingleObj.toEnd G).symm.toMonoidHom.comp (F₀.mapEnd (FundamentalGroupoid.mk x))
  have hφ : P ≤ MonoidHom.ker φ₀ := by
    intro p hp
    change (SingleObj.toEnd G).symm (F₀.mapEnd (FundamentalGroupoid.mk x) p) = 1
    have hp' := hkill p hp
    rw [FundamentalGroup.mapOfEq_rfl] at hp'
    have he : (FundamentalGroupoid.map f.hom).map p.asHom = 𝟙 _ :=
      congrArg (fun q : FundamentalGroup H (f x) => q.asHom) hp'
    have hEnd : F₀.mapEnd (FundamentalGroupoid.mk x) p = 1 := by
      change End.of (B.map ((FundamentalGroupoid.map f.hom).map p.asHom)) = 1
      rw [he, B.map_id]
      rfl
    exact (congrArg (SingleObj.toEnd G).symm hEnd).trans
      (map_one (SingleObj.toEnd G).symm)
  rcases original_connected_CW_plus_construction_full X x P with
    ⟨hp, _, _, _, hs, _, _, _, _⟩
  let eπ := hp.fundamentalGroupQuotientMulEquiv hs
  let ψ : FundamentalGroup X x ⧸ P →* G := QuotientGroup.lift P φ₀ hφ
  let φ : FundamentalGroup Z y →* G := ψ.comp eπ.symm.toMonoidHom
  let F := Groupoid.basedFunctor (FundamentalGroupoid.mk y) φ
  refine ⟨F, ?_⟩
  intro q
  have hm : ((FundamentalGroupoid.map i.hom ⋙ F).map q.asHom : G) =
      φ (FundamentalGroup.mapOfEq i.hom rfl q) := by
    rw [FundamentalGroup.mapOfEq_rfl]
    exact Groupoid.basedFunctor_map_end (FundamentalGroupoid.mk y) φ
      (FundamentalGroup.map i.hom x q)
  rw [hm]
  change ψ (eπ.symm (FundamentalGroup.mapOfEq i.hom rfl q)) = (F₀.map q.asHom : G)
  rw [hp.fundamentalGroupQuotientMulEquiv_symm_map hs q]
  exact QuotientGroup.lift_mk' P hφ q

end AlgebraicTopology.LoopCellIndependentPlus

end
