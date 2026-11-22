/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalOmegaFreeFiller
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalNaiveFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# The chosen omega auxiliary replacement

The actual selected unit is a transfinite composition of auxiliary anodyne
maps. Every whole map from an original generator domain factors through a
finite stage; its labelled cell at the next stage supplies an exact filler.
Thus the same selected omega target is naive fibrant.

This is the finite-domain omega specialization of Cisinski's Construction
2.4.36 and Cisinski 2006, Construction 1.2.34.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace SSet.joyalInterval

/-- The actual selected omega unit lies in the original auxiliary left class. -/
theorem auxiliaryOmegaFreeFillerUnit_mem (X : SSet.{u}) :
    auxiliaryAnodyneExtensions (auxiliaryOmegaFreeFillerUnit.app X) := by
  let Φ := SmallObject.SuccStruct.ofNatTrans auxiliaryFreeFillerUnit.{u}
  let E := (evaluation SSet.{u} SSet.{u}).obj X
  have hle : Φ.prop ≤ auxiliaryAnodyneExtensions.inverseImage E := by
    change (MorphismProperty.ofHoms (fun G : SSet.{u} ⥤ SSet.{u} => Φ.toSucc G)) ≤ _
    rw [MorphismProperty.ofHoms_le_iff]
    intro G
    exact auxiliaryFreeFillerUnit_mem (G.obj X)
  let h := (Φ.transfiniteCompositionOfShapeιIteration ℕ).ofLE hle
  let hX := h.map (F := E)
  change auxiliaryGenerators.rlp.llp _
  exact (auxiliaryGenerators.rlp.isStableUnderTransfiniteCompositionOfShape_llp ℕ).le
    _ (hX.mem _)

private lemma indexed_extension (X : SSet.{u}) (i : AuxiliaryGeneratorIndex.{u})
    (a : (auxiliaryGeneratorArrow i).left ⟶ auxiliaryOmegaFreeFiller.obj X) :
    ∃ b : (auxiliaryGeneratorArrow i).right ⟶ auxiliaryOmegaFreeFiller.obj X,
      (auxiliaryGeneratorArrow i).hom ≫ b = a := by
  change (auxiliaryGeneratorArrow i).left ⟶ (colimit auxiliaryOmegaStages.{u}).obj X at a
  change ∃ b : (auxiliaryGeneratorArrow i).right ⟶
    (colimit auxiliaryOmegaStages.{u}).obj X, (auxiliaryGeneratorArrow i).hom ≫ b = a
  let E := (evaluation SSet.{u} SSet.{u}).obj X
  have hc := isColimitOfPreserves E (colimit.isColimit auxiliaryOmegaStages.{u})
  have : SSet.Finite (auxiliaryGeneratorArrow i).left := finite_auxiliaryGeneratorArrow_source i
  let H := coyoneda.obj (op (auxiliaryGeneratorArrow i).left)
  let : PreservesFilteredColimitsOfSize.{0, 0} H :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits H
  obtain ⟨n, aₙ, ha⟩ := Types.jointly_surjective_of_isColimit (isColimitOfPreserves H hc) a
  change aₙ ≫ (colimit.ι auxiliaryOmegaStages.{u} n).app X = a at ha
  let bₙ : (auxiliaryGeneratorArrow i).right ⟶
      auxiliaryFreeFiller.obj ((auxiliaryOmegaStages.{u}.obj n).obj X) :=
    labelledFreeFiller.cell
    (fun k : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow k).hom) i aₙ
  let e : (auxiliaryOmegaStages.{u}.obj (n + 1)).obj X ≅
      auxiliaryFreeFiller.obj ((auxiliaryOmegaStages.{u}.obj n).obj X) :=
    (auxiliaryOmegaStagesSuccIso.{u} n).app X
  refine ⟨bₙ ≫ e.inv ≫ (colimit.ι auxiliaryOmegaStages.{u} (n + 1)).app X, ?_⟩
  have hcell : (auxiliaryGeneratorArrow i).hom ≫ bₙ =
      aₙ ≫ auxiliaryFreeFillerUnit.app ((auxiliaryOmegaStages.{u}.obj n).obj X) :=
    labelledFreeFiller.cell_boundary
      (fun k : AuxiliaryGeneratorIndex.{u} => (auxiliaryGeneratorArrow k).hom) i aₙ
  have hsucc : (auxiliaryOmegaStages.{u}.map (homOfLE (Nat.le_succ n))).app X ≫ e.hom =
      auxiliaryFreeFillerUnit.app ((auxiliaryOmegaStages.{u}.obj n).obj X) :=
    congrArg (fun m => m.app X) (auxiliaryOmegaStages_map_succ.{u} n)
  have hinc : (auxiliaryOmegaStages.{u}.map (homOfLE (Nat.le_succ n))).app X ≫
      (colimit.ι auxiliaryOmegaStages.{u} (n + 1)).app X =
        (colimit.ι auxiliaryOmegaStages.{u} n).app X :=
    congrArg (fun m => m.app X)
      (colimit.w auxiliaryOmegaStages.{u} (homOfLE (Nat.le_succ n)))
  have hη : auxiliaryFreeFillerUnit.app ((auxiliaryOmegaStages.{u}.obj n).obj X) ≫
      e.inv = (auxiliaryOmegaStages.{u}.map (homOfLE (Nat.le_succ n))).app X := by
    rw [← hsucc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, hcell, Category.assoc]
  rw [← Category.assoc
    (auxiliaryFreeFillerUnit.app ((auxiliaryOmegaStages.{u}.obj n).obj X)), hη, hinc, ha]


/-- The selected unit is anodyne and its same selected omega target is naive fibrant. -/
theorem auxiliaryOmegaFreeFiller_isReplacement (X : SSet.{u}) :
    auxiliaryAnodyneExtensions (auxiliaryOmegaFreeFillerUnit.app X) ∧
      auxiliaryNaiveFibrantObjects (auxiliaryOmegaFreeFiller.obj X) := by
  refine ⟨auxiliaryOmegaFreeFillerUnit_mem X, ?_⟩
  change auxiliaryNaiveFibrations (terminal.from (auxiliaryOmegaFreeFiller.obj X))
  rw [auxiliaryNaiveFibrations_eq_generatorRlp, auxiliaryGenerators_eq_ofHoms]
  intro A B j hj
  cases hj with
  | mk i =>
    constructor
    intro a b sq
    obtain ⟨l, hl⟩ := indexed_extension X i a
    exact CommSq.HasLift.mk' { l := l, fac_left := hl, fac_right := terminal.hom_ext _ _ }

end SSet.joyalInterval
