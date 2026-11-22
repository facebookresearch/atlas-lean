/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidCoverParentCellPreimage
import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexOuterFacesWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.IndexedSums
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceCoproducts

/-!
# The SAME entire original parent-cell preimage inclusion is weak

All individual original high vertices index their actual parent cells.
The full original old-stage preimage is isomorphic to the literal sum
of their SAME original parent endpoint faces. Every index, coefficient
and both inverse operations are retained. Native endpoint weakness
and genuine coproduct stability prove the original inclusion weak.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver in all indexed parent cells. -/
private local instance coverQuiverForAllCells : Quiver.{v} (CoverVertex V z) := coverQuiver V z

/-- Every original high vertex supplies the SAME full native one-arrow simplex. -/
def coverCellSimplex (k : ℕ) (_a : CoverCellLabel V z k) : SSet.{max u v} := Δ[1]

/-- The entire native indexed sum of all actual original parent cells. -/
abbrev coverAllCells (k : ℕ) : SSet.{max u v} := SSet.IndexedSums.object (coverCellSimplex V z k)

/-- The entire original native cell map retains all original high vertices and full generator cells. -/
def coverAllCellMap (k : ℕ) : coverAllCells V z k ⟶ nerve (Paths (CoverVertex V z)) :=
  SSet.IndexedSums.desc (coverCellSimplex V z k) (coverParentCell V z k)

/-- Each original labelled endpoint is the SAME actual parent endpoint face. -/
def coverLabelEndpoint (k : ℕ) (a : CoverCellLabel V z k) : (coverCellSimplex V z k a).Subcomplex :=
  SSet.stdSimplex.face {parentEdgeEndpoint V z a.val (coverCellLabel_pos V z k a)}

/-- The SAME actual original endpoint inclusion is genuinely realization weak. -/
lemma coverLabelEndpoint_weak (k : ℕ) (a : CoverCellLabel V z k) :
    SSet.realizationWeakEquivalences (coverLabelEndpoint V z k a).ι :=
  SSet.stdSimplex.face_inclusion_weak _ (Finset.singleton_nonempty _)

/-- The entire native sum of all SAME original endpoint-face coefficients. -/
abbrev coverEndpointCells (k : ℕ) : SSet.{max u v} :=
  SSet.IndexedSums.object (fun a : CoverCellLabel V z k => (coverLabelEndpoint V z k a : SSet.{max u v}))

/-- The whole original indexed endpoint coefficient maps to the SAME actual old-stage preimage. -/
def coverEndpointsToPreimage (k : ℕ) : coverEndpointCells V z k ⟶
    ((coverRankStage V z k).preimage (coverAllCellMap V z k) : SSet.{max u v}) where
  app q := ↾fun a => ⟨⟨a.1, a.2.val⟩, by
    have he := congrArg (fun K => K.obj q) (coverParentCell_preimage_old V z k a.1)
    change (coverParentCell V z k a.1).app q a.2.val ∈ (coverRankStage V z k).obj q
    exact (congrArg (fun S => a.2.val ∈ S) he).mpr a.2.property⟩
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro a
    rfl

/-- The full original preimage operation keeps its SAME high-vertex index and whole native simplex coefficient. -/
lemma coverEndpointsToPreimage_ι (k : ℕ) :
    coverEndpointsToPreimage V z k ≫ ((coverRankStage V z k).preimage (coverAllCellMap V z k)).ι =
      SSet.IndexedSums.map (fun a : CoverCellLabel V z k => (coverLabelEndpoint V z k a : SSet.{max u v}))
        (fun a => (coverLabelEndpoint V z k a).ι) := rfl

/-- Both original coefficient operations recover all original labelled native endpoint-preimage simplices. -/
instance coverEndpointsToPreimage_isIso (k : ℕ) : IsIso (coverEndpointsToPreimage V z k) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  rw [isIso_iff_bijective]
  constructor
  · intro a b h
    have he := congrArg Subtype.val h
    have hl := Sigma.mk.inj_iff.mp he
    cases a with
    | mk a c =>
      cases b with
      | mk b d =>
        dsimp at hl
        obtain ⟨rfl, hc⟩ := hl
        have hcd : c = d := Subtype.ext (eq_of_heq hc)
        subst d
        rfl
  · rintro ⟨⟨a, c⟩, hc⟩
    have he := congrArg (fun K => K.obj q) (coverParentCell_preimage_old V z k a)
    have hm : c ∈ (coverLabelEndpoint V z k a).obj q :=
      (congrArg (fun S => c ∈ S) he).mp hc
    exact ⟨⟨a, ⟨c, hm⟩⟩, rfl⟩

/-- The SAME whole original native all-cell old-stage preimage inclusion is genuinely weak. -/
theorem coverAllCell_preimage_weak (k : ℕ) :
    SSet.realizationWeakEquivalences ((coverRankStage V z k).preimage (coverAllCellMap V z k)).ι := by
  apply SSet.realizationWeakEquivalences.of_precomp (coverEndpointsToPreimage V z k) _
    (SSet.realizationWeakEquivalences.of_isIso _)
  rw [coverEndpointsToPreimage_ι]
  exact SSet.IndexedSums.map_property _ SSet.realizationWeakEquivalences _ (coverLabelEndpoint_weak V z k)

/-- All original high-vertex cells land in the SAME actual native next rank stage. -/
lemma coverAllCellMap_range_le_next (k : ℕ) :
    SSet.Subcomplex.range (coverAllCellMap V z k) ≤ coverRankStage V z (k + 1) := by
  intro q w hw
  obtain ⟨⟨a, c⟩, rfl⟩ := hw
  exact coverParentCell_range_le_next V z k a q ⟨c, rfl⟩

end Quiver.FreeGroupoid.OriginalWords
