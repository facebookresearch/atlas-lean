/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidCoverParentEdges

/-!
# Full original parent-edge orientation and coefficient data

An actual parent edge is one of the two original arrow orientations,
with its entire original generating coefficient and native path
triangle. The native last signed label proves uniqueness of this
actual edge, including orientation. No tree outcome is assumed.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)

/-- A SAME full original nonroot parent edge, retaining its actual orientation. -/
abbrev ParentEdge (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) :=
  CoverArrow V z (coverParent V z a ha) a ⊕ CoverArrow V z a (coverParent V z a ha)

/-- Both opposite original parent-generator orientations cannot occur at one native full word. -/
lemma parentEdge_opposite_false (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a)
    (f : CoverArrow V z (coverParent V z a ha) a)
    (g : CoverArrow V z a (coverParent V z a ha)) : False := by
  have he := (coverArrow_up_last V z f (coverParent_rank V z a ha)).symm.trans
    (coverArrow_down_last V z g (coverParent_rank V z a ha))
  have hb : true = false := congrArg Prod.snd (Option.some.inj he)
  cases hb

/-- The SAME original full parent-edge type is nonempty from actual native word reconstruction. -/
lemma parentEdge_nonempty (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) :
    Nonempty (ParentEdge V z a ha) := by
  rcases coverParent_arrow V z a ha with ⟨⟨f⟩⟩ | ⟨⟨g⟩⟩
  · exact ⟨.inl f⟩
  · exact ⟨.inr g⟩

/-- The actual original edge is unique in BOTH its full coefficient and orientation. -/
theorem parentEdge_subsingleton (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) :
    Subsingleton (ParentEdge V z a ha) := by
  let _ := CoverArrow.subsingleton V z (coverParent V z a ha) a
  let _ := CoverArrow.subsingleton V z a (coverParent V z a ha)
  refine ⟨fun f g => ?_⟩
  cases f with
  | inl f =>
    cases g with
    | inl g => exact congrArg Sum.inl (Subsingleton.elim f g)
    | inr g => exact False.elim (parentEdge_opposite_false V z a ha f g)
  | inr f =>
    cases g with
    | inl g => exact False.elim (parentEdge_opposite_false V z a ha g f)
    | inr g => exact congrArg Sum.inr (Subsingleton.elim f g)

/-- The actual native reconstructed original parent edge. -/
def parentEdge (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) : ParentEdge V z a ha :=
  Classical.choice (parentEdge_nonempty V z a ha)

/-- The SAME individual original source of the actual parent-generating edge. -/
def parentEdgeSource (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) : CoverVertex V z :=
  match parentEdge V z a ha with
  | .inl _ => coverParent V z a ha
  | .inr _ => a

/-- The SAME individual original target of the actual parent-generating edge. -/
def parentEdgeTarget (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) : CoverVertex V z :=
  match parentEdge V z a ha with
  | .inl _ => a
  | .inr _ => coverParent V z a ha

/-- The actual original generator with its full native path triangle. -/
def parentEdgeArrow (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) :
    CoverArrow V z (parentEdgeSource V z a ha) (parentEdgeTarget V z a ha) := by
  unfold parentEdgeSource parentEdgeTarget
  cases parentEdge V z a ha with
  | inl f => exact f
  | inr g => exact g

/-- The original simplex endpoint occupied by the SAME native parent vertex. -/
def parentEdgeEndpoint (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) : Fin 2 :=
  match parentEdge V z a ha with
  | .inl _ => 0
  | .inr _ => 1

/-- Every source of an actual parent edge retains its original rank bound. -/
lemma parentEdgeSource_rank (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) :
    CoverVertex.rank V z (parentEdgeSource V z a ha) ≤ CoverVertex.rank V z a := by
  unfold parentEdgeSource
  cases parentEdge V z a ha with
  | inl _ =>
    change CoverVertex.rank V z (coverParent V z a ha) ≤ CoverVertex.rank V z a
    have h := coverParent_rank V z a ha
    omega
  | inr _ => exact le_rfl

/-- Every target of an actual parent edge retains its original rank bound. -/
lemma parentEdgeTarget_rank (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) :
    CoverVertex.rank V z (parentEdgeTarget V z a ha) ≤ CoverVertex.rank V z a := by
  unfold parentEdgeTarget
  cases parentEdge V z a ha with
  | inl _ => exact le_rfl
  | inr _ =>
    change CoverVertex.rank V z (coverParent V z a ha) ≤ CoverVertex.rank V z a
    have h := coverParent_rank V z a ha
    omega

/-- The SAME actual parent endpoint reads the original parent vertex. -/
lemma parentEdgeEndpoint_vertex (a : CoverVertex V z) (ha : 0 < CoverVertex.rank V z a) :
    (if parentEdgeEndpoint V z a ha = 0 then parentEdgeSource V z a ha
      else parentEdgeTarget V z a ha) = coverParent V z a ha := by
  unfold parentEdgeEndpoint parentEdgeSource parentEdgeTarget
  cases parentEdge V z a ha <;> rfl

end Quiver.FreeGroupoid.OriginalWords
