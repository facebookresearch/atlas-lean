/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.WalkingIsomorphismStageKernel
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The original alternating-stage successor pushout

Rezk §11.7, equation (11.8), is the original horn/alternating-stage square.
Its pullback, pushout, chosen comparison and unique descent are constructed
with the native Type criterion and categorical APIs. The same square is
transported through the actual inner-discrete embedding in both degrees.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.coherentIso

private theorem oldStage_app_mono (k : ℕ) (d : SimplexCategoryᵒᵖ) :
    Mono ((stageDiagram.{u}.map (homOfLE (Nat.sub_le k 1))).app d) := by
  apply (mono_iff_injective _).mpr
  intro a b h
  apply Subtype.ext
  have hv : ((stageDiagram.{u}.map (homOfLE (Nat.sub_le k 1))).app d a).val =
      ((stageDiagram.{u}.map (homOfLE (Nat.sub_le k 1))).app d b).val :=
    congrArg (fun x : (stage k).obj d => x.val) h
  exact hv

private theorem stageSimplexMap_app_surjective (k : ℕ) (d : SimplexCategoryᵒᵖ) :
    Function.Surjective ((stageSimplexMap.{u} k).app d) := by
  let : Epi (stageSimplexMap.{u} k) := by
    change Epi (Subcomplex.toOfSimplex (alternatingSimplex.{u} k))
    infer_instance
  exact (epi_iff_surjective _).mp (inferInstance : Epi ((stageSimplexMap.{u} k).app d))

/-- The original horn is the literal pullback of the original old-stage inclusion. -/
theorem stageSuccessor_isPullback (k : ℕ) (hk : 2 ≤ k) :
    IsPullback (horn.{u} k 0).ι (hornAttachment k hk) (stageSimplexMap k)
      (stageDiagram.map (homOfLE (Nat.sub_le k 1))) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (fun f : (horn.{u} k 0 : SSet.{u}) ⟶ (stage k : SSet.{u}) => f.app d)
      (hornAttachment_stageSimplexMap.{u} k hk)
  · intro a b h
    exact Subtype.ext h.1
  · intro a b h
    have hraw : (alternatingMap.{u} k).app d a = b.val := congrArg Subtype.val h
    have hold : (alternatingMap.{u} k).app d a ∈ (stage (k - 1)).obj d :=
      hraw.symm ▸ b.property
    have ha : a ∈ (horn.{u} k 0).obj d := by
      change (alternatingMap k).app (op ⦋d.unop.len⦌) a ∈
        (stage (k - 1)).obj (op ⦋d.unop.len⦌) at hold
      exact (mem_oldStage_iff_mem_horn hk a).mp hold
    exact ⟨⟨a, ha⟩, rfl, Subtype.ext hraw⟩

/-- The complete native Type criterion gives the printed original successor pushout. -/
theorem stageSuccessor_isPushout (k : ℕ) (hk : 2 ≤ k) :
    IsPushout (horn.{u} k 0).ι (hornAttachment k hk) (stageSimplexMap k)
      (stageDiagram.map (homOfLE (Nat.sub_le k 1))) := by
  apply IsPushout.of_forall_isPushout_app
  intro d
  let old : (stage (k - 1) : SSet.{u}).obj d ⟶ (stage k : SSet.{u}).obj d :=
    (stageDiagram.{u}.map (homOfLE (Nat.sub_le k 1))).app d
  let sigma : (Δ[k] : SSet.{u}).obj d ⟶ (stage k : SSet.{u}).obj d :=
    (stageSimplexMap.{u} k).app d
  let hι : (horn k 0 : SSet.{u}).obj d ⟶ (Δ[k] : SSet.{u}).obj d := (horn k 0).ι.app d
  let attachment : (horn k 0 : SSet.{u}).obj d ⟶ (stage (k - 1) : SSet.{u}).obj d :=
    (hornAttachment.{u} k hk).app d
  change IsPushout hι attachment sigma old
  let : Mono old :=
    oldStage_app_mono k d
  have hp : IsPullback attachment hι old sigma :=
    ((stageSuccessor_isPullback.{u} k hk).app d).flip
  have hcover : Set.range old ⊔ Set.range sigma = Set.univ := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      obtain ⟨a, ha⟩ := stageSimplexMap_app_surjective.{u} k d x
      exact Or.inr ⟨a, ha⟩
  have houtside : ∀ a b, a ∉ Set.range hι → b ∉ Set.range hι →
      sigma a = sigma b → a = b := by
    intro a b ha hb h
    have ha' : a ∉ (horn.{u} k 0).obj d := by
      intro ha'
      exact ha ⟨⟨a, ha'⟩, rfl⟩
    have hb' : b ∉ (horn.{u} k 0).obj d := by
      intro hb'
      exact hb ⟨⟨b, hb'⟩, rfl⟩
    have hraw : (alternatingMap.{u} k).app d a = (alternatingMap k).app d b :=
      congrArg Subtype.val h
    exact alternatingMap_injOn_complement.{u} (n := d.unop.len) hk ha' hb' hraw
  exact (Types.isPushout_of_isPullback_of_mono' hp hcover houtside).flip

/-- The chosen pushout is compared to the original generated stage. -/
def stageSuccessorPushoutIso (k : ℕ) (hk : 2 ≤ k) :
    pushout (horn.{u} k 0).ι (hornAttachment k hk) ≅ (stage k : SSet.{u}) :=
  (stageSuccessor_isPushout.{u} k hk).isoPushout.symm

@[reassoc (attr := simp)]
theorem stageSuccessorPushoutIso_inl (k : ℕ) (hk : 2 ≤ k) :
    pushout.inl (horn.{u} k 0).ι (hornAttachment k hk) ≫
      (stageSuccessorPushoutIso k hk).hom = stageSimplexMap k :=
  (stageSuccessor_isPushout.{u} k hk).inl_isoPushout_inv

@[reassoc (attr := simp)]
theorem stageSuccessorPushoutIso_inr (k : ℕ) (hk : 2 ≤ k) :
    pushout.inr (horn.{u} k 0).ι (hornAttachment k hk) ≫
      (stageSuccessorPushoutIso k hk).hom = stageDiagram.map (homOfLE (Nat.sub_le k 1)) :=
  (stageSuccessor_isPushout.{u} k hk).inr_isoPushout_inv

@[reassoc (attr := simp)]
theorem stageSuccessorPushoutIso_sigma (k : ℕ) (hk : 2 ≤ k) :
    stageSimplexMap.{u} k ≫ (stageSuccessorPushoutIso k hk).inv =
      pushout.inl (horn.{u} k 0).ι (hornAttachment k hk) :=
  (stageSuccessor_isPushout.{u} k hk).inl_isoPushout_hom

@[reassoc (attr := simp)]
theorem stageSuccessorPushoutIso_old (k : ℕ) (hk : 2 ≤ k) :
    stageDiagram.{u}.map (homOfLE (Nat.sub_le k 1)) ≫
      (stageSuccessorPushoutIso k hk).inv = pushout.inr (horn.{u} k 0).ι (hornAttachment k hk) :=
  (stageSuccessor_isPushout.{u} k hk).inr_isoPushout_hom

/-- Actual unique descent from both original compatible legs to an arbitrary target. -/
def stageSuccessorDesc (k : ℕ) (hk : 2 ≤ k) {X : SSet.{u}}
    (f : (Δ[k] : SSet.{u}) ⟶ X) (g : (stage (k - 1) : SSet.{u}) ⟶ X)
    (w : (horn k 0).ι ≫ f = hornAttachment k hk ≫ g) : (stage k : SSet.{u}) ⟶ X :=
  (stageSuccessor_isPushout.{u} k hk).desc f g w

@[reassoc (attr := simp)]
theorem stageSuccessorDesc_sigma (k : ℕ) (hk : 2 ≤ k) {X : SSet.{u}}
    (f : (Δ[k] : SSet.{u}) ⟶ X) (g : (stage (k - 1) : SSet.{u}) ⟶ X)
    (w : (horn k 0).ι ≫ f = hornAttachment k hk ≫ g) :
    stageSimplexMap k ≫ stageSuccessorDesc k hk f g w = f :=
  (stageSuccessor_isPushout.{u} k hk).inl_desc f g w

@[reassoc (attr := simp)]
theorem stageSuccessorDesc_old (k : ℕ) (hk : 2 ≤ k) {X : SSet.{u}}
    (f : (Δ[k] : SSet.{u}) ⟶ X) (g : (stage (k - 1) : SSet.{u}) ⟶ X)
    (w : (horn k 0).ι ≫ f = hornAttachment k hk ≫ g) :
    stageDiagram.map (homOfLE (Nat.sub_le k 1)) ≫ stageSuccessorDesc k hk f g w = g :=
  (stageSuccessor_isPushout.{u} k hk).inr_desc f g w

/-- The two original factors characterize the actual descendant. -/
theorem stageSuccessorDesc_unique (k : ℕ) (hk : 2 ≤ k) {X : SSet.{u}}
    (f : (Δ[k] : SSet.{u}) ⟶ X) (g : (stage (k - 1) : SSet.{u}) ⟶ X)
    (w : (horn k 0).ι ≫ f = hornAttachment k hk ≫ g) (d : (stage k : SSet.{u}) ⟶ X)
    (hf : stageSimplexMap k ≫ d = f)
    (hg : stageDiagram.map (homOfLE (Nat.sub_le k 1)) ≫ d = g) :
    d = stageSuccessorDesc k hk f g w :=
  (stageSuccessor_isPushout.{u} k hk).hom_ext
    (hf.trans (stageSuccessorDesc_sigma k hk f g w).symm)
    (hg.trans (stageSuccessorDesc_old k hk f g w).symm)

/-- At the original full nerve, descent is the original stage inclusion. -/
theorem stageSuccessorDesc_fullE (k : ℕ) (hk : 2 ≤ k) :
    stageSuccessorDesc.{u} k hk (alternatingMap k) (stage (k - 1)).ι
      (hornAttachment_ι k hk).symm = (stage k).ι := by
  exact (stageSuccessorDesc_unique k hk (alternatingMap k) (stage (k - 1)).ι
    (hornAttachment_ι k hk).symm (stage k).ι (stageSimplexMap_ι k)
    (stageDiagram_map_ι _)).symm

/-- The same original square is a pushout after the actual inner-discrete embedding. -/
theorem innerStageSuccessor_isPushout (k : ℕ) (hk : 2 ≤ k) :
    IsPushout (simplicialSpaceDiscrete.{u}.map (horn k 0).ι)
      (simplicialSpaceDiscrete.map (hornAttachment k hk))
      (simplicialSpaceDiscrete.map (stageSimplexMap k))
      (simplicialSpaceDiscrete.map (stageDiagram.map (homOfLE (Nat.sub_le k 1)))) := by
  apply IsPushout.of_forall_isPushout_app
  intro a
  apply IsPushout.of_forall_isPushout_app
  intro b
  exact (stageSuccessor_isPushout.{u} k hk).app a

/-- Native descent of the original inner-discrete cocone to any simplicial-space target. -/
def innerStageSuccessorDesc (k : ℕ) (hk : 2 ≤ k) {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj (Δ[k] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (stage (k - 1) : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn k 0).ι ≫ f =
      simplicialSpaceDiscrete.map (hornAttachment k hk) ≫ g) :
    simplicialSpaceDiscrete.obj (stage k : SSet.{u}) ⟶ X :=
  (innerStageSuccessor_isPushout.{u} k hk).desc f g w

@[reassoc (attr := simp)]
theorem innerStageSuccessorDesc_sigma (k : ℕ) (hk : 2 ≤ k) {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj (Δ[k] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (stage (k - 1) : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn k 0).ι ≫ f =
      simplicialSpaceDiscrete.map (hornAttachment k hk) ≫ g) :
    dsimp% (simplicialSpaceDiscrete.map (stageSimplexMap k) ≫
        innerStageSuccessorDesc k hk f g w) = f :=
  (innerStageSuccessor_isPushout.{u} k hk).inl_desc f g w

@[reassoc (attr := simp)]
theorem innerStageSuccessorDesc_old (k : ℕ) (hk : 2 ≤ k) {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj (Δ[k] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (stage (k - 1) : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn k 0).ι ≫ f =
      simplicialSpaceDiscrete.map (hornAttachment k hk) ≫ g) :
    dsimp% (simplicialSpaceDiscrete.map (stageDiagram.map (homOfLE (Nat.sub_le k 1))) ≫
      innerStageSuccessorDesc k hk f g w) = g :=
  (innerStageSuccessor_isPushout.{u} k hk).inr_desc f g w

/-- Both original inner-discrete injections characterize descent. -/
theorem innerStageSuccessorDesc_unique (k : ℕ) (hk : 2 ≤ k) {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj (Δ[k] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (stage (k - 1) : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn k 0).ι ≫ f =
      simplicialSpaceDiscrete.map (hornAttachment k hk) ≫ g)
    (d : simplicialSpaceDiscrete.obj (stage k : SSet.{u}) ⟶ X)
    (hf : simplicialSpaceDiscrete.map (stageSimplexMap k) ≫ d = f)
    (hg : simplicialSpaceDiscrete.map (stageDiagram.map (homOfLE (Nat.sub_le k 1))) ≫ d = g) :
    d = innerStageSuccessorDesc k hk f g w :=
  (innerStageSuccessor_isPushout.{u} k hk).hom_ext
    (hf.trans (innerStageSuccessorDesc_sigma k hk f g w).symm)
    (hg.trans (innerStageSuccessorDesc_old k hk f g w).symm)

/-- The original simplex injection equation holds at both original degrees. -/
theorem innerStageSuccessorDesc_sigma_app (k : ℕ) (hk : 2 ≤ k)
    {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj (Δ[k] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (stage (k - 1) : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn k 0).ι ≫ f =
      simplicialSpaceDiscrete.map (hornAttachment k hk) ≫ g)
    (a b : SimplexCategoryᵒᵖ) (x : (Δ[k] : SSet.{u}).obj a) :
    ((innerStageSuccessorDesc k hk f g w).app a).app b ((stageSimplexMap k).app a x) =
      (f.app a).app b x :=
  congrArg (fun h : simplicialSpaceDiscrete.obj (Δ[k] : SSet.{u}) ⟶ X => (h.app a).app b x)
    (innerStageSuccessorDesc_sigma k hk f g w)

/-- The original old-stage injection equation holds at both original degrees. -/
theorem innerStageSuccessorDesc_old_app (k : ℕ) (hk : 2 ≤ k)
    {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj (Δ[k] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (stage (k - 1) : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn k 0).ι ≫ f =
      simplicialSpaceDiscrete.map (hornAttachment k hk) ≫ g)
    (a b : SimplexCategoryᵒᵖ) (x : (stage (k - 1)).obj a) :
    ((innerStageSuccessorDesc k hk f g w).app a).app b
      ((stageDiagram.map (homOfLE (Nat.sub_le k 1))).app a x) = (g.app a).app b x :=
  congrArg (fun h : simplicialSpaceDiscrete.obj (stage (k - 1) : SSet.{u}) ⟶ X =>
    (h.app a).app b x) (innerStageSuccessorDesc_old k hk f g w)

/-- Every outer operator acts by the original stage map before descent. -/
theorem innerStageSuccessorDesc_outer_naturality (k : ℕ) (hk : 2 ≤ k)
    {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj (Δ[k] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (stage (k - 1) : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn k 0).ι ≫ f =
      simplicialSpaceDiscrete.map (hornAttachment k hk) ≫ g)
    {a a' : SimplexCategoryᵒᵖ} (s : a ⟶ a') (b : SimplexCategoryᵒᵖ)
    (x : (stage k).obj a) :
    (X.map s).app b (((innerStageSuccessorDesc k hk f g w).app a).app b x) =
      ((innerStageSuccessorDesc k hk f g w).app a').app b ((stage k : SSet.{u}).map s x) :=
  (congrArg (fun h : (simplicialSpaceDiscrete.obj (stage k : SSet.{u})).obj a ⟶ X.obj a' =>
    h.app b x) ((innerStageSuccessorDesc k hk f g w).naturality s)).symm

/-- Every inner operator acts on the actual target, keeping the original stage point. -/
theorem innerStageSuccessorDesc_inner_naturality (k : ℕ) (hk : 2 ≤ k)
    {X : SimplicialObject SSet.{u}}
    (f : simplicialSpaceDiscrete.obj (Δ[k] : SSet.{u}) ⟶ X)
    (g : simplicialSpaceDiscrete.obj (stage (k - 1) : SSet.{u}) ⟶ X)
    (w : simplicialSpaceDiscrete.map (horn k 0).ι ≫ f =
      simplicialSpaceDiscrete.map (hornAttachment k hk) ≫ g)
    (a : SimplexCategoryᵒᵖ) {b b' : SimplexCategoryᵒᵖ} (s : b ⟶ b') (x : (stage k).obj a) :
    (X.obj a).map s (((innerStageSuccessorDesc k hk f g w).app a).app b x) =
      ((innerStageSuccessorDesc k hk f g w).app a).app b' x :=
  (congrArg (fun h : ((simplicialSpaceDiscrete.obj (stage k : SSet.{u})).obj a).obj b ⟶
      (X.obj a).obj b' => h x)
    (((innerStageSuccessorDesc k hk f g w).app a).naturality s)).symm

end SSet.coherentIso
