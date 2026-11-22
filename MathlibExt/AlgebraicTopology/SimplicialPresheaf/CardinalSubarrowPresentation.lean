/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.KanWeakArrowInterpolation
import Mathlib.SetTheory.Cardinal.HasCardinalLT
import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
import Mathlib.CategoryTheory.Limits.Comma

/-!
# Cardinal-filtered presentations of original simplicial-presheaf arrows

The index consists of actual coupled original subdiagrams. Both total-point
bounds use the native lifted cardinal comparison, and all diagram and colimit
maps retain the original site, inner simplex and ambient arrow components.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w z

open CategoryTheory CategoryTheory.Limits Opposite
open SimplicialPresheaf.KanWeakInterpolation SSet.KanWeakInterpolation
open scoped Simplicial

namespace SimplicialPresheaf

/-- Every original site object, inner simplex object and point, in its original universe. -/
abbrev originalTotalPoints {D : Type w} [Category.{v} D]
    (X : SimplicialPresheaf.{u} D) : Type (max u w) :=
  Σ d : Dᵒᵖ, (X.obj d).Elements

/-- The actual original site and all site/simplex operators used in the size profile. -/
abbrev cardinalSubarrowWidth (D : Type w) [Category.{v} D] :=
  D ⊕ (Arrow D ⊕ Arrow SimplexCategory)

variable {D : Type w} [Category.{v} D]
  {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)

/-- Actual original subarrows with both aggregate original endpoint point bounds. -/
abbrev cardinalSubarrowIndex (μ : Cardinal.{u}) :=
  {s : Subdiagram f //
    HasCardinalLT (originalTotalPoints (Subdiagram.leftFunctor f s)) μ ∧
      HasCardinalLT (originalTotalPoints (Subdiagram.rightFunctor f s)) μ}

private theorem smallOriginalSubdiagram [Small.{u} D] : Small.{u} (Subdiagram f) := by
  apply small_of_injective (f := fun s : Subdiagram f => s.row)
  intro s t h
  exact Subdiagram.ext h

/-- The literal original index is small without changing its carrier. -/
instance cardinalSubarrowIndex_small [Small.{u} D] (μ : Cardinal.{u}) :
    Small.{u} (cardinalSubarrowIndex f μ) := by
  let := smallOriginalSubdiagram f
  infer_instance

/-- The original whole-Arrow inclusion diagram, defined for every cardinal. -/
def cardinalSubarrowDiagram (μ : Cardinal.{u}) :
    cardinalSubarrowIndex f μ ⥤ Arrow (SimplicialPresheaf.{u} D) where
  obj s := Subdiagram.arrow f s.val
  map h := Subdiagram.map f (leOfHom h)
  map_id _ := by ext d n x <;> rfl
  map_comp _ _ := by ext d n x <;> rfl

/-- The same original ambient arrow and both original inclusion legs. -/
def cardinalSubarrowCocone (μ : Cardinal.{u}) : Cocone (cardinalSubarrowDiagram f μ) where
  pt := Arrow.mk f
  ι :=
    { app s := Subdiagram.inclusion f s.val
      naturality := by
        intro s t h
        change Subdiagram.map f (leOfHom h) ≫ Subdiagram.inclusion f t.val =
          Subdiagram.inclusion f s.val ≫ 𝟙 (Arrow.mk f)
        simpa only [Category.comp_id] using Subdiagram.map_inclusion f (leOfHom h) }

/-- The projected original source cocone. -/
def cardinalSubarrowLeftCocone (μ : Cardinal.{u}) :
    Cocone (cardinalSubarrowDiagram f μ ⋙ Arrow.leftFunc) :=
  Arrow.leftFunc.mapCocone (cardinalSubarrowCocone f μ)

/-- The projected original target cocone. -/
def cardinalSubarrowRightCocone (μ : Cardinal.{u}) :
    Cocone (cardinalSubarrowDiagram f μ ⋙ Arrow.rightFunc) :=
  Arrow.rightFunc.mapCocone (cardinalSubarrowCocone f μ)

theorem cardinalSubarrowDiagram_hom (μ : Cardinal.{u}) (s : cardinalSubarrowIndex f μ) :
    ((cardinalSubarrowDiagram f μ).obj s).hom = Subdiagram.hom f s.val := rfl

theorem cardinalSubarrowCocone_left (μ : Cardinal.{u}) (s : cardinalSubarrowIndex f μ) :
    ((cardinalSubarrowCocone f μ).ι.app s).left = Subdiagram.leftInclusion f s.val := rfl

theorem cardinalSubarrowCocone_right (μ : Cardinal.{u}) (s : cardinalSubarrowIndex f μ) :
    ((cardinalSubarrowCocone f μ).ι.app s).right = Subdiagram.rightInclusion f s.val := rfl

theorem cardinalSubarrowCocone_square (μ : Cardinal.{u}) (s : cardinalSubarrowIndex f μ) :
    ((cardinalSubarrowCocone f μ).ι.app s).left ≫ f =
      ((cardinalSubarrowDiagram f μ).obj s).hom ≫
        ((cardinalSubarrowCocone f μ).ι.app s).right :=
  ((cardinalSubarrowCocone f μ).ι.app s).w

theorem cardinalSubarrowCocone_left_val (μ : Cardinal.{u}) (s : cardinalSubarrowIndex f μ)
    (d : Dᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (x : ((Subdiagram.leftFunctor f s.val).obj d).obj n) :
    ((((cardinalSubarrowCocone f μ).ι.app s).left.app d).app n) x = x.val := rfl

theorem cardinalSubarrowCocone_right_val (μ : Cardinal.{u}) (s : cardinalSubarrowIndex f μ)
    (d : Dᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (x : ((Subdiagram.rightFunctor f s.val).obj d).obj n) :
    ((((cardinalSubarrowCocone f μ).ι.app s).right.app d).app n) x = x.val := rfl

theorem cardinalSubarrowDiagram_map_left_val (μ : Cardinal.{u})
    {s t : cardinalSubarrowIndex f μ} (h : s ⟶ t) (d : Dᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (x : ((Subdiagram.leftFunctor f s.val).obj d).obj n) :
    (((((cardinalSubarrowDiagram f μ).map h).left.app d).app n) x).val = x.val := rfl

theorem cardinalSubarrowDiagram_map_right_val (μ : Cardinal.{u})
    {s t : cardinalSubarrowIndex f μ} (h : s ⟶ t) (d : Dᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (x : ((Subdiagram.rightFunctor f s.val).obj d).obj n) :
    (((((cardinalSubarrowDiagram f μ).map h).right.app d).app n) x).val = x.val := rfl

theorem cardinalSubarrowDiagram_hom_val (μ : Cardinal.{u}) (s : cardinalSubarrowIndex f μ)
    (d : Dᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (x : ((Subdiagram.leftFunctor f s.val).obj d).obj n) :
    (((((cardinalSubarrowDiagram f μ).obj s).hom.app d).app n) x).val =
      ((f.app d).app n) x.val := rfl

private def unionPointCover {Z : SimplicialPresheaf.{u} D} {I : Type u}
    (K : I → ∀ d : Dᵒᵖ, (Z.obj d).Subcomplex) :
    (Σ i : I, Σ d : Dᵒᵖ, (K i d : SSet.{u}).Elements) →
      Σ d : Dᵒᵖ, ((⨆ i, K i d : (Z.obj d).Subcomplex) : SSet.{u}).Elements :=
  fun ⟨i, d, q⟩ => ⟨d, Functor.elementsMk _ q.obj
    ⟨q.val.val, (le_iSup (fun j => K j d) i) q.obj q.val.property⟩⟩

private theorem unionPointCover_surjective {Z : SimplicialPresheaf.{u} D} {I : Type u}
    (K : I → ∀ d : Dᵒᵖ, (Z.obj d).Subcomplex) :
    Function.Surjective (unionPointCover K) := by
  rintro ⟨d, q⟩
  have hm := q.val.property
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hm
  obtain ⟨i, hi⟩ := hm
  refine ⟨⟨i, d, Functor.elementsMk _ q.obj ⟨q.val.val, hi⟩⟩, ?_⟩
  apply Sigma.ext rfl
  apply heq_of_eq
  cases q
  rfl

private theorem unionPoints_lt {Z : SimplicialPresheaf.{u} D} {I : Type u}
    (K : I → ∀ d : Dᵒᵖ, (Z.obj d).Subcomplex)
    (μ : Cardinal.{u}) [Fact μ.IsRegular] (hI : HasCardinalLT I μ)
    (hK : ∀ i, HasCardinalLT (Σ d : Dᵒᵖ, (K i d : SSet.{u}).Elements) μ) :
    HasCardinalLT
      (Σ d : Dᵒᵖ, ((⨆ i, K i d : (Z.obj d).Subcomplex) : SSet.{u}).Elements) μ :=
  (hasCardinalLT_sigma _ μ hI hK).of_surjective _ (unionPointCover_surjective K)

private abbrev siteRow {Z : SimplicialPresheaf.{u} D} {I : Type u}
    (site : I → Dᵒᵖ) (K : ∀ i, (Z.obj (site i)).Subcomplex) (d : Dᵒᵖ) :=
  (⨆ i, ⨆ h : site i ⟶ d, (K i).image (Z.map h) : (Z.obj d).Subcomplex)

private def sitePointCover {Z : SimplicialPresheaf.{u} D} {I : Type u}
    (site : I → Dᵒᵖ) (K : ∀ i, (Z.obj (site i)).Subcomplex) :
    (Σ i : I, Σ d : Dᵒᵖ, Σ _ : site i ⟶ d, (K i : SSet.{u}).Elements) →
      Σ d : Dᵒᵖ, (siteRow site K d : SSet.{u}).Elements :=
  fun ⟨i, d, h, q⟩ => by
    have hi : (K i).image (Z.map h) ≤ siteRow site K d :=
      le_iSup_of_le i (le_iSup (fun g : site i ⟶ d => (K i).image (Z.map g)) h)
    exact ⟨d, Functor.elementsMk _ q.obj
      ⟨((Z.map h).app q.obj) q.val.val, hi q.obj ⟨q.val.val, q.val.property, rfl⟩⟩⟩

private theorem sitePointCover_surjective {Z : SimplicialPresheaf.{u} D} {I : Type u}
    (site : I → Dᵒᵖ) (K : ∀ i, (Z.obj (site i)).Subcomplex) :
    Function.Surjective (sitePointCover site K) := by
  rintro ⟨d, q⟩
  have hm := q.val.property
  simp only [siteRow, Subfunctor.iSup_obj, Set.mem_iUnion,
    SSet.Subcomplex.image, Subfunctor.image_obj, Set.mem_image] at hm
  obtain ⟨i, h, x, hx, heq⟩ := hm
  refine ⟨⟨i, d, h, Functor.elementsMk _ q.obj ⟨x, hx⟩⟩, ?_⟩
  dsimp only [sitePointCover]
  apply congrArg (fun r : (siteRow site K d : SSet.{u}).Elements =>
    (⟨d, r⟩ : Σ e : Dᵒᵖ, (siteRow site K e : SSet.{u}).Elements))
  cases q with
  | @mk n val => exact congrArg (Functor.elementsMk _ n) (Subtype.ext heq)

private theorem sitePoints_lt {Z : SimplicialPresheaf.{u} D} {I : Type u}
    (site : I → Dᵒᵖ) (K : ∀ i, (Z.obj (site i)).Subcomplex) [∀ i, SSet.Finite (K i)]
    (μ : Cardinal.{u}) [Fact μ.IsRegular] (hΩ : Cardinal.aleph0.{u} < μ)
    (hD : HasCardinalLT D μ) (hOp : HasCardinalLT (Arrow D) μ) (hI : HasCardinalLT I μ) :
    HasCardinalLT (Σ d : Dᵒᵖ, (siteRow site K d : SSet.{u}).Elements) μ := by
  have hDop : HasCardinalLT Dᵒᵖ μ :=
    hD.of_injective Opposite.unop (by intro a b h; cases a; cases b; cases h; rfl)
  have hArrowOp : HasCardinalLT (Arrow Dᵒᵖ) μ :=
    (hasCardinalLT_arrow_op_iff D μ).mpr hOp
  have hHom (d e : Dᵒᵖ) : HasCardinalLT (d ⟶ e) μ :=
    hArrowOp.of_injective Arrow.mk (Arrow.mk_injective d e)
  have hPieces (i : I) : HasCardinalLT (K i : SSet.{u}).Elements μ :=
    (hasCardinalLT_iff_cardinal_mk_lt _ _).mpr
      ((finiteElements_le_aleph0 _).trans_lt hΩ)
  have hAll := hasCardinalLT_sigma
    (fun i : I => Σ d : Dᵒᵖ, Σ h : site i ⟶ d, (K i : SSet.{u}).Elements) μ hI
    (fun i => hasCardinalLT_sigma _ μ hDop
      (fun d => hasCardinalLT_sigma _ μ (hHom (site i) d) (fun _ => hPieces i)))
  exact hAll.of_surjective _ (sitePointCover_surjective site K)

/-- Close actual finite pieces under all original site maps, with both strict point bounds. -/
theorem cardinalSubarrow_siteClosure_lt {I : Type u} (site : I → Dᵒᵖ)
    (pieces : ∀ i, FiniteSubarrow (f.app (site i)))
    (μ : Cardinal.{u}) [Fact μ.IsRegular] (hΩ : Cardinal.aleph0.{u} < μ)
    (hD : HasCardinalLT D μ) (hOp : HasCardinalLT (Arrow D) μ) (hI : HasCardinalLT I μ) :
    HasCardinalLT (originalTotalPoints (Subdiagram.leftFunctor f
        (Subdiagram.siteClosure f site pieces))) μ ∧
      HasCardinalLT (originalTotalPoints (Subdiagram.rightFunctor f
        (Subdiagram.siteClosure f site pieces))) μ :=
  ⟨sitePoints_lt site (fun i => (pieces i).left _) μ hΩ hD hOp hI,
    sitePoints_lt site (fun i => (pieces i).right _) μ hΩ hD hOp hI⟩

/-- The original union of any actually μ-small external family remains in the literal index. -/
def cardinalSubarrowUnion (μ : Cardinal.{u}) [Fact μ.IsRegular]
    {I : Type z} (s : I → cardinalSubarrowIndex f μ) (hI : HasCardinalLT I μ) :
    cardinalSubarrowIndex f μ := by
  letI : Small.{u} I := hI.small
  let t : Shrink.{u} I → Subdiagram f := fun i => (s ((equivShrink.{u} I).symm i)).val
  have hSmall : HasCardinalLT (Shrink.{u} I) μ :=
    (hasCardinalLT_iff_of_equiv (equivShrink.{u} I) μ).mp hI
  exact ⟨Subdiagram.indexedUnion f t,
    unionPoints_lt (fun i d => (t i |>.row d).left _) μ hSmall
      (fun i => (s ((equivShrink.{u} I).symm i)).property.1),
    unionPoints_lt (fun i d => (t i |>.row d).right _) μ hSmall
      (fun i => (s ((equivShrink.{u} I).symm i)).property.2)⟩

theorem le_cardinalSubarrowUnion (μ : Cardinal.{u}) [Fact μ.IsRegular]
    {I : Type z} (s : I → cardinalSubarrowIndex f μ) (hI : HasCardinalLT I μ) (i : I) :
    s i ≤ cardinalSubarrowUnion f μ s hI := by
  let : Small.{u} I := hI.small
  change (s i).val ≤ Subdiagram.indexedUnion f
    (fun j : Shrink.{u} I => (s ((equivShrink.{u} I).symm j)).val)
  simpa only [Equiv.symm_apply_apply] using Subdiagram.le_indexedUnion f
    (fun j : Shrink.{u} I => (s ((equivShrink.{u} I).symm j)).val) (equivShrink.{u} I i)

/-- Actual μ-small original unions and thinness prove the full native filteredness criterion. -/
theorem cardinalSubarrowIndex_isCardinalFiltered (μ : Cardinal.{u}) [Fact μ.IsRegular] :
    IsCardinalFiltered (cardinalSubarrowIndex f μ) μ := by
  rw [isCardinalFiltered_iff']
  constructor
  · intro I s hI
    exact ⟨cardinalSubarrowUnion f μ s hI,
      fun i => ⟨homOfLE (le_cardinalSubarrowUnion f μ s hI i)⟩⟩
  · intro I j k a hI hNonempty
    let : Nonempty I := hNonempty
    refine ⟨k, 𝟙 k, a (Classical.arbitrary I), ?_⟩
    intro i
    exact Subsingleton.elim _ _

/-- The original source-simplex support includes its actual image on the target. -/
def cardinalSubarrowOfLeftSimplex (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hD : HasCardinalLT D μ)
    (hOp : HasCardinalLT (Arrow D) μ) (d : Dᵒᵖ) {n : ℕ} (x : (X.obj d) _⦋n⦌) :
    cardinalSubarrowIndex f μ :=
  ⟨Subdiagram.siteClosure f (fun _ : PUnit.{u + 1} => d)
      (fun _ => FiniteSubarrow.ofLeftSimplex (f.app d) x),
    cardinalSubarrow_siteClosure_lt f _ _ μ hΩ hD hOp
      (hasCardinalLT_of_finite _ _ hΩ.le)⟩

/-- A prescribed original target point also has an actual μ-small coupled support. -/
def cardinalSubarrowOfRightSimplex (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hD : HasCardinalLT D μ)
    (hOp : HasCardinalLT (Arrow D) μ) (d : Dᵒᵖ) {n : ℕ} (x : (Y.obj d) _⦋n⦌) :
    cardinalSubarrowIndex f μ :=
  ⟨Subdiagram.siteClosure f (fun _ : PUnit.{u + 1} => d)
      (fun _ => FiniteSubarrow.ofRightSimplex (f.app d) x),
    cardinalSubarrow_siteClosure_lt f _ _ μ hΩ hD hOp
      (hasCardinalLT_of_finite _ _ hΩ.le)⟩

theorem cardinalSubarrowOfLeft_mem (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hD : HasCardinalLT D μ)
    (hOp : HasCardinalLT (Arrow D) μ) (d : Dᵒᵖ) {n : ℕ} (x : (X.obj d) _⦋n⦌) :
    x ∈ (((cardinalSubarrowOfLeftSimplex f μ hΩ hD hOp d x).val.row d).left (f.app d)).obj
        (op ⦋n⦌) := by
  have h := (Subdiagram.piece_le_siteClosure f (fun _ : PUnit.{u + 1} => d)
    (fun _ => FiniteSubarrow.ofLeftSimplex (f.app d) x) PUnit.unit).1
  exact h (op ⦋n⦌) (SSet.Subcomplex.mem_ofSimplex_obj x)

theorem cardinalSubarrowOfLeft_image_mem (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hD : HasCardinalLT D μ)
    (hOp : HasCardinalLT (Arrow D) μ) (d : Dᵒᵖ) {n : ℕ} (x : (X.obj d) _⦋n⦌) :
    ((f.app d).app (op ⦋n⦌)) x ∈
      (((cardinalSubarrowOfLeftSimplex f μ hΩ hD hOp d x).val.row d).right (f.app d)).obj
          (op ⦋n⦌) := by
  exact ((cardinalSubarrowOfLeftSimplex f μ hΩ hD hOp d x).val.row d).property (op ⦋n⦌)
    ⟨x, cardinalSubarrowOfLeft_mem f μ hΩ hD hOp d x, rfl⟩

theorem cardinalSubarrowOfRight_mem (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hD : HasCardinalLT D μ)
    (hOp : HasCardinalLT (Arrow D) μ) (d : Dᵒᵖ) {n : ℕ} (x : (Y.obj d) _⦋n⦌) :
    x ∈ (((cardinalSubarrowOfRightSimplex f μ hΩ hD hOp d x).val.row d).right (f.app d)).obj
        (op ⦋n⦌) := by
  have h := (Subdiagram.piece_le_siteClosure f (fun _ : PUnit.{u + 1} => d)
    (fun _ => FiniteSubarrow.ofRightSimplex (f.app d) x) PUnit.unit).2
  exact h (op ⦋n⦌) (SSet.Subcomplex.mem_ofSimplex_obj x)

private theorem width_site (μ : Cardinal.{u}) (h : HasCardinalLT (cardinalSubarrowWidth D) μ) :
    HasCardinalLT D μ := h.of_injective Sum.inl Sum.inl_injective

private theorem width_arrows (μ : Cardinal.{u}) (h : HasCardinalLT (cardinalSubarrowWidth D) μ) :
    HasCardinalLT (Arrow D) μ :=
  h.of_injective (fun a => Sum.inr (Sum.inl a)) (Sum.inr_injective.comp Sum.inl_injective)

/-- The actual original source inclusion cocone recovers X at every site and inner degree. -/
def cardinalSubarrowLeftIsColimit (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hWidth : HasCardinalLT (cardinalSubarrowWidth D) μ) :
    IsColimit (cardinalSubarrowLeftCocone f μ) := by
  letI := cardinalSubarrowIndex_isCardinalFiltered f μ
  letI := isFiltered_of_isCardinalFiltered (cardinalSubarrowIndex f μ) μ
  apply evaluationJointlyReflectsColimits
  intro d
  apply evaluationJointlyReflectsColimits
  intro n
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    let s := cardinalSubarrowOfLeftSimplex f μ hΩ (width_site μ hWidth) (width_arrows μ hWidth)
      d (n := n.unop.len) x
    refine ⟨s, ⟨x, cardinalSubarrowOfLeft_mem f μ hΩ _ _ d x⟩, rfl⟩
  · intro s x y hxy
    refine ⟨s, 𝟙 s, ?_⟩
    have hx : x = y := Subtype.ext hxy
    exact congrArg
        (fun q =>
          (((cardinalSubarrowDiagram f μ ⋙ Arrow.leftFunc).map (𝟙 s)).app d).app n q) hx

/-- The actual original target inclusion cocone recovers Y with the same original index. -/
def cardinalSubarrowRightIsColimit (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hWidth : HasCardinalLT (cardinalSubarrowWidth D) μ) :
    IsColimit (cardinalSubarrowRightCocone f μ) := by
  letI := cardinalSubarrowIndex_isCardinalFiltered f μ
  letI := isFiltered_of_isCardinalFiltered (cardinalSubarrowIndex f μ) μ
  apply evaluationJointlyReflectsColimits
  intro d
  apply evaluationJointlyReflectsColimits
  intro n
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    let s := cardinalSubarrowOfRightSimplex f μ hΩ (width_site μ hWidth) (width_arrows μ hWidth)
      d (n := n.unop.len) x
    refine ⟨s, ⟨x, cardinalSubarrowOfRight_mem f μ hΩ _ _ d x⟩, rfl⟩
  · intro s x y hxy
    refine ⟨s, 𝟙 s, ?_⟩
    have hx : x = y := Subtype.ext hxy
    exact congrArg
        (fun q =>
          (((cardinalSubarrowDiagram f μ ⋙ Arrow.rightFunc).map (𝟙 s)).app d).app n q) hx

/-- Both original endpoint universal properties give the SAME whole original Arrow colimit. -/
def cardinalSubarrowArrowIsColimit (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hWidth : HasCardinalLT (cardinalSubarrowWidth D) μ) :
    IsColimit (cardinalSubarrowCocone f μ) :=
  Comma.fstSndJointlyReflectColimit (cardinalSubarrowLeftIsColimit f μ hΩ hWidth)
    (cardinalSubarrowRightIsColimit f μ hΩ hWidth)

/-- The full native cardinal-filtered presentation, with all three original colimit witnesses. -/
theorem cardinalSubarrowIndex_presentation [Small.{u} D] (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hWidth : HasCardinalLT (cardinalSubarrowWidth D) μ) :
    Small.{u} (cardinalSubarrowIndex f μ) ∧ IsCardinalFiltered (cardinalSubarrowIndex f μ) μ ∧
      Nonempty (IsColimit (cardinalSubarrowLeftCocone f μ)) ∧
      Nonempty (IsColimit (cardinalSubarrowRightCocone f μ)) ∧
      Nonempty (IsColimit (cardinalSubarrowCocone f μ)) :=
  ⟨inferInstance, cardinalSubarrowIndex_isCardinalFiltered f μ,
    ⟨cardinalSubarrowLeftIsColimit f μ hΩ hWidth⟩,
    ⟨cardinalSubarrowRightIsColimit f μ hΩ hWidth⟩,
    ⟨cardinalSubarrowArrowIsColimit f μ hΩ hWidth⟩⟩

/-- Descent along the same original Arrow inclusion cocone. -/
def cardinalSubarrowDesc (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hWidth : HasCardinalLT (cardinalSubarrowWidth D) μ)
    (c : Cocone (cardinalSubarrowDiagram f μ)) : Arrow.mk f ⟶ c.pt :=
  (cardinalSubarrowArrowIsColimit f μ hΩ hWidth).desc c

theorem cardinalSubarrowDesc_left (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hWidth : HasCardinalLT (cardinalSubarrowWidth D) μ)
    (c : Cocone (cardinalSubarrowDiagram f μ)) (s : cardinalSubarrowIndex f μ) :
    (Subdiagram.inclusion f s.val).left ≫ (cardinalSubarrowDesc f μ hΩ hWidth c).left =
      (c.ι.app s).left :=
  congrArg Arrow.Hom.left ((cardinalSubarrowArrowIsColimit f μ hΩ hWidth).fac c s)

theorem cardinalSubarrowDesc_right (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hWidth : HasCardinalLT (cardinalSubarrowWidth D) μ)
    (c : Cocone (cardinalSubarrowDiagram f μ)) (s : cardinalSubarrowIndex f μ) :
    (Subdiagram.inclusion f s.val).right ≫ (cardinalSubarrowDesc f μ hΩ hWidth c).right =
      (c.ι.app s).right :=
  congrArg Arrow.Hom.right ((cardinalSubarrowArrowIsColimit f μ hΩ hWidth).fac c s)

theorem cardinalSubarrowDesc_square (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hWidth : HasCardinalLT (cardinalSubarrowWidth D) μ)
    (c : Cocone (cardinalSubarrowDiagram f μ)) :
    (cardinalSubarrowDesc f μ hΩ hWidth c).left ≫ c.pt.hom =
      f ≫ (cardinalSubarrowDesc f μ hΩ hWidth c).right :=
  (cardinalSubarrowDesc f μ hΩ hWidth c).w

theorem cardinalSubarrowDesc_unique (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hWidth : HasCardinalLT (cardinalSubarrowWidth D) μ)
    (c : Cocone (cardinalSubarrowDiagram f μ)) (h : Arrow.mk f ⟶ c.pt)
    (hL : ∀ s, (Subdiagram.inclusion f s.val).left ≫ h.left = (c.ι.app s).left)
    (hR : ∀ s, (Subdiagram.inclusion f s.val).right ≫ h.right = (c.ι.app s).right) :
    h = cardinalSubarrowDesc f μ hΩ hWidth c := by
  apply (cardinalSubarrowArrowIsColimit f μ hΩ hWidth).uniq c h
  intro s
  apply Arrow.hom_ext
  · exact hL s
  · exact hR s

/-- Original cocone postcomposition commutes with the SAME whole-Arrow descent. -/
theorem cardinalSubarrowDesc_extend (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hWidth : HasCardinalLT (cardinalSubarrowWidth D) μ)
    (c : Cocone (cardinalSubarrowDiagram f μ)) {Q : Arrow (SimplicialPresheaf.{u} D)}
    (q : c.pt ⟶ Q) :
    cardinalSubarrowDesc f μ hΩ hWidth (c.extend q) = cardinalSubarrowDesc f μ hΩ hWidth c ≫ q := by
  symm
  apply cardinalSubarrowDesc_unique f μ hΩ hWidth (c.extend q)
  · intro s
    change (Subdiagram.inclusion f s.val).left ≫
        ((cardinalSubarrowDesc f μ hΩ hWidth c).left ≫ q.left) = (c.ι.app s).left ≫ q.left
    rw [← Category.assoc, cardinalSubarrowDesc_left]
    rfl
  · intro s
    change (Subdiagram.inclusion f s.val).right ≫
        ((cardinalSubarrowDesc f μ hΩ hWidth c).right ≫ q.right) = (c.ι.app s).right ≫ q.right
    rw [← Category.assoc, cardinalSubarrowDesc_right]
    rfl

theorem cardinalSubarrowDesc_left_site (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hWidth : HasCardinalLT (cardinalSubarrowWidth D) μ)
    (c : Cocone (cardinalSubarrowDiagram f μ)) {d e : Dᵒᵖ} (h : d ⟶ e) :
    X.map h ≫ (cardinalSubarrowDesc f μ hΩ hWidth c).left.app e =
      (cardinalSubarrowDesc f μ hΩ hWidth c).left.app d ≫ c.pt.left.map h :=
  (cardinalSubarrowDesc f μ hΩ hWidth c).left.naturality h

theorem cardinalSubarrowDesc_right_site (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hWidth : HasCardinalLT (cardinalSubarrowWidth D) μ)
    (c : Cocone (cardinalSubarrowDiagram f μ)) {d e : Dᵒᵖ} (h : d ⟶ e) :
    Y.map h ≫ (cardinalSubarrowDesc f μ hΩ hWidth c).right.app e =
      (cardinalSubarrowDesc f μ hΩ hWidth c).right.app d ≫ c.pt.right.map h :=
  (cardinalSubarrowDesc f μ hΩ hWidth c).right.naturality h

theorem cardinalSubarrowDesc_left_inner (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hWidth : HasCardinalLT (cardinalSubarrowWidth D) μ)
    (c : Cocone (cardinalSubarrowDiagram f μ)) (d : Dᵒᵖ)
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    (X.obj d).map α ≫ ((cardinalSubarrowDesc f μ hΩ hWidth c).left.app d).app m =
      ((cardinalSubarrowDesc f μ hΩ hWidth c).left.app d).app n ≫ (c.pt.left.obj d).map α :=
  ((cardinalSubarrowDesc f μ hΩ hWidth c).left.app d).naturality α

theorem cardinalSubarrowDesc_right_inner (μ : Cardinal.{u}) [Fact μ.IsRegular]
    (hΩ : Cardinal.aleph0.{u} < μ) (hWidth : HasCardinalLT (cardinalSubarrowWidth D) μ)
    (c : Cocone (cardinalSubarrowDiagram f μ)) (d : Dᵒᵖ)
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    (Y.obj d).map α ≫ ((cardinalSubarrowDesc f μ hΩ hWidth c).right.app d).app m =
      ((cardinalSubarrowDesc f μ hΩ hWidth c).right.app d).app n ≫ (c.pt.right.obj d).map α :=
  ((cardinalSubarrowDesc f μ hΩ hWidth c).right.app d).naturality α

/-- One original-site cardinal works for every original arrow and every larger regular cardinal. -/
theorem exists_regular_cardinalSubarrowPresentation [Small.{u} D] [LocallySmall.{u} D]
    (lower : Cardinal.{u}) :
    ∃ (μ₀ : Cardinal.{u}) (hReg : Fact μ₀.IsRegular),
      letI : Fact μ₀.IsRegular := hReg
      lower < μ₀ ∧ Cardinal.aleph0.{u} < μ₀ ∧ HasCardinalLT (cardinalSubarrowWidth D) μ₀ ∧
        ∀ (μ : Cardinal.{u}) (hμ : Fact μ.IsRegular),
          letI : Fact μ.IsRegular := hμ
          μ₀ ≤ μ → ∀ {A B : SimplicialPresheaf.{u} D} (g : A ⟶ B),
            Small.{u} (cardinalSubarrowIndex g μ) ∧
                IsCardinalFiltered (cardinalSubarrowIndex g μ) μ ∧
              Nonempty (IsColimit (cardinalSubarrowLeftCocone g μ)) ∧
              Nonempty (IsColimit (cardinalSubarrowRightCocone g μ)) ∧
              Nonempty (IsColimit (cardinalSubarrowCocone g μ)) := by
  let Profile := lower.out ⊕ ((Cardinal.aleph0.{u}).out ⊕ cardinalSubarrowWidth D)
  obtain ⟨μ₀, hμ₀, hAll⟩ := HasCardinalLT.exists_regular_cardinal.{u} Profile
  let : Fact μ₀.IsRegular := ⟨hμ₀⟩
  have hLower : lower < μ₀ := by
    have h := hAll.of_injective (fun x : lower.out => (Sum.inl x : Profile)) Sum.inl_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_out] using h
  have hΩ : Cardinal.aleph0.{u} < μ₀ := by
    have h := hAll.of_injective (fun n : (Cardinal.aleph0.{u}).out =>
        (Sum.inr (Sum.inl n) : Profile))
      (Sum.inr_injective.comp Sum.inl_injective)
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_out] using h
  have hWidth : HasCardinalLT (cardinalSubarrowWidth D) μ₀ :=
    hAll.of_injective (fun a => Sum.inr (Sum.inr a)) (Sum.inr_injective.comp Sum.inr_injective)
  refine ⟨μ₀, inferInstance, hLower, hΩ, hWidth, ?_⟩
  intro μ hμ hle A B g
  let : Fact μ.IsRegular := hμ
  exact cardinalSubarrowIndex_presentation g μ (hΩ.trans_le hle) (hWidth.of_le hle)

end SimplicialPresheaf
