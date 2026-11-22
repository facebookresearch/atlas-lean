/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWeakFiniteSubarrow
public import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveWeakClosure
public import MathlibExt.CategoryTheory.SmallObject.EndpointProfile
public import MathlibExt.CategoryTheory.SmallObject.PresheafIterationCardinality
public import MathlibExt.CategoryTheory.Subfunctor.Cardinality
public import MathlibExt.CategoryTheory.Presentable.BoundedPresheafArrows
public import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Comma.LocallySmall

/-!
# Strict bounded interpolation of original objectwise Kan weak arrows

The construction closes original subdiagrams under every original site map
and all simplex operators. Scalar lifts add finite original supports; the
countable union is proved weak through the actual completed detector.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen
open SSet.KanWeakInterpolation

namespace SimplicialPresheaf.KanWeakInterpolation

variable {D : Type w} [Category.{v} D]
variable {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y)

/-- An original subdiagram of BOTH endpoints and the original arrow,
closed under every original site map as well as every simplex operator. -/
@[ext]
structure Subdiagram where
  /-- The original restricted endpoint pair and arrow at the given original site object. -/
  row (d : Dᵒᵖ) : OriginalSubarrow (f.app d)
  left_site {d e : Dᵒᵖ} (h : d ⟶ e) :
    ((row d).left (f.app d)).image (X.map h) ≤ (row e).left (f.app e)
  right_site {d e : Dᵒᵖ} (h : d ⟶ e) :
    ((row d).right (f.app d)).image (Y.map h) ≤ (row e).right (f.app e)

namespace Subdiagram

/-- The original site map restricted to the recorded source subcomplexes. -/
def leftMap (s : Subdiagram f) {d e : Dᵒᵖ} (h : d ⟶ e) :
    ((s.row d).left (f.app d) : SSet.{u}) ⟶ ((s.row e).left (f.app e) : SSet.{u}) :=
  ((s.row d).left (f.app d)).toImage (X.map h) ≫ SSet.Subcomplex.homOfLE (s.left_site h)

/-- The original site map restricted to the recorded target subcomplexes. -/
def rightMap (s : Subdiagram f) {d e : Dᵒᵖ} (h : d ⟶ e) :
    ((s.row d).right (f.app d) : SSet.{u}) ⟶ ((s.row e).right (f.app e) : SSet.{u}) :=
  ((s.row d).right (f.app d)).toImage (Y.map h) ≫ SSet.Subcomplex.homOfLE (s.right_site h)

@[reassoc (attr := simp)]
theorem leftMap_ι (s : Subdiagram f) {d e : Dᵒᵖ} (h : d ⟶ e) :
    leftMap f s h ≫ ((s.row e).left (f.app e)).ι =
      ((s.row d).left (f.app d)).ι ≫ X.map h := by
  rw [leftMap, Category.assoc, SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toImage_ι]

@[reassoc (attr := simp)]
theorem rightMap_ι (s : Subdiagram f) {d e : Dᵒᵖ} (h : d ⟶ e) :
    rightMap f s h ≫ ((s.row e).right (f.app e)).ι =
      ((s.row d).right (f.app d)).ι ≫ Y.map h := by
  rw [rightMap, Category.assoc, SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toImage_ι]

/-- The actual original source subpresheaf, including every original site operator. -/
def leftFunctor (s : Subdiagram f) : SimplicialPresheaf.{u} D where
  obj d := (s.row d).left (f.app d)
  map h := leftMap f s h
  map_id d := by
    apply (cancel_mono ((s.row d).left (f.app d)).ι).mp
    rw [leftMap_ι, X.map_id, Category.comp_id, Category.id_comp]
  map_comp h k := by
    apply (cancel_mono ((s.row _).left (f.app _)).ι).mp
    rw [leftMap_ι, Category.assoc, leftMap_ι, ← Category.assoc, leftMap_ι,
      X.map_comp, Category.assoc]

/-- The actual original target subpresheaf with its original site operators. -/
def rightFunctor (s : Subdiagram f) : SimplicialPresheaf.{u} D where
  obj d := (s.row d).right (f.app d)
  map h := rightMap f s h
  map_id d := by
    apply (cancel_mono ((s.row d).right (f.app d)).ι).mp
    rw [rightMap_ι, Y.map_id, Category.comp_id, Category.id_comp]
  map_comp h k := by
    apply (cancel_mono ((s.row _).right (f.app _)).ι).mp
    rw [rightMap_ι, Category.assoc, rightMap_ι, ← Category.assoc, rightMap_ι,
      Y.map_comp, Category.assoc]

/-- The original natural transformation restricted to both endpoint subpresheaves. -/
def hom (s : Subdiagram f) : leftFunctor f s ⟶ rightFunctor f s where
  app d := (s.row d).hom (f.app d)
  naturality d e h := by
    apply (cancel_mono ((s.row e).right (f.app e)).ι).mp
    change (leftMap f s h ≫ (s.row e).hom (f.app e)) ≫ ((s.row e).right (f.app e)).ι =
      ((s.row d).hom (f.app d) ≫ rightMap f s h) ≫ ((s.row e).right (f.app e)).ι
    simp only [Category.assoc, OriginalSubarrow.hom_right_ι,
      rightMap_ι, OriginalSubarrow.hom_right_ι_assoc, leftMap_ι_assoc]
    rw [f.naturality h]

/-- The original source subpresheaf inclusion at every original site object. -/
def leftInclusion (s : Subdiagram f) : leftFunctor f s ⟶ X where
  app d := ((s.row d).left (f.app d)).ι
  naturality _d _e h := leftMap_ι f s h

/-- The original target subpresheaf inclusion at every original site object. -/
def rightInclusion (s : Subdiagram f) : rightFunctor f s ⟶ Y where
  app d := ((s.row d).right (f.app d)).ι
  naturality _d _e h := rightMap_ι f s h

/-- The whole original restricted presheaf Arrow. -/
def arrow (s : Subdiagram f) : Arrow (SimplicialPresheaf.{u} D) :=
  Arrow.mk (hom f s)

/-- The whole original endpoint inclusion square into the ambient presheaf Arrow. -/
def inclusion (s : Subdiagram f) : arrow f s ⟶ Arrow.mk f :=
  Arrow.homMk (leftInclusion f s) (rightInclusion f s) (by
    apply NatTrans.ext
    funext d
    exact (OriginalSubarrow.hom_right_ι (f.app d) (s.row d)).symm)

instance : PartialOrder (Subdiagram f) where
  le s t := ∀ d, s.row d ≤ t.row d
  le_refl s d := le_refl _
  le_trans s t v hst htv d := (hst d).trans (htv d)
  le_antisymm s t hst hts := by
    apply Subdiagram.ext
    funext d
    exact le_antisymm (hst d) (hts d)

/-- The whole original inclusion square of nested endpoint subdiagrams. -/
def map {s t : Subdiagram f} (h : s ≤ t) : arrow f s ⟶ arrow f t :=
  Arrow.homMk
    { app d := SSet.Subcomplex.homOfLE (h d).1
      naturality d e g := by
        apply (cancel_mono ((t.row e).left (f.app e)).ι).mp
        change (leftMap f s g ≫ SSet.Subcomplex.homOfLE (h e).1) ≫
            ((t.row e).left (f.app e)).ι =
          (SSet.Subcomplex.homOfLE (h d).1 ≫ leftMap f t g) ≫
            ((t.row e).left (f.app e)).ι
        rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, leftMap_ι,
          Category.assoc, leftMap_ι, ← Category.assoc, SSet.Subcomplex.homOfLE_ι] }
    { app d := SSet.Subcomplex.homOfLE (h d).2
      naturality d e g := by
        apply (cancel_mono ((t.row e).right (f.app e)).ι).mp
        change (rightMap f s g ≫ SSet.Subcomplex.homOfLE (h e).2) ≫
            ((t.row e).right (f.app e)).ι =
          (SSet.Subcomplex.homOfLE (h d).2 ≫ rightMap f t g) ≫
            ((t.row e).right (f.app e)).ι
        rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, rightMap_ι,
          Category.assoc, rightMap_ι, ← Category.assoc, SSet.Subcomplex.homOfLE_ι] }
    (by
      apply NatTrans.ext
      funext d
      exact (OriginalSubarrow.map (f.app d) (h d)).w)

@[reassoc (attr := simp)]
theorem map_inclusion {s t : Subdiagram f} (h : s ≤ t) :
    map f h ≫ inclusion f t = inclusion f s := by
  apply Arrow.hom_ext
  · apply NatTrans.ext
    funext d
    exact SSet.Subcomplex.homOfLE_ι (h d).1
  · apply NatTrans.ext
    funext d
    exact SSet.Subcomplex.homOfLE_ι (h d).2

/-- The raw original range of an incoming square is an original subdiagram. -/
def incomingRange {A B : SimplicialPresheaf.{u} D} {i : A ⟶ B}
    (t : Arrow.mk i ⟶ Arrow.mk f) : Subdiagram f where
  row d :=
    ⟨(SSet.Subcomplex.range (t.left.app d), SSet.Subcomplex.range (t.right.app d)), by
      rw [← SSet.Subcomplex.range_comp]
      have hw : t.left.app d ≫ f.app d = i.app d ≫ t.right.app d := congrArg (fun q => q.app d) t.w
      rw [hw]
      rw [SSet.Subcomplex.range_comp]
      exact SSet.Subcomplex.image_le_range _ _⟩
  left_site h := by
    change (SSet.Subcomplex.range (t.left.app _)).image (X.map h) ≤
        SSet.Subcomplex.range (t.left.app _)
    have ht : A.map h ≫ t.left.app _ = t.left.app _ ≫ X.map h := t.left.naturality h
    rw [← SSet.Subcomplex.range_comp, ← ht, SSet.Subcomplex.range_comp]
    exact SSet.Subcomplex.image_le_range _ _
  right_site h := by
    change (SSet.Subcomplex.range (t.right.app _)).image (Y.map h) ≤
        SSet.Subcomplex.range (t.right.app _)
    have ht : B.map h ≫ t.right.app _ = t.right.app _ ≫ Y.map h := t.right.naturality h
    rw [← SSet.Subcomplex.range_comp, ← ht, SSet.Subcomplex.range_comp]
    exact SSet.Subcomplex.image_le_range _ _

end Subdiagram


namespace Subdiagram

private theorem image_sup_le {A B : SSet.{u}} (S T : A.Subcomplex) (g : A ⟶ B)
    (V : B.Subcomplex) (hS : S.image g ≤ V) (hT : T.image g ≤ V) :
    (S ⊔ T).image g ≤ V := by
  rw [SSet.Subcomplex.image_le_iff]
  exact sup_le ((SSet.Subcomplex.image_le_iff S g V).mp hS)
    ((SSet.Subcomplex.image_le_iff T g V).mp hT)

/-- The two original endpoint unions, retaining all original site and simplex operators. -/
@[no_expose]
def union (s t : Subdiagram f) : Subdiagram f where
  row d :=
    ⟨((s.row d).left (f.app d) ⊔ (t.row d).left (f.app d),
      (s.row d).right (f.app d) ⊔ (t.row d).right (f.app d)),
      image_sup_le _ _ (f.app d) _
        ((s.row d).property.trans le_sup_left) ((t.row d).property.trans le_sup_right)⟩
  left_site h := image_sup_le _ _ (X.map h) _
    ((s.left_site h).trans le_sup_left) ((t.left_site h).trans le_sup_right)
  right_site h := image_sup_le _ _ (Y.map h) _
    ((s.right_site h).trans le_sup_left) ((t.right_site h).trans le_sup_right)

theorem le_union_left (s t : Subdiagram f) : s ≤ union f s t :=
  fun _ => ⟨le_sup_left, le_sup_left⟩

theorem le_union_right (s t : Subdiagram f) : t ≤ union f s t :=
  fun _ => ⟨le_sup_right, le_sup_right⟩

/-- The original indexed union of endpoint subdiagrams and their restricted arrow. -/
def indexedUnion {I : Type u} (s : I → Subdiagram f) : Subdiagram f where
  row d :=
    ⟨(⨆ i, ((s i).row d).left (f.app d), ⨆ i, ((s i).row d).right (f.app d)), by
      change (⨆ i, ((s i).row d).left (f.app d)).image (f.app d) ≤
        ⨆ i, ((s i).row d).right (f.app d)
      rw [SSet.Subcomplex.image_iSup]
      exact iSup_le (fun i => ((s i).row d).property.trans
        (le_iSup (fun j => ((s j).row d).right (f.app d)) i))⟩
  left_site h := by
    rename_i d e
    change (⨆ i, ((s i).row d).left (f.app d)).image (X.map h) ≤
      ⨆ i, ((s i).row e).left (f.app e)
    rw [SSet.Subcomplex.image_iSup]
    exact iSup_le (fun i => ((s i).left_site h).trans
      (le_iSup (fun j => ((s j).row e).left (f.app e)) i))
  right_site h := by
    rename_i d e
    change (⨆ i, ((s i).row d).right (f.app d)).image (Y.map h) ≤
      ⨆ i, ((s i).row e).right (f.app e)
    rw [SSet.Subcomplex.image_iSup]
    exact iSup_le (fun i => ((s i).right_site h).trans
      (le_iSup (fun j => ((s j).row e).right (f.app e)) i))

theorem le_indexedUnion {I : Type u} (s : I → Subdiagram f) (i : I) :
    s i ≤ indexedUnion f s := by
  intro d
  exact ⟨le_iSup (fun j => ((s j).row d).left (f.app d)) i,
    le_iSup (fun j => ((s j).row d).right (f.app d)) i⟩

/-- Close finite ORIGINAL row additions under EVERY original site map.
Their simplex operators are retained by their native Subcomplexes. -/
def siteClosure {I : Type u} (site : I → Dᵒᵖ)
    (pieces : ∀ p, FiniteSubarrow (f.app (site p))) : Subdiagram f where
  row d :=
    ⟨(⨆ p, ⨆ h : site p ⟶ d, ((pieces p).left (f.app (site p))).image (X.map h),
      ⨆ p, ⨆ h : site p ⟶ d, ((pieces p).right (f.app (site p))).image (Y.map h)), by
      change (⨆ p, ⨆ h : site p ⟶ d,
          ((pieces p).left (f.app (site p))).image (X.map h)).image (f.app d) ≤
        ⨆ p, ⨆ h : site p ⟶ d, ((pieces p).right (f.app (site p))).image (Y.map h)
      rw [SSet.Subcomplex.image_iSup]
      apply iSup_le
      intro p
      rw [SSet.Subcomplex.image_iSup]
      apply iSup_le
      intro h
      rw [← SSet.Subcomplex.image_comp, f.naturality h, SSet.Subcomplex.image_comp]
      exact (SSet.Subcomplex.image_monotone (Y.map h) ((pieces p).image_le _)).trans
        (le_iSup_of_le p (le_iSup
          (fun g : site p ⟶ d => ((pieces p).right _).image (Y.map g)) h))⟩
  left_site g := by
    rename_i d e
    change (⨆ p, ⨆ h : site p ⟶ d, ((pieces p).left _).image (X.map h)).image (X.map g) ≤
      ⨆ p, ⨆ h : site p ⟶ e, ((pieces p).left _).image (X.map h)
    rw [SSet.Subcomplex.image_iSup]
    apply iSup_le
    intro p
    rw [SSet.Subcomplex.image_iSup]
    apply iSup_le
    intro h
    rw [← SSet.Subcomplex.image_comp, ← X.map_comp]
    exact le_iSup_of_le p (le_iSup
      (fun k : site p ⟶ e => ((pieces p).left _).image (X.map k)) (h ≫ g))
  right_site g := by
    rename_i d e
    change (⨆ p, ⨆ h : site p ⟶ d, ((pieces p).right _).image (Y.map h)).image (Y.map g) ≤
      ⨆ p, ⨆ h : site p ⟶ e, ((pieces p).right _).image (Y.map h)
    rw [SSet.Subcomplex.image_iSup]
    apply iSup_le
    intro p
    rw [SSet.Subcomplex.image_iSup]
    apply iSup_le
    intro h
    rw [← SSet.Subcomplex.image_comp, ← Y.map_comp]
    exact le_iSup_of_le p (le_iSup
      (fun k : site p ⟶ e => ((pieces p).right _).image (Y.map k)) (h ≫ g))

theorem piece_le_siteClosure {I : Type u} (site : I → Dᵒᵖ)
    (pieces : ∀ p, FiniteSubarrow (f.app (site p))) (p : I) :
    OriginalSubarrow.ofFinite (f.app (site p)) (pieces p) ≤
      (siteClosure f site pieces).row (site p) := by
  constructor
  · change (pieces p).left _ ≤ ⨆ q, ⨆ g : site q ⟶ site p, ((pieces q).left _).image (X.map g)
    have h : ((pieces p).left _).image (X.map (𝟙 (site p))) ≤
        ⨆ q, ⨆ g : site q ⟶ site p, ((pieces q).left _).image (X.map g) :=
      le_iSup_of_le p (le_iSup
      (fun g : site p ⟶ site p => ((pieces p).left _).image (X.map g)) (𝟙 (site p)))
    simpa only [X.map_id, SSet.Subcomplex.image_id] using h
  · change (pieces p).right _ ≤ ⨆ q, ⨆ g : site q ⟶ site p, ((pieces q).right _).image (Y.map g)
    have h : ((pieces p).right _).image (Y.map (𝟙 (site p))) ≤
        ⨆ q, ⨆ g : site q ⟶ site p, ((pieces q).right _).image (Y.map g) :=
      le_iSup_of_le p (le_iSup
      (fun g : site p ⟶ site p => ((pieces p).right _).image (Y.map g)) (𝟙 (site p)))
    simpa only [Y.map_id, SSet.Subcomplex.image_id] using h

end Subdiagram


attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

/-- A literal completed-detector boundary problem at an original site object. -/
structure BoundaryProblem (s : Subdiagram f) where
  /-- The original site object at which this completed-detector problem is posed. -/
  site : Dᵒᵖ
  /-- The actual boundary dimension, including dimension zero. -/
  dimension : ℕ
  /-- The entire original boundary map into the chosen completed mapping-path pullback. -/
  top : (SSet.boundary.{u} dimension : SSet.{u}) ⟶
    SSet.mappingPathSpace (completion.map ((s.row site).hom (f.app site)))
  /-- The original simplex map into the same completed target endpoint. -/
  bottom : (Δ[dimension] : SSet.{u}) ⟶ completion.obj ((s.row site).right (f.app site))
  square : CommSq top (SSet.boundary.{u} dimension).ι
    (SSet.mappingPathTarget (completion.map ((s.row site).hom (f.app site)))) bottom

section Normalized

variable {C : Type u} [SmallCategory C]

private abbrev FixedPoints (i : Arrow (SimplicialPresheaf.{u} C)) : Type u :=
  (Cᵒᵖ ⊕ (Σ d e : Cᵒᵖ, d ⟶ e)) ⊕
    ((Σ d : Cᵒᵖ, (i.left.obj d).Elements) ⊕ (Σ d : Cᵒᵖ, (i.right.obj d).Elements))

private structure Envelope (i : Arrow (SimplicialPresheaf.{u} C)) where
  ξ : Cardinal.{u}
  infinite : Cardinal.aleph0.{u} ≤ ξ
  family : Cardinal.mk (Shrink.{u} SSet.modelCategoryQuillen.J.toSet) ≤ ξ
  generator_left : ∀ j : SSet.modelCategoryQuillen.J.{u}.toSet, Cardinal.mk j.val.left.Elements ≤ ξ
  generator_right : ∀ j : SSet.modelCategoryQuillen.J.{u}.toSet,
      Cardinal.mk j.val.right.Elements ≤ ξ
  fixed : Cardinal.mk (FixedPoints i) ≤ ξ
  power : ((2 : Cardinal.{u}) ^ ξ) ^ ξ = (2 : Cardinal.{u}) ^ ξ
  strict : ξ < 2 ^ ξ

private theorem envelope_nonempty (i : Arrow (SimplicialPresheaf.{u} C)) :
    Nonempty (Envelope i) := by
  obtain ⟨ξ, hω, _hκ, _hμ, hJ, hA, hB, hfixed, hpower, hstrict⟩ :=
    CategoryTheory.SmallObject.exists_original_fixed_total_point_profile
      SSet.modelCategoryQuillen.J.{u} Cardinal.aleph0.{u} (𝟭 SSet.{u})
      Cardinal.aleph0.{u} (FixedPoints i)
  exact ⟨⟨ξ, hω, hJ, hA, hB, hfixed, hpower, hstrict⟩⟩

private def envelope (i : Arrow (SimplicialPresheaf.{u} C)) : Envelope i :=
  Classical.choice (envelope_nonempty i)

private abbrev Envelope.γ {i : Arrow (SimplicialPresheaf.{u} C)} (e : Envelope i) :
    Cardinal.{u} := 2 ^ e.ξ

private theorem Envelope.infinite_γ {i : Arrow (SimplicialPresheaf.{u} C)} (e : Envelope i) :
    Cardinal.aleph0.{u} ≤ e.γ := e.infinite.trans e.strict.le

private theorem Envelope.site_bound {i : Arrow (SimplicialPresheaf.{u} C)} (e : Envelope i) :
    Cardinal.mk Cᵒᵖ ≤ e.ξ := by
  let inc : Cᵒᵖ → FixedPoints i := fun d => Sum.inl (Sum.inl d)
  exact (Cardinal.mk_le_of_injective (f := inc)
      (Sum.inl_injective.comp Sum.inl_injective)).trans e.fixed

private theorem Envelope.operator_bound {i : Arrow (SimplicialPresheaf.{u} C)}
    (e : Envelope i) (d c : Cᵒᵖ) : Cardinal.mk (d ⟶ c) ≤ e.ξ := by
  let inc : (d ⟶ c) → FixedPoints i := fun h => Sum.inl (Sum.inr ⟨d, c, h⟩)
  have hi : Function.Injective inc := by
    intro h k he
    have hp := Sum.inr_injective (Sum.inl_injective he)
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hp
  exact (Cardinal.mk_le_of_injective hi).trans e.fixed

private theorem Envelope.incoming_left_bound {i : Arrow (SimplicialPresheaf.{u} C)}
    (e : Envelope i) (d : Cᵒᵖ) : Cardinal.mk (i.left.obj d).Elements ≤ e.ξ := by
  let inc : (i.left.obj d).Elements → FixedPoints i := fun q => Sum.inr (Sum.inl ⟨d, q⟩)
  have hi : Function.Injective inc := by
    intro h k he
    have hp := Sum.inl_injective (Sum.inr_injective he)
    exact sigma_mk_injective (β := fun c : Cᵒᵖ => (i.left.obj c).Elements) hp
  exact (Cardinal.mk_le_of_injective hi).trans e.fixed

private theorem Envelope.incoming_right_bound {i : Arrow (SimplicialPresheaf.{u} C)}
    (e : Envelope i) (d : Cᵒᵖ) : Cardinal.mk (i.right.obj d).Elements ≤ e.ξ := by
  let inc : (i.right.obj d).Elements → FixedPoints i := fun q => Sum.inr (Sum.inr ⟨d, q⟩)
  have hi : Function.Injective inc := by
    intro h k he
    have hp := Sum.inr_injective (Sum.inr_injective he)
    exact sigma_mk_injective (β := fun c : Cᵒᵖ => (i.right.obj c).Elements) hp
  exact (Cardinal.mk_le_of_injective hi).trans e.fixed

private theorem Envelope.completion_bound {i : Arrow (SimplicialPresheaf.{u} C)}
    (e : Envelope i) (T : SSet.{u}) (hT : Cardinal.mk T.Elements ≤ e.γ) :
    Cardinal.mk (completion.obj T).Elements ≤ e.γ :=
  CategoryTheory.SmallObject.obj_terminal_mk_elements_le_of_presheaf_equivalence
    SSet.modelCategoryQuillen.J.{u} Cardinal.aleph0.{u} (𝟭 SSet.{u})
    e.ξ e.infinite e.infinite e.family e.generator_left e.generator_right T hT

private theorem Envelope.finite_hom_bound {i : Arrow (SimplicialPresheaf.{u} C)}
    (e : Envelope i) (A T : SSet.{u}) [SSet.Finite A]
    (hT : Cardinal.mk T.Elements ≤ e.γ) :
    Cardinal.mk (A ⟶ completion.obj T) ≤ e.γ := by
  have hγ0 : e.γ ≠ 0 := ne_of_gt ((show 0 ≤ e.ξ from zero_le).trans_lt e.strict)
  calc
    Cardinal.mk (A ⟶ completion.obj T) ≤
        Cardinal.mk (completion.obj T).Elements ^ Cardinal.mk A.Elements :=
      CategoryTheory.mk_hom_le_elements_power A (completion.obj T)
    _ ≤ e.γ ^ Cardinal.mk A.Elements := Cardinal.power_le_power_right (e.completion_bound T hT)
    _ ≤ e.γ ^ e.ξ := Cardinal.power_le_power_left hγ0
        ((finiteElements_le_aleph0 A).trans e.infinite)
    _ = e.γ := e.power

end Normalized


private theorem range_elements_le {A B : SSet.{u}} (g : A ⟶ B) :
    Cardinal.mk (SSet.Subcomplex.range g : SSet.{u}).Elements ≤ Cardinal.mk A.Elements := by
  let cover : A.Elements → (SSet.Subcomplex.range g : SSet.{u}).Elements :=
    (SSet.Subcomplex.toRange g).mapElements.obj
  have hcover : Function.Surjective cover := by
    intro q
    obtain ⟨x, hx⟩ := q.val.property
    refine ⟨CategoryTheory.Functor.elementsMk A q.obj x, ?_⟩
    apply CategoryTheory.Functor.Elements.ext
        (cover (CategoryTheory.Functor.elementsMk A q.obj x)) q rfl
    simp only [eqToHom_refl, CategoryTheory.Functor.map_id, types_id_apply]
    change (SSet.Subcomplex.toRange g).app q.obj x = q.val
    exact Subtype.ext hx
  exact Cardinal.mk_le_of_surjective hcover

private theorem elements_union_le {Z : SSet.{u}} (S T : Z.Subcomplex)
    {γ : Cardinal.{u}} (hγ : Cardinal.aleph0.{u} ≤ γ)
    (hS : Cardinal.mk (S : SSet.{u}).Elements ≤ γ)
    (hT : Cardinal.mk (T : SSet.{u}).Elements ≤ γ) :
    Cardinal.mk (S ⊔ T : Z.Subcomplex).toSSet.Elements ≤ γ := by
  let F : ULift.{u} Bool → Z.Subcomplex := fun b => if b.down then S else T
  have hI : Cardinal.mk (ULift.{u} Bool) ≤ γ := Cardinal.mk_lt_aleph0.le.trans hγ
  have hF : ∀ b, Cardinal.mk (F b : SSet.{u}).Elements ≤ γ := by
    intro b
    cases hb : b.down
    · simpa only [F, hb, Bool.false_eq_true, ite_false] using hT
    · simpa only [F, hb, ite_true] using hS
  have h := CategoryTheory.Subfunctor.mk_elements_iSup_le_of_le F hγ hI hF
  simpa only [F, iSup_ulift, iSup_bool_eq, ite_true, Bool.false_eq_true, ite_false] using h

section Normalized

variable {C : Type u} [SmallCategory C]
variable {U V : SimplicialPresheaf.{u} C} (g : U ⟶ V)

/-- Bounds on literal scalar row Elements, with no conclusion about weakness. -/
private def RowBounded (s : Subdiagram g) (γ : Cardinal.{u}) : Prop :=
  ∀ d, Cardinal.mk ((s.row d).left (g.app d) : SSet.{u}).Elements ≤ γ ∧
    Cardinal.mk ((s.row d).right (g.app d) : SSet.{u}).Elements ≤ γ

private theorem union_rowBounded {s t : Subdiagram g} {γ : Cardinal.{u}}
    (hγ : Cardinal.aleph0.{u} ≤ γ) (hs : RowBounded g s γ) (ht : RowBounded g t γ) :
    RowBounded g (Subdiagram.union g s t) γ := by
  intro d
  constructor
  · exact elements_union_le _ _ hγ (hs d).1 (ht d).1
  · exact elements_union_le _ _ hγ (hs d).2 (ht d).2

private theorem indexedUnion_rowBounded {I : Type u} (s : I → Subdiagram g)
    {γ : Cardinal.{u}} (hγ : Cardinal.aleph0.{u} ≤ γ)
    (hI : Cardinal.mk I ≤ γ) (hs : ∀ p, RowBounded g (s p) γ) :
    RowBounded g (Subdiagram.indexedUnion g s) γ := by
  intro d
  constructor
  · exact CategoryTheory.Subfunctor.mk_elements_iSup_le_of_le
      (fun p => (s p |>.row d).left (g.app d)) hγ hI (fun p => (hs p d).1)
  · exact CategoryTheory.Subfunctor.mk_elements_iSup_le_of_le
      (fun p => (s p |>.row d).right (g.app d)) hγ hI (fun p => (hs p d).2)

private theorem finite_site_images_bound {i : Arrow (SimplicialPresheaf.{u} C)} (e : Envelope i)
    (Z : SimplicialPresheaf.{u} C) {I : Type u} (site : I → Cᵒᵖ)
    (pieces : ∀ p, (Z.obj (site p)).Subcomplex) [∀ p, SSet.Finite (pieces p)]
    (hI : Cardinal.mk I ≤ e.γ) (d : Cᵒᵖ) :
    Cardinal.mk ((⨆ p, ⨆ h : site p ⟶ d, (pieces p).image (Z.map h) :
      (Z.obj d).Subcomplex) : SSet.{u}).Elements ≤ e.γ := by
  let K : Type u := Σ p : I, site p ⟶ d
  have hK : Cardinal.mk K ≤ e.γ := by
    rw [Cardinal.mk_sigma]
    calc
      Cardinal.sum (fun p : I => Cardinal.mk (site p ⟶ d)) ≤ Cardinal.sum (fun _ : I => e.γ) :=
        Cardinal.sum_le_sum _ _ (fun p => (e.operator_bound (site p) d).trans e.strict.le)
      _ = Cardinal.mk I * e.γ := Cardinal.sum_const' _ _
      _ ≤ e.γ * e.γ := mul_le_mul' hI le_rfl
      _ = e.γ := Cardinal.mul_eq_self e.infinite_γ
  let F : K → (Z.obj d).Subcomplex := fun z => (pieces z.1).image (Z.map z.2)
  have hF : ∀ k, Cardinal.mk (F k : SSet.{u}).Elements ≤ e.γ := by
    intro k
    have : SSet.Finite (F k) := by
      dsimp only [F]
      rw [SSet.Subcomplex.image_eq_range]
      infer_instance
    exact (finiteElements_le_aleph0 _).trans e.infinite_γ
  have h := CategoryTheory.Subfunctor.mk_elements_iSup_le_of_le F e.infinite_γ hK hF
  simpa only [F, K, iSup_sigma] using h

private theorem closure_rowBounded {i : Arrow (SimplicialPresheaf.{u} C)} (e : Envelope i)
    {I : Type u} (site : I → Cᵒᵖ) (pieces : ∀ p, FiniteSubarrow (g.app (site p)))
    (hI : Cardinal.mk I ≤ e.γ) :
    RowBounded g (Subdiagram.siteClosure g site pieces) e.γ := by
  intro d
  constructor
  · exact finite_site_images_bound e U site (fun p => (pieces p).left _) hI d
  · exact finite_site_images_bound e V site (fun p => (pieces p).right _) hI d

private theorem incomingRange_rowBounded {A B : SimplicialPresheaf.{u} C} {h : A ⟶ B}
    (e : Envelope (Arrow.mk h)) (t : Arrow.mk h ⟶ Arrow.mk g) :
    RowBounded g (Subdiagram.incomingRange g t) e.γ := by
  intro d
  constructor
  · exact (range_elements_le (t.left.app d)).trans ((e.incoming_left_bound d).trans e.strict.le)
  · exact (range_elements_le (t.right.app d)).trans ((e.incoming_right_bound d).trans e.strict.le)

end Normalized


section Normalized

variable {C : Type u} [SmallCategory C]
variable {U V : SimplicialPresheaf.{u} C} (g : U ⟶ V)

private abbrev ProblemColumns (s : Subdiagram g) (d : Cᵒᵖ) (n : ℕ) : Type u :=
  ((SSet.boundary.{u} n : SSet.{u}) ⟶ completion.obj ((s.row d).left (g.app d))) ×
    ((((Δ[1] : SSet.{u}) ⊗ (SSet.boundary.{u} n : SSet.{u})) ⟶
      completion.obj ((s.row d).right (g.app d))) ×
      ((Δ[n] : SSet.{u}) ⟶ completion.obj ((s.row d).right (g.app d))))

private abbrev ProblemEncoding (s : Subdiagram g) : Type u :=
  Σ d : Cᵒᵖ, Σ n : ULift.{u} ℕ, ProblemColumns g s d n.down

private def encodeProblem (s : Subdiagram g) (p : BoundaryProblem g s) : ProblemEncoding g s :=
  ⟨p.site, ULift.up p.dimension,
    (p.top ≫ SSet.mappingPathRetract (completion.map ((s.row p.site).hom (g.app p.site))),
      (MonoidalClosed.uncurry
        (p.top ≫
            SSet.mappingPathEval (completion.map
              ((s.row p.site).hom (g.app p.site)))), p.bottom))⟩

private theorem encodeProblem_injective (s : Subdiagram g) :
    Function.Injective (encodeProblem g s) := by
  intro p q he
  rcases p with ⟨d, n, top, bottom, square⟩
  rcases q with ⟨d', n', top', bottom', square'⟩
  dsimp only [encodeProblem] at he
  have hd : d = d' := congrArg Sigma.fst he
  subst d'
  have hdim := sigma_mk_injective
    (β := fun c : Cᵒᵖ => Σ m : ULift.{u} ℕ, ProblemColumns g s c m.down) he
  have hn : n = n' := congrArg ULift.down (congrArg Sigma.fst hdim)
  subst n'
  have hdata := sigma_mk_injective
    (β := fun m : ULift.{u} ℕ => ProblemColumns g s d m.down) hdim
  have hleft := congrArg Prod.fst hdata
  have hpath := congrArg (fun z => z.2.1) hdata
  have hbottom := congrArg (fun z => z.2.2) hdata
  have ht : top = top' := by
    apply pullback.hom_ext
    · change top ≫ SSet.mappingPathRetract (completion.map ((s.row d).hom (g.app d))) =
        top' ≫ SSet.mappingPathRetract (completion.map ((s.row d).hom (g.app d)))
      exact hleft
    · change top ≫ SSet.mappingPathEval (completion.map ((s.row d).hom (g.app d))) =
        top' ≫ SSet.mappingPathEval (completion.map ((s.row d).hom (g.app d)))
      simpa only [MonoidalClosed.curry_uncurry] using congrArg MonoidalClosed.curry hpath
  subst top'
  change bottom = bottom' at hbottom
  subst bottom'
  rfl

private theorem problemColumns_bound {i : Arrow (SimplicialPresheaf.{u} C)} (e : Envelope i)
    (s : Subdiagram g) (hs : RowBounded g s e.γ) (d : Cᵒᵖ) (n : ℕ) :
    Cardinal.mk (ProblemColumns g s d n) ≤ e.γ := by
  have h₁ := e.finite_hom_bound (SSet.boundary.{u} n : SSet.{u})
    ((s.row d).left (g.app d)) (hs d).1
  have h₂ := e.finite_hom_bound
    ((Δ[1] : SSet.{u}) ⊗ (SSet.boundary.{u} n : SSet.{u}))
    ((s.row d).right (g.app d)) (hs d).2
  have h₃ := e.finite_hom_bound (Δ[n] : SSet.{u})
    ((s.row d).right (g.app d)) (hs d).2
  dsimp only [ProblemColumns]
  rw [Cardinal.mk_prod, Cardinal.mk_prod]
  simp only [Cardinal.lift_id]
  exact Cardinal.mul_le_of_le e.infinite_γ h₁
    (Cardinal.mul_le_of_le e.infinite_γ h₂ h₃)

/-- All original site objects and ALL boundary degrees are counted.
The full original top is recovered from its retract and uncurried path maps. -/
private theorem boundaryProblems_bound {i : Arrow (SimplicialPresheaf.{u} C)} (e : Envelope i)
    (s : Subdiagram g) (hs : RowBounded g s e.γ) :
    Cardinal.mk (BoundaryProblem g s) ≤ e.γ := by
  have hdim (d : Cᵒᵖ) :
      Cardinal.mk (Σ n : ULift.{u} ℕ, ProblemColumns g s d n.down) ≤ e.γ := by
    rw [Cardinal.mk_sigma]
    calc
      Cardinal.sum (fun n : ULift.{u} ℕ => Cardinal.mk (ProblemColumns g s d n.down)) ≤
          Cardinal.sum (fun _ : ULift.{u} ℕ => e.γ) :=
        Cardinal.sum_le_sum _ _ (fun n => problemColumns_bound g e s hs d n.down)
      _ = Cardinal.mk (ULift.{u} ℕ) * e.γ := Cardinal.sum_const' _ _
      _ ≤ e.γ := Cardinal.mul_le_of_le e.infinite_γ
        (Cardinal.mk_le_aleph0.trans e.infinite_γ) le_rfl
  have hencoding : Cardinal.mk (ProblemEncoding g s) ≤ e.γ := by
    dsimp only [ProblemEncoding]
    rw [Cardinal.mk_sigma]
    calc
      Cardinal.sum (fun d : Cᵒᵖ =>
          Cardinal.mk (Σ n : ULift.{u} ℕ, ProblemColumns g s d n.down)) ≤
          Cardinal.sum (fun _ : Cᵒᵖ => e.γ) := Cardinal.sum_le_sum _ _ hdim
      _ = Cardinal.mk Cᵒᵖ * e.γ := Cardinal.sum_const' _ _
      _ ≤ e.γ := Cardinal.mul_le_of_le e.infinite_γ (e.site_bound.trans e.strict.le) le_rfl
  exact (Cardinal.mk_le_of_injective (encodeProblem_injective g s)).trans hencoding

end Normalized


section Normalized

variable {C : Type u} [SmallCategory C]
variable {U V : SimplicialPresheaf.{u} C} (g : U ⟶ V)
    (hg : ∀ d, SSet.realizationWeakEquivalences (g.app d))

private def selectedAddition (s : Subdiagram g) (p : BoundaryProblem g s) :
    FiniteSubarrow (g.app p.site) :=
  (OriginalSubarrow.existsFiniteAdditionLift (g.app p.site) (hg p.site) (s.row p.site)
    (SSet.boundary.{u} p.dimension).ι p.top p.bottom p.square).choose

private def selectedLift (s : Subdiagram g) (p : BoundaryProblem g s) :
    (Δ[p.dimension] : SSet.{u}) ⟶ SSet.mappingPathSpace
      (completion.map ((OriginalSubarrow.enlarge (g.app p.site) (s.row p.site)
        (selectedAddition g hg s p)).hom (g.app p.site))) :=
  (OriginalSubarrow.existsFiniteAdditionLift (g.app p.site) (hg p.site) (s.row p.site)
    (SSet.boundary.{u} p.dimension).ι p.top p.bottom p.square).choose_spec.choose

private theorem selectedLift_fac (s : Subdiagram g) (p : BoundaryProblem g s) :
    (SSet.boundary.{u} p.dimension).ι ≫ selectedLift g hg s p =
      p.top ≫ pathMap (OriginalSubarrow.completedMap (g.app p.site)
        (OriginalSubarrow.le_enlarge (g.app p.site) (s.row p.site) (selectedAddition g hg s p))) ∧
    selectedLift g hg s p ≫ SSet.mappingPathTarget
        (completion.map ((OriginalSubarrow.enlarge (g.app p.site) (s.row p.site)
          (selectedAddition g hg s p)).hom (g.app p.site))) =
      p.bottom ≫ (OriginalSubarrow.completedMap (g.app p.site)
        (OriginalSubarrow.le_enlarge (g.app p.site) (s.row p.site)
            (selectedAddition g hg s p))).right :=
  (OriginalSubarrow.existsFiniteAdditionLift (g.app p.site) (hg p.site) (s.row p.site)
    (SSet.boundary.{u} p.dimension).ι p.top p.bottom p.square).choose_spec.choose_spec

private def round (s : Subdiagram g) : Subdiagram g :=
  Subdiagram.union g s
    (Subdiagram.siteClosure g (fun p : BoundaryProblem g s => p.site) (selectedAddition g hg s))

private theorem le_round (s : Subdiagram g) : s ≤ round g hg s :=
  Subdiagram.le_union_left _ _ _

private theorem addition_le_round (s : Subdiagram g) (p : BoundaryProblem g s) :
    OriginalSubarrow.enlarge (g.app p.site) (s.row p.site) (selectedAddition g hg s p) ≤
      (round g hg s).row p.site := by
  have hs := le_round g hg s p.site
  have hj := (Subdiagram.piece_le_siteClosure g
      (fun q : BoundaryProblem g s => q.site) (selectedAddition g hg s) p).trans
    (Subdiagram.le_union_right g s
      (Subdiagram.siteClosure g (fun q : BoundaryProblem g s => q.site)
          (selectedAddition g hg s)) p.site)
  exact ⟨sup_le hs.1 hj.1, sup_le hs.2 hj.2⟩

private def roundLift (s : Subdiagram g) (p : BoundaryProblem g s) :
    (Δ[p.dimension] : SSet.{u}) ⟶ SSet.mappingPathSpace
      (completion.map (((round g hg s).row p.site).hom (g.app p.site))) :=
  selectedLift g hg s p ≫ pathMap (OriginalSubarrow.completedMap (g.app p.site)
    (addition_le_round g hg s p))

private theorem roundLift_fac (s : Subdiagram g) (p : BoundaryProblem g s) :
    (SSet.boundary.{u} p.dimension).ι ≫ roundLift g hg s p =
      p.top ≫ pathMap (OriginalSubarrow.completedMap (g.app p.site) (le_round g hg s p.site)) ∧
    roundLift g hg s p ≫ SSet.mappingPathTarget
        (completion.map (((round g hg s).row p.site).hom (g.app p.site))) =
      p.bottom ≫ (OriginalSubarrow.completedMap (g.app p.site) (le_round g hg s p.site)).right := by
  have hf := selectedLift_fac g hg s p
  constructor
  · dsimp only [roundLift]
    rw [← Category.assoc, hf.1, Category.assoc, ← pathMap_comp, OriginalSubarrow.completedMap_comp]
  · dsimp only [roundLift]
    rw [Category.assoc, pathMap_target, ← Category.assoc, hf.2, Category.assoc]
    have hc := congrArg Arrow.Hom.right (OriginalSubarrow.completedMap_comp (g.app p.site)
      (OriginalSubarrow.le_enlarge (g.app p.site) (s.row p.site) (selectedAddition g hg s p))
      (addition_le_round g hg s p))
    exact congrArg (fun v => p.bottom ≫ v) hc

private theorem round_rowBounded {i : Arrow (SimplicialPresheaf.{u} C)} (e : Envelope i)
    (s : Subdiagram g) (hs : RowBounded g s e.γ) :
    RowBounded g (round g hg s) e.γ :=
  union_rowBounded g e.infinite_γ hs
    (closure_rowBounded g e (fun p : BoundaryProblem g s => p.site)
      (selectedAddition g hg s) (boundaryProblems_bound g e s hs))

private def stage (s : Subdiagram g) : ℕ → Subdiagram g :=
  Nat.rec s (fun _ t => round g hg t)

private theorem stage_le_succ (s : Subdiagram g) (n : ℕ) :
    stage g hg s n ≤ stage g hg s (n + 1) :=
  le_round g hg (stage g hg s n)

private theorem stage_mono (s : Subdiagram g) : Monotone (stage g hg s) := by
  intro n m hnm
  induction hnm with
  | refl => exact le_rfl
  | @step m h ih => exact ih.trans (stage_le_succ g hg s m)

private theorem stage_rowBounded {i : Arrow (SimplicialPresheaf.{u} C)} (e : Envelope i)
    (s : Subdiagram g) (hs : RowBounded g s e.γ) (n : ℕ) :
    RowBounded g (stage g hg s n) e.γ := by
  induction n with
  | zero => exact hs
  | succ n ih => exact round_rowBounded g hg e _ ih

private def limitSubdiagram (s : Subdiagram g) : Subdiagram g :=
  Subdiagram.indexedUnion g (fun n : ULift.{u} ℕ => stage g hg s n.down)

private theorem stage_le_limit (s : Subdiagram g) (n : ℕ) :
    stage g hg s n ≤ limitSubdiagram g hg s :=
  Subdiagram.le_indexedUnion g (fun n : ULift.{u} ℕ => stage g hg s n.down) (ULift.up n)

private theorem limit_rowBounded {i : Arrow (SimplicialPresheaf.{u} C)} (e : Envelope i)
    (s : Subdiagram g) (hs : RowBounded g s e.γ) :
    RowBounded g (limitSubdiagram g hg s) e.γ :=
  indexedUnion_rowBounded g (fun n : ULift.{u} ℕ => stage g hg s n.down) e.infinite_γ
    (Cardinal.mk_le_aleph0.trans e.infinite_γ) (fun n => stage_rowBounded g hg e s hs n.down)

end Normalized


section Normalized

variable {C : Type u} [SmallCategory C]
variable {U V : SimplicialPresheaf.{u} C} (g : U ⟶ V)
    (hg : ∀ d, SSet.realizationWeakEquivalences (g.app d))

private abbrev StageIndex := ULift.{u} ℕ

private instance stageIndex_filtered : IsFiltered StageIndex.{u} := inferInstance

private def stageLeftDiagram (s : Subdiagram g) (d : Cᵒᵖ) : StageIndex.{u} ⥤ SSet.{u} where
  obj n := ((stage g hg s n.down).row d).left (g.app d)
  map h := SSet.Subcomplex.homOfLE ((stage_mono g hg s (leOfHom (X := StageIndex.{u}) h)) d).1
  map_id _n := SSet.Subcomplex.homOfLE_refl _
  map_comp _h _k := rfl

private def stageRightDiagram (s : Subdiagram g) (d : Cᵒᵖ) : StageIndex.{u} ⥤ SSet.{u} where
  obj n := ((stage g hg s n.down).row d).right (g.app d)
  map h := SSet.Subcomplex.homOfLE ((stage_mono g hg s (leOfHom (X := StageIndex.{u}) h)) d).2
  map_id _n := SSet.Subcomplex.homOfLE_refl _
  map_comp _h _k := rfl

private def stageArrow (s : Subdiagram g) (d : Cᵒᵖ) :
    stageLeftDiagram g hg s d ⟶ stageRightDiagram g hg s d where
  app n := ((stage g hg s n.down).row d).hom (g.app d)
  naturality _n _m h := (OriginalSubarrow.map (g.app d)
    ((stage_mono g hg s (leOfHom (X := StageIndex.{u}) h)) d)).w

private def stageLeftCocone (s : Subdiagram g) (d : Cᵒᵖ) :
    Cocone (stageLeftDiagram g hg s d) where
  pt := ((limitSubdiagram g hg s).row d).left (g.app d)
  ι :=
    { app n := SSet.Subcomplex.homOfLE (stage_le_limit g hg s n.down d).1
      naturality _n _m _h := rfl }

private def stageRightCocone (s : Subdiagram g) (d : Cᵒᵖ) :
    Cocone (stageRightDiagram g hg s d) where
  pt := ((limitSubdiagram g hg s).row d).right (g.app d)
  ι :=
    { app n := SSet.Subcomplex.homOfLE (stage_le_limit g hg s n.down d).2
      naturality _n _m _h := rfl }

private def isColimitStageLeft (s : Subdiagram g) (d : Cᵒᵖ) :
    IsColimit (stageLeftCocone g hg s d) := by
  apply evaluationJointlyReflectsColimits
  intro m
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    have hx : x.val ∈ (⨆ n : StageIndex.{u},
        ((stage g hg s n.down).row d).left (g.app d)).obj m := x.property
    simp only [CategoryTheory.Subfunctor.iSup_obj, Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, ⟨x.val, hn⟩, rfl⟩
  · intro n x y hxy
    refine ⟨n, 𝟙 n, ?_⟩
    have hv := congrArg (fun z : (stageLeftCocone g hg s d).pt.obj m => z.val) hxy
    change x.val = y.val at hv
    exact congrArg (fun z => ((stageLeftDiagram g hg s d).map (𝟙 n)).app m z)
      (Subtype.ext hv)

private def isColimitStageRight (s : Subdiagram g) (d : Cᵒᵖ) :
    IsColimit (stageRightCocone g hg s d) := by
  apply evaluationJointlyReflectsColimits
  intro m
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    have hx : x.val ∈ (⨆ n : StageIndex.{u},
        ((stage g hg s n.down).row d).right (g.app d)).obj m := x.property
    simp only [CategoryTheory.Subfunctor.iSup_obj, Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, ⟨x.val, hn⟩, rfl⟩
  · intro n x y hxy
    refine ⟨n, 𝟙 n, ?_⟩
    have hv := congrArg (fun z : (stageRightCocone g hg s d).pt.obj m => z.val) hxy
    change x.val = y.val at hv
    exact congrArg (fun z => ((stageRightDiagram g hg s d).map (𝟙 n)).app m z)
      (Subtype.ext hv)

private def stageWholeDiagram (s : Subdiagram g) (d : Cᵒᵖ) : StageIndex.{u} ⥤ Arrow SSet.{u} :=
  NatTrans.arrow (stageArrow g hg s d)

private def stageWholeCocone (s : Subdiagram g) (d : Cᵒᵖ) :
    Cocone (stageWholeDiagram g hg s d) where
  pt := Arrow.mk (((limitSubdiagram g hg s).row d).hom (g.app d))
  ι :=
    { app n := OriginalSubarrow.map (g.app d) (stage_le_limit g hg s n.down d)
      naturality _n _m _h := rfl }

private def isColimitStageWhole (s : Subdiagram g) (d : Cᵒᵖ) :
    IsColimit (stageWholeCocone g hg s d) := by
  apply Comma.fstSndJointlyReflectColimit
  · change IsColimit (stageLeftCocone g hg s d)
    exact isColimitStageLeft g hg s d
  · change IsColimit (stageRightCocone g hg s d)
    exact isColimitStageRight g hg s d

private def completedStageWholeDiagram (s : Subdiagram g) (d : Cᵒᵖ) :
    StageIndex.{u} ⥤ Arrow SSet.{u} :=
  stageWholeDiagram g hg s d ⋙ completion.mapArrow

private def completedStageWholeCocone (s : Subdiagram g) (d : Cᵒᵖ) :
    Cocone (completedStageWholeDiagram g hg s d) :=
  completion.mapArrow.mapCocone (stageWholeCocone g hg s d)

private def isColimitCompletedStageWhole (s : Subdiagram g) (d : Cᵒᵖ) :
    IsColimit (completedStageWholeCocone g hg s d) := by
  apply Comma.fstSndJointlyReflectColimit
  · change IsColimit (completion.mapCocone (stageLeftCocone g hg s d))
    exact isColimitOfPreserves completion (isColimitStageLeft g hg s d)
  · change IsColimit (completion.mapCocone (stageRightCocone g hg s d))
    exact isColimitOfPreserves completion (isColimitStageRight g hg s d)

private def completedStageMap (s : Subdiagram g) (d : Cᵒᵖ) {n m : StageIndex.{u}} (h : n ≤ m) :
    Arrow.mk (completion.map (((stage g hg s n.down).row d).hom (g.app d))) ⟶
      Arrow.mk (completion.map (((stage g hg s m.down).row d).hom (g.app d))) :=
  OriginalSubarrow.completedMap (g.app d) (stage_mono g hg s h d)

private def completedStageInclusion (s : Subdiagram g) (d : Cᵒᵖ) (n : StageIndex.{u}) :
    Arrow.mk (completion.map (((stage g hg s n.down).row d).hom (g.app d))) ⟶
      Arrow.mk (completion.map (((limitSubdiagram g hg s).row d).hom (g.app d))) :=
  OriginalSubarrow.completedMap (g.app d) (stage_le_limit g hg s n.down d)

@[reassoc (attr := simp)]
private theorem completedStageMap_inclusion (s : Subdiagram g) (d : Cᵒᵖ)
    {n m : StageIndex.{u}} (h : n ≤ m) :
    completedStageMap g hg s d h ≫ completedStageInclusion g hg s d m =
      completedStageInclusion g hg s d n :=
  OriginalSubarrow.completedMap_comp (g.app d) (stage_mono g hg s h d)
    (stage_le_limit g hg s m.down d)

end Normalized


section Normalized

variable {C : Type u} [SmallCategory C]
variable {U V : SimplicialPresheaf.{u} C} (g : U ⟶ V)
    (hg : ∀ d, SSet.realizationWeakEquivalences (g.app d))

/-- Every finite problem in the actual union has an original strict stage
presentation with BOTH top and bottom equations. -/
private theorem refineLimitProblem (s : Subdiagram g) (d : Cᵒᵖ)
    {A B : SSet.{u}} [SSet.Finite A] [SSet.Finite B] (i : A ⟶ B)
    (top : A ⟶ SSet.mappingPathSpace
      (completion.map (((limitSubdiagram g hg s).row d).hom (g.app d))))
    (bottom : B ⟶ completion.obj (((limitSubdiagram g hg s).row d).right (g.app d)))
    (sq : CommSq top i
      (SSet.mappingPathTarget (completion.map
          (((limitSubdiagram g hg s).row d).hom (g.app d)))) bottom) :
    ∃ (n : StageIndex.{u})
      (topn : A ⟶ SSet.mappingPathSpace
          (completion.map (((stage g hg s n.down).row d).hom (g.app d))))
      (bottomn : B ⟶ completion.obj (((stage g hg s n.down).row d).right (g.app d))),
      CommSq topn i (SSet.mappingPathTarget
        (completion.map (((stage g hg s n.down).row d).hom (g.app d)))) bottomn ∧
      topn ≫ pathMap (completedStageInclusion g hg s d n) = top ∧
      bottomn ≫ (completedStageInclusion g hg s d n).right = bottom := by
  let tA := Arrow.mk (initialVertex A)
  let : SSet.Finite tA.left := by change SSet.Finite A; infer_instance
  let : SSet.Finite tA.right := by change SSet.Finite ((Δ[1] : SSet.{u}) ⊗ A); infer_instance
  let : IsFinitelyPresentable.{u} tA :=
    Comma.isCardinalPresentable_mk (F₁ := 𝟭 SSet.{u}) (F₂ := 𝟭 SSet.{u}) tA.hom
  let topArrow : tA ⟶ Arrow.mk
      (completion.map (((limitSubdiagram g hg s).row d).hom (g.app d))) :=
    Arrow.homMk
      (top ≫
          SSet.mappingPathRetract (completion.map (((limitSubdiagram g hg s).row d).hom (g.app d))))
      (MonoidalClosed.uncurry
        (top ≫
            SSet.mappingPathEval (completion.map
              (((limitSubdiagram g hg s).row d).hom (g.app d))))) (by
          change (top ≫ SSet.mappingPathRetract _) ≫ completion.map
            (((limitSubdiagram g hg s).row d).hom (g.app d)) =
              initialVertex A ≫ MonoidalClosed.uncurry (top ≫ SSet.mappingPathEval _)
          rw [initialVertex_uncurry]
          have hp : SSet.mappingPathRetract
                (completion.map (((limitSubdiagram g hg s).row d).hom (g.app d))) ≫
                completion.map (((limitSubdiagram g hg s).row d).hom (g.app d)) =
              SSet.mappingPathEval
                (completion.map (((limitSubdiagram g hg s).row d).hom (g.app d))) ≫ SSet.eval₀ :=
            pullback.condition
          rw [Category.assoc, hp, Category.assoc])
  obtain ⟨nT, aT, haT⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (isColimitCompletedStageWhole g hg s d) topArrow
  change tA ⟶ Arrow.mk (completion.map (((stage g hg s nT.down).row d).hom (g.app d))) at aT
  change aT ≫ completedStageInclusion g hg s d nT = topArrow at haT
  let cR := completion.mapCocone (stageRightCocone g hg s d)
  have hcR : IsColimit cR := isColimitOfPreserves completion (isColimitStageRight g hg s d)
  obtain ⟨nB, bB, hbB⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hcR bottom
  change B ⟶ completion.obj (((stage g hg s nB.down).row d).right (g.app d)) at bB
  change bB ≫ (completedStageInclusion g hg s d nB).right = bottom at hbB
  let k := max nT nB
  let hT : nT ≤ k := le_max_left _ _
  let hB : nB ≤ k := le_max_right _ _
  let aK := aT ≫ completedStageMap g hg s d hT
  let bK := bB ≫ (completedStageMap g hg s d hB).right
  have haK : aK ≫ completedStageInclusion g hg s d k = topArrow := by
    dsimp only [aK]
    rw [Category.assoc, completedStageMap_inclusion, haT]
  have hbK : bK ≫ (completedStageInclusion g hg s d k).right = bottom := by
    have hc := congrArg Arrow.Hom.right (completedStageMap_inclusion g hg s d hB)
    change (completedStageMap g hg s d hB).right ≫ (completedStageInclusion g hg s d k).right =
      (completedStageInclusion g hg s d nB).right at hc
    dsimp only [bK]
    rw [Category.assoc, hc, hbB]
  let topK : A ⟶ SSet.mappingPathSpace
      (completion.map (((stage g hg s k.down).row d).hom (g.app d))) :=
    pullback.lift aK.left (MonoidalClosed.curry aK.right) (by
      have hw : aK.left ≫ completion.map (((stage g hg s k.down).row d).hom (g.app d)) =
          initialVertex A ≫ aK.right := aK.w
      rw [hw, ← initialVertex_uncurry, MonoidalClosed.uncurry_curry])
  have htopK_left : topK ≫ SSet.mappingPathRetract
      (completion.map (((stage g hg s k.down).row d).hom (g.app d))) = aK.left :=
    pullback.lift_fst _ _ _
  have htopK_path : topK ≫ SSet.mappingPathEval
      (completion.map (((stage g hg s k.down).row d).hom (g.app d))) =
          MonoidalClosed.curry aK.right :=
    pullback.lift_snd _ _ _
  have htopK : topK ≫ pathMap (completedStageInclusion g hg s d k) = top := by
    apply pullback.hom_ext
    · change (topK ≫ pathMap (completedStageInclusion g hg s d k)) ≫ SSet.mappingPathRetract _ =
        top ≫ SSet.mappingPathRetract _
      rw [Category.assoc, pathMap_retract, ← Category.assoc, htopK_left]
      exact congrArg Arrow.Hom.left haK
    · change (topK ≫ pathMap (completedStageInclusion g hg s d k)) ≫ SSet.mappingPathEval _ =
        top ≫ SSet.mappingPathEval _
      rw [Category.assoc, pathMap_eval, ← Category.assoc, htopK_path]
      have hc := congrArg Arrow.Hom.right haK
      change aK.right ≫ (completedStageInclusion g hg s d k).right =
        MonoidalClosed.uncurry (top ≫ SSet.mappingPathEval _) at hc
      simpa only [MonoidalClosed.curry_natural_right, MonoidalClosed.curry_uncurry] using
        congrArg MonoidalClosed.curry hc
  have he : (topK ≫ SSet.mappingPathTarget
        (completion.map (((stage g hg s k.down).row d).hom (g.app d)))) ≫
        (completedStageInclusion g hg s d k).right =
      (i ≫ bK) ≫ (completedStageInclusion g hg s d k).right := by
    calc
      _ = (topK ≫ pathMap (completedStageInclusion g hg s d k)) ≫
          SSet.mappingPathTarget
            (completion.map (((limitSubdiagram g hg s).row d).hom (g.app d))) := by
        simp only [Category.assoc, pathMap_target]
      _ = top ≫ SSet.mappingPathTarget
          (completion.map (((limitSubdiagram g hg s).row d).hom (g.app d))) := by rw [htopK]
      _ = i ≫ bottom := sq.w
      _ = (i ≫ bK) ≫ (completedStageInclusion g hg s d k).right := by rw [Category.assoc, hbK]
  obtain ⟨n, a, b, hab⟩ := IsFinitelyPresentable.exists_eq_of_isColimit hcR
    (topK ≫ SSet.mappingPathTarget
      (completion.map (((stage g hg s k.down).row d).hom (g.app d)))) (i ≫ bK) he
  have heq : a = b := Subsingleton.elim _ _
  subst b
  let hkn : k ≤ n := leOfHom (X := StageIndex.{u}) a
  change (topK ≫ SSet.mappingPathTarget
        (completion.map (((stage g hg s k.down).row d).hom (g.app d)))) ≫
        (completedStageMap g hg s d hkn).right =
      (i ≫ bK) ≫ (completedStageMap g hg s d hkn).right at hab
  let topN := topK ≫ pathMap (completedStageMap g hg s d hkn)
  let bottomN := bK ≫ (completedStageMap g hg s d hkn).right
  refine ⟨n, topN, bottomN, ?_, ?_, ?_⟩
  · refine ⟨?_⟩
    dsimp only [topN, bottomN]
    rw [Category.assoc, pathMap_target, ← Category.assoc, hab, Category.assoc]
  · dsimp only [topN]
    rw [Category.assoc, ← pathMap_comp, completedStageMap_inclusion, htopK]
  · have hc := congrArg Arrow.Hom.right (completedStageMap_inclusion g hg s d hkn)
    change (completedStageMap g hg s d hkn).right ≫ (completedStageInclusion g hg s d n).right =
      (completedStageInclusion g hg s d k).right at hc
    dsimp only [bottomN]
    rw [Category.assoc, hc, hbK]

end Normalized


section Normalized

variable {C : Type u} [SmallCategory C]
variable {U V : SimplicialPresheaf.{u} C} (g : U ⟶ V)
    (hg : ∀ d, SSet.realizationWeakEquivalences (g.app d))

/-- The original union is genuinely weak. This is proved by original finite
problem descent and the next round's strict lift, not by a weak-colimit axiom. -/
private theorem limit_weak (s : Subdiagram g) (d : Cᵒᵖ) :
    SSet.realizationWeakEquivalences (((limitSubdiagram g hg s).row d).hom (g.app d)) := by
  apply (weak_iff_completedPathTarget_rlp _).mpr
  intro A B i hi
  rcases hi with ⟨n⟩
  refine ⟨?_⟩
  intro top bottom sq
  obtain ⟨k, topK, bottomK, sqK, htopK, hbottomK⟩ :=
    refineLimitProblem g hg s d (SSet.boundary.{u} n).ι top bottom sq
  let p : BoundaryProblem g (stage g hg s k.down) := ⟨d, n, topK, bottomK, sqK⟩
  let ell : (Δ[n] : SSet.{u}) ⟶ SSet.mappingPathSpace
      (completion.map (((stage g hg s (k.down + 1)).row d).hom (g.app d))) :=
    roundLift g hg (stage g hg s k.down) p
  let step := OriginalSubarrow.completedMap (g.app d) (stage_le_succ g hg s k.down d)
  let inc := OriginalSubarrow.completedMap (g.app d) (stage_le_limit g hg s (k.down + 1) d)
  let l := ell ≫ pathMap inc
  have hfac := roundLift_fac g hg (stage g hg s k.down) p
  change (SSet.boundary.{u} n).ι ≫ ell = topK ≫ pathMap step ∧
    ell ≫ SSet.mappingPathTarget
      (completion.map (((stage g hg s (k.down + 1)).row d).hom (g.app d))) = bottomK ≫
          step.right at hfac
  have hcomp : step ≫ inc = completedStageInclusion g hg s d k :=
    OriginalSubarrow.completedMap_comp (g.app d) (stage_le_succ g hg s k.down d)
      (stage_le_limit g hg s (k.down + 1) d)
  refine ⟨⟨l, ?_, ?_⟩⟩
  · dsimp only [l]
    rw [← Category.assoc, hfac.1, Category.assoc, ← pathMap_comp, hcomp]
    exact htopK
  · dsimp only [l]
    rw [Category.assoc, pathMap_target, ← Category.assoc, hfac.2, Category.assoc]
    have hc := congrArg Arrow.Hom.right hcomp
    change step.right ≫ inc.right = (completedStageInclusion g hg s d k).right at hc
    rw [hc]
    exact hbottomK

end Normalized

namespace Subdiagram

/-- The actual range factor of both maps of an original incoming square. -/
def incomingFactor {A B : SimplicialPresheaf.{u} D} {i : A ⟶ B}
    (t : Arrow.mk i ⟶ Arrow.mk f) : Arrow.mk i ⟶ arrow f (incomingRange f t) :=
  Arrow.homMk
    { app d := SSet.Subcomplex.toRange (t.left.app d)
      naturality d e h := by
        let m : (SSet.Subcomplex.range (t.left.app d) : SSet.{u}) ⟶
            (SSet.Subcomplex.range (t.left.app e) : SSet.{u}) := leftMap f (incomingRange f t) h
        have hm : m ≫ (SSet.Subcomplex.range (t.left.app e)).ι =
            (SSet.Subcomplex.range (t.left.app d)).ι ≫ X.map h := leftMap_ι f (incomingRange f t) h
        change A.map h ≫ SSet.Subcomplex.toRange (t.left.app e) =
            SSet.Subcomplex.toRange (t.left.app d) ≫ m
        apply (cancel_mono (SSet.Subcomplex.range (t.left.app e)).ι).mp
        change (A.map h ≫ SSet.Subcomplex.toRange (t.left.app e)) ≫
            (SSet.Subcomplex.range (t.left.app e)).ι =
          (SSet.Subcomplex.toRange (t.left.app d) ≫ m) ≫
            (SSet.Subcomplex.range (t.left.app e)).ι
        rw [Category.assoc, SSet.Subcomplex.toRange_ι, Category.assoc, hm,
          ← Category.assoc, SSet.Subcomplex.toRange_ι]
        exact t.left.naturality h }
    { app d := SSet.Subcomplex.toRange (t.right.app d)
      naturality d e h := by
        let m : (SSet.Subcomplex.range (t.right.app d) : SSet.{u}) ⟶
            (SSet.Subcomplex.range (t.right.app e) : SSet.{u}) := rightMap f (incomingRange f t) h
        have hm : m ≫ (SSet.Subcomplex.range (t.right.app e)).ι =
            (SSet.Subcomplex.range (t.right.app d)).ι ≫ Y.map h :=
                rightMap_ι f (incomingRange f t) h
        change B.map h ≫ SSet.Subcomplex.toRange (t.right.app e) =
            SSet.Subcomplex.toRange (t.right.app d) ≫ m
        apply (cancel_mono (SSet.Subcomplex.range (t.right.app e)).ι).mp
        change (B.map h ≫ SSet.Subcomplex.toRange (t.right.app e)) ≫
            (SSet.Subcomplex.range (t.right.app e)).ι =
          (SSet.Subcomplex.toRange (t.right.app d) ≫ m) ≫
            (SSet.Subcomplex.range (t.right.app e)).ι
        rw [Category.assoc, SSet.Subcomplex.toRange_ι, Category.assoc, hm,
          ← Category.assoc, SSet.Subcomplex.toRange_ι]
        exact t.right.naturality h }
    (by
      apply NatTrans.ext
      funext d
      let m : (SSet.Subcomplex.range (t.left.app d) : SSet.{u}) ⟶
          (SSet.Subcomplex.range (t.right.app d) : SSet.{u}) :=
              ((incomingRange f t).row d).hom (f.app d)
      have hm : m ≫ (SSet.Subcomplex.range (t.right.app d)).ι =
          (SSet.Subcomplex.range (t.left.app d)).ι ≫ f.app d :=
        OriginalSubarrow.hom_right_ι (f.app d) ((incomingRange f t).row d)
      apply (cancel_mono (SSet.Subcomplex.range (t.right.app d)).ι).mp
      change (SSet.Subcomplex.toRange (t.left.app d) ≫ m) ≫
          (SSet.Subcomplex.range (t.right.app d)).ι =
        (i.app d ≫ SSet.Subcomplex.toRange (t.right.app d)) ≫
          (SSet.Subcomplex.range (t.right.app d)).ι
      rw [Category.assoc, hm, ← Category.assoc,
        SSet.Subcomplex.toRange_ι, Category.assoc, SSet.Subcomplex.toRange_ι]
      exact congrArg (fun q => q.app d) t.w)

@[reassoc (attr := simp)]
theorem incomingFactor_inclusion {A B : SimplicialPresheaf.{u} D} {i : A ⟶ B}
    (t : Arrow.mk i ⟶ Arrow.mk f) :
    incomingFactor f t ≫ inclusion f (incomingRange f t) = t := by
  apply Arrow.hom_ext
  · apply NatTrans.ext
    funext d
    exact SSet.Subcomplex.toRange_ι (t.left.app d)
  · apply NatTrans.ext
    funext d
    exact SSet.Subcomplex.toRange_ι (t.right.app d)

end Subdiagram

section Normalized

variable {C : Type u} [SmallCategory C]
variable {U V : SimplicialPresheaf.{u} C} (g : U ⟶ V)
    (hg : ∀ d, SSet.realizationWeakEquivalences (g.app d))

include hg in
/-- The normalized core retains an ACTUAL original bounded weak subdiagram
and the full original incoming factorization. -/
private theorem existsBoundedWeakSubdiagram {A B : SimplicialPresheaf.{u} C} {i : A ⟶ B}
    (e : Envelope (Arrow.mk i)) (t : Arrow.mk i ⟶ Arrow.mk g) :
    ∃ (s : Subdiagram g), RowBounded g s e.γ ∧
      (∀ d, SSet.realizationWeakEquivalences ((s.row d).hom (g.app d))) ∧
      ∃ (a : Arrow.mk i ⟶ Subdiagram.arrow g s),
        a ≫ Subdiagram.inclusion g s = t := by
  let seed := Subdiagram.incomingRange g t
  let s := limitSubdiagram g hg seed
  have hb : RowBounded g s e.γ :=
    limit_rowBounded g hg e seed (incomingRange_rowBounded g e t)
  have hle : Subdiagram.incomingRange g t ≤ s := stage_le_limit g hg seed 0
  refine ⟨s, hb, limit_weak g hg seed, ?_⟩
  refine ⟨Subdiagram.incomingFactor g t ≫ Subdiagram.map g hle, ?_⟩
  rw [Category.assoc, Subdiagram.map_inclusion, Subdiagram.incomingFactor_inclusion]

end Normalized


private def elementsSigmaEquiv (T : SSet.{u}) :
    T.Elements ≃ Σ n : SimplexCategoryᵒᵖ, T.obj n where
  toFun q := ⟨q.obj, q.val⟩
  invFun z := CategoryTheory.Functor.elementsMk T z.1 z.2
  left_inv q := by cases q; rfl
  right_inv z := by cases z; rfl

private theorem elements_cardinal_eq_of_iso {A B : SSet.{u}} (e : A ≅ B) :
    Cardinal.mk A.Elements = Cardinal.mk B.Elements := by
  calc
    _ = Cardinal.mk (Σ n : SimplexCategoryᵒᵖ, A.obj n) := Cardinal.mk_congr (elementsSigmaEquiv A)
    _ = Cardinal.mk (Σ n : SimplexCategoryᵒᵖ, B.obj n) :=
      Cardinal.mk_congr (Equiv.sigmaCongrRight (fun n => (e.app n).toEquiv))
    _ = Cardinal.mk B.Elements := (Cardinal.mk_congr (elementsSigmaEquiv B)).symm

private theorem value_elements_le (T : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    Cardinal.mk (T.obj n) ≤ Cardinal.mk T.Elements := by
  calc
    _ ≤ Cardinal.mk (Σ n : SimplexCategoryᵒᵖ, T.obj n) :=
      Cardinal.mk_le_of_injective (f := Sigma.mk n)
        (sigma_mk_injective (β := fun n : SimplexCategoryᵒᵖ => T.obj n))
    _ = Cardinal.mk T.Elements := (Cardinal.mk_congr (elementsSigmaEquiv T)).symm

namespace Subdiagram

instance leftInclusion_mono (s : Subdiagram f) : Mono (leftInclusion f s) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  change Mono (((s.row d).left (f.app d)).ι)
  infer_instance

instance rightInclusion_mono (s : Subdiagram f) : Mono (rightInclusion f s) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  change Mono (((s.row d).right (f.app d)).ι)
  infer_instance

/-- A transported monic endpoint pair gives the actual original range isomorphism. -/
theorem incomingFactor_isIso {A B : SimplicialPresheaf.{u} D} {i : A ⟶ B}
    (t : Arrow.mk i ⟶ Arrow.mk f) [Mono t.left] [Mono t.right] :
    IsIso (incomingFactor f t) := by
  let : ∀ d : Dᵒᵖ, IsIso ((incomingFactor f t).left.app d) := fun d => by
    change IsIso (SSet.Subcomplex.toRange (t.left.app d))
    infer_instance
  let : IsIso (incomingFactor f t).left := NatIso.isIso_of_isIso_app _
  let : ∀ d : Dᵒᵖ, IsIso ((incomingFactor f t).right.app d) := fun d => by
    change IsIso (SSet.Subcomplex.toRange (t.right.app d))
    infer_instance
  let : IsIso (incomingFactor f t).right := NatIso.isIso_of_isIso_app _
  exact Arrow.isIso_of_isIso_left_of_isIso_right _

end Subdiagram

section OriginalSites

variable [Small.{u} D] [LocallySmall.{u} D]

/-- Genuine weak arrows with bounds on their named small-model rows.
This makes no equality assertion about global Elements on different sites. -/
def normalizedWeakBoundedArrows (γ : Cardinal.{u}) :
    ObjectProperty (Arrow (SimplicialPresheaf.{u} D)) := fun a =>
  SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ a.hom ∧
    ∀ d : (SmallModel.{u} D)ᵒᵖ,
      Cardinal.mk
          (((SimplicialPresheaf.smallModelTransport (D := D)).functor.obj a.left).obj
            d).Elements ≤ γ ∧
      Cardinal.mk
          (((SimplicialPresheaf.smallModelTransport (D := D)).functor.obj a.right).obj
            d).Elements ≤ γ

private theorem normalizedBounds_of_iso {γ : Cardinal.{u}}
    {a b : Arrow (SimplicialPresheaf.{u} D)} (e : a ≅ b)
    (ha : normalizedWeakBoundedArrows (D := D) γ a) :
    normalizedWeakBoundedArrows (D := D) γ b := by
  refine ⟨((SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ).arrow_iso_iff e).mp ha.1, ?_⟩
  intro d
  let E := SimplicialPresheaf.smallModelTransport (D := D)
  let eL := (E.functor.mapIso (Arrow.leftFunc.mapIso e)).app d
  let eR := (E.functor.mapIso (Arrow.rightFunc.mapIso e)).app d
  constructor
  · have hL : Cardinal.mk ((E.functor.obj a.left).obj d).Elements =
        Cardinal.mk ((E.functor.obj b.left).obj d).Elements := elements_cardinal_eq_of_iso eL
    change Cardinal.mk ((E.functor.obj b.left).obj d).Elements ≤ γ
    rw [← hL]
    exact (ha.2 d).1
  · have hR : Cardinal.mk ((E.functor.obj a.right).obj d).Elements =
        Cardinal.mk ((E.functor.obj b.right).obj d).Elements := elements_cardinal_eq_of_iso eR
    change Cardinal.mk ((E.functor.obj b.right).obj d).Elements ≤ γ
    rw [← hR]
    exact (ha.2 d).2

end OriginalSites


section OriginalSites

variable [Small.{u} D] [LocallySmall.{u} D]

private theorem smallModelWeak_forward {A B : SimplicialPresheaf.{u} D} (g : A ⟶ B)
    (hg : SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ g) :
    SSet.realizationWeakEquivalences.{u}.functorCategory (SmallModel.{u} D)ᵒᵖ
      ((SimplicialPresheaf.smallModelTransport (D := D)).functor.map g) := by
  intro d
  exact hg ((equivSmallModel.{u} D).inverse.op.obj d)

private theorem smallModelWeak_inverse {A B : SimplicialPresheaf.{u} (SmallModel.{u} D)}
    (g : A ⟶ B) (hg : SSet.realizationWeakEquivalences.{u}.functorCategory (SmallModel.{u} D)ᵒᵖ g) :
    SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ
      ((SimplicialPresheaf.smallModelTransport (D := D)).inverse.map g) := by
  intro d
  exact hg ((equivSmallModel.{u} D).functor.op.obj d)

/-- Transport the normalized construction through the native WHOLE Arrow unit.
The returned original subdiagram is the actual range of the monic endpoint pair. -/
private theorem existsOriginalBoundedWeakSubdiagram {A B : SimplicialPresheaf.{u} D} (i : A ⟶ B) :
    ∃ γ : Cardinal.{u}, ∀ {X Y : SimplicialPresheaf.{u} D} (g : X ⟶ Y)
      (_hg : SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ g)
      (t : Arrow.mk i ⟶ Arrow.mk g),
      ∃ (s : Subdiagram g),
        normalizedWeakBoundedArrows (D := D) γ (Subdiagram.arrow g s) ∧
        ∃ (a : Arrow.mk i ⟶ Subdiagram.arrow g s), a ≫ Subdiagram.inclusion g s = t := by
  let E := SimplicialPresheaf.smallModelTransport (D := D)
  let EA := CategoryTheory.Functor.mapArrowEquivalence E
  let iN := E.functor.map i
  let env := envelope (Arrow.mk iN)
  refine ⟨env.γ, ?_⟩
  intro X Y g hg t
  let gN := E.functor.map g
  let tN : Arrow.mk iN ⟶ Arrow.mk gN := E.functor.mapArrow.map t
  have hgN : ∀ d, SSet.realizationWeakEquivalences (gN.app d) :=
    smallModelWeak_forward (D := D) g hg
  obtain ⟨sN, hbN, hwN, aN, haN⟩ := existsBoundedWeakSubdiagram gN hgN env tN
  let qN := Subdiagram.arrow gN sN
  change EA.functor.obj (Arrow.mk i) ⟶ qN at aN
  let qB := EA.inverse.obj qN
  let incN : qN ⟶ EA.functor.obj (Arrow.mk g) := Subdiagram.inclusion gN sN
  have hnorm : aN ≫ incN = EA.functor.map t := haN
  let ui : Arrow.mk i ⟶ EA.inverse.obj (EA.functor.obj (Arrow.mk i)) :=
    EA.unitIso.hom.app (Arrow.mk i)
  let uf : Arrow.mk g ≅ EA.inverse.obj (EA.functor.obj (Arrow.mk g)) :=
    EA.unitIso.app (Arrow.mk g)
  let v : qB ⟶ Arrow.mk g := EA.inverse.map incN ≫ uf.inv
  let aB : Arrow.mk i ⟶ qB := ui ≫ EA.inverse.map aN
  have haB : aB ≫ v = t := by
    have hn : ui ≫ EA.inverse.map (EA.functor.map t) = t ≫ uf.hom := by
      have hn₀ := (EA.unitIso.hom.naturality t).symm
      change ui ≫ EA.inverse.map (EA.functor.map t) = t ≫ uf.hom at hn₀
      exact hn₀
    calc
      aB ≫ v = (ui ≫ (EA.inverse.map aN ≫ EA.inverse.map incN)) ≫ uf.inv := by
        dsimp only [aB, v]
        simp only [Category.assoc]
      _ = (ui ≫ EA.inverse.map (aN ≫ incN)) ≫ uf.inv := by rw [EA.inverse.map_comp]
      _ = (ui ≫ EA.inverse.map (EA.functor.map t)) ≫ uf.inv := by rw [hnorm]
      _ = (t ≫ uf.hom) ≫ uf.inv := by rw [hn]
      _ = t := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let : Mono incN.left := Subdiagram.leftInclusion_mono _ _
  let : Mono incN.right := Subdiagram.rightInclusion_mono _ _
  let hvLeft : Mono v.left := by
    let m : qB.left ⟶ (EA.inverse.obj (EA.functor.obj (Arrow.mk g))).left := E.inverse.map incN.left
    let u : (EA.inverse.obj (EA.functor.obj (Arrow.mk g))).left ⟶ X := uf.inv.left
    let : Mono m := by change Mono (E.inverse.map incN.left); infer_instance
    let : Mono u := by change Mono uf.inv.left; infer_instance
    change Mono (m ≫ u)
    infer_instance
  let hvRight : Mono v.right := by
    let m : qB.right ⟶ (EA.inverse.obj (EA.functor.obj (Arrow.mk g))).right :=
        E.inverse.map incN.right
    let u : (EA.inverse.obj (EA.functor.obj (Arrow.mk g))).right ⟶ Y := uf.inv.right
    let : Mono m := by change Mono (E.inverse.map incN.right); infer_instance
    let : Mono u := by change Mono uf.inv.right; infer_instance
    change Mono (m ≫ u)
    infer_instance
  let s := Subdiagram.incomingRange g v
  let b : qB ⟶ Subdiagram.arrow g s := Subdiagram.incomingFactor g v
  let : IsIso b := by
    exact @Subdiagram.incomingFactor_isIso D inferInstance X Y g qB.left qB.right qB.hom v
        hvLeft hvRight
  have hwB : SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ qB.hom :=
    smallModelWeak_inverse (D := D) qN.hom hwN
  have hbB : normalizedWeakBoundedArrows (D := D) env.γ qB := by
    refine ⟨hwB, ?_⟩
    intro d
    let ce := EA.counitIso.app qN
    let eL := (Arrow.leftFunc.mapIso ce).app d
    let eR := (Arrow.rightFunc.mapIso ce).app d
    have hL : Cardinal.mk ((E.functor.obj qB.left).obj d).Elements =
        Cardinal.mk (qN.left.obj d).Elements := elements_cardinal_eq_of_iso eL
    have hR : Cardinal.mk ((E.functor.obj qB.right).obj d).Elements =
        Cardinal.mk (qN.right.obj d).Elements := elements_cardinal_eq_of_iso eR
    constructor
    · change Cardinal.mk ((E.functor.obj qB.left).obj d).Elements ≤ env.γ
      rw [hL]
      exact (hbN d).1
    · change Cardinal.mk ((E.functor.obj qB.right).obj d).Elements ≤ env.γ
      rw [hR]
      exact (hbN d).2
  refine ⟨s, normalizedBounds_of_iso (D := D) (asIso b) hbB, aB ≫ b, ?_⟩
  have hv : b ≫ Subdiagram.inclusion g s = v := Subdiagram.incomingFactor_inclusion _ _
  rw [Category.assoc, hv]
  exact haB

end OriginalSites


section OriginalSites

variable [Small.{u} D] [LocallySmall.{u} D]

/-- The actual bounded weak-arrow property is essentially small, by the
accepted pointwise bound theorem on the ordered normalized presheaf carrier. -/
private theorem normalizedWeakBoundedArrows_essentiallySmall (γ : Cardinal.{u}) :
    ObjectProperty.EssentiallySmall.{u} (normalizedWeakBoundedArrows (D := D) γ) := by
  let T := SimplicialPresheaf.smallModelTransport (D := D)
  let L : SimplicialPresheaf.{u} (SmallModel.{u} D) ≌
      ((SmallModel.{u} D × SimplexCategory)ᵒᵖ ⥤ Type u) :=
    CategoryTheory.Functor.currying.trans (prodOpEquiv (SmallModel.{u} D)).congrLeft.symm
  let E := T.trans L
  let P := normalizedWeakBoundedArrows (D := D) γ
  let P' := P.strictMap E.functor.mapArrow
  have hP' : ObjectProperty.EssentiallySmall.{u} P' :=
    ObjectProperty.essentiallySmall_presheaf_arrows_of_pointwise_bound γ P' (by
      intro a ha x
      rcases ha with ⟨a, ha⟩
      change Cardinal.mk
          (((T.functor.obj a.left).obj (op x.unop.1)).obj (op x.unop.2)) ≤ γ ∧
        Cardinal.mk
          (((T.functor.obj a.right).obj (op x.unop.1)).obj (op x.unop.2)) ≤ γ
      exact ⟨(value_elements_le _ _).trans (ha.2 (op x.unop.1)).1,
        (value_elements_le _ _).trans (ha.2 (op x.unop.1)).2⟩)
  let : ObjectProperty.EssentiallySmall.{u} P' := hP'
  obtain ⟨Q, hQ, hcover⟩ := ObjectProperty.EssentiallySmall.exists_small_le' P'
  let : ObjectProperty.Small.{u} Q := hQ
  obtain ⟨J, F, hF⟩ := ObjectProperty.Small.exists_eq_ofObj Q
  let R : J → Arrow (SimplicialPresheaf.{u} D) := fun j => E.inverse.mapArrow.obj (F j)
  refine ⟨⟨ObjectProperty.ofObj R, inferInstance, ?_⟩⟩
  intro a ha
  obtain ⟨b, hb, ⟨eb⟩⟩ := hcover (E.functor.mapArrow.obj a) (ObjectProperty.strictMap.mk a ha)
  rw [hF, ObjectProperty.ofObj_iff] at hb
  obtain ⟨j, rfl⟩ := hb
  exact ⟨R j, ObjectProperty.ofObj_apply R j,
    ⟨(CategoryTheory.Functor.mapArrowEquivalence E).unitIso.app a ≪≫ E.inverse.mapArrow.mapIso eb⟩⟩

private theorem existsBoundedWeakRepresentatives (γ : Cardinal.{u}) :
    ∃ (J : Type u) (F : J → Arrow (SimplicialPresheaf.{u} D)),
      (∀ j, normalizedWeakBoundedArrows (D := D) γ (F j)) ∧
      ∀ a, normalizedWeakBoundedArrows (D := D) γ a → ∃ j, Nonempty (a ≅ F j) := by
  let P := normalizedWeakBoundedArrows (D := D) γ
  let : ObjectProperty.EssentiallySmall.{u} P := normalizedWeakBoundedArrows_essentiallySmall γ
  obtain ⟨Q, hQ, hQP, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  let : ObjectProperty.Small.{u} Q := hQ
  obtain ⟨J, F, hF⟩ := ObjectProperty.Small.exists_eq_ofObj Q
  refine ⟨J, F, ?_, ?_⟩
  · intro j
    apply hQP
    rw [hF]
    exact ObjectProperty.ofObj_apply F j
  · intro a ha
    obtain ⟨b, hb, ⟨eb⟩⟩ := hPQ a ha
    rw [hF, ObjectProperty.ofObj_iff] at hb
    obtain ⟨j, rfl⟩ := hb
    exact ⟨j, ⟨eb⟩⟩

end OriginalSites


section OriginalSites

variable [Small.{u} D] [LocallySmall.{u} D]

/-- Strict bounded interpolation for EVERY original incoming Arrow.
The family includes every original incoming Hom label, through its native
working-universe copy. Both composition equations and an actual bounded
original endpoint subdiagram are retained. -/
theorem _root_.SimplicialPresheaf.objectwiseKanWeakArrowInterpolation
    (i : Arrow (SimplicialPresheaf.{u} D)) :
    ∃ (γ : Cardinal.{u}) (J : Type u)
      (F : J → Arrow (SimplicialPresheaf.{u} D)) (incoming : ∀ j, i ⟶ F j),
      (∀ j, normalizedWeakBoundedArrows (D := D) γ (F j)) ∧
      ∀ (a : Arrow (SimplicialPresheaf.{u} D))
        (_ha : SSet.realizationWeakEquivalences.{u}.functorCategory Dᵒᵖ a.hom) (t : i ⟶ a),
        ∃ (j : J) (outgoing : F j ⟶ a) (s : Subdiagram a.hom)
          (e : F j ≅ Subdiagram.arrow a.hom s),
          normalizedWeakBoundedArrows (D := D) γ (Subdiagram.arrow a.hom s) ∧
          outgoing = e.hom ≫ Subdiagram.inclusion a.hom s ∧
          incoming j ≫ outgoing = t ∧
          (incoming j).left ≫ outgoing.left = t.left ∧
          (incoming j).right ≫ outgoing.right = t.right := by
  let : LocallySmall.{u} (SimplicialPresheaf.{u} D) := SimplicialPresheaf.locallySmall
  let : LocallySmall.{u} (Arrow (SimplicialPresheaf.{u} D)) :=
    { hom_small a b := small_of_injective
        (f := fun t : a ⟶ b => (t.left, t.right)) (by
          intro s t h
          apply Arrow.hom_ext
          · exact congrArg Prod.fst h
          · exact congrArg Prod.snd h) }
  obtain ⟨γ, hγ⟩ := existsOriginalBoundedWeakSubdiagram (D := D) i.hom
  obtain ⟨K, R, hR, hcover⟩ := existsBoundedWeakRepresentatives (D := D) γ
  let J : Type u := Σ k : K, Shrink.{u} (i ⟶ R k)
  let F : J → Arrow (SimplicialPresheaf.{u} D) := fun j => R j.1
  let incoming : ∀ j : J, i ⟶ F j := fun j =>
    (equivShrink.{u} (i ⟶ R j.1)).symm j.2
  refine ⟨γ, J, F, incoming, fun j => hR j.1, ?_⟩
  intro a ha t
  obtain ⟨s, hs, b, hb⟩ := hγ a.hom ha t
  obtain ⟨k, ⟨ek⟩⟩ := hcover (Subdiagram.arrow a.hom s) hs
  let label : i ⟶ R k := b ≫ ek.hom
  let j : J := ⟨k, equivShrink.{u} (i ⟶ R k) label⟩
  let e : F j ≅ Subdiagram.arrow a.hom s := ek.symm
  let out : F j ⟶ a := e.hom ≫ Subdiagram.inclusion a.hom s
  have hin : incoming j = label := by
    dsimp only [incoming, j]
    exact Equiv.symm_apply_apply _ _
  have hwhole : incoming j ≫ out = t := by
    rw [hin]
    change (b ≫ ek.hom) ≫ (ek.inv ≫ Subdiagram.inclusion a.hom s) = t
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact hb
  refine ⟨j, out, s, e, hs, rfl, hwhole, ?_, ?_⟩
  · exact congrArg Arrow.Hom.left hwhole
  · exact congrArg Arrow.Hom.right hwhole

end OriginalSites

end SimplicialPresheaf.KanWeakInterpolation
