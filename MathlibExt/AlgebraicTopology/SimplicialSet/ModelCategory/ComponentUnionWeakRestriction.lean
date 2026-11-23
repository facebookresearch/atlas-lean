/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ComponentUnionKanFibration
public import MathlibExt.CategoryTheory.Subfunctor.PreimagePullback
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakPiZero

/-!
# Weak restrictions to exact unions of connected components

The literal restriction of an original simplicial map to the inverse image
of a target component selector is its actual preimage pullback. The target
union inclusion is a Kan fibration for every ambient simplicial set. The
existing, actual right-proper Kan–Quillen model therefore preserves an
original realization weak equivalence under this restriction without an
ambient Kan hypothesis. Kan endpoints give the full structural weak class
and every pointed homotopy-group map of the same restricted arrow.

This native simplicial-set bridge supplies the component restrictions used
in Rezk (2001), Section 11.6. It uses the original preimage and proved native
KQ right properness; no Segal or completeness outcome is an input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

variable {X Y : SSet.{u}}

private theorem componentLabel_naturality (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) (q : X.obj n) :
    mapπ₀ f (π₀.mk (X.map (SimplexCategory.const ⦋0⦌ n.unop 0).op q)) =
      π₀.mk (Y.map (SimplexCategory.const ⦋0⦌ n.unop 0).op (f.app n q)) := by
  rw [mapπ₀_mk]
  exact congrArg π₀.mk (f.naturality_apply _ q)

/-- The exact component preimage is the original native subfunctor preimage. -/
theorem componentUnion_preimage (f : X ⟶ Y) (T : Set (π₀ Y)) :
    componentUnion X ((mapπ₀ f) ⁻¹' T) = Subfunctor.preimage (componentUnion Y T) f := by
  ext n q
  simp only [Subfunctor.preimage_obj, Set.mem_preimage, mem_componentUnion]
  rw [componentLabel_naturality]

/-- The original map has range in the literal selected target union. -/
theorem componentUnionPreimageMap_range (f : X ⟶ Y) (T : Set (π₀ Y)) :
    Subfunctor.range ((componentUnion X ((mapπ₀ f) ⁻¹' T)).ι ≫ f) ≤
      componentUnion Y T := by
  rw [Subfunctor.range_comp, Subfunctor.range_ι, Subfunctor.image_le_iff,
    componentUnion_preimage]

/-- Restriction of the original arrow to the exact preimage of a target selector. -/
def componentUnionPreimageMap (f : X ⟶ Y) (T : Set (π₀ Y)) :
    (componentUnion X ((mapπ₀ f) ⁻¹' T) : SSet.{u}) ⟶
      (componentUnion Y T : SSet.{u}) :=
  Subfunctor.lift ((componentUnion X ((mapπ₀ f) ⁻¹' T)).ι ≫ f)
    (componentUnionPreimageMap_range f T)

/-- Both canonical inclusions retain the same original simplicial map. -/
@[reassoc (attr := simp)]
theorem componentUnionPreimageMap_ι (f : X ⟶ Y) (T : Set (π₀ Y)) :
    componentUnionPreimageMap f T ≫ (componentUnion Y T).ι =
      (componentUnion X ((mapπ₀ f) ⁻¹' T)).ι ≫ f :=
  Subfunctor.lift_ι _ _

/-- Every selected simplex has its original image, in every degree. -/
@[simp]
theorem componentUnionPreimageMap_app_val (f : X ⟶ Y) (T : Set (π₀ Y))
    (n : SimplexCategoryᵒᵖ) (q : (componentUnion X ((mapπ₀ f) ⁻¹' T)).obj n) :
    dsimp% ((componentUnionPreimageMap f T).app n q).val = f.app n q.val := rfl

/-- The original component maps and both inclusion maps form the same square. -/
theorem componentUnionPreimageMap_mapπ₀_ι (f : X ⟶ Y) (T : Set (π₀ Y))
    (c : π₀ (componentUnion X ((mapπ₀ f) ⁻¹' T) : SSet.{u})) :
    mapπ₀ (componentUnion Y T).ι (mapπ₀ (componentUnionPreimageMap f T) c) =
      mapπ₀ f (mapπ₀ (componentUnion X ((mapπ₀ f) ⁻¹' T)).ι c) := by
  simpa only [mapπ₀_comp_apply] using
    congrArg (fun a => mapπ₀ a c) (componentUnionPreimageMap_ι f T)

/-- In particular, the original selected vertex maps to its actual image component. -/
theorem componentUnionPreimageMap_mapπ₀_mk (f : X ⟶ Y) (T : Set (π₀ Y))
    (q : (componentUnion X ((mapπ₀ f) ⁻¹' T) : SSet.{u}) _⦋0⦌) :
    mapπ₀ (componentUnion Y T).ι
        (mapπ₀ (componentUnionPreimageMap f T) (π₀.mk q)) =
      π₀.mk (f.app (op ⦋0⦌) q.val) := by
  simp only [mapπ₀_mk]
  rfl

/-- The whole original preimage square is a pullback with both literal legs. -/
theorem componentUnionPreimageMap_isPullback (f : X ⟶ Y) (T : Set (π₀ Y)) :
    IsPullback (componentUnion X ((mapπ₀ f) ⁻¹' T)).ι
      (componentUnionPreimageMap f T) f (componentUnion Y T).ι := by
  have hAux (U : X.Subcomplex) (hU : U = Subfunctor.preimage (componentUnion Y T) f)
      (hR : Subfunctor.range (U.ι ≫ f) ≤ componentUnion Y T) :
      IsPullback U.ι (Subfunctor.lift (U.ι ≫ f) hR) f (componentUnion Y T).ι := by
    subst U
    exact Subfunctor.preimage_isPullback (componentUnion Y T) f
  exact hAux _ (componentUnion_preimage f T) (componentUnionPreimageMap_range f T)

/-- The prescribed compatible original cone has its native pullback lift. -/
noncomputable def componentUnionPreimageLift (f : X ⟶ Y) (T : Set (π₀ Y))
    {A : SSet.{u}} (a : A ⟶ X) (b : A ⟶ (componentUnion Y T : SSet.{u}))
    (h : a ≫ f = b ≫ (componentUnion Y T).ι) :
    A ⟶ (componentUnion X ((mapπ₀ f) ⁻¹' T) : SSet.{u}) :=
  (componentUnionPreimageMap_isPullback f T).lift a b h

@[reassoc (attr := simp)]
theorem componentUnionPreimageLift_fst (f : X ⟶ Y) (T : Set (π₀ Y))
    {A : SSet.{u}} (a : A ⟶ X) (b : A ⟶ (componentUnion Y T : SSet.{u}))
    (h : a ≫ f = b ≫ (componentUnion Y T).ι) :
    componentUnionPreimageLift f T a b h ≫
      (componentUnion X ((mapπ₀ f) ⁻¹' T)).ι = a :=
  (componentUnionPreimageMap_isPullback f T).lift_fst a b h

@[reassoc (attr := simp)]
theorem componentUnionPreimageLift_snd (f : X ⟶ Y) (T : Set (π₀ Y))
    {A : SSet.{u}} (a : A ⟶ X) (b : A ⟶ (componentUnion Y T : SSet.{u}))
    (h : a ≫ f = b ≫ (componentUnion Y T).ι) :
    componentUnionPreimageLift f T a b h ≫ componentUnionPreimageMap f T = b :=
  (componentUnionPreimageMap_isPullback f T).lift_snd a b h

/-- Both original lift equations determine the actual lift uniquely. -/
theorem componentUnionPreimageLift_unique (f : X ⟶ Y) (T : Set (π₀ Y))
    {A : SSet.{u}} (a : A ⟶ X) (b : A ⟶ (componentUnion Y T : SSet.{u}))
    (h : a ≫ f = b ≫ (componentUnion Y T).ι)
    (l : A ⟶ (componentUnion X ((mapπ₀ f) ⁻¹' T) : SSet.{u}))
    (ha : l ≫ (componentUnion X ((mapπ₀ f) ⁻¹' T)).ι = a)
    (_hb : l ≫ componentUnionPreimageMap f T = b) :
    l = componentUnionPreimageLift f T a b h := by
  apply (cancel_mono (componentUnion X ((mapπ₀ f) ⁻¹' T)).ι).mp
  exact ha.trans (componentUnionPreimageLift_fst f T a b h).symm

/-- Pulling back along the target component inclusion preserves original weakness.
Neither original ambient object needs to be Kan, and f need not be a fibration. -/
theorem componentUnionPreimageMap_weak (f : X ⟶ Y) (T : Set (π₀ Y))
    (hf : realizationWeakEquivalences f) :
    realizationWeakEquivalences (componentUnionPreimageMap f T) := by
  let _ : Fibration (componentUnion Y T).ι := componentUnionInclusionKanFibration Y T
  let _ : WeakEquivalence f := (HomotopicalAlgebra.weakEquivalence_iff f).mpr hf
  have hp : WeakEquivalence (componentUnionPreimageMap f T) :=
    IsRightProper.weakEquivalence_of_isPullback (componentUnionPreimageMap_isPullback f T)
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp hp

/-- The actual component map of the same restricted arrow is bijective for any ambient X,Y. -/
theorem componentUnionPreimageMap_bijective_mapπ₀ (f : X ⟶ Y) (T : Set (π₀ Y))
    (hf : realizationWeakEquivalences f) :
    Function.Bijective (mapπ₀ (componentUnionPreimageMap f T)) :=
  (componentUnionPreimageMap_weak f T hf).bijective_mapπ₀

/-- Actual Kan endpoints give the full native structural weak predicate. -/
theorem componentUnionPreimageMap_W [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) (T : Set (π₀ Y)) (hf : realizationWeakEquivalences f) :
    KanComplex.W (componentUnionPreimageMap f T) := by
  let _ : KanComplex (componentUnion X ((mapπ₀ f) ⁻¹' T) : SSet.{u}) :=
    componentUnionKanComplex X _
  let _ : KanComplex (componentUnion Y T : SSet.{u}) := componentUnionKanComplex Y T
  exact (KanComplex.W_iff_realizationWeakEquivalence _).mpr
    (componentUnionPreimageMap_weak f T hf)

/-- Every pointed map uses the actual selected source q and actual target p(q). -/
theorem componentUnionPreimageMap_bijective_piMap [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) (T : Set (π₀ Y)) (hf : realizationWeakEquivalences f)
    (n : ℕ) (q : (componentUnion X ((mapπ₀ f) ⁻¹' T) : SSet.{u}) _⦋0⦌) :
    Function.Bijective
      (KanComplex.π.map (componentUnionPreimageMap f T) rfl (n := n) (x := q)) :=
  (componentUnionPreimageMap_W f T hf).bijective_piMap n q

/-- The genuine fundamental-groupoid functor of the same restricted arrow is an equivalence. -/
theorem componentUnionPreimageMap_isEquivalence_mapFundamentalGroupoid
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y) (T : Set (π₀ Y))
    (hf : realizationWeakEquivalences f) :
    (SSet.mapFundamentalGroupoid (componentUnionPreimageMap f T)).IsEquivalence :=
  (componentUnionPreimageMap_W f T hf).isEquivalence_mapFundamentalGroupoid

/-- Empty and full target selectors retain the literal empty and full source unions. -/
theorem componentUnionPreimageMap_empty_univ (f : X ⟶ Y) :
    componentUnion X ((mapπ₀ f) ⁻¹' ∅) = ⊥ ∧ componentUnion Y ∅ = ⊥ ∧
      componentUnion X ((mapπ₀ f) ⁻¹' Set.univ) = ⊤ ∧
      componentUnion Y Set.univ = ⊤ := by
  simp only [Set.preimage_empty, Set.preimage_univ, componentUnion_empty,
    componentUnion_univ, and_self]

/-- An empty target selector introduces no selected simplex, in any degree. -/
theorem componentUnionPreimageMap_empty_source (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    IsEmpty ((componentUnion X ((mapπ₀ f) ⁻¹' ∅) : SSet.{u}).obj n) := by
  refine ⟨fun q => ?_⟩
  have hq := (mem_componentUnion X ((mapπ₀ f) ⁻¹' ∅) n q.val).mp q.property
  exact hq

/-- The empty restriction is the unique map from its original empty source. -/
theorem componentUnionPreimageMap_empty_unique (f : X ⟶ Y)
    (g : (componentUnion X ((mapπ₀ f) ⁻¹' ∅) : SSet.{u}) ⟶
      (componentUnion Y ∅ : SSet.{u})) :
    g = componentUnionPreimageMap f ∅ := by
  ext n q
  have hq := (mem_componentUnion X ((mapπ₀ f) ⁻¹' ∅) n q.val).mp q.property
  exact False.elim hq

/-- For a weak original arrow, the preimage of its original image singleton is that singleton. -/
theorem componentUnionPreimageMap_singleton_selector (f : X ⟶ Y)
    (hf : realizationWeakEquivalences f) (c : π₀ X) :
    (mapπ₀ f) ⁻¹' {mapπ₀ f c} = {c} := by
  ext d
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact ⟨fun h => hf.bijective_mapπ₀.1 h, fun h => congrArg (mapπ₀ f) h⟩

/-- Both singleton unions are the same original native component subcomplexes. -/
theorem componentUnionPreimageMap_singleton (f : X ⟶ Y)
    (hf : realizationWeakEquivalences f) (c : π₀ X) :
    componentUnion X ((mapπ₀ f) ⁻¹' {mapπ₀ f c}) = π₀.component c ∧
      componentUnion Y {mapπ₀ f c} = π₀.component (mapπ₀ f c) := by
  constructor
  · rw [componentUnionPreimageMap_singleton_selector f hf c, componentUnion_singleton]
  · exact componentUnion_singleton Y (mapπ₀ f c)

/-- The original full source is identified with X by its canonical full-subcomplex isomorphism. -/
def componentUnionPreimageSourceUnivIso (f : X ⟶ Y) :
    (componentUnion X ((mapπ₀ f) ⁻¹' Set.univ) : SSet.{u}) ≅ X :=
  Subcomplex.eqToIso (by rw [Set.preimage_univ, componentUnion_univ]) ≪≫
    Subcomplex.topIso X

/-- The original full target is identified with Y by its canonical full-subcomplex isomorphism. -/
def componentUnionPreimageTargetUnivIso (Y : SSet.{u}) :
    (componentUnion Y Set.univ : SSet.{u}) ≅ Y :=
  Subcomplex.eqToIso (componentUnion_univ Y) ≪≫ Subcomplex.topIso Y

@[simp]
theorem componentUnionPreimageSourceUnivIso_hom (f : X ⟶ Y) :
    (componentUnionPreimageSourceUnivIso f).hom =
      (componentUnion X ((mapπ₀ f) ⁻¹' Set.univ)).ι := by
  simp only [componentUnionPreimageSourceUnivIso, Iso.trans_hom,
    Subcomplex.eqToIso_hom, Subcomplex.topIso_hom, Subcomplex.homOfLE_ι]

@[simp]
theorem componentUnionPreimageTargetUnivIso_hom (Y : SSet.{u}) :
    (componentUnionPreimageTargetUnivIso Y).hom = (componentUnion Y Set.univ).ι := by
  simp only [componentUnionPreimageTargetUnivIso, Iso.trans_hom,
    Subcomplex.eqToIso_hom, Subcomplex.topIso_hom, Subcomplex.homOfLE_ι]

/-- Under the two actual full-subcomplex isomorphisms, the restriction is the original f. -/
theorem componentUnionPreimageMap_univ (f : X ⟶ Y) :
    componentUnionPreimageMap f Set.univ ≫ (componentUnionPreimageTargetUnivIso Y).hom =
      (componentUnionPreimageSourceUnivIso f).hom ≫ f := by
  rw [componentUnionPreimageTargetUnivIso_hom,
    componentUnionPreimageSourceUnivIso_hom, componentUnionPreimageMap_ι]

/-- The exact singleton source has its original native component as its canonical identification. -/
def componentUnionPreimageSourceSingletonIso (f : X ⟶ Y)
    (hf : realizationWeakEquivalences f) (c : π₀ X) :
    (componentUnion X ((mapπ₀ f) ⁻¹' {mapπ₀ f c}) : SSet.{u}) ≅
      (π₀.component c : SSet.{u}) :=
  Subcomplex.eqToIso (componentUnionPreimageMap_singleton f hf c).1

/-- The exact singleton target has its original native component as its canonical identification. -/
def componentUnionPreimageTargetSingletonIso (f : X ⟶ Y) (c : π₀ X) :
    (componentUnion Y {mapπ₀ f c} : SSet.{u}) ≅ (π₀.component (mapπ₀ f c) : SSet.{u}) :=
  Subcomplex.eqToIso (componentUnion_singleton Y (mapπ₀ f c))

/-- The two original singleton component inclusions preserve the same original f. -/
theorem componentUnionPreimageMap_singleton_ι (f : X ⟶ Y)
    (hf : realizationWeakEquivalences f) (c : π₀ X) :
    componentUnionPreimageMap f {mapπ₀ f c} ≫
        (componentUnionPreimageTargetSingletonIso f c).hom ≫
          (π₀.component (mapπ₀ f c)).ι =
      (componentUnionPreimageSourceSingletonIso f hf c).hom ≫ (π₀.component c).ι ≫ f := by
  simp only [componentUnionPreimageTargetSingletonIso,
    componentUnionPreimageSourceSingletonIso, Subcomplex.eqToIso_hom,
    Subcomplex.homOfLE_ι, Subcomplex.homOfLE_ι_assoc]
  exact componentUnionPreimageMap_ι f {mapπ₀ f c}

/-- The identity preimage selector is the original selector, with its literal equality. -/
theorem componentUnionPreimageMap_id_selector (X : SSet.{u}) (T : Set (π₀ X)) :
    componentUnion X ((mapπ₀ (𝟙 X)) ⁻¹' T) = componentUnion X T := by
  congr 1
  ext c
  simp only [Set.mem_preimage, mapπ₀_id_apply]

/-- The identity restriction is the canonical identification of its actual source. -/
theorem componentUnionPreimageMap_id (X : SSet.{u}) (T : Set (π₀ X)) :
    componentUnionPreimageMap (𝟙 X) T =
      (Subcomplex.eqToIso (componentUnionPreimageMap_id_selector X T)).hom := by
  apply (cancel_mono (componentUnion X T).ι).mp
  rw [componentUnionPreimageMap_ι, Category.comp_id]
  rw [Subcomplex.eqToIso_hom, Subcomplex.homOfLE_ι]

/-- Composition retains the exact iterated original preimage selector. -/
theorem componentUnionPreimageMap_comp_selector {Z : SSet.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (T : Set (π₀ Z)) :
    componentUnion X ((mapπ₀ (f ≫ g)) ⁻¹' T) =
      componentUnion X ((mapπ₀ f) ⁻¹' ((mapπ₀ g) ⁻¹' T)) := by
  congr 1
  ext c
  simp only [Set.mem_preimage, mapπ₀_comp_apply]

/-- With the actual selector identification, restriction preserves original composition. -/
theorem componentUnionPreimageMap_comp {Z : SSet.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (T : Set (π₀ Z)) :
    componentUnionPreimageMap (f ≫ g) T =
      (Subcomplex.eqToIso (componentUnionPreimageMap_comp_selector f g T)).hom ≫
        componentUnionPreimageMap f ((mapπ₀ g) ⁻¹' T) ≫ componentUnionPreimageMap g T := by
  apply (cancel_mono (componentUnion Z T).ι).mp
  simp only [Category.assoc, componentUnionPreimageMap_ι, componentUnionPreimageMap_ι_assoc,
    Subcomplex.eqToIso_hom, Subcomplex.homOfLE_ι_assoc]

end SSet
