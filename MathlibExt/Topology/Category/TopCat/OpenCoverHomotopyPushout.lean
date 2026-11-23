/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SubordinateCoverWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence
public import MathlibExt.AlgebraicTopology.SingularHomology.SmallChains.TwoSet
public import MathlibExt.AlgebraicTopology.SingularHomology.Subspace.Basic
public import Mathlib.Topology.Sets.OpenCover
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantSpanReplacement

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube

/-!
# A concrete homotopy pushout model for a two-set open cover

The singular simplices contained in the two members form subcomplexes. Their
intersection and union give a simplicial pushout. Realization preserves that
pushout and sends its mono legs to cofibrations. The realized union maps to
the covered space by the actual inclusion followed by the singular counit;
singular subdivision proves that this comparison is weak for an open cover.

The three realized subcomplexes evaluate weakly to the actual subspaces.
The union comparison is natural under maps preserving the two members.
These are homotopy excision data. A homotopy-fiber gluing theorem is still
needed for the two-open-set quasifibration criterion.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen TopCat.modelCategory

universe u

namespace TopCat

private def singularSubspaceIso {X : TopCat.{u}} (W : Set X) :
    TopCat.toSSet.obj (TopCat.of W) ≅
      (AlgebraicTopology.subordinateSet W : SSet.{u}) :=
  asIso (SSet.Subcomplex.toRange
    (TopCat.toSSet.map (AlgebraicTopology.subspaceIncl W))) ≪≫
      SSet.Subcomplex.eqToIso
        (AlgebraicTopology.range_subspaceIncl_eq_subordinateSet W)

private theorem singularSubspaceIso_hom_ι {X : TopCat.{u}} (W : Set X) :
    (singularSubspaceIso W).hom ≫ (AlgebraicTopology.subordinateSet W).ι =
      TopCat.toSSet.map (AlgebraicTopology.subspaceIncl W) := by
  simp [singularSubspaceIso]

/-- The realization of singular simplices contained in a given subspace. -/
abbrev realizedSubordinateSet {X : TopCat.{u}} (W : Set X) : TopCat.{u} :=
  SSet.toTop.obj (AlgebraicTopology.subordinateSet W : SSet.{u})

/-- Actual evaluation into the subspace, using the canonical singular range
isomorphism and the singular counit of that subspace. -/
def realizedSubordinateSetEvaluation {X : TopCat.{u}} (W : Set X) :
    realizedSubordinateSet W ⟶ TopCat.of W :=
  SSet.toTop.map (singularSubspaceIso W).inv ≫ sSetTopAdj.counit.app (TopCat.of W)

/-- Evaluation retains the actual inclusion into the ambient space. -/
@[reassoc (attr := simp)]
theorem realizedSubordinateSetEvaluation_inclusion {X : TopCat.{u}} (W : Set X) :
    realizedSubordinateSetEvaluation W ≫ AlgebraicTopology.subspaceIncl W =
      SSet.toTop.map (AlgebraicTopology.subordinateSet W).ι ≫
        sSetTopAdj.counit.app X := by
  have hι : (singularSubspaceIso W).inv ≫
      TopCat.toSSet.map (AlgebraicTopology.subspaceIncl W) =
        (AlgebraicTopology.subordinateSet W).ι := by
    rw [← singularSubspaceIso_hom_ι W]
    simp
  have hn : sSetTopAdj.counit.app (TopCat.of W) ≫
      AlgebraicTopology.subspaceIncl W =
        SSet.toTop.map (TopCat.toSSet.map (AlgebraicTopology.subspaceIncl W)) ≫
          sSetTopAdj.counit.app X := by
    simpa only [Functor.id_map, Functor.comp_map] using
      (sSetTopAdj.counit.naturality (AlgebraicTopology.subspaceIncl W)).symm
  unfold realizedSubordinateSetEvaluation
  rw [Category.assoc, hn]
  rw [← Category.assoc, ← SSet.toTop.map_comp, hι]

/-- Evaluation into every subspace is weak, without an openness hypothesis. -/
theorem realizedSubordinateSetEvaluation_mem_weakHomotopyEquivalences
    {X : TopCat.{u}} (W : Set X) :
    weakHomotopyEquivalences (realizedSubordinateSetEvaluation W) := by
  let _ : IsIso (SSet.toTop.map (singularSubspaceIso W).inv) :=
    (SSet.toTop.mapIso (singularSubspaceIso W)).isIso_inv
  unfold realizedSubordinateSetEvaluation
  exact weakHomotopyEquivalences.comp_mem _ _
    (weakHomotopyEquivalences.of_isIso _)
    (SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences _)

/-- Realized subordinate complexes are cofibrant in the selected TopCat model. -/
theorem realizedSubordinateSet_isCofibrant {X : TopCat.{u}} (W : Set X) :
    IsCofibrant (realizedSubordinateSet W) := by
  let _ : IsCofibrant (AlgebraicTopology.subordinateSet W : SSet.{u}) :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  exact
    CategoryTheory.Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := sSetTopAdj) (inferInstance : IsCofibrant
        (AlgebraicTopology.subordinateSet W : SSet.{u}))

/-- Inclusion of realized subordinate complexes for nested subspaces. -/
@[expose]
def realizedSubordinateSetInclusion {X : TopCat.{u}} {W Z : Set X} (h : W ⊆ Z) :
    realizedSubordinateSet W ⟶ realizedSubordinateSet Z :=
  SSet.toTop.map (SSet.Subcomplex.homOfLE (AlgebraicTopology.subordinateSet_mono h))

/-- The realized inclusion is a cofibration, even when the subspace inclusion
itself need not be a cofibration. -/
theorem realizedSubordinateSetInclusion_cofibration {X : TopCat.{u}}
    {W Z : Set X} (h : W ⊆ Z) :
    Cofibration (realizedSubordinateSetInclusion h) := by
  apply (HomotopicalAlgebra.cofibration_iff _).mpr
  exact
    CategoryTheory.Adjunction.IsQuillenAdjunction.preservesCofibrations
      (adj := sSetTopAdj) _
      ((HomotopicalAlgebra.cofibration_iff _).mp
        (SSet.modelCategoryQuillen.cofibration_of_mono _))

/-- The realized inclusions evaluate to the actual subspace inclusions. -/
@[reassoc (attr := simp)]
theorem realizedSubordinateSetInclusion_evaluation {X : TopCat.{u}}
    {W Z : Set X} (h : W ⊆ Z) :
    realizedSubordinateSetInclusion h ≫ realizedSubordinateSetEvaluation Z =
      realizedSubordinateSetEvaluation W ≫ AlgebraicTopology.subspaceInclOfSubset h := by
  unfold realizedSubordinateSetInclusion
  apply (cancel_mono (AlgebraicTopology.subspaceIncl Z)).mp
  rw [Category.assoc, realizedSubordinateSetEvaluation_inclusion,
    ← Category.assoc, ← SSet.toTop.map_comp, SSet.Subcomplex.homOfLE_ι]
  rw [Category.assoc]
  have hc : AlgebraicTopology.subspaceInclOfSubset h ≫
      AlgebraicTopology.subspaceIncl Z = AlgebraicTopology.subspaceIncl W := by
    ext x
    rfl
  rw [hc, realizedSubordinateSetEvaluation_inclusion]

/-- The union of the two subordinate singular complexes, after realization. -/
abbrev realizedTwoSetCover {X : TopCat.{u}} (U V : Set X) : TopCat.{u} :=
  SSet.toTop.obj ((AlgebraicTopology.subordinateSet U ⊔
    AlgebraicTopology.subordinateSet V : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u})

/-- The two canonical maps into the realized union. -/
@[expose]
def realizedTwoSetCoverLeft {X : TopCat.{u}} (U V : Set X) :
    realizedSubordinateSet U ⟶ realizedTwoSetCover U V :=
  SSet.toTop.map (SSet.Subcomplex.homOfLE
    (show AlgebraicTopology.subordinateSet U ≤
      AlgebraicTopology.subordinateSet U ⊔ AlgebraicTopology.subordinateSet V
      from le_sup_left))

/-- The canonical map from the second member into the realized union. -/
@[expose]
def realizedTwoSetCoverRight {X : TopCat.{u}} (U V : Set X) :
    realizedSubordinateSet V ⟶ realizedTwoSetCover U V :=
  SSet.toTop.map (SSet.Subcomplex.homOfLE
    (show AlgebraicTopology.subordinateSet V ≤
      AlgebraicTopology.subordinateSet U ⊔ AlgebraicTopology.subordinateSet V
      from le_sup_right))

/-- Realization of the actual subcomplex intersection/union pushout. Its two
incoming legs are the cofibrations of realized subordinate inclusions. -/
theorem realizedTwoSetCover_isPushout {X : TopCat.{u}} (U V : Set X) :
    IsPushout
      (realizedSubordinateSetInclusion (Set.inter_subset_left : U ∩ V ⊆ U))
      (realizedSubordinateSetInclusion (Set.inter_subset_right : U ∩ V ⊆ V))
      (realizedTwoSetCoverLeft U V) (realizedTwoSetCoverRight U V) := by
  let sq : SSet.Subcomplex.BicartSq
      (AlgebraicTopology.subordinateSet (U ∩ V))
      (AlgebraicTopology.subordinateSet U) (AlgebraicTopology.subordinateSet V)
      (AlgebraicTopology.subordinateSet U ⊔ AlgebraicTopology.subordinateSet V) :=
    { sup_eq := rfl
      inf_eq := (AlgebraicTopology.subordinateSet_inter U V).symm }
  exact sq.isPushout.map SSet.toTop

/-- The actual union inclusion followed by evaluation to the ambient space. -/
@[expose]
def realizedTwoSetCoverComparison {X : TopCat.{u}} (U V : Set X) :
    realizedTwoSetCover U V ⟶ X :=
  SSet.toTop.map (AlgebraicTopology.subordinateSet U ⊔
    AlgebraicTopology.subordinateSet V).ι ≫ sSetTopAdj.counit.app X

/-- The left member comparison has its actual subspace coordinate. -/
@[reassoc (attr := simp)]
theorem realizedTwoSetCoverLeft_comparison {X : TopCat.{u}} (U V : Set X) :
    realizedTwoSetCoverLeft U V ≫ realizedTwoSetCoverComparison U V =
      realizedSubordinateSetEvaluation U ≫ AlgebraicTopology.subspaceIncl U := by
  rw [realizedSubordinateSetEvaluation_inclusion]
  unfold realizedTwoSetCoverLeft realizedTwoSetCoverComparison
  rw [← Category.assoc, ← SSet.toTop.map_comp, SSet.Subcomplex.homOfLE_ι]

/-- The right member comparison has its actual subspace coordinate. -/
@[reassoc (attr := simp)]
theorem realizedTwoSetCoverRight_comparison {X : TopCat.{u}} (U V : Set X) :
    realizedTwoSetCoverRight U V ≫ realizedTwoSetCoverComparison U V =
      realizedSubordinateSetEvaluation V ≫ AlgebraicTopology.subspaceIncl V := by
  rw [realizedSubordinateSetEvaluation_inclusion]
  unfold realizedTwoSetCoverRight realizedTwoSetCoverComparison
  rw [← Category.assoc, ← SSet.toTop.map_comp, SSet.Subcomplex.homOfLE_ι]

private def booleanOpenCover {X : TopCat.{u}} (U V : TopologicalSpace.Opens X) :
    Bool → TopologicalSpace.Opens X := fun b => if b then U else V

private theorem booleanOpenCover_isOpenCover {X : TopCat.{u}}
    (U V : TopologicalSpace.Opens X) (hcover : (U : Set X) ∪ V = Set.univ) :
    TopologicalSpace.IsOpenCover (booleanOpenCover U V) := by
  apply TopologicalSpace.IsOpenCover.of_sets
    (fun b => (booleanOpenCover U V b).isOpen)
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  have hx : x ∈ (U : Set X) ∪ V := hcover.symm ▸ Set.mem_univ x
  rcases hx with hx | hx
  · exact ⟨true, by simpa [booleanOpenCover] using hx⟩
  · exact ⟨false, by simpa [booleanOpenCover] using hx⟩

/-- Homotopy excision for an actual two-set open cover. The canonical
comparison is weak by subordinate singular subdivision and the counit. -/
theorem realizedTwoSetCoverComparison_mem_weakHomotopyEquivalences
    {X : TopCat.{u}} (U V : TopologicalSpace.Opens X)
    (hcover : (U : Set X) ∪ V = Set.univ) :
    weakHomotopyEquivalences (realizedTwoSetCoverComparison (U : Set X) V) := by
  have h := AlgebraicTopology.subordinateCover_ι_mem_realizationWeakEquivalences
    (booleanOpenCover U V) (booleanOpenCover_isOpenCover U V hcover)
  have hsets : (fun b => (booleanOpenCover U V b : Set X)) =
      AlgebraicTopology.smallCoverBoth (U : Set X) V := by
    funext b
    cases b <;> rfl
  change SSet.realizationWeakEquivalences
    (AlgebraicTopology.subordinateCover
      (fun b => (booleanOpenCover U V b : Set X))).ι at h
  rw [hsets] at h
  change SSet.realizationWeakEquivalences
    (AlgebraicTopology.subCxBoth (U : Set X) V).ι at h
  rw [AlgebraicTopology.subCxBoth_eq_sup] at h
  have hι : weakHomotopyEquivalences (SSet.toTop.map
      (AlgebraicTopology.subordinateSet (U : Set X) ⊔
        AlgebraicTopology.subordinateSet (V : Set X)).ι) := h
  exact weakHomotopyEquivalences.comp_mem _ _ hι
    (SSet.modelCategoryQuillen.counit_mem_weakHomotopyEquivalences _)

private def twoSetSubordinateMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    {U V : Set X} {U' V' : Set Y}
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    ((AlgebraicTopology.subordinateSet U ⊔ AlgebraicTopology.subordinateSet V :
      (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}) ⟶
        ((AlgebraicTopology.subordinateSet U' ⊔ AlgebraicTopology.subordinateSet V' :
          (TopCat.toSSet.obj Y).Subcomplex) : SSet.{u}) := by
  exact SSet.Subcomplex.lift
    ((AlgebraicTopology.subordinateSet U ⊔ AlgebraicTopology.subordinateSet V).ι ≫
      TopCat.toSSet.map f) (by
        rw [← SSet.Subcomplex.image_eq_range, SSet.Subcomplex.image_le_iff]
        exact sup_le
          ((SSet.Subcomplex.image_le_iff _ _ _).mp
            ((AlgebraicTopology.subordinateSet_image_le f hU).trans le_sup_left))
          ((SSet.Subcomplex.image_le_iff _ _ _).mp
            ((AlgebraicTopology.subordinateSet_image_le f hV).trans le_sup_right)))

/-- The actual induced map of the two cover realizations. -/
def realizedTwoSetCoverMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    {U V : Set X} {U' V' : Set Y}
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    realizedTwoSetCover U V ⟶ realizedTwoSetCover U' V' :=
  SSet.toTop.map (twoSetSubordinateMap f hU hV)

/-- Naturality of the actual cover comparison, including its ambient map. -/
@[reassoc (attr := simp)]
theorem realizedTwoSetCoverMap_comparison {X Y : TopCat.{u}} (f : X ⟶ Y)
    {U V : Set X} {U' V' : Set Y}
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    realizedTwoSetCoverMap f hU hV ≫ realizedTwoSetCoverComparison U' V' =
      realizedTwoSetCoverComparison U V ≫ f := by
  unfold realizedTwoSetCoverMap realizedTwoSetCoverComparison
  rw [← Category.assoc, ← SSet.toTop.map_comp]
  have hι : twoSetSubordinateMap f hU hV ≫
      (AlgebraicTopology.subordinateSet U' ⊔ AlgebraicTopology.subordinateSet V').ι =
        (AlgebraicTopology.subordinateSet U ⊔ AlgebraicTopology.subordinateSet V).ι ≫
          TopCat.toSSet.map f := by
    simp [twoSetSubordinateMap]
  rw [hι, SSet.toTop.map_comp, Category.assoc]
  exact congrArg (fun k => SSet.toTop.map
    (AlgebraicTopology.subordinateSet U ⊔ AlgebraicTopology.subordinateSet V).ι ≫ k)
      (by simpa only [Functor.id_map, Functor.comp_map] using
        sSetTopAdj.counit.naturality f)

private def twoOpenSetsDesc {X : TopCat.{u}} (U V : TopologicalSpace.Opens X)
    (hcover : (U : Set X) ∪ V = Set.univ)
    (s : PushoutCocone
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_left : (U : Set X) ∩ V ⊆ U))
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_right : (U : Set X) ∩ V ⊆ V))) : C(X, s.pt) := by
  let φ : (b : Bool) → C((booleanOpenCover U V b : Set X), s.pt) := fun b => by
    cases b
    · exact s.inr.hom
    · exact s.inl.hom
  exact ContinuousMap.liftCover
    (fun b => (booleanOpenCover U V b : Set X)) φ (by
      intro i j x hxi hxj
      cases i <;> cases j
      · rfl
      · exact (ConcreteCategory.congr_hom s.condition ⟨x, hxj, hxi⟩).symm
      · exact ConcreteCategory.congr_hom s.condition ⟨x, hxi, hxj⟩
      · rfl)
    (booleanOpenCover_isOpenCover U V hcover).exists_mem_nhds

private theorem twoOpenSetsDesc_left {X : TopCat.{u}}
    (U V : TopologicalSpace.Opens X) (hcover : (U : Set X) ∪ V = Set.univ)
    (s : PushoutCocone
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_left : (U : Set X) ∩ V ⊆ U))
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_right : (U : Set X) ∩ V ⊆ V))) (x : TopCat.of (U : Set X)) :
    twoOpenSetsDesc U V hcover s x = s.inl x := by
  unfold twoOpenSetsDesc
  exact ContinuousMap.liftCover_coe
    (S := fun b => (booleanOpenCover U V b : Set X)) (i := true) x

private theorem twoOpenSetsDesc_right {X : TopCat.{u}}
    (U V : TopologicalSpace.Opens X) (hcover : (U : Set X) ∪ V = Set.univ)
    (s : PushoutCocone
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_left : (U : Set X) ∩ V ⊆ U))
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_right : (U : Set X) ∩ V ⊆ V))) (x : TopCat.of (V : Set X)) :
    twoOpenSetsDesc U V hcover s x = s.inr x := by
  unfold twoOpenSetsDesc
  exact ContinuousMap.liftCover_coe
    (S := fun b => (booleanOpenCover U V b : Set X)) (i := false) x

/-- The actual subspaces of a two-set open cover form a topological pushout.
The universal map is obtained by gluing continuous maps on the two opens. -/
theorem isPushout_twoSetOpenCover {X : TopCat.{u}}
    (U V : TopologicalSpace.Opens X) (hcover : (U : Set X) ∪ V = Set.univ) :
    IsPushout
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_left : (U : Set X) ∩ V ⊆ U))
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_right : (U : Set X) ∩ V ⊆ V))
      (AlgebraicTopology.subspaceIncl (U : Set X))
      (AlgebraicTopology.subspaceIncl (V : Set X)) := by
  let comm : CommSq
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_left : (U : Set X) ∩ V ⊆ U))
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_right : (U : Set X) ∩ V ⊆ V))
      (AlgebraicTopology.subspaceIncl (U : Set X))
      (AlgebraicTopology.subspaceIncl (V : Set X)) := ⟨by ext x; rfl⟩
  apply IsPushout.of_isColimit' comm
  apply PushoutCocone.isColimitAux'
  intro s
  let d : X ⟶ s.pt := TopCat.ofHom (twoOpenSetsDesc U V hcover s)
  refine ⟨d, ?_, ?_, ?_⟩
  · ext x
    exact twoOpenSetsDesc_left U V hcover s x
  · ext x
    exact twoOpenSetsDesc_right U V hcover s x
  · intro m hleft hright
    ext x
    have hx : x ∈ (U : Set X) ∪ V := hcover.symm ▸ Set.mem_univ x
    rcases hx with hx | hx
    · exact (ConcreteCategory.congr_hom hleft ⟨x, hx⟩).trans
        (twoOpenSetsDesc_left U V hcover s ⟨x, hx⟩).symm
    · exact (ConcreteCategory.congr_hom hright ⟨x, hx⟩).trans
        (twoOpenSetsDesc_right U V hcover s ⟨x, hx⟩).symm

/-- The actual comparison from any standard cofibrant replacement of the
native open-cover span to the covered space. -/
def cofibrantSpanReplacementOpenCoverComparison {X : TopCat.{u}}
    (U V : TopologicalSpace.Opens X) (hcover : (U : Set X) ∪ V = Set.univ)
    (R : CofibrantSpanReplacement (span
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_left : (U : Set X) ∩ V ⊆ U))
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_right : (U : Set X) ∩ V ⊆ V)))) :
    R.pushoutObj ⟶ X :=
  R.toPushout ≫ (isPushout_twoSetOpenCover U V hcover).isoPushout.inv

/-- The replacement comparison has the actual left inclusion coordinate. -/
@[reassoc (attr := simp)]
theorem cofibrantSpanReplacementOpenCoverComparison_left {X : TopCat.{u}}
    (U V : TopologicalSpace.Opens X) (hcover : (U : Set X) ∪ V = Set.univ)
    (R : CofibrantSpanReplacement (span
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_left : (U : Set X) ∩ V ⊆ U))
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_right : (U : Set X) ∩ V ⊆ V)))) :
    colimit.ι R.Q WalkingSpan.left ≫
        cofibrantSpanReplacementOpenCoverComparison U V hcover R =
      R.counit.app WalkingSpan.left ≫ AlgebraicTopology.subspaceIncl (U : Set X) := by
  unfold cofibrantSpanReplacementOpenCoverComparison
  rw [← Category.assoc, R.inl_toPushout, Category.assoc]
  exact congrArg (fun k => R.counit.app WalkingSpan.left ≫ k)
    (isPushout_twoSetOpenCover U V hcover).inl_isoPushout_inv

/-- The replacement comparison has the actual right inclusion coordinate. -/
@[reassoc (attr := simp)]
theorem cofibrantSpanReplacementOpenCoverComparison_right {X : TopCat.{u}}
    (U V : TopologicalSpace.Opens X) (hcover : (U : Set X) ∪ V = Set.univ)
    (R : CofibrantSpanReplacement (span
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_left : (U : Set X) ∩ V ⊆ U))
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_right : (U : Set X) ∩ V ⊆ V)))) :
    colimit.ι R.Q WalkingSpan.right ≫
        cofibrantSpanReplacementOpenCoverComparison U V hcover R =
      R.counit.app WalkingSpan.right ≫ AlgebraicTopology.subspaceIncl (V : Set X) := by
  unfold cofibrantSpanReplacementOpenCoverComparison
  rw [← Category.assoc, R.inr_toPushout, Category.assoc]
  exact congrArg (fun k => R.counit.app WalkingSpan.right ≫ k)
    (isPushout_twoSetOpenCover U V hcover).inr_isoPushout_inv

/-- The native open-cover square is homotopy cocartesian. For every standard
cofibrant span replacement its actual comparison to the covered space is weak.
The proof uses subordinate singular subdivision and cofibrant pushout gluing. -/
theorem cofibrantSpanReplacementOpenCoverComparison_mem_weakHomotopyEquivalences
    {X : TopCat.{u}} (U V : TopologicalSpace.Opens X)
    (hcover : (U : Set X) ∪ V = Set.univ)
    (R : CofibrantSpanReplacement (span
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_left : (U : Set X) ∩ V ⊆ U))
      (AlgebraicTopology.subspaceInclOfSubset
        (Set.inter_subset_right : (U : Set X) ∩ V ⊆ V)))) :
    weakHomotopyEquivalences (cofibrantSpanReplacementOpenCoverComparison U V hcover R) := by
  let qfst := realizedSubordinateSetInclusion
    (Set.inter_subset_left : (U : Set X) ∩ V ⊆ U)
  let qsnd := realizedSubordinateSetInclusion
    (Set.inter_subset_right : (U : Set X) ∩ V ⊆ V)
  let _ : Cofibration qfst := realizedSubordinateSetInclusion_cofibration _
  let _ : Cofibration qsnd := realizedSubordinateSetInclusion_cofibration _
  let _ : IsCofibrant (realizedSubordinateSet ((U : Set X) ∩ V)) :=
    realizedSubordinateSet_isCofibrant _
  let _ : IsCofibrant (realizedSubordinateSet (V : Set X)) :=
    realizedSubordinateSet_isCofibrant _
  let _ : IsCofibrant (R.Q.obj WalkingSpan.zero) := R.isCofibrant_zero
  let _ : Cofibration (R.Q.map WalkingSpan.Hom.fst) := R.cofibration_fst
  let _ : Cofibration (R.Q.map WalkingSpan.Hom.snd) := R.cofibration_snd
  let _ : IsCofibrant (R.Q.obj WalkingSpan.right) :=
    isCofibrant_of_cofibration (R.Q.map WalkingSpan.Hom.snd)
  have hR0 := (mem_trivialFibrations_iff _).mp
    (R.counit_app_mem_trivialFibrations WalkingSpan.zero)
  have hRL := (mem_trivialFibrations_iff _).mp
    (R.counit_app_mem_trivialFibrations WalkingSpan.left)
  have hRR := (mem_trivialFibrations_iff _).mp
    (R.counit_app_mem_trivialFibrations WalkingSpan.right)
  let _ : Fibration (R.counit.app WalkingSpan.zero) := hR0.1
  let _ : WeakEquivalence (R.counit.app WalkingSpan.zero) := hR0.2
  let _ : Fibration (R.counit.app WalkingSpan.left) := hRL.1
  let _ : WeakEquivalence (R.counit.app WalkingSpan.left) := hRL.2
  let _ : Fibration (R.counit.app WalkingSpan.right) := hRR.1
  let _ : WeakEquivalence (R.counit.app WalkingSpan.right) := hRR.2
  have hEval (W : Set X) : WeakEquivalence (realizedSubordinateSetEvaluation W) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      (realizedSubordinateSetEvaluation_mem_weakHomotopyEquivalences W)
  let _ : WeakEquivalence (realizedSubordinateSetEvaluation ((U : Set X) ∩ V)) := hEval _
  let _ : WeakEquivalence (realizedSubordinateSetEvaluation (U : Set X)) := hEval _
  let _ : WeakEquivalence (realizedSubordinateSetEvaluation (V : Set X)) := hEval _
  let sq0 : CommSq (initial.to _) (initial.to _)
      (R.counit.app WalkingSpan.zero)
      (realizedSubordinateSetEvaluation ((U : Set X) ∩ V)) := .mk
  let z := sq0.lift
  let sqL : CommSq (z ≫ R.Q.map WalkingSpan.Hom.fst) qfst
      (R.counit.app WalkingSpan.left) (realizedSubordinateSetEvaluation (U : Set X)) := ⟨by
    rw [Category.assoc, R.counit.naturality, ← Category.assoc, sq0.fac_right]
    exact (realizedSubordinateSetInclusion_evaluation Set.inter_subset_left).symm⟩
  let l := sqL.lift
  let sqR : CommSq (z ≫ R.Q.map WalkingSpan.Hom.snd) qsnd
      (R.counit.app WalkingSpan.right) (realizedSubordinateSetEvaluation (V : Set X)) := ⟨by
    rw [Category.assoc, R.counit.naturality, ← Category.assoc, sq0.fac_right]
    exact (realizedSubordinateSetInclusion_evaluation Set.inter_subset_right).symm⟩
  let r := sqR.lift
  let _ : WeakEquivalence z := weakEquivalence_of_postcomp_of_fac sq0.fac_right
  let _ : WeakEquivalence l := weakEquivalence_of_postcomp_of_fac sqL.fac_right
  let _ : WeakEquivalence r := weakEquivalence_of_postcomp_of_fac sqR.fac_right
  let sigma := realizedTwoSetCover_isPushout (U : Set X) (V : Set X)
  let rho := IsPushout.of_isColimit_cocone (colimit.isColimit R.Q)
  have hrho : R.Q.map WalkingSpan.Hom.fst ≫ colimit.ι R.Q WalkingSpan.left =
      R.Q.map WalkingSpan.Hom.snd ≫ colimit.ι R.Q WalkingSpan.right := rho.w
  have w : qfst ≫ (l ≫ colimit.ι R.Q WalkingSpan.left) =
      qsnd ≫ (r ≫ colimit.ι R.Q WalkingSpan.right) := by
    rw [← Category.assoc, sqL.fac_left, Category.assoc, hrho,
      ← Category.assoc, ← sqR.fac_left, Category.assoc]
  let k : realizedTwoSetCover (U : Set X) V ⟶ R.pushoutObj :=
    sigma.desc (l ≫ colimit.ι R.Q WalkingSpan.left)
      (r ≫ colimit.ι R.Q WalkingSpan.right) w
  have hk : WeakEquivalence k :=
    weakEquivalence_map_of_isPushouts_of_cofibrant sigma rho sqL.fac_left sqR.fac_left
      (sigma.inl_desc _ _ w) (sigma.inr_desc _ _ w)
  have hfac : k ≫ cofibrantSpanReplacementOpenCoverComparison U V hcover R =
      realizedTwoSetCoverComparison (U : Set X) V := by
    apply sigma.hom_ext
    · rw [sigma.inl_desc_assoc, Category.assoc,
        cofibrantSpanReplacementOpenCoverComparison_left,
        ← Category.assoc, sqL.fac_right, realizedTwoSetCoverLeft_comparison]
    · rw [sigma.inr_desc_assoc, Category.assoc,
        cofibrantSpanReplacementOpenCoverComparison_right,
        ← Category.assoc, sqR.fac_right, realizedTwoSetCoverRight_comparison]
  have hkW : weakHomotopyEquivalences k :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mp hk
  have hcomp : weakHomotopyEquivalences
      (k ≫ cofibrantSpanReplacementOpenCoverComparison U V hcover R) := by
    rw [hfac]
    exact realizedTwoSetCoverComparison_mem_weakHomotopyEquivalences U V hcover
  exact weakHomotopyEquivalences.of_precomp _ _ hkW hcomp

end TopCat
