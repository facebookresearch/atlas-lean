/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexResolution
public import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexWeakEquivalences
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanHomotopyPullback
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakPiZero
public import MathlibExt.AlgebraicTopology.SimplicialSet.SimplexResolutionAugmentationWeakEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomotopyInvariance
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointComparison

/-!
# Actual transitions of a simplex-pullback fibration diagram

The standard-simplex point maps are derived from the existing finite-ordinal
nerve contraction. Every actual transition square is a pullback, and existing
right properness derives its weak equivalence from the given fibration.
These are the same canonical generic calculations used privately in the
homotopy-fiber owner; this neutral API serves relative coefficient maps too.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra AlgebraicTopology
open scoped Simplicial SSet.modelCategoryQuillen

universe u

public section

namespace SSet

/-- The transition square is the actual pullback square over the simplex map. -/
theorem simplexPullbackTransition_isPullback {E B : SSet.{u}} (p : E ⟶ B)
    {s t : SSet.SimplexIndex B} (a : s ⟶ t) :
    IsPullback ((SSet.simplexPullbackDiagram p).map a)
      (pullback.snd p s.hom) (pullback.snd p t.hom) (SSet.stdSimplex.map a.left) := by
  have hout : IsPullback
      ((SSet.simplexPullbackDiagram p).map a ≫ pullback.fst p t.hom)
      (pullback.snd p s.hom) p (SSet.stdSimplex.map a.left ≫ t.hom) := by
    rw [SSet.simplexPullbackDiagram_map_fst, CostructuredArrow.w a]
    exact IsPullback.of_hasPullback p s.hom
  exact hout.of_right (SSet.simplexPullbackDiagram_map_snd p a)
    (IsPullback.of_hasPullback p t.hom)

/-- Right properness derives every actual Kan-fibration simplex transition. -/
theorem simplexPullbackTransition_mem_realizationWeakEquivalences {E B : SSet.{u}} (p : E ⟶ B)
    [Fibration p]
    {s t : SSet.SimplexIndex B} (a : s ⟶ t) :
    SSet.realizationWeakEquivalences ((SSet.simplexPullbackDiagram p).map a) := by
  let theta : (SSet.stdSimplex.obj s.left : SSet.{u}) ⟶ SSet.stdSimplex.obj t.left :=
    SSet.stdSimplex.map a.left
  have hWeak : WeakEquivalence theta :=
    (weakEquivalence_iff theta).mpr (stdSimplex_map_mem_realizationWeakEquivalences theta)
  have hFib : Fibration (pullback.snd p t.hom) :=
    SSet.fibration_of_isPullback (IsPullback.of_hasPullback p t.hom).flip
  have hw : WeakEquivalence ((SSet.simplexPullbackDiagram p).map a) :=
    @IsRightProper.weakEquivalence_of_isPullback SSet.{u} _ _ _ _
      _ _ _ _ (pullback.snd p s.hom) ((SSet.simplexPullbackDiagram p).map a)
      theta (pullback.snd p t.hom) (simplexPullbackTransition_isPullback p a).flip hFib hWeak
  exact (weakEquivalence_iff _).mp hw

/-- Connectedness of the original simplicial set gives connectedness of its actual groupoid. -/
theorem fundamentalGroupoid_category_isConnected (X : SSet.{u}) [X.IsConnected] :
    CategoryTheory.IsConnected (SSet.FundamentalGroupoid X) := by
  let : Nonempty (SSet.FundamentalGroupoid X) :=
    ⟨SSet.FundamentalGroupoid.mk (Classical.arbitrary (X _⦋0⦌))⟩
  apply CategoryTheory.zigzag_isConnected
  intro a b
  obtain ⟨x, rfl⟩ := SSet.FundamentalGroupoid.mk_surjective a
  obtain ⟨y, rfl⟩ := SSet.FundamentalGroupoid.mk_surjective b
  have h : SSet.π₀.mk x = SSet.π₀.mk y := Subsingleton.elim _ _
  rw [SSet.π₀.mk_eq_mk_iff] at h
  have hm : Nonempty (SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk y) := by
    induction h with
    | rel _ _ h => exact ⟨SSet.FundamentalGroupoid.homMk h.some⟩
    | refl => exact ⟨𝟙 _⟩
    | symm _ _ _ ih => exact ⟨inv ih.some⟩
    | trans _ _ _ _ _ ih₁ ih₂ => exact ⟨ih₁.some ≫ ih₂.some⟩
  exact CategoryTheory.Zigzag.of_hom hm.some

private def identitySimplexDiagramToPoint (B : SSet.{u}) :
    simplexPullbackDiagram (𝟙 B) ⟶ bkPointDiagram (SimplexIndex B) where
  app s := SSet.stdSimplex.isTerminalObj₀.from ((simplexPullbackDiagram (𝟙 B)).obj s)
  naturality := fun {s t} a => by
    change (simplexPullbackDiagram (𝟙 B)).map a ≫
      SSet.stdSimplex.isTerminalObj₀.from ((simplexPullbackDiagram (𝟙 B)).obj t) =
      SSet.stdSimplex.isTerminalObj₀.from ((simplexPullbackDiagram (𝟙 B)).obj s) ≫ 𝟙 _
    rw [Category.comp_id]
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem identitySimplexDiagramToPoint_app_weak (B : SSet.{u}) (s : SimplexIndex B) :
    realizationWeakEquivalences ((identitySimplexDiagramToPoint B).app s) := by
  let f := pullback.snd (𝟙 B) s.hom
  have hPullback := IsPullback.of_hasPullback (𝟙 B) s.hom
  let : IsIso f := hPullback.isIso_snd_of_isIso (inferInstance : IsIso (𝟙 B))
  have h : f ≫ stdSimplex.isTerminalObj₀.from (stdSimplex.obj s.left) =
      (identitySimplexDiagramToPoint B).app s := stdSimplex.isTerminalObj₀.hom_ext _ _
  exact h ▸ realizationWeakEquivalences.comp_mem _ _
    (realizationWeakEquivalences.of_isIso f)
    (stdSimplex_to_point_mem_realizationWeakEquivalences s.left)

/-- The actual simplex-resolution span derives connectedness of the simplex-index nerve. -/
theorem simplexIndexNerve_isConnected (B : SSet.{u}) [B.IsConnected] :
    (CategoryTheory.nerve (SimplexIndex B)).IsConnected := by
  let Z := simplexResolution (𝟙 B)
  let a := simplexResolutionAugmentation (𝟙 B)
  let b := bkHocolimMap (identitySimplexDiagramToPoint B) ≫ (bkPointIsoNerve (SimplexIndex B)).hom
  have ha : realizationWeakEquivalences a :=
      simplexResolutionAugmentation_mem_realizationWeakEquivalences _
  have hb : realizationWeakEquivalences b := realizationWeakEquivalences.comp_mem _ _
    (bkHocolimMap_mem_realizationWeakEquivalences (identitySimplexDiagramToPoint B)
      (identitySimplexDiagramToPoint_app_weak B)) (realizationWeakEquivalences.of_isIso _)
  let eA := Equiv.ofBijective (mapπ₀ a)
    (SSet.realizationWeakEquivalences.bijective_mapπ₀ (f := a) ha)
  let eB := Equiv.ofBijective (mapπ₀ b)
    (SSet.realizationWeakEquivalences.bijective_mapπ₀ (f := b) hb)
  apply (SSet.isConnected_iff (X := CategoryTheory.nerve (SimplexIndex B))).mpr
  constructor
  · constructor
    intro x y
    apply eB.symm.injective
    apply eA.injective
    exact Subsingleton.elim _ _
  · have hπ : Nonempty (π₀ (CategoryTheory.nerve (SimplexIndex B))) :=
      ⟨eB (eA.symm (Classical.arbitrary (π₀ B)))⟩
    exact (π₀.nonempty_iff _).mp hπ

end SSet
