/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.PathModelCategory
public import MathlibExt.Topology.Category.TopCat.HomotopyPullback
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberHomotopySquare
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import Mathlib.Topology.Homotopy.TopCat.Basic
import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.ContinuousWhitehead
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence
import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyRelOverTrivialFibration
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyRelAtVertex

/-!
# Based inverses of continuous weak maps between simplicial realizations

An arbitrary continuous weak homotopy equivalence between actual realizations,
carrying a specified realized vertex to another specified realized vertex,
has a based inverse and both point-relative inverse homotopies. The inverse
is obtained from the actual compact-open endpoint homotopy pullback. Its two
relative homotopies use the same based section. The ordinary equivalence
retains the exact original forward map.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Topology
open scoped Simplicial TopCat.modelCategory SSet.modelCategoryQuillen
open MonoidalCategory MonoidalClosed CartesianMonoidalCategory Opposite

universe u

namespace TopCat.RealizedBasedWhitehead

variable {X Y : TopCat.{u}}

private abbrev endpointPathSpace (f : X ⟶ Y) : TopCat.{u} :=
  TopCat.homotopyPullback f (𝟙 Y)

private abbrev endpointPathPair (f : X ⟶ Y) : endpointPathSpace f ⟶ X ⨯ Y :=
  pullback.fst (prod.map f (𝟙 Y)) (TopCat.pathEndpoints Y)

private abbrev endpointPathFamily (f : X ⟶ Y) :
    endpointPathSpace f ⟶ TopCat.pathObject Y :=
  TopCat.homotopyPullbackPath f (𝟙 Y)

private abbrev endpointPathSource (f : X ⟶ Y) : endpointPathSpace f ⟶ X :=
  TopCat.homotopyPullbackLeft f (𝟙 Y)

private abbrev endpointPathTarget (f : X ⟶ Y) : endpointPathSpace f ⟶ Y :=
  TopCat.homotopyPullbackRight f (𝟙 Y)

private theorem endpointPathFamily_zero (f : X ⟶ Y) :
    endpointPathSource f ≫ f = endpointPathFamily f ≫ TopCat.pathEvalZero Y :=
  (TopCat.homotopyPullbackPath_evalZero f (𝟙 Y)).symm

private theorem endpointPathFamily_one (f : X ⟶ Y) :
    endpointPathTarget f = endpointPathFamily f ≫ TopCat.pathEvalOne Y := by
  simpa only [Category.comp_id] using
    (TopCat.homotopyPullbackPath_evalOne f (𝟙 Y)).symm

private def endpointPathInclusion (f : X ⟶ Y) : X ⟶ endpointPathSpace f :=
  pullback.lift (prod.lift (𝟙 X) f) (f ≫ TopCat.pathConstant Y) (by
    apply prod.hom_ext
    · simp [TopCat.pathEndpoints, Category.assoc]
    · simp [TopCat.pathEndpoints, Category.assoc])

private theorem endpointPathInclusion_source (f : X ⟶ Y) :
    endpointPathInclusion f ≫ endpointPathSource f = 𝟙 X := by
  simp [endpointPathInclusion, endpointPathSource]

private theorem endpointPathInclusion_target (f : X ⟶ Y) :
    endpointPathInclusion f ≫ endpointPathTarget f = f := by
  simp [endpointPathInclusion, endpointPathTarget]

private theorem endpointPathInclusion_path (f : X ⟶ Y) :
    endpointPathInclusion f ≫ endpointPathFamily f = f ≫ TopCat.pathConstant Y := by
  rw [endpointPathInclusion, pullback.lift_snd]

private theorem endpointPathSource_isPullback (f : X ⟶ Y) :
    IsPullback (endpointPathSource f) (endpointPathFamily f)
      f (TopCat.pathEvalZero Y) := by
  refine { w := endpointPathFamily_zero f, isLimit' := ?_ }
  refine ⟨PullbackCone.IsLimit.mk (endpointPathFamily_zero f)
    (fun c => pullback.lift
      (prod.lift c.fst (c.snd ≫ TopCat.pathEvalOne Y)) c.snd ?_)
    (fun c => ?_) (fun c => by rw [pullback.lift_snd])
    (fun c m h₁ h₂ => ?_)⟩
  · apply prod.hom_ext
    · simpa [TopCat.pathEndpoints, Category.assoc] using c.condition
    · simp [TopCat.pathEndpoints]
  · simp [endpointPathSource]
  · apply pullback.hom_ext
    · apply prod.hom_ext
      · simpa [endpointPathSource, Category.assoc] using h₁
      · simpa only [Category.assoc, pullback.lift_fst_assoc, prod.lift_snd] using
          (show m ≫ endpointPathTarget f = c.snd ≫ TopCat.pathEvalOne Y from by
            rw [endpointPathFamily_one f, ← Category.assoc, h₂])
    · simpa only [pullback.lift_snd] using h₂

private theorem endpointPathPair_fibration (f : X ⟶ Y) :
    Fibration (endpointPathPair f) := by
  let _ : Fibration (TopCat.pathEndpoints Y) :=
    TopCat.modelCategory.pathEndpoints_fibration Y
  apply (fibration_iff _).mpr
  exact MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (prod.map f (𝟙 Y)) (TopCat.pathEndpoints Y)).flip
    (mem_fibrations (TopCat.pathEndpoints Y))

private theorem endpointPathTarget_fibration (f : X ⟶ Y) :
    Fibration (endpointPathTarget f) := by
  let _ : Fibration (endpointPathPair f) := endpointPathPair_fibration f
  let _ : IsFibrant X := SSet.RealizationCWUpgrade.allTopCatObjectsFibrant X
  change Fibration (endpointPathPair f ≫ (prod.snd : X ⨯ Y ⟶ Y))
  infer_instance

private theorem endpointPathSource_trivialFibration (f : X ⟶ Y) :
    trivialFibrations TopCat.{u} (endpointPathSource f) := by
  let _ : Fibration (TopCat.pathEvalZero Y) :=
    (fibration_iff _).mpr (TopCat.pathEvalZero_trivialFibration Y).1
  let _ : WeakEquivalence (TopCat.pathEvalZero Y) :=
    (weakEquivalence_iff _).mpr (TopCat.pathEvalZero_mem_weakHomotopyEquivalences Y)
  let _ : (trivialFibrations TopCat.{u}).IsStableUnderBaseChange := by
    rw [← cofibrations_rlp]
    infer_instance
  exact MorphismProperty.of_isPullback (endpointPathSource_isPullback f).flip
    (mem_trivialFibrations (TopCat.pathEvalZero Y))

private theorem endpointPathInclusion_weak (f : X ⟶ Y) :
    TopCat.weakHomotopyEquivalences (endpointPathInclusion f) := by
  have hs : TopCat.weakHomotopyEquivalences (endpointPathSource f) := by
    change weakEquivalences TopCat.{u} (endpointPathSource f)
    exact (endpointPathSource_trivialFibration f).2
  have hc : TopCat.weakHomotopyEquivalences
      (endpointPathInclusion f ≫ endpointPathSource f) := by
    rw [endpointPathInclusion_source f]
    exact TopCat.weakHomotopyEquivalences.of_isIso _
  exact TopCat.weakHomotopyEquivalences.of_postcomp _ _ hs hc

private theorem endpointPathTarget_trivialFibration (f : X ⟶ Y)
    (hf : TopCat.weakHomotopyEquivalences f) :
    trivialFibrations TopCat.{u} (endpointPathTarget f) := by
  let _ : Fibration (endpointPathTarget f) := endpointPathTarget_fibration f
  have hj : TopCat.weakHomotopyEquivalences (endpointPathInclusion f) :=
    endpointPathInclusion_weak f
  have hc : TopCat.weakHomotopyEquivalences
      (endpointPathInclusion f ≫ endpointPathTarget f) := by
    rw [endpointPathInclusion_target f]
    exact hf
  let _ : WeakEquivalence (endpointPathTarget f) :=
    (weakEquivalence_iff _).mpr
      (TopCat.weakHomotopyEquivalences.of_precomp _ _ hj hc)
  exact mem_trivialFibrations _

private def endpointPathPointMap (f : X ⟶ Y) (x₀ : X) (y₀ : Y)
    (h₀ : f x₀ = y₀) : TopCat.of PUnit.{u + 1} ⟶ endpointPathSpace f :=
  pullback.lift (prod.lift (TopCat.const x₀) (TopCat.const y₀))
    (TopCat.const (ContinuousMap.const TopCat.I.{u} y₀)) (by
      apply prod.hom_ext
      · simp only [Category.assoc, prod.map_fst, prod.lift_fst_assoc,
          TopCat.pathEndpoints, prod.lift_fst]
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro z
        change f x₀ = y₀
        exact h₀
      · simp only [Category.assoc, prod.map_snd,
          TopCat.pathEndpoints, prod.lift_snd, Category.comp_id]
        apply TopCat.hom_ext
        apply ContinuousMap.ext
        intro z
        change y₀ = y₀
        rfl)

private def endpointPathPoint (f : X ⟶ Y) (x₀ : X) (y₀ : Y) (h₀ : f x₀ = y₀) :
    endpointPathSpace f := endpointPathPointMap f x₀ y₀ h₀ PUnit.unit

private theorem endpointPathPoint_source (f : X ⟶ Y) (x₀ : X) (y₀ : Y)
    (h₀ : f x₀ = y₀) : endpointPathSource f (endpointPathPoint f x₀ y₀ h₀) = x₀ := by
  have h : endpointPathPointMap f x₀ y₀ h₀ ≫ endpointPathSource f =
      TopCat.const x₀ := by
    simp [endpointPathPointMap, endpointPathSource]
  exact ConcreteCategory.congr_hom h PUnit.unit

private theorem endpointPathPoint_target (f : X ⟶ Y) (x₀ : X) (y₀ : Y)
    (h₀ : f x₀ = y₀) : endpointPathTarget f (endpointPathPoint f x₀ y₀ h₀) = y₀ := by
  have h : endpointPathPointMap f x₀ y₀ h₀ ≫ endpointPathTarget f =
      TopCat.const y₀ := by
    simp [endpointPathPointMap, endpointPathTarget]
  exact ConcreteCategory.congr_hom h PUnit.unit

private theorem endpointPathPoint_path (f : X ⟶ Y) (x₀ : X) (y₀ : Y)
    (h₀ : f x₀ = y₀) :
    endpointPathFamily f (endpointPathPoint f x₀ y₀ h₀) =
      ContinuousMap.const TopCat.I.{u} y₀ := by
  have h : endpointPathPointMap f x₀ y₀ h₀ ≫ endpointPathFamily f =
      TopCat.const (ContinuousMap.const TopCat.I.{u} y₀) := by
    rw [endpointPathPointMap, pullback.lift_snd]
  exact ConcreteCategory.congr_hom h PUnit.unit

private theorem basedSectionAtRealizedTarget (K : SSet.{u}) (y : K _⦋0⦌)
    (f : X ⟶ SSet.toTop.obj K) (x₀ : X)
    (h₀ : f x₀ = SSet.realizedVertex y)
    (hf : TopCat.weakHomotopyEquivalences f) :
    ∃ s : SSet.toTop.obj K ⟶ endpointPathSpace f,
      s ≫ endpointPathTarget f = 𝟙 (SSet.toTop.obj K) ∧
      s (SSet.realizedVertex y) =
        endpointPathPoint f x₀ (SSet.realizedVertex y) h₀ := by
  let Y : TopCat.{u} := SSet.toTop.obj K
  let P : TopCat.{u} := SSet.toTop.obj (Δ[0] : SSet.{u})
  let iS : (Δ[0] : SSet.{u}) ⟶ K := SSet.const y
  let i : P ⟶ Y := SSet.toTop.map iS
  let _ : Mono iS := SSet.stdSimplex.isTerminalObj₀.mono_from iS
  let _ : Cofibration i := by
    apply (cofibration_iff _).mpr
    exact SSet.toTop_map_mem_realizedBoundaryLLP iS
  have hi₀ : i (default : P) = SSet.realizedVertex y :=
    (SSet.realizedVertex_eq_const y).symm
  have hi : ∀ a : P, i a = SSet.realizedVertex y := fun a =>
    (congrArg i (Subsingleton.elim a (default : P))).trans hi₀
  let z₀ : endpointPathSpace f := endpointPathPoint f x₀ (SSet.realizedVertex y) h₀
  let a : P ⟶ endpointPathSpace f := TopCat.const z₀
  have ht : trivialFibrations TopCat.{u} (endpointPathTarget f) :=
    endpointPathTarget_trivialFibration f hf
  let _ : Fibration (endpointPathTarget f) := (mem_trivialFibrations_iff _).mp ht |>.1
  let _ : WeakEquivalence (endpointPathTarget f) := (mem_trivialFibrations_iff _).mp ht |>.2
  let _ : HasLiftingProperty i (endpointPathTarget f) :=
    ModelCategory.cm4b i (endpointPathTarget f)
  let sq : CommSq a i (endpointPathTarget f) (𝟙 Y) := by
    constructor
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro p
    change endpointPathTarget f z₀ = i p
    exact (endpointPathPoint_target f x₀ (SSet.realizedVertex y) h₀).trans (hi p).symm
  let s : Y ⟶ endpointPathSpace f := sq.lift
  refine ⟨s, sq.fac_right, ?_⟩
  have h := ConcreteCategory.congr_hom sq.fac_left (default : P)
  change s (i (default : P)) = z₀ at h
  exact (congrArg s hi₀.symm).trans h

private structure RealizedTargetRightInverse (K : SSet.{u}) (y : K _⦋0⦌)
    (f : X ⟶ SSet.toTop.obj K) (x₀ : X)
    (h₀ : f x₀ = SSet.realizedVertex y) where
  sectionMap : SSet.toTop.obj K ⟶ endpointPathSpace f
  section_target : sectionMap ≫ endpointPathTarget f = 𝟙 (SSet.toTop.obj K)
  section_point : sectionMap (SSet.realizedVertex y) =
    endpointPathPoint f x₀ (SSet.realizedVertex y) h₀
  inv : SSet.toTop.obj K ⟶ X
  inv_point : inv (SSet.realizedVertex y) = x₀
  section_source : sectionMap ≫ endpointPathSource f = inv
  rightHomotopyRel : ContinuousMap.HomotopyRel
    (inv ≫ f).hom (𝟙 (SSet.toTop.obj K) : SSet.toTop.obj K ⟶ SSet.toTop.obj K).hom
    {SSet.realizedVertex y}

private def basedRightInverseAtRealizedTarget (K : SSet.{u}) (y : K _⦋0⦌)
    (f : X ⟶ SSet.toTop.obj K) (x₀ : X)
    (h₀ : f x₀ = SSet.realizedVertex y)
    (hf : TopCat.weakHomotopyEquivalences f) : RealizedTargetRightInverse K y f x₀ h₀ := by
  let sections := basedSectionAtRealizedTarget K y f x₀ h₀ hf
  let s := Classical.choose sections
  have hs : s ≫ endpointPathTarget f = 𝟙 (SSet.toTop.obj K) :=
    (Classical.choose_spec sections).1
  have hFixed : s (SSet.realizedVertex y) =
      endpointPathPoint f x₀ (SSet.realizedVertex y) h₀ :=
    (Classical.choose_spec sections).2
  let Y : TopCat.{u} := SSet.toTop.obj K
  let g : Y ⟶ X := s ≫ endpointPathSource f
  let paths : Y ⟶ TopCat.pathObject Y := s ≫ endpointPathFamily f
  have hZero : paths ≫ TopCat.pathEvalZero Y = g ≫ f := by
    change (s ≫ endpointPathFamily f) ≫ TopCat.pathEvalZero Y =
      (s ≫ endpointPathSource f) ≫ f
    calc
      _ = s ≫ (endpointPathFamily f ≫ TopCat.pathEvalZero Y) :=
        Category.assoc _ _ _
      _ = s ≫ (endpointPathSource f ≫ f) :=
        congrArg (fun q => s ≫ q) (endpointPathFamily_zero f).symm
      _ = _ := (Category.assoc _ _ _).symm
  have hOne : paths ≫ TopCat.pathEvalOne Y = 𝟙 Y := by
    change (s ≫ endpointPathFamily f) ≫ TopCat.pathEvalOne Y = 𝟙 Y
    calc
      _ = s ≫ (endpointPathFamily f ≫ TopCat.pathEvalOne Y) :=
        Category.assoc _ _ _
      _ = s ≫ endpointPathTarget f :=
        congrArg (fun q => s ≫ q) (endpointPathFamily_one f).symm
      _ = 𝟙 Y := hs
  have hPathFixed : paths (SSet.realizedVertex y) =
      ContinuousMap.const TopCat.I.{u} (SSet.realizedVertex y) := by
    change endpointPathFamily f (s (SSet.realizedVertex y)) = _
    rw [hFixed]
    exact endpointPathPoint_path f x₀ (SSet.realizedVertex y) h₀
  have hg : g (SSet.realizedVertex y) = x₀ := by
    change endpointPathSource f (s (SSet.realizedVertex y)) = x₀
    rw [hFixed]
    exact endpointPathPoint_source f x₀ (SSet.realizedVertex y) h₀
  let H : ContinuousMap.Homotopy (g ≫ f).hom (𝟙 Y : Y ⟶ Y).hom :=
    { toFun := fun z => paths z.2 ((TopCat.I.homeomorph.{u}).symm z.1)
      continuous_toFun := continuous_eval.comp
        ((paths.hom.continuous.comp continuous_snd).prodMk
          ((TopCat.I.homeomorph.{u}).symm.continuous.comp continuous_fst))
      map_zero_left z := by
        have hI : (TopCat.I.homeomorph.{u}).symm (0 : unitInterval) =
            (0 : TopCat.I.{u}) := by
          apply (TopCat.I.homeomorph.{u}).injective
          simp
        exact (congrArg (fun t : TopCat.I.{u} => paths z t) hI).trans
          (ConcreteCategory.congr_hom hZero z)
      map_one_left z := by
        have hI : (TopCat.I.homeomorph.{u}).symm (1 : unitInterval) =
            (1 : TopCat.I.{u}) := by
          apply (TopCat.I.homeomorph.{u}).injective
          simp
        exact (congrArg (fun t : TopCat.I.{u} => paths z t) hI).trans
          (ConcreteCategory.congr_hom hOne z) }
  refine
    { sectionMap := s
      section_target := hs
      section_point := hFixed
      inv := g
      inv_point := hg
      section_source := rfl
      rightHomotopyRel := { toHomotopy := H, prop' := ?_ } }
  intro t z hz
  obtain rfl := Set.mem_singleton_iff.mp hz
  have hValue : H (t, SSet.realizedVertex y) = SSet.realizedVertex y :=
    congrArg (fun p : C(TopCat.I.{u}, Y) => p ((TopCat.I.homeomorph.{u}).symm t)) hPathFixed
  have hBased : (g ≫ f) (SSet.realizedVertex y) = SSet.realizedVertex y := by
    change f (g (SSet.realizedVertex y)) = SSet.realizedVertex y
    rw [hg]
    exact h₀
  exact hValue.trans hBased.symm

private theorem endpointPathInclusion_point (f : X ⟶ Y) (x₀ : X) (y₀ : Y)
    (h₀ : f x₀ = y₀) :
    endpointPathInclusion f x₀ = endpointPathPoint f x₀ y₀ h₀ := by
  have h : (TopCat.const x₀ : TopCat.of PUnit.{u + 1} ⟶ X) ≫
      endpointPathInclusion f = endpointPathPointMap f x₀ y₀ h₀ := by
    apply TopCat.homotopyPullback_hom_ext
    · simp [endpointPathInclusion, endpointPathPointMap,
        TopCat.homotopyPullbackLeft, Category.assoc]
    · simp only [Category.assoc, endpointPathInclusion_target]
      have hp : endpointPathPointMap f x₀ y₀ h₀ ≫ endpointPathTarget f =
          TopCat.const y₀ := by
        simp [endpointPathPointMap, endpointPathTarget]
      rw [hp]
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      change f x₀ = y₀
      exact h₀
    · simp only [Category.assoc, endpointPathInclusion_path]
      have hp : endpointPathPointMap f x₀ y₀ h₀ ≫ endpointPathFamily f =
          TopCat.const (ContinuousMap.const TopCat.I.{u} y₀) := by
        rw [endpointPathPointMap, pullback.lift_snd]
      rw [hp]
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      change ContinuousMap.const TopCat.I.{u} (f x₀) =
        ContinuousMap.const TopCat.I.{u} y₀
      exact congrArg (ContinuousMap.const TopCat.I.{u}) h₀
  exact ConcreteCategory.congr_hom h PUnit.unit

private def realizedLeftRelativeInverse {K L : SSet.{u}} (x : K _⦋0⦌) (y : L _⦋0⦌)
    (f : SSet.toTop.obj K ⟶ SSet.toTop.obj L)
    (h₀ : f (SSet.realizedVertex x) = SSet.realizedVertex y)
    (hf : TopCat.weakHomotopyEquivalences f)
    (R : RealizedTargetRightInverse L y f (SSet.realizedVertex x) h₀) :
    ContinuousMap.HomotopyRel (f ≫ R.inv).hom
      (𝟙 (SSet.toTop.obj K) : SSet.toTop.obj K ⟶ SSet.toTop.obj K).hom
      {SSet.realizedVertex x} := by
  let X : TopCat.{u} := SSet.toTop.obj K
  let Y : TopCat.{u} := SSet.toTop.obj L
  let E : TopCat.{u} := endpointPathSpace f
  let q : E ⟶ Y := endpointPathTarget f
  let j : X ⟶ E := endpointPathInclusion f
  let s : Y ⟶ E := R.sectionMap
  let a₀ : K ⟶ TopCat.toSSet.obj E := sSetTopAdj.homEquiv K E j
  let a₁ : K ⟶ TopCat.toSSet.obj E := sSetTopAdj.homEquiv K E (f ≫ s)
  let p : TopCat.toSSet.obj E ⟶ TopCat.toSSet.obj Y := TopCat.toSSet.map q
  let S : K.Subcomplex := SSet.Subcomplex.range (SSet.const (X := (Δ[0] : SSet.{u})) x)
  have hx : x ∈ S.obj (Opposite.op ⦋0⦌) := by
    change x ∈ Set.range ((SSet.const (X := (Δ[0] : SSet.{u})) x :
      (Δ[0] : SSet.{u}) ⟶ K).app _)
    refine ⟨SSet.stdSimplex.obj₀Equiv.symm 0, ?_⟩
    simp only [SSet.const_app]
    have h : (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op =
        𝟙 (Opposite.op ⦋0⦌) := Subsingleton.elim _ _
    rw [h, CategoryTheory.Functor.map_id]
    rfl
  have hVertex : SSet.toTop.map (SSet.const (X := (Δ[0] : SSet.{u})) x :
        (Δ[0] : SSet.{u}) ⟶ K) ≫ j =
      SSet.toTop.map (SSet.const (X := (Δ[0] : SSet.{u})) x :
        (Δ[0] : SSet.{u}) ⟶ K) ≫ (f ≫ s) := by
    let P : TopCat.{u} := SSet.toTop.obj (Δ[0] : SSet.{u})
    let i : P ⟶ X := SSet.toTop.map (SSet.const (X := (Δ[0] : SSet.{u})) x)
    have hi : ∀ z : P, i z = SSet.realizedVertex x := fun z =>
      (congrArg i (Subsingleton.elim z (default : P))).trans
        (SSet.realizedVertex_eq_const x).symm
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    change j (i z) = s (f (i z))
    rw [hi z, h₀, R.section_point]
    exact endpointPathInclusion_point f (SSet.realizedVertex x) (SSet.realizedVertex y) h₀
  have hConst : (SSet.const (X := (Δ[0] : SSet.{u})) x : (Δ[0] : SSet.{u}) ⟶ K) ≫ a₀ =
      (SSet.const (X := (Δ[0] : SSet.{u})) x : (Δ[0] : SSet.{u}) ⟶ K) ≫ a₁ := by
    change (SSet.const (X := (Δ[0] : SSet.{u})) x) ≫
        (sSetTopAdj.homEquiv K E j) =
      (SSet.const (X := (Δ[0] : SSet.{u})) x) ≫
        (sSetTopAdj.homEquiv K E (f ≫ s))
    rw [← sSetTopAdj.homEquiv_naturality_left,
      ← sSetTopAdj.homEquiv_naturality_left]
    exact congrArg (sSetTopAdj.homEquiv (Δ[0] : SSet.{u}) E) hVertex
  have hS : S.ι ≫ a₀ = S.ι ≫ a₁ := by
    ext n z
    have hz : z.val ∈ Set.range ((SSet.const (X := (Δ[0] : SSet.{u})) x :
        (Δ[0] : SSet.{u}) ⟶ K).app n) := z.property
    obtain ⟨w, hw⟩ := hz
    change a₀.app n z.val = a₁.app n z.val
    rw [← hw]
    exact congrArg (fun m : (Δ[0] : SSet.{u}) ⟶ TopCat.toSSet.obj E => m.app n w) hConst
  have hP : a₀ ≫ p = a₁ ≫ p := by
    change (sSetTopAdj.homEquiv K E j) ≫ TopCat.toSSet.map q =
      (sSetTopAdj.homEquiv K E (f ≫ s)) ≫ TopCat.toSSet.map q
    rw [← sSetTopAdj.homEquiv_naturality_right,
      ← sSetTopAdj.homEquiv_naturality_right]
    apply congrArg (sSetTopAdj.homEquiv K Y)
    calc
      j ≫ q = f := endpointPathInclusion_target f
      _ = f ≫ (s ≫ q) := by rw [R.section_target, Category.comp_id]
      _ = (f ≫ s) ≫ q := (Category.assoc _ _ _).symm
  let _ : CategoryTheory.Adjunction.IsQuillenAdjunction sSetTopAdj.{u} :=
    SSet.modelCategoryQuillen.realizationIsQuillenAdjunction
  have hp : trivialFibrations SSet.{u} p :=
    CategoryTheory.Adjunction.IsQuillenAdjunction.preservesTrivialFibrations
      (adj := sSetTopAdj) q (endpointPathTarget_trivialFibration f hf)
  let U := SSet.HomotopyRelOver.ofTrivialFibration S p hp a₀ a₁ hS hP
  let HR := SSet.realizeHomotopyRelAtVertex U.toHomotopyRel x hx
  let ε : SSet.toTop.obj (TopCat.toSSet.obj E) ⟶ E := sSetTopAdj.counit.app E
  have ha₀ : SSet.toTop.map a₀ ≫ ε = j := by
    exact (sSetTopAdj.homEquiv K E).symm_apply_apply j
  have ha₁ : SSet.toTop.map a₁ ≫ ε = f ≫ s := by
    exact (sSetTopAdj.homEquiv K E).symm_apply_apply (f ≫ s)
  let HC : ContinuousMap.Homotopy
      ((SSet.toTop.map a₀) ≫ ε ≫ endpointPathSource f).hom
      ((SSet.toTop.map a₁) ≫ ε ≫ endpointPathSource f).hom :=
    (ContinuousMap.Homotopy.refl (ε ≫ endpointPathSource f).hom).comp HR.toHomotopy
  have hc₀ : SSet.toTop.map a₀ ≫ ε ≫ endpointPathSource f = 𝟙 X := by
    rw [← Category.assoc, ha₀, endpointPathInclusion_source f]
  have hc₁ : SSet.toTop.map a₁ ≫ ε ≫ endpointPathSource f = f ≫ R.inv := by
    rw [← Category.assoc, ha₁, Category.assoc, R.section_source]
  let H : ContinuousMap.Homotopy (𝟙 X : X ⟶ X).hom (f ≫ R.inv).hom :=
    HC.cast (congrArg TopCat.Hom.hom hc₀) (congrArg TopCat.Hom.hom hc₁)
  let HRel : ContinuousMap.HomotopyRel (𝟙 X : X ⟶ X).hom (f ≫ R.inv).hom
      {SSet.realizedVertex x} :=
    { toHomotopy := H
      prop' := by
        intro t z hz
        obtain rfl := Set.mem_singleton_iff.mp hz
        have hFixed := HR.eq_fst t (Set.mem_singleton_iff.mpr rfl)
        have hEval := congrArg (fun z => (ε ≫ endpointPathSource f) z) hFixed
        change (ε ≫ endpointPathSource f) (HR (t, SSet.realizedVertex x)) =
          SSet.realizedVertex x
        exact hEval.trans (ConcreteCategory.congr_hom hc₀ (SSet.realizedVertex x)) }
  exact HRel.symm

private structure RealizedVertexBasedInverse {K L : SSet.{u}}
    (x : K _⦋0⦌) (y : L _⦋0⦌)
    (f : SSet.toTop.obj K ⟶ SSet.toTop.obj L) where
  inv : SSet.toTop.obj L ⟶ SSet.toTop.obj K
  inv_point : inv (SSet.realizedVertex y) = SSet.realizedVertex x
  leftHomotopyRel : ContinuousMap.HomotopyRel (f ≫ inv).hom
    (𝟙 (SSet.toTop.obj K) : SSet.toTop.obj K ⟶ SSet.toTop.obj K).hom
    {SSet.realizedVertex x}
  rightHomotopyRel : ContinuousMap.HomotopyRel (inv ≫ f).hom
    (𝟙 (SSet.toTop.obj L) : SSet.toTop.obj L ⟶ SSet.toTop.obj L).hom
    {SSet.realizedVertex y}

private def basedInverseOfWeakMapBetweenRealizations {K L : SSet.{u}}
    (x : K _⦋0⦌) (y : L _⦋0⦌)
    (f : SSet.toTop.obj K ⟶ SSet.toTop.obj L)
    (h₀ : f (SSet.realizedVertex x) = SSet.realizedVertex y)
    (hf : TopCat.weakHomotopyEquivalences f) : RealizedVertexBasedInverse x y f := by
  let R := basedRightInverseAtRealizedTarget L y f (SSet.realizedVertex x) h₀ hf
  exact
    { inv := R.inv
      inv_point := R.inv_point
      leftHomotopyRel := realizedLeftRelativeInverse x y f h₀ hf R
      rightHomotopyRel := R.rightHomotopyRel }

private def basedEquivOfWeakMapBetweenRealizations {K L : SSet.{u}}
    (x : K _⦋0⦌) (y : L _⦋0⦌)
    (f : SSet.toTop.obj K ⟶ SSet.toTop.obj L)
    (h₀ : f (SSet.realizedVertex x) = SSet.realizedVertex y)
    (hf : TopCat.weakHomotopyEquivalences f) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj K) (SSet.toTop.obj L) := by
  let B := basedInverseOfWeakMapBetweenRealizations x y f h₀ hf
  exact
    { toFun := f.hom
      invFun := B.inv.hom
      left_inv := ⟨B.leftHomotopyRel.toHomotopy.cast (TopCat.hom_comp f B.inv) rfl⟩
      right_inv := ⟨B.rightHomotopyRel.toHomotopy.cast (TopCat.hom_comp B.inv f) rfl⟩ }

end TopCat.RealizedBasedWhitehead

namespace TopCat

/-- The based inverse of an actual continuous weak map between realizations. -/
def realizedBasedHomotopyInverse {K L : SSet.{u}}
    (x : K _⦋0⦌) (y : L _⦋0⦌)
    (f : SSet.toTop.obj K ⟶ SSet.toTop.obj L)
    (hxy : f (SSet.realizedVertex x) = SSet.realizedVertex y)
    (hf : TopCat.weakHomotopyEquivalences f) :
    SSet.toTop.obj L ⟶ SSet.toTop.obj K :=
  (RealizedBasedWhitehead.basedInverseOfWeakMapBetweenRealizations x y f hxy hf).inv

/-- The constructed inverse takes the literal target vertex to the literal source vertex. -/
theorem realizedBasedHomotopyInverse_point {K L : SSet.{u}}
    (x : K _⦋0⦌) (y : L _⦋0⦌)
    (f : SSet.toTop.obj K ⟶ SSet.toTop.obj L)
    (hxy : f (SSet.realizedVertex x) = SSet.realizedVertex y)
    (hf : TopCat.weakHomotopyEquivalences f) :
    realizedBasedHomotopyInverse x y f hxy hf (SSet.realizedVertex y) =
      SSet.realizedVertex x :=
  (RealizedBasedWhitehead.basedInverseOfWeakMapBetweenRealizations x y f hxy hf).inv_point

/-- The left inverse homotopy is fixed on the literal source vertex at every time. -/
def realizedBasedLeftHomotopy {K L : SSet.{u}}
    (x : K _⦋0⦌) (y : L _⦋0⦌)
    (f : SSet.toTop.obj K ⟶ SSet.toTop.obj L)
    (hxy : f (SSet.realizedVertex x) = SSet.realizedVertex y)
    (hf : TopCat.weakHomotopyEquivalences f) :
    ContinuousMap.HomotopyRel
      (f ≫ realizedBasedHomotopyInverse x y f hxy hf).hom
      (𝟙 (SSet.toTop.obj K) : SSet.toTop.obj K ⟶ SSet.toTop.obj K).hom
      {SSet.realizedVertex x} :=
  (RealizedBasedWhitehead.basedInverseOfWeakMapBetweenRealizations x y f hxy hf).leftHomotopyRel

/-- The right inverse homotopy is fixed on the literal target vertex at every time. -/
def realizedBasedRightHomotopy {K L : SSet.{u}}
    (x : K _⦋0⦌) (y : L _⦋0⦌)
    (f : SSet.toTop.obj K ⟶ SSet.toTop.obj L)
    (hxy : f (SSet.realizedVertex x) = SSet.realizedVertex y)
    (hf : TopCat.weakHomotopyEquivalences f) :
    ContinuousMap.HomotopyRel
      (realizedBasedHomotopyInverse x y f hxy hf ≫ f).hom
      (𝟙 (SSet.toTop.obj L) : SSet.toTop.obj L ⟶ SSet.toTop.obj L).hom
      {SSet.realizedVertex y} :=
  (RealizedBasedWhitehead.basedInverseOfWeakMapBetweenRealizations x y f hxy hf).rightHomotopyRel

/-- The actual weak map is a homotopy equivalence with the constructed based inverse. -/
def realizedBasedHomotopyEquiv {K L : SSet.{u}}
    (x : K _⦋0⦌) (y : L _⦋0⦌)
    (f : SSet.toTop.obj K ⟶ SSet.toTop.obj L)
    (hxy : f (SSet.realizedVertex x) = SSet.realizedVertex y)
    (hf : TopCat.weakHomotopyEquivalences f) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj K) (SSet.toTop.obj L) :=
  RealizedBasedWhitehead.basedEquivOfWeakMapBetweenRealizations x y f hxy hf

/-- The forward continuous map is exactly the given map. -/
theorem realizedBasedHomotopyEquiv_toFun {K L : SSet.{u}}
    (x : K _⦋0⦌) (y : L _⦋0⦌)
    (f : SSet.toTop.obj K ⟶ SSet.toTop.obj L)
    (hxy : f (SSet.realizedVertex x) = SSet.realizedVertex y)
    (hf : TopCat.weakHomotopyEquivalences f) :
    (realizedBasedHomotopyEquiv x y f hxy hf).toFun = f.hom := (rfl)

/-- The inverse continuous map is exactly the same inverse used by both relative homotopies. -/
theorem realizedBasedHomotopyEquiv_invFun {K L : SSet.{u}}
    (x : K _⦋0⦌) (y : L _⦋0⦌)
    (f : SSet.toTop.obj K ⟶ SSet.toTop.obj L)
    (hxy : f (SSet.realizedVertex x) = SSet.realizedVertex y)
    (hf : TopCat.weakHomotopyEquivalences f) :
    (realizedBasedHomotopyEquiv x y f hxy hf).invFun =
      (realizedBasedHomotopyInverse x y f hxy hf).hom := (rfl)

end TopCat

end
