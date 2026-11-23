/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange
public import MathlibExt.Topology.Category.TopCat.PreimageSubspacePullback

/-!
# Actual homotopy-fiber maps of restrictions

Pullback restriction preserves the strict fiber over a point and its image.
The canonical strict-fiber map is the isomorphism supplied by the pasted
pullback squares. If both constant-path comparisons are weak equivalences,
their exact naturality square makes the actual homotopy-fiber map weak.

For nested open restrictions this uses the two local comparisons. It imposes
no weak-equivalence hypothesis on the open inclusions and gives no global
open-cover descent conclusion.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopCat

private theorem restrictionPointPullback
    {E₀ A E B : TopCat.{u}} {q : E₀ ⟶ A} {p : E ⟶ B}
    {s : E₀ ⟶ E} {h : A ⟶ B} (sq : IsPullback s q p h) (a : A) :
    IsPullback
      (pullback.fst q (TopCat.const (X := TopCat.of PUnit) a) ≫ s)
      (pullback.snd q (TopCat.const (X := TopCat.of PUnit) a)) p
      (TopCat.const (X := TopCat.of PUnit) (h a)) := by
  have outer :=
    (IsPullback.of_hasPullback q (TopCat.const (X := TopCat.of PUnit) a)).paste_horiz sq
  have hc : TopCat.const (X := TopCat.of PUnit) a ≫ h =
      TopCat.const (X := TopCat.of PUnit) (h a) := by
    ext x
    rfl
  rw [hc] at outer
  exact outer

/-- A pullback restriction identifies the actual strict fiber with the
original fiber over the image point. -/
def strictFiberRestrictionIso
    {E₀ A E B : TopCat.{u}} {q : E₀ ⟶ A} {p : E ⟶ B}
    {s : E₀ ⟶ E} {h : A ⟶ B} (sq : IsPullback s q p h) (a : A) :
    pullback q (TopCat.const (X := TopCat.of PUnit) a) ≅
      pullback p (TopCat.const (X := TopCat.of PUnit) (h a)) :=
  (restrictionPointPullback sq a).isoIsPullback _ _ (IsPullback.of_hasPullback _ _)

/-- The restriction isomorphism retains the actual total-space inclusion. -/
@[reassoc (attr := simp)]
theorem strictFiberRestrictionIso_hom_fst
    {E₀ A E B : TopCat.{u}} {q : E₀ ⟶ A} {p : E ⟶ B}
    {s : E₀ ⟶ E} {h : A ⟶ B} (sq : IsPullback s q p h) (a : A) :
    (strictFiberRestrictionIso sq a).hom ≫
      pullback.fst p (TopCat.const (X := TopCat.of PUnit) (h a)) =
        pullback.fst q (TopCat.const (X := TopCat.of PUnit) a) ≫ s :=
  (restrictionPointPullback sq a).isoIsPullback_hom_fst _ _
    (IsPullback.of_hasPullback _ _)

/-- The isomorphism is the canonical strict-fiber map of the given square. -/
theorem strictFiberRestrictionIso_hom_eq
    {E₀ A E B : TopCat.{u}} {q : E₀ ⟶ A} {p : E ⟶ B}
    {s : E₀ ⟶ E} {h : A ⟶ B} (sq : IsPullback s q p h) (a : A) :
    (strictFiberRestrictionIso sq a).hom =
      strictFiberMapOfSquare s h sq.w.symm a := by
  apply pullback.hom_ext
  · rw [strictFiberRestrictionIso_hom_fst, strictFiberMapOfSquare_fst]
  · apply TopCat.isTerminalPUnit.hom_ext

/-- Canonical maps of strict fibers are isomorphisms for pullback squares. -/
theorem isIso_strictFiberMapOfSquare_of_isPullback
    {E₀ A E B : TopCat.{u}} {q : E₀ ⟶ A} {p : E ⟶ B}
    {s : E₀ ⟶ E} {h : A ⟶ B} (sq : IsPullback s q p h) (a : A) :
    IsIso (strictFiberMapOfSquare s h sq.w.symm a) := by
  rw [← strictFiberRestrictionIso_hom_eq sq a]
  infer_instance

/-- Two weak local comparisons make the actual homotopy-fiber restriction
map weak, even when the base and total inclusions are not weak equivalences. -/
theorem homotopyFiberMapOfSquare_mem_of_isPullback_comparisons
    {E₀ A E B : TopCat.{u}} {q : E₀ ⟶ A} {p : E ⟶ B}
    {s : E₀ ⟶ E} {h : A ⟶ B} (sq : IsPullback s q p h) (a : A)
    (hlocal : weakHomotopyEquivalences (strictFiberToHomotopyFiber q a))
    (htarget : weakHomotopyEquivalences (strictFiberToHomotopyFiber p (h a))) :
    weakHomotopyEquivalences (homotopyFiberMapOfSquare s h sq.w.symm a) := by
  let _ : IsIso (strictFiberMapOfSquare s h sq.w.symm a) :=
    isIso_strictFiberMapOfSquare_of_isPullback sq a
  have hstrict : weakHomotopyEquivalences (strictFiberMapOfSquare s h sq.w.symm a) :=
    weakHomotopyEquivalences.of_isIso _
  have hcomp : weakHomotopyEquivalences
      (strictFiberToHomotopyFiber q a ≫ homotopyFiberMapOfSquare s h sq.w.symm a) := by
    rw [← strictFiberToHomotopyFiber_naturality]
    exact weakHomotopyEquivalences.comp_mem _ _ hstrict htarget
  exact weakHomotopyEquivalences.of_precomp _ _ hlocal hcomp

/-- The actual projection from a canonical preimage subspace. -/
def restrictionProjection {E B : TopCat.{u}} (p : E ⟶ B) (W : Set B) :
    TopCat.of (p ⁻¹' W) ⟶ TopCat.of W :=
  AlgebraicTopology.subspaceMap p (fun _ hw => hw)

/-- Canonical preimage restriction is a pullback square. -/
theorem restrictionProjection_isPullback {E B : TopCat.{u}}
    (p : E ⟶ B) (W : Set B) :
    IsPullback (AlgebraicTopology.subspaceIncl (p ⁻¹' W))
      (restrictionProjection p W) p (AlgebraicTopology.subspaceIncl W) :=
  (AlgebraicTopology.isPullback_preimageSubspace p W).flip

/-- Inclusion of a smaller canonical total-space restriction. -/
def restrictionTotalInclusion {E B : TopCat.{u}}
    (p : E ⟶ B) {W U : Set B} (hWU : W ⊆ U) :
    TopCat.of (p ⁻¹' W) ⟶ TopCat.of (p ⁻¹' U) :=
  AlgebraicTopology.subspaceInclOfSubset (Set.preimage_mono hWU)

private theorem restrictionTotalInclusion_eq_aux {E B : TopCat.{u}}
    (p : E ⟶ B) {W U : Set B} (hWU : W ⊆ U) :
    restrictionTotalInclusion p hWU =
      AlgebraicTopology.subspaceInclOfSubset (Set.preimage_mono hWU) := rfl

/-- The actual total map of a nested restriction is the preimage subspace inclusion. -/
theorem restrictionTotalInclusion_eq_subspaceInclOfSubset {E B : TopCat.{u}}
    (p : E ⟶ B) {W U : Set B} (hWU : W ⊆ U) :
    restrictionTotalInclusion p hWU =
      AlgebraicTopology.subspaceInclOfSubset (Set.preimage_mono hWU) :=
  restrictionTotalInclusion_eq_aux p hWU

/-- Nested canonical restrictions give the actual pullback square between
the two restricted projections. -/
theorem restrictionProjection_nested_isPullback {E B : TopCat.{u}}
    (p : E ⟶ B) {W U : Set B} (hWU : W ⊆ U) :
    IsPullback (restrictionTotalInclusion p hWU) (restrictionProjection p W)
      (restrictionProjection p U) (AlgebraicTopology.subspaceInclOfSubset hWU) := by
  have hs : restrictionTotalInclusion p hWU ≫
      AlgebraicTopology.subspaceIncl (p ⁻¹' U) =
        AlgebraicTopology.subspaceIncl (p ⁻¹' W) := by
    ext x
    rfl
  have hb : AlgebraicTopology.subspaceInclOfSubset hWU ≫
      AlgebraicTopology.subspaceIncl U = AlgebraicTopology.subspaceIncl W := by
    ext x
    rfl
  have outer : IsPullback
      (restrictionTotalInclusion p hWU ≫ AlgebraicTopology.subspaceIncl (p ⁻¹' U))
      (restrictionProjection p W) p
      (AlgebraicTopology.subspaceInclOfSubset hWU ≫ AlgebraicTopology.subspaceIncl U) := by
    rw [hs, hb]
    exact restrictionProjection_isPullback p W
  have comm : restrictionTotalInclusion p hWU ≫ restrictionProjection p U =
      restrictionProjection p W ≫ AlgebraicTopology.subspaceInclOfSubset hWU := by
    ext x
    rfl
  exact IsPullback.of_right outer comm (restrictionProjection_isPullback p U)

/-- The overlap-to-member map of homotopy fibers is the actual map of
canonical restrictions and is weak from the two given local comparisons. -/
theorem restrictionHomotopyFiberMap_mem {E B : TopCat.{u}}
    (p : E ⟶ B) {W U : Set B} (hWU : W ⊆ U) (w : TopCat.of W)
    (hW : weakHomotopyEquivalences
      (strictFiberToHomotopyFiber (restrictionProjection p W) w))
    (hU : weakHomotopyEquivalences
      (strictFiberToHomotopyFiber (restrictionProjection p U)
        (AlgebraicTopology.subspaceInclOfSubset hWU w))) :
    weakHomotopyEquivalences
      (homotopyFiberMapOfSquare (restrictionTotalInclusion p hWU)
        (AlgebraicTopology.subspaceInclOfSubset hWU)
        (restrictionProjection_nested_isPullback p hWU).w.symm w) :=
  homotopyFiberMapOfSquare_mem_of_isPullback_comparisons
    (restrictionProjection_nested_isPullback p hWU) w hW hU

end TopCat
