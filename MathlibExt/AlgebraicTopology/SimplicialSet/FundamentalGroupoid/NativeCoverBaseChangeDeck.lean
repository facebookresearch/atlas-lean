/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCertificates
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper

/-!
# Deck actions on the actual pulled native cover

An arbitrary map to the base pulls its actual native cover back. The base
deck action induces a computed action on this literal pullback. Maps over
the same base retain both projections, commute with every deck element,
and are weak when their original total-space map is weak: this last fact
uses the actual pullback square and existing right properness.

The construction does not require a supplied lift to the cover, an
expected cover model, an equivariance witness or a homology comparison.
It is the shared primitive used by unit sections and by the actual
relative-factorization comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u

public section

namespace SSet.KanComplex

/-- The actual base deck map on the original pulled native cover. -/
def nativeCoverBaseChangeDeckMap {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (g : End (SSet.FundamentalGroupoid.mk b)) :
    pullback p (nativeCoverProjection B b) ⟶ pullback p (nativeCoverProjection B b) :=
  pullback.lift (pullback.fst p (nativeCoverProjection B b))
    (pullback.snd p (nativeCoverProjection B b) ≫ nativeCoverDeckMap g) (by
      rw [Category.assoc, nativeCoverDeckMap_projection]
      exact pullback.condition)

/-- The actual original total-space projection is unchanged. -/
theorem nativeCoverBaseChangeDeckMap_fst {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (g : End (SSet.FundamentalGroupoid.mk b)) :
    nativeCoverBaseChangeDeckMap p b g ≫ pullback.fst p (nativeCoverProjection B b) =
      pullback.fst p (nativeCoverProjection B b) :=
  pullback.lift_fst _ _ _

/-- The whole base-cover coordinate is the original inverse-precomposition deck map. -/
theorem nativeCoverBaseChangeDeckMap_snd {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (g : End (SSet.FundamentalGroupoid.mk b)) :
    nativeCoverBaseChangeDeckMap p b g ≫ pullback.snd p (nativeCoverProjection B b) =
      pullback.snd p (nativeCoverProjection B b) ≫ nativeCoverDeckMap g :=
  pullback.lift_snd _ _ _

/-- The actual group multiplication gives the original LEFT action convention. -/
theorem nativeCoverBaseChangeDeckMap_mul {E B : SSet.{u}}
    (p : E ⟶ B) (b : B _⦋0⦌) (g h : End (SSet.FundamentalGroupoid.mk b)) :
    nativeCoverBaseChangeDeckMap p b (g * h) =
      nativeCoverBaseChangeDeckMap p b h ≫ nativeCoverBaseChangeDeckMap p b g := by
  apply pullback.hom_ext
  · rw [nativeCoverBaseChangeDeckMap_fst, Category.assoc,
      nativeCoverBaseChangeDeckMap_fst, nativeCoverBaseChangeDeckMap_fst]
  · rw [nativeCoverBaseChangeDeckMap_snd, Category.assoc,
      nativeCoverBaseChangeDeckMap_snd, ← Category.assoc,
      nativeCoverBaseChangeDeckMap_snd, Category.assoc, nativeCoverDeckMap_mul]

/-- The unit deck map is the actual identity map. -/
theorem nativeCoverBaseChangeDeckMap_one {E B : SSet.{u}}
    (p : E ⟶ B) (b : B _⦋0⦌) :
    nativeCoverBaseChangeDeckMap p b 1 = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [nativeCoverBaseChangeDeckMap_fst, Category.id_comp]
  · rw [nativeCoverBaseChangeDeckMap_snd, nativeCoverDeckMap_one,
      Category.comp_id, Category.id_comp]

/-- The actual map of pulled covers induced by the original triangle over the base. -/
def nativeCoverBaseChangeMap {E E' B : SSet.{u}} {p : E ⟶ B} {q : E' ⟶ B}
    (u : E ⟶ E') (hu : u ≫ q = p) (b : B _⦋0⦌) :
    pullback p (nativeCoverProjection B b) ⟶ pullback q (nativeCoverProjection B b) :=
  pullback.lift (pullback.fst p (nativeCoverProjection B b) ≫ u)
    (pullback.snd p (nativeCoverProjection B b)) (by
      rw [Category.assoc, hu]
      exact pullback.condition)

/-- The map retains the original total-space map on its first coordinate. -/
theorem nativeCoverBaseChangeMap_fst {E E' B : SSet.{u}} {p : E ⟶ B} {q : E' ⟶ B}
    (u : E ⟶ E') (hu : u ≫ q = p) (b : B _⦋0⦌) :
    nativeCoverBaseChangeMap u hu b ≫ pullback.fst q (nativeCoverProjection B b) =
      pullback.fst p (nativeCoverProjection B b) ≫ u :=
  pullback.lift_fst _ _ _

/-- The map retains the entire original base-cover coordinate. -/
theorem nativeCoverBaseChangeMap_snd {E E' B : SSet.{u}} {p : E ⟶ B} {q : E' ⟶ B}
    (u : E ⟶ E') (hu : u ≫ q = p) (b : B _⦋0⦌) :
    nativeCoverBaseChangeMap u hu b ≫ pullback.snd q (nativeCoverProjection B b) =
      pullback.snd p (nativeCoverProjection B b) :=
  pullback.lift_snd _ _ _

/-- This is the actual pullback of the original total-space map. -/
theorem nativeCoverBaseChangeMap_isPullback {E E' B : SSet.{u}}
    {p : E ⟶ B} {q : E' ⟶ B} (u : E ⟶ E') (hu : u ≫ q = p) (b : B _⦋0⦌) :
    IsPullback (nativeCoverBaseChangeMap u hu b)
      (pullback.fst p (nativeCoverProjection B b))
      (pullback.fst q (nativeCoverProjection B b)) u := by
  have hOuter : IsPullback
      (nativeCoverBaseChangeMap u hu b ≫ pullback.snd q (nativeCoverProjection B b))
      (pullback.fst p (nativeCoverProjection B b)) (nativeCoverProjection B b) (u ≫ q) := by
    rw [nativeCoverBaseChangeMap_snd, hu]
    exact (IsPullback.of_hasPullback p (nativeCoverProjection B b)).flip
  exact hOuter.of_right (nativeCoverBaseChangeMap_fst u hu b)
    (IsPullback.of_hasPullback q (nativeCoverProjection B b)).flip

/-- Right properness derives weakness of the actual pulled comparison. -/
theorem nativeCoverBaseChangeMap_mem_realizationWeakEquivalences
    {E E' B : SSet.{u}} {p : E ⟶ B} {q : E' ⟶ B}
    (u : E ⟶ E') (hu : u ≫ q = p) (b : B _⦋0⦌)
    (hw : SSet.realizationWeakEquivalences u) :
    SSet.realizationWeakEquivalences (nativeCoverBaseChangeMap u hu b) := by
  let : Fibration (nativeCoverProjection B b) := nativeCoverProjection_fibration B b
  let : Fibration (pullback.fst q (nativeCoverProjection B b)) :=
    SSet.fibration_of_isPullback (IsPullback.of_hasPullback q (nativeCoverProjection B b))
  let : WeakEquivalence u := (weakEquivalence_iff u).mpr hw
  exact (weakEquivalence_iff _).mp
    (IsRightProper.weakEquivalence_of_isPullback (nativeCoverBaseChangeMap_isPullback u hu b).flip)

/-- EVERY base deck element commutes with the actual original map of pulled covers. -/
theorem nativeCoverBaseChangeMap_deck {E E' B : SSet.{u}}
    {p : E ⟶ B} {q : E' ⟶ B} (u : E ⟶ E') (hu : u ≫ q = p) (b : B _⦋0⦌)
    (g : End (SSet.FundamentalGroupoid.mk b)) :
    nativeCoverBaseChangeDeckMap p b g ≫ nativeCoverBaseChangeMap u hu b =
      nativeCoverBaseChangeMap u hu b ≫ nativeCoverBaseChangeDeckMap q b g := by
  apply pullback.hom_ext
  · have hL := (Category.assoc _ _ _).trans
      ((congrArg (fun k => nativeCoverBaseChangeDeckMap p b g ≫ k)
        (nativeCoverBaseChangeMap_fst u hu b)).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun k => k ≫ u) (nativeCoverBaseChangeDeckMap_fst p b g))))
    have hR := (Category.assoc _ _ _).trans
      ((congrArg (fun k => nativeCoverBaseChangeMap u hu b ≫ k)
        (nativeCoverBaseChangeDeckMap_fst q b g)).trans (nativeCoverBaseChangeMap_fst u hu b))
    exact hL.trans hR.symm
  · have hL := (Category.assoc _ _ _).trans
      (congrArg (fun k => nativeCoverBaseChangeDeckMap p b g ≫ k)
        (nativeCoverBaseChangeMap_snd u hu b))
    have hR := (Category.assoc _ _ _).trans
      ((congrArg (fun k => nativeCoverBaseChangeMap u hu b ≫ k)
        (nativeCoverBaseChangeDeckMap_snd q b g)).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun k => k ≫ nativeCoverDeckMap g) (nativeCoverBaseChangeMap_snd u hu b))))
    exact hL.trans ((nativeCoverBaseChangeDeckMap_snd p b g).trans hR.symm)

end SSet.KanComplex
