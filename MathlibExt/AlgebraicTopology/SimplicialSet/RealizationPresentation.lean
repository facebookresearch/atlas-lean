/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

import Mathlib.CategoryTheory.Functor.KanExtension.DenseAtYoneda
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Quotient presentation of geometric realization

The realization of any simplicial set is the quotient of the topological sum
of its realized nondegenerate simplices.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopCat
open scoped Simplicial

namespace SSet

/-- The map from the topological sum of realized nondegenerate simplices to realization. -/
noncomputable def sigmaToTop (T : SSet.{u}) :
    (Σ s : T.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1))) → SSet.toTop.obj T :=
  fun ⟨s, x⟩ =>
    SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
      ((SimplexCategory.toTopHomeo (⦋s.dim⦌)).symm x)

private lemma continuous_sigmaToTop (T : SSet.{u}) : Continuous (sigmaToTop T) := by
  apply continuous_sigma
  intro s
  exact (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)).hom.continuous.comp
    (SimplexCategory.toTopHomeo (⦋s.dim⦌)).symm.continuous

/-- A representable leg of the realization diagram factors continuously through one
nondegenerate simplex summand. -/
private lemma exists_factor_sigmaToTop (T : SSet.{u}) (n : SimplexCategory)
    (a : stdSimplex.obj n ⟶ T) :
    ∃ (s : T.N) (g : toTop.obj (stdSimplex.obj n) →
        Convexity.StdSimplex ℝ (Fin (s.dim + 1))),
      Continuous g ∧ ∀ y, sigmaToTop T ⟨s, g y⟩ = toTop.map a y := by
  obtain ⟨m, f, _, t, ht⟩ := T.exists_nonDegenerate (yonedaEquiv a)
  have ha : stdSimplex.map f ≫ yonedaEquiv.symm t.val = a := by
    rw [yonedaEquiv_symm_naturality_left, ← ht, yonedaEquiv.symm_apply_apply]
  let e := SimplexCategory.toTopHomeo ⦋m⦌
  refine ⟨N.mk t.val t.property, e ∘ toTop.map (stdSimplex.map f),
    e.continuous.comp (toTop.map (stdSimplex.map f)).hom.continuous, ?_⟩
  intro y
  change toTop.map (yonedaEquiv.symm t.val) (e.symm (e (toTop.map (stdSimplex.map f) y))) =
    toTop.map a y
  rw [Homeomorph.symm_apply_apply, ← ha, Functor.map_comp]
  rfl

private def realizationCover (T : SSet.{u}) :
    Cocone (CostructuredArrow.proj stdSimplex T ⋙ stdSimplex) where
  pt := T
  ι := { app j := j.hom }

private noncomputable def realizationCoverIsColimit (T : SSet.{u}) :
    IsColimit (realizationCover T) :=
  denseAtUliftYoneda T

/-- Every realization point lies in the image of a nondegenerate simplex. -/
lemma surjective_sigmaToTop (T : SSet.{u}) : Function.Surjective (sigmaToTop T) := by
  intro x
  have hc : IsColimit ((toTop ⋙ forget TopCat).mapCocone (realizationCover T)) :=
    isColimitOfPreserves _ (realizationCoverIsColimit T)
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc x
  obtain ⟨s, g, _, hg⟩ := exists_factor_sigmaToTop T j.left j.hom
  exact ⟨⟨s, g y⟩, (hg y).trans hy⟩

/-- Every realization point is the image of a point of the realized standard simplex
under a map corresponding to a nondegenerate simplex. -/
theorem exists_nonDegenerate_toTop_presentation (T : SSet.{u})
    (x : SSet.toTop.obj T) :
    ∃ (n : ℕ) (s : T _⦋n⦌) (_ : s ∈ T.nonDegenerate n)
      (y : SSet.toTop.obj (SSet.stdSimplex.obj ⦋n⦌)),
      SSet.toTop.map (SSet.yonedaEquiv.symm s) y = x := by
  obtain ⟨⟨s, y⟩, hy⟩ := surjective_sigmaToTop T x
  exact ⟨s.dim, s.simplex, s.nonDegenerate,
    (SimplexCategory.toTopHomeo ⦋s.dim⦌).symm y, hy⟩

/-- The realization topology is the quotient topology from the sum of the realized
nondegenerate standard simplices, without a finiteness or separation assumption. -/
theorem isQuotientMap_sigmaToTop (T : SSet.{u}) :
    Topology.IsQuotientMap (sigmaToTop (T := T)) := by
  refine ⟨Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen ?_, surjective_sigmaToTop T⟩
  intro U
  refine ⟨fun hOpen => ?_, fun hU => hU.preimage (continuous_sigmaToTop T)⟩
  have hc : IsColimit (toTop.mapCocone (realizationCover T)) :=
    isColimitOfPreserves toTop (realizationCoverIsColimit T)
  apply (TopCat.isOpen_iff_of_isColimit _ hc U).mpr
  intro j
  obtain ⟨s, g, hg, hfac⟩ := exists_factor_sigmaToTop T j.left j.hom
  have hCont : Continuous (fun y ↦ (⟨s, g y⟩ : Σ s : T.N,
      Convexity.StdSimplex ℝ (Fin (s.dim + 1)))) := continuous_sigmaMk.comp hg
  change IsOpen ((fun y ↦ toTop.map j.hom y) ⁻¹' U)
  simpa only [Set.preimage_preimage, Function.comp_def, hfac] using hOpen.preimage hCont

end SSet
