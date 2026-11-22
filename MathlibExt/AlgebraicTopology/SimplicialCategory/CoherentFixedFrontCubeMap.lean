/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontHomUnits
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeZeroPrefix
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomSuspensionFunctor

/-!
# Actual right-cube map into the realized fixed-front Hom

The distinguished original successor simplex maps each actual last
interval into the original realized right Hom. Its proved whole front
identity maps remove every front prefix. These genuine enriched
composition equations descend the actual cube quotient map, and its
free suspension gives a whole enriched comparison functor.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontCubeMap
open SimplicialEnrichment PathLastMaximum FixedFrontCollapse FixedFrontInsertion HornHomFaces

/-- The original distinguished last-interval map with both actual structural endpoint transports. -/
def intervalMap (n : ℕ) (i : Fin (n + 1)) : nerve (LastPath.{u} i) ⟶ rightHom.{u} n :=
  retargetMap (functor n) (SimplicialThickening.mk (ULift.up i.castSucc))
    (SimplicialThickening.mk (ULift.up (Fin.last (n + 1)))) (front_obj n i) (last_obj n)

/-- Actual front-prefix union reads the same original last factor in the realized right Hom. -/
theorem interval_union (n : ℕ) (i j : Fin (n + 1)) (q : SimplexCategoryᵒᵖ)
    (p : (nerve (SimplicialThickening.Path (ULift.up.{u} i.castSucc) (ULift.up.{u} j.castSucc))).obj q)
    (r : (nerve (LastPath.{u} j)).obj q) :
    (intervalMap n i).app q (p.prod' r ⋙ SimplicialThickening.compFunctor
      (.mk (ULift.up i.castSucc)) (.mk (ULift.up j.castSucc)) (.mk (ULift.up (Fin.last (n + 1))))) =
      (intervalMap n j).app q r := by
  let a : coherentSimplex.{u} ⦋n + 1⦌ := .mk (ULift.up i.castSucc)
  let b : coherentSimplex.{u} ⦋n + 1⦌ := .mk (ULift.up j.castSucc)
  let c : coherentSimplex.{u} ⦋n + 1⦌ := .mk (ULift.up (Fin.last (n + 1)))
  have hc := EqualityTransport.composition_retarget (C := realization (FixedFrontCollapse.object n))
    (A := coherentSimplex.{u} ⦋n + 1⦌) a b c (front_obj n i) (front_obj n j) (last_obj n)
    ((functor n).map a b) ((functor n).map b c) ((functor n).map a c) ((functor n).map_comp a b c)
  have h := congr($(hc).app q (p, r))
  have hf := congr($(FixedFrontHomUnits.front_hom n i j).app q p)
  change (intervalMap n i).app q (p.prod' r ⋙ SimplicialThickening.compFunctor a b c) =
    (eComp SSet.{u} (C := realization (FixedFrontCollapse.object n)) (source n) (source n) (target n)).app q
      (((retargetMap (functor n) a b (front_obj n i) (front_obj n j)).app q p), (intervalMap n j).app q r) at h
  exact h.trans ((congrArg (fun v =>
    (eComp SSet.{u} (C := realization (FixedFrontCollapse.object n)) (source n) (source n) (target n)).app q
      (v, (intervalMap n j).app q r)) hf).trans
    (congr($(e_id_comp SSet.{u} (C := realization (FixedFrontCollapse.object n)) (source n) (target n)).app q
      ((intervalMap n j).app q r))))

/-- Adjoining the original zero vertex is actual union with a minimal front prefix, hence keeps the same
  whole realized last factor. -/
theorem interval_prepend (n : ℕ) (i : Fin (n + 1)) (q : SimplexCategoryᵒᵖ)
    (r : (nerve (LastPath.{u} i)).obj q) :
    (intervalMap n 0).app q (r ⋙ RightCubeRelations.prependFunctor i) = (intervalMap n i).app q r :=
  (congrArg ((intervalMap n 0).app q) (RightCubeZeroPrefix.chain_prepend i r)).symm.trans
    (interval_union n 0 i q (RightCubeZeroPrefix.minimalChain i q) r)

/-- Every actual generating cube relation holds in the original realized right Hom. -/
theorem relation_eq (n : ℕ) {q : SimplexCategoryᵒᵖ}
    {a b : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q}
    (h : RightCubeRelations.Relation n a b) : (intervalMap n 0).app q a = (intervalMap n 0).app q b := by
  cases h with
  | composition i p r => exact (interval_union n 0 i q p r).trans (interval_prepend n i q r).symm

/-- The original realized map respects the whole generated cube equivalence relation. -/
theorem setoid_eq (n : ℕ) {q : SimplexCategoryᵒᵖ}
    {a b : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q}
    (h : (RightCubeRelations.setoid.{u} n q).r a b) : (intervalMap n 0).app q a = (intervalMap n 0).app q b := by
  induction h with
  | rel a b h => exact relation_eq n h
  | refl a => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h h' ih ih' => exact ih.trans ih'

/-- The genuine whole cube-quotient map into the actual realized original right Hom. -/
def cubeMap (n : ℕ) : RightCubeRelations.object.{u} n ⟶ rightHom.{u} n where
  app q := ↾_root_.Quotient.lift ((intervalMap n 0).app q) (fun _ _ h => setoid_eq n h)
  naturality q r θ := by
    ext a
    induction a using _root_.Quotient.inductionOn with
    | _ a => exact congr($((intervalMap n 0).naturality θ) a)

/-- The entire original cube retains exactly the distinguished original zero-to-last interval map. -/
theorem cubeMap_projection (n : ℕ) : RightCubeRelations.projection.{u} n ≫ cubeMap n = intervalMap n 0 := by
    ext q a; rfl

/-- The genuine free-suspension comparison, at the same original structural source and target. -/
def suspensionFunctor (n : ℕ) : HomSuspensionGenerators.carrier (RightCubeRelations.object.{u} n) ⟶
    realization (FixedFrontCollapse.object.{u} n) :=
  HomSuspensionFunctor.functor (RightCubeRelations.object n) (realization (FixedFrontCollapse.object n))
    (source n) (target n) (cubeMap n)

end CategoryTheory.CoherentRealization.FixedFrontCubeMap
