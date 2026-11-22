/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontCubeMap
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeFrontFamily
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFrontFamilyEndpoints
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontEvaluationInsertion

/-!
# Genuine right-cube readback of the realized fixed-front Hom

The actual front-compatible cube family gives a resolving evaluation
into the constructed free suspension. Its whole insertion readback
recovers that same original family. The induced reverse Hom map is a
proved retraction of the original cube map in every scalar degree.
No opposite inverse or relative-frame conclusion is assumed here.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontCubeRetraction
open SimplicialEnrichment PathLastMaximum FixedFrontCollapse FixedFrontInsertion
  FixedFrontCubeMap HomSuspensionGenerators HornHomFaces

/-- The actual original mapping simplex defined by the genuine right-cube family. -/
def mappingSimplex (n : ℕ) :
    (SSet.mappingSpaceRight (coherentNerveFunctor.obj (carrier (RightCubeRelations.object.{u} n)))
      (HomSimplexEndpoints.vertex (C := carrier (RightCubeRelations.object.{u} n)) left)
      (HomSimplexEndpoints.vertex (C := carrier (RightCubeRelations.object.{u} n)) right)) _⦋n⦌ :=
  HomFrontFamilyEndpoints.mappingSimplex (C := carrier (RightCubeRelations.object.{u} n))
    left right (RightCubeFrontFamily.family.{u} n)

/-- The actual resolving enriched functor to the free suspension of the original right cube. -/
def reverseFunctor (n : ℕ) : realization (FixedFrontCollapse.object.{u} n) ⟶
    carrier (RightCubeRelations.object.{u} n) :=
  FixedFrontEvaluation.functor (C := carrier (RightCubeRelations.object.{u} n)) left right (mappingSimplex n)

/-- The actual reverse resolving functor retains the structural source as the original free-suspension left object. -/
theorem reverse_source (n : ℕ) : (reverseFunctor.{u} n).obj (source n) = left :=
  FixedFrontEvaluation.functor_source (C := carrier (RightCubeRelations.object.{u} n)) left right (mappingSimplex n)

/-- The actual reverse resolving functor retains the structural target as the original free-suspension right object. -/
theorem reverse_target (n : ℕ) : (reverseFunctor.{u} n).obj (target n) = right :=
  FixedFrontEvaluation.functor_target (C := carrier (RightCubeRelations.object.{u} n)) left right (mappingSimplex n)

/-- Whole insertion into the actual reverse resolving functor recovers the original right-cube family,
  including all Hom maps. -/
theorem reverse_insertion (n : ℕ) : FixedFrontInsertion.functor.{u} n ≫ reverseFunctor n =
    RightCubeFrontFamily.functor n :=
  (FixedFrontEvaluationInsertion.insertion (C := carrier (RightCubeRelations.object.{u} n)) left right
    (mappingSimplex n)).trans
    ((congrArg (fun f : (Δ[n + 1] : SSet.{u}) ⟶ coherentNerveFunctor.obj (carrier (RightCubeRelations.object
      n)) => SSet.yonedaEquiv f)
      (HomFrontFamilyEndpoints.mappingSimplex_readback (C := carrier (RightCubeRelations.object.{u} n)) left
        right (RightCubeFrontFamily.family n))).trans
      ((SSet.yonedaEquiv (X := coherentNerveFunctor.obj (carrier (RightCubeRelations.object.{u} n)))
        (n := ⦋n + 1⦌)).apply_symm_apply (RightCubeFrontFamily.functor n)))

/-- The actual whole reverse Hom map to the original free-suspension forward Hom. -/
def readMap (n : ℕ) : rightHom.{u} n ⟶
    SimplicialQuiver.freeHom (quiver (RightCubeRelations.object.{u} n)) left right :=
  FixedFrontEvaluation.homMap (C := carrier (RightCubeRelations.object.{u} n)) left right (mappingSimplex n)

/-- Every supplied original last interval reads back precisely the same cube family under the actual reverse Hom map. -/
theorem interval_read (n : ℕ) (i : Fin (n + 1)) : intervalMap.{u} n i ≫ readMap n =
    (RightCubeFrontFamily.family n).map i := by
  let a : coherentSimplex.{u} ⦋n + 1⦌ := .mk (ULift.up i.castSucc)
  let b : coherentSimplex.{u} ⦋n + 1⦌ := .mk (ULift.up (Fin.last (n + 1)))
  have hr := HomRetargetAlgebra.restriction_reindex (FixedFrontInsertion.functor.{u} n) (reverseFunctor n) a b
    (front_obj n i) (last_obj n) (reverse_source n) (reverse_target n)
  have he := retargetMap_eq (reverse_insertion.{u} n) a b
    ((congrArg (reverseFunctor n).obj (front_obj n i)).trans (reverse_source n))
    ((congrArg (reverseFunctor n).obj (last_obj n)).trans (reverse_target n))
    (HomFrontFamily.simplex_front (C := carrier (RightCubeRelations.object.{u} n)) left right
      (RightCubeFrontFamily.family n) i)
    (HomFrontFamily.simplex_last (C := carrier (RightCubeRelations.object.{u} n)) left right
      (RightCubeFrontFamily.family n))
  exact (Category.assoc ((FixedFrontInsertion.functor n).map a b)
    (eqToHom (congrArg₂ (fun a b : realization (FixedFrontCollapse.object.{u} n) => a ⟶[SSet.{u}] b)
      (front_obj n i) (last_obj n))) (readMap n)).trans
    (hr.trans (he.trans (HomFrontFamily.homMap_last (C := carrier (RightCubeRelations.object.{u} n)) left
      right (RightCubeFrontFamily.family n) i)))

/-- The actual zero-prepending functor is the identity because each original path already contains its
  original zero endpoint. -/
theorem prepend_zero (n : ℕ) : RightCubeRelations.prependFunctor.{u} (0 : Fin (n + 1)) = 𝟭 _ := by
  refine Functor.ext (fun p => ?_) ?_
  · apply SimplicialThickening.Path.ext
    exact Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr p.left)
  · intro p q f
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The same actual reverse Hom map read in the original right cube, using the genuine free-suspension Hom
  isomorphism. -/
def readCubeMap (n : ℕ) : rightHom.{u} n ⟶ RightCubeRelations.object.{u} n :=
  readMap n ≫ (HomSuspensionForward.homIso (RightCubeRelations.object n)).inv

/-- The entire original cube is recovered exactly by the constructed forward and reverse maps; every
  original scalar cell is retained. -/
theorem cube_read (n : ℕ) : cubeMap.{u} n ≫ readCubeMap n = 𝟙 (RightCubeRelations.object n) := by
  have hN : nerveMap (RightCubeRelations.prependFunctor.{u} (0 : Fin (n + 1))) = 𝟙 _ := by
    rw [prepend_zero]
    rfl
  have hZero : (RightCubeFrontFamily.family.{u} n).map 0 ≫
      (HomSuspensionForward.homIso (RightCubeRelations.object n)).inv = RightCubeRelations.projection n := by
    change (nerveMap (RightCubeRelations.prependFunctor (0 : Fin (n + 1))) ≫
      RightCubeRelations.projection n ≫ (HomSuspensionForward.homIso (RightCubeRelations.object n)).hom) ≫
        (HomSuspensionForward.homIso (RightCubeRelations.object n)).inv = _
    rw [hN, Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext q a
  induction a using _root_.Quotient.inductionOn with
  | _ a =>
    change (((intervalMap n 0 ≫ readMap n) ≫
      (HomSuspensionForward.homIso (RightCubeRelations.object n)).inv).app q a) =
        _root_.Quotient.mk (RightCubeRelations.setoid.{u} n q) a
    exact (congrArg (fun f => (f ≫ (HomSuspensionForward.homIso (RightCubeRelations.object n)).inv).app q a)
      (interval_read n 0)).trans (congr($(hZero).app q a))

end CategoryTheory.CoherentRealization.FixedFrontCubeRetraction
