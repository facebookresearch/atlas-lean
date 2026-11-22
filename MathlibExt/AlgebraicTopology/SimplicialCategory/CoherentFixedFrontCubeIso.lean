/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontSuspensionReadback
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontCubeRetraction
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontInsertionExt

/-!
# The actual realized right Hom is the original right-cube quotient

The two constructed maps are inverse on every whole original scalar
Hom simplex. The opposite inverse follows from the actual free
suspension readback, the genuine realization adjunction and the
distinguished resolving simplex. This is a proved chart, not a given
comparison, and it makes no relative-frame or locally Kan claim.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontCubeIso
open SimplicialEnrichment HomSuspensionGenerators FixedFrontCollapse FixedFrontCubeMap
  FixedFrontCubeRetraction FixedFrontSuspensionReadback HornHomFaces

/-- The actual reverse resolving functor followed by the original free-suspension comparison is the whole
  enriched identity. -/
theorem functor_inverse (n : ℕ) : reverseFunctor.{u} n ≫ suspensionFunctor n = 𝟙 (realization
    (FixedFrontCollapse.object n)) := by
  apply FixedFrontInsertionExt.functor_ext n _ _
  exact (Category.assoc (FixedFrontInsertion.functor n) (reverseFunctor n) (suspensionFunctor n)).symm.trans
    ((congrArg (fun F => F ≫ suspensionFunctor n) (reverse_insertion n)).trans
      ((functor_readback n).trans (Category.comp_id (FixedFrontInsertion.functor n)).symm))

/-- Both entire original right-Hom maps retain every realized scalar cell under the opposite roundtrip. -/
theorem read_cube (n : ℕ) : readCubeMap.{u} n ≫ cubeMap n = 𝟙 (rightHom n) := by
  let Q := RightCubeRelations.object.{u} n
  let e := HomSuspensionForward.homIso Q
  let g := retargetMap (suspensionFunctor.{u} n) left right (source_obj n) (target_obj n)
  have hG : e.hom ≫ g = cubeMap n :=
    HomSuspensionFunctor.generator_readback Q (realization (FixedFrontCollapse.object n))
      (source n) (target n) (cubeMap n)
  have hReduce : readCubeMap n ≫ cubeMap n = readMap n ≫ g := by
    calc
      _ = (readMap n ≫ e.inv) ≫ (e.hom ≫ g) := congrArg (fun f => (readMap n ≫ e.inv) ≫ f) hG.symm
      _ = readMap n ≫ (e.inv ≫ (e.hom ≫ g)) := Category.assoc _ _ _
      _ = readMap n ≫ ((e.inv ≫ e.hom) ≫ g) := congrArg (fun f => readMap n ≫ f) (Category.assoc e.inv e.hom g).symm
      _ = readMap n ≫ g := congrArg (fun f => readMap n ≫ f)
        ((congrArg (fun f => f ≫ g) e.inv_hom_id).trans (Category.id_comp g))
  have hR := HomRetargetAlgebra.restriction_reindex (reverseFunctor.{u} n) (suspensionFunctor n)
    (source n) (target n) (reverse_source n) (reverse_target n) (source_obj n) (target_obj n)
  have hE := retargetMap_eq (functor_inverse.{u} n) (source n) (target n)
    ((congrArg (suspensionFunctor n).obj (reverse_source n)).trans (source_obj n))
    ((congrArg (suspensionFunctor n).obj (reverse_target n)).trans (target_obj n)) rfl rfl
  exact hReduce.trans
    ((Category.assoc ((reverseFunctor n).map (source n) (target n))
      (eqToHom (congrArg₂ (fun a b : carrier Q => a ⟶[SSet.{u}] b) (reverse_source n) (reverse_target n))) g).trans
        (hR.trans (hE.trans (by rfl))))

/-- The genuine whole simplicial-set isomorphism from the original cube quotient to the actual realized
  fixed-front right Hom. -/
def cubeIso (n : ℕ) : RightCubeRelations.object.{u} n ≅ rightHom.{u} n where
  hom := cubeMap n
  inv := readCubeMap n
  hom_inv_id := cube_read n
  inv_hom_id := read_cube n

/-- The actual whole forward chart is the original constructed cube map, with no replacement of original cells. -/
theorem cubeIso_hom (n : ℕ) : (cubeIso.{u} n).hom = cubeMap n := rfl

/-- The actual whole inverse chart is the original resolving readback map. -/
theorem cubeIso_inv (n : ℕ) : (cubeIso.{u} n).inv = readCubeMap n := rfl

end CategoryTheory.CoherentRealization.FixedFrontCubeIso
