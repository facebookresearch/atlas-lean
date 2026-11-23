/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.RootUnitContraction
public import MathlibExt.Topology.Homotopy.RootUnitContractionMap
public import Mathlib.Tactic.NormNum

/-!
# Moving-source examples for the joint root contraction

The root starts at the varying interval parameter and ends at one. Interior
contraction values distinguish the zero-source and one-source roots, and
the original concatenation clock is checked at both joining parameters.
-/

public section

noncomputable section

open unitInterval ContinuousMap

namespace RootUnitContractionTests

private def half : I := ⟨1 / 2, by constructor <;> norm_num⟩

private def threeQuarters : I := ⟨3 / 4, by constructor <;> norm_num⟩

private def movingRoot (a : I) : Path a (1 : I) where
  toFun s := Set.Icc.convexComb a 1 s
  continuous_toFun := Set.Icc.continuous_convexComb_prod.comp
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  source' := Set.Icc.convexComb_zero a 1
  target' := Set.Icc.convexComb_one a 1

private theorem movingRoot_continuous :
    Continuous (fun z : I × I => movingRoot z.1 z.2) :=
  Set.Icc.continuous_convexComb_prod.comp
    (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))

private theorem clock_half : rootUnitClock half = 0 := by
  apply Subtype.ext
  rw [rootUnitClock_coe]
  norm_num [half]

example : rootUnitClock threeQuarters = 0 := by
  apply Subtype.ext
  rw [rootUnitClock_coe]
  norm_num [threeQuarters]

example :
    (rootUnitContraction movingRoot movingRoot_continuous (half, 0) half : ℝ) = 1 / 2 := by
  rw [rootUnitContraction_apply]
  change (Set.Icc.convexComb (0 : I) 1
    (Set.Icc.convexComb (rootUnitClock half) 1 half) : ℝ) = 1 / 2
  rw [clock_half]
  norm_num [Set.Icc.convexComb, half]

example :
    (rootUnitContraction movingRoot movingRoot_continuous (half, 1) half : ℝ) = 1 := by
  rw [rootUnitContraction_apply]
  change (Set.Icc.convexComb (1 : I) 1
    (Set.Icc.convexComb (rootUnitClock half) 1 half) : ℝ) = 1
  rw [Set.Icc.convexComb_eq]
  rfl


private def affineImage : C(I, ℝ) where
  toFun t := 2 * (t : ℝ) + 1
  continuous_toFun := (continuous_const.mul continuous_subtype_val).add continuous_const

example (t a : I) :
    (rootUnitContraction movingRoot movingRoot_continuous (t, a)).map
      affineImage.continuous =
    rootUnitContraction (fun a => (movingRoot a).map affineImage.continuous)
      (rootUnitMappedFamily_continuous movingRoot movingRoot_continuous affineImage) (t, a) :=
  rootUnitContraction_map movingRoot movingRoot_continuous affineImage t a

example :
    ((rootUnitContraction movingRoot movingRoot_continuous (half, 0)).map
      affineImage.continuous) half = (2 : ℝ) := by
  change affineImage (rootUnitContraction movingRoot movingRoot_continuous (half, 0) half) = 2
  rw [rootUnitContraction_apply, clock_half]
  norm_num [affineImage, movingRoot, Set.Icc.convexComb, half]

example :
    ((rootUnitContraction movingRoot movingRoot_continuous (half, 1)).map
      affineImage.continuous) half = (3 : ℝ) := by
  change affineImage (rootUnitContraction movingRoot movingRoot_continuous (half, 1) half) = 3
  rw [rootUnitContraction_apply]
  change affineImage (Set.Icc.convexComb (1 : I) 1 _) = 3
  rw [Set.Icc.convexComb_eq]
  norm_num [affineImage]

end RootUnitContractionTests

end
