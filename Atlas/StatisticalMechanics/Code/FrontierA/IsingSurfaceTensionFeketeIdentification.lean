/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.RectangularBlockTiling

open Filter Set Topology

namespace StatMech.FrontierA

noncomputable section



theorem rectangularSurfaceRate_eq_iteratedFeketeLimit
    {F : Nat -> Nat -> Real} (hF : forall m n, 0 <= F m n)
    (hsub : SeparatelySubadditive F) :
    rectangularSurfaceRate F =
      (horizontalStripRate_subadditive hF hsub.1 hsub.2).lim := by
  let u : Nat -> Real := fun k => (hsub.1 k).lim
  have hu : Subadditive u :=
    horizontalStripRate_subadditive hF hsub.1 hsub.2
  have hu_nonneg : forall k, 0 <= u k := fun k =>
    horizontalStripRate_nonneg hF hsub.1 k
  have hu_bdd : BddBelow (Set.range fun k : Nat => u k / (k : Real)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨k, rfl⟩
    exact div_nonneg (hu_nonneg k) (Nat.cast_nonneg k)
  apply le_antisymm
  · have hrate_le_strip : forall k : Nat, 0 < k ->
        rectangularSurfaceRate F <= u k / (k : Real) := by
      intro k hk
      apply ge_of_tendsto
        (fixedHeightSurfaceDensity_tendsto hF hsub.1 k)
      filter_upwards [eventually_gt_atTop 0] with m hm
      exact rectangularSurfaceRate_le_density hF hm hk
    apply ge_of_tendsto
      (iteratedRectangularSurfaceDensity_tendsto hF hsub.1 hsub.2)
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact hrate_le_strip k hk
  · apply le_csInf (positiveRectangularSurfaceDensities_nonempty F)
    rintro density ⟨m, k, hm, hk, rfl⟩
    have hm_ne : Not (m = 0) := Nat.ne_of_gt hm
    have hk_ne : Not (k = 0) := Nat.ne_of_gt hk
    have hm_real : 0 < (m : Real) := by exact_mod_cast hm
    have hk_real : 0 < (k : Real) := by exact_mod_cast hk
    have hmk_real : 0 < (m : Real) * (k : Real) :=
      mul_pos hm_real hk_real
    have hm_bdd : BddBelow (Set.range fun n : Nat => F n k / (n : Real)) := by
      refine ⟨0, ?_⟩
      rintro x ⟨n, rfl⟩
      exact div_nonneg (hF n k) (Nat.cast_nonneg n)
    have hu_le : u k <= F m k / (m : Real) :=
      (hsub.1 k).lim_le_div hm_bdd hm_ne
    have hlim_le : hu.lim <= u k / (k : Real) :=
      hu.lim_le_div hu_bdd hk_ne
    change hu.lim <= rectangularSurfaceDensity F m k
    calc
      hu.lim <= u k / (k : Real) := hlim_le
      _ <= (F m k / (m : Real)) / (k : Real) :=
        div_le_div_of_nonneg_right hu_le hk_real.le
      _ = rectangularSurfaceDensity F m k := by
        rw [rectangularSurfaceDensity]
        field_simp



theorem iteratedRectangularSurfaceDensity_tendsto_rate
    {F : Nat -> Nat -> Real} (hF : forall m n, 0 <= F m n)
    (hsub : SeparatelySubadditive F) :
    Tendsto (fun k : Nat => (hsub.1 k).lim / (k : Real)) atTop
      (nhds (rectangularSurfaceRate F)) := by
  rw [rectangularSurfaceRate_eq_iteratedFeketeLimit hF hsub]
  exact iteratedRectangularSurfaceDensity_tendsto hF hsub.1 hsub.2



theorem square_and_iterated_surfaceDensity_tendsto_rate
    {F : Nat -> Nat -> Real} (hF : forall m n, 0 <= F m n)
    (hsub : SeparatelySubadditive F) (harea : HasRectangularAreaBound F) :
    Tendsto (fun n : Nat => rectangularSurfaceDensity F n n) atTop
        (nhds (rectangularSurfaceRate F)) /\
      Tendsto (fun k : Nat => (hsub.1 k).lim / (k : Real)) atTop
        (nhds (rectangularSurfaceRate F)) := by
  constructor
  · exact rectangularSurfaceDensity_tendsto_rate hF
      (hasRectangularBlockGluing_of_separatelySubadditive_areaBound
        hF hsub harea)
  · exact iteratedRectangularSurfaceDensity_tendsto_rate hF hsub

end

end StatMech.FrontierA
