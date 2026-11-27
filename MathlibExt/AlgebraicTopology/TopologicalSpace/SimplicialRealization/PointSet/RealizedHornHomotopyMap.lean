/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedHornRetraction
public import Mathlib.Topology.Homotopy.Basic

/-!
# Continuous cylinder map for realized horn homotopy

For a positive-dimensional simplex and a horn index, the affine horn homotopy
transports through the standard-simplex realization homeomorphism to a jointly
continuous map `I × |Δ[n]| → |Δ[n]|`. The interval parameter is its first
coordinate. At time zero the map is the identity.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial
open scoped Simplicial unitInterval

namespace SSet

/--
For `n > 0`, the continuous map `I × |Δ[n]| → |Δ[n]|` obtained by transporting
the affine horn homotopy through the realization homeomorphism.
-/
noncomputable def realizedHornHomotopyMap (n : ℕ) (k : Fin (n + 1))
    (hn : 0 < n) :
    C(I × ↥(SSet.toTop.obj (Δ[n] : SSet.{u})),
      ↥(SSet.toTop.obj (Δ[n] : SSet.{u}))) where
  toFun p :=
    (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm
      (_root_.hornHomotopyMap k hn
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) p.2, p.1))
  continuous_toFun := by
    have hPair : Continuous (fun p : I × ↥(SSet.toTop.obj (Δ[n] : SSet.{u})) =>
        (((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) p.2, p.1) :
          Convexity.StdSimplex ℝ (Fin (n + 1)) × ↥(Set.Icc (0 : ℝ) 1))) := by
      apply Continuous.prodMk
      · exact (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).continuous.comp
          continuous_snd
      · exact continuous_fst
    exact (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm.continuous.comp
      ((_root_.hornHomotopyMap k hn).continuous.comp hPair)

/--
At interval parameter zero, the realized horn homotopy map fixes every point
of the realized simplex.
-/
theorem realizedHornHomotopyMap_zero (n : ℕ) (k : Fin (n + 1))
    (hn : 0 < n) (x : ↥(SSet.toTop.obj (Δ[n] : SSet.{u}))) :
    realizedHornHomotopyMap n k hn (0, x) = x := by
  have hSub : (0 : I) = ⟨(0 : ℝ), Set.left_mem_Icc.mpr zero_le_one⟩ :=
    Subtype.ext rfl
  have hArg : ((((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) x), (0 : I)) :
        Convexity.StdSimplex ℝ (Fin (n + 1)) × ↥(Set.Icc (0 : ℝ) 1)) =
      (((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) x),
        ⟨(0 : ℝ), Set.left_mem_Icc.mpr zero_le_one⟩) := by
    rw [hSub]
  have hZero := _root_.hornHomotopyMap_zero k hn
    ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) x)
  have hEq : _root_.hornHomotopyMap k hn
      (((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) x), (0 : I)) =
      ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) x) := by
    rw [hArg]
    exact hZero
  change (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm
    (_root_.hornHomotopyMap k hn
      (((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) x), (0 : I))) = x
  rw [hEq]
  exact Homeomorph.symm_apply_apply
    (SimplexCategory.toTopHomeo (SimplexCategory.mk n)) x

end SSet
