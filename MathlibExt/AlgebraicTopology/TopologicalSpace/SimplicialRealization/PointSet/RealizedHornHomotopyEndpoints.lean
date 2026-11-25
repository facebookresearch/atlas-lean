/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedHornHomotopyMap

/-!
# Realized horn homotopy endpoint and fix laws

For `0 < n` and `k : Fin (n + 1)`, two pointwise laws for
`SSet.realizedHornHomotopyMap`: at interval one it equals the realized horn
inclusion after `SSet.realizedHornRetract`, and at every interval parameter it
fixes the realized horn pointwise. Both conjugate the public
`_root_.hornHomotopyMap_one` and `_root_.hornHomotopyMap_fix` through
`SimplexCategory.toTopHomeo`, via `_root_.hornRetractMap`,
`realizedHornHomeomorphHornLocus`, and the canonical `Convexity.StdSimplex`
locus `hornRange_image_eq_locus_u`; no affine formula is reproved.

No `ContinuousMap.Homotopy` package, filling, anodyne, weak-equivalence,
fibration, product, colimit, or model-category claim.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial
open scoped Simplicial unitInterval

namespace SSet

/-- Interval-one law: the homotopy at `1` is inclusion after retraction. -/
theorem realizedHornHomotopyMap_one (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n)
    (x : ↥(SSet.toTop.obj (Δ[n] : SSet.{u}))) :
    realizedHornHomotopyMap n k hn (1, x) =
      SSet.toTop.map (SSet.horn.{u} n k).ι (realizedHornRetract n k hn x) := by
  have hSub : (1 : I) = ⟨(1 : ℝ), Set.right_mem_Icc.mpr zero_le_one⟩ :=
    Subtype.ext rfl
  have hArg : ((((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) x), (1 : I)) :
        Convexity.StdSimplex ℝ (Fin (n + 1)) × ↥(Set.Icc (0 : ℝ) 1)) =
      (((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) x),
        ⟨(1 : ℝ), Set.right_mem_Icc.mpr zero_le_one⟩) := by
    rw [hSub]
  have hOne := _root_.hornHomotopyMap_one k hn
      ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) x)
  have hVal : _root_.affineHornRetract k hn
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) x) =
      (((_root_.hornRetractMap k hn
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) x)) :
        ↥(_root_.hornLocus k hn)).val :
        Convexity.StdSimplex ℝ (Fin (n + 1))) := rfl
  have hEq : _root_.hornHomotopyMap k hn
      (((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) x), (1 : I)) =
      (((_root_.hornRetractMap k hn
        ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) x)) :
        ↥(_root_.hornLocus k hn)).val :
        Convexity.StdSimplex ℝ (Fin (n + 1))) := by
    rw [hArg, hOne]
    exact hVal
  have hBridge : ∀ w : {t : Convexity.StdSimplex ℝ (Fin (n + 1)) //
        ∃ j, j ≠ k ∧ t.weights j = 0},
      (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm
        (w.val) =
        SSet.toTop.map (SSet.horn.{u} n k).ι
          ((_root_.realizedHornHomeomorphHornLocus.{u} n k hn).symm w) := by
    intro w
    have hHomeo_val :
        ((_root_.realizedHornHomeomorphHornLocus.{u} n k hn
            ((_root_.realizedHornHomeomorphHornLocus.{u} n k hn).symm w)).val) =
        (SimplexCategory.toTopHomeo (SimplexCategory.mk n))
          (SSet.toTop.map (SSet.horn.{u} n k).ι
            ((_root_.realizedHornHomeomorphHornLocus.{u} n k hn).symm w)) :=
      rfl
    have hInv : _root_.realizedHornHomeomorphHornLocus.{u} n k hn
        ((_root_.realizedHornHomeomorphHornLocus.{u} n k hn).symm w) = w :=
      Homeomorph.apply_symm_apply _ w
    have hH : (SimplexCategory.toTopHomeo (SimplexCategory.mk n))
          (SSet.toTop.map (SSet.horn.{u} n k).ι
            ((_root_.realizedHornHomeomorphHornLocus.{u} n k hn).symm w)) =
          (w.val) := by
      have hComb := hHomeo_val
      rw [hInv] at hComb
      exact hComb.symm
    rw [← hH, Homeomorph.symm_apply_apply]
  change (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm
      (_root_.hornHomotopyMap k hn
        (((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) x), (1 : I))) =
      SSet.toTop.map (SSet.horn.{u} n k).ι
        ((_root_.realizedHornHomeomorphHornLocus.{u} n k hn).symm
          (_root_.hornRetractMap k hn
            ((SimplexCategory.toTopHomeo (SimplexCategory.mk n)) x)))
  rw [hEq]
  exact hBridge _

/-- Fix law: the homotopy fixes every realized horn point at every parameter. -/
theorem realizedHornHomotopyMap_fix (n : ℕ) (k : Fin (n + 1)) (hn : 0 < n)
    (y : SSet.toTop.obj (SSet.horn.{u} n k)) (t : I) :
    realizedHornHomotopyMap n k hn (t, SSet.toTop.map (SSet.horn.{u} n k).ι y) =
      SSet.toTop.map (SSet.horn.{u} n k).ι y := by
  have hmem_image :
      (SimplexCategory.toTopHomeo (SimplexCategory.mk n))
        (SSet.toTop.map (SSet.horn.{u} n k).ι y) ∈
        (SimplexCategory.toTopHomeo (SimplexCategory.mk n)) ''
          Set.range (SSet.toTop.map (SSet.horn.{u} n k).ι) :=
    ⟨SSet.toTop.map (SSet.horn.{u} n k).ι y,
      Set.mem_range.mpr ⟨y, rfl⟩, rfl⟩
  have hmem_locus : ∃ j, j ≠ k ∧
      ((SimplexCategory.toTopHomeo (SimplexCategory.mk n))
        (SSet.toTop.map (SSet.horn.{u} n k).ι y)).weights j = 0 := by
    have hmem : (SimplexCategory.toTopHomeo (SimplexCategory.mk n))
        (SSet.toTop.map (SSet.horn.{u} n k).ι y) ∈
        (SimplexCategory.toTopHomeo (SimplexCategory.mk n)) ''
          Set.range (SSet.toTop.map (SSet.horn.{u} n k).ι) :=
      hmem_image
    rw [_root_.hornRange_image_eq_locus_u n k hn] at hmem
    simpa using hmem
  have hfix :
      _root_.hornHomotopyMap k hn
        (((SimplexCategory.toTopHomeo (SimplexCategory.mk n))
            (SSet.toTop.map (SSet.horn.{u} n k).ι y)), t) =
        (SimplexCategory.toTopHomeo (SimplexCategory.mk n))
            (SSet.toTop.map (SSet.horn.{u} n k).ι y) :=
    _root_.hornHomotopyMap_fix k hn _ hmem_locus t
  change (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).symm
    (_root_.hornHomotopyMap k hn
      (((SimplexCategory.toTopHomeo (SimplexCategory.mk n))
        (SSet.toTop.map (SSet.horn.{u} n k).ι y)), t)) =
    SSet.toTop.map (SSet.horn.{u} n k).ι y
  rw [hfix]
  exact Homeomorph.symm_apply_apply
    (SimplexCategory.toTopHomeo (SimplexCategory.mk n)) _

end SSet
