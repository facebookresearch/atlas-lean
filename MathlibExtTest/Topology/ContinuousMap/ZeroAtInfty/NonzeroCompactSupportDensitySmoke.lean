/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/
module

public import MathlibExt.Topology.ContinuousMap.ZeroAtInfty.CompactSupportDensity
public import MathlibExt.Topology.ContinuousMap.ZeroAtInfty.IocCoordinate
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Tactic.NormNum

/-!
# Nonzero compactly supported approximation on a half-open interval

The complex coordinate on `(0,1]` vanishes at infinity and has supremum norm one.
Compact-support density supplies approximants in its original C₀ norm. Every
approximant within `1/4` is nonzero, so this density assertion has a nontrivial
compactly supported witness on a nonempty domain.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ZeroAtInfty

namespace NonzeroCompactSupportDensitySmoke

private abbrev Interval := Set.Ioc (0 : ℝ) 1

private instance : LocallyCompactSpace Interval := by
  have hopen : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
  have hclosed : IsClosed (Set.Iic (1 : ℝ)) := isClosed_Iic
  have hset : Set.Ioc (0 : ℝ) 1 = Set.Ioi 0 ∩ Set.Iic 1 := by
    ext x
    simp
  have hlocal : IsLocallyClosed (Set.Ioc (0 : ℝ) 1) := by
    rw [hset]
    exact hopen.isLocallyClosed.inter hclosed.isLocallyClosed
  exact hlocal.locallyCompactSpace

private def endpoint : Interval := ⟨1, by constructor <;> norm_num⟩

example : ZeroAtInftyContinuousMap.iocCoordinate 1 endpoint = 1 ∧
    ‖ZeroAtInftyContinuousMap.iocCoordinate 1‖ = 1 ∧
    ZeroAtInftyContinuousMap.iocCoordinate 1 ≠ 0 := by
  have hvalue : ZeroAtInftyContinuousMap.iocCoordinate 1 endpoint = 1 := by
    simp [endpoint]
  have hnorm : ‖ZeroAtInftyContinuousMap.iocCoordinate 1‖ = 1 := by norm_num
  refine ⟨hvalue, hnorm, ?_⟩
  intro hzero
  have h := congrArg (fun f : C₀(Interval, ℂ) => f endpoint) hzero
  rw [hvalue] at h
  norm_num at h

example (ε : ℝ) (hε : 0 < ε) :
    ∃ g : C₀(Interval, ℂ), HasCompactSupport (g : Interval → ℂ) ∧
      dist g (ZeroAtInftyContinuousMap.iocCoordinate 1) < ε := by
  obtain ⟨g, hball, hsupport⟩ :=
    (Metric.dense_iff.mp
      (ZeroAtInftyContinuousMap.dense_hasCompactSupport (X := Interval)))
      (ZeroAtInftyContinuousMap.iocCoordinate 1) ε hε
  exact ⟨g, hsupport, hball⟩

example : ∃ g : C₀(Interval, ℂ), HasCompactSupport (g : Interval → ℂ) ∧
    dist g (ZeroAtInftyContinuousMap.iocCoordinate 1) < 1 / 4 ∧ g ≠ 0 := by
  obtain ⟨g, hball, hsupport⟩ :=
    (Metric.dense_iff.mp
      (ZeroAtInftyContinuousMap.dense_hasCompactSupport (X := Interval)))
      (ZeroAtInftyContinuousMap.iocCoordinate 1) (1 / 4) (by norm_num)
  have hdist : dist g (ZeroAtInftyContinuousMap.iocCoordinate 1) < 1 / 4 := hball
  refine ⟨g, hsupport, hdist, ?_⟩
  intro hzero
  have hnorm : ‖ZeroAtInftyContinuousMap.iocCoordinate 1‖ = 1 := by norm_num
  rw [hzero, dist_zero_left, hnorm] at hdist
  norm_num at hdist

end NonzeroCompactSupportDensitySmoke
