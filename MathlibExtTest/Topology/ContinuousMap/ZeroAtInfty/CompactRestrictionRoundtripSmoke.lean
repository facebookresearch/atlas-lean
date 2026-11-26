/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Topology.ContinuousMap.ZeroAtInfty.CompactRestriction
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.NormNum

/-!
# C0 restriction and zero extension at the boundary of a compact interval

On `[0,1]`, the complex coordinate function is zero outside the open
positive part. Its C0 restriction has value one at the upper endpoint.
Zero extension preserves that value, gives zero at the excluded lower
endpoint, and both public restriction-extension round trips recover the
original functions.
-/

noncomputable section

open scoped ZeroAtInfty

namespace MathlibExtTest.CompactRestrictionRoundtrip

private abbrev Interval := Set.Icc (0 : ℝ) 1

private instance : CompactSpace Interval :=
  isCompact_iff_compactSpace.mp (isCompact_Icc (a := (0 : ℝ)) (b := 1))

private def positivePart : Set Interval := {x | 0 < (x : ℝ)}

private theorem positivePart_open : IsOpen positivePart :=
  isOpen_lt continuous_const continuous_subtype_val

private def lowerEndpoint : Interval := ⟨0, by norm_num⟩
private def upperEndpoint : Interval := ⟨1, by norm_num⟩
private def positiveEndpoint : positivePart :=
  ⟨upperEndpoint, by norm_num [positivePart, upperEndpoint]⟩

private def coordinate : C(Interval, ℂ) where
  toFun x := ((x : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp continuous_subtype_val

private theorem zeroOutside : ∀ x : Interval, x ∉ positivePart → coordinate x = 0 := by
  intro x hx
  have hx0 : (x : ℝ) = 0 := le_antisymm (le_of_not_gt hx) x.property.1
  change ((x : ℝ) : ℂ) = 0
  exact_mod_cast hx0

private abbrev restricted :=
  ZeroAtInftyContinuousMap.restrictZeroOutside positivePart coordinate zeroOutside

private theorem endpoint_value : restricted positiveEndpoint = 1 := by
  rw [ZeroAtInftyContinuousMap.restrictZeroOutside_apply]
  norm_num [coordinate, positiveEndpoint, upperEndpoint]

example : IsOpen positivePart ∧ lowerEndpoint ∉ positivePart ∧ upperEndpoint ∈ positivePart := by
  refine ⟨positivePart_open, ?_, ?_⟩ <;>
    norm_num [positivePart, lowerEndpoint, upperEndpoint]

example :
    restricted positiveEndpoint = 1 ∧
      ZeroAtInftyContinuousMap.extendByZero positivePart_open restricted upperEndpoint = 1 ∧
      ZeroAtInftyContinuousMap.extendByZero positivePart_open restricted lowerEndpoint = 0 := by
  refine ⟨endpoint_value, ?_, ?_⟩
  · exact (ZeroAtInftyContinuousMap.extendByZero_apply
      positivePart_open restricted positiveEndpoint).trans endpoint_value
  · exact ZeroAtInftyContinuousMap.extendByZero_apply_of_not_mem
      positivePart_open restricted (by norm_num [positivePart, lowerEndpoint])

example :
    ZeroAtInftyContinuousMap.extendByZero positivePart_open restricted = coordinate :=
  ZeroAtInftyContinuousMap.extendByZero_restrictZeroOutside
    positivePart_open coordinate zeroOutside

example :
    ZeroAtInftyContinuousMap.restrictZeroOutside positivePart
      (ZeroAtInftyContinuousMap.extendByZero positivePart_open restricted)
      (fun _ hx => ZeroAtInftyContinuousMap.extendByZero_apply_of_not_mem
        positivePart_open restricted hx) = restricted :=
  ZeroAtInftyContinuousMap.restrictZeroOutside_extendByZero positivePart_open restricted

example : restricted ≠ 0 := by
  intro h
  have hv := congrArg (fun f : C₀(positivePart, ℂ) => f positiveEndpoint) h
  rw [endpoint_value] at hv
  norm_num at hv

end MathlibExtTest.CompactRestrictionRoundtrip
