/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Geometry.ConvexHullCorrectness
import Mathlib.Tactic.NormNum

/-!
# Monotone-chain correctness fixtures

The fixtures use real coordinates, check the exact returned vertex order and absence of repeats,
and specialize the correctness theorem to describe the extreme points and the closed region.
The square includes a collinear boundary point and an interior point, neither of which is extreme.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Geometry

open Set Cslib.Algorithms.Lean TimeM

local notation "O" => ((0, 0) : ℝ × ℝ)
local notation "E" => ((2, 0) : ℝ × ℝ)
local notation "N" => ((0, 2) : ℝ × ℝ)
local notation "NE" => ((2, 2) : ℝ × ℝ)
local notation "M" => ((1, 0) : ℝ × ℝ)
local notation "I" => ((1, 1) : ℝ × ℝ)

private noncomputable abbrev triangle : List (ℝ × ℝ) := [O, N, E]

private noncomputable abbrev square : List (ℝ × ℝ) := [O, N, M, I, E, NE]

example : (convexHull triangle).ret = [O, E, N] ∧ (convexHull triangle).ret.Nodup ∧
    {x | x ∈ ([O, E, N] : List (ℝ × ℝ))} =
      (_root_.convexHull ℝ {x | x ∈ triangle}).extremePoints ℝ ∧
    _root_.convexHull ℝ {x | x ∈ triangle} = {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + x.2 ≤ 2} := by
  have hs : triangle.Pairwise fun a b => toLex a < toLex b := by
    norm_num [triangle, List.pairwise_cons, Prod.Lex.toLex_lt_toLex]
  have hn : ∃ a ∈ triangle, ∃ b ∈ triangle, ∃ c ∈ triangle, cross (b - a) (c - a) ≠ 0 := by
    refine ⟨O, by simp [triangle], E, by simp [triangle], N, by simp [triangle], ?_⟩
    norm_num [cross]
  have hret : (convexHull triangle).ret = [O, E, N] := by
    norm_num [triangle, convexHull, lowerHull, upperHull, chainScan, popNonLeft, cross,
      ret_bind, ret_pure, Prod.fst_sub, Prod.snd_sub]
  obtain ⟨_, hnodup, hvertices, hregion⟩ := convexHull_correct triangle hs hn
  rw [hret] at hvertices hregion
  refine ⟨hret, hnodup, hvertices, hregion.symm.trans ?_⟩
  ext x
  simp only [mem_ofPred_eq, List.take_succ_cons, List.take_zero, List.cons_append,
    List.nil_append, List.isChain_cons_cons, List.isChain_singleton, and_true, cross,
    Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h <;> obtain ⟨h₁, h₂, h₃⟩ := h <;>
    exact ⟨by linarith, by linarith, by linarith⟩

example : (convexHull square).ret = [O, E, NE, N] ∧ (convexHull square).ret.Nodup ∧
    {x | x ∈ ([O, E, NE, N] : List (ℝ × ℝ))} =
      (_root_.convexHull ℝ {x | x ∈ square}).extremePoints ℝ ∧
    _root_.convexHull ℝ {x | x ∈ square} = {x | 0 ≤ x.1 ∧ x.1 ≤ 2 ∧ 0 ≤ x.2 ∧ x.2 ≤ 2} := by
  have hs : square.Pairwise fun a b => toLex a < toLex b := by
    norm_num [square, List.pairwise_cons, Prod.Lex.toLex_lt_toLex]
  have hn : ∃ a ∈ square, ∃ b ∈ square, ∃ c ∈ square, cross (b - a) (c - a) ≠ 0 := by
    refine ⟨O, by simp [square], E, by simp [square], N, by simp [square], ?_⟩
    norm_num [cross]
  have hret : (convexHull square).ret = [O, E, NE, N] := by
    norm_num [square, convexHull, lowerHull, upperHull, chainScan, popNonLeft, cross,
      ret_bind, ret_pure, Prod.fst_sub, Prod.snd_sub]
  obtain ⟨_, hnodup, hvertices, hregion⟩ := convexHull_correct square hs hn
  rw [hret] at hvertices hregion
  refine ⟨hret, hnodup, hvertices, hregion.symm.trans ?_⟩
  ext x
  simp only [mem_ofPred_eq, List.take_succ_cons, List.take_zero, List.cons_append,
    List.nil_append, List.isChain_cons_cons, List.isChain_singleton, and_true, cross,
    Prod.fst_sub, Prod.snd_sub]
  constructor <;> intro h <;> obtain ⟨h₁, h₂, h₃, h₄⟩ := h <;>
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

#print axioms convexHull_correct

end Cslib.Algorithms.Lean.Geometry
