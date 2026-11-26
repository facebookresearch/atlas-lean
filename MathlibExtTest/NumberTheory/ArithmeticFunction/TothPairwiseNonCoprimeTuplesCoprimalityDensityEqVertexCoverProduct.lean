/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.TothPairwiseNonCoprimeTuplesCoprimalityDensityEqVertexCoverProduct
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Fintype.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.RiemannZeta
import MathlibExt.NumberTheory.ArithmeticFunction.CoprimalityIndicatorMultiplicativity

open Finset MetaMathlibExt

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.TothPairwiseNonCoprimeTuplesCoprimalityDensityEqVertexCoverProduct

-- Path graph on three vertices with the singleton vertex cover `{1}`.
example : coprimalityDensity ({((0 : Fin 3), (1 : Fin 3)), ((1 : Fin 3), (2 : Fin 3))} :
    Finset (Fin 3 × Fin 3)) =
    ∏' p : Nat.Primes, ((1 - 1 / ((p : ℕ) : ℝ)) +
      (1 / ((p : ℕ) : ℝ)) * (1 - 1 / ((p : ℕ) : ℝ)) ^ 2) := by
  have hE : ∀ e ∈ ({((0 : Fin 3), (1 : Fin 3)), ((1 : Fin 3), (2 : Fin 3))} :
      Finset (Fin 3 × Fin 3)), e.1 < e.2 := by decide
  have hJ : ∀ e ∈ ({((0 : Fin 3), (1 : Fin 3)), ((1 : Fin 3), (2 : Fin 3))} :
      Finset (Fin 3 × Fin 3)), e.1 ∈ ({(1 : Fin 3)} : Finset (Fin 3)) ∨
      e.2 ∈ ({(1 : Fin 3)} : Finset (Fin 3)) := by decide
  have hmain := coprimalityDensity_eq_vertex_cover_product (k := 3) (by decide) _ hE _ hJ
  rw [hmain]
  apply tprod_congr
  intro p
  have hset : ((({(1 : Fin 3)} : Finset (Fin 3)).powerset.filter
      (fun L => ∀ e ∈ ({((0 : Fin 3), (1 : Fin 3)), ((1 : Fin 3), (2 : Fin 3))} :
        Finset (Fin 3 × Fin 3)), ¬(e.1 ∈ L ∧ e.2 ∈ L))))
      = {∅, ({(1 : Fin 3)} : Finset (Fin 3))} := by decide
  rw [hset, Finset.sum_insert (by decide), Finset.sum_singleton]
  have cL0 : (∅ : Finset (Fin 3)).card = 0 := by decide
  have cJ0 : (({(1 : Fin 3)} : Finset (Fin 3)) \ ∅).card = 1 := by decide
  have cN0 : (((univ.filter fun i => ∃ l ∈ (∅ : Finset (Fin 3)),
      (l, i) ∈ ({((0 : Fin 3), (1 : Fin 3)), ((1 : Fin 3), (2 : Fin 3))} :
        Finset (Fin 3 × Fin 3)) ∨ (i, l) ∈ ({((0 : Fin 3), (1 : Fin 3)),
        ((1 : Fin 3), (2 : Fin 3))} : Finset (Fin 3 × Fin 3))) \
      {(1 : Fin 3)} : Finset (Fin 3))).card = 0 := by decide
  have cL1 : (({(1 : Fin 3)} : Finset (Fin 3))).card = 1 := by decide
  have cJ1 : (({(1 : Fin 3)} : Finset (Fin 3)) \
      ({(1 : Fin 3)} : Finset (Fin 3))).card = 0 := by decide
  have cN1 : (((univ.filter fun i => ∃ l ∈ ({(1 : Fin 3)} : Finset (Fin 3)),
      (l, i) ∈ ({((0 : Fin 3), (1 : Fin 3)), ((1 : Fin 3), (2 : Fin 3))} :
        Finset (Fin 3 × Fin 3)) ∨ (i, l) ∈ ({((0 : Fin 3), (1 : Fin 3)),
        ((1 : Fin 3), (2 : Fin 3))} : Finset (Fin 3 × Fin 3))) \
      {(1 : Fin 3)} : Finset (Fin 3))).card = 2 := by decide
  rw [cL0, cJ0, cN0, cL1, cJ1, cN1]
  simp only [pow_zero, one_mul, pow_one, add_zero, zero_add]

-- Single edge with the full vertex cover: the non-independent `{0, 1}` drops out.
example : coprimalityDensity ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2)) =
    ∏' p : Nat.Primes, (1 - (1 / ((p : ℕ) : ℝ)) ^ 2) := by
  have hE : ∀ e ∈ ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2)),
      e.1 < e.2 := by decide
  have hJ : ∀ e ∈ ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2)),
      e.1 ∈ ({(0 : Fin 2), (1 : Fin 2)} : Finset (Fin 2)) ∨
      e.2 ∈ ({(0 : Fin 2), (1 : Fin 2)} : Finset (Fin 2)) := by decide
  have hmain := coprimalityDensity_eq_vertex_cover_product (k := 2) (by decide) _ hE _ hJ
  rw [hmain]
  apply tprod_congr
  intro p
  have hset : ((({(0 : Fin 2), (1 : Fin 2)} : Finset (Fin 2)).powerset.filter
      (fun L => ∀ e ∈ ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2)),
        ¬(e.1 ∈ L ∧ e.2 ∈ L))))
      = {∅, ({(0 : Fin 2)} : Finset (Fin 2)), ({(1 : Fin 2)} : Finset (Fin 2))} := by
    decide
  rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have cL0 : (∅ : Finset (Fin 2)).card = 0 := by decide
  have cJ0 : (({(0 : Fin 2), (1 : Fin 2)} : Finset (Fin 2)) \ ∅).card = 2 := by decide
  have cN0 : (((univ.filter fun i => ∃ l ∈ (∅ : Finset (Fin 2)),
      (l, i) ∈ ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2)) ∨
        (i, l) ∈ ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2))) \
      {(0 : Fin 2), (1 : Fin 2)} : Finset (Fin 2))).card = 0 := by decide
  have cL1 : (({(0 : Fin 2)} : Finset (Fin 2))).card = 1 := by decide
  have cJ1 : (({(0 : Fin 2), (1 : Fin 2)} : Finset (Fin 2)) \
      ({(0 : Fin 2)} : Finset (Fin 2))).card = 1 := by decide
  have cN1 : (((univ.filter fun i => ∃ l ∈ ({(0 : Fin 2)} : Finset (Fin 2)),
      (l, i) ∈ ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2)) ∨
        (i, l) ∈ ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2))) \
      {(0 : Fin 2), (1 : Fin 2)} : Finset (Fin 2))).card = 0 := by decide
  have cL2 : (({(1 : Fin 2)} : Finset (Fin 2))).card = 1 := by decide
  have cJ2 : (({(0 : Fin 2), (1 : Fin 2)} : Finset (Fin 2)) \
      ({(1 : Fin 2)} : Finset (Fin 2))).card = 1 := by decide
  have cN2 : (((univ.filter fun i => ∃ l ∈ ({(1 : Fin 2)} : Finset (Fin 2)),
      (l, i) ∈ ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2)) ∨
        (i, l) ∈ ({((0 : Fin 2), (1 : Fin 2))} : Finset (Fin 2 × Fin 2))) \
      {(0 : Fin 2), (1 : Fin 2)} : Finset (Fin 2))).card = 0 := by decide
  rw [cL0, cJ0, cN0, cL1, cJ1, cN1, cL2, cJ2, cN2]
  simp only [pow_zero, one_mul, pow_one, add_zero]
  set u := 1 / ((p : ℕ) : ℝ) with hu
  ring

end MathlibExtTest.NumberTheory.ArithmeticFunction.TothPairwiseNonCoprimeTuplesCoprimalityDensityEqVertexCoverProduct
