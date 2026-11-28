/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.DoubleAscentDescent
import Mathlib.Tactic.Ring

open MetaMathlibExt
open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

namespace DoubleAscentDescentTest

-- Both permutations of length two avoid the patterns. One ascends and the other descends.
example : PowerSeries.coeff 2 (ascDesGF (pattern3 ![1, 2, 0]) (pattern3 ![2, 0, 1])) =
    MvPolynomial.X 0 + MvPolynomial.X 1 := by
  let inc : Equiv.Perm (Fin 2) := 1
  let dec := Equiv.swap (0 : Fin 2) 1
  have hset : (Finset.univ.filter fun σ : Equiv.Perm (Fin 2) =>
      ¬ HasPattern σ (pattern3 ![1, 2, 0]) ∧ ¬ HasPattern σ (pattern3 ![2, 0, 1])) =
      {inc, dec} := by decide +kernel
  have hne : inc ≠ dec := by decide
  have h : permAscents inc = 1 ∧ permDescents inc = 0 ∧
      permAscents dec = 0 ∧ permDescents dec = 1 := by decide +kernel
  obtain ⟨ai, di, ad, dd⟩ := h
  simp [ascDesGF, hset, hne, ai, di, ad, dd]

private noncomputable abbrev H := dascDdesGF (pattern3 ![1, 2, 0]) (pattern3 ![2, 0, 1])

example : PowerSeries.coeff 0 H = 1 := by
  have h (σ : Equiv.Perm (Fin 0)) (p : Fin 3 → Fin 3) : ¬ HasPattern σ p :=
    fun ⟨e, _⟩ => Fin.elim0 (e 0)
  simp [H, dascDdesGF, h, permDoubleAscents, permDoubleDescents]

-- At length three the increasing and decreasing permutations supply one variable each.
-- The two mixed avoiders both have weight one.
example : PowerSeries.coeff 3 H = MvPolynomial.X 0 + MvPolynomial.X 1 + 2 := by
  let inc := pattern3 ![0, 1, 2]
  let peak := pattern3 ![0, 2, 1]
  let valley := pattern3 ![1, 0, 2]
  let dec := pattern3 ![2, 1, 0]
  have hset : (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) =>
      ¬ HasPattern σ (pattern3 ![1, 2, 0]) ∧ ¬ HasPattern σ (pattern3 ![2, 0, 1])) =
      {inc, peak, valley, dec} := by decide +kernel
  have h₁ : inc ∉ ({peak, valley, dec} : Finset _) := by decide +kernel
  have h₂ : peak ∉ ({valley, dec} : Finset _) := by decide +kernel
  have h₃ : valley ∉ ({dec} : Finset _) := by decide +kernel
  have hs : permDoubleAscents inc = 1 ∧ permDoubleDescents inc = 0 ∧
      permDoubleAscents peak = 0 ∧ permDoubleDescents peak = 0 ∧
      permDoubleAscents valley = 0 ∧ permDoubleDescents valley = 0 ∧
      permDoubleAscents dec = 0 ∧ permDoubleDescents dec = 1 := by decide +kernel
  obtain ⟨ai, di, ap, dp, av, dv, ad, dd⟩ := hs
  simp [H, dascDdesGF, hset, Finset.sum_insert, h₁, h₂, h₃, ai, di, ap, dp, av, dv, ad, dd]
  ring

end DoubleAscentDescentTest
