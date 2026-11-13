/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierA.KacWardTrivalentCoefficients
import Code.Onsager.AugmentedTurnCancellation
import Code.Onsager.DecorationFormalSupport

open scoped BigOperators

namespace StatMech.FrontierA

open Finset



noncomputable def kwLoopOrbitExponent
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    {n : ℕ} (reverse : Dart -> Dart) (loop : Fin n -> Dart) :
    Sym2 Dart →₀ ℕ :=
  ∑ k, Finsupp.single s(loop k, reverse (loop k)) 1



theorem kwLoopOrbitExponent_surgery
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    {n : ℕ} [NeZero n] (selected : Dart) (reverse : Dart -> Dart)
    (hreverse : Function.Involutive reverse) (loop : Fin n -> Dart)
    (hboth : (∃ i, loop i = selected) ∧
      ∃ j, loop j = reverse selected) :
    kwLoopOrbitExponent reverse
        (StatMech.Onsager.ons_surgery selected reverse loop) =
      kwLoopOrbitExponent reverse loop := by
  unfold kwLoopOrbitExponent
  exact StatMech.Onsager.ons_sum_surgery_invariant
    selected reverse hreverse
    (fun dart => Finsupp.single s(dart, reverse dart) 1)
    (fun dart => by
      change Finsupp.single
        s(reverse dart, reverse (reverse dart)) 1 =
          Finsupp.single s(dart, reverse dart) 1
      rw [hreverse, Sym2.eq_swap])
    loop hboth



noncomputable def kwFixedOrbitExponentLoops
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    {n : ℕ} (selected : Dart) (reverse : Dart -> Dart)
    (exponent : Sym2 Dart →₀ ℕ) : Finset (Fin n -> Dart) :=
  (StatMech.Onsager.ons_loopSetBoth (n := n)
    selected (reverse selected)).filter fun loop =>
      kwLoopOrbitExponent reverse loop = exponent




theorem kw_fixedOrbitExponent_surgery_cancel
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    {n : ℕ} [NeZero n] (transition : Matrix Dart Dart ℂ)
    (selected : Dart) (reverse : Dart -> Dart)
    (hreverse : Function.Involutive reverse)
    (hreverse_ne : reverse selected ≠ selected)
    (exponent : Sym2 Dart →₀ ℕ)
    (hsign : ∀ loop ∈ StatMech.Onsager.ons_loopSetBoth (n := n)
        selected (reverse selected),
      StatMech.Onsager.ons_loopWeight transition
          (StatMech.Onsager.ons_surgery selected reverse loop) =
        -StatMech.Onsager.ons_loopWeight transition loop) :
    (∑ loop ∈ kwFixedOrbitExponentLoops (n := n)
        selected reverse exponent,
      StatMech.Onsager.ons_loopWeight transition loop) = 0 := by
  apply StatMech.Onsager.ons_sum_zero_of_sign_involution'
    transition (kwFixedOrbitExponentLoops (n := n)
      selected reverse exponent)
    (StatMech.Onsager.ons_surgery selected reverse)
  · intro loop hloop
    rw [kwFixedOrbitExponentLoops, Finset.mem_filter] at hloop ⊢
    have hboth :=
      (StatMech.Onsager.ons_mem_loopSetBoth
        selected (reverse selected) loop).mp hloop.1
    refine ⟨?_, ?_⟩
    · apply (StatMech.Onsager.ons_mem_loopSetBoth
        selected (reverse selected) _).mpr
      exact StatMech.Onsager.ons_surgery_visitsBoth
        hreverse hreverse_ne hboth
    · rw [kwLoopOrbitExponent_surgery
        selected reverse hreverse loop hboth, hloop.2]
  · intro loop hloop
    rw [kwFixedOrbitExponentLoops, Finset.mem_filter] at hloop
    exact hsign loop hloop.1
  · intro loop hloop
    rw [kwFixedOrbitExponentLoops, Finset.mem_filter] at hloop
    have hboth :=
      (StatMech.Onsager.ons_mem_loopSetBoth
        selected (reverse selected) loop).mp hloop.1
    exact StatMech.Onsager.ons_surgery_involutive
      hreverse hreverse_ne hboth




theorem kw_fixedOrbitExponent_reversibleTurnMatrix_cancel
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    {n : ℕ} [NeZero n]
    (reverse : Dart -> Dart) (hreverse : Function.Involutive reverse)
    (direction : Dart -> Fin 4)
    (hdirection : ∀ dart, direction (reverse dart) = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (edgeFactor : Dart -> Dart -> ℂ)
    (hedgeFactor : ∀ x y,
      edgeFactor (reverse y) (reverse x) = edgeFactor x y)
    (selected : Dart) (hreverse_ne : reverse selected ≠ selected)
    (exponent : Sym2 Dart →₀ ℕ) :
    (∑ loop ∈ kwFixedOrbitExponentLoops (n := n)
        selected reverse exponent,
      StatMech.Onsager.ons_loopWeight
        (StatMech.Onsager.ons_reversibleTurnMatrix
          direction omega edgeFactor) loop) = 0 := by
  apply kw_fixedOrbitExponent_surgery_cancel
    (StatMech.Onsager.ons_reversibleTurnMatrix
      direction omega edgeFactor)
    selected reverse hreverse hreverse_ne exponent
  intro loop hloop
  apply StatMech.Onsager.ons_reversibleTurnMatrix_surgery_sign
    reverse hreverse direction hdirection omega homega homega_sq
      edgeFactor hedgeFactor selected loop
  exact (StatMech.Onsager.ons_mem_loopSetBoth
    selected (reverse selected) loop).mp hloop



theorem kw_fixedOrbitExponent_stateWeightedReversibleTurnMatrix_cancel
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    {n : ℕ} [NeZero n]
    (reverse : Dart -> Dart) (hreverse : Function.Involutive reverse)
    (direction : Dart -> Fin 4)
    (hdirection : ∀ dart, direction (reverse dart) = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (rowWeight colWeight : Dart -> ℂ)
    (hweight : ∀ dart,
      rowWeight (reverse dart) * colWeight (reverse dart) =
        rowWeight dart * colWeight dart)
    (edgeFactor : Dart -> Dart -> ℂ)
    (hedgeFactor : ∀ x y,
      edgeFactor (reverse y) (reverse x) = edgeFactor x y)
    (selected : Dart) (hreverse_ne : reverse selected ≠ selected)
    (exponent : Sym2 Dart →₀ ℕ) :
    (∑ loop ∈ kwFixedOrbitExponentLoops (n := n)
        selected reverse exponent,
      StatMech.Onsager.ons_loopWeight
        (StatMech.Onsager.ons_stateWeightedReversibleTurnMatrix
          direction omega rowWeight colWeight edgeFactor) loop) = 0 := by
  apply kw_fixedOrbitExponent_surgery_cancel
    (StatMech.Onsager.ons_stateWeightedReversibleTurnMatrix
      direction omega rowWeight colWeight edgeFactor)
    selected reverse hreverse hreverse_ne exponent
  intro loop hloop
  apply StatMech.Onsager.ons_stateWeightedReversibleTurnMatrix_surgery_sign
    reverse hreverse direction hdirection omega homega homega_sq
    rowWeight colWeight hweight edgeFactor hedgeFactor selected loop
  exact (StatMech.Onsager.ons_mem_loopSetBoth
    selected (reverse selected) loop).mp hloop



theorem kw_fixedOrbitExponent_gauge_reversibleTurnMatrix_cancel
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    {n : ℕ} [NeZero n]
    (reverse : Dart -> Dart) (hreverse : Function.Involutive reverse)
    (direction : Dart -> Fin 4)
    (hdirection : ∀ dart, direction (reverse dart) = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (edgeFactor : Dart -> Dart -> ℂ)
    (hedgeFactor : ∀ x y,
      edgeFactor (reverse y) (reverse x) = edgeFactor x y)
    (gauge : Dart -> ℂ) (hgauge : ∀ dart, gauge dart ≠ 0)
    (selected : Dart) (hreverse_ne : reverse selected ≠ selected)
    (exponent : Sym2 Dart →₀ ℕ) :
    (∑ loop ∈ kwFixedOrbitExponentLoops (n := n)
        selected reverse exponent,
      StatMech.Onsager.ons_loopWeight
        (kwGaugeConjugate gauge
          (StatMech.Onsager.ons_reversibleTurnMatrix
            direction omega edgeFactor)) loop) = 0 := by
  calc
    (∑ loop ∈ kwFixedOrbitExponentLoops (n := n)
        selected reverse exponent,
      StatMech.Onsager.ons_loopWeight
        (kwGaugeConjugate gauge
          (StatMech.Onsager.ons_reversibleTurnMatrix
            direction omega edgeFactor)) loop) =
      ∑ loop ∈ kwFixedOrbitExponentLoops (n := n)
        selected reverse exponent,
        StatMech.Onsager.ons_loopWeight
          (StatMech.Onsager.ons_reversibleTurnMatrix
            direction omega edgeFactor) loop := by
      apply Finset.sum_congr rfl
      intro loop _
      exact kw_loopWeight_gaugeConjugate gauge _ hgauge loop
    _ = 0 := kw_fixedOrbitExponent_reversibleTurnMatrix_cancel
      reverse hreverse direction hdirection omega homega homega_sq
      edgeFactor hedgeFactor selected hreverse_ne exponent

end StatMech.FrontierA
