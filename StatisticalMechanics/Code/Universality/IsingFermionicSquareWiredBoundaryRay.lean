/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareWiredBoundaryPhase










namespace StatMech.Universality

open Finset Complex SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingDobrushinDomain

variable {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]


def signedExplorationMass (D : FKIsingDobrushinDomain P M)
    (e : M) (phase : Complex) : Real :=
  ∑ omega : ConfigSpace (Sym2 P.V),
    if e ∈ D.exploration omega then
      if D.windingPhase omega e = phase then D.criticalMass omega
      else -D.criticalMass omega
    else 0



theorem fermionicObservable_eq_signedExplorationMass_mul_phase
    (D : FKIsingDobrushinDomain P M) (e : M) (phase : Complex)
    (hphase : ∀ omega, e ∈ D.exploration omega →
      D.windingPhase omega e ^ 2 = phase ^ 2) :
    D.fermionicObservable e =
      (D.signedExplorationMass e phase : Complex) * phase := by
  unfold fermionicObservable signedExplorationMass
  rw [Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases he : e ∈ D.exploration omega
  · by_cases hp : D.windingPhase omega e = phase
    · simp [fermionicSummand, he, hp]
    · have hneg : D.windingPhase omega e = -phase :=
        (sq_eq_sq_iff_eq_or_eq_neg.mp (hphase omega he)).resolve_left hp
      have hnpeq : -phase ≠ phase := fun h ↦ hp (hneg.trans h)
      simp [fermionicSummand, he, hneg, hnpeq]
  · simp [fermionicSummand, he]



theorem exists_nonnegative_boundary_square_of_phase_sq
    (D : FKIsingDobrushinDomain P M)
    (e : M) (normal phase : Complex) (r : Real)
    (hphase : ∀ omega, e ∈ D.exploration omega →
      D.windingPhase omega e ^ 2 = phase ^ 2)
    (hr : 0 ≤ r) (hline : normal * phase ^ 2 = (r : Complex)) :
    ∃ t : Real, 0 ≤ t ∧
      normal * D.fermionicObservable e ^ 2 = (t : Complex) := by
  let mass := D.signedExplorationMass e phase
  refine ⟨mass ^ 2 * r, mul_nonneg (sq_nonneg mass) hr, ?_⟩
  rw [D.fermionicObservable_eq_signedExplorationMass_mul_phase
    e phase hphase]
  calc
    normal * ((mass : Complex) * phase) ^ 2 =
        (mass : Complex) ^ 2 * (normal * phase ^ 2) := by ring
    _ = (mass : Complex) ^ 2 * (r : Complex) := by rw [hline]
    _ = ((mass ^ 2 * r : Real) : Complex) := by push_cast; ring

end FKIsingDobrushinDomain



theorem fkIsingSquare_exp_turn_modEq_eight
    (a b : Int) (h : a ≡ b [ZMOD 8]) :
    Complex.exp (Complex.I *
        (((a : Real) * (Real.pi / 4) : Real) : Complex)) =
      Complex.exp (Complex.I *
        (((b : Real) * (Real.pi / 4) : Real) : Complex)) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h
  refine ⟨-k, ?_⟩
  have hkR := congrArg (fun z : Int ↦ (z : Real)) hk
  push_cast at hkR
  have hangR : (a : Real) * (Real.pi / 4) =
      (b : Real) * (Real.pi / 4) + (-k : Real) * (2 * Real.pi) := by
    linear_combination (Real.pi / 4) * (-hkR)
  have hangC := congrArg (fun z : Real ↦ (z : Complex)) hangR
  push_cast at hangC ⊢
  linear_combination Complex.I * hangC


def fkIsingSquareWiredDirectedPhase (n : Nat) (hn : 0 < n)
    (z : FKIsingSquareWiredCarrier n) : Complex :=
  Complex.exp (Complex.I *
    ((((fkIsingSquareWiredDirectedTangentCode n hn z -
      fkIsingSquareWiredDirectedTangentCode n hn .terminal : Int) : Real) *
        (Real.pi / 8) : Real) : Complex))


def fkIsingSquareWiredDirectedTangent (n : Nat) (hn : 0 < n)
    (z : FKIsingSquareWiredCarrier n) : Complex :=
  Complex.exp (-Complex.I *
    ((((fkIsingSquareWiredDirectedTangentCode n hn z -
      fkIsingSquareWiredDirectedTangentCode n hn .terminal : Int) : Real) *
        (Real.pi / 4) : Real) : Complex))

theorem fkIsingSquareWiredDirectedTangent_mul_phase_sq
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredDirectedTangent n hn z *
        fkIsingSquareWiredDirectedPhase n hn z ^ 2 = 1 := by
  unfold fkIsingSquareWiredDirectedTangent
    fkIsingSquareWiredDirectedPhase
  rw [pow_two, ← Complex.exp_add, ← Complex.exp_add]
  convert Complex.exp_zero
  push_cast
  ring



theorem fkIsingSquareWired_windingPhase_sq
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n)
    (hz : z ∈ fkIsingSquareWiredExplorationOrder n hn omega) :
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase omega z ^ 2 =
      fkIsingSquareWiredDirectedPhase n hn z ^ 2 := by
  have hturn := fkIsingSquareWiredPhysicalTurnCount_modEq_directedTangent
    n hn omega z hz
  calc
    (fkIsingSquareWiredDobrushinDomain n hn).windingPhase omega z ^ 2 =
        Complex.exp (Complex.I *
          ((((fkIsingSquareWiredPhysicalTurnCount n hn omega z : Int) : Real) *
            (Real.pi / 4) : Real) : Complex)) := by
      unfold FKIsingDobrushinDomain.windingPhase
        fkIsingSquareWiredDobrushinDomain fkIsingSquareWiredLiftedWinding
      rw [pow_two, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = Complex.exp (Complex.I *
          ((((fkIsingSquareWiredDirectedTangentCode n hn z -
            fkIsingSquareWiredDirectedTangentCode n hn .terminal : Int) : Real) *
              (Real.pi / 4) : Real) : Complex)) :=
      fkIsingSquare_exp_turn_modEq_eight _ _ hturn
    _ = fkIsingSquareWiredDirectedPhase n hn z ^ 2 := by
      unfold fkIsingSquareWiredDirectedPhase
      rw [pow_two, ← Complex.exp_add]
      congr 1
      push_cast
      ring



theorem fkIsingSquareWired_exists_nonnegative_directed_square
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) :
    ∃ t : Real, 0 ≤ t ∧
      fkIsingSquareWiredDirectedTangent n hn z *
          (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable z ^ 2 =
        (t : Complex) := by
  apply (fkIsingSquareWiredDobrushinDomain n hn).exists_nonnegative_boundary_square_of_phase_sq z
      (fkIsingSquareWiredDirectedTangent n hn z)
      (fkIsingSquareWiredDirectedPhase n hn z) 1
  · intro omega hz
    apply fkIsingSquareWired_windingPhase_sq n hn omega z
    rw [mem_fkIsingSquareWiredExplorationOrder_iff_trace]
    simpa only [fkIsingSquareWiredDobrushinDomain] using hz
  · exact zero_le_one
  · exact fkIsingSquareWiredDirectedTangent_mul_phase_sq n hn z

end

end StatMech.Universality
