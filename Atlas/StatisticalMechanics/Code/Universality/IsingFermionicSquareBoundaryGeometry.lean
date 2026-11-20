/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareWiredCompletion










namespace StatMech.Universality

open Complex
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section


def fkIsingSquareBoundaryTangent : FKIsingSquareBoundarySide → Complex
  | .bottom => 1
  | .right => Complex.I
  | .top => -1
  | .left => -Complex.I



def fkIsingSquareBoundaryPhase : FKIsingSquareBoundarySide → Complex
  | .bottom => 1
  | .right => isingLambda⁻¹
  | .top => Complex.I
  | .left => isingLambda


theorem fkIsingSquareBoundaryTangent_mul_phase_sq
    (side : FKIsingSquareBoundarySide) :
    fkIsingSquareBoundaryTangent side *
        fkIsingSquareBoundaryPhase side ^ 2 = 1 := by
  cases side with
  | bottom => simp [fkIsingSquareBoundaryTangent, fkIsingSquareBoundaryPhase]
  | right =>
      simp only [fkIsingSquareBoundaryTangent, fkIsingSquareBoundaryPhase,
        inv_pow, isingLambda_sq]
      rw [inv_I]
      rw [mul_neg, Complex.I_mul_I]
      norm_num
  | top =>
      simp [fkIsingSquareBoundaryTangent, fkIsingSquareBoundaryPhase,
        Complex.I_mul_I]
  | left =>
      rw [fkIsingSquareBoundaryTangent, fkIsingSquareBoundaryPhase,
        isingLambda_sq]
      rw [neg_mul, Complex.I_mul_I]
      norm_num




theorem FKIsingDobrushinDomain.exists_nonnegative_square_boundary_value
    {P : PlanarZ2Subgraph} {M : Type*} [Fintype M] [DecidableEq M]
    (D : FKIsingDobrushinDomain P M)
    (side : FKIsingSquareBoundarySide) (e : M)
    (hphase : ∀ omega, e ∈ D.exploration omega →
      D.windingPhase omega e = fkIsingSquareBoundaryPhase side) :
    ∃ t : Real, 0 ≤ t ∧
      fkIsingSquareBoundaryTangent side * D.fermionicObservable e ^ 2 =
        (t : Complex) := by
  exact D.exists_nonnegative_boundary_square_of_phase e
    (fkIsingSquareBoundaryTangent side)
    (fkIsingSquareBoundaryPhase side) 1 hphase zero_le_one
    (fkIsingSquareBoundaryTangent_mul_phase_sq side)



theorem fkIsingSquareWired_fermionicObservable_terminal
    (n : Nat) (hn : 0 < n) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
        (.terminal : FKIsingSquareWiredCarrier n) = 1 := by
  exact (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable_terminal


theorem fkIsingSquareWired_terminal_boundary_square
    (n : Nat) (hn : 0 < n) :
    ∃ t : Real, 0 ≤ t ∧
      (1 : Complex) *
          (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
              (.terminal : FKIsingSquareWiredCarrier n) ^ 2 =
        (t : Complex) := by
  refine ⟨1, zero_le_one, ?_⟩
  rw [fkIsingSquareWired_fermionicObservable_terminal]
  norm_num

end

end StatMech.Universality
