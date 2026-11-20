/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicCenteredTensorTentRegularity









namespace StatMech.Universality

noncomputable section




theorem fkIsingExpandingBoundarySquareCenteredNE_window_indices_lt_outer
    (k baseI baseJ R : Nat)
    (hfitI : baseI + R + 1 < fkIsingExpandingSquareSide k)
    (hfitJ : baseJ + R + 1 < fkIsingExpandingSquareSide k)
    (p : IsingLeapfrogBox R) :
    fkIsingExpandingSquareSide k + (baseI + p.1.1) + 1 <
        2 * fkIsingExpandingSquareSide k ∧
      fkIsingExpandingSquareSide k + (baseJ + p.2.1) + 1 <
        2 * fkIsingExpandingSquareSide k := by
  have hpI := p.1.2
  have hpJ := p.2.2
  omega




theorem
    fkIsingExpandingBoundarySquareCenteredNE_normalizedNeighbor_norm_sub_le
    (k baseI baseJ R rho cutoff : Nat) (hk : 1 <= k)
    (hfitI : baseI + R + 1 < fkIsingExpandingSquareSide k)
    (hfitJ : baseJ + R + 1 < fkIsingExpandingSquareSide k)
    (hcutoff : 0 < cutoff)
    (hdeep : forall q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell
          (fkIsingExpandingSquareSide k) baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells
          (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide k)
          (le_refl _) (by
            simp only [fkIsingExpandingSquareSide, pow_two]
            nlinarith) cutoff)
    (hsideCutoff : fkIsingExpandingSquareSide k <= 4 * cutoff)
    (hsideRho : fkIsingExpandingSquareSide k <= 4 * rho)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    norm
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k)
            ⟨fkIsingExpandingSquareSide k + (baseI + p.1.1), by
              have := p.1.2
              omega⟩
            ⟨fkIsingExpandingSquareSide k + (baseJ + p.2.1), by
              have := p.2.2
              omega⟩ /
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex) -
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable
            (fkIsingExpandingSquareSide k)
            (fkIsingExpandingSquareSide_pos k)
            ⟨fkIsingExpandingSquareSide k + (baseI + p'.1.1), by
              have := p'.1.2
              omega⟩
            ⟨fkIsingExpandingSquareSide k + (baseJ + p'.2.1), by
              have := p'.2.2
              omega⟩ /
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k) : Complex)) <=
      fkIsingExpandingSquareScale k * 40000 := by
  let m := fkIsingExpandingSquareSide k
  have hmpos : 0 < m := fkIsingExpandingSquareSide_pos k
  have hm2 : 2 <= m := by
    dsimp only [m]
    simp only [fkIsingExpandingSquareSide, pow_two]
    nlinarith
  have hvariation : fkIsingSquareBoundaryRadialPatchDeepVariation
      m m (fkIsingExpandingSquareSide_pos k) (le_refl _) hm2 cutoff <=
        64 * (m : Real) := by
    calc
      _ <= 16 * (m : Real) ^ 2 / (cutoff : Real) :=
        fkIsingSquareBoundaryRadialPatchDeepVariation_le
          m m cutoff (fkIsingExpandingSquareSide_pos k) (le_refl _)
            hm2 hcutoff
      _ <= 64 * (m : Real) := by
        apply (div_le_iff₀ (by positivity : (0 : Real) < cutoff)).2
        have hsideCutoff' : (m : Real) <= 4 * (cutoff : Real) := by
          exact_mod_cast hsideCutoff
        nlinarith [show (0 : Real) < m by positivity]
  have hradius : (k + 1 : Nat) <=
      fkIsingExpandingSquareMesh k * (rho : Real) := by
    have hk1 : (0 : Real) < ((k + 1 : Nat) : Real) := by positivity
    rw [fkIsingExpandingSquareMesh, fkIsingExpandingSquareScale]
    rw [show 4 * (1 / ((k + 1 : Nat) : Real)) * (rho : Real) =
        (4 * (rho : Real)) / ((k + 1 : Nat) : Real) by field_simp]
    apply (le_div_iff₀ hk1).2
    have hsideRho' : ((k + 1 : Nat) : Real) ^ 2 <= 4 * (rho : Real) := by
      rw [fkIsingExpandingSquareSide] at hsideRho
      exact_mod_cast hsideRho
    norm_num [Nat.cast_add, Nat.cast_one] at hsideRho' ⊢
    nlinarith
  have hscale : 1032080 * (64 * (m : Real)) <=
      (10000 : Real) ^ 2 * (k + 1 : Nat) ^ 3 := by
    let x : Real := ((k + 1 : Nat) : Real)
    have hx : 1 <= x := by
      dsimp only [x]
      norm_num
    have hpow : x ^ 2 <= x ^ 3 := by
      nlinarith [sq_nonneg x]
    dsimp only [m]
    simp only [fkIsingExpandingSquareSide, Nat.cast_pow]
    change 1032080 * (64 * x ^ 2) <= (10000 : Real) ^ 2 * x ^ 3
    norm_num at hpow ⊢
    nlinarith
  have h :=
    fkIsingSquareBoundaryCenteredRadialPatch_add_side_normalizedNeighbor_norm_sub_le
      m m baseI baseJ R rho (fkIsingExpandingSquareMesh k)
      (k + 1 : Nat) 10000 (64 * (m : Real))
      (fkIsingExpandingSquareSide_pos k) (le_refl _) hm2 hfitI hfitJ
      (fkIsingExpandingSquareMesh_pos k) cutoff hdeep hvariation
      (by positivity) (by norm_num) hradius hscale p p' hrho hp hp' hpp'
  dsimp only [m] at h
  convert h using 1
  simp [fkIsingExpandingSquareMesh]
  ring

end

end StatMech.Universality
