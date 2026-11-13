/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicCenteredNESectorRate










namespace StatMech.Universality

noncomputable section



theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le
    (n i j : Nat) (hn : 0 < n)
    (hi0 : 0 < i) (hi1 : i + 1 < 2 * n)
    (hj0 : 0 < j) (hj1 : j + 1 < 2 * n) (r delta : Real)
    (hNS : ‖fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex) -
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i - 1, by omega⟩ ⟨j, by omega⟩ / (r : Complex)‖ ≤ delta)
    (hEW : ‖fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i, by omega⟩ ⟨j, by omega⟩ / (r : Complex) -
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex)‖ ≤ delta) :
    let north := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨i, by omega⟩ ⟨j - 1, by omega⟩
    let east := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨i, by omega⟩ ⟨j, by omega⟩
    let south := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨i - 1, by omega⟩ ⟨j, by omega⟩
    let west := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
    ‖north / (r : Complex) - east / (r : Complex)‖ ≤ 2 * delta ∧
      ‖east / (r : Complex) - south / (r : Complex)‖ ≤ 2 * delta ∧
      ‖south / (r : Complex) - west / (r : Complex)‖ ≤ 2 * delta ∧
      ‖west / (r : Complex) - north / (r : Complex)‖ ≤ 2 * delta := by
  dsimp only
  by_cases heven : Even (i + j)
  · have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad
        n i j hn hi0 hi1 hj0 hj1 heven)
    exact projectionCycle_crossParity_norm_div_sub_div_le _ _ _ _ r delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hNS hEW
  · have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_odd
        n i j hn hi0 hi1 hj0 hj1 heven)
    have hSN := hNS
    have hWE := hEW
    rw [norm_sub_rev] at hSN hWE
    have hodd := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ r delta hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2
      hSN hWE
    exact ⟨hodd.2.2.1, hodd.2.2.2, hodd.1, hodd.2.1⟩



def FKIsingExpandingCenteredDiagonalCellBound
    (L : NNReal) (k i j : Nat) : Prop :=
  ∀ (hi0 : 0 < i)
    (hi1 : i + 1 < 2 * fkIsingExpandingSquareSide k)
    (hj0 : 0 < j)
    (hj1 : j + 1 < 2 * fkIsingExpandingSquareSide k),
    let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservable
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    let normalization := Real.sqrt (2 * fkIsingExpandingSquareMesh k)
    ‖F ⟨i, by omega⟩ ⟨j - 1, by omega⟩ / normalization -
        F ⟨i - 1, by omega⟩ ⟨j, by omega⟩ / normalization‖ ≤
        fkIsingExpandingSquareScale k * (L : Real) ∧
      ‖F ⟨i, by omega⟩ ⟨j, by omega⟩ / normalization -
        F ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ / normalization‖ ≤
        fkIsingExpandingSquareScale k * (L : Real)




def FKIsingExpandingCenteredRightEvenDiagonalCellBound
    (L : NNReal) (k J : Nat) : Prop :=
  ∀ (hJ0 : 0 < J)
    (hJ : J < 2 * fkIsingExpandingSquareSide k)
    (heven : Even ((2 * fkIsingExpandingSquareSide k - 1) + J)),
    let n := fkIsingExpandingSquareSide k
    let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n
      (fkIsingExpandingSquareSide_pos k)
    let normalization := Real.sqrt (2 * fkIsingExpandingSquareMesh k)
    ‖F ⟨2 * n - 1, by omega⟩ ⟨J - 1, by omega⟩ / normalization -
        F ⟨2 * n - 2, by omega⟩ ⟨J, hJ⟩ / normalization‖ ≤
        fkIsingExpandingSquareScale k * (L : Real) ∧
      ‖F ⟨2 * n - 1, by omega⟩ ⟨J, hJ⟩ / normalization -
        F ⟨2 * n - 2, by omega⟩ ⟨J - 1, by omega⟩ / normalization‖ ≤
        fkIsingExpandingSquareScale k * (L : Real)




theorem
    fkIsingExpandingCenteredHorizontalRight_of_even_diagonal
    (L : NNReal) (k : Nat)
    (hdiag : ∀ J,
      FKIsingExpandingCenteredRightEvenDiagonalCellBound L k J) :
    ∀ a b : Nat,
      ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
        (hb : b < 2 * fkIsingExpandingSquareSide k),
        a + 2 = 2 * fkIsingExpandingSquareSide k →
          FKIsingExpandingCenteredHorizontalNeighborBound (2 * L) k a b := by
  intro a b ha hb hright
  intro _ha _hb
  let n := fkIsingExpandingSquareSide k
  let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n
    (fkIsingExpandingSquareSide_pos k)
  let normalization := Real.sqrt (2 * fkIsingExpandingSquareMesh k)
  let delta := fkIsingExpandingSquareScale k * (L : Real)
  have hn : 0 < n := fkIsingExpandingSquareSide_pos k
  have ha0 : a = 2 * n - 2 := by omega
  subst a
  by_cases hbEven : Even b
  · let J := b + 1
    have hJ0 : 0 < J := by simp [J]
    have hJ : J < 2 * n := by
      have hmod := Nat.even_iff.mp hbEven
      dsimp only [J, n]
      omega
    have heven : Even ((2 * n - 1) + J) := by
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp hbEven
      dsimp only [J]
      omega
    have hd := hdiag J hJ0 (by simpa [n] using hJ) (by simpa [n] using heven)
    dsimp only [FKIsingExpandingCenteredRightEvenDiagonalCellBound] at hd
    have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_even
        n J hn hJ0 hJ heven
    have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _ hquad
    have hedges := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ normalization delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hd.1 hd.2
    rw [norm_sub_rev]
    convert hedges.2.2.2 using 1 <;>
      simp [FKIsingExpandingCenteredHorizontalNeighborBound, F,
        normalization, delta, J, n] <;> try ring <;> omega
  · let J := b
    have hJ0 : 0 < J := by
      dsimp only [J]
      have hodd := Nat.not_even_iff.mp hbEven
      omega
    have hJ : J < 2 * n := by simpa [J, n] using hb
    have heven : Even ((2 * n - 1) + J) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp hbEven
      dsimp only [J]
      omega
    have hd := hdiag J hJ0 (by simpa [n] using hJ) (by simpa [n] using heven)
    dsimp only [FKIsingExpandingCenteredRightEvenDiagonalCellBound] at hd
    have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_even
        n J hn hJ0 hJ heven
    have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _ hquad
    have hedges := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ normalization delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hd.1 hd.2
    convert hedges.2.1 using 1 <;>
      simp [FKIsingExpandingCenteredHorizontalNeighborBound, F,
        normalization, delta, J, n] <;> try ring <;> omega



def FKIsingExpandingCenteredTopEvenDiagonalCellBound
    (L : NNReal) (k I : Nat) : Prop :=
  ∀ (hI0 : 0 < I)
    (hI : I < 2 * fkIsingExpandingSquareSide k)
    (heven : Even (I + (2 * fkIsingExpandingSquareSide k - 1))),
    let n := fkIsingExpandingSquareSide k
    let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n
      (fkIsingExpandingSquareSide_pos k)
    let normalization := Real.sqrt (2 * fkIsingExpandingSquareMesh k)
    ‖F ⟨I, hI⟩ ⟨2 * n - 2, by omega⟩ / normalization -
        F ⟨I - 1, by omega⟩ ⟨2 * n - 1, by omega⟩ / normalization‖ ≤
        fkIsingExpandingSquareScale k * (L : Real) ∧
      ‖F ⟨I, hI⟩ ⟨2 * n - 1, by omega⟩ / normalization -
        F ⟨I - 1, by omega⟩ ⟨2 * n - 2, by omega⟩ / normalization‖ ≤
        fkIsingExpandingSquareScale k * (L : Real)



theorem
    fkIsingExpandingCenteredVerticalTop_of_even_diagonal
    (L : NNReal) (k : Nat)
    (hdiag : ∀ I,
      FKIsingExpandingCenteredTopEvenDiagonalCellBound L k I) :
    ∀ a b : Nat,
      ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
        (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
        b + 2 = 2 * fkIsingExpandingSquareSide k →
          FKIsingExpandingCenteredVerticalNeighborBound (2 * L) k a b := by
  intro a b ha hb htop
  intro _ha _hb
  let n := fkIsingExpandingSquareSide k
  let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n
    (fkIsingExpandingSquareSide_pos k)
  let normalization := Real.sqrt (2 * fkIsingExpandingSquareMesh k)
  let delta := fkIsingExpandingSquareScale k * (L : Real)
  have hn : 0 < n := fkIsingExpandingSquareSide_pos k
  have hb0 : b = 2 * n - 2 := by omega
  subst b
  by_cases haEven : Even a
  · let I := a + 1
    have hI0 : 0 < I := by simp [I]
    have hI : I < 2 * n := by
      have hmod := Nat.even_iff.mp haEven
      dsimp only [I, n]
      omega
    have heven : Even (I + (2 * n - 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp haEven
      dsimp only [I]
      omega
    have hd := hdiag I hI0 (by simpa [n] using hI) (by simpa [n] using heven)
    dsimp only [FKIsingExpandingCenteredTopEvenDiagonalCellBound] at hd
    have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_even
        n I hn hI0 hI heven
    have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _ hquad
    have hedges := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ normalization delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hd.1 hd.2
    convert hedges.2.2.1 using 1 <;>
      simp [FKIsingExpandingCenteredVerticalNeighborBound, F,
        normalization, delta, I, n] <;> try ring <;> omega
  · let I := a
    have hI0 : 0 < I := by
      dsimp only [I]
      have hodd := Nat.not_even_iff.mp haEven
      omega
    have hI : I < 2 * n := by simpa [I, n] using ha
    have heven : Even (I + (2 * n - 1)) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp haEven
      dsimp only [I]
      omega
    have hd := hdiag I hI0 (by simpa [n] using hI) (by simpa [n] using heven)
    dsimp only [FKIsingExpandingCenteredTopEvenDiagonalCellBound] at hd
    have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_even
        n I hn hI0 hI heven
    have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _ hquad
    have hedges := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ normalization delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hd.1 hd.2
    rw [norm_sub_rev]
    convert hedges.1 using 1 <;>
      simp [FKIsingExpandingCenteredVerticalNeighborBound, F,
        normalization, delta, I, n] <;> try ring <;> omega




def FKIsingExpandingCenteredTopDiagonalCellBound
    (L : NNReal) (k I : Nat) : Prop :=
  ∀ (hI0 : 0 < I) (hI : I < 2 * fkIsingExpandingSquareSide k),
    let n := fkIsingExpandingSquareSide k
    let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n
      (fkIsingExpandingSquareSide_pos k)
    let normalization := Real.sqrt (2 * fkIsingExpandingSquareMesh k)
    ‖F ⟨I, hI⟩ ⟨2 * n - 2, by omega⟩ / normalization -
        F ⟨I - 1, by omega⟩ ⟨2 * n - 1, by omega⟩ / normalization‖ ≤
        fkIsingExpandingSquareScale k * (L : Real) ∧
      ‖F ⟨I, hI⟩ ⟨2 * n - 1, by omega⟩ / normalization -
        F ⟨I - 1, by omega⟩ ⟨2 * n - 2, by omega⟩ / normalization‖ ≤
        fkIsingExpandingSquareScale k * (L : Real)


def FKIsingExpandingCenteredRightDiagonalCellBound
    (L : NNReal) (k J : Nat) : Prop :=
  ∀ (hJ0 : 0 < J) (hJ : J < 2 * fkIsingExpandingSquareSide k),
    let n := fkIsingExpandingSquareSide k
    let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n
      (fkIsingExpandingSquareSide_pos k)
    let normalization := Real.sqrt (2 * fkIsingExpandingSquareMesh k)
    ‖F ⟨2 * n - 1, by omega⟩ ⟨J - 1, by omega⟩ / normalization -
        F ⟨2 * n - 2, by omega⟩ ⟨J, hJ⟩ / normalization‖ ≤
        fkIsingExpandingSquareScale k * (L : Real) ∧
      ‖F ⟨2 * n - 1, by omega⟩ ⟨J, hJ⟩ / normalization -
        F ⟨2 * n - 2, by omega⟩ ⟨J - 1, by omega⟩ / normalization‖ ≤
        fkIsingExpandingSquareScale k * (L : Real)



theorem fkIsingExpandingCenteredHorizontalTop_of_diagonal
    (L : NNReal) (k : Nat)
    (hdiag : ∀ I, FKIsingExpandingCenteredTopDiagonalCellBound L k I) :
    ∀ a b : Nat,
      ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
        (hb : b < 2 * fkIsingExpandingSquareSide k),
        b + 1 = 2 * fkIsingExpandingSquareSide k →
          FKIsingExpandingCenteredHorizontalNeighborBound (2 * L) k a b := by
  intro a b ha hb htop
  intro _ha _hb
  let n := fkIsingExpandingSquareSide k
  let I := a + 1
  let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n
    (fkIsingExpandingSquareSide_pos k)
  let normalization := Real.sqrt (2 * fkIsingExpandingSquareMesh k)
  let delta := fkIsingExpandingSquareScale k * (L : Real)
  have hn : 0 < n := fkIsingExpandingSquareSide_pos k
  have hI0 : 0 < I := by simp [I]
  have hI : I < 2 * n := by simpa [I, n] using ha
  have hb0 : b = 2 * n - 1 := by omega
  subst b
  have hd := hdiag I hI0 (by simpa [n] using hI)
  dsimp only [FKIsingExpandingCenteredTopDiagonalCellBound] at hd
  by_cases heven : Even (I + (2 * n - 1))
  · have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_even
        n I hn hI0 hI heven
    have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _ hquad
    have hedges := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ normalization delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hd.1 hd.2
    convert hedges.2.1 using 1 <;>
      simp [FKIsingExpandingCenteredHorizontalNeighborBound, F,
        normalization, delta, I, n] <;> try ring <;> omega
  · have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_odd
        n I hn hI0 hI heven
    have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _ hquad
    have hSN := hd.1
    have hWE := hd.2
    rw [norm_sub_rev] at hSN hWE
    have hodd := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ normalization delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hSN hWE
    convert hodd.2.2.2 using 1 <;>
      simp [FKIsingExpandingCenteredHorizontalNeighborBound, F,
        normalization, delta, I, n] <;> try ring <;> omega



theorem fkIsingExpandingCenteredVerticalRight_of_diagonal
    (L : NNReal) (k : Nat)
    (hdiag : ∀ J, FKIsingExpandingCenteredRightDiagonalCellBound L k J) :
    ∀ a b : Nat,
      ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
        (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
        a + 1 = 2 * fkIsingExpandingSquareSide k →
          FKIsingExpandingCenteredVerticalNeighborBound (2 * L) k a b := by
  intro a b ha hb hright
  intro _ha _hb
  let n := fkIsingExpandingSquareSide k
  let J := b + 1
  let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n
    (fkIsingExpandingSquareSide_pos k)
  let normalization := Real.sqrt (2 * fkIsingExpandingSquareMesh k)
  let delta := fkIsingExpandingSquareScale k * (L : Real)
  have hn : 0 < n := fkIsingExpandingSquareSide_pos k
  have hJ0 : 0 < J := by simp [J]
  have hJ : J < 2 * n := by simpa [J, n] using hb
  have ha0 : a = 2 * n - 1 := by omega
  subst a
  have hd := hdiag J hJ0 (by simpa [n] using hJ)
  dsimp only [FKIsingExpandingCenteredRightDiagonalCellBound] at hd
  by_cases heven : Even ((2 * n - 1) + J)
  · have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_even
        n J hn hJ0 hJ heven
    have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _ hquad
    have hedges := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ normalization delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hd.1 hd.2
    rw [norm_sub_rev]
    convert hedges.1 using 1 <;>
      simp [FKIsingExpandingCenteredVerticalNeighborBound, F,
        normalization, delta, J, n] <;> try ring <;> omega
  · have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_odd
        n J hn hJ0 hJ heven
    have hcycle := IsingSquareSHolomorphicQuad.projection_cycle _ _ _ _ hquad
    have hSN := hd.1
    have hWE := hd.2
    rw [norm_sub_rev] at hSN hWE
    have hodd := projectionCycle_crossParity_norm_div_sub_div_le
      _ _ _ _ normalization delta
      hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hSN hWE
    rw [norm_sub_rev]
    convert hodd.2.2.1 using 1 <;>
      simp [FKIsingExpandingCenteredVerticalNeighborBound, F,
        normalization, delta, J, n] <;> try ring <;> omega




theorem
    fkIsingExpandingBoundarySquareCenteredNE_diagonalCellBound
    (k baseI baseJ R rho cutoff a b : Nat) (hk : 1 ≤ k)
    (hfitI : baseI + R + 1 < fkIsingExpandingSquareSide k)
    (hfitJ : baseJ + R + 1 < fkIsingExpandingSquareSide k)
    (hcutoff : 0 < cutoff)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell
          (fkIsingExpandingSquareSide k) baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells
          (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide k)
          (le_refl _) (by
            simp only [fkIsingExpandingSquareSide, pow_two]
            nlinarith) cutoff)
    (hsideCutoff : fkIsingExpandingSquareSide k ≤ 4 * cutoff)
    (hsideRho : fkIsingExpandingSquareSide k ≤ 4 * rho)
    (ha0 : 0 < a) (haR : a < R) (hb0 : 0 < b) (hbR : b < R)
    (hrho : 0 < rho)
    (hmarginN : IsingLeapfrogInteriorMargin R rho
      (⟨a, by omega⟩, ⟨b - 1, by omega⟩))
    (hmarginE : IsingLeapfrogInteriorMargin R rho
      (⟨a, by omega⟩, ⟨b, by omega⟩))
    (hmarginS : IsingLeapfrogInteriorMargin R rho
      (⟨a - 1, by omega⟩, ⟨b, by omega⟩))
    (hmarginW : IsingLeapfrogInteriorMargin R rho
      (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩)) :
    FKIsingExpandingCenteredDiagonalCellBound 40000 k
      (fkIsingExpandingSquareSide k + (baseI + a))
      (fkIsingExpandingSquareSide k + (baseJ + b)) := by
  intro hi0 hi1 hj0 hj1
  let pN : IsingLeapfrogBox R :=
    (⟨a, by omega⟩, ⟨b - 1, by omega⟩)
  let pE : IsingLeapfrogBox R :=
    (⟨a, by omega⟩, ⟨b, by omega⟩)
  let pS : IsingLeapfrogBox R :=
    (⟨a - 1, by omega⟩, ⟨b, by omega⟩)
  let pW : IsingLeapfrogBox R :=
    (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩)
  have hNS :=
    fkIsingExpandingBoundarySquareCenteredNE_normalizedNeighbor_norm_sub_le
      k baseI baseJ R rho cutoff hk hfitI hfitJ hcutoff hdeep
      hsideCutoff hsideRho pN pS hrho
      (by simpa [pN] using hmarginN) (by simpa [pS] using hmarginS) (by
        unfold IsingLeapfrogDiagonalAdjacent
        simp [pN, pS, Nat.dist]
        omega)
  have hEW :=
    fkIsingExpandingBoundarySquareCenteredNE_normalizedNeighbor_norm_sub_le
      k baseI baseJ R rho cutoff hk hfitI hfitJ hcutoff hdeep
      hsideCutoff hsideRho pE pW hrho
      (by simpa [pE] using hmarginE) (by simpa [pW] using hmarginW) (by
        unfold IsingLeapfrogDiagonalAdjacent
        simp [pE, pW, Nat.dist]
        omega)
  have hIa : fkIsingExpandingSquareSide k + (baseI + (a - 1)) =
      fkIsingExpandingSquareSide k + (baseI + a) - 1 := by omega
  have hJb : fkIsingExpandingSquareSide k + (baseJ + (b - 1)) =
      fkIsingExpandingSquareSide k + (baseJ + b) - 1 := by omega
  constructor
  · simpa [pN, pS, hIa, hJb] using hNS
  · simpa [pE, pW, hIa, hJb] using hEW



def FKIsingExpandingCenteredOuterCollarBound
    (L : NNReal) (k : Nat) : Prop :=
  (∀ a b : Nat,
    ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
      (hb : b < 2 * fkIsingExpandingSquareSide k),
    ¬ (a + 2 < 2 * fkIsingExpandingSquareSide k ∧
        b + 1 < 2 * fkIsingExpandingSquareSide k) →
      FKIsingExpandingCenteredHorizontalNeighborBound (2 * L) k a b) ∧
  (∀ a b : Nat,
    ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
      (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
    ¬ (a + 1 < 2 * fkIsingExpandingSquareSide k ∧
        b + 2 < 2 * fkIsingExpandingSquareSide k) →
      FKIsingExpandingCenteredVerticalNeighborBound (2 * L) k a b)




structure FKIsingExpandingCenteredTopRightBoundaryEdgeBounds
    (L : NNReal) (k : Nat) : Prop where
  horizontalRight : ∀ a b : Nat,
    ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
      (hb : b < 2 * fkIsingExpandingSquareSide k),
      a + 2 = 2 * fkIsingExpandingSquareSide k →
        FKIsingExpandingCenteredHorizontalNeighborBound (2 * L) k a b
  horizontalTop : ∀ a b : Nat,
    ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
      (hb : b < 2 * fkIsingExpandingSquareSide k),
      b + 1 = 2 * fkIsingExpandingSquareSide k →
        FKIsingExpandingCenteredHorizontalNeighborBound (2 * L) k a b
  verticalRight : ∀ a b : Nat,
    ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
      (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
      a + 1 = 2 * fkIsingExpandingSquareSide k →
        FKIsingExpandingCenteredVerticalNeighborBound (2 * L) k a b
  verticalTop : ∀ a b : Nat,
    ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
      (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
      b + 2 = 2 * fkIsingExpandingSquareSide k →
        FKIsingExpandingCenteredVerticalNeighborBound (2 * L) k a b



theorem FKIsingExpandingCenteredTopRightBoundaryEdgeBounds.outerCollarBound
    {L : NNReal} {k : Nat}
    (h : FKIsingExpandingCenteredTopRightBoundaryEdgeBounds L k) :
    FKIsingExpandingCenteredOuterCollarBound L k := by
  constructor
  · intro a b ha hb houter
    by_cases hright : a + 2 = 2 * fkIsingExpandingSquareSide k
    · exact h.horizontalRight a b ha hb hright
    · have htop : b + 1 = 2 * fkIsingExpandingSquareSide k := by omega
      exact h.horizontalTop a b ha hb htop
  · intro a b ha hb houter
    by_cases hright : a + 1 = 2 * fkIsingExpandingSquareSide k
    · exact h.verticalRight a b ha hb hright
    · have htop : b + 2 = 2 * fkIsingExpandingSquareSide k := by omega
      exact h.verticalTop a b ha hb htop




theorem
    fkIsingExpandingCenteredTopRightBoundaryEdgeBounds_of_diagonal
    (L : NNReal) (k : Nat)
    (hright : ∀ J,
      FKIsingExpandingCenteredRightDiagonalCellBound L k J)
    (htop : ∀ I,
      FKIsingExpandingCenteredTopDiagonalCellBound L k I) :
    FKIsingExpandingCenteredTopRightBoundaryEdgeBounds L k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply fkIsingExpandingCenteredHorizontalRight_of_even_diagonal L k
    intro J hJ0 hJ _heven
    exact hright J hJ0 hJ
  · exact fkIsingExpandingCenteredHorizontalTop_of_diagonal L k htop
  · exact fkIsingExpandingCenteredVerticalRight_of_diagonal L k hright
  · apply fkIsingExpandingCenteredVerticalTop_of_even_diagonal L k
    intro I hI0 hI _heven
    exact htop I hI0 hI



theorem fkIsingExpandingCenteredOuterCollarBound_of_diagonal
    (L : NNReal) (k : Nat)
    (hright : ∀ J,
      FKIsingExpandingCenteredRightDiagonalCellBound L k J)
    (htop : ∀ I,
      FKIsingExpandingCenteredTopDiagonalCellBound L k I) :
    FKIsingExpandingCenteredOuterCollarBound L k :=
  (fkIsingExpandingCenteredTopRightBoundaryEdgeBounds_of_diagonal
    L k hright htop).outerCollarBound




theorem
    fkIsingExpandingCenteredNeighborTransport_of_four_sector_diagonal_and_collar
    (L : NNReal) (N : Nat) (hN : 1 ≤ N)
    (hdiag : ∀ q : Fin 4, ∀ k, N ≤ k → ∀ i j,
      isingCenteredRadialIndexSector
          (fkIsingExpandingSquareSide k) i j = q →
        FKIsingExpandingCenteredDiagonalCellBound L k i j)
    (hcollar : ∀ k, N ≤ k →
      FKIsingExpandingCenteredOuterCollarBound L k) :
    FKIsingExpandingCenteredNeighborTransport := by
  apply fkIsingExpandingCenteredNeighborTransport_of_four_sector_bounds
    (2 * L) N
  · intro q k hk a b _hsector
    intro ha hb
    by_cases hinner :
        a + 2 < 2 * fkIsingExpandingSquareSide k ∧
          b + 1 < 2 * fkIsingExpandingSquareSide k
    · let i := a + 1
      let j := if b = 0 then 1 else b
      have hk1 : 1 ≤ k := le_trans hN hk
      have hn4 : 4 ≤ fkIsingExpandingSquareSide k := by
        rw [fkIsingExpandingSquareSide]
        nlinarith
      have hi0 : 0 < i := by simp [i]
      have hi1 : i + 1 < 2 * fkIsingExpandingSquareSide k := by
        simpa [i] using hinner.1
      have hj0 : 0 < j := by
        simp only [j]
        split <;> omega
      have hj1 : j + 1 < 2 * fkIsingExpandingSquareSide k := by
        simp only [j]
        split
        · omega
        · exact hinner.2
      have hd := hdiag
        (isingCenteredRadialIndexSector
          (fkIsingExpandingSquareSide k) i j) k hk i j rfl
          hi0 hi1 hj0 hj1
      dsimp only [FKIsingExpandingCenteredDiagonalCellBound] at hd
      have hedges :=
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le
          (fkIsingExpandingSquareSide k) i j
          (fkIsingExpandingSquareSide_pos k) hi0 hi1 hj0 hj1
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k))
          (fkIsingExpandingSquareScale k * (L : Real)) hd.1 hd.2
      dsimp only at hedges
      by_cases hb0 : b = 0
      · subst b
        rw [norm_sub_rev]
        convert hedges.2.2.2 using 1 <;> simp [i, j] <;> ring
      · convert hedges.2.1 using 1 <;> simp [i, j, hb0] <;> ring
    · exact (hcollar k hk).1 a b ha hb hinner ha hb
  · intro q k hk a b _hsector
    intro ha hb
    by_cases hinner :
        a + 1 < 2 * fkIsingExpandingSquareSide k ∧
          b + 2 < 2 * fkIsingExpandingSquareSide k
    · let i := if a = 0 then 1 else a
      let j := b + 1
      have hk1 : 1 ≤ k := le_trans hN hk
      have hn4 : 4 ≤ fkIsingExpandingSquareSide k := by
        rw [fkIsingExpandingSquareSide]
        nlinarith
      have hi0 : 0 < i := by
        simp only [i]
        split <;> omega
      have hi1 : i + 1 < 2 * fkIsingExpandingSquareSide k := by
        simp only [i]
        split
        · omega
        · exact hinner.1
      have hj0 : 0 < j := by simp [j]
      have hj1 : j + 1 < 2 * fkIsingExpandingSquareSide k := by
        simpa [j] using hinner.2
      have hd := hdiag
        (isingCenteredRadialIndexSector
          (fkIsingExpandingSquareSide k) i j) k hk i j rfl
          hi0 hi1 hj0 hj1
      dsimp only [FKIsingExpandingCenteredDiagonalCellBound] at hd
      have hedges :=
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le
          (fkIsingExpandingSquareSide k) i j
          (fkIsingExpandingSquareSide_pos k) hi0 hi1 hj0 hj1
          (Real.sqrt (2 * fkIsingExpandingSquareMesh k))
          (fkIsingExpandingSquareScale k * (L : Real)) hd.1 hd.2
      dsimp only at hedges
      by_cases ha0 : a = 0
      · subst a
        convert hedges.2.2.1 using 1 <;> simp [i, j] <;> ring
      · rw [norm_sub_rev]
        convert hedges.1 using 1 <;> simp [i, j, ha0] <;> ring
    · exact (hcollar k hk).2 a b ha hb hinner ha hb




theorem
    fkIsingExpandingCenteredStrictNeighborTransport_of_four_sector_diagonal
    (L : NNReal) (N : Nat) (hN : 1 ≤ N)
    (hdiag : ∀ q : Fin 4, ∀ k, N ≤ k → ∀ i j,
      isingCenteredRadialIndexSector
          (fkIsingExpandingSquareSide k) i j = q →
        FKIsingExpandingCenteredDiagonalCellBound L k i j) :
    FKIsingExpandingCenteredStrictNeighborTransport := by
  refine ⟨2 * L, N, ?_⟩
  intro k hk
  constructor
  · intro a b ha hb ha2 hb1
    let i := a + 1
    let j := if b = 0 then 1 else b
    have hk1 : 1 ≤ k := le_trans hN hk
    have hn4 : 4 ≤ fkIsingExpandingSquareSide k := by
      rw [fkIsingExpandingSquareSide]
      nlinarith
    have hi0 : 0 < i := by simp [i]
    have hi1 : i + 1 < 2 * fkIsingExpandingSquareSide k := by
      simpa [i] using ha2
    have hj0 : 0 < j := by
      simp only [j]
      split <;> omega
    have hj1 : j + 1 < 2 * fkIsingExpandingSquareSide k := by
      simp only [j]
      split
      · omega
      · exact hb1
    have hd := hdiag
      (isingCenteredRadialIndexSector
        (fkIsingExpandingSquareSide k) i j) k hk i j rfl
        hi0 hi1 hj0 hj1
    dsimp only [FKIsingExpandingCenteredDiagonalCellBound] at hd
    have hedges :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le
        (fkIsingExpandingSquareSide k) i j
        (fkIsingExpandingSquareSide_pos k) hi0 hi1 hj0 hj1
        (Real.sqrt (2 * fkIsingExpandingSquareMesh k))
        (fkIsingExpandingSquareScale k * (L : Real)) hd.1 hd.2
    dsimp only at hedges
    by_cases hb0 : b = 0
    · subst b
      rw [norm_sub_rev]
      convert hedges.2.2.2 using 1 <;> simp [i, j] <;> ring
    · convert hedges.2.1 using 1 <;> simp [i, j, hb0] <;> ring
  · intro a b ha hb ha1 hb2
    let i := if a = 0 then 1 else a
    let j := b + 1
    have hk1 : 1 ≤ k := le_trans hN hk
    have hn4 : 4 ≤ fkIsingExpandingSquareSide k := by
      rw [fkIsingExpandingSquareSide]
      nlinarith
    have hi0 : 0 < i := by
      simp only [i]
      split <;> omega
    have hi1 : i + 1 < 2 * fkIsingExpandingSquareSide k := by
      simp only [i]
      split
      · omega
      · exact ha1
    have hj0 : 0 < j := by simp [j]
    have hj1 : j + 1 < 2 * fkIsingExpandingSquareSide k := by
      simpa [j] using hb2
    have hd := hdiag
      (isingCenteredRadialIndexSector
        (fkIsingExpandingSquareSide k) i j) k hk i j rfl
        hi0 hi1 hj0 hj1
    dsimp only [FKIsingExpandingCenteredDiagonalCellBound] at hd
    have hedges :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le
        (fkIsingExpandingSquareSide k) i j
        (fkIsingExpandingSquareSide_pos k) hi0 hi1 hj0 hj1
        (Real.sqrt (2 * fkIsingExpandingSquareMesh k))
        (fkIsingExpandingSquareScale k * (L : Real)) hd.1 hd.2
    dsimp only at hedges
    by_cases ha0 : a = 0
    · subst a
      convert hedges.2.2.1 using 1 <;> simp [i, j] <;> ring
    · rw [norm_sub_rev]
      convert hedges.1 using 1 <;> simp [i, j, ha0] <;> ring



theorem
    fkIsingExpandingCenteredNeighborTransport_of_four_sector_and_boundary_diagonal
    (L : NNReal) (N : Nat) (hN : 1 ≤ N)
    (hdiag : ∀ q : Fin 4, ∀ k, N ≤ k → ∀ i j,
      isingCenteredRadialIndexSector
          (fkIsingExpandingSquareSide k) i j = q →
        FKIsingExpandingCenteredDiagonalCellBound L k i j)
    (hright : ∀ k, N ≤ k → ∀ J,
      FKIsingExpandingCenteredRightDiagonalCellBound L k J)
    (htop : ∀ k, N ≤ k → ∀ I,
      FKIsingExpandingCenteredTopDiagonalCellBound L k I) :
    FKIsingExpandingCenteredNeighborTransport := by
  apply
    fkIsingExpandingCenteredNeighborTransport_of_four_sector_diagonal_and_collar
      L N hN hdiag
  intro k hk
  exact fkIsingExpandingCenteredOuterCollarBound_of_diagonal
    L k (hright k hk) (htop k hk)

end

end StatMech.Universality
