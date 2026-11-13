/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicEndpointPointwise
import Code.Universality.IsingFermionicPhysicalCenteredRadialPatch










namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section



theorem IsingLeapfrogHarmonicOnBox.norm_sub_le_kernelTimeL1
    {R : Nat} {f : IsingLeapfrogBox R → Complex}
    (hf : IsingLeapfrogHarmonicOnBox R f) (B : Real)
    (hB : ∀ q, ‖f q‖ ≤ B) (t t' : Nat)
    (p p' : IsingLeapfrogBox R) :
    ‖f p - f p'‖ ≤
      B * ∑ q, |isingLeapfrogStoppedKernel R t p q -
        isingLeapfrogStoppedKernel R t' p' q| := by
  classical
  rw [← hf.stoppedMean_eq t p, ← hf.stoppedMean_eq t' p']
  unfold isingLeapfrogStoppedMean
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    ‖∑ q, ((isingLeapfrogStoppedKernel R t p q : Complex) -
          isingLeapfrogStoppedKernel R t' p' q) * f q‖ ≤
        ∑ q, ‖((isingLeapfrogStoppedKernel R t p q : Complex) -
          isingLeapfrogStoppedKernel R t' p' q) * f q‖ :=
      norm_sum_le _ _
    _ = ∑ q, |isingLeapfrogStoppedKernel R t p q -
          isingLeapfrogStoppedKernel R t' p' q| * ‖f q‖ := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [norm_mul, show
        ((isingLeapfrogStoppedKernel R t p q : Complex) -
            isingLeapfrogStoppedKernel R t' p' q) =
          ((isingLeapfrogStoppedKernel R t p q -
            isingLeapfrogStoppedKernel R t' p' q : Real) : Complex) by
          norm_num,
        Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ q, |isingLeapfrogStoppedKernel R t p q -
          isingLeapfrogStoppedKernel R t' p' q| * B := by
      apply Finset.sum_le_sum
      intro q _hq
      exact mul_le_mul_of_nonneg_left (hB q) (abs_nonneg _)
    _ = B * ∑ q, |isingLeapfrogStoppedKernel R t p q -
          isingLeapfrogStoppedKernel R t' p' q| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      ring



theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_norm_le_two
    (n : Nat) (hn : 0 < n) (i j : Fin (2 * n)) :
    ‖fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j‖ ≤ 2 := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquareCenteredRadialPatchEdge n i j
  change ‖D.fermionicObservable (.dart (e, .west)) +
      D.fermionicObservable (.dart (e, .east))‖ ≤ 2
  calc
    _ ≤ ‖D.fermionicObservable (.dart (e, .west))‖ +
        ‖D.fermionicObservable (.dart (e, .east))‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add
      (D.norm_fermionicObservable_le_one _)
      (D.norm_fermionicObservable_le_one _)
    _ = 2 := by norm_num




theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_leapfrog_harmonic
    (n i j : Nat) (hn : 0 < n)
    (hi : i + 3 < 2 * n) (hj : j + 3 < 2 * n) :
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i, by omega⟩ ⟨j, by omega⟩ +
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i, by omega⟩ ⟨j + 2, by omega⟩ +
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i + 2, by omega⟩ ⟨j, by omega⟩ +
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩ =
      4 * fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ := by
  have hSW :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
      n i j hn (by omega) (by omega)
  have hSE :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
      n (i + 1) j hn (by omega) (by omega)
  have hNW :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
      n i (j + 1) hn (by omega) (by omega)
  have hNE :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
      n (i + 1) (j + 1) hn (by omega) (by omega)
  have h := isingCellCRAt_leapfrog_harmonic
    (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn)
    i j hSW hSE hNW hNE
  simpa [fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension,
    show i < 2 * n by omega, show j < 2 * n by omega,
    show i + 1 < 2 * n by omega, show j + 1 < 2 * n by omega,
    show i + 2 < 2 * n by omega, show j + 2 < 2 * n by omega] using h



noncomputable def fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
    (n baseI baseJ R : Nat) (hn : 0 < n)
    (hfitI : baseI + R + 1 < 2 * n)
    (hfitJ : baseJ + R + 1 < 2 * n) :
    IsingLeapfrogBox R → Complex :=
  fun p ↦ fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
    ⟨baseI + p.1.1, by have := p.1.2; omega⟩
    ⟨baseJ + p.2.1, by have := p.2.2; omega⟩




theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_harmonic
    (n baseI baseJ R : Nat) (hn : 0 < n)
    (hfitI : baseI + R + 1 < 2 * n)
    (hfitJ : baseJ + R + 1 < 2 * n) :
    IsingLeapfrogHarmonicOnBox R
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
        n baseI baseJ R hn hfitI hfitJ) := by
  intro p hp
  have hx0 : 0 < p.1.1 := by
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hy0 : 0 < p.2.1 := by
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hxR : p.1.1 + 1 < R + 1 := by
    have hxle := p.1.2
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hyR : p.2.1 + 1 < R + 1 := by
    have hyle := p.2.2
    unfold isingLeapfrogBoxBoundary at hp
    omega
  have hphysical :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_leapfrog_harmonic
      n (baseI + p.1.1 - 1) (baseJ + p.2.1 - 1) hn
      (by omega) (by omega)
  have hSW :
      fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
          n baseI baseJ R hn hfitI hfitJ (isingLeapfrogSW R p) =
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨baseI + p.1.1 - 1, by omega⟩
          ⟨baseJ + p.2.1 - 1, by omega⟩ := by
    unfold fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
      isingLeapfrogSW isingLeapfrogWest isingLeapfrogSouth
    congr 2 <;> simp only <;> omega
  have hNW :
      fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
          n baseI baseJ R hn hfitI hfitJ (isingLeapfrogNW R p hp) =
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨baseI + p.1.1 - 1, by omega⟩
          ⟨baseJ + p.2.1 - 1 + 2, by omega⟩ := by
    unfold fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
      isingLeapfrogNW isingLeapfrogWest isingLeapfrogNorth
    congr 2 <;> simp only <;> omega
  have hSE :
      fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
          n baseI baseJ R hn hfitI hfitJ (isingLeapfrogSE R p hp) =
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨baseI + p.1.1 - 1 + 2, by omega⟩
          ⟨baseJ + p.2.1 - 1, by omega⟩ := by
    unfold fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
      isingLeapfrogSE isingLeapfrogEast isingLeapfrogSouth
    congr 2 <;> simp only <;> omega
  have hNE :
      fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
          n baseI baseJ R hn hfitI hfitJ (isingLeapfrogNE R p hp) =
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨baseI + p.1.1 - 1 + 2, by omega⟩
          ⟨baseJ + p.2.1 - 1 + 2, by omega⟩ := by
    unfold fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
      isingLeapfrogNE isingLeapfrogEast isingLeapfrogNorth
    congr 2 <;> simp only <;> omega
  have hC :
      fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
          n baseI baseJ R hn hfitI hfitJ p =
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨baseI + p.1.1 - 1 + 1, by omega⟩
          ⟨baseJ + p.2.1 - 1 + 1, by omega⟩ := by
    unfold fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
    congr 2 <;> omega
  rw [hSW, hNW, hSE, hNE, hC]
  exact hphysical



theorem
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le
    (n baseI baseJ R rho : Nat) (mesh : Real) (hn : 0 < n)
    (hfitI : baseI + R + 1 < 2 * n)
    (hfitJ : baseJ + R + 1 < 2 * n) (hmesh : 0 < mesh)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    Complex.normSq
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
              n baseI baseJ R hn hfitI hfitJ p /
            (Real.sqrt (2 * mesh) : Complex) -
          fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
              n baseI baseJ R hn hfitI hfitJ p' /
            (Real.sqrt (2 * mesh) : Complex)) ≤
      (1032080 / (rho : Real) ^ 3) *
        ∑ q, Complex.normSq
          (fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
              n baseI baseJ R hn hfitI hfitJ q /
            (Real.sqrt (2 * mesh) : Complex)) := by
  let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
    n baseI baseJ R hn hfitI hfitJ
  have hraw : Complex.normSq (F p - F p') ≤
      (1032080 / (rho : Real) ^ 3) * ∑ q, Complex.normSq (F q) :=
    (fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_harmonic
      n baseI baseJ R hn hfitI hfitJ).normSq_sub_le_of_diffusiveGradient
        isingLeapfrogDiffusiveGradientBound_fermionic p p' hrho hp hp' hpp'
  have hsqrtSq : Real.sqrt (2 * mesh) ^ 2 = 2 * mesh := by
    rw [Real.sq_sqrt]
    positivity
  have hnorm (z : Complex) :
      Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) =
        Complex.normSq z / (2 * mesh) := by
    rw [Complex.normSq_div]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by positivity))]
    exact hsqrtSq
  change Complex.normSq
      (F p / (Real.sqrt (2 * mesh) : Complex) -
        F p' / (Real.sqrt (2 * mesh) : Complex)) ≤ _
  rw [← sub_div, hnorm]
  simp_rw [hnorm, ← Finset.sum_div]
  have hden : 0 < 2 * mesh := by positivity
  calc
    Complex.normSq (F p - F p') / (2 * mesh) ≤
        ((1032080 / (rho : Real) ^ 3) *
          ∑ q, Complex.normSq (F q)) / (2 * mesh) :=
      div_le_div_of_nonneg_right hraw hden.le
    _ = _ := by ring



theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_norm_sub_le_diffusive
    (n baseI baseJ R rho : Nat) (hn : 0 < n)
    (hfitI : baseI + R + 1 < 2 * n)
    (hfitJ : baseJ + R + 1 < 2 * n)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    ‖fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
          n baseI baseJ R hn hfitI hfitJ p -
        fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
          n baseI baseJ R hn hfitI hfitJ p'‖ ≤
      304 / (rho : Real) := by
  let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
    n baseI baseJ R hn hfitI hfitJ
  have hmean :=
    (fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_harmonic
      n baseI baseJ R hn hfitI hfitJ).norm_sub_le_kernelTimeL1
        2 (fun q ↦ by
          exact fkIsingSquareBoundaryCenteredRadialPatchFullObservable_norm_le_two
            n hn _ _)
        (rho * rho) (rho * rho + 1) p p'
  have hl1 := isingLeapfrogStoppedKernel_neighbor_timeOffset_diffusive_l1_le
    R rho p p' hrho hp hp' hpp'
  calc
    ‖F p - F p'‖ ≤
        2 * ∑ q, |isingLeapfrogStoppedKernel R (rho * rho) p q -
          isingLeapfrogStoppedKernel R (rho * rho + 1) p' q| := hmean
    _ ≤ 2 * (152 / (rho : Real)) :=
      mul_le_mul_of_nonneg_left hl1 (by norm_num)
    _ = 304 / (rho : Real) := by ring



theorem
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_physicalNormalized_norm_sub_le
    (n baseI baseJ R rho : Nat) (mesh : Real) (hn : 0 < n)
    (hfitI : baseI + R + 1 < 2 * n)
    (hfitJ : baseJ + R + 1 < 2 * n) (hmesh : 0 < mesh)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    ‖fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
          n baseI baseJ R hn hfitI hfitJ p /
            (Real.sqrt (2 * mesh) : Complex) -
        fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
          n baseI baseJ R hn hfitI hfitJ p' /
            (Real.sqrt (2 * mesh) : Complex)‖ ≤
      304 / ((rho : Real) * Real.sqrt (2 * mesh)) := by
  have hraw :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_norm_sub_le_diffusive
      n baseI baseJ R rho hn hfitI hfitJ p p' hrho hp hp' hpp'
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 (by positivity))]
  calc
    ‖fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
          n baseI baseJ R hn hfitI hfitJ p -
        fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow
          n baseI baseJ R hn hfitI hfitJ p'‖ /
          Real.sqrt (2 * mesh) ≤
      (304 / (rho : Real)) / Real.sqrt (2 * mesh) := by
        exact div_le_div_of_nonneg_right hraw (Real.sqrt_nonneg _)
    _ = 304 / ((rho : Real) * Real.sqrt (2 * mesh)) := by ring

end

end StatMech.Universality
