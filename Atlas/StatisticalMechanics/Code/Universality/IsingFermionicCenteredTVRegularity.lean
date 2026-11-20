/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicCenteredStoppedWalk
import Code.Universality.IsingFermionicCenteredFourSectorAssembly










namespace StatMech.Universality

open Metric Set

noncomputable section



theorem
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le_of_margin
    (n i j rho : Nat) (mesh : Real) (hn : 0 < n)
    (hi0 : 0 < i) (hi1 : i + 1 < 2 * n)
    (hj0 : 0 < j) (hj1 : j + 1 < 2 * n)
    (hrho : 0 < rho) (hmesh : 0 < mesh)
    (hiLeft : rho ≤ i - 1) (hiRight : i + rho ≤ 2 * n - 2)
    (hjBottom : rho ≤ j - 1) (hjTop : j + rho ≤ 2 * n - 2) :
    let north := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨i, by omega⟩ ⟨j - 1, by omega⟩
    let east := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨i, by omega⟩ ⟨j, by omega⟩
    let south := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨i - 1, by omega⟩ ⟨j, by omega⟩
    let west := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
      ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
    ‖north / (Real.sqrt (2 * mesh) : Complex) -
        east / (Real.sqrt (2 * mesh) : Complex)‖ ≤
          608 / ((rho : Real) * Real.sqrt (2 * mesh)) ∧
      ‖east / (Real.sqrt (2 * mesh) : Complex) -
        south / (Real.sqrt (2 * mesh) : Complex)‖ ≤
          608 / ((rho : Real) * Real.sqrt (2 * mesh)) ∧
      ‖south / (Real.sqrt (2 * mesh) : Complex) -
        west / (Real.sqrt (2 * mesh) : Complex)‖ ≤
          608 / ((rho : Real) * Real.sqrt (2 * mesh)) ∧
      ‖west / (Real.sqrt (2 * mesh) : Complex) -
        north / (Real.sqrt (2 * mesh) : Complex)‖ ≤
          608 / ((rho : Real) * Real.sqrt (2 * mesh)) := by
  let R := 2 * n - 2
  have hfit : 0 + R + 1 < 2 * n := by
    dsimp [R]
    omega
  let pN : IsingLeapfrogBox R :=
    (⟨i, by dsimp [R]; omega⟩, ⟨j - 1, by dsimp [R]; omega⟩)
  let pE : IsingLeapfrogBox R :=
    (⟨i, by dsimp [R]; omega⟩, ⟨j, by dsimp [R]; omega⟩)
  let pS : IsingLeapfrogBox R :=
    (⟨i - 1, by dsimp [R]; omega⟩, ⟨j, by dsimp [R]; omega⟩)
  let pW : IsingLeapfrogBox R :=
    (⟨i - 1, by dsimp [R]; omega⟩, ⟨j - 1, by dsimp [R]; omega⟩)
  have hmarginN : IsingLeapfrogInteriorMargin R rho pN := by
    simp only [IsingLeapfrogInteriorMargin, pN]
    dsimp [R]
    omega
  have hmarginE : IsingLeapfrogInteriorMargin R rho pE := by
    simp only [IsingLeapfrogInteriorMargin, pE]
    dsimp [R]
    omega
  have hmarginS : IsingLeapfrogInteriorMargin R rho pS := by
    simp only [IsingLeapfrogInteriorMargin, pS]
    dsimp [R]
    omega
  have hmarginW : IsingLeapfrogInteriorMargin R rho pW := by
    simp only [IsingLeapfrogInteriorMargin, pW]
    dsimp [R]
    omega
  have hNSAdj : IsingLeapfrogDiagonalAdjacent pN pS := by
    constructor
    · change i.dist (i - 1) = 1
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.sub_le i 1)]
      omega
    · change (j - 1).dist j = 1
      rw [Nat.dist_eq_sub_of_le (Nat.sub_le j 1)]
      omega
  have hEWAdj : IsingLeapfrogDiagonalAdjacent pE pW := by
    constructor
    · change i.dist (i - 1) = 1
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.sub_le i 1)]
      omega
    · change j.dist (j - 1) = 1
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (Nat.sub_le j 1)]
      omega
  have hNS :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_physicalNormalized_norm_sub_le
      n 0 0 R rho mesh hn hfit hfit hmesh pN pS hrho
      hmarginN hmarginS hNSAdj
  have hEW :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow_physicalNormalized_norm_sub_le
      n 0 0 R rho mesh hn hfit hfit hmesh pE pW hrho
      hmarginE hmarginW hEWAdj
  have hedges :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le
      n i j hn hi0 hi1 hj0 hj1 (Real.sqrt (2 * mesh))
      (304 / ((rho : Real) * Real.sqrt (2 * mesh)))
      (by simpa [R, pN, pS,
        fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow] using hNS)
      (by simpa [R, pE, pW,
        fkIsingSquareBoundaryCenteredRadialPatchFullObservableWindow] using hEW)
  simpa only [show
      2 * (304 / ((rho : Real) * Real.sqrt (2 * mesh))) =
        608 / ((rho : Real) * Real.sqrt (2 * mesh)) by ring] using hedges



def finiteCenteredRadialGridMarginInterior
    (n rho : Nat) (mesh : Real) : Set Complex :=
  {z | (rho : Real) + 2 <
      (isingCenteredRadialGridCoordinate mesh n z).1 ∧
    (isingCenteredRadialGridCoordinate mesh n z).1 + rho + 5 < 2 * n ∧
    (rho : Real) + 2 <
      (isingCenteredRadialGridCoordinate mesh n z).2 ∧
    (isingCenteredRadialGridCoordinate mesh n z).2 + rho + 5 < 2 * n}



theorem closedBall_subset_finiteCenteredRadialGridMarginInterior
    (n rho : Nat) (mesh R : Real) (hmesh : 0 < mesh) (hR : 0 ≤ R)
    (hwide : 2 * R + ((rho : Real) + 6) * mesh ≤ mesh * n) :
    closedBall (0 : Complex) R ⊆
      finiteCenteredRadialGridMarginInterior n rho mesh := by
  intro z hz
  have hnorm : ‖z‖ ≤ R := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  have hrelo : -R ≤ z.re := by
    linarith [neg_le_of_abs_le (hre.trans hnorm)]
  have hrehi : z.re ≤ R := by
    linarith [le_of_abs_le (hre.trans hnorm)]
  have himlo : -R ≤ z.im := by
    linarith [neg_le_of_abs_le (him.trans hnorm)]
  have himhi : z.im ≤ R := by
    linarith [le_of_abs_le (him.trans hnorm)]
  have hq : 2 * R / mesh + (rho : Real) + 6 ≤ n := by
    calc
      2 * R / mesh + (rho : Real) + 6 =
          (2 * R + ((rho : Real) + 6) * mesh) / mesh := by
        field_simp [hmesh.ne']
        ring
      _ ≤ (mesh * (n : Real)) / mesh :=
        (div_le_div_iff_of_pos_right hmesh).mpr hwide
      _ = n := by field_simp [hmesh.ne']
  have hsumlo : -2 * R / mesh ≤ (z.re + z.im) / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hsumhi : (z.re + z.im) / mesh ≤ 2 * R / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hdifflo : -2 * R / mesh ≤ (z.re - z.im) / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hdiffhi : (z.re - z.im) / mesh ≤ 2 * R / mesh := by
    apply (div_le_div_iff_of_pos_right hmesh).mpr
    linarith
  have hc1 : (isingCenteredRadialGridCoordinate mesh n z).1 =
      (n : Real) + (z.re + z.im) / mesh - 1 / 2 := by
    unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, add_zero]
    field_simp [hmesh.ne']
    ring
  have hc2 : (isingCenteredRadialGridCoordinate mesh n z).2 =
      (n : Real) + (z.re - z.im) / mesh - 1 / 2 := by
    unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, add_zero]
    field_simp [hmesh.ne']
    ring
  change (rho : Real) + 2 <
      (isingCenteredRadialGridCoordinate mesh n z).1 ∧
    (isingCenteredRadialGridCoordinate mesh n z).1 + rho + 5 < 2 * n ∧
    (rho : Real) + 2 <
      (isingCenteredRadialGridCoordinate mesh n z).2 ∧
    (isingCenteredRadialGridCoordinate mesh n z).2 + rho + 5 < 2 * n
  rw [hc1, hc2]
  ring_nf at hq hsumlo hsumhi hdifflo hdiffhi ⊢
  constructor
  · linarith
  constructor
  · push_cast
    linarith
  constructor
  · linarith
  · push_cast
    linarith



theorem
    finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_fullCarrierTV
    (n rho : Nat) (gridScale normalizationScale : Real)
    (hn : 0 < n)
    (hgridScale : 0 < gridScale) (hnormalizationScale : 0 < normalizationScale)
    (hrho : 0 < rho) (s : Set Complex) (hs : Convex Real s) (L : NNReal)
    (hinside : s ⊆
      finiteCenteredRadialGridMarginInterior n rho gridScale)
    (hTV : 608 / ((rho : Real) * Real.sqrt (2 * normalizationScale)) ≤
      gridScale * (L : Real)) :
    LipschitzOnWith (4 * L)
      (finiteCenteredRadialGridInterpolant n gridScale (fun i j ↦
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j /
          (Real.sqrt (2 * normalizationScale) : Complex))) s := by
  let value : Fin (2 * n) → Fin (2 * n) → Complex := fun i j ↦
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j /
      (Real.sqrt (2 * normalizationScale) : Complex)
  change LipschitzOnWith (4 * L)
    (finiteCenteredRadialGridInterpolant n gridScale value) s
  apply lipschitzOnWith_of_open_local_on_convex _ _ _ hs
  intro z hz
  have hzmargin := hinside hz
  change (rho : Real) + 2 <
      (isingCenteredRadialGridCoordinate gridScale n z).1 ∧
    (isingCenteredRadialGridCoordinate gridScale n z).1 + rho + 5 < 2 * n ∧
    (rho : Real) + 2 <
      (isingCenteredRadialGridCoordinate gridScale n z).2 ∧
    (isingCenteredRadialGridCoordinate gridScale n z).2 + rho + 5 < 2 * n
    at hzmargin
  have hzdeep : z ∈ finiteCenteredRadialGridDeeperInterior n gridScale := by
    unfold finiteCenteredRadialGridDeeperInterior
    have hrhoReal : (1 : Real) ≤ rho := by exact_mod_cast hrho
    constructor
    · linarith
    constructor
    · push_cast
      linarith
    constructor
    · linarith
    · push_cast
      linarith
  obtain ⟨i, hi, hi0, hi2⟩ :=
    exists_twoByTwo_cell_of_centeredCoordinate n
      (isingCenteredRadialGridCoordinate gridScale n z).1 hzdeep.1 (by
        linarith [hzdeep.2.1])
  obtain ⟨j, hj, hj0, hj2⟩ :=
    exists_twoByTwo_cell_of_centeredCoordinate n
      (isingCenteredRadialGridCoordinate gridScale n z).2
        hzdeep.2.2.1 (by linarith [hzdeep.2.2.2])
  have hi3 : i + 3 < 2 * n := by
    have hcast : (i : Real) + 3 < (2 * n : Nat) := by
      linarith [hi0, hzdeep.2.1]
    exact_mod_cast hcast
  have hj3 : j + 3 < 2 * n := by
    have hcast : (j : Real) + 3 < (2 * n : Nat) := by
      linarith [hj0, hzdeep.2.2.2]
    exact_mod_cast hcast
  have hiLeft : rho ≤ i - 1 := by
    have hcast : (rho : Real) < i := by linarith [hzmargin.1, hi2]
    have hnat : rho < i := by exact_mod_cast hcast
    omega
  have hjBottom : rho ≤ j - 1 := by
    have hcast : (rho : Real) < j := by linarith [hzmargin.2.2.1, hj2]
    have hnat : rho < j := by exact_mod_cast hcast
    omega
  have hiRight : i + rho + 5 < 2 * n := by
    have hcast : (i : Real) + rho + 5 < 2 * n := by
      linarith [hi0, hzmargin.2.1]
    exact_mod_cast hcast
  have hjTop : j + rho + 5 < 2 * n := by
    have hcast : (j : Real) + rho + 5 < 2 * n := by
      linarith [hj0, hzmargin.2.2.2]
    exact_mod_cast hcast
  have hI (a b : Nat) (hia0 : i ≤ a) (hia1 : a ≤ i + 1)
      (hjb0 : j ≤ b) (hjb2 : b ≤ j + 2) :
      ‖value ⟨a + 1, by omega⟩ ⟨b, by omega⟩ -
        value ⟨a, by omega⟩ ⟨b, by omega⟩‖ ≤
          gridScale * (L : Real) := by
    have hedges :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le_of_margin
        n (a + 1) b rho normalizationScale hn (by omega) (by omega)
        (by omega) (by omega) hrho hnormalizationScale
        (by omega) (by omega) (by omega) (by omega)
    exact (hedges.2.1.trans hTV)
  have hJ (a b : Nat) (hia0 : i ≤ a) (hia2 : a ≤ i + 2)
      (hjb0 : j ≤ b) (hjb1 : b ≤ j + 1) :
      ‖value ⟨a, by omega⟩ ⟨b + 1, by omega⟩ -
        value ⟨a, by omega⟩ ⟨b, by omega⟩‖ ≤
          gridScale * (L : Real) := by
    have hedges :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cell_edges_le_of_margin
        n a (b + 1) rho normalizationScale hn (by omega) (by omega)
        (by omega) (by omega) hrho hnormalizationScale
        (by omega) (by omega) (by omega) (by omega)
    rw [norm_sub_rev]
    exact hedges.1.trans hTV
  let U : Set Complex := {w |
    (i : Real) < (isingCenteredRadialGridCoordinate gridScale n w).1 ∧
    (isingCenteredRadialGridCoordinate gridScale n w).1 < (i : Real) + 2 ∧
    (j : Real) < (isingCenteredRadialGridCoordinate gridScale n w).2 ∧
    (isingCenteredRadialGridCoordinate gridScale n w).2 < (j : Real) + 2}
  refine ⟨U, ?_, ?_, ?_⟩
  · have hc1 : Continuous (fun w : Complex ↦
        (isingCenteredRadialGridCoordinate gridScale n w).1) := by
      unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
      fun_prop
    have hc2 : Continuous (fun w : Complex ↦
        (isingCenteredRadialGridCoordinate gridScale n w).2) := by
      unfold isingCenteredRadialGridCoordinate isingRadialGridCoordinate
      fun_prop
    exact (isOpen_lt continuous_const hc1).inter
      ((isOpen_lt hc1 continuous_const).inter
        ((isOpen_lt continuous_const hc2).inter
          (isOpen_lt hc2 continuous_const)))
  · exact ⟨hi0, hi2, hj0, hj2⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro p hp q hq
    let xp : Real := (isingCenteredRadialGridCoordinate gridScale n p).1 - i
    let xq : Real := (isingCenteredRadialGridCoordinate gridScale n q).1 - i
    let yp : Real := (isingCenteredRadialGridCoordinate gridScale n p).2 - j
    let yq : Real := (isingCenteredRadialGridCoordinate gridScale n q).2 - j
    have hxp0 : 0 ≤ xp := by dsimp only [xp]; linarith [hp.1.1]
    have hxp2 : xp ≤ 2 := by dsimp only [xp]; linarith [hp.1.2.1]
    have hxq0 : 0 ≤ xq := by dsimp only [xq]; linarith [hq.1.1]
    have hxq2 : xq ≤ 2 := by dsimp only [xq]; linarith [hq.1.2.1]
    have hyp0 : 0 ≤ yp := by dsimp only [yp]; linarith [hp.1.2.2.1]
    have hyp2 : yp ≤ 2 := by dsimp only [yp]; linarith [hp.1.2.2.2]
    have hyq0 : 0 ≤ yq := by dsimp only [yq]; linarith [hq.1.2.2.1]
    have hyq2 : yq ≤ 2 := by dsimp only [yq]; linarith [hq.1.2.2.2]
    have H := finiteCenteredRadialGridInterpolant_twoByTwo_norm_sub_le_dist
      n gridScale hgridScale value i j hi hj xp xq yp yq (L : Real)
      hxp0 hxp2 hxq0 hxq2 hyp0 hyp2 hyq0 hyq2 L.2
      (hI i j (by omega) (by omega) (by omega) (by omega))
      (hI (i + 1) j (by omega) (by omega) (by omega) (by omega))
      (hI i (j + 1) (by omega) (by omega) (by omega) (by omega))
      (hI (i + 1) (j + 1) (by omega) (by omega) (by omega) (by omega))
      (hI i (j + 2) (by omega) (by omega) (by omega) (by omega))
      (hI (i + 1) (j + 2) (by omega) (by omega) (by omega) (by omega))
      (hJ i j (by omega) (by omega) (by omega) (by omega))
      (hJ i (j + 1) (by omega) (by omega) (by omega) (by omega))
      (hJ (i + 1) j (by omega) (by omega) (by omega) (by omega))
      (hJ (i + 1) (j + 1) (by omega) (by omega) (by omega) (by omega))
      (hJ (i + 2) j (by omega) (by omega) (by omega) (by omega))
      (hJ (i + 2) (j + 1) (by omega) (by omega) (by omega) (by omega))
    have hpPoint :
        isingCenteredRadialGridCellPoint gridScale n i j xp yp = p :=
      isingCenteredRadialGridCellPoint_coordinate
        gridScale hgridScale.ne' n i j p
    have hqPoint :
        isingCenteredRadialGridCellPoint gridScale n i j xq yq = q :=
      isingCenteredRadialGridCellPoint_coordinate
        gridScale hgridScale.ne' n i j q
    rw [hpPoint, hqPoint] at H
    simpa [dist_eq_norm] using H





theorem fkIsingExpandingSquare_fullCarrierTVCoefficient_le
    (k : Nat) (hk : 2 ≤ k) :
    let rho := (k / 2) * (k + 1)
    608 / ((rho : Real) *
        Real.sqrt (2 * fkIsingExpandingSquareMesh k)) ≤
      fkIsingExpandingSquareScale k * 2432 := by
  dsimp only
  let rho := (k / 2) * (k + 1)
  have hrho : 0 < rho := by
    dsimp [rho]
    exact Nat.mul_pos (Nat.div_pos (by omega) (by norm_num)) (by omega)
  have hscale : 0 < fkIsingExpandingSquareScale k :=
    fkIsingExpandingSquareScale_pos k
  have hmesh : 0 < fkIsingExpandingSquareMesh k :=
    fkIsingExpandingSquareMesh_pos k
  have hscaleLe : fkIsingExpandingSquareScale k ≤ 1 := by
    rw [fkIsingExpandingSquareScale, one_div]
    apply inv_le_one_of_one_le₀
    norm_num
  have hsquare :
      fkIsingExpandingSquareScale k ^ 2 ≤
        2 * fkIsingExpandingSquareMesh k := by
    rw [fkIsingExpandingSquareMesh]
    nlinarith [hscale.le]
  have hsqrt : fkIsingExpandingSquareScale k ≤
      Real.sqrt (2 * fkIsingExpandingSquareMesh k) := by
    exact (Real.le_sqrt hscale.le (by positivity)).2 hsquare
  have hsqrtPos : 0 < Real.sqrt (2 * fkIsingExpandingSquareMesh k) :=
    Real.sqrt_pos.2 (by positivity)
  have hden : 0 < (rho : Real) *
      Real.sqrt (2 * fkIsingExpandingSquareMesh k) := by positivity
  have hfloor : k + 1 ≤ 4 * (k / 2) := by omega
  have hscaleCancel :
      fkIsingExpandingSquareScale k * (k + 1 : Nat) = 1 := by
    simpa [fkIsingExpandingSquareScale, one_div] using
      inv_mul_cancel₀ (show (k : Real) + 1 ≠ 0 by positivity)
  have hscaleCancel' :
      (k + 1 : Nat) * fkIsingExpandingSquareScale k = 1 := by
    rw [mul_comm]
    exact hscaleCancel
  have hscaleCancel'' :
      ((k : Real) + 1) * fkIsingExpandingSquareScale k = 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hscaleCancel'
  have hrhoCancel :
      (rho : Real) * fkIsingExpandingSquareScale k = (k / 2 : Nat) := by
    dsimp [rho]
    push_cast
    rw [mul_assoc, hscaleCancel'']
    ring
  apply (div_le_iff₀ hden).2
  calc
    (608 : Real) = 608 *
        (fkIsingExpandingSquareScale k * (k + 1 : Nat)) := by
          rw [hscaleCancel]
          ring
    _ ≤ 608 *
        (fkIsingExpandingSquareScale k * (4 * (k / 2 : Nat))) := by
          gcongr
          exact_mod_cast hfloor
    _ = fkIsingExpandingSquareScale k * 2432 *
        ((rho : Real) * fkIsingExpandingSquareScale k) := by
          rw [hrhoCancel]
          push_cast
          ring
    _ ≤ fkIsingExpandingSquareScale k * 2432 *
        ((rho : Real) *
          Real.sqrt (2 * fkIsingExpandingSquareMesh k)) := by
          gcongr



theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_fullCarrierTV
    (k : Nat) (R : Real) (hR : 0 ≤ R) (hk : 2 ≤ k)
    (hwide : 2 * R +
        ((((k / 2) * (k + 1) : Nat) : Real) + 6) *
          fkIsingExpandingSquareScale k ≤
      fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k) :
    LipschitzOnWith (4 * (2432 : NNReal))
      (fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k)
      (closedBall (0 : Complex) R) := by
  let n := fkIsingExpandingSquareSide k
  let rho := (k / 2) * (k + 1)
  have hn : 0 < n := fkIsingExpandingSquareSide_pos k
  have hrho : 0 < rho := by
    dsimp [rho]
    exact Nat.mul_pos (Nat.div_pos (by omega) (by norm_num)) (by omega)
  have hinside := closedBall_subset_finiteCenteredRadialGridMarginInterior
    n rho (fkIsingExpandingSquareScale k) R
    (fkIsingExpandingSquareScale_pos k) hR (by
      simpa [n, rho] using hwide)
  have hf := finiteCenteredRadialGridInterpolant_lipschitzOnWith_of_fullCarrierTV
    n rho (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareMesh k)
    hn (fkIsingExpandingSquareScale_pos k)
    (fkIsingExpandingSquareMesh_pos k) hrho (closedBall 0 R)
    (convex_closedBall 0 R) (2432 : NNReal) hinside
    (by simpa [rho] using fkIsingExpandingSquare_fullCarrierTVCoefficient_le k hk)
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  have hzs : star z ∈ closedBall (0 : Complex) R := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hws : star w ∈ closedBall (0 : Complex) R := by
    simpa [mem_closedBall, dist_zero_right] using hw
  have h := hf.dist_le_mul (star z) hzs (star w) hws
  simpa [fkIsingExpandingBoundarySquareCenteredReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant,
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant, n,
    star_isometry.dist_eq] using h



theorem
    fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_meshUniformCompactHolder_fullCarrierTV :
    fkIsingExpandingBoundarySquareCaratheodoryApproximation.MeshUniformCompactHolder
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant := by
  constructor
  intro K hK _hKU
  obtain ⟨R, hKR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Complex)).mp hK.isBounded
  let R0 : Real := max R 0
  have hR0 : 0 ≤ R0 := le_max_right _ _
  have hKR0 : K ⊆ closedBall (0 : Complex) R0 :=
    hKR.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * R0 + 10)
  let M : Nat := max N 2
  obtain ⟨Cpre, hpre⟩ :=
    exists_lipschitzOnWith_forall_lt_of_locallyLipschitz
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant
      fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_locallyLipschitz
      K hK M
  refine ⟨max Cpre (4 * (2432 : NNReal)), 1, by norm_num, ?_⟩
  intro k
  apply LipschitzOnWith.holderOnWith
  by_cases hkM : k < M
  · exact (hpre k hkM).weaken (le_max_left _ _)
  · have hMk : M ≤ k := by omega
    have hk2 : 2 ≤ k := le_trans (le_max_right N 2) hMk
    have hNk : N ≤ k := le_trans (le_max_left N 2) hMk
    have hscale : 0 < fkIsingExpandingSquareScale k :=
      fkIsingExpandingSquareScale_pos k
    have hscaleLe : fkIsingExpandingSquareScale k ≤ 1 := by
      rw [fkIsingExpandingSquareScale, one_div]
      apply inv_le_one_of_one_le₀
      norm_num
    have hrhoCancel :
        ((((k / 2) * (k + 1) : Nat) : Real) *
          fkIsingExpandingSquareScale k) = (k / 2 : Nat) := by
      push_cast
      rw [fkIsingExpandingSquareScale, one_div, mul_assoc]
      norm_cast
      rw [mul_inv_cancel₀
        (show (((k + 1 : Nat) : Real)) ≠ 0 by positivity)]
      ring
    have hfloor : ((k / 2 : Nat) : Real) ≤ (k : Real) / 2 := by
      exact Nat.cast_div_le
    have hNreal : 4 * R0 + 10 < (k : Real) :=
      lt_of_lt_of_le hN (by exact_mod_cast hNk)
    have hwide : 2 * R0 +
        ((((k / 2) * (k + 1) : Nat) : Real) + 6) *
          fkIsingExpandingSquareScale k ≤
        fkIsingExpandingSquareScale k * fkIsingExpandingSquareSide k := by
      rw [fkIsingExpandingSquareScale_mul_side]
      rw [add_mul, hrhoCancel]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hscaleLe (by norm_num : (0 : Real) ≤ 6)]
    exact
      ((fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_lipschitzOnWith_closedBall_of_fullCarrierTV
          k R0 hR0 hk2 hwide).mono hKR0).weaken (le_max_right _ _)

end

end StatMech.Universality
