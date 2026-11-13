/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicProjectedFullMedialInterpolation









namespace StatMech.Universality

noncomputable section


theorem isingProj_div_real (e z : Complex) (r : Real) :
    isingProj e (z / (r : Complex)) = isingProj e z / (r : Complex) := by
  unfold isingProj
  simp
  ring



theorem projectionCycle_crossParity_norm_div_sub_div_le
    (north east south west : Complex) (r delta : Real)
    (hNE : isingProj 1 north = isingProj 1 east)
    (hES : isingProj Complex.I east = isingProj Complex.I south)
    (hSW : isingProj (-1) south = isingProj (-1) west)
    (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
    (hNS : ‖north / (r : Complex) - south / (r : Complex)‖ ≤ delta)
    (hEW : ‖east / (r : Complex) - west / (r : Complex)‖ ≤ delta) :
    ‖north / (r : Complex) - east / (r : Complex)‖ ≤ 2 * delta ∧
      ‖east / (r : Complex) - south / (r : Complex)‖ ≤ 2 * delta ∧
      ‖south / (r : Complex) - west / (r : Complex)‖ ≤ 2 * delta ∧
      ‖west / (r : Complex) - north / (r : Complex)‖ ≤ 2 * delta := by
  apply projectionCycle_crossParity_norm_sub_le
  · rw [isingProj_div_real, isingProj_div_real, hNE]
  · rw [isingProj_div_real, isingProj_div_real, hES]
  · rw [isingProj_div_real, isingProj_div_real, hSW]
  · rw [isingProj_div_real, isingProj_div_real, hWN]
  · exact hNS
  · exact hEW




theorem complexBilinearCell_norm_sub_le_of_cycle_edges
    (a00 a10 a01 a11 : Complex) (x x' y y' D : Real)
    (hx0' : 0 ≤ x') (hx1' : x' ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (h10_11 : ‖a10 - a11‖ ≤ D)
    (h11_01 : ‖a11 - a01‖ ≤ D)
    (h01_00 : ‖a01 - a00‖ ≤ D)
    (h00_10 : ‖a00 - a10‖ ≤ D) :
    ‖complexBilinearCell a00 a10 a01 a11 x y -
      complexBilinearCell a00 a10 a01 a11 x' y'‖ ≤
      D * (|x - x'| + |y - y'|) := by
  apply complexBilinearCell_norm_sub_le a00 a10 a01 a11 x x' y y' D
      hx0' hx1' hy0 hy1
  · simpa only [norm_sub_rev] using h00_10
  · exact h11_01
  · exact h01_00
  · simpa only [norm_sub_rev] using h10_11



theorem finiteRadialGridInterpolant_cellPoint_norm_sub_le_of_cycle_edges
    {m : Nat} (mesh : Real) (hmesh : mesh ≠ 0)
    (value : Fin m → Fin m → Complex)
    (i j : Nat) (hi : i + 1 < m) (hj : j + 1 < m)
    (x x' y y' D : Real)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hx0' : 0 ≤ x') (hx1' : x' ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hy0' : 0 ≤ y') (hy1' : y' ≤ 1)
    (h10_11 :
      ‖value ⟨i + 1, by omega⟩ ⟨j, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩‖ ≤ D)
    (h11_01 :
      ‖value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j + 1, by omega⟩‖ ≤ D)
    (h01_00 :
      ‖value ⟨i, by omega⟩ ⟨j + 1, by omega⟩ -
        value ⟨i, by omega⟩ ⟨j, by omega⟩‖ ≤ D)
    (h00_10 :
      ‖value ⟨i, by omega⟩ ⟨j, by omega⟩ -
        value ⟨i + 1, by omega⟩ ⟨j, by omega⟩‖ ≤ D) :
    ‖finiteRadialGridInterpolant m mesh value
          (isingRadialGridCellPoint mesh i j x y) -
        finiteRadialGridInterpolant m mesh value
          (isingRadialGridCellPoint mesh i j x' y')‖ ≤
      D * (|x - x'| + |y - y'|) := by
  rw [finiteRadialGridInterpolant_cellPoint mesh hmesh value i j hi hj
      x y hx0 hx1 hy0 hy1,
    finiteRadialGridInterpolant_cellPoint mesh hmesh value i j hi hj
      x' y' hx0' hx1' hy0' hy1']
  exact complexBilinearCell_norm_sub_le_of_cycle_edges
    _ _ _ _ x x' y y' D hx0' hx1' hy0 hy1
      h10_11 h11_01 h01_00 h00_10



theorem cellPoint_norm_sub_sq_le_of_coordinate_l1
    (F : Complex → Complex) (mesh : Real) (hmesh : 0 < mesh)
    (i j : Nat) (x x' y y' D : Real)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hx0' : 0 ≤ x') (hx1' : x' ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hy0' : 0 ≤ y') (hy1' : y' ≤ 1)
    (hD : 0 ≤ D)
    (hbound :
      ‖F (isingRadialGridCellPoint mesh i j x y) -
          F (isingRadialGridCellPoint mesh i j x' y')‖ ≤
        D * (|x - x'| + |y - y'|)) :
    ‖F (isingRadialGridCellPoint mesh i j x y) -
        F (isingRadialGridCellPoint mesh i j x' y')‖ ^ 2 ≤
      8 * (D ^ 2 / mesh) *
        dist (isingRadialGridCellPoint mesh i j x y)
          (isingRadialGridCellPoint mesh i j x' y') := by
  let t := |x - x'| + |y - y'|
  let d := dist (isingRadialGridCellPoint mesh i j x y)
    (isingRadialGridCellPoint mesh i j x' y')
  have ht0 : 0 ≤ t := by
    simp only [t]
    positivity
  have hxabs : |x - x'| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hyabs : |y - y'| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have ht2 : t ≤ 2 := by
    simp only [t]
    linarith
  have hgeom : mesh * t ≤ 4 * d := by
    simpa only [abs_of_pos hmesh, t, d] using
      abs_mesh_mul_cellCoordinate_l1_le_four_dist mesh i j x x' y y'
  have htSq : mesh * t ^ 2 ≤ 8 * d := by
    calc
      mesh * t ^ 2 ≤ mesh * (2 * t) := by
        gcongr
        nlinarith [sq_nonneg t]
      _ = 2 * (mesh * t) := by ring
      _ ≤ 2 * (4 * d) := by gcongr
      _ = 8 * d := by ring
  have hnormSq :
      ‖F (isingRadialGridCellPoint mesh i j x y) -
          F (isingRadialGridCellPoint mesh i j x' y')‖ ^ 2 ≤
        D ^ 2 * t ^ 2 := by
    have hnonneg : 0 ≤ D * t := mul_nonneg hD ht0
    change ‖F (isingRadialGridCellPoint mesh i j x y) -
        F (isingRadialGridCellPoint mesh i j x' y')‖ ≤ D * t at hbound
    nlinarith [norm_nonneg
      (F (isingRadialGridCellPoint mesh i j x y) -
        F (isingRadialGridCellPoint mesh i j x' y'))]
  have hright : 8 * (D ^ 2 / mesh) * d =
      (D ^ 2 * (8 * d)) / mesh := by
    field_simp [hmesh.ne']
  change ‖F (isingRadialGridCellPoint mesh i j x y) -
      F (isingRadialGridCellPoint mesh i j x' y')‖ ^ 2 ≤
    8 * (D ^ 2 / mesh) * d
  rw [hright]
  apply (le_div_iff₀ hmesh).2
  calc
    ‖F (isingRadialGridCellPoint mesh i j x y) -
          F (isingRadialGridCellPoint mesh i j x' y')‖ ^ 2 * mesh ≤
        (D ^ 2 * t ^ 2) * mesh := by gcongr
    _ = D ^ 2 * (mesh * t ^ 2) := by ring
    _ ≤ D ^ 2 * (8 * d) :=
      mul_le_mul_of_nonneg_left htSq (sq_nonneg D)



theorem halfScale_cellHolderCoefficient_eq (m : Nat) (hm : 0 < m) :
    8 * ((2 * ((1 / (m : Real)) * Real.sqrt
      (264212480 * (m : Real)))) ^ 2 / (1 / (m : Real))) =
      (8454799360 : Real) := by
  have hm0 : (m : Real) ≠ 0 := by exact_mod_cast hm.ne'
  have hnonneg : 0 ≤ (m : Real) * (264212480 : Real) := by positivity
  have hsqrt : Real.sqrt ((m : Real) * (264212480 : Real)) ^ 2 =
      (m : Real) * (264212480 : Real) := Real.sq_sqrt hnonneg
  field_simp [hm0]
  rw [hsqrt]
  ring



theorem fkIsingSquareBoundaryRadialPatchFullObservable_even_cell_edges_le
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j))
    (r delta : Real)
    (hNS : ‖fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex) -
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j, by omega⟩ / (r : Complex)‖ ≤ delta)
    (hEW : ‖fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j, by omega⟩ / (r : Complex) -
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex)‖ ≤ delta) :
    let north := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i, by omega⟩ ⟨j - 1, by omega⟩
    let east := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i, by omega⟩ ⟨j, by omega⟩
    let south := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i - 1, by omega⟩ ⟨j, by omega⟩
    let west := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
    ‖north / (r : Complex) - east / (r : Complex)‖ ≤ 2 * delta ∧
      ‖east / (r : Complex) - south / (r : Complex)‖ ≤ 2 * delta ∧
      ‖south / (r : Complex) - west / (r : Complex)‖ ≤ 2 * delta ∧
      ‖west / (r : Complex) - north / (r : Complex)‖ ≤ 2 * delta := by
  dsimp only
  have hcycle :=
    fkIsingSquareBoundaryRadialPatchFullObservable_even_projectionCycle
      n m i j hn hm hi0 hi1 hj0 hj1 heven
  dsimp only at hcycle
  exact projectionCycle_crossParity_norm_div_sub_div_le _ _ _ _ r delta
    hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hNS hEW



theorem fkIsingSquareBoundaryRadialPatchFullObservable_odd_cell_edges_le
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (hodd : ¬ Even (i + j))
    (r delta : Real)
    (hSN : ‖fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j, by omega⟩ / (r : Complex) -
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex)‖ ≤ delta)
    (hWE : ‖fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex) -
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j, by omega⟩ / (r : Complex)‖ ≤ delta) :
    let north := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i, by omega⟩ ⟨j - 1, by omega⟩
    let east := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i, by omega⟩ ⟨j, by omega⟩
    let south := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i - 1, by omega⟩ ⟨j, by omega⟩
    let west := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
    ‖south / (r : Complex) - west / (r : Complex)‖ ≤ 2 * delta ∧
      ‖west / (r : Complex) - north / (r : Complex)‖ ≤ 2 * delta ∧
      ‖north / (r : Complex) - east / (r : Complex)‖ ≤ 2 * delta ∧
      ‖east / (r : Complex) - south / (r : Complex)‖ ≤ 2 * delta := by
  dsimp only
  have hcycle :=
    fkIsingSquareBoundaryRadialPatchFullObservable_odd_projectionCycle
      n m i j hn hm hi0 hi1 hj0 hj1 hodd
  dsimp only at hcycle
  exact projectionCycle_crossParity_norm_div_sub_div_le _ _ _ _ r delta
    hcycle.1 hcycle.2.1 hcycle.2.2.1 hcycle.2.2.2 hSN hWE



theorem fkIsingSquareBoundaryRadialPatchFullObservable_cell_edges_le
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (r delta : Real)
    (hNS : ‖fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex) -
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j, by omega⟩ / (r : Complex)‖ ≤ delta)
    (hEW : ‖fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j, by omega⟩ / (r : Complex) -
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex)‖ ≤ delta) :
    let north := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i, by omega⟩ ⟨j - 1, by omega⟩
    let east := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i, by omega⟩ ⟨j, by omega⟩
    let south := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i - 1, by omega⟩ ⟨j, by omega⟩
    let west := fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
      ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
    ‖north / (r : Complex) - east / (r : Complex)‖ ≤ 2 * delta ∧
      ‖east / (r : Complex) - south / (r : Complex)‖ ≤ 2 * delta ∧
      ‖south / (r : Complex) - west / (r : Complex)‖ ≤ 2 * delta ∧
      ‖west / (r : Complex) - north / (r : Complex)‖ ≤ 2 * delta := by
  by_cases heven : Even (i + j)
  · exact fkIsingSquareBoundaryRadialPatchFullObservable_even_cell_edges_le
      n m i j hn hm hi0 hi1 hj0 hj1 heven r delta hNS hEW
  · have hSN :
        ‖fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
            ⟨i - 1, by omega⟩ ⟨j, by omega⟩ / (r : Complex) -
          fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
            ⟨i, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex)‖ ≤ delta := by
      rw [norm_sub_rev]
      exact hNS
    have hWE :
        ‖fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
            ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ / (r : Complex) -
          fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
            ⟨i, by omega⟩ ⟨j, by omega⟩ / (r : Complex)‖ ≤ delta := by
      rw [norm_sub_rev]
      exact hEW
    have hodd :=
      fkIsingSquareBoundaryRadialPatchFullObservable_odd_cell_edges_le
        n m i j hn hm hi0 hi1 hj0 hj1 heven r delta hSN hWE
    exact ⟨hodd.2.2.1, hodd.2.2.2, hodd.1, hodd.2.1⟩



theorem
    fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_cell_edges_halfScale
    (n m baseI baseJ R rho cutoff : Nat)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) (hcutoff : 0 < cutoff)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 cutoff)
    (hmcutoff : m ≤ 2 * cutoff) (hmrho : m ≤ 2 * rho)
    (a b : Nat) (ha0 : 0 < a) (haR : a < R)
    (hb0 : 0 < b) (hbR : b < R)
    (hrho : 0 < rho)
    (hmarginN : IsingLeapfrogInteriorMargin R rho
      (⟨a, by omega⟩, ⟨b - 1, by omega⟩))
    (hmarginE : IsingLeapfrogInteriorMargin R rho
      (⟨a, by omega⟩, ⟨b, by omega⟩))
    (hmarginS : IsingLeapfrogInteriorMargin R rho
      (⟨a - 1, by omega⟩, ⟨b, by omega⟩))
    (hmarginW : IsingLeapfrogInteriorMargin R rho
      (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩)) :
    let F := fkIsingSquareBoundaryRadialPatchFullObservableWindow
      n m baseI baseJ R hn hm hfitI hfitJ
    let normalization := Real.sqrt (2 * (1 / (m : Real)))
    let delta := (1 / (m : Real)) * Real.sqrt (264212480 * (m : Real))
    ‖F (⟨a, by omega⟩, ⟨b - 1, by omega⟩) / normalization -
        F (⟨a, by omega⟩, ⟨b, by omega⟩) / normalization‖ ≤ 2 * delta ∧
      ‖F (⟨a, by omega⟩, ⟨b, by omega⟩) / normalization -
        F (⟨a - 1, by omega⟩, ⟨b, by omega⟩) / normalization‖ ≤ 2 * delta ∧
      ‖F (⟨a - 1, by omega⟩, ⟨b, by omega⟩) / normalization -
        F (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩) / normalization‖ ≤ 2 * delta ∧
      ‖F (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩) / normalization -
        F (⟨a, by omega⟩, ⟨b - 1, by omega⟩) / normalization‖ ≤ 2 * delta := by
  let pN : IsingLeapfrogBox R :=
    (⟨a, by omega⟩, ⟨b - 1, by omega⟩)
  let pE : IsingLeapfrogBox R :=
    (⟨a, by omega⟩, ⟨b, by omega⟩)
  let pS : IsingLeapfrogBox R :=
    (⟨a - 1, by omega⟩, ⟨b, by omega⟩)
  let pW : IsingLeapfrogBox R :=
    (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩)
  let normalization : Real := Real.sqrt (2 * (1 / (m : Real)))
  let delta : Real :=
    (1 / (m : Real)) * Real.sqrt (264212480 * (m : Real))
  have hNS :
      ‖fkIsingSquareBoundaryRadialPatchFullObservableWindow
            n m baseI baseJ R hn hm hfitI hfitJ pN /
            (normalization : Complex) -
        fkIsingSquareBoundaryRadialPatchFullObservableWindow
            n m baseI baseJ R hn hm hfitI hfitJ pS /
            (normalization : Complex)‖ ≤ delta := by
    simpa only [normalization, delta] using
      fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_halfScale
        n m baseI baseJ R rho cutoff hn hm hm2 hcutoff hfitI hfitJ
        hdeep hmcutoff hmrho pN pS hrho (by simpa [pN] using hmarginN)
        (by simpa [pS] using hmarginS) (by
          unfold IsingLeapfrogDiagonalAdjacent
          simp [pN, pS, Nat.dist]
          omega)
  have hEW :
      ‖fkIsingSquareBoundaryRadialPatchFullObservableWindow
            n m baseI baseJ R hn hm hfitI hfitJ pE /
            (normalization : Complex) -
        fkIsingSquareBoundaryRadialPatchFullObservableWindow
            n m baseI baseJ R hn hm hfitI hfitJ pW /
            (normalization : Complex)‖ ≤ delta := by
    simpa only [normalization, delta] using
      fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_neighbor_halfScale
        n m baseI baseJ R rho cutoff hn hm hm2 hcutoff hfitI hfitJ
        hdeep hmcutoff hmrho pE pW hrho (by simpa [pE] using hmarginE)
        (by simpa [pW] using hmarginW) (by
          unfold IsingLeapfrogDiagonalAdjacent
          simp [pE, pW, Nat.dist]
          omega)
  have hbaseIa : baseI + (a - 1) = baseI + a - 1 := by omega
  have hbaseJb : baseJ + (b - 1) = baseJ + b - 1 := by omega
  have hNS' :
      ‖fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
            ⟨baseI + a, by omega⟩ ⟨baseJ + b - 1, by omega⟩ /
            (normalization : Complex) -
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
            ⟨baseI + a - 1, by omega⟩ ⟨baseJ + b, by omega⟩ /
            (normalization : Complex)‖ ≤ delta := by
    simpa [fkIsingSquareBoundaryRadialPatchFullObservableWindow, pN, pS,
      hbaseIa, hbaseJb] using hNS
  have hEW' :
      ‖fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
            ⟨baseI + a, by omega⟩ ⟨baseJ + b, by omega⟩ /
            (normalization : Complex) -
        fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
            ⟨baseI + a - 1, by omega⟩ ⟨baseJ + b - 1, by omega⟩ /
            (normalization : Complex)‖ ≤ delta := by
    simpa [fkIsingSquareBoundaryRadialPatchFullObservableWindow, pE, pW,
      hbaseIa, hbaseJb] using hEW
  have hedges :=
    fkIsingSquareBoundaryRadialPatchFullObservable_cell_edges_le
      n m (baseI + a) (baseJ + b) hn hm (by omega) (by omega)
      (by omega) (by omega) normalization delta hNS' hEW'
  simpa [pN, pE, pS, pW, normalization, delta,
    fkIsingSquareBoundaryRadialPatchFullObservableWindow,
    hbaseIa, hbaseJb] using hedges



theorem
    fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_tensorTent_cell_norm_sub_le
    (n m baseI baseJ R rho cutoff : Nat)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) (hcutoff : 0 < cutoff)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 cutoff)
    (hmcutoff : m ≤ 2 * cutoff) (hmrho : m ≤ 2 * rho)
    (a b : Nat) (ha0 : 0 < a) (haR : a < R)
    (hb0 : 0 < b) (hbR : b < R)
    (hrho : 0 < rho)
    (hmarginN : IsingLeapfrogInteriorMargin R rho
      (⟨a, by omega⟩, ⟨b - 1, by omega⟩))
    (hmarginE : IsingLeapfrogInteriorMargin R rho
      (⟨a, by omega⟩, ⟨b, by omega⟩))
    (hmarginS : IsingLeapfrogInteriorMargin R rho
      (⟨a - 1, by omega⟩, ⟨b, by omega⟩))
    (hmarginW : IsingLeapfrogInteriorMargin R rho
      (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩))
    (gridScale : Real) (hgridScale : gridScale ≠ 0)
    (x x' y y' : Real)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hx0' : 0 ≤ x') (hx1' : x' ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hy0' : 0 ≤ y') (hy1' : y' ≤ 1) :
    let I := fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant
      n m hn hm gridScale (1 / (m : Real))
    let i := baseI + a - 1
    let j := baseJ + b - 1
    let delta := (1 / (m : Real)) * Real.sqrt (264212480 * (m : Real))
    ‖I (isingRadialGridCellPoint gridScale i j x y) -
        I (isingRadialGridCellPoint gridScale i j x' y')‖ ≤
      (2 * delta) * (|x - x'| + |y - y'|) := by
  let pN : IsingLeapfrogBox R :=
    (⟨a, by omega⟩, ⟨b - 1, by omega⟩)
  let pE : IsingLeapfrogBox R :=
    (⟨a, by omega⟩, ⟨b, by omega⟩)
  let pS : IsingLeapfrogBox R :=
    (⟨a - 1, by omega⟩, ⟨b, by omega⟩)
  let pW : IsingLeapfrogBox R :=
    (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩)
  let F := fkIsingSquareBoundaryRadialPatchFullObservableWindow
    n m baseI baseJ R hn hm hfitI hfitJ
  let normalization : Real := Real.sqrt (2 * (1 / (m : Real)))
  let delta : Real :=
    (1 / (m : Real)) * Real.sqrt (264212480 * (m : Real))
  have hedges :
      ‖F pN / (normalization : Complex) -
          F pE / (normalization : Complex)‖ ≤ 2 * delta ∧
        ‖F pE / (normalization : Complex) -
          F pS / (normalization : Complex)‖ ≤ 2 * delta ∧
        ‖F pS / (normalization : Complex) -
          F pW / (normalization : Complex)‖ ≤ 2 * delta ∧
        ‖F pW / (normalization : Complex) -
          F pN / (normalization : Complex)‖ ≤ 2 * delta := by
    simpa [F, pN, pE, pS, pW, normalization, delta] using
      fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_cell_edges_halfScale
        n m baseI baseJ R rho cutoff hn hm hm2 hcutoff hfitI hfitJ
        hdeep hmcutoff hmrho a b ha0 haR hb0 hbR hrho
        hmarginN hmarginE hmarginS hmarginW
  let i := baseI + a - 1
  let j := baseJ + b - 1
  have hi : i + 1 < m := by simp only [i]; omega
  have hj : j + 1 < m := by simp only [j]; omega
  have hiBase : baseI + (a - 1) = i := by simp only [i]; omega
  have hjBase : baseJ + (b - 1) = j := by simp only [j]; omega
  have hiSucc : i + 1 = baseI + a := by simp only [i]; omega
  have hjSucc : j + 1 = baseJ + b := by simp only [j]; omega
  dsimp only
  unfold fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant
  apply finiteRadialGridInterpolant_cellPoint_norm_sub_le_of_cycle_edges
      gridScale hgridScale _ i j hi hj x x' y y' (2 * delta)
      hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1'
  · simpa [F, pN, pE, hiSucc, hjBase, hjSucc,
      fkIsingSquareBoundaryRadialPatchFullObservableWindow, normalization] using
      hedges.1
  · simpa [F, pE, pS, hiBase, hiSucc, hjSucc,
      fkIsingSquareBoundaryRadialPatchFullObservableWindow, normalization] using
      hedges.2.1
  · simpa [F, pS, pW, hiBase, hjBase, hjSucc,
      fkIsingSquareBoundaryRadialPatchFullObservableWindow, normalization] using
      hedges.2.2.1
  · simpa [F, pW, pN, hiBase, hiSucc, hjBase,
      fkIsingSquareBoundaryRadialPatchFullObservableWindow, normalization] using
      hedges.2.2.2



theorem
    fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_tensorTent_cell_holderHalf_sq
    (n m baseI baseJ R rho cutoff : Nat)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) (hcutoff : 0 < cutoff)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 cutoff)
    (hmcutoff : m ≤ 2 * cutoff) (hmrho : m ≤ 2 * rho)
    (a b : Nat) (ha0 : 0 < a) (haR : a < R)
    (hb0 : 0 < b) (hbR : b < R)
    (hrho : 0 < rho)
    (hmarginN : IsingLeapfrogInteriorMargin R rho
      (⟨a, by omega⟩, ⟨b - 1, by omega⟩))
    (hmarginE : IsingLeapfrogInteriorMargin R rho
      (⟨a, by omega⟩, ⟨b, by omega⟩))
    (hmarginS : IsingLeapfrogInteriorMargin R rho
      (⟨a - 1, by omega⟩, ⟨b, by omega⟩))
    (hmarginW : IsingLeapfrogInteriorMargin R rho
      (⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩))
    (x x' y y' : Real)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hx0' : 0 ≤ x') (hx1' : x' ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hy0' : 0 ≤ y') (hy1' : y' ≤ 1) :
    let mesh := 1 / (m : Real)
    let I := fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant
      n m hn hm mesh mesh
    let i := baseI + a - 1
    let j := baseJ + b - 1
    ‖I (isingRadialGridCellPoint mesh i j x y) -
        I (isingRadialGridCellPoint mesh i j x' y')‖ ^ 2 ≤
      8454799360 *
        dist (isingRadialGridCellPoint mesh i j x y)
          (isingRadialGridCellPoint mesh i j x' y') := by
  have hmpos : 0 < m := by omega
  let mesh : Real := 1 / (m : Real)
  let I := fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant
    n m hn hm mesh mesh
  let i := baseI + a - 1
  let j := baseJ + b - 1
  let D : Real :=
    2 * ((1 / (m : Real)) * Real.sqrt (264212480 * (m : Real)))
  have hmesh : 0 < mesh := by
    simp only [mesh]
    positivity
  have hD : 0 ≤ D := by
    simp only [D]
    positivity
  have hlocal :
      ‖I (isingRadialGridCellPoint mesh i j x y) -
          I (isingRadialGridCellPoint mesh i j x' y')‖ ≤
        D * (|x - x'| + |y - y'|) := by
    simpa [I, i, j, mesh, D] using
      fkIsingSquareBoundaryRadialPatchPhysicalNormalizedWindow_tensorTent_cell_norm_sub_le
        n m baseI baseJ R rho cutoff hn hm hm2 hcutoff hfitI hfitJ
        hdeep hmcutoff hmrho a b ha0 haR hb0 hbR hrho
        hmarginN hmarginE hmarginS hmarginW
        (1 / (m : Real)) (by positivity) x x' y y'
        hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1'
  have hsq := cellPoint_norm_sub_sq_le_of_coordinate_l1
    I mesh hmesh i j x x' y y' D
    hx0 hx1 hx0' hx1' hy0 hy1 hy0' hy1' hD hlocal
  have hcoefficient : 8 * (D ^ 2 / mesh) = (8454799360 : Real) := by
    simpa [D, mesh] using halfScale_cellHolderCoefficient_eq m hmpos
  simpa only [hcoefficient] using hsq

end

end StatMech.Universality
