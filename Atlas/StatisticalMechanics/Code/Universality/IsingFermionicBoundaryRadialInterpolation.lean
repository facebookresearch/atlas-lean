/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy









namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section


def isingLinearTent (x : Real) : Real := max 0 (1 - |x|)

theorem isingLinearTent_continuous : Continuous isingLinearTent := by
  unfold isingLinearTent
  fun_prop

@[simp] theorem isingLinearTent_zero : isingLinearTent 0 = 1 := by
  simp [isingLinearTent]

theorem isingLinearTent_natCast_sub_eq_zero
    (i j : Nat) (hij : i ≠ j) :
    isingLinearTent ((i : Real) - (j : Real)) = 0 := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hle : (i : Real) - (j : Real) ≤ -1 := by exact_mod_cast (show (i : Int) - j ≤ -1 by omega)
    have habs : 1 ≤ |(i : Real) - (j : Real)| := by
      rw [abs_of_nonpos (hle.trans (by norm_num))]
      linarith
    unfold isingLinearTent
    rw [max_eq_left (sub_nonpos.mpr habs)]
  · have hle : (j : Real) - (i : Real) ≤ -1 := by
      exact_mod_cast (show (j : Int) - i ≤ -1 by omega)
    have hpos : 1 ≤ (i : Real) - (j : Real) := by linarith
    have habs : 1 ≤ |(i : Real) - (j : Real)| := by
      rw [abs_of_nonneg (by linarith)]
      exact hpos
    unfold isingLinearTent
    rw [max_eq_left (sub_nonpos.mpr habs)]

theorem isingLinearTent_eq_one_sub_of_mem_unit
    (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    isingLinearTent x = 1 - x := by
  simp [isingLinearTent, abs_of_nonneg hx0, hx1]

theorem isingLinearTent_sub_one_eq_of_mem_unit
    (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    isingLinearTent (x - 1) = x := by
  simp [isingLinearTent, abs_of_nonpos (sub_nonpos.mpr hx1), hx0]



theorem isingLinearTent_nat_add_mem_unit_sub_eq_zero
    (i a : Nat) (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hai : a ≠ i) (hai1 : a ≠ i + 1) :
    isingLinearTent ((i : Real) + x - (a : Real)) = 0 := by
  rcases lt_or_gt_of_ne hai with ha | ha
  · have hcast : (a : Real) + 1 ≤ (i : Real) := by
      exact_mod_cast (show a + 1 ≤ i by omega)
    have habs : 1 ≤ |(i : Real) + x - (a : Real)| := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    simp [isingLinearTent, habs]
  · have hai2 : i + 2 ≤ a := by omega
    have hcast : (i : Real) + 2 ≤ (a : Real) := by exact_mod_cast hai2
    have habs : 1 ≤ |(i : Real) + x - (a : Real)| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    simp [isingLinearTent, habs]



theorem finite_sum_isingLinearTent_nat_add_mem_unit
    {m : Nat} (i : Nat) (hi : i + 1 < m)
    (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (f : Fin m → Complex) :
    ∑ a : Fin m,
        ((isingLinearTent ((i : Real) + x - (a.1 : Real)) : Real) : Complex) * f a =
      (((1 - x : Real) : Complex) * f ⟨i, by omega⟩ +
        ((x : Real) : Complex) * f ⟨i + 1, by omega⟩) := by
  classical
  let i0 : Fin m := ⟨i, by omega⟩
  let i1 : Fin m := ⟨i + 1, by omega⟩
  rw [← Finset.sum_subset (s₁ := {i0, i1}) (s₂ := Finset.univ)]
  · simp [i0, i1, isingLinearTent_eq_one_sub_of_mem_unit x hx0 hx1,
      isingLinearTent_sub_one_eq_of_mem_unit x hx0 hx1]
  · simp
  · intro a _ha ha
    have hai : a.1 ≠ i := by
      intro h
      apply ha
      simp only [Finset.mem_insert, Finset.mem_singleton]
      left
      apply Fin.ext
      simpa [i0] using h
    have hai1 : a.1 ≠ i + 1 := by
      intro h
      apply ha
      simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      apply Fin.ext
      simpa [i1] using h
    rw [isingLinearTent_nat_add_mem_unit_sub_eq_zero
      i a.1 x hx0 hx1 hai hai1]
    simp


def isingRadialGridPosition (mesh : Real) (i j : Nat) : Complex :=
  (mesh : Complex) *
    ⟨((i : Real) + (j : Real) + 1) / 2,
      ((i : Real) - (j : Real)) / 2⟩


def isingRadialGridCoordinate (mesh : Real) (z : Complex) : Real × Real :=
  (z.re / mesh + z.im / mesh - 1 / 2,
    z.re / mesh - z.im / mesh - 1 / 2)

theorem isingRadialGridCoordinate_position
    (mesh : Real) (hmesh : mesh ≠ 0) (i j : Nat) :
    isingRadialGridCoordinate mesh (isingRadialGridPosition mesh i j) =
      ((i : Real), (j : Real)) := by
  apply Prod.ext <;>
    simp [isingRadialGridCoordinate, isingRadialGridPosition, hmesh] <;>
    field_simp <;> ring



def isingRadialGridCellPoint
    (mesh : Real) (i j : Nat) (x y : Real) : Complex :=
  (mesh : Complex) *
    ⟨((i : Real) + x + (j : Real) + y + 1) / 2,
      ((i : Real) + x - ((j : Real) + y)) / 2⟩

theorem isingRadialGridCoordinate_cellPoint
    (mesh : Real) (hmesh : mesh ≠ 0) (i j : Nat) (x y : Real) :
    isingRadialGridCoordinate mesh
        (isingRadialGridCellPoint mesh i j x y) =
      ((i : Real) + x, (j : Real) + y) := by
  apply Prod.ext <;>
    simp [isingRadialGridCoordinate, isingRadialGridCellPoint, hmesh] <;>
    field_simp <;> ring

theorem isingRadialGridCellPoint_sub
    (mesh : Real) (i j : Nat) (x x' y y' : Real) :
    isingRadialGridCellPoint mesh i j x y -
        isingRadialGridCellPoint mesh i j x' y' =
      (mesh : Complex) *
        ⟨((x - x') + (y - y')) / 2,
          ((x - x') - (y - y')) / 2⟩ := by
  apply Complex.ext <;>
    simp [isingRadialGridCellPoint] <;> ring



theorem abs_mesh_mul_cellCoordinate_l1_le_four_dist
    (mesh : Real) (i j : Nat) (x x' y y' : Real) :
    |mesh| * (|x - x'| + |y - y'|) ≤
      4 * dist (isingRadialGridCellPoint mesh i j x y)
        (isingRadialGridCellPoint mesh i j x' y') := by
  let z := isingRadialGridCellPoint mesh i j x y -
    isingRadialGridCellPoint mesh i j x' y'
  have hzre : z.re = mesh * ((x - x') + (y - y')) / 2 := by
    rw [show z = (mesh : Complex) *
        ⟨((x - x') + (y - y')) / 2,
          ((x - x') - (y - y')) / 2⟩ by
      exact isingRadialGridCellPoint_sub mesh i j x x' y y']
    simp
    ring
  have hzim : z.im = mesh * ((x - x') - (y - y')) / 2 := by
    rw [show z = (mesh : Complex) *
        ⟨((x - x') + (y - y')) / 2,
          ((x - x') - (y - y')) / 2⟩ by
      exact isingRadialGridCellPoint_sub mesh i j x x' y y']
    simp
    ring
  have hxident : mesh * (x - x') = z.re + z.im := by
    rw [hzre, hzim]
    ring
  have hyident : mesh * (y - y') = z.re - z.im := by
    rw [hzre, hzim]
    ring
  have hxbound : |mesh| * |x - x'| ≤ 2 * ‖z‖ := by
    rw [← abs_mul, hxident]
    calc
      |z.re + z.im| ≤ |z.re| + |z.im| := abs_add_le _ _
      _ ≤ ‖z‖ + ‖z‖ :=
        add_le_add (Complex.abs_re_le_norm z) (Complex.abs_im_le_norm z)
      _ = 2 * ‖z‖ := by ring
  have hybound : |mesh| * |y - y'| ≤ 2 * ‖z‖ := by
    rw [← abs_mul, hyident]
    calc
      |z.re - z.im| ≤ |z.re| + |z.im| := abs_sub _ _
      _ ≤ ‖z‖ + ‖z‖ :=
        add_le_add (Complex.abs_re_le_norm z) (Complex.abs_im_le_norm z)
      _ = 2 * ‖z‖ := by ring
  rw [mul_add]
  calc
    |mesh| * |x - x'| + |mesh| * |y - y'| ≤
        2 * ‖z‖ + 2 * ‖z‖ := add_le_add hxbound hybound
    _ = 4 * dist (isingRadialGridCellPoint mesh i j x y)
        (isingRadialGridCellPoint mesh i j x' y') := by
      rw [dist_eq_norm]
      change 2 * ‖z‖ + 2 * ‖z‖ = 4 * ‖z‖
      ring


def complexBilinearCell
    (a00 a10 a01 a11 : Complex) (x y : Real) : Complex :=
  ((1 - x) * (1 - y) : Real) * a00 +
    (x * (1 - y) : Real) * a10 +
    ((1 - x) * y : Real) * a01 +
    (x * y : Real) * a11



theorem complexBilinearCell_norm_sub_le
    (a00 a10 a01 a11 : Complex) (x x' y y' D : Real)
    (hx0' : 0 ≤ x') (hx1' : x' ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hbottom : ‖a10 - a00‖ ≤ D) (htop : ‖a11 - a01‖ ≤ D)
    (hleft : ‖a01 - a00‖ ≤ D) (hright : ‖a11 - a10‖ ≤ D) :
    ‖complexBilinearCell a00 a10 a01 a11 x y -
      complexBilinearCell a00 a10 a01 a11 x' y'‖ ≤
      D * (|x - x'| + |y - y'|) := by
  have hxident : complexBilinearCell a00 a10 a01 a11 x y -
        complexBilinearCell a00 a10 a01 a11 x' y =
      ((x - x' : Real) : Complex) *
        (((1 - y : Real) : Complex) * (a10 - a00) +
          ((y : Real) : Complex) * (a11 - a01)) := by
    unfold complexBilinearCell
    push_cast
    ring
  have hyident : complexBilinearCell a00 a10 a01 a11 x' y -
        complexBilinearCell a00 a10 a01 a11 x' y' =
      ((y - y' : Real) : Complex) *
        (((1 - x' : Real) : Complex) * (a01 - a00) +
          ((x' : Real) : Complex) * (a11 - a10)) := by
    unfold complexBilinearCell
    push_cast
    ring
  have hxbound : ‖complexBilinearCell a00 a10 a01 a11 x y -
        complexBilinearCell a00 a10 a01 a11 x' y‖ ≤ D * |x - x'| := by
    rw [hxident, norm_mul]
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1y : |1 - y| = 1 - y := abs_of_nonneg (by linarith)
    have hy : |y| = y := abs_of_nonneg hy0
    have hnorm1y : ‖((1 - y : Real) : Complex)‖ = 1 - y := by
      rw [Complex.norm_real, Real.norm_eq_abs, h1y]
    have hnormy : ‖((y : Real) : Complex)‖ = y := by
      rw [Complex.norm_real, Real.norm_eq_abs, hy]
    calc
      |x - x'| * ‖((1 - y : Real) : Complex) * (a10 - a00) +
          ((y : Real) : Complex) * (a11 - a01)‖ ≤
        |x - x'| * (‖((1 - y : Real) : Complex) * (a10 - a00)‖ +
          ‖((y : Real) : Complex) * (a11 - a01)‖) := by
            gcongr
            exact norm_add_le _ _
      _ = |x - x'| * ((1 - y) * ‖a10 - a00‖ +
          y * ‖a11 - a01‖) := by
        rw [norm_mul, norm_mul, hnorm1y, hnormy]
      _ ≤ |x - x'| * ((1 - y) * D + y * D) := by gcongr
      _ = D * |x - x'| := by ring
  have hybound : ‖complexBilinearCell a00 a10 a01 a11 x' y -
        complexBilinearCell a00 a10 a01 a11 x' y'‖ ≤ D * |y - y'| := by
    rw [hyident, norm_mul]
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1x : |1 - x'| = 1 - x' := abs_of_nonneg (by linarith)
    have hx : |x'| = x' := abs_of_nonneg hx0'
    have hnorm1x : ‖((1 - x' : Real) : Complex)‖ = 1 - x' := by
      rw [Complex.norm_real, Real.norm_eq_abs, h1x]
    have hnormx : ‖((x' : Real) : Complex)‖ = x' := by
      rw [Complex.norm_real, Real.norm_eq_abs, hx]
    calc
      |y - y'| * ‖((1 - x' : Real) : Complex) * (a01 - a00) +
          ((x' : Real) : Complex) * (a11 - a10)‖ ≤
        |y - y'| * (‖((1 - x' : Real) : Complex) * (a01 - a00)‖ +
          ‖((x' : Real) : Complex) * (a11 - a10)‖) := by
            gcongr
            exact norm_add_le _ _
      _ = |y - y'| * ((1 - x') * ‖a01 - a00‖ +
          x' * ‖a11 - a10‖) := by
        rw [norm_mul, norm_mul, hnorm1x, hnormx]
      _ ≤ |y - y'| * ((1 - x') * D + x' * D) := by gcongr
      _ = D * |y - y'| := by ring
  calc
    ‖complexBilinearCell a00 a10 a01 a11 x y -
        complexBilinearCell a00 a10 a01 a11 x' y'‖ ≤
      ‖complexBilinearCell a00 a10 a01 a11 x y -
          complexBilinearCell a00 a10 a01 a11 x' y‖ +
        ‖complexBilinearCell a00 a10 a01 a11 x' y -
          complexBilinearCell a00 a10 a01 a11 x' y'‖ := by
      rw [show complexBilinearCell a00 a10 a01 a11 x y -
          complexBilinearCell a00 a10 a01 a11 x' y' =
        (complexBilinearCell a00 a10 a01 a11 x y -
          complexBilinearCell a00 a10 a01 a11 x' y) +
        (complexBilinearCell a00 a10 a01 a11 x' y -
          complexBilinearCell a00 a10 a01 a11 x' y') by ring]
      exact norm_add_le _ _
    _ ≤ D * |x - x'| + D * |y - y'| := add_le_add hxbound hybound
    _ = _ := by ring



theorem isingRadialGridPosition_eq_scaledCarrierPosition
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (mesh : Real) (i j : Fin m) (s : FKIsingMedialSide) :
    isingRadialGridPosition mesh i.1 j.1 =
      (mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn
        (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) := by
  unfold isingRadialGridPosition
  congr 1
  change _ = (fkIsingSquareSitePosition
      (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm i j)).tail.1 +
    fkIsingSquareSitePosition
      (fkIsingSquareOrientedEdge n
        (fkIsingSquareRadialPatchEdge n m hm i j)).head.1) / 2
  by_cases h : Even (i.1 + j.1)
  · rw [fkIsingSquareRadialPatchEdge_eq_east n m hm i j h]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    simp [
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareSitePosition,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq]
    have hmod := Nat.even_iff.mp h
    have hqNat : 2 * ((i.1 + j.1 + 1) / 2) = i.1 + j.1 := by omega
    have hq : (2 : Real) * (((i.1 + j.1 + 1) / 2 : Nat) : Real) =
        (i.1 : Real) + (j.1 : Real) := by exact_mod_cast hqNat
    have hdivInt :
        ((i.1 : Int) + (j.1 : Int) + 1) / 2 =
          (((i.1 + j.1 + 1) / 2 : Nat) : Int) := by
      omega
    have hdivReal :
        ((((i.1 : Int) + (j.1 : Int) + 1) / 2 : Int) : Real) =
          (((i.1 + j.1 + 1) / 2 : Nat) : Real) := by
      norm_cast
    apply Complex.ext <;> simp
    all_goals rw [hdivReal]
    all_goals linarith
  · rw [fkIsingSquareRadialPatchEdge_eq_north n m hm i j h]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    simp [
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareSitePosition,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq]
    have hmod := Nat.not_even_iff.mp h
    have hqNat : 2 * ((i.1 + j.1 + 1) / 2) = i.1 + j.1 + 1 := by omega
    have hq : (2 : Real) * (((i.1 + j.1 + 1) / 2 : Nat) : Real) =
        (i.1 : Real) + (j.1 : Real) + 1 := by exact_mod_cast hqNat
    have hdivInt :
        ((i.1 : Int) + (j.1 : Int) + 1) / 2 =
          (((i.1 + j.1 + 1) / 2 : Nat) : Int) := by
      omega
    have hdivReal :
        ((((i.1 : Int) + (j.1 : Int) + 1) / 2 : Int) : Real) =
          (((i.1 + j.1 + 1) / 2 : Nat) : Real) := by
      norm_cast
    apply Complex.ext <;> simp
    all_goals rw [hdivReal]
    all_goals linarith


noncomputable def finiteRadialGridInterpolant
    (m : Nat) (mesh : Real) (value : Fin m → Fin m → Complex)
    (z : Complex) : Complex :=
  ∑ i : Fin m, ∑ j : Fin m,
    ((isingLinearTent ((isingRadialGridCoordinate mesh z).1 - (i.1 : Real)) *
      isingLinearTent ((isingRadialGridCoordinate mesh z).2 - (j.1 : Real)) : Real) :
        Complex) * value i j



theorem finiteRadialGridInterpolant_cellPoint
    {m : Nat} (mesh : Real) (hmesh : mesh ≠ 0)
    (value : Fin m → Fin m → Complex)
    (i j : Nat) (hi : i + 1 < m) (hj : j + 1 < m)
    (x y : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    finiteRadialGridInterpolant m mesh value
        (isingRadialGridCellPoint mesh i j x y) =
      complexBilinearCell
        (value ⟨i, by omega⟩ ⟨j, by omega⟩)
        (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩)
        (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩)
        (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) x y := by
  classical
  unfold finiteRadialGridInterpolant
  rw [isingRadialGridCoordinate_cellPoint mesh hmesh i j x y]
  have hcast (u v : Real) : (((u * v : Real) : Complex)) =
      (u : Complex) * (v : Complex) := by push_cast; rfl
  simp_rw [hcast, mul_assoc]
  simp_rw [← Finset.mul_sum]
  rw [finite_sum_isingLinearTent_nat_add_mem_unit i hi x hx0 hx1]
  simp_rw [finite_sum_isingLinearTent_nat_add_mem_unit j hj y hy0 hy1]
  unfold complexBilinearCell
  push_cast
  ring

theorem finiteRadialGridInterpolant_continuous
    (m : Nat) (mesh : Real) (value : Fin m → Fin m → Complex) :
    Continuous (finiteRadialGridInterpolant m mesh value) := by
  unfold finiteRadialGridInterpolant isingRadialGridCoordinate
  apply continuous_finset_sum
  intro i _hi
  apply continuous_finset_sum
  intro j _hj
  have hx : Continuous (fun z : Complex =>
      z.re / mesh + z.im / mesh - 1 / 2 - (i.1 : Real)) := by
    fun_prop
  have hy : Continuous (fun z : Complex =>
      z.re / mesh - z.im / mesh - 1 / 2 - (j.1 : Real)) := by
    fun_prop
  exact (Complex.continuous_ofReal.comp
    ((isingLinearTent_continuous.comp hx).mul
      (isingLinearTent_continuous.comp hy))).mul continuous_const

@[simp] theorem finiteRadialGridInterpolant_position
    (m : Nat) (mesh : Real) (hmesh : mesh ≠ 0)
    (value : Fin m → Fin m → Complex) (i j : Fin m) :
    finiteRadialGridInterpolant m mesh value
        (isingRadialGridPosition mesh i.1 j.1) = value i j := by
  classical
  unfold finiteRadialGridInterpolant
  rw [isingRadialGridCoordinate_position mesh hmesh]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _hb hbj
      rw [isingLinearTent_natCast_sub_eq_zero j.1 b.1 (by
        intro h
        apply hbj
        exact Fin.ext h.symm)]
      simp
    · simp
  · intro a _ha hai
    rw [isingLinearTent_natCast_sub_eq_zero i.1 a.1 (by
      intro h
      apply hai
      exact Fin.ext h.symm)]
    simp
  · simp



noncomputable def fkIsingSquareBoundaryRadialPatchInterpolant
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (mesh : Real) :
    Complex → Complex :=
  finiteRadialGridInterpolant m mesh (fun i j =>
    fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j /
      (Real.sqrt (2 * mesh) : Complex))

theorem fkIsingSquareBoundaryRadialPatchInterpolant_continuous
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (mesh : Real) :
    Continuous (fkIsingSquareBoundaryRadialPatchInterpolant n m hn hm mesh) :=
  finiteRadialGridInterpolant_continuous _ _ _



@[simp] theorem fkIsingSquareBoundaryRadialPatchInterpolant_position
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (mesh : Real) (hmesh : mesh ≠ 0) (i j : Fin m) :
    fkIsingSquareBoundaryRadialPatchInterpolant n m hn hm mesh
        (isingRadialGridPosition mesh i.1 j.1) =
      fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j /
        (Real.sqrt (2 * mesh) : Complex) :=
  finiteRadialGridInterpolant_position m mesh hmesh _ i j



theorem fkIsingSquareBoundaryRadialPatchInterpolant_projection
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (mesh : Real) (hmesh : 0 < mesh) (i j : Fin m)
    (s : FKIsingMedialSide) :
    isingProj (fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)))
      (fkIsingSquareBoundaryRadialPatchInterpolant n m hn hm mesh
        (isingRadialGridPosition mesh i.1 j.1)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) /
        (Real.sqrt (2 * mesh) : Complex) := by
  rw [fkIsingSquareBoundaryRadialPatchInterpolant_position _ _ _ _ _ hmesh.ne']
  have hproj_div (u z : Complex) (r : Real) :
      isingProj u (z / (r : Complex)) = isingProj u z / (r : Complex) := by
    unfold isingProj
    simp
    ring
  rw [hproj_div]
  rw [fkIsingSquareBoundaryRadialPatchFullObservable_projection]





noncomputable def fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (gridScale normalizationScale : Real) : Complex → Complex :=
  finiteRadialGridInterpolant m gridScale (fun i j =>
    fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j /
      (Real.sqrt (2 * normalizationScale) : Complex))

theorem fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_continuous
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (gridScale normalizationScale : Real) :
    Continuous (fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant
      n m hn hm gridScale normalizationScale) :=
  finiteRadialGridInterpolant_continuous _ _ _

@[simp] theorem fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_position
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (i j : Fin m) :
    fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant
        n m hn hm gridScale normalizationScale
        (isingRadialGridPosition gridScale i.1 j.1) =
      fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm i j /
        (Real.sqrt (2 * normalizationScale) : Complex) :=
  finiteRadialGridInterpolant_position m gridScale hgridScale _ i j




theorem fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_projection
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (gridScale normalizationScale : Real) (hgridScale : 0 < gridScale)
    (i j : Fin m) (s : FKIsingMedialSide) :
    isingProj (fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)))
      (fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant
        n m hn hm gridScale normalizationScale
        (isingRadialGridPosition gridScale i.1 j.1)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) /
        (Real.sqrt (2 * normalizationScale) : Complex) := by
  rw [fkIsingSquareBoundaryRadialPatchTwoScaleInterpolant_position
    _ _ _ _ _ _ hgridScale.ne']
  have hproj_div (u z : Complex) (r : Real) :
      isingProj u (z / (r : Complex)) = isingProj u z / (r : Complex) := by
    unfold isingProj
    simp
    ring
  rw [hproj_div]
  rw [fkIsingSquareBoundaryRadialPatchFullObservable_projection]

end

end StatMech.Universality
