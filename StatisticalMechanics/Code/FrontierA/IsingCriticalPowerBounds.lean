/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingCriticalCubeInfrared

open Filter Finset MeasureTheory Set Topology
open scoped BigOperators

namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

variable {d : Nat}


def criticalIsingSupRadius (z : Site d) : Nat :=
  Finset.univ.sup (fun i => (z i).natAbs)

theorem coordinate_natAbs_le_criticalIsingSupRadius
    (z : Site d) (i : Fin d) :
    (z i).natAbs <= criticalIsingSupRadius z := by
  exact Finset.le_sup (f := fun i => (z i).natAbs) (Finset.mem_univ i)

theorem criticalIsingSupRadius_pos
    (z : Site d) (hz : z ≠ Percolation.origin d) :
    0 < criticalIsingSupRadius z := by
  by_contra h
  have hzero : criticalIsingSupRadius z = 0 := by omega
  apply hz
  funext i
  have hi := coordinate_natAbs_le_criticalIsingSupRadius z i
  rw [hzero] at hi
  have hzi : z i = 0 := Int.natAbs_eq_zero.mp (by omega)
  simpa [Percolation.origin] using hzi



theorem mem_boxSV_vbF_criticalIsingSupRadius
    (z : Site d) (hz : z ≠ Percolation.origin d) :
    z ∈ boxSV_vbF d (criticalIsingSupRadius z) := by
  classical
  let r := criticalIsingSupRadius z
  have hr : 0 < r := criticalIsingSupRadius_pos z hz
  have hbox : z ∈ box d r := by
    intro i
    exact coordinate_natAbs_le_criticalIsingSupRadius z i
  have huniv : (Finset.univ : Finset (Fin d)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hr0 : r = 0 := by simp [r, criticalIsingSupRadius, h]
    omega
  obtain ⟨i, _hi, himax⟩ := Finset.exists_mem_eq_sup' huniv
    (fun i : Fin d => (z i).natAbs)
  rw [boxSV_vbF, Finset.mem_sdiff]
  refine ⟨?_, ?_⟩
  · change z ∈ (boxSV_boxF d r : Set (Site d))
    rw [boxSV_coe_boxF]
    exact hbox
  · intro hinner
    have hinnerSet : z ∈ box d (r - 1) := by
      change z ∈ (boxSV_boxF d (r - 1) : Set (Site d)) at hinner
      rw [boxSV_coe_boxF] at hinner
      exact hinner
    have hiinner := hinnerSet i
    change (z i).natAbs <= r - 1 at hiinner
    have himax' : (z i).natAbs = r := by
      rw [Finset.sup'_eq_sup huniv] at himax
      simpa [r, criticalIsingSupRadius] using himax.symm
    omega



theorem currentContinuityFreeTwoPoint_eq_origin_sub
    (beta : Real) (hbeta : 0 <= beta) (x y : Site d) :
    currentContinuityFreeTwoPoint d beta x y =
      currentContinuityFreeTwoPoint d beta (Percolation.origin d) (y - x) := by
  let g : Multiplicative (Site d) := Multiplicative.ofAdd (-x)
  have hgx : g • x = Percolation.origin d := by
    funext i
    simp [g, smul_site_apply, Percolation.origin]
  have hgy : g • y = y - x := by
    funext i
    simp [g, smul_site_apply, sub_eq_add_neg, add_comm]
  have htranslate := integral_freeState_spinProd_translate
    d beta hbeta g ({x, y} : Finset (Site d))
  have himage : ({x, y} : Finset (Site d)).image (fun z => g • z) =
      {Percolation.origin d, y - x} := by
    simp [hgx, hgy]
  rw [himage] at htranslate
  exact htranslate.symm

theorem currentContinuityFreeTwoPoint_le_one_of_ne
    (beta : Real) (hbeta : 0 < beta) (hd : 1 <= d)
    (x y : Site d) (hxy : x ≠ y) :
    currentContinuityFreeTwoPoint d beta x y <= 1 := by
  rw [currentContinuityFreeTwoPoint_eq_freeInfiniteTwoPoint
    beta hbeta hd x y hxy]
  exact measureReal_le_one



theorem exists_criticalFreeTwoPoint_shell_le_power_all
    (hd : 2 < d) :
    ∃ C : Real, 0 < C ∧ ∀ (r : Nat), 1 <= r ->
      ∀ x ∈ boxSV_vbF d r,
        currentContinuityFreeTwoPoint d
            (IsingFK.betaC (magnetization d)) (Percolation.origin d) x <=
          C / (r : Real) ^ (d - 2) := by
  obtain ⟨C0, hC0, hlarge⟩ := exists_criticalFreeTwoPoint_shell_le_power hd
  let D : Real := (2 * (d : Real)) ^ (d - 2)
  let C : Real := C0 + D
  have hD : 0 < D := pow_pos (by positivity) _
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro r hr x hx
  by_cases hrlarge : 2 * d <= r
  · exact (hlarge r hrlarge x hx).trans (by
      have hdenom : 0 <= (r : Real) ^ (d - 2) := by positivity
      exact div_le_div_of_nonneg_right (by dsimp [C]; linarith) hdenom)
  · have hbetaC : 0 < IsingFK.betaC (magnetization d) := by
      rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 <= d)]
      exact tildeBetaCIsing_pos (by omega)
    have hxo : Percolation.origin d ≠ x := by
      intro h
      subst x
      rw [boxSV_vbF, Finset.mem_sdiff] at hx
      apply hx.2
      change Percolation.origin d ∈ (boxSV_boxF d (r - 1) : Set (Site d))
      rw [boxSV_coe_boxF]
      exact origin_mem_box' (r - 1)
    have hone := currentContinuityFreeTwoPoint_le_one_of_ne
      (d := d) (IsingFK.betaC (magnetization d)) hbetaC (by omega)
      (Percolation.origin d) x hxo
    have hrscaleNat : r <= 2 * d := by omega
    have hrscale : (r : Real) <= 2 * (d : Real) := by
      exact_mod_cast hrscaleNat
    have hpow : (r : Real) ^ (d - 2) <= D := by
      dsimp [D]
      gcongr
    have hpowC : (r : Real) ^ (d - 2) <= C := by
      dsimp [C]
      linarith
    have hpowpos : 0 < (r : Real) ^ (d - 2) := by positivity
    exact hone.trans ((le_div_iff₀ hpowpos).2 (by simpa using hpowC))



theorem exists_criticalFreeTwoPoint_shell_ge_power_all
    (hd : 2 < d) :
    ∃ c : Real, 0 < c ∧ ∀ (r : Nat), 1 <= r ->
      ∀ x ∈ boxSV_vbF d r,
        c / (r : Real) ^ (d - 1) <=
          currentContinuityFreeTwoPoint d
            (IsingFK.betaC (magnetization d)) (Percolation.origin d) x := by
  let betaC := IsingFK.betaC (magnetization d)
  let A : Real := 4 * (d : Real) ^ 2 * Real.tanh betaC *
    (2 * (d : Real) + 1) ^ (d - 1)
  let c : Real := 1 / A
  have hbetaC : 0 < betaC := by
    dsimp [betaC]
    rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 <= d)]
    exact tildeBetaCIsing_pos (by omega)
  have htanh : 0 < Real.tanh betaC := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hbetaC) (Real.cosh_pos betaC)
  have hA : 0 < A := by dsimp [A]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro r hr x hx
  have hlower := criticalBoundaryTwoPoint_powerLower
    (d := d) (n := r) (by omega : 2 <= d) hr x hx
  have hrR : (1 : Real) <= r := by exact_mod_cast hr
  have hscale : 2 * (((d * r : Nat) : Real)) + 1 <=
      (2 * (d : Real) + 1) * (r : Real) := by
    push_cast
    nlinarith [hrR]
  have hscalePow :
      (2 * (((d * r : Nat) : Real)) + 1) ^ (d - 1) <=
        ((2 * (d : Real) + 1) * (r : Real)) ^ (d - 1) := by
    gcongr
  have hfactor : 0 <=
      4 * (d : Real) ^ 2 * Real.tanh betaC := by positivity
  have hdenom :
      4 * (d : Real) ^ 2 * Real.tanh betaC *
          (2 * (((d * r : Nat) : Real)) + 1) ^ (d - 1) <=
        A * (r : Real) ^ (d - 1) := by
    calc
      4 * (d : Real) ^ 2 * Real.tanh betaC *
          (2 * (((d * r : Nat) : Real)) + 1) ^ (d - 1) <=
          (4 * (d : Real) ^ 2 * Real.tanh betaC) *
            (((2 * (d : Real) + 1) * (r : Real)) ^ (d - 1)) :=
        mul_le_mul_of_nonneg_left hscalePow hfactor
      _ = A * (r : Real) ^ (d - 1) := by
        simp only [mul_pow]
        dsimp [A]
        ring
  have hrawpos : 0 <
      4 * (d : Real) ^ 2 * Real.tanh betaC *
        (2 * (((d * r : Nat) : Real)) + 1) ^ (d - 1) := by positivity
  have hinv := one_div_le_one_div_of_le hrawpos hdenom
  have hnormalized : c / (r : Real) ^ (d - 1) <=
      1 / (4 * (d : Real) ^ 2 * Real.tanh betaC *
        (2 * (((d * r : Nat) : Real)) + 1) ^ (d - 1)) := by
    calc
      c / (r : Real) ^ (d - 1) =
          1 / (A * (r : Real) ^ (d - 1)) := by
        dsimp [c]
        field_simp
      _ <= 1 / (4 * (d : Real) ^ 2 * Real.tanh betaC *
          (2 * (((d * r : Nat) : Real)) + 1) ^ (d - 1)) := hinv
  exact hnormalized.trans (by simpa [betaC] using hlower)



theorem exists_criticalFreeTwoPoint_shell_powerBounds_all
    (hd : 2 < d) :
    ∃ c C : Real, 0 < c ∧ c < C ∧ ∀ (r : Nat), 1 <= r ->
      ∀ x ∈ boxSV_vbF d r,
        c / (r : Real) ^ (d - 1) <=
            currentContinuityFreeTwoPoint d
              (IsingFK.betaC (magnetization d)) (Percolation.origin d) x ∧
          currentContinuityFreeTwoPoint d
              (IsingFK.betaC (magnetization d)) (Percolation.origin d) x <=
            C / (r : Real) ^ (d - 2) := by
  obtain ⟨c, hc, hlower⟩ := exists_criticalFreeTwoPoint_shell_ge_power_all hd
  obtain ⟨C0, hC0, hupper⟩ := exists_criticalFreeTwoPoint_shell_le_power_all hd
  let C := C0 + c
  have hcC : c < C := by dsimp [C]; linarith
  refine ⟨c, C, hc, hcC, ?_⟩
  intro r hr x hx
  refine ⟨hlower r hr x hx, ?_⟩
  exact (hupper r hr x hx).trans (by
    have hdenom : 0 <= (r : Real) ^ (d - 2) := by positivity
    exact div_le_div_of_nonneg_right (by dsimp [C]; linarith) hdenom)




theorem criticalIsingTwoPoint_powerBounds
    (hd : 2 < d) :
    ∃ c C : Real, 0 < c ∧ c < C ∧ ∀ (x y : Site d), x ≠ y ->
      c / (criticalIsingSupRadius (y - x) : Real) ^ (d - 1) <=
          currentContinuityFreeTwoPoint d
            (IsingFK.betaC (magnetization d)) x y ∧
        currentContinuityFreeTwoPoint d
            (IsingFK.betaC (magnetization d)) x y <=
          C / (criticalIsingSupRadius (y - x) : Real) ^ (d - 2) := by
  obtain ⟨c, C, hc, hcC, hshell⟩ :=
    exists_criticalFreeTwoPoint_shell_powerBounds_all hd
  refine ⟨c, C, hc, hcC, ?_⟩
  intro x y hxy
  let z := y - x
  have hz : z ≠ Percolation.origin d := by
    change y - x ≠ 0
    exact sub_ne_zero.mpr hxy.symm
  have hr := criticalIsingSupRadius_pos z hz
  have hzshell := mem_boxSV_vbF_criticalIsingSupRadius z hz
  have hbound := hshell (criticalIsingSupRadius z) (by omega) z hzshell
  have hbetaC : 0 <= IsingFK.betaC (magnetization d) := by
    rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 <= d)]
    exact (tildeBetaCIsing_pos (by omega)).le
  have htranslate := currentContinuityFreeTwoPoint_eq_origin_sub
    (d := d) (IsingFK.betaC (magnetization d)) hbetaC x y
  dsimp [z] at hbound
  rw [htranslate]
  exact hbound

end StatMech.FrontierA
