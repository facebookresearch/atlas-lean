/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingCoordinateReflectionInfinite
import Code.FrontierA.IsingCriticalShellGreenComparison

open Finset

namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

variable {d : Nat}



theorem currentContinuityFreeTwoPoint_axis_succ_le
    (hd : 2 <= d) (i : Fin d)
    (beta : Real) (hbeta : 0 <= beta)
    (n : Nat) (hn : 1 <= n) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single i ((n + 1 : Nat) : Int)) <=
      currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single i (n : Int)) := by
  let i0 : Fin d := ⟨0, by omega⟩
  let i1 : Fin d := ⟨1, by omega⟩
  let j : Fin d := if i = i0 then i1 else i0
  have hij : i ≠ j := by
    dsimp [j]
    split_ifs with hi
    · subst i
      intro h
      have := congrArg Fin.val h
      simp [i0, i1] at this
    · exact hi
  let x : Site d := Pi.single i (n : Int) + Pi.single j (1 : Int)
  have hxi : x i = (n : Int) := by
    simp [x, hij]
  have hxine : x i ≠ 0 := by
    rw [hxi]
    exact_mod_cast (Nat.ne_of_gt hn)
  have hsum : (∑ a, (x a).natAbs) = n + 1 := by
    classical
    have hterm (a : Fin d) :
        (x a).natAbs = if a = i then n else if a = j then 1 else 0 := by
      by_cases hai : a = i
      · subst a
        simp [x, hij]
      · by_cases haj : a = j
        · subst a
          simp [x, hai]
        · simp [x, hai, haj]
    simp_rw [hterm]
    let f : Fin d -> Nat := fun a =>
      if a = i then n else if a = j then 1 else 0
    change (∑ a, f a) = n + 1
    rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)]
    have hjmem : j ∈ Finset.univ.erase i := by simp [Ne.symm hij]
    rw [← Finset.sum_erase_add (Finset.univ.erase i) f hjmem]
    have hzero : ∑ a ∈ (Finset.univ.erase i).erase j, f a = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      obtain ⟨haj, ha⟩ := Finset.mem_erase.mp ha
      have hai := (Finset.mem_erase.mp ha).1
      simp [f, hai, haj]
    rw [hzero]
    simp [f, Ne.symm hij]
    omega
  have hl1 := currentContinuityFreeTwoPoint_l1Axis_le
    i beta hbeta x hxine
  rw [hsum] at hl1
  have htransverse := currentContinuityFreeTwoPoint_le_axis_of_coordinate_eq
    i beta hbeta x n hn hxi
  exact hl1.trans htransverse


theorem currentContinuityFreeTwoPoint_axis_antitone
    (hd : 2 <= d) (i : Fin d)
    (beta : Real) (hbeta : 0 <= beta)
    (p q : Nat) (hp : 1 <= p) (hpq : p <= q) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single i (q : Int)) <=
      currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single i (p : Int)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hpq
  induction t with
  | zero => simp
  | succ t ih =>
      have hstep := currentContinuityFreeTwoPoint_axis_succ_le
        hd i beta hbeta (p + t) (by omega)
      have hstep' :
          currentContinuityFreeTwoPoint d beta (Percolation.origin d)
              (Pi.single i ((p + t + 1 : Nat) : Int)) <=
            currentContinuityFreeTwoPoint d beta (Percolation.origin d)
              (Pi.single i ((p + t : Nat) : Int)) := by
        simpa [Nat.add_assoc] using hstep
      exact hstep'.trans (ih (by omega))



theorem criticalIsingMessagerMiracle
    (d : Nat) (hd : 2 <= d) :
    CriticalIsingMessagerMiracle d (by omega) := by
  let betaC := IsingFK.betaC (magnetization d)
  have hbetaC : 0 < betaC := by
    dsimp [betaC]
    rw [isingFK_betaC_eq_tildeBetaCIsing (by omega : 2 <= d)]
    exact tildeBetaCIsing_pos (by omega)
  intro n hn
  constructor
  · intro e he
    exact currentContinuityFreeTwoPoint_shell_le_axis
      (by omega) betaC hbetaC.le n hn e.1
        (boundaryEdges_fst_mem_boxSV_vbF hn he)
  · intro x hx
    obtain ⟨i, hi⟩ :=
      exists_natAbs_coordinate_eq_of_mem_boxSV_vbF hn x hx
    have hxi : x i ≠ 0 := by
      intro h
      rw [h] at hi
      simp at hi
      omega
    let L : Nat := ∑ j, (x j).natAbs
    have hnL : n <= L := by
      dsimp [L]
      calc
        n = (x i).natAbs := hi.symm
        _ <= ∑ j, (x j).natAbs :=
          Finset.single_le_sum
            (f := fun j : Fin d => (x j).natAbs)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hLd : L <= d * n := by
      dsimp [L]
      calc
        (∑ j, (x j).natAbs) <= ∑ _j : Fin d, n := by
          apply Finset.sum_le_sum
          intro j _
          have hx' := hx
          rw [boxSV_vbF, Finset.mem_sdiff] at hx'
          have hxBox : x ∈ box d n := by
            rw [← boxSV_coe_boxF]
            exact hx'.1
          exact hxBox j
        _ = d * n := by simp
    have haxisL := currentContinuityFreeTwoPoint_axis_antitone
      hd i betaC hbetaC.le L (d * n) (hn.trans hnL) hLd
    have hl1 := currentContinuityFreeTwoPoint_l1Axis_le
      i betaC hbetaC.le x hxi
    change currentContinuityFreeTwoPoint d betaC (Percolation.origin d)
        (Pi.single i (L : Int)) <= _ at hl1
    let j0 : Fin d := ⟨0, by omega⟩
    have haxisSwap :
        currentContinuityFreeTwoPoint d betaC (Percolation.origin d)
            (criticalAxisSite (by omega) (d * n)) =
          currentContinuityFreeTwoPoint d betaC (Percolation.origin d)
            (Pi.single i ((d * n : Nat) : Int)) := by
      by_cases hij : i = j0
      · rw [hij]
        congr 1
        funext a
        by_cases ha : a = j0
        · subst a
          simp [criticalAxisSite, j0]
        · simp [criticalAxisSite, j0, ha]
      · have hsymm := currentContinuityFreeTwoPoint_coordinateSwap
          i j0 hij betaC hbetaC.le (Pi.single i ((d * n : Nat) : Int))
        have hreflect : isingDiagonalReflect i j0 0
            (Pi.single i ((d * n : Nat) : Int) : Site d) =
              Pi.single j0 ((d * n : Nat) : Int) := by
          funext a
          by_cases hai : a = i
          · subst a
            simp [hij]
          · by_cases haj : a = j0
            · subst a
              simp [hij]
            · rw [isingDiagonalReflect_apply_of_ne i j0 a hai haj]
              simp [hai, haj]
        rw [hreflect] at hsymm
        have hcritical : (Pi.single j0 ((d * n : Nat) : Int) : Site d) =
            criticalAxisSite (by omega) (d * n) := by
          funext a
          by_cases ha : a = j0
          · subst a
            simp [criticalAxisSite, j0]
          · simp [criticalAxisSite, j0, ha]
        rw [hcritical] at hsymm
        exact hsymm
    rw [haxisSwap]
    exact haxisL.trans hl1


theorem criticalBoundaryTwoPoint_powerLower
    {d n : Nat} (hd : 2 <= d) (hn : 1 <= n)
    (x : Site d) (hx : x ∈ boxSV_vbF d n) :
    1 / (4 * d ^ 2 * Real.tanh (IsingFK.betaC (magnetization d)) *
      (2 * ((d * n : Nat) : Real) + 1) ^ (d - 1)) <=
      currentContinuityFreeTwoPoint d
        (IsingFK.betaC (magnetization d)) (Percolation.origin d) x := by
  exact criticalBoundaryTwoPoint_powerLower_of_messagerMiracle
    hd hn (criticalIsingMessagerMiracle d hd) x hx

end StatMech.FrontierA
