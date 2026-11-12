/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters
import Code.Lattice.UniqueInfiniteComponent
import Code.Lattice.BoundaryConnected
import Code.Lattice.ContourAnchor
import Code.Lattice.LeftFace
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.ContourLinksExits
import Code.Lattice.InterfaceOrbit
import Code.Lattice.ExitDartsOrbit
import Code.Lattice.JordanSingleCycle
import Code.Lattice.Umlaufsatz
import Code.Percolation.OutermostContour
import Code.Percolation.PcFarContour

open Finset Set SimpleGraph Function

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}








open Classical in

noncomputable def fdc_rightExitIdx (_hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) : ℕ :=
  Nat.findGreatest (fun m => axisSite m ∈ cluster 2 ω (origin 2)) R


theorem fdc_rightExitIdx_le (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    fdc_rightExitIdx (ω := ω) hfin R ≤ R := by
  classical
  rw [fdc_rightExitIdx]; exact Nat.findGreatest_le R



theorem fdc_rightExitIdx_mem (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    axisSite (fdc_rightExitIdx (ω := ω) hfin R) ∈ cluster 2 ω (origin 2) := by
  classical
  rw [fdc_rightExitIdx]
  exact Nat.findGreatest_spec (P := fun m => axisSite m ∈ cluster 2 ω (origin 2))
    (Nat.zero_le R) (axisSite_zero_mem_cluster (ω := ω))



theorem fdc_rightExitIdx_is_greatest (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    {k : ℕ} (h1 : fdc_rightExitIdx (ω := ω) hfin R < k) (h2 : k ≤ R) :
    axisSite k ∉ cluster 2 ω (origin 2) := by
  classical
  rw [fdc_rightExitIdx] at h1
  exact Nat.findGreatest_is_greatest h1 h2




theorem fdc_rightExitIdx_succ_not_mem (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    axisSite (fdc_rightExitIdx (ω := ω) hfin R + 1) ∉ cluster 2 ω (origin 2) := by
  set m := fdc_rightExitIdx (ω := ω) hfin R with hm
  rcases lt_or_eq_of_le (fdc_rightExitIdx_le (ω := ω) hfin R) with hlt | heq
  · 
    exact fdc_rightExitIdx_is_greatest (ω := ω) hfin R (by omega) (by omega)
  · 
    have hmR : m = R := heq
    have hext : (axisSite (m + 1) : Site 2) ∈ exterior 2 R := by
      refine ⟨0, ?_⟩
      show R < ((m : ℤ) + 1).natAbs
      rw [show ((m:ℤ)+1).natAbs = m + 1 by rw [Int.natAbs_eq_iff]; left; push_cast; ring]
      omega
    exact exterior_subset_compl _ R hR hext








theorem fdc_axis_reach (K : Set (Site 2)) (a j : ℕ)
    (hout : ∀ k, a ≤ k → k ≤ a + j → (axisSite k : Site 2) ∉ K) :
    ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨axisSite a, hout a le_rfl (by omega)⟩
      ⟨axisSite (a + j), hout (a + j) (by omega) le_rfl⟩ := by
  induction j with
  | zero => exact Reachable.refl _
  | succ n ih =>
    have hout' : ∀ k, a ≤ k → k ≤ a + n → (axisSite k : Site 2) ∉ K := by
      intro k h1 h2; exact hout k h1 (by omega)
    have h1 := ih hout'
    have hk1 : (axisSite (a + n) : Site 2) ∉ K := hout (a + n) (by omega) (by omega)
    have hk2 : (axisSite (a + n + 1) : Site 2) ∉ K := hout (a + n + 1) (by omega) (by omega)
    have hdiff : unitWt ((axisSite (a + n) : Site 2) - axisSite (a + n + 1)) = 1 := by
      unfold unitWt
      rw [Fin.sum_univ_two]
      have e0 : ((axisSite (a + n) : Site 2) - axisSite (a + n + 1)) 0 = -1 := by
        simp [axisSite, Pi.sub_apply]
      have e1 : ((axisSite (a + n) : Site 2) - axisSite (a + n + 1)) 1 = 0 := by
        simp [axisSite, Pi.sub_apply]
      rw [e0, e1]; rfl
    have hstep := complReachable_of_unitDiff K hk1 hk2 hdiff
    have heq : (axisSite (a + n + 1) : Site 2) = axisSite (a + (n + 1)) := by
      have : a + n + 1 = a + (n + 1) := by omega
      rw [this]
    exact complReachable_congr (G := hypercubicLattice 2) (S := Kᶜ) rfl heq (h1.trans hstep)









theorem fdc_rightExit_adj (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    (hypercubicLattice 2).Adj (axisSite (fdc_rightExitIdx (ω := ω) hfin R))
      (axisSite (fdc_rightExitIdx (ω := ω) hfin R + 1)) := by
  set m := fdc_rightExitIdx (ω := ω) hfin R
  have hsucc : (axisSite (m + 1) : Site 2) = ![(m : ℤ) + 1, 0] := by
    funext i; fin_cases i <;> simp [axisSite]
  rw [show (axisSite m : Site 2) = ![(m : ℤ), 0] from rfl, hsucc]
  exact latAdj_right (m : ℤ) 0



noncomputable def fdc_farExitDart (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) : Dart where
  tail := axisSite (fdc_rightExitIdx (ω := ω) hfin R)
  head := axisSite (fdc_rightExitIdx (ω := ω) hfin R + 1)
  adj := fdc_rightExit_adj (ω := ω) hfin R

@[simp] theorem fdc_farExitDart_tail (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    (fdc_farExitDart (ω := ω) hfin R).tail = axisSite (fdc_rightExitIdx (ω := ω) hfin R) := rfl

@[simp] theorem fdc_farExitDart_head (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    (fdc_farExitDart (ω := ω) hfin R).head = axisSite (fdc_rightExitIdx (ω := ω) hfin R + 1) := rfl




theorem fdc_farExitDart_isBoundaryDart (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    IsBoundaryDart (cluster 2 ω (origin 2)) (fdc_farExitDart (ω := ω) hfin R) :=
  ⟨fdc_rightExitIdx_mem (ω := ω) hfin R, fdc_rightExitIdx_succ_not_mem (ω := ω) hfin R hR⟩









theorem fdc_rightRun_not_mem (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) {k : ℕ}
    (h1 : fdc_rightExitIdx (ω := ω) hfin R + 1 ≤ k) (h2 : k ≤ R + 1) :
    (axisSite k : Site 2) ∉ cluster 2 ω (origin 2) := by
  rcases lt_or_eq_of_le h2 with hlt | heq
  · 
    exact fdc_rightExitIdx_is_greatest (ω := ω) hfin R (by omega) (by omega)
  · 
    have hkR : k = R + 1 := heq
    have hext : (axisSite k : Site 2) ∈ exterior 2 R := by
      refine ⟨0, ?_⟩
      show R < ((k : ℤ)).natAbs
      rw [show ((k:ℤ)).natAbs = k by exact Int.natAbs_natCast k]
      omega
    exact exterior_subset_compl _ R hR hext




theorem fdc_farExitDart_head_reaches_axisFar (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨(fdc_farExitDart (ω := ω) hfin R).head,
        (fdc_farExitDart_isBoundaryDart (ω := ω) hfin R hR).2⟩
      ⟨axisSite (R + 1), fdc_rightRun_not_mem (ω := ω) hfin R hR
        (Nat.succ_le_succ (fdc_rightExitIdx_le (ω := ω) hfin R)) (le_refl _)⟩ := by
  set m := fdc_rightExitIdx (ω := ω) hfin R with hm
  have hmR : m ≤ R := fdc_rightExitIdx_le (ω := ω) hfin R
  
  have hout : ∀ k, m + 1 ≤ k → k ≤ (m + 1) + (R - m) → (axisSite k : Site 2)
      ∉ cluster 2 ω (origin 2) := by
    intro k hk1 hk2
    have hk2' : k ≤ R + 1 := by omega
    exact fdc_rightRun_not_mem (ω := ω) hfin R hR hk1 hk2'
  have hreach := fdc_axis_reach (cluster 2 ω (origin 2)) (m + 1) (R - m) hout
  
  have heq : (axisSite ((m + 1) + (R - m)) : Site 2) = axisSite (R + 1) := by
    have : (m + 1) + (R - m) = R + 1 := by
      have : m ≤ R := fdc_rightExitIdx_le (ω := ω) hfin R
      omega
    rw [this]
  exact complReachable_congr (G := hypercubicLattice 2) (S := (cluster 2 ω (origin 2))ᶜ)
    rfl heq hreach








open Classical in

noncomputable def fdc_leftExitIdx (_hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) : ℕ :=
  Nat.findGreatest (fun n => leftAxisSite n ∈ cluster 2 ω (origin 2)) R


theorem fdc_leftExitIdx_le (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    fdc_leftExitIdx (ω := ω) hfin R ≤ R := by
  classical
  rw [fdc_leftExitIdx]; exact Nat.findGreatest_le R


theorem fdc_leftExitIdx_mem (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R) ∈ cluster 2 ω (origin 2) := by
  classical
  rw [fdc_leftExitIdx]
  exact Nat.findGreatest_spec (P := fun n => leftAxisSite n ∈ cluster 2 ω (origin 2))
    (Nat.zero_le R) (leftAxisSite_zero_mem_cluster (ω := ω))


theorem fdc_leftExitIdx_is_greatest (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    {k : ℕ} (h1 : fdc_leftExitIdx (ω := ω) hfin R < k) (h2 : k ≤ R) :
    leftAxisSite k ∉ cluster 2 ω (origin 2) := by
  classical
  rw [fdc_leftExitIdx] at h1
  exact Nat.findGreatest_is_greatest h1 h2


theorem fdc_leftRun_not_mem (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) {k : ℕ}
    (h1 : fdc_leftExitIdx (ω := ω) hfin R + 1 ≤ k) (h2 : k ≤ R + 1) :
    (leftAxisSite k : Site 2) ∉ cluster 2 ω (origin 2) := by
  rcases lt_or_eq_of_le h2 with hlt | heq
  · exact fdc_leftExitIdx_is_greatest (ω := ω) hfin R (by omega) (by omega)
  · have hkR : k = R + 1 := heq
    have hext : (leftAxisSite k : Site 2) ∈ exterior 2 R := by
      refine ⟨0, ?_⟩
      show R < (-(k : ℤ)).natAbs
      rw [Int.natAbs_neg, show ((k:ℤ)).natAbs = k by exact Int.natAbs_natCast k]
      omega
    exact exterior_subset_compl _ R hR hext


theorem fdc_leftExitIdx_succ_not_mem (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R + 1) ∉ cluster 2 ω (origin 2) :=
  fdc_leftRun_not_mem (ω := ω) hfin R hR (le_refl _)
    (Nat.succ_le_succ (fdc_leftExitIdx_le (ω := ω) hfin R))


theorem fdc_leftExit_adj (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    (hypercubicLattice 2).Adj (leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R))
      (leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R + 1)) := by
  set n := fdc_leftExitIdx (ω := ω) hfin R
  rw [leftAxisSite_eq n, leftAxisSite_succ_eq n]
  simp [hypercubicLattice_adj, Fin.sum_univ_two]



noncomputable def fdc_farLeftExitDart (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) : Dart where
  tail := leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R)
  head := leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R + 1)
  adj := fdc_leftExit_adj (ω := ω) hfin R

@[simp] theorem fdc_farLeftExitDart_tail (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    (fdc_farLeftExitDart (ω := ω) hfin R).tail
      = leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R) := rfl

@[simp] theorem fdc_farLeftExitDart_head (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    (fdc_farLeftExitDart (ω := ω) hfin R).head
      = leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R + 1) := rfl


theorem fdc_farLeftExitDart_isBoundaryDart (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    IsBoundaryDart (cluster 2 ω (origin 2)) (fdc_farLeftExitDart (ω := ω) hfin R) :=
  ⟨fdc_leftExitIdx_mem (ω := ω) hfin R, fdc_leftExitIdx_succ_not_mem (ω := ω) hfin R hR⟩



theorem fdc_leftAxis_reach (K : Set (Site 2)) (a j : ℕ)
    (hout : ∀ k, a ≤ k → k ≤ a + j → (leftAxisSite k : Site 2) ∉ K) :
    ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨leftAxisSite a, hout a le_rfl (by omega)⟩
      ⟨leftAxisSite (a + j), hout (a + j) (by omega) le_rfl⟩ := by
  induction j with
  | zero => exact Reachable.refl _
  | succ n ih =>
    have hout' : ∀ k, a ≤ k → k ≤ a + n → (leftAxisSite k : Site 2) ∉ K := by
      intro k h1 h2; exact hout k h1 (by omega)
    have h1 := ih hout'
    have hk1 : (leftAxisSite (a + n) : Site 2) ∉ K := hout (a + n) (by omega) (by omega)
    have hk2 : (leftAxisSite (a + n + 1) : Site 2) ∉ K := hout (a + n + 1) (by omega) (by omega)
    have hdiff : unitWt ((leftAxisSite (a + n) : Site 2) - leftAxisSite (a + n + 1)) = 1 := by
      unfold unitWt
      rw [Fin.sum_univ_two]
      have e0 : ((leftAxisSite (a + n) : Site 2) - leftAxisSite (a + n + 1)) 0 = 1 := by
        rw [leftAxisSite_succ_eq]
        simp [leftAxisSite, Pi.sub_apply]
      have e1 : ((leftAxisSite (a + n) : Site 2) - leftAxisSite (a + n + 1)) 1 = 0 := by
        rw [leftAxisSite_succ_eq]; simp [leftAxisSite, Pi.sub_apply]
      rw [e0, e1]; rfl
    have hstep := complReachable_of_unitDiff K hk1 hk2 hdiff
    have heq : (leftAxisSite (a + n + 1) : Site 2) = leftAxisSite (a + (n + 1)) := by
      have : a + n + 1 = a + (n + 1) := by omega
      rw [this]
    exact complReachable_congr (G := hypercubicLattice 2) (S := Kᶜ) rfl heq (h1.trans hstep)


theorem fdc_farLeftExitDart_head_reaches_axisFar (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨(fdc_farLeftExitDart (ω := ω) hfin R).head,
        (fdc_farLeftExitDart_isBoundaryDart (ω := ω) hfin R hR).2⟩
      ⟨leftAxisSite (R + 1), fdc_leftRun_not_mem (ω := ω) hfin R hR
        (Nat.succ_le_succ (fdc_leftExitIdx_le (ω := ω) hfin R)) (le_refl _)⟩ := by
  set n := fdc_leftExitIdx (ω := ω) hfin R with hn
  have hnR : n ≤ R := fdc_leftExitIdx_le (ω := ω) hfin R
  have hout : ∀ k, n + 1 ≤ k → k ≤ (n + 1) + (R - n) → (leftAxisSite k : Site 2)
      ∉ cluster 2 ω (origin 2) := by
    intro k hk1 hk2
    have hk2' : k ≤ R + 1 := by omega
    exact fdc_leftRun_not_mem (ω := ω) hfin R hR hk1 hk2'
  have hreach := fdc_leftAxis_reach (cluster 2 ω (origin 2)) (n + 1) (R - n) hout
  have heq : (leftAxisSite ((n + 1) + (R - n)) : Site 2) = leftAxisSite (R + 1) := by
    have : (n + 1) + (R - n) = R + 1 := by omega
    rw [this]
  exact complReachable_congr (G := hypercubicLattice 2) (S := (cluster 2 ω (origin 2))ᶜ)
    rfl heq hreach










theorem fdc_axisSite_eq_farRight (R : ℕ) : (axisSite (R + 1) : Site 2) = ![(R : ℤ) + 1, 0] := by
  funext i; fin_cases i <;> simp [axisSite]


theorem fdc_leftAxisSite_eq_farLeft (R : ℕ) :
    (leftAxisSite (R + 1) : Site 2) = ![-((R : ℤ) + 1), 0] := by
  rw [leftAxisSite_succ_eq]; funext i; fin_cases i <;> simp; ring






theorem fdc_farExitHeads_sameComponent (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨(fdc_farExitDart (ω := ω) hfin R).head,
        (fdc_farExitDart_isBoundaryDart (ω := ω) hfin R hR).2⟩
      ⟨(fdc_farLeftExitDart (ω := ω) hfin R).head,
        (fdc_farLeftExitDart_isBoundaryDart (ω := ω) hfin R hR).2⟩ := by
  
  have h1 := fdc_farExitDart_head_reaches_axisFar (ω := ω) hfin R hR
  
  have h2 := outC_axisFar_reachable (ω := ω) R hR
  
  have h3 := (fdc_farLeftExitDart_head_reaches_axisFar (ω := ω) hfin R hR).symm
  
  have h1' : ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨(fdc_farExitDart (ω := ω) hfin R).head,
        (fdc_farExitDart_isBoundaryDart (ω := ω) hfin R hR).2⟩
      ⟨(![(R : ℤ) + 1, 0] : Site 2), outC_axisFarRight_mem_compl (ω := ω) R hR⟩ :=
    complReachable_congr (G := hypercubicLattice 2) (S := (cluster 2 ω (origin 2))ᶜ)
      rfl (fdc_axisSite_eq_farRight R) h1
  have h3' : ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨(![-((R : ℤ) + 1), 0] : Site 2), outC_axisFarLeft_mem_compl (ω := ω) R hR⟩
      ⟨(fdc_farLeftExitDart (ω := ω) hfin R).head,
        (fdc_farLeftExitDart_isBoundaryDart (ω := ω) hfin R hR).2⟩ :=
    complReachable_congr (G := hypercubicLattice 2) (S := (cluster 2 ω (origin 2))ᶜ)
      (fdc_leftAxisSite_eq_farLeft R) rfl h3
  exact h1'.trans (h2.trans h3')











theorem fdc_farExitHeads_exterior (hfin : (cluster 2 ω (origin 2)).Finite) :
    outC_FarAxisHeadsFar ω hfin :=
  outC_farAxisHeadsFar_discharge (ω := ω) hfin














theorem fdc_farExitDartsSameOrbit (hfin : (cluster 2 ω (origin 2)).Finite)
    (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    ∃ n : ℕ, (dartNext (cluster 2 ω (origin 2)))^[n] (fdc_farExitDart (ω := ω) hfin R)
      = fdc_farLeftExitDart (ω := ω) hfin R :=
  hInt (fdc_farExitDart (ω := ω) hfin R) (fdc_farLeftExitDart (ω := ω) hfin R)
    (fdc_farExitDart_isBoundaryDart (ω := ω) hfin R hR)
    (fdc_farLeftExitDart_isBoundaryDart (ω := ω) hfin R hR)
    (fdc_farExitHeads_sameComponent (ω := ω) hfin R hR)












theorem fdc_sameOrbit_symm (K : Set (Site 2)) (hK : K.Finite) (e f : Dart)
    (he : IsBoundaryDart K e) {n : ℕ} (hn : (dartNext K)^[n] e = f) :
    ∃ m : ℕ, (dartNext K)^[m] f = e := by
  obtain ⟨p, hp, hper⟩ := dartNext_periodic K hK e he
  refine ⟨p * (n + 1) - n, ?_⟩
  rw [← hn, ← Function.iterate_add_apply]
  have hmn : p * (n + 1) - n + n = p * (n + 1) := by
    have : n ≤ p * (n + 1) := by nlinarith [hp]
    omega
  rw [hmn, Function.iterate_mul]
  have : (fun x => (dartNext K)^[p] x)^[n + 1] e = e := Function.iterate_fixed hper (n + 1)
  simpa using this


theorem fdc_sameOrbit_trans (K : Set (Site 2)) (e f g : Dart)
    {a b : ℕ} (ha : (dartNext K)^[a] e = f) (hb : (dartNext K)^[b] f = g) :
    ∃ c : ℕ, (dartNext K)^[c] e = g := by
  refine ⟨b + a, ?_⟩
  rw [Function.iterate_add_apply, ha, hb]










def fdc_FarReanchors (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) : Prop :=
  (∃ a : ℕ, (dartNext (cluster 2 ω (origin 2)))^[a] (exitDart (ω := ω) hfin)
      = fdc_farExitDart (ω := ω) hfin R) ∧
  (∃ b : ℕ, (dartNext (cluster 2 ω (origin 2)))^[b] (fdc_farLeftExitDart (ω := ω) hfin R)
      = leftExitDart (ω := ω) hfin)








theorem fdc_exitDartsSameOrbit (hfin : (cluster 2 ω (origin 2)).Finite)
    (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
    (hre : fdc_FarReanchors ω hfin R) :
    ExitDartsSameOrbit ω hfin := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hre
  obtain ⟨c, hc⟩ := fdc_farExitDartsSameOrbit (ω := ω) hfin hInt R hR
  
  obtain ⟨d, hd⟩ := fdc_sameOrbit_trans (cluster 2 ω (origin 2))
    (exitDart (ω := ω) hfin) (fdc_farExitDart (ω := ω) hfin R)
    (fdc_farLeftExitDart (ω := ω) hfin R) ha hc
  exact fdc_sameOrbit_trans (cluster 2 ω (origin 2))
    (exitDart (ω := ω) hfin) (fdc_farLeftExitDart (ω := ω) hfin R)
    (leftExitDart (ω := ω) hfin) hd hb












theorem fdc_pc_lt_one
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        OrbitFaceSimple ω hfin ∧ InterfaceConnected (cluster 2 ω (origin 2)) ∧
          ∃ R : ℕ, cluster 2 ω (origin 2) ⊆ box 2 R ∧ fdc_FarReanchors ω hfin R) :
    (StatMech.Percolation.pc 2 : ℝ) < 1 := by
  apply pc_lt_one_of_orbitFaceSimple
  intro ω hfin
  obtain ⟨hsimple, hInt, R, hR, hre⟩ := h ω hfin
  exact ⟨hsimple, fdc_exitDartsSameOrbit (ω := ω) hfin hInt R hR hre⟩

















































