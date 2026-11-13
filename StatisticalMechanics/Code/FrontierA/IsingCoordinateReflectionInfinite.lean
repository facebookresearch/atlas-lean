/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingCoordinateReflectionCauchy
import Code.FrontierA.IsingCriticalTwoPointShell

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation StatMech.FrontierB

variable {d : Nat}

private theorem freeDomainSpinSupport_pair_eq
    (K : Finset (Site d)) (a b : Site d) (ha : a ∈ K) (hb : b ∈ K) :
    freeDomainSpinSupport K {a, b} =
      ({(⟨a, ha⟩ : freeDomainVertices K),
        (⟨b, hb⟩ : freeDomainVertices K)} :
        Finset (freeDomainVertices K)) := by
  ext z
  simp only [freeDomainSpinSupport, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (hz | hz)
    · left
      exact Subtype.ext hz
    · right
      exact Subtype.ext hz
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

private theorem spinProd_freeDomainSpinSupport_pair
    (K : Finset (Site d)) (a b : Site d) (ha : a ∈ K) (hb : b ∈ K)
    (hab : a ≠ b) (sigma : ConfigSpace (freeDomainVertices K)) :
    spinProd (freeDomainSpinSupport K {a, b}) sigma =
      spin sigma (⟨a, ha⟩ : freeDomainVertices K) *
        spin sigma (⟨b, hb⟩ : freeDomainVertices K) := by
  rw [freeDomainSpinSupport_pair_eq K a b ha hb, spinProd,
    Finset.prod_pair]
  intro h
  exact hab (congrArg Subtype.val h)

private theorem coordinateAxisSite_ne_origin
    (i : Fin d) (n : Nat) (hn : 1 <= n) :
    (Pi.single i (n : Int) : Site d) ≠ Percolation.origin d := by
  intro h
  have hi := congrFun h i
  simp [Percolation.origin] at hi
  omega

private theorem exists_natAbs_coordinate_eq_of_shell
    {n : Nat} (hn : 1 <= n) (x : Site d) (hx : x ∈ boxSV_vbF d n) :
    ∃ i : Fin d, (x i).natAbs = n := by
  classical
  rw [boxSV_vbF, Finset.mem_sdiff] at hx
  have hin : x ∈ box d n := by
    rw [← boxSV_coe_boxF]
    exact hx.1
  by_contra h
  push Not at h
  apply hx.2
  have hinner : x ∈ box d (n - 1) := by
    intro i
    have hle := hin i
    have hne := h i
    omega
  change x ∈ (boxSV_boxF d (n - 1) : Set (Site d))
  rw [boxSV_coe_boxF]
  exact hinner




theorem currentContinuityFreeTwoPoint_le_axis_of_coordinate_eq
    (i : Fin d) (beta : Real) (hbeta : 0 <= beta)
    (x : Site d) (n : Nat) (hn : 1 <= n) (hxi : x i = (n : Int)) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d) x <=
      currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single i (n : Int)) := by
  let o : Site d := Percolation.origin d
  let axis : Site d := Pi.single i (n : Int)
  let b : Site d := Function.update x i 0
  let m : Int := n
  have hoAxis : o ≠ axis := by
    exact (coordinateAxisSite_ne_origin i n hn).symm
  have hox : o ≠ x := by
    intro h
    have hi := congrFun h i
    simp [o, Percolation.origin, hxi] at hi
    omega
  have hbx : b ≠ x := by
    intro h
    have hi := congrFun h i
    simp [b, hxi] at hi
    omega
  have hreflectO : isingCoordinateReflect i m o = axis := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [m, o, axis, Percolation.origin]
    · simp [isingCoordinateReflect_apply_of_ne i j hji, o, axis,
        Percolation.origin, hji]
  have hreflectB : isingCoordinateReflect i m b = x := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [m, b, hxi]
    · simp [isingCoordinateReflect_apply_of_ne i j hji, b,
        Function.update_of_ne hji]
  let A : Finset (Site d) := {o, x}
  let Aaxis : Finset (Site d) := {o, axis}
  let Ab : Finset (Site d) := {b, x}
  let S : Finset (Site d) := {o, x, b, axis}
  obtain ⟨N, hSN⟩ := Lattice.finite_subset_box
    (↑S : Set (Site d)) S.finite_toSet
  have hlim : Tendsto
      (fun r => ∫ omega, spinProd A omega
        ∂(freeMeasure d r beta 0 : Measure (ConfigSpace (Site d))))
      atTop
      (nhds (∫ omega, spinProd A omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) :=
    integral_freeMeasure_spinProd_tendsto_freeState d beta hbeta A
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop N] with r hr
  let B := Ising.boxFinset d r
  let K := isingCoordinateSymmetricHull B i m
  have hSbox : S ⊆ B := by
    intro z hz
    rw [Ising.mem_boxFinset]
    exact box_mono d hr (hSN hz)
  have hoB : o ∈ B := hSbox (by simp [S])
  have hxB : x ∈ B := hSbox (by simp [S])
  have hbB : b ∈ B := hSbox (by simp [S])
  have haxisB : axis ∈ B := hSbox (by simp [S])
  have hBK : B ⊆ K := subset_isingCoordinateSymmetricHull B i m
  have hoK : o ∈ K := hBK hoB
  have hxK : x ∈ K := hBK hxB
  have hbK : b ∈ K := hBK hbB
  have haxisK : axis ∈ K := hBK haxisB
  have hA_B : A ⊆ B := by
    intro z hz
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hoB
    · exact hxB
  have hA_K : A ⊆ K := hA_B.trans hBK
  have hAaxis_K : Aaxis ⊆ K := by
    intro z hz
    simp only [Aaxis, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hoK
    · exact haxisK
  have hAb_K : Ab ⊆ K := by
    intro z hz
    simp only [Ab, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hbK
    · exact hxK
  have hK : forall z : Site d,
      z ∈ K ↔ isingCoordinateReflect i m z ∈ K :=
    mem_isingCoordinateSymmetricHull_reflect_iff B i m
  let oK : freeDomainVertices K := ⟨o, hoK⟩
  let bK : freeDomainVertices K := ⟨b, hbK⟩
  let xK : freeDomainVertices K := ⟨x, hxK⟩
  let axisK : freeDomainVertices K := ⟨axis, haxisK⟩
  have hoLower : isingCoordinateDomainLower K i m oK := by
    unfold isingCoordinateDomainLower isingCoordinateLower
    simp [oK, o, m, Percolation.origin]
    omega
  have hbLower : isingCoordinateDomainLower K i m bK := by
    unfold isingCoordinateDomainLower isingCoordinateLower
    simp [bK, b, m]
    omega
  let oL : IsingCoordinateDomainLower K i m := ⟨oK, hoLower⟩
  let bL : IsingCoordinateDomainLower K i m := ⟨bK, hbLower⟩
  have hreflectOK : isingCoordinateDomainReflectEquiv K i m hK oK = axisK := by
    exact Subtype.ext hreflectO
  have hreflectBK : isingCoordinateDomainReflectEquiv K i m hK bK = xK := by
    exact Subtype.ext hreflectB
  have hcauchy := isingCoordinateDomain_twoPoint_reflection_cauchy
    K i m hK beta hbeta oL bL
  dsimp only [oL, bL] at hcauchy
  rw [hreflectOK, hreflectBK] at hcauchy
  change isingExpectation (freeDomainGraph K) beta 0
      (fun sigma => spin sigma oK * spin sigma xK) ^ 2 <=
    isingExpectation (freeDomainGraph K) beta 0
        (fun sigma => spin sigma oK * spin sigma axisK) *
      isingExpectation (freeDomainGraph K) beta 0
        (fun sigma => spin sigma bK * spin sigma xK) at hcauchy
  let qcross := isingExpectation (freeDomainGraph K) beta 0
    (spinProd (freeDomainSpinSupport K A))
  let qaxis := isingExpectation (freeDomainGraph K) beta 0
    (spinProd (freeDomainSpinSupport K Aaxis))
  let qb := isingExpectation (freeDomainGraph K) beta 0
    (spinProd (freeDomainSpinSupport K Ab))
  have hcrossEq : qcross = isingExpectation (freeDomainGraph K) beta 0
      (fun sigma => spin sigma oK * spin sigma xK) := by
    unfold qcross isingExpectation
    apply Finset.sum_congr rfl
    intro sigma _
    rw [spinProd_freeDomainSpinSupport_pair K o x hoK hxK hox sigma]
  have haxisEq : qaxis = isingExpectation (freeDomainGraph K) beta 0
      (fun sigma => spin sigma oK * spin sigma axisK) := by
    unfold qaxis isingExpectation
    apply Finset.sum_congr rfl
    intro sigma _
    rw [spinProd_freeDomainSpinSupport_pair K o axis hoK haxisK hoAxis sigma]
  have hbEq : qb = isingExpectation (freeDomainGraph K) beta 0
      (fun sigma => spin sigma bK * spin sigma xK) := by
    unfold qb isingExpectation
    apply Finset.sum_congr rfl
    intro sigma _
    rw [spinProd_freeDomainSpinSupport_pair K b x hbK hxK hbx sigma]
  rw [← hcrossEq, ← haxisEq, ← hbEq] at hcauchy
  let qinf := ∫ omega, spinProd Aaxis omega
    ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))
  have hqaxis : qaxis <= qinf :=
    freeDomain_spinProd_le_freeState K beta hbeta Aaxis hAaxis_K
  have hqbToInf : qb <= ∫ omega, spinProd Ab omega
      ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) :=
    freeDomain_spinProd_le_freeState K beta hbeta Ab hAb_K
  let g : Multiplicative (Site d) := Multiplicative.ofAdd (-b)
  have hgo : g • b = o := by
    funext j
    simp [g, o, Percolation.origin, smul_site_apply]
  have hgx : g • x = axis := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [g, b, axis, hxi, smul_site_apply]
    · simp [g, b, axis, hji, smul_site_apply]
  have htranslate : ∫ omega, spinProd Ab omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) = qinf := by
    have h := integral_freeState_spinProd_translate d beta hbeta g Ab
    have himage : Ab.image (fun z => g • z) = Aaxis := by
      simp [Ab, Aaxis, hgo, hgx]
    rw [himage] at h
    exact h.symm
  rw [htranslate] at hqbToInf
  have hqcrossNonneg : 0 <= qcross := by
    exact gks_first (freeDomainGraph K) beta 0 hbeta le_rfl
      (freeDomainSpinSupport K A)
  have hqaxisNonneg : 0 <= qaxis := by
    exact gks_first (freeDomainGraph K) beta 0 hbeta le_rfl
      (freeDomainSpinSupport K Aaxis)
  have hqbNonneg : 0 <= qb := by
    exact gks_first (freeDomainGraph K) beta 0 hbeta le_rfl
      (freeDomainSpinSupport K Ab)
  have hqinfNonneg : 0 <= qinf := hqaxisNonneg.trans hqaxis
  have hqcrossInf : qcross <= qinf := by
    nlinarith
  calc
    (∫ omega, spinProd A omega
        ∂(freeMeasure d r beta 0 : Measure (ConfigSpace (Site d)))) =
        isingExpectation (freeDomainGraph B) beta 0
          (spinProd (freeDomainSpinSupport B A)) :=
      integral_freeMeasure_spinProd_eq_freeDomain d r beta A hA_B
    _ <= qcross := by
      exact freeDomain_spinProd_mono hBK beta hbeta A hA_B
    _ <= qinf := hqcrossInf
    _ = currentContinuityFreeTwoPoint d beta (Percolation.origin d) axis := by
      rfl


theorem currentContinuityFreeTwoPoint_le_axis_of_natAbs_coordinate
    (i : Fin d) (beta : Real) (hbeta : 0 <= beta)
    (x : Site d) (n : Nat) (hn : 1 <= n) (hxi : (x i).natAbs = n) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d) x <=
      currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (Pi.single i (n : Int)) := by
  cases hcoord : x i with
  | ofNat r =>
      have hr : r = n := by simpa [hcoord] using hxi
      subst r
      exact currentContinuityFreeTwoPoint_le_axis_of_coordinate_eq
        i beta hbeta x n hn (by simp [hcoord])
  | negSucc r =>
      let y := isingCoordinateNegate i x
      have hyn : y i = (n : Int) := by
        dsimp only [y]
        rw [isingCoordinateNegate_apply_same, hcoord]
        have hr : r + 1 = n := by simpa [hcoord] using hxi
        omega
      have hy := currentContinuityFreeTwoPoint_le_axis_of_coordinate_eq
        i beta hbeta y n hn hyn
      have heq := currentContinuityFreeTwoPoint_coordinateNegate
        i beta hbeta x
      exact heq.symm.trans_le hy



theorem currentContinuityFreeTwoPoint_shell_le_axis
    (hd : 1 <= d) (beta : Real) (hbeta : 0 <= beta)
    (n : Nat) (hn : 1 <= n) (x : Site d) (hx : x ∈ boxSV_vbF d n) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d) x <=
      currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (criticalAxisSite hd n) := by
  obtain ⟨i, hi⟩ := exists_natAbs_coordinate_eq_of_shell hn x hx
  have haxis := currentContinuityFreeTwoPoint_le_axis_of_natAbs_coordinate
    i beta hbeta x n hn hi
  let j : Fin d := ⟨0, hd⟩
  have hcritical : (Pi.single j (n : Int) : Site d) =
      criticalAxisSite hd n := by
    funext a
    by_cases ha : a = j
    · subst a
      simp [j, criticalAxisSite]
    · simp [j, criticalAxisSite, ha]
  by_cases hij : i = j
  · subst i
    rw [hcritical] at haxis
    exact haxis
  · have hsymm := currentContinuityFreeTwoPoint_coordinateSwap
      i j hij beta hbeta (Pi.single i (n : Int))
    have hreflect : isingDiagonalReflect i j 0
        (Pi.single i (n : Int) : Site d) = Pi.single j (n : Int) := by
      funext a
      by_cases hai : a = i
      · subst a
        simp [hij, Ne.symm hij]
      · by_cases haj : a = j
        · subst a
          simp [hij]
        · rw [isingDiagonalReflect_apply_of_ne i j a hai haj]
          simp [hai, haj]
    rw [hreflect] at hsymm
    have hresult := haxis.trans_eq hsymm.symm
    rw [hcritical] at hresult
    exact hresult

end StatMech.FrontierA
