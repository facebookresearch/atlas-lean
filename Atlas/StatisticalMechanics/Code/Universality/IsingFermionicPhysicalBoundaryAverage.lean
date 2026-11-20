/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalBoundaryRadialEnergy
import Code.Universality.IsingFermionicPhysicalBoundaryDistance
import Code.Universality.IsingFermionicSquareWindowRealization










namespace StatMech.Universality

open Finset

noncomputable section



theorem fkIsingSquareRadialPatchWindowCell_mem_deepCells_of_margin
    (n m baseI baseJ R r : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hleft : r ≤ baseI) (hbottom : r ≤ baseJ)
    (hright : baseI + R + 1 + r < m)
    (htop : baseJ + R + 1 + r < m)
    (p : IsingLeapfrogBox R) :
    fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈
      fkIsingSquareRadialPatchDeepCells n m hm hm2 r := by
  classical
  rw [fkIsingSquareRadialPatchDeepCells, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rw [fkIsingSquareRadialPatchPrimalDeepDarts, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    apply fkIsingSquareRadialPatchPrimalBoundaryDistance_ge_of_coordinate_margin
      n m r hm hm2
    all_goals
      by_cases h : Even ((baseI + p.1.1) + (baseJ + p.2.1)) <;>
        simp [fkIsingSquareRadialPatchCellPrimalDart,
          fkIsingSquareRadialPatchCellPrimalHead, h,
          fkIsingSquareRadialPatchWindowCell] <;> omega
  · rw [fkIsingSquareRadialPatchDualDeepDarts, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    apply fkIsingSquareRadialPatchDualBoundaryDistance_ge_of_coordinate_margin
      m r hm2
    all_goals
      by_cases h : Even ((baseI + p.1.1) + (baseJ + p.2.1)) <;>
        simp [fkIsingSquareRadialPatchCellDualDart,
          fkIsingSquareRadialPatchCellDualHead, h,
          fkIsingSquareRadialPatchWindowCell] <;> omega



theorem fkIsingSquareBoundaryRadialPatchNormalizedWindow_energy_le_deepCell
    (n m baseI baseJ R : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (r : Nat)
    (hdeep : ∀ p : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r) :
    (∑ p : IsingLeapfrogBox R,
        Complex.normSq
          (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
              ⟨baseI + p.1.1, by have := p.1.2; omega⟩
              ⟨baseJ + p.2.1, by have := p.2.2; omega⟩ /
            (Real.sqrt (2 * mesh) : Complex))) ≤
      ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
        Complex.normSq
          (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
              ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
            (Real.sqrt (2 * mesh) : Complex)) := by
  classical
  let cell := fkIsingSquareRadialPatchWindowCell
    m baseI baseJ R hfitI hfitJ
  let C := fkIsingSquareRadialPatchDeepCells n m hm hm2 r
  let energy := fun c : FKIsingSquareRadialPatchInteriorCell m ↦
    Complex.normSq
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
          ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
        (Real.sqrt (2 * mesh) : Complex))
  have himage : Finset.univ.image cell ⊆ C := by
    intro c hc
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hc
    exact hdeep p
  have hsum : (∑ p : IsingLeapfrogBox R, energy (cell p)) ≤
      ∑ c ∈ C, energy c := by
    rw [← Finset.sum_image
      (fkIsingSquareRadialPatchWindowCell_injective
        m baseI baseJ R hfitI hfitJ).injOn]
    exact Finset.sum_le_sum_of_subset_of_nonneg himage
      (fun c _ _ ↦ Complex.normSq_nonneg _)
  simpa [cell, C, energy, fkIsingSquareRadialPatchWindowCell] using hsum




theorem fkIsingSquareBoundaryRadialPatch_deepCell_normalizedEnergy_le
    (n m r : Nat) (K : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) (hr : 0 < r)
    (hmr : (m : Real) ≤ K * (r : Real)) :
    (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
        Complex.normSq
          (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
              ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
            (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ≤
      16 * K * (m : Real) ^ 2 := by
  let Sp := fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r
  let Sd := fkIsingSquareRadialPatchDualDeepDarts m hm2 r
  let Vp : Real := ∑ d ∈ Sp,
    |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
          n m hn hm d.snd -
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchPrimalValue
          n m hn hm d.fst|
  let Vd : Real := ∑ d ∈ Sd,
    |FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
          n m hn hm hm2 d.snd -
      FKIsingSquareBoundaryLayerCoordinateOneForm.radialPatchDualValue
          n m hn hm hm2 d.fst|
  have hVp0 : 0 ≤ Vp := by
    dsimp only [Vp]
    positivity
  have hVd0 : 0 ≤ Vd := by
    dsimp only [Vd]
    positivity
  have hscaledVp0 : 0 ≤ (1 / (m : Real)) * Vp := mul_nonneg (by positivity) hVp0
  have hscaledVd0 : 0 ≤ (1 / (m : Real)) * Vd := mul_nonneg (by positivity) hVd0
  have hbound0 : 0 ≤ 8 * (m : Real) / (r : Real) := by positivity
  have hVpSq : ((1 / (m : Real)) * Vp) ^ 2 ≤
      (8 * (m : Real) / (r : Real)) ^ 2 := by
    change ((1 / (m : Real)) * Vp) ^ 2 ≤ _
    calc
      _ ≤ 64 * (m : Real) ^ 2 / (r : Real) ^ 2 :=
        fkIsingSquareBoundaryRadialPatchPrimal_physicalDeepVariation_sq_le
          n m hn hm hm2 r hr
      _ = (8 * (m : Real) / (r : Real)) ^ 2 := by ring
  have hVdSq : ((1 / (m : Real)) * Vd) ^ 2 ≤
      (8 * (m : Real) / (r : Real)) ^ 2 := by
    change ((1 / (m : Real)) * Vd) ^ 2 ≤ _
    calc
      _ ≤ 64 * (m : Real) ^ 2 / (r : Real) ^ 2 :=
        fkIsingSquareBoundaryRadialPatchDual_physicalDeepVariation_sq_le
          n m hn hm hm2 r hr
      _ = (8 * (m : Real) / (r : Real)) ^ 2 := by ring
  have hVp : (1 / (m : Real)) * Vp ≤ 8 * (m : Real) / (r : Real) :=
    (sq_le_sq₀ hscaledVp0 hbound0).mp hVpSq
  have hVd : (1 / (m : Real)) * Vd ≤ 8 * (m : Real) / (r : Real) :=
    (sq_le_sq₀ hscaledVd0 hbound0).mp hVdSq
  have hraw :
      (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
              ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩)) ≤
        2 * (Vp + Vd) := by
    simpa [Sp, Sd, Vp, Vd] using
      fkIsingSquareBoundaryRadialPatch_deepCell_normSq_sum_le_variation
        n m hn hm hm2 r
  have hsqrt : 0 < Real.sqrt (2 * (1 / (m : Real))) :=
    Real.sqrt_pos.2 (by positivity)
  have hnorm (z : Complex) :
      Complex.normSq
          (z / (Real.sqrt (2 * (1 / (m : Real))) : Complex)) =
        (m : Real) / 2 * Complex.normSq z := by
    have hden :
        Complex.normSq
            ((Real.sqrt (2 * (1 / (m : Real))) : Real) : Complex) =
          2 * (1 / (m : Real)) := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hsqrt, Real.sq_sqrt (by positivity)]
    rw [Complex.normSq_div]
    rw [hden]
    field_simp
  simp_rw [hnorm, ← Finset.mul_sum]
  calc
    (m : Real) / 2 *
        (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
              ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩)) ≤
      (m : Real) / 2 * (2 * (Vp + Vd)) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = (m : Real) ^ 2 *
        ((1 / (m : Real)) * Vp + (1 / (m : Real)) * Vd) := by
      field_simp
    _ ≤ (m : Real) ^ 2 *
        (16 * (m : Real) / (r : Real)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      calc
        (1 / (m : Real)) * Vp + (1 / (m : Real)) * Vd ≤
            8 * (m : Real) / (r : Real) +
              8 * (m : Real) / (r : Real) := add_le_add hVp hVd
        _ = 16 * (m : Real) / (r : Real) := by ring
    _ ≤ (m : Real) ^ 2 * (16 * K) := by
      gcongr
      apply (div_le_iff₀' (by positivity : (0 : Real) < r)).2
      nlinarith
    _ = 16 * K * (m : Real) ^ 2 := by ring



theorem fkIsingSquareBoundaryRadialPatchNormalizedWindow_average_normSq_le
    (n m baseI baseJ R r : Nat) (K Q : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) (hr : 0 < r)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hmr : (m : Real) ≤ K * (r : Real))
    (hmR : (m : Real) ≤ Q * (R + 1 : Nat))
    (hdeep : ∀ p : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r) :
    (∑ p : IsingLeapfrogBox R,
        Complex.normSq
          (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
              ⟨baseI + p.1.1, by have := p.1.2; omega⟩
              ⟨baseJ + p.2.1, by have := p.2.2; omega⟩ /
            (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ≤
      (Fintype.card (IsingLeapfrogBox R) : Real) * (16 * K * Q ^ 2) := by
  have hwindow :=
    fkIsingSquareBoundaryRadialPatchNormalizedWindow_energy_le_deepCell
      n m baseI baseJ R (1 / (m : Real)) hn hm hm2 hfitI hfitJ r hdeep
  have hglobal := fkIsingSquareBoundaryRadialPatch_deepCell_normalizedEnergy_le
    n m r K hn hm hm2 hr hmr
  have htotal := hwindow.trans hglobal
  have hmR' : (m : Real) ≤ Q * ((R + 1 : Nat) : Real) := by
    exact_mod_cast hmR
  have hmRsq : (m : Real) ^ 2 ≤
      (Q * ((R + 1 : Nat) : Real)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (mul_nonneg hQ (by positivity))).2 hmR'
  calc
    _ ≤ 16 * K * (m : Real) ^ 2 := htotal
    _ ≤ 16 * K * (Q * ((R + 1 : Nat) : Real)) ^ 2 := by
      gcongr
    _ = (Fintype.card (IsingLeapfrogBox R) : Real) *
        (16 * K * Q ^ 2) := by
      simp [Fintype.card_prod]
      ring



theorem normalizedFermionicObservable_normSq_anti_mesh
    (z : Complex) {mesh₀ mesh : Real}
    (hmesh₀ : 0 < mesh₀) (hle : mesh₀ ≤ mesh) :
    Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) ≤
      Complex.normSq (z / (Real.sqrt (2 * mesh₀) : Complex)) := by
  have hmesh : 0 < mesh := hmesh₀.trans_le hle
  have hsqrt₀ : 0 < Real.sqrt (2 * mesh₀) := Real.sqrt_pos.2 (by positivity)
  have hsqrt : 0 < Real.sqrt (2 * mesh) := Real.sqrt_pos.2 (by positivity)
  have hnorm (w : Complex) (t : Real) (ht : 0 < t)
      (hsqrt : 0 < Real.sqrt (2 * t)) :
      Complex.normSq (w / (Real.sqrt (2 * t) : Complex)) =
        Complex.normSq w / (2 * t) := by
    rw [Complex.normSq_div]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsqrt, Real.sq_sqrt (by positivity)]
  rw [hnorm z mesh hmesh hsqrt, hnorm z mesh₀ hmesh₀ hsqrt₀]
  exact div_le_div_of_nonneg_left (Complex.normSq_nonneg z) (by positivity)
    (mul_le_mul_of_nonneg_left hle (by norm_num))



theorem fkIsingSquareBoundaryRadialPatchWindowCarrier_average_normSq_le
    (n m baseI baseJ R r : Nat) (mesh K Q : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) (hr : 0 < r)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (hmeshLower : 1 / (m : Real) ≤ mesh)
    (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hmr : (m : Real) ≤ K * (r : Real))
    (hmR : (m : Real) ≤ Q * (R + 1 : Nat))
    (hdeep : ∀ p : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r) :
    (∑ a ∈ Finset.univ.map
          (fkIsingSquareRadialPatchWindowCarrierEmbedding
            n m baseI baseJ R hm hfitI hfitJ),
        Complex.normSq
          ((fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).normalizedFermionicObservable
            mesh a)) ≤
      ((Finset.univ.map
          (fkIsingSquareRadialPatchWindowCarrierEmbedding
            n m baseI baseJ R hm hfitI hfitJ)).card : Real) *
        (16 * K * Q ^ 2) := by
  let window := fkIsingSquareRadialPatchWindowCarrierEmbedding
    n m baseI baseJ R hm hfitI hfitJ
  let abstract := fun a : FKIsingSquareWiredCarrier n ↦
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).normalizedFermionicObservable
      mesh a
  let concrete := fun p : IsingLeapfrogBox R ↦ abstract (window p)
  have hmesh₀ : 0 < 1 / (m : Real) := by positivity
  have hpointwise (p : IsingLeapfrogBox R) :
      Complex.normSq (concrete p) ≤
        Complex.normSq
          (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
              ⟨baseI + p.1.1, by have := p.1.2; omega⟩
              ⟨baseJ + p.2.1, by have := p.2.2; omega⟩ /
            (Real.sqrt (2 * (1 / (m : Real))) : Complex)) := by
    calc
      Complex.normSq (concrete p) ≤
          Complex.normSq
            (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
                ⟨baseI + p.1.1, by have := p.1.2; omega⟩
                ⟨baseJ + p.2.1, by have := p.2.2; omega⟩ /
              (Real.sqrt (2 * mesh) : Complex)) := by
        exact fkIsingSquareBoundaryRadialPatchWindowCarrier_normalized_normSq_le
          n m baseI baseJ R mesh hn hm hfitI hfitJ hmesh p
      _ ≤ _ := normalizedFermionicObservable_normSq_anti_mesh _ hmesh₀ hmeshLower
  have hfull :=
    fkIsingSquareBoundaryRadialPatchNormalizedWindow_average_normSq_le
      n m baseI baseJ R r K Q hn hm hm2 hr hfitI hfitJ hK hQ
      hmr hmR hdeep
  have haverage :
      (∑ p : IsingLeapfrogBox R, Complex.normSq (concrete p)) ≤
        (Fintype.card (IsingLeapfrogBox R) : Real) * (16 * K * Q ^ 2) :=
    (Finset.sum_le_sum fun p _ ↦ hpointwise p).trans hfull
  exact finiteWindow_average_normSq_le_of_embedding
    window concrete abstract (16 * K * Q ^ 2) (fun _ ↦ rfl) haverage

end

end StatMech.Universality
