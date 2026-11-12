/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalGhostEnergy









namespace StatMech.Universality

open Finset

noncomputable section



theorem fkIsingSquareRadialPatchPhysicalNormalizedWindow_energy_le_deepCell
    (n m baseI baseJ R : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (r : Nat)
    (hdeep : ∀ p : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r) :
    mesh ^ 2 *
        ∑ p : IsingLeapfrogBox R,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservableWindow
                n m baseI baseJ R hn hm hfitI hfitJ p /
              (Real.sqrt (2 * mesh) : Complex)) ≤
      mesh ^ 2 *
        ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
                ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
              (Real.sqrt (2 * mesh) : Complex)) := by
  classical
  let cell := fkIsingSquareRadialPatchWindowCell
    m baseI baseJ R hfitI hfitJ
  let C := fkIsingSquareRadialPatchDeepCells n m hm hm2 r
  let energy := fun c : FKIsingSquareRadialPatchInteriorCell m ↦
    Complex.normSq
      (fkIsingSquareRadialPatchFullObservable n m hn hm
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
  have hscaled := mul_le_mul_of_nonneg_left hsum (sq_nonneg mesh)
  simpa [cell, C, energy,
    fkIsingSquareRadialPatchFullObservableWindow,
    fkIsingSquareRadialPatchWindowCell] using hscaled




theorem fkIsingSquareRadialPatchPhysicalNormalizedWindow_average_normSq_le
    (n m baseI baseJ R r : Nat) (K Q base : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m) (hr : 0 < r)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hmr : (m : Real) ≤ K * (r : Real))
    (hmR : (m : Real) ≤ Q * (R + 1 : Nat))
    (hdeep : ∀ p : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (hprimalLower : ∀ p, 0 ≤
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base p)
    (hdualUpper : ∀ q,
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base q ≤ 1) :
    (∑ p : IsingLeapfrogBox R,
        Complex.normSq
          (fkIsingSquareRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p /
            (Real.sqrt (2 * (1 / (m : Real))) : Complex))) ≤
      (Fintype.card (IsingLeapfrogBox R) : Real) * (16 * K * Q ^ 2) := by
  let W : Real := ∑ p : IsingLeapfrogBox R,
    Complex.normSq
      (fkIsingSquareRadialPatchFullObservableWindow
          n m baseI baseJ R hn hm hfitI hfitJ p /
        (Real.sqrt (2 * (1 / (m : Real))) : Complex))
  let G : Real := (1 / (m : Real)) ^ 2 *
    ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
      Complex.normSq
        (fkIsingSquareRadialPatchFullObservable n m hn hm
            ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
          (Real.sqrt (2 * (1 / (m : Real))) : Complex))
  have hmesh : 0 < 1 / (m : Real) := by positivity
  have hwindow : (1 / (m : Real)) ^ 2 * W ≤ G := by
    exact fkIsingSquareRadialPatchPhysicalNormalizedWindow_energy_le_deepCell
      n m baseI baseJ R (1 / (m : Real)) hn hm hm2 hfitI hfitJ r hdeep
  have hglobalSq : G ^ 2 ≤ 256 * K ^ 2 := by
    exact
      fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_sq_le_fixedFraction
        n m hn hm hm2 r hr base K hK hmr hprimalLower hdualUpper
  have hGnonneg : 0 ≤ G := by
    dsimp only [G]
    apply mul_nonneg (sq_nonneg _)
    apply Finset.sum_nonneg
    intro c hc
    exact Complex.normSq_nonneg _
  have hglobal : G ≤ 16 * K := by
    apply (sq_le_sq₀ hGnonneg (mul_nonneg (by norm_num) hK)).mp
    calc
      G ^ 2 ≤ 256 * K ^ 2 := hglobalSq
      _ = (16 * K) ^ 2 := by ring
  have hwindowBound : (1 / (m : Real)) ^ 2 * W ≤ 16 * K :=
    hwindow.trans hglobal
  have hmR' : (m : Real) ≤ Q * ((R + 1 : Nat) : Real) := by
    exact_mod_cast hmR
  have hmRsq : (m : Real) ^ 2 ≤
      (Q * ((R + 1 : Nat) : Real)) ^ 2 :=
    (sq_le_sq₀ (by positivity)
      (mul_nonneg hQ (by positivity))).2 hmR'
  change W ≤ _
  calc
    W = (m : Real) ^ 2 * ((1 / (m : Real)) ^ 2 * W) := by
      field_simp
    _ ≤ (m : Real) ^ 2 * (16 * K) :=
      mul_le_mul_of_nonneg_left hwindowBound (sq_nonneg _)
    _ ≤ (Q * ((R + 1 : Nat) : Real)) ^ 2 * (16 * K) :=
      mul_le_mul_of_nonneg_right hmRsq (mul_nonneg (by norm_num) hK)
    _ = (Fintype.card (IsingLeapfrogBox R) : Real) *
        (16 * K * Q ^ 2) := by
      simp [Fintype.card_prod]
      ring

end

end StatMech.Universality
