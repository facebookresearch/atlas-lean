/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicFiniteBoundaryCutoff
import Code.Universality.IsingFermionicPhysicalCaccioppoli









namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

theorem fkIsingSquareRadialPatchPrimalBoundary_nonempty
    (m : Nat) (hm : 0 < m) :
    ∃ p : FKIsingSquareRadialPatchPrimalNode m,
      fkIsingSquareRadialPatchPrimalBoundary m p := by
  let p : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨0, hm⟩, ⟨0, hm⟩), by norm_num⟩
  exact ⟨p, by simp [p, fkIsingSquareRadialPatchPrimalBoundary]⟩

theorem fkIsingSquareRadialPatchDualBoundary_nonempty
    (m : Nat) (hm : 2 ≤ m) :
    ∃ p : FKIsingSquareRadialPatchDualNode m,
      fkIsingSquareRadialPatchDualBoundary m p := by
  let p : FKIsingSquareRadialPatchDualNode m :=
    ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by norm_num⟩
  exact ⟨p, by simp [p, fkIsingSquareRadialPatchDualBoundary]⟩

noncomputable def fkIsingSquareRadialPatchPrimalBoundaryDistance
    (n m : Nat) (hm : m ≤ n) (hmpos : 0 < m)
    (p : FKIsingSquareRadialPatchPrimalNode m) : Nat :=
  isingFiniteGraphDistanceToBoundary
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalBoundary_nonempty m hmpos) p

noncomputable def fkIsingSquareRadialPatchDualBoundaryDistance
    (m : Nat) (hm : 2 ≤ m) (p : FKIsingSquareRadialPatchDualNode m) : Nat :=
  isingFiniteGraphDistanceToBoundary
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualBoundary_nonempty m hm) p

noncomputable def fkIsingSquareRadialPatchPrimalTentCutoff
    (n m : Nat) (hm : m ≤ n) (hmpos : 0 < m) (r : Nat)
    (p : FKIsingSquareRadialPatchPrimalNode m) : Real :=
  isingFiniteGraphBoundaryTentCutoff
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalBoundary_nonempty m hmpos) r p

noncomputable def fkIsingSquareRadialPatchDualTentCutoff
    (m : Nat) (hm : 2 ≤ m) (r : Nat)
    (p : FKIsingSquareRadialPatchDualNode m) : Real :=
  isingFiniteGraphBoundaryTentCutoff
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualBoundary_nonempty m hm) r p

noncomputable def fkIsingSquareRadialPatchPrimalDeepDarts
    (n m : Nat) (hm : m ≤ n) (hmpos : 0 < m) (r : Nat) :
    Finset (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart := by
  classical
  exact Finset.univ.filter fun d ↦
    r ≤ fkIsingSquareRadialPatchPrimalBoundaryDistance n m hm hmpos d.snd

noncomputable def fkIsingSquareRadialPatchDualDeepDarts
    (m : Nat) (hm : 2 ≤ m) (r : Nat) :
    Finset (fkIsingSquareRadialPatchDualGraph m).Dart := by
  classical
  exact Finset.univ.filter fun d ↦
    r ≤ fkIsingSquareRadialPatchDualBoundaryDistance m hm d.snd

theorem fkIsingSquareRadialPatchPrimalTentCutoff_support
    (n m : Nat) (hm : m ≤ n) (hmpos : 0 < m) (r : Nat) :
    ∀ p, fkIsingSquareRadialPatchPrimalTentCutoff n m hm hmpos r p ≠ 0 →
      ¬ fkIsingSquareRadialPatchPrimalBoundary m p := by
  exact isingFiniteGraphBoundaryTentCutoff_support
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalBoundary_nonempty m hmpos) r

theorem fkIsingSquareRadialPatchDualTentCutoff_support
    (m : Nat) (hm : 2 ≤ m) (r : Nat) :
    ∀ p, fkIsingSquareRadialPatchDualTentCutoff m hm r p ≠ 0 →
      ¬ fkIsingSquareRadialPatchDualBoundary m p := by
  exact isingFiniteGraphBoundaryTentCutoff_support
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualBoundary_nonempty m hm) r

theorem fkIsingSquareRadialPatchPrimalTentCutoff_lipschitz
    (n m : Nat) (hm : m ≤ n) (hmpos : 0 < m)
    (r : Nat) (hr : 0 < r)
    (d : (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart) :
    |fkIsingSquareRadialPatchPrimalTentCutoff n m hm hmpos r d.snd -
      fkIsingSquareRadialPatchPrimalTentCutoff n m hm hmpos r d.fst| ≤
        1 / (r : Real) :=
  isingFiniteGraphBoundaryTentCutoff_lipschitz
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalBoundary_nonempty m hmpos) r hr d

theorem fkIsingSquareRadialPatchDualTentCutoff_lipschitz
    (m : Nat) (hm : 2 ≤ m) (r : Nat) (hr : 0 < r)
    (d : (fkIsingSquareRadialPatchDualGraph m).Dart) :
    |fkIsingSquareRadialPatchDualTentCutoff m hm r d.snd -
      fkIsingSquareRadialPatchDualTentCutoff m hm r d.fst| ≤
        1 / (r : Real) :=
  isingFiniteGraphBoundaryTentCutoff_lipschitz
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualBoundary_nonempty m hm) r hr d

theorem fkIsingSquareRadialPatchPrimalTentCutoff_one
    (n m : Nat) (hm : m ≤ n) (hmpos : 0 < m)
    (r : Nat) (hr : 0 < r) :
    ∀ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r,
      (1 : Real) ≤
        fkIsingSquareRadialPatchPrimalTentCutoff n m hm hmpos r d.snd := by
  intro d hd
  have hdeep : r ≤
      fkIsingSquareRadialPatchPrimalBoundaryDistance n m hm hmpos d.snd := by
    simpa [fkIsingSquareRadialPatchPrimalDeepDarts] using hd
  rw [show fkIsingSquareRadialPatchPrimalTentCutoff n m hm hmpos r d.snd = 1 by
    exact isingFiniteGraphBoundaryTentCutoff_eq_one
      (fkIsingSquareRadialPatchPrimalGraph n m hm)
      (fkIsingSquareRadialPatchPrimalBoundary m)
      (fkIsingSquareRadialPatchPrimalBoundary_nonempty m hmpos)
      r hr d.snd hdeep]

theorem fkIsingSquareRadialPatchDualTentCutoff_one
    (m : Nat) (hm : 2 ≤ m) (r : Nat) (hr : 0 < r) :
    ∀ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm r,
      (1 : Real) ≤ fkIsingSquareRadialPatchDualTentCutoff m hm r d.snd := by
  intro d hd
  have hdeep : r ≤ fkIsingSquareRadialPatchDualBoundaryDistance m hm d.snd := by
    simpa [fkIsingSquareRadialPatchDualDeepDarts] using hd
  rw [show fkIsingSquareRadialPatchDualTentCutoff m hm r d.snd = 1 by
    exact isingFiniteGraphBoundaryTentCutoff_eq_one
      (fkIsingSquareRadialPatchDualGraph m)
      (fkIsingSquareRadialPatchDualBoundary m)
      (fkIsingSquareRadialPatchDualBoundary_nonempty m hm)
      r hr d.snd hdeep]

theorem fkIsingSquareRadialPatchPrimalTentCutoff_energy_le
    (n m : Nat) (hm : m ≤ n) (hmpos : 0 < m)
    (r : Nat) (hr : 0 < r) :
    isingFiniteGraphDartSum
        (fkIsingSquareRadialPatchPrimalGraph n m hm)
        (fun x y ↦
          (fkIsingSquareRadialPatchPrimalTentCutoff n m hm hmpos r y -
            fkIsingSquareRadialPatchPrimalTentCutoff n m hm hmpos r x) ^ 2) ≤
      4 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
  have h := isingFiniteGraphDartSum_cutoffEnergy_le
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalTentCutoff n m hm hmpos r) 4
    (1 / (r : Real))
    (fkIsingSquareRadialPatchPrimalGraph_neighbor_card_le_four n m hm)
    (by positivity)
    (fkIsingSquareRadialPatchPrimalTentCutoff_lipschitz
      n m hm hmpos r hr)
  have hcardNat :
      Fintype.card (FKIsingSquareRadialPatchPrimalNode m) * 4 ≤
        4 * m ^ 2 := by
    calc
      _ ≤ m ^ 2 * 4 := Nat.mul_le_mul_right 4
        (fkIsingSquareRadialPatchPrimalNode_card_le_sq m)
      _ = 4 * m ^ 2 := by ring
  have hcardReal :
      ((Fintype.card (FKIsingSquareRadialPatchPrimalNode m) * 4 : Nat) :
          Real) ≤ 4 * (m : Real) ^ 2 := by
    exact_mod_cast hcardNat
  calc
    _ ≤ (Fintype.card (FKIsingSquareRadialPatchPrimalNode m) * 4 : Nat) *
        (1 / (r : Real)) ^ 2 := h
    _ ≤ (4 * (m : Real) ^ 2) * (1 / (r : Real)) ^ 2 :=
      mul_le_mul_of_nonneg_right hcardReal (sq_nonneg _)
    _ = 4 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
      field_simp

theorem fkIsingSquareRadialPatchDualTentCutoff_energy_le
    (m : Nat) (hm : 2 ≤ m) (r : Nat) (hr : 0 < r) :
    isingFiniteGraphDartSum
        (fkIsingSquareRadialPatchDualGraph m)
        (fun x y ↦
          (fkIsingSquareRadialPatchDualTentCutoff m hm r y -
            fkIsingSquareRadialPatchDualTentCutoff m hm r x) ^ 2) ≤
      4 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
  have h := isingFiniteGraphDartSum_cutoffEnergy_le
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualTentCutoff m hm r) 4
    (1 / (r : Real))
    (fkIsingSquareRadialPatchDualGraph_neighbor_card_le_four m)
    (by positivity)
    (fkIsingSquareRadialPatchDualTentCutoff_lipschitz m hm r hr)
  have hcardNat :
      Fintype.card (FKIsingSquareRadialPatchDualNode m) * 4 ≤
        4 * m ^ 2 := by
    calc
      _ ≤ m ^ 2 * 4 := Nat.mul_le_mul_right 4
        (fkIsingSquareRadialPatchDualNode_card_le_sq m)
      _ = 4 * m ^ 2 := by ring
  have hcardReal :
      ((Fintype.card (FKIsingSquareRadialPatchDualNode m) * 4 : Nat) :
          Real) ≤ 4 * (m : Real) ^ 2 := by
    exact_mod_cast hcardNat
  calc
    _ ≤ (Fintype.card (FKIsingSquareRadialPatchDualNode m) * 4 : Nat) *
        (1 / (r : Real)) ^ 2 := h
    _ ≤ (4 * (m : Real) ^ 2) * (1 / (r : Real)) ^ 2 :=
      mul_le_mul_of_nonneg_right hcardReal (sq_nonneg _)
    _ = 4 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
      field_simp

theorem fkIsingSquareRadialPatchPrimalDeepDarts_card_le
    (n m : Nat) (hm : m ≤ n) (hmpos : 0 < m) (r : Nat) :
    (fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r).card ≤
      4 * m ^ 2 := by
  classical
  calc
    _ ≤ Fintype.card (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = Nat.card (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart :=
      Nat.card_eq_fintype_card.symm
    _ ≤ Fintype.card (FKIsingSquareRadialPatchPrimalNode m) * 4 :=
      isingFiniteGraphDart_card_le
        (fkIsingSquareRadialPatchPrimalGraph n m hm) 4
        (fkIsingSquareRadialPatchPrimalGraph_neighbor_card_le_four n m hm)
    _ ≤ m ^ 2 * 4 := Nat.mul_le_mul_right 4
      (fkIsingSquareRadialPatchPrimalNode_card_le_sq m)
    _ = 4 * m ^ 2 := by ring

theorem fkIsingSquareRadialPatchDualDeepDarts_card_le
    (m : Nat) (hm : 2 ≤ m) (r : Nat) :
    (fkIsingSquareRadialPatchDualDeepDarts m hm r).card ≤ 4 * m ^ 2 := by
  classical
  calc
    _ ≤ Fintype.card (fkIsingSquareRadialPatchDualGraph m).Dart := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = Nat.card (fkIsingSquareRadialPatchDualGraph m).Dart :=
      Nat.card_eq_fintype_card.symm
    _ ≤ Fintype.card (FKIsingSquareRadialPatchDualNode m) * 4 :=
      isingFiniteGraphDart_card_le
        (fkIsingSquareRadialPatchDualGraph m) 4
        (fkIsingSquareRadialPatchDualGraph_neighbor_card_le_four m)
    _ ≤ m ^ 2 * 4 := Nat.mul_le_mul_right 4
      (fkIsingSquareRadialPatchDualNode_card_le_sq m)
    _ = 4 * m ^ 2 := by ring

theorem fkIsingSquareRadialPatchPrimal_deepVariation_sq_le
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (r : Nat) (hr : 0 < r) (base : Real) :
    (∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r,
        |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd -
          fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|) ^ 2 ≤
      256 * (#(fkIsingSquareRadialPatchPrimalDeepDarts
        n m hm hmpos r) : Real) * (m : Real) ^ 4 / (r : Real) ^ 2 := by
  have h := isingFiniteGraph_compactVariation_sq_le_of_superharmonicOn
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalTentCutoff n m hm hmpos r)
    (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base)
    (base - 2 * (m : Real)) (base + 2 * (m : Real)) 1
    (4 * (m : Real) ^ 2 / (r : Real) ^ 2)
    (fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r)
    (fkIsingSquareRadialPatchPrimalValue_superharmonicOn
      n m hn hm hmpos base)
    (fun p ↦ (fkIsingSquareRadialPatchPrimalValue_mem_range
      n m hn hm hmpos base p).1)
    (fun p ↦ (fkIsingSquareRadialPatchPrimalValue_mem_range
      n m hn hm hmpos base p).2)
    (fkIsingSquareRadialPatchPrimalTentCutoff_support n m hm hmpos r)
    (by norm_num)
    (fkIsingSquareRadialPatchPrimalTentCutoff_one n m hm hmpos r hr)
    (fkIsingSquareRadialPatchPrimalTentCutoff_energy_le
      n m hm hmpos r hr)
  norm_num at h
  ring_nf at h ⊢
  exact h

theorem fkIsingSquareRadialPatchDual_deepVariation_sq_le
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (hr : 0 < r) (base : Real) :
    (∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
        |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
          fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) ^ 2 ≤
      256 * (#(fkIsingSquareRadialPatchDualDeepDarts m hm2 r) : Real) *
        (m : Real) ^ 4 / (r : Real) ^ 2 := by
  have hmpos : 0 < m := by omega
  have h := isingFiniteGraph_compactVariation_sq_le_of_subharmonicOn
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualTentCutoff m hm2 r)
    (fkIsingSquareRadialPatchDualValue n m hn hm hmpos base)
    (base - 2 * (m : Real)) (base + 2 * (m : Real)) 1
    (4 * (m : Real) ^ 2 / (r : Real) ^ 2)
    (fkIsingSquareRadialPatchDualDeepDarts m hm2 r)
    (fkIsingSquareRadialPatchDualValue_subharmonicOn
      n m hn hm hmpos base)
    (fun p ↦ (fkIsingSquareRadialPatchDualValue_mem_range
      n m hn hm hmpos base p).1)
    (fun p ↦ (fkIsingSquareRadialPatchDualValue_mem_range
      n m hn hm hmpos base p).2)
    (fkIsingSquareRadialPatchDualTentCutoff_support m hm2 r)
    (by norm_num)
    (fkIsingSquareRadialPatchDualTentCutoff_one m hm2 r hr)
    (fkIsingSquareRadialPatchDualTentCutoff_energy_le m hm2 r hr)
  norm_num at h
  ring_nf at h ⊢
  exact h



theorem fkIsingSquareRadialPatchPrimal_normalizedDeepVariation_sq_le
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (r : Nat) (hr : 0 < r) (base : Real) :
    ((1 / (m : Real) ^ 2) *
      ∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r,
        |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd -
          fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|) ^ 2 ≤
      1024 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
  let S := fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r
  let V : Real := ∑ d ∈ S,
    |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd -
      fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|
  have hraw : V ^ 2 ≤
      256 * (#S : Real) * (m : Real) ^ 4 / (r : Real) ^ 2 := by
    exact fkIsingSquareRadialPatchPrimal_deepVariation_sq_le
      n m hn hm hmpos r hr base
  have hcardNat : S.card ≤ 4 * m ^ 2 :=
    fkIsingSquareRadialPatchPrimalDeepDarts_card_le n m hm hmpos r
  have hcard : (#S : Real) ≤ 4 * (m : Real) ^ 2 := by
    exact_mod_cast hcardNat
  have hraw' : V ^ 2 ≤
      1024 * (m : Real) ^ 6 / (r : Real) ^ 2 := by
    calc
      _ ≤ 256 * (#S : Real) * (m : Real) ^ 4 / (r : Real) ^ 2 := hraw
      _ ≤ 256 * (4 * (m : Real) ^ 2) * (m : Real) ^ 4 /
          (r : Real) ^ 2 := by gcongr
      _ = 1024 * (m : Real) ^ 6 / (r : Real) ^ 2 := by ring
  change ((1 / (m : Real) ^ 2) * V) ^ 2 ≤ _
  calc
    _ = (1 / (m : Real) ^ 4) * V ^ 2 := by ring
    _ ≤ (1 / (m : Real) ^ 4) *
        (1024 * (m : Real) ^ 6 / (r : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hraw' (by positivity)
    _ = 1024 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
      field_simp

theorem fkIsingSquareRadialPatchDual_normalizedDeepVariation_sq_le
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (hr : 0 < r) (base : Real) :
    ((1 / (m : Real) ^ 2) *
      ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
        |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
          fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) ^ 2 ≤
      1024 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
  let S := fkIsingSquareRadialPatchDualDeepDarts m hm2 r
  let V : Real := ∑ d ∈ S,
    |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|
  have hraw : V ^ 2 ≤
      256 * (#S : Real) * (m : Real) ^ 4 / (r : Real) ^ 2 := by
    exact fkIsingSquareRadialPatchDual_deepVariation_sq_le
      n m hn hm hm2 r hr base
  have hcardNat : S.card ≤ 4 * m ^ 2 :=
    fkIsingSquareRadialPatchDualDeepDarts_card_le m hm2 r
  have hcard : (#S : Real) ≤ 4 * (m : Real) ^ 2 := by
    exact_mod_cast hcardNat
  have hraw' : V ^ 2 ≤
      1024 * (m : Real) ^ 6 / (r : Real) ^ 2 := by
    calc
      _ ≤ 256 * (#S : Real) * (m : Real) ^ 4 / (r : Real) ^ 2 := hraw
      _ ≤ 256 * (4 * (m : Real) ^ 2) * (m : Real) ^ 4 /
          (r : Real) ^ 2 := by gcongr
      _ = 1024 * (m : Real) ^ 6 / (r : Real) ^ 2 := by ring
  change ((1 / (m : Real) ^ 2) * V) ^ 2 ≤ _
  calc
    _ = (1 / (m : Real) ^ 4) * V ^ 2 := by ring
    _ ≤ (1 / (m : Real) ^ 4) *
        (1024 * (m : Real) ^ 6 / (r : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hraw' (by positivity)
    _ = 1024 * (m : Real) ^ 2 / (r : Real) ^ 2 := by
      field_simp

theorem fkIsingSquareRadialPatchPrimal_normalizedDeepVariation_fixedFraction
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (r K : Nat) (hr : 0 < r) (hfrac : m ≤ K * r) (base : Real) :
    ((1 / (m : Real) ^ 2) *
      ∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm hmpos r,
        |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd -
          fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|) ^ 2 ≤
      1024 * (K : Real) ^ 2 := by
  have hmain := fkIsingSquareRadialPatchPrimal_normalizedDeepVariation_sq_le
    n m hn hm hmpos r hr base
  have hfracReal : (m : Real) ≤ (K : Real) * (r : Real) := by
    exact_mod_cast hfrac
  have hsq : (m : Real) ^ 2 ≤ (K : Real) ^ 2 * (r : Real) ^ 2 := by
    nlinarith [sq_nonneg ((K : Real) * (r : Real) - (m : Real))]
  calc
    _ ≤ 1024 * (m : Real) ^ 2 / (r : Real) ^ 2 := hmain
    _ ≤ 1024 * (K : Real) ^ 2 := by
      apply (div_le_iff₀ (by positivity : (0 : Real) < (r : Real) ^ 2)).2
      nlinarith

theorem fkIsingSquareRadialPatchDual_normalizedDeepVariation_fixedFraction
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r K : Nat) (hr : 0 < r) (hfrac : m ≤ K * r) (base : Real) :
    ((1 / (m : Real) ^ 2) *
      ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
        |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
          fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) ^ 2 ≤
      1024 * (K : Real) ^ 2 := by
  have hmain := fkIsingSquareRadialPatchDual_normalizedDeepVariation_sq_le
    n m hn hm hm2 r hr base
  have hfracReal : (m : Real) ≤ (K : Real) * (r : Real) := by
    exact_mod_cast hfrac
  have hsq : (m : Real) ^ 2 ≤ (K : Real) ^ 2 * (r : Real) ^ 2 := by
    nlinarith [sq_nonneg ((K : Real) * (r : Real) - (m : Real))]
  calc
    _ ≤ 1024 * (m : Real) ^ 2 / (r : Real) ^ 2 := hmain
    _ ≤ 1024 * (K : Real) ^ 2 := by
      apply (div_le_iff₀ (by positivity : (0 : Real) < (r : Real) ^ 2)).2
      nlinarith

end

end StatMech.Universality
