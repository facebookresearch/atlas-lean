/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalCompactVariation
import Code.Universality.IsingFermionicPhysicalCompactEnergy
import Code.Universality.IsingFermionicEndpointPointwise



namespace StatMech.Universality

open Finset SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

abbrev FKIsingSquareRadialPatchInteriorCell (m : Nat) :=
  Fin (m - 1) × Fin (m - 1)

private theorem fkIsingSquareRadialPatchInteriorCell_succ_lt
    {m : Nat} (i : Fin (m - 1)) : i.1 + 1 < m := by
  omega

noncomputable def fkIsingSquareRadialPatchCellPrimalTail
    (m : Nat) (c : FKIsingSquareRadialPatchInteriorCell m) :
    FKIsingSquareRadialPatchPrimalNode m := by
  classical
  by_cases h : Even (c.1.1 + c.2.1)
  · exact ⟨(⟨c.1.1, by omega⟩, ⟨c.2.1, by omega⟩), h⟩
  · exact ⟨(⟨c.1.1 + 1, by
        exact fkIsingSquareRadialPatchInteriorCell_succ_lt c.1⟩,
      ⟨c.2.1, by omega⟩), by
      change Even ((c.1.1 + 1) + c.2.1)
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp h
      omega⟩

noncomputable def fkIsingSquareRadialPatchCellPrimalHead
    (m : Nat) (c : FKIsingSquareRadialPatchInteriorCell m) :
    FKIsingSquareRadialPatchPrimalNode m := by
  classical
  by_cases h : Even (c.1.1 + c.2.1)
  · exact ⟨(⟨c.1.1 + 1, by
        exact fkIsingSquareRadialPatchInteriorCell_succ_lt c.1⟩,
      ⟨c.2.1 + 1, by
        exact fkIsingSquareRadialPatchInteriorCell_succ_lt c.2⟩), by
      change Even ((c.1.1 + 1) + (c.2.1 + 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp h
      omega⟩
  · exact ⟨(⟨c.1.1, by omega⟩,
      ⟨c.2.1 + 1, by
        exact fkIsingSquareRadialPatchInteriorCell_succ_lt c.2⟩), by
      change Even (c.1.1 + (c.2.1 + 1))
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp h
      omega⟩

noncomputable def fkIsingSquareRadialPatchCellDualTail
    (m : Nat) (c : FKIsingSquareRadialPatchInteriorCell m) :
    FKIsingSquareRadialPatchDualNode m := by
  classical
  by_cases h : Even (c.1.1 + c.2.1)
  · exact ⟨(⟨c.1.1, by omega⟩,
      ⟨c.2.1 + 1, by
        exact fkIsingSquareRadialPatchInteriorCell_succ_lt c.2⟩), by
      change ¬ Even (c.1.1 + (c.2.1 + 1))
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp h
      omega⟩
  · exact ⟨(⟨c.1.1, by omega⟩, ⟨c.2.1, by omega⟩), h⟩

noncomputable def fkIsingSquareRadialPatchCellDualHead
    (m : Nat) (c : FKIsingSquareRadialPatchInteriorCell m) :
    FKIsingSquareRadialPatchDualNode m := by
  classical
  by_cases h : Even (c.1.1 + c.2.1)
  · exact ⟨(⟨c.1.1 + 1, by
        exact fkIsingSquareRadialPatchInteriorCell_succ_lt c.1⟩,
      ⟨c.2.1, by omega⟩), by
      change ¬ Even ((c.1.1 + 1) + c.2.1)
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp h
      omega⟩
  · exact ⟨(⟨c.1.1 + 1, by
        exact fkIsingSquareRadialPatchInteriorCell_succ_lt c.1⟩,
      ⟨c.2.1 + 1, by
        exact fkIsingSquareRadialPatchInteriorCell_succ_lt c.2⟩), by
      change ¬ Even ((c.1.1 + 1) + (c.2.1 + 1))
      rw [Nat.not_even_iff]
      have hmod := Nat.not_even_iff.mp h
      omega⟩

noncomputable def fkIsingSquareRadialPatchCellPrimalDart
    (n m : Nat) (hm : m ≤ n) (c : FKIsingSquareRadialPatchInteriorCell m) :
    (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart := by
  classical
  refine ⟨(fkIsingSquareRadialPatchCellPrimalTail m c,
    fkIsingSquareRadialPatchCellPrimalHead m c), ?_⟩
  change (fkSquareBoxPlanar n).G.Adj
    (fkIsingSquareRadialPatchPrimalNodeVertex n m hm
      (fkIsingSquareRadialPatchCellPrimalTail m c))
    (fkIsingSquareRadialPatchPrimalNodeVertex n m hm
      (fkIsingSquareRadialPatchCellPrimalHead m c))
  by_cases h : Even (c.1.1 + c.2.1)
  · simp only [fkIsingSquareRadialPatchCellPrimalTail,
      fkIsingSquareRadialPatchCellPrimalHead, h, dif_pos]
    change (fkSquareBoxPlanar n).G.Adj
      (fkIsingSquareRadialPatchVertex n m hm
        ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩)
      (fkIsingSquareRadialPatchVertex n m hm
        ⟨c.1.1 + 1, by omega⟩ ⟨c.2.1 + 1, by omega⟩)
    rw [fkIsingSquareRadialPatchVertex_northeast_eq_neighbor_east
      n m c.1.1 c.2.1 hm
      (fkIsingSquareRadialPatchInteriorCell_succ_lt c.1)
      (fkIsingSquareRadialPatchInteriorCell_succ_lt c.2) h]
    exact fkIsingSquare_adj_neighbor n _ .east _
  · have heven : Even ((c.1.1 + 1) + c.2.1) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp h
      omega
    simp only [fkIsingSquareRadialPatchCellPrimalTail,
      fkIsingSquareRadialPatchCellPrimalHead, h]
    change (fkSquareBoxPlanar n).G.Adj
      (fkIsingSquareRadialPatchVertex n m hm
        ⟨c.1.1 + 1, by omega⟩ ⟨c.2.1, by omega⟩)
      (fkIsingSquareRadialPatchVertex n m hm
        ⟨c.1.1, by omega⟩ ⟨c.2.1 + 1, by omega⟩)
    have hse := fkIsingSquareRadialPatchVertex_southeast_eq_neighbor_south
      n m (c.1.1 + 1) c.2.1 hm (by omega)
      (fkIsingSquareRadialPatchInteriorCell_succ_lt c.2)
      (fkIsingSquareRadialPatchInteriorCell_succ_lt c.1) heven
    simp only [Nat.add_sub_cancel] at hse
    rw [hse]
    exact fkIsingSquare_adj_neighbor n _ .south _

noncomputable def fkIsingSquareRadialPatchCellDualDart
    (m : Nat) (c : FKIsingSquareRadialPatchInteriorCell m) :
    (fkIsingSquareRadialPatchDualGraph m).Dart := by
  classical
  refine ⟨(fkIsingSquareRadialPatchCellDualTail m c,
    fkIsingSquareRadialPatchCellDualHead m c), ?_⟩
  change
    ((_ + 1 = _) ∨ (_ + 1 = _)) ∧ ((_ + 1 = _) ∨ (_ + 1 = _))
  by_cases h : Even (c.1.1 + c.2.1) <;>
    simp [fkIsingSquareRadialPatchCellDualTail,
      fkIsingSquareRadialPatchCellDualHead, h]

theorem fkIsingSquareRadialPatchCellPrimalDart_injective
    (n m : Nat) (hm : m ≤ n) :
    Function.Injective (fkIsingSquareRadialPatchCellPrimalDart n m hm) := by
  classical
  intro c d hcd
  have hcoords := congrArg (fun e :
      (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart ↦
        (e.fst.1.1.1, e.fst.1.2.1, e.snd.1.1.1, e.snd.1.2.1)) hcd
  by_cases hc : Even (c.1.1 + c.2.1) <;>
    by_cases hd : Even (d.1.1 + d.2.1) <;>
    simp [fkIsingSquareRadialPatchCellPrimalDart,
      fkIsingSquareRadialPatchCellPrimalTail,
      fkIsingSquareRadialPatchCellPrimalHead, hc, hd] at hcoords <;>
    apply Prod.ext <;> apply Fin.ext <;> omega

theorem fkIsingSquareRadialPatchCellDualDart_injective (m : Nat) :
    Function.Injective (fkIsingSquareRadialPatchCellDualDart m) := by
  classical
  intro c d hcd
  have hcoords := congrArg (fun e :
      (fkIsingSquareRadialPatchDualGraph m).Dart ↦
        (e.fst.1.1.1, e.fst.1.2.1, e.snd.1.1.1, e.snd.1.2.1)) hcd
  by_cases hc : Even (c.1.1 + c.2.1) <;>
    by_cases hd : Even (d.1.1 + d.2.1) <;>
    simp [fkIsingSquareRadialPatchCellDualDart,
      fkIsingSquareRadialPatchCellDualTail,
      fkIsingSquareRadialPatchCellDualHead, hc, hd] at hcoords <;>
    apply Prod.ext <;> apply Fin.ext <;> omega

theorem fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation_eq_cellDarts
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (c : FKIsingSquareRadialPatchInteriorCell m) :
    fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
        n m hn hm hmpos c.1.1 c.2.1 =
      |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base
          (fkIsingSquareRadialPatchCellPrimalDart n m hm c).snd -
        fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base
          (fkIsingSquareRadialPatchCellPrimalDart n m hm c).fst| +
      |fkIsingSquareRadialPatchDualValue n m hn hm hmpos base
          (fkIsingSquareRadialPatchCellDualDart m c).snd -
        fkIsingSquareRadialPatchDualValue n m hn hm hmpos base
          (fkIsingSquareRadialPatchCellDualDart m c).fst| := by
  classical
  by_cases h : Even (c.1.1 + c.2.1)
  · simp [fkIsingSquareRadialPatchCellPrimalDart,
      fkIsingSquareRadialPatchCellDualDart,
      fkIsingSquareRadialPatchCellPrimalTail,
      fkIsingSquareRadialPatchCellPrimalHead,
      fkIsingSquareRadialPatchCellDualTail,
      fkIsingSquareRadialPatchCellDualHead, h]
    unfold fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
    unfold fkIsingSquareRadialPatchPrimalValue
      fkIsingSquareRadialPatchDualValue
    simp
  · simp [fkIsingSquareRadialPatchCellPrimalDart,
      fkIsingSquareRadialPatchCellDualDart,
      fkIsingSquareRadialPatchCellPrimalTail,
      fkIsingSquareRadialPatchCellPrimalHead,
      fkIsingSquareRadialPatchCellDualTail,
      fkIsingSquareRadialPatchCellDualHead, h]
    unfold fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
    unfold fkIsingSquareRadialPatchPrimalValue
      fkIsingSquareRadialPatchDualValue
    simp
    rw [abs_sub_comm
      (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos
        c.1.1 (c.2.1 + 1))
      (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos
        (c.1.1 + 1) c.2.1)]
    ring



noncomputable def fkIsingSquareRadialPatchDeepCells
    (n m : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m) (r : Nat) :
    Finset (FKIsingSquareRadialPatchInteriorCell m) := by
  classical
  exact Finset.univ.filter fun c ↦
    fkIsingSquareRadialPatchCellPrimalDart n m hm c ∈
        fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r ∧
      fkIsingSquareRadialPatchCellDualDart m c ∈
        fkIsingSquareRadialPatchDualDeepDarts m hm2 r



theorem fkIsingSquareRadialPatch_deepCellDiagonalVariation_sum_le
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (base : Real) :
    (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
        fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
          n m hn hm (by omega) c.1.1 c.2.1) ≤
      (∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
        |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd -
          fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) +
      ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
        |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
          fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst| := by
  classical
  let C := fkIsingSquareRadialPatchDeepCells n m hm hm2 r
  let Sp := fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r
  let Sd := fkIsingSquareRadialPatchDualDeepDarts m hm2 r
  let pd := fkIsingSquareRadialPatchCellPrimalDart n m hm
  let dd := fkIsingSquareRadialPatchCellDualDart m
  let fp := fun d : (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart ↦
    |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd -
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|
  let fd := fun d : (fkIsingSquareRadialPatchDualGraph m).Dart ↦
    |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|
  have hpInject : Set.InjOn pd (C : Set _) :=
    (fkIsingSquareRadialPatchCellPrimalDart_injective n m hm).injOn
  have hdInject : Set.InjOn dd (C : Set _) :=
    (fkIsingSquareRadialPatchCellDualDart_injective m).injOn
  have hpSubset : C.image pd ⊆ Sp := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp hc).2.1
  have hdSubset : C.image dd ⊆ Sd := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp hc).2.2
  have hpSum : (∑ c ∈ C, fp (pd c)) ≤ ∑ d ∈ Sp, fp d := by
    rw [← Finset.sum_image hpInject]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpSubset
      (fun d _ _ ↦ abs_nonneg _)
  have hdSum : (∑ c ∈ C, fd (dd c)) ≤ ∑ d ∈ Sd, fd d := by
    rw [← Finset.sum_image hdInject]
    exact Finset.sum_le_sum_of_subset_of_nonneg hdSubset
      (fun d _ _ ↦ abs_nonneg _)
  simp_rw [fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation_eq_cellDarts
    n m hn hm (by omega) base]
  change (∑ c ∈ C, (fp (pd c) + fd (dd c))) ≤ _
  rw [Finset.sum_add_distrib]
  exact add_le_add hpSum hdSum



theorem fkIsingSquareRadialPatch_deepCell_normSq_sum_le_variation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (base : Real) :
    (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
        Complex.normSq
          (fkIsingSquareRadialPatchFullObservable n m hn hm
            ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩)) ≤
      2 *
        ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
          |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) +
        ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
          |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) := by
  have hcell :
      (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
              ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩)) ≤
        2 *
          ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
            fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
              n m hn hm (by omega) c.1.1 c.2.1 := by
    calc
      _ ≤ ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          2 * fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
            n m hn hm (by omega) c.1.1 c.2.1 := by
        apply Finset.sum_le_sum
        intro c hc
        exact fkIsingSquareRadialPatch_normSq_full_le_two_mul_cellDiagonalVariation
          n m hn hm (by omega) ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩
      _ = _ := by simp_rw [Finset.mul_sum]
  have hvariation :=
    fkIsingSquareRadialPatch_deepCellDiagonalVariation_sum_le
      n m hn hm hm2 r base
  exact hcell.trans (mul_le_mul_of_nonneg_left hvariation (by norm_num))


theorem fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_le
    (n m : Nat) (mesh : Real) (hn : 0 < n) (hm : m ≤ n)
    (hm2 : 2 ≤ m) (hmesh : 0 < mesh) (r : Nat) (base : Real) :
    mesh ^ 2 *
        ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
                ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
              (Real.sqrt (2 * mesh) : Complex)) ≤
      mesh *
        ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
          |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) +
        ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
          |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) := by
  have hsqrtSq : Real.sqrt (2 * mesh) ^ 2 = 2 * mesh := by
    rw [Real.sq_sqrt]
    positivity
  have hnorm (z : Complex) :
      Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) =
        Complex.normSq z / (2 * mesh) := by
    rw [Complex.normSq_div]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by positivity))]
    exact hsqrtSq
  have hraw := fkIsingSquareRadialPatch_deepCell_normSq_sum_le_variation
    n m hn hm hm2 r base
  simp_rw [hnorm]
  rw [← Finset.sum_div]
  calc
    mesh ^ 2 *
        ((∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
              ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩)) / (2 * mesh)) =
      mesh / 2 *
        ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
              ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩) := by
        field_simp
    _ ≤ mesh / 2 * (2 *
        ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
          |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) +
        ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
          |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|)) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = _ := by ring

noncomputable def fkIsingSquareRadialPatchWindowCell
    (m baseI baseJ R : Nat)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (p : IsingLeapfrogBox R) : FKIsingSquareRadialPatchInteriorCell m :=
  (⟨baseI + p.1.1, by have := p.1.2; omega⟩,
    ⟨baseJ + p.2.1, by have := p.2.2; omega⟩)

theorem fkIsingSquareRadialPatchWindowCell_injective
    (m baseI baseJ R : Nat)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m) :
    Function.Injective
      (fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ) := by
  intro p q hpq
  have hx := congrArg (fun c : FKIsingSquareRadialPatchInteriorCell m ↦ c.1.1) hpq
  have hy := congrArg (fun c : FKIsingSquareRadialPatchInteriorCell m ↦ c.2.1) hpq
  change baseI + p.1.1 = baseI + q.1.1 at hx
  change baseJ + p.2.1 = baseJ + q.2.1 at hy
  apply Prod.ext <;> apply Fin.ext <;> omega



theorem fkIsingSquareRadialPatchFullObservableWindow_deep_energy_le
    (n m baseI baseJ R : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat) (base : Real)
    (hdeep : ∀ p : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ p ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r) :
    mesh ^ 2 *
        ∑ p : IsingLeapfrogBox R,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservableWindow
                n m baseI baseJ R hn hm hfitI hfitJ p /
              (Real.sqrt (2 * mesh) : Complex)) ≤
      mesh *
        ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
          |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) +
        ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
          |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) := by
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
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    exact hdeep p
  have hsum : (∑ p : IsingLeapfrogBox R, energy (cell p)) ≤
      ∑ c ∈ C, energy c := by
    rw [← Finset.sum_image
      (fkIsingSquareRadialPatchWindowCell_injective
        m baseI baseJ R hfitI hfitJ).injOn]
    exact Finset.sum_le_sum_of_subset_of_nonneg himage
      (fun c _ _ ↦ Complex.normSq_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left hsum (sq_nonneg mesh)
  have hdeepEnergy :=
    fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_le
      n m mesh hn hm hm2 hmesh r base
  calc
    _ = mesh ^ 2 * ∑ p : IsingLeapfrogBox R, energy (cell p) := by
      congr 1
    _ ≤ mesh ^ 2 * ∑ c ∈ C, energy c := hscaled
    _ ≤ _ := hdeepEnergy



theorem fkIsingSquareRadialPatchFullObservableWindow_deep_diffusive
    (n m baseI baseJ R rho : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (hmesh : 0 < mesh) (r : Nat) (base : Real)
    (hdeep : ∀ q : IsingLeapfrogBox R,
      fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈
        fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
    (p p' : IsingLeapfrogBox R) (hrho : 0 < rho)
    (hp : IsingLeapfrogInteriorMargin R rho p)
    (hp' : IsingLeapfrogInteriorMargin R rho p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    mesh ^ 2 * Complex.normSq
        (fkIsingSquareRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p /
            (Real.sqrt (2 * mesh) : Complex) -
          fkIsingSquareRadialPatchFullObservableWindow
              n m baseI baseJ R hn hm hfitI hfitJ p' /
            (Real.sqrt (2 * mesh) : Complex)) ≤
      (1032080 / (rho : Real) ^ 3) * mesh *
        ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
          |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) +
        ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
          |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) := by
  have hgradient :=
    fkIsingSquareRadialPatchFullObservableWindow_physicalNormalized_normSq_sub_le_diffusive
      n m baseI baseJ R rho mesh hn hm hfitI hfitJ hmesh
      p p' hrho hp hp' hpp'
  have henergy :=
    fkIsingSquareRadialPatchFullObservableWindow_deep_energy_le
      n m baseI baseJ R mesh hn hm hm2 hfitI hfitJ hmesh r base hdeep
  have hfactor : 0 ≤ 1032080 / (rho : Real) ^ 3 := by positivity
  calc
    _ ≤ mesh ^ 2 *
        ((1032080 / (rho : Real) ^ 3) *
          ∑ q : IsingLeapfrogBox R,
            Complex.normSq
              (fkIsingSquareRadialPatchFullObservableWindow
                  n m baseI baseJ R hn hm hfitI hfitJ q /
                (Real.sqrt (2 * mesh) : Complex))) :=
      mul_le_mul_of_nonneg_left hgradient (sq_nonneg mesh)
    _ = (1032080 / (rho : Real) ^ 3) *
        (mesh ^ 2 *
          ∑ q : IsingLeapfrogBox R,
            Complex.normSq
              (fkIsingSquareRadialPatchFullObservableWindow
                  n m baseI baseJ R hn hm hfitI hfitJ q /
                (Real.sqrt (2 * mesh) : Complex))) := by ring
    _ ≤ (1032080 / (rho : Real) ^ 3) *
        (mesh *
          ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts
              n m hm (by omega) r,
            |fkIsingSquareRadialPatchPrimalValue
                n m hn hm (by omega) base d.snd -
              fkIsingSquareRadialPatchPrimalValue
                n m hn hm (by omega) base d.fst|) +
          ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
            |fkIsingSquareRadialPatchDualValue
                n m hn hm (by omega) base d.snd -
              fkIsingSquareRadialPatchDualValue
                n m hn hm (by omega) base d.fst|)) :=
      mul_le_mul_of_nonneg_left henergy hfactor
    _ = _ := by ring

end

end StatMech.Universality
