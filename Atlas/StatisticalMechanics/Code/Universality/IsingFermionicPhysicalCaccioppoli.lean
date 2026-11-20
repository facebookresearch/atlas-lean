/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicFiniteCutoff
import Code.Universality.IsingFermionicPhysicalCheckerboard
import Code.Universality.IsingFermionicPhysicalPrimitiveBounds









namespace StatMech.Universality

open Finset SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section



theorem fkIsingSquareRadialPatchDualGraph_neighbor_card_le_four
    (m : Nat) (p : FKIsingSquareRadialPatchDualNode m) :
    Nat.card ((fkIsingSquareRadialPatchDualGraph m).neighborSet p) ≤ 4 := by
  classical
  let code : (fkIsingSquareRadialPatchDualGraph m).neighborSet p →
      Bool × Bool := fun q ↦
    (decide (p.1.1.1 + 1 = q.1.1.1),
      decide (p.1.2.1 + 1 = q.1.1.2.1))
  have hcode : Function.Injective code := by
    intro q r hqr
    have hq := q.2
    have hr := r.2
    change
      (p.1.1.1 + 1 = q.1.1.1 ∨ q.1.1.1 + 1 = p.1.1.1) ∧
        (p.1.2.1 + 1 = q.1.1.2.1 ∨ q.1.1.2.1 + 1 = p.1.2.1) at hq
    change
      (p.1.1.1 + 1 = r.1.1.1 ∨ r.1.1.1 + 1 = p.1.1.1) ∧
        (p.1.2.1 + 1 = r.1.1.2.1 ∨ r.1.1.2.1 + 1 = p.1.2.1) at hr
    have hqx := hq.1
    have hqy := hq.2
    have hrx := hr.1
    have hry := hr.2
    have hqr0 := congrArg Prod.fst hqr
    have hqr1 := congrArg Prod.snd hqr
    dsimp [code] at hqr0 hqr1
    have hx : q.1.1.1.1 = r.1.1.1.1 := by
      rcases hqx with hqx | hqx <;> rcases hrx with hrx | hrx
      · omega
      · simp [hqx] at hqr0
        omega
      · simp [hrx] at hqr0
        omega
      · omega
    have hy : q.1.1.2.1 = r.1.1.2.1 := by
      rcases hqy with hqy | hqy <;> rcases hry with hry | hry
      · omega
      · simp [hqy] at hqr1
        omega
      · simp [hry] at hqr1
        omega
      · omega
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (Fin.ext hx) (Fin.ext hy)
  have hcard := Fintype.card_le_of_injective code hcode
  norm_num [code] at hcard
  simpa [Nat.card_eq_fintype_card] using hcard



theorem fkIsingSquareRadialPatchPrimalGraph_neighbor_card_le_four
    (n m : Nat) (hm : m ≤ n)
    (p : FKIsingSquareRadialPatchPrimalNode m) :
    Nat.card ((fkIsingSquareRadialPatchPrimalGraph n m hm).neighborSet p) ≤
      4 := by
  classical
  let embed := fkIsingSquareRadialPatchPrimalNodeVertex n m hm
  let code :
      (fkIsingSquareRadialPatchPrimalGraph n m hm).neighborSet p →
        (fkSquareBoxPlanar n).G.neighborSet (embed p) := fun q ↦
    ⟨embed q.1, by
      have hq := q.2
      change (fkSquareBoxPlanar n).G.Adj (embed p) (embed q.1) at hq
      exact hq⟩
  have hcode : Function.Injective code := by
    intro q r hqr
    apply Subtype.ext
    apply fkIsingSquareRadialPatchPrimalNodeVertex_injective n m hm
    exact congrArg Subtype.val hqr
  calc
    Nat.card ((fkIsingSquareRadialPatchPrimalGraph n m hm).neighborSet p) ≤
        Nat.card ((fkSquareBoxPlanar n).G.neighborSet (embed p)) :=
      Nat.card_le_card_of_injective code hcode
    _ = (fkSquareBoxPlanar n).G.degree (embed p) := by
      rw [Nat.card_eq_fintype_card,
        SimpleGraph.card_neighborSet_eq_degree]
    _ ≤ 4 := by
      simpa only [fkSquareBoxPlanar_graph] using
        StatMech.FK.qp_boxGraph_degree_le 2 n (embed p)


noncomputable def fkIsingSquareRadialPatchPrimalInteriorCutoff
    (m : Nat) (p : FKIsingSquareRadialPatchPrimalNode m) : Real := by
  classical
  exact if fkIsingSquareRadialPatchPrimalBoundary m p then 0 else 1


noncomputable def fkIsingSquareRadialPatchDualInteriorCutoff
    (m : Nat) (p : FKIsingSquareRadialPatchDualNode m) : Real := by
  classical
  exact if fkIsingSquareRadialPatchDualBoundary m p then 0 else 1


noncomputable def fkIsingSquareRadialPatchPrimalInteriorDarts
    (n m : Nat) (hm : m ≤ n) :
    Finset (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart := by
  classical
  exact Finset.univ.filter fun d ↦
    fkIsingSquareRadialPatchPrimalInteriorCutoff m d.snd = 1


noncomputable def fkIsingSquareRadialPatchDualInteriorDarts
    (m : Nat) : Finset (fkIsingSquareRadialPatchDualGraph m).Dart := by
  classical
  exact Finset.univ.filter fun d ↦
    fkIsingSquareRadialPatchDualInteriorCutoff m d.snd = 1

theorem fkIsingSquareRadialPatchPrimalInteriorCutoff_support
    (m : Nat) : ∀ p,
    fkIsingSquareRadialPatchPrimalInteriorCutoff m p ≠ 0 →
      ¬ fkIsingSquareRadialPatchPrimalBoundary m p := by
  intro p hp hboundary
  simp [fkIsingSquareRadialPatchPrimalInteriorCutoff, hboundary] at hp

theorem fkIsingSquareRadialPatchDualInteriorCutoff_support
    (m : Nat) : ∀ p,
    fkIsingSquareRadialPatchDualInteriorCutoff m p ≠ 0 →
      ¬ fkIsingSquareRadialPatchDualBoundary m p := by
  intro p hp hboundary
  simp [fkIsingSquareRadialPatchDualInteriorCutoff, hboundary] at hp

theorem fkIsingSquareRadialPatchPrimalInteriorCutoff_lipschitz
    (n m : Nat) (hm : m ≤ n)
    (d : (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart) :
    |fkIsingSquareRadialPatchPrimalInteriorCutoff m d.snd -
      fkIsingSquareRadialPatchPrimalInteriorCutoff m d.fst| ≤ 1 := by
  by_cases hs : fkIsingSquareRadialPatchPrimalBoundary m d.snd <;>
    by_cases hf : fkIsingSquareRadialPatchPrimalBoundary m d.fst <;>
    simp [fkIsingSquareRadialPatchPrimalInteriorCutoff, hs, hf]

theorem fkIsingSquareRadialPatchDualInteriorCutoff_lipschitz
    (m : Nat) (d : (fkIsingSquareRadialPatchDualGraph m).Dart) :
    |fkIsingSquareRadialPatchDualInteriorCutoff m d.snd -
      fkIsingSquareRadialPatchDualInteriorCutoff m d.fst| ≤ 1 := by
  by_cases hs : fkIsingSquareRadialPatchDualBoundary m d.snd <;>
    by_cases hf : fkIsingSquareRadialPatchDualBoundary m d.fst <;>
    simp [fkIsingSquareRadialPatchDualInteriorCutoff, hs, hf]

theorem fkIsingSquareRadialPatchPrimalInteriorCutoff_one
    (n m : Nat) (hm : m ≤ n) : ∀ d ∈
      fkIsingSquareRadialPatchPrimalInteriorDarts n m hm,
      (1 : Real) ≤ fkIsingSquareRadialPatchPrimalInteriorCutoff m d.snd := by
  intro d hd
  have hone : fkIsingSquareRadialPatchPrimalInteriorCutoff m d.snd = 1 := by
    simpa [fkIsingSquareRadialPatchPrimalInteriorDarts] using hd
  rw [hone]

theorem fkIsingSquareRadialPatchDualInteriorCutoff_one
    (m : Nat) : ∀ d ∈ fkIsingSquareRadialPatchDualInteriorDarts m,
      (1 : Real) ≤ fkIsingSquareRadialPatchDualInteriorCutoff m d.snd := by
  intro d hd
  have hone : fkIsingSquareRadialPatchDualInteriorCutoff m d.snd = 1 := by
    simpa [fkIsingSquareRadialPatchDualInteriorDarts] using hd
  rw [hone]

theorem fkIsingSquareRadialPatchPrimalInteriorCutoff_energy_le
    (n m : Nat) (hm : m ≤ n) :
    isingFiniteGraphDartSum
        (fkIsingSquareRadialPatchPrimalGraph n m hm)
        (fun x y ↦
          (fkIsingSquareRadialPatchPrimalInteriorCutoff m y -
            fkIsingSquareRadialPatchPrimalInteriorCutoff m x) ^ 2) ≤
      4 * (m : Real) ^ 2 := by
  have h := isingFiniteGraphDartSum_cutoffEnergy_le
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalInteriorCutoff m) 4 1
    (fkIsingSquareRadialPatchPrimalGraph_neighbor_card_le_four n m hm)
    (by norm_num)
    (fkIsingSquareRadialPatchPrimalInteriorCutoff_lipschitz n m hm)
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
        (1 : Real) ^ 2 := h
    _ = ((Fintype.card (FKIsingSquareRadialPatchPrimalNode m) * 4 : Nat) :
        Real) := by norm_num
    _ ≤ 4 * (m : Real) ^ 2 := hcardReal

theorem fkIsingSquareRadialPatchDualInteriorCutoff_energy_le
    (m : Nat) :
    isingFiniteGraphDartSum
        (fkIsingSquareRadialPatchDualGraph m)
        (fun x y ↦
          (fkIsingSquareRadialPatchDualInteriorCutoff m y -
            fkIsingSquareRadialPatchDualInteriorCutoff m x) ^ 2) ≤
      4 * (m : Real) ^ 2 := by
  have h := isingFiniteGraphDartSum_cutoffEnergy_le
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualInteriorCutoff m) 4 1
    (fkIsingSquareRadialPatchDualGraph_neighbor_card_le_four m)
    (by norm_num)
    (fkIsingSquareRadialPatchDualInteriorCutoff_lipschitz m)
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
        (1 : Real) ^ 2 := h
    _ = ((Fintype.card (FKIsingSquareRadialPatchDualNode m) * 4 : Nat) :
        Real) := by norm_num
    _ ≤ 4 * (m : Real) ^ 2 := hcardReal



theorem fkIsingSquareRadialPatchPrimitive_mem_range
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    -(2 * (m : Real)) ≤
        fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j ∧
      fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j ≤
        2 * (m : Real) := by
  have habs := abs_fkIsingSquareRadialPatchPrimitive_le
    n m hn hm hmpos i j
  have hij : (i : Real) + (j : Real) ≤ 2 * (m : Real) := by
    exact_mod_cast (by omega : i + j ≤ 2 * m)
  exact abs_le.mp (habs.trans hij)

theorem fkIsingSquareRadialPatchPrimalValue_mem_range
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (p : FKIsingSquareRadialPatchPrimalNode m) :
    base - 2 * (m : Real) ≤
        fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p ∧
      fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base p ≤
        base + 2 * (m : Real) := by
  have h := fkIsingSquareRadialPatchPrimitive_mem_range
    n m hn hm hmpos p.1.1.1 p.1.2.1 p.1.1.2 p.1.2.2
  unfold fkIsingSquareRadialPatchPrimalValue
  constructor <;> linarith

theorem fkIsingSquareRadialPatchDualValue_mem_range
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (p : FKIsingSquareRadialPatchDualNode m) :
    base - 2 * (m : Real) ≤
        fkIsingSquareRadialPatchDualValue n m hn hm hmpos base p ∧
      fkIsingSquareRadialPatchDualValue n m hn hm hmpos base p ≤
        base + 2 * (m : Real) := by
  have h := fkIsingSquareRadialPatchPrimitive_mem_range
    n m hn hm hmpos p.1.1.1 p.1.2.1 p.1.1.2 p.1.2.2
  unfold fkIsingSquareRadialPatchDualValue
  constructor <;> linarith




theorem fkIsingSquareRadialPatchDual_interiorVariation_sq_le
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) :
    (∑ d ∈ fkIsingSquareRadialPatchDualInteriorDarts m,
        |fkIsingSquareRadialPatchDualValue n m hn hm hmpos base d.snd -
          fkIsingSquareRadialPatchDualValue n m hn hm hmpos base d.fst|) ^ 2 ≤
      256 * (#(fkIsingSquareRadialPatchDualInteriorDarts m) : Real) *
        (m : Real) ^ 4 := by
  have h := isingFiniteGraph_compactVariation_sq_le_of_subharmonicOn
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualInteriorCutoff m)
    (fkIsingSquareRadialPatchDualValue n m hn hm hmpos base)
    (base - 2 * (m : Real)) (base + 2 * (m : Real)) 1
    (4 * (m : Real) ^ 2)
    (fkIsingSquareRadialPatchDualInteriorDarts m)
    (fkIsingSquareRadialPatchDualValue_subharmonicOn
      n m hn hm hmpos base)
    (fun p ↦ (fkIsingSquareRadialPatchDualValue_mem_range
      n m hn hm hmpos base p).1)
    (fun p ↦ (fkIsingSquareRadialPatchDualValue_mem_range
      n m hn hm hmpos base p).2)
    (fkIsingSquareRadialPatchDualInteriorCutoff_support m)
    (by norm_num)
    (fkIsingSquareRadialPatchDualInteriorCutoff_one m)
    (fkIsingSquareRadialPatchDualInteriorCutoff_energy_le m)
  norm_num at h
  ring_nf at h ⊢
  exact h



theorem fkIsingSquareRadialPatchPrimal_interiorVariation_sq_le
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) :
    (∑ d ∈ fkIsingSquareRadialPatchPrimalInteriorDarts n m hm,
        |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.snd -
          fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base d.fst|) ^ 2 ≤
      256 * (#(fkIsingSquareRadialPatchPrimalInteriorDarts n m hm) : Real) *
        (m : Real) ^ 4 := by
  have h := isingFiniteGraph_compactVariation_sq_le_of_superharmonicOn
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalInteriorCutoff m)
    (fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base)
    (base - 2 * (m : Real)) (base + 2 * (m : Real)) 1
    (4 * (m : Real) ^ 2)
    (fkIsingSquareRadialPatchPrimalInteriorDarts n m hm)
    (fkIsingSquareRadialPatchPrimalValue_superharmonicOn
      n m hn hm hmpos base)
    (fun p ↦ (fkIsingSquareRadialPatchPrimalValue_mem_range
      n m hn hm hmpos base p).1)
    (fun p ↦ (fkIsingSquareRadialPatchPrimalValue_mem_range
      n m hn hm hmpos base p).2)
    (fkIsingSquareRadialPatchPrimalInteriorCutoff_support m)
    (by norm_num)
    (fkIsingSquareRadialPatchPrimalInteriorCutoff_one n m hm)
    (fkIsingSquareRadialPatchPrimalInteriorCutoff_energy_le n m hm)
  norm_num at h
  ring_nf at h ⊢
  exact h

end

end StatMech.Universality
