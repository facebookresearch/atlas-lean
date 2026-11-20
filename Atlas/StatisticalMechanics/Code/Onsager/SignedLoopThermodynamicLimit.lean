/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Onsager.SignedLoopRectangularDualPath
import Code.FrontierB.FreeBoxEvenLimit

open Finset SimpleGraph MeasureTheory Filter Topology

namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Sharpness StatMech.FrontierA
  StatMech.FrontierB

noncomputable section

private theorem ons_int_bounds_of_natAbs_le {n : Nat} {z : Int}
    (hz : z.natAbs <= n) : -(n : Int) <= z ∧ z <= n := by
  rcases Int.natAbs_eq z with hz' | hz' <;> omega


noncomputable def ons_centeredCoordEquiv (n : Nat) :
    {z : Int // z.natAbs <= n} ≃ Fin (2 * n + 1) where
  toFun z := ⟨(z.1 + n).toNat, by
    have hz := ons_int_bounds_of_natAbs_le z.2
    omega⟩
  invFun k := ⟨(k : Int) - n, by
    have hk := k.2
    have hb : -(n : Int) <= (k : Int) - n ∧ (k : Int) - n <= n := by
      constructor <;> omega
    rcases Int.natAbs_eq ((k : Int) - n) with h | h <;> omega⟩
  left_inv z := by
    apply Subtype.ext
    have hz := ons_int_bounds_of_natAbs_le z.2
    simp only
    rw [Int.toNat_of_nonneg (by omega : 0 <= z.1 + n)]
    omega
  right_inv k := by
    apply Fin.ext
    simp only
    have hk := k.2
    rw [show (k : Int) - n + n = (k : Int) by ring]
    exact Int.toNat_natCast k



noncomputable def ons_box2EquivRect (n : Nat) :
    sctBox 2 n ≃ ons_RectDualVertex (2 * n) (2 * n) where
  toFun x :=
    (ons_centeredCoordEquiv n ⟨x.1 0, x.2 0⟩,
      ons_centeredCoordEquiv n ⟨x.1 1, x.2 1⟩)
  invFun x :=
    ⟨![((ons_centeredCoordEquiv n).symm x.1).1,
        ((ons_centeredCoordEquiv n).symm x.2).1], by
      intro i
      fin_cases i
      · exact ((ons_centeredCoordEquiv n).symm x.1).2
      · exact ((ons_centeredCoordEquiv n).symm x.2).2⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    fin_cases i
    · exact congrArg Subtype.val
        ((ons_centeredCoordEquiv n).symm_apply_apply
          ⟨x.1 0, x.2 0⟩)
    · exact congrArg Subtype.val
        ((ons_centeredCoordEquiv n).symm_apply_apply
          ⟨x.1 1, x.2 1⟩)
  right_inv x := by
    apply Prod.ext <;>
      exact (ons_centeredCoordEquiv n).apply_symm_apply _

private theorem ons_centeredCoordEquiv_dist
    (n : Nat) (x y : {z : Int // z.natAbs <= n}) :
    Nat.dist (ons_centeredCoordEquiv n x).val
        (ons_centeredCoordEquiv n y).val = (x.1 - y.1).natAbs := by
  have hx := ons_int_bounds_of_natAbs_le x.2
  have hy := ons_int_bounds_of_natAbs_le y.2
  change Nat.dist (x.1 + n).toNat (y.1 + n).toNat = _
  have hxnat := Int.toNat_of_nonneg (by omega : 0 <= x.1 + n)
  have hynat := Int.toNat_of_nonneg (by omega : 0 <= y.1 + n)
  rcases Int.natAbs_eq (x.1 - y.1) with h | h
  · by_cases hxy : (x.1 + n).toNat <= (y.1 + n).toNat
    · rw [Nat.dist_eq_sub_of_le hxy]
      omega
    · rw [Nat.dist_comm,
        Nat.dist_eq_sub_of_le (by omega : (y.1 + n).toNat <= (x.1 + n).toNat)]
      omega
  · by_cases hxy : (x.1 + n).toNat <= (y.1 + n).toNat
    · rw [Nat.dist_eq_sub_of_le hxy]
      omega
    · rw [Nat.dist_comm,
        Nat.dist_eq_sub_of_le (by omega : (y.1 + n).toNat <= (x.1 + n).toNat)]
      omega


theorem ons_box2EquivRect_adj (n : Nat) (x y : sctBox 2 n) :
    (sctBoxGraph 2 n).Adj x y ↔
      (ons_rectDualGraph (2 * n) (2 * n)).Adj
        (ons_box2EquivRect n x) (ons_box2EquivRect n y) := by
  rw [show (sctBoxGraph 2 n).Adj x y ↔
      (x.1 0 - y.1 0).natAbs + (x.1 1 - y.1 1).natAbs = 1 by
    simp [sctBoxGraph, hypercubicLattice_adj, Fin.sum_univ_two]]
  rw [show (ons_rectDualGraph (2 * n) (2 * n)).Adj
      (ons_box2EquivRect n x) (ons_box2EquivRect n y) ↔
      (x.1 1 = y.1 1 ∧ (x.1 0 - y.1 0).natAbs = 1) ∨
      (x.1 0 = y.1 0 ∧ (x.1 1 - y.1 1).natAbs = 1) by
    change
      ((ons_centeredCoordEquiv n ⟨x.1 1, x.2 1⟩ =
          ons_centeredCoordEquiv n ⟨y.1 1, y.2 1⟩ ∧
        Nat.dist (ons_centeredCoordEquiv n ⟨x.1 0, x.2 0⟩).val
          (ons_centeredCoordEquiv n ⟨y.1 0, y.2 0⟩).val = 1) ∨
       (ons_centeredCoordEquiv n ⟨x.1 0, x.2 0⟩ =
          ons_centeredCoordEquiv n ⟨y.1 0, y.2 0⟩ ∧
        Nat.dist (ons_centeredCoordEquiv n ⟨x.1 1, x.2 1⟩).val
          (ons_centeredCoordEquiv n ⟨y.1 1, y.2 1⟩).val = 1)) ↔ _
    rw [ons_centeredCoordEquiv_dist n ⟨x.1 0, x.2 0⟩
        ⟨y.1 0, y.2 0⟩,
      ons_centeredCoordEquiv_dist n ⟨x.1 1, x.2 1⟩
        ⟨y.1 1, y.2 1⟩]
    simp only [Equiv.apply_eq_iff_eq, Subtype.mk.injEq]]
  omega



theorem ons_rectDualPath_twoPoint_eq_freeMeasure
    (n : Nat) (beta : Real) (path : ons_RectDualPath (2 * n) (2 * n)) :
    isingExpectation (ons_rectDualGraph (2 * n) (2 * n)) beta 0
        (fun spin => Ising.spin spin path.source * Ising.spin spin path.target) =
      ∫ spin, spinProd
          {((ons_box2EquivRect n).symm path.source).1,
            ((ons_box2EquivRect n).symm path.target).1} spin
        ∂(freeMeasure 2 n beta 0 : Measure (ConfigSpace (Site 2))) := by
  let a : sctBox 2 n := (ons_box2EquivRect n).symm path.source
  let b : sctBox 2 n := (ons_box2EquivRect n).symm path.target
  have hab : a ≠ b := by
    intro h
    apply path.source_ne_target
    simpa [a, b] using congrArg (ons_box2EquivRect n) h
  have hval : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
  have hrel := isingExpectation_spinProd_relabel
    (sctBoxGraph 2 n) (ons_rectDualGraph (2 * n) (2 * n))
    (ons_box2EquivRect n) (ons_box2EquivRect_adj n) beta 0
    ({a, b} : Finset (sctBox 2 n))
  have hmap : ({a, b} : Finset (sctBox 2 n)).map
      (ons_box2EquivRect n).toEmbedding =
        ({path.source, path.target} :
          Finset (ons_RectDualVertex (2 * n) (2 * n))) := by
    ext z
    simp [a, b]
  have hsupp : boxSpinSupport 2 n ({a.1, b.1} : Finset (Site 2)) =
      ({a, b} : Finset (sctBox 2 n)) := by
    ext z
    simp only [boxSpinSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (hz | hz)
      · exact Or.inl (Subtype.ext hz)
      · exact Or.inr (Subtype.ext hz)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  rw [integral_freeMeasure_spinProd 2 n beta 0 {a.1, b.1}]
  · rw [hsupp]
    rw [hmap] at hrel
    simpa [a, b, spinProd_pair a b hab,
      spinProd_pair path.source path.target path.source_ne_target] using hrel.symm
  · intro z hz
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact a.2
    · exact b.2


noncomputable def ons_rectDualPathCriticalRatio {n : Nat}
    (embedding : KWStraightLineEmbedding
      (ons_rectDualGraph (2 * n) (2 * n)))
    (path : ons_RectDualPath (2 * n) (2 * n)) : Complex :=
  ((ons_signedLoopCriticalWeight : Complex) ^
      (2 * (ons_rectDualPathDefect path).card) *
    ons_rectDualPathDefectKWDet embedding path
      ons_signedLoopCriticalWeight) /
    ons_rectDualKWDet embedding ons_signedLoopCriticalWeight




theorem ons_rectDualPathCriticalRatio_tendsto_freeState
    (embedding : ∀ n, KWStraightLineEmbedding
      (ons_rectDualGraph (2 * n) (2 * n)))
    (path : ∀ n, ons_RectDualPath (2 * n) (2 * n))
    (a b : Site 2)
    (hsource : ∀ᶠ n in atTop,
      ((ons_box2EquivRect n).symm (path n).source).1 = a)
    (htarget : ∀ᶠ n in atTop,
      ((ons_box2EquivRect n).symm (path n).target).1 = b) :
    Tendsto (fun n => ons_rectDualPathCriticalRatio (embedding n) (path n))
      atTop
      (nhds ((((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 ons_betaC 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) ^ 2)) := by
  let f : Nat -> Real := fun n =>
    ∫ spin, spinProd {a, b} spin
      ∂(freeMeasure 2 n ons_betaC 0 : Measure (ConfigSpace (Site 2)))
  have hf : Tendsto f atTop
      (nhds (∫ spin, spinProd {a, b} spin
        ∂(freeState 2 ons_betaC 0 : Measure (ConfigSpace (Site 2))))) := by
    simpa only [f] using
      integral_freeMeasure_spinProd_tendsto_freeState
        2 ons_betaC ons_betaC_pos.le ({a, b} : Finset (Site 2))
  have hfComplex : Tendsto (fun n => (f n : Complex)) atTop
      (nhds (((∫ spin, spinProd {a, b} spin
        ∂(freeState 2 ons_betaC 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex)) := by
    simpa only [Function.comp_apply] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hf
  apply (hfComplex.pow 2).congr'
  filter_upwards [hsource, htarget] with n hs ht
  rw [show ons_rectDualPathCriticalRatio (embedding n) (path n) =
      (isingExpectation (ons_rectDualGraph (2 * n) (2 * n)) ons_betaC 0
        (fun spin => Ising.spin spin (path n).source *
          Ising.spin spin (path n).target) : Complex) ^ 2 by
    symm
    exact coe_ons_rectDualPath_criticalTwoPoint_sq_eq_kwDet_ratio
      (embedding n) (path n)]
  rw [show (isingExpectation (ons_rectDualGraph (2 * n) (2 * n))
      ons_betaC 0 (fun spin => Ising.spin spin (path n).source *
        Ising.spin spin (path n).target) : Complex) =
      (((∫ spin, spinProd
        {((ons_box2EquivRect n).symm (path n).source).1,
          ((ons_box2EquivRect n).symm (path n).target).1} spin
        ∂(freeMeasure 2 n ons_betaC 0 : Measure (ConfigSpace (Site 2)))) : Real) :
          Complex) by
    exact_mod_cast ons_rectDualPath_twoPoint_eq_freeMeasure
      n ons_betaC (path n)]
  simp only [hs, ht, f]

end

end StatMech.Onsager
