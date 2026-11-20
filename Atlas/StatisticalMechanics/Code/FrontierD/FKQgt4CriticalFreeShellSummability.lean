/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKQgt4UnconditionalRateAssembly
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

private theorem summable_quadratic_exponential {c : Real} (hc : 0 < c) :
    Summable (fun n : Nat =>
      ((2 * n + 1 : Nat) : Real) ^ 2 * Real.exp (-c * (n : Real))) := by
  let g : Nat -> Real := fun n =>
    4 * ((n + 1 : Nat) : Real) ^ 2 * Real.exp (-c * (n : Real))
  have hbase : Summable (fun n : Nat =>
      (n : Real) ^ 2 * Real.exp (-c * (n : Real))) :=
    Real.summable_pow_mul_exp_neg_nat_mul 2 hc
  have hshift : Summable (fun n : Nat =>
      ((n + 1 : Nat) : Real) ^ 2 * Real.exp (-c * ((n + 1 : Nat) : Real))) :=
    hbase.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hg : Summable g := by
    have hscaled := hshift.mul_left (4 * Real.exp c)
    apply hscaled.congr
    intro n
    dsimp [g]
    rw [show (-c * (n : Real)) =
        -c * ((n + 1 : Nat) : Real) + c by push_cast; ring,
      Real.exp_add]
    ring
  apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      (fun n => ?_) hg
  dsimp [g]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  norm_num
  have hn : 0 <= (n : Real) := Nat.cast_nonneg n
  nlinarith



theorem fkQgt4CriticalFreeSphereConnectionEvent_summable_of_ratePos
    {q : Real} (hq : 4 < q)
    (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
    Summable (fun n : Nat =>
      ((FK.freeInfiniteVolume 2
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (fkQgt4CriticalFreeSphereConnectionEvent n)) := by
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q)
  let c := fkQgt4CriticalFreeExactDiagonalRateLimit hq / 4
  have hc : 0 < c := by
    dsimp [c]
    linarith
  have hmajorant : Summable (fun n : Nat =>
      ((2 * n + 1 : Nat) : Real) ^ 2 * Real.exp (-c * (n : Real))) :=
    summable_quadratic_exponential hc
  obtain ⟨N, hN⟩ :=
    fkQgt4CriticalFreeSphereConnectionEvent_eventually_exponential hq hpos
  apply hmajorant.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop, eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have hnonneg : 0 <= mu.real (fkQgt4CriticalFreeSphereConnectionEvent n) :=
    measureReal_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  simpa [mu, c] using hN n hn

theorem fkQgt4CriticalFreeSphereConnectionEvent_summable_of_winding
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q)) :
    Summable (fun n : Nat =>
      ((FK.freeInfiniteVolume 2
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (fkQgt4CriticalFreeSphereConnectionEvent n)) :=
  fkQgt4CriticalFreeSphereConnectionEvent_summable_of_ratePos hq
    (fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_winding hq hwind)




theorem fkQgt4CriticalFreeSphereConnectionEvent_tsum_ne_top_of_ratePos
    {q : Real} (hq : 4 < q)
    (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
    (∑' n : Nat,
      ((FK.freeInfiniteVolume 2
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
        Measure (ConfigSpace (Sym2 (Site 2))))
          (fkQgt4CriticalFreeSphereConnectionEvent n)) ≠ ⊤ := by
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) :=
    FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q)
  have hsum : Summable (fun n : Nat =>
      mu.real (fkQgt4CriticalFreeSphereConnectionEvent n)) := by
    simpa [mu] using
      fkQgt4CriticalFreeSphereConnectionEvent_summable_of_ratePos hq hpos
  have hnonneg : forall n : Nat,
      0 <= mu.real (fkQgt4CriticalFreeSphereConnectionEvent n) :=
    fun _ => measureReal_nonneg
  have hmeasure : forall n : Nat,
      mu (fkQgt4CriticalFreeSphereConnectionEvent n) =
        ENNReal.ofReal (mu.real (fkQgt4CriticalFreeSphereConnectionEvent n)) := by
    intro n
    rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top mu _)]
  simp_rw [show ((FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2)))) = mu by rfl,
    hmeasure]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsum]
  exact ENNReal.ofReal_ne_top

theorem fkQgt4CriticalFreeSphereConnectionEvent_tsum_ne_top_of_winding
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q)) :
    (∑' n : Nat,
      ((FK.freeInfiniteVolume 2
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
        (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
        (by linarith : (0 : Real) < q) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
        Measure (ConfigSpace (Sym2 (Site 2))))
        (fkQgt4CriticalFreeSphereConnectionEvent n)) ≠ ⊤ :=
  fkQgt4CriticalFreeSphereConnectionEvent_tsum_ne_top_of_ratePos hq
    (fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_winding hq hwind)



theorem fkQgt4CriticalFreeSphereConnectionEvent_limsup_zero_of_winding
    {q : Real} (hq : 4 < q)
    (hwind : FKQgt4TorusSixVertexWindingBridge
      (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)
      (fkQgt4SixVertexGapRate q)) :
    ((FK.freeInfiniteVolume 2
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1
      (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2
      (by linarith : (0 : Real) < q) :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
      Measure (ConfigSpace (Sym2 (Site 2))))
        (limsup fkQgt4CriticalFreeSphereConnectionEvent atTop) = 0 := by
  apply measure_limsup_atTop_eq_zero
  exact fkQgt4CriticalFreeSphereConnectionEvent_tsum_ne_top_of_winding hq hwind

end

end StatMech.FrontierD
