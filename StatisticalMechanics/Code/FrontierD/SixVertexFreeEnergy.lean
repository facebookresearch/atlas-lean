/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.FrontierD.SixVertexPerron
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Matrix Filter Topology

namespace StatMech.FrontierD

private theorem hermitian_trace_pow_eq_sum_eigenvalues
    {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (hA : A.IsHermitian) (M : ℕ) :
    Matrix.trace (A ^ M) = ∑ i : α, hA.eigenvalues i ^ M := by
  conv_lhs =>
    rw [hA.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply,
      Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
      Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp

private theorem hermitian_trace_pow_eq_sum_eigenvalues₀
    {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (hA : A.IsHermitian) (M : ℕ) :
    Matrix.trace (A ^ M) =
      ∑ i : Fin (Fintype.card α), hA.eigenvalues₀ i ^ M := by
  rw [hermitian_trace_pow_eq_sum_eigenvalues A hA M]
  symm
  apply Fintype.sum_equiv (Fintype.equivOfCardEq (Fintype.card_fin _))
  intro i
  simp [Matrix.IsHermitian.eigenvalues]



theorem sixVertexSector_eigenvalues₀_ne_top_of_ne {N n : ℕ} (hn : n ≤ N)
    {c : ℝ} (hc : 0 < c)
    (i : Fin (Fintype.card (SixVertexSector N n)))
    (hi : i ≠ sixVertexSectorTopIndex N n hn) :
    (sixVertexSectorTransfer_isHermitian N n c).eigenvalues₀ i ≠
      sixVertexSectorTopEigenvalue N n hn c := by
  classical
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hn
  let A := sixVertexSectorTransfer N n c
  let T := Matrix.toEuclideanLin A
  let hA : A.IsHermitian := sixVertexSectorTransfer_isHermitian N n c
  let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let i0 := sixVertexSectorTopIndex N n hn
  let top := hA.eigenvalues₀ i0
  let b := hT.eigenvectorBasis finrank_euclideanSpace
  change hA.eigenvalues₀ i ≠ top
  intro heq
  let S := Module.End.eigenspace T top
  have huMem : b i0 ∈ S := by
    apply Module.End.mem_eigenspace_iff.mpr
    have hu := hT.apply_eigenvectorBasis finrank_euclideanSpace i0
    exact hu
  have hwMem : b i ∈ S := by
    apply Module.End.mem_eigenspace_iff.mpr
    have hw := hT.apply_eigenvectorBasis finrank_euclideanSpace i
    rw [← heq]
    exact hw
  let u : S := ⟨b i0, huMem⟩
  let w : S := ⟨b i, hwMem⟩
  have hune : u ≠ 0 := by
    intro hu0
    apply b.orthonormal.ne_zero i0
    exact congrArg Subtype.val hu0
  have hfin : Module.finrank ℝ S = 1 := by
    simpa [S, T, A, top, hA, i0] using
      sixVertexSectorTop_eigenspace_finrank hn hc
  have hspan : ℝ ∙ u = ⊤ :=
    (finrank_eq_one_iff_of_nonzero u hune).mp hfin
  have hwspan : w ∈ ℝ ∙ u := by
    rw [hspan]
    trivial
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hwspan
  have hrbase : r • b i0 = b i := congrArg Subtype.val hr
  have hself : @inner ℝ _ _ (b i0) (b i0) = 1 := by
    have h := orthonormal_iff_ite.mp b.orthonormal i0 i0
    rw [if_pos rfl] at h
    exact h
  have hcross : @inner ℝ _ _ (b i0) (b i) = 0 :=
    b.orthonormal.inner_eq_zero (Ne.symm hi)
  have hr0 : r = 0 := by
    have hinner := congrArg (fun z => @inner ℝ _ _ (b i0) z) hrbase
    change @inner ℝ _ _ (b i0) (r • b i0) =
      @inner ℝ _ _ (b i0) (b i) at hinner
    rw [inner_smul_right, hself, hcross, mul_one] at hinner
    exact hinner
  apply b.orthonormal.ne_zero i
  rw [← hrbase, hr0, zero_smul]



theorem sixVertexSector_trace_div_top_pow_tendsto_one
    {N n : ℕ} (hn : n ≤ N) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun M : ℕ =>
      Matrix.trace (sixVertexSectorTransfer N n c ^ M) /
        sixVertexSectorTopEigenvalue N n hn c ^ M)
      atTop (nhds 1) := by
  classical
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hn
  let A := sixVertexSectorTransfer N n c
  let hA : A.IsHermitian := sixVertexSectorTransfer_isHermitian N n c
  let T := Matrix.toEuclideanLin A
  let hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let i0 := sixVertexSectorTopIndex N n hn
  let top := hA.eigenvalues₀ i0
  have htoppos : 0 < top := by
    simpa [top, hA, i0] using sixVertexSectorTopEigenvalue_pos hn hc
  have htrace (M : ℕ) :
      Matrix.trace (A ^ M) =
        ∑ i : Fin (Fintype.card (SixVertexSector N n)),
          hA.eigenvalues₀ i ^ M :=
    hermitian_trace_pow_eq_sum_eigenvalues₀ A hA M
  have hformula (M : ℕ) :
      Matrix.trace (A ^ M) / top ^ M =
        ∑ i : Fin (Fintype.card (SixVertexSector N n)),
          (hA.eigenvalues₀ i / top) ^ M := by
    rw [htrace, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    exact (div_pow _ _ M).symm
  have hterm (i : Fin (Fintype.card (SixVertexSector N n))) (hi : i ≠ i0) :
      Tendsto (fun M : ℕ => (hA.eigenvalues₀ i / top) ^ M)
        atTop (nhds 0) := by
    have hine : hA.eigenvalues₀ i ≠ top := by
      simpa [hA, top, i0] using
        sixVertexSector_eigenvalues₀_ne_top_of_ne hn hc i hi
    have hei : Module.End.HasEigenvalue T (hA.eigenvalues₀ i) := by
      exact hT.hasEigenvalue_eigenvalues finrank_euclideanSpace i
    have hstrict : |hA.eigenvalues₀ i| < top := by
      simpa [T, A, hA, top, i0] using
        sixVertexSector_eigenvalue_abs_lt_top hn hc hei hine
    apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    rw [abs_div, abs_of_pos htoppos]
    exact (div_lt_one htoppos).mpr hstrict
  have hrest : Tendsto (fun M : ℕ =>
      ∑ i ∈ (Finset.univ.erase i0), (hA.eigenvalues₀ i / top) ^ M)
      atTop (nhds 0) := by
    have h := tendsto_finsetSum (Finset.univ.erase i0) (fun i hi =>
      hterm i (Finset.ne_of_mem_erase hi))
    simpa using h
  have hsplit (M : ℕ) :
      ∑ i : Fin (Fintype.card (SixVertexSector N n)),
          (hA.eigenvalues₀ i / top) ^ M =
        1 + ∑ i ∈ (Finset.univ.erase i0),
          (hA.eigenvalues₀ i / top) ^ M := by
    have h := Finset.sum_erase_add Finset.univ
      (fun i : Fin (Fintype.card (SixVertexSector N n)) =>
        (hA.eigenvalues₀ i / top) ^ M) (Finset.mem_univ i0)
    have htopterm : (hA.eigenvalues₀ i0 / top) ^ M = 1 := by
      simp [top, htoppos.ne']
    change (∑ i ∈ Finset.univ.erase i0, (hA.eigenvalues₀ i / top) ^ M) +
      (hA.eigenvalues₀ i0 / top) ^ M =
        ∑ i, (hA.eigenvalues₀ i / top) ^ M at h
    rw [htopterm] at h
    exact h.symm.trans (add_comm _ _)
  have hall : Tendsto (fun M : ℕ =>
      ∑ i : Fin (Fintype.card (SixVertexSector N n)),
        (hA.eigenvalues₀ i / top) ^ M) atTop (nhds 1) := by
    have hadd : Tendsto (fun M : ℕ =>
        1 + ∑ i ∈ (Finset.univ.erase i0), (hA.eigenvalues₀ i / top) ^ M)
        atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add hrest
    apply hadd.congr'
    exact Filter.Eventually.of_forall fun M => (hsplit M).symm
  apply hall.congr'
  filter_upwards [] with M
  simpa [A, top, hA, i0] using (hformula M).symm



theorem sixVertexSector_trace_pow_pos {N n : ℕ} (hn : n ≤ N)
    {c : ℝ} (hc : 0 < c) (M : ℕ) :
    0 < Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
  classical
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  apply Finset.sum_pos'
  · intro x hx
    exact sixVertexSectorTransfer_pow_nonneg hc.le x x
  · let x := sixVertexPackedSector N n hn
    exact ⟨x, Finset.mem_univ x, sixVertexSectorTransfer_pow_self_pos hc x⟩



theorem sixVertexSector_log_trace_div_height_tendsto_log_top
    {N n : ℕ} (hn : n ≤ N) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun M : ℕ =>
      Real.log (Matrix.trace (sixVertexSectorTransfer N n c ^ M)) / (M : ℝ))
      atTop (nhds (Real.log (sixVertexSectorTopEigenvalue N n hn c))) := by
  let A := sixVertexSectorTransfer N n c
  let top := sixVertexSectorTopEigenvalue N n hn c
  let normalized : ℕ → ℝ := fun M => Matrix.trace (A ^ M) / top ^ M
  have htoppos : 0 < top := sixVertexSectorTopEigenvalue_pos hn hc
  have hnorm : Tendsto normalized atTop (nhds 1) := by
    simpa [normalized, A, top] using
      sixVertexSector_trace_div_top_pow_tendsto_one hn hc
  have hnormpos (M : ℕ) : 0 < normalized M := by
    exact div_pos (sixVertexSector_trace_pow_pos hn hc M) (pow_pos htoppos M)
  have hlognorm : Tendsto (fun M => Real.log (normalized M)) atTop (nhds 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hnorm
    simpa using h
  have hsmall : Tendsto (fun M : ℕ => Real.log (normalized M) / (M : ℝ))
      atTop (nhds 0) :=
    hlognorm.div_atTop tendsto_natCast_atTop_atTop
  have hmain : Tendsto (fun M : ℕ =>
      Real.log top + Real.log (normalized M) / (M : ℝ))
      atTop (nhds (Real.log top)) := by
    simpa using tendsto_const_nhds.add hsmall
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with M hM
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have htoppow : top ^ M ≠ 0 := pow_ne_zero M htoppos.ne'
  have hfactor : normalized M * top ^ M = Matrix.trace (A ^ M) := by
    exact div_mul_cancel₀ _ htoppow
  rw [← hfactor, Real.log_mul (hnormpos M).ne' htoppow, Real.log_pow]
  dsimp only [normalized]
  field_simp
  ring


theorem sixVertexLambda_trace_div_pow_tendsto_one
    (N r : ℕ) (hN : Even N) (hr : r ≤ N / 2) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun M : ℕ =>
      Matrix.trace (sixVertexSectorTransfer N (N / 2 - r) c ^ M) /
        sixVertexLambda N r hN hr c ^ M) atTop (nhds 1) := by
  let hn : N / 2 - r ≤ N := (Nat.sub_le _ _).trans (Nat.div_le_self N 2)
  simpa only [sixVertexLambda] using
    (sixVertexSector_trace_div_top_pow_tendsto_one hn hc)


theorem sixVertexLambda_log_trace_div_height_tendsto
    (N r : ℕ) (hN : Even N) (hr : r ≤ N / 2) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun M : ℕ =>
      Real.log (Matrix.trace (sixVertexSectorTransfer N (N / 2 - r) c ^ M)) /
        (M : ℝ)) atTop (nhds (Real.log (sixVertexLambda N r hN hr c))) := by
  let hn : N / 2 - r ≤ N := (Nat.sub_le _ _).trans (Nat.div_le_self N 2)
  simpa only [sixVertexLambda] using
    (sixVertexSector_log_trace_div_height_tendsto_log_top hn hc)




theorem sixVertexLambda_log_trace_ratio_div_height_tendsto
    (N r : Nat) (hN : Even N) (hr : r ≤ N / 2)
    {c : Real} (hc : 0 < c) :
    Tendsto (fun M : Nat =>
      Real.log
          (Matrix.trace
                (sixVertexSectorTransfer N (N / 2 - r) c ^ M) /
            Matrix.trace
                (sixVertexSectorTransfer N (N / 2) c ^ M)) /
        (M : Real))
      atTop
      (nhds (Real.log
        (sixVertexLambda N r hN hr c /
          sixVertexLambda N 0 hN (Nat.zero_le _) c))) := by
  have hlr : 0 < sixVertexLambda N r hN hr c :=
    (sixVertexLambda_isPerronFrobenius N r hN hr hc).1
  have hl0 : 0 < sixVertexLambda N 0 hN (Nat.zero_le _) c :=
    (sixVertexLambda_isPerronFrobenius N 0 hN (Nat.zero_le _) hc).1
  rw [Real.log_div hlr.ne' hl0.ne']
  have hrLim := sixVertexLambda_log_trace_div_height_tendsto
    N r hN hr hc
  have h0Lim := sixVertexLambda_log_trace_div_height_tendsto
    N 0 hN (Nat.zero_le _) hc
  apply (hrLim.sub h0Lim).congr'
  filter_upwards [] with M
  have htr : 0 < Matrix.trace
      (sixVertexSectorTransfer N (N / 2 - r) c ^ M) :=
    sixVertexSector_trace_pow_pos
      ((Nat.sub_le _ _).trans (Nat.div_le_self N 2)) hc M
  have ht0 : 0 < Matrix.trace
      (sixVertexSectorTransfer N (N / 2) c ^ M) :=
    sixVertexSector_trace_pow_pos (Nat.div_le_self N 2) hc M
  rw [Real.log_div htr.ne' ht0.ne']
  simp only [Nat.sub_zero]
  ring

end StatMech.FrontierD
