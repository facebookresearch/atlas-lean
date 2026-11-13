/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.FrontierD.SixVertexFiniteTorus
import Code.FrontierD.SixVertexFreeEnergy

open Finset Matrix Filter Topology

namespace StatMech.FrontierD


theorem sixVertexWidthSectorIndex_le (N : ℕ) (n : Fin (N + 1)) : n.val ≤ N := by
  omega


noncomputable def sixVertexWidthSectorTopEigenvalue
    (N : ℕ) (c : ℝ) (n : Fin (N + 1)) : ℝ :=
  sixVertexSectorTopEigenvalue N n (sixVertexWidthSectorIndex_le N n) c


noncomputable def sixVertexWidthTopEigenvalue (N : ℕ) (c : ℝ) : ℝ :=
  (Finset.univ.image (sixVertexWidthSectorTopEigenvalue N c)).max'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

theorem sixVertexWidthSectorTopEigenvalue_le (N : ℕ) (c : ℝ)
    (n : Fin (N + 1)) :
    sixVertexWidthSectorTopEigenvalue N c n ≤ sixVertexWidthTopEigenvalue N c := by
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨n, Finset.mem_univ n, rfl⟩)

theorem sixVertexWidthTopEigenvalue_exists_sector (N : ℕ) (c : ℝ) :
    ∃ n : Fin (N + 1),
      sixVertexWidthSectorTopEigenvalue N c n = sixVertexWidthTopEigenvalue N c := by
  obtain ⟨n, hn, hmax⟩ := Finset.mem_image.mp
    (Finset.max'_mem (Finset.univ.image (sixVertexWidthSectorTopEigenvalue N c)) _)
  exact ⟨n, hmax⟩

theorem sixVertexWidthTopEigenvalue_pos (N : ℕ) {c : ℝ} (hc : 0 < c) :
    0 < sixVertexWidthTopEigenvalue N c := by
  let n : Fin (N + 1) := ⟨0, Nat.zero_lt_succ N⟩
  exact lt_of_lt_of_le
    (sixVertexSectorTopEigenvalue_pos (sixVertexWidthSectorIndex_le N n) hc)
    (sixVertexWidthSectorTopEigenvalue_le N c n)


noncomputable def sixVertexFixedWidthPartitionSum (N M : ℕ) (c : ℝ) : ℝ :=
  Matrix.trace (sixVertexTransfer N c ^ M)



theorem sixVertexFixedWidthPartitionSum_eq_periodicRows
    (N M : ℕ) (hM : 0 < M) (c : ℝ) :
    sixVertexFixedWidthPartitionSum N M c =
      sixVertexPeriodicRowPartitionSum N M hM c := by
  exact (sixVertexPeriodicRowPartitionSum_eq_trace N M hM c).symm



theorem sixVertexFixedWidthPartitionSum_eq_sum_sector_traces
    (N M : ℕ) (hM : 0 < M) (c : ℝ) :
    sixVertexFixedWidthPartitionSum N M c =
      ∑ n : Fin (N + 1), Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
  rw [sixVertexFixedWidthPartitionSum_eq_periodicRows N M hM c]
  exact sixVertexPeriodicRowPartitionSum_eq_sum_sector_traces N M hM c


theorem sixVertexFixedWidthPartitionSum_pos
    (N M : ℕ) (hM : 0 < M) {c : ℝ} (hc : 0 < c) :
    0 < sixVertexFixedWidthPartitionSum N M c := by
  rw [sixVertexFixedWidthPartitionSum_eq_sum_sector_traces N M hM c]
  apply Finset.sum_pos'
  · intro n hn
    exact (sixVertexSector_trace_pow_pos (sixVertexWidthSectorIndex_le N n) hc M).le
  · let n : Fin (N + 1) := ⟨0, Nat.zero_lt_succ N⟩
    exact ⟨n, Finset.mem_univ n,
      sixVertexSector_trace_pow_pos (sixVertexWidthSectorIndex_le N n) hc M⟩



noncomputable def sixVertexWidthMaxSectorCount (N : ℕ) (c : ℝ) : ℝ :=
  ∑ n : Fin (N + 1),
    if sixVertexWidthSectorTopEigenvalue N c n = sixVertexWidthTopEigenvalue N c
    then 1 else 0

theorem sixVertexWidthMaxSectorCount_pos (N : ℕ) (c : ℝ) :
    0 < sixVertexWidthMaxSectorCount N c := by
  classical
  obtain ⟨n, hn⟩ := sixVertexWidthTopEigenvalue_exists_sector N c
  unfold sixVertexWidthMaxSectorCount
  apply Finset.sum_pos'
  · intro i hi
    split_ifs <;> norm_num
  · exact ⟨n, Finset.mem_univ n, by simp [hn]⟩



theorem sixVertexFixedWidthPartitionSum_div_top_pow_tendsto
    (N : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun M : ℕ => sixVertexFixedWidthPartitionSum N M c /
      sixVertexWidthTopEigenvalue N c ^ M) atTop
      (nhds (sixVertexWidthMaxSectorCount N c)) := by
  classical
  let top := sixVertexWidthTopEigenvalue N c
  have htoppos : 0 < top := sixVertexWidthTopEigenvalue_pos N hc
  have hterm (n : Fin (N + 1)) :
      Tendsto (fun M : ℕ =>
        Matrix.trace (sixVertexSectorTransfer N n c ^ M) / top ^ M) atTop
        (nhds (if sixVertexWidthSectorTopEigenvalue N c n = top then 1 else 0)) := by
    let sectorTop := sixVertexWidthSectorTopEigenvalue N c n
    have hsectorpos : 0 < sectorTop :=
      sixVertexSectorTopEigenvalue_pos (sixVertexWidthSectorIndex_le N n) hc
    have hnorm : Tendsto (fun M : ℕ =>
        Matrix.trace (sixVertexSectorTransfer N n c ^ M) / sectorTop ^ M)
        atTop (nhds 1) := by
      simpa [sectorTop, sixVertexWidthSectorTopEigenvalue] using
        sixVertexSector_trace_div_top_pow_tendsto_one
          (sixVertexWidthSectorIndex_le N n) hc
    by_cases heq : sectorTop = top
    · simpa [sectorTop, heq] using hnorm
    · have hsectorlt : sectorTop < top :=
        lt_of_le_of_ne (sixVertexWidthSectorTopEigenvalue_le N c n) heq
      have hratio : Tendsto (fun M : ℕ => (sectorTop / top) ^ M)
          atTop (nhds 0) := by
        apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
        rw [abs_div, abs_of_pos hsectorpos, abs_of_pos htoppos]
        exact (div_lt_one htoppos).mpr hsectorlt
      have hprod := hnorm.mul hratio
      have hformula (M : ℕ) :
          (Matrix.trace (sixVertexSectorTransfer N n c ^ M) / sectorTop ^ M) *
              (sectorTop / top) ^ M =
            Matrix.trace (sixVertexSectorTransfer N n c ^ M) / top ^ M := by
        rw [div_pow]
        field_simp [pow_ne_zero M hsectorpos.ne', pow_ne_zero M htoppos.ne']
      simpa [sectorTop, heq] using hprod.congr'
        (Filter.Eventually.of_forall hformula)
  have hsum : Tendsto (fun M : ℕ =>
      ∑ n : Fin (N + 1),
        Matrix.trace (sixVertexSectorTransfer N n c ^ M) / top ^ M) atTop
      (nhds (sixVertexWidthMaxSectorCount N c)) := by
    have h := tendsto_finsetSum Finset.univ (fun n hn => hterm n)
    simpa [sixVertexWidthMaxSectorCount, top] using h
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with M hM
  rw [sixVertexFixedWidthPartitionSum_eq_sum_sector_traces N M hM c,
    Finset.sum_div]



theorem sixVertexFixedWidth_log_partition_div_height_tendsto
    (N : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun M : ℕ => Real.log (sixVertexFixedWidthPartitionSum N M c) /
      (M : ℝ)) atTop (nhds (Real.log (sixVertexWidthTopEigenvalue N c))) := by
  let top := sixVertexWidthTopEigenvalue N c
  let count := sixVertexWidthMaxSectorCount N c
  let normalized : ℕ → ℝ := fun M =>
    sixVertexFixedWidthPartitionSum N M c / top ^ M
  have htoppos : 0 < top := sixVertexWidthTopEigenvalue_pos N hc
  have hcountpos : 0 < count := sixVertexWidthMaxSectorCount_pos N c
  have hnorm : Tendsto normalized atTop (nhds count) := by
    simpa [normalized, top, count] using
      sixVertexFixedWidthPartitionSum_div_top_pow_tendsto N hc
  have hlognorm : Tendsto (fun M => Real.log (normalized M)) atTop
      (nhds (Real.log count)) :=
    (Real.continuousAt_log hcountpos.ne').tendsto.comp hnorm
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
  have hnormalizedpos : 0 < normalized M := by
    exact div_pos (sixVertexFixedWidthPartitionSum_pos N M hM hc) (pow_pos htoppos M)
  have hfactor : normalized M * top ^ M = sixVertexFixedWidthPartitionSum N M c := by
    exact div_mul_cancel₀ _ htoppow
  rw [← hfactor, Real.log_mul hnormalizedpos.ne' htoppow, Real.log_pow]
  dsimp only [normalized]
  field_simp
  ring

end StatMech.FrontierD
