/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.SLE.BrownianKolmogorovTail
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli









open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace StatMech.SLE


def brownianDyadicDenominator (n : Nat) : Nat := 256 ^ n


noncomputable def brownianDyadicPoint (N n k : Nat) : Real :=
  -(N : Real) + (k : Real) / brownianDyadicDenominator n


noncomputable def brownianDyadicThreshold (n : Nat) : ENNReal :=
  (2 : ENNReal)⁻¹ ^ n

theorem brownianDyadicDenominator_pos (n : Nat) :
    0 < brownianDyadicDenominator n := by
  exact pow_pos (by norm_num) n

theorem brownianDyadicPoint_succ_sub (N n k : Nat) :
    brownianDyadicPoint N n (k + 1) - brownianDyadicPoint N n k =
      ((brownianDyadicDenominator n : Nat) : Real)⁻¹ := by
  have hdenom : Ne ((brownianDyadicDenominator n : Nat) : Real) 0 := by
    exact_mod_cast (brownianDyadicDenominator_pos n).ne'
  simp only [brownianDyadicPoint]
  field_simp
  norm_num

theorem edist_brownianDyadicPoint_succ (N n k : Nat) :
    edist (brownianDyadicPoint N n k) (brownianDyadicPoint N n (k + 1)) =
      ((brownianDyadicDenominator n : Nat) : ENNReal)⁻¹ := by
  rw [edist_dist, Real.dist_eq, abs_sub_comm,
    brownianDyadicPoint_succ_sub]
  rw [abs_of_nonneg]
  · simp [ENNReal.ofReal_inv_of_pos,
      Nat.cast_pos.mpr (brownianDyadicDenominator_pos n)]
  · positivity


def brownianDyadicEdgeBadEvent (N n k : Nat) : Set (Real -> Real) :=
  {omega | brownianDyadicThreshold n <=
    edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega)
      (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega)}


theorem brownianProductLaw_brownianDyadicEdgeBadEvent_le (N n k : Nat) :
    brownianProductLaw (brownianDyadicEdgeBadEvent N n k) <=
      ((3 : NNReal) *
        (((brownianDyadicDenominator n : Nat) : ENNReal)⁻¹) ^ (2 : Real)) /
        (brownianDyadicThreshold n) ^ (4 : Nat) := by
  have h := brownianCoordinateProcess_measure_edist_ge_le
    (brownianDyadicPoint N n k) (brownianDyadicPoint N n (k + 1))
    (brownianDyadicThreshold n)
    (by simp [brownianDyadicThreshold])
    (by simp [brownianDyadicThreshold])
  rw [edist_brownianDyadicPoint_succ] at h
  exact h


def brownianDyadicBadEvent (N n : Nat) : Set (Real -> Real) :=
  ⋃ k ∈ Finset.range (2 * N * brownianDyadicDenominator n),
    brownianDyadicEdgeBadEvent N n k


theorem brownianProductLaw_brownianDyadicBadEvent_le_raw (N n : Nat) :
    brownianProductLaw (brownianDyadicBadEvent N n) <=
      (2 * N * brownianDyadicDenominator n : Nat) *
        (((3 : NNReal) *
          (((brownianDyadicDenominator n : Nat) : ENNReal)⁻¹) ^ (2 : Real)) /
          (brownianDyadicThreshold n) ^ (4 : Nat)) := by
  unfold brownianDyadicBadEvent
  calc
    brownianProductLaw
        (⋃ k ∈ Finset.range (2 * N * brownianDyadicDenominator n),
          brownianDyadicEdgeBadEvent N n k) <=
        ∑ k ∈ Finset.range (2 * N * brownianDyadicDenominator n),
          brownianProductLaw (brownianDyadicEdgeBadEvent N n k) :=
      measure_biUnion_finset_le _ _
    _ <= ∑ _k ∈ Finset.range (2 * N * brownianDyadicDenominator n),
        (((3 : NNReal) *
          (((brownianDyadicDenominator n : Nat) : ENNReal)⁻¹) ^ (2 : Real)) /
          (brownianDyadicThreshold n) ^ (4 : Nat)) := by
      exact Finset.sum_le_sum fun k _hk =>
        brownianProductLaw_brownianDyadicEdgeBadEvent_le N n k
    _ = (2 * N * brownianDyadicDenominator n : Nat) *
        (((3 : NNReal) *
          (((brownianDyadicDenominator n : Nat) : ENNReal)⁻¹) ^ (2 : Real)) /
          (brownianDyadicThreshold n) ^ (4 : Nat)) := by
      simp


theorem brownianProductLaw_brownianDyadicBadEvent_le (N n : Nat) :
    brownianProductLaw (brownianDyadicBadEvent N n) <=
      ((6 * N : Nat) : ENNReal) * ((16 : ENNReal)⁻¹) ^ n := by
  have hsquare : ((((((256 : Nat) : ENNReal))⁻¹) ^ n) ^ (2 : Nat)) =
      (((((256 : Nat) : ENNReal))⁻¹) ^ (2 : Nat)) ^ n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
  have hfour : ((((2 : ENNReal)⁻¹)⁻¹ ^ n) ^ (4 : Nat)) =
      (((2 : ENNReal)⁻¹)⁻¹ ^ (4 : Nat)) ^ n := by
    rw [← pow_mul, Nat.mul_comm n 4, pow_mul]
  have hbase : (256 : ENNReal) * (256 : ENNReal)⁻¹ ^ (2 : Nat) * 16 =
      (16 : ENNReal)⁻¹ := by
    change ((256 : NNReal) : ENNReal) *
        (((256 : NNReal) : ENNReal)⁻¹) ^ (2 : Nat) *
        ((16 : NNReal) : ENNReal) = (((16 : NNReal) : ENNReal))⁻¹
    rw [← ENNReal.coe_inv (show Ne (256 : NNReal) 0 by norm_num),
      ← ENNReal.coe_pow, ← ENNReal.coe_mul, ← ENNReal.coe_mul,
      ← ENNReal.coe_inv (show Ne (16 : NNReal) 0 by norm_num)]
    norm_num
  have hnumeric : (256 : ENNReal) ^ n *
      (((256 : ENNReal)⁻¹) ^ (2 : Nat)) ^ n * (16 : ENNReal) ^ n =
      ((16 : ENNReal)⁻¹) ^ n := by
    calc
      (256 : ENNReal) ^ n * (((256 : ENNReal)⁻¹) ^ (2 : Nat)) ^ n *
          (16 : ENNReal) ^ n =
          ((256 : ENNReal) * (256 : ENNReal)⁻¹ ^ (2 : Nat) * 16) ^ n := by
        rw [mul_pow, mul_pow]
      _ = ((16 : ENNReal)⁻¹) ^ n := congrArg (fun x => x ^ n) hbase
  refine (brownianProductLaw_brownianDyadicBadEvent_le_raw N n).trans_eq ?_
  simp only [brownianDyadicDenominator, brownianDyadicThreshold,
    Nat.cast_mul, Nat.cast_pow, ENNReal.rpow_ofNat,
    ENNReal.inv_pow, div_eq_mul_inv]
  rw [hsquare, hfour]
  norm_num
  calc
    (2 : ENNReal) * (N : ENNReal) * (256 : ENNReal) ^ n *
        ((3 : ENNReal) * (((256 : ENNReal)⁻¹) ^ (2 : Nat)) ^ n *
          (16 : ENNReal) ^ n) =
        (6 : ENNReal) * (N : ENNReal) *
          ((256 : ENNReal) ^ n * (((256 : ENNReal)⁻¹) ^ (2 : Nat)) ^ n *
            (16 : ENNReal) ^ n) := by
      rw [show (6 : ENNReal) = 2 * 3 by norm_num]
      ac_rfl
    _ = (6 : ENNReal) * (N : ENNReal) * ((16 : ENNReal)⁻¹) ^ n := by
      rw [hnumeric]



theorem tsum_brownianProductLaw_brownianDyadicBadEvent_ne_top (N : Nat) :
    Ne (∑' n : Nat, brownianProductLaw (brownianDyadicBadEvent N n))
      (⊤ : ENNReal) := by
  apply ne_top_of_le_ne_top
    (b := ∑' n : Nat,
      ((6 * N : Nat) : ENNReal) * ((16 : ENNReal)⁻¹) ^ n)
  · rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top (6 * N))
      (ENNReal.inv_ne_top.mpr <| ne_of_gt <|
        tsub_pos_iff_lt.mpr <| ENNReal.inv_lt_one.2 <| by norm_num)
  · exact ENNReal.tsum_le_tsum
      (fun n => brownianProductLaw_brownianDyadicBadEvent_le N n)



theorem brownianCoordinateProcess_ae_eventually_dyadicEdge_lt (N : Nat) :
    ∀ᵐ omega ∂brownianProductLaw, ∀ᶠ n in atTop,
      ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n),
        edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega)
          (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) <
            brownianDyadicThreshold n := by
  have hbc : ∀ᵐ omega ∂brownianProductLaw, ∀ᶠ n in atTop,
      omega ∉ brownianDyadicBadEvent N n :=
    ae_eventually_notMem
      (tsum_brownianProductLaw_brownianDyadicBadEvent_ne_top N)
  filter_upwards [hbc] with omega homega
  filter_upwards [homega] with n hn
  intro k hk
  have hedge : omega ∉ brownianDyadicEdgeBadEvent N n k := by
    intro hkbad
    apply hn
    exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, hkbad⟩⟩
  simpa only [brownianDyadicEdgeBadEvent, Set.mem_setOf_eq, not_le] using hedge



theorem brownianCoordinateProcess_ae_forall_eventually_dyadicEdge_lt :
    ∀ᵐ omega ∂brownianProductLaw, ∀ N : Nat, ∀ᶠ n in atTop,
      ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n),
        edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega)
          (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) <
            brownianDyadicThreshold n := by
  rw [ae_all_iff]
  exact brownianCoordinateProcess_ae_eventually_dyadicEdge_lt



theorem edist_brownianCoordinateProcess_dyadicPoint_le
    (omega : Real -> Real) (N n a b : Nat)
    (hedge : ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n),
      edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega)
        (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) <
          brownianDyadicThreshold n)
    (hab : a <= b) (hb : b <= 2 * N * brownianDyadicDenominator n) :
    edist (brownianCoordinateProcess (brownianDyadicPoint N n a) omega)
        (brownianCoordinateProcess (brownianDyadicPoint N n b) omega) <=
      (b - a : Nat) * brownianDyadicThreshold n := by
  calc
    edist (brownianCoordinateProcess (brownianDyadicPoint N n a) omega)
        (brownianCoordinateProcess (brownianDyadicPoint N n b) omega) <=
        ∑ k ∈ Finset.Ico a b, brownianDyadicThreshold n := by
      apply edist_le_Ico_sum_of_edist_le
      · exact hab
      · intro k _hka hkb
        exact (hedge k (Finset.mem_range.2 <|
          hkb.trans_le hb)).le
    _ = (b - a : Nat) * brownianDyadicThreshold n := by
      simp [nsmul_eq_mul]

end StatMech.SLE
