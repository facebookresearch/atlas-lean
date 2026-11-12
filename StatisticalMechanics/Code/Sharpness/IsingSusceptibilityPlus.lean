/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Sharpness.HighTempPlusBox
import Code.Ising.IsingPlusTIFromPlacement
import Code.IsingFK.CorrelationMonotone

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators StatMech

namespace StatMech
namespace Sharpness

open Ising Lattice Percolation ConfigSpace

variable {d : ℕ}


theorem plusCorr_shift (beta : ℝ) (hbeta : 0 ≤ beta)
    (g : Multiplicative (Site d)) (x y : Site d) :
    plusCorr d beta (g • x) (g • y) = plusCorr d beta x y := by
  let mu : Measure (ConfigSpace (Site d)) := plusState d beta 0
  have hti := iptp_plusState_isTranslationInvariant (d := d) hbeta
    (by norm_num : (0 : ℝ) ≤ 0)
  unfold plusCorr
  calc
    (∫ omega, spin omega (g • x) * spin omega (g • y)
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) =
      ∫ omega, spin omega (g • x) * spin omega (g • y)
        ∂Measure.map (ConfigSpace.shift g)
          (plusState d beta 0 : Measure (ConfigSpace (Site d))) := by
            rw [hti.map_eq g]
    _ = ∫ omega,
          spin (ConfigSpace.shift g omega) (g • x) *
            spin (ConfigSpace.shift g omega) (g • y)
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))) := by
      change (∫ omega, spinPairBCF (g • x) (g • y) omega
          ∂Measure.map (ConfigSpace.shift g)
            (plusState d beta 0 : Measure (ConfigSpace (Site d)))) =
        ∫ omega, spinPairBCF (g • x) (g • y)
          (ConfigSpace.shift g omega)
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))
      rw [integral_map (continuous_shift g).measurable.aemeasurable
        (spinPairBCF (g • x) (g • y)).continuous.aestronglyMeasurable]
    _ = _ := by simp_rw [iptp_spin_shift]


theorem gvPlus_pair_nonneg (Lambda : Finset (Site d))
    (beta : ℝ) (hbeta : 0 ≤ beta) (a b : {v // v ∈ Lambda}) :
    0 ≤ ∫ omega, spin omega a.1 * spin omega b.1
      ∂(gvPlusMeasure Lambda beta 0) := by
  rw [gvPlus_pair_eq_vertexField, ← vertexGhost_twoPoint_eq]
  apply twoPointJ_nonneg
  · exact hbeta
  · intro e
    induction e using Sym2.inductionOn with
    | _ x y =>
        cases x <;> cases y <;>
          simp [vertexGhostCoupling, unitEdgeCoupling_nonneg,
            plusBoundaryField_nonneg]


theorem plusCorr_nonneg (beta : ℝ) (hbeta : 0 ≤ beta) (x y : Site d) :
    0 ≤ plusCorr d beta x y := by
  obtain ⟨phi, hphi, hconv⟩ := plusState_isInfiniteVolumeState d beta 0
  obtain ⟨R, hR⟩ := finite_subset_box ({x, y} : Set (Site d))
    (Set.toFinite _)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds
    (plusMeasure_pair_tendsto beta phi hconv x y)
  filter_upwards
    [hphi.tendsto_atTop.eventually (Filter.eventually_ge_atTop R)] with n hn
  have hx : x ∈ boxFinset d (phi n) := by
    rw [mem_boxFinset, mem_box]
    intro i
    exact (hR (by simp) i).trans hn
  have hy : y ∈ boxFinset d (phi n) := by
    rw [mem_boxFinset, mem_box]
    intro i
    exact (hR (by simp) i).trans hn
  rw [← iptp_gvPlusMeasure_eq_plusMeasure]
  exact gvPlus_pair_nonneg (boxFinset d (phi n)) beta hbeta
    ⟨x, hx⟩ ⟨y, hy⟩


theorem plusCorr_le_one (beta : ℝ) (x y : Site d) :
    plusCorr d beta x y ≤ 1 := by
  unfold plusCorr
  have hf : ∀ omega : ConfigSpace (Site d),
      spin omega x * spin omega y ≤ (1 : ℝ) := by
    intro omega
    rcases spin_eq_pm omega x with hx | hx <;>
      rcases spin_eq_pm omega y with hy | hy <;> rw [hx, hy] <;> norm_num
  calc
    (∫ omega, spin omega x * spin omega y
        ∂(plusState d beta 0 : Measure (ConfigSpace (Site d)))) ≤
        ∫ _omega, (1 : ℝ)
          ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))) := by
      apply integral_mono
      · exact (spinPairBCF x y).integrable _
      · exact integrable_const 1
      · exact hf
    _ = 1 := by simp


theorem plusCorr_eq_origin_translate (beta : ℝ) (hbeta : 0 ≤ beta)
    (x y : Site d) :
    plusCorr d beta x y =
      plusCorr d beta (Percolation.origin d) (y - x) := by
  let g : Multiplicative (Site d) := Multiplicative.ofAdd x
  have h := plusCorr_shift beta hbeta g (Percolation.origin d) (y - x)
  have hg0 : g • Percolation.origin d = x := by
    ext i
    simp [g, Percolation.origin]
  have hgy : g • (y - x) = y := by
    ext i
    simp [g]
  rw [hg0, hgy] at h
  exact h


noncomputable def plusCorrWindowSum (d : ℕ) (beta : ℝ)
    (L : Finset (Site d)) : ℝ :=
  ∑ z ∈ L, plusCorr d beta (Percolation.origin d) z


noncomputable def plusCorrWindowSup (d : ℕ) (beta : ℝ) (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ L : Finset (Site d), L.card ≤ n ∧
    r = plusCorrWindowSum d beta L}

theorem plusCorrWindowSet_nonempty (beta : ℝ) (n : ℕ) :
    ({r : ℝ | ∃ L : Finset (Site d), L.card ≤ n ∧
      r = plusCorrWindowSum d beta L} : Set ℝ).Nonempty := by
  refine ⟨0, ∅, by simp, ?_⟩
  simp [plusCorrWindowSum]

theorem plusCorrWindowSet_bddAbove (beta : ℝ) (n : ℕ) :
    BddAbove {r : ℝ | ∃ L : Finset (Site d), L.card ≤ n ∧
      r = plusCorrWindowSum d beta L} := by
  refine ⟨n, ?_⟩
  rintro r ⟨L, hcard, rfl⟩
  unfold plusCorrWindowSum
  calc
    (∑ z ∈ L, plusCorr d beta (Percolation.origin d) z) ≤
        ∑ _z ∈ L, (1 : ℝ) := by
      exact Finset.sum_le_sum (fun z _ ↦ plusCorr_le_one beta _ _)
    _ = L.card := by simp
    _ ≤ n := by exact_mod_cast hcard

theorem plusCorrWindowSum_le_sup (beta : ℝ) (n : ℕ)
    (L : Finset (Site d)) (hcard : L.card ≤ n) :
    plusCorrWindowSum d beta L ≤ plusCorrWindowSup d beta n := by
  apply le_csSup (plusCorrWindowSet_bddAbove (d := d) beta n)
  exact ⟨L, hcard, rfl⟩

theorem plusCorrWindowSup_nonneg (beta : ℝ) (n : ℕ) :
    0 ≤ plusCorrWindowSup d beta n := by
  apply le_csSup (plusCorrWindowSet_bddAbove (d := d) beta n)
  exact ⟨∅, by simp, by simp [plusCorrWindowSum]⟩


theorem plusCorr_translatedWindow_le_sup
    (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ)
    (L : Finset (Site d)) (hcard : L.card ≤ n) (y : Site d) :
    (∑ z ∈ L, plusCorr d beta y z) ≤ plusCorrWindowSup d beta n := by
  let shiftBack : Site d → Site d := fun z ↦ z - y
  have hinj : Function.Injective shiftBack := by
    intro a b hab
    dsimp [shiftBack] at hab
    have h := congrArg (fun z ↦ z + y) hab
    simpa using h
  have hsum : (∑ z ∈ L, plusCorr d beta y z) =
      plusCorrWindowSum d beta (L.image shiftBack) := by
    unfold plusCorrWindowSum
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro z _
      exact plusCorr_eq_origin_translate beta hbeta y z
    · intro a _ b _ hab
      exact hinj hab
  rw [hsum]
  apply plusCorrWindowSum_le_sup beta n
  rw [Finset.card_image_of_injective L hinj]
  exact hcard


theorem plusCorrWindowSum_self_bound
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (T : Finset (Site d)) (ho : Percolation.origin d ∈ T)
    (L : Finset (Site d)) (n : ℕ) (hcard : L.card ≤ n) :
    plusCorrWindowSum d beta L ≤
      (T.card : ℝ) + phiIsing d beta T * plusCorrWindowSup d beta n := by
  let w : Site d × Site d → ℝ := fun e ↦
    Real.tanh beta * corrOriginInner d beta T e.1
  have hw : ∀ e, 0 ≤ w e := by
    intro e
    apply mul_nonneg
    · rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr hbeta)
        (Real.cosh_pos _).le
    · exact corrOriginInner_nonneg d hbeta T e.1
  have hinside :
      (∑ z ∈ L ∩ T, plusCorr d beta (Percolation.origin d) z) ≤
        (T.card : ℝ) := by
    calc
      (∑ z ∈ L ∩ T, plusCorr d beta (Percolation.origin d) z) ≤
          ∑ _z ∈ L ∩ T, (1 : ℝ) := by
        exact Finset.sum_le_sum (fun z _ ↦ plusCorr_le_one beta _ _)
      _ = (L ∩ T).card := by simp
      _ ≤ T.card := by exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  unfold plusCorrWindowSum
  rw [← Finset.sum_inter_add_sum_diff L T
    (fun z ↦ plusCorr d beta (Percolation.origin d) z)]
  apply add_le_add hinside
  calc
    (∑ z ∈ L \ T, plusCorr d beta (Percolation.origin d) z) ≤
        ∑ z ∈ L \ T, simonBoundaryPlus beta T
          (Percolation.origin d) z := by
      apply Finset.sum_le_sum
      intro z hz
      exact plusCorr_simon beta hbeta T ho z (Finset.mem_sdiff.mp hz).2
    _ = ∑ e ∈ boundaryEdges d T, w e *
          (∑ z ∈ L \ T, plusCorr d beta e.2 z) := by
      unfold simonBoundaryPlus w
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.mul_sum]
    _ ≤ ∑ e ∈ boundaryEdges d T,
          w e * plusCorrWindowSup d beta n := by
      apply Finset.sum_le_sum
      intro e _
      apply mul_le_mul_of_nonneg_left _ (hw e)
      apply plusCorr_translatedWindow_le_sup beta hbeta n (L \ T)
      exact (Finset.card_le_card Finset.sdiff_subset).trans hcard
    _ = phiIsing d beta T * plusCorrWindowSup d beta n := by
      unfold phiIsing w
      rw [Finset.mul_sum, Finset.sum_mul]


theorem plusCorrWindowSup_self_bound
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (T : Finset (Site d)) (ho : Percolation.origin d ∈ T) (n : ℕ) :
    plusCorrWindowSup d beta n ≤
      (T.card : ℝ) + phiIsing d beta T * plusCorrWindowSup d beta n := by
  unfold plusCorrWindowSup
  apply csSup_le (plusCorrWindowSet_nonempty (d := d) beta n)
  rintro r ⟨L, hcard, rfl⟩
  exact plusCorrWindowSum_self_bound beta hbeta T ho L n hcard


theorem plusCorr_summable_of_phi_lt_one
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (T : Finset (Site d)) (ho : Percolation.origin d ∈ T)
    (hphi : phiIsing d beta T < 1) :
    Summable (plusCorr d beta (Percolation.origin d)) := by
  refine summable_of_sum_le
    (c := (T.card : ℝ) / (1 - phiIsing d beta T))
    (fun z ↦ plusCorr_nonneg beta hbeta (Percolation.origin d) z) ?_
  intro L
  have hsup := plusCorrWindowSup_self_bound beta hbeta T ho L.card
  have hbound : plusCorrWindowSup d beta L.card ≤
      (T.card : ℝ) / (1 - phiIsing d beta T) := by
    rw [le_div_iff₀ (sub_pos.mpr hphi)]
    nlinarith
  exact (plusCorrWindowSum_le_sup beta L.card L le_rfl).trans hbound



theorem freeCorr_mono_beta {beta gamma : ℝ}
    (hbeta : 0 ≤ beta) (hbg : beta ≤ gamma)
    (S : Finset (Site d)) (a b : {v // v ∈ S}) :
    freeCorr d beta S a b ≤ freeCorr d gamma S a b := by
  by_cases hab : a = b
  · simp [freeCorr, hab]
  · simp only [freeCorr, if_neg hab]
    exact IsingFK.twoPoint_monotone (graphS d S) 0 le_rfl a b
      hbeta (le_trans hbeta hbg) hbg

theorem corrOriginInner_mono_beta {beta gamma : ℝ}
    (hbeta : 0 ≤ beta) (hbg : beta ≤ gamma)
    (S : Finset (Site d)) (x : Site d) :
    corrOriginInner d beta S x ≤ corrOriginInner d gamma S x := by
  unfold corrOriginInner
  split
  · split
    · exact freeCorr_mono_beta hbeta hbg S _ _
    · rfl
  · rfl



theorem phiIsing_mono {beta gamma : ℝ}
    (hbeta : 0 ≤ beta) (hbg : beta ≤ gamma)
    (S : Finset (Site d)) :
    phiIsing d beta S ≤ phiIsing d gamma S := by
  unfold phiIsing
  have hsum : (∑ e ∈ boundaryEdges d S,
      corrOriginInner d beta S e.1) ≤
      ∑ e ∈ boundaryEdges d S, corrOriginInner d gamma S e.1 :=
    Finset.sum_le_sum (fun e _ ↦ corrOriginInner_mono_beta hbeta hbg S e.1)
  have htanh : Real.tanh beta ≤ Real.tanh gamma :=
    by
      by_contra h
      have hlt : Real.tanh gamma < Real.tanh beta := lt_of_not_ge h
      have ha := Real.artanh_lt_artanh (Real.neg_one_lt_tanh gamma)
        (Real.tanh_lt_one beta) hlt
      rw [Real.artanh_tanh, Real.artanh_tanh] at ha
      exact (not_lt_of_ge hbg) ha
  have htbeta : 0 ≤ Real.tanh beta := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hbeta)
      (Real.cosh_pos _).le
  have hsumgamma : 0 ≤ ∑ e ∈ boundaryEdges d S,
      corrOriginInner d gamma S e.1 :=
    Finset.sum_nonneg (fun e _ ↦ corrOriginInner_nonneg d
      (le_trans hbeta hbg) S e.1)
  exact (mul_le_mul_of_nonneg_left hsum htbeta).trans
    (mul_le_mul_of_nonneg_right htanh hsumgamma)



theorem exists_phiIsing_witness_of_lt_tildeBetaCIsing
    {beta : ℝ} (hbeta : 0 ≤ beta) (hlt : beta < tildeBetaCIsing d) :
    ∃ S : Finset (Site d), Percolation.origin d ∈ S ∧
      phiIsing d beta S < 1 := by
  unfold tildeBetaCIsing at hlt
  have hne : (tildeBetaCIsingSet d).Nonempty := by
    refine ⟨0, le_rfl, {Percolation.origin d}, by simp, ?_⟩
    simp [phiIsing]
  obtain ⟨gamma, hgamma, hbg⟩ := exists_lt_of_lt_csSup hne hlt
  obtain ⟨hgamma0, S, h0S, hphi⟩ := hgamma
  exact ⟨S, h0S, (phiIsing_mono hbeta hbg.le S).trans_lt hphi⟩



theorem finite_susceptibility_of_lt_tildeBetaCIsing
    {beta : ℝ} (hbeta : 0 ≤ beta) (hlt : beta < tildeBetaCIsing d) :
    ∃ S : Finset (Site d),
      Percolation.origin d ∈ S ∧
      phiIsing d beta S < 1 ∧
      Summable (plusCorr d beta (Percolation.origin d)) := by
  obtain ⟨S, h0S, hphi⟩ :=
    exists_phiIsing_witness_of_lt_tildeBetaCIsing hbeta hlt
  exact ⟨S, h0S, hphi,
    plusCorr_summable_of_phi_lt_one beta hbeta S h0S hphi⟩

end Sharpness
end StatMech
