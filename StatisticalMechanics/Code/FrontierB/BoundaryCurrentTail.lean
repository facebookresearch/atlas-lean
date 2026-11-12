/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierB.LocalCurrentTail

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def extendInteriorPlus (interior : Finset V)
    (s : ConfigSpace ↑interior) : ConfigSpace V :=
  fun v => if h : v ∈ interior then s ⟨v, h⟩ else true

omit [Fintype V] in
@[simp] theorem extendInteriorPlus_inside (interior : Finset V)
    (s : ConfigSpace ↑interior) (v : ↑interior) :
    extendInteriorPlus interior s v.1 = s v := by
  simp [extendInteriorPlus, v.2]

omit [Fintype V] in
@[simp] theorem extendInteriorPlus_outside (interior : Finset V)
    (s : ConfigSpace ↑interior) (v : V) (hv : v ∉ interior) :
    extendInteriorPlus interior s v = true := by
  simp [extendInteriorPlus, hv]

theorem prod_spin_extendInteriorPlus (interior : Finset V)
    (s : ConfigSpace ↑interior) (a : V → ℕ) :
    (∏ v : V, spin (extendInteriorPlus interior s) v ^ a v) =
      ∏ v : ↑interior, spin s v ^ a v.1 := by
  classical
  calc
    (∏ v : V, spin (extendInteriorPlus interior s) v ^ a v) =
        ∏ v ∈ interior, spin (extendInteriorPlus interior s) v ^ a v := by
      symm
      apply Finset.prod_subset (Finset.subset_univ interior)
      intro v hvuniv hvnot
      simp [extendInteriorPlus, hvnot]
    _ = ∏ v : ↑interior,
        spin (extendInteriorPlus interior s) v.1 ^ a v.1 := by
      exact Finset.prod_subtype interior (fun _ => Iff.rfl) _
    _ = ∏ v : ↑interior, spin s v ^ a v.1 := by
      apply Finset.prod_congr rfl
      intro v hv
      simp [spin, extendInteriorPlus, v.2]

theorem interiorSpinSum_monomial_eq (interior : Finset V)
    (n : Sharpness.Current V) :
    (∑ s : ConfigSpace ↑interior,
      ∏ e ∈ G.edgeFinset, bond (extendInteriorPlus interior s) e ^ n e) =
      if (sources G n) ∩ interior = ∅ then
        (2 : ℝ) ^ interior.card else 0 := by
  classical
  have hrewrite : ∀ s : ConfigSpace ↑interior,
      (∏ e ∈ G.edgeFinset, bond (extendInteriorPlus interior s) e ^ n e) =
        ∏ v : ↑interior, spin s v ^ incidentFlux G n v.1 := by
    intro s
    rw [prod_bond_pow_eq_prod_spin_pow]
    exact prod_spin_extendInteriorPlus interior s (incidentFlux G n)
  simp_rw [hrewrite]
  simp_rw [spin_eq_spinB]
  rw [← Fintype.prod_sum
    (fun v : ↑interior => fun b : Bool =>
      spinB b ^ incidentFlux G n v.1)]
  simp_rw [sum_spinB_pow]
  by_cases hsrc : (sources G n) ∩ interior = ∅
  · rw [if_pos hsrc]
    have heven : ∀ v : ↑interior, Even (incidentFlux G n v.1) := by
      intro v
      rw [← Nat.not_odd_iff_even]
      intro hodd
      have hvsrc : v.1 ∈ sources G n := by
        exact (Sharpness.mem_sources G).2 hodd
      have : v.1 ∈ (sources G n) ∩ interior := Finset.mem_inter.2 ⟨hvsrc, v.2⟩
      rw [hsrc] at this
      simp at this
    have hall :
        (∏ v : ↑interior,
          if Even (incidentFlux G n v.1) then (2 : ℝ) else 0) =
          ∏ _v : ↑interior, (2 : ℝ) := by
      apply Finset.prod_congr rfl
      intro v hv
      rw [if_pos (heven v)]
    rw [hall]
    simp
  · rw [if_neg hsrc]
    have hne : ∃ v : V, v ∈ sources G n ∧ v ∈ interior := by
      obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.2 hsrc
      exact ⟨v, (Finset.mem_inter.1 hv).1, (Finset.mem_inter.1 hv).2⟩
    obtain ⟨v, hvsrc, hvint⟩ := hne
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨v, hvint⟩ : ↑interior))
    have hvodd : Odd (incidentFlux G n v) := (Sharpness.mem_sources G).1 hvsrc
    rw [if_neg]
    exact Nat.not_even_iff_odd.mpr hvodd

noncomputable def boundaryPartitionJ (beta : ℝ) (J : Sym2 V → ℝ)
    (interior : Finset V) : ℝ :=
  ∑ s : ConfigSpace ↑interior,
    boltzmannJ G beta J (extendInteriorPlus interior s)

theorem boundaryPartitionJ_eq_boundaryCurrentSum
    (beta : ℝ) (J : Sym2 V → ℝ) (interior : Finset V) :
    boundaryPartitionJ G beta J interior =
      (2 : ℝ) ^ interior.card * boundaryCurrentSum G beta J interior := by
  classical
  unfold boundaryPartitionJ
  have hstep : ∀ s : ConfigSpace ↑interior,
      boltzmannJ G beta J (extendInteriorPlus interior s) =
        ∑' m : EdgeCurrent G,
          weight G beta J (ofEdgeFun G m) *
            ∏ e : G.edgeFinset,
              bond (extendInteriorPlus interior s) e.1 ^ m e := by
    intro s
    exact boltzmannJ_eq_tsum G beta J (extendInteriorPlus interior s)
  simp_rw [hstep]
  rw [← Summable.tsum_finsetSum (s := (Finset.univ : Finset (ConfigSpace ↑interior)))
    (f := fun s (m : EdgeCurrent G) =>
      weight G beta J (ofEdgeFun G m) *
        ∏ e : G.edgeFinset, bond (extendInteriorPlus interior s) e.1 ^ m e)
    (fun s _ => summable_weight_bond G beta J (extendInteriorPlus interior s))]
  have hinner : ∀ m : EdgeCurrent G,
      (∑ s : ConfigSpace ↑interior,
        weight G beta J (ofEdgeFun G m) *
          ∏ e : G.edgeFinset, bond (extendInteriorPlus interior s) e.1 ^ m e) =
        if (sources G (ofEdgeFun G m)) ∩ interior = ∅ then
          weight G beta J (ofEdgeFun G m) * (2 : ℝ) ^ interior.card else 0 := by
    intro m
    rw [← Finset.mul_sum]
    have hbonds : ∀ s : ConfigSpace ↑interior,
        (∏ e : G.edgeFinset, bond (extendInteriorPlus interior s) e.1 ^ m e) =
          ∏ e ∈ G.edgeFinset,
            bond (extendInteriorPlus interior s) e ^ (ofEdgeFun G m) e :=
      fun s => (prod_bond_pow_ofEdgeFun G (extendInteriorPlus interior s) m).symm
    simp_rw [hbonds]
    rw [interiorSpinSum_monomial_eq G interior (ofEdgeFun G m)]
    split <;> simp_all
  simp_rw [hinner]
  unfold boundaryCurrentSum
  rw [mul_comm ((2 : ℝ) ^ interior.card), ← tsum_mul_right]
  apply tsum_congr
  intro m
  split <;> simp_all

theorem boundaryPartitionJ_doubledEdgeCoupling_le
    (beta : ℝ) (J : Sym2 V → ℝ) (hbeta : 0 ≤ beta)
    (hJ : ∀ f, 0 ≤ J f) (interior : Finset V) (e : G.edgeFinset) :
    boundaryPartitionJ G beta (doubledEdgeCoupling J e.1) interior ≤
      Real.exp (beta * J e.1) * boundaryPartitionJ G beta J interior := by
  calc
    (∑ s : ConfigSpace ↑interior,
      boltzmannJ G beta (doubledEdgeCoupling J e.1)
        (extendInteriorPlus interior s)) ≤
      ∑ s : ConfigSpace ↑interior,
        Real.exp (beta * J e.1) *
          boltzmannJ G beta J (extendInteriorPlus interior s) := by
      exact Finset.sum_le_sum fun s _ =>
        boltzmannJ_doubledEdgeCoupling_le G beta J hbeta hJ e _
    _ = Real.exp (beta * J e.1) * boundaryPartitionJ G beta J interior := by
      simp only [boundaryPartitionJ, Finset.mul_sum]

theorem boundaryCurrentSum_doubledEdgeCoupling_le
    (beta : ℝ) (J : Sym2 V → ℝ) (hbeta : 0 ≤ beta)
    (hJ : ∀ f, 0 ≤ J f) (interior : Finset V) (e : G.edgeFinset) :
    boundaryCurrentSum G beta (doubledEdgeCoupling J e.1) interior ≤
      Real.exp (beta * J e.1) * boundaryCurrentSum G beta J interior := by
  have hp := boundaryPartitionJ_doubledEdgeCoupling_le G beta J hbeta hJ interior e
  rw [boundaryPartitionJ_eq_boundaryCurrentSum,
    boundaryPartitionJ_eq_boundaryCurrentSum] at hp
  have hpow : (0 : ℝ) < 2 ^ interior.card := by positivity
  nlinarith

theorem boundary_current_tail_doubling_le
    (beta : ℝ) (J : Sym2 V → ℝ) (hbeta : 0 ≤ beta)
    (hJ : ∀ f, 0 ≤ J f) (interior : Finset V) (e : G.edgeFinset)
    (K : ℕ) :
    (∑' m : EdgeCurrent G,
        if (sources G (ofEdgeFun G m)) ∩ interior = ∅ ∧ K ≤ m e then
          weight G beta J (ofEdgeFun G m) else 0) ≤
      ((2 : ℝ) ^ K)⁻¹ *
        boundaryCurrentSum G beta (doubledEdgeCoupling J e.1) interior := by
  let tail : EdgeCurrent G → ℝ := fun m =>
    if (sources G (ofEdgeFun G m)) ∩ interior = ∅ ∧ K ≤ m e then
      weight G beta J (ofEdgeFun G m) else 0
  let major : EdgeCurrent G → ℝ := fun m =>
    ((2 : ℝ) ^ K)⁻¹ *
      (if (sources G (ofEdgeFun G m)) ∩ interior = ∅ then
        weight G beta (doubledEdgeCoupling J e.1) (ofEdgeFun G m) else 0)
  have hJ' : ∀ f, 0 ≤ doubledEdgeCoupling J e.1 f :=
    doubledEdgeCoupling_nonneg J hJ e.1
  have htail_nonneg : ∀ m, 0 ≤ tail m := by
    intro m
    simp only [tail]
    split
    · exact currentWeight_nonneg G beta J hbeta hJ _
    · exact le_rfl
  have hmajor : Summable major := by
    exact (summable_boundaryCurrentSummand G beta
      (doubledEdgeCoupling J e.1) interior).mul_left (((2 : ℝ) ^ K)⁻¹)
  have hpoint : ∀ m, tail m ≤ major m := by
    intro m
    simp only [tail, major]
    by_cases hsrc : (sources G (ofEdgeFun G m)) ∩ interior = ∅
    · by_cases hm : K ≤ m e
      · simp only [hsrc, hm, and_self, if_true]
        rw [weight_doubledEdgeCoupling G beta J e m]
        have hpow : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ m e :=
          pow_le_pow_right₀ (by norm_num) hm
        have hpos : 0 < (2 : ℝ) ^ K := by positivity
        rw [inv_mul_eq_div]
        apply (le_div_iff₀ hpos).2
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hpow
          (currentWeight_nonneg G beta J hbeta hJ _)
      · simp [hsrc, hm,
          currentWeight_nonneg G beta (doubledEdgeCoupling J e.1) hbeta hJ']
    · simp [hsrc]
  calc
    (∑' m : EdgeCurrent G,
        if (sources G (ofEdgeFun G m)) ∩ interior = ∅ ∧ K ≤ m e then
          weight G beta J (ofEdgeFun G m) else 0) = ∑' m, tail m := rfl
    _ ≤ ∑' m, major m :=
      (Summable.of_nonneg_of_le htail_nonneg hpoint hmajor).tsum_le_tsum hpoint hmajor
    _ = ((2 : ℝ) ^ K)⁻¹ *
        boundaryCurrentSum G beta (doubledEdgeCoupling J e.1) interior := by
      rw [show (∑' m, major m) = ((2 : ℝ) ^ K)⁻¹ *
          ∑' m : EdgeCurrent G,
            if (sources G (ofEdgeFun G m)) ∩ interior = ∅ then
              weight G beta (doubledEdgeCoupling J e.1) (ofEdgeFun G m) else 0 by
        exact tsum_mul_left]
      rfl

theorem boundaryCurrentMeasure_edge_exponential_tail_le
    (beta : ℝ) (J : Sym2 V → ℝ) (hbeta : 0 ≤ beta)
    (hJ : ∀ f, 0 ≤ J f) (interior : Finset V) (e : G.edgeFinset)
    (K : ℕ) :
    (boundaryCurrentMeasure G beta J hbeta hJ interior : Measure (EdgeCurrent G))
        {m | K ≤ m e} ≤
      ENNReal.ofReal (Real.exp (beta * J e.1) / (2 : ℝ) ^ K) := by
  let tail : EdgeCurrent G → ℝ := fun m =>
    if (sources G (ofEdgeFun G m)) ∩ interior = ∅ ∧ K ≤ m e then
      weight G beta J (ofEdgeFun G m) else 0
  have htail_nonneg : ∀ m, 0 ≤ tail m := by
    intro m
    simp only [tail]
    split
    · exact currentWeight_nonneg G beta J hbeta hJ _
    · exact le_rfl
  have htailSummable : Summable tail := by
    refine Summable.of_nonneg_of_le htail_nonneg (fun m => ?_)
      (summable_norm_weight_ofEdgeFun G beta J).of_norm
    simp only [tail]
    split
    · exact le_rfl
    · exact currentWeight_nonneg G beta J hbeta hJ m
  have hZ : 0 < boundaryCurrentSum G beta J interior :=
    lt_of_lt_of_le Real.zero_lt_one
      (one_le_boundaryCurrentSum G beta J hbeta hJ interior)
  change (boundaryCurrentPMF G beta J hbeta hJ interior).toMeasure
    {m | K ≤ m e} ≤ _
  rw [PMF.toMeasure_apply_eq_tsum]
  have hsum :
      (∑' m : EdgeCurrent G,
        {m : EdgeCurrent G | K ≤ m e}.indicator
          (boundaryCurrentPMF G beta J hbeta hJ interior) m) =
        ENNReal.ofReal (∑' m, tail m) /
          ENNReal.ofReal (boundaryCurrentSum G beta J interior) := by
    calc
      (∑' m : EdgeCurrent G,
          {m : EdgeCurrent G | K ≤ m e}.indicator
            (boundaryCurrentPMF G beta J hbeta hJ interior) m) =
          ∑' m : EdgeCurrent G,
            ENNReal.ofReal (tail m) *
              (ENNReal.ofReal (boundaryCurrentSum G beta J interior))⁻¹ := by
        apply tsum_congr
        intro m
        by_cases hm : K ≤ m e
        · rw [Set.indicator_of_mem
            (show m ∈ {m : EdgeCurrent G | K ≤ m e} from hm)]
          rw [boundaryCurrentPMF_apply]
          by_cases hsrc : (sources G (ofEdgeFun G m)) ∩ interior = ∅
          · simp [boundaryCurrentRawMass, tail, hsrc, hm]
          · simp [boundaryCurrentRawMass, tail, hsrc]
        · rw [Set.indicator_of_notMem
            (show m ∉ {m : EdgeCurrent G | K ≤ m e} from hm)]
          simp [tail, hm]
      _ = (∑' m : EdgeCurrent G, ENNReal.ofReal (tail m)) *
          (ENNReal.ofReal (boundaryCurrentSum G beta J interior))⁻¹ :=
        ENNReal.tsum_mul_right
      _ = ENNReal.ofReal (∑' m, tail m) *
          (ENNReal.ofReal (boundaryCurrentSum G beta J interior))⁻¹ := by
        rw [ENNReal.ofReal_tsum_of_nonneg htail_nonneg htailSummable]
      _ = ENNReal.ofReal (∑' m, tail m) /
          ENNReal.ofReal (boundaryCurrentSum G beta J interior) := rfl
  rw [hsum]
  rw [ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hZ).ne' ENNReal.ofReal_ne_top]
  have hcoef : 0 ≤ Real.exp (beta * J e.1) / (2 : ℝ) ^ K :=
    div_nonneg (Real.exp_pos _).le (pow_nonneg (by norm_num) _)
  rw [← ENNReal.ofReal_mul hcoef]
  apply ENNReal.ofReal_le_ofReal
  have htail := boundary_current_tail_doubling_le
    G beta J hbeta hJ interior e K
  have hZ' := boundaryCurrentSum_doubledEdgeCoupling_le
    G beta J hbeta hJ interior e
  calc
    (∑' m, tail m) ≤ ((2 : ℝ) ^ K)⁻¹ *
        boundaryCurrentSum G beta (doubledEdgeCoupling J e.1) interior := htail
    _ ≤ ((2 : ℝ) ^ K)⁻¹ *
        (Real.exp (beta * J e.1) * boundaryCurrentSum G beta J interior) :=
      mul_le_mul_of_nonneg_left hZ' (inv_nonneg.2 (pow_nonneg (by norm_num) _))
    _ = (Real.exp (beta * J e.1) / (2 : ℝ) ^ K) *
        boundaryCurrentSum G beta J interior := by field_simp

theorem boundaryCurrentMeasure_edge_inverse_tail_le
    (beta : ℝ) (J : Sym2 V → ℝ) (hbeta : 0 ≤ beta)
    (hJ : ∀ f, 0 ≤ J f) (interior : Finset V) (e : G.edgeFinset)
    (K : ℕ) (hK : 0 < K) :
    (boundaryCurrentMeasure G beta J hbeta hJ interior : Measure (EdgeCurrent G))
        {m | K ≤ m e} ≤
      ENNReal.ofReal (Real.exp (beta * J e.1) / K) := by
  calc
    (boundaryCurrentMeasure G beta J hbeta hJ interior : Measure (EdgeCurrent G))
        {m | K ≤ m e} ≤
        ENNReal.ofReal (Real.exp (beta * J e.1) / (2 : ℝ) ^ K) :=
      boundaryCurrentMeasure_edge_exponential_tail_le
        G beta J hbeta hJ interior e K
    _ ≤ ENNReal.ofReal (Real.exp (beta * J e.1) / K) := by
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_left (Real.exp_pos _).le (Nat.cast_pos.2 hK)
      exact_mod_cast nat_le_two_pow K

end StatMech.FrontierB

