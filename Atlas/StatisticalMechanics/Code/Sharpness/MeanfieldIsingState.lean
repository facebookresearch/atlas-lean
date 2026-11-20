/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Sharpness.MeanfieldIsingFull
import Code.Ising.FVConsistencyProve
import Code.Ising.GHSThreePoint

open MeasureTheory Real Set Filter Topology
open scoped BigOperators

namespace StatMech
namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising



theorem sct_bondFinsetInternal_eq_map_edgeFinset (d n : ℕ) :
    bondFinsetInternal d n =
      (sctBoxGraph d n).edgeFinset.map
        (Function.Embedding.subtype (fun x : Site d => x ∈ box d n)).sym2Map := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    simp only [bondFinsetInternal, Finset.mem_image, Finset.mem_map]
    constructor
    · rintro ⟨p, hp, he⟩
      simp only [bondPairsInternal, Finset.mem_filter, Finset.mem_product] at hp
      rw [Sym2.eq_iff] at he
      rcases he with he | he
      · rcases he with ⟨rfl, rfl⟩
        refine ⟨s(⟨p.1, Ising.mem_boxFinset.mp hp.1.1⟩,
          ⟨p.2, Ising.mem_boxFinset.mp hp.1.2⟩), ?_, ?_⟩
        · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
          simpa [sctBoxGraph, SimpleGraph.induce_adj] using hp.2
        · rfl
      · rcases he with ⟨rfl, rfl⟩
        refine ⟨s(⟨p.2, Ising.mem_boxFinset.mp hp.1.2⟩,
          ⟨p.1, Ising.mem_boxFinset.mp hp.1.1⟩), ?_, ?_⟩
        · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
          simpa [sctBoxGraph, SimpleGraph.induce_adj,
            SimpleGraph.adj_comm] using hp.2
        · rfl
    · rintro ⟨e, he, hmap⟩
      induction e using Sym2.inductionOn with
      | _ a b =>
        refine ⟨(a.1, b.1), ?_, hmap⟩
        rw [bondPairsInternal, Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨Ising.mem_boxFinset.mpr a.2,
          Ising.mem_boxFinset.mpr b.2⟩, ?_⟩
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        simpa [sctBoxGraph, SimpleGraph.induce_adj] using he


theorem sct_internal_bond_sum_eq (d n : ℕ)
    (tau : ConfigSpace (sctBox d n)) :
    (∑ e ∈ bondFinsetInternal d n, bond (glue (minusField d) tau) e) =
      ∑ e ∈ (sctBoxGraph d n).edgeFinset, bond tau e := by
  rw [sct_bondFinsetInternal_eq_map_edgeFinset]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e _
  induction e using Sym2.inductionOn with
  | _ a b =>
    change bond (glue (minusField d) tau) s(a.1, b.1) = _
    simp [bond_mk, spin, glue, a.2, b.2]


theorem sct_internal_spin_sum_eq (d n : ℕ)
    (tau : ConfigSpace (sctBox d n)) :
    (∑ x ∈ Ising.boxFinset d n, spin (glue (minusField d) tau) x) =
      ∑ x : sctBox d n, spin tau x := by
  apply Finset.sum_bij
    (fun x hx => (⟨x, Ising.mem_boxFinset.mp hx⟩ : sctBox d n))
  · intro x _
    exact Finset.mem_univ _
  · intro x₁ _ x₂ _ heq
    exact congrArg Subtype.val heq
  · intro y _
    exact ⟨y.1, Ising.mem_boxFinset.mpr y.2, Subtype.ext rfl⟩
  · intro x hx
    simp [spin, glue, Ising.mem_boxFinset.mp hx]


theorem sct_fvWeight_eq_isingWeight (d n : ℕ) (beta h : ℝ)
    (tau : ConfigSpace (sctBox d n)) :
    fvWeight (minusField d) n (bondFinsetInternal d n) beta h tau =
      isingWeight (sctBoxGraph d n) beta h tau := by
  unfold fvWeight fvEnergy isingWeight hamiltonian
  rw [sct_internal_bond_sum_eq, sct_internal_spin_sum_eq]


theorem sct_fvZ_eq_isingZ (d n : ℕ) (beta h : ℝ) :
    fvZ (minusField d) n (bondFinsetInternal d n) beta h =
      isingZ (sctBoxGraph d n) beta h := by
  unfold fvZ isingZ
  apply Finset.sum_congr rfl
  intro tau _
  exact sct_fvWeight_eq_isingWeight d n beta h tau


theorem sct_fvProb_eq_isingProb (d n : ℕ) (beta h : ℝ)
    (tau : ConfigSpace (sctBox d n)) :
    fvProb (minusField d) n (bondFinsetInternal d n) beta h tau =
      isingProb (sctBoxGraph d n) beta h tau := by
  unfold fvProb isingProb
  rw [sct_fvWeight_eq_isingWeight, sct_fvZ_eq_isingZ]



theorem sct_integral_freeMeasure_eq_originMag (d n : ℕ) (beta h : ℝ) :
    ∫ omega, spin omega (Percolation.origin d)
      ∂(freeMeasure d n beta h : Measure (ConfigSpace (Site d))) =
      sctOriginMag d beta h n := by
  change (∫ omega, spin omega (Percolation.origin d)
    ∂(fvMeasure (minusField d) n (bondFinsetInternal d n) beta h)) = _
  rw [integral_fvMeasure_eq_sum]
  unfold sctOriginMag sctBoxMag isingExpectation
  apply Finset.sum_congr rfl
  intro tau _
  rw [sct_fvProb_eq_isingProb]
  congr 1
  simp [spin, glue, sctBoxOrigin, Percolation.origin]
  congr 2



theorem sct_integral_freeState_eq_infiniteFieldMag (d : ℕ) (beta h : ℝ)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    ∫ omega, spin omega (Percolation.origin d)
      ∂(freeState d beta h : Measure (ConfigSpace (Site d))) =
      sctInfiniteFieldMag d beta h := by
  obtain ⟨phi, hphi, hweak⟩ := freeState_isInfiniteVolumeState d beta h
  have hweakInt := hweak.tendsto_integral (spinBCF (Percolation.origin d))
  have hbox :=
    (sctOriginMag_tendsto_iSup d beta h hbeta hh).comp hphi.tendsto_atTop
  have hweakInt' : Tendsto (fun n => sctOriginMag d beta h (phi n)) atTop
      (nhds (∫ omega, spin omega (Percolation.origin d)
        ∂(freeState d beta h : Measure (ConfigSpace (Site d))))) := by
    simpa only [Function.comp_apply, spinBCF_apply,
      sct_integral_freeMeasure_eq_originMag] using hweakInt
  have hbox' : Tendsto (fun n => sctOriginMag d beta h (phi n)) atTop
      (nhds (sctInfiniteFieldMag d beta h)) := by
    simpa only [sctInfiniteFieldMag] using hbox
  exact tendsto_nhds_unique hweakInt' hbox'



section FieldMonotonicity

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



theorem isingExpectation_eq_expJ (beta h : ℝ) (f : ConfigSpace V → ℝ) :
    isingExpectation G beta h f =
      expJ G.edgeFinset (fun _ => beta) (fun _ => beta * h) f := by
  unfold isingExpectation isingProb expJ
  rw [ZJ_edgeFinset_const_eq_isingZ G]
  simp_rw [wJ_edgeFinset_const_eq_isingWeight G]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring



theorem ghsiCovariance_const_eq_cov2 (beta h : ℝ) (o x : V) :
    ghsiCovariance G (fun _ => beta) (fun _ => beta * h) o x =
      cov2 G beta h o x := by
  unfold ghsiCovariance cov2
  rw [← isingExpectation_eq_expJ G beta h,
    ← isingExpectation_eq_expJ G beta h,
    ← isingExpectation_eq_expJ G beta h]



theorem ghsiDirectionalCovariance_const_nonneg (beta h : ℝ)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (o : V) :
    0 ≤ ghsiDirectionalCovariance G (fun _ => beta) (fun _ => beta * h)
      (fun _ => beta) (fun s => spin s o) := by
  rw [ghsi_directionalCovariance_eq_sum_covariance]
  apply Finset.sum_nonneg
  intro x _
  rw [ghsiCovariance_const_eq_cov2]
  apply mul_nonneg hbeta
  by_cases hox : o = x
  · subst x
    unfold cov2
    have hm := expectation_spin_bounds G beta h hbeta hh o
    rw [expectation_spin_mul_self]
    nlinarith
  · exact cov2_nonneg G beta h hbeta hh o x hox


theorem hasDerivAt_isingExpectation_spin_field (beta h : ℝ) (o : V) :
    HasDerivAt (fun u => isingExpectation G beta u (fun s => spin s o))
      (ghsiDirectionalCovariance G (fun _ => beta) (fun _ => beta * h)
        (fun _ => beta) (fun s => spin s o)) h := by
  have hd := ghsi_hasDerivAt_expectation_fieldLine G (fun _ => beta)
    (fun _ => 0) (fun _ => beta) (fun s => spin s o) h
  have hline (u : ℝ) : ghsiFieldLine (fun _ : V => 0) (fun _ => beta) u =
      (fun _ => beta * u) := by
    funext x
    simp [ghsiFieldLine]
    ring
  have hfun : (fun u => expJ G.edgeFinset (fun _ => beta)
      (ghsiFieldLine (fun _ => 0) (fun _ => beta) u) (fun s => spin s o)) =
      (fun u => isingExpectation G beta u (fun s => spin s o)) := by
    funext u
    rw [hline, ← isingExpectation_eq_expJ G beta u]
  rw [hfun] at hd
  simpa [hline] using hd

end FieldMonotonicity



theorem sctOriginMag_monotone_field (d n : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    MonotoneOn (fun h => sctOriginMag d beta h n) (Ici 0) := by
  let G := sctBoxGraph d n
  let o := sctBoxOrigin d n
  have hd (h : ℝ) : HasDerivAt (fun u => sctOriginMag d beta u n)
      (ghsiDirectionalCovariance G (fun _ => beta) (fun _ => beta * h)
        (fun _ => beta) (fun s => spin s o)) h := by
    exact hasDerivAt_isingExpectation_spin_field G beta h o
  apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
  · intro h _
    exact (hd h).continuousAt.continuousWithinAt
  · intro h _
    exact (hd h).differentiableAt.differentiableWithinAt
  · intro h hh
    rw [(hd h).deriv]
    have hh0 : 0 ≤ h := le_of_lt (by
      simpa only [interior_Ici, mem_Ioi] using hh)
    exact ghsiDirectionalCovariance_const_nonneg G beta h hbeta hh0 o



theorem sctInfiniteFieldMag_monotone_field (d : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    MonotoneOn (fun h => sctInfiniteFieldMag d beta h) (Ici 0) := by
  intro h₁ hh₁ h₂ hh₂ hle
  unfold sctInfiniteFieldMag
  change (⨆ n, sctOriginMag d beta h₁ n) ≤
    ⨆ n, sctOriginMag d beta h₂ n
  apply ciSup_mono
  · refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact sctOriginMag_le_one d beta h₂ n
  · intro n
    exact sctOriginMag_monotone_field d n beta hbeta hh₁ hh₂ hle


theorem sctOriginMag_nonneg (d n : ℕ) (beta h : ℝ)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    0 ≤ sctOriginMag d beta h n :=
  expectation_spin_nonneg (sctBoxGraph d n) beta h hbeta hh
    (sctBoxOrigin d n)


theorem sctInfiniteFieldMag_nonneg (d : ℕ) (beta h : ℝ)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    0 ≤ sctInfiniteFieldMag d beta h := by
  unfold sctInfiniteFieldMag
  have hbdd : BddAbove (Set.range (sctOriginMag d beta h)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact sctOriginMag_le_one d beta h n
  exact (sctOriginMag_nonneg d 0 beta h hbeta hh).trans
    (le_ciSup hbdd 0)


theorem sctInfiniteFieldMag_le_one (d : ℕ) (beta h : ℝ) :
    sctInfiniteFieldMag d beta h ≤ 1 := by
  unfold sctInfiniteFieldMag
  exact ciSup_le (fun n => sctOriginMag_le_one d beta h n)


noncomputable def sctFieldToZero (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)



noncomputable def sctZeroPlusMag (d : ℕ) (beta : ℝ) : ℝ :=
  ⨅ n : ℕ, sctInfiniteFieldMag d beta (sctFieldToZero n)

theorem sctFieldToZero_pos (n : ℕ) : 0 < sctFieldToZero n := by
  unfold sctFieldToZero
  positivity

theorem sctFieldToZero_antitone : Antitone sctFieldToZero := by
  intro n m hnm
  unfold sctFieldToZero
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hnm 1



theorem sctInfiniteFieldMag_tendsto_zeroPlus (d : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Tendsto (fun n => sctInfiniteFieldMag d beta (sctFieldToZero n))
      atTop (nhds (sctZeroPlusMag d beta)) := by
  apply tendsto_atTop_ciInf
  · intro n m hnm
    have hn0 : 0 ≤ sctFieldToZero n := (sctFieldToZero_pos n).le
    have hm0 : 0 ≤ sctFieldToZero m := (sctFieldToZero_pos m).le
    exact sctInfiniteFieldMag_monotone_field d beta hbeta hm0 hn0
      (sctFieldToZero_antitone hnm)
  · refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact sctInfiniteFieldMag_nonneg d beta (sctFieldToZero n)
      hbeta (sctFieldToZero_pos n).le



theorem sct_integral_freeState_tendsto_zeroPlus (d : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Tendsto
      (fun n => ∫ omega, spin omega (Percolation.origin d)
        ∂(freeState d beta (sctFieldToZero n) :
          Measure (ConfigSpace (Site d))))
      atTop (nhds (sctZeroPlusMag d beta)) := by
  have hlim := sctInfiniteFieldMag_tendsto_zeroPlus d beta hbeta
  simpa only [sct_integral_freeState_eq_infiniteFieldMag d beta _ hbeta
    (sctFieldToZero_pos _).le] using hlim








theorem sctZeroPlus_meanfield_lower_bound_of_deriv_tendsto
    (d : ℕ) (hbdd : BddAbove (tildeBetaCIsingSet d))
    (hcrit : 0 < tildeBetaCIsing d)
    (hdiff : ∀ k : ℕ, ∀ gamma ∈ Ici (tildeBetaCIsing d),
      DifferentiableAt ℝ
        (fun b => (sctInfiniteFieldMag d b (sctFieldToZero k)) ^ 2) gamma)
    (hderiv : ∀ k : ℕ, ∀ gamma ∈ Ioi (tildeBetaCIsing d),
      Tendsto
        (fun n : ℕ => deriv
          (fun b => (sctOriginMag d b (sctFieldToZero k) (n + 1)) ^ 2) gamma)
        atTop
        (nhds (deriv
          (fun b => (sctInfiniteFieldMag d b (sctFieldToZero k)) ^ 2) gamma)))
    {beta : ℝ} (hbeta : tildeBetaCIsing d ≤ beta) :
    Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤
      sctZeroPlusMag d beta := by
  have hcrit0 : 0 ≤ tildeBetaCIsing d := hcrit.le
  have hbounds : ∀ k : ℕ,
      Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤
        sctInfiniteFieldMag d beta (sctFieldToZero k) := by
    intro k
    apply meanfield_lower_bound_of_initial_nonneg
      (tildeBetaCIsing d) hcrit
      (fun b => sctInfiniteFieldMag d b (sctFieldToZero k))
      (hdiff k)
    · intro gamma hgamma
      exact sct_infiniteField_meanfield_inequality_of_deriv_tendsto
        d gamma (sctFieldToZero k) hbdd hgamma
        (sctFieldToZero_pos k) (hderiv k gamma hgamma)
    · intro gamma hgamma
      have hgamma0 : 0 ≤ gamma := hcrit0.trans (mem_Ici.mp hgamma)
      exact sctInfiniteFieldMag_nonneg d gamma (sctFieldToZero k)
        hgamma0 (sctFieldToZero_pos k).le
    · exact hbeta
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (sctInfiniteFieldMag_tendsto_zeroPlus d beta
      (hcrit0.trans hbeta))
    (Filter.Eventually.of_forall hbounds)

end Sharpness
end StatMech
