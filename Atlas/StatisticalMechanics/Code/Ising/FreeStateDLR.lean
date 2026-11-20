/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Ising.FVConsistencyProve

open MeasureTheory Set
open scoped BigOperators BoundedContinuousFunction

namespace StatMech.Ising

open StatMech.Lattice

variable {d : Nat}



theorem bondFinsetTouch_subset_bondFinsetInternal {n m : Nat}
    (hnm : n + 1 <= m) :
    bondFinsetTouch d n ⊆ bondFinsetInternal d m := by
  intro e he
  rw [bondFinsetTouch, Finset.mem_image] at he
  obtain ⟨p, hp, rfl⟩ := he
  rw [bondPairsTouch, Finset.mem_filter] at hp
  have hpbox := hp.1
  rw [Finset.mem_product] at hpbox
  have hp1 : p.1 ∈ box d (n + 1) := mem_boxFinset.mp hpbox.1
  have hp2 : p.2 ∈ box d (n + 1) := mem_boxFinset.mp hpbox.2
  have hadj := hp.2.1
  rw [bondFinsetInternal, Finset.mem_image]
  refine ⟨p, ?_, rfl⟩
  simp only [bondPairsInternal, Finset.mem_filter, Finset.mem_product,
    mem_boxFinset]
  exact ⟨⟨box_mono d hnm hp1, box_mono d hnm hp2⟩, hadj⟩




theorem bond_sum_diff_eq_of_touch_subset {n m : Nat} (hnm : n <= m)
    (eta : ConfigSpace (Site d)) (B : Finset (Sym2 (Site d)))
    (hsub : bondFinsetTouch d n ⊆ B)
    (hB : ∀ e ∈ B, e ∈ (hypercubicLattice d).edgeSet)
    (sigma : {x // x ∈ box d m} → Bool)
    (tau : {x // x ∈ box d n} → Bool) :
    (∑ e ∈ B, bond (glue eta (ovrBox hnm sigma tau)) e)
        - (∑ e ∈ B, bond (glue eta sigma) e)
      = (∑ e ∈ bondFinsetTouch d n,
          bond (glue eta (ovrBox hnm sigma tau)) e)
        - (∑ e ∈ bondFinsetTouch d n, bond (glue eta sigma) e) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine (Finset.sum_subset hsub (fun e heB heN => ?_)).symm
  rw [bond_glue_ovrBox_eq_of_notMem hnm eta sigma tau (hB e heB) heN,
    sub_self]



theorem fv_energy_decomp_outer {n m : Nat} (hnm : n <= m)
    (eta : ConfigSpace (Site d)) (B : Finset (Sym2 (Site d)))
    (hsub : bondFinsetTouch d n ⊆ B)
    (hB : ∀ e ∈ B, e ∈ (hypercubicLattice d).edgeSet)
    (h : Real) (sigma : {x // x ∈ box d m} → Bool)
    (tau : {x // x ∈ box d n} → Bool) :
    fvEnergy eta m B h sigma
        + fvEnergy (glue eta sigma) n (bondFinsetTouch d n) h tau
      = fvEnergy eta m B h (ovrBox hnm sigma tau)
        + fvEnergy (glue eta (ovrBox hnm sigma tau)) n
            (bondFinsetTouch d n) h (resBox hnm sigma) := by
  unfold fvEnergy
  rw [glue_glue_eq_glue_ovrBox hnm eta sigma tau,
    glue_glue_eq_glue_ovrBox hnm eta (ovrBox hnm sigma tau)
      (resBox hnm sigma),
    ovrBox_ovrBox_resBox hnm sigma tau]
  have hb := bond_sum_diff_eq_of_touch_subset hnm eta B hsub hB sigma tau
  have hs := spin_sum_diff_eq hnm eta sigma tau
  linear_combination hb + h * hs


theorem fvWeight_spec_symm_outer {n m : Nat} (hnm : n <= m)
    (eta : ConfigSpace (Site d)) (B : Finset (Sym2 (Site d)))
    (hsub : bondFinsetTouch d n ⊆ B)
    (hB : ∀ e ∈ B, e ∈ (hypercubicLattice d).edgeSet)
    (beta h : Real) (sigma : {x // x ∈ box d m} → Bool)
    (tau : {x // x ∈ box d n} → Bool) :
    fvWeight eta m B beta h sigma
        * fvWeight (glue eta sigma) n (bondFinsetTouch d n) beta h tau
      = fvWeight eta m B beta h (ovrBox hnm sigma tau)
        * fvWeight (glue eta (ovrBox hnm sigma tau)) n
            (bondFinsetTouch d n) beta h (resBox hnm sigma) := by
  unfold fvWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have hE := fv_energy_decomp_outer hnm eta B hsub hB h sigma tau
  ring_nf
  linear_combination (-beta) * hE


theorem consistency_double_sum_outer {n m : Nat} (hnm : n <= m)
    (eta : ConfigSpace (Site d)) (B : Finset (Sym2 (Site d)))
    (hsub : bondFinsetTouch d n ⊆ B)
    (hB : ∀ e ∈ B, e ∈ (hypercubicLattice d).edgeSet)
    (beta h : Real) (g : ConfigSpace (Site d) → Real) :
    (∑ sigma : {x // x ∈ box d m} → Bool,
        fvProb eta m B beta h sigma
          * ∑ tau : {x // x ∈ box d n} → Bool,
              fvProb (glue eta sigma) n (bondFinsetTouch d n) beta h tau
                * g (glue (glue eta sigma) tau))
      = ∑ sigma : {x // x ∈ box d m} → Bool,
          fvProb eta m B beta h sigma * g (glue eta sigma) := by
  set F : (({x // x ∈ box d m} → Bool) ×
      ({x // x ∈ box d n} → Bool)) → Real :=
    fun p => fvProb eta m B beta h p.1
      * (fvProb (glue eta p.1) n (bondFinsetTouch d n) beta h p.2
        * g (glue (glue eta p.1) p.2)) with hF
  have hLHS : (∑ sigma : {x // x ∈ box d m} → Bool,
      fvProb eta m B beta h sigma
        * ∑ tau : {x // x ∈ box d n} → Bool,
            fvProb (glue eta sigma) n (bondFinsetTouch d n) beta h tau
              * g (glue (glue eta sigma) tau)) = ∑ p, F p := by
    rw [Fintype.sum_prod_type (f := F)]
    refine Finset.sum_congr rfl (fun sigma _ => ?_)
    rw [Finset.mul_sum]
  rw [hLHS, ← Function.Bijective.sum_comp (swapPair_bijective hnm) F]
  have hpoint : ∀ p : (({x // x ∈ box d m} → Bool) ×
      ({x // x ∈ box d n} → Bool)),
      F (swapPair hnm p) = fvProb eta m B beta h p.1
        * (fvProb (glue eta p.1) n (bondFinsetTouch d n) beta h p.2
          * g (glue eta p.1)) := by
    rintro ⟨sigma, tau⟩
    simp only [hF, swapPair]
    have harg : glue (glue eta (ovrBox hnm sigma tau)) (resBox hnm sigma)
        = glue eta sigma := by
      rw [glue_glue_eq_glue_ovrBox hnm eta (ovrBox hnm sigma tau)
        (resBox hnm sigma), ovrBox_ovrBox_resBox hnm sigma tau]
    rw [harg]
    have hprob : fvProb eta m B beta h (ovrBox hnm sigma tau)
          * fvProb (glue eta (ovrBox hnm sigma tau)) n
              (bondFinsetTouch d n) beta h (resBox hnm sigma)
        = fvProb eta m B beta h sigma
          * fvProb (glue eta sigma) n (bondFinsetTouch d n) beta h tau := by
      unfold fvProb
      have hagree : ∀ x ∉ box d n,
          glue eta (ovrBox hnm sigma tau) x = glue eta sigma x :=
        fun x hx => glue_ovrBox_eq_off_box hnm eta sigma tau hx
      rw [fvZ_eq_of_agree_off_box (bondFinsetTouch d n) beta h hagree]
      have hw := fvWeight_spec_symm_outer hnm eta B hsub hB beta h sigma tau
      rw [div_mul_div_comm, div_mul_div_comm, hw]
    calc
      fvProb eta m B beta h (ovrBox hnm sigma tau)
          * (fvProb (glue eta (ovrBox hnm sigma tau)) n
              (bondFinsetTouch d n) beta h (resBox hnm sigma)
            * g (glue eta sigma))
          = (fvProb eta m B beta h (ovrBox hnm sigma tau)
              * fvProb (glue eta (ovrBox hnm sigma tau)) n
                (bondFinsetTouch d n) beta h (resBox hnm sigma))
              * g (glue eta sigma) := by ring
      _ = (fvProb eta m B beta h sigma
              * fvProb (glue eta sigma) n (bondFinsetTouch d n) beta h tau)
            * g (glue eta sigma) := by rw [hprob]
      _ = fvProb eta m B beta h sigma
          * (fvProb (glue eta sigma) n (bondFinsetTouch d n) beta h tau
            * g (glue eta sigma)) := by ring
  rw [Finset.sum_congr rfl (fun p _ => hpoint p), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun sigma _ => ?_)
  have hcollapse : (∑ tau : {x // x ∈ box d n} → Bool,
      fvProb eta m B beta h sigma
        * (fvProb (glue eta sigma) n (bondFinsetTouch d n) beta h tau
          * g (glue eta sigma)))
      = fvProb eta m B beta h sigma * g (glue eta sigma)
        * (∑ tau : {x // x ∈ box d n} → Bool,
            fvProb (glue eta sigma) n (bondFinsetTouch d n) beta h tau) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun tau _ => ?_)
    ring
  rw [hcollapse,
    fvProb_sum_eq_one (glue eta sigma) n (bondFinsetTouch d n) beta h,
    mul_one]



theorem freeMeasure_specApply_integral_eq {n m : Nat} (hnm : n + 1 <= m)
    (beta h : Real) (f : ConfigSpace (Site d) →ᵇ Real) :
    (∫ omega, specApply n (bondFinsetTouch d n) beta h
        (f : ConfigSpace (Site d) → Real) omega
      ∂(freeMeasure d m beta h : Measure (ConfigSpace (Site d))))
      = ∫ omega, f omega
        ∂(freeMeasure d m beta h : Measure (ConfigSpace (Site d))) := by
  have hnm' : n <= m := by omega
  change (∫ omega, specApply n (bondFinsetTouch d n) beta h
      (f : ConfigSpace (Site d) → Real) omega
    ∂(fvMeasure (minusField d) m (bondFinsetInternal d m) beta h))
    = ∫ omega, f omega
      ∂(fvMeasure (minusField d) m (bondFinsetInternal d m) beta h)
  rw [integral_fvMeasure_eq_sum (minusField d) m
      (bondFinsetInternal d m) beta h
      (specApply n (bondFinsetTouch d n) beta h
        (f : ConfigSpace (Site d) → Real)),
    integral_fvMeasure_eq_sum (minusField d) m
      (bondFinsetInternal d m) beta h
      (f : ConfigSpace (Site d) → Real)]
  simp only [specApply_eq_sum]
  apply consistency_double_sum_outer hnm' (minusField d)
    (bondFinsetInternal d m)
  · exact bondFinsetTouch_subset_bondFinsetInternal hnm
  · intro e he
    rw [bondFinsetInternal, Finset.mem_image] at he
    obtain ⟨p, hp, rfl⟩ := he
    rw [bondPairsInternal, Finset.mem_filter] at hp
    exact hp.2

end StatMech.Ising
