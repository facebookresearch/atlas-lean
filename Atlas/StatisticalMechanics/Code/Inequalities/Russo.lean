/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































import Code.Inequalities.Pivotal
import Code.Foundations.ProductMeasure

namespace StatMech

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]





noncomputable def edgeWeight (p : ℝ) (ω : ConfigSpace E) (e : E) : ℝ :=
  if ω e then p else 1 - p




noncomputable def weightOff (p : ℝ) (e : E) (ω : ConfigSpace E) : ℝ :=
  ∏ j ∈ univ.erase e, edgeWeight p ω j



noncomputable def configWeight (p : ℝ) (ω : ConfigSpace E) : ℝ :=
  ∏ e, edgeWeight p ω e



noncomputable def prob (p : ℝ) (A : Set (ConfigSpace E)) : ℝ :=
  ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * configWeight p ω



noncomputable def pivotalProb (p : ℝ) (A : Set (ConfigSpace E)) (e : E) : ℝ :=
  ∑ ω, (Set.indicator {ω | IsPivotal e A ω} (fun _ => (1 : ℝ)) ω) * configWeight p ω





lemma configWeight_eq (p : ℝ) (e : E) (ω : ConfigSpace E) :
    configWeight p ω = edgeWeight p ω e * weightOff p e ω := by
  unfold configWeight weightOff
  rw [← Finset.mul_prod_erase univ _ (mem_univ e)]



lemma weightOff_congr (p : ℝ) (e : E) {ω ω' : ConfigSpace E}
    (h : ∀ e', e' ≠ e → ω e' = ω' e') : weightOff p e ω = weightOff p e ω' := by
  unfold weightOff
  apply Finset.prod_congr rfl
  intro j hj
  have hje : j ≠ e := (Finset.mem_erase.mp hj).1
  unfold edgeWeight; rw [h j hje]

omit [Fintype E] [DecidableEq E] in


lemma hasDerivAt_edgeWeight (ω : ConfigSpace E) (e : E) (p : ℝ) :
    HasDerivAt (fun p => edgeWeight p ω e) (if ω e then 1 else -1) p := by
  unfold edgeWeight
  by_cases h : ω e
  · simp only [h, if_true]; exact hasDerivAt_id p
  · simp only [h]
    have : HasDerivAt (fun p : ℝ => 1 - p) (-1) p := by
      simpa using (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)
    simpa using this




lemma hasDerivAt_configWeight (ω : ConfigSpace E) (p : ℝ) :
    HasDerivAt (fun p => configWeight p ω)
      (∑ e, weightOff p e ω * (if ω e then (1 : ℝ) else -1)) p := by
  unfold configWeight weightOff
  have h := HasDerivAt.finsetProd (u := (univ : Finset E)) (f := fun e p => edgeWeight p ω e)
    (f' := fun e => if ω e then (1 : ℝ) else -1) (fun e _ => hasDerivAt_edgeWeight ω e p)
  simp only [smul_eq_mul] at h
  convert h using 1
  funext q
  simp [Finset.prod_apply]




lemma hasDerivAt_prob (A : Set (ConfigSpace E)) (p : ℝ) :
    HasDerivAt (fun p => prob p A)
      (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω *
        ∑ e, weightOff p e ω * (if ω e then (1 : ℝ) else -1)) p := by
  unfold prob
  apply HasDerivAt.fun_sum
  intro ω _
  exact (hasDerivAt_configWeight ω p).const_mul (A.indicator (fun _ => (1 : ℝ)) ω)



omit [Fintype E] in


lemma setOpen_symm (e : E) (b : Bool) (η : {j : E // j ≠ e} → Bool) :
    setOpen e ((Equiv.funSplitAt e Bool).symm (b, η))
      = (Equiv.funSplitAt e Bool).symm (true, η) := by
  funext j
  by_cases hj : j = e
  · subst hj; simp [setOpen, Equiv.funSplitAt, Equiv.piSplitAt]
  · rw [setOpen_of_ne hj]; simp [Equiv.funSplitAt, Equiv.piSplitAt, hj]

omit [Fintype E] in


lemma setClosed_symm (e : E) (b : Bool) (η : {j : E // j ≠ e} → Bool) :
    setClosed e ((Equiv.funSplitAt e Bool).symm (b, η))
      = (Equiv.funSplitAt e Bool).symm (false, η) := by
  funext j
  by_cases hj : j = e
  · subst hj; simp [setClosed, Equiv.funSplitAt, Equiv.piSplitAt]
  · rw [setClosed_of_ne hj]; simp [Equiv.funSplitAt, Equiv.piSplitAt, hj]





lemma russo_per_eta (p : ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (e : E)
    (ωt ωf : ConfigSpace E)
    (hwo : weightOff p e ωt = weightOff p e ωf)
    (hto : setOpen e ωt = ωt) (htc : setClosed e ωt = ωf)
    (ht : ωt e = true) (hf : ωf e = false) :
    A.indicator (fun _ => (1 : ℝ)) ωt * (weightOff p e ωt * if ωt e then 1 else -1) +
        A.indicator (fun _ => (1 : ℝ)) ωf * (weightOff p e ωf * if ωf e then 1 else -1) =
      {ω | IsPivotal e A ω}.indicator (fun _ => (1 : ℝ)) ωt * configWeight p ωt +
        {ω | IsPivotal e A ω}.indicator (fun _ => (1 : ℝ)) ωf * configWeight p ωf := by
  classical
  have hife : (if ωt e then (1 : ℝ) else -1) = 1 := by rw [ht]; rfl
  have hiff : (if ωf e then (1 : ℝ) else -1) = -1 := by rw [hf]; rfl
  rw [hife, hiff, configWeight_eq p e ωt, configWeight_eq p e ωf]
  have hewt : edgeWeight p ωt e = p := by unfold edgeWeight; rw [ht]; rfl
  have hewf : edgeWeight p ωf e = 1 - p := by unfold edgeWeight; rw [hf]; rfl
  rw [hewt, hewf, ← hwo]
  set w := weightOff p e ωt with hw
  have hpiv_eq : IsPivotal e A ωt ↔ IsPivotal e A ωf := by
    apply isPivotal_congr; intro e' he'; rw [← htc, setClosed_of_ne he']
  have hpiv_t : IsPivotal e A ωt ↔ (ωf ∉ A ∧ ωt ∈ A) := by
    rw [isPivotal_iff_of_isIncreasing hA, hto, htc]
  have pivInd : ∀ ω, {ω | IsPivotal e A ω}.indicator (fun _ => (1 : ℝ)) ω
      = if IsPivotal e A ω then 1 else 0 := fun ω => by
    rw [Set.indicator_apply]; congr 1
  rw [pivInd ωt, pivInd ωf]
  by_cases hmt : ωt ∈ A <;> by_cases hmf : ωf ∈ A
  · have hnp : ¬ IsPivotal e A ωt := by rw [hpiv_t]; tauto
    rw [Set.indicator_of_mem hmt, Set.indicator_of_mem hmf, if_neg hnp,
        if_neg (hpiv_eq.not.mp hnp)]; ring
  · have hp : IsPivotal e A ωt := by rw [hpiv_t]; exact ⟨hmf, hmt⟩
    rw [Set.indicator_of_mem hmt, Set.indicator_of_notMem hmf, if_pos hp,
        if_pos (hpiv_eq.mp hp)]; ring
  · exfalso
    have hle : ωf ≤ ωt := by
      have := setClosed_le_setOpen e ωt; rwa [htc, hto] at this
    exact hmt (hA hle hmf)
  · have hnp : ¬ IsPivotal e A ωt := by rw [hpiv_t]; tauto
    rw [Set.indicator_of_notMem hmt, Set.indicator_of_notMem hmf, if_neg hnp,
        if_neg (hpiv_eq.not.mp hnp)]; ring



lemma russo_per_edge (p : ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (e : E) :
    ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * (weightOff p e ω * (if ω e then (1 : ℝ) else -1))
      = pivotalProb p A e := by
  unfold pivotalProb
  rw [← Equiv.sum_comp (Equiv.funSplitAt e Bool).symm
        (fun ω => A.indicator (fun _ => (1 : ℝ)) ω *
          (weightOff p e ω * (if ω e then (1 : ℝ) else -1)))]
  rw [← Equiv.sum_comp (Equiv.funSplitAt e Bool).symm
        (fun ω => (Set.indicator {ω | IsPivotal e A ω} (fun _ => (1 : ℝ)) ω) * configWeight p ω)]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro η _
  set ωt := (Equiv.funSplitAt e Bool).symm (true, η) with hωt
  set ωf := (Equiv.funSplitAt e Bool).symm (false, η) with hωf
  have ht : ωt e = true := by rw [hωt]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hf : ωf e = false := by rw [hωf]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hto : setOpen e ωt = ωt := by rw [hωt, setOpen_symm]
  have htc : setClosed e ωt = ωf := by rw [hωt, setClosed_symm]
  have hwo : weightOff p e ωt = weightOff p e ωf := by
    apply weightOff_congr; intro e' he'
    rw [hωt, hωf]; simp [Equiv.funSplitAt, Equiv.piSplitAt, he']
  exact russo_per_eta p A hA e ωt ωf hwo hto htc ht hf







theorem hasDerivAt_prob_eq_sum_pivotalProb
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (p : ℝ) :
    HasDerivAt (fun p => prob p A) (∑ e, pivotalProb p A e) p := by
  have hd := hasDerivAt_prob A p
  convert hd using 1
  rw [show (∑ e, pivotalProb p A e)
        = ∑ e, ∑ ω,
            A.indicator (fun _ => (1 : ℝ)) ω * (weightOff p e ω * (if ω e then (1 : ℝ) else -1))
        from Finset.sum_congr rfl (fun e _ => (russo_per_edge p A hA e).symm)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]




theorem deriv_prob_eq_sum_pivotalProb
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (p : ℝ) :
    deriv (fun p => prob p A) p = ∑ e, pivotalProb p A e :=
  (hasDerivAt_prob_eq_sum_pivotalProb A hA p).deriv

end StatMech
