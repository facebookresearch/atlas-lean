/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































import Code.FK.RandomCluster

open scoped BigOperators

namespace StatMech

namespace FK

open Finset ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]










noncomputable def edgeProductW (pf : Sym2 V → ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∏ e ∈ G.edgeFinset, (if ω e then pf e else 1 - pf e)



noncomputable def fkWeightW (pf : Sym2 V → ℝ) (q : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  edgeProductW G pf ω * q ^ numClusters G ω


noncomputable def fkZW (pf : Sym2 V → ℝ) (q : ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), fkWeightW G pf q ω


noncomputable def fkProbW (pf : Sym2 V → ℝ) (q : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  fkWeightW G pf q ω / fkZW G pf q


noncomputable def fkMeanW (pf : Sym2 V → ℝ) (q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), g ω * fkProbW G pf q ω


noncomputable def fkCovW (pf : Sym2 V → ℝ) (q : ℝ)
    (f g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  fkMeanW G pf q (fun ω => f ω * g ω) - fkMeanW G pf q f * fkMeanW G pf q g



noncomputable def coordR (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  if ω e then (1 : ℝ) else 0







omit [DecidableEq V] in


lemma edgeProductW_pos {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    (ω : ConfigSpace (Sym2 V)) : 0 < edgeProductW G pf ω := by
  unfold edgeProductW
  apply Finset.prod_pos
  intro e _
  split
  · exact hpf e
  · have := hpf1 e; linarith


lemma fkWeightW_pos {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) (ω : ConfigSpace (Sym2 V)) : 0 < fkWeightW G pf q ω :=
  mul_pos (edgeProductW_pos G hpf hpf1 ω) (pow_pos hq _)


lemma fkZW_pos {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) : 0 < fkZW G pf q :=
  Finset.sum_pos (fun ω _ => fkWeightW_pos G hpf hpf1 hq ω) Finset.univ_nonempty

lemma fkZW_ne_zero {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) : fkZW G pf q ≠ 0 :=
  (fkZW_pos G hpf hpf1 hq).ne'








noncomputable def edgeProductWOff (pf : Sym2 V → ℝ) (e₀ : Sym2 V)
    (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∏ j ∈ G.edgeFinset.erase e₀, (if ω j then pf j else 1 - pf j)


lemma edgeProductWOff_update (pf : Sym2 V → ℝ) (e₀ : Sym2 V) (t : ℝ)
    (ω : ConfigSpace (Sym2 V)) :
    edgeProductWOff G (Function.update pf e₀ t) e₀ ω = edgeProductWOff G pf e₀ ω := by
  unfold edgeProductWOff
  refine Finset.prod_congr rfl (fun j hj => ?_)
  have hne : j ≠ e₀ := (Finset.mem_erase.1 hj).1
  rw [Function.update_of_ne hne]



lemma edgeProductW_update_factor (pf : Sym2 V → ℝ) (e₀ : Sym2 V) (t : ℝ)
    (ω : ConfigSpace (Sym2 V)) (he : e₀ ∈ G.edgeFinset) :
    edgeProductW G (Function.update pf e₀ t) ω
      = edgeProductWOff G pf e₀ ω * (if ω e₀ then t else 1 - t) := by
  unfold edgeProductW
  rw [← Finset.prod_erase_mul G.edgeFinset _ he]
  congr 1
  · rw [← edgeProductWOff_update G pf e₀ t ω]; rfl
  · rw [Function.update_self]









lemma hasDerivAt_edgeProductW_update (pf : Sym2 V → ℝ) (e₀ : Sym2 V) (t : ℝ)
    (ω : ConfigSpace (Sym2 V)) (he : e₀ ∈ G.edgeFinset) :
    HasDerivAt (fun t => edgeProductW G (Function.update pf e₀ t) ω)
      (edgeProductWOff G pf e₀ ω * (if ω e₀ then (1 : ℝ) else -1)) t := by
  have hfac : (fun t => edgeProductW G (Function.update pf e₀ t) ω)
      = (fun t => edgeProductWOff G pf e₀ ω * (if ω e₀ then t else 1 - t)) := by
    funext s; exact edgeProductW_update_factor G pf e₀ s ω he
  rw [hfac]
  have hfactor : HasDerivAt (fun t => if ω e₀ then t else 1 - t)
      (if ω e₀ then (1 : ℝ) else -1) t := by
    by_cases h : ω e₀
    · simp only [h, if_true]; exact hasDerivAt_id t
    · simp only [h]; simpa using (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
  exact hfactor.const_mul (edgeProductWOff G pf e₀ ω)




lemma hasDerivAt_edgeProductW_clean {pf : Sym2 V → ℝ} {e₀ : Sym2 V} {t : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (ω : ConfigSpace (Sym2 V)) (he : e₀ ∈ G.edgeFinset) :
    HasDerivAt (fun t => edgeProductW G (Function.update pf e₀ t) ω)
      (edgeProductW G (Function.update pf e₀ t) ω
        * ((coordR e₀ ω - t) / (t * (1 - t)))) t := by
  refine (hasDerivAt_edgeProductW_update G pf e₀ t ω he).congr_deriv ?_
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  have htne : t ≠ 0 := ht.ne'
  have ht1ne : (1 : ℝ) - t ≠ 0 := ht1'.ne'
  rw [edgeProductW_update_factor G pf e₀ t ω he]
  unfold coordR
  by_cases h : ω e₀ = true
  · rw [if_pos h, if_pos h, if_pos h]; field_simp
  · rw [if_neg h, if_neg h, if_neg h]; field_simp; ring






lemma hasDerivAt_fkWeightW {pf : Sym2 V → ℝ} {e₀ : Sym2 V} {t : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (q : ℝ) (ω : ConfigSpace (Sym2 V))
    (he : e₀ ∈ G.edgeFinset) :
    HasDerivAt (fun t => fkWeightW G (Function.update pf e₀ t) q ω)
      (fkWeightW G (Function.update pf e₀ t) q ω
        * ((coordR e₀ ω - t) / (t * (1 - t)))) t := by
  have h := (hasDerivAt_edgeProductW_clean (pf := pf) G ht ht1 ω he).mul_const
    (q ^ numClusters G ω)
  refine h.congr_deriv ?_
  unfold fkWeightW
  ring










noncomputable def fkNumerW (pf : Sym2 V → ℝ) (q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), g ω * fkWeightW G pf q ω


lemma fkNumerW_one (pf : Sym2 V → ℝ) (q : ℝ) :
    fkNumerW G pf q (fun _ => 1) = fkZW G pf q := by
  unfold fkNumerW fkZW
  exact Finset.sum_congr rfl (fun ω _ => by rw [one_mul])





lemma hasDerivAt_fkNumerW {pf : Sym2 V → ℝ} {e₀ : Sym2 V} {t : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ)
    (he : e₀ ∈ G.edgeFinset) :
    HasDerivAt (fun t => fkNumerW G (Function.update pf e₀ t) q g)
      ((∑ ω : ConfigSpace (Sym2 V),
        g ω * (fkWeightW G (Function.update pf e₀ t) q ω * (coordR e₀ ω - t)))
          / (t * (1 - t))) t := by
  unfold fkNumerW
  have hsum : HasDerivAt
      (fun t => ∑ ω : ConfigSpace (Sym2 V),
        g ω * fkWeightW G (Function.update pf e₀ t) q ω)
      (∑ ω : ConfigSpace (Sym2 V),
        g ω * (fkWeightW G (Function.update pf e₀ t) q ω
          * ((coordR e₀ ω - t) / (t * (1 - t))))) t := by
    apply HasDerivAt.fun_sum
    intro ω _
    exact (hasDerivAt_fkWeightW (pf := pf) G ht ht1 q ω he).const_mul (g ω)
  refine hsum.congr_deriv ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [mul_div_assoc, mul_div_assoc]









lemma fkMeanW_eq_div (pf : Sym2 V → ℝ) (q : ℝ) (g : ConfigSpace (Sym2 V) → ℝ) :
    fkMeanW G pf q g = fkNumerW G pf q g / fkZW G pf q := by
  unfold fkMeanW fkNumerW fkProbW
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [mul_div_assoc]


lemma fkMeanW_add (pf : Sym2 V → ℝ) (q : ℝ) (g h : ConfigSpace (Sym2 V) → ℝ) :
    fkMeanW G pf q (fun ω => g ω + h ω) = fkMeanW G pf q g + fkMeanW G pf q h := by
  unfold fkMeanW
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun ω _ => by ring)


lemma fkMeanW_const (pf : Sym2 V → ℝ) (q : ℝ) {c : ℝ}
    (hZ : fkZW G pf q ≠ 0) : fkMeanW G pf q (fun _ => c) = c := by
  unfold fkMeanW fkProbW
  have hstep : ∀ ω : ConfigSpace (Sym2 V), c * (fkWeightW G pf q ω / fkZW G pf q)
      = (c * fkWeightW G pf q ω) / fkZW G pf q := fun ω => by rw [mul_div_assoc]
  rw [Finset.sum_congr rfl (fun ω _ => hstep ω), ← Finset.sum_div, ← Finset.mul_sum]
  show (c * fkZW G pf q) / fkZW G pf q = c
  rw [mul_div_assoc, div_self hZ, mul_one]


lemma fkMeanW_const_mul (pf : Sym2 V → ℝ) (q : ℝ) (c : ℝ)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    fkMeanW G pf q (fun ω => c * g ω) = c * fkMeanW G pf q g := by
  unfold fkMeanW
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  ring



lemma fkCovW_sub_const (pf : Sym2 V → ℝ) (q : ℝ)
    (f g : ConfigSpace (Sym2 V) → ℝ) {c : ℝ} (hZ : fkZW G pf q ≠ 0) :
    fkCovW G pf q f (fun ω => g ω - c) = fkCovW G pf q f g := by
  unfold fkCovW
  have hprod : fkMeanW G pf q (fun ω => f ω * (g ω - c))
      = fkMeanW G pf q (fun ω => f ω * g ω) - c * fkMeanW G pf q f := by
    have heq : (fun ω => f ω * (g ω - c)) = (fun ω => f ω * g ω + (-c) * f ω) := by
      funext ω; ring
    rw [heq, fkMeanW_add, fkMeanW_const_mul]
    ring
  have hgc : fkMeanW G pf q (fun ω => g ω - c) = fkMeanW G pf q g - c := by
    have heq : (fun ω => g ω - c) = (fun ω => g ω + (fun _ => -c) ω) := by funext ω; ring
    rw [heq, fkMeanW_add, fkMeanW_const G pf q hZ]; ring
  rw [hprod, hgc]; ring


















theorem hasDerivAt_fkMeanW {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) {e₀ : Sym2 V} (he : e₀ ∈ G.edgeFinset)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    HasDerivAt (fun t => fkMeanW G (Function.update pf e₀ t) q g)
      (fkCovW G (Function.update pf e₀ (pf e₀)) q g (coordR e₀) / (pf e₀ * (1 - pf e₀)))
      (pf e₀) := by
  set t₀ := pf e₀ with ht₀
  have ht : 0 < t₀ := hpf e₀
  have ht1 : t₀ < 1 := hpf1 e₀
  have hppos : 0 < t₀ * (1 - t₀) := mul_pos ht (by linarith)
  have hpne : t₀ * (1 - t₀) ≠ 0 := hppos.ne'
  
  have hupd_pos : ∀ s : ℝ, 0 < s → s < 1 → ∀ e, 0 < Function.update pf e₀ s e := by
    intro s hs _ e
    by_cases h : e = e₀
    · subst h; rw [Function.update_self]; exact hs
    · rw [Function.update_of_ne h]; exact hpf e
  have hupd_lt : ∀ s : ℝ, 0 < s → s < 1 → ∀ e, Function.update pf e₀ s e < 1 := by
    intro s hs hs1 e
    by_cases h : e = e₀
    · subst h; rw [Function.update_self]; exact hs1
    · rw [Function.update_of_ne h]; exact hpf1 e
  
  
  have hN : HasDerivAt (fun t => fkNumerW G (Function.update pf e₀ t) q g)
      (fkNumerW G (Function.update pf e₀ t₀) q (fun ω => g ω * (coordR e₀ ω - t₀))
        / (t₀ * (1 - t₀))) t₀ := by
    have h := hasDerivAt_fkNumerW (pf := pf) G ht ht1 q g he
    refine h.congr_deriv ?_
    congr 1
    unfold fkNumerW
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    ring
  have hZd : HasDerivAt (fun t => fkZW G (Function.update pf e₀ t) q)
      (fkNumerW G (Function.update pf e₀ t₀) q (fun ω => coordR e₀ ω - t₀)
        / (t₀ * (1 - t₀))) t₀ := by
    have h := hasDerivAt_fkNumerW (pf := pf) G ht ht1 q (fun _ => 1) he
    have hfun : (fun t => fkNumerW G (Function.update pf e₀ t) q (fun _ => 1))
        = (fun t => fkZW G (Function.update pf e₀ t) q) := by
      funext s; exact fkNumerW_one G (Function.update pf e₀ s) q
    rw [hfun] at h
    refine h.congr_deriv ?_
    congr 1
    unfold fkNumerW
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    ring
  
  have hZne : fkZW G (Function.update pf e₀ t₀) q ≠ 0 :=
    fkZW_ne_zero G (hupd_pos t₀ ht ht1) (hupd_lt t₀ ht ht1) hq
  
  have hdiv := HasDerivAt.div hN hZd hZne
  have hexp : (fun t => fkMeanW G (Function.update pf e₀ t) q g)
      = (fun t => fkNumerW G (Function.update pf e₀ t) q g)
        / (fun t => fkZW G (Function.update pf e₀ t) q) := by
    funext s; rw [fkMeanW_eq_div]; rfl
  rw [hexp]
  refine hdiv.congr_deriv ?_
  
  set Pf := Function.update pf e₀ t₀ with hPf
  set N := fkNumerW G Pf q g with hNdef
  set Z := fkZW G Pf q with hZdef
  set NgC := fkNumerW G Pf q (fun ω => g ω * (coordR e₀ ω - t₀)) with hNgC
  set NC := fkNumerW G Pf q (fun ω => coordR e₀ ω - t₀) with hNC
  
  have hgC : fkMeanW G Pf q (fun ω => g ω * (coordR e₀ ω - t₀)) = NgC / Z :=
    fkMeanW_eq_div G Pf q _
  have hCexp : fkMeanW G Pf q (fun ω => coordR e₀ ω - t₀) = NC / Z :=
    fkMeanW_eq_div G Pf q _
  have hgexp : fkMeanW G Pf q g = N / Z := fkMeanW_eq_div G Pf q g
  
  have hcov : fkCovW G Pf q g (fun ω => coordR e₀ ω - t₀)
      = (NgC * Z - N * NC) / Z ^ 2 := by
    unfold fkCovW
    rw [hgC, hCexp, hgexp]
    field_simp
  
  have hshift : fkCovW G Pf q g (fun ω => coordR e₀ ω - t₀)
      = fkCovW G Pf q g (coordR e₀) :=
    fkCovW_sub_const G Pf q g (coordR e₀) hZne
  
  show (NgC / (t₀ * (1 - t₀)) * Z - N * (NC / (t₀ * (1 - t₀)))) / Z ^ 2
      = fkCovW G Pf q g (coordR e₀) / (t₀ * (1 - t₀))
  rw [← hshift, hcov]
  field_simp




theorem deriv_fkMeanW {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e) (hpf1 : ∀ e, pf e < 1)
    {q : ℝ} (hq : 0 < q) {e₀ : Sym2 V} (he : e₀ ∈ G.edgeFinset)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    deriv (fun t => fkMeanW G (Function.update pf e₀ t) q g) (pf e₀)
      = fkCovW G (Function.update pf e₀ (pf e₀)) q g (coordR e₀)
        / (pf e₀ * (1 - pf e₀)) :=
  (hasDerivAt_fkMeanW G hpf hpf1 hq he g).deriv










noncomputable def fkProbWOf (pf : Sym2 V → ℝ) (q : ℝ)
    (A : Set (ConfigSpace (Sym2 V))) : ℝ :=
  fkMeanW G pf q (A.indicator (fun _ => (1 : ℝ)))















theorem hasDerivAt_fkProbWOf {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e)
    (hpf1 : ∀ e, pf e < 1) {q : ℝ} (hq : 0 < q) {e₀ : Sym2 V} (he : e₀ ∈ G.edgeFinset)
    (A : Set (ConfigSpace (Sym2 V))) :
    HasDerivAt (fun t => fkProbWOf G (Function.update pf e₀ t) q A)
      (fkCovW G (Function.update pf e₀ (pf e₀)) q (A.indicator (fun _ => (1 : ℝ)))
          (coordR e₀)
        / (pf e₀ * (1 - pf e₀)))
      (pf e₀) :=
  hasDerivAt_fkMeanW G hpf hpf1 hq he _


theorem deriv_fkProbWOf {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e)
    (hpf1 : ∀ e, pf e < 1) {q : ℝ} (hq : 0 < q) {e₀ : Sym2 V} (he : e₀ ∈ G.edgeFinset)
    (A : Set (ConfigSpace (Sym2 V))) :
    deriv (fun t => fkProbWOf G (Function.update pf e₀ t) q A) (pf e₀)
      = fkCovW G (Function.update pf e₀ (pf e₀)) q (A.indicator (fun _ => (1 : ℝ)))
          (coordR e₀)
        / (pf e₀ * (1 - pf e₀)) :=
  (hasDerivAt_fkProbWOf G hpf hpf1 hq he A).deriv























lemma hasDerivAt_paramOfBeta (J β : ℝ) :
    HasDerivAt (fun b => 1 - Real.exp (-(b * J))) (J * Real.exp (-(β * J))) β := by
  have h1 : HasDerivAt (fun b : ℝ => -(b * J)) (-J) β := by
    simpa using ((hasDerivAt_id β).mul_const J).neg
  have h2 : HasDerivAt (fun b => Real.exp (-(b * J))) (Real.exp (-(β * J)) * (-J)) β :=
    (Real.hasDerivAt_exp _).comp β h1
  have h3 := (hasDerivAt_const β (1 : ℝ)).sub h2
  convert h3 using 1
  ring











theorem hasDerivAt_fkProbWOf_beta {pf : Sym2 V → ℝ} (hpf : ∀ e, 0 < pf e)
    (hpf1 : ∀ e, pf e < 1) {q : ℝ} (hq : 0 < q) {e₀ : Sym2 V} (he : e₀ ∈ G.edgeFinset)
    (A : Set (ConfigSpace (Sym2 V))) (J β₀ : ℝ)
    (hpt : pf e₀ = 1 - Real.exp (-(β₀ * J))) :
    HasDerivAt
      (fun b => fkProbWOf G (Function.update pf e₀ (1 - Real.exp (-(b * J)))) q A)
      ((J / (1 - Real.exp (-(β₀ * J))))
        * fkCovW G (Function.update pf e₀ (pf e₀)) q
            (A.indicator (fun _ => (1 : ℝ))) (coordR e₀))
      β₀ := by
  have hinner := hasDerivAt_paramOfBeta J β₀
  have hval : (1 - Real.exp (-(β₀ * J))) = pf e₀ := hpt.symm
  
  have houter : HasDerivAt (fun t => fkProbWOf G (Function.update pf e₀ t) q A)
      (fkCovW G (Function.update pf e₀ (pf e₀)) q (A.indicator (fun _ => (1 : ℝ)))
          (coordR e₀) / (pf e₀ * (1 - pf e₀)))
      (1 - Real.exp (-(β₀ * J))) := by
    rw [hval]; exact hasDerivAt_fkProbWOf G hpf hpf1 hq he A
  have hcomp := houter.comp β₀ hinner
  refine hcomp.congr_deriv ?_
  rw [hpt]
  set u := Real.exp (-(β₀ * J)) with hu
  have hupos : 0 < u := Real.exp_pos _
  have h1u : (0 : ℝ) < 1 - u := by
    have := hpf e₀; rw [hpt] at this; linarith
  have hune : u ≠ 0 := hupos.ne'
  have h1une : (1 : ℝ) - u ≠ 0 := h1u.ne'
  
  rw [show (1 : ℝ) - (1 - u) = u by ring]
  field_simp

end FK

end StatMech
