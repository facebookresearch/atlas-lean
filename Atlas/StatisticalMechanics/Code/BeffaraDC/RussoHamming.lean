/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Code.BeffaraDC.RussoInfluence
import Code.BeffaraDC.Hamming
import Code.Inequalities.FKG

namespace StatMech

namespace BeffaraDC

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]






noncomputable def expect (p : ℝ) (f : ConfigSpace E → ℝ) : ℝ :=
  ∑ ω, f ω * configWeight p ω


lemma expect_indicator (p : ℝ) (A : Set (ConfigSpace E)) :
    expect p (A.indicator (fun _ => (1 : ℝ))) = prob p A := rfl


lemma expect_add (p : ℝ) (f g : ConfigSpace E → ℝ) :
    expect p (fun ω => f ω + g ω) = expect p f + expect p g := by
  unfold expect
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun ω _ => by ring)


lemma expect_const_mul (p : ℝ) (c : ℝ) (f : ConfigSpace E → ℝ) :
    expect p (fun ω => c * f ω) = c * expect p f := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ω _ => by ring)


lemma expect_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f g : ConfigSpace E → ℝ}
    (h : ∀ ω, f ω ≤ g ω) : expect p f ≤ expect p g := by
  unfold expect
  refine Finset.sum_le_sum (fun ω _ => ?_)
  exact mul_le_mul_of_nonneg_right (h ω) (configWeight_nonneg hp0 hp1 ω)


lemma expect_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f : ConfigSpace E → ℝ}
    (h : ∀ ω, 0 ≤ f ω) : 0 ≤ expect p f := by
  have := expect_mono hp0 hp1 (f := fun _ => (0 : ℝ)) (g := f) h
  simpa [expect] using this




lemma configWeight_sum_one (p : ℝ) : ∑ ω : ConfigSpace E, configWeight p ω = 1 := by
  unfold configWeight edgeWeight
  rw [← Fintype.prod_sum (fun (e : E) (b : Bool) => if b then p else 1 - p)]
  refine Finset.prod_eq_one (fun e _ => ?_)
  rw [Fintype.sum_bool]; simp

omit [DecidableEq E] in




lemma configWeight_logModular (p : ℝ) (a b : ConfigSpace E) :
    configWeight p a * configWeight p b = configWeight p (a ⊔ b) * configWeight p (a ⊓ b) := by
  have coord : ∀ (φ : Bool → ℝ) (x y : Bool), φ x * φ y = φ (x ⊔ y) * φ (x ⊓ y) := by
    intro φ x y
    rcases le_total x y with h | h
    · rw [sup_eq_right.mpr h, inf_eq_left.mpr h]; ring
    · rw [sup_eq_left.mpr h, inf_eq_right.mpr h]
  unfold configWeight edgeWeight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  simp only [Pi.sup_apply, Pi.inf_apply]
  exact coord (fun c => if c = true then p else 1 - p) (a e) (b e)

omit [DecidableEq E] in

lemma configWeight_fkg (p : ℝ) : FKGLatticeCondition (configWeight (E := E) p) :=
  FKGLatticeCondition.of_logModular (fun a b => configWeight_logModular p a b)




theorem fkg_cov {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f g : ConfigSpace E → ℝ}
    (hf : Monotone f) (hg : Monotone g) :
    expect p f * expect p g ≤ expect p (fun ω => f ω * g ω) := by
  have hπ0 : (0 : ConfigSpace E → ℝ) ≤ configWeight p :=
    fun ω => configWeight_nonneg hp0 hp1 ω
  have h := fkg_inequality (E := E) hπ0 (configWeight_sum_one p) (configWeight_fkg p) hf hg
  unfold expect
  calc (∑ ω, f ω * configWeight p ω) * (∑ ω, g ω * configWeight p ω)
      = (∑ ω, configWeight p ω * f ω) * (∑ ω, configWeight p ω * g ω) := by
        rw [Finset.sum_congr rfl (fun ω _ => mul_comm (f ω) _),
            Finset.sum_congr rfl (fun ω _ => mul_comm (g ω) _)]
    _ ≤ ∑ ω, configWeight p ω * (f ω * g ω) := h
    _ = ∑ ω, (fun ω => f ω * g ω) ω * configWeight p ω :=
        Finset.sum_congr rfl (fun ω _ => by ring)





def numOpen (ω : ConfigSpace E) : ℕ := (univ.filter (fun e => ω e = true)).card

omit [DecidableEq E] in

lemma numOpen_eq_sum (ω : ConfigSpace E) :
    (numOpen ω : ℝ) = ∑ e, (if ω e then (1 : ℝ) else 0) := by
  unfold numOpen
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases h : ω e <;> simp [h]

omit [Fintype E] [DecidableEq E] in

lemma le_open_coord {ω ω' : ConfigSpace E} (hle : ω ≤ ω') (e : E) (h : ω e = true) :
    ω' e = true := by
  have := hle e; rw [h] at this
  cases h' : ω' e with
  | false => rw [h'] at this; exact absurd this (by simp)
  | true => rfl



lemma numOpen_add_hammingDist {ω ω' : ConfigSpace E} (hle : ω ≤ ω') :
    numOpen ω' = numOpen ω + hammingDist ω ω' := by
  unfold numOpen hammingDist
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext e
    simp only [Finset.mem_union, Finset.mem_filter, mem_univ, true_and]
    constructor
    · intro h
      by_cases hω : ω e = true
      · exact Or.inl hω
      · refine Or.inr ?_
        simp only [Bool.not_eq_true] at hω
        rw [hω, h]; simp
    · rintro (h | h)
      · exact le_open_coord hle e h
      · cases hωe : ω e with
        | false =>
          cases hω'e : ω' e with
          | false => rw [hωe, hω'e] at h; exact absurd rfl h
          | true => rfl
        | true => exact le_open_coord hle e hωe
  · rw [Finset.disjoint_filter]
    intro e _ h1 h2
    exact h2 (by rw [h1]; exact (le_open_coord hle e h1).symm)


lemma numOpen_mono : Monotone (fun ω : ConfigSpace E => (numOpen ω : ℝ)) := by
  intro ω ω' hle
  simp only
  have h := numOpen_add_hammingDist hle
  have : numOpen ω ≤ numOpen ω' := by rw [h]; omega
  exact_mod_cast this




theorem numOpen_add_hamming_mono (A : Set (ConfigSpace E)) :
    Monotone (fun ω => (numOpen ω : ℝ) + (hammingToSet A ω : ℝ)) := by
  intro ω ω' hle
  simp only
  have h1 : numOpen ω' = numOpen ω + hammingDist ω ω' := numOpen_add_hammingDist hle
  rcases A.eq_empty_or_nonempty with rfl | hne
  · rw [h1]
    have : (0 : ℝ) ≤ (hammingDist ω ω' : ℝ) := by positivity
    simp only [hammingToSet, Set.image_empty, Nat.sInf_empty, Nat.cast_zero, add_zero]
    push_cast
    linarith
  · have htri : (hammingToSet A ω : ℝ)
        ≤ (hammingDist ω ω' : ℝ) + (hammingToSet A ω' : ℝ) := by
      exact_mod_cast hammingToSet_le_add A hne ω ω'
    rw [h1]; push_cast; linarith





lemma sum_prob_openEdge (p : ℝ) :
    ∑ e : E, prob p (openEdge e) = expect p (fun ω : ConfigSpace E => (numOpen ω : ℝ)) := by
  have step : ∀ e : E, prob p (openEdge e)
      = ∑ ω, (if ω e then (1 : ℝ) else 0) * configWeight p ω := by
    intro e; unfold prob
    exact Finset.sum_congr rfl (fun ω _ => by rw [openEdge_indicator])
  rw [Finset.sum_congr rfl (fun e (_ : e ∈ univ) => step e)]
  unfold expect
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  simp only []
  rw [numOpen_eq_sum, Finset.sum_mul]



lemma sum_prob_inter_openEdge (p : ℝ) (A : Set (ConfigSpace E)) :
    ∑ e : E, prob p (A ∩ openEdge e)
      = expect p (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (numOpen ω : ℝ)) := by
  have step : ∀ e : E, prob p (A ∩ openEdge e)
      = ∑ ω, (A.indicator (fun _ => (1 : ℝ)) ω * (if ω e then (1 : ℝ) else 0))
          * configWeight p ω := by
    intro e; unfold prob
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    classical
    by_cases h : ω e
    · rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hA : ω ∈ A
      · simp [hA, (show ω ∈ A ∩ openEdge e from ⟨hA, h⟩), h]
      · have : ω ∉ A ∩ openEdge e := fun hc => hA hc.1
        simp [hA, this, h]
    · have hnotmem : ω ∉ A ∩ openEdge e := fun hc => h hc.2
      rw [Set.indicator_of_notMem hnotmem]; simp [h]
  rw [Finset.sum_congr rfl (fun e (_ : e ∈ univ) => step e)]
  unfold expect
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  simp only []
  rw [numOpen_eq_sum, Finset.mul_sum, Finset.sum_mul]




theorem cov_with_numOpen (p : ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    p * (1 - p) * ∑ e, pivotalProb p A e
      = expect p (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (numOpen ω : ℝ))
        - prob p A * expect p (fun ω : ConfigSpace E => (numOpen ω : ℝ)) := by
  rw [← sum_cov_eq p A hA]
  have hsplit : ∑ e, (prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A)
      = (∑ e : E, prob p (A ∩ openEdge e))
        - (∑ e : E, prob p (openEdge e)) * prob p A := by
    rw [Finset.sum_sub_distrib, Finset.sum_mul]
  rw [hsplit, sum_prob_inter_openEdge, sum_prob_openEdge]
  ring





lemma expect_indicator_hamming_zero (p : ℝ) (A : Set (ConfigSpace E)) :
    expect p (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (hammingToSet A ω : ℝ)) = 0 := by
  unfold expect
  refine Finset.sum_eq_zero (fun ω _ => ?_)
  simp only []
  classical
  by_cases h : ω ∈ A
  · rw [Set.indicator_of_mem h, hammingToSet_eq_zero_of_mem A h]; simp
  · rw [Set.indicator_of_notMem h]; simp





theorem prob_mul_expect_hamming_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    prob p A * expect p (fun ω => (hammingToSet A ω : ℝ))
      ≤ expect p (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (numOpen ω : ℝ))
        - prob p A * expect p (fun ω : ConfigSpace E => (numOpen ω : ℝ)) := by
  
  
  have hfkg := fkg_cov hp0 hp1 hA.indicator_monotone (numOpen_add_hamming_mono A)
  rw [expect_indicator p A] at hfkg
  
  have hNH : expect p (fun ω => (numOpen ω : ℝ) + (hammingToSet A ω : ℝ))
      = expect p (fun ω : ConfigSpace E => (numOpen ω : ℝ))
        + expect p (fun ω => (hammingToSet A ω : ℝ)) :=
    expect_add p (fun ω => (numOpen ω : ℝ)) (fun ω => (hammingToSet A ω : ℝ))
  
  have hprod : expect p (fun ω => A.indicator (fun _ => (1 : ℝ)) ω
        * ((numOpen ω : ℝ) + (hammingToSet A ω : ℝ)))
      = expect p (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (numOpen ω : ℝ))
        + expect p (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (hammingToSet A ω : ℝ)) := by
    rw [← expect_add p (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (numOpen ω : ℝ))
          (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (hammingToSet A ω : ℝ))]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  
  have hzero := expect_indicator_hamming_zero p A
  
  rw [hNH, hprod, hzero, add_zero] at hfkg
  nlinarith [hfkg]









theorem russoHamming {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    4 * prob p A * expect p (fun ω => (hammingToSet A ω : ℝ))
      ≤ deriv (fun p => prob p A) p := by
  have hp0' : (0 : ℝ) ≤ p := hp0.le
  have hp1' : p ≤ 1 := hp1.le
  
  rw [deriv_prob_eq_sum_pivotalProb A hA p]
  
  have hcov : prob p A * expect p (fun ω => (hammingToSet A ω : ℝ))
      ≤ p * (1 - p) * ∑ e, pivotalProb p A e := by
    rw [cov_with_numOpen p A hA]
    exact prob_mul_expect_hamming_le hp0' hp1' A hA
  
  have hpiv : 0 ≤ ∑ e, pivotalProb p A e :=
    Finset.sum_nonneg (fun e _ => pivotalProb_nonneg hp0' hp1' A e)
  
  have hquarter : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
  
  calc 4 * prob p A * expect p (fun ω => (hammingToSet A ω : ℝ))
      = 4 * (prob p A * expect p (fun ω => (hammingToSet A ω : ℝ))) := by ring
    _ ≤ 4 * (p * (1 - p) * ∑ e, pivotalProb p A e) := by
        have h4 : (0 : ℝ) ≤ 4 := by norm_num
        nlinarith [hcov]
    _ ≤ ∑ e, pivotalProb p A e := by nlinarith [hquarter, hpiv]









lemma expect_neg (p : ℝ) (f : ConfigSpace E → ℝ) :
    expect p (fun ω => - f ω) = - expect p f := by
  unfold expect
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun ω _ => by ring)




theorem fkg_anticorr {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f g : ConfigSpace E → ℝ}
    (hf : Antitone f) (hg : Monotone g) :
    expect p (fun ω => f ω * g ω) ≤ expect p f * expect p g := by
  have hnf : Monotone (fun ω => - f ω) := fun a b h => neg_le_neg (hf h)
  have h := fkg_cov hp0 hp1 hnf hg
  rw [expect_neg] at h
  have heq : expect p (fun ω => (fun ω => - f ω) ω * g ω)
      = - expect p (fun ω => f ω * g ω) := by
    rw [← expect_neg]
    exact Finset.sum_congr rfl (fun ω _ => by ring)
  rw [heq] at h
  linarith



lemma hasDerivAt_expect_raw (f : ConfigSpace E → ℝ) (p : ℝ) :
    HasDerivAt (fun p => expect p f)
      (∑ ω, f ω * ∑ e, weightOff p e ω * (if ω e then (1 : ℝ) else -1)) p := by
  unfold expect
  refine HasDerivAt.fun_sum (fun ω _ => ?_)
  exact (hasDerivAt_configWeight ω p).const_mul (f ω)


lemma differentiable_expect (f : ConfigSpace E → ℝ) :
    Differentiable ℝ (fun p => expect p f) :=
  fun p => (hasDerivAt_expect_raw f p).differentiableAt



lemma deriv_term_eq {p : ℝ} (hp0 : p ≠ 0) (hp1 : (1 : ℝ) - p ≠ 0)
    (ω : ConfigSpace E) (e : E) :
    weightOff p e ω * (if ω e then (1 : ℝ) else -1)
      = configWeight p ω * ((if ω e then (1 : ℝ) else 0) - p) / (p * (1 - p)) := by
  have hcw : configWeight p ω = edgeWeight p ω e * weightOff p e ω := configWeight_eq p e ω
  unfold edgeWeight at hcw
  cases h : ω e
  · rw [hcw, h]; simp only [Bool.false_eq_true, if_false]
    rw [eq_div_iff (mul_ne_zero hp0 hp1)]; ring
  · rw [hcw, h]; simp only [if_true]
    rw [eq_div_iff (mul_ne_zero hp0 hp1)]; ring



lemma deriv_omega_eq {p : ℝ} (hp0 : p ≠ 0) (hp1 : (1 : ℝ) - p ≠ 0) (ω : ConfigSpace E) :
    ∑ e, weightOff p e ω * (if ω e then (1 : ℝ) else -1)
      = configWeight p ω * ((numOpen ω : ℝ) - p * (Fintype.card E)) / (p * (1 - p)) := by
  rw [Finset.sum_congr rfl (fun e _ => deriv_term_eq hp0 hp1 ω e)]
  rw [← Finset.sum_div]; congr 1
  rw [← Finset.mul_sum]; congr 1
  rw [Finset.sum_sub_distrib, ← numOpen_eq_sum]; congr 1
  rw [Finset.sum_const, Finset.card_univ]; ring



lemma hasDerivAt_expect {p : ℝ} (f : ConfigSpace E → ℝ) (hp0 : p ≠ 0)
    (hp1 : (1 : ℝ) - p ≠ 0) :
    HasDerivAt (fun p => expect p f)
      ((expect p (fun ω => f ω * (numOpen ω : ℝ))
        - p * (Fintype.card E) * expect p f) / (p * (1 - p))) p := by
  have hd := hasDerivAt_expect_raw f p
  convert hd using 1
  rw [Finset.sum_congr rfl (fun ω _ => by rw [deriv_omega_eq hp0 hp1 ω])]
  unfold expect
  rw [sub_div, Finset.sum_div, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun ω _ => by ring)


lemma deriv_expect_eq {p : ℝ} (f : ConfigSpace E → ℝ) (hp0 : p ≠ 0)
    (hp1 : (1 : ℝ) - p ≠ 0) :
    deriv (fun p => expect p f) p
      = (expect p (fun ω => f ω * (numOpen ω : ℝ))
        - p * (Fintype.card E) * expect p f) / (p * (1 - p)) :=
  (hasDerivAt_expect f hp0 hp1).deriv


lemma expect_numOpen (p : ℝ) :
    expect p (fun ω : ConfigSpace E => (numOpen ω : ℝ)) = p * (Fintype.card E) := by
  rw [← sum_prob_openEdge]
  rw [Finset.sum_congr rfl (fun e (_ : e ∈ univ) => prob_openEdge p e)]
  rw [Finset.sum_const, Finset.card_univ]; ring





theorem expect_antitoneOn {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp2 : p₂ < 1)
    {f : ConfigSpace E → ℝ} (hf : Antitone f) :
    AntitoneOn (fun p => expect p f) (Set.Icc p₁ p₂) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc p₁ p₂)
    (differentiable_expect f).continuous.continuousOn
    (differentiable_expect f).differentiableOn
  intro p hp
  rw [interior_Icc, Set.mem_Ioo] at hp
  have hpp0 : 0 < p := lt_trans hp1 hp.1
  have hpp1 : p < 1 := lt_trans hp.2 hp2
  rw [deriv_expect_eq f (ne_of_gt hpp0) (by linarith)]
  apply div_nonpos_of_nonpos_of_nonneg
  · have hac := fkg_anticorr hpp0.le hpp1.le hf numOpen_mono
    rw [expect_numOpen (E := E) p] at hac
    have : expect p (fun ω => f ω * (numOpen ω : ℝ))
        ≤ p * (Fintype.card E) * expect p f := by
      calc expect p (fun ω => f ω * (numOpen ω : ℝ))
          ≤ expect p f * (p * (Fintype.card E)) := hac
        _ = p * (Fintype.card E) * expect p f := by ring
    linarith
  · nlinarith [hpp0, hpp1]



omit [DecidableEq E] in


lemma hammingToSet_real_antitone (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    Antitone (fun ω => (hammingToSet A ω : ℝ)) := by
  intro ω ω' hle
  simp only
  exact_mod_cast hammingToSet_antitone A hA hle


lemma differentiable_prob (A : Set (ConfigSpace E)) :
    Differentiable ℝ (fun p => prob p A) :=
  fun p => (hasDerivAt_prob A p).differentiableAt


lemma prob_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Set (ConfigSpace E)) :
    0 ≤ prob p A := by
  unfold prob
  refine Finset.sum_nonneg (fun ω _ => ?_)
  exact mul_nonneg (indicator_nonneg' A ω) (configWeight_nonneg hp0 hp1 ω)


lemma expect_hamming_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Set (ConfigSpace E)) :
    0 ≤ expect p (fun ω => (hammingToSet A ω : ℝ)) :=
  expect_nonneg hp0 hp1 (fun ω => by positivity)




theorem gronwall_prob (A : Set (ConfigSpace E)) (c : ℝ) {p₁ p₂ : ℝ} (hp : p₁ ≤ p₂)
    (hdiff : ∀ p ∈ Set.Icc p₁ p₂, c * prob p A ≤ deriv (fun p => prob p A) p) :
    prob p₁ A ≤ prob p₂ A * Real.exp (- c * (p₂ - p₁)) := by
  set h := fun p => prob p A * Real.exp (- c * p) with hh
  have hmono : MonotoneOn h (Set.Icc p₁ p₂) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc p₁ p₂)
    · exact (differentiable_prob A).continuous.continuousOn.mul
        (Real.continuous_exp.comp (by continuity)).continuousOn
    · exact (differentiable_prob A).differentiableOn.mul
        (Real.differentiable_exp.comp (by fun_prop)).differentiableOn
    · intro p hp'
      rw [interior_Icc, Set.mem_Ioo] at hp'
      have hd : HasDerivAt h
          (deriv (fun p => prob p A) p * Real.exp (- c * p)
            + prob p A * (Real.exp (- c * p) * (- c))) p := by
        have h1 : HasDerivAt (fun p => prob p A) (deriv (fun p => prob p A) p) p :=
          (differentiable_prob A p).hasDerivAt
        have h2 : HasDerivAt (fun p => Real.exp (- c * p)) (Real.exp (- c * p) * (- c)) p := by
          have hlin : HasDerivAt (fun p : ℝ => - c * p) (- c) p := by
            simpa using (hasDerivAt_id p).const_mul (-c)
          exact (Real.hasDerivAt_exp _).comp p hlin
        exact h1.mul h2
      rw [hd.deriv]
      have hineq := hdiff p ⟨le_of_lt hp'.1, le_of_lt hp'.2⟩
      have hexp : 0 < Real.exp (- c * p) := Real.exp_pos _
      nlinarith [hineq, hexp]
  have hle := hmono (Set.left_mem_Icc.mpr hp) (Set.right_mem_Icc.mpr hp) hp
  simp only [hh] at hle
  have hexp1 : 0 < Real.exp (- c * p₁) := Real.exp_pos _
  rw [show (- c * (p₂ - p₁)) = (- c * p₂) - (- c * p₁) by ring, Real.exp_sub, mul_div_assoc']
  rw [le_div_iff₀ hexp1]
  exact hle










theorem russoHammingIntegrated {p₁ p₂ : ℝ} (hp1 : 0 < p₁) (hp12 : p₁ < p₂) (hp2 : p₂ < 1)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    prob p₁ A
      ≤ prob p₂ A
          * Real.exp (- 4 * (p₂ - p₁) * expect p₂ (fun ω => (hammingToSet A ω : ℝ))) := by
  set H₂ := expect p₂ (fun ω => (hammingToSet A ω : ℝ)) with hH₂
  
  have hgr := gronwall_prob A (4 * H₂) (le_of_lt hp12) ?_
  · rw [show (- 4 * (p₂ - p₁) * H₂) = (- (4 * H₂) * (p₂ - p₁)) by ring]
    exact hgr
  · 
    intro p hp
    obtain ⟨hpl, hpr⟩ := hp
    have hpp0 : 0 < p := lt_of_lt_of_le hp1 hpl
    have hpp1 : p < 1 := lt_of_le_of_lt hpr hp2
    
    have hrh := russoHamming hpp0 hpp1 A hA
    
    have hanti := expect_antitoneOn hp1 hp2 (hammingToSet_real_antitone A hA)
    have hH2le : H₂ ≤ expect p (fun ω => (hammingToSet A ω : ℝ)) :=
      hanti ⟨hpl, hpr⟩ ⟨le_of_lt hp12, le_refl _⟩ hpr
    have hprob_nn := prob_nonneg hpp0.le hpp1.le A
    calc 4 * H₂ * prob p A
        = 4 * prob p A * H₂ := by ring
      _ ≤ 4 * prob p A * expect p (fun ω => (hammingToSet A ω : ℝ)) := by
          have h4p : (0 : ℝ) ≤ 4 * prob p A := by positivity
          nlinarith [hH2le, h4p]
      _ ≤ deriv (fun p => prob p A) p := hrh

end BeffaraDC

end StatMech
