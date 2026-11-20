/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































import Code.Sharpness.PivotalFactor

namespace StatMech

namespace Percolation

open ConfigSpace Function Finset StatMech StatMech.Sharpness

variable {E : Type*} [Fintype E] [DecidableEq E]






noncomputable def rus_openCount (ω : ConfigSpace E) : ℝ := ∑ e, openInd ω e




noncomputable def rus_expect (p : ℝ) (f : ConfigSpace E → ℝ) : ℝ :=
  ∑ ω, f ω * configWeight p ω








lemma rus_prod_extract (e₀ : E) (h : Bool → ℝ) (g : E → Bool → ℝ) (ω : ConfigSpace E) :
    h (ω e₀) * (∏ e, g e (ω e))
      = ∏ e, (if e = e₀ then h (ω e) * g e (ω e) else g e (ω e)) := by
  symm
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ e₀), if_pos rfl]
  rw [Finset.prod_congr rfl (g := fun e => g e (ω e))
        (fun e he => if_neg (Finset.mem_erase.mp he).1)]
  rw [← Finset.mul_prod_erase univ (fun e => g e (ω e)) (Finset.mem_univ e₀)]
  ring








lemma rus_expect_openInd (p : ℝ) (e₀ : E) :
    ∑ ω : ConfigSpace E, openInd ω e₀ * configWeight p ω = p := by
  set G : E → Bool → ℝ := fun e b =>
      if e = e₀ then (if b then (1 : ℝ) else 0) * (if b then p else 1 - p)
                else (if b then p else 1 - p) with hG
  have step : ∀ ω : ConfigSpace E, openInd ω e₀ * configWeight p ω = ∏ e, G e (ω e) := by
    intro ω
    rw [configWeight]
    have hpe : (∏ e, edgeWeight p ω e) = ∏ e, (if ω e then p else 1 - p) :=
      Finset.prod_congr rfl (fun e _ => rfl)
    rw [hpe, openInd,
      rus_prod_extract e₀ (fun b => if b then (1 : ℝ) else 0) (fun e b => if b then p else 1 - p) ω]
  rw [Finset.sum_congr rfl (fun ω _ => step ω), ← Fintype.prod_sum G,
      ← Finset.mul_prod_erase univ _ (Finset.mem_univ e₀)]
  have hG0 : (∑ b : Bool, G e₀ b) = p := by rw [hG]; simp
  have hGe : ∀ e ∈ univ.erase e₀, (∑ b : Bool, G e b) = 1 := by
    intro e he
    rw [hG]; simp only [if_neg (Finset.mem_erase.mp he).1, Fintype.sum_bool]
    show p + (1 - p) = 1; ring
  rw [hG0, Finset.prod_congr rfl hGe, Finset.prod_const_one, mul_one]






lemma rus_expect_openCount (p : ℝ) :
    rus_expect p (rus_openCount (E := E)) = (Fintype.card E : ℝ) * p := by
  unfold rus_expect rus_openCount
  rw [show (∑ ω : ConfigSpace E, (∑ e, openInd ω e) * configWeight p ω)
        = ∑ e, ∑ ω : ConfigSpace E, openInd ω e * configWeight p ω from ?_]
  · rw [Finset.sum_congr rfl (fun e _ => rus_expect_openInd p e),
        Finset.sum_const, Finset.card_univ]
    ring
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun ω _ => Finset.sum_mul _ _ _)











lemma rus_sum_weightOff_sign (ω : ConfigSpace E) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (∑ e, weightOff p e ω * (if ω e then (1 : ℝ) else -1))
      = (1 / (p * (1 - p))) *
          ((rus_openCount ω - (Fintype.card E : ℝ) * p) * configWeight p ω) := by
  rw [Finset.sum_congr rfl (fun e _ => weightOff_mul_sign_eq_pivotalFactor ω e hp0 hp1),
      ← Finset.sum_mul]
  have hsum : (∑ e, (openInd ω e - p) / (p * (1 - p)))
      = (1 / (p * (1 - p))) * (rus_openCount ω - (Fintype.card E : ℝ) * p) := by
    have hpull : (∑ e, (openInd ω e - p) / (p * (1 - p)))
        = (1 / (p * (1 - p))) * (∑ e, (openInd ω e - p)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun e _ => by ring)
    rw [hpull, rus_openCount, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
    ring
  rw [hsum, mul_assoc]














theorem rus_russo_formula (A : Set (ConfigSpace E)) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun p => prob p A)
      ((1 / (p * (1 - p))) *
        (rus_expect p (fun ω => rus_openCount ω * A.indicator (fun _ => (1 : ℝ)) ω)
          - rus_expect p (rus_openCount (E := E)) * prob p A)) p := by
  have hd := hasDerivAt_prob A p
  convert hd using 1
  
  rw [show (∑ ω : ConfigSpace E, A.indicator (fun _ => (1 : ℝ)) ω *
              ∑ e, weightOff p e ω * (if ω e then (1 : ℝ) else -1))
        = ∑ ω : ConfigSpace E, A.indicator (fun _ => (1 : ℝ)) ω *
              ((1 / (p * (1 - p))) *
                ((rus_openCount ω - (Fintype.card E : ℝ) * p) * configWeight p ω))
        from Finset.sum_congr rfl (fun ω _ => by rw [rus_sum_weightOff_sign ω hp0 hp1])]
  
  rw [rus_expect_openCount]
  
  rw [show (∑ ω : ConfigSpace E, A.indicator (fun _ => (1 : ℝ)) ω *
              ((1 / (p * (1 - p))) *
                ((rus_openCount ω - (Fintype.card E : ℝ) * p) * configWeight p ω)))
        = (1 / (p * (1 - p))) * ∑ ω : ConfigSpace E,
              A.indicator (fun _ => (1 : ℝ)) ω *
                ((rus_openCount ω - (Fintype.card E : ℝ) * p) * configWeight p ω)
        from by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun ω _ => by ring)]
  congr 1
  
  rw [show (rus_expect p (fun ω => rus_openCount ω * A.indicator (fun _ => (1 : ℝ)) ω))
        = ∑ ω : ConfigSpace E,
            A.indicator (fun _ => (1 : ℝ)) ω * (rus_openCount ω * configWeight p ω)
        from by unfold rus_expect; exact Finset.sum_congr rfl (fun ω _ => by ring)]
  rw [prob, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun ω _ => by ring)





theorem rus_russo_formula_deriv (A : Set (ConfigSpace E)) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    deriv (fun p => prob p A) p
      = (1 / (p * (1 - p))) *
        (rus_expect p (fun ω => rus_openCount ω * A.indicator (fun _ => (1 : ℝ)) ω)
          - rus_expect p (rus_openCount (E := E)) * prob p A) :=
  (rus_russo_formula A hp0 hp1).deriv









theorem rus_russo_formula_pivotal (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (p : ℝ) :
    HasDerivAt (fun p => prob p A) (∑ e, pivotalProb p A e) p :=
  hasDerivAt_prob_eq_sum_pivotalProb A hA p







theorem rus_covariance_eq_sum_pivotalProb (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (1 / (p * (1 - p))) *
        (rus_expect p (fun ω => rus_openCount ω * A.indicator (fun _ => (1 : ℝ)) ω)
          - rus_expect p (rus_openCount (E := E)) * prob p A)
      = ∑ e, pivotalProb p A e := by
  have h1 := rus_russo_formula A hp0 hp1
  have h2 := rus_russo_formula_pivotal A hA p
  exact h1.unique h2

end Percolation

end StatMech
