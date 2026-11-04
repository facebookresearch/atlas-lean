/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.PivotalFactor

/-!
# Russo's formula in covariance form

For independent Bernoulli(`p`) coordinates on a finite set `E`, the derivative of
`p ↦ ℙ_p(A)` is, for every event `A` (not necessarily increasing),
`d/dp ℙ_p(A) = (p (1 - p))⁻¹ (𝔼_p[N · 1_A] - 𝔼_p[N] ℙ_p(A)) = Cov_p(N, 1_A) / (p (1 - p))`,
where `N(ω)` is the number of open coordinates. For increasing `A` this covariance equals the
expected number of pivotal coordinates (Russo's formula in pivotal form,
`StatMech.hasDerivAt_prob_eq_sum_pivotalProb`).

## Main definitions

* `StatMech.Percolation.rus_openCount`: the number `N(ω)` of open coordinates of `ω`.
* `StatMech.Percolation.rus_expect`: the expectation `𝔼_p[f] = ∑ ω, f ω · configWeight p ω`.

## Main results

* `StatMech.Percolation.rus_russo_formula`: the covariance form of Russo's formula, for all events.
* `StatMech.Percolation.rus_covariance_eq_sum_pivotalProb`: for increasing `A`, the covariance
  form equals `∑ e, pivotalProb p A e`.

## References

* L. Russo, *A note on percolation*, Z. Wahrsch. Verw. Gebiete 43 (1978).
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Section 2.4.
-/

@[expose] public section

namespace StatMech

namespace Percolation

open ConfigSpace Function Finset StatMech StatMech.Sharpness

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The number `N(ω) = ∑ e, 1[ω e open]` of open coordinates of `ω`. -/
noncomputable def rus_openCount (ω : ConfigSpace E) : ℝ := ∑ e, openInd ω e

/-- The expectation `𝔼_p[f] = ∑ ω, f ω · configWeight p ω` of `f` under independent Bernoulli(`p`)
coordinates (a signed weight when `p ∉ [0, 1]`). -/
noncomputable def rus_expect (p : ℝ) (f : ConfigSpace E → ℝ) : ℝ :=
  ∑ ω, f ω * configWeight p ω

/-- Multiplying a product over `E` by a factor depending on coordinate `e₀` merges the factor into
the `e₀` term. -/
lemma rus_prod_extract (e₀ : E) (h : Bool → ℝ) (g : E → Bool → ℝ) (ω : ConfigSpace E) :
    h (ω e₀) * (∏ e, g e (ω e))
      = ∏ e, (if e = e₀ then h (ω e) * g e (ω e) else g e (ω e)) := by
  symm
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ e₀), ite_eq_left rfl]
  rw [Finset.prod_congr rfl (g := fun e => g e (ω e))
        (fun e he => ite_eq_right (Finset.mem_erase.mp he).1)]
  rw [← Finset.mul_prod_erase univ (fun e => g e (ω e)) (Finset.mem_univ e₀)]
  ring

/-- `𝔼_p[1[ω e₀ open]] = p`. See also `StatMech.BeffaraDC.prob_openEdge`, the same fact stated with
`prob` and the event `openEdge e₀`. -/
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
    rw [hG]; simp only [ite_eq_right (Finset.mem_erase.mp he).1, Fintype.sum_bool]
    change p + (1 - p) = 1; ring
  rw [hG0, Finset.prod_congr rfl hGe, Finset.prod_const_one, mul_one]

/-- `𝔼_p[N] = |E| p`. -/
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

/-- The pivotal-factor identity summed over coordinates:
`∑ e, weightOff p e ω · (±1) = (p (1 - p))⁻¹ (N(ω) - |E| p) configWeight p ω`. -/
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

/-- **Russo's formula**, covariance form: for every event `A` and `0 < p < 1`,
`d/dp ℙ_p(A) = (p (1 - p))⁻¹ (𝔼_p[N 1_A] - 𝔼_p[N] ℙ_p(A))`, with `N` the number of open
coordinates. No monotonicity is assumed. See also `StatMech.hasDerivAt_prob_eq_sum_pivotalProb`
(pivotal form, increasing `A`) and `StatMech.Sharpness.hasDerivAt_prob_eq_pivotalFactor`.

L. Russo, *A note on percolation*, 1978; G. Grimmett, *Percolation*, 1999, Section 2.4. -/
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

/-- `deriv` form of `rus_russo_formula`. -/
theorem rus_russo_formula_deriv (A : Set (ConfigSpace E)) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    deriv (fun p => prob p A) p
      = (1 / (p * (1 - p))) *
        (rus_expect p (fun ω => rus_openCount ω * A.indicator (fun _ => (1 : ℝ)) ω)
          - rus_expect p (rus_openCount (E := E)) * prob p A) :=
  (rus_russo_formula A hp0 hp1).deriv

/-- For an increasing event, the covariance form of Russo's formula equals the expected number of
pivotal coordinates. -/
theorem rus_covariance_eq_sum_pivotalProb (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (1 / (p * (1 - p))) *
        (rus_expect p (fun ω => rus_openCount ω * A.indicator (fun _ => (1 : ℝ)) ω)
          - rus_expect p (rus_openCount (E := E)) * prob p A)
      = ∑ e, pivotalProb p A e := by
  have h1 := rus_russo_formula A hp0 hp1
  have h2 := hasDerivAt_prob_eq_sum_pivotalProb A hA p
  exact h1.unique h2

end Percolation

end StatMech
