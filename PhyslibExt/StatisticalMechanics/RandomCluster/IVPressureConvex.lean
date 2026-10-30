/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.LogitFreeEnergyComparison
/-!
# Convexity of the random-cluster free energy in the logit parameter

The finite-volume random-cluster free energy, as a function of `t = logit p`, is a cumulant
generating function and hence convex; pointwise limits of convex functions are convex, so every
infinite-volume limit of it is convex.

## i. Overview

For finite `ι`, weights `w ≥ 0` (not all zero) and reals `a`, the function
`ivp2_Kcgf w a t = log ∑_i w_i e^{a_i t}` is convex: its second derivative is
`(S₂ S₀ - S₁²) / S₀² ≥ 0` by Cauchy–Schwarz (`ivp2_Kcgf_convexOn`). With
`p = fsc_logistic t`, the random-cluster weight is
`q ^ k(ω) e^{o(ω) t} / (1 + eᵗ) ^ |E|` (`ivp2_fkWeight_logistic`), so
`ivp2_tiltFreeEnergy G q t = |E|⁻¹ log Z_{G, p(t), q} + log (1 + eᵗ)` equals
`|E|⁻¹ ivp2_Kcgf (q ^ k) o t` and is convex (`ivp2_tiltFreeEnergy_convexOn`). Its derivative is
`|E|⁻¹` times the mean number of open edges (`ivp2_tiltFreeEnergy_hasDerivAt`,
`ivp2_cgfMean_eq_openCount_expect`). Any pointwise limit along a sequence of graphs is convex
(`ivp2_limitFreeEnergy_convexOn`).

## ii. Key results

- `StatMech.FK.ivp2_Kcgf` : the log-sum-exp (cumulant generating) function, with
  `ivp2_Kcgf_convexOn`.
- `StatMech.FK.ivp2_tiltFreeEnergy` : the finite-volume free energy in the logit parameter,
  with `ivp2_tiltFreeEnergy_convexOn` and `ivp2_tiltFreeEnergy_hasDerivAt`.
- `StatMech.FK.ivp2_convexOn_of_tendsto` : a pointwise limit of convex functions is convex.
- `StatMech.FK.ivp2_limitFreeEnergy_convexOn` : convexity of infinite-volume limits.

## iii. Table of contents

- A. Log-sum-exp functions
  - A.1. Derivatives
  - A.2. Convexity
- B. The random-cluster free energy in the logit parameter
- C. Limits of convex functions
- D. Derivative of the free energy

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapter 4.

-/

@[expose] public section

open MeasureTheory Set Filter Topology Real Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

/-!

## A. Log-sum-exp functions

### A.1. Derivatives

-/

lemma ivp2_expmul_hasDerivAt (c t : ℝ) :
    HasDerivAt (fun s => Real.exp (c * s)) (c * Real.exp (c * t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => c * s) c t := by simpa using (hasDerivAt_id t).const_mul c
  have := (Real.hasDerivAt_exp (c * t)).comp t h1
  simpa [mul_comm, Function.comp_def] using this

variable {ι : Type*} [Fintype ι]

lemma ivp2_sumExp_hasDerivAt (b a : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∑ i, b i * Real.exp (a i * s))
      (∑ i, b i * a i * Real.exp (a i * t)) t := by
  have key : HasDerivAt (∑ i : ι, fun s => b i * Real.exp (a i * s))
      (∑ i, b i * (a i * Real.exp (a i * t))) t :=
    HasDerivAt.sum (fun i _ => (ivp2_expmul_hasDerivAt (a i) t).const_mul (b i))
  have hfun : (∑ i : ι, fun s => b i * Real.exp (a i * s))
      = fun s => ∑ i, b i * Real.exp (a i * s) := by funext s; rw [Finset.sum_apply]
  rw [hfun] at key
  have heq : (∑ i, b i * (a i * Real.exp (a i * t)))
      = ∑ i, b i * a i * Real.exp (a i * t) := by
    apply Finset.sum_congr rfl; intro i _; ring
  rw [heq] at key; exact key

/-- The exponential sum `S₀(t) = ∑_i w_i e^{a_i t}`. -/
noncomputable def ivp2_Ssum (w a : ι → ℝ) (t : ℝ) : ℝ := ∑ i, w i * Real.exp (a i * t)

/-- The first moment sum `S₁(t) = ∑_i w_i a_i e^{a_i t}`, the derivative of `S₀`. -/
noncomputable def ivp2_S1 (w a : ι → ℝ) (t : ℝ) : ℝ := ∑ i, w i * a i * Real.exp (a i * t)

/-- The second moment sum `S₂(t) = ∑_i w_i a_i² e^{a_i t}`, the derivative of `S₁`. -/
noncomputable def ivp2_S2 (w a : ι → ℝ) (t : ℝ) : ℝ := ∑ i, w i * a i ^ 2 * Real.exp (a i * t)

lemma ivp2_Ssum_pos (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) (t : ℝ) :
    0 < ivp2_Ssum w a t :=
  Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le)
    (by obtain ⟨j, hj⟩ := hpos; exact ⟨j, Finset.mem_univ j, mul_pos hj (Real.exp_pos _)⟩)

lemma ivp2_Ssum_hasDerivAt (w a : ι → ℝ) (t : ℝ) :
    HasDerivAt (ivp2_Ssum w a) (ivp2_S1 w a t) t :=
  ivp2_sumExp_hasDerivAt w a t

lemma ivp2_S1_hasDerivAt (w a : ι → ℝ) (t : ℝ) :
    HasDerivAt (ivp2_S1 w a) (ivp2_S2 w a t) t := by
  have h := ivp2_sumExp_hasDerivAt (fun i => w i * a i) a t
  have hfun : (fun s => ∑ i, (fun i => w i * a i) i * Real.exp (a i * s)) = ivp2_S1 w a := by
    funext s; rfl
  have hval : (∑ i, (fun i => w i * a i) i * a i * Real.exp (a i * t)) = ivp2_S2 w a t := by
    unfold ivp2_S2; apply Finset.sum_congr rfl; intro i _; ring
  rw [hfun, hval] at h; exact h

/-!

### A.2. Convexity

-/

/-- Cauchy–Schwarz for the exponential sums: `S₁² ≤ S₂ S₀`. -/
lemma ivp2_cauchy_schwarz_cgf (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (t : ℝ) :
    (ivp2_S1 w a t) ^ 2 ≤ (ivp2_S2 w a t) * (ivp2_Ssum w a t) := by
  unfold ivp2_S1 ivp2_S2 ivp2_Ssum
  set f : ι → ℝ := fun i => Real.sqrt (w i * Real.exp (a i * t)) * a i with hf
  set g : ι → ℝ := fun i => Real.sqrt (w i * Real.exp (a i * t)) with hg
  have hcs := sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have e1 : (∑ i, f i * g i) = ∑ i, w i * a i * Real.exp (a i * t) := by
    apply Finset.sum_congr rfl; intro i _; simp only [hf, hg]
    rw [mul_right_comm, Real.mul_self_sqrt (mul_nonneg (hw i) (Real.exp_pos _).le)]; ring
  have e2 : (∑ i, f i ^ 2) = ∑ i, w i * a i ^ 2 * Real.exp (a i * t) := by
    apply Finset.sum_congr rfl; intro i _; simp only [hf]
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (hw i) (Real.exp_pos _).le)]; ring
  have e3 : (∑ i, g i ^ 2) = ∑ i, w i * Real.exp (a i * t) := by
    apply Finset.sum_congr rfl; intro i _; simp only [hg]
    rw [Real.sq_sqrt (mul_nonneg (hw i) (Real.exp_pos _).le)]
  rw [e1, e2, e3] at hcs; exact hcs

/-- The log-sum-exp function `K(t) = log ∑_i w_i e^{a_i t}`, the cumulant generating function of
`a` under the weights `w`. -/
noncomputable def ivp2_Kcgf (w a : ι → ℝ) (t : ℝ) : ℝ := Real.log (ivp2_Ssum w a t)

lemma ivp2_Kcgf_hasDerivAt (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) (t : ℝ) :
    HasDerivAt (ivp2_Kcgf w a) (ivp2_S1 w a t / ivp2_Ssum w a t) t := by
  have hS := ivp2_Ssum_hasDerivAt w a t
  have := hS.log (ivp2_Ssum_pos w a hw hpos t).ne'
  exact this

lemma ivp2_deriv_Kcgf (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) :
    deriv (ivp2_Kcgf w a) = fun t => ivp2_S1 w a t / ivp2_Ssum w a t := by
  funext t; exact (ivp2_Kcgf_hasDerivAt w a hw hpos t).deriv

lemma ivp2_Kcgf_deriv2_hasDerivAt (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i)
    (t : ℝ) :
    HasDerivAt (fun s => ivp2_S1 w a s / ivp2_Ssum w a s)
      ((ivp2_S2 w a t * ivp2_Ssum w a t - ivp2_S1 w a t * ivp2_S1 w a t)
        / (ivp2_Ssum w a t) ^ 2) t := by
  have h1 := ivp2_S1_hasDerivAt w a t
  have h2 := ivp2_Ssum_hasDerivAt w a t
  have hne := (ivp2_Ssum_pos w a hw hpos t).ne'
  have := h1.div h2 hne
  convert this using 1

lemma ivp2_Kcgf_deriv2_nonneg (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i)
    (t : ℝ) : 0 ≤ (deriv^[2] (ivp2_Kcgf w a)) t := by
  change 0 ≤ deriv (deriv (ivp2_Kcgf w a)) t
  rw [ivp2_deriv_Kcgf w a hw hpos, (ivp2_Kcgf_deriv2_hasDerivAt w a hw hpos t).deriv]
  apply div_nonneg
  · have hcs := ivp2_cauchy_schwarz_cgf w a hw t
    nlinarith [hcs]
  · positivity

/-- A cumulant generating function is convex. -/
lemma ivp2_Kcgf_convexOn (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) :
    ConvexOn ℝ univ (ivp2_Kcgf w a) := by
  apply convexOn_univ_of_deriv2_nonneg
  · exact fun t => (ivp2_Kcgf_hasDerivAt w a hw hpos t).differentiableAt
  · rw [ivp2_deriv_Kcgf w a hw hpos]
    exact fun t => (ivp2_Kcgf_deriv2_hasDerivAt w a hw hpos t).differentiableAt
  · exact ivp2_Kcgf_deriv2_nonneg w a hw hpos

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-!

## B. The random-cluster free energy in the logit parameter

-/

omit [DecidableEq V] in
lemma ivp2_edgeProduct_logistic (t : ℝ) (ω : ConfigSpace (Sym2 V)) :
    edgeProduct G (fsc_logistic t) ω
      = Real.exp (openCount G ω * t) / (1 + Real.exp t) ^ G.edgeFinset.card := by
  rw [edgeProduct_eq_pow]
  unfold fsc_logistic
  have hpos : (0:ℝ) < 1 + Real.exp t := by positivity
  have h1 : (1 : ℝ) - Real.exp t / (1 + Real.exp t) = 1 / (1 + Real.exp t) := by
    field_simp; ring
  have hexp : Real.exp (openCount G ω * t) = (Real.exp t) ^ (openCount G ω) := by
    rw [← Real.exp_nat_mul]
  rw [h1, div_pow, div_pow, one_pow, ← openCount_add_closedCount G ω, pow_add, hexp]
  field_simp

lemma ivp2_fkWeight_logistic (t q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    fkWeight G (fsc_logistic t) q ω
      = (q ^ numClusters G ω * Real.exp ((openCount G ω : ℝ) * t))
          / (1 + Real.exp t) ^ G.edgeFinset.card := by
  unfold fkWeight
  rw [ivp2_edgeProduct_logistic G t ω]
  ring

lemma ivp2_fkZ_logistic (t q : ℝ) :
    fkZ G (fsc_logistic t) q
      = ivp2_Ssum (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t
          / (1 + Real.exp t) ^ G.edgeFinset.card := by
  unfold fkZ ivp2_Ssum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  rw [ivp2_fkWeight_logistic G t q ω]

/-- The finite-volume random-cluster free energy in the logit parameter:
`|E|⁻¹ log Z_{G, p, q} + log (1 + eᵗ)` with `p = fsc_logistic t`. The added term removes the
normalization `(1 + eᵗ) ^ (-|E|)` of the Bernoulli factors. -/
noncomputable def ivp2_tiltFreeEnergy (q : ℝ) (t : ℝ) : ℝ :=
  (1 / (G.edgeFinset.card : ℝ)) * Real.log (fkZ G (fsc_logistic t) q)
    + Real.log (1 + Real.exp t)

lemma ivp2_tiltFreeEnergy_eq_Kcgf (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card)
    (t : ℝ) :
    ivp2_tiltFreeEnergy G q t
      = (1 / (G.edgeFinset.card : ℝ))
          * ivp2_Kcgf (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t := by
  unfold ivp2_tiltFreeEnergy ivp2_Kcgf
  set w : ConfigSpace (Sym2 V) → ℝ := fun ω => q ^ numClusters G ω with hw
  set a : ConfigSpace (Sym2 V) → ℝ := fun ω => (openCount G ω : ℝ) with ha
  have hwnn : ∀ ω, 0 ≤ w ω := fun ω => pow_nonneg hq.le _
  have hwpos : ∃ ω, 0 < w ω := ⟨Classical.arbitrary _, pow_pos hq _⟩
  have hSpos : 0 < ivp2_Ssum w a t := ivp2_Ssum_pos w a hwnn hwpos t
  have hEpos : (0:ℝ) < 1 + Real.exp t := by positivity
  have hElt : (0:ℝ) < (1 + Real.exp t) ^ G.edgeFinset.card := by positivity
  have hZ : fkZ G (fsc_logistic t) q = ivp2_Ssum w a t / (1 + Real.exp t) ^ G.edgeFinset.card :=
    ivp2_fkZ_logistic G t q
  rw [hZ, Real.log_div hSpos.ne' hElt.ne', Real.log_pow]
  have hEne : (G.edgeFinset.card : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
  field_simp
  ring

/-- The finite-volume free energy is convex in `t`. -/
lemma ivp2_tiltFreeEnergy_convexOn (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card) :
    ConvexOn ℝ univ (ivp2_tiltFreeEnergy G q) := by
  set w : ConfigSpace (Sym2 V) → ℝ := fun ω => q ^ numClusters G ω with hw
  set a : ConfigSpace (Sym2 V) → ℝ := fun ω => (openCount G ω : ℝ) with ha
  have hwnn : ∀ ω, 0 ≤ w ω := fun ω => pow_nonneg hq.le _
  have hwpos : ∃ ω, 0 < w ω := ⟨Classical.arbitrary _, pow_pos hq _⟩
  have hconv : ConvexOn ℝ univ (ivp2_Kcgf w a) := ivp2_Kcgf_convexOn w a hwnn hwpos
  have hsmul : ConvexOn ℝ univ (fun t => (1 / (G.edgeFinset.card : ℝ)) * ivp2_Kcgf w a t) := by
    have hc : (0:ℝ) ≤ 1 / (G.edgeFinset.card : ℝ) := by positivity
    exact hconv.smul hc
  have heq : ivp2_tiltFreeEnergy G q
      = fun t => (1 / (G.edgeFinset.card : ℝ)) * ivp2_Kcgf w a t := by
    funext t; exact ivp2_tiltFreeEnergy_eq_Kcgf G q hq hE t
  rw [heq]; exact hsmul

/-!

## C. Limits of convex functions

-/

/-- A pointwise limit of convex functions on `ℝ` along a nontrivial filter is convex. -/
lemma ivp2_convexOn_of_tendsto {κ : Type*} {l : Filter κ} [l.NeBot]
    (f : κ → ℝ → ℝ) (g : ℝ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ univ (f i))
    (hlim : ∀ x, Tendsto (fun i => f i x) l (𝓝 (g x))) :
    ConvexOn ℝ univ g := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  have hle : ∀ i, f i (s • x + t • y) ≤ s • f i x + t • f i y := fun i =>
    (hconv i).2 (mem_univ x) (mem_univ y) hs ht hst
  have h1 := hlim (s • x + t • y)
  have h2 : Tendsto (fun i => s • f i x + t • f i y) l (𝓝 (s • g x + t • g y)) :=
    Tendsto.add ((hlim x).const_smul s) ((hlim y).const_smul t)
  exact le_of_tendsto_of_tendsto h1 h2 (Filter.Eventually.of_forall hle)

/-- Every pointwise limit of finite-volume free energies along a nontrivial filter is convex. -/
lemma ivp2_limitFreeEnergy_convexOn
    {κ : Type*} {l : Filter κ} [l.NeBot]
    {W : Type*} [Fintype W] [DecidableEq W]
    (Gn : κ → SimpleGraph W) [∀ i, DecidableRel (Gn i).Adj]
    (q : ℝ) (hq : 0 < q) (hE : ∀ i, 0 < (Gn i).edgeFinset.card)
    (g : ℝ → ℝ)
    (hlim : ∀ t, Tendsto (fun i => ivp2_tiltFreeEnergy (Gn i) q t) l (𝓝 (g t))) :
    ConvexOn ℝ univ g :=
  ivp2_convexOn_of_tendsto (fun i => ivp2_tiltFreeEnergy (Gn i) q) g
    (fun i => ivp2_tiltFreeEnergy_convexOn (Gn i) q hq (hE i)) hlim

/-!

## D. Derivative of the free energy

-/

lemma ivp2_tiltFreeEnergy_hasDerivAt (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card)
    (t : ℝ) :
    HasDerivAt (ivp2_tiltFreeEnergy G q)
      ((1 / (G.edgeFinset.card : ℝ))
        * (ivp2_S1 (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t
            / ivp2_Ssum (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t)) t := by
  set w : ConfigSpace (Sym2 V) → ℝ := fun ω => q ^ numClusters G ω with hw
  set a : ConfigSpace (Sym2 V) → ℝ := fun ω => (openCount G ω : ℝ) with ha
  have hwnn : ∀ ω, 0 ≤ w ω := fun ω => pow_nonneg hq.le _
  have hwpos : ∃ ω, 0 < w ω := ⟨Classical.arbitrary _, pow_pos hq _⟩
  have heq : ivp2_tiltFreeEnergy G q
      = fun t => (1 / (G.edgeFinset.card : ℝ)) * ivp2_Kcgf w a t := by
    funext t; exact ivp2_tiltFreeEnergy_eq_Kcgf G q hq hE t
  rw [heq]
  exact (ivp2_Kcgf_hasDerivAt w a hwnn hwpos t).const_mul _

lemma ivp2_cgfMean_eq_openCount_expect (q : ℝ) (hq : 0 < q) (t : ℝ) :
    fkExpect G (fsc_logistic t) q (fun ω => (openCount G ω : ℝ))
      = ivp2_S1 (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t
          / ivp2_Ssum (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t := by
  have hSpos : (0:ℝ) < ivp2_Ssum (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t :=
    ivp2_Ssum_pos _ _ (fun ω => pow_nonneg hq.le _) ⟨Classical.arbitrary _, pow_pos hq _⟩ t
  unfold ivp2_Ssum at hSpos
  have hEpos : (0:ℝ) < (1 + Real.exp t) ^ G.edgeFinset.card := by positivity
  unfold fkExpect ivp2_S1 ivp2_Ssum fkProb
  rw [ivp2_fkZ_logistic G t q, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  rw [ivp2_fkWeight_logistic G t q ω]
  unfold ivp2_Ssum
  rw [show (q ^ numClusters G ω * Real.exp ((openCount G ω : ℝ) * t)
        / (1 + Real.exp t) ^ G.edgeFinset.card)
        / ((∑ i, q ^ numClusters G i * Real.exp ((openCount G i : ℝ) * t))
            / (1 + Real.exp t) ^ G.edgeFinset.card)
      = q ^ numClusters G ω * Real.exp ((openCount G ω : ℝ) * t)
          / (∑ i, q ^ numClusters G i * Real.exp ((openCount G i : ℝ) * t)) from
    div_div_div_cancel_right₀ hEpos.ne' _ _]
  rw [div_mul_eq_mul_div]
  ring_nf

end FK

end StatMech
