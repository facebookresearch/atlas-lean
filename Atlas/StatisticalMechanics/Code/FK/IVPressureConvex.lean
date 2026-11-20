/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib
import Code.FK.Tilt
import Code.FK.RandomCluster
import Code.FK.SecantClose

open MeasureTheory Set Filter Topology Real Finset
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice









theorem ivp2_expmul_hasDerivAt (c t : ℝ) :
    HasDerivAt (fun s => Real.exp (c * s)) (c * Real.exp (c * t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => c * s) c t := by simpa using (hasDerivAt_id t).const_mul c
  have := (Real.hasDerivAt_exp (c * t)).comp t h1
  simpa [mul_comm] using this

variable {ι : Type*} [Fintype ι]



theorem ivp2_sumExp_hasDerivAt (b a : ι → ℝ) (t : ℝ) :
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


noncomputable def ivp2_Ssum (w a : ι → ℝ) (t : ℝ) : ℝ := ∑ i, w i * Real.exp (a i * t)


noncomputable def ivp2_S1 (w a : ι → ℝ) (t : ℝ) : ℝ := ∑ i, w i * a i * Real.exp (a i * t)


noncomputable def ivp2_S2 (w a : ι → ℝ) (t : ℝ) : ℝ := ∑ i, w i * a i ^ 2 * Real.exp (a i * t)


theorem ivp2_Ssum_pos (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) (t : ℝ) :
    0 < ivp2_Ssum w a t :=
  Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le)
    (by obtain ⟨j, hj⟩ := hpos; exact ⟨j, Finset.mem_univ j, mul_pos hj (Real.exp_pos _)⟩)


theorem ivp2_Ssum_hasDerivAt (w a : ι → ℝ) (t : ℝ) :
    HasDerivAt (ivp2_Ssum w a) (ivp2_S1 w a t) t :=
  ivp2_sumExp_hasDerivAt w a t


theorem ivp2_S1_hasDerivAt (w a : ι → ℝ) (t : ℝ) :
    HasDerivAt (ivp2_S1 w a) (ivp2_S2 w a t) t := by
  have h := ivp2_sumExp_hasDerivAt (fun i => w i * a i) a t
  have hfun : (fun s => ∑ i, (fun i => w i * a i) i * Real.exp (a i * s)) = ivp2_S1 w a := by
    funext s; rfl
  have hval : (∑ i, (fun i => w i * a i) i * a i * Real.exp (a i * t)) = ivp2_S2 w a t := by
    unfold ivp2_S2; apply Finset.sum_congr rfl; intro i _; ring
  rw [hfun, hval] at h; exact h






theorem ivp2_cauchy_schwarz_cgf (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (t : ℝ) :
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


noncomputable def ivp2_Kcgf (w a : ι → ℝ) (t : ℝ) : ℝ := Real.log (ivp2_Ssum w a t)


theorem ivp2_Kcgf_hasDerivAt (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) (t : ℝ) :
    HasDerivAt (ivp2_Kcgf w a) (ivp2_S1 w a t / ivp2_Ssum w a t) t := by
  have hS := ivp2_Ssum_hasDerivAt w a t
  have := hS.log (ivp2_Ssum_pos w a hw hpos t).ne'
  convert this using 1

theorem ivp2_deriv_Kcgf (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) :
    deriv (ivp2_Kcgf w a) = fun t => ivp2_S1 w a t / ivp2_Ssum w a t := by
  funext t; exact (ivp2_Kcgf_hasDerivAt w a hw hpos t).deriv



theorem ivp2_Kcgf_deriv2_hasDerivAt (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i)
    (t : ℝ) :
    HasDerivAt (fun s => ivp2_S1 w a s / ivp2_Ssum w a s)
      ((ivp2_S2 w a t * ivp2_Ssum w a t - ivp2_S1 w a t * ivp2_S1 w a t)
        / (ivp2_Ssum w a t) ^ 2) t := by
  have h1 := ivp2_S1_hasDerivAt w a t
  have h2 := ivp2_Ssum_hasDerivAt w a t
  have hne := (ivp2_Ssum_pos w a hw hpos t).ne'
  have := h1.div h2 hne
  convert this using 1



theorem ivp2_Kcgf_deriv2_nonneg (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i)
    (t : ℝ) : 0 ≤ (deriv^[2] (ivp2_Kcgf w a)) t := by
  show 0 ≤ deriv (deriv (ivp2_Kcgf w a)) t
  rw [ivp2_deriv_Kcgf w a hw hpos, (ivp2_Kcgf_deriv2_hasDerivAt w a hw hpos t).deriv]
  apply div_nonneg
  · have hcs := ivp2_cauchy_schwarz_cgf w a hw t
    nlinarith [hcs]
  · positivity






theorem ivp2_Kcgf_convexOn (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) :
    ConvexOn ℝ univ (ivp2_Kcgf w a) := by
  apply convexOn_univ_of_deriv2_nonneg
  · exact fun t => (ivp2_Kcgf_hasDerivAt w a hw hpos t).differentiableAt
  · rw [ivp2_deriv_Kcgf w a hw hpos]
    exact fun t => (ivp2_Kcgf_deriv2_hasDerivAt w a hw hpos t).differentiableAt
  · exact ivp2_Kcgf_deriv2_nonneg w a hw hpos









variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in



theorem ivp2_edgeProduct_logistic (t : ℝ) (ω : ConfigSpace (Sym2 V)) :
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





theorem ivp2_fkWeight_logistic (t q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    fkWeight G (fsc_logistic t) q ω
      = (q ^ numClusters G ω * Real.exp ((openCount G ω : ℝ) * t))
          / (1 + Real.exp t) ^ G.edgeFinset.card := by
  unfold fkWeight
  rw [ivp2_edgeProduct_logistic G t ω]
  ring






theorem ivp2_fkZ_logistic (t q : ℝ) :
    fkZ G (fsc_logistic t) q
      = ivp2_Ssum (fun ω => q ^ numClusters G ω) (fun ω => (openCount G ω : ℝ)) t
          / (1 + Real.exp t) ^ G.edgeFinset.card := by
  unfold fkZ ivp2_Ssum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  rw [ivp2_fkWeight_logistic G t q ω]













noncomputable def ivp2_tiltFreeEnergy (q : ℝ) (t : ℝ) : ℝ :=
  (1 / (G.edgeFinset.card : ℝ)) * Real.log (fkZ G (fsc_logistic t) q)
    + Real.log (1 + Real.exp t)







theorem ivp2_tiltFreeEnergy_eq_Kcgf (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card)
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









theorem ivp2_tiltFreeEnergy_convexOn (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card) :
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














theorem ivp2_convexOn_of_tendsto {κ : Type*} {l : Filter κ} [l.NeBot]
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









theorem ivp2_limitFreeEnergy_convexOn
    {κ : Type*} {l : Filter κ} [l.NeBot]
    {W : Type*} [Fintype W] [DecidableEq W]
    (Gn : κ → SimpleGraph W) [∀ i, DecidableRel (Gn i).Adj]
    (q : ℝ) (hq : 0 < q) (hE : ∀ i, 0 < (Gn i).edgeFinset.card)
    (g : ℝ → ℝ)
    (hlim : ∀ t, Tendsto (fun i => ivp2_tiltFreeEnergy (Gn i) q t) l (𝓝 (g t))) :
    ConvexOn ℝ univ g :=
  ivp2_convexOn_of_tendsto (fun i => ivp2_tiltFreeEnergy (Gn i) q) g
    (fun i => ivp2_tiltFreeEnergy_convexOn (Gn i) q hq (hE i)) hlim
















theorem ivp2_tiltFreeEnergy_hasDerivAt (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card)
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











theorem ivp2_cgfMean_eq_openCount_expect (q : ℝ) (hq : 0 < q) (t : ℝ) :
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
















theorem ivp2_freeEnergyData_convex_part
    {κ : Type*} {l : Filter κ} [l.NeBot]
    {W : Type*} [Fintype W] [DecidableEq W]
    (Gn : κ → SimpleGraph W) [∀ i, DecidableRel (Gn i).Adj]
    (q : ℝ) (hq : 0 < q) (hE : ∀ i, 0 < (Gn i).edgeFinset.card)
    (g : ℝ → ℝ)
    (hlim : ∀ t, Tendsto (fun i => ivp2_tiltFreeEnergy (Gn i) q t) l (𝓝 (g t))) :
    ConvexOn ℝ univ g :=
  ivp2_limitFreeEnergy_convexOn Gn q hq hE g hlim











noncomputable def ivp2_softplus (t : ℝ) : ℝ := Real.log (1 + Real.exp t)



theorem ivp2_softplus_convexOn : ConvexOn ℝ univ ivp2_softplus := by
  have hconv : ConvexOn ℝ univ (ivp2_Kcgf (fun _ : Bool => (1:ℝ)) (fun b => if b then 1 else 0)) :=
    ivp2_Kcgf_convexOn _ _ (fun _ => zero_le_one) ⟨false, one_pos⟩
  have heq : ivp2_softplus
      = ivp2_Kcgf (fun _ : Bool => (1:ℝ)) (fun b => if b then 1 else 0) := by
    funext t
    unfold ivp2_softplus ivp2_Kcgf ivp2_Ssum
    congr 1
    rw [Fintype.sum_bool]
    simp [add_comm]
  rw [heq]; exact hconv

end FK

end StatMech
