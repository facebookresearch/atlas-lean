/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
/-!
# Weierstrass factorization (closed discrete zero set, simple zeros)
-/

namespace MathlibExt.Analysis.Complex.WeierstrassFactorizationWanted

open Set Filter Metric Topology

/-- Weierstrass elementary factor: `(1 - w) * exp(-logTaylor (p+1) (-w))`. -/
private noncomputable def wfElemFactor (p : ℕ) (w : ℂ) : ℂ :=
  (1 - w) * Complex.exp (-(Complex.logTaylor (p + 1) (-w)))

/-- N1: a closed discrete set meets every closed ball in a finite set. -/
private theorem wf_isClosed_inter_closedBall_finite (S : Set ℂ) (hS_closed : IsClosed S)
    (hS_discrete : ∀ z ∈ S, ∃ ε > 0, (Metric.ball z ε \ {z}) ∩ S = ∅)
    (R : ℝ) : (S ∩ Metric.closedBall 0 R).Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  have hcomp : IsCompact (S ∩ Metric.closedBall 0 R) :=
    IsCompact.inter_left (isCompact_closedBall 0 R) hS_closed
  obtain ⟨x, hxK, hacc⟩ := hinf.exists_accPt_of_subset_isCompact hcomp (Subset.rfl)
  have hxS : x ∈ S := hxK.1
  obtain ⟨ε, hεpos, hε⟩ := hS_discrete x hxS
  rw [accPt_iff_nhds] at hacc
  obtain ⟨y, ⟨hyU, hyK⟩, hyne⟩ := hacc (Metric.ball x ε) (Metric.ball_mem_nhds x hεpos)
  have hyS : y ∈ S := (hyK : y ∈ S ∩ Metric.closedBall 0 R).1
  have hymem : y ∈ (Metric.ball x ε \ {x}) ∩ S := ⟨⟨hyU, hyne⟩, hyS⟩
  rw [hε] at hymem
  exact Set.notMem_empty y hymem

/-- N2: a locally finite set in ℂ admits an injection into ℕ. -/
private theorem wf_exists_injective_nat (S : Set ℂ)
    (hfin : ∀ R : ℝ, (S ∩ Metric.closedBall 0 R).Finite) :
    ∃ e : ↥S → ℕ, Function.Injective e := by
  have hsub : S ⊆ ⋃ n : ℕ, S ∩ Metric.closedBall 0 n := by
    intro z hz
    obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
    exact Set.mem_iUnion.mpr ⟨n, hz, mem_closedBall_zero_iff.mpr (le_of_lt hn)⟩
  have hunion : Set.Countable (⋃ n : ℕ, S ∩ Metric.closedBall 0 n) := by
    apply Set.countable_iUnion
    intro n
    exact (hfin n).countable
  have hcount : Set.Countable S := hunion.mono hsub
  have hsubtype : Countable ↥S := Set.Countable.to_subtype hcount
  exact exists_injective_nat ↥S

/-- N3: a discrete set is not all of ℂ. -/
private theorem wf_exists_not_mem (S : Set ℂ)
    (hS_discrete : ∀ z ∈ S, ∃ ε > 0, (Metric.ball z ε \ {z}) ∩ S = ∅) :
    ∃ c : ℂ, c ∉ S := by
  by_cases h0 : (0 : ℂ) ∈ S
  · obtain ⟨ε, hεpos, hε⟩ := hS_discrete 0 h0
    refine ⟨(ε / 2 : ℝ), ?_⟩
    intro hc
    have hnorm : ‖((ε / 2 : ℝ) : ℂ)‖ = ε / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε / 2)]
    have hmem_ball : ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
      rw [mem_ball_zero_iff, hnorm]
      linarith
    have hne : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      linarith
    have hymem : ((ε / 2 : ℝ) : ℂ) ∈ (Metric.ball (0 : ℂ) ε \ {0}) ∩ S :=
      ⟨⟨hmem_ball, hne⟩, hc⟩
    rw [hε] at hymem
    exact Set.notMem_empty _ hymem
  · exact ⟨0, h0⟩

/-- N4a: the elementary factor is entire. -/
private theorem wfElemFactor_differentiable (p : ℕ) : Differentiable ℂ (wfElemFactor p) := by
  unfold wfElemFactor
  have hlog : Differentiable ℂ (Complex.logTaylor (p + 1)) :=
    fun z => (Complex.hasDerivAt_logTaylor p z).differentiableAt
  have h1 : Differentiable ℂ (fun w : ℂ => 1 - w) :=
    Differentiable.const_sub differentiable_id 1
  have h2 : Differentiable ℂ (fun w : ℂ => Complex.logTaylor (p + 1) (-w)) :=
    hlog.comp differentiable_id.neg
  have h3 : Differentiable ℂ (fun w : ℂ => -(Complex.logTaylor (p + 1) (-w))) := h2.neg
  have h4 : Differentiable ℂ (fun w : ℂ => Complex.exp (-(Complex.logTaylor (p + 1) (-w)))) :=
    h3.cexp
  exact h1.mul h4

/-- N4b: the elementary factor vanishes exactly at `w = 1`. -/
private theorem wfElemFactor_eq_zero_iff (p : ℕ) (w : ℂ) :
    wfElemFactor p w = 0 ↔ w = 1 := by
  unfold wfElemFactor
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · rw [sub_eq_zero] at h
      exact h.symm
    · exact absurd h (Complex.exp_ne_zero _)
  · intro h
    left
    rw [sub_eq_zero]
    exact h.symm

/-- N4c: the elementary factor has nonzero derivative at `w = 1`. -/
private theorem wfElemFactor_hasDerivAt_one (p : ℕ) :
    HasDerivAt (wfElemFactor p) (-Complex.exp (-Complex.logTaylor (p + 1) (-1))) 1 := by
  have hlog : Differentiable ℂ (Complex.logTaylor (p + 1)) :=
    fun z => (Complex.hasDerivAt_logTaylor p z).differentiableAt
  have h2 : Differentiable ℂ (fun w : ℂ => Complex.logTaylor (p + 1) (-w)) :=
    hlog.comp differentiable_id.neg
  have h3 : Differentiable ℂ (fun w : ℂ => -(Complex.logTaylor (p + 1) (-w))) := h2.neg
  have hexp : Differentiable ℂ (fun w : ℂ => Complex.exp (-(Complex.logTaylor (p + 1) (-w)))) :=
    h3.cexp
  have hh' : HasDerivAt (fun w : ℂ => Complex.exp (-(Complex.logTaylor (p + 1) (-w))))
      (deriv (fun w : ℂ => Complex.exp (-(Complex.logTaylor (p + 1) (-w)))) 1) 1 :=
    hexp.differentiableAt.hasDerivAt
  have hder1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) (1 : ℂ) :=
    (hasDerivAt_id (1 : ℂ)).const_sub 1
  have hmul := hder1.mul hh'
  have hval : (-1 : ℂ) * Complex.exp (-Complex.logTaylor (p + 1) (-(1 : ℂ))) +
        (1 - (1 : ℂ)) * deriv (fun w : ℂ => Complex.exp (-(Complex.logTaylor (p + 1) (-w)))) 1 =
      -Complex.exp (-Complex.logTaylor (p + 1) (-1)) := by
    simp
  rw [hval] at hmul
  exact hmul

private theorem wfElemFactor_deriv_one_ne_zero (p : ℕ) :
    (deriv (wfElemFactor p) 1) ≠ 0 := by
  have h := wfElemFactor_hasDerivAt_one p
  rw [h.deriv]
  apply neg_ne_zero.mpr
  exact Complex.exp_ne_zero _

/-- N5: elementary-factor estimate on the half-disk. -/
private theorem norm_wfElemFactor_sub_one_le (p : ℕ) (w : ℂ) (hw : ‖w‖ ≤ 1 / 2) :
    ‖wfElemFactor p w - 1‖ ≤ 4 * ‖w‖ ^ (p + 1) := by
  have ht_nonneg : 0 ≤ ‖w‖ := norm_nonneg _
  have hw_lt1 : ‖w‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have hneg_lt1 : ‖-w‖ < 1 := by rwa [norm_neg]
  have h1w : (1 : ℂ) - w ≠ 0 := by
    intro h
    have heq : w = 1 := by linear_combination -h
    rw [heq, norm_one] at hw
    norm_num at hw
  have h1w' : (1 : ℂ) + (-w) ≠ 0 := by
    rwa [sub_eq_add_neg] at h1w
  have hexp : (1 : ℂ) - w = Complex.exp (Complex.log (1 + (-w))) := by
    have h := Complex.exp_log h1w'
    have heq : (1 : ℂ) - w = 1 + (-w) := by ring
    rw [heq]
    exact h.symm
  have hfactor : wfElemFactor p w =
      Complex.exp (Complex.log (1 + (-w)) - Complex.logTaylor (p + 1) (-w)) := by
    unfold wfElemFactor
    rw [hexp, ← Complex.exp_add, sub_eq_add_neg]
  have hbound := Complex.norm_log_sub_logTaylor_le p hneg_lt1
  rw [norm_neg] at hbound
  set t := ‖w‖ with ht
  set L := Complex.log (1 + (-w)) - Complex.logTaylor (p + 1) (-w) with hL
  have h1mt : (1 / 2 : ℝ) ≤ 1 - t := by linarith
  have h1mt_pos : (0 : ℝ) < 1 - t := by linarith
  have hinv_le : (1 - t)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ h1mt_pos]
    linarith
  have hcast : (1 : ℝ) ≤ (p : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    linarith
  have hdiv_le : (1 : ℝ) / ((p : ℝ) + 1) ≤ 1 := by
    apply div_le_one_of_le₀ hcast (by positivity)
  have hpow_nonneg : (0 : ℝ) ≤ t ^ (p + 1) := pow_nonneg ht_nonneg _
  have hexp_bound : ‖L‖ ≤ 2 * t ^ (p + 1) := by
    have h1 : t ^ (p + 1) * (1 - t)⁻¹ / ((p : ℝ) + 1) ≤ 2 * t ^ (p + 1) := by
      have h2 : t ^ (p + 1) * (1 - t)⁻¹ / ((p : ℝ) + 1) =
          t ^ (p + 1) * ((1 - t)⁻¹ * (1 / ((p : ℝ) + 1))) := by ring
      rw [h2]
      have h3 : (1 - t)⁻¹ * (1 / ((p : ℝ) + 1)) ≤ 2 * 1 := by
        apply mul_le_mul hinv_le hdiv_le (by positivity) (by norm_num)
      calc t ^ (p + 1) * ((1 - t)⁻¹ * (1 / ((p : ℝ) + 1)))
          ≤ t ^ (p + 1) * (2 * 1) :=
            mul_le_mul_of_nonneg_left h3 hpow_nonneg
        _ = 2 * t ^ (p + 1) := by ring
    exact le_trans hbound h1
  have hL_le_one : ‖L‖ ≤ 1 := by
    have ht1 : t ≤ 1 := le_trans hw (by norm_num)
    have htp : t ^ p ≤ 1 := pow_le_one₀ ht_nonneg ht1
    have hpow_half : t ^ (p + 1) ≤ 1 / 2 := by
      calc t ^ (p + 1) = t ^ p * t := by ring
        _ ≤ 1 * (1 / 2) := mul_le_mul htp hw (by linarith) (by norm_num)
        _ = 1 / 2 := by ring
    linarith
  have hexp_le := Complex.norm_exp_sub_one_le hL_le_one
  rw [hfactor]
  calc ‖Complex.exp L - 1‖ ≤ 2 * ‖L‖ := hexp_le
    _ ≤ 2 * (2 * t ^ (p + 1)) := mul_le_mul_of_nonneg_left hexp_bound (by norm_num)
    _ = 4 * t ^ (p + 1) := by ring

/-- N6: an infinite product with a local summable bound is entire. -/
private theorem wf_differentiable_tprod_of_localBound (ι : Type*) (g : ι → ℂ → ℂ)
    (hg : ∀ i, Differentiable ℂ (g i))
    (hlb : ∀ R : ℝ, ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in Filter.cofinite, ∀ z : ℂ, ‖z‖ ≤ R → ‖g i z - 1‖ ≤ u i) :
    Differentiable ℂ (fun z => ∏' i, g i z) := by
  intro z₀
  set R : ℝ := ‖z₀‖ + 1 with hR
  obtain ⟨u, hu, hbound⟩ := hlb R
  have hz₀R : z₀ ∈ Metric.ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    linarith [norm_nonneg z₀]
  have hboundU : ∀ᶠ i in Filter.cofinite, ∀ x ∈ Metric.ball (0 : ℂ) R, ‖g i x - 1‖ ≤ u i := by
    filter_upwards [hbound] with i hi x hx
    apply hi
    rw [mem_ball_zero_iff] at hx
    exact le_of_lt hx
  have hcont : ∀ i, ContinuousOn (fun x => g i x - 1) (Metric.ball (0 : ℂ) R) :=
    fun i => ((hg i).continuous.sub continuous_const).continuousOn
  have hprod : HasProdLocallyUniformlyOn g (fun x => ∏' i, g i x) (Metric.ball (0 : ℂ) R) := by
    have h := hu.hasProdLocallyUniformlyOn_one_add (K := Metric.ball (0 : ℂ) R)
      (f := fun i x => g i x - 1) Metric.isOpen_ball hboundU hcont
    simpa [add_sub_cancel] using h
  have htend : TendstoLocallyUniformlyOn (fun s x => ∏ i ∈ s, g i x)
      (fun x => ∏' i, g i x) Filter.atTop (Metric.ball (0 : ℂ) R) :=
    hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod
  have hparts : ∀ᶠ s : Finset ι in Filter.atTop,
      DifferentiableOn ℂ ((fun s x => ∏ i ∈ s, g i x) s) (Metric.ball (0 : ℂ) R) := by
    apply Filter.Eventually.of_forall
    intro s
    simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (fun i _ => ((hg i).differentiableOn))
  have hdiff : DifferentiableOn ℂ (fun x => ∏' i, g i x) (Metric.ball (0 : ℂ) R) :=
    htend.differentiableOn hparts Metric.isOpen_ball
  exact (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hz₀R))

/-- N7a: pointwise summability from the local bound. -/
private theorem wf_summable_norm (ι : Type*) (g : ι → ℂ → ℂ)
    (hlb : ∀ R : ℝ, ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in Filter.cofinite, ∀ z : ℂ, ‖z‖ ≤ R → ‖g i z - 1‖ ≤ u i)
    (z : ℂ) : Summable (fun i => ‖g i z - 1‖) := by
  obtain ⟨u, hu, hev⟩ := hlb ‖z‖
  apply hu.of_norm_bounded_eventually
  filter_upwards [hev] with i hi
  rw [norm_norm]
  exact hi z le_rfl

/-- N7b: a convergent product with no vanishing factor is nonzero. -/
private theorem wf_tprod_ne_zero (ι : Type*) (g : ι → ℂ → ℂ)
    (hlb : ∀ R : ℝ, ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in Filter.cofinite, ∀ z : ℂ, ‖z‖ ≤ R → ‖g i z - 1‖ ≤ u i)
    (z : ℂ) (hne : ∀ i, g i z ≠ 0) : ∏' i, g i z ≠ 0 := by
  have hs := wf_summable_norm ι g hlb z
  have h := tprod_one_add_ne_zero_of_summable (f := fun i => g i z - 1)
    (fun i => by simpa [add_sub_cancel] using hne i) hs
  simpa [add_sub_cancel] using h

/-- N7c: splitting off one factor. -/
private theorem wf_tprod_split (ι : Type*) [DecidableEq ι] (g : ι → ℂ → ℂ)
    (hlb : ∀ R : ℝ, ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in Filter.cofinite, ∀ z : ℂ, ‖z‖ ≤ R → ‖g i z - 1‖ ≤ u i)
    (z : ℂ) (b : ι) :
    ∏' i, g i z = g b z * ∏' i, (if i = b then 1 else g i z) := by
  have hs := wf_summable_norm ι g hlb z
  have hle : ∀ i, ‖Function.update (fun i => g i z) b 1 i - 1‖ ≤ ‖g i z - 1‖ := by
    intro i
    by_cases h : i = b
    · subst h
      rw [Function.update_self]
      simp [sub_self, norm_nonneg]
    · rw [Function.update_of_ne h]
  have hsum : Summable (fun i => ‖Function.update (fun i => g i z) b 1 i - 1‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hle hs
  have hmult : Multipliable (Function.update (fun i => g i z) b 1) := by
    have h := multipliable_one_add_of_summable
      (f := fun i => Function.update (fun i => g i z) b 1 i - 1) hsum
    simpa [add_sub_cancel] using h
  have hsplit := hmult.tprod_eq_mul_tprod_ite' b
  simpa [Function.update_apply] using hsplit

/-- N8a: the local bound survives replacing one factor by 1. -/
private theorem wf_localBound_ite (ι : Type*) [DecidableEq ι] (g : ι → ℂ → ℂ) (b : ι)
    (hlb : ∀ R : ℝ, ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in Filter.cofinite, ∀ z : ℂ, ‖z‖ ≤ R → ‖g i z - 1‖ ≤ u i) :
    ∀ R : ℝ, ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in Filter.cofinite, ∀ z : ℂ, ‖z‖ ≤ R →
        ‖(if i = b then (1 : ℂ) else g i z) - 1‖ ≤ u i := by
  intro R
  obtain ⟨u, hu, hev⟩ := hlb R
  refine ⟨u, hu, ?_⟩
  rw [Filter.eventually_cofinite] at hev ⊢
  apply Set.Finite.subset (hev.insert b)
  intro i hi
  rw [Set.mem_insert_iff]
  by_cases hb : i = b
  · exact Or.inl hb
  · apply Or.inr
    intro hP
    exact hi (fun z hz => by simp only [hb, ite_false]; exact hP z hz)

/-- N8b: replacing one factor by 1 preserves differentiability. -/
private theorem wf_differentiable_ite (ι : Type*) [DecidableEq ι] (g : ι → ℂ → ℂ) (b : ι)
    (hg : ∀ i, Differentiable ℂ (g i)) (i : ι) :
    Differentiable ℂ (fun z => if i = b then (1 : ℂ) else g i z) := by
  by_cases h : i = b
  · subst h
    simp
  · have hfun : (fun z => if i = b then (1 : ℂ) else g i z) = g i := by
      funext z
      simp [h]
    rw [hfun]
    exact hg i

/-- N9i: the product vanishes exactly on the range of `a`. -/
private theorem wf_tprod_eq_zero_iff (ι : Type*) (g : ι → ℂ → ℂ) (a : ι → ℂ)
    (hlb : ∀ R : ℝ, ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in Filter.cofinite, ∀ z : ℂ, ‖z‖ ≤ R → ‖g i z - 1‖ ≤ u i)
    (hzero : ∀ i z, g i z = 0 ↔ z = a i)
    (z : ℂ) : (∏' i, g i z) = 0 ↔ ∃ i, a i = z := by
  classical
  constructor
  · intro hz
    by_contra hne
    rw [not_exists] at hne
    have hne' : ∀ i, g i z ≠ 0 := by
      intro i hi
      exact hne i ((hzero i z).mp hi).symm
    exact wf_tprod_ne_zero ι g hlb z hne' hz
  · rintro ⟨i, rfl⟩
    have hsplit := wf_tprod_split ι g hlb (a i) i
    rw [hsplit, (hzero i (a i)).mpr rfl, zero_mul]

/-- N9ii: the product has nonzero derivative at each `a i`. -/
private theorem wf_tprod_deriv_ne_zero (ι : Type*) (g : ι → ℂ → ℂ) (a : ι → ℂ)
    (ha : Function.Injective a)
    (hg : ∀ i, Differentiable ℂ (g i))
    (hlb : ∀ R : ℝ, ∃ u : ι → ℝ, Summable u ∧
      ∀ᶠ i in Filter.cofinite, ∀ z : ℂ, ‖z‖ ≤ R → ‖g i z - 1‖ ≤ u i)
    (hzero : ∀ i z, g i z = 0 ↔ z = a i)
    (hderiv : ∀ i, deriv (g i) (a i) ≠ 0)
    (i : ι) : deriv (fun z => ∏' j, g j z) (a i) ≠ 0 := by
  classical
  have hlb' := wf_localBound_ite ι g i hlb
  have hg' : ∀ j, Differentiable ℂ (fun z => if j = i then (1 : ℂ) else g j z) :=
    fun j => wf_differentiable_ite ι g i hg j
  have hG : Differentiable ℂ (fun z => ∏' j, (if j = i then (1 : ℂ) else g j z)) :=
    wf_differentiable_tprod_of_localBound ι _ hg' hlb'
  have hGne : (∏' j, (if j = i then (1 : ℂ) else g j (a i))) ≠ 0 := by
    apply wf_tprod_ne_zero ι _ hlb'
    intro j
    by_cases hj : j = i
    · subst hj
      simp
    · simp only [hj, ite_false]
      intro h0
      exact hj (ha ((hzero j (a i)).mp h0)).symm
  have hFG : (fun z => ∏' j, g j z) =
      (fun z => g i z * ∏' j, (if j = i then (1 : ℂ) else g j z)) :=
    funext fun z => wf_tprod_split ι g hlb z i
  rw [hFG, deriv_fun_mul (hg i).differentiableAt hG.differentiableAt,
    (hzero i (a i)).mpr rfl, zero_mul, add_zero]
  exact mul_ne_zero (hderiv i) hGne

/-- N10: the specific family satisfies the local bound. -/
private theorem wf_family_localBound (S : Set ℂ)
    (hfin : ∀ R : ℝ, (S ∩ Metric.closedBall 0 R).Finite)
    (c : ℂ) (e : ↥S → ℕ) (he : Function.Injective e) :
    ∀ R : ℝ, ∃ u : ↥S → ℝ, Summable u ∧
      ∀ᶠ i in Filter.cofinite, ∀ z : ℂ, ‖z‖ ≤ R →
        ‖wfElemFactor (e i) ((z - c) / ((i : ℂ) - c)) - 1‖ ≤ u i := by
  have hsum : Summable (fun i : ↥S => 4 * (1 / 2 : ℝ) ^ (e i)) := by
    have hcomp : Summable ((fun n : ℕ => (1 / 2 : ℝ) ^ n) ∘ e) :=
      summable_geometric_two.comp_injective he
    have hmul := hcomp.mul_left (4 : ℝ)
    simpa [Function.comp] using hmul
  intro R
  refine ⟨fun i : ↥S => 4 * (1 / 2 : ℝ) ^ (e i), hsum, ?_⟩
  set M : ℝ := 2 * (|R| + ‖c‖) + ‖c‖ with hM
  have hfinex : {i : ↥S | ‖((i : ℂ))‖ ≤ M}.Finite := by
    apply Set.Finite.subset ((hfin M).preimage (Subtype.val_injective.injOn))
    intro i hi
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hi ⊢
    exact ⟨i.2, mem_closedBall_zero_iff.mpr hi⟩
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset hfinex
  intro i hi
  simp only [Set.mem_ofPred_eq] at hi ⊢
  by_contra hnge
  have hgt : M < ‖((i : ℂ))‖ := lt_of_not_ge hnge
  have habs : (0 : ℝ) ≤ |R| := abs_nonneg _
  have hcn : (0 : ℝ) ≤ ‖c‖ := norm_nonneg _
  apply hi
  intro z hz
  have hden_pos : (0 : ℝ) < ‖((i : ℂ)) - c‖ := by
    have h1 : ‖((i : ℂ))‖ - ‖c‖ ≤ ‖((i : ℂ)) - c‖ := norm_sub_norm_le _ _
    have h2 : (0 : ℝ) < ‖((i : ℂ))‖ - ‖c‖ := by linarith
    linarith
  have hR : ‖z‖ ≤ |R| := le_trans hz (le_abs_self R)
  have hnum : ‖z - c‖ ≤ |R| + ‖c‖ := by
    calc ‖z - c‖ ≤ ‖z‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ |R| + ‖c‖ := by linarith
  have hden_ge : 2 * (|R| + ‖c‖) ≤ ‖((i : ℂ)) - c‖ := by
    have h1 : ‖((i : ℂ))‖ - ‖c‖ ≤ ‖((i : ℂ)) - c‖ := norm_sub_norm_le _ _
    linarith
  have harg : ‖(z - c) / ((i : ℂ) - c)‖ ≤ 1 / 2 := by
    rw [Complex.norm_div]
    by_cases hpos : |R| + ‖c‖ = 0
    · have hzc : ‖z - c‖ = 0 := by linarith [norm_nonneg (z - c)]
      rw [hzc]
      simp
    · rw [div_le_iff₀ hden_pos]
      have : ‖z - c‖ ≤ (1 / 2) * ‖((i : ℂ)) - c‖ := by
        calc ‖z - c‖ ≤ |R| + ‖c‖ := hnum
          _ ≤ (1 / 2) * (2 * (|R| + ‖c‖)) := le_of_eq (by ring)
          _ ≤ (1 / 2) * ‖((i : ℂ)) - c‖ := by
            apply mul_le_mul_of_nonneg_left hden_ge (by norm_num)
      linarith
  have hN5 := norm_wfElemFactor_sub_one_le (e i) ((z - c) / ((i : ℂ) - c)) harg
  have hpow1 : ‖(z - c) / ((i : ℂ) - c)‖ ^ (e i + 1) ≤ (1 / 2 : ℝ) ^ (e i + 1) := by
    apply pow_le_pow_left₀ (norm_nonneg _) harg
  have hpow2 : (1 / 2 : ℝ) ^ (e i + 1) ≤ (1 / 2 : ℝ) ^ (e i) := by
    have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (e i) := pow_nonneg (by norm_num) _
    calc (1 / 2 : ℝ) ^ (e i + 1) = (1 / 2 : ℝ) ^ (e i) * (1 / 2) := by ring
      _ ≤ (1 / 2 : ℝ) ^ (e i) * 1 := by
        apply mul_le_mul_of_nonneg_left (by norm_num) hnn
      _ = (1 / 2 : ℝ) ^ (e i) := by ring
  calc ‖wfElemFactor (e i) ((z - c) / ((i : ℂ) - c)) - 1‖
      ≤ 4 * ‖(z - c) / ((i : ℂ) - c)‖ ^ (e i + 1) := hN5
    _ ≤ 4 * (1 / 2 : ℝ) ^ (e i + 1) := by
        apply mul_le_mul_of_nonneg_left hpow1 (by norm_num)
    _ ≤ 4 * (1 / 2 : ℝ) ^ (e i) := by
        apply mul_le_mul_of_nonneg_left hpow2 (by norm_num)

/-- N11a: each factor is entire. -/
private theorem wf_family_differentiable (S : Set ℂ) (c : ℂ) (e : ↥S → ℕ) (i : ↥S) :
    Differentiable ℂ (fun z => wfElemFactor (e i) ((z - c) / ((i : ℂ) - c))) :=
  (wfElemFactor_differentiable (e i)).comp
    ((differentiable_id.sub_const c).div_const ((i : ℂ) - c))

/-- N11b: each factor vanishes exactly at its index point. -/
private theorem wf_family_zero_iff (S : Set ℂ) (c : ℂ) (hc : c ∉ S) (e : ↥S → ℕ) (i : ↥S) (z : ℂ) :
    wfElemFactor (e i) ((z - c) / ((i : ℂ) - c)) = 0 ↔ z = (i : ℂ) := by
  have hne : ((i : ℂ) - c) ≠ 0 := by
    intro h
    apply hc
    have heq : (i : ℂ) = c := sub_eq_zero.mp h
    exact heq ▸ i.2
  rw [wfElemFactor_eq_zero_iff]
  constructor
  · intro h
    have h2 : z - c = (i : ℂ) - c := (div_eq_one_iff_eq hne).mp h
    exact sub_left_inj.mp h2
  · intro h
    rw [h, div_self hne]

/-- N11c: each factor has nonzero derivative at its index point. -/
private theorem wf_family_deriv_ne_zero (S : Set ℂ) (c : ℂ) (hc : c ∉ S) (e : ↥S → ℕ) (i : ↥S) :
    deriv (fun z => wfElemFactor (e i) ((z - c) / ((i : ℂ) - c))) (i : ℂ) ≠ 0 := by
  have hne : ((i : ℂ) - c) ≠ 0 := by
    intro h
    apply hc
    have heq : (i : ℂ) = c := sub_eq_zero.mp h
    exact heq ▸ i.2
  have hinner : HasDerivAt (fun z : ℂ => (z - c) / ((i : ℂ) - c))
      (1 / ((i : ℂ) - c)) (i : ℂ) := by
    have h := ((hasDerivAt_id (i : ℂ)).sub_const c).div_const ((i : ℂ) - c)
    simpa using h
  have hself : ((i : ℂ) - c) / ((i : ℂ) - c) = 1 := div_self hne
  have houter : HasDerivAt (wfElemFactor (e i))
      (-Complex.exp (-Complex.logTaylor (e i + 1) (-1)))
      (((i : ℂ) - c) / ((i : ℂ) - c)) := by
    rw [hself]
    exact wfElemFactor_hasDerivAt_one (e i)
  have hchain := HasDerivAt.comp ((i : ℂ)) houter hinner
  have hderiv : deriv (fun z => wfElemFactor (e i) ((z - c) / ((i : ℂ) - c))) (i : ℂ) =
      deriv (wfElemFactor (e i) ∘ (fun z : ℂ => (z - c) / ((i : ℂ) - c))) (i : ℂ) := rfl
  rw [hderiv, hchain.deriv]
  apply mul_ne_zero _ (div_ne_zero one_ne_zero hne)
  apply neg_ne_zero.mpr
  exact Complex.exp_ne_zero _

/--
**Weierstrass theorem on prescribed simple zeros.** Let $S \subseteq \mathbb{C}$ be a closed set
all of whose points are isolated: for each $z \in S$ there is $\varepsilon > 0$ such that no point
$w \ne z$ of $S$ satisfies $|w - z| < \varepsilon$. Then there is an entire function $f$ whose zeros
are exactly the points of $S$, all of them simple: $f'(z) \ne 0$ for every $z \in S$.

Source:
Weierstrass factorization theorem 1876; see Rudin; Lean is simple-zero corollary with closed
discrete prescribed zero set S and entire f with exact zeros S and nonvanishing derivative on S.

Proves `Wanted` entry `weierstrass_factorization`.
-/
theorem weierstrass_factorization
    (S : Set ℂ) (hS_closed : IsClosed S)
    (hS_discrete : ∀ z ∈ S, ∃ ε > 0, (Metric.ball z ε \ {z}) ∩ S = ∅) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      (∀ z : ℂ, f z = 0 ↔ z ∈ S) ∧
      (∀ z ∈ S, deriv f z ≠ 0) := by
  have hfin : ∀ R : ℝ, (S ∩ Metric.closedBall 0 R).Finite :=
    fun R => wf_isClosed_inter_closedBall_finite S hS_closed hS_discrete R
  obtain ⟨e, he⟩ := wf_exists_injective_nat S hfin
  obtain ⟨c, hc⟩ := wf_exists_not_mem S hS_discrete
  have : DecidableEq ↥S := Classical.decEq ↥S
  have hlb := wf_family_localBound S hfin c e he
  have hg : ∀ i : ↥S, Differentiable ℂ
      (fun z => wfElemFactor (e i) ((z - c) / ((i : ℂ) - c))) :=
    fun i => wf_family_differentiable S c e i
  have hzero : ∀ i : ↥S, ∀ z : ℂ,
      wfElemFactor (e i) ((z - c) / ((i : ℂ) - c)) = 0 ↔ z = (i : ℂ) :=
    fun i z => wf_family_zero_iff S c hc e i z
  have hderiv : ∀ i : ↥S,
      deriv (fun z => wfElemFactor (e i) ((z - c) / ((i : ℂ) - c))) (i : ℂ) ≠ 0 :=
    fun i => wf_family_deriv_ne_zero S c hc e i
  refine ⟨fun z => ∏' i : ↥S, wfElemFactor (e i) ((z - c) / ((i : ℂ) - c)), ?_, ?_, ?_⟩
  · exact wf_differentiable_tprod_of_localBound ↥S _ hg hlb
  · intro z
    have h := wf_tprod_eq_zero_iff ↥S _ (fun i : ↥S => (i : ℂ))
      hlb (fun i z => hzero i z) z
    constructor
    · intro hfz
      obtain ⟨i, hi⟩ := (h.mp hfz)
      exact hi ▸ i.2
    · intro hzS
      apply h.mpr
      exact ⟨⟨z, hzS⟩, rfl⟩
  · intro z hzS
    exact wf_tprod_deriv_ne_zero ↥S _ _ Subtype.val_injective
      hg hlb (fun i z => hzero i z) (fun i => hderiv i) ⟨z, hzS⟩

end MathlibExt.Analysis.Complex.WeierstrassFactorizationWanted
end
