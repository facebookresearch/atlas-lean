/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DirichletForm.Basic

import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Beurling–Deny resolvent criterion

Minimizing the energy with a quadratic penalty gives the following criterion.

* `unitContractionOperates_iff_resolvent`: the Beurling–Deny correspondence between Markovian
  closed forms
  and Markovian resolvents (Fukushima, Oshima and Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, 2nd revised and extended ed., de Gruyter, 2011, Theorem 1.4.1, (b) ⇔ (d)).

Fukushima's theorem (a regular Dirichlet form is the Dirichlet form of an `m`-symmetric Hunt
process, FOT Theorem 7.2.1) and the Albeverio–Ma–Röckner characterisation of quasi-regular forms
by right processes are not stated: Mathlib has no Hunt or right processes, and a statement about
an undefined process predicate would not be a faithful proposition.
-/

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
open MathlibExt.Probability.DirichletForm

namespace MathlibExt.Probability.DirichletFormWanted

section

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

private def InUnitInterval (u : Lp ℝ 2 m) : Prop := ∀ᵐ x ∂m, 0 ≤ u x ∧ u x ≤ 1

private theorem clamp_mem (x : Lp ℝ 2 m) : InUnitInterval (unitContractionLp x) := by
  filter_upwards [unitContractionLp_ae_eq x] with t ht
  rw [ht]
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

-- The variational inequality for the metric projection onto the unit interval in L².
private theorem inner_clamp_nonpos (x z : Lp ℝ 2 m) (hz : InUnitInterval z) :
    ⟪x - unitContractionLp x, z - unitContractionLp x⟫ ≤ 0 := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_nonpos_of_ae
  filter_upwards [hz, unitContractionLp_ae_eq x, Lp.coeFn_sub x (unitContractionLp x),
    Lp.coeFn_sub z (unitContractionLp x)] with t hzt ht hx hz'
  simp only [hx, hz', Pi.sub_apply, ht, Real.inner_apply]
  rcases le_total (x t) 0 with h | h
  · simp [min_eq_left (h.trans zero_le_one), max_eq_left h,
      mul_nonpos_of_nonpos_of_nonneg h hzt.1]
  · rcases le_total (x t) 1 with h' | h'
    · simp [min_eq_left h', max_eq_right h]
    · simp [min_eq_right h',
        mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h') (sub_nonpos.mpr hzt.2)]

-- The graph norm depends on the resolvent parameter, so give it a separate carrier.
private def EnergyDomain (E : SymmetricForm m) (_a : Set.Ici (1 : ℝ)) : Type _ := E.domain

private instance energyAddCommGroup (E : SymmetricForm m) (a : Set.Ici (1 : ℝ)) :
    AddCommGroup (EnergyDomain E a) := inferInstanceAs (AddCommGroup E.domain)

private instance energyModule (E : SymmetricForm m) (a : Set.Ici (1 : ℝ)) :
    Module ℝ (EnergyDomain E a) := inferInstanceAs (Module ℝ E.domain)

private def inclusion (E : SymmetricForm m) (a : Set.Ici (1 : ℝ)) :
    EnergyDomain E a →ₗ[ℝ] Lp ℝ 2 m := E.domain.subtype

private theorem inclusion_mem {E : SymmetricForm m} {a : Set.Ici (1 : ℝ)}
    (u : EnergyDomain E a) : inclusion E a u ∈ E.domain := (show E.domain from u).property

private noncomputable instance energyCore (E : SymmetricForm m) (a : Set.Ici (1 : ℝ)) :
    InnerProductSpace.Core ℝ (EnergyDomain E a) where
  inner u v := E.form (inclusion E a u) (inclusion E a v) +
    a * ⟪inclusion E a u, inclusion E a v⟫
  conj_inner_symm u v := by
    simp only [starRingEnd_apply, star_trivial]
    rw [E.symm _ (inclusion_mem v) _ (inclusion_mem u), real_inner_comm]
  re_inner_nonneg u := by
    exact add_nonneg (E.nonneg _ (inclusion_mem u))
      (mul_nonneg (zero_le_one.trans a.property) real_inner_self_nonneg)
  add_left u v w := by simp [inner_add_left, mul_add]; ring
  smul_left u v r := by simp [real_inner_smul_left]; ring
  definite u hu := by
    change E.form _ _ + (a : ℝ) * ⟪inclusion E a u, inclusion E a u⟫ = 0 at hu
    rw [real_inner_self_eq_norm_sq] at hu
    have hz : ‖inclusion E a u‖ = 0 := by
      nlinarith [E.nonneg _ (inclusion_mem u), a.property,
        mul_nonneg (sub_nonneg.mpr a.property) (sq_nonneg ‖inclusion E a u‖)]
    exact Subtype.ext (norm_eq_zero.mp hz)

private noncomputable instance energyNormedGroup (E : SymmetricForm m) (a : Set.Ici (1 : ℝ)) :
    NormedAddCommGroup (EnergyDomain E a) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

private noncomputable instance energyInnerSpace (E : SymmetricForm m) (a : Set.Ici (1 : ℝ)) :
    InnerProductSpace ℝ (EnergyDomain E a) := InnerProductSpace.ofCore _

private theorem energy_norm_sq {E : SymmetricForm m} {a : Set.Ici (1 : ℝ)}
    (u : EnergyDomain E a) :
    ‖u‖ ^ 2 = E.form (inclusion E a u) (inclusion E a u) + a * ‖inclusion E a u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (x := u), ← real_inner_self_eq_norm_sq]
  rfl

private theorem energyOne_le_sq {E : SymmetricForm m} {a : Set.Ici (1 : ℝ)}
    (v : EnergyDomain E a) :
    E.energyOne (inclusion E a v) (inclusion E a v) ≤ ‖v‖ ^ 2 := by
  rw [energy_norm_sq, SymmetricForm.energyOne, real_inner_self_eq_norm_sq]
  nlinarith [mul_nonneg (sub_nonneg.mpr a.property) (sq_nonneg ‖inclusion E a v‖)]

private theorem inclusion_norm_le {E : SymmetricForm m} {a : Set.Ici (1 : ℝ)}
    (u : EnergyDomain E a) : ‖inclusion E a u‖ ≤ ‖u‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simpa only [sq] using (E.norm_sq_le_energyOne (inclusion_mem u)).trans (energyOne_le_sq u)

private noncomputable def continuousInclusion (E : SymmetricForm m) (a : Set.Ici (1 : ℝ)) :
    EnergyDomain E a →L[ℝ] Lp ℝ 2 m :=
  (inclusion E a).mkContinuous 1 (fun u => by simpa using inclusion_norm_le u)

private theorem sq_le_energyOne_mul {E : SymmetricForm m} {a : Set.Ici (1 : ℝ)}
    (v : EnergyDomain E a) :
    ‖v‖ ^ 2 ≤ a * E.energyOne (inclusion E a v) (inclusion E a v) := by
  rw [energy_norm_sq, SymmetricForm.energyOne, real_inner_self_eq_norm_sq]
  nlinarith [mul_nonneg (sub_nonneg.mpr a.property) (E.nonneg _ (inclusion_mem v))]

private theorem energy_complete (E : SymmetricForm m) (hE : E.IsClosed) (a : Set.Ici (1 : ℝ)) :
    CompleteSpace (EnergyDomain E a) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨w, hw, hlim⟩ := hE (fun n => inclusion E a (u n)) (fun n => inclusion_mem _) (by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
    refine ⟨N, fun n hn k hk => ?_⟩
    have hd := hN n hn k hk
    rw [dist_eq_norm] at hd
    have h := energyOne_le_sq (u n - u k)
    rw [map_sub] at h
    exact h.trans_lt (by nlinarith [Real.sq_sqrt hε.le, norm_nonneg (u n - u k)]))
  let v : EnergyDomain E a := (⟨w, hw⟩ : E.domain)
  refine ⟨v, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hsq : Tendsto (fun n => ‖u n - v‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) (fun n => sq_le_energyOne_mul (u n - v))
    have hv : inclusion E a v = w := rfl
    simpa only [map_sub, hv, mul_zero] using hlim.const_mul (a : ℝ)
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

-- Riesz representation in the complete domain gives the unscaled resolvent.
private theorem exists_resolvent (E : SymmetricForm m) (hE : E.IsClosed) (a : Set.Ici (1 : ℝ))
    (f : Lp ℝ 2 m) : ∃ u ∈ E.domain, ∀ v ∈ E.domain, E.form u v + a * ⟪u, v⟫ = ⟪f, v⟫ := by
  let := energy_complete E hE a
  let L := (innerSL ℝ f).comp (continuousInclusion E a)
  let u := (InnerProductSpace.toDual ℝ (EnergyDomain E a)).symm L
  refine ⟨inclusion E a u, inclusion_mem _, fun v hv => ?_⟩
  let w : EnergyDomain E a := (⟨v, hv⟩ : E.domain)
  exact InnerProductSpace.toDual_symm_apply (x := w) (y := L)

private theorem clamp_dist_sq (x z : Lp ℝ 2 m) (hz : InUnitInterval z) :
    ‖x - unitContractionLp x‖ ^ 2 + ‖z - unitContractionLp x‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by
  have h := norm_sub_sq_real (x - unitContractionLp x) (z - unitContractionLp x)
  rw [sub_sub_sub_cancel_right] at h
  linarith [inner_clamp_nonpos x z hz]

-- For a > 0, the resolvent equation makes a • u minimize E(v,v) + a * ‖v - f‖².
-- The excess over the minimum is exactly the squared graph norm of v - a • u.
private theorem resolvent_minimum (E : SymmetricForm m) (a : ℝ) (f u : Lp ℝ 2 m)
    (hu : u ∈ E.domain) (heq : ∀ v ∈ E.domain, E.form u v + a * ⟪u, v⟫ = ⟪f, v⟫)
    (v : Lp ℝ 2 m) (hv : v ∈ E.domain) :
    let z := a • u
    E.form v v + a * ‖v - f‖ ^ 2 = E.form z z + a * ‖z - f‖ ^ 2 +
      (E.form (v - z) (v - z) + a * ‖v - z‖ ^ 2) := by
  intro z
  have hz : z ∈ E.domain := E.domain.smul_mem a hu
  have h := heq (v - z) (E.domain.sub_mem hv hz)
  have hs : E.form z (v - z) + a * ⟪z, v - z⟫ = a * ⟪f, v - z⟫ := by
    change E.form (a • u) (v - z) + a * ⟪a • u, v - z⟫ = _
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, real_inner_smul_left]
    linarith only [congrArg (a * ·) h]
  simp only [map_sub, inner_sub_right, real_inner_self_eq_norm_sq] at hs
  simp only [norm_sub_sq_real, map_sub, LinearMap.sub_apply, E.symm v hv z hz]
  rw [real_inner_comm f v, real_inner_comm f z, real_inner_comm z v]
  linarith only [hs]

private theorem interval_of_operates (E : SymmetricForm m) (h : E.UnitContractionOperates)
    (a : ℝ) (ha : 0 < a) (f u : Lp ℝ 2 m) (hu : u ∈ E.domain)
    (heq : ∀ v ∈ E.domain, E.form u v + a * ⟪u, v⟫ = ⟪f, v⟫) (hf : InUnitInterval f) :
    InUnitInterval (a • u) := by
  let z := a • u
  obtain ⟨hp, henergy⟩ := h z (E.domain.smul_mem a hu)
  have hmin := resolvent_minimum E a f u hu heq (unitContractionLp z) hp
  change E.form _ _ + a * ‖unitContractionLp z - f‖ ^ 2 = E.form z z +
    a * ‖z - f‖ ^ 2 + (E.form _ _ + a * ‖unitContractionLp z - z‖ ^ 2) at hmin
  have hd := clamp_dist_sq z f hf
  rw [norm_sub_rev f] at hd
  have hzero : ‖z - unitContractionLp z‖ = 0 := by
    by_contra hne
    linarith [mul_le_mul_of_nonneg_left hd ha.le,
      E.nonneg _ (E.domain.sub_mem hp (E.domain.smul_mem a hu)),
      mul_nonneg ha.le (sq_nonneg ‖unitContractionLp z - z‖),
      mul_pos ha (sq_pos_of_ne_zero hne)]
  change InUnitInterval z
  rw [sub_eq_zero.mp (norm_eq_zero.mp hzero)]
  exact clamp_mem z

private theorem interval_smul_iff (a : ℝ) (u : Lp ℝ 2 m) :
    InUnitInterval (a • u) ↔ ∀ᵐ t ∂m, 0 ≤ a * u t ∧ a * u t ≤ 1 := by
  unfold InUnitInterval
  apply eventually_congr
  filter_upwards [Lp.coeFn_smul a u] with t ht
  rw [ht]
  rfl

private theorem operates_of_interval (E : SymmetricForm m) (hE : E.IsClosed)
    (h : ∀ a : ℝ, 0 < a → ∀ f u : Lp ℝ 2 m, u ∈ E.domain →
      (∀ v ∈ E.domain, E.form u v + a * ⟪u, v⟫ = ⟪f, v⟫) →
      InUnitInterval f → InUnitInterval (a • u)) : E.UnitContractionOperates := by
  intro x hx
  let p := unitContractionLp x
  let a (n : ℕ) : ℝ := n + 1
  have ha (n : ℕ) : 1 ≤ a n := by simp [a]
  have hpos (n : ℕ) : 0 < a n := zero_lt_one.trans_le (ha n)
  choose u hu heq using fun n => exists_resolvent E hE ⟨a n, ha n⟩ p
  let z (n : ℕ) := a n • u n
  have hz (n : ℕ) : z n ∈ E.domain := E.domain.smul_mem _ (hu n)
  have hinterval (n : ℕ) : InUnitInterval (z n) := h _ (hpos n) _ _ (hu n) (heq n) (clamp_mem x)
  -- The projection inequality cancels the penalty paid by the competitor x,
  -- bounding the minimum by the energy of x.
  let J (n : ℕ) := E.form (z n) (z n) + a n * ‖z n - p‖ ^ 2
  have hgap (n : ℕ) (v : Lp ℝ 2 m) (hv : v ∈ E.domain) :
      E.form v v + a n * ‖v - p‖ ^ 2 = J n +
        (E.form (v - z n) (v - z n) + a n * ‖v - z n‖ ^ 2) :=
    resolvent_minimum E _ p _ (hu n) (heq n) v hv
  have hbound (n : ℕ) : J n ≤ E.form x x := by
    have hd := clamp_dist_sq x (z n) (hinterval n)
    change ‖x - p‖ ^ 2 + ‖z n - p‖ ^ 2 ≤ _ at hd
    linarith [hgap n x hx, mul_le_mul_of_nonneg_left hd (hpos n).le,
      E.nonneg _ (E.domain.sub_mem hx (hz n)), mul_nonneg (hpos n).le (sq_nonneg ‖z n - p‖)]
  have hLp : Tendsto z atTop (𝓝 p) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hs : Tendsto (fun n => ‖z n - p‖ ^ 2) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => sq_nonneg _) (g := fun n => E.form x x / a n)
      · intro n
        apply (le_div_iff₀ (hpos n)).mpr
        have hb := hbound n
        dsimp only [J] at hb
        linarith [E.nonneg _ (hz n)]
      · simpa [a, div_eq_mul_inv] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (E.form x x)
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using
      (Real.continuous_sqrt.tendsto 0).comp hs
  -- The same gap controls the graph distance by the increment of the minimum.
  let one : Set.Ici (1 : ℝ) := ⟨1, le_rfl⟩
  let w (n : ℕ) : EnergyDomain E one := (⟨z n, hz n⟩ : E.domain)
  have hincl (n : ℕ) : inclusion E one (w n) = z n := rfl
  have hdiff {n k : ℕ} (hnk : n ≤ k) : ‖w k - w n‖ ^ 2 ≤ J k - J n := by
    have hnk' : a n ≤ a k := by simpa [a] using hnk
    have hmono := mul_le_mul_of_nonneg_right hnk' (sq_nonneg ‖z k - p‖)
    have hg := hgap n (z k) (hz k)
    rw [energy_norm_sq, map_sub, hincl, hincl]
    change E.form _ _ + 1 * ‖z k - z n‖ ^ 2 ≤
      E.form (z k) (z k) + a k * ‖z k - p‖ ^ 2 - J n
    nlinarith [mul_nonneg (sub_nonneg.mpr (ha n)) (sq_nonneg ‖z k - z n‖)]
  have hmono : Monotone J := fun n k hnk => by linarith [hdiff hnk, sq_nonneg ‖w k - w n‖]
  have hJ := (tendsto_atTop_ciSup hmono ⟨E.form x x, Set.forall_mem_range.mpr hbound⟩).cauchySeq
  have hc : CauchySeq w := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hJ (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have hdist := hN n hn
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hmono hn))] at hdist
    rw [dist_eq_norm]
    nlinarith [hdiff hn, norm_nonneg (w n - w N)]
  let := energy_complete E hE one
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hc
  have hvLp : Tendsto z atTop (𝓝 (inclusion E one v)) :=
    ((continuousInclusion E one).continuous.tendsto v).comp hv
  have hp := tendsto_nhds_unique hvLp hLp
  change p ∈ E.domain ∧ E.form p p ≤ E.form x x
  rw [← hp]
  refine ⟨inclusion_mem _, ?_⟩
  have hlim := (hv.norm.pow 2).sub (hvLp.norm.pow 2)
  have hform (v : EnergyDomain E one) :
      ‖v‖ ^ 2 - ‖inclusion E one v‖ ^ 2 = E.form (inclusion E one v) (inclusion E one v) := by
    rw [energy_norm_sq]
    change _ + 1 * _ - _ = _
    ring
  rw [hform] at hlim
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  change ‖w n‖ ^ 2 - ‖inclusion E one (w n)‖ ^ 2 ≤ _
  rw [hform, hincl]
  have hb := hbound n
  dsimp only [J] at hb
  linarith [mul_nonneg (hpos n).le (sq_nonneg ‖z n - p‖)]

end

/-- **Beurling–Deny: the unit contraction operates on a closed form iff its resolvent is
Markovian.** Let `E` be a closed symmetric form on `L²(X; m)`, `m` σ-finite. For `α > 0` and
`f ∈ L²`, the resolvent `G_α f` is the element `u ∈ D[E]` with `E(u, v) + α (u, v) = (f, v)` for
all `v ∈ D[E]` (FOT, equation (1.3.7)). Then the unit contraction operates on `E` (condition
(E.4)′, equivalent for closed forms to FOT's Markov condition (E.4)) if and only if every
`α G_α` is Markovian: `0 ≤ f ≤ 1` a.e. implies `0 ≤ α G_α f ≤ 1` a.e. (Fukushima, Oshima and
Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd ed., 2011, Theorem 1.4.1, (b) ⇔
(d)). FOT prove (b) ⇒ (e) under their topological assumption (1.1.7) and note (footnote 10) that
it holds without it, referring to Ma–Röckner (1992) and Bouleau–Hirsch (1991); the statement
here has no topological assumption. -/
public theorem unitContractionOperates_iff_resolvent {X : Type*} [MeasurableSpace X] {m : Measure X}
    [SigmaFinite m] (E : SymmetricForm m) (hE : E.IsClosed) :
    E.UnitContractionOperates ↔ ∀ α : ℝ, 0 < α → ∀ f u : Lp ℝ 2 m, u ∈ E.domain →
      (∀ v ∈ E.domain, E.form u v + α * ⟪u, v⟫ = ⟪f, v⟫) →
      (∀ᵐ x ∂m, 0 ≤ f x ∧ f x ≤ 1) → ∀ᵐ x ∂m, 0 ≤ α * u x ∧ α * u x ≤ 1 := by
  constructor
  · intro h a ha f u hu heq hf
    exact (interval_smul_iff a u).mp (interval_of_operates E h a ha f u hu heq hf)
  · intro h
    apply operates_of_interval E hE
    intro a ha f u hu heq hf
    exact (interval_smul_iff a u).mpr (h a ha f u hu heq hf)

end MathlibExt.Probability.DirichletFormWanted
