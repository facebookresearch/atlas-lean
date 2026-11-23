/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Privacy.DifferentialPrivacyComposition
import Cslib.Probability.PMF

/-!
# Pure-DP composition clients and countermodels

These are analytic PMF proofs, not certified sampler executions. Concrete
joint masses and events distinguish conditional privacy from private marginals.
-/

open CSLibExt.Privacy.DifferentialPrivacy
open Cslib.Probability.PMF
open scoped NNReal ENNReal

namespace CSLibExtTest.Privacy.DifferentialPrivacyComposition

-- A fresh two-to-one map of a canonical uniform three-point distribution.
private noncomputable def thirds (d : Bool) : PMF Bool :=
  (uniformOfFintype (Fin 3)).map (fun i => if i = 0 then !d else d)

private theorem thirds_apply (d o : Bool) :
    thirds d o = ((if o = d then 2 / 3 else 1 / 3 : ℝ≥0) : ℝ≥0∞) := by
  cases d <;> cases o <;>
    norm_num [thirds, PMF.map_apply, tsum_fintype, Fin.sum_univ_succ,
      uniformOfFintype_apply, div_eq_mul_inv]

private theorem thirds_private :
    IsDP thirds (fun _ _ => True) (Real.log 2) := by
  refine ⟨Real.log_nonneg (by norm_num), fun d d' _ o => ?_⟩
  rw [thirds_apply, thirds_apply, Real.exp_log (by norm_num)]
  norm_num only [ENNReal.ofReal_ofNat]
  change ((if o = d then 2 / 3 else 1 / 3 : ℝ≥0) : ℝ≥0∞) ≤
    (((2 : ℝ≥0) * (if o = d' then 2 / 3 else 1 / 3) : ℝ≥0) : ℝ≥0∞)
  exact ENNReal.coe_le_coe.mpr (by
    cases d <;> cases d' <;> cases o <;>
      norm_num [← NNReal.coe_le_coe])

-- Both stages vary with the database; stage two also varies with the release.
private noncomputable def adaptive (a d : Bool) : PMF Bool :=
  thirds (Bool.xor a d)

private theorem adaptive_private (a : Bool) :
    IsDP (adaptive a) (fun _ _ => True) (Real.log 2) := by
  exact ⟨thirds_private.1, fun d d' _ o =>
    thirds_private.2 (Bool.xor a d) (Bool.xor a d') trivial o⟩

private noncomputable def transcript (d : Bool) : PMF (Bool × Bool) :=
  (thirds d).bind fun a => (adaptive a d).bind fun b => PMF.pure (a, b)

private theorem transcript_private :
    IsDP transcript (fun _ _ => True) (Real.log 2 + Real.log 2) :=
  isDP_comp_bind_pair thirds_private thirds_private.1 adaptive_private

private theorem transcript_event_private :
    IsDPEvent transcript (fun _ _ => True) (Real.log 2 + Real.log 2) :=
  isDP_iff_isDPEvent.mp transcript_private

private theorem transcript_normalized (d : Bool) :
    ∑' ab, transcript d ab = 1 := (transcript d).tsum_coe

private theorem transcript_mass (d a b : Bool) :
    transcript d (a, b) = thirds d a * thirds (Bool.xor a d) b :=
  bind_pair_apply _ _ _ _

private theorem channels_nonconstant : thirds false ≠ thirds true ∧
    adaptive false false ≠ adaptive true false := by
  constructor <;> intro h <;>
    have bad := congrArg (fun p : PMF Bool => p false) h <;>
    simp only [adaptive, thirds_apply, Bool.false_xor, Bool.true_xor,
      Bool.not_false, ite_true, Bool.false_eq_true, ite_false] at bad <;>
    have hn := ENNReal.coe_inj.mp bad <;>
    norm_num [← NNReal.coe_inj] at hn

-- The joint ratio is four, not two.
private theorem transcript_false_mass :
    transcript false (false, false) = ((4 / 9 : ℝ≥0) : ℝ≥0∞) := by
  simp only [transcript_mass, thirds_apply, Bool.false_xor, ite_true,
    ← ENNReal.coe_mul, ENNReal.coe_inj]
  norm_num

private theorem transcript_true_mass :
    transcript true (false, false) = ((1 / 9 : ℝ≥0) : ℝ≥0∞) := by
  simp only [transcript_mass, thirds_apply, Bool.false_xor,
    Bool.false_eq_true, ite_false, ← ENNReal.coe_mul, ENNReal.coe_inj]
  norm_num

private theorem max_budget_fails : ¬IsDP transcript (fun _ _ => True)
    (max (Real.log 2) (Real.log 2)) := by
  intro h
  have bad := h.2 false true trivial (false, false)
  rw [transcript_false_mass, transcript_true_mass, max_self,
    Real.exp_log (by norm_num)] at bad
  have hn : (4 / 9 : ℝ≥0) ≤ 2 * (1 / 9) := by exact_mod_cast bad
  norm_num [← NNReal.coe_le_coe] at hn

-- Non-adaptive composition retains both independent releases.
private theorem nonadaptive_event_private :
    IsDPEvent (fun d => (thirds d).bind fun a =>
      (thirds d).bind fun b => PMF.pure (a, b)) (fun _ _ => True)
      (Real.log 2 + Real.log 2) :=
  isDP_iff_isDPEvent.mp (isDP_comp_bind_pair thirds_private
    thirds_private.1 (fun _ => thirds_private))

private theorem nonadaptive_mass :
    ((thirds false).bind fun a => (thirds false).bind
      fun b => PMF.pure (a, b)) (false, false) =
      ((4 / 9 : ℝ≥0) : ℝ≥0∞) := by
  rw [bind_pair_apply]
  simpa only [transcript_mass, Bool.false_xor] using transcript_false_mass

private theorem singleton_event_mass :
    (transcript false).toOuterMeasure {(false, false)} =
      ((4 / 9 : ℝ≥0) : ℝ≥0∞) := by
  simpa only [PMF.toOuterMeasure_apply_singleton] using transcript_false_mass

private theorem first_release_event_bound :
    (transcript false).toOuterMeasure {ab | ab.1 = false} ≤
      ENNReal.ofReal (Real.exp (Real.log 2 + Real.log 2)) *
        (transcript true).toOuterMeasure {ab | ab.1 = false} :=
  (isDP_iff_isDPEvent.mp transcript_private).2 false true trivial _

-- A genuinely randomized kernel depends on the release, not the database.
private theorem randomized_postprocessing_event_private :
    IsDPEvent (fun d => (thirds d).bind thirds)
      (fun _ _ => True) (Real.log 2) :=
  isDP_iff_isDPEvent.mp (isDP_bind thirds_private thirds)

private theorem randomized_postprocessing_normalized (d : Bool) :
    ∑' b, (thirds d).bind thirds b = 1 :=
  ((thirds d).bind thirds).tsum_coe

private theorem randomized_postprocessing_mass :
    (thirds false).bind thirds false = ((5 / 9 : ℝ≥0) : ℝ≥0∞) := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [Fintype.sum_bool, thirds_apply, ite_true, Bool.false_eq_true,
    Bool.true_eq_false, ite_false, ← ENNReal.coe_mul, ← ENNReal.coe_add,
    ENNReal.coe_inj]
  norm_num

-- Deterministic kernels and many-to-one output loss use the same bind API.
private theorem deterministic_kernel_private :
    IsDP (fun d => (thirds d).bind (fun a => PMF.pure (!a)))
      (fun _ _ => True) (Real.log 2) := isDP_bind thirds_private _

private theorem many_to_one_mass :
    (thirds false).bind (fun _ => PMF.pure ()) () = 1 := by
  simp only [PMF.bind_const, PMF.pure_apply_self]

private theorem zero_budget_composition :
    IsDP (fun _ : Bool => (PMF.pure false).bind fun a =>
      (PMF.pure a).bind fun b => PMF.pure (a, b)) (fun _ _ => True) 0 := by
  simpa only [add_zero] using isDP_comp_bind_pair
    (isDP_const (PMF.pure false) (fun _ _ : Bool => True)) (le_refl 0)
    (fun a => isDP_const (PMF.pure a) _)

private theorem zero_joint_mass :
    ((PMF.pure false).bind fun a =>
      (PMF.pure a).bind fun b => PMF.pure (a, b)) (false, true) = 0 := by
  simp [PMF.pure_bind, PMF.pure_apply]

private theorem zero_budget_randomized_postprocessing :
    IsDP (fun _ : Bool => (thirds false).bind thirds)
      (fun _ _ => True) 0 := isDP_bind (isDP_const _ _) thirds

-- A one-way, nonreflexive relation also works; symmetry is not assumed.
private theorem ordered_relation_private :
    IsDP (fun d => (thirds d).bind thirds)
      (fun d d' => d = false ∧ d' = true) (Real.log 2) :=
  isDP_bind ⟨thirds_private.1, fun d d' _ o =>
    thirds_private.2 d d' trivial o⟩ thirds

-- Empty types require no chosen element and no Nonempty assumption.
private theorem empty_composition (ε₂ : ℝ) (hε₂ : 0 ≤ ε₂) :
    IsDP (fun d : Empty => (d.elim : PMF Empty).bind fun a =>
      (a.elim : PMF Bool).bind fun b => PMF.pure (a, b))
      (fun _ _ => True) (0 + ε₂) :=
  isDP_comp_bind_pair ⟨le_refl 0, fun d => d.elim⟩ hε₂ (fun a => a.elim)

-- Per-output privacy alone does not force a nonnegative second budget.
private theorem empty_requires_global_nonneg :
    let M : Empty → PMF Empty := Empty.elim
    let K : Empty → Empty → PMF Bool := fun a => a.elim
    IsDP M (fun _ _ => True) 0 ∧
      (∀ a, IsDP (K a) (fun _ _ => True) (-1)) ∧
      ¬IsDP (fun d => (M d).bind fun a =>
        (K a d).bind fun b => PMF.pure (a, b))
        (fun _ _ => True) (0 + (-1)) := by
  refine ⟨⟨le_refl 0, fun d => d.elim⟩, (fun a => a.elim), fun h => ?_⟩
  have hn := h.1
  norm_num at hn

private noncomputable def xorTranscript (d : Bool) : PMF (Bool × Bool) :=
  (uniformOfFintype Bool).bind fun a =>
    (PMF.pure (Bool.xor d a)).bind fun b => PMF.pure (a, b)

private theorem xor_fst (d : Bool) :
    (xorTranscript d).map Prod.fst = uniformOfFintype Bool := by
  simp only [xorTranscript, PMF.pure_bind, PMF.map_bind, PMF.pure_map,
    PMF.bind_pure]

private theorem xor_snd (d : Bool) :
    (xorTranscript d).map Prod.snd = uniformOfFintype Bool := by
  ext b
  cases d <;> cases b <;>
    norm_num [xorTranscript, PMF.pure_bind, PMF.map_bind, PMF.pure_map,
      PMF.bind_apply, tsum_fintype, uniformOfFintype_apply, PMF.pure_apply]

private theorem xor_marginals_private :
    IsDP (postProcess Prod.fst xorTranscript) (fun _ _ => True) 0 ∧
      IsDP (postProcess Prod.snd xorTranscript) (fun _ _ => True) 0 := by
  unfold postProcess
  constructor <;> simpa only [xor_fst, xor_snd] using
    isDP_const (uniformOfFintype Bool) (fun _ _ : Bool => True)

-- Despite the two zero-private marginals, the joint reveals the database.
private theorem xor_joint_not_private (ε : ℝ) :
    ¬IsDP xorTranscript (fun _ _ => True) ε := by
  intro h
  have bad := h.2 false true trivial (false, false)
  norm_num [xorTranscript, bind_pair_apply, uniformOfFintype_apply,
    PMF.pure_apply] at bad

private theorem xor_joint_masses :
    xorTranscript false (false, false) = 1 / 2 ∧
      xorTranscript true (false, false) = 0 := by
  norm_num [xorTranscript, bind_pair_apply, uniformOfFintype_apply,
    PMF.pure_apply]

-- The conditional second stage fails privacy, precisely the missing premise.
private theorem xor_conditional_not_private (ε : ℝ) :
    ¬IsDP (fun d => PMF.pure (Bool.xor d false)) (fun _ _ => True) ε := by
  intro h
  have bad := h.2 false true trivial false
  norm_num [PMF.pure_apply] at bad

-- Allowing a postprocessor to see the database destroys the guarantee.
private theorem database_postprocessor_not_private (ε : ℝ) :
    ¬IsDP (fun d : Bool =>
      (uniformOfFintype Bool).bind (fun _ => PMF.pure d))
      (fun _ _ => True) ε := by
  intro h
  have bad := h.2 false true trivial false
  norm_num [PMF.bind_const, PMF.pure_apply] at bad

private theorem database_postprocessor_input_private :
    IsDP (fun _ : Bool => uniformOfFintype Bool)
      (fun _ _ => True) 0 := isDP_const _ _

-- Event-level inputs are sufficient via the existing equivalence.
private theorem event_input_composition {D A B : Type*}
    {M : D → PMF A} {K : A → D → PMF B}
    {adj : D → D → Prop} {ε₁ ε₂ : ℝ}
    (hM : IsDPEvent M adj ε₁) (hε₂ : 0 ≤ ε₂)
    (hK : ∀ a, IsDPEvent (K a) adj ε₂) :
    IsDPEvent (fun d => (M d).bind fun a =>
      (K a d).bind fun b => PMF.pure (a, b)) adj (ε₁ + ε₂) :=
  isDP_iff_isDPEvent.mp (isDP_comp_bind_pair
    (isDP_iff_isDPEvent.mpr hM) hε₂
    (fun a => isDP_iff_isDPEvent.mpr (hK a)))

end CSLibExtTest.Privacy.DifferentialPrivacyComposition
