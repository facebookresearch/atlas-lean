/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.DifferentialPrivacy
import Cslib.Probability.PMF

/-!
# Two-stage pure differential privacy

The joint transcript retains both releases. The second mechanism may depend
on the first released value, but must be private for every such value with
one uniform nonnegative budget and the same ordered adjacency relation.
This is fixed-depth, two-stage composition, not adaptive budget selection,
random stopping, or an accountant. Budgets add.

Database-independent randomized postprocessing preserves the original budget.
All distributions are normalized PMFs; these are analytic guarantees, not
executable samplers. Approximate DP and additive delta are not covered.
-/

@[expose] public section

namespace CSLibExt.Privacy.DifferentialPrivacy

/-- Two-stage pure DP for the full joint transcript. The second stage can
adapt to the first output. Its budget is nonnegative even when both the
first output type and database type are empty. -/
theorem isDP_comp_bind_pair {D A B : Type*}
    {M : D → PMF A} {K : A → D → PMF B}
    {adj : D → D → Prop} {ε₁ ε₂ : ℝ}
    (hM : IsDP M adj ε₁) (hε₂ : 0 ≤ ε₂)
    (hK : ∀ a, IsDP (K a) adj ε₂) :
    IsDP (fun d => (M d).bind fun a =>
      (K a d).bind fun b => PMF.pure (a, b)) adj (ε₁ + ε₂) := by
  refine ⟨add_nonneg hM.1 hε₂, fun d d' hadj ⟨a, b⟩ => ?_⟩
  rw [Cslib.Probability.PMF.bind_pair_apply,
    Cslib.Probability.PMF.bind_pair_apply, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact (mul_le_mul' (hM.2 d d' hadj a) ((hK a).2 d d' hadj b)).trans_eq
    (mul_mul_mul_comm _ _ _ _)

/-- Randomized postprocessing preserves pure DP. The kernel may depend on
the released value, but has no access to the private database. -/
theorem isDP_bind {D A B : Type*} {M : D → PMF A}
    {adj : D → D → Prop} {ε : ℝ} (hM : IsDP M adj ε)
    (k : A → PMF B) : IsDP (fun d => (M d).bind k) adj ε := by
  have h := isDP_comp_bind_pair hM (le_refl 0)
    (fun a => isDP_const (k a) adj)
  have hp := isDP_postProcess h Prod.snd
  unfold postProcess at hp
  simpa only [PMF.map_bind, PMF.pure_map, PMF.bind_pure, add_zero] using hp

end CSLibExt.Privacy.DifferentialPrivacy
