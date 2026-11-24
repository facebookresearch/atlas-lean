/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.SturmBoundGamma0

@[expose] public section

open UpperHalfPlane
open scoped MatrixGroups

/-- exactSource consumer: the original binders apply verbatim. -/
example (N : ℕ) [NeZero N] {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (h : ∀ n : ℕ, n ≤ (k * (CongruenceSubgroup.Gamma0 N).index).toNat / 12 →
      (qExpansion 1 f).coeff n = 0) : f = 0 :=
  ModularForm.sturm_bound_Gamma0 N f h

/-- The zero form satisfies the coefficient hypothesis at every weight. -/
example (N : ℕ) [NeZero N] {k : ℤ} :
    ∀ n : ℕ, n ≤ (k * (CongruenceSubgroup.Gamma0 N).index).toNat / 12 →
      (qExpansion 1 (0 : ModularForm (CongruenceSubgroup.Gamma0 N) k)).coeff n = 0 := by
  intro n _
  simp only [FunLike.coe_zero, UpperHalfPlane.qExpansion_zero]
  exact map_zero _

/-- Boundary: the coefficient hypothesis cannot be dropped. The constant
weight-zero form `1` on `Γ₀(1)` is nonzero, and its `0`-th `q`-expansion
coefficient is `1`, so it fails the hypothesis already at `n = 0`. -/
example :
    (qExpansion 1 (ModularForm.const (1 : ℂ) :
      ModularForm (CongruenceSubgroup.Gamma0 1) 0)).coeff 0 ≠ 0 := by
  have hper : Function.Periodic
      ((ModularForm.const (1 : ℂ) :
        ModularForm (CongruenceSubgroup.Gamma0 1) 0) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex _
      (by simp [CongruenceSubgroup.strictPeriods_Gamma0])
  rw [UpperHalfPlane.qExpansion_coeff_zero one_pos
    (ModularFormClass.analyticAt_cuspFunction_zero _ one_pos
      (by simp [CongruenceSubgroup.strictPeriods_Gamma0])) hper]
  have hcoe : ∀ τ : ℍ, ((ModularForm.const (1 : ℂ) :
      ModularForm (CongruenceSubgroup.Gamma0 1) 0) : ℍ → ℂ) τ = 1 := by
    intro τ
    rfl
  have htend : Filter.Tendsto
      ((ModularForm.const (1 : ℂ) :
        ModularForm (CongruenceSubgroup.Gamma0 1) 0) : ℍ → ℂ)
      atImInfty (nhds 1) :=
    tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun τ ↦ (hcoe τ).symm)
  have hval : UpperHalfPlane.valueAtInfty
      ((ModularForm.const (1 : ℂ) :
        ModularForm (CongruenceSubgroup.Gamma0 1) 0) : ℍ → ℂ) = 1 :=
    htend.limUnder_eq
  rw [hval]
  exact one_ne_zero
