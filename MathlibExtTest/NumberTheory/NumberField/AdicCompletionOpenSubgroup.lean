/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.AdicCompletionOpenSubgroup

@[expose] public section

open NumberField IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

-- Consumer with the original binders.
example (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (Φ : (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
    (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ)
    (hΦ0 : ∀ p, Φ p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0) :
    ∃ U : Subgroup (v.adicCompletion K)ˣ, IsOpen (U : Set (v.adicCompletion K)ˣ) ∧
      ∀ t ∈ U, ∀ b z : v.adicCompletion K, Φ (b * (t : v.adicCompletion K), z) = Φ (b, z) :=
  exists_isOpen_subgroup_forall_apply_mul_eq_of_isLocallyConstant_of_hasCompactSupport
    K v Φ hΦ hΦc hΦ0

-- The compact-support hypothesis matters: without it the zero function would
-- still satisfy the conclusion, so exhibit instead that a locally constant
-- function with noncompact support need not come from this construction; here
-- the constant `1` function is locally constant and nowhere zero.
example (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    IsLocallyConstant (fun _ : (v.adicCompletion K) × (v.adicCompletion K) => (1 : ℂ)) :=
  IsLocallyConstant.const 1
