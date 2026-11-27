/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.ContinuousMap.ZeroAtInfty.CompactSupportCutoff

/-!
# A support-bearing C0 cutoff on the empty discrete domain

The domain is `Fin 0` with the discrete topology, so the regularity and local
compactness requirements remain present. The public cutoff factory returns
one complex-valued C0 function with compact support, its one-on-empty-set
values, and both norm bounds. Empty-domain extensionality makes that same
witness zero. Its product with every C0 function has compact support and
zero approximation error in the original C0 norm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped ZeroAtInfty

namespace EmptyCutoffFactorySmoke

private instance : TopologicalSpace (Fin 0) := ⊥
private instance : DiscreteTopology (Fin 0) := ⟨rfl⟩

private theorem emptyC0_eq_zero (f : C₀(Fin 0, ℂ)) : f = 0 := by
  ext x
  exact Fin.elim0 x

example :
    ∃ φ : C₀(Fin 0, ℂ),
      HasCompactSupport φ ∧ EqOn φ (1 : Fin 0 → ℂ) (∅ : Set (Fin 0)) ∧
      ‖φ‖ ≤ 1 ∧ (∀ x : Fin 0, ‖φ x‖ ≤ 1) ∧ φ = 0 ∧ ‖φ‖ = 0 ∧
      (∀ f : C₀(Fin 0, ℂ), HasCompactSupport (φ * f) ∧ ‖φ * f - f‖ = 0) := by
  obtain ⟨φ, hsupport, hone, hnorm, hpoint⟩ :=
    ZeroAtInftyContinuousMap.exists_compact_one_on_of_regularSpace
      (X := Fin 0) (K := (∅ : Set (Fin 0))) isCompact_empty
  have hzero : φ = 0 := emptyC0_eq_zero φ
  refine ⟨φ, hsupport, hone, hnorm, hpoint, hzero, ?_, ?_⟩
  · rw [hzero, norm_zero]
  · intro f
    refine ⟨hsupport.mul_right, ?_⟩
    have hfzero : f = 0 := emptyC0_eq_zero f
    rw [hzero, hfzero, zero_mul, sub_self, norm_zero]

end EmptyCutoffFactorySmoke
