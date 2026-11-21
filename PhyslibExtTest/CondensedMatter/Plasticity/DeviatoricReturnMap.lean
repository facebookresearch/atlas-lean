/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

import PhyslibExt.CondensedMatter.Plasticity.DeviatoricReturnMap

/-!
# Deviatoric return-map checks

## i. Overview

Elaboration, non-vacuity, and endpoint checks for
`PhyslibExt.CondensedMatter.Plasticity.DeviatoricReturnMap`: the public
shape of the metric identity, its symmetric-shear double count, the
zero-correction case at the singleton yield section `{0}`, the
totalized zero-shear-modulus endpoint, and the energy characterization
at `{0}`. These are checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Metric identity
- B. Zero correction and totalization
- C. Energy characterization at a singleton

## iv. References

- `PhyslibExt.CondensedMatter.Plasticity.DeviatoricReturnMap`
-/

open scoped InnerProductSpace Matrix
open MathlibExt.Analysis.InnerProductSpace.ConvexProjection

/-! ## A. Metric identity -/

/-- Public shape of the Frobenius metric identity. -/
example (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    ⟪A, B⟫_ℝ = ∑ i, ∑ j, A i j * B i j :=
  Plasticity.frobenius_inner_eq_sum_mul A B

/-- The unit symmetric shear tensor has squared Frobenius norm `2`:
the off-diagonal pair is counted twice. -/
example :
    ⟪(!![0, 1, 0; 1, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ),
      !![0, 1, 0; 1, 0, 0; 0, 0, 0]⟫_ℝ = 2 := by
  rw [Plasticity.frobenius_inner_eq_sum_mul]
  norm_num [Fin.sum_univ_three]

/-! ## B. Zero correction and totalization -/

/-- At the singleton yield section `{0}` and zero trial stress, the
return has zero plastic strain increment (the in-`K` component of
`deviatoric_return`, with every premise discharged). -/
example :
    Plasticity.plasticStrainIncrement 1 (0 : Matrix (Fin 3) (Fin 3) ℝ)
        (Elasticity.meanStress (0 : Matrix (Fin 3) (Fin 3) ℝ) • 1 +
          convexProjection ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ))
            (Elasticity.deviatoricStress (0 : Matrix (Fin 3) (Fin 3) ℝ)))
      = 0 := by
  have hKne : ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)).Nonempty :=
    Set.singleton_nonempty 0
  have hKc : IsComplete ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)) :=
    @IsCompact.isComplete _ Plasticity.frobeniusUniformSpace _
      (@isCompact_singleton _ Plasticity.frobeniusUniformSpace.toTopologicalSpace _)
  have hKv : Convex ℝ ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)) :=
    convex_singleton 0
  have hKdev : ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)) ⊆
      Plasticity.deviatoricStresses := by
    intro σ hσ
    rw [Set.mem_singleton_iff] at hσ
    subst hσ
    exact ⟨Matrix.transpose_zero, by simp⟩
  have h := Plasticity.deviatoric_return (μ := 1)
    (K := ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)))
    (by norm_num) hKne hKc hKv hKdev
    (σTrial := (0 : Matrix (Fin 3) (Fin 3) ℝ)) Matrix.transpose_zero
  have hmem0 : Elasticity.deviatoricStress (0 : Matrix (Fin 3) (Fin 3) ℝ) ∈
      ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
    simp [Elasticity.deviatoricStress, Elasticity.meanStress]
  exact (h.2.2.2.2.2.2.2.2 hmem0).1

/-- At `μ = 0` the totalized plastic strain increment is `0` for every
pair of stresses. -/
example (σTrial σ : Matrix (Fin 3) (Fin 3) ℝ) :
    Plasticity.plasticStrainIncrement 0 σTrial σ = 0 := by
  simp [Plasticity.plasticStrainIncrement]

/-! ## C. Energy characterization at a singleton -/

/-- At the singleton yield section `{0}`, the energy characterization
gives `convexProjection {0} sTrial = 0` for every trial deviator. -/
example (sTrial : Matrix (Fin 3) (Fin 3) ℝ) :
    convexProjection ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)) sTrial = 0 := by
  have hKne : ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)).Nonempty :=
    Set.singleton_nonempty 0
  have hKc : IsComplete ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)) :=
    @IsCompact.isComplete _ Plasticity.frobeniusUniformSpace _
      (@isCompact_singleton _ Plasticity.frobeniusUniformSpace.toTopologicalSpace _)
  have hKv : Convex ℝ ({0} : Set (Matrix (Fin 3) (Fin 3) ℝ)) :=
    convex_singleton 0
  refine (Plasticity.eq_projection_iff_energy_le (μ := 1) (by norm_num)
    hKne hKc hKv sTrial 0).mpr ⟨rfl, ?_⟩
  intro τ hτ
  rw [Set.mem_singleton_iff] at hτ
  subst hτ
  exact le_refl _
