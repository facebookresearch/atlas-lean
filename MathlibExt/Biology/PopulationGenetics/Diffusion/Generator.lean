/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.Mutation

/-!
# The Wright–Fisher generator with genic selection and two-way mutation

With time in units of `2N` generations, scaled genic selection `α = 2Ns`, and scaled mutation
rates `θ₁ = 4Nu₁` (towards the allele) and `θ₂ = 4Nu₂` (away from it), the backward generator is

`(L f)(x) = x (1 - x) / 2 · f''(x) + (α x (1 - x) + (θ₁ (1 - x) - θ₂ x) / 2) · f'(x)`.

This combines the selection generator `generator` and the mutation generator
`mutationGenerator`, which share the neutral diffusion term.

## Main results

* `selectionMutationGenerator_zero_zero`: without mutation, this is `generator α`.
* `selectionMutationGenerator_zero_left`: without selection, this is `mutationGenerator θ₁ θ₂`.
* `selectionMutationGenerator_eq`: the drifts add, after removing the shared neutral term.
* `selectionMutationGenerator_id`: on the identity, the generator is the drift.
* `selectionMutationGenerator_neutral_sq`: in the neutral case, `L (y ↦ y²) = x (1 - x)`.

## References

* W. J. Ewens, *Mathematical Population Genetics I*, 2nd ed., Springer (2004), ch. 4–5.
* S. N. Ethier and T. G. Kurtz, *Markov Processes*, Wiley (1986), ch. 10.
-/

@[expose] public section

open Real Set Filter
open scoped Topology

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- The backward generator of the Wright–Fisher diffusion with genic selection and two-way
mutation:
`(L f)(x) = x (1 - x) / 2 · f''(x) + (α x (1 - x) + (θ₁ (1 - x) - θ₂ x) / 2) · f'(x)`. -/
noncomputable def selectionMutationGenerator (α θ₁ θ₂ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * (1 - x) / 2 * deriv (deriv f) x +
    (α * x * (1 - x) + (θ₁ * (1 - x) - θ₂ * x) / 2) * deriv f x

/-- Without mutation the generator is the selection generator `generator α`. -/
theorem selectionMutationGenerator_zero_zero (α : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    selectionMutationGenerator α 0 0 f x = generator α f x := by
  simp only [selectionMutationGenerator, generator]
  ring

/-- Without selection the generator is the mutation generator `mutationGenerator θ₁ θ₂`. -/
theorem selectionMutationGenerator_zero_left (θ₁ θ₂ : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    selectionMutationGenerator 0 θ₁ θ₂ f x = mutationGenerator θ₁ θ₂ f x := by
  simp only [selectionMutationGenerator, mutationGenerator]
  ring

/-- The neutral case `L₀ f = x (1 - x) f'' / 2`. -/
theorem selectionMutationGenerator_neutral (f : ℝ → ℝ) (x : ℝ) :
    selectionMutationGenerator 0 0 0 f x = x * (1 - x) / 2 * deriv (deriv f) x := by
  simp only [selectionMutationGenerator]
  ring

/-- The drifts add: the combined generator is the selection generator plus the mutation
generator minus the neutral generator they share. -/
theorem selectionMutationGenerator_eq (α θ₁ θ₂ : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    selectionMutationGenerator α θ₁ θ₂ f x =
      generator α f x + mutationGenerator θ₁ θ₂ f x - generator 0 f x := by
  simp only [selectionMutationGenerator, generator, mutationGenerator]
  ring

/-- The generator on the frequency itself is the drift:
`L id = α x (1 - x) + (θ₁ (1 - x) - θ₂ x) / 2`. -/
theorem selectionMutationGenerator_id (α θ₁ θ₂ x : ℝ) :
    selectionMutationGenerator α θ₁ θ₂ id x =
      α * x * (1 - x) + (θ₁ * (1 - x) - θ₂ * x) / 2 := by
  simp only [selectionMutationGenerator, deriv_id', deriv_const']
  ring

/-- The neutral generator on `y ↦ y ^ 2` is the infinitesimal variance `x (1 - x)`. -/
theorem selectionMutationGenerator_neutral_sq (x : ℝ) :
    selectionMutationGenerator 0 0 0 (fun y => y ^ 2) x = x * (1 - x) := by
  rw [selectionMutationGenerator_zero_zero, generator_pow]
  norm_num
  ring

end MathlibExt.Biology.PopulationGenetics.Diffusion
