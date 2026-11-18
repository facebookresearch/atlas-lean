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
* `selectionMutationGenerator_kimuraFixation`, `eq_kimuraFixation_of_selectionMutationGenerator_eq_zero`:
  with mutation switched off, Kimura's fixation probability is the unique
  `C[0, 1] ∩ C²(0, 1)` solution of the fixation boundary-value problem.
* `kimuraFixation_one_half`, `continuousAt_kimuraFixation_zero`, `kimuraFixation_two_mul_mul`:
  the midpoint value, continuity in the selection coefficient at neutrality, and the `4Ns` form.

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

/-! ### Kimura's fixation probability for the mutation-free generator -/

/-- Kimura's fixation probability solves `L_{α,0} u = 0` everywhere, for the combined
selection–mutation generator with mutation switched off. -/
theorem selectionMutationGenerator_kimuraFixation (α x : ℝ) :
    selectionMutationGenerator α 0 0 (kimuraFixation α) x = 0 := by
  rw [selectionMutationGenerator_zero_zero, generator_kimuraFixation]

/-- **Uniqueness** for the fixation boundary-value problem of `L_{α,0}`: a function continuous
on `[0, 1]`, `C²` on `(0, 1)`, solving `L_{α,0} u = 0` on `(0, 1)` with `u 0 = 0` and `u 1 = 1`
equals Kimura's fixation probability on `[0, 1]`. -/
theorem eq_kimuraFixation_of_selectionMutationGenerator_eq_zero {α : ℝ} {u : ℝ → ℝ}
    (hcont : ContinuousOn u (Icc 0 1)) (hu : ContDiffOn ℝ 2 u (Ioo 0 1))
    (hgen : ∀ x ∈ Ioo (0 : ℝ) 1, selectionMutationGenerator α 0 0 u x = 0)
    (h0 : u 0 = 0) (h1 : u 1 = 1) :
    ∀ x ∈ Icc (0 : ℝ) 1, u x = kimuraFixation α x := by
  refine eq_kimuraFixation_of_contDiffOn hcont hu (fun x hx => ?_) h0 h1
  rw [← selectionMutationGenerator_zero_zero]
  exact hgen x hx

/-- The midpoint value at `α = 1`: `u_1(1/2) = 1 / (1 + e^{-1})`. -/
theorem kimuraFixation_one_half : kimuraFixation 1 (1 / 2) = 1 / (1 + exp (-1)) := by
  have ht : exp (-2) = exp (-1) * exp (-1) := by rw [← exp_add]; norm_num
  have h1 : exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hpos := exp_pos (-1)
  have hd1 : 1 - exp (-1) * exp (-1) ≠ 0 := by nlinarith
  have hd2 : (1 : ℝ) + exp (-1) ≠ 0 := by linarith
  simp only [kimuraFixation, one_ne_zero, ↓reduceIte]
  rw [show -2 * (1 : ℝ) * (1 / 2) = -1 by norm_num, show -2 * (1 : ℝ) = -2 by norm_num, ht,
    div_eq_div_iff hd1 hd2]
  ring

/-- `α ↦ u_α(x)` is continuous at the neutral point `α = 0`, where its value is `x`;
so the explicit neutral branch is the continuous extension. -/
theorem continuousAt_kimuraFixation_zero (x : ℝ) :
    ContinuousAt (fun α => kimuraFixation α x) 0 := by
  have hf : HasDerivAt (fun α : ℝ => 1 - exp (-2 * α * x)) (2 * x) 0 := by
    have h : HasDerivAt (fun α : ℝ => -2 * α * x) (-2 * x) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (-2)).mul_const x
    convert h.exp.const_sub 1 using 1
    simp
  have hg : HasDerivAt (fun α : ℝ => 1 - exp (-2 * α)) 2 0 := by
    have h : HasDerivAt (fun α : ℝ => -2 * α) (-2) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-2)
    convert h.exp.const_sub 1 using 1
    simp
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt, kimuraFixation_neutral]
  have key := hf.tendsto_slope_zero.div hg.tendsto_slope_zero two_ne_zero
  rw [show 2 * x / 2 = x by ring] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  have hα' : α ≠ 0 := hα
  simp only [zero_add, smul_eq_mul, kimuraFixation, hα', ↓reduceIte, mul_zero, zero_mul,
    exp_zero, sub_self, sub_zero]
  exact mul_div_mul_left _ _ (inv_ne_zero hα')

/-- Source bridge (Kimura 1962, `N_e = N`): with `α = 2Ns`, `u_α(p) = (1 - e^{-4Nsp}) / (1 - e^{-4Ns})`
whenever `Ns ≠ 0`. -/
theorem kimuraFixation_two_mul_mul (N s p : ℝ) (hNs : N * s ≠ 0) :
    kimuraFixation (2 * N * s) p = (1 - exp (-(4 * N * s * p))) / (1 - exp (-(4 * N * s))) := by
  have h : 2 * N * s ≠ 0 := by rw [mul_assoc]; exact mul_ne_zero two_ne_zero hNs
  have hform : kimuraFixation (2 * N * s) p =
      (1 - exp (-2 * (2 * N * s) * p)) / (1 - exp (-2 * (2 * N * s))) := by
    simp [kimuraFixation, h]
  rw [hform, show -2 * (2 * N * s) * p = -(4 * N * s * p) by ring,
    show -2 * (2 * N * s) = -(4 * N * s) by ring]

end MathlibExt.Biology.PopulationGenetics.Diffusion
