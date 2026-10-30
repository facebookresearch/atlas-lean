/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Bernstein.Voronovskaya
public import MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisher

/-!
# Diffusion limit of the Wright–Fisher generator

In one generation of the neutral Wright–Fisher model with `M` gene copies (`M = 2N` for a
diploid population of size `N`), the number of copies of an allele at frequency `x` in the next
generation is `Bin(M, x)`. The expected value of a test function `f` of the new frequency is
`E_x[f(X₁)] = ∫ k, f (k / M) ∂Bin(M, x)`, which is the Bernstein approximation of `f`
(`integral_binomial_eq_bernsteinApproximation`).

Measuring time in units of `M` generations (the convention of
`MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisher`), the rescaled one-generation
generator `M · (E_x[f(X₁)] - f(x))` converges, for `f` of class `C²`, to the neutral
Wright–Fisher diffusion generator `(L_0 f)(x) = x (1 - x) / 2 · f''(x)` (`tendsto_wfGenerator`).
This is Voronovskaya's theorem (`bernsteinApproximation.tendsto_voronovskaya`) read in
population-genetic terms: the generator half of Feller's diffusion approximation. Weak
convergence of the rescaled processes (Ethier and Kurtz 1986, Chapter 10, Theorem 1.1) is not
formalized.

## Main results

* `integral_binomial_eq_bernsteinApproximation`: the one-generation expectation is a Bernstein
  approximation.
* `tendsto_wfGenerator`: `M · (E_x[f(X₁)] - f(x)) → (L_0 f)(x)` for `f ∈ C²` and `x ∈ [0, 1]`.

## References

* W. Feller, *Diffusion processes in genetics*, Proc. Second Berkeley Symp. Math. Statist.
  Probab. (1951) 227–246.
* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley
  (1986), Chapter 10.
* E. V. Voronovskaya, *Détermination de la forme asymptotique d'approximation des fonctions par
  les polynômes de M. Bernstein*, C. R. Acad. Sci. URSS (1932) 79–85.
-/

@[expose] public section

open Filter
open scoped unitInterval Topology

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- **One Wright–Fisher generation as a Bernstein approximation.** For `M` gene copies and
current frequency `x`, the expected value of `f` at the next frequency, `∫ k, f (k / M) ∂Bin(M, x)`,
is the `M`-th Bernstein approximation of `f` on `[0, 1]` evaluated at `x`. -/
theorem integral_binomial_eq_bernsteinApproximation (M : ℕ) {f : ℝ → ℝ} (hf : Continuous f)
    (x : I) :
    ∫ k, f (k / M) ∂(ProbabilityTheory.binomial M x) =
      bernsteinApproximation M ((⟨f, hf⟩ : C(ℝ, ℝ)).restrict I) x := by
  rw [ProbabilityTheory.integral_binomial, bernsteinApproximation.apply, ← Nat.range_succ_eq_Iic,
    ← Fin.sum_univ_eq_sum_range (fun k => ((M.choose k : ℝ) * (x : ℝ) ^ k * (1 - x) ^ (M - k)) •
      f (k / M))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bernstein_apply]
  rfl

/-- **Wright–Fisher diffusion limit, generator form (Feller 1951; Voronovskaya 1932).** For `f`
of class `C²` and `x ∈ [0, 1]`, the one-generation generator of the neutral Wright–Fisher chain
with `M` gene copies, sped up by the factor `M` (time in units of `M` generations), converges
to the neutral Wright–Fisher diffusion generator `(L_0 f)(x) = x (1 - x) / 2 · f''(x)`. -/
theorem tendsto_wfGenerator {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : I) :
    Tendsto (fun M : ℕ => (M : ℝ) *
        (∫ k, f (k / M) ∂(ProbabilityTheory.binomial M x) - f x)) atTop
      (𝓝 (generator 0 f x)) := by
  have h := bernsteinApproximation.tendsto_voronovskaya hf x
  simp only [generator, zero_mul, add_zero]
  refine h.congr fun M => ?_
  rw [integral_binomial_eq_bernsteinApproximation M hf.continuous x]

end MathlibExt.Biology.PopulationGenetics.Diffusion
