/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.PartialDedekindZeta
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Complex.ReImTopology

/-!
# Polar density of sets of height-one primes

This module introduces the corrected polar-density API for `ATLAS NumberTheoryI N409`.

The key semantic correction: `MeromorphicAt` is asserted of `F`, the actual
meromorphic continuation, never of the raw Euler-product `tprod`.
The raw Euler product is only used as a pointwise germ on the right half-plane
`{z : ℂ | 1 < z.re}` near `1`.
-/

@[expose] public section

open Filter Topology NumberField IsDedekindDomain

namespace NumberField.Set

variable {K : Type*} [Field K] [NumberField K]

/-- **Polar density.** Let $K$ be a number field, let $S$ be a set of height-one primes of the
ring of integers of $K$, and let $\zeta_S$ be the partial Dedekind zeta function of $S$. A
rational number $\rho$ is a polar density of $S$ when there exist a positive integer $n$, an
integer $m$ and a function $F : \mathbb{C} \to \mathbb{C}$ such that $F$ is meromorphic at $1$,
$F(s) = \zeta_S(s)^n$ for all $s$ with $\operatorname{Re} s > 1$ in some neighbourhood of $1$,
the meromorphic order of $F$ at $1$ equals $-m$, and $\rho = m / n$.

Meromorphy is required of the continuation $F$, not of the Euler product defining $\zeta_S$. -/
def HasPolarDensity (S : Set (HeightOneSpectrum (𝓞 K))) (ρ : ℚ) : Prop :=
  ∃ (n : ℕ+) (m : ℤ) (F : ℂ → ℂ),
    MeromorphicAt F (1 : ℂ) ∧
      F =ᶠ[nhdsWithin (1 : ℂ) {z : ℂ | (1 : ℝ) < z.re}]
        (fun s => NumberField.partialDedekindZeta K S s ^ (n : ℕ)) ∧
      meromorphicOrderAt F (1 : ℂ) = (↑(-m) : WithTop ℤ) ∧
      ρ = (m : ℚ) / (n : ℚ)

private theorem eventuallyEq_nhdsNE_of_eventuallyEq_re_gt_one
    {f g : ℂ → ℂ} (hf : MeromorphicAt f (1 : ℂ))
    (hg : MeromorphicAt g (1 : ℂ))
    (hfg : f =ᶠ[nhdsWithin (1 : ℂ) {z : ℂ | (1 : ℝ) < z.re}] g) :
    f =ᶠ[𝓝[≠] (1 : ℂ)] g := by
  apply (hf.frequently_eq_iff_eventuallyEq hg).mp
  have hcl : (1 : ℂ) ∈ closure {z : ℂ | (1 : ℝ) < z.re} := by
    rw [Complex.closure_setOfPred_lt_re]
    simp
  let : NeBot (nhdsWithin (1 : ℂ) {z : ℂ | (1 : ℝ) < z.re}) :=
    mem_closure_iff_nhdsWithin_neBot.mp hcl
  exact hfg.frequently.filter_mono <| nhdsWithin_mono (1 : ℂ) <| by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    simp at hz

/-- **Uniqueness of the polar density.** Let $K$ be a number field and let $S$ be a set of
height-one primes of the ring of integers of $K$. If $\rho_1$ and $\rho_2$ are both polar
densities of $S$, then $\rho_1 = \rho_2$.

The point $1$ lies in the closure of the half-plane $\operatorname{Re} s > 1$, so two meromorphic
functions that agree on that half-plane near $1$ agree on a punctured neighbourhood of $1$ and
have the same order there. -/
theorem HasPolarDensity.unique {S : Set (HeightOneSpectrum (𝓞 K))} {ρ₁ ρ₂ : ℚ}
    (h₁ : S.HasPolarDensity ρ₁) (h₂ : S.HasPolarDensity ρ₂) : ρ₁ = ρ₂ := by
  obtain ⟨n₁, m₁, F₁, hmer₁, hcont₁, hord₁, rfl⟩ := h₁
  obtain ⟨n₂, m₂, F₂, hmer₂, hcont₂, hord₂, rfl⟩ := h₂
  have hpow : F₁ ^ (n₂ : ℕ) =ᶠ[nhdsWithin (1 : ℂ) {z : ℂ | (1 : ℝ) < z.re}]
      F₂ ^ (n₁ : ℕ) := by
    filter_upwards [hcont₁, hcont₂] with z hz₁ hz₂
    simp only [Pi.pow_apply]
    rw [hz₁, hz₂, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hne := eventuallyEq_nhdsNE_of_eventuallyEq_re_gt_one
    (hmer₁.pow _) (hmer₂.pow _) hpow
  have hord := meromorphicOrderAt_congr hne
  rw [meromorphicOrderAt_pow hmer₁, meromorphicOrderAt_pow hmer₂,
    hord₁, hord₂] at hord
  have horderZ : ((n₂ : ℕ) : ℤ) * (-m₁) = ((n₁ : ℕ) : ℤ) * (-m₂) := by
    exact_mod_cast hord
  have hint : m₁ * ((n₂ : ℕ) : ℤ) = m₂ * ((n₁ : ℕ) : ℤ) := by
    simpa [mul_comm] using congrArg Neg.neg horderZ
  have hq : (m₁ : ℚ) / (↑n₁ : ℚ) = (m₂ : ℚ) / (↑n₂ : ℚ) := by
    rw [div_eq_div_iff (by exact_mod_cast n₁.ne_zero) (by exact_mod_cast n₂.ne_zero)]
    exact_mod_cast hint
  exact hq

/-- **The empty set has polar density zero.** For every number field $K$, the empty set of
height-one primes of the ring of integers of $K$ has polar density $0$.

The partial Dedekind zeta function of the empty set is the constant $1$, so the constant
continuation $F = 1$ with $n = 1$ and $m = 0$ witnesses this. -/
@[simp] theorem hasPolarDensity_empty (K : Type*) [Field K] [NumberField K] :
    (∅ : Set (HeightOneSpectrum (𝓞 K))).HasPolarDensity 0 := by
  refine ⟨1, 0, fun _ => 1, MeromorphicAt.const (1 : ℂ) (1 : ℂ), ?_, ?_, ?_⟩
  · filter_upwards with z
    simp [NumberField.partialDedekindZeta_empty]
  · simpa using meromorphicOrderAt_const (𝕜 := ℂ) (1 : ℂ) (1 : ℂ)
  · simp

end NumberField.Set
