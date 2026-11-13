/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Multiple recurrence and convergence along fractional powers of primes (Frantzikinakis, Problem 27)

Frantzikinakis, Some open problems on multiple ergodic averages, Problem 27: let `c` be a positive
non-integer. Show that the sequence `([p_n^c])`, `p_n` the `n`-th prime, is good for multiple
recurrence and convergence of powers.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Nat.Nth
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

@[expose] public section

namespace MathlibExt.Dynamics.PrimeFractionalPowerRecurrenceAMR47Problem0027Wanted

/-!
Source: N. Frantzikinakis, Some open problems on multiple ergodic averages, Bull. Hellenic Math.
Soc. 60 (2016), 41-90, arXiv:1103.3808, Problem 27. UnsolvedMath record UM-04800027
(`AMR-047-0027`), dataset ulamai/UnsolvedMath v1.8.0.

Frantzikinakis's notions (survey, Definitions 3.1-3.4) are formalized for the powers `T, T², …, T^k`
of one transformation, the form in which Koutsogiannis and Tsinas state and prove them: recurrence
asks for `n` with `⌊p_n^c⌋ ≠ 0` and `μ(A ∩ T^{-⌊p_n^c⌋} A ∩ ⋯ ∩ T^{-k⌊p_n^c⌋} A) > 0`; convergence
asks that `(1/N) ∑_{n=1}^{N} T^{⌊p_n^c⌋} f₁ ⋯ T^{k⌊p_n^c⌋} f_k` converge in `L²(μ)` for all `f₁, …,
f_k ∈ L^∞(μ)`. Systems are invertible measure-preserving transformations (measurable equivalences)
of a standard Borel probability space, as in Koutsogiannis-Tsinas (Section 1); `T^m f = f ∘ T^m` and
`T^{-m} A` is the preimage of `A` under `T^m`. Primes are indexed from `0` (`p_0 = 2`), which does
not change the averages. Koutsogiannis-Tsinas average over the primes `p ≤ N` with weight `1 / π(N)`
and state that their Theorems 1.3 and 1.6(a), for `a(t) = t^c`, answer Problem 27.
-/

open MeasureTheory Filter Topology

/-- `⌊p_n^c⌋` for the `n`-th prime `p_n` (indexed from `0`, so `p_0 = 2`). -/
noncomputable def primePowerFloor (c : ℝ) (n : ℕ) : ℕ :=
  ⌊((Nat.nth Nat.Prime n : ℕ) : ℝ) ^ c⌋₊

/-- Multiple recurrence along `⌊p_n^c⌋` (Frantzikinakis's Problem 27, recurrence part, for the
powers `T, T², …, T^k` as in Koutsogiannis-Tsinas): for every positive non-integer `c`, every `k`,
every invertible measure-preserving transformation `T` of a standard probability space and every
measurable `A` with `μ A > 0`, some `n` has `⌊p_n^c⌋ ≠ 0` and
`μ(A ∩ T^{-⌊p_n^c⌋} A ∩ ⋯ ∩ T^{-k ⌊p_n^c⌋} A) > 0`. -/
def primeFractionalPowerMultipleRecurrence : Prop :=
  ∀ c : ℝ, 0 < c → (∀ m : ℤ, c ≠ m) → ∀ k : ℕ,
    ∀ (X : Type) [MeasurableSpace X] [StandardBorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
      (T : X ≃ᵐ X), MeasurePreserving T μ μ → ∀ A : Set X, MeasurableSet A → 0 < μ A →
        ∃ n : ℕ, 0 < primePowerFloor c n ∧
          0 < μ (A ∩ ⋂ j : Fin k, (⇑T)^[((j : ℕ) + 1) * primePowerFloor c n] ⁻¹' A)

/-- Mean convergence along `⌊p_n^c⌋` (Frantzikinakis's Problem 27, convergence part, for the powers
`T, T², …, T^k` as in Koutsogiannis-Tsinas): for every positive non-integer `c`, every `k`, every
invertible measure-preserving transformation `T` of a standard probability space and all
`f₁, …, f_k ∈ L^∞`, the averages `(1/N) ∑_{n < N} ∏ⱼ fⱼ ∘ T^{j ⌊p_n^c⌋}` converge in `L²`. -/
def primeFractionalPowerMultipleConvergence : Prop :=
  ∀ c : ℝ, 0 < c → (∀ m : ℤ, c ≠ m) → ∀ k : ℕ,
    ∀ (X : Type) [MeasurableSpace X] [StandardBorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
      (T : X ≃ᵐ X), MeasurePreserving T μ μ → ∀ f : Fin k → X → ℂ, (∀ j, MemLp (f j) ⊤ μ) →
        ∃ g : X → ℂ, MemLp g 2 μ ∧
          Tendsto (fun N : ℕ => eLpNorm (fun x => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N,
            ∏ j : Fin k, f j ((⇑T)^[((j : ℕ) + 1) * primePowerFloor c n] x) - g x) 2 μ)
            atTop (𝓝 0)

/--
Resolved true: Koutsogiannis and Tsinas (Theorem 1.6(a) with `a(t) = t^c`, which satisfies their
condition (11) for positive non-integer `c`) prove that the averages over the primes `p ≤ N` of `μ(A
∩ T^{-⌊p^c⌋} A ∩ ⋯ ∩ T^{-k⌊p^c⌋} A)` have a positive limit, so some prime `p_n` gives a set of
positive measure, and `⌊p_n^c⌋ ≥ 1` since `p_n ≥ 2`; they state that this, with Theorem 1.3, answers
Problem 27. Source: N. Frantzikinakis, Some open problems on multiple ergodic averages, Bull.
Hellenic Math. Soc. 60 (2016), 41-90, arXiv:1103.3808, Problem 27; resolution: A. Koutsogiannis and
K. Tsinas, Ergodic averages for sparse sequences along primes, J. Mod. Dyn. 22 (2026), 1-71;
arXiv:2309.04939, Theorem 1.3 (for a Hardy field function a of polynomial growth satisfying (11),
and any system, k and f₁, …, f_k ∈ L^∞(μ), the averages (1/π(N)) ∑_{p ≤ N prime} T^{⌊a(p)⌋} f₁ ⋯
T^{k⌊a(p)⌋} f_k converge in L²(μ)) and Theorem 1.6(a) (under (11), lim_N (1/π(N)) ∑_{p ≤ N prime}
μ(A ∩ T^{-⌊a(p)⌋} A ∩ ⋯ ∩ T^{-k⌊a(p)⌋} A) > 0 for every A of positive measure); after Corollary 1.7:
'Specializing to the case where a(n) = n^c where c is a positive non-integer, Theorem 1.3 and part
(a) of Theorem 1.6 provide an affirmative answer to [12, Problem 27]', [12] being Frantzikinakis's
survey; a(t) = t^c satisfies their condition (11), |a(t) - c' q(t)| / log t -> infinity for all c'
in R and q in Z[t], https://doi.org/10.3934/jmd.2026001.
-/
public theorem_wanted primeFractionalPowerMultipleRecurrence_holds :
    primeFractionalPowerMultipleRecurrence

/--
Resolved true: Koutsogiannis and Tsinas (Theorem 1.3 with `a(t) = t^c`) prove that `(1/π(N)) ∑_{p ≤
N} T^{⌊p^c⌋} f₁ ⋯ T^{k⌊p^c⌋} f_k` converges in `L²(μ)`; these are the averages over the first `π(N)`
primes, and they state that this, with Theorem 1.6(a), answers Problem 27, whose averages run over
the first `N` primes. Source: N. Frantzikinakis, Some open problems on multiple ergodic averages,
Bull. Hellenic Math. Soc. 60 (2016), 41-90, arXiv:1103.3808, Problem 27; resolution: A.
Koutsogiannis and K. Tsinas, Ergodic averages for sparse sequences along primes, J. Mod. Dyn. 22
(2026), 1-71; arXiv:2309.04939, Theorem 1.3 (for a Hardy field function a of polynomial growth
satisfying (11), and any system, k and f₁, …, f_k ∈ L^∞(μ), the averages (1/π(N)) ∑_{p ≤ N prime}
T^{⌊a(p)⌋} f₁ ⋯ T^{k⌊a(p)⌋} f_k converge in L²(μ)) and Theorem 1.6(a) (under (11), lim_N (1/π(N))
∑_{p ≤ N prime} μ(A ∩ T^{-⌊a(p)⌋} A ∩ ⋯ ∩ T^{-k⌊a(p)⌋} A) > 0 for every A of positive measure);
after Corollary 1.7: 'Specializing to the case where a(n) = n^c where c is a positive non-integer,
Theorem 1.3 and part (a) of Theorem 1.6 provide an affirmative answer to [12, Problem 27]', [12]
being Frantzikinakis's survey; a(t) = t^c satisfies their condition (11), |a(t) - c' q(t)| / log t
-> infinity for all c' in R and q in Z[t], https://doi.org/10.3934/jmd.2026001.
-/
public theorem_wanted primeFractionalPowerMultipleConvergence_holds :
    primeFractionalPowerMultipleConvergence

end MathlibExt.Dynamics.PrimeFractionalPowerRecurrenceAMR47Problem0027Wanted
