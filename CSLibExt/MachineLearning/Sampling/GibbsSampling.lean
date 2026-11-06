/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.MetropolisHastings

/-!
# Gibbs sampling

The target is a law `π` with full support on configurations `ι → S` (finite `ι` and `S`).

* `condLaw π hπ i x`: the conditional law of coordinate `i` given the others,
  `π(xᵢ = s | x₋ᵢ) = π(x with xᵢ := s) / condNorm π i x`.
* `gibbsStep π hπ i x`: one **Gibbs update** of coordinate `i`, which resamples `xᵢ` from its
  conditional law. `gibbsStep_apply` gives its transition probabilities.
* `gibbs_detailedBalance`: each update satisfies detailed balance with respect to `π`.
  `isReversible_gibbsKernel` and `invariant_gibbsKernel` (**Gibbs sampling leaves the target
  stationary**) follow from `MetropolisHastings.lean`.
* `gibbsSweep π hπ l`: the systematic-scan sampler that updates the coordinates in the order of
  the list `l`; `gibbsSweep_cons_apply` says the head coordinate is updated first.
  `invariant_gibbsSweep`: a full sweep, in any order, leaves `π` stationary
  (Mathlib's `Kernel.Invariant.comp`).

## References

* C. P. Robert and G. Casella, *Monte Carlo Statistical Methods*, 2nd ed., Springer, 2004,
  Chapter 10.
* C. M. Bishop, *Pattern Recognition and Machine Learning*, Springer, 2006, §11.3.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Sampling

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S]

/-- **Normalizer of the conditional law.** Let $\pi$ be a probability distribution on the
configurations $x : \iota \to S$, with $\iota$ and $S$ finite. For a coordinate $i \in \iota$ and a
configuration $x$, the normalizer is $Z_i(x) = \sum_{s \in S} \pi(x[i \mapsto s]) \in [0, \infty]$,
where $x[i \mapsto s]$ is $x$ with coordinate $i$ set to $s$. It normalizes the conditional law of
coordinate $i$ given the other coordinates of $x$. -/
noncomputable def condNorm (π : PMF (ι → S)) (i : ι) (x : ι → S) : ℝ≥0∞ :=
  ∑ s, π (update x i s)

omit [Fintype ι] in
theorem condNorm_update (π : PMF (ι → S)) (i : ι) (x : ι → S) (s : S) :
    condNorm π i (update x i s) = condNorm π i x := by
  simp only [condNorm, update_idem]

omit [Fintype ι] in
theorem le_condNorm (π : PMF (ι → S)) (i : ι) (x : ι → S) : π x ≤ condNorm π i x := by
  have := Finset.single_le_sum (f := fun s ↦ π (update x i s)) (fun _ _ ↦ bot_le)
    (Finset.mem_univ (x i))
  simpa [condNorm, update_eq_self] using this

omit [Fintype ι] in
theorem condNorm_ne_top (π : PMF (ι → S)) (i : ι) (x : ι → S) : condNorm π i x ≠ ∞ :=
  ENNReal.sum_ne_top.mpr fun _ _ ↦ PMF.apply_ne_top _ _

/-- **Conditional law of a coordinate.** Let $\pi$ be a probability distribution on the
configurations $x : \iota \to S$, with $\iota$ and $S$ finite, such that $\pi(x) \neq 0$ for every
$x$. For a coordinate $i \in \iota$ and a configuration $x$, the conditional law of coordinate $i$
given the others is the probability distribution on $S$ that gives $s \in S$ the mass
$\pi(x[i \mapsto s]) / Z_i(x)$, where $x[i \mapsto s]$ is $x$ with coordinate $i$ set to $s$ and
$Z_i(x) = \sum_{t \in S} \pi(x[i \mapsto t])$. In the usual notation this is
$\pi(x_i = s \mid x_{-i})$, where $x_i$ is coordinate $i$ of $x$ and $x_{-i}$ is the family of
its other coordinates. -/
noncomputable def condLaw (π : PMF (ι → S)) (hπ : ∀ x, π x ≠ 0) (i : ι) (x : ι → S) : PMF S :=
  PMF.ofFintype (fun s ↦ π (update x i s) / condNorm π i x) (by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    exact ENNReal.mul_inv_cancel (ne_bot_of_le_ne_bot (hπ x) (le_condNorm π i x))
      (condNorm_ne_top π i x))

/-- **Gibbs update.** Let $\pi$ be a probability distribution on the configurations
$x : \iota \to S$, with $\iota$ and $S$ finite, such that $\pi(x) \neq 0$ for every $x$. The Gibbs
update of coordinate $i \in \iota$ from $x$ is the probability distribution of $x[i \mapsto s]$,
the configuration $x$ with coordinate $i$ set to $s$, where $s$ is drawn from the conditional law
of coordinate $i$ given the other coordinates of $x$. -/
noncomputable def gibbsStep (π : PMF (ι → S)) (hπ : ∀ x, π x ≠ 0) (i : ι) (x : ι → S) :
    PMF (ι → S) :=
  (condLaw π hπ i x).map (update x i)

theorem gibbsStep_apply [DecidableEq S] (π : PMF (ι → S)) (hπ : ∀ x, π x ≠ 0) (i : ι)
    (x y : ι → S) :
    gibbsStep π hπ i x y = if update x i (y i) = y then π y / condNorm π i x else 0 := by
  rw [gibbsStep, PMF.map_apply, tsum_eq_single (y i)]
  · by_cases h : update x i (y i) = y
    · simp [h, condLaw]
    · simp [h, Ne.symm h]
  · intro s hs
    simp only [ite_eq_right_iff]
    rintro rfl
    exact absurd (update_self i s x).symm hs

omit [Fintype ι] [Fintype S] in
/-- **Symmetry of differing in one coordinate.** For functions $x, y : \iota \to S$ and a coordinate
$i \in \iota$, if setting coordinate $i$ of $x$ to $y(i)$ gives $y$, then setting coordinate $i$ of
$y$ to $x(i)$ gives $x$. -/
theorem update_eq_comm {i : ι} {x y : ι → S} (h : update x i (y i) = y) :
    update y i (x i) = x := by
  rw [← h, update_idem, update_eq_self]

omit [Fintype ι] in
/-- **Detailed balance for a Gibbs update.** Let $\pi$ be a probability distribution on the
configurations $x : \iota \to S$, with $\iota$ and $S$ finite, such that $\pi(x) \neq 0$ for every
$x$, and for a coordinate $i$ let $P_i(x, y)$ be the probability that the Gibbs update of
coordinate $i$ moves $x$ to $y$. Then $\pi(x) P_i(x, y) = \pi(y) P_i(y, x)$ for all
configurations $x$ and $y$.

When $x$ and $y$ differ at most in coordinate $i$, both sides equal $\pi(x) \pi(y) / Z$ for the
same normalizer $Z$; otherwise both sides are $0$. -/
theorem gibbs_detailedBalance [Finite ι] (π : PMF (ι → S)) (hπ : ∀ x, π x ≠ 0) (i : ι)
    (x y : ι → S) : π x * gibbsStep π hπ i x y = π y * gibbsStep π hπ i y x := by
  have := Fintype.ofFinite ι
  classical
  rw [gibbsStep_apply, gibbsStep_apply]
  by_cases h : update x i (y i) = y
  · have h' := update_eq_comm h
    have hZ : condNorm π i y = condNorm π i x := by rw [← h, condNorm_update]
    simp only [h, h', ite_true, hZ]
    rw [← mul_div_assoc, ← mul_div_assoc, mul_comm]
  · have h' : update y i (x i) ≠ x := fun h' ↦ h (update_eq_comm h')
    simp [h, h']

variable [MeasurableSpace S] [MeasurableSingletonClass S]

/-- **Gibbs updates are reversible.** Let $\pi$ be a probability distribution on the
configurations $x : \iota \to S$, with $\iota$ and $S$ finite, such that $\pi(x) \neq 0$ for every
$x$. For every coordinate $i$, the Markov kernel $K$ of the Gibbs update of coordinate $i$ is
reversible with respect to $\pi$: for all measurable sets $A$ and $B$ of configurations,
$\int_A K(x, B) \, d\pi(x) = \int_B K(x, A) \, d\pi(x)$. -/
theorem isReversible_gibbsKernel (π : PMF (ι → S)) (hπ : ∀ x, π x ≠ 0) (i : ι) :
    (pmfKernel (gibbsStep π hπ i)).IsReversible π.toMeasure :=
  isReversible_pmfKernel (gibbs_detailedBalance π hπ i)

/-- **Gibbs sampling leaves the target stationary.** Let $\pi$ be a probability distribution on
the configurations $x : \iota \to S$, with $\iota$ and $S$ finite, such that $\pi(x) \neq 0$ for
every $x$. For every coordinate $i$, $\pi$ is an invariant measure of the Markov kernel of the
Gibbs update of coordinate $i$: if $x$ is drawn from $\pi$ and coordinate $i$ is resampled from
its conditional law given the other coordinates, the result is again distributed as $\pi$. -/
theorem invariant_gibbsKernel (π : PMF (ι → S)) (hπ : ∀ x, π x ≠ 0) (i : ι) :
    (pmfKernel (gibbsStep π hπ i)).Invariant π.toMeasure :=
  invariant_pmfKernel (gibbs_detailedBalance π hπ i)

/-- **Systematic-scan Gibbs sampler.** Let $\pi$ be a probability distribution on the
configurations $x : \iota \to S$, with $\iota$ and $S$ finite, such that $\pi(x) \neq 0$ for every
$x$. For a list $l = (i_1, \dots, i_n)$ of coordinates, the systematic-scan Gibbs sampler is the
Markov kernel on configurations that applies the Gibbs updates of the coordinates
$i_1, i_2, \dots, i_n$ in this order; for the empty list it is the identity kernel. -/
noncomputable def gibbsSweep (π : PMF (ι → S)) (hπ : ∀ x, π x ≠ 0) :
    List ι → Kernel (ι → S) (ι → S)
  | [] => Kernel.id
  | i :: l => gibbsSweep π hπ l ∘ₖ pmfKernel (gibbsStep π hπ i)

/-- **First step of a Gibbs sweep.** Let $\pi$ be a probability distribution on the configurations
$x : \iota \to S$, with $\iota$ and $S$ finite, such that $\pi(x) \neq 0$ for every $x$. For a list
$l$ of coordinates let $K_l$ be the systematic-scan Gibbs sampler for $l$, and for a coordinate $i$
let $P_i$ be the Markov kernel of the Gibbs update of coordinate $i$. Then for every configuration
$x$, the law $K_{(i, l)}(x)$ of the sampler for the list $(i, l)$ obtained by putting $i$ in front
of $l$ is the mixture $\int K_l(y) \, P_i(x, dy)$: first coordinate $i$ is updated, then the sweep
$l$ runs from the result. -/
theorem gibbsSweep_cons_apply (π : PMF (ι → S)) (hπ : ∀ x, π x ≠ 0) (i : ι) (l : List ι)
    (x : ι → S) :
    gibbsSweep π hπ (i :: l) x = (pmfKernel (gibbsStep π hπ i) x).bind (gibbsSweep π hπ l) :=
  Kernel.comp_apply _ _ x

instance (π : PMF (ι → S)) (hπ : ∀ x, π x ≠ 0) (l : List ι) :
    IsMarkovKernel (gibbsSweep π hπ l) := by
  induction l with
  | nil => exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | cons i l ih => exact inferInstanceAs (IsMarkovKernel (_ ∘ₖ _))

/-- **A full Gibbs sweep leaves the target stationary.** Let $\pi$ be a probability distribution on
the configurations $x : \iota \to S$, with $\iota$ and $S$ finite, such that $\pi(x) \neq 0$ for
every $x$. For every finite list $l$ of coordinates, in any order and possibly with repetitions,
$\pi$ is an invariant measure of the systematic-scan Gibbs sampler that updates the coordinates in
the order of $l$. -/
theorem invariant_gibbsSweep (π : PMF (ι → S)) (hπ : ∀ x, π x ≠ 0) (l : List ι) :
    (gibbsSweep π hπ l).Invariant π.toMeasure := by
  induction l with
  | nil => exact Measure.id_comp
  | cons i l ih => exact ih.comp (invariant_gibbsKernel π hπ i)

end Cslib.MachineLearning.Sampling
