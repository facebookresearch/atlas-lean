/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `bc0a5a31aa07d127ead55e6848aa133300c4ce0a`.
Original formalization by Manasa Hariharan (@manasahari-meta); ported with permission.
-/

module

public import Mathlib.Probability.Density
public import Mathlib.Order.Filter.Extr
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.CompleteLattice.Basic

/-!
# Iid likelihood, MLE maps, and induced likelihood (Casella–Berger §7.2.2)

Summary: genuine normalized iid density/mass model with finite-product
likelihood; complete all-sample MLE map predicate; whole-fiber supremum
induced likelihood on the image of a parameter transformation.

Source locators only: normalized `text.txt` 11226–11237 (iid product and
complete MLE map) and 11335–11359 (induced fiber supremum, equation 7.2.5);
raw OCR inspected directly by Muse. No source text is reproduced here.

Representation: an `AEMeasurable` `ℝ≥0∞` density family normalized by
`∫⁻ = 1` under a common dominating measure, with laws defined by
`withDensity`. No pointwise finiteness is assumed. Counting measure gives
the discrete case; volume gives the continuous case.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

open scoped BigOperators ENNReal

/-- **Normalized density family.** Let $\Omega$ be a measurable space with a measure $\mu$ and
let $\Theta$ be a set of parameters. A normalized density family on $\Omega$ indexed by $\Theta$
with dominating measure $\mu$ consists of a function $f_\theta : \Omega \to [0, \infty]$ for
each $\theta \in \Theta$ such that $f_\theta$ is $\mu$-almost everywhere measurable and
$\int_\Omega f_\theta \, d\mu = 1$.

Taking $\mu$ to be counting measure gives probability mass functions, and taking $\mu$ to be
volume gives probability density functions. The densities may take the value $\infty$. -/
structure NormalizedDensityFamily (Ω : Type*) (Θ : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) where
  dens : Θ → Ω → ℝ≥0∞
  measurable : ∀ θ, AEMeasurable (dens θ) μ
  normalized : ∀ θ, ∫⁻ x, dens θ x ∂μ = 1

namespace NormalizedDensityFamily

variable {Ω Θ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Normalized density families are determined by their densities.** Let $F$ and $G$ be
normalized density families on a measurable space $\Omega$ with the same parameter set
$\Theta$ and the same dominating measure $\mu$. If for every $\theta \in \Theta$ and every
$x \in \Omega$ the density of $F$ at $\theta$ and the density of $G$ at $\theta$ take the same
value at $x$, then $F = G$.

Only the densities are compared; the measurability and normalization conditions are
propositions. -/
@[ext]
theorem ext {F G : NormalizedDensityFamily Ω Θ μ}
    (h : ∀ θ x, F.dens θ x = G.dens θ x) : F = G := by
  obtain ⟨densF, _, _⟩ := F
  obtain ⟨densG, _, _⟩ := G
  have hdens : densF = densG := funext fun θ => funext fun x => h θ x
  subst hdens
  rfl

/-- **Population law.** Let $F$ be a normalized density family on a measurable space $\Omega$
with parameter set $\Theta$, dominating measure $\mu$ and densities $f_\theta$. The population
law at $\theta \in \Theta$ is the measure $P_\theta$ on $\Omega$ with density $f_\theta$ with
respect to $\mu$, so that $P_\theta(A) = \int_A f_\theta \, d\mu$ for every measurable set
$A \subseteq \Omega$. -/
noncomputable def law (F : NormalizedDensityFamily Ω Θ μ) (θ : Θ) :
    Measure Ω :=
  μ.withDensity (F.dens θ)

/-- **Population laws are probability measures.** Let $F$ be a normalized density family on
$\Omega$ with parameter set $\Theta$, dominating measure $\mu$ and densities $f_\theta$. For
every $\theta \in \Theta$, the population law $P_\theta$, the measure with density $f_\theta$
with respect to $\mu$, is a probability measure. -/
theorem isProbabilityMeasure_law (F : NormalizedDensityFamily Ω Θ μ)
    (θ : Θ) : IsProbabilityMeasure (F.law θ) := by
  constructor
  rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    F.normalized θ]

/-- **Likelihood of an iid sample.** Let $F$ be a normalized density family on $\Omega$ with
parameter set $\Theta$ and densities $f_\theta$ for $\theta \in \Theta$. For a sample size $n$,
a parameter $\theta \in \Theta$ and a sample $x = (x_0, \dots, x_{n-1}) \in \Omega^n$, the iid
likelihood of $\theta$ at $x$ is $L_n(\theta; x) = \prod_{i < n} f_\theta(x_i)$, a value in
$[0, \infty]$. For $n = 0$ this is the empty product $1$. -/
noncomputable def iidLikelihood (F : NormalizedDensityFamily Ω Θ μ) (n : ℕ)
    (θ : Θ) (x : Fin n → Ω) : ℝ≥0∞ :=
  ∏ i, F.dens θ (x i)

@[simp]
theorem iidLikelihood_apply (F : NormalizedDensityFamily Ω Θ μ) (n : ℕ)
    (θ : Θ) (x : Fin n → Ω) :
    F.iidLikelihood n θ x = ∏ i, F.dens θ (x i) :=
  rfl

/-- **Likelihood of the empty sample.** For a normalized density family $F$, every parameter
$\theta$ and the empty sample $x$ (sample size $n = 0$), the iid likelihood of $\theta$ at $x$
equals $1$, the empty product. -/
@[simp]
theorem iidLikelihood_nil (F : NormalizedDensityFamily Ω Θ μ) (θ : Θ)
    (x : Fin 0 → Ω) : F.iidLikelihood 0 θ x = 1 := by
  simp [iidLikelihood]

/-- **Maximum likelihood estimator.** Let $F$ be a normalized density family on $\Omega$ with
parameter set $\Theta$, let $n$ be a sample size, and let $L_n(\theta; x)$ denote the iid
likelihood of $\theta \in \Theta$ at a sample $x \in \Omega^n$. A map $\hat\theta$ from
$\Omega^n$ to $\Theta$ is a maximum likelihood estimator for samples of size $n$ if for every
sample $x \in \Omega^n$ the parameter $\hat\theta(x)$ maximizes $\theta \mapsto L_n(\theta; x)$
over all of $\Theta$. -/
def IsMaximumLikelihoodEstimator (F : NormalizedDensityFamily Ω Θ μ) (n : ℕ)
    (θhat : (Fin n → Ω) → Θ) : Prop :=
  ∀ x, IsMaxOn (fun θ => F.iidLikelihood n θ x) Set.univ (θhat x)

/-- **Characterization of maximum likelihood estimators.** Let $F$ be a normalized density
family on $\Omega$ with parameter set $\Theta$, let $n$ be a sample size, let $L_n(\theta; x)$
denote the iid likelihood of $\theta \in \Theta$ at a sample $x \in \Omega^n$, and let
$\hat\theta$ be a map from $\Omega^n$ to $\Theta$. Then $\hat\theta$ is a maximum likelihood
estimator for samples of size $n$ if and only if $L_n(\theta; x) \le L_n(\hat\theta(x); x)$
for every sample $x \in \Omega^n$ and every $\theta \in \Theta$. -/
theorem isMaximumLikelihoodEstimator_iff (F : NormalizedDensityFamily Ω Θ μ)
    (n : ℕ) (θhat : (Fin n → Ω) → Θ) :
    F.IsMaximumLikelihoodEstimator n θhat ↔
      ∀ x θ, F.iidLikelihood n θ x ≤ F.iidLikelihood n (θhat x) x := by
  constructor
  · intro h x θ
    exact (isMaxOn_univ_iff.mp (h x)) θ
  · intro h x
    exact isMaxOn_univ_iff.mpr (h x)

/-- **Induced likelihood.** Let $F$ be a normalized density family on $\Omega$ with parameter
set $\Theta$, let $n$ be a sample size, let $\tau : \Theta \to H$ be a map into a set $H$, and
let $x \in \Omega^n$ be a sample. For $\eta$ in the image of $\tau$, the induced likelihood of
$\eta$ at $x$ is the supremum, in $[0, \infty]$, of the iid likelihood $L_n(\theta; x)$ over
the fiber of $\tau$ above $\eta$:
$$L^*_n(\eta; x) = \sup_{\theta \in \Theta,\ \tau(\theta) = \eta} L_n(\theta; x).$$

Since $\eta$ lies in the image of $\tau$, the fiber is nonempty; no inverse of $\tau$ is
chosen. -/
noncomputable def inducedLikelihood (F : NormalizedDensityFamily Ω Θ μ)
    (n : ℕ) {H : Type*} (τ : Θ → H) (x : Fin n → Ω)
    (η : Set.range τ) : ℝ≥0∞ :=
  ⨆ θ : { θ : Θ // τ θ = η.val }, F.iidLikelihood n θ.val x

end NormalizedDensityFamily

end ProbabilityTheory
