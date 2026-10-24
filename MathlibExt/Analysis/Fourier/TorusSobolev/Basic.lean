/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Data.EReal.Operations

/-!
# Fourier Sobolev optimization on the two-dimensional torus

Actual real continuous functions on the period-`2π` torus, their canonical Haar
Fourier coefficients, full spectral `H²`, and global logarithmic optimization.
The supremum definitions do not assume finiteness or attainment. Equivalence to
physical weak-derivative energies is a separate mathematical bridge.
-/

@[expose] public section

noncomputable section

namespace TorusSobolev

/-- **The torus of period $2\pi$.** The two-dimensional torus
$\mathbb{T}^2 = (\mathbb{R}/2\pi\mathbb{Z})^2$, the product of two copies of the circle
$\mathbb{R}/2\pi\mathbb{Z}$. -/
abbrev Torus := Fin 2 → AddCircle (2 * Real.pi)

/-- **Integer frequencies.** The frequencies are the elements of the lattice $\mathbb{Z}^2$,
that is, the pairs $k = (k_1, k_2)$ of integers; they index the Fourier modes of the torus
$(\mathbb{R}/2\pi\mathbb{Z})^2$. -/
abbrev Frequency := Fin 2 → ℤ

/-- **Rescaling the torus to unit period.** The homeomorphism from the torus
$\mathbb{T}^2 = (\mathbb{R}/2\pi\mathbb{Z})^2$ onto the unit torus $(\mathbb{R}/\mathbb{Z})^2$
that sends $(x_1, x_2)$ to $(x_1/(2\pi), x_2/(2\pi))$. -/
def unitRescaling : Torus ≃ₜ UnitAddTorus (Fin 2) :=
  Homeomorph.piCongrRight fun _ ↦
    AddCircle.homeomorphAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero

/-- **A function on the torus as a function on the unit torus.** For a continuous function
$u : \mathbb{T}^2 \to \mathbb{R}$ on the torus $\mathbb{T}^2 = (\mathbb{R}/2\pi\mathbb{Z})^2$, its
unit representative is the continuous function $\tilde u : (\mathbb{R}/\mathbb{Z})^2 \to \mathbb{C}$
given by $\tilde u(y) = u(2\pi y)$, the composition of $u$ with the inverse of the rescaling to
unit period, with its real values regarded as complex numbers. -/
def unitRepresentative (u : C(Torus, ℝ)) : C(UnitAddTorus (Fin 2), ℂ) where
  toFun x := (u (unitRescaling.symm x) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (u.continuous.comp unitRescaling.symm.continuous)

/-- **Fourier coefficients on the torus.** Let $u : (\mathbb{R}/2\pi\mathbb{Z})^2 \to \mathbb{R}$
be continuous and let $k \in \mathbb{Z}^2$ be a frequency. The Fourier coefficient of $u$ at
$k$ is $a_k = 2\pi c_k$, where $c_k = \int_{[0,1]^2} u(2\pi y)\, e^{-2\pi i\, k \cdot y}\, dy$
is the Fourier coefficient of the rescaled function $y \mapsto u(2\pi y)$ on the unit torus
with respect to normalized Haar measure. Equivalently,
$a_k = \frac{1}{2\pi} \int_{[0,2\pi]^2} u(x)\, e^{-i\, k \cdot x}\, dx$. -/
def fourierCoefficient (u : C(Torus, ℝ)) (k : Frequency) : ℂ :=
  (2 * Real.pi : ℂ) * UnitAddTorus.mFourierCoeff (unitRepresentative u) k

/-- **Squared frequency.** For a frequency $k = (k_1, k_2) \in \mathbb{Z}^2$, the frequency
weight is $|k|^2 = k_1^2 + k_2^2$, the squared frequency of the mode $e^{i k \cdot x}$ on the
torus $(\mathbb{R}/2\pi\mathbb{Z})^2$. -/
def frequencyWeight (k : Frequency) : ℝ := ∑ i, (k i : ℝ) ^ 2

/-- **Gradient energy.** For a continuous function
$u : (\mathbb{R}/2\pi\mathbb{Z})^2 \to \mathbb{R}$ with Fourier coefficients $a_k$, the gradient
energy is $\sum_{k \in \mathbb{Z}^2} |k|^2 \, |a_k|^2$, where $|k|^2 = k_1^2 + k_2^2$; the sum is
taken to be $0$ when the series diverges.

By Parseval's identity, for smooth $u$ this equals $\int_{[0,2\pi]^2} |\nabla u(x)|^2 \, dx$. -/
def gradientEnergy (u : C(Torus, ℝ)) : ℝ :=
  ∑' k, frequencyWeight k * ‖fourierCoefficient u k‖ ^ 2

/-- **Laplacian energy.** For a continuous function
$u : (\mathbb{R}/2\pi\mathbb{Z})^2 \to \mathbb{R}$ with Fourier coefficients $a_k$, the Laplacian
energy is $\sum_{k \in \mathbb{Z}^2} |k|^4 \, |a_k|^2$, where $|k|^2 = k_1^2 + k_2^2$; the sum is
taken to be $0$ when the series diverges.

By Parseval's identity, for smooth $u$ this equals $\int_{[0,2\pi]^2} |\Delta u(x)|^2 \, dx$. -/
def laplaceEnergy (u : C(Torus, ℝ)) : ℝ :=
  ∑' k, frequencyWeight k ^ 2 * ‖fourierCoefficient u k‖ ^ 2

/-- **Functions in $H^2$.** A continuous function $u : (\mathbb{R}/2\pi\mathbb{Z})^2 \to \mathbb{R}$
with Fourier coefficients $a_k$ is in $H^2$ when the series
$\sum_{k \in \mathbb{Z}^2} (1 + |k|^2)^2 \, |a_k|^2$ converges, where $|k|^2 = k_1^2 + k_2^2$.

This is the full spectral $H^2$ condition, not a restriction to trigonometric polynomials. -/
def IsH2 (u : C(Torus, ℝ)) : Prop :=
  Summable fun k ↦ (1 + frequencyWeight k) ^ 2 * ‖fourierCoefficient u k‖ ^ 2

/-- **Normalized Haar measure on the unit torus.** The measure on the unit torus
$(\mathbb{R}/\mathbb{Z})^2$ that is the product of two copies of the Haar probability measure on the
circle $\mathbb{R}/\mathbb{Z}$. -/
def unitHaar : MeasureTheory.Measure (UnitAddTorus (Fin 2)) :=
  MeasureTheory.Measure.pi fun _ : Fin 2 ↦ AddCircle.haarAddCircle

/-- **Mean of a function on the torus.** For a continuous function $u : \mathbb{T}^2 \to \mathbb{R}$
on the torus $\mathbb{T}^2 = (\mathbb{R}/2\pi\mathbb{Z})^2$, its mean is
$\int_{(\mathbb{R}/\mathbb{Z})^2} u(2\pi y)\, d\mu(y)$, where $\mu$ is the normalized Haar measure
on the unit torus $(\mathbb{R}/\mathbb{Z})^2$ and $y \mapsto 2\pi y$ is the inverse of the rescaling
to unit period.

Since $\mu$ is a probability measure, this is the average
$(2\pi)^{-2} \int_{[0, 2\pi]^2} u(x)\, dx$; the Lebesgue integral of $u$ over a period cell is
$(2\pi)^2$ times the mean. -/
def mean (u : C(Torus, ℝ)) : ℝ :=
  ∫ y, u (unitRescaling.symm y) ∂unitHaar

/-- **Zero-mean $H^2$ functions.** A continuous function
$u : (\mathbb{R}/2\pi\mathbb{Z})^2 \to \mathbb{R}$ is a zero-mean $H^2$ function when it is in
$H^2$ and its mean is $0$. -/
def IsZeroMeanH2 (u : C(Torus, ℝ)) : Prop := IsH2 u ∧ mean u = 0

/-- **Conditionally admissible functions.** Let $\delta$ be a real number. A continuous
function $u : (\mathbb{R}/2\pi\mathbb{Z})^2 \to \mathbb{R}$ is admissible at level $\delta$
when it is a zero-mean $H^2$ function, its gradient energy equals $1$, and its Laplacian
energy equals $\delta$. -/
def ConditionalAdmissible (u : C(Torus, ℝ)) (δ : ℝ) : Prop :=
  IsZeroMeanH2 u ∧ gradientEnergy u = 1 ∧ laplaceEnergy u = δ

/-- **Squared values at the origin of admissible functions.** For a real number $\delta$,
this is the set of extended real numbers $u(0)^2$, where $u$ ranges over the continuous
functions $u : (\mathbb{R}/2\pi\mathbb{Z})^2 \to \mathbb{R}$ that are conditionally admissible
at level $\delta$. -/
def conditionalPointValues (δ : ℝ) : Set EReal :=
  (fun u : C(Torus, ℝ) ↦ (((u 0) ^ 2 : ℝ) : EReal)) '' {u | ConditionalAdmissible u δ}

/-- **Conditional supremum of the squared value at the origin.** For real $\delta$,
$\theta(\delta)$ is the supremum, taken in the extended reals $[-\infty, \infty]$, of the
conditional point values at $\delta$: the numbers $u(0)^2$ over all continuous
$u : \mathbb{T}^2 \to \mathbb{R}$ on the torus $\mathbb{T}^2 = (\mathbb{R}/2\pi\mathbb{Z})^2$
that are conditionally admissible at $\delta$, that is, of mean zero and in $H^2$ with gradient
energy $1$ and Laplace energy $\delta$.

The supremum may be $+\infty$, and it is $-\infty$ when no function is admissible. -/
def theta (δ : ℝ) : EReal := sSup (conditionalPointValues δ)

/-- **Frequency ratio.** For a continuous function
$u : (\mathbb{R}/2\pi\mathbb{Z})^2 \to \mathbb{R}$, the frequency ratio is the Laplacian energy
of $u$ divided by the gradient energy of $u$.

Applications assume positive gradient energy; when the gradient energy is $0$, the quotient is
taken to be $0$. -/
def frequencyRatio (u : C(Torus, ℝ)) : ℝ := laplaceEnergy u / gradientEnergy u

/-- **Logarithmic remainder.** For real $\delta$, the remainder is the extended real number
$R(\delta) = 4\pi\,\theta(\delta) - \log \delta - \log(1 + \log \delta)$, where $\theta(\delta)$
is the conditional supremum of $u(0)^2$ over the functions conditionally admissible at $\delta$.

Here $\log$ is the real logarithm with the conventions $\log 0 = 0$ and $\log x = \log |x|$ for
$x < 0$, so $R(\delta)$ is defined for every real $\delta$. -/
def remainder (δ : ℝ) : EReal :=
  ((4 * Real.pi : ℝ) : EReal) * theta δ - (Real.log δ : EReal) -
    (Real.log (1 + Real.log δ) : EReal)

/-- **Set of remainder values.** The set of extended real numbers $R(\delta)$ for all real
$\delta \ge 1$, where $R(\delta) = 4\pi\,\theta(\delta) - \log \delta - \log(1 + \log \delta)$
is the logarithmic remainder and $\theta(\delta)$ is the conditional supremum of $u(0)^2$ over
the functions conditionally admissible at $\delta$.

Every $\delta \ge 1$ is included, not only sufficiently large ratios. -/
def sharpRemainderValues : Set EReal := remainder '' Set.Ici 1

/-- **Sharp logarithmic remainder.** The sharp remainder is the supremum, in the extended reals
$[-\infty, \infty]$, of the remainders
$R(\delta) = 4\pi\,\theta(\delta) - \log \delta - \log(1 + \log \delta)$ over all real
$\delta \ge 1$, where $\theta(\delta)$ is the conditional supremum of $u(0)^2$ over the functions
conditionally admissible at $\delta$.

The definition does not assume that the supremum is finite or attained. -/
def sharpRemainderValue : EReal := sSup sharpRemainderValues

/-- **Uniform logarithmic remainder bound.** For a real constant $L$, the bound with constant $L$
holds when, for every continuous $u : \mathbb{T}^2 \to \mathbb{R}$ on the torus
$\mathbb{T}^2 = (\mathbb{R}/2\pi\mathbb{Z})^2$ that has mean zero and lies in $H^2$, has positive
gradient energy $E(u)$, and, writing $\Delta(u)$ for its Laplace energy, has frequency ratio
$\Lambda(u) = \Delta(u)/E(u) \ge 1$, every point $x$ of the torus satisfies
$u(x)^2 \le \frac{E(u)}{4\pi}\bigl(\log \Lambda(u) + \log(1 + \log \Lambda(u)) + L\bigr)$. -/
def UniformRemainderBound (L : ℝ) : Prop :=
  ∀ u : C(Torus, ℝ), IsZeroMeanH2 u → 0 < gradientEnergy u → 1 ≤ frequencyRatio u →
    ∀ x : Torus, (u x) ^ 2 ≤ gradientEnergy u / (4 * Real.pi) *
      (Real.log (frequencyRatio u) + Real.log (1 + Real.log (frequencyRatio u)) + L)

end TorusSobolev
