/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.TorusSobolev.Basic

@[expose] public section

noncomputable section

namespace TorusSobolev

/-- **Finite extremal parameters.** A finite extremal parameter is a real number $\mu$ with
$\mu < -1$ or $\mu > 0$.

The endpoints $\mu = -1$ and $\mu = \infty$ are not finite extremal parameters; the extremal
parameter domain adds them separately. -/
abbrev FiniteExtremalParameter := {μ : ℝ // μ < -1 ∨ 0 < μ}

/-- **Extremal parameters.** An extremal parameter is either a finite extremal parameter, that
is, a real number $\mu$ with $\mu < -1$ or $\mu > 0$, or one of two further parameters: the
first-shell parameter, standing for the endpoint $\mu = -1$, and the biharmonic parameter,
standing for the endpoint $\mu = \infty$.

Together these cover the parameter domain $(-\infty, -1] \cup (0, \infty]$, the two endpoints
being represented by limiting coefficient families rather than by values of $\mu$. -/
inductive ExtremalParameter where
  | finite (μ : FiniteExtremalParameter)
  | firstShell
  | biharmonic

/-- **Kernel-admissible extremal parameters.** Write $|k|^2 = k_1^2 + k_2^2$ for a frequency
$k \in \mathbb{Z}^2$. A finite extremal parameter $\mu$ is kernel-admissible when
$|k|^2 \neq 0$ and $1 + \mu |k|^2 \neq 0$ for every nonzero frequency $k$; the first-shell
parameter is always kernel-admissible; the biharmonic parameter is kernel-admissible when
$|k|^2 \neq 0$ for every nonzero frequency $k$.

These conditions make every reciprocal in the extremal coefficients well defined. -/
def KernelAdmissible : ExtremalParameter → Prop
  | .finite μ => ∀ k : Frequency, k ≠ 0 →
      frequencyWeight k ≠ 0 ∧ 1 + μ.1 * frequencyWeight k ≠ 0
  | .firstShell => True
  | .biharmonic => ∀ k : Frequency, k ≠ 0 → frequencyWeight k ≠ 0

/-- **Extremal coefficients.** Let $p$ be a kernel-admissible extremal parameter and write
$|k|^2 = k_1^2 + k_2^2$ for $k \in \mathbb{Z}^2$. The extremal coefficients $c_p(k)$, complex
numbers indexed by $k \in \mathbb{Z}^2$, are as follows. If $p$ is a finite parameter $\mu$, then
$c_p(0) = 0$ and $c_p(k) = 2\pi / (|k|^2 (1 + \mu |k|^2))$ for $k \neq 0$. If $p$ is the
first-shell parameter, then $c_p(k) = \pi$ when $|k|^2 = 1$ and $c_p(k) = 0$ otherwise. If $p$ is
the biharmonic parameter, then $c_p(0) = 0$ and $c_p(k) = 2\pi / |k|^4$ for $k \neq 0$.

The values are real and do not depend on the proof of admissibility. -/
def extremalCoefficient (p : ExtremalParameter) (_hp : KernelAdmissible p) (k : Frequency) : ℂ :=
  match p with
  | .finite μ => if k = 0 then 0 else
      ((2 * Real.pi / (frequencyWeight k * (1 + μ.1 * frequencyWeight k)) : ℝ) : ℂ)
  | .firstShell => if frequencyWeight k = 1 then (Real.pi : ℂ) else 0
  | .biharmonic => if k = 0 then 0 else ((2 * Real.pi / frequencyWeight k ^ 2 : ℝ) : ℂ)

/-- **Explicit extremals.** A continuous real function $u$ on the torus
$\mathbb{T} = (\mathbb{R}/2\pi\mathbb{Z})^2$ is an explicit extremal when there are a
kernel-admissible extremal parameter $p$ and a real number $a \neq 0$ such that the extremal
coefficients $c_p(k)$ are summable over $k \in \mathbb{Z}^2$, the Fourier coefficient
$\hat u(k) = \frac{1}{2\pi} \int_{[0, 2\pi]^2} u(x) e^{-i k \cdot x} \, dx$ equals $a \, c_p(k)$
for every $k \in \mathbb{Z}^2$, and
$u(x) = \frac{1}{2\pi} \sum_{k \in \mathbb{Z}^2} a \, c_p(k) \, e^{i k \cdot x}$ for every
$x \in \mathbb{T}$. -/
def IsExplicitExtremal (u : C(Torus, ℝ)) : Prop :=
  ∃ p : ExtremalParameter, ∃ hp : KernelAdmissible p, ∃ a : ℝ,
    a ≠ 0 ∧ Summable (extremalCoefficient p hp) ∧
      (∀ k : Frequency, fourierCoefficient u k = (a : ℂ) * extremalCoefficient p hp k) ∧
      ∀ x : Torus, (u x : ℂ) = (2 * Real.pi : ℂ)⁻¹ *
        ∑' k : Frequency, (a : ℂ) * extremalCoefficient p hp k *
          UnitAddTorus.mFourier k (unitRescaling x)

/-- **Same extremal orbit.** Two continuous real functions $u$ and $v$ on the torus
$\mathbb{T} = (\mathbb{R}/2\pi\mathbb{Z})^2$ lie in the same extremal orbit when there are a
real number $a \neq 0$ and a point $x_0 \in \mathbb{T}$ such that $v(x) = a \, u(x - x_0)$ for
every $x \in \mathbb{T}$. -/
def SameExtremalOrbit (u v : C(Torus, ℝ)) : Prop :=
  ∃ a : ℝ, a ≠ 0 ∧ ∃ x₀ : Torus, ∀ x : Torus, v x = a * u (x - x₀)

end TorusSobolev
