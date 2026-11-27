/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.Analysis.SpecialFunctions.Elliptic.Function

/-!
# Steps towards the argument principle for elliptic functions

This module collects three elementary steps in the proof that an elliptic function has as many
zeros as poles in a period parallelogram, counted with multiplicity:

* `Function.Periodic.deriv`, `Function.Periodic.logDeriv`, `PeriodPair.IsLatticePeriodic.deriv`,
  `PeriodPair.IsLatticePeriodic.logDeriv` and `PeriodPair.IsEllipticFunction.logDeriv`: the
  derivative and the logarithmic derivative `f' / f` of a periodic function are periodic with the
  same periods, so the logarithmic derivative of an elliptic function is elliptic.
* `parallelogramBoundaryIntegral`, the integral of a function along the four sides of the
  parallelogram with a vertex `z₀` and sides `ω₁`, `ω₂`, and
  `Function.Periodic.parallelogramBoundaryIntegral_eq_zero`: when `ω₁` and `ω₂` are periods, the
  integrals over opposite sides cancel and the boundary integral is `0`. The corollary
  `PeriodPair.IsLatticePeriodic.parallelogramBoundaryIntegral_eq_zero` specializes to the period
  parallelogram of a period pair.
* `Meromorphic.finite_closedParallelogram_inter_order_ne_zero`: a function that is meromorphic on
  `ℂ` with finite order at every point has only finitely many zeros and poles in a closed
  parallelogram, with the corollary
  `PeriodPair.IsEllipticFunction.finite_closedParallelogram_inter_order_ne_zero`.

The statements drop hypotheses that the source assumes but the proofs do not use; each docstring
says which.

## References

* J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021; author's version at
  <https://jmilne.org/math/Books/EC2.pdf>, Chapter III, §2, Proposition 2.1 and its proof,
  pp. 86–87.
-/

@[expose] public section

open MeasureTheory

/-! ### Derivatives of periodic functions -/

/-- **The derivative of a periodic function is periodic.** Let $\mathbb{K}$ be a nontrivially
normed field, $F$ a normed space over $\mathbb{K}$, $f : \mathbb{K} \to F$ and $c \in \mathbb{K}$.
If $f(x + c) = f(x)$ for all $x$, then $f'(x + c) = f'(x)$ for all $x$, where $f'$ is the
derivative of $f$ (taken to be $0$ where $f$ is not differentiable).

No differentiability hypothesis is needed: the translate $x \mapsto f(x + c)$ equals $f$, and the
derivative of a translate is the translate of the derivative. -/
theorem Function.Periodic.deriv {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f : 𝕜 → F} {c : 𝕜} (h : f.Periodic c) : (_root_.deriv f).Periodic c := by
  intro x
  rw [← deriv_comp_add_const]
  congr 1
  funext y
  exact h y

/-- **The logarithmic derivative of a periodic function is periodic.** Let $\mathbb{K}$ be a
nontrivially normed field, $\mathbb{K}'$ a normed $\mathbb{K}$-algebra that is a nontrivially
normed field, $f : \mathbb{K} \to \mathbb{K}'$ and $c \in \mathbb{K}$. If $f(x + c) = f(x)$ for all
$x$, then the logarithmic derivative $f'/f$ satisfies $(f'/f)(x + c) = (f'/f)(x)$ for all $x$.

No differentiability or nonvanishing hypothesis is needed (division by $0$ gives $0$). -/
theorem Function.Periodic.logDeriv {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {f : 𝕜 → 𝕜'} {c : 𝕜}
    (h : f.Periodic c) : (_root_.logDeriv f).Periodic c := by
  intro x
  rw [logDeriv_apply, logDeriv_apply, h.deriv x, h x]

namespace PeriodPair

/-- **The derivative of a lattice-periodic function is lattice-periodic.** Let $L$ be a period
pair with period lattice $\Lambda$ and let $f : \mathbb{C} \to \mathbb{C}$ satisfy
$f(z + \omega) = f(z)$ for all $z \in \mathbb{C}$ and $\omega \in \Lambda$. Then its derivative
satisfies $f'(z + \omega) = f'(z)$ for all $z \in \mathbb{C}$ and $\omega \in \Lambda$. -/
theorem IsLatticePeriodic.deriv {L : PeriodPair} {f : ℂ → ℂ} (hf : L.IsLatticePeriodic f) :
    L.IsLatticePeriodic (_root_.deriv f) :=
  fun ω ↦ (hf ω).deriv

/-- **The logarithmic derivative of a lattice-periodic function is lattice-periodic.** Let $L$ be
a period pair with period lattice $\Lambda$ and let $f : \mathbb{C} \to \mathbb{C}$ satisfy
$f(z + \omega) = f(z)$ for all $z \in \mathbb{C}$ and $\omega \in \Lambda$. Then the logarithmic
derivative $f'/f$ satisfies $(f'/f)(z + \omega) = (f'/f)(z)$ for all $z \in \mathbb{C}$ and
$\omega \in \Lambda$. -/
theorem IsLatticePeriodic.logDeriv {L : PeriodPair} {f : ℂ → ℂ} (hf : L.IsLatticePeriodic f) :
    L.IsLatticePeriodic (_root_.logDeriv f) :=
  fun ω ↦ (hf ω).logDeriv

/-- **The derivative of an elliptic function is elliptic.** Let $L$ be a period pair and let $f$
be an elliptic function for $L$. Then its derivative $f'$ is an elliptic function for $L$: it is
meromorphic on $\mathbb{C}$ and $f'(z + \omega) = f'(z)$ for every period $\omega$ of $L$. -/
theorem IsEllipticFunction.deriv {L : PeriodPair} {f : ℂ → ℂ} (hf : L.IsEllipticFunction f) :
    L.IsEllipticFunction (_root_.deriv f) :=
  ⟨hf.meromorphic.deriv, hf.periodic.deriv⟩

/-- **The logarithmic derivative of an elliptic function is elliptic.** Let $L$ be a period pair
and let $f$ be an elliptic function for $L$. Then its logarithmic derivative
$f'/f$ (Mathlib's `logDeriv f`, with $f'(z)/f(z) = 0$ where $f(z) = 0$) is an elliptic function for
$L$: it is meromorphic on $\mathbb{C}$ and $(f'/f)(z + \omega) = (f'/f)(z)$ for every period
$\omega$ of $L$.

Source: Milne, *Elliptic Curves*, 2nd ed., Chapter III, proof of Proposition 2.1, p. 87: "For (b)
one applies the residue theorem to $f'/f$, noting that this is again doubly periodic". The source
assumes that $f$ is not identically zero as a meromorphic function, that is, $f$ vanishes on no
punctured neighbourhood of any point (equivalently, its meromorphic order is finite at every
point). The proof does not use this, and the hypothesis is dropped: for instance, for $f = 0$ the
logarithmic derivative is the elliptic function $0$. -/
theorem IsEllipticFunction.logDeriv {L : PeriodPair} {f : ℂ → ℂ}
    (hf : L.IsEllipticFunction f) : L.IsEllipticFunction (_root_.logDeriv f) :=
  ⟨hf.meromorphic.logDeriv, hf.periodic.logDeriv⟩

end PeriodPair

/-! ### Boundary integrals over parallelograms -/

/-- **Boundary integral over a parallelogram.** For $g : \mathbb{C} \to \mathbb{C}$ and
$z_0, \omega_1, \omega_2 \in \mathbb{C}$, this is the integral of $g$ along the boundary of the
parallelogram with vertices $z_0$, $z_0 + \omega_1$, $z_0 + \omega_1 + \omega_2$, $z_0 + \omega_2$,
traversed in this order, with each side parametrized affinely by $t \in [0, 1]$:

$$\int_0^1 g(z_0 + t\omega_1)\,\omega_1\,dt +
\int_0^1 g(z_0 + \omega_1 + t\omega_2)\,\omega_2\,dt -
\int_0^1 g(z_0 + \omega_2 + t\omega_1)\,\omega_1\,dt -
\int_0^1 g(z_0 + t\omega_2)\,\omega_2\,dt.$$

Each integral is a Bochner interval integral, which is $0$ when the integrand is not integrable.
No relation between $\omega_1$ and $\omega_2$ is assumed; when
$\operatorname{Im}(\omega_2 / \omega_1) > 0$ the boundary is traversed counterclockwise. -/
noncomputable def parallelogramBoundaryIntegral (g : ℂ → ℂ) (z₀ ω₁ ω₂ : ℂ) : ℂ :=
  (∫ t in (0 : ℝ)..1, g (z₀ + t • ω₁) * ω₁) + (∫ t in (0 : ℝ)..1, g (z₀ + ω₁ + t • ω₂) * ω₂) -
    (∫ t in (0 : ℝ)..1, g (z₀ + ω₂ + t • ω₁) * ω₁) - (∫ t in (0 : ℝ)..1, g (z₀ + t • ω₂) * ω₂)

/-- **Opposite sides of a period parallelogram cancel.** Let $g : \mathbb{C} \to \mathbb{C}$ and
$z_0, \omega_1, \omega_2 \in \mathbb{C}$. If $g(z + \omega_1) = g(z)$ and $g(z + \omega_2) = g(z)$
for all $z$, then the boundary integral of $g$ over the parallelogram with vertex $z_0$ and sides
$\omega_1$, $\omega_2$ is $0$.

Source: Milne, *Elliptic Curves*, 2nd ed., Chapter III, proof of Proposition 2.1, p. 87: "Because
$f$ is periodic, the integrals over opposite sides of $D$ cancel, and so the integral is zero."
No integrability, meromorphy or linear independence of $\omega_1, \omega_2$ is needed: the
integrands over opposite sides agree pointwise. -/
theorem Function.Periodic.parallelogramBoundaryIntegral_eq_zero {g : ℂ → ℂ} {ω₁ ω₂ : ℂ}
    (h₁ : g.Periodic ω₁) (h₂ : g.Periodic ω₂) (z₀ : ℂ) :
    parallelogramBoundaryIntegral g z₀ ω₁ ω₂ = 0 := by
  have e₁ : (fun t : ℝ ↦ g (z₀ + ω₂ + t • ω₁) * ω₁) = fun t : ℝ ↦ g (z₀ + t • ω₁) * ω₁ := by
    funext t
    rw [add_right_comm, h₂]
  have e₂ : (fun t : ℝ ↦ g (z₀ + ω₁ + t • ω₂) * ω₂) = fun t : ℝ ↦ g (z₀ + t • ω₂) * ω₂ := by
    funext t
    rw [add_right_comm, h₁]
  rw [parallelogramBoundaryIntegral, e₁, e₂]
  ring

/-- **Opposite sides of the period parallelogram of a period pair cancel.** Let $L$ be a period
pair with periods $\omega_1, \omega_2$ and period lattice $\Lambda$, and let
$g : \mathbb{C} \to \mathbb{C}$ satisfy $g(z + \omega) = g(z)$ for all $z \in \mathbb{C}$ and
$\omega \in \Lambda$. Then for every $z_0 \in \mathbb{C}$ the boundary integral of $g$ over the
parallelogram with vertex $z_0$ and sides $\omega_1$, $\omega_2$ is $0$.

Source: Milne, *Elliptic Curves*, 2nd ed., Chapter III, proof of Proposition 2.1, p. 87: "Because
$f$ is periodic, the integrals over opposite sides of $D$ cancel, and so the integral is zero."
No integrability or meromorphy of $g$ is needed. -/
theorem PeriodPair.IsLatticePeriodic.parallelogramBoundaryIntegral_eq_zero {L : PeriodPair}
    {g : ℂ → ℂ} (hg : L.IsLatticePeriodic g) (z₀ : ℂ) :
    parallelogramBoundaryIntegral g z₀ L.ω₁ L.ω₂ = 0 :=
  (hg ⟨L.ω₁, L.ω₁_mem_lattice⟩).parallelogramBoundaryIntegral_eq_zero
    (hg ⟨L.ω₂, L.ω₂_mem_lattice⟩) z₀

/-! ### Zeros and poles in a closed parallelogram -/

/-- **Finitely many zeros and poles in a closed parallelogram.** Let $f : \mathbb{C} \to \mathbb{C}$
be meromorphic at every point of $\mathbb{C}$, with finite meromorphic order at every point, and let
$z_0, \omega_1, \omega_2 \in \mathbb{C}$. Then the set of points
$P = z_0 + t_1\omega_1 + t_2\omega_2$ with $t_1, t_2 \in [0, 1]$ at which the order of $f$ is
nonzero, that is, the set of zeros and poles of $f$ in the closed parallelogram with vertex $z_0$
and sides $\omega_1$, $\omega_2$, is finite.

Source: Milne, *Elliptic Curves*, 2nd ed., Chapter III, Proposition 2.1, pp. 86–87: the sums in
(b) and (c) run over the points of $D$ where $f$ has a zero or a pole, and "Each sum is finite."
The source takes $f$ elliptic for $\omega_1, \omega_2$; periodicity and linear independence of
$\omega_1, \omega_2$ are not used and are dropped. The finite-order hypothesis says that $f$
vanishes on no punctured neighbourhood of any point, that is, $f$ is not the zero meromorphic
function near any point; it is needed and is not implied by $f$ being nonzero at some point. A
function that vanishes on a punctured neighbourhood of every point, such as the zero function or
the indicator function of a lattice, has infinite, hence nonzero, order at every point. -/
theorem Meromorphic.finite_closedParallelogram_inter_order_ne_zero {f : ℂ → ℂ}
    (hf : Meromorphic f) (hord : ∀ z, meromorphicOrderAt f z ≠ ⊤) (z₀ ω₁ ω₂ : ℂ) :
    {P : ℂ | ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ 0 ≤ t₂ ∧ t₂ ≤ 1 ∧
      P = z₀ + t₁ • ω₁ + t₂ • ω₂ ∧ meromorphicOrderAt f P ≠ 0}.Finite := by
  set K : Set ℂ := (fun p : ℝ × ℝ ↦ z₀ + p.1 • ω₁ + p.2 • ω₂) ''
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
  have hKc : IsCompact K :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hU : MeromorphicOn f K := hf.meromorphicOn
  refine (hU.divisor_support_finite_of_subset hKc subset_rfl).subset ?_
  rintro P ⟨t₁, t₂, h1, h2, h3, h4, rfl, hP⟩
  have hPK : z₀ + t₁ • ω₁ + t₂ • ω₂ ∈ K := ⟨(t₁, t₂), ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, rfl⟩
  rw [Function.mem_support, MeromorphicOn.divisor_apply hU hPK]
  intro h0
  rcases WithTop.untop₀_eq_zero.mp h0 with h | h
  · exact hP h
  · exact hord _ h

/-- **Finitely many zeros and poles of an elliptic function in a closed period parallelogram.**
Let $L$ be a period pair with periods $\omega_1, \omega_2$, let $f$ be an elliptic function for
$L$ with finite meromorphic order at every point (that is, $f$ vanishes on no punctured
neighbourhood of any point: it is not the zero meromorphic function), and let
$z_0 \in \mathbb{C}$. Then the set of points $P = z_0 + t_1\omega_1 + t_2\omega_2$ with
$t_1, t_2 \in [0, 1]$ at which the order of $f$ is nonzero, that is, the set of zeros and poles of
$f$ in the closed period parallelogram with vertex $z_0$, is finite.

Source: Milne, *Elliptic Curves*, 2nd ed., Chapter III, Proposition 2.1, pp. 86–87: the sums in
(b) and (c) run over the points of $D$ where $f$ has a zero or a pole, and "Each sum is finite."
The source assumes $f$ not identically zero, as a meromorphic function; the finite-order
hypothesis is this condition. Periodicity is not used in the proof. -/
theorem PeriodPair.IsEllipticFunction.finite_closedParallelogram_inter_order_ne_zero
    {L : PeriodPair} {f : ℂ → ℂ} (hf : L.IsEllipticFunction f)
    (hord : ∀ z, meromorphicOrderAt f z ≠ ⊤) (z₀ : ℂ) :
    {P : ℂ | ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ 0 ≤ t₂ ∧ t₂ ≤ 1 ∧
      P = z₀ + t₁ • L.ω₁ + t₂ • L.ω₂ ∧ meromorphicOrderAt f P ≠ 0}.Finite :=
  hf.meromorphic.finite_closedParallelogram_inter_order_ne_zero hord z₀ L.ω₁ L.ω₂
