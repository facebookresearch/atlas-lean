/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

@[expose] public section

open MeasureTheory

open scoped MatrixGroups ENNReal Topology

noncomputable section

namespace MathlibExt.NumberTheory.SelbergSpectralGap

/-!
# The Selberg congruence spectral-gap constant

For a congruence subgroup `Γ ≤ SL(2, ℤ)`, an exceptional eigenvalue is an
eigenvalue `λ ∈ (0, 1/4)` of the hyperbolic Laplacian
`Δ = -y² (∂²/∂x² + ∂²/∂y²)` on `L²(Γ \ ℍ)`, below the continuous spectrum
threshold `1/4`. The gap parameter of `Γ` measures the deepest exceptional
eigenvalue: `θ(Γ) = sup {√(1/4 - λ) | λ exceptional} ∪ {0}`, which is
`√(max (0, 1/4 - λ₁(Γ)))` for the first nonzero eigenvalue `λ₁(Γ)` whenever
the spectrum below `1/4` is discrete. The Selberg constant (catalogue
constant C61a) is `C₆₁ = sup_Γ θ(Γ)` over congruence subgroups; it is `0`
exactly when no congruence subgroup has an exceptional eigenvalue, which
is Selberg's eigenvalue conjecture. This file proves the elementary
framework `0 ≤ C₆₁ ≤ 1/2` and that equivalence. Selberg's bound
`λ₁ ≥ 3/16` (`C₆₁ ≤ 1/4`) and the Kim--Sarnak bound `λ₁ ≥ 975/4096`
(`C₆₁ ≤ 7/64`) are registered as proof requests in the wanted file.

Model scope. Eigenvalues are modelled by smooth eigenfunctions on the
upper half plane that are `Γ`-invariant and square-integrable over a
fundamental domain assembled from finitely many translates of the
standard `SL(2, ℤ)` fundamental domain, with Mathlib's hyperbolic volume
on `UpperHalfPlane`. This captures the discrete `L²` spectrum. It does
not formalize the self-adjoint extension of the Laplacian, its full
spectrum including the continuous part `[1/4, ∞)`, discreteness of the
spectrum below `1/4`, independence of the `L²` condition from the chosen
coset covering, or that every spectral value below `1/4` comes from a
smooth `L²` eigenfunction in this sense. Since `θ(Γ)` depends only on
eigenvalues below `1/4`, the constant defined here is the catalogue
constant under those recorded identifications.

Source: Optimization Problems, constants/61a.md, frozen at
teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; SHA-256
`21fddd97d037cfa94393294ab112f709d5242cdc0ca11ef3bd62073408a80a8e`.
-/

/-- **Congruence subgroup of the modular group.** A subgroup $\Gamma$ of
$\mathrm{SL}(2, \mathbb{Z})$ is a congruence subgroup if there is a positive integer $N$
such that every $\gamma \in \mathrm{SL}(2, \mathbb{Z})$ whose entries are congruent modulo
$N$ to those of the identity matrix lies in $\Gamma$; that is, $\Gamma$ contains the
principal congruence subgroup of level $N$. -/
def IsCongruenceSubgroup (Γ : Subgroup SL(2, ℤ)) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ γ : SL(2, ℤ),
    (∀ i j, γ.1 i j ≡ (1 : Matrix (Fin 2) (Fin 2) ℤ) i j [ZMOD (N : ℤ)]) →
      γ ∈ Γ

/-- **The modular group is a congruence subgroup.** The full group
$\mathrm{SL}(2, \mathbb{Z})$, as a subgroup of itself, is a congruence subgroup.

It contains the principal congruence subgroup of level $1$, which is the whole group. -/
theorem isCongruenceSubgroup_top : IsCongruenceSubgroup ⊤ :=
  ⟨1, one_pos, fun γ _ => Subgroup.mem_top γ⟩

/-- **Zero extension from the upper half plane.** For a function $f$ from the upper half plane
to $\mathbb{C}$, its zero extension is the function from $\mathbb{C}$ to $\mathbb{C}$ that takes
the value $f(z)$ at every $z$ with $\operatorname{Im} z > 0$ and the value $0$ at every other
point.

It is used to read coordinate derivatives of $f$ in the interior. -/
def ext (f : UpperHalfPlane → ℂ) : ℂ → ℂ :=
  fun z => if hz : 0 < z.im then f ⟨z, hz⟩ else 0

/-- **Partial derivative in the real direction.** For a function
$f \colon \mathbb{H} \to \mathbb{C}$ and a point $z \in \mathbb{H}$, $\partial_x f(z)$ is the real
Fréchet derivative at $z$ of the zero extension of $f$ to $\mathbb{C}$, applied to the vector $1$.
When the zero extension is real-differentiable at $z$ this is the partial derivative of $f$ with
respect to $x = \operatorname{Re} z$; otherwise the value is $0$.

Real, not complex, differentiability is essential: with complex derivatives the two second
derivatives in the hyperbolic Laplacian would cancel by the Cauchy–Riemann equations, and the
Laplacian would vanish identically. -/
def partialRe (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  fderiv ℝ (ext f) z (1 : ℂ)

/-- **Partial derivative in the imaginary direction.** For a function
$f \colon \mathbb{H} \to \mathbb{C}$ and a point $z \in \mathbb{H}$, $\partial_y f(z)$ is the real
Fréchet derivative at $z$ of the zero extension of $f$ to $\mathbb{C}$, applied to the vector $i$.
When the zero extension is real-differentiable at $z$ this is the partial derivative of $f$ with
respect to $y = \operatorname{Im} z$; otherwise the value is $0$. -/
def partialIm (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  fderiv ℝ (ext f) z Complex.I

/-- **Hyperbolic Laplacian.** For a function $f$ from the upper half plane to $\mathbb{C}$ and a
point $z = x + iy$ of the upper half plane, the hyperbolic Laplacian of $f$ at $z$ is
$$\Delta f(z) = -y^2 \left(\partial_x \partial_x f(z) + \partial_y \partial_y f(z)\right),$$
where, for a function $g$ from the upper half plane to $\mathbb{C}$, $\partial_x g(z)$ and
$\partial_y g(z)$ are the real Fréchet derivatives at $z$ of the zero extension of $g$ to
$\mathbb{C}$, applied to the vectors $1$ and $i$ respectively (taken to be $0$ where that
extension is not real differentiable).

On smooth functions this agrees with the coordinate formula
$-y^2 (\partial^2 f / \partial x^2 + \partial^2 f / \partial y^2)$ at every interior point. -/
def hyperbolicLaplacian (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  -((z.im : ℂ) ^ 2) * (partialRe (partialRe f) z + partialIm (partialIm f) z)

private theorem ext_fderiv_const (c v : ℂ) (z : UpperHalfPlane) :
    fderiv ℝ (ext fun _ => c) z v = 0 := by
  have heq : ext (fun _ => c) =ᶠ[𝓝 (z : ℂ)] fun _ => c := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos]
      with w hw
    rw [ext, dif_pos hw]
  rw [heq.fderiv_eq]
  simp

theorem partialRe_const (c : ℂ) (z : UpperHalfPlane) :
    partialRe (fun _ => c) z = 0 :=
  ext_fderiv_const c 1 z

theorem partialIm_const (c : ℂ) (z : UpperHalfPlane) :
    partialIm (fun _ => c) z = 0 :=
  ext_fderiv_const c Complex.I z

/-- **The hyperbolic Laplacian kills constants.** For every complex number $c$ and every
point $z$ of the upper half plane, the hyperbolic Laplacian of the constant function with
value $c$ at $z$ is $0$. -/
theorem hyperbolicLaplacian_const (c : ℂ) (z : UpperHalfPlane) :
    hyperbolicLaplacian (fun _ => c) z = 0 := by
  have hRe : partialRe (fun _ => c) = fun _ => 0 :=
    funext (partialRe_const c)
  have hIm : partialIm (fun _ => c) = fun _ => 0 :=
    funext (partialIm_const c)
  rw [hyperbolicLaplacian, hRe, hIm, partialRe_const, partialIm_const]
  simp


/-- Near an interior point, the zero extension agrees with any extension
of `f`, so their real derivatives at that point agree. -/
private theorem ext_eventuallyEq {f : UpperHalfPlane → ℂ} {F : ℂ → ℂ}
    (hF : ∀ z : UpperHalfPlane, f z = F z) (z : UpperHalfPlane) :
    ext f =ᶠ[𝓝 (z : ℂ)] F := by
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos]
    with w hw
  rw [ext, dif_pos hw]
  exact hF ⟨w, hw⟩

private theorem partialRe_eq {f : UpperHalfPlane → ℂ} {F : ℂ → ℂ}
    (hF : ∀ z : UpperHalfPlane, f z = F z) (z : UpperHalfPlane) :
    partialRe f z = fderiv ℝ F z (1 : ℂ) := by
  rw [partialRe, (ext_eventuallyEq hF z).fderiv_eq]

private theorem partialIm_eq {f : UpperHalfPlane → ℂ} {F : ℂ → ℂ}
    (hF : ∀ z : UpperHalfPlane, f z = F z) (z : UpperHalfPlane) :
    partialIm f z = fderiv ℝ F z Complex.I := by
  rw [partialIm, (ext_eventuallyEq hF z).fderiv_eq]

private theorem fderiv_im_sq_apply (w v : ℂ) :
    fderiv ℝ (fun u : ℂ => ((u.im ^ 2 : ℝ) : ℂ)) w v =
      ((2 * w.im * v.im : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun u : ℂ => u.im) Complex.imCLM w :=
    Complex.imCLM.hasFDerivAt
  have h2 : HasFDerivAt (fun r : ℝ => r ^ 2)
      ((2 * w.im) • ContinuousLinearMap.id ℝ ℝ) w.im := by
    simpa using (hasFDerivAt_pow (𝕜 := ℝ) (𝔸 := ℝ) (x := w.im) 2)
  have h4 := Complex.ofRealCLM.hasFDerivAt.comp w (h2.comp w h1)
  rw [show (fun u : ℂ => ((u.im ^ 2 : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ (fun r : ℝ => r ^ 2) ∘ Complex.im from rfl,
    h4.fderiv]
  simp [mul_comm]

private theorem fderiv_two_im_apply (w v : ℂ) :
    fderiv ℝ (fun u : ℂ => ((2 * u.im : ℝ) : ℂ)) w v =
      ((2 * v.im : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun u : ℂ => u.im) Complex.imCLM w :=
    Complex.imCLM.hasFDerivAt
  have h2 : HasFDerivAt (fun r : ℝ => 2 * r)
      ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) w.im :=
    (hasFDerivAt_id w.im).const_mul 2
  have h4 := Complex.ofRealCLM.hasFDerivAt.comp w (h2.comp w h1)
  rw [show (fun u : ℂ => ((2 * u.im : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ (fun r : ℝ => 2 * r) ∘ Complex.im from rfl,
    h4.fderiv]
  simp

/-- **Hyperbolic Laplacian of the squared imaginary part.** Let $f$ be the function on the upper
half plane given by $f(u) = (\operatorname{Im} u)^2$, viewed as a complex number. Then for
every point $z$ of the upper half plane the hyperbolic Laplacian of $f$ at $z$ equals
$-2 (\operatorname{Im} z)^2$.

This is a non-holomorphic check: the value is not zero, whereas with complex derivatives the
computation would collapse by Cauchy--Riemann. -/
theorem hyperbolicLaplacian_im_sq (z : UpperHalfPlane) :
    hyperbolicLaplacian (fun u : UpperHalfPlane => (((u : ℂ).im ^ 2 : ℝ) : ℂ)) z =
      -2 * (((z : ℂ).im ^ 2 : ℝ) : ℂ) := by
  have hRe : partialRe (fun u : UpperHalfPlane => (((u : ℂ).im ^ 2 : ℝ) : ℂ)) =
      fun _ => 0 := by
    funext u
    rw [partialRe_eq (F := fun w : ℂ => ((w.im ^ 2 : ℝ) : ℂ)) (fun _ => rfl),
      fderiv_im_sq_apply]
    simp
  have hIm : partialIm (fun u : UpperHalfPlane => (((u : ℂ).im ^ 2 : ℝ) : ℂ)) =
      fun u : UpperHalfPlane => ((2 * (u : ℂ).im : ℝ) : ℂ) := by
    funext u
    rw [partialIm_eq (F := fun w : ℂ => ((w.im ^ 2 : ℝ) : ℂ)) (fun _ => rfl),
      fderiv_im_sq_apply]
    simp
  have hImIm :
      partialIm (fun u : UpperHalfPlane => ((2 * (u : ℂ).im : ℝ) : ℂ)) z = 2 := by
    rw [partialIm_eq (F := fun w : ℂ => ((2 * w.im : ℝ) : ℂ)) (fun _ => rfl),
      fderiv_two_im_apply]
    simp
  rw [hyperbolicLaplacian, hRe, hIm, partialRe_const, hImIm]
  have hzim : ((z : ℂ).im : ℂ) = (z.im : ℂ) := rfl
  rw [← hzim]
  push_cast
  ring

/-- **Twice continuously differentiable functions on the upper half-plane.** A function
$f \colon \mathbb{H} \to \mathbb{C}$ is smooth (of order two) when it is the restriction of a
function $F \colon \mathbb{C} \to \mathbb{C}$ that is twice continuously differentiable, in the real
sense, on the open set $\{z \in \mathbb{C} : \operatorname{Im} z > 0\}$.

Differentiability is real, not complex: eigenfunctions of the Laplacian need not be holomorphic. -/
def IsSmooth (f : UpperHalfPlane → ℂ) : Prop :=
  ∃ F : ℂ → ℂ, ContDiffOn ℝ 2 F {z | 0 < z.im} ∧ ∀ z : UpperHalfPlane, f z = F z

/-- **Standard fundamental domain of the modular group.** The standard fundamental domain for
$\mathrm{SL}(2, \mathbb{Z})$ is the set of points $z$ of the upper half plane with
$|\operatorname{Re} z| \le 1/2$ and $|z| \ge 1$. -/
def fundamentalDomain : Set UpperHalfPlane :=
  {z | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖(z : ℂ)‖}

/-- **Finite coset covers of the modular group.** A finite set
$s \subseteq \mathrm{SL}(2, \mathbb{Z})$ covers $\mathrm{SL}(2, \mathbb{Z})$ by cosets of a subgroup
$\Gamma$ when every $g \in \mathrm{SL}(2, \mathbb{Z})$ can be written as $g = \gamma a$ with
$\gamma \in \Gamma$ and $a \in s$, that is, when the cosets $\Gamma a$ with $a \in s$ cover
$\mathrm{SL}(2, \mathbb{Z})$. The elements of $s$ need not lie in distinct cosets. -/
def IsCosetCover (Γ : Subgroup SL(2, ℤ)) (s : Finset SL(2, ℤ)) : Prop :=
  ∀ g : SL(2, ℤ), ∃ a ∈ s, ∃ γ ∈ Γ, g = γ * a

/-- **Square-integrable functions on a modular quotient.** For a subgroup $\Gamma$ of
$\mathrm{SL}(2, \mathbb{Z})$, a function $f \colon \mathbb{H} \to \mathbb{C}$ is
square-integrable on $\Gamma \backslash \mathbb{H}$ when there is a finite set
$s \subseteq \mathrm{SL}(2, \mathbb{Z})$ whose cosets $\Gamma a$, $a \in s$, cover
$\mathrm{SL}(2, \mathbb{Z})$, such that

$$\int_{U} |f(z)|^2 \, d\mu(z) < \infty, \qquad U = \bigcup_{a \in s} a \cdot \mathcal{F},$$

where $\mathcal{F} = \{z \in \mathbb{H} : |\operatorname{Re} z| \le 1/2,\ |z| \ge 1\}$ is the
standard fundamental domain of $\mathrm{SL}(2, \mathbb{Z})$, $a \cdot \mathcal{F}$ is its image
under the Möbius action of $a$, and $\mu$ is the hyperbolic area measure $dx \, dy / y^2$ on
$\mathbb{H}$. -/
def IsL2Quotient (Γ : Subgroup SL(2, ℤ)) (f : UpperHalfPlane → ℂ) : Prop :=
  ∃ s : Finset SL(2, ℤ), IsCosetCover Γ s ∧
    (∫⁻ z in ⋃ a ∈ (s : Set SL(2, ℤ)), (fun z => a • z) '' fundamentalDomain,
      ‖f z‖ₑ ^ 2) < ∞

/-- **Eigenvalues of the hyperbolic Laplacian on a modular quotient.** Let $\Gamma$ be a subgroup
of $\mathrm{SL}(2, \mathbb{Z})$. A real number $\lambda$ is an eigenvalue of the hyperbolic
Laplacian $\Delta$ for $\Gamma$ when there is a function $f \colon \mathbb{H} \to \mathbb{C}$ on
the upper half plane $\mathbb{H}$ such that $f$ is not identically zero, $f$ is the restriction of
a function on $\mathbb{C}$ that is twice continuously differentiable in the real sense on the
upper half plane, $f(\gamma z) = f(z)$ for every $\gamma \in \Gamma$ and every $z \in \mathbb{H}$
(Möbius action), $f$ is square-integrable on $\Gamma \backslash \mathbb{H}$, and
$\Delta f(z) = \lambda f(z)$ for every $z \in \mathbb{H}$. -/
def IsEigenvalue (Γ : Subgroup SL(2, ℤ)) (lam : ℝ) : Prop :=
  ∃ f : UpperHalfPlane → ℂ, f ≠ 0 ∧ IsSmooth f ∧
    (∀ γ : SL(2, ℤ), γ ∈ Γ → ∀ z : UpperHalfPlane, f (γ • z) = f z) ∧
    IsL2Quotient Γ f ∧
    ∀ z : UpperHalfPlane, hyperbolicLaplacian f z = (lam : ℂ) * f z

/-- **Gap contributions of a subgroup of the modular group.** For a subgroup $\Gamma$ of
$\mathrm{SL}(2, \mathbb{Z})$, the set of gap contributions of $\Gamma$ is the set of real
numbers consisting of $0$ together with $\sqrt{1/4 - \lambda}$ for every real eigenvalue
$\lambda$ of the hyperbolic Laplacian for $\Gamma$ with $0 < \lambda < 1/4$ (an exceptional
eigenvalue). -/
def exceptionalGaps (Γ : Subgroup SL(2, ℤ)) : Set ℝ :=
  {0} ∪ {y | ∃ lam : ℝ, IsEigenvalue Γ lam ∧ 0 < lam ∧ lam < 1 / 4 ∧
    y = Real.sqrt (1 / 4 - lam)}

/-- **Gap parameter of a subgroup of the modular group.** For a subgroup $\Gamma$ of
$\mathrm{SL}(2, \mathbb{Z})$, the gap parameter $\theta(\Gamma)$ is the supremum of the set of
gap contributions of $\Gamma$: the number $0$ together with $\sqrt{1/4 - \lambda}$ for every
real eigenvalue $\lambda$ of the hyperbolic Laplacian for $\Gamma$ with $0 < \lambda < 1/4$. -/
noncomputable def exceptionalGap (Γ : Subgroup SL(2, ℤ)) : ℝ :=
  sSup (exceptionalGaps Γ)

/-- **Selberg's congruence spectral-gap constant.** Selberg's constant $C_{61}$ is the supremum of
the gap parameters $\theta(\Gamma)$ over all congruence subgroups $\Gamma$ of
$\mathrm{SL}(2, \mathbb{Z})$, where $\theta(\Gamma)$ is the supremum of $0$ and of the numbers
$\sqrt{1/4 - \lambda}$ for the eigenvalues $\lambda$ of $\Gamma$ with $0 < \lambda < 1/4$. -/
noncomputable def selbergConstant : ℝ :=
  sSup {y | ∃ Γ : Subgroup SL(2, ℤ), IsCongruenceSubgroup Γ ∧
    y = exceptionalGap Γ}

/-- **Selberg's eigenvalue conjecture.** No congruence subgroup $\Gamma$ of
$\mathrm{SL}(2, \mathbb{Z})$ has an eigenvalue $\lambda$ with $0 < \lambda < 1/4$: for every
congruence subgroup $\Gamma$ and every eigenvalue $\lambda$ of $\Gamma$, either $\lambda \le 0$ or
$\lambda \ge 1/4$.

Here eigenvalues are realized by smooth square-integrable eigenfunctions, which captures the
discrete spectrum of the hyperbolic Laplacian. -/
def SelbergEigenvalueConjecture : Prop :=
  ∀ Γ : Subgroup SL(2, ℤ), IsCongruenceSubgroup Γ → ∀ lam : ℝ,
    IsEigenvalue Γ lam → ¬ (0 < lam ∧ lam < 1 / 4)

private theorem sqrt_quarter : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem le_half_of_mem_exceptionalGaps {Γ : Subgroup SL(2, ℤ)} {y : ℝ}
    (hy : y ∈ exceptionalGaps Γ) : y ≤ 1 / 2 := by
  rcases hy with rfl | ⟨lam, _hlam, hpos, hlt, rfl⟩
  · norm_num
  · calc
      Real.sqrt (1 / 4 - lam) ≤ Real.sqrt (1 / 4 : ℝ) := by
        apply Real.sqrt_le_sqrt
        linarith
      _ = 1 / 2 := sqrt_quarter

theorem exceptionalGaps_bddAbove (Γ : Subgroup SL(2, ℤ)) :
    BddAbove (exceptionalGaps Γ) :=
  ⟨1 / 2, fun _y hy => le_half_of_mem_exceptionalGaps hy⟩

theorem exceptionalGaps_nonempty (Γ : Subgroup SL(2, ℤ)) :
    (exceptionalGaps Γ).Nonempty :=
  ⟨0, Or.inl rfl⟩

theorem zero_le_exceptionalGap (Γ : Subgroup SL(2, ℤ)) :
    0 ≤ exceptionalGap Γ :=
  le_csSup (exceptionalGaps_bddAbove Γ) (Or.inl rfl)

theorem exceptionalGap_le_half (Γ : Subgroup SL(2, ℤ)) :
    exceptionalGap Γ ≤ 1 / 2 := by
  apply csSup_le (exceptionalGaps_nonempty Γ)
  intro y hy
  exact le_half_of_mem_exceptionalGaps hy

/-- **Exceptional eigenvalues bound the gap parameter.** Let $\Gamma$ be a subgroup of
$\mathrm{SL}(2, \mathbb{Z})$ and let $\lambda$ be a real eigenvalue of the hyperbolic
Laplacian on $L^2(\Gamma \backslash \mathbb{H})$ with $0 < \lambda < 1/4$. Then
$\sqrt{1/4 - \lambda}$ is at most the gap parameter $\theta(\Gamma)$ of $\Gamma$. -/
theorem sqrt_le_exceptionalGap {Γ : Subgroup SL(2, ℤ)} {lam : ℝ}
    (hlam : IsEigenvalue Γ lam) (hpos : 0 < lam) (hlt : lam < 1 / 4) :
    Real.sqrt (1 / 4 - lam) ≤ exceptionalGap Γ :=
  le_csSup (exceptionalGaps_bddAbove Γ) (Or.inr ⟨lam, hlam, hpos, hlt, rfl⟩)

theorem selbergGaps_bddAbove :
    BddAbove {y | ∃ Γ : Subgroup SL(2, ℤ), IsCongruenceSubgroup Γ ∧
      y = exceptionalGap Γ} := by
  refine ⟨1 / 2, ?_⟩
  rintro y ⟨Γ, _hΓ, rfl⟩
  exact exceptionalGap_le_half Γ

theorem selbergGaps_nonempty :
    {y | ∃ Γ : Subgroup SL(2, ℤ), IsCongruenceSubgroup Γ ∧
      y = exceptionalGap Γ}.Nonempty :=
  ⟨exceptionalGap ⊤, ⊤, isCongruenceSubgroup_top, rfl⟩

/-- **Congruence gaps are bounded by Selberg's constant.** For every congruence subgroup
$\Gamma$ of $\mathrm{SL}(2, \mathbb{Z})$, the gap parameter $\theta(\Gamma)$ is at most the
Selberg constant $C_{61}$. -/
theorem exceptionalGap_le_selbergConstant {Γ : Subgroup SL(2, ℤ)}
    (hΓ : IsCongruenceSubgroup Γ) : exceptionalGap Γ ≤ selbergConstant :=
  le_csSup selbergGaps_bddAbove ⟨Γ, hΓ, rfl⟩

theorem zero_le_selbergConstant : 0 ≤ selbergConstant :=
  (zero_le_exceptionalGap ⊤).trans
    (exceptionalGap_le_selbergConstant isCongruenceSubgroup_top)

/-- **Selberg's constant is at most one half.** Selberg's constant $C_{61}$ satisfies
$C_{61} \le 1/2$.

This elementary bound follows directly from the definition. -/
theorem selbergConstant_le_half : selbergConstant ≤ 1 / 2 := by
  apply csSup_le selbergGaps_nonempty
  rintro y ⟨Γ, _hΓ, rfl⟩
  exact exceptionalGap_le_half Γ

/-- **Exceptional eigenvalues bound Selberg's constant.** Let $\Gamma$ be a congruence
subgroup of $\mathrm{SL}(2, \mathbb{Z})$ and let $\lambda$ be a real eigenvalue of the
hyperbolic Laplacian on $L^2(\Gamma \backslash \mathbb{H})$ with $0 < \lambda < 1/4$.
Then $\sqrt{1/4 - \lambda}$ is at most Selberg's constant $C_{61}$. -/
theorem sqrt_le_selbergConstant {Γ : Subgroup SL(2, ℤ)}
    (hΓ : IsCongruenceSubgroup Γ) {lam : ℝ} (hlam : IsEigenvalue Γ lam)
    (hpos : 0 < lam) (hlt : lam < 1 / 4) :
    Real.sqrt (1 / 4 - lam) ≤ selbergConstant :=
  (sqrt_le_exceptionalGap hlam hpos hlt).trans
    (exceptionalGap_le_selbergConstant hΓ)

/-- **Selberg's constant vanishes exactly under Selberg's eigenvalue conjecture.** Selberg's
constant $C_{61}$ equals $0$ if and only if Selberg's eigenvalue conjecture holds, that is, if and
only if no congruence subgroup of $\mathrm{SL}(2, \mathbb{Z})$ has an eigenvalue $\lambda$ with
$0 < \lambda < 1/4$. -/
theorem selbergConstant_eq_zero_iff :
    selbergConstant = 0 ↔ SelbergEigenvalueConjecture := by
  constructor
  · intro hC Γ hΓ lam hlam hlt
    have h1 := sqrt_le_selbergConstant hΓ hlam hlt.1 hlt.2
    rw [hC] at h1
    have h2 : (0 : ℝ) < Real.sqrt (1 / 4 - lam) := by
      apply Real.sqrt_pos.mpr
      linarith
    linarith
  · intro hconj
    apply le_antisymm _ zero_le_selbergConstant
    apply csSup_le selbergGaps_nonempty
    rintro y ⟨Γ, hΓ, rfl⟩
    apply csSup_le (exceptionalGaps_nonempty Γ)
    intro t ht
    rcases ht with rfl | ⟨lam, hlam, hpos, hlt, rfl⟩
    · exact le_refl 0
    · exact absurd ⟨hpos, hlt⟩ (hconj Γ hΓ lam hlam)

end MathlibExt.NumberTheory.SelbergSpectralGap

end
