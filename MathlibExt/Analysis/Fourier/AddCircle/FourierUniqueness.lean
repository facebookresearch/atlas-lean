/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Fourier coefficients determine a continuous periodic function

For a period `T > 0`, the Fourier coefficients of a continuous function
`f : C(AddCircle T, ℂ)` determine `f`: if every coefficient vanishes, then
`f = 0`, and if two continuous functions have the same coefficients, they are
equal. In other words the coefficient map
`C(AddCircle T, ℂ) → (ℤ → ℂ)` is injective. The same holds on an interval
`[a, a + T]` for a continuous `f : ℝ → ℂ` with `f a = f (a + T)`, where the
coefficients are Mathlib's `fourierCoeffOn`.

The proof goes through `L²`: the Fourier monomials form a Hilbert basis
`fourierBasis` of `Lp ℂ 2 haarAddCircle`, and the `n`-th coordinate of
`fourierBasis.repr F` is exactly `fourierCoeff F n`
(`fourierBasis_repr`). A function in `L²` with all coefficients zero is
therefore zero, and a continuous function agreeing with it in `L²` is zero
by injectivity of `ContinuousMap.toLp` (Haar measure on the circle is an
open-pos measure). This route is independent of Fejér's theorem: it does
not use Cesàro means.

Provenance: these declarations are new corollaries of Mathlib's complete
Fourier basis and coefficient API. The contextual archived file
`v1/Atlas/IntroductionToFunctionalAnalysis/code/FourierSeries.lean` and its
Theorem (Fejér) target (April 22, 2021) formalize uniform convergence of
Cesàro means. The uniqueness statements proved here have no corresponding
v1 target or archived declaration.
-/

@[expose] public section

namespace MathlibExt.Analysis.Fourier.AddCircle.FourierUniqueness

open MeasureTheory Filter Topology

variable {T : ℝ} [hT : Fact (0 < T)]

/-- **Uniqueness of Fourier coefficients in L².** Let $T > 0$ and let $\mu$ be the Haar
probability measure on the circle $\mathbb{R}/T\mathbb{Z}$. If an element $F$ of
$L^2(\mathbb{R}/T\mathbb{Z}, \mu; \mathbb{C})$ has Fourier coefficients
$\hat F(n) = \int e^{-2\pi i n t / T} F(t)\,d\mu(t)$ equal to $0$ for every $n \in \mathbb{Z}$,
then $F = 0$ in $L^2(\mathbb{R}/T\mathbb{Z}, \mu; \mathbb{C})$. -/
theorem eq_zero_of_fourierCoeff_eq_zero_Lp
    {F : Lp ℂ 2 (AddCircle.haarAddCircle (T := T))}
    (h : ∀ n : ℤ, fourierCoeff F n = 0) :
    F = 0 := by
  have h0 : fourierBasis.repr F = 0 := by
    apply lp.ext
    funext n
    simp [fourierBasis_repr, h]
  have h1 := congr_arg ((@fourierBasis T hT).repr.symm) h0
  rwa [LinearIsometryEquiv.symm_apply_apply, map_zero] at h1

/-- **Uniqueness of Fourier coefficients for continuous functions.** Let $T > 0$ and let $\mu$
be the Haar probability measure on the circle $\mathbb{R}/T\mathbb{Z}$. If a continuous function
$f : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ has Fourier coefficients
$\hat f(n) = \int e^{-2\pi i n t / T} f(t)\,d\mu(t)$ equal to $0$ for every $n \in \mathbb{Z}$,
then $f = 0$. -/
theorem eq_zero_of_fourierCoeff_eq_zero
    {f : C(AddCircle T, ℂ)} (h : ∀ n : ℤ, fourierCoeff f n = 0) : f = 0 := by
  have hLp : ContinuousMap.toLp (E := ℂ) 2 (AddCircle.haarAddCircle (T := T)) ℂ f = 0 :=
    eq_zero_of_fourierCoeff_eq_zero_Lp fun n => by
      rw [fourierCoeff_toLp]
      exact h n
  have h2 : ContinuousMap.toLp (E := ℂ) 2 (AddCircle.haarAddCircle (T := T)) ℂ f =
      ContinuousMap.toLp (E := ℂ) 2 (AddCircle.haarAddCircle (T := T)) ℂ
        (0 : C(AddCircle T, ℂ)) := by
    rw [map_zero]
    exact hLp
  exact ContinuousMap.toLp_injective (AddCircle.haarAddCircle (T := T)) h2

/-- **Fourier coefficients determine a continuous function.** Let $T > 0$ and let $\mu$ be the
Haar probability measure on the circle $\mathbb{R}/T\mathbb{Z}$. For a function
$h : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ and $n \in \mathbb{Z}$, let
$\hat h(n) = \int e^{-2\pi i n t / T} h(t)\,d\mu(t)$ be the $n$-th Fourier coefficient of $h$. If
two continuous functions $f, g : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ satisfy
$\hat f(n) = \hat g(n)$ for every $n \in \mathbb{Z}$, then $f = g$. -/
theorem eq_of_fourierCoeff_eq
    {f g : C(AddCircle T, ℂ)} (h : ∀ n : ℤ, fourierCoeff f n = fourierCoeff g n) :
    f = g := by
  have hrepr : fourierBasis.repr
      (ContinuousMap.toLp (E := ℂ) 2 (AddCircle.haarAddCircle (T := T)) ℂ f) =
      fourierBasis.repr
        (ContinuousMap.toLp (E := ℂ) 2 (AddCircle.haarAddCircle (T := T)) ℂ g) := by
    apply lp.ext
    funext n
    rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_toLp, fourierCoeff_toLp]
    exact h n
  have hLp : ContinuousMap.toLp (E := ℂ) 2 (AddCircle.haarAddCircle (T := T)) ℂ f =
      ContinuousMap.toLp (E := ℂ) 2 (AddCircle.haarAddCircle (T := T)) ℂ g := by
    have h1 := congr_arg ((@fourierBasis T hT).repr.symm) hrepr
    rwa [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply] at h1
  exact ContinuousMap.toLp_injective (AddCircle.haarAddCircle (T := T)) hLp

/-- **Injectivity of the Fourier-coefficient map.** Let $T > 0$ and let $\mu$ be the Haar
probability measure on the circle $\mathbb{R}/T\mathbb{Z}$. The map sending a continuous function
$f : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ to its sequence of Fourier coefficients
$(\hat f(n))_{n \in \mathbb{Z}}$, where $\hat f(n) = \int e^{-2\pi i n t / T} f(t)\,d\mu(t)$, is
injective. -/
theorem fourierCoeff_injective :
    Function.Injective (fun f : C(AddCircle T, ℂ) => fun n : ℤ => fourierCoeff f n) :=
  fun _ _ h => eq_of_fourierCoeff_eq fun n => congr_fun h n

/-- **Uniqueness of Fourier coefficients on an interval.** Let $a, T \in \mathbb{R}$ with
$T > 0$, and let $f : \mathbb{R} \to \mathbb{C}$ be continuous with $f(a) = f(a + T)$. If the
Fourier coefficients of $f$ on $[a, a + T]$,

$$\hat f(n) = \frac{1}{T} \int_a^{a+T} e^{-2\pi i n x / T} f(x)\,dx,$$

are $0$ for every $n \in \mathbb{Z}$, then $f(x) = 0$ for every $x \in [a, a + T]$.

This is a corollary of uniqueness on the circle: the endpoint condition makes $f$ on
$[a, a + T]$ descend to a continuous function on $\mathbb{R}/T\mathbb{Z}$. -/
theorem eq_zero_of_fourierCoeffOn_eq_zero {a T : ℝ} (hT : 0 < T)
    {f : ℝ → ℂ} (hf : Continuous f) (hper : f a = f (a + T))
    (h : ∀ n : ℤ,
      fourierCoeffOn (lt_add_of_pos_right a hT) f n = 0) :
    ∀ x ∈ Set.Icc a (a + T), f x = 0 := by
  have hFact : Fact (0 < T) := ⟨hT⟩
  let F : C(AddCircle T, ℂ) :=
    ⟨AddCircle.liftIoc T a f,
      AddCircle.liftIoc_continuous hper hf.continuousOn⟩
  have hF : F = 0 := by
    apply eq_zero_of_fourierCoeff_eq_zero
    intro n
    have hcoeff : fourierCoeff (F : AddCircle T → ℂ) n = 0 := by
      have h1 : (F : AddCircle T → ℂ) = AddCircle.liftIoc T a f := rfl
      rw [h1, fourierCoeff_liftIoc_eq]
      exact h n
    exact hcoeff
  intro x hx
  have hright : f (a + T) = 0 := by
    have hmem : (a + T) ∈ Set.Ioc a (a + T) := ⟨lt_add_of_pos_right a hT, le_refl _⟩
    have h2 : F ((a + T : ℝ) : AddCircle T) = 0 := by rw [hF]; rfl
    rw [show F ((a + T : ℝ) : AddCircle T) = f (a + T) from
      AddCircle.liftIoc_coe_apply hmem] at h2
    exact h2
  rcases lt_or_eq_of_le hx.1 with hlt | heq
  · have hmem : x ∈ Set.Ioc a (a + T) := ⟨hlt, hx.2⟩
    have h2 : F (↑x : AddCircle T) = 0 := by rw [hF]; rfl
    rwa [show F (↑x : AddCircle T) = f x from AddCircle.liftIoc_coe_apply hmem] at h2
  · rw [← heq, hper]
    exact hright

end MathlibExt.Analysis.Fourier.AddCircle.FourierUniqueness
