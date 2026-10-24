/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# One-sided Laplace transform

This file defines the convergence predicate, the one-sided Laplace transform, and the
packaged `HasLaplace` relation, following Mathlib's `MellinConvergent` / `mellin` /
`HasMellin` pattern with the domain restricted to the open ray `Set.Ioi 0`.

This stage provides only the basic definitions; further API is out of scope.

## Main definitions

* `LaplaceConvergent`
* `laplace`
* `HasLaplace`
-/

@[expose] public section

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Convergence of the Laplace transform.** Let $E$ be a complex normed space,
$f : \mathbb{R} \to E$ and $s \in \mathbb{C}$. The Laplace transform of $f$ converges at $s$
when the function $t \mapsto e^{-st} f(t)$ is integrable on $(0, \infty)$ with respect to
Lebesgue measure.

Integrability here is absolute (Bochner) integrability, so conditionally convergent Laplace
integrals are not covered.

Source: ATLAS NumberTheoryI Definition 16.9 introduces the Laplace transform for real-valued
functions; here functions are complex-valued (or valued in a complex normed space), and the
source's real-valued case is covered by coercion. -/
def LaplaceConvergent (f : ℝ → E) (s : ℂ) : Prop :=
  IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • f t) (Set.Ioi 0)

/-- **The one-sided Laplace transform.** Let $E$ be a complex normed space,
$f : \mathbb{R} \to E$ and $s \in \mathbb{C}$. The Laplace transform of $f$ at $s$ is the Bochner
integral $\int_{(0, \infty)} e^{-st} f(t)\,dt \in E$.

It is defined for every $s$, with no convergence hypothesis: where $t \mapsto e^{-st} f(t)$ is not
integrable on $(0, \infty)$, or when $E$ is not complete, the integral is $0$ by convention.
Convergence of the Laplace transform is a separate notion. -/
noncomputable def laplace (f : ℝ → E) (s : ℂ) : E :=
  ∫ t : ℝ in Set.Ioi 0, Complex.exp (-s * (t : ℂ)) • f t

/-- **Laplace transform with a given value.** Let $E$ be a complex normed space,
$f : \mathbb{R} \to E$, $s \in \mathbb{C}$ and $v \in E$. Then $f$ has Laplace transform $v$ at
$s$ when the Laplace transform of $f$ converges at $s$, that is, $t \mapsto e^{-st} f(t)$ is
integrable on $(0, \infty)$, and the Bochner integral $\int_{(0, \infty)} e^{-st} f(t)\,dt$
equals $v$; as usual this integral is taken to be $0$ when $E$ is not complete. -/
def HasLaplace (f : ℝ → E) (s : ℂ) (v : E) : Prop :=
  LaplaceConvergent f s ∧ laplace f s = v
