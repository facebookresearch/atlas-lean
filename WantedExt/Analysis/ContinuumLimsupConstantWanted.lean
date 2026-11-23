/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
AMR-022-2035: if `Γ` is a continuum receding to infinity, then
`limsup_{z → ∞ on Γ} log |f z| / log M(|z|) ≥ -A` for an absolute
constant `A`. Is `A = 1`?

Here `f` is entire (ambient context from Hayman) and `M(r)` is the
maximum modulus on the circle of radius `r`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.EReal.Basic
public import MathlibExt.Analysis.Complex.Wiman

@[expose] public section

namespace MathlibExt.Analysis.ContinuumLimsupConstantWanted

/-! Source record `AMR-022-2035`. -/
open Filter

/-- **Entire functions.** A function $f : \mathbb{C} \to \mathbb{C}$ is entire when it is complex
differentiable at every point of $\mathbb{C}$.

Source: the problem record gives $f$ entire only as ambient context from Hayman; it is taken here
as an explicit hypothesis. -/
def Entire (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f Set.univ

/- Maximum modulus `M(r)` is MathlibExt's `Complex.wimanMaximumModulus`,
the supremum of `‖f‖` on the sphere of radius `|r|`. -/
/-- **Continua receding to infinity.** A set $\Gamma \subseteq \mathbb{C}$ is a continuum receding
to infinity when it is closed, connected and unbounded.

Here a continuum is read as a closed connected set and receding to infinity as unbounded;
compactness is not required, since an unbounded set is never compact. -/
def RecedesToInf (Γ : Set ℂ) : Prop :=
  IsClosed Γ ∧ IsConnected Γ ∧ ¬Bornology.IsBounded Γ

/-- **Ratio of $\log |f|$ to the logarithm of the maximum modulus.** For a function
$f : \mathbb{C} \to \mathbb{C}$ and a point $z \in \mathbb{C}$, this is the extended real number
equal to $-\infty$ if $f(z) = 0$, and otherwise to the real number
$\log |f(z)| / \log M(f, |z|)$, where $M(f, r)$ is the Wiman maximum modulus of $f$, $\log 0$ is
taken to be $0$, and division by $0$ gives $0$. -/
noncomputable def Ratio (f : ℂ → ℂ) (z : ℂ) : EReal :=
  if f z = 0 then (⊥ : EReal)
  else ((Real.log ‖f z‖ / Real.log (Complex.wimanMaximumModulus f ‖z‖) : ℝ) : EReal)

/-- **Lower bound $-1$ for the log-modulus ratio along continua.** Write $M(f, r)$ for the Wiman
maximum modulus of a function $f : \mathbb{C} \to \mathbb{C}$ at radius $r$. This is the statement
that for every entire, transcendental function $f$ and every continuum $\Gamma$ receding to
infinity (a closed, connected, unbounded subset of $\mathbb{C}$), the limit superior, as
$|z| \to \infty$ with $z \in \Gamma$, of the extended real ratio $\log |f(z)| / \log M(f, |z|)$
is at least $-1$. Here the ratio is taken to be $-\infty$ where $f(z) = 0$, and $0$ where
$f(z) \ne 0$ and $\log M(f, |z|) = 0$.

Transcendence is the standing hypothesis of Hayman's problem; without it the zero function would
be a counterexample, its ratio being constantly $-\infty$.

Source: problem record AMR-022-2035. -/
noncomputable def conjecture : Prop :=
  ∀ f : ℂ → ℂ, Entire f → Complex.IsTranscendental f →
    ∀ Γ : Set ℂ, RecedesToInf Γ →
    (-1 : EReal) ≤ Filter.limsup (Ratio f) (Filter.cocompact ℂ ⊓ 𝓟 Γ)

/--
**Hayman–Kjellberg theorem on continua receding to infinity.** Write $M(f, r)$ for the Wiman
maximum modulus of a function $f : \mathbb{C} \to \mathbb{C}$ at radius $r$. For every entire,
transcendental function $f$ and every closed, connected, unbounded set
$\Gamma \subseteq \mathbb{C}$, the limit superior, as $|z| \to \infty$ with $z \in \Gamma$, of the
extended real ratio $\log |f(z)| / \log M(f, |z|)$ is at least $-1$. Here the ratio is taken to
be $-\infty$ where $f(z) = 0$, and $0$ where $f(z) \ne 0$ and $\log M(f, |z|) = 0$.

Hayman and Kjellberg (Studies in Pure Mathematics, Birkhauser 1983) proved that for entire $f$ and
every $K > 1$ all components of $\{z : \log |f(z)| + K \log M(f, |z|) < 0\}$ are bounded, so the
absolute constant in Hayman–Lingham Problem 2.35 is $A = 1$.

Source: A. Eremenko and J. K. Langley, Meromorphic functions of one complex
variable. A survey, arXiv:0801.0692 (2008), https://arxiv.org/abs/0801.0692; Walter K. Hayman
and Eleanor F. Lingham, Research Problems in Function Theory (New Edition), arXiv:1809.07200v2
(2018), https://arxiv.org/abs/1809.07200. Moved from
`OpenConjectures/Analysis/ContinuumLimsupConstant`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.ContinuumLimsupConstantWanted
