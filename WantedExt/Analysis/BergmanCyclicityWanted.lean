/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
AMR-022-8010: if f and 1/f are in the Bergman space A^2,
does it follow that Pf = {polynomial multiples of f} is dense in A^2?

Gap: the record also asks a generalization (to other spaces);
only the first part (A^2 cyclicity) is formalized here.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

namespace MathlibExt.Analysis.BergmanCyclicityWanted

/-! Source record `AMR-022-8010`. -/
open MeasureTheory

/-- **The open unit disc.** The set $\mathbb{D} = \{z \in \mathbb{C} : |z| < 1\}$. -/
def Disc : Set ℂ := {z | ‖z‖ < 1}

/-- **Bergman space $A^2$ of the unit disc.** A function $f : \mathbb{C} \to \mathbb{C}$ belongs to
the Bergman space $A^2$ when it is analytic on the open unit disc
$\mathbb{D} = \{z \in \mathbb{C} : |z| < 1\}$ and square-integrable on $\mathbb{D}$ with respect to
Lebesgue area measure $dA$: $f$ is almost everywhere strongly measurable on $\mathbb{D}$ and
$\int_{\mathbb{D}} |f|^2 \, dA < \infty$. -/
def Bergman (f : ℂ → ℂ) : Prop :=
  AnalyticOn ℂ f Disc ∧ MemLp f 2 (volume.restrict Disc)

/-- **Pointwise reciprocal.** For a function $f : \mathbb{C} \to \mathbb{C}$, the function
$z \mapsto f(z)^{-1}$, with the convention $0^{-1} = 0$ at the zeros of $f$. -/
noncomputable def Inv (f : ℂ → ℂ) : ℂ → ℂ := fun z => (f z)⁻¹

/-- **Density of polynomial multiples in $A^2$.** Write $\mathbb{D}$ for the open unit disc and
$dA$ for Lebesgue area measure on it. For a function $f : \mathbb{C} \to \mathbb{C}$, the statement
that the polynomial multiples of $f$ are dense in the Bergman space $A^2$: for every $g \in A^2$
and every $\varepsilon > 0$ there is a complex polynomial $p$ with
$\left(\int_{\mathbb{D}} |p f - g|^2 \, dA\right)^{1/2} < \varepsilon$. -/
def Dense (f : ℂ → ℂ) : Prop :=
  ∀ g : ℂ → ℂ, Bergman g → ∀ ε : ENNReal, 0 < ε →
    ∃ p : Polynomial ℂ, eLpNorm (fun z => p.eval z * f z - g z) 2 (volume.restrict Disc) < ε

/-- **Bergman cyclicity conjecture.** Write $\mathbb{D}$ for the open unit disc and $dA$ for
Lebesgue area measure on it. The statement that for every function $f : \mathbb{C} \to \mathbb{C}$
with no zeros in $\mathbb{D}$ such that $f$ and its pointwise reciprocal $1/f$ both belong to the
Bergman space $A^2$, the polynomial multiples of $f$ are dense in $A^2$: for every $g \in A^2$ and
every $\varepsilon > 0$ there is a complex polynomial $p$ with
$\left(\int_{\mathbb{D}} |p f - g|^2 \, dA\right)^{1/2} < \varepsilon$.

Source: record `AMR-022-8010`; the record's generalization to other spaces is not formalized. -/
def conjecture : Prop :=
  ∀ f : ℂ → ℂ, Bergman f → Bergman (Inv f) →
    (∀ z ∈ Disc, f z ≠ 0) → Dense f

/--
**Invertible non-cyclic functions in the Bergman space $A^2$.** Write $\mathbb{D}$ for the open
unit disc and $dA$ for Lebesgue area measure on it. There is a function
$f : \mathbb{C} \to \mathbb{C}$ with no zeros in $\mathbb{D}$ such that $f$ and its pointwise
reciprocal $1/f$ both belong to the Bergman space $A^2$, but the polynomial multiples of $f$ are
not dense in $A^2$: there are $g \in A^2$ and $\varepsilon > 0$ with
$\left(\int_{\mathbb{D}} |p f - g|^2 \, dA\right)^{1/2} \ge \varepsilon$ for every complex
polynomial $p$. That is, the Bergman cyclicity conjecture is false.

Borichev and Hedenmalm (J. Amer. Math. Soc. 10 (1997) 761-796) constructed invertible but
non-cyclic functions in the unweighted Bergman spaces $B^p(\mathbb{D})$, $0 < p < \infty$; the case
$p = 2$ gives such an $f$, as stated in Borichev-Hedenmalm-Volberg (arXiv:math/0304318).

Source: Alexander Borichev, Haakan Hedenmalm
and Alexander Volberg, Large Bergman spaces: invertibility, cyclicity, and subspaces of
arbitrary index, arXiv:math/0304318 (2003), https://arxiv.org/abs/math/0304318. Moved from
`OpenConjectures/Analysis/BergmanCyclicity`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Analysis.BergmanCyclicityWanted
