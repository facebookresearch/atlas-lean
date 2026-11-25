/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Batteries.Util.ProofWanted
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Fintype.Perm
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Probability.IdentDistribIndep

/-!
# Beardwood-Halton-Hammersley theorem and catalogue bounds: wishlist

The primary sources fix independent uniform points in the unit square. This module represents
the source constant as a real number: the infimum of all real values satisfying the generic
almost-sure BHH limit characterization. The source-facing closed theorem says that this real
value is the unique unit-square limit. It is an unproved `Prop`, not an axiom or proof of the
Beardwood-Halton-Hammersley theorem.

The generic common-law definitions expose all probability and i.i.d. quantifiers. The six
catalogue bounds concern the same real unit-square constant. The source reports these as known
results, not open conjectures; their missing Lean proofs are recorded with `theorem_wanted`.
-/

open scoped BigOperators ENNReal
open Filter MeasureTheory Metric Set

namespace MathlibExt.Probability.BeardwoodHaltonHammersleyConstantWanted

/-- **Points of the Euclidean plane.** A planar point is a point of the Euclidean plane
$\mathbb{R}^2$: a pair $(x, y)$ of real numbers, with the Euclidean norm
$\lVert (x, y) \rVert = \sqrt{x^2 + y^2}$. -/
abbrev PlanarPoint := EuclideanSpace ℝ (Fin 2)

local instance planarMeasurableSpace : MeasurableSpace PlanarPoint := borel PlanarPoint
local instance planarBorelSpace : BorelSpace PlanarPoint := ⟨rfl⟩

/-- **Cyclic successor.** For a natural number $n$ and an index $i$ with $0 \le i < n$, the cyclic
successor of $i$ is $(i + 1) \bmod n$; in particular the successor of $n - 1$ is $0$. For $n = 0$
there are no indices. -/
def cyclicNext {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- **Length of a closed tour.** For points $x_0, \dots, x_{n-1}$ in the Euclidean plane and a
permutation $\sigma$ of $\{0, \dots, n-1\}$, the tour length is
$\sum_{i=0}^{n-1} \lVert x_{\sigma(i)} - x_{\sigma(i+1 \bmod n)} \rVert$, the length of the closed
tour that visits $x_{\sigma(0)}, \dots, x_{\sigma(n-1)}$ in this order and returns to its start. -/
noncomputable def tourLength
    {n : ℕ} (points : Fin n → PlanarPoint) (order : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i : Fin n, dist (points (order i)) (points (order (cyclicNext i)))

/-- **Shortest tour length.** For points $x_0, \dots, x_{n-1}$ in the Euclidean plane, $L_n$ is
the minimum, over all permutations $\sigma$ of $\{0, \dots, n-1\}$, of the length of the closed
tour that visits $x_{\sigma(0)}, \dots, x_{\sigma(n-1)}$ in this order and returns to its start. -/
noncomputable def shortestTourLength {n : ℕ} (points : Fin n → PlanarPoint) : ℝ :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).inf'
    ⟨Equiv.refl (Fin n), Finset.mem_univ _⟩ (tourLength points)

/-- **Normalized tour length.** Let $\Omega$ be a set and let
$X_0, X_1, X_2, \dots \colon \Omega \to \mathbb{R}^2$ be functions. For an outcome
$\omega \in \Omega$ and $n \ge 1$, the normalized tour length is $L_n(\omega)/\sqrt{n}$, where
$L_n(\omega)$ is the length of a shortest closed tour through $X_0(\omega), \dots, X_{n-1}(\omega)$.
For $n = 0$ it is defined to be $0$.

The value at $n = 0$ does not affect limits as $n \to \infty$. -/
noncomputable def normalizedTourLength
    {Ω : Type*} (points : ℕ → Ω → PlanarPoint) (ω : Ω) (n : ℕ) : ℝ :=
  if 0 < n then
    shortestTourLength (fun i : Fin n => points i.val ω) / Real.sqrt n
  else
    0

/-- **I.i.d. points with a given law.** Let $\Omega$ be a measurable space with a measure
$\mathbb{P}$, let $X_0, X_1, X_2, \dots \colon \Omega \to \mathbb{R}^2$ be functions and let $\nu$
be a measure on the Borel sets of the plane. The $X_i$ are i.i.d. with law $\nu$ when
$\mathbb{P}$ and $\nu$ are probability measures, every $X_i$ is measurable, the $X_i$ are mutually
independent under $\mathbb{P}$, and the distribution of each $X_i$ under $\mathbb{P}$ is $\nu$. -/
def IsIIDWithLaw
    {Ω : Type*}
    (mΩ : MeasurableSpace Ω)
    (probability : Measure Ω)
    (points : ℕ → Ω → PlanarPoint)
    (law : Measure PlanarPoint) : Prop :=
  letI := mΩ
  IsProbabilityMeasure probability ∧
    IsProbabilityMeasure law ∧
    (∀ i, Measurable (points i)) ∧
    ProbabilityTheory.iIndepFun points probability ∧
    ∀ i, Measure.map (points i) probability = law

/-- **I.i.d. realization.** For a measure $\nu$ on the plane, an i.i.d. realization with law $\nu$
consists of a measurable space $\Omega$ with a measure $\mathbb{P}$, together with a sequence
$X_0, X_1, X_2, \dots \colon \Omega \to \mathbb{R}^2$ of points that is i.i.d. with common law
$\nu$ under $\mathbb{P}$. -/
structure IIDRealization (law : Measure PlanarPoint) where
  Ω : Type
  measurableSpace : MeasurableSpace Ω
  probability : Measure Ω
  points : ℕ → Ω → PlanarPoint
  isIID : IsIIDWithLaw measurableSpace probability points law

/-- **Almost-sure BHH limit.** Let $\Omega$ be a measurable space with a measure $\mu$, let
$X_0, X_1, X_2, \dots \colon \Omega \to \mathbb{R}^2$ be functions into the plane, and let $\beta$
be a real number. The sequence has BHH limit $\beta$ when, for $\mu$-almost every
$\omega \in \Omega$, the normalized tour length $L_n(\omega)/\sqrt{n}$ tends to $\beta$ as
$n \to \infty$, where $L_n(\omega)$ is the length of a shortest closed tour through
$X_0(\omega), \dots, X_{n-1}(\omega)$. -/
def HasBHHLimit
    {Ω : Type*}
    (mΩ : MeasurableSpace Ω)
    (probability : Measure Ω)
    (points : ℕ → Ω → PlanarPoint)
    (β : ℝ) : Prop :=
  letI := mΩ
  ∀ᵐ ω ∂probability,
    Tendsto (normalizedTourLength points ω) atTop (nhds β)

/-- **BHH constant of a law.** For a measure $\nu$ on the plane and a real number $\beta$, $\beta$
is a BHH constant for $\nu$ when an i.i.d. realization with law $\nu$ exists and every i.i.d.
realization with law $\nu$ has almost-sure BHH limit $\beta$: almost surely,
$L_n/\sqrt{n} \to \beta$, where $L_n$ is the length of a shortest closed tour through the first
$n$ points.

Requiring a realization to exist keeps the condition from holding vacuously. -/
def IsBHHConstantFor (law : Measure PlanarPoint) (β : ℝ) : Prop :=
  Nonempty (IIDRealization law) ∧
    ∀ realization : IIDRealization law,
      HasBHHLimit realization.measurableSpace realization.probability realization.points β

/-- **BHH limit values of a sampling law.** For a measure $\mu$ on the plane, the BHH limit values
of $\mu$ form the set of real numbers $\beta$ that are BHH limits for $\mu$. -/
def bhhLimitValues (law : Measure PlanarPoint) : Set ℝ :=
  {β | IsBHHConstantFor law β}

/-- **Membership in the set of BHH limit values.** For a measure $\nu$ on the plane and a real
number $\beta$, $\beta$ belongs to the set of BHH limit values of $\nu$ if and only if $\beta$ is a
BHH constant for $\nu$. -/
theorem mem_bhhLimitValues_iff (law : Measure PlanarPoint) (β : ℝ) :
    β ∈ bhhLimitValues law ↔ IsBHHConstantFor law β :=
  Iff.rfl

/-- **Unique BHH constant of a law.** A measure $\nu$ on the plane has a unique BHH constant when
there is exactly one real number $\beta$ that is a BHH constant for $\nu$. -/
def HasUniqueBHHConstantFor (law : Measure PlanarPoint) : Prop :=
  ∃! β : ℝ, IsBHHConstantFor law β

/--
**BHH constant of a sampling law.** For a measure $\mu$ on the plane, the BHH constant of $\mu$
is the infimum of the set of real numbers $\beta$ that are BHH limits for $\mu$. The infimum of a
set of reals that is empty or not bounded below is taken to be $0$.

No existence theorem is assumed: the definition does not presuppose that a BHH limit exists.
-/
noncomputable def bhhConstantFor (law : Measure PlanarPoint) : ℝ :=
  sInf (bhhLimitValues law)

/--
**The BHH constant equals the unique BHH limit.** Let $\mu$ be a measure on the plane and
$\beta$ a real number. If, for every real $\gamma$, $\gamma$ is a BHH limit for $\mu$ if and only
if $\gamma = \beta$, then the BHH constant of $\mu$ (the infimum of its BHH limits) equals $\beta$.

The hypothesis excludes the case with no BHH limit, where the infimum is $0$ by convention.
-/
theorem bhhConstantFor_eq_of_unique_characterization
    (law : Measure PlanarPoint) (β : ℝ)
    (h : ∀ γ : ℝ, IsBHHConstantFor law γ ↔ γ = β) :
    bhhConstantFor law = β := by
  have hset : bhhLimitValues law = {β} := by
    ext γ
    simpa [bhhLimitValues] using h γ
  rw [bhhConstantFor, hset, csInf_singleton]

/-- **Unit square.** The closed unit square $[0,1]^2$: the set of points of the Euclidean plane
both of whose coordinates lie in the interval $[0,1]$. -/
def unitSquare : Set PlanarPoint :=
  {point | ∀ coordinate, point coordinate ∈ Set.Icc (0 : ℝ) 1}

/-- **Uniform law on the unit square.** Lebesgue measure on the Euclidean plane restricted to the
closed unit square $[0,1]^2$. -/
noncomputable def unitSquareUniformLaw : Measure PlanarPoint :=
  volume.restrict unitSquare

/-- **Beardwood–Halton–Hammersley constant.** The Beardwood–Halton–Hammersley constant is the
BHH constant of the uniform law on the closed unit square $[0,1]^2$ (Lebesgue measure restricted
to $[0,1]^2$): the infimum of the set of real numbers $\beta$ such that i.i.d. samples with this
law exist and, for every such sample $X_1, X_2, \dots$, the length of the shortest closed tour
through $X_1, \dots, X_n$ divided by $\sqrt{n}$ tends to $\beta$ almost surely. The infimum of a
set of reals that is empty or not bounded below is taken to be $0$. -/
noncomputable def beardwoodHaltonHammersleyConstant : ℝ :=
  bhhConstantFor unitSquareUniformLaw

/-- **The notation $\beta_2$.** We write $\beta_2$ for the real-valued Beardwood–Halton–Hammersley
constant of the unit square. -/
noncomputable abbrev β₂ : ℝ := beardwoodHaltonHammersleyConstant

/-- **Notation C₁₂ for the BHH constant.** The constant $C_{12}$ is defined to be the
Beardwood–Halton–Hammersley constant $\beta_2$ for uniform points in the unit square; $C_{12}$ is
the name the source uses for it. -/
noncomputable abbrev C₁₂ : ℝ := β₂

/--
**Statement of the Beardwood–Halton–Hammersley theorem.** The proposition that the
Beardwood–Halton–Hammersley constant $\beta_2$ is a BHH constant for the uniform law on the closed
unit square $[0,1]^2$, and that every real number $\beta$ that is a BHH constant for this law equals
$\beta_2$. Here a real number $\beta$ is a BHH constant for a law $\mu$ on the plane when a
sequence $X_0, X_1, \dots$ of independent random points with common law $\mu$ exists on some
probability space, and for every such sequence, almost surely $L_n / \sqrt{n} \to \beta$ as
$n \to \infty$, where $L_n$ is the length of the shortest closed tour through $X_0, \dots, X_{n-1}$.
-/
def unitSquareBHHTheorem : Prop :=
  IsBHHConstantFor unitSquareUniformLaw β₂ ∧
    ∀ β : ℝ, IsBHHConstantFor unitSquareUniformLaw β → β = β₂

/--
**Statement of the Beardwood–Halton–Hammersley upper bound.** This is the proposition that the
Beardwood–Halton–Hammersley constant $\beta_2$ for uniform points in the unit square satisfies
$\beta_2 \le 0.92117$, the upper bound reported by Beardwood, Halton and Hammersley (1959).
-/
def bhh1959UpperBound : Prop :=
  β₂ ≤ (92117 : ℝ) / 100000

/-- **Statement of Steinerberger's upper bound.** The proposition that the
Beardwood–Halton–Hammersley constant $\beta_2$ satisfies
$\beta_2 \le 0.92117 - \frac{9}{16} \cdot 10^{-6}$. -/
def steinerberger2015ImprovedUpperBound : Prop :=
  β₂ ≤ (92117 : ℝ) / 100000 - (9 : ℝ) / 16 * (1 / 1000000)

/-- **Statement of the Yu–Carlsson upper bound.** This is the proposition that the real-valued
Beardwood–Halton–Hammersley constant $\beta_2$ of the unit square satisfies $\beta_2 < 0.90304$.

Source: [YC2023], strict computer-aided upper bound. -/
def yuCarlsson2023StrictUpperBound : Prop :=
  β₂ < (90304 : ℝ) / 100000

/--
**Statement of the Beardwood–Halton–Hammersley lower bound.** This is the proposition that the
Beardwood–Halton–Hammersley constant $\beta_2$ for uniform points in the unit square satisfies
$\beta_2 \ge 5/8 = 0.625$, the lower bound reported by Beardwood, Halton and Hammersley (1959).
-/
def bhh1959LowerBound : Prop :=
  (5 : ℝ) / 8 ≤ β₂

/--
**Statement of the corrected Steinerberger lower bound.** The proposition that the
Beardwood–Halton–Hammersley constant $\beta_2$ satisfies
$\frac{5}{8} + \frac{19}{10368} \le \beta_2$.

The bound is the exact rational $\frac{5}{8} + \frac{19}{10368}$, not a decimal approximation of it.
-/
def steinerberger2015CorrectedSymbolicLowerBound : Prop :=
  (5 : ℝ) / 8 + 19 / 10368 ≤ β₂

/-- **Statement of the Gaudio–Jaillet lower bound.** The proposition that the
Beardwood–Halton–Hammersley constant $\beta_2$ of the unit square is at least $0.6277$, that is,
$0.6277 \le \beta_2$. -/
def gaudioJaillet2020LowerBound : Prop :=
  (6277 : ℝ) / 10000 ≤ β₂

/-- **Beardwood–Halton–Hammersley theorem.** Let $\beta_2$ be the Beardwood–Halton–Hammersley
constant and, for points $X_0, X_1, \dots$ of the plane, let $L_n$ be the length of the shortest
closed tour through $X_0, \dots, X_{n-1}$. Then a sequence of independent random points
$X_0, X_1, \dots$, each uniformly distributed on the closed unit square $[0,1]^2$, exists on some
probability space; for every such sequence, almost surely $L_n / \sqrt{n} \to \beta_2$ as
$n \to \infty$; and $\beta_2$ is the only real number $\beta$ such that every such sequence almost
surely satisfies $L_n / \sqrt{n} \to \beta$.

Source: Beardwood, Halton and Hammersley (1959), quoted in Steinerberger (2015). -/
theorem_wanted unitSquareBHHTheorem_holds : unitSquareBHHTheorem

/--
**Beardwood–Halton–Hammersley upper bound.** The Beardwood–Halton–Hammersley constant $\beta_2$
for uniform points in the unit square satisfies $\beta_2 \le 0.92117$.

Source: Beardwood, Halton and Hammersley (1959), catalogue upper-bound row.
-/
theorem_wanted bhh1959UpperBound_holds : bhh1959UpperBound

/-- **Steinerberger's upper bound for the BHH constant.** The Beardwood–Halton–Hammersley constant
$\beta_2$ satisfies $\beta_2 \le 0.92117 - \frac{9}{16} \cdot 10^{-6}$.

Source: Steinerberger, New Bounds for the Traveling Salesman Constant (2015). -/
theorem_wanted steinerberger2015ImprovedUpperBound_holds :
    steinerberger2015ImprovedUpperBound

/-- **Yu–Carlsson upper bound on the BHH constant.** The real-valued Beardwood–Halton–Hammersley
constant $\beta_2$ of the unit square satisfies $\beta_2 < 0.90304$.

Source: Yu and Carlsson (2023), strict upper-bound row in the frozen catalogue. -/
theorem_wanted yuCarlsson2023StrictUpperBound_holds : yuCarlsson2023StrictUpperBound

/--
**Beardwood–Halton–Hammersley lower bound.** The Beardwood–Halton–Hammersley constant $\beta_2$
for uniform points in the unit square satisfies $\beta_2 \ge 5/8 = 0.625$.

Source: Beardwood, Halton and Hammersley (1959), catalogue lower-bound row.
-/
theorem_wanted bhh1959LowerBound_holds : bhh1959LowerBound

/-- **Gaudio–Jaillet corrected lower bound for the BHH constant.** The Beardwood–Halton–Hammersley
constant $\beta_2$ satisfies $\frac{5}{8} + \frac{19}{10368} \le \beta_2$.

Source: Gaudio and Jaillet (2020), correction of Steinerberger's lower coefficient. -/
theorem_wanted steinerberger2015CorrectedSymbolicLowerBound_holds :
    steinerberger2015CorrectedSymbolicLowerBound

/-- **Gaudio–Jaillet lower bound for the BHH constant.** The Beardwood–Halton–Hammersley
constant $\beta_2$ of the unit square satisfies $0.6277 \le \beta_2$.

Source: Gaudio and Jaillet, An improved lower bound for the Traveling Salesman constant. -/
theorem_wanted gaudioJaillet2020LowerBound_holds : gaudioJaillet2020LowerBound

end MathlibExt.Probability.BeardwoodHaltonHammersleyConstantWanted
