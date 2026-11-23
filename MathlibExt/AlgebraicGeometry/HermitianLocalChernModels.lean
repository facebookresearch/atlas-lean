/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ArithmeticModelHermitianMetrics
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Local Chern currents of the actual model metric

Local weights are `-log` of the norm of an actual model-line frame at an
actual complex point. Plots preserve all regular functions. Every tested
ball has closure inside the original plot and every frame open; no boundary
extension of a local coefficient is assumed.

The weak `(1,1)` coefficient is computed by actual real Frechet derivatives
and integration. The convention is `d^c=(partial-bar_partial)/(2*pi*i)`;
in one complex variable this is the Laplacian divided by `2*pi`.
For mixed products, smooth densities use the complete signed permutation
expression, not an assigned Chern-measure oracle. Locally integrable weights
are actual differences of continuous plurisubharmonic functions equal to
the original metric weight. Smooth positive/negative approximations converge
uniformly on the fixed outer ball. Their compact-test limit defines the
signed local measure; its construction is deferred and not requested here.

Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 4.2--4.3, especially
printed pp119--120; the source explicitly distinguishes the denominator
`2*pi*i` from `4*pi*i`. Chern products use Bedford--Taylor/CLD as in Section3.6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HermitianLocalChernModels

open CategoryTheory CategoryTheory.Limits Opposite Filter MeasureTheory
open _root_.AlgebraicGeometry
open ArithmeticModelHermitianMetrics ComplexAnalytification
open scoped Topology Interval ContDiff CompactlySupported

abbrev Space (d : ℕ) := Fin d → ℂ

/-- Evaluation is defined on the actual regular-function domain. -/
def regularFunctionValue {d : ℕ} {Y : Over (Spec (.of ℂ))}
    (point : Space d → ComplexPoints Y.hom) (V : Y.left.Opens)
    (s : Γ(Y.left, V)) : Space d → ℂ := by
  classical
  exact fun z ↦ if h : (point z).Mem V then ComplexPoints.eval s (point z) h else 0

/-- A complex plot is tested by the actual regular functions of the scheme. -/
structure Plot (d : ℕ) (Y : Over (Spec (.of ℂ))) where
  domain : Set (Space d)
  isOpen : IsOpen domain
  point : Space d → ComplexPoints Y.hom
  continuous : ContinuousOn point domain
  holomorphic : ∀ (V : Y.left.Opens) (s : Γ(Y.left,V)),
    DifferentiableOn ℂ
      (regularFunctionValue point V s)
      (domain ∩ {z | (point z).Mem V})

/-- The coordinate directions are the actual standard vectors of complex space. -/
def direction {d : ℕ} (i : Fin d) (a : ℂ) : Space d := Pi.single i a

def holDerivative {d : ℕ} (i : Fin d) (f : Space d → ℂ) (z : Space d) : ℂ :=
  (fderiv ℝ f z (direction i 1) - Complex.I * fderiv ℝ f z (direction i Complex.I)) / 2

def antiDerivative {d : ℕ} (i : Fin d) (f : Space d → ℂ) (z : Space d) : ℂ :=
  (fderiv ℝ f z (direction i 1) + Complex.I * fderiv ℝ f z (direction i Complex.I)) / 2

/-- The Hessian is computed only from this actual real-valued function. -/
def hessian {d : ℕ} (u : Space d → ℝ) (z : Space d) : Fin d → Fin d → ℂ :=
  fun i j ↦ antiDerivative j (holDerivative i (fun w ↦ (u w : ℂ))) z

/-- Literal weak coefficient of `dd^c u` against a smooth compact test. -/
def weakCoefficient {d : ℕ} (u : Space d → ℝ) (i j : Fin d)
    (test : Space d → ℂ) : ℂ :=
  (Complex.I / (Real.pi : ℂ)) *
    ∫ z, (u z : ℂ) * antiDerivative j (holDerivative i test) z

/-- Smooth functions, rather than derivatives of a merely continuous metric. -/
structure SmoothPotentials (d : ℕ) where
  value : Fin d → Space d → ℝ
  smooth : ∀ i, ContDiff ℝ ∞ (value i)

/-- All signed row/column permutations occur in the mixed determinant. -/
def mixedHessian {d : ℕ} (S : SmoothPotentials d) (z : Space d) : ℂ :=
  ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
    (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
      (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) *
        ∏ i : Fin d, hessian (S.value i) z (σ i) (τ i)

/-- The mixed smooth Chern density in the standard real volume coordinates. -/
def mixedDensity {d : ℕ} (S : SmoothPotentials d) (z : Space d) : ℝ :=
  ((((2 / Real.pi) ^ d : ℝ) : ℂ) * mixedHessian S z).re

/-- Positivity is the actual Hermitian quadratic inequality of this Hessian. -/
def IsSemipositiveHessian {d : ℕ} (u : Space d → ℝ) (D : Set (Space d)) : Prop :=
  ∀ z ∈ D,
    (∀ i j, hessian u z i j = star (hessian u z j i)) ∧
      ∀ a : Space d,
        0 ≤ (∑ i : Fin d, ∑ j : Fin d, star (a i) * hessian u z i j * a j).re

/-- Continuous plurisubharmonicity has its literal complex-line submean test. -/
def IsPlurisubharmonic {d : ℕ} (u : Space d → ℝ) (D : Set (Space d)) : Prop :=
  ContinuousOn u D ∧ ∀ (z w : Space d) (r : ℝ), 0 < r →
    (∀ t : ℂ, ‖t‖ ≤ r → z + t • w ∈ D) →
    CircleIntegrable (fun t : ℂ ↦ u (z + t • w)) 0 r ∧
      u z ≤ (2 * Real.pi)⁻¹ *
        ∫ θ in 0..2 * Real.pi, u (z + circleMap 0 r θ • w)

variable {d : ℕ} {Y : Scheme.{0}} (L : Fin d → Y.Modules)
  (H : ∀ i, HermitianLine (L i))
  (U : Fin d → (complexScheme Y).left.Opens)
  (F : ∀ i, LocalFrame (complexLine (L i)) (U i))
  (P : Plot d (complexScheme Y))

/-- The weight is the negative log norm of the actual local frame germ. -/
def localWeight (i : Fin d) (z : Space d) : ℝ := by
  classical
  exact if h : (P.point z).Mem (U i) then
    -Real.log (((H i).metric.fibreNorm ((H i).dictionary.point (P.point z))).norm
      (ValuedLineFibres.evaluateSection _ _ _ (F i).sectionValue
        ((H i).dictionary.point (P.point z)) (by
          change (P.point z).schemePoint ∈ U i
          exact (ComplexPoints.schemePoint_mem_iff _ _).mpr h))) else 0

/-- The mother domain is fixed by the source plot and every actual frame open. -/
def motherDomain : Set (Space d) := P.domain ∩ {z | ∀ i, (P.point z).Mem (U i)}

/-- A test ball has an outer closure entirely inside that source domain. -/
structure TestChart where
  center : Space d
  innerRadius : ℝ
  outerRadius : ℝ
  positive : 0 < innerRadius
  ordered : innerRadius < outerRadius
  contained : Metric.closedBall center outerRadius ⊆ motherDomain U P

variable (C : TestChart U P)

def TestChart.inner : Set (Space d) := Metric.ball C.center C.innerRadius
def TestChart.outer : Set (Space d) := Metric.ball C.center C.outerRadius
def TestChart.outerClosure : Set (Space d) := Metric.closedBall C.center C.outerRadius

/-- The psh difference is tied at every source point to the original metric norm. -/
structure IntegrableSplitting where
  positivePart : Fin d → Space d → ℝ
  negativePart : Fin d → Space d → ℝ
  positivePSH : ∀ i, IsPlurisubharmonic (positivePart i) (motherDomain U P)
  negativePSH : ∀ i, IsPlurisubharmonic (negativePart i) (motherDomain U P)
  normalized : ∀ (i : Fin d) (z : Space d), z ∈ motherDomain U P →
    localWeight L H U F P i z = positivePart i z - negativePart i z

variable (I : IntegrableSplitting L H U F P)

/-- Actual smooth psh approximations on the outer ball, with uniform source limits. -/
structure SmoothApproximation where
  positivePart : ℕ → SmoothPotentials d
  negativePart : ℕ → SmoothPotentials d
  positiveHessian : ∀ n i, IsSemipositiveHessian ((positivePart n).value i) C.outer
  negativeHessian : ∀ n i, IsSemipositiveHessian ((negativePart n).value i) C.outer
  positiveLimit : ∀ (i : Fin d) (ε : ℝ), 0 < ε →
    ∀ᶠ n in atTop, ∀ z ∈ C.outerClosure,
      |(positivePart n).value i z - I.positivePart i z| < ε
  negativeLimit : ∀ (i : Fin d) (ε : ℝ), 0 < ε →
    ∀ᶠ n in atTop, ∀ z ∈ C.outerClosure,
      |(negativePart n).value i z - I.negativePart i z| < ε

variable (S : SmoothApproximation L H U F P C I)

/-- The signed approximating potential is computed from the two actual psh sequences. -/
def SmoothApproximation.signedPotentials (n : ℕ) : SmoothPotentials d where
  value i z := (S.positivePart n).value i z - (S.negativePart n).value i z
  smooth i := ((S.positivePart n).smooth i).sub ((S.negativePart n).smooth i)

/-- The local source action uses the literal smooth mixed densities. -/
def compactTestAction (f : C_c(Space d, ℝ)) : ℝ :=
  limUnder atTop (fun n ↦ ∫ z, f z *
    mixedDensity (SmoothApproximation.signedPotentials L H U F P C I S n) z)

/-- Positive and negative finite measures represent this exact signed source action.
Both are supported on the test ball. Their difference, not independently
assigned measure data, is fixed on every compactly supported continuous test. -/
structure ChernMeasureParts where
  positivePart : Measure (Space d)
  negativePart : Measure (Space d)
  [positiveFinite : IsFiniteMeasure positivePart]
  [negativeFinite : IsFiniteMeasure negativePart]
  positiveSupported : positivePart C.innerᶜ = 0
  negativeSupported : negativePart C.innerᶜ = 0
  converges : ∀ f : C_c(Space d, ℝ), tsupport f ⊆ C.inner →
    Tendsto (fun n ↦ ∫ z, f z *
      mixedDensity (SmoothApproximation.signedPotentials L H U F P C I S n) z)
      atTop (nhds (compactTestAction L H U F P C I S f))
  normalized : ∀ f : C_c(Space d, ℝ), tsupport f ⊆ C.inner →
    (∫ z, f z ∂positivePart) - (∫ z, f z ∂negativePart) =
      compactTestAction L H U F P C I S f

attribute [instance] ChernMeasureParts.positiveFinite ChernMeasureParts.negativeFinite

end MathlibExt.AlgebraicGeometry.HermitianLocalChernModels
