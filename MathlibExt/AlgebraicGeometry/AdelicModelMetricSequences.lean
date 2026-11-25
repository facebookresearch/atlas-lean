/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AdelicArithmeticModelFrames
public import MathlibExt.AlgebraicGeometry.BoundaryMetricCompletionModels

/-!
# Model-compatible adelic metric completion

Each approximation is a line on one actual common arithmetic model.
Its norms at every nonarchimedean place are the fixed integral-frame
coordinate norms; archimedean metrics use the same actual global line.
The sequence uses one arithmetic base and the actual boundary Cauchy
relation. Completion is the image of these model sequences in the
already computed boundary metric quotient, not an arbitrary real space.

Modelled on Yuan--Zhang, arXiv:2105.13587v9, Sections 2.1--2.2 and A.5.
The completion is the fixed-gauge completion of `BoundaryMetricCompletionModels`, not
Yuan--Zhang's boundary topology: their adelic line bundles and positivity notions are not
claimed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AdelicModelMetricSequences

open CategoryTheory _root_.AlgebraicGeometry
open PlacewiseMetrizedLineModels CoherentCurveLinearSeries
open AdelicArithmeticModelFrames BoundaryMetricCompletionModels

variable {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
  {L : X.left.Modules}

/-- A genuine all-place metric from one common arithmetic line model. -/
structure ModelMetric where
  model : ArithmeticModel A X L
  metric : MetrizedLine A X L
  centre : ∀ (v : A.places)
    (h : ∀ a b : A.completion v, ‖a + b‖ ≤ max ‖a‖ ‖b‖)
    (p : ValuedLineFibres.NonArchPoint (A.completion v) (placeScheme A X v)), Centre model v h p
  frame : ∀ (v : A.places)
    (h : ∀ a b : A.completion v, ‖a + b‖ ≤ max ‖a‖ ‖b‖)
    (p : ValuedLineFibres.NonArchPoint (A.completion v) (placeScheme A X v)),
    FrameAt model (centre v h p)
  normalized : ∀ (v : A.places)
    (h : ∀ a b : A.completion v, ‖a + b‖ ≤ max ‖a‖ ‖b‖)
    (p : ValuedLineFibres.NonArchPoint (A.completion v) (placeScheme A X v))
    (z : Fibre metric v p.val), norm metric v p.val z = frameNorm model (frame v h p) z

/-- All approximation models lie over the same actual arithmetic base. -/
structure ModelSequence (B : EffectiveBoundary A X) where
  base : ArithmeticBase A
  model : ℕ → ModelMetric (A := A) (X := X) (L := L)
  common_base : ∀ n, (model n).model.base = base
  cauchy : IsCauchy B (fun n => (model n).metric)

def ModelSequence.toCauchy {B : EffectiveBoundary A X} (S : ModelSequence (L := L) B) :
    CauchySequence (L := L) B := ⟨fun n => (S.model n).metric, S.cauchy⟩

/-- The actual class of the model sequence in the native boundary quotient. -/
def ModelSequence.class {B : EffectiveBoundary A X} (S : ModelSequence (L := L) B) :
    BoundaryMetricCompletion (L := L) B := Quotient.mk _ S.toCauchy

/-- Model-compatible adelic metrics form the literal image of actual model sequences. -/
def FixedGaugeAdelicMetric (B : EffectiveBoundary A X) :=
  {m : BoundaryMetricCompletion (L := L) B //
    ∃ S : ModelSequence (L := L) B, S.class = m}

end MathlibExt.AlgebraicGeometry.AdelicModelMetricSequences
