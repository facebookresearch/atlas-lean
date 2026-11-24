/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ValuedLineFibres
public import MathlibExt.AlgebraicGeometry.ModelLineMetrics
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Actual all-place metrized line bundles

Places have actual complete normed-field realizations and embeddings of
the base field. The measure and product formula retain the normalization
needed by arithmetic heights. Each analytic fibre is the literal scheme
base change, with the pullback of the same algebraic module sheaf and
continuous norms on its actual completed residue-field fibres.

This language allows both discrete place sets and measured adelic fields;
it is not restricted to a finite list of places or to number fields.
References: Yuan--Zhang, arXiv:2105.13587v9, Sections 2 and 4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels

open CategoryTheory CategoryTheory.Limits Opposite MeasureTheory
open _root_.AlgebraicGeometry
open ValuedLineFibres CoherentCurveLinearSeries

variable (K : Type) [Field K]

/-- An actual measured system of completed absolute-value realizations. -/
structure AdelicField where
  places : Type
  [measurable : MeasurableSpace places]
  completion : places → Type
  [normed : ∀ v, NormedField (completion v)]
  [complete : ∀ v, CompleteSpace (completion v)]
  embedding : ∀ v, K →+* completion v
  dense : ∀ v, DenseRange (embedding v)
  measure : Measure places
  nonzero_measure : measure ≠ 0
  integrable : ∀ a : K, a ≠ 0 → Integrable (fun v => Real.log ‖embedding v a‖) measure
  product_formula : ∀ a : K, a ≠ 0 → ∫ v, Real.log ‖embedding v a‖ ∂measure = 0

attribute [instance] AdelicField.measurable AdelicField.normed AdelicField.complete

variable {K} (A : AdelicField K) (X : Over (Spec (.of K)))

/-- The literal base-changed scheme at this completed place. -/
def placeScheme (v : A.places) : Over (Spec (.of (A.completion v))) :=
  Over.mk (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (A.embedding v))))

def placeProjection (v : A.places) : (placeScheme A X v).left ⟶ X.left :=
  pullback.fst X.hom (Spec.map (CommRingCat.ofHom (A.embedding v)))

def placeLine (L : X.left.Modules) (v : A.places) : (placeScheme A X v).left.Modules :=
  (Scheme.Modules.pullback (placeProjection A X v)).obj L

/-- All metrics have the same literal algebraic pullback, at every place. -/
structure MetrizedLine (L : X.left.Modules) where
  line : IsLineBundle L
  metric : ∀ v : A.places,
    ValuedLineFibres.MetrizedLine (A.completion v) (placeScheme A X v) (placeLine A X L v)

variable {A X}

/-- An actual completed fibre vector of this same global algebraic line. -/
abbrev Fibre {L : X.left.Modules} (_M : MetrizedLine A X L) (v : A.places)
    (p : Point (A.completion v) (placeScheme A X v)) :=
  ValuedLineFibres.Fibre (A.completion v) (placeScheme A X v) (placeLine A X L v) p

def norm {L : X.left.Modules} (M : MetrizedLine A X L) (v : A.places)
    (p : Point (A.completion v) (placeScheme A X v)) (a : Fibre M v p) : ℝ :=
  ((M.metric v).fibreNorm p).norm a

theorem norm_zero_iff {L : X.left.Modules} (M : MetrizedLine A X L) (v : A.places)
    (p : Point (A.completion v) (placeScheme A X v)) (a : Fibre M v p) :
    norm M v p a = 0 ↔ a = 0 := ((M.metric v).fibreNorm p).zero a

/-- Local nonarchimedean model normalization uses the actual integral frame norm. -/
structure PlaceModel {L : X.left.Modules} (M : MetrizedLine A X L) (v : A.places)
    (ultrametric : ∀ a b : A.completion v, ‖a + b‖ ≤ max ‖a‖ ‖b‖) where
  model : ModelLineMetrics.Model (A.completion v) (placeScheme A X v) ultrametric
    (placeLine A X L v)
  frames : ModelLineMetrics.Frames model
  normalized : ∀ (p : NonArchPoint (A.completion v) (placeScheme A X v))
    (a : Fibre M v p.val), norm M v p.val a = (ModelLineMetrics.modelNorm model frames p).norm a

end MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
