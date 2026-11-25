/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AdelicModelMetricSequences
public import MathlibExt.AlgebraicGeometry.MetrizedLineOperationModels

/-!
# Actual compactification extensions of model metrics

The model metric extends to the literal generic compactification and
its actual model line. The open restriction map is native base change
of the original open immersion. Its line identification uses only the
native pullback-composition maps and the original generic line isomorphism.

At every place the restriction metric uses the actual completed-residue
pullback fibre comparison and its pure-tensor norm rule. This excludes
metrics on the open X that fail to extend continuously to the model.
Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 1.1.3 and 2.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CompactificationMetricExtensions

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open PlacewiseMetrizedLineModels CoherentCurveLinearSeries
open AdelicArithmeticModelFrames

variable {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
  {L : X.left.Modules} (M : ArithmeticModel A X L)

/-- The same arithmetic model's actual full generic line. -/
def compactLine : M.compactification.left.Modules :=
  (Scheme.Modules.pullback M.genericMap).obj M.line

/-- The true placewise open restriction is native base change of the original open map. -/
def placeOpen (v : A.places) : placeScheme A X v ⟶ placeScheme A M.compactification v :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (A.embedding v)))).map M.openMap

theorem placeOpen_projection (v : A.places) :
    (placeOpen M v).left ≫ placeProjection A M.compactification v =
      placeProjection A X v ≫ M.openMap.left := by
  change _ ≫ pullback.fst M.compactification.hom _ =
    pullback.fst X.hom _ ≫ M.openMap.left
  simp [placeOpen, Over.pullback]

/-- The actual line comparison on the placewise open, with no independent line choice. -/
def placeOpenLine (v : A.places) :
    (Scheme.Modules.pullback (placeOpen M v).left).obj
      (placeLine A M.compactification (compactLine M) v) ≅ placeLine A X L v :=
  (Scheme.Modules.pullback (placeOpen M v).left).mapIso
    ((Scheme.Modules.pullbackComp (placeProjection A M.compactification v)
      M.genericMap).app M.line) ≪≫
    (Scheme.Modules.pullbackComp (placeOpen M v).left
      (placeProjection A M.compactification v ≫ M.genericMap)).app M.line ≪≫
    eqToIso (congrArg (fun g => (Scheme.Modules.pullback g).obj M.line) (by
      rw [← Category.assoc, placeOpen_projection]
      rfl)) ≪≫ placeModelLine M v

/-- A model metric extends to the whole compactification with its actual restriction norms. -/
structure Extension (N : MetrizedLine A X L) where
  metric : MetrizedLine A M.compactification (compactLine M)
  fibre : ∀ v : A.places,
    MetrizedLineOperationModels.PullbackFibre (A.completion v)
      (placeScheme A M.compactification v)
      (placeLine A M.compactification (compactLine M) v) (placeOpen M v)
  pullback : ∀ v : A.places,
    MetrizedLineOperationModels.PullbackMetric (A.completion v)
      (placeScheme A M.compactification v)
      (placeLine A M.compactification (compactLine M) v) (placeOpen M v)
      (fibre v) (metric.metric v)
  lineFibre : ∀ v : A.places,
    MetrizedLineOperationModels.FibreIso (A.completion v) (placeScheme A X v)
      ((Scheme.Modules.pullback (placeOpen M v).left).obj
        (placeLine A M.compactification (compactLine M) v))
      (placeLine A X L v) (placeOpenLine M v)
  norm_normalized : ∀ (v : A.places)
    (p : ValuedLineFibres.Point (A.completion v) (placeScheme A X v))
    (z : ValuedLineFibres.Fibre (A.completion v) (placeScheme A X v)
      ((Scheme.Modules.pullback (placeOpen M v).left).obj
        (placeLine A M.compactification (compactLine M) v)) p),
    norm N v p ((lineFibre v).map p z) = ((pullback v).metric.fibreNorm p).norm z

end MathlibExt.AlgebraicGeometry.CompactificationMetricExtensions
