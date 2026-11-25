/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AdelicSemipositiveClosures

/-!
# Hermitian degree and semipositive completion construction requests

The ground base, native curve degrees, whole model hermitian metric,
original quotient operations and exact positivity predicates are fixed.
No metric on an arbitrary open is asserted to extend to a model.
Modelled on Yuan--Zhang, arXiv:2105.13587v9, Sections 1.1.4, 2.5--2.6 and A.4.1.
The completion is the fixed-gauge completion of `BoundaryMetricCompletionModels`, not
Yuan--Zhang's boundary topology: their adelic line bundles and positivity notions are not
claimed here.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.HermitianModels

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
open MathlibExt.AlgebraicGeometry.ArithmeticModelHermitianMetrics
open MathlibExt.AlgebraicGeometry.HermitianModelRestrictions
open MathlibExt.AlgebraicGeometry.ArithmeticModelCurveDegrees

/-- The residue dictionary of a scheme-valued complex point fixes every regular evaluation. -/
public def_wanted complexPointDictionary (Y : Over (Spec (.of ℂ))) : PointDictionary Y

/-- Pull back the full model metric by its native complexified scheme and line maps. -/
public def_wanted hermitianPullback {Y Z : Scheme.{0}} (f : Y ⟶ Z) {L : Z.Modules}
    (H : HermitianLine L) : HermitianPullback f H

/-- The source archimedean normalization is fixed on every ground-field scalar. -/
public def_wanted complexPointExtension {K : Type} [Field K] {A : AdelicField K}
    {X : Over (Spec (.of K))} (v : A.places) (N : StandardArchimedeanPlace (A := A) v)
    (p : MathlibExt.AlgebraicGeometry.ValuedLineFibres.Point (A.completion v) (placeScheme A X v)) :
    {E : ComplexPointExtension (A := A) (X := X) v p // ∀ a : A.completion v,
      E.embedding (MathlibExt.AlgebraicGeometry.ValuedLineFibres.completionUnit _ _ p
        (MathlibExt.AlgebraicGeometry.BerkovichAnalytification.scalarMap _ _ p.schemePoint a)) =
          N.embedding a}

/-- Given the actual standard places, every archimedean valued point has a normalized extension. -/
public def_wanted archimedeanPoints {K : Type} [Field K] {A : AdelicField K}
    (X : Over (Spec (.of K)))
    (P : ∀ (v : A.places), IsArchimedean v → StandardArchimedeanPlace (A := A) v) :
    {S : ArchimedeanPoints (A := A) (X := X) // ∀ v hv, S.place v hv = P v hv}

/-- Every proper integral arithmetic curve is an actual vertical or finite horizontal curve. -/
public theorem_wanted arithmeticCurveClassification {Y : Scheme.{0}} (C : ModelCurve Y)
    (L : Y.Modules) (hL : IsLineBundle L) :
    (∃ (p : ℕ) (hp : Fact p.Prime), Nonempty (@Vertical Y C L p hp)) ∨ Horizontal C

/-- Finite horizontal line modules have an actual integral section and finite cokernel. -/
public def_wanted horizontalSection {Y : Scheme.{0}} (C : ModelCurve Y) (L : Y.Modules)
    (hL : IsLineBundle L) (Q : Horizontal C) : HorizontalSection C L

/-- The literal cokernel and complex-embedding formula is independent of the section. -/
public theorem_wanted horizontalDegreeIndependent {Y : Scheme.{0}} (C : ModelCurve Y)
    (L : Y.Modules) (Q : Horizontal C) (H : HermitianLine (curveLine C L))
    (s t : HorizontalSection C L) : horizontalDegree C L Q H s = horizontalDegree C L Q H t

/-- Finiteness of coherent cohomology in degrees $0$ and $1$: let $k$ be a field,
$f : Y \to \operatorname{Spec} k$ a proper morphism and $L$ a line bundle on $Y$. Then the
cohomology groups $H^0(Y, L)$, $H^1(Y, L)$, $H^0(Y, \mathcal{O}_Y)$ and $H^1(Y, \mathcal{O}_Y)$,
computed as right derived functors of global sections with the $k$-module structure given by $f$,
are finite-dimensional over $k$. -/
public theorem_wanted geometricCurveFinite {k : Type} [Field k] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (.of k)) [IsProper f] (L : Y.Modules) (hL : IsLineBundle L) :
    FiniteDimensional k (cohomology f L 0) ∧ FiniteDimensional k (cohomology f L 1) ∧
      FiniteDimensional k (cohomology f (structureModule Y) 0) ∧
        FiniteDimensional k (cohomology f (structureModule Y) 1)

end WantedExt.AlgebraicGeometry.HermitianModels

namespace WantedExt.AlgebraicGeometry.AdelicSemipositiveClosures

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
open MathlibExt.AlgebraicGeometry.BoundaryMetricCompletionModels
open MathlibExt.AlgebraicGeometry.RationalAdelicModelMetrics
open MathlibExt.AlgebraicGeometry.AdelicCompletionOperations
open MathlibExt.AlgebraicGeometry.AdelicSemipositiveClosures

variable {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
  {L M : X.left.Modules} (G : GroundBase (K := K)) (B : EffectiveBoundary A X)

/-- Strong nefness is invariant under the actual completed algebraic isometry. -/
public theorem_wanted isometryStronglyNef (m : FixedGaugeAdelicMetric (L := L) B)
    (n : FixedGaugeAdelicMetric (L := M) B) (H : IsIsometric B m n) (hm : IsStronglyNef G B m) :
    IsStronglyNef G B n

/-- Strongly nef model limits satisfy the source's auxiliary-line nef definition. -/
public theorem_wanted stronglyNefNef (m : FixedGaugeAdelicMetric (L := L) B)
    (H : IsStronglyNef G B m) :
    IsNef G B m

/-- Strongly nef model limits are isometric differences with the trivial strongly nef line. -/
public theorem_wanted stronglyNefIntegrable (m : FixedGaugeAdelicMetric (L := L) B)
    (H : IsStronglyNef G B m) : IsIntegrable G B m

/-- Native tensor model refinements preserve strong nefness. -/
public def_wanted stronglyNefTensor
    (F : AllPlaceTensor (A := A) (X := X) (L := L) (M := M))
    (m : FixedGaugeAdelicMetric (L := L) B) (n : FixedGaugeAdelicMetric (L := M) B)
    (hm : IsStronglyNef G B m) (hn : IsStronglyNef G B n) :
    {R : TensorResult B F m n // IsStronglyNef G B R.metric}

/-- Integrable tensor products retain their actual difference-of-strongly-nef presentation. -/
public def_wanted integrableTensor
    (F : AllPlaceTensor (A := A) (X := X) (L := L) (M := M))
    (m : FixedGaugeAdelicMetric (L := L) B) (n : FixedGaugeAdelicMetric (L := M) B)
    (hm : IsIntegrable G B m) (hn : IsIntegrable G B n) :
    {R : TensorResult B F m n // IsIntegrable G B R.metric}

variable {Y : Over (Spec (.of K))} (f : Y ⟶ X) (C : EffectiveBoundary A Y)
  (F : AllPlacePullback (A := A) (L := L) f)

/-- The normalized scheme pullback to a quasi-projective variety (an open subscheme of a
projective `K`-scheme; a proper compactification alone does not give the projective models
that nef models require) preserves strong nefness under boundary domination. -/
public def_wanted stronglyNefPullback (D : BoundaryDominated B f C)
    (hY : ∃ (Z : Over (Spec (.of K))) (j : Y ⟶ Z),
      MathlibExt.AlgebraicGeometry.RelativePolynomialProjectivity.IsProjective Z.hom ∧
        IsOpenImmersion j.left)
    (m : FixedGaugeAdelicMetric (L := L) B) (H : IsStronglyNef G B m) :
    {R : PullbackResult B f C m F // IsStronglyNef G C R.metric}

/-- The same actual pullback to a quasi-projective variety preserves the source
auxiliary-line nef property under boundary domination. -/
public def_wanted nefPullback (D : BoundaryDominated B f C)
    (hY : ∃ (Z : Over (Spec (.of K))) (j : Y ⟶ Z),
      MathlibExt.AlgebraicGeometry.RelativePolynomialProjectivity.IsProjective Z.hom ∧
        IsOpenImmersion j.left)
    (m : FixedGaugeAdelicMetric (L := L) B) (H : IsNef G B m) :
    {R : PullbackResult B f C m F // IsNef G C R.metric}

/-- Actual tensor and dual presentations make integrability stable under scheme pullback to a
quasi-projective variety, under boundary domination. -/
public def_wanted integrablePullback (D : BoundaryDominated B f C)
    (hY : ∃ (Z : Over (Spec (.of K))) (j : Y ⟶ Z),
      MathlibExt.AlgebraicGeometry.RelativePolynomialProjectivity.IsProjective Z.hom ∧
        IsOpenImmersion j.left)
    (m : FixedGaugeAdelicMetric (L := L) B) (H : IsIntegrable G B m) :
    {R : PullbackResult B f C m F // IsIntegrable G C R.metric}

end WantedExt.AlgebraicGeometry.AdelicSemipositiveClosures
