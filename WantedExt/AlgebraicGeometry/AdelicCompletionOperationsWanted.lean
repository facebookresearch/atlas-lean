/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.AdelicCompletionOperations
public import MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights
public import MathlibExt.AlgebraicGeometry.AdelicCompletionOperationsAdmissible
public import MathlibExt.AlgebraicGeometry.AdelicCompletionOperationsHeightLimit

/-!
# Construction requests on the literal adelic Cauchy quotient

All outputs use its already computed pointwise limit norms. Height
convergence, proved in `MathlibExt.AlgebraicGeometry.AdelicCompletionOperationsHeightLimit`,
retains the actual boundary integrability condition.
Modelled on Yuan--Zhang, arXiv:2105.13587v9, Sections 2.5--2.6, 3.4 and 5.3.
The completion is the fixed-gauge completion of `BoundaryMetricCompletionModels`, not
Yuan--Zhang's boundary topology: their adelic line bundles and positivity notions are not
claimed here.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AdelicCompletionOperations

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
open MathlibExt.AlgebraicGeometry.BoundaryMetricCompletionModels
open MathlibExt.AlgebraicGeometry.RationalAdelicModelMetrics
open MathlibExt.AlgebraicGeometry.AdelicCompletionOperations

variable {K : Type} [Field K] (A : AdelicField K) (X : Over (Spec (.of K)))
  (L M : X.left.Modules) (B : EffectiveBoundary A X)

/-- Continuity realizes the native quotient's exact pointwise limit norms. -/
public def_wanted completedMetric (m : BoundaryMetricCompletion (L := L) B) :
    MathlibExt.AlgebraicGeometry.AdelicCompletionEvaluations.Realization B m

/-- Native tensor fibres retain every original algebraic local-section germ. -/
public def_wanted allPlaceTensor (hL : IsLineBundle L) (hM : IsLineBundle M) :
    AllPlaceTensor (A := A) (X := X) (L := L) (M := M)

/-- Every algebraic line isomorphism has its source-normalized completed-fibre map. -/
public def_wanted allPlaceIso (e : L ≅ M) : AllPlaceIso (A := A) (X := X) e

/-- Tensor model refinements produce a class in the same boundary completion. -/
public def_wanted tensor (F : AllPlaceTensor (A := A) (X := X) (L := L) (M := M))
    (m : FixedGaugeAdelicMetric (L := L) B) (n : FixedGaugeAdelicMetric (L := M) B) :
    TensorResult B F m n

/-- Power norms and rational model denominators are retained on the same quotient. -/
public def_wanted power (m : FixedGaugeAdelicMetric (L := L) B) (r : ℕ)
    (F : AllPlacePower (A := A) (X := X) (L := L) r) : PowerResult B m r F

/-- Completed fibres of the dual of a line bundle at all places. Let $K$ be a field with an adelic
structure $A$ (`AdelicField`: places $v$ with complete normed completions $K_v$ and a measure
satisfying the product formula), $X$ a $K$-scheme, $L$ a line bundle on $X$ (`hL`) and $D$ an
algebraic dual of $L$ (`AlgebraicDual`): a line bundle $L^\vee$ with a map
$\mathrm{ev} : L \otimes L^\vee \to \mathcal{O}_X$ such that, for every sheaf of modules $T$,
$\phi \mapsto \mathrm{ev} \circ (1 \otimes \phi)$ is a bijection from maps $T \to L^\vee$ to maps
$L \otimes T \to \mathcal{O}_X$. Then, for every place $v$ and every point $p$ of $X_{K_v}$ with an
absolute value on its residue field extending that of $K_v$, there is an isomorphism, linear over
the completed residue field $\mathcal{H}(p)$, from the completed fibre of $L^\vee$ at $p$ to the
dual of the completed fibre of $L$ at $p$, that pairs the values at $p$ of local sections $t$ of
$L^\vee$ and $s$ of $L$ to the value at $p$ of $\mathrm{ev}(s \otimes t)$ (`AllPlaceDual`). -/
public def_wanted allPlaceDual (hL : IsLineBundle L) (D : AlgebraicDual (X := X) (L := L)) :
    AllPlaceDual (A := A) D

/-- Dual model norms use the actual functional/value quotient. -/
public def_wanted dual (m : FixedGaugeAdelicMetric (L := L) B) (D : AlgebraicDual (X := X) (L := L))
    (F : AllPlaceDual (A := A) D) : DualResult B m D F

/-- Native base change fixes every residue-field unit and pulled-back section. -/
public def_wanted allPlacePullback {Y : Over (Spec (.of K))} (f : Y ⟶ X) :
    AllPlacePullback (A := A) (L := L) f

/-- Boundary domination preserves Cauchy convergence under the actual scheme pullback. -/
public def_wanted pullback {Y : Over (Spec (.of K))} (f : Y ⟶ X)
    (C : EffectiveBoundary A Y) (H : BoundaryDominated B f C)
    (m : FixedGaugeAdelicMetric (L := L) B) (F : AllPlacePullback (A := A) (L := L) f) :
    PullbackResult B f C m F

end WantedExt.AlgebraicGeometry.AdelicCompletionOperations

namespace WantedExt.AlgebraicGeometry.CompletedAdelicPointHeights

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PlacewiseMetrizedLineModels
open MathlibExt.AlgebraicGeometry.BoundaryMetricCompletionModels
open MathlibExt.AlgebraicGeometry.MeasuredLinePointHeights
open MathlibExt.AlgebraicGeometry.CompletedAdelicPointHeights

variable {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
  {L : X.left.Modules} (B : EffectiveBoundary A X) (m : BoundaryMetricCompletion (L := L) B)
  {x : BasePoint (K := K) ⟶ X} (F : PointFrame A X L x)

end WantedExt.AlgebraicGeometry.CompletedAdelicPointHeights
