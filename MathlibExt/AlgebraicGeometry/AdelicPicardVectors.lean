/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AdelicSemipositiveClosures
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Rational Picard classes of actual integrable adelic lines

Every object retains an actual algebraic line, an actual effective boundary,
and the same rational-model Cauchy class and integrability witness. Isometry
and tensor relations use the computed norms on every actual completed fibre.
The carrier is the native rational-module quotient by those relations.

All model boundaries occur in this one presentation. A finite-point norm may
therefore choose its genuine target model boundary while its vector height
still belongs to the same Picard vector space over the original field.
No separately supplied Picard carrier or height function is introduced.

Modelled on Yuan--Zhang, arXiv:2105.13587v9, Sections 2.5--2.6 and 5.3.1.
Provider proofs for normalized geometric operations remain separate.
The completion is the fixed-gauge completion of `BoundaryMetricCompletionModels`, not
Yuan--Zhang's boundary topology: their adelic line bundles and positivity notions are not
claimed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AdelicPicardVectors

open CategoryTheory _root_.AlgebraicGeometry
open CoherentCurveLinearSeries PlacewiseMetrizedLineModels BoundaryMetricCompletionModels
open RationalAdelicModelMetrics AdelicCompletionOperations AdelicSemipositiveClosures
open scoped TensorProduct

variable {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
  (G : GroundBase (K := K))

/-- One actual integrable line together with its own genuine model boundary. -/
structure LineObject where
  line : X.left.Modules
  isLine : IsLineBundle line
  boundary : EffectiveBoundary A X
  metric : FixedGaugeAdelicMetric (L := line) boundary
  integrable : IsIntegrable G boundary metric

abbrev FreeVector := LineObject (A := A) (X := X) G →₀ ℚ

variable {G}

/-- The native rational generator of this same source object. -/
def generator (M : LineObject (A := A) (X := X) G) : FreeVector (A := A) (X := X) G := by
  classical
  exact Finsupp.single M 1

/-- Isometries are actual algebraic line isomorphisms with all computed fibre norms fixed. -/
def Isometry (M N : LineObject (A := A) (X := X) G) : Prop :=
  ∃ (e : M.line ≅ N.line) (F : AllPlaceIso (A := A) (X := X) e),
    ∀ v p z,
      AdelicCompletionEvaluations.fibreNorm N.boundary N.metric.val v p (F.map v p z) =
        AdelicCompletionEvaluations.fibreNorm M.boundary M.metric.val v p z

/-- Tensor comparison retains the actual tensor sheaf, local germs and each source boundary. -/
structure TensorComparison (M N T : LineObject (A := A) (X := X) G) where
  tensor : AllPlaceTensor (A := A) (X := X) (L := M.line) (M := N.line)
  line : CurvePositivity.moduleTensor X.left M.line N.line ≅ T.line
  fibre : AllPlaceIso (A := A) (X := X) line
  normalized : ∀ v p z w,
    AdelicCompletionEvaluations.fibreNorm T.boundary T.metric.val v p
        (fibre.map v p (tensor.map v p (z ⊗ₜ w))) =
      AdelicCompletionEvaluations.fibreNorm M.boundary M.metric.val v p z *
        AdelicCompletionEvaluations.fibreNorm N.boundary N.metric.val v p w

/-- A fixed-boundary source object enters the same full Picard presentation. -/
def ofFixedBoundary (L : X.left.Modules) (hLine : IsLineBundle L)
    (B : EffectiveBoundary A X) (m : FixedGaugeAdelicMetric (L := L) B)
    (hIntegrable : IsIntegrable G B m) : LineObject (A := A) (X := X) G :=
  ⟨L, hLine, B, m, hIntegrable⟩

/-- Relations between actual completed-fibre isometries. -/
def isometryRelations : Set (FreeVector (A := A) (X := X) G) :=
  {r | ∃ M N : LineObject (A := A) (X := X) G,
    Isometry M N ∧ r = generator M - generator N}

/-- The tensor relations: the elements $[T] - [M] - [N]$ of the free $\mathbb{Q}$-vector space on
line objects, for all line objects $M$, $N$, $T$ admitting a normalized tensor comparison
`TensorComparison M N T` (an isomorphism from the tensor product of the underlying lines of $M$ and
$N$ to that of $T$, with identifications of completed fibres at every place, under which the fibre
norm of $T$ is the product of those of $M$ and $N$). -/
def tensorRelations : Set (FreeVector (A := A) (X := X) G) :=
  {r | ∃ M N T : LineObject (A := A) (X := X) G,
    Nonempty (TensorComparison M N T) ∧ r = generator T - generator M - generator N}

/-- The exact rational relation submodule. -/
def relations : Submodule ℚ (FreeVector (A := A) (X := X) G) :=
  Submodule.span ℚ (isometryRelations (A := A) (X := X) (G := G) ∪
    tensorRelations (A := A) (X := X) (G := G))

/-- Rational isometry/tensor classes of actual integrable adelic lines. -/
abbrev PicardVector := FreeVector (A := A) (X := X) G ⧸ relations (A := A) (X := X) (G := G)

/-- The class map is the actual quotient of this source generator. -/
def lineClass (M : LineObject (A := A) (X := X) G) : PicardVector (A := A) (X := X) (G := G) :=
  (relations (A := A) (X := X) (G := G)).mkQ (generator M)

/-- Every source object retains its original algebraic module sheaf. -/
def underlyingLine (M : LineObject (A := A) (X := X) G) : X.left.Modules := M.line

/-- Genuine norm-preserving source isometries identify the vector classes. -/
theorem lineClass_isometric (M N : LineObject (A := A) (X := X) G)
    (h : Isometry M N) : lineClass M = lineClass N := by
  have hm : generator M - generator N ∈ relations (A := A) (X := X) (G := G) :=
    Submodule.subset_span (Or.inl ⟨M, N, h, rfl⟩)
  have hz : (relations (A := A) (X := X) (G := G)).mkQ
      (generator M - generator N) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hm
  apply sub_eq_zero.mp
  simpa only [lineClass, map_sub] using hz

/-- A normalized tensor comparison has the prescribed additive class. -/
theorem lineClass_tensor (M N T : LineObject (A := A) (X := X) G)
    (F : TensorComparison M N T) : lineClass T = lineClass M + lineClass N := by
  have hm : generator T - generator M - generator N ∈
      relations (A := A) (X := X) (G := G) :=
    Submodule.subset_span (Or.inr ⟨M, N, T, ⟨F⟩, rfl⟩)
  have hz : (relations (A := A) (X := X) (G := G)).mkQ
      (generator T - generator M - generator N) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hm
  apply sub_eq_zero.mp
  simpa only [lineClass, map_sub, map_add, sub_sub] using hz

end MathlibExt.AlgebraicGeometry.AdelicPicardVectors
