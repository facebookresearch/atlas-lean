/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MetrizedFibrePowerModels
public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
public import MathlibExt.AlgebraicGeometry.GenericSectionMaps
public import MathlibExt.AlgebraicGeometry.CurvePositivity

/-!
# Actual metric isometry, tensor, dual and pullback normalizations

Every algebraic carrier is the displayed native line sheaf. Fibre maps
are linear over the actual completed residue field and fixed on every
local-section germ. Tensor norms agree on all pure tensor vectors.
Duality is the full native sheaf-Hom adjunction with its actual
evaluation, and the fibre functional is fixed by that evaluation.

The construction of these comparison maps and metrics is deferred;
none is an unrelated field or unnamed geometric functor.
Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 2.1--2.2 and A.5.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.MetrizedLineOperationModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open CoherentCurveLinearSeries ValuedLineFibres MetrizedFibrePowerModels
open LineBundleTaskContracts
open scoped TensorProduct

/-- The actual algebraic dual is characterized by full sheaf-Hom evaluation. It uses no norm on
`K`, so it also serves fields with several places. -/
structure DualLine (K : Type) [Field K] (X : Over (Spec (.of K))) (L : X.left.Modules) where
  line : X.left.Modules
  isLine : IsLineBundle line
  evaluation : CurvePositivity.moduleTensor X.left L line ⟶ structureModule X.left
  universal : ∀ T : X.left.Modules,
    Function.Bijective (fun f : T ⟶ line ↦ tensorMap (𝟙 L) f ≫ evaluation)

variable (K : Type) [NormedField K] (X : Over (Spec (.of K)))

/-- The native map of actual valued scheme points, including archimedean valuations. -/
def mapPoint {Y : Over (Spec (.of K))} (f : X ⟶ Y) (p : Point K X) : Point K Y where
  schemePoint := f.left p.schemePoint
  absoluteValue := p.absoluteValue.comp
    (RingHom.injective (f.left.residueFieldMap p.schemePoint).hom)
  extends_norm a := by
    change p.absoluteValue
      (f.left.residueFieldMap p.schemePoint (BerkovichAnalytification.scalarMap K Y _ a)) = ‖a‖
    rw [BerkovichAnalytification.scalarMap_naturality]
    exact p.extends_norm a

variable (L M : X.left.Modules)

/-- An algebraic isomorphism acts by its actual local-section germs on completed fibres. -/
structure FibreIso (e : L ≅ M) where
  map : ∀ p : Point K X, Fibre K X L p ≃ₗ[CompletedResidue K X p] Fibre K X M p
  section_normalized : ∀ (U : X.left.Opens) (s : Γ(L,U))
    (p : Point K X) (hp : p.schemePoint ∈ U),
    map p (evaluateSection K X L s p hp) =
      evaluateSection K X M (e.hom.app U s) p hp

/-- A genuine isometry has that same algebraic map and every actual fibre norm. -/
def IsIsometry (e : L ≅ M) (F : FibreIso K X L M e)
    (N : MetrizedLine K X L) (P : MetrizedLine K X M) : Prop :=
  ∀ p v, (P.fibreNorm p).norm (F.map p v) = (N.fibreNorm p).norm v

/-- The actual tensor fibre comparison is fixed on every original local section. -/
structure TensorFibre where
  map : ∀ p : Point K X,
    Fibre K X L p ⊗[CompletedResidue K X p] Fibre K X M p ≃ₗ[CompletedResidue K X p]
      Fibre K X (CurvePositivity.moduleTensor X.left L M) p
  section_normalized : ∀ (U : X.left.Opens) (s : Γ(L,U)) (t : Γ(M,U))
    (p : Point K X) (hp : p.schemePoint ∈ U),
    map p ((evaluateSection K X L s p hp) ⊗ₜ[CompletedResidue K X p]
      evaluateSection K X M t p hp) =
        evaluateSection K X (CurvePositivity.moduleTensor X.left L M)
          (tensorSectionAt L M U s t) p hp

/-- Tensor metrics retain the literal tensor sheaf and all pure-tensor norms. -/
structure TensorMetric (F : TensorFibre K X L M)
    (N : MetrizedLine K X L) (P : MetrizedLine K X M) where
  metric : MetrizedLine K X (CurvePositivity.moduleTensor X.left L M)
  normalized : ∀ (p : Point K X) (v : Fibre K X L p) (w : Fibre K X M p),
    (metric.fibreNorm p).norm (F.map p (v ⊗ₜ[CompletedResidue K X p] w)) =
      (N.fibreNorm p).norm v * (P.fibreNorm p).norm w

variable (D : DualLine K X L)

/-- The completed dual functional is fixed by actual evaluation on all local section pairs. -/
structure DualFibre where
  map : ∀ p : Point K X, Fibre K X D.line p ≃ₗ[CompletedResidue K X p]
    Module.Dual (CompletedResidue K X p) (Fibre K X L p)
  evaluation : ∀ (U : X.left.Opens) (s : Γ(L,U)) (t : Γ(D.line,U))
    (p : Point K X) (hp : p.schemePoint ∈ U),
    map p (evaluateSection K X D.line t p hp) (evaluateSection K X L s p hp) =
      completionUnit K X p
        (X.left.evaluation U p.schemePoint hp (D.evaluation.app U (tensorSectionAt L D.line U s t)))

/-- Dual norms use the actual functional/value quotient on every nonzero vector. -/
structure DualMetric (F : DualFibre K X L D) (N : MetrizedLine K X L) where
  metric : MetrizedLine K X D.line
  normalized : ∀ (p : Point K X) (f : Fibre K X D.line p) (v : Fibre K X L p), v ≠ 0 →
    (metric.fibreNorm p).norm f =
      ‖F.map p f v‖ / (N.fibreNorm p).norm v

variable {Y : Over (Spec (.of K))} (f : Y ⟶ X)

/-- Native pullback fibre data retains the actual residue-field comorphism and module germs. -/
structure PullbackFibre where
  embedding : ∀ p : Point K Y,
    CompletedResidue K X (mapPoint K Y f p) →+* CompletedResidue K Y p
  unit_normalized : ∀ (p : Point K Y) (a : X.left.residueField (f.left p.schemePoint)),
    embedding p (completionUnit K X (mapPoint K Y f p) a) =
      completionUnit K Y p (f.left.residueFieldMap p.schemePoint a)
  isometry : ∀ p a, ‖embedding p a‖ = ‖a‖
  comparison : ∀ p : Point K Y,
    letI := (embedding p).toAlgebra
    CompletedResidue K Y p ⊗[CompletedResidue K X (mapPoint K Y f p)]
      Fibre K X L (mapPoint K Y f p) ≃ₗ[CompletedResidue K Y p]
        Fibre K Y ((Scheme.Modules.pullback f.left).obj L) p
  section_normalized : ∀ (U : X.left.Opens) (s : Γ(L,U))
    (p : Point K Y) (hp : f.left p.schemePoint ∈ U),
    letI := (embedding p).toAlgebra
    comparison p ((1 : CompletedResidue K Y p) ⊗ₜ
      (evaluateSection K X L s (mapPoint K Y f p) hp)) =
      evaluateSection K Y ((Scheme.Modules.pullback f.left).obj L)
        (GenericSectionMaps.localPullbackSection f.left L U (f.left ⁻¹ᵁ U) (by rfl) s) p hp

/-- Pullback norms are fixed on every native completed-field tensor vector. -/
structure PullbackMetric (F : PullbackFibre K X L f) (N : MetrizedLine K X L) where
  metric : MetrizedLine K Y ((Scheme.Modules.pullback f.left).obj L)
  normalized : ∀ (p : Point K Y) (a : CompletedResidue K Y p)
    (v : Fibre K X L (mapPoint K Y f p)),
    letI := (F.embedding p).toAlgebra
    (metric.fibreNorm p).norm (F.comparison p (a ⊗ₜ v)) =
      ‖a‖ * (N.fibreNorm (mapPoint K Y f p)).norm v

end MathlibExt.AlgebraicGeometry.MetrizedLineOperationModels
