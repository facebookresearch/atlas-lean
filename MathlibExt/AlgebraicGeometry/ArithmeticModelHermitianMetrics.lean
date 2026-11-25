/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AdelicArithmeticModelFrames
public import MathlibExt.AlgebraicGeometry.ComplexAnalytification
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.Complex.Basic

/-!
# Full arithmetic-model hermitian metrics and local semipositivity

Complexification uses the actual model's native map to Spec Z. The
metric is continuous on the whole complex model, including complex
fibres which are absent from its generic compactification. Conjugation
is the actual conjugation of its scheme-valued complex points.

Semipositivity is expressed by the submean inequality for the negative
logarithmic weight of every actual local frame, on every holomorphic
disk plot. Holomorphic plots are tested by all regular functions. The
circle average has its literal probability normalization 1/(2 pi).
Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 1.1.3 and A.4.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ArithmeticModelHermitianMetrics

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open ComplexAnalytification ValuedLineFibres CoherentCurveLinearSeries
open GenericSectionMaps
open scoped TensorProduct Topology Interval

def integerMap (Y : Scheme.{0}) : Y ⟶ Spec (.of ℤ) := specZIsTerminal.from Y

def complexScheme (Y : Scheme.{0}) : Over (Spec (.of ℂ)) :=
  Over.mk (pullback.snd (integerMap Y) (Spec.map (CommRingCat.ofHom (Int.castRingHom ℂ))))

def complexProjection (Y : Scheme.{0}) : (complexScheme Y).left ⟶ Y :=
  pullback.fst (integerMap Y) (Spec.map (CommRingCat.ofHom (Int.castRingHom ℂ)))

def complexLine {Y : Scheme.{0}} (L : Y.Modules) : (complexScheme Y).left.Modules :=
  (Scheme.Modules.pullback (complexProjection Y)).obj L

/-- The actual complex point dictionary is fixed on scalars and every regular function. -/
structure PointDictionary (Y : Over (Spec (.of ℂ))) where
  residue : ∀ p : ComplexPoints Y.hom, Y.left.residueField p.schemePoint ≃+* ℂ
  scalars : ∀ (p : ComplexPoints Y.hom) (a : ℂ),
    residue p (BerkovichAnalytification.scalarMap ℂ Y p.schemePoint a) = a
  regular : ∀ (V : Y.left.Opens) (s : Γ(Y.left,V)) (p : ComplexPoints Y.hom)
    (hp : p.Mem V), residue p
      (Y.left.evaluation V p.schemePoint ((ComplexPoints.schemePoint_mem_iff p V).mpr hp) s) =
        ComplexPoints.eval s p hp

def PointDictionary.point {Y : Over (Spec (.of ℂ))} (D : PointDictionary Y)
    (p : ComplexPoints Y.hom) : ValuedLineFibres.Point ℂ Y where
  schemePoint := p.schemePoint
  absoluteValue := (IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ)).comp
    (f := (D.residue p).toRingHom) (D.residue p).injective
  extends_norm a := by
    change ‖D.residue p (BerkovichAnalytification.scalarMap ℂ Y p.schemePoint a)‖ = ‖a‖
    rw [D.scalars]

/-- Conjugation is defined on actual scheme-valued points by the native pullback. -/
def conjugatePoint (Y : Scheme.{0}) (p : ComplexPoints (complexScheme Y).hom) :
    ComplexPoints (complexScheme Y).hom :=
  ⟨pullback.lift
    (Spec.map (CommRingCat.ofHom Complex.conjAe.toRingEquiv.toRingHom) ≫
      p.hom ≫ complexProjection Y)
    (𝟙 (Spec (.of ℂ))) (specZIsTerminal.hom_ext _ _), by
      change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
      simp⟩

def complexSection {Y : Scheme.{0}} {L : Y.Modules} (V : Y.Opens) (s : Γ(L,V)) :
    Γ(complexLine L, complexProjection Y ⁻¹ᵁ V) :=
  localPullbackSection (complexProjection Y) L V (complexProjection Y ⁻¹ᵁ V) (by rfl) s

/-- A full continuous hermitian metric on the actual model over Spec Z. -/
structure HermitianLine {Y : Scheme.{0}} (L : Y.Modules) where
  dictionary : PointDictionary (complexScheme Y)
  metric : ValuedLineFibres.MetrizedLine ℂ (complexScheme Y) (complexLine L)
  conjugation : ∀ (V : Y.Opens) (s : Γ(L,V)) (p : ComplexPoints (complexScheme Y).hom)
    (hp : p.Mem (complexProjection Y ⁻¹ᵁ V))
    (hq : (conjugatePoint Y p).Mem (complexProjection Y ⁻¹ᵁ V)),
    (metric.fibreNorm (dictionary.point (conjugatePoint Y p))).norm
      (evaluateSection _ _ _ (complexSection V s) (dictionary.point (conjugatePoint Y p))
        (by change (conjugatePoint Y p).schemePoint ∈ _
            exact (ComplexPoints.schemePoint_mem_iff _ _).mpr hq)) =
    (metric.fibreNorm (dictionary.point p)).norm
      (evaluateSection _ _ _ (complexSection V s) (dictionary.point p)
        (by change p.schemePoint ∈ _
            exact (ComplexPoints.schemePoint_mem_iff _ _).mpr hp))

def plotRegularValue {Y : Over (Spec (.of ℂ))} (f : ℂ → ComplexPoints Y.hom)
    (V : Y.left.Opens) (s : Γ(Y.left,V)) (z : ℂ) : ℂ := by
  classical
  exact if h : (f z).Mem V then ComplexPoints.eval s (f z) h else 0

/-- A holomorphic disk plot on the actual complex-point space. -/
structure HolomorphicPlot (Y : Over (Spec (.of ℂ))) where
  domain : Set ℂ
  isOpen : IsOpen domain
  point : ℂ → ComplexPoints Y.hom
  continuous : ContinuousOn point domain
  holomorphic : ∀ (V : Y.left.Opens) (s : Γ(Y.left,V)),
    DifferentiableOn ℂ (plotRegularValue point V s) (domain ∩ {z | (point z).Mem V})

/-- An actual local algebraic frame, fixed by its module stalk germs. -/
structure LocalFrame {Y : Over (Spec (.of ℂ))} (L : Y.left.Modules) (V : Y.left.Opens) where
  sectionValue : Γ(L,V)
  basis : ∀ (y : Y.left) (_hy : y ∈ V),
    Module.Basis Unit (Y.left.presheaf.stalk y)
      (↑(TopCat.Presheaf.stalk L.val.presheaf y : AddCommGrpCat.{0}))
  normalized : ∀ y hy, basis y hy () =
    TopCat.Presheaf.germ L.val.presheaf V y hy sectionValue

def frameWeight {Y : Scheme.{0}} {L : Y.Modules} (H : HermitianLine L)
    (V : (complexScheme Y).left.Opens) (F : LocalFrame (complexLine L) V)
    (P : HolomorphicPlot (complexScheme Y)) (z : ℂ) : ℝ := by
  classical
  exact if h : (P.point z).Mem V then
    -Real.log ((H.metric.fibreNorm (H.dictionary.point (P.point z))).norm
      (evaluateSection _ _ _ F.sectionValue (H.dictionary.point (P.point z))
        (by change (P.point z).schemePoint ∈ V
            exact (ComplexPoints.schemePoint_mem_iff _ _).mpr h))) else 0

/-- Local plurisubharmonicity has the source's exact submean inequality. -/
def IsSemipositive {Y : Scheme.{0}} {L : Y.Modules} (H : HermitianLine L) : Prop :=
  ∀ (V : (complexScheme Y).left.Opens) (F : LocalFrame (complexLine L) V)
    (P : HolomorphicPlot (complexScheme Y)) (z : ℂ) (r : ℝ), 0 < r →
    Metric.closedBall z r ⊆ P.domain ∩ {w | (P.point w).Mem V} →
    CircleIntegrable (frameWeight H V F P) z r ∧
      frameWeight H V F P z ≤ (2 * Real.pi)⁻¹ *
        ∫ θ in 0..2 * Real.pi, frameWeight H V F P (circleMap z r θ)

end MathlibExt.AlgebraicGeometry.ArithmeticModelHermitianMetrics
