/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HermitianLocalChernModels
public import MathlibExt.AlgebraicGeometry.SchemeComponentIntersectionModels
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Global Archimedean Chern sources on genuine complex coordinate charts

An atlas consists of actual open partial homeomorphisms, covering all
points, with holomorphic inverse regular evaluations and holomorphic
transitions. It is stronger than a holomorphic test plot. Singular and
nonreduced schemes retain every reduced component and its original local
length; integration takes place on an actual proper resolution, with
dense source and target scheme opens and their genuine scheme isomorphism.
Every resolved metric is fixed on all actual pulled-back section germs.

Local weights and their psh splittings are fixed to those norms. Smooth
approximations are C-infinity; densities are the native complete signed
permutation mixed Hessians with the source 2*pi*i convention. Overlap
Jacobians are computed from the actual coordinate derivatives. Compact
tests are reconstructed by literal finite chart decompositions. Global
measure results retain overlap gluing, genuine convergence and exact
normalization on every continuous compact test.

Sources: Yuan--Zhang, arXiv:2105.13587v9, pp109--110, pp119--120;
Sections 3.6 and 4.3, and Appendix A.6.2. Resolution/regularization/gluing
constructions and proofs remain direct Wanted requests.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ArchimedeanChernModels

open CategoryTheory CategoryTheory.Limits Opposite Filter MeasureTheory
open _root_.AlgebraicGeometry
open ComplexAnalytification ArithmeticModelHermitianMetrics HermitianLocalChernModels
open SchemeComponentIntersectionModels CoherentCurveLinearSeries GenericSectionMaps
open scoped Topology CompactlySupported ContDiff
attribute [local instance] Classical.propDecidable

variable (d : ℕ) (M : Type) [TopologicalSpace M]

/-- Genuine complex coordinate charts, with all actual transition functions. -/
structure CoordinateAtlas where
  index : Type
  chart : index → OpenPartialHomeomorph M (Space d)
  cover : ∀ p : M, ∃ i, p ∈ (chart i).source
  holomorphicTransitions : ∀ i j, DifferentiableOn ℂ
    (fun z ↦ chart j ((chart i).symm z))
    ((chart i).target ∩ (chart i).symm ⁻¹' (chart j).source)

variable (Y : Over (Spec (.of ℂ)))

instance complexMeasurable : MeasurableSpace (ComplexPoints Y.hom) := borel _
instance complexBorel : BorelSpace (ComplexPoints Y.hom) := ⟨rfl⟩

/-- The scheme's regular functions are holomorphic in these genuine inverse charts. -/
structure ComplexAtlas extends CoordinateAtlas d (ComplexPoints Y.hom) where
  inverseRegular : ∀ i (U : Y.left.Opens) (s : Γ(Y.left,U)),
    DifferentiableOn ℂ (regularFunctionValue (chart i).symm U s)
      ((chart i).target ∩ {z | ((chart i).symm z).Mem U})

variable {d M Y}

/-- A metric on this exact complex line, with its canonical scalar/function dictionary. -/
structure ComplexMetric (L : Y.left.Modules) where
  dictionary : PointDictionary Y
  metric : ValuedLineFibres.MetrizedLine ℂ Y L

variable (L : Fin d → Y.left.Modules) (H : ∀ i, ComplexMetric (L i))
  (A : ComplexAtlas d Y) (j : A.index)

/-- Local frames and psh differences on an actual chart of this same line tuple. -/
structure ChartPotentials where
  openSet : Fin d → Y.left.Opens
  frame : ∀ i, LocalFrame (L i) (openSet i)
  contained : ∀ p ∈ (A.chart j).source, ∀ i, p.Mem (openSet i)
  positivePart : Fin d → Space d → ℝ
  negativePart : Fin d → Space d → ℝ
  positivePSH : ∀ i, IsPlurisubharmonic (positivePart i) (A.chart j).target
  negativePSH : ∀ i, IsPlurisubharmonic (negativePart i) (A.chart j).target
  normalized : ∀ (i : Fin d) (z : Space d) (hz : z ∈ (A.chart j).target),
    -Real.log (((H i).metric.fibreNorm ((H i).dictionary.point ((A.chart j).symm z))).norm
      (ValuedLineFibres.evaluateSection ℂ Y (L i) (frame i).sectionValue
        ((H i).dictionary.point ((A.chart j).symm z)) (by
          change ((A.chart j).symm z).schemePoint ∈ openSet i
          exact (ComplexPoints.schemePoint_mem_iff _ _).mpr
            (contained _ ((A.chart j).map_target hz) i)))) =
      positivePart i z - negativePart i z
  positiveSmooth : ℕ → SmoothPotentials d
  negativeSmooth : ℕ → SmoothPotentials d
  positiveHessian : ∀ n i, IsSemipositiveHessian ((positiveSmooth n).value i) (A.chart j).target
  negativeHessian : ∀ n i, IsSemipositiveHessian ((negativeSmooth n).value i) (A.chart j).target
  positiveLimit : ∀ i (Q : Set (Space d)), IsCompact Q → Q ⊆ (A.chart j).target →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ z ∈ Q,
      |(positiveSmooth n).value i z - positivePart i z| < ε
  negativeLimit : ∀ i (Q : Set (Space d)), IsCompact Q → Q ⊆ (A.chart j).target →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ z ∈ Q,
      |(negativeSmooth n).value i z - negativePart i z| < ε

variable {L H A j}

def ChartPotentials.signed (S : ChartPotentials L H A j) (n : ℕ) : SmoothPotentials d where
  value i z := (S.positiveSmooth n).value i z - (S.negativeSmooth n).value i z
  smooth i := ((S.positiveSmooth n).smooth i).sub ((S.negativeSmooth n).smooth i)

/-- The literal real volume Jacobian of a holomorphic coordinate transition. -/
def transitionJacobian (A : ComplexAtlas d Y) (i j : A.index) (z : Space d) : ℝ :=
  ‖Matrix.det (fun a b : Fin d ↦ holDerivative b
    (fun w ↦ A.chart j ((A.chart i).symm w) a) z)‖ ^ 2

/-- Every compact test is an actual finite sum of supported coordinate tests. -/
structure ChartDecomposition (A : ComplexAtlas d Y) (f : ComplexPoints Y.hom → ℝ) where
  count : ℕ
  chart : Fin count → A.index
  test : Fin count → C_c(Space d,ℝ)
  supported : ∀ k, tsupport (test k) ⊆ (A.chart (chart k)).target
  reconstruction : ∀ p : ComplexPoints Y.hom,
    f p = ∑ k : Fin count,
      if p ∈ (A.chart (chart k)).source then test k (A.chart (chart k) p) else 0

def chartStage (A : ComplexAtlas d Y) (S : ∀ j, ChartPotentials L H A j)
    {f : ComplexPoints Y.hom → ℝ} (D : ChartDecomposition A f) (n : ℕ) : ℝ :=
  ∑ k : Fin D.count, ∫ z, D.test k z * mixedDensity ((S (D.chart k)).signed n) z

/-- A proper resolution of the actual reduced component, with genuine dense opens. -/
structure Resolution (Y : Over (Spec (.of ℂ))) where
  scheme : Over (Spec (.of ℂ))
  map : scheme ⟶ Y
  [proper : IsProper map.left]
  [integral : IsIntegral scheme.left]
  sourceOpen : scheme.left.Opens
  targetOpen : Y.left.Opens
  sourceDense : Dense (sourceOpen : Set scheme.left)
  targetDense : Dense (targetOpen : Set Y.left)
  openIso : sourceOpen.toScheme ≅ targetOpen.toScheme
  onOpen : sourceOpen.ι ≫ map.left = openIso.hom ≫ targetOpen.ι
  properAnalytic : ∀ Q : Set (ComplexPoints Y.hom), IsCompact Q →
    IsCompact ((ComplexPoints.map map.left map.w) ⁻¹' Q)

attribute [instance] Resolution.proper Resolution.integral

/-- Composition with the actual reduced component inclusion is a map over the original field. -/
def componentMap {Y : Over (Spec (.of ℂ))} {C : Component Y.left}
    (T : ReducedComponent Y.left C) (R : Resolution (ReducedComponent.asOver Y T)) :
    R.scheme ⟶ Y :=
  Over.homMk (R.map.left ≫ T.inclusion) (by
    simpa only [ReducedComponent.asOver, Over.mk_hom, Category.assoc] using R.map.w)

variable (Y : Over (Spec (.of ℂ))) (d : ℕ) (L : Fin d → Y.left.Modules)
  (H : ∀ i, ComplexMetric (L i))

/-- The whole nonreduced scheme uses its actual components, lengths, resolutions and metrics. -/
structure GlobalSources where
  [proper : IsProper Y.hom]
  [finiteType : LocallyOfFiniteType Y.hom]
  pureDimension : RelativeDeterminantPairings.IsPureRelativeDimension Y.hom d
  components : ComponentSources Y.left
  resolution : ∀ C : Component Y.left,
    Resolution (ReducedComponent.asOver Y (components.frame C))
  metric : ∀ C i, ComplexMetric
    ((Scheme.Modules.pullback ((resolution C).map.left ≫ (components.frame C).inclusion)).obj (L i))
  pullbackNorm : ∀ C i (U : Y.left.Opens) (s : Γ(L i,U))
    (p : ComplexPoints (resolution C).scheme.hom)
    (hp : p.schemePoint ∈ ((resolution C).map.left ≫ (components.frame C).inclusion) ⁻¹ᵁ U)
    (hq : (ComplexPoints.map (componentMap (components.frame C) (resolution C)).left
      (componentMap (components.frame C) (resolution C)).w p).schemePoint ∈ U),
    ((metric C i).metric.fibreNorm ((metric C i).dictionary.point p)).norm
      (ValuedLineFibres.evaluateSection _ _ _
        (localPullbackSection ((resolution C).map.left ≫ (components.frame C).inclusion)
          (L i) U (((resolution C).map.left ≫ (components.frame C).inclusion) ⁻¹ᵁ U)
          (by rfl) s) ((metric C i).dictionary.point p) hp) =
    ((H i).metric.fibreNorm ((H i).dictionary.point
      (ComplexPoints.map (componentMap (components.frame C) (resolution C)).left
        (componentMap (components.frame C) (resolution C)).w p))).norm
      (ValuedLineFibres.evaluateSection _ _ _ s
        ((H i).dictionary.point
          (ComplexPoints.map (componentMap (components.frame C) (resolution C)).left
            (componentMap (components.frame C) (resolution C)).w p)) hq)
  atlas : ∀ C, ComplexAtlas d (resolution C).scheme
  chartSources : ∀ C j, ChartPotentials
    (fun i ↦ (Scheme.Modules.pullback
      ((resolution C).map.left ≫ (components.frame C).inclusion)).obj (L i))
    (metric C) (atlas C) j
  decomposition : ∀ (C : Component Y.left) (f : C_c(ComplexPoints Y.hom,ℝ)),
    ChartDecomposition (atlas C)
      (fun p ↦ f (ComplexPoints.map (componentMap (components.frame C) (resolution C)).left
        (componentMap (components.frame C) (resolution C)).w p))

variable {Y d L H} (S : GlobalSources Y d L H)

/-- The global stage is the actual component-length sum of actual chart density integrals. -/
def globalStage (f : C_c(ComplexPoints Y.hom,ℝ)) (n : ℕ) : ℝ := by
  letI := S.components.finite
  exact ∑ C : Component Y.left,
    ((componentLength (S.components.frame C)).toNat : ℝ) *
      chartStage (S.atlas C) (S.chartSources C) (S.decomposition C f) n

def globalAction (f : C_c(ComplexPoints Y.hom,ℝ)) : ℝ :=
  limUnder atTop (globalStage S f)

/-- Transition gluing is stated for the actual computed Jacobians and density limits. -/
def OverlapCompatible : Prop :=
  ∀ (C : Component Y.left) (i j : (S.atlas C).index) (t : C_c(Space d,ℝ)),
    tsupport t ⊆ ((S.atlas C).chart i).target ∩
      ((S.atlas C).chart i).symm ⁻¹' ((S.atlas C).chart j).source →
    limUnder atTop (fun n ↦ ∫ z, t z * mixedDensity ((S.chartSources C i).signed n) z) =
      limUnder atTop (fun n ↦ ∫ z, t z *
        mixedDensity ((S.chartSources C j).signed n)
          ((S.atlas C).chart j (((S.atlas C).chart i).symm z)) *
            transitionJacobian (S.atlas C) i j z)

/-- A global signed Chern measure has genuine source convergence on EVERY compact test. -/
structure ChernMeasureParts where
  positivePart : Measure (ComplexPoints Y.hom)
  negativePart : Measure (ComplexPoints Y.hom)
  [positiveFinite : IsFiniteMeasure positivePart]
  [negativeFinite : IsFiniteMeasure negativePart]
  overlap : OverlapCompatible S
  converges : ∀ f : C_c(ComplexPoints Y.hom,ℝ),
    Tendsto (globalStage S f) atTop (nhds (globalAction S f))
  normalized : ∀ f : C_c(ComplexPoints Y.hom,ℝ),
    (∫ p, f p ∂positivePart) - (∫ p, f p ∂negativePart) = globalAction S f

attribute [instance] ChernMeasureParts.positiveFinite ChernMeasureParts.negativeFinite

end MathlibExt.AlgebraicGeometry.ArchimedeanChernModels
