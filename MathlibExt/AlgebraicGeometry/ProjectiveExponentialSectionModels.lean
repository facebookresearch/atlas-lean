/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HolomorphicCoefficientSheaves
public import MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
public import MathlibExt.AlgebraicGeometry.RightCoordinateDifferentials
public import MathlibExt.AlgebraicGeometry.EnhancedIndQuotientModels
public import MathlibExt.AlgebraicGeometry.GeometricDModuleFiltrations
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Source projective-line exponentials with actual meromorphic coefficients

The line is the native one-point compactification of C. The two affine
coordinates are tau and zeta=1/tau. Meromorphic coefficients are actual
holomorphic functions on the finite part with a finite pole at infinity;
they are not restricted to rational functions. Left exp(±tau) acts by
f'±f; r(exp(-tau)) retains the actual top-form tensor and acts on its
d-tau coefficient by -f'+f. All full finite P-operators retain the native
differential ring/module action.

Source: DK1311.2374v2 Sections2.5,8.2 and9.1; Mathlib56a005 native
OnePoint, holomorphic coefficients, differential rings and O-tensor, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ProjectiveExponentialSectionModels

open _root_.CategoryTheory _root_.Opposite TopologicalSpace Set
open HolomorphicCoefficientSheaves DifferentialOperatorSheaves RightDifferentialModules
open RightCoordinateDifferentials
open scoped Manifold ContDiff

attribute [local instance] Classical.propDecidable

abbrev ProjectiveLine := OnePoint ℂ
abbrev ProjectiveCoordinates := KahlerClassGeometry.Coordinates 1

def tauInclusion : ℂ → ProjectiveLine := fun z => ↑z

def zetaInclusion (z : ℂ) : ProjectiveLine :=
  if z = 0 then OnePoint.infty else ↑z⁻¹

/-- A complex structure on the projective line, the one-point compactification of $ℂ$, in which
both affine coordinates are holomorphic: charts modelled on $ℂ^1$ forming a complex manifold, for
which the maps $τ : ℂ → \mathbb{P}^1$, $z ↦ z$, and $ζ : ℂ → \mathbb{P}^1$, $z ↦ 1/z$ (sending $0$
to $∞$), are holomorphic. -/
class ProjectiveComplexSource where
  [charts : ChartedSpace ProjectiveCoordinates ProjectiveLine]
  [manifold : IsManifold 𝓘(ℂ, ProjectiveCoordinates) ∞ ProjectiveLine]
  tauHolomorphic : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ProjectiveCoordinates) ∞ tauInclusion
  zetaHolomorphic : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ProjectiveCoordinates) ∞ zetaInclusion

attribute [instance_reducible, instance] ProjectiveComplexSource.charts
attribute [instance] ProjectiveComplexSource.manifold

def affineOpen (U : Opens ProjectiveLine) : Opens ℂ :=
  ⟨tauInclusion ⁻¹' U, U.isOpen.preimage OnePoint.continuous_coe⟩

def totalAffineFunction {U : Opens ProjectiveLine} (f : affineOpen U → ℂ) (z : ℂ) : ℂ :=
  if h : z ∈ affineOpen U then f ⟨z, h⟩ else 0

/-- Finite pole order at the actual point infinity, tested in the original reciprocal coordinate. -/
def HasFinitePoleAtInfinity (U : Opens ProjectiveLine) (f : affineOpen U → ℂ) : Prop :=
  OnePoint.infty ∈ U → ∃ (N : ℕ) (ε : ℝ) (g : ℂ → ℂ), 0 < ε ∧
    ContDiffOn ℂ ∞ g (Metric.ball 0 ε) ∧
    ∀ z : ℂ, z ≠ 0 → ‖z‖ < ε →
      ∃ h : z⁻¹ ∈ affineOpen U, z ^ N * f ⟨z⁻¹, h⟩ = g z

def IsMeromorphicCoefficient (U : Opens ProjectiveLine) (f : affineOpen U → ℂ) : Prop :=
  ContDiffOn ℂ ∞ (totalAffineFunction f) (affineOpen U) ∧ HasFinitePoleAtInfinity U f

/-- Algebra closure of the analytic/finite-pole condition. It holds (see the instance below), so it
is not an assumption of any dependent declaration. -/
class MeromorphicAlgebraSource : Prop where
  zero : ∀ U, IsMeromorphicCoefficient U 0
  one : ∀ U, IsMeromorphicCoefficient U 1
  add : ∀ U f g, IsMeromorphicCoefficient U f → IsMeromorphicCoefficient U g →
    IsMeromorphicCoefficient U (f + g)
  mul : ∀ U f g, IsMeromorphicCoefficient U f → IsMeromorphicCoefficient U g →
    IsMeromorphicCoefficient U (f * g)
  constants : ∀ U c, IsMeromorphicCoefficient U (fun _ => c)

/-- A neighbourhood of infinity in an open set containing it reaches every large finite point. -/
theorem exists_inv_mem_affineOpen {U : Opens ProjectiveLine} (hU : OnePoint.infty ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ < ε → z⁻¹ ∈ affineOpen U := by
  have hK : IsCompact ((OnePoint.some : ℂ → OnePoint ℂ) ⁻¹' (U : Set (OnePoint ℂ)))ᶜ :=
    ((OnePoint.isOpen_iff_of_mem hU).1 U.isOpen).2
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hK.isBounded
  refine ⟨1 / (max R 0 + 1), by positivity, fun z hz hzε => ?_⟩
  by_contra hmem
  have hin : z⁻¹ ∈ ((OnePoint.some : ℂ → OnePoint ℂ) ⁻¹' (U : Set (OnePoint ℂ)))ᶜ := hmem
  have hle : ‖z⁻¹‖ ≤ R := by simpa using hR hin
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [norm_inv] at hle
  have h1 : ‖z‖ * (max R 0 + 1) < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hzε
    linarith
  have h2 : 1 ≤ ‖z‖ * R := by
    have := (inv_le_iff_one_le_mul₀' hpos).1 hle
    linarith
  nlinarith [le_max_left R 0, le_max_right R 0]

theorem totalAffineFunction_add {U : Opens ProjectiveLine} (f g : affineOpen U → ℂ) :
    totalAffineFunction (f + g) = totalAffineFunction f + totalAffineFunction g := by
  funext z
  by_cases h : z ∈ affineOpen U <;> simp [totalAffineFunction, h]

theorem totalAffineFunction_mul {U : Opens ProjectiveLine} (f g : affineOpen U → ℂ) :
    totalAffineFunction (f * g) = totalAffineFunction f * totalAffineFunction g := by
  funext z
  by_cases h : z ∈ affineOpen U <;> simp [totalAffineFunction, h]

theorem isMeromorphicCoefficient_const (U : Opens ProjectiveLine) (c : ℂ) :
    IsMeromorphicCoefficient U (fun _ => c) := by
  refine ⟨(contDiffOn_const (c := c)).congr fun z hz => ?_, fun hU => ?_⟩
  · have hz' : z ∈ affineOpen U := hz
    simp [totalAffineFunction, hz']
  obtain ⟨ε, hε, hinv⟩ := exists_inv_mem_affineOpen hU
  exact ⟨0, ε, fun _ => c, hε, contDiffOn_const, fun z hz hzε => ⟨hinv z hz hzε, by simp⟩⟩

theorem isMeromorphicCoefficient_add {U : Opens ProjectiveLine} {f g : affineOpen U → ℂ}
    (hf : IsMeromorphicCoefficient U f) (hg : IsMeromorphicCoefficient U g) :
    IsMeromorphicCoefficient U (f + g) := by
  refine ⟨by rw [totalAffineFunction_add]; exact hf.1.add hg.1, fun hU => ?_⟩
  obtain ⟨N₁, ε₁, g₁, hε₁, hg₁, e₁⟩ := hf.2 hU
  obtain ⟨N₂, ε₂, g₂, hε₂, hg₂, e₂⟩ := hg.2 hU
  refine ⟨N₁ + N₂, min ε₁ ε₂, fun z => z ^ N₂ * g₁ z + z ^ N₁ * g₂ z, lt_min hε₁ hε₂, ?_, ?_⟩
  · exact ((contDiffOn_id.pow N₂).mul (hg₁.mono (Metric.ball_subset_ball (min_le_left _ _)))).add
      ((contDiffOn_id.pow N₁).mul (hg₂.mono (Metric.ball_subset_ball (min_le_right _ _))))
  · intro z hz hzε
    obtain ⟨h₁, k₁⟩ := e₁ z hz (lt_of_lt_of_le hzε (min_le_left _ _))
    obtain ⟨h₂, k₂⟩ := e₂ z hz (lt_of_lt_of_le hzε (min_le_right _ _))
    refine ⟨h₁, ?_⟩
    simp only [Pi.add_apply]
    rw [← k₁, ← k₂]
    ring

theorem isMeromorphicCoefficient_mul {U : Opens ProjectiveLine} {f g : affineOpen U → ℂ}
    (hf : IsMeromorphicCoefficient U f) (hg : IsMeromorphicCoefficient U g) :
    IsMeromorphicCoefficient U (f * g) := by
  refine ⟨by rw [totalAffineFunction_mul]; exact hf.1.mul hg.1, fun hU => ?_⟩
  obtain ⟨N₁, ε₁, g₁, hε₁, hg₁, e₁⟩ := hf.2 hU
  obtain ⟨N₂, ε₂, g₂, hε₂, hg₂, e₂⟩ := hg.2 hU
  refine ⟨N₁ + N₂, min ε₁ ε₂, fun z => g₁ z * g₂ z, lt_min hε₁ hε₂, ?_, ?_⟩
  · exact (hg₁.mono (Metric.ball_subset_ball (min_le_left _ _))).mul
      (hg₂.mono (Metric.ball_subset_ball (min_le_right _ _)))
  · intro z hz hzε
    obtain ⟨h₁, k₁⟩ := e₁ z hz (lt_of_lt_of_le hzε (min_le_left _ _))
    obtain ⟨h₂, k₂⟩ := e₂ z hz (lt_of_lt_of_le hzε (min_le_right _ _))
    refine ⟨h₁, ?_⟩
    simp only [Pi.mul_apply]
    rw [← k₁, ← k₂]
    ring

/-- The meromorphic coefficients form a subalgebra: the closure properties are proved above. -/
instance : MeromorphicAlgebraSource where
  zero U := isMeromorphicCoefficient_const U 0
  one U := isMeromorphicCoefficient_const U 1
  add _ _ _ hf hg := isMeromorphicCoefficient_add hf hg
  mul _ _ _ hf hg := isMeromorphicCoefficient_mul hf hg
  constants U c := isMeromorphicCoefficient_const U c


def meromorphicAlgebra (U : Opens ProjectiveLine) : Subalgebra ℂ (affineOpen U → ℂ) where
  carrier := {f | IsMeromorphicCoefficient U f}
  zero_mem' := MeromorphicAlgebraSource.zero U
  one_mem' := MeromorphicAlgebraSource.one U
  add_mem' := fun {f g} hf hg => MeromorphicAlgebraSource.add U f g hf hg
  mul_mem' := fun {f g} hf hg => MeromorphicAlgebraSource.mul U f g hf hg
  algebraMap_mem' := MeromorphicAlgebraSource.constants U

def leftExponentialDerivative (sign : ℂ) {U : Opens ProjectiveLine}
    (f : meromorphicAlgebra U) (z : affineOpen U) : ℂ :=
  deriv (totalAffineFunction f.val) z.val + sign * f.val z

def rightNegativeExponentialDerivative {U : Opens ProjectiveLine}
    (f : meromorphicAlgebra U) (z : affineOpen U) : ℂ :=
  -deriv (totalAffineFunction f.val) z.val + f.val z

variable [ProjectiveComplexSource]
  [HasSheafify (Opens.grothendieckTopology ProjectiveLine) RingCat.{0}]

abbrev projectiveCoefficients := coefficientPresheaf ProjectiveCoordinates ProjectiveLine
abbrev ProjectiveDModule := DModule ℂ ProjectiveLine projectiveCoefficients
abbrev ProjectiveRightDModule := RightModule ℂ ProjectiveLine projectiveCoefficients

/-- A complete local finite-operator realization of the exponential gauge on actual coefficients. -/
structure ExponentialDModuleSource (sign : ℂ) where
  object : ProjectiveDModule
  sections : ∀ U : Opens ProjectiveLine, object.val.obj (op U) ≃+ meromorphicAlgebra U
  restriction : ∀ (U V : Opens ProjectiveLine) (h : V ≤ U) (s : object.val.obj (op U))
      (z : affineOpen V),
    (sections V ((object.val.map (homOfLE h).op).hom s)).val z =
      (sections U s).val ⟨z.val, h z.property⟩
  gaugeSection : ∀ (U V : Opens ProjectiveLine) (h : V ≤ U)
    (_hfinite : OnePoint.infty ∉ V) (s : object.val.obj (op U)),
      projectiveCoefficients.obj (op V)
  gaugeValue : ∀ (U V : Opens ProjectiveLine) (h : V ≤ U)
    (hfinite : OnePoint.infty ∉ V) (s : object.val.obj (op U)) (z : affineOpen V),
      (gaugeSection U V h hfinite s).val ⟨tauInclusion z.val, z.property⟩ =
        Complex.exp (sign * z.val) * (sections U s).val ⟨z.val, h z.property⟩
  scalarAction : ∀ (U : Opens ProjectiveLine) (a : projectiveCoefficients.obj (op U))
      (s : object.val.obj (op U)) (z : affineOpen U),
    (sections U (GeometricDModuleFiltrations.act ProjectiveCoordinates ProjectiveLine object
      (DifferentialOperatorScalars.scalarFinite ℂ ProjectiveLine projectiveCoefficients U a) s)).val z =
        a.val ⟨tauInclusion z.val, z.property⟩ * (sections U s).val z
  fullOperatorGauge : ∀ (U V : Opens ProjectiveLine) (h : V ≤ U)
      (P : finiteOperatorRing ℂ ProjectiveLine projectiveCoefficients U)
      (s : object.val.obj (op U))
      (g : projectiveCoefficients.obj (op V)),
      (∀ z : affineOpen V, g.val ⟨tauInclusion z.val, z.property⟩ =
        Complex.exp (sign * z.val) * (sections U s).val ⟨z.val, h z.property⟩) →
      ∀ z : affineOpen V,
        (sections U (GeometricDModuleFiltrations.act ProjectiveCoordinates ProjectiveLine object P s)).val
          ⟨z.val, h z.property⟩ =
          Complex.exp (-sign * z.val) *
            (P.val.val ⟨V, h⟩ g).val ⟨tauInclusion z.val, z.property⟩

open HolomorphicCotangentModuleModels HarmonicHolomorphicModuleModels

variable [HolomorphicCoefficientSheaves.SheafCondition ProjectiveCoordinates ProjectiveLine]
  [CotangentSectionCalculus (n := 1) (M := ProjectiveLine)]
  [CotangentSheafCondition (n := 1) (M := ProjectiveLine)]
  [HasSheafify (Opens.grothendieckTopology ProjectiveLine) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology ProjectiveLine).WEqualsLocallyBijective AddCommGrpCat.{0}]

def holomorphicCoefficientComparison :
    holomorphicStructureRing (n := 1) (M := ProjectiveLine) ⟶
      DifferentialOperatorScalars.coefficientSheaf ℂ ProjectiveLine projectiveCoefficients :=
  ObjectProperty.homMk (toSheafify (Opens.grothendieckTopology ProjectiveLine)
    (HolomorphicCoefficientSheaves.ringPresheaf ProjectiveCoordinates ProjectiveLine))

def leftHolomorphicCoefficients (N : ProjectiveDModule) :
    SheafOfModules.{0} (holomorphicStructureRing (n := 1) (M := ProjectiveLine)) :=
  (SheafOfModules.restrictScalars holomorphicCoefficientComparison).obj
    ((DifferentialOperatorScalars.underlyingO ℂ ProjectiveLine projectiveCoefficients).obj N)

def rightHolomorphicCoefficients (N : ProjectiveRightDModule) :
    SheafOfModules.{0} (holomorphicStructureRing (n := 1) (M := ProjectiveLine)) :=
  (SheafOfModules.restrictScalars holomorphicCoefficientComparison).obj
    ((RightDifferentialModules.underlyingO ℂ ProjectiveLine projectiveCoefficients).obj N)

def tauCoordinate (p : ProjectiveLine) : ℂ := p.elim 0 id

/-- The frame is the actual native holomorphic cotangent of the prescribed affine coordinate. -/
structure TauTopFormSource where
  dtau : ∀ (U : Opens ProjectiveLine), OnePoint.infty ∉ U →
    (holomorphicOmega (n := 1) (M := ProjectiveLine) 1).val.obj (op U)
  value : ∀ (U : Opens ProjectiveLine) (hfinite : OnePoint.infty ∉ U)
      (x : U) (v : Fin 1 → TangentSpace 𝓘(ℂ, ProjectiveCoordinates) x.val),
    (dtau U hfinite).val x v =
      (mfderiv 𝓘(ℂ, ProjectiveCoordinates) 𝓘(ℂ, ℂ) tauCoordinate x.val) (v 0)

/-- The actual global holomorphic vector field d/dtau has no global holomorphic tau function. -/
structure TauDerivativeSource where
  derivative : ∀ U : Opens ProjectiveLine,
    Derivation ℂ (projectiveCoefficients.obj (op U)) (projectiveCoefficients.obj (op U))
  restriction : ∀ (U V : Opens ProjectiveLine) (h : V ≤ U),
    (restrictionLinear ℂ ProjectiveLine projectiveCoefficients h).comp (derivative U).toLinearMap =
      (derivative V).toLinearMap.comp (restrictionLinear ℂ ProjectiveLine projectiveCoefficients h)
  affineValue : ∀ (U : Opens ProjectiveLine) (f : projectiveCoefficients.obj (op U))
      (z : affineOpen U),
    (derivative U f).val ⟨tauInclusion z.val, z.property⟩ =
      deriv (totalAffineFunction (fun w : affineOpen U =>
        f.val ⟨tauInclusion w.val, w.property⟩)) z.val

def tauFiniteOperator (D : TauDerivativeSource) (U : Opens ProjectiveLine) :
    finiteOperatorRing ℂ ProjectiveLine projectiveCoefficients U :=
  ⟨⟨fun V => (D.derivative V.val).toLinearMap,
    fun V W h => D.restriction V.val W.val h⟩,
    Subring.subset_closure ⟨1, fun V => RightCoordinateDifferentials.derivation_order_one ℂ
      (projectiveCoefficients.obj (op V.val)) (D.derivative V.val)⟩⟩

structure LocalFormalTransposeSource (U : Opens ProjectiveLine)
    (_hfinite : OnePoint.infty ∉ U) (D : TauDerivativeSource) where
  transpose : finiteOperatorRing ℂ ProjectiveLine projectiveCoefficients U →+*
    (finiteOperatorRing ℂ ProjectiveLine projectiveCoefficients U)ᵐᵒᵖ
  constants : ∀ a : projectiveCoefficients.obj (op U),
    MulOpposite.unop (transpose
      (DifferentialOperatorScalars.scalarFinite ℂ ProjectiveLine projectiveCoefficients U a)) =
        DifferentialOperatorScalars.scalarFinite ℂ ProjectiveLine projectiveCoefficients U a
  derivative : MulOpposite.unop (transpose
    (tauFiniteOperator D U)) = -tauFiniteOperator D U
  generation : ∀ P : finiteOperatorRing ℂ ProjectiveLine projectiveCoefficients U,
    P ∈ Subring.closure (Set.range (DifferentialOperatorScalars.scalarFinite ℂ ProjectiveLine
      projectiveCoefficients U) ∪ {tauFiniteOperator D U})

/-- The right carrier is the actual Omega_P tensor E^{-tau}, with every native P action normalized. -/
structure RightNegativeExponentialSource (Eminus : ExponentialDModuleSource (-1))
    (D : TauDerivativeSource)
    (W : TauTopFormSource)
    (T : ∀ (U : Opens ProjectiveLine) (hfinite : OnePoint.infty ∉ U),
      LocalFormalTransposeSource U hfinite D) where
  object : ProjectiveRightDModule
  sections : ∀ U : Opens ProjectiveLine, object.val.obj (op U) ≃+ meromorphicAlgebra U
  restriction : ∀ (U V : Opens ProjectiveLine) (h : V ≤ U) (s : object.val.obj (op U))
      (z : affineOpen V),
    (sections V ((object.val.map (homOfLE h).op).hom s)).val z =
      (sections U s).val ⟨z.val, h z.property⟩
  scalarAction : ∀ (U : Opens ProjectiveLine) (a : projectiveCoefficients.obj (op U))
      (s : object.val.obj (op U)) (z : affineOpen U),
    (sections U (rightAct ℂ ProjectiveLine projectiveCoefficients object U
      (DifferentialOperatorScalars.scalarFinite ℂ ProjectiveLine projectiveCoefficients U a) s)).val z =
        a.val ⟨tauInclusion z.val, z.property⟩ * (sections U s).val z
  topformTensor : rightHolomorphicCoefficients object ≅
    holomorphicTensor (holomorphicOmega (n := 1) (M := ProjectiveLine) 1)
      (leftHolomorphicCoefficients Eminus.object)
  dtauValue : ∀ (U : Opens ProjectiveLine) (hfinite : OnePoint.infty ∉ U)
      (s : Eminus.object.val.obj (op U)) (z : affineOpen U),
    (sections U ((topformTensor.inv.val.app (op U)).hom
      (holomorphicTensorSection (holomorphicOmega (n := 1) (M := ProjectiveLine) 1)
        (leftHolomorphicCoefficients Eminus.object) U (W.dtau U hfinite) s))).val z =
      (Eminus.sections U s).val z
  fullRightAction : ∀ (U : Opens ProjectiveLine) (hfinite : OnePoint.infty ∉ U)
      (P : finiteOperatorRing ℂ ProjectiveLine projectiveCoefficients U)
      (s : object.val.obj (op U)),
    sections U (rightAct ℂ ProjectiveLine projectiveCoefficients object U P s) =
      Eminus.sections U (GeometricDModuleFiltrations.act ProjectiveCoordinates ProjectiveLine
        Eminus.object (MulOpposite.unop ((T U hfinite).transpose P))
          ((Eminus.sections U).symm (sections U s)))

/-- The fixed extension of the real parameter sends both ends to the actual point infinity. -/
def realProjectiveMap : EReal → ProjectiveLine :=
  EReal.rec OnePoint.infty (fun t => tauInclusion (t : ℂ)) OnePoint.infty

structure RealProjectiveMapSource : Prop where
  continuous : Continuous realProjectiveMap

def realGraphInclusion (X : TopCat.{0}) (S : RealProjectiveMapSource) :
    (EnhancedIndQuotientModels.enhancedSpace X).ambient ⟶ TopCat.of (X × ProjectiveLine) :=
  TopCat.ofHom ⟨fun p => (p.1, realProjectiveMap p.2),
    continuous_fst.prodMk (S.continuous.comp continuous_snd)⟩

end MathlibExt.AlgebraicGeometry.ProjectiveExponentialSectionModels
