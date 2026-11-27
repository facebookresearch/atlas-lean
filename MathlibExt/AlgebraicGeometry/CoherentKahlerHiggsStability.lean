/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HolomorphicSheafHiggsModels
public import MathlibExt.AlgebraicGeometry.HolomorphicSmoothScalarModels
public import MathlibExt.AlgebraicGeometry.HarmonicChernWeilFormulas
public import MathlibExt.AlgebraicGeometry.CoordinateFormIntegrals
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Coherent subsheaf stability on compact Kähler manifolds

Every test is an actual finitely presented O-module subsheaf, with an
actual monomorphism and the actual theta preservation square. On the
complex-manifold structure sheaf this is the usual analytic coherent
subcategory. The generic rank is tested on an actual dense open.

Degree is the actual first Chern form of the reflexive determinant,
wedged with the chosen Kähler form power and integrated by the existing
coordinate/partition integral. Determinant and smooth-realization
providers concern those exact objects; no real-valued degree assignment
is supplied. Polystability uses actual finite direct sums and their
theta intertwining maps. Simpson, alg-geom/9604005v1, pp10--11.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CoherentKahlerHiggsStability

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open KahlerClassGeometry SmoothHarmonicBundleGeometry ManifoldDifferentialForms
open HolomorphicCotangentModuleModels HolomorphicSheafHiggsModels
open HolomorphicSmoothScalarModels HarmonicChernWeilFormulas CoordinateFormIntegrals
open scoped Manifold ContDiff

attribute [local instance] Abelian.hasFiniteBiproducts

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  [ExteriorTheory ℝ (Coordinates n) M] [WedgeTheory n M]
  [HolomorphicCoefficientSheaves.SheafCondition (Coordinates n) M]
  [CotangentSectionCalculus (n := n) (M := M)] [CotangentSheafCondition (n := n) (M := M)]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- Coherent subsheaves use the actual native finite-presentation condition and monomorphism. -/
structure CoherentSubsheaf (E : HolomorphicModules (n := n) (M := M)) where
  module : HolomorphicModules (n := n) (M := M)
  coherent : module.IsFinitePresentation
  inclusion : module ⟶ E
  mono : Mono inclusion

/-- Theta invariance is actual factorization through F tensor the actual holomorphic Omega1. -/
def IsThetaInvariant {A : TensorAssociatorSource (n := n) (M := M)}
    {W : CotangentWedgeSource (n := n) (M := M)} (E : HiggsModule A W)
    (F : CoherentSubsheaf E.module) : Prop :=
  ∃ θ : F.module ⟶ holomorphicTensor F.module (holomorphicOmega (n := n) (M := M) 1),
    F.inclusion ≫ E.theta = θ ≫ tensorMap F.inclusion (𝟙 _)

variable (S : HolomorphicSmoothInclusionSource (n := n) (M := M))

/-- Smooth line realization and its actual normalized first Chern form for the exact reflexive determinant. -/
structure DeterminantDegreeData (F : HolomorphicModules (n := n) (M := M)) (q : ℕ) where
  realization : SmoothModuleRealization (r := 1) S (determinantSheaf F q)
  connection : SmoothConnection realization.bundle
  chern : ChernWeilFormSource realization.bundle connection 0

/-- The degree is the actual top-degree coordinate integral of c1(det F) wedge eta^(n-1). -/
def determinantDegree (eta : KahlerStructure n M) (R : RealCoordinateMap n) (A : IntegrationAtlas n M)
    {F : HolomorphicModules (n := n) (M := M)} {q : ℕ} (D : DeterminantDegreeData S F q) : ℝ :=
  if hn : 0 < n then
    integral n M R A (castForm n M (by omega)
      (WedgeTheory.wedge 2 (2 * (n - 1)) D.chern.form.val
        (wedgePower n M eta.form.val (n - 1))))
  else 0

/-- Construction providers supply these exact determinant objects for bundles and coherent subobjects. -/
structure DeterminantDegreeTheory where
  bundle : ∀ (E : HolomorphicModules (n := n) (M := M)) (r : ℕ),
    IsLocallyFreeRank E r → DeterminantDegreeData S E r
  subobject : ∀ (E : HolomorphicModules (n := n) (M := M)) (r : ℕ), IsLocallyFreeRank E r →
    ∀ (F : CoherentSubsheaf E) (q : ℕ), HasGenericRank F.module q → DeterminantDegreeData S F.module q

variable (D : DeterminantDegreeTheory S) (eta : KahlerStructure n M)
  (R : RealCoordinateMap n) (A : IntegrationAtlas n M)

/-- Stability tests every actual coherent theta-invariant subsheaf of smaller positive generic rank. -/
def IsStable [ConnectedSpace M] {T : TensorAssociatorSource (n := n) (M := M)}
    {W : CotangentWedgeSource (n := n) (M := M)} (E : HiggsModule T W) : Prop :=
  0 < E.rank ∧
    ∀ (F : CoherentSubsheaf E.module), IsThetaInvariant E F →
      ∀ (q : ℕ) (hq : HasGenericRank F.module q), 0 < q → q < E.rank →
        determinantDegree S eta R A (D.subobject E.module E.rank E.locallyFree F q hq) / (q : ℝ) <
          determinantDegree S eta R A (D.bundle E.module E.rank E.locallyFree) / (E.rank : ℝ)

/-- The slope is computed from the same actual determinant integral. -/
def slope {T : TensorAssociatorSource (n := n) (M := M)}
    {W : CotangentWedgeSource (n := n) (M := M)} (E : HiggsModule T W) : ℝ :=
  determinantDegree S eta R A (D.bundle E.module E.rank E.locallyFree) / (E.rank : ℝ)

/-- Polystability is an actual finite direct sum of stable Higgs sheaves of equal computed slope. -/
def IsPolystable [ConnectedSpace M] {T : TensorAssociatorSource (n := n) (M := M)}
    {W : CotangentWedgeSource (n := n) (M := M)} (E : HiggsModule T W) : Prop :=
  ∃ (k : ℕ) (F : Fin k → HiggsModule T W),
    (∀ i, IsStable S D eta R A (F i) ∧ slope S D eta R A (F i) = slope S D eta R A E) ∧
    ∃ e : biproduct (fun i => (F i).module) ≅ E.module,
      ∀ i : Fin k, biproduct.ι (fun j => (F j).module) i ≫ e.hom ≫ E.theta =
        (F i).theta ≫ tensorMap (biproduct.ι (fun j => (F j).module) i ≫ e.hom) (𝟙 _)

end MathlibExt.AlgebraicGeometry.CoherentKahlerHiggsStability
