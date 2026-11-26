/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PolarizedTestConfigurations
public import MathlibExt.AlgebraicGeometry.DivisorialModuleSheaves
public import MathlibExt.AlgebraicGeometry.MonomialModelRetractions
public import MathlibExt.AlgebraicGeometry.DivisorDynamics
public import MathlibExt.AlgebraicGeometry.LineBundleTensor
public import MathlibExt.AlgebraicGeometry.ProjectiveSpace

/-!
# Concrete vertical Cartier models and nonarchimedean model formulas

A model is an actual proper birational scheme over X×P¹. Its parameter
is the pullback of the actual affine coordinate, its divisor is an actual
vertical Cartier divisor, and its polarization is computed as the pulled
base polarization tensored with the completed O(D) sheaf. The base
polarization L is an ample line bundle on the proper base, which is part
of every model, so the model polarization is a line bundle and the Euler
differences below are intersection numbers of line bundles. The central
components are Gauss, so model values are values at base valuations. Monge--Ampère
masses and entropy are defined for semipositive models (relatively nef polarization
over ℙ¹), as in BHJ. Model values,
Monge--Ampère weights, energy and entropy are computed from actual orders,
Euler-intersection differences and actual valuation discrepancies.

There is no supplied metric, energy, entropy or weight function. Passing
from a test configuration to a dominating compatible model, proving model
independence and assembling completed metric spaces are separate normalized
provider/comparison boundaries. Generic projective charts, Cartier/O(D),
DVR valuations and intersections are positively reused.

Source: Boucksom--Hisamoto--Jonsson, arXiv1504.06568v3,
Definitions 6.1/6.11 and Theorem C.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NonarchimedeanCartierModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.PolarizedTestConfigurations
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open MathlibExt.AlgebraicGeometry.CenteredValuationSections
open MathlibExt.AlgebraicGeometry.MonomialModelRetractions
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
open scoped BigOperators

variable {k : Type} [Field k] {n : ℕ}

/-- A fixed actual projective line and an actual affine-coordinate open chart. -/
structure ProjectiveParameter where
  line : Over (Spec (.of k))
  comparison : line ≅ ProjectiveSpace.projectiveSpace k 1
  affineChart : AffineLine k ⟶ line
  [openChart : IsOpenImmersion affineChart.left]

/-- A literal Cartier multiple of an actual prime divisor. -/
structure PrimeCartierMultiple (W : NormalVariety k (n + 1)) (p : PrimePoint W) where
  index : ℕ
  positive : 0 < index
  [dvr : ∀ q : PrimePoint W, IsDiscreteValuationRing (LocalRing W q.val)]
  line : IsLineBundle
    (DivisorialModuleSheaves.sheaf W (Finsupp.single p (index : ℤ)))

/-- The volume `(Lⁿ)` of a line bundle on the proper base, as Snapper's Euler-characteristic
difference. -/
def baseVolume (P : LogPair k n) [IsProper P.variety.X.hom] (L : LineBundle P.variety.X.left) :
    ℝ :=
  DivisorDynamics.mixedIntersection P.variety.X n P.variety.dimension.le (fun _ => L)

/-- The function-field map `K(X) → K(Y)` of a dominant morphism `Y ⟶ X` of varieties: the
literal generic-point stalk map. -/
def dominantFieldMap {d d' : ℕ} {V : NormalVariety k d} {W : NormalVariety k d'}
    (f : W.X ⟶ V.X) (h : f.left (genericPoint W.X.left) = genericPoint V.X.left) :
    FunctionField V →+* FunctionField W :=
  (eqToHom (congrArg (fun x => V.X.left.presheaf.stalk x) h.symm) ≫
    f.left.stalkMap (genericPoint W.X.left)).hom

/-- Gauss compatibility at a prime divisor `p` of `W`, for `φ : K(V) → K(W)` and `t ∈ K(W)`: the
order at `p` of `∑ aᵢ tⁱ` is `minᵢ (ord_p (φ aᵢ) + i · ord_p t)`. For the central components of a
`𝔾ₘ`-equivariant model of `X × ℙ¹` this holds with `t` the coordinate (BHJ, Lemma 4.7): their
valuations are Gauss extensions of their restrictions to `K(X)`. -/
def IsGaussAt {d d' : ℕ} {V : NormalVariety k d} {W : NormalVariety k d'}
    (φ : FunctionField V →+* FunctionField W) (t : FunctionField W) (p : PrimePoint W) : Prop :=
  ∀ (q : Polynomial (FunctionField V)) (hq : q ≠ 0),
    W.X.left.ord (Polynomial.eval₂ φ t q) p.val =
      q.support.inf' (Polynomial.support_nonempty.mpr hq) fun i =>
        W.X.left.ord (φ (q.coeff i)) p.val + i * W.X.left.ord t p.val

/-- A proper birational model of `X × ℙ¹` with a vertical Cartier divisor, for the polarized
proper variety `(X, L)`: `L` is an ample line bundle (so `(Lⁿ) > 0`), the model polarization
`modelPolarization` (pulled-back `L^r` twisted by `𝒪(D)`) is a line bundle
(`modelPolarization_isLineBundle`), and the normalized intersection functionals are defined.

The central components are Gauss (`gauss`): each component valuation is the Gauss extension of
its restriction to `K(X)`, as for the components of a `𝔾ₘ`-equivariant model (BHJ, Lemma 4.7).
So distinct central components have distinct restrictions and `modelValue` is a function of the
base valuation; an arbitrary birational model need not have this property. -/
structure VerticalModel (P : LogPair k n) (L : P.variety.X.left.Modules) where
  [baseProper : IsProper P.variety.X.hom]
  polarization : IsLineBundle L
  ample : ProjectiveLineSystems.IsAmpleLine ⟨L, polarization⟩
  parameter : ProjectiveParameter (k := k)
  model : NormalVariety k (n+1)
  [properOverField : IsProper model.X.hom]
  map : model.X ⟶ P.variety.X ⊗ parameter.line
  [proper : IsProper map.left]
  birational : MathlibExt.AlgebraicGeometry.BirationalResolution.IsBirationalMorphism map.left
  [dvr : ∀ q : PrimePoint model, IsDiscreteValuationRing (LocalRing model q.val)]
  exponent : ℕ
  positiveExponent : 0 < exponent
  affineOpen : model.X.left.Opens
  nonemptyOpen : Nonempty affineOpen
  affineProjection : Over.mk (affineOpen.ι ≫ model.X.hom) ⟶ AffineLine k
  projection_normalized : affineProjection ≫ parameter.affineChart =
    Over.homMk affineOpen.ι ≫ map ≫ snd P.variety.X parameter.line
  rationalParameter : (FunctionField model)ˣ
  parameter_normalized :
    letI := nonemptyOpen
    (rationalParameter : FunctionField model) =
      model.X.left.germToFunctionField affineOpen
        (affineOpen.topIso.hom
          (affineProjection.left.appTop
            ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X)))
  central : Finset (PrimePoint model)
  central_normalized : ∀ p, p ∈ central ↔ 0 <
    model.X.left.ord (rationalParameter : FunctionField model) p.val
  divisor : IntegerWeil model
  vertical : ∀ p, divisor p ≠ 0 → p ∈ central
  cartier : IsLineBundle (DivisorialModuleSheaves.sheaf model divisor)
  primeCartier : ∀ p ∈ central, PrimeCartierMultiple model p
  dominant : (map ≫ fst P.variety.X parameter.line).left
    (genericPoint model.X.left) = genericPoint P.variety.X.left
  gauss : ∀ p ∈ central,
    IsGaussAt (dominantFieldMap (map ≫ fst P.variety.X parameter.line) dominant)
      (rationalParameter : FunctionField model) p

/-- Actual projection to the polarized base variety. -/
def baseProjection {P : LogPair k n} {L : P.variety.X.left.Modules} (M : VerticalModel P L) :=
  M.map ≫ fst P.variety.X M.parameter.line

/-- Literal generic-point stalk map; no free function-field embedding. -/
def fieldMap {P : LogPair k n} {L : P.variety.X.left.Modules} (M : VerticalModel P L) :
    FunctionField P.variety →+* FunctionField M.model :=
  dominantFieldMap (baseProjection M) M.dominant

/-- The actual polarization is pulled L^r tensored with actual O(D). -/
def modelPolarization {P : LogPair k n} {L : P.variety.X.left.Modules}
    (M : VerticalModel P L) : M.model.X.left.Modules := by
  letI := M.dvr
  exact moduleTensor M.model.X.left
    ((Scheme.Modules.pullback (baseProjection M).left).obj (power L M.exponent))
    (DivisorialModuleSheaves.sheaf M.model M.divisor)

/-- The model polarization is a line bundle: the tensor product of the pulled-back line bundle
`L^r` and the Cartier sheaf `𝒪(D)`. -/
theorem modelPolarization_isLineBundle {P : LogPair k n} {L : P.variety.X.left.Modules}
    (M : VerticalModel P L) : IsLineBundle (modelPolarization M) := by
  letI := M.dvr
  exact ((M.polarization.power M.exponent).pullback (baseProjection M).left).moduleTensor
    M.cartier

/-- The model polarization as a line bundle. -/
def modelPolarizationLine {P : LogPair k n} {L : P.variety.X.left.Modules}
    (M : VerticalModel P L) : LineBundle M.model.X.left :=
  ⟨modelPolarization M, modelPolarization_isLineBundle M⟩

/-- The base polarization as a line bundle. -/
def baseLine {P : LogPair k n} {L : P.variety.X.left.Modules} (M : VerticalModel P L) :
    LineBundle P.variety.X.left :=
  ⟨L, M.polarization⟩

/-- Actual normalized model function value at a central component `p`: `D_p / (r · ord_p(t))`.
Centrality (`hp`) makes the denominator positive (`central_normalized`). -/
def modelValue {P : LogPair k n} {L : P.variety.X.left.Modules}
    (M : VerticalModel P L) (p : PrimePoint M.model) (_hp : p ∈ M.central) : ℝ :=
  (M.divisor p : ℝ) /
    ((M.exponent : ℝ) * (M.model.X.left.ord (M.rationalParameter : FunctionField M.model) p.val))

/-- Actual intersection with a central component, using its fixed Cartier multiple. -/
def componentIntersection {P : LogPair k n} {L : P.variety.X.left.Modules}
    (M : VerticalModel P L) (p : PrimePoint M.model) (hp : p ∈ M.central) : ℝ := by
  letI := M.dvr
  haveI := M.properOverField
  let C := M.primeCartier p hp
  exact (DivisorDynamics.mixedIntersection M.model.X (n+1) M.model.dimension.le
    (fun i => if i.val = 0 then
      ⟨DivisorialModuleSheaves.sheaf M.model (Finsupp.single p (C.index : ℤ)), C.line⟩
      else modelPolarizationLine M) : ℝ) / C.index

/-- The model is semipositive (BHJ's semipositive model metrics): its polarization is relatively
nef over `ℙ¹`, i.e. has nonnegative degree on every curve that the projection to `ℙ¹` contracts
to a point. -/
def IsSemipositive {P : LogPair k n} {L : P.variety.X.left.Modules} (M : VerticalModel P L) :
    Prop :=
  ∀ C : NumericalCurveCones.Curve M.model.X,
    (Set.range (C.map.left ≫ (M.map ≫ snd P.variety.X M.parameter.line).left).base).Subsingleton →
      0 ≤ NumericalCurveCones.curveDegrees C (modelPolarizationLine M)

/-- The actual central Monge--Ampère mass of a semipositive model, not a supplied numerical
weight: `ord_E(t) · (E · ℒⁿ) / (rⁿ (Lⁿ))`. Semipositivity (`IsSemipositive`) makes it
nonnegative; without it this coefficient can be negative and is not a Monge--Ampère mass. -/
def componentMass {P : LogPair k n} {L : P.variety.X.left.Modules}
    (M : VerticalModel P L) (_hM : IsSemipositive M) (p : PrimePoint M.model)
    (hp : p ∈ M.central) : ℝ :=
  (M.model.X.left.ord (M.rationalParameter : FunctionField M.model) p.val : ℝ) *
    componentIntersection M p hp /
      ((M.exponent : ℝ)^n * (haveI := M.baseProper; baseVolume P (baseLine M)))

/-- Actual intersection energy of the compactified model polarization. -/
def energy {P : LogPair k n} {L : P.variety.X.left.Modules}
    (M : VerticalModel P L) : ℝ :=
  haveI := M.properOverField
  haveI := M.baseProper
  (DivisorDynamics.mixedIntersection M.model.X (n+1) M.model.dimension.le
      (fun _ => modelPolarizationLine M) : ℝ) /
    ((n+1 : ℕ) * (M.exponent : ℝ)^(n+1) * baseVolume P (baseLine M))

/-- Actual geometric divisorial valuation induced by the component and its field map. Its
discrepancy is computed by charts (`charts`), so that `entropy` uses actual discrepancies. -/
structure ComponentValuation {P : LogPair k n} {L : P.variety.X.left.Modules}
    (M : VerticalModel P L) (p : PrimePoint M.model) (hp : p ∈ M.central) where
  valuation : CenteredValuation P.variety
  charts : HasDiscrepancyCharts valuation
  center : valuation.center = (baseProjection M).left p.val
  normalized : ∀ a : (FunctionField P.variety)ˣ,
    order valuation a =
      (M.model.X.left.ord (fieldMap M a) p.val : ℝ) /
        (M.model.X.left.ord (M.rationalParameter : FunctionField M.model) p.val : ℝ)

/-- The entropy of a semipositive model: the Monge--Ampère masses weighted by the actual
normalized component valuations' discrepancies (BHJ's nonarchimedean entropy). -/
def entropy {P : LogPair k n} {L : P.variety.X.left.Modules}
    (M : VerticalModel P L) (hM : IsSemipositive M)
    (V : ∀ p (hp : p ∈ M.central), ComponentValuation M p hp) : EReal :=
  ∑ p : {p : PrimePoint M.model // p ∈ M.central},
    (componentMass M hM p.val p.property : EReal) *
      extendedDiscrepancy (V p.val p.property).valuation

end MathlibExt.AlgebraicGeometry.NonarchimedeanCartierModels
