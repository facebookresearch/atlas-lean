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

/-!
# Concrete vertical Cartier models and nonarchimedean model formulas

A model is an actual proper birational scheme over X×P¹. Its parameter
is the pullback of the actual affine coordinate, its divisor is an actual
vertical Cartier divisor, and its polarization is computed as the pulled
base polarization tensored with the completed O(D) sheaf. Model values,
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
open scoped BigOperators

variable {k : Type} [Field k] {n : ℕ}

/-- A fixed actual projective line and an actual affine-coordinate open chart. -/
structure ProjectiveParameter where
  line : Over (Spec (.of k))
  comparison : line ≅ SurfaceHilbertSchemes.projectiveSpace k 1
  affineChart : AffineLine k ⟶ line
  [openChart : IsOpenImmersion affineChart.left]

/-- A literal Cartier multiple of an actual prime divisor. -/
structure PrimeCartierMultiple (W : NormalVariety k (n + 1)) (p : PrimePoint W) where
  index : ℕ
  positive : 0 < index
  [dvr : ∀ q : PrimePoint W, IsDiscreteValuationRing (LocalRing W q.val)]
  line : IsLineBundle
    (DivisorialModuleSheaves.sheaf W (Finsupp.single p (index : ℤ)))

/-- Proper birational vertical-Cartier model; all metric data are actual schemes and divisors. -/
structure VerticalModel (P : LogPair k n) (L : P.variety.X.left.Modules) where
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

/-- Actual projection to the polarized base variety. -/
def baseProjection {P : LogPair k n} {L : P.variety.X.left.Modules} (M : VerticalModel P L) :=
  M.map ≫ fst P.variety.X M.parameter.line

/-- Literal generic-point stalk map; no free function-field embedding. -/
def fieldMap {P : LogPair k n} {L : P.variety.X.left.Modules} (M : VerticalModel P L) :
    FunctionField P.variety →+* FunctionField M.model :=
  (eqToHom (congrArg (fun x => P.variety.X.left.presheaf.stalk x) M.dominant.symm) ≫
    (baseProjection M).left.stalkMap (genericPoint M.model.X.left)).hom

/-- The actual polarization is pulled L^r tensored with actual O(D). -/
def modelPolarization {P : LogPair k n} {L : P.variety.X.left.Modules}
    (M : VerticalModel P L) : M.model.X.left.Modules := by
  letI := M.dvr
  exact moduleTensor M.model.X.left
    ((Scheme.Modules.pullback (baseProjection M).left).obj (power L M.exponent))
    (DivisorialModuleSheaves.sheaf M.model M.divisor)

/-- The base volume is the actual Euler-intersection difference of the base line. -/
def baseVolume (P : LogPair k n) (L : P.variety.X.left.Modules) : ℝ :=
  DivisorDynamics.mixedIntersection P.variety.X n (fun _ => L)

/-- Actual normalized model function value at a central divisorial valuation. -/
def modelValue {P : LogPair k n} {L : P.variety.X.left.Modules}
    (M : VerticalModel P L) (p : PrimePoint M.model) : ℝ :=
  (M.divisor p : ℝ) /
    ((M.exponent : ℝ) * (M.model.X.left.ord (M.rationalParameter : FunctionField M.model) p.val))

/-- Actual intersection with a central component, using its fixed Cartier multiple. -/
def componentIntersection {P : LogPair k n} {L : P.variety.X.left.Modules}
    (M : VerticalModel P L) (p : PrimePoint M.model) (hp : p ∈ M.central) : ℝ := by
  letI := M.dvr
  let C := M.primeCartier p hp
  exact (DivisorDynamics.mixedIntersection M.model.X (n+1)
    (fun i => if i.val = 0 then
      DivisorialModuleSheaves.sheaf M.model (Finsupp.single p (C.index : ℤ))
      else modelPolarization M) : ℝ) / C.index

/-- The actual central Monge--Ampère mass, not a supplied numerical weight. -/
def componentMass {P : LogPair k n} {L : P.variety.X.left.Modules}
    (M : VerticalModel P L) (p : PrimePoint M.model) (hp : p ∈ M.central) : ℝ :=
  (M.model.X.left.ord (M.rationalParameter : FunctionField M.model) p.val : ℝ) *
    componentIntersection M p hp / ((M.exponent : ℝ)^n * baseVolume P L)

/-- Actual intersection energy of the compactified model polarization. -/
def energy {P : LogPair k n} {L : P.variety.X.left.Modules}
    (M : VerticalModel P L) : ℝ :=
  (DivisorDynamics.mixedIntersection M.model.X (n+1) (fun _ => modelPolarization M) : ℝ) /
    ((n+1 : ℕ) * (M.exponent : ℝ)^(n+1) * baseVolume P L)

/-- Actual geometric divisorial valuation induced by the component and its field map. -/
structure ComponentValuation {P : LogPair k n} {L : P.variety.X.left.Modules}
    (M : VerticalModel P L) (p : PrimePoint M.model) (hp : p ∈ M.central) where
  valuation : CenteredValuation P.variety
  center : valuation.center = (baseProjection M).left p.val
  normalized : ∀ a : (FunctionField P.variety)ˣ,
    order valuation a =
      (M.model.X.left.ord (fieldMap M a) p.val : ℝ) /
        (M.model.X.left.ord (M.rationalParameter : FunctionField M.model) p.val : ℝ)

/-- Entropy uses the actual normalized component valuations and discrepancy supremum. -/
def entropy {P : LogPair k n} {L : P.variety.X.left.Modules}
    (M : VerticalModel P L) (V : ∀ p (hp : p ∈ M.central), ComponentValuation M p hp) : EReal :=
  ∑ p : {p : PrimePoint M.model // p ∈ M.central},
    (componentMass M p.val p.property : EReal) * extendedDiscrepancy (V p.val p.property).valuation

end MathlibExt.AlgebraicGeometry.NonarchimedeanCartierModels

