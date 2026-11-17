/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticProperSmoothSources
public import MathlibExt.CategoryTheory.NativeRingInverseImages
public import MathlibExt.RingTheory.ContinuousDeRhamQuotients

/-!
# Analytic affinoid source normalization for relative de Rham outputs

Continuous quotient differentials are fixed on EVERY original affinoid
chart of the etale site and glued as an actual module sheaf. Arbitrary
global section rings are never identified with raw Kaehler forms.
Coefficient connections and filtered bundles are BASE input. The native
cochain source has exactly E tensor Omega^n, the completed public native
extended connection on all those charts, and the original filtered term
images. It supplies no higher bundle, filtration or Gauss--Manin output.

References: Scholze, arXiv:1205.3463v2, Definitions 6.8 and 7.4,
Proposition 8.5 and Theorem 8.8; completed Atlas PR2245
`76de3f2665f9c44b06932f9861ee9aae65e04395`, AxiomMath/Stacks
`c496df0d9beea9deaeabcea8492605f9a0a2313b`, Apache 2.0.
Native Mathlib, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticRelativeDeRhamSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open AnalyticTateAdicModels AnalyticDiamondEtaleSites
open AnalyticProEtaleCoefficientSources AnalyticProperSmoothSources
open MathlibExt.CategoryTheory.RingedDerivedCoefficientOperations
open MathlibExt.CategoryTheory.RingSheafModuleTensors
open MathlibExt.CategoryTheory.NativeRingInverseImages
open MathlibExt.CategoryTheory.NativeFilteredDeRhamOutputs
open MathlibExt.RingTheory.ContinuousDeRhamQuotients
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] {X Y : AnalyticAdicSpace p} (f : X ⟶ Y)

/-- Every chart uses the original analytic etale object and original morphism. -/
structure RelativeAffinoid (U : Etale p X) where
  source : Chart p U.obj.left
  [whole : IsIso source.map]
  target : Chart p Y
  map : AffinoidMap p source target
  square : source.map ≫ U.obj.hom.hom ≫ f.hom = map.valued ≫ target.map
  coordinates : ULift.{1} source.pair.ring ≃+* (etaleRingsLarge p X).obj (op U)
  coordinate_source : ∀ a : source.pair.ring,
    ((source.map.val.c.app (op ⊤)).hom)
      (coordinates (ULift.up a)).down = source.model.globalRing a

attribute [instance] RelativeAffinoid.whole

def liftRingHom {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) :
    ULift.{1} A →+* ULift.{1} B :=
  (liftRings.map (CommRingCat.ofHom g)).hom

variable (E : AnalyticProperSmoothSources.EtaleBaseChangeSource p f)
  (hX : Presheaf.IsSheaf (analyticEtaleTopology p X) (etaleRingsLarge p X))
  (hY : Presheaf.IsSheaf (analyticEtaleTopology p Y) (etaleRingsLarge p Y))
  [E.functor.IsContinuous (analyticEtaleTopology p Y) (analyticEtaleTopology p X)]
  [(E.functor.sheafPushforwardContinuous CommRingCat.{1}
    (analyticEtaleTopology p Y) (analyticEtaleTopology p X)).IsRightAdjoint]

/-- Γ of every original analytic pullback gives the original ringed-site scalar map. -/
def regularScalar : regularEtale p Y hY ⟶
    (E.functor.sheafPushforwardContinuous CommRingCat.{1}
      (analyticEtaleTopology p Y) (analyticEtaleTopology p X)).obj (regularEtale p X hX) :=
  ObjectProperty.homMk (Functor.whiskerRight (E.regularScalar) liftRings)

def relativeRing : Sheaf (analyticEtaleTopology p X) CommRingCat.{1} :=
  inverseRing E.functor (regularEtale p Y hY)

def relativeScalar : relativeRing p f E hY ⟶ regularEtale p X hX :=
  inverseScalar E.functor (regularEtale p Y hY) (regularEtale p X hX)
    (regularScalar p f E hX hY)

variable [HasSheafify (analyticEtaleTopology p X) AddCommGrpCat.{1}]
  [(analyticEtaleTopology p X).WEqualsLocallyBijective AddCommGrpCat.{1}]

abbrev O := regularEtale p X hX

section Local

variable (M Ω : Modules (O p hX)) (U : Etale p X) (A : RelativeAffinoid p f U)

local instance affineAlgebra :
    Algebra (ULift.{1} A.target.pair.ring) (ULift.{1} A.source.pair.ring) :=
  (liftRingHom A.map.ring.hom).toAlgebra

local instance coefficientModule : Module (ULift.{1} A.source.pair.ring) (M.val.obj (op U)) :=
  Module.compHom (M.val.obj (op U)) A.coordinates.toRingHom

/-- A local continuous form and connection model on the ORIGINAL affinoid rings. -/
structure AffineConnection where
  quotient : ContinuousQuotient (ULift.{1} A.target.pair.ring) (ULift.{1} A.source.pair.ring)
  omega : quotient.omega →ₛₗ[A.coordinates.toRingHom] Ω.val.obj (op U)
  omega_bijective : Function.Bijective omega
  connection : quotient.NativeConnection (M.val.obj (op U))
  integrable : quotient.IsIntegrable (M.val.obj (op U)) connection
  terms : ∀ n : ℕ,
    (M.val.obj (op U) ⊗[ULift.{1} A.source.pair.ring] (⋀[ULift.{1} A.source.pair.ring]^n quotient.omega)) →+
      (tensor (O p hX) M (exterior (O p hX) Ω n)).val.obj (op U)
  terms_bijective : ∀ n : ℕ, Function.Bijective (terms n)
  terms_source : ∀ (n : ℕ) (m : M.val.obj (op U))
    (w : ⋀[ULift.{1} A.source.pair.ring]^n quotient.omega),
    terms n (m ⊗ₜ[ULift.{1} A.source.pair.ring] w) =
      generator (O p hX) M (exterior (O p hX) Ω n) (op U) m
        (exteriorUnit (O p hX) Ω n (op U)
          (ExteriorAlgebra.powMapₛₗ n A.coordinates.toRingHom omega w))

end Local

/-- A global continuous differential sheaf is pinned on ALL original affinoid etale charts. -/
structure DifferentialSource where
  oneForms : Modules (O p hX)
  differential : ∀ U : (Etale p X)ᵒᵖ, (O p hX).obj.obj U →+ oneForms.val.obj U
  natural : ∀ {U V : (Etale p X)ᵒᵖ} (g : U ⟶ V) (a : (O p hX).obj.obj U),
    differential V (((O p hX).obj.map g).hom a) = oneForms.val.map g (differential U a)
  leibniz : ∀ U a b, differential U (a * b) = a • differential U b + b • differential U a
  affinoid : ∀ (U : Etale p X) (A : RelativeAffinoid p f U),
    letI := (liftRingHom A.map.ring.hom).toAlgebra
    ContinuousQuotient (ULift.{1} A.target.pair.ring) (ULift.{1} A.source.pair.ring)
  omega : ∀ (U : Etale p X) (A : RelativeAffinoid p f U),
    letI := (liftRingHom A.map.ring.hom).toAlgebra
    (affinoid U A).omega →ₛₗ[A.coordinates.toRingHom] oneForms.val.obj (op U)
  omega_bijective : ∀ U A,
    letI := (liftRingHom A.map.ring.hom).toAlgebra
    Function.Bijective (omega U A)
  differential_source : ∀ (U : Etale p X) (A : RelativeAffinoid p f U)
    (a : ULift.{1} A.source.pair.ring),
    letI := (liftRingHom A.map.ring.hom).toAlgebra
    omega U A ((affinoid U A).quotient
      (_root_.KaehlerDifferential.D (ULift.{1} A.target.pair.ring) (ULift.{1} A.source.pair.ring) a)) =
        differential (op U) (A.coordinates a)

/-- All E, connection and filtration fields here are BASE data, never higher outputs. -/
structure BaseCoefficientInput (Ω : DifferentialSource p f hX) where
  module : Modules (O p hX)
  finiteLocallyFree : MathlibExt.CategoryTheory.FiniteLocallyFreeSource.IsFiniteLocallyFree (O p hX) module
  filtration : CoefficientFiltration (O p hX) module
  connection : ∀ U : (Etale p X)ᵒᵖ, module.val.obj U →+
    (tensor (O p hX) module Ω.oneForms).val.obj U
  connection_natural : ∀ {U V : (Etale p X)ᵒᵖ} (g : U ⟶ V) (m : module.val.obj U),
    connection V (module.val.map g m) =
      (tensor (O p hX) module Ω.oneForms).val.map g (connection U m)
  leibniz : ∀ U a m, connection U (a • m) = a • connection U m +
    generator (O p hX) module Ω.oneForms U m (Ω.differential U a)
  localModel : ∀ (U : Etale p X) (A : RelativeAffinoid p f U),
    AffineConnection p f hX module Ω.oneForms U A
  local_forms : ∀ U A,
    letI := (liftRingHom A.map.ring.hom).toAlgebra
    (localModel U A).quotient = Ω.affinoid U A
  local_omega : ∀ U A,
    letI := (liftRingHom A.map.ring.hom).toAlgebra
    HEq (localModel U A).omega (Ω.omega U A)
  locally_split : ∀ (j : ℤ) (U : (Etale p X)ᵒᵖ),
    ∃ S : Sieve U.unop, S ∈ analyticEtaleTopology p X U.unop ∧
      ∀ (V : Etale p X) (g : V ⟶ U.unop), S g →
        ∃ N : Submodule ((O p hX).obj.obj (op V)) (module.val.obj (op V)),
          IsCompl ((filtration.pieces j).toSubmodule.obj (op V)) N
  griffiths : ∀ (j : ℤ) (U : (Etale p X)ᵒᵖ) (m : module.val.obj U),
    m ∈ (filtration.pieces j).toSubmodule.obj U →
      connection U m ∈ LinearMap.range
        ((image.ι ((tensorFunctor (O p hX) Ω.oneForms).map
          (filtration.pieces (j - 1)).ι)).val.app U).hom
  oneFormIdentification : tensor (O p hX) module Ω.oneForms ≅
    tensor (O p hX) module (exterior (O p hX) Ω.oneForms 1)
  oneForm_source : ∀ U m w,
    ((oneFormIdentification.hom.val.app U).hom)
      (generator (O p hX) module Ω.oneForms U m w) =
      generator (O p hX) module (exterior (O p hX) Ω.oneForms 1) U m
        (exteriorUnit (O p hX) Ω.oneForms 1 U
          ((_root_.exteriorPower.oneEquiv ((O p hX).obj.obj U) (Ω.oneForms.val.obj U)).symm w))
  connection_source : ∀ U A,
    letI := (liftRingHom A.map.ring.hom).toAlgebra
    letI := Module.compHom (module.val.obj (op U)) A.coordinates.toRingHom
    ∀ m : module.val.obj (op U),
    (localModel U A).terms 1
      (TensorProduct.map LinearMap.id
        (_root_.exteriorPower.oneEquiv (ULift.{1} A.source.pair.ring)
          (localModel U A).quotient.omega).symm.toLinearMap ((localModel U A).connection m)) =
      (oneFormIdentification.hom.val.app (op U)).hom (connection (op U) m)

section ComplexSources

variable (Ω : DifferentialSource p f hX) (M : BaseCoefficientInput p f hX Ω)

/-- The filtered degree map uses the ORIGINAL coefficient filtration and native tensor functor. -/
def filteredTermMap (j : ℤ) (n : ℕ) :=
  (restrict (relativeRing p f E hY) (O p hX) (relativeScalar p f E hX hY)).map
    ((tensorFunctor (O p hX) (exterior (O p hX) Ω.oneForms n)).map
      (M.filtration.pieces (j - (n : ℤ))).ι)

/-- A construction request for the actual native coefficient cochains, with all local arrows fixed. -/
structure FilteredDeRhamSource where
  native : FilteredComplex (relativeRing p f E hY)
  terms : ∀ n : ℕ, native.total.obj.X (n : ℤ) ≅
    term (relativeRing p f E hY) (O p hX) (relativeScalar p f E hX hY)
      M.module Ω.oneForms n
  negative_zero : ∀ i : ℤ, i < 0 → IsZero (native.total.obj.X i)
  filtered_terms : ∀ (j : ℤ) (n : ℕ), (native.filtered.obj (op j)).obj.X (n : ℤ) ≅
    image (filteredTermMap p f E hX hY Ω M j n)
  filtered_source : ∀ (j : ℤ) (n : ℕ),
    ((native.inclusion.app (op j)).hom.f (n : ℤ)) ≫ (terms n).hom =
      (filtered_terms j n).hom ≫ image.ι (filteredTermMap p f E hX hY Ω M j n)
  differential_source : ∀ (U : Etale p X) (A : RelativeAffinoid p f U),
    letI := (liftRingHom A.map.ring.hom).toAlgebra
    letI := Module.compHom (M.module.val.obj (op U)) A.coordinates.toRingHom
    ∀ (n : ℕ) (x : M.module.val.obj (op U) ⊗[ULift.{1} A.source.pair.ring]
      (⋀[ULift.{1} A.source.pair.ring]^n (M.localModel U A).quotient.omega)),
      (((terms (n + 1)).hom.val.app (op U)).hom)
        (((native.total.obj.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).val.app (op U)).hom
          (((terms n).inv.val.app (op U)).hom ((M.localModel U A).terms n x))) =
      (M.localModel U A).terms (n + 1)
        (RestrictScalars.addEquiv (ULift.{1} A.target.pair.ring) (ULift.{1} A.source.pair.ring) _
          (((M.localModel U A).quotient.extended (M.module.val.obj (op U))
            (M.localModel U A).connection).toLinearMap n x))

end ComplexSources

section RelativeFromAbsolute

variable {K : GeneralPadicCoefficientFields.BaseField p}
  (B : BaseRealization p K) (Z : Over B.analytic)
  (hZ : Presheaf.IsSheaf (analyticEtaleTopology p Z.left) (etaleRingsLarge p Z.left))
  [HasSheafify (analyticEtaleTopology p Z.left) AddCommGrpCat.{1}]
  [(analyticEtaleTopology p Z.left).WEqualsLocallyBijective AddCommGrpCat.{1}]
  {Y : AnalyticAdicSpace p} (g : Z.left ⟶ Y)
  (ΩA : DifferentialSource p Z.hom hZ) (ΩR : DifferentialSource p g hZ)
  (M : BaseCoefficientInput p Z.hom hZ ΩA) (ρ : ΩA.oneForms ⟶ ΩR.oneForms)

/-- Relative base input is the ORIGINAL absolute associated coefficient, projected by the
actual relative cotangent map. The carrier and filtration are fixed, not newly selected. -/
structure RelativeCoefficientInputSource where
  relative : BaseCoefficientInput p g hZ ΩR
  module_source : relative.module = M.module
  filtration_source : HEq relative.filtration M.filtration
  connection_source : ∀ (U : (Etale p Z.left)ᵒᵖ) (m : relative.module.val.obj U),
    relative.connection U m =
      (((tensorFunctor (regularEtale p Z.left hZ) ΩR.oneForms).map
        (eqToHom module_source.symm)).val.app U).hom
          (((tensorMap (regularEtale p Z.left hZ) (𝟙 M.module) ρ).val.app U).hom
            (M.connection U (((eqToHom module_source).val.app U).hom m)))

end RelativeFromAbsolute

end MathlibExt.AlgebraicGeometry.AnalyticRelativeDeRhamSources
