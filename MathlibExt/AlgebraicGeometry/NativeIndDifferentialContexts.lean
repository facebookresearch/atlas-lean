/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IndDifferentialModuleModels
public import MathlibExt.AlgebraicGeometry.DifferentialComplexScalarModels
public import MathlibExt.AlgebraicGeometry.ConjugateHolomorphicCoefficients
public import MathlibExt.AlgebraicGeometry.RightDifferentialModules
public import MathlibExt.AlgebraicGeometry.TemperedDistributionSectionModels
public import MathlibExt.CategoryTheory.NativeDerivedBimoduleCalculus
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# Fixed native Ind contexts and actual analytic differential rings

This packaging retains the compact-Yoneda tensor, actual alpha/left-beta,
all original ordinary ring sections and their monoid actions. The analytic
ring names below are the actual native finite-operator sheafifications of
the original complex and conjugate coefficient sheaves, including their
actual opposite rings. No differential-ring carrier is independently chosen.

Source: DK1311.2374v2 Sections2.2,4.10,5.2; Mathlib56a005, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeIndDifferentialContexts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves IndSheafCoefficientModels IndSheafAlphaBetaModels
open IndSheafMonoidalModels RingedComplexCoefficientModels BetaDifferentialRingModels
open IndDifferentialModuleModels DifferentialOperatorSheaves ConjugateHolomorphicCoefficients
open RightDifferentialModules
open MathlibExt.CategoryTheory.NativeMonoidalBimoduleMapping

variable (X : TopCat.{0})
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ X]

local instance contextIndPreadditive : Preadditive (IndSheaf ℂ X) := Abelian.toPreadditive

/-- The ind-sheaf calculus of $X$ with complex coefficients, given sheafification of presheaves of
$\mathbb{C}$-modules on $X$ and the abelian structure of ind-sheaves from `CompactSheafSource ℂ X`.
An instance records: the sheafified tensor product of two compactly supported sheaves is compactly
supported; the Ind tensor product and α exist as left Kan extensions along the Ind-Yoneda embedding
(of the tensor product and of the inclusion of compactly supported sheaves), and α has a left
adjoint β; symmetric monoidal structures on sheaves and on ind-sheaves whose tensor products are
identified with the sheafified and the Ind tensor products (and the unit of sheaves with the
constant sheaf $\mathbb{C}$), with β braided monoidal; the bimodule calculus of the Ind tensor
product (`NativeModuleCalculus`); a $\mathbb{C}$-linear structure on ind-sheaves; that the
associator, unitors and braiding of sheaves act on local sections by
$(f \otimes g) \otimes h \mapsto f \otimes (g \otimes h)$, $1 \otimes f \mapsto f$,
$f \otimes 1 \mapsto f$ and $f \otimes g \mapsto g \otimes f$; and that the embedding of compactly
supported sheaves into ind-sheaves commutes with multiplication of morphisms by complex scalars. -/
class IndSpaceSource where
  compactTensor : CompactTensorSource ℂ X
  indTensor : IndTensorSource ℂ X compactTensor
  alpha : AlphaSource ℂ X
  beta : BetaSource ℂ X alpha
  [ordinaryMonoidal : OrdinaryMonoidalSource ℂ X]
  [indMonoidal : IndMonoidalSource ℂ X compactTensor indTensor]
  [betaMonoidal : BetaMonoidalSource ℂ X compactTensor indTensor alpha beta]
  [moduleCalculus : NativeModuleCalculus X compactTensor indTensor]
  [linear : Linear ℂ (IndSheaf ℂ X)]
  associatorValues : ∀ (F G H : OrdinarySheaf ℂ X) (U : Opens X)
      (f : F.presheaf.obj (op U)) (g : G.presheaf.obj (op U)) (h : H.presheaf.obj (op U)),
    (α_ F G H).hom.hom.app (op U)
      (sourceTensorSection ℂ X (F ⊗ G) H U (sourceTensorSection ℂ X F G U f g) h) =
      sourceTensorSection ℂ X F (G ⊗ H) U f (sourceTensorSection ℂ X G H U g h)
  leftUnitValues : ∀ (F : OrdinarySheaf ℂ X) (U : Opens X) (f : F.presheaf.obj (op U)),
    (λ_ F).hom.hom.app (op U)
      (sourceTensorSection ℂ X (𝟙_ (OrdinarySheaf ℂ X)) F U (sourceUnitSection ℂ X U 1) f) = f
  rightUnitValues : ∀ (F : OrdinarySheaf ℂ X) (U : Opens X) (f : F.presheaf.obj (op U)),
    (ρ_ F).hom.hom.app (op U)
      (sourceTensorSection ℂ X F (𝟙_ (OrdinarySheaf ℂ X)) U f (sourceUnitSection ℂ X U 1)) = f
  braidingValues : ∀ (F G : OrdinarySheaf ℂ X) (U : Opens X)
      (f : F.presheaf.obj (op U)) (g : G.presheaf.obj (op U)),
    (β_ F G).hom.hom.app (op U) (sourceTensorSection ℂ X F G U f g) =
      sourceTensorSection ℂ X G F U g f
  compactScalars : ∀ (F G : CompactSheaf ℂ X) (a : ℂ) (f : F ⟶ G),
    (compactToInd ℂ X).map (ObjectProperty.homMk (ObjectProperty.homMk (a • f.hom.hom))) =
      a • (compactToInd ℂ X).map f

attribute [instance_reducible, instance] IndSpaceSource.ordinaryMonoidal
  IndSpaceSource.indMonoidal IndSpaceSource.betaMonoidal IndSpaceSource.moduleCalculus
  IndSpaceSource.linear

/-- The linear structure at `TopCat.of M`: Lean 4.36 does not find the generic instance there, as
its key keeps the carrier of `X`, which the query reduces to `M`. -/
instance IndSpaceSource.linearOf (M : Type) [TopologicalSpace M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M)) (ModuleCat.{0} ℂ)]
    [CompactSheafSource ℂ (TopCat.of M)] [IndSpaceSource (TopCat.of M)] :
    Linear ℂ (IndSheaf ℂ (TopCat.of M)) :=
  IndSpaceSource.linear

/-- The Ind monoidal structure at `TopCat.of M` (see `IndSpaceSource.linearOf`). -/
instance IndSpaceSource.indMonoidalOf (M : Type) [TopologicalSpace M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M)) (ModuleCat.{0} ℂ)]
    [CompactSheafSource ℂ (TopCat.of M)] [C : IndSpaceSource (TopCat.of M)] :
    MonoidalCategory (IndSheaf ℂ (TopCat.of M)) :=
  IndMonoidalSource.monoidal (T := C.compactTensor) (I := C.indTensor)

/-- The Ind symmetric structure at `TopCat.of M` (see `IndSpaceSource.linearOf`). -/
instance IndSpaceSource.indSymmetricOf (M : Type) [TopologicalSpace M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M)) (ModuleCat.{0} ℂ)]
    [CompactSheafSource ℂ (TopCat.of M)] [C : IndSpaceSource (TopCat.of M)] :
    SymmetricCategory (IndSheaf ℂ (TopCat.of M)) :=
  IndMonoidalSource.symmetric (T := C.compactTensor) (I := C.indTensor)

/-- The braided structure of `β` at `TopCat.of M` (see `IndSpaceSource.linearOf`). -/
instance IndSpaceSource.betaBraidedOf (M : Type) [TopologicalSpace M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M)) (ModuleCat.{0} ℂ)]
    [CompactSheafSource ℂ (TopCat.of M)] [C : IndSpaceSource (TopCat.of M)] :
    (IndSheafAlphaBetaModels.beta ℂ (TopCat.of M) C.alpha C.beta).Braided :=
  BetaMonoidalSource.braided (T := C.compactTensor) (I := C.indTensor)

/-- Bimodule abelian structures at `TopCat.of M` (see `IndSpaceSource.linearOf`). -/
instance IndSpaceSource.bimodAbelianOf (M : Type) [TopologicalSpace M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M)) (ModuleCat.{0} ℂ)]
    [CompactSheafSource ℂ (TopCat.of M)] [C : IndSpaceSource (TopCat.of M)]
    (D E : Mon (IndSheaf ℂ (TopCat.of M))) : Abelian (Bimod D E) :=
  NativeModuleCalculus.abelian (T := C.compactTensor) (I := C.indTensor) D E

/-- Coequalizers of ind-sheaves at `TopCat.of M` (see `IndSpaceSource.linearOf`). -/
instance IndSpaceSource.coequalizersOf (M : Type) [TopologicalSpace M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M)) (ModuleCat.{0} ℂ)]
    [CompactSheafSource ℂ (TopCat.of M)] [C : IndSpaceSource (TopCat.of M)] :
    Limits.HasCoequalizers (IndSheaf ℂ (TopCat.of M)) :=
  NativeModuleCalculus.coequalizers (T := C.compactTensor) (I := C.indTensor)

/-- Tensoring on the left preserves colimits at `TopCat.of M` (see `IndSpaceSource.linearOf`). -/
instance IndSpaceSource.leftColimitsOf (M : Type) [TopologicalSpace M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M)) (ModuleCat.{0} ℂ)]
    [CompactSheafSource ℂ (TopCat.of M)] [C : IndSpaceSource (TopCat.of M)]
    (K : IndSheaf ℂ (TopCat.of M)) : Limits.PreservesColimitsOfSize.{0, 0} (tensorLeft K) :=
  NativeModuleCalculus.leftColimits (T := C.compactTensor) (I := C.indTensor) K

/-- Tensoring on the right preserves colimits at `TopCat.of M` (see `IndSpaceSource.linearOf`). -/
instance IndSpaceSource.rightColimitsOf (M : Type) [TopologicalSpace M]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of M)) (ModuleCat.{0} ℂ)]
    [CompactSheafSource ℂ (TopCat.of M)] [C : IndSpaceSource (TopCat.of M)]
    (K : IndSheaf ℂ (TopCat.of M)) : Limits.PreservesColimitsOfSize.{0, 0} (tensorRight K) :=
  NativeModuleCalculus.rightColimits (T := C.compactTensor) (I := C.indTensor) K

variable [C : IndSpaceSource X]

abbrev coefficientMonoid : Mon (IndSheaf ℂ X) :=
  betaCoefficientRing X C.compactTensor C.indTensor C.alpha C.beta

variable (R : TopCat.Sheaf RingCat.{0} X)

class BetaRingSource where
  [complex : ComplexRingSheafSource X R]
  coefficient : RingCoefficientSheafSource X R
  monoid : OrdinaryRingMonoidSource X R coefficient

attribute [instance_reducible, instance] BetaRingSource.complex

variable [S : BetaRingSource X R]

abbrev betaRing : Mon (IndSheaf ℂ X) :=
  nativeBetaRing X C.compactTensor C.indTensor C.alpha C.beta R S.coefficient S.monoid

class OrdinaryBetaModuleSource where
  forget : ComplexModuleForgetSource X R
  ordinary : OrdinaryModuleRepresentationSource X R S.coefficient S.monoid forget
  betaMap : BimoduleMappingSource (IndSheafAlphaBetaModels.beta ℂ X C.alpha C.beta)
    (ordinaryRing X R S.coefficient S.monoid) (Mon.trivial (OrdinarySheaf ℂ X))

variable (N : OrdinaryBetaModuleSource X R)

def betaModules : OrdinaryModule X R ⥤ Bimod (betaRing X R) (coefficientMonoid X) :=
  betaOrdinaryModule X C.compactTensor C.indTensor C.alpha C.beta R
    S.coefficient S.monoid N.forget N.ordinary N.betaMap

section NormalizedDifferentialScalars

variable (M : Type) [TopologicalSpace M]
  (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} ℂ)
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ (TopCat.of M)] [IndSpaceSource (TopCat.of M)]

/-- The beta source retains precisely the original constant multiplication operators. -/
class DifferentialBetaSource where
  [source : BetaRingSource (TopCat.of M) (differentialRing ℂ M O)]
  constants : ∀ (U : Opens M) (c : ℂ),
    letI : Algebra ℂ ((differentialRing ℂ M O).obj.obj (op U)) :=
      ComplexRingSheafSource.algebra (X := TopCat.of M) (R := differentialRing ℂ M O) U
    algebraMap ℂ ((differentialRing ℂ M O).obj.obj (op U)) c =
      DifferentialComplexScalarModels.differentialConstant M O U c

attribute [instance_reducible, instance] DifferentialBetaSource.source

def oppositeDifferentialConstant (U : Opens M) (c : ℂ) :
    (rightDifferentialRing ℂ M O).obj.obj (op U) :=
  ((toSheafify (Opens.grothendieckTopology M) (rightOperatorPresheaf ℂ M O)).app (op U)).hom
    (rightScalarFinite ℂ M O U (algebraMap ℂ (O.obj (op U)) c))

class OppositeDifferentialBetaSource where
  [source : BetaRingSource (TopCat.of M) (rightDifferentialRing ℂ M O)]
  constants : ∀ (U : Opens M) (c : ℂ),
    letI : Algebra ℂ ((rightDifferentialRing ℂ M O).obj.obj (op U)) :=
      ComplexRingSheafSource.algebra (X := TopCat.of M) (R := rightDifferentialRing ℂ M O) U
    algebraMap ℂ ((rightDifferentialRing ℂ M O).obj.obj (op U)) c =
      oppositeDifferentialConstant M O U c

attribute [instance_reducible, instance] OppositeDifferentialBetaSource.source

end NormalizedDifferentialScalars

section AnalyticRings

open scoped Manifold ContDiff

variable (n : ℕ) (M : Type) [TopologicalSpace M]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) M]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ M]
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]

abbrev analyticCoefficients := HolomorphicCoefficientSheaves.coefficientPresheaf
  (TemperedDistributionSectionModels.ComplexCoordinates n) M

abbrev analyticDifferentialRing : TopCat.Sheaf RingCat.{0} (TopCat.of M) :=
  differentialRing ℂ M (analyticCoefficients n M)

abbrev analyticOppositeDifferentialRing : TopCat.Sheaf RingCat.{0} (TopCat.of M) :=
  rightDifferentialRing ℂ M (analyticCoefficients n M)

abbrev analyticConjugateCoefficients := conjugateCoefficientPresheaf
  (TemperedDistributionSectionModels.ComplexCoordinates n) M

abbrev analyticConjugateDifferentialRing : TopCat.Sheaf RingCat.{0} (TopCat.of M) :=
  differentialRing ℂ M (analyticConjugateCoefficients n M)

abbrev analyticConjugateOppositeRing : TopCat.Sheaf RingCat.{0} (TopCat.of M) :=
  rightDifferentialRing ℂ M (analyticConjugateCoefficients n M)

end AnalyticRings
end MathlibExt.AlgebraicGeometry.NativeIndDifferentialContexts
