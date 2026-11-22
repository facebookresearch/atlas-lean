/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationK
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSpherePowers
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.SphereOperatorCategory
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.NativeOperatorIndex
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SpherePowerComparison
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.CanonicalOperatorProjectiveModels

/-!
# Native operator stabilization and K-generated Ω replacement

The carriers are the full native symmetric and orthogonal enriched operator
categories. The source coefficient and complete coend inclusion determine each
free stabilization arrow. Native scalar/free and free/evaluation adjunctions
construct the mapping correspondence on the actual mapping ends.

## Primary source and conventions

The primary reference is M. A. Mandell, J. P. May, S. Schwede and B. Shipley,
*Model Categories of Diagram Spectra*, author version dated December 30, 1999:
https://www.math.uchicago.edu/~may/PAPERS/mmssLMSDec30.pdf.
The references below use that version's printed page numbers, which agree
with its 67 PDF pages.

* Construction 2.1 and Theorem 2.2 (p. 9), with the proof in Section 23
  (p. 63), describe the enriched operator category of right sphere modules.
  The proof constructs the coend inclusion ν : R(e) → D_R(d, d □ e).
* Examples 4.2 and 4.4 (pp. 12–13) give the symmetric permutation/block
  convention, orthogonal direct-sum convention and their sphere coefficients.
* Definition 8.4 and Lemma 8.5 (p. 25) define the one-step free map
  λ_n : F_(n+1)(S¹) → F_n(S⁰) by the free/evaluation adjunction and identify
  its mapping-space transpose with the adjoint structure map.
* Definition 9.3 (p. 29) factors λ_n through its mapping cylinder and defines
  K = FJ ∪ { k_n □ i | n ≥ 0, i ∈ I }. Definition 6.2 (p. 19) specifies
  that paper's based disk-boundary generators I and disk-cylinder generators J.

## The family formalized here

`NativeStabilizationFamily` abstracts the operator objects, actual pointed
coefficients and coend inclusions. Its symmetric specialization keeps every
pair `(n, a)` of actual finite-bijection objects: source n, target n ⊗ a and
coefficient the native sphere at a. The coend generator is coefficient-first,
so `symmetricNu` uses the actual block braid β_(a,n) : a ⊗ n → n ⊗ a.
The orthogonal specialization keeps every dimension pair `(n, a)`, target
n + a, the actual one-point sphere at a and the continuous native ν inclusion.
These implement the operator/coend structure above with the native carrier
and coefficient maps fixed.

This is a full-family version of the paper's one-step construction. The level
I/J and scalar boundaries used here are the project's freely pointed realized
simplicial boundary/horn families, rather than the disk/cylinder families
printed in Definition 6.2. The native mapping cylinder and scalar Leibniz
pushout product implement the pattern of Definition 9.3 for those actual
choices. In this file, “original” refers to these fixed native source maps,
coefficients, correlated labels and chosen algorithms; it does not assert
literal equality with the paper's generating sets or its factorization choices.
For an arbitrary supplied family, `NativeK.IsOmega` means the full-label
condition defined here. Comparison with the paper's one-step Ω condition and
K-right class is a separate result.

## Returned data and remaining stable-model work

The K family retains the actual free horn family and correlated pointed
boundary/mapping-cylinder maps. Its source bounds, regular cardinal, bottom,
entire small-object functions and all `CategoryTheory.Arrow` inputs are kept.
The file constructs `NativeK.omegaReplacement` and its K-left unit, proves that
its target is Ω, and exposes the symmetric and orthogonal specializations.
This is a K-generated Ω replacement. A stable model structure, localization
and stable-model fibrant replacement are not constructed here.

Stable existence still requires arbitrary-source K-left acyclicity and the
intersection of K-right with the Ω-test weak class. Stable monoidality
requires the full native smash pushout-product and sphere unit arguments.
No symmetric naive homotopy-group criterion is asserted here.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.MorphismProperty CategoryTheory.EnrichedFunctorCat
open CategoryTheory.MonoidalCategory.TensorPower
open CategoryTheory.BraidedCategory
open Topology
open scoped CGWH.modelCategory MonoidalClosed Cardinal Simplicial

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
namespace Actual

open HomotopicalAlgebra.EnrichedProjective.Native
attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal

/-- The native symmetric carrier is the complete original enriched operator functor category. -/
abbrev SymmetricCarrier :=
  EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}

/-- The native orthogonal carrier retains every full continuous isometry/coend Hom. -/
abbrev OrthogonalCarrier :=
  EnrichedFunctorCat PointedCGWH.{u, v} CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}

/-- Every ordered power of the actual native sphere coefficient has its derived carrier bound. -/
theorem spherePower_bound (n : ℕ) :
    #↥(tensorPowObj PointedCGWH.sphereOne.{u, v} n).right ≤ Cardinal.continuum := by
  induction n with
  | zero => exact PointedCGWH.CoefficientCardinal.unit_mk_le
  | succ n h =>
    exact PointedCGWH.CoefficientCardinal.smash_mk_le_continuum
      (tensorPowObj PointedCGWH.sphereOne.{u, v} n) PointedCGWH.sphereOne
      h PointedCGWH.CoefficientCardinal.sphereOne_mk_le

/-- The actual current representation sphere inherits its bound through the original full Iso. -/
theorem orthogonalSphere_bound (n : ℕ) :
    #↥(PointedCGWH.orthogonalSphere.{u, v} n).right ≤ Cardinal.continuum := by
  let e : (tensorPowObj PointedCGWH.sphereOne.{u, v} n).right ≅
      (PointedCGWH.orthogonalSphere.{u, v} n).right := PointedCGWH.pointedToCGWH.mapIso
    (CategoryTheory.Spectra.originalSpherePowerComparisonIso.{u, v} n)
  exact (Cardinal.mk_congr (CGWH.homeoOfIso e).toEquiv).symm.le.trans (spherePower_bound n)

/-- The actual orthogonal coefficient is cofibrant via the source-derived original sphere Iso. -/
theorem orthogonalSphere_cofibrant (n : ℕ) :
    IsCofibrant (PointedCGWH.orthogonalSphere.{u, v} n) := by
  let e := CategoryTheory.Spectra.originalSpherePowerComparisonIso.{u, v} n
  let _ : IsCofibrant (tensorPowObj PointedCGWH.sphereOne.{u, v} n) :=
    PointedCGWH.modelCategory.tensorPowObj_sphereOne_isCofibrant n
  rw [isCofibrant_iff_of_isInitial
    (initial.to (tensorPowObj PointedCGWH.sphereOne.{u, v} n) ≫ e.hom) initialIsInitial]
  infer_instance

/-- The original symmetric right inclusion is its full coend generator at the actual block swap. -/
def symmetricNu (n a : Operad.SmallFinBijGroupoid) :
    PointedCGWH.sphereSequence.{u, v}.functor.obj a ⟶
      (PointedCGWH.symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}]
        PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ a)) :=
  PointedCGWH.SymmetricModulePresentation.operatorGenerator a n (n ⊗ a) (β_ a n).hom

/-- The symmetric stabilization data discharges every coefficient premise by its actual powers. -/
def symmetricFamily : NativeStabilizationFamily.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}
    (Operad.SmallFinBijGroupoid × Operad.SmallFinBijGroupoid) where
  source na := PointedCGWH.symmetricOperatorObj na.1
  target na := PointedCGWH.symmetricOperatorObj (na.1 ⊗ na.2)
  coefficient na := PointedCGWH.sphereSequence.functor.obj na.2
  inclusion na := symmetricNu na.1 na.2
  coefficient_cofibrant na := by
    change IsCofibrant (tensorPowObj PointedCGWH.sphereOne.{u, v} na.2.of.len)
    exact PointedCGWH.modelCategory.tensorPowObj_sphereOne_isCofibrant na.2.of.len
  coefficient_bound na := spherePower_bound na.2.of.len

/-- The orthogonal data uses the original continuous nu and actual one-point spheres. -/
def orthogonalFamily : NativeStabilizationFamily.{u, v}
    CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v} (ℕ × ℕ) where
  source na := CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex na.1
  target na := CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex (na.1 + na.2)
  coefficient na := PointedCGWH.orthogonalSphere na.2
  inclusion na := CategoryTheory.Spectra.OrthogonalOperatorIndex.nu na.1 na.2
  coefficient_cofibrant na := orthogonalSphere_cofibrant.{u, v} na.2
  coefficient_bound na := orthogonalSphere_bound.{u, v} na.2

/-- The whole symmetric family retains the native block-permutation inclusion. -/
theorem symmetricFamily_inclusion (n a : Operad.SmallFinBijGroupoid) :
    symmetricFamily.{u, v}.inclusion (n, a) =
      PointedCGWH.SymmetricModulePresentation.operatorGenerator a n (n ⊗ a) (β_ a n).hom := rfl

/-- The whole orthogonal source family retains the original native continuous coend inclusion. -/
theorem orthogonalFamily_inclusion (n a : ℕ) :
    orthogonalFamily.{u, v}.inclusion (n, a) =
      CategoryTheory.Spectra.OrthogonalOperatorIndex.nu n a := rfl

/-- Both complete constructor functions agree on the actual native symmetric carrier. -/
theorem symmetricConstructor_functions_eq :
    CurrentFree.OriginalConstructors.scalarConstructorFunction
      (V := PointedCGWH.{u, v}) (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) =
    CurrentFree.OriginalConstructors.rawConstructorFunction
      (V := PointedCGWH.{u, v}) (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
  CurrentFree.OriginalConstructors.constructor_functions_eq

/-- Both complete constructor functions agree on the full native orthogonal carrier. -/
theorem orthogonalConstructor_functions_eq :
    CurrentFree.OriginalConstructors.scalarConstructorFunction
      (V := PointedCGWH.{u, v}) (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) =
    CurrentFree.OriginalConstructors.rawConstructorFunction
      (V := PointedCGWH.{u, v}) (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}) :=
  CurrentFree.OriginalConstructors.constructor_functions_eq

/-- Every actual native symmetric sphere input retains both original whole source functions. -/
theorem symmetricSphere_stabilization_functions_eq :
    (fun (Γ : Center PointedCGWH.{u, v}) (n a : Operad.SmallFinBijGroupoid)
      (h : Γ.1 ⟶ PointedCGWH.sphereSequence.{u, v}.functor.obj a) =>
      CurrentFree.stabilization (PointedCGWH.symmetricOperatorObj n)
        (PointedCGWH.symmetricOperatorObj (n ⊗ a)) Γ.1 (h ≫ symmetricNu n a)) =
    fun (Γ : Center PointedCGWH.{u, v}) (n a : Operad.SmallFinBijGroupoid)
      (h : Γ.1 ⟶ PointedCGWH.sphereSequence.{u, v}.functor.obj a) =>
      CurrentFree.OriginalConstructors.rawStabilization Γ (PointedCGWH.symmetricOperatorObj n)
        (PointedCGWH.symmetricOperatorObj (n ⊗ a)) (h ≫ symmetricNu n a) := by
  funext Γ n a h
  exact congrFun (congrFun (congrFun (congrFun
    (CurrentFree.OriginalConstructors.stabilization_functions_eq
      (V := PointedCGWH.{u, v}) (A := PointedCGWH.SymmetricOperatorIndex.{u, v}))
    Γ) (PointedCGWH.symmetricOperatorObj n)) (PointedCGWH.symmetricOperatorObj (n ⊗ a)))
    (h ≫ symmetricNu n a)

/-- Every actual orthogonal sphere input preserves the full original continuous nu function. -/
theorem orthogonalSphere_stabilization_functions_eq :
    (fun (Γ : Center PointedCGWH.{u, v}) (n a : ℕ)
      (h : Γ.1 ⟶ PointedCGWH.orthogonalSphere.{u, v} a) =>
      CurrentFree.stabilization (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n)
        (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex (n + a)) Γ.1
        (h ≫ CategoryTheory.Spectra.OrthogonalOperatorIndex.nu n a)) =
    fun (Γ : Center PointedCGWH.{u, v}) (n a : ℕ)
      (h : Γ.1 ⟶ PointedCGWH.orthogonalSphere.{u, v} a) =>
      CurrentFree.OriginalConstructors.rawStabilization Γ
        (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n)
        (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex (n + a))
        (h ≫ CategoryTheory.Spectra.OrthogonalOperatorIndex.nu n a) := by
  funext Γ n a h
  exact congrFun (congrFun (congrFun (congrFun
    (CurrentFree.OriginalConstructors.stabilization_functions_eq
      (V := PointedCGWH.{u, v}) (A := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}))
    Γ) (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex n))
    (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex (n + a)))
    (h ≫ CategoryTheory.Spectra.OrthogonalOperatorIndex.nu n a)

/-- Every current symmetric stabilization map is the actual original free/evaluation adjunct. -/
abbrev symmetricStabilization (n a : Operad.SmallFinBijGroupoid) :=
  NativeK.stabilization symmetricFamily.{u, v} (n, a)

/-- Each orthogonal stabilization map retains its original source and coefficient labels. -/
abbrev orthogonalStabilization (n a : ℕ) := NativeK.stabilization orthogonalFamily.{u, v} (n, a)

/-- The symmetric Omega predicate uses all original sphere/block actions on the same carrier. -/
abbrev SymmetricIsOmega (X : SymmetricCarrier.{u, v}) := NativeK.IsOmega symmetricFamily X

/-- The orthogonal Omega predicate uses all original continuous representation-sphere actions. -/
abbrev OrthogonalIsOmega (X : OrthogonalCarrier.{u, v}) := NativeK.IsOmega orthogonalFamily X

/-- The native symmetric K family is the original horn family and complete correlated new maps. -/
abbrev symmetricK : MorphismProperty SymmetricCarrier.{u, v} := NativeK.generators symmetricFamily

/-- The native orthogonal K family retains the literal original free-horn summand. -/
abbrev orthogonalK : MorphismProperty OrthogonalCarrier.{u, v} :=
  NativeK.generators orthogonalFamily

attribute [local instance] Construction.generatorOrderBot

/-- The original symmetric free-boundary family has its actual fixed-cardinal eligibility. -/
local instance symmetricIEligible :
    IsCardinalForSmallObjectArgument
      (NativeK.levelI (I := PointedCGWH.SymmetricOperatorIndex.{u, v}))
      realizedGeneratorCardinal.{v} :=
  Construction.generatorsI_isCardinalForSmallObjectArgument

/-- The original symmetric free-horn family has its actual fixed-cardinal eligibility. -/
local instance symmetricJEligible :
    IsCardinalForSmallObjectArgument
      (NativeK.levelJ (I := PointedCGWH.SymmetricOperatorIndex.{u, v}))
      realizedGeneratorCardinal.{v} :=
  Construction.generatorsJ_isCardinalForSmallObjectArgument

/-- The original orthogonal free-boundary family has its actual fixed-cardinal eligibility. -/
local instance orthogonalIEligible :
    IsCardinalForSmallObjectArgument
      (NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}))
      realizedGeneratorCardinal.{v} :=
  Construction.generatorsI_isCardinalForSmallObjectArgument

/-- The original orthogonal free-horn family has its actual fixed-cardinal eligibility. -/
local instance orthogonalJEligible :
    IsCardinalForSmallObjectArgument
      (NativeK.levelJ (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}))
      realizedGeneratorCardinal.{v} :=
  Construction.generatorsJ_isCardinalForSmallObjectArgument

/-- The original-cardinal symmetric K factorization is constructed on its native carrier. -/
def symmetricKFactorizationData :
    FunctorialFactorizationData symmetricK.{u, v}.rlp.llp symmetricK.rlp :=
  NativeK.factorizationData symmetricFamily

/-- The original-cardinal orthogonal K factorization uses the actual continuous operator carrier. -/
def orthogonalKFactorizationData :
    FunctorialFactorizationData orthogonalK.{u, v}.rlp.llp orthogonalK.rlp :=
  NativeK.factorizationData orthogonalFamily

/-- All native symmetric K small-object premises are discharged at the literal original cardinal. -/
theorem symmetricK_eligible :
    symmetricK.{u, v}.IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
  NativeK.generators_isCardinalForSmallObjectArgument symmetricFamily

/-- All native orthogonal K premises are discharged by its actual bounded cofibrant coefficients. -/
theorem orthogonalK_eligible :
    orthogonalK.{u, v}.IsCardinalForSmallObjectArgument realizedGeneratorCardinal.{v} :=
  NativeK.generators_isCardinalForSmallObjectArgument orthogonalFamily

attribute [local instance] symmetricK_eligible orthogonalK_eligible

/-- The actual symmetric model retains every full original level weak component. -/
theorem symmetricLevelModel_weakEquivalences :
    PointedCGWH.Spectra.Symmetric.levelModel.{u, v}.categoryWithWeakEquivalences.weakEquivalences =
      EvaluationTransfer.evaluationProperty
        (fun a : PointedCGWH.SymmetricOperatorIndex.{u, v} => evaluation a)
        (weakEquivalences PointedCGWH.{u, v}) :=
  HomotopicalAlgebra.EnrichedProjective.Native.Construction.weakEquivalences_eq

/-- The actual symmetric cofibrations are the entire original native I-left class. -/
theorem symmetricLevelModel_cofibrations :
    PointedCGWH.Spectra.Symmetric.levelModel.{u, v}.categoryWithCofibrations.cofibrations =
      (NativeK.levelI (I := PointedCGWH.SymmetricOperatorIndex.{u, v})).rlp.llp :=
  HomotopicalAlgebra.EnrichedProjective.Native.Construction.cofibrations_eq

/-- Native symmetric fibrations retain every complete evaluation of the actual source map. -/
theorem symmetricLevelModel_fibrations :
    PointedCGWH.Spectra.Symmetric.levelModel.{u, v}.categoryWithFibrations.fibrations =
      EvaluationTransfer.evaluationProperty
        (fun a : PointedCGWH.SymmetricOperatorIndex.{u, v} => evaluation a)
        (fibrations PointedCGWH.{u, v}) :=
  HomotopicalAlgebra.EnrichedProjective.Native.Construction.fibrations_eq

/-- The actual symmetric trivial fibrations are the full original evaluation class. -/
theorem symmetricLevelModel_trivialFibrations :
    letI : ModelCategory SymmetricCarrier.{u, v} := PointedCGWH.Spectra.Symmetric.levelModel
    trivialFibrations SymmetricCarrier.{u, v} = EvaluationTransfer.evaluationProperty
      (fun a : PointedCGWH.SymmetricOperatorIndex.{u, v} => evaluation a)
      (trivialFibrations PointedCGWH.{u, v}) :=
  HomotopicalAlgebra.EnrichedProjective.Native.Construction.trivialFibrations_eq

/-- The actual symmetric trivial cofibrations are the entire original native J-left class. -/
theorem symmetricLevelModel_trivialCofibrations :
    letI : ModelCategory SymmetricCarrier.{u, v} := PointedCGWH.Spectra.Symmetric.levelModel
    trivialCofibrations SymmetricCarrier.{u, v} =
      (NativeK.levelJ (I := PointedCGWH.SymmetricOperatorIndex.{u, v})).rlp.llp :=
  HomotopicalAlgebra.EnrichedProjective.Native.Construction.trivialCofibrations_eq

/-- The actual orthogonal weak class is evaluated on every full native operator object. -/
theorem orthogonalLevelModel_weakEquivalences :
    PointedCGWH.Spectra.Orthogonal.levelModel.{u, v}.categoryWithWeakEquivalences.weakEquivalences =
      EvaluationTransfer.evaluationProperty
        (fun a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v} => evaluation a)
        (weakEquivalences PointedCGWH.{u, v}) :=
  HomotopicalAlgebra.EnrichedProjective.Native.Construction.weakEquivalences_eq

/-- The actual orthogonal cofibration class is the complete original I-left class. -/
theorem orthogonalLevelModel_cofibrations :
    PointedCGWH.Spectra.Orthogonal.levelModel.{u, v}.categoryWithCofibrations.cofibrations =
      (NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})).rlp.llp :=
  HomotopicalAlgebra.EnrichedProjective.Native.Construction.cofibrations_eq

/-- The actual orthogonal fibrations retain the full original evaluation class. -/
theorem orthogonalLevelModel_fibrations :
    PointedCGWH.Spectra.Orthogonal.levelModel.{u, v}.categoryWithFibrations.fibrations =
      EvaluationTransfer.evaluationProperty
        (fun a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v} => evaluation a)
        (fibrations PointedCGWH.{u, v}) :=
  HomotopicalAlgebra.EnrichedProjective.Native.Construction.fibrations_eq

/-- Every orthogonal trivial fibration is the literal complete source evaluation predicate. -/
theorem orthogonalLevelModel_trivialFibrations :
    letI : ModelCategory OrthogonalCarrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    trivialFibrations OrthogonalCarrier.{u, v} = EvaluationTransfer.evaluationProperty
      (fun a : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v} => evaluation a)
      (trivialFibrations PointedCGWH.{u, v}) :=
  HomotopicalAlgebra.EnrichedProjective.Native.Construction.trivialFibrations_eq

/-- Every orthogonal trivial cofibration belongs to the full original free-J left class. -/
theorem orthogonalLevelModel_trivialCofibrations :
    letI : ModelCategory OrthogonalCarrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    trivialCofibrations OrthogonalCarrier.{u, v} =
      (NativeK.levelJ (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})).rlp.llp :=
  HomotopicalAlgebra.EnrichedProjective.Native.Construction.trivialCofibrations_eq

/-- Every original symmetric I input retains the entire original same-cardinal intermediate map. -/
theorem symmetricIFactorizationData_Z_map
    {F G : CategoryTheory.Arrow SymmetricCarrier.{u, v}} (φ : F ⟶ G) :
    PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.Z.map φ = SmallObject.objMap
      (NativeK.levelI (I := PointedCGWH.SymmetricOperatorIndex.{u, v}))
      realizedGeneratorCardinal.{v} φ :=
  HomotopicalAlgebra.EnrichedProjective.Native.Construction.cofibrantFactorizationData_Z_map φ

/-- Every original symmetric J input retains the full original intermediate map function. -/
theorem symmetricJFactorizationData_Z_map
    {F G : CategoryTheory.Arrow SymmetricCarrier.{u, v}} (φ : F ⟶ G) :
    PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.Z.map φ = SmallObject.objMap
      (NativeK.levelJ (I := PointedCGWH.SymmetricOperatorIndex.{u, v}))
      realizedGeneratorCardinal.{v} φ :=
  HomotopicalAlgebra.EnrichedProjective.Native.Construction.fibrantFactorizationData_Z_map φ

/-- Every original orthogonal I input retains its complete original Arrow map function. -/
theorem orthogonalIFactorizationData_Z_map
    {F G : CategoryTheory.Arrow OrthogonalCarrier.{u, v}} (φ : F ⟶ G) :
    PointedCGWH.Spectra.Orthogonal.cofibrantFactorizationData.Z.map φ = SmallObject.objMap
      (NativeK.levelI (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}))
      realizedGeneratorCardinal.{v} φ :=
  HomotopicalAlgebra.EnrichedProjective.Native.Construction.cofibrantFactorizationData_Z_map φ

/-- Every original orthogonal J input retains its whole original regular-cardinal map function. -/
theorem orthogonalJFactorizationData_Z_map
    {F G : CategoryTheory.Arrow OrthogonalCarrier.{u, v}} (φ : F ⟶ G) :
    PointedCGWH.Spectra.Orthogonal.fibrantFactorizationData.Z.map φ = SmallObject.objMap
      (NativeK.levelJ (I := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}))
      realizedGeneratorCardinal.{v} φ :=
  HomotopicalAlgebra.EnrichedProjective.Native.Construction.fibrantFactorizationData_Z_map φ

/-- Both full symmetric I natural arrows retain every original source/target Arrow square. -/
theorem symmetricIFactorizationData_naturality
    {F G : CategoryTheory.Arrow SymmetricCarrier.{u, v}} (φ : F ⟶ G) :
    PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.i.app F ≫
      PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.Z.map φ =
      φ.left ≫ PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.i.app G ∧
    PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.Z.map φ ≫
      PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.p.app G =
      PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.p.app F ≫ φ.right :=
  ⟨(PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.i.naturality φ).symm,
    PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.p.naturality φ⟩

/-- Both full symmetric J natural arrows retain every actual original Arrow input. -/
theorem symmetricJFactorizationData_naturality
    {F G : CategoryTheory.Arrow SymmetricCarrier.{u, v}} (φ : F ⟶ G) :
    PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.i.app F ≫
      PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.Z.map φ =
      φ.left ≫ PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.i.app G ∧
    PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.Z.map φ ≫
      PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.p.app G =
      PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.p.app F ≫ φ.right :=
  ⟨(PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.i.naturality φ).symm,
    PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.p.naturality φ⟩

/-- Both entire orthogonal I natural arrows preserve the original complete source squares. -/
theorem orthogonalIFactorizationData_naturality
    {F G : CategoryTheory.Arrow OrthogonalCarrier.{u, v}} (φ : F ⟶ G) :
    PointedCGWH.Spectra.Orthogonal.cofibrantFactorizationData.i.app F ≫
      PointedCGWH.Spectra.Orthogonal.cofibrantFactorizationData.Z.map φ =
      φ.left ≫ PointedCGWH.Spectra.Orthogonal.cofibrantFactorizationData.i.app G ∧
    PointedCGWH.Spectra.Orthogonal.cofibrantFactorizationData.Z.map φ ≫
      PointedCGWH.Spectra.Orthogonal.cofibrantFactorizationData.p.app G =
      PointedCGWH.Spectra.Orthogonal.cofibrantFactorizationData.p.app F ≫ φ.right :=
  ⟨(PointedCGWH.Spectra.Orthogonal.cofibrantFactorizationData.i.naturality φ).symm,
    PointedCGWH.Spectra.Orthogonal.cofibrantFactorizationData.p.naturality φ⟩

/-- Both complete orthogonal J natural arrows retain the entire original Arrow input functions. -/
theorem orthogonalJFactorizationData_naturality
    {F G : CategoryTheory.Arrow OrthogonalCarrier.{u, v}} (φ : F ⟶ G) :
    PointedCGWH.Spectra.Orthogonal.fibrantFactorizationData.i.app F ≫
      PointedCGWH.Spectra.Orthogonal.fibrantFactorizationData.Z.map φ =
      φ.left ≫ PointedCGWH.Spectra.Orthogonal.fibrantFactorizationData.i.app G ∧
    PointedCGWH.Spectra.Orthogonal.fibrantFactorizationData.Z.map φ ≫
      PointedCGWH.Spectra.Orthogonal.fibrantFactorizationData.p.app G =
      PointedCGWH.Spectra.Orthogonal.fibrantFactorizationData.p.app F ≫ φ.right :=
  ⟨(PointedCGWH.Spectra.Orthogonal.fibrantFactorizationData.i.naturality φ).symm,
    PointedCGWH.Spectra.Orthogonal.fibrantFactorizationData.p.naturality φ⟩

/-- All four projective factorizations retain the original caller Arrow equations. -/
theorem projectiveFactorizationData_fac
    (F : CategoryTheory.Arrow SymmetricCarrier.{u, v})
    (G : CategoryTheory.Arrow OrthogonalCarrier.{u, v}) :
    PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.i.app F ≫
      PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.p.app F = F.hom ∧
      PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.i.app F ≫
        PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.p.app F = F.hom ∧
      PointedCGWH.Spectra.Orthogonal.cofibrantFactorizationData.i.app G ≫
        PointedCGWH.Spectra.Orthogonal.cofibrantFactorizationData.p.app G = G.hom ∧
      PointedCGWH.Spectra.Orthogonal.fibrantFactorizationData.i.app G ≫
        PointedCGWH.Spectra.Orthogonal.fibrantFactorizationData.p.app G = G.hom :=
  ⟨PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.fac_app,
    PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.fac_app,
    PointedCGWH.Spectra.Orthogonal.cofibrantFactorizationData.fac_app,
      PointedCGWH.Spectra.Orthogonal.fibrantFactorizationData.fac_app⟩

/-- Both actual symmetric K natural transformations are the original same-cardinal maps. -/
theorem symmetricKFactorizationData_fields :
    symmetricKFactorizationData.{u, v}.Z = (NativeK.factorizationData symmetricFamily).Z ∧
      symmetricKFactorizationData.i = (NativeK.factorizationData symmetricFamily).i ∧
      symmetricKFactorizationData.p = (NativeK.factorizationData symmetricFamily).p :=
  ⟨rfl, rfl, rfl⟩

/-- Both actual orthogonal K natural transformations retain the same original functions. -/
theorem orthogonalKFactorizationData_fields :
    orthogonalKFactorizationData.{u, v}.Z = (NativeK.factorizationData orthogonalFamily).Z ∧
      orthogonalKFactorizationData.i = (NativeK.factorizationData orthogonalFamily).i ∧
      orthogonalKFactorizationData.p = (NativeK.factorizationData orthogonalFamily).p :=
  ⟨rfl, rfl, rfl⟩

/-- Every full symmetric Arrow input keeps the actual original intermediate map. -/
theorem symmetricKFactorizationData_Z_map
    {f g : CategoryTheory.Arrow SymmetricCarrier.{u, v}} (φ : f ⟶ g) :
    symmetricKFactorizationData.Z.map φ =
      SmallObject.objMap symmetricK realizedGeneratorCardinal.{v} φ :=
  NativeK.factorizationData_Z_map symmetricFamily φ

/-- Every full orthogonal Arrow input retains the literal same-cardinal map function. -/
theorem orthogonalKFactorizationData_Z_map
    {f g : CategoryTheory.Arrow OrthogonalCarrier.{u, v}} (φ : f ⟶ g) :
    orthogonalKFactorizationData.Z.map φ =
      SmallObject.objMap orthogonalK realizedGeneratorCardinal.{v} φ :=
  NativeK.factorizationData_Z_map orthogonalFamily φ

/-- The native symmetric K-right class recognizes precisely actual native Omega objects. -/
theorem symmetricK_local_iff_isOmega (X : SymmetricCarrier.{u, v}) :
    symmetricK.rlp (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.toZero X) ↔
      SymmetricIsOmega X :=
  NativeK.lifting_toZero_iff_isOmega symmetricFamily X

/-- The actual orthogonal K-right class recognizes its own full original Omega action. -/
theorem orthogonalK_local_iff_isOmega (X : OrthogonalCarrier.{u, v}) :
    orthogonalK.rlp (HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.toZero X) ↔
      OrthogonalIsOmega X :=
  NativeK.lifting_toZero_iff_isOmega orthogonalFamily X

/-- The actual original symmetric K algorithm supplies a whole native Omega replacement functor. -/
def symmetricOmegaReplacement : SymmetricCarrier.{u, v} ⥤ SymmetricCarrier.{u, v} :=
  NativeK.omegaReplacement symmetricFamily

/-- The actual original orthogonal K algorithm retains the full continuous carrier as its output. -/
def orthogonalOmegaReplacement : OrthogonalCarrier.{u, v} ⥤ OrthogonalCarrier.{u, v} :=
  NativeK.omegaReplacement orthogonalFamily

/-- Every actual original symmetric replacement output has the entire native Omega condition. -/
theorem symmetricOmegaReplacement_isOmega (X : SymmetricCarrier.{u, v}) :
    SymmetricIsOmega (symmetricOmegaReplacement.obj X) :=
  NativeK.omegaReplacement_isOmega symmetricFamily X

/-- Every actual original orthogonal output satisfies all representation-sphere Omega conditions. -/
theorem orthogonalOmegaReplacement_isOmega (X : OrthogonalCarrier.{u, v}) :
    OrthogonalIsOmega (orthogonalOmegaReplacement.obj X) :=
  NativeK.omegaReplacement_isOmega orthogonalFamily X

/-- Native symmetric weak tests use the actual level homotopy source functions and Omega targets. -/
abbrev symmetricOmegaTests : MorphismProperty SymmetricCarrier.{u, v} :=
  NativeK.omegaTests symmetricFamily

/-- Native orthogonal weak tests use their own complete original representation-sphere targets. -/
abbrev orthogonalOmegaTests : MorphismProperty OrthogonalCarrier.{u, v} :=
  NativeK.omegaTests orthogonalFamily

/-- Between genuine native symmetric Omega objects, the actual source tests are levelwise weak. -/
theorem symmetricOmegaTests_iff_levelWeak
    {X Y : SymmetricCarrier.{u, v}} (f : X ⟶ Y)
    (hX : SymmetricIsOmega X) (hY : SymmetricIsOmega Y) :
    symmetricOmegaTests f ↔
      letI : ModelCategory SymmetricCarrier.{u, v} := PointedCGWH.Spectra.Symmetric.levelModel
      weakEquivalences SymmetricCarrier.{u, v} f :=
  NativeK.omegaTests_iff_levelWeak_of_isOmega symmetricFamily f hX hY

/-- Between orthogonal Omega objects, the full source tests detect the level model. -/
theorem orthogonalOmegaTests_iff_levelWeak
    {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    (hX : OrthogonalIsOmega X) (hY : OrthogonalIsOmega Y) :
    orthogonalOmegaTests f ↔
      letI : ModelCategory OrthogonalCarrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
      weakEquivalences OrthogonalCarrier.{u, v} f :=
  NativeK.omegaTests_iff_levelWeak_of_isOmega orthogonalFamily f hX hY

end Actual

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
