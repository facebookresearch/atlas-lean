/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.PeriodCoefficientComplexSources

/-!
# Normalized BASE filtered de Rham association

The lisse scalar extensions, original vector bundle extension, full
structural filtration and coefficient connection are actual native
objects. This is BASE associated data as in Scholze Definition 7.5.
Its filtered/horizontal isomorphism is allowed input. There is NO higher
bundle, higher filtration, higher connection or higher comparison here.

Full module filtrations are native sheaf submodules over the POSITIVE
structural ring. They use the original coefficient filtration and the
actual ideal-sheaf/local-fraction period filtration.

References: Scholze, arXiv:1205.3463v2, Definitions 7.4--7.5, Theorem 7.6
and Definition 8.3; native Mathlib, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.BaseFilteredPeriodAssociation

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry.GeneralPadicCoefficientFields
open RingedDerivedCoefficientOperations NativeFilteredDeRhamOutputs RingSheafModuleTensors
open StructuralDeRhamPeriodSources UntiltingSheafSources StructuralPeriodConnectionSources

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [UnivLE.{max u v, 1}] [HasSheafify J CommRingCat.{1}]
  [HasSheafify J AddCommGrpCat.{1}] [J.WEqualsLocallyBijective AddCommGrpCat.{1}]
  (p : ℕ) [Fact p.Prime] (K : BaseField p)
  (O Rplus Z : Sheaf J CommRingCat.{1}) (A : UntiltingData p Rplus)
  (W : WittScalarSource p K O Rplus A) (z : Z ⟶ A.deRhamPositive) (L : Modules Z)
  (M Ω : Modules O) (F : CoefficientFiltration O M)
  [(pushforward (𝟭 C) O W.naiveStructuralPositive W.originalToPositive).IsRightAdjoint]
  [(pushforward (𝟭 C) W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).IsRightAdjoint]
  [(pushforward (𝟭 C) Z A.deRhamPositive z).IsRightAdjoint]

def absoluteToStructuralFull : A.deRhamPositive ⟶ W.naiveStructuralFull :=
  W.absoluteToPositive ≫ W.positiveToFull

variable [(pushforward (𝟭 C) A.deRhamPositive W.naiveStructuralFull
  (absoluteToStructuralFull p K O Rplus A W)).IsRightAdjoint]

def localSystemPositive : Modules A.deRhamPositive := (pullback (𝟭 C) Z A.deRhamPositive z).obj L
def localSystemFull : Modules W.naiveStructuralFull :=
  (pullback (𝟭 C) A.deRhamPositive W.naiveStructuralFull (absoluteToStructuralFull p K O Rplus A W)).obj
    (localSystemPositive p Rplus Z A z L)

def localSystemUnit (U : Cᵒᵖ) : (localSystemPositive p Rplus Z A z L).val.obj U →+
    (localSystemFull p K O Rplus Z A W z L).val.obj U :=
  (((adjunction (𝟭 C) A.deRhamPositive W.naiveStructuralFull (absoluteToStructuralFull p K O Rplus A W)).unit.app
    (localSystemPositive p Rplus Z A z L)).val.app U).hom.toAddMonoidHom

def vectorFull := fullForms p K O Rplus A W M

def vectorFiltration (i : ℤ) :
    ((restrict W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).obj (vectorFull p K O Rplus A W M)).Submodule :=
  sInf {N | ∀ (U : Cᵒᵖ) (j : ℤ)
    (m : (F.pieces j).toSheafOfModules.val.obj U) (r : W.naiveStructuralFull.obj.obj U),
    r ∈ (WittScalarSource.structuralFiltration p K O Rplus A W (i - j)).sections U →
      (show ((restrict W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).obj
        (vectorFull p K O Rplus A W M)).val.obj U from
        r • originalFullFormSemilinearUnit p K O Rplus A W M U (((F.pieces j).ι.val.app U).hom m)) ∈ N.toSubmodule.obj U}

def localSystemFiltration (i : ℤ) :
    ((restrict W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).obj
      (localSystemFull p K O Rplus Z A W z L)).Submodule :=
  sInf {N | ∀ (U : Cᵒᵖ) (m : (localSystemPositive p Rplus Z A z L).val.obj U) (r : W.naiveStructuralFull.obj.obj U),
    r ∈ (WittScalarSource.structuralFiltration p K O Rplus A W i).sections U →
      (show ((restrict W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).obj
        (localSystemFull p K O Rplus Z A W z L)).val.obj U from r • localSystemUnit p K O Rplus Z A W z L U m) ∈
          N.toSubmodule.obj U}

variable (d : ∀ U : Cᵒᵖ, O.obj.obj U →+ Ω.val.obj U)
  (nabla : ∀ U : Cᵒᵖ, M.val.obj U →+ (tensor O M Ω).val.obj U)
  (P : PositiveConnectionSource p K O Rplus A W Ω d)
  (Q : FullConnectionSource p K O Rplus A W Ω d P)

/-- Total coefficient connection on the ACTUAL base vector bundle period extension. -/
structure CoefficientConnectionSource where
  originalTensor : tensor O M Ω ⟶
    (pushforward (𝟭 C) O W.naiveStructuralPositive W.originalToPositive).obj
      ((pushforward (𝟭 C) W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).obj
        (tensor W.naiveStructuralFull (vectorFull p K O Rplus A W M) (fullForms p K O Rplus A W Ω)))
  tensor_source : ∀ U m w,
    (originalTensor.val.app U).hom (generator O M Ω U m w) =
    (show ((pushforward (𝟭 C) O W.naiveStructuralPositive W.originalToPositive).obj
      ((pushforward (𝟭 C) W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).obj
        (tensor W.naiveStructuralFull (vectorFull p K O Rplus A W M) (fullForms p K O Rplus A W Ω)))).val.obj U from
      generator W.naiveStructuralFull (vectorFull p K O Rplus A W M) (fullForms p K O Rplus A W Ω) U
        (originalFullFormSemilinearUnit p K O Rplus A W M U m)
        (originalFullFormSemilinearUnit p K O Rplus A W Ω U w))
  connection : ∀ U : Cᵒᵖ, (vectorFull p K O Rplus A W M).val.obj U →+
    (tensor W.naiveStructuralFull (vectorFull p K O Rplus A W M) (fullForms p K O Rplus A W Ω)).val.obj U
  natural : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) m,
    connection V ((vectorFull p K O Rplus A W M).val.map f m) =
      (tensor W.naiveStructuralFull (vectorFull p K O Rplus A W M) (fullForms p K O Rplus A W Ω)).val.map f (connection U m)
  original_source : ∀ (U : Cᵒᵖ) (r : W.naiveStructuralFull.obj.obj U) (m : M.val.obj U),
    connection U (r • originalFullFormSemilinearUnit p K O Rplus A W M U m) =
      r • (show (tensor W.naiveStructuralFull (vectorFull p K O Rplus A W M) (fullForms p K O Rplus A W Ω)).val.obj U from
        (originalTensor.val.app U).hom (nabla U m)) +
      generator W.naiveStructuralFull (vectorFull p K O Rplus A W M) (fullForms p K O Rplus A W Ω) U
        (originalFullFormSemilinearUnit p K O Rplus A W M U m) (Q.connection U r)

variable (conn : CoefficientConnectionSource p K O Rplus A W M Ω d nabla P Q)

/-- BASE associated filtered/horizontal data. Higher outputs are constructed elsewhere. -/
structure Associated where
  comparison : localSystemFull p K O Rplus Z A W z L ≅ vectorFull p K O Rplus A W M
  filtered : ∀ (i : ℤ) (U : Cᵒᵖ) (m : (localSystemFull p K O Rplus Z A W z L).val.obj U),
    (show ((restrict W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).obj
      (localSystemFull p K O Rplus Z A W z L)).val.obj U from m) ∈
        (localSystemFiltration p K O Rplus Z A W z L i).toSubmodule.obj U ↔
    (show ((restrict W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).obj
      (vectorFull p K O Rplus A W M)).val.obj U from (comparison.hom.val.app U).hom m) ∈
        (vectorFiltration p K O Rplus A W M F i).toSubmodule.obj U
  horizontal : ∀ (U : Cᵒᵖ) (m : (localSystemPositive p Rplus Z A z L).val.obj U),
    conn.connection U ((comparison.hom.val.app U).hom (localSystemUnit p K O Rplus Z A W z L U m)) = 0

/-- Filtered/horizontal properties of an ACTUAL constructed comparison map. -/
structure AssociatedMapProperties
    (comparison : localSystemFull p K O Rplus Z A W z L ⟶ vectorFull p K O Rplus A W M) : Prop where
  filtered : ∀ (i : ℤ) (U : Cᵒᵖ) (m : (localSystemFull p K O Rplus Z A W z L).val.obj U),
    (show ((restrict W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).obj
      (localSystemFull p K O Rplus Z A W z L)).val.obj U from m) ∈
        (localSystemFiltration p K O Rplus Z A W z L i).toSubmodule.obj U ↔
    (show ((restrict W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).obj
      (vectorFull p K O Rplus A W M)).val.obj U from (comparison.val.app U).hom m) ∈
        (vectorFiltration p K O Rplus A W M F i).toSubmodule.obj U
  horizontal : ∀ (U : Cᵒᵖ) (m : (localSystemPositive p Rplus Z A z L).val.obj U),
    conn.connection U ((comparison.val.app U).hom (localSystemUnit p K O Rplus Z A W z L U m)) = 0


/-- An association is OUTPUT from the actual map and its proved properties. -/
def associatedOfMap
    (comparison : localSystemFull p K O Rplus Z A W z L ⟶ vectorFull p K O Rplus A W M)
    [IsIso comparison]
    (H : AssociatedMapProperties p K O Rplus Z A W z L M Ω F d nabla P Q conn comparison) :
    Associated p K O Rplus Z A W z L M Ω F d nabla P Q conn where
  comparison := asIso comparison
  filtered := H.filtered
  horizontal := H.horizontal

end MathlibExt.CategoryTheory.BaseFilteredPeriodAssociation
