/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AdicDerivedContracts
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Continuous adic coefficient rings and their fixed module presentation

The coefficient ring is literally the continuous-function sheaf `E_X`
of Bhatt--Scholze, Definition 6.8.1. Its modules belong to Mathlib's
`SheafOfModules`, with the sectionwise continuous-function scalar action.
The comparison with sheaves of abstract `E`-modules is the native forgetful
functor followed by restriction along constant continuous functions.

This completed construction asserts no equivalence of the ambient derived
categories. Such a comparison on the constructible scope is a separate
dependency of any use of that presentation.

References: Bhatt--Scholze, *The pro-etale topology for schemes*, Lemma
4.2.12 and Definition 6.8.1, https://arxiv.org/abs/1309.1198.
The continuous-function sheaf proof is Mathlib's fpqc sheaf theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.ContinuousAdicRingModules

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open ContinuousAdicCoefficients

variable (E : Type) [CommRing E] [TopologicalSpace E]
  [IsTopologicalRing E]

/-- The pointwise continuous-function ring presheaf on actual schemes. -/
def continuousRingPresheaf : Scheme.{0}ᵒᵖ ⥤ RingCat.{1} where
  obj U := RingCat.of C(U.unop, ULift.{1} E)
  map f := RingCat.ofHom
    { toFun a := a.comp f.unop.base.hom
      map_zero' := rfl
      map_one' := rfl
      map_add' _ _ := rfl
      map_mul' _ _ := rfl }
  map_id U := by
    apply RingCat.hom_ext
    apply RingHom.ext
    intro a
    apply ContinuousMap.ext
    intro x
    rfl
  map_comp f g := by
    apply RingCat.hom_ext
    apply RingHom.ext
    intro a
    apply ContinuousMap.ext
    intro x
    rfl

/-- The actual ring sheaf of continuous coefficients on the big site. -/
def globalContinuousRing : Sheaf proetaleTopology RingCat.{1} :=
  ⟨continuousRingPresheaf E, by
    apply Presheaf.IsSheaf.of_le proetaleTopology_le_fpqcTopology
    apply (Presheaf.isSheaf_iff_isSheaf_forget fpqcTopology
      (continuousRingPresheaf E) (forget RingCat.{1})).mpr
    exact isSheaf_fpqcTopology_continuousMapPresheaf (ULift.{1} E)⟩

/-- The literal small-site continuous coefficient ring `E_X`. -/
def coefficientRing (X : Scheme) : Sheaf (ProEt.topology X) RingCat.{1} :=
  ((ProEt.forget X ⋙ Over.forget X).sheafPushforwardContinuous
    RingCat.{1} (ProEt.topology X) proetaleTopology).obj
      (globalContinuousRing E)

/-- Actual sheaves of modules over the continuous coefficient ring. -/
abbrev CoefficientModules (X : Scheme) :=
  SheafOfModules.{1} (coefficientRing E X)

/-- Constants as an actual ring map into continuous global sections. -/
def constantScalars (X : Scheme) :
    E →+* (coefficientRing E X).obj.obj (op (⊤_ X.ProEt)) where
  toFun a := ContinuousMap.const (⊤_ X.ProEt).left (ULift.up a)
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The fixed underlying abstract-coefficient module-sheaf functor.
No free comparison functor or scalar action is selected. -/
def underlying (X : Scheme) :
    CoefficientModules E X ⥤ CoefficientSheaf X E :=
  SheafOfModules.forgetToSheafModuleCat (coefficientRing E X)
    (op (⊤_ X.ProEt)) (terminalIsTerminal (C := X.ProEt)).op ⋙
      sheafCompose (ProEt.topology X)
        (ModuleCat.restrictScalars (constantScalars E X))

instance underlying_additive (X : Scheme) : (underlying E X).Additive where
  map_add := rfl

/-- The underlying continuous coefficient-ring unit is the prescribed
continuous coefficient object, by the identity on every section. -/
def unitUnderlyingIso (X : Scheme) :
    (underlying E X).obj (SheafOfModules.unit (coefficientRing E X)) ≅
      continuousModuleSheaf E (ULift.{1} E) X :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦
    { hom := ModuleCat.ofHom
        (X := ((underlying E X).obj
          (SheafOfModules.unit (coefficientRing E X))).obj.obj U)
        (Y := (continuousModuleSheaf E (ULift.{1} E) X).obj.obj U)
        { toFun := fun a ↦ a
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a b ↦ by
            apply ContinuousMap.ext
            intro x
            rfl }
      inv := ModuleCat.ofHom
        (X := (continuousModuleSheaf E (ULift.{1} E) X).obj.obj U)
        (Y := ((underlying E X).obj
          (SheafOfModules.unit (coefficientRing E X))).obj.obj U)
        { toFun := fun a ↦ a
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a b ↦ by
            apply ContinuousMap.ext
            intro x
            rfl }
      hom_inv_id := by ext a; rfl
      inv_hom_id := by ext a; rfl })
    (by intro U V f; ext a; rfl))

attribute [local instance] HasDerivedCategory.standard

/-- The actual bounded-below derived category over `E_X`. -/
abbrev CoefficientDerived (X : Scheme) :=
  DerivedCategory.Plus (CoefficientModules E X)

/-- The fixed native right-derived forgetful functor. Its identification
with the exact degreewise forgetful functor is an adapter obligation. -/
def derivedUnderlying (X : Scheme)
    [EnoughInjectives (CoefficientModules E X)] :
    CoefficientDerived E X ⥤ AdicDerivedContracts.Derived E X :=
  (underlying E X).rightDerivedFunctorPlus

/-- The fixed discrete-point-unit coefficient map, characterized by
constant continuous functions through the actual sections adjunction. -/
def unitCoefficientMap (X : Scheme) :
    ProEtaleCohomologyFunctoriality.constantUnit E X ⟶
      continuousModuleSheaf E (ULift.{1} E) X :=
  ((constantSheafAdj (ProEt.topology X) (ModuleCat.{1} E)
    (terminalIsTerminal (C := X.ProEt))).homEquiv
      (ModuleCat.of E (ULift.{1} E)) _).symm
    (ModuleCat.ofHom
      { toFun a := ContinuousMap.const (⊤_ X.ProEt).left a
        map_add' _ _ := rfl
        map_smul' _ _ := rfl })

end MathlibExt.AlgebraicGeometry.ContinuousAdicRingModules
