/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
public import MathlibExt.AlgebraicTopology.ModelCategory.ExplicitModelFactorization
public import MathlibExt.AlgebraicTopology.ModelCategory.GivenFactorizationReplacements

/-!
# A model constructed from the original two families and given factor records

The caller supplies the two actual functorial factorization records, the
two-out-of-three and acyclicity laws, and the right-class comparison.
Recognition proves the left-class comparison from the same given K record.
The resulting model has precisely the supplied candidate weak
class, the original I-left class and the original K-right class.

Both weak factorization systems use the supplied records. The returned I/K
factorizations only change membership proofs with `ofLE`. Their entire middle
functors and both natural maps are the original values. Model-keyed carriers
allow this model and an existing level model to coexist on the same underlying
category. No desired model, localization packet or equality of default chosen
factorizations is an input or conclusion.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.OriginalGeneratedModel

variable {C : Type u} [Category.{v} C]

/-- The entire given right-orthogonal factorization proves its actual WFS. -/
theorem weakFactorizationSystemOfGiven (P : MorphismProperty C)
    (data : FunctorialFactorizationData P.rlp.llp P.rlp) :
    IsWeakFactorizationSystem P.rlp.llp P.rlp := by
  let : HasFunctorialFactorization P.rlp.llp P.rlp := ⟨⟨data⟩⟩
  exact IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp => hi p hp)

/-- The actual two factor records and their proved recognition equations. -/
@[ext]
structure RecognitionData (I W : MorphismProperty C) where
  /-- The caller's original trivial-cofibration family. -/
  J : MorphismProperty C
  /-- The entire original I record. -/
  givenI : FunctorialFactorizationData I.rlp.llp I.rlp
  /-- The entire original J record. -/
  givenK : FunctorialFactorizationData J.rlp.llp J.rlp
  /-- Recognition identifies the actual trivial-left class. -/
  trivialCofibrations_eq : J.rlp.llp = I.rlp.llp ⊓ W
  /-- The supplied right-class law identifies the actual trivial-right class. -/
  trivialFibrations_eq : J.rlp ⊓ W = I.rlp

namespace RecognitionData

variable {I W : MorphismProperty C} (d : RecognitionData I W)

include d in
/-- The original I record supplies the first weak factorization system. -/
theorem cofibration_wfs : IsWeakFactorizationSystem I.rlp.llp I.rlp :=
  weakFactorizationSystemOfGiven I d.givenI

/-- The original J record supplies the second weak factorization system. -/
theorem trivialCofibration_wfs : IsWeakFactorizationSystem d.J.rlp.llp d.J.rlp :=
  weakFactorizationSystemOfGiven d.J d.givenK

/-- The right orthogonal is the one determined by the same proved left class. -/
theorem fibrations_eq : d.J.rlp = (I.rlp.llp ⊓ W).rlp := by
  rw [← d.trivialCofibrations_eq, d.J.rlp_llp_rlp]

end RecognitionData

/-- The actual given K factor of each arrow proves the whole left-class equality. -/
theorem left_class_eq (I K W : MorphismProperty C)
    (hW : W.HasTwoOutOfThreeProperty) (hRight : I.rlp = K.rlp ⊓ W)
    (hAcyclic : K.rlp.llp ≤ W)
    (givenK : FunctorialFactorizationData K.rlp.llp K.rlp) :
    K.rlp.llp = I.rlp.llp ⊓ W := by
  let : W.HasTwoOutOfThreeProperty := hW
  have hRightLe : I.rlp ≤ K.rlp := hRight.le.trans inf_le_left
  have hForward : K.rlp.llp ≤ I.rlp.llp ⊓ W :=
    le_inf (MorphismProperty.antitone_llp hRightLe) hAcyclic
  have hReverse : I.rlp.llp ⊓ W ≤ K.rlp.llp := by
    intro X Y f hf
    let d := givenK.factorizationData f
    have hiW : W d.i := hAcyclic _ d.hi
    have hcomp : W (d.i ≫ d.p) := by
      rw [d.fac]
      exact hf.2
    have hpW : W d.p := W.of_precomp _ _ hiW hcomp
    have hpI : I.rlp d.p := by
      rw [hRight]
      exact ⟨d.hp, hpW⟩
    let : HasLiftingProperty f d.p := hf.1 _ hpI
    exact K.rlp.llp.of_retract (RetractArrow.ofLeftLiftingProperty d.fac) d.hi
  exact le_antisymm hForward hReverse

variable (I K W : MorphismProperty C)
  (hW : W.HasTwoOutOfThreeProperty)
  (hRight : I.rlp = K.rlp ⊓ W)
  (hAcyclic : K.rlp.llp ≤ W)
  (givenI : FunctorialFactorizationData I.rlp.llp I.rlp)
  (givenK : FunctorialFactorizationData K.rlp.llp K.rlp)

/-- Retain both original records and derive recognition from the actual given K factors. -/
def recognition : RecognitionData I W where
  J := K
  givenI := givenI
  givenK := givenK
  trivialCofibrations_eq := left_class_eq I K W hW hRight hAcyclic givenK
  trivialFibrations_eq := hRight.symm

/-- The generating trivial-cofibration family remains precisely the original K. -/
theorem recognition_J : (recognition I K W hW hRight hAcyclic givenI givenK).J = K := rfl

/-- The entire first record in recognition is the original supplied I value. -/
theorem recognition_givenI :
    (recognition I K W hW hRight hAcyclic givenI givenK).givenI = givenI := rfl

/-- The entire second record in recognition is the original supplied K value. -/
theorem recognition_givenK :
    (recognition I K W hW hRight hAcyclic givenI givenK).givenK = givenK := rfl

include givenI in
/-- The original given I record supplies the complete cofibration WFS. -/
theorem original_I_wfs : IsWeakFactorizationSystem I.rlp.llp I.rlp :=
  weakFactorizationSystemOfGiven I givenI

include givenK in
/-- The original given K record supplies the complete trivial-cofibration WFS. -/
theorem original_K_wfs : IsWeakFactorizationSystem K.rlp.llp K.rlp :=
  weakFactorizationSystemOfGiven K givenK

section Model

variable [HasFiniteLimits C] [HasFiniteColimits C]

/-- Construct the model with its three literal original morphism classes. -/
@[instance_reducible]
def modelCategory : ModelCategory C := by
  letI : CategoryWithCofibrations C := ⟨I.rlp.llp⟩
  letI : CategoryWithFibrations C := ⟨K.rlp⟩
  letI : CategoryWithWeakEquivalences C := ⟨W⟩
  let d := recognition I K W hW hRight hAcyclic givenI givenK
  letI : (weakEquivalences C).HasTwoOutOfThreeProperty := hW
  letI : IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C) := by
    change IsWeakFactorizationSystem I.rlp.llp (K.rlp ⊓ W)
    rw [← hRight]
    exact d.cofibration_wfs
  letI : IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C) := by
    change IsWeakFactorizationSystem (I.rlp.llp ⊓ W) K.rlp
    rw [← d.trivialCofibrations_eq]
    exact d.trivialCofibration_wfs
  exact ModelCategory.mk' C

/-- The constructed weak class is the entire original candidate property. -/
theorem weakEquivalences_eq :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    weakEquivalences C = W := rfl

/-- The constructed cofibrations are exactly the original I-left class. -/
theorem cofibrations_eq :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    cofibrations C = I.rlp.llp := rfl

/-- The constructed fibrations are exactly the entire original K-right class. -/
theorem fibrations_eq :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    fibrations C = K.rlp := rfl

/-- Recognition, rather than a supplied model, identifies the whole trivial-left class. -/
theorem trivialCofibrations_eq :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    trivialCofibrations C = K.rlp.llp := by
  let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
  change I.rlp.llp ⊓ W = K.rlp.llp
  exact (left_class_eq I K W hW hRight hAcyclic givenK).symm

/-- The necessary all-arrow right-class law gives exactly the original I-right class. -/
theorem trivialFibrations_eq :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    trivialFibrations C = I.rlp := by
  let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
  change K.rlp ⊓ W = I.rlp
  exact hRight.symm

/-- All five classes belong to this single constructed model dictionary. -/
theorem five_classes :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    weakEquivalences C = W ∧ cofibrations C = I.rlp.llp ∧ fibrations C = K.rlp ∧
      trivialCofibrations C = K.rlp.llp ∧ trivialFibrations C = I.rlp := by
  let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
  exact ⟨rfl, rfl, rfl,
    trivialCofibrations_eq I K W hW hRight hAcyclic givenI givenK,
    trivialFibrations_eq I K W hW hRight hAcyclic givenI givenK⟩

/-- The first model WFS is the original I WFS under the proved class equations. -/
theorem model_I_wfs :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C) := by
  change IsWeakFactorizationSystem I.rlp.llp (K.rlp ⊓ W)
  rw [← hRight]
  exact weakFactorizationSystemOfGiven I givenI

/-- The second model WFS is the original K WFS under the recognition equality. -/
theorem model_K_wfs :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C) := by
  change IsWeakFactorizationSystem (I.rlp.llp ⊓ W) K.rlp
  rw [← left_class_eq I K W hW hRight hAcyclic givenK]
  exact weakFactorizationSystemOfGiven K givenK

/-- Retype the entire supplied I record using only the exact two class equations. -/
def cofibrantFactorizationData :
    letI : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    FunctorialFactorizationData (cofibrations C) (trivialFibrations C) := by
  letI : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
  exact givenI.ofLE
    (by rw [cofibrations_eq I K W hW hRight hAcyclic givenI givenK])
    (by rw [trivialFibrations_eq I K W hW hRight hAcyclic givenI givenK])

/-- Retype the entire supplied K record without rerunning any factor construction. -/
def fibrantFactorizationData :
    letI : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    FunctorialFactorizationData (trivialCofibrations C) (fibrations C) := by
  letI : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
  exact givenK.ofLE
    (by rw [trivialCofibrations_eq I K W hW hRight hAcyclic givenI givenK])
    (by rw [fibrations_eq I K W hW hRight hAcyclic givenI givenK])

/-- The complete I middle functor is the supplied original function. -/
theorem cofibrantFactorizationData_Z :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    (cofibrantFactorizationData I K W hW hRight hAcyclic givenI givenK).Z = givenI.Z := rfl

/-- The complete K middle functor is the supplied original function. -/
theorem fibrantFactorizationData_Z :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    (fibrantFactorizationData I K W hW hRight hAcyclic givenI givenK).Z = givenK.Z := rfl

/-- The complete first I natural arrow retains the original value. -/
theorem cofibrantFactorizationData_i :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    (cofibrantFactorizationData I K W hW hRight hAcyclic givenI givenK).i = givenI.i := rfl

/-- The complete second I natural arrow retains the original value. -/
theorem cofibrantFactorizationData_p :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    (cofibrantFactorizationData I K W hW hRight hAcyclic givenI givenK).p = givenI.p := rfl

/-- The complete first K natural arrow retains the original value. -/
theorem fibrantFactorizationData_i :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    (fibrantFactorizationData I K W hW hRight hAcyclic givenI givenK).i = givenK.i := rfl

/-- The complete second K natural arrow retains the original value. -/
theorem fibrantFactorizationData_p :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    (fibrantFactorizationData I K W hW hRight hAcyclic givenI givenK).p = givenK.p := rfl

/-- Every original I Arrow action is the supplied full middle map. -/
theorem cofibrantFactorizationData_map {F G : Arrow C} (a : F ⟶ G) :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    (cofibrantFactorizationData I K W hW hRight hAcyclic givenI givenK).Z.map a =
      givenI.Z.map a := rfl

/-- Every original K Arrow action is the supplied full middle map. -/
theorem fibrantFactorizationData_map {F G : Arrow C} (a : F ⟶ G) :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    (fibrantFactorizationData I K W hW hRight hAcyclic givenI givenK).Z.map a =
      givenK.Z.map a := rfl

/-- The supplied I factors still compose to every entire caller arrow. -/
theorem cofibrantFactorizationData_fac (F : Arrow C) :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    (cofibrantFactorizationData I K W hW hRight hAcyclic givenI givenK).i.app F ≫
      (cofibrantFactorizationData I K W hW hRight hAcyclic givenI givenK).p.app F = F.hom :=
  givenI.fac_app

/-- The supplied K factors still compose to every entire caller arrow. -/
theorem fibrantFactorizationData_fac (F : Arrow C) :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    (fibrantFactorizationData I K W hW hRight hAcyclic givenI givenK).i.app F ≫
      (fibrantFactorizationData I K W hW hRight hAcyclic givenI givenK).p.app F = F.hom :=
  givenK.fac_app

/-- Move the original I record to the carrier keyed by the constructed model. -/
def cofibrantFactorizationOnCarrier :
    FunctorialFactorizationData
      (cofibrations (ExplicitModelIdentity.Carrier
        (modelCategory I K W hW hRight hAcyclic givenI givenK)))
      (trivialFibrations (ExplicitModelIdentity.Carrier
        (modelCategory I K W hW hRight hAcyclic givenI givenK))) := by
  let m := modelCategory I K W hW hRight hAcyclic givenI givenK
  let raw := ExplicitModelIdentity.factorizationOnCarrier m givenI
  exact raw.ofLE
    (by
      intro X Y f hf
      change I.rlp.llp f.hom at hf ⊢
      exact hf)
    (by
      intro X Y f hf
      change I.rlp f.hom at hf
      change (K.rlp ⊓ W) f.hom
      rw [← hRight]
      exact hf)

/-- Move the original K record to the same model-keyed carrier. -/
def fibrantFactorizationOnCarrier :
    FunctorialFactorizationData
      (trivialCofibrations (ExplicitModelIdentity.Carrier
        (modelCategory I K W hW hRight hAcyclic givenI givenK)))
      (fibrations (ExplicitModelIdentity.Carrier
        (modelCategory I K W hW hRight hAcyclic givenI givenK))) := by
  let m := modelCategory I K W hW hRight hAcyclic givenI givenK
  let raw := ExplicitModelIdentity.factorizationOnCarrier m givenK
  exact raw.ofLE
    (by
      intro X Y f hf
      change K.rlp.llp f.hom at hf
      change (I.rlp.llp ⊓ W) f.hom
      rw [← left_class_eq I K W hW hRight hAcyclic givenK]
      exact hf)
    (by
      intro X Y f hf
      change K.rlp f.hom at hf ⊢
      exact hf)

/-- The entire carrier I middle functor retains the exact supplied I value. -/
theorem cofibrantFactorizationOnCarrier_Z :
    (cofibrantFactorizationOnCarrier I K W hW hRight hAcyclic givenI givenK).Z =
      (ExplicitModelIdentity.toBase
        (modelCategory I K W hW hRight hAcyclic givenI givenK)).mapArrow ⋙
          givenI.Z ⋙ ExplicitModelIdentity.ofBase
            (modelCategory I K W hW hRight hAcyclic givenI givenK) := rfl

/-- The entire carrier K middle functor retains the exact supplied K value. -/
theorem fibrantFactorizationOnCarrier_Z :
    (fibrantFactorizationOnCarrier I K W hW hRight hAcyclic givenI givenK).Z =
      (ExplicitModelIdentity.toBase
        (modelCategory I K W hW hRight hAcyclic givenI givenK)).mapArrow ⋙
          givenK.Z ⋙ ExplicitModelIdentity.ofBase
            (modelCategory I K W hW hRight hAcyclic givenI givenK) := rfl

/-- Every carrier I left leg is the original underlying left leg on that same arrow. -/
theorem cofibrantFactorizationOnCarrier_i
    (F : Arrow (ExplicitModelIdentity.Carrier
      (modelCategory I K W hW hRight hAcyclic givenI givenK))) :
    ((cofibrantFactorizationOnCarrier I K W hW hRight hAcyclic givenI givenK).i.app F).hom =
      givenI.i.app ((ExplicitModelIdentity.toBase
        (modelCategory I K W hW hRight hAcyclic givenI givenK)).mapArrow.obj F) := rfl

/-- Every carrier I right leg is the original underlying right leg. -/
theorem cofibrantFactorizationOnCarrier_p
    (F : Arrow (ExplicitModelIdentity.Carrier
      (modelCategory I K W hW hRight hAcyclic givenI givenK))) :
    ((cofibrantFactorizationOnCarrier I K W hW hRight hAcyclic givenI givenK).p.app F).hom =
      givenI.p.app ((ExplicitModelIdentity.toBase
        (modelCategory I K W hW hRight hAcyclic givenI givenK)).mapArrow.obj F) := rfl

/-- Every carrier K left leg is the original underlying left leg. -/
theorem fibrantFactorizationOnCarrier_i
    (F : Arrow (ExplicitModelIdentity.Carrier
      (modelCategory I K W hW hRight hAcyclic givenI givenK))) :
    ((fibrantFactorizationOnCarrier I K W hW hRight hAcyclic givenI givenK).i.app F).hom =
      givenK.i.app ((ExplicitModelIdentity.toBase
        (modelCategory I K W hW hRight hAcyclic givenI givenK)).mapArrow.obj F) := rfl

/-- Every carrier K right leg is the original underlying right leg. -/
theorem fibrantFactorizationOnCarrier_p
    (F : Arrow (ExplicitModelIdentity.Carrier
      (modelCategory I K W hW hRight hAcyclic givenI givenK))) :
    ((fibrantFactorizationOnCarrier I K W hW hRight hAcyclic givenI givenK).p.app F).hom =
      givenK.p.app ((ExplicitModelIdentity.toBase
        (modelCategory I K W hW hRight hAcyclic givenI givenK)).mapArrow.obj F) := rfl

/-- The complete cofibrant replacement uses the actual supplied I record and initial object. -/
def cofibrantReplacement (Z : C) (hZ : IsInitial Z) : C ⥤ C :=
  GivenFactorizationReplacements.initialReplacement
    (cofibrantFactorizationData I K W hW hRight hAcyclic givenI givenK) Z hZ

/-- The complete fibrant replacement uses the actual supplied K record and terminal object. -/
def fibrantReplacement (Z : C) (hZ : IsTerminal Z) : C ⥤ C :=
  GivenFactorizationReplacements.terminalReplacement
    (fibrantFactorizationData I K W hW hRight hAcyclic givenI givenK) Z hZ

/-- The complete I replacement projection remains the original actual right-factor function. -/
def cofibrantReplacementProjection (Z : C) (hZ : IsInitial Z) :
    cofibrantReplacement I K W hW hRight hAcyclic givenI givenK Z hZ ⟶ 𝟭 C :=
  GivenFactorizationReplacements.initialProjection
    (cofibrantFactorizationData I K W hW hRight hAcyclic givenI givenK) Z hZ

/-- The complete K replacement unit remains the original actual left-factor function. -/
def fibrantReplacementUnit (Z : C) (hZ : IsTerminal Z) :
    𝟭 C ⟶ fibrantReplacement I K W hW hRight hAcyclic givenI givenK Z hZ :=
  GivenFactorizationReplacements.terminalUnit
    (fibrantFactorizationData I K W hW hRight hAcyclic givenI givenK) Z hZ

/-- The entire Q functor is the original given I middle functor on the same initial arrows. -/
theorem cofibrantReplacement_original (Z : C) (hZ : IsInitial Z) :
    cofibrantReplacement I K W hW hRight hAcyclic givenI givenK Z hZ =
      GivenFactorizationReplacements.initialArrows Z hZ ⋙ givenI.Z := rfl

/-- The entire R functor is the original given K middle functor on the same terminal arrows. -/
theorem fibrantReplacement_original (Z : C) (hZ : IsTerminal Z) :
    fibrantReplacement I K W hW hRight hAcyclic givenI givenK Z hZ =
      GivenFactorizationReplacements.terminalArrows Z hZ ⋙ givenK.Z := rfl

/-- Every Q map retains the complete original I square action. -/
theorem cofibrantReplacement_map (Z : C) (hZ : IsInitial Z) {X Y : C} (f : X ⟶ Y) :
    (cofibrantReplacement I K W hW hRight hAcyclic givenI givenK Z hZ).map f =
      givenI.Z.map ((GivenFactorizationReplacements.initialArrows Z hZ).map f) := rfl

/-- Every R map retains the complete original K square action. -/
theorem fibrantReplacement_map (Z : C) (hZ : IsTerminal Z) {X Y : C} (f : X ⟶ Y) :
    (fibrantReplacement I K W hW hRight hAcyclic givenI givenK Z hZ).map f =
      givenK.Z.map ((GivenFactorizationReplacements.terminalArrows Z hZ).map f) := rfl

/-- Each Q projection is the full original I right factor at that same initial arrow. -/
theorem cofibrantReplacementProjection_original (Z : C) (hZ : IsInitial Z) (X : C) :
    (cofibrantReplacementProjection I K W hW hRight hAcyclic givenI givenK Z hZ).app X =
      givenI.p.app (Arrow.mk (hZ.to X)) := rfl

/-- Each R unit is the full original K left factor at that same terminal arrow. -/
theorem fibrantReplacementUnit_original (Z : C) (hZ : IsTerminal Z) (X : C) :
    (fibrantReplacementUnit I K W hW hRight hAcyclic givenI givenK Z hZ).app X =
      givenK.i.app (Arrow.mk (hZ.from X)) := rfl

/-- Every chosen Q object is cofibrant in the newly constructed dictionary. -/
theorem cofibrantReplacement_isCofibrant (Z : C) (hZ : IsInitial Z) (X : C) :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    IsCofibrant ((cofibrantReplacement I K W hW hRight hAcyclic givenI givenK Z hZ).obj X) :=
  GivenFactorizationReplacements.initialReplacement_isCofibrant
    (modelCategory I K W hW hRight hAcyclic givenI givenK)
    (cofibrantFactorizationData I K W hW hRight hAcyclic givenI givenK) Z hZ X

/-- Every chosen R object is fibrant in the same constructed dictionary. -/
theorem fibrantReplacement_isFibrant (Z : C) (hZ : IsTerminal Z) (X : C) :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    IsFibrant ((fibrantReplacement I K W hW hRight hAcyclic givenI givenK Z hZ).obj X) :=
  GivenFactorizationReplacements.terminalReplacement_isFibrant
    (modelCategory I K W hW hRight hAcyclic givenI givenK)
    (fibrantFactorizationData I K W hW hRight hAcyclic givenI givenK) Z hZ X

/-- The entire original I projection is weak in the constructed candidate weak class. -/
theorem cofibrantReplacementProjection_weak (Z : C) (hZ : IsInitial Z) (X : C) :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    WeakEquivalence
      ((cofibrantReplacementProjection I K W hW hRight hAcyclic givenI givenK Z hZ).app X) :=
  GivenFactorizationReplacements.initialProjection_weak
    (modelCategory I K W hW hRight hAcyclic givenI givenK)
    (cofibrantFactorizationData I K W hW hRight hAcyclic givenI givenK) Z hZ X

/-- The entire original K unit is weak for every source in the constructed model. -/
theorem fibrantReplacementUnit_weak (Z : C) (hZ : IsTerminal Z) (X : C) :
    let : ModelCategory C := modelCategory I K W hW hRight hAcyclic givenI givenK
    WeakEquivalence
      ((fibrantReplacementUnit I K W hW hRight hAcyclic givenI givenK Z hZ).app X) :=
  GivenFactorizationReplacements.terminalUnit_weak
    (modelCategory I K W hW hRight hAcyclic givenI givenK)
    (fibrantFactorizationData I K W hW hRight hAcyclic givenI givenK) Z hZ X

/-- The given Q/R values retain their complete projection/unit naturality square. -/
theorem cofibrantReplacementProjection_naturality (Z : C) (hZ : IsInitial Z)
    {X Y : C} (f : X ⟶ Y) :
    (cofibrantReplacement I K W hW hRight hAcyclic givenI givenK Z hZ).map f ≫
        (cofibrantReplacementProjection I K W hW hRight hAcyclic givenI givenK Z hZ).app Y =
      (cofibrantReplacementProjection I K W hW hRight hAcyclic givenI givenK Z hZ).app X ≫ f :=
  (cofibrantReplacementProjection I K W hW hRight hAcyclic givenI givenK Z hZ).naturality f

/-- The full original K unit is natural on every actual source map. -/
theorem fibrantReplacementUnit_naturality (Z : C) (hZ : IsTerminal Z)
    {X Y : C} (f : X ⟶ Y) :
    f ≫ (fibrantReplacementUnit I K W hW hRight hAcyclic givenI givenK Z hZ).app Y =
      (fibrantReplacementUnit I K W hW hRight hAcyclic givenI givenK Z hZ).app X ≫
        (fibrantReplacement I K W hW hRight hAcyclic givenI givenK Z hZ).map f :=
  (fibrantReplacementUnit I K W hW hRight hAcyclic givenI givenK Z hZ).naturality f

/-- The actual identity adjunction from an existing level model to the constructed model. -/
def levelToConstructedAdjunction (level : ModelCategory C) :
    ExplicitModelIdentity.comparison level
        (modelCategory I K W hW hRight hAcyclic givenI givenK) ⊣
      ExplicitModelIdentity.comparison
        (modelCategory I K W hW hRight hAcyclic givenI givenK) level :=
  ExplicitModelIdentity.identityAdjunction level
    (modelCategory I K W hW hRight hAcyclic givenI givenK)

/-- Actual cofibration equality and weak inclusion prove the level-to-constructed Quillen pair. -/
theorem levelToConstructedAdjunction_isQuillen (level : ModelCategory C)
    (hCof : level.categoryWithCofibrations.cofibrations = I.rlp.llp)
    (hWeak : level.categoryWithWeakEquivalences.weakEquivalences ≤ W) :
    (levelToConstructedAdjunction I K W hW hRight hAcyclic
      givenI givenK level).IsQuillenAdjunction :=
  ExplicitModelIdentity.identityAdjunction_isQuillen level
    (modelCategory I K W hW hRight hAcyclic givenI givenK) hCof hWeak

end Model

end HomotopicalAlgebra.OriginalGeneratedModel
