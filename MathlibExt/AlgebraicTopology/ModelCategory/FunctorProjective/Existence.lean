/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Existence
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.Factorization

/-!
# The original projective model from a compatible base witness

Select only the actual base cardinal, bottom and generation datum. The
original index, fixed-data projective model, free families and both
factorization values are retained. No presentability or diagram model
hypothesis enters this constructor.

The conventional uniform relative-smallness conversion is separate.
Another legitimate base datum is compared by its five prescribed classes,
not by identifying its cardinal, generating arrows or selected factors.
-/

set_option autoImplicit false
noncomputable section
universe w uD vD uM vM
open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.FunctorProjective.Selected

variable {D : Type uD} [Category.{vD} D] {M : Type uM} [Category.{vM} M]
  [ModelCategory M] [HasCompatibleCofibrantGeneration.{w} M]
  [Small.{w} D] [LocallySmall.{w} D]

/-- The cardinal is the actual selected base witness, independent of the index universes. -/
abbrev cardinal : Cardinal.{w} := HasCompatibleCofibrantGeneration.cardinal (M := M)

/-- The same selected base cardinal retains its regularity proof. -/
theorem cardinal_regular : Fact (cardinal (M := M)).IsRegular :=
  HasCompatibleCofibrantGeneration.cardinal_regular

/-- Retain the actual selected ordinal bottom. -/
@[instance_reducible]
def orderBot : OrderBot (cardinal (M := M)).ord.ToType :=
  HasCompatibleCofibrantGeneration.orderBot

/-- The complete selected base datum belongs to the same cardinal and bottom. -/
def baseData :
    letI : Fact (cardinal (M := M)).IsRegular := cardinal_regular
    letI : OrderBot (cardinal (M := M)).ord.ToType := orderBot
    CofibrantGenerationData M (cardinal (M := M)) :=
  HasCompatibleCofibrantGeneration.data

/-- The selected model is the existing fixed-data construction on the original index. -/
@[instance_reducible]
def modelCategory : ModelCategory (D ⥤ M) := by
  letI : Fact (cardinal (M := M)).IsRegular := cardinal_regular
  letI : OrderBot (cardinal (M := M)).ord.ToType := orderBot
  exact FunctorProjective.modelCategory (J := D) (baseData (M := M))

/-- Constructor compatibility uses this exact selected datum, without another choice. -/
theorem modelCategory_eq_fixed :
    letI : Fact (cardinal (M := M)).IsRegular := cardinal_regular
    letI : OrderBot (cardinal (M := M)).ord.ToType := orderBot
    modelCategory (D := D) (M := M) =
      FunctorProjective.modelCategory (J := D) (baseData (M := M)) := rfl

section SameWitness

/-- The local regularity dictionary is the actual selected base proof. -/
local instance selectedCardinalRegular : Fact (cardinal (M := M)).IsRegular := cardinal_regular
/-- The local ordinal bottom is the actual selected base bottom. -/
local instance selectedOrdinalBottom : OrderBot (cardinal (M := M)).ord.ToType := orderBot
/-- The local diagram model is precisely the selected fixed-data constructor. -/
local instance selectedDiagramModel : ModelCategory (D ⥤ M) := modelCategory

/-- Public diagram generation data uses the original selected cardinal and fixed-data getter. -/
def generationData : CofibrantGenerationData (D ⥤ M) (cardinal (M := M)) :=
  FunctorProjective.generationData (D := D) (baseData (M := M))

/-- The entire returned record is the same fixed-data generation record. -/
theorem generationData_eq_fixed :
    generationData (D := D) (M := M) =
      FunctorProjective.generationData (D := D) (baseData (M := M)) := rfl

/-- The I family consists of the genuine free images at all original index objects. -/
theorem generationData_I :
    (generationData (D := D) (M := M)).I =
      FunctorProjective.freeGenerators (D := D) (baseData (M := M)) (baseData (M := M)).I := rfl

/-- The J family likewise retains all original index objects and actual base arrows. -/
theorem generationData_J :
    (generationData (D := D) (M := M)).J =
      FunctorProjective.freeGenerators (D := D) (baseData (M := M)) (baseData (M := M)).J := rfl

/-- All six I eligibility fields are the original same-cardinal free-diagram proof. -/
theorem generationData_I_eligible :
    (generationData (D := D) (M := M)).I.IsCardinalForSmallObjectArgument (cardinal (M := M)) :=
  (generationData (D := D) (M := M)).I_smallObject

/-- All six J eligibility fields retain that same selected cardinal. -/
theorem generationData_J_eligible :
    (generationData (D := D) (M := M)).J.IsCardinalForSmallObjectArgument (cardinal (M := M)) :=
  (generationData (D := D) (M := M)).J_smallObject

/-- Every original free I-arrow belongs to the actual returned family. -/
theorem freeI_mem (x : D) {A B : M} (f : A ⟶ B) (hf : (baseData (M := M)).I f) :
    (generationData (D := D) (M := M)).I
      ((FunctorProjective.freeFunctor (baseData (M := M)) x).map f) :=
  FunctorProjective.freeGenerator_mem (baseData (M := M)) (baseData (M := M)).I x f hf

/-- Every original free J-arrow belongs to the actual returned family. -/
theorem freeJ_mem (x : D) {A B : M} (f : A ⟶ B) (hf : (baseData (M := M)).J f) :
    (generationData (D := D) (M := M)).J
      ((FunctorProjective.freeFunctor (baseData (M := M)) x).map f) :=
  FunctorProjective.freeGenerator_mem (baseData (M := M)) (baseData (M := M)).J x f hf

/-- The selected model has exactly the original pointwise weak equivalences. -/
theorem weakEquivalences_eq :
    weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D :=
  FunctorProjective.weakEquivalences_eq (baseData (M := M))

/-- Its fibrations are precisely the original pointwise base fibrations. -/
theorem fibrations_eq : fibrations (D ⥤ M) = (fibrations M).functorCategory D :=
  FunctorProjective.fibrations_eq (baseData (M := M))

/-- Its trivial fibrations retain the original pointwise intersection. -/
theorem trivialFibrations_eq :
    trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D :=
  FunctorProjective.trivialFibrations_eq (baseData (M := M))

/-- Its cofibrations are the left lifting class of the original pointwise trivial fibrations. -/
theorem cofibrations_eq :
    cofibrations (D ⥤ M) = ((trivialFibrations M).functorCategory D).llp :=
  FunctorProjective.cofibrations_eq_objectwise_llp (baseData (M := M))

/-- Its trivial cofibrations are the left lifting class of original pointwise fibrations. -/
theorem trivialCofibrations_eq :
    trivialCofibrations (D ⥤ M) = ((fibrations M).functorCategory D).llp :=
  FunctorProjective.trivialCofibrations_eq_objectwise_llp (baseData (M := M))

/-- All five class equations belong to this same returned model. -/
theorem five_classes :
    weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D ∧
      fibrations (D ⥤ M) = (fibrations M).functorCategory D ∧
      trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D ∧
      cofibrations (D ⥤ M) = ((trivialFibrations M).functorCategory D).llp ∧
      trivialCofibrations (D ⥤ M) = ((fibrations M).functorCategory D).llp :=
  ⟨weakEquivalences_eq, fibrations_eq, trivialFibrations_eq,
    cofibrations_eq, trivialCofibrations_eq⟩

/-- Every selected projective cofibration is an original objectwise cofibration. -/
theorem cofibrations_le_objectwise :
    cofibrations (D ⥤ M) ≤ (cofibrations M).functorCategory D :=
  FunctorProjective.cofibrations_le_objectwise (baseData (M := M))

/-- Every selected trivial cofibration is an original objectwise trivial cofibration. -/
theorem trivialCofibrations_le_objectwise :
    trivialCofibrations (D ⥤ M) ≤ (trivialCofibrations M).functorCategory D :=
  FunctorProjective.trivialCofibrations_le_objectwise (baseData (M := M))

/-- The first actual factor value is the existing same-datum getter. -/
def cofibrantFactorizationData :
    FunctorialFactorizationData (cofibrations (D ⥤ M)) (trivialFibrations (D ⥤ M)) :=
  FunctorProjective.cofibrantFactorizationData (baseData (M := M))

/-- The second actual factor value is the existing getter at that same cardinal. -/
def fibrantFactorizationData :
    FunctorialFactorizationData (trivialCofibrations (D ⥤ M)) (fibrations (D ⥤ M)) :=
  FunctorProjective.fibrantFactorizationData (baseData (M := M))

/-- The whole first factor record agrees with the original same-witness record. -/
theorem cofibrantFactorizationData_eq_fixed :
    cofibrantFactorizationData (D := D) (M := M) =
      FunctorProjective.cofibrantFactorizationData (baseData (M := M)) := rfl

/-- The whole second factor record agrees with the original same-witness record. -/
theorem fibrantFactorizationData_eq_fixed :
    fibrantFactorizationData (D := D) (M := M) =
      FunctorProjective.fibrantFactorizationData (baseData (M := M)) := rfl

/-- The entire selected first middle functor is the original free-I SOA field. -/
theorem cofibrantFactorizationData_Z :
    letI : (FunctorProjective.freeGenerators (D := D) (baseData (M := M))
      (baseData (M := M)).I).IsCardinalForSmallObjectArgument (cardinal (M := M)) :=
        FunctorProjective.freeI_eligible (baseData (M := M))
    (cofibrantFactorizationData (D := D) (M := M)).Z =
      (SmallObject.functorialFactorizationData
        (FunctorProjective.freeGenerators (D := D) (baseData (M := M)) (baseData (M := M)).I)
        (cardinal (M := M))).Z := rfl

/-- The entire selected first left transformation is the original free-I SOA field. -/
theorem cofibrantFactorizationData_i :
    letI : (FunctorProjective.freeGenerators (D := D) (baseData (M := M))
      (baseData (M := M)).I).IsCardinalForSmallObjectArgument (cardinal (M := M)) :=
        FunctorProjective.freeI_eligible (baseData (M := M))
    (cofibrantFactorizationData (D := D) (M := M)).i =
      (SmallObject.functorialFactorizationData
        (FunctorProjective.freeGenerators (D := D) (baseData (M := M)) (baseData (M := M)).I)
        (cardinal (M := M))).i := rfl

/-- The entire selected first right transformation is the original free-I SOA field. -/
theorem cofibrantFactorizationData_p :
    letI : (FunctorProjective.freeGenerators (D := D) (baseData (M := M))
      (baseData (M := M)).I).IsCardinalForSmallObjectArgument (cardinal (M := M)) :=
        FunctorProjective.freeI_eligible (baseData (M := M))
    (cofibrantFactorizationData (D := D) (M := M)).p =
      (SmallObject.functorialFactorizationData
        (FunctorProjective.freeGenerators (D := D) (baseData (M := M)) (baseData (M := M)).I)
        (cardinal (M := M))).p := rfl




/-- Each original component retains the selected first left naturality square. -/
theorem cofibrantFactorizationData_i_naturality_app {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) (x : D) :
    φ.left.app x ≫ ((cofibrantFactorizationData (D := D) (M := M)).i.app g).app x =
      ((cofibrantFactorizationData (D := D) (M := M)).i.app f).app x ≫
        ((cofibrantFactorizationData (D := D) (M := M)).Z.map φ).app x :=
  NatTrans.congr_app ((cofibrantFactorizationData (D := D) (M := M)).i.naturality φ) x

/-- Each original component retains the selected first right naturality square. -/
theorem cofibrantFactorizationData_p_naturality_app {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) (x : D) :
    ((cofibrantFactorizationData (D := D) (M := M)).Z.map φ).app x ≫
      ((cofibrantFactorizationData (D := D) (M := M)).p.app g).app x =
        ((cofibrantFactorizationData (D := D) (M := M)).p.app f).app x ≫ φ.right.app x :=
  NatTrans.congr_app ((cofibrantFactorizationData (D := D) (M := M)).p.naturality φ) x



/-- The entire selected second middle functor is the original free-J SOA field. -/
theorem fibrantFactorizationData_Z :
    letI : (FunctorProjective.freeGenerators (D := D) (baseData (M := M))
      (baseData (M := M)).J).IsCardinalForSmallObjectArgument (cardinal (M := M)) :=
        FunctorProjective.freeJ_eligible (baseData (M := M))
    (fibrantFactorizationData (D := D) (M := M)).Z =
      (SmallObject.functorialFactorizationData
        (FunctorProjective.freeGenerators (D := D) (baseData (M := M)) (baseData (M := M)).J)
        (cardinal (M := M))).Z := rfl

/-- The entire selected second left transformation is the original free-J SOA field. -/
theorem fibrantFactorizationData_i :
    letI : (FunctorProjective.freeGenerators (D := D) (baseData (M := M))
      (baseData (M := M)).J).IsCardinalForSmallObjectArgument (cardinal (M := M)) :=
        FunctorProjective.freeJ_eligible (baseData (M := M))
    (fibrantFactorizationData (D := D) (M := M)).i =
      (SmallObject.functorialFactorizationData
        (FunctorProjective.freeGenerators (D := D) (baseData (M := M)) (baseData (M := M)).J)
        (cardinal (M := M))).i := rfl

/-- The entire selected second right transformation is the original free-J SOA field. -/
theorem fibrantFactorizationData_p :
    letI : (FunctorProjective.freeGenerators (D := D) (baseData (M := M))
      (baseData (M := M)).J).IsCardinalForSmallObjectArgument (cardinal (M := M)) :=
        FunctorProjective.freeJ_eligible (baseData (M := M))
    (fibrantFactorizationData (D := D) (M := M)).p =
      (SmallObject.functorialFactorizationData
        (FunctorProjective.freeGenerators (D := D) (baseData (M := M)) (baseData (M := M)).J)
        (cardinal (M := M))).p := rfl




/-- Each original component retains the selected second left naturality square. -/
theorem fibrantFactorizationData_i_naturality_app {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) (x : D) :
    φ.left.app x ≫ ((fibrantFactorizationData (D := D) (M := M)).i.app g).app x =
      ((fibrantFactorizationData (D := D) (M := M)).i.app f).app x ≫
        ((fibrantFactorizationData (D := D) (M := M)).Z.map φ).app x :=
  NatTrans.congr_app ((fibrantFactorizationData (D := D) (M := M)).i.naturality φ) x

/-- Each original component retains the selected second right naturality square. -/
theorem fibrantFactorizationData_p_naturality_app {f g : Arrow (D ⥤ M)} (φ : f ⟶ g) (x : D) :
    ((fibrantFactorizationData (D := D) (M := M)).Z.map φ).app x ≫
      ((fibrantFactorizationData (D := D) (M := M)).p.app g).app x =
        ((fibrantFactorizationData (D := D) (M := M)).p.app f).app x ≫ φ.right.app x :=
  NatTrans.congr_app ((fibrantFactorizationData (D := D) (M := M)).p.naturality φ) x



/-- Original componentwise factor equations hold for the first selected factor. -/
theorem cofibrantFactorizationData_fac_app (f : Arrow (D ⥤ M)) (x : D) :
    ((cofibrantFactorizationData (D := D) (M := M)).i.app f).app x ≫
      ((cofibrantFactorizationData (D := D) (M := M)).p.app f).app x = f.hom.app x :=
  NatTrans.congr_app ((cofibrantFactorizationData (D := D) (M := M)).fac_app) x

/-- Original componentwise factor equations hold for the second selected factor. -/
theorem fibrantFactorizationData_fac_app (f : Arrow (D ⥤ M)) (x : D) :
    ((fibrantFactorizationData (D := D) (M := M)).i.app f).app x ≫
      ((fibrantFactorizationData (D := D) (M := M)).p.app f).app x = f.hom.app x :=
  NatTrans.congr_app ((fibrantFactorizationData (D := D) (M := M)).fac_app) x




end SameWitness

section CompareClasses

variable {μ : Cardinal.{w}} [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
  (e : CofibrantGenerationData M μ)

/-- A second legitimate datum has the same prescribed weak, fibrant and cofibrant classes. -/
theorem prescribed_classes_eq_fixed :
    let m := modelCategory (D := D) (M := M)
    let n := FunctorProjective.modelCategory (J := D) e
    m.categoryWithWeakEquivalences.weakEquivalences =
        n.categoryWithWeakEquivalences.weakEquivalences ∧
      m.categoryWithFibrations.fibrations = n.categoryWithFibrations.fibrations ∧
      m.categoryWithCofibrations.cofibrations = n.categoryWithCofibrations.cofibrations ∧
      m.categoryWithFibrations.fibrations ⊓ m.categoryWithWeakEquivalences.weakEquivalences =
        n.categoryWithFibrations.fibrations ⊓ n.categoryWithWeakEquivalences.weakEquivalences ∧
      m.categoryWithCofibrations.cofibrations ⊓ m.categoryWithWeakEquivalences.weakEquivalences =
        n.categoryWithCofibrations.cofibrations ⊓
          n.categoryWithWeakEquivalences.weakEquivalences := by
  let m := modelCategory (D := D) (M := M)
  let n := FunctorProjective.modelCategory (J := D) e
  have hw : m.categoryWithWeakEquivalences.weakEquivalences =
      (weakEquivalences M).functorCategory D := weakEquivalences_eq
  have hw' : n.categoryWithWeakEquivalences.weakEquivalences =
      (weakEquivalences M).functorCategory D := FunctorProjective.weakEquivalences_eq e
  have hf : m.categoryWithFibrations.fibrations =
      (fibrations M).functorCategory D := fibrations_eq
  have hf' : n.categoryWithFibrations.fibrations =
      (fibrations M).functorCategory D := FunctorProjective.fibrations_eq e
  have hc : m.categoryWithCofibrations.cofibrations =
      ((trivialFibrations M).functorCategory D).llp := cofibrations_eq
  have hc' : n.categoryWithCofibrations.cofibrations =
      ((trivialFibrations M).functorCategory D).llp :=
    FunctorProjective.cofibrations_eq_objectwise_llp e
  exact ⟨hw.trans hw'.symm, hf.trans hf'.symm, hc.trans hc'.symm,
    congrArg₂ (fun a b : MorphismProperty (D ⥤ M) => a ⊓ b)
      (hf.trans hf'.symm) (hw.trans hw'.symm),
    congrArg₂ (fun a b : MorphismProperty (D ⥤ M) => a ⊓ b)
      (hc.trans hc'.symm) (hw.trans hw'.symm)⟩

end CompareClasses

end HomotopicalAlgebra.FunctorProjective.Selected
