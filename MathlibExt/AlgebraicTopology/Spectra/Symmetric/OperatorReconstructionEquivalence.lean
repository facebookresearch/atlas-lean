/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorFromRepresentationMaps
public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorReconstructionRecovery

/-!
# The original ordinary sphere-module and genuine operator equivalence

Both functors retain every original map. The unit and counit are the
complete original identity-component transformations, with their full
coefficient and coend squares proved by the reconstruction laws.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [MonoidalClosed V] {T : V}

/-- The complete original unit transformation on the ordinary sphere-module diagram. -/
def reconstructionUnitMap (d : SphereData T) : d ⟶ fromRepresentation (toRepresentation d) where
  map :=
    { app n := 𝟙 (d.diagram.obj n)
      naturality n k f := by
        let r : d.diagram.obj n ⟶ d.diagram.obj k :=
          (fromRepresentation (toRepresentation d)).diagram.map f
        have h : r = d.diagram.map f := ordinaryDiagram_toRepresentation_map d f
        change d.diagram.map f ≫ (𝟙 (d.diagram.obj k)) = (𝟙 (d.diagram.obj n)) ≫ r
        rw [Category.comp_id, Category.id_comp, h] }
  comm a n := by
    let P := (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a
    let z : P ⊗ d.diagram.obj n ⟶ d.diagram.obj (a ⊗ n) :=
      coefficient (fromRepresentation (toRepresentation d)) a n
    have h : z = coefficient d a n := from_to_coefficient d a n
    change coefficient d a n ≫ (𝟙 (d.diagram.obj (a ⊗ n))) =
      (P ◁ (𝟙 (d.diagram.obj n))) ≫ z
    rw [Category.comp_id, whiskerLeft_id, Category.id_comp, h]

/-- The complete inverse original unit transformation on the ordinary sphere-module diagram. -/
def reconstructionUnitInv (d : SphereData T) : fromRepresentation (toRepresentation d) ⟶ d where
  map :=
    { app n := 𝟙 (d.diagram.obj n)
      naturality n k f := by
        let r : d.diagram.obj n ⟶ d.diagram.obj k :=
          (fromRepresentation (toRepresentation d)).diagram.map f
        have h : r = d.diagram.map f := ordinaryDiagram_toRepresentation_map d f
        change r ≫ (𝟙 (d.diagram.obj k)) = (𝟙 (d.diagram.obj n)) ≫ d.diagram.map f
        rw [Category.comp_id, Category.id_comp, h] }
  comm a n := by
    let P := (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a
    let z : P ⊗ d.diagram.obj n ⟶ d.diagram.obj (a ⊗ n) :=
      coefficient (fromRepresentation (toRepresentation d)) a n
    have h : z = coefficient d a n := from_to_coefficient d a n
    change z ≫ (𝟙 (d.diagram.obj (a ⊗ n))) =
      (P ◁ (𝟙 (d.diagram.obj n))) ≫ coefficient d a n
    rw [Category.comp_id, whiskerLeft_id, Category.id_comp, h]

/-- Both original ordinary identity-component maps give the complete reconstruction unit isomorphism. -/
def reconstructionUnitIsoApp (d : SphereData T) : d ≅ fromRepresentation (toRepresentation d) where
  hom := reconstructionUnitMap d
  inv := reconstructionUnitInv d
  hom_inv_id := by
    apply DayFunctor.ExternalModule.Data.Hom.ext
    apply NatTrans.ext
    funext n
    exact Category.id_comp _
  inv_hom_id := by
    apply DayFunctor.ExternalModule.Data.Hom.ext
    apply NatTrans.ext
    funext n
    exact Category.id_comp _

/-- The entire original enriched identity-component map is the reconstruction counit. -/
def reconstructionCounitMap (X : Representation T) : toRepresentation (fromRepresentation X) ⟶ X := by
  letI : EnrichedCategory V I := enrichedCategory T
  exact
    { app n := 𝟙 (representationObject X n)
      comm n k := by
        let z : representationObject X n ⊗ Hom T n k ⟶ representationObject X k :=
          operatorAction (fromRepresentation X) n k
        change (𝟙 (representationObject X n) ▷ Hom T n k) ≫ representationAction X n k =
          z ≫ (𝟙 (representationObject X k))
        rw [id_whiskerRight, Category.id_comp, Category.comp_id]
        exact (to_from_action X n k).symm }

/-- The entire inverse original enriched identity-component map is the inverse reconstruction counit. -/
def reconstructionCounitInv (X : Representation T) : X ⟶ toRepresentation (fromRepresentation X) := by
  letI : EnrichedCategory V I := enrichedCategory T
  exact
    { app n := 𝟙 (representationObject X n)
      comm n k := by
        let z : representationObject X n ⊗ Hom T n k ⟶ representationObject X k :=
          operatorAction (fromRepresentation X) n k
        change (𝟙 (representationObject X n) ▷ Hom T n k) ≫ z =
          representationAction X n k ≫ (𝟙 (representationObject X k))
        rw [id_whiskerRight, Category.id_comp, Category.comp_id]
        exact to_from_action X n k }

/-- Both original whole enriched identity-component maps give the complete counit isomorphism. -/
def reconstructionCounitIsoApp (X : Representation T) : toRepresentation (fromRepresentation X) ≅ X where
  hom := reconstructionCounitMap X
  inv := reconstructionCounitInv X
  hom_inv_id := by
    let _ : EnrichedCategory V I := enrichedCategory T
    apply WholeRepresentation.hom_ext
    intro n
    change (𝟙 (representationObject X n)) ≫ (𝟙 (representationObject X n)) = 𝟙 (representationObject X n)
    exact Category.id_comp _
  inv_hom_id := by
    let _ : EnrichedCategory V I := enrichedCategory T
    apply WholeRepresentation.hom_ext
    intro n
    change (𝟙 (representationObject X n)) ≫ (𝟙 (representationObject X n)) = 𝟙 (representationObject X n)
    exact Category.id_comp _

/-- The original unit maps are natural on all complete ordinary spectrum morphisms. -/
def reconstructionUnitIso (T : V) : 𝟭 (SphereData T) ≅ toRepresentations T ⋙ fromRepresentations T :=
  NatIso.ofComponents reconstructionUnitIsoApp (fun f => by
    apply DayFunctor.ExternalModule.Data.Hom.ext
    apply NatTrans.ext
    funext n
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The original counit maps are natural on all complete enriched operator transformations. -/
def reconstructionCounitIso (T : V) : fromRepresentations T ⋙ toRepresentations T ≅ 𝟭 (Representation T) :=
  NatIso.ofComponents reconstructionCounitIsoApp (fun {X Y} f => by
    let _ : EnrichedCategory V I := enrichedCategory T
    apply WholeRepresentation.hom_ext
    intro n
    change representationMapComponent f n ≫ (𝟙 (representationObject Y n)) =
      (𝟙 (representationObject X n)) ≫ representationMapComponent f n
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The complete original ordinary sphere-module and genuine enriched operator equivalence. -/
def externalRepresentationEquivalence (T : V) : SphereData T ≌ Representation T where
  functor := toRepresentations T
  inverse := fromRepresentations T
  unitIso := reconstructionUnitIso T
  counitIso := reconstructionCounitIso T
  functor_unitIso_comp d := by
    let _ : EnrichedCategory V I := enrichedCategory T
    apply WholeRepresentation.hom_ext
    intro n
    change (𝟙 (d.diagram.obj n)) ≫ (𝟙 (d.diagram.obj n)) = 𝟙 (d.diagram.obj n)
    exact Category.id_comp _

/-- Every whole original ordinary unit component is the original identity map. -/
theorem reconstructionUnitMap_component (d : SphereData T) (n : I) :
    (reconstructionUnitMap d).map.app n = 𝟙 (d.diagram.obj n) := rfl

/-- Every whole inverse original ordinary unit component is the original identity map. -/
theorem reconstructionUnitInv_component (d : SphereData T) (n : I) :
    (reconstructionUnitInv d).map.app n = 𝟙 (d.diagram.obj n) := rfl

/-- Every whole original enriched counit component is the original identity map. -/
theorem reconstructionCounitMap_component (X : Representation T) (n : I) :
    representationMapComponent (reconstructionCounitMap X) n = 𝟙 (representationObject X n) := rfl

/-- Every whole inverse original enriched counit component is the original identity map. -/
theorem reconstructionCounitInv_component (X : Representation T) (n : I) :
    representationMapComponent (reconstructionCounitInv X) n = 𝟙 (representationObject X n) := rfl

end CategoryTheory.Spectra.Symmetric.OperatorCoend
