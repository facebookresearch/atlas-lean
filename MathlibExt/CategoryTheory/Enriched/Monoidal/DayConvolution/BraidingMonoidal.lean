/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingHexagonComponents

/-!
# The actual braiding of the unchanged continuous Day monoidal category

The coend braid is an isomorphism on the existing tensor. Its entire
component, input naturality and symmetry are the original proved coend
maps. The Day monoidal category is constructed from the given colimits.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.BraidingMonoidal

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)

/-- The original balanced coend braid on the unchanged, constructed Day tensor. -/
def braiding (F G : EnrichedFunctorCat V I) :
    letI := ColimitMonoidal.monoidalCategory d
    F ⊗ G ≅ G ⊗ F := by
  letI := ColimitMonoidal.monoidalCategory d
  exact BraidingFunctor.functorIso d b F.toEnrichedFunctor G.toEnrichedFunctor

/-- Every complete forward component is the original full coend braid. -/
theorem braiding_hom_component (F G : EnrichedFunctorCat V I) (k : I) :
    letI := ColimitMonoidal.monoidalCategory d
    EnrichedFunctorCat.component (braiding d b F G).hom k =
      BraidingComponents.component d b F.toEnrichedFunctor G.toEnrichedFunctor k :=
  BraidingFunctor.functorIso_hom_component d b F.toEnrichedFunctor G.toEnrichedFunctor k

/-- Every complete inverse component is the original coend braid with reversed inputs. -/
theorem braiding_inv_component (F G : EnrichedFunctorCat V I) (k : I) :
    letI := ColimitMonoidal.monoidalCategory d
    EnrichedFunctorCat.component (braiding d b F G).inv k =
      BraidingComponents.component d b G.toEnrichedFunctor F.toEnrichedFunctor k :=
  BraidingFunctor.functorIso_inv_component d b F.toEnrichedFunctor G.toEnrichedFunctor k

/-- The inverse is exactly the same original coend braid with reversed inputs. -/
theorem braiding_inv_eq_reverse (F G : EnrichedFunctorCat V I) :
    letI := ColimitMonoidal.monoidalCategory d
    (braiding d b F G).inv = (braiding d b G F).hom := by
  let := ColimitMonoidal.monoidalCategory d
  apply EnrichedFunctorCat.hom_ext
  intro k
  exact (braiding_inv_component d b F G k).trans (braiding_hom_component d b G F k).symm

/-- Both actual Day braids compose to the whole identity of the unchanged original tensor. -/
theorem braiding_symmetry (F G : EnrichedFunctorCat V I) :
    letI := ColimitMonoidal.monoidalCategory d
    (braiding d b F G).hom ≫ (braiding d b G F).hom = 𝟙 (F ⊗ G) := by
  let := ColimitMonoidal.monoidalCategory d
  exact (congrArg (fun t => (braiding d b F G).hom ≫ t)
    (braiding_inv_eq_reverse d b F G).symm).trans (braiding d b F G).hom_inv_id

/-- All genuine input maps commute with the original braiding of the unchanged Day tensor. -/
theorem braiding_naturality {F F' G G' : EnrichedFunctorCat V I}
    (f : F ⟶ F') (g : G ⟶ G') :
    letI := ColimitMonoidal.monoidalCategory d
    (f ⊗ₘ g) ≫ (braiding d b F' G').hom =
      (braiding d b F G).hom ≫ (g ⊗ₘ f) := by
  let := ColimitMonoidal.monoidalCategory d
  rw [ColimitMonoidal.tensorHom_eq, ColimitMonoidal.tensorHom_eq]
  exact BraidingTensor.naturality d b f g

/-- The actual Day braid and constructed associator satisfy the forward hexagon. -/
theorem hexagon_forward (F G H : EnrichedFunctorCat V I) :
    letI := ColimitMonoidal.monoidalCategory d
    (α_ F G H).hom ≫ (braiding d b F (G ⊗ H)).hom ≫ (α_ G H F).hom =
      ((braiding d b F G).hom ▷ H) ≫ (α_ G F H).hom ≫
        (G ◁ (braiding d b F H).hom) := by
  let := ColimitMonoidal.monoidalCategory d
  apply EnrichedFunctorCat.hom_ext
  intro k
  rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp,
    EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp]
  have hp : EnrichedFunctorCat.component (α_ F G H).hom k =
      (AssociatorConstruction.componentIso d F.toEnrichedFunctor G.toEnrichedFunctor
        H.toEnrichedFunctor k).hom :=
    AssociatorConstruction.functorIso_hom_component d F.toEnrichedFunctor G.toEnrichedFunctor
      H.toEnrichedFunctor k
  have hq : EnrichedFunctorCat.component (braiding d b F (G ⊗ H)).hom k =
      BraidingComponents.component d b F.toEnrichedFunctor
        (Output.functor d.tensorEnrichedFunctor G.toEnrichedFunctor H.toEnrichedFunctor) k :=
    braiding_hom_component d b F (G ⊗ H) k
  have hr : EnrichedFunctorCat.component (α_ G H F).hom k =
      (AssociatorConstruction.componentIso d G.toEnrichedFunctor H.toEnrichedFunctor
        F.toEnrichedFunctor k).hom :=
    AssociatorConstruction.functorIso_hom_component d G.toEnrichedFunctor H.toEnrichedFunctor
      F.toEnrichedFunctor k
  have hm : EnrichedFunctorCat.component ((braiding d b F G).hom ▷ H) k =
      Input.mapAt d.tensorEnrichedFunctor (BraidingFunctor.functorIso d b F.toEnrichedFunctor
        G.toEnrichedFunctor).hom (GradedNatTrans.unitId H.toEnrichedFunctor) k :=
    Input.natTrans_component d.tensorEnrichedFunctor (braiding d b F G).hom
      (GradedNatTrans.unitId H.toEnrichedFunctor) k
  have hn : EnrichedFunctorCat.component (α_ G F H).hom k =
      (AssociatorConstruction.componentIso d G.toEnrichedFunctor F.toEnrichedFunctor
        H.toEnrichedFunctor k).hom :=
    AssociatorConstruction.functorIso_hom_component d G.toEnrichedFunctor F.toEnrichedFunctor
      H.toEnrichedFunctor k
  have ho : EnrichedFunctorCat.component (G ◁ (braiding d b F H).hom) k =
      Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId G.toEnrichedFunctor)
        (BraidingFunctor.functorIso d b F.toEnrichedFunctor H.toEnrichedFunctor).hom k :=
    Input.natTrans_component d.tensorEnrichedFunctor (GradedNatTrans.unitId G.toEnrichedFunctor)
      (braiding d b F H).hom k
  rw [hp, hq, hr, hm, hn, ho]
  exact BraidingHexagonComponents.forward d b F.toEnrichedFunctor G.toEnrichedFunctor
    H.toEnrichedFunctor k

/-- The same whole forward hexagon as an equality of the original Day isomorphisms. -/
theorem hexagon_forward_iso (F G H : EnrichedFunctorCat V I) :
    letI := ColimitMonoidal.monoidalCategory d
    (α_ F G H) ≪≫ braiding d b F (G ⊗ H) ≪≫ (α_ G H F) =
      whiskerRightIso (braiding d b F G) H ≪≫ (α_ G F H) ≪≫
        whiskerLeftIso G (braiding d b F H) := by
  let := ColimitMonoidal.monoidalCategory d
  exact Iso.ext (hexagon_forward d b F G H)

/-- Symmetry and inversion of the proved forward hexagon give the whole reverse hexagon. -/
theorem hexagon_reverse (F G H : EnrichedFunctorCat V I) :
    letI := ColimitMonoidal.monoidalCategory d
    (α_ F G H).inv ≫ (braiding d b (F ⊗ G) H).hom ≫ (α_ H F G).inv =
      (F ◁ (braiding d b G H).hom) ≫ (α_ F H G).inv ≫
        ((braiding d b F H).hom ▷ G) := by
  let := ColimitMonoidal.monoidalCategory d
  have h := congrArg (fun e => e.inv) (hexagon_forward_iso d b H F G)
  simp only [Iso.trans_inv, whiskerLeftIso_inv, whiskerRightIso_inv] at h
  rw [braiding_inv_eq_reverse, braiding_inv_eq_reverse, braiding_inv_eq_reverse] at h
  simp only [Category.assoc] at h
  exact h

/-- The actual coend braid, full input naturality and both proved whole Day hexagons. -/
@[instance_reducible]
def braidedCategory :
    letI := ColimitMonoidal.monoidalCategory d
    BraidedCategory (EnrichedFunctorCat V I) := by
  letI := ColimitMonoidal.monoidalCategory d
  refine
    { braiding := braiding d b
      braiding_naturality_right := ?_
      braiding_naturality_left := ?_
      hexagon_forward := hexagon_forward d b
      hexagon_reverse := hexagon_reverse d b }
  · intro F G H f
    have h := braiding_naturality d b (𝟙 F) f
    simp only [id_tensorHom, tensorHom_id] at h
    exact h
  · intro F G f H
    have h := braiding_naturality d b f (𝟙 H)
    simp only [id_tensorHom, tensorHom_id] at h
    exact h

/-- The genuine original Day braiding is symmetric on the unchanged tensor and associator. -/
@[instance_reducible]
def symmetricCategory :
    letI := ColimitMonoidal.monoidalCategory d
    SymmetricCategory (EnrichedFunctorCat V I) := by
  letI := ColimitMonoidal.monoidalCategory d
  exact
    { toBraidedCategory := braidedCategory d b
      symmetry := braiding_symmetry d b }

end CategoryTheory.EnrichedDayKernel.BraidingMonoidal
