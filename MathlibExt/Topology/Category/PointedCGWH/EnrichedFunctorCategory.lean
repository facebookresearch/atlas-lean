/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.EnrichedFunctorMapping
public import MathlibExt.CategoryTheory.Enriched.GradedComposition

/-!
# The genuine native category of enriched diagrams

The original small weighted mapping ends are the Hom objects. Their identity
and composition are constructed from the actual positive graded projection
families, using the native symmetry already proved in NativeGradedHom.
Every original projection gives the actual target identity or composition.
Those full equations prove enrichment and its ordinary carrier compatibility.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace PointedCGWH.EnrichedFunctorMapping

attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits

set_option maxHeartbeats 200000 in
-- Normalize the entire closed identity endpoint before specializing native opaque data.
private theorem closed_e_id_comp (T : Type u) [Category.{v} T] [MonoidalCategory T]
    [MonoidalClosed T] (X Y : T) :
    (λ_ ((ihom X).obj Y)).inv ≫ eId T X ▷ (ihom X).obj Y ≫ eComp T X X Y =
      𝟙 ((ihom X).obj Y) :=
  e_id_comp T X Y

set_option maxHeartbeats 200000 in
-- Normalize the entire closed identity endpoint before specializing native opaque data.
private theorem closed_e_comp_id (T : Type u) [Category.{v} T] [MonoidalCategory T]
    [MonoidalClosed T] (X Y : T) :
    (ρ_ ((ihom X).obj Y)).inv ≫ (ihom X).obj Y ◁ eId T Y ≫ eComp T X Y Y =
      𝟙 ((ihom X).obj Y) :=
  e_comp_id T X Y

set_option maxHeartbeats 200000 in
-- Normalize the entire closed associativity endpoint before specializing native opaque data.
private theorem closed_e_assoc (T : Type u) [Category.{v} T] [MonoidalCategory T]
    [MonoidalClosed T] (W X Y Z : T) :
    (α_ ((ihom W).obj X) ((ihom X).obj Y) ((ihom Y).obj Z)).inv ≫
        eComp T W X Y ▷ (ihom Y).obj Z ≫ eComp T W Y Z =
      (ihom W).obj X ◁ eComp T X Y Z ≫ eComp T W X Z :=
  e_assoc T W X Y Z

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

set_option maxHeartbeats 200000 in
-- Preserve the original project budget for the actual native enriched identity.
/-- The native mapping identity is the original end lift of the actual diagram identity. -/
@[no_expose]
def mappingIdentity (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    𝟙_ PointedCGWH.{u, v} ⟶ mappingObject X X :=
  ofGrade X X (𝟙 X)

set_option maxHeartbeats 200000 in
-- Preserve the original project budget for the complete native identity projection.
private theorem mappingIdentity_π_proof (X : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (a : I) : mappingIdentity X ≫ π X X a = eId PointedCGWH.{u, v}
      (X.toEnrichedFunctor.obj a) := by
  unfold mappingIdentity
  rw [ofGrade_π]
  exact GradedNatTrans.unitId_app X.toEnrichedFunctor a

/-- Every original identity projection is the actual target enriched identity. -/
theorem mappingIdentity_π (X : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) :
    mappingIdentity X ≫ π X X a = eId PointedCGWH.{u, v} (X.toEnrichedFunctor.obj a) :=
  mappingIdentity_π_proof X a

set_option maxHeartbeats 200000 in
-- Preserve the original project budget for full native enriched composition.
/-- Native mapping composition is the original end lift of the full tensor-graded composition. -/
@[no_expose]
def mappingComposition (X Y Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    mappingObject X Y ⊗ mappingObject Y Z ⟶ mappingObject X Z :=
  ofGrade X Z
    (GradedNatTrans.regrade
      (Functor.OplaxMonoidal.δ (Center.ofBraided PointedCGWH.{u, v})
        (mappingObject X Y) (mappingObject Y Z))
      (GradedNatTrans.tensorComp
        (toGrade X Y (mappingObject X Y) (𝟙 (mappingObject X Y)))
        (toGrade Y Z (mappingObject Y Z) (𝟙 (mappingObject Y Z)))))

set_option maxHeartbeats 200000 in
-- Preserve the original project budget for the complete original composition projection.
set_option backward.isDefEq.respectTransparency false in
private theorem mappingComposition_π_proof (X Y Z : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (a : I) : mappingComposition X Y Z ≫ π X Z a =
      (π X Y a ⊗ₘ π Y Z a) ≫ eComp PointedCGWH.{u, v}
        (X.toEnrichedFunctor.obj a) (Y.toEnrichedFunctor.obj a) (Z.toEnrichedFunctor.obj a) := by
  unfold mappingComposition
  rw [ofGrade_π, GradedNatTrans.regrade_app, Center.ofBraided_δ_f, Category.id_comp,
    GradedNatTrans.tensorComp_app, toGrade_app, toGrade_app, Category.id_comp, Category.id_comp]

/-- Every original composition projection is the tensor of projections followed by actual eComp. -/
theorem mappingComposition_π (X Y Z : EnrichedFunctorCat PointedCGWH.{u, v} I) (a : I) :
    mappingComposition X Y Z ≫ π X Z a =
      (π X Y a ⊗ₘ π Y Z a) ≫ eComp PointedCGWH.{u, v}
        (X.toEnrichedFunctor.obj a) (Y.toEnrichedFunctor.obj a) (Z.toEnrichedFunctor.obj a) :=
  mappingComposition_π_proof X Y Z a

set_option maxHeartbeats 200000 in
-- Preserve the original project budget for both actual native coefficient inputs.
set_option backward.isDefEq.respectTransparency false in
/-- Mapping composition retains every pair of actual positive graded coefficients. -/
theorem mappingComposition_toGrade (X Y Z : EnrichedFunctorCat PointedCGWH.{u, v} I)
    {T U : PointedCGWH.{u, v}} (f : T ⟶ mappingObject X Y) (g : U ⟶ mappingObject Y Z) :
    toGrade X Z (T ⊗ U) ((f ⊗ₘ g) ≫ mappingComposition X Y Z) =
      GradedNatTrans.regrade
        (Functor.OplaxMonoidal.δ (Center.ofBraided PointedCGWH.{u, v}) T U)
        (GradedNatTrans.tensorComp (toGrade X Y T f) (toGrade Y Z U g)) := by
  apply GradedNatTrans.ext
  funext a
  rw [toGrade_app, Category.assoc, mappingComposition_π, GradedNatTrans.regrade_app,
    Center.ofBraided_δ_f, Category.id_comp, GradedNatTrans.tensorComp_app,
    toGrade_app, toGrade_app]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ eComp PointedCGWH.{u, v}
      (X.toEnrichedFunctor.obj a) (Y.toEnrichedFunctor.obj a) (Z.toEnrichedFunctor.obj a))
      (tensorHom_comp_tensorHom f g (π X Y a) (π Y Z a)))

set_option maxHeartbeats 200000 in
-- Preserve the original project budget for the complete enriched left identity law.
/-- The native identity is a left identity on the entire original mapping object. -/
theorem mappingIdentity_comp (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (λ_ (mappingObject X Y)).inv ≫ mappingIdentity X ▷ mappingObject X Y ≫
        mappingComposition X X Y = 𝟙 (mappingObject X Y) := by
  apply Enriched.weightedEnd.hom_ext X.toEnrichedFunctor Y.toEnrichedFunctor
  intro a
  simp only [Category.assoc, Category.id_comp]
  rw [mappingComposition_π]
  have ht := tensorHom_comp_tensorHom (mappingIdentity X) (𝟙 (mappingObject X Y))
    (π X X a) (π X Y a)
  simp only [tensorHom_id, Category.id_comp, mappingIdentity_π] at ht
  rw [← Category.assoc (mappingIdentity X ▷ mappingObject X Y), ht, tensorHom_def',
    Category.assoc, ← leftUnitor_inv_naturality_assoc,
    closed_e_id_comp PointedCGWH.{u, v} (X.toEnrichedFunctor.obj a)
      (Y.toEnrichedFunctor.obj a), Category.comp_id]

set_option maxHeartbeats 200000 in
-- Preserve the original project budget for the complete enriched right identity law.
/-- The native identity is a right identity on the entire original mapping object. -/
theorem mappingComposition_id (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (ρ_ (mappingObject X Y)).inv ≫ mappingObject X Y ◁ mappingIdentity Y ≫
        mappingComposition X Y Y = 𝟙 (mappingObject X Y) := by
  apply Enriched.weightedEnd.hom_ext X.toEnrichedFunctor Y.toEnrichedFunctor
  intro a
  simp only [Category.assoc, Category.id_comp]
  rw [mappingComposition_π]
  have ht := tensorHom_comp_tensorHom (𝟙 (mappingObject X Y)) (mappingIdentity Y)
    (π X Y a) (π Y Y a)
  simp only [id_tensorHom, Category.id_comp, mappingIdentity_π] at ht
  rw [← Category.assoc (mappingObject X Y ◁ mappingIdentity Y), ht, tensorHom_def,
    Category.assoc, ← rightUnitor_inv_naturality_assoc,
    closed_e_comp_id PointedCGWH.{u, v} (X.toEnrichedFunctor.obj a)
      (Y.toEnrichedFunctor.obj a), Category.comp_id]

set_option maxHeartbeats 200000 in
-- Preserve the original project budget for the complete enriched associativity law.
/-- The full native mapping composition is associative under the actual ambient associator. -/
theorem mappingComposition_assoc (W X Y Z : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (α_ (mappingObject W X) (mappingObject X Y) (mappingObject Y Z)).inv ≫
        mappingComposition W X Y ▷ mappingObject Y Z ≫ mappingComposition W Y Z =
      mappingObject W X ◁ mappingComposition X Y Z ≫ mappingComposition W X Z := by
  apply Enriched.weightedEnd.hom_ext W.toEnrichedFunctor Z.toEnrichedFunctor
  intro a
  simp only [Category.assoc]
  rw [mappingComposition_π, mappingComposition_π,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc,
    mappingComposition_π, mappingComposition_π]
  have hL := tensorHom_comp_tensorHom (π W X a ⊗ₘ π X Y a) (π Y Z a)
    (eComp PointedCGWH.{u, v} (W.toEnrichedFunctor.obj a)
      (X.toEnrichedFunctor.obj a) (Y.toEnrichedFunctor.obj a))
    (𝟙 ((ihom (Y.toEnrichedFunctor.obj a)).obj (Z.toEnrichedFunctor.obj a)))
  simp only [tensorHom_id, Category.comp_id] at hL
  have hR := tensorHom_comp_tensorHom (π W X a) (π X Y a ⊗ₘ π Y Z a)
    (𝟙 ((ihom (W.toEnrichedFunctor.obj a)).obj (X.toEnrichedFunctor.obj a)))
    (eComp PointedCGWH.{u, v} (X.toEnrichedFunctor.obj a)
      (Y.toEnrichedFunctor.obj a) (Z.toEnrichedFunctor.obj a))
  simp only [id_tensorHom, Category.comp_id] at hR
  rw [← hL, ← hR]
  have hα :
      (α_ (mappingObject W X) (mappingObject X Y) (mappingObject Y Z)).inv ≫
        ((π W X a ⊗ₘ π X Y a) ⊗ₘ π Y Z a) =
      (π W X a ⊗ₘ (π X Y a ⊗ₘ π Y Z a)) ≫
        (α_ ((ihom (W.toEnrichedFunctor.obj a)).obj (X.toEnrichedFunctor.obj a))
          ((ihom (X.toEnrichedFunctor.obj a)).obj (Y.toEnrichedFunctor.obj a))
          ((ihom (Y.toEnrichedFunctor.obj a)).obj (Z.toEnrichedFunctor.obj a))).inv := by
    apply (cancel_mono
      (α_ ((ihom (W.toEnrichedFunctor.obj a)).obj (X.toEnrichedFunctor.obj a))
        ((ihom (X.toEnrichedFunctor.obj a)).obj (Y.toEnrichedFunctor.obj a))
        ((ihom (Y.toEnrichedFunctor.obj a)).obj (Z.toEnrichedFunctor.obj a))).hom).1
    have h := congrArg
      (fun k => (α_ (mappingObject W X) (mappingObject X Y) (mappingObject Y Z)).inv ≫ k)
      (associator_naturality (π W X a) (π X Y a) (π Y Z a))
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using h
  simp only [Category.assoc]
  rw [← Category.assoc _ ((π W X a ⊗ₘ π X Y a) ⊗ₘ π Y Z a), hα]
  simpa only [Category.assoc] using congrArg
    (fun k => (π W X a ⊗ₘ (π X Y a ⊗ₘ π Y Z a)) ≫ k)
    (closed_e_assoc PointedCGWH.{u, v} (W.toEnrichedFunctor.obj a) (X.toEnrichedFunctor.obj a)
      (Y.toEnrichedFunctor.obj a) (Z.toEnrichedFunctor.obj a))

set_option maxHeartbeats 200000 in
-- Preserve the original project budget for the genuine ordinary carrier correspondence.
/-- Genuine unit-graded diagram maps are the native unit-shaped mapping-end arrows. -/
@[no_expose]
def mappingHomEquiv (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (X ⟶ Y) ≃ (𝟙_ PointedCGWH.{u, v} ⟶ mappingObject X Y) :=
  (gradeEquiv X Y (𝟙_ PointedCGWH.{u, v})).symm

set_option maxHeartbeats 200000 in
-- Preserve the original project budget for the ordinary correspondence forward map.
private theorem mappingHomEquiv_apply_proof (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (f : X ⟶ Y) : mappingHomEquiv X Y f = ofGrade X Y f := by
  unfold mappingHomEquiv
  exact gradeEquiv_symm_apply X Y f

/-- The ordinary correspondence uses the same original native end lift. -/
theorem mappingHomEquiv_apply (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I) (f : X ⟶ Y) :
    mappingHomEquiv X Y f = ofGrade X Y f :=
  mappingHomEquiv_apply_proof X Y f

set_option maxHeartbeats 200000 in
-- Preserve the original project budget for the ordinary correspondence inverse map.
private theorem mappingHomEquiv_symm_apply_proof
    (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (f : 𝟙_ PointedCGWH.{u, v} ⟶ mappingObject X Y) :
    (mappingHomEquiv X Y).symm f = toGrade X Y (𝟙_ PointedCGWH.{u, v}) f := by
  unfold mappingHomEquiv
  exact gradeEquiv_apply X Y (𝟙_ PointedCGWH.{u, v}) f

/-- The ordinary inverse is the full original native unit-graded projection family. -/
theorem mappingHomEquiv_symm_apply (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (f : 𝟙_ PointedCGWH.{u, v} ⟶ mappingObject X Y) :
    (mappingHomEquiv X Y).symm f = toGrade X Y (𝟙_ PointedCGWH.{u, v}) f :=
  mappingHomEquiv_symm_apply_proof X Y f

set_option maxHeartbeats 200000 in
-- Preserve the original project budget for the full ordinary mapping projection.
/-- Every original ordinary correspondence projection is the actual full raw unit-grade app. -/
theorem mappingHomEquiv_π (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I)
    (f : X ⟶ Y) (a : I) : mappingHomEquiv X Y f ≫ π X Y a = f.app a := by
  rw [mappingHomEquiv_apply, ofGrade_π]

set_option maxHeartbeats 200000 in
-- Preserve the original project budget for ordinary and enriched identity compatibility.
/-- The genuine ordinary identity agrees with the entire native enriched identity. -/
theorem mappingHomEquiv_id (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    mappingHomEquiv X X (𝟙 X) = mappingIdentity X := by
  apply Enriched.weightedEnd.hom_ext X.toEnrichedFunctor X.toEnrichedFunctor
  intro a
  rw [mappingHomEquiv_π, mappingIdentity_π]
  exact GradedNatTrans.unitId_app X.toEnrichedFunctor a

set_option maxHeartbeats 200000 in
-- Preserve the original project budget for ordinary and enriched composition compatibility.
/-- Genuine ordinary composition agrees with full native enriched composition at the unit. -/
theorem mappingHomEquiv_comp {X Y Z : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    mappingHomEquiv X Z (f ≫ g) = (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
      (mappingHomEquiv X Y f ⊗ₘ mappingHomEquiv Y Z g) ≫ mappingComposition X Y Z := by
  apply Enriched.weightedEnd.hom_ext X.toEnrichedFunctor Z.toEnrichedFunctor
  intro a
  rw [mappingHomEquiv_π]
  change (GradedNatTrans.unitComp f g).app a = _
  rw [GradedNatTrans.unitComp_app]
  simp only [Category.assoc]
  rw [mappingComposition_π]
  have h := tensorHom_comp_tensorHom (mappingHomEquiv X Y f) (mappingHomEquiv Y Z g)
    (π X Y a) (π Y Z a)
  rw [mappingHomEquiv_π, mappingHomEquiv_π] at h
  exact (congrArg (fun k => (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫ k ≫
    eComp PointedCGWH.{u, v} (X.toEnrichedFunctor.obj a)
      (Y.toEnrichedFunctor.obj a) (Z.toEnrichedFunctor.obj a)) h).symm

set_option maxHeartbeats 200000 in
-- Preserve the original project budget for the actual native enriched diagram carrier.
/-- Original native mapping ends give the enrichment of a small plain-enriched diagram type. -/
@[instance_reducible]
def enrichedCategory (I : Type) [EnrichedCategory PointedCGWH.{u, v} I] :
    EnrichedCategory PointedCGWH.{u, v} (EnrichedFunctorCat PointedCGWH.{u, v} I) where
  Hom := mappingObject
  id := mappingIdentity
  comp := mappingComposition
  id_comp := mappingIdentity_comp
  comp_id := mappingComposition_id
  assoc := mappingComposition_assoc

set_option maxHeartbeats 200000 in
-- Preserve the original project budget for full native enriched ordinary compatibility.
/-- The genuine unit-graded ordinary carrier and the original mapping-end enrichment agree. -/
@[instance_reducible]
def enrichedOrdinaryCategory (I : Type) [EnrichedCategory PointedCGWH.{u, v} I] :
    EnrichedOrdinaryCategory PointedCGWH.{u, v}
      (EnrichedFunctorCat PointedCGWH.{u, v} I) where
  toEnrichedCategory := enrichedCategory I
  homEquiv := mappingHomEquiv _ _
  homEquiv_id := mappingHomEquiv_id
  homEquiv_comp := mappingHomEquiv_comp

end PointedCGWH.EnrichedFunctorMapping
