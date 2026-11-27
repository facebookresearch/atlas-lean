/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidCompletionHoms

/-!
# The actual original-object degreewise groupoid-completion enrichment

The SAME original object type receives its actual completed simplicial
Homs. The complete native degreewise identities, compositions and
inverses commute with every original scalar operator. Both whole inverse
equations and all enriched laws use the genuine native groupoid laws.
No completion unit weakness or derived/model conclusion is assumed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion

variable (C : Carrier.{u})

/-- The SAME actual original completed identity in every scalar degree. -/
def idMap (x : C) : 𝟙_ SSet.{u} ⟶ hom C x x where
  app q := ↾fun _ => 𝟙 (vertex C q x)
  naturality q r f := by
    ext a
    exact (Functor.map_id (operator C f) (vertex C q x)).symm

/-- Actual full completed composition uses SAME native degreewise composition on original
endpoints. -/
def compMap (x y z : C) : hom C x y ⊗ hom C y z ⟶ hom C x z where
  app q := ↾fun a => a.1 ≫ a.2
  naturality q r f := by
    ext a
    exact (Functor.map_comp (operator C f) a.1 a.2).symm

/-- Every full original completed inverse is a genuine scalar map retaining all ordinal
operators. -/
def inverseMap (x y : C) : hom C x y ⟶ hom C y x where
  app q := ↾fun a => @Groupoid.inv (category C q) inferInstance (vertex C q x) (vertex C q y) a
  naturality q r f := by
    ext a
    let _ : IsIso a := @IsIso.of_groupoid (category C q) inferInstance (vertex C q x)
      (vertex C q y) a
    let _ : IsIso ((operator C f).map a) := @IsIso.of_groupoid (category C r) inferInstance
      ((operator C f).obj (vertex C q x)) ((operator C f).obj (vertex C q y)) ((operator C f).map a)
    change Groupoid.inv ((operator C f).map a) = (operator C f).map (Groupoid.inv a)
    exact (Groupoid.inv_eq_inv ((operator C f).map a)).trans
      ((Functor.map_inv (operator C f) a).symm.trans
        (congrArg (fun b => (operator C f).map b) (Groupoid.inv_eq_inv a).symm))

/-- The complete original-object enrichment is supplied by the SAME actual native completed Homs. -/
@[instance_reducible]
def enrichment : EnrichedCategory SSet.{u} C where
  Hom := hom C
  id := idMap C
  comp := compMap C
  id_comp x y := by
    ext q a
    exact Category.id_comp a
  comp_id x y := by
    ext q a
    exact Category.comp_id a
  assoc x y z t := by
    ext q a
    exact Category.assoc a.1 a.2.1 a.2.2

/-- The actual full original-object completion carrier, preserving the SAME supplied
individual objects. -/
def object : Carrier.{u} := by
  let _ : EnrichedCategory SSet.{u} C := enrichment C
  exact SimplicialEnrichment.of C

/-- The SAME completed Hom readback is literal at every original ordered pair. -/
theorem object_hom (x y : object C) : (x ⟶[SSet.{u}] y) = hom C x y := rfl

/-- The actual full inverse followed by its SAME original completed arrow is the whole
native identity in each
degree. -/
theorem inverse_comp (q : SimplexCategoryᵒᵖ) (x y : C) (a : (hom C x y).obj q) :
    (compMap C y x y).app q ((inverseMap C x y).app q a, a) = (idMap C y).app q PUnit.unit :=
  @Groupoid.inv_comp (category C q) inferInstance (vertex C q x) (vertex C q y) a

/-- The SAME actual arrow followed by its full completed inverse is the whole native
identity in each degree. -/
theorem comp_inverse (q : SimplexCategoryᵒᵖ) (x y : C) (a : (hom C x y).obj q) :
    (compMap C x y x).app q (a, (inverseMap C x y).app q a) = (idMap C x).app q PUnit.unit :=
  @Groupoid.comp_inv (category C q) inferInstance (vertex C q x) (vertex C q y) a

/-- Applying the actual full completed inverse twice recovers every original completed Hom
simplex. -/
theorem inverseMap_involutive (x y : C) : inverseMap C x y ≫ inverseMap C y x = 𝟙 (hom C x y) := by
  ext q a
  exact (@Groupoid.invEquiv (category C q) inferInstance (vertex C q x) (vertex C q y)).left_inv a

end CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion
