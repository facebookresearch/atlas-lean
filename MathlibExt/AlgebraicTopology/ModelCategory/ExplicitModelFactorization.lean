/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.ExplicitModelIdentity

/-!
# Transport the actual chosen factorization through a model carrier

The input is the entire actual functorial factorization record.  Its original
middle objects, every Arrow map, both natural factors and their factorization
law are transported directly through the underlying identity functors.
Membership uses precisely the two inverse-image classes.  No new factorization
or cardinal is selected, and an existentially selected default getter is not
identified with this given data.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.ExplicitModelIdentity

variable {C : Type u} [Category.{v} C]

/-- Transport every component of the supplied actual record through the model-keyed identity. -/
def factorizationOnCarrier (m : ModelCategory C) {P Q : MorphismProperty C}
    (d : FunctorialFactorizationData P Q) :
    FunctorialFactorizationData (P.inverseImage (toBase m)) (Q.inverseImage (toBase m)) where
  Z := (toBase m).mapArrow ⋙ d.Z ⋙ ofBase m
  i :=
    { app F := InducedCategory.homMk (d.i.app ((toBase m).mapArrow.obj F))
      naturality {F G} a := by
        apply InducedCategory.hom_ext
        exact d.i.naturality ((toBase m).mapArrow.map a) }
  p :=
    { app F := InducedCategory.homMk (d.p.app ((toBase m).mapArrow.obj F))
      naturality {F G} a := by
        apply InducedCategory.hom_ext
        exact d.p.naturality ((toBase m).mapArrow.map a) }
  fac := by
    apply NatTrans.ext
    funext F
    apply InducedCategory.hom_ext
    exact d.fac_app
  hi F := d.hi ((toBase m).mapArrow.obj F)
  hp F := d.hp ((toBase m).mapArrow.obj F)

/-- The entire original middle functor is retained between the two full identity functions. -/
theorem factorizationOnCarrier_Z (m : ModelCategory C) {P Q : MorphismProperty C}
    (d : FunctorialFactorizationData P Q) :
    (factorizationOnCarrier m d).Z = (toBase m).mapArrow ⋙ d.Z ⋙ ofBase m := rfl

/-- Every underlying middle object is the supplied record's original object on the same arrow. -/
theorem factorizationOnCarrier_Z_obj (m : ModelCategory C) {P Q : MorphismProperty C}
    (d : FunctorialFactorizationData P Q) (F : Arrow (Carrier m)) :
    ((factorizationOnCarrier m d).Z.obj F).1 = d.Z.obj ((toBase m).mapArrow.obj F) := rfl

/-- Every complete Arrow input keeps the original supplied middle map function. -/
theorem factorizationOnCarrier_Z_map (m : ModelCategory C) {P Q : MorphismProperty C}
    (d : FunctorialFactorizationData P Q) {F G : Arrow (Carrier m)} (a : F ⟶ G) :
    ((factorizationOnCarrier m d).Z.map a).hom = d.Z.map ((toBase m).mapArrow.map a) := rfl

/-- The whole first-factor function is exactly the actual supplied original first factor. -/
theorem factorizationOnCarrier_i_app (m : ModelCategory C) {P Q : MorphismProperty C}
    (d : FunctorialFactorizationData P Q) (F : Arrow (Carrier m)) :
    ((factorizationOnCarrier m d).i.app F).hom = d.i.app ((toBase m).mapArrow.obj F) := rfl

/-- The whole second-factor function is exactly the actual supplied original second factor. -/
theorem factorizationOnCarrier_p_app (m : ModelCategory C) {P Q : MorphismProperty C}
    (d : FunctorialFactorizationData P Q) (F : Arrow (Carrier m)) :
    ((factorizationOnCarrier m d).p.app F).hom = d.p.app ((toBase m).mapArrow.obj F) := rfl

/-- The complete two factor functions recover the same actual original caller arrow. -/
theorem factorizationOnCarrier_fac (m : ModelCategory C) {P Q : MorphismProperty C}
    (d : FunctorialFactorizationData P Q) (F : Arrow (Carrier m)) :
    (factorizationOnCarrier m d).i.app F ≫ (factorizationOnCarrier m d).p.app F = F.hom :=
  (factorizationOnCarrier m d).fac_app

/-- Every whole caller square retains the full first-factor naturality law. -/
theorem factorizationOnCarrier_i_naturality (m : ModelCategory C) {P Q : MorphismProperty C}
    (d : FunctorialFactorizationData P Q) {F G : Arrow (Carrier m)} (a : F ⟶ G) :
    a.left ≫ (factorizationOnCarrier m d).i.app G =
      (factorizationOnCarrier m d).i.app F ≫ (factorizationOnCarrier m d).Z.map a :=
  (factorizationOnCarrier m d).i.naturality a

/-- Every whole caller square retains the full second-factor naturality law. -/
theorem factorizationOnCarrier_p_naturality (m : ModelCategory C) {P Q : MorphismProperty C}
    (d : FunctorialFactorizationData P Q) {F G : Arrow (Carrier m)} (a : F ⟶ G) :
    (factorizationOnCarrier m d).Z.map a ≫ (factorizationOnCarrier m d).p.app G =
      (factorizationOnCarrier m d).p.app F ≫ a.right :=
  (factorizationOnCarrier m d).p.naturality a

/-- The original transported middle functor preserves every actual identity input. -/
theorem factorizationOnCarrier_map_id (m : ModelCategory C) {P Q : MorphismProperty C}
    (d : FunctorialFactorizationData P Q) (F : Arrow (Carrier m)) :
    (factorizationOnCarrier m d).Z.map (𝟙 F) = 𝟙 ((factorizationOnCarrier m d).Z.obj F) :=
  (factorizationOnCarrier m d).Z.map_id F

/-- The supplied original middle function preserves every pair of complete caller squares. -/
theorem factorizationOnCarrier_map_comp (m : ModelCategory C) {P Q : MorphismProperty C}
    (d : FunctorialFactorizationData P Q) {F G H : Arrow (Carrier m)} (a : F ⟶ G) (b : G ⟶ H) :
    (factorizationOnCarrier m d).Z.map (a ≫ b) =
      (factorizationOnCarrier m d).Z.map a ≫ (factorizationOnCarrier m d).Z.map b :=
  (factorizationOnCarrier m d).Z.map_comp a b

/-- The first supplied actual membership field is retained on the same underlying map. -/
theorem factorizationOnCarrier_i_mem (m : ModelCategory C) {P Q : MorphismProperty C}
    (d : FunctorialFactorizationData P Q) (F : Arrow (Carrier m)) :
    P ((factorizationOnCarrier m d).i.app F).hom := (factorizationOnCarrier m d).hi F

/-- The second supplied actual membership field is retained on the same underlying map. -/
theorem factorizationOnCarrier_p_mem (m : ModelCategory C) {P Q : MorphismProperty C}
    (d : FunctorialFactorizationData P Q) (F : Arrow (Carrier m)) :
    Q ((factorizationOnCarrier m d).p.app F).hom := (factorizationOnCarrier m d).hp F

/-- The supplied actual record proves functorial factorization without equating default choices. -/
theorem factorizationOnCarrier_exists (m : ModelCategory C) {P Q : MorphismProperty C}
    (d : FunctorialFactorizationData P Q) :
    HasFunctorialFactorization (P.inverseImage (toBase m)) (Q.inverseImage (toBase m)) :=
  ⟨⟨factorizationOnCarrier m d⟩⟩

end HomotopicalAlgebra.ExplicitModelIdentity
