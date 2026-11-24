/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# Small simplicial-presheaf carriers and their original maps

The carrier is the ordinary functor category on the opposite of the original site. Discrete
representables retain the original Hom types through the native shrinking equivalence. Products,
scalar tensors and site equivalences use the native functor-category constructions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w v' w'

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory Opposite

/-- Simplicial presheaves on the original site in the fixed value universe. -/
abbrev SimplicialPresheaf (D : Type w) [Category.{v} D] := Dᵒᵖ ⥤ SSet.{u}

namespace SimplicialPresheaf

variable {D : Type w} [Category.{v} D] {E : Type w'} [Category.{v'} E]

section Representables

variable [LocallySmall.{u} D]

/-- The discrete representable simplicial presheaves, with Hom values shrunk in the fixed
value universe using the original Hom equivalence. -/
def discreteYoneda : D ⥤ SimplicialPresheaf.{u} D :=
  shrinkYoneda.{u} ⋙ (whiskeringRight Dᵒᵖ (Type u) SSet.{u}).obj
    (Functor.const SimplexCategoryᵒᵖ)

/-- Every degree of a discrete representable identifies with the original Hom type. -/
def discreteYonedaObjEquiv (d : D) (a : Dᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    (((discreteYoneda.{u}.obj d).obj a).obj n) ≃ (a.unop ⟶ d) :=
  shrinkYonedaObjObjEquiv

/-- An original site map acts by precomposition on the original Hom value. -/
theorem discreteYoneda_obj_map (d : D) {a b : Dᵒᵖ} (g : a ⟶ b)
    (n : SimplexCategoryᵒᵖ) (h : ((discreteYoneda.{u}.obj d).obj a).obj n) :
    discreteYonedaObjEquiv d b n (((discreteYoneda.{u}.obj d).map g).app n h) =
      g.unop ≫ discreteYonedaObjEquiv d a n h :=
  shrinkYonedaObjObjEquiv_obj_map g h

/-- An original representing-object map acts by postcomposition on the original Hom value. -/
theorem discreteYoneda_map_app {d d' : D} (t : d ⟶ d') (a : Dᵒᵖ)
    (n : SimplexCategoryᵒᵖ) (h : ((discreteYoneda.{u}.obj d).obj a).obj n) :
    discreteYonedaObjEquiv d' a n (((discreteYoneda.{u}.map t).app a).app n h) =
      discreteYonedaObjEquiv d a n h ≫ t :=
  shrinkYonedaObjObjEquiv_map_app h t

/-- Every inner simplex operator is the identity on the discrete representable value. -/
theorem discreteYoneda_inner_map (d : D) (a : Dᵒᵖ)
    {n n' : SimplexCategoryᵒᵖ} (δ : n ⟶ n') :
    ((discreteYoneda.{u}.obj d).obj a).map δ = 𝟙 _ :=
  rfl

end Representables

section ProductsAndTensors

/-- The native pointwise product has the original two values in every bidegree. -/
theorem product_obj (X Y : SimplicialPresheaf.{u} D) (a : Dᵒᵖ)
    (n : SimplexCategoryᵒᵖ) :
    ((X ⊗ Y).obj a).obj n = ((X.obj a).obj n × (Y.obj a).obj n) :=
  rfl

/-- The product of natural maps acts by their original two components. -/
theorem product_map_apply {X X' Y Y' : SimplicialPresheaf.{u} D}
    (f : X ⟶ X') (g : Y ⟶ Y') (a : Dᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (z : ((X ⊗ Y).obj a).obj n) :
    ((f ⊗ₘ g).app a).app n z = ((f.app a).app n z.1, (g.app a).app n z.2) :=
  rfl

/-- The scalar tensor bifunctor is the native tensor with a constant scalar presheaf. -/
def scalarTensor : SimplicialPresheaf.{u} D ⥤ SSet.{u} ⥤ SimplicialPresheaf.{u} D :=
  curriedTensor (SimplicialPresheaf.{u} D) ⋙
    (whiskeringLeft SSet.{u} (SimplicialPresheaf.{u} D) (SimplicialPresheaf.{u} D)).obj
      (Functor.const Dᵒᵖ)

/-- The scalar tensor keeps the original presheaf and scalar points in each bidegree. -/
theorem scalarTensor_obj (X : SimplicialPresheaf.{u} D) (K : SSet.{u})
    (a : Dᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    (((scalarTensor.obj X).obj K).obj a).obj n = ((X.obj a).obj n × K.obj n) :=
  rfl

/-- A scalar map is the original scalar component at each presheaf point. -/
theorem scalarTensor_scalar_map (X : SimplicialPresheaf.{u} D) {K L : SSet.{u}}
    (g : K ⟶ L) (a : Dᵒᵖ) :
    ((scalarTensor.obj X).map g).app a = X.obj a ◁ g :=
  rfl

/-- A presheaf map is the original component at the same scalar. -/
theorem scalarTensor_presheaf_map {X Y : SimplicialPresheaf.{u} D}
    (f : X ⟶ Y) (K : SSet.{u}) (a : Dᵒᵖ) :
    ((scalarTensor.map f).app K).app a = f.app a ▷ K :=
  rfl

end ProductsAndTensors

section SiteTransport

/-- A site equivalence transports the literal presheaf category by native inverse
precomposition on the opposite site. -/
def transport (e : D ≌ E) : SimplicialPresheaf.{u} D ≌ SimplicialPresheaf.{u} E :=
  e.op.congrLeft

/-- Forward transport keeps the original diagram after inverse-opposite precomposition. -/
theorem transport_functor_obj (e : D ≌ E) (X : SimplicialPresheaf.{u} D) :
    (transport e).functor.obj X = e.inverse.op ⋙ X :=
  rfl

/-- Inverse transport keeps the original diagram after forward-opposite precomposition. -/
theorem transport_inverse_obj (e : D ≌ E) (Y : SimplicialPresheaf.{u} E) :
    (transport e).inverse.obj Y = e.functor.op ⋙ Y :=
  rfl

/-- Forward transport evaluates each original natural map at the inverse site object. -/
theorem transport_functor_map_app (e : D ≌ E) {X Y : SimplicialPresheaf.{u} D}
    (f : X ⟶ Y) (a : Eᵒᵖ) :
    ((transport e).functor.map f).app a = f.app (e.inverse.op.obj a) :=
  rfl

/-- Inverse transport evaluates each original natural map at the forward site object. -/
theorem transport_inverse_map_app (e : D ≌ E) {X Y : SimplicialPresheaf.{u} E}
    (f : X ⟶ Y) (a : Dᵒᵖ) :
    ((transport e).inverse.map f).app a = f.app (e.functor.op.obj a) :=
  rfl

/-- The native transport unit evaluates the original diagram on the opposite-site unit. -/
theorem transport_unit_app (e : D ≌ E) (X : SimplicialPresheaf.{u} D) (a : Dᵒᵖ) :
    ((transport e).unitIso.app X).hom.app a = X.map ((e.op.unitIso.app a).hom) := by
  exact Equivalence.funInvIdAssoc_inv_app e.op X a

/-- The native transport counit evaluates the original diagram on the opposite-site counit. -/
theorem transport_counit_app (e : D ≌ E) (Y : SimplicialPresheaf.{u} E) (a : Eᵒᵖ) :
    ((transport e).counitIso.app Y).hom.app a = Y.map ((e.op.counitIso.app a).hom) := by
  exact Equivalence.invFunIdAssoc_hom_app e.op Y a

/-- Forward site transport keeps the same pointwise product. -/
theorem transport_product (e : D ≌ E) (X Y : SimplicialPresheaf.{u} D) :
    (transport e).functor.obj (X ⊗ Y) =
      (transport e).functor.obj X ⊗ (transport e).functor.obj Y :=
  rfl

/-- Forward site transport keeps the same scalar tensor in the fixed scalar universe. -/
theorem transport_scalarTensor (e : D ≌ E) (X : SimplicialPresheaf.{u} D) (K : SSet.{u}) :
    (transport e).functor.obj ((scalarTensor.obj X).obj K) =
      (scalarTensor.obj ((transport e).functor.obj X)).obj K :=
  rfl

/-- Identity site transport is the native identity precomposition on the original carrier. -/
def transportIdentity (D : Type w) [Category.{v} D] :
    (transport (CategoryTheory.Equivalence.refl (C := D))).functor ≅
      𝟭 (SimplicialPresheaf.{u} D) :=
  whiskeringLeftObjIdIso

/-- Both original endpoints and the original arrow equation are retained by the Arrow unit. -/
theorem transport_arrow_unit (e : D ≌ E) (f : Arrow (SimplicialPresheaf.{u} D)) :
    let A := Functor.mapArrowEquivalence (transport e)
    ((A.unitIso.app f).hom.left = ((transport e).unitIso.app f.left).hom) ∧
    ((A.unitIso.app f).hom.right = ((transport e).unitIso.app f.right).hom) ∧
    ((A.unitIso.app f).hom.left ≫
        (transport e).inverse.map ((transport e).functor.map f.hom) =
      f.hom ≫ (A.unitIso.app f).hom.right) := by
  dsimp only
  exact ⟨rfl, rfl, ((Functor.mapArrowEquivalence (transport e)).unitIso.app f).hom.w⟩

/-- Both original endpoints and the original arrow equation are retained by the Arrow counit. -/
theorem transport_arrow_counit (e : D ≌ E) (f : Arrow (SimplicialPresheaf.{u} E)) :
    let A := Functor.mapArrowEquivalence (transport e)
    ((A.counitIso.app f).hom.left = ((transport e).counitIso.app f.left).hom) ∧
    ((A.counitIso.app f).hom.right = ((transport e).counitIso.app f.right).hom) ∧
    ((A.counitIso.app f).hom.left ≫ f.hom =
      (transport e).functor.map ((transport e).inverse.map f.hom) ≫
        (A.counitIso.app f).hom.right) := by
  dsimp only
  exact ⟨rfl, rfl, ((Functor.mapArrowEquivalence (transport e)).counitIso.app f).hom.w⟩

end SiteTransport

section Normalization

/-- The actual native Hom-shrink equivalence transports the original presheaf carrier. -/
def homShrinkTransport [LocallySmall.{u} D] :
    letI : Category.{u} (ShrinkHoms D) := inferInstance
    SimplicialPresheaf.{u} D ≌ SimplicialPresheaf.{u} (ShrinkHoms D) := by
  letI : Category.{u} (ShrinkHoms D) := inferInstance
  exact transport (ShrinkHoms.equivalence.{u} D)

/-- The native small model transports the original carrier when both objects and Hom types
are small in the fixed value universe. -/
def smallModelTransport [Small.{u} D] [LocallySmall.{u} D] :
    SimplicialPresheaf.{u} D ≌ SimplicialPresheaf.{u} (SmallModel.{u} D) :=
  transport (equivSmallModel.{u} D)

/-- The original presheaf Hom types are small in the fixed value universe, via the native
fully faithful small-model transport. -/
theorem locallySmall [Small.{u} D] [LocallySmall.{u} D] :
    LocallySmall.{u} (SimplicialPresheaf.{u} D) := by
  exact locallySmall_of_faithful (smallModelTransport (D := D)).functor

end Normalization

section RepresentableTransport

variable [LocallySmall.{u} D] [LocallySmall.{u} E]

/-- The original Hom-value equivalence for a transported representable, adjusted by the
actual site counit. -/
def representableValueEquiv (e : D ≌ E) (d : D) (a : Eᵒᵖ) :
    ((shrinkYoneda.{u}.obj d).obj (e.inverse.op.obj a)) ≃
      ((shrinkYoneda.{u}.obj (e.functor.obj d)).obj a) :=
  (shrinkYonedaObjObjEquiv (X := d) (Y := e.inverse.op.obj a)).trans <|
    (e.fullyFaithfulFunctor.homEquiv).trans <|
      (Iso.homCongr (e.counitIso.app a.unop) (Iso.refl _)).trans
        (shrinkYonedaObjObjEquiv (X := e.functor.obj d) (Y := a)).symm

/-- The transported representable value keeps the original Hom map and counit component. -/
theorem representableValueEquiv_apply (e : D ≌ E) (d : D) (a : Eᵒᵖ)
    (h : (shrinkYoneda.{u}.obj d).obj (e.inverse.op.obj a)) :
    shrinkYonedaObjObjEquiv (representableValueEquiv e d a h) =
      (e.counitIso.app a.unop).inv ≫ e.functor.map (shrinkYonedaObjObjEquiv h) := by
  simp [representableValueEquiv, Equiv.trans_apply]

/-- The Hom-value comparison commutes with each original opposite-site map. -/
theorem representableValueEquiv_naturality (e : D ≌ E) (d : D)
    {a b : Eᵒᵖ} (g : a ⟶ b)
    (h : (shrinkYoneda.{u}.obj d).obj (e.inverse.op.obj a)) :
    representableValueEquiv e d b
        ((shrinkYoneda.{u}.obj d).map (e.inverse.op.map g) h) =
      (shrinkYoneda.{u}.obj (e.functor.obj d)).map g (representableValueEquiv e d a h) := by
  apply shrinkYonedaObjObjEquiv.injective
  rw [representableValueEquiv_apply, shrinkYonedaObjObjEquiv_obj_map,
    shrinkYonedaObjObjEquiv_obj_map, representableValueEquiv_apply]
  simpa only [Functor.op_map, Quiver.Hom.unop_op, Functor.map_comp, Functor.comp_map,
    Functor.id_map, Functor.id_obj, Iso.app_inv, Category.assoc] using
    congrArg (fun f => f ≫ e.functor.map (shrinkYonedaObjObjEquiv h))
      (e.counitIso.inv.naturality g.unop).symm

/-- The Hom-value comparison commutes with each original representing-object map. -/
theorem representableValueEquiv_target_naturality (e : D ≌ E) {d d' : D}
    (t : d ⟶ d') (a : Eᵒᵖ)
    (h : (shrinkYoneda.{u}.obj d).obj (e.inverse.op.obj a)) :
    representableValueEquiv e d' a
        (((shrinkYoneda.{u}.map t).app (e.inverse.op.obj a)) h) =
      ((shrinkYoneda.{u}.map (e.functor.map t)).app a) (representableValueEquiv e d a h) := by
  have hs : shrinkYonedaObjObjEquiv
        (((shrinkYoneda.{u}.map t).app (e.inverse.op.obj a)) h) =
      shrinkYonedaObjObjEquiv h ≫ t :=
    shrinkYonedaObjObjEquiv_map_app (C := D) (X := d) (X' := d')
      (Y := e.inverse.op.obj a) h t
  apply shrinkYonedaObjObjEquiv.injective
  rw [shrinkYonedaObjObjEquiv_map_app, representableValueEquiv_apply,
    representableValueEquiv_apply, hs,
    Functor.map_comp, Category.assoc]

/-- Transport identifies each original discrete representable with the representable at the
transported object, using the original Hom equivalence and counit. -/
def transportDiscreteYoneda (e : D ≌ E) :
    discreteYoneda.{u} ⋙ (transport e).functor ≅ e.functor ⋙ discreteYoneda.{u} := by
  change discreteYoneda.{u} ⋙
      (whiskeringLeft Eᵒᵖ Dᵒᵖ SSet.{u}).obj e.inverse.op ≅
    e.functor ⋙ discreteYoneda.{u}
  refine NatIso.ofComponents (fun d => NatIso.ofComponents
    (fun a => (Functor.const SimplexCategoryᵒᵖ).mapIso
      (representableValueEquiv e d a).toIso) ?_) ?_
  · intro a b g
    ext n h
    exact representableValueEquiv_naturality e d g h
  · intro d d' t
    ext a n h
    exact representableValueEquiv_target_naturality e t a h

/-- The actual forward transported-representable component is the original Hom comparison. -/
theorem transportDiscreteYoneda_hom_app (e : D ≌ E) (d : D) (a : Eᵒᵖ)
    (n : SimplexCategoryᵒᵖ)
    (h : (((transport e).functor.obj (discreteYoneda.{u}.obj d)).obj a).obj n) :
    (((transportDiscreteYoneda e).hom.app d).app a).app n h =
      representableValueEquiv e d a h :=
  rfl

/-- The actual inverse transported-representable component is the same Hom comparison's inverse. -/
theorem transportDiscreteYoneda_inv_app (e : D ≌ E) (d : D) (a : Eᵒᵖ)
    (n : SimplexCategoryᵒᵖ)
    (h : ((discreteYoneda.{u}.obj (e.functor.obj d)).obj a).obj n) :
    (((transportDiscreteYoneda e).inv.app d).app a).app n h =
      (representableValueEquiv e d a).symm h :=
  rfl

end RepresentableTransport

end SimplicialPresheaf
