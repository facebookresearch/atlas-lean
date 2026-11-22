/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplex
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalSSet
public import MathlibExt.AlgebraicTopology.SimplicialSpace.Presheaf
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic

/-!
# The original total-space adjunction

The outer-first kernel is `Δ[n] × J[m]`, with the full free-category-groupoid
nerve in the inner parameter. Its native extension along product-site Yoneda
and original restricted-Hom right adjoint are transported through the actual
designated simplicial-space and Joyal carriers. Every map retains its original
source operators and adjunction maps.

These are the data of Joyal–Tierney §2 preceding Lemma 2.11. Model preservation and
Theorem 4.12 are subsequent properties of this same adjunction.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory

namespace SimplicialSpace.TotalSpace

/-- The actual outer-simplex, inner-free-groupoid product kernel. -/
def kernel : SimplexCategory × SimplexCategory ⥤ SSet.{u} :=
  (SSet.stdSimplex.{u}.prod SSet.FreeGroupoidSimplex.J.{u}) ⋙ tensor SSet.{u}

/-- The actual native extension along the product-site lifted Yoneda embedding. -/
abbrev presheafLeft : ((SimplexCategory × SimplexCategory)ᵒᵖ ⥤ Type u) ⥤ SSet.{u} :=
  (uliftYoneda.{u} (C := SimplexCategory × SimplexCategory)).leftKanExtension kernel.{u}

/-- The original lifted Hom functor from the actual total kernel. -/
abbrev presheafRight : SSet.{u} ⥤ (SimplexCategory × SimplexCategory)ᵒᵖ ⥤ Type u :=
  Presheaf.restrictedULiftYoneda.{0} kernel.{u}

set_option backward.isDefEq.respectTransparency false in
/-- The native product-Yoneda extension/restricted-Hom adjunction. -/
def presheafAdjunction : presheafLeft.{u} ⊣ presheafRight.{u} :=
  Presheaf.uliftYonedaAdjunction.{0}
    ((uliftYoneda.{u} (C := SimplexCategory × SimplexCategory)).leftKanExtension kernel.{u})
    ((uliftYoneda.{u} (C := SimplexCategory × SimplexCategory)).leftKanExtensionUnit kernel.{u})

/-- The full original representable comparison for the product-site extension. -/
def presheafRepresentableIso :
    (uliftYoneda.{u} (C := SimplexCategory × SimplexCategory)) ⋙ presheafLeft.{u} ≅
      kernel.{u} :=
  Presheaf.isExtensionAlongULiftYoneda kernel.{u}

/-- The same left extension is the actual colimit over its original generators. -/
def presheafLeftIsoColimit (P : (SimplexCategory × SimplexCategory)ᵒᵖ ⥤ Type u) :
    presheafLeft.obj P ≅ Limits.colimit
      (CostructuredArrow.proj
        (uliftYoneda.{u} (C := SimplexCategory × SimplexCategory)) P ⋙ kernel.{u}) :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    ((uliftYoneda.{u} (C := SimplexCategory × SimplexCategory)).leftKanExtension kernel.{u})
    ((uliftYoneda.{u} (C := SimplexCategory × SimplexCategory)).leftKanExtensionUnit kernel.{u})
    P).isoColimit

/-- The actual left total-space functor on the designated source and target. -/
abbrev left : SimplicialSpace.{u} ⥤ JoyalSSet.{u} :=
  equivalencePresheaf.{u}.functor ⋙ presheafLeft.{u} ⋙ JoyalSSet.ofSSet.{u}

/-- The actual right total-space functor on the designated target and source. -/
abbrev right : JoyalSSet.{u} ⥤ SimplicialSpace.{u} :=
  JoyalSSet.forget.{u} ⋙ presheafRight.{u} ⋙ equivalencePresheaf.{u}.inverse

/-- Transport of this same actual extension/Hom adjunction through the carriers. -/
def adjunction : left.{u} ⊣ right.{u} :=
  (equivalencePresheaf.{u}.toAdjunction.comp presheafAdjunction.{u}).comp
    JoyalSSet.equivalenceSSet.{u}.symm.toAdjunction

/-- The original box representables with outer and inner degrees in that order. -/
def representable : SimplexCategory × SimplexCategory ⥤ SimplicialSpace.{u} :=
  (SSet.stdSimplex.{u}.prod SSet.stdSimplex.{u}) ⋙
    externalProductBifunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u) ⋙
    Functor.curry ⋙ ofSimplicialObject.{u}

/-- The original box representable is product-site Yoneda by literal pairing. -/
def representablePresheafIso :
    representable.{u} ⋙ equivalencePresheaf.{u}.functor ≅
      uliftYoneda.{u} (C := SimplexCategory × SimplexCategory) := by
  refine NatIso.ofComponents (fun c => ?_) ?_
  · refine
      { hom :=
          { app := fun p => ↾fun x => ULift.up (x.1.down, x.2.down)
            naturality := by intro p q f; ext x; rfl }
        inv :=
          { app := fun p => ↾fun x => (ULift.up x.down.1, ULift.up x.down.2)
            naturality := by intro p q f; ext x; rfl }
        hom_inv_id := by ext p x; rfl
        inv_hom_id := by ext p x; rfl }
  · intro c d f
    ext p x
    rfl

/-- The full natural comparison of the actual left image of every box representable. -/
def representableIso : representable.{u} ⋙ left.{u} ≅ kernel.{u} ⋙ JoyalSSet.ofSSet.{u} :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerRight representablePresheafIso.{u} presheafLeft.{u} ≪≫
      presheafRepresentableIso.{u}) JoyalSSet.ofSSet.{u}

/-- The original right-image bidegree is the actual unlifted kernel Hom set. -/
def rightHomEquiv (Q : JoyalSSet.{u}) (c : SimplexCategory × SimplexCategory) :
    ((right.obj Q).diagram.obj (op c.1)).obj (op c.2) ≃ (kernel.obj c ⟶ Q.toSSet) :=
  Equiv.ulift

/-- The original map from a box representable specified by an actual bidegree point. -/
def simplexMap (X : SimplicialSpace.{u}) (c : SimplexCategory × SimplexCategory)
    (x : (toPresheaf.obj X).obj (op c)) : representable.obj c ⟶ X :=
  equivalencePresheaf.{u}.fullyFaithfulFunctor.preimage
    (representablePresheafIso.hom.app c ≫ uliftYonedaEquiv.symm x)

/-- The original representable map retains its exact product-Yoneda component. -/
theorem simplexMap_toPresheaf (X : SimplicialSpace.{u})
    (c : SimplexCategory × SimplexCategory) (x : (toPresheaf.obj X).obj (op c)) :
    toPresheaf.map (simplexMap X c x) =
      representablePresheafIso.hom.app c ≫ uliftYonedaEquiv.symm x :=
  equivalencePresheaf.{u}.fullyFaithfulFunctor.map_preimage _

/-- The kernel has the literal pointwise product carrier in every simplex degree. -/
theorem kernel_obj_obj (c : SimplexCategory × SimplexCategory) (p : SimplexCategoryᵒᵖ) :
    (kernel.{u}.obj c).obj p =
      ((SSet.stdSimplex.{u}.obj c.1).obj p ×
        (SSet.FreeGroupoidSimplex.J.{u}.obj c.2).obj p) := rfl

/-- Both original cosimplicial source operators act on the corresponding kernel factors. -/
theorem kernel_map {c d : SimplexCategory × SimplexCategory} (f : c ⟶ d) :
    kernel.{u}.map f =
      SSet.stdSimplex.map f.1 ⊗ₘ SSet.FreeGroupoidSimplex.J.map f.2 := rfl

/-- The right image retains the original Hom set in every bidegree. -/
theorem right_obj_obj (Q : JoyalSSet.{u}) (n m : SimplexCategoryᵒᵖ) :
    ((right.obj Q).diagram.obj n).obj m =
      ULift.{0} (kernel.obj (n.unop, m.unop) ⟶ Q.toSSet) := rfl

/-- An original target map postcomposes every actual kernel map. -/
theorem right_map_app {Q Q' : JoyalSSet.{u}} (q : Q ⟶ Q')
    (n m : SimplexCategoryᵒᵖ)
    (h : ULift.{0} (kernel.obj (n.unop, m.unop) ⟶ Q.toSSet)) :
    (((right.map q).hom.app n).app m) h =
      ULift.up (h.down ≫ JoyalSSet.forget.map q) := rfl

/-- Every original kernel parameter map acts on the literal pair of simplices. -/
theorem kernel_map_app {c d : SimplexCategory × SimplexCategory} (f : c ⟶ d)
    (p : SimplexCategoryᵒᵖ) (x : (kernel.{u}.obj c).obj p) :
    (kernel.map f).app p x =
      ((SSet.stdSimplex.map f.1).app p x.1,
        (SSet.FreeGroupoidSimplex.J.map f.2).app p x.2) := rfl

/-- Simplicial degree restriction inside the kernel acts on both original factors. -/
theorem kernel_obj_map (c : SimplexCategory × SimplexCategory)
    {p q : SimplexCategoryᵒᵖ} (f : p ⟶ q) (x : (kernel.{u}.obj c).obj p) :
    (kernel.obj c).map f x =
      ((SSet.stdSimplex.obj c.1).map f x.1,
        (SSet.FreeGroupoidSimplex.J.obj c.2).map f x.2) := rfl

/-- The box representable retains its original outer/inner product carrier. -/
theorem representable_obj_obj (c : SimplexCategory × SimplexCategory)
    (n m : SimplexCategoryᵒᵖ) :
    ((representable.{u}.obj c).diagram.obj n).obj m =
      ((SSet.stdSimplex.{u}.obj c.1).obj n × (SSet.stdSimplex.{u}.obj c.2).obj m) := rfl

/-- The original parameter maps of a box representable act in their own coordinates. -/
theorem representable_map_app {c d : SimplexCategory × SimplexCategory} (f : c ⟶ d)
    (n m : SimplexCategoryᵒᵖ) (x : ((representable.{u}.obj c).diagram.obj n).obj m) :
    (((representable.map f).hom.app n).app m) x =
      ((SSet.stdSimplex.map f.1).app n x.1, (SSet.stdSimplex.map f.2).app m x.2) := rfl

/-- The original outer operator restricts the outer simplex of each right-image map. -/
theorem right_obj_map_outer (Q : JoyalSSet.{u}) {n n' : SimplexCategoryᵒᵖ}
    (f : n ⟶ n') (m : SimplexCategoryᵒᵖ)
    (h : ULift.{0} (kernel.obj (n.unop, m.unop) ⟶ Q.toSSet)) :
    (((right.obj Q).diagram.map f).app m) h =
      ULift.up (kernel.map (f.unop, 𝟙 m.unop) ≫ h.down) := rfl

/-- The original inner operator restricts the full free-groupoid factor of each map. -/
theorem right_obj_map_inner (Q : JoyalSSet.{u}) (n : SimplexCategoryᵒᵖ)
    {m m' : SimplexCategoryᵒᵖ} (f : m ⟶ m')
    (h : ULift.{0} (kernel.obj (n.unop, m.unop) ⟶ Q.toSSet)) :
    ((right.obj Q).diagram.obj n).map f h =
      ULift.up (kernel.map (𝟙 n.unop, f.unop) ≫ h.down) := rfl

/-- The original actual left total functor and its actual unit/counit satisfy the left triangle. -/
theorem adjunction_left_triangle (X : SimplicialSpace.{u}) :
    left.map (adjunction.unit.app X) ≫ adjunction.counit.app (left.obj X) =
      𝟙 (left.obj X) := adjunction.left_triangle_components X

/-- The original actual right total functor and its actual unit/counit satisfy the right
triangle. -/
theorem adjunction_right_triangle (Q : JoyalSSet.{u}) :
    adjunction.unit.app (right.obj Q) ≫ right.map (adjunction.counit.app Q) =
      𝟙 (right.obj Q) := adjunction.right_triangle_components Q

/-- Every original box parameter operator respects the full representable comparison. -/
@[reassoc]
theorem representableIso_hom_naturality {c d : SimplexCategory × SimplexCategory}
    (f : c ⟶ d) :
    left.map (representable.map f) ≫ representableIso.{u}.hom.app d =
      representableIso.hom.app c ≫ JoyalSSet.ofSSet.map (kernel.map f) :=
  representableIso.hom.naturality f

set_option backward.isDefEq.respectTransparency false in
/-- The actual raw adjunct sends an original point to its original extension generator. -/
theorem presheafAdjunction_homEquiv_app
    {P : (SimplexCategory × SimplexCategory)ᵒᵖ ⥤ Type u} {Q : SSet.{u}}
    (f : presheafLeft.obj P ⟶ Q) (c : SimplexCategory × SimplexCategory)
    (x : P.obj (op c)) :
    ULift.down (((presheafAdjunction.homEquiv P Q) f).app (op c) x) =
      presheafRepresentableIso.inv.app c ≫ presheafLeft.map (uliftYonedaEquiv.symm x) ≫ f := by
  let : presheafLeft.{u}.IsLeftKanExtension
      ((uliftYoneda.{u} (C := SimplexCategory × SimplexCategory)).leftKanExtensionUnit
          kernel.{u}) := by
    change
        ((uliftYoneda.{u} (C := SimplexCategory × SimplexCategory)).leftKanExtension
          kernel.{u}).IsLeftKanExtension
      ((uliftYoneda.{u} (C := SimplexCategory × SimplexCategory)).leftKanExtensionUnit kernel.{u})
    infer_instance
  have h := @Presheaf.uliftYonedaAdjunction_homEquiv_app.{0, 0, u, 0, u + 1}
    (SimplexCategory × SimplexCategory) _ (SSet.{u}) _ kernel.{u} _
    presheafLeft.{u}
    ((uliftYoneda.{u} (C := SimplexCategory × SimplexCategory)).leftKanExtensionUnit kernel.{u})
    _ P Q f (op c) x
  exact congrArg ULift.down h

set_option backward.isDefEq.respectTransparency false in
/-- The actual raw unit retains every original product-site point generator. -/
theorem presheafAdjunction_unit_app
    (P : (SimplexCategory × SimplexCategory)ᵒᵖ ⥤ Type u)
    (c : SimplexCategory × SimplexCategory) (x : P.obj (op c)) :
    ULift.down ((presheafAdjunction.unit.app P).app (op c) x) =
      presheafRepresentableIso.inv.app c ≫ presheafLeft.map (uliftYonedaEquiv.symm x) := by
  let : presheafLeft.{u}.IsLeftKanExtension
      ((uliftYoneda.{u} (C := SimplexCategory × SimplexCategory)).leftKanExtensionUnit
          kernel.{u}) := by
    change
        ((uliftYoneda.{u} (C := SimplexCategory × SimplexCategory)).leftKanExtension
          kernel.{u}).IsLeftKanExtension
      ((uliftYoneda.{u} (C := SimplexCategory × SimplexCategory)).leftKanExtensionUnit kernel.{u})
    infer_instance
  have h := @Presheaf.uliftYonedaAdjunction_unit_app_app.{0, 0, u, 0, u + 1}
    (SimplexCategory × SimplexCategory) _ (SSet.{u}) _ kernel.{u} _
    presheafLeft.{u}
    ((uliftYoneda.{u} (C := SimplexCategory × SimplexCategory)).leftKanExtensionUnit kernel.{u})
    _ P (op c) x
  exact congrArg ULift.down h

private theorem underlying_comp {X Y Z : SimplicialSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := forget.map_comp f g

private theorem carrier_unit_map_app (X : SimplicialSpace.{u})
    {P : (SimplexCategory × SimplexCategory)ᵒᵖ ⥤ Type u}
    (f : toPresheaf.obj X ⟶ P) (c : SimplexCategory × SimplexCategory)
    (x : (toPresheaf.obj X).obj (op c)) :
    (((equivalencePresheaf.unit.app X ≫ equivalencePresheaf.inverse.map f).hom.app
      (op c.1)).app (op c.2)) x = f.app (op c) x := by
  rcases c with ⟨n, m⟩
  simp [Equivalence.unit, Equivalence.congrLeft,
    Equivalence.funInvIdAssoc, toPresheaf, equivalencePresheaf,
    equivalenceSimplicialObject, ofSimplicialObject, forget, underlying_comp,
    Functor.currying, Functor.curry, Functor.curryObj,
    Functor.whiskerLeft, prodOpEquiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The designated total unit has the same original product-site generator in each bidegree. -/
theorem adjunction_unit_app (X : SimplicialSpace.{u})
    (c : SimplexCategory × SimplexCategory) (x : (toPresheaf.obj X).obj (op c)) :
    ULift.down (((adjunction.unit.app X).hom.app (op c.1)).app (op c.2) x) =
      presheafRepresentableIso.inv.app c ≫ presheafLeft.map (uliftYonedaEquiv.symm x) := by
  simp only [adjunction, Adjunction.comp_unit_app]
  simp only [JoyalSSet.equivalenceSSet, Equivalence.toAdjunction,
    Equivalence.unit,
    JoyalSSet.ofSSet, JoyalSSet.forget, CategoryTheory.Functor.comp_obj]
  exact (congrArg ULift.down
    (carrier_unit_map_app X (presheafAdjunction.unit.app (toPresheaf.obj X)) c x)).trans
      (presheafAdjunction_unit_app (toPresheaf.obj X) c x)

/-- The original box map evaluates by both original site operators on the supplied point. -/
theorem simplexMap_app (X : SimplicialSpace.{u}) (c : SimplexCategory × SimplexCategory)
    (x : (toPresheaf.obj X).obj (op c)) (n m : SimplexCategoryᵒᵖ)
    (a : n.unop ⟶ c.1) (b : m.unop ⟶ c.2) :
    (((simplexMap X c x).hom.app n).app m) (ULift.up a, ULift.up b) =
      (toPresheaf.obj X).map (Quiver.Hom.op (show (n.unop, m.unop) ⟶ c from (a, b))) x := by
  have h := congrArg
    (fun k : (toPresheaf.obj (representable.obj c)) ⟶ toPresheaf.obj X =>
      k.app (op (n.unop, m.unop)) (ULift.up a, ULift.up b))
    (simplexMap_toPresheaf X c x)
  exact h

/-- The actual designated left map retains the native extension of the original presheaf map. -/
theorem left_map_forget {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    JoyalSSet.forget.map (left.map f) = presheafLeft.map (toPresheaf.map f) := rfl

/-- The inverse actual representable comparison retains the original native extension unit. -/
theorem representableIso_inv (c : SimplexCategory × SimplexCategory) :
    JoyalSSet.forget.map (representableIso.{u}.inv.app c) =
      presheafRepresentableIso.inv.app c ≫
          presheafLeft.map (representablePresheafIso.inv.app c) := rfl

/-- The original left box generator is the same actual product-site extension generator. -/
theorem left_generator (X : SimplicialSpace.{u}) (c : SimplexCategory × SimplexCategory)
    (x : (toPresheaf.obj X).obj (op c)) :
    JoyalSSet.forget.map (representableIso.inv.app c ≫ left.map (simplexMap X c x)) =
      presheafRepresentableIso.inv.app c ≫ presheafLeft.map (uliftYonedaEquiv.symm x) := by
  change (presheafRepresentableIso.inv.app c ≫
      presheafLeft.map (representablePresheafIso.inv.app c)) ≫
      presheafLeft.map (toPresheaf.map (simplexMap X c x)) = _
  rw [simplexMap_toPresheaf, Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [← Category.assoc, CategoryTheory.Iso.inv_hom_id_app, Category.id_comp]

/-- The actual unit in each bidegree is the original map from that box representable. -/
theorem adjunction_unit_generator (X : SimplicialSpace.{u})
    (c : SimplexCategory × SimplexCategory) (x : (toPresheaf.obj X).obj (op c)) :
    ULift.down (((adjunction.unit.app X).hom.app (op c.1)).app (op c.2) x) =
      JoyalSSet.forget.map (representableIso.inv.app c ≫ left.map (simplexMap X c x)) :=
  (adjunction_unit_app X c x).trans (left_generator X c x).symm

/-- The actual counit evaluates every supplied original kernel map at its original box generator. -/
theorem adjunction_counit_generator (Q : JoyalSSet.{u})
    (c : SimplexCategory × SimplexCategory) (h : kernel.obj c ⟶ Q.toSSet) :
    JoyalSSet.forget.map (representableIso.inv.app c ≫
      left.map (simplexMap (right.obj Q) c (ULift.up h)) ≫ adjunction.counit.app Q) = h := by
  rcases c with ⟨n, m⟩
  have hn := congrArg (fun k : right.obj Q ⟶ right.obj Q => forget.map k)
    (adjunction_right_triangle Q)
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at hn
  have ht := congrArg
    (fun k : (right.obj Q).diagram ⟶ (right.obj Q).diagram =>
      ULift.down ((k.app (op n)).app (op m) (ULift.up h))) hn
  let unitPoint : ULift.{0} (kernel.obj (n, m) ⟶ (left.obj (right.obj Q)).toSSet) :=
    (((adjunction.unit.app (right.obj Q)).hom.app (op n)).app (op m)) (ULift.up h)
  change ULift.down ((((right.map (adjunction.counit.app Q)).hom.app (op n)).app (op m))
    unitPoint) = h at ht
  have hr := congrArg ULift.down
    (right_map_app (adjunction.counit.app Q) (op n) (op m) unitPoint)
  have hgen : unitPoint.down ≫ JoyalSSet.forget.map (adjunction.counit.app Q) = h :=
    hr.symm.trans ht
  dsimp only [unitPoint] at hgen
  have hu := adjunction_unit_generator (right.obj Q) (n, m) (ULift.up h)
  have hcomp := congrArg
    (fun a => a ≫ JoyalSSet.forget.map (adjunction.counit.app Q)) hu
  rw [← Category.assoc, CategoryTheory.Functor.map_comp]
  exact hcomp.symm.trans hgen

end SimplicialSpace.TotalSpace
