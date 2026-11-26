/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InnerMapping
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Enriched constant extension and terminal-site evaluation

Constant presheaves are left adjoint to evaluation at a terminal site object.
The enriched comparison uses the original inner end: its forward map is the
actual end projection, and its inverse extends along the original arrows to
the terminal object. No model structure or fibrancy hypothesis is involved.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

namespace SimplicialPresheaf.ConstantEvaluation

variable {D : Type w} [Category.{v} D]

/-- Constant extension retains the whole scalar simplicial set. -/
abbrev constant : SSet.{u} ⥤ SimplicialPresheaf.{u} D :=
  Functor.const Dᵒᵖ

/-- Evaluation at the original site object, with its one whole opposite. -/
abbrev evaluation (z : D) : SimplicialPresheaf.{u} D ⥤ SSet.{u} :=
  (CategoryTheory.evaluation Dᵒᵖ SSet.{u}).obj (op z)

/-- Reuse the native constant/limit adjunction and its initial-object projection. -/
def adjunction {z : D} (hz : IsTerminal z) :
    constant (D := D) ⊣ evaluation z := by
  let _ : HasInitial Dᵒᵖ := IsInitial.hasInitial hz.op
  let _ : HasLimitsOfShape Dᵒᵖ SSet.{u} := ⟨fun _ => inferInstance⟩
  let e : (lim : (Dᵒᵖ ⥤ SSet.{u}) ⥤ SSet.{u}) ≅ evaluation z :=
    NatIso.ofComponents (fun X => by
      letI : IsIso (limit.π X (op z)) := isIso_π_of_isInitial hz.op X
      exact asIso (limit.π X (op z))) (by
        intro X Y f
        exact limit.map_π f (op z))
  exact (constLimAdj (J := Dᵒᵖ) (C := SSet.{u})).ofNatIsoRight e

/-- The ordinary adjunction sends the original natural map to its terminal component. -/
theorem adjunction_homEquiv {z : D} (hz : IsTerminal z) (K : SSet.{u})
    (X : SimplicialPresheaf.{u} D) (f : constant.obj K ⟶ X) :
    (adjunction hz).homEquiv K X f = f.app (op z) := by
  let _ : HasInitial Dᵒᵖ := IsInitial.hasInitial hz.op
  let _ : HasLimitsOfShape Dᵒᵖ SSet.{u} := ⟨fun _ => inferInstance⟩
  simp only [adjunction, Adjunction.homEquiv_ofNatIsoRight_apply]
  simp only [constLimAdj, Adjunction.mk'_homEquiv]
  change limit.lift X ⟨K, f⟩ ≫ limit.π X (op z) = f.app (op z)
  exact limit.lift_π _ _

/-- The inverse ordinary transpose uses the original operator to the terminal object. -/
theorem adjunction_homEquiv_symm_app {z : D} (hz : IsTerminal z) (K : SSet.{u})
    (X : SimplicialPresheaf.{u} D) (g : K ⟶ X.obj (op z)) (a : Dᵒᵖ) :
    (((adjunction hz).homEquiv K X).symm g).app a =
      g ≫ X.map (hz.from a.unop).op := by
  let f := ((adjunction hz).homEquiv K X).symm g
  have h0 : f.app (op z) = g :=
    (adjunction_homEquiv hz K X f).symm.trans
      (((adjunction hz).homEquiv K X).apply_symm_apply g)
  have h := f.naturality (hz.from a.unop).op
  change (𝟙 K) ≫ f.app a = f.app (op z) ≫ X.map (hz.from a.unop).op at h
  rw [Category.id_comp, h0] at h
  exact h

/-- Tensoring a constant scalar is the same original scalar tensor at every site value. -/
def constantTensorIso (K : SSet.{u}) :
    tensorLeft K ⋙ constant (D := D) ≅ scalarTensor.obj (constant.obj K) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    ext a n x
    rfl)

variable [Small.{u} D] [LocallySmall.{u} D]

/-- Extend a scalar Hom at the terminal value using the existing tensor/end transpose. -/
def lift {z : D} (hz : IsTerminal z) (K : SSet.{u}) (X : SimplicialPresheaf.{u} D) :
    (ihom K).obj (X.obj (op z)) ⟶ innerHom (constant.obj K) X :=
  scalarTensorHomEquiv (constant.obj K) ((ihom K).obj (X.obj (op z))) X
    ((constantTensorIso (D := D) K).inv.app ((ihom K).obj (X.obj (op z))) ≫
      ((adjunction hz).homEquiv (K ⊗ (ihom K).obj (X.obj (op z))) X).symm
        ((ihom.ev K).app (X.obj (op z))))

/-- Every projection of the lift is postcomposition by the same original site operator. -/
theorem lift_projection {z : D} (hz : IsTerminal z) (K : SSet.{u})
    (X : SimplicialPresheaf.{u} D) (a : Dᵒᵖ) :
    lift hz K X ≫ innerHomπ (constant.obj K) X a =
      (ihom K).map (X.map (hz.from a.unop).op) := by
  unfold lift
  rw [scalarTensorHomEquiv_π]
  rw [NatTrans.comp_app, adjunction_homEquiv_symm_app]
  change curry (𝟙 _ ≫ (ihom.ev K).app (X.obj (op z)) ≫
    X.map (hz.from a.unop).op) = _
  rw [Category.id_comp, curry_natural_right]
  rw [← uncurry_id_eq_ev, curry_uncurry, Category.id_comp]

/-- The constant-source inner end is the scalar Hom into the terminal value. -/
def iso {z : D} (hz : IsTerminal z) (K : SSet.{u}) (X : SimplicialPresheaf.{u} D) :
    innerHom (constant.obj K) X ≅ (ihom K).obj (X.obj (op z)) where
  hom := innerHomπ (constant.obj K) X (op z)
  inv := lift hz K X
  hom_inv_id := by
    apply innerHom_ext
    intro a
    rw [Category.assoc, lift_projection]
    have h := innerHom_condition (constant.obj K) X (hz.from a.unop).op
    change innerHomπ (constant.obj K) X (op z) ≫
        (ihom K).map (X.map (hz.from a.unop).op) =
      innerHomπ (constant.obj K) X a ≫ (pre (𝟙 K)).app (X.obj a) at h
    have hid : (pre (𝟙 K)).app (X.obj a) = 𝟙 ((ihom K).obj (X.obj a)) :=
      NatTrans.congr_app (pre_id K) (X.obj a)
    have hc : innerHomπ (constant.obj K) X a ≫ (pre (𝟙 K)).app (X.obj a) =
        innerHomπ (constant.obj K) X a :=
      (congrArg (fun f : (ihom K).obj (X.obj a) ⟶ (ihom K).obj (X.obj a) =>
        innerHomπ (constant.obj K) X a ≫ f) hid).trans (Category.comp_id _)
    exact (h.trans hc).trans (Category.id_comp _).symm
  inv_hom_id := by
    rw [lift_projection]
    have h0 : hz.from z = 𝟙 z := hz.hom_ext _ _
    rw [h0, op_id, X.map_id, (ihom K).map_id]

/-- The forward comparison is literally the original terminal-site end projection. -/
theorem iso_hom {z : D} (hz : IsTerminal z) (K : SSet.{u})
    (X : SimplicialPresheaf.{u} D) :
    (iso hz K X).hom = innerHomπ (constant.obj K) X (op z) :=
  rfl

/-- The inverse comparison keeps every original site map. -/
theorem iso_inv_projection {z : D} (hz : IsTerminal z) (K : SSet.{u})
    (X : SimplicialPresheaf.{u} D) (a : Dᵒᵖ) :
    (iso hz K X).inv ≫ innerHomπ (constant.obj K) X a =
      (ihom K).map (X.map (hz.from a.unop).op) :=
  lift_projection hz K X a

/-- Scalar precomposition commutes with the same terminal-site comparison. -/
theorem iso_source {z : D} (hz : IsTerminal z) {K L : SSet.{u}} (k : K ⟶ L)
    (X : SimplicialPresheaf.{u} D) :
    innerHomPre (constant.map k) X ≫ (iso hz K X).hom =
      (iso hz L X).hom ≫ (pre k).app (X.obj (op z)) := by
  rw [iso_hom, iso_hom, innerHomPre_π]
  rfl

/-- Target postcomposition acts through the scalar internal-Hom functor. -/
theorem iso_target {z : D} (hz : IsTerminal z) (K : SSet.{u})
    {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y) :
    innerHomPost (constant.obj K) f ≫ (iso hz K Y).hom =
      (iso hz K X).hom ≫ (ihom K).map (f.app (op z)) := by
  rw [iso_hom, iso_hom, innerHomPost_π]
  rfl

/-- The terminal-site comparison is a natural isomorphism in the presheaf target. -/
def natIso {z : D} (hz : IsTerminal z) (K : SSet.{u}) :
    innerHomFunctor.obj (op (constant.obj K)) ≅ evaluation z ⋙ ihom K :=
  NatIso.ofComponents (iso hz K) (fun f => iso_target hz K f)

end SimplicialPresheaf.ConstantEvaluation
