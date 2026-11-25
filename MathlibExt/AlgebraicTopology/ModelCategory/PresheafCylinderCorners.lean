/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorialCylinder
public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Images
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# The unions defined by exact-cylinder corners

For a monomorphism of presheaves, the endpoint and boundary corners of an
exact cylinder are monomorphisms. The specified pushout domains are
isomorphic, over the target cylinder, to the corresponding unions of
subobjects. The boundary pullback is assembled from the two endpoint
pullbacks using universality of binary coproducts in presheaves.

This is the presheaf consequence in Cisinski, Higher Categories and
Homotopical Algebra, Remark 2.4.9, July 30, 2026 version, printed page 53.
The index category, value universe and exactness colimit size are independent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u v'

namespace HomotopicalAlgebra.Precylinder

private lemma mk_pushoutDesc_eq_sup {C : Type v} [Category.{v'} C]
    [HasImages C] [HasBinaryCoproducts C] {A B K Y : C}
    (f : K ⟶ A) (g : K ⟶ B) [HasPushout f g]
    (a : A ⟶ Y) (b : B ⟶ Y) [Mono a] [Mono b]
    (h : f ≫ a = g ≫ b) [Mono (pushout.desc a b h)] :
    Subobject.mk (pushout.desc a b h) = Subobject.mk b ⊔ Subobject.mk a := by
  let S : Subobject Y := Subobject.mk b ⊔ Subobject.mk a
  let a' : A ⟶ (S : C) := Subobject.ofMkLE a S le_sup_right
  let b' : B ⟶ (S : C) := Subobject.ofMkLE b S le_sup_left
  have h' : f ≫ a' = g ≫ b' := by
    apply (cancel_mono S.arrow).1
    simpa only [a', b', Category.assoc, Subobject.ofMkLE_arrow] using h
  have hc : pushout.desc a' b' h' ≫ S.arrow = pushout.desc a b h := by
    apply pushout.hom_ext <;> simp only [pushout.inl_desc_assoc, pushout.inr_desc_assoc,
      pushout.inl_desc, pushout.inr_desc, a', b', Subobject.ofMkLE_arrow]
  apply le_antisymm
  · exact Subobject.mk_le_of_comm (pushout.desc a' b' h') hc
  · exact sup_le (Subobject.mk_le_mk_of_comm (pushout.inr f g) (pushout.inr_desc a b h))
      (Subobject.mk_le_mk_of_comm (pushout.inl f g) (pushout.inl_desc a b h))

section Presheaves

variable {A : Type v} [Category.{v'} A]
variable (P : Precylinder (𝟭 (Aᵒᵖ ⥤ Type u))) [P.IsExact.{w}]
variable {X Y : Aᵒᵖ ⥤ Type u} (i : X ⟶ Y) [Mono i]

/-- The boundary naturality square is a pullback. Both endpoint pullbacks
are used, and the binary coproduct is universal in presheaves. -/
lemma boundary_isPullback :
    IsPullback (coprod.map i i) (P.app X).i (P.app Y).i (P.I.map i) := by
  let a : Cofan (pairFunction Y Y) := BinaryCofan.mk coprod.inl coprod.inr
  let d : Cofan (pairFunction X X) := BinaryCofan.mk coprod.inl coprod.inr
  let f : ∀ j, pairFunction Y Y j ⟶ P.I.obj Y
    | .left => (P.app Y).i₀
    | .right => (P.app Y).i₁
  let q₁ : ∀ j, pairFunction X X j ⟶ P.I.obj X
    | .left => (P.app X).i₀
    | .right => (P.app X).i₁
  let q₂ : ∀ j, pairFunction X X j ⟶ pairFunction Y Y j
    | .left => i
    | .right => i
  have ha : IsColimit a := coprodIsCoprod Y Y
  have hd : IsColimit d := coprodIsCoprod X X
  have hq : ∀ j, IsPullback (q₁ j) (q₂ j) (P.I.map i) (f j) := by
    intro j
    cases j
    · exact (IsExact.endpoint_isPullback (P := P) i 0).flip
    · exact (IsExact.endpoint_isPullback (P := P) i 1).flip
  have hu : ∀ j, a.inj j ≫ (P.app Y).i = f j := by
    intro j
    cases j <;> simp [a, Cofan.inj, f]
  have h₁ : Cofan.IsColimit.desc hd q₁ = (P.app X).i := by
    apply coprod.hom_ext
    · change d.inj .left ≫ _ = coprod.inl ≫ (P.app X).i
      rw [Cofan.IsColimit.fac]
      exact (inl_i (P.app X)).symm
    · change d.inj .right ≫ _ = coprod.inr ≫ (P.app X).i
      rw [Cofan.IsColimit.fac]
      exact (inr_i (P.app X)).symm
  have h₂ : Cofan.IsColimit.desc hd (fun j ↦ q₂ j ≫ a.inj j) = coprod.map i i := by
    apply coprod.hom_ext
    · change d.inj .left ≫ _ = coprod.inl ≫ coprod.map i i
      rw [Cofan.IsColimit.fac]
      exact (coprod.inl_map i i).symm
    · change d.inj .right ≫ _ = coprod.inr ≫ coprod.map i i
      rw [Cofan.IsColimit.fac]
      exact (coprod.inr_map i i).symm
  have hp := (FinitaryPreExtensive.universal' a ha).isPullback_of_isColimit_left
    f (P.app Y).i (P.I.map i) q₁ q₂ hq hd hu
  rw [h₁, h₂] at hp
  exact hp.flip

/-- The actual endpoint corner map is monic. -/
instance mono_endpointCorner (ε : Fin 2) : Mono (P.endpointCorner i ε) := by
  let hp := IsPushout.of_hasPushout i ((P.app X).endpoint ε)
  let hq := IsExact.endpoint_isPullback (P := P) i ε
  have he : hp.desc ((P.app Y).endpoint ε) (P.I.map i) hq.w =
      P.endpointCorner i ε := by
    apply hp.hom_ext <;> simp
  rw [← he]
  exact hp.desc_mono_of_isPullback hq

/-- The actual boundary corner map is monic. -/
instance mono_boundaryCorner : Mono (P.boundaryCorner i) := by
  let hp := IsPushout.of_hasPushout (coprod.map i i) (P.app X).i
  let hq := P.boundary_isPullback i
  have he : hp.desc (P.app Y).i (P.I.map i) hq.w = P.boundaryCorner i := by
    apply hp.hom_ext <;> simp
  rw [← he]
  exact hp.desc_mono_of_isPullback hq

/-- The endpoint corner represents the union of the cylinder on the source
and the chosen endpoint on the target. -/
lemma mk_endpointCorner (ε : Fin 2) :
    Subobject.mk (P.endpointCorner i ε) =
      Subobject.mk (P.I.map i) ⊔ Subobject.mk ((P.app Y).endpoint ε) := by
  have : Mono (pushout.desc ((P.app Y).endpoint ε) (P.I.map i)
      (P.endpoint_naturality i ε)) := by
    change Mono (P.endpointCorner i ε)
    infer_instance
  exact mk_pushoutDesc_eq_sup i ((P.app X).endpoint ε) ((P.app Y).endpoint ε)
    (P.I.map i) (P.endpoint_naturality i ε)

/-- The boundary corner represents the union of the cylinder on the source
and both endpoints on the target. -/
lemma mk_boundaryCorner :
    Subobject.mk (P.boundaryCorner i) =
      Subobject.mk (P.I.map i) ⊔ Subobject.mk (P.app Y).i := by
  have : Mono (pushout.desc (P.app Y).i (P.I.map i) (P.boundary_naturality i)) := by
    change Mono (P.boundaryCorner i)
    infer_instance
  exact mk_pushoutDesc_eq_sup (coprod.map i i) (P.app X).i (P.app Y).i
    (P.I.map i) (P.boundary_naturality i)

/-- Identify the specified endpoint pushout domain with its union subobject. -/
def endpointCornerUnionIso (ε : Fin 2) :
    pushout i ((P.app X).endpoint ε) ≅
      ((Subobject.mk (P.I.map i) ⊔ Subobject.mk ((P.app Y).endpoint ε) :
        Subobject (P.I.obj Y)) : Aᵒᵖ ⥤ Type u) :=
  Subobject.isoOfMkEq (P.endpointCorner i ε) _ (P.mk_endpointCorner i ε)

@[reassoc (attr := simp)]
lemma endpointCornerUnionIso_hom_arrow (ε : Fin 2) :
    (P.endpointCornerUnionIso i ε).hom ≫
      (Subobject.mk (P.I.map i) ⊔ Subobject.mk ((P.app Y).endpoint ε)).arrow =
    P.endpointCorner i ε := by
  exact Subobject.ofMkLE_arrow (P.mk_endpointCorner i ε).le

/-- Identify the specified boundary pushout domain with its union subobject. -/
def boundaryCornerUnionIso :
    pushout (coprod.map i i) (P.app X).i ≅
      ((Subobject.mk (P.I.map i) ⊔ Subobject.mk (P.app Y).i : Subobject (P.I.obj Y)) :
        Aᵒᵖ ⥤ Type u) :=
  Subobject.isoOfMkEq (P.boundaryCorner i) _ (P.mk_boundaryCorner i)

@[reassoc (attr := simp)]
lemma boundaryCornerUnionIso_hom_arrow :
    (P.boundaryCornerUnionIso i).hom ≫
      (Subobject.mk (P.I.map i) ⊔ Subobject.mk (P.app Y).i).arrow =
    P.boundaryCorner i := by
  exact Subobject.ofMkLE_arrow (P.mk_boundaryCorner i).le

end Presheaves

end HomotopicalAlgebra.Precylinder
