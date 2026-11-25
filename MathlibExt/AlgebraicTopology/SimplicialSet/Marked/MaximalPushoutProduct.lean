/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianMonoidal
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MaximalColimits
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductAssociativity
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterLeibniz
import Mathlib.CategoryTheory.Monoidal.PushoutProduct

/-!
# Whole original scalar and marked pushout-product comparisons

The native marked product structure uses the literal original products.
Maximal marking preserves the actual scalar pushout, and the original
max-product isomorphisms compare its whole corner map with the marked
corner. The existing marked parameter corner is compared to the same
canonical Leibniz corner through its actual pushout point. No lifting or
weak-class outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked

attribute [local instance] cartesianMonoidalCategory monoidalClosed
local instance maximalCornerPreservesColimits : PreservesColimitsOfSize.{u, u} maximal.{u} := maximal_preservesColimits

/-- Maximal marking sends the same original scalar pushout point and side maps to the native marked product square. -/
def maximalPushoutSquare {A D K L : SSet.{u}} (a : A ⟶ D) (b : K ⟶ L)
    (s : (curriedTensor SSet.{u}).PushoutObjObj a b) :
    (curriedTensor Marked.{u}).PushoutObjObj (maximal.map a) (maximal.map b) where
  pt := max s.pt
  inl := (maxProductIso D K).hom ≫ maximal.map s.inl
  inr := (maxProductIso A L).hom ≫ maximal.map s.inr
  isPushout := (maximal.map_isPushout s.isPushout).of_iso
    (maxProductIso A K).symm (maxProductIso D K).symm
    (maxProductIso A L).symm (Iso.refl _)
    (Hom.ext rfl) (Hom.ext rfl) (Hom.ext rfl) (Hom.ext rfl)
  ι := maximal.map s.ι ≫ (maxProductIso D L).inv
  inl_ι := by
    let e : prod (max D) (max K) ≅ max (D ⊗ K) := maxProductIso D K
    let q : prod (max D) (max L) ≅ max (D ⊗ L) := maxProductIso D L
    let h₁ : max (D ⊗ K) ⟶ max s.pt := maximal.map s.inl
    let h₂ : max s.pt ⟶ max (D ⊗ L) := maximal.map s.ι
    let g : prod (max D) (max K) ⟶ prod (max D) (max L) := prodMap (𝟙 (max D)) (maximal.map b)
    have hcomp : h₁ ≫ h₂ = maximal.map (s.inl ≫ s.ι) := (maximal.map_comp _ _).symm
    change (e.hom ≫ h₁) ≫ (h₂ ≫ q.inv) = g
    calc
      _ = e.hom ≫ (h₁ ≫ h₂) ≫ q.inv := by simp only [Category.assoc]
      _ = e.hom ≫ maximal.map (s.inl ≫ s.ι) ≫ q.inv := congrArg (fun z => e.hom ≫ z ≫ q.inv) hcomp
      _ = e.hom ≫ maximal.map (((curriedTensor SSet).obj D).map b) ≫ q.inv :=
        congrArg (fun z => e.hom ≫ maximal.map z ≫ q.inv) s.inl_ι
      _ = g := Hom.ext rfl
  inr_ι := by
    let e : prod (max A) (max L) ≅ max (A ⊗ L) := maxProductIso A L
    let q : prod (max D) (max L) ≅ max (D ⊗ L) := maxProductIso D L
    let h₁ : max (A ⊗ L) ⟶ max s.pt := maximal.map s.inr
    let h₂ : max s.pt ⟶ max (D ⊗ L) := maximal.map s.ι
    let g : prod (max A) (max L) ⟶ prod (max D) (max L) := prodMap (maximal.map a) (𝟙 (max L))
    have hcomp : h₁ ≫ h₂ = maximal.map (s.inr ≫ s.ι) := (maximal.map_comp _ _).symm
    change (e.hom ≫ h₁) ≫ (h₂ ≫ q.inv) = g
    calc
      _ = e.hom ≫ (h₁ ≫ h₂) ≫ q.inv := by simp only [Category.assoc]
      _ = e.hom ≫ maximal.map (s.inr ≫ s.ι) ≫ q.inv := congrArg (fun z => e.hom ≫ z ≫ q.inv) hcomp
      _ = e.hom ≫ maximal.map (((curriedTensor SSet).map a).app L) ≫ q.inv :=
        congrArg (fun z => e.hom ≫ maximal.map z ≫ q.inv) s.inr_ι
      _ = g := Hom.ext rfl

/-- The whole original maximally marked scalar corner agrees with the canonical marked corner through the
  actual pushout and max-product maps. -/
def maximalPushoutProductIso {A D K L : SSet.{u}} (a : A ⟶ D) (b : K ⟶ L) :
    Arrow.mk (maximal.map ((Arrow.mk a □ Arrow.mk b).hom)) ≅
      Arrow.mk (maximal.map a) □ Arrow.mk (maximal.map b) := by
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) a b
  let m := maximalPushoutSquare a b s
  let t := Functor.PushoutObjObj.ofHasPushout (curriedTensor Marked.{u}) (maximal.map a) (maximal.map b)
  let e : Arrow.mk (maximal.map s.ι) ≅ Arrow.mk m.ι :=
    Arrow.isoMk (Iso.refl _) (maxProductIso D L).symm rfl
  exact e ≪≫ Functor.PushoutObjObj.ι_iso_of_iso_right
    (f₁ := Arrow.mk (maximal.map a)) (f₂ := Arrow.mk (maximal.map b))
    (f₂' := Arrow.mk (maximal.map b)) m t (Iso.refl (Arrow.mk (maximal.map b)))

/-- The original marked parameter point and maps form the same canonical marked product square with its
  sides in the corresponding order. -/
def parameterCanonicalSquare {A D : SSet.{u}} {X Y : Marked.{u}} (a : A ⟶ D) (f : X ⟶ Y) :
    (curriedTensor Marked.{u}).PushoutObjObj (maximal.map a) f := by
  let s := parameterPushout a f
  refine
    { pt := s.pt
      inl := s.inr
      inr := s.inl
      isPushout := ?_
      ι := s.ι
      inl_ι := ?_
      inr_ι := ?_ }
  · change IsPushout (prodMap (maximal.map a) (𝟙 X)) (prodMap (𝟙 (max A)) f) s.inr s.inl
    exact s.isPushout.flip
  · change s.inr ≫ s.ι = prodMap (𝟙 (max D)) f
    exact s.inr_ι
  · change s.inl ≫ s.ι = prodMap (maximal.map a) (𝟙 Y)
    exact s.inl_ι

/-- The original complete parameter corner is the canonical marked Leibniz corner through the actual native
  pushout-point isomorphism. -/
def parameterPushoutProductCanonicalIso {A D : SSet.{u}} {X Y : Marked.{u}} (a : A ⟶ D) (f : X ⟶ Y) :
    Arrow.mk (parameterPushoutProduct a f) ≅ Arrow.mk (maximal.map a) □ Arrow.mk f := by
  let s := parameterCanonicalSquare a f
  let t := Functor.PushoutObjObj.ofHasPushout (curriedTensor Marked.{u}) (maximal.map a) f
  exact Functor.PushoutObjObj.ι_iso_of_iso_right
    (f₁ := Arrow.mk (maximal.map a)) (f₂ := Arrow.mk f) (f₂' := Arrow.mk f) s t (Iso.refl (Arrow.mk f))

end SSet.Marked

namespace SSet.Marked

attribute [local instance] cartesianMonoidalCategory monoidalClosed
open CategoryTheory Limits MonoidalCategory

/-- The native marked-parameter comparison keeps its complete original target map equal to the identity. -/
@[simp]
theorem parameterPushoutProductCanonicalIso_hom_right {A D : SSet.{u}} {X Y : Marked.{u}}
    (a : A ⟶ D) (f : X ⟶ Y) :
    (parameterPushoutProductCanonicalIso a f).hom.right = 𝟙 (prod (max D) Y) := by
  change ((curriedTensor Marked).obj (max D)).map (𝟙 Y) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

/-- The scalar-to-marked corner comparison keeps precisely the original inverse max-product map on its target. -/
@[simp]
theorem maximalPushoutProductIso_hom_right {A D K L : SSet.{u}} (a : A ⟶ D) (b : K ⟶ L) :
    (maximalPushoutProductIso a b).hom.right = (maxProductIso D L).inv := by
  change (maxProductIso D L).inv ≫ ((curriedTensor Marked).obj (max D)).map (𝟙 (max L)) = _
  rw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

end SSet.Marked
