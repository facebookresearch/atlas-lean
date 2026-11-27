/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomEqualityTransport

/-!
# Full original Hom squares at actual prescribed endpoints

The SAME whole original enriched square and its true endpoint equations
give the complete coefficient square. All original maps and inverses
of equality transports are retained, in the original coefficient universe.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.SimplicialEnrichment

/-- A genuine whole original enriched square retains its SAME full Hom square at every
actual endpoint. -/
theorem originalHomSquare {A B C D : Carrier.{u}} (E : A ⟶ B) (F : A ⟶ C)
    (G : B ⟶ D) (H : C ⟶ D) (sq : E ≫ G = F ≫ H) (a b : A)
    {x₀ x₁ : B} {y₀ y₁ : C} {z₀ z₁ : D}
    (hx₀ : E.obj a = x₀) (hx₁ : E.obj b = x₁) (hy₀ : F.obj a = y₀) (hy₁ : F.obj b = y₁)
    (hg₀ : G.obj x₀ = z₀) (hg₁ : G.obj x₁ = z₁) (hh₀ : H.obj y₀ = z₀) (hh₁ : H.obj y₁ = z₁) :
    E.map a b ≫ eqToHom (congrArg₂ (fun x y : B => x ⟶[SSet.{u}] y) hx₀ hx₁) ≫
      G.map x₀ x₁ ≫ eqToHom (congrArg₂ (fun x y : D => x ⟶[SSet.{u}] y) hg₀ hg₁) =
    F.map a b ≫ eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y) hy₀ hy₁) ≫
      H.map y₀ y₁ ≫ eqToHom (congrArg₂ (fun x y : D => x ⟶[SSet.{u}] y) hh₀ hh₁) := by
  subst x₀
  subst x₁
  subst y₀
  subst y₁
  subst z₀
  subst z₁
  have h := EnrichedFunctor.homMap_transport_of_eq sq a b
  let tc := congrArg₂ (fun x y : D => x ⟶[SSet.{u}] y)
    (congrArg (fun K : A ⟶ D => K.obj a) sq) (congrArg (fun K : A ⟶ D => K.obj b) sq)
  let th := congrArg₂ (fun x y : D => x ⟶[SSet.{u}] y) hh₀ hh₁
  change (E.map a b ≫ G.map (E.obj a) (E.obj b)) ≫ eqToHom tc = F.map a b ≫
    H.map (F.obj a) (F.obj b) at h
  have ht := congrArg (fun f : (a ⟶[SSet.{u}] b) ⟶ (H.obj (F.obj a) ⟶[SSet.{u}] H.obj
    (F.obj b)) => f ≫ eqToHom th) h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (Category.comp_id _).symm.trans
    ((congrArg (fun f => (E.map a b ≫ G.map (E.obj a) (E.obj b)) ≫ f)
      (eqToHom_refl _ (tc.trans th))).symm.trans
        ((congrArg (fun f => (E.map a b ≫ G.map (E.obj a) (E.obj b)) ≫ f)
          (eqToHom_trans tc th).symm).trans
            ((Category.assoc _ _ _).symm.trans (ht.trans (Category.assoc _ _ _)))))

end CategoryTheory.SimplicialEnrichment
