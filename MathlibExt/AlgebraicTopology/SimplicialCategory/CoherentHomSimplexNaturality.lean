/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomSimplexOperators
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentPathEndpointTransport

/-!
# Whole original enriched-simplex naturality of Hom comparisons

Every right-join simplex operator acts on the original enriched simplex
built from the same Hom simplex. The complete Hom equality retains its
specified source and target, not only its vertices or components.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomSimplexNaturality
open SimplicialEnrichment HomSimplex HomSimplexOperators PathMaximumOperators PathEndpointTransport
variable {C : Carrier.{u}} {n m : ℕ} (x y : C)

private theorem whole_ext {A B : Carrier.{u}} (F G : A ⟶ B)
    (ho : ∀ a, F.obj a = G.obj a) (hm : ∀ a b, F.map a b ≍ G.map a b) : F = G := by
  refine EnrichedFunctor.ext SSet.{u} ho ?_
  intro a b
  exact eq_of_heq ((comp_eqToHom_heq _ _).trans (hm a b))

/-- Actual Hom maps are natural for the exact equality of two original endpoint pairs. -/
theorem homMap_reindex (τ : (Δ[m] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y))
    {a a' b b' : Fin (m + 2)} (ha : a = a') (hb : b = b') :
    homMap x y τ a b ≫ eqToHom (congrArg₂ (fun a b : Fin (m + 2) =>
      (HomSimplex.object x y a ⟶[SSet.{u}] HomSimplex.object x y b)) ha hb) =
      eqToHom (congrArg₂ (fun a b : Fin (m + 2) => nerve (SimplicialThickening.Path (ULift.up.{u} a)
        (ULift.up.{u} b))) ha hb) ≫
        homMap x y τ a' b' := by
  subst a'
  subst b'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- The actual Hom comparison is natural on the original front-to-last whole Hom under the
right join operator. -/
theorem last_hom_operator (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (τ : (Δ[m] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y)) (i : Fin (n + 1)) :
    (coherentSimplexMap (extension θ)).map (.mk (ULift.up.{u} i.castSucc)) (.mk
      (ULift.up.{u} (Fin.last (n + 1)))) ≫
      homMap x y τ ((extension θ).toOrderHom i.castSucc) ((extension θ).toOrderHom
        (Fin.last (n + 1))) ≫
      eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b)
        ((congrArg (HomSimplex.object x y) (extension_front θ i)).trans (object_front x y
          (θ.toOrderHom i)))
        ((congrArg (HomSimplex.object x y) (extension_last θ)).trans (object_last (n := m) x y))) =
      lastMap x y (SSet.stdSimplex.map θ ≫ τ) i := by
  have h := homMap_reindex x y τ (extension_front θ i) (extension_last θ)
  have hL := homMap_last x y τ (θ.toOrderHom i)
  have hI := image_nerve θ i
  let A := (coherentSimplexMap (extension θ)).map (.mk (ULift.up.{u} i.castSucc)) (.mk (ULift.up.{u}
    (Fin.last (n + 1))))
  let B := homMap x y τ ((extension θ).toOrderHom i.castSucc) ((extension θ).toOrderHom
    (Fin.last (n + 1)))
  let e₀ := eqToHom (congrArg₂ (fun a b : Fin (m + 2) =>
      (HomSimplex.object x y a ⟶[SSet.{u}] HomSimplex.object x y b)) (extension_front θ
        i) (extension_last θ))
  let e₁ := eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b) (object_front x y (θ.toOrderHom i))
    (object_last (n := m) x y))
  have hE : eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b)
        ((congrArg (HomSimplex.object x y) (extension_front θ i)).trans (object_front x y
          (θ.toOrderHom i)))
        ((congrArg (HomSimplex.object x y) (extension_last θ)).trans (object_last (n :=
          m) x y))) = e₀ ≫ e₁ :=
    (eqToHom_trans _ _).symm
  let Q := eqToHom (congrArg₂ (fun a b : Fin (m + 2) => nerve (SimplicialThickening.Path
    (ULift.up.{u} a)
    (ULift.up.{u} b)))
    (extension_front θ i) (extension_last θ))
  let M := homMap x y τ (θ.toOrderHom i).castSucc (Fin.last (m + 1))
  have hB : B ≫ e₀ = Q ≫ M := h
  have hM : M ≫ e₁ = lastMap x y τ (θ.toOrderHom i) := hL
  have hQ : A ≫ Q = nerveMap (imageFunctor θ i) := hI
  have hs₀ : A ≫ (B ≫ _) = A ≫ (B ≫ (e₀ ≫ e₁)) := congrArg (fun g => A ≫ (B ≫ g)) hE
  have hs₁ : A ≫ (B ≫ (e₀ ≫ e₁)) = A ≫ ((B ≫ e₀) ≫ e₁) :=
    congrArg (fun g => A ≫ g) (Category.assoc B e₀ e₁).symm
  have hs₂ : A ≫ ((B ≫ e₀) ≫ e₁) = A ≫ ((Q ≫ M) ≫ e₁) :=
    congrArg (fun g => A ≫ (g ≫ e₁)) hB
  have hs₃ : A ≫ ((Q ≫ M) ≫ e₁) = A ≫ (Q ≫ (M ≫ e₁)) :=
    congrArg (fun g => A ≫ g) (Category.assoc Q M e₁)
  have hs₄ : A ≫ (Q ≫ (M ≫ e₁)) = A ≫ (Q ≫ lastMap x y τ (θ.toOrderHom i)) :=
    congrArg (fun g => A ≫ (Q ≫ g)) hM
  have hs₅ : A ≫ (Q ≫ lastMap x y τ (θ.toOrderHom i)) =
      nerveMap (imageFunctor θ i) ≫ lastMap x y τ (θ.toOrderHom i) :=
    (Category.assoc A Q _).symm.trans (congrArg (fun g => g ≫ lastMap x y τ (θ.toOrderHom i)) hQ)
  exact hs₀.trans (hs₁.trans (hs₂.trans (hs₃.trans (hs₄.trans
    (hs₅.trans (lastMap_naturality x y θ τ i))))))

end CategoryTheory.CoherentRealization.HomSimplexNaturality
