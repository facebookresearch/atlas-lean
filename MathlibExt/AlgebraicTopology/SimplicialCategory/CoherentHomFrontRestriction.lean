/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomSimplexNaturality

/-!
# Whole constant front restrictions of original Hom simplices

An actual enriched functor whose original vertices land in the front
ordinal restricts the constructed Hom simplex to the supplied source
identity. The conclusion follows from the entire original Hom maps and
the specified vertex equations, without a coherence certificate.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomFrontRestriction
open SimplicialEnrichment HomSimplex HomSimplexNaturality
variable {C A : Carrier.{u}} {n : ℕ} (x y : C)
  (τ : (Δ[n] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y))

/-- A whole original Hom map whose endpoints lie in the front reads the constant supplied
source identity. -/
theorem hom_constant (F : A ⟶ coherentSimplex.{u} ⦋n + 1⦌)
    (i : A → Fin (n + 1)) (hi : ∀ a, (F.obj a).as.down = (i a).castSucc) (a b : A) :
    F.map a b ≫ homMap x y τ (F.obj a).as.down (F.obj b).as.down ≫
      eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b)
        ((congrArg (HomSimplex.object x y) (hi a)).trans (object_front x y (i a)))
        ((congrArg (HomSimplex.object x y) (hi b)).trans (object_front x y (i b)))) =
      toUnit (a ⟶[SSet.{u}] b) ≫ eId SSet.{u} x := by
  let U := F.map a b
  let V := homMap x y τ (F.obj a).as.down (F.obj b).as.down
  let e₀ := eqToHom (congrArg₂ (fun a b : Fin (n + 2) =>
    (HomSimplex.object x y a ⟶[SSet.{u}] HomSimplex.object x y b)) (hi a) (hi b))
  let e₁ := eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b) (object_front x y (i
    a)) (object_front x y (i b)))
  let Q := eqToHom (congrArg₂ (fun a b : Fin (n + 2) => nerve (SimplicialThickening.Path
    (ULift.up.{u} a)
    (ULift.up.{u} b))) (hi a) (hi b))
  let M := homMap x y τ (i a).castSucc (i b).castSucc
  have hE : eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b)
        ((congrArg (HomSimplex.object x y) (hi a)).trans (object_front x y (i a)))
        ((congrArg (HomSimplex.object x y) (hi b)).trans (object_front x y (i b)))) = e₀ ≫ e₁ :=
          (eqToHom_trans _ _).symm
  have hV : V ≫ e₀ = Q ≫ M := homMap_reindex x y τ (hi a) (hi b)
  have hM : M ≫ e₁ = toUnit _ ≫ eId SSet.{u} x := homMap_front x y τ (i a) (i b)
  have hs₀ : U ≫ (V ≫ _) = U ≫ (V ≫ (e₀ ≫ e₁)) := congrArg (fun g => U ≫ (V ≫ g)) hE
  have hs₁ : U ≫ (V ≫ (e₀ ≫ e₁)) = U ≫ ((V ≫ e₀) ≫ e₁) :=
    congrArg (fun g => U ≫ g) (Category.assoc V e₀ e₁).symm
  have hs₂ : U ≫ ((V ≫ e₀) ≫ e₁) = U ≫ ((Q ≫ M) ≫ e₁) := congrArg (fun g => U ≫ (g ≫ e₁)) hV
  have hs₃ : U ≫ ((Q ≫ M) ≫ e₁) = U ≫ (Q ≫ (M ≫ e₁)) := congrArg (fun g =>
    U ≫ g) (Category.assoc Q M e₁)
  have hs₄ : U ≫ (Q ≫ (M ≫ e₁)) = U ≫ (Q ≫ (toUnit _ ≫ eId SSet.{u} x)) :=
    congrArg (fun g => U ≫ (Q ≫ g)) hM
  have hU : U ≫ Q ≫ toUnit _ = toUnit (a ⟶[SSet.{u}] b) := by
    ext q p
    rfl
  have hs₅ : U ≫ (Q ≫ (toUnit _ ≫ eId SSet.{u} x)) = toUnit _ ≫ eId SSet.{u} x :=
    (congrArg (fun g => U ≫ g) (Category.assoc Q _ _).symm).trans
      ((Category.assoc U _ _).symm.trans (congrArg (fun g => g ≫ eId SSet.{u} x) hU))
  exact hs₀.trans (hs₁.trans (hs₂.trans (hs₃.trans (hs₄.trans hs₅))))

/-- The entire actual enriched front restriction is the supplied source's constant simplex. -/
theorem front (m : SimplexCategory) (F : coherentSimplex.{u} m ⟶ coherentSimplex.{u} ⦋n + 1⦌)
    (i : coherentSimplex.{u} m → Fin (n + 1)) (hi : ∀ a, (F.obj a).as.down = (i a).castSucc) :
    F ≫ simplex x y τ = constantSimplex C m x := by
  refine EnrichedFunctor.ext SSet.{u}
    (fun a => (congrArg (HomSimplex.object x y) (hi a)).trans (object_front x y (i a))) ?_
  intro a b
  exact hom_constant x y τ F i hi a b

end CategoryTheory.CoherentRealization.HomFrontRestriction
