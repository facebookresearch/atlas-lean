/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaSmashFaces

/-!
# Generic

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback

section Family
universe uV vV uJ
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {J : Type uJ} [EnrichedCategory V J]

/-- The free-pair comparison is natural in both coefficient objects and their tensor-product maps. -/
def CoefficientFamily (M : MonoidalCategory (EnrichedFunctorCat V J))
    (a : ℕ → J) (t : ℕ → ℕ → ℕ)
    (p : Independent.PairFormula M (fun n X => Free.object (a n) X) t) : Prop :=
  letI := M
  ∀ (n r : ℕ) {X X' Y Y' : V} (f : X ⟶ X') (g : Y ⟶ Y'),
    (Free.coefficientMap (a n) f ⊗ₘ Free.coefficientMap (a r) g) ≫
        (p n r X' Y').hom =
      (p n r X Y).hom ≫ Free.coefficientMap (a (t n r)) (f ⊗ₘ g)

/-- Type transport retains the original full pair and its coefficient naturality. -/
theorem coefficientFamily_transport
    (M M' : MonoidalCategory (EnrichedFunctorCat V J))
    (a a' : ℕ → J) (t t' : ℕ → ℕ → ℕ)
    (hM : M = M') (ha : a = a') (ht : t = t')
    (p : Independent.PairFormula M (fun n X => Free.object (a n) X) t)
    (p' : Independent.PairFormula M' (fun n X => Free.object (a' n) X) t')
    (hp : HEq p p') (h : CoefficientFamily M a t p) :
    CoefficientFamily M' a' t' p' := by
  cases hM
  cases ha
  cases ht
  cases eq_of_heq hp
  exact h

end Family

section FreeLift
universe uV vV uJ
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {J : Type uJ} [EnrichedCategory V J]

theorem free_evaluation_counit (a : J) {K : V} (N : EnrichedFunctorCat V J)
    (g : Free.object a K ⟶ N) :
    Free.coefficientMap a (Free.evaluate a K N g) ≫
      Free.extend a (N.toEnrichedFunctor.obj a) N (𝟙 _) = g := by
  have h := Free.extend_precomp a N (Free.evaluate a K N g) (𝟙 _)
  simpa only [Category.comp_id, Free.extend_evaluate] using h.symm

private theorem inverse_square {D : Type*} [Category* D]
    {A A' B B' : D} (e : A ≅ B) (e' : A' ≅ B')
    (u : A ⟶ A') (v : B ⟶ B') (h : u ≫ e'.hom = e.hom ≫ v) :
    v ≫ e'.inv = e.inv ≫ u := by
  apply (cancel_mono e'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, e.inv_hom_id_assoc]

/-- Lift a unit-target free map through the pair comparison, then apply the right unitor to the
remaining free factor. -/
def rightLift (M : MonoidalCategory (EnrichedFunctorCat V J))
    (a : ℕ → J) (t : ℕ → ℕ → ℕ)
    (p : Independent.PairFormula M (fun n X => Free.object (a n) X) t)
    (n r : ℕ) (X K : V) :
    letI := M
    (Free.object (a r) K ⟶ 𝟙_ (EnrichedFunctorCat V J)) →
      (Free.object (a (t n r)) (X ⊗ K) ⟶ Free.object (a n) X) := by
  letI := M
  intro g
  exact (p n r X K).inv ≫ Free.object (a n) X ◁ g ≫ (ρ_ (Free.object (a n) X)).hom

theorem rightLift_coefficient (M : MonoidalCategory (EnrichedFunctorCat V J))
    (a : ℕ → J) (t : ℕ → ℕ → ℕ)
    (p : Independent.PairFormula M (fun n X => Free.object (a n) X) t)
    (h : CoefficientFamily M a t p) (n r : ℕ) (X : V) {K K' : V} (f : K ⟶ K') :
    letI := M
    ∀ g : Free.object (a r) K' ⟶ 𝟙_ (EnrichedFunctorCat V J),
      Free.coefficientMap (a (t n r)) (X ◁ f) ≫ rightLift M a t p n r X K' g =
        rightLift M a t p n r X K (Free.coefficientMap (a r) f ≫ g) := by
  let := M
  intro g
  have hid : Free.coefficientMap (a n) (𝟙 X) = 𝟙 (Free.object (a n) X) :=
    (Free.functor (a n)).map_id X
  have hn := h n r (𝟙 X) f
  rw [hid, id_tensorHom, id_tensorHom] at hn
  have hi := inverse_square (p n r X K) (p n r X K')
    (Free.object (a n) X ◁ Free.coefficientMap (a r) f)
    (Free.coefficientMap (a (t n r)) (X ◁ f)) hn
  calc
    _ = (Free.coefficientMap (a (t n r)) (X ◁ f) ≫ (p n r X K').inv) ≫
        Free.object (a n) X ◁ g ≫ (ρ_ (Free.object (a n) X)).hom := by
      simp only [rightLift, Category.assoc]
    _ = ((p n r X K).inv ≫ Free.object (a n) X ◁ Free.coefficientMap (a r) f) ≫
        Free.object (a n) X ◁ g ≫ (ρ_ (Free.object (a n) X)).hom :=
      congrArg (fun z => z ≫ Free.object (a n) X ◁ g ≫ (ρ_ (Free.object (a n) X)).hom) hi
    _ = _ := by simp only [rightLift, whiskerLeft_comp, Category.assoc]

theorem rightLift_evaluate (M : MonoidalCategory (EnrichedFunctorCat V J))
    (a : ℕ → J) (t : ℕ → ℕ → ℕ)
    (p : Independent.PairFormula M (fun n X => Free.object (a n) X) t)
    (h : CoefficientFamily M a t p) (n r : ℕ) (X K : V) :
    letI := M
    ∀ g : Free.object (a r) K ⟶ 𝟙_ (EnrichedFunctorCat V J),
      Free.evaluate (a (t n r)) (X ⊗ K) (Free.object (a n) X)
          (rightLift M a t p n r X K g) =
        (X ◁ Free.evaluate (a r) K (𝟙_ (EnrichedFunctorCat V J)) g) ≫
          Free.evaluate (a (t n r))
            (X ⊗ (𝟙_ (EnrichedFunctorCat V J)).toEnrichedFunctor.obj (a r))
            (Free.object (a n) X)
            (rightLift M a t p n r X
              ((𝟙_ (EnrichedFunctorCat V J)).toEnrichedFunctor.obj (a r))
              (Free.extend (a r) ((𝟙_ (EnrichedFunctorCat V J)).toEnrichedFunctor.obj (a r))
                (𝟙_ (EnrichedFunctorCat V J)) (𝟙 _))) := by
  let := M
  intro g
  let N : EnrichedFunctorCat V J := 𝟙_ (EnrichedFunctorCat V J)
  let U := N.toEnrichedFunctor.obj (a r)
  let ev := Free.evaluate (a r) K N g
  let c : Free.object (a r) U ⟶ N := Free.extend (a r) U N (𝟙 U)
  have hc : Free.coefficientMap (a r) ev ≫ c = g := free_evaluation_counit (a r) N g
  have hl := rightLift_coefficient M a t p h n r X ev c
  rw [hc] at hl
  have he := congrArg
    (Free.evaluate (a (t n r)) (X ⊗ K) (Free.object (a n) X)) hl.symm
  have hn := (Free.adjunction (a (t n r))).homEquiv_naturality_left (X ◁ ev)
    (rightLift M a t p n r X U c)
  rw [Free.adjunction_homEquiv] at hn
  exact he.trans hn

end FreeLift

end PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
