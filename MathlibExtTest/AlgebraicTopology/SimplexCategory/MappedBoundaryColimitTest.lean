/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplexCategory.MappedBoundaryColimit

/-! # Clients of the original coface and mapped-boundary colimits -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory Limits SimplexCategory
open scoped Simplicial

namespace MappedBoundaryColimitTest

/-- An arbitrary compatible family has a unique map with every original coprojection equation. -/
theorem originalFamilyDesc (H : SimplexCategory ⥤ Type v) (n : ℕ) (T : Type v)
    (a : Fin (n + 3) → (H.obj ⦋n + 1⦌ ⟶ T))
    (w : ∀ p : (MultispanShape.ofLinearOrder (Fin (n + 3))).L,
      (cofaceMultispan H n).fst p ≫ a p.1.1 = (cofaceMultispan H n).snd p ≫ a p.1.2) :
    ∃! f : cofaceRangeUnion H n ⟶ T, ∀ i, (cofaceUnionCocone H n).π i ≫ f = a i :=
  existsUnique_cofaceUnionDesc H n T a w

/-- The constructed descendant commutes with every original target map. -/
theorem originalFamilyDesc_postcomp (H : SimplexCategory ⥤ Type v) (n : ℕ)
    (T T' : Type v) (a : Fin (n + 3) → (H.obj ⦋n + 1⦌ ⟶ T))
    (w : ∀ p : (MultispanShape.ofLinearOrder (Fin (n + 3))).L,
      (cofaceMultispan H n).fst p ≫ a p.1.1 = (cofaceMultispan H n).snd p ≫ a p.1.2)
    (b : T ⟶ T') :
    Multicofork.IsColimit.desc (cofaceUnionIsColimit H n) (fun i ↦ a i ≫ b)
        (fun p ↦ by
          have hp : H.map (δ (p.1.2.pred (Fin.ne_zero_of_lt p.2))) ≫ a p.1.1 =
              H.map (δ (p.1.1.castPred (Fin.ne_last_of_lt p.2))) ≫ a p.1.2 := w p
          change H.map (δ (p.1.2.pred (Fin.ne_zero_of_lt p.2))) ≫ (a p.1.1 ≫ b) =
            H.map (δ (p.1.1.castPred (Fin.ne_last_of_lt p.2))) ≫ (a p.1.2 ≫ b)
          simpa only [Category.assoc] using congrArg (· ≫ b) hp) =
      Multicofork.IsColimit.desc (cofaceUnionIsColimit H n) a w ≫ b := by
  have w' : ∀ p : (MultispanShape.ofLinearOrder (Fin (n + 3))).L,
      (cofaceMultispan H n).fst p ≫ (a p.1.1 ≫ b) =
        (cofaceMultispan H n).snd p ≫ (a p.1.2 ≫ b) := by
    intro p
    have hp : H.map (δ (p.1.2.pred (Fin.ne_zero_of_lt p.2))) ≫ a p.1.1 =
        H.map (δ (p.1.1.castPred (Fin.ne_last_of_lt p.2))) ≫ a p.1.2 := w p
    change H.map (δ (p.1.2.pred (Fin.ne_zero_of_lt p.2))) ≫ (a p.1.1 ≫ b) =
      H.map (δ (p.1.1.castPred (Fin.ne_last_of_lt p.2))) ≫ (a p.1.2 ≫ b)
    simpa only [Category.assoc] using congrArg (· ≫ b) hp
  change Multicofork.IsColimit.desc (cofaceUnionIsColimit H n) (fun i ↦ a i ≫ b) w' =
    Multicofork.IsColimit.desc (cofaceUnionIsColimit H n) a w ≫ b
  apply Multicofork.IsColimit.hom_ext (cofaceUnionIsColimit H n)
  intro i
  change Fin (n + 3) at i
  trans a i ≫ b
  · exact Multicofork.IsColimit.fac (cofaceUnionIsColimit H n) (fun i ↦ a i ≫ b) w' i
  · exact (congrArg (· ≫ b) (Multicofork.IsColimit.fac (cofaceUnionIsColimit H n) a w i)).symm.trans
      (Category.assoc _ _ _)

/-- Both original doubleface legs retain their equation after an arbitrary source map. -/
theorem originalDoubleface_precomp (H : SimplexCategory ⥤ Type v) (n : ℕ)
    (p : { q : Fin (n + 3) × Fin (n + 3) // q.1 < q.2 })
    (A : Type v) (r : A ⟶ H.obj ⦋n⦌) :
    r ≫ H.map (δ (p.1.2.pred (Fin.ne_zero_of_lt p.2))) ≫
        (cofaceUnionCocone H n).π p.1.1 =
      r ≫ H.map (δ (p.1.1.castPred (Fin.ne_last_of_lt p.2))) ≫
        (cofaceUnionCocone H n).π p.1.2 := by
  have hw : H.map (δ (p.1.2.pred (Fin.ne_zero_of_lt p.2))) ≫
        (cofaceUnionCocone H n).π p.1.1 =
      H.map (δ (p.1.1.castPred (Fin.ne_last_of_lt p.2))) ≫
        (cofaceUnionCocone H n).π p.1.2 := (cofaceUnionCocone H n).condition p
  exact congrArg (r ≫ ·) hw

/-- Boundary coverage retains the ambient image of the very same original point. -/
theorem originalBoundaryPoint (F : SSet.{u} ⥤ Type v) [PreservesFiniteColimits F]
    (n : ℕ) (x : F.obj (∂Δ[n + 1] : SSet.{u})) :
    ∃ i : Fin (n + 2), ∃ a : F.obj (Δ[n] : SSet.{u}),
      F.map (SSet.boundary.ι i) a = x ∧
        F.map (SSet.stdSimplex.δ i) a = F.map ((SSet.boundary.{u} (n + 1)).ι) x := by
  obtain ⟨i, a, ha⟩ := SSet.mappedBoundary_jointly_surjective F n x
  refine ⟨i, a, ha, ?_⟩
  have hw := ConcreteCategory.congr_hom (SSet.mappedBoundary_ι_comp F i) a
  change F.map ((SSet.boundary.{u} (n + 1)).ι) (F.map (SSet.boundary.ι i) a) =
    F.map (SSet.stdSimplex.δ i) a at hw
  rw [ha] at hw
  exact hw.symm

/-- The inverse union map retains the literal original ambient image. -/
theorem originalHigherUnionInverse (F : SSet.{u} ⥤ Type v) [PreservesFiniteColimits F]
    (n : ℕ) (y : cofaceRangeUnion (SSet.stdSimplex.{u} ⋙ F) n) :
    F.map ((SSet.boundary.{u} (n + 2)).ι) ((SSet.mappedBoundaryUnionIso F n).inv y) = y.val := by
  have hw := ConcreteCategory.congr_hom (SSet.mappedBoundaryUnionIso_hom_val F n)
    ((SSet.mappedBoundaryUnionIso F n).inv y)
  have hy := ConcreteCategory.congr_hom (SSet.mappedBoundaryUnionIso F n).inv_hom_id y
  change (SSet.mappedBoundaryUnionIso F n).hom ((SSet.mappedBoundaryUnionIso F n).inv y) = y at hy
  change ((SSet.mappedBoundaryUnionIso F n).hom
      ((SSet.mappedBoundaryUnionIso F n).inv y)).val =
    F.map ((SSet.boundary.{u} (n + 2)).ι) ((SSet.mappedBoundaryUnionIso F n).inv y) at hw
  rw [hy] at hw
  exact hw.symm

/-- The zero case uses the produced initial object. -/
theorem originalZeroBoundary (F : SSet.{u} ⥤ Type v) [PreservesFiniteColimits F]
    (T : Type v) (a b : F.obj (∂Δ[0] : SSet.{u}) ⟶ T) : a = b :=
  (SSet.mappedBoundaryZeroIsInitial F).hom_ext a b

/-- Every original endpoint pair has a unique map from the actual mapped one-boundary. -/
theorem originalOneBoundaryDesc (F : SSet.{u} ⥤ Type v) [PreservesFiniteColimits F]
    (T : Type v) (a b : F.obj (Δ[0] : SSet.{u}) ⟶ T) :
    ∃! f : F.obj (∂Δ[1] : SSet.{u}) ⟶ T,
      F.map (SSet.boundary.ι (0 : Fin 2)) ≫ f = a ∧
        F.map (SSet.boundary.ι (1 : Fin 2)) ≫ f = b := by
  let hc := SSet.mappedBoundaryOneIsColimit F
  refine ⟨BinaryCofan.IsColimit.desc hc a b, ⟨?_, ?_⟩, ?_⟩
  · exact BinaryCofan.IsColimit.inl_desc hc a b
  · exact BinaryCofan.IsColimit.inr_desc hc a b
  · intro f hf
    apply BinaryCofan.IsColimit.hom_ext hc
    · exact hf.1.trans (BinaryCofan.IsColimit.inl_desc hc a b).symm
    · exact hf.2.trans (BinaryCofan.IsColimit.inr_desc hc a b).symm

end MappedBoundaryColimitTest
