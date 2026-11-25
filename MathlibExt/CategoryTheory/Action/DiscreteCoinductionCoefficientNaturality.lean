/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Action.DiscreteCoinductionCoresolution
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientLongExact

/-! Actual original field native comparison proof components. -/

/-! Original qualified proof block: CoindCoefficientNaturality -/
/-! Actual coefficient maps of the original continuous coinduction coresolution. -/

@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DiscreteAbelianAction

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The fixed power comparison preserves the actual stock coefficient maps. -/
theorem coindPowerToTopRepIso_coefficient_naturality
    {A B : DiscreteAbelianAction.{u, max u w} G} (f : A ⟶ B) (n : ℕ) :
    toTopRep.map ((Monad.monadPow (coindMonad.{u, w} G) n).map f) ≫
        (coindPowerToTopRepIso.{u, w} G B n).hom =
      (coindPowerToTopRepIso.{u, w} G A n).hom ≫
        ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G)
          (((TopRep.resFunctor (MonoidHom.id G)).map (toTopRep.map f))) n := by
  induction n with
  | zero =>
      change toTopRep.map f ≫ 𝟙 _ = 𝟙 _ ≫ toTopRep.map f
      simp only [Category.comp_id, Category.id_comp]
  | succ n ih =>
      rw [coindPowerToTopRepIso_succ_hom, coindPowerToTopRepIso_succ_hom]
      have hp := Monad.monadPow_succ_obj_eq_naturality (coindMonad.{u, w} G) n f
      have hmap :
          toTopRep.map ((Monad.monadPow (coindMonad.{u, w} G) (n + 1)).map f) ≫
            toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n B)) =
          toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A)) ≫
            toTopRep.map ((coindMonad.{u, w} G).map
              ((Monad.monadPow (coindMonad.{u, w} G) n).map f)) := by
        rw [← Functor.map_comp, hp, Functor.map_comp]
      have hcoind := coindToTopRepIso_naturality.{u, w} G
        ((Monad.monadPow (coindMonad.{u, w} G) n).map f)
      have hiter :
          (TopRep.coind₁Functor ℤ G).map
              (toTopRep.map ((Monad.monadPow (coindMonad.{u, w} G) n).map f)) ≫
            (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G B n).hom =
          (TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom ≫
            (TopRep.coind₁Functor ℤ G).map
              (ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G)
                (((TopRep.resFunctor (MonoidHom.id G)).map (toTopRep.map f))) n) := by
        rw [← Functor.map_comp, ih, Functor.map_comp]
      change _ = _ ≫ (TopRep.coind₁Functor ℤ G).map
        (ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G)
          (((TopRep.resFunctor (MonoidHom.id G)).map (toTopRep.map f))) n)
      have s₀ : CommSq
          (toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n A)))
          (toTopRep.map ((Monad.monadPow (coindMonad.{u, w} G) (n + 1)).map f))
          (toTopRep.map (coind.{u, w}.map
            ((Monad.monadPow (coindMonad.{u, w} G) n).map f)))
          (toTopRep.map (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{u, w} G) n B))) :=
        ⟨hmap.symm⟩
      have s₁ : CommSq
          (coindToTopRepIso.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj A)).hom
          (toTopRep.map (coind.{u, w}.map
            ((Monad.monadPow (coindMonad.{u, w} G) n).map f)))
          ((TopRep.coind₁Functor ℤ G).map
            (toTopRep.map ((Monad.monadPow (coindMonad.{u, w} G) n).map f)))
          (coindToTopRepIso.{u, w} G ((Monad.monadPow (coindMonad.{u, w} G) n).obj B)).hom :=
        ⟨hcoind.symm⟩
      have s₂ : CommSq
          ((TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G A n).hom)
          ((TopRep.coind₁Functor ℤ G).map
            (toTopRep.map ((Monad.monadPow (coindMonad.{u, w} G) n).map f)))
          ((TopRep.coind₁Functor ℤ G).map
            (ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G)
              ((TopRep.resFunctor (MonoidHom.id G)).map (toTopRep.map f)) n))
          ((TopRep.coind₁Functor ℤ G).map (coindPowerToTopRepIso.{u, w} G B n).hom) :=
        ⟨hiter.symm⟩
      exact (s₀.horiz_comp (s₁.horiz_comp s₂)).w.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual canonical coresolution degree map preserves the original stock coefficient arrow. -/
theorem coindCoresolutionTermIso_coefficient_naturality
    {A B : DiscreteAbelianAction.{u, max u w} G} (f : A ⟶ B) (n : ℕ) :
    toTopRep.map (((Monad.coresolutionFunctor (coindMonad.{u, w} G)).map f).app
        (SimplexCategory.mk n)) ≫ (coindCoresolutionTermIso.{u, w} G B n).hom =
      (coindCoresolutionTermIso.{u, w} G A n).hom ≫
        ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G)
          (((TopRep.resFunctor (MonoidHom.id G)).map (toTopRep.map f))) (n + 1) := by
  have hc := Monad.coresolutionObjIso_naturality (coindMonad.{u, w} G) f n
  have hm :
      toTopRep.map (((Monad.coresolutionFunctor (coindMonad.{u, w} G)).map f).app
          (SimplexCategory.mk n)) ≫
        toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) B n).hom =
      toTopRep.map (Monad.coresolutionObjIso (coindMonad.{u, w} G) A n).hom ≫
        toTopRep.map ((Monad.monadPow (coindMonad.{u, w} G) (n + 1)).map f) := by
    exact (toTopRep.map_comp _ _).symm.trans
      ((congrArg (fun m => toTopRep.map m) hc).trans (toTopRep.map_comp _ _))
  change _ ≫ (toTopRep.map _ ≫ _) = (toTopRep.map _ ≫ _) ≫ _
  rw [← Category.assoc, hm, Category.assoc,
    coindPowerToTopRepIso_coefficient_naturality, ← Category.assoc]

end CategoryTheory.DiscreteAbelianAction
end

/-! Original qualified proof block: CoindInvariantTermNaturality -/
/-! Original coinduction coefficient naturality after actual invariants and forgetting topology. -/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DiscreteAbelianAction
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual coefficient term square persists under original invariant evaluation. -/
theorem coindCoresolutionInvariantTerm_coefficient_naturality
    {A B : DiscreteAbelianAction.{u, max u w} G} (f : A ⟶ B) (n : ℕ) :
    (TopRep.invariantsFunctor ℤ G ⋙
        ContinuousCohomology.discreteCoefficientForget.{max u w}).map
        (toTopRep.map (((Monad.coresolutionFunctor (coindMonad.{u, w} G)).map f).app
          (SimplexCategory.mk n))) ≫
      (TopRep.invariantsFunctor ℤ G ⋙
        ContinuousCohomology.discreteCoefficientForget.{max u w}).map
        (coindCoresolutionTermIso.{u, w} G B n).hom =
    (TopRep.invariantsFunctor ℤ G ⋙
        ContinuousCohomology.discreteCoefficientForget.{max u w}).map
        (coindCoresolutionTermIso.{u, w} G A n).hom ≫
      (TopRep.invariantsFunctor ℤ G ⋙
        ContinuousCohomology.discreteCoefficientForget.{max u w}).map
        (ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G)
          ((TopRep.resFunctor (MonoidHom.id G)).map (toTopRep.map f)) (n + 1)) := by
  let Q := TopRep.invariantsFunctor ℤ G ⋙
    ContinuousCohomology.discreteCoefficientForget.{max u w}
  have h := coindCoresolutionTermIso_coefficient_naturality.{u, w} G f n
  exact (Q.map_comp _ _).symm.trans
    ((congrArg (fun q => Q.map q) h).trans (Q.map_comp _ _))

end CategoryTheory.DiscreteAbelianAction
end
