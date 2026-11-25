/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy

/-!
# Homotopy-category precomposition from actual lifting

A source map lifting against the chosen target-to-terminal map and the
chosen good path projection induces a bijection on the actual homotopy
category Hom. Both strict representatives and the same chosen path are used.
Native applications must supply those lifting facts from the actual K class.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsFibrant Z]

/-- Actual terminal/path lifting gives a bijection of the original homotopy-category Hom. -/
theorem bijective_Ho_precomp_of_terminal_path_lifting
    (f : X ⟶ Y) (P : PathObject Z) [P.IsGood]
    [HasLiftingProperty f (terminal.from Z)] [HasLiftingProperty f P.p] :
    Function.Bijective (fun g : ((weakEquivalences C).Q).obj Y ⟶ ((weakEquivalences C).Q).obj Z =>
      ((weakEquivalences C).Q).map f ≫ g) := by
  let H := ((weakEquivalences C).Q)
  constructor
  · intro a b hab
    obtain ⟨g, hg⟩ := (map_surjective_of_isLocalization H Y Z) a
    obtain ⟨h, hh⟩ := (map_surjective_of_isLocalization H Y Z) b
    have hr : RightHomotopyRel (f ≫ g) (f ≫ h) :=
      (RightHomotopyRel.iff_map_eq H X Z).mpr (by
        simpa only [H.map_comp, hg, hh] using hab)
    let r := hr.rightHomotopy P
    have sq : CommSq r.h f P.p (prod.lift g h) :=
      { w := by
          apply prod.hom_ext
          · simpa only [Category.assoc, P.p_fst, prod.lift_fst] using r.h₀
          · simpa only [Category.assoc, P.p_snd, prod.lift_snd] using r.h₁ }
    let lifted : P.RightHomotopy g h :=
      { h := sq.lift
        h₀ := by
          simpa only [Category.assoc, P.p_fst, prod.lift_fst] using
            congrArg (fun q => q ≫ prod.fst) sq.fac_right
        h₁ := by
          simpa only [Category.assoc, P.p_snd, prod.lift_snd] using
            congrArg (fun q => q ≫ prod.snd) sq.fac_right }
    exact hg.symm.trans (((RightHomotopyRel.iff_map_eq H Y Z).mp
      lifted.rightHomotopyRel).trans hh)
  · intro a
    obtain ⟨g, hg⟩ := (map_surjective_of_isLocalization H X Z) a
    have sq : CommSq g f (terminal.from Z) (terminal.from Y) :=
      { w := terminal.hom_ext _ _ }
    refine ⟨H.map sq.lift, ?_⟩
    change H.map f ≫ H.map sq.lift = a
    rw [← H.map_comp, sq.fac_left, hg]

end HomotopicalAlgebra
