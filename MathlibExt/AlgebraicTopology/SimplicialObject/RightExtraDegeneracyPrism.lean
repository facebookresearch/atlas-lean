/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedExtraDegeneracyRev
public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedOver
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Simplicial contractions from right extra degeneracies

A right extra degeneracy of an augmented simplicial object gives a section of the
augmentation and a simplicial homotopy from the identity to augmentation followed by
that section. The section in degree `n` is the augmentation section `s'` followed by
the degeneracy induced by the unique map `[n] → [0]`.

Simplex reversal identifies this contraction with the corresponding left extra-degeneracy
homotopy. Applying any functor preserves its prism operators. In the slice over a map
from the augmentation target to `A`, every operator stays over `A`. These statements
hold in arbitrary categories with independent object and morphism universes.

See `SimplicialObject.Augmented.ExtraDegeneracy.homotopy` for the left-handed contraction.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v u' v'

namespace CategoryTheory.SimplicialObject.Augmented.RightExtraDegeneracy

variable {C : Type u} [Category.{v} C]
  {X : SimplicialObject.Augmented C} (R : RightExtraDegeneracy X)

/--
The simplicial section of the augmentation whose degree-`n` component is `s'`
followed by the degeneracy from degree zero induced by the unique map `[n] → [0]`.
-/
def section_ : (SimplicialObject.const C).obj X.right ⟶ X.left where
  app Δ := R.s' ≫ X.left.map (SimplexCategory.isTerminalZero.from Δ.unop).op
  naturality {Δ Δ'} θ := by
    simp only [Functor.const_obj_map, Category.id_comp, Category.assoc, ← X.left.map_comp]
    have h : (SimplexCategory.isTerminalZero.from Δ.unop).op ≫ θ =
        (SimplexCategory.isTerminalZero.from Δ'.unop).op := by
      apply Quiver.Hom.unop_inj
      apply Subsingleton.elim
    exact (Category.id_comp _).trans
      (congrArg (fun f => R.s' ≫ X.left.map f) h).symm

/--
The degree-zero component of the simplicial section associated to a right extra
degeneracy is its augmentation section `s'`.
-/
@[simp]
theorem section_app_zero : R.section_.app (op ⦋0⦌) = R.s' := by
  simp [section_]

/--
The simplicial section associated to a right extra degeneracy, followed by the
augmentation, is the identity on the constant target diagram.
-/
@[reassoc (attr := simp)]
theorem section_comp_augmentation : R.section_ ≫ X.hom = 𝟙 _ := by
  apply NatTrans.ext
  funext Δ
  dsimp only [section_, NatTrans.comp_app, NatTrans.id_app]
  let θ := (SimplexCategory.isTerminalZero.from Δ.unop).op
  have hNat := X.hom.naturality θ
  change X.left.map θ ≫ X.hom.app Δ =
    X.hom.app (op ⦋0⦌) ≫ 𝟙 X.right at hNat
  have hNat' := hNat.trans (Category.comp_id _)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => R.s' ≫ f) hNat').trans R.s'_comp_ε)

/--
The degree-`n` section component from a right extra degeneracy equals that from the
corresponding left extra degeneracy on the reversed augmented object.
-/
theorem section_app_eq_rev (n : ℕ) :
    R.section_.app (op ⦋n⦌) = R.toExtraDegeneracyRev.section_.app (op ⦋n⦌) := by
  dsimp only [section_, ExtraDegeneracy.section_, toExtraDegeneracyRev]
  rw [rev_left_map]
  apply congrArg (fun f => R.s' ≫ X.left.map f)
  apply Quiver.Hom.unop_inj
  apply Subsingleton.elim

/--
The simplicial homotopy from the identity of the augmented object's diagram to its
augmentation followed by the associated simplicial section, obtained by reversing
the left extra-degeneracy prism.
-/
def prism : SimplicialObject.Homotopy (𝟙 X.left) (X.hom ≫ R.section_) where
  h i := R.toExtraDegeneracyRev.homotopy.h i.rev
  h_zero_comp_δ_zero n := by
    have h := R.toExtraDegeneracyRev.homotopy.h_last_comp_δ_last n
    simp only [Functor.id_obj, rev_left_δ, Fin.rev_zero, Fin.rev_last, rev_hom_app_mk, NatTrans.comp_app, ←
      R.section_app_eq_rev n] at h
    dsimp only [rev, revFunctor, Comma.map, SimplicialObject.opFunctor,
      Functor.whiskeringLeft, Functor.comp_obj, SimplexCategory.rev, Functor.op_obj] at h
    dsimp only [rev, revFunctor, Comma.map, SimplicialObject.opFunctor,
      Functor.whiskeringLeft, Functor.comp_obj, SimplexCategory.rev, Functor.op_obj]
    simp only [Fin.rev_succ, Fin.rev_castSucc, Fin.rev_last, Fin.rev_zero,
      NatTrans.id_app, NatTrans.comp_app, Fin.succ_castSucc]
    exact h
  h_last_comp_δ_last n := by
    have h := R.toExtraDegeneracyRev.homotopy.h_zero_comp_δ_zero n
    simp only [Functor.id_obj, rev_left_δ, Fin.rev_last, Fin.rev_zero, NatTrans.id_app] at h
    dsimp only [rev, revFunctor, Comma.map, SimplicialObject.opFunctor,
      Functor.whiskeringLeft, Functor.comp_obj, SimplexCategory.rev, Functor.op_obj] at h
    dsimp only [rev, revFunctor, Comma.map, SimplicialObject.opFunctor,
      Functor.whiskeringLeft, Functor.comp_obj, SimplexCategory.rev, Functor.op_obj]
    simp only [Fin.rev_succ, Fin.rev_castSucc, Fin.rev_last, Fin.rev_zero,
      NatTrans.id_app, NatTrans.comp_app, Fin.succ_castSucc]
    exact h
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    have hji : j.rev.castSucc < i.rev := by
      simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_rev] at hij ⊢
      omega
    have h := R.toExtraDegeneracyRev.homotopy.h_castSucc_comp_δ_succ_of_lt
      i.rev j.rev hji
    simp only [Functor.id_obj, rev_left_δ, Fin.rev_succ, Fin.rev_castSucc, Fin.rev_rev] at h
    dsimp only [rev, revFunctor, Comma.map, SimplicialObject.opFunctor,
      Functor.whiskeringLeft, Functor.comp_obj, SimplexCategory.rev, Functor.op_obj] at h
    dsimp only [rev, revFunctor, Comma.map, SimplicialObject.opFunctor,
      Functor.whiskeringLeft, Functor.comp_obj, SimplexCategory.rev, Functor.op_obj]
    simp only [Fin.rev_succ, Fin.rev_castSucc, Fin.rev_last, Fin.rev_zero,
      NatTrans.id_app, NatTrans.comp_app, Fin.succ_castSucc]
    exact h
  h_succ_comp_δ_castSucc_succ j := by
    have h := R.toExtraDegeneracyRev.homotopy.h_succ_comp_δ_castSucc_succ j.rev
    simp only [Functor.id_obj, rev_left_δ, Fin.rev_succ, Fin.rev_castSucc, Fin.rev_rev, Fin.succ_castSucc] at h
    dsimp only [rev, revFunctor, Comma.map, SimplicialObject.opFunctor,
      Functor.whiskeringLeft, Functor.comp_obj, SimplexCategory.rev, Functor.op_obj] at h
    dsimp only [rev, revFunctor, Comma.map, SimplicialObject.opFunctor,
      Functor.whiskeringLeft, Functor.comp_obj, SimplexCategory.rev, Functor.op_obj]
    simp only [Fin.rev_succ, Fin.rev_castSucc, Fin.rev_last, Fin.rev_zero,
      NatTrans.id_app, NatTrans.comp_app, Fin.succ_castSucc]
    exact h.symm
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    have hij : i.rev ≤ j.rev.castSucc := by
      simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_rev] at hji ⊢
      omega
    have h := R.toExtraDegeneracyRev.homotopy.h_succ_comp_δ_castSucc_of_lt
      i.rev j.rev hij
    simp only [Functor.id_obj, rev_left_δ, Fin.rev_succ, Fin.rev_castSucc, Fin.rev_rev] at h
    dsimp only [rev, revFunctor, Comma.map, SimplicialObject.opFunctor,
      Functor.whiskeringLeft, Functor.comp_obj, SimplexCategory.rev, Functor.op_obj] at h
    dsimp only [rev, revFunctor, Comma.map, SimplicialObject.opFunctor,
      Functor.whiskeringLeft, Functor.comp_obj, SimplexCategory.rev, Functor.op_obj]
    simp only [Fin.rev_succ, Fin.rev_castSucc, Fin.rev_last, Fin.rev_zero,
      NatTrans.id_app, NatTrans.comp_app, Fin.succ_castSucc]
    exact h
  h_comp_σ_castSucc_of_le i j hij := by
    have hji : j.rev ≤ i.rev := Fin.rev_le_rev.mpr hij
    have h := R.toExtraDegeneracyRev.homotopy.h_comp_σ_succ_of_lt i.rev j.rev hji
    simp only [Functor.id_obj, rev_left_σ, Fin.rev_succ, Fin.rev_castSucc, Fin.rev_rev] at h
    dsimp only [rev, revFunctor, Comma.map, SimplicialObject.opFunctor,
      Functor.whiskeringLeft, Functor.comp_obj, SimplexCategory.rev, Functor.op_obj] at h
    dsimp only [rev, revFunctor, Comma.map, SimplicialObject.opFunctor,
      Functor.whiskeringLeft, Functor.comp_obj, SimplexCategory.rev, Functor.op_obj]
    simp only [Fin.rev_succ, Fin.rev_castSucc, Fin.rev_last, Fin.rev_zero,
      NatTrans.id_app, NatTrans.comp_app, Fin.succ_castSucc]
    exact h
  h_comp_σ_succ_of_lt i j hji := by
    have hij : i.rev ≤ j.rev := Fin.rev_le_rev.mpr hji
    have h := R.toExtraDegeneracyRev.homotopy.h_comp_σ_castSucc_of_le i.rev j.rev hij
    simp only [Functor.id_obj, rev_left_σ, Fin.rev_succ, Fin.rev_castSucc, Fin.rev_rev] at h
    dsimp only [rev, revFunctor, Comma.map, SimplicialObject.opFunctor,
      Functor.whiskeringLeft, Functor.comp_obj, SimplexCategory.rev, Functor.op_obj] at h
    dsimp only [rev, revFunctor, Comma.map, SimplicialObject.opFunctor,
      Functor.whiskeringLeft, Functor.comp_obj, SimplexCategory.rev, Functor.op_obj]
    simp only [Fin.rev_succ, Fin.rev_castSucc, Fin.rev_last, Fin.rev_zero,
      NatTrans.id_app, NatTrans.comp_app, Fin.succ_castSucc]
    exact h

/--
For a functor `F` between arbitrary categories, the degree-`n` prism operator of
the mapped right extra degeneracy is `F` applied to the original prism operator.
-/
theorem prism_map_h {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    {n : ℕ} (i : Fin (n + 1)) :
    (R.map F).prism.h i = F.map (R.prism.h i) := by
  dsimp only [prism, ExtraDegeneracy.homotopy, ExtraDegeneracy.homotopy.h,
    toExtraDegeneracyRev, RightExtraDegeneracy.map, SimplicialObject.δ₀Iter,
    SimplicialObject.σ₀Iter]
  rw [rev_left_map, rev_left_map, rev_left_map, rev_left_map]
  dsimp only [SimplicialObject.Augmented.whiskeringObj,
    SimplicialObject.whiskering, Functor.whiskeringRight,
    Functor.comp_map, Functor.whiskerRight, rev, revFunctor, Comma.map,
    SimplicialObject.opFunctor, Functor.whiskeringLeft,
    SimplicialObject.Augmented.drop, SimplicialObject.Augmented.point]
  simp only [Functor.map_comp]
  rfl
/--
For a map `a : X.right → A`, every prism operator in the slice over `A` commutes
with the degreewise augmentation to `A`:
`h_i ≫ (ε_(n+1) ≫ a) = ε_n ≫ a`.
-/
@[simp]
theorem overPoint_prism_augmentation {A : C} (a : X.right ⟶ A)
    {n : ℕ} (i : Fin (n + 1)) :
    ((R.overPoint a).prism.h i).left ≫ (X.hom.app (op ⦋n + 1⦌) ≫ a) =
      X.hom.app (op ⦋n⦌) ≫ a :=
  ((R.overPoint a).prism.h i).w

end CategoryTheory.SimplicialObject.Augmented.RightExtraDegeneracy

end
