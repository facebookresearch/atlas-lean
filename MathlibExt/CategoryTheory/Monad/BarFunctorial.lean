/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Monad.BarSimplicial
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataIso

/-!
# Functoriality of the two-sided bar in its module arguments

For the bar source and face conventions, see `Bar`.

For fixed carrier `C` and monad `T`, `B(-, T, -)` is covariant in morphisms
of right modules and of left modules (`barMap`, `barDataHom`,
`barDataFunctor`, `twoSidedBarHom`). Target postcomposition (`K : D ⥤ E`)
and source precomposition (`H : B ⥤ A`) are outer whiskerings, thin aliases
for Mathlib's `(Functor.whiskeringRight _ _ _).obj K` and
`(Functor.whiskeringLeft _ _ _).obj H`; ambient identity/composition
coherence is Mathlib's `whiskeringRightObjIdIso`/`whiskeringRightObjCompIso`
and `whiskeringLeftObjIdIso`/`whiskeringLeftObjCompIso` (all components are
identities, so the associator triangle/pentagon close by `simp`).
Each reassociates to the bar over the whiskered module through an explicit
functor-associator data isomorphism (`barDataPostcompOuterIso`,
`barDataPrecompOuterIso`), promoted to a genuine simplicial isomorphism
(`twoSidedBarPostcompOuterIso`, `twoSidedBarPrecompOuterIso`) and to a
whiskered genuine isomorphism (`twoSidedBarPostcompWhiskerIso`,
`twoSidedBarPrecompWhiskerIso`). Both whiskered isomorphisms are genuinely
natural over the product of module categories
(`twoSidedBarPostcompWhiskerNatIso`, `twoSidedBarPrecompWhiskerNatIso`),
reusing the existing degreewise isomorphisms and component naturality.
Identity whiskers and iterated whiskers coincide with the single whisker as
product-level NatTrans equalities (`twoSidedBarPostcompWhiskerNatIso_id`,
`twoSidedBarPostcompWhiskerNatIso_comp`,
`twoSidedBarPrecompWhiskerNatIso_id`,
`twoSidedBarPrecompWhiskerNatIso_comp`), chaining the ambient
`functorPostcompOuterId/Comp` or `functorPrecompOuterId/Comp` coherence with
the module-side `postcompId`/`postcompComp` or `precompId`/`precompComp`
bridge lifted through `twoSidedBarIso` via the product-level
`...ModuleIdNatIso`/`...ModuleCompNatIso` packages; the degree-`n`
component equalities (`twoSidedBarPostcompWhiskerIso_id_hom_app`,
`twoSidedBarPostcompWhiskerIso_comp_hom_app`,
`twoSidedBarPrecompWhiskerIso_id_hom_app`,
`twoSidedBarPrecompWhiskerIso_comp_hom_app`) are corollaries, with further
component consequences at `app a`/`app b₂` (all components are identities,
with correct contravariant `J ⋙ H` source order); the module-side
`postcompId`/`postcompComp` and `precompId`/`precompComp` bridges are
likewise componentwise identities.
Change of monad on a fixed carrier is not another strict formula here; it is a
separate restriction-of-scalars boundary. No pseudofunctor is built, and no
Kan--Quillen weak-equivalence or realization claim is made here.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]
variable {T : Monad C}

section BarMap

variable {R R' R'' : RightModule T D} {L L' L'' : LeftModule A T}

theorem rightModuleHom_rightActionPow (fR : R ⟶ R') (n : ℕ) (X : C) :
    fR.f.app ((monadPow T (n + 1)).obj X) ≫ rightActionPow T R' n X =
    rightActionPow T R n X ≫ fR.f.app ((monadPow T n).obj X) := by
  induction n generalizing X with
  | zero =>
    simp only [rightActionPow]
    exact RightModule.hom_condition_app fR X
  | succ n ih =>
    calc
      fR.f.app ((monadPow T (n + 1 + 1)).obj X) ≫ rightActionPow T R' (n + 1) X
          = fR.f.app ((monadPow T (n + 1)).obj (T.obj X)) ≫ rightActionPow T R' n (T.obj X) := rfl
      _ = rightActionPow T R n (T.obj X) ≫ fR.f.app ((monadPow T n).obj (T.obj X)) := ih (T.obj X)
      _ = rightActionPow T R (n + 1) X ≫ fR.f.app ((monadPow T (n + 1)).obj X) := rfl

/-- Covariant degreewise bar map in a right-module hom and a left-module hom. -/
noncomputable def barMap (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) :
    barObj T R L n ⟶ barObj T R' L' n where
  app a :=
    R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
      fR.f.app ((monadPow T n).obj (L'.functor.obj a))
  naturality a b g := by
    have hL : L.functor.map g ≫ fL.f.app b = fL.f.app a ≫ L'.functor.map g :=
      fL.f.naturality g
    have h_pow_Lmap_fL : (monadPow T n).map (L.functor.map g) ≫ (monadPow T n).map (fL.f.app b) =
        (monadPow T n).map (L.functor.map g ≫ fL.f.app b) := by
      rw [(monadPow T n).map_comp]
    have h_pow_fL_Lmap : (monadPow T n).map (fL.f.app a) ≫ (monadPow T n).map (L'.functor.map g) =
        (monadPow T n).map (fL.f.app a ≫ L'.functor.map g) := by
      rw [(monadPow T n).map_comp]
    -- naturality of fR at T^n (L' map g)
    have h_fR : R.functor.map ((monadPow T n).map (L'.functor.map g)) ≫
        fR.f.app ((monadPow T n).obj (L'.functor.obj b)) =
        fR.f.app ((monadPow T n).obj (L'.functor.obj a)) ≫
          R'.functor.map ((monadPow T n).map (L'.functor.map g)) :=
      fR.f.naturality ((monadPow T n).map (L'.functor.map g))
    -- combine maps
    have hR_comb1 : R.functor.map ((monadPow T n).map (L.functor.map g)) ≫
        R.functor.map ((monadPow T n).map (fL.f.app b)) =
        R.functor.map ((monadPow T n).map (L.functor.map g) ≫ (monadPow T n).map (fL.f.app b)) := by
      rw [← R.functor.map_comp]
    have hR_comb2 : R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
        R.functor.map ((monadPow T n).map (L'.functor.map g)) =
        R.functor.map ((monadPow T n).map (fL.f.app a) ≫
          (monadPow T n).map (L'.functor.map g)) := by
      rw [← R.functor.map_comp]
    -- main calc using right-associated chains
    calc
      R.functor.map ((monadPow T n).map (L.functor.map g)) ≫
          (R.functor.map ((monadPow T n).map (fL.f.app b)) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj b)))
          = (R.functor.map ((monadPow T n).map (L.functor.map g)) ≫
              R.functor.map ((monadPow T n).map (fL.f.app b))) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj b)) := by
        rw [Category.assoc]
      _ = R.functor.map ((monadPow T n).map (L.functor.map g) ≫
              (monadPow T n).map (fL.f.app b)) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj b)) := by
        rw [hR_comb1]
      _ = R.functor.map ((monadPow T n).map (L.functor.map g ≫ fL.f.app b)) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj b)) := by
        rw [← h_pow_Lmap_fL]
      _ = R.functor.map ((monadPow T n).map (fL.f.app a ≫ L'.functor.map g)) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj b)) := by
        rw [hL]
      _ = R.functor.map ((monadPow T n).map (fL.f.app a) ≫
              (monadPow T n).map (L'.functor.map g)) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj b)) := by
        rw [h_pow_fL_Lmap]
      _ = (R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
              R.functor.map ((monadPow T n).map (L'.functor.map g))) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj b)) := by
        rw [hR_comb2]
      _ = R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
            (R.functor.map ((monadPow T n).map (L'.functor.map g)) ≫
              fR.f.app ((monadPow T n).obj (L'.functor.obj b))) := by
        rw [Category.assoc]
      _ = R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
            (fR.f.app ((monadPow T n).obj (L'.functor.obj a)) ≫
              R'.functor.map ((monadPow T n).map (L'.functor.map g))) := by
        rw [h_fR]
      _ = (R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
              fR.f.app ((monadPow T n).obj (L'.functor.obj a))) ≫
            R'.functor.map ((monadPow T n).map (L'.functor.map g)) := by
        rw [Category.assoc]

@[simp] lemma barMap_app (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) (a : A) :
    (barMap fR fL n).app a =
      R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
        fR.f.app ((monadPow T n).obj (L'.functor.obj a)) := rfl

lemma barMap_app_alt (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) (a : A) :
    (barMap fR fL n).app a =
      fR.f.app ((monadPow T n).obj (L.functor.obj a)) ≫
        R'.functor.map ((monadPow T n).map (fL.f.app a)) :=
  fR.f.naturality ((monadPow T n).map (fL.f.app a))

@[simp] lemma barMap_id (R : RightModule T D) (L : LeftModule A T) (n : ℕ) :
    barMap (𝟙 R) (𝟙 L) n = 𝟙 (barObj T R L n) := by
  ext a
  simp

@[simp] lemma barMap_comp (fR : R ⟶ R') (gR : R' ⟶ R'') (fL : L ⟶ L') (gL : L' ⟶ L'') (n : ℕ) :
    barMap fR fL n ≫ barMap gR gL n = barMap (fR ≫ gR) (fL ≫ gL) n := by
  ext a
  simp only [barMap_app, NatTrans.comp_app, Algebra.comp_f, Category.assoc]
  have h_swap : fR.f.app ((monadPow T n).obj (L'.functor.obj a)) ≫
      R'.functor.map ((monadPow T n).map (gL.f.app a)) =
      R.functor.map ((monadPow T n).map (gL.f.app a)) ≫
        fR.f.app ((monadPow T n).obj (L''.functor.obj a)) := by
    rw [← fR.f.naturality ((monadPow T n).map (gL.f.app a))]
  calc
    R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
        fR.f.app ((monadPow T n).obj (L'.functor.obj a)) ≫
          R'.functor.map ((monadPow T n).map (gL.f.app a)) ≫
            gR.f.app ((monadPow T n).obj (L''.functor.obj a))
        = R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
            (fR.f.app ((monadPow T n).obj (L'.functor.obj a)) ≫
              R'.functor.map ((monadPow T n).map (gL.f.app a))) ≫
            gR.f.app ((monadPow T n).obj (L''.functor.obj a)) := by
      simp only [Category.assoc]
    _ = R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
            (R.functor.map ((monadPow T n).map (gL.f.app a)) ≫
              fR.f.app ((monadPow T n).obj (L''.functor.obj a))) ≫
            gR.f.app ((monadPow T n).obj (L''.functor.obj a)) := by
      rw [h_swap]
    _ = R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
            R.functor.map ((monadPow T n).map (gL.f.app a)) ≫
            fR.f.app ((monadPow T n).obj (L''.functor.obj a)) ≫
              gR.f.app ((monadPow T n).obj (L''.functor.obj a)) := by
      simp only [Category.assoc]
    _ = (R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
            R.functor.map ((monadPow T n).map (gL.f.app a))) ≫
            fR.f.app ((monadPow T n).obj (L''.functor.obj a)) ≫
              gR.f.app ((monadPow T n).obj (L''.functor.obj a)) := by
      simp only [Category.assoc]
    _ = R.functor.map ((monadPow T n).map (fL.f.app a) ≫
              (monadPow T n).map (gL.f.app a)) ≫
            fR.f.app ((monadPow T n).obj (L''.functor.obj a)) ≫
              gR.f.app ((monadPow T n).obj (L''.functor.obj a)) := by
      rw [← R.functor.map_comp]
    _ = R.functor.map ((monadPow T n).map (fL.f.app a ≫ gL.f.app a)) ≫
            fR.f.app ((monadPow T n).obj (L''.functor.obj a)) ≫
              gR.f.app ((monadPow T n).obj (L''.functor.obj a)) := by
      rw [← (monadPow T n).map_comp]

section DegeneracyComp

theorem barMap_barDegeneracy (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) (i : Fin (n + 1)) :
    barMap fR fL n ≫ barDegeneracy (T := T) (R := R') (L := L') n i =
    barDegeneracy (T := T) (R := R) (L := L) n i ≫ barMap fR fL (n + 1) := by
  ext a
  simp only [barMap_app, barDegeneracy_app, NatTrans.comp_app]
  have h_swap : fR.f.app ((monadPow T n).obj (L'.functor.obj a)) ≫
      R'.functor.map (barEtaAtPos T n i (L'.functor.obj a)) =
      R.functor.map (barEtaAtPos T n i (L'.functor.obj a)) ≫
        fR.f.app ((monadPow T (n + 1)).obj (L'.functor.obj a)) := by
    rw [← fR.f.naturality (barEtaAtPos T n i (L'.functor.obj a))]
  have h_nat_pow : (monadPow T n).map (fL.f.app a) ≫ barEtaAtPos T n i (L'.functor.obj a) =
      barEtaAtPos T n i (L.functor.obj a) ≫ (monadPow T (n + 1)).map (fL.f.app a) :=
    barEtaAtPos_naturality T n i (fL.f.app a)
  calc
    (R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
        fR.f.app ((monadPow T n).obj (L'.functor.obj a))) ≫
        R'.functor.map (barEtaAtPos T n i (L'.functor.obj a))
        = R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
            (fR.f.app ((monadPow T n).obj (L'.functor.obj a)) ≫
              R'.functor.map (barEtaAtPos T n i (L'.functor.obj a))) := by
      rw [Category.assoc]
    _ = R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
            (R.functor.map (barEtaAtPos T n i (L'.functor.obj a)) ≫
              fR.f.app ((monadPow T (n + 1)).obj (L'.functor.obj a))) := by
      rw [h_swap]
    _ = (R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
            R.functor.map (barEtaAtPos T n i (L'.functor.obj a))) ≫
            fR.f.app ((monadPow T (n + 1)).obj (L'.functor.obj a)) := by
      rw [Category.assoc]
    _ = R.functor.map ((monadPow T n).map (fL.f.app a) ≫
              barEtaAtPos T n i (L'.functor.obj a)) ≫
            fR.f.app ((monadPow T (n + 1)).obj (L'.functor.obj a)) := by
      rw [← R.functor.map_comp]
    _ = R.functor.map (barEtaAtPos T n i (L.functor.obj a) ≫
              (monadPow T (n + 1)).map (fL.f.app a)) ≫
            fR.f.app ((monadPow T (n + 1)).obj (L'.functor.obj a)) := by
      rw [h_nat_pow]
    _ = (R.functor.map (barEtaAtPos T n i (L.functor.obj a)) ≫
              R.functor.map ((monadPow T (n + 1)).map (fL.f.app a))) ≫
            fR.f.app ((monadPow T (n + 1)).obj (L'.functor.obj a)) := by
      rw [R.functor.map_comp]
    _ = R.functor.map (barEtaAtPos T n i (L.functor.obj a)) ≫
            (R.functor.map ((monadPow T (n + 1)).map (fL.f.app a)) ≫
              fR.f.app ((monadPow T (n + 1)).obj (L'.functor.obj a))) := by
      rw [Category.assoc]

end DegeneracyComp

section FaceCompZero

theorem barMap_barFace_zero (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) :
    barMap fR fL (n + 1) ≫ barFace (T := T) (R := R') (L := L') n ⟨0, by omega⟩ =
    barFace (T := T) (R := R) (L := L) n ⟨0, by omega⟩ ≫ barMap fR fL n := by
  ext a
  simp only [barMap_app, NatTrans.comp_app, barFace_right]
  have h_fR_right := rightModuleHom_rightActionPow fR n (L'.functor.obj a)
  have h_nat : R.functor.map ((monadPow T (n + 1)).map (fL.f.app a)) ≫
      rightActionPow T R n (L'.functor.obj a) =
      rightActionPow T R n (L.functor.obj a) ≫
        R.functor.map ((monadPow T n).map (fL.f.app a)) :=
    rightActionPow_naturality T R n (fL.f.app a)
  calc
    (R.functor.map ((monadPow T (n + 1)).map (fL.f.app a)) ≫
        fR.f.app ((monadPow T (n + 1)).obj (L'.functor.obj a))) ≫
        rightActionPow T R' n (L'.functor.obj a)
        = R.functor.map ((monadPow T (n + 1)).map (fL.f.app a)) ≫
            (fR.f.app ((monadPow T (n + 1)).obj (L'.functor.obj a)) ≫
              rightActionPow T R' n (L'.functor.obj a)) := by
      rw [Category.assoc]
    _ = R.functor.map ((monadPow T (n + 1)).map (fL.f.app a)) ≫
            (rightActionPow T R n (L'.functor.obj a) ≫
              fR.f.app ((monadPow T n).obj (L'.functor.obj a))) := by
      rw [h_fR_right]
    _ = (R.functor.map ((monadPow T (n + 1)).map (fL.f.app a)) ≫
            rightActionPow T R n (L'.functor.obj a)) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj a)) := by
      rw [Category.assoc]
    _ = (rightActionPow T R n (L.functor.obj a) ≫
            R.functor.map ((monadPow T n).map (fL.f.app a))) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj a)) := by
      rw [h_nat]
    _ = rightActionPow T R n (L.functor.obj a) ≫
            (R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
              fR.f.app ((monadPow T n).obj (L'.functor.obj a))) := by
      rw [Category.assoc]

theorem barMap_barFace_last (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) :
    barMap fR fL (n + 1) ≫ barFace (T := T) (R := R') (L := L') n ⟨n + 1, by omega⟩ =
    barFace (T := T) (R := R) (L := L) n ⟨n + 1, by omega⟩ ≫ barMap fR fL n := by
  ext a
  simp only [barMap_app, NatTrans.comp_app, barFace_left]
  have h_swap : fR.f.app ((monadPow T (n + 1)).obj (L'.functor.obj a)) ≫
      R'.functor.map ((monadPow T n).map (L'.action.app a)) =
      R.functor.map ((monadPow T n).map (L'.action.app a)) ≫
        fR.f.app ((monadPow T n).obj (L'.functor.obj a)) :=
    (fR.f.naturality ((monadPow T n).map (L'.action.app a))).symm
  have hL : T.map (fL.f.app a) ≫ L'.action.app a = L.action.app a ≫ fL.f.app a :=
    LeftModule.hom_condition_app fL a
  calc
    (R.functor.map ((monadPow T (n + 1)).map (fL.f.app a)) ≫
        fR.f.app ((monadPow T (n + 1)).obj (L'.functor.obj a))) ≫
        R'.functor.map ((monadPow T n).map (L'.action.app a))
        = R.functor.map ((monadPow T (n + 1)).map (fL.f.app a)) ≫
            (fR.f.app ((monadPow T (n + 1)).obj (L'.functor.obj a)) ≫
              R'.functor.map ((monadPow T n).map (L'.action.app a))) := by
      rw [Category.assoc]
    _ = R.functor.map ((monadPow T (n + 1)).map (fL.f.app a)) ≫
            (R.functor.map ((monadPow T n).map (L'.action.app a)) ≫
              fR.f.app ((monadPow T n).obj (L'.functor.obj a))) := by
      rw [h_swap]
    _ = (R.functor.map ((monadPow T (n + 1)).map (fL.f.app a)) ≫
            R.functor.map ((monadPow T n).map (L'.action.app a))) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj a)) := by
      rw [Category.assoc]
    _ = R.functor.map ((monadPow T (n + 1)).map (fL.f.app a) ≫
              (monadPow T n).map (L'.action.app a)) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj a)) := by
      rw [← R.functor.map_comp]
    _ = R.functor.map ((monadPow T n).map (T.map (fL.f.app a)) ≫
              (monadPow T n).map (L'.action.app a)) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj a)) := rfl
    _ = R.functor.map ((monadPow T n).map (T.map (fL.f.app a) ≫ L'.action.app a)) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj a)) := by
      rw [← (monadPow T n).map_comp]
    _ = R.functor.map ((monadPow T n).map (L.action.app a ≫ fL.f.app a)) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj a)) := by
      rw [hL]
    _ = (R.functor.map ((monadPow T n).map (L.action.app a)) ≫
              R.functor.map ((monadPow T n).map (fL.f.app a))) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj a)) := by
      rw [(monadPow T n).map_comp, R.functor.map_comp]
    _ = R.functor.map ((monadPow T n).map (L.action.app a)) ≫
            (R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
              fR.f.app ((monadPow T n).obj (L'.functor.obj a))) := by
      rw [Category.assoc]

theorem barMap_barFace_middle (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) (k : Fin n) :
    let i : Fin (n + 2) := ⟨k.val + 1, by omega⟩
    barMap fR fL (n + 1) ≫ barFace (T := T) (R := R') (L := L') n i =
    barFace (T := T) (R := R) (L := L) n i ≫ barMap fR fL n := by
  intro i
  ext a
  have hi_eq : i = ⟨k.val + 1, by omega⟩ := rfl
  have h0 : ¬ (i.val = 0) := by simp [hi_eq]
  have hlast : ¬ (i.val = n + 1) := by simp [hi_eq]; omega
  have h_mid : ∀ {S : RightModule T D} {M : LeftModule A T},
      (barFace (T := T) (R := S) (L := M) n i).app a =
        S.functor.map (barMuAtPos T n k (M.functor.obj a)) := by
    intro S M
    have hk : i.val - 1 < n := by
      have : i.val - 1 = k.val := by simp [hi_eq]
      rw [this]
      exact k.isLt
    have hk_eq : (⟨i.val - 1, hk⟩ : Fin n) = k := by apply Fin.ext; simp [hi_eq]
    have h_app : barFaceApp (T := T) (R := S) (L := M) n i a =
        S.functor.map (barMuAtPos T n ⟨i.val - 1, hk⟩ (M.functor.obj a)) := by
      unfold barFaceApp; rw [dite_eq_right h0, dite_eq_right hlast]
    calc
      (barFace (T := T) (R := S) (L := M) n i).app a = barFaceApp n i a := rfl
      _ = S.functor.map (barMuAtPos T n ⟨i.val - 1, hk⟩ (M.functor.obj a)) := h_app
      _ = S.functor.map (barMuAtPos T n k (M.functor.obj a)) := by rw [hk_eq]
  simp only [barMap_app, NatTrans.comp_app, h_mid]
  have h_fR_swap : fR.f.app ((monadPow T (n + 1)).obj (L'.functor.obj a)) ≫
      R'.functor.map (barMuAtPos T n k (L'.functor.obj a)) =
      R.functor.map (barMuAtPos T n k (L'.functor.obj a)) ≫
        fR.f.app ((monadPow T n).obj (L'.functor.obj a)) :=
    (fR.f.naturality (barMuAtPos T n k (L'.functor.obj a))).symm
  have h_mu_nat : (monadPow T (n + 1)).map (fL.f.app a) ≫ barMuAtPos T n k (L'.functor.obj a) =
      barMuAtPos T n k (L.functor.obj a) ≫ (monadPow T n).map (fL.f.app a) :=
    barMuAtPos_naturality T n k (fL.f.app a)
  calc
    (R.functor.map ((monadPow T (n + 1)).map (fL.f.app a)) ≫
        fR.f.app ((monadPow T (n + 1)).obj (L'.functor.obj a))) ≫
        R'.functor.map (barMuAtPos T n k (L'.functor.obj a))
        = R.functor.map ((monadPow T (n + 1)).map (fL.f.app a)) ≫
            (fR.f.app ((monadPow T (n + 1)).obj (L'.functor.obj a)) ≫
              R'.functor.map (barMuAtPos T n k (L'.functor.obj a))) := by
      rw [Category.assoc]
    _ = R.functor.map ((monadPow T (n + 1)).map (fL.f.app a)) ≫
            (R.functor.map (barMuAtPos T n k (L'.functor.obj a)) ≫
              fR.f.app ((monadPow T n).obj (L'.functor.obj a))) := by
      rw [h_fR_swap]
    _ = (R.functor.map ((monadPow T (n + 1)).map (fL.f.app a)) ≫
            R.functor.map (barMuAtPos T n k (L'.functor.obj a))) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj a)) := by
      rw [Category.assoc]
    _ = R.functor.map ((monadPow T (n + 1)).map (fL.f.app a) ≫
              barMuAtPos T n k (L'.functor.obj a)) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj a)) := by
      rw [← R.functor.map_comp]
    _ = R.functor.map (barMuAtPos T n k (L.functor.obj a) ≫
              (monadPow T n).map (fL.f.app a)) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj a)) := by
      rw [h_mu_nat]
    _ = (R.functor.map (barMuAtPos T n k (L.functor.obj a)) ≫
              R.functor.map ((monadPow T n).map (fL.f.app a))) ≫
            fR.f.app ((monadPow T n).obj (L'.functor.obj a)) := by
      rw [R.functor.map_comp]
    _ = R.functor.map (barMuAtPos T n k (L.functor.obj a)) ≫
            (R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
              fR.f.app ((monadPow T n).obj (L'.functor.obj a))) := by
      rw [Category.assoc]

theorem barMap_barFace (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) (j : Fin (n + 2)) :
    barMap fR fL (n + 1) ≫ barFace (T := T) (R := R') (L := L') n j =
    barFace (T := T) (R := R) (L := L) n j ≫ barMap fR fL n := by
  by_cases h0 : j.val = 0
  · have hj : j = ⟨0, by omega⟩ := by ext; omega
    rw [hj]
    exact barMap_barFace_zero fR fL n
  · by_cases hlast : j.val = n + 1
    · have hj : j = ⟨n + 1, by omega⟩ := by ext; omega
      rw [hj]
      exact barMap_barFace_last fR fL n
    · have hk : j.val - 1 < n := by omega
      let k : Fin n := ⟨j.val - 1, hk⟩
      have hj : j = ⟨k.val + 1, by omega⟩ := by
        apply Fin.ext
        simp only [k]
        omega
      rw [hj]
      exact barMap_barFace_middle fR fL n k

end FaceCompZero

section DataHom

/-- Data-level bar morphism, covariant in both module morphisms. -/
noncomputable def barDataHom (fR : R ⟶ R') (fL : L ⟶ L') :
    barData T R L ⟶ barData T R' L' where
  app n := barMap fR fL n
  w_δ := fun i => barMap_barFace fR fL _ i
  w_σ := fun i => barMap_barDegeneracy fR fL _ i

@[simp]
theorem barDataHom_app (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) :
    (barDataHom fR fL).app n = barMap fR fL n :=
  rfl

@[simp]
theorem barDataHom_app_app (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) (a : A) :
    ((barDataHom fR fL).app n).app a =
      R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
        fR.f.app ((monadPow T n).obj (L'.functor.obj a)) :=
  rfl

@[simp]
theorem barDataHom_id (R : RightModule T D) (L : LeftModule A T) :
    barDataHom (𝟙 R) (𝟙 L) = 𝟙 (barData T R L) := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  simp [barDataHom, barMap_id]

@[simp]
theorem barDataHom_comp {R'' : RightModule T D} {L'' : LeftModule A T}
    (fR : R ⟶ R') (gR : R' ⟶ R'') (fL : L ⟶ L') (gL : L' ⟶ L'') :
    barDataHom fR fL ≫ barDataHom gR gL = barDataHom (fR ≫ gR) (fL ≫ gL) := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  simp [barDataHom, barMap_comp]

end DataHom

section DataIso

variable {R R' : RightModule T D} {L L' : LeftModule A T}

noncomputable def barObjIso (eR : R ≅ R') (eL : L ≅ L') (n : ℕ) :
    barObj T R L n ≅ barObj T R' L' n where
  hom := barMap eR.hom eL.hom n
  inv := barMap eR.inv eL.inv n
  hom_inv_id := by
    calc
      barMap eR.hom eL.hom n ≫ barMap eR.inv eL.inv n
          = barMap (eR.hom ≫ eR.inv) (eL.hom ≫ eL.inv) n := by
            rw [← barMap_comp]
      _ = barMap (𝟙 R) (𝟙 L) n := by
            rw [eR.hom_inv_id, eL.hom_inv_id]
      _ = 𝟙 _ := barMap_id R L n
  inv_hom_id := by
    calc
      barMap eR.inv eL.inv n ≫ barMap eR.hom eL.hom n
          = barMap (eR.inv ≫ eR.hom) (eL.inv ≫ eL.hom) n := by
            rw [← barMap_comp]
      _ = barMap (𝟙 R') (𝟙 L') n := by
            rw [eR.inv_hom_id, eL.inv_hom_id]
      _ = 𝟙 _ := barMap_id R' L' n

@[simp]
theorem barObjIso_hom (eR : R ≅ R') (eL : L ≅ L') (n : ℕ) :
    (barObjIso eR eL n).hom = barMap eR.hom eL.hom n :=
  rfl

@[simp]
theorem barObjIso_inv (eR : R ≅ R') (eL : L ≅ L') (n : ℕ) :
    (barObjIso eR eL n).inv = barMap eR.inv eL.inv n :=
  rfl

@[simp]
theorem barObjIso_hom_app (eR : R ≅ R') (eL : L ≅ L') (n : ℕ) (a : A) :
    (barObjIso eR eL n).hom.app a =
      R.functor.map ((monadPow T n).map (eL.hom.f.app a)) ≫
        eR.hom.f.app ((monadPow T n).obj (L'.functor.obj a)) :=
  rfl

@[simp]
theorem barObjIso_inv_app (eR : R ≅ R') (eL : L ≅ L') (n : ℕ) (a : A) :
    (barObjIso eR eL n).inv.app a =
      R'.functor.map ((monadPow T n).map (eL.inv.f.app a)) ≫
        eR.inv.f.app ((monadPow T n).obj (L.functor.obj a)) :=
  rfl

noncomputable def barDataIso (eR : R ≅ R') (eL : L ≅ L') :
    barData T R L ≅ barData T R' L' where
  hom := barDataHom eR.hom eL.hom
  inv := barDataHom eR.inv eL.inv
  hom_inv_id := by
    calc
      barDataHom eR.hom eL.hom ≫ barDataHom eR.inv eL.inv
          = barDataHom (eR.hom ≫ eR.inv) (eL.hom ≫ eL.inv) := by
            rw [← barDataHom_comp]
      _ = barDataHom (𝟙 R) (𝟙 L) := by
            rw [eR.hom_inv_id, eL.hom_inv_id]
      _ = 𝟙 _ := barDataHom_id R L
  inv_hom_id := by
    calc
      barDataHom eR.inv eL.inv ≫ barDataHom eR.hom eL.hom
          = barDataHom (eR.inv ≫ eR.hom) (eL.inv ≫ eL.hom) := by
            rw [← barDataHom_comp]
      _ = barDataHom (𝟙 R') (𝟙 L') := by
            rw [eR.inv_hom_id, eL.inv_hom_id]
      _ = 𝟙 _ := barDataHom_id R' L'

@[simp]
theorem barDataIso_hom (eR : R ≅ R') (eL : L ≅ L') :
    (barDataIso eR eL).hom = barDataHom eR.hom eL.hom :=
  rfl

@[simp]
theorem barDataIso_inv (eR : R ≅ R') (eL : L ≅ L') :
    (barDataIso eR eL).inv = barDataHom eR.inv eL.inv :=
  rfl

@[simp]
theorem barDataIso_hom_app (eR : R ≅ R') (eL : L ≅ L') (n : ℕ) :
    (barDataIso eR eL).hom.app n = barMap eR.hom eL.hom n :=
  rfl

@[simp]
theorem barDataIso_inv_app (eR : R ≅ R') (eL : L ≅ L') (n : ℕ) :
    (barDataIso eR eL).inv.app n = barMap eR.inv eL.inv n :=
  rfl

@[simp]
theorem barDataIso_hom_app_app (eR : R ≅ R') (eL : L ≅ L') (n : ℕ) (a : A) :
    ((barDataIso eR eL).hom.app n).app a =
      R.functor.map ((monadPow T n).map (eL.hom.f.app a)) ≫
        eR.hom.f.app ((monadPow T n).obj (L'.functor.obj a)) :=
  rfl

@[simp]
theorem barDataIso_inv_app_app (eR : R ≅ R') (eL : L ≅ L') (n : ℕ) (a : A) :
    ((barDataIso eR eL).inv.app n).app a =
      R'.functor.map ((monadPow T n).map (eL.inv.f.app a)) ≫
        eR.inv.f.app ((monadPow T n).obj (L.functor.obj a)) :=
  rfl

end DataIso

section Functor

/-- Bifunctorial data-level two-sided bar on the product of module categories. -/
noncomputable def barDataFunctor (T : Monad C) :
    (RightModule T D) × (LeftModule A T) ⥤ SimplicialObject.Data (A ⥤ D) where
  obj p := barData T p.1 p.2
  map f := barDataHom f.1 f.2
  map_id p := by
    apply SimplicialObject.Data.Hom.ext
    intro n
    simp
  map_comp f g := by
    apply SimplicialObject.Data.Hom.ext
    intro n
    simp

theorem barDataFunctor_obj (T : Monad C) (R : RightModule T D) (L : LeftModule A T) :
    (barDataFunctor T).obj (R, L) = barData T R L :=
  rfl

theorem barDataFunctor_obj_fst_snd (T : Monad C)
    (p : (RightModule T D) × (LeftModule A T)) :
    (barDataFunctor T).obj p = barData T p.1 p.2 :=
  rfl

theorem barDataFunctor_map_app (T : Monad C)
    {p q : (RightModule T D) × (LeftModule A T)} (f : p ⟶ q) (n : ℕ) :
    ((barDataFunctor T).map f).app n = barMap f.1 f.2 n :=
  rfl

theorem barDataFunctor_map_app_app (T : Monad C)
    {p q : (RightModule T D) × (LeftModule A T)} (f : p ⟶ q) (n : ℕ) (a : A) :
    (((barDataFunctor T).map f).app n).app a =
      p.1.functor.map ((monadPow T n).map (f.2.f.app a)) ≫
        f.1.f.app ((monadPow T n).obj (q.2.functor.obj a)) :=
  rfl

@[simp]
theorem barDataFunctor_obj_obj (T : Monad C) (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (a : A) :
    (((barDataFunctor T).obj (R, L)).obj n).obj a =
      R.functor.obj ((monadPow T n).obj (L.functor.obj a)) :=
  rfl

@[simp]
theorem barDataFunctor_map_id_app (T : Monad C)
    (p : (RightModule T D) × (LeftModule A T)) (n : ℕ) :
    ((barDataFunctor T).map (𝟙 p)).app n = 𝟙 _ := by
  simp

end Functor

section GenRel

noncomputable def barGenRelHom {R R' : RightModule T D} {L L' : LeftModule A T}
    (fR : R ⟶ R') (fL : L ⟶ L') :
    barGenRel T R L ⟶ barGenRel T R' L' :=
  SimplicialObject.Data.toGenRelNatTrans (barDataHom fR fL)

theorem barGenRelHom_app_op_mk {R R' : RightModule T D} {L L' : LeftModule A T}
    (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) :
    (barGenRelHom fR fL).app (Opposite.op (SimplexCategoryGenRel.mk n)) = barMap fR fL n := by
  unfold barGenRelHom
  simp only [SimplicialObject.Data.toGenRelNatTrans_app_op_mk, barDataHom_app]
  rfl

theorem barGenRelHom_app_len {R R' : RightModule T D} {L L' : LeftModule A T}
    (fR : R ⟶ R') (fL : L ⟶ L') (q : SimplexCategoryGenRelᵒᵖ) :
    (barGenRelHom fR fL).app q = barMap fR fL (Opposite.unop q).len := by
  unfold barGenRelHom
  simp only [SimplicialObject.Data.toGenRelNatTrans_app_len, barDataHom_app]
  rfl

end GenRel

section GenRelIso

variable {R R' : RightModule T D} {L L' : LeftModule A T}

theorem barGenRelHom_id (R : RightModule T D) (L : LeftModule A T) :
    barGenRelHom (𝟙 R) (𝟙 L) = 𝟙 (barGenRel T R L) := by
  ext q a
  simp only [barGenRelHom_app_len, barMap_id]
  rfl

theorem barGenRelHom_comp {R R' R'' : RightModule T D} {L L' L'' : LeftModule A T}
    (fR : R ⟶ R') (gR : R' ⟶ R'') (fL : L ⟶ L') (gL : L' ⟶ L'') :
    barGenRelHom fR fL ≫ barGenRelHom gR gL =
    barGenRelHom (fR ≫ gR) (fL ≫ gL) := by
  ext q a
  simp only [NatTrans.comp_app, barGenRelHom_app_len]
  calc
    ((barMap fR fL (Opposite.unop q).len).app a ≫ (barMap gR gL (Opposite.unop q).len).app a)
        = ((barMap fR fL (Opposite.unop q).len ≫ barMap gR gL (Opposite.unop q).len).app a) := by
          simp only [NatTrans.comp_app]
    _ = ((barMap (fR ≫ gR) (fL ≫ gL) (Opposite.unop q).len).app a) := by
          rw [barMap_comp]

noncomputable def barGenRelIso (eR : R ≅ R') (eL : L ≅ L') :
    barGenRel T R L ≅ barGenRel T R' L' where
  hom := barGenRelHom eR.hom eL.hom
  inv := barGenRelHom eR.inv eL.inv
  hom_inv_id := by
    calc
      barGenRelHom eR.hom eL.hom ≫ barGenRelHom eR.inv eL.inv
          = barGenRelHom (eR.hom ≫ eR.inv) (eL.hom ≫ eL.inv) := by
            rw [← barGenRelHom_comp]
      _ = barGenRelHom (𝟙 R) (𝟙 L) := by
            rw [eR.hom_inv_id, eL.hom_inv_id]
      _ = 𝟙 _ := barGenRelHom_id R L
  inv_hom_id := by
    calc
      barGenRelHom eR.inv eL.inv ≫ barGenRelHom eR.hom eL.hom
          = barGenRelHom (eR.inv ≫ eR.hom) (eL.inv ≫ eL.hom) := by
            rw [← barGenRelHom_comp]
      _ = barGenRelHom (𝟙 R') (𝟙 L') := by
            rw [eR.inv_hom_id, eL.inv_hom_id]
      _ = 𝟙 _ := barGenRelHom_id R' L'

@[simp]
theorem barGenRelIso_hom (eR : R ≅ R') (eL : L ≅ L') :
    (barGenRelIso eR eL).hom = barGenRelHom eR.hom eL.hom :=
  rfl

@[simp]
theorem barGenRelIso_inv (eR : R ≅ R') (eL : L ≅ L') :
    (barGenRelIso eR eL).inv = barGenRelHom eR.inv eL.inv :=
  rfl

@[simp]
theorem barGenRelIso_hom_app_op_mk (eR : R ≅ R') (eL : L ≅ L') (n : ℕ) :
    (barGenRelIso eR eL).hom.app (Opposite.op (SimplexCategoryGenRel.mk n)) =
      barMap eR.hom eL.hom n :=
  rfl

@[simp]
theorem barGenRelIso_inv_app_op_mk (eR : R ≅ R') (eL : L ≅ L') (n : ℕ) :
    (barGenRelIso eR eL).inv.app (Opposite.op (SimplexCategoryGenRel.mk n)) =
      barMap eR.inv eL.inv n :=
  rfl

@[simp]
theorem barGenRelIso_hom_app_len (eR : R ≅ R') (eL : L ≅ L') (q : SimplexCategoryGenRelᵒᵖ) :
    (barGenRelIso eR eL).hom.app q = barMap eR.hom eL.hom (Opposite.unop q).len :=
  rfl

@[simp]
theorem barGenRelIso_inv_app_len (eR : R ≅ R') (eL : L ≅ L') (q : SimplexCategoryGenRelᵒᵖ) :
    (barGenRelIso eR eL).inv.app q = barMap eR.inv eL.inv (Opposite.unop q).len :=
  rfl

@[simp]
theorem barGenRelIso_hom_app (eR : R ≅ R') (eL : L ≅ L') (q : SimplexCategoryGenRelᵒᵖ) (a : A) :
    ((barGenRelIso eR eL).hom.app q).app a =
      R.functor.map ((monadPow T (Opposite.unop q).len).map (eL.hom.f.app a)) ≫
        eR.hom.f.app ((monadPow T (Opposite.unop q).len).obj (L'.functor.obj a)) :=
  rfl

@[simp]
theorem barGenRelIso_inv_app (eR : R ≅ R') (eL : L ≅ L') (q : SimplexCategoryGenRelᵒᵖ) (a : A) :
    ((barGenRelIso eR eL).inv.app q).app a =
      R'.functor.map ((monadPow T (Opposite.unop q).len).map (eL.inv.f.app a)) ≫
        eR.inv.f.app ((monadPow T (Opposite.unop q).len).obj (L.functor.obj a)) :=
  rfl

end GenRelIso

section TwoSidedBarHomTransport

variable {R R' : RightModule T D} {L L' : LeftModule A T}

/-- Simplicial morphism induced by module homs, via generic `Data` transport. -/
noncomputable def twoSidedBarHom (fR : R ⟶ R') (fL : L ⟶ L') :
    twoSidedBar T R L ⟶ twoSidedBar T R' L' :=
  SimplicialObject.Data.toSimplicialNatTrans (barDataHom fR fL)

@[simp]
theorem twoSidedBarHom_app_op_mk (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) :
    (twoSidedBarHom fR fL).app (Opposite.op (SimplexCategory.mk n)) = barMap fR fL n :=
  rfl

theorem twoSidedBarHom_app (fR : R ⟶ R') (fL : L ⟶ L') (Δ : SimplexCategoryᵒᵖ) :
    (twoSidedBarHom fR fL).app Δ = barMap fR fL (Opposite.unop Δ).len := by
  obtain ⟨Δ⟩ := Δ
  rfl

@[simp]
theorem twoSidedBarHom_app_len (fR : R ⟶ R') (fL : L ⟶ L') (Δ : SimplexCategoryᵒᵖ) :
    (twoSidedBarHom fR fL).app Δ = barMap fR fL (Opposite.unop Δ).len :=
  twoSidedBarHom_app fR fL Δ

@[simp]
theorem twoSidedBarHom_app_app_op_mk (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) (a : A) :
    ((twoSidedBarHom fR fL).app (Opposite.op (SimplexCategory.mk n))).app a =
      R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
        fR.f.app ((monadPow T n).obj (L'.functor.obj a)) :=
  rfl

theorem twoSidedBarHom_app_app (fR : R ⟶ R') (fL : L ⟶ L') (Δ : SimplexCategoryᵒᵖ) (a : A) :
    ((twoSidedBarHom fR fL).app Δ).app a =
      R.functor.map ((monadPow T (Opposite.unop Δ).len).map (fL.f.app a)) ≫
        fR.f.app ((monadPow T (Opposite.unop Δ).len).obj (L'.functor.obj a)) := by
  obtain ⟨Δ⟩ := Δ
  rfl

theorem twoSidedBarHom_id (R : RightModule T D) (L : LeftModule A T) :
    twoSidedBarHom (𝟙 R) (𝟙 L) = 𝟙 (twoSidedBar T R L) := by
  ext Δ a
  simp only [twoSidedBarHom_app, barMap_id]
  rfl

theorem twoSidedBarHom_comp {R R' R'' : RightModule T D} {L L' L'' : LeftModule A T}
    (fR : R ⟶ R') (gR : R' ⟶ R'') (fL : L ⟶ L') (gL : L' ⟶ L'') :
    twoSidedBarHom fR fL ≫ twoSidedBarHom gR gL =
      twoSidedBarHom (fR ≫ gR) (fL ≫ gL) := by
  ext Δ a
  simp only [NatTrans.comp_app, twoSidedBarHom_app]
  calc
    (barMap fR fL (Opposite.unop Δ).len).app a ≫
        (barMap gR gL (Opposite.unop Δ).len).app a
        = (barMap fR fL (Opposite.unop Δ).len ≫
          barMap gR gL (Opposite.unop Δ).len).app a := by
            simp only [NatTrans.comp_app]
    _ = (barMap (fR ≫ gR) (fL ≫ gL) (Opposite.unop Δ).len).app a := by
            rw [barMap_comp]

end TwoSidedBarHomTransport

section TwoSidedBarIsoTransport

variable {R R' : RightModule T D} {L L' : LeftModule A T}

noncomputable def twoSidedBarIso (eR : R ≅ R') (eL : L ≅ L') :
    twoSidedBar T R L ≅ twoSidedBar T R' L' where
  hom := twoSidedBarHom eR.hom eL.hom
  inv := twoSidedBarHom eR.inv eL.inv
  hom_inv_id := by
    calc
      twoSidedBarHom eR.hom eL.hom ≫ twoSidedBarHom eR.inv eL.inv
          = twoSidedBarHom (eR.hom ≫ eR.inv) (eL.hom ≫ eL.inv) := by
            rw [← twoSidedBarHom_comp]
      _ = twoSidedBarHom (𝟙 R) (𝟙 L) := by
            rw [eR.hom_inv_id, eL.hom_inv_id]
      _ = 𝟙 _ := twoSidedBarHom_id R L
  inv_hom_id := by
    calc
      twoSidedBarHom eR.inv eL.inv ≫ twoSidedBarHom eR.hom eL.hom
          = twoSidedBarHom (eR.inv ≫ eR.hom) (eL.inv ≫ eL.hom) := by
            rw [← twoSidedBarHom_comp]
      _ = twoSidedBarHom (𝟙 R') (𝟙 L') := by
            rw [eR.inv_hom_id, eL.inv_hom_id]
      _ = 𝟙 _ := twoSidedBarHom_id R' L'

@[simp]
theorem twoSidedBarIso_hom (eR : R ≅ R') (eL : L ≅ L') :
    (twoSidedBarIso eR eL).hom = twoSidedBarHom eR.hom eL.hom :=
  rfl

@[simp]
theorem twoSidedBarIso_inv (eR : R ≅ R') (eL : L ≅ L') :
    (twoSidedBarIso eR eL).inv = twoSidedBarHom eR.inv eL.inv :=
  rfl

@[simp]
theorem twoSidedBarIso_hom_app_op_mk (eR : R ≅ R') (eL : L ≅ L') (n : ℕ) :
    (twoSidedBarIso eR eL).hom.app (Opposite.op (SimplexCategory.mk n)) =
      barMap eR.hom eL.hom n :=
  rfl

@[simp]
theorem twoSidedBarIso_inv_app_op_mk (eR : R ≅ R') (eL : L ≅ L') (n : ℕ) :
    (twoSidedBarIso eR eL).inv.app (Opposite.op (SimplexCategory.mk n)) =
      barMap eR.inv eL.inv n :=
  rfl

theorem twoSidedBarIso_hom_app_len (eR : R ≅ R') (eL : L ≅ L') (Δ : SimplexCategoryᵒᵖ) :
    (twoSidedBarIso eR eL).hom.app Δ = barMap eR.hom eL.hom (Opposite.unop Δ).len :=
  twoSidedBarHom_app eR.hom eL.hom Δ

theorem twoSidedBarIso_inv_app_len (eR : R ≅ R') (eL : L ≅ L') (Δ : SimplexCategoryᵒᵖ) :
    (twoSidedBarIso eR eL).inv.app Δ = barMap eR.inv eL.inv (Opposite.unop Δ).len :=
  twoSidedBarHom_app eR.inv eL.inv Δ

@[simp]
theorem twoSidedBarIso_hom_app (eR : R ≅ R') (eL : L ≅ L') (Δ : SimplexCategoryᵒᵖ) (a : A) :
    ((twoSidedBarIso eR eL).hom.app Δ).app a =
      R.functor.map ((monadPow T (Opposite.unop Δ).len).map (eL.hom.f.app a)) ≫
        eR.hom.f.app ((monadPow T (Opposite.unop Δ).len).obj (L'.functor.obj a)) := by
  obtain ⟨Δ⟩ := Δ
  rfl

@[simp]
theorem twoSidedBarIso_inv_app (eR : R ≅ R') (eL : L ≅ L') (Δ : SimplexCategoryᵒᵖ) (a : A) :
    ((twoSidedBarIso eR eL).inv.app Δ).app a =
      R'.functor.map ((monadPow T (Opposite.unop Δ).len).map (eL.inv.f.app a)) ≫
        eR.inv.f.app ((monadPow T (Opposite.unop Δ).len).obj (L.functor.obj a)) := by
  obtain ⟨Δ⟩ := Δ
  rfl

end TwoSidedBarIsoTransport

section TwoSidedBarFunctorTransport

/-- Bifunctorial two-sided bar, as composite of data-level functor and generic transport. -/
noncomputable def twoSidedBarFunctor (T : Monad C) :
    (RightModule T D) × (LeftModule A T) ⥤ SimplicialObject (A ⥤ D) :=
  barDataFunctor T ⋙ SimplicialObject.Data.toSimplicialFunctor

@[simp]
theorem twoSidedBarFunctor_obj (T : Monad C) (R : RightModule T D) (L : LeftModule A T) :
    (twoSidedBarFunctor T).obj (R, L) = twoSidedBar T R L :=
  rfl

theorem twoSidedBarFunctor_obj_fst_snd (T : Monad C)
    (p : (RightModule T D) × (LeftModule A T)) :
    (twoSidedBarFunctor T).obj p = twoSidedBar T p.1 p.2 := by
  obtain ⟨R, L⟩ := p
  rfl

@[simp]
theorem twoSidedBarFunctor_map (T : Monad C)
    {p q : (RightModule T D) × (LeftModule A T)} (f : p ⟶ q) :
    (twoSidedBarFunctor T).map f = twoSidedBarHom f.1 f.2 :=
  rfl

@[simp]
theorem twoSidedBarFunctor_obj_obj_op_mk (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) :
    ((twoSidedBarFunctor T).obj (R, L)).obj (Opposite.op (SimplexCategory.mk n)) =
      barObj T R L n :=
  rfl

theorem twoSidedBarFunctor_obj_obj (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) (Δ : SimplexCategoryᵒᵖ) :
    ((twoSidedBarFunctor T).obj (R, L)).obj Δ = barObj T R L (Opposite.unop Δ).len := by
  obtain ⟨Δ⟩ := Δ
  rfl

@[simp]
theorem twoSidedBarFunctor_obj_obj_op_mk_obj (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) (a : A) :
    (((twoSidedBarFunctor T).obj (R, L)).obj (Opposite.op (SimplexCategory.mk n))).obj a =
      R.functor.obj ((monadPow T n).obj (L.functor.obj a)) :=
  rfl

theorem twoSidedBarFunctor_obj_obj_obj (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) (Δ : SimplexCategoryᵒᵖ) (a : A) :
    (((twoSidedBarFunctor T).obj (R, L)).obj Δ).obj a =
      R.functor.obj ((monadPow T (Opposite.unop Δ).len).obj (L.functor.obj a)) := by
  obtain ⟨Δ⟩ := Δ
  rfl

@[simp]
theorem twoSidedBarFunctor_map_app_op_mk (T : Monad C)
    {p q : (RightModule T D) × (LeftModule A T)} (f : p ⟶ q) (n : ℕ) :
    ((twoSidedBarFunctor T).map f).app (Opposite.op (SimplexCategory.mk n)) = barMap f.1 f.2 n :=
  rfl

theorem twoSidedBarFunctor_map_app_len (T : Monad C)
    {p q : (RightModule T D) × (LeftModule A T)} (f : p ⟶ q) (Δ : SimplexCategoryᵒᵖ) :
    ((twoSidedBarFunctor T).map f).app Δ = barMap f.1 f.2 (Opposite.unop Δ).len := by
  obtain ⟨Δ⟩ := Δ
  rfl

@[simp]
theorem twoSidedBarFunctor_map_app (T : Monad C)
    {p q : (RightModule T D) × (LeftModule A T)} (f : p ⟶ q) (Δ : SimplexCategoryᵒᵖ) :
    ((twoSidedBarFunctor T).map f).app Δ = barMap f.1 f.2 (Opposite.unop Δ).len :=
  twoSidedBarFunctor_map_app_len T f Δ

theorem twoSidedBarFunctor_map_app_app (T : Monad C)
    {p q : (RightModule T D) × (LeftModule A T)} (f : p ⟶ q) (Δ : SimplexCategoryᵒᵖ) (a : A) :
    (((twoSidedBarFunctor T).map f).app Δ).app a =
      p.1.functor.map ((monadPow T (Opposite.unop Δ).len).map (f.2.f.app a)) ≫
        f.1.f.app ((monadPow T (Opposite.unop Δ).len).obj (q.2.functor.obj a)) := by
  obtain ⟨Δ⟩ := Δ
  rfl

end TwoSidedBarFunctorTransport

section RightPostcompOuter

universe v₄ u₄

variable {E : Type u₄} [Category.{v₄} E]
variable (K : D ⥤ E)

/--
Outer target postcomposition whiskering by `K : D ⥤ E`.

Thin alias for Mathlib's `(Functor.whiskeringRight _ _ _).obj K`; the previous
explicit structure is deleted to avoid duplicate ambient coherence.
-/
abbrev functorPostcompOuter : (A ⥤ D) ⥤ (A ⥤ E) :=
  (Functor.whiskeringRight A D E).obj K

@[simp]
theorem functorPostcompOuter_map_app {F G : A ⥤ D} (f : F ⟶ G) (a : A) :
    ((functorPostcompOuter K).map f).app a = K.map (f.app a) := rfl

theorem rightActionPow_postcomp (R : RightModule T D) (n : ℕ) (X : C) :
    rightActionPow T (R.postcomp K) n X = K.map (rightActionPow T R n X) := by
  induction n generalizing X with
  | zero =>
    rfl
  | succ n ih =>
    exact ih (T.obj X)

theorem barObj_postcomp (R : RightModule T D) (L : LeftModule A T) (n : ℕ) :
    barObj T (R.postcomp K) L n = barObj T R L n ⋙ K := rfl

theorem barFaceApp_postcomp (R : RightModule T D) (L : LeftModule A T) (n : ℕ)
    (i : Fin (n + 2)) (a : A) :
    barFaceApp (T := T) (R := R.postcomp K) (L := L) n i a =
      K.map (barFaceApp (T := T) (R := R) (L := L) n i a) := by
  unfold barFaceApp
  by_cases h0 : i.val = 0
  · simp only [dite_eq_left h0]
    exact rightActionPow_postcomp K R n (L.functor.obj a)
  · simp only [dite_eq_right h0]
    by_cases hlast : i.val = n + 1
    · simp only [dite_eq_left hlast]
      rfl
    · simp only [dite_eq_right hlast]
      rfl

theorem barDegeneracyApp_postcomp (R : RightModule T D) (L : LeftModule A T) (n : ℕ)
    (i : Fin (n + 1)) (a : A) :
    (barDegeneracy (T := T) (R := R.postcomp K) (L := L) n i).app a =
      K.map ((barDegeneracy (T := T) (R := R) (L := L) n i).app a) := rfl

theorem barFace_postcomp (R : RightModule T D) (L : LeftModule A T) (n : ℕ)
    (i : Fin (n + 2)) :
    barFace (T := T) (R := R.postcomp K) (L := L) n i =
      Functor.whiskerRight (barFace (T := T) (R := R) (L := L) n i) K := by
  ext a
  simp only [barFace, Functor.whiskerRight_app]
  exact barFaceApp_postcomp K R L n i a

theorem barDegeneracy_postcomp (R : RightModule T D) (L : LeftModule A T) (n : ℕ)
    (i : Fin (n + 1)) :
    barDegeneracy (T := T) (R := R.postcomp K) (L := L) n i =
      Functor.whiskerRight (barDegeneracy (T := T) (R := R) (L := L) n i) K := by
  ext a
  simp only [barDegeneracy, Functor.whiskerRight_app]
  rfl

section PostcompIso

/-- Degreewise target-postcomposition comparison, as the functor associator. -/
noncomputable def barDataPostcompOuterIsoObj (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) :
    (SimplicialObject.Data.mapObj (functorPostcompOuter (E := E) K) (barData T R L)).obj n ≅
      (barData T (R.postcomp K) L).obj n :=
  Functor.associator (L.functor ⋙ monadPow T n) R.functor K

@[simp]
theorem barDataPostcompOuterIsoObj_hom (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) :
    (barDataPostcompOuterIsoObj (E := E) K R L n).hom =
      (Functor.associator (L.functor ⋙ monadPow T n) R.functor K).hom := rfl

@[simp]
theorem barDataPostcompOuterIsoObj_inv (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) :
    (barDataPostcompOuterIsoObj (E := E) K R L n).inv =
      (Functor.associator (L.functor ⋙ monadPow T n) R.functor K).inv := rfl

@[simp]
theorem barDataPostcompOuterIsoObj_hom_app (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (a : A) :
    (barDataPostcompOuterIsoObj (E := E) K R L n).hom.app a =
      (Functor.associator (L.functor ⋙ monadPow T n) R.functor K).hom.app a := rfl

@[simp]
theorem barDataPostcompOuterIsoObj_inv_app (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (a : A) :
    (barDataPostcompOuterIsoObj (E := E) K R L n).inv.app a =
      (Functor.associator (L.functor ⋙ monadPow T n) R.functor K).inv.app a := rfl

/--
Data-level target-postcomposition comparison, assembled from the associator
degreewise isomorphism with the generic degreewise-isomorphism infrastructure.
No simplicial identity is reproved here.
-/
noncomputable def barDataPostcompOuterIso (R : RightModule T D) (L : LeftModule A T) :
    SimplicialObject.Data.mapObj (functorPostcompOuter (E := E) K) (barData T R L) ≅
      barData T (R.postcomp K) L :=
  SimplicialObject.Data.isoOfIso (barDataPostcompOuterIsoObj (E := E) K R L)
    (by
      intro n i
      ext a
      simp [SimplicialObject.Data.mapObj_δ, barData_δ, barFace_postcomp,
        barDataPostcompOuterIsoObj, Functor.associator, functorPostcompOuter])
    (by
      intro n i
      ext a
      simp [SimplicialObject.Data.mapObj_σ, barData_σ, barDegeneracy_postcomp,
        barDataPostcompOuterIsoObj, Functor.associator, functorPostcompOuter])

@[simp]
theorem barDataPostcompOuterIso_hom_app (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) :
    (barDataPostcompOuterIso (E := E) K R L).hom.app n =
      (Functor.associator (L.functor ⋙ monadPow T n) R.functor K).hom := rfl

@[simp]
theorem barDataPostcompOuterIso_inv_app (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) :
    (barDataPostcompOuterIso (E := E) K R L).inv.app n =
      (Functor.associator (L.functor ⋙ monadPow T n) R.functor K).inv := rfl

@[simp]
theorem barDataPostcompOuterIso_hom_app_app (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (a : A) :
    ((barDataPostcompOuterIso (E := E) K R L).hom.app n).app a =
      (Functor.associator (L.functor ⋙ monadPow T n) R.functor K).hom.app a := rfl

@[simp]
theorem barDataPostcompOuterIso_inv_app_app (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (a : A) :
    ((barDataPostcompOuterIso (E := E) K R L).inv.app n).app a =
      (Functor.associator (L.functor ⋙ monadPow T n) R.functor K).inv.app a := rfl

end PostcompIso

section PostcompSimplicial

/--
Simplicial target-postcomposition comparison, obtained functorially from `barDataPostcompOuterIso`
via `Data.toSimplicialFunctor`. Covariant in both modules; postcomposition is outer whiskering in
the target.  This is the `K`-postcomposition of the bar compared with the bar of the postcomposed
right module.
-/
noncomputable def twoSidedBarPostcompOuterIso (R : RightModule T D)
    (L : LeftModule A T) :
    (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ E)).obj
        (SimplicialObject.Data.mapObj (functorPostcompOuter (E := E) K)
          (barData T R L)) ≅
      twoSidedBar T (R.postcomp K) L :=
  (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ E)).mapIso
    (barDataPostcompOuterIso (E := E) K R L)

@[simp]
theorem twoSidedBarPostcompOuterIso_hom (R : RightModule T D) (L : LeftModule A T) :
    (twoSidedBarPostcompOuterIso (E := E) K R L).hom =
      (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ E)).map
        (barDataPostcompOuterIso (E := E) K R L).hom :=
  rfl

@[simp]
theorem twoSidedBarPostcompOuterIso_inv (R : RightModule T D) (L : LeftModule A T) :
    (twoSidedBarPostcompOuterIso (E := E) K R L).inv =
      (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ E)).map
        (barDataPostcompOuterIso (E := E) K R L).inv :=
  rfl

@[simp]
theorem twoSidedBarPostcompOuterIso_hom_app_op_mk (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) :
    (twoSidedBarPostcompOuterIso (E := E) K R L).hom.app
        (Opposite.op (SimplexCategory.mk n)) =
      (barDataPostcompOuterIsoObj (E := E) K R L n).hom :=
  rfl

@[simp]
theorem twoSidedBarPostcompOuterIso_inv_app_op_mk (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) :
    (twoSidedBarPostcompOuterIso (E := E) K R L).inv.app
        (Opposite.op (SimplexCategory.mk n)) =
      (barDataPostcompOuterIsoObj (E := E) K R L n).inv :=
  rfl

end PostcompSimplicial

section PostcompWhisker

/--
Target-postcomposition comparison with whiskered source.

The source is literally the whiskered bar `twoSidedBar T R L ⋙ functorPostcompOuter K`, not
`toSimplicialFunctor.obj (Data.mapObj _ _)`. It composes the generic
`toSimplicialFunctor_mapFunctorIso` bridge with the transport of the data-level
`barDataPostcompOuterIso` (functor associator orientation preserved).
-/
noncomputable def twoSidedBarPostcompWhiskerIso (R : RightModule T D)
    (L : LeftModule A T) :
    (twoSidedBar T R L ⋙ functorPostcompOuter (E := E) K) ≅
      twoSidedBar T (R.postcomp K) L :=
  (SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso
    (functorPostcompOuter (E := E) K)).app (barData T R L) ≪≫
    twoSidedBarPostcompOuterIso (E := E) K R L

@[simp]
theorem twoSidedBarPostcompWhiskerIso_hom_app_op_mk (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) :
    (twoSidedBarPostcompWhiskerIso (E := E) K R L).hom.app
        (Opposite.op (SimplexCategory.mk n)) =
      (barDataPostcompOuterIsoObj (E := E) K R L n).hom := by
  ext a
  have hBridgeApp :
      ((((SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso
        (functorPostcompOuter (E := E) K)).app
          (barData T R L)).hom.app
        (Opposite.op (SimplexCategory.mk n))).app a) = 𝟙 _ := by
    have h :=
      SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso_hom_app_app_mk
        (functorPostcompOuter (E := E) K) (barData T R L) n
    exact congrArg (fun h => h.app a) h
  have hOuterApp :
      (((twoSidedBarPostcompOuterIso (E := E) K R L).hom.app
        (Opposite.op (SimplexCategory.mk n))).app a) = 𝟙 _ := by
    simp
  have hRhs :
      ((barDataPostcompOuterIsoObj (E := E) K R L n).hom.app a) = 𝟙 _ := by
    simp
  have hComp :
      (((twoSidedBarPostcompWhiskerIso (E := E) K R L).hom.app
        (Opposite.op (SimplexCategory.mk n))).app a) =
      (((((SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso
        (functorPostcompOuter (E := E) K)).app
          (barData T R L)).hom.app
        (Opposite.op (SimplexCategory.mk n))).app a) ≫
      (((twoSidedBarPostcompOuterIso (E := E) K R L).hom.app
        (Opposite.op (SimplexCategory.mk n))).app a)) := rfl
  rw [hComp, hBridgeApp, hOuterApp, hRhs]
  exact Category.id_comp _

@[simp]
theorem twoSidedBarPostcompWhiskerIso_inv_app_op_mk (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) :
    (twoSidedBarPostcompWhiskerIso (E := E) K R L).inv.app
        (Opposite.op (SimplexCategory.mk n)) =
      (barDataPostcompOuterIsoObj (E := E) K R L n).inv := by
  ext a
  have hBridgeInv :
      ((((SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso
        (functorPostcompOuter (E := E) K)).app
          (barData T R L)).inv.app
        (Opposite.op (SimplexCategory.mk n))).app a) = 𝟙 _ := by
    have h :=
      SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso_inv_app_app_mk
        (functorPostcompOuter (E := E) K) (barData T R L) n
    exact congrArg (fun h => h.app a) h
  have hOuterInv :
      (((twoSidedBarPostcompOuterIso (E := E) K R L).inv.app
        (Opposite.op (SimplexCategory.mk n))).app a) = 𝟙 _ := by
    simp
  have hRhsInv :
      ((barDataPostcompOuterIsoObj (E := E) K R L n).inv.app a) = 𝟙 _ := by
    simp
  have hComp :
      (((twoSidedBarPostcompWhiskerIso (E := E) K R L).inv.app
        (Opposite.op (SimplexCategory.mk n))).app a) =
      (((twoSidedBarPostcompOuterIso (E := E) K R L).inv.app
        (Opposite.op (SimplexCategory.mk n))).app a ≫
      ((((SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso
        (functorPostcompOuter (E := E) K)).app
          (barData T R L)).inv.app
        (Opposite.op (SimplexCategory.mk n))).app a)) := rfl
  rw [hComp, hOuterInv, hBridgeInv, hRhsInv]
  exact Category.id_comp _

/--
Smallest robust naturality in module maps, at `op (mk n)` components.

Whiskered maps commute with the whisker comparison; the postcomposed right-module map is
`(RightModule.postcompFunctor K).map fR`. This component naturality is reused by the product-level
`twoSidedBarPostcompWhiskerNatIso`; identity/composition coherence in `K` is proved at components
in `PostcompProductNaturality` (all components are identities, so the associator triangle/pentagon
close by `simp`).
-/
theorem twoSidedBarPostcompWhiskerIso_naturality_app_op_mk
    {R R' : RightModule T D} {L L' : LeftModule A T}
    (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) :
    (((SimplicialObject.whiskering _ _).obj
      (functorPostcompOuter (E := E) K)).map
        (twoSidedBarHom fR fL)).app (Opposite.op (SimplexCategory.mk n)) ≫
      (twoSidedBarPostcompWhiskerIso (E := E) K R' L').hom.app
        (Opposite.op (SimplexCategory.mk n)) =
      (twoSidedBarPostcompWhiskerIso (E := E) K R L).hom.app
        (Opposite.op (SimplexCategory.mk n)) ≫
      (twoSidedBarHom ((RightModule.postcompFunctor K).map fR) fL).app
        (Opposite.op (SimplexCategory.mk n)) := by
  ext a
  change (((((SimplicialObject.whiskering (A ⥤ D) (A ⥤ E)).obj
      (functorPostcompOuter K)).map (twoSidedBarHom fR fL)).app
        (Opposite.op (SimplexCategory.mk n))).app a ≫
      (((twoSidedBarPostcompWhiskerIso K R' L').hom.app
        (Opposite.op (SimplexCategory.mk n))).app a)) =
    ((((twoSidedBarPostcompWhiskerIso K R L).hom.app
        (Opposite.op (SimplexCategory.mk n))).app a) ≫
      (((twoSidedBarHom ((RightModule.postcompFunctor K).map fR) fL).app
        (Opposite.op (SimplexCategory.mk n))).app a))
  simp only [Functor.whiskeringRight_obj_map, twoSidedBarHom_app_app_op_mk,
    Functor.whiskerRight_app, RightModule.postcomp_functor_map,
    twoSidedBarPostcompWhiskerIso_hom_app_op_mk,
    barDataPostcompOuterIsoObj_hom_app, Functor.associator_hom_app]
  have e : K.map (R.functor.map ((T.monadPow n).map (fL.f.app a)) ≫
      fR.f.app ((T.monadPow n).obj (L'.functor.obj a))) =
      K.map (R.functor.map ((T.monadPow n).map (fL.f.app a))) ≫
        K.map (fR.f.app ((T.monadPow n).obj (L'.functor.obj a))) :=
    Functor.map_comp _ _ _
  exact (congrArg (· ≫ _) e).trans
    ((Category.comp_id _).trans (Category.id_comp _).symm)

end PostcompWhisker

section PostcompProductNaturality

/-- Every simplicial opposite object is `op (mk len)`. -/
private theorem twoSidedBarOpMkLen (Δ : SimplexCategoryᵒᵖ) :
    Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) := by
  obtain ⟨d⟩ := Δ
  exact congrArg Opposite.op (SimplexCategory.mk_len d).symm

/-- Left whisker functor for product naturality: bar then target whiskering. -/
noncomputable def twoSidedBarPostcompWhiskerFunctorLeft :
    (RightModule T D × LeftModule A T) ⥤ SimplicialObject (A ⥤ E) :=
  twoSidedBarFunctor T ⋙
    (SimplicialObject.whiskering (A ⥤ D) (A ⥤ E)).obj
      (functorPostcompOuter (E := E) K)

/-- Right whisker functor: module postcomposition then bar. -/
noncomputable def twoSidedBarPostcompWhiskerFunctorRight :
    (RightModule T D × LeftModule A T) ⥤ SimplicialObject (A ⥤ E) :=
  (RightModule.postcompFunctor (T := T) K).prod (𝟭 (LeftModule A T)) ⋙
    twoSidedBarFunctor T

/-- Naturality at a general opposite simplex object, reduced to `mk` components. -/
theorem twoSidedBarPostcompWhiskerIso_naturality_app
    {R R' : RightModule T D} {L L' : LeftModule A T}
    (fR : R ⟶ R') (fL : L ⟶ L') (Δ : SimplexCategoryᵒᵖ) :
    (((SimplicialObject.whiskering (A ⥤ D) (A ⥤ E)).obj
      (functorPostcompOuter (E := E) K)).map
        (twoSidedBarHom fR fL)).app Δ ≫
      (twoSidedBarPostcompWhiskerIso (E := E) K R' L').hom.app Δ =
      (twoSidedBarPostcompWhiskerIso (E := E) K R L).hom.app Δ ≫
      (twoSidedBarHom ((RightModule.postcompFunctor K).map fR) fL).app Δ := by
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) :=
    twoSidedBarOpMkLen Δ
  rw [hΔ]
  exact twoSidedBarPostcompWhiskerIso_naturality_app_op_mk (E := E) K fR fL _

/--
Genuinely natural target-postcomposition whisker isomorphism over the
product of module categories, reusing the degreewise associator isos and
component naturality.
-/
noncomputable def twoSidedBarPostcompWhiskerNatIso :
    twoSidedBarPostcompWhiskerFunctorLeft (T := T) (A := A) (E := E) K ≅
      twoSidedBarPostcompWhiskerFunctorRight (T := T) (A := A) (E := E) K :=
  NatIso.ofComponents
    (fun p => twoSidedBarPostcompWhiskerIso (E := E) K p.1 p.2)
    (by
      intro p q f
      obtain ⟨R, L⟩ := p
      obtain ⟨R', L'⟩ := q
      obtain ⟨fR, fL⟩ := f
      apply NatTrans.ext
      funext Δ
      exact twoSidedBarPostcompWhiskerIso_naturality_app (E := E) K fR fL Δ)

@[simp]
theorem twoSidedBarPostcompWhiskerNatIso_hom_app (p : RightModule T D × LeftModule A T)
    (Δ : SimplexCategoryᵒᵖ) :
    ((twoSidedBarPostcompWhiskerNatIso (E := E) K).hom.app p).app Δ =
      (twoSidedBarPostcompWhiskerIso (E := E) K p.1 p.2).hom.app Δ := rfl

@[simp]
theorem twoSidedBarPostcompWhiskerNatIso_inv_app (p : RightModule T D × LeftModule A T)
    (Δ : SimplexCategoryᵒᵖ) :
    ((twoSidedBarPostcompWhiskerNatIso (E := E) K).inv.app p).app Δ =
      (twoSidedBarPostcompWhiskerIso (E := E) K p.1 p.2).inv.app Δ := rfl

/--
Whisker comparison components are identities at `app a`: the associator
has identity components, so Mathlib's triangle/pentagon close by `simp`.
-/
@[simp]
theorem twoSidedBarPostcompWhiskerIso_hom_app_app_id
    (R : RightModule T D) (L : LeftModule A T) (n : ℕ) (a : A) :
    (((twoSidedBarPostcompWhiskerIso (E := E) K R L).hom.app
      (Opposite.op (SimplexCategory.mk n))).app a) = 𝟙 _ := by
  simp [twoSidedBarPostcompWhiskerIso_hom_app_op_mk, barDataPostcompOuterIsoObj]

@[simp]
theorem twoSidedBarPostcompWhiskerIso_inv_app_app_id
    (R : RightModule T D) (L : LeftModule A T) (n : ℕ) (a : A) :
    (((twoSidedBarPostcompWhiskerIso (E := E) K R L).inv.app
      (Opposite.op (SimplexCategory.mk n))).app a) = 𝟙 _ := by
  simp [twoSidedBarPostcompWhiskerIso_inv_app_op_mk, barDataPostcompOuterIsoObj]

universe v₅ u₅

variable {F : Type u₅} [Category.{v₅} F]

/--
Degree-`n` component of identity whisker coherence.

The identity whisker followed by the module-side `postcompId` bridge is the
identity at `op (mk n)`; see `twoSidedBarPostcompWhiskerNatIso_id` for the
functor-level statement. Together with the categorical
`functorPostcompOuterId` and `twoSidedBarIso_postcompId_hom_app` identities,
this is the associator triangle; no pseudofunctor is built.
-/
theorem twoSidedBarPostcompWhiskerIso_id_hom_app
    (R : RightModule T D) (L : LeftModule A T) (n : ℕ) :
    (twoSidedBarPostcompWhiskerIso (E := D) (𝟭 D) R L).hom.app
      (Opposite.op (SimplexCategory.mk n)) ≫
    (twoSidedBarIso ((RightModule.postcompId).app R) (Iso.refl L)).hom.app
      (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ := by
  ext a
  simp

/--
Identity whisker coherence at components, derived from the degree-`n`
`twoSidedBarPostcompWhiskerIso_id_hom_app` equality.
-/
theorem twoSidedBarPostcompWhiskerIso_id_hom_app_app
    (R : RightModule T D) (L : LeftModule A T) (n : ℕ) (a : A) :
    (((twoSidedBarPostcompWhiskerIso (E := D) (𝟭 D) R L).hom.app
      (Opposite.op (SimplexCategory.mk n))).app a) ≫
    (((twoSidedBarIso ((RightModule.postcompId).app R) (Iso.refl L)).hom.app
      (Opposite.op (SimplexCategory.mk n))).app a) = 𝟙 _ := by
  have h := twoSidedBarPostcompWhiskerIso_id_hom_app (T := T) R L n
  exact congrArg (fun α => α.app a) h

/--
Degree-`n` component of composition whisker coherence, with the
orientation `postcomp K ⋙ postcomp Q ≅ postcomp (K ⋙ Q)`.

The `Q`-whiskering of the `K` comparison, followed by the `Q` comparison and
the module-side `postcompComp` bridge, coincides with the single `K ⋙ Q`
comparison at `op (mk n)`; see `twoSidedBarPostcompWhiskerNatIso_comp` for the
functor-level statement. All sides have identity components, so Mathlib's
associator pentagon closes by `simp`; the ambient
`functorPostcompOuterComp` bridge is likewise componentwise identity.
-/
theorem twoSidedBarPostcompWhiskerIso_comp_hom_app
    (R : RightModule T D) (L : LeftModule A T) (Q : E ⥤ F) (n : ℕ) :
    (functorPostcompOuter Q).map
        ((twoSidedBarPostcompWhiskerIso (E := E) K R L).hom.app
          (Opposite.op (SimplexCategory.mk n))) ≫
    (twoSidedBarPostcompWhiskerIso (E := F) Q (R.postcomp K) L).hom.app
      (Opposite.op (SimplexCategory.mk n)) ≫
    (twoSidedBarIso ((RightModule.postcompComp K Q).app R)
      (Iso.refl L)).hom.app
      (Opposite.op (SimplexCategory.mk n)) =
    (twoSidedBarPostcompWhiskerIso (E := F) (K ⋙ Q) R L).hom.app
      (Opposite.op (SimplexCategory.mk n)) := by
  ext a
  simp

/--
Composition whisker coherence at components, derived from the degree-`n`
`twoSidedBarPostcompWhiskerIso_comp_hom_app` equality.
-/
theorem twoSidedBarPostcompWhiskerIso_comp_hom_app_app
    (R : RightModule T D) (L : LeftModule A T) (Q : E ⥤ F) (n : ℕ) (a : A) :
    (Q.map (((twoSidedBarPostcompWhiskerIso (E := E) K R L).hom.app
      (Opposite.op (SimplexCategory.mk n))).app a)) ≫
    (((twoSidedBarPostcompWhiskerIso (E := F) Q (R.postcomp K) L).hom.app
      (Opposite.op (SimplexCategory.mk n))).app a) ≫
    (((twoSidedBarIso ((RightModule.postcompComp K Q).app R)
      (Iso.refl L)).hom.app
      (Opposite.op (SimplexCategory.mk n))).app a) =
    (((twoSidedBarPostcompWhiskerIso (E := F) (K ⋙ Q) R L).hom.app
      (Opposite.op (SimplexCategory.mk n))).app a) := by
  have h := twoSidedBarPostcompWhiskerIso_comp_hom_app (T := T) (K := K) R L Q n
  exact congrArg (fun α => α.app a) h

end PostcompProductNaturality

section PostcompModuleCoherence

universe v₅ u₅

variable {F : Type u₅} [Category.{v₅} F]

/--
Bar-level identity coherence for the module side of target whiskering.

`RightModule.postcompId` lifts through `twoSidedBarIso` to a degreewise-identity bar iso. The
whisker comparison itself remains the `Functor.associator` component recorded in
`twoSidedBarPostcompWhiskerIso_hom_app_op_mk`; only the postcomposed module is identified here.
Functor-level whisker-composite coherence is `twoSidedBarPostcompWhiskerNatIso_id`, with
degree-`n` corollary `twoSidedBarPostcompWhiskerIso_id_hom_app` and component consequence
`twoSidedBarPostcompWhiskerIso_id_hom_app_app`: the identity whisker and this module bridge
compose to the identity, using identity-preservation for `functorPostcompOuter` (alias for
Mathlib's `whiskeringRight`) together with the associator triangle, all via componentwise
identities.
-/
@[simp]
theorem twoSidedBarIso_postcompId_hom_app (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) :
    (twoSidedBarIso ((RightModule.postcompId).app R) (Iso.refl L)).hom.app
        (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ := by
  ext a
  simp only [twoSidedBarIso_hom_app_op_mk, barMap_app]
  have hR : ∀ X,
      (((((RightModule.postcompId).app R).hom).f).app X) = 𝟙 _ := fun _ => rfl
  have hL : ∀ x, ((((Iso.refl L).hom).f).app x) = 𝟙 _ := fun _ => rfl
  simp only [hL, hR]
  simp

@[simp]
theorem twoSidedBarIso_postcompId_inv_app (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) :
    (twoSidedBarIso ((RightModule.postcompId).app R) (Iso.refl L)).inv.app
        (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ := by
  ext a
  simp only [twoSidedBarIso_inv_app_op_mk, barMap_app]
  have hR : ∀ X,
      (((((RightModule.postcompId).app R).inv).f).app X) = 𝟙 _ := fun _ => rfl
  have hL : ∀ x, ((((Iso.refl L).inv).f).app x) = 𝟙 _ := fun _ => rfl
  simp only [hL, hR]
  simp

/--
Bar-level composition coherence for the module side of target whiskering.

`RightModule.postcompComp K Q` lifts through `twoSidedBarIso` to a degreewise-identity bar iso,
preserving the orientation `(R.postcomp K).postcomp Q ≅ R.postcomp (K ⋙ Q)`.
Functor-level whisker-composite coherence is `twoSidedBarPostcompWhiskerNatIso_comp`, with
degree-`n` corollary `twoSidedBarPostcompWhiskerIso_comp_hom_app` and component consequence
`twoSidedBarPostcompWhiskerIso_comp_hom_app_app`: the two iterated whisker comparisons followed by
this module bridge coincide with the single `K ⋙ Q` comparison, using composition-preservation for
`functorPostcompOuter` (alias for Mathlib's `whiskeringRight`) together with the associator
pentagon, all via componentwise identities.
-/
@[simp]
theorem twoSidedBarIso_postcompComp_hom_app (R : RightModule T D)
    (L : LeftModule A T) (Q : E ⥤ F) (n : ℕ) :
    (twoSidedBarIso ((RightModule.postcompComp K Q).app R)
      (Iso.refl L)).hom.app
        (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ := by
  ext a
  simp only [twoSidedBarIso_hom_app_op_mk, barMap_app]
  have hR : ∀ X,
      (((((RightModule.postcompComp K Q).app R).hom).f).app X) = 𝟙 _ :=
    fun _ => rfl
  have hL : ∀ x, ((((Iso.refl L).hom).f).app x) = 𝟙 _ := fun _ => rfl
  simp only [hL, hR]
  simp

@[simp]
theorem twoSidedBarIso_postcompComp_inv_app (R : RightModule T D)
    (L : LeftModule A T) (Q : E ⥤ F) (n : ℕ) :
    (twoSidedBarIso ((RightModule.postcompComp K Q).app R)
      (Iso.refl L)).inv.app
        (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ := by
  ext a
  simp only [twoSidedBarIso_inv_app_op_mk, barMap_app]
  have hR : ∀ X,
      (((((RightModule.postcompComp K Q).app R).inv).f).app X) = 𝟙 _ :=
    fun _ => rfl
  have hL : ∀ x, ((((Iso.refl L).inv).f).app x) = 𝟙 _ := fun _ => rfl
  simp only [hL, hR]
  simp

end PostcompModuleCoherence

section PostcompOuterFunctorCoherence

universe v₅ u₅

variable {F : Type u₅} [Category.{v₅} F]

/--
Identity coherence for the outer target postcomposition functor.

Direct use of Mathlib's `whiskeringRightObjIdIso` (which is `Iso.refl _`);
the right-unitor description follows since all components are identities.
No pseudofunctor is built.
-/
abbrev functorPostcompOuterId :
    functorPostcompOuter (E := D) (𝟭 D) ≅ 𝟭 (A ⥤ D) :=
  Functor.whiskeringRightObjIdIso

@[simp]
theorem functorPostcompOuterId_hom_app (G : A ⥤ D) :
    (functorPostcompOuterId).hom.app G = (Functor.rightUnitor G).hom := by
  ext a
  rfl

@[simp]
theorem functorPostcompOuterId_inv_app (G : A ⥤ D) :
    (functorPostcompOuterId).inv.app G = (Functor.rightUnitor G).inv := by
  ext a
  rfl

@[simp]
theorem functorPostcompOuterId_hom_app_app (G : A ⥤ D) (a : A) :
    ((functorPostcompOuterId).hom.app G).app a = 𝟙 _ := rfl

@[simp]
theorem functorPostcompOuterId_inv_app_app (G : A ⥤ D) (a : A) :
    ((functorPostcompOuterId).inv.app G).app a = 𝟙 _ := rfl

/--
Composition coherence for the outer target postcomposition functor.

Direct use of Mathlib's `whiskeringRightObjCompIso` (which is `Iso.refl _`),
preserving the orientation `postcomp K ⋙ postcomp Q ≅ postcomp (K ⋙ Q)`.
The associator description follows since all components are identities.
No pseudofunctor is built.
-/
abbrev functorPostcompOuterComp (Q : E ⥤ F) :
    functorPostcompOuter (A := A) (E := E) K ⋙
        functorPostcompOuter (A := A) (D := E) (E := F) Q ≅
      functorPostcompOuter (A := A) (E := F) (K ⋙ Q) :=
  Functor.whiskeringRightObjCompIso K Q

@[simp]
theorem functorPostcompOuterComp_hom_app (Q : E ⥤ F) (G : A ⥤ D) :
    (functorPostcompOuterComp K Q).hom.app G =
      (Functor.associator G K Q).hom := by
  ext a
  rfl

@[simp]
theorem functorPostcompOuterComp_inv_app (Q : E ⥤ F) (G : A ⥤ D) :
    (functorPostcompOuterComp K Q).inv.app G =
      (Functor.associator G K Q).inv := by
  ext a
  rfl

@[simp]
theorem functorPostcompOuterComp_hom_app_app (Q : E ⥤ F) (G : A ⥤ D) (a : A) :
    (((functorPostcompOuterComp K Q).hom.app G).app a) = 𝟙 _ := rfl

@[simp]
theorem functorPostcompOuterComp_inv_app_app (Q : E ⥤ F) (G : A ⥤ D) (a : A) :
    (((functorPostcompOuterComp K Q).inv.app G).app a) = 𝟙 _ := rfl

/- Functor-level whisker-composite coherence is `twoSidedBarPostcompWhiskerNatIso_id`
and `twoSidedBarPostcompWhiskerNatIso_comp` in `PostcompFunctorLevel`.

Relating iterated `twoSidedBarPostcompWhiskerIso` comparisons to the single
`K ⋙ Q` comparison uses the associator pentagon together with the above
`functorPostcompOuterComp` (direct use of Mathlib's
`whiskeringRightObjCompIso`) and the module-side
`RightModule.postcompComp`; relating the identity whisker to the identity uses
the associator triangle together with `functorPostcompOuterId` (direct use of
Mathlib's `whiskeringRightObjIdIso`) and `RightModule.postcompId`. All
components are identities, so the triangle/pentagon close by `simp`; see the
functor-level `twoSidedBarPostcompWhiskerNatIso_id` and
`twoSidedBarPostcompWhiskerNatIso_comp` equalities, their degree-`n`
corollaries `twoSidedBarPostcompWhiskerIso_id_hom_app` and
`twoSidedBarPostcompWhiskerIso_comp_hom_app`, and component consequences
`twoSidedBarPostcompWhiskerIso_id_hom_app_app` and
`twoSidedBarPostcompWhiskerIso_comp_hom_app_app`. No pseudofunctor is built. -/

end PostcompOuterFunctorCoherence

section PostcompFunctorLevel

universe v₅ u₅

variable {F : Type u₅} [Category.{v₅} F]

/--
Product-level module bridge for identity postcomposition.

`RightModule.postcompId` lifted through `twoSidedBarIso`; the smallest package
needed to state `twoSidedBarPostcompWhiskerNatIso_id`. No pseudofunctor is
built.
-/
noncomputable def twoSidedBarPostcompModuleIdNatIso :
    twoSidedBarPostcompWhiskerFunctorRight (T := T) (A := A) (E := D) (𝟭 D) ≅
      twoSidedBarFunctor T :=
  NatIso.ofComponents
    (fun p => twoSidedBarIso ((RightModule.postcompId).app p.1) (Iso.refl p.2))
    (by
      intro p q f
      obtain ⟨R, L⟩ := p
      obtain ⟨R', L'⟩ := q
      obtain ⟨fR, fL⟩ := f
      change twoSidedBarHom ((RightModule.postcompFunctor (T := T) (𝟭 D)).map fR) fL ≫
          (twoSidedBarIso ((RightModule.postcompId).app R') (Iso.refl L')).hom =
        (twoSidedBarIso ((RightModule.postcompId).app R) (Iso.refl L)).hom ≫
          twoSidedBarHom fR fL
      rw [twoSidedBarIso_hom, twoSidedBarIso_hom,
        twoSidedBarHom_comp, twoSidedBarHom_comp]
      have hR : ((RightModule.postcompFunctor (T := T) (𝟭 D)).map fR) ≫
          ((RightModule.postcompId).app R').hom =
          ((RightModule.postcompId).app R).hom ≫ fR := by
        have h := (RightModule.postcompId).hom.naturality fR
        rw [Functor.id_map] at h
        exact h
      have hL : fL ≫ (Iso.refl L').hom = (Iso.refl L).hom ≫ fL := by
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rw [hR, hL])

/--
Product-level module bridge for composed postcomposition, preserving the
orientation `postcomp K ⋙ postcomp Q ≅ postcomp (K ⋙ Q)`.

`RightModule.postcompComp K Q` lifted through `twoSidedBarIso`; the smallest
package needed to state `twoSidedBarPostcompWhiskerNatIso_comp`. No
pseudofunctor is built.
-/
noncomputable def twoSidedBarPostcompModuleCompNatIso (Q : E ⥤ F) :
    ((RightModule.postcompFunctor (T := T) K ⋙ RightModule.postcompFunctor (T := T) Q).prod
        (𝟭 (LeftModule A T)) ⋙ twoSidedBarFunctor T) ≅
      twoSidedBarPostcompWhiskerFunctorRight (T := T) (A := A) (E := F) (K ⋙ Q) :=
  NatIso.ofComponents
    (fun p => twoSidedBarIso ((RightModule.postcompComp K Q).app p.1) (Iso.refl p.2))
    (by
      intro p q f
      obtain ⟨R, L⟩ := p
      obtain ⟨R', L'⟩ := q
      obtain ⟨fR, fL⟩ := f
      change twoSidedBarHom ((RightModule.postcompFunctor (T := T) K ⋙
          RightModule.postcompFunctor (T := T) Q).map fR) fL ≫
          (twoSidedBarIso ((RightModule.postcompComp K Q).app R') (Iso.refl L')).hom =
        (twoSidedBarIso ((RightModule.postcompComp K Q).app R) (Iso.refl L)).hom ≫
          twoSidedBarHom ((RightModule.postcompFunctor (T := T) (K ⋙ Q)).map fR) fL
      rw [twoSidedBarIso_hom, twoSidedBarIso_hom,
        twoSidedBarHom_comp, twoSidedBarHom_comp]
      have hR : ((RightModule.postcompFunctor (T := T) K ⋙
            RightModule.postcompFunctor (T := T) Q).map fR) ≫
          ((RightModule.postcompComp K Q).app R').hom =
          ((RightModule.postcompComp K Q).app R).hom ≫
            ((RightModule.postcompFunctor (T := T) (K ⋙ Q)).map fR) :=
        (RightModule.postcompComp K Q).hom.naturality fR
      have hL : fL ≫ (Iso.refl L').hom = (Iso.refl L).hom ≫ fL := by
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rw [hR, hL])

/--
Functor-level identity coherence for target postcomposition.

The identity whisker followed by the product-level `postcompId` bridge equals
the ambient `functorPostcompOuterId` coherence lifted through the bar and the
right unitor; no `R`, `L`, `n`, or `Δ` is bound. The degree-`n` corollary is
`twoSidedBarPostcompWhiskerIso_id_hom_app`. No pseudofunctor is built.
-/
theorem twoSidedBarPostcompWhiskerNatIso_id :
    (twoSidedBarPostcompWhiskerNatIso (T := T) (A := A) (E := D) (𝟭 D)).hom ≫
      twoSidedBarPostcompModuleIdNatIso.hom =
    (Functor.isoWhiskerLeft (twoSidedBarFunctor T)
      ((SimplicialObject.whiskering (A ⥤ D) (A ⥤ D)).mapIso
        functorPostcompOuterId)).hom ≫
      (Functor.rightUnitor _).hom := by
  apply NatTrans.ext
  funext p
  obtain ⟨R, L⟩ := p
  apply NatTrans.ext
  funext Δ
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) :=
    twoSidedBarOpMkLen Δ
  rw [hΔ]
  simp only [NatTrans.comp_app, twoSidedBarPostcompWhiskerNatIso_hom_app]
  change (twoSidedBarPostcompWhiskerIso (E := D) (𝟭 D) R L).hom.app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)) ≫
      (twoSidedBarIso ((RightModule.postcompId).app R) (Iso.refl L)).hom.app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)) = _
  rw [twoSidedBarPostcompWhiskerIso_id_hom_app]
  ext a
  rw [Functor.isoWhiskerLeft_hom]
  change (𝟙 _) = ((𝟙 _) ≫ (𝟙 _))
  exact (Category.comp_id _).symm

/--
Functor-level composition coherence for target postcomposition, with the
orientation `postcomp K ⋙ postcomp Q ≅ postcomp (K ⋙ Q)`.

The `Q`-whiskering of the `K` comparison, followed by the `Q` comparison at
the postcomposed module and the product-level `postcompComp` bridge, equals
the single `K ⋙ Q` comparison up to the ambient `functorPostcompOuterComp`
coherence; no `R`, `L`, `n`, or `Δ` is bound. The degree-`n` corollary is
`twoSidedBarPostcompWhiskerIso_comp_hom_app`. No pseudofunctor is built.
-/
theorem twoSidedBarPostcompWhiskerNatIso_comp (Q : E ⥤ F) :
    (Functor.isoWhiskerRight (twoSidedBarPostcompWhiskerNatIso (T := T) (A := A) (E := E) K)
      ((SimplicialObject.whiskering (A ⥤ E) (A ⥤ F)).obj (functorPostcompOuter Q))).hom ≫
    (Functor.isoWhiskerLeft ((RightModule.postcompFunctor (T := T) K).prod (𝟭 (LeftModule A T)))
      (twoSidedBarPostcompWhiskerNatIso (T := T) (A := A) (E := F) Q)).hom ≫
    (twoSidedBarPostcompModuleCompNatIso (K := K) (Q := Q)).hom =
    (Functor.isoWhiskerLeft (twoSidedBarFunctor T)
      ((SimplicialObject.whiskering (A ⥤ D) (A ⥤ F)).mapIso
        (functorPostcompOuterComp K Q))).hom ≫
    (twoSidedBarPostcompWhiskerNatIso (T := T) (A := A) (E := F) (K ⋙ Q)).hom := by
  apply NatTrans.ext
  funext p
  obtain ⟨R, L⟩ := p
  apply NatTrans.ext
  funext Δ
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) :=
    twoSidedBarOpMkLen Δ
  rw [hΔ]
  simp only [NatTrans.comp_app]
  change (functorPostcompOuter Q).map
        ((twoSidedBarPostcompWhiskerIso (E := E) K R L).hom.app
          (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))) ≫
      (twoSidedBarPostcompWhiskerIso (E := F) Q (R.postcomp K) L).hom.app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)) ≫
      (twoSidedBarIso ((RightModule.postcompComp K Q).app R)
        (Iso.refl L)).hom.app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)) = _
  rw [twoSidedBarPostcompWhiskerIso_comp_hom_app]
  ext a
  rw [Functor.isoWhiskerLeft_hom]
  change (((twoSidedBarPostcompWhiskerIso (E := F) (K ⋙ Q) R L).hom.app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))).app a) =
      ((𝟙 _) ≫ (((twoSidedBarPostcompWhiskerIso (E := F) (K ⋙ Q) R L).hom.app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))).app a))
  exact (Category.id_comp _).symm

end PostcompFunctorLevel

end RightPostcompOuter

section LeftPrecompOuter

universe v₄ u₄

variable {B : Type u₄} [Category.{v₄} B]
variable (H : B ⥤ A)

/--
Outer source precomposition whiskering by `H : B ⥤ A`.

Thin alias for Mathlib's `(Functor.whiskeringLeft _ _ _).obj H`; the previous
explicit structure is deleted to avoid duplicate ambient coherence.
-/
abbrev functorPrecompOuter : (A ⥤ D) ⥤ (B ⥤ D) :=
  (Functor.whiskeringLeft B A D).obj H

@[simp]
theorem functorPrecompOuter_obj (F : A ⥤ D) :
    (functorPrecompOuter H).obj F = H ⋙ F := rfl

@[simp]
theorem functorPrecompOuter_obj_obj (F : A ⥤ D) (b : B) :
    ((functorPrecompOuter H).obj F).obj b = F.obj (H.obj b) := rfl

@[simp]
theorem functorPrecompOuter_obj_map (F : A ⥤ D) {b b' : B} (f : b ⟶ b') :
    ((functorPrecompOuter H).obj F).map f = F.map (H.map f) := rfl

@[simp]
theorem functorPrecompOuter_map_app {F G : A ⥤ D} (f : F ⟶ G) (b : B) :
    ((functorPrecompOuter H).map f).app b = f.app (H.obj b) := rfl

theorem barObj_precomp (R : RightModule T D) (L : LeftModule A T) (n : ℕ) :
    barObj T R (L.precomp H) n = (functorPrecompOuter H).obj (barObj T R L n) := rfl

@[simp]
theorem barObj_precomp_obj (R : RightModule T D) (L : LeftModule A T) (n : ℕ) (b : B) :
    (barObj T R (L.precomp H) n).obj b = (barObj T R L n).obj (H.obj b) := rfl

@[simp]
theorem barObj_precomp_map (R : RightModule T D) (L : LeftModule A T) (n : ℕ) {b b' : B}
    (f : b ⟶ b') :
    (barObj T R (L.precomp H) n).map f = (barObj T R L n).map (H.map f) := rfl

theorem barFaceApp_precomp (R : RightModule T D) (L : LeftModule A T) (n : ℕ)
    (i : Fin (n + 2)) (b : B) :
    barFaceApp (T := T) (R := R) (L := L.precomp H) n i b =
      barFaceApp (T := T) (R := R) (L := L) n i (H.obj b) := rfl

theorem barDegeneracyApp_precomp (R : RightModule T D) (L : LeftModule A T) (n : ℕ)
    (i : Fin (n + 1)) (b : B) :
    (barDegeneracy (T := T) (R := R) (L := L.precomp H) n i).app b =
      (barDegeneracy (T := T) (R := R) (L := L) n i).app (H.obj b) := rfl

theorem barFace_precomp (R : RightModule T D) (L : LeftModule A T) (n : ℕ)
    (i : Fin (n + 2)) :
    barFace (T := T) (R := R) (L := L.precomp H) n i =
      Functor.whiskerLeft H (barFace (T := T) (R := R) (L := L) n i) := by
  ext b
  simp only [barFace, Functor.whiskerLeft_app]
  rfl

theorem barDegeneracy_precomp (R : RightModule T D) (L : LeftModule A T) (n : ℕ)
    (i : Fin (n + 1)) :
    barDegeneracy (T := T) (R := R) (L := L.precomp H) n i =
      Functor.whiskerLeft H (barDegeneracy (T := T) (R := R) (L := L) n i) := by
  ext b
  simp only [barDegeneracy, Functor.whiskerLeft_app]
  rfl

section PrecompIso

/--
Degreewise source-precomposition comparison: `H ⋙ ((L ⋙ Tⁿ) ⋙ R)` with
`((H ⋙ L) ⋙ Tⁿ) ⋙ R`, as the composite of the two required functor associators.
Covariant in `R` and `L`; contravariant in the indexing category through `H`.
All universe levels stay distinct, and the comparison is not a definitional identity.
-/
noncomputable def barDataPrecompOuterIsoObj (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) :
    (SimplicialObject.Data.mapObj (functorPrecompOuter H) (barData T R L)).obj n ≅
      (barData T R (L.precomp H)).obj n :=
  (Functor.associator H (L.functor ⋙ monadPow T n) R.functor).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator H L.functor (monadPow T n)).symm R.functor

@[simp]
theorem barDataPrecompOuterIsoObj_hom (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) :
    (barDataPrecompOuterIsoObj H R L n).hom =
      ((Functor.associator H (L.functor ⋙ monadPow T n) R.functor).symm ≪≫
        Functor.isoWhiskerRight (Functor.associator H L.functor (monadPow T n)).symm
          R.functor).hom :=
  rfl

@[simp]
theorem barDataPrecompOuterIsoObj_inv (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) :
    (barDataPrecompOuterIsoObj H R L n).inv =
      ((Functor.associator H (L.functor ⋙ monadPow T n) R.functor).symm ≪≫
        Functor.isoWhiskerRight (Functor.associator H L.functor (monadPow T n)).symm
          R.functor).inv :=
  rfl

@[simp]
theorem barDataPrecompOuterIsoObj_hom_app (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (b : B) :
    (barDataPrecompOuterIsoObj H R L n).hom.app b =
      ((Functor.associator H (L.functor ⋙ monadPow T n) R.functor).symm ≪≫
        Functor.isoWhiskerRight (Functor.associator H L.functor (monadPow T n)).symm
          R.functor).hom.app b := rfl

@[simp]
theorem barDataPrecompOuterIsoObj_inv_app (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (b : B) :
    (barDataPrecompOuterIsoObj H R L n).inv.app b =
      ((Functor.associator H (L.functor ⋙ monadPow T n) R.functor).symm ≪≫
        Functor.isoWhiskerRight (Functor.associator H L.functor (monadPow T n)).symm
          R.functor).inv.app b := rfl

/--
Data-level source-precomposition comparison, assembled from
`barDataPrecompOuterIsoObj` with the generic degreewise-isomorphism infrastructure.
No simplicial identity is reproved here.
-/
noncomputable def barDataPrecompOuterIso (R : RightModule T D) (L : LeftModule A T) :
    SimplicialObject.Data.mapObj (functorPrecompOuter H) (barData T R L) ≅
      barData T R (L.precomp H) :=
  SimplicialObject.Data.isoOfIso (barDataPrecompOuterIsoObj H R L)
    (by
      intro n i
      ext b
      simp [SimplicialObject.Data.mapObj_δ, barData_δ, barFace_precomp,
        barDataPrecompOuterIsoObj, Functor.associator, Functor.isoWhiskerRight,
        functorPrecompOuter])
    (by
      intro n i
      ext b
      simp [SimplicialObject.Data.mapObj_σ, barData_σ, barDegeneracy_precomp,
        barDataPrecompOuterIsoObj, Functor.associator, Functor.isoWhiskerRight,
        functorPrecompOuter])

@[simp]
theorem barDataPrecompOuterIso_hom_app (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) :
    (barDataPrecompOuterIso H R L).hom.app n = (barDataPrecompOuterIsoObj H R L n).hom := rfl

@[simp]
theorem barDataPrecompOuterIso_inv_app (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) :
    (barDataPrecompOuterIso H R L).inv.app n = (barDataPrecompOuterIsoObj H R L n).inv := rfl

@[simp]
theorem barDataPrecompOuterIso_hom_app_app (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (b : B) :
    ((barDataPrecompOuterIso H R L).hom.app n).app b =
      (barDataPrecompOuterIsoObj H R L n).hom.app b := rfl

@[simp]
theorem barDataPrecompOuterIso_inv_app_app (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (b : B) :
    ((barDataPrecompOuterIso H R L).inv.app n).app b =
      (barDataPrecompOuterIsoObj H R L n).inv.app b := rfl

end PrecompIso

section PrecompSimplicial

/--
Simplicial source-precomposition comparison, obtained functorially from `barDataPrecompOuterIso`
via `Data.toSimplicialFunctor`.  This is the `H`-precomposition of the bar compared with the bar
of the precomposed left module.
-/
noncomputable def twoSidedBarPrecompOuterIso (R : RightModule T D)
    (L : LeftModule A T) :
    (SimplicialObject.Data.toSimplicialFunctor (C := B ⥤ D)).obj
        (SimplicialObject.Data.mapObj (functorPrecompOuter H) (barData T R L)) ≅
      twoSidedBar T R (L.precomp H) :=
  (SimplicialObject.Data.toSimplicialFunctor (C := B ⥤ D)).mapIso
    (barDataPrecompOuterIso H R L)

@[simp]
theorem twoSidedBarPrecompOuterIso_hom (R : RightModule T D) (L : LeftModule A T) :
    (twoSidedBarPrecompOuterIso H R L).hom =
      (SimplicialObject.Data.toSimplicialFunctor (C := B ⥤ D)).map
        (barDataPrecompOuterIso H R L).hom :=
  rfl

@[simp]
theorem twoSidedBarPrecompOuterIso_inv (R : RightModule T D) (L : LeftModule A T) :
    (twoSidedBarPrecompOuterIso H R L).inv =
      (SimplicialObject.Data.toSimplicialFunctor (C := B ⥤ D)).map
        (barDataPrecompOuterIso H R L).inv :=
  rfl

@[simp]
theorem twoSidedBarPrecompOuterIso_hom_app_op_mk (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) :
    (twoSidedBarPrecompOuterIso H R L).hom.app
        (Opposite.op (SimplexCategory.mk n)) =
      (barDataPrecompOuterIsoObj H R L n).hom :=
  rfl

@[simp]
theorem twoSidedBarPrecompOuterIso_inv_app_op_mk (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) :
    (twoSidedBarPrecompOuterIso H R L).inv.app
        (Opposite.op (SimplexCategory.mk n)) =
      (barDataPrecompOuterIsoObj H R L n).inv :=
  rfl

theorem twoSidedBarPrecompOuterIso_hom_app_len (R : RightModule T D)
    (L : LeftModule A T) (Δ : SimplexCategoryᵒᵖ) :
    (twoSidedBarPrecompOuterIso H R L).hom.app Δ =
      (barDataPrecompOuterIsoObj H R L (Opposite.unop Δ).len).hom := by
  obtain ⟨Δ⟩ := Δ
  rfl

theorem twoSidedBarPrecompOuterIso_inv_app_len (R : RightModule T D)
    (L : LeftModule A T) (Δ : SimplexCategoryᵒᵖ) :
    (twoSidedBarPrecompOuterIso H R L).inv.app Δ =
      (barDataPrecompOuterIsoObj H R L (Opposite.unop Δ).len).inv := by
  obtain ⟨Δ⟩ := Δ
  rfl

@[simp]
theorem twoSidedBarPrecompOuterIso_hom_app (R : RightModule T D)
    (L : LeftModule A T) (Δ : SimplexCategoryᵒᵖ) (b : B) :
    (((twoSidedBarPrecompOuterIso H R L).hom.app Δ).app b) =
      (barDataPrecompOuterIsoObj H R L (Opposite.unop Δ).len).hom.app b := by
  obtain ⟨Δ⟩ := Δ
  rfl

@[simp]
theorem twoSidedBarPrecompOuterIso_inv_app (R : RightModule T D)
    (L : LeftModule A T) (Δ : SimplexCategoryᵒᵖ) (b : B) :
    (((twoSidedBarPrecompOuterIso H R L).inv.app Δ).app b) =
      (barDataPrecompOuterIsoObj H R L (Opposite.unop Δ).len).inv.app b := by
  obtain ⟨Δ⟩ := Δ
  rfl

end PrecompSimplicial

section PrecompWhisker

/--
Source-precomposition comparison with whiskered source.

The source is literally the whiskered bar `twoSidedBar T R L ⋙ functorPrecompOuter H`, not
`toSimplicialFunctor.obj (Data.mapObj _ _)`. It composes the generic
`toSimplicialFunctor_mapFunctorIso` bridge with the transport of the data-level
`barDataPrecompOuterIso` (double-associator orientation preserved).
-/
noncomputable def twoSidedBarPrecompWhiskerIso (R : RightModule T D)
    (L : LeftModule A T) :
    (twoSidedBar T R L ⋙ functorPrecompOuter H) ≅
      twoSidedBar T R (L.precomp H) :=
  (SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso
    (functorPrecompOuter H)).app (barData T R L) ≪≫
    twoSidedBarPrecompOuterIso H R L

@[simp]
theorem twoSidedBarPrecompWhiskerIso_hom_app_op_mk (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) :
    (twoSidedBarPrecompWhiskerIso H R L).hom.app
        (Opposite.op (SimplexCategory.mk n)) =
      (barDataPrecompOuterIsoObj H R L n).hom := by
  ext b
  have hBridgeApp :
      ((((SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso
        (functorPrecompOuter H)).app
          (barData T R L)).hom.app
        (Opposite.op (SimplexCategory.mk n))).app b) = 𝟙 _ := by
    have h :=
      SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso_hom_app_app_mk
        (functorPrecompOuter H) (barData T R L) n
    exact congrArg (fun h => h.app b) h
  have hOuterApp :
      (((twoSidedBarPrecompOuterIso H R L).hom.app
        (Opposite.op (SimplexCategory.mk n))).app b) = 𝟙 _ := by
    simp
  have hRhs :
      ((barDataPrecompOuterIsoObj H R L n).hom.app b) = 𝟙 _ := by
    simp
  have hComp :
      (((twoSidedBarPrecompWhiskerIso H R L).hom.app
        (Opposite.op (SimplexCategory.mk n))).app b) =
      (((((SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso
        (functorPrecompOuter H)).app
          (barData T R L)).hom.app
        (Opposite.op (SimplexCategory.mk n))).app b) ≫
      (((twoSidedBarPrecompOuterIso H R L).hom.app
        (Opposite.op (SimplexCategory.mk n))).app b)) := rfl
  rw [hComp, hBridgeApp, hOuterApp, hRhs]
  exact Category.id_comp _

@[simp]
theorem twoSidedBarPrecompWhiskerIso_inv_app_op_mk (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) :
    (twoSidedBarPrecompWhiskerIso H R L).inv.app
        (Opposite.op (SimplexCategory.mk n)) =
      (barDataPrecompOuterIsoObj H R L n).inv := by
  ext b
  have hBridgeInv :
      ((((SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso
        (functorPrecompOuter H)).app
          (barData T R L)).inv.app
        (Opposite.op (SimplexCategory.mk n))).app b) = 𝟙 _ := by
    have h :=
      SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso_inv_app_app_mk
        (functorPrecompOuter H) (barData T R L) n
    exact congrArg (fun h => h.app b) h
  have hOuterInv :
      (((twoSidedBarPrecompOuterIso H R L).inv.app
        (Opposite.op (SimplexCategory.mk n))).app b) = 𝟙 _ := by
    simp
  have hRhsInv :
      ((barDataPrecompOuterIsoObj H R L n).inv.app b) = 𝟙 _ := by
    simp
  have hComp :
      (((twoSidedBarPrecompWhiskerIso H R L).inv.app
        (Opposite.op (SimplexCategory.mk n))).app b) =
      (((twoSidedBarPrecompOuterIso H R L).inv.app
        (Opposite.op (SimplexCategory.mk n))).app b ≫
      ((((SimplicialObject.Data.toSimplicialFunctor_mapFunctorIso
        (functorPrecompOuter H)).app
          (barData T R L)).inv.app
        (Opposite.op (SimplexCategory.mk n))).app b)) := rfl
  rw [hComp, hOuterInv, hBridgeInv, hRhsInv]
  exact Category.id_comp _

/--
Smallest robust naturality in module maps, at `op (mk n)` components.

Whiskered maps commute with the whisker comparison; the precomposed left-module map is
`(LeftModule.precompFunctor H).map fL`. This component naturality is reused by the product-level
`twoSidedBarPrecompWhiskerNatIso`; identity/composition coherence in `H` is proved at components
in `PrecompProductNaturality` (all components are identities, so the associator
triangle/double-associator pentagon close by `simp`, with correct contravariant `J ⋙ H` source
order).
-/
theorem twoSidedBarPrecompWhiskerIso_naturality_app_op_mk
    {R R' : RightModule T D} {L L' : LeftModule A T}
    (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) :
    (((SimplicialObject.whiskering _ _).obj
      (functorPrecompOuter H)).map
        (twoSidedBarHom fR fL)).app (Opposite.op (SimplexCategory.mk n)) ≫
      (twoSidedBarPrecompWhiskerIso H R' L').hom.app
        (Opposite.op (SimplexCategory.mk n)) =
      (twoSidedBarPrecompWhiskerIso H R L).hom.app
        (Opposite.op (SimplexCategory.mk n)) ≫
      (twoSidedBarHom fR ((LeftModule.precompFunctor H).map fL)).app
        (Opposite.op (SimplexCategory.mk n)) := by
  ext b
  have hCompL :
      ((((((SimplicialObject.whiskering (A ⥤ D) (B ⥤ D)).obj
        (functorPrecompOuter H)).map
          (twoSidedBarHom fR fL)).app (Opposite.op (SimplexCategory.mk n)) ≫
        (twoSidedBarPrecompWhiskerIso H R' L').hom.app
          (Opposite.op (SimplexCategory.mk n))).app b)) =
      ((((((SimplicialObject.whiskering (A ⥤ D) (B ⥤ D)).obj
        (functorPrecompOuter H)).map
          (twoSidedBarHom fR fL)).app
          (Opposite.op (SimplexCategory.mk n))).app b) ≫
        (((twoSidedBarPrecompWhiskerIso H R' L').hom.app
          (Opposite.op (SimplexCategory.mk n))).app b)) := rfl
  have hCompR :
      (((((twoSidedBarPrecompWhiskerIso H R L).hom.app
          (Opposite.op (SimplexCategory.mk n))) ≫
        (twoSidedBarHom fR ((LeftModule.precompFunctor H).map fL)).app
          (Opposite.op (SimplexCategory.mk n))).app b)) =
      (((((twoSidedBarPrecompWhiskerIso H R L).hom.app
          (Opposite.op (SimplexCategory.mk n))).app b) ≫
        (((twoSidedBarHom fR ((LeftModule.precompFunctor H).map fL)).app
          (Opposite.op (SimplexCategory.mk n))).app b))) := rfl
  rw [hCompL, hCompR]
  simp only [Functor.whiskeringRight_obj_map,
    functorPrecompOuter_map_app, twoSidedBarHom_app_app_op_mk,
    twoSidedBarPrecompWhiskerIso_hom_app_op_mk, barDataPrecompOuterIsoObj_hom_app,
    Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, LeftModule.precomp_functor_obj,
    Functor.comp_obj, Functor.map_id, Category.comp_id]
  exact (Category.comp_id (R.functor.map ((T.monadPow n).map (fL.f.app (H.obj b))) ≫
      fR.f.app ((T.monadPow n).obj (L'.functor.obj (H.obj b))))).trans
    (Category.id_comp (R.functor.map ((T.monadPow n).map (fL.f.app (H.obj b))) ≫
      fR.f.app ((T.monadPow n).obj (L'.functor.obj (H.obj b))))).symm

/-- Naturality at a general opposite simplex object, reduced to `mk` components. -/
theorem twoSidedBarPrecompWhiskerIso_naturality_app
    {R R' : RightModule T D} {L L' : LeftModule A T}
    (fR : R ⟶ R') (fL : L ⟶ L') (Δ : SimplexCategoryᵒᵖ) :
    (((SimplicialObject.whiskering (A ⥤ D) (B ⥤ D)).obj
      (functorPrecompOuter H)).map
        (twoSidedBarHom fR fL)).app Δ ≫
      (twoSidedBarPrecompWhiskerIso H R' L').hom.app Δ =
      (twoSidedBarPrecompWhiskerIso H R L).hom.app Δ ≫
      (twoSidedBarHom fR ((LeftModule.precompFunctor H).map fL)).app Δ := by
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) :=
    twoSidedBarOpMkLen Δ
  rw [hΔ]
  exact twoSidedBarPrecompWhiskerIso_naturality_app_op_mk H fR fL _

end PrecompWhisker

section PrecompProductNaturality

/-- Left whisker functor for product naturality: bar then source whiskering. -/
noncomputable def twoSidedBarPrecompWhiskerFunctorLeft :
    (RightModule T D × LeftModule A T) ⥤ SimplicialObject (B ⥤ D) :=
  twoSidedBarFunctor T ⋙
    (SimplicialObject.whiskering _ _).obj (functorPrecompOuter H)

/-- Right whisker functor: module precomposition then bar. -/
noncomputable def twoSidedBarPrecompWhiskerFunctorRight :
    (RightModule T D × LeftModule A T) ⥤ SimplicialObject (B ⥤ D) :=
  (𝟭 _).prod (LeftModule.precompFunctor (T := T) H) ⋙ twoSidedBarFunctor T

/--
Genuinely natural source-precomposition whisker isomorphism over the
product of module categories, reusing the degreewise double-associator isos
and component naturality, with correct contravariant source order.
-/
noncomputable def twoSidedBarPrecompWhiskerNatIso :
    twoSidedBarPrecompWhiskerFunctorLeft (T := T) (D := D) H ≅
      twoSidedBarPrecompWhiskerFunctorRight (T := T) (D := D) H :=
  NatIso.ofComponents
    (fun p => twoSidedBarPrecompWhiskerIso H p.1 p.2)
    (by
      intro p q f
      obtain ⟨R, L⟩ := p
      obtain ⟨R', L'⟩ := q
      obtain ⟨fR, fL⟩ := f
      apply NatTrans.ext
      funext Δ
      exact twoSidedBarPrecompWhiskerIso_naturality_app H fR fL Δ)

@[simp]
theorem twoSidedBarPrecompWhiskerNatIso_hom_app (p : RightModule T D × LeftModule A T)
    (Δ : SimplexCategoryᵒᵖ) :
    ((twoSidedBarPrecompWhiskerNatIso H).hom.app p).app Δ =
      (twoSidedBarPrecompWhiskerIso H p.1 p.2).hom.app Δ := rfl

@[simp]
theorem twoSidedBarPrecompWhiskerNatIso_inv_app (p : RightModule T D × LeftModule A T)
    (Δ : SimplexCategoryᵒᵖ) :
    ((twoSidedBarPrecompWhiskerNatIso H).inv.app p).app Δ =
      (twoSidedBarPrecompWhiskerIso H p.1 p.2).inv.app Δ := rfl

/--
Whisker comparison components are identities at `app b`: the
double-associator has identity components, so Mathlib's triangle/pentagon
close by `simp`.
-/
@[simp]
theorem twoSidedBarPrecompWhiskerIso_hom_app_app_id
    (R : RightModule T D) (L : LeftModule A T) (n : ℕ) (b : B) :
    (((twoSidedBarPrecompWhiskerIso H R L).hom.app
      (Opposite.op (SimplexCategory.mk n))).app b) = 𝟙 _ := by
  simp [twoSidedBarPrecompWhiskerIso_hom_app_op_mk, barDataPrecompOuterIsoObj]

@[simp]
theorem twoSidedBarPrecompWhiskerIso_inv_app_app_id
    (R : RightModule T D) (L : LeftModule A T) (n : ℕ) (b : B) :
    (((twoSidedBarPrecompWhiskerIso H R L).inv.app
      (Opposite.op (SimplexCategory.mk n))).app b) = 𝟙 _ := by
  simp [twoSidedBarPrecompWhiskerIso_inv_app_op_mk, barDataPrecompOuterIsoObj]

universe v₅ u₅

variable {B₂ : Type u₅} [Category.{v₅} B₂]

/--
Degree-`n` component of identity whisker coherence.

The identity whisker followed by the module-side `precompId` bridge is the
identity at `op (mk n)`; see `twoSidedBarPrecompWhiskerNatIso_id` for the
functor-level statement. Together with the categorical
`functorPrecompOuterId` and `twoSidedBarIso_precompId_hom_app` identities,
this is the associator triangle; no pseudofunctor is built.
-/
theorem twoSidedBarPrecompWhiskerIso_id_hom_app
    (R : RightModule T D) (L : LeftModule A T) (n : ℕ) :
    (twoSidedBarPrecompWhiskerIso (𝟭 A) R L).hom.app
      (Opposite.op (SimplexCategory.mk n)) ≫
    (twoSidedBarIso (Iso.refl R) ((LeftModule.precompId).app L)).hom.app
      (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ := by
  ext a
  simp

/--
Identity whisker coherence at components, derived from the degree-`n`
`twoSidedBarPrecompWhiskerIso_id_hom_app` equality.
-/
theorem twoSidedBarPrecompWhiskerIso_id_hom_app_app
    (R : RightModule T D) (L : LeftModule A T) (n : ℕ) (a : A) :
    (((twoSidedBarPrecompWhiskerIso (𝟭 A) R L).hom.app
      (Opposite.op (SimplexCategory.mk n))).app a) ≫
    (((twoSidedBarIso (Iso.refl R) ((LeftModule.precompId).app L)).hom.app
      (Opposite.op (SimplexCategory.mk n))).app a) = 𝟙 _ := by
  have h := twoSidedBarPrecompWhiskerIso_id_hom_app (T := T) R L n
  exact congrArg (fun α => α.app a) h

/--
Degree-`n` component of composition whisker coherence, with
correct contravariant order `(L.precomp H).precomp J ≅ L.precomp (J ⋙ H)`.

The `J`-whiskering of the `H` comparison, followed by the `J` comparison and
the module-side `precompComp` bridge, coincides with the single `J ⋙ H`
comparison at `op (mk n)`; see `twoSidedBarPrecompWhiskerNatIso_comp` for the
functor-level statement. All sides have identity components, so Mathlib's
double-associator pentagon closes by `simp`; the ambient
`functorPrecompOuterComp` bridge is likewise componentwise identity, with
Mathlib refl alias `whiskeringLeftObjCompIso` in symm orientation.
-/
theorem twoSidedBarPrecompWhiskerIso_comp_hom_app
    (R : RightModule T D) (L : LeftModule A T) (J : B₂ ⥤ B) (n : ℕ) :
    (functorPrecompOuter J).map
        ((twoSidedBarPrecompWhiskerIso H R L).hom.app
          (Opposite.op (SimplexCategory.mk n))) ≫
    (twoSidedBarPrecompWhiskerIso J R (L.precomp H)).hom.app
      (Opposite.op (SimplexCategory.mk n)) ≫
    (twoSidedBarIso (Iso.refl R)
      ((LeftModule.precompComp H J).app L)).hom.app
      (Opposite.op (SimplexCategory.mk n)) =
    (twoSidedBarPrecompWhiskerIso (J ⋙ H) R L).hom.app
      (Opposite.op (SimplexCategory.mk n)) := by
  ext b₂
  simp

/--
Composition whisker coherence at components, derived from the degree-`n`
`twoSidedBarPrecompWhiskerIso_comp_hom_app` equality.
-/
theorem twoSidedBarPrecompWhiskerIso_comp_hom_app_app
    (R : RightModule T D) (L : LeftModule A T) (J : B₂ ⥤ B) (n : ℕ) (b₂ : B₂) :
    (((twoSidedBarPrecompWhiskerIso H R L).hom.app
      (Opposite.op (SimplexCategory.mk n))).app (J.obj b₂)) ≫
    (((twoSidedBarPrecompWhiskerIso J R (L.precomp H)).hom.app
      (Opposite.op (SimplexCategory.mk n))).app b₂) ≫
    (((twoSidedBarIso (Iso.refl R)
      ((LeftModule.precompComp H J).app L)).hom.app
      (Opposite.op (SimplexCategory.mk n))).app b₂) =
    (((twoSidedBarPrecompWhiskerIso (J ⋙ H) R L).hom.app
      (Opposite.op (SimplexCategory.mk n))).app b₂) := by
  have h := twoSidedBarPrecompWhiskerIso_comp_hom_app (T := T) (H := H) R L J n
  exact congrArg (fun α => α.app b₂) h

end PrecompProductNaturality

section PrecompModuleCoherence

universe v₅ u₅

variable {B₂ : Type u₅} [Category.{v₅} B₂]

/--
Bar-level identity coherence for the module side of source whiskering.

`LeftModule.precompId` lifts through `twoSidedBarIso` to a degreewise-identity bar iso. The
whisker comparison itself remains the double-associator component recorded in
`twoSidedBarPrecompWhiskerIso_hom_app_op_mk`; only the precomposed module is identified here.
Functor-level whisker-composite coherence is `twoSidedBarPrecompWhiskerNatIso_id`, with degree-`n`
corollary `twoSidedBarPrecompWhiskerIso_id_hom_app` and component consequence
`twoSidedBarPrecompWhiskerIso_id_hom_app_app`: the identity whisker and this module bridge compose
to the identity, using identity-preservation for `functorPrecompOuter` (alias for Mathlib's
`whiskeringLeft`) together with the associator triangle, all via componentwise identities.
-/
@[simp]
theorem twoSidedBarIso_precompId_hom_app (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) :
    (twoSidedBarIso (Iso.refl R) ((LeftModule.precompId).app L)).hom.app
        (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ := by
  ext a
  simp only [twoSidedBarIso_hom_app_op_mk, barMap_app]
  have hR : ∀ X,
      (((((Iso.refl R).hom).f).app X)) = 𝟙 _ := fun _ => rfl
  have hL : ∀ x, (((((LeftModule.precompId).app L).hom).f).app x) = 𝟙 _ :=
    fun _ => rfl
  simp only [hL, hR]
  simp

@[simp]
theorem twoSidedBarIso_precompId_inv_app (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) :
    (twoSidedBarIso (Iso.refl R) ((LeftModule.precompId).app L)).inv.app
        (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ := by
  ext a
  simp only [twoSidedBarIso_inv_app_op_mk, barMap_app]
  have hR : ∀ X,
      (((((Iso.refl R).inv).f).app X)) = 𝟙 _ := fun _ => rfl
  have hL : ∀ x, (((((LeftModule.precompId).app L).inv).f).app x) = 𝟙 _ :=
    fun _ => rfl
  simp only [hL, hR]
  simp

/--
Bar-level composition coherence for the module side of source whiskering.

`LeftModule.precompComp H J` lifts through `twoSidedBarIso` to a degreewise-identity bar iso,
preserving the orientation `(L.precomp H).precomp J ≅ L.precomp (J ⋙ H)`. Functor-level
whisker-composite coherence is `twoSidedBarPrecompWhiskerNatIso_comp`, with degree-`n` corollary
`twoSidedBarPrecompWhiskerIso_comp_hom_app` and component consequence
`twoSidedBarPrecompWhiskerIso_comp_hom_app_app`: the two iterated whisker comparisons (with
correct contravariant `J ⋙ H` order) followed by this module bridge coincide with the single `J ⋙
H` comparison, using composition-preservation for `functorPrecompOuter` (alias for Mathlib's
`whiskeringLeft`) together with the double-associator pentagon, all via componentwise identities.
-/
@[simp]
theorem twoSidedBarIso_precompComp_hom_app (R : RightModule T D)
    (L : LeftModule A T) (J : B₂ ⥤ B) (n : ℕ) :
    (twoSidedBarIso (Iso.refl R)
      ((LeftModule.precompComp H J).app L)).hom.app
        (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ := by
  ext a
  simp only [twoSidedBarIso_hom_app_op_mk, barMap_app]
  have hR : ∀ X,
      (((((Iso.refl R).hom).f).app X)) = 𝟙 _ := fun _ => rfl
  have hL : ∀ x,
      (((((LeftModule.precompComp H J).app L).hom).f).app x) = 𝟙 _ :=
    fun _ => rfl
  simp only [hL, hR]
  simp

@[simp]
theorem twoSidedBarIso_precompComp_inv_app (R : RightModule T D)
    (L : LeftModule A T) (J : B₂ ⥤ B) (n : ℕ) :
    (twoSidedBarIso (Iso.refl R)
      ((LeftModule.precompComp H J).app L)).inv.app
        (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ := by
  ext a
  simp only [twoSidedBarIso_inv_app_op_mk, barMap_app]
  have hR : ∀ X,
      (((((Iso.refl R).inv).f).app X)) = 𝟙 _ := fun _ => rfl
  have hL : ∀ x,
      (((((LeftModule.precompComp H J).app L).inv).f).app x) = 𝟙 _ :=
    fun _ => rfl
  simp only [hL, hR]
  simp

end PrecompModuleCoherence

section PrecompOuterFunctorCoherence

universe v₅ u₅

variable {B₂ : Type u₅} [Category.{v₅} B₂]

/--
Identity coherence for the outer source precomposition functor.

Direct use of Mathlib's `whiskeringLeftObjIdIso` (which is `Iso.refl _`);
the left-unitor description follows since all components are identities.
No pseudofunctor is built.
-/
abbrev functorPrecompOuterId :
    functorPrecompOuter (𝟭 A) ≅ 𝟭 (A ⥤ D) :=
  Functor.whiskeringLeftObjIdIso

@[simp]
theorem functorPrecompOuterId_hom_app (G : A ⥤ D) :
    (functorPrecompOuterId).hom.app G = (Functor.leftUnitor G).hom := by
  ext a
  rfl

@[simp]
theorem functorPrecompOuterId_inv_app (G : A ⥤ D) :
    (functorPrecompOuterId).inv.app G = (Functor.leftUnitor G).inv := by
  ext a
  rfl

@[simp]
theorem functorPrecompOuterId_hom_app_app (G : A ⥤ D) (a : A) :
    ((functorPrecompOuterId).hom.app G).app a = 𝟙 _ := rfl

@[simp]
theorem functorPrecompOuterId_inv_app_app (G : A ⥤ D) (a : A) :
    ((functorPrecompOuterId).inv.app G).app a = 𝟙 _ := rfl

/--
Composition coherence for the outer source precomposition functor.

For `H : B ⥤ A` and `J : B₂ ⥤ B`, this is the appropriately oriented
`(Functor.whiskeringLeftObjCompIso J H).symm` (which is `Iso.refl _.symm`),
preserving the contravariant orientation
`precomp H ⋙ precomp J ≅ precomp (J ⋙ H)`.
The reversed-associator description follows since all components are identities.
No pseudofunctor is built.
-/
abbrev functorPrecompOuterComp (J : B₂ ⥤ B) :
    functorPrecompOuter (D := D) H ⋙ functorPrecompOuter (D := D) J ≅
      functorPrecompOuter (D := D) (J ⋙ H) :=
  (Functor.whiskeringLeftObjCompIso J H).symm

@[simp]
theorem functorPrecompOuterComp_hom_app (J : B₂ ⥤ B) (G : A ⥤ D) :
    (functorPrecompOuterComp H J).hom.app G =
      (Functor.associator J H G).symm.hom := by
  ext b
  rfl

@[simp]
theorem functorPrecompOuterComp_inv_app (J : B₂ ⥤ B) (G : A ⥤ D) :
    (functorPrecompOuterComp H J).inv.app G =
      (Functor.associator J H G).symm.inv := by
  ext b
  rfl

@[simp]
theorem functorPrecompOuterComp_hom_app_app (J : B₂ ⥤ B) (G : A ⥤ D) (b : B₂) :
    (((functorPrecompOuterComp H J).hom.app G).app b) = 𝟙 _ := rfl

@[simp]
theorem functorPrecompOuterComp_inv_app_app (J : B₂ ⥤ B) (G : A ⥤ D) (b : B₂) :
    (((functorPrecompOuterComp H J).inv.app G).app b) = 𝟙 _ := rfl

/- Functor-level whisker-composite coherence is `twoSidedBarPrecompWhiskerNatIso_id`
and `twoSidedBarPrecompWhiskerNatIso_comp` in `PrecompFunctorLevel`.

Relating iterated `twoSidedBarPrecompWhiskerIso` comparisons to the single
`J ⋙ H` comparison (correct contravariant order) uses the double-associator
pentagon together with the above `functorPrecompOuterComp` (direct use of
`(Functor.whiskeringLeftObjCompIso J H).symm`) and the module-side
`LeftModule.precompComp`; relating the identity whisker to the identity uses
the associator triangle together with `functorPrecompOuterId` (direct use of
Mathlib's `whiskeringLeftObjIdIso`) and `LeftModule.precompId`. All components
are identities, so the triangle/pentagon close by `simp`; see the functor-level
`twoSidedBarPrecompWhiskerNatIso_id` and
`twoSidedBarPrecompWhiskerNatIso_comp` equalities, their degree-`n`
corollaries `twoSidedBarPrecompWhiskerIso_id_hom_app` and
`twoSidedBarPrecompWhiskerIso_comp_hom_app`, and component consequences
`twoSidedBarPrecompWhiskerIso_id_hom_app_app` and
`twoSidedBarPrecompWhiskerIso_comp_hom_app_app`. No pseudofunctor is built. -/

end PrecompOuterFunctorCoherence

section PrecompFunctorLevel

universe v₅ u₅

variable {B₂ : Type u₅} [Category.{v₅} B₂]

/--
Product-level module bridge for identity precomposition.

`LeftModule.precompId` lifted through `twoSidedBarIso`; the smallest package
needed to state `twoSidedBarPrecompWhiskerNatIso_id`. No pseudofunctor is
built.
-/
noncomputable def twoSidedBarPrecompModuleIdNatIso :
    twoSidedBarPrecompWhiskerFunctorRight (T := T) (D := D) (𝟭 A) ≅
      twoSidedBarFunctor T :=
  NatIso.ofComponents
    (fun p => twoSidedBarIso (Iso.refl p.1) ((LeftModule.precompId).app p.2))
    (by
      intro p q f
      obtain ⟨R, L⟩ := p
      obtain ⟨R', L'⟩ := q
      obtain ⟨fR, fL⟩ := f
      change twoSidedBarHom fR ((LeftModule.precompFunctor (T := T) (𝟭 A)).map fL) ≫
          (twoSidedBarIso (Iso.refl R') ((LeftModule.precompId).app L')).hom =
        (twoSidedBarIso (Iso.refl R) ((LeftModule.precompId).app L)).hom ≫
          twoSidedBarHom fR fL
      rw [twoSidedBarIso_hom, twoSidedBarIso_hom,
        twoSidedBarHom_comp, twoSidedBarHom_comp]
      have hR : fR ≫ (Iso.refl R').hom = (Iso.refl R).hom ≫ fR := by
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      have hL : ((LeftModule.precompFunctor (T := T) (𝟭 A)).map fL) ≫
          ((LeftModule.precompId).app L').hom =
          ((LeftModule.precompId).app L).hom ≫ fL := by
        have h := (LeftModule.precompId).hom.naturality fL
        rw [Functor.id_map] at h
        exact h
      rw [hR, hL])

/--
Product-level module bridge for composed precomposition, preserving the
contravariant orientation `(L.precomp H).precomp J ≅ L.precomp (J ⋙ H)`.

`LeftModule.precompComp H J` lifted through `twoSidedBarIso`; the smallest
package needed to state `twoSidedBarPrecompWhiskerNatIso_comp`. No
pseudofunctor is built.
-/
noncomputable def twoSidedBarPrecompModuleCompNatIso (J : B₂ ⥤ B) :
    ((𝟭 (RightModule T D)).prod
        (LeftModule.precompFunctor (T := T) H ⋙ LeftModule.precompFunctor (T := T) J) ⋙
      twoSidedBarFunctor T) ≅
      twoSidedBarPrecompWhiskerFunctorRight (T := T) (D := D) (J ⋙ H) :=
  NatIso.ofComponents
    (fun p => twoSidedBarIso (Iso.refl p.1) ((LeftModule.precompComp H J).app p.2))
    (by
      intro p q f
      obtain ⟨R, L⟩ := p
      obtain ⟨R', L'⟩ := q
      obtain ⟨fR, fL⟩ := f
      change twoSidedBarHom fR ((LeftModule.precompFunctor (T := T) H ⋙
          LeftModule.precompFunctor (T := T) J).map fL) ≫
          (twoSidedBarIso (Iso.refl R') ((LeftModule.precompComp H J).app L')).hom =
        (twoSidedBarIso (Iso.refl R) ((LeftModule.precompComp H J).app L)).hom ≫
          twoSidedBarHom fR ((LeftModule.precompFunctor (T := T) (J ⋙ H)).map fL)
      rw [twoSidedBarIso_hom, twoSidedBarIso_hom,
        twoSidedBarHom_comp, twoSidedBarHom_comp]
      have hR : fR ≫ (Iso.refl R').hom = (Iso.refl R).hom ≫ fR := by
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      have hL : ((LeftModule.precompFunctor (T := T) H ⋙
            LeftModule.precompFunctor (T := T) J).map fL) ≫
          ((LeftModule.precompComp H J).app L').hom =
          ((LeftModule.precompComp H J).app L).hom ≫
            ((LeftModule.precompFunctor (T := T) (J ⋙ H)).map fL) :=
        (LeftModule.precompComp H J).hom.naturality fL
      rw [hR, hL])

/--
Functor-level identity coherence for source precomposition.

The identity whisker followed by the product-level `precompId` bridge equals
the ambient `functorPrecompOuterId` coherence lifted through the bar and the
right unitor; no `R`, `L`, `n`, or `Δ` is bound. The degree-`n` corollary is
`twoSidedBarPrecompWhiskerIso_id_hom_app`. No pseudofunctor is built.
-/
theorem twoSidedBarPrecompWhiskerNatIso_id :
    (twoSidedBarPrecompWhiskerNatIso (T := T) (D := D) (𝟭 A)).hom ≫
      twoSidedBarPrecompModuleIdNatIso.hom =
    (Functor.isoWhiskerLeft (twoSidedBarFunctor T)
      ((SimplicialObject.whiskering (A ⥤ D) (A ⥤ D)).mapIso
        functorPrecompOuterId)).hom ≫
      (Functor.rightUnitor _).hom := by
  apply NatTrans.ext
  funext p
  obtain ⟨R, L⟩ := p
  apply NatTrans.ext
  funext Δ
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) :=
    twoSidedBarOpMkLen Δ
  rw [hΔ]
  simp only [NatTrans.comp_app, twoSidedBarPrecompWhiskerNatIso_hom_app]
  change (twoSidedBarPrecompWhiskerIso (𝟭 A) R L).hom.app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)) ≫
      (twoSidedBarIso (Iso.refl R) ((LeftModule.precompId).app L)).hom.app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)) = _
  rw [twoSidedBarPrecompWhiskerIso_id_hom_app]
  ext a
  rw [Functor.isoWhiskerLeft_hom]
  change (𝟙 _) = ((𝟙 _) ≫ (𝟙 _))
  exact (Category.comp_id _).symm

/--
Functor-level composition coherence for source precomposition, with correct
contravariant order `(L.precomp H).precomp J ≅ L.precomp (J ⋙ H)`.

The `J`-whiskering of the `H` comparison, followed by the `J` comparison at
the precomposed module and the product-level `precompComp` bridge, equals the
single `J ⋙ H` comparison up to the ambient `functorPrecompOuterComp`
coherence (direct use of `(Functor.whiskeringLeftObjCompIso J H).symm`); no
`R`, `L`, `n`, or `Δ` is bound. The degree-`n` corollary is
`twoSidedBarPrecompWhiskerIso_comp_hom_app`. No pseudofunctor is built.
-/
theorem twoSidedBarPrecompWhiskerNatIso_comp (J : B₂ ⥤ B) :
    (Functor.isoWhiskerRight (twoSidedBarPrecompWhiskerNatIso (T := T) (D := D) H)
      ((SimplicialObject.whiskering (B ⥤ D) (B₂ ⥤ D)).obj (functorPrecompOuter J))).hom ≫
    (Functor.isoWhiskerLeft ((𝟭 (RightModule T D)).prod (LeftModule.precompFunctor (T := T) H))
      (twoSidedBarPrecompWhiskerNatIso (T := T) (D := D) J)).hom ≫
    (twoSidedBarPrecompModuleCompNatIso (T := T) (H := H) (J := J)).hom =
    (Functor.isoWhiskerLeft (twoSidedBarFunctor T)
      ((SimplicialObject.whiskering (A ⥤ D) (B₂ ⥤ D)).mapIso
        (functorPrecompOuterComp H J))).hom ≫
    (twoSidedBarPrecompWhiskerNatIso (T := T) (D := D) (J ⋙ H)).hom := by
  apply NatTrans.ext
  funext p
  obtain ⟨R, L⟩ := p
  apply NatTrans.ext
  funext Δ
  have hΔ : Δ = Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len) :=
    twoSidedBarOpMkLen Δ
  rw [hΔ]
  simp only [NatTrans.comp_app]
  change (functorPrecompOuter J).map
        ((twoSidedBarPrecompWhiskerIso H R L).hom.app
          (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))) ≫
      (twoSidedBarPrecompWhiskerIso J R (L.precomp H)).hom.app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)) ≫
      (twoSidedBarIso (Iso.refl R)
        ((LeftModule.precompComp H J).app L)).hom.app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len)) = _
  rw [twoSidedBarPrecompWhiskerIso_comp_hom_app]
  ext b₂
  rw [Functor.isoWhiskerLeft_hom]
  change (((twoSidedBarPrecompWhiskerIso (J ⋙ H) R L).hom.app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))).app b₂) =
      ((𝟙 _) ≫ (((twoSidedBarPrecompWhiskerIso (J ⋙ H) R L).hom.app
        (Opposite.op (SimplexCategory.mk (Opposite.unop Δ).len))).app b₂))
  exact (Category.id_comp _).symm

end PrecompFunctorLevel

end LeftPrecompOuter

end BarMap

end Monad
end CategoryTheory
