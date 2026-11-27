/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.Category

/-!
# Finite general linear groups as a categorical diagram

For each `n`, the assignment `R ↦ GL (Fin n) R` is a functor
`SemiRingCat ⥤ GrpCat` with coefficient maps given by `mapRingHom`.
Successor stabilization `GLₙ → GLₙ₊₁` assembles into a natural
transformation.  `Functor.ofSequence` packages the `ℕ`-indexed system
`ℕ ⥤ (SemiRingCat ⥤ GrpCat)` and `Functor.flip` yields
`SemiRingCat ⥤ (ℕ ⥤ GrpCat)`, the finite-GL stabilization diagram.
-/

@[expose] public section

namespace AlgebraicKTheory

open CategoryTheory Matrix

universe u

/-! ## Finite-rank GL functors -/

/-- For `n : ℕ`, the functor `SemiRingCat ⥤ GrpCat` on a fixed universe sends
a semiring `R` to `GL (Fin n) R` and a semiring homomorphism to its entrywise group map. -/
def finiteGLFunctor (n : ℕ) : SemiRingCat.{u} ⥤ GrpCat.{u} where
  obj R := GrpCat.of (Matrix.GeneralLinearGroup (Fin n) R)
  map {R S} f := GrpCat.ofHom (Matrix.GeneralLinearGroup.mapRingHom f.hom)
  map_id R := by
    have h : (𝟙 R : R ⟶ R).hom = RingHom.id R := rfl
    rw [h, Matrix.GeneralLinearGroup.mapRingHom_id]
    rfl
  map_comp {R S T} f g := by
    have hfg : (f ≫ g).hom = g.hom.comp f.hom := rfl
    rw [hfg, Matrix.GeneralLinearGroup.mapRingHom_comp]
    rfl

@[simp]
lemma finiteGLFunctor_obj (n : ℕ) (R : SemiRingCat.{u}) :
    (finiteGLFunctor n).obj R =
      GrpCat.of (Matrix.GeneralLinearGroup (Fin n) R) :=
  rfl

@[simp]
lemma finiteGLFunctor_obj_of (n : ℕ) (R : Type u) [Semiring R] :
    (finiteGLFunctor n).obj (SemiRingCat.of R) =
      GrpCat.of (Matrix.GeneralLinearGroup (Fin n) R) :=
  rfl

@[simp]
lemma finiteGLFunctor_map (n : ℕ) {R S : SemiRingCat.{u}} (f : R ⟶ S) :
    (finiteGLFunctor n).map f =
      GrpCat.ofHom (Matrix.GeneralLinearGroup.mapRingHom f.hom) :=
  rfl

@[simp]
lemma finiteGLFunctor_map_ofHom (n : ℕ) {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) :
    (finiteGLFunctor n).map (SemiRingCat.ofHom f) =
      GrpCat.ofHom (Matrix.GeneralLinearGroup.mapRingHom f) :=
  rfl

/-! ## Successor stabilization as a natural transformation -/

/-- For `n : ℕ`, the rank-`n` and rank-`n + 1` general linear group functors
on semirings are related by the natural transformation whose component at `R` sends
`g : GL (Fin n) R` to `diag(g, 1)` at rank `n + 1`. -/
def stabilizationNatTrans (n : ℕ) :
    finiteGLFunctor (n := n) ⟶ finiteGLFunctor (n + 1) where
  app R := GrpCat.ofHom (Matrix.GeneralLinearGroup.stabilization R)
  naturality {R S} f := by
    apply GrpCat.hom_ext
    simp only [finiteGLFunctor, GrpCat.hom_comp, GrpCat.hom_ofHom]
    exact Matrix.GeneralLinearGroup.stabilization_mapRingHom f.hom

@[simp]
lemma stabilizationNatTrans_app (n : ℕ) (R : SemiRingCat.{u}) :
    (stabilizationNatTrans n).app R =
      GrpCat.ofHom (Matrix.GeneralLinearGroup.stabilization R) :=
  rfl

lemma stabilizationNatTrans_app_of (n : ℕ) (R : Type u) [Semiring R] :
    (stabilizationNatTrans (n := n)).app (SemiRingCat.of R) =
      GrpCat.ofHom (Matrix.GeneralLinearGroup.stabilization R) :=
  rfl

/-! ## `ℕ`-indexed system and flipped diagram -/

/-- The sequence `ℕ ⥤ (SemiRingCat ⥤ GrpCat)` has the rank-`n` general linear
group functor at `n` and successor map with component `g ↦ diag(g, 1)` at every semiring `R`.
The transition from `a` to `b` for `a ≤ b` is the composite of these successor maps. -/
def finiteGLSequence : ℕ ⥤ SemiRingCat.{u} ⥤ GrpCat.{u} :=
  Functor.ofSequence (X := fun n => finiteGLFunctor (n := n))
    (fun n => stabilizationNatTrans (n := n))

@[simp]
lemma finiteGLSequence_obj (n : ℕ) :
    (finiteGLSequence : ℕ ⥤ SemiRingCat.{u} ⥤ GrpCat.{u}).obj n = finiteGLFunctor n :=
  rfl

@[simp]
lemma finiteGLSequence_map_succ (n : ℕ) :
    (finiteGLSequence : ℕ ⥤ SemiRingCat.{u} ⥤ GrpCat.{u}).map
      (homOfLE (Nat.le_add_right n 1)) =
      stabilizationNatTrans n :=
  Functor.OfSequence.map_le_succ _ _

/-- For each semiring `R`, this functor assigns the sequence with rank-`n`
group `GL (Fin n) R` and successor transition `g ↦ diag(g, 1)`. A semiring homomorphism
induces the natural transformation of these sequences whose components apply it entrywise.
Source and target semirings are in the same universe. -/
def finiteGLDiagram : SemiRingCat.{u} ⥤ ℕ ⥤ GrpCat.{u} :=
  finiteGLSequence.flip

@[simp]
lemma finiteGLDiagram_obj_obj (R : SemiRingCat.{u}) (n : ℕ) :
    (finiteGLDiagram.obj R).obj n =
      GrpCat.of (Matrix.GeneralLinearGroup (Fin n) R) :=
  rfl

@[simp]
lemma finiteGLDiagram_obj_obj_of (R : Type u) [Semiring R] (n : ℕ) :
    (finiteGLDiagram.obj (SemiRingCat.of R)).obj n =
      GrpCat.of (Matrix.GeneralLinearGroup (Fin n) R) :=
  rfl

@[simp]
lemma finiteGLDiagram_obj_map_succ (R : SemiRingCat.{u}) (n : ℕ) :
    (finiteGLDiagram.obj R).map (homOfLE (Nat.le_add_right n 1)) =
      GrpCat.ofHom (Matrix.GeneralLinearGroup.stabilization R) := by
  change (finiteGLSequence.map _).app R = _
  rw [finiteGLSequence_map_succ]
  rfl

@[simp]
lemma finiteGLDiagram_map_app (n : ℕ) {R S : SemiRingCat.{u}} (f : R ⟶ S) :
    (finiteGLDiagram.map f).app n =
      GrpCat.ofHom (Matrix.GeneralLinearGroup.mapRingHom f.hom) :=
  rfl

@[simp]
lemma finiteGLDiagram_map_app_ofHom (n : ℕ) {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) :
    (finiteGLDiagram.map (SemiRingCat.ofHom f)).app n =
      GrpCat.ofHom (Matrix.GeneralLinearGroup.mapRingHom f) :=
  rfl

end AlgebraicKTheory
