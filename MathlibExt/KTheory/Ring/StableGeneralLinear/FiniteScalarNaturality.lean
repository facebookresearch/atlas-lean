/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.Finite
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization

/-!
# Coefficient naturality of the actual finite general-linear diagram

The original rank transitions commute with the existing entrywise matrix
coefficient map. The ring universes remain independent. The proof uses only
finite stabilization and diagram composition; it imports no classifying
space, nerve, telescope or topological realization.
-/

noncomputable section

open CategoryTheory

universe uR uS

namespace AlgebraicKTheory.StableGL

variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]

/-- Let `R` and `S` be semirings, possibly in different
universes, `f : R →+* S`, `a ≤ b`, and `x : GL (Fin a) R`. Applying `f` entrywise after the
rank-`a` to rank-`b` stabilization over `R` equals stabilizing over `S` after applying `f`
entrywise to `x`. Both transitions are the maps of the actual finite GL diagrams for
the arrow `a ⟶ b`. -/
public theorem finiteGLDiagram_mapRingHom_naturality (f : R →+* S) {a b : ℕ}
    (p : a ⟶ b) (x : Matrix.GeneralLinearGroup (Fin a) R) :
    Matrix.GeneralLinearGroup.mapRingHom f
        ((finiteGLDiagram.obj (SemiRingCat.of R)).map p x) =
      (finiteGLDiagram.obj (SemiRingCat.of S)).map p
        (Matrix.GeneralLinearGroup.mapRingHom f x) := by
  have h : ∀ b (hab : a ≤ b) (x : Matrix.GeneralLinearGroup (Fin a) R),
      Matrix.GeneralLinearGroup.mapRingHom f
          ((finiteGLDiagram.obj (SemiRingCat.of R)).map (homOfLE hab) x) =
        (finiteGLDiagram.obj (SemiRingCat.of S)).map (homOfLE hab)
          (Matrix.GeneralLinearGroup.mapRingHom f x) := by
    intro b hab
    induction b, hab using Nat.le_induction with
    | base =>
        intro x
        have hi : (homOfLE (Nat.le_refl a) : a ⟶ a) = 𝟙 a := Subsingleton.elim _ _
        let z : Matrix.GeneralLinearGroup (Fin a) S :=
          Matrix.GeneralLinearGroup.mapRingHom f x
        have hR :
            (show Matrix.GeneralLinearGroup (Fin a) R from
              (finiteGLDiagram.obj (SemiRingCat.of R)).map (𝟙 a) x) = x :=
          ConcreteCategory.congr_hom
            ((finiteGLDiagram.obj (SemiRingCat.of R)).map_id a) x
        have hS :
            (show Matrix.GeneralLinearGroup (Fin a) S from
              (finiteGLDiagram.obj (SemiRingCat.of S)).map (𝟙 a) z) = z :=
          ConcreteCategory.congr_hom
            ((finiteGLDiagram.obj (SemiRingCat.of S)).map_id a) z
        have h1 :
            (Matrix.GeneralLinearGroup.mapRingHom f
              ((finiteGLDiagram.obj (SemiRingCat.of R)).map
                (homOfLE (Nat.le_refl a)) x) : Matrix.GeneralLinearGroup (Fin a) S) =
            Matrix.GeneralLinearGroup.mapRingHom f
              ((finiteGLDiagram.obj (SemiRingCat.of R)).map (𝟙 a) x) :=
          congrArg (fun q : a ⟶ a => Matrix.GeneralLinearGroup.mapRingHom f
            ((finiteGLDiagram.obj (SemiRingCat.of R)).map q x)) hi
        have h2 :
            (Matrix.GeneralLinearGroup.mapRingHom f
              ((finiteGLDiagram.obj (SemiRingCat.of R)).map (𝟙 a) x) :
                Matrix.GeneralLinearGroup (Fin a) S) = z :=
          congrArg (Matrix.GeneralLinearGroup.mapRingHom f) hR
        have h3 : z =
            (show Matrix.GeneralLinearGroup (Fin a) S from
              (finiteGLDiagram.obj (SemiRingCat.of S)).map (𝟙 a) z) :=
          hS.symm
        have h4 :
            (show Matrix.GeneralLinearGroup (Fin a) S from
              (finiteGLDiagram.obj (SemiRingCat.of S)).map (𝟙 a) z) =
            (show Matrix.GeneralLinearGroup (Fin a) S from
              (finiteGLDiagram.obj (SemiRingCat.of S)).map
                (homOfLE (Nat.le_refl a)) z) :=
          (congrArg (fun q : a ⟶ a =>
            (show Matrix.GeneralLinearGroup (Fin a) S from
              (finiteGLDiagram.obj (SemiRingCat.of S)).map q z)) hi).symm
        exact Eq.trans h1 (Eq.trans h2 (Eq.trans h3 h4))
    | succ b hab ih =>
        intro x
        have hs : (homOfLE (Nat.le_succ_of_le hab) : a ⟶ b + 1) =
            homOfLE hab ≫ homOfLE (Nat.le_add_right b 1) := Subsingleton.elim _ _
        rw [hs, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
          finiteGLDiagram_obj_map_succ, finiteGLDiagram_obj_map_succ]
        change Matrix.GeneralLinearGroup.mapRingHom f
            (Matrix.GeneralLinearGroup.stabilization R
              ((finiteGLDiagram.obj (SemiRingCat.of R)).map (homOfLE hab) x)) =
          Matrix.GeneralLinearGroup.stabilization S
            ((finiteGLDiagram.obj (SemiRingCat.of S)).map (homOfLE hab)
              (Matrix.GeneralLinearGroup.mapRingHom f x))
        exact (Matrix.GeneralLinearGroup.stabilization_mapRingHom_apply f _).symm.trans
          (congrArg (Matrix.GeneralLinearGroup.stabilization S) (ih x))
  have hp : p = homOfLE (leOfHom p) := Subsingleton.elim _ _
  rw [hp]
  exact h b (leOfHom p) x

end AlgebraicKTheory.StableGL

end
