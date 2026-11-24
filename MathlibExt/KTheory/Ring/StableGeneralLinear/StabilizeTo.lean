/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.Stabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.StabilizeTo

/-!
# Finite target-size stabilization in `StableGL`

This file compares the explicit finite matrix map `stabilizeTo` with the
canonical finite-GL diagram.  Functorial coherence and invariance of the
stable class then follow without another matrix reindexing calculation.
-/

@[expose] public section

open CategoryTheory

noncomputable section

namespace AlgebraicKTheory
namespace StableGL

universe u

variable {R : Type u} [Semiring R]

private noncomputable abbrev finiteGLDiagramMap
    (R : Type u) [Semiring R] {n N : ℕ} (h : n ≤ N) :
    Matrix.GeneralLinearGroup (Fin n) R →*
      Matrix.GeneralLinearGroup (Fin N) R :=
  ((finiteGLDiagram.obj (SemiRingCat.of R)).map (homOfLE h)).hom

private theorem finiteGLDiagramMap_refl (R : Type u) [Semiring R]
    (n : ℕ) : finiteGLDiagramMap R (le_refl n) = MonoidHom.id _ := by
  let F := finiteGLDiagram.obj (SemiRingCat.of R)
  have harrow : homOfLE (le_refl n) = 𝟙 n := by
    apply Subsingleton.elim
  have hhom := congrArg GrpCat.Hom.hom
    (CategoryTheory.Functor.map_id F n)
  rw [GrpCat.hom_id] at hhom
  change (F.map (homOfLE (le_refl n))).hom = MonoidHom.id _
  rw [harrow]
  exact hhom

private theorem finiteGLDiagramMap_trans (R : Type u) [Semiring R]
    {n m N : ℕ} (hnm : n ≤ m) (hmN : m ≤ N) :
    (finiteGLDiagramMap R hmN).comp (finiteGLDiagramMap R hnm) =
      finiteGLDiagramMap R (hnm.trans hmN) := by
  let F := finiteGLDiagram.obj (SemiRingCat.of R)
  have hcomp : homOfLE hnm ≫ homOfLE hmN =
      homOfLE (hnm.trans hmN) := by
    apply Subsingleton.elim
  have hhom := congrArg GrpCat.Hom.hom
    (CategoryTheory.Functor.map_comp F
      (homOfLE hnm) (homOfLE hmN))
  rw [GrpCat.hom_comp] at hhom
  change (F.map (homOfLE hmN)).hom.comp
      (F.map (homOfLE hnm)).hom =
    (F.map (homOfLE (hnm.trans hmN))).hom
  rw [← hcomp]
  exact hhom.symm

private theorem finiteGLDiagramMap_succ (R : Type u) [Semiring R]
    (n : ℕ) :
    finiteGLDiagramMap R (Nat.le_add_right n 1) =
      Matrix.GeneralLinearGroup.stabilization R := by
  have hhom := congrArg GrpCat.Hom.hom
    (finiteGLDiagram_obj_map_succ (R := SemiRingCat.of R) n)
  change finiteGLDiagramMap R (Nat.le_add_right n 1) =
    Matrix.GeneralLinearGroup.stabilization R at hhom
  exact hhom

private theorem finiteGLDiagramMap_le_add (R : Type u) [Semiring R]
    (n m : ℕ) :
    finiteGLDiagramMap R (Nat.le_add_right n m) =
      Matrix.GeneralLinearGroup.blockStabilization n m R := by
  induction m with
  | zero =>
      apply MonoidHom.ext
      intro g
      exact DFunLike.congr_fun (finiteGLDiagramMap_refl R n) g |>.trans
        (Matrix.GeneralLinearGroup.blockStabilization_zero n R g).symm
  | succ m ih =>
      have hle₁ : n ≤ n + m := Nat.le_add_right n m
      have hle₂ : n + m ≤ (n + m) + 1 := Nat.le_add_right (n + m) 1
      have hle₃ : n ≤ n + (m + 1) := Nat.le_add_right n (m + 1)
      apply MonoidHom.ext
      intro g
      have htrans := DFunLike.congr_fun
        (finiteGLDiagramMap_trans R hle₁ hle₂) g
      have hstep := DFunLike.congr_fun
        (finiteGLDiagramMap_succ R (n + m))
        (Matrix.GeneralLinearGroup.blockStabilization n m R g)
      exact htrans.symm |>.trans
        (congrArg (finiteGLDiagramMap R hle₂) (DFunLike.congr_fun ih g) |>.trans
          (hstep.trans
            (Matrix.GeneralLinearGroup.blockStabilization_succ n m R g).symm))

private theorem finiteGLDiagramMap_cast (R : Type u) [Semiring R]
    {m n : ℕ} (h : m = n) :
    finiteGLDiagramMap R h.le =
      (Matrix.GeneralLinearGroup.reindexMulEquiv
        (finCongr h)).toMonoidHom := by
  cases h
  exact (finiteGLDiagramMap_refl R m).trans (by
    apply MonoidHom.ext
    intro g
    apply Units.ext
    change (g : Matrix (Fin m) (Fin m) R) =
      Matrix.reindex (Equiv.refl (Fin m)) (Equiv.refl (Fin m))
        (g : Matrix (Fin m) (Fin m) R)
    exact (Matrix.reindex_refl_refl _).symm)

/-- The explicit finite map `stabilizeTo` is the canonical arrow in the
finite-GL diagram. -/
theorem stabilizeTo_eq_finiteGLDiagram_map
    (R : Type u) [Semiring R] {n N : ℕ} (h : n ≤ N)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    Matrix.GeneralLinearGroup.stabilizeTo R h g =
      (finiteGLDiagram.obj (SemiRingCat.of R)).map (homOfLE h) g := by
  have hadd : n + (N - n) = N := Nat.add_sub_of_le h
  have hle : n ≤ n + (N - n) := Nat.le_add_right n (N - n)
  have hcast : n + (N - n) ≤ N := hadd.le
  have htotal : hle.trans hcast = h := Subsingleton.elim _ _
  have hfactor := DFunLike.congr_fun
    (finiteGLDiagramMap_trans R hle hcast) g
  have hblock := DFunLike.congr_fun
    (finiteGLDiagramMap_le_add R n (N - n)) g
  have hcastMap := DFunLike.congr_fun
    (finiteGLDiagramMap_cast R hadd)
    (Matrix.GeneralLinearGroup.blockStabilization n (N - n) R g)
  have htyped : Matrix.GeneralLinearGroup.stabilizeTo R h g =
      finiteGLDiagramMap R h g := by
    change Matrix.GeneralLinearGroup.reindexMulEquiv (finCongr hadd)
        (Matrix.GeneralLinearGroup.blockStabilization n (N - n) R g) =
      finiteGLDiagramMap R h g
    exact hcastMap.symm |>.trans
      (congrArg (finiteGLDiagramMap R hcast) hblock.symm |>.trans
        (hfactor.trans
          (congrArg (fun h' : n ≤ N => finiteGLDiagramMap R h' g) htotal)))
  exact htyped

/-- Stabilization to any larger finite size does not change the `StableGL`
class. -/
theorem of_stabilizeTo {n N : ℕ} (h : n ≤ N)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.of (Matrix.GeneralLinearGroup.stabilizeTo R h g) =
      StableGL.of g := by
  rw [stabilizeTo_eq_finiteGLDiagram_map]
  exact of_map (homOfLE h) g

end StableGL
end AlgebraicKTheory

namespace AlgebraicKTheory.StableGL

universe uCast

/-- Reindexing only by an equality of finite ranks preserves the original
stable representative. The proof uses the actual finite reindexing. -/
theorem of_reindex_finCongr {R : Type uCast} [Semiring R] {m n : ℕ} (h : m = n)
    (g : Matrix.GeneralLinearGroup (Fin m) R) :
    StableGL.of (Matrix.GeneralLinearGroup.reindexMulEquiv (finCongr h) g) =
      StableGL.of g := by
  cases h
  apply congrArg (fun a : Matrix.GeneralLinearGroup (Fin m) R => StableGL.of a)
  apply Units.ext
  exact Matrix.reindex_refl_refl _

end AlgebraicKTheory.StableGL

end
