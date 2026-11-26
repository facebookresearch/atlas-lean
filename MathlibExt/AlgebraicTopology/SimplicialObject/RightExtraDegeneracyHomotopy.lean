/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedRightExtraDegeneracy
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Tactic.Abel

/-!
# Terminal-face extra degeneracies and alternating augmentation

Let `X` be an augmented simplicial object in a preadditive category and let `s_n : X_n →
X_(n+1)` be a right extra degeneracy, with augmentation section `s'`. The alternating
differential satisfies `d s_0 = s' ε - id` in degree zero and the terminal-face recurrence in
positive degrees.

With a zero object, the augmentation to the point concentrated in degree zero and the section
from `s'` are a chain homotopy equivalence. The homotopy of the augmentation–section composite
with the identity has component `(-1)^n s_n`. It yields a quasi-isomorphism when the
alternating complex has homology in every degree. The single-zero augmentation and section
follow Joël Riou's extra-degeneracy homotopy construction.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicTopology
open scoped Simplicial BigOperators

universe v u

namespace CategoryTheory.SimplicialObject.Augmented.RightExtraDegeneracy

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {X : SimplicialObject.Augmented C} (ed : RightExtraDegeneracy X)

local notation "K" => CategoryTheory.Functor.obj (drop ⋙ alternatingFaceMapComplex C) X

/-- The degree-zero terminal extra-degeneracy identity.

For the alternating complex, extra degeneracy followed by the degree-one boundary equals the
augmentation followed by its section minus the identity. -/
theorem s_comp_d_zero :
    ed.s 0 ≫ (K).d 1 0 = X.hom.app (Opposite.op (SimplexCategory.mk 0)) ≫ ed.s' - 𝟙 _ := by
  simp only [Functor.comp_obj, drop_obj]
  rw [alternatingFaceMapComplex_obj_d]
  dsimp only [AlternatingFaceMapComplex.objD]
  rw [Fin.sum_univ_two, Preadditive.comp_add]
  have hlast : (1 : Fin 2) = Fin.last 1 := rfl
  simp only [Fin.val_zero, Fin.val_last,
    pow_zero, pow_one, one_smul, neg_one_smul, Preadditive.comp_neg,
    hlast, ed.s₀_comp_δ₀, ed.s_comp_δ_last, sub_eq_add_neg, Functor.id_obj]

/-- The successor terminal extra-degeneracy recurrence.

In degree `n+1`, the boundary after extra degeneracy equals extra degeneracy after the
previous boundary plus `(-1)^(n+2)` times the identity. -/
theorem s_comp_d_succ (n : ℕ) :
    ed.s (n + 1) ≫ (K).d ((n + 1) + 1) (n + 1) =
      (K).d (n + 1) n ≫ ed.s n + (-1 : ℤ) ^ ((n + 1) + 1) • 𝟙 _ := by
  simp only [Functor.comp_obj, drop_obj]
  rw [alternatingFaceMapComplex_obj_d, alternatingFaceMapComplex_obj_d]
  dsimp only [AlternatingFaceMapComplex.objD]
  rw [Preadditive.comp_sum, Fin.sum_univ_castSucc]
  simp only [Preadditive.comp_zsmul, Preadditive.sum_comp, Preadditive.zsmul_comp,
    ed.s_comp_δ, ed.s_comp_δ_last, Fin.val_castSucc, Fin.val_last,
    alternatingFaceMapComplex_obj_X]

section Homotopy

variable [HasZeroObject C]

/-- Homology of an augmentation point concentrated in degree zero.

In a preadditive category with a zero object, the single-zero chain complex on the
augmentation point has homology in every nonnegative degree. -/
local instance pointSingleHasHomology :
    ∀ n : ℕ, ((point ⋙ ChainComplex.single₀ C).obj X).HasHomology n := by
  intro n
  change ((ChainComplex.single₀ C).obj X.right).HasHomology n
  infer_instance

/-- The alternating chain augmentation of a right extra-degeneracy object.

The augmented simplicial structure gives a chain map from its alternating-face complex to the
augmentation point concentrated in degree zero. -/
def augmentation (_ed : RightExtraDegeneracy X) :
    K ⟶ (ChainComplex.single₀ C).obj X.right :=
  AlternatingFaceMapComplex.ε.app X

/-- The chain section supplied by a right extra degeneracy.

The augmentation section `s'` defines the degree-zero component of a chain map from the
single-zero point complex into the alternating complex. -/
def sectionMap : (ChainComplex.single₀ C).obj X.right ⟶ K :=
  (ChainComplex.fromSingle₀Equiv _ _).symm (by exact ed.s')

/-- The signed terminal extra-degeneracy chain homotopy.

The augmentation followed by its section is homotopic to the identity on alternating chains,
with component `(-1)^n s_n` from degree `n` to degree `n+1`. -/
def homotopy :
    _root_.Homotopy
      (augmentation ed ≫ sectionMap ed)
      (𝟙 K) where
  hom i := Pi.single (i + 1) ((-1 : ℤ) ^ i • ed.s i)
  zero i j hij := Pi.single_eq_of_ne (Ne.symm hij) _
  comm i := by
    dsimp only [augmentation, sectionMap]
    cases i with
    | zero =>
        rw [_root_.Homotopy.prevD_chainComplex, _root_.Homotopy.dNext_zero_chainComplex]
        simp only [HomologicalComplex.comp_f, AlternatingFaceMapComplex.ε_app_f_zero,
          HomologicalComplex.id_f, Pi.single_eq_same, pow_zero, one_smul, zero_add]
        have hs :
            (((ChainComplex.fromSingle₀Equiv ((alternatingFaceMapComplex C).obj X.left)
              X.right).symm ed.s').f 0) = ed.s' := by
          exact (ChainComplex.fromSingle₀Equiv
            ((alternatingFaceMapComplex C).obj X.left) X.right).apply_symm_apply ed.s'
        rw [ed.s_comp_d_zero]
        simp only [Functor.comp_obj, drop_obj, alternatingFaceMapComplex_obj_X,
          Functor.id_obj]
        abel_nf
        exact congrArg
          (fun f : X.right ⟶ ((alternatingFaceMapComplex C).obj X.left).X 0 =>
            X.hom.app (Opposite.op (SimplexCategory.mk 0)) ≫ f) hs
    | succ i =>
        rw [_root_.Homotopy.prevD_chainComplex, _root_.Homotopy.dNext_succ_chainComplex]
        simp only [HomologicalComplex.comp_f, AlternatingFaceMapComplex.ε_app_f_succ,
          zero_comp, HomologicalComplex.id_f, Pi.single_eq_same]
        have hsign : (-1 : ℤ) ^ (i + 1) = -((-1 : ℤ) ^ i) := by
          rw [pow_succ, mul_neg, mul_one]
        have hlast : (-1 : ℤ) ^ (i + 1) * (-1 : ℤ) ^ ((i + 1) + 1) = -1 := by
          rw [pow_succ (-1 : ℤ) (i + 1), ← mul_assoc, ← mul_pow]
          simp
        rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, ed.s_comp_d_succ,
          smul_add, smul_smul, hlast, hsign, neg_smul, neg_one_smul]
        abel

/-- The successor component of the terminal extra-degeneracy homotopy.

The homotopy map from degree `n` to degree `n+1` is `(-1)^n` times the right extra degeneracy. -/
theorem homotopy_hom_succ (n : ℕ) :
    (homotopy ed).hom n (n + 1) = (-1 : ℤ) ^ n • ed.s n := by
  simp only [homotopy, Pi.single_eq_same]

/-- The alternating augmentation equivalence from a right extra degeneracy.

The alternating complex is chain homotopy equivalent to the augmentation point concentrated in
degree zero, with forward map augmentation and inverse map the extra-degeneracy section. -/
def homotopyEquiv :
    _root_.HomotopyEquiv K ((ChainComplex.single₀ C).obj X.right) where
  hom := augmentation ed
  inv := sectionMap ed
  homotopyInvHomId := _root_.Homotopy.ofEq (by
    ext
    simp [augmentation, sectionMap,
      dsimp% ChainComplex.fromSingle₀Equiv_symm_apply_f_zero (C := K)])
  homotopyHomInvId := homotopy ed

/-- The forward map of the right extra-degeneracy augmentation equivalence.

The forward homotopy-equivalence map is the alternating-face augmentation to the single-zero
point complex. -/
theorem homotopyEquiv_hom :
    (homotopyEquiv ed).hom = AlternatingFaceMapComplex.ε.app X := rfl

/-- The right extra-degeneracy augmentation quasi-isomorphism.

If the alternating complex has homology in every nonnegative degree, its augmentation to the
point concentrated in degree zero is a quasi-isomorphism. -/
theorem quasiIso_augmentation (ed : RightExtraDegeneracy X)
    [∀ n : ℕ, (K).HasHomology n] :
    QuasiIso (AlternatingFaceMapComplex.ε.app X) := by
  exact (homotopyEquiv ed).quasiIso_hom

end Homotopy

end CategoryTheory.SimplicialObject.Augmented.RightExtraDegeneracy

end
