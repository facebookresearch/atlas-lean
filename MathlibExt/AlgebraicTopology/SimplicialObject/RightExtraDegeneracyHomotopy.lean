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
# Terminal-face extra degeneracies and the original alternating complex

A right extra degeneracy contracts the actual alternating face-map complex
to its augmentation point. The native homotopy has component (-1)^n s_n.
The single-zero maps follow Mathlib's ExtraDegeneracy.homotopyEquiv
construction (Joël Riou); the signed cancellation uses the terminal face.
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

/-- The terminal contraction has the actual augmentation discrepancy in degree zero. -/
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

/-- Splitting the actual alternating differential at its terminal face gives the recurrence. -/
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

local instance pointSingleHasHomology :
    ∀ n : ℕ, ((point ⋙ ChainComplex.single₀ C).obj X).HasHomology n := by
  intro n
  change ((ChainComplex.single₀ C).obj X.right).HasHomology n
  infer_instance

/-- The actual native augmentation of the original alternating complex. -/
def augmentation (_ed : RightExtraDegeneracy X) :
    K ⟶ (ChainComplex.single₀ C).obj X.right :=
  AlternatingFaceMapComplex.ε.app X

/-- The actual degree-zero section induced by the right extra degeneracy. -/
def sectionMap : (ChainComplex.single₀ C).obj X.right ⟶ K :=
  (ChainComplex.fromSingle₀Equiv _ _).symm (by exact ed.s')

/-- The actual original-chain homotopy has component (-1)^n times the extra degeneracy. -/
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

/-- The actual homotopy's nonzero component retains the terminal-face sign. -/
theorem homotopy_hom_succ (n : ℕ) :
    (homotopy ed).hom n (n + 1) = (-1 : ℤ) ^ n • ed.s n := by
  simp only [homotopy, Pi.single_eq_same]

/-- A right extra degeneracy gives the native original-chain augmentation equivalence. -/
def homotopyEquiv :
    _root_.HomotopyEquiv K ((ChainComplex.single₀ C).obj X.right) where
  hom := augmentation ed
  inv := sectionMap ed
  homotopyInvHomId := _root_.Homotopy.ofEq (by
    ext
    simp [augmentation, sectionMap,
      dsimp% ChainComplex.fromSingle₀Equiv_symm_apply_f_zero (C := K)])
  homotopyHomInvId := homotopy ed

/-- The equivalence's forward map is the actual native augmentation. -/
theorem homotopyEquiv_hom :
    (homotopyEquiv ed).hom = AlternatingFaceMapComplex.ε.app X := rfl

/-- The actual augmentation is a quasi-isomorphism at the available native homology objects. -/
theorem quasiIso_augmentation (ed : RightExtraDegeneracy X)
    [∀ n : ℕ, (K).HasHomology n] :
    QuasiIso (AlternatingFaceMapComplex.ε.app X) := by
  exact (homotopyEquiv ed).quasiIso_hom

end Homotopy

end CategoryTheory.SimplicialObject.Augmented.RightExtraDegeneracy

end
