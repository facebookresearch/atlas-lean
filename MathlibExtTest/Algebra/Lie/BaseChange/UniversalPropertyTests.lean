/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/

module

import MathlibExt.Algebra.Lie.BaseChange.UniversalProperty
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Reindex
meta import Mathlib.Tactic.NormNum

/-!
# The Lie scalar-extension Hom equivalence over a nonflat quotient

Integral two-by-two matrices map to matrices over `ZMod 6` by coefficient
reduction. Their Lie scalar extension has nonzero matrix-unit values and
the commutator has diagonal coefficients one and minus one. Nonzero
coefficients two and three can annihilate a commutator in this quotient.

Index exchange supplies nonidentity morphisms in both naturality squares.
The source integral matrix module carries no `ZMod 6`-action.
-/

noncomputable section

open scoped TensorProduct

namespace MathlibExtTest.LieBaseChangeUniversalProperty

attribute [local instance 100] LieRing.ofAssociativeRing

private abbrev S := ZMod 6
private abbrev L := Matrix (Fin 2) (Fin 2) ℤ
private abbrev N := Matrix (Fin 2) (Fin 2) S
private abbrev SL := S ⊗[ℤ] L

private def f : L →ₗ⁅ℤ⁆ N := ((Algebra.ofId ℤ S).mapMatrix : L →ₐ[ℤ] N)
private abbrev F : SL →ₗ⁅S⁆ N := LieHom.liftBaseChange ℤ S f
private abbrev E : (L →ₗ⁅ℤ⁆ N) ≃ (SL →ₗ⁅S⁆ N) :=
  LieHom.liftBaseChangeEquiv ℤ S L N

private def e01 : L := Matrix.single 0 1 1
private def e10 : L := Matrix.single 1 0 1
private abbrev x : SL := (5 : S) ⊗ₜ[ℤ] e01

private lemma f_e01 : f e01 = Matrix.single 0 1 (1 : S) := by
  change e01.map (algebraMap ℤ S) = Matrix.single 0 1 (1 : S)
  ext i j
  simp only [e01, Matrix.map_apply, Matrix.single_apply, apply_ite, map_one, map_zero]
  by_cases hij : (0 : Fin 2) = i ∧ (1 : Fin 2) = j
  · simp only [if_pos hij]
  · simp only [if_neg hij]

private lemma f_e10 : f e10 = Matrix.single 1 0 (1 : S) := by
  change e10.map (algebraMap ℤ S) = Matrix.single 1 0 (1 : S)
  ext i j
  simp only [e10, Matrix.map_apply, Matrix.single_apply, apply_ite, map_one, map_zero]
  by_cases hij : (1 : Fin 2) = i ∧ (0 : Fin 2) = j
  · simp only [if_pos hij]
  · simp only [if_neg hij]

private lemma F_entry01 (s : S) : F (s ⊗ₜ[ℤ] e01) 0 1 = s := by
  rw [LieHom.liftBaseChange_tmul, f_e01]
  simp [Matrix.smul_apply, Matrix.single_apply]

private lemma F_entry10 (s : S) : F (s ⊗ₜ[ℤ] e10) 1 0 = s := by
  rw [LieHom.liftBaseChange_tmul, f_e10]
  simp [Matrix.smul_apply, Matrix.single_apply]

private def sourceSwap : L →ₗ⁅ℤ⁆ L :=
  ((Matrix.reindexAlgEquiv ℤ ℤ (Equiv.swap (0 : Fin 2) 1)).toAlgHom : L →ₗ⁅ℤ⁆ L)

private def targetSwap : N →ₗ⁅S⁆ N :=
  ((Matrix.reindexAlgEquiv S S (Equiv.swap (0 : Fin 2) 1)).toAlgHom : N →ₗ⁅S⁆ N)

private lemma sourceSwap_e01 : sourceSwap e01 = e10 := by
  change Matrix.reindex (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1) e01 = e10
  decide

private lemma targetSwap_f_e01 : targetSwap (f e01) = f e10 := by
  rw [f_e01, f_e10]
  change Matrix.reindex (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
    (Matrix.single 0 1 (1 : S)) = Matrix.single 1 0 (1 : S)
  decide

example : ¬ Module.Flat ℤ S := by
  intro h
  letI : Module.Flat ℤ S := h
  letI : Module.IsTorsionFree ℤ S := Module.Flat.isTorsionFree
  have hzero : (6 : ℤ) • (1 : S) = 0 := by decide
  have hbad : (1 : S) = 0 :=
    (smul_eq_zero.mp hzero).resolve_left (by decide : (6 : ℤ) ≠ 0)
  exact (by decide : (1 : S) ≠ 0) hbad

example : F x 0 1 = 5 := F_entry01 5

example : (E f) x 0 1 = 5 := F_entry01 5

example : (E.symm F) e01 0 1 = 1 := by
  rw [LieHom.liftBaseChangeEquiv_symm_apply]
  exact F_entry01 1

example : E.symm (E f) = f := E.symm_apply_apply f

example : E (E.symm (targetSwap.comp F)) = targetSwap.comp F :=
  E.apply_symm_apply (targetSwap.comp F)

example : x ≠ 0 := by
  intro h
  have hv := congrArg (fun z : SL => F z 0 1) h
  rw [F_entry01] at hv
  simp only [map_zero, Matrix.zero_apply] at hv
  exact (by decide : (5 : S) ≠ 0) hv

example : F ⁅(1 : S) ⊗ₜ[ℤ] e01, (1 : S) ⊗ₜ[ℤ] e10⁆ 0 0 = 1 ∧
    F ⁅(1 : S) ⊗ₜ[ℤ] e01, (1 : S) ⊗ₜ[ℤ] e10⁆ 1 1 = 5 := by
  simp only [F.map_lie, LieHom.liftBaseChange_tmul, one_smul, f_e01, f_e10,
    LieRing.of_associative_ring_bracket]
  norm_num [Matrix.single_mul_single_same, Matrix.single_apply] <;> decide

example : F ⁅(2 : S) ⊗ₜ[ℤ] e01, (3 : S) ⊗ₜ[ℤ] e10⁆ = 0 ∧
    F ((2 : S) ⊗ₜ[ℤ] e01) ≠ 0 ∧ F ((3 : S) ⊗ₜ[ℤ] e10) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [LieAlgebra.ExtendScalars.bracket_tmul]
    have hscalar : (2 : S) * 3 = 0 := by decide
    rw [hscalar, TensorProduct.zero_tmul, map_zero]
  · intro h
    have hv := congrArg (fun n : N => n 0 1) h
    rw [F_entry01] at hv
    exact (by decide : (2 : S) ≠ 0) hv
  · intro h
    have hv := congrArg (fun n : N => n 1 0) h
    rw [F_entry10] at hv
    exact (by decide : (3 : S) ≠ 0) hv

example : (LieHom.liftBaseChange ℤ S (f.comp sourceSwap)) x 1 0 = 5 ∧
    F (LieHom.baseChange ℤ S sourceSwap x) 1 0 = 5 := by
  have hsquare := DFunLike.congr_fun (LieHom.liftBaseChange_comp ℤ S f sourceSwap) x
  have hvalue : (LieHom.liftBaseChange ℤ S (f.comp sourceSwap)) x 1 0 = 5 := by
    rw [LieHom.liftBaseChange_tmul, LieHom.comp_apply, sourceSwap_e01, f_e10]
    norm_num [Matrix.smul_apply, Matrix.single_apply]
  have he := congrArg (fun n : N => n (1 : Fin 2) 0) hsquare
  exact ⟨hvalue, he.symm.trans hvalue⟩

example : targetSwap (F x) 1 0 = 5 ∧
    (LieHom.liftBaseChange ℤ S ((LieHom.restrictScalars ℤ S targetSwap).comp f)) x 1 0 = 5 := by
  have hsquare := DFunLike.congr_fun (LieHom.comp_liftBaseChange ℤ S f targetSwap) x
  have hvalue : targetSwap (F x) 1 0 = 5 := by
    rw [LieHom.liftBaseChange_tmul, map_smul, targetSwap_f_e01, f_e10]
    norm_num [Matrix.smul_apply, Matrix.single_apply]
  have he := congrArg (fun n : N => n (1 : Fin 2) 0) hsquare
  exact ⟨hvalue, he.symm.trans hvalue⟩

end MathlibExtTest.LieBaseChangeUniversalProperty
