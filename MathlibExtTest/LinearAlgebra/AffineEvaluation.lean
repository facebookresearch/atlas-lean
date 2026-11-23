/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.AffineEvaluation
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

open Finset

-- Evaluation and interpolation over an infinite field need no finiteness assumption.
example : LinearEquiv.affineEvaluation (0 : ℚ) 2 (by norm_num) (2, 3) = (3, 7) := by
  norm_num

example : (LinearEquiv.affineEvaluation (0 : ℚ) 2 (by norm_num)).symm (3, 7) = (2, 3) := by
  norm_num

-- The exact bijection used in the ETH source follows from the linear equivalence.
example {F : Type*} [Field F] (theta theta' : F) (h : theta ≠ theta') :
    Function.Bijective fun p : F × F =>
      (p.1 * theta + p.2, p.1 * theta' + p.2) := by
  change Function.Bijective ⇑(LinearEquiv.affineEvaluation theta theta' h)
  exact (LinearEquiv.affineEvaluation theta theta' h).bijective

-- An arbitrary finite target has equally many coefficient pairs in its preimage.
example {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (theta theta' : F) (h : theta ≠ theta') (S : Finset (F × F)) :
    #{p : F × F | (p.1 * theta + p.2, p.1 * theta' + p.2) ∈ S} = #S := by
  exact card_equiv (LinearEquiv.affineEvaluation theta theta' h).toEquiv fun p => by
    simp

-- Every prescribed pair of values has one preimage over `ZMod 3`.
example :
    #{p : ZMod 3 × ZMod 3 | (p.1 * 0 + p.2, p.1 * 1 + p.2) = (1, 2)} = 1 := by
  decide

-- Prescribing one evaluation value leaves three choices for the other value.
example : #{p : ZMod 3 × ZMod 3 | p.1 * 0 + p.2 = 1} = Fintype.card (ZMod 3) := by
  decide

-- A two-by-two target rectangle has four preimages among the nine coefficient pairs.
example :
    #{p : ZMod 3 × ZMod 3 |
      (p.1 * 0 + p.2, p.1 * 1 + p.2) ∈
        ({0, 1} : Finset (ZMod 3)) ×ˢ ({1, 2} : Finset (ZMod 3))} = 4 := by
  decide

example :
    #{p : ZMod 3 × ZMod 3 |
      (p.1 * 0 + p.2, p.1 * 1 + p.2) ∈ (∅ : Finset (ZMod 3 × ZMod 3))} = 0 := by
  simp

example :
    #{p : ZMod 3 × ZMod 3 |
      (p.1 * 0 + p.2, p.1 * 1 + p.2) ∈ (univ : Finset (ZMod 3 × ZMod 3))} = 9 := by
  decide

-- Characteristic two uses the same inverse formula.
example : LinearEquiv.affineEvaluation (0 : ZMod 2) 1 (by decide) (1, 1) = (1, 0) := by
  decide

example : (LinearEquiv.affineEvaluation (0 : ZMod 2) 1 (by decide)).symm (1, 0) = (1, 1) := by
  rw [LinearEquiv.symm_apply_eq]
  decide

-- Distinctness is necessary: repeated evaluations cannot produce unequal values.
example : ¬ ∃ p : ZMod 3 × ZMod 3, (p.1 * 1 + p.2, p.1 * 1 + p.2) = (0, 1) := by
  decide
