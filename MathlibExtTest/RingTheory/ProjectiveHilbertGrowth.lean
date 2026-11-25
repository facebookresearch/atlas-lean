/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.ProjectiveHilbertGrowth
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public noncomputable section

namespace MathlibExtTest.RingTheory.ProjectiveHilbertGrowth

open MvPolynomial MathlibExt.RingTheory.ProjectiveHilbertGrowth

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Macaulay expansions -/

/-- The zero expansion: every digit is inactive (`aᵢ = i`, so `aᵢ choose (i + 1) = 0`). -/
def zeroExpansion (d : ℕ) : MacaulayExpansion d 0 where
  upper i := i
  lowerBound _ := le_rfl
  strictMono _ _ h := h
  value_eq := by simp

-- Inactive digits stay inactive after the transform: `0 ^ ⟨d⟩ = 0`.
example (d : ℕ) : (zeroExpansion d).successor = 0 := by
  simp [MacaulayExpansion.successor, zeroExpansion]

/-- `4 = (3 choose 2) + (1 choose 1)`: the second Macaulay expansion of `4`. -/
def fourExpansion : MacaulayExpansion 2 4 where
  upper := ![1, 3]
  lowerBound i := by fin_cases i <;> decide
  strictMono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  value_eq := by decide

-- The transform raises both binomial indices: `4 ^ ⟨2⟩ = (4 choose 3) + (2 choose 2) = 5`.
example : fourExpansion.successor = 5 := by
  decide

/-- In degree one the expansion of `h` is `h choose 1`. -/
def degreeOneExpansion (h : ℕ) : MacaulayExpansion 1 h where
  upper _ := h
  lowerBound i := by rw [Fin.val_eq_zero i]; exact Nat.zero_le _
  strictMono := Subsingleton.strictMono _
  value_eq := by simp

-- Macaulay's degree-one bound is `h ^ ⟨1⟩ = (h + 1 choose 2)`.
example (h : ℕ) : (degreeOneExpansion h).successor = (h + 1).choose 2 := by
  simp [MacaulayExpansion.successor, degreeOneExpansion]

-- Every natural number has an expansion in each positive degree.
example (h : ℕ) : Nonempty (MacaulayExpansion 3 h) :=
  MacaulayExpansion.nonempty (by norm_num) h

-- In degree `0` only `0` has an expansion.
example (h : ℕ) (E : MacaulayExpansion 0 h) : h = 0 := by
  simpa using E.value_eq.symm

/-! ### Quotient pieces and the Hilbert function -/

variable {k : Type*} [Field k] {n : ℕ}

-- Every degree piece of a quotient is finite-dimensional, by instance search.
example (I : HomogeneousIdeal (homogeneousSubmodule (Fin n) k)) (d : ℕ) :
    Module.Finite k (quotientPiece I d) :=
  inferInstance

-- The zero ring `k[x] ⧸ ⊤` has Hilbert function zero.
example (d : ℕ) : hilbertFunction (k := k) (n := n) ⊤ d = 0 := by
  have : Subsingleton (MvPolynomial (Fin n) k ⧸
      (⊤ : HomogeneousIdeal (homogeneousSubmodule (Fin n) k)).toIdeal) := by
    rw [HomogeneousIdeal.toIdeal_top]
    exact Ideal.Quotient.subsingleton_iff.mpr rfl
  simp [hilbertFunction, Module.finrank_zero_of_subsingleton]

-- The degree-`0` piece of `k[x]` is spanned by the constants.
example : hilbertFunction (k := k) (n := n) ⊥ 0 = 1 := by
  have hinj : Function.Injective
      (Ideal.Quotient.mkₐ k
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) k)).toIdeal).toLinearMap := by
    intro p q h
    simpa [HomogeneousIdeal.toIdeal_bot, Ideal.Quotient.eq, sub_eq_zero] using h
  have hset : {d : Fin n →₀ ℕ | Finsupp.degree d = 0} = {0} := by
    ext d
    simp [Finsupp.degree_eq_zero_iff]
  rw [hilbertFunction, quotientPiece,
    ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _),
    homogeneousSubmodule_eq_finsupp_supported]
  rw [show {d : Fin n →₀ ℕ | Finsupp.degree d = 0} = {0} from hset]
  exact (Module.finrank_eq_nat_card_basis (basisRestrictSupport k {0})).trans (by simp)

-- The zero ideal is generated in every degree bound.
example (d : ℕ) : GeneratedThrough (k := k) (n := n) ⊥ d := by
  simp only [GeneratedThrough, HomogeneousIdeal.toIdeal_bot]
  refine le_antisymm bot_le (Ideal.span_le.mpr ?_)
  rintro f ⟨hf, -⟩
  exact hf

end MathlibExtTest.RingTheory.ProjectiveHilbertGrowth
