/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.TorusPolynomialDegreeModels

@[expose] public noncomputable section

open MathlibExt.AlgebraicGeometry.AlgebraicSplitTorusModels
open MathlibExt.AlgebraicGeometry.TorusPolynomialDegreeModels

namespace TorusPolynomialDegreeModelsTest

variable {r s : ℕ}

/-- Characters give linear forms additively. -/
example : linearCharacter (0 : Lattice r) = 0 := by
  simp [linearCharacter]

example (a b : Lattice r) :
    linearCharacter (a + b) = linearCharacter a + linearCharacter b := by
  simp [linearCharacter, add_mul, Finset.sum_add_distrib]

/-- The `j`-th coordinate character is the `j`-th variable. -/
example (j : Fin r) : linearCharacter (Pi.single j 1 : Lattice r) = MvPolynomial.X j := by
  simp [linearCharacter, Pi.single_apply]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (q : CharacterPolynomials s →ₐ[ℂ] CharacterPolynomials r)
  (ρ : CharacterPolynomials s →ₐ[ℂ] Module.End ℂ V)

/-- Zero satisfies every strict degree bound, including codimension zero. -/
example (c : ℕ) : strictHalfDegree q ρ c 0 := Or.inl rfl

/-- In codimension zero only the zero class has strictly smaller half degree. -/
example (a : RelativeTensor q ρ) (h : strictHalfDegree q ρ 0 a) : a = 0 := by
  rcases h with h | ⟨d, hd, _⟩
  · exact h
  · omega

/-- The degree filtration is increasing. -/
example {d e : ℕ} (h : d ≤ e) : relativeFiltration q ρ d ≤ relativeFiltration q ρ e := by
  apply Submodule.span_mono
  rintro x ⟨p, v, hp, rfl⟩
  exact ⟨p, v, hp.trans h, rfl⟩

end TorusPolynomialDegreeModelsTest
