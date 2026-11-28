/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPolynomial.MacaulayGrowth

@[expose] public section

open MvPolynomial AlgebraicGeometry.HilbertFunctor

universe u

-- Consumer with the original binders.
example (n d : ℕ) (hd : 1 ≤ d) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) :
    Module.finrank K (piece J (d + 1)) ≤ Nat.macaulayPow d (Module.finrank K (piece J d)) :=
  MvPolynomial.finrank_piece_succ_le_macaulayPow n d hd K J hJ

-- The same consumer in a higher universe.
example (n d : ℕ) (hd : 1 ≤ d) (K : Type u) [Field K]
    (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) :
    Module.finrank K (piece J (d + 1)) ≤ Nat.macaulayPow d (Module.finrank K (piece J d)) :=
  MvPolynomial.finrank_piece_succ_le_macaulayPow n d hd K J hJ

/-! ### The projective Hilbert-growth formulation -/

section ProjectiveHilbertGrowth

open MathlibExt.RingTheory.ProjectiveHilbertGrowth

attribute [local instance] MvPolynomial.gradedAlgebra

-- Consumer with the binders of the projective Hilbert-growth statement.
example {k : Type*} [Field k] {n : ℕ} (I : HomogeneousIdeal (homogeneousSubmodule (Fin n) k))
    (d : ℕ) (hd : 0 < d) (E : MacaulayExpansion d (hilbertFunction I d)) :
    hilbertFunction I (d + 1) ≤ E.successor :=
  macaulay_growth I d hd E

-- The statement covers zero variables, where `k[x] = k`.
example {k : Type*} [Field k] (I : HomogeneousIdeal (homogeneousSubmodule (Fin 0) k))
    (E : MacaulayExpansion 1 (hilbertFunction I 1)) :
    hilbertFunction I 2 ≤ E.successor :=
  macaulay_growth I 1 Nat.one_pos E

-- Every second Macaulay expansion of `4` has transform `5`, whatever its indices.
example (E : MacaulayExpansion 2 4) : E.successor = 5 := by
  rw [E.successor_eq_macaulayPow, Nat.macaulayPow_succ_eq 1 4 3 (by decide) (by decide),
    Nat.macaulayPow_one]
  decide

-- The Hilbert function in degree `d` is the dimension of the graded piece `piece I d`.
example {k : Type*} [Field k] {n : ℕ}
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)) (d : ℕ) :
    hilbertFunction I d = Module.finrank k (piece I.toIdeal d) :=
  hilbertFunction_eq_finrank_piece I d

-- With the bridges, the bound reads `h(d + 1) ≤ h(d)^⟨d⟩` for the Hilbert function.
example {k : Type*} [Field k] {n : ℕ} (I : HomogeneousIdeal (homogeneousSubmodule (Fin n) k))
    (d : ℕ) (hd : 0 < d) :
    hilbertFunction I (d + 1) ≤ Nat.macaulayPow d (hilbertFunction I d) := by
  obtain ⟨E⟩ := MacaulayExpansion.nonempty hd (hilbertFunction I d)
  exact E.successor_eq_macaulayPow ▸ macaulay_growth I d hd E

end ProjectiveHilbertGrowth
