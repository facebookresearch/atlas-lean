/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Poset.OrderPolynomial

@[expose] public section

open MathlibExt.Combinatorics.Poset.OrderPolynomial

namespace MathlibExtTest.Combinatorics.Poset.OrderPolynomial

/-- One colour on the three-element chain. -/
example : orderPolynomialValue (Fin 3) 1 = 1 := orderPolynomialValue_one _

/-- `e_P(p) = e(P)` on the three-element chain. -/
example : surjMonotoneCount (Fin 3) (Fintype.card (Fin 3)) =
    (FinPoset.linearExtensions (Fin 3)).card :=
  surjMonotoneCount_card_eq _

/-- `e_P(p) = e(P)` on a product poset, where linear extensions are not unique. -/
example : surjMonotoneCount (Fin 2 × Fin 2) (Fintype.card (Fin 2 × Fin 2)) =
    (FinPoset.linearExtensions (Fin 2 × Fin 2)).card :=
  surjMonotoneCount_card_eq _

/-- Boundary: the empty poset has one order-preserving map to `[0]`, the empty map. -/
example : orderPolynomialValue Empty 0 = 1 := by
  unfold orderPolynomialValue
  have : Unique {σ : Empty → Fin 0 // Monotone σ} :=
    ⟨⟨⟨Empty.elim, fun a => a.elim⟩⟩, fun σ => Subtype.ext (funext fun a => a.elim)⟩
  exact Nat.card_unique

/-- The expansion on the two-element chain. -/
example (m : ℕ) : orderPolynomialValue (Fin 2) m =
    ∑ s ∈ Finset.range (Fintype.card (Fin 2) + 1), surjMonotoneCount (Fin 2) s * m.choose s :=
  orderPolynomialValue_eq_sum _ m

/-- Nothing maps onto `[4]` from a three-element poset. -/
example : surjMonotoneCount (Fin 3) 4 = 0 := surjMonotoneCount_eq_zero _ (by simp)

/-- The order polynomial of the product `Fin 2 × Fin 2` has degree `4`. -/
example : ∃ Q : Polynomial ℚ, Q.natDegree = 4 ∧
    ∀ m : ℕ, Q.eval (m : ℚ) = orderPolynomialValue (Fin 2 × Fin 2) m := by
  obtain ⟨Q, hdeg, -, heval⟩ := exists_orderPolynomial (Fin 2 × Fin 2)
  exact ⟨Q, by simpa using hdeg, heval⟩

/-- A concrete value: `Ω_{2-chain}(3) = C(4, 2) = 6` order-preserving maps `Fin 2 → Fin 3`. -/
example : orderPolynomialValue (Fin 2) 3 = 6 := by
  classical
  rw [orderPolynomialValue, Nat.card_eq_fintype_card]
  rfl

/-- `Fin 2 × Fin 2` has `e_P(4) = e(P) = 2` linear extensions, so the leading coefficient of its
order polynomial is `2/4!`. -/
example : surjMonotoneCount (Fin 2 × Fin 2) 4 = 2 := by
  classical
  rw [surjMonotoneCount, Nat.card_eq_fintype_card]
  rfl

end MathlibExtTest.Combinatorics.Poset.OrderPolynomial
