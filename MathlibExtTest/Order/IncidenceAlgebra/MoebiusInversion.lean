/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Order.IncidenceAlgebra.MoebiusInversion

@[expose] public section

open Finset IncidenceAlgebra MathlibExt.Order.IncidenceAlgebra.MoebiusInversion

namespace MathlibExtTest.Order.IncidenceAlgebra.MoebiusInversion

/-- Non-vacuity on `ℕ`: partial sums of the constant sequence `1` invert to `1`. -/
example (t : ℕ) : (1 : ℤ) = ∑ s ∈ Iic t, ((s : ℤ) + 1) * mu ℤ s t :=
  (moebius_inversion_iff (fun _ : ℕ => (1 : ℤ)) (fun t => (t : ℤ) + 1)).1
    (fun t => by simp [Nat.card_Iic]) t

/-- The converse direction of the dual form, on the finite chain `Fin 4`. -/
example (f g : Fin 4 → ℚ) (h : ∀ s, f s = ∑ t ∈ Ici s, mu ℚ s t * g t) (s : Fin 4) :
    g s = ∑ t ∈ Ici s, f t :=
  (moebius_inversion_dual_iff f g).2 h s

/-- The product theorem on `ℕ × ℕ`. -/
example : mu ℤ ((0 : ℕ), (1 : ℕ)) ((3 : ℕ), (1 : ℕ)) = mu ℤ (0 : ℕ) 3 * mu ℤ (1 : ℕ) 1 :=
  mu_prod_apply _ _ _ _

/-- The Möbius function of the Boolean algebra of subsets of `Fin 3`: `μ(∅, [3]) = -1`. -/
example : mu ℤ (∅ : Finset (Fin 3)) univ = -1 := by
  rw [mu_finset_of_subset (empty_subset _)]
  decide

/-- Boundary case `S = T`: `μ(S, S) = 1`. -/
example (S : Finset (Fin 3)) : mu ℤ S S = 1 := by
  rw [mu_finset_of_subset subset_rfl]
  simp

end MathlibExtTest.Order.IncidenceAlgebra.MoebiusInversion
