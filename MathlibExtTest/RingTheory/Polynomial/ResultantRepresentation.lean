/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Polynomial.ResultantRepresentation

@[expose] public section

universe u

-- Consumer with the original binders.
example (K : Type u) [Field K] (D : Polynomial ℤ → ℚ) (n : ℕ) (hn : Even n)
    (h1 : D 1 = 1)
    (hmul : ∀ G H : Polynomial ℤ, G.Monic → H.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
      ((H.coeff 0 : ℤ) : K) ≠ 0 → D (G * H) = D G * D H)
    (hpoly : ∀ b : ℕ, ∃ N : MvPolynomial (Fin (b + 1)) ℚ, N.totalDegree ≤ n ∧
      N.coeff (Finsupp.single 0 n) = 1 ∧
      ∀ G : Polynomial ℤ, G.Monic → G.natDegree = b + 1 → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        MvPolynomial.eval (fun i : Fin (b + 1) => ((G.coeff (i : ℕ) : ℤ) : ℚ)) N = D G) :
    ∃ P : Polynomial ℚ, P.Monic ∧ P.natDegree = n ∧
      ∀ G : Polynomial ℤ, G.Monic → ((G.coeff 0 : ℤ) : K) ≠ 0 →
        D G = (G.map (Int.castRingHom ℚ)).resultant P :=
  Polynomial.exists_monic_eq_resultant_of_mul_of_forall_exists_mvPolynomial
    K D n hn h1 hmul hpoly

-- Boundary case `n = 0`: for the constant function `1`, the representing
-- polynomial is `1`.
example : ∃ P : Polynomial ℚ, P = 1 := by
  obtain ⟨P, hP, hdeg, -⟩ :=
    Polynomial.exists_monic_eq_resultant_of_mul_of_forall_exists_mvPolynomial
      ℚ (fun _ => 1) 0 (Even.zero) rfl
      (fun G H _ _ _ _ => (mul_one (1 : ℚ)).symm)
      (fun b => ⟨1, by simp, by simp, fun G _ _ _ => by simp⟩)
  exact ⟨P, Polynomial.eq_one_of_monic_natDegree_zero hP hdeg⟩
