/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.ElementaryDivisorsUniqueness
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

open scoped DirectSum

/-- Swapping the two factors does not change the multiset of exponents. -/
example : Multiset.map ![1, 2] (Finset.univ.val : Multiset (Fin 2))
    = Multiset.map ![2, 1] (Finset.univ.val : Multiset (Fin 2)) := by
  have hswap : (⨁ i : Fin 2, ZMod (2 ^ ![1, 2] i)) ≃+
      ⨁ k : Fin 2, ZMod (2 ^ ![1, 2] ((Equiv.swap (0 : Fin 2) 1).symm k)) :=
    DirectSum.equivCongrLeft (Equiv.swap (0 : Fin 2) 1)
  have h := elementary_divisors_unique (p := 2) (Nat.prime_two) (e := ![1, 2])
    (f := fun k => ![1, 2] ((Equiv.swap (0 : Fin 2) 1).symm k)) (by decide) (by decide)
    (A := ⨁ i : Fin 2, ZMod (2 ^ ![1, 2] i)) ⟨AddEquiv.refl _⟩ ⟨hswap⟩
  have hg_eq : (fun k => ![1, 2] ((Equiv.swap (0 : Fin 2) 1).symm k)) = ![2, 1] := by
    funext i
    fin_cases i <;> decide
  rw [hg_eq] at h
  exact h.2

/-- `ZMod 4` does not split as `ZMod 2 × ZMod 2`. -/
example : ¬ Nonempty ((⨁ i : Fin 1, ZMod (2 ^ ![2] i)) ≃+
    ⨁ i : Fin 2, ZMod (2 ^ ![1, 1] i)) := by
  rintro ⟨eB⟩
  have h := elementary_divisors_unique (p := 2) (Nat.prime_two) (e := ![2]) (f := ![1, 1])
    (by decide) (by decide) (A := ⨁ i : Fin 1, ZMod (2 ^ ![2] i)) ⟨AddEquiv.refl _⟩ ⟨eB⟩
  exact absurd h.1 (by decide)

/-- The two `2`-primary groups of order `16` with exponent multisets `{3, 1}`
and `{2, 2}` are not isomorphic. -/
example : ¬ Nonempty ((⨁ i : Fin 2, ZMod (2 ^ ![3, 1] i)) ≃+
    ⨁ i : Fin 2, ZMod (2 ^ ![2, 2] i)) := by
  rintro ⟨eB⟩
  have h := elementary_divisors_unique (p := 2) (Nat.prime_two) (e := ![3, 1]) (f := ![2, 2])
    (by decide) (by decide) (A := ⨁ i : Fin 2, ZMod (2 ^ ![3, 1] i))
    ⟨AddEquiv.refl _⟩ ⟨eB⟩
  have hne : Multiset.map ![3, 1] (Finset.univ.val : Multiset (Fin 2))
      ≠ Multiset.map ![2, 2] (Finset.univ.val : Multiset (Fin 2)) := by decide
  exact hne h.2

/-- The trivial group has the empty decomposition. -/
example : (0 : ℕ) = 0 ∧
    Multiset.map (![] : Fin 0 → ℕ) (Finset.univ.val : Multiset (Fin 0))
      = Multiset.map (![] : Fin 0 → ℕ) (Finset.univ.val : Multiset (Fin 0)) :=
  elementary_divisors_unique (p := 2) (Nat.prime_two) (e := ![]) (f := ![])
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (A := ⨁ i : Fin 0, ZMod (2 ^ (![] : Fin 0 → ℕ) i))
    ⟨AddEquiv.refl _⟩ ⟨AddEquiv.refl _⟩
