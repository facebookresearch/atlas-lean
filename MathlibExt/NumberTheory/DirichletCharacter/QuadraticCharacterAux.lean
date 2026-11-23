/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DirichletCharacter.Quadratic

@[expose] public section

/-! Shared lemmas for the quadratic Dirichlet character construction. -/

namespace MetaMathlibExt

public theorem IsFundamentalDiscriminant.ne_zero (D : ℤ)
    (hD : IsFundamentalDiscriminant D) : D ≠ 0 := by
  rintro rfl
  cases hD with
  | inl hleft =>
    obtain ⟨_, hmod⟩ := hleft
    omega
  | inr hright =>
    obtain ⟨m, hm, hsqm, _⟩ := hright
    have hm0 : m = 0 := by omega
    have hdvd : (2 : ℤ) * 2 ∣ 0 := dvd_zero _
    have hsq0 : Squarefree (0 : ℤ) := by
      rw [← hm0]
      exact hsqm
    have hunit : IsUnit (2 : ℤ) := hsq0 2 hdvd
    have h2not : ¬ IsUnit (2 : ℤ) := by
      rw [Int.isUnit_iff]
      decide
    exact h2not hunit

public theorem IsFundamentalDiscriminant.natAbs_pos (D : ℤ)
    (hD : IsFundamentalDiscriminant D) : 0 < D.natAbs := by
  have hne : D ≠ 0 := IsFundamentalDiscriminant.ne_zero D hD
  exact Int.natAbs_pos.mpr hne

private theorem eq_one_of_natAbs_one_of_ne_neg_one (D : ℤ)
    (hN : D.natAbs = 1) (hD : D ≠ -1) : D = 1 := by
  have h12 : D = 1 ∨ D = -1 := by omega
  cases h12 with
  | inl h => exact h
  | inr h => exact absurd h hD

public theorem kroneckerSym_one_left (n : ℕ) :
    kroneckerSym 1 n = 1 := by
  by_cases hn0 : n = 0
  · subst hn0
    rw [kroneckerSym_zero]
    simp
  · simp only [kroneckerSym, hn0, if_false]
    apply List.prod_eq_one
    intro x hx
    obtain ⟨p, hp_mem, hpx⟩ := List.mem_map.mp hx
    have hp_prime : p.Prime :=
      Nat.prime_of_mem_primeFactorsList hp_mem
    rw [← hpx]
    by_cases hp2 : p = 2
    · subst hp2
      rw [kroneckerAtPrime_two]
      decide
    · have : Fact p.Prime := ⟨hp_prime⟩
      simp [kroneckerAtPrime, hp2, hp_prime]

public theorem kroneckerSym_mul (D : ℤ)
    (hD : D ≠ -1) (m n : ℕ) :
    kroneckerSym D (m * n) =
      kroneckerSym D m * kroneckerSym D n := by
  by_cases hm : m = 0
  · subst hm
    rw [zero_mul]
    have h0 : kroneckerSym D 0 =
        if D.natAbs = 1 then 1 else 0 :=
      kroneckerSym_zero D
    by_cases hN : D.natAbs = 1
    · have hD1 : D = 1 :=
        eq_one_of_natAbs_one_of_ne_neg_one D hN hD
      subst hD1
      rw [kroneckerSym_one_left 0,
        kroneckerSym_one_left n, mul_one]
    · rw [h0, ite_eq_right hN, zero_mul]
  · by_cases hn : n = 0
    · subst hn
      rw [mul_zero]
      have h0 : kroneckerSym D 0 =
          if D.natAbs = 1 then 1 else 0 :=
        kroneckerSym_zero D
      by_cases hN : D.natAbs = 1
      · have hD1 : D = 1 :=
            eq_one_of_natAbs_one_of_ne_neg_one D hN hD
        subst hD1
        rw [kroneckerSym_one_left m,
          kroneckerSym_one_left 0, mul_one]
      · rw [h0, ite_eq_right hN, mul_zero]
    · have hmn : m * n ≠ 0 := mul_ne_zero hm hn
      have hperm : (m * n).primeFactorsList.Perm
          (m.primeFactorsList ++ n.primeFactorsList) :=
        Nat.perm_primeFactorsList_mul hm hn
      simp only [kroneckerSym, hmn, if_false, hm, hn]
      have hmap := hperm.map (kroneckerAtPrime D)
      have hperm_prod := hmap.prod_eq
      rw [List.map_append, List.prod_append] at hperm_prod
      exact hperm_prod

/-- **Kronecker and Jacobi symbols agree at odd primes.** For every integer $D$ and every prime
$p \ne 2$, the Kronecker symbol $\left(\frac{D}{p}\right)$ equals the Jacobi symbol
$\left(\frac{D}{p}\right)$. -/
public theorem kroneckerSym_eq_jacobiSym_of_prime_ne_two (D : ℤ)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    kroneckerSym D p = jacobiSym D p := by
  have : Fact p.Prime := ⟨hp⟩
  have hprime_eq : kroneckerSym D p = kroneckerAtPrime D p :=
    kroneckerSym_prime D p hp
  have h_at : kroneckerAtPrime D p = legendreSym p D := by
    simp [kroneckerAtPrime, hp2, hp]
  have hleg : legendreSym p D = jacobiSym D p :=
    jacobiSym.legendreSym.to_jacobiSym p D
  rw [hprime_eq, h_at, hleg]

end MetaMathlibExt

end
