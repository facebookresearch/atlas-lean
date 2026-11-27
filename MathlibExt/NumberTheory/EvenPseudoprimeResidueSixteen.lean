/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.EvenPseudoprime
import all MathlibExt.NumberTheory.EvenPseudoprimeWieferich
import Mathlib.Data.Nat.Factors

/-!
# Even pseudoprimes modulo sixteen

An even pseudoprime is twice an odd integer whose prime factors are all congruent to
`1` or `-1` modulo eight. The same alternatives hold for their product.

## References

* Xuyan Cheng, Paul Kinlaw and Duc Nguyen, *The Reciprocal Sum of Even Pseudoprimes*,
  Journal of Integer Sequences 29 (2026), Article 26.1.3, pp. 1–13, Corollary 4 and Lemma 2.
* Carl Pomerance and Samuel S. Wagstaff, Jr., *Some thoughts on pseudoprimes*, Bulletin de la
  Classe des Sciences, Mathématique 46 (2021), pp. 53–72, §4, Lemma 2 and Table 4. Their proof
  also uses that the base is a square modulo every odd prime factor of an even pseudoprime.
-/

public section

namespace MetaMathlibExt

/-- **Even pseudoprimes modulo 16.** Every even pseudoprime $N$ satisfies
$N \equiv 2 \pmod{16}$ or $N \equiv 14 \pmod{16}$.

Source: Cheng, Kinlaw and Nguyen, *The Reciprocal Sum of Even Pseudoprimes*, Journal of
Integer Sequences 29 (2026), Article 26.1.3, Corollary 4 (`jis-2026-26.1.3-cor-4`). -/
theorem evenPseudoprime_mod_sixteen {N : ℕ} (hN : MathlibExt.NumberTheory.IsEvenPseudoprime N) :
    N % 16 = 2 ∨ N % 16 = 14 := by
  have hNpos : 2 < N := hN.two_lt
  have hfour : ¬ 4 ∣ N := fun h ↦ EvenPseudoprimeWieferich.ne_two_of_sq_dvd hN h rfl
  obtain ⟨M, hM⟩ := even_iff_two_dvd.mp hN.even
  have hM0 : M ≠ 0 := by
    rintro rfl
    simp [hM] at hNpos
  have hM2 : ¬ 2 ∣ M := fun h ↦ hfour (hM ▸ Nat.mul_dvd_mul_left 2 h)
  have hMN : M ∣ N := hM ▸ dvd_mul_left M 2
  have hfactor (p : ℕ) (hp : p ∈ M.primeFactorsList) : p ≡ 1 [MOD 8] ∨ p ≡ 7 [MOD 8] := by
    have hd := Nat.dvd_of_mem_primeFactorsList hp
    have hp2 : p ≠ 2 := by rintro rfl; exact hM2 hd
    exact EvenPseudoprimeWieferich.mod_eight_of_dvd hN (Nat.prime_of_mem_primeFactorsList hp)
      hp2 (hd.trans hMN)
  have hprod (l : List ℕ) (hl : ∀ p ∈ l, p ≡ 1 [MOD 8] ∨ p ≡ 7 [MOD 8]) :
      l.prod ≡ 1 [MOD 8] ∨ l.prod ≡ 7 [MOD 8] := by
    induction l with
    | nil => exact Or.inl (Nat.ModEq.refl 1)
    | cons p l ih =>
      rw [List.prod_cons]
      rcases hl p (List.mem_cons_self ..) with hp | hp <;>
        rcases ih (fun q hq ↦ hl q (List.mem_cons_of_mem _ hq)) with h | h
      · exact Or.inl (hp.mul h)
      · exact Or.inr (hp.mul h)
      · exact Or.inr (hp.mul h)
      · exact Or.inl (hp.mul h)
  have h := hprod M.primeFactorsList hfactor
  rw [Nat.prod_primeFactorsList hM0] at h
  rcases h with h | h
  · exact Or.inl (hM ▸ h.mul_left' 2)
  · exact Or.inr (hM ▸ h.mul_left' 2)

end MetaMathlibExt
