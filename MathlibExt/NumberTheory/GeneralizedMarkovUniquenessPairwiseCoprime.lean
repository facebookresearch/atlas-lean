/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedMarkovCharacteristic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.GeneralizedMarkovVietaEq

/-!
# Pairwise coprimality of generalized Markov triples

The entries of a generalized Markov triple are pairwise coprime.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.3 (citing Gyoda and
Matsushita, Corollary 8).
-/

namespace MetaMathlibExt.IsGenMarkovTriple

private theorem swap {k a b c : ℕ} (h : IsGenMarkovTriple k a b c) :
    IsGenMarkovTriple k b a c :=
  ⟨h.2.1, h.1, h.2.2.1, by nlinarith only [h.2.2.2]⟩

private theorem rotate {k a b c : ℕ} (h : IsGenMarkovTriple k a b c) :
    IsGenMarkovTriple k b c a :=
  ⟨h.2.1, h.2.2.1, h.1, by nlinarith only [h.2.2.2]⟩

private theorem descent {k a b c : ℕ} (h : IsGenMarkovTriple k a b c)
    (ha : 1 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    ∃ d : ℕ, IsGenMarkovTriple k a b d ∧ d < c ∧
      d + c + k * (a + b) = (3 + 3 * k) * a * b := by
  let d : ℤ := (3 + 3 * (k : ℤ)) * a * b - c - k * (a + b)
  have hprod : (a : ℤ) ^ 2 + k * a * b + b ^ 2 = c * d := h.vieta_eq.1
  have hroots : d + c + k * (a + b) = (3 + 3 * (k : ℤ)) * a * b := by
    dsimp [d]
    ring
  have hd : 0 < d := by
    apply pos_of_mul_pos_right (a := (c : ℤ)) _ (by positivity)
    rw [← hprod]
    positivity
  have habZ : (a : ℤ) ≤ b := by exact_mod_cast hab
  have hbcZ : (b : ℤ) ≤ c := by exact_mod_cast hbc
  have haZ : 1 < (a : ℤ) := by exact_mod_cast ha
  have hbZ : 0 < (b : ℤ) := by omega
  have habsq : (a : ℤ) ^ 2 ≤ b ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr habZ)
      (show 0 ≤ (b : ℤ) + a by positivity)]
  have hlead : 3 * (b : ℤ) ^ 2 < 3 * a * b ^ 2 := by
    nlinarith only [mul_pos (show 0 < (a : ℤ) - 1 by omega)
      (show 0 < (b : ℤ) ^ 2 by positivity)]
  have hkterm : (k : ℤ) * ((b : ℤ) ^ 2 + 2 * a * b) ≤ 3 * k * a * b ^ 2 := by
    nlinarith only [mul_nonneg (show 0 ≤ (b : ℤ) - 2 by omega)
      (show 0 ≤ (k : ℤ) * a * b by positivity),
      mul_nonneg (show 0 ≤ (a : ℤ) - 1 by omega)
        (show 0 ≤ (k : ℤ) * b ^ 2 by positivity),
      (show 0 ≤ (k : ℤ) * a * b ^ 2 by positivity)]
  have hf : (a : ℤ) ^ 2 + 2 * b ^ 2 + k * (b ^ 2 + 2 * a * b) <
      (3 + 3 * k) * a * b ^ 2 := by
    nlinarith only [habsq, hlead, hkterm]
  have hdb : d < b := by
    by_contra hdb
    have hfactor : 0 ≤ ((c : ℤ) - b) * (d - b) :=
      mul_nonneg (sub_nonneg.mpr hbcZ) (by omega)
    nlinarith only [hprod, congrArg (fun z : ℤ => (b : ℤ) * z) hroots, hf, hfactor]
  have hdcast : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd.le
  refine ⟨d.toNat, ⟨h.1, h.2.1, by omega, ?_⟩, by omega, ?_⟩
  · have he : (a : ℤ) ^ 2 + b ^ 2 + (d.toNat : ℤ) ^ 2 +
        k * (b * (d.toNat : ℤ) + (d.toNat : ℤ) * a + a * b) =
        (3 + 3 * k) * a * b * (d.toNat : ℤ) := by
      rw [hdcast]
      linear_combination d * hroots + hprod
    exact_mod_cast he
  · rw [← hdcast] at hroots
    exact_mod_cast hroots

private theorem no_common_prime {k a b c p : ℕ} (h : IsGenMarkovTriple k a b c)
    (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) (hpc : p ∣ c) : False := by
  suffices ∀ n a b c : ℕ, a + b + c = n → IsGenMarkovTriple k a b c →
      p ∣ a → p ∣ b → p ∣ c → False from this (a + b + c) a b c rfl h hpa hpb hpc
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have ordered (a b c : ℕ) (hs : a + b + c = n) (h : IsGenMarkovTriple k a b c)
        (hpa : p ∣ a) (hpb : p ∣ b) (hpc : p ∣ c) (hab : a ≤ b) (hbc : b ≤ c) : False := by
      have ha : 1 < a := hp.one_lt.trans_le (Nat.le_of_dvd h.1 hpa)
      obtain ⟨d, ht, hdc, hroots⟩ := descent h ha hab hbc
      have hpd : p ∣ d := by
        apply (Nat.dvd_add_iff_left (dvd_add hpc
          (dvd_mul_of_dvd_right (dvd_add hpa hpb) k))).mpr
        rw [← add_assoc, hroots]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpa _) b
      exact ih (a + b + d) (by omega) a b d rfl ht hpa hpb hpd
    intro a b c hs ht hpa hpb hpc
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      · exact ordered a b c hs ht hpa hpb hpc hab hbc
      · rcases le_total a c with hac | hca
        · exact ordered a c b (by omega) ht.rotate.rotate.swap hpa hpc hpb hac hcb
        · exact ordered c a b (by omega) ht.rotate.rotate hpc hpa hpb hca hab
    · rcases le_total a c with hac | hca
      · exact ordered b a c (by omega) ht.swap hpb hpa hpc hba hac
      · rcases le_total b c with hbc | hcb
        · exact ordered b c a (by omega) ht.rotate hpb hpc hpa hbc hca
        · exact ordered c b a (by omega) ht.rotate.swap hpc hpb hpa hcb hba

private theorem coprime_left {k a b c : ℕ} (h : IsGenMarkovTriple k a b c) :
    Nat.Coprime a b := by
  apply Nat.coprime_of_dvd'
  intro p hp hpa hpb
  have hpc : p ∣ c := by
    apply hp.dvd_of_dvd_pow (n := 2)
    have hs : p ∣ a ^ 2 + b ^ 2 + k * (b * c + c * a + a * b) :=
      dvd_add (dvd_add (dvd_pow hpa (by decide)) (dvd_pow hpb (by decide)))
        (dvd_mul_of_dvd_right (dvd_add (dvd_add (dvd_mul_of_dvd_left hpb c)
          (dvd_mul_of_dvd_right hpa c)) (dvd_mul_of_dvd_left hpa b)) k)
    apply (Nat.dvd_add_iff_right hs).mpr
    convert dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right hpa (3 + 3 * k)) b) c using 1
    nlinarith only [h.2.2.2]
  exact (no_common_prime h hp hpa hpb hpc).elim

/-- **Generalized Markov triples are pairwise coprime.** If $(a, b, c)$ is a $k$-generalized
Markov triple, then $\gcd(a, b) = \gcd(b, c) = \gcd(a, c) = 1$.

Source: Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That
Are Prime Powers*, INTEGERS 26 (2026), Article A91, Proposition 2.3 (citing Gyoda and
Matsushita, Corollary 8). -/
public theorem pairwise_coprime {k a b c : ℕ}
    (h : IsGenMarkovTriple k a b c) :
    Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c
    := by
  exact ⟨coprime_left h, coprime_left h.rotate, (coprime_left h.rotate.rotate).symm⟩

end MetaMathlibExt.IsGenMarkovTriple
