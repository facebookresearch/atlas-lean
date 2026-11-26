/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Effective population size with separate sexes

A parental gene copy at an autosomal locus is identified by its origin (maternal or paternal),
the parent within that group, and one of the parent's two copies. We compute the probability that
copies sampled independently from two distinct offspring have the same such identity.
-/

open scoped BigOperators

namespace MathlibExt.Biology.PopulationGenetics.EffectivePopulationSizeSeparateSexes

private abbrev ParentalCopy (Nf Nm : ℕ) := (Fin Nf × Fin 2) ⊕ (Fin Nm × Fin 2)

-- The factors are a fair origin choice, a uniform parent given the origin,
-- and a fair choice between that parent's two Mendelian copies.
private noncomputable def originCopyMass (n : ℕ) : ℝ :=
  (1 / 2) * (1 / (n : ℝ)) * (1 / 2)

private noncomputable def copyMass {Nf Nm : ℕ} : ParentalCopy Nf Nm → ℝ
  | .inl _ => originCopyMass Nf
  | .inr _ => originCopyMass Nm

private theorem sum_originCopyMass {n : ℕ} (hn : 0 < n) :
    (∑ _ : Fin n × Fin 2, originCopyMass n) = 1 / 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [originCopyMass, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

-- The two origin branches form a normalized, nonnegative mass function.
private theorem copyMass_nonneg {Nf Nm : ℕ} (a : ParentalCopy Nf Nm) : 0 ≤ copyMass a := by
  cases a <;> simp only [copyMass, originCopyMass] <;> positivity

private theorem sum_copyMass {Nf Nm : ℕ} (hf : 0 < Nf) (hm : 0 < Nm) :
    (∑ a : ParentalCopy Nf Nm, copyMass a) = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [copyMass, sum_originCopyMass hf, sum_originCopyMass hm]
  norm_num

-- The two offspring are distinct, so the joint mass is the product of the two marginal masses.
-- The tags are part of the identity: copies of opposite origin cannot be equal.
public noncomputable def collisionProbability (Nf Nm : ℕ) : ℝ := by
  classical
  exact ∑ a : ParentalCopy Nf Nm, ∑ b : ParentalCopy Nf Nm,
    if a = b then copyMass a * copyMass b else 0

private theorem collisionProbability_eq {Nf Nm : ℕ} (hf : 0 < Nf) (hm : 0 < Nm) :
    collisionProbability Nf Nm = (1 / 8 : ℝ) * (1 / (Nf : ℝ) + 1 / (Nm : ℝ)) := by
  classical
  have diagonal (a : ParentalCopy Nf Nm) :
      (∑ b : ParentalCopy Nf Nm, if a = b then copyMass a * copyMass b else 0) =
        copyMass a * copyMass a := by
    simp [eq_comm (a := a)]
  have branch (n : ℕ) (hn : 0 < n) :
      (∑ _ : Fin n × Fin 2, originCopyMass n * originCopyMass n) = (1 / 8) * (1 / (n : ℝ)) := by
    rw [← Finset.sum_mul, sum_originCopyMass hn, originCopyMass]
    ring
  simp only [collisionProbability, diagonal]
  rw [Fintype.sum_sum_type]
  simp only [copyMass, branch Nf hf, branch Nm hm, mul_add]

/-- **Effective population size with separate sexes.** Suppose a diploid population has positive
integer female and male counts $N_f,N_m$. Sample one autosomal copy from each of two distinct
independent offspring. For each sampled copy, independently choose the maternal or paternal origin
with equal probability, choose a uniform parent of that origin, and choose one of its two copies
with equal probability. The probability $c$ of the same parental copy is
$\tfrac18(\tfrac1{N_f}+\tfrac1{N_m})$. The unique real size satisfying $c=1/(2N^*)$ is
$N^*=4N_fN_m/(N_f+N_m)>0$. It is at most $N_f+N_m$, with equality exactly when $N_f=N_m$.
This is the conventional one-generation size, not the distinct long-run approximation.

Source: J. Felsenstein, *Theoretical Evolutionary Genetics*, December 2019, §VI.6,
pp. 266–267, equations (VI-33)–(VI-35). -/
public theorem effective_population_size_separate_sexes (Nf Nm : ℕ) (hf : 0 < Nf) (hm : 0 < Nm) :
    let c := collisionProbability Nf Nm
    let nStar : ℝ := 4 * (Nf : ℝ) * (Nm : ℝ) / ((Nf : ℝ) + (Nm : ℝ))
    c = (1 / 8 : ℝ) * (1 / (Nf : ℝ) + 1 / (Nm : ℝ)) ∧
      0 < nStar ∧
      (∀ n : ℝ, c = 1 / (2 * n) ↔ n = nStar) ∧
      nStar ≤ (Nf : ℝ) + (Nm : ℝ) ∧
      (nStar = (Nf : ℝ) + (Nm : ℝ) ↔ Nf = Nm) := by
  dsimp only
  have hf' : 0 < (Nf : ℝ) := by exact_mod_cast hf
  have hm' : 0 < (Nm : ℝ) := by exact_mod_cast hm
  have hsum : 0 < (Nf : ℝ) + (Nm : ℝ) := add_pos hf' hm'
  have hc := collisionProbability_eq hf hm
  have hstar : 0 < 4 * (Nf : ℝ) * (Nm : ℝ) / ((Nf : ℝ) + (Nm : ℝ)) := by positivity
  have hmatch : collisionProbability Nf Nm =
      1 / (2 * (4 * (Nf : ℝ) * (Nm : ℝ) / ((Nf : ℝ) + (Nm : ℝ)))) := by
    rw [hc]
    field_simp
    ring
  refine ⟨hc, hstar, ?_, ?_, ?_⟩
  · intro n
    rw [hmatch, one_div, one_div, inv_inj]
    constructor <;> intro h <;> linarith only [h]
  · apply (div_le_iff₀ hsum).2
    nlinarith only [sq_nonneg ((Nf : ℝ) - (Nm : ℝ))]
  · rw [div_eq_iff hsum.ne']
    constructor
    · intro h
      have hs : ((Nf : ℝ) - (Nm : ℝ)) ^ 2 = 0 := by nlinarith only [h]
      rw [pow_two, mul_eq_zero, or_self, sub_eq_zero] at hs
      exact_mod_cast hs
    · rintro rfl
      ring

end MathlibExt.Biology.PopulationGenetics.EffectivePopulationSizeSeparateSexes
