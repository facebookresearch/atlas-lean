/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

@[expose] public section

/-!
# Concave symmetric welfare prefers equalization

A social welfare function `W` on income distributions is symmetric when relabeling
individuals does not change welfare. Mean-preserving equalization gives everyone the mean
income (`sum_equalize`).

If `W` is concave and symmetric then `W x ≤ W (equalize x)` (`le_welfare_equalize`): by
Jensen's inequality over all relabelings of `x`, whose average is the equalized distribution,
`W x = average of W (x ∘ σ) ≤ W (average of x ∘ σ) = W (equalize x)`. This is a normative
ordering, not an empirical law; concavity may be required only on a domain (such as the
positive orthant) that contains the relabelings of `x`.

## Main results

* `MathlibExt.Economics.SocialWelfare.sum_equalize`
* `MathlibExt.Economics.SocialWelfare.le_welfare_equalize`

Atlas roadmap target AP05.T04.
-/

namespace MathlibExt.Economics.SocialWelfare

open Finset

/-- Mean-preserving equalization of the income distribution `x`: every individual receives
the mean income `(∑ i, x i) / card ι`. -/
noncomputable def equalize {ι : Type*} [Fintype ι] (x : ι → ℝ) : ι → ℝ :=
  fun _ => (∑ i, x i) / Fintype.card ι

/-- A social welfare function is symmetric (anonymous) when relabeling individuals does not
change welfare. -/
def IsSymmetric {ι : Type*} (W : (ι → ℝ) → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm ι) (y : ι → ℝ), W (y ∘ σ) = W y

/-- Equalization preserves total income in a nonempty population. -/
theorem sum_equalize {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    ∑ i, equalize x i = ∑ i, x i := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [equalize, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_comm, div_mul_cancel₀ _ hcard]

/-- **A symmetric concave welfare function weakly prefers equalization.** If `W` is concave on
a set `s` that contains every relabeling of `x`, and `W` is symmetric, then replacing every
income by the mean does not lower welfare. -/
theorem le_welfare_equalize {ι : Type*} [Fintype ι] {W : (ι → ℝ) → ℝ} {s : Set (ι → ℝ)}
    (hW : ConcaveOn ℝ s W) (hsym : IsSymmetric W) (x : ι → ℝ)
    (hs : ∀ σ : Equiv.Perm ι, x ∘ σ ∈ s) :
    W x ≤ W (equalize x) := by
  classical
  rcases isEmpty_or_nonempty ι with hempty | hne
  · have hx : x = equalize x := funext fun i => (hempty.false i).elim
    exact le_of_eq (congrArg W hx)
  · have hn : 0 < Fintype.card ι := @Fintype.card_pos _ inferInstance hne
    have hfact : (((Fintype.card ι).factorial : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hw_nonneg : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
        0 ≤ (1 : ℝ) / (((Fintype.card ι).factorial : ℕ) : ℝ) := by
      intro σ _
      exact one_div_nonneg.mpr (Nat.cast_nonneg _)
    have hw_sum : ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
        (1 : ℝ) / (((Fintype.card ι).factorial : ℕ) : ℝ) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul,
        mul_one_div_cancel hfact]
    have hp_mem : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x ∘ σ ∈ s :=
      fun σ _ => hs σ
    have hJ : (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
          ((1 : ℝ) / (((Fintype.card ι).factorial : ℕ) : ℝ)) • W (x ∘ σ))
        ≤ W (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
          ((1 : ℝ) / (((Fintype.card ι).factorial : ℕ) : ℝ)) • (x ∘ σ)) :=
      hW.le_map_sum hw_nonneg hw_sum hp_mem
    have hLHS : (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
          ((1 : ℝ) / (((Fintype.card ι).factorial : ℕ) : ℝ)) • W (x ∘ σ)) = W x := by
      have h1 : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
          ((1 : ℝ) / (((Fintype.card ι).factorial : ℕ) : ℝ)) • W (x ∘ σ)
          = ((1 : ℝ) / (((Fintype.card ι).factorial : ℕ) : ℝ)) • W x := by
        intro σ _
        rw [hsym σ x]
      calc (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
            ((1 : ℝ) / (((Fintype.card ι).factorial : ℕ) : ℝ)) • W (x ∘ σ))
          = ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
            ((1 : ℝ) / (((Fintype.card ι).factorial : ℕ) : ℝ)) • W x :=
            Finset.sum_congr rfl h1
        _ = (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
            (1 : ℝ) / (((Fintype.card ι).factorial : ℕ) : ℝ)) • W x :=
            Finset.sum_smul.symm
        _ = W x := by rw [hw_sum, one_smul]
    have hconst : ∀ i₁ i₂ : ι,
        (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x (σ i₁))
        = ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x (σ i₂) := by
      intro i₁ i₂
      have happly : ∀ σ : Equiv.Perm ι,
          x ((Equiv.mulRight (Equiv.swap i₁ i₂) σ) i₁) = x (σ i₂) := by
        intro σ
        simp only [Equiv.coe_mulRight]
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      have hcongr : (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x (σ i₂))
          = ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
            x ((Equiv.mulRight (Equiv.swap i₁ i₂) σ) i₁) :=
        Finset.sum_congr rfl (fun σ _ => (happly σ).symm)
      have hreindex : (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
            x ((Equiv.mulRight (Equiv.swap i₁ i₂) σ) i₁))
          = ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x (σ i₁) :=
        Equiv.sum_comp (Equiv.mulRight (Equiv.swap i₁ i₂)) (fun σ => x (σ i₁))
      exact (hcongr.trans hreindex).symm
    have htotal : (∑ i ∈ (Finset.univ : Finset ι),
          ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x (σ i))
        = (((Fintype.card ι).factorial : ℕ) : ℝ)
          * ∑ j ∈ (Finset.univ : Finset ι), x j := by
      rw [Finset.sum_comm]
      have hinner : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
          (∑ i ∈ (Finset.univ : Finset ι), x (σ i))
          = ∑ i ∈ (Finset.univ : Finset ι), x i := by
        intro σ _
        exact Equiv.sum_comp σ x
      calc (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
            ∑ i ∈ (Finset.univ : Finset ι), x (σ i))
          = ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
            (∑ i ∈ (Finset.univ : Finset ι), x i) := Finset.sum_congr rfl hinner
        _ = (((Fintype.card ι).factorial : ℕ) : ℝ)
            * ∑ i ∈ (Finset.univ : Finset ι), x i := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (ne_of_gt hn)
    have hS : ∀ i : ι, (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x (σ i))
        = (((m.factorial : ℕ) : ℝ)) * ∑ j ∈ (Finset.univ : Finset ι), x j := by
      intro i
      have h1 : ∀ j ∈ (Finset.univ : Finset ι),
          (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x (σ j))
          = ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x (σ i) :=
        fun j _ => hconst j i
      have hsum : (∑ j ∈ (Finset.univ : Finset ι),
            ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x (σ j))
          = ((m + 1 : ℕ) : ℝ)
            * (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x (σ i)) := by
        calc (∑ j ∈ (Finset.univ : Finset ι),
              ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x (σ j))
            = ∑ j ∈ (Finset.univ : Finset ι),
              (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x (σ i)) :=
              Finset.sum_congr rfl h1
          _ = ((m + 1 : ℕ) : ℝ)
              * (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x (σ i)) := by
              rw [Finset.sum_const, Finset.card_univ, hm, nsmul_eq_mul]
      have h2 : ((m + 1 : ℕ) : ℝ)
          * (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x (σ i))
          = ((m + 1 : ℕ) : ℝ)
            * ((((m.factorial : ℕ) : ℝ)) * ∑ j ∈ (Finset.univ : Finset ι), x j) := by
        calc ((m + 1 : ℕ) : ℝ)
              * (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x (σ i))
            = ∑ j ∈ (Finset.univ : Finset ι),
              ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)), x (σ j) := hsum.symm
          _ = ((m + 1 : ℕ) : ℝ)
              * ((((m.factorial : ℕ) : ℝ)) * ∑ j ∈ (Finset.univ : Finset ι), x j) := by
              rw [hm, Nat.factorial_succ, Nat.cast_mul] at htotal
              linear_combination htotal
      have hne' : ((m + 1 : ℕ) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
      exact mul_left_cancel₀ hne' h2
    have hRHS : (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm ι)),
          ((1 : ℝ) / (((Fintype.card ι).factorial : ℕ) : ℝ)) • (x ∘ σ))
        = equalize x := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
      rw [← Finset.mul_sum, hS i]
      simp only [equalize]
      rw [hm, Nat.factorial_succ, Nat.cast_mul]
      have h1 : (((m.factorial : ℕ) : ℝ)) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have h2 : ((m + 1 : ℕ) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
      have h3 : ((m + 1 : ℕ) : ℝ) * (((m.factorial : ℕ) : ℝ)) ≠ 0 :=
        mul_ne_zero h2 h1
      field_simp
    rw [hLHS, hRHS] at hJ
    exact hJ

end MathlibExt.Economics.SocialWelfare
