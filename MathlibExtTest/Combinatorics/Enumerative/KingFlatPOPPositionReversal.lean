/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import MathlibExt.Combinatorics.Enumerative.KingFlatPOPPositionReversal

/-! # Tests for position reversal of king permutations -/

namespace MetaMathlibExt

-- The empty king permutation avoids both patterns and contributes the constant monomial 1.
example : PowerSeries.coeff 0 (kingFlatPOPBelowGF 2) = 1 ∧
    PowerSeries.coeff 0
      (PowerSeries.map (MvPolynomial.rename
        ⇑(Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4))).toRingHom
          (kingFlatPOPBelowGF 1)) = 1 := by
  classical
  have coeff_zero (j : Fin 4) : PowerSeries.coeff 0 (kingFlatPOPBelowGF j) = 1 := by
    rw [coeff_kingFlatPOPBelowGF, Finset.sum_eq_single_of_mem (1 : Equiv.Perm (Fin 0))]
    · have ha : permAscentCount (1 : Equiv.Perm (Fin 0)) = 0 := by decide
      have hd : permDescentCount (1 : Equiv.Perm (Fin 0)) = 0 := by decide
      have hl : permLeftToRightMaxCount (1 : Equiv.Perm (Fin 0)) = 0 := by decide
      have hr : permRightToLeftMaxCount (1 : Equiv.Perm (Fin 0)) = 0 := by decide
      simp [ha, hd, hl, hr]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, isKingPerm_iff,
        containsFlatPOPBelow_iff]
      exact ⟨fun i => i.elim0, fun ⟨f, _⟩ => (f 0).elim0⟩
    · intro τ _ hτ
      exact (hτ (Subsingleton.elim τ 1)).elim
  exact ⟨coeff_zero 2, by rw [PowerSeries.coeff_map, coeff_zero, map_one]⟩

-- In one-based notation this king is 42531. Both pairs of statistics have unequal counts.
private def sampleKing : Equiv.Perm (Fin 5) :=
  ⟨![3, 1, 4, 2, 0], ![4, 1, 3, 0, 2], by decide, by decide⟩

private def reversedSampleKing : Equiv.Perm (Fin 5) := Fin.revPerm.trans sampleKing

example : IsKingPerm sampleKing ∧ IsKingPerm reversedSampleKing := by
  simp only [isKingPerm_iff]
  decide

example :
    (permAscentCount sampleKing, permDescentCount sampleKing,
      permLeftToRightMaxCount sampleKing, permRightToLeftMaxCount sampleKing) = (1, 3, 2, 3) ∧
    (permAscentCount reversedSampleKing, permDescentCount reversedSampleKing,
      permLeftToRightMaxCount reversedSampleKing, permRightToLeftMaxCount reversedSampleKing) =
        (3, 1, 3, 2) := by decide

-- The first four entries witness P₂; the last four entries of the reverse witness P₃.
example : ContainsFlatPOPBelow sampleKing 1 ∧ ContainsFlatPOPBelow reversedSampleKing 2 := by
  simp only [containsFlatPOPBelow_iff]
  constructor
  · exact ⟨OrderEmbedding.ofStrictMono (fun i : Fin 4 => ⟨i, i.isLt.trans (by decide)⟩)
      (fun _ _ h => h), by decide⟩
  · exact ⟨OrderEmbedding.ofStrictMono Fin.succ (fun _ _ h => Nat.succ_lt_succ h), by decide⟩

-- Enumerate the four-position witnesses as functions whose positions increase at each step.
private def avoidsFive (σ : Equiv.Perm (Fin 5)) (j : Fin 4) : Prop :=
  ¬ ∃ f : Fin 4 → Fin 5, (∀ i : Fin 3, f i.castSucc < f i.succ) ∧
    ∀ m, m ≠ j → σ (f j) < σ (f m)

private instance (σ : Equiv.Perm (Fin 5)) (j : Fin 4) : Decidable (avoidsFive σ j) := by
  unfold avoidsFive
  infer_instance

private theorem avoidsFive_iff (σ : Equiv.Perm (Fin 5)) (j : Fin 4) :
    avoidsFive σ j ↔ ¬ ContainsFlatPOPBelow σ j := by
  rw [avoidsFive, containsFlatPOPBelow_iff]
  apply not_congr
  constructor
  · rintro ⟨f, hmono, hbelow⟩
    exact ⟨OrderEmbedding.ofStrictMono f (Fin.strictMono_iff_lt_succ.mpr hmono), hbelow⟩
  · rintro ⟨f, hbelow⟩
    exact ⟨f, Fin.strictMono_iff_lt_succ.mp f.strictMono, hbelow⟩

private def statsFive (σ : Equiv.Perm (Fin 5)) : Fin 4 → ℕ :=
  ![permAscentCount σ, permDescentCount σ, permLeftToRightMaxCount σ, permRightToLeftMaxCount σ]

private noncomputable def degrees (e : Fin 4 → ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.onFinset Finset.univ e (fun i _ => Finset.mem_univ i)

-- Count directly over all 120 permutations, without using reversal or the series identity.
private def enumerateFive (j : Fin 4) (e : Fin 4 → ℕ) : ℤ :=
  ∑ σ : Equiv.Perm (Fin 5),
    if (∀ i k : Fin 5, (k : ℕ) = i + 1 → (σ i : ℕ) + 1 ≠ σ k ∧ (σ k : ℕ) + 1 ≠ σ i) ∧
      (∀ i, statsFive σ i = e i) ∧ avoidsFive σ j then 1 else 0

private theorem coeff_five_eq_enumerate (j : Fin 4) (e : Fin 4 → ℕ) :
    (PowerSeries.coeff 5 (kingFlatPOPBelowGF j)).coeff (degrees e) =
      enumerateFive j e := by
  classical
  rw [coeff_kingFlatPOPBelowGF, MvPolynomial.coeff_sum, Finset.sum_filter, enumerateFive]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hdegree : Finsupp.single 0 (permAscentCount σ) + Finsupp.single 1 (permDescentCount σ) +
      Finsupp.single 2 (permLeftToRightMaxCount σ) + Finsupp.single 3 (permRightToLeftMaxCount σ) =
        degrees (statsFive σ) := by
    ext i
    fin_cases i <;> simp [degrees, statsFive]
  have hmatch : degrees (statsFive σ) = degrees e ↔ ∀ i, statsFive σ i = e i := by
    constructor
    · intro h i
      exact DFunLike.congr_fun h i
    · intro h
      ext i
      exact h i
  simp only [isKingPerm_iff, ← avoidsFive_iff, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial, mul_one, MvPolynomial.coeff_monomial, hdegree, hmatch]
  split_ifs <;> simp_all

private noncomputable def renamedFive (s : Equiv.Perm (Fin 4)) :
    PowerSeries (MvPolynomial (Fin 4) ℤ) :=
  PowerSeries.map (MvPolynomial.rename ⇑s).toRingHom (kingFlatPOPBelowGF 1)

private theorem coeff_renamed_five_eq_enumerate (s : Equiv.Perm (Fin 4)) (e : Fin 4 → ℕ) :
    (PowerSeries.coeff 5 (renamedFive s)).coeff (degrees e) =
      enumerateFive 1 (e ∘ s) := by
  have h : (degrees (e ∘ s)).mapDomain ⇑s = degrees e := by
    ext i
    rw [Finsupp.mapDomain_equiv_apply]
    simp [degrees, Function.comp_def]
  rw [renamedFive, PowerSeries.coeff_map, ← h]
  exact (MvPolynomial.coeff_rename_mapDomain _ s.injective _ _).trans (coeff_five_eq_enumerate 1 _)

-- The coefficient of x⁵ p q³ u² v³ is 1 after both swaps, but 0 after either swap alone.
private noncomputable def probeFive (A : PowerSeries (MvPolynomial (Fin 4) ℤ)) : ℤ :=
  (PowerSeries.coeff 5 A).coeff (degrees ![1, 3, 2, 3])

example :
    probeFive (kingFlatPOPBelowGF 2) = 1 ∧
    probeFive (kingFlatPOPBelowGF 2) = probeFive (renamedFive (Equiv.swap 0 1 * Equiv.swap 2 3)) ∧
    probeFive (renamedFive (Equiv.swap 0 1 * Equiv.swap 2 3)) = 1 ∧
    probeFive (renamedFive (Equiv.swap 0 1)) = 0 ∧
    probeFive (renamedFive (Equiv.swap 2 3)) = 0 := by
  refine ⟨?_, congrArg probeFive kingFlatPOPBelowGF_two_eq_rename, ?_, ?_, ?_⟩
  · rw [probeFive, coeff_five_eq_enumerate]
    decide +kernel
  all_goals
    rw [probeFive, coeff_renamed_five_eq_enumerate]
    decide +kernel

end MetaMathlibExt
