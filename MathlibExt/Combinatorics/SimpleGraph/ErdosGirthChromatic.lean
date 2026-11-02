/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open Finset

private noncomputable def ehgWeight {α : Type*} [Fintype α] [DecidableEq α] (p : ℝ) (E : Finset α) :
    ℝ :=
  p ^ E.card * (1 - p) ^ Eᶜ.card

private theorem ehg_prod_avoid {α : Type*} [DecidableEq α]
    (p : ℝ) (T E : Finset α) (ha : ∀ i ∈ E, i ∉ T) :
    (∏ i ∈ E, (if i ∈ T then (0 : ℝ) else p)) = p ^ E.card := by
  have hcongr : (∏ i ∈ E, (if i ∈ T then (0 : ℝ) else p)) = ∏ _i ∈ E, p :=
    Finset.prod_congr rfl (fun i hi => by simp [ha i hi])
  rw [hcongr, Finset.prod_const]

private theorem ehg_prod_hit {α : Type*} [DecidableEq α]
    (p : ℝ) (T E : Finset α) (ha : ¬ ∀ i ∈ E, i ∉ T) :
    (∏ i ∈ E, (if i ∈ T then (0 : ℝ) else p)) = 0 := by
  push Not at ha
  obtain ⟨i, hi, hTi⟩ := ha
  exact Finset.prod_eq_zero hi (by simp [hTi])

private theorem ehg_weight_sum_subset_disjoint {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (F T : Finset α) (hFT : Disjoint F T) :
    ∑ E ∈ (Finset.univ.powerset), (if F ⊆ E ∧ Disjoint E T then ehgWeight p E else 0)
      = p ^ F.card * (1 - p) ^ T.card := by
  have key : ∀ E : Finset α,
      (∏ i ∈ E, (if i ∈ T then (0 : ℝ) else p)) * ∏ i ∈ Finset.univ \ E,
          (if i ∈ F then (0 : ℝ) else 1 - p)
      = (if F ⊆ E ∧ Disjoint E T then ehgWeight p E else 0) := by
    intro E
    by_cases h1 : F ⊆ E ∧ Disjoint E T
    · obtain ⟨hFE, hET⟩ := h1
      have ha : ∀ i ∈ E, i ∉ T := fun i hi hTi => (Finset.disjoint_left.mp hET) hi hTi
      have hb : ∀ i ∈ Finset.univ \ E, i ∉ F := by
        intro i hi hFi
        rw [Finset.mem_sdiff] at hi
        exact hi.2 (hFE hFi)
      have hite : (if F ⊆ E ∧ Disjoint E T then ehgWeight p E else (0 : ℝ)) = ehgWeight p E := by
        simp [hFE, hET]
      rw [hite, ehg_prod_avoid p T E ha, ehg_prod_avoid (1 - p) F _ hb]
      unfold ehgWeight
      rw [Finset.compl_eq_univ_sdiff]
    · have hite : (if F ⊆ E ∧ Disjoint E T then ehgWeight p E else (0 : ℝ)) = 0 := by
        simp [h1]
      rw [hite]
      by_cases hET : Disjoint E T
      · have hFE : ¬ F ⊆ E := fun h => h1 ⟨h, hET⟩
        have hb : ¬ ∀ i ∈ Finset.univ \ E, i ∉ F := by
          intro hall
          apply hFE
          intro x hx
          by_contra hxE
          exact hall x (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxE⟩) hx
        rw [ehg_prod_hit (1 - p) F _ hb, mul_zero]
      · have ha : ¬ ∀ i ∈ E, i ∉ T := by
          intro hall
          apply hET
          rw [Finset.disjoint_left]
          exact hall
        rw [ehg_prod_hit p T E ha, zero_mul]
  have h := Finset.prod_add (fun e => (if e ∈ T then (0 : ℝ) else p))
    (fun e => (if e ∈ F then (0 : ℝ) else 1 - p)) Finset.univ
  have prodval : ∏ e ∈ (Finset.univ : Finset α),
      ((if e ∈ T then (0 : ℝ) else p) + (if e ∈ F then (0 : ℝ) else 1 - p))
      = p ^ F.card * (1 - p) ^ T.card := by
    have hsplit : ∀ e ∈ (Finset.univ : Finset α),
        ((if e ∈ T then (0 : ℝ) else p) + (if e ∈ F then (0 : ℝ) else 1 - p))
        = (if e ∈ F then p else 1) * (if e ∈ T then (1 - p) else 1) := by
      intro e _
      by_cases heF : e ∈ F
      · have heT : e ∉ T := fun h => (Finset.disjoint_left.mp hFT) heF h
        simp [heF, heT]
      · by_cases heT : e ∈ T
        · simp [heF, heT]
        · simp [heF, heT]
    rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib]
    have hF : ∏ e ∈ (Finset.univ : Finset α), (if e ∈ F then (p : ℝ) else 1) = p ^ F.card := by
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
        Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hT : ∏ e ∈ (Finset.univ : Finset α), (if e ∈ T then ((1 : ℝ) - p) else 1)
        = (1 - p) ^ T.card := by
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
        Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [hF, hT]
  rw [prodval] at h
  calc (∑ E ∈ (Finset.univ.powerset), (if F ⊆ E ∧ Disjoint E T then ehgWeight p E else 0))
      = ∑ E ∈ (Finset.univ.powerset),
        ((∏ i ∈ E, (if i ∈ T then (0 : ℝ) else p))
          * ∏ i ∈ Finset.univ \ E, (if i ∈ F then (0 : ℝ) else 1 - p)) :=
        Finset.sum_congr rfl (fun E _ => (key E).symm)
    _ = p ^ F.card * (1 - p) ^ T.card := h.symm

/-- Total mass: weights sum to 1. -/
private theorem ehg_weight_sum_univ {α : Type*} [Fintype α] [DecidableEq α] (p : ℝ) :
    ∑ E ∈ (Finset.univ.powerset : Finset (Finset α)), ehgWeight p E = 1 := by
  have h := ehg_weight_sum_subset_disjoint p (∅ : Finset α) (∅ : Finset α)
    (Finset.disjoint_empty_right _)
  simp only [Finset.card_empty, pow_zero, mul_one] at h
  have hcond : ∀ E : Finset α, (if (∅ : Finset α) ⊆ E ∧ Disjoint E (∅ : Finset α)
      then ehgWeight p E else 0) = ehgWeight p E := by
    intro E
    simp [Finset.empty_subset, Finset.disjoint_empty_right]
  rw [Finset.sum_congr rfl (fun E _ => hcond E)] at h
  exact h

/-- Marginal: sum over E ⊇ F equals p^|F|. -/
private theorem ehg_weight_sum_superset {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (F : Finset α) :
    ∑ E ∈ (Finset.univ.powerset : Finset (Finset α)),
      (if F ⊆ E then ehgWeight p E else 0) = p ^ F.card := by
  have h := ehg_weight_sum_subset_disjoint p F (∅ : Finset α) (Finset.disjoint_empty_right _)
  simp only [Finset.card_empty, pow_zero, mul_one] at h
  have hcond : ∀ E : Finset α, (if F ⊆ E ∧ Disjoint E (∅ : Finset α)
      then ehgWeight p E else 0) = (if F ⊆ E then ehgWeight p E else 0) := by
    intro E
    by_cases hFE : F ⊆ E <;> simp [hFE, Finset.disjoint_empty_right]
  rw [Finset.sum_congr rfl (fun E _ => hcond E)] at h
  exact h

/-- Marginal: sum over E disjoint from T equals (1-p)^|T|. -/
private theorem ehg_weight_sum_disjoint {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (T : Finset α) :
    ∑ E ∈ (Finset.univ.powerset : Finset (Finset α)),
      (if Disjoint E T then ehgWeight p E else 0) = (1 - p) ^ T.card := by
  have h := ehg_weight_sum_subset_disjoint p (∅ : Finset α) T (by simp : Disjoint (∅ : Finset α) T)
  simp only [Finset.card_empty, pow_zero, one_mul] at h
  have hcond : ∀ E : Finset α, (if (∅ : Finset α) ⊆ E ∧ Disjoint E T
      then ehgWeight p E else 0) = (if Disjoint E T then ehgWeight p E else 0) := by
    intro E
    by_cases hET : Disjoint E T <;> simp [hET, Finset.empty_subset]
  rw [Finset.sum_congr rfl (fun E _ => hcond E)] at h
  exact h

/-- Nonnegativity of weights for p ∈ [0,1]. -/
private theorem ehg_weight_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset α) : 0 ≤ ehgWeight p E := by
  unfold ehgWeight
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

/-- In `Fin (j+3)`, `a = b+1` and `a+1 = b` are contradictory. -/
private theorem ehg_fin_add_two_ne {j : ℕ} {a b : Fin (j + 3)} (e1 : a = b + 1) (e2 : a + 1 = b) :
    False := by
  have h : ((b + 1 : Fin (j + 3))).val = (b.val + 1) % (j + 3) := by rw [Fin.val_add]; simp
  rw [← e1] at h
  have h' : ((a + 1 : Fin (j + 3))).val = (a.val + 1) % (j + 3) := by rw [Fin.val_add]; simp
  rw [e2] at h'
  have c1 : b.val + 1 < j + 3 ∨ b.val + 1 = j + 3 := by
    have := Fin.is_lt b
    omega
  have c2 : a.val + 1 < j + 3 ∨ a.val + 1 = j + 3 := by
    have := Fin.is_lt a
    omega
  rcases c1 with hlt | heq <;> rcases c2 with hlt2 | heq2
  · rw [Nat.mod_eq_of_lt hlt] at h
    rw [Nat.mod_eq_of_lt hlt2] at h'
    omega
  · rw [Nat.mod_eq_of_lt hlt] at h
    rw [heq2, Nat.mod_self] at h'
    omega
  · rw [heq, Nat.mod_self] at h
    rw [Nat.mod_eq_of_lt hlt2] at h'
    omega
  · rw [heq, Nat.mod_self] at h
    rw [heq2, Nat.mod_self] at h'
    omega

/-- Cycle-edge set of a cyclic tuple. -/
private def ehgCycleEdges {V : Type*} [DecidableEq V] (j : ℕ) (f : Fin (j + 3) → V) : Finset
    (Sym2 V) :=
  Finset.univ.image (fun i => s(f i, f (i + 1)))

/-- The cycle-edge set of an injective tuple has full cardinality. -/
private theorem ehg_card_cycleEdges {V : Type*} [DecidableEq V] (j : ℕ) (f : Fin (j + 3) → V)
    (hf : Function.Injective f) : (ehgCycleEdges j f).card = j + 3 := by
  unfold ehgCycleEdges
  rw [Finset.card_image_of_injective _ (by
    intro a b hab
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact hf h1
    · exact (ehg_fin_add_two_ne (hf h1) (hf h2)).elim)]
  simp [Finset.card_univ, Fintype.card_fin]

/-- Number of short-cycle witnesses in an edge set. -/
private noncomputable def ehgShortCycleCount (n g : ℕ) (E : Finset (Sym2 (Fin n))) : ℕ :=
  ∑ j ∈ Finset.range (g - 3),
    (Finset.univ.filter (fun f : Fin (j + 3) → Fin n =>
      Function.Injective f ∧ ehgCycleEdges j f ⊆ E)).card

/-- Inner bound for one cycle length. -/
private theorem ehg_inner_short_cycle (n j : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
      ehgWeight p E * (∑ f ∈ (Finset.univ : Finset (Fin (j + 3) → Fin n)),
        (if Function.Injective f ∧ ehgCycleEdges j f ⊆ E then (1 : ℝ) else 0))
    ≤ ((n : ℝ) * p) ^ (j + 3) := by
  have hbound : ∀ f : Fin (j + 3) → Fin n,
      ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
        ehgWeight p E * (if Function.Injective f ∧ ehgCycleEdges j f ⊆ E then (1 : ℝ) else 0)
      ≤ p ^ (j + 3) := by
    intro f
    by_cases hf : Function.Injective f
    · calc ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
            ehgWeight p E * (if Function.Injective f ∧ ehgCycleEdges j f ⊆ E then (1 : ℝ) else 0)
          = ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
            (if ehgCycleEdges j f ⊆ E then ehgWeight p E else 0) :=
            Finset.sum_congr rfl (fun E _ => by simp [hf, mul_ite, mul_one, mul_zero])
        _ = p ^ (ehgCycleEdges j f).card := ehg_weight_sum_superset p _
        _ ≤ p ^ (j + 3) := by simp [ehg_card_cycleEdges j f hf]
    · have hzero : ∀ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
          ehgWeight p E * (if Function.Injective f ∧ ehgCycleEdges j f ⊆ E then (1 : ℝ) else 0)
          = 0 := by
        intro E _
        simp [hf]
      calc ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
              ehgWeight p E * (if Function.Injective f ∧ ehgCycleEdges j f ⊆ E then (1 : ℝ) else 0)
          = 0 := Finset.sum_eq_zero hzero
        _ ≤ p ^ (j + 3) := pow_nonneg hp _
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc ∑ f ∈ (Finset.univ : Finset (Fin (j + 3) → Fin n)),
          ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
            ehgWeight p E * (if Function.Injective f ∧ ehgCycleEdges j f ⊆ E then (1 : ℝ) else 0)
      ≤ ∑ _f ∈ (Finset.univ : Finset (Fin (j + 3) → Fin n)), p ^ (j + 3) :=
        Finset.sum_le_sum (fun f _ => hbound f)
    _ = ((n : ℝ) * p) ^ (j + 3) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : (Finset.univ : Finset (Fin (j + 3) → Fin n)).card = n ^ (j + 3) := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
        rw [hcard, Nat.cast_pow, ← mul_pow]

/-- Expected short-cycle count is bounded by the geometric sum. -/
private theorem ehg_expected_short_cycles_le (n g : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
      ehgWeight p E * (ehgShortCycleCount n g E : ℝ)
    ≤ ∑ j ∈ Finset.range (g - 3), ((n : ℝ) * p) ^ (j + 3) := by
  have hexpand : ∀ E : Finset (Sym2 (Fin n)), (ehgShortCycleCount n g E : ℝ)
      = ∑ j ∈ Finset.range (g - 3), ∑ f ∈ (Finset.univ : Finset (Fin (j + 3) → Fin n)),
          (if Function.Injective f ∧ ehgCycleEdges j f ⊆ E then (1 : ℝ) else 0) := by
    intro E
    unfold ehgShortCycleCount
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro f _
    simp
  calc ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
          ehgWeight p E * (ehgShortCycleCount n g E : ℝ)
      = ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
          ehgWeight p E * (∑ j ∈ Finset.range (g - 3),
            ∑ f ∈ (Finset.univ : Finset (Fin (j + 3) → Fin n)),
              (if Function.Injective f ∧ ehgCycleEdges j f ⊆ E then (1 : ℝ) else 0)) :=
        Finset.sum_congr rfl (fun E _ => by rw [hexpand E])
    _ = ∑ j ∈ Finset.range (g - 3),
          ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
            ehgWeight p E * (∑ f ∈ (Finset.univ : Finset (Fin (j + 3) → Fin n)),
              (if Function.Injective f ∧ ehgCycleEdges j f ⊆ E then (1 : ℝ) else 0)) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
    _ ≤ ∑ j ∈ Finset.range (g - 3), ((n : ℝ) * p) ^ (j + 3) :=
        Finset.sum_le_sum (fun j _ => ehg_inner_short_cycle n j p hp)

/-- Off-diagonal pairs of a vertex set, as a finset of edges. -/
private noncomputable def ehgOffPairs {n : ℕ} (A : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  A.offDiag.image (Function.uncurry Sym2.mk)

/-- Number of t-sets with no edge inside. -/
private noncomputable def ehgIndepCount (n t : ℕ) (E : Finset (Sym2 (Fin n))) : ℕ :=
  ((Finset.powersetCard t Finset.univ).filter (fun A => Disjoint E (ehgOffPairs A))).card

/-- Inner expectation for one t-set. -/
private theorem ehg_inner_indep (n t : ℕ) (p : ℝ) (A : Finset (Fin n))
    (hA : A ∈ Finset.powersetCard t Finset.univ) :
    ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
      ehgWeight p E * (if Disjoint E (ehgOffPairs A) then (1 : ℝ) else 0)
    = (1 - p) ^ (t.choose 2) := by
  have hcard : (ehgOffPairs A).card = t.choose 2 := by
    unfold ehgOffPairs
    rw [Sym2.card_image_offDiag, (Finset.mem_powersetCard.mp hA).2]
  calc ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
          ehgWeight p E * (if Disjoint E (ehgOffPairs A) then (1 : ℝ) else 0)
      = ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
          (if Disjoint E (ehgOffPairs A) then ehgWeight p E else 0) :=
        Finset.sum_congr rfl (fun E _ => by by_cases hD : Disjoint E (ehgOffPairs A) <;> simp [hD])
    _ = (1 - p) ^ (ehgOffPairs A).card := ehg_weight_sum_disjoint p _
    _ = (1 - p) ^ (t.choose 2) := by rw [hcard]

/-- Expected independent-set count. -/
private theorem ehg_expected_indep_sets_eq (n t : ℕ) (p : ℝ) :
    ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
      ehgWeight p E * (ehgIndepCount n t E : ℝ)
    = (n.choose t : ℝ) * (1 - p) ^ (t.choose 2) := by
  have hexpand : ∀ E : Finset (Sym2 (Fin n)), (ehgIndepCount n t E : ℝ)
      = ∑ A ∈ Finset.powersetCard t (Finset.univ : Finset (Fin n)),
          (if Disjoint E (ehgOffPairs A) then (1 : ℝ) else 0) := by
    intro E
    unfold ehgIndepCount
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro A _
    simp
  calc ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
          ehgWeight p E * (ehgIndepCount n t E : ℝ)
      = ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
          ehgWeight p E * (∑ A ∈ Finset.powersetCard t (Finset.univ : Finset (Fin n)),
            (if Disjoint E (ehgOffPairs A) then (1 : ℝ) else 0)) :=
        Finset.sum_congr rfl (fun E _ => by rw [hexpand E])
    _ = ∑ A ∈ Finset.powersetCard t (Finset.univ : Finset (Fin n)),
          ∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
            ehgWeight p E * (if Disjoint E (ehgOffPairs A) then (1 : ℝ) else 0) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
    _ = ∑ _A ∈ Finset.powersetCard t (Finset.univ : Finset (Fin n)), (1 - p) ^ (t.choose 2) :=
        Finset.sum_congr rfl (fun A hA => ehg_inner_indep n t p A hA)
    _ = (n.choose t : ℝ) * (1 - p) ^ (t.choose 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_univ,
          Fintype.card_fin]

/-- Averaging: some edge set has few short cycles and no independent t-set. -/
private theorem ehg_exists_good_edgeset (n g t : ℕ) (hn : 0 < n) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (H : (2 / (n : ℝ)) * (∑ j ∈ Finset.range (g - 3), ((n : ℝ) * p) ^ (j + 3))
      + (n.choose t : ℝ) * (1 - p) ^ (t.choose 2) < 1) :
    ∃ E : Finset (Sym2 (Fin n)), 2 * ehgShortCycleCount n g E < n ∧ ehgIndepCount n t E = 0 := by
  have hXle : (∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
        ehgWeight p E * (ehgShortCycleCount n g E : ℝ))
      ≤ ∑ j ∈ Finset.range (g - 3), ((n : ℝ) * p) ^ (j + 3) :=
    ehg_expected_short_cycles_le n g p hp0
  have hYeq : (∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
        ehgWeight p E * (ehgIndepCount n t E : ℝ))
      = (n.choose t : ℝ) * (1 - p) ^ (t.choose 2) :=
    ehg_expected_indep_sets_eq n t p
  have hW : (∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
      ehgWeight p E) = 1 :=
    ehg_weight_sum_univ p
  have hterm : ∀ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
      ehgWeight p E * (2 * (ehgShortCycleCount n g E : ℝ) / (n : ℝ) + (ehgIndepCount n t E : ℝ))
        = (2 / (n : ℝ)) * (ehgWeight p E * (ehgShortCycleCount n g E : ℝ))
          + ehgWeight p E * (ehgIndepCount n t E : ℝ) := by
    intro E _
    ring
  have hsum : (∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
        ehgWeight p E * (2 * (ehgShortCycleCount n g E : ℝ) / (n : ℝ)
          + (ehgIndepCount n t E : ℝ))) < 1 := by
    have hexpand : (∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
          ehgWeight p E * (2 * (ehgShortCycleCount n g E : ℝ) / (n : ℝ)
            + (ehgIndepCount n t E : ℝ)))
        = (2 / (n : ℝ)) * (∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
            ehgWeight p E * (ehgShortCycleCount n g E : ℝ))
          + (∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
            ehgWeight p E * (ehgIndepCount n t E : ℝ)) := by
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hexpand, hYeq]
    have hnn : (0 : ℝ) ≤ 2 / (n : ℝ) := by
      apply div_nonneg (by norm_num) (Nat.cast_nonneg _)
    exact lt_of_le_of_lt (add_le_add_left (mul_le_mul_of_nonneg_left hXle hnn) _) H
  have hlt : (∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
        ehgWeight p E * (2 * (ehgShortCycleCount n g E : ℝ) / (n : ℝ)
          + (ehgIndepCount n t E : ℝ)))
      < (∑ E ∈ (Finset.univ.powerset : Finset (Finset (Sym2 (Fin n)))),
        ehgWeight p E) := by
    rw [hW]
    exact hsum
  obtain ⟨E, _, hElt⟩ := Finset.exists_lt_of_sum_lt hlt
  have hwt0 : 0 ≤ ehgWeight p E := ehg_weight_nonneg p hp0 hp1 E
  have hwtpos : 0 < ehgWeight p E := by
    rcases eq_or_lt_of_le hwt0 with h | h
    · exfalso
      rw [← h, zero_mul] at hElt
      simp at hElt
    · exact h
  have hZ : 2 * (ehgShortCycleCount n g E : ℝ) / (n : ℝ) + (ehgIndepCount n t E : ℝ) < 1 := by
    by_contra hcon
    push Not at hcon
    have hle : ehgWeight p E * 1
        ≤ ehgWeight p E * (2 * (ehgShortCycleCount n g E : ℝ) / (n : ℝ)
          + (ehgIndepCount n t E : ℝ)) :=
      mul_le_mul_of_nonneg_left hcon hwt0
    rw [mul_one] at hle
    exact absurd hElt (not_lt_of_ge hle)
  have hXnn : (0 : ℝ) ≤ 2 * (ehgShortCycleCount n g E : ℝ) / (n : ℝ) := by positivity
  have hYnn : (0 : ℝ) ≤ (ehgIndepCount n t E : ℝ) := Nat.cast_nonneg _
  have hYlt : (ehgIndepCount n t E : ℝ) < 1 := by linarith
  have hXlt : 2 * (ehgShortCycleCount n g E : ℝ) / (n : ℝ) < 1 := by linarith
  have hY0 : ehgIndepCount n t E = 0 := by
    have h1 : (ehgIndepCount n t E : ℝ) < ((1 : ℕ) : ℝ) := by exact_mod_cast hYlt
    exact Nat.lt_one_iff.mp (Nat.cast_lt.mp h1)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2X : 2 * (ehgShortCycleCount n g E : ℝ) < (n : ℝ) := by
    have := (div_lt_one hnpos).mp hXlt
    linarith
  have h2Xn : 2 * ehgShortCycleCount n g E < n := by exact_mod_cast h2X
  exact ⟨E, h2Xn, hY0⟩

/-- Geometric tail: short-cycle powers sum to less than a quarter of `m^g`. -/
private theorem ehg_short_cycle_numeric (m g : ℕ) (hm : 4 * g < m) :
    ∑ j ∈ Finset.range (g - 3), (m : ℝ) ^ (j + 3) < (m : ℝ) ^ g / 4 := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : 1 ≤ m := by omega
    exact_mod_cast this
  have hposm : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  by_cases hg : g ≤ 3
  · have hgr : g - 3 = 0 := by omega
    rw [hgr]
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  · push Not at hg
    have hexp : ∀ j ∈ Finset.range (g - 3), (m : ℝ) ^ (j + 3) ≤ (m : ℝ) ^ (g - 1) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hj3 : j + 3 ≤ g - 1 := by omega
      exact pow_le_pow_right₀ hm1 hj3
    have hsum : ∑ j ∈ Finset.range (g - 3), (m : ℝ) ^ (j + 3)
        ≤ (((g - 3 : ℕ)) : ℝ) * (m : ℝ) ^ (g - 1) := by
      have h := Finset.sum_le_card_nsmul (Finset.range (g - 3))
        (fun j => (m : ℝ) ^ (j + 3)) ((m : ℝ) ^ (g - 1)) hexp
      rw [Finset.card_range, nsmul_eq_mul] at h
      exact h
    have h4 : (((4 * (g - 3) : ℕ)) : ℝ) < (m : ℝ) := by
      have : 4 * (g - 3) < m := by omega
      exact_mod_cast this
    have h4A : 4 * ((((g - 3) : ℕ)) : ℝ) < (m : ℝ) := by
      push_cast at h4 ⊢
      linarith [h4]
    have hpos : (0 : ℝ) < (m : ℝ) ^ (g - 1) := by positivity
    have hg1 : g = (g - 1) + 1 := by omega
    have hfin : ((((g - 3) : ℕ)) : ℝ) * (m : ℝ) ^ (g - 1) < (m : ℝ) ^ g / 4 := by
      have h1 : 4 * (((((g - 3) : ℕ)) : ℝ) * (m : ℝ) ^ (g - 1)) < (m : ℝ) * (m : ℝ) ^ (g - 1) := by
        have e : 4 * (((((g - 3) : ℕ)) : ℝ) * (m : ℝ) ^ (g - 1))
            = (4 * ((((g - 3) : ℕ)) : ℝ)) * (m : ℝ) ^ (g - 1) := by ring
        rw [e]
        exact mul_lt_mul_of_pos_right h4A hpos
      conv_rhs => rw [hg1, pow_succ]
      linarith
    exact lt_of_le_of_lt hsum hfin

/-- Explicit exp-beats-polynomial bound. -/
private theorem ehg_exp_dominates_poly (k' g r : ℕ) (_hk : 1 ≤ k') (hr : 2 ≤ r)
    (hrbig : 2 * 4 ^ (g + 1) * (Nat.factorial (g + 1)) * (2 * k') ^ g ≤ r) :
    2 * ((((2 * k' * r : ℕ))) : ℝ) ^ g ≤ Real.exp (((r : ℝ) - 1) / 2) := by
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hx : (r : ℝ) / 4 ≤ (((r : ℝ) - 1) / 2) := by linarith
  have hx0 : (0 : ℝ) ≤ (((r : ℝ) - 1) / 2) := by linarith
  have h1 := Real.pow_div_factorial_le_exp (((r : ℝ) - 1) / 2) hx0 (g + 1)
  have h2 : ((r : ℝ) / 4) ^ (g + 1) ≤ ((((r : ℝ) - 1) / 2)) ^ (g + 1) :=
    pow_le_pow_left₀ (by positivity) hx _
  have hF : (0 : ℝ) < (((((Nat.factorial (g + 1))) : ℕ)) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have h3a : ((r : ℝ) / 4) ^ (g + 1) / (((((Nat.factorial (g + 1))) : ℕ)) : ℝ)
      ≤ ((((r : ℝ) - 1) / 2)) ^ (g + 1) / (((((Nat.factorial (g + 1))) : ℕ)) : ℝ) := by
    gcongr
  have h3 : ((r : ℝ) / 4) ^ (g + 1) / (((((Nat.factorial (g + 1))) : ℕ)) : ℝ)
      ≤ Real.exp (((r : ℝ) - 1) / 2) :=
    le_trans h3a h1
  have hbigR : (2 : ℝ) * (4 : ℝ) ^ (g + 1) * (((((Nat.factorial (g + 1))) : ℕ)) : ℝ)
      * (2 * (k' : ℝ)) ^ g ≤ (r : ℝ) := by
    exact_mod_cast hrbig
  have hB : (0 : ℝ) ≤ (r : ℝ) ^ g := by positivity
  have hC : (0 : ℝ) < (4 : ℝ) ^ (g + 1) := by positivity
  have hCF : (0 : ℝ) < (4 : ℝ) ^ (g + 1) * (((((Nat.factorial (g + 1))) : ℕ)) : ℝ) := mul_pos hC hF
  have hdiv : 2 * (2 * (k' : ℝ)) ^ g
      ≤ (r : ℝ) / ((4 : ℝ) ^ (g + 1) * (((((Nat.factorial (g + 1))) : ℕ)) : ℝ)) :=
    (le_div_iff₀ hCF).mpr (by linear_combination hbigR)
  have hmul : (2 * (2 * (k' : ℝ)) ^ g) * (r : ℝ) ^ g
      ≤ ((r : ℝ) / ((4 : ℝ) ^ (g + 1) * (((((Nat.factorial (g + 1))) : ℕ)) : ℝ))) * (r : ℝ) ^ g :=
    mul_le_mul_of_nonneg_right hdiv hB
  have ecast : ((((2 * k' * r : ℕ))) : ℝ) = 2 * (k' : ℝ) * (r : ℝ) := by push_cast; ring
  have eR : ((r : ℝ) / ((4 : ℝ) ^ (g + 1) * (((((Nat.factorial (g + 1))) : ℕ)) : ℝ))) * (r : ℝ) ^ g
      = ((r : ℝ) / 4) ^ (g + 1) / (((((Nat.factorial (g + 1))) : ℕ)) : ℝ) := by
    rw [div_pow, div_div]
    nth_rewrite 1 [pow_succ]
    rw [div_mul_eq_mul_div]
    ring
  calc 2 * ((((2 * k' * r : ℕ))) : ℝ) ^ g
      = (2 * (2 * (k' : ℝ)) ^ g) * (r : ℝ) ^ g := by rw [ecast, mul_pow]; ring
    _ ≤ ((r : ℝ) / 4) ^ (g + 1) / (((((Nat.factorial (g + 1))) : ℕ)) :
        ℝ) := by rw [← eR]; exact hmul
    _ ≤ Real.exp (((r : ℝ) - 1) / 2) := h3

/-- Independent-set tail bound for the concrete parameters. -/
private theorem ehg_indep_tail_numeric (k' g r m q n t : ℕ) (p : ℝ)
    (hk : 1 ≤ k') (_hg : 1 ≤ g) (hr : 2 ≤ r)
    (hm : m = 2 * k' * r) (hq : q = m ^ (g - 1)) (hn : n = m ^ g) (ht : t = r * q)
    (hp : p = 1 / (q : ℝ))
    (hexp : 2 * ((((2 * k' * r : ℕ))) : ℝ) ^ g ≤ Real.exp (((r : ℝ) - 1) / 2)) :
    (n.choose t : ℝ) * (1 - p) ^ (t.choose 2) ≤ 1 / 2 := by
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hm2 : 2 ≤ m := by
    have h2 : 2 ≤ 2 * k' * r := by
      have h1 : (2 : ℕ) * 1 ≤ 2 * k' := Nat.mul_le_mul (le_refl _) hk
      have h3 : (2 : ℕ) * 1 * 1 ≤ 2 * k' * r := Nat.mul_le_mul h1 (by omega)
      simpa using h3
    omega
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hq1 : 1 ≤ q := by
    rw [hq]
    exact Nat.one_le_pow _ _ (by omega)
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have ht2 : 2 ≤ t := by
    have h2 : 2 ≤ r * q := by
      have h3 : (2 : ℕ) * 1 ≤ r * q := Nat.mul_le_mul hr hq1
      simpa using h3
    omega
  have hp0 : 0 ≤ p := by
    rw [hp]
    positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one hqpos]
    exact hqR
  have h1pm : 0 ≤ 1 - p := by linarith
  -- Step 1: C(n,t) ≤ n^t
  have step1 : ((n.choose t : ℕ) : ℝ) ≤ (n : ℝ) ^ t := by
    exact_mod_cast Nat.choose_le_pow n t
  -- Step 2: (1-p)^C(t,2) ≤ exp(C(t,2) * (-p))
  have step2 : (1 - p) ^ (t.choose 2) ≤ Real.exp (((t.choose 2 : ℕ) : ℝ) * (-p)) := by
    have h := pow_le_pow_left₀ h1pm (Real.one_sub_le_exp_neg p) (t.choose 2)
    rwa [← Real.exp_nat_mul] at h
  -- Step 3: C(t,2) cast and p * C(t,2) ≥ t * (r-1) / 2
  have hC2 : (((t.choose 2 : ℕ)) : ℝ) = (t : ℝ) * ((t : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ t
  have htR : (t : ℝ) = (r : ℝ) * (q : ℝ) := by rw [ht]; push_cast; ring
  have step3 : (t : ℝ) * (((r : ℝ) - 1) / 2) ≤ p * (((t.choose 2 : ℕ)) : ℝ) := by
    rw [hC2, hp]
    have hqq : (1 : ℝ) / (q : ℝ) ≤ 1 := by
      rw [div_le_one hqpos]
      exact hqR
    have key : (t : ℝ) * (((r : ℝ) - 1) / 2) ≤ (t : ℝ) * (((t : ℝ) - 1) / (2 * (q : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ (t : ℝ))
      rw [le_div_iff₀ (show (0 : ℝ) < 2 * (q : ℝ) by positivity),
        div_mul_eq_mul_div, div_le_iff₀ (show (0 : ℝ) < 2 by norm_num)]
      -- (r-1) * (2*q) ≤ (t-1) * 2
      rw [htR]
      nlinarith [hqR, hrR]
    have eeq : (1 / (q : ℝ)) * ((t : ℝ) * ((t : ℝ) - 1) / 2)
        = (t : ℝ) * (((t : ℝ) - 1) / (2 * (q : ℝ))) := by
      field_simp
    rw [eeq]
    exact key
  -- Step 4: combine into (n * exp(-(r-1)/2))^t
  have hB : (0 : ℝ) ≤ (n : ℝ) ^ t := by positivity
  have step4 : (n : ℝ) ^ t * Real.exp (((t.choose 2 : ℕ) : ℝ) * (-p))
      ≤ ((n : ℝ) * Real.exp (-(((r : ℝ) - 1) / 2))) ^ t := by
    have hexp_le : Real.exp (((t.choose 2 : ℕ) : ℝ) * (-p))
        ≤ Real.exp (-((t : ℝ) * (((r : ℝ) - 1) / 2))) := by
      apply Real.exp_le_exp.mpr
      linarith [step3]
    have eExp : Real.exp (-((t : ℝ) * (((r : ℝ) - 1) / 2)))
        = (Real.exp (-(((r : ℝ) - 1) / 2))) ^ t := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc (n : ℝ) ^ t * Real.exp (((t.choose 2 : ℕ) : ℝ) * (-p))
        ≤ (n : ℝ) ^ t * Real.exp (-((t : ℝ) * (((r : ℝ) - 1) / 2))) :=
          mul_le_mul_of_nonneg_left hexp_le hB
      _ = ((n : ℝ) * Real.exp (-(((r : ℝ) - 1) / 2))) ^ t := by
          rw [mul_pow, eExp]
  -- Step 5: base ≤ 1/2
  have hnR : (n : ℝ) = ((((2 * k' * r : ℕ))) : ℝ) ^ g := by
    rw [hn, hm]
    push_cast
    ring
  have step5 : (n : ℝ) * Real.exp (-(((r : ℝ) - 1) / 2)) ≤ 1 / 2 := by
    have hexp_pos := Real.exp_pos (((r : ℝ) - 1) / 2)
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hexp_pos]
    rw [hnR]
    rw [← hnR] at hexp
    linarith
  -- Step 6: assemble
  have hbase_nn : (0 : ℝ) ≤ (n : ℝ) * Real.exp (-(((r : ℝ) - 1) / 2)) := by positivity
  calc (n.choose t : ℝ) * (1 - p) ^ (t.choose 2)
      ≤ (n : ℝ) ^ t * (1 - p) ^ (t.choose 2) :=
        mul_le_mul_of_nonneg_right step1 (pow_nonneg h1pm _)
    _ ≤ (n : ℝ) ^ t * Real.exp (((t.choose 2 : ℕ) : ℝ) * (-p)) :=
        mul_le_mul_of_nonneg_left step2 hB
    _ ≤ ((n : ℝ) * Real.exp (-(((r : ℝ) - 1) / 2))) ^ t := step4
    _ ≤ (1 / 2) ^ t := pow_le_pow_left₀ hbase_nn step5 t
    _ ≤ 1 / 2 := by
        have ht1 : 1 ≤ t := by omega
        have h :=
          pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (by norm_num : (1 : ℝ) / 2 ≤ 1) ht1
        simpa using h

/-- The concrete parameters satisfy the averaging hypothesis. -/
private theorem ehg_parameters (k' g : ℕ) (hk : 1 ≤ k') (hg : 3 ≤ g) :
    ∃ n t : ℕ, ∃ p : ℝ, 0 < n ∧ 1 ≤ t ∧ n = 2 * k' * t ∧ 0 ≤ p ∧ p ≤ 1 ∧
      (2 / (n : ℝ)) * (∑ j ∈ Finset.range (g - 3), (((n : ℝ)) * p) ^ (j + 3))
        + (n.choose t : ℝ) * (1 - p) ^ (t.choose 2) < 1 := by
  set r : ℕ := 2 * 4 ^ (g + 1) * (Nat.factorial (g + 1)) * (2 * k') ^ g + 4 * g + 2 with hr_def
  set m : ℕ := 2 * k' * r with hm_def
  set q : ℕ := m ^ (g - 1) with hq_def
  have hr2 : 2 ≤ r := by rw [hr_def]; omega
  have hm_pos : 0 < m := by
    have h2 : 2 ≤ 2 * k' * r := by
      have h1 : (2 : ℕ) * 1 ≤ 2 * k' := Nat.mul_le_mul (le_refl _) hk
      have h3 : (2 : ℕ) * 1 * 1 ≤ 2 * k' * r := Nat.mul_le_mul h1 (by omega)
      simpa using h3
    omega
  have hq1 : 1 ≤ q := by
    rw [hq_def]
    exact Nat.one_le_pow _ _ hm_pos
  have hqposR : (0 : ℝ) < ((q : ℕ) : ℝ) := by
    have hq0 : 0 < q := by omega
    exact_mod_cast hq0
  refine ⟨m ^ g, r * q, 1 / ((q : ℝ)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pow_pos hm_pos g
  · have h3 : (2 : ℕ) * 1 ≤ r * q := Nat.mul_le_mul hr2 hq1
    have h2 : 2 ≤ r * q := by simpa using h3
    omega
  · have hgm : g = (g - 1) + 1 := by omega
    have hnm : m ^ g = m * q := by
      rw [hgm, pow_succ, hq_def, mul_comm]
    rw [hnm, hm_def]
    ring
  · rw [div_nonneg_iff]
    left
    exact ⟨by norm_num, Nat.cast_nonneg _⟩
  · rw [div_le_one hqposR]
    exact_mod_cast hq1
  · have hrbig : 2 * 4 ^ (g + 1) * (Nat.factorial (g + 1)) * (2 * k') ^ g ≤ r := by
      rw [hr_def]; omega
    have hexp := ehg_exp_dominates_poly k' g r hk hr2 hrbig
    have hqR0 : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have hnR0 : (0 : ℝ) < ((((m ^ g : ℕ))) : ℝ) :=
      by exact_mod_cast pow_pos (show 0 < m by omega) g
    have hnp : ((((m ^ g : ℕ))) : ℝ) * (1 / ((q : ℝ))) = ((m : ℕ) : ℝ) := by
      have hgm : g = (g - 1) + 1 := by omega
      have hnm : m ^ g = m * q := by
        rw [hgm, pow_succ, hq_def, mul_comm]
      rw [hnm]
      push_cast
      field_simp
    have hmr : r ≤ m := by
      rw [hm_def]
      nlinarith [hk, hr2]
    have h4m : 4 * g < m := by omega
    have hN6 := ehg_short_cycle_numeric m g h4m
    have h2n : (0 : ℝ) ≤ 2 / ((((m ^ g : ℕ))) : ℝ) := by
      apply div_nonneg (by norm_num)
      exact le_of_lt hnR0
    have heq : (2 / ((((m ^ g : ℕ))) : ℝ)) * ((((m : ℕ)) : ℝ) ^ g / 4) = 1 / 2 := by
      rw [← Nat.cast_pow]
      field_simp
      ring
    have hsum_eq : (∑ j ∈ Finset.range (g - 3),
          (((((m ^ g : ℕ))) : ℝ) * (1 / ((q : ℝ)))) ^ (j + 3))
        = ∑ j ∈ Finset.range (g - 3), (((m : ℕ)) : ℝ) ^ (j + 3) :=
      Finset.sum_congr rfl (fun j _ => by rw [hnp])
    have hfirst : (2 / ((((m ^ g : ℕ))) : ℝ))
        * (∑ j ∈ Finset.range (g - 3), (((m : ℕ)) : ℝ) ^ (j + 3))
        < 1 / 2 := by
      have hlt : (2 / ((((m ^ g : ℕ))) : ℝ))
          * (∑ j ∈ Finset.range (g - 3), (((m : ℕ)) : ℝ) ^ (j + 3))
          < (2 / ((((m ^ g : ℕ))) : ℝ)) * ((((m : ℕ)) : ℝ) ^ g / 4) :=
        mul_lt_mul_of_pos_left hN6 (by positivity)
      rwa [heq] at hlt
    have htail : (((m ^ g).choose (r * q) : ℕ) : ℝ)
        * (1 - 1 / ((q : ℝ))) ^ ((r * q).choose 2) ≤ 1 / 2 :=
      ehg_indep_tail_numeric k' g r m q (m ^ g) (r * q) (1 / ((q : ℝ)))
        hk (by omega) hr2 rfl rfl rfl rfl rfl hexp
    rw [hsum_eq]
    linarith [hfirst, htail, hsum_eq]

/-- A walk cycle yields an injective cyclic tuple. -/
private theorem ehg_cycle_to_injective_tuple {V : Type*} (G : SimpleGraph V) (u : V)
    (c : G.Walk u u) (hc : c.IsCycle) (j : ℕ) (hj : c.length = j + 3) :
    ∃ f : Fin (j + 3) → V, Function.Injective f ∧ ∀ i, G.Adj (f i) (f (i + 1)) := by
  have key : ∀ x y : ℕ, x < j + 3 → y < j + 3 → c.getVert x = c.getVert y → x = y := by
    intro x y hx hy hxy
    have hxL : x ≤ c.length := by rw [hj]; omega
    have hyL : y ≤ c.length := by rw [hj]; omega
    have hLL : c.length ∈ {i | 1 ≤ i ∧ i ≤ c.length} := ⟨by rw [hj]; omega, le_refl _⟩
    by_cases hx0 : x = 0
    · subst hx0
      by_cases hy0 : y = 0
      · subst hy0; rfl
      · exfalso
        have hy1 : 1 ≤ y := by omega
        have h1 : c.getVert y = c.getVert c.length := by
          have hz : c.getVert 0 = u := SimpleGraph.Walk.getVert_zero c
          have hl : c.getVert c.length = u := SimpleGraph.Walk.getVert_length c
          rw [hz] at hxy
          exact hxy.symm.trans hl.symm
        have h2 := hc.getVert_injOn ⟨hy1, hyL⟩ hLL h1
        rw [hj] at h2
        omega
    · by_cases hy0 : y = 0
      · subst hy0
        exfalso
        have hx1 : 1 ≤ x := by omega
        have h1 : c.getVert x = c.getVert c.length := by
          have hz : c.getVert 0 = u := SimpleGraph.Walk.getVert_zero c
          have hl : c.getVert c.length = u := SimpleGraph.Walk.getVert_length c
          rw [hz] at hxy
          exact hxy.trans hl.symm
        have h2 := hc.getVert_injOn ⟨hx1, hxL⟩ hLL h1
        rw [hj] at h2
        omega
      · have hx1 : 1 ≤ x := by omega
        have hy1 : 1 ≤ y := by omega
        exact hc.getVert_injOn ⟨hx1, hxL⟩ ⟨hy1, hyL⟩ hxy
  have hinj : Function.Injective (fun i : Fin (j + 3) => c.getVert (i.val)) := by
    intro a b hab
    simp only at hab
    have h := key a.val b.val (Fin.is_lt a) (Fin.is_lt b) hab
    exact Fin.ext h
  refine ⟨fun i : Fin (j + 3) => c.getVert (i.val), hinj, ?_⟩
  intro i
  have hi : i.val < j + 3 := Fin.is_lt i
  have hval : ((i + 1 : Fin (j + 3))).val = (i.val + 1) % (j + 3) := by
    rw [Fin.val_add]
    simp
  by_cases h : i.val + 1 < j + 3
  · have e : ((i + 1 : Fin (j + 3))).val = i.val + 1 := by
      rw [hval, Nat.mod_eq_of_lt h]
    change G.Adj (c.getVert i.val) (c.getVert ((i + 1 : Fin (j + 3))).val)
    rw [e]
    exact SimpleGraph.Walk.adj_getVert_succ c (by rw [hj]; omega)
  · have elast : i.val + 1 = j + 3 := by omega
    have hiv : i.val = j + 2 := by omega
    have e : ((i + 1 : Fin (j + 3))).val = 0 := by
      rw [hval, elast, Nat.mod_self]
    have hadj := SimpleGraph.Walk.adj_getVert_succ c (show j + 2 < c.length by rw [hj]; omega)
    have e1 : c.getVert i.val = c.getVert (j + 2) := by rw [hiv]
    have e2 : c.getVert ((i + 1 : Fin (j + 3))).val = c.getVert (j + 2 + 1) := by
      rw [e]
      have hz := SimpleGraph.Walk.getVert_zero c
      have hL := SimpleGraph.Walk.getVert_length c
      have hjj : j + 2 + 1 = c.length := by rw [hj]
      rw [hjj]
      exact hz.trans hL.symm
    have hgoal : G.Adj (c.getVert i.val) (c.getVert ((i + 1 : Fin (j + 3))).val) := by
      rw [e1, e2]
      exact hadj
    exact hgoal

/-- Vertices deleted to kill all short cycles. -/
private noncomputable def ehgDeleted (n g : ℕ) (E : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  Finset.biUnion (Finset.range (g - 3)) (fun j =>
    (Finset.univ.filter (fun f : Fin (j + 3) → Fin n =>
      Function.Injective f ∧ ehgCycleEdges j f ⊆ E)).image (fun f => f 0))

/-- Deleted vertices are few. -/
private theorem ehg_deleted_card (n g : ℕ) (E : Finset (Sym2 (Fin n))) :
    (ehgDeleted n g E).card ≤ ehgShortCycleCount n g E := by
  unfold ehgDeleted ehgShortCycleCount
  calc (Finset.biUnion (Finset.range (g - 3)) (fun j =>
          (Finset.univ.filter (fun f : Fin (j + 3) → Fin n =>
            Function.Injective f ∧ ehgCycleEdges j f ⊆ E)).image (fun f => f 0))).card
      ≤ ∑ j ∈ Finset.range (g - 3),
          ((Finset.univ.filter (fun f : Fin (j + 3) → Fin n =>
            Function.Injective f ∧ ehgCycleEdges j f ⊆ E)).image (fun f => f 0)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ j ∈ Finset.range (g - 3),
          (Finset.univ.filter (fun f : Fin (j + 3) → Fin n =>
            Function.Injective f ∧ ehgCycleEdges j f ⊆ E)).card :=
        Finset.sum_le_sum (fun j _ => Finset.card_image_le)

/-- Every cycle surviving deletion has length at least `g`. -/
private theorem ehg_deletion_girth (n g : ℕ) (E : Finset (Sym2 (Fin n)))
    (a : {v : Fin n // v ∉ ehgDeleted n g E})
    (w : (SimpleGraph.comap Subtype.val
      (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n))))).Walk a a)
    (hw : w.IsCycle) : g ≤ w.length := by
  by_contra hlt
  push Not at hlt
  have hL3 : 3 ≤ w.length :=
    SimpleGraph.Walk.IsCircuit.three_le_length (SimpleGraph.Walk.IsCycle.isCircuit hw)
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hL3
  have hj3 : w.length = j + 3 := by omega
  have hjmem : j ∈ Finset.range (g - 3) := by
    rw [Finset.mem_range]
    omega
  obtain ⟨f', hfinj', hadj'⟩ := ehg_cycle_to_injective_tuple _ _ w hw j hj3
  have hsub : ∀ i : Fin (j + 3), s(((Subtype.val ∘ f') i), ((Subtype.val ∘ f') (i + 1))) ∈ E := by
    intro i
    have hG := hadj' i
    rw [SimpleGraph.comap_adj] at hG
    rw [SimpleGraph.fromEdgeSet_adj] at hG
    exact Finset.mem_coe.mp hG.1
  have hfinj : Function.Injective (Subtype.val ∘ f') :=
    Subtype.val_injective.comp hfinj'
  have hsub' : ehgCycleEdges j (Subtype.val ∘ f') ⊆ E := by
    unfold ehgCycleEdges
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨i, _, rfl⟩ := he
    exact hsub i
  have hf0 : (Subtype.val ∘ f') 0 ∈ ehgDeleted n g E := by
    unfold ehgDeleted
    rw [Finset.mem_biUnion]
    refine ⟨j, hjmem, ?_⟩
    rw [Finset.mem_image]
    refine ⟨Subtype.val ∘ f', ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hfinj, hsub'⟩
  exact (f' 0).property hf0

/-- No independent t-set plus pigeonhole gives non-colorability. -/
private theorem ehg_not_colorable_of_no_indep (W : Type*) [Fintype W] (G : SimpleGraph W) (c t : ℕ)
    (h : ∀ s : Finset W, s.card = t → ∃ x ∈ s, ∃ y ∈ s, G.Adj x y)
    (hc : c * (t - 1) < Fintype.card W) : ¬ G.Colorable c := by
  rintro ⟨C⟩
  by_cases ht : t = 0
  · subst ht
    obtain ⟨x, hx, _, _, _⟩ := h ∅ (by simp)
    exact Finset.notMem_empty x hx
  · have hmaps : ∀ a ∈ (Finset.univ : Finset W), C a ∈ (Finset.univ : Finset (Fin c)) :=
      fun a _ => Finset.mem_univ _
    have hcard : (Finset.univ : Finset (Fin c)).card * (t - 1)
        < (Finset.univ : Finset W).card := by
      rw [Finset.card_univ, Finset.card_univ, Fintype.card_fin]
      exact hc
    obtain ⟨y, _, hyfib⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hcard
    have hle : t ≤ ({x ∈ (Finset.univ : Finset W) | C x = y}).card := by omega
    obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq hle
    obtain ⟨x, hxs, y', hy's, hadj⟩ := h s hs_card
    have hx_eq : C x = y := (Finset.mem_filter.mp (hs_sub hxs)).2
    have hy_eq : C y' = y := (Finset.mem_filter.mp (hs_sub hy's)).2
    exact C.valid hadj (hx_eq.trans hy_eq.symm)

section
namespace MathlibExt.Combinatorics.SimpleGraph.ErdosGirthChromaticWanted

/-!
# Erdős high-girth high-chromatic

Probabilistic existence of finite graphs with arbitrarily large girth and
chromatic number.
-/

/--
**Erdős's theorem on graphs of high girth and high chromatic number.** For all natural numbers
$k$ and $g$ with $g \ge 3$, there is a finite simple graph $G$ that has a cycle, whose girth
(the length of a shortest cycle) is at least $g$, and whose chromatic number is at least $k$.

In particular, there are finite graphs of arbitrarily high girth and chromatic number.

Source: P. Erdős, Graph theory and probability, Canad. J. Math. 11 (1959), 34–38, DOI
10.4153/CJM-1959-003-9.

Proves `Wanted` entry `erdos_high_girth_chromatic`.
-/
theorem erdos_high_girth_chromatic (k g : ℕ) (hg : 3 ≤ g) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      g ≤ G.girth ∧ (k : ℕ∞) ≤ G.chromaticNumber := by
  set k' := k.max 3 with hk'def
  have hk'1 : 1 ≤ k' := by rw [hk'def]; exact le_trans (by norm_num) (le_max_right _ _)
  have hk'3 : 3 ≤ k' := by rw [hk'def]; exact le_max_right _ _
  have kle : k ≤ k' := by rw [hk'def]; exact le_max_left _ _
  obtain ⟨n, t, p, hn0, ht1, hnt, hp0, hp1, hH⟩ := ehg_parameters k' g hk'1 hg
  obtain ⟨E, h2X, hY0⟩ := ehg_exists_good_edgeset n g t hn0 p hp0 hp1 hH
  have hDle : (ehgDeleted n g E).card ≤ ehgShortCycleCount n g E :=
    ehg_deleted_card n g E
  have hVcard : Fintype.card {v : Fin n // v ∉ ehgDeleted n g E}
      = n - (ehgDeleted n g E).card := by
    have e : ({v : Fin n // v ∉ ehgDeleted n g E}) ≃ ↥((ehgDeleted n g E)ᶜ) :=
      Equiv.subtypeEquivRight (fun v => (Finset.mem_compl).symm)
    rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  have hnoindep : ∀ s : Finset {v : Fin n // v ∉ ehgDeleted n g E}, s.card = t →
      ∃ x ∈ s, ∃ y ∈ s, (SimpleGraph.comap
        (Subtype.val : {v : Fin n // v ∉ ehgDeleted n g E} → Fin n)
        (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n))))).Adj x y := by
    intro s hs
    by_contra hcon
    push Not at hcon
    have hAcard : (s.map (Function.Embedding.subtype
        (fun v => v ∉ ehgDeleted n g E))).card = t := by
      rw [Finset.card_map, hs]
    have hAmem : (s.map (Function.Embedding.subtype
        (fun v => v ∉ ehgDeleted n g E))) ∈ Finset.powersetCard t Finset.univ :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hAcard⟩
    have hdis : Disjoint E (ehgOffPairs (s.map (Function.Embedding.subtype
        (fun v => v ∉ ehgDeleted n g E)))) := by
      rw [Finset.disjoint_left]
      intro e heE heO
      unfold ehgOffPairs at heO
      rw [Finset.mem_image] at heO
      obtain ⟨⟨x', y'⟩, hxy, rfl⟩ := heO
      rw [Finset.mem_offDiag] at hxy
      obtain ⟨hx'A, hy'A, hne⟩ := hxy
      rw [Finset.mem_map] at hx'A hy'A
      obtain ⟨x, hxs, rfl⟩ := hx'A
      obtain ⟨y, hys, rfl⟩ := hy'A
      have hadjE : (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n)))).Adj ↑x ↑y := by
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨Finset.mem_coe.mpr heE, hne⟩
      have hadjG : (SimpleGraph.comap
          (Subtype.val : {v : Fin n // v ∉ ehgDeleted n g E} → Fin n)
          (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n))))).Adj x y :=
        SimpleGraph.comap_adj.mpr hadjE
      exact hcon x hxs y hys hadjG
    have hYmem : (s.map (Function.Embedding.subtype
        (fun v => v ∉ ehgDeleted n g E))) ∈
        ((Finset.powersetCard t Finset.univ).filter
          (fun A => Disjoint E (ehgOffPairs A))) := by
      rw [Finset.mem_filter]
      exact ⟨hAmem, hdis⟩
    have hpos : 0 < ehgIndepCount n t E := by
      unfold ehgIndepCount
      rw [Finset.card_pos]
      exact ⟨_, hYmem⟩
    omega
  obtain ⟨a', ha'⟩ : ∃ a', k' = a' + 1 := ⟨k' - 1, by omega⟩
  obtain ⟨b', hb'⟩ : ∃ b', t = b' + 1 := ⟨t - 1, by omega⟩
  have hQ : (k' - 1) * (t - 1) = a' * b' := by
    rw [ha', hb']
    simp only [Nat.add_sub_cancel]
  have hB : k' * t = (a' + 1) * (b' + 1) := by rw [ha', hb']
  have hexpand : (a' + 1) * (b' + 1) = a' * b' + a' + b' + 1 := by ring
  have hbridge : (2 * k') * t = 2 * (k' * t) := by ring
  have hBle : k' * t ≤ Fintype.card {v : Fin n // v ∉ ehgDeleted n g E} := by omega
  have hcount : (k' - 1) * (t - 1)
      < Fintype.card {v : Fin n // v ∉ ehgDeleted n g E} := by
    rw [hQ]
    omega
  have hNC : ¬ (SimpleGraph.comap
      (Subtype.val : {v : Fin n // v ∉ ehgDeleted n g E} → Fin n)
      (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n))))).Colorable (k' - 1) :=
    ehg_not_colorable_of_no_indep _ _ _ _ hnoindep hcount
  have hchrom : ((k' : ℕ) : ℕ∞) ≤ (SimpleGraph.comap
      (Subtype.val : {v : Fin n // v ∉ ehgDeleted n g E} → Fin n)
      (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n))))).chromaticNumber := by
    rw [SimpleGraph.le_chromaticNumber_iff_colorable]
    intro m hm
    by_contra hltm
    push Not at hltm
    have hcm : (SimpleGraph.comap
        (Subtype.val : {v : Fin n // v ∉ ehgDeleted n g E} → Fin n)
        (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n))))).Colorable (k' - 1) :=
      SimpleGraph.Colorable.mono (by omega : m ≤ k' - 1) hm
    exact hNC hcm
  have hnonac : ¬ (SimpleGraph.comap
      (Subtype.val : {v : Fin n // v ∉ ehgDeleted n g E} → Fin n)
      (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n))))).IsAcyclic := by
    intro hac
    have h2 := hac.chromaticNumber_le_two
    have h3 : ((3 : ℕ) : ℕ∞) ≤ ((2 : ℕ) : ℕ∞) :=
      le_trans (by exact_mod_cast hk'3) (le_trans hchrom h2)
    have h32 : 3 ≤ 2 := by exact_mod_cast h3
    omega
  obtain ⟨a, w, hwc, hgirth⟩ := SimpleGraph.exists_girth_eq_length.mpr hnonac
  have hgirth_le : g ≤ (SimpleGraph.comap
      (Subtype.val : {v : Fin n // v ∉ ehgDeleted n g E} → Fin n)
      (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n))))).girth := by
    have hNb := ehg_deletion_girth n g E a w hwc
    rw [← hgirth] at hNb
    exact hNb
  have hchromK : ((k : ℕ) : ℕ∞) ≤ (SimpleGraph.comap
      (Subtype.val : {v : Fin n // v ∉ ehgDeleted n g E} → Fin n)
      (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n))))).chromaticNumber :=
    le_trans (by exact_mod_cast kle) hchrom
  exact ⟨{v : Fin n // v ∉ ehgDeleted n g E}, inferInstance, inferInstance,
    SimpleGraph.comap (Subtype.val : {v : Fin n // v ∉ ehgDeleted n g E} → Fin n)
      (SimpleGraph.fromEdgeSet (↑E : Set (Sym2 (Fin n)))),
    hgirth_le, hchromK⟩

end MathlibExt.Combinatorics.SimpleGraph.ErdosGirthChromaticWanted
end
