/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OptimalStopping.Secretary
public import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Field

/-!
# Optimality of the threshold rule in the secretary problem

The applicants are interviewed at times `0, …, n - 1` and `σ i` is the quality of the applicant
interviewed at time `i` (larger is better), for a uniformly random permutation `σ` of `Fin n`.
A rule based on relative ranks selects the applicant interviewed at time `s σ`, where the
decision to stop at time `t` may only depend on the relative order of the applicants interviewed
at times `0, …, t`.

`MathlibExt.Probability.Secretary.card_rankRule_wins_div_factorial_le`: **no rule based on
relative ranks selects the best applicant more often than the optimal threshold rule** (Ferguson,
*Optimal Stopping and Applications*, Chapter 2, §2.1). For every such rule, the proportion of
permutations for which it selects the best applicant is at most `winProb n r₁`, the win
probability of the threshold rule `N_{r₁}` computed in
`MathlibExt.Probability.OptimalStopping.SecretaryModel`, where `r₁ = optimalThreshold n` is the
threshold of `MathlibExt.Probability.OptimalStopping.Secretary`.

## Proof outline

The proof combines the linear-programming formulation of Buchbinder, Jain and Singh with a
backward induction in the manner of Lindley's dynamic-programming solution (Ferguson's survey
recounts the solutions of Lindley and Dynkin).

* **Symmetry.** Removing the applicant interviewed last is a bijection between the
  permutations of `Fin (m + 1)` and the pairs made of the quality of that applicant and a
  permutation of `Fin m` with the same relative order on the other times. By induction on the
  number of applicants, if a property depends only on the relative order of the applicants
  interviewed before time `t`, then the applicant interviewed at time `t` is best so far for a
  proportion `1 / (t + 1)` of the permutations with that property; and if it depends only on the
  relative order before time `k`, then the best applicant overall comes before time `k` for a
  proportion `k / n` of them.
* **Reduction.** Let `x t` be the proportion of permutations for which the rule selects at time
  `t` an applicant who is best so far. The rule wins only on these permutations, and on them it
  wins with conditional probability `(t + 1) / n`, so its win probability is
  `∑_t (t + 1) x t / n`. The event of not stopping before time `t` depends only on the relative
  order before time `t`, which gives the constraints `(t + 1) x t + ∑_{t' < t} x t' ≤ 1` of
  Buchbinder, Jain and Singh.
* **Backward induction.** With `V u = P_{max (u + 1) r₁}` for `u < n` and `V n = 0`, the value
  of the problem for an employer who has not selected anyone before time `u`, one checks
  `V (u + 1) ≤ V u` and `(u + 1) / n + u V (u + 1) ≤ (u + 1) V u`, using the monotonicity of
  `P_r` on both sides of `r₁` and the identity `r P_r - (r - 1) P_{r+1} = r / n`. Induction from
  `u = n` down to `u = 0` then shows that `∑_{t ≥ u} (t + 1) x t / n` is at most
  `(1 - ∑_{t < u} x t) V u`, and `V 0 = P_{r₁}`.

## References

* T. S. Ferguson, *Optimal Stopping and Applications*, Chapter 2 (Finite Horizon Problems), §2.1
  (The Classical Secretary Problem), https://www.math.ucla.edu/~tom/Stopping/Contents.html.
* T. S. Ferguson, *Who solved the secretary problem?*, Statistical Science 4 (1989), no. 3,
  282–289.
* D. V. Lindley, *Dynamic programming and decision theory*, Applied Statistics 10 (1961), 39–51.
* E. B. Dynkin, *The optimum choice of the instant for stopping a Markov process*, Soviet
  Mathematics Doklady 4 (1963), 627–629.
* N. Buchbinder, K. Jain and M. Singh, *Secretary problems via linear programming*, Integer
  Programming and Combinatorial Optimization (IPCO 2010), Section 2, Figure 1 and Lemma 1;
  Mathematics of Operations Research 39 (2014), 190–206.
-/

@[expose] public section

open Finset Equiv

namespace MathlibExt.Probability.Secretary

/-! ### Inserting the last applicant -/

section Insert

variable {m : ℕ}

private def insertLastFun (v : Fin (m + 1)) (τ : Perm (Fin m)) : Fin (m + 1) → Fin (m + 1) :=
  Fin.lastCases v fun j => v.succAbove (τ j)

private theorem insertLastFun_injective (v : Fin (m + 1)) (τ : Perm (Fin m)) :
    Function.Injective (insertLastFun v τ) := by
  intro a b h
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rfl
    | cast j => exact absurd h.symm (by simp [insertLastFun])
  | cast i =>
    induction b using Fin.lastCases with
    | last => exact absurd h (by simp [insertLastFun])
    | cast j =>
      simp only [insertLastFun, Fin.lastCases_castSucc] at h
      rw [τ.injective (Fin.succAbove_right_injective h)]

-- The permutation that puts `v` at the last position and orders the other positions as `τ`.
-- It is not Mathlib's `Equiv.Perm.decomposeFin'Symm`, which inserts at position `0` and needs at
-- least two elements: the induction below inserts at the last position, which keeps the relative
-- order of the earlier positions, and needs the case of `Perm (Fin 1)` too.
private noncomputable def insertLast (v : Fin (m + 1)) (τ : Perm (Fin m)) : Perm (Fin (m + 1)) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (insertLastFun_injective v τ))

@[simp] private theorem insertLast_last (v : Fin (m + 1)) (τ : Perm (Fin m)) :
    insertLast v τ (Fin.last m) = v := by
  simp [insertLast, insertLastFun]

@[simp] private theorem insertLast_castSucc (v : Fin (m + 1)) (τ : Perm (Fin m)) (j : Fin m) :
    insertLast v τ j.castSucc = v.succAbove (τ j) := by
  simp [insertLast, insertLastFun]

private theorem insertLast_of_lt (v : Fin (m + 1)) (τ : Perm (Fin m)) (j : Fin (m + 1))
    (h : (j : ℕ) < m) : insertLast v τ j = v.succAbove (τ (j.castLT h)) := by
  conv_lhs => rw [← Fin.castSucc_castLT j h]
  exact insertLast_castSucc v τ _

private theorem insertLast_bijective :
    Function.Bijective (fun p : Fin (m + 1) × Perm (Fin m) => insertLast p.1 p.2) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · rintro ⟨v, τ⟩ ⟨v', τ'⟩ h
    have hv : v = v' := by simpa using DFunLike.congr_fun h (Fin.last m)
    subst hv
    refine Prod.ext rfl (Equiv.ext fun j => ?_)
    have := DFunLike.congr_fun h j.castSucc
    simp only [insertLast_castSucc] at this
    exact Fin.succAbove_right_injective this
  · simp [Fintype.card_perm, Nat.factorial_succ]

-- Counting permutations of `Fin (m + 1)` through the bijection `(v, τ) ↦ insertLast v τ`.
private theorem card_filter_eq_sum (p : Perm (Fin (m + 1)) → Prop) [DecidablePred p] :
    #{σ : Perm (Fin (m + 1)) | p σ} = ∑ v, #{τ : Perm (Fin m) | p (insertLast v τ)} := by
  rw [Finset.card_filter, ← (Equiv.ofBijective _ insertLast_bijective).sum_comp,
    Fintype.sum_prod_type]
  simp only [Equiv.ofBijective_apply, Finset.card_filter]

private theorem forall_lt_iff_castSucc {k : ℕ} (hk : k ≤ m) (Q : Fin (m + 1) → Prop) :
    (∀ j : Fin (m + 1), (j : ℕ) < k → Q j) ↔ ∀ j : Fin m, (j : ℕ) < k → Q j.castSucc := by
  refine ⟨fun h j hj => h _ (by simpa using hj), fun h j hj => ?_⟩
  have := h (j.castLT (by omega)) (by simpa using hj)
  rwa [Fin.castSucc_castLT] at this

end Insert

/-! ### Permutations with the same relative order -/

section SameOrder

variable {n : ℕ}

-- `σ` and `σ'` order the applicants interviewed before time `k` in the same way.
private def SameOrder (k : ℕ) (σ σ' : Perm (Fin n)) : Prop :=
  ∀ j l : Fin n, (j : ℕ) < k → (l : ℕ) < k → (σ j < σ l ↔ σ' j < σ' l)

private theorem SameOrder.refl (k : ℕ) (σ : Perm (Fin n)) : SameOrder k σ σ :=
  fun _ _ _ _ => Iff.rfl

private theorem SameOrder.symm {k : ℕ} {σ σ' : Perm (Fin n)} (h : SameOrder k σ σ') :
    SameOrder k σ' σ :=
  fun j l hj hl => (h j l hj hl).symm

private theorem SameOrder.mono {k k' : ℕ} (hk : k ≤ k') {σ σ' : Perm (Fin n)}
    (h : SameOrder k' σ σ') : SameOrder k σ σ' :=
  fun j l hj hl => h j l (by omega) (by omega)

private theorem sameOrder_insertLast {m k : ℕ} (hk : k ≤ m) {τ τ' : Perm (Fin m)}
    (v v' : Fin (m + 1)) (h : SameOrder k τ τ') :
    SameOrder k (insertLast v τ) (insertLast v' τ') := by
  intro j l hj hl
  rw [insertLast_of_lt v τ j (by omega), insertLast_of_lt v τ l (by omega),
    insertLast_of_lt v' τ' j (by omega), insertLast_of_lt v' τ' l (by omega),
    Fin.succAbove_lt_succAbove_iff, Fin.succAbove_lt_succAbove_iff]
  exact h _ _ (by simpa using hj) (by simpa using hl)

end SameOrder

/-! ### The relative rank of an applicant is independent of the past -/

-- The applicant interviewed last is best so far exactly when it is the best of all.
private theorem record_last_iff {t : ℕ} (σ : Perm (Fin (t + 1))) :
    (∀ j : Fin (t + 1), (j : ℕ) < t → σ j < σ (Fin.last t)) ↔ σ (Fin.last t) = Fin.last t := by
  constructor
  · intro h
    by_contra hne
    set i := σ.symm (Fin.last t)
    have hi : i ≠ Fin.last t := fun h' => hne (by
      have := σ.apply_symm_apply (Fin.last t)
      rwa [show σ.symm (Fin.last t) = Fin.last t from h'] at this)
    have := h i (Fin.val_lt_last hi)
    rw [Equiv.apply_symm_apply] at this
    exact absurd this (not_lt.mpr (Fin.le_last _))
  · intro h j hj
    rw [h, Fin.lt_last_iff_ne_last]
    intro h'
    have : j = Fin.last t := σ.injective (h'.trans h.symm)
    rw [this] at hj
    simp at hj

private theorem card_record_mul_base (t : ℕ) (P : Perm (Fin (t + 1)) → Prop) [DecidablePred P]
    (hP : ∀ σ σ', SameOrder t σ σ' → (P σ ↔ P σ')) :
    #{σ | P σ ∧ ∀ j : Fin (t + 1), (j : ℕ) < t → σ j < σ ⟨t, by omega⟩} * (t + 1) =
      #{σ | P σ} := by
  have h1 : ∀ v (τ : Perm (Fin t)), P (insertLast v τ) ↔ P (insertLast (Fin.last t) τ) :=
    fun v τ => hP _ _ (sameOrder_insertLast le_rfl v _ (SameOrder.refl t τ))
  have h2 : ∀ v (τ : Perm (Fin t)), (∀ j : Fin (t + 1), (j : ℕ) < t →
      insertLast v τ j < insertLast v τ ⟨t, by omega⟩) ↔ v = Fin.last t := by
    intro v τ
    have := record_last_iff (insertLast v τ)
    rw [insertLast_last] at this
    simpa only [show (⟨t, by omega⟩ : Fin (t + 1)) = Fin.last t from rfl, insertLast_last]
  rw [card_filter_eq_sum, card_filter_eq_sum]
  simp only [h1, h2]
  have h3 : ∀ x : Fin (t + 1),
      #{τ : Perm (Fin t) | P (insertLast (Fin.last t) τ) ∧ x = Fin.last t} =
        if x = Fin.last t then #{τ : Perm (Fin t) | P (insertLast (Fin.last t) τ)} else 0 := by
    intro x
    split_ifs with h <;> simp [h]
  simp only [h3, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  ring

private theorem card_record_mul_succ {t m : ℕ} (htm : t < m)
    (ih : ∀ (P : Perm (Fin m) → Prop) [DecidablePred P],
      (∀ σ σ', SameOrder t σ σ' → (P σ ↔ P σ')) →
        #{σ | P σ ∧ ∀ j : Fin m, (j : ℕ) < t → σ j < σ ⟨t, htm⟩} * (t + 1) = #{σ | P σ})
    (P : Perm (Fin (m + 1)) → Prop) [DecidablePred P]
    (hP : ∀ σ σ', SameOrder t σ σ' → (P σ ↔ P σ')) :
    #{σ | P σ ∧ ∀ j : Fin (m + 1), (j : ℕ) < t → σ j < σ ⟨t, by omega⟩} * (t + 1) =
      #{σ | P σ} := by
  have h1 : ∀ v (τ : Perm (Fin m)), P (insertLast v τ) ↔ P (insertLast 0 τ) :=
    fun v τ => hP _ _ (sameOrder_insertLast htm.le v _ (SameOrder.refl t τ))
  have h2 : ∀ v (τ : Perm (Fin m)), (∀ j : Fin (m + 1), (j : ℕ) < t →
      insertLast v τ j < insertLast v τ ⟨t, by omega⟩) ↔
        ∀ j : Fin m, (j : ℕ) < t → τ j < τ ⟨t, htm⟩ := by
    intro v τ
    rw [forall_lt_iff_castSucc htm.le, insertLast_of_lt v τ _ htm]
    simp only [insertLast_castSucc, Fin.succAbove_lt_succAbove_iff]
    rfl
  have hP' : ∀ τ τ' : Perm (Fin m), SameOrder t τ τ' →
      (P (insertLast 0 τ) ↔ P (insertLast 0 τ')) :=
    fun τ τ' h => hP _ _ (sameOrder_insertLast htm.le 0 0 h)
  rw [card_filter_eq_sum, card_filter_eq_sum]
  simp only [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [mul_assoc, ih (fun τ => P (insertLast 0 τ)) hP']

/-- For `t < n` and a property `P` of permutations that depends only on the relative order of the
applicants interviewed before time `t`, the applicant interviewed at time `t` is best so far for
a proportion `1 / (t + 1)` of the permutations satisfying `P`. -/
private theorem card_record_mul (t : ℕ) :
    ∀ {n : ℕ} (ht : t < n) (P : Perm (Fin n) → Prop) [DecidablePred P],
      (∀ σ σ', SameOrder t σ σ' → (P σ ↔ P σ')) →
        #{σ | P σ ∧ ∀ j : Fin n, (j : ℕ) < t → σ j < σ ⟨t, ht⟩} * (t + 1) = #{σ | P σ} := by
  intro n
  induction n with
  | zero => intro ht; exact absurd ht (Nat.not_lt_zero _)
  | succ m ih =>
    intro ht P _ hP
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with htm | htm
    · exact card_record_mul_succ htm (fun P' _ hP' => ih htm P' hP') P hP
    · subst htm
      exact card_record_mul_base t P hP

/-- For `k ≤ m ≤ n` and a property `F` of permutations that depends only on the relative order of
the applicants interviewed before time `k`, the best of the applicants interviewed before time `m`
comes before time `k` for a proportion `k / m` of the permutations satisfying `F`. -/
private theorem card_beaten_mul {n k : ℕ} (F : Perm (Fin n) → Prop) [DecidablePred F]
    (hF : ∀ σ σ', SameOrder k σ σ' → (F σ ↔ F σ')) :
    ∀ m, k ≤ m → m ≤ n →
      #{σ | F σ ∧ ∀ j : Fin n, k ≤ (j : ℕ) → (j : ℕ) < m →
        ∃ i : Fin n, (i : ℕ) < k ∧ σ j < σ i} * m = #{σ | F σ} * k := by
  intro m hkm
  induction m, hkm using Nat.le_induction with
  | base =>
    intro _
    congr 2
    ext σ
    simp only [mem_filter, mem_univ, true_and, and_iff_left_iff_imp]
    intro _ j h1 h2
    omega
  | succ m hkm ih =>
    intro hmn
    have hm : m < n := by omega
    have hG : ∀ σ σ' : Perm (Fin n), SameOrder m σ σ' →
        ((F σ ∧ ∀ j : Fin n, k ≤ (j : ℕ) → (j : ℕ) < m → ∃ i : Fin n, (i : ℕ) < k ∧ σ j < σ i) ↔
          (F σ' ∧ ∀ j : Fin n, k ≤ (j : ℕ) → (j : ℕ) < m →
            ∃ i : Fin n, (i : ℕ) < k ∧ σ' j < σ' i)) := by
      intro σ σ' h
      refine and_congr (hF σ σ' (h.mono hkm)) (forall_congr' fun j => ?_)
      refine imp_congr_right fun hj => imp_congr_right fun hjm => exists_congr fun i => ?_
      refine and_congr_right fun hi => h j i hjm (by omega)
    have hC := card_record_mul m hm _ hG
    have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter
      fun σ : Perm (Fin n) => F σ ∧ ∀ j : Fin n, k ≤ (j : ℕ) → (j : ℕ) < m →
        ∃ i : Fin n, (i : ℕ) < k ∧ σ j < σ i)
      (fun σ => ∀ j : Fin n, (j : ℕ) < m → σ j < σ ⟨m, hm⟩)
    have heq : #{σ : Perm (Fin n) | F σ ∧ ∀ j : Fin n, k ≤ (j : ℕ) → (j : ℕ) < m + 1 →
        ∃ i : Fin n, (i : ℕ) < k ∧ σ j < σ i} =
        #((Finset.univ.filter fun σ : Perm (Fin n) => F σ ∧ ∀ j : Fin n, k ≤ (j : ℕ) →
          (j : ℕ) < m → ∃ i : Fin n, (i : ℕ) < k ∧ σ j < σ i).filter
            fun σ => ¬∀ j : Fin n, (j : ℕ) < m → σ j < σ ⟨m, hm⟩) := by
      congr 1
      ext σ
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨hF', h⟩
        refine ⟨⟨hF', fun j hj hjm => h j hj (by omega)⟩, fun hrec => ?_⟩
        obtain ⟨i, hi, hlt⟩ := h ⟨m, hm⟩ hkm (Nat.lt_succ_self m)
        exact absurd (hrec i (by omega)) (not_lt.mpr hlt.le)
      · rintro ⟨⟨hF', h⟩, hrec⟩
        refine ⟨hF', fun j hj hjm => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjm with hjm | hjm
        · exact h j hj hjm
        · push Not at hrec
          obtain ⟨j', hj', hle⟩ := hrec
          have hj_eq : j = ⟨m, hm⟩ := Fin.ext hjm
          subst hj_eq
          have hlt : σ ⟨m, hm⟩ < σ j' :=
            lt_of_le_of_ne hle fun h' => by
              have := σ.injective h'
              rw [← this] at hj'
              simp at hj'
          by_cases hj'k : (j' : ℕ) < k
          · exact ⟨j', hj'k, hlt⟩
          · obtain ⟨i, hi, hlt'⟩ := h j' (by omega) hj'
            exact ⟨i, hi, hlt.trans hlt'⟩
    rw [heq]
    have hfilt : #((Finset.univ.filter fun σ : Perm (Fin n) => F σ ∧ ∀ j : Fin n, k ≤ (j : ℕ) →
          (j : ℕ) < m → ∃ i : Fin n, (i : ℕ) < k ∧ σ j < σ i).filter
            fun σ => ∀ j : Fin n, (j : ℕ) < m → σ j < σ ⟨m, hm⟩) =
        #{σ : Perm (Fin n) | (F σ ∧ ∀ j : Fin n, k ≤ (j : ℕ) → (j : ℕ) < m →
          ∃ i : Fin n, (i : ℕ) < k ∧ σ j < σ i) ∧
            ∀ j : Fin n, (j : ℕ) < m → σ j < σ ⟨m, hm⟩} := by
      rw [Finset.filter_filter]
    rw [hfilt] at hsplit
    have := ih hm.le
    nlinarith

/-! ### Rules based on relative ranks -/

section Rule

variable {n : ℕ} {s : Perm (Fin n) → Fin n}

private theorem stop_record_congr {t : ℕ} (ht : t < n) (σ : Perm (Fin n)) :
    ((s σ : ℕ) = t ∧ ∀ j, j < s σ → σ j < σ (s σ)) ↔
      ((s σ : ℕ) = t ∧ ∀ j : Fin n, (j : ℕ) < t → σ j < σ ⟨t, ht⟩) := by
  refine and_congr_right fun h1 => ?_
  rw [show s σ = ⟨t, ht⟩ from Fin.ext h1]
  exact forall_congr' fun j => imp_congr_left Fin.lt_def

private theorem stop_win_iff {t : ℕ} (ht : t < n) (σ : Perm (Fin n)) :
    ((s σ : ℕ) = t ∧ ∀ j, σ j ≤ σ (s σ)) ↔
      (((s σ : ℕ) = t ∧ ∀ j : Fin n, (j : ℕ) < t → σ j < σ ⟨t, ht⟩) ∧
        ∀ j : Fin n, t + 1 ≤ (j : ℕ) → (j : ℕ) < n →
          ∃ i : Fin n, (i : ℕ) < t + 1 ∧ σ j < σ i) := by
  rw [and_assoc]
  refine and_congr_right fun h1 => ?_
  rw [show s σ = ⟨t, ht⟩ from Fin.ext h1]
  have hne : ∀ j : Fin n, (j : ℕ) ≠ t → σ j ≠ σ ⟨t, ht⟩ := fun j hj h =>
    hj (congrArg Fin.val (σ.injective h))
  constructor
  · intro h
    refine ⟨fun j hj => lt_of_le_of_ne (h j) (hne j (by omega)),
      fun j hj _ => ⟨⟨t, ht⟩, Nat.lt_succ_self t, lt_of_le_of_ne (h j) (hne j (by omega))⟩⟩
  · rintro ⟨hrec, hbeat⟩ j
    rcases lt_trichotomy (j : ℕ) t with hj | hj | hj
    · exact (hrec j hj).le
    · rw [show j = ⟨t, ht⟩ from Fin.ext hj]
    · obtain ⟨i, hi, hlt⟩ := hbeat j hj j.isLt
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
      · exact (hlt.trans (hrec i hi)).le
      · rw [show i = ⟨t, ht⟩ from Fin.ext hi] at hlt
        exact hlt.le

variable (hs : ∀ σ σ' : Perm (Fin n),
  (∀ j k : Fin n, j ≤ s σ → k ≤ s σ → (σ j < σ k ↔ σ' j < σ' k)) → s σ' = s σ)
include hs

private theorem eq_of_sameOrder {t : ℕ} {σ σ' : Perm (Fin n)} (h : SameOrder t σ σ')
    (hσ : (s σ : ℕ) < t) : s σ' = s σ :=
  hs σ σ' fun j k hj hk =>
    h j k (by rw [Fin.le_iff_val_le_val] at hj; omega) (by rw [Fin.le_iff_val_le_val] at hk; omega)

private theorem le_rule_iff {t : ℕ} {σ σ' : Perm (Fin n)} (h : SameOrder t σ σ') :
    t ≤ (s σ : ℕ) ↔ t ≤ (s σ' : ℕ) := by
  constructor
  · intro h1
    by_contra h2
    have := congrArg Fin.val (eq_of_sameOrder hs h.symm (not_le.mp h2))
    omega
  · intro h1
    by_contra h2
    have := congrArg Fin.val (eq_of_sameOrder hs h (not_le.mp h2))
    omega

private theorem stop_record_iff {t : ℕ} (ht : t < n) {σ σ' : Perm (Fin n)}
    (h : SameOrder (t + 1) σ σ') :
    ((s σ : ℕ) = t ∧ ∀ j : Fin n, (j : ℕ) < t → σ j < σ ⟨t, ht⟩) ↔
      ((s σ' : ℕ) = t ∧ ∀ j : Fin n, (j : ℕ) < t → σ' j < σ' ⟨t, ht⟩) := by
  have key : ∀ {σ σ' : Perm (Fin n)}, SameOrder (t + 1) σ σ' → (s σ : ℕ) = t →
      (s σ' : ℕ) = t := fun h h1 => by
    rw [eq_of_sameOrder hs h (by omega)]
    exact h1
  exact and_congr ⟨key h, key h.symm⟩
    (forall_congr' fun j => imp_congr_right fun hj => h j ⟨t, ht⟩ (by omega) (Nat.lt_succ_self t))

private theorem card_win_mul {t : ℕ} (ht : t < n) :
    #{σ | (s σ : ℕ) = t ∧ ∀ j, σ j ≤ σ (s σ)} * n =
      #{σ | (s σ : ℕ) = t ∧ ∀ j, j < s σ → σ j < σ (s σ)} * (t + 1) := by
  have := card_beaten_mul (k := t + 1)
    (fun σ => (s σ : ℕ) = t ∧ ∀ j : Fin n, (j : ℕ) < t → σ j < σ ⟨t, ht⟩)
    (fun σ σ' h => stop_record_iff hs ht h) n (by omega) le_rfl
  rw [Finset.filter_congr (fun σ _ => stop_win_iff ht σ),
    Finset.filter_congr (fun σ _ => stop_record_congr ht σ)]
  exact this

private theorem card_record_add_le {t : ℕ} (ht : t < n) :
    #{σ | (s σ : ℕ) = t ∧ ∀ j, j < s σ → σ j < σ (s σ)} * (t + 1) +
      ∑ t' ∈ range t, #{σ | (s σ : ℕ) = t' ∧ ∀ j, j < s σ → σ j < σ (s σ)} ≤
        n.factorial := by
  have hC := card_record_mul t ht (fun σ => t ≤ (s σ : ℕ)) (fun σ σ' h => le_rule_iff hs h)
  have h1 : #{σ | (s σ : ℕ) = t ∧ ∀ j, j < s σ → σ j < σ (s σ)} ≤
      #{σ | t ≤ (s σ : ℕ) ∧ ∀ j : Fin n, (j : ℕ) < t → σ j < σ ⟨t, ht⟩} := by
    apply Finset.card_le_card
    intro σ
    simp only [mem_filter, mem_univ, true_and]
    intro h
    rw [stop_record_congr ht σ] at h
    exact ⟨h.1.ge, h.2⟩
  have h2 : ∑ t' ∈ range t, #{σ | (s σ : ℕ) = t' ∧ ∀ j, j < s σ → σ j < σ (s σ)} ≤
      #{σ | ¬ t ≤ (s σ : ℕ)} := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun σ => (s σ : ℕ)) (t := range t)
      (fun σ hσ => by simpa using hσ)]
    refine Finset.sum_le_sum fun t' ht' => Finset.card_le_card ?_
    intro σ
    simp only [mem_filter, mem_univ, true_and, mem_range] at ht' ⊢
    rintro ⟨h1, -⟩
    exact ⟨by omega, h1⟩
  have h3 := Finset.card_filter_add_card_filter_not (s := univ)
    (fun σ : Perm (Fin n) => t ≤ (s σ : ℕ))
  rw [card_univ, Fintype.card_perm, Fintype.card_fin] at h3
  have := Nat.mul_le_mul_right (t + 1) h1
  omega

end Rule

/-! ### The optimal threshold rule solves the optimality equation -/

private theorem winProb_self {n : ℕ} : winProb n n = 1 / n := by
  simp [winProb, harmonicTail]

private theorem winProb_identity {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    (i : ℝ) * winProb n i - ((i : ℝ) - 1) * winProb n (i + 1) = i / n := by
  have h := winProb_succ_sub hi hin
  have hn : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact this.ne'
  have hP : winProb n i = (1 + ((i : ℝ) - 1) * harmonicTail n i) / n := rfl
  rw [show winProb n (i + 1) = winProb n i + (harmonicTail n i - 1) / n by linarith, hP]
  field_simp
  ring

-- The value of the problem at time `u` for an employer who has not selected anyone before time `u`.
private noncomputable def tailValue (n u : ℕ) : ℝ :=
  if u < n then winProb n (max (u + 1) (optimalThreshold n)) else 0

private theorem tailValue_succ_le {n u : ℕ} (hu : u < n) :
    tailValue n (u + 1) ≤ tailValue n u ∧
      ((u : ℝ) + 1) / n + u * tailValue n (u + 1) ≤ ((u : ℝ) + 1) * tailValue n u := by
  have hn : 1 ≤ n := by omega
  have hr1 : 1 ≤ optimalThreshold n := one_le_optimalThreshold n
  have hrn : optimalThreshold n ≤ n := optimalThreshold_le hn
  unfold tailValue
  simp only [hu, ↓reduceIte]
  rcases Nat.lt_or_ge (u + 1) n with h | h
  · simp only [h, ↓reduceIte]
    have hid := winProb_identity (n := n) (i := u + 1) (by omega) h
    push_cast at hid
    rcases le_or_gt (optimalThreshold n) (u + 1) with hru | hru
    · rw [max_eq_left hru, max_eq_left (by omega : optimalThreshold n ≤ u + 1 + 1)]
      refine ⟨winProb_succ_le_of_optimalThreshold_le hru h, ?_⟩
      linarith
    · rw [max_eq_right hru.le, max_eq_right (by omega : u + 1 + 1 ≤ optimalThreshold n)]
      refine ⟨le_rfl, ?_⟩
      have h1 := winProb_le_succ_of_lt_optimalThreshold hn (by omega : 1 ≤ u + 1) hru
      have h2 := winProb_le_winProb_optimalThreshold hn (by omega : 1 ≤ u + 1 + 1)
        (by omega : u + 1 + 1 ≤ n)
      have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (u : ℝ) + 1)
      nlinarith
  · have hun : u + 1 = n := by omega
    have hnot : ¬ (u + 1 < n) := by omega
    simp only [hnot, ↓reduceIte]
    rw [max_eq_left (by omega : optimalThreshold n ≤ u + 1), hun, winProb_self]
    have : ((u : ℝ) + 1) = n := by exact_mod_cast hun
    rw [this]
    refine ⟨by positivity, le_of_eq (by ring)⟩

/-- Backward induction for the reduced problem: if `x t ≥ 0` and
`(t + 1) x t + ∑_{t' < t} x t' ≤ 1` for `t < n`, then `∑_{t < n} (t + 1) x t / n ≤ P_{r₁}`. -/
private theorem sum_le_winProb_optimalThreshold {n : ℕ} (hn : 1 ≤ n) (x : ℕ → ℝ)
    (hx0 : ∀ t < n, 0 ≤ x t) (hx : ∀ t < n, ((t : ℝ) + 1) * x t + ∑ t' ∈ range t, x t' ≤ 1) :
    ∑ t ∈ range n, ((t : ℝ) + 1) * x t / n ≤ winProb n (optimalThreshold n) := by
  have key : ∀ d ≤ n, ∑ t ∈ Ico (n - d) n, ((t : ℝ) + 1) * x t / n ≤
      (1 - ∑ t ∈ range (n - d), x t) * tailValue n (n - d) := by
    intro d
    induction d with
    | zero => intro _; simp [tailValue]
    | succ d ih =>
      intro hd
      have hun : n - (d + 1) < n := by omega
      have ih' := ih (by omega)
      rw [show n - d = n - (d + 1) + 1 by omega, Finset.sum_range_succ] at ih'
      rw [Finset.sum_eq_sum_Ico_succ_bot hun]
      obtain ⟨ha, hb⟩ := tailValue_succ_le hun
      have hxu := hx _ hun
      have hx0u := hx0 _ hun
      set u := n - (d + 1)
      set S := ∑ t ∈ range u, x t
      set W1 := tailValue n (u + 1)
      set W0 := tailValue n u
      have hD : 0 ≤ 1 - S := by nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (u : ℝ) + 1) hx0u]
      have hmain : x u * (((u : ℝ) + 1) / n - W1) ≤ (1 - S) * (W0 - W1) := by
        rcases le_or_gt W1 (((u : ℝ) + 1) / n) with hc | hc
        · have hc' : 0 ≤ ((u : ℝ) + 1) / n - W1 := by linarith
          have e1 := mul_le_mul_of_nonneg_right (show ((u : ℝ) + 1) * x u ≤ 1 - S by linarith) hc'
          have e2 := mul_le_mul_of_nonneg_left
            (show ((u : ℝ) + 1) / n - W1 ≤ ((u : ℝ) + 1) * (W0 - W1) by linarith) hD
          have e3 : (x u * (((u : ℝ) + 1) / n - W1)) * ((u : ℝ) + 1) ≤
              ((1 - S) * (W0 - W1)) * ((u : ℝ) + 1) := by nlinarith
          exact le_of_mul_le_mul_right e3 (by positivity)
        · have e1 : x u * (((u : ℝ) + 1) / n - W1) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hx0u (by linarith)
          have e2 : 0 ≤ (1 - S) * (W0 - W1) := mul_nonneg hD (by linarith)
          linarith
      have : ((u : ℝ) + 1) * x u / n = x u * (((u : ℝ) + 1) / n) := by ring
      nlinarith
  have := key n le_rfl
  rw [Nat.sub_self, ← Finset.range_eq_Ico] at this
  simpa [tailValue, Nat.lt_of_lt_of_le zero_lt_one hn,
    max_eq_right (one_le_optimalThreshold n)] using this

/-- **Optimality of the threshold rule among all rank-based rules** (Ferguson, *Optimal Stopping
and Applications*, Chapter 2, §2.1). A rule that must select one of `n ≥ 1` applicants and may
only use the relative ranks seen so far is a map `s` from permutations to selection times such
that `s σ' = s σ` whenever `σ'` and `σ` order the applicants interviewed up to time `s σ` in the
same way. For every such rule, the proportion of permutations for which it selects the best
applicant is at most `winProb n r₁`, the win probability of the optimal threshold rule. Rules
that may decline to select anyone are not covered; selecting the last applicant instead never
lowers the win probability. -/
theorem card_rankRule_wins_div_factorial_le {n : ℕ} (hn : 1 ≤ n)
    (s : Equiv.Perm (Fin n) → Fin n)
    (hs : ∀ σ σ' : Equiv.Perm (Fin n),
      (∀ j k : Fin n, j ≤ s σ → k ≤ s σ → (σ j < σ k ↔ σ' j < σ' k)) → s σ' = s σ) :
    ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) => ∀ j, σ j ≤ σ (s σ)).card : ℝ) /
        n.factorial ≤ winProb n (optimalThreshold n) := by
  have hN : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- `a t` counts the permutations for which the rule selects, at time `t`, a best-so-far applicant
  set a : ℕ → ℕ := fun t =>
    #{σ : Perm (Fin n) | (s σ : ℕ) = t ∧ ∀ j, j < s σ → σ j < σ (s σ)}
  have hwin : #{σ : Perm (Fin n) | ∀ j, σ j ≤ σ (s σ)} =
      ∑ t ∈ range n, #{σ : Perm (Fin n) | (s σ : ℕ) = t ∧ ∀ j, σ j ≤ σ (s σ)} := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun σ => (s σ : ℕ)) (t := range n)
      (fun σ _ => by simp)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.filter_filter]
    simp only [and_comm]
  have hterm : ∀ t ∈ range n,
      (#{σ : Perm (Fin n) | (s σ : ℕ) = t ∧ ∀ j, σ j ≤ σ (s σ)} : ℝ) / n.factorial =
        ((t : ℝ) + 1) * ((a t : ℝ) / n.factorial) / n := by
    intro t ht
    have h' : (#{σ : Perm (Fin n) | (s σ : ℕ) = t ∧ ∀ j, σ j ≤ σ (s σ)} : ℝ) * n =
        (a t : ℝ) * ((t : ℝ) + 1) := by exact_mod_cast card_win_mul hs (mem_range.mp ht)
    field_simp
    linarith
  rw [hwin, Nat.cast_sum, Finset.sum_div, Finset.sum_congr rfl hterm]
  refine sum_le_winProb_optimalThreshold hn (fun t => (a t : ℝ) / n.factorial)
    (fun t _ => by positivity) fun t ht => ?_
  have h' : (a t : ℝ) * ((t : ℝ) + 1) + ∑ t' ∈ range t, (a t' : ℝ) ≤ n.factorial := by
    exact_mod_cast card_record_add_le hs ht
  rw [← Finset.sum_div, mul_div_assoc', ← add_div, div_le_one hN]
  linarith

end MathlibExt.Probability.Secretary
