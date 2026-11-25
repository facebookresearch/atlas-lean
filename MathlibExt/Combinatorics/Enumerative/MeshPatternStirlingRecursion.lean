/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt

/-! # Stirling-type recursion for mesh-pattern counts -/

/-- **Mesh-pattern match.** Let $\sigma$ be a permutation of $m$ elements, with positions numbered
$1, \dots, m$, let $p$ be the position of the largest value of $\sigma$, and let $r$ be a natural
number. A position $i$ is a mesh-pattern match of $\sigma$ with parameter $r$ when
$\sigma(t) < \sigma(i)$ for every position $t < i$ and at least $r - 1$ positions $t$ with
$i < t < p$ have $\sigma(t) > \sigma(i)$. -/
def MatchPred {m : ℕ} (r : ℕ) (σ : Equiv.Perm (Fin m)) (i : Fin m) : Prop :=
  ∃ maxIndex : Fin m,
    (∀ t : Fin m, σ t ≤ σ maxIndex) ∧
    r - 1 ≤ (Finset.univ.filter fun t : Fin m =>
      i < t ∧ t < maxIndex ∧ σ i < σ t).card ∧
    ∀ t : Fin m, t < i → σ t < σ i

/-- **Mesh-pattern zero condition.** Let $\sigma$ be a permutation of $m$ elements, with positions
numbered $1, \dots, m$, and let $r$ be a natural number. The zero condition holds for $\sigma$
with parameter $r$ when some position $p \ge r$ holds the largest value of $\sigma$. -/
def ZeroPred {m : ℕ} (r : ℕ) (σ : Equiv.Perm (Fin m)) : Prop :=
  ∃ maxIndex : Fin m,
    (∀ t : Fin m, σ t ≤ σ maxIndex) ∧ r ≤ maxIndex.val + 1

instance decMatchPred (m : ℕ) (r : ℕ) (σ : Equiv.Perm (Fin m)) :
    DecidablePred (MatchPred r σ) := by
  intro i
  unfold MatchPred
  infer_instance

instance decZeroPred (m : ℕ) (r : ℕ) (σ : Equiv.Perm (Fin m)) :
    Decidable (ZeroPred r σ) := by
  unfold ZeroPred
  infer_instance

/-- **Canonical mesh-pattern statistic.** Let $\sigma$ be a permutation of $m$ elements, with
positions numbered $1, \dots, m$, and let $r$ be a natural number. The statistic $N_r(\sigma)$ is
the number of mesh-pattern matches of $\sigma$ with parameter $r$, plus $1$ if the mesh-pattern
zero condition holds, that is, if the largest value of $\sigma$ sits at a position $p \ge r$. -/
def meshN {m : ℕ} (r : ℕ) (σ : Equiv.Perm (Fin m)) : ℕ :=
  (Finset.univ.filter (MatchPred r σ)).card + if ZeroPred r σ then 1 else 0

/-- **Mesh-pattern counting polynomial.** For natural numbers $m$ and $r$, the polynomial
$P_{m,r}(X) \in \mathbb{N}[X]$ is the sum of $X^{N_r(\sigma)}$ over all permutations $\sigma$ of
$m$ elements, where $N_r(\sigma)$ is the canonical mesh-pattern statistic with parameter $r$. -/
noncomputable def PolyN : ℕ → ℕ → Polynomial ℕ := fun m r =>
  ∑ σ : Equiv.Perm (Fin m), (Polynomial.X : Polynomial ℕ) ^ meshN r σ

/-- Mirror of the `C` let-binding. -/
private noncomputable def CoefN : ℕ → ℕ → ℕ → ℕ := fun m r s => (PolyN m r).coeff s

/-- The maximizer of a permutation (as a function value) is unique. -/
private lemma maxUnique (m : ℕ) (σ : Equiv.Perm (Fin m)) (a b : Fin m)
    (ha : ∀ t : Fin m, σ t ≤ σ a) (hb : ∀ t : Fin m, σ t ≤ σ b) : a = b := by
  have h1 : σ b ≤ σ a := ha b
  have h2 : σ a ≤ σ b := hb a
  have heq : σ a = σ b := le_antisymm h2 h1
  exact σ.injective heq

/-- Every permutation of a nonempty `Fin` attains a maximum value. -/
private lemma maxExists (m : ℕ) (mpos : 0 < m) (σ : Equiv.Perm (Fin m)) :
    ∃ M : Fin m, ∀ t : Fin m, σ t ≤ σ M := by
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact ⟨⟨0, mpos⟩⟩
  obtain ⟨M, _, hM⟩ := Finset.exists_max_image Finset.univ (fun t => σ t) hne
  exact ⟨M, fun t => hM t (Finset.mem_univ t)⟩

/-- `zeroMatches` unfolds to a condition on any maximizer. -/
private lemma zero_of_max (m : ℕ) (r : ℕ) (σ : Equiv.Perm (Fin m))
    (M : Fin m) (hM : ∀ t : Fin m, σ t ≤ σ M) :
    ZeroPred r σ ↔ r ≤ M.val + 1 := by
  constructor
  · rintro ⟨a, ha, hr⟩
    have e : a = M := maxUnique m σ a M ha hM
    subst e
    exact hr
  · intro hr
    exact ⟨M, hM, hr⟩

/-- `isMeshMatch` unfolds to left-to-right-maximality plus a filter-card condition. -/
private lemma match_of_max (m : ℕ) (r : ℕ) (σ : Equiv.Perm (Fin m))
    (M : Fin m) (hM : ∀ t : Fin m, σ t ≤ σ M) (i : Fin m) :
    MatchPred r σ i ↔
      ((∀ t : Fin m, t < i → σ t < σ i) ∧
        r - 1 ≤ (Finset.univ.filter fun t : Fin m => i < t ∧ t < M ∧ σ i < σ t).card) := by
  constructor
  · rintro ⟨a, ha, hc, hl⟩
    have e : a = M := maxUnique m σ a M ha hM
    subst e
    exact ⟨hl, hc⟩
  · rintro ⟨hl, hc⟩
    exact ⟨M, hM, hc, hl⟩

/-- Vanishing lemma: if the max position is at most `k - 2`, the mesh count is zero. -/
private lemma vanish_meshN (m k : ℕ) (σ : Equiv.Perm (Fin m))
    (M : Fin m) (hM : ∀ t : Fin m, σ t ≤ σ M) (hMb : M.val + 2 ≤ k) :
    meshN k σ = 0 := by
  have hZ : ¬ ZeroPred k σ := by
    rw [zero_of_max m k σ M hM]
    omega
  have hN : ∀ i : Fin m, ¬ MatchPred k σ i := by
    intro i hi
    rw [match_of_max m k σ M hM i] at hi
    obtain ⟨-, hc⟩ := hi
    have hsub : Finset.univ.filter
        (fun t : Fin m => i < t ∧ t < M ∧ σ i < σ t) ⊆ Finset.Iio M := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_Iio]
      exact hx.2.1
    have hle := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hle
    omega
  have hfilter : Finset.univ.filter (MatchPred k σ) = ∅ :=
    Finset.filter_false_of_mem (fun x _ => hN x)
  unfold meshN
  simp [hfilter, hZ]

/-- Base case: every permutation of `Fin (k-1)` has mesh count zero at `r = k`. -/
private lemma base_poly (k : ℕ) (hk : 1 < k) :
    PolyN (k - 1) k = Polynomial.C (Nat.factorial (k - 1)) := by
  have mpos : 0 < k - 1 := by omega
  have hterm : ∀ σ : Equiv.Perm (Fin (k - 1)),
      (Polynomial.X : Polynomial ℕ) ^ meshN k σ = 1 := by
    intro σ
    obtain ⟨M, hM⟩ := maxExists (k - 1) mpos σ
    have hMb : M.val + 2 ≤ k := by
      have hlt := M.isLt
      omega
    rw [vanish_meshN (k - 1) k σ M hM hMb]
    exact pow_zero _
  change ∑ σ : Equiv.Perm (Fin (k - 1)), (Polynomial.X : Polynomial ℕ) ^ meshN k σ
    = Polynomial.C (Nat.factorial (k - 1))
  simp only [hterm]
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin (k - 1)))).card
      = Nat.factorial (k - 1) := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
  simp

/-- Coefficient recurrence at a positive index, from the polynomial recursion. -/
private lemma coeff_rec_succ (c j' : ℕ) (Q : Polynomial ℕ) :
    ((Polynomial.X + Polynomial.C c) * Q).coeff (j' + 1)
      = Q.coeff j' + c * Q.coeff (j' + 1) := by
  rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul,
    Polynomial.coeff_C_mul]

/-- Coefficient recurrence at index zero, from the polynomial recursion. -/
private lemma coeff_rec_zero (c : ℕ) (Q : Polynomial ℕ) :
    ((Polynomial.X + Polynomial.C c) * Q).coeff 0 = c * Q.coeff 0 := by
  rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul_zero,
    Polynomial.coeff_C_mul, zero_add]

/-- Insertion map: plant value `0` at position `p`, shifting `τ` up by one elsewhere. -/
private def Phi (m : ℕ) (p : Fin (m.succ)) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm (Fin (m.succ)) :=
  (Equiv.Perm.decomposeFin.symm (0, τ)) * p.cycleRange

/-- `Phi` sends the insertion position to `0`. -/
private lemma Phi_apply_p (m : ℕ) (p : Fin (m.succ)) (τ : Equiv.Perm (Fin m)) :
    Phi m p τ p = 0 := by
  have h1 : p.cycleRange p = 0 := Fin.cycleRange_self p
  have h2 : (Equiv.Perm.decomposeFin.symm (0, τ)) (0 : Fin (m.succ)) = 0 :=
    Equiv.Perm.decomposeFin_symm_apply_zero 0 τ
  unfold Phi
  rw [Equiv.Perm.mul_apply, h1, h2]

/-- `Phi` sends other positions to shifted values of `τ`. -/
private lemma Phi_apply_succAbove (m : ℕ) (p : Fin (m.succ)) (τ : Equiv.Perm (Fin m))
    (j : Fin m) :
    Phi m p τ (p.succAbove j) = (τ j).succ := by
  have h1 : p.cycleRange (p.succAbove j) = j.succ := Fin.cycleRange_succAbove p j
  have h2 : (Equiv.Perm.decomposeFin.symm (0, τ)) (j.succ) = ((τ j).succ) := by
    have h := Equiv.Perm.decomposeFin_symm_apply_succ τ (0 : Fin (m + 1)) j
    rw [Equiv.swap_self] at h
    exact h
  unfold Phi
  rw [Equiv.Perm.mul_apply, h1, h2]

/-- The insertion position is the unique preimage of `0` under `Phi`. -/
private lemma Phi_preimage_zero (m : ℕ) (p : Fin (m.succ)) (τ : Equiv.Perm (Fin m))
    (x : Fin (m.succ)) (hx : Phi m p τ x = 0) : x = p := by
  have hD0 : (Equiv.Perm.decomposeFin.symm (0, τ)) (0 : Fin (m.succ)) = 0 :=
    Equiv.Perm.decomposeFin_symm_apply_zero 0 τ
  have hCp : p.cycleRange p = 0 := Fin.cycleRange_self p
  unfold Phi at hx
  rw [Equiv.Perm.mul_apply] at hx
  have hCx : p.cycleRange x = 0 := by
    have h2 : (Equiv.Perm.decomposeFin.symm (0, τ)) (p.cycleRange x) =
        (Equiv.Perm.decomposeFin.symm (0, τ)) 0 := by rw [hx, hD0]
    exact (Equiv.Perm.decomposeFin.symm (0, τ)).injective h2
  exact p.cycleRange.injective (hCx.trans hCp.symm)

/-- `Phi` is injective as a map on pairs. -/
private lemma Phi_injective (m : ℕ) : Function.Injective
    (fun pr : Fin (m.succ) × Equiv.Perm (Fin m) => Phi m pr.1 pr.2) := by
  rintro ⟨p, τ⟩ ⟨p', τ'⟩ h
  have h' : Phi m p τ = Phi m p' τ' := h
  have hpp : p = p' := by
    have h0 : Phi m p' τ' p = 0 := by
      have hpp0 : Phi m p τ p = 0 := Phi_apply_p m p τ
      rwa [h'] at hpp0
    exact Phi_preimage_zero m p' τ' p h0
  subst hpp
  have hτ : τ = τ' := by
    apply Equiv.ext
    intro j
    have hc := congrArg (fun σ : Equiv.Perm (Fin (m.succ)) => σ (p.succAbove j)) h'
    rw [Phi_apply_succAbove, Phi_apply_succAbove] at hc
    exact Fin.succ_injective m hc
  rw [hτ]

/-- `Phi` as an equivalence, by injectivity plus a cardinality count. -/
private noncomputable def PhiEquiv (m : ℕ) :
    Fin (m.succ) × Equiv.Perm (Fin m) ≃ Equiv.Perm (Fin (m.succ)) :=
  Equiv.ofBijective _ (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨Phi_injective m, ?_⟩
    rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin,
      Fintype.card_perm, Fintype.card_fin, Fintype.card_fin,
      Nat.succ_eq_add_one, Nat.factorial_succ])

/-- Reindex the counting polynomial along `Phi`. -/
private lemma poly_reindex (m k : ℕ) : PolyN (m.succ) k
    = ∑ _pr : Fin (m.succ) × Equiv.Perm (Fin m),
      (Polynomial.X : Polynomial ℕ) ^ meshN k (Phi m _pr.1 _pr.2) := by
  change (∑ σ : Equiv.Perm (Fin (m.succ)), (Polynomial.X : Polynomial ℕ) ^ meshN k σ) = _
  exact (Fintype.sum_equiv (PhiEquiv m)
    (fun _pr : Fin (m.succ) × Equiv.Perm (Fin m) =>
      (Polynomial.X : Polynomial ℕ) ^ meshN k (Phi m _pr.1 _pr.2))
    (fun σ : Equiv.Perm (Fin (m.succ)) => (Polynomial.X : Polynomial ℕ) ^ meshN k σ)
    (fun _pr => rfl)).symm

/-- The shifted max position maximizes `Phi`. -/
private lemma Phi_max (m : ℕ) (p : Fin (m.succ)) (τ : Equiv.Perm (Fin m))
    (M' : Fin m) (hM' : ∀ t : Fin m, τ t ≤ τ M') :
    ∀ x : Fin (m.succ), Phi m p τ x ≤ Phi m p τ (p.succAbove M') := by
  intro x
  by_cases hxp : x = p
  · subst hxp
    rw [Phi_apply_p]
    exact Fin.zero_le _
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hxp
    have e1 : Phi m p τ x = (τ j).succ := by
      rw [← hj]
      exact Phi_apply_succAbove m p τ j
    have e2 : Phi m p τ (p.succAbove M') = (τ M').succ :=
      Phi_apply_succAbove m p τ M'
    rw [e1, e2]
    exact Fin.succ_le_succ_iff.mpr (hM' j)

/-- Left-to-right maximality at the insertion point holds iff it is at the front. -/
private lemma Phi_ltr_p (m : ℕ) (p : Fin (m.succ)) (τ : Equiv.Perm (Fin m)) :
    (∀ t : Fin (m.succ), t < p → Phi m p τ t < Phi m p τ p) ↔ p = 0 := by
  constructor
  · intro h
    by_contra hne
    have h0lt : (0 : Fin (m.succ)) < p := by
      by_contra hcon
      rw [not_lt] at hcon
      exact hne (le_antisymm hcon (Fin.zero_le p))
    have hbad := h 0 h0lt
    rw [Phi_apply_p] at hbad
    exact absurd hbad (not_lt_of_ge (Fin.zero_le _))
  · intro hp t ht
    subst hp
    exact absurd ht (Fin.not_lt_zero t)

/-- Left-to-right maximality transfers across the insertion. -/
private lemma Phi_ltr_succAbove (m : ℕ) (p : Fin (m.succ)) (τ : Equiv.Perm (Fin m))
    (j : Fin m) :
    (∀ t : Fin (m.succ), t < p.succAbove j → Phi m p τ t < Phi m p τ (p.succAbove j))
    ↔ (∀ i : Fin m, i < j → τ i < τ j) := by
  constructor
  · intro h i hij
    have hlt : p.succAbove i < p.succAbove j :=
      Fin.succAbove_lt_succAbove_iff.mpr hij
    have h2 := h _ hlt
    rw [Phi_apply_succAbove, Phi_apply_succAbove] at h2
    exact Fin.succ_lt_succ_iff.mp h2
  · intro h t ht
    by_cases htp : t = p
    · subst htp
      rw [Phi_apply_p, Phi_apply_succAbove]
      exact Fin.succ_pos _
    · obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq htp
      have hij : i < j := by
        have hrew : p.succAbove i < p.succAbove j := by
          rw [hi]
          exact ht
        exact Fin.succAbove_lt_succAbove_iff.mp hrew
      have h2 := h i hij
      have e1 : Phi m p τ t = (τ i).succ := by
        rw [← hi]
        exact Phi_apply_succAbove m p τ i
      have e2 : Phi m p τ (p.succAbove j) = (τ j).succ :=
        Phi_apply_succAbove m p τ j
      rw [e1, e2]
      exact Fin.succ_lt_succ_iff.mpr h2

/-- The witness filter at a shifted position has the same card as for `τ`. -/
private lemma Phi_filter_card (m : ℕ) (p : Fin (m.succ)) (τ : Equiv.Perm (Fin m))
    (M' : Fin m) (j : Fin m) :
    (Finset.univ.filter (fun i : Fin m =>
      j < i ∧ i < M' ∧ τ j < τ i)).card
    = (Finset.univ.filter (fun t : Fin (m.succ) =>
      p.succAbove j < t ∧ t < p.succAbove M' ∧
        Phi m p τ (p.succAbove j) < Phi m p τ t)).card := by
  apply Finset.card_bij (fun i _ => p.succAbove i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨hij, hiM, hτ⟩ := hi
    refine ⟨Fin.succAbove_lt_succAbove_iff.mpr hij,
      Fin.succAbove_lt_succAbove_iff.mpr hiM, ?_⟩
    rw [Phi_apply_succAbove, Phi_apply_succAbove]
    exact Fin.succ_lt_succ_iff.mpr hτ
  · intro a₁ _ a₂ _ heq
    exact Fin.succAbove_right_injective heq
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    obtain ⟨hjt, htM, hστ⟩ := ht
    have htp : t ≠ p := by
      intro hcon
      subst hcon
      rw [Phi_apply_p, Phi_apply_succAbove] at hστ
      exact absurd hστ (not_lt_of_ge (Fin.zero_le _))
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq htp
    have hmem : i ∈ Finset.univ.filter (fun i : Fin m =>
        j < i ∧ i < M' ∧ τ j < τ i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hjt' : j < i := by
        have hrew : p.succAbove j < p.succAbove i := by
          rw [hi]
          exact hjt
        exact Fin.succAbove_lt_succAbove_iff.mp hrew
      have htM' : i < M' := by
        have hrew : p.succAbove i < p.succAbove M' := by
          rw [hi]
          exact htM
        exact Fin.succAbove_lt_succAbove_iff.mp hrew
      have hτ' : τ j < τ i := by
        have hrew : Phi m p τ (p.succAbove j) < Phi m p τ (p.succAbove i) := by
          rw [hi]
          exact hστ
        rw [Phi_apply_succAbove, Phi_apply_succAbove] at hrew
        exact Fin.succ_lt_succ_iff.mp hrew
      exact ⟨hjt', htM', hτ'⟩
    exact ⟨i, hmem, hi⟩

/-- The witness filter at a fresh front position counts the earlier-max positions. -/
private lemma Phi_filter_p0 (m : ℕ) (τ : Equiv.Perm (Fin m)) (M' : Fin m) :
    (Finset.univ.filter (fun t : Fin (m.succ) =>
      (0 : Fin (m.succ)) < t ∧ t < (0 : Fin (m.succ)).succAbove M' ∧
        Phi m 0 τ 0 < Phi m 0 τ t)).card = M'.val := by
  have hM : (0 : Fin (m.succ)).succAbove M' = M'.succ := Fin.zero_succAbove M'
  have hσ0 : Phi m 0 τ 0 = 0 := Phi_apply_p m 0 τ
  rw [hM]
  have hset : Finset.univ.filter (fun t : Fin (m.succ) =>
      (0 : Fin (m.succ)) < t ∧ t < M'.succ ∧ Phi m 0 τ 0 < Phi m 0 τ t)
      = (Finset.Iio M'.succ).erase 0 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      Finset.mem_Iio]
    constructor
    · rintro ⟨h0t, htM, hσ⟩
      refine ⟨?_, htM⟩
      intro hcon
      subst hcon
      rw [hσ0] at hσ
      exact absurd hσ (lt_irrefl _)
    · rintro ⟨hne, htM⟩
      refine ⟨?_, htM, ?_⟩
      · rwa [Fin.pos_iff_ne_zero]
      · rw [hσ0]
        by_contra hcon
        push Not at hcon
        have h0 := le_antisymm hcon (Fin.zero_le _)
        have hpre := Phi_preimage_zero m 0 τ t h0
        exact hne hpre
  rw [hset, Finset.card_erase_of_mem]
  · rw [Fin.card_Iio]
    simp [Fin.val_succ]
  · simp [Fin.succ_pos]

/-- Value of `succAbove` in terms of a case split. -/
private lemma succAbove_val_add (m : ℕ) (p : Fin (m.succ)) (i : Fin m) :
    (p.succAbove i).val = i.val + (if p.val ≤ i.val then 1 else 0) := by
  by_cases h : p.val ≤ i.val
  · have hle : p ≤ i.castSucc := by
      rw [Fin.le_iff_val_le_val, Fin.val_castSucc]
      exact h
    rw [Fin.succAbove_of_le_castSucc p i hle, Fin.val_succ]
    simp [h]
  · have hlt : i.castSucc < p := by
      rw [Fin.castSucc_lt_iff_succ_le, Fin.le_iff_val_le_val, Fin.val_succ]
      omega
    rw [Fin.succAbove_of_castSucc_lt p i hlt, Fin.val_castSucc]
    simp [h]

/-- The position of the maximum value of `τ : S_{t+1}`, as `τ⁻¹(last)`. -/
private def maxPos (t : ℕ) (τ : Equiv.Perm (Fin (t.succ))) : Fin (t.succ) :=
  τ.symm (Fin.last t)

/-- `maxPos` indeed maximizes `τ`. -/
private lemma maxPos_max (t : ℕ) (τ : Equiv.Perm (Fin (t.succ))) :
    ∀ x : Fin (t.succ), τ x ≤ τ (maxPos t τ) := by
  intro x
  change τ x ≤ τ (τ.symm (Fin.last t))
  rw [Equiv.apply_symm_apply]
  exact Fin.le_last _

/-- `MatchPred` transfers across the insertion at shifted positions. -/
private lemma Phi_match_transfer (t a : ℕ) (p : Fin ((t.succ).succ))
    (τ : Equiv.Perm (Fin (t.succ))) (j : Fin (t.succ)) :
    MatchPred (a + 2) (Phi (t.succ) p τ) (p.succAbove j) ↔
      MatchPred (a + 2) τ j := by
  have hM' := maxPos_max t τ
  have hMσ := Phi_max (t.succ) p τ (maxPos t τ) hM'
  rw [match_of_max _ _ _ _ hMσ, match_of_max _ _ _ _ hM']
  rw [Phi_ltr_succAbove]
  have hcard := Phi_filter_card (t.succ) p τ (maxPos t τ) j
  constructor
  · rintro ⟨hl, hc⟩
    exact ⟨hl, by rwa [← hcard] at hc⟩
  · rintro ⟨hl, hc⟩
    exact ⟨hl, by rwa [hcard] at hc⟩

/-- `MatchPred` at the insertion point holds iff it is at the front with large max. -/
private lemma Phi_match_p (t a : ℕ) (p : Fin ((t.succ).succ))
    (τ : Equiv.Perm (Fin (t.succ))) :
    MatchPred (a + 2) (Phi (t.succ) p τ) p ↔
      (p = 0 ∧ a + 1 ≤ (maxPos t τ).val) := by
  have hM' := maxPos_max t τ
  have hMσ := Phi_max (t.succ) p τ (maxPos t τ) hM'
  have hsub : a + 2 - 1 = a + 1 := by omega
  rw [match_of_max _ _ _ _ hMσ p, Phi_ltr_p]
  constructor
  · rintro ⟨hl, hc⟩
    subst hl
    refine ⟨rfl, ?_⟩
    have h0 := Phi_filter_p0 (t.succ) τ (maxPos t τ)
    omega
  · rintro ⟨rfl, hu⟩
    refine ⟨rfl, ?_⟩
    have h0 := Phi_filter_p0 (t.succ) τ (maxPos t τ)
    omega

/-- The match set of `σ = Phi p τ` is the shifted match set of `τ` plus possibly `p`. -/
private lemma Phi_filter_set (t a : ℕ) (p : Fin ((t.succ).succ))
    (τ : Equiv.Perm (Fin (t.succ))) :
    Finset.univ.filter (MatchPred (a + 2) (Phi (t.succ) p τ))
      = (Finset.univ.filter (MatchPred (a + 2) τ)).map
          ⟨p.succAbove, Fin.succAbove_right_injective⟩ ∪
        (if p = 0 ∧ a + 1 ≤ (maxPos t τ).val then {p} else ∅) := by
  ext x
  by_cases hxp : x = p
  · subst hxp
    have hL : (x ∈ Finset.univ.filter (MatchPred (a + 2) (Phi (t.succ) x τ)))
        ↔ (x = 0 ∧ a + 1 ≤ (maxPos t τ).val) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Phi_match_p t a x τ
    have hR : (x ∈ (Finset.univ.filter (MatchPred (a + 2) τ)).map
          ⟨x.succAbove, Fin.succAbove_right_injective⟩ ∪
        (if x = 0 ∧ a + 1 ≤ (maxPos t τ).val then ({x} : Finset _) else ∅))
        ↔ (x = 0 ∧ a + 1 ≤ (maxPos t τ).val) := by
      have hne : ¬ ∃ j : Fin (t.succ),
          j ∈ Finset.univ.filter (MatchPred (a + 2) τ) ∧ x.succAbove j = x := by
        rintro ⟨j, _, hj⟩
        exact Fin.succAbove_ne x j hj
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk,
        Finset.mem_union, hne, false_or]
      by_cases hcond : x = 0 ∧ a + 1 ≤ (maxPos t τ).val
      · rw [ite_eq_left hcond]
        exact iff_of_true (Finset.mem_singleton_self x) hcond
      · rw [ite_eq_right hcond]
        exact iff_of_false (Finset.notMem_empty x) hcond
    rw [hL, hR]
  · have hnot : x ∉ (if p = 0 ∧ a + 1 ≤ (maxPos t τ).val then
        ({p} : Finset (Fin ((t.succ).succ))) else ∅) := by
      by_cases hcond : p = 0 ∧ a + 1 ≤ (maxPos t τ).val
      · rw [ite_eq_left hcond]
        simp [hxp]
      · rw [ite_eq_right hcond]
        simp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_union, hnot, or_false]
    constructor
    · intro hx
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hxp
      exact ⟨j, (Phi_match_transfer t a p τ j).mp hx, rfl⟩
    · rintro ⟨j, hjmem, hjx⟩
      subst hjx
      exact (Phi_match_transfer t a p τ j).mpr hjmem

/-- Cardinality version of the match-set identity. -/
private lemma Phi_filter_card_eq (t a : ℕ) (p : Fin ((t.succ).succ))
    (τ : Equiv.Perm (Fin (t.succ))) :
    (Finset.univ.filter (MatchPred (a + 2) (Phi (t.succ) p τ))).card
      = (Finset.univ.filter (MatchPred (a + 2) τ)).card
        + (if p = 0 ∧ a + 1 ≤ (maxPos t τ).val then 1 else 0) := by
  have hdisj : Disjoint
      ((Finset.univ.filter (MatchPred (a + 2) τ)).map
        ⟨p.succAbove, Fin.succAbove_right_injective⟩)
      (if p = 0 ∧ a + 1 ≤ (maxPos t τ).val then ({p} : Finset _) else ∅) := by
    rw [Finset.disjoint_left]
    intro y hy hmem
    obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hy
    by_cases hcond : p = 0 ∧ a + 1 ≤ (maxPos t τ).val
    · rw [ite_eq_left hcond] at hmem
      rw [Finset.mem_singleton.mp hmem] at hj
      exact Fin.succAbove_ne p j hj
    · rw [ite_eq_right hcond] at hmem
      exact Finset.notMem_empty y hmem
  rw [Phi_filter_set, Finset.card_union_of_disjoint hdisj, Finset.card_map]
  congr 1
  by_cases hcond : p = 0 ∧ a + 1 ≤ (maxPos t τ).val
  · rw [ite_eq_left hcond, ite_eq_left hcond, Finset.card_singleton]
  · rw [ite_eq_right hcond, ite_eq_right hcond, Finset.card_empty]

/-- The zero-match condition for `σ = Phi p τ`, in terms of `τ`'s max position. -/
private lemma Phi_zero_iff (t a : ℕ) (p : Fin ((t.succ).succ))
    (τ : Equiv.Perm (Fin (t.succ))) :
    ZeroPred (a + 2) (Phi (t.succ) p τ) ↔
      a + 2 ≤ (maxPos t τ).val + (if p.val ≤ (maxPos t τ).val then 1 else 0) + 1 := by
  have hM' := maxPos_max t τ
  have hMσ := Phi_max (t.succ) p τ _ hM'
  rw [zero_of_max _ _ _ _ hMσ, succAbove_val_add]

/-- meshCount change in the high case (`M'(τ) ≥ a + 1`). -/
private lemma Phi_mesh_high (t a : ℕ) (p : Fin ((t.succ).succ))
    (τ : Equiv.Perm (Fin (t.succ))) (hu : a + 1 ≤ (maxPos t τ).val) :
    meshN (a + 2) (Phi (t.succ) p τ) = meshN (a + 2) τ + (if p = 0 then 1 else 0) := by
  have hcard := Phi_filter_card_eq t a p τ
  have hzσ : ZeroPred (a + 2) (Phi (t.succ) p τ) := by
    rw [Phi_zero_iff]
    split <;> omega
  have hzτ : ZeroPred (a + 2) τ := by
    rw [zero_of_max _ _ _ _ (maxPos_max t τ)]
    omega
  unfold meshN
  rw [hcard, ite_eq_left hzσ, ite_eq_left hzτ]
  by_cases hp : p = 0
  · have hc : p = 0 ∧ a + 1 ≤ (maxPos t τ).val := ⟨hp, hu⟩
    rw [ite_eq_left hc, ite_eq_left hp]
  · have hc : ¬ (p = 0 ∧ a + 1 ≤ (maxPos t τ).val) := fun h => hp h.1
    rw [ite_eq_right hc, ite_eq_right hp, add_zero]

/-- meshCount change in the middle case (`M'(τ) = a`). -/
private lemma Phi_mesh_mid (t a : ℕ) (p : Fin ((t.succ).succ))
    (τ : Equiv.Perm (Fin (t.succ))) (hu : (maxPos t τ).val = a) :
    meshN (a + 2) (Phi (t.succ) p τ) = (if p.val ≤ a then 1 else 0) := by
  have hcard := Phi_filter_card_eq t a p τ
  have hcond : ¬ (p = 0 ∧ a + 1 ≤ (maxPos t τ).val) := by omega
  rw [ite_eq_right hcond, add_zero] at hcard
  have hvan : meshN (a + 2) τ = 0 :=
    vanish_meshN _ _ _ _ (maxPos_max t τ) (by omega)
  have hvan0 : (Finset.univ.filter (MatchPred (a + 2) τ)).card = 0 := by
    unfold meshN at hvan
    omega
  have hz : (if ZeroPred (a + 2) (Phi (t.succ) p τ) then 1 else 0)
      = (if p.val ≤ a then 1 else 0) := by
    by_cases h : p.val ≤ a
    · rw [ite_eq_left h]
      have hzσ : ZeroPred (a + 2) (Phi (t.succ) p τ) := by
        rw [Phi_zero_iff t a p τ, hu, ite_eq_left h]
      rw [ite_eq_left hzσ]
    · rw [ite_eq_right h]
      have hzσ : ¬ ZeroPred (a + 2) (Phi (t.succ) p τ) := by
        rw [Phi_zero_iff t a p τ, hu, ite_eq_right h]
        omega
      rw [ite_eq_right hzσ]
  unfold meshN
  rw [hcard, hvan0, hz]
  simp

/-- meshCount change in the low case (`M'(τ) < a`). -/
private lemma Phi_mesh_low (t a : ℕ) (p : Fin ((t.succ).succ))
    (τ : Equiv.Perm (Fin (t.succ))) (hu : (maxPos t τ).val < a) :
    meshN (a + 2) (Phi (t.succ) p τ) = 0 := by
  have hcard := Phi_filter_card_eq t a p τ
  have hcond : ¬ (p = 0 ∧ a + 1 ≤ (maxPos t τ).val) := by omega
  rw [ite_eq_right hcond, add_zero] at hcard
  have hvanτ : meshN (a + 2) τ = 0 :=
    vanish_meshN _ _ _ _ (maxPos_max t τ) (by omega)
  have hzσ : ¬ ZeroPred (a + 2) (Phi (t.succ) p τ) := by
    rw [Phi_zero_iff]
    split <;> omega
  have hcard0 : (Finset.univ.filter (MatchPred (a + 2) τ)).card = 0 := by
    unfold meshN at hvanτ
    omega
  unfold meshN
  rw [hcard, hcard0, ite_eq_right hzσ]

/-- Right-multiplication by a swap sends one max-fiber to another. -/
private lemma fiber_card_eq (t u₁ u₂ : ℕ) (h₁ : u₁ < t.succ) (h₂ : u₂ < t.succ) :
    (Finset.univ.filter (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val = u₁)).card
      = (Finset.univ.filter (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val = u₂)).card := by
  obtain ⟨a, ha⟩ : ∃ a : Fin (t.succ), a.val = u₁ := ⟨⟨u₁, h₁⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin (t.succ), b.val = u₂ := ⟨⟨u₂, h₂⟩, rfl⟩
  have hss : Equiv.swap a b * Equiv.swap a b = 1 := Equiv.swap_mul_self a b
  have hsM : ∀ τ : Equiv.Perm (Fin (t.succ)),
      Equiv.swap a b (Equiv.swap a b (maxPos t τ)) = maxPos t τ := fun τ => by
    have h := congrArg (· (maxPos t τ)) hss
    simp
  have hsym : ∀ τ : Equiv.Perm (Fin (t.succ)),
      (τ * Equiv.swap a b).symm (Fin.last t) = Equiv.swap a b (maxPos t τ) := by
    intro τ
    rw [Equiv.symm_apply_eq, Equiv.Perm.mul_apply, hsM τ]
    exact (Equiv.apply_symm_apply τ (Fin.last t)).symm
  have hmap : ∀ τ : Equiv.Perm (Fin (t.succ)),
      (maxPos t (τ * Equiv.swap a b)).val
        = (Equiv.swap a b (maxPos t τ)).val := by
    intro τ
    change ((τ * Equiv.swap a b).symm (Fin.last t)).val = _
    rw [hsym]
  apply Finset.card_bij (fun τ _ => τ * Equiv.swap a b)
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    have hMa : maxPos t τ = a := Fin.ext (hτ.trans ha.symm)
    rw [hmap, hMa, Equiv.swap_apply_left]
    exact hb
  · intro τ₁ _ τ₂ _ h
    exact mul_right_cancel h
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    refine ⟨σ * Equiv.swap a b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hMb : maxPos t σ = b := Fin.ext (hσ.trans hb.symm)
      rw [hmap, hMb, Equiv.swap_apply_right]
      exact ha
    · show σ * Equiv.swap a b * Equiv.swap a b = σ
      rw [mul_assoc, hss, mul_one]

/-- Every max-fiber has `(t)!` elements. -/
private lemma fiber_card (t u : ℕ) (hu : u < t.succ) :
    (Finset.univ.filter (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val = u)).card
      = Nat.factorial t := by
  have htot : (Finset.univ : Finset (Equiv.Perm (Fin (t.succ)))).card
      = Nat.factorial (t + 1) := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hmaps : Set.MapsTo (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val)
      ↑(Finset.univ : Finset (Equiv.Perm (Fin (t.succ)))) ↑(Finset.range (t + 1)) := by
    intro τ _
    simp only [Finset.mem_coe, Finset.mem_range]
    exact (maxPos t τ).isLt
  have hfib := Finset.card_eq_sum_card_fiberwise (f :=
    fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val)
    (s := Finset.univ) (t := Finset.range (t + 1)) hmaps
  have hconst : ∀ v ∈ Finset.range (t + 1),
      (Finset.univ.filter (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val = v)).card
        = (Finset.univ.filter (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val =
            u)).card := by
    intro v hv
    exact fiber_card_eq t v u (Finset.mem_range.mp hv) hu
  rw [htot, Finset.sum_eq_card_nsmul hconst, Finset.card_range, smul_eq_mul,
    Nat.factorial_succ] at hfib
  exact (Nat.mul_left_cancel (Nat.succ_pos t) hfib).symm

/-- Positions with value at most `a` form an initial interval of cardinal `a + 1`. -/
private lemma filter_le_card (t a : ℕ) (h : a ≤ t) :
    (Finset.univ.filter (fun p : Fin ((t.succ).succ) => p.val ≤ a)).card = a + 1 := by
  have hF : Finset.univ.filter (fun p : Fin ((t.succ).succ) => p.val ≤ a)
      = Finset.Iio (⟨a + 1, by omega⟩ : Fin ((t.succ).succ)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio,
      Fin.lt_def]
    show p.val ≤ a ↔ p.val < a + 1
    omega
  rw [hF, Fin.card_Iio]

/-- Complement count for positions. -/
private lemma filter_card_add (t a : ℕ) (h : a ≤ t) :
    (Finset.univ.filter (fun p : Fin ((t.succ).succ) => ¬ p.val ≤ a)).card + (a + 1)
      = (t.succ).succ := by
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin ((t.succ).succ)))) (fun p => p.val ≤ a)
  rw [filter_le_card t a h] at hsum
  have hU : (Finset.univ : Finset (Fin ((t.succ).succ))).card = (t.succ).succ := by
    rw [Finset.card_univ, Fintype.card_fin]
  omega

/-- Summing over the insertion position in the high case. -/
private lemma high_inner (t a : ℕ) (τ : Equiv.Perm (Fin (t.succ)))
    (hu : a + 1 ≤ (maxPos t τ).val) :
    ∑ p : Fin ((t.succ).succ),
        (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ)
      = (Polynomial.X + Polynomial.C (t.succ))
        * (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) τ := by
  have hC : ((t.succ : ℕ) : Polynomial ℕ) = Polynomial.C (t.succ) := by
    rw [← map_natCast Polynomial.C (t.succ), Nat.cast_id]
  have h0 : meshN (a + 2) (Phi (t.succ) 0 τ) = meshN (a + 2) τ + 1 := by
    rw [Phi_mesh_high t a 0 τ hu, ite_eq_left rfl]
  have hrest : ∀ p ∈ Finset.univ.erase (0 : Fin ((t.succ).succ)),
      (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ)
        = (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) τ := by
    intro p hp
    have hne : p ≠ 0 := Finset.ne_of_mem_erase hp
    rw [Phi_mesh_high t a p τ hu, ite_eq_right hne, add_zero]
  have hcard : (Finset.univ.erase (0 : Fin ((t.succ).succ))).card = t.succ := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
    omega
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin ((t.succ).succ))), h0,
    Finset.sum_congr rfl hrest, Finset.sum_const, hcard, nsmul_eq_mul, pow_succ,
    add_mul, mul_comm (Polynomial.X : Polynomial ℕ) _, ← hC]

/-- Summing over the insertion position in the middle case. -/
private lemma mid_inner (t a : ℕ) (τ : Equiv.Perm (Fin (t.succ)))
    (hu : (maxPos t τ).val = a) :
    ∑ p : Fin ((t.succ).succ),
        (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ)
      = ((Finset.univ.filter (fun p : Fin ((t.succ).succ) => p.val ≤ a)).card)
          • (Polynomial.X : Polynomial ℕ)
        + ((Finset.univ.filter (fun p : Fin ((t.succ).succ) => ¬ p.val ≤ a)).card)
          • (1 : Polynomial ℕ) := by
  have hterm : ∀ p : Fin ((t.succ).succ),
      (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ)
        = (if p.val ≤ a then (Polynomial.X : Polynomial ℕ) else 0)
          + (if ¬ p.val ≤ a then (1 : Polynomial ℕ) else 0) := by
    intro p
    rw [Phi_mesh_mid t a p τ hu]
    by_cases h : p.val ≤ a <;> simp [h]
  rw [Finset.sum_congr rfl (fun p _ => hterm p), Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const]

/-- Summing over the insertion position in the low case. -/
private lemma low_inner (t a : ℕ) (τ : Equiv.Perm (Fin (t.succ)))
    (hu : (maxPos t τ).val < a) :
    ∑ p : Fin ((t.succ).succ),
        (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ)
      = ((t.succ).succ) • (1 : Polynomial ℕ) := by
  have hterm : ∀ p : Fin ((t.succ).succ),
      (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ) = 1 := by
    intro p
    rw [Phi_mesh_low t a p τ hu]
    exact pow_zero _
  rw [Finset.sum_congr rfl (fun p _ => hterm p), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]

/-- Purely algebraic aggregate identity for the low fibers. -/
private lemma aggregate_identity (a T K Fc : ℕ) (X Cm : Polynomial ℕ)
    (hC : ((T : ℕ) : Polynomial ℕ) = Cm)
    (hK : K + (a + 1) = T + 1) :
    a • (Fc • ((((T + 1 : ℕ))) • (1 : Polynomial ℕ)))
      + Fc • ((a + 1) • X + K • (1 : Polynomial ℕ))
      = ((a + 1) * Fc) • (X + Cm) := by
  have haK : a + K = T := by omega
  have hnat : a * (T + 1) + K = (a + 1) * T := by
    calc a * (T + 1) + K = a * T + (a + K) := by ring
      _ = a * T + T := by rw [haK]
      _ = (a + 1) * T := by ring
  have hnatC : ((a * (T + 1) + K : ℕ) : Polynomial ℕ) = (((a + 1) * T : ℕ)) := by
    exact_mod_cast hnat
  have e1 : ((a : Polynomial ℕ) * (((T + 1 : ℕ)) : Polynomial ℕ) + (K : Polynomial ℕ))
      = ((a + 1 : ℕ) : Polynomial ℕ) * (T : Polynomial ℕ) := by
    conv_lhs => rw [← Nat.cast_mul, ← Nat.cast_add, hnatC, Nat.cast_mul]
  simp only [nsmul_eq_mul, mul_one]
  rw [← hC, Nat.cast_mul]
  rw [show ((a : Polynomial ℕ) * ((Fc : Polynomial ℕ) * (((T + 1 : ℕ)) : Polynomial ℕ))
      + (Fc : Polynomial ℕ) * (((a + 1 : ℕ) : Polynomial ℕ) * X + (K : Polynomial ℕ)))
      = (Fc : Polynomial ℕ) * ((a : Polynomial ℕ) * (((T + 1 : ℕ)) : Polynomial ℕ)
        + (K : Polynomial ℕ))
        + (Fc : Polynomial ℕ) * (((a + 1 : ℕ) : Polynomial ℕ) * X) from by ring, e1]
  ring

/-- The Stirling-type recursion for the counting polynomial (main step). -/
private lemma poly_rec (t a : ℕ) (h : a ≤ t) : PolyN (t.succ.succ) (a + 2)
    = (Polynomial.X + Polynomial.C (t.succ)) * PolyN (t.succ) (a + 2) := by
  have hLHS : PolyN (t.succ.succ) (a + 2)
      = ∑ τ : Equiv.Perm (Fin (t.succ)), ∑ p : Fin ((t.succ).succ),
        (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ) := by
    have h1 := poly_reindex (t.succ) (a + 2)
    rw [Fintype.sum_prod_type, Finset.sum_comm] at h1
    exact h1
  have hRHS : (Polynomial.X + Polynomial.C (t.succ)) * PolyN (t.succ) (a + 2)
      = ∑ τ : Equiv.Perm (Fin (t.succ)),
        (Polynomial.X + Polynomial.C (t.succ))
          * (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) τ := by
    change (Polynomial.X + Polynomial.C (t.succ)) *
      (∑ σ : Equiv.Perm (Fin (t.succ)),
        (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) σ) = _
    rw [Finset.mul_sum]
  have hsplit : ∀ (f : Equiv.Perm (Fin (t.succ)) → Polynomial ℕ),
      ∑ τ : Equiv.Perm (Fin (t.succ)), f τ
        = (∑ τ ∈ Finset.univ.filter
            (fun τ : Equiv.Perm (Fin (t.succ)) => a + 1 ≤ (maxPos t τ).val), f τ)
          + (∑ τ ∈ Finset.univ.filter
            (fun τ : Equiv.Perm (Fin (t.succ)) => ¬ a + 1 ≤ (maxPos t τ).val), f τ) := by
    intro f
    rw [Finset.sum_filter_add_sum_filter_not]
  rw [hLHS, hRHS, hsplit, hsplit]
  congr 1
  · apply Finset.sum_congr rfl
    intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    exact high_inner t a τ hτ
  · have hLowEq : Finset.univ.filter
          (fun τ : Equiv.Perm (Fin (t.succ)) => ¬ a + 1 ≤ (maxPos t τ).val)
        = Finset.univ.filter
          (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a) := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [hLowEq]
    have hmaps : ∀ τ ∈ Finset.univ.filter
        (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a),
        (maxPos t τ).val ∈ Finset.range (a + 1) := by
      intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_range] at hτ ⊢
      omega
    have hfibS := Finset.sum_fiberwise_of_maps_to hmaps
      (fun τ : Equiv.Perm (Fin (t.succ)) => ∑ p : Fin ((t.succ).succ),
        (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ))
    have hfibR := Finset.sum_fiberwise_of_maps_to hmaps
      (fun τ : Equiv.Perm (Fin (t.succ)) =>
        (Polynomial.X + Polynomial.C (t.succ))
          * (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) τ)
    have hred : ∀ u ∈ Finset.range (a + 1),
        (Finset.univ.filter
          (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a)).filter
          (fun τ => (maxPos t τ).val = u)
        = Finset.univ.filter
          (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val = u) := by
      intro u hu
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨-, h2⟩
        exact h2
      · intro h2
        refine ⟨?_, h2⟩
        simp only [Finset.mem_range] at hu
        omega
    have hTotS : (∑ τ ∈ Finset.univ.filter
          (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a),
          ∑ p : Fin ((t.succ).succ),
          (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ))
        = a • ((Nat.factorial t)
            • ((((t.succ).succ : ℕ)) • (1 : Polynomial ℕ)))
          + (Nat.factorial t)
            • ((a + 1) • (Polynomial.X : Polynomial ℕ)
              + (Finset.univ.filter
                (fun p : Fin ((t.succ).succ) => ¬ p.val ≤ a)).card
                • (1 : Polynomial ℕ)) := by
      rw [← hfibS]
      show (∑ u ∈ Finset.range (a + 1), ∑ τ ∈ (Finset.univ.filter
        (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a)).filter
        (fun τ => (maxPos t τ).val = u),
        ∑ p : Fin ((t.succ).succ),
        (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ)) = _
      rw [Finset.sum_range_succ]
      congr 1
      · have hconst : ∀ u ∈ Finset.range a,
            (∑ τ ∈ (Finset.univ.filter
              (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a)).filter
              (fun τ => (maxPos t τ).val = u),
              ∑ p : Fin ((t.succ).succ),
              (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ))
            = (Nat.factorial t) • ((((t.succ).succ : ℕ)) • (1 : Polynomial ℕ)) := by
          intro u hu
          have hu' : u ∈ Finset.range (a + 1) := by
            simp only [Finset.mem_range] at hu ⊢
            omega
          rw [hred u hu']
          have hterm : ∀ τ ∈ Finset.univ.filter
              (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val = u),
              (∑ p : Fin ((t.succ).succ),
                (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ))
              = ((((t.succ).succ : ℕ)) • (1 : Polynomial ℕ)) := by
            intro τ hτ
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
            simp only [Finset.mem_range] at hu
            have hlt : (maxPos t τ).val < a := by omega
            exact low_inner t a τ hlt
          rw [Finset.sum_congr rfl hterm, Finset.sum_const,
            fiber_card t u (by simp only [Finset.mem_range] at hu; omega)]
        rw [Finset.sum_eq_card_nsmul hconst, Finset.card_range]
      · show (∑ τ ∈ (Finset.univ.filter
          (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a)).filter
          (fun τ => (maxPos t τ).val = a),
          ∑ p : Fin ((t.succ).succ),
          (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ)) = _
        rw [hred a (by simp only [Finset.mem_range]; omega)]
        have htermM : ∀ τ ∈ Finset.univ.filter
            (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val = a),
            (∑ p : Fin ((t.succ).succ),
              (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) (Phi (t.succ) p τ))
            = ((Finset.univ.filter (fun p : Fin ((t.succ).succ) => p.val ≤ a)).card)
                • (Polynomial.X : Polynomial ℕ)
              + ((Finset.univ.filter
                (fun p : Fin ((t.succ).succ) => ¬ p.val ≤ a)).card)
                • (1 : Polynomial ℕ) := by
          intro τ hτ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
          exact mid_inner t a τ hτ
        rw [Finset.sum_congr rfl htermM, Finset.sum_const,
          fiber_card t a (by omega), filter_le_card t a h]
    have hTotR : (∑ τ ∈ Finset.univ.filter
          (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a),
          (Polynomial.X + Polynomial.C (t.succ))
            * (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) τ)
        = ((a + 1) * Nat.factorial t)
          • ((Polynomial.X + Polynomial.C (t.succ))) := by
      rw [← hfibR]
      show (∑ u ∈ Finset.range (a + 1), ∑ τ ∈ (Finset.univ.filter
        (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a)).filter
        (fun τ => (maxPos t τ).val = u),
        (Polynomial.X + Polynomial.C (t.succ))
          * (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) τ) = _
      have hconstR : ∀ u ∈ Finset.range (a + 1),
          (∑ τ ∈ (Finset.univ.filter
            (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val ≤ a)).filter
            (fun τ => (maxPos t τ).val = u),
            (Polynomial.X + Polynomial.C (t.succ))
              * (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) τ)
          = (Nat.factorial t) • (Polynomial.X + Polynomial.C (t.succ)) := by
        intro u hu
        rw [hred u hu]
        have htermR : ∀ τ ∈ Finset.univ.filter
            (fun τ : Equiv.Perm (Fin (t.succ)) => (maxPos t τ).val = u),
            (Polynomial.X + Polynomial.C (t.succ))
              * (Polynomial.X : Polynomial ℕ) ^ meshN (a + 2) τ
            = (Polynomial.X + Polynomial.C (t.succ)) := by
          intro τ hτ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
          simp only [Finset.mem_range] at hu
          have hc0 : meshN (a + 2) τ = 0 :=
            vanish_meshN _ _ _ _ (maxPos_max t τ) (by omega)
          rw [hc0, pow_zero, mul_one]
        rw [Finset.sum_congr rfl htermR, Finset.sum_const,
          fiber_card t u (by simp only [Finset.mem_range] at hu; omega)]
      rw [Finset.sum_eq_card_nsmul hconstR, Finset.card_range]
      simp only [nsmul_eq_mul, Nat.cast_mul, mul_assoc]
    rw [hTotS, hTotR]
    have hC : ((t.succ : ℕ) : Polynomial ℕ) = Polynomial.C (t.succ) := by
      rw [← map_natCast Polynomial.C (t.succ), Nat.cast_id]
    exact aggregate_identity a (t.succ)
      (Finset.univ.filter (fun p : Fin ((t.succ).succ) => ¬ p.val ≤ a)).card
      (Nat.factorial t) (Polynomial.X) (Polynomial.C (t.succ)) hC
      (filter_card_add t a h)

/--
**Stirling-type recursion for the mesh-pattern counting polynomial.** Let $1 < k \le n$ and
$j > 0$. For a permutation $\sigma$ of $m$ elements, with positions numbered $1, \dots, m$, let
$p$ be the position of its largest value and let $N_r(\sigma)$ be the number of positions $i$
such that $\sigma(t) < \sigma(i)$ for all $t < i$ and at least $r - 1$ positions $t$ with
$i < t < p$ have $\sigma(t) > \sigma(i)$, plus $1$ if $p \ge r$. Let $P_{m,r}(X) \in \mathbb{N}[X]$
be the sum of $X^{N_r(\sigma)}$ over all permutations $\sigma$ of $m$ elements, and let
$c_{m,r}(s)$ be its coefficient of $X^s$. Then
$c_{n,k}(j) = (n-1)\,c_{n-1,k}(j) + c_{n-1,k}(j-1)$,
$P_{n,k}(X) = (X + n - 1)\,P_{n-1,k}(X)$, $c_{n,k}(0) = (n-1)\,c_{n-1,k}(0)$, and
$P_{k-1,k}(X) = (k-1)!$.

Source: Matt Davis, "Quadrant Marked Mesh Patterns and the r-Stirling Numbers," Journal
of Integer Sequences 18 (2015), Article 15.10.1, Theorem (label `thm:main`), line 175,
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Davis/davis3.tex>.

Proves `Wanted` entry `meshPatternCount_stirlingRecursion`.
-/
theorem meshPatternCount_stirlingRecursion
    (k n j : ℕ) (hk : 1 < k) (hn : k ≤ n) (hj : 0 < j) :
    let isMeshMatch : {m : ℕ} → ℕ → Equiv.Perm (Fin m) → Fin m → Prop :=
      fun {m} r σ i =>
        ∃ maxIndex : Fin m,
          (∀ t : Fin m, σ t ≤ σ maxIndex) ∧
          r - 1 ≤ (Finset.univ.filter fun t : Fin m =>
            i < t ∧ t < maxIndex ∧ σ i < σ t).card ∧
          ∀ t : Fin m, t < i → σ t < σ i
    let zeroMatches : {m : ℕ} → ℕ → Equiv.Perm (Fin m) → Prop :=
      fun {m} r σ =>
        ∃ maxIndex : Fin m,
          (∀ t : Fin m, σ t ≤ σ maxIndex) ∧ r ≤ maxIndex.val + 1
    let meshCount : {m : ℕ} → ℕ → Equiv.Perm (Fin m) → ℕ :=
      fun {_m} r σ =>
        (Finset.univ.filter (isMeshMatch r σ)).card + if zeroMatches r σ then 1 else 0
    let P : ℕ → ℕ → Polynomial ℕ := fun m r =>
      ∑ σ : Equiv.Perm (Fin m), Polynomial.X ^ meshCount r σ
    let C : ℕ → ℕ → ℕ → ℕ := fun m r s => (P m r).coeff s
    C n k j = (n - 1) * C (n - 1) k j + C (n - 1) k (j - 1) ∧
      P n k = (Polynomial.X + Polynomial.C (n - 1)) * P (n - 1) k ∧
      C n k 0 = (n - 1) * C (n - 1) k 0 ∧
      P (k - 1) k = Polynomial.C (Nat.factorial (k - 1)) := by
  intro isMeshMatch zeroMatches meshCount P C
  have hM : ∀ {m : ℕ} (r : ℕ) (σ : Equiv.Perm (Fin m)) (i : Fin m),
      isMeshMatch r σ i = MatchPred r σ i := fun _ _ _ => rfl
  have hZ : ∀ {m : ℕ} (r : ℕ) (σ : Equiv.Perm (Fin m)),
      zeroMatches r σ = ZeroPred r σ := fun _ _ => rfl
  have hmesh : ∀ {m : ℕ} (r : ℕ) (σ : Equiv.Perm (Fin m)),
      meshCount r σ = meshN r σ := fun _ _ => rfl
  have hP : ∀ (m r : ℕ), P m r = PolyN m r := fun _ _ => rfl
  have hC : ∀ (m r s : ℕ), C m r s = CoefN m r s := fun _ _ _ => rfl
  simp only [hP, hC]
  obtain ⟨m₀, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m₀ ≠ 0)
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ k by omega)
  rw [add_comm (2 : ℕ) a]
  obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hRec : PolyN (t.succ.succ) (a + 2)
      = (Polynomial.X + Polynomial.C (t.succ.succ - 1))
        * PolyN (t.succ.succ - 1) (a + 2) :=
    poly_rec t a (by omega)
  rw [Nat.succ_eq_add_one j', Nat.add_sub_cancel]
  refine ⟨?_, hRec, ?_, base_poly (a + 2) (by omega)⟩
  · unfold CoefN
    rw [hRec, coeff_rec_succ]
    exact add_comm _ _
  · unfold CoefN
    rw [hRec]
    exact coeff_rec_zero _ _

end MetaMathlibExt
end
