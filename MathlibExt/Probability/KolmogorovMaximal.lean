/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Kolmogorov maximal inequality

Finite product-space Kolmogorov maximal inequality: decompose the bad event by its
first hitting time, use centered future coordinates to kill the cross term, and identify
the second moment of the total sum with the sum of coordinate second moments.

Primary source: A. Kolmogoroff, "Über die Summen durch den Zufall bestimmter
unabhängiger Größen", Math. Ann. 99 (1928), 309–319, DOI 10.1007/BF01459098.
-/

@[expose] public section

open Finset BigOperators

namespace MathlibExt.Probability.KolmogorovMaximal

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable {n : ℕ}

/-- Product weight of a joint outcome. -/
private noncomputable def weight (p : Fin n → α → ℝ) (ω : Fin n → α) : ℝ :=
  ∏ i, p i (ω i)

/-- Partial sum up to `k` (inclusive). -/
private noncomputable def partialSum (X : Fin n → α → ℝ) (k : Fin n)
    (ω : Fin n → α) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≤ k), X j (ω j)

/-- Total sum over all coordinates. -/
private noncomputable def total (X : Fin n → α → ℝ) (ω : Fin n → α) : ℝ :=
  ∑ j, X j (ω j)

/-- First-hitting set: `|S_k| ≥ lam` and no earlier hit. -/
private noncomputable def firstHit (X : Fin n → α → ℝ) (lam : ℝ) (k : Fin n) :
    Finset (Fin n → α) :=
  Finset.univ.filter
    (fun ω : Fin n → α =>
      |partialSum X k ω| ≥ lam ∧ ∀ j : Fin n, j < k → |partialSum X j ω| < lam)

/-- Bad event: some partial sum exceeds `lam`. Matches the wanted statement. -/
private noncomputable def badSet (X : Fin n → α → ℝ) (lam : ℝ) : Finset (Fin n → α) :=
  Finset.univ.filter
    (fun ω : Fin n → α => ∃ i : Fin n, |partialSum X i ω| ≥ lam)

omit [DecidableEq α] [Nonempty α] in
/-- Sum over a function space of a product splits as a product of sums. -/
private theorem sum_prod_pi (g : Fin n → α → ℝ) :
    (∑ ω : Fin n → α, ∏ i, g i (ω i)) = ∏ i, ∑ a, g i a := by
  simpa [Fintype.piFinset_univ] using
    Finset.sum_prod_piFinset (s := (Finset.univ : Finset α)) (g := g)

/-- A product that is `v` at `k` and `1` elsewhere equals `v`. -/
private theorem single_insert (F : Fin n → ℝ) (k : Fin n) (v : ℝ)
    (hk : F k = v) (h1 : ∀ i, i ≠ k → F i = 1) :
    (∏ i, F i) = v := by
  have h := Finset.prod_eq_single k (fun i _ hi => h1 i hi) (fun h => absurd (Finset.mem_univ k) h)
  rwa [hk] at h

/-- A product with a zero factor is zero. -/
private theorem double_insert (F : Fin n → ℝ) (k : Fin n) (hk : F k = 0) :
    (∏ i, F i) = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_univ k) hk

omit [DecidableEq α] [Nonempty α] in
/-- Variance identity: `E[total²] = ∑ᵢ E[Xᵢ²]`. Diagonal terms give the second
moments; off-diagonal cross terms vanish by independence plus mean zero. -/
private theorem variance_identity
    (p : Fin n → α → ℝ)
    (hp_sum : ∀ i, ∑ a : α, p i a = 1)
    (X : Fin n → α → ℝ)
    (h_mean : ∀ i, ∑ a : α, p i a * X i a = 0) :
    (∑ ω : Fin n → α, weight p ω * (total X ω) ^ 2)
      = ∑ i : Fin n, ∑ a : α, p i a * (X i a) ^ 2 := by
  have hdiag : ∀ i : Fin n,
      (∑ ω : Fin n → α, weight p ω * (X i (ω i) * X i (ω i)))
        = ∑ a : α, p i a * (X i a) ^ 2 := by
    intro i
    set g : Fin n → α → ℝ :=
      fun k a => if k = i then p i a * (X i a) ^ 2 else p k a with hg
    have hpt : ∀ ω : Fin n → α,
      ∏ k, g k (ω k) = weight p ω * (X i (ω i)) ^ 2 := fun ω => by
      have hmem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
      have e1 := (Finset.mul_prod_erase Finset.univ (fun k => g k (ω k)) hmem).symm
      have e2 := (Finset.mul_prod_erase Finset.univ (fun k => p k (ω k)) hmem).symm
      have hcongr : ∏ k ∈ Finset.univ.erase i, g k (ω k)
          = ∏ k ∈ Finset.univ.erase i, p k (ω k) :=
        Finset.prod_congr rfl fun k hk => by simp [hg, (Finset.mem_erase.mp hk).1]
      have hgi : g i (ω i) = p i (ω i) * (X i (ω i)) ^ 2 := by simp [hg]
      rw [show weight p ω = ∏ k, p k (ω k) from rfl, e1, e2, hgi, hcongr]; ring
    have hsum : (∑ ω : Fin n → α, weight p ω * (X i (ω i) * X i (ω i)))
        = ∏ k, ∑ a, g k a := by
      have h1 : (∑ ω : Fin n → α, weight p ω * (X i (ω i) * X i (ω i)))
          = ∑ ω : Fin n → α, ∏ k, g k (ω k) :=
        Finset.sum_congr rfl fun ω _ => by rw [hpt ω]; ring
      rw [h1, sum_prod_pi]
    have hk : (∑ a, g i a) = ∑ a, p i a * (X i a) ^ 2 :=
      Finset.sum_congr rfl fun a _ => by simp [hg]
    have hone : ∀ k, k ≠ i → (∑ a, g k a) = 1 :=
      fun k hki => (Finset.sum_congr rfl fun a _ => by simp [hg, hki]).trans (hp_sum k)
    exact hsum.trans (single_insert _ i _ hk hone)
  have hoff : ∀ i j : Fin n, i ≠ j →
      (∑ ω : Fin n → α, weight p ω * (X i (ω i) * X j (ω j))) = 0 := by
    intro i j hij
    have hji : j ≠ i := Ne.symm hij
    set g : Fin n → α → ℝ := fun k a =>
      if k = i then p i a * X i a else if k = j then p j a * X j a else p k a with hg
    have hpt : ∀ ω : Fin n → α,
      ∏ k, g k (ω k) = weight p ω * (X i (ω i) * X j (ω j)) := fun ω => by
      have hmem_i : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
      have hmem_j : j ∈ (Finset.univ : Finset (Fin n)).erase i :=
        Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
      have e1 := (Finset.mul_prod_erase Finset.univ (fun k => g k (ω k)) hmem_i).symm
      have e1b := (Finset.mul_prod_erase (Finset.univ.erase i) (fun k => g k (ω k)) hmem_j).symm
      have e2 := (Finset.mul_prod_erase Finset.univ (fun k => p k (ω k)) hmem_i).symm
      have e2b := (Finset.mul_prod_erase (Finset.univ.erase i) (fun k => p k (ω k)) hmem_j).symm
      have hcongr : ∏ k ∈ (Finset.univ.erase i).erase j, g k (ω k)
          = ∏ k ∈ (Finset.univ.erase i).erase j, p k (ω k) := by
        refine Finset.prod_congr rfl fun k hk => ?_
        simp only [Finset.mem_erase] at hk
        obtain ⟨hkj, hki, -⟩ := hk
        simp [hg, hki, hkj]
      have hgi : g i (ω i) = p i (ω i) * X i (ω i) := by simp [hg]
      have hgj : g j (ω j) = p j (ω j) * X j (ω j) := by simp [hg, hji]
      rw [show weight p ω = ∏ k, p k (ω k) from rfl, e1, e1b, e2, e2b, hgi, hgj, hcongr]; ring
    have hsum : (∑ ω : Fin n → α, weight p ω * (X i (ω i) * X j (ω j)))
        = ∏ k, ∑ a, g k a := by
      have h1 : (∑ ω : Fin n → α, weight p ω * (X i (ω i) * X j (ω j)))
          = ∑ ω : Fin n → α, ∏ k, g k (ω k) :=
        Finset.sum_congr rfl fun ω _ => (hpt ω).symm
      rw [h1, sum_prod_pi]
    rw [hsum]
    exact double_insert _ i ((Finset.sum_congr rfl fun a _ => by simp [hg]).trans (h_mean i))
  have hsq : ∀ ω : Fin n → α, (total X ω) ^ 2
      = ∑ i : Fin n, ∑ j : Fin n, X i (ω i) * X j (ω j) :=
    fun ω => by
      rw [pow_two, show total X ω = ∑ j, X j (ω j) from rfl]
      exact Fintype.sum_mul_sum _ _
  have hLHS : (∑ ω : Fin n → α, weight p ω * (total X ω) ^ 2)
      = ∑ i : Fin n, ∑ j : Fin n, ∑ ω : Fin n → α,
        weight p ω * (X i (ω i) * X j (ω j)) := by
    have h1 : (∑ ω : Fin n → α, weight p ω * (total X ω) ^ 2)
        = ∑ ω : Fin n → α, ∑ i : Fin n, ∑ j : Fin n,
          weight p ω * (X i (ω i) * X j (ω j)) :=
      Finset.sum_congr rfl fun ω _ => by
        rw [hsq ω, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    rw [h1, Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [hLHS]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin n)), j ≠ i →
      (∑ ω : Fin n → α, weight p ω * (X i (ω i) * X j (ω j))) = 0 :=
    fun j _ hji => hoff i j (Ne.symm hji)
  exact (Finset.sum_eq_single i h0 (fun h => absurd (Finset.mem_univ i) h)).trans (hdiag i)

omit [DecidableEq α] [Nonempty α] in
/-- Distinct first-hitting sets are disjoint: `ω` cannot first hit at two places. -/
private theorem firstHit_disjoint (X : Fin n → α → ℝ) (lam : ℝ) (k₁ k₂ : Fin n)
    (h : k₁ ≠ k₂) : Disjoint (firstHit X lam k₁) (firstHit X lam k₂) := by
  rw [Finset.disjoint_left]
  intro ω h1 h2
  simp only [firstHit, Finset.mem_filter] at h1 h2
  obtain ⟨_, hge1, hfirst1⟩ := h1
  obtain ⟨_, hge2, hfirst2⟩ := h2
  rcases lt_trichotomy k₁ k₂ with hlt | heq | hgt
  · exact absurd hge1 (not_le_of_gt (hfirst2 k₁ hlt))
  · exact h heq
  · exact absurd hge2 (not_le_of_gt (hfirst1 k₂ hgt))

omit [Nonempty α] in
/-- The bad event is the union of the first-hitting sets, via the least hitting index. -/
private theorem badSet_eq_biUnion (X : Fin n → α → ℝ) (lam : ℝ) :
    badSet X lam = Finset.univ.biUnion (fun k => firstHit X lam k) := by
  apply Finset.Subset.antisymm
  · intro ω hω
    rw [badSet, Finset.mem_filter] at hω
    obtain ⟨_, i, hi⟩ := hω
    set S : Finset (Fin n) :=
      Finset.univ.filter (fun i : Fin n => |partialSum X i ω| ≥ lam) with hS
    have hmem : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
    have hne : S.Nonempty := ⟨i, hmem⟩
    set k₀ : Fin n := S.min' hne with hk₀
    have hk₀ge : |partialSum X k₀ ω| ≥ lam :=
      (Finset.mem_filter.mp (Finset.min'_mem S hne)).2
    have hfirst : ∀ j : Fin n, j < k₀ → |partialSum X j ω| < lam := by
      intro j hlt
      rcases lt_or_ge (|partialSum X j ω|) lam with h | h
      · exact h
      · have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩
        exact absurd (Finset.min'_le S j hjS) (not_le_of_gt hlt)
    rw [Finset.mem_biUnion]
    refine ⟨k₀, Finset.mem_univ k₀, ?_⟩
    rw [firstHit, Finset.mem_filter]
    exact ⟨Finset.mem_univ ω, hk₀ge, hfirst⟩
  · intro ω hω
    rw [Finset.mem_biUnion] at hω
    obtain ⟨k, _, hk⟩ := hω
    simp only [firstHit, Finset.mem_filter] at hk
    obtain ⟨-, hkge, -⟩ := hk
    rw [badSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ ω, k, hkge⟩

omit [DecidableEq α] [Nonempty α] in
/-- `sum_prod_pi` generalized to any finite index type (e.g. the future subtype). -/
private theorem sum_prod_pi_subtype (ι : Type*) [Fintype ι] [DecidableEq ι]
    (g : ι → α → ℝ) :
    (∑ ω : ι → α, ∏ i, g i (ω i)) = ∏ i, ∑ a, g i a := by
  simpa [Fintype.piFinset_univ] using
    Finset.sum_prod_piFinset (s := (Finset.univ : Finset α)) (g := g)

/-- Past/future splitting equivalence at `k`. -/
private noncomputable def splitEquiv (k : Fin n) :
    (Fin n → α) ≃ ({j : Fin n // j ≤ k} → α) × ({j : Fin n // ¬ j ≤ k} → α) :=
  Equiv.piEquivPiSubtypeProd (fun j : Fin n => j ≤ k) (fun _ => α)

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The splitting equivalence is the past on past coordinates. -/
private theorem e_symm_past (k : Fin n)
    (u : {j : Fin n // j ≤ k} → α) (v : {j : Fin n // ¬ j ≤ k} → α)
    (j : {j : Fin n // j ≤ k}) :
    (splitEquiv k).symm (u, v) j.1 = u j := by
  exact dite_eq_left j.2

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The splitting equivalence is the future on future coordinates. -/
private theorem e_symm_fut (k : Fin n)
    (u : {j : Fin n // j ≤ k} → α) (v : {j : Fin n // ¬ j ≤ k} → α)
    (j : {j : Fin n // ¬ j ≤ k}) :
    (splitEquiv k).symm (u, v) j.1 = v j := by
  exact dite_eq_right j.2

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The weight splits as past-weight times future-weight. -/
private theorem weight_split (p : Fin n → α → ℝ) (k : Fin n)
    (u : {j : Fin n // j ≤ k} → α) (v : {j : Fin n // ¬ j ≤ k} → α) :
    weight p ((splitEquiv k).symm (u, v))
      = (∏ j : {j : Fin n // j ≤ k}, p ↑j (u j))
        * (∏ j : {j : Fin n // ¬ j ≤ k}, p ↑j (v j)) := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin n))
    (fun j => j ≤ k) (fun j => p j (((splitEquiv k).symm (u, v)) j))
  have hpast : (∏ j : {j : Fin n // j ≤ k}, p ↑j (u j))
      = ∏ j ∈ (Finset.univ : Finset (Fin n)).filter (fun j => j ≤ k),
        p j (((splitEquiv k).symm (u, v)) j) :=
    Finset.prod_bij (fun j _ => j.1) (fun j _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩)
      (fun j₁ _ j₂ _ h => Subtype.ext h)
      (fun j hj => ⟨⟨j, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, rfl⟩)
      (fun j _ => by rw [e_symm_past k u v j])
  have hfut : (∏ j : {j : Fin n // ¬ j ≤ k}, p ↑j (v j))
      = ∏ j ∈ (Finset.univ : Finset (Fin n)).filter (fun j => ¬ j ≤ k),
        p j (((splitEquiv k).symm (u, v)) j) :=
    Finset.prod_bij (fun j _ => j.1) (fun j _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩)
      (fun j₁ _ j₂ _ h => Subtype.ext h)
      (fun j hj => ⟨⟨j, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, rfl⟩)
      (fun j _ => by rw [e_symm_fut k u v j])
  have hwrw : weight p ((splitEquiv k).symm (u, v))
      = ∏ j ∈ (Finset.univ : Finset (Fin n)),
        p j (((splitEquiv k).symm (u, v)) j) := rfl
  rw [hwrw, hpast, hfut]
  exact hsplit.symm

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The partial sum at `k` depends only on past coordinates. -/
private theorem partialSum_split (X : Fin n → α → ℝ) (k : Fin n)
    (u : {j : Fin n // j ≤ k} → α) (v : {j : Fin n // ¬ j ≤ k} → α) :
    partialSum X k ((splitEquiv k).symm (u, v))
      = ∑ j : {j : Fin n // j ≤ k}, X ↑j (u j) := by
  have h : (∑ j : {j : Fin n // j ≤ k}, X ↑j (u j))
      = ∑ j ∈ (Finset.univ : Finset (Fin n)).filter (fun j => j ≤ k),
        X j (((splitEquiv k).symm (u, v)) j) :=
    Finset.sum_bij (fun j _ => j.1) (fun j _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩)
      (fun j₁ _ j₂ _ h => Subtype.ext h)
      (fun j hj => ⟨⟨j, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, rfl⟩)
      (fun j _ => by rw [e_symm_past k u v j])
  have hprw : partialSum X k ((splitEquiv k).symm (u, v))
      = ∑ j ∈ (Finset.univ : Finset (Fin n)).filter (fun j => j ≤ k),
        X j (((splitEquiv k).symm (u, v)) j) := rfl
  rw [hprw]
  exact h.symm

/-- Future sum after `k`. -/
private noncomputable def remainder (X : Fin n → α → ℝ) (k : Fin n)
    (ω : Fin n → α) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j ≤ k), X j (ω j)

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The total is past plus future. -/
private theorem total_eq_partialSum_add_remainder (X : Fin n → α → ℝ) (k : Fin n)
    (ω : Fin n → α) :
    total X ω = partialSum X k ω + remainder X k ω :=
  (Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ≤ k) (fun j => X j (ω j))).symm

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The remainder depends only on future coordinates. -/
private theorem remainder_split (X : Fin n → α → ℝ) (k : Fin n)
    (u : {j : Fin n // j ≤ k} → α) (v : {j : Fin n // ¬ j ≤ k} → α) :
    remainder X k ((splitEquiv k).symm (u, v))
      = ∑ j : {j : Fin n // ¬ j ≤ k}, X ↑j (v j) := by
  have h : (∑ j : {j : Fin n // ¬ j ≤ k}, X ↑j (v j))
      = ∑ j ∈ (Finset.univ : Finset (Fin n)).filter (fun j => ¬ j ≤ k),
        X j (((splitEquiv k).symm (u, v)) j) :=
    Finset.sum_bij (fun j _ => j.1) (fun j _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩)
      (fun j₁ _ j₂ _ h => Subtype.ext h)
      (fun j hj => ⟨⟨j, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, rfl⟩)
      (fun j _ => by rw [e_symm_fut k u v j])
  have hrrw : remainder X k ((splitEquiv k).symm (u, v))
      = ∑ j ∈ (Finset.univ : Finset (Fin n)).filter (fun j => ¬ j ≤ k),
        X j (((splitEquiv k).symm (u, v)) j) := rfl
  rw [hrrw]
  exact h.symm

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- Partial sums at indices `≤ k` see only the past component. -/
private theorem partialSum_le_past (X : Fin n → α → ℝ) (k : Fin n) (j' : Fin n)
    (hj' : j' ≤ k) (u : {j : Fin n // j ≤ k} → α)
    (v v' : {j : Fin n // ¬ j ≤ k} → α) :
    partialSum X j' ((splitEquiv k).symm (u, v))
      = partialSum X j' ((splitEquiv k).symm (u, v')) := by
  have hsum : ∀ ω ω' : Fin n → α, (∀ j : Fin n, j ≤ j' → ω j = ω' j) →
      partialSum X j' ω = partialSum X j' ω' :=
    fun ω ω' hEq => by
      unfold partialSum
      exact Finset.sum_congr rfl fun j hj => by rw [hEq j (Finset.mem_filter.mp hj).2]
  exact hsum _ _ fun j hj => by
    have hjk : j ≤ k := le_trans hj hj'
    rw [e_symm_past k u v ⟨j, hjk⟩, e_symm_past k u v' ⟨j, hjk⟩]

omit [DecidableEq α] [Nonempty α] in
/-- First-hit membership is determined by the past component. -/
private theorem mem_firstHit_past (X : Fin n → α → ℝ) (lam : ℝ) (k : Fin n)
    (u : {j : Fin n // j ≤ k} → α) (v v' : {j : Fin n // ¬ j ≤ k} → α) :
    ((splitEquiv k).symm (u, v) ∈ firstHit X lam k)
      ↔ ((splitEquiv k).symm (u, v') ∈ firstHit X lam k) := by
  have h : ∀ j' : Fin n, j' ≤ k →
      partialSum X j' ((splitEquiv k).symm (u, v))
        = partialSum X j' ((splitEquiv k).symm (u, v')) :=
    fun j' hj' => partialSum_le_past X k j' hj' u v v'
  simp only [firstHit, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hge, hf⟩
    refine ⟨?_, ?_⟩
    · rwa [← h k le_rfl]
    · intro j' hj'; rw [← h j' (le_of_lt hj')]; exact hf j' hj'
  · rintro ⟨hge, hf⟩
    refine ⟨?_, ?_⟩
    · rwa [h k le_rfl]
    · intro j' hj'; rw [h j' (le_of_lt hj')]; exact hf j' hj'

/-- Past-coordinate first-hitting set. -/
private noncomputable def pastHit (X : Fin n → α → ℝ) (lam : ℝ) (k : Fin n) :
    Finset ({j : Fin n // j ≤ k} → α) := by
  classical
  exact Finset.univ.filter
    (fun u => ∃ v : {j : Fin n // ¬ j ≤ k} → α,
      (splitEquiv k).symm (u, v) ∈ firstHit X lam k)

omit [Nonempty α] in
/-- The first-hitting set is the split image of past-hits times all futures. -/
private theorem firstHit_eq_map (X : Fin n → α → ℝ) (lam : ℝ) (k : Fin n) :
    firstHit X lam k
      = (pastHit X lam k ×ˢ (Finset.univ : Finset ({j : Fin n // ¬ j ≤ k} → α))).map
        (splitEquiv k).symm.toEmbedding := by
  apply Finset.Subset.antisymm
  · intro ω hω
    have hω' : ω = (splitEquiv k).symm ((splitEquiv k) ω) :=
      ((splitEquiv k).symm_apply_apply ω).symm
    rw [hω', Finset.mem_map]
    refine ⟨(((splitEquiv k) ω).1, ((splitEquiv k) ω).2), ?_, rfl⟩
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [pastHit, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ((splitEquiv k) ω).2, ?_⟩
    rwa [(splitEquiv k).symm_apply_apply ω]
  · intro ω hω
    rw [Finset.mem_map] at hω
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := hω
    obtain ⟨hu, -⟩ := Finset.mem_product.mp huv
    obtain ⟨-, v', hv'⟩ := Finset.mem_filter.mp hu
    exact (mem_firstHit_past X lam k u v' v).mp hv'

omit [Nonempty α] in
/-- Reindex a sum over `firstHit k` as a double sum over past times future. -/
private theorem sum_firstHit_eq (X : Fin n → α → ℝ) (lam : ℝ) (k : Fin n)
    (f : (Fin n → α) → ℝ) :
    ∑ ω ∈ firstHit X lam k, f ω
      = ∑ u ∈ pastHit X lam k, ∑ v : {j : Fin n // ¬ j ≤ k} → α,
        f ((splitEquiv k).symm (u, v)) := by
  rw [firstHit_eq_map, Finset.sum_map, Finset.sum_product]
  exact rfl

omit [DecidableEq α] [Nonempty α] in
/-- Future mean zero: a future coordinate has zero mean under the future weight. -/
private theorem sum_fut_weight_mul_coord (p : Fin n → α → ℝ)
    (_hp_sum : ∀ i, ∑ a : α, p i a = 1)
    (X : Fin n → α → ℝ)
    (h_mean : ∀ i, ∑ a : α, p i a * X i a = 0)
    (k : Fin n) (j₀ : {j : Fin n // ¬ j ≤ k}) :
    (∑ v : {j : Fin n // ¬ j ≤ k} → α,
        (∏ j : {j : Fin n // ¬ j ≤ k}, p ↑j (v j)) * (X ↑j₀ (v j₀))) = 0 := by
  set g : {j : Fin n // ¬ j ≤ k} → α → ℝ :=
    fun j a => if j = j₀ then p ↑j a * X ↑j a else p ↑j a with hg
  have hpt : ∀ v : {j : Fin n // ¬ j ≤ k} → α,
      ∏ j, g j (v j)
        = (∏ j : {j : Fin n // ¬ j ≤ k}, p ↑j (v j)) * (X ↑j₀ (v j₀)) := fun v => by
    have hmem : j₀ ∈ (Finset.univ : Finset {j : Fin n // ¬ j ≤ k}) := Finset.mem_univ j₀
    have e1 := (Finset.mul_prod_erase
      (Finset.univ : Finset {j : Fin n // ¬ j ≤ k})
      (fun j => g j (v j)) hmem).symm
    have e2 := (Finset.mul_prod_erase
      (Finset.univ : Finset {j : Fin n // ¬ j ≤ k})
      (fun j => p ↑j (v j)) hmem).symm
    have hcongr : ∏ j ∈ (Finset.univ : Finset {j : Fin n // ¬ j ≤ k}).erase j₀, g j (v j)
        = ∏ j ∈ (Finset.univ : Finset {j : Fin n // ¬ j ≤ k}).erase j₀, p ↑j (v j) :=
      Finset.prod_congr rfl fun j hj => by simp [hg, (Finset.mem_erase.mp hj).1]
    have hgj : g j₀ (v j₀) = p ↑j₀ (v j₀) * X ↑j₀ (v j₀) := by simp [hg]
    rw [e1, e2, hgj, hcongr]; ring
  have hsum : (∑ v : {j : Fin n // ¬ j ≤ k} → α,
      (∏ j : {j : Fin n // ¬ j ≤ k}, p ↑j (v j)) * (X ↑j₀ (v j₀)))
      = ∏ j : {j : Fin n // ¬ j ≤ k}, ∑ a, g j a := by
    have h1 : (∑ v : {j : Fin n // ¬ j ≤ k} → α,
        (∏ j : {j : Fin n // ¬ j ≤ k}, p ↑j (v j)) * (X ↑j₀ (v j₀)))
        = ∑ v : {j : Fin n // ¬ j ≤ k} → α, ∏ j, g j (v j) :=
      Finset.sum_congr rfl fun v _ => (hpt v).symm
    rw [h1]; exact sum_prod_pi_subtype _ g
  rw [hsum]
  exact Finset.prod_eq_zero (Finset.mem_univ j₀)
    ((Finset.sum_congr rfl fun a _ => by simp [hg]).trans (h_mean ↑j₀))

omit [DecidableEq α] [Nonempty α] in
/-- Cross term vanishes: the mixed partial-sum/remainder sum over each first-hit set is zero. -/
private theorem cross_term_zero
    (p : Fin n → α → ℝ)
    (hp_sum : ∀ i, ∑ a : α, p i a = 1)
    (X : Fin n → α → ℝ)
    (h_mean : ∀ i, ∑ a : α, p i a * X i a = 0)
    (lam : ℝ) (k : Fin n) :
    (∑ ω ∈ firstHit X lam k, weight p ω * (partialSum X k ω * remainder X k ω)) = 0 := by
  classical
  rw [sum_firstHit_eq X lam k]
  refine Finset.sum_eq_zero fun u _ => ?_
  have hfac : ∀ v : {j : Fin n // ¬ j ≤ k} → α,
      weight p ((splitEquiv k).symm (u, v)) *
        (partialSum X k ((splitEquiv k).symm (u, v)) * remainder X k ((splitEquiv k).symm (u, v)))
      = ((∏ j : {j : Fin n // j ≤ k}, p ↑j (u j))
          * (∑ j : {j : Fin n // j ≤ k}, X ↑j (u j))) *
        ((∏ j : {j : Fin n // ¬ j ≤ k}, p ↑j (v j))
          * (∑ j : {j : Fin n // ¬ j ≤ k}, X ↑j (v j))) :=
    fun v => by
      rw [weight_split p k u v, partialSum_split X k u v,
        remainder_split X k u v]
      ring
  have hexpand : ∀ v : {j : Fin n // ¬ j ≤ k} → α,
      (∏ j : {j : Fin n // ¬ j ≤ k}, p ↑j (v j))
          * (∑ j : {j : Fin n // ¬ j ≤ k}, X ↑j (v j))
      = ∑ j : {j : Fin n // ¬ j ≤ k},
        (∏ j' : {j : Fin n // ¬ j ≤ k}, p ↑j' (v j')) * X ↑j (v j) :=
    fun v => by rw [Finset.mul_sum]
  have hfut : (∑ v : {j : Fin n // ¬ j ≤ k} → α,
      (∏ j : {j : Fin n // ¬ j ≤ k}, p ↑j (v j))
        * (∑ j : {j : Fin n // ¬ j ≤ k}, X ↑j (v j))) = 0 := by
    rw [Finset.sum_congr rfl (fun v _ => hexpand v), Finset.sum_comm]
    exact Finset.sum_eq_zero fun j₀ _ => sum_fut_weight_mul_coord p hp_sum X h_mean k j₀
  have hsum : (∑ v : {j : Fin n // ¬ j ≤ k} → α,
      weight p ((splitEquiv k).symm (u, v)) *
        (partialSum X k ((splitEquiv k).symm (u, v)) *
          remainder X k ((splitEquiv k).symm (u, v))))
      = ((∏ j : {j : Fin n // j ≤ k}, p ↑j (u j))
          * (∑ j : {j : Fin n // j ≤ k}, X ↑j (u j))) *
        (∑ v : {j : Fin n // ¬ j ≤ k} → α,
          (∏ j : {j : Fin n // ¬ j ≤ k}, p ↑j (v j))
            * (∑ j : {j : Fin n // ¬ j ≤ k}, X ↑j (v j))) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => hfac v
  rw [hsum, hfut, mul_zero]

omit [DecidableEq α] [Nonempty α] in
/-- Per-k estimate: `lam² * P(first hit at k) ≤ E[total² * 1_{first hit at k}]`. -/
private theorem per_k_estimate
    (p : Fin n → α → ℝ)
    (hp_nonneg : ∀ i a, 0 ≤ p i a)
    (hp_sum : ∀ i, ∑ a : α, p i a = 1)
    (X : Fin n → α → ℝ)
    (h_mean : ∀ i, ∑ a : α, p i a * X i a = 0)
    (lam : ℝ) (hlam : 0 < lam) (k : Fin n) :
    lam ^ 2 * (∑ ω ∈ firstHit X lam k, weight p ω)
      ≤ ∑ ω ∈ firstHit X lam k, weight p ω * (total X ω) ^ 2 := by
  have hw_nonneg : ∀ ω ∈ firstHit X lam k, 0 ≤ weight p ω :=
    fun ω _ => by unfold weight; exact Finset.prod_nonneg fun i _ => hp_nonneg i (ω i)
  have hsq : ∀ ω ∈ firstHit X lam k, lam ^ 2 ≤ (partialSum X k ω) ^ 2 := by
    intro ω hω
    simp only [firstHit, Finset.mem_filter] at hω
    obtain ⟨-, hge, -⟩ := hω
    have h1 : lam ≤ |partialSum X k ω| := hge
    have h2 : -|partialSum X k ω| ≤ lam := le_trans (neg_nonpos.mpr (abs_nonneg _)) hlam.le
    have h3 : lam ^ 2 ≤ |partialSum X k ω| ^ 2 := sq_le_sq' h2 h1
    rwa [sq_abs] at h3
  have hpt : ∀ ω ∈ firstHit X lam k,
      lam ^ 2 * weight p ω ≤ weight p ω * (partialSum X k ω) ^ 2 :=
    fun ω hω => by
      rw [mul_comm (lam ^ 2) _]
      exact mul_le_mul_of_nonneg_left (hsq ω hω) (hw_nonneg ω hω)
  have hsum1 : lam ^ 2 * (∑ ω ∈ firstHit X lam k, weight p ω)
      ≤ ∑ ω ∈ firstHit X lam k, weight p ω * (partialSum X k ω) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun ω hω => hpt ω hω
  have hexpand : ∀ ω : Fin n → α, weight p ω * (total X ω) ^ 2
      = weight p ω * (partialSum X k ω) ^ 2
        + weight p ω * (2 * (partialSum X k ω * remainder X k ω))
        + weight p ω * (remainder X k ω) ^ 2 :=
    fun ω => by rw [total_eq_partialSum_add_remainder X k ω]; ring
  have hsum2 : (∑ ω ∈ firstHit X lam k, weight p ω * (total X ω) ^ 2)
      = (∑ ω ∈ firstHit X lam k, weight p ω * (partialSum X k ω) ^ 2)
        + (∑ ω ∈ firstHit X lam k, weight p ω * (2 * (partialSum X k ω * remainder X k ω)))
        + (∑ ω ∈ firstHit X lam k, weight p ω * (remainder X k ω) ^ 2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ω _ => hexpand ω
  have hcross2 : (∑ ω ∈ firstHit X lam k,
      weight p ω * (2 * (partialSum X k ω * remainder X k ω))) = 0 := by
    have hfactor : (∑ ω ∈ firstHit X lam k,
        weight p ω * (2 * (partialSum X k ω * remainder X k ω)))
        = 2 * (∑ ω ∈ firstHit X lam k,
          weight p ω * (partialSum X k ω * remainder X k ω)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ω _ => by ring
    rw [hfactor, cross_term_zero p hp_sum X h_mean lam k, mul_zero]
  have hrem_nonneg : 0 ≤ ∑ ω ∈ firstHit X lam k, weight p ω * (remainder X k ω) ^ 2 :=
    Finset.sum_nonneg fun ω hω => mul_nonneg (hw_nonneg ω hω) (sq_nonneg _)
  have hsum3 : (∑ ω ∈ firstHit X lam k, weight p ω * (partialSum X k ω) ^ 2)
      ≤ ∑ ω ∈ firstHit X lam k, weight p ω * (total X ω) ^ 2 := by
    rw [hsum2, hcross2, add_zero]; exact le_add_of_nonneg_right hrem_nonneg
  exact le_trans hsum1 hsum3

/-- **Kolmogorov's maximal inequality for finitely-valued variables.** Let $\alpha$ be a finite
nonempty set and $n \in \mathbb{N}$. For each $i \in \{0, \dots, n-1\}$ let $p_i$ be a probability
vector on $\alpha$, so $p_i(a) \ge 0$ and $\sum_{a \in \alpha} p_i(a) = 1$, and let
$X_i : \alpha \to \mathbb{R}$ satisfy $\sum_{a \in \alpha} p_i(a) X_i(a) = 0$. Give each
$\omega \in \alpha^n$ the weight $\prod_{i=0}^{n-1} p_i(\omega_i)$, so that the coordinates are
independent with laws $p_i$. Then for every real $\lambda > 0$, the total weight of the $\omega$
for which $\bigl|\sum_{j \le i} X_j(\omega_j)\bigr| \ge \lambda$ for some $i$ is at most
$\lambda^{-2} \sum_{i=0}^{n-1} \sum_{a \in \alpha} p_i(a) X_i(a)^2$.

Source: A. Kolmogoroff, "Über die Summen durch den Zufall bestimmter
unabhängiger Größen", Math. Ann. 99 (1928), 309–319, DOI 10.1007/BF01459098. -/
public theorem kolmogorov_maximal_inequality
    {α : Type*} [Fintype α] [Nonempty α]
    {n : ℕ}
    (p : Fin n → α → ℝ)
    (hp_nonneg : ∀ i a, 0 ≤ p i a)
    (hp_sum : ∀ i, ∑ a : α, p i a = 1)
    (X : Fin n → α → ℝ)
    (h_mean : ∀ i, ∑ a : α, p i a * X i a = 0)
    (lam : ℝ) (hlam : 0 < lam) :
    (∑ ω ∈ Finset.univ.filter
        (fun ω : Fin n → α =>
          ∃ i : Fin n,
            |∑ j ∈ Finset.univ.filter
                (fun j : Fin n => j ≤ i), X j (ω j)| ≥ lam),
      ∏ i : Fin n, p i (ω i))
    ≤ (∑ i : Fin n, ∑ a : α, p i a * (X i a) ^ 2) / lam ^ 2 := by
  classical
  have _ne : Nonempty α := inferInstance
  change (∑ ω ∈ badSet X lam, weight p ω) ≤ _
  rw [badSet_eq_biUnion X lam]
  have hdisj : ∀ k₁ ∈ (Finset.univ : Finset (Fin n)),
      ∀ k₂ ∈ (Finset.univ : Finset (Fin n)),
      k₁ ≠ k₂ → Disjoint (firstHit X lam k₁) (firstHit X lam k₂) :=
    fun k₁ _ k₂ _ h => firstHit_disjoint X lam k₁ k₂ h
  rw [Finset.sum_biUnion hdisj]
  have hlam2 : 0 < lam ^ 2 := pow_pos hlam 2
  rw [le_div_iff₀ hlam2]
  have hper : ∀ k ∈ (Finset.univ : Finset (Fin n)),
      lam ^ 2 * (∑ ω ∈ firstHit X lam k, weight p ω)
        ≤ ∑ ω ∈ firstHit X lam k, weight p ω * (total X ω) ^ 2 :=
    fun k _ => per_k_estimate p hp_nonneg hp_sum X h_mean lam hlam k
  have hsum_le : lam ^ 2 *
      (∑ k ∈ (Finset.univ : Finset (Fin n)),
        ∑ ω ∈ firstHit X lam k, weight p ω)
      ≤ ∑ k ∈ (Finset.univ : Finset (Fin n)),
        ∑ ω ∈ firstHit X lam k, weight p ω * (total X ω) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun k hk => hper k hk
  have hbi : (∑ k ∈ (Finset.univ : Finset (Fin n)),
      ∑ ω ∈ firstHit X lam k, weight p ω * (total X ω) ^ 2)
      = ∑ ω ∈ (Finset.univ : Finset (Fin n)).biUnion (fun k => firstHit X lam k),
        weight p ω * (total X ω) ^ 2 :=
    (Finset.sum_biUnion hdisj).symm
  have hsub : (Finset.univ : Finset (Fin n)).biUnion (fun k => firstHit X lam k) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hnonneg : ∀ ω ∈ (Finset.univ : Finset (Fin n → α)),
      0 ≤ weight p ω * (total X ω) ^ 2 :=
    fun ω _ => mul_nonneg
      (by
        unfold weight
        exact Finset.prod_nonneg fun i _ => hp_nonneg i (ω i))
      (sq_nonneg _)
  have hle_univ : (∑ ω ∈ (Finset.univ : Finset (Fin n)).biUnion (fun k => firstHit X lam k),
        weight p ω * (total X ω) ^ 2)
      ≤ ∑ ω : Fin n → α, weight p ω * (total X ω) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun ω _ _ => hnonneg ω (Finset.mem_univ ω)
  have hvar : (∑ ω : Fin n → α, weight p ω * (total X ω) ^ 2)
      = ∑ i : Fin n, ∑ a : α, p i a * (X i a) ^ 2 :=
    variance_identity p hp_sum X h_mean
  calc (∑ k ∈ (Finset.univ : Finset (Fin n)),
        ∑ ω ∈ firstHit X lam k, weight p ω) * lam ^ 2
      = lam ^ 2 * (∑ k ∈ (Finset.univ : Finset (Fin n)),
        ∑ ω ∈ firstHit X lam k, weight p ω) := mul_comm _ _
    _ ≤ ∑ k ∈ (Finset.univ : Finset (Fin n)),
        ∑ ω ∈ firstHit X lam k, weight p ω * (total X ω) ^ 2 := hsum_le
    _ = ∑ ω ∈ (Finset.univ : Finset (Fin n)).biUnion
        (fun k => firstHit X lam k),
      weight p ω * (total X ω) ^ 2 := hbi
    _ ≤ ∑ ω : Fin n → α, weight p ω * (total X ω) ^ 2 := hle_univ
    _ = ∑ i : Fin n, ∑ a : α, p i a * (X i a) ^ 2 := hvar

end MathlibExt.Probability.KolmogorovMaximal
