/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Matroid.Circuit
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.SymmDiff

/-!
# Shortest augmenting paths for matroid intersection

The directed exchange graph of a common independent set has arcs from inside to outside
for the first matroid, and from outside to inside for the second. Length is the number
of arcs. We minimize over walks between the **two sets** of endpoints; a common endpoint
therefore gives a walk of length zero. A minimizer is simple.

The proof follows fundamental circuits along the path. A later outside vertex is not a
source, and its fundamental circuit cannot use an earlier removed vertex: the corresponding
exchange arc would skip part of the path. Thus each successive exchange preserves independence.
Reversing the walk gives the other matroid's conclusion.

Source: M. X. Goemans, *Advanced Combinatorial Optimization*, MIT 18.438, Lecture 11,
“Matroid Intersection” (22 October 2009, scribe Jacob Steinhardt), Definition 3 (p. 11-3) and the
augmenting-path proof of Theorem 4 (pp. 11-3–11-4; statement on p. 11-2). The lecture uses a unique
matching and a fresh element instead.
-/

@[expose] public section

namespace Matroid.Intersection

open Set
open scoped symmDiff

variable {α : Type*} (M N : Matroid α) (I : Set α)

/-- Outside vertices individually addable in one matroid. -/
def addable : Set α := {x | x ∉ I ∧ M.Indep (insert x I)}

/-- `Exchange M I y x` means that `y ∈ I`, `x ∉ I`, and replacing `y` by `x` in `I` gives
an independent set in `M`. -/
def Exchange (y x : α) : Prop := y ∈ I ∧ x ∉ I ∧ M.Indep (insert x I \ {y})

/-- For `y ∈ I` and `x ∉ I`, the exchange graph has the arc `y → x` if replacing `y` by `x`
gives an independent set in `M`, and the arc `x → y` if it gives an independent set in `N`.
There are no other arcs. -/
def Arc (u v : α) : Prop := Exchange M I u v ∨ Exchange N I v u

/-- The first `n + 1` entries of `p` give a directed walk of `n` arcs; later entries are ignored. -/
def Walk (n : ℕ) (p : ℕ → α) : Prop := ∀ i < n, Arc M N I (p i) (p (i + 1))

/-- A walk from an outside vertex addable in `M` to one addable in `N`. -/
def Joins (n : ℕ) (p : ℕ → α) : Prop :=
  p 0 ∈ addable M I ∧ Walk M N I n p ∧ p n ∈ addable N I

/-- Minimum number of arcs among *all* joining walks, not just those with specified endpoints. -/
def Shortest (n : ℕ) (p : ℕ → α) : Prop :=
  Joins M N I n p ∧ ∀ m q, Joins M N I m q → n ≤ m

/-- The vertex set of an indexed walk, including both endpoints. -/
def vertices (n : ℕ) (p : ℕ → α) : Set α := p '' Iic n

variable {M N I} {n : ℕ} {p : ℕ → α}

private theorem Joins.reverse (h : Joins M N I n p) :
    Joins N M I n (fun i ↦ p (n - i)) := by
  refine ⟨by simpa using h.2.2, ?_, by simpa using h.1⟩
  intro i hi
  have e := (h.2.1 (n - (i + 1)) (by omega)).symm
  rwa [show n - (i + 1) + 1 = n - i by omega] at e

private theorem Shortest.reverse (h : Shortest M N I n p) :
    Shortest N M I n (fun i ↦ p (n - i)) :=
  ⟨h.1.reverse, fun m _ hq ↦ h.2 m _ hq.reverse⟩

private theorem Shortest.not_source (h : Shortest M N I n p) {j : ℕ} (hj : 0 < j) (hjn : j ≤ n) :
    p j ∉ addable M I := by
  intro hs
  have short := h.2 (n - j) (fun t ↦ p (j + t)) ⟨by simpa using hs,
    fun i hi ↦ h.1.2.1 (j + i) (by omega), by simpa [show j + (n - j) = n by omega] using h.1.2.2⟩
  omega

private theorem Shortest.no_chord (h : Shortest M N I n p) {i j : ℕ}
    (hij : i + 1 < j) (hjn : j ≤ n) : ¬ Arc M N I (p i) (p j) := by
  intro e
  let f t := if t ≤ i then t else j + (t - (i + 1))
  let m := i + 1 + (n - j)
  have hzero : f 0 = 0 := by simp [f]
  have hend : f m = n := by dsimp [f, m]; split <;> omega
  have hw : Walk M N I m (fun t ↦ p (f t)) := by
    intro t ht
    by_cases hti : t < i
    · simpa [f, show t ≤ i by omega, show t + 1 ≤ i by omega] using h.1.2.1 t (by omega)
    obtain rfl | hgt := eq_or_lt_of_le (Nat.le_of_not_gt hti)
    · simpa [f] using e
    · have ht' : j + (t - (i + 1)) < n := by dsimp [m] at ht; omega
      simpa only [f, ite_eq_right (show ¬ t ≤ i by omega), ite_eq_right (show ¬ t + 1 ≤ i by omega),
        show j + (t + 1 - (i + 1)) = j + (t - (i + 1)) + 1 by omega] using h.1.2.1 _ ht'
  have short := h.2 m _ ⟨by simpa [hzero] using h.1.1, hw, by simpa [hend] using h.1.2.2⟩
  dsimp [m] at short
  omega

/-- A globally shortest joining walk does not repeat a vertex. -/
theorem Shortest.injOn (h : Shortest M N I n p) : InjOn p (Iic n) := by
  suffices aux : ∀ i j, i < j → j ≤ n → p i ≠ p j by
    intro i hi j hj heq
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact (aux i j hij hj heq).elim
    · rfl
    · exact (aux j i hji hi heq.symm).elim
  rintro (_ | i) j hij hj heq
  · exact h.not_source hij hj (heq ▸ h.1.1)
  · exact h.no_chord hij hj (heq ▸ h.1.2.1 i (by omega))

private theorem vertices_succ (k : ℕ) (p : ℕ → α) :
    vertices (k + 1) p = insert (p (k + 1)) (vertices k p) := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    change t ≤ k + 1 at ht
    obtain h | rfl := lt_or_eq_of_le ht
    · exact Or.inr ⟨t, Nat.le_of_lt_succ h, rfl⟩
    · exact mem_insert ..
  · rintro (rfl | ⟨t, ht, rfl⟩)
    · exact ⟨_, Nat.le_refl _, rfl⟩
    · exact ⟨t, ht.trans (Nat.le_succ _), rfl⟩

private theorem Shortest.fresh (h : Shortest M N I n p) {i j : ℕ} (hij : i < j) (hj : j ≤ n) :
    p j ∉ vertices i p := by
  rintro ⟨t, ht, heq⟩
  change t ≤ i at ht
  have := h.injOn (ht.trans (hij.le.trans hj)) hj heq
  omega

-- Including an inside and an outside vertex in the visited set removes one and inserts the other.
private theorem toggle_pair {I V : Set α} {x y : α} (hx : x ∉ I) (hy : y ∈ I) :
    I ∆ insert x (insert y V) = insert x (I ∆ V) \ {y} := by
  ext z
  simp only [mem_symmDiff, mem_insert_iff, mem_sdiff, mem_singleton_iff]
  grind

-- Transfer the circuit witnessing the exchange from the original set `I` to the current set `J`.
private theorem Shortest.exchange_prefix [Finite α] {i : ℕ} (h : Shortest M N I n p)
    (hk : i + 2 ≤ n) (hI : M.Indep I) (hJ : M.Indep (I ∆ vertices i p))
    (e : Exchange M I (p (i + 1)) (p (i + 2))) :
    M.Indep (I ∆ vertices (i + 2) p) ∧
      (I ∆ vertices (i + 2) p).ncard = (I ∆ vertices i p).ncard := by
  let J := I ∆ vertices i p
  let x := p (i + 2)
  let y := p (i + 1)
  obtain ⟨hy : y ∈ I, hx : x ∉ I, he : M.Indep (insert x I \ {y})⟩ := e
  have hxE : x ∈ M.E := he.subset_ground ⟨mem_insert .., fun hxy ↦ hx (hxy ▸ hy)⟩
  have hcl : x ∈ M.closure I := hI.mem_closure_iff'.2
    ⟨hxE, fun add ↦ (h.not_source (by omega) hk ⟨hx, add⟩).elim⟩
  have hC := hI.fundCircuit_isCircuit hcl hx
  have hyC : y ∈ M.fundCircuit x I := (hI.mem_fundCircuit_iff hcl hx).2 he
  have hsub : M.fundCircuit x I ⊆ insert x J := by
    intro z hz
    obtain rfl | hzI := M.fundCircuit_subset_insert x I hz
    · exact mem_insert ..
    refine Or.inr (Or.inl ⟨hzI, ?_⟩)
    rintro ⟨t, ht, rfl⟩
    change t ≤ i at ht
    exact h.no_chord (i := t) (j := i + 2) (by omega) hk
      (.inl ⟨hzI, hx, (hI.mem_fundCircuit_iff hcl hx).1 hz⟩)
  have fx : x ∉ vertices i p := h.fresh (by omega : i < i + 2) hk
  have fy : y ∉ vertices i p := h.fresh (Nat.lt_succ_self i) (by omega)
  have hxJ : x ∉ J := fun hz ↦ hz.elim (fun hz ↦ hx hz.1) (fun hz ↦ fx hz.1)
  have hyJ : y ∈ J := Or.inl ⟨hy, fy⟩
  have hxclJ : x ∈ M.closure J := hJ.mem_closure_iff'.2
    ⟨hxE, fun add ↦ (hC.not_indep (add.subset hsub)).elim⟩
  rw [hC.eq_fundCircuit_of_subset hJ hsub] at hyC
  rw [vertices_succ (i + 1), vertices_succ i, toggle_pair hx hy]
  refine ⟨(hJ.mem_fundCircuit_iff hxclJ hxJ).1 hyC, ?_⟩
  have hc := ncard_sdiff_singleton_add_one (mem_insert_of_mem x hyJ)
  rw [ncard_insert_of_notMem hxJ] at hc
  exact Nat.add_right_cancel hc

-- The prefix ending at an outside vertex has gained exactly one element in `M`.
private theorem Shortest.prefix [Finite α] (h : Shortest M N I n p) (hI : M.Indep I) (k : ℕ)
    (hk : k ≤ n) (hout : p k ∉ I) :
    M.Indep (I ∆ vertices k p) ∧ (I ∆ vertices k p).ncard = I.ncard + 1 := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    cases k with
    | zero =>
      have hv : vertices 0 p = {p 0} := by
        change p '' Iic (⊥ : ℕ) = _
        rw [Set.Iic_bot, Set.image_singleton, show (⊥ : ℕ) = 0 from rfl]
      have ht : I ∆ vertices 0 p = insert (p 0) I := by
        rw [hv]; ext z; simp only [mem_symmDiff, mem_singleton_iff, mem_insert_iff]; grind
      exact ht ▸ ⟨h.1.1.2, ncard_insert_of_notMem hout⟩
    | succ l =>
      obtain e | er := h.1.2.1 l (by omega)
      · cases l with
        | zero => exact (h.1.1.1 e.1).elim
        | succ i =>
          have hi : p i ∉ I := by
            obtain ef | eb := h.1.2.1 i (by omega)
            · exact (ef.2.1 e.1).elim
            · exact eb.2.1
          obtain ⟨hJ, hc⟩ := ih i (by omega) (by omega) hi
          obtain ⟨hJ', hc'⟩ := h.exchange_prefix hk hI hJ e
          exact ⟨hJ', hc'.trans hc⟩
      · exact (hout er.1).elim

/-- Let `M` and `N` be matroids on a finite type and let `I` be independent in both. Choose a
walk of minimum length among all directed walks from any vertex of `addable M I` to any vertex of
`addable N I`. The symmetric difference of `I` with its vertex set is independent in both matroids
and has cardinality `I.ncard + 1`. A shared endpoint gives a one-vertex walk of length zero. -/
theorem Shortest.augment [Finite α] (h : Shortest M N I n p) (hM : M.Indep I) (hN : N.Indep I) :
    M.Indep (I ∆ vertices n p) ∧ N.Indep (I ∆ vertices n p) ∧
      (I ∆ vertices n p).ncard = I.ncard + 1 := by
  obtain ⟨h₁, hc⟩ := h.prefix hM n le_rfl h.1.2.2.1
  obtain ⟨h₂, -⟩ := h.reverse.prefix hN n le_rfl h.reverse.1.2.2.1
  have hv : vertices n (fun i ↦ p (n - i)) = vertices n p := by
    ext z
    constructor
    · rintro ⟨i, -, rfl⟩; exact ⟨n - i, Nat.sub_le .., rfl⟩
    · rintro ⟨i, hi, rfl⟩
      change i ≤ n at hi
      exact ⟨n - i, Nat.sub_le .., by simp [Nat.sub_sub_self hi]⟩
  exact ⟨h₁, hv ▸ h₂, hc⟩

end Matroid.Intersection
