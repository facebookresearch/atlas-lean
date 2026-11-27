/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import MathlibExt.Combinatorics.SimpleGraph.MatrixTree
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

/-!
# Cayley's formula

The complete graph on `n` vertices has `n^(n-2)` spanning trees.
-/

/-! ## Helpers -/

/-- Rooted forests on `U` with root set `R`, as parent maps `f : α → α`.
(a) `f` fixes everything outside `U \ R`; (b) `f` maps `U \ R` into `U`;
(c) a rank function strictly decreases along `f` on `U \ R` (acyclicity). -/
private noncomputable def acyclicMaps {α : Type*} [Fintype α] [DecidableEq α]
    (U R : Finset α) : Finset (α → α) := by
  classical
  exact Finset.univ.filter fun f : α → α =>
    ((∀ x : α, x ∉ U \ R → f x = x) ∧
     (∀ x : α, x ∈ U \ R → f x ∈ U) ∧
     (∃ h : α → ℕ, ∀ x : α, x ∈ U \ R → h (f x) < h x))

/-- Membership in `acyclicMaps`. -/
private theorem mem_acyclicMaps {α : Type*} [Fintype α] [DecidableEq α]
    {U R : Finset α} {f : α → α} :
    f ∈ acyclicMaps U R ↔
      ((∀ x : α, x ∉ U \ R → f x = x) ∧
       (∀ x : α, x ∈ U \ R → f x ∈ U) ∧
       (∃ h : α → ℕ, ∀ x : α, x ∈ U \ R → h (f x) < h x)) := by
  simp [acyclicMaps]

/-- If `U \ R = ∅` then there is exactly one parent map (`id`). -/
private theorem card_acyclicMaps_of_sdiff_empty {α : Type*} [Fintype α] [DecidableEq α]
    {U R : Finset α} (h : U \ R = ∅) : (acyclicMaps U R).card = 1 := by
  have hempty : ∀ x : α, x ∉ U \ R := by
    intro x hx
    rw [h] at hx
    exact Finset.notMem_empty x hx
  have hsub : acyclicMaps U R = {id} := by
    ext f
    simp only [mem_acyclicMaps, Finset.mem_singleton]
    constructor
    · intro ⟨ha, _, _⟩
      funext x
      exact ha x (hempty x)
    · intro hf
      subst hf
      refine ⟨fun x _ => rfl, fun x hx => absurd hx (hempty x),
        ⟨fun _ => 0, fun x hx => absurd hx (hempty x)⟩⟩
  rw [hsub, Finset.card_singleton]

/-- With an empty root set on a nonempty `U`, no parent map is acyclic. -/
private theorem acyclicMaps_empty_root_eq_empty {α : Type*} [Fintype α] [DecidableEq α]
    {U : Finset α} (hne : U.Nonempty) : acyclicMaps U ∅ = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro f hf
  rw [mem_acyclicMaps] at hf
  obtain ⟨_, hb, h, hh⟩ := hf
  simp only [Finset.sdiff_empty] at hb hh
  obtain ⟨x0, hx0U, hmin⟩ := Finset.exists_min_image U h hne
  have hfx0 : f x0 ∈ U := hb x0 hx0U
  have hlt : h (f x0) < h x0 := hh x0 hx0U
  have hle : h x0 ≤ h (f x0) := hmin (f x0) hfx0
  omega

private def fwd {α : Type*} [Fintype α] [DecidableEq α]
    (r : α) (U R : Finset α) (f : α → α) : α → α :=
  fun x => if x ∈ (U \ R).filter (fun y => f y = r) then x else f x

private def bwd {α : Type*} [DecidableEq α] (r : α) (S : Finset α) (g : α → α) : α → α :=
  fun x => if x ∈ S then r else g x

private theorem acyclicMaps_delete_root_mapsTo {α : Type*} [Fintype α] [DecidableEq α]
    {U R : Finset α} {r : α} (hRU : R ⊆ U) (hrR : r ∈ R)
    {f : α → α} (hf : f ∈ acyclicMaps U R) :
    fwd r U R f ∈ acyclicMaps (U.erase r) ((R.erase r) ∪ (U \ R).filter (fun y => f y = r)) := by
  rw [mem_acyclicMaps] at hf ⊢
  obtain ⟨ha, hb, h, hh⟩ := hf
  have hrU : r ∈ U := hRU hrR
  have hset : ∀ x : α, (x ∈ (U.erase r) \ ((R.erase r) ∪ (U \ R).filter (fun y => f y = r)) ↔
      (x ∈ (U \ R) ∧ x ∉ (U \ R).filter (fun y => f y = r))) := by
    intro x
    constructor
    · intro hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hxUe, hxRe⟩ := hx
      rw [Finset.mem_erase] at hxUe
      obtain ⟨hxne, hxU⟩ := hxUe
      rw [Finset.mem_union, Finset.mem_erase] at hxRe
      have hxR : x ∉ R := by
        intro hxRmem
        by_cases heq : x = r
        · subst heq; exact hxne rfl
        · exact hxRe (Or.inl ⟨heq, hxRmem⟩)
      have hxUR : x ∈ U \ R := Finset.mem_sdiff.mpr ⟨hxU, hxR⟩
      have hxF : x ∉ (U \ R).filter (fun y => f y = r) := by
        intro hxFmem
        exact hxRe (Or.inr hxFmem)
      exact ⟨hxUR, hxF⟩
    · intro hx
      obtain ⟨hxUR, hxF⟩ := hx
      rw [Finset.mem_sdiff] at hxUR
      obtain ⟨hxU, hxR⟩ := hxUR
      rw [Finset.mem_sdiff]
      constructor
      · rw [Finset.mem_erase]
        constructor
        · intro heq
          subst heq
          exact hxR hrR
        · exact hxU
      · rw [Finset.mem_union]
        intro hmem
        rcases hmem with hmem | hmem
        · rw [Finset.mem_erase] at hmem
          exact hxR hmem.2
        · exact hxF hmem
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    unfold fwd
    by_cases hxS : x ∈ (U \ R).filter (fun y => f y = r)
    · simp only [hxS, ↓reduceIte]
    · simp only [hxS, ite_false]
      apply ha
      intro hxUR
      have : x ∈ (U.erase r) \ ((R.erase r) ∪ (U \ R).filter (fun y => f y = r)) :=
        (hset x).mpr ⟨hxUR, hxS⟩
      exact hx this
  · intro x hx
    rw [hset] at hx
    obtain ⟨hxUR, hxS⟩ := hx
    unfold fwd
    simp only [hxS, ite_false]
    have hfxU : f x ∈ U := hb x hxUR
    have hfxne : f x ≠ r := by
      intro heq
      exact hxS (Finset.mem_filter.mpr ⟨hxUR, heq⟩)
    exact Finset.mem_erase.mpr ⟨hfxne, hfxU⟩
  · refine ⟨h, fun x hx => ?_⟩
    rw [hset] at hx
    obtain ⟨hxUR, hxS⟩ := hx
    unfold fwd
    simp only [hxS, ite_false]
    exact hh x hxUR

private theorem acyclicMaps_add_root_mapsTo {α : Type*} [Fintype α] [DecidableEq α]
    {U R : Finset α} {r : α} (hRU : R ⊆ U) (hrR : r ∈ R)
    {S : Finset α} (hSU : S ⊆ U \ R)
    {g : α → α} (hg : g ∈ acyclicMaps (U.erase r) ((R.erase r) ∪ S)) :
    bwd r S g ∈ acyclicMaps U R := by
  rw [mem_acyclicMaps] at hg ⊢
  obtain ⟨ga, gb, hg_rank, hgg⟩ := hg
  have hrU : r ∈ U := hRU hrR
  have hr_not_U' : r ∉ U.erase r := Finset.notMem_erase r U
  have hS_of_not : ∀ x : α, x ∉ U \ R → x ∉ S := fun x hx hxS =>
    hx (hSU hxS)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hxS : x ∉ S := hS_of_not x hx
    unfold bwd
    simp only [hxS, ite_false]
    apply ga
    intro hxmem
    rw [Finset.mem_sdiff] at hxmem hx
    obtain ⟨hxUe, hxRe⟩ := hxmem
    by_cases hxU : x ∈ U
    · have hxR : x ∈ R := by
        by_contra hcon
        exact hx ⟨hxU, hcon⟩
      by_cases heq : x = r
      · subst heq
        exact hr_not_U' hxUe
      · have hxmem : x ∈ R.erase r := Finset.mem_erase.mpr ⟨heq, hxR⟩
        have : x ∈ (R.erase r) ∪ S := Finset.mem_union.mpr (Or.inl hxmem)
        exact hxRe this
    · have : x ∉ U.erase r := by
        intro hmem
        rw [Finset.mem_erase] at hmem
        exact hxU hmem.2
      exact this hxUe
  · intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxU, hxR⟩ := hx
    unfold bwd
    by_cases hxS : x ∈ S
    · simp only [hxS, ↓reduceIte]
      exact hrU
    · simp only [hxS, ite_false]
      have hxne : x ≠ r := by
        intro heq
        subst heq
        exact hxR hrR
      have hxUe : x ∈ U.erase r := Finset.mem_erase.mpr ⟨hxne, hxU⟩
      have hxRe : x ∉ (R.erase r) ∪ S := by
        rw [Finset.mem_union]
        intro hmem
        rcases hmem with hmem | hmem
        · rw [Finset.mem_erase] at hmem
          exact hxR hmem.2
        · exact hxS hmem
      have hxmem : x ∈ (U.erase r) \ ((R.erase r) ∪ S) :=
        Finset.mem_sdiff.mpr ⟨hxUe, hxRe⟩
      have hgb := gb x hxmem
      rw [Finset.mem_erase] at hgb
      exact hgb.2
  · refine ⟨fun x => if x = r then 0 else hg_rank x + 1, fun x hx => ?_⟩
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxU, hxR⟩ := hx
    have hxne : x ≠ r := by
      intro heq
      subst heq
      exact hxR hrR
    unfold bwd
    by_cases hxS : x ∈ S
    · simp only [hxS, ↓reduceIte]
      simp [hxne]
    · simp only [hxS, ite_false]
      have hxUe : x ∈ U.erase r := Finset.mem_erase.mpr ⟨hxne, hxU⟩
      have hxRe : x ∉ (R.erase r) ∪ S := by
        rw [Finset.mem_union]
        intro hmem
        rcases hmem with hmem | hmem
        · rw [Finset.mem_erase] at hmem
          exact hxR hmem.2
        · exact hxS hmem
      have hxmem : x ∈ (U.erase r) \ ((R.erase r) ∪ S) :=
        Finset.mem_sdiff.mpr ⟨hxUe, hxRe⟩
      have hgb := gb x hxmem
      rw [Finset.mem_erase] at hgb
      obtain ⟨hgne, _⟩ := hgb
      have hlt := hgg x hxmem
      simp only [hgne, ite_false, hxne, ite_false]
      omega

private theorem acyclicMaps_add_root_fiber {α : Type*} [Fintype α] [DecidableEq α]
    {U R : Finset α} {r : α} (_hRU : R ⊆ U) (hrR : r ∈ R)
    {S : Finset α} (hSU : S ⊆ U \ R)
    {g : α → α} (hg : g ∈ acyclicMaps (U.erase r) ((R.erase r) ∪ S)) :
    (U \ R).filter (fun x => bwd r S g x = r) = S := by
  rw [mem_acyclicMaps] at hg
  obtain ⟨ga, gb, hg_rank, hgg⟩ := hg
  ext x
  constructor
  · intro hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxUR, hxeq⟩ := hx
    unfold bwd at hxeq
    by_cases hxS : x ∈ S
    · exact hxS
    · simp only [hxS, ite_false] at hxeq
      have hxUR' : x ∈ U \ R := hxUR
      rw [Finset.mem_sdiff] at hxUR'
      obtain ⟨hxU, hxR⟩ := hxUR'
      have hxne : x ≠ r := fun heq => hxR (heq ▸ hrR)
      have hxUe : x ∈ U.erase r := Finset.mem_erase.mpr ⟨hxne, hxU⟩
      have hxRe : x ∉ (R.erase r) ∪ S := by
        rw [Finset.mem_union]
        intro hmem
        rcases hmem with hmem | hmem
        · rw [Finset.mem_erase] at hmem
          exact hxR hmem.2
        · exact hxS hmem
      have hxmem : x ∈ (U.erase r) \ ((R.erase r) ∪ S) :=
        Finset.mem_sdiff.mpr ⟨hxUe, hxRe⟩
      have hgb := gb x hxmem
      rw [Finset.mem_erase, hxeq] at hgb
      exact False.elim (hgb.1 rfl)
  · intro hxS
    have hxUR := hSU hxS
    rw [Finset.mem_filter]
    refine ⟨hxUR, ?_⟩
    unfold bwd
    simp only [hxS, ↓reduceIte]

private theorem card_acyclicMaps_eq_sum {α : Type*} [Fintype α] [DecidableEq α]
    {U R : Finset α} (hRU : R ⊆ U) {r : α} (hrR : r ∈ R) :
    (acyclicMaps U R).card =
      ∑ S ∈ (U \ R).powerset, (acyclicMaps (U.erase r) ((R.erase r) ∪ S)).card := by
  classical
  -- fiber map
  let φ : (α → α) → Finset α := fun f => (U \ R).filter (fun x => f x = r)
  have hmaps : Set.MapsTo φ ↑(acyclicMaps U R) ↑((U \ R).powerset) := by
    intro f hf
    rw [Finset.mem_coe, Finset.mem_powerset]
    exact Finset.filter_subset _ _
  have hfib := Finset.card_eq_sum_card_fiberwise (s := acyclicMaps U R)
    (t := (U \ R).powerset) (f := φ) hmaps
  rw [hfib]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mem_powerset] at hS
  -- fiber = {f ∈ acyclicMaps U R | φ f = S}
  -- show its card equals target card via nbij'
  have hfib_eq : ({a ∈ acyclicMaps U R | φ a = S}).card =
      (acyclicMaps (U.erase r) ((R.erase r) ∪ S)).card := by
    apply Finset.card_nbij' (i := fun f => fwd r U R f) (j := fun g => bwd r S g)
    · -- i maps fiber to target
      intro f hf
      rw [Finset.mem_coe, Finset.mem_filter] at hf
      obtain ⟨hfmem, hφ⟩ := hf
      -- φ f = S, so fwd's filter = S
      have h1 : fwd r U R f ∈ acyclicMaps (U.erase r) ((R.erase r) ∪ φ f) :=
        acyclicMaps_delete_root_mapsTo hRU hrR hfmem
      rw [hφ] at h1
      exact Finset.mem_coe.mpr h1
    · -- j maps target to fiber
      intro g hg
      rw [Finset.mem_coe] at hg ⊢
      have hgmem : g ∈ acyclicMaps (U.erase r) ((R.erase r) ∪ S) := hg
      have hbwd : bwd r S g ∈ acyclicMaps U R :=
        acyclicMaps_add_root_mapsTo hRU hrR hS hgmem
      have hφbwd : φ (bwd r S g) = S :=
        acyclicMaps_add_root_fiber hRU hrR hS hgmem
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_coe.mpr hbwd, hφbwd⟩
    · -- left inv: bwd (fwd f) = f for f in fiber
      intro f hf
      rw [Finset.mem_coe, Finset.mem_filter] at hf
      obtain ⟨hfmem, hφ⟩ := hf
      -- for each x: bwd (fwd f) x = f x
      change bwd r S (fwd r U R f) = f
      have hS_eq : φ f = S := hφ
      have hSe : ((U \ R).filter (fun y => f y = r)) = S := hφ
      -- fwd f x = if x ∈ S then x else f x
      have hfwdeq : ∀ x, fwd r U R f x = (if x ∈ S then x else f x) := by
        intro x
        unfold fwd φ at *
        have : (x ∈ (U \ R).filter (fun y => f y = r)) ↔ (x ∈ S) := by
          rw [hS_eq]
        by_cases hxS : x ∈ S
        · have hxF : x ∈ (U \ R).filter (fun y => f y = r) := by
            rw [hS_eq]; exact hxS
          simp [hxF, hxS]
        · have hxF : x ∉ (U \ R).filter (fun y => f y = r) := by
            rw [hS_eq]; exact hxS
          simp [hxF, hxS]
      funext x
      unfold bwd
      by_cases hxS : x ∈ S
      · simp only [hxS, ↓reduceIte]
        -- f x = r since x ∈ S = φ f
        have : f x = r := by
          have hxF : x ∈ (U \ R).filter (fun y => f y = r) := by
            rw [hSe]; exact hxS
          rw [Finset.mem_filter] at hxF
          exact hxF.2
        exact this.symm
      · simp only [hxS, ite_false]
        rw [hfwdeq x]; simp [hxS]
    · -- right inv: fwd (bwd g) = g for g in target
      intro g hg
      rw [Finset.mem_coe] at hg
      have hgmem : g ∈ acyclicMaps (U.erase r) ((R.erase r) ∪ S) := hg
      rw [mem_acyclicMaps] at hg
      obtain ⟨ga, gb, hg_rank, hgg⟩ := hg
      change fwd r U R (bwd r S g) = g
      have hφbwd : φ (bwd r S g) = S :=
        acyclicMaps_add_root_fiber hRU hrR hS hgmem
      funext x
      unfold fwd
      -- filter of bwd = S
      have hF : ((U \ R).filter (fun y => bwd r S g y = r)) = S := hφbwd
      by_cases hxS : x ∈ ((U \ R).filter (fun y => bwd r S g y = r))
      · -- then x ∈ S, fwd gives x, and g x = x
        have hxS' : x ∈ S := by rw [← hF]; exact hxS
        simp only [hxS, ↓reduceIte]
        -- g x = x since x ∈ S ⊆ R'
        have hxR' : x ∈ (R.erase r) ∪ S := Finset.mem_union.mpr (Or.inr hxS')
        -- x ∉ U' \ R' since x ∈ R'
        have : x ∉ (U.erase r) \ ((R.erase r) ∪ S) := by
          intro hmem
          rw [Finset.mem_sdiff] at hmem
          exact hmem.2 hxR'
        exact (ga x this).symm
      · have hxS' : x ∉ S := by
          intro hcon
          have hconF : x ∈ ((U \ R).filter (fun y => bwd r S g y = r)) := by
            rw [hF]; exact hcon
          exact hxS hconF
        simp only [hxS, ite_false]
        unfold bwd
        simp only [hxS', ite_false]
  exact hfib_eq

/-- Abel-type binomial identity used by the root-deletion induction.
By induction on `m` generalizing `j`, via Pascal's rule. -/
private theorem abel_binomial_identity (m j x : ℕ) :
    (x + 1) * (∑ i ∈ Finset.range (m + 1), m.choose i * (j + i) * x ^ (m - i))
      = (x + 1) ^ m * (j * (x + 1) + m) := by
  induction m generalizing j with
  | zero => simp [mul_comm]
  | succ m ih =>
    have hrec : (∑ i ∈ Finset.range (m + 2), (m+1).choose i * (j + i) * x ^ (m + 1 - i))
        = x * (∑ i ∈ Finset.range (m + 1), m.choose i * (j + i) * x ^ (m - i))
          + (∑ i ∈ Finset.range (m + 1), m.choose i * ((j+1) + i) * x ^ (m - i)) := by
      have hexpand : (∑ i ∈ Finset.range (m + 2), (m+1).choose i * (j + i) * x ^ (m + 1 - i))
          = (∑ k ∈ Finset.range (m + 1), (m+1).choose (k+1) * (j + (k+1)) * x ^ (m + 1 - (k+1)))
            + (j + 0) * x ^ (m + 1) := by
        rw [Finset.sum_range_succ']
        simp [Nat.choose_zero_right]
      rw [hexpand]
      have hpascal : (∑ k ∈ Finset.range (m + 1),
            (m+1).choose (k+1) * (j + (k+1)) * x ^ (m + 1 - (k+1)))
          = (∑ k ∈ Finset.range (m + 1), m.choose k * ((j+1) + k) * x ^ (m - k))
            + (∑ k ∈ Finset.range (m + 1),
              m.choose (k+1) * (j + (k+1)) * x ^ (m - k)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [Nat.choose_succ_succ']
        have e1 : m + 1 - (k + 1) = m - k := by omega
        have e2 : j + (k + 1) = (j + 1) + k := by omega
        rw [e1, e2]
        ring
      rw [hpascal]
      have hS : (∑ i ∈ Finset.range (m + 1), m.choose i * (j + i) * x ^ (m - i))
          = (∑ k ∈ Finset.range m, m.choose (k+1) * ((j+1) + k) * x ^ (m - (k+1)))
            + m.choose 0 * (j + 0) * x ^ (m - 0) := by
        have h := Finset.sum_range_succ' (fun i => m.choose i * (j + i) * x ^ (m - i)) m
        rw [h]
        apply congrArg₂ (· + ·)
        · apply Finset.sum_congr rfl
          intro k _
          have e2 : j + (k + 1) = (j + 1) + k := by omega
          rw [e2]
        · simp
      have hextend : (∑ k ∈ Finset.range m, m.choose (k+1) * ((j+1) + k) * x ^ (m - (k+1)))
          = (∑ k ∈ Finset.range (m + 1), m.choose (k+1) * ((j+1) + k) * x ^ (m - (k+1))) := by
        rw [Finset.sum_range_succ]
        simp
      have hfactor : (∑ k ∈ Finset.range (m + 1), m.choose (k+1) * (j + (k+1)) * x ^ (m - k))
          = x * (∑ k ∈ Finset.range (m + 1), m.choose (k+1) * ((j+1) + k) * x ^ (m - (k+1))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have e2 : j + (k + 1) = (j + 1) + k := by omega
        rw [e2]
        by_cases hkm : k + 1 ≤ m
        · have em : m - k = (m - (k + 1)) + 1 := by omega
          rw [em, pow_succ]
          ring
        · have hzero : m.choose (k + 1) = 0 := by
            apply Nat.choose_eq_zero_of_lt
            omega
          rw [hzero]
          simp
      rw [hS, hextend] at *
      rw [hfactor]
      simp [Nat.choose_zero_right]
      ring
    rw [hrec, mul_add, mul_left_comm (x + 1) x _, ih j, ih (j + 1)]
    ring

/-- Forest count, by induction on `U.card`. -/
private theorem card_acyclicMaps_mul_aux {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (U R : Finset α) (hRU : R ⊆ U) (hcard : U.card = n) :
    (acyclicMaps U R).card * U.card = R.card * U.card ^ (U.card - R.card) := by
  induction n generalizing U R with
  | zero =>
    have hU : U = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hU
    have hR : R = ∅ := Finset.subset_empty.mp hRU
    subst hR
    simp
  | succ n ih =>
    by_cases hR0 : R = ∅
    · subst hR0
      have hpos : 0 < U.card := by omega
      have hne : U.Nonempty := Finset.card_pos.mp hpos
      have h0 : acyclicMaps U ∅ = ∅ := acyclicMaps_empty_root_eq_empty hne
      rw [h0, Finset.card_empty]
      simp
    · by_cases hUR : U \ R = ∅
      · have hsub : U ⊆ R := Finset.sdiff_eq_empty_iff_subset.mp hUR
        have hRU' : R = U := Finset.Subset.antisymm hRU hsub
        have hc : (acyclicMaps U R).card = 1 := card_acyclicMaps_of_sdiff_empty hUR
        have hcc : R.card = U.card := by rw [hRU']
        rw [hc, hcc, Nat.sub_self, pow_zero, mul_one, one_mul]
      · obtain ⟨r, hrR⟩ := Finset.nonempty_iff_ne_empty.mpr hR0
        have hrU : r ∈ U := hRU hrR
        have hU'card : (U.erase r).card = n := by
          rw [Finset.card_erase_of_mem hrU, hcard]
          omega
        have hm : (U \ R).card = U.card - R.card :=
          Finset.card_sdiff_of_subset hRU
        have hmpos : 0 < (U \ R).card :=
          Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hUR)
        have hkpos : 0 < R.card := Finset.card_pos.mpr ⟨r, hrR⟩
        have hkle : R.card ≤ U.card := Finset.card_le_card hRU
        have hRp : (R.erase r).card + 1 = R.card := by
          rw [Finset.card_erase_of_mem hrR]
          omega
        have hUp : (U.erase r).card + 1 = U.card := by
          rw [Finset.card_erase_of_mem hrU]
          omega
        have hxmj : (U.erase r).card = (U \ R).card + (R.erase r).card := by omega
        have hxpos : 0 < (U.erase r).card := by omega
        have hN5 := card_acyclicMaps_eq_sum hRU hrR
        have hterm : ∀ S ∈ (U \ R).powerset,
            (acyclicMaps (U.erase r) ((R.erase r) ∪ S)).card * (U.erase r).card
            = (((R.erase r).card + S.card) * (U.erase r).card ^ ((U \ R).card - S.card)) := by
          intro S hS
          rw [Finset.mem_powerset] at hS
          have hsub' : (R.erase r) ∪ S ⊆ U.erase r := by
            apply Finset.union_subset
            · exact Finset.erase_subset_erase r hRU
            · intro a ha
              have haUR := hS ha
              rw [Finset.mem_sdiff] at haUR
              obtain ⟨haU, haR⟩ := haUR
              rw [Finset.mem_erase]
              constructor
              · intro heq
                subst heq
                exact haR hrR
              · exact haU
          have hdisj : Disjoint (R.erase r) S := by
            rw [Finset.disjoint_left]
            intro a haA haS
            rw [Finset.mem_erase] at haA
            have haUR := hS haS
            rw [Finset.mem_sdiff] at haUR
            exact haUR.2 haA.2
          have hcard' : ((R.erase r) ∪ S).card = (R.erase r).card + S.card :=
            Finset.card_union_of_disjoint hdisj
          have hIH := ih (U.erase r) ((R.erase r) ∪ S) hsub' hU'card
          have hexp : (U.erase r).card - ((R.erase r) ∪ S).card
              = (U \ R).card - S.card := by
            have h1 : S.card ≤ (U \ R).card := Finset.card_le_card hS
            have h2 : ((R.erase r) ∪ S).card ≤ (U.erase r).card :=
              Finset.card_le_card hsub'
            omega
          rw [hexp] at hIH
          rw [hcard'] at hIH
          exact hIH
        have hXC : (U.erase r).card * (acyclicMaps U R).card
            = ∑ S ∈ (U \ R).powerset,
              (((R.erase r).card + S.card) * (U.erase r).card ^ ((U \ R).card - S.card)) := by
          rw [hN5, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hS
          have h := hterm S hS
          rw [mul_comm]
          exact h
        have hps := Finset.sum_powerset_apply_card
          (fun c => ((R.erase r).card + c) * (U.erase r).card ^ ((U \ R).card - c)) (x := U \ R)
        have hregroup : (∑ S ∈ (U \ R).powerset,
              (((R.erase r).card + S.card) * (U.erase r).card ^ ((U \ R).card - S.card)))
            = ∑ i ∈ Finset.range ((U \ R).card + 1),
              ((U \ R).card.choose i * (((R.erase r).card + i)
                * (U.erase r).card ^ ((U \ R).card - i))) := by
          have hps' : (∑ S ∈ (U \ R).powerset,
              ((fun c => ((R.erase r).card + c) * (U.erase r).card ^ ((U \ R).card - c)) (S.card)))
              = ∑ i ∈ Finset.range ((U \ R).card + 1),
              ((U \ R).card.choose i •
                ((fun c => ((R.erase r).card + c)
                  * (U.erase r).card ^ ((U \ R).card - c)) i)) := hps
          simpa [smul_eq_mul, mul_assoc] using hps'
        have hsum_eq : (∑ i ∈ Finset.range ((U \ R).card + 1),
              ((U \ R).card.choose i * (((R.erase r).card + i)
                * (U.erase r).card ^ ((U \ R).card - i))))
            = (∑ i ∈ Finset.range ((U \ R).card + 1),
              ((U \ R).card.choose i * ((R.erase r).card + i)
                * (U.erase r).card ^ ((U \ R).card - i))) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        have habel := abel_binomial_identity ((U \ R).card) ((R.erase r).card) ((U.erase r).card)
        have hcombine : ((U.erase r).card + 1) * ((U.erase r).card * (acyclicMaps U R).card)
            = ((U.erase r).card + 1) ^ (U \ R).card
              * ((R.erase r).card * ((U.erase r).card + 1) + (U \ R).card) := by
          rw [hXC, hregroup, hsum_eq]
          exact habel
        have hident : (R.erase r).card * ((U.erase r).card + 1) + (U \ R).card
            = (U.erase r).card * ((R.erase r).card + 1) := by
          rw [hxmj]; ring
        have hLHS : ((U.erase r).card + 1) * ((U.erase r).card * (acyclicMaps U R).card)
            = (U.erase r).card * ((acyclicMaps U R).card * U.card) := by
          rw [← hUp]; ring
        have hRHS : ((U.erase r).card + 1) ^ (U \ R).card
              * ((R.erase r).card * ((U.erase r).card + 1) + (U \ R).card)
            = (U.erase r).card * (R.card * U.card ^ (U.card - R.card)) := by
          rw [hident, hRp, ← hm, ← hUp]
          ring
        rw [hLHS, hRHS] at hcombine
        exact Nat.eq_of_mul_eq_mul_left hxpos hcombine

/-- Forest count, closed form. -/
private theorem card_acyclicMaps_mul {α : Type*} [Fintype α] [DecidableEq α]
    {U R : Finset α} (hRU : R ⊆ U) :
    (acyclicMaps U R).card * U.card = R.card * U.card ^ (U.card - R.card) :=
  card_acyclicMaps_mul_aux U.card U R hRU rfl

/-- Connectivity half: parent map gives a connected graph. -/
private theorem fromRel_connected_of_mem {V : Type*} [Fintype V] [DecidableEq V]
    {r : V} {f : V → V} (hf : f ∈ acyclicMaps Finset.univ {r}) :
    (SimpleGraph.fromRel (fun u v => f u = v)).Connected := by
  rw [mem_acyclicMaps] at hf
  obtain ⟨ha, hb, h, hh⟩ := hf
  have hmem : ∀ x : V, (x ∈ Finset.univ \ {r} ↔ x ≠ r) := by
    intro x
    simp [Finset.mem_sdiff, Finset.mem_singleton]
  have hfr : f r = r := by
    apply ha
    simp [hmem]
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨r, fun w => ?_⟩
  -- strong induction on h w
  have key : ∀ (k : ℕ) (x : V), h x = k →
      (SimpleGraph.fromRel (fun u v => f u = v)).Reachable x r := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro x hx
      by_cases heq : x = r
      · subst heq
        exact SimpleGraph.Reachable.refl _
      · have hxUR : x ∈ Finset.univ \ {r} := (hmem x).mpr heq
        have hlt : h (f x) < h x := hh x hxUR
        have hihr := ih (h (f x)) (by omega) (f x) rfl
        have hne : x ≠ f x := by
          intro heq2
          have heq3 : h x = h (f x) := congrArg h heq2
          omega
        have hadj : (SimpleGraph.fromRel (fun u v => f u = v)).Adj x (f x) := by
          rw [SimpleGraph.fromRel_adj]
          exact ⟨hne, Or.inl rfl⟩
        exact hadj.reachable.trans hihr
  exact (key (h w) w rfl).symm

/-- Edge half: the edges of the parent-map graph are exactly
`Sym2.mk x (f x)` for `x ≠ r`. -/
private theorem edgeFinset_fromRel_of_mem {V : Type*} [Fintype V] [DecidableEq V]
    {r : V} {f : V → V} (hf : f ∈ acyclicMaps Finset.univ {r}) :
    (SimpleGraph.fromRel (fun u v => f u = v)).edgeFinset =
      (Finset.univ.erase r).image (fun x => Sym2.mk x (f x)) := by
  rw [mem_acyclicMaps] at hf
  obtain ⟨ha, _, h, hh⟩ := hf
  have hmem : ∀ x : V, (x ∈ Finset.univ \ {r} ↔ x ≠ r) := by
    intro x
    simp [Finset.mem_sdiff, Finset.mem_singleton]
  have hfr : f r = r := ha r (by simp [hmem])
  have hfx : ∀ x : V, x ≠ r → x ≠ f x := by
    intro x hxr heq
    have hcon : h x = h (f x) := congrArg h heq
    have hlt := hh x ((hmem x).mpr hxr)
    omega
  ext e
  induction e using Sym2.ind with
  | h u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      SimpleGraph.fromRel_adj]
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨huv, hfu | hfv⟩
      · have hur : u ≠ r := by
          rintro rfl
          rw [hfr] at hfu
          exact huv hfu
        exact ⟨u, hur, by rw [hfu]⟩
      · have hvr : v ≠ r := by
          rintro rfl
          rw [hfr] at hfv
          exact huv hfv.symm
        exact ⟨v, hvr, by rw [hfv]; exact Sym2.eq_swap⟩
    · rintro ⟨x, hxr, heq⟩
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1
        subst h2
        exact ⟨hfx _ hxr, Or.inl rfl⟩
      · subst h1
        subst h2
        exact ⟨fun he => hfx _ hxr he.symm, Or.inr rfl⟩

/-- The graph of an acyclic parent map is a tree. -/
private theorem isTree_fromRel_of_mem {V : Type*} [Fintype V] [DecidableEq V]
    {r : V} {f : V → V} (hf : f ∈ acyclicMaps Finset.univ {r}) :
    (SimpleGraph.fromRel (fun u v => f u = v)).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨fromRel_connected_of_mem hf, ?_⟩
  have hinj : Set.InjOn (fun x => Sym2.mk x (f x)) ↑(Finset.univ.erase r) := by
    rw [mem_acyclicMaps] at hf
    obtain ⟨_, _, h, hh⟩ := hf
    have hmem : ∀ x : V, (x ∈ Finset.univ \ {r} ↔ x ≠ r) := by
      intro x
      simp [Finset.mem_sdiff, Finset.mem_singleton]
    intro x hx y hy heq
    simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true] at hx hy
    by_contra hne
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact hne h1
    · have h1' := hh x ((hmem x).mpr hx)
      have h2' := hh y ((hmem y).mpr hy)
      subst h1
      rw [h2] at h1'
      omega
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card, edgeFinset_fromRel_of_mem hf,
    Finset.card_image_of_injOn hinj,
    Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ]
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
  omega

/-- Depth function for an acyclic parent map, agreeing with distance. -/
private theorem fromRel_depth_spec {V : Type*} [Fintype V] [DecidableEq V]
    {r : V} {f : V → V} (hf : f ∈ acyclicMaps Finset.univ {r}) :
    ∃ d : V → ℕ, d r = 0 ∧ (∀ x : V, x ≠ r → d (f x) + 1 = d x) ∧
      ∀ x : V, (SimpleGraph.fromRel (fun u v => f u = v)).dist x r = d x := by
  rw [mem_acyclicMaps] at hf
  obtain ⟨ha, hb, h, hh⟩ := hf
  have hmem : ∀ x : V, (x ∈ Finset.univ \ {r} ↔ x ≠ r) := by
    intro x
    simp [Finset.mem_sdiff, Finset.mem_singleton]
  have hfr : f r = r := ha r (by simp [hmem])
  have hfx : ∀ x : V, x ≠ r → x ≠ f x := by
    intro x hxr heq
    have hcon : h x = h (f x) := congrArg h heq
    have hlt := hh x ((hmem x).mpr hxr)
    omega
  have hconn : (SimpleGraph.fromRel (fun u v => f u = v)).Connected :=
    fromRel_connected_of_mem (mem_acyclicMaps.mpr ⟨ha, hb, h, hh⟩)
  have hex : ∀ x : V, ∃ k : ℕ, f^[k] x = r := by
    have key : ∀ k : ℕ, ∀ x : V, h x = k → ∃ j : ℕ, f^[j] x = r := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro x hx
        by_cases hxr : x = r
        · exact ⟨0, by simp [hxr]⟩
        · have hlt : h (f x) < h x := hh x ((hmem x).mpr hxr)
          obtain ⟨j, hj⟩ := ih (h (f x)) (by omega) (f x) rfl
          refine ⟨j + 1, ?_⟩
          rw [show j + 1 = j.succ from rfl, Function.iterate_succ_apply]
          exact hj
    exact fun x => key (h x) x rfl
  have hdr : Nat.find (hex r) = 0 :=
    Nat.eq_zero_of_le_zero (Nat.find_min' _ (Function.iterate_zero_apply f r))
  have heq : ∀ x : V, x ≠ r → Nat.find (hex (f x)) + 1 = Nat.find (hex x) := by
    intro x hxr
    have hspec : f^[Nat.find (hex x)] x = r := Nat.find_spec (hex x)
    have hspecf : f^[Nat.find (hex (f x))] (f x) = r := Nat.find_spec (hex (f x))
    have hpos : 0 < Nat.find (hex x) := by
      rcases Nat.eq_zero_or_pos (Nat.find (hex x)) with h0 | hp
      · exfalso
        rw [h0, Function.iterate_zero_apply f] at hspec
        exact hxr hspec
      · exact hp
    have e1 : f^[Nat.find (hex x) - 1] (f x) = r := by
      have hdx1 : (Nat.find (hex x) - 1).succ = Nat.find (hex x) := by omega
      calc f^[Nat.find (hex x) - 1] (f x)
          = f^[(Nat.find (hex x) - 1).succ] x :=
            (Function.iterate_succ_apply _ _ _).symm
        _ = f^[Nat.find (hex x)] x := by rw [hdx1]
        _ = r := hspec
    have e2 : f^[Nat.find (hex (f x)) + 1] x = r := by
      rw [show Nat.find (hex (f x)) + 1 = (Nat.find (hex (f x))).succ from rfl,
        Function.iterate_succ_apply]
      exact hspecf
    have hle1 : Nat.find (hex (f x)) ≤ Nat.find (hex x) - 1 :=
      Nat.find_min' _ e1
    have hle2 : Nat.find (hex x) ≤ Nat.find (hex (f x)) + 1 :=
      Nat.find_min' _ e2
    omega
  have hub : ∀ x : V, ∃ p : (SimpleGraph.fromRel (fun u v => f u = v)).Walk x r,
      p.length = Nat.find (hex x) := by
    have key : ∀ k : ℕ, ∀ x : V, Nat.find (hex x) = k →
        ∃ p : (SimpleGraph.fromRel (fun u v => f u = v)).Walk x r, p.length = k := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro x hx
        by_cases hxr : x = r
        · subst hxr
          refine ⟨SimpleGraph.Walk.nil, ?_⟩
          rw [SimpleGraph.Walk.length_nil]
          rw [hdr] at hx
          exact hx
        · have hlt : Nat.find (hex (f x)) < k := by
            have he := heq x hxr
            omega
          obtain ⟨p, hp⟩ := ih _ hlt _ rfl
          have hadj : (SimpleGraph.fromRel (fun u v => f u = v)).Adj x (f x) := by
            rw [SimpleGraph.fromRel_adj]
            exact ⟨hfx x hxr, Or.inl rfl⟩
          refine ⟨p.cons hadj, ?_⟩
          rw [SimpleGraph.Walk.length_cons, hp, heq x hxr]
          exact hx
    exact fun x => key _ x rfl
  have hle : ∀ {u v : V} (p : (SimpleGraph.fromRel (fun u v => f u = v)).Walk u v),
      Nat.find (hex u) ≤ p.length + Nat.find (hex v) := by
    intro u v p
    induction p with
    | nil =>
      rw [SimpleGraph.Walk.length_nil, Nat.zero_add]
    | @cons u w v h q ih =>
      rw [SimpleGraph.Walk.length_cons]
      have hadj : u ≠ w ∧ (f u = w ∨ f w = u) :=
        (SimpleGraph.fromRel_adj _ _ _).mp h
      have hstep : Nat.find (hex u) ≤ Nat.find (hex w) + 1 := by
        rcases hadj.2 with hfu | hfw
        · by_cases hur : u = r
          · subst hur
            rw [hdr]
            exact Nat.zero_le _
          · rw [← hfu, heq u hur]
        · by_cases hwr : w = r
          · subst hwr
            rw [hfr] at hfw
            subst hfw
            rw [hdr]
            exact Nat.zero_le _
          · rw [← hfw]
            have he := heq _ hwr
            omega
      omega
  refine ⟨fun x => Nat.find (hex x), ?_, ?_, ?_⟩
  · change Nat.find (hex r) = 0
    exact hdr
  · intro x hxr
    change Nat.find (hex (f x)) + 1 = Nat.find (hex x)
    exact heq x hxr
  · intro x
    change (SimpleGraph.fromRel (fun u v => f u = v)).dist x r = Nat.find (hex x)
    apply le_antisymm
    · obtain ⟨p, hp⟩ := hub x
      rw [← hp]
      exact SimpleGraph.dist_le p
    · have hreach : (SimpleGraph.fromRel (fun u v => f u = v)).Reachable x r :=
        hconn x r
      obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
      have hbound := hle p
      rw [hp, hdr, add_zero] at hbound
      exact hbound

open scoped Classical in
/-- Parent map of a graph toward a root, via distance-descent choice. -/
private noncomputable def treeParent {V : Type*}
    (T : _root_.SimpleGraph V) (r : V) : V → V :=
  fun v => if _hv : v = r then r
    else if _Hex : ∃ u, T.Adj v u ∧ T.dist u r < T.dist v r then
      Classical.choose _Hex
    else v

/-- The parent map of a parent-map graph is the original map. -/
private theorem treeParent_fromRel {V : Type*} [Fintype V] [DecidableEq V]
    {r : V} {f : V → V} (hf : f ∈ acyclicMaps Finset.univ {r}) :
    treeParent (SimpleGraph.fromRel (fun u v => f u = v)) r = f := by
  obtain ⟨d, hdr, hdf, hdist⟩ := fromRel_depth_spec hf
  rw [mem_acyclicMaps] at hf
  obtain ⟨ha, _, h, hh⟩ := hf
  have hmem : ∀ x : V, (x ∈ Finset.univ \ {r} ↔ x ≠ r) := by
    intro x
    simp [Finset.mem_sdiff, Finset.mem_singleton]
  have hfr : f r = r := ha r (by simp [hmem])
  have hfx : ∀ x : V, x ≠ r → x ≠ f x := by
    intro x hxr heq
    have hcon : h x = h (f x) := congrArg h heq
    have hlt := hh x ((hmem x).mpr hxr)
    omega
  funext v
  by_cases hvr : v = r
  · subst hvr
    unfold treeParent
    rw [dite_eq_left rfl]
    exact hfr.symm
  · have hfv_adj : (SimpleGraph.fromRel (fun u v => f u = v)).Adj v (f v) := by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨hfx v hvr, Or.inl rfl⟩
    have hfv_lt : (SimpleGraph.fromRel (fun u v => f u = v)).dist (f v) r
        < (SimpleGraph.fromRel (fun u v => f u = v)).dist v r := by
      rw [hdist (f v), hdist v]
      have hde := hdf v hvr
      omega
    have hex : ∃ u, (SimpleGraph.fromRel (fun u v => f u = v)).Adj v u ∧
        (SimpleGraph.fromRel (fun u v => f u = v)).dist u r
          < (SimpleGraph.fromRel (fun u v => f u = v)).dist v r :=
      ⟨f v, hfv_adj, hfv_lt⟩
    have hTP : treeParent (SimpleGraph.fromRel (fun u v => f u = v)) r v
        = Classical.choose hex := by
      unfold treeParent
      rw [dite_eq_right hvr, dite_eq_left hex]
    rw [hTP]
    have hch := Classical.choose_spec hex
    set c := Classical.choose hex with hc
    obtain ⟨hadj, hlt⟩ := hch
    rw [SimpleGraph.fromRel_adj] at hadj
    obtain ⟨_, hfl | hfr'⟩ := hadj
    · exact hfl.symm
    · by_cases hcr : c = r
      · rw [hcr, hfr] at hfr'
        exact False.elim (hvr hfr'.symm)
      · have hde := hdf _ hcr
        rw [hdist, hdist] at hlt
        rw [hfr'] at hde
        omega

/-- Helper: the root is its own parent. -/
private theorem treeParent_self {V : Type*}
    (T : _root_.SimpleGraph V) (r : V) : treeParent T r r = r := by
  unfold treeParent
  rw [dite_eq_left rfl]

/-- Helper: every non-root vertex has a distance-descent neighbour. -/
private theorem treeParent_hex {V : Type*}
    {T : _root_.SimpleGraph V} {r : V} (hconn : T.Connected) {v : V}
    (hvr : v ≠ r) : ∃ u, T.Adj v u ∧ T.dist u r < T.dist v r := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v r
  have hnil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hvr
  have hadj : T.Adj v p.snd := p.adj_snd hnil
  have hlen : p.tail.length + 1 = p.length :=
    SimpleGraph.Walk.length_tail_add_one hnil
  have hle : T.dist p.snd r ≤ p.tail.length := SimpleGraph.dist_le p.tail
  refine ⟨p.snd, hadj, by omega⟩

/-- The parent map of a connected graph is an acyclic parent map. -/
private theorem treeParent_mem_acyclicMaps {V : Type*} [Fintype V] [DecidableEq V]
    {T : _root_.SimpleGraph V} {r : V} (hconn : T.Connected) :
    treeParent T r ∈ acyclicMaps Finset.univ {r} := by
  rw [mem_acyclicMaps]
  have hmem : ∀ x : V, (x ∈ Finset.univ \ {r} ↔ x ≠ r) := by
    intro x
    simp [Finset.mem_sdiff, Finset.mem_singleton]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hxr : x = r := by
      by_contra hne
      exact hx ((hmem x).mpr hne)
    subst hxr
    exact treeParent_self _ _
  · intro x _
    exact Finset.mem_univ _
  · refine ⟨fun v => T.dist v r, fun v hv => ?_⟩
    have hvr : v ≠ r := (hmem v).mp hv
    have hex := treeParent_hex hconn hvr
    have hTP : treeParent T r v = Classical.choose hex := by
      unfold treeParent
      rw [dite_eq_right hvr, dite_eq_left hex]
    rw [hTP]
    exact (Classical.choose_spec hex).2

/-- The graph of a tree's parent map is the tree. -/
private theorem fromRel_treeParent {V : Type*} [Fintype V] [DecidableEq V]
    {T : _root_.SimpleGraph V} {r : V} (hT : T.IsTree)
    (hmem : treeParent T r ∈ acyclicMaps Finset.univ {r}) :
    SimpleGraph.fromRel (fun u v => treeParent T r u = v) = T := by
  classical
  have hconn := hT.connected
  have hGtree : (SimpleGraph.fromRel (fun u v => treeParent T r u = v)).IsTree :=
    isTree_fromRel_of_mem hmem
  have hle : SimpleGraph.fromRel (fun u v => treeParent T r u = v) ≤ T := by
    intro u v hadj
    rw [SimpleGraph.fromRel_adj] at hadj
    obtain ⟨hne, hpu | hpv⟩ := hadj
    · have hur : u ≠ r := by
        rintro rfl
        rw [treeParent_self] at hpu
        exact hne hpu
      have hexu := treeParent_hex hconn hur
      have hTPu : treeParent T r u = Classical.choose hexu := by
        unfold treeParent
        rw [dite_eq_right hur, dite_eq_left hexu]
      rw [hTPu] at hpu
      have hch := Classical.choose_spec hexu
      rw [hpu] at hch
      exact hch.1
    · have hvr : v ≠ r := by
        rintro rfl
        rw [treeParent_self] at hpv
        exact hne hpv.symm
      have hexv := treeParent_hex hconn hvr
      have hTPv : treeParent T r v = Classical.choose hexv := by
        unfold treeParent
        rw [dite_eq_right hvr, dite_eq_left hexv]
      rw [hTPv] at hpv
      have hch := Classical.choose_spec hexv
      rw [hpv] at hch
      exact hch.1.symm
  have hcard : (SimpleGraph.fromRel (fun u v => treeParent T r u = v)).edgeFinset.card
      = T.edgeFinset.card := by
    have h1 := hGtree.card_edgeFinset
    have h2 := hT.card_edgeFinset
    omega
  have hsub : (SimpleGraph.fromRel (fun u v => treeParent T r u = v)).edgeFinset
      ⊆ T.edgeFinset := SimpleGraph.edgeFinset_subset_edgeFinset.mpr hle
  have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  exact SimpleGraph.edgeFinset_inj.mp heq

/-- Trees on a vertex type are the same as acyclic parent maps. -/
private theorem card_isTree_eq_card_acyclicMaps {V : Type*} [Fintype V]
    [DecidableEq V] (r : V) : Nat.card { H : _root_.SimpleGraph V // H.IsTree }
      = (acyclicMaps Finset.univ {r}).card := by
  let e : { H : _root_.SimpleGraph V // H.IsTree }
      ≃ { f : V → V // f ∈ acyclicMaps Finset.univ {r} } :=
  { toFun := fun T => ⟨treeParent T.1 r,
      treeParent_mem_acyclicMaps T.2.connected⟩
    invFun := fun f => ⟨SimpleGraph.fromRel (fun u v => f.1 u = v),
      isTree_fromRel_of_mem f.2⟩
    left_inv := fun T =>
      Subtype.ext (fromRel_treeParent T.2 (treeParent_mem_acyclicMaps T.2.connected))
    right_inv := fun f => Subtype.ext (treeParent_fromRel f.2) }
  refine (Nat.card_congr e).trans ?_
  exact Nat.card_eq_finsetCard _

/-- Spanning trees of `⊤` are just trees on the vertex type. -/
private theorem numSpanningTrees_top_eq_card_isTree {V : Type*} [Fintype V]
    (inst : DecidableRel (⊤ : _root_.SimpleGraph V).Adj) :
    @numSpanningTrees V (⊤ : _root_.SimpleGraph V) _ inst
      = Nat.card { H : _root_.SimpleGraph V // H.IsTree } := by
  unfold numSpanningTrees
  apply Nat.card_congr
  let e : { T : (⊤ : _root_.SimpleGraph V).Subgraph // IsSpanningTree T } ≃
      { H : _root_.SimpleGraph V // H.IsTree } :=
  { toFun := fun T => ⟨T.val.spanningCoe,
      (SimpleGraph.Iso.isTree_iff
        (SimpleGraph.Subgraph.spanningCoeEquivCoeOfSpanning T.val T.property.1)).mpr
        T.property.2⟩
    invFun := fun H => ⟨SimpleGraph.toSubgraph H.val le_top, by
      refine ⟨SimpleGraph.toSubgraph.isSpanning H.val le_top, ?_⟩
      have iso : (SimpleGraph.toSubgraph H.val le_top).coe ≃g H.val :=
        { toEquiv := Equiv.subtypeUnivEquiv (fun x => Set.mem_univ x)
          map_rel_iff' := by
            intro a b
            rfl }
      exact (SimpleGraph.Iso.isTree_iff iso).mpr H.property⟩
    left_inv := fun T => by
      apply Subtype.ext
      apply SimpleGraph.Subgraph.ext
      · rw [SimpleGraph.Subgraph.isSpanning_iff.mp T.property.1]
        rfl
      · rfl
    right_inv := fun H => by
      apply Subtype.ext
      apply SimpleGraph.ext
      rfl }
  exact e

/--
**Cayley's formula.** For every natural number $n \ge 2$, the complete graph on $n$ vertices has
exactly $n^{n-2}$ spanning trees.

Proves `Wanted` entry `cayley_formula`.

Source: A. Cayley, "A theorem on trees", Quarterly Journal of Pure and
Applied Mathematics 23 (1889), 376-378.
-/
theorem cayley_formula :
    ∀ {n : ℕ}, 2 ≤ n → numSpanningTrees (⊤ : _root_.SimpleGraph (Fin n)) = n ^ (n - 2) := by
  intro n hn
  classical
  have hnpos : 0 < n := by omega
  set r : Fin n := ⟨0, by omega⟩
  rw [numSpanningTrees_top_eq_card_isTree,
    card_isTree_eq_card_acyclicMaps (V := Fin n) r]
  have hN7 := card_acyclicMaps_mul (U := Finset.univ) (R := {r})
    (Finset.subset_univ _)
  rw [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at hN7
  have hexp : n - 1 = (n - 2) + 1 := by omega
  rw [hexp, pow_succ, one_mul] at hN7
  exact Nat.eq_of_mul_eq_mul_right hnpos hN7

end MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted
end
