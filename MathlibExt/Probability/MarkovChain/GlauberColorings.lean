/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ProbabilityMassFunction.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.InformationTheory.Hamming

open scoped ENNReal

@[expose] public section



/-! # Glauber dynamics for proper colorings

One coupled Glauber (heat-bath with rejection) step contracts the
expected Hamming distance between two proper colorings by the
factor `1 - 1/n + 3Δ/(n q)`. The constant is `3Δ`, not the `2Δ`
of Jerrum's available-color coupling: for the rejection coupling
a disagreeing vertex can also spread disagreement to its
neighbors, and the bound above is what the counting gives (it is
tight on two-vertex examples; an earlier draft of this statement
with `2Δ` was refuted by a machine-checked counterexample during
this work). Combined with path coupling, this gives mixing in
`O(n log n)` for `q > 3Δ`. This is roadmap package ML-28 of the
Atlas TCS canon roadmap.

Source: Jerrum (1995); Dyer and Greenhill (1999).
-/

open Finset

/-- A coloring is proper for the adjacency relation `adj` if
adjacent vertices get different colors. -/
def IsProper {n q : ℕ} (adj : Fin n → Fin n → Bool) (c : Fin n → Fin q) : Prop :=
  ∀ i j, adj i j = true → c i ≠ c j


open Classical in
/-- One Glauber (heat-bath with rejection) proposal: pick a uniform
site `i` and a uniform color `col`; move to the updated coloring if
it is still proper, else stay. -/
noncomputable def glauberStep {n q : ℕ} [Nonempty (Fin n)] [Nonempty (Fin q)] (adj : Fin n → Fin n → Bool)
    (c : Fin n → Fin q) : PMF (Fin n → Fin q) :=
  (PMF.uniformFintype (Fin n)).bind fun i =>
    (PMF.uniformFintype (Fin q)).bind fun col =>
      PMF.pure (if IsProper adj (Function.update c i col) then
        Function.update c i col else c)

open Classical in
/-- The synchronous coupling of two Glauber steps: same site, same
proposed color, applied to both colorings with their own rejection
tests. -/
noncomputable def glauberCouple {n q : ℕ} [Nonempty (Fin n)] [Nonempty (Fin q)] (adj : Fin n → Fin n → Bool)
    (c d : Fin n → Fin q) : PMF ((Fin n → Fin q) × (Fin n → Fin q)) :=
  (PMF.uniformFintype (Fin n)).bind fun i =>
    (PMF.uniformFintype (Fin q)).bind fun col =>
      PMF.pure ((if IsProper adj (Function.update c i col) then
          Function.update c i col else c),
        (if IsProper adj (Function.update d i col) then
          Function.update d i col else d))

/-- The first marginal of the synchronous coupling is the Glauber step. -/
theorem glauberCouple_map_fst {n q : ℕ} [Nonempty (Fin n)] [Nonempty (Fin q)]
    (adj : Fin n → Fin n → Bool) (c d : Fin n → Fin q) :
    (glauberCouple adj c d).map Prod.fst = glauberStep adj c := by
  simp [glauberCouple, glauberStep, PMF.map_bind, PMF.pure_map]

/-- The second marginal of the synchronous coupling is the Glauber step. -/
theorem glauberCouple_map_snd {n q : ℕ} [Nonempty (Fin n)] [Nonempty (Fin q)]
    (adj : Fin n → Fin n → Bool) (c d : Fin n → Fin q) :
    (glauberCouple adj c d).map Prod.snd = glauberStep adj d := by
  simp [glauberCouple, glauberStep, PMF.map_bind, PMF.pure_map]


private lemma uniform_toReal {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    ((PMF.uniformFintype α) a).toReal = 1 / (Fintype.card α : ℝ) := by
  simp [PMF.uniformFintype_apply]

private lemma uniform_ne_top {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    (PMF.uniformFintype α) a ≠ ⊤ := by
  simp [PMF.uniformFintype_apply, Fintype.card_pos.ne']

private lemma pure_toReal_dec {β : Type*} [DecidableEq β] (x z : β) :
    ((PMF.pure x) z).toReal = (if z = x then (1 : ℝ) else 0) := by
  rw [PMF.pure_apply]
  by_cases h : z = x
  · simp [h]
  · simp [h]

private lemma expect_single {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (g : α → β) (F : β → ℝ) :
    (∑ z, (((PMF.uniformFintype α).bind (fun a => PMF.pure (g a))) z).toReal * F z)
      = (1 / (Fintype.card α : ℝ)) * ∑ a, F (g a) := by
  have hbind : ∀ z : β, (((PMF.uniformFintype α).bind (fun a => PMF.pure (g a))) z).toReal
      = ∑ a, (((PMF.uniformFintype α) a).toReal * ((PMF.pure (g a)) z).toReal) := by
    intro z
    rw [PMF.bind_apply]
    rw [tsum_fintype]
    rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro a _
      rw [ENNReal.toReal_mul]
    · intro a _
      apply ENNReal.mul_ne_top
      · exact uniform_ne_top a
      · exact PMF.apply_ne_top _ _
  calc (∑ z, (((PMF.uniformFintype α).bind (fun a => PMF.pure (g a))) z).toReal * F z)
      = ∑ z, ((∑ a, (((PMF.uniformFintype α) a).toReal * ((PMF.pure (g a)) z).toReal)) * F z) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [hbind z]
    _ = ∑ z, ∑ a, ((((PMF.uniformFintype α) a).toReal * ((PMF.pure (g a)) z).toReal) * F z) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.sum_mul]
    _ = ∑ a, ∑ z, ((((PMF.uniformFintype α) a).toReal * ((PMF.pure (g a)) z).toReal) * F z) := by
        rw [Finset.sum_comm]
    _ = ∑ a, (((PMF.uniformFintype α) a).toReal * F (g a)) := by
        apply Finset.sum_congr rfl
        intro a _
        have hinner : ∀ z ∈ (Finset.univ : Finset β), ((((PMF.uniformFintype α) a).toReal * ((PMF.pure (g a)) z).toReal) * F z)
            = (if z = g a then (((PMF.uniformFintype α) a).toReal * F (g a)) else 0) := by
          intro z _
          rw [pure_toReal_dec]
          by_cases hz : z = g a
          · simp [hz]
          · simp [hz]
        rw [Finset.sum_congr rfl hinner]
        rw [Finset.sum_ite_eq' Finset.univ (g a) (fun _ => ((PMF.uniformFintype α) a).toReal * F (g a))]
        simp
    _ = (1 / (Fintype.card α : ℝ)) * ∑ a, F (g a) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [uniform_toReal]

private lemma expect_bind {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : PMF α) (f : α → PMF β) (F : β → ℝ) :
    (∑ z, ((p.bind f z).toReal * F z))
      = ∑ a, ((p a).toReal * (∑ z, ((f a z).toReal * F z))) := by
  have hbind : ∀ z : β, ((p.bind f z).toReal)
      = ∑ a, ((p a).toReal * (f a z).toReal) := by
    intro z
    rw [PMF.bind_apply]
    rw [tsum_fintype]
    rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro a _
      rw [ENNReal.toReal_mul]
    · intro a _
      apply ENNReal.mul_ne_top
      · exact PMF.apply_ne_top _ _
      · exact PMF.apply_ne_top _ _
  calc (∑ z, ((p.bind f z).toReal * F z))
      = ∑ z, ((∑ a, ((p a).toReal * (f a z).toReal)) * F z) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [hbind z]
    _ = ∑ z, ∑ a, (((p a).toReal * (f a z).toReal) * F z) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.sum_mul]
    _ = ∑ a, ∑ z, (((p a).toReal * (f a z).toReal) * F z) := by
        rw [Finset.sum_comm]
    _ = ∑ a, ((p a).toReal * (∑ z, ((f a z).toReal * F z))) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring

open Classical in
theorem expected_glauberCouple {n q : ℕ} [Nonempty (Fin n)] [Nonempty (Fin q)]
    (adj : Fin n → Fin n → Bool) (c d : Fin n → Fin q)
    (F : ((Fin n → Fin q) × (Fin n → Fin q)) → ℝ) :
    (∑ z, ((glauberCouple adj c d z).toReal * F z))
      = (1 / ((Fintype.card (Fin n) : ℝ) * (Fintype.card (Fin q) : ℝ)))
        * ∑ i, ∑ col, F ((if IsProper adj (Function.update c i col) then
            Function.update c i col else c),
          (if IsProper adj (Function.update d i col) then
            Function.update d i col else d)) := by
  unfold glauberCouple
  rw [expect_bind]
  have hinner : ∀ i : Fin n, (∑ z, ((((PMF.uniformFintype (Fin q)).bind fun col =>
      PMF.pure ((if IsProper adj (Function.update c i col) then
          Function.update c i col else c),
        (if IsProper adj (Function.update d i col) then
          Function.update d i col else d))) z).toReal * F z))
      = (1 / (Fintype.card (Fin q) : ℝ)) * ∑ col, F ((if IsProper adj (Function.update c i col) then
            Function.update c i col else c),
          (if IsProper adj (Function.update d i col) then
            Function.update d i col else d)) := by
    intro i
    exact expect_single (fun col => ((if IsProper adj (Function.update c i col) then
            Function.update c i col else c),
          (if IsProper adj (Function.update d i col) then
            Function.update d i col else d))) F
  calc (∑ a, (((PMF.uniformFintype (Fin n)) a).toReal *
        (∑ z, ((((PMF.uniformFintype (Fin q)).bind fun col =>
          PMF.pure ((if IsProper adj (Function.update c a col) then
              Function.update c a col else c),
            (if IsProper adj (Function.update d a col) then
              Function.update d a col else d))) z).toReal * F z))))
      = ∑ i, (((PMF.uniformFintype (Fin n)) i).toReal *
        ((1 / (Fintype.card (Fin q) : ℝ)) * ∑ col, F ((if IsProper adj (Function.update c i col) then
            Function.update c i col else c),
          (if IsProper adj (Function.update d i col) then
            Function.update d i col else d)))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hinner i]
    _ = ∑ i, ((1 / (Fintype.card (Fin n) : ℝ)) *
        ((1 / (Fintype.card (Fin q) : ℝ)) * ∑ col, F ((if IsProper adj (Function.update c i col) then
            Function.update c i col else c),
          (if IsProper adj (Function.update d i col) then
            Function.update d i col else d)))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [uniform_toReal]
    _ = (1 / ((Fintype.card (Fin n) : ℝ) * (Fintype.card (Fin q) : ℝ)))
        * ∑ i, ∑ col, F ((if IsProper adj (Function.update c i col) then
            Function.update c i col else c),
          (if IsProper adj (Function.update d i col) then
            Function.update d i col else d)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

private lemma no_self {n q : ℕ} (adj : Fin n → Fin n → Bool) (c : Fin n → Fin q)
    (hc : IsProper adj c) (i : Fin n) : adj i i ≠ true := by
  intro h
  have hne := hc i i h
  exact hne rfl

private lemma accept_iff {n q : ℕ} (adj : Fin n → Fin n → Bool)
    (hadj : ∀ i j, adj i j = true → adj j i = true)
    (c : Fin n → Fin q) (hc : IsProper adj c) (i : Fin n) (col : Fin q) :
    IsProper adj (Function.update c i col) ↔
      (∀ j, adj i j = true → j ≠ i → col ≠ c j) ∧ adj i i ≠ true := by
  constructor
  · intro h
    constructor
    · intro j hij hji
      have hupd : Function.update c i col i ≠ Function.update c i col j := h i j hij
      rw [Function.update_self] at hupd
      have hj : Function.update c i col j = c j := Function.update_of_ne hji col c
      rw [hj] at hupd
      exact hupd
    · exact no_self adj c hc i
  · intro h p q hpq
    obtain ⟨havoid, hnoself⟩ := h
    by_cases hpi : p = i
    · by_cases hqi : q = i
      · exfalso
        rw [hpi, hqi] at hpq
        exact hnoself hpq
      · have h1 : Function.update c i col p = col := by
          rw [hpi]
          exact Function.update_self i col c
        have h2 : Function.update c i col q = c q := Function.update_of_ne hqi col c
        rw [h1, h2]
        have hpq' : adj i q = true := by rw [← hpi]; exact hpq
        exact havoid q hpq' hqi
    · by_cases hqi : q = i
      · have h1 : Function.update c i col p = c p := Function.update_of_ne hpi col c
        have h2 : Function.update c i col q = col := by
          rw [hqi]
          exact Function.update_self i col c
        rw [h1, h2]
        have hpq' : adj p i = true := by rw [hqi] at hpq; exact hpq
        have hsymm : adj i p = true := hadj p i hpq'
        have hne : col ≠ c p := havoid p hsymm hpi
        exact Ne.symm hne
      · have h1 : Function.update c i col p = c p := Function.update_of_ne hpi col c
        have h2 : Function.update c i col q = c q := Function.update_of_ne hqi col c
        rw [h1, h2]
        exact hc p q hpq

private def neigh {n : ℕ} (adj : Fin n → Fin n → Bool) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => adj i j = true)

private def blockedA {n q : ℕ} (adj : Fin n → Fin n → Bool) (c : Fin n → Fin q) (i : Fin n) : Finset (Fin q) :=
  (neigh adj i).image c

private def blockedB {n q : ℕ} (adj : Fin n → Fin n → Bool) (d : Fin n → Fin q) (i : Fin n) : Finset (Fin q) :=
  (neigh adj i).image d

private lemma mem_blockedA {n q : ℕ} (adj : Fin n → Fin n → Bool) (c : Fin n → Fin q) (i : Fin n) (col : Fin q) :
    col ∈ blockedA adj c i ↔ ∃ j, adj i j = true ∧ c j = col := by
  unfold blockedA neigh
  constructor
  · intro h
    obtain ⟨j, hj, hcj⟩ := Finset.mem_image.mp h
    have hadj : adj i j = true := by simp at hj; exact hj
    exact ⟨j, hadj, hcj⟩
  · intro h
    obtain ⟨j, hadj, hcj⟩ := h
    apply Finset.mem_image.mpr
    exact ⟨j, by simp [hadj], hcj⟩

private lemma mem_blockedB {n q : ℕ} (adj : Fin n → Fin n → Bool) (d : Fin n → Fin q) (i : Fin n) (col : Fin q) :
    col ∈ blockedB adj d i ↔ ∃ j, adj i j = true ∧ d j = col := by
  unfold blockedB neigh
  constructor
  · intro h
    obtain ⟨j, hj, hcj⟩ := Finset.mem_image.mp h
    have hadj : adj i j = true := by simp at hj; exact hj
    exact ⟨j, hadj, hcj⟩
  · intro h
    obtain ⟨j, hadj, hcj⟩ := h
    apply Finset.mem_image.mpr
    exact ⟨j, by simp [hadj], hcj⟩

private lemma accept_eq_notmem {n q : ℕ} (adj : Fin n → Fin n → Bool)
    (hadj : ∀ i j, adj i j = true → adj j i = true)
    (c : Fin n → Fin q) (hc : IsProper adj c) (i : Fin n) (col : Fin q) :
    IsProper adj (Function.update c i col) ↔ col ∉ blockedA adj c i := by
  rw [accept_iff adj hadj c hc i col]
  have hns : adj i i ≠ true := no_self adj c hc i
  constructor
  · intro h hmem
    obtain ⟨havoid, _⟩ := h
    rw [mem_blockedA] at hmem
    obtain ⟨j, hadj', hcj⟩ := hmem
    have hji : j ≠ i := by
      intro heq
      rw [heq] at hadj'
      exact hns hadj'
    have hne : col ≠ c j := havoid j hadj' hji
    rw [hcj] at hne
    exact hne rfl
  · intro h
    constructor
    · intro j hij hji heq
      apply h
      rw [mem_blockedA]
      exact ⟨j, hij, heq.symm⟩
    · exact hns

private lemma accept_eq_notmemB {n q : ℕ} (adj : Fin n → Fin n → Bool)
    (hadj : ∀ i j, adj i j = true → adj j i = true)
    (d : Fin n → Fin q) (hd : IsProper adj d) (i : Fin n) (col : Fin q) :
    IsProper adj (Function.update d i col) ↔ col ∉ blockedB adj d i := by
  rw [accept_iff adj hadj d hd i col]
  have hns : adj i i ≠ true := no_self adj d hd i
  constructor
  · intro h hmem
    obtain ⟨havoid, _⟩ := h
    rw [mem_blockedB] at hmem
    obtain ⟨j, hadj', hcj⟩ := hmem
    have hji : j ≠ i := by
      intro heq
      rw [heq] at hadj'
      exact hns hadj'
    have hne : col ≠ d j := havoid j hadj' hji
    rw [hcj] at hne
    exact hne rfl
  · intro h
    constructor
    · intro j hij hji heq
      apply h
      rw [mem_blockedB]
      exact ⟨j, hij, heq.symm⟩
    · exact hns

private lemma self_not_blockedA {n q : ℕ} (adj : Fin n → Fin n → Bool)
    (c : Fin n → Fin q) (hc : IsProper adj c) (i : Fin n) :
    c i ∉ blockedA adj c i := by
  rw [mem_blockedA]
  intro h
  obtain ⟨j, hadj, hcj⟩ := h
  have hne : c i ≠ c j := hc i j hadj
  rw [hcj] at hne
  exact hne rfl

private lemma self_not_blockedB {n q : ℕ} (adj : Fin n → Fin n → Bool)
    (d : Fin n → Fin q) (hd : IsProper adj d) (i : Fin n) :
    d i ∉ blockedB adj d i := by
  rw [mem_blockedB]
  intro h
  obtain ⟨j, hadj, hcj⟩ := h
  have hne : d i ≠ d j := hd i j hadj
  rw [hcj] at hne
  exact hne rfl

private lemma blocked_ne_selfA {n q : ℕ} (adj : Fin n → Fin n → Bool)
    (c : Fin n → Fin q) (hc : IsProper adj c) (i : Fin n) (col : Fin q)
    (hmem : col ∈ blockedA adj c i) : col ≠ c i := by
  intro heq
  rw [heq] at hmem
  exact self_not_blockedA adj c hc i hmem

private lemma blocked_ne_selfB {n q : ℕ} (adj : Fin n → Fin n → Bool)
    (d : Fin n → Fin q) (hd : IsProper adj d) (i : Fin n) (col : Fin q)
    (hmem : col ∈ blockedB adj d i) : col ≠ d i := by
  intro heq
  rw [heq] at hmem
  exact self_not_blockedB adj d hd i hmem

-- Helper: value at i after update

open Classical in
private lemma upd_val_c {n q : ℕ} (adj : Fin n → Fin n → Bool) (c : Fin n → Fin q)
    (i : Fin n) (col : Fin q) :
    (if IsProper adj (Function.update c i col) then Function.update c i col else c) i =
      (if IsProper adj (Function.update c i col) then col else c i) := by
  by_cases h : IsProper adj (Function.update c i col)
  · simp [h, Function.update_self]
  · simp [h]

open Classical in
private lemma upd_val_d {n q : ℕ} (adj : Fin n → Fin n → Bool) (d : Fin n → Fin q)
    (i : Fin n) (col : Fin q) :
    (if IsProper adj (Function.update d i col) then Function.update d i col else d) i =
      (if IsProper adj (Function.update d i col) then col else d i) := by
  by_cases h : IsProper adj (Function.update d i col)
  · simp [h, Function.update_self]
  · simp [h]

open Classical in
private lemma after_disagreeing {n q : ℕ} (adj : Fin n → Fin n → Bool)
    (hadj : ∀ i j, adj i j = true → adj j i = true)
    (c d : Fin n → Fin q) (hc : IsProper adj c) (hd : IsProper adj d)
    (i : Fin n) (col : Fin q) (hdis : c i ≠ d i) :
    let c' := (if IsProper adj (Function.update c i col) then Function.update c i col else c)
    let d' := (if IsProper adj (Function.update d i col) then Function.update d i col else d)
    (c' i ≠ d' i ↔ (col ∈ blockedA adj c i ∨ col ∈ blockedB adj d i)) := by
  intro c' d'
  have hacc_c := (accept_eq_notmem adj hadj c hc i col)
  have hacc_d := (accept_eq_notmemB adj hadj d hd i col)
  by_cases hCc : IsProper adj (Function.update c i col)
  · by_cases hDd : IsProper adj (Function.update d i col)
    · have hc_i : c' i = col := by
        simp only [c']
        simp [hCc, Function.update_self]
      have hd_i : d' i = col := by
        simp only [d']
        simp [hDd, Function.update_self]
      have hnmemA : col ∉ blockedA adj c i := hacc_c.mp hCc
      have hnmemB : col ∉ blockedB adj d i := hacc_d.mp hDd
      constructor
      · intro hne
        rw [hc_i, hd_i] at hne
        exact absurd rfl hne
      · intro hor
        cases hor with
        | inl hmem => exact absurd hmem hnmemA
        | inr hmem => exact absurd hmem hnmemB
    · have hc_i : c' i = col := by
        simp only [c']
        simp [hCc, Function.update_self]
      have hd_i : d' i = d i := by
        simp only [d']
        simp [hDd]
      have hmemB : col ∈ blockedB adj d i := by
        by_contra hnmem
        exact hDd (hacc_d.mpr hnmem)
      have hne_col : col ≠ d i := blocked_ne_selfB adj d hd i col hmemB
      constructor
      · intro _
        exact Or.inr hmemB
      · intro _
        rw [hc_i, hd_i]
        exact hne_col
  · by_cases hDd : IsProper adj (Function.update d i col)
    · have hc_i : c' i = c i := by
        simp only [c']
        simp [hCc]
      have hd_i : d' i = col := by
        simp only [d']
        simp [hDd, Function.update_self]
      have hmemA : col ∈ blockedA adj c i := by
        by_contra hnmem
        exact hCc (hacc_c.mpr hnmem)
      have hne_col : c i ≠ col := Ne.symm (blocked_ne_selfA adj c hc i col hmemA)
      constructor
      · intro _
        exact Or.inl hmemA
      · intro _
        rw [hc_i, hd_i]
        exact hne_col
    · have hc_i : c' i = c i := by
        simp only [c']
        simp [hCc]
      have hd_i : d' i = d i := by
        simp only [d']
        simp [hDd]
      have hmemA : col ∈ blockedA adj c i := by
        by_contra hnmem
        exact hCc (hacc_c.mpr hnmem)
      constructor
      · intro _
        exact Or.inl hmemA
      · intro _
        rw [hc_i, hd_i]
        exact hdis

open Classical in
private lemma after_agreeing {n q : ℕ} (adj : Fin n → Fin n → Bool)
    (hadj : ∀ i j, adj i j = true → adj j i = true)
    (c d : Fin n → Fin q) (hc : IsProper adj c) (hd : IsProper adj d)
    (i : Fin n) (col : Fin q) (hagr : c i = d i) :
    let c' := (if IsProper adj (Function.update c i col) then Function.update c i col else c)
    let d' := (if IsProper adj (Function.update d i col) then Function.update d i col else d)
    (c' i ≠ d' i ↔ ((col ∈ blockedA adj c i ∧ col ∉ blockedB adj d i) ∨
      (col ∉ blockedA adj c i ∧ col ∈ blockedB adj d i))) := by
  intro c' d'
  have hacc_c := (accept_eq_notmem adj hadj c hc i col)
  have hacc_d := (accept_eq_notmemB adj hadj d hd i col)
  by_cases hCc : IsProper adj (Function.update c i col)
  · by_cases hDd : IsProper adj (Function.update d i col)
    · have hc_i : c' i = col := by
        simp only [c']
        simp [hCc, Function.update_self]
      have hd_i : d' i = col := by
        simp only [d']
        simp [hDd, Function.update_self]
      have hnmemA : col ∉ blockedA adj c i := hacc_c.mp hCc
      have hnmemB : col ∉ blockedB adj d i := hacc_d.mp hDd
      constructor
      · intro hne
        rw [hc_i, hd_i] at hne
        exact absurd rfl hne
      · intro hor
        cases hor with
        | inl h => exact absurd h.1 hnmemA
        | inr h => exact absurd h.2 hnmemB
    · have hc_i : c' i = col := by
        simp only [c']
        simp [hCc, Function.update_self]
      have hd_i : d' i = d i := by
        simp only [d']
        simp [hDd]
      have hnmemA : col ∉ blockedA adj c i := hacc_c.mp hCc
      have hmemB : col ∈ blockedB adj d i := by
        by_contra hnmem
        exact hDd (hacc_d.mpr hnmem)
      have hne_col : col ≠ d i := blocked_ne_selfB adj d hd i col hmemB
      constructor
      · intro _
        exact Or.inr ⟨hnmemA, hmemB⟩
      · intro _
        rw [hc_i, hd_i]
        exact hne_col
  · by_cases hDd : IsProper adj (Function.update d i col)
    · have hc_i : c' i = c i := by
        simp only [c']
        simp [hCc]
      have hd_i : d' i = col := by
        simp only [d']
        simp [hDd, Function.update_self]
      have hmemA : col ∈ blockedA adj c i := by
        by_contra hnmem
        exact hCc (hacc_c.mpr hnmem)
      have hnmemB : col ∉ blockedB adj d i := hacc_d.mp hDd
      have hne_col : c i ≠ col := Ne.symm (blocked_ne_selfA adj c hc i col hmemA)
      constructor
      · intro _
        exact Or.inl ⟨hmemA, hnmemB⟩
      · intro _
        rw [hc_i, hd_i]
        exact hne_col
    · have hc_i : c' i = c i := by
        simp only [c']
        simp [hCc]
      have hd_i : d' i = d i := by
        simp only [d']
        simp [hDd]
      have hmemA : col ∈ blockedA adj c i := by
        by_contra hnmem
        exact hCc (hacc_c.mpr hnmem)
      have hmemB : col ∈ blockedB adj d i := by
        by_contra hnmem
        exact hDd (hacc_d.mpr hnmem)
      constructor
      · intro hne
        rw [hc_i, hd_i, hagr] at hne
        exact absurd rfl hne
      · intro hor
        cases hor with
        | inl h => exact absurd hmemB h.2
        | inr h => exact absurd hmemA h.1

open Classical in
private lemma update_other {n q : ℕ} (adj : Fin n → Fin n → Bool) (c : Fin n → Fin q)
    (i : Fin n) (col : Fin q) (j : Fin n) (hji : j ≠ i) :
    (if IsProper adj (Function.update c i col) then Function.update c i col else c) j = c j := by
  by_cases h : IsProper adj (Function.update c i col)
  · simp [h, Function.update_of_ne hji]
  · simp [h]

open Classical in
private lemma hamming_update_eq {n q : ℕ} (adj : Fin n → Fin n → Bool)
    (c d : Fin n → Fin q) (i : Fin n) (col : Fin q) :
    let c' := (if IsProper adj (Function.update c i col) then Function.update c i col else c)
    let d' := (if IsProper adj (Function.update d i col) then Function.update d i col else d)
    ((hammingDist c' d' : ℕ) : ℝ) = ((hammingDist c d : ℕ) : ℝ) - (if c i ≠ d i then (1 : ℝ) else 0) + (if c' i ≠ d' i then (1 : ℝ) else 0) := by
  intro c' d'
  -- rewrite ((hammingDist as sums : ℕ) : ℝ)
  have hcard : ∀ (a b : Fin n → Fin q), ((hammingDist a b : ℕ) : ℝ) = ∑ j, (if a j ≠ b j then (1 : ℝ) else 0) := by
    intro a b
    unfold hammingDist
    rw [Finset.card_filter]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : a j ≠ b j
    · simp [hj]
    · simp [hj]
  rw [hcard c' d', hcard c d]
  -- sums differ only at i
  have hmem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have herase : ∀ j ∈ (Finset.univ.erase i : Finset (Fin n)),
      (if c' j ≠ d' j then (1 : ℝ) else 0) = (if c j ≠ d j then (1 : ℝ) else 0) := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hc' : c' j = c j := update_other adj c i col j hji
    have hd' : d' j = d j := update_other adj d i col j hji
    by_cases h : c j ≠ d j
    · have h' : c' j ≠ d' j := by rw [hc', hd']; exact h
      simp [h, h']
    · have h' : ¬ (c' j ≠ d' j) := by rw [hc', hd']; exact h
      simp [h, h']
  have h1 := Finset.add_sum_erase Finset.univ (fun j => (if c' j ≠ d' j then (1 : ℝ) else 0)) hmem
  have h2 := Finset.add_sum_erase Finset.univ (fun j => (if c j ≠ d j then (1 : ℝ) else 0)) hmem
  have hsum_eq : (∑ x ∈ Finset.univ.erase i, (if c' x ≠ d' x then (1 : ℝ) else 0))
      = ∑ x ∈ Finset.univ.erase i, (if c x ≠ d x then (1 : ℝ) else 0) :=
    Finset.sum_congr rfl herase
  -- from h1, h2 derive equality
  have h1' : (∑ x ∈ Finset.univ, (if c' x ≠ d' x then (1 : ℝ) else 0))
      = (if c' i ≠ d' i then (1 : ℝ) else 0) + ∑ x ∈ Finset.univ.erase i, (if c' x ≠ d' x then (1 : ℝ) else 0) := h1.symm
  have h2' : (∑ x ∈ Finset.univ, (if c x ≠ d x then (1 : ℝ) else 0))
      = (if c i ≠ d i then (1 : ℝ) else 0) + ∑ x ∈ Finset.univ.erase i, (if c x ≠ d x then (1 : ℝ) else 0) := h2.symm
  rw [h1', h2', hsum_eq]
  ring

private def disNeigh {n q : ℕ} (adj : Fin n → Fin n → Bool) (c d : Fin n → Fin q) (i : Fin n) : Finset (Fin n) :=
  (neigh adj i).filter (fun j => c j ≠ d j)

private lemma sdiffB_subset {n q : ℕ} (adj : Fin n → Fin n → Bool) (c d : Fin n → Fin q)
    (i : Fin n) : (blockedB adj d i \ blockedA adj c i) ⊆ (disNeigh adj c d i).image d := by
  intro b hb
  have hbmem := Finset.mem_sdiff.mp hb
  obtain ⟨hbB, hbnotA⟩ := hbmem
  rw [mem_blockedB] at hbB
  obtain ⟨j, hadj, hdj⟩ := hbB
  apply Finset.mem_image.mpr
  refine ⟨j, ?_, hdj⟩
  unfold disNeigh neigh
  simp [hadj]
  intro heq
  apply hbnotA
  rw [mem_blockedA]
  exact ⟨j, hadj, heq.trans hdj⟩

private lemma sdiffA_subset {n q : ℕ} (adj : Fin n → Fin n → Bool) (c d : Fin n → Fin q)
    (i : Fin n) : (blockedA adj c i \ blockedB adj d i) ⊆ (disNeigh adj c d i).image c := by
  intro a ha
  have hamem := Finset.mem_sdiff.mp ha
  obtain ⟨haA, hanotB⟩ := hamem
  rw [mem_blockedA] at haA
  obtain ⟨j, hadj, hcj⟩ := haA
  apply Finset.mem_image.mpr
  refine ⟨j, ?_, hcj⟩
  unfold disNeigh neigh
  simp [hadj]
  intro heq
  apply hanotB
  rw [mem_blockedB]
  exact ⟨j, hadj, heq.symm.trans hcj⟩

private lemma card_sdiffB_le {n q : ℕ} (adj : Fin n → Fin n → Bool) (c d : Fin n → Fin q) (i : Fin n) :
    (blockedB adj d i \ blockedA adj c i).card ≤ (disNeigh adj c d i).card := by
  calc (blockedB adj d i \ blockedA adj c i).card
      ≤ ((disNeigh adj c d i).image d).card := Finset.card_le_card (sdiffB_subset adj c d i)
    _ ≤ (disNeigh adj c d i).card := Finset.card_image_le

private lemma card_sdiffA_le {n q : ℕ} (adj : Fin n → Fin n → Bool) (c d : Fin n → Fin q) (i : Fin n) :
    (blockedA adj c i \ blockedB adj d i).card ≤ (disNeigh adj c d i).card := by
  calc (blockedA adj c i \ blockedB adj d i).card
      ≤ ((disNeigh adj c d i).image c).card := Finset.card_le_card (sdiffA_subset adj c d i)
    _ ≤ (disNeigh adj c d i).card := Finset.card_image_le

private lemma card_blockedA_le {n q : ℕ} (adj : Fin n → Fin n → Bool) (c : Fin n → Fin q) (i : Fin n)
    (Δ : ℕ) (hdeg : ∀ i, (Finset.univ.filter (fun j => adj i j = true)).card ≤ Δ) :
    (blockedA adj c i).card ≤ Δ := by
  unfold blockedA neigh
  calc ((Finset.univ.filter (fun j => adj i j = true)).image c).card
      ≤ (Finset.univ.filter (fun j => adj i j = true)).card := Finset.card_image_le
    _ ≤ Δ := hdeg i

private lemma card_union_le_add {n q : ℕ} (adj : Fin n → Fin n → Bool) (c d : Fin n → Fin q) (i : Fin n)
    (Δ : ℕ) (hdeg : ∀ i, (Finset.univ.filter (fun j => adj i j = true)).card ≤ Δ) :
    (blockedA adj c i ∪ blockedB adj d i).card ≤ Δ + (disNeigh adj c d i).card := by
  have h_eq : blockedA adj c i ∪ blockedB adj d i = blockedA adj c i ∪ (blockedB adj d i \ blockedA adj c i) := by
    rw [Finset.union_sdiff_self_eq_union]
  rw [h_eq]
  calc (blockedA adj c i ∪ (blockedB adj d i \ blockedA adj c i)).card
      ≤ (blockedA adj c i).card + (blockedB adj d i \ blockedA adj c i).card :=
        Finset.card_union_le _ _
    _ ≤ Δ + (disNeigh adj c d i).card := by
        apply Nat.add_le_add
        · exact card_blockedA_le adj c i Δ hdeg
        · exact card_sdiffB_le adj c d i

private lemma card_symm_le {n q : ℕ} (adj : Fin n → Fin n → Bool) (c d : Fin n → Fin q) (i : Fin n) :
    ((blockedA adj c i \ blockedB adj d i) ∪ (blockedB adj d i \ blockedA adj c i)).card
      ≤ 2 * (disNeigh adj c d i).card := by
  calc ((blockedA adj c i \ blockedB adj d i) ∪ (blockedB adj d i \ blockedA adj c i)).card
      ≤ (blockedA adj c i \ blockedB adj d i).card + (blockedB adj d i \ blockedA adj c i).card :=
        Finset.card_union_le _ _
    _ ≤ (disNeigh adj c d i).card + (disNeigh adj c d i).card := by
        apply Nat.add_le_add
        · exact card_sdiffA_le adj c d i
        · exact card_sdiffB_le adj c d i
    _ = 2 * (disNeigh adj c d i).card := by ring


open Classical in
private lemma per_site_dis {n q : ℕ} [Nonempty (Fin n)] [Nonempty (Fin q)]
    (adj : Fin n → Fin n → Bool)
    (hadj : ∀ i j, adj i j = true → adj j i = true)
    (Δ : ℕ) (hdeg : ∀ i, (Finset.univ.filter (fun j => adj i j = true)).card ≤ Δ)
    (c d : Fin n → Fin q) (hc : IsProper adj c) (hd : IsProper adj d)
    (i : Fin n) (hdis : c i ≠ d i) :
    (∑ col, ((hammingDist (if IsProper adj (Function.update c i col) then Function.update c i col else c) (if IsProper adj (Function.update d i col) then Function.update d i col else d) : ℕ) : ℝ))
      ≤ (q : ℝ) * ((hammingDist c d : ℕ) : ℝ) - (q : ℝ) + (Δ : ℝ) + ((disNeigh adj c d i).card : ℝ) := by
  have hpt : ∀ col : Fin q,
      ((hammingDist (if IsProper adj (Function.update c i col) then Function.update c i col else c) (if IsProper adj (Function.update d i col) then Function.update d i col else d) : ℕ) : ℝ)
      = ((hammingDist c d : ℕ) : ℝ) - 1 + (if (if IsProper adj (Function.update c i col) then Function.update c i col else c) i ≠
          (if IsProper adj (Function.update d i col) then Function.update d i col else d) i then (1 : ℝ) else 0) := by
    intro col
    have hcol := hamming_update_eq adj c d i col
    simp only at hcol
    rw [ite_eq_left hdis] at hcol
    exact hcol
  have hsum_eq : (∑ col, ((hammingDist (if IsProper adj (Function.update c i col) then Function.update c i col else c) (if IsProper adj (Function.update d i col) then Function.update d i col else d) : ℕ) : ℝ))
      = (q : ℝ) * (((hammingDist c d : ℕ) : ℝ) - 1) + ∑ col, (if (if IsProper adj (Function.update c i col) then Function.update c i col else c) i ≠
          (if IsProper adj (Function.update d i col) then Function.update d i col else d) i then (1 : ℝ) else 0) := by
    rw [Finset.sum_congr rfl (fun col _ => hpt col)]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_const]
    simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum_eq]
  have hfilter : (Finset.univ.filter (fun col =>
      (if IsProper adj (Function.update c i col) then Function.update c i col else c) i ≠
        (if IsProper adj (Function.update d i col) then Function.update d i col else d) i))
      = blockedA adj c i ∪ blockedB adj d i := by
    have hcongr : ∀ col ∈ (Finset.univ : Finset (Fin q)),
        (((if IsProper adj (Function.update c i col) then Function.update c i col else c) i ≠
          (if IsProper adj (Function.update d i col) then Function.update d i col else d) i)
          ↔ col ∈ blockedA adj c i ∪ blockedB adj d i) := by
      intro col _
      have haf := after_disagreeing adj hadj c d hc hd i col hdis
      simp only at haf
      rw [haf]
      rw [Finset.mem_union]
    have h1 := Finset.filter_congr hcongr
    rw [Finset.filter_univ_mem] at h1
    exact h1
  have hafter_eq : (∑ col, (if (if IsProper adj (Function.update c i col) then Function.update c i col else c) i ≠
      (if IsProper adj (Function.update d i col) then Function.update d i col else d) i then (1 : ℝ) else 0))
      = (((blockedA adj c i ∪ blockedB adj d i).card : ℕ) : ℝ) := by
    have hboole : (∑ x ∈ (Finset.univ : Finset (Fin q)), (if (if IsProper adj (Function.update c i x) then Function.update c i x else c) i ≠
        (if IsProper adj (Function.update d i x) then Function.update d i x else d) i then (1 : ℝ) else 0))
        = ((((Finset.univ.filter (fun col =>
          (if IsProper adj (Function.update c i col) then Function.update c i col else c) i ≠
            (if IsProper adj (Function.update d i col) then Function.update d i col else d) i)).card : ℕ)) : ℝ) :=
      Finset.sum_boole _ _
    rw [hfilter] at hboole
    simpa using hboole
  rw [hafter_eq]
  have hcard_le : ((blockedA adj c i ∪ blockedB adj d i).card : ℝ) ≤ (Δ : ℝ) + ((disNeigh adj c d i).card : ℝ) := by
    have hnat : (blockedA adj c i ∪ blockedB adj d i).card ≤ Δ + (disNeigh adj c d i).card :=
      card_union_le_add adj c d i Δ hdeg
    calc (((blockedA adj c i ∪ blockedB adj d i).card : ℕ) : ℝ)
        ≤ ((Δ + (disNeigh adj c d i).card : ℕ) : ℝ) := by
          apply Nat.cast_le.mpr
          exact hnat
      _ = (Δ : ℝ) + ((disNeigh adj c d i).card : ℝ) := by
          push_cast
          ring
  calc (q : ℝ) * (((hammingDist c d : ℕ) : ℝ) - 1) + (((blockedA adj c i ∪ blockedB adj d i).card : ℕ) : ℝ)
      ≤ (q : ℝ) * (((hammingDist c d : ℕ) : ℝ) - 1) + ((Δ : ℝ) + ((disNeigh adj c d i).card : ℝ)) := by
        apply add_le_add_right
        exact hcard_le
    _ = (q : ℝ) * ((hammingDist c d : ℕ) : ℝ) - (q : ℝ) + (Δ : ℝ) + ((disNeigh adj c d i).card : ℝ) := by ring

open Classical in
private lemma per_site_agr {n q : ℕ} [Nonempty (Fin n)] [Nonempty (Fin q)]
    (adj : Fin n → Fin n → Bool)
    (hadj : ∀ i j, adj i j = true → adj j i = true)
    (Δ : ℕ) (_hdeg : ∀ i, (Finset.univ.filter (fun j => adj i j = true)).card ≤ Δ)
    (c d : Fin n → Fin q) (hc : IsProper adj c) (hd : IsProper adj d)
    (i : Fin n) (hagr : c i = d i) :
    (∑ col, ((hammingDist (if IsProper adj (Function.update c i col) then Function.update c i col else c) (if IsProper adj (Function.update d i col) then Function.update d i col else d) : ℕ) : ℝ))
      ≤ (q : ℝ) * ((hammingDist c d : ℕ) : ℝ) + 2 * ((disNeigh adj c d i).card : ℝ) := by
  have hnot : ¬ (c i ≠ d i) := fun h => h hagr
  have hpt : ∀ col : Fin q,
      ((hammingDist (if IsProper adj (Function.update c i col) then Function.update c i col else c) (if IsProper adj (Function.update d i col) then Function.update d i col else d) : ℕ) : ℝ)
      = ((hammingDist c d : ℕ) : ℝ) + (if (if IsProper adj (Function.update c i col) then Function.update c i col else c) i ≠
          (if IsProper adj (Function.update d i col) then Function.update d i col else d) i then (1 : ℝ) else 0) := by
    intro col
    have hcol := hamming_update_eq adj c d i col
    simp only at hcol
    rw [ite_eq_right hnot] at hcol
    -- hcol : ((hammingDist ...  : ℕ) : ℝ)= ((hammingDist   : ℕ) : ℝ)- 0 + after; need = ((hammingDist   : ℕ) : ℝ)+ after
    have hsub : ((hammingDist c d : ℕ) : ℝ) - (0 : ℝ) = ((hammingDist c d : ℕ) : ℝ) := by ring
    rw [hsub] at hcol
    exact hcol
  have hsum_eq : (∑ col, ((hammingDist (if IsProper adj (Function.update c i col) then Function.update c i col else c) (if IsProper adj (Function.update d i col) then Function.update d i col else d) : ℕ) : ℝ))
      = (q : ℝ) * ((hammingDist c d : ℕ) : ℝ) + ∑ col, (if (if IsProper adj (Function.update c i col) then Function.update c i col else c) i ≠
          (if IsProper adj (Function.update d i col) then Function.update d i col else d) i then (1 : ℝ) else 0) := by
    rw [Finset.sum_congr rfl (fun col _ => hpt col)]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_const]
    simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum_eq]
  have hfilter : (Finset.univ.filter (fun col =>
      (if IsProper adj (Function.update c i col) then Function.update c i col else c) i ≠
        (if IsProper adj (Function.update d i col) then Function.update d i col else d) i))
      = (blockedA adj c i \ blockedB adj d i) ∪ (blockedB adj d i \ blockedA adj c i) := by
    have hcongr : ∀ col ∈ (Finset.univ : Finset (Fin q)),
        (((if IsProper adj (Function.update c i col) then Function.update c i col else c) i ≠
          (if IsProper adj (Function.update d i col) then Function.update d i col else d) i)
          ↔ col ∈ (blockedA adj c i \ blockedB adj d i) ∪ (blockedB adj d i \ blockedA adj c i)) := by
      intro col _
      have haf := after_agreeing adj hadj c d hc hd i col hagr
      simp only at haf
      constructor
      · intro hafter
        rw [haf] at hafter
        rw [Finset.mem_union]
        cases hafter with
        | inl h =>
          exact Or.inl (Finset.mem_sdiff.mpr h)
        | inr h =>
          obtain ⟨hnA, hmB⟩ := h
          exact Or.inr (Finset.mem_sdiff.mpr ⟨hmB, hnA⟩)
      · intro hmem
        rw [Finset.mem_union] at hmem
        rw [haf]
        cases hmem with
        | inl h =>
          have hm := Finset.mem_sdiff.mp h
          exact Or.inl hm
        | inr h =>
          have hm := Finset.mem_sdiff.mp h
          obtain ⟨hmB, hnA⟩ := hm
          exact Or.inr ⟨hnA, hmB⟩
    have h1 := Finset.filter_congr hcongr
    rw [Finset.filter_univ_mem] at h1
    exact h1
  have hafter_eq : (∑ col, (if (if IsProper adj (Function.update c i col) then Function.update c i col else c) i ≠
      (if IsProper adj (Function.update d i col) then Function.update d i col else d) i then (1 : ℝ) else 0))
      = ((((blockedA adj c i \ blockedB adj d i) ∪ (blockedB adj d i \ blockedA adj c i)).card : ℕ) : ℝ) := by
    have hboole : (∑ x ∈ (Finset.univ : Finset (Fin q)), (if (if IsProper adj (Function.update c i x) then Function.update c i x else c) i ≠
        (if IsProper adj (Function.update d i x) then Function.update d i x else d) i then (1 : ℝ) else 0))
        = ((((Finset.univ.filter (fun col =>
          (if IsProper adj (Function.update c i col) then Function.update c i col else c) i ≠
            (if IsProper adj (Function.update d i col) then Function.update d i col else d) i)).card : ℕ)) : ℝ) :=
      Finset.sum_boole _ _
    rw [hfilter] at hboole
    simpa using hboole
  rw [hafter_eq]
  have hcard_le : ((((blockedA adj c i \ blockedB adj d i) ∪ (blockedB adj d i \ blockedA adj c i)).card : ℕ) : ℝ)
      ≤ 2 * ((disNeigh adj c d i).card : ℝ) := by
    have hnat : ((blockedA adj c i \ blockedB adj d i) ∪ (blockedB adj d i \ blockedA adj c i)).card
        ≤ 2 * (disNeigh adj c d i).card :=
      card_symm_le adj c d i
    calc (((((blockedA adj c i \ blockedB adj d i) ∪ (blockedB adj d i \ blockedA adj c i)).card : ℕ)) : ℝ)
        ≤ ((2 * (disNeigh adj c d i).card : ℕ) : ℝ) := by
          apply Nat.cast_le.mpr
          exact hnat
      _ = 2 * ((disNeigh adj c d i).card : ℝ) := by
          push_cast
          ring
  calc (q : ℝ) * ((hammingDist c d : ℕ) : ℝ) + (((((blockedA adj c i \ blockedB adj d i) ∪ (blockedB adj d i \ blockedA adj c i)).card : ℕ)) : ℝ)
      ≤ (q : ℝ) * ((hammingDist c d : ℕ) : ℝ) + (2 * ((disNeigh adj c d i).card : ℝ)) := by
        apply add_le_add_right
        exact hcard_le

private lemma double_count {n q : ℕ} (adj : Fin n → Fin n → Bool)
    (hadj : ∀ i j, adj i j = true → adj j i = true)
    (Δ : ℕ) (hdeg : ∀ i, (Finset.univ.filter (fun j => adj i j = true)).card ≤ Δ)
    (c d : Fin n → Fin q) :
    (∑ i, (disNeigh adj c d i).card) ≤ Δ * (Finset.univ.filter (fun j => c j ≠ d j)).card := by
  -- Step 1: card as sum over univ with double indicator
  have hcard_eq : ∀ i : Fin n, (disNeigh adj c d i).card
      = ∑ j, (if adj i j = true ∧ c j ≠ d j then 1 else 0) := by
    intro i
    unfold disNeigh neigh
    rw [Finset.card_filter]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hadj_ij : adj i j = true
    · by_cases hdis : c j ≠ d j
      · simp [hadj_ij, hdis]
      · simp [hadj_ij, hdis]
    · simp [hadj_ij]
  -- Step 2: swap sums
  have hsum_swap : (∑ i, ∑ j, (if adj i j = true ∧ c j ≠ d j then 1 else 0))
      = ∑ j, ∑ i, (if adj i j = true ∧ c j ≠ d j then 1 else 0) := Finset.sum_comm
  -- Step 3: inner sum factors disj
  have hinner : ∀ j : Fin n, (∑ i, (if adj i j = true ∧ c j ≠ d j then 1 else 0))
      = (if c j ≠ d j then ∑ i, (if adj i j = true then 1 else 0) else 0) := by
    intro j
    by_cases hdis : c j ≠ d j
    · simp [hdis]
    · simp [hdis]
  -- Step 4: inner adj sum = degree (via symmetry)
  have hdeg_eq : ∀ j : Fin n, (∑ i, (if adj i j = true then 1 else 0))
      = (Finset.univ.filter (fun k => adj j k = true)).card := by
    intro j
    have hsymm : ∀ i : Fin n, (adj i j = true ↔ adj j i = true) := by
      intro i
      constructor
      · exact hadj i j
      · exact hadj j i
    -- filter equality: {i | adj i j} = {i | adj j i}
    have hfilter : (Finset.univ.filter (fun i => adj i j = true))
        = Finset.univ.filter (fun i => adj j i = true) := by
      apply Finset.filter_congr
      intro i _
      exact hsymm i
    have hcard : (Finset.univ.filter (fun i => adj i j = true)).card
        = ∑ i, (if adj i j = true then 1 else 0) := Finset.card_filter _ _
    rw [hfilter] at hcard
    exact hcard.symm
  -- Combine
  calc (∑ i, (disNeigh adj c d i).card)
      = ∑ i, ∑ j, (if adj i j = true ∧ c j ≠ d j then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hcard_eq i
    _ = ∑ j, ∑ i, (if adj i j = true ∧ c j ≠ d j then 1 else 0) := hsum_swap
    _ = ∑ j, (if c j ≠ d j then ∑ i, (if adj i j = true then 1 else 0) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hinner j
    _ = ∑ j, (if c j ≠ d j then (Finset.univ.filter (fun k => adj j k = true)).card else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hdis : c j ≠ d j
        · simp [hdis, hdeg_eq j]
        · simp [hdis]
    _ ≤ ∑ j, (if c j ≠ d j then Δ else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hdis : c j ≠ d j
        · simp [hdis]
          exact hdeg j
        · simp [hdis]
    _ = Δ * (Finset.univ.filter (fun j => c j ≠ d j)).card := by
        have hfilter_sum : (∑ j, (if c j ≠ d j then Δ else 0))
            = ∑ j ∈ Finset.univ.filter (fun j => c j ≠ d j), Δ := by
          rw [Finset.sum_filter]
        rw [hfilter_sum]
        rw [Finset.sum_const]
        simp [Nat.mul_comm]

open Classical in
private lemma total_bound {n q : ℕ} [Nonempty (Fin n)] [Nonempty (Fin q)]
    (adj : Fin n → Fin n → Bool)
    (hadj : ∀ i j, adj i j = true → adj j i = true)
    (Δ : ℕ) (hdeg : ∀ i, (Finset.univ.filter (fun j => adj i j = true)).card ≤ Δ)
    (c d : Fin n → Fin q) (hc : IsProper adj c) (hd : IsProper adj d) :
    (∑ i, ∑ col, ((hammingDist (if IsProper adj (Function.update c i col) then Function.update c i col else c) (if IsProper adj (Function.update d i col) then Function.update d i col else d) : ℕ) : ℝ))
      ≤ (n : ℝ) * (q : ℝ) * ((hammingDist c d : ℕ) : ℝ) - (q : ℝ) * ((hammingDist c d : ℕ) : ℝ) + 3 * (Δ : ℝ) * ((hammingDist c d : ℕ) : ℝ) := by
  -- Step A: per-site bounds combined
  have hper : ∀ i : Fin n,
      (∑ col, ((hammingDist (if IsProper adj (Function.update c i col) then Function.update c i col else c) (if IsProper adj (Function.update d i col) then Function.update d i col else d) : ℕ) : ℝ))
      ≤ (if c i ≠ d i then ((q : ℝ) * ((hammingDist c d : ℕ) : ℝ) - (q : ℝ) + (Δ : ℝ) + ((disNeigh adj c d i).card : ℝ))
          else ((q : ℝ) * ((hammingDist c d : ℕ) : ℝ) + 2 * ((disNeigh adj c d i).card : ℝ))) := by
    intro i
    by_cases hdis : c i ≠ d i
    · simp [hdis]
      exact per_site_dis adj hadj Δ hdeg c d hc hd i hdis
    · simp [hdis]
      have hagr : c i = d i := Classical.byContradiction hdis
      exact per_site_agr adj hadj Δ hdeg c d hc hd i hagr
  have hle1 : (∑ i, ∑ col, ((hammingDist (if IsProper adj (Function.update c i col) then Function.update c i col else c) (if IsProper adj (Function.update d i col) then Function.update d i col else d) : ℕ) : ℝ))
      ≤ ∑ i, (if c i ≠ d i then ((q : ℝ) * ((hammingDist c d : ℕ) : ℝ) - (q : ℝ) + (Δ : ℝ) + ((disNeigh adj c d i).card : ℝ))
          else ((q : ℝ) * ((hammingDist c d : ℕ) : ℝ) + 2 * ((disNeigh adj c d i).card : ℝ))) := by
    apply Finset.sum_le_sum
    intro i _
    exact hper i
  -- Step B: rewrite bound sum as n*q*H + extras
  have hbound_eq : (∑ i, (if c i ≠ d i then ((q : ℝ) * ((hammingDist c d : ℕ) : ℝ) - (q : ℝ) + (Δ : ℝ) + ((disNeigh adj c d i).card : ℝ))
      else ((q : ℝ) * ((hammingDist c d : ℕ) : ℝ) + 2 * ((disNeigh adj c d i).card : ℝ))))
      = (n : ℝ) * (q : ℝ) * ((hammingDist c d : ℕ) : ℝ) + ∑ i, (if c i ≠ d i then (-(q : ℝ) + (Δ : ℝ) + ((disNeigh adj c d i).card : ℝ))
          else (2 * ((disNeigh adj c d i).card : ℝ))) := by
    have hrewrite : ∀ i : Fin n,
        (if c i ≠ d i then ((q : ℝ) * ((hammingDist c d : ℕ) : ℝ) - (q : ℝ) + (Δ : ℝ) + ((disNeigh adj c d i).card : ℝ))
          else ((q : ℝ) * ((hammingDist c d : ℕ) : ℝ) + 2 * ((disNeigh adj c d i).card : ℝ)))
        = (q : ℝ) * ((hammingDist c d : ℕ) : ℝ) + (if c i ≠ d i then (-(q : ℝ) + (Δ : ℝ) + ((disNeigh adj c d i).card : ℝ))
            else (2 * ((disNeigh adj c d i).card : ℝ))) := by
      intro i
      by_cases hdis : c i ≠ d i
      · simp [hdis]
        ring
      · simp [hdis]
    rw [Finset.sum_congr rfl (fun i _ => hrewrite i)]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_const]
    simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hbound_eq] at hle1
  -- Step C: bound extras
  have hH : ((hammingDist c d : ℕ) : ℝ) = (((Finset.univ.filter (fun j => c j ≠ d j)).card : ℕ) : ℝ) := rfl
  have hsum_one : (∑ i, (if c i ≠ d i then (1 : ℝ) else 0)) = ((hammingDist c d : ℕ) : ℝ) := by
    have hboole : (∑ x ∈ (Finset.univ : Finset (Fin n)), (if c x ≠ d x then (1 : ℝ) else 0))
        = ((((Finset.univ.filter (fun j => c j ≠ d j)).card : ℕ)) : ℝ) :=
      Finset.sum_boole _ _
    simpa [hH] using hboole
  have hsum_neg_q : (∑ i, (if c i ≠ d i then (-(q : ℝ)) else 0)) = -(q : ℝ) * ((hammingDist c d : ℕ) : ℝ) := by
    have heq : ∀ i : Fin n, (if c i ≠ d i then (-(q : ℝ)) else 0)
        = (-(q : ℝ)) * (if c i ≠ d i then (1 : ℝ) else 0) := by
      intro i
      by_cases hdis : c i ≠ d i
      · simp [hdis]
      · simp [hdis]
    rw [Finset.sum_congr rfl (fun i _ => heq i)]
    rw [← Finset.mul_sum]
    rw [hsum_one]
  have hsum_Delta : (∑ i, (if c i ≠ d i then (Δ : ℝ) else 0)) = (Δ : ℝ) * ((hammingDist c d : ℕ) : ℝ) := by
    have heq : ∀ i : Fin n, (if c i ≠ d i then (Δ : ℝ) else 0)
        = (Δ : ℝ) * (if c i ≠ d i then (1 : ℝ) else 0) := by
      intro i
      by_cases hdis : c i ≠ d i
      · simp [hdis]
      · simp [hdis]
    rw [Finset.sum_congr rfl (fun i _ => heq i)]
    rw [← Finset.mul_sum]
    rw [hsum_one]
  -- Double counting in reals
  have hdouble_nat : (∑ i, (disNeigh adj c d i).card)
      ≤ Δ * (Finset.univ.filter (fun j => c j ≠ d j)).card :=
    double_count adj hadj Δ hdeg c d
  have hdouble_real : (∑ i, (((disNeigh adj c d i).card : ℕ) : ℝ))
      ≤ (Δ : ℝ) * ((hammingDist c d : ℕ) : ℝ) := by
    have hcast : (∑ i, (((disNeigh adj c d i).card : ℕ) : ℝ))
        = ((((∑ i, (disNeigh adj c d i).card) : ℕ)) : ℝ) := by
      rw [Nat.cast_sum]
    rw [hcast]
    rw [hH]
    have hle : ((((∑ i, (disNeigh adj c d i).card) : ℕ)) : ℝ)
        ≤ (((Δ * (Finset.univ.filter (fun j => c j ≠ d j)).card : ℕ)) : ℝ) := by
      apply Nat.cast_le.mpr
      exact hdouble_nat
    calc (((((∑ i, (disNeigh adj c d i).card) : ℕ))) : ℝ)
        ≤ (((Δ * (Finset.univ.filter (fun j => c j ≠ d j)).card : ℕ)) : ℝ) := hle
      _ = (Δ : ℝ) * ((((Finset.univ.filter (fun j => c j ≠ d j)).card : ℕ)) : ℝ) := by
        push_cast
        ring
  -- Filtered DisN sums
  have hsum_dis_combined :
      (∑ i, (if c i ≠ d i then (((disNeigh adj c d i).card : ℕ) : ℝ) else 0)) +
        (∑ i, (if c i ≠ d i then (0 : ℝ) else 2 * (((disNeigh adj c d i).card : ℕ) : ℝ))) ≤
        2 * ((Δ : ℝ) * ((hammingDist c d : ℕ) : ℝ)) := by
    have hper : (∑ i, (if c i ≠ d i then (((disNeigh adj c d i).card : ℕ) : ℝ) else 0)) +
        (∑ i, (if c i ≠ d i then (0 : ℝ) else 2 * (((disNeigh adj c d i).card : ℕ) : ℝ))) ≤
        2 * (∑ i, (((disNeigh adj c d i).card : ℕ) : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      calc (∑ i, ((if c i ≠ d i then (((disNeigh adj c d i).card : ℕ) : ℝ) else 0) +
          (if c i ≠ d i then (0 : ℝ) else 2 * (((disNeigh adj c d i).card : ℕ) : ℝ))))
          ≤ ∑ i, (2 * (((disNeigh adj c d i).card : ℕ) : ℝ)) := by
            apply Finset.sum_le_sum
            intro i _
            split_ifs with hdis
            · have h0 : (0 : ℝ) ≤ (((disNeigh adj c d i).card : ℕ) : ℝ) := Nat.cast_nonneg _
              linarith
            · linarith
        _ = 2 * (∑ i, (((disNeigh adj c d i).card : ℕ) : ℝ)) := by
            rw [Finset.mul_sum]
    linarith [hper, hdouble_real]
  -- Combine extras
  have hextra_eq : (∑ i, (if c i ≠ d i then (-(q : ℝ) + (Δ : ℝ) + ((disNeigh adj c d i).card : ℝ))
      else (2 * ((disNeigh adj c d i).card : ℝ))))
      = (∑ i, (if c i ≠ d i then (-(q : ℝ)) else 0))
        + (∑ i, (if c i ≠ d i then (Δ : ℝ) else 0))
        + (∑ i, (if c i ≠ d i then (((disNeigh adj c d i).card : ℕ) : ℝ) else 0))
        + (∑ i, (if c i ≠ d i then (0 : ℝ) else 2 * (((disNeigh adj c d i).card : ℕ) : ℝ))) := by
    have hper2 : ∀ i : Fin n,
        (if c i ≠ d i then (-(q : ℝ) + (Δ : ℝ) + ((disNeigh adj c d i).card : ℝ))
          else (2 * ((disNeigh adj c d i).card : ℝ)))
        = (if c i ≠ d i then (-(q : ℝ)) else 0)
          + (if c i ≠ d i then (Δ : ℝ) else 0)
          + (if c i ≠ d i then (((disNeigh adj c d i).card : ℕ) : ℝ) else 0)
          + (if c i ≠ d i then (0 : ℝ) else 2 * (((disNeigh adj c d i).card : ℕ) : ℝ)) := by
      intro i
      by_cases hdis : c i ≠ d i
      · simp [hdis]
      · simp [hdis]
    rw [Finset.sum_congr rfl (fun i _ => hper2 i)]
    simp [Finset.sum_add_distrib]
  have hextra_le : (∑ i, (if c i ≠ d i then (-(q : ℝ) + (Δ : ℝ) + ((disNeigh adj c d i).card : ℝ))
      else (2 * ((disNeigh adj c d i).card : ℝ))))
      ≤ (-(q : ℝ) * ((hammingDist c d : ℕ) : ℝ)) + ((Δ : ℝ) * ((hammingDist c d : ℕ) : ℝ)) +
        (2 * ((Δ : ℝ) * ((hammingDist c d : ℕ) : ℝ))) := by
    rw [hextra_eq, hsum_neg_q, hsum_Delta]
    linarith [hsum_dis_combined]
  calc (∑ i, ∑ col, ((hammingDist (if IsProper adj (Function.update c i col) then Function.update c i col else c) (if IsProper adj (Function.update d i col) then Function.update d i col else d) : ℕ) : ℝ))
      ≤ (n : ℝ) * (q : ℝ) * ((hammingDist c d : ℕ) : ℝ) + ∑ i, (if c i ≠ d i then (-(q : ℝ) + (Δ : ℝ) + ((disNeigh adj c d i).card : ℝ))
          else (2 * ((disNeigh adj c d i).card : ℝ))) := hle1
    _ ≤ (n : ℝ) * (q : ℝ) * ((hammingDist c d : ℕ) : ℝ) + ((-(q : ℝ) * ((hammingDist c d : ℕ) : ℝ)) + ((Δ : ℝ) * ((hammingDist c d : ℕ) : ℝ)) + (2 * ((Δ : ℝ) * ((hammingDist c d : ℕ) : ℝ)))) := by
        apply add_le_add_right
        exact hextra_le
    _ = (n : ℝ) * (q : ℝ) * ((hammingDist c d : ℕ) : ℝ) - (q : ℝ) * ((hammingDist c d : ℕ) : ℝ) + 3 * (Δ : ℝ) * ((hammingDist c d : ℕ) : ℝ) := by ring

/-- Path-coupling contraction for Glauber dynamics on proper
colorings (Jerrum's bound): if every vertex has at most `Δ`
neighbors, the expected Hamming distance after one coupled step is
at most `(1 - 1/n + 3Δ/(n q))` times the current Hamming distance. -/
theorem glauber_hamming_contract {n q : ℕ} [Nonempty (Fin n)] [Nonempty (Fin q)] (hn : 0 < n) (hq : 0 < q)
    (adj : Fin n → Fin n → Bool)
    (hadj : ∀ i j, adj i j = true → adj j i = true)
    (Δ : ℕ) (hdeg : ∀ i, (Finset.univ.filter (fun j => adj i j = true)).card ≤ Δ)
    {c d : Fin n → Fin q} (hc : IsProper adj c) (hd : IsProper adj d) :
    (∑ z, (glauberCouple adj c d z).toReal * ((hammingDist z.1 z.2 : ℕ) : ℝ)) ≤
      (1 - 1 / n + 3 * Δ / (n * q)) * ((hammingDist c d : ℕ) : ℝ) := by
  classical
  have hexp := expected_glauberCouple adj c d (fun z => ((hammingDist z.1 z.2 : ℕ) : ℝ))
  rw [Fintype.card_fin, Fintype.card_fin] at hexp
  rw [hexp]
  have htotal := total_bound adj hadj Δ hdeg c d hc hd
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hnq_pos : (0 : ℝ) < (n : ℝ) * (q : ℝ) := mul_pos hn_pos hq_pos
  have hw_nonneg : (0 : ℝ) ≤ 1 / ((n : ℝ) * (q : ℝ)) := by
    positivity
  calc (1 / ((n : ℝ) * (q : ℝ))) * ∑ i, ∑ col, ((hammingDist (if IsProper adj (Function.update c i col) then Function.update c i col else c) (if IsProper adj (Function.update d i col) then Function.update d i col else d) : ℕ) : ℝ)
      ≤ (1 / ((n : ℝ) * (q : ℝ))) * ((n : ℝ) * (q : ℝ) * ((hammingDist c d : ℕ) : ℝ) - (q : ℝ) * ((hammingDist c d : ℕ) : ℝ) + 3 * (Δ : ℝ) * ((hammingDist c d : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · exact htotal
        · exact hw_nonneg
    _ = (1 - 1 / n + 3 * Δ / (n * q)) * ((hammingDist c d : ℕ) : ℝ) := by
        field_simp
