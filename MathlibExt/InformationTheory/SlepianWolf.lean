/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-! # Slepian-Wolf core: chain rule and random binning

The entropy chain rule `H (X, Y) = H (Y) + H (X | Y)` on finite
types, and the random-binning collision count: averaging over
all binnings `Fin k → Fin M`, the expected number of colliding
pairs is `C(k, 2) / M`. These are the counting core of roadmap
package QCI-42 of the Atlas TCS canon roadmap.

Source: Cover and Thomas, Elements of Information Theory (2006),
Section 15.4.
-/

open Finset
open scoped Classical

/-- Shannon entropy (nats) of a PMF on a finite type, with
`0 log 0 = 0` by the real conventions. -/
noncomputable def entropyPMF {α : Type*} [Fintype α] (p : PMF α) : ℝ :=
  ∑ a, -(p a).toReal * Real.log (p a).toReal

/-- Conditional entropy `H (X | Y)` (nats) of a joint PMF. -/
noncomputable def condEntropy {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) : ℝ :=
  ∑ x, ∑ y, -(p (x, y)).toReal *
    Real.log ((p (x, y)).toReal / (∑ x', (p (x', y)).toReal))

/-- The second marginal of a joint PMF, written as finite sums. -/
noncomputable def marginalSnd {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) : PMF β :=
  p.map Prod.snd

private theorem pmf_ne_top {α : Type*} [Fintype α] (p : PMF α) (a : α) :
    p a ≠ Top.top := by
  have h1 : p a ≤ 1 := PMF.coe_le_one p a
  have h2 : (1 : ENNReal) ≠ Top.top := ne_of_lt ENNReal.one_lt_top
  exact ne_top_of_le_ne_top h2 h1

private theorem marginal_toReal {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) (y : β) :
    ((marginalSnd p) y).toReal = ∑ x', (p (x', y)).toReal := by
  unfold marginalSnd
  rw [PMF.map_apply]
  rw [tsum_fintype]
  have hfin : ∀ a ∈ (Finset.univ : Finset (α × β)),
      (if y = a.snd then p a else 0) ≠ Top.top := by
    intro a _
    by_cases h : y = a.snd
    · simp [h, pmf_ne_top p a]
    · simp [h]
  rw [ENNReal.toReal_sum hfin]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  have h0 : ∀ y' : β, y' ∈ (Finset.univ : Finset β) → y' ≠ y →
      (if y = (x, y').snd then p (x, y') else 0).toReal = 0 := by
    intro y' _ hy'
    have hsnd : (x, y').snd = y' := rfl
    have hne : y ≠ (x, y').snd := by
      rw [hsnd]
      exact Ne.symm hy'
    simp [hne, ENNReal.toReal_zero]
  have h1 : y ∉ (Finset.univ : Finset β) →
      (if y = (x, y).snd then p (x, y) else 0).toReal = 0 := by
    intro hcontra
    simp at hcontra
  have heq := Finset.sum_eq_single (a := y) (s := (Finset.univ : Finset β))
    (f := fun y' => (if y = (x, y').snd then p (x, y') else 0).toReal) h0 h1
  rw [heq]
  simp

private theorem cond_term_eq {u uY : ℝ} (h : u ≠ 0 → uY ≠ 0) :
    -u * Real.log (u / uY) = -u * Real.log u + u * Real.log uY := by
  by_cases hu0 : u = 0
  · simp [hu0]
  · have huY0 : uY ≠ 0 := h hu0
    rw [Real.log_div hu0 huY0]
    ring

private theorem chain_per_y {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) (y : β) :
    (∑ x, -(p (x, y)).toReal * Real.log (p (x, y)).toReal)
      = (-(∑ x', (p (x', y)).toReal) * Real.log (∑ x', (p (x', y)).toReal))
        + (∑ x, -(p (x, y)).toReal *
          Real.log ((p (x, y)).toReal / (∑ x', (p (x', y)).toReal))) := by
  set uY : ℝ := ∑ x', (p (x', y)).toReal with huYdef
  have hnonneg : ∀ x ∈ (Finset.univ : Finset α), 0 ≤ (p (x, y)).toReal := by
    intro x _
    exact ENNReal.toReal_nonneg
  by_cases huY0 : uY = 0
  · have hall : ∀ x ∈ (Finset.univ : Finset α), (p (x, y)).toReal = 0 := by
      have hiff := Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset α))
        (f := fun x' => (p (x', y)).toReal) hnonneg
      have huY0' : (∑ i ∈ (Finset.univ : Finset α), (p (i, y)).toReal) = 0 := by
        simpa [huYdef] using huY0
      exact (hiff.mp huY0')
    have hC0 : (∑ x, -(p (x, y)).toReal * Real.log (p (x, y)).toReal) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [hall x (Finset.mem_univ x)]
      simp
    have hB0 : (∑ x, -(p (x, y)).toReal *
        Real.log ((p (x, y)).toReal / uY)) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [hall x (Finset.mem_univ x)]
      simp
    rw [hC0, hB0]
    have hA0 : (-uY * Real.log uY) = 0 := by
      rw [huY0]
      simp
    simp [hA0]
  · have hterm : ∀ x ∈ (Finset.univ : Finset α),
        -(p (x, y)).toReal * Real.log ((p (x, y)).toReal / uY)
          = -(p (x, y)).toReal * Real.log (p (x, y)).toReal
            + (p (x, y)).toReal * Real.log uY := by
      intro x _
      apply cond_term_eq
      intro _
      exact huY0
    have hcongr : (∑ x : α, -(p (x, y)).toReal * Real.log ((p (x, y)).toReal / uY))
        = ∑ x : α, (-(p (x, y)).toReal * Real.log (p (x, y)).toReal
          + (p (x, y)).toReal * Real.log uY) := by
      apply Finset.sum_congr rfl
      intro x _
      exact hterm x (Finset.mem_univ x)
    have hsum : (∑ x : α, -(p (x, y)).toReal * Real.log ((p (x, y)).toReal / uY))
        = (∑ x : α, -(p (x, y)).toReal * Real.log (p (x, y)).toReal)
          + (∑ x : α, (p (x, y)).toReal * Real.log uY) := by
      rw [hcongr]
      rw [Finset.sum_add_distrib]
    have hmul : (∑ x : α, (p (x, y)).toReal * Real.log uY)
        = uY * Real.log uY := by
      have h := Finset.sum_mul (s := (Finset.univ : Finset α))
        (f := fun x => (p (x, y)).toReal) (a := Real.log uY)
      have hsym : (∑ i ∈ (Finset.univ : Finset α), (p (i, y)).toReal * Real.log uY)
          = (∑ i ∈ (Finset.univ : Finset α), (p (i, y)).toReal) * Real.log uY := by
        exact h.symm
      simpa [huYdef] using hsym
    have hB : (∑ x : α, -(p (x, y)).toReal * Real.log ((p (x, y)).toReal / uY))
        = (∑ x : α, -(p (x, y)).toReal * Real.log (p (x, y)).toReal)
          + uY * Real.log uY := by
      rw [hsum, hmul]
    rw [hB]
    ring

/-- Entropy chain rule: `H (X, Y) = H (Y) + H (X | Y)`. -/
theorem entropy_chain_rule {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) :
    entropyPMF p = entropyPMF (marginalSnd p) + condEntropy p := by
  have hLHS : entropyPMF p
      = ∑ y : β, ∑ x : α, -(p (x, y)).toReal * Real.log (p (x, y)).toReal := by
    unfold entropyPMF
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
  have hRHS1 : entropyPMF (marginalSnd p)
      = ∑ y : β, (-(∑ x', (p (x', y)).toReal)
        * Real.log (∑ x', (p (x', y)).toReal)) := by
    unfold entropyPMF
    apply Finset.sum_congr rfl
    intro y _
    rw [marginal_toReal]
  have hRHS2 : condEntropy p
      = ∑ y : β, ∑ x : α, -(p (x, y)).toReal *
        Real.log ((p (x, y)).toReal / (∑ x', (p (x', y)).toReal)) := by
    unfold condEntropy
    rw [Finset.sum_comm]
  rw [hLHS, hRHS1, hRHS2]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  exact chain_per_y p y

/-- Number of colliding pairs under a binning `b : Fin k → Fin M`. -/
noncomputable def binCollisions {k M : ℕ} (b : Fin k → Fin M) : ℝ :=
  ((Finset.univ.filter (fun ij : Fin k × Fin k =>
    ij.1 < ij.2 ∧ b ij.1 = b ij.2)).card : ℝ)

private def fiberEquiv {k M : ℕ} (i j : Fin k) (hij : i ≠ j) :
    {b : Fin k → Fin M // b i = b j} ≃ ({x : Fin k // x ≠ j} → Fin M) where
  toFun := fun b s => b.val s.val
  invFun := fun f => ⟨fun x => if h : x = j then f ⟨i, hij⟩ else f ⟨x, h⟩, by
    simp [hij]
  ⟩
  left_inv := by
    intro b
    apply Subtype.ext
    funext x
    by_cases hx : x = j
    · simp [hx, b.property]
    · simp [hx]
  right_inv := by
    intro f
    funext s
    simp [s.property]

private theorem card_subtype_ne {k : ℕ} (j : Fin k) :
    Fintype.card {x : Fin k // x ≠ j} = k - 1 := by
  rw [Fintype.card_subtype]
  have huniv : (Finset.univ : Finset (Fin k)).card = k := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hmem : j ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ j
  have herase : ((Finset.univ : Finset (Fin k)).erase j).card = k - 1 := by
    rw [Finset.card_erase_of_mem hmem, huniv]
  have hfilter_eq : (Finset.univ : Finset (Fin k)).filter (fun x => x ≠ j)
      = (Finset.univ : Finset (Fin k)).erase j := by
    ext x
    simp [Finset.mem_filter, Finset.mem_erase, and_comm]
  rw [hfilter_eq]
  exact herase

private theorem fiber_card {k M : ℕ} (i j : Fin k) (hij : i ≠ j) :
    Fintype.card {b : Fin k → Fin M // b i = b j} = M ^ (k - 1) := by
  have hcongr := Fintype.card_congr (fiberEquiv (k := k) (M := M) i j hij)
  have hfun := Fintype.card_fun (α := {x : Fin k // x ≠ j}) (β := Fin M)
  rw [Fintype.card_fin] at hfun
  rw [card_subtype_ne j] at hfun
  rw [hcongr]
  exact hfun

private theorem bin_inner_sum {k M : ℕ} (i j : Fin k) (hij : i ≠ j) :
    (∑ b : Fin k → Fin M, (if b i = b j then (1 : ℝ) else 0))
      = ((M ^ (k - 1) : ℕ) : ℝ) := by
  have hcard_nat : ((Finset.univ : Finset (Fin k → Fin M)).filter
      (fun b => b i = b j)).card = M ^ (k - 1) := by
    have hsub := Fintype.card_subtype (α := Fin k → Fin M) (fun b => b i = b j)
    have hfib := fiber_card (k := k) (M := M) i j hij
    rw [hfib] at hsub
    exact hsub.symm
  have hsum_nat : ((Finset.univ : Finset (Fin k → Fin M)).filter
      (fun b => b i = b j)).card
      = ∑ b ∈ (Finset.univ : Finset (Fin k → Fin M)),
        (if b i = b j then 1 else 0) := by
    rw [Finset.card_filter]
  have hcast : ((((Finset.univ : Finset (Fin k → Fin M)).filter
      (fun b => b i = b j)).card : ℕ) : ℝ)
      = ∑ b : Fin k → Fin M, (if b i = b j then (1 : ℝ) else 0) := by
    rw [hsum_nat]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : b i = b j
    · simp [h]
    · simp [h]
  rw [← hcast, hcard_nat]

private theorem bin_pair_card {k : ℕ} :
    ((Finset.univ : Finset (Fin k × Fin k)).filter
      (fun ij => ij.1 < ij.2)).card = k.choose 2 := by
  have h := Fintype.card_product_filter_lt (α := Fin k)
  rw [Fintype.card_fin] at h
  exact h

private theorem bin_as_sum {k M : ℕ} (b : Fin k → Fin M) :
    binCollisions b = ∑ ij ∈ ((Finset.univ : Finset (Fin k × Fin k)).filter
      (fun ij => ij.1 < ij.2)), (if b ij.1 = b ij.2 then (1 : ℝ) else 0) := by
  unfold binCollisions
  have hfilter : (Finset.univ : Finset (Fin k × Fin k)).filter
        (fun ij => ij.1 < ij.2 ∧ b ij.1 = b ij.2)
      = (((Finset.univ : Finset (Fin k × Fin k)).filter
        (fun ij => ij.1 < ij.2)).filter (fun ij => b ij.1 = b ij.2)) := by
    rw [Finset.filter_filter]
  rw [hfilter]
  rw [Finset.card_filter]
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro ij _
  by_cases h : b ij.1 = b ij.2
  · simp [h]
  · simp [h]

/-- Random binning: the average number of colliding pairs over all
binnings `Fin k → Fin M` is `C(k, 2) / M` (each pair collides with
probability `1 / M`). -/
theorem expected_bin_collisions {k M : ℕ} (hM : 0 < M) :
    (∑ b : Fin k → Fin M, binCollisions b) / (M : ℝ) ^ k =
      (k.choose 2 : ℝ) / M := by
  have htotal : (∑ b : Fin k → Fin M, binCollisions b)
      = (k.choose 2 : ℝ) * ((M ^ (k - 1) : ℕ) : ℝ) := by
    have h1 : (∑ b : Fin k → Fin M, binCollisions b)
        = ∑ b : Fin k → Fin M, ∑ ij ∈ ((Finset.univ : Finset (Fin k × Fin k)).filter
          (fun ij => ij.1 < ij.2)), (if b ij.1 = b ij.2 then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro b _
      exact bin_as_sum b
    rw [h1]
    rw [Finset.sum_comm]
    have h2 : (∑ ij ∈ ((Finset.univ : Finset (Fin k × Fin k)).filter
          (fun ij => ij.1 < ij.2)), ∑ b : Fin k → Fin M,
          (if b ij.1 = b ij.2 then (1 : ℝ) else 0))
        = ∑ ij ∈ ((Finset.univ : Finset (Fin k × Fin k)).filter
          (fun ij => ij.1 < ij.2)), ((M ^ (k - 1) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro ij hij
      have hlt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).right
      have hne : ij.1 ≠ ij.2 := ne_of_lt hlt
      exact bin_inner_sum ij.1 ij.2 hne
    rw [h2]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [bin_pair_card]
  rw [htotal]
  by_cases hk : k < 2
  · have hchoose : k.choose 2 = 0 := by
      interval_cases k
      · rfl
      · rfl
    rw [hchoose]
    simp
  · have hk2 : 2 ≤ k := by omega
    have hk1 : 1 ≤ k := by omega
    have hk_eq : (k - 1) + 1 = k := Nat.sub_add_cancel hk1
    have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
    have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
    have hBne : (M : ℝ) ^ k ≠ 0 := pow_ne_zero k hMne
    have hAM : ((M ^ (k - 1) : ℕ) : ℝ) * (M : ℝ) = (M : ℝ) ^ k := by
      rw [Nat.cast_pow, ← pow_succ, hk_eq]
    field_simp
    linear_combination (k.choose 2 : ℝ) * hAM
