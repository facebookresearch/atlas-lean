/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalEntropy

@[expose] public section

/-! # Slepian-Wolf core: chain rule and random binning

The entropy chain rule `H (X, Y) = H (Y) + H (X | Y)`, in bits via
the repository API `InformationTheory.shannonEntropy` and
`InformationTheory.finiteConditionalEntropy`, and the
random-binning collision count: averaging over all binnings
`Fin k → Fin M`, the expected number of colliding pairs is
`C(k, 2) / M`. These are the counting core of roadmap package
QCI-42 of the Atlas TCS canon roadmap.

The chain rule here is the second-coordinate orientation of the
existing `shannonEntropy_eq_add_finiteConditionalEntropy`
(`H (X, Y) = H (X) + H (Y | X)`), obtained by applying it to
`p.map (Equiv.prodComm α β)`; multiplying by `Real.log 2`
converts the bits statement to the nats convention
`H (X, Y) = H (Y) + H (X | Y)` in nats.

Source: Cover and Thomas, Elements of Information Theory (2006),
Section 15.4.
-/

namespace InformationTheory

open Finset
open scoped Classical

/-- **Chain rule, second-coordinate orientation**: `H (X, Y) = H (Y) + H (X | Y)`,
in bits. This is `shannonEntropy_eq_add_finiteConditionalEntropy`
applied to `p.map (Equiv.prodComm α β)`. -/
theorem shannonEntropy_eq_add_finiteConditionalEntropy_snd {α β : Type*}
    [Fintype α] [Fintype β] (p : PMF (α × β)) :
    shannonEntropy p =
      shannonEntropy (p.map Prod.snd) +
        finiteConditionalEntropy (p.map (Equiv.prodComm α β)) := by
  have h := shannonEntropy_eq_add_finiteConditionalEntropy (p.map (Equiv.prodComm α β))
  have h1 : shannonEntropy (p.map (Equiv.prodComm α β)) = shannonEntropy p :=
    shannonEntropy_map_equiv p (Equiv.prodComm α β)
  have hfun : Prod.fst ∘ Equiv.prodComm α β = Prod.snd := by
    funext ⟨a, b⟩
    rfl
  have h2 : (p.map (Equiv.prodComm α β)).map Prod.fst = p.map Prod.snd := by
    rw [PMF.map_comp, hfun]
  rw [h1, h2] at h
  exact h

/-- **Chain rule, second-coordinate orientation, in nats**: multiplying the bits
chain rule by `Real.log 2` converts it to the nats convention. -/
theorem shannonEntropy_mul_log_two_eq_add_finiteConditionalEntropy_snd {α β : Type*}
    [Fintype α] [Fintype β] (p : PMF (α × β)) :
    shannonEntropy p * Real.log 2 =
      shannonEntropy (p.map Prod.snd) * Real.log 2 +
        finiteConditionalEntropy (p.map (Equiv.prodComm α β)) * Real.log 2 := by
  rw [shannonEntropy_eq_add_finiteConditionalEntropy_snd]
  ring

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

end InformationTheory
