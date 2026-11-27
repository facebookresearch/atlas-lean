/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Cauchy–Davenport–Chowla theorem

This file records the composite-modulus sumset bound obtained when every
nonzero element of the second summand is a unit.
-/

section

open scoped Pointwise

namespace MathlibExt.Combinatorics.Additive.CauchyDavenportChowlaWanted

/-- A finset of `ZMod q` containing `0` and closed under `· + 1` is everything. -/
private theorem univ_of_zero_mem_add_one_mem (q : ℕ) [NeZero q] (S : Finset (ZMod q))
    (h0 : (0 : ZMod q) ∈ S) (hs : ∀ s ∈ S, s + 1 ∈ S) : S = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro y
  have hall : ∀ k : ℕ, (k : ZMod q) ∈ S := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih => simpa using hs _ ih
  have hy : ((y.val : ZMod q)) = y := ZMod.natCast_zmod_val y
  rw [← hy]
  exact hall y.val

/-- **Cauchy–Davenport–Chowla theorem.** Let $q$ be a positive integer and let $A$ and $B$ be
nonempty subsets of $\mathbb{Z}/q\mathbb{Z}$ such that $0 \in B$ and every nonzero element of $B$
is a unit of $\mathbb{Z}/q\mathbb{Z}$. Then $|A + B| \ge \min(q, |A| + |B| - 1)$, where
$A + B = \{a + b : a \in A, b \in B\}$.

Source: R. C. Vaughan, *The Hardy–Littlewood Method*, 2nd ed., Cambridge Tracts in
Mathematics 125, Cambridge University Press, 1997, Lemma 2.14; also stated as
Lemma 3.5 in H. Wang and S. Tian, arXiv:2608.12397v1. Mathlib's
`ZMod.cauchy_davenport` covers the prime-modulus special case.

Proves `Wanted` entry `cauchy_davenport_chowla`.
-/
theorem cauchy_davenport_chowla (q : ℕ) (A B : Finset (ZMod q)) :
    0 < q → A.Nonempty → B.Nonempty → (0 : ZMod q) ∈ B →
      (∀ b ∈ B, b ≠ (0 : ZMod q) → IsUnit b) →
        min q (A.card + B.card - 1) ≤ (A + B).card := by
  intro hq
  have : NeZero q := ⟨hq.ne'⟩
  revert A
  refine Finset.strongInductionOn B (fun B ih A hA hB h0B hunit => ?_)
  by_cases hB0 : ∃ b ∈ B, b ≠ (0 : ZMod q)
  · obtain ⟨u, huB, _hu0⟩ := hB0
    have hu : IsUnit u := hunit u huB _hu0
    by_cases hprog : ∃ e ∈ A, ∃ b ∈ B, e + b ∉ A
    · -- Dyson e-transform step: grow `A`, shrink `B`, keep the card sum.
      obtain ⟨e, heA, b, hbB, heb⟩ := hprog
      have hfinj : Function.Injective (e + · : ZMod q → ZMod q) :=
        fun x y h => add_left_cancel h
      have hB'sub : B.filter (fun c => e + c ∈ A) ⊆ B := Finset.filter_subset _ _
      have hbB' : b ∉ B.filter (fun c => e + c ∈ A) := by
        intro hc
        rw [Finset.mem_filter] at hc
        exact heb hc.2
      have hB'ss : B.filter (fun c => e + c ∈ A) ⊂ B :=
        Finset.ssubset_iff_subset_ne.mpr
          ⟨hB'sub, fun h => hbB' (by rw [h]; exact hbB)⟩
      have h0B' : (0 : ZMod q) ∈ B.filter (fun c => e + c ∈ A) := by
        rw [Finset.mem_filter]
        exact ⟨h0B, by simpa using heA⟩
      have hunit' : ∀ c ∈ B.filter (fun c => e + c ∈ A), c ≠ 0 → IsUnit c :=
        fun c hc h => hunit c (hB'sub hc) h
      have hTcard : (B.image (e + ·)).card = B.card :=
        Finset.card_image_of_injective _ hfinj
      have hinter : A ∩ B.image (e + ·) =
          (B.filter (fun c => e + c ∈ A)).image (e + ·) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨hxA, c, hcB, hcx⟩
          have hcA : e + c ∈ A := hcx.symm ▸ hxA
          exact ⟨c, ⟨hcB, hcA⟩, hcx⟩
        · rintro ⟨c, ⟨hcB, hcA⟩, hcx⟩
          exact ⟨hcx.symm ▸ hcA, c, hcB, hcx⟩
      have hinter_card : (A ∩ B.image (e + ·)).card =
          (B.filter (fun c => e + c ∈ A)).card := by
        rw [hinter]
        exact Finset.card_image_of_injective _ hfinj
      have hcardsum : (A ∪ B.image (e + ·)).card +
          (B.filter (fun c => e + c ∈ A)).card = A.card + B.card := by
        have h1 : (A ∪ B.image (e + ·)).card + (A ∩ B.image (e + ·)).card =
            A.card + (B.image (e + ·)).card :=
          Finset.card_union_add_card_inter _ _
        omega
      have hsub : (A ∪ B.image (e + ·)) + B.filter (fun c => e + c ∈ A) ⊆
          A + B := by
        intro x hx
        rw [Finset.mem_add] at hx
        obtain ⟨a', ha', b', hb'B', rfl⟩ := hx
        rw [Finset.mem_union] at ha'
        have hb'B : b' ∈ B := hB'sub hb'B'
        have hfb' : e + b' ∈ A := (Finset.mem_filter.mp hb'B').2
        rcases ha' with ha'A | ha'T
        · exact Finset.add_mem_add ha'A hb'B
        · rw [Finset.mem_image] at ha'T
          obtain ⟨b'', hb''B, hb''eq⟩ := ha'T
          have hb''eq' : e + b'' = a' := hb''eq
          have hmem : (e + b') + b'' ∈ A + B := Finset.add_mem_add hfb' hb''B
          have heq : a' + b' = (e + b') + b'' := by rw [← hb''eq']; abel
          rw [heq]
          exact hmem
      have hA'ne : (A ∪ B.image (e + ·)).Nonempty := by
        obtain ⟨a, ha⟩ := hA
        exact ⟨a, Finset.mem_union.mpr (Or.inl ha)⟩
      have hB'ne : (B.filter (fun c => e + c ∈ A)).Nonempty := ⟨0, h0B'⟩
      have hIH := ih _ hB'ss _ hA'ne hB'ne h0B' hunit'
      rw [hcardsum] at hIH
      exact le_trans hIH (Finset.card_le_card hsub)
    · -- Degenerate case: `A + B ⊆ A`, so translation by the unit `u`
      -- fixes `A`, forcing `|A| = q`.
      have hdeg : ∀ e ∈ A, ∀ b ∈ B, e + b ∈ A := by
        intro e he b hb
        by_contra hcon
        exact hprog ⟨e, he, b, hb, hcon⟩
      obtain ⟨w, hw⟩ : ∃ w : ZMod q, w * u = 1 := ⟨_, hu.val_inv_mul⟩
      obtain ⟨a₀, ha₀⟩ := hA
      have huw : u * w = 1 := by rw [mul_comm]; exact hw
      have hginj : Function.Injective (fun x : ZMod q => w * (x - a₀)) := by
        have hleft : Function.LeftInverse (fun z : ZMod q => u * z + a₀)
            (fun x : ZMod q => w * (x - a₀)) := fun x => by
          change u * (w * (x - a₀)) + a₀ = x
          rw [← mul_assoc, huw, one_mul, sub_add_cancel]
        exact hleft.injective
      have hScard : (A.image (fun x : ZMod q => w * (x - a₀))).card = A.card :=
        Finset.card_image_of_injective _ hginj
      have h0S : (0 : ZMod q) ∈ A.image (fun x : ZMod q => w * (x - a₀)) := by
        have hg0 : (fun x : ZMod q => w * (x - a₀)) a₀ = 0 := by
          change w * (a₀ - a₀) = 0
          rw [sub_self, mul_zero]
        rw [Finset.mem_image]
        exact ⟨a₀, ha₀, hg0⟩
      have hSS : ∀ s ∈ A.image (fun x : ZMod q => w * (x - a₀)), s + 1 ∈
          A.image (fun x : ZMod q => w * (x - a₀)) := by
        intro s hs
        rw [Finset.mem_image] at hs
        obtain ⟨a, haA, rfl⟩ := hs
        have hau : a + u ∈ A := hdeg a haA u huB
        have hga : (fun x : ZMod q => w * (x - a₀)) (a + u) =
            (fun x : ZMod q => w * (x - a₀)) a + 1 := by
          change w * ((a + u) - a₀) = w * (a - a₀) + 1
          rw [show (a + u) - a₀ = (a - a₀) + u by abel, mul_add, hw]
        rw [Finset.mem_image]
        exact ⟨a + u, hau, hga⟩
      have hSuniv : A.image (fun x : ZMod q => w * (x - a₀)) = Finset.univ :=
        univ_of_zero_mem_add_one_mem q _ h0S hSS
      have hAq : A.card = q := by
        have h1 : (A.image (fun x : ZMod q => w * (x - a₀))).card =
            Fintype.card (ZMod q) := by
          rw [hSuniv]
          exact Finset.card_univ
        rw [ZMod.card q] at h1
        omega
      have hAle : A.card ≤ (A + B).card := by
        apply Finset.card_le_card
        intro a ha
        have hmem : a + 0 ∈ A + B := Finset.add_mem_add ha h0B
        simpa using hmem
      calc min q (A.card + B.card - 1) ≤ q := min_le_left _ _
        _ = A.card := hAq.symm
        _ ≤ (A + B).card := hAle
  · -- `B = {0}`, so `A + B = A`.
    have hB0' : ∀ b ∈ B, b = (0 : ZMod q) := by
      intro b hb
      by_contra hcon
      exact hB0 ⟨b, hb, hcon⟩
    have hBsub : B ⊆ {0} := fun b hb => Finset.mem_singleton.mpr (hB0' b hb)
    have hBcard : B.card = 1 := by
      have h1 : B.card ≤ 1 := by
        have h := Finset.card_le_card hBsub
        simpa using h
      have h2 : 1 ≤ B.card := Finset.card_pos.mpr hB
      omega
    have hAB : A + B = A := by
      apply subset_antisymm
      · intro x hx
        rw [Finset.mem_add] at hx
        obtain ⟨a, haA, b, hbB, rfl⟩ := hx
        have hb0 : b = 0 := hB0' b hbB
        rw [hb0, add_zero]
        exact haA
      · intro a ha
        have hmem : a + 0 ∈ A + B := Finset.add_mem_add ha h0B
        simpa using hmem
    rw [hAB, hBcard]
    have h10 : A.card + 1 - 1 = A.card := by omega
    rw [h10]
    exact min_le_right _ _

end MathlibExt.Combinatorics.Additive.CauchyDavenportChowlaWanted
