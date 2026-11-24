/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Classes
import CSLibExt.Computability.Complexity.ACGateBridge
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.ZMod.Basic
import MathlibExt.NumberTheory.SizeChooseTwoPow
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Majority is not in AC0

The strict majority language has no polynomial-size, constant-depth circuit family over
unbounded fan-in AND, OR and unary NOT. The proof approximates the gates by polynomials
over the field of two elements. For an OR gate, a parity of a subset of its inputs detects
at least half the nonzero rows. Repeating this test `k` times per gate gives a degree at most
`k ^ d` for a depth-`d` circuit, with an error fraction at most its gate count divided by
`2 ^ k`.

On either side of the majority threshold, arbitrary functions interpolate in degree at most
`n / 2`, using complemented variables on the upper half. If a degree-`D` polynomial computes
majority on a set of inputs, it can select between these two interpolants there. The number
of those inputs is thus at most the number of squarefree monomials of degree at most
`n / 2 + D`. For polylogarithmic `D`, this contradicts agreement on seven eighths of the cube.
-/

namespace MetaMathlibExt.Complexity.KeyTheorems.MajorityNotInAC0

open Cslib.Complexity.Classes Finset Module

private abbrev Cube (n : ℕ) := Finset (Fin n)
private abbrev F := ZMod 2
private abbrev Fn (n : ℕ) := Cube n → F

private def mon {n : ℕ} (s : Cube n) : Fn n := fun x => if s ⊆ x then 1 else 0

private def ball (n d : ℕ) : Finset (Cube n) := univ.filter (fun x => x.card ≤ d)

private def polys (n d : ℕ) : Submodule F (Fn n) :=
  Submodule.span F (Set.range fun s : ball n d => mon s.val)

private theorem mem_monomial {n d : ℕ} (s : Cube n) (hs : s.card ≤ d) :
    mon s ∈ polys n d :=
  Submodule.subset_span ⟨⟨s, by simpa [ball]⟩, rfl⟩

private theorem polys_mono {n a b : ℕ} (h : a ≤ b) : polys n a ≤ polys n b := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, rfl⟩
  exact mem_monomial _ ((show s.val.card ≤ a by simpa [ball] using s.property).trans h)

private theorem mem_one (n d : ℕ) : (1 : Fn n) ∈ polys n d := by
  have h : mon (∅ : Cube n) = 1 := by ext; simp [mon]
  exact h ▸ mem_monomial (n := n) (d := d) ∅ (by simp)

private theorem mem_mul {n a b : ℕ} {f g : Fn n} (hf : f ∈ polys n a) (hg : g ∈ polys n b) :
    f * g ∈ polys n (a + b) := by
  apply Submodule.span_induction₂ (p := fun f g _ _ => f * g ∈ polys n (a + b))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf hg
  · rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    have hst : mon s.val * mon t.val = mon (s.val ∪ t.val) := by
      ext x
      simp only [mon, Pi.mul_apply, union_subset_iff]
      split_ifs <;> simp_all
    rw [hst]
    exact mem_monomial _ ((card_union_le _ _).trans (Nat.add_le_add
      (by simpa [ball] using s.property) (by simpa [ball] using t.property)))
  · simp
  · simp
  · intro x y z _ _ _ hx hy
    simpa only [add_mul] using (polys _ _).add_mem hx hy
  · intro x y z _ _ _ hy hz
    simpa only [mul_add] using (polys _ _).add_mem hy hz
  · intro r x y _ _ h
    simpa only [smul_mul_assoc] using (polys _ _).smul_mem r h
  · intro r x y _ _ h
    simpa only [mul_smul_comm] using (polys _ _).smul_mem r h

private theorem mem_compl_monomial {n : ℕ} (s : Cube n) :
    (fun x : Cube n => mon s xᶜ) ∈ polys n s.card := by
  induction s using Finset.induction_on with
  | empty => simpa [mon, Pi.one_def] using mem_one n 0
  | @insert i s hi ih =>
    have h := mem_mul ((polys n 1).sub_mem (mem_one n 1)
      (mem_monomial {i} (by simp))) ih
    rw [card_insert_of_notMem hi, add_comm]
    convert h using 1
    ext x
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, mon, singleton_subset_iff,
      insert_subset_iff, mem_compl]
    split_ifs <;> simp_all

-- Interpolate in order of increasing weight. A correction at a maximal point vanishes
-- on every other point already fitted, since none of them contains that point.
private theorem interpolate {n m : ℕ} (s : Finset (Cube n)) (h : ∀ x ∈ s, x.card ≤ m)
    (f : Fn n) (flip : Bool) :
    ∃ p ∈ polys n m, ∀ x ∈ s, p (if flip then xᶜ else x) = f x := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨a, ha, hmax⟩ := s.exists_max_image Finset.card hs
    obtain ⟨p, hp, he⟩ := interpolate (s.erase a)
      (fun x hx => h x (mem_of_mem_erase hx)) f flip
    let q : Fn n := fun x => mon a (if flip then xᶜ else x)
    have hq : q ∈ polys n m := by
      cases flip
      · exact mem_monomial a (h a ha)
      · exact polys_mono (h a ha) (mem_compl_monomial a)
    refine ⟨p + (f a - p (if flip then aᶜ else a)) • q,
      (polys _ _).add_mem hp ((polys _ _).smul_mem _ hq), ?_⟩
    intro x hx
    by_cases hxa : x = a
    · subst x
      cases flip <;> simp [q, mon]
    · have hax : ¬a ⊆ x := fun hsub => hxa (eq_of_subset_of_card_le hsub (hmax x hx)).symm
      have hh := he x (mem_erase.mpr ⟨hxa, hx⟩)
      cases flip <;> simpa [q, mon, hax] using hh
  · exact ⟨0, (polys _ _).zero_mem, fun _ hx => (hs ⟨_, hx⟩).elim⟩
termination_by s.card
decreasing_by exact card_erase_lt_of_mem ha

-- On the agreement set, the approximant selects the correct one of the two interpolants.
private theorem agreement_bound {n D : ℕ} (s : Finset (Cube n)) {q : Fn n}
    (hq : q ∈ polys n D) (he : ∀ x ∈ s, q x = if n < 2 * x.card then 1 else 0) :
    s.card ≤ (ball n (n / 2 + D)).card := by
  classical
  let V := polys n (n / 2 + D)
  let ev : V →ₗ[F] (s → F) :=
    { toFun := fun p x => p.val x.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hsur : Function.Surjective ev := by
    intro v
    let f : Fn n := fun x => if hx : x ∈ s then v ⟨x, hx⟩ else 0
    have hball : ∀ x ∈ ball n (n / 2), x.card ≤ n / 2 := by simp [ball]
    obtain ⟨a, ha, ea⟩ := interpolate _ hball f false
    obtain ⟨b, hb, eb⟩ := interpolate _ hball (fun x => f xᶜ) true
    refine ⟨⟨a * (1 - q) + b * q, (polys _ _).add_mem
      (mem_mul ha ((polys _ _).sub_mem (mem_one _ _) hq)) (mem_mul hb hq)⟩, ?_⟩
    funext ⟨x, hx⟩
    change a x * (1 - q x) + b x * q x = _
    rw [he x hx]
    by_cases h : n < 2 * x.card
    · have hc : xᶜ ∈ ball n (n / 2) := by
        simp only [ball, mem_filter, mem_univ, true_and, card_compl, Fintype.card_fin]
        omega
      simpa [h, f, hx] using eb xᶜ hc
    · have hc : x ∈ ball n (n / 2) := by simp [ball]; omega
      simpa [h, f, hx] using ea x hc
  have hdim := LinearMap.finrank_le_finrank_of_surjective hsur
  rw [Module.finrank_pi, Fintype.card_coe] at hdim
  have hd := finrank_range_le_card (R := F) (fun t : ball n (n / 2 + D) => mon t.val)
  exact hdim.trans (hd.trans_eq (Fintype.card_coe _))

-- Choose a parity of a sublist that detects at least half the nonzero input vectors.
private theorem parity_split {n r : ℕ} (fs : List (Fn n)) (hf : ∀ f ∈ fs, f ∈ polys n r)
    (s : Finset (Cube n)) (hs : ∀ x ∈ s, ∃ f ∈ fs, f x ≠ 0) :
    ∃ u ∈ polys n r, (∀ x, (∀ f ∈ fs, f x = 0) → u x = 0) ∧
      2 * (s.filter (fun x => u x = 0)).card ≤ s.card := by
  classical
  induction fs generalizing s with
  | nil =>
    have : s = ∅ := eq_empty_iff_forall_notMem.mpr (by simpa using hs)
    subst s
    exact ⟨0, (polys _ _).zero_mem, by simp⟩
  | cons f fs ih =>
    let t := s.filter (fun x => f x = 0)
    obtain ⟨u, hu, hz, hhalf⟩ := ih (fun g hg => hf g (List.mem_cons_of_mem _ hg)) t (by
      intro x hx
      obtain ⟨g, hg, hn⟩ := hs x (mem_filter.mp hx).1
      exact ⟨g, (List.mem_cons.mp hg).resolve_left (by rintro rfl; exact hn (mem_filter.mp hx).2),
        hn⟩)
    let A := s.filter (fun x => u x = 0)
    let B := s.filter (fun x => (u + f) x = 0)
    have hi : A ∩ B = t.filter (fun x => u x = 0) := by
      ext x
      simp [A, B, t]
      grind
    -- On the rows where f is nonzero the two choices have disjoint zero sets.
    have hu' : A ∪ B ⊆ (s \ t) ∪ (A ∩ B) := by
      intro x hx
      simp [A, B, t] at hx ⊢
      grind
    have ht : t ⊆ s := filter_subset _ _
    have h := (card_le_card hu').trans (card_union_le _ _)
    rw [card_sdiff_of_subset ht] at h
    have hsum := card_union_add_card_inter A B
    rw [hi] at h hsum
    have ht' := card_le_card ht
    by_cases hA : 2 * A.card ≤ s.card
    · exact ⟨u, hu, fun x h => hz x (fun g hg => h g (List.mem_cons_of_mem _ hg)), hA⟩
    · refine ⟨u + f, (polys _ _).add_mem hu (hf _ List.mem_cons_self), ?_, ?_⟩
      · intro x hx
        simp [hz x (fun g hg => hx g (List.mem_cons_of_mem _ hg)), hx f List.mem_cons_self]
      · change 2 * B.card ≤ s.card
        omega

private theorem zero_or_one (v : F) : v = 0 ∨ v = 1 := by
  exact (show ∀ v : ZMod 2, v = 0 ∨ v = 1 by decide) v

-- A product of k such tests is one on all-zero rows and misses at most a 2⁻ᵏ fraction
-- of the rows with a nonzero entry.
private theorem zero_test {n r : ℕ} (fs : List (Fn n)) (hf : ∀ f ∈ fs, f ∈ polys n r)
    (k : ℕ) (s : Finset (Cube n)) (hs : ∀ x ∈ s, ∃ f ∈ fs, f x ≠ 0) :
    ∃ p ∈ polys n (r * k), ∃ e : Finset (Cube n), 2 ^ k * e.card ≤ s.card ∧
      (∀ x, (∀ f ∈ fs, f x = 0) → p x = 1) ∧ (∀ x ∈ s, x ∉ e → p x = 0) := by
  classical
  induction k generalizing s with
  | zero => exact ⟨1, mem_one _ _, s, by simp, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨u, hu, hu0, hu2⟩ := parity_split fs hf s hs
    obtain ⟨p, hp, e, he, hp1, hp0⟩ := ih (s.filter fun x => u x = 0)
      (fun x hx => hs x (mem_filter.mp hx).1)
    refine ⟨p * (1 - u), Nat.mul_succ r k ▸
      mem_mul hp ((polys _ _).sub_mem (mem_one _ _) hu), e, ?_, ?_, ?_⟩
    · rw [pow_succ, mul_right_comm]
      omega
    · intro x hx
      simp [hp1 x hx, hu0 x hx]
    · intro x hx hxe
      rcases zero_or_one (u x) with h | h
      · simp [hp0 x (mem_filter.mpr ⟨hx, h⟩) hxe]
      · simp [h]

private def bit (b : Bool) : F := if b then 1 else 0

private def assign {n : ℕ} (x : Cube n) (i : Fin n) : Bool := decide (i ∈ x)

private def flipPoly {n : ℕ} (b : Bool) (p : Fn n) : Fn n := if b then 1 - p else p

private theorem mem_flip {n r : ℕ} (b : Bool) {p : Fn n} (hp : p ∈ polys n r) :
    flipPoly b p ∈ polys n r := by
  cases b
  · exact hp
  · exact (polys _ _).sub_mem (mem_one _ _) hp

private theorem flip_eq_zero {n : ℕ} {p : Fn n} {x : Cube n} {v : Bool} (b : Bool)
    (hp : p x = bit v) : flipPoly b p x = 0 ↔ v = b := by
  cases b <;> cases v <;> simp_all [flipPoly, bit]

private theorem le_fold_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | hl
    · exact le_max_left _ _
    · exact (ih hl).trans (le_max_right _ _)

private theorem approx_fanin {n r : ℕ} (b : Bool) (k : ℕ) (l : List ℕ)
    (P : ℕ → Fn n) (hp : ∀ i ∈ l, P i ∈ polys n r) :
    ∃ q ∈ polys n (r * k), ∃ e : Finset (Cube n), 2 ^ k * e.card ≤ 2 ^ n ∧
      ∀ x ∉ e, ∀ v : ℕ → Bool, (∀ i ∈ l, P i x = bit (v i)) →
        q x = bit (if ∀ i ∈ l, v i = b then b else !b) := by
  classical
  let fs := l.map (fun i => flipPoly b (P i))
  let s := univ.filter (fun x : Cube n => ∃ f ∈ fs, f x ≠ 0)
  obtain ⟨p, hp', e, he, hz, hn⟩ := zero_test fs (by
    intro f hf
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    exact mem_flip b (hp i hi)) k s (fun _ hx => (mem_filter.mp hx).2)
  refine ⟨flipPoly (!b) p, mem_flip _ hp', e, he.trans ?_, ?_⟩
  · simpa using (card_le_univ s)
  · intro x hxe v hv
    have iff_zero : (∀ f ∈ fs, f x = 0) ↔ ∀ i ∈ l, v i = b := by
      simp only [fs, List.forall_mem_map]
      exact forall₂_congr fun i hi => flip_eq_zero b (hv i hi)
    by_cases h : ∀ i ∈ l, v i = b
    · have := hz x (iff_zero.mpr h)
      rw [ite_eq_left h]
      cases b <;> simp_all [flipPoly, bit]
    · have hs : x ∈ s := by
        simp only [s, mem_filter, mem_univ, true_and]
        simpa using mt iff_zero.mp h
      have := hn x hs hxe
      rw [ite_eq_right h]
      cases b <;> simp_all [flipPoly, bit]

private theorem gate_approx {n k : ℕ} (hk : 1 ≤ k) (C : List (ACGate n))
    (P : ℕ → Fn n) (hp : ∀ i, P i ∈ polys n (k ^ (circuitDepths C).getD i 0))
    (g : ACGate n) (hm : IsModFree [g]) :
    ∃ q ∈ polys n (k ^ gateDepthOf (circuitDepths C) g), ∃ e : Finset (Cube n),
      2 ^ k * e.card ≤ 2 ^ n ∧ ∀ x ∉ e,
        (∀ i, P i x = bit ((circuitEval C (assign x)).getD i false)) →
        q x = bit (gateValue (circuitEval C (assign x)) (assign x) g) := by
  classical
  let ds := circuitDepths C
  have fanin (b : Bool) (l : List ℕ) := approx_fanin (n := n)
    (r := k ^ (l.map (fun i => ds.getD i 0)).foldr max 0) b k l P
    (fun i hi => polys_mono (Nat.pow_le_pow_right hk (le_fold_max
      (List.mem_map_of_mem (f := fun i => ds.getD i 0) hi))) (hp i))
  cases g with
  | modGate m l => exact (hm _ List.mem_cons_self).elim
  | const b =>
    refine ⟨(if b then 1 else 0), ?_, ∅, by simp, ?_⟩
    · cases b
      · exact (polys _ _).zero_mem
      · exact mem_one _ _
    · cases b <;> simp [bit, gateValue]
  | var i =>
    refine ⟨mon {i}, mem_monomial _ (by simp [gateDepthOf]), ∅, by simp, ?_⟩
    simp [mon, bit, assign, gateValue]
  | notGate i =>
    refine ⟨1 - P i, (polys _ _).sub_mem (mem_one _ _) (polys_mono
      (Nat.pow_le_pow_right hk (Nat.le_succ _)) (hp i)), ∅, by simp, ?_⟩
    intro x _ hx
    simp only [Pi.sub_apply, Pi.one_apply, hx, gateValue]
    cases (circuitEval C (assign x)).getD i false <;> simp [bit]
  | andGate l =>
    obtain ⟨q, hq, e, he, hval⟩ := fanin true l
    refine ⟨q, by simpa [gateDepthOf, pow_succ, ds] using hq, e, he, ?_⟩
    intro x hx hv
    rw [hval x hx _ (fun i _ => hv i)]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp [gateValue]
  | orGate l =>
    obtain ⟨q, hq, e, he, hval⟩ := fanin false l
    refine ⟨q, by simpa [gateDepthOf, pow_succ, ds] using hq, e, he, ?_⟩
    intro x hx hv
    rw [hval x hx _ (fun i _ => hv i)]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp [gateValue]

private theorem getD_snoc {α : Type*} (l : List α) (a d : α) (i : ℕ) :
    (l ++ [a]).getD i d = if i = l.length then a else l.getD i d := by
  split_ifs with h
  · subst i
    simp
  · by_cases hi : i < l.length
    · exact List.getD_append _ _ _ _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem circuit_approx {n k : ℕ} (hk : 1 ≤ k) (C : List (ACGate n))
    (hm : IsModFree C) :
    ∃ (P : ℕ → Fn n) (E : Finset (Cube n)), 2 ^ k * E.card ≤ C.length * 2 ^ n ∧
      (∀ i, P i ∈ polys n (k ^ (circuitDepths C).getD i 0)) ∧
      ∀ x ∉ E, ∀ i, P i x = bit ((circuitEval C (assign x)).getD i false) := by
  classical
  induction C using List.reverseRecOn with
  | nil => exact ⟨0, ∅, by simp, fun i => (polys _ _).zero_mem, by simp [circuitEval, bit]⟩
  | append_singleton C g ih =>
    obtain ⟨P, E, hE, hp, hval⟩ := ih (fun a ha => hm a (by simp [ha]))
    obtain ⟨q, hq, e, he, hv⟩ := gate_approx hk C P hp g (fun a ha => hm a (by simp_all))
    refine ⟨fun i => if i = C.length then q else P i, E ∪ e, ?_, ?_, ?_⟩
    · calc 2 ^ k * (E ∪ e).card ≤ 2 ^ k * (E.card + e.card) := by gcongr; exact card_union_le ..
        _ ≤ (C ++ [g]).length * 2 ^ n := by
          rw [Nat.mul_add]
          simpa [Nat.add_mul] using Nat.add_le_add hE he
    · intro i
      rw [circuitDepths_append_singleton, getD_snoc, length_circuitDepths]
      dsimp only
      split_ifs
      · exact hq
      · exact hp i
    · intro x hx i
      rw [circuitEval_append_singleton, getD_snoc, length_circuitEval]
      simp only [mem_union, not_or] at hx
      dsimp only
      split_ifs
      · exact hv x hx.2 (hval x hx.1)
      · exact hval x hx.1 i

-- Below the middle layer there are at most half the cube's points, by complementation.
-- Each further layer has at most the middle binomial coefficient many points.
private theorem ball_bound (n D : ℕ) (hn : 2 ≤ n) :
    2 * (ball n (n / 2 + D)).card ≤ 2 ^ n + 2 * (D + 1) * n.choose (n / 2) := by
  classical
  let m := n / 2 - 1
  have hm : m + 1 = n / 2 := by dsimp [m]; omega
  have hinj : (ball n m).card ≤ (ball n m)ᶜ.card := by
    apply card_le_card_of_injOn (fun x : Cube n => xᶜ) _ compl_injective.injOn
    intro x hx
    simp [ball, m, card_compl] at hx ⊢
    omega
  rw [card_compl] at hinj
  simp only [Fintype.card_finset, Fintype.card_fin] at hinj
  have step (d : ℕ) : (ball n (d + 1)).card ≤ (ball n d).card + n.choose (n / 2) := by
    have hs : ball n (d + 1) ⊆ ball n d ∪ (univ : Cube n).powersetCard (d + 1) := by
      intro x
      simp only [ball, mem_filter, mem_univ, true_and, mem_union, mem_powersetCard,
        subset_univ]
      omega
    exact (card_le_card hs).trans ((card_union_le _ _).trans (Nat.add_le_add_left
      (by simpa using Nat.choose_le_middle (d + 1) n) _))
  have hpow : 0 < (2 : ℕ) ^ n := by positivity
  induction D with
  | zero =>
    have h0 := step m
    rw [hm] at h0
    simp only [Nat.add_zero, zero_add, mul_one]
    omega
  | succ D ih =>
    have h1 := step (n / 2 + D)
    rw [Nat.add_succ, ← Nat.succ_eq_add_one]
    calc 2 * (ball n ((n / 2 + D).succ)).card
        ≤ 2 * ((ball n (n / 2 + D)).card + n.choose (n / 2)) := Nat.mul_le_mul_left _ h1
      _ = 2 * (ball n (n / 2 + D)).card + 2 * n.choose (n / 2) := by ring
      _ ≤ _ := by linarith only [ih]

-- Take n = 2^(2t), so the central binomial coefficient occupies less than a 2⁻ᵗ
-- fraction of the cube. The number of repetitions k need grow only linearly in t.
private theorem parameters (p : Polynomial ℕ) (d : ℕ) :
    ∃ n k : ℕ, 2 ≤ n ∧ 1 ≤ k ∧ 8 * p.eval n ≤ 2 ^ k ∧
      4 * (k ^ d + 1) * n.choose (n / 2) ≤ 2 ^ n := by
  let A := 2 * p.natDegree + 4
  let B := 4 * (A ^ d + 1)
  have hB : 0 < (B : ℝ) := by dsimp [B]; positivity
  have hev := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) d (r := 2) (by norm_num)).bound
    (inv_pos.mpr hB)
  obtain ⟨t, ht, h1, hc⟩ := (hev.and ((Filter.eventually_ge_atTop 1).and
    (Filter.eventually_ge_atTop (p.eval 1)))).exists
  simp only [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)] at ht
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t : ℝ) ^ d)] at ht
  have htB : B * t ^ d ≤ 2 ^ t := by
    exact_mod_cast (by rwa [inv_mul_eq_div, le_div_iff₀ hB, mul_comm] at ht :
      (B : ℝ) * (t : ℝ) ^ d ≤ 2 ^ t)
  let n := 2 ^ (2 * t)
  let k := A * t
  have hn : 2 ≤ n :=
    Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ 2 * t by omega)
  have hpoly : p.eval n ≤ p.eval 1 * n ^ p.natDegree := by
    simp only [Polynomial.eval_eq_sum_range, one_pow, mul_one, sum_mul]
    exact sum_le_sum fun i hi => Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega)
      (Nat.le_of_lt_succ (mem_range.mp hi)))
  have hsize : 8 * p.eval n ≤ 2 ^ k := by
    calc 8 * p.eval n ≤ 8 * (2 ^ t * n ^ p.natDegree) := Nat.mul_le_mul_left _
          (hpoly.trans (Nat.mul_le_mul_right _ (hc.trans Nat.lt_two_pow_self.le)))
      _ = 2 ^ (3 + (t + 2 * t * p.natDegree)) := by
        rw [pow_add 2 3, pow_add 2 t, pow_mul 2 (2 * t)]
        rfl
      _ ≤ 2 ^ k := by
        apply Nat.pow_le_pow_right (by decide)
        dsimp [k, A]
        linarith only [h1]
  have hn' : n = 2 ^ (2 * t - 1) * 2 := by
    change 2 ^ (2 * t) = _
    conv_lhs => rw [show 2 * t = (2 * t - 1) + 1 by omega, pow_succ]
  have hch := MathlibExt.NumberTheory.OeisConjecturesWanted.size_choose_two_pow
    (2 * t) (by omega)
  have hcbin : n.choose (n / 2) < 2 ^ (n - t) := by
    have hh : n / 2 = 2 ^ (2 * t - 1) := by rw [hn']; omega
    rw [hh]
    apply Nat.size_le.mp
    dsimp [n]
    omega
  have hk : 4 * (k ^ d + 1) ≤ 2 ^ t := by
    apply le_trans _ htB
    have hpos : 1 ≤ t ^ d := Nat.one_le_pow _ _ h1
    dsimp [B, k]
    rw [mul_pow]
    linarith only [hpos]
  have hkpos : 0 < k := Nat.mul_pos (by dsimp [A]; omega) h1
  refine ⟨n, k, hn, hkpos, hsize, ?_⟩
  calc 4 * (k ^ d + 1) * n.choose (n / 2) ≤ 2 ^ t * 2 ^ (n - t) := Nat.mul_le_mul hk hcbin.le
    _ = 2 ^ n := by
      rw [← pow_add, Nat.add_sub_of_le]
      exact (Nat.lt_two_pow_self).le.trans
        (Nat.pow_le_pow_right (by decide) (by omega))

private theorem output_true (l : List Bool) :
    l.getD (l.length - 1) false = true ↔ l.getLast? = some true := by
  rw [List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
  cases l[l.length - 1]? <;> simp

private theorem majority_on_cube {n : ℕ} (x : Cube n) :
    majorityDec (List.ofFn (assign x)) = decide (n < 2 * x.card) := by
  simp [majorityDec, ← List.countP_eq_length_filter, assign]

/-- **Majority is not in AC0.** The majority language is not in the class $\mathsf{AC}^0$.

Source: M. Ajtai, "Σ₁¹-formulae on finite structures", Annals
of Pure and Applied Logic 24 (1983), 1-48; J. Håstad, "Almost optimal lower bounds for
small depth circuits" (STOC 1986). -/
public theorem majority_not_in_ac0 :
    majorityDec ∉ AC0 := by
  classical
  rintro ⟨d, p, C, h⟩
  obtain ⟨n, k, hn, hk, hsize, hmiddle⟩ := parameters p d
  obtain ⟨_, hm, hlen, hdepth, heval⟩ := h n
  obtain ⟨P, E, hE, hp, hP⟩ := circuit_approx hk (C n) hm
  let j := (C n).length - 1
  have hd : (circuitDepths (C n)).getD j 0 ≤ d := by
    by_cases hj : j < (circuitDepths (C n)).length
    · rw [List.getD_eq_getElem _ _ hj]
      exact (le_fold_max (List.getElem_mem _)).trans hdepth
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hj)]
      exact Nat.zero_le _
  have hq := polys_mono (Nat.pow_le_pow_right hk hd) (hp j)
  have hagree := agreement_bound Eᶜ hq (by
    intro x hx
    rw [hP x (mem_compl.mp hx) j]
    have ht := heval (List.ofFn (assign x)) (List.length_ofFn ..)
    have hread : (fun i : Fin n => (List.ofFn (assign x)).getD i.val false) = assign x := by
      funext i
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
      simp
    rw [hread, majority_on_cube, ← output_true, length_circuitEval] at ht
    by_cases hw : n < 2 * x.card
    · change bit ((circuitEval (C n) (assign x)).getD ((C n).length - 1) false) = _
      rw [ht.mp (by simpa using hw)]
      simp [hw, bit]
    · have := mt ht.mpr (by simpa using hw)
      simp_all [bit, j])
  have herr : 8 * E.card ≤ 2 ^ n := by
    apply Nat.le_of_mul_le_mul_left (c := 2 ^ k) _ (by positivity)
    calc 2 ^ k * (8 * E.card) = 8 * (2 ^ k * E.card) := by ring
      _ ≤ 8 * ((C n).length * 2 ^ n) := Nat.mul_le_mul_left _ hE
      _ ≤ 2 ^ k * 2 ^ n := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ ((Nat.mul_le_mul_left _ hlen).trans hsize)
  rw [card_compl] at hagree
  simp only [Fintype.card_finset, Fintype.card_fin] at hagree
  have hb := ball_bound n (k ^ d) hn
  have hpos : 0 < (2 : ℕ) ^ n := by positivity
  have hsub : 2 ^ n ≤ 2 ^ n - E.card + E.card := by omega
  nlinarith only [hagree, hb, hmiddle, herr, hpos, hsub]

end MetaMathlibExt.Complexity.KeyTheorems.MajorityNotInAC0
