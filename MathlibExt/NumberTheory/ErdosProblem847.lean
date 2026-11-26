/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Combinatorics.Additive.AP.Three.Defs

import Mathlib.Combinatorics.HalesJewett
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.NormNum

/-!
# Erdős Problem 847

We prove the refutation of Erdős Problem 847 from the construction of Reiher, Rödl and
Sales ([arXiv:2311.08556v2](https://arxiv.org/html/2311.08556v2), Theorems 1.4 and 1.7).
Only a positive uniform proportion is needed here. We use shift paths on ordered pairs:
selecting pairs from the first side of a bipartition to the second gives the proportion `1/4`.
The link at each pair has a bipartition, which simplifies the partite amalgamation for triples.

The sparse line selection uses Hales–Jewett on subcubes formed by choosing one slot per bin.
Lines through a common point have disjoint moving coordinates unless they are equal. This keeps
all nontrivial progressions in standard copies during amalgamation. Digit encoding in base five
reflects progressions, and gaps separate the finite blocks for different numbers of colours.

The original statement (source record `FC-ErdosProblem847`, ported from FormalConjectures
`ErdosProblems/847.lean`) and its declaration names are retained.
-/

open Function Finset Combinatorics

namespace MathlibExt.NumberTheory.ErdosProblem847Wanted

noncomputable section

/-! ### The shift template -/

private def Shift (a b c : ℕ × ℕ) : Prop :=
  a.1 < a.2 ∧ a.2 = b.1 ∧ b.1 < b.2 ∧ b.2 = c.1 ∧ c.1 < c.2

private def Adj (v a : ℕ × ℕ) : Prop :=
  (a.2 = v.1 ∧ a.1 < a.2) ∨ (a.1 > v.2 ∧ a.1 < a.2)

private theorem shift_link {v a b : ℕ × ℕ}
    (h : Shift v a b ∨ Shift v b a ∨ Shift a v b ∨ Shift b v a ∨
      Shift a b v ∨ Shift b a v) : Adj v a ↔ ¬ Adj v b := by
  unfold Shift Adj at *
  omega

private theorem shift_ramsey (r : ℕ) :
    ∃ N : ℕ, ∀ C : (Fin N × Fin N) → Fin r,
      ∃ a b c : Fin N × Fin N, Shift (a.1, a.2) (b.1, b.2) (c.1, c.2) ∧
        C a = C b ∧ C b = C c := by
  classical
  refine ⟨3 ^ r + 1, fun C ↦ ?_⟩
  let N := 3 ^ r + 1
  change ((Fin N × Fin N) → Fin r) at C
  by_contra! h
  let reach (b : Fin N) (k : Fin r) := ∃ a : Fin N, a < b ∧ C (a, b) = k
  let reach₂ (c : Fin N) (k : Fin r) :=
    ∃ b : Fin N, b < c ∧ C (b, c) = k ∧ reach b k
  let state (b : Fin N) (k : Fin r) : Fin 3 :=
    if reach₂ b k then 2 else if reach b k then 1 else 0
  have step {a b : Fin N} (hab : a < b) : state a (C (a, b)) < state b (C (a, b)) := by
    let k := C (a, b)
    have hb : reach b k := ⟨a, hab, rfl⟩
    have ha₂ : ¬ reach₂ a k := by
      rintro ⟨d, hda, hd, e, hed, he⟩
      exact h (e, d) (d, a) (a, b) ⟨hed, rfl, hda, rfl, hab⟩ (he.trans hd.symm) hd
    by_cases ha : reach a k
    · have hb₂ : reach₂ b k := ⟨a, hab, rfl, ha⟩
      simp [state, ha, ha₂, hb₂, k]
    · by_cases hb₂ : reach₂ b k <;> simp [state, ha, ha₂, hb, hb₂, k]
  have hinj : Injective state := by
    intro a b hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact False.elim ((step hlt).ne (congrFun hab _))
    · exact heq
    · exact False.elim ((step hgt).ne (congrFun hab.symm _))
  have hc := Fintype.card_le_of_injective state hinj
  simp [N] at hc



/-! ### Sparse Hales–Jewett line systems -/

private theorem line_injective {A I : Type} (l : Line A I) : Injective l := by
  obtain ⟨i, hi⟩ := l.proper
  intro a b h
  simpa only [l.apply_none _ _ hi] using congrFun h i

private def move {A I : Type} [Fintype I] (l : Line A I) : Finset I :=
  univ.filter fun i ↦ (l.idxFun i).isNone

private theorem mem_move {A I : Type} [Fintype I] (l : Line A I) (i : I) :
    i ∈ move l ↔ l.idxFun i = none := by simp [move]

private def collide {A I : Type} (l₁ l₂ : Line A I) : Prop :=
  (∃ a b, l₁ a = l₂ b) ∧ ∃ i, l₁.idxFun i = none ∧ l₂.idxFun i = none

noncomputable section

open Classical in
private theorem card_fibers {X Y : Type} [Fintype Y] (S : Finset X) (f : X → Y)
    (b : ℕ) (hb : ∀ y, (S.filter fun x ↦ f x = y).card ≤ b) :
    S.card ≤ Fintype.card Y * b := by
  have h := sum_card_fiberwise_eq_card_filter S (univ : Finset Y) f
  simp only [mem_univ, filter_true] at h
  rw [← h]
  exact Finset.sum_le_card_nsmul _ _ _ fun y _ ↦ hb y

private theorem card_biUnion_bound {X Y : Type} [DecidableEq Y] (S : Finset X)
    (T : X → Finset Y) (b : ℕ) (hb : ∀ x ∈ S, (T x).card ≤ b) :
    (S.biUnion T).card ≤ S.card * b :=
  card_biUnion_le.trans (Finset.sum_le_card_nsmul S _ _ hb)

section Sparse

variable {A I : Type} {n : ℕ}

private abbrev Word (A I : Type) (n : ℕ) := I × Fin n → A
private abbrev Frame (A I : Type) (n : ℕ) := (I → Fin n) × Word A I n

private def frameWord (p : Frame A I n) (w : I → A) : Word A I n :=
  fun j ↦ if j.2 = p.1 j.1 then w j.1 else p.2 j

private def frameLine (p : Frame A I n) (l : Line A I) : Line A (I × Fin n) where
  idxFun j := if j.2 = p.1 j.1 then l.idxFun j.1 else some (p.2 j)
  proper := by
    obtain ⟨i, hi⟩ := l.proper
    exact ⟨(i, p.1 i), by simp [hi]⟩

private theorem frameLine_apply (p : Frame A I n) (l : Line A I) (a : A) :
    frameLine p l a = frameWord p (l a) := by
  funext j
  by_cases h : j.2 = p.1 j.1 <;> simp [Line.coe_apply, frameLine, frameWord, h]

private def fits (p : Frame A I n) (v : Word A I n) : Prop :=
  ∀ j, j.2 ≠ p.1 j.1 → p.2 j = v j

variable [Fintype A] [Fintype I]

open Classical in
private theorem count_fills (v : Word A I n) (p : I → Fin n)
    (S : Finset (Frame A I n)) (h : ∀ e ∈ S, e.1 = p ∧ fits e v) :
    S.card ≤ Fintype.card (I → A) := by
  refine card_le_card_of_injOn (fun e : Frame A I n ↦ fun i ↦ e.2 (i, p i))
    (t := univ) (fun _ _ ↦ mem_univ _) ?_
  intro e he f hf hef
  obtain ⟨he₁, he₂⟩ := h e he
  obtain ⟨hf₁, hf₂⟩ := h f hf
  refine Prod.ext (he₁.trans hf₁.symm) (funext fun j ↦ ?_)
  by_cases hj : j.2 = p j.1
  · have hj' : j = (j.1, p j.1) := Prod.ext rfl hj
    rw [hj']
    exact congrFun hef j.1
  · exact (he₂ j (he₁ ▸ hj)).trans (hf₂ j (hf₁ ▸ hj)).symm

open Classical in
private theorem count_fit (v : Word A I n) :
    (univ.filter fun e : Frame A I n ↦ fits e v).card ≤
      Fintype.card (I → Fin n) * Fintype.card (I → A) := by
  classical
  apply card_fibers _ (Prod.fst : Frame A I n → (I → Fin n))
  intro p
  apply count_fills v p
  intro e he
  simp only [mem_filter, mem_univ, true_and] at he
  exact ⟨he.2, he.1⟩

open Classical in
private theorem count_fit_through (v : Word A I n) (j : I × Fin n) :
    (univ.filter fun e : Frame A I n ↦ fits e v ∧ e.1 j.1 = j.2).card * n ≤
      Fintype.card (I → Fin n) * Fintype.card (I → A) := by
  classical
  let P := univ.filter fun e : Frame A I n ↦ fits e v ∧ e.1 j.1 = j.2
  have aux : (P ×ˢ (univ : Finset (Fin n))).card ≤
      Fintype.card (I → Fin n) * Fintype.card (I → A) := by
    let f (q : Frame A I n × Fin n) : (I → Fin n) × (I → A) :=
      (update q.1.1 j.1 q.2, fun i ↦ q.1.2 (i, q.1.1 i))
    have hf : (P ×ˢ (univ : Finset (Fin n))).card ≤ (univ : Finset
        ((I → Fin n) × (I → A))).card := by
      refine card_le_card_of_injOn f (fun _ _ ↦ mem_univ _) ?_
      intro x hx y hy hxy
      have hx' := (mem_filter.mp (mem_product.mp hx).1).2
      have hy' := (mem_filter.mp (mem_product.mp hy).1).2
      have hab := congrArg Prod.fst hxy
      have hcd := congrArg Prod.snd hxy
      have hslots : x.1.1 = y.1.1 := by
        funext i
        by_cases h : i = j.1
        · subst i
          exact hx'.2.trans hy'.2.symm
        · simpa only [f, update_of_ne h] using congrFun hab i
      refine Prod.ext (Prod.ext hslots (funext fun k ↦ ?_)) ?_
      · by_cases hk : k.2 = x.1.1 k.1
        · have hxk : k = (k.1, x.1.1 k.1) := Prod.ext rfl hk
          have hyk : k = (k.1, y.1.1 k.1) := Prod.ext rfl (hslots ▸ hk)
          exact (congrArg x.1.2 hxk).trans ((congrFun hcd k.1).trans (congrArg y.1.2 hyk).symm)
        · exact (hx'.1 k hk).trans (hy'.1 k (hslots ▸ hk)).symm
      · simpa only [f, update_self] using congrFun hab j.1
    simpa only [card_univ, Fintype.card_prod] using hf
  simpa only [card_product, card_univ, Fintype.card_fin] using aux

private def degree (L : Finset (Line A (I × Fin n))) (v : Word A I n) : ℕ := by
  classical
  exact (L.filter fun l ↦ ∃ a, l a = v).card

open Classical in
private theorem sum_degree (L : Finset (Line A (I × Fin n))) :
    (∑ v : Word A I n, degree L v) = L.card * Fintype.card A := by
  classical
  calc
    (∑ v : Word A I n, degree L v) =
        ∑ v : Word A I n, ∑ l ∈ L, if ∃ a, l a = v then 1 else 0 := by
      exact sum_congr rfl fun v _ ↦ (Finset.sum_boole _ _).symm
    _ = ∑ l ∈ L, ∑ v : Word A I n, if ∃ a, l a = v then 1 else 0 := Finset.sum_comm
    _ = ∑ l ∈ L, (univ.image (l : A → Word A I n)).card := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext v
      simp
    _ = _ := by simp [Finset.card_image_of_injective _ (line_injective _)]

private def goodFrames (d : ℕ) (L : Finset (Line A (I × Fin n))) : Finset (Frame A I n) := by
  classical
  exact univ.filter fun p ↦
    (∀ v, fits p v → degree L v < d) ∧
      ∀ l ∈ L, ∀ a j, l.idxFun j = none → j.2 = p.1 j.1 → ¬ fits p (l a)

private theorem frameLine_good {d : ℕ} {L : Finset (Line A (I × Fin n))}
    {p : Frame A I n} (hp : p ∈ goodFrames d L) (l : Line A I) :
    (∀ a, degree L (frameLine p l a) < d) ∧
      ∀ m ∈ L, ¬ collide (frameLine p l) m := by
  classical
  have hp' := (mem_filter.mp hp).2
  have hfit (a : A) : fits p (frameLine p l a) := by
    rw [frameLine_apply]
    intro j hj
    simp [frameWord, hj]
  refine ⟨fun a ↦ hp'.1 _ (hfit a), ?_⟩
  rintro m hm ⟨⟨a, b, hab⟩, j, h₁, h₂⟩
  have hsel : j.2 = p.1 j.1 := by
    by_contra h
    simp [frameLine, h] at h₁
  exact hp'.2 m hm b j h₂ hsel (hab ▸ hfit a)

-- Moving coordinates are confined to at most one slot per bin.
private def BinLine (l : Line A (I × Fin n)) : Prop :=
  ∀ i j k, l.idxFun (i, j) = none → l.idxFun (i, k) = none → j = k

omit [Fintype A] in
private theorem move_card_le {l : Line A (I × Fin n)} (h : BinLine l) :
    (move l).card ≤ Fintype.card I := by
  classical
  apply card_le_card_of_injOn Prod.fst (t := univ) (fun _ _ ↦ mem_univ _)
  rintro ⟨i, j⟩ hj ⟨i', k⟩ hk (rfl : i = i')
  exact Prod.ext rfl (h i j k ((mem_move _ _).mp hj) ((mem_move _ _).mp hk))

open Classical in
private theorem goodFrames_nonempty [Nonempty A] [NeZero n] (d K : ℕ) (hK : 0 < K)
    (hd : 4 * K * Fintype.card A * Fintype.card (I → A) ≤ d)
    (hn : 4 * K * Fintype.card A * Fintype.card I * Fintype.card (I → A) ≤ n)
    (L : Finset (Line A (I × Fin n))) (hL : L.card ≤ K * Fintype.card (Word A I n))
    (hbin : ∀ l ∈ L, BinLine l) : (goodFrames d L).Nonempty := by
  let V := Fintype.card (Word A I n)
  let W := Fintype.card (I → A)
  let P := Fintype.card (I → Fin n)
  let a := Fintype.card A
  let m := Fintype.card I
  have hV : 0 < V := Fintype.card_pos
  have hP : 0 < P := Fintype.card_pos
  let S := univ.filter fun v : Word A I n ↦ d ≤ degree L v
  let F₁ := S.biUnion fun v ↦ univ.filter fun e : Frame A I n ↦ fits e v
  let F₂ := L.biUnion fun l ↦ (univ ×ˢ move l).biUnion fun aj : A × (I × Fin n) ↦
    univ.filter fun e : Frame A I n ↦ fits e (l aj.1) ∧ e.1 aj.2.1 = aj.2.2
  have hS : S.card * d ≤ L.card * a := by
    rw [← sum_degree L]
    exact (Finset.card_nsmul_le_sum S (degree L) d fun v hv ↦ (mem_filter.mp hv).2).trans
      (Finset.sum_le_sum_of_subset (subset_univ _) )
  have hF₁ : F₁.card ≤ S.card * (P * W) :=
    card_biUnion_bound S _ _ fun v _ ↦ count_fit v
  have hF₁' : 4 * F₁.card ≤ P * V := by
    calc
      4 * F₁.card ≤ 4 * (S.card * (P * W)) := Nat.mul_le_mul_left _ hF₁
      _ = 4 * S.card * W * P := by ring
      _ ≤ V * P := by
        apply Nat.mul_le_mul_right
        have h := (Nat.mul_le_mul_left S.card hd).trans
          (hS.trans (Nat.mul_le_mul_right a hL))
        have hk : 0 < K * a := Nat.mul_pos hK Fintype.card_pos
        apply Nat.le_of_mul_le_mul_right _ hk
        calc
          (4 * S.card * W) * (K * a) = S.card * (4 * K * a * W) := by ring
          _ ≤ K * V * a := h
          _ = V * (K * a) := by ring
      _ = _ := Nat.mul_comm ..
  have hF₂ : F₂.card * n ≤ L.card * (a * m * (P * W)) := by
    calc
      F₂.card * n ≤ (∑ l ∈ L, #((univ ×ˢ move l).biUnion
          fun aj : A × (I × Fin n) ↦ univ.filter fun e : Frame A I n ↦
            fits e (l aj.1) ∧ e.1 aj.2.1 = aj.2.2)) * n :=
        Nat.mul_le_mul_right _ card_biUnion_le
      _ ≤ _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_card_nsmul
        intro l hl
        calc
          _ ≤ (∑ aj ∈ (univ ×ˢ move l : Finset (A × (I × Fin n))), #(
            univ.filter fun e : Frame A I n ↦
              fits e (l aj.1) ∧ e.1 aj.2.1 = aj.2.2)) * n :=
            Nat.mul_le_mul_right _ card_biUnion_le
          _ ≤ _ := by
            rw [Finset.sum_mul]
            refine (Finset.sum_le_card_nsmul _ _ (P * W) fun aj _ ↦
              count_fit_through (l aj.1) aj.2).trans ?_
            rw [nsmul_eq_mul, card_product, card_univ]
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left a (move_card_le (hbin l hl)))
  have hF₂' : 4 * F₂.card ≤ P * V := by
    apply Nat.le_of_mul_le_mul_right _ (Nat.pos_of_ne_zero (NeZero.ne n))
    calc
      (4 * F₂.card) * n = 4 * (F₂.card * n) := by ring
      _ ≤ 4 * ((K * V) * (a * m * (P * W))) :=
        Nat.mul_le_mul_left _ (hF₂.trans (Nat.mul_le_mul_right _ hL))
      _ = P * V * (4 * K * a * m * W) := by ring
      _ ≤ P * V * n := Nat.mul_le_mul_left _ hn
  have hlt : (F₁ ∪ F₂).card < Fintype.card (Frame A I n) := by
    have hcard : (F₁ ∪ F₂).card ≤ F₁.card + F₂.card := Finset.card_union_le _ _
    have hpos : 0 < P * V := Nat.mul_pos hP hV
    rw [Fintype.card_prod]
    change _ < P * V
    omega
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := F₁ ∪ F₂) (t := univ)
    (by simpa only [card_univ] using hlt)
  refine ⟨p, mem_filter.mpr ?_⟩
  refine ⟨mem_univ _, fun v hv ↦ ?_, fun l hl b j hj hj' hv ↦ ?_⟩
  · by_contra! h
    exact hp (mem_union_left _ (mem_biUnion.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, h⟩,
      mem_filter.mpr ⟨mem_univ _, hv⟩⟩))
  · exact hp (mem_union_right _ (mem_biUnion.mpr ⟨l, hl, mem_biUnion.mpr
      ⟨(b, j), mem_product.mpr ⟨mem_univ _, (mem_move _ _).mpr hj⟩,
      mem_filter.mpr ⟨mem_univ _, hv, hj'.symm⟩⟩⟩))

end Sparse

-- A bounded greedy construction, using integer halving rather than logarithms.
private theorem greedy {X : Type} (size bad : X → ℕ) (x₀ : X) (m t : ℕ) (hm : 0 < m)
    (h₀ : size x₀ = 0) (hbad : bad x₀ < 2 ^ t)
    (extend : ∀ x, size x < m * t → 0 < bad x →
      ∃ y, size y ≤ size x + 1 ∧ (m + 1) * bad y ≤ m * bad x) : ∃ x, bad x = 0 := by
  have phase (x : X) (s : ℕ) (hs : size x + s ≤ m * t) :
      ∃ y, size y ≤ size x + s ∧ (m + s) * bad y ≤ m * bad x := by
    induction s with
    | zero => exact ⟨x, by simp, by simp⟩
    | succ s ih =>
      obtain ⟨z, hz, hzb⟩ := ih (by omega)
      by_cases h : bad z = 0
      · exact ⟨z, by omega, by simp [h]⟩
      obtain ⟨y, hy, hyb⟩ := extend z (by omega) (by omega)
      have hle : bad y ≤ bad z := by
        by_contra! hh
        have := Nat.mul_lt_mul_of_pos_left hh hm
        nlinarith only [this, hyb]
      have hsle := Nat.mul_le_mul_left s hle
      exact ⟨y, by omega, by nlinarith only [hyb, hsle, hzb]⟩
  have iterate (j : ℕ) (hj : j ≤ t) :
      ∃ y, size y ≤ m * j ∧ 2 ^ j * bad y ≤ bad x₀ := by
    induction j with
    | zero => exact ⟨x₀, by simp [h₀], by simp⟩
    | succ j ih =>
      obtain ⟨x, hx, hxb⟩ := ih (by omega)
      have hstep : m * (j + 1) ≤ m * t := Nat.mul_le_mul_left _ hj
      obtain ⟨y, hy, hyb⟩ := phase x m (by rw [Nat.mul_succ] at hstep; omega)
      refine ⟨y, by rw [Nat.mul_succ]; omega, ?_⟩
      have half : 2 * bad y ≤ bad x := by
        apply Nat.le_of_mul_le_mul_left _ hm
        nlinarith only [hyb]
      rw [pow_succ, mul_assoc]
      exact (Nat.mul_le_mul_left _ half).trans hxb
  obtain ⟨x, _, hx⟩ := iterate t le_rfl
  refine ⟨x, ?_⟩
  by_contra! h
  have hpos : 1 ≤ bad x := by omega
  have := Nat.mul_le_mul_left (2 ^ t) hpos
  omega

-- A fixed uncovered frame suffices: its bounded number of template lines
-- covers all the colourings still missing a witness.
set_option maxHeartbeats 800000 in
-- The greedy step elaborates both cardinal estimates and the preservation of sparse incidence.
private theorem sparseHJ (A : Type) [Finite A] [Nonempty A] (r : ℕ) :
    ∃ (J : Type) (_ : Fintype J) (S : Finset (Line A J)),
      (∀ l ∈ S, ∀ m ∈ S, collide l m → l = m) ∧
      ∀ c : (J → A) → Fin r, ∃ l ∈ S, l.IsMono c := by
  classical
  let F := Fintype.ofFinite A
  obtain ⟨I, _, hHJ⟩ := Line.exists_mono_in_high_dimension A (Fin r)
  let T := { f : I → Option A // ∃ i, f i = none }
  let toLine (f : T) : Line A I := ⟨f.1, f.2⟩
  let M := Fintype.card (I → Option A)
  have hM : 0 < M := Fintype.card_pos
  let K := M * (r + 1)
  have hK : 0 < K := Nat.mul_pos hM (Nat.succ_pos _)
  let d := 4 * K * Fintype.card A * Fintype.card (I → A)
  let n := d * Fintype.card I + 1
  let _ : NeZero n := ⟨Nat.succ_ne_zero _⟩
  let J := I × Fin n
  let V := Fintype.card (J → A)
  have hV : 0 < V := Fintype.card_pos
  let t := (r + 1) * V
  let X := { L : Finset (Line A J) // (∀ l ∈ L, BinLine l) ∧
    (∀ v, degree L v ≤ d) ∧ (∀ l ∈ L, ∀ m ∈ L, collide l m → l = m) }
  let size (x : X) := x.1.card
  let avoid (x : X) := (univ : Finset ((J → A) → Fin r)).filter fun c ↦
    ∀ l ∈ x.1, ¬ l.IsMono c
  let x₀ : X := ⟨∅, by simp [degree]⟩
  have hbudget : M * t = K * V := by simp only [t, K, mul_assoc]
  have hstart : (avoid x₀).card < 2 ^ t := by
    calc
      (avoid x₀).card ≤ Fintype.card ((J → A) → Fin r) := card_le_univ _
      _ = r ^ V := by rw [Fintype.card_fun, Fintype.card_fin]
      _ < 2 ^ t := by
        rw [show t = (r + 1) * V by rfl, pow_mul]
        exact Nat.pow_lt_pow_left (by
          exact (Nat.lt_succ_self r).trans (Nat.lt_two_pow_self (n := r + 1))) hV.ne'
  have step (x : X) (hx : size x < M * t) (hb : 0 < (avoid x).card) :
      ∃ y : X, size y ≤ size x + 1 ∧ (M + 1) * (avoid y).card ≤ M * (avoid x).card := by
    obtain ⟨p, hp⟩ := goodFrames_nonempty (n := n) d K hK le_rfl
      (by dsimp [n, d]; rw [Nat.mul_right_comm _ (Fintype.card (I → A))]; omega)
      x.1 (by rw [hbudget] at hx; exact hx.le) x.2.1
    let cover (f : T) := (avoid x).filter fun c ↦ (frameLine p (toLine f)).IsMono c
    have hcover : avoid x ⊆ (univ : Finset T).biUnion cover := by
      intro c hc
      obtain ⟨l, col, hcol⟩ := hHJ (fun w ↦ c (frameWord p w))
      refine mem_biUnion.mpr ⟨⟨l.idxFun, l.proper⟩, mem_univ _, mem_filter.mpr ⟨hc, col, ?_⟩⟩
      intro a
      simpa only [toLine, frameLine_apply] using hcol a
    have hmT : Fintype.card T ≤ M := Fintype.card_subtype_le _
    have hchoose : ∃ f : T, (avoid x).card ≤ M * (cover f).card := by
      by_contra! h
      have hsum := card_le_card hcover |>.trans (card_biUnion_le (s := (univ : Finset T)))
      have ht : (univ : Finset T).Nonempty := by
        obtain ⟨c, hc⟩ := card_pos.mp hb
        obtain ⟨f, hf, _⟩ := mem_biUnion.mp (hcover hc)
        exact ⟨f, hf⟩
      have hstrict : (∑ f : T, M * (cover f).card) < ∑ _f : T, (avoid x).card :=
        Finset.sum_lt_sum_of_nonempty ht fun f _ ↦ h f
      rw [← Finset.mul_sum] at hstrict
      simp only [sum_const, card_univ, nsmul_eq_mul] at hstrict
      exact (not_lt_of_ge ((Nat.mul_le_mul_right _ hmT).trans (Nat.mul_le_mul_left _ hsum)))
        hstrict
    obtain ⟨f, hf⟩ := hchoose
    let l := frameLine p (toLine f)
    have hg := frameLine_good hp (toLine f)
    have hnot : l ∉ x.1 := by
      intro hmem
      apply hg.2 l hmem
      obtain ⟨i, hi⟩ := l.proper
      exact ⟨⟨Classical.arbitrary A, Classical.arbitrary A, rfl⟩, i, hi, hi⟩
    let y : X := ⟨insert l x.1, by
      refine ⟨?_, ?_, ?_⟩
      · intro z hz
        rcases mem_insert.mp hz with rfl | hz
        · intro i j k hj hk
          change (if j = p.1 i then (toLine f).idxFun i else some (p.2 (i, j))) = none at hj
          change (if k = p.1 i then (toLine f).idxFun i else some (p.2 (i, k))) = none at hk
          split at hj <;> split at hk <;> simp_all
        · exact x.2.1 _ hz
      · intro v
        by_cases h : ∃ a, l a = v
        · obtain ⟨a, rfl⟩ := h
          have hl : ∃ b, l b = l a := ⟨a, rfl⟩
          have hd' : degree x.1 (l a) < d := hg.1 a
          unfold degree at *
          rw [filter_insert, ite_eq_left hl,
            card_insert_of_notMem (fun h ↦ hnot (mem_filter.mp h).1)]
          omega
        · simpa [degree, filter_insert, h] using x.2.2.1 v
      · intro u hu v hv huv
        rcases mem_insert.mp hu with rfl | hu <;> rcases mem_insert.mp hv with rfl | hv
        · rfl
        · exact False.elim (hg.2 _ hv huv)
        · obtain ⟨⟨a, b, hab⟩, i, h₁, h₂⟩ := huv
          exact False.elim (hg.2 _ hu ⟨⟨b, a, hab.symm⟩, i, h₂, h₁⟩)
        · exact x.2.2.2 u hu v hv huv⟩
    have hy : avoid y = (avoid x).filter fun c ↦ ¬ l.IsMono c := by
      ext c
      simp only [avoid, y, mem_filter, mem_univ, true_and, mem_insert, forall_eq_or_imp]
      exact and_comm
    have hsplit : (cover f).card + (avoid y).card = (avoid x).card := by
      simpa only [hy, cover, l] using
        (Finset.card_filter_add_card_filter_not (s := avoid x) (fun c ↦ l.IsMono c))
    refine ⟨y, by simp [size, y, card_insert_of_notMem hnot], ?_⟩
    nlinarith only [hf, hsplit, congrArg (M * ·) hsplit]
  obtain ⟨x, hx⟩ := greedy size (fun x ↦ (avoid x).card) x₀ M t hM rfl hstart step
  refine ⟨J, inferInstance, x.1, x.2.2.2, fun c ↦ ?_⟩
  by_contra! h
  exact (notMem_empty c) (card_eq_zero.mp hx ▸ mem_filter.mpr ⟨mem_univ _, h⟩)

end


/-! ### Partite pictures -/

private abbrev Triple (X : Type) := Fin 3 → X

private def PointAP {X D : Type} (rep : X → D → Fin 3) (t : Triple X) : Prop :=
  ∀ j, (rep (t 0) j).val + (rep (t 2) j).val = (rep (t 1) j).val + (rep (t 1) j).val

private def Forward {X D : Type} (rep : X → D → Fin 3) (t : Triple X) : Prop :=
  ∀ j, rep (t 0) j ≤ rep (t 1) j

private def rev : Fin 3 → Fin 3 := ![2, 1, 0]

private def Ordered {V : Type} (val : V → ℕ × ℕ) (t : Triple V) : Prop :=
  Shift (val (t 0)) (val (t 1)) (val (t 2))

private structure Picture {V : Type} (val : V → ℕ × ℕ) where
  X : Type
  finiteX : Finite X
  D : Type
  finiteD : Finite D
  rep : X → D → Fin 3
  inj : Injective rep
  lab : X → V
  recover (t : Triple X) (ht : PointAP rep t) (hne : t 0 ≠ t 1) :
    (Forward rep t ∧ Ordered val (lab ∘ t)) ∨
      (Forward rep (t ∘ rev) ∧ Ordered val (lab ∘ t ∘ rev))

private theorem rev_zero : rev 0 = 2 := rfl
private theorem rev_one : rev 1 = 1 := rfl
private theorem rev_two : rev 2 = 0 := rfl

private theorem ap_reverse {X D : Type} {rep : X → D → Fin 3} {t : Triple X}
    (h : PointAP rep t) : PointAP rep (t ∘ rev) := by
  intro j
  simpa only [Function.comp_apply, rev_zero, rev_one, rev_two, Nat.add_comm] using h j

private theorem ap_agree {X D : Type} {rep : X → D → Fin 3} (hinj : Injective rep)
    {t s : Triple X} (ht : PointAP rep t) (hs : PointAP rep s)
    {i j : Fin 3} (hij : i ≠ j) (hi : t i = s i) (hj : t j = s j) : t = s := by
  have third (k : Fin 3) : t k = s k := by
    by_cases hki : k = i
    · simpa only [hki] using hi
    by_cases hkj : k = j
    · simpa only [hkj] using hj
    apply hinj
    funext d
    apply Fin.ext
    have e₁ := ht d
    have e₂ := hs d
    have a := congrArg (fun x ↦ (rep x d).val) hi
    have b := congrArg (fun x ↦ (rep x d).val) hj
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> omega
  exact funext third

private theorem ap_labels_distinct {V : Type} {val : V → ℕ × ℕ} (P : Picture val)
    {t : Triple P.X} (h : PointAP P.rep t) (hne : t 0 ≠ t 1) : Injective (P.lab ∘ t) := by
  intro i j heq
  by_contra hij
  rcases P.recover t h hne with ⟨_, hs⟩ | ⟨_, hs⟩ <;>
    unfold Ordered Shift at hs <;>
    simp only [Function.comp_apply, rev_zero, rev_one, rev_two] at hs heq <;>
    have hv := congrArg (fun x ↦ (val x).1) heq <;>
    fin_cases i <;> fin_cases j <;> simp_all <;> omega

private theorem focus_sides {V : Type} {val : V → ℕ × ℕ} (P : Picture val)
    {t : Triple P.X} (h : PointAP P.rep t) (hne : t 0 ≠ t 1) {v : V} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hk : P.lab (t k) = v) :
    Adj (val v) (val (P.lab (t i))) ↔ ¬ Adj (val v) (val (P.lab (t j))) := by
  apply shift_link
  rcases P.recover t h hne with ⟨_, hs⟩ | ⟨_, hs⟩ <;>
    simp only [Ordered, Function.comp_apply, rev_zero, rev_one, rev_two] at hs <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

private theorem genuine_line {X D : Type} (rep : X → D → Fin 3) (hinj : Injective rep)
    {t : Triple X} (h : PointAP rep t) (hf : Forward rep t) (hne : t 0 ≠ t 1) :
    ∃ l : Line (Fin 3) D, ∀ a, rep (t a) = l a := by
  classical
  have hdiff : ∃ j, rep (t 0) j ≠ rep (t 1) j := by
    by_contra! he
    exact hne (hinj (funext he))
  let l : Line (Fin 3) D := ⟨fun j ↦ if rep (t 0) j = rep (t 1) j then
    some (rep (t 0) j) else none, by
      obtain ⟨j, hj⟩ := hdiff
      exact ⟨j, by simp [hj]⟩⟩
  refine ⟨l, fun a ↦ funext fun j ↦ ?_⟩
  have he := h j
  have hl := hf j
  by_cases hj : rep (t 0) j = rep (t 1) j
  · simp only [l, Line.coe_apply, ite_eq_left hj, Option.getD_some]
    fin_cases a <;> simp_all only [Fin.reduceFinMk, Fin.isValue]
    apply Fin.ext
    omega
  · have hd : (rep (t 0) j).val ≠ (rep (t 1) j).val := fun hh ↦ hj (Fin.ext hh)
    simp only [l, Line.coe_apply, ite_eq_right hj, Option.getD_none]
    fin_cases a
    · apply Fin.ext
      change (rep (t 0) j).val = 0
      omega
    · apply Fin.ext
      change (rep (t 1) j).val = 1
      omega
    · apply Fin.ext
      change (rep (t 2) j).val = 2
      omega

private theorem lines_same_of_two {D : Type} {l m : Line (Fin 3) D}
    {a b c d : Fin 3} (hab : a ≠ b) (hcd : c ≠ d) (h₁ : l a = m c) (h₂ : l b = m d) :
    l = m := by
  ext j
  have e₁ := congrFun h₁ j
  have e₂ := congrFun h₂ j
  cases hl : l.idxFun j <;> cases hm : m.idxFun j <;> simp_all

private theorem same_range_of_two {V : Type} {val : V → ℕ × ℕ} (P : Picture val)
    {t s : Triple P.X} (ht : PointAP P.rep t) (hs : PointAP P.rep s)
    (htne : t 0 ≠ t 1) (hsne : s 0 ≠ s 1)
    {x y : P.X} (hxy : x ≠ y) (hx : x ∈ Set.range t ∩ Set.range s)
    (hy : y ∈ Set.range t ∩ Set.range s) : Set.range t = Set.range s := by
  classical
  have hr : Function.Surjective rev := by
    intro a
    refine ⟨rev a, ?_⟩
    fin_cases a <;> rfl
  have conj (u : Triple P.X) (hu : PointAP P.rep u) (hne : u 0 ≠ u 1) :
      ∃ l : Line (Fin 3) P.D, Set.range (P.rep ∘ u) = Set.range (⇑l) := by
    rcases P.recover u hu hne with ⟨hf, _⟩ | ⟨hf, _⟩
    · obtain ⟨l, hl⟩ := genuine_line P.rep P.inj hu hf hne
      exact ⟨l, congrArg Set.range (funext hl)⟩
    · have hne' : (u ∘ rev) 0 ≠ (u ∘ rev) 1 := by
        intro he
        exact (by decide : (2 : Fin 3) ≠ 1) (ap_labels_distinct P hu hne (congrArg P.lab he))
      obtain ⟨l, hl⟩ := genuine_line P.rep P.inj (ap_reverse hu) hf hne'
      refine ⟨l, ?_⟩
      ext z
      change (∃ a, P.rep (u a) = z) ↔ ∃ a, l a = z
      constructor
      · rintro ⟨a, ha⟩
        obtain ⟨b, rfl⟩ := hr a
        exact ⟨b, (hl b).symm.trans ha⟩
      · rintro ⟨a, ha⟩
        exact ⟨rev a, (hl a).trans ha⟩
  obtain ⟨l, hl⟩ := conj t ht htne
  obtain ⟨m, hm⟩ := conj s hs hsne
  have memRep (u : Triple P.X) {z : P.X} (hz : z ∈ Set.range u) :
      P.rep z ∈ Set.range (P.rep ∘ u) := by
    obtain ⟨i, rfl⟩ := hz
    exact ⟨i, rfl⟩
  obtain ⟨a, ha⟩ := hl ▸ memRep t hx.1
  obtain ⟨b, hb⟩ := hl ▸ memRep t hy.1
  obtain ⟨c, hc⟩ := hm ▸ memRep s hx.2
  obtain ⟨d, hd⟩ := hm ▸ memRep s hy.2
  have neArgs (q : Line (Fin 3) P.D) {i j : Fin 3}
      (e₁ : q i = P.rep x) (e₂ : q j = P.rep y) : i ≠ j := by
    rintro rfl
    exact hxy (P.inj (e₁.symm.trans e₂))
  have he := lines_same_of_two (neArgs l ha hb) (neArgs m hc hd) (ha.trans hc.symm)
    (hb.trans hd.symm)
  have hh : Set.range (P.rep ∘ t) = Set.range (P.rep ∘ s) := by rw [hl, hm, he]
  ext z
  constructor <;> intro hz
  · obtain ⟨i, hi⟩ := hh ▸ memRep t hz
    exact ⟨i, P.inj hi⟩
  · obtain ⟨i, hi⟩ := hh.symm ▸ memRep s hz
    exact ⟨i, P.inj hi⟩

private theorem opposite_star (f : Fin 3 → Bool) :
    ∃ k, ∀ i j, f i ≠ f j → i = k ∨ j = k := by
  have aux (i j k : Fin 3) (h : f i = f j) (hc : ∀ a, a = i ∨ a = j ∨ a = k) :
      ∀ a b, f a ≠ f b → a = k ∨ b = k := by
    intro a b hab
    rcases hc a with rfl | rfl | rfl <;> rcases hc b with rfl | rfl | rfl <;> simp_all
  by_cases h : f 0 = f 1
  · exact ⟨2, aux 0 1 2 h (by intro a; fin_cases a <;> decide)⟩
  by_cases h' : f 0 = f 2
  · exact ⟨1, aux 0 2 1 h' (by intro a; fin_cases a <;> decide)⟩
  have h'' : f 1 = f 2 := by
    cases e₀ : f 0 <;> cases e₁ : f 1 <;> cases e₂ : f 2 <;> simp_all
  exact ⟨0, aux 1 2 0 h'' (by intro a; fin_cases a <;> decide)⟩

private theorem other_two (i : Fin 3) : ∃ j k, j ≠ k ∧ (∀ a, a = j ∨ a = k ↔ a ≠ i) := by
  fin_cases i
  · exact ⟨1, 2, by decide, by intro a; fin_cases a <;> decide⟩
  · exact ⟨0, 2, by decide, by intro a; fin_cases a <;> decide⟩
  · exact ⟨0, 1, by decide, by intro a; fin_cases a <;> decide⟩


section Amalgam

variable {V : Type} {val : V → ℕ × ℕ} (P : Picture val) (v : V)
variable {J : Type}

private abbrev Fibre := {p : P.X // P.lab p = v}

private def wrap (l : Line (Fibre P v) J) (p : P.X) (j : J) : P.X :=
  (l.idxFun j).elim p Subtype.val

private theorem wrap_injective (l : Line (Fibre P v) J) : Injective (wrap P v l) := by
  obtain ⟨j, hj⟩ := l.proper
  intro a b h
  simpa only [wrap, hj, Option.elim_none] using congrFun h j

private theorem wrap_letter (l : Line (Fibre P v) J) (a : Fibre P v) (j : J) :
    wrap P v l a j = (l a j).val := by
  cases h : l.idxFun j <;> simp [wrap, h]

private def Amalgam (S : Finset (Line (Fibre P v) J)) :=
  {w : J → P.X // ∃ l ∈ S, ∃ p, w = wrap P v l p}

open Classical in
private def amalgamLab {S : Finset (Line (Fibre P v) J)} (w : Amalgam P v S) : V :=
  if h : ∃ j, P.lab (w.val j) ≠ v then P.lab (w.val h.choose) else v

private theorem amalgamLab_wrap {S : Finset (Line (Fibre P v) J)}
    {l : Line (Fibre P v) J} (hl : l ∈ S) (p : P.X) :
    amalgamLab P v (⟨wrap P v l p, l, hl, p, rfl⟩ : Amalgam P v S) = P.lab p := by
  classical
  have of_outside (j : J) (hj : P.lab (wrap P v l p j) ≠ v) : wrap P v l p j = p := by
    cases h : l.idxFun j with
    | none => simp [wrap, h]
    | some a => exact (hj (by simpa only [wrap, h, Option.elim_some] using a.property)).elim
  unfold amalgamLab
  split
  · rename_i h
    exact congrArg P.lab (of_outside h.choose h.choose_spec)
  · rename_i h
    obtain ⟨j, hj⟩ := l.proper
    exact (not_ne_iff.mp (fun he ↦ h ⟨j, by simpa [wrap, hj] using he⟩)).symm

private theorem wrap_ap (l : Line (Fibre P v) J) {t : Triple P.X} (h : PointAP P.rep t) :
    PointAP (fun w : J → P.X ↦ fun ij : J × P.D ↦ P.rep (w ij.1) ij.2)
      (wrap P v l ∘ t) := by
  intro ij
  cases he : l.idxFun ij.1 <;> simp [wrap, he, h ij.2]

private theorem wrap_forward (l : Line (Fibre P v) J) {t : Triple P.X}
    (h : Forward P.rep t) :
    Forward (fun w : J → P.X ↦ fun ij : J × P.D ↦ P.rep (w ij.1) ij.2)
      (wrap P v l ∘ t) := by
  intro ij
  cases he : l.idxFun ij.1 <;> simp [wrap, he, h ij.2]

-- All nonconstant rows of a progression use a common moving line. The
-- bipartite link of v makes this a three-index argument.
set_option maxHeartbeats 1000000 in
-- The argument tracks both witnesses for each word throughout the row comparisons.
private theorem amalgam_recover {S : Finset (Line (Fibre P v) J)}
    (sparse : ∀ l ∈ S, ∀ m ∈ S, collide l m → l = m)
    (t : Triple (Amalgam P v S))
    (ht : PointAP (fun w ↦ fun ij : J × P.D ↦ P.rep (w.val ij.1) ij.2) t)
    (hne : t 0 ≠ t 1) :
    ∃ l ∈ S, ∃ u : Triple P.X, PointAP P.rep u ∧ u 0 ≠ u 1 ∧
      ∀ i, (t i).val = wrap P v l (u i) := by
  classical
  choose L hL p hp using fun i ↦ (t i).property
  let row (j : J) (i : Fin 3) := (t i).val j
  let active (j : J) (i : Fin 3) := P.lab (row j i) ≠ v
  let varies (j : J) := row j 0 ≠ row j 1
  have hrow (j : J) : PointAP P.rep (row j) := fun d ↦ ht (j, d)
  have eval (i : Fin 3) (j : J) : row j i = wrap P v (L i) (p i) j := congrFun (hp i) j
  have moving {i : Fin 3} {j : J} (h : active j i) : (L i).idxFun j = none := by
    cases e : (L i).idxFun j with
    | none => rfl
    | some a => exact (h (by rw [eval]; simpa only [wrap, e, Option.elim_some] using a.2)).elim
  have active_eq {i : Fin 3} {j : J} (h : active j i) : row j i = p i := by
    rw [eval, wrap, moving h, Option.elim_none]
  have distinct {j : J} (h : varies j) : Injective (P.lab ∘ row j) :=
    ap_labels_distinct P (hrow j) h
  have at_most_one {j : J} (hj : varies j) {a b : Fin 3}
      (ha : P.lab (row j a) = v) (hb : P.lab (row j b) = v) : a = b :=
    distinct hj (ha.trans hb.symm)
  have two_active {j : J} (hj : varies j) : ∃ a b, a ≠ b ∧ active j a ∧ active j b := by
    by_cases h : ∀ i, active j i
    · exact ⟨0, 1, by decide, h _, h _⟩
    · push Not at h
      obtain ⟨i, hi⟩ := h
      obtain ⟨a, b, hab, hlast⟩ := other_two i
      have ha : active j a := fun ha ↦
        ((hlast a).mp (Or.inl rfl)) (at_most_one hj ha (not_ne_iff.mp hi))
      have hb : active j b := fun hb ↦
        ((hlast b).mp (Or.inr rfl)) (at_most_one hj hb (not_ne_iff.mp hi))
      exact ⟨a, b, hab, ha, hb⟩
  obtain ⟨j₀, hj₀⟩ : ∃ j, varies j := by
    by_contra! h
    exact hne (Subtype.ext (funext fun j ↦ not_ne_iff.mp (h j)))
  have constant_row {j : J} (hj : ¬ varies j) : ∀ i, row j i = row j 0 := by
    have hh : row j = fun _ ↦ row j 0 :=
      ap_agree P.inj (hrow j) (fun _ ↦ rfl) (i := 0) (j := 1) (by decide) rfl
        (not_ne_iff.mp hj).symm
    exact fun i ↦ congrFun hh i
  have const_in_fibre {j : J} (hj : ¬ varies j) (i : Fin 3) : ¬ active j i := by
    intro hi
    have hall (a : Fin 3) : active j a := by
      simpa only [active, constant_row hj a, constant_row hj i] using hi
    obtain ⟨a, b, hab, ha, hb⟩ := two_active hj₀
    have hpp : p a = p b :=
      (active_eq (hall a)).symm.trans ((constant_row hj a).trans
        ((constant_row hj b).symm.trans (active_eq (hall b))))
    exact hab (distinct hj₀ (congrArg P.lab ((active_eq ha).trans
      (hpp.trans (active_eq hb).symm))))
  have common : ∃ k, ∀ j, varies j → active j k := by
    by_cases h : ∃ s, varies s ∧ ∀ i, active s i
    · obtain ⟨s, hs, hsa⟩ := h
      refine ⟨0, fun j hj ↦ ?_⟩
      obtain ⟨a, b, hab, ha, hb⟩ := two_active hj
      have eq_old {i : Fin 3} (hi : active j i) : row j i = row s i :=
        (active_eq hi).trans (active_eq (hsa i)).symm
      have hn : row j a ≠ row j b := fun he ↦ hab (distinct hj (congrArg P.lab he))
      have he := same_range_of_two P (hrow j) (hrow s) hj hs hn
        ⟨⟨a, rfl⟩, ⟨a, (eq_old ha).symm⟩⟩ ⟨⟨b, rfl⟩, ⟨b, (eq_old hb).symm⟩⟩
      have hm : row j 0 ∈ Set.range (row s) := he ▸ Set.mem_range_self 0
      obtain ⟨i, hi⟩ := hm
      simpa only [active, hi] using hsa i
    · push Not at h
      let side (i : Fin 3) := decide (Adj (val v) (val (P.lab (p i))))
      obtain ⟨k, hk⟩ := opposite_star side
      refine ⟨k, fun j hj ↦ ?_⟩
      obtain ⟨i, hi⟩ := h j hj
      obtain ⟨a, b, hab, habi⟩ := other_two i
      have ha : active j a := fun he ↦
        ((habi a).mp (.inl rfl)) (at_most_one hj he (not_ne_iff.mp hi))
      have hb : active j b := fun he ↦
        ((habi b).mp (.inr rfl)) (at_most_one hj he (not_ne_iff.mp hi))
      have hs := focus_sides P (hrow j) hj hab ((habi a).mp (.inl rfl))
        ((habi b).mp (.inr rfl)) (not_ne_iff.mp hi)
      have hne' : side a ≠ side b := by
        rw [active_eq ha, active_eq hb] at hs
        intro he
        by_cases hp' : Adj (val v) (val (P.lab (p a)))
        · have hb' := hs.mp hp'
          simp [side, hp', hb'] at he
        · have hb' : Adj (val v) (val (P.lab (p b))) := by
            by_contra hnb
            exact hp' (hs.mpr hnb)
          simp [side, hp', hb'] at he
      rcases hk a b hne' with rfl | rfl
      · exact ha
      · exact hb
  obtain ⟨k, hk⟩ := common
  -- If the i-th line switched between moving and fixed on nonconstant rows,
  -- it would meet the k-th line while sharing a moving coordinate with it.
  have inactive_agree {i : Fin 3} {j s : J} (hj : varies j) (hs : varies s)
      (hi : ¬ active j i) (hi' : ¬ active s i) : row j = row s := by
    obtain ⟨a, b, hab, habi⟩ := other_two i
    have eq_old {a : Fin 3} (ha : a ≠ i) : row j a = row s a :=
      (active_eq (fun hd ↦ ha (at_most_one hj hd (not_ne_iff.mp hi)))).trans
        (active_eq (fun hd ↦ ha (at_most_one hs hd (not_ne_iff.mp hi')))).symm
    exact ap_agree P.inj (hrow j) (hrow s) hab
      (eq_old ((habi a).mp (Or.inl rfl))) (eq_old ((habi b).mp (Or.inr rfl)))
  have fixed_value {i : Fin 3} {j : J} (hi : P.lab (p i) ≠ v)
      (hj : ¬ active j i) : ∃ a, (L i).idxFun j = some a ∧ a.val = row j i := by
    cases h : (L i).idxFun j with
    | none => exact (hj (by simpa [active, eval, wrap, h] using hi)).elim
    | some a => exact ⟨a, rfl, (by simp [eval, wrap, h])⟩
  have no_switch {i : Fin 3} {s j : J} (hs : varies s) (ha : active s i)
      (hj : varies j) : active j i := by
    intro heq
    have hi : ¬ active j i := fun h ↦ h heq
    have hpi : P.lab (p i) ≠ v := active_eq ha ▸ ha
    have hpk : P.lab (p k) ≠ v := active_eq (hk s hs) ▸ (hk s hs)
    let a : Fibre P v := ⟨row j i, heq⟩
    have hit : L i a = L k a := by
      funext q
      by_cases hv : varies q
      · rw [(L k).apply_none a q (moving (hk q hv))]
        by_cases hqi : active q i
        · exact (L i).apply_none a q (moving hqi)
        · obtain ⟨b, hb, hb'⟩ := fixed_value hpi hqi
          rw [Line.apply_some hb]
          exact Subtype.ext (hb'.trans (congrFun (inactive_agree hv hj hqi hi) i))
      · obtain ⟨b, hb, hb'⟩ := fixed_value hpi (const_in_fibre hv i)
        obtain ⟨c, hc, hc'⟩ := fixed_value hpk (const_in_fibre hv k)
        rw [Line.apply_some hb, Line.apply_some hc]
        exact Subtype.ext (hb'.trans ((constant_row hv i).trans
          ((constant_row hv k).symm.trans hc'.symm)))
    have he := sparse (L i) (hL i) (L k) (hL k)
      ⟨⟨a, a, hit⟩, s, moving ha, moving (hk s hs)⟩
    obtain ⟨b, hb, _⟩ := fixed_value hpi hi
    rw [he, moving (hk j hj)] at hb
    contradiction
  have rows_same {j : J} (hj : varies j) : row j = row j₀ := by
    obtain ⟨a, b, hab, ha, hb⟩ := two_active hj₀
    exact ap_agree P.inj (hrow j) (hrow j₀) hab
      ((active_eq (no_switch hj₀ ha hj)).trans (active_eq ha).symm)
      ((active_eq (no_switch hj₀ hb hj)).trans (active_eq hb).symm)
  refine ⟨L k, hL k, row j₀, hrow j₀, hj₀, fun i ↦ funext fun j ↦ ?_⟩
  change row j i = wrap P v (L k) (row j₀ i) j
  by_cases hj : varies j
  · rw [wrap, moving (hk j hj), Option.elim_none]
    exact congrFun (rows_same hj) i
  · have hpk : P.lab (p k) ≠ v := active_eq (hk j₀ hj₀) ▸ (hk j₀ hj₀)
    obtain ⟨a, ha, ha'⟩ := fixed_value hpk (const_in_fibre hj k)
    rw [wrap, ha, Option.elim_some, ha']
    rw [constant_row hj i, constant_row hj k]

end Amalgam


private def shiftedPicture {V : Type} {val : V → ℕ × ℕ} (P : Picture val) (v : V)
    {J : Type} [Finite J] (S : Finset (Line (Fibre P v) J))
    (sparse : ∀ l ∈ S, ∀ m ∈ S, collide l m → l = m) : Picture val where
  X := Amalgam P v S
  finiteX := by
    let _ := P.finiteX
    unfold Amalgam
    infer_instance
  D := J × P.D
  finiteD := by
    let _ := P.finiteD
    infer_instance
  rep w ij := P.rep (w.val ij.1) ij.2
  inj := by
    intro x y he
    exact Subtype.ext (funext fun j ↦ P.inj (funext fun d ↦ congrFun he (j, d)))
  lab := amalgamLab P v
  recover t ht hne := by
    obtain ⟨l, hl, u, hu, hune, hcopy⟩ := amalgam_recover P v sparse t ht hne
    have hlabel (i : Fin 3) : amalgamLab P v (t i) = P.lab (u i) := by
      have eq : t i = ⟨wrap P v l (u i), l, hl, u i, rfl⟩ := Subtype.ext (hcopy i)
      exact (congrArg (amalgamLab P v) eq).trans (amalgamLab_wrap P v hl _)
    rcases P.recover u hu hune with ⟨hf, hs⟩ | ⟨hf, hs⟩
    · left
      refine ⟨?_, ?_⟩
      · intro j
        simpa only [hcopy, Function.comp_apply] using wrap_forward P v l hf j
      · simpa only [Ordered, Function.comp_apply, hlabel] using hs
    · right
      refine ⟨?_, ?_⟩
      · intro j
        simpa only [hcopy, Function.comp_apply] using wrap_forward P v l hf j
      · simpa only [Ordered, Function.comp_apply, hlabel] using hs

private structure PictureMap {V : Type} {val : V → ℕ × ℕ} (P Q : Picture val) where
  toFun : P.X → Q.X
  inj : Injective toFun
  label (x : P.X) : Q.lab (toFun x) = P.lab x
  ap (t : Triple P.X) : PointAP P.rep t → PointAP Q.rep (toFun ∘ t)

private def PictureMap.id {V : Type} {val : V → ℕ × ℕ} (P : Picture val) : PictureMap P P :=
  ⟨fun x ↦ x, injective_id, fun _ ↦ rfl, fun _ h ↦ h⟩

private def PictureMap.comp {V : Type} {val : V → ℕ × ℕ} {P Q R : Picture val}
    (g : PictureMap Q R) (f : PictureMap P Q) : PictureMap P R :=
  ⟨g.toFun ∘ f.toFun, g.inj.comp f.inj, fun x ↦ (g.label _).trans (f.label x),
    fun t h ↦ g.ap _ (f.ap t h)⟩

private theorem focus {V : Type} {val : V → ℕ × ℕ} (P : Picture val) (v : V) (r : ℕ) :
    ∃ Q : Picture val, ∀ c : Q.X → Fin (r + 1),
      ∃ (f : PictureMap P Q) (k : Fin (r + 1)), ∀ x, P.lab x = v → c (f.toFun x) = k := by
  classical
  let _ := P.finiteX
  by_cases h : Nonempty (Fibre P v)
  · obtain ⟨J, _, S, hS, hmono⟩ := sparseHJ (Fibre P v) (r + 1)
    let Q := shiftedPicture P v S hS
    refine ⟨Q, fun c ↦ ?_⟩
    let C (w : J → Fibre P v) : Fin (r + 1) :=
      if hw : ∃ l ∈ S, ∃ x, (fun j ↦ (w j).val) = wrap P v l x then
        c ⟨fun j ↦ (w j).val, hw⟩ else 0
    obtain ⟨l, hl, k, hk⟩ := hmono C
    let f : PictureMap P Q :=
      ⟨fun x ↦ ⟨wrap P v l x, l, hl, x, rfl⟩,
        fun _ _ he ↦ wrap_injective P v l (congrArg Subtype.val he),
        amalgamLab_wrap P v hl, fun _ ht ↦ wrap_ap P v l ht⟩
    refine ⟨f, k, fun x hx ↦ ?_⟩
    have hw : (fun j ↦ (l (⟨x, hx⟩ : Fibre P v) j).val) = wrap P v l x :=
      funext fun j ↦ (wrap_letter P v l ⟨x, hx⟩ j).symm
    have hh : ∃ m ∈ S, ∃ p, (fun j ↦ (l (⟨x, hx⟩ : Fibre P v) j).val) = wrap P v m p :=
      ⟨l, hl, x, hw⟩
    have eq : (⟨fun j ↦ (l (⟨x, hx⟩ : Fibre P v) j).val, hh⟩ : Q.X) = f.toFun x :=
      Subtype.ext hw
    simpa only [C, dite_eq_left hh, eq] using hk ⟨x, hx⟩
  · exact ⟨P, fun _ ↦ ⟨PictureMap.id P, 0, fun x hx ↦ (h ⟨⟨x, hx⟩⟩).elim⟩⟩

private theorem focus_all {V : Type} {val : V → ℕ × ℕ} (P : Picture val) (r : ℕ)
    (s : Finset V) : ∃ Q : Picture val, ∀ c : Q.X → Fin (r + 1),
      ∃ (f : PictureMap P Q) (k : V → Fin (r + 1)),
        ∀ x, P.lab x ∈ s → c (f.toFun x) = k (P.lab x) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨P, fun _ ↦ ⟨PictureMap.id P, fun _ ↦ 0, by simp⟩⟩
  | @insert v s hv ih =>
    obtain ⟨Q, hQ⟩ := ih
    obtain ⟨R, hR⟩ := focus Q v r
    refine ⟨R, fun c ↦ ?_⟩
    obtain ⟨g, a, ha⟩ := hR c
    obtain ⟨f, k, hk⟩ := hQ (c ∘ g.toFun)
    refine ⟨g.comp f, Function.update k v a, fun x hx ↦ ?_⟩
    rcases mem_insert.mp hx with h | h
    · rw [h, Function.update_self]
      exact ha _ ((f.label x).trans h)
    · have hne : P.lab x ≠ v := fun he ↦ hv (he ▸ h)
      rw [Function.update_of_ne hne]
      exact hk x h

private abbrev Edges {V : Type} (val : V → ℕ × ℕ) := {t : Triple V // Ordered val t}

open Classical in
private def initialRep {V : Type} {val : V → ℕ × ℕ}
    (x : Edges val × Fin 3) (j : Bool × Edges val) : Fin 3 :=
  if x.1 = j.2 then if j.1 then 1 else x.2 else 0

private def initialPicture {V : Type} [Finite V] (val : V → ℕ × ℕ) : Picture val where
  X := Edges val × Fin 3
  finiteX := inferInstance
  D := Bool × Edges val
  finiteD := inferInstance
  rep := initialRep
  inj := by
    classical
    rintro ⟨e, i⟩ ⟨f, j⟩ h
    have e₁ := congrFun h (true, e)
    have he : e = f := by
      by_contra hn
      have hn' : f ≠ e := fun h' ↦ hn h'.symm
      simp [initialRep, hn'] at e₁
    subst f
    have e₂ := congrFun h (false, e)
    simpa [initialRep] using e₂
  lab x := x.1.val x.2
  recover t h hne := by
    classical
    have ht₁ : (t 0).1 = (t 1).1 := by
      have ht := h (true, (t 0).1)
      by_contra hh
      have hh' : (t 1).1 ≠ (t 0).1 := fun e ↦ hh e.symm
      by_cases hc : (t 2).1 = (t 0).1 <;>
        simp [initialRep, hh', hc] at ht
    have ht₂ : (t 2).1 = (t 0).1 := by
      have ht := h (true, (t 0).1)
      by_contra hh
      simp [initialRep, ht₁.symm, hh] at ht
    have hpos := h (false, (t 0).1)
    simp only [initialRep, ht₁.symm, ht₂, ↓reduceIte, Bool.false_eq_true] at hpos
    have hne' : (t 0).2 ≠ (t 1).2 := fun he ↦ hne (Prod.ext ht₁ he)
    have hneval : (t 0).2.val ≠ (t 1).2.val := fun he ↦ hne' (Fin.ext he)
    have shape : ((t 0).2 = 0 ∧ (t 1).2 = 1 ∧ (t 2).2 = 2) ∨
        ((t 0).2 = 2 ∧ (t 1).2 = 1 ∧ (t 2).2 = 0) := by
      by_cases hlt : (t 0).2 < (t 1).2
      · exact Or.inl ⟨Fin.ext (show (t 0).2.val = 0 by omega),
          Fin.ext (show (t 1).2.val = 1 by omega), Fin.ext (show (t 2).2.val = 2 by omega)⟩
      · exact Or.inr ⟨Fin.ext (show (t 0).2.val = 2 by omega),
          Fin.ext (show (t 1).2.val = 1 by omega), Fin.ext (show (t 2).2.val = 0 by omega)⟩
    rcases shape with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
    · left
      refine ⟨?_, ?_⟩
      · rintro ⟨b, e⟩
        cases b <;> by_cases he : (t 0).1 = e <;>
          simp [initialRep, ht₁.symm, he, h₀, h₁]
      · simpa only [Ordered, Function.comp_apply, ht₁.symm, ht₂, h₀, h₁, h₂] using
          (t 0).1.property
    · right
      refine ⟨?_, ?_⟩
      · rintro ⟨b, e⟩
        cases b <;> by_cases he : (t 0).1 = e <;>
          simp [initialRep, Function.comp_apply, rev_zero, rev_one, ht₁.symm, ht₂, he, h₂, h₁]
      · simpa only [Ordered, Function.comp_apply, rev_zero, rev_one, rev_two,
          ht₁.symm, ht₂, h₀, h₁, h₂] using (t 0).1.property

private theorem initialAP {V : Type} [Finite V] {val : V → ℕ × ℕ} (e : Edges val) :
    PointAP (initialPicture val).rep (fun i ↦ (e, i)) := by
  classical
  rintro ⟨b, f⟩
  change (initialRep (e, 0) (b, f)).val + (initialRep (e, 2) (b, f)).val =
    (initialRep (e, 1) (b, f)).val + (initialRep (e, 1) (b, f)).val
  cases b <;> by_cases he : e = f <;> simp [initialRep, he]

private theorem has_picture (r : ℕ) : ∃ (V : Type) (val : V → ℕ × ℕ) (P : Picture val),
    (∀ v, (val v).1 < (val v).2) ∧ ∀ c : P.X → Fin (r + 1),
      ∃ t : Triple P.X, PointAP P.rep t ∧ t 0 ≠ t 1 ∧ c (t 0) = c (t 1) ∧ c (t 1) = c (t 2) := by
  classical
  obtain ⟨N, hN⟩ := shift_ramsey (r + 1)
  let V := {x : Fin N × Fin N // x.1 < x.2}
  let val (v : V) : ℕ × ℕ := (v.val.1.val, v.val.2.val)
  let P := initialPicture val
  obtain ⟨Q, hQ⟩ := focus_all P r (univ : Finset V)
  refine ⟨V, val, Q, fun v ↦ v.property, fun c ↦ ?_⟩
  obtain ⟨f, k, hk⟩ := hQ c
  let C (x : Fin N × Fin N) : Fin (r + 1) := if hx : x.1 < x.2 then k ⟨x, hx⟩ else 0
  obtain ⟨a, b, d, h, hab, hbd⟩ := hN C
  let e : Edges val := ⟨![⟨a, h.1⟩, ⟨b, h.2.2.1⟩, ⟨d, h.2.2.2.2⟩], h⟩
  let u : Triple P.X := fun i ↦ (e, i)
  have ha' : a.1 < a.2 := h.1
  have hb' : b.1 < b.2 := h.2.2.1
  have hd' : d.1 < d.2 := h.2.2.2.2
  refine ⟨f.toFun ∘ u, f.ap u (initialAP e), ?_, ?_, ?_⟩
  · intro he
    exact (by decide : (0 : Fin 3) ≠ 1) (congrArg Prod.snd (f.inj he))
  · change c (f.toFun (u 0)) = c (f.toFun (u 1))
    rw [hk _ (mem_univ _), hk _ (mem_univ _)]
    change k ⟨a, ha'⟩ = k ⟨b, hb'⟩
    simpa only [C, dite_eq_left ha', dite_eq_left hb'] using hab
  · change c (f.toFun (u 1)) = c (f.toFun (u 2))
    rw [hk _ (mem_univ _), hk _ (mem_univ _)]
    change k ⟨b, hb'⟩ = k ⟨d, hd'⟩
    simpa only [C, dite_eq_left hb', dite_eq_left hd'] using hbd

/-! ### Finite blocks in the natural numbers -/

private def encode : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f 0 + 5 * encode n (fun i ↦ f i.succ)

private theorem encode_add (n : ℕ) (f g : Fin n → ℕ) :
    encode n (fun i ↦ f i + g i) = encode n f + encode n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [encode, ih]; omega

private theorem encode_inj (n : ℕ) {f g : Fin n → ℕ}
    (hf : ∀ i, f i < 5) (hg : ∀ i, g i < 5) (h : encode n f = encode n g) : f = g := by
  induction n with
  | zero => exact funext fun i ↦ i.elim0
  | succ n ih =>
    change f 0 + 5 * encode n (fun i ↦ f i.succ) =
      g 0 + 5 * encode n (fun i ↦ g i.succ) at h
    have e₀ : f 0 = g 0 := by
      have hm := congrArg (· % 5) h
      simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf 0), Nat.mod_eq_of_lt (hg 0)]
        using hm
    have e₁ : encode n (fun i ↦ f i.succ) = encode n (fun i ↦ g i.succ) := by omega
    have he := ih (fun i ↦ hf i.succ) (fun i ↦ hg i.succ) e₁
    exact funext (Fin.cases e₀ (congrFun he))

private structure Block (r : ℕ) where
  X : Type
  finiteX : Finite X
  place : X → ℕ
  inj : Injective place
  lab : X → ℕ × ℕ
  ascending (x : X) : (lab x).1 < (lab x).2
  reflect {a b c : X} : place a + place c = place b + place b → a ≠ b →
    Shift (lab a) (lab b) (lab c) ∨ Shift (lab c) (lab b) (lab a)
  ramsey (C : X → Fin (r + 1)) : ∃ a b c : X,
    place a + place c = place b + place b ∧ a ≠ b ∧ C a = C b ∧ C b = C c

private theorem has_block (r : ℕ) : Nonempty (Block r) := by
  classical
  obtain ⟨V, val, P, has_lt, hP⟩ := has_picture r
  let _ := P.finiteD
  let _ := Fintype.ofFinite P.D
  let n := Fintype.card P.D
  let e : P.D ≃ Fin n := Fintype.equivFin _
  let digits (x : P.X) (i : Fin n) := (P.rep x (e.symm i)).val
  let place (x : P.X) := encode n (digits x)
  have refl {t : Triple P.X} (h : place (t 0) + place (t 2) = place (t 1) + place (t 1)) :
      PointAP P.rep t := by
    have hd (x : P.X) (i : Fin n) : digits x i < 3 := (P.rep x (e.symm i)).isLt
    have he := encode_inj n (f := fun i ↦ digits (t 0) i + digits (t 2) i)
      (g := fun i ↦ digits (t 1) i + digits (t 1) i)
      (fun i ↦ by have := hd (t 0) i; have := hd (t 2) i; omega)
      (fun i ↦ by have := hd (t 1) i; omega) (by rw [encode_add, encode_add]; exact h)
    intro j
    simpa only [digits, Equiv.symm_apply_apply] using congrFun he (e j)
  refine ⟨⟨P.X, P.finiteX, place, ?_, val ∘ P.lab, fun x ↦ has_lt _, ?_, ?_⟩⟩
  · intro x y h
    have hd := encode_inj n (f := digits x) (g := digits y)
      (fun i ↦ lt_trans (P.rep x (e.symm i)).isLt (by decide))
      (fun i ↦ lt_trans (P.rep y (e.symm i)).isLt (by decide)) h
    apply P.inj
    funext j
    apply Fin.ext
    simpa only [digits, Equiv.symm_apply_apply] using congrFun hd (e j)
  · intro a b c h hne
    rcases P.recover ![a, b, c] (refl h) hne with ⟨_, hs⟩ | ⟨_, hs⟩
    · exact Or.inl hs
    · exact Or.inr hs
  · intro C
    obtain ⟨t, ht, hne, h₁, h₂⟩ := hP C
    refine ⟨t 0, t 1, t 2, ?_, hne, h₁, h₂⟩
    change encode n (digits (t 0)) + encode n (digits (t 2)) =
      encode n (digits (t 1)) + encode n (digits (t 1))
    rw [← encode_add, ← encode_add]
    exact congrArg (encode n) (funext fun i ↦ ht (e.symm i))


/-! ### The infinite counterexample -/

private def blocks (r : ℕ) : Block r := Classical.choice (has_block r)

private def width (r : ℕ) : ℕ := by
  let _ := (blocks r).finiteX
  let _ := Fintype.ofFinite (blocks r).X
  exact univ.sup (blocks r).place

private theorem place_le_width (r : ℕ) (x : (blocks r).X) : (blocks r).place x ≤ width r := by
  let _ := (blocks r).finiteX
  let _ := Fintype.ofFinite (blocks r).X
  unfold width
  exact Finset.le_sup (f := (blocks r).place) (mem_univ x)

-- `cap r` bounds every earlier block; the gap below block r exceeds
-- both its width and the maximum size of an earlier point.
private def cap : ℕ → ℕ
  | 0 => 0
  | r + 1 => 3 * (cap r + width r + 1)

private theorem cap_mono : Monotone cap := by
  apply monotone_nat_of_le_succ
  intro r
  simp only [cap]
  omega

private def offset (r : ℕ) := 2 * cap r + 2 * width r + 1

private abbrev AllPoints := Σ r : ℕ, (blocks r).X

private def location (w : AllPoints) : ℕ := offset w.1 + (blocks w.1).place w.2

private theorem location_bounds (w : AllPoints) :
    offset w.1 ≤ location w ∧ location w ≤ offset w.1 + width w.1 ∧
      location w ≤ cap (w.1 + 1) := by
  have hp := place_le_width w.1 w.2
  simp only [location, offset, cap]
  omega

private theorem earlier_le {x y : AllPoints} (h : x.1 < y.1) : location x ≤ cap y.1 :=
  (location_bounds x).2.2.trans (cap_mono (by omega))

private theorem location_lt {x y : AllPoints} (h : x.1 < y.1) : location x < location y := by
  have hx := earlier_le h
  have hy := (location_bounds y).1
  unfold offset at hy
  omega

private theorem location_inj : Injective location := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact ((location_lt (x := ⟨i, x⟩) (y := ⟨j, y⟩) hij).ne h).elim
  · have eq : (blocks i).place x = (blocks i).place y := Nat.add_left_cancel h
    rw [(blocks i).inj eq]
  · exact ((location_lt (x := ⟨j, y⟩) (y := ⟨i, x⟩) hji).ne h.symm).elim

private theorem same_block_ordered {a b c : AllPoints} (h : location a + location c =
    location b + location b) (hab : location a < location b) : a.1 = b.1 ∧ b.1 = c.1 := by
  have hbc : location b < location c := by omega
  have hle₁ : a.1 ≤ b.1 := by
    by_contra! h'
    exact (location_lt (x := b) (y := a) h').not_gt hab
  have hle₂ : b.1 ≤ c.1 := by
    by_contra! h'
    exact (location_lt (x := c) (y := b) h').not_gt hbc
  have he : b.1 = c.1 := by
    by_contra hne
    have hb := earlier_le (x := b) (y := c) (lt_of_le_of_ne hle₂ hne)
    have hc := (location_bounds c).1
    unfold offset at hc
    omega
  refine ⟨?_, he⟩
  by_contra hne
  have ha := earlier_le (x := a) (y := b) (lt_of_le_of_ne hle₁ hne)
  have hb := (location_bounds b).1
  have hc := (location_bounds c).2.1
  rw [← he] at hc
  unfold offset at hb hc
  omega

private def counterexample : Set ℕ := Set.range location

private def pointLab (p : ℕ) : ℕ × ℕ := by
  classical
  exact if h : p ∈ counterexample then (blocks h.choose.1).lab h.choose.2 else (0, 1)

private theorem pointLab_location (w : AllPoints) :
    pointLab (location w) = (blocks w.1).lab w.2 := by
  have hm : location w ∈ counterexample := ⟨w, rfl⟩
  rw [pointLab, dite_eq_left hm, location_inj hm.choose_spec]

private theorem counterexample_shift {a b c : ℕ} (ha : a ∈ counterexample)
    (hb : b ∈ counterexample) (hc : c ∈ counterexample) (h : a + c = b + b) (hne : a ≠ b) :
    Shift (pointLab a) (pointLab b) (pointLab c) ∨
      Shift (pointLab c) (pointLab b) (pointLab a) := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨c, rfl⟩ := hc
  have hi : a.1 = b.1 ∧ b.1 = c.1 := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact same_block_ordered h hlt
    · have hc' : location c < location b := by omega
      obtain ⟨e₁, e₂⟩ := same_block_ordered ((Nat.add_comm ..).trans h) hc'
      exact ⟨e₂.symm, e₁.symm⟩
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  obtain ⟨k, c⟩ := c
  change i = j ∧ j = k at hi
  obtain ⟨rfl, rfl⟩ := hi
  simp only [pointLab_location]
  apply (blocks i).reflect
  · unfold location at h
    simp only at h
    omega
  · intro he
    exact hne (by rw [he])

private theorem counterexample_ramsey (r : ℕ) (C : ℕ → Fin (r + 1)) :
    ∃ a ∈ counterexample, ∃ b ∈ counterexample, ∃ c ∈ counterexample,
      a + c = b + b ∧ a ≠ b ∧ C a = C b ∧ C b = C c := by
  obtain ⟨a, b, c, h, hne, e₁, e₂⟩ := (blocks r).ramsey (fun x ↦ C (location ⟨r, x⟩))
  refine ⟨location ⟨r, a⟩, ⟨⟨r, a⟩, rfl⟩, location ⟨r, b⟩, ⟨⟨r, b⟩, rfl⟩,
    location ⟨r, c⟩, ⟨⟨r, c⟩, rfl⟩, ?_, ?_, e₁, e₂⟩
  · change (offset r + (blocks r).place a) + (offset r + (blocks r).place c) =
      (offset r + (blocks r).place b) + (offset r + (blocks r).place b)
    omega
  · intro he
    apply hne
    have eq : (blocks r).place a = (blocks r).place b := Nat.add_left_cancel he
    exact (blocks r).inj eq

-- Prescribing two distinct bits retains at least a quarter of all assignments.
open Classical in
private theorem bit_count {I : Type} [Fintype I] [DecidableEq I] (a b : I) (hne : a ≠ b) :
    ∃ S : Finset (I → Bool), (∀ s, s ∈ S ↔ s a = true ∧ s b = false) ∧
      Fintype.card (I → Bool) ≤ 4 * S.card := by
  classical
  let S := (univ : Finset (I → Bool)).filter fun s ↦ s a = true ∧ s b = false
  have hS (s : I → Bool) : s ∈ S ↔ s a = true ∧ s b = false := by simp [S]
  let f (s : I → Bool) : S × Bool × Bool :=
    (⟨update (update s a true) b false, (hS _).mpr
      ⟨by simp [update_of_ne hne], by simp⟩⟩, s a, s b)
  have hf : Injective f := by
    intro x y he
    have e₁ : x a = y a := congrArg (fun z : S × Bool × Bool ↦ z.2.1) he
    have e₂ : x b = y b := congrArg (fun z : S × Bool × Bool ↦ z.2.2) he
    have e₃ := congrArg (fun z : S × Bool × Bool ↦ z.1.val) he
    funext i
    by_cases hia : i = a
    · simpa only [hia] using e₁
    by_cases hib : i = b
    · simpa only [hib] using e₂
    simpa only [f, update_of_ne hib, update_of_ne hia] using congrFun e₃ i
  refine ⟨S, hS, ?_⟩
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bool, Fintype.card_coe] at hcard
  omega

private theorem choose_bits (B : Finset ℕ) (f g : ℕ → ℕ) (h : ∀ x ∈ B, f x ≠ g x) :
    ∃ s : ℕ → Bool, B.card ≤ 4 * (B.filter fun x ↦ s (f x) = true ∧ s (g x) = false).card := by
  classical
  let N := B.sup (fun x ↦ max (f x) (g x)) + 1
  let extend (s : Fin N → Bool) (k : ℕ) : Bool := if hk : k < N then s ⟨k, hk⟩ else false
  let accept (s : Fin N → Bool) (x : ℕ) := extend s (f x) = true ∧ extend s (g x) = false
  let take (s : Fin N → Bool) := B.filter (accept s)
  let ways (x : ℕ) := (univ : Finset (Fin N → Bool)).filter fun s ↦ accept s x
  let M := Fintype.card (Fin N → Bool)
  have count (x : ℕ) (hx : x ∈ B) : M ≤ 4 * (ways x).card := by
    have hh := Finset.le_sup (f := fun x ↦ max (f x) (g x)) hx
    have h₁ : f x < N := by dsimp [N]; exact Nat.lt_succ_of_le ((le_max_left ..).trans hh)
    have h₂ : g x < N := by dsimp [N]; exact Nat.lt_succ_of_le ((le_max_right ..).trans hh)
    obtain ⟨S, hS, hcard⟩ := bit_count (⟨f x, h₁⟩ : Fin N) ⟨g x, h₂⟩
      (fun he ↦ h x hx (congrArg Fin.val he))
    have he : ways x = S := by
      ext s
      simp only [ways, mem_filter, mem_univ, true_and, hS, accept, extend,
        dite_eq_left h₁, dite_eq_left h₂]
    exact he.symm ▸ hcard
  have swap : (∑ x ∈ B, (ways x).card) = ∑ s : Fin N → Bool, (take s).card := by
    calc
      _ = ∑ x ∈ B, ∑ s : Fin N → Bool, if accept s x then 1 else 0 :=
        sum_congr rfl fun x _ ↦ (sum_boole _ _).symm
      _ = ∑ s : Fin N → Bool, ∑ x ∈ B, if accept s x then 1 else 0 := sum_comm
      _ = _ := sum_congr rfl fun s _ ↦ sum_boole _ _
  have hsum : B.card * M ≤ 4 * ∑ s : Fin N → Bool, (take s).card := by
    rw [← swap, mul_sum]
    exact Finset.card_nsmul_le_sum B _ M count
  have hex : ∃ s, B.card ≤ 4 * (take s).card := by
    by_contra! hh
    have hn : (univ : Finset (Fin N → Bool)).Nonempty := ⟨fun _ ↦ false, mem_univ _⟩
    have ht : (∑ s : Fin N → Bool, 4 * (take s).card) < ∑ _s : Fin N → Bool, B.card :=
      Finset.sum_lt_sum_of_nonempty hn fun s _ ↦ hh s
    simp only [← mul_sum, sum_const, card_univ, nsmul_eq_mul] at ht
    exact (not_lt_of_ge ((Nat.mul_comm M B.card).le.trans hsum)) ht
  obtain ⟨s, hs⟩ := hex
  exact ⟨extend s, hs⟩

@[expose] public section

/-- **Sets with uniformly large 3AP-free subsets.** A set $A$ of natural numbers has this property
if there is a real number $\varepsilon > 0$ such that every finite subset $B \subseteq A$ contains
a subset $C \subseteq B$ with $|C| \ge \varepsilon |B|$ that contains no nontrivial three-term
arithmetic progression, that is, no $a, b, c \in C$ with $a + c = 2b$ and $a \ne b$. -/
def HasFew3APs (A : Set ℕ) := ∃ (ε : ℝ), ε > 0 ∧
  ∀ (B : Set ℕ), B ⊆ A → Finite B →
  ∃ (C : Set ℕ), C ⊆ B ∧ C.ncard ≥ ε * B.ncard ∧ ThreeAPFree C

/-- **Erdős Problem 847.** Call a set of natural numbers 3AP-free if it contains no $a, b, c$ with
$a + c = 2b$ and $a \ne b$. The proposition asserts that every infinite set $A$ of natural numbers
such that, for some real number $\varepsilon > 0$, every finite subset $B \subseteq A$ has a
3AP-free subset of size at least $\varepsilon |B|$, is a finite union of 3AP-free sets: there are
a natural number $n$ and 3AP-free sets $S_0, \dots, S_{n-1}$ of natural numbers with
$A = S_0 \cup \dots \cup S_{n-1}$. -/
def conjecture : Prop :=
  ∀ (A : Set ℕ), Infinite A → HasFew3APs A →
    ∃ n, ∃ (S : Fin n → Set ℕ), (∀ i, ThreeAPFree (S i)) ∧ A = ⋃ i : Fin n, S i

end

private theorem counterexample_few : HasFew3APs counterexample := by
  classical
  refine ⟨1 / 4, by norm_num, fun B hB hfin ↦ ?_⟩
  have hBf : B.Finite := Set.finite_coe_iff.mp hfin
  let T := hBf.toFinset
  let f (x : ℕ) := (pointLab x).1
  let g (x : ℕ) := (pointLab x).2
  obtain ⟨s, hs⟩ := choose_bits T f g (by
    intro x hx
    have hx' : x ∈ counterexample := hB (hBf.mem_toFinset.mp hx)
    obtain ⟨w, rfl⟩ := hx'
    change (pointLab (location w)).1 ≠ (pointLab (location w)).2
    rw [pointLab_location]
    exact ((blocks w.1).ascending w.2).ne)
  let C := T.filter fun x ↦ s (f x) = true ∧ s (g x) = false
  have hmem (x : ℕ) : x ∈ C ↔ x ∈ B ∧ s (f x) = true ∧ s (g x) = false := by
    simp [C, T]
  refine ⟨(C : Set ℕ), fun x hx ↦ ((hmem x).mp hx).1, ?_, ?_⟩
  · rw [Set.ncard_coe_finset, Set.ncard_eq_toFinset_card B hBf]
    have hh : (T.card : ℝ) ≤ 4 * (C.card : ℝ) := by exact_mod_cast hs
    change (1 / 4 : ℝ) * (T.card : ℝ) ≤ (C.card : ℝ)
    linarith
  · intro a ha b hb c hc h
    by_contra hne
    obtain ⟨ha', ha₁, ha₂⟩ := (hmem a).mp ha
    obtain ⟨hb', hb₁, _⟩ := (hmem b).mp hb
    obtain ⟨hc', _, hc₂⟩ := (hmem c).mp hc
    rcases counterexample_shift (hB ha') (hB hb') (hB hc') h hne with h | h
    · have he : g a = f b := h.2.1
      rw [he, hb₁] at ha₂
      contradiction
    · have he : g c = f b := h.2.1
      rw [he, hb₁] at hc₂
      contradiction

private theorem counterexample_infinite : Infinite counterexample := by
  classical
  refine not_finite_iff_infinite.mp fun h ↦ ?_
  let _ := h
  let _ := Fintype.ofFinite counterexample
  let n := Fintype.card counterexample
  let e := Fintype.equivFin counterexample
  let col (x : ℕ) : Fin (n + 1) := if hx : x ∈ counterexample then (e ⟨x, hx⟩).succ else 0
  obtain ⟨a, ha, b, hb, c, hc, hap, hne, eq, _⟩ := counterexample_ramsey n col
  simp only [col, dite_eq_left ha, dite_eq_left hb, Fin.succ_inj] at eq
  exact hne (congrArg Subtype.val (e.injective eq))

/--
**Erdős Problem 847 is false.** Call a set of natural numbers 3AP-free if it contains no
$a, b, c$ with $a + c = 2b$ and $a \ne b$. There is an infinite set $A$ of natural numbers such
that, for some real number $\varepsilon > 0$, every finite subset $B \subseteq A$ has a 3AP-free
subset of size at least $\varepsilon |B|$, but $A$ is not the union of finitely many 3AP-free sets
of natural numbers.

Source: Christian Reiher, Vojtěch Rödl, and Marcelo
Sales, Colouring versus density in integers and Hales–Jewett cubes, Journal of the London
Mathematical Society (2024), e12987, https://doi.org/10.1112/jlms.12987. Moved from
`OpenConjectures/NumberTheory/ErdosProblem847`.
-/
public theorem conjecture_refuted : ¬ conjecture := by
  classical
  intro h
  obtain ⟨n, S, hfree, hS⟩ := h counterexample counterexample_infinite counterexample_few
  have fromCover (x : ℕ) (hx : x ∈ counterexample) : ∃ i : Fin n, x ∈ S i :=
    Set.mem_iUnion.mp (hS ▸ hx)
  let col (x : ℕ) : Fin (n + 1) :=
    if hx : x ∈ counterexample then (fromCover x hx).choose.succ else 0
  obtain ⟨a, ha, b, hb, c, hc, hap, hne, hab, hbc⟩ := counterexample_ramsey n col
  simp only [col, dite_eq_left ha, dite_eq_left hb, Fin.succ_inj] at hab
  simp only [col, dite_eq_left hb, dite_eq_left hc, Fin.succ_inj] at hbc
  let i := (fromCover b hb).choose
  have h₁ : a ∈ S i := by
    change a ∈ S (fromCover b hb).choose
    rw [← hab]
    exact (fromCover a ha).choose_spec
  have h₂ : b ∈ S i := (fromCover b hb).choose_spec
  have h₃ : c ∈ S i := by
    change c ∈ S (fromCover b hb).choose
    rw [hbc]
    exact (fromCover c hc).choose_spec
  exact hne (hfree i h₁ h₂ h₃ hap)

end
end MathlibExt.NumberTheory.ErdosProblem847Wanted
