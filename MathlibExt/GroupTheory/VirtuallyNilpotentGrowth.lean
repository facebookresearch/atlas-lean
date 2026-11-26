/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Nilpotent
public import MathlibExt.GroupTheory.GroupGrowth
import Mathlib.Tactic.Group
import MathlibExt.GroupTheory.GroupGrowthGenerators

/-!
# Polynomial growth of virtually nilpotent groups

Every finite generating family of a group with a nilpotent subgroup of finite index has
polynomial growth. We collect letters using the upper central series and then rewrite words
in the ambient group using representatives of the left cosets.
-/

public section

namespace MathlibExt.GroupTheory.PolynomialGrowthWanted

section

open Subgroup commutatorElement

variable {G : Type*} [Group G]

-- Conjugating a letter introduces commutators one step lower in the upper central series.
-- Iterating the conjugation sums their word lengths, increasing the degree by at most one.
private theorem conjugateWord (x : G) (k : ℕ) {y : G} (hy : y ∈ upperCentralSeries G k) :
    ∃ s : Finset G, (∀ a ∈ s, a ∈ upperCentralSeries G (k - 1)) ∧
      ∀ m : ℕ, ∃ w : List G, (∀ a ∈ w, a = y ∨ a ∈ s) ∧
        w.length ≤ (m + 1) ^ k ∧ w.prod = x ^ m * y * (x ^ m)⁻¹ := by
  classical
  induction k generalizing y with
  | zero =>
    have : y = 1 := by simpa using hy
    exact ⟨∅, by simp, fun m => ⟨[], by simp, by simp, by simp [this]⟩⟩
  | succ k ih =>
    let z := ⁅y, x⁆⁻¹
    have hz : z ∈ upperCentralSeries G k :=
      inv_mem (mem_upperCentralSeries_succ_iff.mp hy x)
    obtain ⟨s, hs, hw⟩ := ih hz
    refine ⟨insert z s, ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hz
      · exact upperCentralSeries_mono G (Nat.sub_le k 1) (hs a ha)
    · intro m
      induction m with
      | zero => exact ⟨[y], by simp, by simp, by simp⟩
      | succ m ihm =>
        obtain ⟨u, hu, hlu, hpu⟩ := hw m
        obtain ⟨v, hv, hlv, hpv⟩ := ihm
        refine ⟨u ++ v, ?_, ?_, ?_⟩
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact Or.inr (Finset.mem_insert.mpr (hu a ha))
          · exact hv a ha
        · rw [List.length_append]
          calc
            _ ≤ (m + 1) ^ k + (m + 1) ^ (k + 1) := Nat.add_le_add hlu hlv
            _ = (m + 1) ^ k * (m + 2) := by rw [pow_succ, Nat.mul_succ _ (m + 1), Nat.add_comm]
            _ ≤ (m + 2) ^ (k + 1) := by
              rw [pow_succ]
              exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) k)
        · rw [List.prod_append, hpu, hpv, pow_succ]
          dsimp [z, commutatorElement_def]
          group

-- Move every occurrence of x to the left. The other letters are conjugated by powers
-- of x⁻¹, so they use only the original alphabet and finitely many letters at a lower level.
private theorem extractLetter [DecidableEq G] (x : G) (s : Finset G) (k : ℕ)
    (hs : ∀ a ∈ s, a ∈ upperCentralSeries G (k + 1)) :
    ∃ t : Finset G, (∀ a ∈ t, a ∈ upperCentralSeries G k) ∧
      ∀ w : List G, (∀ a ∈ w, a ∈ insert x s) →
        ∃ (m : ℕ) (v : List G), m ≤ w.length ∧ (∀ a ∈ v, a ∈ s ∪ t) ∧
          v.length ≤ w.length * (w.length + 1) ^ (k + 1) ∧ w.prod = x ^ m * v.prod := by
  classical
  choose extra hlevel hword using fun a : s =>
    conjugateWord x⁻¹ (k + 1) (hs a a.property)
  let t := s.attach.biUnion extra
  have memExtra (a : s) {z : G} (hz : z ∈ extra a) : z ∈ t :=
    Finset.mem_biUnion.mpr ⟨a, s.mem_attach a, hz⟩
  refine ⟨t, ?_, ?_⟩
  · intro z hz
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hz
    exact hlevel a z ha
  · intro w
    induction w with
    | nil => exact fun _ => ⟨0, [], by simp⟩
    | cons a w ih =>
      intro hall
      obtain ⟨m, v, hm, hv, hlen, hprod⟩ := ih fun z hz => hall z (List.mem_cons_of_mem _ hz)
      have hbound :
          (w.length + 1) ^ (k + 1) + w.length * (w.length + 1) ^ (k + 1) ≤
            (a :: w).length * ((a :: w).length + 1) ^ (k + 1) := by
        rw [List.length_cons, Nat.add_comm _ (w.length * _), ← Nat.succ_mul]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      by_cases ha : a = x
      · subst a
        refine ⟨m + 1, v, by simp; omega, hv, by omega, ?_⟩
        rw [List.prod_cons, hprod, pow_succ', mul_assoc]
      · have has := (Finset.mem_insert.mp (hall a List.mem_cons_self)).resolve_left ha
        let b : s := ⟨a, has⟩
        obtain ⟨u, hu, hlu, hpu⟩ := hword b m
        refine ⟨m, u ++ v, by simp; omega, ?_, ?_, ?_⟩
        · intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · rcases hu z hz with rfl | he
            · exact Finset.mem_union_left _ has
            · exact Finset.mem_union_right _ (memExtra b he)
          · exact hv z hz
        · rw [List.length_append]
          exact (Nat.add_le_add (hlu.trans (Nat.pow_le_pow_left (by omega) _)) hlen).trans hbound
        · rw [List.prod_cons, hprod, List.prod_append, hpu]
          dsimp [b]
          simp [inv_pow, mul_assoc]

-- A finite cover lets the collection argument count representations without requiring
-- their uniqueness.
private def PolynomialCover (s : Finset G) : Prop :=
  ∃ C d : ℕ, ∀ n : ℕ, ∃ ball : Finset G, ball.card ≤ C * (n + 1) ^ d ∧
    ∀ w : List G, (∀ a ∈ w, a ∈ s) → w.length ≤ n → w.prod ∈ ball

private theorem coverInsert [DecidableEq G] (x : G) (s : Finset G) (k : ℕ)
    (hs : ∀ a ∈ s, a ∈ upperCentralSeries G (k + 1))
    (hcover : ∀ t : Finset G, (∀ a ∈ t, a ∈ upperCentralSeries G k) →
      PolynomialCover (s ∪ t)) : PolynomialCover (insert x s) := by
  obtain ⟨t, ht, hcollect⟩ := extractLetter x s k hs
  obtain ⟨C, d, hball⟩ := hcover t ht
  refine ⟨C, (k + 2) * d + 1, fun n => ?_⟩
  let r := n * (n + 1) ^ (k + 1)
  obtain ⟨ball, hcard, hmem⟩ := hball r
  let f (m : ℕ) (v : G) := x ^ m * v
  refine ⟨Finset.image₂ f (Finset.range (n + 1)) ball, ?_, ?_⟩
  · have hr : r + 1 ≤ (n + 1) ^ (k + 2) := by
      rw [pow_succ' _ (k + 1), Nat.succ_mul]
      have : 0 < (n + 1) ^ (k + 1) := Nat.pow_pos (by omega)
      dsimp [r]
      omega
    calc
      _ ≤ (Finset.range (n + 1)).card * ball.card := Finset.card_image₂_le ..
      _ ≤ (n + 1) * (C * ((n + 1) ^ (k + 2)) ^ d) := by
        rw [Finset.card_range]
        gcongr
        exact hcard.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hr d))
      _ = C * (n + 1) ^ ((k + 2) * d + 1) := by
        rw [pow_succ _ ((k + 2) * d), pow_mul]
        ac_rfl
  · intro w hw hn
    obtain ⟨m, v, hm, hv, hlen, hp⟩ := hcollect w hw
    rw [hp]
    apply Finset.mem_image₂_of_mem (f := f) (Finset.mem_range.mpr (by omega))
    apply hmem v hv (hlen.trans ?_)
    exact Nat.mul_le_mul hn (Nat.pow_le_pow_left (by omega) _)

private theorem coverUpperCentral (k : ℕ) (s : Finset G)
    (hs : ∀ a ∈ s, a ∈ upperCentralSeries G k) : PolynomialCover s := by
  classical
  induction k generalizing s with
  | zero =>
    refine ⟨1, 0, fun n => ⟨{1}, by simp, fun w hw _ => ?_⟩⟩
    apply Finset.mem_singleton.mpr
    exact List.prod_eq_one fun a ha => by simpa using hs a (hw a ha)
  | succ k ih =>
    -- Induct on the letters at the current level, allowing arbitrary lower-level letters.
    suffices aux : ∀ u : Finset G, (∀ a ∈ u, a ∈ upperCentralSeries G (k + 1)) →
        ∀ l : Finset G, (∀ a ∈ l, a ∈ upperCentralSeries G k) → PolynomialCover (u ∪ l) by
      simpa using aux s hs ∅ (by simp)
    intro u
    induction u using Finset.induction_on with
    | empty =>
      intro _ l hl
      simpa using ih l hl
    | insert x u _ ihu =>
      intro hu l hl
      rw [Finset.insert_union]
      apply coverInsert x (u ∪ l) k
      · intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact hu a (Finset.mem_insert_of_mem ha)
        · exact upperCentralSeries_mono G (Nat.le_succ k) (hl a ha)
      · intro t ht
        rw [Finset.union_assoc]
        apply ihu (fun a ha => hu a (Finset.mem_insert_of_mem ha))
        intro a ha
        exact (Finset.mem_union.mp ha).elim (hl a) (ht a)

-- Each signed generator takes a coset representative to another representative times
-- a letter in H. There are only finitely many such letters, and rewriting preserves length.
private theorem coverFiniteExtension (H : Subgroup G) [H.FiniteIndex] [Group.IsNilpotent H]
    (s : Finset G) : PolynomialCover s := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  let next (a : G) (q : G ⧸ H) : G ⧸ H := QuotientGroup.mk (a * q.out)
  let step (a : G) (q : G ⧸ H) : H :=
    ⟨(next a q).out⁻¹ * (a * q.out), QuotientGroup.eq.mp (Quotient.out_eq' (next a q))⟩
  let letters := Finset.image₂ step s Finset.univ
  let q₀ : G ⧸ H := QuotientGroup.mk 1
  have rewriteWord (w : List G) (hw : ∀ a ∈ w, a ∈ s) :
      ∃ (q : G ⧸ H) (v : List H), (∀ b ∈ v, b ∈ letters) ∧ v.length = w.length ∧
        w.prod * q₀.out = q.out * (v.prod : G) := by
    induction w with
    | nil => exact ⟨q₀, [], by simp⟩
    | cons a w ih =>
      obtain ⟨q, v, hv, hlen, hp⟩ := ih fun b hb => hw b (List.mem_cons_of_mem _ hb)
      refine ⟨next a q, step a q :: v, ?_, by simp [hlen], ?_⟩
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact Finset.mem_image₂_of_mem (hw a List.mem_cons_self) (Finset.mem_univ q)
        · exact hv b hb
      · simp only [List.prod_cons, Subgroup.coe_mul, mul_assoc, hp]
        dsimp [step]
        group
  obtain ⟨k, hk⟩ := Group.IsNilpotent.nilpotent (G := H)
  obtain ⟨C, d, hball⟩ := coverUpperCentral k letters (fun _ _ => hk ▸ Subgroup.mem_top _)
  refine ⟨Fintype.card (G ⧸ H) * C, d, fun n => ?_⟩
  obtain ⟨ball, hcard, hmem⟩ := hball n
  let f (q : G ⧸ H) (b : H) := q.out * (b : G) * q₀.out⁻¹
  refine ⟨Finset.image₂ f Finset.univ ball, ?_, ?_⟩
  · calc
      _ ≤ Finset.univ.card * ball.card := Finset.card_image₂_le ..
      _ ≤ _ := by rw [Finset.card_univ, mul_assoc]; exact Nat.mul_le_mul_left _ hcard
  · intro w hw hn
    obtain ⟨q, v, hv, hlen, hp⟩ := rewriteWord w hw
    have he : w.prod = f q v.prod := eq_mul_inv_iff_mul_eq.mpr hp
    rw [he]
    exact Finset.mem_image₂_of_mem (Finset.mem_univ q) (hmem v hv (hlen.trans_le hn))

end

/-- **Virtually nilpotent groups have polynomial growth** (Wolf 1968, Bass 1972; the converse of
Gromov's theorem, as recalled in Gromov, *Groups of polynomial growth and expanding maps*, Publ.
Math. IHÉS 53 (1981), p. 54: "If a finitely generated group Γ has a nilpotent subgroup of finite
index then Γ has polynomial growth"). If `G` has a nilpotent subgroup of finite index, every finite
generating family of `G` has polynomial growth. -/
theorem hasPolynomialGrowth_of_virtuallyNilpotent {G ι : Type*} [Group G] [Finite ι]
    (P : Group.Generators G ι) (H : Subgroup G) (hH : H.FiniteIndex) (hn : Group.IsNilpotent H) :
    P.HasPolynomialGrowth := by
  classical
  let := Fintype.ofFinite ι
  let letter (p : ι × Bool) := cond p.2 (P.val p.1) (P.val p.1)⁻¹
  let s := Finset.univ.image letter
  obtain ⟨C, d, hball⟩ := coverFiniteExtension H s
  refine ⟨P.finite_wordLength_le, C, d, fun n => ?_⟩
  obtain ⟨ball, hcard, hmem⟩ := hball n
  have eval (l : List (ι × Bool)) : (l.map letter).prod = P.wordProd l := by
    induction l with
    | nil => simp
    | cons a l ih => rw [List.map_cons, List.prod_cons, ih, P.wordProd_cons]
  have memBall (g : G) (hg : P.wordLength g ≤ n) : g ∈ ball := by
    obtain ⟨l, hl, rfl⟩ := (P.wordLength_le_iff g).mp hg
    rw [← eval]
    apply hmem (l.map letter) _ (by simpa using hl)
    intro a ha
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp ha
    exact Finset.mem_image_of_mem _ (Finset.mem_univ p)
  calc
    P.growth n ≤ Nat.card ball :=
      Nat.card_le_card_of_injective
        (fun g : {g : G // P.wordLength g ≤ n} => (⟨g.1, memBall g.1 g.2⟩ : ball))
        (fun _ _ h => Subtype.ext (congrArg (fun b : ball => (b : G)) h))
    _ = ball.card := Nat.card_eq_finsetCard ball
    _ ≤ _ := hcard

end MathlibExt.GroupTheory.PolynomialGrowthWanted
