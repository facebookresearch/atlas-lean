/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two-colorings of sparse uniform hypergraphs

`manyTransversalNonCoverSets_holds` gives a positive lower bound on the fraction of proper
two-colorings in Erdős Problem 1027. We leave some vertices uncolored at random and then
prescribe one additional vertex color for each edge still missing a color.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.TransversalNonCoverSetsErdosProblem1027Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1027, https://www.erdosproblems.com/1027 (status
PROVED). UnsolvedMath record UM-30007134 (`EP-1027`), dataset ulamai/UnsolvedMath v1.8.0.

The sets are finite sets of natural numbers, which loses nothing for finite families. `≫_c 2^{|X|}`
is `≥ δ 2^{|X|}` with `δ > 0` depending only on `c`. Compared with the formal-conjectures statement
`ErdosProblems/1027.lean` (equivalent; no code imported).
-/

/-- **Sets meeting but not containing the members of a family.** For a finite family $F$ of finite
sets of natural numbers with union $X$, this is the finite set of all $B \subseteq X$ that meet
every member of $F$ and contain none of them. -/
def transversalNonCoverSets (F : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  (F.biUnion id).powerset.filter fun B => ∀ A ∈ F, (A ∩ B).Nonempty ∧ ¬ A ⊆ B

/-- **Erdős Problem 1027 (sets meeting but not containing members of a family).** For every real
$c > 0$ there is a real $\delta > 0$ such that, for all sufficiently large $n$, every finite family
$F$ of finite sets of natural numbers, each of size $n$, with $|F| \le c \cdot 2^n$ and with union
$X$, has at least $\delta \cdot 2^{|X|}$ subsets $B \subseteq X$ that meet every member of $F$ and
contain none of them. -/
def manyTransversalNonCoverSets : Prop :=
  ∀ c : ℝ, 0 < c → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ F : Finset (Finset ℕ),
    (∀ A ∈ F, A.card = n) → (F.card : ℝ) ≤ c * 2 ^ n →
      δ * 2 ^ (F.biUnion id).card ≤ (transversalNonCoverSets F).card

open Finset

variable {V I : Type*} [Fintype V] [Fintype I]

-- Mass of an event under independent coordinate weights.
open scoped Classical in
private noncomputable def mass {α : Type*} [Fintype α] (w : V → α → ℝ)
    (P : (V → α) → Prop) : ℝ :=
  ∑ x ∈ univ.filter P, ∏ v, w v (x v)

private lemma mass_nonneg {α : Type*} [Fintype α] {w : V → α → ℝ}
    (hw : ∀ v a, 0 ≤ w v a) (P : (V → α) → Prop) : 0 ≤ mass w P :=
  sum_nonneg fun _ _ => prod_nonneg fun _ _ => hw _ _

private lemma mass_mono {α : Type*} [Fintype α] {w : V → α → ℝ}
    (hw : ∀ v a, 0 ≤ w v a) {P Q : (V → α) → Prop} (h : ∀ x, P x → Q x) :
    mass w P ≤ mass w Q := by
  classical
  exact sum_le_sum_of_subset_of_nonneg (monotone_filter_right _ fun x _ => h x)
    fun _ _ _ => prod_nonneg fun _ _ => hw _ _

open scoped Classical in
private lemma mass_box {α : Type*} [Fintype α] (w : V → α → ℝ) (D : V → α → Prop) :
    mass w (fun x => ∀ v, D v (x v)) = ∏ v, ∑ a, if D v a then w v a else 0 := by
  simp only [mass, sum_filter, Fintype.prod_sum, Fintype.prod_ite_zero]
  apply sum_congr rfl
  intro x _
  split_ifs <;> rfl

private noncomputable def partialWeight (q : ℝ) : Option Bool → ℝ
  | none => q
  | some _ => (1 - q) / 2

private lemma partial_nonneg {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1) (a : Option Bool) :
    0 ≤ partialWeight q a := by
  cases a <;> simp [partialWeight, *]
  linarith

private lemma partial_sum (q : ℝ) : ∑ a, partialWeight q a = 1 := by
  simp [Fintype.sum_option, partialWeight]
  ring

private noncomputable def fillWeight : Option Bool → Bool → ℝ
  | none, _ => 1 / 2
  | some a, b => if a = b then 1 else 0

private lemma fill_nonneg (a : Option Bool) (b : Bool) : 0 ≤ fillWeight a b := by
  cases a <;> simp only [fillWeight] <;> positivity

private def missing (a : Finset V) (b : Bool) (p : V → Option Bool) : Prop :=
  ∀ v, v ∈ a → p v ≠ some b

private def solid (a : Finset V) (b : Bool) (p : V → Option Bool) : Prop :=
  ∀ v, v ∈ a → p v = some b

open scoped Classical in
private lemma mass_edge (q : ℝ) (a : Finset V) (D : Option Bool → Prop) :
    mass (fun _ => partialWeight q) (fun p => ∀ v, v ∈ a → D (p v)) =
      (∑ z, if D z then partialWeight q z else 0) ^ a.card := by
  rw [mass_box _ (fun v z => v ∈ a → D z)]
  calc
    _ = ∏ v, (if v ∈ a then (∑ z, if D z then partialWeight q z else 0) else 1) := by
      apply prod_congr rfl
      intro v _
      by_cases h : v ∈ a <;> simp [h, partialWeight]
      ring
    _ = _ := by simp

private lemma mass_missing (q : ℝ) (a : Finset V) (b : Bool) :
    mass (fun _ => partialWeight q) (missing a b) = ((1 + q) / 2) ^ a.card := by
  change mass _ (fun p => ∀ v, v ∈ a → p v ≠ some b) = _
  rw [mass_edge _ _ (· ≠ some b)]
  congr 1
  cases b <;> simp [Fintype.sum_option, partialWeight] <;> ring

private lemma mass_solid (q : ℝ) (a : Finset V) (b : Bool) :
    mass (fun _ => partialWeight q) (solid a b) = ((1 - q) / 2) ^ a.card := by
  change mass _ (fun p => ∀ v, v ∈ a → p v = some b) = _
  rw [mass_edge _ _ (· = some b)]
  simp [partialWeight]

-- On the overlap of oppositely deficient edges a vertex must be blank. Relative to
-- two independent missing-color constraints this costs a factor of at most 4q.
open scoped Classical in
private def conflict (a d : Finset V) (p : V → Option Bool) : Prop :=
  (a ∩ d).Nonempty ∧ missing a false p ∧ missing d true p

private lemma mass_conflict (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1 / 4) (a d : Finset V) :
    mass (fun _ => partialWeight q) (conflict a d) ≤
      4 * q * (((1 + q) / 2) ^ a.card * ((1 + q) / 2) ^ d.card) := by
  classical
  let r := (1 + q) / 2
  let f (s : Finset V) (v : V) := if v ∈ s then r else 1
  have hf (s : Finset V) : ∏ v, f s v = r ^ s.card := by simp [f]
  by_cases h : (a ∩ d).Nonempty
  · obtain ⟨j, hj⟩ := h
    obtain ⟨hja, hjd⟩ := mem_inter.mp hj
    let D (v : V) (z : Option Bool) := (v ∈ a → z ≠ some false) ∧ (v ∈ d → z ≠ some true)
    calc
      _ ≤ mass (fun _ => partialWeight q) (fun p => ∀ v, D v (p v)) :=
        mass_mono (fun _ => partial_nonneg hq (by linarith)) fun p hp v => ⟨hp.2.1 v, hp.2.2 v⟩
      _ = _ := mass_box _ _
      _ ≤ ∏ v, ((if j = v then 4 * q else 1) * (f a v * f d v)) := by
        apply prod_le_prod₀
        · exact fun v _ => sum_nonneg fun z _ => by
            split_ifs <;> first | exact partial_nonneg hq (by linarith) _ | rfl
        · intro v _
          have hr : (1 / 2 : ℝ) ≤ r := by dsimp [r]; linarith
          have hs : (1 / 2 : ℝ) * (1 / 2) ≤ r * r := mul_self_le_mul_self (by norm_num) hr
          by_cases hjv : j = v
          · subst v
            simp [D, Fintype.sum_option, partialWeight, f, hja, hjd]
            nlinarith [mul_le_mul_of_nonneg_left hs hq]
          · by_cases ha : v ∈ a <;> by_cases hd : v ∈ d <;>
              simp [D, Fintype.sum_option, partialWeight, f, ha, hd, hjv, r] <;>
              dsimp [r] at hs <;> linarith
      _ = _ := by rw [prod_mul_distrib, prod_mul_distrib, hf, hf]; simp [r]
  · have : univ.filter (conflict a d) = ∅ := by simp [conflict, h]
    rw [mass, this, sum_empty]
    positivity

private def proper (e : I → Finset V) (y : V → Bool) : Prop :=
  ∀ i b, ∃ v ∈ e i, y v = b

open scoped Classical in
private noncomputable def properColorings (e : I → Finset V) := univ.filter (proper e)

open scoped Classical in
private noncomputable def needs (e : I → Finset V) (p : V → Option Bool) :
    Finset (I × Bool) :=
  univ.filter fun k => missing (e k.1) k.2 p

-- Pick one blank for each missing color. A vertex chosen by two edges gets the
-- same prescription, since edges missing opposite colors are disjoint.
omit [Fintype V] in
private lemma prescriptions (e : I → Finset V) (p : V → Option Bool)
    (hs : ∀ i b, ¬ solid (e i) b p) (hc : ∀ i j, ¬ conflict (e i) (e j) p) :
    ∃ (S : Finset V) (t : V → Bool), S.card ≤ (needs e p).card ∧
      (∀ v ∈ S, p v = none) ∧
      ∀ y, (∀ v b, p v = some b → y v = b) → (∀ v ∈ S, y v = t v) → proper e y := by
  classical
  let T := needs e p
  have hm (k : T) : missing (e k.val.1) k.val.2 p := (mem_filter.mp k.property).2
  have hex (k : T) : ∃ v ∈ e k.val.1, p v = none := by
    by_contra! h
    apply hs k.val.1 (!k.val.2)
    intro v hv
    have h₁ := hm k v hv
    have h₂ := h v hv
    cases hk : k.val.2 <;> cases hz : p v <;> simp_all
  choose pick hmem hblank using hex
  have consistent (k l : T) (h : pick k = pick l) : k.val.2 = l.val.2 := by
    have overlap : pick k ∈ e k.val.1 ∩ e l.val.1 :=
      mem_inter.mpr ⟨hmem k, h ▸ hmem l⟩
    have hk := hm k
    have hl := hm l
    cases hb : k.val.2 <;> cases hd : l.val.2 <;> simp_all only [Bool.false_eq_true,
      Bool.true_eq_false]
    · exact hc _ _ ⟨⟨_, overlap⟩, hk, hl⟩
    · exact hc _ _ ⟨⟨_, mem_inter.mpr (mem_inter.mp overlap).symm⟩, hl, hk⟩
  let S := univ.image pick
  let t := fun v => decide (∃ k : T, pick k = v ∧ k.val.2 = true)
  have ht (k : T) : t (pick k) = k.val.2 := by
    cases h : k.val.2
    · apply decide_eq_false
      rintro ⟨l, hl, hb⟩
      simp_all [consistent l k hl]
    · exact decide_eq_true ⟨k, rfl, h⟩
  refine ⟨S, t, card_image_le.trans_eq (by simp [T]), ?_, ?_⟩
  · intro v hv
    obtain ⟨k, _, rfl⟩ := mem_image.mp hv
    exact hblank k
  · intro y hfixed hpres i b
    by_cases h : missing (e i) b p
    · let k : T := ⟨(i, b), mem_filter.mpr ⟨mem_univ _, h⟩⟩
      exact ⟨pick k, hmem k, (hpres _ (mem_image_of_mem _ (mem_univ k))).trans (ht k)⟩
    · unfold missing at h
      push Not at h
      obtain ⟨v, hv, h⟩ := h
      exact ⟨v, hv, hfixed v b h⟩

private lemma completion_bound (e : I → Finset V) (p : V → Option Bool) (K : ℕ)
    (hs : ∀ i b, ¬ solid (e i) b p) (hc : ∀ i j, ¬ conflict (e i) (e j) p)
    (hk : (needs e p).card ≤ K) :
    (1 / 2 : ℝ) ^ K ≤ mass (fun v => fillWeight (p v)) (proper e) := by
  classical
  obtain ⟨S, t, hcard, hblank, hproper⟩ := prescriptions e p hs hc
  let D (v : V) (b : Bool) := (∀ a, p v = some a → b = a) ∧ (v ∈ S → b = t v)
  calc
    _ ≤ (1 / 2 : ℝ) ^ S.card :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (hcard.trans hk)
    _ = mass (fun v => fillWeight (p v)) (fun y => ∀ v, D v (y v)) := by
      rw [mass_box]
      have heq (v : V) : (∑ b, if D v b then fillWeight (p v) b else 0) =
          if v ∈ S then 1 / 2 else 1 := by
        by_cases h : v ∈ S
        · by_cases ht : t v = true <;> simp_all [D, fillWeight]
        · obtain hp | ⟨b, hp⟩ := (p v).eq_none_or_eq_some
          · norm_num [D, h, hp, fillWeight]
          · cases b <;> simp [D, h, hp, fillWeight]
      calc
        _ = ∏ v, (if v ∈ S then (1 / 2 : ℝ) else 1) := by simp
        _ = _ := by
          apply prod_congr rfl
          intro v _
          convert (heq v).symm using 1
          apply sum_congr rfl
          intro b _
          split_ifs <;> rfl
    _ ≤ _ := mass_mono (fun _ => fill_nonneg _) fun y hy =>
      hproper y (fun v => (hy v).1) fun v => (hy v).2

open scoped Classical in
private noncomputable def average (q : ℝ) (f : (V → Option Bool) → ℝ) :=
  ∑ p, (∏ v, partialWeight q (p v)) * f p

private lemma average_const (q x : ℝ) : average (V := V) q (fun _ => x) = x := by
  classical
  unfold average
  rw [← sum_mul, ← Fintype.prod_sum (fun (_ : V) => partialWeight q)]
  simp only [partial_sum, prod_const_one, one_mul]

open scoped Classical in
private lemma average_count {J : Type*} [Fintype J] (q : ℝ) (A : J → (V → Option Bool) → Prop) :
    average q (fun p => ((univ.filter fun i => A i p).card : ℝ)) =
      ∑ i, mass (fun _ => partialWeight q) (A i) := by
  classical
  unfold average mass
  simp only [← sum_boole, mul_sum, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro p _
  split_ifs <;> simp

-- Summing out the partial coloring leaves independent fair colors.
open scoped Classical in
private lemma average_completion (q : ℝ) (P : (V → Bool) → Prop) :
    average q (fun p => mass (fun v => fillWeight (p v)) P) =
      ((univ.filter P).card : ℝ) * (1 / 2) ^ Fintype.card V := by
  classical
  unfold average mass
  simp_rw [mul_sum]
  rw [sum_comm]
  have hm (b : Bool) : (∑ z, partialWeight q z * fillWeight z b) = 1 / 2 := by
    cases b <;> simp [Fintype.sum_option, partialWeight, fillWeight] <;> ring
  calc
    _ = ∑ _ ∈ univ.filter P, (1 / 2 : ℝ) ^ Fintype.card V := by
      apply sum_congr rfl
      intro y _
      simp only [← prod_mul_distrib]
      rw [← Fintype.prod_sum (fun v z => partialWeight q z * fillWeight z (y v))]
      simp only [hm, prod_const, card_univ]
    _ = _ := by simp

open scoped Classical in
private noncomputable def solids (e : I → Finset V) (p : V → Option Bool) :=
  univ.filter fun k : I × Bool => solid (e k.1) k.2 p

open scoped Classical in
private noncomputable def conflicts (e : I → Finset V) (p : V → Option Bool) :=
  univ.filter fun k : I × I => conflict (e k.1) (e k.2) p

-- Charge a failed partial coloring to a solid edge, a conflicting pair, or more
-- than K missing colors. This also handles an empty edge family.
private lemma pointwise_bound (e : I → Finset V) (p : V → Option Bool) {K : ℕ} (hK : 0 < K) :
    (1 / 2 : ℝ) ^ K * (1 - (solids e p).card - (conflicts e p).card - (needs e p).card / K) ≤
      mass (fun v => fillWeight (p v)) (proper e) := by
  classical
  have hn := mass_nonneg (fun v => fill_nonneg (p v)) (proper e)
  have hdiv : 0 ≤ ((needs e p).card : ℝ) / K := by positivity
  have h₁ := Nat.cast_nonneg (α := ℝ) (solids e p).card
  have h₂ := Nat.cast_nonneg (α := ℝ) (conflicts e p).card
  by_cases hbad : 1 - ((solids e p).card : ℝ) - (conflicts e p).card - (needs e p).card / K ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hbad).trans hn
  have hs (i : I) (b : Bool) (h : solid (e i) b p) : False := by
    have hpos : (solids e p).Nonempty := ⟨(i, b), mem_filter.mpr ⟨mem_univ _, h⟩⟩
    have : (1 : ℝ) ≤ (solids e p).card := by exact_mod_cast one_le_card.mpr hpos
    linarith
  have hc (i j : I) (h : conflict (e i) (e j) p) : False := by
    have hpos : (conflicts e p).Nonempty := ⟨(i, j), mem_filter.mpr ⟨mem_univ _, h⟩⟩
    have : (1 : ℝ) ≤ (conflicts e p).card := by exact_mod_cast one_le_card.mpr hpos
    linarith
  have hk : (needs e p).card ≤ K := by
    have : ((needs e p).card : ℝ) / K ≤ 1 := by linarith
    exact_mod_cast (div_le_one (by exact_mod_cast hK)).mp this
  apply le_trans _ (completion_bound e p K hs hc hk)
  exact mul_le_of_le_one_right (by positivity) (by linarith)

private lemma density_bound (e : I → Finset V) {n K : ℕ} (he : ∀ i, (e i).card = n)
    {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1 / 4) (hK : 0 < K)
    (hs : (Fintype.card I : ℝ) * ((1 - q) / 2) ^ n ≤ 1 / 16)
    (hm : (Fintype.card I : ℝ) * ((1 + q) / 2) ^ n ≤ K / 16)
    (hc : 4 * q * ((Fintype.card I : ℝ) * ((1 + q) / 2) ^ n) ^ 2 ≤ 1 / 8) :
    (1 / 2 : ℝ) ^ K / 2 ≤ ((properColorings e).card : ℝ) * (1 / 2) ^ Fintype.card V := by
  classical
  have hsol : average q (fun p => ((solids e p).card : ℝ)) ≤ 1 / 8 := by
    unfold solids
    rw [average_count q (fun k : I × Bool => solid (e k.1) k.2)]
    simp only [mass_solid, he, sum_const, card_univ, Fintype.card_prod, Fintype.card_bool,
      Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul]
    linarith
  have hneed : average q (fun p => ((needs e p).card : ℝ)) / K ≤ 1 / 8 := by
    unfold needs
    rw [average_count q (fun k : I × Bool => missing (e k.1) k.2),
      div_le_iff₀ (by exact_mod_cast hK)]
    simp only [mass_missing, he, sum_const, card_univ, Fintype.card_prod, Fintype.card_bool,
      Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul]
    linarith
  have hpair : average q (fun p => ((conflicts e p).card : ℝ)) ≤ 1 / 8 := by
    unfold conflicts
    rw [average_count q (fun k : I × I => conflict (e k.1) (e k.2))]
    calc
      _ ≤ ∑ _ : I × I, 4 * q * (((1 + q) / 2) ^ n * ((1 + q) / 2) ^ n) := by
        apply sum_le_sum
        intro k _
        simpa only [he] using mass_conflict q hq hq' (e k.1) (e k.2)
      _ ≤ _ := by
        simp only [sum_const, card_univ, Fintype.card_prod, Nat.cast_mul, nsmul_eq_mul]
        linarith only [hc]
  let d := (1 / 2 : ℝ) ^ K
  calc
    _ ≤ d * (1 - average q (fun p => ((solids e p).card : ℝ)) -
        average q (fun p => ((conflicts e p).card : ℝ)) -
        average q (fun p => ((needs e p).card : ℝ)) / K) := by
      have hd : 0 ≤ d := by dsimp [d]; positivity
      change d / 2 ≤ _
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (by linarith) hd
    _ = average q (fun p => d * (1 - (solids e p).card - (conflicts e p).card -
        (needs e p).card / K)) := by
      have hunit := average_const (V := V) q 1
      unfold average at hunit ⊢
      simp only [mul_one] at hunit
      conv_rhs => arg 2; ext p; rw [mul_left_comm]
      rw [← mul_sum]
      congr 1
      simp only [mul_sub, mul_one, ← mul_div_assoc, sum_sub_distrib, hunit]
      simp only [div_eq_inv_mul, mul_sum]
    _ ≤ average q (fun p => mass (fun v => fillWeight (p v)) (proper e)) :=
      sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (pointwise_bound e p hK)
        (prod_nonneg fun _ _ => partial_nonneg hq (by linarith) _)
    _ = _ := average_completion q _

private def edgeOnUnion (F : Finset (Finset ℕ)) (i : F) : Finset (F.biUnion id) :=
  i.val.subtype (· ∈ F.biUnion id)

-- The true color class of a proper coloring determines it uniquely and is
-- one of the transversals in the statement.
private lemma count_transversals (F : Finset (Finset ℕ)) :
    (properColorings (edgeOnUnion F)).card ≤ (transversalNonCoverSets F).card := by
  classical
  let X := F.biUnion id
  let B (y : X → Bool) := (univ.filter fun v => y v = true).map (Function.Embedding.subtype _)
  have hB (y : X → Bool) (v : X) : v.val ∈ B y ↔ y v = true := by simp [B]
  have hinj : Function.Injective B := by
    intro y z h
    funext v
    have hh := (hB y v).symm.trans (h ▸ hB z v)
    cases hy : y v <;> cases hz : z v <;> simp_all
  rw [← card_image_of_injective _ hinj]
  apply card_le_card
  intro B' h
  obtain ⟨y, hy, rfl⟩ := mem_image.mp h
  have hp := (mem_filter.mp hy).2
  refine mem_filter.mpr ⟨mem_powerset.mpr (fun v hv => property_of_mem_map_subtype _ hv), ?_⟩
  intro a ha
  let i : F := ⟨a, ha⟩
  obtain ⟨v, hv, hv'⟩ := hp i true
  obtain ⟨u, hu, hu'⟩ := hp i false
  refine ⟨⟨v.val, mem_inter.mpr ⟨mem_subtype.mp hv, (hB y v).mpr hv'⟩⟩, fun hsub => ?_⟩
  have := (hB y u).mp (hsub (mem_subtype.mp hu))
  simp_all

/--
**Erdős Problem 1027 holds.** For every real $c > 0$ there is a real $\delta > 0$ such that, for
all sufficiently large $n$, every finite family $F$ of finite sets of natural numbers, each of
size $n$, with $|F| \le c \cdot 2^n$ and with union $X$, has at least $\delta \cdot 2^{|X|}$
subsets $B \subseteq X$ that meet every member of $F$ and contain none of them.

Source: T.
F. Bloom, Erdős Problems, Problem #1027, https://www.erdosproblems.com/1027 (status PROVED);
resolution: K. Chan, proof in the erdosproblems.com/1027 comments; formal proof plby/lean-proofs,
src/latest/ErdosProblems/Erdos1027.lean, erdosproblems.com/1027: 'This is true, and a proof was
given in the comment section by Koishi Chan',
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1027.lean#L209.
-/
public theorem manyTransversalNonCoverSets_holds : manyTransversalNonCoverSets := by
  classical
  intro c hc
  let t := 16 * c
  let M := c * Real.exp t
  let K := ⌈16 * M⌉₊ + 1
  have ht : 0 < t := by dsimp [t]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hK : 0 < K := Nat.succ_pos _
  have hKM : 16 * M ≤ (K : ℝ) := (Nat.le_ceil _).trans (by dsimp [K]; push_cast; linarith)
  refine ⟨(1 / 2 : ℝ) ^ K / 2, by positivity, ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_ge (max (4 * t) (32 * t * M ^ 2))
  apply Filter.eventually_atTop.mpr
  refine ⟨N, fun n hn F hunif hF => ?_⟩
  have hlarge : max (4 * t) (32 * t * M ^ 2) ≤ (n : ℝ) :=
    hN.trans (by exact_mod_cast hn)
  obtain ⟨htn, hMn⟩ := max_le_iff.mp hlarge
  have hn' : 0 < (n : ℝ) := by linarith
  let q := t / n
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq' : q ≤ 1 / 4 := (div_le_iff₀ hn').mpr (by linarith)
  let X := F.biUnion id
  let e := edgeOnUnion F
  have he (i : F) : (e i).card = n := by
    have hsub : i.val ⊆ F.biUnion id := subset_biUnion_of_mem id i.property
    simpa only [e, edgeOnUnion, card_subtype, filter_true_of_mem fun _ hv => hsub hv] using
      hunif i.val i.property
  have hedge (s : ℝ) (hs : 0 ≤ s) :
      (Fintype.card F : ℝ) * (s / 2) ^ n ≤ c * s ^ n := by
    rw [Fintype.card_coe]
    calc
      _ ≤ (c * 2 ^ n) * (s / 2) ^ n :=
        mul_le_mul_of_nonneg_right hF (by positivity)
      _ = _ := by rw [div_pow]; field_simp
  have hsolid : (Fintype.card F : ℝ) * ((1 - q) / 2) ^ n ≤ 1 / 16 := by
    apply (hedge _ (by linarith)).trans
    calc
      _ ≤ c * Real.exp (-t) :=
        mul_le_mul_of_nonneg_left (Real.one_sub_div_pow_le_exp_neg (by linarith : t ≤ n)) hc.le
      _ ≤ _ := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos t)]
        have := Real.add_one_le_exp t
        dsimp [t] at *
        linarith
  have hmissing : (Fintype.card F : ℝ) * ((1 + q) / 2) ^ n ≤ M :=
    (hedge _ (by positivity)).trans (mul_le_mul_of_nonneg_left
      (Real.one_add_div_pow_le_exp (by linarith : -(n : ℝ) ≤ t)) hc.le)
  have hconf : 4 * q * ((Fintype.card F : ℝ) * ((1 + q) / 2) ^ n) ^ 2 ≤ 1 / 8 := by
    calc
      _ ≤ 4 * q * M ^ 2 := by gcongr
      _ = (4 * t * M ^ 2) / n := by dsimp [q]; ring
      _ ≤ _ := (div_le_iff₀ hn').mpr (by linarith)
  have h := density_bound e he hq hq' hK hsolid (hmissing.trans (by linarith)) hconf
  rw [one_div_pow (2 : ℝ) (Fintype.card X), ← div_eq_mul_one_div, Fintype.card_coe,
    le_div_iff₀ (by positivity)] at h
  exact h.trans (Nat.cast_le.mpr (count_transversals F))

end MathlibExt.Combinatorics.TransversalNonCoverSetsErdosProblem1027Wanted
