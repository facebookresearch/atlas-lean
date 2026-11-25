/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.InformationTheory.Coding.KraftMcMillan
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
public import MathlibExt.InformationTheory.PrefixFree

@[expose] public section

open scoped BigOperators

namespace MathlibExt.InformationTheory.KraftMcMillan

/-!
# Kraft–McMillan theorem for finite prefix codes

For a finite code alphabet with at least two symbols, a finite family of
natural-number lengths is realized by a prefix-free code if and only if its
Kraft sum is at most one.

* The forward direction goes through unique decodability: a prefix-free code
  with no empty codeword is uniquely decodable, so pinned Mathlib's
  `InformationTheory.kraft_mcmillan_inequality` applies. (The empty-codeword
  case forces a singleton source alphabet, where the sum equals one.)
* The converse is the classical finite greedy construction, which Mathlib does
  not currently provide: words are chosen length by length, each new word of
  length `n` outside the extensions of previously chosen codewords; the Kraft
  hypothesis guarantees such a word exists.

Source: Leon G. Kraft, *A Device for Quantizing, Grouping, and Coding
Amplitude-Modulated Pulses*, S.M. thesis, MIT, 1949; B. McMillan,
"Two inequalities implied by unique decipherability",
*IEEE Transactions on Information Theory* 2(4) (1956), 115–116,
DOI 10.1109/TIT.1956.1056818.
-/

/-- Two words admitting a common extension are comparable by prefix. -/
private theorem prefix_of_common_extension {β : Type*} (w₁ : List β) :
    ∀ (w₂ A B : List β), w₁ ++ A = w₂ ++ B → w₁ <+: w₂ ∨ w₂ <+: w₁ := by
  induction w₁ with
  | nil => intro w₂ _ _ _; exact Or.inl ⟨w₂, rfl⟩
  | cons x xs ih =>
    intro w₂ A B h
    cases w₂ with
    | nil => exact Or.inr ⟨x :: xs, rfl⟩
    | cons y ys =>
      obtain ⟨hxy, htail⟩ := List.cons_eq_cons.mp h
      subst hxy
      rcases ih _ _ _ htail with ⟨t, ht⟩ | ⟨t, ht⟩
      · exact Or.inl ⟨t, by simp [ht]⟩
      · exact Or.inr ⟨t, by simp [ht]⟩

/-- A prefix-free code with no empty codeword is uniquely decodable. -/
private theorem uniquelyDecodable_of_prefixFree {α β : Type*} {code : α → List β}
    (hPF : IsPrefixFree code) (hempty : ∀ a, code a ≠ []) :
    InformationTheory.UniquelyDecodable (Set.range code) := by
  suffices key : ∀ L₁ L₂ : List (List β), (∀ w ∈ L₁, w ∈ Set.range code) →
      (∀ w ∈ L₂, w ∈ Set.range code) → L₁.flatten = L₂.flatten → L₁ = L₂ from
    fun L₁ L₂ h₁ h₂ hh => key L₁ L₂ h₁ h₂ hh
  intro L₁
  induction L₁ with
  | nil =>
    intro L₂ _ h₂ hflat
    cases L₂ with
    | nil => rfl
    | cons w₂ _ =>
      obtain ⟨a₂, ha₂⟩ := h₂ w₂ (by simp)
      have hw2nil : w₂ = [] := by
        cases w₂ with
        | nil => rfl
        | cons _ _ => simp at hflat
      have hcon : code a₂ = [] := by rw [ha₂, hw2nil]
      exact absurd hcon (hempty a₂)
  | cons w₁ t₁ ih =>
    intro L₂ h₁ h₂ hflat
    cases L₂ with
    | nil =>
      obtain ⟨a₁, ha₁⟩ := h₁ w₁ (by simp)
      have hw1nil : w₁ = [] := by
        cases w₁ with
        | nil => rfl
        | cons _ _ => simp at hflat
      have hcon : code a₁ = [] := by rw [ha₁, hw1nil]
      exact absurd hcon (hempty a₁)
    | cons w₂ t₂ =>
      obtain ⟨a₁, ha₁⟩ := h₁ w₁ (by simp)
      obtain ⟨a₂, ha₂⟩ := h₂ w₂ (by simp)
      have happ : w₁ ++ t₁.flatten = w₂ ++ t₂.flatten := hflat
      have hweq : w₁ = w₂ := by
        have heq : a₁ = a₂ := by
          by_contra hne
          rcases prefix_of_common_extension w₁ w₂ _ _ happ with hpref | hpref
          · exact hPF hne (by rw [ha₁, ha₂]; exact hpref)
          · exact hPF (fun heq => hne heq.symm) (by rw [ha₁, ha₂]; exact hpref)
        rw [← ha₁, ← ha₂, heq]
      have htail : t₁.flatten = t₂.flatten := by
        rw [hweq] at happ
        exact List.append_cancel_left happ
      have hteq : t₁ = t₂ :=
        ih _ (fun w hw => h₁ w (by simp [hw])) (fun w hw => h₂ w (by simp [hw])) htail
      rw [hweq, hteq]

/-- Forward direction: lengths of a prefix-free code satisfy the Kraft bound. -/
private theorem forward {α β : Type*} [Fintype α] [Fintype β]
    (l : α → ℕ) (code : α → List β) (hPF : IsPrefixFree code)
    (hlen : ∀ a, (code a).length = l a) (hq : 2 ≤ Fintype.card β) :
    ∑ a : α, (1 : ℝ) / (Fintype.card β : ℝ) ^ (l a) ≤ 1 := by
  classical
  by_cases em : ∃ a, code a = []
  · -- An empty codeword forces a singleton source alphabet, so the sum is one.
    obtain ⟨a₀, ha₀⟩ := em
    have hsingle : ∀ a, a = a₀ := fun a => hPF.eq_of_mem_nil ha₀ a
    have hl0 : l a₀ = 0 := by simp [← hlen a₀, ha₀]
    have hsum : ∑ a : α, (1 : ℝ) / (Fintype.card β : ℝ) ^ (l a)
        = (1 : ℝ) / (Fintype.card β : ℝ) ^ (l a₀) := by
      refine Finset.sum_eq_single_of_mem _ (Finset.mem_univ a₀) ?_
      intro b _ hb
      exact absurd (hsingle b) hb
    calc ∑ a : α, (1 : ℝ) / (Fintype.card β : ℝ) ^ (l a) = (1 : ℝ) := by
            rw [hsum, hl0, pow_zero, div_one]
      _ ≤ 1 := le_refl 1
  · -- Otherwise the code is uniquely decodable and Mathlib's inequality applies.
    have hempty : ∀ a, code a ≠ [] := fun a ha => em ⟨a, ha⟩
    have hUD := uniquelyDecodable_of_prefixFree hPF hempty
    have himg : ((Finset.image code Finset.univ : Finset (List β)) : Set (List β))
        = Set.range code := by
      ext w
      simp
    have hUDS : InformationTheory.UniquelyDecodable
        ((Finset.image code Finset.univ : Finset (List β)) : Set (List β)) := by
      rw [himg]
      exact hUD
    have hne : Nonempty β := Fintype.card_pos_iff.mp (by omega)
    have hK := @InformationTheory.kraft_mcmillan_inequality _ _ _ hne hUDS
    rw [Finset.sum_image (fun x _ y _ hxy => hPF.injective hxy)] at hK
    simpa [div_pow, one_pow, hlen] using hK

/-- All words of length `n` over `β`, as a finset. -/
private def words (β : Type*) [Fintype β] [DecidableEq β] : ℕ → Finset (List β)
  | 0 => {[]}
  | n + 1 => Finset.univ.biUnion fun b => (words β n).image fun tl => b :: tl

/-- Membership in `words` is exactly the length condition. -/
private theorem mem_words {β : Type*} [Fintype β] [DecidableEq β] (n : ℕ)
    (w : List β) : w ∈ words β n ↔ w.length = n := by
  induction n generalizing w with
  | zero =>
    rw [show words β 0 = {[]} from rfl]
    constructor
    · intro hmem
      rw [Finset.mem_singleton] at hmem
      simp [hmem]
    · intro hlen
      have heq : w = [] := by
        cases w with
        | nil => rfl
        | cons _ _ => simp at hlen
      rw [heq]
      simp
  | succ n ih =>
    have hU : words β (n + 1)
        = Finset.univ.biUnion (fun b => (words β n).image fun tl => b :: tl) := rfl
    rw [hU]
    constructor
    · intro hmem
      rw [Finset.mem_biUnion] at hmem
      obtain ⟨b, _, himg⟩ := hmem
      obtain ⟨tl, htl, rfl⟩ := Finset.mem_image.mp himg
      have htl_len : tl.length = n := (ih tl).mp htl
      simp [htl_len]
    · intro hlen
      rw [Finset.mem_biUnion]
      cases w with
      | nil => simp at hlen
      | cons b tl =>
        refine ⟨b, Finset.mem_univ b, ?_⟩
        rw [Finset.mem_image]
        refine ⟨tl, (ih tl).mpr ?_, rfl⟩
        simp only [List.length_cons] at hlen ⊢
        omega

/-- There are `(card β) ^ n` words of length `n`. -/
private theorem card_words {β : Type*} [Fintype β] [DecidableEq β] (n : ℕ) :
    (words β n).card = Fintype.card β ^ n := by
  induction n with
  | zero => rw [show words β 0 = {[]} from rfl]; simp
  | succ n ih =>
    have hU : words β (n + 1)
        = Finset.univ.biUnion (fun b => (words β n).image fun tl => b :: tl) := rfl
    have hdisj : ((Finset.univ : Finset β) : Set β).PairwiseDisjoint
        (fun b => (words β n).image fun tl => b :: tl) := by
      intro b₁ _ b₂ _ hne
      apply Finset.disjoint_left.mpr
      rintro w hw₁ hw₂
      rw [Finset.mem_image] at hw₁ hw₂
      obtain ⟨t₁, _, heq₁⟩ := hw₁
      obtain ⟨t₂, _, heq₂⟩ := hw₂
      have heq : b₁ :: t₁ = b₂ :: t₂ := heq₁.trans heq₂.symm
      exact hne (List.cons_eq_cons.mp heq).1
    have hinj : ∀ b : β, Function.Injective (fun tl : List β => b :: tl) := by
      intro b x y hxy
      exact (List.cons_eq_cons.mp hxy).2
    rw [hU, Finset.card_biUnion hdisj]
    have himg : ∀ b ∈ (Finset.univ : Finset β),
        ((words β n).image fun tl => b :: tl).card = (words β n).card := by
      intro b _
      exact Finset.card_image_of_injective _ (hinj b)
    rw [Finset.sum_congr rfl (fun b hb => himg b hb), ih]
    simp [Finset.sum_const, Finset.card_univ, pow_succ']

/-- Extensions of chosen codewords cover few length-`n` words: the extensions of
each codeword `code b` form a fiber of size `(card β) ^ (n - length)`. -/
private theorem card_blocked_le {α β : Type*} [Fintype β]
    [DecidableEq β] (n : ℕ) (code : α → List β) (S : Finset α)
    (hle : ∀ b ∈ S, (code b).length ≤ n) :
    ((words β n).filter fun w => ∃ b ∈ S, code b <+: w).card
      ≤ ∑ b ∈ S, Fintype.card β ^ (n - (code b).length) := by
  classical
  induction S using Finset.induction with
  | empty =>
    simp
  | insert a R hna ih =>
    have hleS : ∀ b ∈ R, (code b).length ≤ n :=
      fun b hb => hle b (Finset.mem_insert_of_mem hb)
    have hle_a : (code a).length ≤ n := hle a (Finset.mem_insert_self a R)
    have hfib : ((words β n).filter fun w => code a <+: w).card
        ≤ Fintype.card β ^ (n - (code a).length) := by
      have heq : (words β n).filter (fun w => code a <+: w)
          = ((words β (n - (code a).length)).image fun t => code a ++ t) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_image, mem_words]
        constructor
        · rintro ⟨hlen, hpre⟩
          obtain ⟨t, ht⟩ := hpre
          refine ⟨t, ?_, ht⟩
          have e : (code a ++ t).length = n := by rw [ht]; exact hlen
          rw [List.length_append] at e
          omega
        · rintro ⟨t, htlen, rfl⟩
          refine ⟨?_, t, rfl⟩
          simp [List.length_append, htlen, Nat.add_sub_cancel' hle_a]
      rw [heq]
      calc ((words β (n - (code a).length)).image fun t => code a ++ t).card
          ≤ (words β (n - (code a).length)).card := Finset.card_image_le
        _ = Fintype.card β ^ (n - (code a).length) := card_words _
    have hsub : (words β n).filter (fun w => ∃ b ∈ insert a R, code b <+: w)
        ⊆ (words β n).filter (fun w => code a <+: w)
          ∪ (words β n).filter (fun w => ∃ b ∈ R, code b <+: w) := by
      intro w hw
      rw [Finset.mem_filter] at hw
      obtain ⟨hmem, b, hb, hpre⟩ := hw
      rw [Finset.mem_insert] at hb
      rcases hb with rfl | hbR
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmem, hpre⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmem, b, hbR, hpre⟩)
    have hcard :=
      (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hih := ih hleS
    rw [Finset.sum_insert hna]
    omega

/-- The real Kraft hypothesis yields an integer budget: symbols of length at
most `n` already chosen leave room for one more word of length `n`. -/
private theorem nat_blocked_bound {α β : Type*} [Fintype α] [Fintype β]
    (l : α → ℕ)
    (hK : ∑ b : α, (1 : ℝ) / (Fintype.card β : ℝ) ^ (l b) ≤ 1)
    (hq : 2 ≤ Fintype.card β) (S : Finset α) (a : α) (n : ℕ) (hna : a ∉ S)
    (hle : ∀ b ∈ S, l b ≤ n) (hla : l a = n) :
    ∑ b ∈ S, Fintype.card β ^ (n - l b) ≤ Fintype.card β ^ n - 1 := by
  classical
  have hDpos : 0 < Fintype.card β := by omega
  have hDR : (0 : ℝ) < (Fintype.card β : ℝ) := by exact_mod_cast hDpos
  have hleT : ∀ b ∈ insert a S, l b ≤ n := by
    intro b hb
    rw [Finset.mem_insert] at hb
    rcases hb with rfl | hmem
    · omega
    · exact hle b hmem
  have hsub : ∑ b ∈ insert a S, (1 : ℝ) / (Fintype.card β : ℝ) ^ (l b) ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun b _ _ => div_nonneg zero_le_one (pow_nonneg (by positivity) _))).trans hK
  have hsplit : ∀ b ∈ insert a S, (Fintype.card β : ℝ) ^ n
      = (Fintype.card β : ℝ) ^ (l b) * (Fintype.card β : ℝ) ^ (n - l b) := by
    intro b hb
    conv_lhs => rw [← Nat.add_sub_cancel' (hleT b hb), pow_add]
  have hterm : ∀ b ∈ insert a S, (Fintype.card β : ℝ) ^ n
      * (1 / (Fintype.card β : ℝ) ^ (l b)) = (Fintype.card β : ℝ) ^ (n - l b) := by
    intro b hb
    have hDne : (Fintype.card β : ℝ) ^ (l b) ≠ 0 :=
      pow_ne_zero _ (ne_of_gt hDR)
    have hcancel : (Fintype.card β : ℝ) ^ (l b)
        * ((Fintype.card β : ℝ) ^ (l b))⁻¹ = 1 := mul_inv_cancel₀ hDne
    calc (Fintype.card β : ℝ) ^ n * (1 / (Fintype.card β : ℝ) ^ (l b))
        = (Fintype.card β : ℝ) ^ (n - l b) *
          ((Fintype.card β : ℝ) ^ (l b) * ((Fintype.card β : ℝ) ^ (l b))⁻¹) := by
          rw [hsplit b hb, div_eq_mul_inv, one_mul, mul_assoc,
            mul_left_comm ((Fintype.card β : ℝ) ^ (l b))]
      _ = (Fintype.card β : ℝ) ^ (n - l b) := by rw [hcancel, mul_one]
  have hmul : (Fintype.card β : ℝ) ^ n
      * (∑ b ∈ insert a S, 1 / (Fintype.card β : ℝ) ^ (l b))
      = ∑ b ∈ insert a S, (Fintype.card β : ℝ) ^ (n - l b) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b hb => hterm b hb)
  have hfin : ∑ b ∈ insert a S, (Fintype.card β : ℝ) ^ (n - l b)
      ≤ (Fintype.card β : ℝ) ^ n := by
    calc ∑ b ∈ insert a S, (Fintype.card β : ℝ) ^ (n - l b)
        = (Fintype.card β : ℝ) ^ n
          * (∑ b ∈ insert a S, 1 / (Fintype.card β : ℝ) ^ (l b)) := hmul.symm
      _ ≤ (Fintype.card β : ℝ) ^ n * 1 :=
          mul_le_mul_of_nonneg_left hsub (pow_nonneg hDR.le _)
      _ = (Fintype.card β : ℝ) ^ n := mul_one _
  rw [Finset.sum_insert hna] at hfin
  have ha0 : n - l a = 0 := by omega
  rw [ha0, pow_zero, add_comm (1 : ℝ)] at hfin
  have hNat : (∑ b ∈ S, Fintype.card β ^ (n - l b)) + 1
      ≤ Fintype.card β ^ n := by
    have h2 : ((∑ b ∈ S, Fintype.card β ^ (n - l b)) + 1 : ℕ) ≤ Fintype.card β ^ n := by
      exact_mod_cast hfin
    omega
  omega

/-- Converse direction: the Kraft bound lets us greedily realize the lengths by
a prefix-free code. Symbols are handled length by length; at each step the
integer budget leaves a length-`n` word outside all previously blocked
extensions. -/
private theorem backward {α β : Type*} [Fintype α] [Fintype β]
    (l : α → ℕ)
    (hK : ∑ b : α, (1 : ℝ) / (Fintype.card β : ℝ) ^ (l b) ≤ 1)
    (hq : 2 ≤ Fintype.card β) :
    ∃ code : α → List β, IsPrefixFree code ∧ ∀ a, (code a).length = l a := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ a : α, l a < N := by
    refine ⟨∑ a ∈ Finset.univ, (l a + 1), fun a => ?_⟩
    have hle : l a + 1 ≤ ∑ b ∈ Finset.univ, (l b + 1) :=
      Finset.single_le_sum (s := Finset.univ) (f := fun b => l b + 1)
        (fun x _ => Nat.zero_le _) (Finset.mem_univ a)
    omega
  suffices stage : ∀ n : ℕ, ∃ code : α → List β,
      (∀ b : α, l b < n → (code b).length = l b) ∧
        (∀ b₁ b₂ : α, l b₁ < n → l b₂ < n → b₁ ≠ b₂ → ¬ code b₁ <+: code b₂) by
    obtain ⟨code, hlen, hpf⟩ := stage N
    refine ⟨code, ?_, fun a => hlen a (hN a)⟩
    intro a₁ a₂ hne hpre
    exact hpf a₁ a₂ (hN a₁) (hN a₂) hne hpre
  intro n
  induction n with
  | zero =>
    exact ⟨fun _ => [],
      fun b hb => absurd hb (Nat.not_lt_zero _),
      fun b₁ _ h₁ _ _ _ => absurd h₁ (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨code₀, hlen₀, hpf₀⟩ := ih
    have step : ∀ F : Finset α, F ⊆ Finset.univ.filter (fun b => l b = n) →
        ∃ code : α → List β,
          (∀ b ∈ Finset.univ.filter (fun b => l b < n) ∪ F, (code b).length = l b) ∧
            (∀ b₁ ∈ Finset.univ.filter (fun b => l b < n) ∪ F,
              ∀ b₂ ∈ Finset.univ.filter (fun b => l b < n) ∪ F,
                b₁ ≠ b₂ → ¬ code b₁ <+: code b₂) ∧
            (∀ b ∈ Finset.univ.filter (fun b => l b < n), code b = code₀ b) := by
      intro F
      induction F using Finset.induction with
      | empty =>
        intro _
        refine ⟨code₀, ?_, ?_, fun b _ => rfl⟩
        · intro b hb
          rw [Finset.mem_union] at hb
          rcases hb with hb | hb
          · exact hlen₀ b (Finset.mem_filter.mp hb).2
          · exact absurd hb (Finset.notMem_empty _)
        · intro b₁ hb₁ b₂ hb₂ hne hpre
          rw [Finset.mem_union] at hb₁ hb₂
          rcases hb₁ with hb₁ | hb₁
          · rcases hb₂ with hb₂ | hb₂
            · exact hpf₀ b₁ b₂ (Finset.mem_filter.mp hb₁).2
                (Finset.mem_filter.mp hb₂).2 hne hpre
            · exact absurd hb₂ (Finset.notMem_empty _)
          · exact absurd hb₁ (Finset.notMem_empty _)
      | insert a R hna ihR =>
        intro hsub
        have hsubR : R ⊆ Finset.univ.filter (fun b => l b = n) := by
          intro x hx
          exact hsub (Finset.mem_insert_of_mem hx)
        obtain ⟨codeS, hlenS, hpfS, heqS⟩ := ihR hsubR
        have hla : l a = n :=
          (Finset.mem_filter.mp (hsub (Finset.mem_insert_self a R))).2
        set Sprev := Finset.univ.filter (fun b => l b < n) ∪ R with hSprev
        have haS : a ∉ Sprev := by
          intro hcon
          rw [hSprev, Finset.mem_union, Finset.mem_filter] at hcon
          rcases hcon with ⟨hlt, _⟩ | hmem
          · simp at hlt
            omega
          · exact hna hmem
        have hlen_le : ∀ b ∈ Sprev, l b ≤ n := by
          intro b hb
          rw [hSprev, Finset.mem_union] at hb
          rcases hb with hb | hb
          · have hlt : l b < n := (Finset.mem_filter.mp hb).2
            omega
          · have heq : l b = n := (Finset.mem_filter.mp (hsubR hb)).2
            omega
        have hcode_le : ∀ b ∈ Sprev, (codeS b).length ≤ n := by
          intro b hb
          rw [hlenS b hb]
          exact hlen_le b hb
        have hcode_eq : ∀ b ∈ Sprev, (codeS b).length = l b :=
          fun b hb => hlenS b hb
        have hblocked := card_blocked_le n codeS Sprev hcode_le
        have hsum_eq : ∑ b ∈ Sprev, Fintype.card β ^ (n - (codeS b).length)
            = ∑ b ∈ Sprev, Fintype.card β ^ (n - l b) :=
          Finset.sum_congr rfl (fun b hb => by rw [hcode_eq b hb])
        have hbudget := nat_blocked_bound l hK hq Sprev a n haS hlen_le hla
        have hroom : ((words β n).filter
            fun w => ∃ b ∈ Sprev, codeS b <+: w).card < (words β n).card := by
          rw [card_words]
          calc ((words β n).filter fun w => ∃ b ∈ Sprev, codeS b <+: w).card
              ≤ ∑ b ∈ Sprev, Fintype.card β ^ (n - l b) := by
                rw [← hsum_eq]
                exact hblocked
            _ ≤ Fintype.card β ^ n - 1 := hbudget
            _ < Fintype.card β ^ n := by
                have hpos : 0 < Fintype.card β ^ n := pow_pos (by omega) n
                omega
        obtain ⟨w, hwmem, hwnot⟩ := Finset.exists_of_ssubset
          (Finset.ssubset_iff_subset_ne.mpr
            ⟨Finset.filter_subset _ _,
              fun heq => by rw [heq] at hroom; exact lt_irrefl _ hroom⟩)
        have hw_len : w.length = n := (mem_words n w).mp hwmem
        have hnot : ¬ ∃ b ∈ Sprev, codeS b <+: w := fun hex =>
          hwnot (Finset.mem_filter.mpr ⟨hwmem, hex⟩)
        have hunion : Finset.univ.filter (fun b => l b < n) ∪ insert a R
            = insert a Sprev := by
          ext x
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_insert,
            Finset.mem_univ, true_and, hSprev]
          tauto
        refine ⟨Function.update codeS a w, ?_, ?_, ?_⟩
        · intro b hb
          rw [hunion, Finset.mem_insert] at hb
          rcases hb with rfl | hmem
          · rw [Function.update_self, hw_len, hla]
          · have hne : b ≠ a := fun heq => haS (heq ▸ hmem)
            rw [Function.update_of_ne hne]
            exact hlenS b hmem
        · intro b₁ hb₁ b₂ hb₂ hne hpre
          rw [hunion, Finset.mem_insert] at hb₁ hb₂
          have ho1 : b₁ = a ∨ b₁ ∈ Sprev := by simpa using hb₁
          have ho2 : b₂ = a ∨ b₂ ∈ Sprev := by simpa using hb₂
          rcases ho1 with heq1 | hm1
          · rcases ho2 with heq2 | hm2
            · exact absurd (heq1.trans heq2.symm) hne
            · have hne2 : b₂ ≠ a := fun heq => haS (heq ▸ hm2)
              rw [heq1, Function.update_self, Function.update_of_ne hne2] at hpre
              obtain ⟨t, ht⟩ := hpre
              have htl : t.length = 0 := by
                have e : (w ++ t).length = n + t.length := by
                  simp [List.length_append, hw_len]
                rw [ht, hcode_eq b₂ hm2] at e
                have hle2 := hlen_le b₂ hm2
                omega
              have htnil : t = [] := List.length_eq_zero_iff.mp htl
              have hweq : codeS b₂ = w := by rw [← ht, htnil, List.append_nil]
              exact hnot ⟨b₂, hm2, ⟨[], by rw [List.append_nil]; exact hweq⟩⟩
          · rcases ho2 with heq2 | hm2
            · have hne1 : b₁ ≠ a := fun heq => haS (heq ▸ hm1)
              rw [Function.update_of_ne hne1, heq2, Function.update_self] at hpre
              exact hnot ⟨b₁, hm1, hpre⟩
            · have hne1 : b₁ ≠ a := fun heq => haS (heq ▸ hm1)
              have hne2 : b₂ ≠ a := fun heq => haS (heq ▸ hm2)
              rw [Function.update_of_ne hne1, Function.update_of_ne hne2] at hpre
              exact hpfS b₁ hm1 b₂ hm2 hne hpre
        · intro b hb
          have hblt : l b < n := (Finset.mem_filter.mp hb).2
          have hne : b ≠ a := by
            intro heq
            rw [heq, hla] at hblt
            exact absurd hblt (lt_irrefl _)
          rw [Function.update_of_ne hne]
          exact heqS b hb
    have hE : Finset.univ.filter (fun b => l b < n + 1)
        = Finset.univ.filter (fun b => l b < n)
          ∪ Finset.univ.filter (fun b => l b = n) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
      omega
    obtain ⟨codeN, hlenN, hpfN, _⟩ :=
      step (Finset.univ.filter fun b => l b = n) le_rfl
    refine ⟨codeN, fun b hb => ?_, fun b₁ b₂ h₁ h₂ hne hpre => ?_⟩
    · have hbU : b ∈ Finset.univ.filter (fun b => l b < n + 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩
      rw [hE] at hbU
      exact hlenN b hbU
    · have hb1U : b₁ ∈ Finset.univ.filter (fun b => l b < n + 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ b₁, h₁⟩
      have hb2U : b₂ ∈ Finset.univ.filter (fun b => l b < n + 1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ b₂, h₂⟩
      rw [hE] at hb1U hb2U
      exact hpfN b₁ hb1U b₂ hb2U hne hpre

/-- **Kraft's inequality for prefix codes.** Let $\alpha$ be a finite set of source symbols,
let $\beta$ be a finite alphabet with $D \ge 2$ letters, and let $l : \alpha \to \mathbb{N}$.
There is a prefix-free code assigning to each $a \in \alpha$ a word over $\beta$ of length
$l(a)$ if and only if $\sum_{a \in \alpha} D^{-l(a)} \le 1$. -/
public theorem kraft_mcmillan_lengths {α β : Type*} [Fintype α] [Fintype β]
    (l : α → ℕ) (hq : 2 ≤ Fintype.card β) :
    (∃ code : α → List β, IsPrefixFree code ∧ ∀ a, (code a).length = l a)
      ↔ ∑ a : α, (1 : ℝ) / (Fintype.card β : ℝ) ^ (l a) ≤ 1 := by
  constructor
  · rintro ⟨code, hPF, hlen⟩
    exact forward l code hPF hlen hq
  · intro hK
    obtain ⟨code, hPF, hlen⟩ := backward l hK hq
    exact ⟨code, hPF, hlen⟩

end MathlibExt.InformationTheory.KraftMcMillan
