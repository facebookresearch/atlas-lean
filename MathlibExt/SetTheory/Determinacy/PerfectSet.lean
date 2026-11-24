/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.SetTheory.Determinacy.GaleStewart
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Perfect

/-!
# Davis's perfect set theorem from determinacy

We prove the perfect set property for determinacy families on Baire space that are closed under
Borel preimages. In the splitting game, player I offers two distinct extensions of equal length
and player II selects one. A winning strategy for I gives a Cantor space of outcomes, while a
winning strategy for II can block at most one outcome at each finite history.
-/

open Set Filter
open scoped Topology
open MathlibExt.SetTheory.Determinacy

namespace MathlibExt.SetTheory.DeterminacyWanted

/-- An offer consists of two distinct words of equal length, hence both are nonempty. -/
private abbrev Offer :=
  {w : List ℕ × List ℕ // w.1.length = w.2.length ∧ w.1 ≠ w.2}

private def decodeOffer (a : ℕ) : Offer :=
  (Encodable.decode a).getD ⟨([0], [1]), by decide⟩

private theorem decodeOffer_encode (w : Offer) : decodeOffer (Encodable.encode w) = w := by
  simp [decodeOffer, Encodable.encodek]

/-- Player II selects one of the offered words by the parity of the response. -/
private def selectedWord (a b : ℕ) : List ℕ :=
  if b % 2 = 0 then (decodeOffer a).val.1 else (decodeOffer a).val.2

private theorem selectedWord_length_pos (a b : ℕ) : 0 < (selectedWord a b).length := by
  unfold selectedWord
  generalize decodeOffer a = w
  obtain ⟨⟨u, v⟩, hlen, hne⟩ := w
  change u.length = v.length at hlen
  change u ≠ v at hne
  have hu : 0 < u.length := by
    by_contra! h
    exact hne ((List.eq_nil_of_length_eq_zero (by omega)).trans
      (List.eq_nil_of_length_eq_zero (by omega)).symm)
  split <;> simp_all

/-- The concatenation of the words selected in the first `n` rounds. -/
private def roundPrefix (x : ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => roundPrefix x n ++ selectedWord (x (2 * n)) (x (2 * n + 1))

private theorem roundPrefix_mono (x : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) :
    roundPrefix x m <+: roundPrefix x n := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | step _ ih => exact ih.trans (List.prefix_append _ _)

private theorem le_length_roundPrefix (x : ℕ → ℕ) (n : ℕ) : n ≤ (roundPrefix x n).length := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    simp only [roundPrefix, List.length_append]
    have := selectedWord_length_pos (x (2 * n)) (x (2 * n + 1))
    omega

private theorem roundPrefix_congr {x y : ℕ → ℕ} {n : ℕ} (h : ∀ j < 2 * n, x j = y j) :
    roundPrefix x n = roundPrefix y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [roundPrefix, roundPrefix, ih (fun j hj => h j (by omega)),
      h (2 * n) (by omega), h (2 * n + 1) (by omega)]

/-- The infinite outcome obtained by concatenating the selected words. -/
private def outcome (x : ℕ → ℕ) (i : ℕ) : ℕ :=
  (roundPrefix x (i + 1))[i]'(le_length_roundPrefix x (i + 1))

/-- A real matches a word if the word is an initial segment of it. -/
private def Matches (p : List ℕ) (x : ℕ → ℕ) : Prop :=
  ∀ i (hi : i < p.length), p[i] = x i

private theorem outcome_matches (x : ℕ → ℕ) (n : ℕ) : Matches (roundPrefix x n) (outcome x) := by
  intro i hi
  exact ((roundPrefix_mono x (le_max_left n (i + 1))).getElem hi).trans
    ((roundPrefix_mono x (le_max_right n (i + 1))).getElem
      (le_length_roundPrefix x (i + 1))).symm

private theorem eq_of_matches {p q : List ℕ} {x : ℕ → ℕ} (hl : p.length = q.length)
    (hp : Matches p x) (hq : Matches q x) : p = q :=
  List.ext_getElem hl fun i hi hj => (hp i hi).trans (hq i hj).symm

private theorem continuous_of_prefix {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    {f : (ℕ → A) → ℕ → ℕ}
    (h : ∀ i, ∃ n, ∀ x y, (∀ j < n, x j = y j) → f x i = f y i) :
    Continuous f := by
  apply continuous_pi
  intro i
  obtain ⟨n, hn⟩ := h i
  refine continuous_iff_continuousAt.mpr fun x => (continuousAt_const (y := f x i)).congr ?_
  filter_upwards [(PiNat.isOpen_cylinder (fun _ => A) x n).mem_nhds
    (PiNat.self_mem_cylinder x n)]
    with y hy
  exact (hn y x (PiNat.mem_cylinder_iff.mp hy)).symm

private theorem continuous_outcome : Continuous outcome := by
  apply continuous_of_prefix
  intro i
  refine ⟨2 * (i + 1), fun x y h => ?_⟩
  simpa only [outcome, List.getElem?_eq_getElem (le_length_roundPrefix x (i + 1)),
    List.getElem?_eq_getElem (le_length_roundPrefix y (i + 1)), Option.getD_some] using
    congrArg (fun l : List ℕ => l[i]?.getD 0) (roundPrefix_congr h)

private theorem selectedWord_length_eq (a b c : ℕ) :
    (selectedWord a b).length = (selectedWord a c).length := by
  simp only [selectedWord]
  split <;> split
  · rfl
  · exact (decodeOffer a).property.1
  · exact (decodeOffer a).property.1.symm
  · rfl

private theorem selectedWord_toNat_injective (a : ℕ) :
    Function.Injective (fun b : Bool => selectedWord a b.toNat) := by
  have hne := (decodeOffer a).property.2
  intro b c h
  cases b <;> cases c <;> simp_all [selectedWord, Ne.symm hne]

/-- A play against `σ` in which player II follows the given sequence of bits. -/
private noncomputable def binaryPlay (σ : List ℕ → ℕ) (b : ℕ → Bool) : ℕ → ℕ :=
  play σ fun p => (b (p.length / 2)).toNat

private theorem binaryPlay_odd (σ : List ℕ → ℕ) (b : ℕ → Bool) (n : ℕ) :
    binaryPlay σ b (2 * n + 1) = (b n).toNat := by
  simpa only [binaryPlay, length_history, show (2 * n + 1) / 2 = n by omega] using
    followsII_play σ (fun p => (b (p.length / 2)).toNat) (2 * n + 1) (by omega)

private theorem binaryPlay_even_eq (σ : List ℕ → ℕ) {b c : ℕ → Bool} {n : ℕ}
    (h : ∀ j < n, binaryPlay σ b j = binaryPlay σ c j) (hn : n % 2 = 0) :
    binaryPlay σ b n = binaryPlay σ c n := by
  calc
    binaryPlay σ b n = σ (history (binaryPlay σ b) n) := followsI_play σ _ n hn
    _ = σ (history (binaryPlay σ c) n) := congrArg σ (history_eq_history_iff.mpr h)
    _ = binaryPlay σ c n := (followsI_play σ _ n hn).symm

private theorem binaryPlay_agree (σ : List ℕ → ℕ) {b c : ℕ → Bool} {n : ℕ}
    (h : ∀ j < n, b j = c j) :
    ∀ i < 2 * n, binaryPlay σ b i = binaryPlay σ c i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases he : i % 2 = 0
    · exact binaryPlay_even_eq σ (fun j hj => ih j hj (hj.trans hi)) he
    · have hi' : i = 2 * (i / 2) + 1 := by omega
      have hb := h (i / 2) (by omega)
      conv_lhs => rw [hi', binaryPlay_odd]
      conv_rhs => rw [hi', binaryPlay_odd]
      rw [hb]

private theorem continuous_binaryPlay (σ : List ℕ → ℕ) : Continuous (binaryPlay σ) := by
  apply continuous_of_prefix
  intro i
  exact ⟨i + 1, fun _ _ h => binaryPlay_agree σ h i (by omega)⟩

private theorem binaryOutcome_injective (σ : List ℕ → ℕ) :
    Function.Injective (outcome ∘ binaryPlay σ) := by
  intro b c he
  funext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have hplay := binaryPlay_agree σ ih
    have hprefix := roundPrefix_congr hplay
    have heven := binaryPlay_even_eq σ hplay (show (2 * n) % 2 = 0 by omega)
    have h₁ := outcome_matches (binaryPlay σ b) (n + 1)
    have h₂ := outcome_matches (binaryPlay σ c) (n + 1)
    change outcome (binaryPlay σ b) = outcome (binaryPlay σ c) at he
    rw [← he, roundPrefix, ← hprefix, ← heven, binaryPlay_odd] at h₂
    rw [roundPrefix, binaryPlay_odd] at h₁
    have hw := eq_of_matches (by simp only [List.length_append,
      selectedWord_length_eq (binaryPlay σ b (2 * n)) (b n).toNat (c n).toNat]) h₁ h₂
    exact selectedWord_toNat_injective _ (List.append_cancel_left hw)

private theorem perfect_range {f : (ℕ → Bool) → ℕ → ℕ} (hf : Continuous f)
    (hinj : Function.Injective f) : Perfect (range f) := by
  refine ⟨(isCompact_range hf).isClosed, preperfect_iff_nhds.mpr ?_⟩
  rintro _ ⟨b, rfl⟩ U hU
  have hmem : f ⁻¹' U ∈ 𝓝 b := hf.continuousAt.preimage_mem_nhds hU
  obtain ⟨V, hVU, hV, hbV⟩ := mem_nhds_iff.mp hmem
  obtain ⟨W, ⟨c, n, rfl⟩, hbW, hWV⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ => Bool)).exists_subset_of_mem_open hbV hV
  let d := Function.update b n (!(b n))
  have hdW : d ∈ PiNat.cylinder c n := PiNat.mem_cylinder_iff.mpr fun i hi => by
    dsimp only [d]
    rw [Function.update_of_ne (ne_of_lt hi)]
    exact PiNat.mem_cylinder_iff.mp hbW i hi
  refine ⟨f d, ⟨hVU (hWV hdW), mem_range_self d⟩, fun h => ?_⟩
  have hd := congrFun (hinj h) n
  simp only [d, Function.update_self] at hd
  cases hb : b n <;> simp [hb] at hd

private theorem exists_perfect_of_iWins {S : Set (ℕ → ℕ)} (h : IWins (outcome ⁻¹' S)) :
    ∃ P ⊆ S, P.Nonempty ∧ Perfect P := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨range (outcome ∘ binaryPlay σ),
    fun _ ⟨b, hb⟩ => hb ▸ hσ (binaryPlay σ b) (followsI_play σ _),
    range_nonempty _, perfect_range (continuous_outcome.comp (continuous_binaryPlay σ))
      (binaryOutcome_injective σ)⟩

/-- The prefix produced by the completed rounds in a finite history. -/
private def positionPrefix (p : List ℕ) : List ℕ :=
  roundPrefix (fun i => p[i]?.getD 0) (p.length / 2)

private theorem positionPrefix_history (x : ℕ → ℕ) (n : ℕ) :
    positionPrefix (history x (2 * n)) = roundPrefix x n := by
  rw [positionPrefix, length_history, show 2 * n / 2 = n by omega]
  exact roundPrefix_congr fun i hi => by simp [getElem?_history hi]

private def nextPrefix (τ : List ℕ → ℕ) (p : List ℕ) (a : ℕ) : List ℕ :=
  positionPrefix p ++ selectedWord a (τ (p ++ [a]))

/-- A real is blocked at a history if it extends the current prefix but none of the
extensions that player II would select after an offer. -/
private def blocked (τ : List ℕ → ℕ) (p : List ℕ) : Set (ℕ → ℕ) :=
  {x | Matches (positionPrefix p) x ∧ ∀ a, ¬Matches (nextPrefix τ p a) x}

private theorem exists_matching_append {p : List ℕ} {x : ℕ → ℕ} (hp : Matches p x)
    (k : ℕ) : ∃ w : List ℕ, w.length = k ∧ Matches (p ++ w) x := by
  let w := List.ofFn fun i : Fin k => x (p.length + i)
  refine ⟨w, by simp [w], fun i hi => ?_⟩
  by_cases h : i < p.length
  · exact (List.getElem_append_left h).trans (hp i h)
  · rw [List.getElem_append_right (by omega)]
    simp only [w, List.getElem_ofFn, Nat.add_sub_of_le (by omega : p.length ≤ i)]

private theorem blocked_subsingleton (τ : List ℕ → ℕ) (p : List ℕ) :
    (blocked τ p).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra! h
    exact hxy (funext h)
  let q := positionPrefix p
  have hlen : q.length ≤ i := by
    by_contra! h
    exact hi ((hx.1 i h).symm.trans (hy.1 i h))
  obtain ⟨u, hu, hxu⟩ := exists_matching_append hx.1 (i + 1 - q.length)
  obtain ⟨v, hv, hyv⟩ := exists_matching_append hy.1 (i + 1 - q.length)
  have hne : u ≠ v := by
    intro he
    subst v
    have hlt : i < (q ++ u).length := by simp only [List.length_append, hu]; omega
    exact hi ((hxu i hlt).symm.trans (hyv i hlt))
  let w : Offer := ⟨(u, v), hu.trans hv.symm, hne⟩
  let a := Encodable.encode w
  by_cases h : τ (p ++ [a]) % 2 = 0
  · exact hx.2 a (by simpa [nextPrefix, selectedWord, h, a, w, decodeOffer_encode] using hxu)
  · exact hy.2 a (by simpa [nextPrefix, selectedWord, h, a, w, decodeOffer_encode] using hyv)

private theorem countable_of_iiWins {S : Set (ℕ → ℕ)} (h : IIWins (outcome ⁻¹' S)) :
    S.Countable := by
  classical
  obtain ⟨τ, hτ⟩ := h
  refine (countable_iUnion fun p => (blocked_subsingleton τ p).countable).mono ?_
  intro x hx
  by_contra hnot
  have hmove (p : List ℕ) (hp : Matches (positionPrefix p) x) :
      ∃ a, Matches (nextPrefix τ p a) x := by
    by_contra! h
    exact hnot (mem_iUnion.mpr ⟨p, hp, h⟩)
  -- If no position blocks `x`, player I can keep selecting offers with a reply along `x`.
  let σ : List ℕ → ℕ := fun p =>
    if h : ∃ a, Matches (nextPrefix τ p a) x then h.choose else 0
  let y := play σ τ
  have hmatch (n : ℕ) : Matches (roundPrefix y n) x := by
    induction n with
    | zero => simp [Matches, roundPrefix]
    | succ n ih =>
      let p := history y (2 * n)
      have hp : positionPrefix p = roundPrefix y n := positionPrefix_history y n
      have hm := hmove p (hp ▸ ih)
      have hy₀ : y (2 * n) = σ p := followsI_play σ τ (2 * n) (by omega)
      have hy₁ : y (2 * n + 1) = τ (p ++ [σ p]) := by
        have h : y (2 * n + 1) = τ (history y (2 * n + 1)) :=
          followsII_play σ τ (2 * n + 1) (by omega)
        rw [h, history_succ, hy₀]
      rw [roundPrefix, hy₀, hy₁, ← hp]
      change Matches (nextPrefix τ p (σ p)) x
      simpa only [σ, dite_eq_left hm] using hm.choose_spec
  apply hτ y (followsII_play σ τ)
  change outcome y ∈ S
  suffices outcome y = x by rwa [this]
  funext i
  exact (hmatch (i + 1)) i (le_length_roundPrefix y (i + 1))

/-- **Davis's perfect set theorem from determinacy.** Let `Γ` be a family of subsets of Baire
space `ℕ^ℕ`, closed under preimages by Borel maps `ℕ^ℕ → ℕ^ℕ`, all of whose members are
determined. Then every member of `Γ` is countable or contains a non-empty perfect set
(M. Davis, *Infinite games of perfect information*, Ann. of Math. Stud. 52 (1964); Moschovakis,
*Descriptive Set Theory*, 2nd ed., AMS 2009, 6A.10–6A.12; Woodin, *The continuum hypothesis,
Part I*, Notices AMS 48 (2001)). -/
public theorem countable_or_exists_perfect_of_determined {Γ : Set (Set (ℕ → ℕ))}
    (hΓ : ∀ f : (ℕ → ℕ) → ℕ → ℕ, Measurable f → ∀ B ∈ Γ, f ⁻¹' B ∈ Γ)
    (hdet : ∀ B ∈ Γ, Determined B) {S : Set (ℕ → ℕ)} (hS : S ∈ Γ) :
    S.Countable ∨ ∃ P ⊆ S, P.Nonempty ∧ Perfect P := by
  rcases hdet (outcome ⁻¹' S) (hΓ outcome continuous_outcome.measurable S hS) with hI | hII
  · exact Or.inr (exists_perfect_of_iWins hI)
  · exact Or.inl (countable_of_iiWins hII)

end MathlibExt.SetTheory.DeterminacyWanted
