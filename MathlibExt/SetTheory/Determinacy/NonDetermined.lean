/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.SetTheory.Determinacy.GaleStewart
public import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.CountableCover

/-!
# A non-determined game, and the failure of the axiom of determinacy under choice

Gale and Stewart (1953) showed, using the axiom of choice, that some game on `{0, 1}` with
payoff set `S ⊆ 2^ℕ` is not determined (Moschovakis, *Descriptive Set Theory*, 2nd ed., AMS 2009,
Exercise 6A.6). The proof is a diagonalisation of length `2^ℵ₀`: there are only continuum many
strategies, each strategy has continuum many plays following it, so by transfinite recursion
along a well-ordering of the strategies one can put, for each strategy of player I, one of its
plays outside `S`, and for each strategy of player II, one of its plays inside `S`.

We prove the abstract diagonalisation (`exists_meets_and_compl_meets`) and the theorem for every
countable set of moves with at least two elements, hence for `Bool` and for `ℕ`. The latter says
that the **axiom of determinacy** AD — every `S ⊆ ℕ^ℕ` is determined — is false in Lean's ambient
logic, which includes choice; mathematically the proof uses only a well-ordering of the reals,
so in ZF it shows that AD refutes the existence of such a well-ordering. Consequently, results
"under AD" have to be stated with explicit determinacy hypotheses on specific classes of sets
(as in `WantedExt.SetTheory.Determinacy.RegularityWanted`), never with AD as a hypothesis, which
would make them vacuous.
-/

@[expose] public section

noncomputable section

open Set Cardinal

namespace MathlibExt.SetTheory.Determinacy

universe u

private theorem exists_not_mem_of_mk_lt {α : Type u} {S F : Set α} (h : #S < #F) :
    ∃ x ∈ F, x ∉ S := by
  by_contra hc
  push Not at hc
  exact (mk_le_mk_of_subset hc).not_gt h

/-- **Bernstein-type diagonalisation.** Let `κ` be an infinite cardinal and `F : ι → Set α` a
family of at most `κ` sets, each of cardinality at least `κ`. Then some `B ⊆ α` meets every
`F i`, and so does its complement. This is the transfinite construction of Moschovakis,
*Descriptive Set Theory*, 2nd ed., AMS 2009, hint to Exercise 6A.6 (sets `A_ξ`, `B_ξ` of
cardinality `< 2^ℵ₀` built along a well-ordering of the strategies), and of Bernstein's set. -/
theorem exists_meets_and_compl_meets {α ι : Type u} (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (F : ι → Set α) (hι : #ι ≤ κ) (hF : ∀ i, κ ≤ #(F i)) :
    ∃ B : Set α, ∀ i, (B ∩ F i).Nonempty ∧ (Bᶜ ∩ F i).Nonempty := by
  classical
  set idx : Type u := (#ι).ord.ToType
  have hTo : #idx = #ι := mk_ord_toType _
  obtain ⟨e⟩ := Cardinal.eq.mp hTo.symm
  have htype : (#idx).ord = Ordinal.type (fun x y : idx => x < y) := by
    rw [hTo]
    exact (Ordinal.type_toType _).symm
  have hseg : ∀ b : idx, #(Set.Iio b) < κ := fun b =>
    lt_of_lt_of_le (by simpa [hTo] using mk_Iio_lt b htype) hι
  -- the points chosen before stage `b`
  let S : ∀ b : idx, (∀ a, a < b → α × α) → Set α := fun b p =>
    Set.range (fun d : Set.Iio b => (p d.1 d.2).1) ∪ Set.range (fun d : Set.Iio b => (p d.1 d.2).2)
  have hS : ∀ b p, #(S b p) < κ := fun b p =>
    lt_of_le_of_lt ((mk_union_le _ _).trans (add_le_add mk_range_le mk_range_le))
      (add_lt_of_lt hκ (hseg b) (hseg b))
  have hfresh : ∀ (b : idx) (p : ∀ a, a < b → α × α),
      Nonempty {q : α × α // q.1 ∈ F (e.symm b) ∧ q.2 ∈ F (e.symm b) ∧ q.1 ≠ q.2 ∧
        q.1 ∉ S b p ∧ q.2 ∉ insert q.1 (S b p)} := by
    intro b p
    obtain ⟨x, hxF, hxS⟩ := exists_not_mem_of_mk_lt ((hS b p).trans_le (hF (e.symm b)))
    have hins : #(insert x (S b p) : Set α) < #(F (e.symm b)) := by
      refine lt_of_lt_of_le ?_ (hF _)
      rw [mk_insert hxS]
      exact add_lt_of_lt hκ (hS b p) (lt_of_lt_of_le one_lt_aleph0 hκ)
    obtain ⟨y, hyF, hyS⟩ := exists_not_mem_of_mk_lt hins
    refine ⟨⟨(x, y), hxF, hyF, fun h => hyS ?_, hxS, hyS⟩⟩
    simp only at h
    rw [← h]
    exact Set.mem_insert _ _
  let step : ∀ b : idx, (∀ a, a < b → α × α) → α × α := fun b p => (Classical.choice (hfresh b p)).1
  have hwf : WellFounded (fun a b : idx => a < b) := wellFounded_lt
  let pick : idx → α × α := hwf.fix step
  have good : ∀ b, (pick b).1 ∈ F (e.symm b) ∧ (pick b).2 ∈ F (e.symm b) ∧
      (pick b).1 ≠ (pick b).2 ∧ (pick b).1 ∉ S b (fun a _ => pick a) ∧
      (pick b).2 ∉ insert (pick b).1 (S b (fun a _ => pick a)) := by
    intro b
    have h : pick b = step b (fun a _ => pick a) := hwf.fix_eq step b
    rw [h]
    exact (Classical.choice (hfresh b (fun a _ => pick a))).2
  refine ⟨Set.range (fun b => (pick b).1), fun i => ?_⟩
  obtain ⟨hx, hy, hxy, -, hyS⟩ := good (e i)
  rw [Equiv.symm_apply_apply] at hx hy
  refine ⟨⟨_, ⟨e i, rfl⟩, hx⟩, ⟨_, ?_, hy⟩⟩
  rintro ⟨c, hc⟩
  rcases lt_trichotomy c (e i) with hci | rfl | hic
  · exact hyS (Set.mem_insert_of_mem _ (Or.inl ⟨⟨c, hci⟩, hc⟩))
  · exact hxy hc
  · obtain ⟨-, -, -, hcS, -⟩ := good c
    exact hcS (Or.inr ⟨⟨e i, hic⟩, hc.symm⟩)

/-- The strategy that answers with `a₁` or `a₀` according to the bit `y (n / 2)` at a history of
length `n`; distinct bit sequences give distinct plays against any fixed strategy. -/
private def bitStrategy {A : Type u} (a₀ a₁ : A) (y : ℕ → Bool) : List A → A := fun h =>
  if y (h.length / 2) then a₁ else a₀

private theorem bitStrategy_play {A : Type u} {a₀ a₁ : A} (hne : a₀ ≠ a₁) {y y' : ℕ → Bool} {n : ℕ}
    {x x' : ℕ → A} (hx : x n = bitStrategy a₀ a₁ y (history x n))
    (hx' : x' n = bitStrategy a₀ a₁ y' (history x' n)) (h : x = x') : y (n / 2) = y' (n / 2) := by
  subst h
  simp only [bitStrategy, length_history] at hx hx'
  cases hy : y (n / 2) <;> cases hy' : y' (n / 2) <;>
    simp only [hy, hy', Bool.false_eq_true, ↓reduceIte] at hx hx'
  · rfl
  · exact absurd (hx.symm.trans hx') hne
  · exact absurd (hx'.symm.trans hx) hne
  · rfl

private theorem continuum_le_mk_follows {A : Type u} {a₀ a₁ : A} (hne : a₀ ≠ a₁) (k : ℕ)
    (hk : k < 2) (σ : List A → A) : 𝔠 ≤ #{x : ℕ → A | Follows k σ x} := by
  -- the play of `σ` against the bit strategy of `y`, with `σ` moving at the turns of parity `k`
  let f : (ℕ → Bool) → {x : ℕ → A | Follows k σ x} := fun y =>
    if hk0 : k = 0 then ⟨play σ (bitStrategy a₀ a₁ y), by subst hk0; exact followsI_play _ _⟩
    else ⟨play (bitStrategy a₀ a₁ y) σ, by
      have : k = 1 := by omega
      subst this; exact followsII_play _ _⟩
  have hf : Function.Injective f := by
    intro y y' hyy
    funext j
    have hval := congrArg Subtype.val hyy
    by_cases hk0 : k = 0
    · subst hk0
      simp only [f, ↓reduceDIte] at hval
      have h1 := followsII_play σ (bitStrategy a₀ a₁ y) (2 * j + 1) (by omega)
      have h2 := followsII_play σ (bitStrategy a₀ a₁ y') (2 * j + 1) (by omega)
      have := bitStrategy_play hne h1 h2 hval
      rwa [show (2 * j + 1) / 2 = j by omega] at this
    · simp only [f, hk0, ↓reduceDIte] at hval
      have h1 := followsI_play (bitStrategy a₀ a₁ y) σ (2 * j) (by omega)
      have h2 := followsI_play (bitStrategy a₀ a₁ y') σ (2 * j) (by omega)
      have := bitStrategy_play hne h1 h2 hval
      rwa [show 2 * j / 2 = j by omega] at this
  have h2 : #(ℕ → Bool) = 𝔠 := by
    rw [← two_power_aleph0, ← mk_bool, ← mk_nat, power_def]
  have := lift_mk_le_lift_mk_of_injective hf
  simpa [h2, lift_continuum, lift_uzero] using this

private theorem mk_strategy_le {A : Type u} [Countable A] : #(List A → A) ≤ 𝔠 := by
  rw [← aleph0_power_aleph0, ← power_def]
  exact (power_le_power_right mk_le_aleph0).trans
    (power_le_power_left aleph0_ne_zero mk_le_aleph0)

/-- **Existence of a non-determined game.** If the set of moves `A` is countable and has at
least two elements, some payoff set `S ⊆ A^ℕ` is not determined. The proof diagonalises over
the continuum many strategies, each of which has continuum many plays (Gale and Stewart,
*Infinite games with perfect information*, Ann. of Math. Stud. 28 (1953); Moschovakis,
*Descriptive Set Theory*, 2nd ed., AMS 2009, Exercise 6A.6, stated there for `A = {0, 1}`).
It uses the axiom of choice, through a well-ordering of the strategies. With a single move every
set is determined (`determined_of_subsingleton`). -/
theorem exists_not_determined {A : Type u} [Countable A] [Nontrivial A] :
    ∃ S : Set (ℕ → A), ¬ Determined S := by
  obtain ⟨a₀, a₁, hne⟩ := exists_pair_ne A
  let F : (List A → A) ⊕ (List A → A) → Set (ℕ → A) := fun i =>
    Sum.elim (fun σ => {x | Follows 0 σ x}) (fun τ => {x | Follows 1 τ x}) i
  have hι : #((List A → A) ⊕ (List A → A)) ≤ 𝔠 := by
    rw [mk_sum, lift_id]
    exact (add_le_add mk_strategy_le mk_strategy_le).trans (add_eq_self aleph0_le_continuum).le
  have hF : ∀ i, 𝔠 ≤ #(F i) := by
    rintro (σ | τ)
    · exact continuum_le_mk_follows hne 0 (by norm_num) σ
    · exact continuum_le_mk_follows hne 1 (by norm_num) τ
  obtain ⟨B, hB⟩ := exists_meets_and_compl_meets 𝔠 aleph0_le_continuum F hι hF
  refine ⟨B, ?_⟩
  rintro (⟨σ, hσ⟩ | ⟨τ, hτ⟩)
  · obtain ⟨x, hxB, hxF⟩ := (hB (Sum.inl σ)).2
    exact hxB (hσ x hxF)
  · obtain ⟨x, hxB, hxF⟩ := (hB (Sum.inr τ)).1
    exact hτ x hxF hxB

/-- **A non-determined game on `{0, 1}`.** Some `S ⊆ 2^ℕ` is not determined (Gale and Stewart
1953; Moschovakis, *Descriptive Set Theory*, 2nd ed., AMS 2009, Exercise 6A.6). -/
theorem exists_not_determined_bool : ∃ S : Set (ℕ → Bool), ¬ Determined S :=
  exists_not_determined

/-- **The axiom of determinacy contradicts choice.** Not every `S ⊆ ℕ^ℕ` is determined: the
axiom of determinacy AD of Mycielski and Steinhaus is false in Lean's ambient logic, which
includes the axiom of choice (Moschovakis, *Descriptive Set Theory*, 2nd ed., AMS 2009, Exercise
6A.6; Woodin, *The continuum hypothesis, Part I*, Notices AMS 48 (2001), section
"Determinacy"). The proof only uses a well-ordering of the strategies, that is of the reals. -/
theorem not_forall_determined : ¬ ∀ S : Set (ℕ → ℕ), Determined S := by
  obtain ⟨S, hS⟩ := exists_not_determined (A := ℕ)
  exact fun h => hS (h S)

end MathlibExt.SetTheory.Determinacy
