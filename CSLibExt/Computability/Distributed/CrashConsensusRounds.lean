/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Consensus with f crash failures needs f + 1 rounds
-/
module

public import CSLibExt.Computability.Distributed.CrashConsensus

/-!
# Consensus with `f` crash failures needs `f + 1` rounds

The round lower bound for synchronous consensus with crash failures, in the model of
`CSLibExt.Computability.Distributed.CrashConsensus`: with at least `f + 2` processes, no protocol
solves consensus tolerating `f` crashes in `f` rounds or fewer.

## Proof

The bivalency proof of Aguilera and Toueg, which they model on the proof of Fischer, Lynch and
Paterson. Suppose a protocol solves consensus in `T ≤ f` rounds, `T ≥ 1` (the case `T = 0` is
`CrashProtocol.not_solves_zero`). Only crash patterns with at most one crash per round, all
before round `T`, are used; they have at most `T ≤ f` faulty processes. A partial run up to
round `k` is such a pattern whose crashes happen before round `k`; its valence is the set of
values decided by correct processes in its extensions.

* Lemma 2: every partial run up to round `T - 1` is univalent. If an extension crashing `p` in
  the last round decided otherwise than the extension without that crash, letting `p` reach one
  more correct process `c` would give a run in which `c` decides as without the crash and
  another correct process as with it.
* Lemma 3: some initial configuration is bivalent, by the chain argument of Fischer, Lynch and
  Paterson, crashing at the start the process whose input changes.
* Lemma 4: a bivalent partial run up to round `k < T - 1` has a bivalent one-round extension.
  Otherwise the extensions crashing some `p` in round `k` and reaching fewer and fewer
  processes would at some point change valence between two runs that differ only in whether one
  process `q` hears `p`; crashing `q` silently in round `k + 1` makes them indistinguishable to
  every correct process.

Lemmas 3 and 4 give a bivalent partial run up to round `T - 1`, contradicting Lemma 2.

## Main results

* `CrashPattern.Good`: crashes before round `T`, at most one per round;
  `CrashPattern.card_faulty_le`: such a pattern has at most `T` faulty processes.
* `CrashProtocol.state_congr`, `CrashProtocol.state_succ_eq`, `CrashProtocol.state_eq_of_silent`:
  what a process computes depends only on the messages delivered to it.
* `CrashProtocol.SolvesOnePerRound`, `CrashProtocol.not_solvesOnePerRound`: Aguilera and Toueg's
  Theorem 1 in their system (at most one crash per round).
* `CrashProtocol.f_add_one_le_of_solves`: the `f + 1` round lower bound when any `f` processes may
  crash, a corollary.

## References

* M. K. Aguilera, S. Toueg, *A simple bivalency proof that t-resilient consensus requires
  t + 1 rounds*, Information Processing Letters 71(3–4), 1999, 155–158: Theorem 1, Lemmas 2–4.
* M. J. Fischer, N. A. Lynch, M. S. Paterson, *Impossibility of distributed consensus with one
  faulty process*, Journal of the ACM 32(2), 1985, 374–382: Lemma 2 (the chain argument reused
  in Lemma 3).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.CrashConsensus

namespace CrashPattern

variable {G : Type*} [DecidableEq G]

/-- **Admissible crash pattern for `T` rounds.** Every crash happens in one of the rounds
`0, …, T - 1`, and at most one process crashes in each round. -/
def Good (T : ℕ) (π : CrashPattern G) : Prop :=
  (∀ j ρ D, π j = some (ρ, D) → ρ < T) ∧
    ∀ j j' ρ D D', π j = some (ρ, D) → π j' = some (ρ, D') → j = j'

/-- **Crash round.** The round in which a process crashes, `0` if it does not. -/
def crashRound (π : CrashPattern G) (j : G) : ℕ :=
  match π j with
  | some (ρ, _) => ρ
  | none => 0

omit [DecidableEq G] in
/-- **Faulty processes are those that crash.** -/
theorem mem_faulty [Fintype G] {π : CrashPattern G} {j : G} :
    j ∈ π.faulty ↔ ∃ c, π j = some c := by
  simp [faulty, Option.isSome_iff_exists]

omit [DecidableEq G] in
/-- **An admissible pattern has at most `T` faulty processes.** A pattern whose crashes happen
before round `T`, at most one per round, has at most `T` faulty processes. -/
theorem card_faulty_le [Fintype G] {T : ℕ} {π : CrashPattern G} (h : π.Good T) :
    π.faulty.card ≤ T := by
  calc π.faulty.card ≤ (Finset.range T).card := by
        refine Finset.card_le_card_of_injOn π.crashRound (fun j hj => ?_) ?_
        · obtain ⟨⟨ρ, D⟩, hρ⟩ := mem_faulty.1 hj
          simpa [crashRound, hρ] using h.1 j ρ D hρ
        · intro j hj j' hj' he
          obtain ⟨⟨ρ, D⟩, hρ⟩ := mem_faulty.1 (Finset.mem_coe.1 hj)
          obtain ⟨⟨ρ', D'⟩, hρ'⟩ := mem_faulty.1 (Finset.mem_coe.1 hj')
          simp only [crashRound, hρ, hρ'] at he
          subst he
          exact h.2 j j' ρ D D' hρ hρ'
    _ = T := Finset.card_range T

end CrashPattern

namespace CrashProtocol

variable {G V σ M : Type*} (Q : CrashProtocol G V σ M) [DecidableEq G]

/-- **Executions agree while deliveries agree.** States agree up to round `k` when the
deliveries of the rounds before `k` agree. -/
theorem state_congr (x : G → V) {π π' : CrashPattern G} {k : ℕ}
    (h : ∀ r < k, ∀ j i, π.delivers r j i = π'.delivers r j i) :
    ∀ r ≤ k, Q.state x π r = Q.state x π' r := by
  intro r hr
  induction r with
  | zero => rfl
  | succ r ih =>
      funext i
      simp only [state]
      rw [ih (by omega)]
      congr 1
      funext j
      rw [h r (by omega) j i]

/-- **A silent process changes nothing for the others.** From round `k₀` on, let the process
`q` deliver nothing in two executions, let the other processes deliver alike, and let the
processes other than `q` be in equal states at round `k₀`. Then the processes other than `q`
stay in equal states. -/
theorem state_eq_of_silent (x x' : G → V) {π π' : CrashPattern G} {q : G} {k₀ : ℕ}
    (h0 : ∀ i, i ≠ q → Q.state x π k₀ i = Q.state x' π' k₀ i)
    (hd : ∀ r, k₀ ≤ r → ∀ j, j ≠ q → ∀ i, π.delivers r j i = π'.delivers r j i)
    (hq : ∀ r, k₀ ≤ r → ∀ i, π.delivers r q i = false ∧ π'.delivers r q i = false) :
    ∀ r, k₀ ≤ r → ∀ i, i ≠ q → Q.state x π r i = Q.state x' π' r i := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => exact h0
  | succ r hr ih =>
      intro i hi
      simp only [state]
      rw [ih i hi]
      congr 1
      funext j
      by_cases hj : j = q
      · subst hj
        simp [(hq r hr i).1, (hq r hr i).2]
      · rw [hd r hr j hj i, ih j hj]

/-- **One round of an execution under crash failures.** A process's next state depends only on
the current states and on what it receives. -/
theorem state_succ_eq (x : G → V) {π π' : CrashPattern G} {r : ℕ} {i : G}
    (h : Q.state x π r = Q.state x π' r) (hd : ∀ j, π.delivers r j i = π'.delivers r j i) :
    Q.state x π (r + 1) i = Q.state x π' (r + 1) i := by
  simp only [state, h, hd]

/-- **Solving consensus against at most one crash per round.** `Q` solves consensus in `T`
rounds against every admissible crash pattern for `T` rounds (crashes before round `T`, at most
one per round): no two correct processes decide differently, and the value decided by a correct
process is the input of some process. This is the system of Aguilera and Toueg's Theorem 1. -/
def SolvesOnePerRound (T : ℕ) : Prop :=
  ∀ (x : G → V) (π : CrashPattern G), π.Good T →
    (∀ i j, π i = none → π j = none → Q.decision x π T i = Q.decision x π T j) ∧
      ∀ i, π i = none → ∃ j, x j = Q.decision x π T i

/-- **Solving consensus against `f ≥ T` crashes includes one crash per round.** -/
theorem solvesOnePerRound_of_solves [Fintype G] {f T : ℕ} (hQ : Q.Solves f T) (hT : T ≤ f) :
    Q.SolvesOnePerRound T :=
  fun x π hπ => hQ x π ((CrashPattern.card_faulty_le hπ).trans hT)

/-! ### The proof of Aguilera and Toueg -/

section Proof

variable [Fintype G] (x : G → V) (T : ℕ)

/-- A partial run up to round `k`: an admissible pattern whose crashes happen before round `k`. -/
private def PartialAt (k : ℕ) (π : CrashPattern G) : Prop :=
  π.Good T ∧ ∀ j ρ D, π j = some (ρ, D) → ρ < k

/-- An admissible extension of a partial run up to round `k`: it keeps the crashes of `π` and
adds crashes in round `k` or later. -/
private def Ext (k : ℕ) (π π' : CrashPattern G) : Prop :=
  (∀ j c, π j = some c → π' j = some c) ∧ (∀ j ρ D, π' j = some (ρ, D) → π j = none → k ≤ ρ) ∧
    π'.Good T

/-- `v` is a possible decision of a correct process in some extension. -/
private def Valence (k : ℕ) (π : CrashPattern G) (v : V) : Prop :=
  ∃ π', Ext T k π π' ∧ ∃ i, π' i = none ∧ Q.decision x π' T i = v

/-- All extensions decide the same value. -/
private def Univalent (k : ℕ) (π : CrashPattern G) : Prop :=
  ∀ v w, Valence Q x T k π v → Valence Q x T k π w → v = w

omit [DecidableEq G] in
/-- An admissible pattern has two correct processes, one of them other than any given `c`. -/
private theorem exists_correct_ne {f : ℕ} (hG : f + 2 ≤ Fintype.card G) (hT : T ≤ f)
    {π : CrashPattern G} (hπ : π.Good T) (c : G) : ∃ c', c' ≠ c ∧ π c' = none := by
  classical
  have hcard := CrashPattern.card_faulty_le hπ
  have : 1 < (Finset.univ \ π.faulty).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 this
  have hna : π a = none := by
    by_contra h
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 h
    exact (Finset.mem_sdiff.1 ha).2 (CrashPattern.mem_faulty.2 ⟨c, hc⟩)
  have hnb : π b = none := by
    by_contra h
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 h
    exact (Finset.mem_sdiff.1 hb).2 (CrashPattern.mem_faulty.2 ⟨c, hc⟩)
  by_cases hac : a = c
  · exact ⟨b, fun h => hab (hac.trans h.symm), hnb⟩
  · exact ⟨a, hac, hna⟩

variable {Q x T}

omit [DecidableEq G] [Fintype G] in
/-- A partial run extends itself. -/
private theorem ext_refl {k : ℕ} {π : CrashPattern G} (h : PartialAt T k π) : Ext T k π π :=
  ⟨fun _ _ h => h, fun _ _ _ h h' => by simp [h'] at h, h.1⟩

/-- Every partial run has a possible decision. -/
private theorem exists_valence {f : ℕ} (hG : f + 2 ≤ Fintype.card G) (hT : T ≤ f) {k : ℕ}
    {π : CrashPattern G} (h : PartialAt T k π) : ∃ c, π c = none ∧
      Valence Q x T k π (Q.decision x π T c) := by
  have : Nonempty G := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨c, -, hc⟩ := exists_correct_ne T hG hT h.1 (Classical.arbitrary G)
  exact ⟨c, hc, π, ext_refl h, c, hc, rfl⟩

omit [Fintype G] in
/-- Agreement in an admissible pattern. -/
private theorem agree (hQ : Q.SolvesOnePerRound T) {π : CrashPattern G}
    (hπ : π.Good T) {i j : G} (hi : π i = none) (hj : π j = none) :
    Q.decision x π T i = Q.decision x π T j :=
  (hQ x π hπ).1 i j hi hj

omit [Fintype G] in
/-- Deliveries of a crashed process. -/
private theorem delivers_some {π : CrashPattern G} {j : G} {ρ : ℕ} {D : Finset G}
    (h : π j = some (ρ, D)) (r : ℕ) (i : G) :
    π.delivers r j i =
      (Decidable.decide (r < ρ) || (Decidable.decide (r = ρ) && Decidable.decide (i ∈ D))) := by
  simp [CrashPattern.delivers, h]

/-- **Lemma 2 of Aguilera and Toueg.** A partial run up to round `T - 1` is univalent. -/
private theorem univalent_last {f : ℕ} (hG : f + 2 ≤ Fintype.card G)
    (hQ : Q.SolvesOnePerRound T) (hT : T ≤ f) (hT1 : 1 ≤ T) {π : CrashPattern G}
    (hπ : PartialAt T (T - 1) π) :
    Univalent Q x T (T - 1) π := by
  obtain ⟨c₀, hc₀, -⟩ := exists_valence (Q := Q) (x := x) hG hT hπ
  set v₀ := Q.decision x π T c₀
  -- Every extension decides `v₀`.
  suffices key : ∀ π', Ext T (T - 1) π π' → ∀ i, π' i = none → Q.decision x π' T i = v₀ by
    rintro v w ⟨π₁, h₁, i₁, hi₁, rfl⟩ ⟨π₂, h₂, i₂, hi₂, rfl⟩
    rw [key π₁ h₁ i₁ hi₁, key π₂ h₂ i₂ hi₂]
  intro π' ⟨hkeep, hnew, hgood⟩ i hi
  -- New crashes are in round `T - 1`.
  have hnewT : ∀ j ρ D, π' j = some (ρ, D) → π j = none → ρ = T - 1 := fun j ρ D h h' => by
    have := hnew j ρ D h h'; have := hgood.1 j ρ D h; omega
  -- The two patterns deliver alike before round `T - 1`.
  have hbefore : ∀ r < T - 1, ∀ j i, π.delivers r j i = π'.delivers r j i := by
    intro r hr j i
    cases hj : π j with
    | some c => rw [CrashPattern.delivers, CrashPattern.delivers, hj, hkeep j c hj]
    | none =>
        cases hj' : π' j with
        | none => simp [CrashPattern.delivers, hj, hj']
        | some c =>
            obtain ⟨ρ, D⟩ := c
            have := hnewT j ρ D hj' hj
            simp [CrashPattern.delivers, hj, hj', this, hr]
  have hstate := Q.state_congr x hbefore (T - 1) le_rfl
  -- A correct process that receives the round-`T - 1` messages as in `π` decides `v₀`.
  have hsame : ∀ π₁ : CrashPattern G, (∀ j c, π j = some c → π₁ j = some c) →
      Q.state x π₁ (T - 1) = Q.state x π (T - 1) → ∀ j, π₁ j = none →
      (∀ l, π₁.delivers (T - 1) l j = π.delivers (T - 1) l j) → Q.decision x π₁ T j = v₀ := by
    intro π₁ hk₁ hs₁ j hj hd
    have hjπ : π j = none := by
      cases h : π j with
      | none => rfl
      | some c => simp [hk₁ j c h] at hj
    have e := Q.state_succ_eq x hs₁ hd
    rw [Nat.sub_add_cancel hT1] at e
    simp only [decision, e]
    exact agree hQ hπ.1 hjπ hc₀
  by_cases hp : ∃ p ρ D, π' p = some (ρ, D) ∧ π p = none
  · obtain ⟨p, ρ, D, hp, hpπ⟩ := hp
    have hρ := hnewT p ρ D hp hpπ
    subst hρ
    -- The only new crash is that of `p`.
    have honly : ∀ j, j ≠ p → π' j = π j := by
      intro j hjp
      cases hj : π j with
      | some c => exact hkeep j c hj
      | none =>
          cases hj' : π' j with
          | none => rfl
          | some c =>
              obtain ⟨ρ', D'⟩ := c
              have := hnewT j ρ' D' hj' hj
              subst this
              exact absurd (hgood.2 j p _ D' D hj' hp) hjp
    have hpπd : ∀ j, π.delivers (T - 1) p j = true := fun j => by
      simp [CrashPattern.delivers, hpπ]
    by_cases hall : ∀ j, π' j = none → j ∈ D
    · refine hsame π' hkeep hstate.symm i hi fun l => ?_
      by_cases hl : l = p
      · subst hl; simp [delivers_some hp, hall i hi, hpπd]
      · simp only [CrashPattern.delivers, honly l hl]
    · push Not at hall
      obtain ⟨c, hc, hcD⟩ := hall
      -- `p` also reaches `c`.
      let π₁ : CrashPattern G := fun j => if j = p then some (T - 1, insert c D) else π' j
      have hp₁ : π₁ p = some (T - 1, insert c D) := by simp [π₁]
      have hne₁ : ∀ j, j ≠ p → π₁ j = π' j := fun j hj => by simp [π₁, hj]
      have hg₁ : π₁.Good T := by
        refine ⟨fun j ρ' D' h => ?_, fun j j' ρ' D₁ D₂ h h' => ?_⟩
        · by_cases hj : j = p
          · subst hj; rw [hp₁] at h; cases h; omega
          · rw [hne₁ j hj] at h; exact hgood.1 j ρ' D' h
        · have key : ∀ l ρ₀ D₀, π₁ l = some (ρ₀, D₀) → ∃ E₀, π' l = some (ρ₀, E₀) := by
            intro l ρ₀ D₀ h
            by_cases hl : l = p
            · subst hl; rw [hp₁] at h; cases h; exact ⟨D, hp⟩
            · rw [hne₁ l hl] at h; exact ⟨D₀, h⟩
          obtain ⟨E₁, hE₁⟩ := key j ρ' D₁ h
          obtain ⟨E₂, hE₂⟩ := key j' ρ' D₂ h'
          exact hgood.2 j j' ρ' E₁ E₂ hE₁ hE₂
      have hk₁ : ∀ j c', π j = some c' → π₁ j = some c' := fun j c' h => by
        by_cases hj : j = p
        · subst hj; simp [hpπ] at h
        · rw [hne₁ j hj]; exact hkeep j c' h
      have hbefore₁ : ∀ r < T - 1, ∀ j i, π'.delivers r j i = π₁.delivers r j i := by
        intro r hr j i
        by_cases hj : j = p
        · subst hj; simp [delivers_some hp, delivers_some hp₁, hr]
        · simp only [CrashPattern.delivers, hne₁ j hj]
      have hstate₁ : Q.state x π₁ (T - 1) = Q.state x π (T - 1) :=
        (Q.state_congr x hbefore₁ (T - 1) le_rfl).symm.trans hstate.symm
      have hcp : c ≠ p := fun h => by rw [h, hp] at hc; cases hc
      have hc₁ : π₁ c = none := by rw [hne₁ c hcp]; exact hc
      -- In `π₁`, `c` decides `v₀`.
      have hdc : Q.decision x π₁ T c = v₀ := by
        refine hsame π₁ hk₁ hstate₁ c hc₁ fun l => ?_
        by_cases hl : l = p
        · subst hl; simp [delivers_some hp₁, hpπd]
        · simp only [CrashPattern.delivers, hne₁ l hl, honly l hl]
      -- Every correct process of `π'` other than `c` decides as in `π₁`, hence `v₀`.
      have hother : ∀ j, j ≠ c → π' j = none → Q.decision x π' T j = v₀ := by
        intro j hjc hj
        have hjp : j ≠ p := fun h => by rw [h, hp] at hj; cases hj
        have e : Q.state x π' T j = Q.state x π₁ T j := by
          have := Q.state_succ_eq x (π := π') (π' := π₁) (r := T - 1) (i := j)
            (Q.state_congr x hbefore₁ (T - 1) le_rfl) (fun l => by
              by_cases hl : l = p
              · subst hl; simp [delivers_some hp, delivers_some hp₁, hjc]
              · simp only [CrashPattern.delivers, hne₁ l hl])
          rwa [Nat.sub_add_cancel hT1] at this
        have hj₁ : π₁ j = none := by rw [hne₁ j hjp]; exact hj
        simp only [decision, e]
        exact (agree hQ hg₁ hj₁ hc₁).trans hdc
      by_cases hic : i = c
      · subst hic
        obtain ⟨j, hjc, hj⟩ := exists_correct_ne T hG hT hgood i
        exact (agree hQ hgood hi hj).trans (hother j hjc hj)
      · exact hother i hic hi
  · -- No new crash: `π'` is `π`.
    push Not at hp
    have : π' = π := by
      funext j
      cases hj : π j with
      | some c => exact hkeep j c hj
      | none =>
          cases hj' : π' j with
          | none => rfl
          | some c => exact absurd hj (hp j c.1 c.2 hj')
    subst this
    exact agree hQ hπ.1 hi hc₀

/-- The pattern with no crash. -/
private def noCrash : CrashPattern G := fun _ => none

omit [DecidableEq G] [Fintype G] in
private theorem partialAt_noCrash (k : ℕ) : PartialAt T k (noCrash : CrashPattern G) :=
  ⟨⟨fun _ _ _ h => by simp [noCrash] at h, fun _ _ _ _ _ h => by simp [noCrash] at h⟩,
    fun _ _ _ h => by simp [noCrash] at h⟩

/-- **Lemma 3 of Aguilera and Toueg.** If `T ≥ 1`, some input assignment gives a bivalent
initial configuration. -/
private theorem exists_bivalent_initial [Nontrivial V] {f : ℕ} (hG : f + 2 ≤ Fintype.card G)
    (hQ : Q.SolvesOnePerRound T) (hT : T ≤ f) (hT1 : 1 ≤ T) :
    ∃ x : G → V, ¬ Univalent Q x T 0 noCrash := by
  obtain ⟨v, w, hvw⟩ := exists_pair_ne V
  let e := Fintype.equivFin G
  let x : ℕ → G → V := fun k j => if (e j).val < k then w else v
  by_contra hno
  push Not at hno
  -- Validity: every value decided from `x k` is an input.
  have hvalid : ∀ k u, Valence Q (x k) T 0 noCrash u → ∃ j, x k j = u := by
    rintro k u ⟨π', ⟨-, -, hg⟩, i, hi, rfl⟩
    exact (hQ (x k) π' hg).2 i hi
  have key : ∀ k, k ≤ Fintype.card G → Valence Q (x k) T 0 noCrash v := by
    intro k
    induction k with
    | zero =>
        intro _
        obtain ⟨c, -, hc⟩ := exists_valence (Q := Q) (x := x 0) hG hT
          (partialAt_noCrash (T := T) 0)
        obtain ⟨j, hj⟩ := hvalid 0 _ hc
        simp only [x, Nat.not_lt_zero, ite_false] at hj
        exact hj ▸ hc
    | succ k ih =>
        intro hk
        have hv := ih (by omega)
        -- Crash the process `p` numbered `k` at the start: nobody hears its input.
        let p := e.symm ⟨k, by omega⟩
        let πp : CrashPattern G := fun j => if j = p then some (0, ∅) else none
        have hπp : πp p = some (0, ∅) := by simp [πp]
        have hg : πp.Good T := by
          refine ⟨fun j ρ D h => ?_, fun j j' ρ D D' h h' => ?_⟩
          · by_cases hj : j = p
            · subst hj; rw [hπp] at h; cases h; omega
            · simp [πp, hj] at h
          · by_cases hj : j = p
            · by_cases hj' : j' = p
              · rw [hj, hj']
              · simp [πp, hj'] at h'
            · simp [πp, hj] at h
        have hext : Ext T 0 noCrash πp := ⟨fun _ _ h => by simp [noCrash] at h,
          fun _ _ _ _ _ => Nat.zero_le _, hg⟩
        obtain ⟨c, hcp, hc⟩ := exists_correct_ne T hG hT hg p
        have hsame : Q.decision (x k) πp T c = Q.decision (x (k + 1)) πp T c := by
          simp only [decision]
          refine congrArg _ (Q.state_eq_of_silent (x k) (x (k + 1)) (q := p) (k₀ := 0)
            (fun i hi => ?_) (fun _ _ _ _ _ => rfl) (fun r _ i => ?_) T (Nat.zero_le _) c hcp)
          · have hi' : (e i).val ≠ k := fun h => hi (by
              apply e.injective; simp [p, Fin.ext_iff, h])
            simp only [state, x]
            congr 2
            by_cases h1 : (e i).val < k
            · simp [h1, show (e i).val < k + 1 by omega]
            · simp [h1, show ¬ (e i).val < k + 1 by omega]
          · simp [delivers_some hπp]
        have hb₁ : Valence Q (x k) T 0 noCrash (Q.decision (x k) πp T c) := ⟨πp, hext, c, hc, rfl⟩
        have hb₂ : Valence Q (x (k + 1)) T 0 noCrash (Q.decision (x k) πp T c) :=
          ⟨πp, hext, c, hc, hsame.symm⟩
        rwa [← hno (x k) v _ hv hb₁] at hb₂
  obtain ⟨j, hj⟩ := hvalid _ _ (key _ le_rfl)
  simp only [x, (e j).isLt, ite_true] at hj
  exact hvw hj.symm

/-- The pattern `π` in which the process `p` crashes as `c` says. -/
private def upd (π : CrashPattern G) (p : G) (c : ℕ × Finset G) : CrashPattern G :=
  fun j => if j = p then some c else π j

omit [Fintype G] in
private theorem upd_self (π : CrashPattern G) (p : G) (c : ℕ × Finset G) : upd π p c p = some c :=
  by simp [upd]

omit [Fintype G] in
private theorem upd_ne {π : CrashPattern G} {p j : G} (c : ℕ × Finset G) (h : j ≠ p) :
    upd π p c j = π j := by simp [upd, h]

omit [Fintype G] in
private theorem delivers_upd_ne {π : CrashPattern G} {p j : G} (c : ℕ × Finset G) (h : j ≠ p)
    (r : ℕ) (i : G) : (upd π p c).delivers r j i = π.delivers r j i := by
  simp only [CrashPattern.delivers, upd_ne c h]

omit [Fintype G] in
/-- Crashing a correct process in an unused round keeps a pattern admissible. -/
private theorem good_upd {π : CrashPattern G} {p : G} {ρ : ℕ} {D : Finset G} (hπ : π.Good T)
    (hp : π p = none) (hρ : ρ < T) (hfree : ∀ j ρ' D', π j = some (ρ', D') → ρ' ≠ ρ) :
    (upd π p (ρ, D)).Good T := by
  refine ⟨fun j ρ' D' h => ?_, fun j j' ρ' D₁ D₂ h h' => ?_⟩
  · by_cases hj : j = p
    · subst hj; rw [upd_self] at h; cases h; exact hρ
    · rw [upd_ne _ hj] at h; exact hπ.1 j ρ' D' h
  · by_cases hj : j = p
    · by_cases hj' : j' = p
      · rw [hj, hj']
      · subst hj; rw [upd_self] at h; cases h
        rw [upd_ne _ hj'] at h'
        exact absurd rfl (hfree j' _ D₂ h')
    · by_cases hj' : j' = p
      · subst hj'; rw [upd_self] at h'; cases h'
        rw [upd_ne _ hj] at h
        exact absurd rfl (hfree j _ D₁ h)
      · rw [upd_ne _ hj] at h; rw [upd_ne _ hj'] at h'
        exact hπ.2 j j' ρ' D₁ D₂ h h'

omit [Fintype G] in
/-- Crashing a correct process in round `k₀` or later extends a pattern. -/
private theorem ext_upd {k₀ : ℕ} {π : CrashPattern G} {p : G} {ρ : ℕ} {D : Finset G}
    (hp : π p = none) (hρ : k₀ ≤ ρ) (hg : (upd π p (ρ, D)).Good T) :
    Ext T k₀ π (upd π p (ρ, D)) := by
  refine ⟨fun j c h => ?_, fun j ρ' D' h h' => ?_, hg⟩
  · have hj : j ≠ p := fun e => by rw [e, hp] at h; cases h
    rw [upd_ne _ hj]; exact h
  · by_cases hj : j = p
    · subst hj; rw [upd_self] at h; cases h; exact hρ
    · rw [upd_ne _ hj, h'] at h; cases h

omit [Fintype G] in
private theorem delivers_lt {π : CrashPattern G} {j : G} {ρ : ℕ} {D : Finset G}
    (h : π j = some (ρ, D)) {r : ℕ} (hr : r < ρ) (i : G) : π.delivers r j i = true := by
  simp [CrashPattern.delivers, h, hr]

omit [Fintype G] in
private theorem delivers_gt {π : CrashPattern G} {j : G} {ρ : ℕ} {D : Finset G}
    (h : π j = some (ρ, D)) {r : ℕ} (hr : ρ < r) (i : G) : π.delivers r j i = false := by
  have h1 : ¬ r < ρ := by omega
  have h2 : r ≠ ρ := by omega
  simp [CrashPattern.delivers, h, h1, h2]

omit [Fintype G] in
private theorem delivers_ge_empty {π : CrashPattern G} {j : G} {ρ : ℕ}
    (h : π j = some (ρ, ∅)) {r : ℕ} (hr : ρ ≤ r) (i : G) : π.delivers r j i = false := by
  have h1 : ¬ r < ρ := by omega
  simp [CrashPattern.delivers, h, h1]

omit [Fintype G] in
private theorem delivers_eq {π : CrashPattern G} {j : G} {ρ : ℕ} {D : Finset G}
    (h : π j = some (ρ, D)) (i : G) : π.delivers ρ j i = Decidable.decide (i ∈ D) := by
  simp [CrashPattern.delivers, h]

/-- **Lemma 4 of Aguilera and Toueg.** A bivalent partial run up to round `k`, with
`k + 1 < T`, has a bivalent one-round extension. -/
private theorem exists_bivalent_succ {f : ℕ} (hG : f + 2 ≤ Fintype.card G) (hT : T ≤ f)
    {k : ℕ} (hk : k + 1 < T) {π : CrashPattern G} (hπ : PartialAt T k π)
    (hb : ¬ Univalent Q x T k π) :
    ∃ π₁, PartialAt T (k + 1) π₁ ∧ ¬ Univalent Q x T (k + 1) π₁ := by
  by_contra H
  push Not at H
  have hπ1 : PartialAt T (k + 1) π := ⟨hπ.1, fun j ρ D h => by have := hπ.2 j ρ D h; omega⟩
  obtain ⟨c₀, hc₀, hv⟩ := exists_valence (Q := Q) (x := x) hG hT hπ1
  set v := Q.decision x π T c₀
  -- A value `u ≠ v` decided in some extension of `π`.
  obtain ⟨u, huv, hu⟩ : ∃ u, u ≠ v ∧ Valence Q x T k π u := by
    simp only [Univalent, not_forall] at hb
    obtain ⟨a, b, ha, hb', hab⟩ := hb
    by_cases hav : a = v
    · exact ⟨b, fun h => hab (hav.trans h.symm), hb'⟩
    · exact ⟨a, hav, ha⟩
  obtain ⟨π', ⟨hkeep, hnew, hgood⟩, i, hi, hiu⟩ := hu
  -- The crashes of `π` are before round `k`; a process crashing in round `k` is new.
  have hfree : ∀ j ρ D, π j = some (ρ, D) → ρ ≠ k := fun j ρ D h => by
    have := hπ.2 j ρ D h; omega
  by_cases hp : ∃ p D, π' p = some (k, D)
  swap
  · -- No crash in round `k`: `π'` extends `π` from round `k + 1`, so `u = v`.
    push Not at hp
    refine huv (H π hπ1 u v ⟨π', ⟨hkeep, fun j ρ D h h' => ?_, hgood⟩, i, hi, hiu⟩ hv)
    have := hnew j ρ D h h'
    rcases Nat.lt_or_ge k ρ with hlt | hge
    · omega
    · have : ρ = k := by omega
      subst this; exact absurd h (hp j D)
  obtain ⟨p, D, hpD⟩ := hp
  have hpπ : π p = none := by
    cases h : π p with
    | none => rfl
    | some c =>
        obtain ⟨ρ, D'⟩ := c
        rw [hkeep p _ h] at hpD; cases hpD; exact absurd rfl (hfree p _ _ h)
  -- The patterns in which `p` crashes in round `k`, reaching `E`.
  let πE : Finset G → CrashPattern G := fun E => upd π p (k, E)
  have hgE : ∀ E, (πE E).Good T := fun E => good_upd hπ.1 hpπ (by omega) hfree
  have hPE : ∀ E, PartialAt T (k + 1) (πE E) := fun E => ⟨hgE E, fun j ρ D' h => by
    by_cases hj : j = p
    · subst hj; simp only [πE, upd_self] at h; cases h; omega
    · simp only [πE, upd_ne _ hj] at h; have := hπ.2 j ρ D' h; omega⟩
  have hdelp : ∀ E r i, (πE E).delivers r p i =
      (Decidable.decide (r < k) || (Decidable.decide (r = k) && Decidable.decide (i ∈ E))) :=
    fun E r i => delivers_some (upd_self π p (k, E)) r i
  -- `u` is decided in an extension of `πE D`.
  have huD : Valence Q x T (k + 1) (πE D) u := by
    refine ⟨π', ⟨fun j c h => ?_, fun j ρ D' h h' => ?_, hgood⟩, i, hi, hiu⟩
    · by_cases hj : j = p
      · subst hj; simp only [πE, upd_self] at h; rw [← h]; exact hpD
      · simp only [πE, upd_ne _ hj] at h; exact hkeep j c h
    · have hj : j ≠ p := fun e => by subst e; simp [πE, upd_self] at h'
      simp only [πE, upd_ne _ hj] at h'
      have := hnew j ρ D' h h'
      rcases Nat.lt_or_ge k ρ with hlt | hge
      · omega
      · have : ρ = k := by omega
        subst this; exact absurd (hgood.2 j p _ D' D h hpD) hj
  -- Every one-round extension that some correct process sees as `πE E` in all rounds ...
  -- Claim A: `v` is decided in an extension of `πE univ`.
  have hA : Valence Q x T (k + 1) (πE Finset.univ) v := by
    let πa := upd π p (k + 1, ∅)
    have hga : πa.Good T := good_upd hπ.1 hpπ hk (fun j ρ D' h => by
      have := hπ.2 j ρ D' h; omega)
    have hexa : Ext T (k + 1) π πa := ext_upd hpπ le_rfl hga
    obtain ⟨c, hcp, hc⟩ := exists_correct_ne T hG hT hga p
    have hcv : Q.decision x πa T c = v := H π hπ1 _ _ ⟨πa, hexa, c, hc, rfl⟩ hv
    have hcπ : π c = none := by simp only [πa, upd_ne _ hcp] at hc; exact hc
    have hsame : Q.state x (πE Finset.univ) T c = Q.state x πa T c := by
      refine Q.state_eq_of_silent x x (q := p) (k₀ := k + 1) (fun i' _ => ?_)
        (fun r _ j hj i' => by simp only [delivers_upd_ne _ hj])
        (fun r hr i' => ⟨delivers_gt (upd_self π p (k, Finset.univ)) (show k < r by omega) i',
          delivers_ge_empty (upd_self π p (k + 1, ∅)) hr i'⟩) T (by omega) c hcp
      refine congrFun (Q.state_congr x (fun r hr j i'' => ?_) (k + 1) le_rfl) i'
      by_cases hj : j = p
      · rw [hj, delivers_lt (upd_self π p (k + 1, ∅)) hr]
        rcases Nat.lt_or_ge r k with h | h
        · exact delivers_lt (upd_self π p (k, _)) h i''
        · have : r = k := by omega
          subst this
          simp [delivers_eq (upd_self π p (r, Finset.univ))]
      · simp only [delivers_upd_ne _ hj]
    refine ⟨πE Finset.univ, ext_refl (hPE _), c, by simp [πE, upd_ne _ hcp, hcπ], ?_⟩
    simp only [decision, hsame]; exact hcv
  -- Claim B: removing the recipients outside `D` one by one keeps `v` decided.
  have hB : ∀ S : Finset G, S ⊆ Dᶜ → Valence Q x T (k + 1) (πE (Finset.univ \ S)) v := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; simpa using hA
    | @insert q S hqS ih =>
        intro hsub
        have hv' := ih ((Finset.subset_insert q S).trans hsub)
        set E := Finset.univ \ S
        set E' := Finset.univ \ insert q S
        have hEE' : ∀ i', i' ≠ q → (i' ∈ E ↔ i' ∈ E') := fun i' hi' => by
          simp [E, E', hi']
        -- Two extensions, of `πE E` and `πE E'`, in which `q` is silent from round `k + 1`.
        obtain ⟨ρa, ρb, ha, hb, hcorr, hqa, hst⟩ : ∃ ρa ρb : CrashPattern G,
            Ext T (k + 1) (πE E) ρa ∧ Ext T (k + 1) (πE E') ρb ∧
            (∀ j, ρa j = none ↔ ρb j = none) ∧ ρa q ≠ none ∧
            ∀ i', i' ≠ q → Q.state x ρa T i' = Q.state x ρb T i' := by
          -- States agree up to round `k` (all processes) and at `k + 1` (all but `q`).
          by_cases hq : q ≠ p ∧ π q = none
          · obtain ⟨hqp, hqπ⟩ := hq
            let ρa := upd (πE E) q (k + 1, ∅)
            let ρb := upd (πE E') q (k + 1, ∅)
            have hfr : ∀ E₀, ∀ j ρ D', πE E₀ j = some (ρ, D') → ρ ≠ k + 1 := by
              intro E₀ j ρ D' h
              by_cases hj : j = p
              · subst hj; simp only [πE, upd_self] at h; cases h; omega
              · simp only [πE, upd_ne _ hj] at h; have := hπ.2 j ρ D' h; omega
            have hqE : ∀ E₀, πE E₀ q = none := fun E₀ => by simp [πE, upd_ne _ hqp, hqπ]
            refine ⟨ρa, ρb, ext_upd (hqE E) le_rfl (good_upd (hgE E) (hqE E) hk (hfr E)),
              ext_upd (hqE E') le_rfl (good_upd (hgE E') (hqE E') hk (hfr E')),
              fun j => ?_, by simp [ρa, upd_self], fun i' hi' => ?_⟩
            · by_cases hj : j = q
              · subst hj; simp [ρa, ρb, upd_self]
              · by_cases hj' : j = p
                · subst hj'; simp [ρa, ρb, πE, upd_ne _ hj, upd_self]
                · simp [ρa, ρb, πE, upd_ne _ hj, upd_ne _ hj']
            · have hdq : ∀ E₀ r i'', (upd (πE E₀) q (k + 1, ∅)).delivers r q i'' =
                  (Decidable.decide (r < k + 1) ||
                    (Decidable.decide (r = k + 1) && Decidable.decide (i'' ∈ (∅ : Finset G)))) :=
                fun E₀ r i'' => delivers_some (upd_self _ q _) r i''
              have hk' : Q.state x ρa k = Q.state x ρb k := Q.state_congr x (fun r hr j i'' => by
                by_cases hj : j = q
                · rw [hj, delivers_lt (upd_self _ q _) (show r < k + 1 by omega),
                    delivers_lt (upd_self _ q _) (show r < k + 1 by omega)]
                · simp only [ρa, ρb, delivers_upd_ne _ hj]
                  by_cases hj' : j = p
                  · rw [hj', delivers_lt (upd_self π p (k, E)) hr,
                      delivers_lt (upd_self π p (k, E')) hr]
                  · simp only [πE, delivers_upd_ne _ hj']) k le_rfl
              refine Q.state_eq_of_silent x x (q := q) (k₀ := k + 1) (fun i'' hi'' => ?_)
                (fun r hr j hj i'' => ?_) (fun r hr i'' => ⟨?_, ?_⟩) T (by omega) i' hi'
              · refine Q.state_succ_eq x hk' (fun j => ?_)
                by_cases hj : j = q
                · rw [hj, delivers_lt (upd_self _ q _) (show k < k + 1 by omega),
                    delivers_lt (upd_self _ q _) (show k < k + 1 by omega)]
                · simp only [ρa, ρb, delivers_upd_ne _ hj]
                  by_cases hj' : j = p
                  · rw [hj', delivers_eq (upd_self π p (k, E)), delivers_eq (upd_self π p (k, E'))]
                    exact decide_eq_decide.2 (hEE' i'' hi'')
                  · simp only [πE, delivers_upd_ne _ hj']
              · simp only [ρa, ρb, delivers_upd_ne _ hj]
                by_cases hj' : j = p
                · rw [hj', delivers_gt (upd_self π p (k, E)) (show k < r by omega),
                    delivers_gt (upd_self π p (k, E')) (show k < r by omega)]
                · simp only [πE, delivers_upd_ne _ hj']
              · exact delivers_ge_empty (upd_self (πE E) q (k + 1, ∅)) hr i''
              · exact delivers_ge_empty (upd_self (πE E') q (k + 1, ∅)) hr i''
          · -- `q` is already faulty: it crashed before round `k`, or it is `p`.
            have hqsil : ∀ E₀ r, k + 1 ≤ r → ∀ i'', (πE E₀).delivers r q i'' = false := by
              intro E₀ r hr i''
              by_cases hqp : q = p
              · rw [hqp]; exact delivers_gt (upd_self π p (k, E₀)) (by omega) i''
              · have : π q ≠ none := fun h => hq ⟨hqp, h⟩
                obtain ⟨⟨ρ, D'⟩, hρ⟩ := Option.ne_none_iff_exists'.1 this
                have := hπ.2 q ρ D' hρ
                simp only [πE, delivers_upd_ne _ hqp]
                exact delivers_gt hρ (by omega) i''
            refine ⟨πE E, πE E', ext_refl (hPE E), ext_refl (hPE E'), fun j => ?_, ?_,
              fun i' hi' => ?_⟩
            · by_cases hj : j = p
              · subst hj; simp [πE, upd_self]
              · simp [πE, upd_ne _ hj]
            · by_cases hqp : q = p
              · subst hqp; simp [πE, upd_self]
              · have : π q ≠ none := fun h => hq ⟨hqp, h⟩
                simpa [πE, upd_ne _ hqp] using this
            · have hk' : Q.state x (πE E) k = Q.state x (πE E') k :=
                Q.state_congr x (fun r hr j i'' => by
                  by_cases hj' : j = p
                  · rw [hj', delivers_lt (upd_self π p (k, E)) hr,
                      delivers_lt (upd_self π p (k, E')) hr]
                  · simp only [πE, delivers_upd_ne _ hj']) k le_rfl
              refine Q.state_eq_of_silent x x (q := q) (k₀ := k + 1) (fun i'' hi'' => ?_)
                (fun r hr j hj i'' => ?_) (fun r hr i'' => ⟨hqsil E r hr i'', hqsil E' r hr i''⟩)
                T (by omega) i' hi'
              · refine Q.state_succ_eq x hk' (fun j => ?_)
                by_cases hj' : j = p
                · rw [hj', delivers_eq (upd_self π p (k, E)), delivers_eq (upd_self π p (k, E'))]
                  exact decide_eq_decide.2 (hEE' i'' hi'')
                · simp only [πE, delivers_upd_ne _ hj']
              · by_cases hj' : j = p
                · rw [hj', delivers_gt (upd_self π p (k, E)) (show k < r by omega),
                    delivers_gt (upd_self π p (k, E')) (show k < r by omega)]
                · simp only [πE, delivers_upd_ne _ hj']
        obtain ⟨c, hcq, hc⟩ := exists_correct_ne T hG hT ha.2.2 q
        have hcv : Q.decision x ρa T c = v :=
          H (πE E) (hPE E) _ _ ⟨ρa, ha, c, hc, rfl⟩ hv'
        refine ⟨ρb, hb, c, (hcorr c).1 hc, ?_⟩
        simp only [decision, ← hst c hcq]
        exact hcv
  have hD := hB (Finset.univ \ D) (by intro j; simp)
  rw [show Finset.univ \ (Finset.univ \ D) = D by ext; simp] at hD
  exact huv (H (πE D) (hPE D) u v huD hD)

end Proof

/-- **Consensus against `T` crashes, at most one per round, needs more than `T` rounds**
(Aguilera and Toueg, *A simple bivalency proof that t-resilient consensus requires t + 1
rounds*, Information Processing Letters 71, 1999, Theorem 1, with `t = T`). If there are at
least `T + 2` processes and at least two values, no deterministic synchronous protocol solves
consensus in `T` rounds against the crash patterns with crashes before round `T` and at most one
crash per round. Aguilera and Toueg's system also allows crashes in later rounds, which change
nothing before the decisions, so this hypothesis is weaker than theirs and the theorem is at
least as strong as their Theorem 1. -/
theorem not_solvesOnePerRound [Fintype G] [Nontrivial V] (Q : CrashProtocol G V σ M) {T : ℕ}
    (hG : T + 2 ≤ Fintype.card G) : ¬ Q.SolvesOnePerRound T := by
  intro hQ
  rcases Nat.eq_zero_or_pos T with h0 | hT1
  · -- Zero rounds: each process decides a function of its own input.
    subst h0
    obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card G)
    obtain ⟨v, w, hvw⟩ := exists_pair_ne V
    have hg : (noCrash : CrashPattern G).Good 0 := (partialAt_noCrash (T := 0) 0).1
    have hconst : ∀ (u : V) (k : G), Q.decide k (Q.init k u) = u := by
      intro u k
      obtain ⟨l, hl⟩ := (hQ (fun _ => u) _ hg).2 k rfl
      exact hl.symm
    have h := (hQ (fun k => if k = i then v else w) _ hg).1 i j rfl rfl
    simp only [decision, state, ite_true, hij.symm, ite_false, hconst] at h
    exact hvw h
  obtain ⟨x, hx⟩ := exists_bivalent_initial (Q := Q) hG hQ le_rfl hT1
  -- Extend the bivalent initial configuration round by round, up to round `T - 1`.
  have key : ∀ k, k ≤ T - 1 → ∃ π, PartialAt T k π ∧ ¬ Univalent Q x T k π := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨noCrash, partialAt_noCrash 0, hx⟩
    | succ k ih =>
        intro hk
        obtain ⟨π, hπ, hb⟩ := ih (by omega)
        exact exists_bivalent_succ hG le_rfl (by omega) hπ hb
  obtain ⟨π, hπ, hb⟩ := key (T - 1) le_rfl
  exact hb (univalent_last hG hQ le_rfl hT1 hπ)

/-- **Consensus with `f` crash failures needs `f + 1` rounds.** If there are at least `f + 2`
processes and at least two values, and a deterministic synchronous protocol solves consensus
(agreement and validity, every correct process deciding at the end of round `T`) tolerating `f`
crash failures, then `T ≥ f + 1`. This is weaker than Aguilera and Toueg's Theorem 1 (*A simple
bivalency proof that t-resilient consensus requires t + 1 rounds*, 1999), which allows at most
one crash per round; it follows from their form, `not_solvesOnePerRound`. -/
theorem f_add_one_le_of_solves [Fintype G] [Nontrivial V] (Q : CrashProtocol G V σ M) {f T : ℕ}
    (hG : f + 2 ≤ Fintype.card G) (hQ : Q.Solves f T) : f + 1 ≤ T := by
  by_contra hlt
  exact Q.not_solvesOnePerRound (T := T) (by omega) (Q.solvesOnePerRound_of_solves hQ (by omega))

end CrashProtocol

end Cslib.Distributed.CrashConsensus
