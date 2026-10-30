/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Generalized Büchi automata and degeneralization
-/
module

public import Cslib.Computability.Automata.NA.Basic

/-!
# Generalized Büchi automata and degeneralization

A *generalized* Büchi automaton has finitely many acceptance sets `F₀, …, Fₖ₋₁` and
accepts a run when it visits every one of them infinitely often. The classical
degeneralization replaces the `k` sets by a single Büchi set: the product automaton
keeps a counter in `Fin (k + 1)` recording which acceptance set is awaited next,
advances the counter when the awaited set is hit, and resets it to `0` after the
`k`-th set. The Büchi acceptance set is the counter value `k`, so an accepting run
cycles through all `k` sets infinitely often.

Main definitions and results:

* `Cslib.Automata.NA.GenBuchi`: generalized Büchi automata, with the `k` acceptance
  sets indexed by `Fin k`.
* `Cslib.Automata.NA.GenBuchi.nextCount`: the counter update.
* `Cslib.Automata.NA.GenBuchi.toBuchi`: the degeneralized Büchi automaton.
* `Cslib.Automata.NA.GenBuchi.language_toBuchi`: degeneralization preserves the
  language (`B20`).

## References

* W. Thomas, "Automata on infinite objects", in *Handbook of Theoretical Computer
  Science*, Vol. B, Elsevier, 1990, Section 3 (generalized Büchi automata and
  degeneralization by a counter).
* E. Grädel, W. Thomas, T. Wilke (eds.), *Automata, Logics, and Infinite Games*,
  LNCS 2500, Springer, 2002, Chapter 1 (Büchi automata).
-/

@[expose] public section

namespace Cslib.Automata.NA

open Filter ωSequence ωAcceptor

variable {State Symbol : Type*}

/-- A generalized Büchi automaton: a nondeterministic automaton with `k` acceptance
sets, indexed by `Fin k`. A run is accepting when it visits every acceptance set
infinitely often. -/
structure GenBuchi (State Symbol : Type*) extends NA State Symbol where
  /-- The number of acceptance sets. -/
  k : ℕ
  /-- The acceptance sets. -/
  accept : Fin k → Set State

namespace GenBuchi

/-- A run of a generalized Büchi automaton is accepting iff it visits every acceptance
set infinitely often. -/
instance : ωAcceptor (GenBuchi State Symbol) Symbol where
  Accepts (g : GenBuchi State Symbol) (xs : ωSequence Symbol) :=
    ∃ ss, g.Run xs ss ∧ ∀ j, ∃ᶠ k in atTop, ss k ∈ g.accept j

/-- Membership in the language of a generalized Büchi automaton, unfolded. -/
theorem mem_language_iff {g : GenBuchi State Symbol} {xs : ωSequence Symbol} :
    xs ∈ language g ↔
      ∃ ss, g.Run xs ss ∧ ∀ j, ∃ᶠ k in atTop, ss k ∈ g.accept j :=
  Iff.rfl

/-! ## The counter -/

open Classical in
/-- The counter update for degeneralization: from counter `i`, awaiting the `i`-th
acceptance set, move to `i + 1` on landing in that set, stay at `i` otherwise, and
reset to `0` from the top value `k`. -/
noncomputable def nextCount (g : GenBuchi State Symbol) (i : Fin (g.k + 1)) (t : State) :
    Fin (g.k + 1) :=
  if h : i.val < g.k then
    if t ∈ g.accept ⟨i.val, h⟩ then ⟨i.val + 1, by have := i.isLt; omega⟩ else i
  else ⟨0, Nat.zero_lt_succ _⟩

/-- The counter stays put when the awaited acceptance set is missed. -/
theorem nextCount_eq_self {g : GenBuchi State Symbol} {i : Fin (g.k + 1)} {t : State}
    (h : i.val < g.k) (ht : t ∉ g.accept ⟨i.val, h⟩) : g.nextCount i t = i := by
  simp [nextCount, h, ht]

/-- The counter advances when the awaited acceptance set is hit. -/
theorem nextCount_eq_succ {g : GenBuchi State Symbol} {i : Fin (g.k + 1)} {t : State}
    (h : i.val < g.k) (ht : t ∈ g.accept ⟨i.val, h⟩) :
    g.nextCount i t = ⟨i.val + 1, by have := i.isLt; omega⟩ := by
  simp [nextCount, h, ht]

/-- The counter resets to `0` from the top value `k`. -/
theorem nextCount_eq_zero {g : GenBuchi State Symbol} {i : Fin (g.k + 1)} {t : State}
    (h : i.val = g.k) : g.nextCount i t = ⟨0, Nat.zero_lt_succ _⟩ := by
  simp [nextCount, show ¬ i.val < g.k by omega]

/-- The counter sequence along a run: `countSeq g ss n` is the counter after the first
`n` states of `ss`. -/
noncomputable def countSeq (g : GenBuchi State Symbol) (ss : ωSequence State) : ℕ → Fin (g.k + 1)
  | 0 => ⟨0, Nat.zero_lt_succ _⟩
  | n + 1 => g.nextCount (countSeq g ss n) (ss (n + 1))

/-- The counter at time `0` is `0`. -/
theorem countSeq_zero (g : GenBuchi State Symbol) (ss : ωSequence State) :
    g.countSeq ss 0 = ⟨0, Nat.zero_lt_succ _⟩ :=
  rfl

/-- The counter at time `n + 1` is the update of the counter at time `n`. -/
theorem countSeq_succ (g : GenBuchi State Symbol) (ss : ωSequence State) (n : ℕ) :
    g.countSeq ss (n + 1) = g.nextCount (g.countSeq ss n) (ss (n + 1)) :=
  rfl

/-- The counter stays at `i` while the awaited acceptance set is missed. -/
theorem countSeq_stay {g : GenBuchi State Symbol} {ss : ωSequence State}
    {i : Fin (g.k + 1)} {n : ℕ} (hi : i.val < g.k) (hc : g.countSeq ss n = i) :
    ∀ {m}, n ≤ m → (∀ j, n ≤ j → j < m → ss (j + 1) ∉ g.accept ⟨i.val, hi⟩) →
      g.countSeq ss m = i := by
  intro m hnm
  induction m, hnm using Nat.le_induction with
  | base => intro _; exact hc
  | succ m hmn ih =>
    intro hstay
    have hcm : g.countSeq ss m = i := ih (fun j hj1 hj2 => hstay j hj1 (by omega))
    rw [countSeq_succ, hcm]
    exact nextCount_eq_self hi (hstay m hmn (by omega))

/-- From any time, the counter eventually reaches any value at least its current one
(up to `k`), provided every acceptance set is visited infinitely often. The proof is
by induction on the distance to the target: the first visit to the awaited set after
the current time advances the counter by one (the counter stays put until then). -/
theorem countSeq_reach {g : GenBuchi State Symbol} {ss : ωSequence State}
    (hacc : ∀ j, ∃ᶠ t in atTop, ss t ∈ g.accept j) :
    ∀ d n j, j - (g.countSeq ss n).val = d → (g.countSeq ss n).val ≤ j → j ≤ g.k →
      ∃ m, n ≤ m ∧ (g.countSeq ss m).val = j := by
  classical
  intro d
  induction d with
  | zero =>
    intro n j hd hle _
    exact ⟨n, le_refl n, by omega⟩
  | succ d ih =>
    intro n j hd hle hjk
    have hlt : (g.countSeq ss n).val < g.k := by omega
    obtain ⟨t, _htge, htmem⟩ :=
      frequently_atTop.mp (hacc ⟨(g.countSeq ss n).val, hlt⟩) (n + 1)
    have hex : ∃ t0, n < t0 ∧ ss t0 ∈ g.accept ⟨(g.countSeq ss n).val, hlt⟩ :=
      ⟨t, by omega, htmem⟩
    obtain ⟨t0, ht0gt, ht0mem, ht0min⟩ :
        ∃ t0, n < t0 ∧ ss t0 ∈ g.accept ⟨(g.countSeq ss n).val, hlt⟩ ∧
          ∀ m, m < t0 → ¬ (n < m ∧ ss m ∈ g.accept ⟨(g.countSeq ss n).val, hlt⟩) :=
      ⟨Nat.find hex, Nat.find_spec hex |>.1, Nat.find_spec hex |>.2,
        fun m hm => Nat.find_min hex hm⟩
    obtain ⟨t1, ht1⟩ : ∃ t1, t0 = t1 + 1 := ⟨t0 - 1, by omega⟩
    subst ht1
    have hstaycount : g.countSeq ss t1 = g.countSeq ss n := by
      refine countSeq_stay hlt rfl (by omega) fun j' hj1 hj2 => ?_
      exact fun hmem => ht0min (j' + 1) (by omega) ⟨by omega, hmem⟩
    have hadv : (g.countSeq ss (t1 + 1)).val = (g.countSeq ss n).val + 1 := by
      rw [countSeq_succ, hstaycount, nextCount_eq_succ hlt ht0mem]
    obtain ⟨m, hm1, hm2⟩ := ih (t1 + 1) j (by omega) (by omega) hjk
    exact ⟨m, by omega, hm2⟩

/-- The counter crosses every value below its target: from `0` to `d`, with no
intermediate visit to `k`, some step advances the counter from `j` to `j + 1`,
and the destination state then lies in the `j`-th acceptance set. The proof is by
induction on the right endpoint, case-splitting the last counter step into
stay, advance, or (impossible) reset. -/
theorem counter_cross {g : GenBuchi State Symbol} {cc : ℕ → Fin (g.k + 1)}
    {ss : ωSequence State}
    (hstep : ∀ n, cc (n + 1) = g.nextCount (cc n) (ss (n + 1))) :
    ∀ b a d, a ≤ b → (cc a).val = 0 → (cc b).val = d → ∀ (hd : d ≤ g.k),
      (∀ s, a < s → s < b → (cc s).val ≠ g.k) → ∀ (j : ℕ) (hj : j < d),
      ∃ s, a ≤ s ∧ s < b ∧ (cc s).val = j ∧ (cc (s + 1)).val = j + 1 ∧
        ss (s + 1) ∈ g.accept ⟨j, Nat.lt_of_lt_of_le hj hd⟩ := by
  intro b
  induction b with
  | zero =>
    intro a d hab ha hb _hd _ j hj
    have ha0 : a = 0 := by omega
    subst ha0
    have hd0 : d = 0 := by omega
    rw [hd0] at hj
    exact absurd hj (Nat.not_lt_zero j)
  | succ b ih =>
    intro a d hab ha hb hd hnok j hj
    by_cases hab' : a = b + 1
    · subst hab'
      have hd0 : d = 0 := by omega
      rw [hd0] at hj
      exact absurd hj (Nat.not_lt_zero j)
    · have hab2 : a ≤ b := by omega
      by_cases hcc : (cc b).val = g.k
      · have h0 : (cc (b + 1)).val = 0 := by
          rw [hstep b, nextCount_eq_zero hcc]
        have hd0 : d = 0 := by omega
        rw [hd0] at hj
        exact absurd hj (Nat.not_lt_zero j)
      · have hlt : (cc b).val < g.k := by have := (cc b).isLt; omega
        by_cases hmem : ss (b + 1) ∈ g.accept ⟨(cc b).val, hlt⟩
        · have hadv : (cc (b + 1)).val = (cc b).val + 1 := by
            rw [hstep b, nextCount_eq_succ hlt hmem]
          by_cases hjb : j = (cc b).val
          · refine ⟨b, hab2, by omega, hjb.symm, by omega, ?_⟩
            have hfin : (⟨(cc b).val, hlt⟩ : Fin g.k) = ⟨j, Nat.lt_of_lt_of_le hj hd⟩ :=
              Fin.ext hjb.symm
            exact hfin ▸ hmem
          · obtain ⟨s, hs1, hs2, hs3, hs4, hs5⟩ :=
              ih a (cc b).val hab2 ha rfl (by omega)
                (fun s hs1 hs2 => hnok s hs1 (by omega)) j (by omega)
            exact ⟨s, hs1, by omega, hs3, hs4, hs5⟩
        · have hstay : (cc (b + 1)).val = (cc b).val := by
            rw [hstep b, nextCount_eq_self hlt hmem]
          obtain ⟨s, hs1, hs2, hs3, hs4, hs5⟩ :=
            ih a d hab2 ha (by omega) hd
              (fun s hs1 hs2 => hnok s hs1 (by omega)) j hj
          exact ⟨s, hs1, by omega, hs3, hs4, hs5⟩

/-- The degeneralized Büchi automaton: states are pairs of a state of `g` with a
counter in `Fin (k + 1)`; the counter updates by `nextCount`, the start states
have counter `0`, and the accepting states have counter `k`. -/
def toBuchi (g : GenBuchi State Symbol) : Buchi (State × Fin (g.k + 1)) Symbol where
  Tr p x q := g.Tr p.1 x q.1 ∧ q.2 = g.nextCount p.2 q.1
  start := {p | p.1 ∈ g.start ∧ p.2 = ⟨0, Nat.zero_lt_succ _⟩}
  accept := {p | p.2.val = g.k}

/-- **Degeneralization preserves the language.** A word is accepted by the
degeneralized Büchi automaton iff it is accepted by the generalized Büchi
automaton. -/
theorem language_toBuchi (g : GenBuchi State Symbol) :
    language g.toBuchi = language g := by
  apply ωLanguage.mem_ext
  intro xs
  rw [mem_language_iff, mem_language]
  constructor
  · rintro ⟨tt, hrun, hacc⟩
    -- Project the product run to a run of `g` and its counter sequence.
    refine ⟨(fun n => (tt n).1 : ℕ → State), ⟨?_, ?_⟩, ?_⟩
    · exact hrun.start.1
    · intro i
      exact (hrun.trans i).1
    · intro j
      -- To see `F j` infinitely often, take two consecutive visits of the
      -- product run to counter `k` and apply `counter_cross` between them.
      rw [frequently_atTop]
      intro N
      obtain ⟨t1, _ht1ge, ht1acc⟩ := frequently_atTop.mp hacc (N + 1)
      have ht1val : (tt t1).2.val = g.k := ht1acc
      -- The next visit to counter `k` after `t1`.
      have hex : ∃ t2, t1 < t2 ∧ (tt t2).2.val = g.k := by
        obtain ⟨t2, ht2ge, ht2acc⟩ := frequently_atTop.mp hacc (t1 + 1)
        exact ⟨t2, by omega, ht2acc⟩
      obtain ⟨t2, _ht2gt, ht2val, ht2min⟩ :
          ∃ t2, t1 < t2 ∧ (tt t2).2.val = g.k ∧
            ∀ m, t1 < m → m < t2 → (tt m).2.val ≠ g.k :=
        ⟨Nat.find hex, Nat.find_spec hex |>.1, Nat.find_spec hex |>.2,
          fun m hm1 hm2 hval => Nat.find_min hex hm2 ⟨hm1, hval⟩⟩
      -- After a visit to `k`, the counter resets to `0`.
      have hreset : (tt (t1 + 1)).2.val = 0 := by
        have htr := (hrun.trans t1).2
        rw [nextCount_eq_zero ht1val] at htr
        rw [htr]
      obtain ⟨s, _hs1, _hs2, _hs3, _hs4, hs5⟩ :=
        counter_cross (g := g) (cc := fun n => (tt n).2) (ss := fun n => (tt n).1)
          (fun n => (hrun.trans n).2) (t2) (t1 + 1) g.k (by omega) hreset ht2val
          (by omega) (fun s hs1 hs2 => ht2min s (by omega) hs2) j.val j.isLt
      exact ⟨s + 1, by omega, hs5⟩
  · rintro ⟨ss, hrun, hacc⟩
    -- Pair the run with its counter sequence.
    refine ⟨(fun n => (ss n, g.countSeq ss n) : ℕ → State × Fin (g.k + 1)),
      ⟨?_, ?_⟩, ?_⟩
    · exact ⟨hrun.start, rfl⟩
    · intro i
      exact ⟨hrun.trans i, rfl⟩
    · rw [frequently_atTop]
      intro N
      obtain ⟨m, hmge, hmval⟩ :=
        countSeq_reach hacc (g.k - (g.countSeq ss N).val) N g.k (by omega)
          (by have := (g.countSeq ss N).isLt; omega) (le_refl _)
      exact ⟨m, hmge, hmval⟩

end GenBuchi

end Cslib.Automata.NA
