/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Consistent cuts
-/
module

public import CSLibExt.Computability.Distributed.VectorClock
public import Mathlib.Order.SupClosed
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Set.Finite.Basic

/-!
# Consistent cuts and their lattice

Cuts and consistent cuts of a distributed computation (F. Mattern, *Virtual time and global
states of distributed systems*, 1989), over the executions of `LamportClock.lean`. The events of
an execution `tr` are its positions `Fin tr.length`; happened-before is the transitive closure of
process order and message order (`LamportClock.HappensBefore`), and the vector timestamps are
those of `VectorClock.timestamps`. The initial event of a process is its first event. An
execution lists the events of a computation in one order that extends happened-before. Every
finite computation in which each process runs a sequence of events, each receipt receives one
message sent by another event, and causality is acyclic can be listed so.

* `IsCut`: a set of events that contains the initial event of every process and, with any event
  of a process, all earlier events of the same process.
* `IsConsistentCut`: a cut that is left-closed under happened-before.
* `globalTime`: the componentwise maximum of the vector timestamps of the events of a set.
* `isConsistentCut_iff_vectorTime`: Mattern's vector-time criterion: a cut with last events
  `c p` is consistent exactly when `C(c q) p ≤ C(c p) p` for all processes `p` and `q`, that is,
  when the componentwise supremum of the `C(c p)` is `fun p => C(c p) p`.
* `consistentCuts_lattice`: the cuts form a sublattice of the lattice of sets of events; on a
  well-formed execution a cut is consistent exactly when every message received in it was sent
  in it; the consistent cuts form a sublattice of the cuts, so finitely many of them (at least
  one) have a consistent union and intersection; a cut with last events `c p` is consistent
  exactly when its global time is `fun i => C(c i) i`, that is, when `C(c j) i ≤ C(c i) i` for
  all processes `i` and `j`; and `X ↦ globalTime tr X` is an isomorphism from the lattice of
  consistent cuts onto the lattice of possible time vectors, ordered componentwise.

## References

* F. Mattern, *Virtual time and global states of distributed systems*, in M. Cosnard et al.
  (eds.), *Parallel and Distributed Algorithms*, North-Holland, 1989; edited version at
  <https://www.vs.inf.ethz.ch/publ/papers/VirtTimeGlobStates.pdf>, whose numbering this follows:
  Sections 3, 7 and 8.
-/

@[expose] public section

namespace Cslib.Distributed.ConsistentCut

open LamportClock (Event WellFormed Step HappensBefore)
open VectorClock

variable {P : Type*}

/-- **Cut of an execution.** Let $e_0, \dots, e_{N-1}$ be an execution, with events indexed by
their positions $0, \dots, N - 1$. The *initial event* of a process is its first event in the
execution. A *cut* is a set $C$ of positions that contains the initial event of every process
and, with any event of a process, all earlier events of the same process. -/
def IsCut (tr : List (Event P)) (C : Set (Fin tr.length)) : Prop :=
  (∀ a : Fin tr.length, (∀ b < a, tr[b].proc ≠ tr[a].proc) → a ∈ C) ∧
    ∀ a b : Fin tr.length, b ∈ C → tr[a].proc = tr[b].proc → a < b → a ∈ C

/-- **Consistent cut.** A cut $C$ of an execution is *consistent* when it is left-closed under
Lamport's happened-before relation $<$: if $b \in C$ and $a < b$, then $a \in C$. -/
def IsConsistentCut (tr : List (Event P)) (C : Set (Fin tr.length)) : Prop :=
  IsCut tr C ∧ ∀ a b : Fin tr.length, b ∈ C → HappensBefore tr a b → a ∈ C

variable {tr : List (Event P)}

private theorem getElem?_fin (a : Fin tr.length) : tr[(a : ℕ)]? = some tr[a] :=
  List.getElem?_eq_getElem a.2

private theorem step_of_proc_eq {a b : Fin tr.length} (hab : a < b) (h : tr[a].proc = tr[b].proc) :
    Step tr a b :=
  ⟨hab, tr[a], tr[b], getElem?_fin a, getElem?_fin b, Or.inl h⟩

theorem isConsistentCut_iff_recv (hwf : WellFormed tr) {C : Set (Fin tr.length)}
    (hC : IsCut tr C) :
    IsConsistentCut tr C ↔
      ∀ a b : Fin tr.length, b ∈ C → tr[b].recvFrom = some (a : ℕ) → a ∈ C := by
  constructor
  · rintro ⟨-, hX⟩ a b hb hr
    exact hX a b hb (.single ⟨hwf b tr[b] a (getElem?_fin b) hr, tr[a], tr[b], getElem?_fin a,
      getElem?_fin b, Or.inr hr⟩)
  · intro hrecv
    have hstep : ∀ i j : ℕ, Step tr i j → ∀ hj : j < tr.length, (⟨j, hj⟩ : Fin tr.length) ∈ C →
        ∀ hi : i < tr.length, (⟨i, hi⟩ : Fin tr.length) ∈ C := by
      rintro i j ⟨hij, ei, ej, hi', hj', hrel⟩ hj hjC hi
      have hei : tr[(⟨i, hi⟩ : Fin tr.length)] = ei := by
        simpa [getElem?_fin] using (getElem?_fin (tr := tr) ⟨i, hi⟩).symm.trans hi'
      have hej : tr[(⟨j, hj⟩ : Fin tr.length)] = ej := by
        simpa [getElem?_fin] using (getElem?_fin (tr := tr) ⟨j, hj⟩).symm.trans hj'
      rcases hrel with hp | hr
      · exact hC.2 _ _ hjC (by rw [hei, hej, hp]) hij
      · exact hrecv _ _ hjC (by rw [hej, hr])
    refine ⟨hC, fun a b hb hab => ?_⟩
    have key : ∀ y, HappensBefore tr a y → ∀ hy : y < tr.length,
        (⟨y, hy⟩ : Fin tr.length) ∈ C → a ∈ C := by
      intro y hy
      induction hy with
      | single hs => exact fun hy hyC => hstep _ _ hs hy hyC a.2
      | @tail b' c' _ hs ih =>
          exact fun hc hcC => ih (lt_trans hs.1 hc) (hstep _ _ hs hc hcC _)
    exact key b hab b.2 hb

theorem isSublattice_isCut : IsSublattice {C | IsCut tr C} where
  supClosed := by
    rintro C ⟨hC₁, hC₂⟩ D ⟨hD₁, hD₂⟩
    refine ⟨fun a ha => Or.inl (hC₁ a ha), fun a b hb hab hlt => ?_⟩
    rcases hb with hb | hb
    · exact Or.inl (hC₂ a b hb hab hlt)
    · exact Or.inr (hD₂ a b hb hab hlt)
  infClosed := by
    rintro C ⟨hC₁, hC₂⟩ D ⟨hD₁, hD₂⟩
    exact ⟨fun a ha => ⟨hC₁ a ha, hD₁ a ha⟩,
      fun a b hb hab hlt => ⟨hC₂ a b hb.1 hab hlt, hD₂ a b hb.2 hab hlt⟩⟩

theorem isSublattice_isConsistentCut : IsSublattice {C | IsConsistentCut tr C} where
  supClosed := by
    rintro C ⟨hC, hC'⟩ D ⟨hD, hD'⟩
    refine ⟨isSublattice_isCut.supClosed hC hD, fun a b hb hab => ?_⟩
    rcases hb with hb | hb
    · exact Or.inl (hC' a b hb hab)
    · exact Or.inr (hD' a b hb hab)
  infClosed := by
    rintro C ⟨hC, hC'⟩ D ⟨hD, hD'⟩
    exact ⟨isSublattice_isCut.infClosed hC hD,
      fun a b hb hab => ⟨hC' a b hb.1 hab, hD' a b hb.2 hab⟩⟩

theorem isConsistentCut_biUnion {S : Finset (Set (Fin tr.length))} (hS : S.Nonempty)
    (h : ∀ C ∈ S, IsConsistentCut tr C) : IsConsistentCut tr (⋃ C ∈ S, C) := by
  obtain ⟨C₀, hC₀⟩ := hS
  refine ⟨⟨fun a ha => Set.mem_biUnion hC₀ ((h C₀ hC₀).1.1 a ha), fun a b hb hab hlt => ?_⟩,
    fun a b hb hab => ?_⟩
  · obtain ⟨C, hC, hbC⟩ := Set.mem_iUnion₂.1 hb
    exact Set.mem_biUnion hC ((h C hC).1.2 a b hbC hab hlt)
  · obtain ⟨C, hC, hbC⟩ := Set.mem_iUnion₂.1 hb
    exact Set.mem_biUnion hC ((h C hC).2 a b hbC hab)

theorem isConsistentCut_biInter {S : Finset (Set (Fin tr.length))}
    (h : ∀ C ∈ S, IsConsistentCut tr C) : IsConsistentCut tr (⋂ C ∈ S, C) := by
  refine ⟨⟨fun a ha => Set.mem_iInter₂.2 fun C hC => (h C hC).1.1 a ha,
    fun a b hb hab hlt => Set.mem_iInter₂.2 fun C hC => ?_⟩,
    fun a b hb hab => Set.mem_iInter₂.2 fun C hC => ?_⟩
  · exact (h C hC).1.2 a b (Set.mem_iInter₂.1 hb C hC) hab hlt
  · exact (h C hC).2 a b (Set.mem_iInter₂.1 hb C hC) hab

section GlobalTime

variable [DecidableEq P]

/-- **Global time of a set of events.** For a set $X$ of positions of an execution of a set $P$
of processes, the global time $t_X \in \mathbb{N}^P$ is the componentwise maximum of the vector
timestamps $C(e)$ that the vector clock algorithm assigns to the events $e \in X$, and the zero
vector if $X$ is empty. -/
noncomputable def globalTime (tr : List (Event P)) (X : Set (Fin tr.length)) : P → ℕ :=
  X.toFinite.toFinset.sup fun a => (timestamps tr).getD a 0

/- A nonzero entry `q` of a vector timestamp is at most the same entry of the timestamp of an
event of `q` that is the event itself or happened before it. -/
theorem exists_proc_eq_le_of_ne_zero :
    ∀ (b : ℕ) (q : P), (timestamps tr).getD b 0 q ≠ 0 →
      ∃ e ee, tr[e]? = some ee ∧ ee.proc = q ∧ (e = b ∨ HappensBefore tr e b) ∧
        (timestamps tr).getD b 0 q ≤ (timestamps tr).getD e 0 q := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro q hne
    cases hb : tr[b]? with
    | none =>
        exfalso
        apply hne
        have : tr.length ≤ b := List.getElem?_eq_none_iff.mp hb
        rw [List.getD_eq_default _ _ (by rw [length_timestamps]; exact this)]
        rfl
    | some eb =>
      have hblen : b < tr.length := (List.getElem?_eq_some_iff.mp hb).1
      by_cases hp : eb.proc = q
      · exact ⟨b, eb, hb, hp, Or.inl rfl, le_rfl⟩
      · have hval := timestamps_getD_eq_stamp hb
        have hq : q ≠ eb.proc := Ne.symm hp
        have hle : (timestamps tr).getD b 0 q ≤
            max ((run (tr.take b)).1 eb.proc q)
              ((eb.recvFrom.map fun i => ((run (tr.take b)).2[i]?.getD 0) q).getD 0) := by
          rw [hval]
          simp only [stamp, Function.update_of_ne hq, le_refl]
        rcases le_max_iff.mp hle with hv | hr
        · rcases vector_eq (tr.take b) eb.proc with h0 | ⟨j, ej, hj, hjp, hv'⟩
          · rw [h0, Pi.zero_apply] at hv
            omega
          · have hjb : j < b := by
              have := (List.getElem?_eq_some_iff.mp hj).1
              rw [List.length_take] at this
              omega
            have hj' : tr[j]? = some ej := by rw [List.getElem?_take_of_lt hjb] at hj; exact hj
            rw [hv', ← timestamps_getD_take tr hjb hblen.le] at hv
            have hstep : Step tr j b := ⟨hjb, ej, eb, hj', hb, Or.inl hjp⟩
            obtain ⟨e, ee, he, hep, hrel, hle'⟩ := ih j hjb q (by omega)
            refine ⟨e, ee, he, hep, Or.inr ?_, hv.trans hle'⟩
            rcases hrel with rfl | hej
            · exact .single hstep
            · exact .tail hej hstep
        · cases hrecv : eb.recvFrom with
          | none =>
              rw [hrecv, Option.map_none, Option.getD_none] at hr
              omega
          | some i =>
              rw [hrecv] at hr
              simp only [Option.map_some, Option.getD_some] at hr
              by_cases hib : i < b
              · obtain ⟨ei, hi⟩ : ∃ ei, tr[i]? = some ei :=
                  ⟨tr[i], List.getElem?_eq_getElem (by omega)⟩
                rw [run_getD, ← timestamps_getD_take tr hib hblen.le] at hr
                have hstep : Step tr i b := ⟨hib, ei, eb, hi, hb, Or.inr hrecv⟩
                obtain ⟨e, ee, he, hep, hrel, hle'⟩ := ih i hib q (by omega)
                refine ⟨e, ee, he, hep, Or.inr ?_, hr.trans hle'⟩
                rcases hrel with rfl | hei
                · exact .single hstep
                · exact .tail hei hstep
              · have : (run (tr.take b)).2[i]?.getD 0 = 0 := by
                  rw [run_getD, List.getD_eq_default]
                  rw [length_timestamps]
                  simp
                  omega
                rw [this, Pi.zero_apply] at hr
                omega

theorem globalTime_apply (X : Set (Fin tr.length)) (q : P) :
    globalTime tr X q = X.toFinite.toFinset.sup fun a => (timestamps tr).getD a 0 q :=
  Finset.sup_apply _ _ _

theorem le_globalTime {X : Set (Fin tr.length)} {a : Fin tr.length} (ha : a ∈ X) :
    (timestamps tr).getD a 0 ≤ globalTime tr X :=
  Finset.le_sup (f := fun a : Fin tr.length => (timestamps tr).getD a 0)
    ((Set.Finite.mem_toFinset _).2 ha)

theorem globalTime_mono {X Y : Set (Fin tr.length)} (h : X ⊆ Y) :
    globalTime tr X ≤ globalTime tr Y :=
  Finset.sup_le fun _ ha => le_globalTime (h ((Set.Finite.mem_toFinset _).1 ha))

theorem globalTime_union (X Y : Set (Fin tr.length)) :
    globalTime tr (X ∪ Y) = globalTime tr X ⊔ globalTime tr Y := by
  refine le_antisymm (Finset.sup_le fun a ha => ?_)
    (sup_le (globalTime_mono Set.subset_union_left) (globalTime_mono Set.subset_union_right))
  rcases (Set.Finite.mem_toFinset _).1 ha with ha | ha
  · exact (le_globalTime ha).trans le_sup_left
  · exact (le_globalTime ha).trans le_sup_right

/- In a set left-closed under happened-before, a nonzero entry `q` of the global time is at
most the same entry of the timestamp of an event of `q` in the set. -/
theorem exists_mem_le_globalTime {X : Set (Fin tr.length)}
    (hX : ∀ a b : Fin tr.length, b ∈ X → HappensBefore tr a b → a ∈ X) (q : P)
    (hne : globalTime tr X q ≠ 0) :
    ∃ e ∈ X, tr[e].proc = q ∧ globalTime tr X q ≤ (timestamps tr).getD e 0 q := by
  have hpos : ⊥ < globalTime tr X q := Nat.pos_of_ne_zero hne
  obtain ⟨b, hb, hle⟩ := (Finset.le_sup_iff hpos).1 (globalTime_apply X q).le
  rw [Set.Finite.mem_toFinset] at hb
  obtain ⟨e, ee, he, hep, hrel, hle'⟩ := exists_proc_eq_le_of_ne_zero (tr := tr) b q (by omega)
  have helen : e < tr.length := (List.getElem?_eq_some_iff.mp he).1
  have hee : tr[(⟨e, helen⟩ : Fin tr.length)] = ee := by
    simpa [getElem?_fin] using (getElem?_fin (tr := tr) ⟨e, helen⟩).symm.trans he
  refine ⟨⟨e, helen⟩, ?_, by rw [hee, hep], hle.trans hle'⟩
  rcases hrel with h | h
  · obtain rfl : (⟨e, helen⟩ : Fin tr.length) = b := Fin.ext h
    exact hb
  · exact hX _ b hb h

/- In a set left-closed under happened-before, an event belongs to the set exactly when its
own entry of its timestamp is at most the same entry of the global time. -/
theorem mem_iff_le_globalTime {X : Set (Fin tr.length)}
    (hX : ∀ a b : Fin tr.length, b ∈ X → HappensBefore tr a b → a ∈ X) (a : Fin tr.length) :
    a ∈ X ↔ (timestamps tr).getD a 0 tr[a].proc ≤ globalTime tr X tr[a].proc := by
  refine ⟨fun ha => le_globalTime ha _, fun h => ?_⟩
  have hpos := one_le_own (getElem?_fin a)
  obtain ⟨e, he, hep, hle⟩ := exists_mem_le_globalTime hX tr[a].proc (by omega)
  rcases eq_or_happensBefore_of_le e (getElem?_fin a) (getElem?_fin e) (h.trans hle) with
    hae | hae
  · rwa [Fin.ext hae]
  · exact hX a e he hae

theorem subset_iff_globalTime_le {X Y : Set (Fin tr.length)}
    (hX : ∀ a b : Fin tr.length, b ∈ X → HappensBefore tr a b → a ∈ X)
    (hY : ∀ a b : Fin tr.length, b ∈ Y → HappensBefore tr a b → a ∈ Y) :
    X ⊆ Y ↔ globalTime tr X ≤ globalTime tr Y := by
  refine ⟨globalTime_mono, fun h a ha => ?_⟩
  exact (mem_iff_le_globalTime hY a).2 (((mem_iff_le_globalTime hX a).1 ha).trans (h _))

theorem le_globalTime_inter {X Y : Set (Fin tr.length)}
    (hX : ∀ a b : Fin tr.length, b ∈ X → HappensBefore tr a b → a ∈ X)
    (hY : ∀ a b : Fin tr.length, b ∈ Y → HappensBefore tr a b → a ∈ Y) {q : P}
    (hq : globalTime tr X q ≤ globalTime tr Y q) :
    globalTime tr X q ≤ globalTime tr (X ∩ Y) q := by
  by_cases h0 : globalTime tr X q = 0
  · rw [h0]
    exact Nat.zero_le _
  obtain ⟨e, he, hep, hle⟩ := exists_mem_le_globalTime hX q h0
  have heY : e ∈ Y := by
    rw [mem_iff_le_globalTime hY, hep]
    exact (le_globalTime he q).trans hq
  exact hle.trans (le_globalTime (show e ∈ X ∩ Y from ⟨he, heY⟩) q)

theorem globalTime_inter {X Y : Set (Fin tr.length)}
    (hX : ∀ a b : Fin tr.length, b ∈ X → HappensBefore tr a b → a ∈ X)
    (hY : ∀ a b : Fin tr.length, b ∈ Y → HappensBefore tr a b → a ∈ Y) :
    globalTime tr (X ∩ Y) = globalTime tr X ⊓ globalTime tr Y := by
  refine le_antisymm
    (le_inf (globalTime_mono Set.inter_subset_left) (globalTime_mono Set.inter_subset_right))
    fun q => ?_
  rw [Pi.inf_apply]
  rcases le_total (globalTime tr X q) (globalTime tr Y q) with hq | hq
  · exact inf_le_left.trans (le_globalTime_inter hX hY hq)
  · rw [Set.inter_comm]
    exact inf_le_right.trans (le_globalTime_inter hY hX hq)

/- The global time of a set is the componentwise maximum of the timestamps of the last events
of the processes in it. -/
theorem globalTime_eq_sup [Fintype P] {X : Set (Fin tr.length)} {c : P → Fin tr.length}
    (hc : ∀ p, c p ∈ X ∧ tr[c p].proc = p ∧ ∀ a ∈ X, tr[a].proc = p → a ≤ c p) :
    globalTime tr X = Finset.univ.sup fun p => (timestamps tr).getD (c p) 0 := by
  refine le_antisymm (Finset.sup_le fun a ha => ?_)
    (Finset.sup_le fun p _ => le_globalTime (hc p).1)
  rw [Set.Finite.mem_toFinset] at ha
  have hle : a ≤ c tr[a].proc := (hc _).2.2 a ha rfl
  refine le_trans ?_ (Finset.le_sup (f := fun p => (timestamps tr).getD (c p) 0)
    (Finset.mem_univ tr[a].proc))
  rcases hle.lt_or_eq with hlt | heq
  · exact vectorClock_le_of_step (step_of_proc_eq hlt ((hc _).2.1).symm)
  · simp only [← heq, le_refl]

/- Mattern's consistency criterion: a cut with last events `c p` is consistent exactly when
`C(c j) i ≤ C(c i) i` for all processes `i` and `j`. -/
theorem isConsistentCut_iff_le {X : Set (Fin tr.length)} {c : P → Fin tr.length}
    (hXc : IsCut tr X)
    (hc : ∀ p, c p ∈ X ∧ tr[c p].proc = p ∧ ∀ a ∈ X, tr[a].proc = p → a ≤ c p) :
    IsConsistentCut tr X ↔
      ∀ i j, (timestamps tr).getD (c j) 0 i ≤ (timestamps tr).getD (c i) 0 i := by
  constructor
  · rintro ⟨-, hX⟩ i j
    by_cases h0 : (timestamps tr).getD (c j) 0 i = 0
    · rw [h0]
      exact Nat.zero_le _
    obtain ⟨e, ee, he, hep, hrel, hle⟩ := exists_proc_eq_le_of_ne_zero (tr := tr) (c j) i h0
    have helen : e < tr.length := (List.getElem?_eq_some_iff.mp he).1
    set e' : Fin tr.length := ⟨e, helen⟩
    have hee : tr[e'] = ee := by
      simpa [getElem?_fin] using (getElem?_fin (tr := tr) e').symm.trans he
    have he'X : e' ∈ X := by
      rcases hrel with h | h
      · rw [show e' = c j from Fin.ext h]
        exact (hc j).1
      · exact hX e' (c j) (hc j).1 h
    have hei : tr[e'].proc = i := by rw [hee, hep]
    refine hle.trans ?_
    rcases ((hc i).2.2 e' he'X hei).lt_or_eq with hlt | heq
    · exact vectorClock_le_of_step (step_of_proc_eq hlt (hei.trans (hc i).2.1.symm)) i
    · change (timestamps tr).getD e' 0 i ≤ _
      rw [heq]
  · intro h
    refine ⟨hXc, fun a b hb hab => ?_⟩
    have hbc : HappensBefore tr a (c tr[b].proc) := by
      rcases ((hc _).2.2 b hb rfl).lt_or_eq with hlt | heq
      · exact .tail hab (step_of_proc_eq hlt (hc _).2.1.symm)
      · rwa [← heq]
    have h1 := vectorClock_le_of_happensBefore hbc tr[a].proc
    rcases eq_or_happensBefore_of_le (c tr[a].proc) (getElem?_fin a) (getElem?_fin _)
        (h1.trans (h _ _)) with hac | hac
    · rw [Fin.ext hac]
      exact (hc _).1
    · exact hXc.2 a _ (hc _).1 (hc _).2.1.symm hac.lt

/-- **Vector-time criterion for consistent cuts.** Let $X$ be a cut of an execution of a finite
set $P$ of processes, with last event $c_p$ on each process $p$, and let $C(e) \in \mathbb{N}^P$ be
the vector timestamps that the vector clock algorithm assigns to the events. Then $X$ is
consistent if and only if $C(c_q)[p] \le C(c_p)[p]$ for all processes $p$ and $q$, and if and only
if the componentwise supremum of $C(c_p)$ over $p \in P$ equals $(C(c_p)[p])_{p \in P}$. The
execution need not be well formed, and a message may be received by several events. -/
theorem isConsistentCut_iff_vectorTime [Fintype P] {X : Set (Fin tr.length)}
    {c : P → Fin tr.length} (hX : IsCut tr X)
    (hc : ∀ p, c p ∈ X ∧ tr[c p].proc = p ∧ ∀ a ∈ X, tr[a].proc = p → a ≤ c p) :
    (IsConsistentCut tr X ↔
      ∀ p q, (timestamps tr).getD (c q) 0 p ≤ (timestamps tr).getD (c p) 0 p) ∧
    (IsConsistentCut tr X ↔ (Finset.univ.sup fun p => (timestamps tr).getD (c p) 0) =
      fun p => (timestamps tr).getD (c p) 0 p) := by
  refine ⟨isConsistentCut_iff_le hX hc, ?_⟩
  rw [isConsistentCut_iff_le hX hc, funext_iff]
  refine forall_congr' fun i => ?_
  rw [Finset.sup_apply]
  constructor
  · intro h
    exact le_antisymm (Finset.sup_le fun j _ => h j)
      (Finset.le_sup (f := fun p => (timestamps tr).getD (c p) 0 i) (Finset.mem_univ i))
  · intro h j
    rw [← h]
    exact Finset.le_sup (f := fun p => (timestamps tr).getD (c p) 0 i) (Finset.mem_univ j)

theorem isSublattice_image_globalTime :
    IsSublattice (globalTime tr '' {C | IsConsistentCut tr C}) where
  supClosed := by
    rintro _ ⟨X, hX, rfl⟩ _ ⟨Y, hY, rfl⟩
    exact ⟨X ∪ Y, isSublattice_isConsistentCut.supClosed hX hY, globalTime_union X Y⟩
  infClosed := by
    rintro _ ⟨X, hX, rfl⟩ _ ⟨Y, hY, rfl⟩
    exact ⟨X ∩ Y, isSublattice_isConsistentCut.infClosed hX hY, globalTime_inter hX.2 hY.2⟩

/-- **Consistent cuts and their lattice.** Let $e_0, \dots, e_{N-1}$ be a well-formed execution
of a finite set $P$ of processes. Its events, identified with their positions, are partially
ordered by Lamport's happened-before relation $<$, the transitive closure of process order and
message order, and carry vector timestamps $C(e) \in \mathbb{N}^P$. The initial event of a
process is its first event; a process need not have any events.

1. The cuts are closed under union and intersection, so they form a lattice.
2. A cut $C$ is consistent if and only if every message received in $C$ was sent in $C$: if
   $b \in C$ receives the message sent by $a$, then $a \in C$.
3. The consistent cuts are cuts and are closed under union and intersection, so they form a
   sublattice of the lattice of cuts. For every nonempty finite set $S$ of consistent cuts, the
   union and the intersection of the members of $S$ are consistent cuts, the union later than
   (containing) and the intersection earlier than (contained in) each member of $S$.
4. Let $X$ be a cut whose last event on each process $i$ is $c_i$. Its global time $t_X$, the
   componentwise maximum of the timestamps of its events, is $\sup_{i \in P} C(c_i)$, and $X$ is
   consistent if and only if $t_X = (C(c_i)[i])_{i \in P}$, and if and only if
   $C(c_j)[i] \le C(c_i)[i]$ for all processes $i$ and $j$.
5. The possible time vectors, the global times of the consistent cuts, form a sublattice of
   $\mathbb{N}^P$ ordered componentwise. The map $X \mapsto t_X$ sends the union and the
   intersection of two consistent cuts to the componentwise maximum and minimum of their global
   times, and is an order isomorphism from the consistent cuts, ordered by inclusion, onto the
   possible time vectors. -/
theorem consistentCuts_lattice [Fintype P] (hwf : WellFormed tr) :
    IsSublattice {C | IsCut tr C} ∧
    (∀ C, IsCut tr C → (IsConsistentCut tr C ↔
      ∀ a b : Fin tr.length, b ∈ C → tr[b].recvFrom = some (a : ℕ) → a ∈ C)) ∧
    ({C | IsConsistentCut tr C} ⊆ {C | IsCut tr C} ∧ IsSublattice {C | IsConsistentCut tr C} ∧
      ∀ S : Finset (Set (Fin tr.length)), S.Nonempty → (∀ C ∈ S, IsConsistentCut tr C) →
        IsConsistentCut tr (⋃ C ∈ S, C) ∧ IsConsistentCut tr (⋂ C ∈ S, C) ∧
          ∀ C ∈ S, C ⊆ ⋃ D ∈ S, D ∧ ⋂ D ∈ S, D ⊆ C) ∧
    (∀ (X : Set (Fin tr.length)) (c : P → Fin tr.length), IsCut tr X →
      (∀ p, c p ∈ X ∧ tr[c p].proc = p ∧ ∀ a ∈ X, tr[a].proc = p → a ≤ c p) →
      globalTime tr X = Finset.univ.sup (fun p => (timestamps tr).getD (c p) 0) ∧
      (IsConsistentCut tr X ↔ globalTime tr X = fun i => (timestamps tr).getD (c i) 0 i) ∧
      (IsConsistentCut tr X ↔
        ∀ i j, (timestamps tr).getD (c j) 0 i ≤ (timestamps tr).getD (c i) 0 i)) ∧
    IsSublattice (globalTime tr '' {C | IsConsistentCut tr C}) ∧
    (∀ X Y, IsConsistentCut tr X → IsConsistentCut tr Y →
      globalTime tr (X ∪ Y) = globalTime tr X ⊔ globalTime tr Y ∧
      globalTime tr (X ∩ Y) = globalTime tr X ⊓ globalTime tr Y) ∧
    ∃ e : {C : Set (Fin tr.length) // IsConsistentCut tr C} ≃o
        globalTime tr '' {C | IsConsistentCut tr C},
      ∀ X, (e X : P → ℕ) = globalTime tr X := by
  refine ⟨isSublattice_isCut, fun C hC => isConsistentCut_iff_recv hwf hC,
    ⟨fun C hC => hC.1, isSublattice_isConsistentCut, fun S hS h =>
      ⟨isConsistentCut_biUnion hS h, isConsistentCut_biInter h, fun C hC =>
        ⟨Set.subset_biUnion_of_mem (u := id) hC, Set.biInter_subset_of_mem (t := id) hC⟩⟩⟩,
    fun X c hX hc => ⟨globalTime_eq_sup hc,
      by rw [globalTime_eq_sup hc]; exact (isConsistentCut_iff_vectorTime hX hc).2,
      (isConsistentCut_iff_vectorTime hX hc).1⟩,
    isSublattice_image_globalTime,
    fun X Y hX hY => ⟨globalTime_union X Y, globalTime_inter hX.2 hY.2⟩, ?_⟩
  let f : {C : Set (Fin tr.length) // IsConsistentCut tr C} →
      globalTime tr '' {C | IsConsistentCut tr C} :=
    fun X => ⟨globalTime tr X, X, X.2, rfl⟩
  have hle : ∀ X Y, f X ≤ f Y ↔ X ≤ Y := fun X Y =>
    (subset_iff_globalTime_le X.2.2 Y.2.2).symm
  have hinj : Function.Injective f := fun X Y h =>
    le_antisymm ((hle X Y).1 h.le) ((hle Y X).1 h.ge)
  have hsurj : Function.Surjective f := by
    rintro ⟨_, X, hX, rfl⟩
    exact ⟨⟨X, hX⟩, rfl⟩
  exact ⟨{ toEquiv := Equiv.ofBijective f ⟨hinj, hsurj⟩, map_rel_iff' := hle _ _ },
    fun X => rfl⟩

end GlobalTime

end Cslib.Distributed.ConsistentCut
