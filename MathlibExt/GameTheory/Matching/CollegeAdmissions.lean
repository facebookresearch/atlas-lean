/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.Matching.RuralHospitals
public import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Fin

/-! # College admissions by quota slots

A feasible college assignment sends each student to at most one college and respects the
college quotas. We use the pairwise implications of responsive preferences (acceptance into a
vacancy and replacement of one incumbent), not a ranking of all sets of students. Following
A. E. Roth, *Deferred acceptance algorithms: history, theory, practice, and open questions*,
International Journal of Game Theory 36 (2008), §2.2 (author manuscript, pp. 10–11), we replace
each college by unit-capacity copies. We refine each block of copies by increasing index for
every student. This makes a stable assignment of copies unique over its college assignment.
-/

@[expose] public section

namespace MathlibExt.GameTheory.Matching.CollegeAdmissions

open MathlibExt.Order
open MathlibExt.GameTheory.Matching.RuralHospitals

variable {S C : Type*} {q : C → ℕ}

/-- The unit-capacity copies of colleges with quotas `q`: copy `⟨c,i⟩` has index
`0 ≤ i < q c`. A zero-quota college has no copy. -/
abbrev Slot (q : C → ℕ) := (c : C) × Fin (q c)

/-- The index used to break a tie of projected colleges: the slot number on an actual copy,
and zero at `none` (where the only other outside option is itself). -/
def slotIndex (x : Option (Slot q)) : ℕ := x.elim 0 fun k => k.2.val

private theorem slot_ext {x y : Option (Slot q)} (hc : x.map Sigma.fst = y.map Sigma.fst)
    (hi : slotIndex x = slotIndex y) : x = y := by
  cases x with
  | none => cases y <;> simp_all
  | some x =>
    cases y with
    | none => simp at hc
    | some y =>
      obtain ⟨c, i⟩ := x
      obtain ⟨d, j⟩ := y
      simp only [Option.map_some, Option.some.injEq] at hc
      subst d
      have : i = j := Fin.ext hi
      subst j
      rfl

/-- A student's strict ranking of optional slots first compares the projected optional colleges
(`none` stays unmatched); within a college all students prefer the smaller index. Thus the whole
block is above, or below, being unmatched exactly when its college is. -/
def studentPrefs (q : C → ℕ) (sp : MPrefsSingle S C) : MPrefsSingle S (Slot q) := fun s => {
  lt := fun x y => (sp s).lt (x.map Sigma.fst) (y.map Sigma.fst) ∨
    x.map Sigma.fst = y.map Sigma.fst ∧ slotIndex x < slotIndex y
  irrefl := fun x => by simp [(sp s).irrefl]
  trans := by
    rintro x y z (h | ⟨e, h⟩) (k | ⟨f, k⟩)
    · exact Or.inl ((sp s).trans h k)
    · exact Or.inl (f ▸ h)
    · exact Or.inl (e.symm ▸ k)
    · exact Or.inr ⟨e.trans f, lt_trans h k⟩
  total := by
    intro x y h
    by_cases e : x.map Sigma.fst = y.map Sigma.fst
    · rcases lt_or_gt_of_ne (fun k => h (slot_ext e k)) with k | k
      · exact Or.inl (Or.inr ⟨e, k⟩)
      · exact Or.inr (Or.inr ⟨e.symm, k⟩)
    · exact ((sp s).total e).imp Or.inl Or.inl }

/-- Each unit-capacity copy compares students and leaving its seat empty by its college's
original strict order on `Option S`, independently of its index. -/
abbrev slotPrefs (q : C → ℕ) (cp : WPrefsSingle S C) : WPrefsSingle S (Slot q) := fun k => cp k.1

variable [Fintype S]

open Classical in
/-- The roster of `c` consists of exactly the students whose assignment is `some c`;
`none` is an unmatched student, not an extra college. -/
noncomputable def roster (a : S → Option C) (c : C) : Finset S :=
  Finset.univ.filter fun s => a s = some c

/-- Membership in a college roster is assignment to that particular college. -/
@[simp] theorem mem_roster {a : S → Option C} {c : C} {s : S} : s ∈ roster a c ↔ a s = some c := by
  classical
  simp [roster]

/-- A quota-feasible many-to-one matching: each student has one optional college, and for each
college `c` the number of students assigned to it is at most `q c`. Feasibility alone requires
neither acceptability nor absence of blocking pairs. -/
@[ext] structure Assignment (S C : Type*) [Fintype S] (q : C → ℕ) where
  /-- Each student's college, or `none` when unmatched. -/
  assign : S → Option C
  /-- Cardinality bound on each college's roster, including quota zero. -/
  capacity : ∀ c, (roster assign c).card ≤ q c

/-- A student and college block a feasible assignment if the student prefers the college to the
current assignment, and the college either finds the student acceptable and has a vacancy, or
prefers the student to an incumbent. -/
def Blocks (sp : MPrefsSingle S C) (cp : WPrefsSingle S C) (a : Assignment S C q) (s : S) (c : C) :
    Prop :=
  (sp s).lt (some c) (a.assign s) ∧
    (((roster a.assign c).card < q c ∧ (cp c).lt (some s) none) ∨
      ∃ t, a.assign t = some c ∧ (cp c).lt (some s) (some t))

/-- A feasible college assignment is pairwise stable if no student or college prefers the
outside option to an assigned partner and no student-college pair blocks by vacancy or
replacement. Empty seats and unmatched students are allowed, and the sides need not balance. -/
def IsStable (sp : MPrefsSingle S C) (cp : WPrefsSingle S C) (a : Assignment S C q) : Prop :=
  (∀ s, ¬ (sp s).lt none (a.assign s)) ∧
    (∀ s c, a.assign s = some c → ¬ (cp c).lt none (some s)) ∧ ∀ s c, ¬ Blocks sp cp a s c

/-- When `q c = 0`, feasibility forces the roster of `c` to be empty. -/
theorem roster_eq_empty_of_quota_zero (a : Assignment S C q) {c : C} (h : q c = 0) :
    roster a.assign c = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (h ▸ a.capacity c))

/-- No student can block with a zero-quota college: it has neither a vacancy nor an incumbent. -/
theorem not_blocks_of_quota_zero (sp : MPrefsSingle S C) (cp : WPrefsSingle S C)
    (a : Assignment S C q) {c : C} (h : q c = 0) (s : S) : ¬ Blocks sp cp a s c := by
  rintro ⟨_, ⟨v, _⟩ | ⟨t, ht, _⟩⟩
  · omega
  · have := mem_roster.mpr ht
    simp [roster_eq_empty_of_quota_zero a h] at this

omit [Fintype S] in
private theorem assigned_iff (ν : S ≃. Slot q) (s : S) (c : C) :
    (ν s).map Sigma.fst = some c ↔ ∃ i, ν s = some ⟨c, i⟩ := by
  cases h : ν s with
  | none => simp
  | some k =>
    obtain ⟨d, j⟩ := k
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨j, rfl⟩
    · rintro ⟨i, e⟩; exact congrArg Sigma.fst e

open Classical in
private noncomputable def indices (ν : S ≃. Slot q) (c : C) (p : S → Prop) : Finset (Fin (q c)) :=
  Finset.univ.filter fun i => ∃ s, ν s = some ⟨c, i⟩ ∧ p s

private theorem mem_indices {ν : S ≃. Slot q} {c : C} {p : S → Prop} {i : Fin (q c)} :
    i ∈ indices ν c p ↔ ∃ s, ν s = some ⟨c, i⟩ ∧ p s := by classical simp [indices]

-- Count any sub-roster by its occupied indices. The same bijective count handles both
-- vacancies (all incumbents) and rank (just the incumbents preferred to a given student).
open Classical in
private theorem count_indices (ν : S ≃. Slot q) (c : C) (p : S → Prop) :
    ((roster (fun s => (ν s).map Sigma.fst) c).filter p).card = (indices ν c p).card := by
  classical
  let f := fun s => (ν s).map Sigma.fst
  let pos (s : S) (h : s ∈ (roster (fun t => (ν t).map Sigma.fst) c).filter p) :=
    ((assigned_iff ν s c).mp ((mem_roster (a := f)).mp (Finset.mem_filter.mp h).1)).choose
  have spec s h : ν s = some ⟨c, pos s h⟩ :=
    ((assigned_iff ν s c).mp ((mem_roster (a := f)).mp (Finset.mem_filter.mp h).1)).choose_spec
  apply Finset.card_bij pos
  · exact fun s h => mem_indices.mpr ⟨s, spec s h, (Finset.mem_filter.mp h).2⟩
  · intro s hs t ht e
    exact ν.inj (e ▸ spec s hs) (spec t ht)
  · intro i hi
    obtain ⟨s, hs, hp⟩ := mem_indices.mp hi
    have hm : s ∈ (roster f c).filter p :=
      Finset.mem_filter.mpr ⟨mem_roster.mpr ((assigned_iff ν s c).mpr ⟨i, hs⟩), hp⟩
    refine ⟨s, hm, ?_⟩
    have e := Option.some.inj ((spec s hm).symm.trans hs)
    simpa using e

private theorem roster_card (ν : S ≃. Slot q) (c : C) :
    (roster (fun s => (ν s).map Sigma.fst) c).card = (indices ν c (fun _ => True)).card := by
  classical simpa using count_indices ν c (fun _ => True)

/-- Forget slot indices in any partial matching. Its fiber over `c` has at most `q c` students
because distinct students assigned to `c` occupy distinct indices in `Fin (q c)`. -/
def collapse (ν : S ≃. Slot q) : Assignment S C q where
  assign s := (ν s).map Sigma.fst
  capacity c := by
    rw [roster_card]
    simpa using (Finset.card_le_univ (indices ν c fun _ => True))

private theorem vacancy_iff (ν : S ≃. Slot q) (c : C) :
    (roster (collapse ν).assign c).card < q c ↔ ∃ i, ν.symm ⟨c, i⟩ = none := by
  classical
  change (roster (fun s => (ν s).map Sigma.fst) c).card < q c ↔ _
  have size := Finset.card_lt_iff_ne_univ (indices ν c fun _ => True)
  simp only [Fintype.card_fin] at size
  rw [roster_card, size, ne_eq, Finset.eq_univ_iff_forall, not_forall]
  apply exists_congr
  intro i
  simp only [mem_indices, and_true, ← ν.eq_some_iff]
  cases ν.symm ⟨c, i⟩ <;> simp

open Classical in
/-- The zero-based priority rank of `s` at `c` in an assignment: the number of students assigned
there whom `c` strictly prefers to `s`. For an incumbent this is the index of its canonical slot. -/
noncomputable def rank (cp : WPrefsSingle S C) (a : Assignment S C q) (c : C) (s : S) : ℕ :=
  ((roster a.assign c).filter fun t => (cp c).lt (some t) (some s)).card

/-- For a student assigned to `c`, the number of higher-priority incumbents is strictly
smaller than the roster size, hence below quota. -/
theorem rank_lt_card (cp : WPrefsSingle S C) (a : Assignment S C q) {c : C} {s : S}
    (hs : a.assign s = some c) : rank cp a c s < (roster a.assign c).card := by
  classical
  apply Finset.card_lt_card
  exact Finset.filter_ssubset.mpr ⟨s, mem_roster.mpr hs, (cp c).irrefl _⟩

private theorem rank_lt (cp : WPrefsSingle S C) (a : Assignment S C q) {s t : S} {c : C}
    (hs : a.assign s = some c) (h : (cp c).lt (some s) (some t)) :
    rank cp a c s < rank cp a c t := by
  classical
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (fun u hu => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hu).1, (cp c).trans (Finset.mem_filter.mp hu).2 h⟩)).mpr
  exact ⟨s, Finset.mem_filter.mpr ⟨mem_roster.mpr hs, h⟩, fun hs' =>
    (cp c).irrefl _ (Finset.mem_filter.mp hs').2⟩

/-- A student at `c` takes the copy whose index is the number of higher-priority incumbents;
a student assigned `none` takes no copy. This uses only capacity feasibility. -/
noncomputable def assignedSlot (cp : WPrefsSingle S C) (a : Assignment S C q) (s : S) :
    Option (Slot q) :=
  match h : a.assign s with
  | none => none
  | some c => some ⟨c, ⟨rank cp a c s, (rank_lt_card cp a h).trans_le (a.capacity c)⟩⟩

private theorem place_eq {cp : WPrefsSingle S C} {a : Assignment S C q} {s : S} {c : C}
    {i : Fin (q c)} : assignedSlot cp a s = some ⟨c, i⟩ ↔
      a.assign s = some c ∧ rank cp a c s = i.val := by
  unfold assignedSlot
  split
  · simp_all
  · rename_i d h
    constructor
    · intro e
      obtain rfl : d = c := congrArg Sigma.fst (Option.some.inj e)
      exact ⟨h, congrArg (fun k : Slot q => k.2.val) (Option.some.inj e)⟩
    · rintro ⟨e, hr⟩
      cases Option.some.inj (h.symm.trans e)
      apply congrArg some
      apply congrArg (Sigma.mk c)
      exact Fin.ext hr

/-- The canonical sorted lift sends each incumbent at `c` to slot `(c, rank)` and leaves an
unmatched student unmatched. It is defined for every feasible assignment, without a stability
or acceptability hypothesis. -/
noncomputable def lift (cp : WPrefsSingle S C) (a : Assignment S C q) : S ≃. Slot q where
  toFun := assignedSlot cp a
  invFun k := open Classical in
    if h : ∃ s, assignedSlot cp a s = some k then some h.choose else none
  inv := by
    classical
    intro s ⟨c, i⟩
    split
    · rename_i h
      simp only [Option.some.injEq]
      constructor
      · rintro rfl; exact h.choose_spec
      · intro hs
        obtain ⟨ht, et⟩ := place_eq.mp h.choose_spec
        obtain ⟨hs, es⟩ := place_eq.mp hs
        by_contra hn
        rcases (cp c).total (fun e => hn (Option.some.inj e)) with hp | hp
        · have := rank_lt cp a ht hp; omega
        · have := rank_lt cp a hs hp; omega
    · rename_i h
      simp only [reduceCtorEq, false_iff]
      exact fun hs => h ⟨s, hs⟩

/-- Assigning `s` to copy `(c,i)` in the sorted lift means exactly that `s` is at `c` in the
original assignment and exactly `i` incumbents there outrank `s`. -/
theorem lift_eq_some_iff {cp : WPrefsSingle S C} {a : Assignment S C q} {s : S} {c : C}
    {i : Fin (q c)} : lift cp a s = some ⟨c, i⟩ ↔ a.assign s = some c ∧ rank cp a c s = i.val :=
  place_eq

/-- Forgetting the indices after the sorted lift recovers every quota-feasible assignment,
including unstable assignments. -/
@[simp] theorem collapse_lift (cp : WPrefsSingle S C) (a : Assignment S C q) :
    collapse (lift cp a) = a := by
  apply Assignment.ext
  funext s
  change (assignedSlot cp a s).map Sigma.fst = a.assign s
  unfold assignedSlot
  split <;> simp_all

/-- Within each college's block, every slot earlier than an occupied slot is occupied by a
strictly higher-priority student. In particular the occupied indices form a prefix, possibly
empty or the whole block. This condition concerns slots of the same college only. -/
def Ordered (cp : WPrefsSingle S C) (ν : S ≃. Slot q) : Prop :=
  ∀ (c : C) (i j : Fin (q c)) (s : S), i < j → ν s = some ⟨c, j⟩ →
    ∃ t, ν t = some ⟨c, i⟩ ∧ (cp c).lt (some t) (some s)

private theorem rank_indices (cp : WPrefsSingle S C) (ν : S ≃. Slot q) (c : C) (s : S) :
    rank cp (collapse ν) c s = (indices ν c fun t => (cp c).lt (some t) (some s)).card :=
  count_indices ν c _

/-- In the canonical lift of any feasible assignment, even an unstable one, the students
assigned to a college occupy a prefix of its slots in strictly decreasing college priority. -/
theorem ordered_lift (cp : WPrefsSingle S C) (a : Assignment S C q) : Ordered cp (lift cp a) := by
  classical
  intro c i j s hij hs
  obtain ⟨_, hr⟩ := lift_eq_some_iff.mp hs
  let better := indices (lift cp a) c fun t => (cp c).lt (some t) (some s)
  have sub : better ⊆ Finset.Iio j := by
    intro k hk
    obtain ⟨t, ht, hp⟩ := mem_indices.mp hk
    obtain ⟨hc, he⟩ := lift_eq_some_iff.mp ht
    exact Finset.mem_Iio.mpr (show k.val < j.val by simpa [← he, ← hr] using rank_lt cp a hc hp)
  have cnt := rank_indices cp (lift cp a) c s
  rw [collapse_lift] at cnt
  have eq : better = Finset.Iio j :=
    Finset.eq_of_subset_of_card_le sub (by simp [better, ← cnt, hr])
  exact mem_indices.mp (show i ∈ better from eq ▸ Finset.mem_Iio.mpr hij)

omit [Fintype S] in
/-- Every stable partial matching in the copies market fills each college's slots from the
start, in decreasing college priority. Each student replaces the college in their strict ranking
of colleges and being unmatched by a consecutive block, in increasing slot index. Every copy uses
its college's strict ranking of students and an empty seat. Thus a later occupant would block
with a vacant earlier slot or one holding a lower-priority student. -/
theorem ordered_of_stable {sp : MPrefsSingle S C} {cp : WPrefsSingle S C} {ν : S ≃. Slot q}
    (hν : IsStableSingle (studentPrefs q sp) (slotPrefs q cp) ν) : Ordered cp ν := by
  intro c i j s hij hs
  have wants : (studentPrefs q sp s).lt (some ⟨c, i⟩) (ν s) := by
    rw [hs]; exact Or.inr ⟨rfl, hij⟩
  have nb := fun hp => hν.2.2 s ⟨c, i⟩ ⟨wants, hp⟩
  change ¬ (cp c).lt (some s) (ν.symm ⟨c, i⟩) at nb
  cases h : ν.symm ⟨c, i⟩ with
  | none =>
    rw [h] at nb
    have ir := hν.2.1 ⟨c, j⟩
    rw [ν.eq_some_iff.mpr hs] at ir
    exact (nb (((cp c).total (Option.some_ne_none s)).resolve_right ir)).elim
  | some t =>
    rw [h] at nb
    refine ⟨t, ν.eq_some_iff.mp h, ((cp c).total ?_).resolve_right nb⟩
    rintro e
    cases Option.some.inj e
    have eq := congrArg (fun k : Slot q => k.2.val)
      (Option.some.inj ((ν.eq_some_iff.mp h).symm.trans hs))
    exact hij.ne (Fin.ext eq)

private theorem rank_eq_index_of_ordered {cp : WPrefsSingle S C} {ν : S ≃. Slot q}
    (ord : Ordered cp ν) {s : S} {c : C} {j : Fin (q c)} (hs : ν s = some ⟨c, j⟩) :
    rank cp (collapse ν) c s = j.val := by
  classical
  rw [rank_indices]
  suffices indices ν c (fun t => (cp c).lt (some t) (some s)) = Finset.Iio j by simp [this]
  ext i
  rw [mem_indices, Finset.mem_Iio]
  refine ⟨?_, fun h => ord c i j s h hs⟩
  rintro ⟨t, ht, hp⟩
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact hij
  · have e := (ν.eq_some_iff.mpr ht).symm.trans (ν.eq_some_iff.mpr hs)
    exact ((cp c).irrefl _ (e ▸ hp)).elim
  · obtain ⟨u, hu, hu'⟩ := ord c j i t hji ht
    have e := (ν.eq_some_iff.mpr hu).symm.trans (ν.eq_some_iff.mpr hs)
    exact ((cp c).irrefl _ ((cp c).trans hp (e ▸ hu'))).elim

/-- In a stable partial matching of finitely many students to college copies, slot `(c,i)` is
occupied exactly when `i` is smaller than the number of students assigned to `c` after collapse.
Each student ranks the copies consecutively where `c` stood relative to other colleges and being
unmatched, always preferring the smaller index. Each copy inherits `c`'s strict ranking of
students and an empty seat. The cutoff includes empty and full rosters; at quota zero there is
no slot index. -/
theorem occupied_iff_lt_roster_card {sp : MPrefsSingle S C} {cp : WPrefsSingle S C}
    {ν : S ≃. Slot q}
    (hν : IsStableSingle (studentPrefs q sp) (slotPrefs q cp) ν) (c : C) (i : Fin (q c)) :
    (ν.symm ⟨c, i⟩).isSome ↔ i.val < (roster (collapse ν).assign c).card := by
  classical
  have ord := ordered_of_stable hν
  constructor
  · intro h
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h
    have hi := ν.eq_some_iff.mp hs
    rw [← rank_eq_index_of_ordered ord hi]
    exact rank_lt_card cp (collapse ν) ((assigned_iff ν s c).mpr ⟨i, hi⟩)
  · contrapose!
    intro empty
    have sub : indices ν c (fun _ => True) ⊆ Finset.Iio i := by
      intro j hj
      obtain ⟨s, hs, _⟩ := mem_indices.mp hj
      apply Finset.mem_Iio.mpr
      rcases lt_trichotomy j i with h | rfl | h
      · exact h
      · simp [ν.eq_some_iff.mpr hs] at empty
      · obtain ⟨t, ht, _⟩ := ord c i j s h hs
        simp [ν.eq_some_iff.mpr ht] at empty
    simpa [collapse, roster_card] using Finset.card_le_card sub

/-- If a partial slot matching already has sorted, gap-free rosters, lifting its collapse
recovers the matching itself, not just its occupied students up to permutation. -/
theorem lift_collapse_of_ordered {cp : WPrefsSingle S C} {ν : S ≃. Slot q} (ord : Ordered cp ν) :
    lift cp (collapse ν) = ν := by
  ext s ⟨c, i⟩
  rw [lift_eq_some_iff]
  constructor
  · rintro ⟨hc, hr⟩
    obtain ⟨j, hj⟩ := (assigned_iff ν s c).mp hc
    have eq : j = i := Fin.ext ((rank_eq_index_of_ordered ord hj).symm.trans hr)
    exact eq ▸ hj
  · exact fun h => ⟨(assigned_iff ν s c).mpr ⟨i, h⟩, rank_eq_index_of_ordered ord h⟩

private theorem college_wants_iff (cp : WPrefsSingle S C) (ν : S ≃. Slot q) (c : C) (s : S) :
    (((roster (collapse ν).assign c).card < q c ∧ (cp c).lt (some s) none) ∨
      ∃ t, (collapse ν).assign t = some c ∧ (cp c).lt (some s) (some t)) ↔
    ∃ i : Fin (q c), (cp c).lt (some s) (ν.symm ⟨c, i⟩) := by
  constructor
  · rintro (⟨hv, hp⟩ | ⟨t, ht, hp⟩)
    · obtain ⟨i, hi⟩ := (vacancy_iff ν c).mp hv
      exact ⟨i, hi ▸ hp⟩
    · obtain ⟨i, hi⟩ := (assigned_iff ν t c).mp ht
      exact ⟨i, (ν.eq_some_iff.mpr hi) ▸ hp⟩
  · rintro ⟨i, hp⟩
    cases h : ν.symm ⟨c, i⟩ with
    | none => exact Or.inl ⟨(vacancy_iff ν c).mpr ⟨i, h⟩, h ▸ hp⟩
    | some t => exact Or.inr ⟨t, (assigned_iff ν t c).mpr ⟨i, ν.eq_some_iff.mp h⟩, h ▸ hp⟩

omit [Fintype S] in
private theorem outside_iff (sp : MPrefsSingle S C) (ν : S ≃. Slot q) (s : S) :
    (studentPrefs q sp s).lt none (ν s) ↔ (sp s).lt none ((ν s).map Sigma.fst) := by
  cases ν s <;> simp [studentPrefs, slotIndex]

/-- Forgetting the slot index in a stable partial matching gives a pairwise stable college
assignment. Each student ranks a college's copies consecutively in increasing index where that
college stood in their strict ranking of colleges and being unmatched. Each copy ranks students
and an empty seat as its college does. A college blocking by vacancy would have an empty copy;
a replacement block would name an incumbent's copy. Neither is possible at quota zero. -/
theorem stable_collapse {sp : MPrefsSingle S C} {cp : WPrefsSingle S C} {ν : S ≃. Slot q}
    (hν : IsStableSingle (studentPrefs q sp) (slotPrefs q cp) ν) : IsStable sp cp (collapse ν) := by
  refine ⟨fun s h => hν.1 s ((outside_iff sp ν s).mpr h), ?_, ?_⟩
  · intro s c hs
    obtain ⟨i, hi⟩ := (assigned_iff ν s c).mp hs
    simpa [ν.eq_some_iff.mpr hi] using hν.2.1 ⟨c, i⟩
  · rintro s c ⟨hs, hc⟩
    obtain ⟨i, hi⟩ := (college_wants_iff cp ν c s).mp hc
    exact hν.2.2 s ⟨c, i⟩ ⟨Or.inl hs, hi⟩

private theorem stable_of_ordered {sp : MPrefsSingle S C} {cp : WPrefsSingle S C} {ν : S ≃. Slot q}
    (ord : Ordered cp ν) (ha : IsStable sp cp (collapse ν)) :
    IsStableSingle (studentPrefs q sp) (slotPrefs q cp) ν := by
  refine ⟨fun s h => ha.1 s ((outside_iff sp ν s).mp h), ?_, ?_⟩
  · intro ⟨c, i⟩
    cases h : ν.symm ⟨c, i⟩ with
    | none => exact (cp c).irrefl _
    | some s => exact ha.2.1 s c ((assigned_iff ν s c).mpr ⟨i, ν.eq_some_iff.mp h⟩)
  · rintro s ⟨c, i⟩ ⟨h | ⟨hc, hi⟩, hp⟩
    · exact ha.2.2 s c ⟨h, (college_wants_iff cp ν c s).mpr ⟨i, hp⟩⟩
    · obtain ⟨j, hj⟩ := (assigned_iff ν s c).mp hc.symm
      rw [hj] at hi
      obtain ⟨t, ht, hts⟩ := ord c i j s hi hj
      rw [ν.eq_some_iff.mpr ht] at hp
      exact (cp c).irrefl _ ((cp c).trans hp hts)

/-- A feasible assignment of finitely many students to colleges is pairwise stable if and only
if its sorted lift is stable in the copies market. Each student replaces each college in their
strict ranking of colleges and being unmatched by its consecutive copies, all students preferring
smaller indices. Each copy inherits its college's strict ranking of students and an empty seat.
The lift leaves unmatched students unmatched and seats each college's incumbents in priority
order. Both markets require individual rationality. College blocks are by acceptable vacancy or
replacement of a lower-priority incumbent; a zero-quota college has no copy and cannot block. -/
theorem stable_lift_iff (sp : MPrefsSingle S C) (cp : WPrefsSingle S C) (a : Assignment S C q) :
    IsStableSingle (studentPrefs q sp) (slotPrefs q cp) (lift cp a) ↔ IsStable sp cp a := by
  exact ⟨fun h => by simpa using stable_collapse h,
    fun h => stable_of_ordered (ordered_lift cp a) (by simpa using h)⟩

/-- For finitely many students and arbitrary colleges with natural quotas, stable college
assignments are in bijection with stable partial matchings in the copies market. Each student
replaces each college in their strict ranking of colleges and being unmatched by a consecutive
block of copies, ordered by increasing index for every student. Each copy inherits its college's
strict ranking of students and an empty seat. The forward map sends a student assigned to `c` to
slot `(c,i)`, where `i` counts the incumbents that `c` ranks above the student, and leaves an
unmatched student unmatched. The inverse forgets the index. A zero quota gives an empty block.
This correspondence does not assert existence or describe a deferred-acceptance outcome. -/
noncomputable def stableEquiv (q : C → ℕ) (sp : MPrefsSingle S C) (cp : WPrefsSingle S C) :
    {a : Assignment S C q // IsStable sp cp a} ≃
      {ν : S ≃. Slot q // IsStableSingle (studentPrefs q sp) (slotPrefs q cp) ν} where
  toFun a := ⟨lift cp a.val, (stable_lift_iff sp cp a.val).mpr a.property⟩
  invFun ν := ⟨collapse ν.val, stable_collapse ν.property⟩
  left_inv a := Subtype.ext (collapse_lift cp a.val)
  right_inv ν := Subtype.ext (lift_collapse_of_ordered (ordered_of_stable ν.property))

end MathlibExt.GameTheory.Matching.CollegeAdmissions
