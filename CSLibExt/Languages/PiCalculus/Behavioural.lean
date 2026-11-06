/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.PiCalculus.Basic
public import Cslib.Foundations.Semantics.LTS.Bisimulation

/-!
# Strong free-channel barbed bisimilarity

Observations are input/output readiness on free constant subjects. The
transmitted object is not a barb: receivers can observe it after `Step`.
`Offer` exposes selected guards under parallel composition and restriction;
`Barb` permits structural rearrangement, but no reduction. In particular,
arbitrary unguarded sums are not flattened into offers.

`observedLTS` decorates the existing `Step` relation with observation-only
self-loops. It does not introduce labelled input/output execution rules.
Canonical strong bisimilarity on this LTS is exactly strong barbed
bisimilarity, as proved by `isBisimulation_observedLTS_iff`. Every reduction
must be matched by one reduction; no weak or divergence-insensitive result
is claimed. `Cong.barbedBisimilar` proves structural soundness.
-/

@[expose] public section

namespace Cslib.PiCalculus

/-- **Free-channel input and output observables.**
A visible input or output subject. Restricted variables are not subjects
of these free-channel observations. -/
inductive Observable where
  | input (channel : ℕ)
  | output (channel : ℕ)
  deriving DecidableEq, Repr

/-- **Free-channel guard offered without reduction.**
A selected free-channel guard exposed without reduction. Restrictions
hide bound subjects but do not hide free constants. -/
inductive Offer : Proc → Observable → Prop where
  | input {p q : Proc} {a : ℕ} :
      Select p (.inp (.const a) q) → Offer p (.input a)
  | output {p q : Proc} {a : ℕ} {b : Name} :
      Select p (.out (.const a) b q) → Offer p (.output a)
  | parL {p q : Proc} {o : Observable} :
      Offer p o → Offer (.par p q) o
  | parR {p q : Proc} {o : Observable} :
      Offer q o → Offer (.par p q) o
  | nu {p : Proc} {o : Observable} : Offer p o → Offer (.nu p) o

/-- **Immediate free-channel barb.** Immediate free-channel readiness, up to the existing structural
congruence. A witness performs no `Step`. -/
def Barb (p : Proc) (o : Observable) : Prop :=
  ∃ q, Cong p q ∧ Offer q o

/-- **Labels for reductions and barb observations.**
Labels for reductions and observation-only self-loops. -/
inductive BehaviourLabel where
  | reduce
  | observe (o : Observable)
  deriving DecidableEq, Repr

/-- **Reduction LTS decorated with barb observations.**
The existing reduction semantics decorated with barb tests. The
observation transitions do not consume a prefix or transmit a name. -/
def observedLTS : LTS Proc BehaviourLabel where
  Tr p label q := match label with
    | .reduce => Step p q
    | .observe o => p = q ∧ Barb p o

/-- **Strong barbed bisimilarity.**
Strong barbed bisimilarity, using the canonical CSLib bisimulation API.
No context closure is built into this relation. -/
def BarbedBisimilar : Proc → Proc → Prop :=
  LTS.HomBisimilarity observedLTS

/-- **Decorated-LTS bisimulations are exactly strong barbed bisimulations.**
The decorated LTS has precisely the strong reduction-matching and
immediate-barb-preservation clauses of a strong barbed bisimulation. -/
theorem isBisimulation_observedLTS_iff (r : Proc → Proc → Prop) :
    LTS.IsHomBisimulation observedLTS r ↔
      ∀ ⦃p q⦄, r p q →
        (∀ p', Step p p' → ∃ q', Step q q' ∧ r p' q') ∧
        (∀ q', Step q q' → ∃ p', Step p p' ∧ r p' q') ∧
        (∀ o, Barb p o ↔ Barb q o) := by
  constructor
  · intro h p q hpq
    refine ⟨(h hpq .reduce).1, (h hpq .reduce).2, ?_⟩
    intro o
    constructor
    · intro hp
      obtain ⟨q', ⟨_, hq⟩, _⟩ := (h hpq (.observe o)).1 p ⟨rfl, hp⟩
      exact hq
    · intro hq
      obtain ⟨p', ⟨_, hp⟩, _⟩ := (h hpq (.observe o)).2 q ⟨rfl, hq⟩
      exact hp
  · intro h p q hpq label
    obtain ⟨hleft, hright, hbarb⟩ := h hpq
    cases label with
    | reduce => exact ⟨hleft, hright⟩
    | observe o =>
      exact ⟨fun p' ⟨heq, hb⟩ => ⟨q, ⟨rfl, (hbarb o).mp hb⟩, heq ▸ hpq⟩,
        fun q' ⟨heq, hb⟩ => ⟨p, ⟨rfl, (hbarb o).mpr hb⟩, heq ▸ hpq⟩⟩

/-- **Structural congruence preserves immediate barbs.**
Structural congruence preserves immediate barbs. -/
theorem Cong.barb_iff {p q : Proc} (h : Cong p q) (o : Observable) :
    Barb p o ↔ Barb q o := by
  constructor
  · rintro ⟨r, hpr, hr⟩
    exact ⟨r, h.symm.trans hpr, hr⟩
  · rintro ⟨r, hqr, hr⟩
    exact ⟨r, h.trans hqr, hr⟩

/-- **Structural congruence is a strong barbed bisimulation.**
Structural congruence is a strong barbed bisimulation: reductions
match one for one, while free-channel observations match immediately. -/
theorem cong_isBarbedBisimulation :
    LTS.IsHomBisimulation observedLTS Cong := by
  apply (isBisimulation_observedLTS_iff Cong).mpr
  intro p q h
  exact ⟨fun p' hp => ⟨p', Step.cong h.symm hp (.refl _), .refl _⟩,
    fun q' hq => ⟨q', Step.cong h hq (.refl _), .refl _⟩,
    h.barb_iff⟩

/-- **Structurally congruent processes are barbed bisimilar.**
Every structural law of `Basic` is sound for strong barbed
bisimilarity, including scope extrusion and replication unfolding. -/
theorem Cong.barbedBisimilar {p q : Proc} (h : Cong p q) :
    BarbedBisimilar p q :=
  cong_isBarbedBisimulation.le_bisimilarity p q h

/-- **Unguarded output in a process.**
An output not behind a prefix, on any subject (including bound names).
This is an overapproximation for arbitrary unguarded sums, not a barb. -/
def HasUnguardedOutput : Proc → Prop
  | .nil => False
  | .out _ _ _ => True
  | .inp _ _ => False
  | .par p q => HasUnguardedOutput p ∨ HasUnguardedOutput q
  | .nu p => HasUnguardedOutput p
  | .repl p => HasUnguardedOutput p
  | .sum p q => HasUnguardedOutput p ∨ HasUnguardedOutput q

private theorem output_lift (p : Proc) (k : ℕ) :
    HasUnguardedOutput (liftProc k p) ↔ HasUnguardedOutput p := by
  induction p generalizing k <;> simp_all [liftProc, HasUnguardedOutput]

private theorem output_swap (p : Proc) (k : ℕ) :
    HasUnguardedOutput (swapProc k p) ↔ HasUnguardedOutput p := by
  induction p generalizing k <;> simp_all [swapProc, HasUnguardedOutput]

/-- **Structural congruence preserves unguarded outputs.**
Structural rearrangement cannot expose an output from an input-guarded
process. This includes arbitrary uses of replication and scope laws. -/
theorem Cong.hasUnguardedOutput_iff {p q : Proc} (h : Cong p q) :
    HasUnguardedOutput p ↔ HasUnguardedOutput q := by
  induction h <;>
    simp_all [HasUnguardedOutput, output_lift, output_swap,
      or_comm, or_assoc]

private theorem select_output {p q : Proc} (h : Select p q) :
    HasUnguardedOutput q → HasUnguardedOutput p := by
  induction h with
  | refl => exact id
  | left => exact Or.inl
  | right => exact Or.inr
  | trans _ _ ih₁ ih₂ => exact ih₁ ∘ ih₂

/-- **Every reduction source has an unguarded output.**
Every reduction needs an unguarded output in its source, even when
communication is private or structural congruence is used arbitrarily. -/
theorem Step.hasUnguardedOutput {p q : Proc} (h : Step p q) :
    HasUnguardedOutput p := by
  induction h with
  | commSelect hout _ => exact Or.inl (select_output hout trivial)
  | parL _ ih => exact Or.inl ih
  | parR _ ih => exact Or.inr ih
  | nu _ ih => exact ih
  | cong hcong _ _ ih => exact hcong.hasUnguardedOutput_iff.mpr ih

/-- **Processes without unguarded output cannot reduce.**
Outputless processes cannot reduce. Input guards may still have
observable input barbs; this theorem does not identify them with `nil`. -/
theorem not_step_of_no_output {p : Proc}
    (h : ¬ HasUnguardedOutput p) (q : Proc) : ¬ Step p q :=
  fun hs => h hs.hasUnguardedOutput

private def potential : Proc → Observable → Prop
  | .nil, _ => False
  | .out a _ _, o => ∃ n, a = .const n ∧ o = .output n
  | .inp a _, o => ∃ n, a = .const n ∧ o = .input n
  | .par p q, o => potential p o ∨ potential q o
  | .nu p, o => potential p o
  | .repl p, o => potential p o
  | .sum p q, o => potential p o ∨ potential q o

private theorem lift_const_iff (a : Name) (k n : ℕ) :
    liftName k a = .const n ↔ a = .const n := by
  cases a with
  | const => simp [liftName]
  | var i => by_cases h : k ≤ i <;> simp [liftName, h]

private theorem swap_const_iff (a : Name) (k n : ℕ) :
    swapNameAt k a = .const n ↔ a = .const n := by
  cases a with
  | const => simp [swapNameAt]
  | var i =>
    by_cases h₁ : i = k <;> by_cases h₂ : i = k + 1 <;>
      simp [swapNameAt, h₁, h₂]

private theorem potential_lift (p : Proc) (k : ℕ) (o : Observable) :
    potential (liftProc k p) o ↔ potential p o := by
  induction p generalizing k <;>
    simp_all [potential, liftProc, lift_const_iff]

private theorem potential_swap (p : Proc) (k : ℕ) (o : Observable) :
    potential (swapProc k p) o ↔ potential p o := by
  induction p generalizing k <;>
    simp_all [potential, swapProc, swap_const_iff]

private theorem potential_cong {p q : Proc} (h : Cong p q)
    (o : Observable) : potential p o ↔ potential q o := by
  induction h <;>
    simp_all [potential, potential_lift, potential_swap, or_comm, or_assoc]

private theorem potential_select {p q : Proc} (h : Select p q)
    (o : Observable) : potential q o → potential p o := by
  induction h with
  | refl => exact id
  | left => exact Or.inl
  | right => exact Or.inr
  | trans _ _ ih₁ ih₂ => exact ih₁ ∘ ih₂

private theorem potential_offer {p : Proc} {o : Observable}
    (h : Offer p o) : potential p o := by
  induction h with
  | input h => exact potential_select h _ ⟨_, rfl, rfl⟩
  | output h => exact potential_select h _ ⟨_, rfl, rfl⟩
  | parL _ ih => exact Or.inl ih
  | parR _ ih => exact Or.inr ih
  | nu _ ih => exact ih

private theorem potential_barb {p : Proc} {o : Observable}
    (h : Barb p o) : potential p o := by
  obtain ⟨q, hpq, hq⟩ := h
  exact (potential_cong hpq o).mpr (potential_offer hq)

/-- **Exposed guards are barbs.** A directly exposed guard is a barb, with the reflexive structural
representative as witness. -/
theorem Barb.of_offer {p : Proc} {o : Observable} (h : Offer p o) :
    Barb p o := ⟨p, .refl p, h⟩

/-- **The inactive process has no barbs.**
The inactive process has no barb, even after structural rearrangement. -/
@[simp] theorem barb_nil (o : Observable) : ¬ Barb .nil o :=
  fun h => potential_barb h

/-- **Barbs of an output prefix.**
Output readiness sees only its free subject and direction, not its
object or guarded continuation. -/
@[simp] theorem barb_out_iff (a b : Name) (p : Proc) (o : Observable) :
    Barb (.out a b p) o ↔ ∃ n, a = .const n ∧ o = .output n := by
  constructor
  · exact potential_barb
  · rintro ⟨n, rfl, rfl⟩
    exact Barb.of_offer (.output (.refl _))

/-- **Barbs of an input prefix.**
Waiting inputs are observable, despite being unable to reduce alone. -/
@[simp] theorem barb_inp_iff (a : Name) (p : Proc) (o : Observable) :
    Barb (.inp a p) o ↔ ∃ n, a = .const n ∧ o = .input n := by
  constructor
  · exact potential_barb
  · rintro ⟨n, rfl, rfl⟩
    exact Barb.of_offer (.input (.refl _))

/-- **Barbs of a restricted output prefix.**
A restricted output is visible exactly when its subject is free.
Sending the private name on a free subject remains observable. -/
@[simp] theorem barb_nu_out_iff (a b : Name) (p : Proc) (o : Observable) :
    Barb (.nu (.out a b p)) o ↔ ∃ n, a = .const n ∧ o = .output n := by
  constructor
  · exact potential_barb
  · rintro ⟨n, rfl, rfl⟩
    exact Barb.of_offer (.nu (.output (.refl _)))

/-- **Barbed bisimilar processes have the same barbs.**
Bisimilar processes have the same immediate free-channel barbs. -/
theorem BarbedBisimilar.barb_iff {p q : Proc}
    (h : BarbedBisimilar p q) (o : Observable) : Barb p o ↔ Barb q o := by
  obtain ⟨r, hpq, hr⟩ := h
  exact ((isBisimulation_observedLTS_iff r).mp hr hpq).2.2 o

/-- **Barbed bisimilarity matches each reduction by one reduction.**
A reduction from the first process is matched by one reduction,
with strong barbed bisimilar derivatives. -/
theorem BarbedBisimilar.step {p q p' : Proc}
    (h : BarbedBisimilar p q) (hs : Step p p') :
    ∃ q', Step q q' ∧ BarbedBisimilar p' q' := by
  obtain ⟨r, hpq, hr⟩ := h
  obtain ⟨q', hq', hr'⟩ :=
    ((isBisimulation_observedLTS_iff r).mp hr hpq).1 p' hs
  exact ⟨q', hq', r, hr', hr⟩

/-- **Free-channel input is not barbed bisimilar to nil.**
Waiting for input is not equivalent to doing nothing. Reduction-only
bisimilarity would miss this distinction. -/
theorem input_not_barbedBisimilar_nil (a : ℕ) (p : Proc) :
    ¬ BarbedBisimilar (.inp (.const a) p) .nil := by
  intro h
  exact barb_nil _ ((h.barb_iff _).mp
    (Barb.of_offer (.input (.refl _))))

/-- **May-barb after finitely many reductions.**
A free-channel barb reachable by finitely many existing reductions,
possibly zero. This is a may observation, not a weak equivalence. -/
def MayBarb (p : Proc) (o : Observable) : Prop :=
  ∃ p', Relation.ReflTransGen Step p p' ∧ Barb p' o

/-- **Barbed bisimilarity transfers finite reduction paths.**
A finite reduction path transfers across strong barbed bisimilarity. -/
theorem BarbedBisimilar.reductionPath {p q p' : Proc}
    (h : BarbedBisimilar p q) (hs : Relation.ReflTransGen Step p p') :
    ∃ q', Relation.ReflTransGen Step q q' ∧ BarbedBisimilar p' q' := by
  induction hs with
  | refl => exact ⟨q, .refl, h⟩
  | tail _ hstep ih =>
    obtain ⟨r, hqr, hpr⟩ := ih
    obtain ⟨q', hrq', hfinal⟩ := hpr.step hstep
    exact ⟨q', hqr.tail hrq', hfinal⟩

/-- **Barbed bisimilarity preserves may-barbs.**
Strong barbed bisimilarity preserves finite may observations. -/
theorem BarbedBisimilar.mayBarb_iff {p q : Proc}
    (h : BarbedBisimilar p q) (o : Observable) :
    MayBarb p o ↔ MayBarb q o := by
  have transfer {s t : Proc} (hst : BarbedBisimilar s t)
      (hb : MayBarb s o) : MayBarb t o := by
    obtain ⟨s', hs', hb'⟩ := hb
    obtain ⟨t', ht', hst'⟩ := hst.reductionPath hs'
    exact ⟨t', ht', (hst'.barb_iff o).mp hb'⟩
  exact ⟨transfer h, transfer (LTS.Bisimilarity.symm h)⟩

end Cslib.PiCalculus
