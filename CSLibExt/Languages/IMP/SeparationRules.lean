/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.SeparationPrecondition

/-!
# Safe backward rules for heap IMP

The atomic `safePre` characterizations apply to arbitrary finite heaps:
reads require a successful lookup; writes and frees require an allocated
address; allocation quantifies over every address fresh for the original
heap. Expressions are evaluated in the original store, before any update.

Sequencing, conditionals and supplied loop invariants give sufficient
backward proof rules, derived from the existing `SepValid` rules. These
rules establish fault-avoiding partial correctness, without a termination
claim or automatic invariant discovery. They compose with `safePre.frame`.

The command semantics and separation specification follow J. C. Reynolds,
*Separation Logic: A Logic for Shared Mutable Data Structures*, LICS 2002,
Sections 2–4: <https://www.cs.cmu.edu/~jcr/seplogic.pdf>.
-/

@[expose] public section

namespace Cslib.IMP.safePre

open HAssertion

private theorem atomic_iff {c : HeapCmd} {s : State} {h : Heap}
    {Q : HAssertion} (hne : c ≠ .skip)
    (hfinal : ∀ cfg, HStep (c, s, h) cfg → cfg.1 = .skip) :
    safePre c Q s h ↔ (∃ cfg, HStep (c, s, h) cfg) ∧
      ∀ cfg, HStep (c, s, h) cfg → Q cfg.2.1 cfg.2.2 := by
  constructor
  · intro hp
    refine ⟨?_, ?_⟩
    · rcases hp.1 _ .refl with hc | hex
      · exact (hne hc).elim
      · exact hex
    · rintro ⟨c', s', h'⟩ hs
      have hc : c' = .skip := hfinal _ hs
      subst c'
      exact hp.2 (.single hs)
  · rintro ⟨hex, hpost⟩
    constructor
    · intro cfg hs
      rcases Relation.ReflTransGen.cases_head hs with rfl |
        ⟨next, hstep, htail⟩
      · exact Or.inr hex
      · obtain ⟨c', s', h'⟩ := next
        have hc : c' = .skip := hfinal _ hstep
        subst c'
        have heq := HSteps.skip_eq htail
        subst cfg
        exact Or.inl rfl
    · intro s' h' hs
      rcases Relation.ReflTransGen.cases_head hs with heq |
        ⟨next, hstep, htail⟩
      · exact (hne (congrArg Prod.fst heq)).elim
      · obtain ⟨c', t, k⟩ := next
        have hc : c' = .skip := hfinal _ hstep
        subst c'
        have heq := HSteps.skip_eq htail
        have hp := hpost _ hstep
        simp only [Prod.mk.injEq] at heq
        obtain ⟨_, rfl, rfl⟩ := heq
        exact hp

/-- For any store `s`, finite heap `h` and heap postcondition `Q`,
`safePre (.assign name value) Q s h` holds if and only if `Q` holds on
`h` and the store obtained by setting `name` to `value.eval s`. The
expression is evaluated in the original store; assignment leaves the heap unchanged. -/
theorem assign_iff {name : Nat} {value : AExp} {Q : HAssertion}
    {s : State} {h : Heap} :
    safePre (.assign name value) Q s h ↔
      Q (Function.update s name (value.eval s)) h := by
  rw [atomic_iff (by simp) (by intro cfg hs; cases hs; rfl)]
  simp [HStep.assign_iff]

/-- For any store `s`, finite heap `h` and heap postcondition `Q`,
`safePre (.read name addr) Q s h` holds if and only if there is a value `v`
with `h.lookup (addr.eval s) = some v` and `Q (Function.update s name v) h`.
The address is evaluated before the store update; the heap is unchanged. -/
theorem read_iff {name : Nat} {addr : AExp} {Q : HAssertion}
    {s : State} {h : Heap} :
    safePre (.read name addr) Q s h ↔
      ∃ v, h.lookup (addr.eval s) = some v ∧
        Q (Function.update s name v) h := by
  rw [atomic_iff (by simp) (by intro cfg hs; cases hs; rfl)]
  constructor
  · rintro ⟨⟨cfg, hs⟩, hp⟩
    obtain ⟨v, hv, rfl⟩ := HStep.read_iff.mp hs
    exact ⟨v, hv, hp _ (.read hv)⟩
  · rintro ⟨v, hv, hp⟩
    refine ⟨⟨_, .read hv⟩, ?_⟩
    intro cfg hs
    obtain ⟨w, hw, rfl⟩ := HStep.read_iff.mp hs
    have heq : w = v := Option.some.inj (hw.symm.trans hv)
    subst w
    exact hp

/-- For any store `s`, finite heap `h` and heap postcondition `Q`,
`safePre (.write addr value) Q s h` holds if and only if `addr.eval s ∈ h`
and `Q s (Finmap.insert (addr.eval s) (value.eval s) h)`. Both expressions
use the original store. The membership condition excludes missing cells,
which `insert` alone would otherwise add. -/
theorem write_iff {addr value : AExp} {Q : HAssertion}
    {s : State} {h : Heap} :
    safePre (.write addr value) Q s h ↔
      addr.eval s ∈ h ∧
        Q s (Finmap.insert (addr.eval s) (value.eval s) h) := by
  rw [atomic_iff (by simp) (by intro cfg hs; cases hs; rfl)]
  simp +contextual [HStep.write_iff]

/-- For any store `s`, finite heap `h` and heap postcondition `Q`,
`safePre (.alloc name value) Q s h` holds if and only if, for every address
`a ∉ h`, `Q (Function.update s name a) (Finmap.insert a (value.eval s) h)`.
The value expression uses the original store. Allocation is demonic over
fresh addresses; finiteness of the heap ensures at least one exists. -/
theorem alloc_iff {name : Nat} {value : AExp} {Q : HAssertion}
    {s : State} {h : Heap} :
    safePre (.alloc name value) Q s h ↔
      ∀ a, a ∉ h → Q (Function.update s name a)
        (Finmap.insert a (value.eval s) h) := by
  rw [atomic_iff (by simp) (by intro cfg hs; cases hs; rfl)]
  constructor
  · rintro ⟨-, hp⟩ a ha
    exact hp _ (.alloc ha)
  · intro hp
    obtain ⟨a, ha⟩ := Heap.exists_notMem h
    refine ⟨⟨_, .alloc ha⟩, ?_⟩
    intro cfg hs
    obtain ⟨b, hb, rfl⟩ := HStep.alloc_iff.mp hs
    exact hp b hb

/-- For any store `s`, finite heap `h` and heap postcondition `Q`,
`safePre (.free addr) Q s h` holds if and only if `addr.eval s ∈ h` and
`Q s (Finmap.erase (addr.eval s) h)`. Free leaves the store unchanged.
The allocated-address requirement remains even when `Q` is always true. -/
theorem free_iff {addr : AExp} {Q : HAssertion} {s : State} {h : Heap} :
    safePre (.free addr) Q s h ↔
      addr.eval s ∈ h ∧ Q s (Finmap.erase (addr.eval s) h) := by
  rw [atomic_iff (by simp) (by intro cfg hs; cases hs; rfl)]
  simp +contextual [HStep.free_iff]

/-- For any heap commands `c₁`, `c₂` and heap postcondition `Q`,
`safePre c₁ (safePre c₂ Q)` entails `safePre (.seq c₁ c₂) Q`.
This is a sufficient backward rule for safe partial correctness. -/
theorem seq {c₁ c₂ : HeapCmd} {Q : HAssertion} :
    (safePre c₁ (safePre c₂ Q)).Entails (safePre (.seq c₁ c₂) Q) :=
  valid_iff.mp (SepValid.seq (valid c₁ _) (valid c₂ Q))

/-- For a Boolean guard, heap commands `t`, `e` and heap postcondition
`Q`, suppose at an initial store and heap that a true guard implies
`safePre t Q` and a false guard implies `safePre e Q`. Then
`safePre (.ite guard t e) Q` holds there. Only the selected branch needs
to establish the postcondition safely. -/
theorem ite {guard : BExp} {t e : HeapCmd} {Q : HAssertion} :
    HAssertion.Entails (fun s h =>
      (guard.eval s = true → safePre t Q s h) ∧
      (guard.eval s = false → safePre e Q s h))
      (safePre (.ite guard t e) Q) := by
  apply valid_iff.mp
  apply SepValid.ite
  · intro s h hp
    exact hp.1.1 hp.2
  · intro s h hp
    exact hp.1.2 hp.2

/-- Let `I` and `Q` be heap assertions. If `I` together with a true
guard entails `safePre body I`, and `I` together with a false guard entails
`Q`, then `I` entails `safePre (.while guard body) Q`. This establishes
fault-avoiding partial correctness; no termination premise is inferred. -/
theorem whileLoop {guard : BExp} {body : HeapCmd} {I Q : HAssertion}
    (hbody : HAssertion.Entails
      (fun s h => I s h ∧ guard.eval s = true) (safePre body I))
    (hexit : HAssertion.Entails
      (fun s h => I s h ∧ guard.eval s = false) Q) :
    I.Entails (safePre (.while guard body) Q) :=
  valid_iff.mp (SepValid.consequence (entails_refl _)
    (SepValid.whileLoop (valid_iff.mpr hbody)) hexit)

end Cslib.IMP.safePre
