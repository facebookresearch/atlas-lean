/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.SeparationVCG
public import CSLibExtTest.Languages.IMP.SeparationExamples

/-!
# List reversal through generated separation conditions

The supplied list invariant discharges the actual backward conditions of
the annotated generator. The proof reuses the individual heap-operation
lemmas of the manual example, not its completed reversal specification.
An explicit frame annotation admits any disjoint frame stable under the
program's store modifications. These are safe partial-correctness results;
the finite execution examples do not assert termination for every input.
-/

@[expose] public section

namespace Cslib.IMP.SeparationVCGReversalTests

open HAssertion Tests.SepExamples
open scoped HAssertion

private def body : AHeapCmd :=
  .seq (.read 2 (.var 0))
    (.seq (.write (.var 0) (.var 1))
      (.seq (.assign 1 (.var 0)) (.assign 0 (.var 2))))

private def annotated (xs : List Nat) : AHeapCmd :=
  .while (reverseInv xs) reverseGuard body

private def input (head : Nat) (xs : List Nat) : HAssertion :=
  fun s h => (s 0 = head ∧ s 1 = 0) ∧ IsList head xs s h

private def output (xs : List Nat) : HAssertion :=
  fun s h => s 0 = 0 ∧ IsList (s 1) xs.reverse s h

example (xs : List Nat) : (annotated xs).strip = reverseCmd := rfl

private theorem read_pre {P Q : HAssertion} {x : Nat} {a : AExp}
    (hv : SepValid P (.read x a) Q) :
    P.Entails ((AHeapCmd.read x a).pre Q) :=
  fun {_ _} hp => safePre.read_iff.mp (hv hp)

private theorem write_pre {P Q : HAssertion} {a v : AExp}
    (hv : SepValid P (.write a v) Q) :
    P.Entails ((AHeapCmd.write a v).pre Q) :=
  fun {_ _} hp => safePre.write_iff.mp (hv hp)

private theorem assign_pre {P Q : HAssertion} {x : Nat} {v : AExp}
    (hv : SepValid P (.assign x v) Q) :
    P.Entails ((AHeapCmd.assign x v).pre Q) :=
  fun {_ _} hp => safePre.assign_iff.mp (hv hp)

-- Derive the nested generated precondition from the four atomic steps.
private theorem body_pre (xs : List Nat) :
    HAssertion.Entails
      (fun s h => reverseInv xs s h ∧ reverseGuard.eval s = true)
      (body.pre (reverseInv xs)) := by
  have h4 := (assign_pre (rev_step4 (xs0 := xs))).trans
    (AHeapCmd.pre_mono _ rev_post_entails)
  have h3 := (assign_pre (rev_step3 (xs0 := xs))).trans
    (AHeapCmd.pre_mono _ h4)
  have h2 := (write_pre (rev_step2 (xs0 := xs))).trans
    (AHeapCmd.pre_mono _ (rev_fold_entails.trans h3))
  exact rev_pre_entails.trans
    ((read_pre rev_step1).trans (AHeapCmd.pre_mono _ h2))

private theorem entry {head : Nat} {xs : List Nat} :
    (input head xs).Entails (reverseInv xs) := by
  rintro s h ⟨⟨hs0, hs1⟩, hl⟩
  refine ⟨xs, [], by simp, ?_⟩
  refine ⟨h, ∅, Heap.disjoint_empty_right h, Finmap.union_empty.symm, ?_, ?_⟩
  · rwa [hs0]
  · exact isList_nil_iff.mpr ⟨hs1, rfl⟩

private theorem exit (xs : List Nat) :
    HAssertion.Entails
      (fun s h => reverseInv xs s h ∧ reverseGuard.eval s = false)
      (output xs) := by
  rintro s h ⟨hI, hg⟩
  have hs0 := eq_of_guard_false hg
  obtain ⟨(_ | ⟨x, rem⟩), rev, hrel, hstar⟩ := hI
  · obtain ⟨h₁, h₂, _hd, heq, hrem, hrev⟩ := hstar
    obtain ⟨_, hh1⟩ := isList_nil_iff.mp hrem
    subst hh1
    have hr : rev.reverse = xs := by simpa using hrel
    have hr' : rev = xs.reverse := by
      simpa using congrArg List.reverse hr
    refine ⟨hs0, ?_⟩
    rw [← hr']
    rwa [heq, Finmap.empty_union]
  · obtain ⟨h₁, _h₂, _hd, _heq, hrem, _hrev⟩ := hstar
    obtain ⟨hax, hx0, _⟩ := isList_cons_iff.mp hrem
    exact (hx0 (hax.symm.trans hs0)).elim

private theorem conditions (xs : List Nat) :
    (annotated xs).vc (output xs) :=
  ⟨body_pre xs, exit xs, by simp [body, AHeapCmd.vc]⟩

private theorem reversal_vcg {head : Nat} {xs : List Nat} :
    SepValid (input head xs) reverseCmd (output xs) :=
  AHeapCmd.vc_valid (C := annotated xs) (conditions xs) entry

-- This goes through the generator's frame annotation, including its side condition.
private theorem framed_vcg {head : Nat} {xs : List Nat} {R : HAssertion}
    (hR : ∀ ⦃s h s'⦄, R s h →
      (∀ x, x ∉ reverseCmd.modVars → s' x = s x) → R s' h) :
    SepValid (input head xs ⋆ R) reverseCmd (output xs ⋆ R) := by
  apply AHeapCmd.vc_valid (C := .frame R (output xs) (annotated xs))
  · exact ⟨conditions xs, hR, entails_refl _⟩
  · exact star_mono entry (entails_refl _)

example : SepValid (input 0 []) reverseCmd (output []) := reversal_vcg

example : SepValid (input 5 [5]) reverseCmd (output [5]) := reversal_vcg

example (head : Nat) (xs : List Nat) :
    SepValid (input head xs ⋆ pointsTo 11 42) reverseCmd
      (output xs ⋆ pointsTo 11 42) :=
  framed_vcg (fun {_ _ _} hr _ => hr)

-- A true invariant forgets the ownership needed by the first read.
example : ¬ (AHeapCmd.while (fun _ _ => True) reverseGuard body).vc
    (fun _ _ => True) := by
  intro hv
  let s : State := fun _ => 5
  have hg : reverseGuard.eval s = true := by decide
  have hp := hv.1 (s := s) (h := ∅) ⟨True.intro, hg⟩
  obtain ⟨v, hv, _⟩ := hp
  simp at hv

example : SepValid
    (fun s h => (s 0 = 5 ∧ s 1 = 0) ∧ IsList 5 [5, 7] s h)
    reverseCmd (fun s h => s 0 = 0 ∧ IsList (s 1) [7, 5] s h) :=
  reversal_vcg

-- Concrete initial heaps witness that the abstract specifications are inhabited.
private theorem singleton_list (s : State) (a : Nat) (ha : a ≠ 0) :
    IsList a [a] s (Finmap.singleton a 0) := by
  refine isList_cons_iff.mpr ⟨rfl, ha, 0, ?_⟩
  exact ⟨_, ∅, Heap.disjoint_empty_right _, Finmap.union_empty.symm,
    rfl, isList_nil_iff.mpr ⟨rfl, rfl⟩⟩

private def start (a : Nat) : State := Function.update (fun _ => 0) 0 a

example : input 0 [] (start 0) ∅ := by
  exact ⟨⟨rfl, rfl⟩, isList_nil_iff.mpr ⟨rfl, rfl⟩⟩

example : input 5 [5] (start 5) (Finmap.singleton 5 0) :=
  ⟨⟨rfl, rfl⟩, singleton_list _ _ (by decide)⟩

private theorem two_nodes : input 5 [5, 7] (start 5)
    (Finmap.singleton 5 7 ∪ Finmap.singleton 7 0) := by
  refine ⟨⟨rfl, rfl⟩, isList_cons_iff.mpr ⟨rfl, by decide, 7, ?_⟩⟩
  exact ⟨_, _, Heap.disjoint_singleton_left.mpr (by simp), rfl,
    rfl, singleton_list _ _ (by decide)⟩

private def advance (s : State) (nxt : Nat) : State :=
  Function.update (Function.update (Function.update s 2 nxt) 1 (s 0)) 0 nxt

private theorem body_run {s : State} {h : Heap} {nxt : Nat}
    (hv : h.lookup (s 0) = some nxt) :
    HSteps (reverseBody, s, h)
      (.skip, advance s nxt, Finmap.insert (s 0) (s 1) h) := by
  let t := Function.update s 2 nxt
  let u := Function.update t 1 (s 0)
  let k := Finmap.insert (s 0) (s 1) h
  have hr : HSteps (.read 2 (.var 0), s, h) (.skip, t, h) :=
    .single (.read hv)
  have hw : HSteps (.write (.var 0) (.var 1), t, h) (.skip, t, k) := by
    have hm : (AExp.var 0).eval t ∈ h := by
      simpa [t, AExp.eval] using Finmap.mem_of_lookup_eq_some hv
    simpa [t, k, AExp.eval] using
      HSteps.single (HStep.write (value := .var 1) hm)
  have h1 : HSteps (.assign 1 (.var 0), t, k) (.skip, u, k) := by
    simpa [u, t, AExp.eval] using
      HSteps.single (HStep.assign (name := 1) (value := .var 0) (state := t) (heap := k))
  have h0 : HSteps (.assign 0 (.var 2), u, k) (.skip, advance s nxt, k) := by
    simpa [advance, u, t, AExp.eval] using
      HSteps.single (HStep.assign (name := 0) (value := .var 2) (state := u) (heap := k))
  exact (hr.seq_congr.trans HSteps.seq_skip).trans
    ((hw.seq_congr.trans HSteps.seq_skip).trans
      ((h1.seq_congr.trans HSteps.seq_skip).trans h0))

private theorem iteration {s : State} {h : Heap} {nxt : Nat}
    (hg : reverseGuard.eval s = true) (hv : h.lookup (s 0) = some nxt) :
    HSteps (reverseCmd, s, h)
      (reverseCmd, advance s nxt, Finmap.insert (s 0) (s 1) h) := by
  exact ((HSteps.single (HStep.whileStep reverseGuard reverseBody s h)).tail (.iteTrue hg)).trans
    ((body_run hv).seq_congr.trans HSteps.seq_skip)

private theorem finish {s : State} {h : Heap}
    (hg : reverseGuard.eval s = false) :
    HSteps (reverseCmd, s, h) (.skip, s, h) :=
  (HSteps.single (HStep.whileStep reverseGuard reverseBody s h)).tail (.iteFalse hg)

-- Zero, one and two actual loop iterations; no validity premise assumes a run.
example : HSteps (reverseCmd, start 0, ∅) (.skip, start 0, ∅) :=
  finish (by decide)

example : ∃ t h, HSteps (reverseCmd, start 5, Finmap.singleton 5 0)
    (.skip, t, h) ∧ output [5] t h := by
  have run := (iteration (s := start 5) (h := Finmap.singleton 5 0)
    (nxt := 0) (by decide) (by change (Finmap.singleton 5 0).lookup 5 = some 0; simp)).trans (finish (by decide))
  exact ⟨_, _, run,
    (reversal_vcg ⟨⟨rfl, rfl⟩, singleton_list _ _ (by decide)⟩).2 run⟩

example : ∃ t h, HSteps (reverseCmd, start 5,
      Finmap.singleton 5 7 ∪ Finmap.singleton 7 0) (.skip, t, h) ∧
    t 0 = 0 ∧ t 1 = 7 ∧ h.lookup 5 = some 0 ∧ h.lookup 7 = some 5 ∧
    IsList 7 [7, 5] t h := by
  have run1 := iteration (s := start 5)
    (h := Finmap.singleton 5 7 ∪ Finmap.singleton 7 0)
    (nxt := 7) (by decide) (by change (Finmap.singleton 5 7 ∪ Finmap.singleton 7 0).lookup 5 = some 7; simp)
  have run2 := iteration (s := advance (start 5) 7)
    (h := Finmap.insert 5 0 (Finmap.singleton 5 7 ∪ Finmap.singleton 7 0))
    (nxt := 0) (by decide) (by change (Finmap.insert 5 0 (Finmap.singleton 5 7 ∪ Finmap.singleton 7 0)).lookup 7 = some 0; simp)
  have run := (run1.trans run2).trans (finish (by decide))
  refine ⟨_, _, run, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · change (Finmap.insert 7 5 (Finmap.insert 5 0 (Finmap.singleton 5 7 ∪ Finmap.singleton 7 0))).lookup 5 = some 0
    simp
  · change (Finmap.insert 7 5 (Finmap.insert 5 0 (Finmap.singleton 5 7 ∪ Finmap.singleton 7 0))).lookup 7 = some 5
    simp
  · exact (reversal_vcg two_nodes).2 run |>.2

end Cslib.IMP.SeparationVCGReversalTests
