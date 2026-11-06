/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.PDL.Algebra
import Cslib.Foundations.Relation.Preserves

/-!
# Partial correctness and loop invariants for PDL

`Hoare M P a Q` concerns all terminating relational executions; it does
not assert termination. Assertions are arbitrary sets of worlds, so an
invariant need not be expressible by a PDL formula.

The algebraic bridge is `P? * a ≤ a * Q?`. The guarded while rule uses
exactly `(guard?; body)*; (not guard)?` in the existing program syntax.
Reachable PDL induction only assumes preservation at states reachable
from the chosen initial world, not at unrelated worlds.
-/

@[expose] public section

namespace Cslib.PDL

open RelationAlgebra

variable {World Atom Label : Type*}
  {M : Model World Atom Label} {P Q I : Set World}
  {a b : Program Atom Label}

/-- **Partial-correctness Hoare triple for PDL programs.**
Every execution of `a` from `P` ends in `Q`, without a termination
requirement. -/
def Hoare (M : Model World Atom Label) (P : Set World)
    (a : Program Atom Label) (Q : Set World) : Prop :=
  ∀ ⦃s t⦄, s ∈ P → ProgRel M a s t → t ∈ Q

/-- **Partial correctness as inclusion in the relational core.**
Partial correctness agrees with the canonical relation's core. -/
theorem hoare_iff_subset_core :
    Hoare M P a Q ↔ P ⊆ SetRel.core (a.toRelation M) Q := by
  constructor
  · intro h s hP t hR
    exact h hP hR
  · intro h s t hP hR
    exact h hP hR

/-- **Hoare triples as KAT test inequalities.**
Hoare verification is equivalent to the KAT test inequality. -/
theorem hoare_iff_test_le :
    Hoare M P a Q ↔ testSet P * a.toRelation M ≤
      a.toRelation M * testSet Q :=
  hoare_iff_subset_core.trans
    (test_mul_le_mul_test_iff P Q (a.toRelation M)).symm

/-- **Hoare triples as KAT absorption equations.**
The equivalent KAT absorption equation for verification. -/
theorem hoare_iff_test_eq :
    Hoare M P a Q ↔ testSet P * a.toRelation M =
      testSet P * a.toRelation M * testSet Q :=
  hoare_iff_subset_core.trans
    (test_mul_eq_test_mul_test_iff P Q (a.toRelation M)).symm

/-- **Hoare triples with formula assertions as box validity.**
Formula assertions connect Hoare verification to global PDL validity,
not just an atomic-action modality. -/
theorem hoare_iff_box (φ ψ : Formula Atom Label) :
    Hoare M {s | Sat M φ s} a {s | Sat M ψ s} ↔
      ∀ s, Sat M (.imp φ (.box a ψ)) s := by
  constructor
  · intro h s hφ t hR
    exact h hφ hR
  · intro h s t hφ hR
    exact h s hφ t hR

namespace Hoare

/-- **Hoare rule of consequence.** Strengthen the precondition and weaken the postcondition. -/
theorem consequence {P' Q' : Set World} (h : Hoare M P a Q)
    (hP : P' ⊆ P) (hQ : Q ⊆ Q') : Hoare M P' a Q' :=
  fun _ _ hP' hR => hQ (h (hP hP') hR)

/-- **Hoare rule for sequential composition.**
Sequential verification uses the first postcondition as the second
precondition. -/
theorem seq (ha : Hoare M P a I) (hb : Hoare M I b Q) :
    Hoare M P (.seq a b) Q := by
  rintro s t hP ⟨u, hsa, hut⟩
  exact hb (ha hP hsa) hut

/-- **Hoare rule for nondeterministic choice.**
Nondeterministic choice is safe exactly when both branches are. -/
theorem choice_iff :
    Hoare M P (.choice a b) Q ↔ Hoare M P a Q ∧ Hoare M P b Q := by
  constructor
  · intro h
    exact ⟨fun _ _ hP hR => h hP (Or.inl hR),
      fun _ _ hP hR => h hP (Or.inr hR)⟩
  · rintro ⟨ha, hb⟩ s t hP (hR | hR)
    · exact ha hP hR
    · exact hb hP hR

/-- **Hoare rule for formula tests.**
A formula test requires the postcondition only where the test passes. -/
theorem test_iff (φ : Formula Atom Label) :
    Hoare M P (.test φ) Q ↔ P ∩ {s | Sat M φ s} ⊆ Q := by
  constructor
  · intro h s ⟨hP, hφ⟩
    exact h hP ⟨rfl, hφ⟩
  · rintro h s t hP ⟨rfl, hφ⟩
    exact h ⟨hP, hφ⟩

/-- **Hoare invariant rule for iteration.**
A one-step invariant holds after every finite number of iterations,
including zero, via CSLib's canonical closure-preservation theorem. -/
theorem star (h : Hoare M I a I) : Hoare M I (.star a) I := by
  have hp : Relation.Preserves (ProgRel M a) I :=
    fun _ _ hR hI => h hI hR
  have hrtc := Relation.preserves_reflTransGen_iff.mpr hp
  exact fun _ _ hI hR => hrtc hR hI

end Hoare

/-- **Guarded while loop in PDL.** A guarded loop in the existing PDL syntax: iterate guarded body
steps, then test that the guard is false. -/
def Program.whileDo (guard : Formula Atom Label)
    (body : Program Atom Label) : Program Atom Label :=
  .seq (.star (.seq (.test guard) body)) (.test (.imp guard .bot))

namespace Hoare

/-- **Hoare invariant rule for guarded while loops.**
The guarded-loop invariant rule is partial correctness, including
zero-step exits; it does not guarantee termination. -/
theorem whileDo (guard : Formula Atom Label)
    (h : Hoare M (I ∩ {s | Sat M guard s}) a I) :
    Hoare M I (Program.whileDo guard a) (I ∩ {s | ¬ Sat M guard s}) := by
  have hbody : Hoare M I (.seq (.test guard) a) I := by
    rintro s t hI ⟨u, ⟨rfl, hguard⟩, hR⟩
    exact h ⟨hI, hguard⟩ hR
  have hiter := star hbody
  rintro s t hI ⟨u, hR, rfl, hguard⟩
  exact ⟨hiter hI hR, hguard⟩

/-- **While-loop rule with initialization and exit implication.**
Verify a guarded loop using initialization, invariant preservation,
and the exit implication to the desired postcondition. -/
theorem whileDo_consequence (guard : Formula Atom Label)
    (hinit : P ⊆ I) (hbody : Hoare M (I ∩ {s | Sat M guard s}) a I)
    (hexit : I ∩ {s | ¬ Sat M guard s} ⊆ Q) :
    Hoare M P (Program.whileDo guard a) Q :=
  (whileDo guard hbody).consequence hinit hexit

/-- **Semantic completeness of the while-loop invariant rule.**
The guarded-loop rule is semantically complete for arbitrary set
assertions. The witness is guarded-body reachability from `P`, independent
of `Q`; this is not a completeness claim for a syntactic assertion language. -/
theorem whileDo_iff_exists_invariant (guard : Formula Atom Label) :
    Hoare M P (Program.whileDo guard a) Q ↔
      ∃ I : Set World, P ⊆ I ∧
        Hoare M (I ∩ {s | Sat M guard s}) a I ∧
        I ∩ {s | ¬ Sat M guard s} ⊆ Q := by
  constructor
  · intro h
    let I : Set World := SetRel.image
      ((Program.star (.seq (.test guard) a)).toRelation M) P
    refine ⟨I, ?_, ?_, ?_⟩
    · intro s hP
      exact ⟨s, hP, Relation.ReflTransGen.refl⟩
    · rintro s t ⟨⟨u, hP, hpath⟩, hguard⟩ hbody
      exact ⟨u, hP, hpath.tail ⟨s, ⟨rfl, hguard⟩, hbody⟩⟩
    · rintro t ⟨⟨s, hP, hpath⟩, hguard⟩
      exact h hP ⟨t, hpath, rfl, hguard⟩
  · rintro ⟨I, hinit, hbody, hexit⟩
    exact whileDo_consequence guard hinit hbody hexit

end Hoare

/-- **PDL induction restricted to reachable states.**
PDL induction restricted to states reachable from the initial world.
This proves `[a*](φ → [a]φ) → (φ → [a*]φ)` without assuming preservation
on unreachable states. -/
theorem sat_box_star_induction {φ : Formula Atom Label} {s : World}
    (hstep : Sat M (.box (.star a) (.imp φ (.box a φ))) s)
    (hinit : Sat M φ s) : Sat M (.box (.star a) φ) s := by
  intro t hpath
  induction hpath with
  | refl => exact hinit
  | @tail u v hpath hstep' ih => exact hstep u hpath ih v hstep'

/-- **Test absorption lifts through iteration.**
Concrete relational test absorption lifts through PDL iteration,
connecting the algebraic verification equation to closure invariance. -/
theorem test_mul_star_absorption
    (h : testSet I * a.toRelation M =
      testSet I * a.toRelation M * testSet I) :
    testSet I * a.star.toRelation M =
      testSet I * a.star.toRelation M * testSet I :=
  hoare_iff_test_eq.mp (Hoare.star (hoare_iff_test_eq.mpr h))

/-- **Loop exit absorption from a guarded-body absorption equation.**
A guarded-body verification equation implies the loop's exit
verification equation over the same canonical relational carrier. -/
theorem test_mul_whileDo_absorption (guard : Formula Atom Label)
    (h : testSet (I ∩ {s | Sat M guard s}) * a.toRelation M =
      testSet (I ∩ {s | Sat M guard s}) * a.toRelation M * testSet I) :
    testSet I * (Program.whileDo guard a).toRelation M =
      testSet I * (Program.whileDo guard a).toRelation M *
        testSet (I ∩ {s | ¬ Sat M guard s}) :=
  hoare_iff_test_eq.mp (Hoare.whileDo guard (hoare_iff_test_eq.mpr h))

end Cslib.PDL
