/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Separation logic for heap IMP
-/
module

public import CSLibExt.Languages.IMP.HeapStep
public import CSLibExt.Languages.IMP.Hoare
public import CSLibExt.Languages.IMP.Equivalence

/-!
# Separation logic

Heap assertions are predicates on a store and a heap. The separating
conjunction `P ⋆ Q` splits the heap into two disjoint parts satisfying `P`
and `Q` respectively. `SepValid P c Q` is fault-avoiding validity: from
any store and heap satisfying `P`, the command `c` is safe (no reachable
configuration is stuck), and every terminating execution ends in a store
and heap satisfying `Q`.

The file proves the algebra of separating conjunction, the structural
rules, the local heap rules, the frame rule, and a bridge embedding
ordinary Hoare validity for heap-free commands.
-/

@[expose] public section

namespace Cslib.IMP

/-- **Heap assertion.** A heap assertion is a predicate on a store and a heap: it assigns a
proposition to every store $s$ and every heap $h$. Heap assertions serve as the preconditions
and postconditions of separation logic. -/
abbrev HAssertion := State → Heap → Prop

namespace HAssertion

/-- **Entailment of heap assertions.** A heap assertion $P$ entails a heap assertion $Q$ when, for
every store $s$ and every heap $h$, if $P$ holds of $s$ and $h$, then $Q$ holds of $s$ and $h$. -/
def Entails (P Q : HAssertion) : Prop :=
  ∀ ⦃s h⦄, P s h → Q s h

theorem entails_refl (P : HAssertion) : P.Entails P :=
  fun {_s _h} h => h

theorem Entails.trans {P Q R : HAssertion}
    (h1 : P.Entails Q) (h2 : Q.Entails R) : P.Entails R :=
  fun {_s _h} h => h2 (h1 h)

/-- **Empty-heap assertion.** The heap assertion $\mathrm{emp}$ holds of a store $s$ and a heap
$h$ exactly when $h$ is the empty heap, whatever the store $s$ is. -/
def emp : HAssertion := fun _ h => h = ∅

/-- **Pure assertion.** For a proposition $p$, the pure assertion of $p$ holds of a store $s$ and
a heap $h$ exactly when $h$ is the empty heap and $p$ is true. -/
def pure (p : Prop) : HAssertion := fun _ h => h = ∅ ∧ p

/-- **Points-to assertion.** For natural numbers $a$ and $v$, the assertion $a \mapsto v$ holds of
a store $s$ and a heap $h$ exactly when $h$ is the singleton heap that maps the address $a$ to the
value $v$ and allocates no other address. -/
def pointsTo (a v : Nat) : HAssertion :=
  fun _ h => h = Finmap.singleton a v

/-- **Separating conjunction.** For heap assertions $P$ and $Q$, the assertion $P \star Q$ holds
of a store $s$ and a heap $h$ when there are disjoint heaps $h_1$ and $h_2$ with
$h = h_1 \cup h_2$ such that $P(s, h_1)$ and $Q(s, h_2)$. -/
def star (P Q : HAssertion) : HAssertion :=
  fun s h => ∃ h₁ h₂, Heap.Disjoint h₁ h₂ ∧ h = h₁ ∪ h₂ ∧ P s h₁ ∧ Q s h₂

scoped infixr:60 " ⋆ " => star

/-- **Existential heap assertion.** For a function $p$ assigning a heap assertion $p(n)$ to each
natural number $n$ (an address or a value), the assertion $\exists n,\ p(n)$ holds of a store $s$
and a heap $h$ exactly when $p(n)$ holds of $s$ and $h$ for some natural number $n$. -/
def hexists (p : Nat → HAssertion) : HAssertion :=
  fun s h => ∃ a, p a s h

/-- **Conjunction of heap assertions.** For heap assertions $P$ and $Q$, the assertion
$P \wedge Q$ holds of a store $s$ and a heap $h$ exactly when $P$ holds of $s$ and $h$ and $Q$
holds of $s$ and the same heap $h$. -/
def hand (P Q : HAssertion) : HAssertion :=
  fun s h => P s h ∧ Q s h

theorem star_def {P Q : HAssertion} {s : State} {h : Heap} :
    (P ⋆ Q) s h ↔
      ∃ h₁ h₂, Heap.Disjoint h₁ h₂ ∧ h = h₁ ∪ h₂ ∧ P s h₁ ∧ Q s h₂ :=
  Iff.rfl

theorem star_comm {P Q : HAssertion} : (P ⋆ Q).Entails (Q ⋆ P) := by
  intro s h hPQ
  rw [star_def] at hPQ ⊢
  obtain ⟨h₁, h₂, hd, heq, hP, hQ⟩ := hPQ
  refine ⟨h₂, h₁, hd.symm, ?_, hQ, hP⟩
  rw [heq]
  exact Finmap.union_comm_of_disjoint hd

private theorem disjoint_union_left_iff {h₁ h₂ h₃ : Heap} :
    Heap.Disjoint (h₁ ∪ h₂) h₃ ↔ Heap.Disjoint h₁ h₃ ∧ Heap.Disjoint h₂ h₃ :=
  Finmap.disjoint_union_left h₁ h₂ h₃

private theorem disjoint_union_right_iff {h₁ h₂ h₃ : Heap} :
    Heap.Disjoint h₁ (h₂ ∪ h₃) ↔ Heap.Disjoint h₁ h₂ ∧ Heap.Disjoint h₁ h₃ :=
  Finmap.disjoint_union_right h₁ h₂ h₃

theorem star_assoc {P Q R : HAssertion} :
    ((P ⋆ Q) ⋆ R) = (P ⋆ (Q ⋆ R)) := by
  funext s h
  apply propext
  simp only [star_def]
  constructor
  · rintro ⟨h₁₂, h₃, hd, heq, ⟨h₁, h₂, hd₁₂, heq₁₂, hP, hQ⟩, hR⟩
    rw [heq₁₂] at hd
    obtain ⟨hd₁₃, hd₂₃⟩ := disjoint_union_left_iff.mp hd
    refine ⟨h₁, h₂ ∪ h₃, disjoint_union_right_iff.mpr ⟨hd₁₂, hd₁₃⟩, ?_,
      hP, ⟨h₂, h₃, hd₂₃, rfl, hQ, hR⟩⟩
    rw [heq, heq₁₂]
    exact Finmap.union_assoc
  · rintro ⟨h₁, h₂₃, hd, heq, hP, ⟨h₂, h₃, hd₂₃, heq₂₃, hQ, hR⟩⟩
    rw [heq₂₃] at hd
    obtain ⟨hd₁₂, hd₁₃⟩ := disjoint_union_right_iff.mp hd
    refine ⟨h₁ ∪ h₂, h₃, disjoint_union_left_iff.mpr ⟨hd₁₃, hd₂₃⟩, ?_,
      ⟨h₁, h₂, hd₁₂, rfl, hP, hQ⟩, hR⟩
    rw [heq, heq₂₃, Finmap.union_assoc]

theorem emp_star {P : HAssertion} : (emp ⋆ P) = P := by
  funext s h
  apply propext
  rw [star_def]
  constructor
  · rintro ⟨h₁, h₂, _hd, heq, hemp, hP⟩
    have h1 : h₁ = ∅ := hemp
    rw [heq, h1, Finmap.empty_union]
    exact hP
  · intro hP
    exact ⟨∅, h, Heap.disjoint_empty_left h, Finmap.empty_union.symm, rfl, hP⟩

theorem star_emp {P : HAssertion} : (P ⋆ emp) = P := by
  funext s h
  apply propext
  rw [star_def]
  constructor
  · rintro ⟨h₁, h₂, _hd, heq, hP, hemp⟩
    have h2 : h₂ = ∅ := hemp
    rw [heq, h2, Finmap.union_empty]
    exact hP
  · intro hP
    exact ⟨h, ∅, Heap.disjoint_empty_right h, Finmap.union_empty.symm, hP, rfl⟩

theorem star_mono {P₁ P₂ Q₁ Q₂ : HAssertion}
    (hP : P₁.Entails P₂) (hQ : Q₁.Entails Q₂) :
    (P₁ ⋆ Q₁).Entails (P₂ ⋆ Q₂) := by
  intro s h hstar
  rw [star_def] at hstar ⊢
  obtain ⟨h₁, h₂, hd, heq, h1, h2⟩ := hstar
  exact ⟨h₁, h₂, hd, heq, hP h1, hQ h2⟩

theorem pointsTo_disjoint_false {a v w : Nat} :
    (pointsTo a v ⋆ pointsTo a w).Entails (fun _ _ => False) := by
  intro s h hstar
  rw [star_def] at hstar
  obtain ⟨h₁, h₂, hd, _heq, h1, h2⟩ := hstar
  have e1 : h₁ = Finmap.singleton a v := h1
  have e2 : h₂ = Finmap.singleton a w := h2
  have m1 : a ∈ h₁ := by simp [e1]
  have m2 : a ∈ h₂ := by simp [e2]
  exact hd a m1 m2

end HAssertion

open scoped HAssertion

private theorem steps_eq_of_fst_skip {cfg cfg' : HConfig}
    (hskip : cfg.1 = .skip) (hsteps : HSteps cfg cfg') : cfg' = cfg := by
  obtain ⟨c, s, h⟩ := cfg
  change c = .skip at hskip
  subst hskip
  exact HSteps.skip_eq hsteps

private theorem safe_of_step_to_skip {c : HeapCmd} {s : State} {h : Heap}
    (hex : ∃ cfg', HStep (c, s, h) cfg')
    (hskip : ∀ cfg', HStep (c, s, h) cfg' → cfg'.1 = .skip) :
    Safe (c, s, h) := by
  intro cfg' hsteps
  rcases Relation.ReflTransGen.cases_head hsteps with rfl |
    ⟨next, hstep, htail⟩
  · exact Or.inr hex
  · have heq : cfg' = next := steps_eq_of_fst_skip (hskip next hstep) htail
    rw [heq]
    exact Or.inl (hskip next hstep)

private theorem step_of_steps_to_skip {c : HeapCmd} {s s' : State}
    {h h' : Heap}
    (hskip : ∀ cfg', HStep (c, s, h) cfg' → cfg'.1 = .skip)
    (hne : c ≠ .skip) (hsteps : HSteps (c, s, h) (.skip, s', h')) :
    HStep (c, s, h) (.skip, s', h') := by
  rcases Relation.ReflTransGen.cases_head hsteps with heq |
    ⟨next, hstep, htail⟩
  · simp only [Prod.mk.injEq] at heq
    exact absurd heq.1 hne
  · have hnext : next = (.skip, s', h') :=
      (steps_eq_of_fst_skip (hskip next hstep) htail).symm
    subst hnext
    exact hstep

namespace HSteps

private theorem seq_cases {c₁ c₂ : HeapCmd} {s : State} {h : Heap}
    {cfg : HConfig} (hsteps : HSteps (.seq c₁ c₂, s, h) cfg) :
    (∃ c₁' s' h', cfg = (.seq c₁' c₂, s', h') ∧
      HSteps (c₁, s, h) (c₁', s', h')) ∨
    (∃ sₘ hₘ, HSteps (c₁, s, h) (.skip, sₘ, hₘ) ∧
      HSteps (c₂, sₘ, hₘ) cfg) := by
  have key : ∀ {cfg : HConfig}, HSteps (.seq c₁ c₂, s, h) cfg →
      (∃ c₁' s' h', cfg = (.seq c₁' c₂, s', h') ∧
        HSteps (c₁, s, h) (c₁', s', h')) ∨
      (∃ sₘ hₘ, HSteps (c₁, s, h) (.skip, sₘ, hₘ) ∧
        HSteps (c₂, sₘ, hₘ) cfg) := by
    intro cfg hsteps
    induction hsteps with
    | refl => exact Or.inl ⟨c₁, s, h, rfl, .refl⟩
    | tail _hprev hstep ih =>
        rcases ih with ⟨c₁', s', h', rfl, hs1⟩ | ⟨sₘ, hₘ, hs1, hs2⟩
        · rw [HStep.seq_iff] at hstep
          rcases hstep with ⟨hskip, rfl⟩ | ⟨c₁'', s'', h'', hinner, rfl⟩
          · subst hskip
            exact Or.inr ⟨s', h', hs1, .refl⟩
          · exact Or.inl ⟨c₁'', s'', h'', rfl, hs1.tail hinner⟩
        · exact Or.inr ⟨sₘ, hₘ, hs1, hs2.tail hstep⟩
  exact key hsteps

end HSteps

private theorem insert_empty_singleton (a v : Nat) :
    Finmap.insert a v (∅ : Heap) = (Finmap.singleton a v : Heap) := by
  apply Finmap.ext_lookup
  intro x
  by_cases hx : x = a
  · subst hx
    rw [Finmap.lookup_insert, Finmap.lookup_singleton_eq]
  · rw [Finmap.lookup_insert_of_ne _ hx, Finmap.lookup_empty,
      Finmap.lookup_eq_none.mpr (by rw [Finmap.mem_singleton]; exact hx)]

private theorem erase_singleton_self (a v : Nat) :
    Finmap.erase a (Finmap.singleton a v : Heap) = (∅ : Heap) := by
  apply Finmap.ext_lookup
  intro x
  by_cases hx : x = a
  · subst hx
    rw [Finmap.lookup_erase, Finmap.lookup_empty]
  · rw [Finmap.lookup_erase_ne hx,
      Finmap.lookup_eq_none.mpr (by rw [Finmap.mem_singleton]; exact hx),
      Finmap.lookup_empty]

/-- **Separation-logic triple validity.** For heap assertions $P$, $Q$ and a heap command $c$,
the triple $\lbrace P \rbrace\ c\ \lbrace Q \rbrace$ is valid (in the fault-avoiding sense)
when, for every store $s$ and heap $h$ with $P(s, h)$, the configuration $(c, s, h)$ is safe
(no configuration reachable from it is stuck at a command other than $\mathtt{skip}$), and
whenever $(c, s, h)$ reaches $(\mathtt{skip}, s', h')$ in finitely many heap steps,
$Q(s', h')$ holds. -/
def SepValid (P : HAssertion) (c : HeapCmd) (Q : HAssertion) : Prop :=
  ∀ ⦃s h⦄, P s h → Safe (c, s, h) ∧
    ∀ ⦃s' h'⦄, HSteps (c, s, h) (.skip, s', h') → Q s' h'

/-- The configurations arising during a while-loop execution: at the
loop head with the invariant, at the unfolded conditional, or inside
the body partway through an iteration begun with the invariant and a
true guard. -/
private def WhilePhase (I : HAssertion) (guard : BExp) (body : HeapCmd)
    (cfg : HConfig) : Prop :=
  (∃ s h, cfg = (.while guard body, s, h) ∧ I s h) ∨
  (∃ s h, cfg = (.ite guard (.seq body (.while guard body)) .skip, s, h) ∧
    I s h) ∨
  (∃ c s h s₀ h₀, cfg = (.seq c (.while guard body), s, h) ∧
    HSteps (body, s₀, h₀) (c, s, h) ∧ I s₀ h₀ ∧ guard.eval s₀ = true)

private theorem WhilePhase.step {I : HAssertion} {guard : BExp}
    {body : HeapCmd}
    (hbody : SepValid (fun s h => I s h ∧ guard.eval s = true) body I)
    {cfg cfg' : HConfig} (hphase : WhilePhase I guard body cfg)
    (hstep : HStep cfg cfg') :
    WhilePhase I guard body cfg' ∨
      ∃ s h, cfg' = (.skip, s, h) ∧ I s h ∧ guard.eval s = false := by
  rcases hphase with ⟨s, h, rfl, hI⟩ | ⟨s, h, rfl, hI⟩ |
    ⟨c, s, h, s₀, h₀, rfl, hprefix, hI₀, hg₀⟩
  · rw [HStep.while_iff] at hstep
    subst hstep
    exact Or.inl (Or.inr (Or.inl ⟨s, h, rfl, hI⟩))
  · rw [HStep.ite_iff] at hstep
    rcases hstep with ⟨hg, rfl⟩ | ⟨hg, rfl⟩
    · exact Or.inl (Or.inr (Or.inr ⟨body, s, h, s, h, rfl, .refl, hI, hg⟩))
    · exact Or.inr ⟨s, h, rfl, hI, hg⟩
  · rw [HStep.seq_iff] at hstep
    rcases hstep with ⟨hskip, rfl⟩ | ⟨c', s', h', hinner, rfl⟩
    · subst hskip
      obtain ⟨-, hterm⟩ := hbody ⟨hI₀, hg₀⟩
      exact Or.inl (Or.inl ⟨s, h, rfl, hterm hprefix⟩)
    · exact Or.inl (Or.inr (Or.inr
        ⟨c', s', h', s₀, h₀, rfl, hprefix.tail hinner, hI₀, hg₀⟩))

private theorem WhilePhase.exists_step {I : HAssertion} {guard : BExp}
    {body : HeapCmd}
    (hbody : SepValid (fun s h => I s h ∧ guard.eval s = true) body I)
    {cfg : HConfig} (hphase : WhilePhase I guard body cfg) :
    ∃ cfg'', HStep cfg cfg'' := by
  rcases hphase with ⟨s, h, rfl, _hI⟩ | ⟨s, h, rfl, _hI⟩ |
    ⟨c, s, h, s₀, h₀, rfl, hprefix, hI₀, hg₀⟩
  · exact ⟨_, .whileStep guard body s h⟩
  · cases hg : guard.eval s with
    | true => exact ⟨_, .iteTrue hg⟩
    | false => exact ⟨_, .iteFalse hg⟩
  · obtain ⟨hsafe, -⟩ := hbody ⟨hI₀, hg₀⟩
    rcases hsafe _ hprefix with hsk | ⟨cfg'', hstep⟩
    · have hsk' : c = .skip := hsk
      subst hsk'
      exact ⟨_, .seqSkip (.while guard body) s h⟩
    · exact ⟨_, .seqStep hstep⟩

private theorem WhilePhase.of_steps {I : HAssertion} {guard : BExp}
    {body : HeapCmd}
    (hbody : SepValid (fun s h => I s h ∧ guard.eval s = true) body I)
    {cfg cfg' : HConfig} (hphase : WhilePhase I guard body cfg)
    (hsteps : HSteps cfg cfg') :
    WhilePhase I guard body cfg' ∨
      ∃ s h, cfg' = (.skip, s, h) ∧ I s h ∧ guard.eval s = false := by
  have key : ∀ {cfg' : HConfig}, HSteps cfg cfg' →
      WhilePhase I guard body cfg' ∨
        ∃ s h, cfg' = (.skip, s, h) ∧ I s h ∧ guard.eval s = false := by
    intro cfg' hsteps
    induction hsteps with
    | refl => exact Or.inl hphase
    | tail _hprev hstep ih =>
        rcases ih with hph | ⟨s₁, h₁, rfl, -, -⟩
        · exact WhilePhase.step hbody hph hstep
        · exact absurd hstep HStep.skip_not_step
  exact key hsteps

namespace SepValid

theorem skip (P : HAssertion) : SepValid P .skip P := by
  intro s h hP
  refine ⟨?_, ?_⟩
  · intro cfg' hsteps
    have heq := HSteps.skip_eq hsteps
    subst heq
    exact Or.inl rfl
  · intro s' h' hsteps
    have heq := HSteps.skip_eq hsteps
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_hc, rfl, rfl⟩ := heq
    exact hP

theorem assign {Q : HAssertion} (name : Nat) (value : AExp) :
    SepValid (fun s h => Q (Function.update s name (value.eval s)) h)
      (.assign name value) Q := by
  intro s h hpre
  have hskip : ∀ cfg', HStep (.assign name value, s, h) cfg' →
      cfg'.1 = .skip := by
    intro cfg' hstep
    rw [HStep.assign_iff] at hstep
    rw [hstep]
  refine ⟨?_, ?_⟩
  · exact safe_of_step_to_skip ⟨_, .assign s name value h⟩ hskip
  · intro s' h' hsteps
    have hstep := step_of_steps_to_skip hskip (by simp) hsteps
    rw [HStep.assign_iff] at hstep
    simp only [Prod.mk.injEq] at hstep
    obtain ⟨_hc, rfl, rfl⟩ := hstep
    exact hpre

theorem seq {P R Q : HAssertion} {c₁ c₂ : HeapCmd}
    (h₁ : SepValid P c₁ R) (h₂ : SepValid R c₂ Q) :
    SepValid P (.seq c₁ c₂) Q := by
  intro s h hpre
  obtain ⟨hsafe₁, hterm₁⟩ := h₁ hpre
  refine ⟨?_, ?_⟩
  · intro cfg' hsteps
    rcases HSteps.seq_cases hsteps with
      ⟨c₁', s', h', rfl, hs1⟩ | ⟨sₘ, hₘ, hs1, hs2⟩
    · rcases hsafe₁ _ hs1 with hsk | ⟨cfg'', hstep⟩
      · have hsk' : c₁' = .skip := hsk
        subst hsk'
        exact Or.inr ⟨_, .seqSkip c₂ s' h'⟩
      · exact Or.inr ⟨_, .seqStep hstep⟩
    · have hR : R sₘ hₘ := hterm₁ hs1
      obtain ⟨hsafe₂, -⟩ := h₂ hR
      exact hsafe₂ cfg' hs2
  · intro s' h' hsteps
    rcases HSteps.seq_cases hsteps with
      ⟨c₁', s'', h'', heq, -⟩ | ⟨sₘ, hₘ, hs1, hs2⟩
    · simp only [Prod.mk.injEq] at heq
      cases heq.1
    · have hR : R sₘ hₘ := hterm₁ hs1
      obtain ⟨-, hterm₂⟩ := h₂ hR
      exact hterm₂ hs2

theorem consequence {P P' Q Q' : HAssertion} {c : HeapCmd}
    (hpre : P.Entails P') (hvalid : SepValid P' c Q')
    (hpost : Q'.Entails Q) : SepValid P c Q := by
  intro s h hP
  obtain ⟨hsafe, hterm⟩ := hvalid (hpre hP)
  refine ⟨hsafe, ?_⟩
  intro s' h' hsteps
  exact hpost (hterm hsteps)

theorem ite {P Q : HAssertion} {guard : BExp} {t e : HeapCmd}
    (hthen : SepValid (fun s h => P s h ∧ guard.eval s = true) t Q)
    (helse : SepValid (fun s h => P s h ∧ guard.eval s = false) e Q) :
    SepValid P (.ite guard t e) Q := by
  intro s h hpre
  refine ⟨?_, ?_⟩
  · intro cfg' hsteps
    rcases Relation.ReflTransGen.cases_head hsteps with rfl |
      ⟨next, hstep, htail⟩
    · cases hg : guard.eval s with
      | true => exact Or.inr ⟨_, .iteTrue hg⟩
      | false => exact Or.inr ⟨_, .iteFalse hg⟩
    · rw [HStep.ite_iff] at hstep
      rcases hstep with ⟨hg, rfl⟩ | ⟨hg, rfl⟩
      · obtain ⟨hsafe, -⟩ := hthen ⟨hpre, hg⟩
        exact hsafe cfg' htail
      · obtain ⟨hsafe, -⟩ := helse ⟨hpre, hg⟩
        exact hsafe cfg' htail
  · intro s' h' hsteps
    rcases Relation.ReflTransGen.cases_head hsteps with heq |
      ⟨next, hstep, htail⟩
    · simp only [Prod.mk.injEq] at heq
      cases heq.1
    · rw [HStep.ite_iff] at hstep
      rcases hstep with ⟨hg, rfl⟩ | ⟨hg, rfl⟩
      · obtain ⟨-, hterm⟩ := hthen ⟨hpre, hg⟩
        exact hterm htail
      · obtain ⟨-, hterm⟩ := helse ⟨hpre, hg⟩
        exact hterm htail

/-- **Separation-logic while rule.** Let $I$ be a heap assertion, $b$ a Boolean expression and
$c$ a heap command. Write $I \wedge b$ for the assertion that holds of a store $s$ and a heap
$h$ when $I(s, h)$ holds and $b$ evaluates to true in $s$, and $I \wedge \neg b$ for the one
that holds when $I(s, h)$ holds and $b$ evaluates to false in $s$. If the triple
$\lbrace I \wedge b \rbrace\ c\ \lbrace I \rbrace$ is valid, then so is the triple
$\lbrace I \rbrace\ \mathtt{while}\ b\ \mathtt{do}\ c\ \lbrace I \wedge \neg b \rbrace$. -/
theorem whileLoop {I : HAssertion} {guard : BExp} {body : HeapCmd}
    (hbody : SepValid (fun s h => I s h ∧ guard.eval s = true) body I) :
    SepValid I (.while guard body)
      (fun s h => I s h ∧ guard.eval s = false) := by
  intro s h hI
  have hphase0 : WhilePhase I guard body (.while guard body, s, h) :=
    Or.inl ⟨s, h, rfl, hI⟩
  refine ⟨?_, ?_⟩
  · intro cfg' hsteps
    rcases WhilePhase.of_steps hbody hphase0 hsteps with hph |
      ⟨s₁, h₁, rfl, -, -⟩
    · exact Or.inr (WhilePhase.exists_step hbody hph)
    · exact Or.inl rfl
  · have key : ∀ {a b : HConfig}, HSteps a b →
        WhilePhase I guard body a →
        ∀ {s' h'}, b = (.skip, s', h') →
          I s' h' ∧ guard.eval s' = false := by
      intro a b hab
      induction hab using Relation.ReflTransGen.head_induction_on with
      | refl =>
          intro hphase s' h' rfl
          rcases hphase with ⟨s₁, h₁, heq, -⟩ | ⟨s₁, h₁, heq, -⟩ |
            ⟨_c, s₁, h₁, _s₀, _h₀, heq, -, -, -⟩ <;>
            simp only [Prod.mk.injEq] at heq <;> cases heq.1
      | head hstep htail ih =>
          intro hphase s' h' hb
          rcases WhilePhase.step hbody hphase hstep with hph |
            ⟨s₂, h₂, hnext, hI₂, hg₂⟩
          · exact ih hph hb
          · have hb2 := steps_eq_of_fst_skip (by rw [hnext]) htail
            rw [hb2, hnext] at hb
            simp only [Prod.mk.injEq] at hb
            obtain ⟨_hc, rfl, rfl⟩ := hb
            exact ⟨hI₂, hg₂⟩
    intro s' h' hsteps
    exact key hsteps hphase0 rfl

theorem read {Q : HAssertion} (name : Nat) (addr : AExp) :
    SepValid (fun s h => ∃ v, h = Finmap.singleton (addr.eval s) v ∧
        Q (Function.update s name v) h)
      (.read name addr) Q := by
  intro s h hpre
  have hskip : ∀ cfg', HStep (.read name addr, s, h) cfg' →
      cfg'.1 = .skip := by
    intro cfg' hstep
    rw [HStep.read_iff] at hstep
    obtain ⟨_v, -, rfl⟩ := hstep
    rfl
  obtain ⟨v, hh, hQ⟩ := hpre
  refine ⟨?_, ?_⟩
  · apply safe_of_step_to_skip _ hskip
    exact ⟨_, .read (show h.lookup (addr.eval s) = some v by
      rw [hh]; exact Finmap.lookup_singleton_eq)⟩
  · intro s' h' hsteps
    have hstep := step_of_steps_to_skip hskip (by simp) hsteps
    rw [HStep.read_iff] at hstep
    obtain ⟨v', hlookup, heq⟩ := hstep
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_hc, rfl, rfl⟩ := heq
    rw [hh, Finmap.lookup_singleton_eq] at hlookup
    rw [Option.some.injEq] at hlookup
    subst hlookup
    exact hQ

theorem write {Q : HAssertion} (addr value : AExp) :
    SepValid (fun s h => ∃ v, h = Finmap.singleton (addr.eval s) v ∧
        Q s (Finmap.singleton (addr.eval s) (value.eval s)))
      (.write addr value) Q := by
  intro s h hpre
  have hskip : ∀ cfg', HStep (.write addr value, s, h) cfg' →
      cfg'.1 = .skip := by
    intro cfg' hstep
    rw [HStep.write_iff] at hstep
    obtain ⟨-, rfl⟩ := hstep
    rfl
  obtain ⟨v, hh, hQ⟩ := hpre
  refine ⟨?_, ?_⟩
  · apply safe_of_step_to_skip _ hskip
    refine ⟨_, .write ?_⟩
    rw [hh]
    simp
  · intro s' h' hsteps
    have hstep := step_of_steps_to_skip hskip (by simp) hsteps
    rw [HStep.write_iff] at hstep
    obtain ⟨-, heq⟩ := hstep
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_hc, rfl, rfl⟩ := heq
    rw [hh, Finmap.insert_singleton_eq]
    exact hQ

theorem alloc {Q : HAssertion} (name : Nat) (value : AExp) :
    SepValid (fun s h => h = ∅ ∧ ∀ a,
        Q (Function.update s name a)
          (Finmap.singleton a (value.eval s)))
      (.alloc name value) Q := by
  intro s h hpre
  have hskip : ∀ cfg', HStep (.alloc name value, s, h) cfg' →
      cfg'.1 = .skip := by
    intro cfg' hstep
    rw [HStep.alloc_iff] at hstep
    obtain ⟨_a, -, rfl⟩ := hstep
    rfl
  obtain ⟨hh, hQ⟩ := hpre
  refine ⟨?_, ?_⟩
  · apply safe_of_step_to_skip _ hskip
    obtain ⟨a, ha⟩ := Heap.exists_notMem h
    exact ⟨_, .alloc ha⟩
  · intro s' h' hsteps
    have hstep := step_of_steps_to_skip hskip (by simp) hsteps
    rw [HStep.alloc_iff] at hstep
    obtain ⟨a, -, heq⟩ := hstep
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_hc, rfl, rfl⟩ := heq
    rw [hh, insert_empty_singleton]
    exact hQ a

theorem free {Q : HAssertion} (addr : AExp) :
    SepValid (fun s h => ∃ v, h = Finmap.singleton (addr.eval s) v ∧
        Q s ∅)
      (.free addr) Q := by
  intro s h hpre
  have hskip : ∀ cfg', HStep (.free addr, s, h) cfg' →
      cfg'.1 = .skip := by
    intro cfg' hstep
    rw [HStep.free_iff] at hstep
    obtain ⟨-, rfl⟩ := hstep
    rfl
  obtain ⟨v, hh, hQ⟩ := hpre
  refine ⟨?_, ?_⟩
  · apply safe_of_step_to_skip _ hskip
    refine ⟨_, .free ?_⟩
    rw [hh]
    simp
  · intro s' h' hsteps
    have hstep := step_of_steps_to_skip hskip (by simp) hsteps
    rw [HStep.free_iff] at hstep
    obtain ⟨-, heq⟩ := hstep
    simp only [Prod.mk.injEq] at heq
    obtain ⟨_hc, rfl, rfl⟩ := heq
    rw [hh, erase_singleton_self]
    exact hQ

/-- **Frame rule.** Let $P$, $Q$ and $R$ be heap assertions and $c$ a heap command. Suppose the
separation-logic triple with precondition $P$, command $c$ and postcondition $Q$ is valid, and
suppose that whenever $R$ holds of a store $s$ and a heap $h$, it also holds of $s'$ and $h$ for
every store $s'$ that agrees with $s$ on every variable outside the set of variables that $c$ may
assign to. Then the triple with precondition $P \star R$, command $c$ and postcondition
$Q \star R$ is valid, where $\star$ denotes separating conjunction. -/
theorem frame {P Q R : HAssertion} {c : HeapCmd}
    (hvalid : SepValid P c Q)
    (hR : ∀ ⦃s h s'⦄, R s h →
      (∀ x, x ∉ c.modVars → s' x = s x) → R s' h) :
    SepValid (P ⋆ R) c (Q ⋆ R) := by
  intro s h hpre
  rw [HAssertion.star_def] at hpre
  obtain ⟨h₁, hf, hd, rfl, hP, hRf⟩ := hpre
  obtain ⟨hsafeSmall, htermSmall⟩ := hvalid hP
  refine ⟨?_, ?_⟩
  · intro cfg' hstepsBig
    obtain ⟨c'', s'', h''⟩ := cfg'
    obtain ⟨h₂, _hs, hd₂, hEq, hsafeMid⟩ :=
      HSteps.decompose_of_safe hd hsafeSmall hstepsBig
    rcases hsafeMid _ .refl with hsk | hex
    · exact Or.inl hsk
    · obtain ⟨cfg''', hstepBig⟩ := HStep.exists_step_frame hd₂ hex
      refine Or.inr ⟨cfg''', ?_⟩
      rw [hEq]
      exact hstepBig
  · intro s' h' hstepsBig
    obtain ⟨h₂, hstepsSmall, hd₂, hEq, -⟩ :=
      HSteps.decompose_of_safe hd hsafeSmall hstepsBig
    have hQ := htermSmall hstepsSmall
    have hR' : R s' hf := hR hRf (HSteps.store_agree hstepsSmall)
    rw [HAssertion.star_def]
    exact ⟨h₂, hf, hd₂, hEq, hQ, hR'⟩

/-- **Hoare validity embeds into separation validity.** Let $P$ and $Q$ be store assertions and
$c$ a command of plain IMP. If the partial-correctness Hoare triple with precondition $P$, command
$c$ and postcondition $Q$ is valid, then the separation-logic triple for the embedding of $c$ into
heap IMP is valid with the precondition that holds of a store $s$ and any heap exactly when $P(s)$
holds and the postcondition that holds of a store $s$ and any heap exactly when $Q(s)$ holds.

Embedded commands are always safe, never change the heap, and terminate exactly when the plain
command does. -/
theorem of_valid {P Q : Assertion} {c : Cmd} (hvalid : Valid P c Q) :
    SepValid (fun s _ => P s) c.toHeap (fun s _ => Q s) := by
  intro s h hpre
  refine ⟨safe_toHeap c s h, ?_⟩
  intro s' h' hsteps
  obtain ⟨c₂, hEq, hSteps, _hh⟩ := HSteps.of_toHeap hsteps
  have hc : c₂ = .skip := Cmd.toHeap_eq_skip.mp hEq.symm
  subst hc
  exact Valid.iff_terminates.mp hvalid hpre hSteps

/-- **Framed embedding of Hoare validity.** Let $P$ and $Q$ be store assertions, $R$ a heap
assertion and $c$ a command of plain IMP, and write $\hat c$ for the embedding of $c$ into heap
IMP. Suppose the partial-correctness Hoare triple with precondition $P$, command $c$ and
postcondition $Q$ is valid, and suppose that whenever $R$ holds of a store $s$ and a heap $h$, it
also holds of $s'$ and $h$ for every store $s'$ that agrees with $s$ on every variable outside the
set of variables that $\hat c$ may assign to. Write $\tilde P$ and $\tilde Q$ for the heap
assertions that hold of a store $s$ and any heap exactly when $P(s)$, respectively $Q(s)$, holds.
Then the separation-logic triple with precondition $\tilde P \star R$, command $\hat c$ and
postcondition $\tilde Q \star R$ is valid, where $\star$ denotes separating conjunction. -/
theorem of_valid_frame {P Q : Assertion} {R : HAssertion} {c : Cmd}
    (h : Valid P c Q)
    (hR : ∀ ⦃s h s'⦄, R s h →
      (∀ x, x ∉ c.toHeap.modVars → s' x = s x) → R s' h) :
    SepValid ((fun s _ => P s) ⋆ R) c.toHeap ((fun s _ => Q s) ⋆ R) :=
  frame (of_valid h) hR

end SepValid

end Cslib.IMP
