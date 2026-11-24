/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Heap-manipulating commands and small-step semantics for IMP
-/
module

public import CSLibExt.Languages.IMP.Syntax
public import CSLibExt.Languages.IMP.Heap
public import CSLibExt.Languages.IMP.SmallStep
public import Mathlib.Logic.Relation

/-!
# Small-step semantics for heap-manipulating commands

`HeapCmd` extends IMP with heap read, write, allocation, and disposal.
`HStep` is the small-step relation on configurations pairing a command
with a store and a heap, and `HSteps` is its reflexive, transitive
closure. A configuration is `Safe` when no reachable configuration is
stuck at a command other than `skip`.

The locality lemmas say that an execution on a large heap `h ∪ hf`
projects to an execution on `h` alone, leaving the frame `hf` untouched,
provided the small configuration is safe. These are the operational
facts the separation-logic frame rule needs. Plain IMP embeds into the
heap language via `Cmd.toHeap`, with the heap unchanged throughout.
-/

@[expose] public section

namespace Cslib.IMP

/-- **Heap commands.** Heap commands extend the commands of IMP with heap operations. A heap
command is one of: $\mathbf{skip}$; an assignment $x := a$; a sequence $c_1; c_2$; a
conditional $\mathbf{if}\ b\ \mathbf{then}\ c_1\ \mathbf{else}\ c_2$; a loop
$\mathbf{while}\ b\ \mathbf{do}\ c$; a heap read $x := [a]$; a heap write $[a] := e$; an
allocation $x := \mathbf{alloc}(e)$; or a deallocation $\mathbf{free}(a)$. Here $x$ is a variable
(a natural number), $a$ and $e$ are arithmetic expressions, $b$ is a Boolean expression, and $c$,
$c_1$, $c_2$ are heap commands. -/
inductive HeapCmd where
  | skip
  | assign (name : Nat) (value : AExp)
  | seq (first second : HeapCmd)
  | ite (guard : BExp) (thenBranch elseBranch : HeapCmd)
  | while (guard : BExp) (body : HeapCmd)
  | read (name : Nat) (addr : AExp)
  | write (addr value : AExp)
  | alloc (name : Nat) (value : AExp)
  | free (addr : AExp)
  deriving DecidableEq, Repr

/-- **Heap configurations.** A heap configuration is a triple $(c, s, h)$ of a heap command $c$,
a store $s$ and a heap $h$. -/
abbrev HConfig := HeapCmd × State × Heap

/-- **Small-step semantics of heap commands.** The single-step relation
$(c, s, h) \to (c', s', h')$ on heap configurations is the least relation closed under the rules
below. Here $a(s)$ is the value of an expression $a$ in the store $s$, $s[x \mapsto n]$ is $s$
with variable $x$ set to $n$, $h[\ell \mapsto n]$ is $h$ with address $\ell$ set to $n$, and
$h \setminus \ell$ is $h$ with address $\ell$ removed.

- Assignment: $(x := a, s, h) \to (\mathbf{skip}, s[x \mapsto a(s)], h)$.
- Sequence: $(\mathbf{skip}; c_2, s, h) \to (c_2, s, h)$, and if
  $(c_1, s, h) \to (c_1', s', h')$ then $(c_1; c_2, s, h) \to (c_1'; c_2, s', h')$.
- Conditional: $(\mathbf{if}\ b\ \mathbf{then}\ c_1\ \mathbf{else}\ c_2, s, h)$ steps to
  $(c_1, s, h)$ if $b(s)$ is true and to $(c_2, s, h)$ if $b(s)$ is false.
- Loop: $(\mathbf{while}\ b\ \mathbf{do}\ c, s, h)$ steps to
  $(\mathbf{if}\ b\ \mathbf{then}\ d\ \mathbf{else}\ \mathbf{skip}, s, h)$, where $d$ is the
  sequence $c; \mathbf{while}\ b\ \mathbf{do}\ c$.
- Read: if $h$ maps the address $a(s)$ to $v$, then
  $(x := [a], s, h) \to (\mathbf{skip}, s[x \mapsto v], h)$.
- Write: if $a(s)$ is allocated in $h$, then
  $([a] := e, s, h) \to (\mathbf{skip}, s, h[a(s) \mapsto e(s)])$.
- Allocation: for every address $\ell$ not allocated in $h$,
  $(x := \mathbf{alloc}(e), s, h) \to (\mathbf{skip}, s[x \mapsto \ell], h[\ell \mapsto e(s)])$.
- Deallocation: if $a(s)$ is allocated in $h$, then
  $(\mathbf{free}(a), s, h) \to (\mathbf{skip}, s, h \setminus a(s))$. -/
inductive HStep : HConfig → HConfig → Prop
  | assign (state) (name) (value) (heap) :
      HStep (.assign name value, state, heap)
        (.skip, Function.update state name (value.eval state), heap)
  | seqSkip (second) (state) (heap) :
      HStep (.seq .skip second, state, heap) (second, state, heap)
  | seqStep {first first' second initial final heap heap'}
      (step : HStep (first, initial, heap) (first', final, heap')) :
      HStep (.seq first second, initial, heap) (.seq first' second, final, heap')
  | iteTrue {guard thenBranch elseBranch state heap}
      (guardTrue : guard.eval state = true) :
      HStep (.ite guard thenBranch elseBranch, state, heap) (thenBranch, state, heap)
  | iteFalse {guard thenBranch elseBranch state heap}
      (guardFalse : guard.eval state = false) :
      HStep (.ite guard thenBranch elseBranch, state, heap) (elseBranch, state, heap)
  | whileStep (guard) (body) (state) (heap) :
      HStep (.while guard body, state, heap)
        (.ite guard (.seq body (.while guard body)) .skip, state, heap)
  | read {name addr state heap value}
      (lookup : heap.lookup (addr.eval state) = some value) :
      HStep (.read name addr, state, heap)
        (.skip, Function.update state name value, heap)
  | write {addr value state heap}
      (mem : addr.eval state ∈ heap) :
      HStep (.write addr value, state, heap)
        (.skip, state, Finmap.insert (addr.eval state) (value.eval state) heap)
  | alloc {name value state heap address}
      (notMem : address ∉ heap) :
      HStep (.alloc name value, state, heap)
        (.skip, Function.update state name address,
          Finmap.insert address (value.eval state) heap)
  | free {addr state heap}
      (mem : addr.eval state ∈ heap) :
      HStep (.free addr, state, heap)
        (.skip, state, Finmap.erase (addr.eval state) heap)

/-- **Multi-step heap execution.** The relation $(c, s, h) \to^* (c', s', h')$ on heap
configurations is the reflexive-transitive closure of the small-step relation: it holds when the
first configuration reaches the second by a finite, possibly empty, sequence of small steps. -/
abbrev HSteps : HConfig → HConfig → Prop := Relation.ReflTransGen HStep

/-- **Safe heap configurations.** A heap configuration, consisting of a heap command, a store and
a heap, is safe when every heap configuration reachable from it in zero or more heap steps
either has command $\mathtt{skip}$ or can take a further heap step. -/
def Safe (cfg : HConfig) : Prop :=
  ∀ cfg', HSteps cfg cfg' → cfg'.1 = .skip ∨ ∃ cfg'', HStep cfg' cfg''

namespace HStep

theorem skip_not_step {state : State} {heap : Heap} {next : HConfig} :
    ¬ HStep (.skip, state, heap) next := by
  intro h
  cases h

@[simp]
theorem assign_iff {name : Nat} {value : AExp} {state : State} {heap : Heap}
    {next : HConfig} :
    HStep (.assign name value, state, heap) next ↔
      next = (.skip, Function.update state name (value.eval state), heap) := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .assign state name value heap

theorem seq_iff {first second : HeapCmd} {state : State} {heap : Heap}
    {next : HConfig} :
    HStep (.seq first second, state, heap) next ↔
      (first = .skip ∧ next = (second, state, heap)) ∨
      ∃ first' state' heap', HStep (first, state, heap) (first', state', heap') ∧
        next = (.seq first' second, state', heap') := by
  constructor
  · intro h
    cases h with
    | seqSkip => exact Or.inl ⟨rfl, rfl⟩
    | seqStep hstep => exact Or.inr ⟨_, _, _, hstep, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨first', state', heap', hstep, rfl⟩)
    · exact .seqSkip second state heap
    · exact .seqStep hstep

theorem ite_iff {guard : BExp} {t e : HeapCmd} {state : State} {heap : Heap}
    {next : HConfig} :
    HStep (.ite guard t e, state, heap) next ↔
      (guard.eval state = true ∧ next = (t, state, heap)) ∨
      (guard.eval state = false ∧ next = (e, state, heap)) := by
  constructor
  · intro h
    cases h with
    | iteTrue hg => exact Or.inl ⟨hg, rfl⟩
    | iteFalse hg => exact Or.inr ⟨hg, rfl⟩
  · rintro (⟨hg, rfl⟩ | ⟨hg, rfl⟩)
    · exact .iteTrue hg
    · exact .iteFalse hg

@[simp]
theorem while_iff {guard : BExp} {body : HeapCmd} {state : State} {heap : Heap}
    {next : HConfig} :
    HStep (.while guard body, state, heap) next ↔
      next = (.ite guard (.seq body (.while guard body)) .skip, state, heap) := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .whileStep guard body state heap

theorem read_iff {name : Nat} {addr : AExp} {state : State} {heap : Heap}
    {next : HConfig} :
    HStep (.read name addr, state, heap) next ↔
      ∃ value, heap.lookup (addr.eval state) = some value ∧
        next = (.skip, Function.update state name value, heap) := by
  constructor
  · intro h
    cases h with
    | read hlookup => exact ⟨_, hlookup, rfl⟩
  · rintro ⟨value, hlookup, rfl⟩
    exact .read hlookup

theorem write_iff {addr value : AExp} {state : State} {heap : Heap}
    {next : HConfig} :
    HStep (.write addr value, state, heap) next ↔
      addr.eval state ∈ heap ∧
        next = (.skip, state,
          Finmap.insert (addr.eval state) (value.eval state) heap) := by
  constructor
  · intro h
    cases h with
    | write hmem => exact ⟨hmem, rfl⟩
  · rintro ⟨hmem, rfl⟩
    exact .write hmem

theorem alloc_iff {name : Nat} {value : AExp} {state : State} {heap : Heap}
    {next : HConfig} :
    HStep (.alloc name value, state, heap) next ↔
      ∃ address, address ∉ heap ∧
        next = (.skip, Function.update state name address,
          Finmap.insert address (value.eval state) heap) := by
  constructor
  · intro h
    cases h with
    | alloc hnotMem => exact ⟨_, hnotMem, rfl⟩
  · rintro ⟨address, hnotMem, rfl⟩
    exact .alloc hnotMem

theorem free_iff {addr : AExp} {state : State} {heap : Heap} {next : HConfig} :
    HStep (.free addr, state, heap) next ↔
      addr.eval state ∈ heap ∧
        next = (.skip, state, Finmap.erase (addr.eval state) heap) := by
  constructor
  · intro h
    cases h with
    | free hmem => exact ⟨hmem, rfl⟩
  · rintro ⟨hmem, rfl⟩
    exact .free hmem

end HStep

namespace HSteps

theorem single {x y : HConfig} (h : HStep x y) : HSteps x y :=
  Relation.ReflTransGen.single h

theorem seq_congr {first first' : HeapCmd} {second : HeapCmd}
    {initial final : State} {heap heap' : Heap}
    (h : HSteps (first, initial, heap) (first', final, heap')) :
    HSteps (.seq first second, initial, heap) (.seq first' second, final, heap') := by
  have key : ∀ {x y : HConfig}, HSteps x y →
      HSteps (.seq x.1 second, x.2.1, x.2.2) (.seq y.1 second, y.2.1, y.2.2) := by
    intro x y hxy
    induction hxy with
    | refl => exact .refl
    | tail _hsteps hstep ih => exact ih.tail (.seqStep hstep)
  exact key h

theorem seq_skip {second : HeapCmd} {state : State} {heap : Heap} :
    HSteps (.seq .skip second, state, heap) (second, state, heap) :=
  single (.seqSkip second state heap)

theorem skip_eq {state : State} {heap : Heap} {cfg : HConfig}
    (h : HSteps (.skip, state, heap) cfg) : cfg = (.skip, state, heap) := by
  induction h with
  | refl => rfl
  | tail _hsteps hstep ih =>
      rw [ih] at hstep
      exact absurd hstep HStep.skip_not_step

end HSteps

/-- **Safety is preserved along executions.** If a heap configuration is safe and reaches a second
configuration by finitely many (possibly zero) small steps, then the second configuration is
safe. -/
theorem Safe.of_steps {cfg cfg' : HConfig} (hsafe : Safe cfg)
    (hsteps : HSteps cfg cfg') : Safe cfg' :=
  fun cfg'' h => hsafe cfg'' (hsteps.trans h)

namespace HStep

/-- **Adding a frame heap preserves the ability to step.** Let $h$ and $h_f$ be disjoint heaps,
$c$ a heap command and $s$ a store. If the configuration $(c, s, h)$ can take a small step, then
so can $(c, s, h \cup h_f)$.

Allocation may choose a different fresh address on the larger heap. -/
theorem exists_step_frame {c : HeapCmd} {s : State} {h hf : Heap}
    (_hd : Heap.Disjoint h hf) (hex : ∃ cfg', HStep (c, s, h) cfg') :
    ∃ cfg', HStep (c, s, h ∪ hf) cfg' := by
  have key : ∀ {cfg cfg' : HConfig} {hf : Heap}, HStep cfg cfg' →
      ∃ cfg'', HStep (cfg.1, cfg.2.1, cfg.2.2 ∪ hf) cfg'' := by
    intro cfg cfg' hf hstep
    induction hstep with
    | assign state name value heap =>
        exact ⟨_, .assign state name value _⟩
    | seqSkip second state heap =>
        exact ⟨_, .seqSkip second state _⟩
    | seqStep _hstep ih =>
        obtain ⟨cfg'', hs⟩ := ih
        exact ⟨_, .seqStep hs⟩
    | iteTrue hg => exact ⟨_, .iteTrue hg⟩
    | iteFalse hg => exact ⟨_, .iteFalse hg⟩
    | whileStep guard body state heap =>
        exact ⟨_, .whileStep guard body state _⟩
    | read hlookup =>
        rw [← Finmap.lookup_union_left (s₂ := hf)
          (Finmap.mem_of_lookup_eq_some hlookup)] at hlookup
        exact ⟨_, .read hlookup⟩
    | write hmem =>
        exact ⟨_, .write (Finmap.mem_union.mpr (Or.inl hmem))⟩
    | alloc _hnotMem =>
        exact ⟨_, .alloc (Heap.exists_notMem _).choose_spec⟩
    | free hmem =>
        exact ⟨_, .free (Finmap.mem_union.mpr (Or.inl hmem))⟩
  obtain ⟨cfg', hstep⟩ := hex
  exact key (hf := hf) hstep

/-- **Frame decomposition of a single heap step.** Let $h$ and $h_f$ be disjoint heaps, $c$ a heap
command and $s$ a store, and suppose that the configuration $(c, s, h)$ can take a small step. If
$(c, s, h \cup h_f)$ takes a small step to $(c', s', h'')$, then there is a heap $h_1$, disjoint
from $h_f$, such that $(c, s, h)$ takes a small step to $(c', s', h_1)$ and $h'' = h_1 \cup h_f$.

The step-existence hypothesis forces any address the step touches to lie in $h$. -/
theorem decompose_of_safe_step {c c' : HeapCmd} {s s' : State} {h hf h'' : Heap}
    (hd : Heap.Disjoint h hf) (hex : ∃ cfg', HStep (c, s, h) cfg')
    (hstep : HStep (c, s, h ∪ hf) (c', s', h'')) :
    ∃ h₁, HStep (c, s, h) (c', s', h₁) ∧ Heap.Disjoint h₁ hf ∧ h'' = h₁ ∪ hf := by
  revert hd hex hstep
  induction c generalizing s h c' s' h'' with
  | skip =>
      intro _hd _hex hstep
      cases hstep
  | assign name value =>
      intro hd _hex hstep
      cases hstep
      exact ⟨h, .assign s name value h, hd, rfl⟩
  | seq first second ihFirst _ihSecond =>
      intro hd hex hstep
      cases hstep with
      | seqSkip => exact ⟨h, .seqSkip second s h, hd, rfl⟩
      | seqStep hinner =>
          obtain ⟨_cfgSmall, hsmall⟩ := hex
          rw [seq_iff] at hsmall
          rcases hsmall with ⟨hskip, _⟩ | ⟨f₂, s₂, h₂, hstepSmall, _⟩
          · subst hskip
            exact absurd hinner skip_not_step
          · obtain ⟨h₁, hs₁, hd₁, heq⟩ :=
              ihFirst hd ⟨(f₂, s₂, h₂), hstepSmall⟩ hinner
            exact ⟨h₁, .seqStep hs₁, hd₁, heq⟩
  | ite _guard _t _e _ihT _ihE =>
      intro hd _hex hstep
      cases hstep with
      | iteTrue hg => exact ⟨h, .iteTrue hg, hd, rfl⟩
      | iteFalse hg => exact ⟨h, .iteFalse hg, hd, rfl⟩
  | «while» guard body _ihBody =>
      intro hd _hex hstep
      cases hstep
      exact ⟨h, .whileStep guard body s h, hd, rfl⟩
  | read _name addr =>
      intro hd hex hstep
      cases hstep with
      | read hlookup =>
          obtain ⟨_cfgSmall, hsmall⟩ := hex
          rw [read_iff] at hsmall
          obtain ⟨_value, hlookupSmall, _⟩ := hsmall
          have hmem : addr.eval s ∈ h :=
            Finmap.mem_of_lookup_eq_some hlookupSmall
          rw [Finmap.lookup_union_left hmem] at hlookup
          exact ⟨h, .read hlookup, hd, rfl⟩
  | write addr value =>
      intro hd hex hstep
      cases hstep with
      | write _hmemBig =>
          obtain ⟨_cfgSmall, hsmall⟩ := hex
          rw [write_iff] at hsmall
          obtain ⟨hmemSmall, _⟩ := hsmall
          have hnotHf : addr.eval s ∉ hf := hd _ hmemSmall
          refine ⟨Finmap.insert (addr.eval s) (value.eval s) h, .write hmemSmall,
            ?_, Finmap.insert_union⟩
          exact Heap.disjoint_insert_left hd hnotHf
  | alloc _name _value =>
      intro hd _hex hstep
      cases hstep with
      | alloc hnotBig =>
          have hnotH : ∀ {a : Nat}, a ∉ h ∪ hf → a ∉ h :=
            fun ha haH => ha (Finmap.mem_union.mpr (Or.inl haH))
          refine ⟨_, .alloc (hnotH hnotBig), ?_, Finmap.insert_union⟩
          apply Heap.disjoint_insert_left hd
          intro haHf
          exact hnotBig (Finmap.mem_union.mpr (Or.inr haHf))
  | free addr =>
      intro hd hex hstep
      cases hstep with
      | free _hmemBig =>
          obtain ⟨_cfgSmall, hsmall⟩ := hex
          rw [free_iff] at hsmall
          obtain ⟨hmemSmall, _⟩ := hsmall
          have hnotHf : addr.eval s ∉ hf := hd _ hmemSmall
          exact ⟨Finmap.erase (addr.eval s) h, .free hmemSmall,
            Heap.disjoint_erase_left hd, Heap.erase_union_of_notMem hnotHf⟩

end HStep

namespace HSteps

/-- **Frame decomposition of heap executions.** Let $h$ and $h_f$ be disjoint heaps, $c$ a heap
command and $s$ a store, and suppose that the configuration $(c, s, h)$ is safe. If
$(c, s, h \cup h_f)$ reaches $(c'', s'', h'')$ by finitely many (possibly zero) small steps, then
there is a heap $h_2$, disjoint from $h_f$, such that $(c, s, h)$ reaches $(c'', s'', h_2)$ by
finitely many small steps, $h'' = h_2 \cup h_f$, and $(c'', s'', h_2)$ is safe.

Safety supplies the step-existence that single-step decomposition needs at each stage. -/
theorem decompose_of_safe {c c'' : HeapCmd} {s s'' : State} {h hf h'' : Heap}
    (hd : Heap.Disjoint h hf) (hsafe : Safe (c, s, h))
    (hsteps : HSteps (c, s, h ∪ hf) (c'', s'', h'')) :
    ∃ h₂, HSteps (c, s, h) (c'', s'', h₂) ∧ Heap.Disjoint h₂ hf ∧
      h'' = h₂ ∪ hf ∧ Safe (c'', s'', h₂) := by
  have decompCfg : ∀ {cfgMid cfgEnd : HConfig} {hsmall : Heap},
      Heap.Disjoint hsmall hf →
      (∃ cfg', HStep (cfgMid.1, cfgMid.2.1, hsmall) cfg') →
      cfgMid.2.2 = hsmall ∪ hf → HStep cfgMid cfgEnd →
      ∃ h₁, HStep (cfgMid.1, cfgMid.2.1, hsmall) (cfgEnd.1, cfgEnd.2.1, h₁) ∧
        Heap.Disjoint h₁ hf ∧ cfgEnd.2.2 = h₁ ∪ hf := by
    intro cfgMid cfgEnd hsmall hdsmall hex heq hstep
    obtain ⟨mc, ms, mh⟩ := cfgMid
    obtain ⟨ec, es, eh⟩ := cfgEnd
    subst heq
    exact HStep.decompose_of_safe_step hdsmall hex hstep
  have skipCfg : ∀ {cfg next : HConfig}, cfg.1 = .skip → ¬ HStep cfg next := by
    intro cfg _next h
    obtain ⟨cc, ss, hh⟩ := cfg
    dsimp only at h
    subst h
    exact HStep.skip_not_step
  have key : ∀ {cfg : HConfig}, HSteps (c, s, h ∪ hf) cfg →
      ∃ h₂, HSteps (c, s, h) (cfg.1, cfg.2.1, h₂) ∧ Heap.Disjoint h₂ hf ∧
        cfg.2.2 = h₂ ∪ hf ∧ Safe (cfg.1, cfg.2.1, h₂) := by
    intro cfg hstepsCfg
    induction hstepsCfg with
    | refl => exact ⟨h, .refl, hd, rfl, hsafe⟩
    | tail _hprev hlast ih =>
        obtain ⟨hMid, hsmallSteps, hdMid, hmidEq, hsafeMid⟩ := ih
        rcases hsafeMid _ .refl with hskip | hexMid
        · exact absurd hlast (skipCfg hskip)
        · obtain ⟨h₂, hlastSmall, hd₂, heq₂⟩ :=
            decompCfg hdMid hexMid hmidEq hlast
          exact ⟨h₂, hsmallSteps.tail hlastSmall, hd₂, heq₂,
            Safe.of_steps hsafeMid (HSteps.single hlastSmall)⟩
  exact key hsteps

end HSteps

namespace Cmd

/-- **Embedding of IMP into the heap language.** The embedding sends each plain IMP command to
the heap command of the same shape: $\mathtt{skip}$ goes to $\mathtt{skip}$, an assignment of an
arithmetic expression to a variable goes to the same assignment, a sequence goes to the
sequence of the embeddings of its parts, and a conditional or while loop goes to the conditional
or while loop with the same guard and with each subcommand replaced by its embedding. -/
def toHeap : Cmd → HeapCmd
  | .skip => .skip
  | .assign name value => .assign name value
  | .seq first second => .seq first.toHeap second.toHeap
  | .ite guard thenBranch elseBranch =>
      .ite guard thenBranch.toHeap elseBranch.toHeap
  | .while guard body => .while guard body.toHeap

@[simp] theorem toHeap_skip : Cmd.skip.toHeap = .skip := rfl

@[simp] theorem toHeap_assign (name : Nat) (value : AExp) :
    (Cmd.assign name value).toHeap = .assign name value := rfl

@[simp] theorem toHeap_seq (first second : Cmd) :
    (Cmd.seq first second).toHeap = .seq first.toHeap second.toHeap := rfl

@[simp] theorem toHeap_ite (guard : BExp) (thenBranch elseBranch : Cmd) :
    (Cmd.ite guard thenBranch elseBranch).toHeap =
      .ite guard thenBranch.toHeap elseBranch.toHeap := rfl

@[simp] theorem toHeap_while (guard : BExp) (body : Cmd) :
    (Cmd.while guard body).toHeap = .while guard body.toHeap := rfl

theorem toHeap_eq_skip {c : Cmd} : c.toHeap = .skip ↔ c = .skip := by
  cases c <;> simp

end Cmd

namespace HStep

/-- **Heap steps of embedded commands are plain steps.** Let $c$ be a plain IMP command, $s$ a
store and $h$ a heap, and write $\overline{d}$ for the embedding of a plain command $d$ into the
heap language. Then $(\overline{c}, s, h)$ takes a heap step to a heap configuration $K$ if and
only if there are a plain command $c'$ and a store $s'$ such that $(c, s)$ takes a plain small
step to $(c', s')$ and $K = (\overline{c'}, s', h)$. -/
theorem toHeap_iff {c : Cmd} {s : State} {h : Heap} {cfg : HConfig} :
    HStep (c.toHeap, s, h) cfg ↔
      ∃ c' s', Step (c, s) (c', s') ∧ cfg = (c'.toHeap, s', h) := by
  constructor
  · induction c generalizing s cfg with
    | skip =>
        intro hstep
        rw [Cmd.toHeap_skip] at hstep
        exact absurd hstep skip_not_step
    | assign name value =>
        intro hstep
        rw [Cmd.toHeap_assign, assign_iff] at hstep
        refine ⟨.skip, _, Step.assign s name value, ?_⟩
        rw [hstep, Cmd.toHeap_skip]
    | seq first second ihFirst _ihSecond =>
        intro hstep
        rw [Cmd.toHeap_seq, seq_iff] at hstep
        rcases hstep with ⟨hskip, rfl⟩ | ⟨f₁, s₁, h₁, hinner, rfl⟩
        · have hf : first = .skip := Cmd.toHeap_eq_skip.mp hskip
          subst hf
          exact ⟨second, s, Step.seqSkip second s, rfl⟩
        · obtain ⟨fc, sc, hstepF, hcfgEq⟩ := ihFirst hinner
          simp only [Prod.mk.injEq] at hcfgEq
          obtain ⟨hfEq, hsEq, hhEq⟩ := hcfgEq
          refine ⟨.seq fc second, sc, Step.seqStep hstepF, ?_⟩
          rw [Cmd.toHeap_seq, hfEq, hsEq, hhEq]
    | ite _guard t e _ihT _ihE =>
        intro hstep
        rw [Cmd.toHeap_ite, ite_iff] at hstep
        rcases hstep with ⟨hg, rfl⟩ | ⟨hg, rfl⟩
        · exact ⟨t, s, Step.iteTrue hg, rfl⟩
        · exact ⟨e, s, Step.iteFalse hg, rfl⟩
    | «while» guard body _ihBody =>
        intro hstep
        rw [Cmd.toHeap_while, while_iff] at hstep
        refine ⟨.ite guard (.seq body (.while guard body)) .skip, s,
          Step.whileStep guard body s, ?_⟩
        rw [hstep]
        simp only [Cmd.toHeap_ite, Cmd.toHeap_seq, Cmd.toHeap_while,
          Cmd.toHeap_skip]
  · rintro ⟨c', s', hstep, rfl⟩
    have key : ∀ {x y : Config}, Step x y →
        HStep (x.1.toHeap, x.2, h) (y.1.toHeap, y.2, h) := by
      intro x y hxy
      induction hxy with
      | assign state name value => exact .assign state name value h
      | seqSkip second state => exact .seqSkip second.toHeap state h
      | seqStep _hstep ih => exact .seqStep ih
      | iteTrue hg => exact .iteTrue hg
      | iteFalse hg => exact .iteFalse hg
      | whileStep guard body state => exact .whileStep guard body.toHeap state h
    exact key hstep

end HStep

namespace HSteps

/-- **Executions of embedded commands are plain executions.** Let $c$ be a plain IMP command,
$s$ a store and $h$ a heap, and write $\overline{d}$ for the embedding of a plain command $d$
into the heap language. If $(\overline{c}, s, h)$ reaches a heap configuration $(c_2, s_2, h_2)$
in zero or more heap steps, then $h_2 = h$ and there is a plain command $c_2'$ with
$c_2 = \overline{c_2'}$ such that $(c, s)$ reaches $(c_2', s_2)$ in zero or more plain small
steps. -/
theorem of_toHeap {c : Cmd} {s : State} {h : Heap} {c₂ : HeapCmd} {s₂ : State}
    {h₂ : Heap} (hsteps : HSteps (c.toHeap, s, h) (c₂, s₂, h₂)) :
    ∃ c₂', c₂ = c₂'.toHeap ∧ Steps (c, s) (c₂', s₂) ∧ h₂ = h := by
  have key : ∀ {cfg : HConfig}, HSteps (c.toHeap, s, h) cfg →
      ∃ c', cfg = (c'.toHeap, cfg.2.1, h) ∧ Steps (c, s) (c', cfg.2.1) := by
    intro cfg hstepsCfg
    induction hstepsCfg with
    | refl => exact ⟨c, rfl, .refl⟩
    | tail _hprev hstep ih =>
        obtain ⟨cMid, hcfgMid, hstepsMid⟩ := ih
        rw [hcfgMid] at hstep
        rw [HStep.toHeap_iff] at hstep
        obtain ⟨c', s', hstepCmd, rfl⟩ := hstep
        exact ⟨c', rfl, hstepsMid.tail hstepCmd⟩
  obtain ⟨c₂', hEq, hSteps⟩ := key hsteps
  change (c₂, s₂, h₂) = (c₂'.toHeap, s₂, h) at hEq
  simp only [Prod.mk.injEq] at hEq
  obtain ⟨hcc, -, hhh⟩ := hEq
  exact ⟨c₂', hcc, hSteps, hhh⟩

/-- **Plain executions lift to the heap language.** Let $c, c_2$ be plain IMP commands, $s, s_2$
stores and $h$ a heap, and write $\overline{d}$ for the embedding of a plain command $d$ into the
heap language. If $(c, s)$ reaches $(c_2, s_2)$ in zero or more plain small steps, then
$(\overline{c}, s, h)$ reaches $(\overline{c_2}, s_2, h)$ in zero or more heap steps. -/
theorem toHeap_of_steps {c c₂ : Cmd} {s s₂ : State} {h : Heap}
    (hsteps : Steps (c, s) (c₂, s₂)) :
    HSteps (c.toHeap, s, h) (c₂.toHeap, s₂, h) := by
  have key : ∀ {x y : Config}, Steps x y →
      HSteps (x.1.toHeap, x.2, h) (y.1.toHeap, y.2, h) := by
    intro x y hxy
    induction hxy with
    | refl => exact .refl
    | tail _hprev hstep ih =>
        refine ih.tail ?_
        exact HStep.toHeap_iff.mpr ⟨_, _, hstep, rfl⟩
  exact key hsteps

end HSteps

/-- **Embedded plain commands are safe.** For every plain IMP command $c$ with embedding
$\overline{c}$ into the heap language, every store $s$ and every heap $h$, the heap
configuration $(\overline{c}, s, h)$ is safe.

This holds because plain IMP never gets stuck except at $\mathtt{skip}$. -/
theorem safe_toHeap (c : Cmd) (s : State) (h : Heap) : Safe (c.toHeap, s, h) := by
  intro cfg' hsteps
  obtain ⟨c₂, s₂, h₂⟩ := cfg'
  obtain ⟨c₂', rfl, _hSteps, rfl⟩ := HSteps.of_toHeap hsteps
  by_cases hc : c₂' = .skip
  · left
    simp [hc]
  · right
    obtain ⟨⟨c₃, s₃⟩, hstep⟩ := Step.exists_step hc
    exact ⟨_, HStep.toHeap_iff.mpr ⟨c₃, s₃, hstep, rfl⟩⟩

/-- **Embedding preserves termination.** Let $c$ be a plain IMP command with embedding
$\overline{c}$ into the heap language, let $s, s'$ be stores and let $h$ be a heap. Then $c$
terminates from $s$ with final store $s'$ if and only if $(\overline{c}, s, h)$ reaches
$(\mathtt{skip}, s', h)$ in zero or more heap steps. -/
theorem terminates_toHeap {c : Cmd} {s s' : State} {h : Heap} :
    Terminates c s s' ↔ HSteps (c.toHeap, s, h) (.skip, s', h) := by
  constructor
  · intro ht
    have ht' : Steps (c, s) (.skip, s') := ht
    simpa using HSteps.toHeap_of_steps (h := h) ht'
  · intro hs
    obtain ⟨c₂', hEq, hSteps, _⟩ := HSteps.of_toHeap hs
    have hc : c₂' = .skip := Cmd.toHeap_eq_skip.mp hEq.symm
    subst hc
    exact hSteps

namespace HeapCmd

/-- **Modified variables of a heap command.** The set $\mathrm{mod}(c)$ of variables a heap command
$c$ may assign to is defined by recursion on $c$. It is empty for $\mathbf{skip}$, a heap write
$[a] := e$ and a deallocation $\mathbf{free}(a)$; it is $\{x\}$ for an assignment $x := a$, a heap
read $x := [a]$ and an allocation $x := \mathbf{alloc}(e)$; it is $\mathrm{mod}(c_1) \cup
\mathrm{mod}(c_2)$ for a sequence $c_1; c_2$ and for a conditional
$\mathbf{if}\ b\ \mathbf{then}\ c_1\ \mathbf{else}\ c_2$; and it is $\mathrm{mod}(c_0)$ for a loop
$\mathbf{while}\ b\ \mathbf{do}\ c_0$. -/
def modVars : HeapCmd → Finset Nat
  | .skip => ∅
  | .assign name _ => {name}
  | .seq first second => first.modVars ∪ second.modVars
  | .ite _ thenBranch elseBranch => thenBranch.modVars ∪ elseBranch.modVars
  | .while _ body => body.modVars
  | .read name _ => {name}
  | .write _ _ => ∅
  | .alloc name _ => {name}
  | .free _ => ∅

end HeapCmd

namespace HStep

/-- **Steps do not enlarge the modified variables.** Write $\mathrm{mod}(c)$ for the set of
variables a heap command $c$ may assign to. If the configuration $(c, s, h)$ takes a small step to
$(c', s', h')$, then $\mathrm{mod}(c') \subseteq \mathrm{mod}(c)$. -/
theorem modVars_subset {c c' : HeapCmd} {s s' : State} {h h' : Heap}
    (hstep : HStep (c, s, h) (c', s', h')) : c'.modVars ⊆ c.modVars := by
  have key : ∀ {cfg cfg' : HConfig}, HStep cfg cfg' →
      cfg'.1.modVars ⊆ cfg.1.modVars := by
    intro cfg cfg' hstepCfg
    induction hstepCfg with
    | assign _ _ _ _ => simp [HeapCmd.modVars]
    | seqSkip _ _ _ => simp [HeapCmd.modVars]
    | seqStep _hstep ih =>
        intro x hx
        simp only [HeapCmd.modVars, Finset.mem_union] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (ih hx)
        · exact Or.inr hx
    | iteTrue _ => simp [HeapCmd.modVars]
    | iteFalse _ => simp [HeapCmd.modVars]
    | whileStep _ _ _ _ => simp [HeapCmd.modVars]
    | read _ => simp [HeapCmd.modVars]
    | write _ => simp [HeapCmd.modVars]
    | alloc _ => simp [HeapCmd.modVars]
    | free _ => simp [HeapCmd.modVars]
  exact key hstep

/-- **A heap step only changes assignable variables.** If a heap configuration $(c, s, h)$ takes
one heap step to $(c', s', h')$, then $s'(x) = s(x)$ for every variable $x$ outside the set of
variables that $c$ may assign to. -/
theorem store_agree {c c' : HeapCmd} {s s' : State} {h h' : Heap}
    (hstep : HStep (c, s, h) (c', s', h')) :
    ∀ x, x ∉ c.modVars → s' x = s x := by
  have key : ∀ {cfg cfg' : HConfig}, HStep cfg cfg' →
      ∀ x, x ∉ cfg.1.modVars → cfg'.2.1 x = cfg.2.1 x := by
    intro cfg cfg' hstepCfg
    induction hstepCfg with
    | assign _ _ _ _ =>
        intro x hx
        simp only [HeapCmd.modVars, Finset.mem_singleton] at hx
        dsimp only
        rw [Function.update_of_ne hx]
    | seqSkip _ _ _ => intro x _hx; rfl
    | seqStep _hstep ih =>
        intro x hx
        simp only [HeapCmd.modVars, Finset.mem_union, not_or] at hx
        exact ih x hx.1
    | iteTrue _ => intro x _hx; rfl
    | iteFalse _ => intro x _hx; rfl
    | whileStep _ _ _ _ => intro x _hx; rfl
    | read _ =>
        intro x hx
        simp only [HeapCmd.modVars, Finset.mem_singleton] at hx
        dsimp only
        rw [Function.update_of_ne hx]
    | write _ => intro x _hx; rfl
    | alloc _ =>
        intro x hx
        simp only [HeapCmd.modVars, Finset.mem_singleton] at hx
        dsimp only
        rw [Function.update_of_ne hx]
    | free _ => intro x _hx; rfl
  exact key hstep

end HStep

namespace HSteps

/-- **Heap executions only change assignable variables.** If a heap configuration $(c, s, h)$
reaches a heap configuration $(c', s', h')$ in zero or more heap steps, then $s'(x) = s(x)$ for
every variable $x$ outside the set of variables that $c$ may assign to. -/
theorem store_agree {c c' : HeapCmd} {s s' : State} {h h' : Heap}
    (hsteps : HSteps (c, s, h) (c', s', h')) :
    ∀ x, x ∉ c.modVars → s' x = s x := by
  have stepSubsetCfg : ∀ {cfg cfg' : HConfig}, HStep cfg cfg' →
      cfg'.1.modVars ⊆ cfg.1.modVars := by
    intro cfg cfg' hstep
    obtain ⟨c₁, s₁, h₁⟩ := cfg
    obtain ⟨c₂, s₂, h₂⟩ := cfg'
    exact HStep.modVars_subset hstep
  have stepAgreeCfg : ∀ {cfg cfg' : HConfig}, HStep cfg cfg' →
      ∀ x, x ∉ cfg.1.modVars → cfg'.2.1 x = cfg.2.1 x := by
    intro cfg cfg' hstep
    obtain ⟨c₁, s₁, h₁⟩ := cfg
    obtain ⟨c₂, s₂, h₂⟩ := cfg'
    exact HStep.store_agree hstep
  have stepsSubsetCfg : ∀ {cfg cfg' : HConfig}, HSteps cfg cfg' →
      cfg'.1.modVars ⊆ cfg.1.modVars := by
    intro cfg cfg' hstepsCfg
    induction hstepsCfg with
    | refl => exact Finset.Subset.rfl
    | tail _hprev hstep ih => exact (stepSubsetCfg hstep).trans ih
  intro x hx
  have key : ∀ {cfg : HConfig}, HSteps (c, s, h) cfg → cfg.2.1 x = s x := by
    intro cfg hstepsCfg
    induction hstepsCfg with
    | refl => rfl
    | tail hprev hstep ih =>
        have hxMid : x ∉ _ := fun hmem => hx (stepsSubsetCfg hprev hmem)
        rw [stepAgreeCfg hstep x hxMid, ih]
  exact key hsteps

end HSteps

end Cslib.IMP
