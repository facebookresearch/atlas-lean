/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Relation.Defs
public import Mathlib.Basic.Finite.Defs

/-!
# Finite RC11 executions

An RC11 execution starts with a labelled trace: events, initial writes, sequenced-before and
read-modify-write pairs. A memory witness then supplies reads-from and modification order.
`Execution.Consistent` requires read completeness, coherence, atomicity, acyclicity of the
partial SC relation and no-thin-air. The graph determines synchronisation and the partial SC
relation; a candidate graph may have a cycle in that relation.

`Fin n` numbers the events of a single trace, up to renaming. Locations and values are finite
types; `zero` is the distinguished initial value. `ProgramTraces` describes the interface to a
partitioned program's trace semantics, not a language of instructions. Which labelled traces
its sequential threads generate (and which represent the whole program) is language-specific.
The trace predicates cannot inspect the memory witness. In particular, a full trace can have an
incomplete execution. Program outcomes and compilation are outside this model.

## Reference

* O. Lahav, V. Vafeiadis, J. Kang, C.-K. Hur and D. Dreyer,
  [Repairing Sequential Consistency in C/C++11](https://plv.mpi-sws.org/scfix/paper.pdf),
  PLDI 2017, §§3.1–3.2, Definition 1. The convention for different-location edges is from §2;
  the two-sided condition for an immediate edge is from the notation at the start of §3.
-/

@[expose] public section

namespace Cslib.Semantics.WeakMemory.RC11

open Relation

/-- RC11 modes, from non-atomic to sequentially consistent. Acquire and release are incomparable. -/
inductive Mode where
  | na | rlx | acq | rel | acqrel | sc
  deriving DecidableEq

/-- The upper cone of a mode in the RC11 mode order: `atLeast lower actual`. -/
def Mode.atLeast : Mode → Mode → Bool
  | .na, _ => true
  | .rlx, m => m != .na
  | .acq, m => m == .acq || m == .acqrel || m == .sc
  | .rel, m => m == .rel || m == .acqrel || m == .sc
  | .acqrel, m => m == .acqrel || m == .sc
  | .sc, m => m == .sc

/-- The five allowed read/write mode pairs of an RMW. Its two halves are distinct events. -/
def Mode.rmwPair : Mode → Mode → Bool
  | .rlx, .rlx | .rlx, .rel | .acq, .rlx | .acq, .rel | .sc, .sc => true
  | _, _ => false

/-- Reads and writes carry a mode, location and value. A fence carries only a mode. -/
inductive Label (L V : Type*) where
  | read (mode : Mode) (loc : L) (value : V)
  | write (mode : Mode) (loc : L) (value : V)
  | fence (mode : Mode)
  deriving DecidableEq

variable {L V : Type*}

/-- Mode legality depends on the kind of event; in particular there is no relaxed fence. -/
def Label.legal : Label L V → Bool
  | .read m .. => m == .na || m == .rlx || m == .acq || m == .sc
  | .write m .. => m == .na || m == .rlx || m == .rel || m == .sc
  | .fence m => m == .acq || m == .rel || m == .acqrel || m == .sc

/-- The mode on the label, including on a fence. -/
def Label.mode : Label L V → Mode
  | .read m .. | .write m .. | .fence m => m

/-- The location and value of a memory access; absent for a fence. -/
def Label.access : Label L V → Option (L × V)
  | .read _ x v | .write _ x v => some (x, v)
  | .fence _ => none

/-- True for a read, including the read half of an RMW. -/
def Label.isRead : Label L V → Bool
  | .read .. => true
  | _ => false

/-- True for a write, including initial writes and the write half of an RMW. -/
def Label.isWrite : Label L V → Bool
  | .write .. => true
  | _ => false

/-- True for a fence of any mode. -/
def Label.isFence : Label L V → Bool
  | .fence _ => true
  | _ => false

/-- Two labels access the same location. Two fences do not, even though neither has an address. -/
def Label.SameLoc (a b : Label L V) : Prop :=
  ∃ x, a.access.map Prod.fst = some x ∧ b.access.map Prod.fst = some x

/-- An immediate edge of a strict partial order as in §3: other predecessors of `b` precede
`a`, and other successors of `a` follow `b`. Just excluding intermediate events is weaker. -/
def Immediate {E : Type*} (s : E → E → Prop) (a b : E) : Prop :=
  s a b ∧ (∀ c, s c b → c = a ∨ s c a) ∧ (∀ c, s a c → b = c ∨ s b c)

/-- A finite labelled trace before a choice of reads-from and modification order. The image of
`init` is the distinguished set of initial events; other writes of zero need not be initial. -/
structure Trace (L V : Type*) [Finite L] [Finite V] (zero : V) (n : Nat) where
  /-- The label of each event. -/
  lab : Fin n → Label L V
  /-- Only modes permitted for the corresponding event kind occur. -/
  legal : ∀ e, (lab e).legal
  /-- One distinguished event for each location. -/
  init : L → Fin n
  /-- Each initial event writes zero non-atomically to its own location. -/
  init_lab : ∀ x, lab (init x) = .write .na x zero
  /-- Sequenced-before, a strict partial order. -/
  sb : Fin n → Fin n → Prop
  /-- No event precedes itself. -/
  sb_irrefl : ∀ a, ¬ sb a a
  /-- Sequenced-before includes indirect sequencing. -/
  sb_trans : ∀ a b c, sb a b → sb b c → sb a c
  /-- Initialisation precedes every non-initial event. -/
  init_sb : ∀ x b, (∀ y, init y ≠ b) → sb (init x) b
  /-- The two halves of a read-modify-write, in read-to-write order. -/
  rmw : Fin n → Fin n → Prop
  /-- Each RMW is an immediate, same-location edge with a legal read/write mode pair. -/
  rmw_spec : ∀ a b, rmw a b → Immediate sb a b ∧ (lab a).isRead ∧ (lab b).isWrite ∧
    (lab a).SameLoc (lab b) ∧ (lab a).mode.rmwPair (lab b).mode

variable [Finite L] [Finite V] {zero : V} {n m : Nat}

/-- A trace prefix keeps all initial events and a downward-closed set of further events.
The injection permits renumbering; labels, RMW pairs and sequencing are induced on its image. -/
def Trace.IsPrefix (t : Trace L V zero m) (u : Trace L V zero n) : Prop :=
  ∃ f : Fin m → Fin n, Function.Injective f ∧ (∀ x, f (t.init x) = u.init x) ∧
    (∀ a, t.lab a = u.lab (f a)) ∧ (∀ a b, t.sb a b ↔ u.sb (f a) (f b)) ∧
    (∀ a b, t.rmw a b ↔ u.rmw (f a) (f b)) ∧ (∀ a b, u.sb b (f a) → ∃ c, f c = b)

/-- A trace is an initialisation-containing prefix of itself. -/
protected theorem Trace.IsPrefix.refl (t : Trace L V zero n) : t.IsPrefix t :=
  ⟨id, Function.injective_id, fun _ => rfl, fun _ => rfl, fun _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ b _ => ⟨b, rfl⟩⟩

/-- Restricting first to a prefix and then to a prefix of that prefix is still a trace prefix. -/
theorem Trace.IsPrefix.trans {k : Nat} {t : Trace L V zero k} {u : Trace L V zero m}
    {v : Trace L V zero n} (h : t.IsPrefix u) (i : u.IsPrefix v) : t.IsPrefix v := by
  obtain ⟨f, hf, fi, fl, fs, fr, fd⟩ := h
  obtain ⟨g, hg, gi, gl, gs, gr, gd⟩ := i
  refine ⟨g ∘ f, hg.comp hf, fun x => (congrArg g (fi x)).trans (gi x),
    fun a => (fl a).trans (gl (f a)), fun a b => (fs a b).trans (gs (f a) (f b)),
    fun a b => (fr a b).trans (gr (f a) (f b)), ?_⟩
  intro a b edge
  obtain ⟨c, rfl⟩ := gd (f a) b edge
  obtain ⟨d, rfl⟩ := fd a c ((gs _ _).mpr edge)
  exact ⟨d, rfl⟩

/-- The trace semantics supplied by a program of finitely many sequential threads. `generated`
is closed under initialisation-containing sequenced-before prefixes. `full` identifies traces of
the whole program, not the graphs in which every read has a source. -/
structure ProgramTraces (L V : Type*) [Finite L] [Finite V] (zero : V) where
  /-- Labelled traces admitted by the threads, before memory consistency is tested. -/
  generated : {k : Nat} → Trace L V zero k → Prop
  /-- Traces generated by the whole program. -/
  full : {k : Nat} → Trace L V zero k → Prop
  /-- A full trace is generated. -/
  full_generated : ∀ {k} (t : Trace L V zero k), full t → generated t
  /-- Restricting a generated trace to an sb-prefix gives another generated trace. -/
  prefix_closed : ∀ {i j} (t : Trace L V zero i) (u : Trace L V zero j),
    t.IsPrefix u → generated u → generated t

/-- A finite execution graph. Reads-from is partial but single-valued **at the read**.
Modification order is a disjoint union of strict total orders, one on each location's writes. -/
structure Execution (L V : Type*) [Finite L] [Finite V] (zero : V) (n : Nat)
    extends Trace L V zero n where
  /-- Reads-from is directed from the source write to the consuming read. -/
  rf : Fin n → Fin n → Prop
  /-- A reads-from edge preserves both address and value. -/
  rf_spec : ∀ w r, rf w r → (lab w).isWrite ∧ (lab r).isRead ∧ (lab w).access = (lab r).access
  /-- A read cannot take its value from two different writes. -/
  rf_unique : ∀ a b r, rf a r → rf b r → a = b
  /-- Modification order, directed from earlier to later writes at one location. -/
  mo : Fin n → Fin n → Prop
  /-- Only writes to the same location are ordered. -/
  mo_spec : ∀ a b, mo a b → (lab a).isWrite ∧ (lab b).isWrite ∧ (lab a).SameLoc (lab b)
  /-- Modification order is strict. -/
  mo_irrefl : ∀ a, ¬ mo a a
  /-- Modification order is transitive. -/
  mo_trans : ∀ a b c, mo a b → mo b c → mo a c
  /-- Distinct writes to the same location are comparable. -/
  mo_total : ∀ a b, (lab a).isWrite → (lab b).isWrite → (lab a).SameLoc (lab b) →
    a ≠ b → mo a b ∨ mo b a

namespace Execution

variable (G : Execution L V zero n)

/-- The identity relation restricted to events satisfying a predicate (the paper's `[S]`). -/
def guardRel (p : Fin n → Prop) (a b : Fin n) : Prop := a = b ∧ p a

local infixr:75 " ;; " => Relation.Comp

/-- Reads-before points from a read to each write later than its source in modification order. -/
def rb : Fin n → Fin n → Prop := Function.swap G.rf ;; G.mo

/-- Extended coherence order is nonempty reachability along reads-from, modification order and
reads-before. -/
def eco := TransGen (G.rf ⊔ G.mo ⊔ G.rb)

/-- A release sequence starts at a write. Stay there or take a sequenced-before edge to the same
location. In either case the write reached at this point must be at least relaxed. From that
write, follow zero or more pairs of a reads-from edge and an RMW edge. -/
def rs := guardRel (fun e => (G.lab e).isWrite) ;;
  ReflGen (fun a b => G.sb a b ∧ (G.lab a).SameLoc (G.lab b)) ;;
  guardRel (fun e => (G.lab e).isWrite ∧ Mode.rlx.atLeast (G.lab e).mode) ;;
  ReflTransGen (G.rf ;; G.rmw)

/-- Synchronises-with starts at a release-or-stronger event and ends at an acquire-or-stronger
event. The source is the starting write of a release sequence, or a fence sequenced before that
write. The sequence ends at a write from which an at-least-relaxed read takes its value. The
target is that read or a fence sequenced after it. The endpoint mode bounds apply in both cases. -/
def sw := guardRel (fun e => Mode.rel.atLeast (G.lab e).mode) ;;
  ReflGen (guardRel (fun e => (G.lab e).isFence) ;; G.sb) ;; G.rs ;; G.rf ;;
  guardRel (fun e => (G.lab e).isRead ∧ Mode.rlx.atLeast (G.lab e).mode) ;;
  ReflGen (G.sb ;; guardRel (fun e => (G.lab e).isFence)) ;;
  guardRel (fun e => Mode.acq.atLeast (G.lab e).mode)

/-- Happens-before is nonempty reachability by sequencing and synchronisation. -/
def hb := TransGen (G.sb ⊔ G.sw)

/-- Sequenced-before minus its same-location restriction: in particular this can include
fence-to-fence edges, since fences do not access a common location. -/
def sbDiffLoc (a b : Fin n) : Prop := G.sb a b ∧ ¬(G.lab a).SameLoc (G.lab b)

/-- SC-before combines sequencing, the different-location bridge through happens-before,
same-location happens-before, modification order and reads-before. -/
def scb : Fin n → Fin n → Prop := G.sb ⊔ (G.sbDiffLoc ;; G.hb ;; G.sbDiffLoc) ⊔
  (fun a b => G.hb a b ∧ (G.lab a).SameLoc (G.lab b)) ⊔ G.mo ⊔ G.rb

/-- Identity restricted to SC events, including both accesses and fences. -/
def scEvents := guardRel (fun e => (G.lab e).mode = .sc)

/-- Identity restricted to SC fences; SC accesses do not pass this guard. -/
def scFences := guardRel (fun e => (G.lab e).isFence ∧ (G.lab e).mode = .sc)

/-- A base partial SC edge from `a` to `b` requires both endpoints to be SC and an SC-before
(`scb`) edge from `x` to `y`. Here `x` is `a` itself or, if `a` is a fence, an event that
happens after `a`. Likewise `y` is `b` itself or, if `b` is a fence, an event that happens
before `b`. -/
def pscBase := (G.scEvents ⊔ (G.scFences ;; ReflGen G.hb)) ;; G.scb ;;
  (G.scEvents ⊔ (ReflGen G.hb ;; G.scFences))

/-- Fence part of the partial SC relation: the middle is either happens-before alone or
happens-before, extended coherence order, then happens-before. Both endpoints are SC fences. -/
def pscF := G.scFences ;; (G.hb ⊔ (G.hb ;; G.eco ;; G.hb)) ;; G.scFences

/-- The partial SC relation, with both its base and fence contributions. -/
def psc := G.pscBase ⊔ G.pscF

/-- Every read has an incoming reads-from edge. Completeness does not assert fullness. -/
def Complete : Prop := ∀ r, (G.lab r).isRead → ∃ w, G.rf w r

/-- RC11 consistency (Lahav et al., §3.2, Definition 1). Every read must have a reads-from
source. Coherence forbids a happens-before edge returning by zero or one extended coherence
edge. Atomicity forbids an RMW read/write pair joined by reads-before then modification order.
Finally both the partial SC relation and the union of sequencing with reads-from must be acyclic.
These conditions do not require the trace to be full. -/
structure Consistent : Prop where
  /-- Every read obtains a value from a write. -/
  complete : G.Complete
  /-- No happens-before edge returns via zero or one extended coherence edge. -/
  coherence : Std.Irrefl (G.hb ;; ReflGen G.eco)
  /-- No RMW skips an intervening write in modification order. -/
  atomicity : ∀ a b, G.rmw a b → ¬(G.rb ;; G.mo) a b
  /-- The union of the base and fence partial SC relations has no cycle. -/
  sc : Acyclic G.psc
  /-- Sequenced-before and reads-from together have no cycle. -/
  noThinAir : Acyclic (G.sb ⊔ G.rf)

/-- Only a release (or stronger) event can be the source of a synchronisation edge. -/
theorem sw_source {a b : Fin n} (h : G.sw a b) : Mode.rel.atLeast (G.lab a).mode := by
  obtain ⟨_, ha, _⟩ := h
  exact ha.2

/-- Both contributions to the partial SC relation start at SC events, including SC fences. -/
theorem psc_source {a b : Fin n} (h : G.psc a b) : (G.lab a).mode = .sc := by
  rcases h with base | fence
  · obtain ⟨_, ha, _⟩ := base
    rcases ha with ha | ⟨_, ha, _⟩
    · exact ha.2
    · exact ha.2.2
  · obtain ⟨_, ha, _⟩ := fence
    exact ha.2.2

/-- In a complete execution every read has exactly one source, not just at least one. -/
theorem Complete.uniqueSource {G : Execution L V zero n} (h : G.Complete) {r : Fin n}
    (hr : (G.lab r).isRead) : ∃! w, G.rf w r := by
  obtain ⟨w, hw⟩ := h r hr
  exact ⟨w, hw, fun v hv => G.rf_unique v w r hv hw⟩

/-- Coherence forbids happens-before cycles even without a return edge in extended coherence. -/
theorem Consistent.hb_irrefl {G : Execution L V zero n} (h : G.Consistent) (e : Fin n) :
    ¬G.hb e e := fun he => h.coherence.irrefl e ⟨e, he, .refl⟩

end Execution
end Cslib.Semantics.WeakMemory.RC11
