/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Scheduling.RealTime.PeriodicTasks
public import CSLibExt.Scheduling.RealTime.SemaphoreProgram
public import Mathlib.Logic.Relation

/-!
# Finite semaphore jobs and sufficient blocking certificates

In the resource-access model of Sha, Rajkumar and Lehoczky (1990), §II, jobs advance by single
atomic instructions. Eligible jobs are dispatched by current rank and then by arrival order, not
by job index. A protocol specifies extra resource guards and a holdings-dependent dispatch rank.

This model certifies **some**, not necessarily all, forced exits. Positive guard, nesting and
chain derivations include cycles. For distinct jobs, a second certificate uses a relaxation of
service: progress is possible, but no relaxed path can serve the victim without passing the
owner's V. The relaxation ignores release gates and keeps only precedence due to a promoted
lower job. Every admitted prefix gives a relaxed path; the converse fails. A relaxed escape may
therefore defeat a certificate even when a late arrival cannot run or a demotion forces an exit.

`certifiedBlockers` is not asserted to equal the paper's β. Nonmembership does not exclude
blocking, and its inclusion-maximal elements need not be maximal among *all* actual blockers.
No worst-case upper bound or inheritance or ceiling protocol theorem follows from these sets.

Source: L. Sha, R. Rajkumar and J. P. Lehoczky, “Priority Inheritance Protocols: An Approach to
Real-Time Synchronization”, IEEE Transactions on Computers 39(9), 1990, §II, pp. 1176–1177.
-/

@[expose] public section

namespace Cslib.Scheduling.RealTime.Semaphore

variable {R T : Type*} {n : ℕ}

/-- Finite jobs numbered in nondecreasing order of base rank (smaller is more urgent).
The fixed rank belongs to the task; different jobs, even of different tasks, may tie. -/
structure Workload (T R : Type*) (n : ℕ) where
  /-- Task instantiated by each job. -/
  task : Fin n → T
  /-- Fixed base rank of each task. -/
  priority : T → ℕ
  /-- Finite program of each job. -/
  code : Fin n → Program R
  /-- Numbering lists priorities in order, without imposing a strict order on ties. -/
  numbered : Monotone (priority ∘ task)

/-- The initial rank of a job is its task's fixed priority. -/
abbrev Workload.base (w : Workload T R n) (i : Fin n) := w.priority (w.task i)

/-- A resource protocol specifies extra admission guards and current dispatch priority. A guard
lists semaphore names that must not be held by *another* job at this instruction. Dispatch rank
is a function of base priority and currently held semaphores, initially equal to base priority. -/
structure Protocol (R : Type*) where
  /-- Additional foreign locks incompatible with this instruction at this base priority. -/
  guard : ℕ → Instruction R → List R
  /-- Dispatch rank of a job at its current holdings. -/
  rank : ℕ → List R → ℕ
  /-- Without a critical section the job has its base priority. -/
  rank_nil : ∀ p, rank p [] = p

/-- Ordinary binary semaphore admission without extra guards or priority changes. -/
def Protocol.ordinary : Protocol R := ⟨fun _ _ => [], fun p _ => p, fun _ => rfl⟩

/-- For a P instruction, the requested lock itself is always required to be free; other guards
are imposed by the protocol. -/
def Protocol.required (π : Protocol R) (p : ℕ) (a : Instruction R) : List R :=
  match a with
  | .acquire s => s :: π.guard p a
  | _ => π.guard p a

/-- Release times and a FIFO ticket for simultaneous arrivals. Tickets resolve only simultaneous
arrivals and are independent of job numbering. -/
structure Arrivals (n : ℕ) where
  /-- Slot at which the job arrives. -/
  time : Fin n → ℕ
  /-- Order of arrival within one slot. -/
  ticket : Fin n → ℕ
  /-- Two distinct jobs never share an arrival slot and ticket. -/
  unique : ∀ i j, time i = time j → ticket i = ticket j → i = j

variable (w : Workload T R n) (π : Protocol R)

/-- One job executes one instruction; no other job's program counter moves. -/
def advance (x : Fin n → ℕ) (i : Fin n) : Fin n → ℕ := Function.update x i (x i + 1)

/-- Local service at a slot boundary, counted from the single-processor schedule. Idle slots
and service of another job do not advance this job's program counter. -/
def service (s : Schedule (Fin n)) : ℕ → Fin n → ℕ
  | 0 => fun _ => 0
  | t + 1 => match s t with
    | some i => advance (service s t) i
    | none => service s t

/-- A schedule assigning every slot to one job increments its service counter in every slot.
For a finite program, only the prefix up to its completion can be admissible. -/
theorem service_solo (i : Fin n) (t : ℕ) : service (fun _ => some i) t i = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [service, advance, ih]

/-- Resource admission at counters `x`: the instruction exists, and none of the physical or
protocol-required locks is held by another job. No job can suspend itself. -/
abbrev Enabled (x : Fin n → ℕ) (i : Fin n) : Prop :=
  x i < (w.code i).length ∧ ∀ j, i ≠ j → ∀ k : Fin (w.code j).count,
    ((w.code j).sec k).Held (x j) →
    ((w.code j).sec k).lock ∉ π.required (w.base i) ((w.code i).instruction (x i))

/-- The current dispatch priority, computed from the task priority and actual holdings. -/
def current (x : Fin n → ℕ) (i : Fin n) : ℕ :=
  π.rank (w.base i) (((List.ofFn (w.code i).sec).filter (fun z => decide (z.Held (x i)))).map
    Section.lock)

/-- Every job initially has its own task's base priority. -/
theorem current_initial (i : Fin n) : current w π (fun _ => 0) i = w.base i := by
  simp [current, Section.Held, π.rank_nil]

/-- Selection among released, resource-enabled jobs uses current priority then FCFS arrival
(slot, ticket). No term compares job indices. -/
abbrev First (a : Arrivals n) (t : ℕ) (x : Fin n → ℕ) (i : Fin n) : Prop :=
  a.time i ≤ t ∧ Enabled w π x i ∧ ∀ j, a.time j ≤ t → Enabled w π x j →
    current w π x i < current w π x j ∨
      (current w π x i = current w π x j ∧ (a.time i < a.time j ∨
        (a.time i = a.time j ∧ a.ticket i ≤ a.ticket j)))

/-- A prefix admits exactly one first eligible job per nonidle slot, and can idle only if none
is eligible. Validity is checked from zero counters, never from an arbitrary lock snapshot. -/
abbrev Admissible (a : Arrivals n) (s : Schedule (Fin n)) (t : ℕ) : Prop :=
  ∀ u : Fin t, match s u with
    | some i => First w π a u (service s u) i
    | none => ∀ i, a.time i ≤ u → ¬ Enabled w π (service s u) i

/-- Whether the next instruction is resource-enabled is decidable on finite jobs and pairs. -/
instance decEnabled [DecidableEq R]
    (x : Fin n → ℕ) (i : Fin n) : Decidable (Enabled w π x i) := by
  unfold Enabled; infer_instance

/-- The priority and FIFO selection predicate is decidable on a finite job family. -/
instance decFirst [DecidableEq R]
    (a : Arrivals n) (t : ℕ) (x : Fin n → ℕ) (i : Fin n) : Decidable (First w π a t x i) := by
  unfold First; infer_instance

/-- Finite prefix admissibility is decidable when lock names have decidable equality. -/
instance decAdmissible [DecidableEq R]
    (a : Arrivals n) (s : Schedule (Fin n)) (t : ℕ) : Decidable (Admissible w π a s t) := by
  unfold Admissible
  refine @Fintype.decidableForallFintype _ _ (fun u => ?_) _
  split <;> infer_instance

/-- Under the same releases, tickets, programs and protocol, admitted prefixes agree on every
slot they both cover. This is uniqueness of dispatch, not causation of a resource wait. -/
theorem admissible_agree {a s r t} (hs : Admissible w π a s t) (hr : Admissible w π a r t)
    {k : ℕ} (hk : k < t) : s k = r k := by
  have go : ∀ d ≤ t, service s d = service r d ∧ ∀ u < d, s u = r u := by
    intro d
    induction d with
    | zero => exact fun _ => ⟨rfl, fun u hu => (Nat.not_lt_zero u hu).elim⟩
    | succ d ih =>
      intro hd
      obtain ⟨eq, prior⟩ := ih (Nat.le_of_succ_le hd)
      have left := hs ⟨d, hd⟩
      have right := hr ⟨d, hd⟩
      simp only [eq] at left right
      have same : s d = r d := by
        cases e : s d <;> cases f : r d <;> simp only [e, f] at left right ⊢
        · exact (left _ right.1 right.2.1).elim
        · exact (right _ left.1 left.2.1).elim
        · rename_i i j
          have h₁ := left.2.2 j right.1 right.2.1
          have h₂ := right.2.2 i left.1 left.2.1
          exact congrArg some (a.unique i j (by omega) (by omega))
      refine ⟨by simp only [service, same, eq], fun u hu => ?_⟩
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hu) with rfl | h
      · exact same
      · exact prior u h
  exact (go t le_rfl).2 _ hk

/-- When the only job arrives at slot zero, assigning it every slot up to its program length
is admissible under any of the resource protocols. -/
theorem solo_admissible (v : Workload T R 1) (a : Arrivals 1) (ha : a.time 0 = 0) :
    Admissible v π a (fun _ => some 0) (v.code 0).length := by
  intro u
  refine ⟨by simp [ha], ⟨by simp [service_solo], ?_⟩, ?_⟩
  · intro j h; exact (h (Subsingleton.elim _ _)).elim
  · intro j; obtain rfl : j = 0 := Subsingleton.elim _ _
    simp

variable {w π}

/-- A positive certificate of a resource wait: the victim needs a live lock of another job,
a needed outer occurrence contains a live inner one, or two certified waits form a chain.
Chains may return to the starting job in a cycle. These rules need no progress witness and
are sufficient, not exhaustive, evidence of exit dependencies. -/
inductive GuardExitCertificate (w : Workload T R n) (π : Protocol R) (x : Fin n → ℕ) :
    (i j : Fin n) → Fin (w.code j).count → Prop where
  | guard {i j k} (diff : i ≠ j) (pending : x i < (w.code i).length)
      (held : ((w.code j).sec k).Held (x j))
      (needed : ((w.code j).sec k).lock ∈ π.required (w.base i) ((w.code i).instruction (x i))) :
      GuardExitCertificate w π x i j k
  | inner {i j k l} (outer : GuardExitCertificate w π x i j k)
      (nested : ((w.code j).sec l).Inside ((w.code j).sec k))
      (held : ((w.code j).sec l).Held (x j)) : GuardExitCertificate w π x i j l
  | chain {i j k m l} (first : GuardExitCertificate w π x i j k)
      (next : GuardExitCertificate w π x j m l) :
      GuardExitCertificate w π x i m l

/-- Every derived exit obligation names a section actually held in this snapshot. -/
theorem GuardExitCertificate.held {x i j k} (h : GuardExitCertificate w π x i j k) :
    ((w.code j).sec k).Held (x j) := by
  induction h with
  | guard _ _ h _ | inner _ _ h _ => exact h
  | chain _ _ _ ih => exact ih

/-- A resource-only move completes one enabled instruction, without imposing the scheduler's
priority order. Necessity against these interleavings is stronger than necessity along one run. -/
def Move (w : Workload T R n) (π : Protocol R) (x y : Fin n → ℕ) : Prop :=
  ∃ i, Enabled w π x i ∧ y = advance x i

private theorem mono_move {x y} (h : Move w π x y) (j : Fin n) : x j ≤ y j := by
  obtain ⟨i, _, rfl⟩ := h
  by_cases he : j = i <;> simp [advance, he, Function.update_of_ne]

private theorem mono_path {x y} (h : Relation.ReflTransGen (Move w π) x y) (j : Fin n) :
    x j ≤ y j := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (mono_move hs _)

/-- For a positive guard certificate, in the **poststate** of every resource-legal path
on which the victim advanced, the owner has passed its V. This statement also admits cyclic
certificates; it does not assume a path making progress exists. -/
theorem GuardExitCertificate.passed_of_progress {x i j k} (h : GuardExitCertificate w π x i j k) {y}
    (path : Relation.ReflTransGen (Move w π) x y) (progress : x i < y i) :
    ((w.code j).sec k).leave < y j := by
  induction h generalizing y with
  | @guard i j k diff pending held needed =>
    induction path with
    | refl => omega
    | @tail b c p step ih =>
      by_cases hb : x i < b i
      · exact (ih hb).trans_le (mono_move step j)
      · have same : b i = x i := le_antisymm (Nat.le_of_not_gt hb) (mono_path p i)
        obtain ⟨q, en, rfl⟩ := step
        by_cases hq : i = q
        · subst q
          by_contra! hn
          rw [advance, Function.update_of_ne diff.symm] at hn
          have live := And.intro (held.1.trans_le (mono_path p j)) hn
          exact en.2 j diff k live (same ▸ needed)
        · simp [advance, Function.update_of_ne hq, same] at progress
  | inner _ nested _ ih => exact nested.2.trans (ih path progress)
  | chain first _ ih₁ ih₂ => exact ih₂ path (first.held.2.trans_lt (ih₁ path progress))

/-- An admitted schedule prefix is a path of resource-legal moves from each earlier boundary;
an idle slot contributes no move. -/
theorem admissible_path {a s t} (h : Admissible w π a s t) {u} (hu : u ≤ t) :
    Relation.ReflTransGen (Move w π) (service s u) (service s t) := by
  induction t with
  | zero => obtain rfl := Nat.eq_zero_of_le_zero hu; exact .refl
  | succ t ih =>
    rcases Nat.eq_or_lt_of_le hu with rfl | hlt
    · exact .refl
    · have prev := ih (fun v => h ⟨v, v.isLt.trans t.lt_succ_self⟩) (Nat.le_of_lt_succ hlt)
      have last := h ⟨t, t.lt_succ_self⟩
      cases hs : s t with
      | none => simpa [service, hs] using prev
      | some i =>
        simp only [hs] at last
        exact prev.tail ⟨i, last.2.1, by simp [service, hs]⟩

/-- Two distinct jobs never hold the same semaphore simultaneously at an admitted boundary. -/
theorem exclusive {a s t} (h : Admissible w π a s t) {i j : Fin n} (diff : i ≠ j)
    (k : Fin (w.code i).count) (l : Fin (w.code j).count)
    (hi : ((w.code i).sec k).Held (service s t i)) (hj : ((w.code j).sec l).Held (service s t j)) :
    ((w.code i).sec k).lock ≠ ((w.code j).sec l).lock := by
  have path := admissible_path h (Nat.zero_le t)
  change Relation.ReflTransGen (Move w π) (fun _ => 0) (service s t) at path
  generalize service s t = y at hi hj path
  induction path with
  | refl => exact (Nat.not_lt_zero _ hi.1).elim
  | @tail b c _ step ih =>
    obtain ⟨q, en, rfl⟩ := step
    by_cases hqi : i = q
    · subst q
      simp only [advance, Function.update_self] at hi
      rw [advance, Function.update_of_ne diff.symm] at hj
      by_cases he : b i = ((w.code i).sec k).enter
      · intro eq
        apply en.2 j diff l hj
        simp [he, (w.code i).matching k |>.1, Protocol.required, eq]
      · exact ih ⟨by have := hi.1; omega, by have := hi.2; omega⟩ hj
    · rw [advance, Function.update_of_ne hqi] at hi
      by_cases hqj : j = q
      · subst q
        simp only [advance, Function.update_self] at hj
        by_cases he : b j = ((w.code j).sec l).enter
        · intro eq
          apply en.2 i diff.symm k hi
          simp [he, (w.code j).matching l |>.1, Protocol.required, eq]
        · exact ih hi ⟨by have := hj.1; omega, by have := hj.2; omega⟩
      · rw [advance, Function.update_of_ne hqj] at hj
        exact ih hi hj

/-- A relaxed service step enforces resource admission and priority precedence due to a promoted,
resource-enabled lower-base-priority job. It *drops* ordinary CPU competition and release gates.
A job with a promoted rank must already hold a lock, so has already arrived in a reachable state.
Necessity under this relaxation is a sufficient test, not an exact test for the scheduler. -/
def ProtectedMove (w : Workload T R n) (π : Protocol R) (a : Arrivals n) (x y : Fin n → ℕ) : Prop :=
  ∃ i, Enabled w π x i ∧ y = advance x i ∧ ∀ j, Enabled w π x j → w.base i < w.base j →
    current w π x j < w.base j → (current w π x i < current w π x j ∨
      (current w π x i = current w π x j ∧ (a.time i < a.time j ∨
        (a.time i = a.time j ∧ a.ticket i ≤ a.ticket j))))

private theorem arrived_of_service {a s t} (h : Admissible w π a s t) {j}
    (pos : 0 < service s t j) : a.time j ≤ t := by
  induction t with
  | zero => exact (Nat.not_lt_zero _ pos).elim
  | succ t ih =>
    have prev : Admissible w π a s t := fun v => h ⟨v, v.isLt.trans t.lt_succ_self⟩
    have last := h ⟨t, t.lt_succ_self⟩
    cases hs : s t with
    | none => exact (ih prev (by simpa [service, hs] using pos)).trans t.le_succ
    | some i =>
      simp only [hs] at last
      by_cases eq : j = i
      · subst j; exact last.1.trans t.le_succ
      · apply (ih prev _).trans t.le_succ
        simpa [service, hs, advance, Function.update_of_ne eq] using pos

/-- A real execution is also a priority-relaxed continuation between any two of its boundaries.
In particular every exit shown necessary under relaxed service is necessary in the scheduler. -/
theorem protectedPath_of_admissible {a s t} (h : Admissible w π a s t) {u} (hu : u ≤ t) :
    Relation.ReflTransGen (ProtectedMove w π a) (service s u) (service s t) := by
  induction t with
  | zero => obtain rfl := Nat.eq_zero_of_le_zero hu; exact .refl
  | succ t ih =>
    rcases Nat.eq_or_lt_of_le hu with rfl | hlt
    · exact .refl
    · have pre : Admissible w π a s t := fun v => h ⟨v, v.isLt.trans t.lt_succ_self⟩
      have prev := ih pre (Nat.le_of_lt_succ hlt)
      have last := h ⟨t, t.lt_succ_self⟩
      cases hs : s t with
      | none => simpa [service, hs] using prev
      | some i =>
        simp only [hs] at last
        refine prev.tail ⟨i, last.2.1, by simp [service, hs], fun j en _ prom => ?_⟩
        apply last.2.2 j _ en
        apply arrived_of_service pre
        by_contra! zero
        have eq : service s t j = 0 := Nat.eq_zero_of_le_zero zero
        simp [current, eq, Section.Held, π.rank_nil] at prom

/-- Under priority-relaxed service each job's program counter is nondecreasing. -/
theorem service_mono_of_protectedPath {a x y} (h : Relation.ReflTransGen (ProtectedMove w π a) x y)
    (i : Fin n) : x i ≤ y i := by
  apply mono_path (w := w) (π := π) _ i
  exact Relation.ReflTransGen.mono (r := ProtectedMove w π a) (p := Move w π)
    (fun _ _ ⟨q, en, eq, _⟩ => ⟨q, en, eq⟩) _ _ h

/-- With ordinary binary semaphores, relaxed steps are exactly the resource-legal moves:
no job's rank can be promoted above its base priority. -/
theorem ordinary_protectedMove {a : Arrivals n} {x y} :
    ProtectedMove w .ordinary a x y ↔ Move w .ordinary x y := by
  constructor
  · rintro ⟨i, en, rfl, _⟩; exact ⟨i, en, rfl⟩
  · rintro ⟨i, en, rfl⟩; exact ⟨i, en, rfl, fun j _ _ h => (Nat.lt_irrefl _ h).elim⟩

/-- A sufficient exit certificate. A positive guard derivation can witness a cycle, even at
deadlock. For *distinct* jobs one may instead exhibit relaxed progress and prove that every
relaxed continuation serving the victim passes the live section's V. The relaxed moves need
not respect arrivals or all rank changes: failure to certify does not refute an actual wait. -/
def CertifiedExitDependency (w : Workload T R n) (π : Protocol R) (a : Arrivals n) (x : Fin n → ℕ)
    (i j : Fin n) (k : Fin (w.code j).count) : Prop :=
  GuardExitCertificate w π x i j k ∨ (i ≠ j ∧ ((w.code j).sec k).Held (x j) ∧
    (∃ y, Relation.ReflTransGen (ProtectedMove w π a) x y ∧ x i < y i) ∧
    ∀ y, Relation.ReflTransGen (ProtectedMove w π a) x y → x i < y i →
      ((w.code j).sec k).leave < y j)

/-- Poststate soundness: on a priority-relaxed path where the victim has advanced, the V
of its certified occurrence has been executed by the final boundary. This statement neither
asserts that progress is possible nor compares the times of two instructions of the same job. -/
theorem CertifiedExitDependency.passed_of_progress {a x i j k}
    (h : CertifiedExitDependency w π a x i j k) {y}
    (path : Relation.ReflTransGen (ProtectedMove w π a) x y) (progress : x i < y i) :
    ((w.code j).sec k).leave < y j := by
  rcases h with direct | ⟨_, _, _, must⟩
  · apply direct.passed_of_progress _ progress
    exact Relation.ReflTransGen.mono (r := ProtectedMove w π a) (p := Move w π)
      (fun _ _ ⟨q, en, eq, _⟩ => ⟨q, en, eq⟩) _ _ path
  · exact must _ path progress

/-- For distinct jobs a certificate forces the owner past its matching V *at the boundary
before* any relaxed step of the victim reachable from the snapshot. The victim's own next
instruction cannot supply this exit. No converse about uncertified sections is asserted. -/
theorem CertifiedExitDependency.exited_before_step {a x i j k}
    (h : CertifiedExitDependency w π a x i j k) (diff : i ≠ j) {y}
    (path : Relation.ReflTransGen (ProtectedMove w π a) x y)
    (step : ProtectedMove w π a y (advance y i)) : ((w.code j).sec k).leave < y j := by
  have prog : x i < advance y i i := by
    simpa [advance] using Nat.lt_succ_of_le (service_mono_of_protectedPath path i)
  simpa [advance, Function.update_of_ne diff.symm] using h.passed_of_progress (path.tail step) prog

/-- Every certified occurrence is open at the snapshot: its P has occurred and its V has not. -/
theorem CertifiedExitDependency.held {a x i j k} (h : CertifiedExitDependency w π a x i j k) :
    ((w.code j).sec k).Held (x j) := h.elim (·.held) (·.2.1)

/-- A certified exit dependency has an unfinished victim. A completed job cannot take another
instruction step, even in the relaxed service relation. -/
theorem CertifiedExitDependency.pending {a x i j k} (h : CertifiedExitDependency w π a x i j k) :
    x i < (w.code i).length := by
  rcases h with cert | ⟨_, _, ⟨y, path, prog⟩, _⟩
  · induction cert with
    | guard _ pending _ _ => exact pending
    | inner _ _ _ ih => exact ih
    | chain _ _ ih _ => exact ih
  · induction path with
    | refl => exact (lt_irrefl _ prog).elim
    | @tail b c pre step ih =>
      by_cases hb : x i < b i
      · exact ih hb
      · have eq : b i = x i := le_antisymm (le_of_not_gt hb) (service_mono_of_protectedPath pre i)
        obtain ⟨q, en, rfl, _⟩ := step
        by_cases same : i = q
        · subst q; exact eq ▸ en.1
        · simp [advance, Function.update_of_ne same, eq] at prog

/-- A certificate of lower-priority blocking at a boundary: strictly lower **base** priority
of the owner, an admitted prefix, arrival of the victim and a sufficient exit dependency.
Its absence does not imply that the victim can proceed before the owner exits. -/
def CertifiedBlockedAt (w : Workload T R n) (π : Protocol R) (a : Arrivals n) (s : Schedule (Fin n))
    (t : ℕ) (i j : Fin n) (k : Fin (w.code j).count) : Prop :=
  w.base i < w.base j ∧ Admissible w π a s t ∧ a.time i ≤ t ∧
    CertifiedExitDependency w π a (service s t) i j k

/-- Actual pre-service soundness. If a lower-priority blocking certificate holds at slot `u`,
then in an admitted extension of this schedule that runs the victim in slot `v ≥ u`, the
owner's counter is past V *before slot `v`*. This says nothing about uncertified waits. -/
theorem CertifiedBlockedAt.exited_before_service {a s u i j k}
    (h : CertifiedBlockedAt w π a s u i j k) {v} (hv : u ≤ v)
    (ok : Admissible w π a s (v + 1)) (run : s v = some i) :
    ((w.code j).sec k).leave < service s v j := by
  have diff : i ≠ j := fun eq => (ne_of_lt h.1) (congrArg w.base eq)
  have pre : Admissible w π a s v := fun b => ok ⟨b, b.isLt.trans v.lt_succ_self⟩
  have path := protectedPath_of_admissible pre hv
  have allSteps := protectedPath_of_admissible ok (u := u) (hv.trans v.le_succ)
  have prog : service s u i < service s (v + 1) i := by
    simpa [service, run, advance] using Nat.lt_succ_of_le (service_mono_of_protectedPath path i)
  simpa [service, run, advance, Function.update_of_ne diff.symm] using
    h.2.2.2.passed_of_progress allSteps prog

/-- A certificate of blocking at an admitted boundary through a named semaphore: some
certified lower-job occurrence has that name on its P/V pair. Not all waits need be certified. -/
def CertifiedThroughAt (w : Workload T R n) (π : Protocol R) (a : Arrivals n) (s : Schedule (Fin n))
    (t : ℕ) (i j : Fin n) (r : R) : Prop :=
  ∃ k, CertifiedBlockedAt w π a s t i j k ∧ ((w.code j).sec k).lock = r

/-- Sections of job `j` with a certificate of blocking job `i` at some admitted boundary,
varying arrivals and schedules but fixing programs and protocol. This is sufficient evidence
only: the set is not identified with the full βᵢⱼ of Sha, Rajkumar and Lehoczky. -/
def certifiedBlockers (w : Workload T R n) (π : Protocol R) (i j : Fin n) :
    Set (Fin (w.code j).count) :=
  {k | w.base i < w.base j ∧ ∃ (a : Arrivals n) (s : Schedule (Fin n)) (t : ℕ),
    Admissible w π a s t ∧ a.time i ≤ t ∧ CertifiedExitDependency w π a (service s t) i j k}

/-- Membership in the per-owner **certified** set means that a boundary carrying a certificate
exists. This unpacks the definition, not a characterisation of all blocking episodes. -/
theorem mem_certifiedBlockers_iff {i j k} :
    k ∈ certifiedBlockers w π i j ↔ ∃ a s t, CertifiedBlockedAt w π a s t i j k := by
  constructor
  · rintro ⟨lt, a, s, t, rest⟩; exact ⟨a, s, t, lt, rest⟩
  · rintro ⟨a, s, t, lt, rest⟩; exact ⟨lt, a, s, t, rest⟩

/-- There is a certified occurrence of the lower job bearing this semaphore name. This label
need not be the victim's next requested lock. An actual wait can lack a certificate. -/
def CertifiedThrough (w : Workload T R n) (π : Protocol R) (i j : Fin n) (r : R) : Prop :=
  ∃ k ∈ certifiedBlockers w π i j, ((w.code j).sec k).lock = r

/-- A through-semaphore certificate over arrivals and schedules is witnessed by a
through-semaphore certificate at a particular boundary. Both sides concern certificates only. -/
theorem certifiedThrough_iff {i j r} : CertifiedThrough w π i j r ↔
    ∃ a s t, CertifiedThroughAt w π a s t i j r := by
  constructor
  · rintro ⟨k, hk, eq⟩
    obtain ⟨a, s, t, episode⟩ := mem_certifiedBlockers_iff.mp hk
    exact ⟨a, s, t, k, episode, eq⟩
  · rintro ⟨a, s, t, k, episode, eq⟩
    exact ⟨k, mem_certifiedBlockers_iff.mpr ⟨a, s, t, episode⟩, eq⟩

/-- Inclusion-maximal elements of the per-owner certified set. A certified occurrence is
discarded only for strict containment in another certified occurrence. An uncertified outer
blocker can be missing, so this is not an identification with the paper's β*ᵢⱼ. -/
def maximalCertifiedBlockers (w : Workload T R n) (π : Protocol R) (i j : Fin n) :
    Set (Fin (w.code j).count) :=
  {k | k ∈ certifiedBlockers w π i j ∧
    ∀ l ∈ certifiedBlockers w π i j, ¬ ((w.code j).sec k).Inside ((w.code j).sec l)}

/-- Union of the inclusion-maximal **certified** sets, retaining the owner of each occurrence.
An owner not strictly below the victim contributes nothing. No completeness for β*ᵢ is claimed. -/
def maximalCertifiedUnion (w : Workload T R n) (π : Protocol R) (i : Fin n) :
    Set ((j : Fin n) × Fin (w.code j).count) := {z | z.2 ∈ maximalCertifiedBlockers w π i z.1}

/-- A certified blocker belongs to a job with strictly lower base priority, hence a later
index in the priority listing. A later index alone is insufficient. -/
theorem lower_of_mem_certifiedBlockers {i j k} (h : k ∈ certifiedBlockers w π i j) :
    i < j ∧ w.base i < w.base j :=
  ⟨lt_of_not_ge (fun hj => (not_le_of_gt h.1) (w.numbered hj)), h.1⟩

/-- Two inclusion-maximal certified sections of the same owner cannot be properly nested.
Maximality here is relative only to certified sections. -/
theorem not_inside_of_maximalCertified {i j k l}
    (hk : k ∈ maximalCertifiedBlockers w π i j) (hl : l ∈ maximalCertifiedBlockers w π i j) :
    ¬ ((w.code j).sec k).Inside ((w.code j).sec l) := hk.2 l hl.1

/-- Each certified blocker equals or lies strictly inside a maximal **certified** blocker of
its owner. Ascent decreases the opening address. This does not cover uncertified blocking. -/
theorem exists_maximalCertified_cover {i j k} (h : k ∈ certifiedBlockers w π i j) :
    ∃ l ∈ maximalCertifiedBlockers w π i j,
      k = l ∨ ((w.code j).sec k).Inside ((w.code j).sec l) := by
  classical
  by_cases hm : k ∈ maximalCertifiedBlockers w π i j
  · exact ⟨k, hm, Or.inl rfl⟩
  · obtain ⟨l, hl, hkl⟩ : ∃ l ∈ certifiedBlockers w π i j,
        ((w.code j).sec k).Inside ((w.code j).sec l) := by
      by_contra! hn
      exact hm ⟨h, hn⟩
    obtain ⟨m, hm, rfl | hlm⟩ := exists_maximalCertified_cover hl
    · exact ⟨_, hm, Or.inr hkl⟩
    · exact ⟨_, hm, Or.inr ⟨hlm.1.trans hkl.1, hkl.2.trans hlm.2⟩⟩
termination_by ((w.code j).sec k).enter

end Cslib.Scheduling.RealTime.Semaphore
