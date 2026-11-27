/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Set.Basic

/-!
# Failure detector classes

The clock is an external index with ticks `ℕ`, not a clock available to the processes.
The process type is finite. The history is a total assignment of suspect sets, including at
observers that have crashed; the accuracy properties specify which observations are relevant.
In particular, the formal strong accuracy clause of §2.3 restricts *both* processes to those
still alive at the tick, a restriction left implicit in “no process is suspected before it
crashes.” At the first tick a process belongs to the crash set, it is no longer alive.

The eventual accuracy definitions use the fixed set of correct processes, as in the paper's
simplified formulas. Over a finite population the set of processes still alive stabilizes to
that set: take a common bound on the crash ticks of all processes that crash (or zero if none
crash). The completeness and eventual accuracy bounds below are inclusive.

## References

* T. D. Chandra and S. Toueg, *Unreliable failure detectors for reliable distributed systems*,
  Journal of the ACM 43(2):225–267, 1996, §§2.1–2.4 and Figure 1.
-/

@[expose] public section

namespace Cslib.Distributed.FailureDetector

/-- A crash failure pattern on a finite process type assigns a growing set of crashed
processes to each natural-number tick and leaves at least one process correct forever. -/
structure FailurePattern (Proc : Type*) [Finite Proc] where
  /-- Processes that have crashed at or before the given tick. -/
  crashedBy : ℕ → Set Proc
  /-- A process that has crashed never leaves the crash set. -/
  mono : Monotone crashedBy
  /-- At least one process never crashes. -/
  exists_correct : ∃ p, ∀ t, p ∉ crashedBy t

variable {Proc : Type*}

/-- The suspicion history assigns to each observer and each natural-number tick the set
of processes it suspects at that tick. Observers need not agree, and suspicions can be removed. -/
abbrev History (Proc : Type*) := Proc → ℕ → Set Proc

variable [Finite Proc]

/-- The processes that crash in a pattern are those in its crash set at some tick. -/
def FailurePattern.crashed (F : FailurePattern Proc) : Set Proc :=
  {p | ∃ t, p ∈ F.crashedBy t}

/-- The correct processes are those that never enter the crash set, i.e. the complement of
`FailurePattern.crashed`. -/
def FailurePattern.correct (F : FailurePattern Proc) : Set Proc :=
  {p | ∀ t, p ∉ F.crashedBy t}

/-- A failure detector assigns a set of permitted suspicion histories to each failure pattern.
This is an abstract specification, with no requirement of nonempty history sets or of an
implementation. -/
abbrev Detector (Proc : Type*) [Finite Proc] := FailurePattern Proc → Set (History Proc)

/-- Strong completeness: for every pattern and permitted history there is a common tick from
which every correct observer permanently suspects every process that crashes. -/
def Detector.StrongCompleteness (D : Detector Proc) : Prop :=
  ∀ F, ∀ H ∈ D F, ∃ T : ℕ, ∀ p ∈ F.crashed, ∀ q ∈ F.correct, ∀ t ≥ T, p ∈ H q t

/-- Weak completeness: for every pattern and permitted history there is a common tick from
which each process that crashes is permanently suspected by a fixed correct observer. The
observer may depend on the crashed process, but not on the tick. -/
def Detector.WeakCompleteness (D : Detector Proc) : Prop :=
  ∀ F, ∀ H ∈ D F, ∃ T : ℕ, ∀ p ∈ F.crashed, ∃ q ∈ F.correct, ∀ t ≥ T, p ∈ H q t

/-- Strong accuracy: for every pattern and permitted history, at each tick no observer still
alive suspects a target still alive. A process is alive exactly when it has not crashed by that
tick; the restriction on suspecting it ends at its crash tick. -/
def Detector.StrongAccuracy (D : Detector Proc) : Prop :=
  ∀ F, ∀ H ∈ D F, ∀ t p q, p ∉ F.crashedBy t → q ∉ F.crashedBy t → p ∉ H q t

/-- Weak accuracy: for every pattern and permitted history some fixed correct process is not
suspected at any tick by any observer still alive at that tick, even if the observer later
crashes. -/
def Detector.WeakAccuracy (D : Detector Proc) : Prop :=
  ∀ F, ∀ H ∈ D F, ∃ p ∈ F.correct, ∀ t q, q ∉ F.crashedBy t → p ∉ H q t

/-- Eventual strong accuracy: for every pattern and permitted history there is a tick from
which no correct observer suspects any correct target. -/
def Detector.EventualStrongAccuracy (D : Detector Proc) : Prop :=
  ∀ F, ∀ H ∈ D F, ∃ T : ℕ, ∀ t ≥ T, ∀ p ∈ F.correct, ∀ q ∈ F.correct, p ∉ H q t

/-- Eventual weak accuracy: for every pattern and permitted history there are a tick and a
fixed correct target which no correct observer suspects from that tick onward. -/
def Detector.EventualWeakAccuracy (D : Detector Proc) : Prop :=
  ∀ F, ∀ H ∈ D F, ∃ T : ℕ, ∃ p ∈ F.correct, ∀ t ≥ T, ∀ q ∈ F.correct, p ∉ H q t

/-- Names for the eight combinations of completeness and accuracy in Chandra–Toueg Figure 1. -/
inductive DetectorClass where
  /-- $\mathcal{P}$ (perfect). -/
  | perfect
  /-- $\mathcal{S}$ (strong). -/
  | strong
  /-- $\Diamond\mathcal{P}$ (eventually perfect). -/
  | eventuallyPerfect
  /-- $\Diamond\mathcal{S}$ (eventually strong). -/
  | eventuallyStrong
  /-- $\mathcal{Q}$. -/
  | q
  /-- $\mathcal{W}$ (weak). -/
  | weak
  /-- $\Diamond\mathcal{Q}$. -/
  | eventuallyQ
  /-- $\Diamond\mathcal{W}$ (eventually weak). -/
  | eventuallyWeak

/-- The eight failure detector classes of Chandra–Toueg Figure 1, as sets of detectors on a
finite process population. The classes $\mathcal{P}$, $\mathcal{S}$, $\Diamond\mathcal{P}$ and
$\Diamond\mathcal{S}$ pair strong completeness with strong, weak, eventual strong and eventual
weak accuracy, respectively. The second row, $\mathcal{Q}$, $\mathcal{W}$, $\Diamond\mathcal{Q}$
and $\Diamond\mathcal{W}$, pairs weak completeness with the same four accuracy notions. -/
def DetectorClass.detectors (kind : DetectorClass) : Set (Detector Proc) :=
  {D | match kind with
    | .perfect => D.StrongCompleteness ∧ D.StrongAccuracy
    | .strong => D.StrongCompleteness ∧ D.WeakAccuracy
    | .eventuallyPerfect => D.StrongCompleteness ∧ D.EventualStrongAccuracy
    | .eventuallyStrong => D.StrongCompleteness ∧ D.EventualWeakAccuracy
    | .q => D.WeakCompleteness ∧ D.StrongAccuracy
    | .weak => D.WeakCompleteness ∧ D.WeakAccuracy
    | .eventuallyQ => D.WeakCompleteness ∧ D.EventualStrongAccuracy
    | .eventuallyWeak => D.WeakCompleteness ∧ D.EventualWeakAccuracy}

end Cslib.Distributed.FailureDetector
