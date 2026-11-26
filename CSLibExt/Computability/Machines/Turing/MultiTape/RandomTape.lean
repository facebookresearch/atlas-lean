/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.MultiTape.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Uniform probabilistic Turing machines

A single finite transition table runs on a binary input and a two-way infinite tape of fair
bits. We use CSLib's work tape number zero for the random tape. Its head can move like any
work head, but no action can write there. Once the tape is fixed, the run is deterministic.

Pass and shelat, *A Course in Cryptography* (Cornell, 2010), Definitions 23.4 and 23.5.
We allow a constant term in the polynomial bound, including at input length zero.
-/

@[expose] public section

open _root_.Turing MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Cslib.Turing

/-- A binary Turing machine with $s$ control states, one read-only input tape, a write-only
output, $k$ ordinary work tapes and a read-only random tape. Tape number zero among the $k+1$
auxiliary tapes holds the random bits. Every table entry forbids writes to that tape but may
move its head. The table sees only the state and the symbols under the heads. -/
structure RandomTapeTM (k s : ℕ) where
  /-- Initial control state. -/
  start : Fin s
  /-- One local action for each possible tuple of scanned symbols and control state. -/
  transition : Fin s → Option Bool → (Fin (k + 1) → Option Bool) → Action (k + 1) Bool (Fin s)
  /-- The random head never writes or erases a cell. -/
  readOnly : ∀ q a w, ((transition q a w).workTapes 0).1 = none

namespace RandomTapeTM

variable {k s : ℕ} (M : RandomTapeTM k s) {x : List Bool}

/-- Loading the bits $r(i)$ into auxiliary tape zero, leaving all heads, the state, the output
and every ordinary work tape unchanged. -/
def loadTape (r : ℤ → Bool) (c : Cfg (k + 1) Bool (Fin s) x) : Cfg (k + 1) Bool (Fin s) x :=
  { c with workTapes := Function.update c.workTapes 0 (fun i ↦ some (r i)) }

/-- The configuration after $t$ transitions on input $x$ and tape $r$. Initially the random
head is at zero, all ordinary work tapes are blank, and the output is empty. A halted
configuration remains fixed. -/
noncomputable def run (x : List Bool) (r : ℤ → Bool) (t : ℕ) : Cfg (k + 1) Bool (Fin s) x :=
  (_root_.Turing.MultiTapeTM.ofTr M.start M.transition).runFrom (loadTape r (.init M.start x)) t

/-- The fixed-tape run is obtained by iterating the successor given by the machine's table. -/
theorem run_eq_iterate (x : List Bool) (r : ℤ → Bool) (t : ℕ) :
    M.run x r t = (MultiTapeTM.stepWith M.transition)^[t] (loadTape r (.init M.start x)) :=
  MultiTapeTM.runFrom_ofTr ..

/-- A worst-case time bound $T$: on every binary word $x$ and every assignment of bits to the
random tape the machine has halted by $T(|x|)$ transitions. -/
def RunsInTime (T : ℕ → ℕ) : Prop := ∀ x r, (M.run x r (T x.length)).Halted

/-- A uniform probabilistic polynomial-time machine is one fixed finite random-tape machine
for which a single polynomial with natural coefficients bounds the number of transitions to
halt on every binary input and every random tape. The bound includes the empty input. -/
def IsPPT : Prop := ∃ p : Polynomial ℕ, M.RunsInTime p.eval

/-- The random tape has the product law of independent fair bits indexed by the integers. -/
noncomputable def tapeLaw : Measure (ℤ → Bool) :=
  Measure.infinitePi fun _ : ℤ ↦ bernoulliMeasure true false ⟨1 / 2, by constructor <;> norm_num⟩

instance : IsProbabilityMeasure tapeLaw := by unfold tapeLaw; infer_instance

private theorem load_load (r v : ℤ → Bool) (c : Cfg (k + 1) Bool (Fin s) x) :
    loadTape r (loadTape v c) = loadTape r c := by simp [loadTape, Function.update_idem]

private theorem apply_load (a : Action (k + 1) Bool (Fin s)) (ha : (a.workTapes 0).1 = none)
    (r : ℤ → Bool) (c : Cfg (k + 1) Bool (Fin s) x) :
    a.apply (loadTape r c) = loadTape r (a.apply c) := by
  apply Cfg.ext <;> try rfl
  funext i
  by_cases hi : i = 0
  · subst i; simp [Action.apply, loadTape, ha]
  · simp [Action.apply, loadTape, hi]

-- At a fixed configuration only the bit at the current random head selects the next branch.
private theorem step_load (r : ℤ → Bool) (c : Cfg (k + 1) Bool (Fin s) x) :
    MultiTapeTM.stepWith M.transition (loadTape r c) =
      loadTape r (MultiTapeTM.stepWith M.transition
        (loadTape (fun _ ↦ r (c.workTapePos 0)) c)) := by
  let v := fun _ : ℤ ↦ r (c.workTapePos 0)
  have hs : (loadTape r c).workTapeSymbols = (loadTape v c).workTapeSymbols := by
    funext i
    by_cases hi : i = 0
    · subst i; simp [Cfg.workTapeSymbols, loadTape, v]
    · simp [Cfg.workTapeSymbols, loadTape, hi]
  change MultiTapeTM.stepWith M.transition (loadTape r c) =
    loadTape r (MultiTapeTM.stepWith M.transition (loadTape v c))
  cases h : c.state with
  | none => simpa only [MultiTapeTM.stepWith, show (loadTape r c).state = none from h,
      show (loadTape v c).state = none from h] using (load_load r v c).symm
  | some q =>
    simp only [MultiTapeTM.stepWith, show (loadTape r c).state = some q from h,
      show (loadTape v c).state = some q from h, hs]
    change (M.transition q c.inputSymbol _).apply (loadTape r c) =
      loadTape r ((M.transition q c.inputSymbol _).apply (loadTape v c))
    simp only [apply_load _ (M.readOnly ..), load_load]

-- The word space is countable and discrete. Use its mass function for the public output law.
local instance : MeasurableSpace (List Bool) := ⊤

private theorem measurable_iterate_output (t : ℕ) (c : Cfg (k + 1) Bool (Fin s) x) :
    Measurable fun r ↦ ((MultiTapeTM.stepWith M.transition)^[t] (loadTape r c)).output := by
  induction t generalizing c with
  | zero => exact measurable_const
  | succ t ih =>
    let next := fun b : Bool ↦ MultiTapeTM.stepWith M.transition (loadTape (fun _ ↦ b) c)
    have he : MeasurableSet {r : ℤ → Bool | r (c.workTapePos 0) = true} :=
      measurableSet_eq_fun (measurable_pi_apply _) measurable_const
    let out := fun b (r : ℤ → Bool) ↦
      ((MultiTapeTM.stepWith M.transition)^[t] (loadTape r (next b))).output
    have hm : Measurable fun r ↦ if r (c.workTapePos 0) = true then out true r else out false r :=
      Measurable.ite he (ih (next true)) (ih (next false))
    convert hm using 1
    funext r
    rw [Function.iterate_succ_apply, M.step_load]
    by_cases h : r (c.workTapePos 0) = true
    · simp [out, next, h]
    · simp [out, next, Bool.eq_false_iff.mpr h]

/-- The output word after a fixed number of transitions is a measurable function of the random
bits, with the discrete measurable space on words. -/
theorem measurable_run_output (x : List Bool) (t : ℕ) :
    Measurable fun r ↦ (M.run x r t).output := by
  simp only [M.run_eq_iterate]; exact M.measurable_iterate_output ..

/-- The output distribution on input $x$ for a uniform PPT machine: push the fair tape law
forward by reading the output after a polynomial time bound, and take its mass function. -/
noncomputable def outputLaw (h : M.IsPPT) (x : List Bool) : PMF (List Bool) :=
  let f := fun r ↦ (M.run x r (h.choose.eval x.length)).output
  haveI : IsProbabilityMeasure (tapeLaw.map f) :=
    (Measure.isProbabilityMeasure_map_iff (M.measurable_run_output ..).aemeasurable).2 inferInstance
  (tapeLaw.map f).toPMF

/-- For any valid time bound $T$, the mass of $y$ in the output law on $x$ is the probability
of tapes whose run has output $y$ after $T(|x|)$ transitions. Thus the law does not depend on
which polynomial witnesses the running-time bound. -/
theorem outputLaw_apply (h : M.IsPPT) {T : ℕ → ℕ} (hT : M.RunsInTime T) (x y : List Bool) :
    M.outputLaw h x y = tapeLaw {r | (M.run x r (T x.length)).output = y} := by
  rw [outputLaw, Measure.toPMF_apply, Measure.map_apply (M.measurable_run_output ..)
    (measurableSet_singleton y)]
  congr 1
  ext r
  change (M.run x r _).output = y ↔ (M.run x r _).output = y
  have hp := h.choose_spec x r
  have ht := hT x r
  rcases le_total (h.choose.eval x.length) (T x.length) with hle | hle
  · rw [show M.run x r (T x.length) = M.run x r (h.choose.eval x.length) from
      _root_.Turing.MultiTapeTM.runFrom_eq_of_halt _ _ hle hp]
  · rw [show M.run x r (h.choose.eval x.length) = M.run x r (T x.length) from
      _root_.Turing.MultiTapeTM.runFrom_eq_of_halt _ _ hle ht]

end RandomTapeTM
end Cslib.Turing
