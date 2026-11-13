/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

/-!
# Fork-join programs: work and span

A fork-join program (`Prog`) is built from unit tasks by sequential composition (`seq`) and
parallel composition (`par`). Its *work* is the number of tasks and its *span* the number of
tasks on a longest sequential chain: both add under `seq`, while under `par` the work adds and
the span is the maximum (CLRS, third edition, Section 27.1).

* `Prog.work`, `Prog.span`, the composition identities `Prog.work_seq`, `Prog.work_par`,
  `Prog.span_seq`, `Prog.span_par`, and `Prog.span_le_work`.
* `brent_level_bound`: a standalone list inequality in natural numbers, the arithmetic step of
  Brent's level-by-level bound. It is not connected to `Prog`: no level decomposition or
  schedule of a program is constructed here. The scheduling theorem itself, on computation
  DAGs, is `Cslib.Algorithms.Lean.Parallel.Brent.levelSchedule_length`.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Parallel.ForkJoin

/-- A fork-join program: sequential composition and parallel
composition of atomic unit tasks. -/
inductive Prog
  | task : Prog
  | seq : Prog → Prog → Prog
  | par : Prog → Prog → Prog

/-- Work: total number of tasks (with multiplicity). -/
def Prog.work : Prog → ℕ
  | .task => 1
  | .seq a b => a.work + b.work
  | .par a b => a.work + b.work

/-- Span: length of the longest sequential chain. -/
def Prog.span : Prog → ℕ
  | .task => 1
  | .seq a b => a.span + b.span
  | .par a b => max a.span b.span

/-- The span never exceeds the work. -/
theorem Prog.span_le_work (p : Prog) : p.span ≤ p.work := by
  induction p with
  | task => simp [Prog.span, Prog.work]
  | seq a b iha ihb =>
    simp only [Prog.span, Prog.work]
    exact Nat.add_le_add iha ihb
  | par a b iha ihb =>
    simp only [Prog.span, Prog.work]
    rw [Nat.max_le]
    constructor
    · omega
    · omega

/-- Work and span of sequential composition are additive in work
and span, and parallel composition is additive in work and
maximal in span (the fork-join cost semantics). -/
theorem Prog.work_seq (a b : Prog) : (a.seq b).work = a.work + b.work := rfl

theorem Prog.work_par (a b : Prog) : (a.par b).work = a.work + b.work := rfl

theorem Prog.span_seq (a b : Prog) : (a.seq b).span = a.span + b.span := rfl

theorem Prog.span_par (a b : Prog) : (a.par b).span = max a.span b.span := rfl

private theorem ceil_div_le (w p : ℕ) (hp : 0 < p) :
    (w + p - 1) / p ≤ w / p + 1 := by
  have hle : w + p - 1 ≤ w + p := by omega
  have hdiv_le : (w + p - 1) / p ≤ (w + p) / p :=
    Nat.div_le_div_right hle
  have heq : w + p = w + 1 * p := by omega
  have hdiv_eq : (w + p) / p = w / p + 1 := by
    rw [heq, Nat.add_mul_div_right _ _ hp]
  omega

/-- Standalone list inequality, the arithmetic step of Brent's
level-by-level bound: for any list `levels` of per-level task counts
and `p ≥ 1`, running each level in `⌈w / p⌉` steps takes in total
`∑ w ∈ levels, ⌈w / p⌉ ≤ (∑ w ∈ levels, w) / p + levels.length`
steps. This is the natural-number form: `⌈w / p⌉` is written
`(w + p - 1) / p` and `/` is truncating `Nat` division. The lemma
does not relate `levels` to a `Prog`; it does not construct a level
decomposition or a schedule. -/
theorem brent_level_bound (levels : List ℕ) {p : ℕ} (hp : 0 < p) :
    (levels.map (fun w => (w + p - 1) / p)).sum ≤
      levels.sum / p + levels.length := by
  induction levels with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hpoint := ceil_div_le a p hp
    have hdiv := Nat.div_add_div_le_add_div (x := a) (y := l.sum) (z := p)
    omega

end Cslib.Algorithms.Lean.Parallel.ForkJoin
