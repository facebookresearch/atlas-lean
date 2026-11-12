/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

@[expose] public section


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

/-- Brent-type bound for the level schedule: running a program
whose level decomposition (list of per-level work amounts, the
level count being the span) on `p ≥ 1` processors takes total
time `∑ w ∈ levels, ⌈w / p⌉ ≤ work / p + span` (real form). For
the abstract statement, `levels` is any list of naturals whose
sum is the work and whose length is the span. -/
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
