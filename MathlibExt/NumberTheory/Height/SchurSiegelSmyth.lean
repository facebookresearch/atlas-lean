/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Algebraic.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.SchurSiegelSmyth

/-!
# The Schur--Siegel--Smyth trace constant

A complex number `α` is a totally positive algebraic integer when it is
integral over `ℤ` and every conjugate of `α` (every root in `ℂ` of its
rational minimal polynomial, counted with multiplicity) is a strictly
positive real number. Its absolute trace is the mean of its conjugates,
`tr(α) / deg(α)`.

The Schur--Siegel--Smyth constant (catalogue constant C86a) is the
smallest limiting absolute trace, in the catalogue's equivalent form: the
supremum of the `ρ ≥ 0` such that all but finitely many totally positive
algebraic integers have absolute trace at least `ρ`. It is defined here
as an extended real following the neighbouring asymptotic Dobrowolski
model, so no finite upper bound is built into the definition; the known
bounds `1.80203 ≤ C₈₆ ≤ 1.8216` and their historical predecessors are
registered as proof requests in the wanted file. This file proves the
elementary framework: absolute traces of totally positive algebraic
integers are positive, admissible bounds are downward closed, `0` is
admissible, and every admissible bound is at most the constant.

Source: Optimization Problems, constants/86a.md, frozen at
teorth/optimizationproblems commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`; SHA-256
`e8cf799325ae9277676e972b38d2f719a4de22883cf513ed2c8074b61fc0aae4`.
-/

/-- **Conjugates.** The conjugates of a complex number $\alpha$ are the roots in $\mathbb{C}$ of
its minimal polynomial over $\mathbb{Q}$, counted with multiplicity. If $\alpha$ is
transcendental, its minimal polynomial is taken to be $0$ and it has no conjugates. -/
noncomputable def conjugates (α : ℂ) : Multiset ℂ :=
  (minpoly ℚ α).aroots ℂ

/-- **Degree of a complex number.** The degree of a complex number $\alpha$ is the degree of its
minimal polynomial over $\mathbb{Q}$. If $\alpha$ is transcendental, its minimal polynomial is
taken to be $0$, so its degree is $0$. -/
noncomputable def degree (α : ℂ) : ℕ :=
  (minpoly ℚ α).natDegree

/-- **Trace as the sum of conjugates.** For $\alpha \in \mathbb{C}$, the trace of $\alpha$ is
the sum of its conjugates, that is, of the roots in $\mathbb{C}$ of the minimal polynomial of
$\alpha$ over $\mathbb{Q}$, counted with multiplicity. For transcendental $\alpha$ there are no
conjugates and the trace is $0$. -/
noncomputable def trace (α : ℂ) : ℂ :=
  (conjugates α).sum

/-- **Absolute trace.** The absolute trace of a complex number $\alpha$ is the real number
obtained by dividing the real part of the trace of $\alpha$ by the degree of $\alpha$. If
$\alpha$ is transcendental, its trace and its degree are both $0$, and its absolute trace is
taken to be $0$.

For algebraic $\alpha$ the trace is real, and for a totally positive algebraic integer $\alpha$
the absolute trace is the mean of the conjugates of $\alpha$. -/
noncomputable def absoluteTrace (α : ℂ) : ℝ :=
  (trace α).re / degree α

/-- **Totally positive algebraic integers.** A complex number $\alpha$ is a totally positive
algebraic integer when it is integral over $\mathbb{Z}$ and every conjugate of $\alpha$ (every
root in $\mathbb{C}$ of its minimal polynomial over $\mathbb{Q}$) is a strictly positive real
number. -/
def IsTotallyPositive (α : ℂ) : Prop :=
  IsIntegral ℤ α ∧ ∀ β ∈ conjugates α, β.im = 0 ∧ 0 < β.re

theorem isAlgebraic_rat_of_isIntegral_int {α : ℂ} (h : IsIntegral ℤ α) :
    IsAlgebraic ℚ α := by
  obtain ⟨p, hp, heval⟩ := h
  exact ⟨p.map (Int.castRingHom ℚ), (hp.map _).ne_zero, by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    exact heval⟩

theorem degree_pos_of_isIntegral_int {α : ℂ} (h : IsIntegral ℤ α) :
    0 < degree α := by
  have hQ : IsIntegral ℚ α := h.tower_top
  exact minpoly.natDegree_pos hQ

theorem self_mem_conjugates {α : ℂ} (h : IsIntegral ℤ α) :
    α ∈ conjugates α := by
  rw [conjugates, Polynomial.mem_aroots]
  have hQ : IsIntegral ℚ α := h.tower_top
  exact ⟨minpoly.ne_zero hQ, minpoly.aeval ℚ α⟩

private theorem re_multiset_sum (s : Multiset ℂ) :
    s.sum.re = (s.map Complex.re).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

private theorem multiset_sum_pos_of_nonempty {s : Multiset ℝ}
    (hne : s ≠ 0) (hpos : ∀ x ∈ s, 0 < x) : 0 < s.sum := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hne
  | cons a s ih =>
    by_cases hs : s = 0
    · subst hs
      simpa using hpos a (by simp)
    · have h1 : 0 < a := hpos a (by simp)
      have h2 : 0 < s.sum := ih hs (fun x hx => hpos x (Multiset.mem_cons_of_mem hx))
      simp only [Multiset.sum_cons]
      linarith

/-- **The trace of a totally positive algebraic integer has positive real part.** If
$\alpha \in \mathbb{C}$ is a totally positive algebraic integer, then the real part of the trace
of $\alpha$ is strictly positive. -/
theorem trace_pos_re {α : ℂ} (hα : IsTotallyPositive α) :
    0 < (trace α).re := by
  rw [trace, re_multiset_sum]
  have hmem := self_mem_conjugates hα.1
  have hne : conjugates α ≠ 0 := by
    intro hc
    rw [hc] at hmem
    simp at hmem
  apply multiset_sum_pos_of_nonempty
  · intro h0
    exact hne (Multiset.map_eq_zero.mp h0)
  · intro x hx
    obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hx
    exact (hα.2 β hβ).2

/-- **The trace of a totally positive algebraic integer is real.** If $\alpha \in \mathbb{C}$ is
a totally positive algebraic integer, then the imaginary part of the trace of $\alpha$ is $0$. -/
theorem trace_im_eq_zero {α : ℂ} (hα : IsTotallyPositive α) :
    (trace α).im = 0 := by
  have : (trace α).im = ((conjugates α).map Complex.im).sum := by
    rw [trace]
    induction conjugates α using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp [ih]
  rw [this]
  apply Multiset.sum_eq_zero
  intro x hx
  obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hx
  exact (hα.2 β hβ).1

/-- **Positivity of the absolute trace.** If a complex number $\alpha$ is a totally positive
algebraic integer, then the absolute trace of $\alpha$ is strictly positive. -/
theorem absoluteTrace_pos {α : ℂ} (hα : IsTotallyPositive α) :
    0 < absoluteTrace α :=
  div_pos (trace_pos_re hα) (by exact_mod_cast degree_pos_of_isIntegral_int hα.1)

/-- **Minimal polynomial of one.** The minimal polynomial of $1 \in \mathbb{C}$ over $\mathbb{Q}$
is $X - 1$. -/
theorem minpoly_rat_one_eq : minpoly ℚ (1 : ℂ) = Polynomial.X - Polynomial.C (1 : ℚ) := by
  rw [minpoly.one]
  simp

theorem conjugates_one : conjugates (1 : ℂ) = {1} := by
  rw [conjugates, minpoly_rat_one_eq, Polynomial.aroots_X_sub_C]
  simp

theorem degree_one : degree (1 : ℂ) = 1 := by
  rw [degree, minpoly_rat_one_eq, Polynomial.natDegree_X_sub_C]

/-- **One is a totally positive algebraic integer.** The complex number $1$ is a totally
positive algebraic integer. -/
theorem isTotallyPositive_one : IsTotallyPositive (1 : ℂ) := by
  refine ⟨isIntegral_one, ?_⟩
  intro β hβ
  rw [conjugates_one] at hβ
  simp at hβ
  rw [hβ]
  simp

theorem absoluteTrace_one : absoluteTrace (1 : ℂ) = 1 := by
  rw [absoluteTrace, trace, conjugates_one, degree_one]
  simp

/-- **Admissible trace bounds.** A real number $\rho$ is admissible when $\rho \ge 0$ and only
finitely many totally positive algebraic integers $\alpha \in \mathbb{C}$ have absolute trace
less than $\rho$. -/
def IsAdmissible (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧ {α : ℂ | IsTotallyPositive α ∧ absoluteTrace α < ρ}.Finite

/-- **Schur–Siegel–Smyth trace constant.** The Schur–Siegel–Smyth trace constant $C_{86}$ is
the supremum, taken in the extended reals, of the admissible real bounds: the real numbers
$\rho \ge 0$ such that only finitely many complex numbers that are totally positive algebraic
integers have absolute trace less than $\rho$.

The extended-real value is $-\infty$ for an empty admissible set and $+\infty$ for an unbounded
one; finiteness is the content of the known upper bounds. -/
noncomputable def schurSiegelSmythConstant : EReal :=
  sSup {x : EReal | ∃ ρ : ℝ, IsAdmissible ρ ∧ x = ρ}

theorem isAdmissible_zero : IsAdmissible 0 := by
  refine ⟨le_refl 0, ?_⟩
  have hempty : {α : ℂ | IsTotallyPositive α ∧ absoluteTrace α < (0 : ℝ)} = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    rintro α ⟨hα, hlt⟩
    exact absurd hlt (not_lt_of_gt (absoluteTrace_pos hα))
  rw [hempty]
  exact Set.finite_empty

theorem IsAdmissible.mono {ρ ρ' : ℝ} (hρ : IsAdmissible ρ) (hle : ρ' ≤ ρ)
    (hρ' : 0 ≤ ρ') : IsAdmissible ρ' := by
  refine ⟨hρ', hρ.2.subset ?_⟩
  intro α hα
  exact ⟨hα.1, lt_of_lt_of_le hα.2 hle⟩

/-- **Admissible bounds lie below the Schur–Siegel–Smyth constant.** Let $C_{86}$ be the
Schur–Siegel–Smyth trace constant, an extended real number. Every admissible real number $\rho$
satisfies $\rho \le C_{86}$ in the extended reals. -/
theorem coe_le_schurSiegelSmythConstant {ρ : ℝ} (hρ : IsAdmissible ρ) :
    (ρ : EReal) ≤ schurSiegelSmythConstant :=
  le_sSup ⟨ρ, hρ, rfl⟩

/-- **Upper bounds for the Schur–Siegel–Smyth constant.** For every extended real number $b$, the
Schur–Siegel–Smyth trace constant is at most $b$ if and only if every admissible real number
$c$ satisfies $c \le b$. -/
theorem schurSiegelSmythConstant_le_iff {b : EReal} :
    schurSiegelSmythConstant ≤ b ↔
      ∀ c : ℝ, IsAdmissible c → (c : EReal) ≤ b := by
  constructor
  · intro hb c hc
    exact (coe_le_schurSiegelSmythConstant hc).trans hb
  · intro hb
    apply sSup_le
    rintro x ⟨c, hc, rfl⟩
    exact hb c hc

theorem zero_le_schurSiegelSmythConstant :
    (0 : EReal) ≤ schurSiegelSmythConstant :=
  coe_le_schurSiegelSmythConstant isAdmissible_zero


end MathlibExt.NumberTheory.SchurSiegelSmyth
