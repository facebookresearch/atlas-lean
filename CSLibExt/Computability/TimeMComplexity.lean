/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Declared polynomial-time predicates and reductions over `TimeM`
-/
module

public import Cslib.Algorithms.Lean.TimeM
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.Complexity

/-!
# Declared polynomial-time predicates and reductions over `TimeM`

Polynomial declared-time predicates for `TimeM`
(`Cslib.Algorithms.Lean.TimeM`) algorithms, declared-time many-one reductions performed
by named `TimeM` functions, composition theorems (a decider gives a
verifier, reductions compose, deciders and verifiers pull back along
reductions), and bridge theorems to the canonical Turing-machine classes
in `MetaMathlibExt.ComplexityTheory`.

## Why there are no `P`/`NP` sets here

`TimeM`'s time annotations are trusted: its `time` field is not verified
against any actual cost (see the design principles in
`Cslib.Algorithms.Lean.TimeM`). Defining complexity classes by
quantifying over all host-language `TimeM` functions is therefore
vacuous: for every decision problem `L`, the function
`fun x => pure (L x)` has declared time `0` and decides `L`
(`exists_decidesInDeclaredPolyTime` below). Sound classes need a costed program
model, which in this repository is the canonical TM2 API behind
`MetaMathlibExt.ComplexityTheory.P`/`NP`.

This file instead provides the per-algorithm predicates and constructions
that are meaningful for `TimeM`: bounds on the declared time of *named*
algorithms, `Verifies` for named verifiers, and reductions performed by
named functions, all over the canonical `DecisionProblem` type and with
the same shapes as the canonical API. The theorems
`mem_P_of_decides`, `mem_NP_of_verifies`, and
`cookLevinPolyManyOneRed_of_declared` are repackaging lemmas: given
independently proved canonical evidence that a named algorithm's
computed function is `ComplexityTheory.IsPolyTime`, they produce
canonical class membership or a canonical reduction. That evidence
cannot be derived from the declared-time predicates (see
`exists_decidesInDeclaredPolyTime`); a sound `TimeM`-to-TM simulation
would first need a restricted executable representation with enforced
cost accounting. No such simulation and no Cook–Levin hardness is
claimed here.
-/

@[expose] public section

namespace Cslib.TimeMComplexity

open Cslib.Algorithms.Lean (TimeM)
open MetaMathlibExt.ComplexityTheory (DecisionProblem)
open Polynomial

/-- A `TimeM` decider decides in *declared* polynomial time when its
declared time is bounded by a polynomial in the input length. This
constrains only the trusted `time` annotation: it establishes neither
computability of `(f x).ret` in any machine model nor any relation to
a language (witness `fun x => pure (L x)`, for arbitrary `L`, in
`exists_decidesInDeclaredPolyTime`). -/
def DecidesInDeclaredPolyTime (f : List Bool → TimeM Nat Bool) : Prop :=
  ∃ p : Polynomial ℕ, ∀ x, (f x).time ≤ p.eval x.length

/-- A `TimeM` function computes in *declared* polynomial time when both
its declared time and its output length are bounded by a polynomial in
the input length. This is an annotation discipline only (per review):
it does not establish that `(f x).ret` is polynomial-time computable in
any machine model - for an arbitrary language `L`, `fun x => pure [L x]`
has declared time zero and constant output length. The output-length
bound is still essential: `TimeM` annotations are trusted, so without it
a function declaring zero time could emit an exponentially long output,
and closure under composition of declared bounds would fail. -/
def ComputesInDeclaredPolyTime (f : List Bool → TimeM Nat (List Bool)) : Prop :=
  ∃ p : Polynomial ℕ, ∀ x, (f x).time ≤ p.eval x.length ∧
    (f x).ret.length ≤ p.eval x.length

/-- A `TimeM` verifier runs in *declared* polynomial time when its
declared time is bounded by a polynomial in the combined input and
witness length. Like `DecidesInDeclaredPolyTime`, this constrains only
the trusted `time` annotation and establishes no computability in any
machine model. -/
def VerifierInDeclaredPolyTime (V : List Bool × List Bool → TimeM Nat Bool) : Prop :=
  ∃ q : Polynomial ℕ, ∀ xw, (V xw).time ≤ q.eval (xw.1.length + xw.2.length)

/-- `V` verifies `L` with witness bound `p`: `L x` holds iff some witness
`w` of length at most `p |x|` is accepted. This is the verifier half of
`MetaMathlibExt.ComplexityTheory.NP`, phrased for a named `TimeM`
verifier. -/
def Verifies (V : List Bool × List Bool → TimeM Nat Bool)
    (L : DecisionProblem) (p : Polynomial ℕ) : Prop :=
  ∀ x, L x ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧
    (V (x, w)).ret = true

/-- The named `TimeM` function `f` is a *declared-time* many-one
reduction from `L₁` to `L₂`: it is `ComputesInDeclaredPolyTime` and
preserves membership exactly. This is not a polynomial-time many-one
reduction in the standard or canonical TM2 sense (per review): no
computability of `(f x).ret` is established, so it must not be cited as
`Cslib.CookLevin.PolyManyOneRed` or as evidence about the canonical
complexity classes. It is the declared-time analogue of that notion,
with the reducing function named rather than quantified over (see the
module doc for why). -/
def DeclaredPolyManyOneRedVia (f : List Bool → TimeM Nat (List Bool))
    (L₁ L₂ : DecisionProblem) : Prop :=
  ComputesInDeclaredPolyTime f ∧ ∀ x, L₁ x = L₂ (f x).ret

/-- Evaluation of a polynomial with natural coefficients is monotone. -/
private theorem polyEval_mono (p : Polynomial ℕ) {m n : ℕ} (h : m ≤ n) :
    p.eval m ≤ p.eval n := by
  induction p using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [eval_add]
    exact Nat.add_le_add hp hq
  | monomial k a _ih =>
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    exact Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left h _)

/-- Unrestricted `TimeM` deciders decide every language with declared time
zero: `fun x => pure (L x)` treats evaluating `L x` as free. This is why
this file defines no `P`/`NP` sets by quantifying over `TimeM` functions;
the classes live in `MetaMathlibExt.ComplexityTheory`, and
`mem_P_of_decides`/`mem_NP_of_verifies` give the exact extra hypothesis
needed to reach them from named `TimeM` algorithms. -/
theorem exists_decidesInDeclaredPolyTime (L : DecisionProblem) :
    ∃ f : List Bool → TimeM Nat Bool, DecidesInDeclaredPolyTime f ∧
      ∀ x, (f x).ret = L x :=
  ⟨fun x => pure (L x), ⟨0, fun x => by simp⟩, fun x => rfl⟩

/-- A decider with polynomial declared time, ignoring the witness, is a
verifier with polynomial declared time. -/
theorem verifierInDeclaredPolyTime_of_decidesInDeclaredPolyTime
    {f : List Bool → TimeM Nat Bool} (hf : DecidesInDeclaredPolyTime f) :
    VerifierInDeclaredPolyTime (fun xw => f xw.1) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, fun xw => le_trans (hp xw.1) (polyEval_mono p (Nat.le_add_right _ _))⟩

/-- A decider for `L`, ignoring the witness, verifies `L` with witness
bound `0` (the empty witness). Together with
`verifierInDeclaredPolyTime_of_decidesInDeclaredPolyTime` this is the `TimeM` form of
`P ⊆ NP`, for named algorithms. -/
theorem verifies_of_decides {f : List Bool → TimeM Nat Bool}
    {L : DecisionProblem} (hdec : ∀ x, (f x).ret = L x) :
    Verifies (fun xw => f xw.1) L 0 := by
  intro x
  constructor
  · intro hx
    exact ⟨[], by simp, by rw [hdec x]; exact hx⟩
  · rintro ⟨w, -, hw⟩
    rw [← hdec x]
    exact hw

/-- Many-one reduction is reflexive, via the identity function. -/
theorem declaredPolyManyOneRedVia_refl (L : DecisionProblem) :
    DeclaredPolyManyOneRedVia (fun x => pure x) L L :=
  ⟨⟨Polynomial.X, fun x => by simp⟩, fun x => by simp⟩

/-- Many-one reductions compose. The composed time and output-length
bound is `p₁ + p₂ ∘ p₁`, using monotonicity of polynomial evaluation
together with the output-length bound on the first reduction. -/
theorem declaredPolyManyOneRedVia_trans
    {f₁ f₂ : List Bool → TimeM Nat (List Bool)} {L₁ L₂ L₃ : DecisionProblem}
    (h₁₂ : DeclaredPolyManyOneRedVia f₁ L₁ L₂) (h₂₃ : DeclaredPolyManyOneRedVia f₂ L₂ L₃) :
    DeclaredPolyManyOneRedVia (fun x => f₁ x >>= f₂) L₁ L₃ := by
  obtain ⟨⟨p₁, hf₁⟩, hr₁⟩ := h₁₂
  obtain ⟨⟨p₂, hf₂⟩, hr₂⟩ := h₂₃
  refine ⟨⟨p₁ + p₂.comp p₁, ?_⟩, ?_⟩
  · intro x
    obtain ⟨ht₁, hl₁⟩ := hf₁ x
    obtain ⟨ht₂, hl₂⟩ := hf₂ (f₁ x).ret
    have hmono : p₂.eval (f₁ x).ret.length ≤ p₂.eval (p₁.eval x.length) :=
      polyEval_mono p₂ hl₁
    constructor
    · simp only [TimeM.time_bind, eval_add, eval_comp]
      exact Nat.add_le_add ht₁ (le_trans ht₂ hmono)
    · simp only [TimeM.ret_bind, eval_add, eval_comp]
      exact le_trans (le_trans hl₂ hmono) (Nat.le_add_left _ _)
  · intro x
    simp only [TimeM.ret_bind]
    rw [hr₁ x]
    exact hr₂ _

/-- Composing a declared reduction with a decider gives a decider with
polynomial declared time, with bound `p_red + p_dec ∘ p_red`. -/
theorem decidesInDeclaredPolyTime_comp_reduction
    {f : List Bool → TimeM Nat (List Bool)} {g : List Bool → TimeM Nat Bool}
    {L₁ L₂ : DecisionProblem} (hred : DeclaredPolyManyOneRedVia f L₁ L₂)
    (hg : DecidesInDeclaredPolyTime g) :
    DecidesInDeclaredPolyTime (fun x => f x >>= g) := by
  obtain ⟨⟨pr, hf⟩, -⟩ := hred
  obtain ⟨pd, hgt⟩ := hg
  refine ⟨pr + pd.comp pr, fun x => ?_⟩
  obtain ⟨htf, hlf⟩ := hf x
  simp only [TimeM.time_bind, eval_add, eval_comp]
  exact Nat.add_le_add htf (le_trans (hgt (f x).ret) (polyEval_mono pd hlf))

/-- Composing a reduction with a decider for the target language decides
the source language. With `decidesInDeclaredPolyTime_comp_reduction`
this is the `TimeM` declared-time form of closure under reductions,
for named algorithms (no canonical `P` membership is claimed). -/
theorem decides_comp_reduction
    {f : List Bool → TimeM Nat (List Bool)} {g : List Bool → TimeM Nat Bool}
    {L₁ L₂ : DecisionProblem} (hred : DeclaredPolyManyOneRedVia f L₁ L₂)
    (hdec : ∀ x, (g x).ret = L₂ x) (x : List Bool) :
    ((fun x => f x >>= g) x).ret = L₁ x := by
  simp only [TimeM.ret_bind]
  rw [hdec, ← hred.2 x]

/-- Composing a reduction with a verifier gives a verifier for the source
language. The composed verifier first runs the reduction, then the
original verifier, rejecting witnesses longer than the original bound at
the reduced input; the witness bound is `p ∘ p_red` and the time bound is
`p_red + q ∘ (p_red + X)` in terms of `|x| + |w|`. This is the `TimeM`
declared-time form of closure under reductions, for named algorithms
(no canonical `NP` membership is claimed). -/
theorem verifies_comp_reduction
    {f : List Bool → TimeM Nat (List Bool)}
    {V : List Bool × List Bool → TimeM Nat Bool}
    {L₁ L₂ : DecisionProblem} {p : Polynomial ℕ}
    (hred : DeclaredPolyManyOneRedVia f L₁ L₂) (hVt : VerifierInDeclaredPolyTime V)
    (hV : Verifies V L₂ p) :
    ∃ p' : Polynomial ℕ,
      VerifierInDeclaredPolyTime (fun xw => f xw.1 >>= fun y =>
        (fun b => b && decide (xw.2.length ≤ p.eval y.length)) <$>
          V (y, xw.2)) ∧
      Verifies (fun xw => f xw.1 >>= fun y =>
        (fun b => b && decide (xw.2.length ≤ p.eval y.length)) <$>
          V (y, xw.2)) L₁ p' := by
  obtain ⟨⟨pr, hf⟩, hr⟩ := hred
  obtain ⟨q, hq⟩ := hVt
  refine ⟨p.comp pr, ⟨pr + q.comp (pr + Polynomial.X), ?_⟩, ?_⟩
  · rintro ⟨x, w⟩
    obtain ⟨htf, hlf⟩ := hf x
    have hV' := hq ((f x).ret, w)
    have h1 : pr.eval x.length ≤ pr.eval (x.length + w.length) :=
      polyEval_mono pr (Nat.le_add_right _ _)
    have h2 : (f x).ret.length ≤ pr.eval (x.length + w.length) :=
      le_trans hlf h1
    have h3 : (f x).ret.length + w.length ≤
        (pr + Polynomial.X).eval (x.length + w.length) := by
      simp only [eval_add, eval_X]
      exact Nat.add_le_add h2 (Nat.le_add_left _ _)
    simp only [TimeM.time_bind, TimeM.time_map]
    rw [eval_add, eval_comp]
    exact Nat.add_le_add (le_trans htf h1) (le_trans hV' (polyEval_mono q h3))
  · intro x
    constructor
    · intro hx
      rw [hr x] at hx
      obtain ⟨w, hwlen, hwV⟩ := (hV (f x).ret).mp hx
      refine ⟨w, ?_, ?_⟩
      · simp only [eval_comp]
        exact le_trans hwlen (polyEval_mono p (hf x).2)
      · simp only [TimeM.ret_bind, TimeM.ret_map]
        rw [hwV]
        simp only [Bool.true_and, decide_eq_true_eq]
        exact hwlen
    · rintro ⟨w, -, hw⟩
      simp only [TimeM.ret_bind, TimeM.ret_map, Bool.and_eq_true,
        decide_eq_true_eq] at hw
      rw [hr x]
      exact (hV (f x).ret).mpr ⟨w, hw.2, hw.1⟩

/-- Repackaging for the canonical class `P`: a named `TimeM` decider
whose computed function is polynomial-time in the canonical TM2 sense
puts its language in `MetaMathlibExt.ComplexityTheory.P`. The
`IsPolyTime` hypothesis is canonical complexity evidence that must be
proved independently for the specific decider; it cannot be derived
from `DecidesInDeclaredPolyTime`, which by
`exists_decidesInDeclaredPolyTime` holds for `fun x => pure (L x)` for
arbitrary `L`. A sound `TimeM`-to-TM simulation would first need a
restricted executable representation with enforced cost accounting. -/
theorem mem_P_of_decides {f : List Bool → TimeM Nat Bool}
    {L : DecisionProblem} (hdec : ∀ x, (f x).ret = L x)
    (h : MetaMathlibExt.ComplexityTheory.IsPolyTime fun x => (f x).ret) :
    L ∈ MetaMathlibExt.ComplexityTheory.P := by
  have hfun : (fun x => (f x).ret) = L := funext hdec
  rw [hfun] at h
  exact h

/-- Repackaging for the canonical class `NP`: a named `TimeM` verifier
whose computed function is polynomial-time in the canonical TM2 sense
puts its language in `MetaMathlibExt.ComplexityTheory.NP`, with the
same witness bound. As in `mem_P_of_decides`, the `IsPolyTime`
hypothesis must be proved independently for the specific verifier; it
does not follow from `VerifierInDeclaredPolyTime`. -/
theorem mem_NP_of_verifies {V : List Bool × List Bool → TimeM Nat Bool}
    {L : DecisionProblem} {p : Polynomial ℕ} (hver : Verifies V L p)
    (h : MetaMathlibExt.ComplexityTheory.IsPolyTime fun xw => (V xw).ret) :
    L ∈ MetaMathlibExt.ComplexityTheory.NP :=
  ⟨p, fun xw => (V xw).ret, h, hver⟩

/-- Repackaging for the canonical many-one reduction: a declared
`TimeM` reduction whose computed function is polynomial-time in the
canonical TM2 sense is a `Cslib.CookLevin.PolyManyOneRed`. As in
`mem_P_of_decides`, the `IsPolyTime` hypothesis must be proved
independently for the specific reduction; it does not follow from
`ComputesInDeclaredPolyTime`. -/
theorem cookLevinPolyManyOneRed_of_declared
    {f : List Bool → TimeM Nat (List Bool)} {L₁ L₂ : DecisionProblem}
    (hred : DeclaredPolyManyOneRedVia f L₁ L₂)
    (h : MetaMathlibExt.ComplexityTheory.IsPolyTime fun x => (f x).ret) :
    Cslib.CookLevin.PolyManyOneRed L₁ L₂ :=
  ⟨fun x => (f x).ret, h, hred.2⟩

end Cslib.TimeMComplexity
