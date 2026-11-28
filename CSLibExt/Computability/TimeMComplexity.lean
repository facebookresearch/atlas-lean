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

/-- **Declared polynomial time for timed deciders.** Let $f$ be a timed function that maps each
list $x$ of Booleans to a Boolean $f(x)$ together with a declared time $t_f(x) \in \mathbb{N}$.
Then $f$ decides in declared polynomial time when there is a polynomial $p$ with natural-number
coefficients such that $t_f(x) \le p(|x|)$ for every list $x$ of Booleans, where $|x|$ is the
length of $x$.

This constrains only the trusted time annotation: it implies neither that $f$ is computable in
any machine model nor that $f$ is related to any particular decision problem. -/
def DecidesInDeclaredPolyTime (f : List Bool → TimeM Nat Bool) : Prop :=
  ∃ p : Polynomial ℕ, ∀ x, (f x).time ≤ p.eval x.length

/-- **Declared polynomial time for timed functions on bitstrings.** Let $f$ be a timed function
that maps each list $x$ of Booleans to an output list $f(x)$ of Booleans together with a declared
time $t_f(x) \in \mathbb{N}$. Then $f$ computes in declared polynomial time when there is a
polynomial $p$ with natural-number coefficients such that, for every list $x$ of Booleans, both
$t_f(x)$ and the length of $f(x)$ are at most $p(|x|)$, where $|x|$ is the length of $x$.

Declared times are trusted annotations, not checked against any machine model, so this does not
make $f$ polynomial-time computable: for an arbitrary decision problem $L$, the function returning
the one-element list $[L(x)]$ with declared time $0$ satisfies it. The output-length bound is what
lets declared bounds compose. -/
def ComputesInDeclaredPolyTime (f : List Bool → TimeM Nat (List Bool)) : Prop :=
  ∃ p : Polynomial ℕ, ∀ x, (f x).time ≤ p.eval x.length ∧
    (f x).ret.length ≤ p.eval x.length

/-- **Verifiers with polynomial declared time.** A timed verifier $V$, which assigns to each pair
of bit strings $(x, w)$ (an input and a witness) a timed computation returning a Boolean, runs in
declared polynomial time when there is a polynomial $q$ with natural coefficients such that the
declared time of $V(x, w)$ is at most $q(|x| + |w|)$ for all $x$ and $w$.

As for deciders, this constrains only the declared time, which is a trusted annotation, and
establishes no computability in any machine model. -/
def VerifierInDeclaredPolyTime (V : List Bool × List Bool → TimeM Nat Bool) : Prop :=
  ∃ q : Polynomial ℕ, ∀ xw, (V xw).time ≤ q.eval (xw.1.length + xw.2.length)

/-- **Verifying a decision problem with a witness bound.** A timed verifier $V$, which assigns to
each pair of bit strings $(x, w)$ (an input and a witness) a timed computation returning a
Boolean, verifies a decision problem $L$ with witness bound $p$, a polynomial with natural
coefficients, when for every bit string $x$, $L(x)$ holds if and only if there is a witness $w$
with $|w| \le p(|x|)$ such that $V(x, w)$ returns true.

This is the verifier half of the definition of NP, phrased for a named timed verifier. -/
def Verifies (V : List Bool × List Bool → TimeM Nat Bool)
    (L : DecisionProblem) (p : Polynomial ℕ) : Prop :=
  ∀ x, L x ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧
    (V (x, w)).ret = true

/-- **Declared-time many-one reduction by a timed function.** Let $L_1$ and $L_2$ be decision
problems and let $f$ be a timed function that maps each list $x$ of Booleans to a list $f(x)$ of
Booleans together with a declared time. Then $f$ is a declared-time many-one reduction from $L_1$
to $L_2$ when $f$ computes in declared polynomial time and $L_1(x) = L_2(f(x))$ for every list $x$
of Booleans.

Because declared times are trusted annotations, this is not a polynomial-time many-one reduction
in the Turing-machine sense: nothing is established about the computability of $f$. -/
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

/-- **Every decision problem has a timed decider in declared polynomial time.** For every decision
problem $L$ there is a timed function $f$ from lists of Booleans to Booleans that decides in
declared polynomial time and whose output $f(x)$ equals $L(x)$ for every list $x$ of Booleans.

The witness returns $L(x)$ with declared time $0$, treating the evaluation of $L$ as free. This is
why no complexity classes are defined by quantifying over timed functions. -/
theorem exists_decidesInDeclaredPolyTime (L : DecisionProblem) :
    ∃ f : List Bool → TimeM Nat Bool, DecidesInDeclaredPolyTime f ∧
      ∀ x, (f x).ret = L x :=
  ⟨fun x => pure (L x), ⟨0, fun x => by simp⟩, fun x => rfl⟩

/-- **A decider with polynomial declared time gives a verifier with polynomial declared time.**
If a timed decider $f$ on bit strings has declared time bounded by a polynomial in the input
length, then the verifier that sends an input $x$ and a witness $w$ to $f(x)$, ignoring $w$, has
declared time bounded by a polynomial in $|x| + |w|$. -/
theorem verifierInDeclaredPolyTime_of_decidesInDeclaredPolyTime
    {f : List Bool → TimeM Nat Bool} (hf : DecidesInDeclaredPolyTime f) :
    VerifierInDeclaredPolyTime (fun xw => f xw.1) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, fun xw => le_trans (hp xw.1) (polyEval_mono p (Nat.le_add_right _ _))⟩

/-- **A decider is a verifier with witness bound zero.** Let $L$ be a decision problem and let $f$
be a timed decider whose return value on every bit string $x$ equals $L(x)$. Then the verifier
that sends an input $x$ and a witness $w$ to $f(x)$, ignoring $w$, verifies $L$ with the zero
polynomial as witness bound, so only the empty witness is allowed.

Together with the fact that this verifier has polynomial declared time whenever $f$ does, this is
the declared-time form of $\mathrm{P} \subseteq \mathrm{NP}$ for named algorithms. -/
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

/-- **Declared-time many-one reduction is reflexive.** For every decision problem $L$, the timed
identity function, which returns its input with declared time $0$, is a declared-time many-one
reduction from $L$ to $L$. -/
theorem declaredPolyManyOneRedVia_refl (L : DecisionProblem) :
    DeclaredPolyManyOneRedVia (fun x => pure x) L L :=
  ⟨⟨Polynomial.X, fun x => by simp⟩, fun x => by simp⟩

/-- **Declared-time many-one reductions compose.** Let $L_1$, $L_2$ and $L_3$ be decision problems.
If $f_1$ is a declared-time many-one reduction from $L_1$ to $L_2$ and $f_2$ is a declared-time
many-one reduction from $L_2$ to $L_3$, then the timed function that on input $x$ returns
$f_2(f_1(x))$, with declared time the declared time of $f_1$ on $x$ plus that of $f_2$ on
$f_1(x)$, is a declared-time many-one reduction from $L_1$ to $L_3$.

If $p_1$ and $p_2$ bound the declared times and output lengths of $f_1$ and $f_2$, then
$p_1 + p_2 \circ p_1$ bounds those of the composite. -/
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

/-- **Declared polynomial time is preserved under precomposition with a reduction.** Let $L_1$ and
$L_2$ be decision problems, let $f$ be a declared-time many-one reduction from $L_1$ to $L_2$, and
let $g$ be a timed function from lists of Booleans to Booleans that decides in declared polynomial
time. Then the timed function that on input $x$ returns $g(f(x))$, with declared time the declared
time of $f$ on $x$ plus that of $g$ on $f(x)$, decides in declared polynomial time.

If $p_f$ bounds the declared time and output length of $f$ and $p_g$ bounds the declared time of
$g$, then $p_f + p_g \circ p_f$ bounds the declared time of the composite. -/
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

/-- **A declared-time reduction followed by a decider for the target decides the source.** Let
$L_1$ and $L_2$ be decision problems, let $f$ be a declared-time many-one reduction from $L_1$ to
$L_2$, and let $g$ be a timed function from lists of Booleans to Booleans whose output on every
list $y$ is $L_2(y)$. Then for every list $x$ of Booleans, the timed function that runs $f$ on $x$
and then $g$ on its output returns $L_1(x)$.

Together with the preservation of declared polynomial time under such compositions, this is the
declared-time form of closure under reductions; no membership in the class P is claimed. -/
theorem decides_comp_reduction
    {f : List Bool → TimeM Nat (List Bool)} {g : List Bool → TimeM Nat Bool}
    {L₁ L₂ : DecisionProblem} (hred : DeclaredPolyManyOneRedVia f L₁ L₂)
    (hdec : ∀ x, (g x).ret = L₂ x) (x : List Bool) :
    ((fun x => f x >>= g) x).ret = L₁ x := by
  simp only [TimeM.ret_bind]
  rw [hdec, ← hred.2 x]

/-- **Pulling a verifier back along a declared reduction.** Let $L_1$ and $L_2$ be decision
problems, let $f$ be a declared polynomial-time many-one reduction from $L_1$ to $L_2$, and let
$V$ be a verifier with polynomial declared time that verifies $L_2$ with witness bound $p$. Let
$V'$ be the verifier that on input $x$ and witness $w$ first runs $f$ on $x$, obtaining $y$, then
runs $V$ on $(y, w)$ and accepts when $V$ accepts and $|w| \le p(|y|)$; its declared time is the
declared time of $f(x)$ plus that of $V(y, w)$. Then $V'$ has polynomial declared time, and there
is a polynomial $p'$ with natural coefficients such that $V'$ verifies $L_1$ with witness bound
$p'$.

The proof takes $p' = p \circ r$ and the time bound $r(n) + q(r(n) + n)$ with $n = |x| + |w|$,
where $r$ bounds the declared time and output length of $f$ and $q$ bounds the declared time of
$V$. -/
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

/-- **A timed decider with polynomial-time output function gives membership in P.** Let $L$ be
a decision problem and let $f$ assign to each bit string $x$ a timed computation, that is, a
Boolean return value together with a declared time in $\mathbb{N}$, whose return value equals
$L(x)$ for every $x$. If the function sending $x$ to the return value of $f(x)$ is
polynomial-time computable, then $L$ belongs to the class P.

The polynomial-time hypothesis must be proved for the specific decider: it does not follow from a
polynomial bound on the declared times, which are trusted annotations, since every decision
problem has a decider of declared time zero. -/
theorem mem_P_of_decides {f : List Bool → TimeM Nat Bool}
    {L : DecisionProblem} (hdec : ∀ x, (f x).ret = L x)
    (h : MetaMathlibExt.ComplexityTheory.IsPolyTime fun x => (f x).ret) :
    L ∈ MetaMathlibExt.ComplexityTheory.P := by
  have hfun : (fun x => (f x).ret) = L := funext hdec
  rw [hfun] at h
  exact h

/-- **A timed verifier with polynomial-time output function puts its language in NP.** Let $L$ be
a decision problem, $p$ a polynomial with natural-number coefficients, and $V$ a timed function
from pairs of lists of Booleans to Booleans that verifies $L$ with witness bound $p$. If the
function sending $(x, w)$ to the output of $V$ on $(x, w)$ is polynomial-time computable by a
Turing machine for the canonical bitstring encodings, then $L$ is in NP.

The polynomial-time hypothesis must be proved separately for $V$; it does not follow from any
bound on the declared time of $V$. -/
theorem mem_NP_of_verifies {V : List Bool × List Bool → TimeM Nat Bool}
    {L : DecisionProblem} {p : Polynomial ℕ} (hver : Verifies V L p)
    (h : MetaMathlibExt.ComplexityTheory.IsPolyTime fun xw => (V xw).ret) :
    L ∈ MetaMathlibExt.ComplexityTheory.NP :=
  ⟨p, fun xw => (V xw).ret, h, hver⟩

/-- **From declared-time to polynomial-time many-one reductions.** Let $L_1$ and $L_2$ be decision
problems and let $f$ be a declared-time many-one reduction from $L_1$ to $L_2$. If the function
sending $x$ to the output of $f$ on $x$ is polynomial-time computable by a Turing machine for the
canonical bitstring encodings, then $L_1$ reduces to $L_2$ by a polynomial-time many-one
reduction.

The polynomial-time hypothesis must be proved separately for $f$; it does not follow from the
declared-time bound. -/
theorem cookLevinPolyManyOneRed_of_declared
    {f : List Bool → TimeM Nat (List Bool)} {L₁ L₂ : DecisionProblem}
    (hred : DeclaredPolyManyOneRedVia f L₁ L₂)
    (h : MetaMathlibExt.ComplexityTheory.IsPolyTime fun x => (f x).ret) :
    Cslib.CookLevin.PolyManyOneRed L₁ L₂ :=
  ⟨fun x => (f x).ret, h, hred.2⟩

end Cslib.TimeMComplexity
