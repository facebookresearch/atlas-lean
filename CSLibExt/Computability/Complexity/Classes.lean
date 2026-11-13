/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared complexity-class definitions for the key-theorems batch

Definitions only: the canonical `MetaMathlibExt.ComplexityTheory.P`/`NP`/`coNP`
classes, the CSLib multi-tape `DTIME`/`DSPACE` classes, and the standard
verifier / counting / circuit characterizations of the classes the
key-theorems statements need. Each definition is the textbook one, with
the variant recorded in its docstring:

* `PSPACE`, `EXP`, `EXPSPACE`, `LogSpace` are the CSLib multi-tape classes,
  bridged to `DecisionProblem` by `langOf`.
* `NTIME`, `NSPACE` are nondeterministic multi-tape classes, with acceptance
  by an accepting computation path.
* `BPP`, `PP`, `AM`, `IP`, `PCP` are verifier / counting definitions over
  `Fin n → Bool` random strings, counted with `Set.ncard` (no decidability
  needed).
* `RP`, `coRP`, `ZPP`, `MA` are the same style of verifier / counting
  definitions: `RP` has one-sided error (`≥ 1/2` on yes-instances, `0` on
  no-instances), `coRP` is the complement class, `ZPP = RP ∩ coRP`
  (Arora-Barak's definition), and `MA` is Merlin-first Arthur-Merlin.
* `PH` (`SigmaK`/`PiK`) is the polynomially bounded alternating-quantifier
  definition, with `AltQuant` recursing on the number of quantifier blocks
  remaining (outermost block `∃` for `SigmaK`, `∀` for `PiK`).
* `#P` (`SharpP`) counts witnesses of one fixed polynomial length.
* Oracle classes use `evalOracle`: the oracle machine is modeled as
  polynomial-time next-query / final-decision functions with a fixed
  polynomial number of adaptive queries (dummy queries simulate early
  halting). This is equivalent to the standard oracle-TM definition.
* Circuits are flat gate lists (`ACGate`): gate `j` may only reference
  earlier gates, so depth and evaluation are folds. `AC0` forbids `mod`
  gates; `AC0Mod m` allows only `mod` gates of modulus `m`; `ACC0` is the
  union over fixed `m` of `AC0Mod m`. A `mod m` gate outputs `true` iff the
  number of true inputs is `≡ 0 (mod m)` (`m = 0` is defined as `false`).
* `NC^k` (`NCK`) is log-space uniform circuits of polynomial size and
  depth `O(log^k n)`: uniformity is a log-space computable description
  function from the unary input `replicate n true` to the bit-encoding of
  the serial circuit, `NC` is the union over `k`.
* Quantum circuits are 2-local unitary gates with rational entries
  (`QGate`, canonical in this file and reused by the Local Hamiltonian
  `QMA` file):
  states are `Fin (2 ^ N) → ℂ` vectors, `applyGate`/`applyCircuit` evolve
  them, `acceptProb` is the Born-rule probability that qubit `0` measures
  `1`. `BQP` is polynomial-size uniform quantum circuits with bounded error.
* Optimization problems (`OptProblem`) are value / feasibility / bound
  bundles; `IsNPO` is the separate computational-content predicate
  (poly-time feasibility and poly-time objective encoding, as in the
  `MAXSNP` file's `NPOProblem`), and `APX`, `PTAS`, `FPTAS` all require it,
  sharing one call convention (the algorithm takes `(instance, unary
  precision tape)`) so that the inclusions `FPTAS ⊆ PTAS ⊆ APX` are direct.
* One-way functions (`IsOneWayFunction`) are polynomially balanced families
  with a uniform polynomial-time evaluator that no uniform polynomial-time
  probabilistic inverter (receiving `(n, output, coins)`) inverts with
  non-negligible probability; one-way permutations
  (`IsOneWayPermutation`) add injectivity and length preservation.

Sources for the definitions (authoritative references):

* J. Hartmanis and R. E. Stearns, "On the computational complexity of
  algorithms", Transactions of the AMS 117 (1965), 285-306 (time hierarchy,
  `DTIME`).
* R. W. Stearns, J. Hartmanis, and P. M. Lewis II, "Hierarchies of memory
  limited computations", Proceedings of the Sixth Annual Symposium on
  Switching Circuit Theory and Logical Design (1965), 179-190 (space
  hierarchy, `DSPACE`).
* S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009
  (`P`, `NP`, `coNP`, `PH`, `BPP`, `PP`, `P/poly`, `#P`, `AM`, `IP`, `PCP`,
  circuit classes, oracle classes, `RP`, `coRP`, `ZPP`, `MA`, `NC`, `BQP`,
  `APX`, `PTAS`, `FPTAS`).
* C. H. Papadimitriou, Computational Complexity, 1994 (`L`, `NL`, `PSPACE`,
  `EXP`, `NEXP`, oracle classes).
* M. Sipser, Introduction to the Theory of Computation, 3rd ed., 2013
  (`P`, `NP`, `PSPACE`, `L`, `NL`, Savitch, `IP`, `PCP`, `RP`, `coRP`, `ZPP`,
  `NC`).
* C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation, and
  complexity classes", Journal of Computer and System Sciences 43 (1991),
  425-440 (`APX`, `PTAS`, `FPTAS`, `MAXSNP`).
* O. Goldreich, Foundations of Cryptography, Vol. 1, Cambridge University
  Press, 2001 (one-way functions, one-way permutations, negligible functions).
* M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information,
  Cambridge University Press, 2000 (`BQP`, quantum circuits, Born rule);
  A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
  Computation, American Mathematical Society, 2002 (2-local gates).
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Nat.Log
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Machines.Turing.MultiTape.TimeSpace
public import Cslib.Computability.Machines.Turing.MultiTape.Nondeterministic
public import Cslib.Computability.Machines.Turing.MultiTape.Space

@[expose] public section

namespace Cslib.Complexity.Classes

open MetaMathlibExt.ComplexityTheory

/-! ### Languages and the multi-tape bridge -/

/-- **Language of a decision problem.** The language of a decision problem $L$ is the set of
bitstrings $x$ with $L(x) = \mathrm{true}$. -/
def langOf (L : DecisionProblem) : Set (List Bool) := {x | L x = true}

/-- **Polynomial space for decision problems.** The class PSPACE of decision problems consists of
the decision problems $L$ whose language $\{x : L(x) = \mathrm{true}\}$ lies in the multi-tape
class PSPACE, that is, is decided by a multi-tape Turing machine that halts on every input and
uses space $O(n^d)$ for some natural number $d$. -/
def PSPACE : DecisionComplexityClass :=
  {L | langOf L ∈ Cslib.Turing.MultiTapeTM.Classes.PSPACE}

/-- **The class EXP.** EXP, deterministic exponential time, is the class of decision problems
$L$ for which there is a natural number $d$ such that the language of $L$, the set of bitstrings
$x$ with $L(x)$ true, belongs to $\mathrm{DTIME}(2^{n^d})$: it is decided by a multi-tape Turing
machine over the binary alphabet with finitely many states in time at most $c_1 2^{n^d} + c_2$
on inputs of length $n$, for some natural numbers $c_1$ and $c_2$. -/
def EXP : DecisionComplexityClass :=
  {L | ∃ d, langOf L ∈ Cslib.Turing.MultiTapeTM.DTIME (fun n => 2 ^ (n ^ d))}

/-- **The class EXPSPACE.** EXPSPACE, deterministic exponential space, is the class of
decision problems $L$ for which there is a natural number $d$ such that the language of $L$, the
set of bitstrings $x$ with $L(x)$ true, belongs to $\mathrm{DSPACE}(2^{n^d})$: it is decided by a
multi-tape Turing machine over the binary alphabet with finitely many states that halts on every
input and visits at most $c_1 2^{n^d} + c_2$ work-tape cells on inputs of length $n$, for some
natural numbers $c_1$ and $c_2$. -/
def EXPSPACE : DecisionComplexityClass :=
  {L | ∃ d, langOf L ∈ Cslib.Turing.MultiTapeTM.DSPACE (fun n => 2 ^ (n ^ d))}

/-- **The class E.** E is the class of decision problems $L$ for which there is a natural
number $c$ such that the language of $L$, the set of bitstrings $x$ with $L(x)$ true, belongs to
$\mathrm{DTIME}(2^{cn})$: it is decided by a multi-tape Turing machine over the binary alphabet
with finitely many states in time at most $c_1 2^{cn} + c_2$ on inputs of length $n$, for some
natural numbers $c_1$ and $c_2$. -/
def E : DecisionComplexityClass :=
  {L | ∃ c, langOf L ∈ Cslib.Turing.MultiTapeTM.DTIME (fun n => 2 ^ (c * n))}

/-- **Deterministic logarithmic space.** The class $\mathsf{L}$ consists of the decision problems
$L$ for which there is a constant $c \in \mathbb{N}$ such that the language of $L$ lies in
$\mathrm{DSPACE}(s)$ for $s(n) = c \lfloor \log_2(n + 1) \rfloor + c$, the class of languages
decided by a multi-tape Turing machine with binary alphabet and finitely many states, within
some time bound, visiting at most $c_1 s(n) + c_2$ work-tape cells on inputs of length $n$ for
some constants $c_1$ and $c_2$. -/
def LogSpace : DecisionComplexityClass :=
  {L | ∃ c, langOf L ∈
    Cslib.Turing.MultiTapeTM.DSPACE (fun n => c * Nat.log 2 (n + 1) + c)}

/-- **Log-space computable functions.** A function $f$ from bitstrings to bitstrings is
log-space computable when there are a constant $c \in \mathbb{N}$ and a time bound
$t : \mathbb{N} \to \mathbb{N}$ such that some multi-tape Turing machine with binary alphabet and
finitely many states, on every bitstring input $x$, halts with output $f(x)$ within $t(|x|)$
steps and visits at most $c \lfloor \log_2(|x| + 1) \rfloor + c$ work-tape cells in total. -/
def LogSpaceComputable (f : List Bool → List Bool) : Prop :=
  ∃ c, ∃ t : ℕ → ℕ,
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength f
      ⟨id, Function.injective_id⟩ ⟨id, Function.injective_id⟩ t
      (fun n => c * Nat.log 2 (n + 1) + c)

/-- **Log-space many-one reductions.** A decision problem $L_1$ is log-space many-one reducible
to a decision problem $L_2$ when there is a log-space computable function $f$ from bitstrings to
bitstrings such that, for every bitstring $x$, $L_1(x)$ is true if and only if $L_2(f(x))$ is
true. -/
def LogSpaceRed (L₁ L₂ : DecisionProblem) : Prop :=
  ∃ f, LogSpaceComputable f ∧ ∀ x, L₁ x ↔ L₂ (f x)

/-! ### Nondeterministic multi-tape classes -/

/-- **Nondeterministic decision.** A nondeterministic multi-tape Turing machine $M$ over the
boolean alphabet decides a set $L$ of bitstrings if, for every bitstring $x$, $x \in L$ if and
only if some computation path of $M$ on $x$ ends in a halted configuration whose output is the
one-element list $[\mathrm{true}]$. -/
def NTMDecides {k : ℕ} {State : Type*} (ntm : Turing.MultiTapeNTM k Bool State)
    (L : Set (List Bool)) : Prop :=
  ∀ x, (x ∈ L ↔ ∃ p : ntm.ComputationPath x, p.last.Halted ∧ p.last.output = [true])

/-- **Nondeterministic decision in bounded time.** Let $M$ be a nondeterministic multi-tape
Turing machine over the boolean alphabet, $t : \mathbb{N} \to \mathbb{N}$ and $L$ a set of
bitstrings. Then $M$ decides $L$ in time $t$ if, for every input $x$, every computation path of
$M$ on $x$ with at least $t(|x|)$ steps ends in a halted configuration, where $|x|$ is the length
of $x$, and for every bitstring $x$, $x \in L$ if and only if some computation path of $M$ on $x$
ends in a halted configuration whose output is the one-element list $[\mathrm{true}]$. -/
def NTMDecidesInTime {k : ℕ} {State : Type*} (ntm : Turing.MultiTapeNTM k Bool State)
    (t : ℕ → ℕ) (L : Set (List Bool)) : Prop :=
  (∀ x, ∀ p : ntm.ComputationPath x, t x.length ≤ p.time → p.last.Halted) ∧
    NTMDecides ntm L

/-- **Nondeterministic decision in bounded space.** Let $M$ be a nondeterministic multi-tape
Turing machine over the boolean alphabet, $s : \mathbb{N} \to \mathbb{N}$ and $L$ a set of
bitstrings. Then $M$ decides $L$ in space $s$ if, for every input $x$, every computation path of
$M$ on $x$ visits at most $s(|x|)$ work-tape cells in total, where $|x|$ is the length of $x$,
and for every bitstring $x$, $x \in L$ if and only if some computation path of $M$ on $x$ ends in
a halted configuration whose output is the one-element list $[\mathrm{true}]$. -/
def NTMDecidesInSpace {k : ℕ} {State : Type*} (ntm : Turing.MultiTapeNTM k Bool State)
    (s : ℕ → ℕ) (L : Set (List Bool)) : Prop :=
  (∀ x, ∀ p : ntm.ComputationPath x, p.space ≤ s x.length) ∧
    NTMDecides ntm L

/-- **Nondeterministic time classes.** For $t : \mathbb{N} \to \mathbb{N}$, $\mathrm{NTIME}(t)$ is
the set of languages $L$ of bitstrings for which there are natural numbers $c_1$, $c_2$, $k$ and a
nondeterministic multi-tape Turing machine $M$ over the boolean alphabet with finitely many states
and $k$ work tapes that decides $L$ in time $c_1 t(n) + c_2$: on every input $x$, every
computation path of $M$ with at least $c_1 t(|x|) + c_2$ steps ends in a halted configuration,
where $|x|$ is the length of $x$, and $x \in L$ if and only if some computation path of $M$ on
$x$ ends in a halted configuration whose output is the one-element list $[\mathrm{true}]$. -/
def NTIME (t : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ c₁ c₂, ∃ k, ∃ (State : Type) (_ : Finite State),
    ∃ ntm : Turing.MultiTapeNTM k Bool State,
    NTMDecidesInTime ntm (fun n => c₁ * t n + c₂) L}

/-- **Nondeterministic space classes.** For $s : \mathbb{N} \to \mathbb{N}$, $\mathrm{NSPACE}(s)$
is the set of languages $L$ of bitstrings for which there are natural numbers $c_1$, $c_2$, $k$
and a nondeterministic multi-tape Turing machine $M$ over the boolean alphabet with finitely many
states and $k$ work tapes that decides $L$ in space $c_1 s(n) + c_2$: on every input $x$, every
computation path of $M$ visits at most $c_1 s(|x|) + c_2$ work-tape cells in total, where $|x|$
is the length of $x$, and $x \in L$ if and only if some computation path of $M$ on $x$ ends in a
halted configuration whose output is the one-element list $[\mathrm{true}]$. -/
def NSPACE (s : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ c₁ c₂, ∃ k, ∃ (State : Type) (_ : Finite State),
    ∃ ntm : Turing.MultiTapeNTM k Bool State,
    NTMDecidesInSpace ntm (fun n => c₁ * s n + c₂) L}

/-- **The complexity class NL.** NL is the set of decision problems $L$ for which there is a
natural number $c$ such that the language of $L$ (the set of bitstrings on which $L$ is true)
belongs to $\mathrm{NSPACE}(s)$ for $s(n) = c \lfloor \log_2 (n + 1) \rfloor + c$, where
$\mathrm{NSPACE}(s)$ is the class of languages decided by a nondeterministic multi-tape Turing
machine with finitely many states in space $c_1 s(n) + c_2$ for some natural numbers $c_1, c_2$. -/
def NL : DecisionComplexityClass :=
  {L | ∃ c, langOf L ∈ NSPACE (fun n => c * Nat.log 2 (n + 1) + c)}

/-- **The complexity class NPSPACE.** NPSPACE is the set of decision problems $L$ for which there
is a natural number $d$ such that the language of $L$ (the set of bitstrings on which $L$ is true)
belongs to $\mathrm{NSPACE}(s)$ for $s(n) = n^d$, where $\mathrm{NSPACE}(s)$ is the class of
languages decided by a nondeterministic multi-tape Turing machine with finitely many states in
space $c_1 s(n) + c_2$ for some natural numbers $c_1, c_2$. -/
def NPSPACE : DecisionComplexityClass :=
  {L | ∃ d, langOf L ∈ NSPACE (fun n => n ^ d)}

/-- **The complexity class NEXP.** NEXP is the set of decision problems $L$ for which there is a
polynomial $p$ with natural-number coefficients such that the language of $L$ (the set of
bitstrings on which $L$ is true) belongs to $\mathrm{NTIME}(t)$ for $t(n) = 2^{p(n)}$, where
$\mathrm{NTIME}(t)$ is the class of languages decided by a nondeterministic multi-tape Turing
machine with finitely many states in time $c_1 t(n) + c_2$ for some natural numbers $c_1, c_2$. -/
def NEXP : DecisionComplexityClass :=
  {L | ∃ p : Polynomial ℕ, langOf L ∈ NTIME (fun n => 2 ^ (p.eval n))}

/-! ### Randomized and counting classes (verifier / counting definitions) -/

/-- **BPP.** The class BPP of bounded-error probabilistic polynomial-time decision problems
consists of the decision problems $L$ for which there are a polynomial $p$ with natural number
coefficients and a polynomial-time computable function $R$ from pairs of bitstrings to booleans
such that, for every bitstring $x$, writing $m = p(|x|)$ and $c_x$ for the number of strings
$r \in \{0,1\}^m$ with $R(x, r)$ true: if $L(x)$ is true then $3 c_x \ge 2 \cdot 2^m$, and if
$L(x)$ is false then $3 c_x \le 2^m$. That is, for a uniformly random $r$, $R(x, r)$ is true with
probability at least $2/3$ on yes-instances and at most $1/3$ on no-instances. -/
def BPP : DecisionComplexityClass :=
  {L | ∃ p : Polynomial ℕ, ∃ R : List Bool × List Bool → Bool, IsPolyTime R ∧
    ∀ x,
      (L x = true →
        3 * Set.ncard {r : Fin (p.eval x.length) → Bool | R (x, List.ofFn r) = true} ≥
          2 * 2 ^ (p.eval x.length)) ∧
      (L x = false →
        3 * Set.ncard {r : Fin (p.eval x.length) → Bool | R (x, List.ofFn r) = true} ≤
          2 ^ (p.eval x.length))}

/-- **Probabilistic polynomial time with unbounded error.** The class PP consists of the decision
problems $L$ for which there are a polynomial $p$ with natural-number coefficients and a
polynomial-time computable function $R$ on pairs of bitstrings such that, for every bitstring $x$
and $r$ uniformly random among the bitstrings of length $p(|x|)$, the probability that $R(x, r)$
is true is greater than $1/2$ if $L(x)$ is true, and at most $1/2$ if $L(x)$ is false. -/
def PP : DecisionComplexityClass :=
  {L | ∃ p : Polynomial ℕ, ∃ R : List Bool × List Bool → Bool, IsPolyTime R ∧
    ∀ x,
      (L x = true →
        2 * Set.ncard {r : Fin (p.eval x.length) → Bool | R (x, List.ofFn r) = true} >
          2 ^ (p.eval x.length)) ∧
      (L x = false →
        2 * Set.ncard {r : Fin (p.eval x.length) → Bool | R (x, List.ofFn r) = true} ≤
          2 ^ (p.eval x.length))}

/-- **Polynomial time with polynomial advice.** The class P/poly consists of the decision problems
$L$ for which there are a polynomial $p$ with natural-number coefficients, bitstrings
$a_0, a_1, a_2, \ldots$ with $|a_n| \le p(n)$ for every $n$, and a polynomial-time computable
function $R$ on pairs of bitstrings such that for every bitstring $x$, $L(x)$ is true if and only
if $R(x, a_{|x|})$ is true. -/
def PPoly : DecisionComplexityClass :=
  {L | ∃ p : Polynomial ℕ, ∃ advice : ℕ → List Bool,
    (∀ n, (advice n).length ≤ p.eval n) ∧
    ∃ R : List Bool × List Bool → Bool, IsPolyTime R ∧
    ∀ x, L x ↔ R (x, advice x.length) = true}

/-- **The counting class $\#P$.** A function $f$ from bitstrings to natural numbers is in
$\#P$ when there are a polynomial $p$ with natural-number coefficients and a
polynomial-time computable Boolean function $R$ on pairs of bitstrings such that for every
bitstring $x$, $f(x)$ is the number of bitstrings $w$ of length exactly $p(|x|)$ for which
$R(x, w)$ is true. -/
def SharpP : Set (List Bool → ℕ) :=
  {f | ∃ p : Polynomial ℕ, ∃ R : List Bool × List Bool → Bool, IsPolyTime R ∧
    ∀ x, f x = Set.ncard
      {w : Fin (p.eval x.length) → Bool | R (x, List.ofFn w) = true}}

/-! ### Oracle computations -/

/-- **Evaluation of an oracle machine with adaptive queries.** Let $\alpha$ be a type of
oracle answers and $\beta$ a type of outputs, and call a list of pairs of a bitstring and an
element of $\alpha$ a history. Fix a length cap $c \in \mathbb{N}$, a next-query function $N$
sending an input bitstring and a history to a bitstring, a decision function $F$ sending an
input bitstring and a history to an element of $\beta$, an oracle $O$ from bitstrings to
$\alpha$ and an input bitstring $x$. For a number $f \in \mathbb{N}$ of remaining queries and a
history $h$, the evaluation $E_f(h)$ is defined by recursion on $f$: $E_0(h) = F(x, h)$, and for
$E_{f+1}(h)$ let $q = N(x, h)$; if $q$ has length at most $c$, then $E_{f+1}(h) = E_f(h')$,
where $h'$ is $h$ with the pair $(q, O(q))$ appended at the end, and otherwise
$E_{f+1}(h) = F(x, h)$.

Dummy queries simulate early halting, so a fixed number of queries is without loss of
generality. At use sites the cap is polynomial in the length of $x$, so polynomial running time
of $N$ and $F$ on each call gives polynomial total running time in the length of $x$. -/
def evalOracle {α β : Type} (cap : ℕ)
    (nextQ : List Bool × List (List Bool × α) → List Bool)
    (final : List Bool × List (List Bool × α) → β)
    (oracle : List Bool → α) (x : List Bool) (fuel : ℕ)
    (hist : List (List Bool × α)) : β :=
  match fuel with
  | 0 => final (x, hist)
  | fuel + 1 =>
    let q := nextQ (x, hist)
    if q.length ≤ cap then
      evalOracle cap nextQ final oracle x fuel
        (hist ++ [(q, oracle q)])
    else final (x, hist)

/-- **Polynomial time with an oracle.** For a Boolean oracle $O$ on bitstrings, the class
$\mathsf{P}^O$ consists of the decision problems $L$ for which there are polynomials $p$ and $q$
and polynomial-time functions $\mathrm{next}$ and $\mathrm{final}$ such that, for every
bitstring $x$, $L(x)$ is true exactly when the following oracle machine outputs true on $x$.
Starting from the empty history $h$, it runs $p(|x|)$ rounds; in each round it computes the
query $y = \mathrm{next}(x, h)$ from $x$ and the history $h$ of queries and answers so far,
and if $|y| \le q(|x|)$ it appends $(y, O(y))$ to $h$, while otherwise it skips all remaining
rounds. Finally it outputs $\mathrm{final}(x, h)$. -/
def PWithOracle (O : List Bool → Bool) : DecisionComplexityClass :=
  {L | ∃ p q : Polynomial ℕ,
    ∃ nextQ : List Bool × List (List Bool × Bool) → List Bool,
    ∃ final : List Bool × List (List Bool × Bool) → Bool,
    IsPolyTime nextQ ∧ IsPolyTime final ∧
    ∀ x, L x ↔
      evalOracle (q.eval x.length) nextQ final O x (p.eval x.length) [] = true}

/-- **NP relative to an oracle.** Let $O$ be a function from bitstrings to booleans. The class
$\mathrm{NP}^O$ is the set of decision problems $L$ for which there are polynomials $p$ and $q$
with natural-number coefficients and polynomial-time computable functions $\mathrm{nextQ}$ and
$\mathrm{final}$, each taking a bitstring and a list of query/answer pairs, such that for every
bitstring $x$, $L(x)$ is true if and only if there is a bitstring $w$ of length at most $p(|x|)$,
where $|x|$ is the length of $x$, for which the oracle computation that chooses queries with
$\mathrm{nextQ}$ and decides with $\mathrm{final}$, run with oracle $O$, query-length cap $q(|x|)$
and $p(|x|)$ adaptive queries on the bitstring encoding of the pair $(x, w)$ from the empty
history, returns true. -/
def NPWithOracle (O : List Bool → Bool) : DecisionComplexityClass :=
  {L | ∃ p q : Polynomial ℕ,
    ∃ nextQ : List Bool × List (List Bool × Bool) → List Bool,
    ∃ final : List Bool × List (List Bool × Bool) → Bool,
    IsPolyTime nextQ ∧ IsPolyTime final ∧
    ∀ x, L x ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧
      evalOracle (q.eval x.length) nextQ final O (MetaMathlibExt.BitstringEncoding.bitEncode (x, w))
        (p.eval x.length) [] = true}

/-- **Polynomial time with a #P oracle.** The class $\mathsf{P}^{\#\mathsf{P}}$ consists of the
decision problems $L$ for which there are a function $f$ in $\#\mathsf{P}$, polynomials $p$ and
$q$, and polynomial-time functions $\mathrm{next}$ and $\mathrm{final}$ such that, for every
bitstring $x$, $L(x)$ is true exactly when the following oracle machine outputs true on $x$.
Starting from the empty history $h$, it runs $p(|x|)$ rounds; in each round it computes the
query $y = \mathrm{next}(x, h)$ from $x$ and the history $h$ of queries and their natural-number
answers so far, and if $|y| \le q(|x|)$ it appends $(y, f(y))$ to $h$, while otherwise it skips
all remaining rounds. Finally it outputs $\mathrm{final}(x, h)$. -/
def PWithSharpP : DecisionComplexityClass :=
  {L | ∃ f ∈ SharpP, ∃ p q : Polynomial ℕ,
    ∃ nextQ : List Bool × List (List Bool × ℕ) → List Bool,
    ∃ final : List Bool × List (List Bool × ℕ) → Bool,
    IsPolyTime nextQ ∧ IsPolyTime final ∧
    ∀ x, L x ↔
      evalOracle (q.eval x.length) nextQ final f x (p.eval x.length) [] = true}

/-- **$\#P$-complete functions.** A function $f$ from bitstrings to natural numbers is
$\#P$-complete when $f$ is in $\#P$ and every function $g$ in $\#P$ is computed from $f$ by a
polynomial-time oracle machine. That is, there are polynomials $p$ and $q$ with natural-number
coefficients and polynomial-time computable functions choosing the next query and the final
natural-number answer from the input and the history of queries and oracle answers, such that
for every bitstring $x$ the following outputs $g(x)$: make up to $p(|x|)$ queries to $f$ in
turn, stop early as soon as the next query is longer than $q(|x|)$, and then return the final
answer computed from $x$ and the history. -/
def SharpPComplete (f : List Bool → ℕ) : Prop :=
  f ∈ SharpP ∧ ∀ g ∈ SharpP, ∃ p q : Polynomial ℕ,
    ∃ nextQ : List Bool × List (List Bool × ℕ) → List Bool,
    ∃ final : List Bool × List (List Bool × ℕ) → ℕ,
    IsPolyTime nextQ ∧ IsPolyTime final ∧
    ∀ x, g x = evalOracle (q.eval x.length) nextQ final f x (p.eval x.length) []

/-! ### The polynomial hierarchy -/

/-- **Alternating bounded quantifiers.** Let $b : \mathbb{N} \to \mathbb{N}$ be a length bound,
$k$ a natural number, $R$ a Boolean function of a bitstring and a list of bitstrings, and $x$ a
bitstring. The statement with $k$ blocks, beginning with $\exists$ when the given flag is true and
with $\forall$ when it is false, is
$$Q_1 w_1 \, Q_2 w_2 \cdots Q_k w_k \; R(x, [w_1, \dots, w_k]) = \mathrm{true},$$
where the quantifiers $Q_1, \dots, Q_k$ alternate between $\exists$ and $\forall$ and every $w_i$
ranges over the bitstrings of length at most $b(|x|)$. For $k = 0$ it is
$R(x, []) = \mathrm{true}$. -/
def AltQuant (bound : ℕ → ℕ) : ℕ → Bool →
    (List Bool × List (List Bool) → Bool) → List Bool → Prop
  | 0, _, R, x => R (x, []) = true
  | k + 1, true, R, x =>
    ∃ w, w.length ≤ bound x.length ∧
      AltQuant bound k false (fun p => R (p.1, w :: p.2)) x
  | k + 1, false, R, x =>
    ∀ w, w.length ≤ bound x.length →
      AltQuant bound k true (fun p => R (p.1, w :: p.2)) x

/-- **The class $\Sigma_k^p$.** For a natural number $k$, a decision problem $L$ is in
$\Sigma_k^p$ when there are a polynomial $p$ with natural-number coefficients and a
polynomial-time computable Boolean function $R$ of a bitstring and a list of bitstrings such
that for every bitstring $x$, $L(x)$ is true if and only if
$Q_1 w_1\, Q_2 w_2 \cdots Q_k w_k$ with $R(x, [w_1, \dots, w_k])$ true, where $Q_i$ is $\exists$
for odd $i$ and $\forall$ for even $i$, and each $w_i$ ranges over bitstrings of length at
most $p(|x|)$. For $k = 0$ the condition is that $R(x, [\,])$ is true. -/
def SigmaK (k : ℕ) : DecisionComplexityClass :=
  {L | ∃ p : Polynomial ℕ, ∃ R : List Bool × List (List Bool) → Bool, IsPolyTime R ∧
    ∀ x, L x ↔ AltQuant (fun n => p.eval n) k true R x}

/-- **The universal levels of the polynomial hierarchy.** For a natural number $k$, the class
$\Pi_k^p$ consists of the decision problems $L$ for which there are a polynomial $p$ with
natural-number coefficients and a polynomial-time computable function $R$, taking a bitstring and
a list of bitstrings to a boolean, such that for every bitstring $x$, $L(x)$ is true if and only
if

$$
\forall w_1\, \exists w_2\, \forall w_3 \cdots Q_k w_k\; R(x, [w_1, \ldots, w_k]) = \mathrm{true},
$$

where the $k$ quantifiers alternate starting with $\forall$ (so $Q_k$ is $\forall$ for odd $k$
and $\exists$ for even $k$) and each $w_i$ ranges over the bitstrings of length at most
$p(|x|)$. For $k = 0$ the condition is $R(x, []) = \mathrm{true}$. -/
def PiK (k : ℕ) : DecisionComplexityClass :=
  {L | ∃ p : Polynomial ℕ, ∃ R : List Bool × List (List Bool) → Bool, IsPolyTime R ∧
    ∀ x, L x ↔ AltQuant (fun n => p.eval n) k false R x}

/-- **The polynomial hierarchy.** The class PH is the union, over all natural numbers $k$, of the
classes $\Sigma_k^p$ of the polynomial hierarchy. -/
def PH : DecisionComplexityClass := ⋃ k, SigmaK k

/-- **The class $\mathsf{AM}$ (Arthur–Merlin).** A decision problem $L$ on bitstrings is in
$\mathsf{AM}$ when there are polynomials $p$ and $q$ with natural-number coefficients and a
polynomial-time computable Boolean function $R(x, r, w)$ of three bitstrings such that, for every
bitstring $x$, writing $A_x$ for the set of strings $r \in \{0,1\}^{p(|x|)}$ for which some
bitstring $w$ of length at most $q(|x|)$ makes $R(x, r, w)$ true: if $L(x)$ is true then
$3|A_x| \ge 2 \cdot 2^{p(|x|)}$, and if $L(x)$ is false then $3|A_x| \le 2^{p(|x|)}$.

Here $r$ is Arthur's random string and $w$ is Merlin's reply, so for uniformly random $r$ the
acceptance probability is at least $2/3$ on yes-instances and at most $1/3$ on no-instances. -/
def AM : DecisionComplexityClass :=
  {L | ∃ p q : Polynomial ℕ,
    ∃ R : List Bool × List Bool × List Bool → Bool, IsPolyTime R ∧
    ∀ x,
      (L x = true →
        3 * Set.ncard {r : Fin (p.eval x.length) → Bool |
          ∃ w : List Bool, w.length ≤ q.eval x.length ∧
            R (x, List.ofFn r, w) = true} ≥ 2 * 2 ^ (p.eval x.length)) ∧
      (L x = false →
        3 * Set.ncard {r : Fin (p.eval x.length) → Bool |
          ∃ w : List Bool, w.length ≤ q.eval x.length ∧
            R (x, List.ofFn r, w) = true} ≤ 2 ^ (p.eval x.length))}

/-- **The class coAM.** coAM is the class of decision problems $L$ whose complement, the
decision problem that accepts exactly the bitstrings that $L$ rejects, belongs to AM. -/
def coAM : DecisionComplexityClass := {L | Lᶜ ∈ AM}

/-! ### Interactive proofs and PCP -/

/-- **Interactive-proof game.** The game takes a length cap $c$, a verifier message function
$V_{\mathrm{msg}}$, a verifier decision function $V_{\mathrm{dec}}$, a prover $P$ mapping
transcripts (lists of bitstrings) to bitstrings, an input $x$, a coin string $\rho$, a number
$k$ of rounds and a transcript $t$, and returns a Boolean outcome. If $k = 0$, the outcome is
$V_{\mathrm{dec}}(x, \rho, t)$. Otherwise the verifier sends $m = V_{\mathrm{msg}}(x, \rho, t)$,
and the prover replies $a = P(t')$, where $t'$ is $t$ extended by $m$. If both $m$ and $a$ have
length at most $c$, the outcome is that of the game with $k - 1$ rounds and transcript $t$
extended by $m$ and then $a$; otherwise the outcome is false.

The transcript records only verifier messages and prover replies, so the prover never sees the
verifier's coins. At use sites the cap is polynomial in $|x|$, so polynomial time for each
verifier step gives polynomial total time in the original input. -/
def IPGame (cap : ℕ)
    (Vmsg : List Bool × List Bool × List (List Bool) → List Bool)
    (Vdec : List Bool × List Bool × List (List Bool) → Bool)
    (P : List (List Bool) → List Bool) (x coins : List Bool) (rounds : ℕ)
    (transcript : List (List Bool)) : Bool :=
  match rounds with
  | 0 => Vdec (x, coins, transcript)
  | rounds + 1 =>
    let m := Vmsg (x, coins, transcript)
    let reply := P (transcript ++ [m])
    if m.length ≤ cap ∧ reply.length ≤ cap then
      IPGame cap Vmsg Vdec P x coins rounds (transcript ++ [m, reply])
    else false

/-- **The class IP.** A decision problem $L$ is in $\mathsf{IP}$ when there are polynomials $s$,
$r$ and $q$ with natural-number coefficients and polynomial-time functions $V_{\mathrm{msg}}$
(the verifier's message function) and $V_{\mathrm{dec}}$ (its decision function) with the
following property. For a bitstring $x$, a prover $P$ (an arbitrary function from transcripts
to bitstrings) and a coin string $c$, let $G(P, c)$ be the outcome of the interactive-proof game
with message length cap $q(|x|)$, verifier $V_{\mathrm{msg}}$ and $V_{\mathrm{dec}}$, prover
$P$, input $x$, coins $c$, $r(|x|)$ rounds and the empty initial transcript. Then for every
bitstring $x$: if $L(x)$ is true, some prover $P$ makes $G(P, c)$ true for at least $2/3$ of
the coin strings $c \in \{0,1\}^{s(|x|)}$; and if $L(x)$ is false, every prover $P$ makes
$G(P, c)$ true for at most $1/3$ of them. -/
def IP : DecisionComplexityClass :=
  {L | ∃ s r q : Polynomial ℕ,
    ∃ Vmsg : List Bool × List Bool × List (List Bool) → List Bool,
    ∃ Vdec : List Bool × List Bool × List (List Bool) → Bool,
    IsPolyTime Vmsg ∧ IsPolyTime Vdec ∧
    ∀ x,
      (L x = true →
        ∃ P : List (List Bool) → List Bool,
          3 * Set.ncard {coins : Fin (s.eval x.length) → Bool |
            IPGame (q.eval x.length) Vmsg Vdec P x (List.ofFn coins)
              (r.eval x.length) [] = true} ≥
            2 * 2 ^ (s.eval x.length)) ∧
      (L x = false →
        ∀ P : List (List Bool) → List Bool,
          3 * Set.ncard {coins : Fin (s.eval x.length) → Bool |
            IPGame (q.eval x.length) Vmsg Vdec P x (List.ofFn coins)
              (r.eval x.length) [] = true} ≤
            2 ^ (s.eval x.length))}

/-- **Probabilistically checkable proofs.** For functions $r, q : \mathbb{N} \to \mathbb{N}$, the
class $\mathrm{PCP}(r, q)$ consists of the decision problems $L$ for which there are
polynomial-time computable functions $Q$ and $D$ such that $Q(x, \rho)$ is a list of at most
$q(|x|)$ natural numbers for all bitstrings $x$ and $\rho$, and such that for every bitstring $x$
the following holds. For a proof $\pi : \mathbb{N} \to \{\mathrm{true}, \mathrm{false}\}$, let
$\pi(Q(x, \rho))$ be the list of values of $\pi$ at the entries of $Q(x, \rho)$, and let
$P_\pi(x)$ be the probability, over a uniformly random bitstring $\rho$ of length $r(|x|)$, that
$D(x, \rho, \pi(Q(x, \rho)))$ is true. If $L(x)$ is true, then $P_\pi(x) \ge 2/3$ for some proof
$\pi$; if $L(x)$ is false, then $P_\pi(x) \le 1/3$ for every proof $\pi$.

The verifier is non-adaptive: the queried positions depend only on $x$ and $\rho$. -/
def PCP (rbound qbound : ℕ → ℕ) : DecisionComplexityClass :=
  {L | ∃ queries : List Bool × List Bool → List ℕ,
    ∃ decide : List Bool × List Bool × List Bool → Bool,
    IsPolyTime queries ∧ IsPolyTime decide ∧
    (∀ x rand, (queries (x, rand)).length ≤ qbound x.length) ∧
    ∀ x,
      (L x = true →
        ∃ proof : ℕ → Bool,
          3 * Set.ncard {rand : Fin (rbound x.length) → Bool |
            decide (x, List.ofFn rand,
              (queries (x, List.ofFn rand)).map proof) = true} ≥
              2 * 2 ^ (rbound x.length)) ∧
      (L x = false →
        ∀ proof : ℕ → Bool,
          3 * Set.ncard {rand : Fin (rbound x.length) → Bool |
            decide (x, List.ofFn rand,
              (queries (x, List.ofFn rand)).map proof) = true} ≤
              2 ^ (rbound x.length))}

/-! ### Flat Boolean circuits -/

/-- **Gates of a flat Boolean circuit.** A gate of a flat Boolean circuit on $n$ inputs is one of:
an input variable $x_i$ for some $i < n$; a Boolean constant; a negation gate with one predecessor
index $a \in \mathbb{N}$; a conjunction gate or a disjunction gate with a list of predecessor
indices; or a mod gate with a modulus $m \in \mathbb{N}$ and a list of predecessor indices.

Predecessors are referred to by their positions in the circuit; that gate $j$ refers only to
gates before $j$ is a separate well-formedness condition on circuits. -/
inductive ACGate (n : ℕ) where
  | var : Fin n → ACGate n
  | const : Bool → ACGate n
  | notGate : ℕ → ACGate n
  | andGate : List ℕ → ACGate n
  | orGate : List ℕ → ACGate n
  | modGate : ℕ → List ℕ → ACGate n

/-- **Predecessors of a gate.** For a gate $g$ of a flat Boolean circuit on $n$ inputs, this is
the list of gate indices that $g$ reads: the empty list for an input variable or a constant, the
one-element list $[a]$ for the negation of gate $a$, and the argument list $l$ for an and, or or
mod gate with argument list $l$ (the modulus of a mod gate is not included). -/
def gateInputs {n : ℕ} : ACGate n → List ℕ
  | .var _ => []
  | .const _ => []
  | .notGate a => [a]
  | .andGate l => l
  | .orGate l => l
  | .modGate _ l => l

/-- **Well-formed flat circuits.** A flat Boolean circuit on $n$ inputs, given as a list of
gates $(g_0, \dots, g_{m-1})$, is well-formed when every gate references only strictly earlier
gates: for every $j < m$, every gate index $a$ among the inputs of $g_j$ satisfies $a < j$. -/
def WellFormedCircuit {n : ℕ} (C : List (ACGate n)) : Prop :=
  ∀ j (h : j < C.length), ∀ a ∈ gateInputs (C[j]'h), a < j

/-- **Value of a gate.** Let $v$ be a list of Boolean values of earlier gates, where an index
outside $v$ reads as false, and let $\sigma$ assign a Boolean value to each of the $n$ inputs.
Given $v$ and $\sigma$, the value of the input variable $x_i$ is $\sigma(i)$; the value of the
constant $b$ is $b$; the value of the negation of gate $a$ is the negation of $v_a$; the value
of an and gate (or gate) with argument list $l$ is the conjunction (disjunction) of the values
$v_a$ for $a$ in $l$; and the value of a mod gate with modulus $m$ and argument list $l$ is false
if $m = 0$, and otherwise true exactly when the number of entries $a$ of $l$ with $v_a$ true,
counted with repetition, is divisible by $m$. -/
def gateValue {n : ℕ} (vs : List Bool) (assign : Fin n → Bool) : ACGate n → Bool
  | .var i => assign i
  | .const b => b
  | .notGate a => !(vs.getD a false)
  | .andGate l => l.all (fun a => vs.getD a false)
  | .orGate l => l.any (fun a => vs.getD a false)
  | .modGate m l =>
    if m = 0 then false
    else (l.filter (fun a => vs.getD a false)).length % m = 0

/-- **Evaluation of a flat Boolean circuit.** For a circuit on $n$ inputs given as a list of
gates $g_0, \dots, g_{m-1}$ and an assignment $\alpha$ of booleans to the inputs, the list of
gate values is $(v_0, \dots, v_{m-1})$, where $v_j$ is computed from $v_0, \dots, v_{j-1}$, a
reference to a gate $a \ge j$ reading as false: an input gate $i$ has value $\alpha(i)$, a
constant gate has its constant, a negation gate on $a$ has value $\lnot v_a$, an and gate (or
gate) has the conjunction (disjunction) of the values it references, and a mod gate with
modulus $k$ is true if and only if $k \ne 0$ and the number of its references with value true,
counted with multiplicity, is divisible by $k$. -/
def circuitEval {n : ℕ} (C : List (ACGate n)) (assign : Fin n → Bool) : List Bool :=
  C.foldl (fun vs g => vs ++ [gateValue vs assign g]) []

/-- **Encoding a gate as a (kind, references) pair.** A gate of a flat Boolean circuit on $n$
inputs is encoded as a pair of a natural number (its kind) and a list of natural numbers (its
references), the shared encoding used by decoding-based problems such as Circuit Value and
succinct circuits: the input variable $x_i$ is encoded as $(0, [i])$; the constant true as
$(1, [1])$ and the constant false as $(1, [0])$; the negation of gate $a$ as $(2, [a])$; the
conjunction of the gates listed in $r$ as $(3, r)$; and the disjunction of the gates listed in $r$
as $(4, r)$. Mod gates have no encoding of their own: every mod gate is encoded as $(5, [])$.

The serial evaluator reads kind $5$ as false. -/
def acGateToPair {n : ℕ} : ACGate n → ℕ × List ℕ
  | .var i => (0, [i.val])
  | .const b => (1, [if b then 1 else 0])
  | .notGate a => (2, [a])
  | .andGate l => (3, l)
  | .orGate l => (4, l)
  | .modGate _ _ => (5, [])

/-- **Decoding a gate from its (kind, references) pair.** A pair $(k, r)$ of a natural number $k$
and a list $r$ of natural numbers decodes to a gate of a flat Boolean circuit on $n$ inputs as
follows: $(0, [i])$ decodes to the input variable $x_i$ when $i < n$ and to the constant false
when $i \ge n$; $(1, [b])$ decodes to the constant that is true if and only if $b = 1$; $(2, [a])$
decodes to the negation of gate $a$; $(3, r)$ decodes to the conjunction of the gates listed in
$r$; and $(4, r)$ decodes to the disjunction of the gates listed in $r$. Every other pair,
including every pair of kind $5$ (the encoding of a mod gate), decodes to the constant false.

These defaults match the serial evaluator, which reads an unknown kind, and an input variable
with no corresponding input, as false. -/
def acGateOfPair {n : ℕ} : ℕ × List ℕ → ACGate n
  | (0, [i]) => if h : i < n then .var ⟨i, h⟩ else .const false
  | (1, [b]) => .const (b = 1)
  | (2, [a]) => .notGate a
  | (3, l) => .andGate l
  | (4, l) => .orGate l
  | _ => .const false

/-- **Evaluating a serialized gate.** Let $v$ be a list of Boolean values of earlier gates,
let $a$ assign a Boolean to each of the $n$ inputs $0, \dots, n - 1$, and let $(k, \ell)$ be a
serialized gate. Write $v_c$ for entry $c$ of $v$, read as false when $c$ is out of range.
The value of the gate is: $a(i)$ if $(k, \ell) = (0, [i])$ with $i < n$, and false if
$(k, \ell) = (0, [i])$ with $i \ge n$; true exactly when $b = 1$ if $(k, \ell) = (1, [b])$;
the negation of $v_c$ if $(k, \ell) = (2, [c])$; the conjunction of the $v_c$ for $c$ in $\ell$
if $k = 3$; their disjunction if $k = 4$; and false in every other case. -/
def serialGateEval {n : ℕ} (vs : List Bool) (assign : Fin n → Bool)
    (g : ℕ × List ℕ) : Bool :=
  match g with
  | (0, [i]) => if h : i < n then assign ⟨i, h⟩ else false
  | (1, [b]) => b = 1
  | (2, [a]) => !(vs.getD a false)
  | (3, l) => l.all (fun a => vs.getD a false)
  | (4, l) => l.any (fun a => vs.getD a false)
  | _ => false

/-- **Serial gate evaluation agrees with typed gate evaluation.** For every list $v$ of Boolean
values of earlier gates, every assignment of Boolean values to the $n$ inputs and every pair
$g = (k, r)$ of a natural number $k$ (the gate kind) and a list $r$ of natural numbers (its
references), evaluating $g$ with the serial $(\mathrm{kind}, \mathrm{refs})$ gate evaluator
gives the same value as evaluating the gate decoded from $g$ with the gate-value function. -/
theorem gateValue_ofPair {n : ℕ} (vs : List Bool) (assign : Fin n → Bool)
    (g : ℕ × List ℕ) :
    serialGateEval vs assign g = gateValue vs assign (acGateOfPair g) := by
  rcases g with ⟨kind, refs⟩
  cases kind with
  | zero => cases refs with
    | nil => rfl
    | cons i rest => cases rest with
      | nil =>
        by_cases hi : i < n <;> simp [serialGateEval, acGateOfPair, gateValue, hi]
      | cons _ _ => rfl
  | succ k => cases k with
    | zero => cases refs with
      | nil => rfl
      | cons b rest => cases rest with
        | nil => rfl
        | cons _ _ => rfl
    | succ k2 => cases k2 with
      | zero => cases refs with
        | nil => rfl
        | cons a rest => cases rest with
          | nil => rfl
          | cons _ _ => rfl
      | succ k3 => cases k3 with
        | zero => rfl
        | succ k4 => cases k4 with
          | zero => rfl
          | succ _ => rfl

/-- **Depth of a gate.** Let $d$ be the list of depths of the earlier gates of a flat Boolean
circuit on $n$ inputs, and for a gate index $a$ let $d_a$ be the entry of $d$ at (zero-based)
position $a$, or $0$ when $a$ is not a position of $d$. The depth of an input-variable gate or a
constant gate is $0$; the depth of a negation, AND, OR or modular gate is one more than the
maximum of $d_a$ over the gates $a$ it references, where the maximum over no gates is $0$. -/
def gateDepthOf (ds : List ℕ) {n : ℕ} : ACGate n → ℕ
  | .var _ => 0
  | .const _ => 0
  | .notGate a => ds.getD a 0 + 1
  | .andGate l => List.foldr max 0 (l.map (fun a => ds.getD a 0)) + 1
  | .orGate l => List.foldr max 0 (l.map (fun a => ds.getD a 0)) + 1
  | .modGate _ l => List.foldr max 0 (l.map (fun a => ds.getD a 0)) + 1

/-- **Gate depths of a flat Boolean circuit.** For a circuit given as a list of gates
$g_0, \dots, g_{m-1}$, the list of gate depths is $(d_0, \dots, d_{m-1})$, where $d_j = 0$ if
$g_j$ is an input or constant gate, and otherwise $d_j$ is one more than the maximum of the
depths $d_a$ of the gates $a$ that $g_j$ references (the maximum over no references is $0$),
a reference $a \ge j$ counting as depth $0$. -/
def circuitDepths {n : ℕ} (C : List (ACGate n)) : List ℕ :=
  C.foldl (fun ds g => ds ++ [gateDepthOf ds g]) []

/-- **Depth of a flat Boolean circuit.** The depth of a circuit, given as a list of gates, is
the maximum of the depths of its gates, and $0$ for the empty circuit. Input and constant gates
have depth $0$; a negation, and, or or mod gate has depth one more than the maximum depth of the
gates it references (the maximum over no references is $0$), where a reference to a gate that
does not come earlier in the list counts as depth $0$. -/
def circuitDepth {n : ℕ} (C : List (ACGate n)) : ℕ :=
  List.foldr max 0 (circuitDepths C)

/-- **Circuits without mod gates.** A flat Boolean circuit $C$ on $n$ inputs is mod-free when
none of its gates is a mod gate. -/
def IsModFree {n : ℕ} (C : List (ACGate n)) : Prop :=
  ∀ g ∈ C, match g with
    | .modGate _ _ => False
    | _ => True

/-- **Circuits whose modular gates have a fixed modulus.** For a natural number $m$, a flat
Boolean circuit on $n$ inputs satisfies the modulus-$m$ condition when every $\mathrm{mod}$
gate in it has modulus exactly $m$; gates of the other kinds are unrestricted. -/
def ModOnly {n : ℕ} (m : ℕ) (C : List (ACGate n)) : Prop :=
  ∀ g ∈ C, match g with
    | .modGate m' _ => m' = m
    | _ => True

/-- **Monotone circuits.** A flat circuit $C$ on $n$ input variables, given as a list of gates, is
monotone when every gate of $C$ is an input variable, an AND gate or an OR gate. Constant, NOT
and mod gates are not allowed. -/
def IsMonotoneCircuit {n : ℕ} (C : List (ACGate n)) : Prop :=
  ∀ g ∈ C, match g with
    | .var _ => True
    | .andGate _ => True
    | .orGate _ => True
    | _ => False

/-- **The class $\mathsf{AC}^0$.** A decision problem $L$ on bitstrings is in $\mathsf{AC}^0$ when
there are a depth bound $d$, a polynomial $p$ with natural-number coefficients and, for every
$n$, a flat Boolean circuit $C_n$ on $n$ inputs such that for every $n$: every gate of $C_n$
refers only to earlier gates; $C_n$ has no mod gates; $C_n$ has at most $p(n)$ gates and depth at
most $d$; and for every bitstring $x$ of length $n$, $L(x)$ is true if and only if $C_n$ has a
last gate and the value of that gate on input $x$ is true.

The and and or gates have unbounded fan-in, and the family $(C_n)$ need not be uniform. -/
def AC0 : DecisionComplexityClass :=
  {L | ∃ d, ∃ p : Polynomial ℕ, ∃ C : (n : ℕ) → List (ACGate n),
    ∀ n, WellFormedCircuit (C n) ∧ IsModFree (C n) ∧ (C n).length ≤ p.eval n ∧
      circuitDepth (C n) ≤ d ∧
      ∀ x : List Bool, x.length = n →
        (L x = true ↔
          (circuitEval (C n) (fun i => x.getD (i : ℕ) false)).getLast? = some true)}

/-- **The class $\mathsf{AC}^0[m]$.** For a natural number $m$, a decision problem $L$ on
bitstrings is in $\mathsf{AC}^0[m]$ when there are a depth bound $d$, a polynomial $p$ with
natural-number coefficients and, for every $n$, a flat Boolean circuit $C_n$ on $n$ inputs such
that for every $n$: every gate of $C_n$ refers only to earlier gates; every mod gate of $C_n$ has
modulus $m$; $C_n$ has at most $p(n)$ gates and depth at most $d$; and for every bitstring $x$ of
length $n$, $L(x)$ is true if and only if $C_n$ has a last gate and the value of that gate on
input $x$ is true.

The and and or gates have unbounded fan-in, the family $(C_n)$ need not be uniform, and a circuit
with no mod gates also qualifies. -/
def AC0Mod (m : ℕ) : DecisionComplexityClass :=
  {L | ∃ d, ∃ p : Polynomial ℕ, ∃ C : (n : ℕ) → List (ACGate n),
    ∀ n, WellFormedCircuit (C n) ∧ ModOnly m (C n) ∧ (C n).length ≤ p.eval n ∧
      circuitDepth (C n) ≤ d ∧
      ∀ x : List Bool, x.length = n →
        (L x = true ↔
          (circuitEval (C n) (fun i => x.getD (i : ℕ) false)).getLast? = some true)}

/-- **The class $\mathsf{ACC}^0$.** $\mathsf{ACC}^0$ is the union of the classes
$\mathsf{AC}^0[m]$ over all natural numbers $m$: a decision problem is in $\mathsf{ACC}^0$ when it
is in $\mathsf{AC}^0[m]$ for some $m$. A circuit family witnessing membership uses one fixed
modulus $m$ throughout. -/
def ACC0 : DecisionComplexityClass := ⋃ m, AC0Mod m

/-- **The parity language.** The parity decision problem accepts a bitstring exactly when an odd
number of its entries are true. -/
def parityDec : MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x : List Bool => decide ((x.filter fun b => b).length % 2 = 1)

/-- **The majority language.** The majority language is the decision problem that accepts a
bitstring $x$ exactly when $x$ has more true bits than false bits, that is, when $2k > |x|$,
where $k$ is the number of true bits of $x$ and $|x|$ is its length. -/
def majorityDec : MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x : List Bool => decide (2 * (x.filter fun b => b).length > x.length)

/-! ### One-sided-error randomized classes: `RP`, `coRP`, `ZPP` -/

/-- **The class RP.** A decision problem $L$ is in $\mathsf{RP}$ when there are a polynomial
$p$ with natural-number coefficients and a polynomial-time computable Boolean function $R$
on pairs of bitstrings such that for every bitstring $x$: if $L(x)$ is true, then $R(x, r)$
is true for at least half of the $2^{p(|x|)}$ bitstrings $r$ of length $p(|x|)$; and if
$L(x)$ is false, then $R(x, r)$ is false for every bitstring $r$ of length $p(|x|)$.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach,
2009, Definition 7.2; M. Sipser, Introduction to the Theory of Computation,
3rd ed., 2013, Definition 10.8. -/
def RP : DecisionComplexityClass :=
  {L | ∃ p : Polynomial ℕ, ∃ R : List Bool × List Bool → Bool, IsPolyTime R ∧
    ∀ x,
      (L x = true →
        2 * Set.ncard {r : Fin (p.eval x.length) → Bool | R (x, List.ofFn r) = true} ≥
          2 ^ (p.eval x.length)) ∧
      (L x = false →
        Set.ncard {r : Fin (p.eval x.length) → Bool | R (x, List.ofFn r) = true} = 0)}

/-- **The class coRP.** coRP is the class of decision problems $L$ whose complement, the
decision problem that accepts exactly the bitstrings that $L$ rejects, belongs to RP.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 7.2; M. Sipser, Introduction to the Theory of Computation, 3rd ed.,
2013, Definition 10.8. -/
def coRP : DecisionComplexityClass := {L | Lᶜ ∈ RP}

/-- **Membership in coRP.** A decision problem $L$ belongs to $\mathsf{coRP}$ if and only if its
complement, the decision problem that accepts exactly the bitstrings $L$ rejects, belongs to
$\mathsf{RP}$.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 7.2. -/
theorem mem_coRP {L : DecisionProblem} : L ∈ coRP ↔ Lᶜ ∈ RP := Iff.rfl

/-- **ZPP.** The class $\mathsf{ZPP}$ (zero-error probabilistic polynomial time) is defined as
the set of decision problems that lie in both $\mathsf{RP}$ and $\mathsf{coRP}$, that is,
$\mathsf{ZPP} = \mathsf{RP} \cap \mathsf{coRP}$.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 7.2 (where `ZPP` is defined as this intersection); M. Sipser,
Introduction to the Theory of Computation, 3rd ed., 2013, Definition 10.8. -/
def ZPP : DecisionComplexityClass := RP ∩ coRP

/-- **ZPP is the intersection of RP and coRP.** The class $\mathsf{ZPP}$ equals
$\mathsf{RP} \cap \mathsf{coRP}$; here this holds by definition.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 7.2. -/
theorem zpp_eq : ZPP = RP ∩ coRP := rfl

/-- **ZPP is contained in RP.** Every decision problem in $\mathsf{ZPP}$ lies in
$\mathsf{RP}$, that is, $\mathsf{ZPP} \subseteq \mathsf{RP}$.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 7.2. -/
theorem zpp_subset_rp : ZPP ⊆ RP := Set.inter_subset_left

/-- **ZPP is contained in coRP.** Every decision problem in $\mathsf{ZPP}$ lies in
$\mathsf{coRP}$, that is, $\mathsf{ZPP} \subseteq \mathsf{coRP}$.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 7.2. -/
theorem zpp_subset_corp : ZPP ⊆ coRP := Set.inter_subset_right

/-! ### Merlin-Arthur: `MA` -/

/-- **The class MA (Merlin–Arthur).** A decision problem $L$ is in $\mathsf{MA}$ when there are
polynomials $p$ and $q$ with natural-number coefficients and a polynomial-time computable
predicate $R$ on triples $(x, w, r)$ of bitstrings such that, for every bitstring $x$, with
$N_x(w)$ the number of strings $r$ of length $p(|x|)$ for which $R(x, w, r)$ is true: if $L(x)$
is true, then some $w$ with $|w| \le q(|x|)$ satisfies $3 N_x(w) \ge 2 \cdot 2^{p(|x|)}$; and if
$L(x)$ is false, then every $w$ with $|w| \le q(|x|)$ satisfies $3 N_x(w) \le 2^{p(|x|)}$.

So Merlin sends a witness $w$ first and Arthur then flips $p(|x|)$ coins $r$: Arthur accepts
with probability at least $2/3$ for some $w$ on yes-instances, and with probability at most
$1/3$ for every $w$ on no-instances. In the class AM the random string comes before the
witness.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach,
2009, Definition 8.1; L. Babai, "Trading group theory for randomness",
Proceedings of the Seventeenth Annual ACM Symposium on Theory of Computing
(STOC 1985), 421-429. -/
def MA : DecisionComplexityClass :=
  {L | ∃ p q : Polynomial ℕ,
    ∃ R : List Bool × List Bool × List Bool → Bool, IsPolyTime R ∧
    ∀ x,
      (L x = true →
        ∃ w : List Bool, w.length ≤ q.eval x.length ∧
          3 * Set.ncard {r : Fin (p.eval x.length) → Bool |
            R (x, w, List.ofFn r) = true} ≥ 2 * 2 ^ (p.eval x.length)) ∧
      (L x = false →
        ∀ w : List Bool, w.length ≤ q.eval x.length →
          3 * Set.ncard {r : Fin (p.eval x.length) → Bool |
            R (x, w, List.ofFn r) = true} ≤ 2 ^ (p.eval x.length))}

/-- **The class coMA.** coMA is the class of decision problems $L$ whose complement, the
decision problem that accepts exactly the bitstrings that $L$ rejects, belongs to MA.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 8.1. -/
def coMA : DecisionComplexityClass := {L | Lᶜ ∈ MA}

/-- **Membership in coMA.** A decision problem $L$ belongs to $\mathsf{coMA}$ if and only if its
complement, the decision problem that accepts exactly the bitstrings $L$ rejects, belongs to
$\mathsf{MA}$.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 8.1. -/
theorem mem_coMA {L : DecisionProblem} : L ∈ coMA ↔ Lᶜ ∈ MA := Iff.rfl

/-! ### `NC`: log-space uniform poly-size polylog-depth circuits -/

/-- **Serial circuits.** A serial circuit is a list of pairs $(k, \ell)$, where $k$ is a
natural number (the gate kind) and $\ell$ is a list of natural numbers (the gate's references).

A flat circuit is serialized gate by gate into this form: kind $0$ is an input variable,
kind $1$ a constant, kind $2$ a negation, kind $3$ a conjunction and kind $4$ a
disjunction, while a modular-counting gate, which has no serial form here, becomes $(5, [\,])$.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Chapter 6 (circuit encodings). -/
abbrev SerialCircuit := List (ℕ × List ℕ)

/-- **Log-space uniform circuit families.** A family $(C_n)_{n \in \mathbb{N}}$ of flat Boolean
circuits, $C_n$ having $n$ inputs, is log-space uniform when there is a log-space computable
function $D$ on bitstrings such that, for every $n$, decoding $D(1^n)$ (where $1^n$ is the string
of $n$ ones) as a list of (gate kind, references) pairs succeeds and returns the serial encoding
of $C_n$, that is, the list of the serial encodings of its gates in order. Since $1^n$ has
length $n$, the description is computed in space $O(\log n)$.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 6.21 (log-space uniformity); M. Sipser, Introduction to the Theory of
Computation, 3rd ed., 2013, Definition 9.20. -/
def UniformCircuitFamily (C : (n : ℕ) → List (ACGate n)) : Prop :=
  ∃ desc : List Bool → List Bool, LogSpaceComputable desc ∧
    ∀ n, MetaMathlibExt.BitstringEncoding.bitDecode
      (desc (List.replicate n true)) = some ((C n).map acGateToPair)

/-- **Circuits of fan-in at most two.** A flat Boolean circuit $C$ on $n$ inputs has fan-in at
most two when every and gate, or gate and mod gate of $C$ has an argument list of length at
most $2$.

Bounded fan-in is what $\mathsf{NC}$ requires: without it, the $\mathsf{NC}^k$ circuit classes
would be the unbounded-fan-in classes $\mathsf{AC}^k$.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 6.21; M. Sipser, Introduction to the Theory of Computation, 3rd ed.,
2013, Definition 9.20. -/
def IsFanInLeTwo {n : ℕ} (C : List (ACGate n)) : Prop :=
  ∀ g ∈ C, match g with
    | .andGate l => l.length ≤ 2
    | .orGate l => l.length ≤ 2
    | .modGate _ l => l.length ≤ 2
    | _ => True

/-- **The class NC^k.** For a natural number $k$, a decision problem $L$ is in $\mathsf{NC}^k$
when there are a constant $c$, a polynomial $p$ with natural number coefficients and a
log-space uniform family of flat Boolean circuits $(C_n)_{n \in \mathbb{N}}$, where $C_n$ has
$n$ inputs, such that for every $n$ the circuit $C_n$ is well formed, has no $\mathrm{mod}$
gates, has at most two inputs at every and gate and every or gate, has at most $p(n)$ gates,
has depth at most $c \cdot (\lfloor \log_2 (n + 1) \rfloor + 1)^k$, and, for every bitstring
$x$ of length $n$, $L$ accepts $x$ exactly when $C_n$ has a last gate and that gate evaluates
to true on input $x$.

So $\mathsf{NC}^k$ consists of the problems decided by log-space uniform circuit families of
polynomial size, fan-in at most $2$ and depth $O(\log^k n)$, and $\mathsf{NC}^0$ is constant
depth. Bounded fan-in is essential: with unbounded fan-in this would be $\mathsf{AC}^k$.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 6.21; M. Sipser, Introduction to the Theory of Computation, 3rd ed.,
2013, Definition 9.20. -/
def NCK (k : ℕ) : DecisionComplexityClass :=
  {L | ∃ c, ∃ p : Polynomial ℕ, ∃ C : (n : ℕ) → List (ACGate n),
    UniformCircuitFamily C ∧
    ∀ n, WellFormedCircuit (C n) ∧ IsModFree (C n) ∧ IsFanInLeTwo (C n) ∧
      (C n).length ≤ p.eval n ∧
      circuitDepth (C n) ≤ c * (Nat.log 2 (n + 1) + 1) ^ k ∧
      ∀ x : List Bool, x.length = n →
        (L x = true ↔
          (circuitEval (C n) (fun i => x.getD (i : ℕ) false)).getLast? = some true)}

/-- **The class NC.** $\mathsf{NC}$ is the complexity class of decision problems that belong to
$\mathsf{NC}^k$ for some natural number $k$, that is, $\mathsf{NC} = \bigcup_{k} \mathsf{NC}^k$.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 6.21; M. Sipser, Introduction to the Theory of Computation, 3rd ed.,
2013, Definition 9.20. -/
def NC : DecisionComplexityClass := ⋃ k, NCK k

/-- **NC is the union of its levels.** The class $\mathsf{NC}$ equals the union
$\bigcup_{k \in \mathbb{N}} \mathsf{NC}^k$ of the classes $\mathsf{NC}^k$ over all natural
numbers $k$; this holds by definition.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 6.21. -/
theorem nc_eq : NC = ⋃ k, NCK k := rfl

/-- **Membership in NC.** A decision problem $L$ belongs to $\mathsf{NC}$ if and only if $L$
belongs to $\mathsf{NC}^k$ for some natural number $k$.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 6.21. -/
theorem mem_nc {L : DecisionProblem} : L ∈ NC ↔ ∃ k, L ∈ NCK k := Set.mem_iUnion

/-- **The NC hierarchy is increasing.** For every natural number $k$, every decision problem in
$\mathsf{NC}^k$ is in $\mathsf{NC}^{k+1}$, that is, $\mathsf{NC}^k \subseteq \mathsf{NC}^{k+1}$.

The depth bound of $\mathsf{NC}^k$, a constant times $(\lfloor \log_2 (n + 1) \rfloor + 1)^k$, is
monotone in $k$ because its base is at least $1$.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 6.21. -/
theorem nck_mono {k : ℕ} : NCK k ⊆ NCK (k + 1) := by
  intro L hL
  obtain ⟨c, p, C, hU, hC⟩ := hL
  refine ⟨c, p, C, hU, fun n => ?_⟩
  obtain ⟨hwf, hmod, hfan, hsize, hdepth, hcorr⟩ := hC n
  refine ⟨hwf, hmod, hfan, hsize, ?_, hcorr⟩
  calc circuitDepth (C n) ≤ c * (Nat.log 2 (n + 1) + 1) ^ k := hdepth
    _ ≤ c * (Nat.log 2 (n + 1) + 1) ^ (k + 1) :=
        Nat.mul_le_mul_left c (Nat.pow_le_pow_right (by omega) (Nat.le_succ k))

/-! ### Quantum circuits and `BQP` -/

/-- **Encoded rational number.** A rational number is encoded as a triple $(s, a, b)$ of a
boolean $s$ and natural numbers $a$ and $b$, read as the sign, the numerator and the
denominator.

Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4 (rational
gate entries). -/
abbrev RatEnc := Bool × ℕ × ℕ

/-- **Rational number of an encoding.** A triple $(s, p, q)$, with $s$ a boolean and $p, q$
natural numbers, encodes the rational number $-p/q$ when $s$ is true and $p/q$ when $s$ is
false; when $q = 0$ the value is $0$, since division by zero gives $0$.

Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4. -/
def toRat (e : RatEnc) : ℚ :=
  (if e.1 then -1 else 1) * (e.2.1 : ℚ) / (e.2.2 : ℚ)

/-- **Complex number of a pair of rational encodings.** A pair $(e_1, e_2)$ of rational
encodings encodes the complex number $q_1 + q_2 i$, where $q_1$ and $q_2$ are the rational
numbers encoded by $e_1$ and $e_2$.

Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4. -/
def toComplex (e : RatEnc × RatEnc) : ℂ :=
  ⟨((toRat e.1 : ℚ) : ℝ), ((toRat e.2 : ℚ) : ℝ)⟩

/-- **Binary digit of a natural number.** For natural numbers $k$ and $i$, this is the digit of
$i$ at position $k$ in binary, counting from the least significant digit at position $0$, that
is, $\lfloor i / 2^k \rfloor \bmod 2$, taken as an element of $\{0, 1\}$.

Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4. -/
def qBit (k i : ℕ) : Fin 2 :=
  ⟨(i / 2 ^ k) % 2, Nat.mod_lt _ (by norm_num)⟩

/-- **Index of a pair of bits.** A pair $(a, b)$ of bits $a, b \in \{0, 1\}$ has index $2a + b$,
its position in the enumeration $(0, 0), (0, 1), (1, 0), (1, 1)$ of the four pairs.

Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4. -/
def qIdx2 (p : Fin 2 × Fin 2) : ℕ := p.1.val * 2 + p.2.val

/-- **Matrix encoded by a list of entries.** Number the pairs $(a, b)$ with $a, b \in \{0, 1\}$
by $2a + b$, and index the rows and columns of a $4 \times 4$ complex matrix by these pairs.
Given a list $e$ of pairs of encoded rational numbers, the matrix of $e$ has in row $p$ and
column $q$ the complex number whose real part is the first and whose imaginary part is the
second rational of the entry of $e$ at position $4p + q$ (counting from $0$, with $p$ and $q$
replaced by their numbers), and $0$ when $e$ has no entry at that position. A list of $16$
pairs thus lists the entries in row-major order.

Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4. -/
def matrixOfEntries (entries : List (RatEnc × RatEnc)) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q =>
    toComplex (entries.getD (qIdx2 p * 4 + qIdx2 q) ((false, 0, 1), (false, 0, 1)))

/-- **Setting two bits of an index.** For natural numbers $N$, $s$, $i$, $j$ and a pair
$b = (b_1, b_2)$ of bits, this is the index in $\{0, \dots, 2^N - 1\}$ given by
$(s - s_i 2^i - s_j 2^j + b_1 2^i + b_2 2^j) \bmod 2^N$, where $s_k$ is bit $k$ of $s$ and
each subtraction of natural numbers is truncated at $0$. When $i \ne j$ this is $s$ with
bit $i$ set to $b_1$ and bit $j$ set to $b_2$, reduced modulo $2^N$.

Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4. -/
def setBits (N s i j : ℕ) (b : Fin 2 × Fin 2) : Fin (2 ^ N) :=
  ⟨(s - (qBit i s).val * 2 ^ i - (qBit j s).val * 2 ^ j +
    b.1.val * 2 ^ i + b.2.val * 2 ^ j) % 2 ^ N, Nat.mod_lt _ (by positivity)⟩

/-- **Encoded 2-local quantum gate.** A 2-local quantum gate is encoded as a triple $(i, j, e)$
of natural numbers $i$ and $j$, the qubits it acts on, and a list $e$ of pairs of encoded
rational numbers, the real and imaginary parts of the entries of its $4 \times 4$ matrix in
row-major order.

The encoding itself does not require $e$ to have $16$ entries or the matrix to be unitary;
unitarity and the qubit bounds are part of well-formedness.

Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4. -/
abbrev QGate := ℕ × ℕ × List (RatEnc × RatEnc)

/-- **Well-formed quantum gate.** A 2-local gate acting on qubits $i$ and $j$ with entry list $e$
is well-formed on $N$ qubits when $i < j < N$ and the $4 \times 4$ complex matrix $U$ encoded by
$e$ is unitary, that is, $U^* U = I$.

Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4. -/
def QGateWellFormed (N : ℕ) (gate : QGate) : Prop :=
  gate.1 < gate.2.1 ∧ gate.2.1 < N ∧
    (star (matrixOfEntries gate.2.2)) * (matrixOfEntries gate.2.2) = 1

/-- **Applying a 2-local gate to a state.** Let $N$ be a number of qubits, and let a gate consist
of two qubit positions $i$ and $j$ together with a list of entries encoding a $4 \times 4$ complex
matrix $U$ whose rows and columns are indexed by pairs of bits. For a state vector $\psi$ on $N$
qubits, that is, a function from $\{0, \dots, 2^N - 1\}$ to $\mathbb{C}$, applying the gate gives
the state whose value at a basis index $s$ is
$\sum_{b \in \{0,1\}^2} U_{(s_i, s_j), b} \, \psi(s[b])$. Here
$s_k = \lfloor s / 2^k \rfloor \bmod 2$ is bit $k$ of $s$, and for $b = (b_1, b_2)$ the index
$s[b]$ is $(s - s_i 2^i - s_j 2^j + b_1 2^i + b_2 2^j) \bmod 2^N$, with truncated subtraction of
natural numbers; when $i \ne j$ and $i, j < N$, this is $s$ with bits $i$ and $j$ replaced by
$b_1$ and $b_2$.

Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 4 (unitary evolution). -/
def applyGate (N : ℕ) (gate : QGate) (ψ : Fin (2 ^ N) → ℂ) : Fin (2 ^ N) → ℂ :=
  fun s => ∑ b : Fin 2 × Fin 2,
    (matrixOfEntries gate.2.2) (qBit gate.1 s.val, qBit gate.2.1 s.val) b *
      ψ (setBits N s.val gate.1 gate.2.1 b)

/-- **Applying a quantum circuit to a state.** For a state vector $\psi \in \mathbb{C}^{2^N}$ on
$N$ qubits and a list of 2-local gates $g_1, \dots, g_k$, the result of applying the circuit to
$\psi$ is obtained by applying the gate $g_1$ to $\psi$, then $g_2$ to the result, and so on up to
$g_k$. For the empty list it is $\psi$ itself.

Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 4 (quantum circuits). -/
def applyCircuit (N : ℕ) (gates : List QGate) (ψ : Fin (2 ^ N) → ℂ) :
    Fin (2 ^ N) → ℂ :=
  gates.foldl (fun ψ g => applyGate N g ψ) ψ

/-- **Number with a given binary expansion.** A list $b_0, b_1, \ldots, b_{n-1}$ of booleans,
read as bits with true as $1$ and false as $0$, denotes the natural number
$\sum_{i < n} b_i 2^i$; the first entry is the least significant bit.

Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 1 (computational basis). -/
def qNumOf : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * qNumOf rest

/-- **Computational basis state of a bitstring.** For a bitstring $x = (x_0, \dots, x_{n-1})$,
reading true as $1$ and false as $0$, the computational basis state of $x$ is the vector
$\psi : \{0, \dots, 2^n - 1\} \to \mathbb{C}$ with $\psi(s) = 1$ if $s = \sum_{k < n} x_k 2^k$
(the number whose binary expansion is $x$, least significant bit first) and $\psi(s) = 0$
otherwise.

Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 1 (computational basis). -/
def basisState (x : List Bool) : Fin (2 ^ x.length) → ℂ :=
  fun s => if s.val = qNumOf x then 1 else 0

/-- **Tensor product of state vectors.** For vectors $\varphi \in \mathbb{C}^{2^a}$ and
$\psi \in \mathbb{C}^{2^b}$, indexed by $\{0, \dots, 2^a - 1\}$ and $\{0, \dots, 2^b - 1\}$, their
tensor product is the vector in $\mathbb{C}^{2^{a+b}}$ whose entry at $s$ is
$\varphi_{s \bmod 2^a}\, \psi_{\lfloor s / 2^a \rfloor}$. Thus $\varphi$ occupies the low-order $a$
bits of the index and $\psi$ the high-order $b$ bits.

Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 2 (tensor products). -/
def tensorProd {a b : ℕ} (φ : Fin (2 ^ a) → ℂ) (ψ : Fin (2 ^ b) → ℂ) :
    Fin (2 ^ (a + b)) → ℂ :=
  fun s => φ ⟨s.val % 2 ^ a, Nat.mod_lt _ (by positivity)⟩ *
    ψ ⟨s.val / 2 ^ a, by
      have h : s.val < 2 ^ b * 2 ^ a := by
        calc s.val < 2 ^ (a + b) := s.isLt
          _ = 2 ^ a * 2 ^ b := by rw [pow_add]
          _ = 2 ^ b * 2 ^ a := by rw [Nat.mul_comm]
      exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr h⟩

/-- **All-zero state.** The all-zero state on $a$ qubits is the vector in $\mathbb{C}^{2^a}$,
indexed by $s \in \{0, \dots, 2^a - 1\}$, whose entry at $s = 0$ is $1$ and whose other
entries are $0$; that is, the computational basis state $|0 \cdots 0\rangle$.

Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 1 (computational basis). -/
def zeroState (a : ℕ) : Fin (2 ^ a) → ℂ :=
  fun s => if s.val = 0 then 1 else 0

/-- **Squared norm of a state vector.** For a vector $\psi \in \mathbb{C}^{2^m}$, indexed by
$\{0, \dots, 2^m - 1\}$, its squared norm is the real number
$\sum_{s} \overline{\psi_s}\, \psi_s = \sum_{s} |\psi_s|^2$.

Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 2 (Born rule). -/
def sqNorm {m : ℕ} (ψ : Fin (2 ^ m) → ℂ) : ℝ :=
  ∑ s : Fin (2 ^ m), (starRingEnd ℂ (ψ s) * ψ s).re

/-- **Acceptance probability of a quantum state.** For a state vector $\psi$ on $N$ qubits, given
by its amplitudes $\psi(s) \in \mathbb{C}$ at the basis states $s \in \{0, \dots, 2^N - 1\}$, the
acceptance probability is the sum of $|\psi(s)|^2$ over the basis states $s$ whose qubit $0$ (the
output qubit, the least significant bit of $s$) equals $1$. By the Born rule, for a unit vector
$\psi$ this is the probability that measuring the output qubit gives $1$.

Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 2 (Born rule, measurement). -/
def acceptProb {N : ℕ} (ψ : Fin (2 ^ N) → ℂ) : ℝ :=
  ∑ s : Fin (2 ^ N), if qBit 0 s.val = 1 then (starRingEnd ℂ (ψ s) * ψ s).re else 0

/-- **Initial state of a BQP computation.** For a bitstring $x = (x_0, \dots, x_{n-1})$, with
true read as $1$ and false as $0$, and a number $a$ of ancilla qubits, the initial state is the
tensor product of the computational basis state of $x$ and the all-zero state on $a$ qubits: the
vector on $\{0, \dots, 2^{n+a} - 1\}$ whose value at $s$ is the value of the basis state of $x$ at
$s \bmod 2^n$ times the value of the all-zero state at $\lfloor s / 2^n \rfloor$. So $x$ occupies
the $n$ low-order bits of the index, and the state equals $1$ at the index $\sum_{k < n} x_k 2^k$
and $0$ elsewhere.

Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 4 (quantum circuits);
S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 10.1. -/
def bqpInitState (x : List Bool) (a : ℕ) : Fin (2 ^ (x.length + a)) → ℂ :=
  tensorProd (basisState x) (zeroState a)

/-- **BQP.** The class BQP of bounded-error quantum polynomial-time decision problems consists
of the decision problems $L$ for which there are polynomials $a$ and $q$ with natural number
coefficients and a polynomial-time computable map sending each bitstring $x$ to a list of
2-local quantum gates such that, for every bitstring $x$, with $n = |x|$ and $N = n + a(n)$:
the list has at most $q(n)$ gates; each gate acts on qubits $i < j < N$ and its $4 \times 4$
matrix, whose entries have rational real and imaginary parts, is unitary; and after the gates
are applied in order to the state with $x$ in the computational basis on the $n$ low-order
qubits and $a(n)$ ancilla qubits in state $0$, the probability that qubit $0$ measures $1$ is
at least $2/3$ if $L(x)$ is true and at most $1/3$ if $L(x)$ is false.

Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 10.1; M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 4; E. Bernstein and
U. Vazirani, "Quantum complexity theory", SIAM Journal on Computing 26 (1997),
1411-1473. -/
def BQP : DecisionComplexityClass :=
  {L | ∃ a s : Polynomial ℕ, ∃ gates : List Bool → List QGate,
    IsPolyTime gates ∧
    (∀ x, (gates x).length ≤ s.eval x.length) ∧
    (∀ x, ∀ g ∈ gates x, QGateWellFormed (x.length + a.eval x.length) g) ∧
    ∀ x,
      (L x = true →
        2 / 3 ≤ acceptProb
          (applyCircuit (x.length + a.eval x.length) (gates x)
            (bqpInitState x (a.eval x.length)))) ∧
      (L x = false → acceptProb
          (applyCircuit (x.length + a.eval x.length) (gates x)
            (bqpInitState x (a.eval x.length))) ≤ 1 / 3)}

/-! ### Approximation classes: `APX`, `PTAS`, `FPTAS` -/

/-- **Optimization problems.** An optimization problem consists of a function $v$ assigning a
rational value $v(x, s)$ to every instance $x$ and every candidate solution $s$, both bitstrings;
a feasibility predicate saying whether $s$ is a feasible solution for $x$; and a polynomial $p$
with natural-number coefficients such that every feasible solution $s$ for $x$ has length at
most $p(|x|)$. It is required that $v(x, s) \ge 0$ for all $x$ and $s$, that $v(x, s) = 0$
whenever $s$ is not feasible for $x$, and that every instance has a feasible solution.

The problem is read as a maximization problem. The structure carries no computational content:
polynomial-time feasibility and a polynomial-time encoding of the objective form a separate
predicate (NPO), which the approximation classes APX, PTAS and FPTAS require.

Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440; S. Arora and B. Barak, Computational Complexity: A Modern Approach,
2009, Chapter 11. -/
structure OptProblem where
  /-- The objective value of solution `s` for instance `x`. -/
  val : List Bool → List Bool → ℚ
  /-- The feasibility predicate: whether `s` is a feasible solution for `x`. -/
  feas : List Bool → List Bool → Bool
  /-- A polynomial bound on feasible solution lengths. -/
  bound : Polynomial ℕ
  /-- Feasible solutions respect the length bound. -/
  feas_len : ∀ x s, feas x s = true → s.length ≤ bound.eval x.length
  /-- Objective values are nonnegative. -/
  val_nonneg : ∀ x s, 0 ≤ val x s
  /-- The value on infeasible solutions is `0`. -/
  val_infeas : ∀ x s, feas x s = false → val x s = 0
  /-- Every instance has a feasible solution. -/
  feas_nonempty : ∀ x, ∃ s, feas x s = true

/-- **Approximation ratio at a precision.** Let $P$ be a maximization problem with objective
value $\mathrm{val}(x, s)$ for instance $x$ and solution $s$, let $A$ be an algorithm taking a
pair of bitstrings, let $k$ be a natural number and let $\rho$ be a rational number. Then $A$
achieves ratio $\rho$ on $P$ at precision $k$ when, for every instance $x$ and every feasible
solution $s$ of $x$, the output $y = A(x, 1^k)$ of $A$ on $x$ and the unary string $1^k$ of $k$
ones is a feasible solution of $x$ with $\rho \cdot \mathrm{val}(x, s) \le \mathrm{val}(x, y)$.

Since every instance has a feasible solution, the output is then always feasible and worth at
least $\rho$ times the value of every feasible solution. The approximation classes share this
call convention: a fully polynomial-time approximation scheme is one algorithm achieving ratio
$1 - 1/k$ at every precision $k \ge 1$, a polynomial-time approximation scheme has such an
algorithm for each $k \ge 1$ separately, and APX asks for some ratio $\rho$ with $0 < \rho \le 1$
at precision $2$.

Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440; S. Arora and B. Barak, Computational Complexity: A Modern Approach,
2009, Chapter 11. -/
def ApproxAt (P : OptProblem) (A : List Bool × List Bool → List Bool) (k : ℕ)
    (ρ : ℚ) : Prop :=
  ∀ x s, P.feas x s = true →
    ρ * P.val x s ≤ P.val x (A (x, List.replicate k true)) ∧
    P.feas x (A (x, List.replicate k true)) = true

/-- **NPO optimization problems.** Let $P$ be an optimization problem whose instances $x$ and
solutions $s$ are bitstrings, with rational value $\mathrm{val}(x, s)$ and feasibility predicate
$\mathrm{feas}(x, s)$. Then $P$ is an NPO problem when the map $(x, s) \mapsto \mathrm{feas}(x, s)$
is polynomial-time computable, and there is a polynomial-time computable map $\mathrm{enc}$
sending each pair $(x, s)$ to a triple $(b, a, d)$ of a boolean and two natural numbers such
that, for all $x$ and $s$: $d \neq 0$; if $s$ is feasible for $x$, then
$\mathrm{val}(x, s) = \sigma a / d$, where $\sigma = -1$ if $b$ is true and $\sigma = 1$
otherwise; and if $s$ is not feasible for $x$, then $\mathrm{val}(x, s) = 0$.

The approximation classes APX, PTAS and FPTAS all require this condition. Without it, a problem
could hide an undecidable feasibility relation while assigning value $0$ everywhere, and the
constant empty-solution algorithm would vacuously satisfy the approximation guarantees.

Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440; S. Arora and B. Barak, Computational Complexity: A Modern Approach,
2009, Chapter 11. -/
def IsNPO (P : OptProblem) : Prop :=
  IsPolyTime (fun p : List Bool × List Bool => P.feas p.1 p.2) ∧
  ∃ enc : List Bool × List Bool → (Bool × ℕ × ℕ), IsPolyTime enc ∧
    (∀ x s, P.val x s =
      if P.feas x s then
        (if (enc (x, s)).1 then -1 else 1) * ((enc (x, s)).2.1 : ℚ) / (enc (x, s)).2.2
      else 0) ∧
    (∀ x s, (enc (x, s)).2.2 ≠ 0)

/-- **Constant-factor approximable problems.** A maximization problem $P$ is in $\mathsf{APX}$
when $P$ is an NPO problem and there are a rational number $\rho$ with $0 < \rho \le 1$ and a
polynomial-time algorithm $A$ such that, for every instance $x$ and every feasible solution $s$
for $x$, the output $A(x, 1^2)$ of $A$ on $x$ with the unary precision tape of length $2$ is a
feasible solution for $x$ whose value is at least $\rho$ times the value of $s$.

The ratio $\rho$ is the fraction of the optimum achieved, the reciprocal of the convention
$\rho \ge 1$ in which the value is at least the optimum divided by $\rho$. The NPO
requirement is part of the class: without it, a problem that is not NPO and has value $0$
everywhere would qualify vacuously.

Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440; S. Arora and B. Barak, Computational Complexity: A Modern Approach,
2009, Chapter 11. -/
def IsAPX (P : OptProblem) : Prop :=
  IsNPO P ∧ ∃ ρ : ℚ, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ A : List Bool × List Bool → List Bool,
    IsPolyTime A ∧ ApproxAt P A 2 ρ

/-- **The class APX.** APX is the set of maximization problems $P$ that are NP optimization
problems (feasibility is decidable in polynomial time, and a polynomial-time computable map
sends every instance-solution pair to a signed fraction with nonzero denominator that equals the
objective value whenever the solution is feasible) and for which there are a rational number
$\rho$ with $0 < \rho \le 1$ and a polynomial-time algorithm $A$ achieving ratio $\rho$ on $P$ at
precision $2$: for every instance $x$ and every feasible solution $s$ of $x$, the output $y$ of
$A$ on $x$ and the unary precision string $11$ is a feasible solution of $x$ whose value is at
least $\rho$ times the value of $s$.

Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440. -/
def APX : Set OptProblem := {P | IsAPX P}

/-- **Polynomial-time approximation schemes.** An optimization problem $P$, with value
$\mathrm{val}(x, s)$ of a solution $s$ for an instance $x$, admits a polynomial-time
approximation scheme when $P$ is an NPO problem and for every integer $k \ge 1$ there is a
polynomial-time computable algorithm $A$ on pairs of bitstrings with the following property:
for every instance $x$ and every feasible solution $s$ for $x$, the output $A(x, 1^k)$ on $x$
and the string $1^k$ of $k$ true bits is a feasible solution for $x$ with
$(1 - 1/k)\,\mathrm{val}(x, s) \le \mathrm{val}(x, A(x, 1^k))$. That is, $A$ achieves
approximation ratio $1 - 1/k$, an error of $\varepsilon = 1/k$; the algorithm may depend on $k$.

Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440; S. Arora and B. Barak, Computational Complexity: A Modern Approach,
2009, Chapter 11. -/
def IsPTAS (P : OptProblem) : Prop :=
  IsNPO P ∧ ∀ k : ℕ, 1 ≤ k → ∃ A : List Bool × List Bool → List Bool,
    IsPolyTime A ∧ ApproxAt P A k (1 - 1 / (k : ℚ))

/-- **The class PTAS.** PTAS is the set of optimization problems $P$ that are NPO problems
(feasibility is decidable in polynomial time and the objective value is given by a
polynomial-time computable rational encoding) and that have a polynomial-time approximation
scheme: for every natural number $k \ge 1$ there is a polynomial-time algorithm $A$ such that,
for every instance $x$ and every feasible solution $s$ of $x$, the output of $A$ on $x$ and the
string of $k$ ones is a feasible solution of $x$ whose value is at least $(1 - 1/k)$ times the
value of $s$.

Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440. -/
def PTAS : Set OptProblem := {P | IsPTAS P}

/-- **Fully polynomial-time approximation schemes.** A maximization problem $P$ has an FPTAS
when $P$ is an NPO problem and there is one polynomial-time algorithm $A$ such that, for every
integer $k \ge 1$, every instance $x$ and every feasible solution $s$ for $x$, the output
$A(x, 1^k)$ of $A$ on $x$ with the unary precision tape of length $k$ is a feasible solution for
$x$ whose value is at least $1 - 1/k$ times the value of $s$.

Since the precision tape is unary, polynomial time in the total input length is polynomial
time in $|x|$ and $1/\varepsilon$, where $\varepsilon = 1/k$.

Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440; S. Arora and B. Barak, Computational Complexity: A Modern Approach,
2009, Chapter 11. -/
def IsFPTAS (P : OptProblem) : Prop :=
  IsNPO P ∧ ∃ A : List Bool × List Bool → List Bool, IsPolyTime A ∧
    ∀ k : ℕ, 1 ≤ k → ApproxAt P A k (1 - 1 / (k : ℚ))

/-- **The class FPTAS.** FPTAS is the class of optimization problems that have a fully
polynomial-time approximation scheme.

Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440. -/
def FPTAS : Set OptProblem := {P | IsFPTAS P}

/-- **FPTAS is contained in PTAS.** Every optimization problem in the class FPTAS of
problems with a fully polynomial-time approximation scheme belongs to the class PTAS of
problems with a polynomial-time approximation scheme.

The single fully polynomial-time algorithm serves as the algorithm for every precision $k$.

Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440. -/
theorem fptas_subset_ptas : FPTAS ⊆ PTAS := by
  intro P hP
  obtain ⟨hNPO, A, hA, hAk⟩ := hP
  exact ⟨hNPO, fun k hk => ⟨A, hA, hAk k hk⟩⟩

/-- **PTAS is contained in APX.** Every optimization problem in the class PTAS belongs to the
class APX.

The algorithm that the approximation scheme provides for error $1/2$ achieves the constant
ratio $1/2$.

Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440. -/
theorem ptas_subset_apx : PTAS ⊆ APX := by
  intro P hP
  obtain ⟨hNPO, hScheme⟩ := hP
  obtain ⟨A, hA, hA2⟩ := hScheme 2 (by norm_num)
  have h12 : (1 : ℚ) - 1 / ((2 : ℕ) : ℚ) = 1 / 2 := by push_cast; norm_num
  rw [h12] at hA2
  exact ⟨hNPO, 1 / 2, by norm_num, by norm_num, A, hA, hA2⟩

/-! ### One-way functions and permutations -/

/-- **Negligible functions.** A function $e : \mathbb{N} \to \mathbb{Q}$ is negligible if for
every natural number $c$ there is a natural number $N$ such that $e(n) \le 1 / n^c$ for all
natural numbers $n \ge N$.

Source: O. Goldreich, Foundations of Cryptography, Vol. 1, Cambridge University
Press, 2001, Section 2.2. -/
def Negligible (e : ℕ → ℚ) : Prop :=
  ∀ c : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → e n ≤ 1 / (n : ℚ) ^ c

/-- **Inversion success probability.** Let $f$ be a family of functions, $f_n$ mapping $n$-bit
strings to bitstrings, and let $A$ be an inverter mapping a triple $(n, y, r)$ of a length $n$,
an output $y$ and a coin string $r$ to a bitstring. For natural numbers $n$ and $m$, the
inversion success probability of $A$ against $f$ at length $n$ with $m$ coins is the fraction of
the $2^{n+m}$ pairs $(x, r)$ of an $n$-bit string $x$ and an $m$-bit string $r$ such that
$f_n(x') = f_n(x)$, where $x'$ is the $n$-bit string whose $i$-th bit is the $i$-th bit of
$A(n, f_n(x), r)$, or false when that output has no $i$-th bit.

The inverter receives the length $n$ explicitly: when output lengths vary, it could not
otherwise recover $n$ from $f_n(x)$ alone.

Source: O. Goldreich, Foundations of Cryptography, Vol. 1, Cambridge University
Press, 2001, Section 2.2. -/
noncomputable def invertSucc (f : (n : ℕ) → (Fin n → Bool) → List Bool)
    (inv : ℕ × List Bool × List Bool → List Bool) (n m : ℕ) : ℚ :=
  (Set.ncard {p : (Fin n → Bool) × (Fin m → Bool) |
    f n (fun i => (inv (n, f n p.1, List.ofFn p.2)).getD i.val false) = f n p.1} : ℚ) /
    (2 : ℚ) ^ (n + m)

/-- **One-way function families.** Let $f$ assign to each $n \in \mathbb{N}$ and each $n$-bit
string $x$ a bitstring $f_n(x)$. The family $f$ is one-way when three conditions hold. First, its
output lengths are polynomially bounded: some polynomial $p$ satisfies $|f_n(x)| \le p(n)$ for
all $n$ and $x$. Second, it is uniformly computable: some polynomial-time computable function
maps the bitstring encoding of the pair $(n, x)$ to $f_n(x)$ for all $n$ and $x$. Third, it is
hard to invert: for every polynomial $q$ with natural-number coefficients and every
polynomial-time computable inverter $A$ on triples $(n, y, r)$ of a natural number and two
bitstrings, the inversion success probability of $A$ against $f$ at length $n$ with $q(n)$
coins is negligible in $n$, that is, for every $c \in \mathbb{N}$ it is at most $1 / n^c$ for
all large enough $n$. Here the inversion success probability is the fraction of pairs $(x, r)$
of an $n$-bit string $x$ and a $q(n)$-bit string $r$ for which the $n$-bit string $x'$ formed
by the first $n$ bits of $A(n, f_n(x), r)$, with missing bits false, satisfies
$f_n(x') = f_n(x)$.

Deterministic inverters are the special case that ignores the coins. The uniform evaluator is
essential: per-length polynomial-size circuits would admit arbitrary noncomputable families.

Source: O. Goldreich, Foundations of Cryptography, Vol. 1, Cambridge University
Press, 2001, Section 2.2; R. Impagliazzo, "A personal view of average-case
complexity", Proceedings of the Tenth Annual Structure in Complexities Theory
Conference (1995), 134-147. -/
def IsOneWayFunction (f : (n : ℕ) → (Fin n → Bool) → List Bool) : Prop :=
  (∃ pOut : Polynomial ℕ, ∀ n, ∀ x : Fin n → Bool, (f n x).length ≤ pOut.eval n) ∧
  (∃ evalf : List Bool → List Bool, IsPolyTime evalf ∧
    ∀ n, ∀ x : Fin n → Bool,
      evalf (MetaMathlibExt.BitstringEncoding.bitEncode (n, List.ofFn x)) = f n x) ∧
  ∀ (q : Polynomial ℕ) (inv : ℕ × List Bool × List Bool → List Bool),
    IsPolyTime inv → Negligible (fun n => invertSucc f inv n (q.eval n))

/-- **Inversion success probability against a permutation family.** Let $\pi$ be a family of
maps $\pi_n$ from $n$-bit strings to $n$-bit strings, let $A$ be a function sending a natural
number and two bitstrings to a bitstring, and let $n$ and $m$ be natural numbers. For a bitstring
$w$, write $\mathrm{trunc}_n(w)$ for the $n$-bit string whose bit at each position $i < n$ is the
entry of $w$ at position $i$, or false if $w$ has at most $i$ entries. The success probability of
$A$ against $\pi$ at length $n$ with $m$ coins is the rational number $N / 2^{n+m}$, where $N$ is
the number of pairs $(x, c)$ of an $n$-bit string $x$ and an $m$-bit string $c$ with
$\pi_n(\mathrm{trunc}_n(A(n, \pi_n(x), c))) = \pi_n(x)$, where $\pi_n(x)$ is passed to $A$ as a
bitstring.

Here $A$ is a probabilistic inverter that receives the security parameter $n$, the image
$\pi_n(x)$ and the coins $c$.

Source: O. Goldreich, Foundations of Cryptography, Vol. 1, Cambridge University
Press, 2001, Section 2.2. -/
noncomputable def permInvertSucc (π : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool))
    (inv : ℕ × List Bool × List Bool → List Bool) (n m : ℕ) : ℚ :=
  (Set.ncard {p : (Fin n → Bool) × (Fin m → Bool) |
    π n (fun i => (inv (n, List.ofFn (π n p.1), List.ofFn p.2)).getD i.val false) =
      π n p.1} : ℚ) / (2 : ℚ) ^ (n + m)

/-- **One-way permutation families.** Let $\pi$ assign to each $n \in \mathbb{N}$ a map $\pi_n$
from $n$-bit strings to $n$-bit strings. The family $\pi$ is a one-way permutation when three
conditions hold. First, each $\pi_n$ is injective, hence a permutation of the $n$-bit strings.
Second, it is uniformly computable: some polynomial-time computable function maps the
bitstring encoding of the pair $(n, x)$ to $\pi_n(x)$ for all $n$ and all $n$-bit strings $x$.
Third, it is hard to invert: for every polynomial $q$ with natural-number coefficients and every
polynomial-time computable inverter $A$ on triples $(n, y, r)$ of a natural number and two
bitstrings, the inversion success probability of $A$ against $\pi$ at length $n$ with $q(n)$
coins is negligible in $n$, that is, for every $c \in \mathbb{N}$ it is at most $1 / n^c$ for
all large enough $n$. Here the inversion success probability is the fraction of pairs $(x, r)$
of an $n$-bit string $x$ and a $q(n)$-bit string $r$ for which the $n$-bit string $x'$ formed
by the first $n$ bits of $A(n, \pi_n(x), r)$, with missing bits false, satisfies
$\pi_n(x') = \pi_n(x)$.

Source: O. Goldreich, Foundations of Cryptography, Vol. 1, Cambridge University
Press, 2001, Section 2.2. -/
def IsOneWayPermutation (π : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool)) : Prop :=
  (∀ n, Function.Injective (π n)) ∧
  (∃ evalπ : List Bool → List Bool, IsPolyTime evalπ ∧
    ∀ n, ∀ x : Fin n → Bool,
      evalπ (MetaMathlibExt.BitstringEncoding.bitEncode (n, List.ofFn x)) =
        List.ofFn (π n x)) ∧
  ∀ (q : Polynomial ℕ) (inv : ℕ × List Bool × List Bool → List Bool),
    IsPolyTime inv → Negligible (fun n => permInvertSucc π inv n (q.eval n))

/-- **One-way permutations are one-way functions.** Let $\pi$ be a one-way permutation family, so
that each $\pi_n$ maps $n$-bit strings to $n$-bit strings. Then the family that sends an $n$-bit
string $x$ to the bitstring $\pi_n(x)$ is a one-way function family.

Length preservation gives the polynomial output bound, the evaluator of $\pi$ serves unchanged,
and the inversion success probabilities coincide because an $n$-bit string is determined by the
list of its bits.

Source: O. Goldreich, Foundations of Cryptography, Vol. 1, Cambridge University
Press, 2001, Section 2.2. -/
theorem one_way_permutation_implies_one_way_function
    {π : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool)}
    (hπ : IsOneWayPermutation π) :
    IsOneWayFunction (fun n x => List.ofFn (π n x)) := by
  obtain ⟨hinj, heval, hhard⟩ := hπ
  refine ⟨⟨Polynomial.X, fun n x => ?_⟩, heval, fun q inv hinv => ?_⟩
  · simp [List.length_ofFn, Polynomial.eval_X]
  · have hsucc : (fun n => invertSucc (fun n x => List.ofFn (π n x)) inv n (q.eval n)) =
        (fun n => permInvertSucc π inv n (q.eval n)) := by
      funext n
      have hset : {p : (Fin n → Bool) × (Fin (q.eval n) → Bool) |
            List.ofFn (π n (fun i =>
              (inv (n, List.ofFn (π n p.1), List.ofFn p.2)).getD i.val false)) =
              List.ofFn (π n p.1)} =
          {p : (Fin n → Bool) × (Fin (q.eval n) → Bool) |
            π n (fun i =>
              (inv (n, List.ofFn (π n p.1), List.ofFn p.2)).getD i.val false) =
              π n p.1} := by
        ext p
        simp only [Set.mem_ofPred_eq]
        exact ⟨fun h => List.ofFn_injective h, fun h => congrArg List.ofFn h⟩
      simp only [invertSucc, permInvertSucc]
      rw [hset]
    rw [hsucc]
    exact hhard q inv hinv

end Cslib.Complexity.Classes
