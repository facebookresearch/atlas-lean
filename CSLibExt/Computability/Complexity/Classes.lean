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

/-- The language (as a set of bitstrings) accepted by a decision problem. -/
def langOf (L : DecisionProblem) : Set (List Bool) := {x | L x = true}

/-- `PSPACE`: the CSLib multi-tape polynomial-space class, bridged to decision problems. -/
def PSPACE : DecisionComplexityClass :=
  {L | langOf L ∈ Cslib.Turing.MultiTapeTM.Classes.PSPACE}

/-- `EXP`: deterministic exponential time, `DTIME(2 ^ (n ^ d))` for some `d`. -/
def EXP : DecisionComplexityClass :=
  {L | ∃ d, langOf L ∈ Cslib.Turing.MultiTapeTM.DTIME (fun n => 2 ^ (n ^ d))}

/-- `EXPSPACE`: deterministic exponential space, `DSPACE(2 ^ (n ^ d))` for some `d`. -/
def EXPSPACE : DecisionComplexityClass :=
  {L | ∃ d, langOf L ∈ Cslib.Turing.MultiTapeTM.DSPACE (fun n => 2 ^ (n ^ d))}

/-- `E`: deterministic time `2 ^ (c * n)` for some constant `c`. -/
def E : DecisionComplexityClass :=
  {L | ∃ c, langOf L ∈ Cslib.Turing.MultiTapeTM.DTIME (fun n => 2 ^ (c * n))}

/-- Deterministic logarithmic space, `DSPACE(O(log n))` on the multi-tape model. -/
def LogSpace : DecisionComplexityClass :=
  {L | ∃ c, langOf L ∈
    Cslib.Turing.MultiTapeTM.DSPACE (fun n => c * Nat.log 2 (n + 1) + c)}

/-- Log-space computable functions, via the CSLib multi-tape model
(space `O(log n)`, some time bound). -/
def LogSpaceComputable (f : List Bool → List Bool) : Prop :=
  ∃ c, ∃ t : ℕ → ℕ,
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength f
      ⟨id, Function.injective_id⟩ ⟨id, Function.injective_id⟩ t
      (fun n => c * Nat.log 2 (n + 1) + c)

/-- Log-space many-one reduction. -/
def LogSpaceRed (L₁ L₂ : DecisionProblem) : Prop :=
  ∃ f, LogSpaceComputable f ∧ ∀ x, L₁ x ↔ L₂ (f x)

/-! ### Nondeterministic multi-tape classes -/

/-- Nondeterministic multi-tape acceptance: some computation path halts
with output `[true]`. -/
def NTMDecides {k : ℕ} {State : Type*} (ntm : Turing.MultiTapeNTM k Bool State)
    (L : Set (List Bool)) : Prop :=
  ∀ x, (x ∈ L ↔ ∃ p : ntm.ComputationPath x, p.last.Halted ∧ p.last.output = [true])

/-- Nondeterministic decision in time `t`: every path of length at least
`t |x|` halts, and acceptance is by an accepting path. -/
def NTMDecidesInTime {k : ℕ} {State : Type*} (ntm : Turing.MultiTapeNTM k Bool State)
    (t : ℕ → ℕ) (L : Set (List Bool)) : Prop :=
  (∀ x, ∀ p : ntm.ComputationPath x, t x.length ≤ p.time → p.last.Halted) ∧
    NTMDecides ntm L

/-- Nondeterministic decision in space `s`: every computation path stays
within the space bound. -/
def NTMDecidesInSpace {k : ℕ} {State : Type*} (ntm : Turing.MultiTapeNTM k Bool State)
    (s : ℕ → ℕ) (L : Set (List Bool)) : Prop :=
  (∀ x, ∀ p : ntm.ComputationPath x, p.space ≤ s x.length) ∧
    NTMDecides ntm L

/-- `NTIME(t)`: languages decided by a nondeterministic multi-tape machine in time `t`. -/
def NTIME (t : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ c₁ c₂, ∃ k, ∃ (State : Type) (_ : Finite State),
    ∃ ntm : Turing.MultiTapeNTM k Bool State,
    NTMDecidesInTime ntm (fun n => c₁ * t n + c₂) L}

/-- `NSPACE(s)`: languages decided by a nondeterministic multi-tape machine in space `s`. -/
def NSPACE (s : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ c₁ c₂, ∃ k, ∃ (State : Type) (_ : Finite State),
    ∃ ntm : Turing.MultiTapeNTM k Bool State,
    NTMDecidesInSpace ntm (fun n => c₁ * s n + c₂) L}

/-- `NL`: nondeterministic logarithmic space. -/
def NL : DecisionComplexityClass :=
  {L | ∃ c, langOf L ∈ NSPACE (fun n => c * Nat.log 2 (n + 1) + c)}

/-- `NPSPACE`: nondeterministic polynomial space. -/
def NPSPACE : DecisionComplexityClass :=
  {L | ∃ d, langOf L ∈ NSPACE (fun n => n ^ d)}

/-- `NEXP`: nondeterministic exponential time, witness/time `2 ^ (p n)` for a polynomial `p`. -/
def NEXP : DecisionComplexityClass :=
  {L | ∃ p : Polynomial ℕ, langOf L ∈ NTIME (fun n => 2 ^ (p.eval n))}

/-! ### Randomized and counting classes (verifier / counting definitions) -/

/-- `BPP`: bounded-error probabilistic polynomial time; acceptance
probability at least `2/3` on yes-instances, at most `1/3` on no-instances. -/
def BPP : DecisionComplexityClass :=
  {L | ∃ p : Polynomial ℕ, ∃ R : List Bool × List Bool → Bool, IsPolyTime R ∧
    ∀ x,
      (L x = true →
        3 * Set.ncard {r : Fin (p.eval x.length) → Bool | R (x, List.ofFn r) = true} ≥
          2 * 2 ^ (p.eval x.length)) ∧
      (L x = false →
        3 * Set.ncard {r : Fin (p.eval x.length) → Bool | R (x, List.ofFn r) = true} ≤
          2 ^ (p.eval x.length))}

/-- `PP`: probabilistic polynomial time with unbounded error;
acceptance probability `> 1/2` on yes-instances, `≤ 1/2` on no-instances. -/
def PP : DecisionComplexityClass :=
  {L | ∃ p : Polynomial ℕ, ∃ R : List Bool × List Bool → Bool, IsPolyTime R ∧
    ∀ x,
      (L x = true →
        2 * Set.ncard {r : Fin (p.eval x.length) → Bool | R (x, List.ofFn r) = true} >
          2 ^ (p.eval x.length)) ∧
      (L x = false →
        2 * Set.ncard {r : Fin (p.eval x.length) → Bool | R (x, List.ofFn r) = true} ≤
          2 ^ (p.eval x.length))}

/-- `P/poly`: polynomial-time with polynomial-length advice depending only on input length. -/
def PPoly : DecisionComplexityClass :=
  {L | ∃ p : Polynomial ℕ, ∃ advice : ℕ → List Bool,
    (∀ n, (advice n).length ≤ p.eval n) ∧
    ∃ R : List Bool × List Bool → Bool, IsPolyTime R ∧
    ∀ x, L x ↔ R (x, advice x.length) = true}

/-- `#P`: functions counting accepting witnesses of one fixed polynomial length. -/
def SharpP : Set (List Bool → ℕ) :=
  {f | ∃ p : Polynomial ℕ, ∃ R : List Bool × List Bool → Bool, IsPolyTime R ∧
    ∀ x, f x = Set.ncard
      {w : Fin (p.eval x.length) → Bool | R (x, List.ofFn w) = true}}

/-! ### Oracle computations -/

/-- Evaluate an oracle machine with a fixed number of adaptive queries:
`nextQ` chooses the next query from the input and the query/answer history,
`final` decides from the input and the full history. Dummy queries simulate
early halting, so a fixed query count is without loss of generality.
`cap` is a global bound on every query length (polynomial in `|x|` at use
sites); a query longer than `cap` halts the machine early with `final`, so
per-call polynomial time of `nextQ`/`final` plus the cap gives total
polynomial time in the original input. -/
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

/-- `P` with a Boolean oracle `O`, via `evalOracle`. -/
def PWithOracle (O : List Bool → Bool) : DecisionComplexityClass :=
  {L | ∃ p q : Polynomial ℕ,
    ∃ nextQ : List Bool × List (List Bool × Bool) → List Bool,
    ∃ final : List Bool × List (List Bool × Bool) → Bool,
    IsPolyTime nextQ ∧ IsPolyTime final ∧
    ∀ x, L x ↔
      evalOracle (q.eval x.length) nextQ final O x (p.eval x.length) [] = true}

/-- `NP` with a Boolean oracle `O`: the verifier is an oracle machine
whose input is the bitstring encoding of `(x, w)`. -/
def NPWithOracle (O : List Bool → Bool) : DecisionComplexityClass :=
  {L | ∃ p q : Polynomial ℕ,
    ∃ nextQ : List Bool × List (List Bool × Bool) → List Bool,
    ∃ final : List Bool × List (List Bool × Bool) → Bool,
    IsPolyTime nextQ ∧ IsPolyTime final ∧
    ∀ x, L x ↔ ∃ w : List Bool, w.length ≤ p.eval x.length ∧
      evalOracle (q.eval x.length) nextQ final O (MetaMathlibExt.BitstringEncoding.bitEncode (x, w))
        (p.eval x.length) [] = true}

/-- `P` with a `#P` oracle `f`, via `evalOracle` (oracle answers in `ℕ`). -/
def PWithSharpP : DecisionComplexityClass :=
  {L | ∃ f ∈ SharpP, ∃ p q : Polynomial ℕ,
    ∃ nextQ : List Bool × List (List Bool × ℕ) → List Bool,
    ∃ final : List Bool × List (List Bool × ℕ) → Bool,
    IsPolyTime nextQ ∧ IsPolyTime final ∧
    ∀ x, L x ↔
      evalOracle (q.eval x.length) nextQ final f x (p.eval x.length) [] = true}

/-- `#P`-completeness, via polynomial-time oracle computations:
`f` is in `#P` and every `#P` function is computable from `f` by an
oracle machine with a polynomial number of adaptive queries. -/
def SharpPComplete (f : List Bool → ℕ) : Prop :=
  f ∈ SharpP ∧ ∀ g ∈ SharpP, ∃ p q : Polynomial ℕ,
    ∃ nextQ : List Bool × List (List Bool × ℕ) → List Bool,
    ∃ final : List Bool × List (List Bool × ℕ) → ℕ,
    IsPolyTime nextQ ∧ IsPolyTime final ∧
    ∀ x, g x = evalOracle (q.eval x.length) nextQ final f x (p.eval x.length) []

/-! ### The polynomial hierarchy -/

/-- Alternating quantifiers over witnesses of length at most `bound |x|`:
`k` blocks remain, outermost `∃` when `isSigma` is `true`, `∀` when `false`.
`R (x, ws)` is the polynomial-time matrix on the list of witnesses so far. -/
def AltQuant (bound : ℕ → ℕ) : ℕ → Bool →
    (List Bool × List (List Bool) → Bool) → List Bool → Prop
  | 0, _, R, x => R (x, []) = true
  | k + 1, true, R, x =>
    ∃ w, w.length ≤ bound x.length ∧
      AltQuant bound k false (fun p => R (p.1, w :: p.2)) x
  | k + 1, false, R, x =>
    ∀ w, w.length ≤ bound x.length →
      AltQuant bound k true (fun p => R (p.1, w :: p.2)) x

/-- `Σ_k^p`: `k` alternating blocks starting with `∃`. -/
def SigmaK (k : ℕ) : DecisionComplexityClass :=
  {L | ∃ p : Polynomial ℕ, ∃ R : List Bool × List (List Bool) → Bool, IsPolyTime R ∧
    ∀ x, L x ↔ AltQuant (fun n => p.eval n) k true R x}

/-- `Π_k^p`: `k` alternating blocks starting with `∀`. -/
def PiK (k : ℕ) : DecisionComplexityClass :=
  {L | ∃ p : Polynomial ℕ, ∃ R : List Bool × List (List Bool) → Bool, IsPolyTime R ∧
    ∀ x, L x ↔ AltQuant (fun n => p.eval n) k false R x}

/-- `PH`: the union of the `Σ_k^p` levels. -/
def PH : DecisionComplexityClass := ⋃ k, SigmaK k

/-- `AM`: Arthur-Merlin; Arthur's random string `r` is followed by Merlin's
witness `w`, acceptance probability at least `2/3` / at most `1/3`. -/
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

/-- `coAM`: complements of `AM` languages. -/
def coAM : DecisionComplexityClass := {L | Lᶜ ∈ AM}

/-! ### Interactive proofs and PCP -/

/-- One interactive-proof game: `rounds` rounds of verifier message
(`Vmsg`) followed by prover reply (`P`), then the verifier decides
(`Vdec`). The transcript contains verifier messages and prover replies
only, so the prover never sees the verifier's coins. `cap` bounds every
message length (polynomial in `|x|` at use sites); an over-long message
rejects, so the verifier's per-step polynomial time gives total
polynomial time in the original input. -/
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

/-- `IP`: polynomially many rounds, polynomially many verifier coins;
completeness `≥ 2/3` (some prover), soundness `≤ 1/3` (every prover). -/
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

/-- Non-adaptive `PCP` with `rbound |x|` random bits and at most
`qbound |x|` queries: `queries` picks the queried positions from `(x, rand)`,
`decide` decides from `(x, rand, answers)`. Completeness `≥ 2/3`,
soundness `≤ 1/3`. -/
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

/-- One gate of a flat Boolean circuit on `n` inputs: gate `j` may only
reference gates `< j` (enforced by `WellFormedCircuit`). -/
inductive ACGate (n : ℕ) where
  | var : Fin n → ACGate n
  | const : Bool → ACGate n
  | notGate : ℕ → ACGate n
  | andGate : List ℕ → ACGate n
  | orGate : List ℕ → ACGate n
  | modGate : ℕ → List ℕ → ACGate n

/-- Inputs referenced by one gate. -/
def gateInputs {n : ℕ} : ACGate n → List ℕ
  | .var _ => []
  | .const _ => []
  | .notGate a => [a]
  | .andGate l => l
  | .orGate l => l
  | .modGate _ l => l

/-- Well-formedness: every gate references only strictly earlier gates. -/
def WellFormedCircuit {n : ℕ} (C : List (ACGate n)) : Prop :=
  ∀ j (h : j < C.length), ∀ a ∈ gateInputs (C[j]'h), a < j

/-- Value of one gate given the values of earlier gates and the input assignment. -/
def gateValue {n : ℕ} (vs : List Bool) (assign : Fin n → Bool) : ACGate n → Bool
  | .var i => assign i
  | .const b => b
  | .notGate a => !(vs.getD a false)
  | .andGate l => l.all (fun a => vs.getD a false)
  | .orGate l => l.any (fun a => vs.getD a false)
  | .modGate m l =>
    if m = 0 then false
    else (l.filter (fun a => vs.getD a false)).length % m = 0

/-- Values of all gates in order. -/
def circuitEval {n : ℕ} (C : List (ACGate n)) (assign : Fin n → Bool) : List Bool :=
  C.foldl (fun vs g => vs ++ [gateValue vs assign g]) []

/-- Serialize a flat-circuit gate into the shared `(kind, refs)` encoding used by
decoding-based problems (Circuit Value, succinct circuits): kind `0` is an input
variable (refs `[i]`), kind `1` a constant (refs `[b]`, true iff `b = 1`), kind `2`
negation (refs `[a]`), kind `3` conjunction (refs = predecessors), kind `4`
disjunction (refs = predecessors). `mod` gates have no serial encoding here;
they serialize to the all-false gate kind `5`, which evaluates to `false`. -/
def acGateToPair {n : ℕ} : ACGate n → ℕ × List ℕ
  | .var i => (0, [i.val])
  | .const b => (1, [if b then 1 else 0])
  | .notGate a => (2, [a])
  | .andGate l => (3, l)
  | .orGate l => (4, l)
  | .modGate _ _ => (5, [])

/-- Decode a `(kind, refs)` pair into a typed `ACGate`. Kind `5` (unknown/mod)
decodes to `const false`, matching the evaluator's behaviour on unknown kinds.
An out-of-range input index (`i ≥ n`) also decodes to `const false`, matching
the `assign.getD i false` semantics of the serial evaluator: a var gate for a
nonexistent input reads as `false`. -/
def acGateOfPair {n : ℕ} : ℕ × List ℕ → ACGate n
  | (0, [i]) => if h : i < n then .var ⟨i, h⟩ else .const false
  | (1, [b]) => .const (b = 1)
  | (2, [a]) => .notGate a
  | (3, l) => .andGate l
  | (4, l) => .orGate l
  | _ => .const false

/-- The serial `(kind, refs)` evaluator: kinds `0`-`4` as in `acGateToPair`,
anything else `false`. An out-of-range input index reads as `false`. -/
def serialGateEval {n : ℕ} (vs : List Bool) (assign : Fin n → Bool)
    (g : ℕ × List ℕ) : Bool :=
  match g with
  | (0, [i]) => if h : i < n then assign ⟨i, h⟩ else false
  | (1, [b]) => b = 1
  | (2, [a]) => !(vs.getD a false)
  | (3, l) => l.all (fun a => vs.getD a false)
  | (4, l) => l.any (fun a => vs.getD a false)
  | _ => false

/-- Evaluation of the shared `(kind, refs)` encoding agrees with `gateValue` on
decoded gates: the serial evaluator is the typed evaluator. -/
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

/-- Depth of one gate given the depths of earlier gates. -/
def gateDepthOf (ds : List ℕ) {n : ℕ} : ACGate n → ℕ
  | .var _ => 0
  | .const _ => 0
  | .notGate a => ds.getD a 0 + 1
  | .andGate l => List.foldr max 0 (l.map (fun a => ds.getD a 0)) + 1
  | .orGate l => List.foldr max 0 (l.map (fun a => ds.getD a 0)) + 1
  | .modGate _ l => List.foldr max 0 (l.map (fun a => ds.getD a 0)) + 1

/-- Depths of all gates in order. -/
def circuitDepths {n : ℕ} (C : List (ACGate n)) : List ℕ :=
  C.foldl (fun ds g => ds ++ [gateDepthOf ds g]) []

/-- Depth of a circuit: the maximum gate depth. -/
def circuitDepth {n : ℕ} (C : List (ACGate n)) : ℕ :=
  List.foldr max 0 (circuitDepths C)

/-- No `mod` gates. -/
def IsModFree {n : ℕ} (C : List (ACGate n)) : Prop :=
  ∀ g ∈ C, match g with
    | .modGate _ _ => False
    | _ => True

/-- Every `mod` gate has modulus exactly `m`. -/
def ModOnly {n : ℕ} (m : ℕ) (C : List (ACGate n)) : Prop :=
  ∀ g ∈ C, match g with
    | .modGate m' _ => m' = m
    | _ => True

/-- Only `var`, `and`, `or` gates (for monotone circuits). -/
def IsMonotoneCircuit {n : ℕ} (C : List (ACGate n)) : Prop :=
  ∀ g ∈ C, match g with
    | .var _ => True
    | .andGate _ => True
    | .orGate _ => True
    | _ => False

/-- `AC0`: polynomial size, constant depth, no `mod` gates. -/
def AC0 : DecisionComplexityClass :=
  {L | ∃ d, ∃ p : Polynomial ℕ, ∃ C : (n : ℕ) → List (ACGate n),
    ∀ n, WellFormedCircuit (C n) ∧ IsModFree (C n) ∧ (C n).length ≤ p.eval n ∧
      circuitDepth (C n) ≤ d ∧
      ∀ x : List Bool, x.length = n →
        (L x = true ↔
          (circuitEval (C n) (fun i => x.getD (i : ℕ) false)).getLast? = some true)}

/-- `AC0[mod m]`: polynomial size, constant depth, `mod` gates of modulus exactly `m`. -/
def AC0Mod (m : ℕ) : DecisionComplexityClass :=
  {L | ∃ d, ∃ p : Polynomial ℕ, ∃ C : (n : ℕ) → List (ACGate n),
    ∀ n, WellFormedCircuit (C n) ∧ ModOnly m (C n) ∧ (C n).length ≤ p.eval n ∧
      circuitDepth (C n) ≤ d ∧
      ∀ x : List Bool, x.length = n →
        (L x = true ↔
          (circuitEval (C n) (fun i => x.getD (i : ℕ) false)).getLast? = some true)}

/-- `ACC0`: the union over fixed moduli `m` of `AC0[mod m]`.
A circuit family in `ACC0` uses one fixed modulus throughout. -/
def ACC0 : DecisionComplexityClass := ⋃ m, AC0Mod m

/-- The parity language: bitstrings with an odd number of `true` bits. -/
def parityDec : MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x : List Bool => decide ((x.filter fun b => b).length % 2 = 1)

/-- The majority language: bitstrings with more `true` than `false` bits. -/
def majorityDec : MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x : List Bool => decide (2 * (x.filter fun b => b).length > x.length)

/-! ### One-sided-error randomized classes: `RP`, `coRP`, `ZPP` -/

/-- `RP`: randomized polynomial time with one-sided error; acceptance
probability at least `1/2` on yes-instances, `0` on no-instances.
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

/-- `coRP`: complements of `RP` languages.
Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 7.2; M. Sipser, Introduction to the Theory of Computation, 3rd ed.,
2013, Definition 10.8. -/
def coRP : DecisionComplexityClass := {L | Lᶜ ∈ RP}

/-- `L ∈ coRP` iff `Lᶜ ∈ RP`.
Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 7.2. -/
theorem mem_coRP {L : DecisionProblem} : L ∈ coRP ↔ Lᶜ ∈ RP := Iff.rfl

/-- `ZPP`: zero-error probabilistic polynomial time, defined as `RP ∩ coRP`.
Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 7.2 (where `ZPP` is defined as this intersection); M. Sipser,
Introduction to the Theory of Computation, 3rd ed., 2013, Definition 10.8. -/
def ZPP : DecisionComplexityClass := RP ∩ coRP

/-- `ZPP = RP ∩ coRP`, by definition.
Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 7.2. -/
theorem zpp_eq : ZPP = RP ∩ coRP := rfl

/-- `ZPP ⊆ RP`.
Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 7.2. -/
theorem zpp_subset_rp : ZPP ⊆ RP := Set.inter_subset_left

/-- `ZPP ⊆ coRP`.
Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 7.2. -/
theorem zpp_subset_corp : ZPP ⊆ coRP := Set.inter_subset_right

/-! ### Merlin-Arthur: `MA` -/

/-- `MA`: Merlin sends a polynomial-length witness `w` first, then Arthur
flips coins `r`; acceptance probability at least `2/3` on yes-instances
(for some `w`), at most `1/3` on no-instances (for every `w`). The triple
is `(input, witness, random string)`, unlike `AM`'s
`(input, random string, witness)`. `MA ⊆ AM` (by error amplification and a
union bound over Merlin's messages) is a `WantedExt` statement, not proved
here: the same verifier does not work, since `∃ w` after the coins is
strictly more permissive than `∃ w` before them.
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

/-- `coMA`: complements of `MA` languages.
Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 8.1. -/
def coMA : DecisionComplexityClass := {L | Lᶜ ∈ MA}

/-- `L ∈ coMA` iff `Lᶜ ∈ MA`.
Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 8.1. -/
theorem mem_coMA {L : DecisionProblem} : L ∈ coMA ↔ Lᶜ ∈ MA := Iff.rfl

/-! ### `NC`: log-space uniform poly-size polylog-depth circuits -/

/-- Serial encoding of a flat circuit: the list of `(kind, refs)` pairs of
`acGateToPair`.
Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Chapter 6 (circuit encodings). -/
abbrev SerialCircuit := List (ℕ × List ℕ)

/-- Log-space uniformity of a circuit family: a log-space computable
description function maps the unary input `replicate n true` (length `n`) to
the bit-encoding of the serial circuit on `n` inputs, so the description is
computed in space `O(log n)` in the number of inputs.
Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 6.21 (log-space uniformity); M. Sipser, Introduction to the Theory of
Computation, 3rd ed., 2013, Definition 9.20. -/
def UniformCircuitFamily (C : (n : ℕ) → List (ACGate n)) : Prop :=
  ∃ desc : List Bool → List Bool, LogSpaceComputable desc ∧
    ∀ n, MetaMathlibExt.BitstringEncoding.bitDecode
      (desc (List.replicate n true)) = some ((C n).map acGateToPair)

/-- Every `and`/`or`/`mod` gate has at most two predecessors (bounded fan-in).
`NC` requires bounded fan-in: without it, `NCK` would model unbounded-fan-in
`AC^k`, not `NC^k`.
Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 6.21; M. Sipser, Introduction to the Theory of Computation, 3rd ed.,
2013, Definition 9.20. -/
def IsFanInLeTwo {n : ℕ} (C : List (ACGate n)) : Prop :=
  ∀ g ∈ C, match g with
    | .andGate l => l.length ≤ 2
    | .orGate l => l.length ≤ 2
    | .modGate _ l => l.length ≤ 2
    | _ => True

/-- `NC^k`: log-space uniform circuits of polynomial size, bounded fan-in at
most `2`, and depth `O(log^k n)` (the constant factor `c` absorbs the base
case, so `NC^0` is constant depth). No `mod` gates. Bounded fan-in is
essential: with unbounded fan-in this would be `AC^k`, not `NC^k`.
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

/-- `NC`: the union of the `NC^k` levels.
Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 6.21; M. Sipser, Introduction to the Theory of Computation, 3rd ed.,
2013, Definition 9.20. -/
def NC : DecisionComplexityClass := ⋃ k, NCK k

/-- `NC` is the union of the `NC^k` levels, by definition.
Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 6.21. -/
theorem nc_eq : NC = ⋃ k, NCK k := rfl

/-- `L ∈ NC` iff `L ∈ NC^k` for some `k`.
Source: S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 6.21. -/
theorem mem_nc {L : DecisionProblem} : L ∈ NC ↔ ∃ k, L ∈ NCK k := Set.mem_iUnion

/-- `NC^k ⊆ NC^(k+1)`: the depth bound is monotone in `k`, since the base
`log 2 (n + 1) + 1` is at least `1`.
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

/-- A rational number encoded as `(sign, numerator, denominator)`.
Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4 (rational
gate entries). -/
abbrev RatEnc := Bool × ℕ × ℕ

/-- The rational number encoded by a `RatEnc`.
Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4. -/
def toRat (e : RatEnc) : ℚ :=
  (if e.1 then -1 else 1) * (e.2.1 : ℚ) / (e.2.2 : ℚ)

/-- The complex number encoded by a pair of rational encodings (real, imaginary).
Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4. -/
def toComplex (e : RatEnc × RatEnc) : ℂ :=
  ⟨((toRat e.1 : ℚ) : ℝ), ((toRat e.2 : ℚ) : ℝ)⟩

/-- Bit `k` of the natural number `i`, as an element of `Fin 2`.
Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4. -/
def qBit (k i : ℕ) : Fin 2 :=
  ⟨(i / 2 ^ k) % 2, Nat.mod_lt _ (by norm_num)⟩

/-- Index of a pair of `Fin 2` values in the row-major `4 × 4` enumeration.
Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4. -/
def qIdx2 (p : Fin 2 × Fin 2) : ℕ := p.1.val * 2 + p.2.val

/-- The `4 × 4` complex matrix encoded by a list of 16 rational pairs, in row-major
order over `Fin 2 × Fin 2`.
Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4. -/
def matrixOfEntries (entries : List (RatEnc × RatEnc)) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q =>
    toComplex (entries.getD (qIdx2 p * 4 + qIdx2 q) ((false, 0, 1), (false, 0, 1)))

/-- `s` with bits `i` and `j` replaced by the pair `b`, as an index into `Fin (2 ^ N)`.
Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4. -/
def setBits (N s i j : ℕ) (b : Fin 2 × Fin 2) : Fin (2 ^ N) :=
  ⟨(s - (qBit i s).val * 2 ^ i - (qBit j s).val * 2 ^ j +
    b.1.val * 2 ^ i + b.2.val * 2 ^ j) % 2 ^ N, Nat.mod_lt _ (by positivity)⟩

/-- A 2-local quantum gate: the two qubits it acts on, and its `4 × 4` unitary (as a
list of 16 rational pairs of rational encodings).
Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4. -/
abbrev QGate := ℕ × ℕ × List (RatEnc × RatEnc)

/-- A gate is well-formed on `N` qubits if it addresses qubits `i < j < N` and its
matrix is unitary.
Source: A. Y. Kitaev, A. H. Shen, and M. N. Vyalyi, Classical and Quantum
Computation, American Mathematical Society, 2002, Section 14.4. -/
def QGateWellFormed (N : ℕ) (gate : QGate) : Prop :=
  gate.1 < gate.2.1 ∧ gate.2.1 < N ∧
    (star (matrixOfEntries gate.2.2)) * (matrixOfEntries gate.2.2) = 1

/-- Apply a 2-local gate to a state vector.
Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 4 (unitary evolution). -/
def applyGate (N : ℕ) (gate : QGate) (ψ : Fin (2 ^ N) → ℂ) : Fin (2 ^ N) → ℂ :=
  fun s => ∑ b : Fin 2 × Fin 2,
    (matrixOfEntries gate.2.2) (qBit gate.1 s.val, qBit gate.2.1 s.val) b *
      ψ (setBits N s.val gate.1 gate.2.1 b)

/-- Apply a list of gates, in order, to a state vector.
Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 4 (quantum circuits). -/
def applyCircuit (N : ℕ) (gates : List QGate) (ψ : Fin (2 ^ N) → ℂ) :
    Fin (2 ^ N) → ℂ :=
  gates.foldl (fun ψ g => applyGate N g ψ) ψ

/-- The number with binary expansion `bs`, least significant bit first.
Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 1 (computational basis). -/
def qNumOf : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * qNumOf rest

/-- The computational basis state for the classical input `x`.
Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 1 (computational basis). -/
def basisState (x : List Bool) : Fin (2 ^ x.length) → ℂ :=
  fun s => if s.val = qNumOf x then 1 else 0

/-- Tensor product of two state vectors.
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

/-- The all-zero state on `a` qubits.
Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 1 (computational basis). -/
def zeroState (a : ℕ) : Fin (2 ^ a) → ℂ :=
  fun s => if s.val = 0 then 1 else 0

/-- The squared norm of a state vector.
Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 2 (Born rule). -/
def sqNorm {m : ℕ} (ψ : Fin (2 ^ m) → ℂ) : ℝ :=
  ∑ s : Fin (2 ^ m), (starRingEnd ℂ (ψ s) * ψ s).re

/-- The acceptance probability of a state: the squared norm of its part on basis states
with qubit `0` equal to `1` (the output qubit), by the Born rule.
Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 2 (Born rule, measurement). -/
def acceptProb {N : ℕ} (ψ : Fin (2 ^ N) → ℂ) : ℝ :=
  ∑ s : Fin (2 ^ N), if qBit 0 s.val = 1 then (starRingEnd ℂ (ψ s) * ψ s).re else 0

/-- The initial state of a `BQP` computation: input `x` in the computational basis,
`a` ancilla qubits in state `0`.
Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 4 (quantum circuits);
S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Definition 10.1. -/
def bqpInitState (x : List Bool) (a : ℕ) : Fin (2 ^ (x.length + a)) → ℂ :=
  tensorProd (basisState x) (zeroState a)

/-- `BQP`: bounded-error quantum polynomial time; a uniform family of
polynomial-size quantum circuits (2-local unitary gates with rational entries,
generated in polynomial time) whose output qubit measures `1` with probability
at least `2/3` on yes-instances and at most `1/3` on no-instances.
`BQP ⊆ PSPACE` and `BQP ⊆ PP` are `WantedExt` statements: they need the
path-integral / gap simulation of quantum circuits, not just this definition.
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

/-- A maximization optimization problem: a value function, a feasibility
predicate, and a polynomial bound on feasible solution lengths. This is the
lightweight CSLibExt bundle; the computational content (poly-time
feasibility and poly-time objective encoding) is the separate predicate
`IsNPO`, required by `APX`/`PTAS`/`FPTAS`. Values are nonnegative, `0` on
infeasible solutions, and every instance has a feasible solution.
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

/-- `ApproxAt P A k ρ`: algorithm `A` achieves approximation ratio `ρ` on `P`
at precision tape `k`: on every instance, its output on `(x, replicate k true)`
is feasible and worth at least `ρ` times every feasible solution's value
(hence at least `ρ` times the optimum). The shared call convention (algorithm
takes `(instance, unary precision tape)`) is what makes `FPTAS ⊆ PTAS ⊆ APX`
direct: an `FPTAS` algorithm is one algorithm handling every precision tape,
a `PTAS` has one algorithm per tape, and `APX` is the `k = 2` (ratio `1/2`)
case.
Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440; S. Arora and B. Barak, Computational Complexity: A Modern Approach,
2009, Chapter 11. -/
def ApproxAt (P : OptProblem) (A : List Bool × List Bool → List Bool) (k : ℕ)
    (ρ : ℚ) : Prop :=
  ∀ x s, P.feas x s = true →
    ρ * P.val x s ≤ P.val x (A (x, List.replicate k true)) ∧
    P.feas x (A (x, List.replicate k true)) = true

/-- `IsNPO`: the computational content of an `OptProblem`, as in the `MAXSNP`
file's `NPOProblem`: feasibility is polynomial-time, and the objective is
given by a polynomial-time rational encoding `(sign, numerator, denominator)`
whose value equals `val` on feasible solutions and `0` elsewhere, with
nonzero denominator. This is a separate predicate, not a structure field, so
bundles can be stated without first exhibiting the polynomial-time machines,
but the classes `APX`/`PTAS`/`FPTAS` below all require it. Without it, a
bundle could hide an undecidable feasibility relation while assigning value
`0` everywhere, and the constant empty-solution algorithm would vacuously
satisfy the approximation predicates.
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

/-- `APX`: an NPO problem with a polynomial-time constant-factor
approximation. The ratio `ρ` is the fraction of the optimum achieved, in
`(0, 1]` (the reciprocal of the `ρ ≥ 1` convention of the `MAXSNP` file,
where `val ≥ OPT / ρ`). The `IsNPO` conjunct is part of the class: without
it, a non-NPO bundle with value `0` everywhere would vacuously qualify.
Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440; S. Arora and B. Barak, Computational Complexity: A Modern Approach,
2009, Chapter 11. -/
def IsAPX (P : OptProblem) : Prop :=
  IsNPO P ∧ ∃ ρ : ℚ, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ A : List Bool × List Bool → List Bool,
    IsPolyTime A ∧ ApproxAt P A 2 ρ

/-- The class `APX` of optimization problems with a polynomial-time
constant-factor approximation.
Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440. -/
def APX : Set OptProblem := {P | IsAPX P}

/-- `PTAS`: an NPO problem such that for every `k ≥ 1`, a polynomial-time
algorithm achieves ratio `1 - 1 / k` (i.e. error `ε = 1 / k`).
Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440; S. Arora and B. Barak, Computational Complexity: A Modern Approach,
2009, Chapter 11. -/
def IsPTAS (P : OptProblem) : Prop :=
  IsNPO P ∧ ∀ k : ℕ, 1 ≤ k → ∃ A : List Bool × List Bool → List Bool,
    IsPolyTime A ∧ ApproxAt P A k (1 - 1 / (k : ℚ))

/-- The class `PTAS` of optimization problems with a polynomial-time
approximation scheme.
Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440. -/
def PTAS : Set OptProblem := {P | IsPTAS P}

/-- `FPTAS`: an NPO problem with one polynomial-time algorithm achieving
ratio `1 - 1 / k` for every `k ≥ 1`; since the precision tape is unary,
polynomial time in the total input length is polynomial in `|x|` and `1 / ε`.
Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440; S. Arora and B. Barak, Computational Complexity: A Modern Approach,
2009, Chapter 11. -/
def IsFPTAS (P : OptProblem) : Prop :=
  IsNPO P ∧ ∃ A : List Bool × List Bool → List Bool, IsPolyTime A ∧
    ∀ k : ℕ, 1 ≤ k → ApproxAt P A k (1 - 1 / (k : ℚ))

/-- The class `FPTAS` of optimization problems with a fully polynomial-time
approximation scheme.
Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440. -/
def FPTAS : Set OptProblem := {P | IsFPTAS P}

/-- `FPTAS ⊆ PTAS`: the single `FPTAS` algorithm serves every `k`.
Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440. -/
theorem fptas_subset_ptas : FPTAS ⊆ PTAS := by
  intro P hP
  obtain ⟨hNPO, A, hA, hAk⟩ := hP
  exact ⟨hNPO, fun k hk => ⟨A, hA, hAk k hk⟩⟩

/-- `PTAS ⊆ APX`: the `PTAS` algorithm at `k = 2` achieves ratio `1 / 2`.
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

/-- A function `e : ℕ → ℚ` is negligible if it is eventually below `1 / n ^ c` for
every `c`.
Source: O. Goldreich, Foundations of Cryptography, Vol. 1, Cambridge University
Press, 2001, Section 2.2. -/
def Negligible (e : ℕ → ℚ) : Prop :=
  ∀ c : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → e n ≤ 1 / (n : ℚ) ^ c

/-- Inversion success probability of a uniform probabilistic inverter `inv`
against a one-way function family `f` at length `n` with `m` random coins:
the fraction of pairs `(x, coins)` for which decoding
`inv (n, f n x, coins)` back to `n` bits is a genuine preimage of `f n x`.
The inverter receives the security parameter `n` explicitly: for variable
output lengths it could not otherwise recover `n` from `f n x` alone, and
the prefix-by-prefix inversion in the proof of `OWF ⇒ P ≠ NP` needs `n`.
Success is over uniform `x` and uniform coins.
Source: O. Goldreich, Foundations of Cryptography, Vol. 1, Cambridge University
Press, 2001, Section 2.2. -/
noncomputable def invertSucc (f : (n : ℕ) → (Fin n → Bool) → List Bool)
    (inv : ℕ × List Bool × List Bool → List Bool) (n m : ℕ) : ℚ :=
  (Set.ncard {p : (Fin n → Bool) × (Fin m → Bool) |
    f n (fun i => (inv (n, f n p.1, List.ofFn p.2)).getD i.val false) = f n p.1} : ℚ) /
    (2 : ℚ) ^ (n + m)

/-- A one-way function family: polynomially balanced, computed by a single
uniform polynomial-time evaluator on the encoded pair `(n, x)`, and no
uniform polynomial-time probabilistic inverter inverts it with
non-negligible probability. The inverter takes `(n, output, coins)` with
`q.eval n` coins for a polynomial `q` (quantified over all `q`), so
deterministic inverters are the special case ignoring the coins. The
uniform evaluator is essential: per-length polynomial-size circuits would
admit arbitrary noncomputable families. This is the uniform analogue of the
nonuniform `OWFExists` of the five-worlds file.
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

/-- Inversion success probability of a uniform probabilistic inverter `inv`
against a one-way permutation family `π` at length `n` with `m` random
coins: the fraction of pairs `(x, coins)` for which decoding
`inv (n, π n x, coins)` is a genuine preimage under `π`. The inverter
receives the security parameter `n` explicitly, as in `invertSucc`.
Source: O. Goldreich, Foundations of Cryptography, Vol. 1, Cambridge University
Press, 2001, Section 2.2. -/
noncomputable def permInvertSucc (π : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool))
    (inv : ℕ × List Bool × List Bool → List Bool) (n m : ℕ) : ℚ :=
  (Set.ncard {p : (Fin n → Bool) × (Fin m → Bool) |
    π n (fun i => (inv (n, List.ofFn (π n p.1), List.ofFn p.2)).getD i.val false) =
      π n p.1} : ℚ) / (2 : ℚ) ^ (n + m)

/-- A one-way permutation family: injective and length-preserving (a permutation
of `n`-bit strings for each `n`), computed by a single uniform polynomial-time
evaluator, and no uniform polynomial-time probabilistic inverter inverts it
with non-negligible probability. The inverter takes `(n, output, coins)` with
`q.eval n` coins for a polynomial `q` (quantified over all `q`).
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

/-- A one-way permutation is a one-way function: length preservation gives the
polynomial output bound, the evaluator is reused verbatim, and the inversion
success sets coincide, since `List.ofFn` is injective and `π n` is injective,
so `ofFn (π n y) = ofFn (π n x)` iff `π n y = π n x`. The converse direction
(one-way functions yield one-way permutations) is not proved here.
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
