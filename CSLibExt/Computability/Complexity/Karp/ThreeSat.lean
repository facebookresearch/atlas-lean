/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.SatTimeM

/-!
# Karp reductions on the canonical classes: 3SAT and the reduction from SAT

Specification module for SAT ≤ 3SAT on `MetaMathlibExt.ComplexityTheory`. It fixes the language,
the pure reduction, and the stack format the reduction machine produces; the correctness proof,
the machine, and NP membership are separate components.

* `sat3Dec`: binary-index CNF formulas (`Cslib.CookLevin.encodeCNF`) in which every clause has at
  most three literals (`is3`), and which are satisfiable.
* `to3`: clauses of length at most one stay; a clause `a₁ ∨ … ∨ aₖ` with `k ≥ 2` becomes the
  chain `(a₁ ∨ z₁), (¬z₁ ∨ a₂ ∨ z₂), …, (¬z_{k-1} ∨ aₖ)` with fresh variables `zᵢ`. Original
  variable `n` is renamed to `2 n` (`ren`); fresh variable number `u` is `2 ^ (u + 1) + 1`
  (`fresh`, an odd number whose binary code is `true`, `u` times `false`, `true`). Fresh numbers
  are handed out from the last clause backwards (`to3Aux`), the order in which a machine walking
  the token stack `(Cslib.Complexity.SatVerifier.toks φ).reverse` meets the literals.
* `reduce3`: the reduction on bit strings; undecodable input goes to `[]`, which is not in
  `sat3Dec`.

Components:
1. correctness of `to3`: `CNFSat (to3 φ) ↔ CNFSat φ` and `is3 (to3 φ)`;
2. an emitter machine: from the token stack `(toks φ).reverse`, push `encodeCNF (to3 φ)` (so the
   output stack reads it top-first);
3. assembly: `IsPolyTime reduce3`, hence `PolyManyOneRed satDec sat3Dec` and NP-hardness of
   `sat3Dec`; and `sat3Dec ∈ NP` from the SAT verifier with a clause-length filter.
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL

/-- **Three-literal clause test.** For a CNF formula $\varphi$, this Boolean test holds exactly
when every clause of $\varphi$ has at most three literals. -/
def is3 (φ : CNF) : Bool := φ.all fun C => decide (C.length ≤ 3)

open Classical in
/-- **The 3SAT decision problem.** 3SAT accepts a bit string $x$ exactly when $x$ is the binary
code of a satisfiable CNF formula in which every clause has at most three literals. -/
noncomputable def sat3Dec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  decide (∃ φ : CNF, encodeCNF φ = x ∧ is3 φ = true ∧ CNFSat φ)

/-- **Renaming of the original variables.** Variable index $n$ is renamed to $2n$, so the
variables of the original formula get even indices. -/
def ren (n : ℕ) : ℕ := 2 * n

/-- **Fresh variable indices.** For $u \in \mathbb{N}$, the $u$-th fresh variable has index
$2^{u+1} + 1$, an odd number. -/
def fresh (u : ℕ) : ℕ := 2 ^ (u + 1) + 1

/-- **Renaming a literal.** The literal with variable index $n$ and polarity $b$ is renamed to
the literal with variable index $2n$ and the same polarity $b$. -/
def renLit (l : ℕ × Bool) : ℕ × Bool := (ren l.1, l.2)

/-- **The tail of a clause chain.** Write $y_v$ for the variable with index $2^{v+1} + 1$ (the
$v$-th fresh variable), $\ell'$ for a literal $\ell$ whose variable index $n$ is replaced by $2n$
with the same polarity, and $z \ominus j$ for $\max(z - j, 0)$. Given literals
$\ell_1, \dots, \ell_m$ and a natural number $z$, the result is the empty formula if $m = 0$, and
otherwise the $m$ clauses $(\neg y_{z \ominus (i - 1)} \lor \ell_i' \lor y_{z \ominus i})$ for
$i = 1, \dots, m - 1$, followed by $(\neg y_{z \ominus (m - 1)} \lor \ell_m')$.

Here $z$ is the fresh number of the variable asserted by the clause before the tail; fresh
numbers decrease along the chain. -/
def chainTail : List (ℕ × Bool) → ℕ → CNF
  | [], _ => []
  | [l], z => [[(fresh z, false), renLit l]]
  | l :: l' :: ls, z =>
      [(fresh z, false), renLit l, (fresh (z - 1), true)] :: chainTail (l' :: ls) (z - 1)

/-- **The chain of clauses replacing one clause.** Write $y_v$ for the variable with index
$2^{v+1} + 1$ (the $v$-th fresh variable) and $\ell'$ for a literal $\ell$ whose variable index $n$
is replaced by $2n$, with the same polarity. Given a clause $C$ and a natural number $u$, the
empty clause is replaced by the empty clause alone, a one-literal clause $\ell_1$ by the clause
$\ell_1'$, and a clause $\ell_1 \lor \dots \lor \ell_k$ with $k \ge 2$ by the $k$ clauses
$(\ell_1' \lor y_{u+k-2})$, then $(\neg y_{u+k-i} \lor \ell_i' \lor y_{u+k-i-1})$ for
$i = 2, \dots, k - 1$, then $(\neg y_u \lor \ell_k')$. A clause of length $k \ge 2$ thus uses
the fresh numbers $u$ to $u + k - 2$. -/
def chain : CNFClause → ℕ → CNF
  | [], _ => [[]]
  | [l], _ => [[renLit l]]
  | l :: l' :: ls, u =>
      [renLit l, (fresh (u + ls.length), true)] :: chainTail (l' :: ls) (u + ls.length)

/-- **Fresh variables reserved for a clause.** The number of fresh variables reserved for a CNF
clause $C$ in the SAT-to-3SAT translation: $k - 1$ if $C$ has $k \ge 1$ literals, and $0$ if $C$
is empty. -/
def used (C : CNFClause) : ℕ := C.length - 1

/-- **Clause-by-clause translation with a fresh-number counter.** For a CNF formula this returns a
pair $(N, \psi)$ of a natural number $N$ and a CNF formula $\psi$. The empty formula gives $N = 0$
and $\psi$ empty. A formula with first clause $C$ and remaining clauses $\varphi'$, whose pair is
$(N', \psi')$, gives $N = N' + \max(|C| - 1, 0)$ and, as $\psi$, the chain of clauses replacing
$C$ with fresh numbers from $N'$ on, followed by the clauses of $\psi'$.

Fresh numbers are thus handed out from the last clause backwards, and $N$ is the next free one. -/
def to3Aux : CNF → ℕ × CNF
  | [] => (0, [])
  | C :: φ => let r := to3Aux φ; (r.1 + used C, chain C r.1 ++ r.2)

/-- **The SAT-to-3SAT translation.** For a CNF formula with clauses $C_1, \dots, C_m$, the
translation is the concatenation, in order, of the chains of clauses replacing $C_1, \dots, C_m$,
where the chain for $C_i$ uses fresh numbers from $u_i = \sum_{j > i} \max(|C_j| - 1, 0)$ on. -/
def to3 (φ : CNF) : CNF := (to3Aux φ).2

/-- **The SAT-to-3SAT reduction on bit strings.** A bit string that decodes, with no bits left
over, to a CNF formula $\varphi$ is sent to the binary code of the SAT-to-3SAT translation of
$\varphi$; any other bit string is sent to the empty string. -/
def reduce3 (x : List Bool) : List Bool :=
  match decodeCNF x with
  | some φ => encodeCNF (to3 φ)
  | none => []

end Cslib.Complexity.Karp
