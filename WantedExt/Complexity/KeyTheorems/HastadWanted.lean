/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hastad: optimal inapproximability of MAX-3SAT

Source:
J. Håstad, "Some optimal inapproximability results", Journal of the ACM 48 (2001), 798-859
(STOC 1997).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Hastad

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Hastad: optimal inapproximability of MAX-3SAT

Håstad's theorem: MAX-3SAT cannot be approximated in polynomial time within a factor of
`7 / 8 + ε` for any `ε > 0`, unless `P = NP`. The factor `7 / 8` is optimal: a random
assignment satisfies `7 / 8` of the clauses in expectation for valid instances,
so the `7 / 8` approximation is achievable and no better constant is possible
(assuming `P ≠ NP`). The value function is the MAX-3SAT value of the MAXSNP
file: the number of satisfied clauses, `0` on malformed inputs. Valid instances
have exactly three nondegenerate literals per clause: every clause has length
exactly `3`, its three variable indices are pairwise distinct, and no clause
contains both a variable and its negation. Such degeneracies make the
random-assignment satisfaction probability differ from `7 / 8`: a repeated
variable lowers it, e.g. `(x ∨ x ∨ y)` is satisfied with probability `3 / 4`
and `(x ∨ x ∨ x)` with probability `1 / 2`, while a complementary pair makes
the clause a tautology, satisfied with probability `1`. Only with all three
literals distinct and non-complementary is the probability exactly `7 / 8`.  As in the MAXSNP file, the variable count
is given in unary (a bitstring of length `n`), so an assignment of length
`|x|` has at least `n` bits.
-/

/-- **Nondegenerate 3-clauses.** A clause, given as a list of literals $(v, s)$ with variable
index $v \in \mathbb{N}$ and polarity $s$, is nondegenerate if it has exactly three literals,
its variable indices are pairwise distinct, and it contains no complementary pair, that is, no
two literals $(v, s)$ and $(v, \lnot s)$. -/
def hastadNondegenerate (clause : List (ℕ × Bool)) : Bool :=
  decide (clause.length = 3 ∧ (clause.map Prod.fst).Nodup) &&
    !clause.any (fun l => (l.1, !l.2) ∈ clause)

/-- **Value of a MAX-3SAT assignment.** For bitstrings $x$ and $a$, read $a$ as the assignment
giving variable $v$ the value $a_v$ if $v < |a|$ and false otherwise. If $x$ decodes, under the
canonical bitstring decoding, to a pair $(u, \varphi)$ of a bitstring $u$ and a CNF formula
$\varphi$ in which every variable index is less than $|u|$ and every clause is nondegenerate,
then the MAX-3SAT value of $a$ on $x$ is the number of clauses of $\varphi$, counted with
multiplicity, that contain a literal $(v, s)$ whose variable gets the value $s$. Otherwise the
value is $0$.

The bitstring $u$ gives the number of variables in unary. Since degenerate and malformed
instances get value $0$, the $7/8$ random-assignment bound holds on every instance with nonzero
value. -/
def hastadVal (x : List Bool) (a : List Bool) : ℚ :=
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := List Bool × Cslib.Logic.PL.CNF) x with
  | some (u, φ) =>
    if (∀ clause ∈ φ, ∀ l ∈ clause, l.1 < u.length) ∧
        ∀ clause ∈ φ, hastadNondegenerate clause then
      (φ.filter (fun clause =>
        clause.any (fun l => (fun v => a.getD v false) l.1 = l.2))).length
    else 0
  | none => 0

/-- **Optimum of a MAX-3SAT instance.** The MAX-3SAT optimum of a bitstring $x$ is the maximum,
over all bitstrings $a$ of length $|x|$, of the MAX-3SAT value of $a$ on $x$. -/
noncomputable def hastadOpt (x : List Bool) : ℚ :=
  Finset.max' (Finset.univ.image (fun a : Fin x.length → Bool => hastadVal x (List.ofFn a)))
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- **Hastad: optimal inapproximability of MAX-3SAT.** If $\mathsf{P} \ne \mathsf{NP}$, then for
every rational $\varepsilon > 0$ there is no polynomial-time function $A$ from bitstrings to
bitstrings such that, for every bitstring $x$, the bitstring $A(x)$ has the same length as $x$
and the MAX-3SAT value of the assignment $A(x)$ on $x$ is at least $(7/8 + \varepsilon)$ times
the MAX-3SAT optimum of $x$.

Source: J. Håstad, "Some optimal
inapproximability results", Journal of the ACM 48 (2001), 798-859 (STOC 1997). -/
public theorem_wanted hastad_max3sat_inapproximability :
    MetaMathlibExt.ComplexityTheory.P ≠ MetaMathlibExt.ComplexityTheory.NP →
      ∀ ε : ℚ, 0 < ε → ¬ ∃ A : List Bool → List Bool,
        IsPolyTime A ∧ ∀ x, (A x).length = x.length ∧
          hastadVal x (A x) ≥ (7 / 8 + ε) * hastadOpt x

end MetaMathlibExt.Complexity.KeyTheorems.Hastad
