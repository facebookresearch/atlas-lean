/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAX-3SAT is MAXSNP-complete

Source:
C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation, and complexity
classes", Journal of Computer and System Sciences 43 (1991), 425-440.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.MaxThreeSATMAXSNPComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# MAX-3SAT is MAXSNP-complete

MAX-3SAT (maximize the number of satisfied clauses of a 3CNF formula) is MAXSNP-complete:
it is in MAXSNP (hence in APX), and every MAXSNP problem `L`-reduces to it. MAXSNP is
the class Papadimitriou and Yannakakis prove completeness for; it is the
`L`-reduction-hardness notion of that paper, not hardness for all of APX (which is a
strictly stronger claim the cited paper does not establish). An `L`-reduction from an
APX problem that is not in MAXSNP is not asserted. An optimization problem is bundled here as an
`NPOProblem`: a value function `val`, a polynomial-time feasibility predicate `feas`,
a polynomial-time objective encoding `enc` (a `(sign, numerator, denominator)` triple,
so the objective is polynomial-time computable as a rational), and a polynomial solution
length bound. `APX` and `L`-reductions quantify only over such bundled NPO problems: over
bare value functions, `APX` would range over noncomputable objectives whose exact
optimum could encode an undecidable predicate, and no polynomial-time `L`-reduction to
MAX-3SAT could exist. An `L`-reduction is the pair of polynomial-time maps `(f, g)` with
constants `α, β` of Papadimitriou-Yannakakis, preserving approximability. The instance
decodes to a unary variable-count bitstring (of length `n`, the number of variables) and
a CNF formula with clauses of at most 3 literals; malformed inputs have value `0`. The
count is unary, not binary, so an assignment of length `|x|` always has at least `n`
bits and the value depends only on its first `n` bits; a binary-encoded count could
exceed `|x|` and force variables beyond the assignment length to `false`. The
completeness here is MAXSNP-completeness (membership in MAXSNP, hence in APX, plus
`L`-reduction hardness for MAXSNP problems), not APX-completeness: hardness for
every APX problem is not asserted.
-/

/-- **The MAX-3SAT objective.** The value of MAX-3SAT on an instance $x$ under an assignment $a$,
both bitstrings, is defined as follows. Suppose $x$ decodes, under the canonical bitstring
encoding, to a pair $(u, \varphi)$ of a bitstring $u$ and a CNF formula $\varphi$, and suppose
moreover that $|a| \le |x|$, that every literal of $\varphi$ has variable index less than $|u|$
and that every clause of $\varphi$ has at most $3$ literals. Then the value is the number of
clauses of $\varphi$, counted with multiplicity, that contain a literal $(v, b)$ with $a_v = b$,
where $a_v$ is the bit of $a$ at position $v$ (counting from $0$), read as false when
$v \ge |a|$. In every other case the value is $0$.

The length of $u$ is the number of variables, so the value reads only $a_v$ for $v < |u|$:
padding an assignment with trailing false bits, or padding an assignment of length at least
$|u|$ with arbitrary trailing bits, does not change its value as long as its length stays at
most $|x|$. -/
def max3SATVal (x : List Bool) (a : List Bool) : ℚ :=
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := List Bool × Cslib.Logic.PL.CNF) x with
  | some (u, φ) =>
    if a.length ≤ x.length ∧
        (∀ clause ∈ φ, ∀ l ∈ clause, l.1 < u.length) ∧
        ∀ clause ∈ φ, clause.length ≤ 3 then
      (φ.filter (fun clause =>
        clause.any (fun l => (fun v => a.getD v false) l.1 = l.2))).length
    else 0
  | none => 0

/-- **NPO problems.** An NPO (NP optimization) problem consists of a rational-valued value
function $v$, a Boolean feasibility predicate $F$ and an objective encoding $e$, each taking an
instance $x$ and a solution $s$ (both bitstrings), together with a polynomial $b$ with
natural-number coefficients, such that the following hold. $F$ and $e$ are polynomial-time
computable. For all $x$ and $s$, $e(x, s)$ is a triple $(\sigma, p, q)$ of a Boolean $\sigma$
and natural numbers $p$ and $q$ with $q \ne 0$; if $s$ is feasible for $x$ (that is,
$F(x, s)$ is true), then $v(x, s) = -p/q$ when $\sigma$ is true and $v(x, s) = p/q$ when
$\sigma$ is false, and otherwise $v(x, s) = 0$; and $v(x, s) \ge 0$. Every feasible solution
$s$ for $x$ has $|s| \le b(|x|)$, and every instance $x$ has a feasible solution.

Feasible solutions on every instance are needed for completeness: an L-reduction to a problem
with no feasible solutions on some instance would have to map a feasible target output back to
a feasible source solution that does not exist. -/
structure NPOProblem where
  /-- The objective value of solution `s` for instance `x`. -/
  val : List Bool → List Bool → ℚ
  /-- The feasibility predicate: whether solution `s` is feasible for instance `x`.
  For `MAXSNP` problems this is canonical: every bitstring of length at most
  the bound is feasible (see `feas_canonical` on `MAXSNPProblem`). -/
  feas : List Bool → List Bool → Bool
  /-- The objective encoding: `(sign, numerator, denominator)` of the rational value. -/
  enc : List Bool × List Bool → (Bool × ℕ × ℕ)
  /-- A polynomial bound on feasible solution lengths. -/
  bound : Polynomial ℕ
  feas_poly : IsPolyTime (fun p : List Bool × List Bool => feas p.1 p.2)
  enc_poly : IsPolyTime enc
  feas_len : ∀ x s, feas x s = true → s.length ≤ bound.eval x.length
  val_eq : ∀ x s, val x s =
    if feas x s then
      (if (enc (x, s)).1 then -1 else 1) * ((enc (x, s)).2.1 : ℚ) / (enc (x, s)).2.2
    else 0
  val_nonneg : ∀ x s, 0 ≤ val x s
  den_ne : ∀ x s, (enc (x, s)).2.2 ≠ 0
  feas_nonempty : ∀ x, ∃ s, feas x s = true

/-- **Optimum of an NPO problem.** The optimum of an NPO problem $M$, with value function $v$ and
solution length bound $b$, on an instance $x$ is the maximum of $v(x, s)$ over all bitstrings $s$
with $|s| \le b(|x|)$.

Since every feasible solution has length at most $b(|x|)$, every instance has a feasible
solution, and $v$ is nonnegative and equals $0$ on infeasible solutions, this is the maximum of
$v(x, s)$ over the feasible solutions $s$ for $x$. -/
noncomputable def optVal (M : NPOProblem) (x : List Bool) : ℚ :=
  Finset.max'
    ((Finset.range (M.bound.eval x.length + 1) ×ˢ (Finset.univ :
      Finset (Fin (M.bound.eval x.length) → Bool))).image
      (fun p => M.val x ((List.ofFn p.2).take p.1)))
    (Finset.image_nonempty.mpr ((Finset.nonempty_product.mpr
      ⟨⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩, ⟨fun _ => false, Finset.mem_univ _⟩⟩)))

/-- **Membership in APX.** An NPO problem $M$ is in APX when there are a rational number
$\rho \ge 1$ and a polynomial-time computable map $A$ from bitstrings to bitstrings such that, for
every instance $x$, the solution $A(x)$ is feasible for $x$ in $M$ and its value is at least
$\mathrm{opt}_M(x) / \rho$, where $\mathrm{opt}_M(x)$ is the optimum of $M$ on $x$. -/
def APX (M : NPOProblem) : Prop :=
  ∃ (ρ : ℚ) (A : List Bool → List Bool), 1 ≤ ρ ∧ IsPolyTime A ∧
    ∀ x, M.feas x (A x) = true ∧ M.val x (A x) ≥ optVal M x / ρ

/-- **L-reductions.** Write $\mathrm{opt}_M(x)$ for the optimum of an NPO problem $M$ on an
instance $x$ and $v_M(x, s)$ for the value of a solution $s$ for $x$. An NPO problem $M_1$
L-reduces to an NPO problem $M_2$ when there are polynomial-time computable maps $f$, from
bitstrings to bitstrings, and $g$, from pairs of bitstrings to bitstrings, and rational numbers
$\alpha > 0$ and $\beta > 0$, such that for every instance $x$ the following hold. First,
$\mathrm{opt}_{M_2}(f(x)) \le \alpha \, \mathrm{opt}_{M_1}(x)$. Second, for every solution $s$
that is feasible for $f(x)$ in $M_2$, the solution $g(x, s)$ is feasible for $x$ in $M_1$ and
$\mathrm{opt}_{M_1}(x) - v_{M_1}(x, g(x, s)) \le
\beta \, (\mathrm{opt}_{M_2}(f(x)) - v_{M_2}(f(x), s))$.

This is the L-reduction of Papadimitriou and Yannakakis, with polynomial-time maps $f$ and $g$. -/
def LReduces (M₁ M₂ : NPOProblem) : Prop :=
  ∃ (f : List Bool → List Bool) (g : List Bool × List Bool → List Bool) (α β : ℚ),
    IsPolyTime f ∧ IsPolyTime g ∧ 0 < α ∧ 0 < β ∧
    (∀ x, optVal M₂ (f x) ≤ α * optVal M₁ x) ∧
    ∀ x (s₂ : List Bool), M₂.feas (f x) s₂ = true →
      M₁.feas x (g (x, s₂)) = true ∧
        optVal M₁ x - M₁.val x (g (x, s₂)) ≤
          β * (optVal M₂ (f x) - M₂.val (f x) s₂)

/-- **MAXSNP problems.** A MAXSNP problem, in the normal form of Papadimitriou and
Yannakakis, is an NPO problem $M$, with value function $v$ and solution length bound $b$,
together with natural numbers $k$ and $N$, a polynomial-time computable map $W$ sending each
instance $x$ to a list $W(x)$ of windows, each a pair $(w, j)$ of a list
$w = (w_1, \dots, w_m)$ of natural numbers (variable indices) and a natural number $j$ (a
pattern index), and a function $\mathrm{acc}$ assigning a truth value to each pair of a natural
number and a bitstring, such that the following hold. There is a polynomial $q$ with
natural-number coefficients such that $W(x)$ has at most $q(|x|)$ entries for every instance
$x$. Every window $(w, j)$ in $W(x)$ has $|w| \le k$ and $j < N$. A bitstring $s$ is a feasible
solution for $x$ exactly when $|s| \le b(|x|)$. For every feasible solution $s$ for $x$, the
value $v(x, s)$ is the number of entries $(w, j)$ of the list $W(x)$, counted with
multiplicity, for which $\mathrm{acc}(j, (s_{w_1}, \dots, s_{w_m}))$ is true, where $s_i$ is
the bit of $s$ at position $i$ (counting from $0$), read as false when $i \ge |s|$.

The windows depend only on the instance, never on the candidate solution: only the fixed
predicate $\mathrm{acc}$ inspects bits of the solution. The counting equation is required only
for feasible solutions, because padding a solution with false bits preserves the window count
while sufficiently long paddings are infeasible. -/
structure MAXSNPProblem extends NPOProblem where
  /-- The maximum number of variables any single constraint window inspects. -/
  k : ℕ
  /-- The number of pattern indices in the fixed finite pattern family. -/
  patCount : ℕ
  /-- The constraint windows of an instance: each window lists variable indices plus a pattern index. -/
  windows : List Bool → List (List ℕ × ℕ)
  /-- Whether pattern `j` accepts the assignment restricted to a window. -/
  accepts : ℕ → List Bool → Bool
  windows_poly : IsPolyTime windows
  windows_len : ∃ q : Polynomial ℕ, ∀ x, (windows x).length ≤ q.eval x.length
  windows_width : ∀ x, ∀ w ∈ windows x, w.1.length ≤ k ∧ w.2 < patCount
  val_count : ∀ x s, feas x s = true →
    val x s =
      ((windows x).filter (fun w =>
        accepts w.2 (w.1.map (fun v => s.getD v false)) = true)).length
  feas_canonical : ∀ x s, feas x s = (decide (s.length ≤ bound.eval x.length))

/-- **MAXSNP-completeness.** A MAXSNP problem $M$ is MAXSNP-complete when its underlying NPO
problem is in APX and, for every MAXSNP problem $M'$, the underlying NPO problem of $M'$
L-reduces to the underlying NPO problem of $M$. -/
def MAXSNPComplete (M : MAXSNPProblem) : Prop :=
  APX M.toNPOProblem ∧ ∀ M' : MAXSNPProblem, LReduces M'.toNPOProblem M.toNPOProblem

/-- **MAX-3SAT is MAXSNP-complete.** There is a MAXSNP problem whose value function is the
MAX-3SAT value function and which is MAXSNP-complete: its underlying NPO problem is in APX, and
the underlying NPO problem of every MAXSNP problem L-reduces to it.

Source: C. H. Papadimitriou and M.
Yannakakis, "Optimization, approximation, and complexity classes", Journal of Computer
and System Sciences 43 (1991), 425-440. -/
public theorem_wanted max_three_sat_maxsnp_complete :
    ∃ M : MAXSNPProblem, M.val = max3SATVal ∧ MAXSNPComplete M

end MetaMathlibExt.Complexity.KeyTheorems.MaxThreeSATMAXSNPComplete
