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

/-- The value of MAX-3SAT on instance `x` under assignment `a`: the number of
satisfied clauses (`0` on malformed inputs, and `0` unless `a.length ≤ x.length`).
The bound is the full input length, not the unary variable count `n`: assignments
shorter than `n` and assignments much longer than `n` are both accepted, as long
as they fit in `|x|` bits. The value depends only on the first `n` bits of `a`
(the clause literals index variables `< n` and are evaluated with `getD`), so
padding a solution with trailing bits does not change its value; this matches
`feas_canonical`, under which every `a` with `a.length ≤ bound.eval |x|` (here
`bound = X`) is feasible. -/
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

/-- A bundled NPO (NP optimization) problem: a value function with a polynomial-time
feasibility predicate, a polynomial-time objective encoding, and a polynomial solution
length bound. The objective is `0` on infeasible solutions and nonnegative everywhere.
Every instance has a feasible solution (`feas_nonempty`): without this, completeness
would be impossible, since an `L`-reduction to a problem with no feasible solutions
on some instance would have to map a feasible target output back to a feasible
source solution that does not exist. -/
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

/-- The optimum of an NPO problem `M` on instance `x`, over feasible solutions of
length at most the bound (enumerated as a take-prefix of a full-length bitstring). -/
noncomputable def optVal (M : NPOProblem) (x : List Bool) : ℚ :=
  Finset.max'
    ((Finset.range (M.bound.eval x.length + 1) ×ˢ (Finset.univ :
      Finset (Fin (M.bound.eval x.length) → Bool))).image
      (fun p => M.val x ((List.ofFn p.2).take p.1)))
    (Finset.image_nonempty.mpr ((Finset.nonempty_product.mpr
      ⟨⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩, ⟨fun _ => false, Finset.mem_univ _⟩⟩)))

/-- `APX`: an NPO problem with a polynomial-time constant-factor approximation whose
output is feasible. -/
def APX (M : NPOProblem) : Prop :=
  ∃ (ρ : ℚ) (A : List Bool → List Bool), 1 ≤ ρ ∧ IsPolyTime A ∧
    ∀ x, M.feas x (A x) = true ∧ M.val x (A x) ≥ optVal M x / ρ

/-- `L`-reduction between NPO problems, in the sense of Papadimitriou-Yannakakis:
polynomial-time maps `f` (instances) and `g` (solutions back) with constants `α, β`
preserving optima up to `α` and gaps up to `β`. -/
def LReduces (M₁ M₂ : NPOProblem) : Prop :=
  ∃ (f : List Bool → List Bool) (g : List Bool × List Bool → List Bool) (α β : ℚ),
    IsPolyTime f ∧ IsPolyTime g ∧ 0 < α ∧ 0 < β ∧
    (∀ x, optVal M₂ (f x) ≤ α * optVal M₁ x) ∧
    ∀ x (s₂ : List Bool), M₂.feas (f x) s₂ = true →
      M₁.feas x (g (x, s₂)) = true ∧
        optVal M₁ x - M₁.val x (g (x, s₂)) ≤
          β * (optVal M₂ (f x) - M₂.val (f x) s₂)

/-- `MAXSNP`: an NPO problem in the MAXSNP normal form (Papadimitriou-Yannakakis):
the value is the number of satisfied constraint-windows, where each window is a list
of at most `k` variable indices together with a pattern index, and a fixed finite
family of patterns decides which assigned patterns satisfy each window. The family
is a predicate `accepts : ℕ → List Bool → Bool` between pattern indices and the
assignment restricted to a window; `patCount` bounds the indices. Crucially, the
window list `windows x` depends only on the instance `x`, never on the candidate
solution `s`: a witness that could inspect all of `s` before choosing the windows
could emit arbitrarily many always-accepted empty windows and encode any
polynomially bounded objective, far outside MAXSNP. Only the fixed predicates
`accepts` inspect the selected bits of `s`. The counting equation `val_count`
applies only to feasible solutions (`feas x s = true`): appending arbitrarily
many `false` bits to a solution preserves every `s.getD v false` and hence the
window count, so an unconditional equation would force every such extension to
be feasible (via `val_eq`, since the value is positive) while `feas_len` rejects
sufficiently long extensions, making every `MAXSNPProblem` identically zero.
Feasibility is canonical, not an arbitrary predicate: `feas x s = true` iff
`s` has length at most the bound, i.e. every bounded bitstring is a feasible
solution (`feas_canonical`). An arbitrary poly-time `feas` would admit any
total polynomially balanced search problem packaged with `val = 0` and
`windows = []`, and the claimed `L`-reduction to an `APX` target would then
compose the reduction, the target approximation algorithm, and the solution
map into a poly-time solver for every such search problem, far stronger than
Papadimitriou-Yannakakis `MAXSNP`-completeness. With canonical feasibility,
the value is the fixed local window count on every bounded assignment, and
the only remaining freedom is the local normal form (`windows`, `accepts`),
as in the cited paper. The value on infeasible solutions is `0` by `val_eq`, and feasibility in
the target bundle is exactly length at most `|x|` (see `max3SATVal`,
whose window evaluation reads only the first `n` bits, so padded
extensions of a solution have the same value). The window count
is bounded by a
polynomial in `|x|` (one polynomial for all `x`, per instance the bound is
`q.eval x.length` for a fixed `q` in the `windows_len` field): standard MAXSNP
normal forms sum over all fixed-arity tuples and can have polynomially many terms,
e.g. counting accepted ordered pairs on a unary `n`-element instance has optimum
`n ^ 2`, which a linear bound `|x| + 1` would exclude. The bound is the one
implied by `windows_poly` (a polynomial-time function's output length is
polynomially bounded in its input length); it is stated explicitly so the
structure carries it. -/
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

/-- `MAXSNP`-completeness: in `MAXSNP`, and every `MAXSNP` problem `L`-reduces to it. -/
def MAXSNPComplete (M : MAXSNPProblem) : Prop :=
  APX M.toNPOProblem ∧ ∀ M' : MAXSNPProblem, LReduces M'.toNPOProblem M.toNPOProblem

/-- **MAX-3SAT is MAXSNP-complete.** Source: C. H. Papadimitriou and M.
Yannakakis, "Optimization, approximation, and complexity classes", Journal of Computer
and System Sciences 43 (1991), 425-440. -/
public theorem_wanted max_three_sat_maxsnp_complete :
    ∃ M : MAXSNPProblem, M.val = max3SATVal ∧ MAXSNPComplete M

end MetaMathlibExt.Complexity.KeyTheorems.MaxThreeSATMAXSNPComplete
