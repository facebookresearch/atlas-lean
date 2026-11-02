/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAX-CUT has no PTAS unless P = NP

Source:
C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation, and
complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440 (MAX-CUT is MAXSNP-complete, hence APX-hard); S. Arora and B. Barak,
Computational Complexity: A Modern Approach, 2009, Chapter 11 (APX-hardness
rules out a PTAS unless P = NP).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.MaxCutNoPTAS

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# MAX-CUT has no PTAS unless P = NP

MAX-CUT (maximize the number of edges crossing a cut) is APX-hard, so it has no
polynomial-time approximation scheme unless `P = NP`. This is the
inapproximability entry for the approximation-classes batch: it does not
duplicate the Håstad file (optimal `7/8` inapproximability of MAX-3SAT) or the
MAXSNP file (MAX-3SAT is MAXSNP-complete).

The instance is an adjacency-matrix bitstring: for `n = ⌊√|x|⌋` vertices
`0, …, n - 1`, the bit at position `i * n + j` says whether the unordered pair
`{i, j}` (with `i < j`) is an edge; bits below the diagonal and trailing bits
past `n ^ 2` are ignored. A solution is a bitstring of length exactly `n`
(the cut, one bit per vertex), so every vertex label occurring in the value is
`0 ≤ i < n` and is covered by the solution. This avoids the flaw of an
edge-list encoding with arbitrary vertex labels: for example, an edge-list
encoding of `[(1000, 1001)]` has length `63`, so no feasible solution of length
at most `63` could assign bits to vertices `1000` and `1001` and the formal
optimum would be `0` for a one-edge graph whose MAX-CUT value is `1`.
`IsPTAS` includes `IsNPO`; the `theorem_wanted` proof must therefore establish
`IsNPO maxCut` (feasibility is a length comparison, the objective encoding
decodes the matrix and counts crossing edges, both polynomial-time) as a lemma
before the APX-hardness argument.
-/

/-- **Vertex count of a MAX-CUT instance.** The vertex count of a MAX-CUT instance, a bitstring
$x$ of length $|x|$, is $\lfloor \sqrt{|x|} \rfloor$.

Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440. -/
def maxCutN (x : List Bool) : ℕ := Nat.sqrt x.length

/-- **Feasible MAX-CUT solutions.** A bitstring $s$ is a feasible solution of a MAX-CUT instance
$x$ exactly when the length of $s$ equals the vertex count $\lfloor \sqrt{|x|} \rfloor$ of $x$,
so that $s$ has one bit per vertex.

Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440. -/
def maxCutFeas (x s : List Bool) : Bool := decide (s.length = maxCutN x)

/-- **Value of a MAX-CUT solution.** Let $x$ be a MAX-CUT instance with vertex count
$n = \lfloor \sqrt{|x|} \rfloor$ and let $s$ be a bitstring, with bits indexed from $0$. If $s$
is a feasible solution of $x$ (its length is $n$), the value of $s$ is the number, as a rational
number, of pairs $(i, j)$ with $i < j < n$ such that bit $i n + j$ of $x$ is true and bits $i$
and $j$ of $s$ differ; otherwise the value is $0$.

Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440. -/
def maxCutVal (x s : List Bool) : ℚ :=
  if maxCutFeas x s then
    ((Finset.filter (fun p : ℕ × ℕ => p.1 < p.2 ∧ p.2 < maxCutN x ∧
      x.getD (p.1 * maxCutN x + p.2) false ∧
        (s.getD p.1 false) ≠ (s.getD p.2 false))
      (Finset.range (maxCutN x) ×ˢ Finset.range (maxCutN x))).card : ℚ)
  else 0

/-- **MAX-CUT as an optimization problem.** MAX-CUT is the optimization problem whose instances
are bitstrings $x$, read as an adjacency matrix on $n = \lfloor \sqrt{|x|} \rfloor$ vertices in
which, for $i < j < n$, bit $i n + j$ of $x$ (bits indexed from $0$) says whether $\{i, j\}$ is
an edge. Its feasible solutions for $x$ are the bitstrings of length $n$, one bit per vertex;
the value of a feasible solution $s$ is the number of pairs $i < j < n$ that are edges and
whose bits in $s$ differ, the value of an infeasible solution is $0$, and the polynomial bound
on the length of feasible solutions is $p(m) = m$.

Source: C. H. Papadimitriou and M. Yannakakis, "Optimization, approximation,
and complexity classes", Journal of Computer and System Sciences 43 (1991),
425-440. -/
noncomputable def maxCut : OptProblem where
  val := maxCutVal
  feas := maxCutFeas
  bound := Polynomial.X
  feas_len := fun x s h => by
    unfold maxCutFeas at h
    rw [decide_eq_true_eq] at h
    rw [h]
    simp [Polynomial.eval_X, maxCutN, Nat.sqrt_le_self]
  val_nonneg := fun x s => by
    unfold maxCutVal
    split
    · exact Nat.cast_nonneg _
    · exact le_rfl
  val_infeas := fun x s h => by
    unfold maxCutVal
    have h' : maxCutFeas x s ≠ true := by rw [h]; exact Bool.false_ne_true
    simp [h']
  feas_nonempty := fun x => ⟨List.replicate (maxCutN x) false, by
    simp [maxCutFeas, List.length_replicate]⟩

/-- **MAX-CUT has no PTAS unless P = NP.** If $\mathsf{P} \neq \mathsf{NP}$, then the
optimization problem MAX-CUT does not admit a polynomial-time approximation scheme.

Source: C. H. Papadimitriou and
M. Yannakakis, "Optimization, approximation, and complexity classes", Journal
of Computer and System Sciences 43 (1991), 425-440 (MAX-CUT is MAXSNP-complete,
hence APX-hard); S. Arora and B. Barak, Computational Complexity: A Modern
Approach, 2009, Chapter 11 (APX-hardness rules out a PTAS unless P = NP). -/
public theorem_wanted max_cut_no_ptas :
    P ≠ NP → ¬ IsPTAS maxCut

end MetaMathlibExt.Complexity.KeyTheorems.MaxCutNoPTAS
