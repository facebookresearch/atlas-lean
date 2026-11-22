/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Path
public import CSLibExt.Computability.SatTimeM
public import Mathlib.Data.List.Dedup

/-!
# Karp reductions on the canonical classes: HAMPATH

Specification module for SAT ≤ HAMPATH (Sipser, Theorem 7.46, for CNF formulas of any clause
width) on `MetaMathlibExt.ComplexityTheory`. It fixes the language and the pure reduction; the
correctness proofs (forward: assignment to path; backward: the normal-path argument), the emitter
machine and NP membership are separate components.

* Instances are PATH instances (`Path.encodeP s t n es`): a digraph on `0, …, n - 1` with `s`, `t`.
* `IsHamPath n es s t p`: `p` lists every vertex exactly once, starts at `s`, ends at `t`, and
  consecutive vertices are joined by arcs (`Path.arc`). `hamPathDec`: some Hamiltonian path exists.
* The construction `toHam φ`, with `m = φ.length` clauses and the distinct variables
  `hamVars φ = (varsOf φ).dedup` (`k` of them):
  - clause `j` is vertex `j`;
  - variable `i` has a diamond: top `hpT m i`, a row `hpR m i l` for `l ≤ 3 m` (separators at
    `l = 3 j`, the pair of clause `j` at `3 j + 1`, `3 j + 2`), and bottom `hpT m (i + 1)`, the
    next top;
  - `hpT m i` points to both row ends, both row ends point to `hpT m (i + 1)`, and row
    neighbours point to each other;
  - if variable `i` occurs positively in clause `j`: `hpR m i (3 j + 1) → j → hpR m i (3 j + 2)`;
    negatively: `hpR m i (3 j + 2) → j → hpR m i (3 j + 1)`;
  - `s = hpT m 0`, `t = hpT m k`, `n = hpT m k + 1`.

  A left-to-right row means "true". `reduceHam` is the reduction on bit strings; undecodable
  inputs go to `noHam` (two vertices, no arcs, `s = t = 0`), a no-instance.
* `DetoursNormal φ p`: every clause vertex `j` of `p` sits between the two vertices of its pair in
  one diamond row. The backward direction splits at this predicate: every Hamiltonian path of
  `toHam φ` has normal detours (Sipser's separator argument), and a Hamiltonian path with normal
  detours traverses each row in one direction and yields a satisfying assignment.
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL

/-- **Hamiltonian paths.** Let $E$ be a list of pairs of natural numbers, viewed as the digraph
on $0, \dots, n - 1$ whose arcs are the pairs in $E$ with both ends below $n$. A list $p$ is a
Hamiltonian path from $s$ to $t$ when it lists each of the vertices $0, \dots, n - 1$ exactly
once, starts at $s$, ends at $t$, and each two consecutive entries of $p$ form an arc. -/
def IsHamPath (n : ℕ) (es : List (ℕ × ℕ)) (s t : ℕ) (p : List ℕ) : Prop :=
  p.Nodup ∧ p.length = n ∧ (∀ v ∈ p, v < n) ∧ p.head? = some s ∧ p.getLast? = some t ∧
    p.IsChain (Path.arc n es)

open Classical in
/-- **The HAMPATH problem.** The decision problem that accepts a bit string $x$ exactly when, for
some $s$, $t$, $n$ and list of pairs $E$, $x$ is the PATH encoding of $s$, $t$ and the digraph on
$0, \dots, n - 1$ with edge list $E$, and this digraph has a Hamiltonian path from $s$ to $t$. -/
noncomputable def hamPathDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  decide (∃ s t n es, Path.encodeP s t n es = x ∧ ∃ p, IsHamPath n es s t p)

/-- **Distinct variables of a formula.** The list of the distinct variables of a CNF formula
$\varphi$, in order of occurrence in $\varphi$, with each variable kept at its last occurrence. -/
def hamVars (φ : CNF) : List ℕ := (varsOf φ).dedup

/-- **Tops of the diamonds.** In the HAMPATH construction with $m$ clauses, the top of
diamond $i$ is the vertex $m + i(3m + 2)$; it is also the bottom of diamond $i - 1$. -/
def hpT (m i : ℕ) : ℕ := m + i * (3 * m + 2)

/-- **Row vertices of a diamond.** In the HAMPATH construction with $m$ clauses, write $T(i)$
for the top of diamond $i$. Row vertex $l$ of diamond $i$ is the number $T(i) + 1 + l$; the row
of diamond $i$ consists of the vertices with $l \le 3m$. -/
def hpR (m i l : ℕ) : ℕ := hpT m i + 1 + l

/-- **Arcs of a variable diamond.** Let $\varphi$ be a CNF formula with $m$ clauses, and write
$T(i)$ for the top of diamond $i$ and $R(i, l)$ for its row vertex $l$. The arcs of diamond $i$
for variable $x$ are $T(i) \to R(i, 0)$, $T(i) \to R(i, 3m)$, $R(i, 0) \to T(i + 1)$ and
$R(i, 3m) \to T(i + 1)$; for every $l < 3m$, both $R(i, l) \to R(i, l + 1)$ and
$R(i, l + 1) \to R(i, l)$; and for every clause $j < m$, the arcs $R(i, 3j + 1) \to j$ and
$j \to R(i, 3j + 2)$ if $x$ occurs positively in clause $j$, and the arcs $R(i, 3j + 2) \to j$
and $j \to R(i, 3j + 1)$ if $x$ occurs negatively in clause $j$. Here $j$ is the vertex of
clause $j$. -/
def diamondEdges (φ : CNF) (i x : ℕ) : List (ℕ × ℕ) :=
  let m := φ.length
  [(hpT m i, hpR m i 0), (hpT m i, hpR m i (3 * m)), (hpR m i 0, hpT m (i + 1)),
    (hpR m i (3 * m), hpT m (i + 1))] ++
  (List.range (3 * m)).flatMap (fun l => [(hpR m i l, hpR m i (l + 1)),
    (hpR m i (l + 1), hpR m i l)]) ++
  (List.range m).flatMap fun j =>
    (if (x, true) ∈ φ.getD j [] then [(hpR m i (3 * j + 1), j), (j, hpR m i (3 * j + 2))]
      else []) ++
    (if (x, false) ∈ φ.getD j [] then [(hpR m i (3 * j + 2), j), (j, hpR m i (3 * j + 1))]
      else [])

/-- **Arcs of the HAMPATH construction.** Let $\varphi$ be a CNF formula and let
$x_0, \dots, x_{k-1}$ be its distinct variables, in the order of the distinct-variable list of
$\varphi$. The arcs of the construction for $\varphi$ are the arcs of diamond $i$ for variable
$x_i$, for $i = 0, \dots, k - 1$, concatenated in this order. -/
def hamEdges (φ : CNF) : List (ℕ × ℕ) :=
  (List.range (hamVars φ).length).flatMap fun i => diamondEdges φ i ((hamVars φ).getD i 0)

/-- **Sipser's HAMPATH instance of a CNF formula.** Let $\varphi$ be a CNF formula with $m$
clauses, numbered $0, \dots, m - 1$, and let $x_0, \dots, x_{k-1}$ be its distinct variables,
in the order of their last occurrences in $\varphi$ (clauses read in order, and the literals of
each clause in order). Put $T_i = m + i(3m + 2)$ and $R_{i,l} = T_i + 1 + l$. The result is the
encoded PATH instance with vertices $0, \dots, T_k$, source $T_0$, target $T_k$, and, for each
$i < k$, the following arcs: the frame arcs $T_i \to R_{i,0}$, $T_i \to R_{i,3m}$,
$R_{i,0} \to T_{i+1}$ and $R_{i,3m} \to T_{i+1}$; the row arcs $R_{i,l} \to R_{i,l+1}$ and
$R_{i,l+1} \to R_{i,l}$ for every $l < 3m$; and, for every clause $j < m$, the arcs
$R_{i,3j+1} \to j$ and $j \to R_{i,3j+2}$ if the literal $x_i$ occurs in clause $j$, and the
arcs $R_{i,3j+2} \to j$ and $j \to R_{i,3j+1}$ if the literal $\neg x_i$ occurs in clause $j$. -/
def toHam (φ : CNF) : List Bool :=
  Path.encodeP (hpT φ.length 0) (hpT φ.length (hamVars φ).length)
    (hpT φ.length (hamVars φ).length + 1) (hamEdges φ)

/-- **A fixed HAMPATH no-instance.** The encoded PATH instance on the two vertices $0$ and $1$,
with no arcs, whose source and target are both $0$.

It is a no-instance of HAMPATH: a Hamiltonian path would visit both vertices and start and end
at $0$, so it would visit $0$ twice. -/
def noHam : List Bool := Path.encodeP 0 0 2 []

/-- **The SAT-to-HAMPATH reduction map.** A bit string $x$ that decodes to a CNF formula
$\varphi$ is sent to Sipser's HAMPATH instance of $\varphi$, and a bit string that does not
decode to a CNF formula is sent to the fixed HAMPATH no-instance (two vertices, no arcs, source
and target $0$). -/
def reduceHam (x : List Bool) : List Bool :=
  match decodeCNF x with
  | some φ => toHam φ
  | none => noHam

/-- **Normal clause detours.** Let $\varphi$ be a CNF formula with $m$ clauses and $k$ distinct
variables, and write $R(i, l)$ for row vertex $l$ of diamond $i$ in the HAMPATH construction for
$\varphi$. A list of vertices $p$ has normal detours when for every clause $j < m$ there is a
diamond $i < k$ such that $p$ contains $R(i, 3j + 1), j, R(i, 3j + 2)$ or
$R(i, 3j + 2), j, R(i, 3j + 1)$ as consecutive entries. -/
def DetoursNormal (φ : CNF) (p : List ℕ) : Prop :=
  ∀ j < φ.length, ∃ i < (hamVars φ).length,
    [hpR φ.length i (3 * j + 1), j, hpR φ.length i (3 * j + 2)] <:+: p ∨
      [hpR φ.length i (3 * j + 2), j, hpR φ.length i (3 * j + 1)] <:+: p

/-! ### Diamond arithmetic -/

/-- **Tops are monotone in the diamond index.** In the HAMPATH construction with $m$ clauses,
if $i \le i'$ then the top of diamond $i$ is at most the top of diamond $i'$. -/
theorem hpT_mono {m i i' : ℕ} (h : i ≤ i') : hpT m i ≤ hpT m i' :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/-- **Row vertices lie below the next top.** In the HAMPATH construction with $m$ clauses, for
every diamond $i$ and every $l \le 3m$, row vertex $l$ of diamond $i$ is a smaller number than
the top of diamond $i + 1$. -/
theorem hpR_lt_hpT_succ {m i l : ℕ} (hl : l ≤ 3 * m) : hpR m i l < hpT m (i + 1) := by
  unfold hpR hpT
  rw [Nat.add_one_mul i]
  omega

end Cslib.Complexity.Karp
