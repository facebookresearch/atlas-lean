/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Multiset.Bind
public import Mathlib.Logic.Relation
public import MathlibExt.NumberTheory.Digits.Permutiple
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Tactic.Ring

/-!
# A multigraph characterization of permutiple strings (Holt)

Statements from Benjamin V. Holt, *A Multigraph Characterization of Permutiple
Strings*, INTEGERS 25 (2025), Article A111 (arXiv:2505.11414).

Permutiples, their digit functions `d : Fin (k + 1) → ℕ` and their carries are those
of `MathlibExt.NumberTheory.Digits.Permutiple` (`IsPermutiple`,
`permutipleCarry`), and so is the mother graph `IsMotherGraphEdge` (Definition 4 here,
Definition 4 of Article A13). Inputs of the `(n, b)`-Hoey-Sloane machine are ordered digit pairs
`(d₁, d₂) : ℕ × ℕ`; its states are the carries `0 ≤ c < n`. A cycle of the mother
graph is given by its list of vertices `[v₀, …, v_{r-1}]`, whose edges are
`(v_i, v_{i+1 mod r})`; a multiset of such lists stands for the multiset `I` of cycle
indices of the paper (rotations of a list give the same edge multiset).
-/

namespace MetaMathlibExt

@[expose] public section

/-- Membership in the mother graph is decidable.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Definition 4. -/
public instance instDecidableIsMotherGraphEdge_wantedExt (n b d₁ d₂ : ℕ) :
    Decidable (IsMotherGraphEdge n b d₁ d₂) := by
  unfold IsMotherGraphEdge
  infer_instance

/-- **Sample edges of the $(4, 10)$-mother graph.** In the $(4, 10)$-mother graph, $(2, 8)$ and
$(9, 9)$ are edges and $(2, 1)$ is not. With $\lambda$ the least non-negative residue modulo
ten, $\lambda(2 + 6 \cdot 8) = 0 \le 3$ and $\lambda(9 + 6 \cdot 9) = 3 \le 3$, while
$\lambda(2 + 6 \cdot 1) = 8 > 3$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Definition 4 and Example 1. -/
public theorem isMotherGraphEdge_four_ten :
    IsMotherGraphEdge 4 10 2 8 ∧ IsMotherGraphEdge 4 10 9 9 ∧ ¬ IsMotherGraphEdge 4 10 2 1 := by
  decide

/-- **Transitions of the Hoey-Sloane machine.** Let $n$, $b$, $c_1$, $c_2$, $d_1$ and $d_2$ be
natural numbers. The input $e = (d_1, d_2)$ moves state $c_1$ to state $c_2$ in one transition of
the $(n, b)$-Hoey-Sloane machine $\Gamma$ when $c_1 < n$, $c_2 < n$, $(d_1, d_2)$ is an edge of
the $(n, b)$-mother graph, and $b c_2 - c_1 = n d_2 - d_1$ in the integers (Equation (1)).

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 2.3, Equation (1). -/
public def IsHoeySloaneStep (n b c₁ c₂ : ℕ) (e : ℕ × ℕ) : Prop :=
  c₁ < n ∧ c₂ < n ∧ IsMotherGraphEdge n b e.1 e.2 ∧ (b : ℤ) * c₂ - c₁ = (n : ℤ) * e.2 - e.1

/-- Transitions of the Hoey-Sloane machine are decidable.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 2.3, Equation (1). -/
public instance instDecidableIsHoeySloaneStep (n b c₁ c₂ : ℕ) (e : ℕ × ℕ) :
    Decidable (IsHoeySloaneStep n b c₁ c₂ e) := by
  unfold IsHoeySloaneStep
  infer_instance

/-- **Uniqueness of Hoey-Sloane transitions.** Let $n \le b$. If an input $e$ moves state $c_1$
to state $c_2$ and also moves state $\hat c_1$ to state $\hat c_2$, each in one transition of the
$(n, b)$-Hoey-Sloane machine, then $c_1 = \hat c_1$ and $c_2 = \hat c_2$.

The paper assumes $1 < n < b$; here it is weakened to $n \le b$. For $n > b$ the claim can fail:
for $n = 3$ and $b = 1$ the input $(0, 0)$ moves $0$ to $0$ and also $1$ to $1$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Theorem 5 (`integers-2025-A111-thm-5`). -/
public theorem isHoeySloaneStep_unique (n b : ℕ) (hnb : n ≤ b) {c₁ c₂ ĉ₁ ĉ₂ : ℕ}
    {e : ℕ × ℕ} (h : IsHoeySloaneStep n b c₁ c₂ e) (ĥ : IsHoeySloaneStep n b ĉ₁ ĉ₂ e) :
    c₁ = ĉ₁ ∧ c₂ = ĉ₂ := by
  -- The digit difference has incoming carry as remainder and negated outgoing carry as quotient.
  have divMod {x y : ℕ} (step : IsHoeySloaneStep n b x y e) :
      ((e.1 : ℤ) - n * e.2) / b = -(y : ℤ) ∧ ((e.1 : ℤ) - n * e.2) % b = x := by
    obtain ⟨hx, _, _, he⟩ := step
    apply (Int.ediv_emod_unique (by omega : 0 < (b : ℤ))).2
    rw [mul_neg]
    exact ⟨by omega, Int.natCast_nonneg _, by exact_mod_cast hx.trans_le hnb⟩
  obtain ⟨hq, hr⟩ := divMod h
  obtain ⟨h'q, h'r⟩ := divMod ĥ
  omega

/-- **Runs of the Hoey-Sloane machine.** Let $n$, $b$, $c$ and $c'$ be natural numbers and let
$s = e_1 e_2 \cdots e_m$ be a finite string of inputs, each a pair of natural numbers. The
$(n, b)$-Hoey-Sloane machine can go from state $c$ to state $c'$ reading $s$ from left to right
when there are natural numbers $c_0, c_1, \dots, c_m$ with $c_0 = c$ and $c_m = c'$ such that,
for each $1 \le i \le m$, the input $e_i$ moves state $c_{i-1}$ to state $c_i$ in one transition
of the $(n, b)$-Hoey-Sloane machine. For the empty string ($m = 0$) this says $c = c'$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 2.3. -/
public def IsHoeySloaneRun (n b : ℕ) : ℕ → List (ℕ × ℕ) → ℕ → Prop
  | c, [], c' => c = c'
  | c, e :: s, c' => ∃ c₂, IsHoeySloaneStep n b c c₂ e ∧ IsHoeySloaneRun n b c₂ s c'

/-- **Language of the Hoey–Sloane machine.** For natural numbers $n$ and $b$, the language
$L$ of the $(n, b)$-Hoey–Sloane machine is the set of strings $s$ of pairs of natural
numbers such that the machine, reading $s$ from left to right, can go from state $0$ to
state $0$. In particular the empty string belongs to $L$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 2.3. -/
public def hoeySloaneLanguage (n b : ℕ) : Set (List (ℕ × ℕ)) :=
  {s | IsHoeySloaneRun n b 0 s 0}

/-- **A word in the $(4, 10)$-Hoey-Sloane language.** The input string
$(2, 8)(1, 7)(9, 9)(7, 1)(8, 2)$ belongs to the language of the $(4, 10)$-Hoey-Sloane machine:
reading it from left to right, the machine can go from state $0$ to state $0$.

Writing $87912 = (d_4, \dots, d_0)_{10}$ and letting $\sigma$ be the digit reversal
$\sigma(j) = 4 - j$, so that $87912 = 4 \cdot (d_{\sigma(4)}, \dots, d_{\sigma(0)})_{10}$ is
$4 \cdot 21978$, the inputs are the pairs $(d_j, d_{\sigma(j)})$ for $j = 0, \dots, 4$; an
accepting run passes through the states $0, 3, 3, 3, 0, 0$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 2.3 and Example 2. -/
public theorem mem_hoeySloaneLanguage_87912 :
    [(2, 8), (1, 7), (9, 9), (7, 1), (8, 2)] ∈ hoeySloaneLanguage 4 10 := by
  refine ⟨3, by decide, 3, by decide, 3, by decide, 0, by decide, 0, by decide, rfl⟩

/-- **Permutiple strings.** Let $n$ and $b$ be natural numbers, and for natural numbers
$a_0, \dots, a_k$ write $(a_k, \dots, a_0)_b = \sum_{j=0}^{k} a_j b^j$. A string $s$ of inputs
(pairs of natural numbers) is an $(n, b)$-permutiple string when it belongs to the language $L$ of
the $(n, b)$-Hoey-Sloane machine and there are a natural number $k$, natural numbers
$d_0, \dots, d_k$ and a permutation $\sigma$ of $\{0, \dots, k\}$ such that $(d_k, \dots, d_0)_b$
is an $(n, b, \sigma)$-permutiple, that is, every $d_j$ is less than $b$ and
$(d_k, \dots, d_0)_b = n (d_{\sigma(k)}, \dots, d_{\sigma(0)})_b$, and
$s = (d_0, d_{\sigma(0)})(d_1, d_{\sigma(1)}) \cdots (d_k, d_{\sigma(k)})$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 2.3. -/
public def IsPermutipleString (n b : ℕ) (s : List (ℕ × ℕ)) : Prop :=
  s ∈ hoeySloaneLanguage n b ∧
    ∃ (k : ℕ) (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))),
      IsPermutiple n b d σ ∧ s = List.ofFn fun j => (d j, d (σ j))

/-- **Inputs of a permutiple string lie on mother-graph cycles.** Let $1 < n < b$ and let $s$ be
an $(n, b)$-permutiple string. Then every input $(d, \hat d)$ of $s$ is an edge of the
$(n, b)$-mother graph, and $\hat d$ reaches $d$ along a (possibly empty) directed path in the
graph whose edges are the inputs of $s$, so $(d, \hat d)$ lies on a directed cycle of that graph.
In this sense the inputs of $s$ form a union of cycles of the mother graph.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Corollary 1 (`integers-2025-A111-cor-1`), quoting Holt,
*Finding Permutiples of a Known Base and Multiplier*. -/
public theorem isPermutipleString_inputs_isUnion_motherGraphCycles (n b : ℕ) (hn : 1 < n)
    (hnb : n < b) {s : List (ℕ × ℕ)} (hs : IsPermutipleString n b s) (e : ℕ × ℕ)
    (he : e ∈ s) :
    IsMotherGraphEdge n b e.1 e.2 ∧ Relation.ReflTransGen (fun u v => (u, v) ∈ s) e.2 e.1 := by
  obtain ⟨_, k, d, σ, hp, hs⟩ := hs
  have hinput (i : Fin (k + 1)) : (d i, d (σ i)) ∈ s := by
    rw [hs]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  rw [hs] at he
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
  constructor
  · refine ⟨hp.1 j, hp.1 (σ j), ?_⟩
    simpa using permutiple_basePerm_residue_le n b hn.le (hn.trans hnb) d σ 1 σ hp hp j
  · -- Positions whose digits are reachable from d (σ j) are closed under σ and hence σ⁻¹.
    let reachable (i : Fin (k + 1)) :=
      Relation.ReflTransGen (fun u v => (u, v) ∈ s) (d (σ j)) (d i)
    have forward (i : Fin (k + 1)) (hi : reachable i) : reachable (σ i) :=
      hi.tail (hinput i)
    have start : reachable (σ j) := .refl
    simpa only [Equiv.symm_apply_apply] using
      Equiv.Perm.perm_symm_on_of_perm_on_finite forward start

/-- **The permutiple string of $87912 = 4 \cdot 21978$.** The string of inputs
$(2, 8)(1, 7)(9, 9)(7, 1)(8, 2)$ is a $(4, 10)$-permutiple string. It is produced by the
$(4, 10)$-permutiple $87912 = 4 \cdot 21978$, whose multiplication reverses the digits.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 2.3 and Table 1. -/
public theorem isPermutipleString_87912 :
    IsPermutipleString 4 10 [(2, 8), (1, 7), (9, 9), (7, 1), (8, 2)] :=
  ⟨mem_hoeySloaneLanguage_87912, 4, ![2, 1, 9, 7, 8], Fin.revPerm, isPermutiple_87912,
    by decide⟩

/-- **Edge list of a closed walk.** For a list $[v_0, \dots, v_{r-1}]$ of natural numbers,
read as the vertex list of a closed walk, the edge list is
$[(v_0, v_1), \dots, (v_{r-2}, v_{r-1}), (v_{r-1}, v_0)]$: each vertex is paired with the
next one, and the last vertex with the first. A single vertex $[v_0]$ gives the loop
$[(v_0, v_0)]$, and the empty list gives the empty edge list.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Definition 5 (cycles of `M`). -/
public def cycleEdges (vs : List ℕ) : List (ℕ × ℕ) :=
  vs.zip (vs.rotate 1)

/-- **Edges of the closed walks $2 \to 8 \to 2$ and $9 \to 9$.** The closed walk with vertex
list $[2, 8]$ has edge list $[(2, 8), (8, 2)]$, and the closed walk with vertex list $[9]$
(a loop at $9$) has edge list $[(9, 9)]$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Example 2. -/
public theorem cycleEdges_examples :
    cycleEdges [2, 8] = [(2, 8), (8, 2)] ∧ cycleEdges [9] = [(9, 9)] := by
  decide

/-- **Cycles of the mother graph.** Let $n$ and $b$ be natural numbers. A list
$[v_0, \dots, v_{r-1}]$ of natural numbers is a (directed) cycle of the $(n, b)$-mother graph when
it is nonempty, has no repeated entry, and each of its edges
$(v_0, v_1), \dots, (v_{r-2}, v_{r-1}), (v_{r-1}, v_0)$ is an edge of the $(n, b)$-mother graph.
In particular a one-element list $[v]$ is a cycle when $(v, v)$ is an edge of the mother graph.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Definition 5 (cycles of `M`). -/
public def IsMotherGraphCycle (n b : ℕ) (vs : List ℕ) : Prop :=
  vs ≠ [] ∧ vs.Nodup ∧ ∀ e ∈ cycleEdges vs, IsMotherGraphEdge n b e.1 e.2

/-- **Multiset union of cycle edges.** For a multiset $I$ of lists of natural numbers, each
read as the vertex list of a closed walk, write $C_j$ for the edge list of $j \in I$. The
multiset union $C_I = \biguplus_{j \in I} C_j$ is the multiset of all these edges, counted
with multiplicity: each list $j$ contributes its edges as often as $j$ occurs in $I$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 2.3 (multiset cycle union `C_I`). -/
public def cycleUnion (cs : Multiset (List ℕ)) : Multiset (ℕ × ℕ) :=
  cs.bind fun vs => (cycleEdges vs : Multiset (ℕ × ℕ))

/-- **Hoey–Sloane transition of a digit pair.** For natural numbers $n$ and $b$ and a pair
$e = (d_1, d_2)$ of natural numbers, the multi-edge of the $(n, b)$-Hoey–Sloane multigraph
carrying the label $e$ is $(c_1, c_2)$, where $c_1 = \lambda(d_1 + (b - n) d_2)$ with
$\lambda$ the least non-negative residue modulo $b$ (computed in the integers), and
$c_2 = \lfloor (n d_2 - d_1 + c_1) / b \rfloor$, replaced by $0$ when negative. For $b = 0$
the conventions are $x \bmod 0 = x$ and $x / 0 = 0$, and $c_1$ is likewise replaced by $0$
when negative.

For an edge $e$ of the $(n, b)$-mother graph with $1 < n < b$, the source shows that
$(c_1, c_2)$ is the unique solution of $b c_2 - c_1 = n d_2 - d_1$ with
$0 \le c_1, c_2 \le n - 1$, that is, the transition of the Hoey–Sloane machine with input $e$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Definition 6 and the proof of Theorem 6. -/
public def hoeySloaneTransition (n b : ℕ) (e : ℕ × ℕ) : ℕ × ℕ :=
  let c₁ : ℤ := ((e.1 : ℤ) + ((b : ℤ) - n) * e.2) % b
  (c₁.toNat, (((n : ℤ) * e.2 - e.1 + c₁) / b).toNat)

/-- **Hoey-Sloane transitions are transitions of the machine.** Let $1 < n < b$, let
$e = (d_1, d_2)$ be an edge of the $(n, b)$-mother graph, and let $(c_1, c_2)$ be the Hoey-Sloane
transition of $e$, that is, $c_1 = \lambda(d_1 + (b - n) d_2)$ and $c_2 = (n d_2 - d_1 + c_1) / b$,
where $\lambda$ is the least non-negative residue modulo $b$. Then the input $e$ moves state $c_1$
to state $c_2$ in one transition of the $(n, b)$-Hoey-Sloane machine.

By the uniqueness of Hoey-Sloane transitions (Theorem 5), it is the only transition labelled
by $e$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Definition 6, from Theorems 5 and 6
(`integers-2025-A111-thm-6`). -/
public theorem isHoeySloaneStep_hoeySloaneTransition (n b : ℕ) (hn : 1 < n) (hnb : n < b)
    (e : ℕ × ℕ) (he : IsMotherGraphEdge n b e.1 e.2) :
    IsHoeySloaneStep n b (hoeySloaneTransition n b e).1 (hoeySloaneTransition n b e).2 e := by
  let c₁ := ((e.1 : ℤ) + ((b : ℤ) - n) * e.2) % b
  let c₂ := ((n : ℤ) * e.2 - e.1 + c₁) / b
  have hb : 0 < (b : ℤ) := by omega
  have hc₁ : 0 ≤ c₁ := Int.emod_nonneg _ hb.ne'
  have hc₁_lt : c₁ ≤ (n : ℤ) - 1 := he.2.2
  -- The incoming carry makes the numerator of the outgoing carry divisible by the base.
  have hdvd : (b : ℤ) ∣ (n : ℤ) * e.2 - e.1 + c₁ := by
    use (e.2 : ℤ) - (((e.1 : ℤ) + ((b : ℤ) - n) * e.2) / b)
    dsimp only [c₁]
    rw [Int.emod_def]
    ring
  have hcarry : (b : ℤ) * c₂ = n * e.2 - e.1 + c₁ := Int.mul_ediv_cancel' hdvd
  have lower : -1 < c₂ := by
    apply (mul_lt_mul_iff_right₀ hb).mp
    rw [hcarry, mul_neg_one]
    have hd₁ : (e.1 : ℤ) < b := by exact_mod_cast he.1
    have hprod := Int.mul_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg e.2)
    omega
  have upper : c₂ < n := by
    apply (mul_lt_mul_iff_right₀ hb).mp
    rw [hcarry, mul_comm (b : ℤ) n]
    have hd₂ : (e.2 : ℤ) + 1 ≤ b := by exact_mod_cast he.2.1
    have hprod := mul_le_mul_of_nonneg_left hd₂ (Int.natCast_nonneg n)
    rw [mul_add, mul_one] at hprod
    omega
  change IsHoeySloaneStep n b c₁.toNat c₂.toNat e
  refine ⟨by omega, by omega, he, ?_⟩
  rw [Int.toNat_of_nonneg hc₁, Int.toNat_of_nonneg (by omega : 0 ≤ c₂), hcarry]
  omega

/-- **Two multi-edges of the $(4, 10)$-Hoey–Sloane multigraph.** In the
$(4, 10)$-Hoey–Sloane multigraph the label $(2, 8)$ sits on the multi-edge from state $0$
to state $3$, and the label $(1, 7)$ sits on the loop at state $3$: the Hoey–Sloane
transition sends $(2, 8)$ to $(0, 3)$ and $(1, 7)$ to $(3, 3)$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Definition 6 and Figure 4. -/
public theorem hoeySloaneTransition_four_ten :
    hoeySloaneTransition 4 10 (2, 8) = (0, 3) ∧ hoeySloaneTransition 4 10 (1, 7) = (3, 3) := by
  decide

/-- **Multi-image union of a multiset of cycles.** Let $n$ and $b$ be natural numbers and let $I$
be a multiset of vertex lists. Let $C_I$ be the multiset cycle union of $I$: the multiset sum,
over the lists in $I$, of their edges, where a nonempty list $[v_0, \dots, v_{r-1}]$ has the
edges $(v_0, v_1), \dots, (v_{r-2}, v_{r-1}), (v_{r-1}, v_0)$ and the empty list has none. The
multi-image union $\Delta_I$ is the multiset obtained by replacing each edge $e = (d_1, d_2)$ of
$C_I$, with its multiplicity, by the multi-edge $(c_1, c_2)$ of the $(n, b)$-Hoey-Sloane
multigraph that carries the label $e$: $c_1 = \lambda(d_1 + (b - n) d_2)$, where $\lambda$ is
the least non-negative residue modulo $b$ computed in the integers (the identity when $b = 0$),
and $c_2 = \lfloor (n d_2 - d_1 + c_1) / b \rfloor$ (taken to be $0$ when $b = 0$), with a
negative value of $c_1$ or $c_2$ replaced by $0$.

The labels are dropped, since they do not affect in- and out-degrees, connectivity or Eulerian
circuits.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Definition 7. -/
public def multiImageUnion (n b : ℕ) (cs : Multiset (List ℕ)) : Multiset (ℕ × ℕ) :=
  (cycleUnion cs).map (hoeySloaneTransition n b)

/-- **Eulerian circuit through the zero state.** Read a multiset $D$ of pairs of natural
numbers as the multi-edges $(c_1, c_2)$ of a directed multigraph. Then $D$ has an Eulerian
circuit beginning and ending with the zero state when there is a nonempty list of pairs
whose multiset of entries is $D$ (so it uses every multi-edge exactly once), in which each
multi-edge ends where the next one begins, the first one starts at $0$ and the last one
ends at $0$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Theorem 7 (hypothesis). -/
public def HasEulerianCircuitFromZero (D : Multiset (ℕ × ℕ)) : Prop :=
  ∃ w : List (ℕ × ℕ), w ≠ [] ∧ (w : Multiset (ℕ × ℕ)) = D ∧
    w.IsChain (fun x y => x.2 = y.1) ∧ w.head?.map Prod.fst = some 0 ∧
    w.getLast?.map Prod.snd = some 0

/-- **$L$-Eulerian multigraphs.** Let $D$ be a finite multiset of multi-edges $(x, y)$ between
natural numbers, and call a number a vertex of $D$ when it is an endpoint of some multi-edge in
$D$. The multigraph $D$ is $L$-Eulerian when $0$ is a vertex of $D$, every vertex $u$ of $D$
reaches every vertex $v$ of $D$ along a (possibly empty) directed path of multi-edges in $D$, and
for every natural number $c$ the number of multi-edges in $D$ ending at $c$ equals the number of
multi-edges in $D$ starting at $c$, counted with multiplicity.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 4 (definition of `L`-Eulerian, before
Corollary 2). -/
public def IsLEulerian (D : Multiset (ℕ × ℕ)) : Prop :=
  (∃ x ∈ D, x.1 = 0 ∨ x.2 = 0) ∧
    (∀ u v, (∃ x ∈ D, x.1 = u ∨ x.2 = u) → (∃ x ∈ D, x.1 = v ∨ x.2 = v) →
      Relation.ReflTransGen (fun x y => (x, y) ∈ D) u v) ∧
    ∀ c, D.countP (fun x => x.2 = c) = D.countP (fun x => x.1 = c)

end

end MetaMathlibExt
