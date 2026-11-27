/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.SymmetricKey.PRF
public import CSLibExt.Crypto.SymmetricKey.PRG
public import CSLibExt.Crypto.Framework.Presampling

/-!
# The GGM construction: pseudorandom functions from pseudorandom generators

Let `G : S → S × S` be a length-doubling generator and write `G s = (G₀ s, G₁ s)`. The
construction of Goldreich, Goldwasser and Micali (Boneh and Shoup's *tree construction*) is the
keyed function `ggm G : S → (Fin ℓ → Bool) → S` with `ggm G k x = G_{x_ℓ} (⋯ (G_{x_1} k) ⋯)`,
where the bit string `x₁ ⋯ x_ℓ` is the function `x : Fin ℓ → Bool` with `x i = x_{i+1}`: the
label of the leaf addressed by `x` in the binary tree of depth `ℓ` whose root is labelled `k` and
whose node labelled `t` has children labelled `G₀ t` and `G₁ t` (`walk` follows a list of bits
down the tree).

* `prfAdvantage_ggm` (Boneh and Shoup, Theorem 4.10): for `ℓ ≥ 1`, `Q ≥ 1` and every PRF adversary
  `A` (in the sense of `Cslib.Crypto.PRF.prfAdvantage`) that makes at most `Q` queries along every
  path (`FreeM.IsQueryBounded`),
  `prfAdvantage (ggm G) A = ℓ * Q * prgAdvantage G (ggmReduction G Q A)`, an exact equality, with
  the PRG advantage of `Cslib.Crypto.PRG.prgAdvantage`.
* `ggmReduction G Q A` is the explicit PRG distinguisher `B`. It draws a level `i < ℓ`, a hybrid
  index `j < Q`, `Q` pairs `u m`, `Q` seeds `v m` and coins for `A`, and runs `A` once. It answers
  the `m`-th query `x₁ ⋯ x_ℓ` (counting from `0`) from a table of pairs of labels for the children
  of the nodes `x₁ ⋯ x_i` at level `i`: a node not in the table gets `u m` if `m < j`, the
  challenge if `m = j` and `G (v m)` if `m > j`.

`B` runs `A` once, keeps at most `Q` table entries and evaluates `G` at most `ℓ - i` times per
query (once for a new node when `m > j`, and `ℓ - i - 1` times to walk down from level `i + 1`).
`prfAdvantage_ggm` is an equality of advantages for fixed finite types: it states no running time,
and the running-time requirement on `B` and the asymptotic statement that `ggm G` is a secure PRF
when `G` is a secure PRG are outside it. Under Boneh and Shoup's efficiency assumptions (`S`
efficiently represented and sampleable, `G` efficient, and `ℓ` and `Q` polynomially bounded in the
security parameter), this `B` is an elementary wrapper around `A` (Definition 2.12). For `Q = 0`
the adversary makes no queries and its advantage is `0`; the assumption `Q ≥ 1` only makes the
coin set of `B` nonempty.

**Proof.** The `ℓ Q` hybrids are indexed by `(i, j)` with `i < ℓ` and `j < Q`. In hybrid
`(i, j)`, the answers are computed as by `B`, the `j`-th query included: from a pair `u m` for the
nodes first asked about at a query `m < j`, and from `G (v m)` for the others. `B` with a
pseudorandom challenge is hybrid `(i, j)`, and with a uniform challenge hybrid `(i, j + 1)`
(resampling the tape entry at `j`). Hybrid `(i, 0)` gives the nodes at level `i` uniform labels and
derives the labels below them, and so does hybrid `(i - 1, Q)` since `A` makes at most `Q`
queries: running `A` against a lazy table with presampled answers (`OracleComp.runLazy`) has the
distribution of running it against a uniformly random function (`OracleComp.map_runLazy_empty`,
through the lazy random function). At level `0` this is the real world of the PRF experiment, and
after level `ℓ - 1` its random world. Picking the hybrid uniformly (`advantage_hybrid_uniform`)
gives the factor `ℓ Q`. The query translation `OracleComp.reindex` and the lazy table are in
`CSLibExt.Crypto.Framework.Presampling`.

## References

* D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017,
  Section 2.4.3 (Definition 2.12) and Section 4.6 (Theorem 4.10).
* O. Goldreich, S. Goldwasser and S. Micali, "How to construct random functions", *Journal of the
  ACM* 33(4):792–807, 1986.
-/

@[expose] public section

namespace Cslib.Crypto.GGM

open Cslib.Crypto.Framework Cslib.Crypto.Framework.LazySampling
open Cslib.Crypto.Framework.OracleComp
  (reindex run_reindex isQueryBounded_reindex runLazy runLazy_comp map_runLazy_empty)

local notation "U" => Cslib.Probability.PMF.uniformOfFintype

universe u v w

/-! ### Uniform sampling helpers -/

section Uniform

variable {α β γ : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]

private theorem map_equiv (e : α ≃ β) (f : β → γ) : (U α).map (f ∘ e) = (U β).map f := by
  rw [← PMF.map_comp, Cslib.Probability.PMF.uniformOfFintype_map_equiv]

private theorem map_snd (f : β → γ) : (U (α × β)).map (fun p => f p.2) = (U β).map f := by
  rw [uniformOfFintype_map_prod]
  exact PMF.bind_const (U α) ((U β).map f)

/-- Two independent uniform samples can be drawn in either order. -/
private theorem bind_map_comm (f : α → β → γ) :
    ((U α).bind fun a => (U β).map (f a)) = (U β).bind fun b => (U α).map fun a => f a b := by
  simp only [← PMF.bind_pure_comp]
  exact PMF.bind_comm _ _ _

private theorem map_prod_comm (f : α × β → γ) :
    (U (α × β)).map f = (U β).bind fun b => (U α).map fun a => f (a, b) := by
  rw [uniformOfFintype_map_prod, bind_map_comm]

end Uniform

/-! ### The tree construction -/

section Tree

variable {S : Type*}

/-- **Walking down the evaluation tree.** Let $G : S \to S \times S$ and write
$G(s) = (G_0(s), G_1(s))$. For a list of bits $b_1, \dots, b_n$ and $t \in S$, the walk from $t$
along $b_1 \cdots b_n$ is $G_{b_n}(\cdots G_{b_2}(G_{b_1}(t)) \cdots)$: starting from a node of
the evaluation tree labelled $t$, each bit $b$ moves from the current node, labelled $s$, to its
child labelled $G_b(s)$ (the left child for $b = 0$, the right child for $b = 1$). The walk along
the empty list is $t$. -/
def walk (G : S → S × S) (bs : List Bool) (t : S) : S :=
  bs.foldl (fun t b => cond b (G t).2 (G t).1) t

/-- **The GGM tree construction.** Let $G : S \to S \times S$ be a length-doubling generator and
write $G(s) = (G_0(s), G_1(s))$. The keyed function $F : S \times \{0,1\}^\ell \to S$ of
Goldreich, Goldwasser and Micali is
$F(k, x_1 \cdots x_\ell) = G_{x_\ell}(\cdots G_{x_2}(G_{x_1}(k)) \cdots)$: the label of the leaf
addressed by $x$ in the binary tree of depth $\ell$ whose root is labelled $k$ and in which the
children of a node labelled $t$ are labelled $G_0(t)$ and $G_1(t)$. A bit string
$x_1 \cdots x_\ell$ is given as the function on $\{0, \dots, \ell - 1\}$ that maps $i$ to
$x_{i+1}$. -/
def ggm (G : S → S × S) {ℓ : ℕ} (k : S) (x : Fin ℓ → Bool) : S :=
  walk G (List.ofFn x) k

theorem walk_nil (G : S → S × S) (t : S) : walk G [] t = t := rfl

theorem walk_cons (G : S → S × S) (b : Bool) (bs : List Bool) (t : S) :
    walk G (b :: bs) t = walk G bs (cond b (G t).2 (G t).1) := rfl

theorem walk_drop_ofFn {ℓ : ℕ} (G : S → S × S) (x : Fin ℓ → Bool) {i : ℕ} (hi : i < ℓ) (t : S) :
    walk G ((List.ofFn x).drop i) t =
      walk G ((List.ofFn x).drop (i + 1)) (cond (x ⟨i, hi⟩) (G t).2 (G t).1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hi), walk_cons, List.getElem_ofFn]

end Tree

/-! ### The hybrid distinguisher -/

section Reduction

variable {S : Type*} [Fintype S] [Nonempty S] {R : Type*} [Fintype R] [Nonempty R] {ℓ : ℕ}

/-- **The PRG distinguisher built from a PRF adversary against the GGM construction.** Let $S$
and $R$ be finite nonempty sets, let $G : S \to S \times S$, write $G(s) = (G_0(s), G_1(s))$, let
$\ell \ge 1$ and $Q \ge 1$, and let $A$ be a PRF adversary against the GGM construction: for coins
$r \in R$, $A(r)$ is an adaptive oracle algorithm with queries $x = x_1 \cdots x_\ell$ in
$\{0,1\}^\ell$, answers in $S$ and a bit as output. The distinguisher $B$ receives a pair
$y \in S \times S$. Its coins, drawn uniformly, are a level $i \in \{0, \dots, \ell - 1\}$, a
hybrid index $j \in \{0, \dots, Q - 1\}$, pairs $u_0, \dots, u_{Q-1} \in S \times S$, seeds
$v_0, \dots, v_{Q-1} \in S$ and coins $r$ for $A$. It runs $A(r)$ once and outputs its output,
answering the queries of $A$ itself from a table that records, for nodes $p$ at level $i$ of the
evaluation tree, a pair of labels for the two children of $p$. The $m$-th query $x$ (counting
from $0$) concerns the node $p = x_1 \cdots x_i$. If the table has a pair for $p$, it is reused;
otherwise the pair is $u_m$ if $m < j$, the challenge $y$ if $m = j$ and $G(v_m)$ if $m > j$, and
it is recorded for $p$. From the pair $(a_0, a_1)$ for $p$, the answer to $x$ is
$G_{x_\ell}(\cdots G_{x_{i+2}}(a_{x_{i+1}}) \cdots)$. A query for a node with no pair in the
table, asked after the first $Q$ queries, makes $B$ stop and output $0$; an adversary that makes
at most $Q$ queries never asks one.

So $B$ runs $A$ once, keeps at most $Q$ table entries and evaluates $G$ at most $\ell - i$ times
per query of $A$: once for a new node when $m > j$, and $\ell - i - 1$ times to walk down from
level $i + 1$. -/
noncomputable def ggmReduction [NeZero ℓ] (G : S → S × S) (Q : ℕ) [NeZero Q]
    (A : R → OracleComp (Fin ℓ → Bool) S Bool) :
    PRG.Distinguisher (S × S) (Fin ℓ × Fin Q × (Fin Q → S × S) × (Fin Q → S) × R) where
  coins := U _
  guess y ω :=
    match ω with
    | (i, j, u, v, r) =>
      runLazy (fun m => if m < j then u m else if m = j then y else G (v m)) false 0 Table.empty
        (reindex (fun x (k : Fin i) => x (Fin.castLE i.2.le k))
          (fun x a => walk G ((List.ofFn x).drop ((i : ℕ) + 1)) (cond (x i) a.2 a.1)) (A r))

/-- The algorithm with oracle access to the pairs of labels at level `i + 1` that runs `A`. -/
private def levelComp (G : S → S × S) (i : Fin ℓ) (c : OracleComp (Fin ℓ → Bool) S Bool) :
    OracleComp (Fin i → Bool) (S × S) Bool :=
  reindex (fun x (k : Fin i) => x (Fin.castLE i.2.le k))
    (fun x a => walk G ((List.ofFn x).drop ((i : ℕ) + 1)) (cond (x i) a.2 a.1)) c

/-- The tape of the `j`-th lazy hybrid: `u m` before position `j`, `G (v m)` from it on. -/
private def tapeL (G : S → S × S) {Q : ℕ} (j : ℕ) (u : Fin Q → S × S) (v : Fin Q → S) :
    Fin Q → S × S :=
  fun m => if (m : ℕ) < j then u m else G (v m)

/-- The lazy hybrid at level `i` with index `j`. -/
private noncomputable def lazyHyb (G : S → S × S) (Q : ℕ)
    (A : R → OracleComp (Fin ℓ → Bool) S Bool) (i : Fin ℓ) (j : ℕ) : PMF Bool :=
  (U ((Fin Q → S × S) × (Fin Q → S) × R)).map fun ω =>
    runLazy (tapeL G j ω.1 ω.2.1) false 0 Table.empty (levelComp G i (A ω.2.2))

/-- The eager hybrid at level `i`: uniform labels at level `i`, derived labels below. -/
private noncomputable def eagerHyb (G : S → S × S) (A : R → OracleComp (Fin ℓ → Bool) S Bool)
    (i : ℕ) (hi : i ≤ ℓ) : PMF Bool :=
  (U R).bind fun r => (U ((Fin i → Bool) → S)).map fun W =>
    (A r).run fun x => walk G ((List.ofFn x).drop i) (W fun k => x (Fin.castLE hi k))

private theorem eagerHyb_congr (G : S → S × S) (A : R → OracleComp (Fin ℓ → Bool) S Bool)
    {i i' : ℕ} (hi : i ≤ ℓ) (hi' : i' ≤ ℓ) (h : i = i') :
    eagerHyb G A i hi = eagerHyb G A i' hi' := by
  subst h
  rfl

private theorem eagerHyb_zero (G : S → S × S) (A : R → OracleComp (Fin ℓ → Bool) S Bool) :
    eagerHyb G A 0 (Nat.zero_le ℓ) = PRF.prfReal (ggm G) A := by
  rw [PRF.prfReal, map_prod_comm, eagerHyb]
  congr 1
  funext r
  rw [← map_equiv (Equiv.funUnique (Fin 0 → Bool) S)]
  congr 1
  funext W
  simp only [Function.comp_apply, Equiv.funUnique_apply, List.drop_zero]
  congr 1
  funext x
  rw [ggm]
  congr 2
  exact Subsingleton.elim _ _

private theorem eagerHyb_ell (G : S → S × S) (A : R → OracleComp (Fin ℓ → Bool) S Bool) :
    eagerHyb G A ℓ le_rfl = PRF.prfRand A := by
  rw [PRF.prfRand, map_prod_comm, eagerHyb]
  congr 1
  funext r
  congr 1
  funext W
  congr 1
  funext x
  rw [List.drop_eq_nil_of_le (by simp), walk_nil]
  simp [Fin.castLE_refl]

omit [Fintype S] [Nonempty S] in
private theorem isQueryBounded_levelComp (G : S → S × S) (i : Fin ℓ) {Q : ℕ}
    {c : OracleComp (Fin ℓ → Bool) S Bool} (hc : FreeM.IsQueryBounded Q c) :
    FreeM.IsQueryBounded Q (levelComp G i c) :=
  isQueryBounded_reindex _ _ hc

/-- With index `0` the lazy hybrid at level `i` is the eager hybrid at level `i`: every fresh
node at level `i` gets a uniform label, and its children the labels `G` derives from it. -/
private theorem lazyHyb_zero (G : S → S × S) (Q : ℕ) (A : R → OracleComp (Fin ℓ → Bool) S Bool)
    (hA : ∀ r, FreeM.IsQueryBounded Q (A r)) (i : Fin ℓ) :
    lazyHyb G Q A i 0 = eagerHyb G A i i.2.le := by
  have htape : ∀ (u : Fin Q → S × S) (v : Fin Q → S), tapeL G 0 u v = fun m => G (v m) := by
    intro u v
    funext m
    simp [tapeL]
  have hsim : ∀ (v : Fin Q → S) (r : R),
      runLazy (fun m => G (v m)) false 0 Table.empty (levelComp G i (A r)) =
        runLazy v false 0 Table.empty (reindex id (fun _ => G) (levelComp G i (A r))) :=
    fun v r => runLazy_comp G v false _ 0 Table.empty
  simp only [lazyHyb, htape, hsim]
  refine (map_snd (α := Fin Q → S × S)
    (fun vr : (Fin Q → S) × R => runLazy vr.1 false 0 Table.empty
      (reindex id (fun _ => G) (levelComp G i (A vr.2))))).trans ?_
  rw [map_prod_comm, eagerHyb]
  congr 1
  funext r
  rw [map_runLazy_empty false (isQueryBounded_reindex _ _ (isQueryBounded_levelComp G i (hA r)))]
  congr 1
  funext W
  rw [run_reindex, levelComp, run_reindex]
  congr 1
  funext x
  rw [walk_drop_ofFn G x i.2]
  rfl

/-- The pairs of labels of the children of the nodes at level `i`, as one function, are the labels
at level `i + 1`. -/
private def childEquiv (i : ℕ) : ((Fin i → Bool) → S × S) ≃ ((Fin (i + 1) → Bool) → S) where
  toFun W z := cond (z (Fin.last i)) (W (Fin.init z)).2 (W (Fin.init z)).1
  invFun W p := (W (Fin.snoc p false), W (Fin.snoc p true))
  left_inv W := by
    funext p
    simp [Fin.init_snoc, Fin.snoc_last]
  right_inv W := by
    funext z
    have hz := Fin.snoc_init_self (α := fun _ => Bool) z
    cases h : z (Fin.last i) <;> simp only [h, Bool.cond_false, Bool.cond_true] <;> rw [← h, hz]

/-- With index `Q` the lazy hybrid at level `i` is the eager hybrid at level `i + 1`: every
fresh node at level `i` gives its children uniform labels. -/
private theorem lazyHyb_Q (G : S → S × S) (Q : ℕ) (A : R → OracleComp (Fin ℓ → Bool) S Bool)
    (hA : ∀ r, FreeM.IsQueryBounded Q (A r)) (i : Fin ℓ) :
    lazyHyb G Q A i Q = eagerHyb G A (i + 1) i.2 := by
  have htape : ∀ (u : Fin Q → S × S) (v : Fin Q → S), tapeL G Q u v = u := by
    intro u v
    funext m
    simp [tapeL, m.2]
  simp only [lazyHyb, htape]
  rw [uniformOfFintype_map_prod]
  have hin : ∀ u : Fin Q → S × S,
      (U ((Fin Q → S) × R)).map (fun vr => runLazy u false 0 Table.empty
        (levelComp G i (A (u, vr).2.2))) =
      (U R).map fun r => runLazy u false 0 Table.empty (levelComp G i (A r)) :=
    fun u => map_snd (α := Fin Q → S) (fun r => runLazy u false 0 Table.empty (levelComp G i (A r)))
  simp only [hin]
  rw [bind_map_comm, eagerHyb]
  congr 1
  funext r
  rw [map_runLazy_empty false (isQueryBounded_levelComp G i (hA r)),
    ← map_equiv (childEquiv (S := S) i)]
  congr 1
  funext W
  rw [Function.comp_apply, levelComp, run_reindex]
  rfl

/-- The real world of the PRG experiment against `ggmReduction` averages the lazy hybrids
`(i, j)`. -/
private theorem prgReal_ggmReduction [NeZero ℓ] (G : S → S × S) (Q : ℕ) [NeZero Q]
    (A : R → OracleComp (Fin ℓ → Bool) S Bool) :
    PRG.prgReal G (ggmReduction G Q A) =
      (U (Fin ℓ × Fin Q)).bind fun ij => lazyHyb G Q A ij.1 ij.2 := by
  let e : S × (Fin ℓ × Fin Q × (Fin Q → S × S) × (Fin Q → S) × R) ≃
      ((Fin ℓ × Fin Q) × (Fin Q → S × S) × (Fin Q → S) × R) × S :=
    { toFun := fun p => (((p.2.1, p.2.2.1), p.2.2.2.1,
        Function.update p.2.2.2.2.1 p.2.2.1 p.1, p.2.2.2.2.2), p.2.2.2.2.1 p.2.2.1)
      invFun := fun q => (q.1.2.2.1 q.1.1.2, q.1.1.1, q.1.1.2, q.1.2.1,
        Function.update q.1.2.2.1 q.1.1.2 q.2, q.1.2.2.2)
      left_inv := fun p => by simp
      right_inv := fun q => by simp }
  let L : ((Fin ℓ × Fin Q) × (Fin Q → S × S) × (Fin Q → S) × R) → Bool := fun q =>
    runLazy (tapeL G q.1.2 q.2.1 q.2.2.1) false 0 Table.empty (levelComp G q.1.1 (A q.2.2.2))
  have hguess : (fun p : S × (Fin ℓ × Fin Q × (Fin Q → S × S) × (Fin Q → S) × R) =>
      (ggmReduction G Q A).guess (G p.1) p.2) = (fun q => L q.1) ∘ e := by
    funext ⟨s, i, j, u, v, r⟩
    simp only [ggmReduction, e, L, Function.comp_apply, Equiv.coe_fn_mk, levelComp]
    congr 1
    funext m
    simp only [tapeL]
    by_cases hm : m < j
    · simp [hm, Fin.lt_def.mp hm]
    · by_cases hmj : m = j
      · subst hmj
        simp
      · simp [hm, hmj, Fin.lt_def.not.mp hm]
  change ((U S).bind fun s => (U _).map ((ggmReduction G Q A).guess (G s))) = _
  rw [← uniformOfFintype_map_prod
      (fun p : S × (Fin ℓ × Fin Q × (Fin Q → S × S) × (Fin Q → S) × R) =>
        (ggmReduction G Q A).guess (G p.1) p.2),
    hguess, map_equiv, uniformOfFintype_map_fst, uniformOfFintype_map_prod]
  rfl

/-- The random world of the PRG experiment against `ggmReduction` averages the lazy hybrids
`(i, j + 1)`. -/
private theorem prgRand_ggmReduction [NeZero ℓ] (G : S → S × S) (Q : ℕ) [NeZero Q]
    (A : R → OracleComp (Fin ℓ → Bool) S Bool) :
    PRG.prgRand (ggmReduction G Q A) =
      (U (Fin ℓ × Fin Q)).bind fun ij => lazyHyb G Q A ij.1 ((ij.2 : ℕ) + 1) := by
  let e : (S × S) × (Fin ℓ × Fin Q × (Fin Q → S × S) × (Fin Q → S) × R) ≃
      ((Fin ℓ × Fin Q) × (Fin Q → S × S) × (Fin Q → S) × R) × (S × S) :=
    { toFun := fun p => (((p.2.1, p.2.2.1), Function.update p.2.2.2.1 p.2.2.1 p.1,
        p.2.2.2.2.1, p.2.2.2.2.2), p.2.2.2.1 p.2.2.1)
      invFun := fun q => (q.1.2.1 q.1.1.2, q.1.1.1, q.1.1.2,
        Function.update q.1.2.1 q.1.1.2 q.2, q.1.2.2.1, q.1.2.2.2)
      left_inv := fun p => by simp
      right_inv := fun q => by simp }
  let L : ((Fin ℓ × Fin Q) × (Fin Q → S × S) × (Fin Q → S) × R) → Bool := fun q =>
    runLazy (tapeL G ((q.1.2 : ℕ) + 1) q.2.1 q.2.2.1) false 0 Table.empty
      (levelComp G q.1.1 (A q.2.2.2))
  have hguess : (fun p : (S × S) × (Fin ℓ × Fin Q × (Fin Q → S × S) × (Fin Q → S) × R) =>
      (ggmReduction G Q A).guess p.1 p.2) = (fun q => L q.1) ∘ e := by
    funext ⟨y, i, j, u, v, r⟩
    simp only [ggmReduction, e, L, Function.comp_apply, Equiv.coe_fn_mk, levelComp]
    congr 1
    funext m
    simp only [tapeL]
    by_cases hm : m < j
    · have hm' : (m : ℕ) < j + 1 := by have := Fin.lt_def.mp hm; omega
      simp [hm, hm', Function.update_of_ne (ne_of_lt hm)]
    · by_cases hmj : m = j
      · subst hmj
        simp
      · have hm' : ¬ (m : ℕ) < j + 1 := by
          have h1 := Fin.lt_def.not.mp hm
          have h2 : (m : ℕ) ≠ j := fun h => hmj (Fin.ext h)
          omega
        simp [hm, hmj, hm']
  change ((U (S × S)).bind fun y => (U _).map ((ggmReduction G Q A).guess y)) = _
  rw [← uniformOfFintype_map_prod
      (fun p : (S × S) × (Fin ℓ × Fin Q × (Fin Q → S × S) × (Fin Q → S) × R) =>
        (ggmReduction G Q A).guess p.1 p.2),
    hguess, map_equiv, uniformOfFintype_map_fst, uniformOfFintype_map_prod]
  rfl

/-- **The GGM construction: pseudorandom generators give pseudorandom functions.** Let $S$ and
$R$ be finite nonempty sets, let $G : S \to S \times S$ be a length-doubling generator with
$G(s) = (G_0(s), G_1(s))$, let $\ell \ge 1$ and let $F : S \times \{0,1\}^\ell \to S$,
$F(k, x_1 \cdots x_\ell) = G_{x_\ell}(\cdots G_{x_2}(G_{x_1}(k)) \cdots)$, be the GGM
construction. Let $Q \ge 1$ and let $A$ be a PRF adversary: an adaptive oracle algorithm, run on
coins drawn uniformly from $R$ independently of the key and of the random function, that makes at
most $Q$ queries along every path, whatever the answers. Then
$\mathrm{Adv}^{\mathrm{PRF}}[A, F] = \ell\, Q \cdot \mathrm{Adv}^{\mathrm{PRG}}[B, G]$ for the
distinguisher $B$ built from $A$ by the hybrid construction. $B$ draws a level $i < \ell$ and a
query index $j < Q$ uniformly and runs $A$ once, answering its queries from a lazily filled table
of pairs of labels for the children of the nodes at level $i$ of the evaluation tree: a node that
enters the table at query $m$ gets a uniform pair if $m < j$, the challenge pair if $m = j$, and
$G(s)$ for a uniform seed $s$ if $m > j$.

$B$ runs $A$ once, keeps at most $Q$ table entries and evaluates $G$ at most $\ell - i$ times per
query. The equality is one between advantages for fixed finite sets and states no running time;
the running-time requirement on $B$ and the asymptotic statement that $F$ is a secure PRF when $G$
is a secure PRG are outside it. Under Boneh and Shoup's efficiency assumptions ($S$ efficiently
represented and sampleable, $G$ efficient, and $\ell$ and $Q$ polynomially bounded in the security
parameter), this $B$ is an elementary wrapper around $A$ (Definition 2.12). For $Q = 0$ the
adversary makes no queries and its advantage is $0$; the assumption $Q \ge 1$ only makes the coin
set of $B$ nonempty. -/
theorem prfAdvantage_ggm [NeZero ℓ] (G : S → S × S) (Q : ℕ) [NeZero Q]
    (A : R → OracleComp (Fin ℓ → Bool) S Bool) (hA : ∀ r, FreeM.IsQueryBounded Q (A r)) :
    PRF.prfAdvantage (ggm G) A = ℓ * Q * PRG.prgAdvantage G (ggmReduction G Q A) := by
  let e : Fin ℓ × Fin Q ≃ Fin (ℓ * Q) := finProdFinEquiv
  let H : ℕ → PMF Bool := fun k =>
    if h : k < ℓ * Q then (fun ij : Fin ℓ × Fin Q => lazyHyb G Q A ij.1 ij.2) (e.symm ⟨k, h⟩)
    else eagerHyb G A ℓ le_rfl
  have hval : ∀ ij : Fin ℓ × Fin Q, ((e ij : Fin (ℓ * Q)) : ℕ) = ij.2 + Q * ij.1 := fun _ => rfl
  have hH : ∀ ij : Fin ℓ × Fin Q, H (e ij) = lazyHyb G Q A ij.1 ij.2 := by
    intro ij
    simp only [H, (e ij).2, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]
  have hH1 : ∀ ij : Fin ℓ × Fin Q, H (e ij + 1) = lazyHyb G Q A ij.1 ((ij.2 : ℕ) + 1) := by
    rintro ⟨i, j⟩
    by_cases hj : (j : ℕ) + 1 < Q
    · have h := hH (i, ⟨j + 1, hj⟩)
      rw [hval] at h ⊢
      rw [show (j : ℕ) + Q * i + 1 = j + 1 + Q * i by omega]
      exact h
    · have hjQ : (j : ℕ) + 1 = Q := by omega
      rw [hjQ, lazyHyb_Q G Q A hA i, hval]
      by_cases hi : (i : ℕ) + 1 < ℓ
      · have h := hH (⟨i + 1, hi⟩, ⟨0, NeZero.pos Q⟩)
        rw [hval] at h
        rw [show (j : ℕ) + Q * i + 1 = 0 + Q * (i + 1) by rw [Nat.mul_succ]; omega, h,
          lazyHyb_zero G Q A hA]
      · have hiℓ : (i : ℕ) + 1 = ℓ := by omega
        have hk : ¬ (j : ℕ) + Q * i + 1 < ℓ * Q := by
          rw [show (j : ℕ) + Q * i + 1 = Q * (i + 1) by rw [Nat.mul_succ]; omega, hiℓ,
            Nat.mul_comm]
          exact lt_irrefl _
        simp only [H, hk, ↓reduceDIte]
        exact eagerHyb_congr G A _ _ hiℓ.symm
  have hunif : (U (Fin (ℓ * Q))) = (U (Fin ℓ × Fin Q)).map e :=
    (Cslib.Probability.PMF.uniformOfFintype_map_equiv e).symm
  have hreal : PRG.prgReal G (ggmReduction G Q A) = (U (Fin (ℓ * Q))).bind fun k => H k := by
    rw [prgReal_ggmReduction, hunif, PMF.bind_map]
    congr 1
    funext ij
    exact (hH ij).symm
  have hrand : PRG.prgRand (ggmReduction G Q A) =
      (U (Fin (ℓ * Q))).bind fun k => H (k + 1) := by
    rw [prgRand_ggmReduction, hunif, PMF.bind_map]
    congr 1
    funext ij
    exact (hH1 ij).symm
  have h0 : H 0 = PRF.prfReal (ggm G) A := by
    have hpos : 0 < ℓ * Q := Nat.mul_pos (NeZero.pos ℓ) (NeZero.pos Q)
    have h := hH (⟨0, NeZero.pos ℓ⟩, ⟨0, NeZero.pos Q⟩)
    rw [hval] at h
    rw [show (0 : ℕ) = 0 + Q * 0 by simp, h, lazyHyb_zero G Q A hA,
      eagerHyb_congr G A _ (Nat.zero_le ℓ) rfl, eagerHyb_zero]
  have hn : H (ℓ * Q) = PRF.prfRand A := by
    simp only [H, lt_irrefl, ↓reduceDIte]
    exact eagerHyb_ell G A
  have hadv := advantage_hybrid_uniform H (n := ℓ * Q)
  rw [← hreal, ← hrand, h0, hn] at hadv
  have hℓ : (ℓ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
  have hQ : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Q)
  change advantage _ _ = _
  rw [PRG.prgAdvantage, hadv, Nat.cast_mul]
  field_simp

end Reduction

end Cslib.Crypto.GGM
