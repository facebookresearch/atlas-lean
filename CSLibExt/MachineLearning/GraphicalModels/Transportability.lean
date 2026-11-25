/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.DoCalculus
public import CSLibExt.MachineLearning.GraphicalModels.Identifiability
public import Mathlib.Data.Finset.Update
import Mathlib.Tactic.NormNum

/-!
# Transportability: selection diagrams and the transport formula

Two domains, a source `Π` where experiments were run and a target `Π*` where only observations
are available, share one causal diagram `G`. A **selection diagram** marks with a selection
arrow `S → V_i` every node whose mechanism may differ between the domains. When a set `Z` of
pre-treatment covariates is **S-admissible**, the causal effect of `X` on `Y` in the target is
the source's `z`-specific effect reweighted by the target law of `Z` (Pearl–Bareinboim 2014,
Corollary 1 and eq. (3.1)):
`P*(y | do(x)) = ∑_z P(y | do(x), z) P*(z)`.

The causal model is a Markovian finite causal Bayesian network (`BayesNet α n`, one finite value
type, nodes in a topological order); latent variables are ordinary nodes outside `X`, `Y`, `Z`.
As in `CSLibExt/MachineLearning/GraphicalModels/DoCalculus.lean`, all values are read off one
assignment: `P(y | do(x), z)` is the ratio
`marginal (b.mutilateSet X x).joint ↑(Y ∪ Z) x / marginal (b.mutilateSet X x).joint ↑Z x`.

## Main definitions

* `SelectionDiagram n`: the shared diagram `pa` and the set `sel` of nodes with a selection
  arrow (Pearl–Bareinboim 2014, Definition 4). `SelectionDiagram.toNet` is the diagram as a graph
  on `n + 1` nodes, with one selection node `S` at index `0` pointing into every node of `sel`.
* `SelectionDiagram.SAdmissible D X Y T`: `(Y ⫫ S | X, T)` in `D_{\bar X}` (Pearl–Bareinboim
  2014, Definition 8).
* `SelectionDiagram.PreTreatment D X Z`: no node of `Z` is a descendant of a node of `X` in `G`.
* `DomainPair α D`: source and target networks inducing `D`: shared parents, and equal tables at
  every node outside `sel`. `DomainPair.source`, `DomainPair.target`.
* `DomainPair.selNet M a c`: the **selection network** on `n + 1` nodes, in which node `0` is
  `S` with two values `a` (source) and `c` (target); conditioning on `S = c` gives the target and
  on `S = a` the source (Pearl–Bareinboim 2014, §4.1 and footnote 16).

## Main results

* `DomainPair.condEffect_eq_of_sAdmissible` (Pearl–Bareinboim 2014, Theorem 2): for an
  S-admissible `Z`, `P*(y | do(x), z) = P(y | do(x), z)` wherever both are defined; rule 1 of the
  do-calculus applied twice in the selection network.
* `DomainPair.transport_formula` (Pearl–Bareinboim 2014, Corollary 1 with eq. (3.1)): the
  transport formula, by rule 1 (through `condEffect_eq_of_sAdmissible`) and rule 3 of the
  do-calculus (once per domain).
* `SelectionDiagram.identifiedOn_transport`: the target effect is a function of the source
  interventional law and the target observational law on the class of domain pairs with
  overlap (Pearl–Bareinboim 2014, Definition 5 and the first clause of Corollary 1).

The rules are used as stated in `DoCalculus.lean` (`BayesNet.doCalculus_rule1`,
`BayesNet.doCalculus_rule3`); rule 2 is not needed.

## Hypotheses of the transport formula

Besides S-admissibility of `Z` and pairwise disjointness of `X`, `Y`, `Z`,
`DomainPair.transport_formula` assumes:

* `hpre` (**pre-treatment**): no node of `Z` is a descendant of a node of `X` in `G`. This is a
  hypothesis of the source: Corollary 1 asks for "a set Z of observed pretreatment covariates"
  (Pearl–Bareinboim 2014; also AAAI 2011, Corollary 1). Without it the formula is false, even for
  a `Z` that is S-admissible under both published definitions of S-admissibility.
* `hov` (**overlap**): every value `z` with `P*(z) ≠ 0` has `P(z) ≠ 0`. The source leaves this
  implicit (its formula uses `P(y | do(x), z)` on every stratum that the target weights); it is
  explicit here because division by zero is `0` in Lean, and without it the formula is false.

`CSLibExtTest/MachineLearning/GraphicalModels/TransportabilityTests.lean` has exact
counterexamples for each of the three hypotheses (S-admissibility, pre-treatment, overlap) and a
non-vacuity instance.

## Implementation notes

The selection network `DomainPair.selNet` and the parent sets `SelectionDiagram.augPa` are
adapted from the private intervention-switch network of `DoCalculus.lean` (`switchPa_r3`,
`switchNet_r3`, `switchPrior_r3`), which this file does not modify. Auxiliary lemmas re-proved
here from private lemmas of `DoCalculus.lean` are private and named `tp_aux_*`, with a docstring
naming the lemma they adapt.

## References

* J. Pearl and E. Bareinboim, *External validity: from do-calculus to transportability across
  populations*, Statistical Science 29(4) (2014), 579–595, doi:10.1214/14-STS486
  (arXiv:1503.01603): Definition 4 (selection diagram), Definition 5 (transportability),
  Definition 8 (S-admissibility), Theorem 2, Corollary 1, eq. (3.1). This is the statement
  source.
* J. Pearl and E. Bareinboim, *Transportability of causal and statistical relations: a formal
  approach*, Proceedings of AAAI-11 (2011), 247–254, doi:10.1609/aaai.v25i1.7861: Corollary 1,
  eq. (1), and its proof, eq. (6) (the original statement).
* J. Pearl, *Causal diagrams for empirical research*, Biometrika 82(4) (1995), 669–688,
  Theorem 3; J. Pearl, *Causality*, 2nd ed., Cambridge University Press (2009), Theorem 3.4.1
  (the rules of the do-calculus).
* J. Pearl, *The do-calculus revisited*, UAI 2012, arXiv:1210.4852 (background on the
  do-calculus and selection diagrams only).
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset MetaMathlibExt.FiniteWeight
open Function (updateFinset)

variable {α : Type*}

/-! ### Selection diagrams -/

/-- A **selection diagram** (Pearl–Bareinboim 2014, Definition 4) on the nodes `0, …, n - 1`,
listed in a topological order as for `BayesNet`: the causal diagram `pa` shared by the source and
target domains, and the set `sel` of nodes that receive a selection arrow `S → V_i`. The absence
of a selection arrow at a node encodes that its mechanism is the same in both domains. A single
merged selection node pointing into every node of `sel` can only open more trails than one
selection node per node of `sel` (it adds forks through `S` between selected nodes), so
d-separation from the merged `S` implies the corresponding separation with separate selection
nodes; `SAdmissible` below is this merged-node condition, which is sufficient for the transport
formula. -/
structure SelectionDiagram (n : ℕ) where
  /-- The parents of node `k` in the shared causal diagram, among the nodes `0, …, k - 1`. -/
  pa : (k : Fin n) → Finset (Fin k)
  /-- The nodes with a selection arrow, whose mechanism may differ between the domains. -/
  sel : Finset (Fin n)

namespace SelectionDiagram

variable {n : ℕ} (D : SelectionDiagram n)

/-- Parents in the selection diagram as a graph on `n + 1` nodes: node `0` is the selection node
`S`, with no parents; node `j.succ` is node `j`, with the parents of `j` shifted by one and with
`S` as an extra parent when `j ∈ D.sel`. (Adapted from the private definition `switchPa_r3` of
`CSLibExt/MachineLearning/GraphicalModels/DoCalculus.lean`.) -/
def augPa : (k : Fin (n + 1)) → Finset (Fin k) :=
  Fin.cases (motive := fun k : Fin (n + 1) => Finset (Fin k)) ∅
    (fun j => (D.pa j).map (Fin.succEmb j.val) ∪
      (if j ∈ D.sel then {⟨0, by rw [Fin.val_succ]; exact Nat.zero_lt_succ _⟩} else ∅))

/-- A parent of `j`, shifted by one, is a parent of `j.succ` in the augmented diagram. (Adapted
from the private lemma `switchPa_r3_mem_succ` of `DoCalculus.lean`.) -/
theorem succ_mem_augPa (j : Fin n) (i : D.pa j) : Fin.succ i.1 ∈ D.augPa j.succ := by
  simp only [augPa, Fin.cases_succ]
  refine Finset.mem_union_left _ ?_
  have h1 := Finset.mem_map_of_mem (Fin.succEmb j.val) i.2
  rwa [Fin.coe_succEmb] at h1

/-- The selection node `0` is a parent of `j.succ` in the augmented diagram when `j ∈ D.sel`.
(Adapted from the private lemma `switchPa_r3_mem_zero` of `DoCalculus.lean`.) -/
theorem zero_mem_augPa (j : Fin n) (hj : j ∈ D.sel) (h0 : 0 < j.succ.val) :
    (⟨0, h0⟩ : Fin j.succ) ∈ D.augPa j.succ := by
  simp only [augPa, Fin.cases_succ]
  rw [ite_eq_left hj]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- The selection diagram as a graph on `n + 1` nodes, with the selection node `S` at index `0`
and node `j` of `D` at index `j.succ`. Only its parents enter d-separation; the tables are point
masses on `Unit`. -/
noncomputable def toNet : BayesNet Unit (n + 1) :=
  ⟨D.augPa, fun _ _ => Convexity.StdSimplex.single ()⟩

/-- The shared causal diagram `G` as a graph on `n` nodes (point-mass tables on `Unit`). -/
noncomputable def graph : BayesNet Unit n :=
  ⟨D.pa, fun _ _ => Convexity.StdSimplex.single ()⟩

/-- **S-admissibility** (Pearl–Bareinboim 2014, Definition 8): a set `T` is S-admissible for the
effect of `X` on `Y` when `(Y ⫫ S | X, T)` holds in `D_{\bar X}`, the selection diagram with the
arrows into `X` removed. In `D.toNet` the node `j` of `D` is `j.succ` and `S` is `0`. -/
def SAdmissible (X Y T : Finset (Fin n)) : Prop :=
  (D.toNet.mutilateSet (X.map (Fin.succEmb n)) fun _ => ()).DSeparated
    ((Y.map (Fin.succEmb n) : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
    (({0} : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
    ((X.map (Fin.succEmb n) ∪ T.map (Fin.succEmb n) : Finset (Fin (n + 1))) :
      Set (Fin (n + 1)))

/-- `Z` consists of **pre-treatment covariates** for the treatment `X` (Pearl–Bareinboim 2014,
Corollary 1): no node of `Z` is a descendant of a node of `X` in the causal diagram `G`. -/
def PreTreatment (X Z : Finset (Fin n)) : Prop :=
  ∀ k ∈ X, ∀ z ∈ Z, ¬D.graph.IsDescendant k z

end SelectionDiagram

/-! ### Pairs of domains -/

/-- A pair of causal Bayesian networks, the source domain `Π` (tables `cpt`) and the target
domain `Π*` (tables `cpt'`), that **induces** the selection diagram `D` (Pearl–Bareinboim 2014,
Definition 4, for Markovian networks): both have the parents `D.pa`, and every node without a
selection arrow has the same mechanism, its table, in both domains. -/
structure DomainPair (α : Type*) {n : ℕ} (D : SelectionDiagram n) where
  /-- The tables of the source domain `Π`. -/
  cpt : (k : Fin n) → (D.pa k → α) → Convexity.StdSimplex ℝ α
  /-- The tables of the target domain `Π*`. -/
  cpt' : (k : Fin n) → (D.pa k → α) → Convexity.StdSimplex ℝ α
  /-- A node without a selection arrow has the same table in both domains. -/
  cpt'_eq : ∀ k, k ∉ D.sel → cpt' k = cpt k

namespace DomainPair

variable {n : ℕ} {D : SelectionDiagram n}

/-- The source domain `Π` as a causal Bayesian network. -/
def source (M : DomainPair α D) : BayesNet α n := ⟨D.pa, M.cpt⟩

/-- The target domain `Π*` as a causal Bayesian network. -/
def target (M : DomainPair α D) : BayesNet α n := ⟨D.pa, M.cpt'⟩

end DomainPair

/-- The prior of the selection node: weight `1/2` on `a` and weight `1/2` on `c`. (Adapted from
the private definition `switchPrior_r3` of `DoCalculus.lean`.) -/
noncomputable def selPrior (a c : α) : Convexity.StdSimplex ℝ α :=
  Convexity.StdSimplex.duple a c (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)

namespace DomainPair

variable {n : ℕ} {D : SelectionDiagram n}

/-- The **selection network** of a domain pair on `n + 1` nodes: node `0` is the selection node
`S` with prior `selPrior a c`; node `j.succ` has the target table of `j` when `j ∈ D.sel` and
`S = c`, and the source table of `j` otherwise. For `a ≠ c`, conditioning on `S = c` gives the
target and on `S = a` the source (Pearl–Bareinboim 2014, §4.1 and footnote 16); if `a = c` the
`S = c` branch is selected at every selected node and the network does not encode the source,
so every bridge lemma below assumes `a ≠ c`. Its graph is that of `D.toNet`. (Adapted from the
private definition `switchNet_r3` of `DoCalculus.lean`.) -/
noncomputable def selNet [DecidableEq α] (M : DomainPair α D) (a c : α) :
    BayesNet α (n + 1) where
  pa := D.augPa
  cpt := Fin.cases (motive := fun k : Fin (n + 1) =>
      (D.augPa k → α) → Convexity.StdSimplex ℝ α)
    (fun _ => selPrior a c)
    (fun j u =>
      if hj : j ∈ D.sel then
        if u ⟨⟨0, by rw [Fin.val_succ]; exact Nat.zero_lt_succ _⟩,
            D.zero_mem_augPa j hj _⟩ = c then
          M.cpt' j fun i => u ⟨Fin.succ i.1, D.succ_mem_augPa j i⟩
        else M.cpt j fun i => u ⟨Fin.succ i.1, D.succ_mem_augPa j i⟩
      else M.cpt j fun i => u ⟨Fin.succ i.1, D.succ_mem_augPa j i⟩)

end DomainPair

/-! ### Stage S1: graph lemmas -/

namespace BayesNet

/-- An intervention reads its values only on the intervened set. -/
theorem mutilateSet_congr [Nonempty α] {n : ℕ} (b : BayesNet α n) (W : Finset (Fin n))
    {w w' : Fin n → α} (h : ∀ j ∈ W, w j = w' j) : b.mutilateSet W w = b.mutilateSet W w' := by
  cases b with
  | mk pa cpt =>
    simp only [mutilateSet]
    congr 1
    funext j z
    by_cases hj : j ∈ W
    · simp [hj, h j hj]
    · simp [hj]

/-- d-separation depends only on the parent sets of a network. -/
theorem dSeparated_congr_pa {β : Type*} {m : ℕ} (b : BayesNet α m) (b' : BayesNet β m)
    (h : b.pa = b'.pa) {A B C : Set (Fin m)} : b.DSeparated A B C ↔ b'.DSeparated A B C := by
  have hpa : ∀ j, b.pa j = b'.pa j := fun j => congrArg (fun pa => pa j) h
  have hEdge : b.Edge = b'.Edge := by
    funext i j
    unfold Edge
    rw [hpa j]
  have hDesc : b.IsDescendant = b'.IsDescendant := by
    unfold IsDescendant
    rw [hEdge]
  have hAdj : b.Adj = b'.Adj := by
    unfold Adj
    rw [hEdge]
  have hIsPath : b.IsPath = b'.IsPath := by
    unfold IsPath
    rw [hAdj]
  have hBlocked : b.BlockedAt = b'.BlockedAt := by
    unfold BlockedAt
    rw [hEdge, hDesc]
  have hPathBlocked : b.PathBlocked = b'.PathBlocked := by
    unfold PathBlocked
    rw [hBlocked]
  unfold DSeparated
  rw [hIsPath, hPathBlocked]

/-- If no node of `Z` is a descendant of a node of `X`, then `∅` d-separates `Z` from `X` in
`G_{\bar X}` (the graph of `b.mutilateSet X w`): on a path from `z ∈ Z` to `k ∈ X` no arrow enters
`k`, and the path is not directed from `k` to `z`, so it has a collider, blocked by `∅`. This is
the d-separation hypothesis of rule 3 for `P(z | do(x)) = P(z)`. -/
theorem dSeparated_mutilateSet_of_not_isDescendant [Nonempty α] {n : ℕ} (b : BayesNet α n)
    {X Z : Finset (Fin n)} (w : Fin n → α) (h : ∀ k ∈ X, ∀ z ∈ Z, ¬b.IsDescendant k z) :
    (b.mutilateSet X w).DSeparated (Z : Set (Fin n)) (X : Set (Fin n))
      ((∅ : Finset (Fin n)) : Set (Fin n)) := by
  unfold DSeparated
  intro x hx y hy p hp
  unfold IsPath at hp
  obtain ⟨hNodup, hChain, hHead, hLast⟩ := hp
  have hBlockedEmpty : ∀ u m v : Fin n,
      (b.mutilateSet X w).BlockedAt ((∅ : Finset (Fin n)) : Set (Fin n)) u m v ↔
      (b.mutilateSet X w).Edge u m ∧ (b.mutilateSet X w).Edge v m := by
    intro u m v
    unfold BlockedAt
    simp
  unfold PathBlocked
  by_contra hNotBlocked
  push_neg at hNotBlocked
  have hNoCollider : ∀ (i : Nat) (hi : i + 2 < p.length),
      ¬ ((b.mutilateSet X w).Edge p[i] p[i + 1] ∧
        (b.mutilateSet X w).Edge p[i + 2] p[i + 1]) := by
    intro i hi
    have hb := hNotBlocked i hi
    rw [hBlockedEmpty] at hb
    exact hb
  have hEdgeOrig : ∀ {i j : Fin n}, (b.mutilateSet X w).Edge i j → b.Edge i j := by
    intro i j hij
    unfold Edge at hij ⊢
    obtain ⟨hlt, hmem⟩ := hij
    refine ⟨hlt, ?_⟩
    unfold mutilateSet at hmem
    by_cases hj : j ∈ X
    · simp [hj] at hmem
    · simp [hj] at hmem
      exact hmem
  have hNoIncoming : ∀ {i j : Fin n}, j ∈ X → ¬ (b.mutilateSet X w).Edge i j := by
    intro i j hj hij
    unfold Edge at hij
    obtain ⟨hlt, hmem⟩ := hij
    unfold mutilateSet at hmem
    simp [hj] at hmem
  have hDescOrig : ∀ {i j : Fin n},
      (b.mutilateSet X w).IsDescendant i j → b.IsDescendant i j := by
    intro i j hij
    unfold IsDescendant at hij ⊢
    induction hij with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hEdge ih => exact Relation.ReflTransGen.tail ih (hEdgeOrig hEdge)
  have hyFin : y ∈ X := Finset.mem_coe.mp hy
  have hxFin : x ∈ Z := Finset.mem_coe.mp hx
  have hHeadOpt : p[0]? = some x := by
    rw [← List.head?_eq_getElem?, hHead]
  have hLastOpt : p[p.length - 1]? = some y := by
    rw [← List.getLast?_eq_getElem?, hLast]
  obtain ⟨h0Lt, h0Eq⟩ := List.getElem?_eq_some_iff.mp hHeadOpt
  obtain ⟨hLastLt, hLastEq⟩ := List.getElem?_eq_some_iff.mp hLastOpt
  have hAdj : ∀ (j : Nat) (hj : j + 1 < p.length),
      (b.mutilateSet X w).Adj p[j] p[j + 1] :=
    fun j hj => List.IsChain.getElem hChain j hj
  have hEdgeBack : ∀ (k : Nat) (hk : k + 1 < p.length),
      (b.mutilateSet X w).Edge p[p.length - 1 - k] p[p.length - 2 - k] := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hj : p.length - 2 + 1 < p.length := by omega
      have hAdjLast := hAdj (p.length - 2) hj
      have heq1 : p.length - 2 + 1 = p.length - 1 := by omega
      simp only [heq1] at hAdjLast
      unfold Adj at hAdjLast
      cases hAdjLast with
      | inl hFwd =>
        exfalso
        simp only [hLastEq] at hFwd
        exact hNoIncoming hyFin hFwd
      | inr hBack =>
        simpa using hBack
    | succ k ih =>
      intro hk
      have hk' : k + 1 < p.length := by omega
      have ihEdge := ih hk'
      have hj2 : p.length - 3 - k + 1 < p.length := by omega
      have hAdj2 := hAdj (p.length - 3 - k) hj2
      have heq2 : p.length - 3 - k + 1 = p.length - 2 - k := by omega
      simp only [heq2] at hAdj2
      unfold Adj at hAdj2
      cases hAdj2 with
      | inl hFwd2 =>
        exfalso
        have hi : p.length - 3 - k + 2 < p.length := by omega
        have hNC := hNoCollider (p.length - 3 - k) hi
        have heq3 : p.length - 3 - k + 1 = p.length - 2 - k := by omega
        have heq4 : p.length - 3 - k + 2 = p.length - 1 - k := by omega
        simp only [heq3, heq4] at hNC
        exact hNC ⟨hFwd2, ihEdge⟩
      | inr hBack2 =>
        have heq5 : p.length - 1 - (k + 1) = p.length - 2 - k := by omega
        have heq6 : p.length - 2 - (k + 1) = p.length - 3 - k := by omega
        simp only [heq5, heq6]
        exact hBack2
  have hReach : ∀ (k : Nat) (hk : k < p.length),
      (b.mutilateSet X w).IsDescendant y p[p.length - 1 - k] := by
    intro k
    induction k with
    | zero =>
      intro hk
      have heq : p.length - 1 - 0 = p.length - 1 := by omega
      simp only [heq]
      simp only [hLastEq]
      unfold IsDescendant
      exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro hk
      have hk' : k < p.length := by omega
      have ihDesc := ih hk'
      have hkEdge : k + 1 < p.length := hk
      have hE := hEdgeBack k hkEdge
      have heq7 : p.length - 2 - k = p.length - 1 - (k + 1) := by omega
      simp only [heq7] at hE
      unfold IsDescendant at ihDesc ⊢
      exact Relation.ReflTransGen.tail ihDesc hE
  have hkFinal : p.length - 1 < p.length := by omega
  have hDescMut := hReach (p.length - 1) hkFinal
  have heqFinal : p.length - 1 - (p.length - 1) = 0 := by omega
  simp only [heqFinal] at hDescMut
  simp only [h0Eq] at hDescMut
  have hDescOrigFinal : b.IsDescendant y x := hDescOrig hDescMut
  exact (h y hyFin x hxFin) hDescOrigFinal

end BayesNet

namespace DomainPair

variable {n : ℕ} {D : SelectionDiagram n}

/-- The source network has the descendant relation of the shared diagram. -/
theorem isDescendant_source (M : DomainPair α D) :
    M.source.IsDescendant = D.graph.IsDescendant := by
  rfl

/-- The target network has the descendant relation of the shared diagram. -/
theorem isDescendant_target (M : DomainPair α D) :
    M.target.IsDescendant = D.graph.IsDescendant := by
  rfl

/-- S-admissibility transfers to the selection network: if `Z` is S-admissible for the effect of
`X` on `Y`, then `(Y ⫫ S | X, Z)` holds in the selection network with the arrows into `X`
removed, for every intervention value. This is the d-separation hypothesis of rule 1 for
`P(y | do(x), z, s) = P(y | do(x), z)`. -/
theorem selNet_dSeparated_of_sAdmissible [DecidableEq α] [Nonempty α] (M : DomainPair α D)
    (a c : α) {X Y Z : Finset (Fin n)} (w : Fin (n + 1) → α) (h : D.SAdmissible X Y Z) :
    ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) w).DSeparated
      ((Y.map (Fin.succEmb n) : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
      (({0} : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
      ((X.map (Fin.succEmb n) ∪ Z.map (Fin.succEmb n) : Finset (Fin (n + 1))) :
        Set (Fin (n + 1))) := by
  have hpa : (D.toNet.mutilateSet (X.map (Fin.succEmb n)) fun _ => ()).pa =
      ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) w).pa := rfl
  exact (BayesNet.dSeparated_congr_pa _ _ hpa).mp h

end DomainPair

/-! ### Stage S2: the selection-network bridge -/

/-- For `a ≠ c`, the selection prior gives weight `1/2` to `a`. -/
theorem selPrior_weights_left {a c : α} (h : a ≠ c) : (selPrior a c).weights a = 1 / 2 := by
  unfold selPrior
  rw [Convexity.StdSimplex.weights_duple, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne h]
  norm_num

/-- For `a ≠ c`, the selection prior gives weight `1/2` to `c`. -/
theorem selPrior_weights_right {a c : α} (h : a ≠ c) : (selPrior a c).weights c = 1 / 2 := by
  unfold selPrior
  rw [Convexity.StdSimplex.weights_duple, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (Ne.symm h)]
  norm_num

/-- The selection prior gives positive weight to `a`. (Adapted from the private lemma
`switchPrior_r3_weights_left_pos` of `DoCalculus.lean`.) -/
theorem selPrior_weights_left_pos (a c : α) : 0 < (selPrior a c).weights a := by
  unfold selPrior
  rw [Convexity.StdSimplex.weights_duple, Finsupp.add_apply, Finsupp.single_eq_same]
  by_cases h : a = c
  · subst h
    rw [Finsupp.single_eq_same]
    norm_num
  · rw [Finsupp.single_eq_of_ne h]
    norm_num

/-- The selection prior gives positive weight to `c`. (Adapted from the private lemma
`switchPrior_r3_weights_right_pos` of `DoCalculus.lean`.) -/
theorem selPrior_weights_right_pos (a c : α) : 0 < (selPrior a c).weights c := by
  unfold selPrior
  rw [Convexity.StdSimplex.weights_duple, Finsupp.add_apply, Finsupp.single_eq_same]
  by_cases h : c = a
  · subst h
    rw [Finsupp.single_eq_same]
    norm_num
  · rw [Finsupp.single_eq_of_ne h]
    norm_num

namespace DomainPair

variable {n : ℕ} {D : SelectionDiagram n}

/-- The factor of node `0` of the selection network. (Adapted from the private lemma
`switchNet_r3_factor_zero` of `DoCalculus.lean`.) -/
private theorem tp_aux_selNet_factor_zero [DecidableEq α] [Nonempty α] (M : DomainPair α D)
    (a c : α) (v : Fin (n + 1) → α) :
    ((M.selNet a c).cpt 0 ((M.selNet a c).paVal 0 v)).weights (v 0) =
      (selPrior a c).weights (v 0) := by
  simp only [DomainPair.selNet]
  rw [Fin.cases_zero]

/-- The factor of node `j.succ` of the selection network: the target table of `j` when
`j ∈ D.sel` and `S = c`, the source table otherwise. (Adapted from the private lemma
`switchNet_r3_factor_succ` of `DoCalculus.lean`.) -/
private theorem tp_aux_selNet_factor_succ [DecidableEq α] [Nonempty α] (M : DomainPair α D)
    (a c : α) (v : Fin (n + 1) → α) (j : Fin n) :
    ((M.selNet a c).cpt j.succ ((M.selNet a c).paVal j.succ v)).weights (v j.succ) =
      if j ∈ D.sel ∧ v 0 = c then
        (M.cpt' j (M.target.paVal j (Fin.tail v))).weights (v j.succ)
      else (M.cpt j (M.source.paVal j (Fin.tail v))).weights (v j.succ) := by
  have h0 : ∀ (p : 0 < (j.succ).val) (q : (⟨0, p⟩ : Fin (j.succ).val) ∈ D.augPa j.succ),
      ((M.selNet a c).paVal j.succ v) ⟨⟨0, p⟩, q⟩ = v 0 := by
    intro p q
    simp only [BayesNet.paVal]
    congr 1
  have hfunS : (fun i : D.pa j => ((M.selNet a c).paVal j.succ v) ⟨Fin.succ i.1, D.succ_mem_augPa j i⟩)
      = M.source.paVal j (Fin.tail v) := by
    funext i
    simp only [BayesNet.paVal, Fin.tail]
    congr 1
  have hfunT : (fun i : D.pa j => ((M.selNet a c).paVal j.succ v) ⟨Fin.succ i.1, D.succ_mem_augPa j i⟩)
      = M.target.paVal j (Fin.tail v) := hfunS
  simp only [DomainPair.selNet] at h0 hfunS hfunT ⊢
  rw [Fin.cases_succ]
  by_cases hj : j ∈ D.sel
  · rw [dite_eq_left hj, h0]
    by_cases h0c : v 0 = c
    · rw [ite_eq_left h0c, ite_eq_left ⟨hj, h0c⟩, hfunT]
    · rw [ite_eq_right h0c, ite_eq_right (fun h => h0c h.2), hfunS]
  · rw [dite_eq_right hj, ite_eq_right (fun h => hj h.1), hfunS]

/-- **The selection network under an intervention**: with the arrows into `X` removed, the joint
of the selection network at `(g, u)` is the prior weight of `g` times the target joint under
`do(X = v)` when `g = c`, and the source joint otherwise. (Adapted from the private lemma
`switchNet_r3_joint_cons` of `DoCalculus.lean`.) -/
theorem selNet_mutilateSet_joint_cons [DecidableEq α] [Nonempty α] (M : DomainPair α D)
    (a c : α) (X : Finset (Fin n)) (f g : α) (v u : Fin n → α) :
    ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons f v)).joint (Fin.cons g u) =
      (selPrior a c).weights g *
        (if g = c then (M.target.mutilateSet X v).joint u
          else (M.source.mutilateSet X v).joint u) := by
  have hmem : ∀ j : Fin n, j.succ ∈ X.map (Fin.succEmb n) ↔ j ∈ X := by
    intro j
    constructor
    · intro h
      rw [Finset.mem_map] at h
      obtain ⟨i, hiX, h⟩ := h
      rw [Fin.coe_succEmb] at h
      have hij : i = j := Fin.succ_injective _ h
      rwa [hij] at hiX
    · intro h
      rw [Finset.mem_map]
      exact ⟨j, h, by rw [Fin.coe_succEmb]⟩
  have h0mem : (0 : Fin (n + 1)) ∉ X.map (Fin.succEmb n) := by
    rw [Finset.mem_map]
    rintro ⟨i, _, h⟩
    rw [Fin.coe_succEmb] at h
    exact Fin.succ_ne_zero i h
  have htc : M.target.cpt = M.cpt' := rfl
  have hsc : M.source.cpt = M.cpt := rfl
  have hpa : ∀ (j : Fin n) (y : Fin n → α), M.source.paVal j y = M.target.paVal j y :=
    fun j y => rfl
  rw [BayesNet.joint_mutilateSet, Fin.prod_univ_succ, ite_eq_right h0mem,
    tp_aux_selNet_factor_zero, Fin.cons_zero]
  congr 1
  by_cases hgc : g = c
  · rw [ite_eq_left hgc, BayesNet.joint_mutilateSet, htc]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hjX : j ∈ X
    · rw [ite_eq_left ((hmem j).mpr hjX), ite_eq_left hjX]
      simp only [Fin.cons_succ]
    · rw [ite_eq_right (fun h => hjX ((hmem j).mp h)), ite_eq_right hjX,
        tp_aux_selNet_factor_succ]
      simp only [Fin.cons_zero, Fin.tail_cons, Fin.cons_succ]
      by_cases hjS : j ∈ D.sel
      · rw [ite_eq_left ⟨hjS, hgc⟩]
      · rw [ite_eq_right (fun h => hjS h.1), hpa, M.cpt'_eq j hjS]
  · rw [ite_eq_right hgc, BayesNet.joint_mutilateSet, hsc]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hjX : j ∈ X
    · rw [ite_eq_left ((hmem j).mpr hjX), ite_eq_left hjX]
      simp only [Fin.cons_succ]
    · rw [ite_eq_right (fun h => hjX ((hmem j).mp h)), ite_eq_right hjX,
        tp_aux_selNet_factor_succ]
      simp only [Fin.cons_zero, Fin.tail_cons, Fin.cons_succ]
      rw [ite_eq_right (fun h => hgc h.2)]

/-- **Marginals of the selection network under an intervention**: the marginal over `S` and the
shifted nodes of `U` at `(g, u)` is the prior weight of `g` times the marginal over `U` of the
target under `do(X = v)` when `g = c`, and of the source otherwise. (Adapted from the private
lemma `switchNet_r3_marginal_cons` of `DoCalculus.lean`.) -/
theorem selNet_mutilateSet_marginal_cons [Fintype α] [DecidableEq α] [Nonempty α]
    (M : DomainPair α D) (a c : α) (X U : Finset (Fin n)) (f g : α) (v u : Fin n → α) :
    marginal ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons f v)).joint
        ((insert 0 (U.map (Fin.succEmb n)) : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
        (Fin.cons g u) =
      (selPrior a c).weights g *
        (if g = c then marginal (M.target.mutilateSet X v).joint ↑U u
          else marginal (M.source.mutilateSet X v).joint ↑U u) := by
  have hmemU : ∀ j : Fin n, j.succ ∈ U.map (Fin.succEmb n) ↔ j ∈ U := by
    intro j
    constructor
    · intro h
      rw [Finset.mem_map] at h
      obtain ⟨i, hiU, h⟩ := h
      rw [Fin.coe_succEmb] at h
      have hij : i = j := Fin.succ_injective _ h
      rwa [hij] at hiU
    · intro h
      rw [Finset.mem_map]
      exact ⟨j, h, by rw [Fin.coe_succEmb]⟩
  have himg : Finset.filter
        (fun y : Fin (n + 1) → α => ∀ i ∈ insert 0 (U.map (Fin.succEmb n)),
          y i = (Fin.cons (α := fun _ => α) g u) i)
        Finset.univ
        = (Finset.filter (fun z : Fin n → α => ∀ j ∈ U, z j = u j) Finset.univ).image
          (Fin.cons (α := fun _ => α) g) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hy
      refine ⟨Fin.tail y, ?_, ?_⟩
      · intro j hjU
        have hyj := hy j.succ (Finset.mem_insert_of_mem ((hmemU j).mpr hjU))
        rw [Fin.cons_succ] at hyj
        exact hyj
      · have hy0 : y 0 = g := by
          have h0mem : (0 : Fin (n + 1)) ∈ insert 0 (U.map (Fin.succEmb n)) :=
            Finset.mem_insert_self 0 _
          have hy0 := hy 0 h0mem
          rw [Fin.cons_zero] at hy0
          exact hy0
        rw [← hy0]
        exact Fin.cons_self_tail y
    · rintro ⟨z, hz, rfl⟩
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · simp only [Fin.cons_zero]
      · rw [Finset.mem_map] at hi
        obtain ⟨a, haU, h⟩ := hi
        rw [Fin.coe_succEmb] at h
        subst h
        simp only [Fin.cons_succ]
        exact hz a haU
  have hinj : Set.InjOn ((Fin.cons (α := fun _ => α) g : (Fin n → α) → (Fin (n + 1) → α)))
      ↑(Finset.filter (fun z : Fin n → α => ∀ j ∈ U, z j = u j) Finset.univ) := by
    intro x _ y _ h
    have h2 := congrArg Fin.tail h
    simp only [Fin.tail_cons] at h2
    exact h2
  rw [marginal_coe]
  by_cases hgc : g = c
  · rw [ite_eq_left hgc, marginal_coe, himg, Finset.sum_image hinj]
    simp only [selNet_mutilateSet_joint_cons, ite_eq_left hgc]
    rw [← Finset.mul_sum]
  · rw [ite_eq_right hgc, marginal_coe, himg, Finset.sum_image hinj]
    simp only [selNet_mutilateSet_joint_cons, ite_eq_right hgc]
    rw [← Finset.mul_sum]

end DomainPair

/-! ### Stage S3: the do-calculus derivation -/

/-- Summing out `Z`: for `Y` disjoint from `Z`, the marginal over `Y` at `x` is the sum over the
values `z` of `Z` of the marginal over `Y ∪ Z` at the assignment equal to `z` on `Z` and to `x`
elsewhere. -/
theorem marginal_eq_sum_updateFinset [Fintype α] {n : ℕ} (P : (Fin n → α) → ℝ)
    {Y Z : Finset (Fin n)} (hYZ : Disjoint Y Z) (x : Fin n → α) :
    marginal P ↑Y x = ∑ z : Z → α, marginal P ↑(Y ∪ Z) (updateFinset x Z z) := by
  classical
  simp only [marginal_coe]
  have hfill_eq : ∀ (z : Z → α) (i : Fin n) (h : i ∈ Z), updateFinset x Z z i = z ⟨i, h⟩ := by
    intro z i h
    exact dite_eq_left h
  have hfill_ne : ∀ (z : Z → α) (i : Fin n) (h : i ∉ Z), updateFinset x Z z i = x i := by
    intro z i h
    exact dite_eq_right h
  have hfib : ∀ z : Z → α,
      (univ.filter (fun x' : Fin n → α => ∀ i ∈ Y, x' i = x i)).filter
        (fun x' => (fun j : Z => x' j) = z) =
        univ.filter (fun x' : Fin n → α => ∀ i ∈ Y ∪ Z, x' i = updateFinset x Z z i) := by
    intro z
    ext x'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hag, hgz⟩ i hi
      rw [Finset.mem_union] at hi
      rcases hi with hiY | hiZ
      · rw [hfill_ne z i (fun hz => Finset.disjoint_left.mp hYZ hiY hz)]
        exact hag i hiY
      · rw [hfill_eq z i hiZ]
        exact congrFun hgz ⟨i, hiZ⟩
    · intro hag
      refine ⟨fun i hiY => ?_, ?_⟩
      · have h := hag i (Finset.mem_union_left Z hiY)
        rw [hfill_ne z i (fun hz => Finset.disjoint_left.mp hYZ hiY hz)] at h
        exact h
      · apply funext
        rintro ⟨i, hiZ⟩
        have h := hag i (Finset.mem_union_right Y hiZ)
        rw [hfill_eq z i hiZ] at h
        exact h
  have hmaps : ∀ x' ∈ univ.filter (fun x' : Fin n → α => ∀ i ∈ Y, x' i = x i),
      (fun j : Z => x' j) ∈ (univ : Finset (Z → α)) :=
    fun x' _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := univ.filter (fun x' : Fin n → α => ∀ i ∈ Y, x' i = x i))
    (t := (univ : Finset (Z → α))) (g := fun x' j => x' j) hmaps P]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [hfib z]

namespace BayesNet

/-- **Intervening does not change the law of pre-treatment covariates**: if no node of `Z` is a
descendant of a node of `X`, then `P(z | do(x)) = P(z)`. By rule 3 of the do-calculus
(`doCalculus_rule3` with `X := ∅`, `Y := Z`, `Z := X`, `W := ∅`), whose d-separation hypothesis
is `dSeparated_mutilateSet_of_not_isDescendant`. -/
theorem marginal_mutilateSet_of_preTreatment [Fintype α] [Nonempty α] {n : ℕ}
    (b : BayesNet α n) {X Z : Finset (Fin n)} (x : Fin n → α) (hXZ : Disjoint X Z)
    (h : ∀ k ∈ X, ∀ z ∈ Z, ¬b.IsDescendant k z) :
    marginal (b.mutilateSet X x).joint ↑Z x = marginal b.joint ↑Z x := by
  classical
  have hmarg_empty : ∀ (c : BayesNet α n),
      marginal c.joint ↑(∅ : Finset (Fin n)) x = 1 := by
    intro c
    rw [marginal_coe]
    have hfil : (univ.filter
        (fun x' : Fin n → α => ∀ i ∈ (∅ : Finset (Fin n)), x' i = x i)) = univ := by
      ext x'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      intro i hi
      exact (Finset.notMem_empty i hi).elim
    rw [hfil]
    exact c.sum_joint
  have hZWdef : ∀ z : Fin n, z ∈ X ↔
      z ∈ X ∧ ∀ w ∈ (∅ : Finset (Fin n)), ¬(b.mutilateSet ∅ x).IsDescendant z w := by
    intro z
    constructor
    · intro hzx
      exact ⟨hzx, fun w hmem _ => (Finset.notMem_empty w hmem).elim⟩
    · intro hzx
      exact hzx.1
  have hdsep := b.dSeparated_mutilateSet_of_not_isDescendant x h
  have hd : ((b.mutilateSet (∅ ∪ X) x).DSeparated (Z : Set (Fin n)) (X : Set (Fin n))
      ((∅ ∪ ∅ : Finset (Fin n)) : Set (Fin n))) := by
    simpa only [Finset.empty_union] using hdsep
  have hwz : marginal (b.mutilateSet (∅ ∪ X) x).joint
      ((∅ : Finset (Fin n)) : Set (Fin n)) x ≠ 0 := by
    simp only [Finset.empty_union, hmarg_empty]
    norm_num
  have hw : marginal (b.mutilateSet ∅ x).joint ((∅ : Finset (Fin n)) : Set (Fin n)) x ≠ 0 := by
    rw [hmarg_empty]
    norm_num
  have h3 := b.doCalculus_rule3 (X := ∅) (Y := Z) (Z := X) (W := ∅) x
    (by simp) (by simp) (by simp) hXZ.symm (by simp) (by simp) X hZWdef hd hwz hw
  simp only [Finset.empty_union, Finset.union_empty] at h3
  rw [b.joint_mutilateSet_empty x] at h3
  simp only [hmarg_empty, div_one] at h3
  exact h3

end BayesNet

namespace DomainPair

variable {n : ℕ} {D : SelectionDiagram n}

private theorem tp_aux_selNet_marginal_insert_c [Fintype α] [DecidableEq α] [Nonempty α]
    (M : DomainPair α D) (a c : α) (hac : a ≠ c) (X Z : Finset (Fin n)) (v : Fin n → α) :
    marginal ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons c v)).joint
        ↑(insert 0 (Z.map (Fin.succEmb n))) (Fin.cons c v) =
      1 / 2 * marginal (M.target.mutilateSet X v).joint ↑Z v := by
  rw [M.selNet_mutilateSet_marginal_cons a c X Z c c v v, ite_eq_left rfl,
    selPrior_weights_right hac]

private theorem tp_aux_selNet_marginal_insert_a [Fintype α] [DecidableEq α] [Nonempty α]
    (M : DomainPair α D) (a c : α) (hac : a ≠ c) (X Z : Finset (Fin n)) (v : Fin n → α) :
    marginal ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons a v)).joint
        ↑(insert 0 (Z.map (Fin.succEmb n))) (Fin.cons a v) =
      1 / 2 * marginal (M.source.mutilateSet X v).joint ↑Z v := by
  rw [M.selNet_mutilateSet_marginal_cons a c X Z a a v v, ite_eq_right hac,
    selPrior_weights_left hac]

private theorem tp_aux_selNet_marginal_map_ne_zero [Fintype α] [DecidableEq α] [Nonempty α]
    (M : DomainPair α D) (a c : α) (hac : a ≠ c) (X Z : Finset (Fin n)) (v : Fin n → α)
    {g : α} (hg : g = a ∨ g = c)
    (hT : marginal (M.target.mutilateSet X v).joint ↑Z v ≠ 0)
    (hS : marginal (M.source.mutilateSet X v).joint ↑Z v ≠ 0) :
    marginal ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons g v)).joint
      ↑(Z.map (Fin.succEmb n)) (Fin.cons g v) ≠ 0 := by
  have hle : marginal ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons g v)).joint
      ↑(insert 0 (Z.map (Fin.succEmb n))) (Fin.cons g v) ≤
      marginal ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons g v)).joint
        ↑(Z.map (Fin.succEmb n)) (Fin.cons g v) :=
    marginal_le_of_subset (fun x => Chain.joint_nonneg _ _ x)
      (fun _ hx => Finset.mem_insert_of_mem hx) _
  rcases hg with hga | hgc
  · rw [hga] at hle ⊢
    rw [tp_aux_selNet_marginal_insert_a M a c hac X Z v] at hle
    have hSpos : 0 < marginal (M.source.mutilateSet X v).joint ↑Z v :=
      lt_of_le_of_ne (marginal_nonneg (fun x => Chain.joint_nonneg _ _ x) _ _) (Ne.symm hS)
    have hpos : 0 < 1 / 2 * marginal (M.source.mutilateSet X v).joint ↑Z v :=
      mul_pos (by norm_num) hSpos
    exact ne_of_gt (lt_of_lt_of_le hpos hle)
  · rw [hgc] at hle ⊢
    rw [tp_aux_selNet_marginal_insert_c M a c hac X Z v] at hle
    have hTpos : 0 < marginal (M.target.mutilateSet X v).joint ↑Z v :=
      lt_of_le_of_ne (marginal_nonneg (fun x => Chain.joint_nonneg _ _ x) _ _) (Ne.symm hT)
    have hpos : 0 < 1 / 2 * marginal (M.target.mutilateSet X v).joint ↑Z v :=
      mul_pos (by norm_num) hTpos
    exact ne_of_gt (lt_of_lt_of_le hpos hle)

private theorem tp_aux_selNet_marginal_union_zero_ne_zero [Fintype α] [DecidableEq α]
    [Nonempty α] (M : DomainPair α D) (a c : α) (hac : a ≠ c) (X Z : Finset (Fin n))
    (v : Fin n → α) {g : α} (hg : g = a ∨ g = c)
    (hT : marginal (M.target.mutilateSet X v).joint ↑Z v ≠ 0)
    (hS : marginal (M.source.mutilateSet X v).joint ↑Z v ≠ 0) :
    marginal ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons g v)).joint
      ↑({0} ∪ Z.map (Fin.succEmb n)) (Fin.cons g v) ≠ 0 := by
  have hden : ({0} ∪ Z.map (Fin.succEmb n)) = insert 0 (Z.map (Fin.succEmb n)) := by
    rw [Finset.insert_eq]
  rw [hden]
  rcases hg with hga | hgc
  · rw [hga, tp_aux_selNet_marginal_insert_a M a c hac X Z v]
    exact mul_ne_zero (by norm_num) hS
  · rw [hgc, tp_aux_selNet_marginal_insert_c M a c hac X Z v]
    exact mul_ne_zero (by norm_num) hT

/-- A domain pair over a type with at most one value has equal target and source. -/
private theorem tp_aux_target_eq_source_of_subsingleton [Subsingleton α] (M : DomainPair α D) :
    M.target = M.source := by
  classical
  have hsubS : Subsingleton (Convexity.StdSimplex ℝ α) := by
    refine ⟨fun w1 w2 => ?_⟩
    by_cases hempty : IsEmpty α
    · exfalso
      have hw0 : w1.weights = 0 := Finsupp.ext fun a => hempty.elim a
      have hsum0 : w1.weights.sum (fun x r => r) = 0 := by
        simp [hw0, Finsupp.sum, Finsupp.support_zero]
      rw [w1.total] at hsum0
      norm_num at hsum0
    · rw [not_isEmpty_iff] at hempty
      obtain ⟨a₀⟩ := hempty
      have key : ∀ (w : Convexity.StdSimplex ℝ α) (a : α), w.weights a = 1 := by
        intro w a
        have hsub1 : w.weights.support ⊆ {a₀} := by
          intro s hs
          simp only [Finset.mem_singleton]
          exact Subsingleton.elim _ _
        rcases Finset.subset_singleton_iff.mp hsub1 with h0 | h1
        · exfalso
          have hsum0 : w.weights.sum (fun x r => r) = 0 := by
            simp [Finsupp.sum, h0]
          rw [w.total] at hsum0
          norm_num at hsum0
        · have hsum1 : w.weights.sum (fun x r => r) = w.weights a₀ := by
            simp [Finsupp.sum, h1]
          rw [w.total] at hsum1
          have haa : w.weights a = w.weights a₀ := congrArg _ (Subsingleton.elim _ _)
          rw [haa]
          exact hsum1.symm
      have hw : w1.weights = w2.weights := Finsupp.ext fun a => by rw [key w1 a, key w2 a]
      exact Convexity.StdSimplex.ext hw
  cases M with
  | mk cpt cpt' eq =>
    show BayesNet.mk D.pa cpt' = BayesNet.mk D.pa cpt
    congr 1
    funext k u
    exact @Subsingleton.elim _ hsubS _ _

/-- The left side of rule 1 in the selection network at `S = g`, for `g ∈ {a, c}`: the target
conditional when `g = c`, the source conditional otherwise. -/
private theorem tp_aux_selNet_rule1_lhs [Fintype α] [DecidableEq α] [Nonempty α]
    (M : DomainPair α D) (a c : α) (X Y Z : Finset (Fin n)) {g : α} (hg : g = a ∨ g = c)
    (v : Fin n → α) :
    marginal ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons g v)).joint
          ↑(Y.map (Fin.succEmb n) ∪ {0} ∪ Z.map (Fin.succEmb n)) (Fin.cons g v) /
        marginal ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons g v)).joint
          ↑({0} ∪ Z.map (Fin.succEmb n)) (Fin.cons g v) =
      if g = c then
        marginal (M.target.mutilateSet X v).joint ↑(Y ∪ Z) v /
          marginal (M.target.mutilateSet X v).joint ↑Z v
      else
        marginal (M.source.mutilateSet X v).joint ↑(Y ∪ Z) v /
          marginal (M.source.mutilateSet X v).joint ↑Z v := by
  have hnum : (Y.map (Fin.succEmb n) ∪ {0} ∪ Z.map (Fin.succEmb n)) =
      insert 0 ((Y ∪ Z).map (Fin.succEmb n)) := by
    rw [Finset.map_union, Finset.insert_eq]
    ac_rfl
  have hden : ({0} ∪ Z.map (Fin.succEmb n)) = insert 0 (Z.map (Fin.succEmb n)) := by
    rw [Finset.insert_eq]
  rw [hnum, hden,
    M.selNet_mutilateSet_marginal_cons a c X (Y ∪ Z) g g v v,
    M.selNet_mutilateSet_marginal_cons a c X Z g g v v]
  have hw : (selPrior a c).weights g ≠ 0 := by
    rcases hg with hga | hgc
    · rw [hga]
      exact ne_of_gt (selPrior_weights_left_pos a c)
    · rw [hgc]
      exact ne_of_gt (selPrior_weights_right_pos a c)
  rw [mul_div_mul_left _ _ hw]
  by_cases hgc : g = c <;> simp [hgc]

/-- A marginal of the intervened selection network over shifted nodes does not depend on the
value of `S` in the intervention and query assignment. (Adapted from the private lemma
`switch_marginal_cons_eq_r3` of `DoCalculus.lean`.) -/
private theorem tp_aux_selNet_rule1_rhs_eq [Fintype α] [DecidableEq α] [Nonempty α]
    (M : DomainPair α D) (a c : α) (X U : Finset (Fin n)) (f g : α) (v : Fin n → α) :
    marginal ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons f v)).joint
        ↑(U.map (Fin.succEmb n)) (Fin.cons f v) =
      marginal ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons g v)).joint
        ↑(U.map (Fin.succEmb n)) (Fin.cons g v) := by
  have hcons : ∀ (i : Fin n), (Fin.cons f v : Fin (n + 1) → α) (Fin.succEmb n i) =
      (Fin.cons g v : Fin (n + 1) → α) (Fin.succEmb n i) := by
    intro i
    simp only [Fin.coe_succEmb, Fin.cons_succ]
  have hnet : (M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons f v) =
      (M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons g v) := by
    apply BayesNet.mutilateSet_congr
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj
    exact hcons i
  rw [hnet]
  apply marginal_congr_of_eqOn
  intro i hi
  obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hi
  exact hcons k

/-- **z-specific transportability** (Pearl–Bareinboim 2014, Theorem 2): if `Z` is S-admissible
for the effect of `X` on `Y`, then `P*(y | do(x), z) = P(y | do(x), z)` wherever both
conditionals are defined. Proof: rule 1 of the do-calculus (`doCalculus_rule1`) in the selection
network at `S = c` and at `S = a`. -/
theorem condEffect_eq_of_sAdmissible [Fintype α] [Nonempty α] (M : DomainPair α D)
    {X Y Z : Finset (Fin n)} (v : Fin n → α) (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (hYZ : Disjoint Y Z) (hadm : D.SAdmissible X Y Z)
    (hT : marginal (M.target.mutilateSet X v).joint ↑Z v ≠ 0)
    (hS : marginal (M.source.mutilateSet X v).joint ↑Z v ≠ 0) :
    marginal (M.target.mutilateSet X v).joint ↑(Y ∪ Z) v /
        marginal (M.target.mutilateSet X v).joint ↑Z v =
      marginal (M.source.mutilateSet X v).joint ↑(Y ∪ Z) v /
        marginal (M.source.mutilateSet X v).joint ↑Z v := by
  classical
  by_cases hsub : Subsingleton α
  · have hts : M.target = M.source := tp_aux_target_eq_source_of_subsingleton M
    rw [hts]
  · obtain ⟨a, c, hac⟩ : ∃ a c : α, a ≠ c := by
      by_contra hcon
      apply hsub
      refine ⟨fun a' c' => ?_⟩
      by_contra hne
      exact hcon ⟨a', c', hne⟩
    have hne0 : ∀ (i : Fin n), Fin.succEmb n i ≠ 0 := by
      intro i
      rw [Fin.coe_succEmb]
      exact Fin.succ_ne_zero i
    have hmapdisj : ∀ {S T : Finset (Fin n)}, Disjoint S T →
        Disjoint (S.map (Fin.succEmb n)) (T.map (Fin.succEmb n)) := by
      intro S T hST
      rw [Finset.disjoint_left]
      rintro j hj1 hj2
      obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hj1
      obtain ⟨t, ht, hst⟩ := Finset.mem_map.mp hj2
      have hts : t = s := (Fin.succEmb n).injective hst
      subst hts
      exact Finset.disjoint_left.mp hST hs ht
    have h0notmem : ∀ (S : Finset (Fin n)), 0 ∉ S.map (Fin.succEmb n) := by
      intro S h0
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h0
      exact hne0 i hi
    have dXY : Disjoint (X.map (Fin.succEmb n)) (Y.map (Fin.succEmb n)) := hmapdisj hXY
    have dXZ : Disjoint (X.map (Fin.succEmb n)) (Z.map (Fin.succEmb n)) := hmapdisj hXZ
    have dYZ : Disjoint (Y.map (Fin.succEmb n)) (Z.map (Fin.succEmb n)) := hmapdisj hYZ
    have dX0 : Disjoint (X.map (Fin.succEmb n)) {0} :=
      Finset.disjoint_singleton_right.mpr (h0notmem X)
    have dY0 : Disjoint (Y.map (Fin.succEmb n)) {0} :=
      Finset.disjoint_singleton_right.mpr (h0notmem Y)
    have d0Z : Disjoint ({0} : Finset (Fin (n + 1))) (Z.map (Fin.succEmb n)) :=
      Finset.disjoint_singleton_left.mpr (h0notmem Z)
    have hd_c := M.selNet_dSeparated_of_sAdmissible a c (Fin.cons c v) hadm
    have hzw_c := tp_aux_selNet_marginal_union_zero_ne_zero M a c hac X Z v
      (Or.inr rfl : c = a ∨ c = c) hT hS
    have hw_c := tp_aux_selNet_marginal_map_ne_zero M a c hac X Z v
      (Or.inr rfl : c = a ∨ c = c) hT hS
    have r1c := (M.selNet a c).doCalculus_rule1
      (X := X.map (Fin.succEmb n)) (Y := Y.map (Fin.succEmb n)) (Z := {0})
      (W := Z.map (Fin.succEmb n)) (Fin.cons c v)
      dXY dX0 dXZ dY0 dYZ d0Z hd_c hzw_c hw_c
    have e1c := tp_aux_selNet_rule1_lhs M a c X Y Z (Or.inr rfl : c = a ∨ c = c) v
    rw [e1c, ite_eq_left rfl] at r1c
    have hd_a := M.selNet_dSeparated_of_sAdmissible a c (Fin.cons a v) hadm
    have hzw_a := tp_aux_selNet_marginal_union_zero_ne_zero M a c hac X Z v
      (Or.inl rfl : a = a ∨ a = c) hT hS
    have hw_a := tp_aux_selNet_marginal_map_ne_zero M a c hac X Z v
      (Or.inl rfl : a = a ∨ a = c) hT hS
    have r1a := (M.selNet a c).doCalculus_rule1
      (X := X.map (Fin.succEmb n)) (Y := Y.map (Fin.succEmb n)) (Z := {0})
      (W := Z.map (Fin.succEmb n)) (Fin.cons a v)
      dXY dX0 dXZ dY0 dYZ d0Z hd_a hzw_a hw_a
    have e1a := tp_aux_selNet_rule1_lhs M a c X Y Z (Or.inl rfl : a = a ∨ a = c) v
    rw [e1a, ite_eq_right hac] at r1a
    have hN : marginal ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons c v)).joint
          ↑(Y.map (Fin.succEmb n) ∪ Z.map (Fin.succEmb n)) (Fin.cons c v) =
        marginal ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons a v)).joint
          ↑(Y.map (Fin.succEmb n) ∪ Z.map (Fin.succEmb n)) (Fin.cons a v) := by
      rw [show Y.map (Fin.succEmb n) ∪ Z.map (Fin.succEmb n) = (Y ∪ Z).map (Fin.succEmb n)
        from by rw [Finset.map_union]]
      exact tp_aux_selNet_rule1_rhs_eq M a c X (Y ∪ Z) c a v
    have hD : marginal ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons c v)).joint
          ↑(Z.map (Fin.succEmb n)) (Fin.cons c v) =
        marginal ((M.selNet a c).mutilateSet (X.map (Fin.succEmb n)) (Fin.cons a v)).joint
          ↑(Z.map (Fin.succEmb n)) (Fin.cons a v) :=
      tp_aux_selNet_rule1_rhs_eq M a c X Z c a v
    rw [hN, hD] at r1c
    rw [r1c, r1a]

/-- **The transport formula** (Pearl–Bareinboim 2014, Corollary 1 with eq. (3.1); AAAI 2011,
Corollary 1 with eqs. (1) and (6)): let `D` be a selection diagram, `M` a pair of domains inducing
it, and `X`, `Y`, `Z` pairwise disjoint sets of nodes such that `Z` is S-admissible for the
effect of `X` on `Y` (`hadm`), `Z` consists of pre-treatment covariates (`hpre`), and every value
of `Z` with positive target probability has positive source probability (`hov`). Then
`P*(y | do(x)) = ∑_z P(y | do(x), z) P*(z)`, with `y` and the intervention values read off `x`.
The hypotheses `hpre` and `hov` are the source's (see the module documentation); neither can be
dropped. -/
theorem transport_formula [Fintype α] [Nonempty α] (M : DomainPair α D)
    {X Y Z : Finset (Fin n)} (x : Fin n → α) (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (hYZ : Disjoint Y Z) (hadm : D.SAdmissible X Y Z) (hpre : D.PreTreatment X Z)
    (hov : ∀ z : Z → α, marginal M.target.joint ↑Z (updateFinset x Z z) ≠ 0 →
      marginal M.source.joint ↑Z (updateFinset x Z z) ≠ 0) :
    marginal (M.target.mutilateSet X x).joint ↑Y x =
      ∑ z : Z → α,
        marginal (M.source.mutilateSet X x).joint ↑(Y ∪ Z) (updateFinset x Z z) /
            marginal (M.source.mutilateSet X x).joint ↑Z (updateFinset x Z z) *
          marginal M.target.joint ↑Z (updateFinset x Z z) := by
  classical
  rw [marginal_eq_sum_updateFinset _ hYZ x]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  have hfillX : ∀ i ∈ X, updateFinset x Z z i = x i := by
    intro i hi
    have hni : i ∉ Z := fun hz => Finset.disjoint_left.mp hXZ hi hz
    unfold updateFinset
    exact dite_eq_right hni
  have hTm : M.target.mutilateSet X x = M.target.mutilateSet X (updateFinset x Z z) :=
    BayesNet.mutilateSet_congr _ _ (fun j hj => (hfillX j hj).symm)
  have hSm : M.source.mutilateSet X x = M.source.mutilateSet X (updateFinset x Z z) :=
    BayesNet.mutilateSet_congr _ _ (fun j hj => (hfillX j hj).symm)
  have preT : ∀ k ∈ X, ∀ z' ∈ Z, ¬M.target.IsDescendant k z' := by
    intro k hk z' hz'
    rw [M.isDescendant_target]
    exact hpre k hk z' hz'
  have preS : ∀ k ∈ X, ∀ z' ∈ Z, ¬M.source.IsDescendant k z' := by
    intro k hk z' hz'
    rw [M.isDescendant_source]
    exact hpre k hk z' hz'
  rw [hTm, hSm]
  by_cases hTf :
      marginal (M.target.mutilateSet X (updateFinset x Z z)).joint ↑Z (updateFinset x Z z) = 0
  · have hT0 : marginal M.target.joint ↑Z (updateFinset x Z z) = 0 := by
      have e := M.target.marginal_mutilateSet_of_preTreatment (updateFinset x Z z) hXZ preT
      rw [← e]
      exact hTf
    have hnum0 : marginal (M.target.mutilateSet X (updateFinset x Z z)).joint ↑(Y ∪ Z)
        (updateFinset x Z z) = 0 := by
      have hle : marginal (M.target.mutilateSet X (updateFinset x Z z)).joint ↑(Y ∪ Z)
          (updateFinset x Z z) ≤
          marginal (M.target.mutilateSet X (updateFinset x Z z)).joint ↑Z (updateFinset x Z z) :=
        marginal_le_of_subset (fun t => Chain.joint_nonneg _ _ t)
          Finset.subset_union_right _
      rw [hTf] at hle
      have hnn : 0 ≤ marginal (M.target.mutilateSet X (updateFinset x Z z)).joint ↑(Y ∪ Z)
          (updateFinset x Z z) :=
        marginal_nonneg (fun t => Chain.joint_nonneg _ _ t) _ _
      exact le_antisymm hle hnn
    rw [hnum0, hT0, mul_zero]
  · have hSf : marginal (M.source.mutilateSet X (updateFinset x Z z)).joint ↑Z
        (updateFinset x Z z) ≠ 0 := by
      have eT := M.target.marginal_mutilateSet_of_preTreatment (updateFinset x Z z) hXZ preT
      have eS := M.source.marginal_mutilateSet_of_preTreatment (updateFinset x Z z) hXZ preS
      have hTpl : marginal M.target.joint ↑Z (updateFinset x Z z) ≠ 0 := by
        rw [← eT]
        exact hTf
      have hSpl : marginal M.source.joint ↑Z (updateFinset x Z z) ≠ 0 := hov z hTpl
      rw [eS]
      exact hSpl
    have hce := M.condEffect_eq_of_sAdmissible (updateFinset x Z z) hXY hXZ hYZ hadm hTf hSf
    have hdecomp : marginal (M.target.mutilateSet X (updateFinset x Z z)).joint ↑(Y ∪ Z)
          (updateFinset x Z z) =
        marginal (M.target.mutilateSet X (updateFinset x Z z)).joint ↑(Y ∪ Z) (updateFinset x Z z) /
          marginal (M.target.mutilateSet X (updateFinset x Z z)).joint ↑Z (updateFinset x Z z) *
          marginal (M.target.mutilateSet X (updateFinset x Z z)).joint ↑Z (updateFinset x Z z) :=
      (div_mul_cancel₀ _ hTf).symm
    rw [hdecomp, hce,
      M.target.marginal_mutilateSet_of_preTreatment (updateFinset x Z z) hXZ preT]

end DomainPair

namespace SelectionDiagram

variable {n : ℕ} (D : SelectionDiagram n)

/-- **The target effect is transportable** (Pearl–Bareinboim 2014, Definition 5 and the first
clause of Corollary 1): under the hypotheses of `DomainPair.transport_formula` on `D`, the target
effect `P*(y | do(x))` is determined by exactly the quantities the formula consumes: the source
interventional marginals on `Y ∪ Z` and on `Z` at each `z`, and the target observational
`Z`-marginal at each `z` — not by the complete joints, so latent coordinates outside `X`, `Y`
and `Z` are never compared. The class is the domain pairs inducing `D` with overlap. -/
theorem identifiedOn_transport [Fintype α] [Nonempty α] {X Y Z : Finset (Fin n)}
    (x : Fin n → α) (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hadm : D.SAdmissible X Y Z) (hpre : D.PreTreatment X Z) :
    IdentifiedOn
      {M : DomainPair α D | ∀ z : Z → α, marginal M.target.joint ↑Z (updateFinset x Z z) ≠ 0 →
        marginal M.source.joint ↑Z (updateFinset x Z z) ≠ 0}
      (fun M => ((fun z : Z → α => (marginal (M.source.mutilateSet X x).joint ↑(Y ∪ Z)
            (updateFinset x Z z),
          marginal (M.source.mutilateSet X x).joint ↑Z (updateFinset x Z z))),
        fun z : Z → α => marginal M.target.joint ↑Z (updateFinset x Z z)))
      (fun M => marginal (M.target.mutilateSet X x).joint ↑Y x) := by
  refine IdentifiedOn.of_eq_comp
    (F := fun p : ((Z → α) → ℝ × ℝ) × ((Z → α) → ℝ) =>
      ∑ z : Z → α, (p.1 z).1 / (p.1 z).2 * p.2 z) (fun M hM => ?_)
  exact M.transport_formula x hXY hXZ hYZ hadm hpre hM

end SelectionDiagram

end Cslib.MachineLearning.GraphicalModels
