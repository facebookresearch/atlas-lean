/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The species-reaction graph criterion for unique equilibria

A reaction network on a finite set `S` of species is operated in a continuous-flow stirred-tank
reactor (CFSTR): with flow rate per volume `g/V > 0` and nonnegative feed concentrations
`c^f`, mass action gives `ċ = (g/V) (c^f - c) + ∑ (reaction terms)`. The network has the **capacity
for multiple positive equilibria** if for some `g/V > 0`, `c^f ≥ 0` and positive rate constants
this system has two distinct equilibria with all concentrations positive.

The **species-reaction (SR) graph** has a species node for each species and a reaction node for
each reaction or reversible reaction pair. If a species appears in a complex at the head or tail
of a reaction node, an unoriented edge joins the species node to the reaction node; it is labeled
by that complex, and its stoichiometric coefficient is the coefficient of the species in the
label. Two edges meeting at a reaction node with the same complex label form a **c-pair**. A cycle
is an **o-cycle** if it contains an odd number of c-pairs and an **e-cycle** otherwise. It is an
**s-cycle** if alternately multiplying and dividing the stoichiometric coefficients along it gives
`1`. Two cycles have a **species-to-reaction (S-to-R) intersection** if their common edges form a
path that begins at a species node and ends at a reaction node, or a disjoint union of such paths.

**Theorem 1.1** (Craciun–Feinberg 2006). Consider a reaction network such that in its SR graph
(i) each cycle is an o-cycle or an s-cycle and (ii) no two e-cycles have an S-to-R intersection.
Then, taken with mass-action kinetics, the network does not have the capacity for multiple
positive equilibria.

Representation. Each reaction node `r` carries two distinct complexes `lhs r` and `rhs r` with
natural-number coefficients, a forward reaction `lhs r → rhs r`, and the reverse reaction when
`r` is a reversible pair. An edge is a triple (species, reaction node, side), so a species that
occurs in both complexes of a reaction node gives two parallel edges. A cycle of length `2k`
visits distinct species nodes `s_0, …, s_{k-1}` and distinct reaction nodes `r_0, …, r_{k-1}`,
entering `r_i` from `s_i` and leaving it to `s_{i+1}` (indices mod `k`) along two different
edges. Its common edges with another cycle are a union of maximal runs of consecutive edges, and
a run joins a species node to a reaction node exactly when it has an odd number of edges.

Sources: G. Craciun, M. Feinberg, "Multiple equilibria in complex chemical reaction networks:
II. The species-reaction graph", SIAM J. Appl. Math. 66 (2006) 1321–1338, Section 1,
Theorem 1.1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.Group.Nat.Even

@[expose] public section

namespace WantedExt.Biology.Biophysics.SpeciesReactionGraphWanted

/-- A reaction network whose reaction nodes are reactions or reversible reaction pairs: node `r`
has the distinct complexes `lhs r` and `rhs r`, the reaction `lhs r → rhs r`, and the reverse
reaction `rhs r → lhs r` when `reversible r`. -/
structure SRNetwork (S ρ : Type*) where
  /-- The left complex of each reaction node. -/
  lhs : ρ → S → ℕ
  /-- The right complex of each reaction node. -/
  rhs : ρ → S → ℕ
  /-- Whether the reaction node is a reversible pair. -/
  reversible : ρ → Bool
  /-- The two complexes of a reaction node are distinct. -/
  lhs_ne_rhs : ∀ r, lhs r ≠ rhs r

namespace SRNetwork

variable {S ρ : Type*} (N : SRNetwork S ρ)

/-- The CFSTR mass-action vector field with flow rate per volume `flow`, feed concentrations `cf`,
forward rate constants `kf` and reverse rate constants `kb`. -/
noncomputable def cfstrField [Fintype S] [Fintype ρ] (flow : ℝ) (cf : S → ℝ) (kf kb : ρ → ℝ)
    (c : S → ℝ) : S → ℝ :=
  fun s => flow * (cf s - c s) + ∑ r, (kf r * (∏ s', c s' ^ N.lhs r s') *
      ((N.rhs r s : ℝ) - N.lhs r s) +
    if N.reversible r then kb r * (∏ s', c s' ^ N.rhs r s') * ((N.lhs r s : ℝ) - N.rhs r s)
    else 0)

/-- The network has the capacity for multiple positive equilibria in the CFSTR. -/
def HasCapacityForMultipleEquilibria [Fintype S] [Fintype ρ] : Prop :=
  ∃ (flow : ℝ) (cf : S → ℝ) (kf kb : ρ → ℝ), 0 < flow ∧ (∀ s, 0 ≤ cf s) ∧
    (∀ r, 0 < kf r) ∧ (∀ r, 0 < kb r) ∧
    ∃ a b : S → ℝ, a ≠ b ∧ (∀ s, 0 < a s) ∧ (∀ s, 0 < b s) ∧
      N.cfstrField flow cf kf kb a = 0 ∧ N.cfstrField flow cf kf kb b = 0

/-- The complex on side `side` of reaction node `r` (`false`: `lhs`, `true`: `rhs`). -/
def complexOn (r : ρ) (side : Bool) : S → ℕ :=
  if side then N.rhs r else N.lhs r

/-- An edge of the SR graph: species `s`, reaction node `r`, and the side whose complex labels
the edge; it is present when `s` occurs in that complex. -/
structure Edge (S ρ : Type*) where
  /-- The species node. -/
  species : S
  /-- The reaction node. -/
  rxn : ρ
  /-- The side of the reaction node whose complex labels the edge. -/
  side : Bool

/-- The stoichiometric coefficient of an edge: the coefficient of its species in its label. -/
def coeff (e : Edge S ρ) : ℕ :=
  N.complexOn e.rxn e.side e.species

/-- A cycle of the SR graph of length `2k`: distinct species `sp i` and distinct reaction nodes
`rx i`; the cycle enters `rx i` from `sp i` along the edge labeled by side `inSide i` and leaves it
to `sp (i + 1)` along the edge labeled by side `outSide i`, these two edges being different. -/
structure Cycle (k : ℕ) where
  /-- The species nodes, in order. -/
  sp : Fin (k + 1) → S
  /-- The reaction nodes, in order. -/
  rx : Fin (k + 1) → ρ
  /-- The label side of the edge entering `rx i`. -/
  inSide : Fin (k + 1) → Bool
  /-- The label side of the edge leaving `rx i`. -/
  outSide : Fin (k + 1) → Bool
  sp_injective : Function.Injective sp
  rx_injective : Function.Injective rx
  in_edge : ∀ i, 0 < N.complexOn (rx i) (inSide i) (sp i)
  out_edge : ∀ i, 0 < N.complexOn (rx i) (outSide i) (sp (i + 1))
  edges_ne : ∀ i, (sp i, inSide i) ≠ (sp (i + 1), outSide i)

variable {N}

namespace Cycle

variable {k : ℕ} (C : N.Cycle k)

/-- The edge entering reaction node `rx i`. -/
def inEdge (i : Fin (k + 1)) : Edge S ρ :=
  ⟨C.sp i, C.rx i, C.inSide i⟩

/-- The edge leaving reaction node `rx i`. -/
def outEdge (i : Fin (k + 1)) : Edge S ρ :=
  ⟨C.sp (i + 1), C.rx i, C.outSide i⟩

/-- The `j`-th edge of the cycle in cyclic order (period `2 (k + 1)`). -/
def edgeAt (j : ℕ) : Edge S ρ :=
  if j % 2 = 0 then C.inEdge ⟨j / 2 % (k + 1), Nat.mod_lt _ k.succ_pos⟩
  else C.outEdge ⟨j / 2 % (k + 1), Nat.mod_lt _ k.succ_pos⟩

/-- The set of edges of the cycle. -/
def edges : Set (Edge S ρ) :=
  Set.range C.inEdge ∪ Set.range C.outEdge

open scoped Classical in
/-- The number of c-pairs: reaction nodes whose two cycle edges carry the same complex label. -/
noncomputable def numCPairs : ℕ :=
  (Finset.univ.filter fun i => C.inSide i = C.outSide i).card

/-- An o-cycle: an odd number of c-pairs. -/
def IsOCycle : Prop :=
  Odd C.numCPairs

/-- An e-cycle: an even number of c-pairs. -/
def IsECycle : Prop :=
  Even C.numCPairs

/-- An s-cycle: alternately multiplying and dividing the stoichiometric coefficients along the
cycle gives `1`. -/
def IsSCycle : Prop :=
  ∏ i, ((N.coeff (C.inEdge i) : ℚ) / N.coeff (C.outEdge i)) = 1

end Cycle

/-- Two cycles have a species-to-reaction intersection: their common edges are nonempty, are not
all the edges of the first cycle, and every maximal run of consecutive common edges along the
first cycle has an odd number of edges (so joins a species node to a reaction node). -/
def STORIntersection {k l : ℕ} (C : N.Cycle k) (D : N.Cycle l) : Prop :=
  (C.edges ∩ D.edges).Nonempty ∧ ¬ C.edges ⊆ D.edges ∧
    ∀ a len : ℕ, 0 < len → (∀ i < len, C.edgeAt (a + i) ∈ D.edges) →
      C.edgeAt (a + 2 * (k + 1) - 1) ∉ D.edges → C.edgeAt (a + len) ∉ D.edges → Odd len

end SRNetwork

open SRNetwork

/-- **Species-reaction graph theorem** (Craciun–Feinberg 2006, Theorem 1.1). If in the SR graph
of a network (i) each cycle is an o-cycle or an s-cycle and (ii) no two e-cycles have a
species-to-reaction intersection, then the network, taken with mass-action kinetics in a CFSTR,
does not have the capacity for multiple positive equilibria.

Source: G. Craciun, M. Feinberg, SIAM J. Appl. Math. 66 (2006) 1321–1338, Theorem 1.1. -/
theorem_wanted not_hasCapacityForMultipleEquilibria {S ρ : Type*} [Fintype S] [DecidableEq S]
    [Fintype ρ] (N : SRNetwork S ρ)
    (h1 : ∀ (k : ℕ) (C : N.Cycle k), C.IsOCycle ∨ C.IsSCycle)
    (h2 : ∀ (k l : ℕ) (C : N.Cycle k) (D : N.Cycle l), C.IsECycle → D.IsECycle →
      ¬ STORIntersection C D) :
    ¬ N.HasCapacityForMultipleEquilibria

end WantedExt.Biology.Biophysics.SpeciesReactionGraphWanted
