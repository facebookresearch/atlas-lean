/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minimum degree of triangle-Ramsey-minimal graphs

`AIM-COMBINATORICS-0060` (AIM Graph Ramsey theory, Ramsey minimal
graphs, item 13): `s_r(3) = Θ(r² log r)` as `r → ∞`, where `s_r(3)`
is the least minimum degree of an `r`-Ramsey-minimal graph for the
triangle.
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Basic.Real.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.TriangleRamseyMinimalThetaWanted

/-- `r`-Ramsey property for the triangle `K3` on `Fin n` ([AIM-COMBINATORICS-0060], `aim-combinatorics-notes.json notes[59]`, Source item 13, Section Ramsey minimal graphs, Workshop Graph Ramsey theory). Every symmetric `r`-coloring contains a monochromatic triangle on three distinct vertices. -/
def IsTriangleRamsey (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℕ) : Prop :=
  ∀ c : Fin n → Fin n → Fin r,
    (∀ a : Fin n, ∀ b : Fin n, c a b = c b a) →
      ∃ u : Fin n, ∃ v : Fin n, ∃ w : Fin n,
        u ≠ v ∧ v ≠ w ∧ w ≠ u ∧ G.Adj u v ∧ G.Adj v w ∧ G.Adj w u ∧
          c u v = c v w ∧ c v w = c w u

/-- Vertex-deleted `r`-Ramsey property for the triangle at `x` ([AIM-COMBINATORICS-0060], `aim-combinatorics-notes.json notes[59]`, Source item 13, Section Ramsey minimal graphs, Workshop Graph Ramsey theory). Every symmetric `r`-coloring contains a monochromatic triangle with all three vertices distinct from `x`. -/
def IsTriangleRamseyDeleteVertex (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℕ)
    (x : Fin n) : Prop :=
  ∀ c : Fin n → Fin n → Fin r,
    (∀ a : Fin n, ∀ b : Fin n, c a b = c b a) →
      ∃ u : Fin n, ∃ v : Fin n, ∃ w : Fin n,
        u ≠ x ∧ v ≠ x ∧ w ≠ x ∧
          u ≠ v ∧ v ≠ w ∧ w ≠ u ∧ G.Adj u v ∧ G.Adj v w ∧ G.Adj w u ∧
          c u v = c v w ∧ c v w = c w u

/-- Ramsey-minimal property for the triangle ([AIM-COMBINATORICS-0060], `aim-combinatorics-notes.json notes[59]`, Source item 13, Section Ramsey minimal graphs, Workshop Graph Ramsey theory). `G` is `r`-Ramsey for the triangle, no proper spanning subgraph is, and deletion of any single vertex destroys the Ramsey property. -/
def IsRamseyMinimal (n : ℕ) (G : SimpleGraph (Fin n)) (r : ℕ) : Prop :=
  IsTriangleRamsey n G r ∧
    (∀ H : SimpleGraph (Fin n),
      (∀ u : Fin n, ∀ v : Fin n, H.Adj u v → G.Adj u v) →
        (∃ u : Fin n, ∃ v : Fin n, G.Adj u v ∧ ¬ H.Adj u v) →
          ¬ IsTriangleRamsey n H r) ∧
    ∀ x : Fin n, ¬ IsTriangleRamseyDeleteVertex n G r x

/-- Minimum-degree predicate via `Set.ncard` of adjacency sets ([AIM-COMBINATORICS-0060], `aim-combinatorics-notes.json notes[59]`, Source item 13, Section Ramsey minimal graphs, Workshop Graph Ramsey theory). `d` is below every vertex degree and attained at some vertex. -/
def HasMinDegree (n : ℕ) (G : SimpleGraph (Fin n)) (d : ℕ) : Prop :=
  (∀ v : Fin n, d ≤ Set.ncard { w : Fin n | G.Adj v w }) ∧
    ∃ v : Fin n, Set.ncard { w : Fin n | G.Adj v w } = d

/-- `s_r(3)` as the least minimum-degree over `r`-Ramsey-minimal graphs for the triangle, `0` if none ([AIM-COMBINATORICS-0060], `aim-combinatorics-notes.json notes[59]`, Source item 13, Section Ramsey minimal graphs, Workshop Graph Ramsey theory, Conjecture `$s_r(3) = \Theta(r^2 \log r)$`). -/
noncomputable def sRamsey (r : ℕ) : ℕ := by
  classical
  exact if h : ∃ d : ℕ, ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
      IsRamseyMinimal n G r ∧ HasMinDegree n G d then Nat.find h else 0

/-- AIM Combinatorics 0060 conjecture `s_r(3) = Theta (r^2 * log r)` as `r` tends to infinity ([AIM-COMBINATORICS-0060], `aim-combinatorics-notes.json notes[59]`, Source item 13, Section Ramsey minimal graphs, Workshop Graph Ramsey theory, Canonical tag conjecture). -/
def conjecture : Prop :=
  Asymptotics.IsTheta Filter.atTop
    (fun r : ℕ => (sRamsey r : ℝ))
    (fun r : ℕ => (r : ℝ) ^ 2 * Real.log (r : ℝ))

/--
Resolved true: Resolved true: Guo and Warnke (Packing nearly optimal Ramsey R(3,t) graphs,
arXiv:1711.05877) prove s_r(K_3) = Theta(r^2 log r), confirming the conjecture of Fox,
Grinshpun, Liebenau, Person and Szabó. Source: H. Guo and L. Warnke, Packing nearly optimal
Ramsey R(3,t) graphs, arXiv:1711.05877, https://arxiv.org/abs/1711.05877. Moved from
`OpenConjectures/Combinatorics/TriangleRamseyMinimalTheta`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.TriangleRamseyMinimalThetaWanted
