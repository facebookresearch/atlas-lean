/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyNonneg
public import Mathlib.Algebra.Order.Ring.Defs
public import MathlibExt.Combinatorics.Enumerative.LindstromGesselViennot
public import MathlibExt.LinearAlgebra.Matrix.PositiveMinors
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
# Weight matrices of planar networks are totally nonnegative

Fomin and Zelevinsky, *Total positivity: tests and parametrizations*, Math. Intelligencer 22
(2000), arXiv:math/9912128v1, Corollary 2: if a planar network has nonnegative real weights, its
weight matrix is totally nonnegative. The proof applies the weighted Lindström–Gessel–Viennot
lemma `MetaMathlibExt.lindstrom_gessel_viennot_weighted` to every minor: each minor is a sum of
weights of families of vertex-disjoint paths, hence nonnegative. Planarity enters only through
the noncrossing hypothesis of that lemma.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Nonnegative edge weights give nonnegative path weights.** -/
theorem lgvPathWeight_nonneg {V : Type*} {R : Type*} [CommRing R] [PartialOrder R]
    [IsOrderedRing R] {wt : V → V → R} (hwt : ∀ u v, 0 ≤ wt u v) :
    ∀ p : List V, 0 ≤ lgvPathWeight wt p
  | [] => by simp [lgvPathWeight]
  | [_] => by simp [lgvPathWeight]
  | u :: v :: l => by
    rw [lgvPathWeight]
    exact mul_nonneg (hwt u v) (lgvPathWeight_nonneg hwt (v :: l))

/-- **Total nonnegativity of planar networks.** Let `E` be an acyclic relation on `V`, with
nonnegative edge weights `wt` in an ordered commutative ring, sources `A 0, …, A (n-1)`, sinks
`B 0, …, B (n-1)` and finite sets `P i j` of vertex-list paths from `A i` to `B j`. If every path
from `A i` to `B k` meets every path from `A j` to `B l` whenever `i < j` and `l < k`, then the
weight matrix `M i j = ∑_{p ∈ P i j} w(p)` is totally nonnegative: all its minors are `≥ 0`
(Fomin and Zelevinsky, *Total positivity: tests and parametrizations*, Math. Intelligencer 22
(2000), no. 1, 23–33, arXiv:math/9912128v1, Corollary 2, from Lemma 1). The noncrossing
hypothesis holds for the planar networks of the source, whose sources and sinks lie on the
boundary in the same order; it is the only consequence of planarity that the proof uses. -/
theorem planarNetwork_isTotallyNonneg
    {V : Type*}
    {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
    (n : ℕ)
    (E : V → V → Prop)
    (A B : Fin n → V)
    (rank : V → ℕ)
    (hAcyc : ∀ u v : V, E u v → rank u < rank v)
    (P : Fin n → Fin n → Finset (List V))
    (hPath : ∀ i j : Fin n, ∀ p : List V, p ∈ P i j ↔
      (p.head? = some (A i) ∧ p.getLast? = some (B j) ∧
        p.IsChain (fun u v => E u v)))
    (wt : V → V → R) (hwt : ∀ u v, 0 ≤ wt u v)
    (hPlanar : ∀ i j k l : Fin n, i < j → l < k →
      ∀ p ∈ P i k, ∀ q ∈ P j l, ∃ v : V, v ∈ p ∧ v ∈ q) :
    (Matrix.of fun i j => ∑ p ∈ P i j, lgvPathWeight wt p).IsTotallyNonneg := by
  classical
  intro k r c hr hc
  let S : Finset (Fin k → List V) :=
    (Fintype.piFinset fun a => P (r a) (c a)).filter
      fun F => ∀ a b : Fin k, a ≠ b → Disjoint (F a).toFinset (F b).toFinset
  have hdet := lindstrom_gessel_viennot_weighted k E (A ∘ r) (B ∘ c) rank hAcyc
    (fun a b => P (r a) (c b)) (fun a b p => hPath (r a) (c b) p) wt
    ((Matrix.of fun i j => ∑ p ∈ P i j, lgvPathWeight wt p).submatrix r c)
    (fun a b => by simp)
    (fun a b d l hab hld p hp q hq => hPlanar (r a) (r b) (c d) (c l) (hr hab) (hc hld) p hp q hq)
    S (fun F => by simp [S, Fintype.mem_piFinset])
  rw [← hdet]
  exact Finset.sum_nonneg fun F _ => Finset.prod_nonneg fun a _ => lgvPathWeight_nonneg hwt _

/-- **Positive edge weights give positive path weights.** -/
theorem lgvPathWeight_pos {V : Type*} {wt : V → V → ℝ} (hwt : ∀ u v, 0 < wt u v) :
    ∀ p : List V, 0 < lgvPathWeight wt p
  | [] => by simp [lgvPathWeight]
  | [_] => by simp [lgvPathWeight]
  | u :: v :: l => by
    rw [lgvPathWeight]
    exact mul_pos (hwt u v) (lgvPathWeight_pos hwt (v :: l))

/-- **Total positivity of totally connected planar networks.** In the setting of
`planarNetwork_isTotallyNonneg`, with real edge weights, suppose the weights are positive and
the network is totally connected: for all row indices `r 0 < ⋯ < r (k-1)` and column indices
`c 0 < ⋯ < c (k-1)` there is a family of pairwise vertex-disjoint paths from `A (r a)` to
`B (c a)`. Then every minor of the weight matrix is positive (Fomin and Zelevinsky, *Total
positivity: tests and parametrizations*, Math. Intelligencer 22 (2000), no. 1, 23–33,
arXiv:math/9912128v1, Corollary 3). -/
theorem planarNetwork_hasPositiveMinors
    {V : Type*}
    (n : ℕ)
    (E : V → V → Prop)
    (A B : Fin n → V)
    (rank : V → ℕ)
    (hAcyc : ∀ u v : V, E u v → rank u < rank v)
    (P : Fin n → Fin n → Finset (List V))
    (hPath : ∀ i j : Fin n, ∀ p : List V, p ∈ P i j ↔
      (p.head? = some (A i) ∧ p.getLast? = some (B j) ∧
        p.IsChain (fun u v => E u v)))
    (wt : V → V → ℝ) (hwt : ∀ u v, 0 < wt u v)
    (hPlanar : ∀ i j k l : Fin n, i < j → l < k →
      ∀ p ∈ P i k, ∀ q ∈ P j l, ∃ v : V, v ∈ p ∧ v ∈ q)
    (hConn : ∀ (k : ℕ) (r c : Fin k → Fin n), StrictMono r → StrictMono c →
      ∃ F : Fin k → List V, (∀ a, F a ∈ P (r a) (c a)) ∧
        ∀ a b, a ≠ b → ∀ v, v ∈ F a → v ∉ F b) :
    Matrix.HasPositiveMinors (Matrix.of fun i j => ∑ p ∈ P i j, lgvPathWeight wt p) := by
  classical
  intro k r c hr hc
  let S : Finset (Fin k → List V) :=
    (Fintype.piFinset fun a => P (r a) (c a)).filter
      fun F => ∀ a b : Fin k, a ≠ b → Disjoint (F a).toFinset (F b).toFinset
  have hdet := lindstrom_gessel_viennot_weighted k E (A ∘ r) (B ∘ c) rank hAcyc
    (fun a b => P (r a) (c b)) (fun a b p => hPath (r a) (c b) p) wt
    ((Matrix.of fun i j => ∑ p ∈ P i j, lgvPathWeight wt p).submatrix r c)
    (fun a b => by simp)
    (fun a b d l hab hld p hp q hq => hPlanar (r a) (r b) (c d) (c l) (hr hab) (hc hld) p hp q hq)
    S (fun F => by simp [S, Fintype.mem_piFinset])
  rw [← hdet]
  obtain ⟨F, hFP, hFd⟩ := hConn k r c hr hc
  have hFS : F ∈ S := by
    simp only [S, Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨hFP, fun a b hab => Finset.disjoint_left.mpr fun v hva hvb => ?_⟩
    exact hFd a b hab v (List.mem_toFinset.mp hva) (List.mem_toFinset.mp hvb)
  exact Finset.sum_pos (fun F _ => Finset.prod_pos fun a _ => lgvPathWeight_pos hwt _) ⟨F, hFS⟩

end MetaMathlibExt
