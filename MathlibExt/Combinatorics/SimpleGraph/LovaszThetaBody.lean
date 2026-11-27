/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.LovaszTheta
public import Mathlib.Analysis.Convex.Hull

/-!
# The stable set polytope, the clique-constrained polytope and the theta body

For a finite graph `G` on `V`, three convex sets of vectors `x : V → ℝ`:

* `STAB(G)`, the convex hull of the characteristic vectors of the stable sets;
* `QSTAB(G)`, the vectors `x ≥ 0` with `∑_{v ∈ Q} x_v ≤ 1` for every clique `Q`;
* `TH(G)`, the theta body of Grötschel, Lovász and Schrijver: the vectors `x ≥ 0` with
  `∑_v cost c (a_v) x_v ≤ 1` for every orthogonal labeling `a` of `G` and every handle `c`.

We prove Knuth's Lemma 2, `STAB(G) ⊆ TH(G) ⊆ QSTAB(G)`: stable sets have total cost at most one,
and a clique gives a one-dimensional orthogonal labeling whose costs are its characteristic vector.

Source: D. E. Knuth, "The Sandwich Theorem", Electron. J. Combin. 1 (1994), #A1
(arXiv:math/9312214v1), §2 (definitions of STAB, QSTAB, TH and Lemma 2). Knuth measures costs
against the first coordinate vector; we allow any handle `c`, as in `LovaszTheta`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.LovaszTheta

open scoped RealInnerProductSpace
open Finset

variable {V : Type*} [Fintype V]

open Classical in
/-- **Characteristic vector of a vertex set.** The vector `V → ℝ` that is `1` on `S` and `0`
elsewhere (Knuth, *The Sandwich Theorem*, 1994, §2, "characteristic labeling"). -/
noncomputable def charVec (S : Finset V) : V → ℝ :=
  fun v => if v ∈ S then 1 else 0

/-- **Stable set polytope.** `STAB(G)` is the convex hull of the characteristic vectors of the
stable sets of `G` (Knuth, *The Sandwich Theorem*, 1994, §2). -/
def stab (G : SimpleGraph V) : Set (V → ℝ) :=
  convexHull ℝ {x | ∃ S : Finset V, G.IsIndepSet (S : Set V) ∧ x = charVec S}

/-- **Clique-constrained stable set polytope.** `QSTAB(G)` is the set of `x ≥ 0` with
`∑_{v ∈ Q} x_v ≤ 1` for every clique `Q` of `G` (Knuth, *The Sandwich Theorem*, 1994, §2). -/
def qstab (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | 0 ≤ x ∧ ∀ Q : Finset V, G.IsClique (Q : Set V) → ∑ v ∈ Q, x v ≤ 1}

/-- **Theta body.** `TH(G)` is the set of `x ≥ 0` with `∑_v cost c (a_v) x_v ≤ 1` for every
orthogonal labeling `a : V → ℝ^d` of `G` (any `d`) and every handle `c ∈ ℝ^d` (Knuth, *The
Sandwich Theorem*, 1994, §2, where `TH` is credited to Grötschel, Lovász and Schrijver; Knuth fixes
the handle to the first coordinate vector). -/
def th (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | 0 ≤ x ∧ ∀ (d : ℕ) (a : V → EuclideanSpace ℝ (Fin d)) (c : EuclideanSpace ℝ (Fin d)),
    IsOrthogonalLabeling G a → ∑ v, cost c (a v) * x v ≤ 1}

/-- **The theta body is convex.** It is an intersection of half-spaces and the orthant. -/
theorem convex_th (G : SimpleGraph V) : Convex ℝ (th G) := by
  intro x hx y hy s t hs ht hst
  refine ⟨?_, fun d a c ha => ?_⟩
  · intro v
    have h1 : 0 ≤ x v := hx.1 v
    have h2 : 0 ≤ y v := hy.1 v
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact add_nonneg (mul_nonneg hs h1) (mul_nonneg ht h2)
  · have h1 := hx.2 d a c ha
    have h2 := hy.2 d a c ha
    have e : ∑ v, cost c (a v) * (s • x + t • y) v =
        s * ∑ v, cost c (a v) * x v + t * ∑ v, cost c (a v) * y v := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [e]
    nlinarith

/-- **Stable sets lie in the theta body.** The characteristic vector of a stable set of `G` lies
in `TH(G)`, by Knuth's Lemma 1 (Knuth, *The Sandwich Theorem*, 1994, proof of Lemma 2). -/
theorem charVec_mem_th {G : SimpleGraph V} {S : Finset V} (hS : G.IsIndepSet (S : Set V)) :
    charVec S ∈ th G := by
  classical
  refine ⟨fun v => by simp only [charVec, Pi.zero_apply]; split_ifs <;> norm_num, ?_⟩
  intro d a c ha
  have h := sum_cost_le_one ha c hS
  calc ∑ v, cost c (a v) * charVec S v = ∑ v ∈ S, cost c (a v) := by
        simp only [charVec, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ ≤ 1 := h

/-- **The stable set polytope lies in the theta body.** `STAB(G) ⊆ TH(G)` (Knuth, *The Sandwich
Theorem*, 1994, Lemma 2). -/
theorem stab_subset_th (G : SimpleGraph V) : stab G ⊆ th G :=
  convexHull_min (by rintro x ⟨S, hS, rfl⟩; exact charVec_mem_th hS) (convex_th G)

/-- **The theta body lies in the clique-constrained polytope.** `TH(G) ⊆ QSTAB(G)`: the
characteristic vector of a clique, as a labeling in `ℝ¹` with handle `1`, is an orthogonal labeling
whose costs are `1` on the clique and `0` elsewhere (Knuth, *The Sandwich Theorem*, 1994,
Lemma 2). -/
theorem th_subset_qstab (G : SimpleGraph V) : th G ⊆ qstab G := by
  classical
  intro x ⟨hx0, hx⟩
  refine ⟨hx0, fun Q hQ => ?_⟩
  let a : V → EuclideanSpace ℝ (Fin 1) := fun v => if v ∈ Q then EuclideanSpace.single 0 1 else 0
  let c : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
  have ha : IsOrthogonalLabeling G a := by
    intro u v huv hadj
    by_cases hu : u ∈ Q
    · by_cases hv : v ∈ Q
      · exact absurd (hQ hu hv huv) hadj
      · simp [a, hv]
    · simp [a, hu]
  have hcost : ∀ v, cost c (a v) = if v ∈ Q then 1 else 0 := by
    intro v
    by_cases hv : v ∈ Q
    · simp [a, c, hv, cost, PiLp.norm_single]
    · simp [a, c, hv, cost]
  have h := hx 1 a c ha
  simp only [hcost, ite_mul, one_mul, zero_mul] at h
  rwa [Finset.sum_ite_mem, Finset.univ_inter] at h

/-- **Knuth's sandwich of convex sets.** For a finite graph, `STAB(G) ⊆ TH(G) ⊆ QSTAB(G)` (Knuth,
*The Sandwich Theorem*, 1994, Lemma 2, eq. (2.1)). -/
theorem stab_subset_th_subset_qstab (G : SimpleGraph V) :
    stab G ⊆ th G ∧ th G ⊆ qstab G :=
  ⟨stab_subset_th G, th_subset_qstab G⟩

end MathlibExt.Combinatorics.SimpleGraph.LovaszTheta
