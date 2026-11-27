/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# The moment curve and cyclic polytopes

The moment curve `t ↦ (t, t², …, t^d)` in `ℝ^d` is a curve of order `d`: no `d + 1` of its
points lie on a common affine hyperplane. The convex hull of `n` points on it is the cyclic
polytope `C_d(n)`, whose facets are described by Gale's evenness condition
(G. M. Ziegler, "Convex polytopes: extremal constructions and f-vector shapes",
IAS/Park City Math. Ser. 14 (2004), Example 2.6, arXiv:math/0411400v2).
-/

@[expose] public section

open Matrix

namespace MathlibExt.Geometry.Polytope

/-- **The moment curve.** The point `γ(t) = (t, t², …, t^d)` of `ℝ^d`. -/
noncomputable def momentCurve (d : ℕ) (t : ℝ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i : Fin d => t ^ (i.val + 1)

/-- **Coordinates of the moment curve.** The `i`-th coordinate of `γ(t)` is `t^{i+1}`. -/
@[simp]
theorem momentCurve_apply (d : ℕ) (t : ℝ) (i : Fin d) :
    momentCurve d t i = t ^ (i.val + 1) :=
  rfl

/-- **The moment curve is injective in positive dimension.** For `d ≥ 1`, distinct parameters
give distinct points `γ(t)`, already in the first coordinate `t`. -/
theorem momentCurve_injective {d : ℕ} (hd : 1 ≤ d) : Function.Injective (momentCurve d) := by
  intro a b h
  have := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v ⟨0, hd⟩) h
  simpa using this

/-- **The moment curve has order `d`.** Any `m ≤ d + 1` points `γ(t_1), …, γ(t_m)` of the moment
curve in `ℝ^d` with distinct parameters are affinely independent; for `m = d + 1` this says that
no `d + 1` points of the curve lie on a common affine hyperplane (Ziegler, PCMI lecture notes,
arXiv:math/0411400v2, Example 2.6). The proof reduces an affine dependence to a vanishing
combination of the columns of a Vandermonde matrix. -/
theorem affineIndependent_momentCurve {d m : ℕ} (hm : m ≤ d + 1) {t : Fin m → ℝ}
    (ht : Function.Injective t) :
    AffineIndependent ℝ (fun i => momentCurve d (t i)) := by
  classical
  rw [affineIndependent_iff_of_fintype]
  intro w hw0 hws
  have hsum : ∑ i, w i • momentCurve d (t i) = 0 := by
    rw [Finset.univ.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero w _ hw0 0,
      Finset.weightedVSubOfPoint_apply] at hws
    simpa using hws
  have hvec : w ᵥ* vandermonde t = 0 := by
    funext k
    simp only [vecMul, dotProduct, vandermonde_apply, Pi.zero_apply]
    rcases k with ⟨_ | j, hk⟩
    · simpa using hw0
    · have hj : j < d := by omega
      have h := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v ⟨j, hj⟩) hsum
      simpa [mul_comm] using h
  have hw : w = 0 := eq_zero_of_vecMul_eq_zero (det_vandermonde_ne_zero_iff.2 ht) hvec
  intro i
  simp [hw]

/-- **Vertices of a cyclic polytope.** The finite set `{γ(t_1), …, γ(t_n)}` of points on the
moment curve in `ℝ^d`; its convex hull is the cyclic polytope `C_d(n)` when the parameters are
distinct (Ziegler, PCMI lecture notes, arXiv:math/0411400v2, Example 2.6). -/
noncomputable def cyclicVertices (d : ℕ) {n : ℕ} (t : Fin n → ℝ) :
    Finset (EuclideanSpace ℝ (Fin d)) :=
  Finset.univ.image fun i => momentCurve d (t i)

/-- **Cyclic polytope.** The convex hull `C_d(n)` of `n` points `γ(t_1), …, γ(t_n)` of the moment
curve in `ℝ^d` (Ziegler, PCMI lecture notes, arXiv:math/0411400v2, Example 2.6). -/
noncomputable def cyclicPolytope (d : ℕ) {n : ℕ} (t : Fin n → ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  convexHull ℝ (cyclicVertices d t : Set (EuclideanSpace ℝ (Fin d)))

/-- **Gale's evenness condition.** A set `S` of indices in `{0, …, n - 1}` satisfies Gale's
evenness condition when any two indices `j < k` outside `S` are separated by an even number of
elements of `S`. For `t_1 < ⋯ < t_n` and `|S| = d`, Gale's evenness criterion says that the points
`γ(t_i)`, `i ∈ S`, span a facet of the cyclic polytope `C_d(n)` exactly when `S` satisfies this
condition (D. Gale, "Neighborly and cyclic polytopes", Proc. Sympos. Pure Math. 7 (1963);
Ziegler, PCMI lecture notes, arXiv:math/0411400v2, Example 2.6). -/
def GaleEvenness {n : ℕ} (S : Finset (Fin n)) : Prop :=
  ∀ j k : Fin n, j ∉ S → k ∉ S → j < k → Even (S.filter fun i => j < i ∧ i < k).card

instance {n : ℕ} (S : Finset (Fin n)) : Decidable (GaleEvenness S) := by
  unfold GaleEvenness
  infer_instance

end MathlibExt.Geometry.Polytope
