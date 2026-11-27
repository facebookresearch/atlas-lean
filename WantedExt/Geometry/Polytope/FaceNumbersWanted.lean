/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Geometry.Polytope.BoundaryComplex
public import WantedExt.Combinatorics.UpperBoundSimplicialSpheresWanted

/-!
# Face numbers of convex polytopes: wanted theorems

The Euler–Poincaré relation, the characterization of face numbers in dimension three,
and McMullen's upper bound theorem for polytopes.
Faces and face numbers are those of `MathlibExt.Geometry.Polytope`: exposed subsets of
`conv s`, counted by the dimension of their affine hull.
-/

@[expose] public section

open MathlibExt.Geometry.Polytope
open MathlibExt.Combinatorics.UpperBoundSimplicialSpheresWanted.Combinatorics
open UpperBoundSimplicialSpheresProblem (cyclicPolytopeFaceCount)

namespace MathlibExt.Geometry.Polytope.FaceNumbersWanted

/-- **Euler–Poincaré relation.** For every nonempty finite set `s` of points in `ℝ^n`, the face
numbers of the polytope `P = conv s`, of dimension `d = dim P`, satisfy
`f_0 - f_1 + f_2 - ⋯ + (-1)^d f_d = 1`, where `f_d = 1` counts `P` itself. Equivalently
`f_0 - f_1 + ⋯ + (-1)^{d-1} f_{d-1} = 1 + (-1)^{d-1}`, the form in G. M. Ziegler,
"Face numbers of 4-polytopes and 3-spheres", Proc. ICM 2002, Section 2 (arXiv:math/0208073);
for `d = 3` this is Euler's equation `f_0 - f_1 + f_2 = 2`. -/
theorem_wanted euler_poincare {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n)))
    (hs : s.Nonempty) :
    ∑ k ∈ Finset.range (dim s + 1), (-1 : ℤ) ^ k * (faceNumber s k : ℤ) = 1

/-- **Steinitz's lemma: the f-vectors of 3-polytopes.** A triple `(f₀, f₁, f₂)` of natural
numbers is the f-vector of a 3-dimensional polytope in `ℝ^3` if and only if
`f₀ - f₁ + f₂ = 2`, `f₂ ≤ 2 f₀ - 4` and `f₀ ≤ 2 f₂ - 4` (E. Steinitz, 1906; G. M. Ziegler,
"Convex polytopes: extremal constructions and f-vector shapes", IAS/Park City Math. Ser. 14
(2004), Lemma 1.1, arXiv:math/0411400v2). The source states it for integer triples; the
conditions force `f₀, f₂ ≥ 4`, so nothing is lost by taking natural numbers. -/
theorem_wanted steinitz_lemma (f₀ f₁ f₂ : ℕ) :
    (∃ s : Finset (EuclideanSpace ℝ (Fin 3)),
        (interior (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3))))).Nonempty ∧
          faceNumber s 0 = f₀ ∧ faceNumber s 1 = f₁ ∧ faceNumber s 2 = f₂) ↔
      ((f₀ : ℤ) - f₁ + f₂ = 2 ∧ (f₂ : ℤ) ≤ 2 * f₀ - 4 ∧ (f₀ : ℤ) ≤ 2 * f₂ - 4)

/-- **Upper bound theorem (McMullen).** Let `P = conv s` be a polytope of dimension `d` with `m`
vertices. Then for every `k < d` the number of `k`-dimensional faces of `P` is at most the
number of `k`-dimensional faces of the cyclic polytope `C_d(m)`, given by the h-vector formula
`cyclicPolytopeFaceCount m d k` (P. McMullen, "The maximum numbers of faces of a convex
polytope", Mathematika 17 (1970), 179–184). The polytope need not be simplicial, and need not
be full-dimensional in the ambient space. -/
theorem_wanted upper_bound_theorem {n d m k : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n)))
    (hd : dim s = d) (hm : faceNumber s 0 = m) (hk : k < d) :
    faceNumber s k ≤ cyclicPolytopeFaceCount m d k

end MathlibExt.Geometry.Polytope.FaceNumbersWanted
