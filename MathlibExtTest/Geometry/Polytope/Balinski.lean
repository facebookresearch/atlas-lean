/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Polytope.Balinski

open MathlibExt.Geometry.Polytope

namespace MathlibExtTest.Geometry.Polytope.Balinski

/-- A singleton in zero-dimensional space has the required nonzero vertex count. -/
example (p : EuclideanSpace ℝ (Fin 0)) :
    0 < @Fintype.card _ (extremePoints_finite ({p} : Finset _)).fintype := by
  classical
  have hd : dim ({p} : Finset (EuclideanSpace ℝ (Fin 0))) = 0 := by
    simp [dim]
  exact (GraphWanted.balinski {p} (by simp) (hd := hd)).1

/-- A triangle in three-dimensional space stays connected after deleting any one vertex. -/
example :
    let p := EuclideanSpace.basisFun (Fin 3) ℝ
    let s := Finset.univ.image p
    ∀ S : Finset ((convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))).extremePoints ℝ),
      S.card = 1 → ((graph s).induce (S : Set _)ᶜ).Connected := by
  classical
  intro p s S hS
  have hs : s.Nonempty := Finset.univ_nonempty.image p
  have hd : dim s = 2 := by
    have hrange : (s : Set (EuclideanSpace ℝ (Fin 3))) = Set.range p := by simp [s]
    have hi : AffineIndependent ℝ p := p.toBasis.linearIndependent.affineIndependent
    rw [dim, affineSpan_convexHull, direction_affineSpan, hrange]
    exact hi.finrank_vectorSpan (by decide)
  exact (GraphWanted.balinski s hs (hd := hd)).2 S (by simp [hS])

end MathlibExtTest.Geometry.Polytope.Balinski
