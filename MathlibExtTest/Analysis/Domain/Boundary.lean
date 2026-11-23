/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Babak Modami
-/
module

public import MathlibExt.Analysis.Domain.Boundary

@[expose] public section

open Metric Set

namespace MathlibExtTest.Analysis.Domain.Boundary

open MetaMathlibExt

-- Analysis 501: C2 boundary

/- empty frontier (boundary) => C^2 boundary-/

lemma hasC2Boundary_of_frontier_empty {Ω : Set (EuclideanSpace ℝ (Fin 2))}
  (hO : IsOpen Ω) (hF : frontier Ω = ∅) : HasC2Boundary Ω :=
⟨hO, fun x hx => by rw [hF] at hx; exact hx.elim⟩

/- R^2 = univ has C^2 boundary -/

lemma hasC2Boundary_univ : HasC2Boundary (univ : Set (EuclideanSpace ℝ (Fin 2))) :=
  hasC2Boundary_of_frontier_empty isOpen_univ frontier_univ

-- Analysis 506: Lipschitz boundary

/-empty frontier => Lipschitz boundary-/

lemma hasLipschitzBoundary_of_frontier_empty {Ω : Set (EuclideanSpace ℝ (Fin 2))}
  (hO : IsOpen Ω) (hF : frontier Ω = ∅) : HasLipschitzBoundary Ω :=
⟨hO, fun x hx => by rw [hF] at hx; exact hx.elim⟩

/-  R^2 = univ has Lipschitz boundary-/

lemma hasLipschitzBoundary_univ : HasLipschitzBoundary (univ : Set (EuclideanSpace ℝ (Fin 2))) :=
  hasLipschitzBoundary_of_frontier_empty isOpen_univ frontier_univ

end MathlibExtTest.Analysis.Domain.Boundary

end
