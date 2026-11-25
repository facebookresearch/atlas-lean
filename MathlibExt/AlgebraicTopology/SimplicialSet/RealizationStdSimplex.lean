/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Analysis.Convex.StdSimplex

/-!
# Realization of a standard simplex

This module packages `SimplexCategory.toTopHomeo` as the canonical `TopCat`
isomorphism between the simplicial realization of `Δ[n]` and the topological
standard simplex `StdSimplex ℝ (Fin (n.len + 1))`. It also provides the
categorical naturality bridge for the `TopCat` isomorphism:

* `SSet.stdSimplex.toTopMap` – the `TopCat` morphism
  `TopCat.of (StdSimplex ℝ (Fin (n.len + 1))) ⟶ TopCat.of (StdSimplex ℝ (Fin (m.len + 1)))`
  induced by `StdSimplex.map f`;
* `SSet.stdSimplex.toTopIso_naturality` – the equality
  `SSet.toTop.map (SSet.stdSimplex.map f) ≫ (toTopIso m).hom`
  equals
  `(toTopIso n).hom ≫ toTopMap f`,
  derived directly from `SimplexCategory.toTopHomeo_naturality` via
  concrete (`TopCat.ext`) extensionality.

No product, prism, filtration, DeltaGenerated, weak-equivalence, or
model-category result is proved here.

-/

@[expose] public section

open CategoryTheory Simplicial Convexity

namespace SSet.stdSimplex

/-- The realization of `Δ[n]` is canonically isomorphic to the topological
standard `n`-simplex. -/
noncomputable def toTopIso (n : SimplexCategory) :
    SSet.toTop.obj (SSet.stdSimplex.obj n) ≅
      TopCat.of (StdSimplex ℝ (Fin (n.len + 1))) :=
  TopCat.isoOfHomeo n.toTopHomeo

/-- The `TopCat` morphism between topological standard simplices induced by
`StdSimplex.map f`. This is `SimplexCategory.toTop₀.map f`. -/
noncomputable def toTopMap {n m : SimplexCategory} (f : n ⟶ m) :
    TopCat.of (StdSimplex ℝ (Fin (n.len + 1))) ⟶
      TopCat.of (StdSimplex ℝ (Fin (m.len + 1))) :=
  SimplexCategory.toTop₀.map f

/-- Naturality of `toTopIso` with respect to `f : n ⟶ m`:

`SSet.toTop.map (SSet.stdSimplex.map f)` followed by `toTopIso m`
equals `toTopIso n` followed by the induced topological simplex map
`StdSimplex.map f` (packaged as `toTopMap f`).

This is the categorical form of `SimplexCategory.toTopHomeo_naturality`,
proved by concrete extensionality in `TopCat`. -/
@[reassoc]
theorem toTopIso_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    SSet.toTop.map (SSet.stdSimplex.map f) ≫ (toTopIso m).hom =
      (toTopIso n).hom ≫ toTopMap f := by
  apply TopCat.ext
  intro x
  change m.toTopHomeo ((SSet.toTop.map (SSet.stdSimplex.map f)) x) =
    StdSimplex.map f (n.toTopHomeo x)
  exact SimplexCategory.toTopHomeo_naturality_apply f x

/-- The preimage of the barycenter-complement under `toTopIso` is open. -/
theorem toTopIso_barycenterCompl_preimage_isOpen (n : SimplexCategory) :
    IsOpen ((toTopIso n).hom ⁻¹'
      {(Convexity.StdSimplex.barycenter :
        Convexity.StdSimplex ℝ (Fin (n.len + 1)))}ᶜ) := by
  have : T2Space (Convexity.StdSimplex ℝ (Fin (n.len + 1))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n.len + 1))).t2Space
  exact isOpen_compl_singleton.preimage (toTopIso n).hom.hom.continuous

end SSet.stdSimplex

end
