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
# Realization of standard simplices

For a finite ordinal `n : SimplexCategory`, the realization of `stdSimplex.obj n` is canonically isomorphic in `TopCat` to the real standard simplex `StdSimplex ℝ (Fin (n.len + 1))`. For every ordinal map `f : n ⟶ m`, these isomorphisms satisfy
`SSet.toTop.map (stdSimplex.map f) ≫ (toTopIso m).hom = (toTopIso n).hom ≫ toTopMap f`,
where `toTopMap f` is the induced map on barycentric coordinates. The inverse image of the complement of the barycenter under `toTopIso n` is open in the realization.
-/

@[expose] public section

open CategoryTheory Simplicial Convexity

namespace SSet.stdSimplex

/-- For `n : SimplexCategory`, the canonical isomorphism in `TopCat` from `SSet.toTop.obj
(stdSimplex.obj n)` to `TopCat.of (StdSimplex ℝ (Fin (n.len + 1)))`, induced by the
homeomorphism `n.toTopHomeo` between the realization and the real standard simplex. -/
noncomputable def toTopIso (n : SimplexCategory) :
    SSet.toTop.obj (SSet.stdSimplex.obj n) ≅
      TopCat.of (StdSimplex ℝ (Fin (n.len + 1))) :=
  TopCat.isoOfHomeo n.toTopHomeo

/-- For an ordinal map `f : n ⟶ m` in `SimplexCategory`, the continuous map from `StdSimplex ℝ
(Fin (n.len + 1))` to `StdSimplex ℝ (Fin (m.len + 1))` induced by `StdSimplex.map f` on
barycentric coordinates. As a morphism in `TopCat`, it is `SimplexCategory.toTop₀.map f`. -/
noncomputable def toTopMap {n m : SimplexCategory} (f : n ⟶ m) :
    TopCat.of (StdSimplex ℝ (Fin (n.len + 1))) ⟶
      TopCat.of (StdSimplex ℝ (Fin (m.len + 1))) :=
  SimplexCategory.toTop₀.map f

/-- For `n, m : SimplexCategory` and `f : n ⟶ m`, the canonical realization isomorphisms commute with the induced simplex maps:
`SSet.toTop.map (stdSimplex.map f) ≫ (toTopIso m).hom = (toTopIso n).hom ≫ toTopMap f`.
Both sides are morphisms from the realization of `stdSimplex.obj n` to the real standard simplex on `Fin (m.len + 1)`. -/
@[reassoc]
theorem toTopIso_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    SSet.toTop.map (SSet.stdSimplex.map f) ≫ (toTopIso m).hom =
      (toTopIso n).hom ≫ toTopMap f := by
  apply TopCat.ext
  intro x
  change m.toTopHomeo ((SSet.toTop.map (SSet.stdSimplex.map f)) x) =
    StdSimplex.map f (n.toTopHomeo x)
  exact SimplexCategory.toTopHomeo_naturality_apply f x

/-- For `n : SimplexCategory`, the subset `(toTopIso n).hom ⁻¹'
{Convexity.StdSimplex.barycenter}ᶜ` is open in the realization of `stdSimplex.obj n`, where
the barycenter lies in `StdSimplex ℝ (Fin (n.len + 1))`. -/
theorem toTopIso_barycenterCompl_preimage_isOpen (n : SimplexCategory) :
    IsOpen ((toTopIso n).hom ⁻¹'
      {(Convexity.StdSimplex.barycenter :
        Convexity.StdSimplex ℝ (Fin (n.len + 1)))}ᶜ) := by
  have : T2Space (Convexity.StdSimplex ℝ (Fin (n.len + 1))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n.len + 1))).t2Space
  exact isOpen_compl_singleton.preimage (toTopIso n).hom.hom.continuous

end SSet.stdSimplex

end
