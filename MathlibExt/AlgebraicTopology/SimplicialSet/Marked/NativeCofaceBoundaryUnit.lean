/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBoundaryRootSourceMap
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeChartRestrictionPostSection

/-!
# Original boundary cofaces read the same genuine native unit

Each unchanged boundary coface chart map is the actual straightening
of its full original marked slice coface. Its native Hom readback is
that same coface followed by the original boundary's actual unit.
The original pullback adjunction reads the whole coherent simplex map.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The unchanged original single-face simplex over the base enters the full actual minimally marked boundary by its
same single-face slice isomorphism and original boundary face injection. -/
def nativeCofaceBoundaryBasisMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) (j : Fin (n + 2)) :
    nativeSimplexBasis B n (B.map (SimplexCategory.δ j).op σ) ⟶
      nativeSubcomplexBasis B (n + 1) σ (boundary (n + 1)) :=
  (nativeSingleFaceBasisIso B n j σ).hom ≫
    (nativeSubcomplexBasisFunctor B (n + 1) σ).map ((nativeBoundaryFaceSubcomplexDiagram n).multicofork.π j)

/-- The actual original boundary coface basis retains exactly its original whole simplex restriction when followed
by the unchanged boundary inclusion. -/
theorem nativeCofaceBoundaryBasisMap_attachment (B : SSet.{u}) (n : ℕ)
    (σ : B _⦋n + 1⦌) (j : Fin (n + 2)) :
    nativeCofaceBoundaryBasisMap B n σ j ≫ nativeSubcomplexInclusion B (n + 1) σ (boundary (n + 1)) =
      nativeSimplexRestriction B (SimplexCategory.δ j) σ := by
  let X := nativeSubcomplexBasisFunctor B (n + 1) σ
  let d := nativeBoundaryFaceSubcomplexDiagram.{u} n
  let e := nativeSingleFaceBasisIso B n j σ
  let g := nativeSubcomplexInclusion B (n + 1) σ (boundary (n + 1))
  have hx : X.map (d.multicofork.π j) ≫ g =
      nativeSubcomplexInclusion B (n + 1) σ (SSet.stdSimplex.face {j}ᶜ) := by
    apply Over.OverMorphism.ext
    apply Hom.ext
    rfl
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => e.hom ≫ a) hx).trans (nativeSingleFaceBasisIso_inclusion B n j σ))

/-- The same full original native boundary coface chart is the actual straightened coface basis map under its
unchanged original simplex image isomorphism. -/
theorem nativeBoundaryCofaceChartMap_mapped (B : SSet.{u}) (n : ℕ)
    (σ : B _⦋n + 1⦌) (j : Fin (n + 2)) :
    (nativeSimplexImageIso B n (B.map (SimplexCategory.δ j).op σ)).hom ≫ nativeBoundaryCofaceChartMap B n σ j =
      (nativeStraightening B).map (nativeCofaceBoundaryBasisMap B n σ j) := by
  let e := nativeSimplexImageIso B n (B.map (SimplexCategory.δ j).op σ)
  let a := (nativeSingleFaceBasisIso B n j σ).hom
  let b := (nativeSubcomplexBasisFunctor B (n + 1) σ).map ((nativeBoundaryFaceSubcomplexDiagram n).multicofork.π j)
  let T := nativeStraightening B
  change e.hom ≫ ((e.inv ≫ T.map a) ≫ T.map b) = T.map (a ≫ b)
  exact (congrArg (fun z => e.hom ≫ z) (Category.assoc _ _ _)).trans
    ((e.hom_inv_id_assoc (T.map a ≫ T.map b)).trans (T.map_comp a b).symm)

/-- Every original boundary coface's native chart Hom is precisely its original full marked slice map followed by
the actual boundary straightening unit. -/
theorem nativeBoundaryCofaceChartMap_hom_unit (B : SSet.{u}) (n : ℕ)
    (σ : B _⦋n + 1⦌) (j : Fin (n + 2)) :
    nativeSimplexChartHomEquiv B n (B.map (SimplexCategory.δ j).op σ)
      (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))) (nativeBoundaryCofaceChartMap B n σ j) =
      nativeCofaceBoundaryBasisMap B n σ j ≫
        (nativeStraighteningAdjunction B).unit.app (nativeSubcomplexBasis B (n + 1) σ (boundary (n + 1))) := by
  let A := nativeStraighteningAdjunction B
  let K := nativeSubcomplexBasis B (n + 1) σ (boundary (n + 1))
  let F := nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))
  let a := nativeCofaceBoundaryBasisMap B n σ j
  have hn := A.homEquiv_naturality_left a (𝟙 F)
  have ha : A.homEquiv _ F ((nativeStraightening B).map a) = a ≫ A.unit.app K :=
    (congrArg (A.homEquiv _ F) (Category.comp_id _)).symm.trans
      (hn.trans (congrArg (fun g => a ≫ g) (A.homEquiv_id K)))
  exact (nativeSimplexImageIso_post_homEquiv B n (B.map (SimplexCategory.δ j).op σ) F _).symm.trans
    ((congrArg (A.homEquiv _ F) (nativeBoundaryCofaceChartMap_mapped B n σ j)).trans ha)

/-- The original boundary's genuine native straightening unit, read through the actual coherent-base pullback
adjunction, retains its whole original minimally marked boundary source. -/
def nativeBoundaryUnitCoherentMap (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) :
    (Over.map (maximal.map (unit B))).obj (nativeSubcomplexBasis B n σ (boundary n)) ⟶
      (coherentUnstraighteningFunctor (realization B)).obj (nativeSubcomplexChart B n σ (boundary n)) :=
  ((Over.mapPullbackAdj (maximal.map (unit B))).homEquiv
    (nativeSubcomplexBasis B n σ (boundary n))
    ((coherentUnstraighteningFunctor (realization B)).obj (nativeSubcomplexChart B n σ (boundary n)))).symm
      ((nativeStraighteningAdjunction B).unit.app (nativeSubcomplexBasis B n σ (boundary n)))

/-- The whole original native boundary coface section is exactly the original boundary unit simplex on that same
coface. -/
theorem nativeBoundaryCofaceUnit_raw (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) (j : Fin (n + 2)) :
    (nativeSimplexUnHomEquiv B n (B.map (SimplexCategory.δ j).op σ)
      (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))
      (nativeSimplexChartHomEquiv B n (B.map (SimplexCategory.δ j).op σ)
        (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))) (nativeBoundaryCofaceChartMap B n σ j))).val =
      SSet.yonedaEquiv ((nativeCofaceBoundaryBasisMap B n σ j).left.hom ≫
        (nativeBoundaryUnitCoherentMap B (n + 1) σ).left.hom) := by
  let F := nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))
  let a := nativeCofaceBoundaryBasisMap B n σ j
  let β := (nativeStraighteningAdjunction B).unit.app (nativeSubcomplexBasis B (n + 1) σ (boundary (n + 1)))
  let P := Over.mapPullbackAdj (maximal.map (unit B))
  have hp := P.homEquiv_naturality_left_symm a β
  exact (congrArg (fun g => (nativeSimplexUnHomEquiv B n (B.map (SimplexCategory.δ j).op σ) F g).val)
      (nativeBoundaryCofaceChartMap_hom_unit B n σ j)).trans
    ((nativeSimplexUnHomEquiv_val B n (B.map (SimplexCategory.δ j).op σ) F (a ≫ β)).trans
      (congrArg (fun g => SSet.yonedaEquiv g.left.hom) hp))

/-- All original scalar operators read the same whole coherent boundary-unit map on the full original restricted
coface. -/
theorem nativeBoundaryCofaceUnit_pull_raw (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌)
    (j : Fin (n + 2)) {r : ℕ} (f : ⦋r⦌ ⟶ ⦋n⦌) :
    ((nativeSimplexUnHomEquiv B n (B.map (SimplexCategory.δ j).op σ)
      (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))
      (nativeSimplexChartHomEquiv B n (B.map (SimplexCategory.δ j).op σ)
        (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))) (nativeBoundaryCofaceChartMap B n σ j))).val).pull
        f.toOrderHom.uliftMap =
      SSet.yonedaEquiv (SSet.stdSimplex.map f ≫ (nativeCofaceBoundaryBasisMap B n σ j).left.hom ≫
        (nativeBoundaryUnitCoherentMap B (n + 1) σ).left.hom) := by
  let F := nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))
  let g := (nativeCofaceBoundaryBasisMap B n σ j).left.hom ≫ (nativeBoundaryUnitCoherentMap B (n + 1) σ).left.hom
  exact (congrArg (fun a : UnstraighteningSimplex F n => a.pull f.toOrderHom.uliftMap)
    (nativeBoundaryCofaceUnit_raw B n σ j)).trans (SSet.yonedaEquiv_naturality f g)

end SSet.Marked
