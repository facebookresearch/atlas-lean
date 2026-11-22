/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation

/-!
# The colimit relation on simplex realization presentations

Equal values of `SSet.sigmaToTop X` determine points related by the
equivalence closure of `ColimitTypeRel` for the realized tautological
presheaf diagram. The prime tautological cocone remains colimiting after
realization and passage to underlying types. Identifying its legs with
`sigmaToTop` and applying `Limits.Types.colimit_eq` gives the relation.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopCat
open scoped Simplicial

namespace SSet

namespace realizationColimitPresentation

/-- Realized tautological diagram for a simplicial set: the prime tautological
presheaf diagram realized in `TopCat` and forgotten to `Type u`.
This is the diagram whose colimit cocone has the legs computed by
`SSet.sigmaToTop`. -/
noncomputable abbrev realizedTautologicalDiagram (X : SSet.{u}) :
    CostructuredArrow CategoryTheory.uliftYoneda X ⥤ Type u :=
  (CostructuredArrow.proj CategoryTheory.uliftYoneda X ⋙ CategoryTheory.uliftYoneda) ⋙
    (SSet.toTop.{u} ⋙ forget TopCat.{u})

/-- Element object for a nondegenerate-simplex presentation: the costructured
arrow named by the simplex via `SSet.yonedaEquiv`. -/
noncomputable def sigmaPresentObj (X : SSet.{u}) (s : X.N) :
    CostructuredArrow CategoryTheory.uliftYoneda X :=
  CostructuredArrow.mk (SSet.yonedaEquiv.symm s.simplex)

/-- Element point for a sigma presentation: the standard-simplex point
transported into the realized representable leg. -/
noncomputable def sigmaPresentPoint (X : SSet.{u})
    (p : Σ s : X.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :
    (realizedTautologicalDiagram X).obj (sigmaPresentObj X p.1) :=
  (SimplexCategory.toTopHomeo ⦋p.1.dim⦌).symm p.2

/-- Bridge from sigma-presentation equality to the tautological-colimit
relation: equal `SSet.sigmaToTop X` values give related points in the realized
tautological diagram. The legs of the realized tautological cocone compute to
`SSet.sigmaToTop` by definition, so the equality transports along
`coconePointUniqueUpToIso` to the chosen colimit and `Limits.Types.colimit_eq`
extracts the relation. -/
theorem sigmaToTop_eq_to_eqvGen_colimitTypeRel (X : SSet.{u})
    (p p' : Σ s : X.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1)))
    (h : SSet.sigmaToTop X p = SSet.sigmaToTop X p') :
    Relation.EqvGen (realizedTautologicalDiagram X).ColimitTypeRel
      ⟨sigmaPresentObj X p.1, sigmaPresentPoint X p⟩
      ⟨sigmaPresentObj X p'.1, sigmaPresentPoint X p'⟩ := by
  let c := Presheaf.tautologicalCocone' (C := SimplexCategory) (P := X)
  have hc : IsColimit c := Presheaf.isColimitTautologicalCocone' X
  have hcTop : IsColimit (SSet.toTop.mapCocone c) := isColimitOfPreserves SSet.toTop hc
  have hcType : IsColimit ((SSet.toTop ⋙ forget TopCat).mapCocone c) :=
    isColimitOfPreserves (forget TopCat) hcTop
  have : HasColimit (realizedTautologicalDiagram X) := HasColimit.mk ⟨_, hcType⟩
  have hleg : ∀ q : Σ s : X.N, Convexity.StdSimplex ℝ (Fin (s.dim + 1)),
      ((SSet.toTop ⋙ forget TopCat).mapCocone c).ι.app (sigmaPresentObj X q.1)
        (sigmaPresentPoint X q) = SSet.sigmaToTop X q := by
    rintro ⟨s, z⟩
    rfl
  have h1 : (Limits.IsColimit.coconePointUniqueUpToIso hcType
        (Limits.colimit.isColimit (realizedTautologicalDiagram X))).hom
        (SSet.sigmaToTop X p) =
      Limits.colimit.ι (realizedTautologicalDiagram X) (sigmaPresentObj X p.1)
        (sigmaPresentPoint X p) := by
    rw [← hleg p]
    exact CategoryTheory.ConcreteCategory.congr_hom
      (Limits.IsColimit.comp_coconePointUniqueUpToIso_hom hcType
        (Limits.colimit.isColimit (realizedTautologicalDiagram X))
        (sigmaPresentObj X p.1)) (sigmaPresentPoint X p)
  have h2 : (Limits.IsColimit.coconePointUniqueUpToIso hcType
        (Limits.colimit.isColimit (realizedTautologicalDiagram X))).hom
        (SSet.sigmaToTop X p') =
      Limits.colimit.ι (realizedTautologicalDiagram X) (sigmaPresentObj X p'.1)
        (sigmaPresentPoint X p') := by
    rw [← hleg p']
    exact CategoryTheory.ConcreteCategory.congr_hom
      (Limits.IsColimit.comp_coconePointUniqueUpToIso_hom hcType
        (Limits.colimit.isColimit (realizedTautologicalDiagram X))
        (sigmaPresentObj X p'.1)) (sigmaPresentPoint X p')
  have hcol : Limits.colimit.ι (realizedTautologicalDiagram X)
        (sigmaPresentObj X p.1) (sigmaPresentPoint X p) =
      Limits.colimit.ι (realizedTautologicalDiagram X)
        (sigmaPresentObj X p'.1) (sigmaPresentPoint X p') := by
    rw [← h1, ← h2, h]
  exact Limits.Types.colimit_eq hcol

end realizationColimitPresentation

end SSet
