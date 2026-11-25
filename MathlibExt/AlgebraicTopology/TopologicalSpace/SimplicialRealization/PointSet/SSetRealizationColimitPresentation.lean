/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPresentation

/-!
# Colimit presentation of the sigma-presentation kernel

Provenance: exact base `d322f03869943eb85adc0ea42728913a77d722a5`; implements
run `kq3root-c-p7923-colimit-presentation-bridge` from the `s7905`/`s7910`
read-only proof maps on the same base. This file is the run's only new Lean
file; no root, ref, or other file is touched.

What is proved: for `X : SSet.{u}`, equality of two `SSet.sigmaToTop X`
presentations implies the corresponding `Relation.EqvGen` relation for the
realized tautological diagram
`CostructuredArrow.proj uliftYoneda X ⋙ uliftYoneda ⋙ SSet.toTop ⋙ forget TopCat`.

Reuse map (every capability is `reuse`; no new abstraction is introduced):
- tautological cocone and its colimit: `Presheaf.tautologicalCocone'` and
  `Presheaf.isColimitTautologicalCocone'` (prime version, as in
  `SSet.exists_nonDegenerate_toTop_presentation`), transported by
  `isColimitOfPreserves` through `SSet.toTop` and then `forget TopCat`;
- element objects: `CostructuredArrow.mk` applied to `SSet.yonedaEquiv.symm`
  (which is `uliftYonedaEquiv`, matching the prime diagram, since
  `SSet.stdSimplex` is `uliftYoneda` by definition);
- element points: `(SimplexCategory.toTopHomeo _).symm`;
- cocone-point identification: `Limits.IsColimit.coconePointUniqueUpToIso`
  with `Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`;
- kernel extraction: `Limits.Types.colimit_eq`.

Explicit nonclaims: no induction over the generated relation, no simplex
epi/mono argument, no open-cell injectivity or compact-support argument, and
no change to any generated root or import graph.
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
  let c : Cocone (CostructuredArrow.proj CategoryTheory.uliftYoneda X ⋙
      CategoryTheory.uliftYoneda) := { pt := X, ι := { app j := j.hom } }
  have hc : IsColimit c := denseAtUliftYoneda X
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
