/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanVerticalHomologyFaces
public import MathlibExt.Algebra.Homology.VerticalHomologyComplex

/-!
# The horizontal complex of Bousfield--Kan vertical homology

Fixing a vertical degree in the Bousfield--Kan alternating bicomplex gives a
horizontal complex of vertical homology objects.  The exact-coproduct and
face-compatibility results identify this complex with the alternating-face
complex of the weighted bar on the coefficient-homology diagram.

The terminal-weight comparison and horizontal homology are supplied by
`BousfieldKanVerticalCoefficientBar`, and the resulting second page is
packaged in `BousfieldKanSpectralSequence`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite
open scoped Simplicial

universe w v

namespace SSet

variable {J : Type w} [Category.{v} J]

/-- Alternating weighted-bar complex on the degree-`q` homology diagram. -/
noncomputable def wbarVerticalHomologyComplex
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v}) (q : ℕ) :
    ChainComplex AddCommGrpCat.{max w v} ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex
    AddCommGrpCat.{max w v}).obj
      (StrictOrdinaryWeightedBar.wbarSimplicial
        (CategoryBar.replUnit J)
        (D ⋙ SSet.homologyFunctor R q))

/-- The horizontal differential on the vertical-homology complex is the
alternating sum of homology maps induced by the outer weighted-bar faces. -/
theorem bkVerticalHomologyComplex_d_eq_sum
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v})
    (n q : ℕ) :
    ((bkAlternatingBicomplex
      AddCommGrpCat.{max w v} R D).verticalHomologyComplex q).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        SSet.homologyMap
          (StrictOrdinaryWeightedBar.wbarδ
            (CategoryBar.replUnit J) D n i) R q := by
  rw [HomologicalComplex₂.verticalHomologyComplex_d]
  change HomologicalComplex.homologyMap
      ((AlgebraicTopology.bisimplicialAlternatingBicomplex
        AddCommGrpCat.{max w v}
        ((bisimplicialLinearizationFunctor AddCommGrpCat.{max w v} R).obj
          (bkBarBisimplicial D))).d (n + 1) n) q = _
  rw [AlgebraicTopology.bisimplicialAlternatingBicomplex_horizontal_d_eq_sum]
  change (HomologicalComplex.homologyFunctor AddCommGrpCat.{max w v}
      (ComplexShape.down ℕ) q).map
        (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (AlgebraicTopology.alternatingFaceMapComplex
            AddCommGrpCat.{max w v}).map
              (((bisimplicialLinearizationFunctor AddCommGrpCat.{max w v} R).obj
                (bkBarBisimplicial D)).δ i)) = _
  rw [Functor.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Functor.map_zsmul]
  congr 1
  change SSet.homologyMap ((bkBarBisimplicial D).δ i) R q =
    SSet.homologyMap
      (StrictOrdinaryWeightedBar.wbarδ
        (CategoryBar.replUnit J) D n i) R q
  have hδ : (bkBarBisimplicial D).δ i =
      StrictOrdinaryWeightedBar.wbarδ
        (CategoryBar.replUnit J) D n i :=
    StrictOrdinaryWeightedBar.wbarSimplicial_map_δ
      (CategoryBar.replUnit J) D i
  exact congrArg (fun f => SSet.homologyMap f R q) hδ

/-- The differential of the target weighted-bar complex is its alternating
sum of outer faces. -/
theorem wbarVerticalHomologyComplex_d_eq_sum
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v})
    (n q : ℕ) :
    (wbarVerticalHomologyComplex R D q).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        StrictOrdinaryWeightedBar.wbarδ
          (CategoryBar.replUnit J)
          (D ⋙ SSet.homologyFunctor R q) n i := by
  change ((AlgebraicTopology.alternatingFaceMapComplex
    AddCommGrpCat.{max w v}).obj
      (StrictOrdinaryWeightedBar.wbarSimplicial
        (CategoryBar.replUnit J)
        (D ⋙ SSet.homologyFunctor R q))).d (n + 1) n = _
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  unfold AlgebraicTopology.AlternatingFaceMapComplex.objD
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact StrictOrdinaryWeightedBar.wbarSimplicial_map_δ
    (CategoryBar.replUnit J)
    (D ⋙ SSet.homologyFunctor R q) i

/-- The horizontal complex of vertical homology is the alternating weighted
bar on the coefficient-homology diagram. -/
noncomputable def bkVerticalHomologyComplexIso
    (R : AddCommGrpCat.{max w v}) (D : J ⥤ SSet.{max w v}) (q : ℕ) :
    (bkAlternatingBicomplex
      AddCommGrpCat.{max w v} R D).verticalHomologyComplex q ≅
      wbarVerticalHomologyComplex R D q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => bkAlternatingVerticalHomologyIso R D p q) (by
      intro i j hij
      obtain rfl : i = j + 1 := hij.symm
      change (wbarVerticalHomologyIso R D (j + 1) q).hom ≫
          (wbarVerticalHomologyComplex R D q).d (j + 1) j =
        ((bkAlternatingBicomplex AddCommGrpCat.{max w v} R D).verticalHomologyComplex q).d
            (j + 1) j ≫
          (wbarVerticalHomologyIso R D j q).hom
      rw [wbarVerticalHomologyComplex_d_eq_sum,
        bkVerticalHomologyComplex_d_eq_sum]
      simp only [Preadditive.comp_sum, Preadditive.sum_comp,
        Preadditive.comp_zsmul, Preadditive.zsmul_comp]
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg ((-1 : ℤ) ^ (k : ℕ) • ·)
        (wbarVerticalHomologyIso_face R D j q k).symm)

end SSet

end
