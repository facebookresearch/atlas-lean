/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeFarguesFontaineSheaves
public import MathlibExt.AlgebraicGeometry.AffinePerfectoidVSite
public import Mathlib.CategoryTheory.Sites.InducedTopology

/-!
# Actual residue-linear relative FF base and orbit maps

Base morphisms are original bounded perfectoid maps linear over the
actual residue field. Uniformizers of the perfectoid bases need not be
preserved. The coefficient map is the actual relative Witt tensor map
on the original plus rings, and its orbit map is the native coequalizer
descent of the corresponding all-rank valuation map.

The whole source site is obtained from the actual perfectoid v-cover
topology by its real projection. This retains relative-base indexing
and never substitutes base change of one absolute curve.

Source: Fargues--Scholze, arXiv:2102.13459v4, Sections I.2 and II.1.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.RelativeFarguesFontaineMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open RelativeFarguesFontaineRings RelativeFarguesFontaineSheaves
open LocalWittCoefficientFields

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E)

/-- Actual bounded geometric maps retain every original residue coefficient. -/
def BaseHom (S T : Base p C) :=
  {f : S.pair ⟶ T.pair // ∀ a : Residue p E,
    f.hom ((algebraMap (Residue p E) T.pair.plus a) : T.pair.ring) =
      ((algebraMap (Residue p E) S.pair.plus a) : S.pair.ring)}

instance : Category (Base p C) where
  Hom := BaseHom p C
  id S := ⟨𝟙 S.pair, by intros; rfl⟩
  comp f g := ⟨f.val ≫ g.val, by
    intro a
    change f.val.hom (g.val.hom _) = _
    rw [g.property, f.property]⟩
  id_comp f := Subtype.ext (Category.id_comp _)
  comp_id f := Subtype.ext (Category.comp_id _)
  assoc f g h := Subtype.ext (Category.assoc _ _ _)

/-- The original projection forgets only the presentation parameter and residue label. -/
def forgetBase : Base p C ⥤ AffinePerfectoidVSite.Affine p where
  obj S := S.pair
  map f := f.val

/-- The actual perfectoid v-cover topology on these relative bases. -/
def baseTopology : GrothendieckTopology (Base p C) :=
  (forgetBase p C).restrictedTopology (AffinePerfectoidVSite.topology p)

/-- The actual scalar-linear map on the original plus rings. -/
def residueMap {S T : Base p C} (f : S ⟶ T) :
    T.pair.plus →ₐ[Residue p E] S.pair.plus where
  toFun a := ⟨f.val.hom a.val, f.val.plus _ a.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' _a _b := Subtype.ext (map_add _ _ _)
  map_mul' _a _b := Subtype.ext (map_mul _ _ _)
  commutes' a := Subtype.ext (f.property a)

/-- The actual algebra morphism on perfect residue tests. -/
def testMap {S T : Base p C} (f : S ⟶ T) :
    residueTest p C T ⟶ residueTest p C S :=
  ObjectProperty.homMk (CommAlgCat.ofHom (residueMap p C f))

/-- The exact coefficient map of relative ramified period rings. -/
def periodMap {S T : Base p C} (f : S ⟶ T) :
    Ring p C T →+* Ring p C S := ramifiedMap p C (testMap p C f)

/-- Source-normalized annular Frobenius data on this actual relative base. -/
structure Source (S : Base p C) where
  [restrictions : RationalRestrictions p C S]
  phi : FrobeniusPoints p C S
  period : PeriodSheaf p C S
  chartFunctor : RationalPresentation p C S ⥤ RationalPresentation p C S
  chartMaps : FrobeniusMapFamily p C S chartFunctor
  [chartLaws : IsFrobeniusCharts p C S phi chartFunctor chartMaps]
  sheafMap : period.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat (frobeniusMap p C S phi)).obj period.sheaf
  [sheafLaw : IsSheafFrobenius p C S phi period chartFunctor chartMaps sheafMap]

variable {S T : Base p C} (A : Source p C S) (B : Source p C T) (f : S ⟶ T)

/-- The all-rank source map is normalized by the actual coefficient map and q-Frobenius. -/
structure PointMap where
  map : ySpace p C S ⟶ ySpace p C T
  normalized : ∀ y : Y p C S, (map y).val.val =
    AffineAdicSpectra.comap (periodMap p C f) y.val.val
  frobenius : frobeniusMap p C S A.phi ≫ map = map ≫ frobeniusMap p C T B.phi

variable (F : PointMap p C A B f)

/-- The actual relative orbit map descends the specified original annular point map. -/
def orbitMap : xSpace p C S A.phi ⟶ xSpace p C T B.phi :=
  coequalizer.desc (F.map ≫ quotient p C T B.phi) (by
    calc
      frobeniusMap p C S A.phi ≫ (F.map ≫ quotient p C T B.phi) =
          (frobeniusMap p C S A.phi ≫ F.map) ≫ quotient p C T B.phi :=
        (Category.assoc _ _ _).symm
      _ = (F.map ≫ frobeniusMap p C T B.phi) ≫ quotient p C T B.phi := by
        rw [F.frobenius]
      _ = F.map ≫ quotient p C T B.phi := by
        rw [Category.assoc, quotient_frobenius]
      _ = 𝟙 _ ≫ (F.map ≫ quotient p C T B.phi) := (Category.id_comp _).symm)

/-- The relative base-change map retains the native quotient-projection equation. -/
theorem quotient_orbitMap :
    quotient p C S A.phi ≫ orbitMap p C A B f F = F.map ≫ quotient p C T B.phi :=
  coequalizer.π_desc _ _

end MathlibExt.AlgebraicGeometry.RelativeFarguesFontaineMaps
