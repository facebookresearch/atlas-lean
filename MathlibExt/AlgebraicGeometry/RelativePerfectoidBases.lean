/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PerfectoidDiamondModels
public import MathlibExt.AlgebraicGeometry.LocalWittCoefficientFields
public import MathlibExt.AlgebraicGeometry.RelativeFarguesFontaineRings
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Actual global perfectoid bases over the local field's residue field

The space is the existing actual v-sheaf/open-atlas perfectoid model.
Its residue-field structure is a ring map into every original plus
ring, natural on every actual affine-valued point. Morphisms preserve
those actual scalar maps. Covers retain joint epimorphy of the actual
underlying v-sheaf maps.

The chosen atlas has a small index so its ringed realization is in the
same universe as the imported analytic models. This is a size bound,
with no affineness or noetherianity restriction on the global base.
Source: Fargues--Scholze, arXiv:2102.13459v4, Sections I.2 and II.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativePerfectoidBases

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open AffinePerfectoidVSite PerfectoidDiamondModels LocalWittCoefficientFields
open RelativeFarguesFontaineRings

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E)

/-- Every original bounded affine map has its actual plus-ring homomorphism. -/
def plusMap {P Q : Affine p} (f : P ⟶ Q) : Q.plus →+* P.plus where
  toFun a := ⟨f.hom a.val, f.plus a.val a.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' _a _b := Subtype.ext (map_add _ _ _)
  map_mul' _a _b := Subtype.ext (map_mul _ _ _)

@[nolint unusedArguments]
structure Space (_C : CoefficientData p E) where
  perfectoid : PerfectoidSpace p
  [small_atlas : Small.{0} perfectoid.atlas.index]
  coefficients : ∀ (P : Affine p) (_x : perfectoid.sheaf.obj.obj (op P)),
    Residue p E →+* P.plus
  natural : ∀ {P Q : Affine p} (f : P ⟶ Q) (x : perfectoid.sheaf.obj.obj (op Q)),
    coefficients P (perfectoid.sheaf.obj.map f.op x) = (plusMap p f).comp (coefficients Q x)

def Hom (X Y : Space p C) :=
  {f : X.perfectoid ⟶ Y.perfectoid // ∀ (P : Affine p)
    (x : X.perfectoid.sheaf.obj.obj (op P)),
    Y.coefficients P (f.hom.app (op P) x) = X.coefficients P x}

instance : Category (Space p C) where
  Hom := Hom p C
  id X := ⟨𝟙 X.perfectoid, by intros; rfl⟩
  comp {X Y Z} f g := ⟨f.val ≫ g.val, by
    intro P x
    change Z.coefficients P (g.val.hom.app (op P) (f.val.hom.app (op P) x)) = X.coefficients P x
    rw [g.property, f.property]⟩
  id_comp f := Subtype.ext (Category.id_comp _)
  comp_id f := Subtype.ext (Category.comp_id _)
  assoc f g h := Subtype.ext (Category.assoc _ _ _)

/-- The actual geometric projection remembers every original v-sheaf map. -/
def forget : Space p C ⥤ VSheaf p where
  obj X := X.perfectoid.sheaf
  map f := f.val

/-- The global residue-linear Perf v-topology uses actual joint epimorphy. -/
def topology : GrothendieckTopology (Space p C) :=
  sInf {J | ∀ (I : Type 1) (T : Space p C) (U : I → Space p C) (f : ∀ i, U i ⟶ T),
    JointlyEpi p (fun i ↦ (U i).perfectoid.sheaf) (fun i ↦ (f i).val) →
      Sieve.ofArrows U f ∈ J T}

/-- The point is the literal native sheafification unit of the original affine morphism. -/
def affinePoint {P Q : Affine p} (f : P ⟶ Q) : (affineSheaf p Q).obj.obj (op P) :=
  (toSheafify (AffinePerfectoidVSite.topology p) (yoneda.obj Q ⋙ liftTypes)).app (op P) (ULift.up f)

/-- An affine relative base retains exactly its actual sheaf and every original scalar point. -/
structure AffineModel (S : Base p C) where
  space : Space p C
  comparison : affineSheaf p S.pair ≅ space.perfectoid.sheaf
  normalized : ∀ (P : Affine p) (f : P ⟶ S.pair),
    space.coefficients P (comparison.hom.hom.app (op P) (affinePoint p f)) =
      (plusMap p f).comp (algebraMap (Residue p E) S.pair.plus)

/-- The existing actual open atlas is labelled by residue-linear affine bases. -/
structure LabelledAtlas (S : Space p C) where
  base : S.perfectoid.atlas.index → Base p C
  pair : ∀ i, (base i).pair ≅ S.perfectoid.atlas.affine i
  normalized : ∀ i (P : Affine p) (f : P ⟶ (base i).pair),
    S.coefficients P
      ((affineMap p (pair i).hom ≫ S.perfectoid.atlas.chart i).hom.app (op P)
        (affinePoint p f)) =
      (plusMap p f).comp (algebraMap (Residue p E) (base i).pair.plus)

def LabelledAtlas.chart {S : Space p C} (A : LabelledAtlas p C S) (i : S.perfectoid.atlas.index) :
    affineSheaf p (A.base i).pair ⟶ S.perfectoid.sheaf :=
  affineMap p (A.pair i).hom ≫ S.perfectoid.atlas.chart i

end MathlibExt.AlgebraicGeometry.RelativePerfectoidBases
