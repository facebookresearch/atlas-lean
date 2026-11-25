/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PDivisiblePointFunctors
public import MathlibExt.AlgebraicGeometry.GeometricPDCrystallineSheaves

/-!
# Actual p-divisible tower maps and crystalline coefficient maps

A map is a natural transformation of the original scheme levels,
with its original group-map property. Its point map is the native
filtered colimit of postcomposition on every scheme test. Its
crystalline coefficient map is actual restriction and sheafification
of that same group map. No point map is selected independently.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDivisibleGroupMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open PDivisibleGroupSchemes PDivisiblePointFunctors
open GeometricPDCrystallineTests GeometricPDCrystallineSheaves
open scoped CategoryTheory.MonObj

variable (p : ℕ) [Fact p.Prime] {S : Scheme.{0}}

/-- A map retains all original finite scheme/group maps. -/
structure Hom (G H : PDivisibleGroup S p) where
  levels : G.levels ⟶ H.levels
  group : ∀ n : ℕ, IsMonHom (levels.app n)

variable {p} {G H : PDivisibleGroup S p} (f : Hom p G H)

attribute [local instance] Hom.group

/-- Every finite-level point map is literal postcomposition by the source scheme map. -/
def levelPointMap (n : ℕ) : levelPoints (p := p) (S := S) G n ⟶
    levelPoints (p := p) (S := S) H n where
  app T := CommGrpCat.ofHom {
    toFun x := x ≫ f.levels.app n
    map_one' := MonObj.one_comp _
    map_mul' x y := MonObj.mul_comp x y _ }
  naturality {T U} a := by
    ext x
    change T.unop ⟶ G.levels.obj n at x
    change (a.unop ≫ x) ≫ f.levels.app n = a.unop ≫ (x ≫ f.levels.app n)
    exact Category.assoc a.unop x (f.levels.app n)

/-- The natural transformation uses precisely the original scheme tower naturality. -/
def pointTowerMap : pointTower (p := p) (S := S) G ⟶ pointTower (p := p) (S := S) H where
  app := levelPointMap f
  naturality {n m} a := by
    apply NatTrans.ext
    funext T
    ext x
    change T.unop ⟶ G.levels.obj n at x
    change (x ≫ G.levels.map a) ≫ f.levels.app m =
      (x ≫ f.levels.app n) ≫ H.levels.map a
    exact (Category.assoc x (G.levels.map a) (f.levels.app m)).trans
      ((congrArg (fun k => x ≫ k) (f.levels.naturality a)).trans
        (Category.assoc x (f.levels.app n) (H.levels.map a)).symm)

/-- The original filtered group-colimit map, before any coefficient realization. -/
def pointMap : pointwisePoints (p := p) (S := S) G ⟶ pointwisePoints (p := p) (S := S) H :=
  colim.map (pointTowerMap f)

/-- The actual point map preserves each original finite inclusion. -/
theorem pointMap_finite (n : ℕ) :
    levelInclusion (p := p) (S := S) G n ≫ pointMap f =
      levelPointMap f n ≫ levelInclusion (p := p) (S := S) H n :=
  colimit.ι_map (pointTowerMap f) n

variable (A : PDBase) (X : Over A.reduction) {G H : PDivisibleGroup X.left p}
  (f : Hom p G H)

/-- All reduction-point coefficient maps retain the original PD site and source group map. -/
def crystallinePresheafMap : groupPresheaf p A X G ⟶ groupPresheaf p A X H :=
  Functor.whiskerLeft (reductions p A X).op
    (Functor.whiskerRight (pointMap f) (CommGrpCat.toAddCommGrp ⋙ liftAbelianGroups))

/-- The sheaf map is actual sheafification of the original coefficient map. -/
def crystallineSheafMap : groupSheaf p A X G ⟶ groupSheaf p A X H :=
  (presheafToSheaf (topology p A X) AddCommGrpCat.{1}).map (crystallinePresheafMap A X f)

end MathlibExt.AlgebraicGeometry.PDivisibleGroupMaps
