/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FiniteCartierCharacterModels
public import MathlibExt.AlgebraicGeometry.PDivisibleGeometricTateModels

/-!
# Actual finite duals, tower arrows and finite geometric Cartier dlog

Each dual object is the completed native Cartier dual of the original
finite-flat scheme level. Its forward tower arrow dualizes the original
p-power division; its division arrow dualizes the original inclusion.
The assembled p-divisible tower is a separate normalized construction,
with both sorts of arrows fixed at every pair of levels.

All original scheme tests remain available. The finite dlog below starts
from the original integral scheme point, recovers its actual coordinate
functional through the native spectrum counit, and applies the finite
Cartier character dlog. Nothing differentiates a generic field fibre.

Sources: Tate, p-divisible groups (1967); Scholze--Weinstein,
arXiv:1211.6357v2, Sections 1--3.3. Finite Cartier dualization is a
completed source port; only its geometric tower assembly is deferred.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open PDivisibleGroupSchemes PDivisibleGeometricTateModels
open FiniteCartierCharacterModels
open MathlibExt.FiniteLocallyFreeCommAffineGroupSchemeCat
open scoped _root_.CategoryTheory.MonObj

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
  (G : PDivisibleGroup (Spec (.of R)) p)

/-- The original finite group level in the completed native finite Cartier category. -/
def finiteLevel (n : ℕ) : FiniteLocallyFreeCommAffineGroupSchemeCat (.of R) := by
  refine ⟨⟨Grp.mk (G.levels.obj n), ?_⟩, ?_⟩
  · rw [affineGroupSchemeProperty_iff]
    change IsAffine (G.levels.obj n).left
    exact (HasAffineProperty.iff_of_isAffine (P := @IsFinite)
      (f := (G.levels.obj n).hom)).mp (G.finite n) |>.1
  · rw [finiteLocallyFreeCommAffineGroupSchemeProperty_iff]
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

variable {p R G}

/-- The original finite-group forget functor, retaining the actual scheme in its slice. -/
def finiteForget (R : Type) [CommRing R] :
    FiniteLocallyFreeCommAffineGroupSchemeCat (.of R) ⥤ Over (Spec (.of R)) :=
  (finiteLocallyFreeCommAffineGroupSchemeProperty (.of R)).ι ⋙
    (affineGroupSchemeProperty (.of R)).ι ⋙ Grp.forget (Over (Spec (.of R)))

/-- The original group map, with only the native full-subcategory proofs added. -/
def finiteGroupHom {n m : ℕ} (f : G.levels.obj n ⟶ G.levels.obj m) [IsMonHom f] :
    finiteLevel p R G n ⟶ finiteLevel p R G m :=
  ObjectProperty.homMk (ObjectProperty.homMk (Grp.ofHom f))

/-- The actual original finite-level inclusion. -/
def finiteInclusion (n m : ℕ) (h : n ≤ m) :
    finiteLevel p R G n ⟶ finiteLevel p R G m :=
  finiteGroupHom (G.levels.map (homOfLE h))

/-- The actual original p-power division between any two displayed levels. -/
def divisionBetween (n m : ℕ) (h : n ≤ m) : G.levels.obj m ⟶ G.levels.obj n :=
  G.levels.map (homOfLE (Nat.sub_add_cancel h).symm.le) ≫ G.divide (m - n) n

instance divisionBetween_group (n m : ℕ) (h : n ≤ m) :
    IsMonHom (divisionBetween (G := G) n m h) := by
  dsimp [divisionBetween]
  infer_instance

/-- The same division map in the original finite group category. -/
def finiteDivisionBetween (n m : ℕ) (h : n ≤ m) :
    finiteLevel p R G m ⟶ finiteLevel p R G n :=
  finiteGroupHom (divisionBetween (G := G) n m h)

/-- Division in the source n+m to m formulation, retaining that exact source arrow. -/
def finiteDivision (n m : ℕ) :
    finiteLevel p R G (n + m) ⟶ finiteLevel p R G m :=
  finiteGroupHom (G.divide n m)

variable (p R G)

/-- The actual completed finite Cartier dual of this exact scheme level. -/
abbrev dualLevel (n : ℕ) := cartierDual R (finiteLevel p R G n)

/-- Forward dual-tower arrows are the duals of the original divisions. -/
def dualTransition (n m : ℕ) (h : n ≤ m) :
    dualLevel p R G n ⟶ dualLevel p R G m :=
  (cartierDualFunctor R).map (finiteDivisionBetween (G := G) n m h).op

/-- Dual division is the dual of the original subgroup inclusion. -/
def dualDivision (n m : ℕ) : dualLevel p R G (n + m) ⟶ dualLevel p R G m :=
  (cartierDualFunctor R).map
    (finiteInclusion (G := G) m (n + m) (Nat.le_add_left m n)).op

/-- Source-normalized assembly of the actual finite Cartier duals into a geometric tower. -/
structure CartierDualTower where
  group : PDivisibleGroup (Spec (.of R)) p
  finiteIso : ∀ n : ℕ, finiteLevel p R group n ≅ dualLevel p R G n
  inclusions : ∀ (n m : ℕ) (h : n ≤ m),
    finiteInclusion (G := group) n m h ≫ (finiteIso m).hom =
      (finiteIso n).hom ≫ dualTransition p R G n m h
  divisions : ∀ n m : ℕ,
    finiteDivision (G := group) n m ≫ (finiteIso m).hom =
      (finiteIso (n + m)).hom ≫ dualDivision p R G n m

/-- Every original finite geometric point is killed by its displayed p-power. -/
theorem finite_point_power (n : ℕ) (x : BaseTest R ⟶ G.levels.obj n) :
    x ^ (p ^ n) = 1 := by
  exact finite_point_torsion p (Spec (.of R)) G (BaseTest R) n (Additive.ofMul x)

set_option maxHeartbeats 1000000 in
/-- The original finite point becomes the original p-power coordinate root point. -/
def finiteCoordinateRoots (n : ℕ) :
    (BaseTest R ⟶ G.levels.obj n) →*
      rootPoints R (Coordinate R (finiteLevel p R G n)) p n where
  toFun x :=
    ⟨coordinatePointHom R (finiteLevel p R G n) x, by
      change coordinatePointHom R (finiteLevel p R G n) x ^ (p ^ n) = 1
      exact (map_pow (coordinatePointHom R (finiteLevel p R G n)) x (p ^ n)).symm.trans
        ((congrArg (coordinatePointHom R (finiteLevel p R G n))
          (finite_point_power p R G n x)).trans
            (coordinatePointHom R (finiteLevel p R G n)).map_one)⟩
  map_one' := by
    apply Subtype.ext
    exact (coordinatePointHom R (finiteLevel p R G n)).map_one
  map_mul' x y := by
    apply Subtype.ext
    exact (coordinatePointHom R (finiteLevel p R G n)).map_mul x y

/-- The actual invariant cotangent of the original finite dual coordinate algebra. -/
abbrev DualFiniteCotangent (n : ℕ) :=
  (dualAugmentedAlgebra R (Coordinate R (finiteLevel p R G n))).cotangent R

/-- Actual finite cotangent restriction dualizes the original division map. -/
def finiteCotangentTransition (n m : ℕ) (h : n ≤ m) :
    DualFiniteCotangent p R G m →ₗ[R] DualFiniteCotangent p R G n :=
  (dualAugmentedMap R (Coordinate R (finiteLevel p R G n))
    (Coordinate R (finiteLevel p R G m))
    (MathlibExt.FiniteLocallyFreeBicommutativeHopfAlgCat.toBialgHom
      (coordinateMap R (finiteLevel p R G m) (finiteDivisionBetween (G := G) n m h)))).cotangent R

/-- Original integral finite points map to their genuine Cartier-character dlog classes. -/
def geometricFiniteDlog (n : ℕ) :
    Additive (BaseTest R ⟶ G.levels.obj n) →+ DualFiniteCotangent p R G n :=
  (finiteDlog R (Coordinate R (finiteLevel p R G n)) p n).comp
    (finiteCoordinateRoots p R G n).toAdditive

end MathlibExt.AlgebraicGeometry.PDivisibleCartierTowerModels
