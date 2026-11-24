/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import MathlibExt.Algebra.Module.Torsion.TateModule
public import MathlibExt.AlgebraicGeometry.PDivisiblePointFunctors

/-!
# The original geometric Tate module of a p-divisible scheme tower

The point group is the original filtered group-scheme point diagram.
Its Tate module is the repository's root `TateModule` of that group
(compatible p-power torsion sequences, with its Z_p-module structure);
the torsion-level projections and induced maps come from the adapted
source port. No second Tate carrier or inverse-limit construction is
requested.

The finite geometric levels map to their actual p-power-torsion
subgroups. This is the domain used by the Cartier/dlog/formal-Lie
Hodge--Tate realization. At a generic geometric point over O_C the test
is the actual Spec C map, while the formal cotangent lives over O_C.

Source: Scholze--Weinstein, arXiv:1211.6357v2, Section 3.3;
TauCeti/Algebra/Module/Torsion/TateModule.lean, pinned source core.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDivisibleGeometricTateModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open PDivisibleGroupSchemes PDivisiblePointFunctors
open MathlibExt.Algebra.Module.Torsion

variable (p : ℕ) [Fact p.Prime]

/-- The original generic Tate map, regarded as a native coefficient functor. -/
def genericTateFunctor : AddCommGrpCat.{0} ⥤ ModuleCat.{0} (PadicInt p) where
  obj A := ModuleCat.of (PadicInt p) ↥(_root_.TateModule p A)
  map f := ModuleCat.ofHom (TateModule.mapLinearMap f.hom)
  map_id A := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact DFunLike.congr_fun (TateModule.map_id (p := p) (A := A)) x
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact DFunLike.congr_fun (TateModule.map_comp (p := p) g.hom f.hom) x

variable (S : Scheme.{0}) (G : PDivisibleGroup S p)

/-- The actual geometric group-valued filtered point colimit, written additively. -/
def points : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  pointwisePoints (p := p) (S := S) G ⋙ CommGrpCat.toAddCommGrp

/-- Every scheme test uses the native Z_p-linear Tate module of that exact point group. -/
def geometricTateFunctor : (Over S)ᵒᵖ ⥤ ModuleCat.{0} (PadicInt p) :=
  points p S G ⋙ genericTateFunctor p

/-- The actual geometric Tate carrier, not a supplied lattice. -/
abbrev GeometricTate (T : Over S) := (geometricTateFunctor p S G).obj (op T)

/-- The finite torsion level in that original geometric point group. -/
abbrev TorsionLevel (T : Over S) (n : ℕ) :=
  TateModuleLevel p ((points p S G).obj (op T)) n

/-- The actual finite projection of the generic source Tate inverse limit. -/
def projection (T : Over S) (n : ℕ) : GeometricTate p S G T →+ TorsionLevel p S G T n :=
  TateModule.levelProj n

/-- The actual finite-level group-valued point diagram. -/
def finitePoints (n : ℕ) : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  levelPoints (p := p) (S := S) G n ⋙ CommGrpCat.toAddCommGrp

/-- The original geometric inclusion of that level into the point colimit. -/
def finiteInclusion (n : ℕ) : finitePoints p S G n ⟶ points p S G :=
  _root_.CategoryTheory.Functor.whiskerRight
    (levelInclusion (p := p) (S := S) G n) CommGrpCat.toAddCommGrp

omit [Fact p.Prime] in
/-- Group multiplication is its original pointwise group power. -/
theorem multiplication_point (A : Over S) [GrpObj A] [IsCommMonObj A]
    (n : ℕ) (T : Over S) (x : T ⟶ A) :
    x ≫ multiply S A n = x ^ n := by
  simpa [multiply] using (MonObj.comp_pow (𝟙 A) n x)

/-- The geometric kernel square forces exactly p^n-torsion at level n. -/
theorem level_multiplication (n : ℕ) :
    multiply S (G.levels.obj n) (p ^ n) =
      toUnit (G.levels.obj n) ≫ η[G.levels.obj n] := by
  have h := (G.kernel n 0).w
  simpa only [Nat.add_zero, homOfLE_refl, _root_.CategoryTheory.Functor.map_id,
    Category.id_comp] using h

/-- Every original finite geometric point is killed by its displayed p-power. -/
theorem finite_point_torsion (T : Over S) (n : ℕ)
    (x : (finitePoints p S G n).obj (op T)) : (p ^ n) • x = 0 := by
  let y : T ⟶ G.levels.obj n := Additive.toMul x
  have h := congrArg (fun f : G.levels.obj n ⟶ G.levels.obj n ↦
    y ≫ f) (level_multiplication p S G n)
  rw [multiplication_point] at h
  have he : y ≫ toUnit (G.levels.obj n) = toUnit T := comp_toUnit y
  rw [← Category.assoc, he] at h
  change y ^ (p ^ n) = 1 at h
  exact h

/-- The original level inclusion lands in its actual native Tate torsion level. -/
def finiteToTorsion (T : Over S) (n : ℕ) :
    (finitePoints p S G n).obj (op T) →+ TorsionLevel p S G T n :=
  ((finiteInclusion p S G n).app (op T)).hom.codRestrict
    (AddSubgroup.torsionBy ((points p S G).obj (op T)) ((p ^ n : ℕ) : ℤ)) (by
      intro x
      apply AddSubgroup.torsionBy.nsmul_iff.mpr
      rw [← map_nsmul, finite_point_torsion, map_zero])

end MathlibExt.AlgebraicGeometry.PDivisibleGeometricTateModels
