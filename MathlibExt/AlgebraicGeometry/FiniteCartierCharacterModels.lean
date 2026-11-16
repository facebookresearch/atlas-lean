/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffineGroupScheme.CartierDuality.FiniteLocallyFree
public import MathlibExt.AlgebraicGeometry.IntegralRootDlogModels
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Actual finite Cartier characters and their integral dlog

A base-valued point of a finite projective Hopf algebra is its original
algebra homomorphism. The corresponding character of the finite dual is
that exact functional, with no new coefficient choice. Its group-like
equations express the character multiplication and identity on the
original finite dual. The p-power character then maps by u to [u-1] in
the actual augmentation ideal modulo its square at the original base.

The group-scheme point dictionary below uses the completed native Cartier
anti-equivalence and its actual Hopf-spectrum counit. Every commutative
base algebra, including nilpotent and zero algebras, is allowed.

Sources: Waterhouse, Introduction to Affine Group Schemes, Chapter 2;
Scholze--Weinstein, arXiv:1211.6357v2, Section 1 Hodge--Tate sequence.
Finite dualization and its proofs are the credited pinned Tau source ports.
Passing finite characters to the formal cotangent is separate construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteCartierCharacterModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.Coalgebra WithConv
open GroupZeroCotangentModels IntegralRootDlogModels
open scoped TensorProduct
open scoped _root_.CategoryTheory.MonObj

variable (R H : Type) [CommRing R] [CommRing H] [HopfAlgebra R H]
  [Module.Finite R H] [Module.Projective R H] [IsCocomm R H]

/-- Original base-valued points, with their actual convolution group law. -/
abbrev HopfPoints := WithConv (H →ₐ[R] R)

/-- The corresponding character is precisely the original point functional. -/
def pointCharacter (x : HopfPoints R H) : GroupLike R (ConvolutionDual R H) where
  val := toConv x.ofConv.toLinearMap
  isGroupLikeElem_val :=
    { counit_eq_one := by
        rw [ConvolutionDual.counit_apply]
        exact x.ofConv.map_one
      comul_eq_tmul_self := by
        apply (ConvolutionDual.dualDistribEquiv R H).injective
        apply TensorProduct.ext'
        intro a b
        rw [ConvolutionDual.dualDistribEquiv_comul_apply,
          ConvolutionDual.dualDistribEquiv_tmul_apply]
        exact x.ofConv.map_mul a b }

/-- Cartier character extraction preserves the original finite point group law. -/
def pointCharacterHom : HopfPoints R H →* GroupLike R (ConvolutionDual R H) where
  toFun := pointCharacter R H
  map_one' := by
    apply GroupLike.ext
    exact AlgHom.toLinearMap_convOne
  map_mul' x y := by
    apply GroupLike.ext
    exact AlgHom.toLinearMap_convMul x y

/-- The actual finite-dual coordinate ring and its actual identity augmentation. -/
def dualAugmentedAlgebra : AugmentedAlgebra R where
  ring := CommAlgCat.of R (ConvolutionDual R H)
  augmentation := Bialgebra.counitAlgHom R (ConvolutionDual R H)

/-- Transpose an original coordinate Hopf map, preserving its actual augmentation. -/
def dualAugmentedMap (K : Type) [CommRing K] [HopfAlgebra R K]
    [Module.Finite R K] [Module.Projective R K] [IsCocomm R K] (f : H →ₐc[R] K) :
    AugmentedMap R (dualAugmentedAlgebra R K) (dualAugmentedAlgebra R H) where
  map := (ConvolutionDual.map R f).toAlgHom
  augmentation := BialgHom.counitAlgHom_comp (ConvolutionDual.map R f)

/-- The character's original unit; its inverse is the native antipode. -/
def characterUnit : HopfPoints R H →* (dualAugmentedAlgebra R H).ringˣ where
  toFun x :=
    { val := (pointCharacter R H x).val
      inv := HopfAlgebra.antipode (A := ConvolutionDual R H) R (pointCharacter R H x).val
      val_inv := (pointCharacter R H x).isGroupLikeElem_val.mul_antipode_cancel
      inv_val := (pointCharacter R H x).isGroupLikeElem_val.antipode_mul_cancel }
  map_one' := by
    apply Units.ext
    exact congrArg GroupLike.val (pointCharacterHom R H).map_one
  map_mul' x y := by
    apply Units.ext
    exact congrArg GroupLike.val ((pointCharacterHom R H).map_mul x y)

/-- The identity section is preserved before any localization at p. -/
theorem characterUnit_augmentation (x : HopfPoints R H) :
    (dualAugmentedAlgebra R H).augmentation (characterUnit R H x) = 1 := by
  change counit (R := R) (pointCharacter R H x).val = 1
  exact (pointCharacter R H x).isGroupLikeElem_val.counit_eq_one

variable (p : ℕ) [Fact p.Prime]

/-- Actual p-power torsion points of this original finite point group. -/
def rootPoints (n : ℕ) : Subgroup (HopfPoints R H) :=
  (powMonoidHom (p ^ n)).ker

/-- The actual Cartier character of a p-power point, based at the original identity. -/
def rootCharacter (n : ℕ) : rootPoints R H p n →*
    basedRoots p R (dualAugmentedAlgebra R H) n where
  toFun x :=
    ⟨characterUnit R H x, by
      constructor
      · have hx : (x : HopfPoints R H) ^ (p ^ n) = 1 := x.property
        rw [← map_pow, hx, map_one]
      · exact characterUnit_augmentation R H x⟩
  map_one' := by apply Subtype.ext; exact (characterUnit R H).map_one
  map_mul' x y := by apply Subtype.ext; exact (characterUnit R H).map_mul x y

/-- Pull back finite Cartier dlog to the actual integral cotangent I/I². -/
def finiteDlog (n : ℕ) : Additive (rootPoints R H p n) →+
    (dualAugmentedAlgebra R H).cotangent R :=
  (basedDlog p R (dualAugmentedAlgebra R H) n).comp
    (rootCharacter R H p n).toAdditive

omit [Fact p.Prime] in
/-- No coefficient has been replaced: the character evaluates as the original point. -/
theorem character_coefficient (x : HopfPoints R H) (a : H) :
    ((show ConvolutionDual R H from
      (characterUnit R H x : (dualAugmentedAlgebra R H).ring)).ofConv) a = x.ofConv a := rfl

section Geometry

open MathlibExt.FiniteLocallyFreeCommAffineGroupSchemeCat

variable (G : FiniteLocallyFreeCommAffineGroupSchemeCat (.of R))

/-- The original coordinate Hopf algebra, obtained from the native source counit. -/
abbrev Coordinate := coordinateHopfAlgebra R G

/-- The original scheme group map induces its actual contravariant coordinate map. -/
def coordinateMap {K : FiniteLocallyFreeCommAffineGroupSchemeCat (.of R)} (f : G ⟶ K) :
    Coordinate R K ⟶ Coordinate R G :=
  (finiteLocallyFreeBicommutativeHopfAlgCatOpEquivFiniteLocallyFreeCommAffineGroupSchemeCat
    R).rightOp.inverse.map f.op

/-- The source native Hopf spectrum recovers the actual original finite group. -/
def coordinateSchemeIso :
    (hopfSpec (.of R)).obj (op (Coordinate R G).obj) ≅ G.obj.obj :=
  ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso (.of R)).app
    (op (Coordinate R G).obj)).symm ≪≫
      (affineGroupSchemeProperty (.of R)).ι.mapIso
        (hopfSpecCoordinateHopfAlgebraIso R G)

/-- The original base scheme is the actual point test, not a chosen point carrier. -/
abbrev BaseTest := (Spec (.of R)).asOver (Spec (.of R))

/-- Every actual coefficient algebra is an original scheme-valued point test. -/
abbrev AlgebraTest (A : Type) [CommRing A] [Algebra R A] :=
  (Spec (.of A)).asOver (Spec (.of R))

/-- The actual coordinate dictionary on every R-algebra, retaining all nilpotents. -/
def coordinatePointAt (A : Type) [CommRing A] [Algebra R A] :
    (AlgebraTest R A ⟶ G.obj.obj.X) →* WithConv (Coordinate R G →ₐ[R] A) :=
  (Spec.mapMulEquiv (R := R) (S := Coordinate R G) (T := A)).symm.toMonoidHom.comp
    (((yonedaGrp (C := Over (Spec (.of R)))).map
      (coordinateSchemeIso R G).inv).app (op (AlgebraTest R A))).hom

/-- The dictionary recovers the entire original scheme point on every algebra test. -/
theorem coordinate_point_recovers (A : Type) [CommRing A] [Algebra R A]
    (x : AlgebraTest R A ⟶ G.obj.obj.X) :
    Spec.mapMulEquiv (R := R) (S := Coordinate R G) (T := A) (coordinatePointAt R G A x) =
      x ≫ (coordinateSchemeIso R G).inv.hom.hom :=
  (Spec.mapMulEquiv (R := R) (S := Coordinate R G) (T := A)).apply_symm_apply _

/-- Original scheme points become their actual coordinate algebra maps. -/
def coordinatePointHom :
    (BaseTest R ⟶ G.obj.obj.X) →* HopfPoints R (Coordinate R G) :=
  (Spec.mapMulEquiv (R := R) (S := Coordinate R G) (T := R)).symm.toMonoidHom.comp
    (((yonedaGrp (C := Over (Spec (.of R)))).map
      (coordinateSchemeIso R G).inv).app (op (BaseTest R))).hom

/-- The genuine finite Cartier character of the original scheme-valued point. -/
def geometricCharacter :
    (BaseTest R ⟶ G.obj.obj.X) →* GroupLike R (ConvolutionDual R (Coordinate R G)) :=
  (pointCharacterHom R (Coordinate R G)).comp (coordinatePointHom R G)

/-- The actual dual coordinate ring comparison is supplied by completed Cartier duality. -/
def dualCoordinateIso :
    Coordinate R (cartierDual R G) ≅
      MathlibExt.FiniteLocallyFreeBicommutativeHopfAlgCat.dual (Coordinate R G) :=
  coordinateHopfAlgebraCartierDualIso R G

end Geometry

end MathlibExt.AlgebraicGeometry.FiniteCartierCharacterModels
