/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.Shuffle
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleDifferential.Maps
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryLeft.Signs
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShuffleBoundaryRight.Signs

/-!
# Boundary maps for the bisimplicial shuffle

This file supplies the map-level input for the bisimplicial shuffle
differential identity.  It reuses the existing shuffle boundary partitions
and sign formulas.  The only new ingredient is the interchange law for a
bisimplicial object, expressed through `Bisimplicial.map`.

Mixed boundary faces have equal underlying maps and hence cancel after the
existing sign involution.  Left and right boundary faces are identified with
an outer or inner face followed by the smaller shuffle map.
-/

@[expose] public section

open CategoryTheory Simplicial SimplexCategory
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialEilenbergZilber

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [Category.{v} A] [Preadditive A]
  (B : SimplicialObject (SimplicialObject A))

private theorem mixedFace_leftHom_eq {p q : ℕ}
    (x : AlgebraicTopology.EilenbergZilber.Shuffle.MixedFace (p + 1) (q + 1)) :
    SimplexCategory.δ (n := (p + 1) + q) (Fin.cast (by omega) x.faceIndex) ≫
        x.shuffle.leftHom =
      SimplexCategory.δ (n := (p + 1) + q)
          (Fin.cast (by omega) x.partner.faceIndex) ≫
        x.partner.shuffle.leftHom := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    SimplexCategory.len_mk, OrderHom.comp_coe, Function.comp_apply,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  exact congrArg Fin.val (x.leftHom_partner_succAbove k)

private theorem mixedFace_rightHom_eq {p q : ℕ}
    (x : AlgebraicTopology.EilenbergZilber.Shuffle.MixedFace (p + 1) (q + 1)) :
    SimplexCategory.δ (n := (p + 1) + q) (Fin.cast (by omega) x.faceIndex) ≫
        x.shuffle.rightHom =
      SimplexCategory.δ (n := (p + 1) + q)
          (Fin.cast (by omega) x.partner.faceIndex) ≫
        x.partner.shuffle.rightHom := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    SimplexCategory.len_mk, OrderHom.comp_coe, Function.comp_apply,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  exact congrArg Fin.val (x.rightHom_partner_succAbove k)

/-- The unsigned boundary map of a positive-bidegree shuffle and a diagonal
face. -/
noncomputable def diagonalBoundaryMapPositive (p q : ℕ)
    (s : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) (q + 1))
    (i : Fin ((p + 1) + (q + 1) + 1)) :
    (B.obj (Opposite.op ⦋p + 1⦌)).obj (Opposite.op ⦋q + 1⦌) ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        ((p + 1) + q) :=
  shuffleMap B s ≫
    ((SimplicialObject.diagonalFunctor A).obj B).δ
      (n := (p + 1) + q) (Fin.cast (by omega) i)

/-- A positive-bidegree shuffle boundary map is the bidegree map induced by
the two composites of simplex-category morphisms. -/
theorem diagonalBoundaryMapPositive_eq_map (p q : ℕ)
    (s : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) (q + 1))
    (i : Fin ((p + 1) + (q + 1) + 1)) :
    diagonalBoundaryMapPositive B p q s i =
      AlgebraicTopology.Bisimplicial.map B
        (SimplexCategory.δ (n := (p + 1) + q) (Fin.cast (by omega) i) ≫
          s.leftHom)
        (SimplexCategory.δ (n := (p + 1) + q) (Fin.cast (by omega) i) ≫
          s.rightHom) := by
  unfold diagonalBoundaryMapPositive shuffleMap
  change AlgebraicTopology.Bisimplicial.map B s.leftHom s.rightHom ≫
      ((SimplicialObject.diagonalFunctor A).obj B).map
        (SimplexCategory.δ (n := (p + 1) + q) (Fin.cast (by omega) i)).op = _
  rw [← AlgebraicTopology.Bisimplicial.map_diagonal]
  exact AlgebraicTopology.Bisimplicial.map_comp _ _ _ _ _

/-- Mixed partner faces induce the same unsigned bisimplicial boundary map. -/
theorem diagonalBoundaryMapPositive_partner (p q : ℕ)
    (x : AlgebraicTopology.EilenbergZilber.Shuffle.MixedFace (p + 1) (q + 1)) :
    diagonalBoundaryMapPositive B p q x.partner.shuffle x.partner.faceIndex =
      diagonalBoundaryMapPositive B p q x.shuffle x.faceIndex := by
  rw [diagonalBoundaryMapPositive_eq_map, diagonalBoundaryMapPositive_eq_map]
  exact congrArg₂ (AlgebraicTopology.Bisimplicial.map B)
    (mixedFace_leftHom_eq x).symm (mixedFace_rightHom_eq x).symm

/-- The diagonal-face sign times an unsigned positive-bidegree shuffle
boundary map. -/
noncomputable def shuffleBoundaryTermPositive (p q : ℕ)
    (s : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) (q + 1))
    (i : Fin ((p + 1) + (q + 1) + 1)) :
    (B.obj (Opposite.op ⦋p + 1⦌)).obj (Opposite.op ⦋q + 1⦌) ⟶
      (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
        ((p + 1) + q) :=
  ((-1 : ℤ) ^ i.val) • diagonalBoundaryMapPositive B p q s i

/-- Mixed partner faces have the same signed boundary term; their shuffle
signs are opposite in the boundary sum. -/
theorem shuffleBoundaryTermPositive_partner (p q : ℕ)
    (x : AlgebraicTopology.EilenbergZilber.Shuffle.MixedFace (p + 1) (q + 1)) :
    shuffleBoundaryTermPositive B p q x.partner.shuffle x.partner.faceIndex =
      shuffleBoundaryTermPositive B p q x.shuffle x.faceIndex := by
  unfold shuffleBoundaryTermPositive
  have h := diagonalBoundaryMapPositive_partner B p q x
  simpa only [AlgebraicTopology.EilenbergZilber.Shuffle.MixedFace.partner_faceIndex]
    using congrArg (fun k => ((-1 : ℤ) ^ x.faceIndex.val) • k) h

private theorem leftBoundaryIndex_cast_succAbove {p q : ℕ}
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p (q + 1))
    (a : Fin (p + 2)) (k : Fin ((p + 1) + q + 1)) :
    (Fin.cast (by omega)
        (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryIndex t a)).succAbove k =
      Fin.cast (by omega)
        ((AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryIndex t a).succAbove
          (Fin.cast (by omega) k)) := by
  apply Fin.ext
  simp only [Fin.succAbove, Fin.val_cast, Fin.val_castSucc, Fin.val_succ,
    apply_ite Fin.val]
  split_ifs
  all_goals simp_all [Fin.lt_def]
  omega

private theorem leftBoundary_outerHom_eq {p q : ℕ}
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p (q + 1))
    (a : Fin (p + 2)) :
    SimplexCategory.δ (n := (p + 1) + q)
          (Fin.cast (by omega)
            (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryIndex t a)) ≫
        (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryShuffle t a).leftHom =
      eqToHom (by rw [show (p + 1) + q = p + (q + 1) by omega]) ≫
        t.leftHom ≫ SimplexCategory.δ a := by
  ext k
  change Fin ((p + 1) + q + 1) at k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
    OrderHom.comp_coe, Function.comp_apply, OrderEmbedding.toOrderHom_coe,
    OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
    Fin.succAboveOrderEmb_apply]
  rw [leftBoundaryIndex_cast_succAbove]
  exact congrArg Fin.val
    (AlgebraicTopology.EilenbergZilber.Shuffle.leftHom_leftBoundaryShuffle_succAbove
      t a (Fin.cast (by omega) k))

private theorem leftBoundary_innerHom_eq {p q : ℕ}
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p (q + 1))
    (a : Fin (p + 2)) :
    SimplexCategory.δ (n := (p + 1) + q)
          (Fin.cast (by omega)
            (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryIndex t a)) ≫
        (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryShuffle t a).rightHom =
      eqToHom (by rw [show (p + 1) + q = p + (q + 1) by omega]) ≫
        t.rightHom := by
  ext k
  change Fin ((p + 1) + q + 1) at k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    SimplexCategory.eqToHom_toOrderHom, SimplexCategory.len_mk,
    OrderHom.comp_coe, Function.comp_apply, OrderEmbedding.toOrderHom_coe,
    OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply,
    Fin.succAboveOrderEmb_apply]
  rw [leftBoundaryIndex_cast_succAbove]
  exact congrArg Fin.val
    (AlgebraicTopology.EilenbergZilber.Shuffle.rightHom_leftBoundaryShuffle_succAbove
      t a (Fin.cast (by omega) k))

/-- A left-boundary shuffle face is an outer face followed by the smaller
shuffle, with the canonical total-degree transport. -/
theorem diagonalBoundaryMapPositive_leftBoundary (p q : ℕ)
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p (q + 1))
    (a : Fin (p + 2)) :
    diagonalBoundaryMapPositive B p q
        (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryShuffle t a)
        (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryIndex t a) =
      (B.δ a).app (Opposite.op ⦋q + 1⦌) ≫ shuffleMap B t ≫
        (eqToHom (by rw [show p + (q + 1) = (p + 1) + q by omega]) :
          (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
              (p + (q + 1)) ⟶
            (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
              ((p + 1) + q)) := by
  rw [diagonalBoundaryMapPositive_eq_map]
  unfold shuffleMap
  rw [← Category.assoc]
  rw [← AlgebraicTopology.Bisimplicial.map_delta_id]
  rw [AlgebraicTopology.Bisimplicial.map_comp]
  rw [← AlgebraicTopology.Bisimplicial.map_eqToHom B
    (show (p + 1) + q = p + (q + 1) by omega)
    (show (p + 1) + q = p + (q + 1) by omega)]
  rw [AlgebraicTopology.Bisimplicial.map_comp]
  simp only [Category.comp_id]
  exact congrArg₂ (AlgebraicTopology.Bisimplicial.map B)
    (leftBoundary_outerHom_eq t a) (leftBoundary_innerHom_eq t a)

private theorem rightBoundaryIndex_succAbove_cast {p q : ℕ}
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p q)
    (b : Fin (q + 2)) (k : Fin (p + q + 1)) :
    (Fin.cast rfl
      (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryIndex t b)).succAbove k =
      (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryIndex t b).succAbove
        (Fin.cast (by omega) k) := by
  apply Fin.ext
  simp only [Fin.succAbove, Fin.val_cast, Fin.val_castSucc, Fin.val_succ,
    apply_ite Fin.val]
  split_ifs
  all_goals simp_all [Fin.lt_def]
  omega

private theorem rightBoundary_innerHom_eq {p q : ℕ}
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p q)
    (b : Fin (q + 2)) :
    SimplexCategory.δ
          (Fin.cast rfl
            (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryIndex
              (p := p) (q := q) t b)) ≫
        (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryShuffle
          (p := p) (q := q) t b).rightHom =
      t.rightHom ≫ SimplexCategory.δ b := by
  ext k
  change Fin (p + q + 1) at k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    SimplexCategory.len_mk, OrderHom.comp_coe, Function.comp_apply,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [rightBoundaryIndex_succAbove_cast]
  exact congrArg Fin.val
    (AlgebraicTopology.EilenbergZilber.Shuffle.rightHom_rightBoundaryShuffle_succAbove
      t b k)

private theorem rightBoundary_outerHom_eq {p q : ℕ}
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p q)
    (b : Fin (q + 2)) :
    SimplexCategory.δ
          (Fin.cast rfl
            (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryIndex
              (p := p) (q := q) t b)) ≫
        (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryShuffle
          (p := p) (q := q) t b).leftHom =
      t.leftHom := by
  ext k
  change Fin (p + q + 1) at k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    SimplexCategory.len_mk, OrderHom.comp_coe, Function.comp_apply,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [rightBoundaryIndex_succAbove_cast]
  exact congrArg Fin.val
    (AlgebraicTopology.EilenbergZilber.Shuffle.leftHom_rightBoundaryShuffle_succAbove
      t b k)

/-- A right-boundary shuffle face is an inner face followed by the smaller
shuffle. -/
theorem diagonalBoundaryMapPositive_rightBoundary (p q : ℕ)
    (t : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) q)
    (b : Fin (q + 2)) :
    diagonalBoundaryMapPositive B p q
        (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryShuffle t b)
        (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryIndex t b) =
      (B.obj (Opposite.op ⦋p + 1⦌)).δ b ≫ shuffleMap B t := by
  rw [diagonalBoundaryMapPositive_eq_map]
  unfold shuffleMap
  rw [← AlgebraicTopology.Bisimplicial.map_id_delta]
  rw [AlgebraicTopology.Bisimplicial.map_comp]
  simp only [Category.comp_id]
  exact congrArg₂ (AlgebraicTopology.Bisimplicial.map B)
    (rightBoundary_outerHom_eq t b) (rightBoundary_innerHom_eq t b)

/-- The signed contribution of a left-boundary face. -/
theorem shuffleBoundaryTermPositive_leftBoundary (p q : ℕ)
    (t : AlgebraicTopology.EilenbergZilber.Shuffle p (q + 1))
    (a : Fin (p + 2)) :
    AlgebraicTopology.EilenbergZilber.shuffleSignZ
          (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryShuffle t a) •
        shuffleBoundaryTermPositive B p q
          (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryShuffle t a)
          (AlgebraicTopology.EilenbergZilber.Shuffle.leftBoundaryIndex t a) =
      (((-1 : ℤ) ^ a.val) * AlgebraicTopology.EilenbergZilber.shuffleSignZ t) •
        ((B.δ a).app (Opposite.op ⦋q + 1⦌) ≫ shuffleMap B t ≫
          (eqToHom (by rw [show p + (q + 1) = (p + 1) + q by omega]) :
            (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
                (p + (q + 1)) ⟶
              (AlgebraicTopology.BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X
                ((p + 1) + q))) := by
  unfold shuffleBoundaryTermPositive
  rw [diagonalBoundaryMapPositive_leftBoundary]
  simp only [smul_smul]
  rw [mul_comm]
  rw [AlgebraicTopology.EilenbergZilber.Shuffle.shuffleSignZ_leftBoundaryShuffle]

/-- The signed contribution of a right-boundary face. -/
theorem shuffleBoundaryTermPositive_rightBoundary (p q : ℕ)
    (t : AlgebraicTopology.EilenbergZilber.Shuffle (p + 1) q)
    (b : Fin (q + 2)) :
    AlgebraicTopology.EilenbergZilber.shuffleSignZ
          (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryShuffle t b) •
        shuffleBoundaryTermPositive B p q
          (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryShuffle t b)
          (AlgebraicTopology.EilenbergZilber.Shuffle.rightBoundaryIndex t b) =
      (((-1 : ℤ) ^ (p + 1 + b.val)) *
          AlgebraicTopology.EilenbergZilber.shuffleSignZ t) •
        ((B.obj (Opposite.op ⦋p + 1⦌)).δ b ≫ shuffleMap B t) := by
  unfold shuffleBoundaryTermPositive
  rw [diagonalBoundaryMapPositive_rightBoundary]
  simp only [smul_smul]
  rw [mul_comm]
  rw [AlgebraicTopology.EilenbergZilber.Shuffle.shuffleSignZ_rightBoundaryShuffle]

end AlgebraicTopology.BisimplicialEilenbergZilber
