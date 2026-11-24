/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeRelations
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFrontFamily
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomSuspensionForward

/-!
# Actual front-compatible maps into the free right-cube suspension

Each original last interval is prepended by the original zero vertex and
then mapped into the actual front-composition quotient. The generating
quotient relation proves compatibility with every original front prefix.
The free suspension supplies its original whole forward Hom; no realized
Hom identification is assumed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeFrontFamily
open SimplicialEnrichment PathLastMaximum RightCubeRelations
variable {n : ℕ}

/-- The original zero-prepended front prefix of an actual supplied interval. -/
def zeroPrefix {i j : Fin (n + 1)}
    (p : SimplicialThickening.Path (ULift.up.{u} i.castSucc) (ULift.up.{u} j.castSucc)) :
    SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} j.castSucc) where
  I := {ULift.up.{u} (0 : Fin (n + 2))} ∪ p.I
  left := Or.inl rfl
  right := Or.inr p.right
  left_le k _ := Fin.zero_le k.down
  le_right k := by
    rintro (rfl | hk)
    · exact Fin.zero_le _
    · exact p.le_right k hk

/-- The whole original front-prefix zero insertion functor. -/
def zeroPrefixFunctor (i j : Fin (n + 1)) :
    SimplicialThickening.Path (ULift.up.{u} i.castSucc) (ULift.up.{u} j.castSucc) ⥤
      SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} j.castSucc) where
  obj := zeroPrefix
  map f := ⟨homOfLE (Set.union_subset_union le_rfl f.hom.down.down)⟩

/-- Original zero insertion commutes with the whole union of a front prefix and last interval. -/
theorem prepend_union (i j : Fin (n + 1))
    (p : SimplicialThickening.Path (ULift.up.{u} i.castSucc) (ULift.up.{u} j.castSucc))
    (r : LastPath.{u} j) :
    prependZero i (compose i j p r) = compose 0 j (zeroPrefix p) r := by
  apply SimplicialThickening.Path.ext
  exact (Set.union_assoc _ _ _).symm

/-- The same original zero-prefix union equation retains every scalar simplex and its operators. -/
theorem prepend_chain (i j : Fin (n + 1)) (q : SimplexCategoryᵒᵖ)
    (p : (nerve (SimplicialThickening.Path (ULift.up.{u} i.castSucc) (ULift.up.{u}
      j.castSucc))).obj q)
    (r : (nerve (LastPath.{u} j)).obj q) :
    (p.prod' r ⋙ SimplicialThickening.compFunctor (.mk (ULift.up i.castSucc))
      (.mk (ULift.up j.castSucc)) (.mk (ULift.up (Fin.last (n + 1))))) ⋙ prependFunctor i =
    (p ⋙ zeroPrefixFunctor i j).prod' r ⋙ SimplicialThickening.compFunctor (.mk
      (ULift.up (0 : Fin (n + 2))))
      (.mk (ULift.up j.castSucc)) (.mk (ULift.up (Fin.last (n + 1)))) := by
  refine Functor.ext (fun k => prepend_union i j (p.obj k) (r.obj k)) ?_
  intro k l f
  apply InducedCategory.Hom.ext
  exact Subsingleton.elim _ _

/-- The actual original front-composition quotient removes every front prefix at its
supplied original endpoint. -/
theorem quotient_union (i j : Fin (n + 1)) (q : SimplexCategoryᵒᵖ)
    (p : (nerve (SimplicialThickening.Path (ULift.up.{u} i.castSucc) (ULift.up.{u}
      j.castSucc))).obj q)
    (r : (nerve (LastPath.{u} j)).obj q) :
    (RightCubeRelations.projection n).app q
      ((p.prod' r ⋙ SimplicialThickening.compFunctor (.mk (ULift.up i.castSucc))
        (.mk (ULift.up j.castSucc)) (.mk (ULift.up (Fin.last (n + 1))))) ⋙ prependFunctor i) =
      (RightCubeRelations.projection n).app q (r ⋙ prependFunctor j) :=
  (congrArg ((RightCubeRelations.projection n).app q) (prepend_chain i j q p r)).trans
    (_root_.Quotient.sound (Relation.EqvGen.rel _ _
      (RightCubeRelations.Relation.composition (n := n) j (p ⋙ zeroPrefixFunctor i j) r)))

/-- The genuine whole original last-interval family into the constructed free suspension of
the right cube. -/
def family (n : ℕ) : HomFrontFamily.Family
    (C := HomSuspensionGenerators.carrier (RightCubeRelations.object.{u} n))
    HomSuspensionGenerators.left HomSuspensionGenerators.right n where
  map i := nerveMap (prependFunctor i) ≫ RightCubeRelations.projection n ≫
    (HomSuspensionForward.homIso (RightCubeRelations.object n)).hom
  map_comp i j q p r := congrArg
    ((HomSuspensionForward.homIso (RightCubeRelations.object n)).hom.app q) (quotient_union
      i j q p r)

/-- The original successor simplex gives an actual enriched functor into the free right-cube
suspension. -/
def functor (n : ℕ) : coherentSimplex.{u} ⦋n + 1⦌ ⟶
    HomSuspensionGenerators.carrier (RightCubeRelations.object.{u} n) :=
  HomFrontFamily.simplex _ _ (family n)

end CategoryTheory.CoherentRealization.RightCubeFrontFamily
