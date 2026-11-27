/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFrontFamily
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Whole original enriched simplices from original Hom simplices

A supplied Hom simplex gives an actual enriched coherent simplex: every
front object is the specified source and the last object is the specified
target. The front-to-last maps use the original last-front maximum, and
their union law makes them a `HomFrontFamily.Family`; the whole simplex is
the front-family construction for that family. No Kan or mapping-comparison
outcome is an input.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomSimplex
open SimplicialEnrichment PathLastMaximum
variable {C : Carrier.{u}} {n : ℕ} (x y : C) (τ : (Δ[n] : SSet.{u}) ⟶ (x ⟶[SSet.{u}] y))

/-- The whole original maximum map on the Hom from the supplied front vertex to the actual
last vertex. -/
def lastMap (i : Fin (n + 1)) : nerve (LastPath.{u} i) ⟶ (x ⟶[SSet.{u}] y) :=
  nerveMap (maximumFunctor i) ≫ (SSet.stdSimplex.isoNerve.{u} n).inv ≫ τ

/-- The original scalar Hom simplex is evaluated on the same maximum-labelled front ordinal. -/
theorem lastMap_apply (i : Fin (n + 1)) (q : SimplexCategoryᵒᵖ)
    (p : (nerve (LastPath.{u} i)).obj q) :
    (lastMap x y τ i).app q p = τ.app q ((SSet.stdSimplex.isoNerve.{u} n).inv.app q (p ⋙
      maximumFunctor i)) := rfl

/-- Whole original union composition with a front interval reads the same last Hom map. -/
theorem lastMap_compose (i j : Fin (n + 1)) (q : SimplexCategoryᵒᵖ)
    (p : (nerve (SimplicialThickening.Path (ULift.up.{u} i.castSucc) (ULift.up.{u}
      j.castSucc))).obj q)
    (r : (nerve (LastPath.{u} j)).obj q) :
    (lastMap x y τ i).app q
        (p.prod' r ⋙ SimplicialThickening.compFunctor (.mk (ULift.up i.castSucc))
          (SimplicialThickening.mk (ULift.up j.castSucc)) (SimplicialThickening.mk (ULift.up
            (Fin.last (n + 1))))) =
      (lastMap x y τ j).app q r := by
  change τ.app q ((SSet.stdSimplex.isoNerve.{u} n).inv.app q
      ((p.prod' r ⋙ SimplicialThickening.compFunctor _ _ _) ⋙ maximumFunctor i)) =
    τ.app q ((SSet.stdSimplex.isoNerve.{u} n).inv.app q (r ⋙ maximumFunctor j))
  congr 2
  refine Functor.ext (fun k => ULift.ext (maximum_compose i j (p.obj k) (r.obj k))) ?_
  intro k l f
  exact Subsingleton.elim _ _

/-- The original front-to-last maximum maps of the supplied Hom simplex, as a family of
last-interval maps compatible with every original front-prefix union. -/
def family : HomFrontFamily.Family x y n where
  map := lastMap x y τ
  map_comp := lastMap_compose x y τ

/-! The whole construction below is `HomFrontFamily.simplex` for this family. -/

/-- The supplied source at every original front vertex and supplied target at the actual
last vertex. -/
abbrev object (a : Fin (n + 2)) : C := HomFrontFamily.object x y a

/-- The original front object reads the supplied source. -/
theorem object_front (i : Fin (n + 1)) : object x y i.castSucc = x :=
  HomFrontFamily.object_front x y i

/-- The original last object reads the supplied target. -/
theorem object_last : object x y (Fin.last (n + 1)) = y := HomFrontFamily.object_last x y

/-- The actual whole Hom maps, including constant original front identities and genuinely
empty reverse intervals. -/
def homMap (a b : Fin (n + 2)) :
    nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b)) ⟶
      (object x y a ⟶[SSet.{u}] object x y b) :=
  HomFrontFamily.homMap x y (family x y τ) a b

/-- The whole original last Hom map reads back the maximum map after the exact endpoint
equalities. -/
theorem homMap_last (i : Fin (n + 1)) :
    homMap x y τ i.castSucc (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b) (object_front x y i)
        (object_last x y)) = lastMap
        x y τ i :=
  HomFrontFamily.homMap_last x y (family x y τ) i

/-- The whole original front Hom map reads back the supplied source identity after the same
exact endpoint
  equalities. -/
theorem homMap_front (i j : Fin (n + 1)) :
    homMap x y τ i.castSucc j.castSucc ≫
      eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b) (object_front x y i)
        (object_front x y j)) =
      toUnit _ ≫ eId SSet.{u} x :=
  HomFrontFamily.homMap_front x y (family x y τ) i j

/-- The last whole diagonal Hom map reads back the supplied target identity after its exact
object equality. -/
theorem homMap_last_last :
    homMap x y τ (Fin.last (n + 1)) (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b) (object_last x y) (object_last x y)) =
      toUnit _ ≫ eId SSet.{u} y :=
  HomFrontFamily.homMap_last_last x y (family x y τ)

/-- The constructed whole Hom maps preserve the original enriched identity at every original
vertex. -/
theorem homMap_id (a : Fin (n + 2)) :
    eId SSet.{u} (SimplicialThickening.mk (ULift.up.{u} a)) ≫ homMap x y τ a a =
      eId SSet.{u} (object x y a) :=
  HomFrontFamily.homMap_id x y (family x y τ) a

/-- The constructed whole Hom maps preserve actual original union composition at every
triple of original vertices. -/
theorem homMap_comp (a b c : Fin (n + 2)) :
    eComp SSet.{u} (SimplicialThickening.mk (ULift.up.{u} a))
      (SimplicialThickening.mk (ULift.up.{u} b)) (SimplicialThickening.mk (ULift.up.{u} c))
        ≫ homMap x y τ a c =
      (homMap x y τ a b ⊗ₘ homMap x y τ b c) ≫ eComp SSet.{u} (object x y a) (object
        x y b) (object x y c) :=
  HomFrontFamily.homMap_comp x y (family x y τ) a b c

/-- The actual enriched coherent simplex, with the original supplied source and target and
every whole Hom map. -/
def simplex : coherentSimplex.{u} ⦋n + 1⦌ ⟶ C := HomFrontFamily.simplex x y (family x y τ)

/-- Every front object is the supplied individual original source. -/
theorem simplex_front (i : Fin (n + 1)) : (simplex x y τ).obj (.mk (ULift.up i.castSucc)) = x :=
  HomFrontFamily.simplex_front x y (family x y τ) i

/-- The actual last object is the supplied individual original target. -/
theorem simplex_last : (simplex x y τ).obj (.mk (ULift.up (Fin.last (n + 1)))) = y :=
  HomFrontFamily.simplex_last x y (family x y τ)

end CategoryTheory.CoherentRealization.HomSimplex
