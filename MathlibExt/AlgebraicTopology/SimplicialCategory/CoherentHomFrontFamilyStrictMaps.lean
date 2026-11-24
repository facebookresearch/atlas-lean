/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFrontFamily

/-!
# Actual postcomposition of front-compatible Hom families

Strict original enriched maps act on the actual whole last-interval
families. The corresponding entire enriched simplex follows that same
map, including the original source, target and constant front identities.
There is no Kan, weak-equivalence or comparison outcome hypothesis.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomFrontFamilyStrictMaps
open SimplicialEnrichment HomFrontFamily
variable {C D : Carrier.{u}} {n : ℕ} (F : C ⟶ D) (x y : C)

/-- Postcompose every actual original last-interval map by the same supplied strict enriched
functor. -/
def postFamily (family : Family x y n) : Family (C := D) (F.obj x) (F.obj y) n where
  map i := family.map i ≫ F.map x y
  map_comp i j q p r := congrArg ((F.map x y).app q) (family.map_comp i j q p r)

private theorem map_reindex {a a' b b' : C} (ha : a = a') (hb : b = b') :
    F.map a b ≫ EqualityTransport.hom (congrArg F.obj ha) (congrArg F.obj hb) =
      EqualityTransport.hom ha hb ≫ F.map a' b' := by
  subst a'
  subst b'
  simp only [EqualityTransport.hom, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The actual source/last object assignment follows the same original strict enriched functor. -/
theorem object_map (a : Fin (n + 2)) :
    F.obj (HomFrontFamily.object x y a) = HomFrontFamily.object (F.obj x) (F.obj y) a := by
  cases a using Fin.lastCases <;>
    simp only [HomFrontFamily.object, Fin.lastCases_castSucc, Fin.lastCases_last]

private theorem whole_ext {A B : Carrier.{u}} (L R : A ⟶ B)
    (ho : ∀ a, L.obj a = R.obj a) (hm : ∀ a b, L.map a b ≍ R.map a b) : L = R := by
  refine EnrichedFunctor.ext SSet.{u} ho ?_
  intro a b
  exact eq_of_heq ((comp_eqToHom_heq _ _).trans (hm a b))

private theorem postcomp_retarget {X : SSet.{u}} {a a' b b' : C} (ha : a = a') (hb : b = b')
    (U : X ⟶ (a ⟶[SSet.{u}] b)) :
    (U ≫ EqualityTransport.hom ha hb) ≫ F.map a' b' ≍ U ≫ F.map a b := by
  have h := map_reindex F ha hb
  have h₀ : (U ≫ EqualityTransport.hom ha hb) ≫ F.map a' b' =
      (U ≫ F.map a b) ≫ EqualityTransport.hom (congrArg F.obj ha) (congrArg F.obj hb) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t => U ≫ t) h.symm).trans (Category.assoc _ _ _).symm)
  exact (heq_of_eq h₀).trans (comp_eqToHom_heq _ _)

/-- The entire original maximum simplex follows the same supplied strict enriched map. -/
theorem simplex_postcompose (family : Family x y n) :
    simplex x y family ≫ F = simplex (F.obj x) (F.obj y) (postFamily F x y family) := by
  let L := simplex x y family ≫ F
  let R := simplex (F.obj x) (F.obj y) (postFamily F x y family)
  have ho : ∀ a : coherentSimplex.{u} ⦋n + 1⦌, L.obj a = R.obj a := fun a =>
    object_map F x y a.as.down
  apply whole_ext L R ho
  intro a b
  cases a with | mk a =>
    cases a with | up a =>
      cases b with | mk b =>
        cases b with | up b =>
          cases a using Fin.lastCases with
          | last =>
            cases b using Fin.lastCases with
            | last =>
              change (homMap x y family _ _ ≫ F.map _ _) ≍ homMap (F.obj x) (F.obj y) _ _ _
              simp only [homMap, Fin.lastCases_last]
              have h := postcomp_retarget F (object_last (n := n) x y).symm (object_last (n
                := n) x y).symm
                (toUnit (nerve (SimplicialThickening.Path (ULift.up.{u} (Fin.last (n + 1)))
                  (ULift.up.{u}
                (Fin.last (n + 1))))) ≫ eId SSet.{u} y)
              have hI : (toUnit (nerve (SimplicialThickening.Path (ULift.up.{u} (Fin.last (n + 1)))
                (ULift.up.{u} (Fin.last (n + 1))))) ≫ eId SSet.{u} y) ≫ F.map y y = toUnit (nerve
                (SimplicialThickening.Path (ULift.up.{u} (Fin.last (n + 1))) (ULift.up.{u}
                  (Fin.last (n +
                1))))) ≫ eId SSet.{u} (F.obj y) :=
                (Category.assoc _ _ _).trans (congrArg (fun f =>
                  toUnit (nerve (SimplicialThickening.Path
                  (ULift.up.{u} (Fin.last (n + 1))) (ULift.up.{u} (Fin.last (n + 1))))) ≫
                    f) (F.map_id y))
              exact h.trans ((heq_of_eq hI).trans (comp_eqToHom_heq _ _).symm)
            | cast j =>
              apply (conj_eqToHom_iff_heq _ _ rfl (congrArg₂ (fun a b : D =>
                a ⟶[SSet.{u}] b) (ho (.mk
                (ULift.up (Fin.last (n + 1))))) (ho (.mk (ULift.up j.castSucc))))).mp
              rw [eqToHom_refl, Category.id_comp]
              apply HomUnitsAndEmpty.empty_hom_ext
                (show ¬(ULift.up.{u} (Fin.last (n + 1)) : ULift.{u} (Fin (n + 2))) ≤
                  ULift.up j.castSucc
                  from not_le.mpr (Fin.castSucc_lt_last j))
          | cast i =>
            cases b using Fin.lastCases with
            | last =>
              change (homMap x y family _ _ ≫ F.map _ _) ≍ homMap (F.obj x) (F.obj y) _ _ _
              simp only [homMap, Fin.lastCases_castSucc, Fin.lastCases_last]
              exact (postcomp_retarget F (object_front x y i).symm (object_last (n :=
                n) x y).symm (family.map i)).trans
                ((heq_of_eq ((rfl : family.map i ≫ F.map x y =
                  (postFamily F x y family).map i))).trans
                  (comp_eqToHom_heq _ _).symm)
            | cast j =>
              change (homMap x y family _ _ ≫ F.map _ _) ≍ homMap (F.obj x) (F.obj y) _ _ _
              simp only [homMap, Fin.lastCases_castSucc]
              have h := postcomp_retarget F (object_front x y i).symm (object_front x y
                j).symm (toUnit
                (nerve (SimplicialThickening.Path (ULift.up.{u} i.castSucc) (ULift.up.{u}
                  j.castSucc))) ≫
                eId SSet.{u} x)
              have hI : (toUnit (nerve (SimplicialThickening.Path (ULift.up.{u} i.castSucc)
                (ULift.up.{u}
                j.castSucc))) ≫ eId SSet.{u} x) ≫ F.map x x =
                  toUnit (nerve (SimplicialThickening.Path
                (ULift.up.{u} i.castSucc) (ULift.up.{u} j.castSucc))) ≫ eId SSet.{u} (F.obj x) :=
                (Category.assoc _ _ _).trans (congrArg (fun f =>
                  toUnit (nerve (SimplicialThickening.Path
                  (ULift.up.{u} i.castSucc) (ULift.up.{u} j.castSucc))) ≫ f) (F.map_id x))
              exact h.trans ((heq_of_eq hI).trans (comp_eqToHom_heq _ _).symm)


end CategoryTheory.CoherentRealization.HomFrontFamilyStrictMaps
