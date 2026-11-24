/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentPathLastMaximum
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedSingletonHomUnits
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedEqualityTransport

/-!
# Whole coherent simplices from actual front-compatible Hom families

An actual family of last-interval maps, compatible with each original
front-prefix union, supplies all Hom maps of a genuine enriched simplex.
Its front identities, reverse empty intervals, units and composition
are proved using the original interval nerves. The input consists of
these actual Hom maps and their generating union law, not a comparison
or weak-equivalence outcome. The original Hom simplex construction of
`CoherentHomSimplex` is the instance of this one for the maximum maps.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomFrontFamily
open SimplicialEnrichment PathLastMaximum

/-- Actual original last-interval maps with their generating front-prefix union law. -/
structure Family {C : Carrier.{u}} (x y : C) (n : ℕ) where
  /-- The whole map on each original last interval. -/
  map (i : Fin (n + 1)) : nerve (LastPath.{u} i) ⟶ (x ⟶[SSet.{u}] y)
  /-- Union with an original front-prefix interval reads the same actual last factor. -/
  map_comp (i j : Fin (n + 1)) (q : SimplexCategoryᵒᵖ)
      (p : (nerve (SimplicialThickening.Path (ULift.up.{u} i.castSucc) (ULift.up.{u}
        j.castSucc))).obj q)
      (r : (nerve (LastPath.{u} j)).obj q) :
      (map i).app q (p.prod' r ⋙ SimplicialThickening.compFunctor
        (.mk (ULift.up i.castSucc)) (SimplicialThickening.mk (ULift.up j.castSucc))
        (SimplicialThickening.mk (ULift.up (Fin.last (n + 1))))) = (map j).app q r

variable {C : Carrier.{u}} {n : ℕ} (x y : C) (family : Family x y n)

/-- The supplied source at every original front vertex and supplied target at the actual
last vertex. -/
abbrev object (a : Fin (n + 2)) : C := Fin.lastCases y (fun _ => x) a

/-- The original front object reads the supplied source. -/
theorem object_front (i : Fin (n + 1)) : object x y i.castSucc = x := Fin.lastCases_castSucc i

/-- The original last object reads the supplied target. -/
theorem object_last : object x y (Fin.last (n + 1)) = y := Fin.lastCases_last

/-- The actual whole Hom maps, including constant original front identities and genuinely
empty reverse intervals. -/
def homMap (a b : Fin (n + 2)) :
    nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b)) ⟶
      (object x y a ⟶[SSet.{u}] object x y b) := by
  classical
  cases a using Fin.lastCases with
  | last =>
    cases b using Fin.lastCases with
    | last =>
      exact (toUnit _ ≫ eId SSet.{u} y) ≫
        EqualityTransport.hom (object_last x y).symm (object_last x y).symm
    | cast i =>
      exact HomUnitsAndEmpty.emptyMap
        (show ¬(ULift.up.{u} (Fin.last (n + 1)) : ULift.{u} (Fin (n + 2))) ≤ ULift.up
          i.castSucc from
          not_le.mpr (Fin.castSucc_lt_last i)) _
  | cast i =>
    cases b using Fin.lastCases with
    | last =>
      exact family.map i ≫
        EqualityTransport.hom (object_front x y i).symm (object_last x y).symm
    | cast j =>
      exact (toUnit _ ≫ eId SSet.{u} x) ≫
        EqualityTransport.hom (object_front x y i).symm (object_front x y j).symm

/-- The whole original last Hom map reads back the maximum map after the exact endpoint
equalities. -/
theorem homMap_last (i : Fin (n + 1)) :
    homMap x y family i.castSucc (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b) (object_front x y i)
        (object_last x y)) = family.map i := by
  simp only [homMap, EqualityTransport.hom, Fin.lastCases_castSucc, Fin.lastCases_last,
    Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The whole original front Hom map reads back the supplied source identity after the same
exact endpoint
  equalities. -/
theorem homMap_front (i j : Fin (n + 1)) :
    homMap x y family i.castSucc j.castSucc ≫
      eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b) (object_front x y i)
        (object_front x y j)) =
      toUnit _ ≫ eId SSet.{u} x := by
  simp only [homMap, EqualityTransport.hom, Fin.lastCases_castSucc, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

/-- The last whole diagonal Hom map reads back the supplied target identity after its exact
object equality. -/
theorem homMap_last_last :
    homMap x y family (Fin.last (n + 1)) (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b) (object_last x y) (object_last x y)) =
      toUnit _ ≫ eId SSet.{u} y := by
  simp only [homMap, EqualityTransport.hom, Fin.lastCases_last, Category.assoc,
    eqToHom_trans, eqToHom_refl,
    Category.comp_id]

/-- The constructed whole Hom maps preserve the original enriched identity at every original
vertex. -/
theorem homMap_id (a : Fin (n + 2)) :
    eId SSet.{u} (SimplicialThickening.mk (ULift.up.{u} a)) ≫ homMap x y family a a =
      eId SSet.{u} (object x y a) := by
  cases a using Fin.lastCases with
  | last =>
    simp only [homMap, Fin.lastCases_last]
    apply EqualityTransport.identity_retarget (C := C) (A :=
      coherentSimplex.{u} ⦋n + 1⦌) (.mk (ULift.up.{u}
      (Fin.last (n + 1))) : coherentSimplex.{u} ⦋n + 1⦌)
      (object_last x y).symm
    ext q p
    rfl
  | cast i =>
    simp only [homMap, Fin.lastCases_castSucc]
    apply EqualityTransport.identity_retarget (C := C) (A :=
      coherentSimplex.{u} ⦋n + 1⦌) (.mk (ULift.up.{u}
      i.castSucc) : coherentSimplex.{u} ⦋n + 1⦌)
      (object_front x y i).symm
    ext q p
    rfl

/-- The constructed whole Hom maps preserve actual original union composition at every
triple of original vertices. -/
theorem homMap_comp (a b c : Fin (n + 2)) :
    eComp SSet.{u} (SimplicialThickening.mk (ULift.up.{u} a))
      (SimplicialThickening.mk (ULift.up.{u} b)) (SimplicialThickening.mk (ULift.up.{u} c))
        ≫ homMap x y family a c =
      (homMap x y family a b ⊗ₘ homMap x y family b c) ≫
        eComp SSet.{u} (object x y a) (object x y b)
        (object x y c) := by
  cases a using Fin.lastCases with
  | last =>
    cases b using Fin.lastCases with
    | last =>
      cases c using Fin.lastCases with
      | last =>
        simp only [homMap, Fin.lastCases_last]
        apply EqualityTransport.composition_retarget (C := C) (A := coherentSimplex.{u} ⦋n + 1⦌)
          (.mk (ULift.up.{u} (Fin.last (n + 1))) : coherentSimplex.{u} ⦋n + 1⦌)
          (SimplicialThickening.mk (ULift.up (Fin.last (n + 1)))) (SimplicialThickening.mk (ULift.up
            (Fin.last (n + 1))))
          (object_last x y).symm (object_last x y).symm (object_last x y).symm
        apply SSet.hom_ext
        intro q
        apply ConcreteCategory.hom_ext
        rintro ⟨p, r⟩
        change (eId SSet.{u} y).app q PUnit.unit =
          (eComp SSet.{u} y y y).app q ((eId SSet.{u} y).app q PUnit.unit,
            (eId SSet.{u} y).app q PUnit.unit)
        exact congr($(e_id_comp SSet.{u} y y).app q ((eId SSet.{u} y).app q PUnit.unit)).symm
      | cast k =>
        apply SSet.hom_ext
        intro q
        apply ConcreteCategory.hom_ext
        rintro ⟨p, r⟩
        exact False.elim ((not_le.mpr (Fin.castSucc_lt_last k))
          (show Fin.last (n + 1) ≤ k.castSucc from HomUnitsAndEmpty.source_order
            (a := ULift.up.{u} (Fin.last (n + 1))) (b := ULift.up.{u} k.castSucc) r))
    | cast j =>
      apply SSet.hom_ext
      intro q
      apply ConcreteCategory.hom_ext
      rintro ⟨p, r⟩
      exact False.elim ((not_le.mpr (Fin.castSucc_lt_last j))
        (show Fin.last (n + 1) ≤ j.castSucc from HomUnitsAndEmpty.source_order
          (a := ULift.up.{u} (Fin.last (n + 1))) (b := ULift.up.{u} j.castSucc) p))
  | cast i =>
    cases b using Fin.lastCases with
    | last =>
      cases c using Fin.lastCases with
      | last =>
        exact @SingletonHomUnits.right_comp (coherentSimplex.{u} ⦋n + 1⦌) C
          (.mk (ULift.up i.castSucc)) (.mk (ULift.up (Fin.last (n + 1))))
          (object x y i.castSucc) (object x y (Fin.last (n + 1)))
          (HomUnitsAndEmpty.unit_isIso (ULift.up.{u} (Fin.last (n + 1))))
          (homMap x y family (Fin.last (n + 1)) (Fin.last (n + 1)))
          (homMap x y family i.castSucc (Fin.last (n + 1))) (homMap_id x y family (Fin.last
            (n + 1)))
      | cast k =>
        apply SSet.hom_ext
        intro q
        apply ConcreteCategory.hom_ext
        rintro ⟨p, r⟩
        exact False.elim ((not_le.mpr (Fin.castSucc_lt_last k))
          (show Fin.last (n + 1) ≤ k.castSucc from HomUnitsAndEmpty.source_order
            (a := ULift.up.{u} (Fin.last (n + 1))) (b := ULift.up.{u} k.castSucc) r))
    | cast j =>
      cases c using Fin.lastCases with
      | last =>
        simp only [homMap, Fin.lastCases_castSucc, Fin.lastCases_last]
        apply EqualityTransport.composition_retarget (C := C) (A := coherentSimplex.{u} ⦋n + 1⦌)
          (.mk (ULift.up.{u} i.castSucc) : coherentSimplex.{u} ⦋n + 1⦌)
          (SimplicialThickening.mk (ULift.up j.castSucc)) (SimplicialThickening.mk (ULift.up
            (Fin.last (n + 1))))
          (object_front x y i).symm (object_front x y j).symm (object_last x y).symm
        apply SSet.hom_ext
        intro q
        apply ConcreteCategory.hom_ext
        rintro ⟨p, r⟩
        change (family.map i).app q (p.prod' r ⋙ SimplicialThickening.compFunctor _ _ _) =
          (eComp SSet.{u} x x y).app q ((eId SSet.{u} x).app q PUnit.unit, (family.map j).app q r)
        have h := family.map_comp i j q p r
        exact h.trans (congr($(e_id_comp SSet.{u} x y).app q ((family.map j).app q r))).symm
      | cast k =>
        simp only [homMap, Fin.lastCases_castSucc]
        apply EqualityTransport.composition_retarget (C := C) (A := coherentSimplex.{u} ⦋n + 1⦌)
          (.mk (ULift.up.{u} i.castSucc) : coherentSimplex.{u} ⦋n + 1⦌)
          (SimplicialThickening.mk (ULift.up j.castSucc)) (SimplicialThickening.mk (ULift.up
            k.castSucc))
          (object_front x y i).symm (object_front x y j).symm (object_front x y k).symm
        apply SSet.hom_ext
        intro q
        apply ConcreteCategory.hom_ext
        rintro ⟨p, r⟩
        change (eId SSet.{u} x).app q PUnit.unit =
          (eComp SSet.{u} x x x).app q ((eId SSet.{u} x).app q PUnit.unit,
            (eId SSet.{u} x).app q PUnit.unit)
        exact congr($(e_id_comp SSet.{u} x x).app q ((eId SSet.{u} x).app q PUnit.unit)).symm

/-- The actual enriched coherent simplex, with the original supplied source and target and
every whole Hom map. -/
def simplex : coherentSimplex.{u} ⦋n + 1⦌ ⟶ C where
  obj a := object x y a.as.down
  map a b := homMap x y family a.as.down b.as.down
  map_id a := homMap_id x y family a.as.down
  map_comp a b c := homMap_comp x y family a.as.down b.as.down c.as.down

/-- Every front object is the supplied individual original source. -/
theorem simplex_front (i : Fin (n + 1)) : (simplex x y family).obj (.mk (ULift.up
  i.castSucc)) = x := by
  simp only [simplex, object_front]

/-- The actual last object is the supplied individual original target. -/
theorem simplex_last : (simplex x y family).obj (.mk (ULift.up (Fin.last (n + 1)))) = y := by
  simp only [simplex, object_last]

end CategoryTheory.CoherentRealization.HomFrontFamily
