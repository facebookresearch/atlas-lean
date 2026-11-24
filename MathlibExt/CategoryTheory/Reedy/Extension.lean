/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Reedy.Boundary

public import Mathlib.CategoryTheory.Whiskering

/-!
# Extending original Reedy diagrams across a source degree

The original category, degree, boundary maps and coefficient factories are retained.
Only the actual latching and matching shape (co)limits used by these constructions
are required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uJ vJ uD uC vC uB vB uS vS uK vK

section ReedyPart1

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]

variable [∀ j, HasLimitsOfShape (r.Matching j) C]

/-- The original lower matching universal maps form the whole actual latching cocone. -/
abbrev lowerBoundaryCocone {d : D} (P : r.Below d ⥤ C) (j : J) (hj : r.degree j = d) :
    Cocone (r.lowerLatchingDiagram P j hj) where
  pt := limit (r.lowerMatchingDiagram P j hj)
  ι.app a := limit.lift _ (r.lowerBoundaryCone P j hj a)
  ι.naturality a c f := by
    change P.map ((r.latchingBelow j hj).map f) ≫
        limit.lift _ (r.lowerBoundaryCone P j hj c) =
      limit.lift _ (r.lowerBoundaryCone P j hj a) ≫ 𝟙 _
    rw [Category.comp_id]
    apply limit.hom_ext
    intro b
    rw [Category.assoc, limit.lift_π, limit.lift_π]
    change P.map ((r.latchingBelow j hj).map f) ≫
        P.map (r.lowerBoundaryArrow j hj c b) = P.map (r.lowerBoundaryArrow j hj a b)
    rw [← P.map_comp]
    congr 1
    apply ObjectProperty.hom_ext
    change r.latchingComparison f ≫ (r.latchingArrow c ≫ r.matchingArrow b) =
      r.latchingArrow a ≫ r.matchingArrow b
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun h ↦ h ≫ r.matchingArrow b) (r.latchingComparison_arrow f))

variable [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The actual full lower latching-to-matching map on the original shapes. -/
def lowerBoundaryMap {d : D} (P : r.Below d ⥤ C) (j : J) (hj : r.degree j = d) :
    colimit (r.lowerLatchingDiagram P j hj) ⟶ limit (r.lowerMatchingDiagram P j hj) :=
  colimit.desc _ (lowerBoundaryCocone r P j hj)

/-- Every actual incoming/outgoing boundary composite is the original lower diagram map. -/
@[reassoc]
theorem lowerBoundaryMap_ι_π {d : D} (P : r.Below d ⥤ C) (j : J) (hj : r.degree j = d)
    (a : r.Latching j) (b : r.Matching j) :
    colimit.ι (r.lowerLatchingDiagram P j hj) a ≫ lowerBoundaryMap r P j hj ≫
      limit.π (r.lowerMatchingDiagram P j hj) b = P.map (r.lowerBoundaryArrow j hj a b) := by
  rw [lowerBoundaryMap, colimit.ι_desc_assoc, limit.lift_π]

/-- Actual lower diagrams and new-degree factor maps on precisely the original boundaries. -/
structure LayerData (d : D) where
  /-- The supplied diagram on the full subcategory of objects whose degrees are below `d`. -/
  lower : r.Below d ⥤ C
  /-- The new diagram value at each object of degree exactly `d`. -/
  obj (j : J) (hj : r.degree j = d) : C
  /-- The map from the lower latching colimit into the new object at degree `d`. -/
  incoming (j : J) (hj : r.degree j = d) :
    colimit (r.lowerLatchingDiagram lower j hj) ⟶ obj j hj
  /-- The map from the new object at degree `d` into the lower matching limit. -/
  outgoing (j : J) (hj : r.degree j = d) :
    obj j hj ⟶ limit (r.lowerMatchingDiagram lower j hj)
  fac (j : J) (hj : r.degree j = d) :
    incoming j hj ≫ outgoing j hj = lowerBoundaryMap r lower j hj

end CategoryTheory.ReedyStructure

end ReedyPart1

section ReedyPart2

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure.LayerData

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] {r : ReedyStructure J D}
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  {d : D} (a : LayerData (C := C) r d)

/-- The actual extended original object, selected only by its original degree. -/
def extendedObj (j : r.Through d) : C := by
  classical
  exact if h : r.degree j.obj < d then a.lower.obj ⟨j.obj, h⟩
    else a.obj j.obj (le_antisymm j.property (le_of_not_gt h))

/-- An original smaller object retains the supplied lower coefficient value. -/
theorem extendedObj_old (j : r.Through d) (hj : r.degree j.obj < d) :
    a.extendedObj j = a.lower.obj ⟨j.obj, hj⟩ := by
  rw [extendedObj, dite_eq_left hj]

/-- An original object of the new degree retains the supplied new coefficient value. -/
theorem extendedObj_new (j : r.Through d) (hj : r.degree j.obj = d) :
    a.extendedObj j = a.obj j.obj hj := by
  have h : ¬ r.degree j.obj < d := by rw [hj]; exact lt_irrefl d
  rw [extendedObj, dite_eq_right h]

/-- The actual identity transport to the supplied lower coefficient. -/
def oldIso (j : r.Through d) (hj : r.degree j.obj < d) :
    a.extendedObj j ≅ a.lower.obj ⟨j.obj, hj⟩ := eqToIso (a.extendedObj_old j hj)

/-- The actual identity transport to the supplied new coefficient. -/
def newIso (j : r.Through d) (hj : r.degree j.obj = d) :
    a.extendedObj j ≅ a.obj j.obj hj := eqToIso (a.extendedObj_new j hj)

/-- The original lower-source map, with only the exact object equality transports. -/
def oldMap {i j : r.Through d} (f : i ⟶ j) (hi : r.degree i.obj < d) (hj : r.degree j.obj < d) :
    a.extendedObj i ⟶ a.extendedObj j :=
  (a.oldIso i hi).hom ≫ a.lower.map (ObjectProperty.homMk f.hom) ≫ (a.oldIso j hj).inv


/-- The original latching injection has its precise supplied lower coefficient as its source. -/
def incomingInjection {i j : r.Through d} (f : i ⟶ j) (hf : r.direct f.hom)
    (hi : r.degree i.obj < d) (hj : r.degree j.obj = d) :
    a.lower.obj ⟨i.obj, hi⟩ ⟶ colimit (r.lowerLatchingDiagram a.lower j.obj hj) :=
  colimit.ι (r.lowerLatchingDiagram a.lower j.obj hj) (r.latchingMk f.hom hf (hi.trans_eq hj.symm))

/-- The original matching projection has its precise supplied lower coefficient as its target. -/
def outgoingProjection {i j : r.Through d} (f : i ⟶ j) (hf : r.inverse f.hom)
    (hi : r.degree i.obj = d) (hj : r.degree j.obj < d) :
    limit (r.lowerMatchingDiagram a.lower i.obj hi) ⟶ a.lower.obj ⟨j.obj, hj⟩ :=
  limit.π (r.lowerMatchingDiagram a.lower i.obj hi) (r.matchingMk f.hom hf (hj.trans_eq hi.symm))

/-- The incoming original direct map through its original latching injection. -/
def incomingMap {i j : r.Through d} (f : i ⟶ j) (hf : r.direct f.hom)
    (hi : r.degree i.obj < d) (hj : r.degree j.obj = d) : a.extendedObj i ⟶ a.extendedObj j :=
  (a.oldIso i hi).hom ≫
    a.incomingInjection f hf hi hj ≫
    a.incoming j.obj hj ≫ (a.newIso j hj).inv

/-- The outgoing original inverse map through its original matching projection. -/
def outgoingMap {i j : r.Through d} (f : i ⟶ j) (hf : r.inverse f.hom)
    (hi : r.degree i.obj = d) (hj : r.degree j.obj < d) : a.extendedObj i ⟶ a.extendedObj j :=
  (a.newIso i hi).hom ≫ a.outgoing i.obj hi ≫
    a.outgoingProjection f hf hi hj ≫
    (a.oldIso j hj).inv

/-- The actual direct source map at an arbitrary pair of objects of the degree truncation. -/
def directMap {i j : r.Through d} (f : i ⟶ j) (hf : r.direct f.hom) :
    a.extendedObj i ⟶ a.extendedObj j := by
  classical
  exact if hj : r.degree j.obj < d then
    a.oldMap f ((r.direct_le f.hom hf).trans_lt hj) hj
  else if hi : r.degree i.obj < d then
    a.incomingMap f hf hi (le_antisymm j.property (le_of_not_gt hj))
  else
    let hi' : r.degree i.obj = d := le_antisymm i.property (le_of_not_gt hi)
    let hj' : r.degree j.obj = d := le_antisymm j.property (le_of_not_gt hj)
    let e := ((r.throughStructure d).direct_equal f hf (hi'.trans hj'.symm)).choose
    eqToHom (congrArg a.extendedObj e)

/-- The actual inverse source map at an arbitrary pair of objects of the degree truncation. -/
def inverseMap {i j : r.Through d} (f : i ⟶ j) (hf : r.inverse f.hom) :
    a.extendedObj i ⟶ a.extendedObj j := by
  classical
  exact if hi : r.degree i.obj < d then
    a.oldMap f hi ((r.inverse_le f.hom hf).trans_lt hi)
  else if hj : r.degree j.obj < d then
    a.outgoingMap f hf (le_antisymm i.property (le_of_not_gt hi)) hj
  else
    let hi' : r.degree i.obj = d := le_antisymm i.property (le_of_not_gt hi)
    let hj' : r.degree j.obj = d := le_antisymm j.property (le_of_not_gt hj)
    let e := ((r.throughStructure d).inverse_equal f hf (hi'.trans hj'.symm)).choose
    eqToHom (congrArg a.extendedObj e)

/-- Every original direct map whose target is smaller is the same original lower-source map. -/
theorem directMap_old {i j : r.Through d} (f : i ⟶ j) (hf : r.direct f.hom)
    (hj : r.degree j.obj < d) :
    a.directMap f hf = a.oldMap f ((r.direct_le f.hom hf).trans_lt hj) hj := by
  rw [directMap, dite_eq_left hj]

/-- Every original inverse map whose source is smaller is the same original lower-source map. -/
theorem inverseMap_old {i j : r.Through d} (f : i ⟶ j) (hf : r.inverse f.hom)
    (hi : r.degree i.obj < d) :
    a.inverseMap f hf = a.oldMap f hi ((r.inverse_le f.hom hf).trans_lt hi) := by
  rw [inverseMap, dite_eq_left hi]

/-- Every incoming original direct map retains its original latching injection and new factor
map. -/
theorem directMap_incoming {i j : r.Through d} (f : i ⟶ j) (hf : r.direct f.hom)
    (hi : r.degree i.obj < d) (hj : r.degree j.obj = d) :
    a.directMap f hf = a.incomingMap f hf hi hj := by
  have hj' : ¬ r.degree j.obj < d := by rw [hj]; exact lt_irrefl d
  rw [directMap, dite_eq_right hj', dite_eq_left hi]

/-- Every outgoing original inverse map retains its new factor map and original matching
projection. -/
theorem inverseMap_outgoing {i j : r.Through d} (f : i ⟶ j) (hf : r.inverse f.hom)
    (hi : r.degree i.obj = d) (hj : r.degree j.obj < d) :
    a.inverseMap f hf = a.outgoingMap f hf hi hj := by
  have hi' : ¬ r.degree i.obj < d := by rw [hi]; exact lt_irrefl d
  rw [inverseMap, dite_eq_right hi', dite_eq_left hj]

/-- The transported original lower identity is the original extended identity. -/
theorem oldMap_id (i : r.Through d) (hi : r.degree i.obj < d) :
    a.oldMap (𝟙 i) hi hi = 𝟙 (a.extendedObj i) := by
  have hid : (ObjectProperty.homMk (𝟙 i.obj) :
      (⟨i.obj, hi⟩ : r.Below d) ⟶ ⟨i.obj, hi⟩) = 𝟙 _ := rfl
  rw [oldMap, ObjectProperty.FullSubcategory.id_hom, hid, a.lower.map_id,
    Category.id_comp, Iso.hom_inv_id]

/-- Every direct original identity is retained by the extension. -/
theorem directMap_id (i : r.Through d) (hf : r.direct (𝟙 i.obj)) :
    a.directMap (𝟙 i) hf = 𝟙 (a.extendedObj i) := by
  classical
  by_cases h : r.degree i.obj < d
  · rw [directMap, dite_eq_left h]
    exact a.oldMap_id i h
  · rw [directMap, dite_eq_right h, dite_eq_right h]
    exact eqToHom_refl (a.extendedObj i) _

/-- Every inverse original identity is retained by the extension. -/
theorem inverseMap_id (i : r.Through d) (hf : r.inverse (𝟙 i.obj)) :
    a.inverseMap (𝟙 i) hf = 𝟙 (a.extendedObj i) := by
  classical
  by_cases h : r.degree i.obj < d
  · rw [inverseMap, dite_eq_left h]
    exact a.oldMap_id i h
  · rw [inverseMap, dite_eq_right h, dite_eq_right h]
    exact eqToHom_refl (a.extendedObj i) _

/-- Every original composite between smaller objects retains its original lower-source map. -/
theorem oldMap_comp {i j k : r.Through d} (f : i ⟶ j) (g : j ⟶ k)
    (hi : r.degree i.obj < d) (hj : r.degree j.obj < d) (hk : r.degree k.obj < d) :
    a.oldMap (f ≫ g) hi hk = a.oldMap f hi hj ≫ a.oldMap g hj hk := by
  dsimp only [oldMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← a.lower.map_comp_assoc]
  rfl


/-- An original lower direct composite retains exactly the original latching comparison triangle. -/
theorem oldMap_incoming {i j k : r.Through d} (f : i ⟶ j) (g : j ⟶ k)
    (hf : r.direct f.hom) (hg : r.direct g.hom)
    (hi : r.degree i.obj < d) (hj : r.degree j.obj < d) (hk : r.degree k.obj = d) :
    a.oldMap f hi hj ≫ a.incomingMap g hg hj hk =
      a.incomingMap (f ≫ g) (r.direct.comp_mem _ _ hf hg) hi hk := by
  let af := r.latchingMk (f ≫ g).hom (r.direct.comp_mem _ _ hf hg) (hi.trans_eq hk.symm)
  let ag := r.latchingMk g.hom hg (hj.trans_eq hk.symm)
  let τ : af ⟶ ag := ObjectProperty.homMk (Over.homMk ⟨f.hom, hf⟩ rfl)
  have ht : a.lower.map (ObjectProperty.homMk f.hom :
      (⟨i.obj, hi⟩ : r.Below d) ⟶ ⟨j.obj, hj⟩) ≫
      a.incomingInjection g hg hj hk =
      a.incomingInjection (f ≫ g) (r.direct.comp_mem _ _ hf hg) hi hk :=
    colimit.w (r.lowerLatchingDiagram a.lower k.obj hk) τ
  dsimp only [oldMap, incomingMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using
    congrArg (fun h => (a.oldIso i hi).hom ≫ h ≫ a.incoming k.obj hk ≫ (a.newIso k hk).inv) ht

/-- An original lower inverse composite retains exactly the original matching comparison
triangle. -/
theorem outgoingMap_old {i j k : r.Through d} (f : i ⟶ j) (g : j ⟶ k)
    (hf : r.inverse f.hom) (hg : r.inverse g.hom)
    (hi : r.degree i.obj = d) (hj : r.degree j.obj < d) (hk : r.degree k.obj < d) :
    a.outgoingMap f hf hi hj ≫ a.oldMap g hj hk =
      a.outgoingMap (f ≫ g) (r.inverse.comp_mem _ _ hf hg) hi hk := by
  let af := r.matchingMk f.hom hf (hj.trans_eq hi.symm)
  let ag := r.matchingMk (f ≫ g).hom (r.inverse.comp_mem _ _ hf hg) (hk.trans_eq hi.symm)
  let τ : af ⟶ ag := ObjectProperty.homMk (Under.homMk ⟨g.hom, hg⟩ rfl)
  have ht : a.outgoingProjection f hf hi hj ≫
      a.lower.map (ObjectProperty.homMk g.hom :
        (⟨j.obj, hj⟩ : r.Below d) ⟶ ⟨k.obj, hk⟩) =
      a.outgoingProjection (f ≫ g) (r.inverse.comp_mem _ _ hf hg) hi hk :=
        limit.w (r.lowerMatchingDiagram a.lower i.obj
        hi) τ
  dsimp only [outgoingMap, oldMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using
    congrArg (fun h => (a.newIso i hi).hom ≫ a.outgoing i.obj hi ≫ h ≫ (a.oldIso k hk).inv) ht

/-- The actual extended direct maps preserve all original direct composites. -/
theorem directMap_comp {i j k : r.Through d} (f : i ⟶ j) (g : j ⟶ k)
    (hf : r.direct f.hom) (hg : r.direct g.hom) :
    a.directMap (f ≫ g) (r.direct.comp_mem _ _ hf hg) = a.directMap f hf ≫ a.directMap g hg := by
  classical
  by_cases hk : r.degree k.obj < d
  · have hj : r.degree j.obj < d := (r.direct_le g.hom hg).trans_lt hk
    have hi : r.degree i.obj < d := (r.direct_le f.hom hf).trans_lt hj
    rw [a.directMap_old _ _ hk, a.directMap_old _ hf hj, a.directMap_old _ hg hk]
    exact a.oldMap_comp f g hi hj hk
  · have hk' : r.degree k.obj = d := le_antisymm k.property (le_of_not_gt hk)
    by_cases hj : r.degree j.obj < d
    · have hi : r.degree i.obj < d := (r.direct_le f.hom hf).trans_lt hj
      rw [a.directMap_incoming _ _ hi hk', a.directMap_old _ hf hj,
        a.directMap_incoming _ hg hj hk']
      exact (a.oldMap_incoming f g hf hg hi hj hk').symm
    · have hj' : r.degree j.obj = d := le_antisymm j.property (le_of_not_gt hj)
      obtain ⟨e, he⟩ := (r.throughStructure d).direct_equal g hg (hj'.trans hk'.symm)
      cases e
      have he' : g = 𝟙 j := by simpa only [eqToHom_refl] using he
      cases he'
      simp only [Category.comp_id, a.directMap_id]

/-- The actual extended inverse maps preserve all original inverse composites. -/
theorem inverseMap_comp {i j k : r.Through d} (f : i ⟶ j) (g : j ⟶ k)
    (hf : r.inverse f.hom) (hg : r.inverse g.hom) :
    a.inverseMap (f ≫ g) (r.inverse.comp_mem _ _ hf hg) =
      a.inverseMap f hf ≫ a.inverseMap g hg := by
  classical
  by_cases hi : r.degree i.obj < d
  · have hj : r.degree j.obj < d := (r.inverse_le f.hom hf).trans_lt hi
    have hk : r.degree k.obj < d := (r.inverse_le g.hom hg).trans_lt hj
    rw [a.inverseMap_old _ _ hi, a.inverseMap_old _ hf hi, a.inverseMap_old _ hg hj]
    exact a.oldMap_comp f g hi hj hk
  · have hi' : r.degree i.obj = d := le_antisymm i.property (le_of_not_gt hi)
    by_cases hj : r.degree j.obj < d
    · have hk : r.degree k.obj < d := (r.inverse_le g.hom hg).trans_lt hj
      rw [a.inverseMap_outgoing _ _ hi' hk, a.inverseMap_outgoing _ hf hi' hj,
        a.inverseMap_old _ hg hj]
      exact (a.outgoingMap_old f g hf hg hi' hj hk).symm
    · have hj' : r.degree j.obj = d := le_antisymm j.property (le_of_not_gt hj)
      obtain ⟨e, he⟩ := (r.throughStructure d).inverse_equal f hf (hi'.trans hj'.symm)
      cases e
      have he' : f = 𝟙 i := by simpa only [eqToHom_refl] using he
      cases he'
      simp only [Category.id_comp, a.inverseMap_id]


theorem direct_mem_original {i j : r.Through d} (f : i ⟶ j)
    (hf : (r.throughStructure d).direct f) : r.direct f.hom := hf

theorem inverse_mem_original {i j : r.Through d} (f : i ⟶ j)
    (hf : (r.throughStructure d).inverse f) : r.inverse f.hom := hf

/-- The evaluation of an original complete inverse--direct factor record in the actual extension. -/
def evaluateFactor {i j : r.Through d} {f : i ⟶ j}
    (h : ReedyFactorization (r.throughStructure d).direct (r.throughStructure d).inverse f) :
    a.extendedObj i ⟶ a.extendedObj j :=
  a.inverseMap h.inverseMap (inverse_mem_original h.inverseMap h.inverse_mem) ≫
    a.directMap h.directMap (direct_mem_original h.directMap h.direct_mem)

/-- The actual extended value of the original canonical factor record. -/
def factorValue {i j : r.Through d} (f : i ⟶ j) : a.extendedObj i ⟶ a.extendedObj j :=
  a.evaluateFactor ((r.throughStructure d).factor f)

/-- Every canonical factor between smaller objects retains the same original lower-source map. -/
theorem factorValue_old {i j : r.Through d} (f : i ⟶ j)
    (hi : r.degree i.obj < d) (hj : r.degree j.obj < d) : a.factorValue f = a.oldMap f hi hj := by
  let h := (r.throughStructure d).factor f
  have hm : r.degree h.middle.obj < d := ((r.throughStructure d).middle_le_source f).trans_lt hi
  change a.inverseMap h.inverseMap (inverse_mem_original h.inverseMap h.inverse_mem) ≫
    a.directMap h.directMap (direct_mem_original h.directMap h.direct_mem) = _
  rw [a.inverseMap_old _ _ hi, a.directMap_old _ _ hj, ← a.oldMap_comp _ _ hi hm hj, h.fac]

/-- Canonical factor evaluation of an original inverse arrow is the same actual extended inverse
map. -/
theorem factorValue_inverse {i j : r.Through d} (f : i ⟶ j) (hf : r.inverse f.hom) :
    a.factorValue f = a.inverseMap f hf := by
  let h : ReedyFactorization (r.throughStructure d).direct (r.throughStructure d).inverse f :=
    ReedyFactorization.mk j f (𝟙 j) hf ((r.throughStructure d).direct.id_mem j) (Category.comp_id f)
  have he := congrArg a.evaluateFactor ((r.throughStructure d).factor_unique f
    ((r.throughStructure d).factor f) h)
  rw [factorValue, he]
  change a.inverseMap f hf ≫ a.directMap (𝟙 j) _ = _
  rw [a.directMap_id, Category.comp_id]

/-- Canonical factor evaluation of an original direct arrow is the same actual extended direct
map. -/
theorem factorValue_direct {i j : r.Through d} (f : i ⟶ j) (hf : r.direct f.hom) :
    a.factorValue f = a.directMap f hf := by
  let h : ReedyFactorization (r.throughStructure d).direct (r.throughStructure d).inverse f :=
    ReedyFactorization.mk i (𝟙 i) f ((r.throughStructure d).inverse.id_mem i) hf
      (Category.id_comp f)
  have he := congrArg a.evaluateFactor ((r.throughStructure d).factor_unique f
    ((r.throughStructure d).factor f) h)
  rw [factorValue, he]
  change a.inverseMap (𝟙 i) _ ≫ a.directMap f hf = _
  rw [a.inverseMap_id, Category.id_comp]

attribute [reassoc] LayerData.fac

/-- The original incoming and outgoing maps agree on their complete original composite through
the new object. -/
theorem incomingMap_outgoingMap {i j k : r.Through d} (f : i ⟶ j) (g : j ⟶ k)
    (hf : r.direct f.hom) (hg : r.inverse g.hom)
    (hi : r.degree i.obj < d) (hj : r.degree j.obj = d) (hk : r.degree k.obj < d) :
    a.incomingMap f hf hi hj ≫ a.outgoingMap g hg hj hk = a.oldMap (f ≫ g) hi hk := by
  let af := r.latchingMk f.hom hf (hi.trans_eq hj.symm)
  let ag := r.matchingMk g.hom hg (hk.trans_eq hj.symm)
  have hb : a.incomingInjection f hf hi hj ≫
      a.incoming j.obj hj ≫ a.outgoing j.obj hj ≫ a.outgoingProjection g hg hj hk =
      a.lower.map (ObjectProperty.homMk (f ≫ g).hom :
        (⟨i.obj, hi⟩ : r.Below d) ⟶ ⟨k.obj, hk⟩) := by
    have ht := lowerBoundaryMap_ι_π r a.lower j.obj hj af ag
    change a.incomingInjection f hf hi hj ≫ lowerBoundaryMap r a.lower j.obj hj ≫
      a.outgoingProjection g hg hj hk = a.lower.map
        (ObjectProperty.homMk (f ≫ g).hom : (⟨i.obj, hi⟩ : r.Below d) ⟶ ⟨k.obj, hk⟩) at ht
    rw [a.fac_assoc]
    exact ht
  dsimp only [incomingMap, outgoingMap, oldMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using
    congrArg (fun h => (a.oldIso i hi).hom ≫ h ≫ (a.oldIso k hk).inv) hb

/-- Every original direct/inverse mixed composite has its exact original canonical factor
evaluation. -/
theorem interchange {i j k : r.Through d} (f : i ⟶ j) (g : j ⟶ k)
    (hf : r.direct f.hom) (hg : r.inverse g.hom) :
    a.directMap f hf ≫ a.inverseMap g hg = a.factorValue (f ≫ g) := by
  classical
  by_cases hj : r.degree j.obj < d
  · have hi : r.degree i.obj < d := (r.direct_le f.hom hf).trans_lt hj
    have hk : r.degree k.obj < d := (r.inverse_le g.hom hg).trans_lt hj
    rw [a.directMap_old _ hf hj, a.inverseMap_old _ hg hj, a.factorValue_old _ hi hk]
    exact (a.oldMap_comp f g hi hj hk).symm
  · have hj' : r.degree j.obj = d := le_antisymm j.property (le_of_not_gt hj)
    by_cases hi : r.degree i.obj < d
    · by_cases hk : r.degree k.obj < d
      · rw [a.directMap_incoming _ hf hi hj', a.inverseMap_outgoing _ hg hj' hk,
          a.factorValue_old _ hi hk]
        exact a.incomingMap_outgoingMap f g hf hg hi hj' hk
      · have hk' : r.degree k.obj = d := le_antisymm k.property (le_of_not_gt hk)
        obtain ⟨e, he⟩ := (r.throughStructure d).inverse_equal g hg (hj'.trans hk'.symm)
        cases e
        have he' : g = 𝟙 j := by simpa only [eqToHom_refl] using he
        cases he'
        simp only [Category.comp_id, a.inverseMap_id, a.factorValue_direct _ hf]
    · have hi' : r.degree i.obj = d := le_antisymm i.property (le_of_not_gt hi)
      obtain ⟨e, he⟩ := (r.throughStructure d).direct_equal f hf (hi'.trans hj'.symm)
      cases e
      have he' : f = 𝟙 i := by simpa only [eqToHom_refl] using he
      cases he'
      simp only [Category.id_comp, a.directMap_id, a.factorValue_inverse _ hg]

/-- The actual lower diagram and latching/matching factor maps form complete original
direct/inverse functor data. -/
def normalData : NormalFunctorData (r.throughStructure d) C where
  obj := a.extendedObj
  directMap f hf := a.directMap f (direct_mem_original f hf)
  inverseMap f hf := a.inverseMap f (inverse_mem_original f hf)
  direct_id i := a.directMap_id i _
  inverse_id i := a.inverseMap_id i _
  direct_comp f g hf hg := a.directMap_comp f g hf hg
  inverse_comp f g hf hg := a.inverseMap_comp f g hf hg
  interchange f g hf hg := a.interchange f g hf hg

/-- The actual full original degree-truncation diagram, constructed from the supplied boundary
factor maps. -/
def extension : r.Through d ⥤ C := a.normalData.toFunctor

/-- The full extension retains each supplied original lower object value. -/
theorem extension_obj_old (j : r.Through d) (hj : r.degree j.obj < d) :
    a.extension.obj j = a.lower.obj ⟨j.obj, hj⟩ := a.extendedObj_old j hj

/-- The full extension retains each supplied original new object value. -/
theorem extension_obj_new (j : r.Through d) (hj : r.degree j.obj = d) :
    a.extension.obj j = a.obj j.obj hj := a.extendedObj_new j hj

/-- Every original direct source map is retained in the actual full extension. -/
theorem extension_direct {i j : r.Through d} (f : i ⟶ j) (hf : r.direct f.hom) :
    a.extension.map f = a.directMap f hf := a.normalData.toFunctor_direct f hf

/-- Every original inverse source map is retained in the actual full extension. -/
theorem extension_inverse {i j : r.Through d} (f : i ⟶ j) (hf : r.inverse f.hom) :
    a.extension.map f = a.inverseMap f hf := a.normalData.toFunctor_inverse f hf

/-- Every original full lower-source map is retained with its exact original coefficient
equality transports. -/
theorem extension_map_old {i j : r.Through d} (f : i ⟶ j)
    (hi : r.degree i.obj < d) (hj : r.degree j.obj < d) :
    a.extension.map f = a.oldMap f hi hj := a.factorValue_old f hi hj

end CategoryTheory.ReedyStructure.LayerData

end ReedyPart2

section ReedyPart3

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] {r : ReedyStructure J D}
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  {d : D} (a b : LayerData (C := C) r d)

/-- The original lower transformation and new-degree maps with both actual boundary
compatibilities. -/
structure LayerHom where
  /-- The natural transformation between the supplied diagrams below degree `d`. -/
  lower : a.lower ⟶ b.lower
  /-- The component from `a.obj j hj` to `b.obj j hj` on the new degree layer. -/
  app (j : J) (hj : r.degree j = d) : a.obj j hj ⟶ b.obj j hj
  incoming (j : J) (hj : r.degree j = d) :
    a.incoming j hj ≫ app j hj =
      colimMap (Functor.whiskerLeft (r.latchingBelow j hj) lower) ≫ b.incoming j hj
  outgoing (j : J) (hj : r.degree j = d) :
    app j hj ≫ b.outgoing j hj =
      a.outgoing j hj ≫ limMap (Functor.whiskerLeft (r.matchingBelow j hj) lower)

attribute [reassoc] LayerHom.incoming LayerHom.outgoing

namespace LayerHom

variable {a b} (h : LayerHom a b)

/-- The full actual coefficient transformation through the supplied object equality transports. -/
def extendedApp (j : r.Through d) : a.extendedObj j ⟶ b.extendedObj j := by
  classical
  exact if hj : r.degree j.obj < d then
    (a.oldIso j hj).hom ≫ h.lower.app ⟨j.obj, hj⟩ ≫ (b.oldIso j hj).inv
  else
    let hj' := le_antisymm j.property (le_of_not_gt hj)
    (a.newIso j hj').hom ≫ h.app j.obj hj' ≫ (b.newIso j hj').inv

/-- Every smaller original coefficient map retains the supplied lower transformation. -/
theorem extendedApp_old (j : r.Through d) (hj : r.degree j.obj < d) :
    h.extendedApp j = (a.oldIso j hj).hom ≫ h.lower.app ⟨j.obj, hj⟩ ≫ (b.oldIso j hj).inv := by
  rw [extendedApp, dite_eq_left hj]

/-- Every new-degree original coefficient map retains the supplied new transformation. -/
theorem extendedApp_new (j : r.Through d) (hj : r.degree j.obj = d) :
    h.extendedApp j = (a.newIso j hj).hom ≫ h.app j.obj hj ≫ (b.newIso j hj).inv := by
  have hj' : ¬ r.degree j.obj < d := by rw [hj]; exact lt_irrefl d
  rw [extendedApp, dite_eq_right hj']

/-- The full lower latching comparison retains every original incoming injection. -/
@[reassoc]
theorem injection_naturality {i j : r.Through d} (f : i ⟶ j) (hf : r.direct f.hom)
    (hi : r.degree i.obj < d) (hj : r.degree j.obj = d) :
    a.incomingInjection f hf hi hj ≫
      colimMap (Functor.whiskerLeft (r.latchingBelow j.obj hj) h.lower) =
      h.lower.app ⟨i.obj, hi⟩ ≫ b.incomingInjection f hf hi hj :=
  ι_colimMap _ (r.latchingMk f.hom hf (hi.trans_eq hj.symm))

/-- The full lower matching comparison retains every original outgoing projection. -/
@[reassoc]
theorem projection_naturality {i j : r.Through d} (f : i ⟶ j) (hf : r.inverse f.hom)
    (hi : r.degree i.obj = d) (hj : r.degree j.obj < d) :
    limMap (Functor.whiskerLeft (r.matchingBelow i.obj hi) h.lower) ≫
      b.outgoingProjection f hf hi hj =
      a.outgoingProjection f hf hi hj ≫ h.lower.app ⟨j.obj, hj⟩ :=
  limMap_π _ (r.matchingMk f.hom hf (hj.trans_eq hi.symm))

/-- Every original lower-source map commutes with the actual extended coefficient transformation. -/
theorem old_naturality {i j : r.Through d} (f : i ⟶ j)
    (hi : r.degree i.obj < d) (hj : r.degree j.obj < d) :
    a.oldMap f hi hj ≫ h.extendedApp j = h.extendedApp i ≫ b.oldMap f hi hj := by
  have ht := h.lower.naturality (ObjectProperty.homMk f.hom :
    (⟨i.obj, hi⟩ : r.Below d) ⟶ ⟨j.obj, hj⟩)
  rw [h.extendedApp_old _ hj, h.extendedApp_old _ hi]
  dsimp only [LayerData.oldMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using
    congrArg (fun g => (a.oldIso i hi).hom ≫ g ≫ (b.oldIso j hj).inv) ht

/-- Every original incoming direct arrow commutes with the actual new-degree transformation. -/
theorem incoming_naturality {i j : r.Through d} (f : i ⟶ j) (hf : r.direct f.hom)
    (hi : r.degree i.obj < d) (hj : r.degree j.obj = d) :
    a.incomingMap f hf hi hj ≫ h.extendedApp j = h.extendedApp i ≫ b.incomingMap f hf hi hj := by
  have ht : a.incomingInjection f hf hi hj ≫ a.incoming j.obj hj ≫ h.app j.obj hj =
      h.lower.app ⟨i.obj, hi⟩ ≫ b.incomingInjection f hf hi hj ≫ b.incoming j.obj hj := by
    rw [h.incoming, h.injection_naturality_assoc]
  rw [h.extendedApp_new _ hj, h.extendedApp_old _ hi]
  dsimp only [LayerData.incomingMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using
    congrArg (fun g => (a.oldIso i hi).hom ≫ g ≫ (b.newIso j hj).inv) ht

/-- Every original outgoing inverse arrow commutes with the actual new-degree transformation. -/
theorem outgoing_naturality {i j : r.Through d} (f : i ⟶ j) (hf : r.inverse f.hom)
    (hi : r.degree i.obj = d) (hj : r.degree j.obj < d) :
    a.outgoingMap f hf hi hj ≫ h.extendedApp j = h.extendedApp i ≫ b.outgoingMap f hf hi hj := by
  have ht : a.outgoing i.obj hi ≫ a.outgoingProjection f hf hi hj ≫ h.lower.app ⟨j.obj, hj⟩ =
      h.app i.obj hi ≫ b.outgoing i.obj hi ≫ b.outgoingProjection f hf hi hj := by
    rw [h.outgoing_assoc, h.projection_naturality]
  rw [h.extendedApp_old _ hj, h.extendedApp_new _ hi]
  dsimp only [LayerData.outgoingMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using
    congrArg (fun g => (a.newIso i hi).hom ≫ g ≫ (b.oldIso j hj).inv) ht

/-- The actual extended maps are natural on every original direct source arrow. -/
theorem direct_naturality {i j : r.Through d} (f : i ⟶ j) (hf : r.direct f.hom) :
    a.directMap f hf ≫ h.extendedApp j = h.extendedApp i ≫ b.directMap f hf := by
  classical
  by_cases hj : r.degree j.obj < d
  · have hi : r.degree i.obj < d := (r.direct_le f.hom hf).trans_lt hj
    rw [a.directMap_old _ hf hj, b.directMap_old _ hf hj]
    exact h.old_naturality f hi hj
  · have hj' : r.degree j.obj = d := le_antisymm j.property (le_of_not_gt hj)
    by_cases hi : r.degree i.obj < d
    · rw [a.directMap_incoming _ hf hi hj', b.directMap_incoming _ hf hi hj']
      exact h.incoming_naturality f hf hi hj'
    · have hi' : r.degree i.obj = d := le_antisymm i.property (le_of_not_gt hi)
      obtain ⟨e, he⟩ := (r.throughStructure d).direct_equal f hf (hi'.trans hj'.symm)
      cases e
      have he' : f = 𝟙 i := by simpa only [eqToHom_refl] using he
      cases he'
      simp only [a.directMap_id, b.directMap_id, Category.id_comp, Category.comp_id]

/-- The actual extended maps are natural on every original inverse source arrow. -/
theorem inverse_naturality {i j : r.Through d} (f : i ⟶ j) (hf : r.inverse f.hom) :
    a.inverseMap f hf ≫ h.extendedApp j = h.extendedApp i ≫ b.inverseMap f hf := by
  classical
  by_cases hi : r.degree i.obj < d
  · have hj : r.degree j.obj < d := (r.inverse_le f.hom hf).trans_lt hi
    rw [a.inverseMap_old _ hf hi, b.inverseMap_old _ hf hi]
    exact h.old_naturality f hi hj
  · have hi' : r.degree i.obj = d := le_antisymm i.property (le_of_not_gt hi)
    by_cases hj : r.degree j.obj < d
    · rw [a.inverseMap_outgoing _ hf hi' hj, b.inverseMap_outgoing _ hf hi' hj]
      exact h.outgoing_naturality f hf hi' hj
    · have hj' : r.degree j.obj = d := le_antisymm j.property (le_of_not_gt hj)
      obtain ⟨e, he⟩ := (r.throughStructure d).inverse_equal f hf (hi'.trans hj'.symm)
      cases e
      have he' : f = 𝟙 i := by simpa only [eqToHom_refl] using he
      cases he'
      simp only [a.inverseMap_id, b.inverseMap_id, Category.id_comp, Category.comp_id]

/-- The actual lower and new-degree maps assemble to an ordinary natural transformation of the
full extensions. -/
def transformation : a.extension ⟶ b.extension where
  app := h.extendedApp
  naturality _ _ f := (r.throughStructure d).naturality_of_direct_inverse
    (X := a.extension) (Y := b.extension)
    h.extendedApp
    (fun {_ _} g hg => by
      have hg' := LayerData.direct_mem_original g hg
      rw [a.extension_direct _ hg', b.extension_direct _ hg']
      exact h.direct_naturality g hg')
    (fun {_ _} g hg => by
      have hg' := LayerData.inverse_mem_original g hg
      rw [a.extension_inverse _ hg', b.extension_inverse _ hg']
      exact h.inverse_naturality g hg') f

/-- The full transformation retains every original lower coefficient map and its equality
transports. -/
theorem transformation_app_old (j : r.Through d) (hj : r.degree j.obj < d) :
    h.transformation.app j = (a.oldIso j hj).hom ≫ h.lower.app ⟨j.obj, hj⟩ ≫ (b.oldIso j hj).inv :=
  h.extendedApp_old j hj

/-- The full transformation retains every original new-degree coefficient map and its equality
transports. -/
theorem transformation_app_new (j : r.Through d) (hj : r.degree j.obj = d) :
    h.transformation.app j = (a.newIso j hj).hom ≫ h.app j.obj hj ≫ (b.newIso j hj).inv :=
  h.extendedApp_new j hj

end LayerHom

end CategoryTheory.ReedyStructure

end ReedyPart3

section ReedyPart4

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The lower boundary map of an original diagram is its unchanged latching-to-matching
composite. -/
theorem lowerBoundaryMap_restrict (X : J ⥤ C) {d : D} (j : J) (hj : r.degree j = d) :
    lowerBoundaryMap r (r.restrictBelow X d) j hj = latchingMap r X j ≫ matchingMap r X j := by
  apply colimit.hom_ext
  intro a
  apply limit.hom_ext
  intro b
  simp only [Category.assoc]
  rw [lowerBoundaryMap_ι_π r]
  change X.map (r.latchingArrow a ≫ r.matchingArrow b) =
    colimit.ι (r.latchingDiagram X j) a ≫ latchingMap r X j ≫ matchingMap r X j ≫
      limit.π (r.matchingDiagram X j) b
  rw [latchingMap_ι_assoc r, matchingMap_π r]
  exact X.map_comp (r.latchingArrow a) (r.matchingArrow b)

/-- The full original caller diagram provides its actual layer object values and both unchanged
boundary maps. -/
abbrev layerOfFunctor (X : J ⥤ C) (d : D) : LayerData (C := C) r d where
  lower := r.restrictBelow X d
  obj j _ := X.obj j
  incoming j _ := latchingMap r X j
  outgoing j _ := matchingMap r X j
  fac j hj := (lowerBoundaryMap_restrict r X j hj).symm

/-- Every original lower object of the caller layer is its unchanged original coefficient. -/
theorem layerOfFunctor_obj (X : J ⥤ C) (d : D) (j : r.Through d) :
    (layerOfFunctor r X d).extendedObj j = X.obj j.obj := by
  by_cases h : r.degree j.obj < d
  · exact (layerOfFunctor r X d).extendedObj_old j h
  · exact (layerOfFunctor r X d).extendedObj_new j (le_antisymm j.property (le_of_not_gt h))

/-- The complete caller layer keeps the identity transport to its unchanged original coefficient. -/
def layerOfFunctorObjIso (X : J ⥤ C) (d : D) (j : r.Through d) :
    (layerOfFunctor r X d).extendedObj j ≅ X.obj j.obj := eqToIso (layerOfFunctor_obj r X d j)

/-- The caller layer's lower transport is the same original coefficient equality transport. -/
theorem layerOfFunctor_oldIso (X : J ⥤ C) (d : D) (j : r.Through d) (hj : r.degree j.obj < d) :
    (layerOfFunctor r X d).oldIso j hj = layerOfFunctorObjIso r X d j := rfl

/-- The caller layer's new transport is the same original coefficient equality transport. -/
theorem layerOfFunctor_newIso (X : J ⥤ C) (d : D) (j : r.Through d) (hj : r.degree j.obj = d) :
    (layerOfFunctor r X d).newIso j hj = layerOfFunctorObjIso r X d j := rfl


/-- The caller layer injection followed by its latching map is the same original direct
coefficient arrow. -/
@[reassoc]
theorem layerOfFunctor_incoming (X : J ⥤ C) (d : D) {i j : r.Through d} (f : i ⟶ j)
    (hf : r.direct f.hom) (hi : r.degree i.obj < d) (hj : r.degree j.obj = d) :
    (layerOfFunctor r X d).incomingInjection f hf hi hj ≫ latchingMap r X j.obj = X.map f.hom := by
  let af := r.latchingMk f.hom hf (hi.trans_eq hj.symm)
  change colimit.ι (r.latchingDiagram X j.obj) af ≫ latchingMap r X j.obj =
    X.map (r.latchingArrow af)
  exact latchingMap_ι r X j.obj af

/-- The caller layer matching map followed by its projection is the same original inverse
coefficient arrow. -/
@[reassoc]
theorem layerOfFunctor_outgoing (X : J ⥤ C) (d : D) {i j : r.Through d} (f : i ⟶ j)
    (hf : r.inverse f.hom) (hi : r.degree i.obj = d) (hj : r.degree j.obj < d) :
    matchingMap r X i.obj ≫ (layerOfFunctor r X d).outgoingProjection f hf hi hj = X.map f.hom := by
  let af := r.matchingMk f.hom hf (hj.trans_eq hi.symm)
  change matchingMap r X i.obj ≫ limit.π (r.matchingDiagram X i.obj) af = X.map (r.matchingArrow af)
  exact matchingMap_π r X i.obj af

/-- Every original direct arrow commutes with the identity transports of the reconstructed
caller layer. -/
theorem layerOfFunctor_direct (X : J ⥤ C) (d : D) {i j : r.Through d} (f : i ⟶ j)
    (hf : r.direct f.hom) :
    (layerOfFunctor r X d).directMap f hf ≫ (layerOfFunctorObjIso r X d j).hom =
      (layerOfFunctorObjIso r X d i).hom ≫ X.map f.hom := by
  classical
  by_cases hj : r.degree j.obj < d
  · have hi : r.degree i.obj < d := (r.direct_le f.hom hf).trans_lt hj
    rw [(layerOfFunctor r X d).directMap_old _ hf hj]
    dsimp only [LayerData.oldMap]
    rw [layerOfFunctor_oldIso r X d i hi, layerOfFunctor_oldIso r X d j hj]
    simp only [Category.assoc]
    change (layerOfFunctorObjIso r X d i).hom ≫ X.map f.hom ≫
      (layerOfFunctorObjIso r X d j).inv ≫ (layerOfFunctorObjIso r X d j).hom = _
    simp only [Iso.inv_hom_id, Category.comp_id]
  · have hj' : r.degree j.obj = d := le_antisymm j.property (le_of_not_gt hj)
    by_cases hi : r.degree i.obj < d
    · rw [(layerOfFunctor r X d).directMap_incoming _ hf hi hj']
      dsimp only [LayerData.incomingMap]
      rw [layerOfFunctor_oldIso r X d i hi, layerOfFunctor_newIso r X d j hj']
      simp only [Category.assoc]
      change (layerOfFunctorObjIso r X d i).hom ≫
        (layerOfFunctor r X d).incomingInjection f hf hi hj' ≫ latchingMap r X j.obj ≫
          (layerOfFunctorObjIso r X d j).inv ≫ (layerOfFunctorObjIso r X d j).hom = _
      rw [Iso.inv_hom_id, Category.comp_id, layerOfFunctor_incoming r]
    · have hi' : r.degree i.obj = d := le_antisymm i.property (le_of_not_gt hi)
      obtain ⟨e, he⟩ := (r.throughStructure d).direct_equal f hf (hi'.trans hj'.symm)
      cases e
      have he' : f = 𝟙 i := by simpa only [eqToHom_refl] using he
      cases he'
      simp only [LayerData.directMap_id, ObjectProperty.FullSubcategory.id_hom,
        Functor.map_id, Category.id_comp, Category.comp_id]

/-- Every original inverse arrow commutes with the identity transports of the reconstructed
caller layer. -/
theorem layerOfFunctor_inverse (X : J ⥤ C) (d : D) {i j : r.Through d} (f : i ⟶ j)
    (hf : r.inverse f.hom) :
    (layerOfFunctor r X d).inverseMap f hf ≫ (layerOfFunctorObjIso r X d j).hom =
      (layerOfFunctorObjIso r X d i).hom ≫ X.map f.hom := by
  classical
  by_cases hi : r.degree i.obj < d
  · have hj : r.degree j.obj < d := (r.inverse_le f.hom hf).trans_lt hi
    rw [(layerOfFunctor r X d).inverseMap_old _ hf hi]
    dsimp only [LayerData.oldMap]
    rw [layerOfFunctor_oldIso r X d i hi, layerOfFunctor_oldIso r X d j hj]
    simp only [Category.assoc]
    change (layerOfFunctorObjIso r X d i).hom ≫ X.map f.hom ≫
      (layerOfFunctorObjIso r X d j).inv ≫ (layerOfFunctorObjIso r X d j).hom = _
    simp only [Iso.inv_hom_id, Category.comp_id]
  · have hi' : r.degree i.obj = d := le_antisymm i.property (le_of_not_gt hi)
    by_cases hj : r.degree j.obj < d
    · rw [(layerOfFunctor r X d).inverseMap_outgoing _ hf hi' hj]
      dsimp only [LayerData.outgoingMap]
      rw [layerOfFunctor_newIso r X d i hi', layerOfFunctor_oldIso r X d j hj]
      simp only [Category.assoc]
      change (layerOfFunctorObjIso r X d i).hom ≫ matchingMap r X i.obj ≫
        (layerOfFunctor r X d).outgoingProjection f hf hi' hj ≫
          (layerOfFunctorObjIso r X d j).inv ≫ (layerOfFunctorObjIso r X d j).hom = _
      rw [Iso.inv_hom_id, Category.comp_id, layerOfFunctor_outgoing r]
    · have hj' : r.degree j.obj = d := le_antisymm j.property (le_of_not_gt hj)
      obtain ⟨e, he⟩ := (r.throughStructure d).inverse_equal f hf (hi'.trans hj'.symm)
      cases e
      have he' : f = 𝟙 i := by simpa only [eqToHom_refl] using he
      cases he'
      simp only [LayerData.inverseMap_id, ObjectProperty.FullSubcategory.id_hom,
        Functor.map_id, Category.id_comp, Category.comp_id]

/-- The actual reconstructed caller layer is naturally the same original full degree restriction. -/
def layerOfFunctorIso (X : J ⥤ C) (d : D) :
    (layerOfFunctor r X d).extension ≅ r.restrictThrough X d :=
  NatIso.ofComponents (fun j => layerOfFunctorObjIso r X d j) (fun f =>
    (r.throughStructure d).naturality_of_direct_inverse
      (X := (layerOfFunctor r X d).extension) (Y := r.restrictThrough X d)
      (fun j => (layerOfFunctorObjIso r X d j).hom)
      (fun {_ _} g hg => by
        have hg' := LayerData.direct_mem_original g hg
        rw [(layerOfFunctor r X d).extension_direct _ hg']
        exact layerOfFunctor_direct r X d g hg')
      (fun {_ _} g hg => by
        have hg' := LayerData.inverse_mem_original g hg
        rw [(layerOfFunctor r X d).extension_inverse _ hg']
        exact layerOfFunctor_inverse r X d g hg') f)

/-- The caller reconstruction comparison retains each original coefficient equality transport. -/
theorem layerOfFunctorIso_hom_app (X : J ⥤ C) (d : D) (j : r.Through d) :
    (layerOfFunctorIso r X d).hom.app j = (layerOfFunctorObjIso r X d j).hom := rfl

/-- The inverse caller reconstruction comparison retains each original coefficient equality
transport. -/
theorem layerOfFunctorIso_inv_app (X : J ⥤ C) (d : D) (j : r.Through d) :
    (layerOfFunctorIso r X d).inv.app j = (layerOfFunctorObjIso r X d j).inv := rfl

end CategoryTheory.ReedyStructure

end ReedyPart4

section ReedyPart5

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)
  {C : Type uC} [Category.{vC} C] {d : D}

section Latching

variable [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The complete original lower latching functor retains its actual source inclusion. -/
abbrev lowerLatchingFunctor (j : J) (hj : r.degree j = d) : (r.Below d ⥤ C) ⥤ C :=
  (Functor.whiskeringLeft (r.Latching j) (r.Below d) C).obj (r.latchingBelow j hj) ⋙ colim

/-- Every lower latching functor map is the actual original colimit comparison. -/
theorem lowerLatchingFunctor_map {P Q : r.Below d ⥤ C} (f : P ⟶ Q) (j : J) (hj : r.degree j = d) :
    (lowerLatchingFunctor r (C := C) j hj).map f =
      colimMap (Functor.whiskerLeft (r.latchingBelow j hj) f) := rfl

end Latching

section Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C]

/-- The complete original lower matching functor retains its actual source inclusion. -/
abbrev lowerMatchingFunctor (j : J) (hj : r.degree j = d) : (r.Below d ⥤ C) ⥤ C :=
  (Functor.whiskeringLeft (r.Matching j) (r.Below d) C).obj (r.matchingBelow j hj) ⋙ lim

/-- Every lower matching functor map is the actual original limit comparison. -/
theorem lowerMatchingFunctor_map {P Q : r.Below d ⥤ C} (f : P ⟶ Q) (j : J) (hj : r.degree j = d) :
    (lowerMatchingFunctor r (C := C) j hj).map f =
      limMap (Functor.whiskerLeft (r.matchingBelow j hj) f) := rfl

end Matching

variable [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]

/-- The full actual lower latching-to-matching boundary is natural on all original lower source
maps. -/
theorem lowerBoundaryMap_naturality {P Q : r.Below d ⥤ C} (f : P ⟶ Q)
    (j : J) (hj : r.degree j = d) :
    (lowerLatchingFunctor r (C := C) j hj).map f ≫ lowerBoundaryMap r Q j hj =
      lowerBoundaryMap r P j hj ≫ (lowerMatchingFunctor r (C := C) j hj).map f := by
  change colimMap (Functor.whiskerLeft (r.latchingBelow j hj) f) ≫ lowerBoundaryMap r Q j hj =
    lowerBoundaryMap r P j hj ≫ limMap (Functor.whiskerLeft (r.matchingBelow j hj) f)
  apply colimit.hom_ext
  intro a
  apply limit.hom_ext
  intro b
  simp only [Category.assoc,
    ι_colimMap_assoc, limMap_π, lowerBoundaryMap_ι_π, lowerBoundaryMap_ι_π_assoc]
  exact (f.naturality (r.lowerBoundaryArrow j hj a b)).symm

end CategoryTheory.ReedyStructure

end ReedyPart5

section ReedyPart6

open CategoryTheory Limits

namespace CategoryTheory.ReedyStructure

variable {J : Type uJ} [Category.{vJ} J]
  {D : Type uD} [LinearOrder D] [WellFoundedLT D] (r : ReedyStructure J D)

namespace LayerData

variable {r} {C : Type uC} [Category.{vC} C]
  [∀ j, HasLimitsOfShape (r.Matching j) C]
  [∀ j, HasColimitsOfShape (r.Latching j) C]
  {d : D} (a : LayerData (C := C) r d)

/-- Every original lower source arrow commutes with the actual lower coefficient comparison. -/
theorem lowerIso_naturality {i j : r.Below d} (f : i ⟶ j) :
    a.extension.map ((r.belowThrough d).map f) ≫
      (a.oldIso ((r.belowThrough d).obj j) j.property).hom =
      (a.oldIso ((r.belowThrough d).obj i) i.property).hom ≫ a.lower.map f := by
  rw [a.extension_map_old _ i.property j.property]
  change ((a.oldIso ((r.belowThrough d).obj i) i.property).hom ≫ a.lower.map f ≫
    (a.oldIso ((r.belowThrough d).obj j) j.property).inv) ≫
      (a.oldIso ((r.belowThrough d).obj j) j.property).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The full actual smaller-degree restriction is naturally the supplied original lower diagram. -/
def lowerIso : r.belowThrough d ⋙ a.extension ≅ a.lower :=
  NatIso.ofComponents (fun j => a.oldIso ((r.belowThrough d).obj j) j.property)
    (fun f => a.lowerIso_naturality f)

/-- Each original lower coefficient retains its exact original object equality transport. -/
theorem lowerIso_hom_app (j : r.Below d) :
    a.lowerIso.hom.app j = (a.oldIso ((r.belowThrough d).obj j) j.property).hom := rfl

/-- Each inverse lower comparison retains its exact original object equality transport. -/
theorem lowerIso_inv_app (j : r.Below d) :
    a.lowerIso.inv.app j = (a.oldIso ((r.belowThrough d).obj j) j.property).inv := rfl

end LayerData

end CategoryTheory.ReedyStructure

end ReedyPart6
