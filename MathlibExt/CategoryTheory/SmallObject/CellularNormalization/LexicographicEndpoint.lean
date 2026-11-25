/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.LexicographicDiagram

/-!
# The original endpoint is a colimit of the whole lexicographic diagram

Use the unchanged inner and outer colimits to construct every descent map,
every leg equation and uniqueness at the literal original endpoint.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w w'

namespace CategoryTheory.SmallObject.CellularNormalization

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [LinearOrder J] [SuccOrder J]
variable {K : J → Type w'} [∀ j, LinearOrder (K j)] [∀ j, SuccOrder (K j)]
  [∀ j, OrderBot (K j)] [∀ j, WellFoundedLT (K j)]
variable (F : J ⥤ C)
variable (c : ∀ j, TransfiniteCompositionOfShape (K j)
  (F.map (homOfLE (Order.le_succ j))))

variable {Y : C} (ι : F ⟶ (Functor.const J).obj Y)

/-- A cocone leg typed at the literal original inner object. -/
def coconeLeg (s : Cocone (diagram F c)) (j : J) (k : K j) : (c j).F.obj k ⟶ s.pt :=
  s.ι.app (vertex j k)

@[reassoc]
theorem coconeLeg_inner (s : Cocone (diagram F c)) (j : J) {k l : K j} (h : k ≤ l) :
    (c j).F.map (homOfLE h) ≫ coconeLeg F c s j l = coconeLeg F c s j k := by
  have hs := s.ι.naturality (homOfLE (show vertex j k ≤ vertex j l from Sigma.Lex.right k l h))
  change indexMap F c (vertex j k) (vertex j l) (Sigma.Lex.right k l h) ≫ coconeLeg F c s j l =
    coconeLeg F c s j k ≫ 𝟙 _ at hs
  rw [indexMap_inner, Category.comp_id] at hs
  exact hs

@[reassoc]
theorem coconeLeg_cross (s : Cocone (diagram F c)) {i j : J} (h : i < j)
    (k : K i) (l : K j) :
    crossMap F c h k l ≫ coconeLeg F c s j l = coconeLeg F c s i k := by
  have hs := s.ι.naturality (homOfLE (show vertex i k ≤ vertex j l from Sigma.Lex.left k l h))
  change indexMap F c (vertex i k) (vertex j l) _ ≫ coconeLeg F c s j l =
    coconeLeg F c s i k ≫ 𝟙 _ at hs
  rw [indexMap_cross F c h, Category.comp_id] at hs
  exact hs

/-- Restrict any flattened cocone to one actual original inner block. -/
def blockCocone (s : Cocone (diagram F c)) (j : J) : Cocone (c j).F where
  pt := s.pt
  ι :=
    { app k := coconeLeg F c s j k
      naturality k l f := by
        have h := coconeLeg_inner F c s j (leOfHom f)
        have e : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
        rw [e] at h
        simpa using h }

/-- The original inner colimit constructs the endpoint map of every block. -/
noncomputable def blockDesc (s : Cocone (diagram F c)) (j : J) :
    F.obj (Order.succ j) ⟶ s.pt :=
  (c j).isColimit.desc (blockCocone F c s j)

@[reassoc]
theorem blockDesc_fac (s : Cocone (diagram F c)) (j : J) (k : K j) :
    (c j).incl.app k ≫ blockDesc F c s j = coconeLeg F c s j k :=
  (c j).isColimit.fac (blockCocone F c s j) k

/-- The map at an original outer vertex is obtained from its unchanged inner root. -/
def outerLeg (s : Cocone (diagram F c)) (j : J) : F.obj j ⟶ s.pt :=
  (c j).isoBot.inv ≫ coconeLeg F c s j ⊥

@[reassoc]
theorem innerRoot_outerLeg (s : Cocone (diagram F c)) (j : J) (k : K j) :
    innerRoot F c j k ≫ coconeLeg F c s j k = outerLeg F c s j := by
  change ((c j).isoBot.inv ≫ (c j).F.map (homOfLE bot_le)) ≫
    coconeLeg F c s j k = (c j).isoBot.inv ≫ coconeLeg F c s j ⊥
  rw [Category.assoc, coconeLeg_inner]

@[reassoc]
theorem blockDesc_outerLeg (s : Cocone (diagram F c)) (j : J) :
    F.map (homOfLE (Order.le_succ j)) ≫ blockDesc F c s j = outerLeg F c s j := by
  rw [← innerRoot_endpoint F c j (⊥ : K j), Category.assoc, blockDesc_fac,
    innerRoot_outerLeg]

@[reassoc]
theorem cross_outerLeg (s : Cocone (diagram F c)) {i j : J} (h : i < j)
    (k : K i) :
    (c i).incl.app k ≫ F.map (homOfLE (Order.succ_le_of_lt h)) ≫
      outerLeg F c s j = coconeLeg F c s i k := by
  simpa [crossMap, innerRoot, outerLeg, Category.assoc] using
    coconeLeg_cross F c s h k (⊥ : K j)

@[reassoc]
theorem blockDesc_transition (s : Cocone (diagram F c)) {i j : J} (h : i < j) :
    F.map (homOfLE (Order.succ_le_of_lt h)) ≫ outerLeg F c s j = blockDesc F c s i := by
  apply (c i).isColimit.hom_ext
  intro k
  exact (cross_outerLeg F c s h k).trans (blockDesc_fac F c s i k).symm

@[reassoc]
theorem outerLeg_naturality (s : Cocone (diagram F c)) {i j : J} (h : i ≤ j) :
    F.map (homOfLE h) ≫ outerLeg F c s j = outerLeg F c s i := by
  obtain rfl | hij := h.eq_or_lt
  · simp
  · rw [← blockDesc_outerLeg F c s i, ← blockDesc_transition F c s hij]
    rw [← Functor.map_comp_assoc]
    rfl

@[reassoc]
theorem outerLeg_eq (s : Cocone (diagram F c)) {i j : J} (e : i = j) :
    F.map (eqToHom e) ≫ outerLeg F c s j = outerLeg F c s i := by
  subst j
  simp

/-- Every flattened cocone induces a cocone on the unchanged whole outer diagram. -/
def outerCocone (s : Cocone (diagram F c)) : Cocone F where
  pt := s.pt
  ι :=
    { app j := outerLeg F c s j
      naturality i j f := by
        have h := outerLeg_naturality F c s (leOfHom f)
        have e : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
        rw [e] at h
        simpa using h }

@[reassoc]
theorem outerLeg_succ (s : Cocone (diagram F c)) (j : J) :
    outerLeg F c s (Order.succ j) = blockDesc F c s j := by
  by_cases hj : IsMax j
  · have he : Order.succ j = j := hj.succ_eq
    have hw := outerLeg_eq F c s he
    calc
      outerLeg F c s (Order.succ j) = F.map (eqToHom he) ≫ outerLeg F c s j := hw.symm
      _ = F.map (eqToHom he) ≫
          (F.map (homOfLE (Order.le_succ j)) ≫ blockDesc F c s j) :=
        congrArg (fun t => F.map (eqToHom he) ≫ t) (blockDesc_outerLeg F c s j).symm
      _ = blockDesc F c s j := by
        rw [← F.map_comp_assoc]
        have e : eqToHom he ≫ homOfLE (Order.le_succ j) = 𝟙 (Order.succ j) := Subsingleton.elim _ _
        rw [e, F.map_id, Category.id_comp]
  · have h := blockDesc_transition F c s (Order.lt_succ_iff_not_isMax.mpr hj)
    have e : homOfLE (Order.succ_le_of_lt (Order.lt_succ_iff_not_isMax.mpr hj)) =
        𝟙 (Order.succ j) := Subsingleton.elim _ _
    rw [e, F.map_id, Category.id_comp] at h
    exact h

/-- The actual original outer colimit descent, with its point typed literally. -/
noncomputable def endpointDesc (hι : IsColimit (Cocone.mk Y ι))
    (s : Cocone (diagram F c)) : Y ⟶ s.pt :=
  hι.desc (outerCocone F c s)

@[reassoc]
theorem endpointDesc_fac (hι : IsColimit (Cocone.mk Y ι))
    (s : Cocone (diagram F c)) (j : J) :
    ι.app j ≫ endpointDesc F c ι hι s = outerLeg F c s j :=
  hι.fac (outerCocone F c s) j

/-- The original outer colimit constructs the flattened descent map. -/
noncomputable def endpointIsColimit (hι : IsColimit (Cocone.mk Y ι)) :
    IsColimit (Cocone.mk Y (endpoint F c ι)) where
  desc s := endpointDesc F c ι hι s
  fac s a := by
    rcases a with ⟨j, k⟩
    change ((c j).incl.app k ≫ ι.app (Order.succ j)) ≫
      endpointDesc F c ι hι s = coconeLeg F c s j k
    calc
      ((c j).incl.app k ≫ ι.app (Order.succ j)) ≫ endpointDesc F c ι hι s =
          (c j).incl.app k ≫ outerLeg F c s (Order.succ j) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun t => (c j).incl.app k ≫ t) (endpointDesc_fac F c ι hι s (Order.succ j)))
      _ = (c j).incl.app k ≫ blockDesc F c s j :=
        congrArg (fun t => (c j).incl.app k ≫ t) (outerLeg_succ F c s j)
      _ = coconeLeg F c s j k := blockDesc_fac F c s j k
  uniq s m hm := by
    apply hι.hom_ext
    intro j
    change ι.app j ≫ m = ι.app j ≫ endpointDesc F c ι hι s
    have hm' : (endpoint F c ι).app (vertex j ⊥) ≫ m = coconeLeg F c s j ⊥ :=
      hm (vertex j ⊥)
    calc
      ι.app j ≫ m = (innerRoot F c j ⊥ ≫ (endpoint F c ι).app (vertex j ⊥)) ≫ m :=
        congrArg (fun t => t ≫ m) (innerRoot_endpoint_leg F c ι j ⊥).symm
      _ = innerRoot F c j ⊥ ≫ coconeLeg F c s j ⊥ :=
        (Category.assoc _ _ _).trans
          (congrArg (fun t => innerRoot F c j ⊥ ≫ t) hm')
      _ = outerLeg F c s j := innerRoot_outerLeg F c s j ⊥
      _ = ι.app j ≫ endpointDesc F c ι hι s := (endpointDesc_fac F c ι hι s j).symm

end CategoryTheory.SmallObject.CellularNormalization
