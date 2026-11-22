/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.NaturalTransformationCorner
public import MathlibExt.AlgebraicTopology.ModelCategory.HCofibrationGluing
public import MathlibExt.AlgebraicTopology.ModelCategory.HCofibrationFilteredColimits

/-!
Actual weak pushout corners under source composition and cobase change.

All maps are the original domain maps of the natural-transformation corner
functor. The two mapped source legs remain genuine h-cofibrations. No weakness
of an individual natural-transformation component is assumed.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty HomotopicalAlgebra

namespace HomotopicalAlgebra.NaturalTransformationCorner

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [HasPushouts C] {P Q : D ⥤ C} (α : P ⟶ Q)

theorem inl_corner_mk {A B : D} (i : A ⟶ B) :
    pushout.inl (α.app A) (P.map i) ≫ corner α (Arrow.mk i) = Q.map i := by
  simpa only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom] using inl_corner α (Arrow.mk i)

theorem inr_corner_mk {A B : D} (i : A ⟶ B) :
    pushout.inr (α.app A) (P.map i) ≫ corner α (Arrow.mk i) = α.app B := by
  simpa only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom] using inr_corner α (Arrow.mk i)

theorem domainMap_inl_mk {A B A' B' : D} {i : A ⟶ B} {j : A' ⟶ B'}
    (f : Arrow.mk i ⟶ Arrow.mk j) :
    pushout.inl (α.app A) (P.map i) ≫ domainMap α f =
      Q.map f.left ≫ pushout.inl (α.app A') (P.map j) := by
  simpa only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom] using domainMap_inl α f

theorem domainMap_inr_mk {A B A' B' : D} {i : A ⟶ B} {j : A' ⟶ B'}
    (f : Arrow.mk i ⟶ Arrow.mk j) :
    pushout.inr (α.app A) (P.map i) ≫ domainMap α f =
      P.map f.right ≫ pushout.inr (α.app A') (P.map j) := by
  simpa only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom] using domainMap_inr α f

/-- The original cobase-change square is the complete source Arrow map. -/
def cobaseArrow {A B A' B' : D} {i : A ⟶ B} {u : A ⟶ A'}
    {v : B ⟶ B'} {j : A' ⟶ B'} (sq : IsPushout i u v j) :
    Arrow.mk i ⟶ Arrow.mk j := Arrow.homMk u v sq.w.symm

/-- The new domain corner is the actual pushout of the old domain corner. -/
theorem domain_cobase_pushout [PreservesColimitsOfShape WalkingSpan P]
    {A B A' B' : D} {i : A ⟶ B} {u : A ⟶ A'}
    {v : B ⟶ B'} {j : A' ⟶ B'} (sq : IsPushout i u v j) :
    IsPushout (pushout.inl (α.app A) (P.map i)) (Q.map u)
      (domainMap α (cobaseArrow sq)) (pushout.inl (α.app A') (P.map j)) := by
  have outer : IsPushout (P.map i) (α.app A ≫ Q.map u)
      (pushout.inr (α.app A) (P.map i) ≫ domainMap α (cobaseArrow sq))
      (pushout.inl (α.app A') (P.map j)) := by
    rw [domainMap_inr_mk α (cobaseArrow sq)]
    change IsPushout (P.map i) (α.app A ≫ Q.map u)
      (P.map v ≫ pushout.inr (α.app A') (P.map j))
      (pushout.inl (α.app A') (P.map j))
    rw [← α.naturality u]
    exact (sq.map P).paste_vert (IsPushout.of_hasPushout (α.app A') (P.map j)).flip
  exact IsPushout.of_top outer (domainMap_inl_mk α (cobaseArrow sq))
    (IsPushout.of_hasPushout (α.app A) (P.map i)).flip

/-- The original prefix Arrow extends the source map by its actual following map. -/
def prefixArrow {A B E : D} (i : A ⟶ B) (j : B ⟶ E) :
    Arrow.mk i ⟶ Arrow.mk (i ≫ j) := Arrow.homMk (𝟙 A) j (by simp)

/-- The original suffix Arrow uses the first source map and the actual target identity. -/
def suffixArrow {A B E : D} (i : A ⟶ B) (j : B ⟶ E) :
    Arrow.mk (i ≫ j) ⟶ Arrow.mk j := Arrow.homMk i (𝟙 E) (by simp)

/-- Extending the source map gives the actual cobase change of the following P-map. -/
theorem domain_composition_pushout {A B E : D} (i : A ⟶ B) (j : B ⟶ E) :
    IsPushout (pushout.inr (α.app A) (P.map i)) (P.map j)
      (domainMap α (prefixArrow i j))
      (pushout.inr (α.app A) (P.map (i ≫ j))) := by
  have outer : IsPushout (α.app A) (P.map i ≫ P.map j)
      (pushout.inl (α.app A) (P.map i) ≫ domainMap α (prefixArrow i j))
      (pushout.inr (α.app A) (P.map (i ≫ j))) := by
    rw [domainMap_inl_mk α (prefixArrow i j)]
    change IsPushout (α.app A) (P.map i ≫ P.map j)
      (Q.map (𝟙 A) ≫ pushout.inl (α.app A) (P.map (i ≫ j)))
      (pushout.inr (α.app A) (P.map (i ≫ j)))
    rw [Q.map_id, Category.id_comp, ← P.map_comp]
    exact IsPushout.of_hasPushout _ _
  exact IsPushout.of_top outer (domainMap_inr_mk α (prefixArrow i j))
    (IsPushout.of_hasPushout (α.app A) (P.map i))

/-- The actual two domain maps paste to the first corner followed by the original inclusion. -/
theorem domain_composition_square {A B E : D} (i : A ⟶ B) (j : B ⟶ E) :
    domainMap α (prefixArrow i j) ≫ domainMap α (suffixArrow i j) =
      corner α (Arrow.mk i) ≫ pushout.inl (α.app B) (P.map j) := by
  apply pushout.hom_ext
  · simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom]
    rw [← Category.assoc, domainMap_inl_mk α (prefixArrow i j)]
    change (Q.map (𝟙 A) ≫ pushout.inl (α.app A) (P.map (i ≫ j))) ≫
        domainMap α (suffixArrow i j) = _
    rw [Q.map_id, Category.id_comp, domainMap_inl_mk α (suffixArrow i j)]
    change Q.map i ≫ pushout.inl (α.app B) (P.map j) =
      pushout.inl (α.app A) (P.map i) ≫ corner α (Arrow.mk i) ≫
        pushout.inl (α.app B) (P.map j)
    rw [← Category.assoc, inl_corner_mk α i]
  · simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom]
    rw [← Category.assoc, domainMap_inr_mk α (prefixArrow i j)]
    change (P.map j ≫ pushout.inr (α.app A) (P.map (i ≫ j))) ≫
        domainMap α (suffixArrow i j) = _
    rw [Category.assoc, domainMap_inr_mk α (suffixArrow i j)]
    change P.map j ≫ (P.map (𝟙 E) ≫ pushout.inr (α.app B) (P.map j)) = _
    rw [P.map_id, Category.id_comp]
    change P.map j ≫ pushout.inr (α.app B) (P.map j) =
      pushout.inr (α.app A) (P.map i) ≫ corner α (Arrow.mk i) ≫
        pushout.inl (α.app B) (P.map j)
    rw [← Category.assoc, inr_corner_mk α i]
    exact pushout.condition.symm

/-- The middle corner map is the actual pushout of the first corner. -/
theorem corner_composition_pushout {A B E : D} (i : A ⟶ B) (j : B ⟶ E) :
    IsPushout (domainMap α (prefixArrow i j)) (corner α (Arrow.mk i))
      (domainMap α (suffixArrow i j)) (pushout.inl (α.app B) (P.map j)) := by
  have outer : IsPushout (P.map j)
      (pushout.inr (α.app A) (P.map i) ≫ corner α (Arrow.mk i))
      (pushout.inr (α.app A) (P.map (i ≫ j)) ≫ domainMap α (suffixArrow i j))
      (pushout.inl (α.app B) (P.map j)) := by
    rw [inr_corner_mk α i, domainMap_inr_mk α (suffixArrow i j)]
    change IsPushout (P.map j) (α.app B)
      (P.map (𝟙 E) ≫ pushout.inr (α.app B) (P.map j))
      (pushout.inl (α.app B) (P.map j))
    rw [P.map_id, Category.id_comp]
    exact (IsPushout.of_hasPushout (α.app B) (P.map j)).flip
  exact IsPushout.of_top outer (domain_composition_square α i j)
    (domain_composition_pushout α i j).flip

/-- The original target identity retains the entire composite corner map. -/
theorem corner_composition_factor {A B E : D} (i : A ⟶ B) (j : B ⟶ E) :
    domainMap α (suffixArrow i j) ≫ corner α (Arrow.mk j) =
      corner α (Arrow.mk (i ≫ j)) := by
  have h := map_square α (suffixArrow i j)
  change domainMap α (suffixArrow i j) ≫ corner α (Arrow.mk j) =
    corner α (Arrow.mk (i ≫ j)) ≫ Q.map (𝟙 E) at h
  exact h.trans ((congrArg (fun t => corner α (Arrow.mk (i ≫ j)) ≫ t)
    (Q.map_id E)).trans (Category.comp_id _))

section Weak

variable [ModelCategory C]

/-- Composition preserves corner weakness through the actual h-cofibration pushout. -/
theorem corner_weak_composition {A B E : D} (i : A ⟶ B) (j : B ⟶ E)
    (hi : weakEquivalences C (corner α (Arrow.mk i)))
    (hj : weakEquivalences C (corner α (Arrow.mk j)))
    (hPj : hCofibrations C (P.map j)) :
    weakEquivalences C (corner α (Arrow.mk (i ≫ j))) := by
  let : WeakEquivalence (corner α (Arrow.mk i)) := (weakEquivalence_iff _).mpr hi
  have hd : hCofibrations C (domainMap α (prefixArrow i j)) :=
    (hCofibrations C).of_isPushout (domain_composition_pushout α i j) hPj
  have hm : weakEquivalences C (domainMap α (suffixArrow i j)) :=
    (weakEquivalence_iff _).mp
      (HomotopicalAlgebra.HCofibrationGluing.weakEquivalence_of_pushout_hCof (corner_composition_pushout α i j) hd)
  rw [← corner_composition_factor α i j]
  exact (weakEquivalences C).comp_mem _ _ hm hj

/-- Cobase change preserves the actual weak corner through both original h-cofibration spans. -/
theorem corner_weak_cobase [IsLeftProper C]
    [PreservesColimitsOfShape WalkingSpan P] [PreservesColimitsOfShape WalkingSpan Q]
    {A B A' B' : D} {i : A ⟶ B} {u : A ⟶ A'}
    {v : B ⟶ B'} {j : A' ⟶ B'} (sq : IsPushout i u v j)
    (hi : weakEquivalences C (corner α (Arrow.mk i)))
    (hPi : hCofibrations C (P.map i)) (hQi : hCofibrations C (Q.map i)) :
    weakEquivalences C (corner α (Arrow.mk j)) := by
  let : WeakEquivalence (corner α (Arrow.mk i)) := (weakEquivalence_iff _).mpr hi
  have hLeg : hCofibrations C (pushout.inl (α.app A) (P.map i)) :=
    (hCofibrations C).of_isPushout (IsPushout.of_hasPushout (α.app A) (P.map i)) hPi
  apply (weakEquivalence_iff _).mp
  apply HomotopicalAlgebra.HCofibrationGluing.weakEquivalence_map_of_isPushouts_of_hCof
    (domain_cobase_pushout α sq) (sq.map Q)
    (a := 𝟙 (Q.obj A)) (b := corner α (Arrow.mk i)) (c := 𝟙 (Q.obj A'))
    (d := corner α (Arrow.mk j))
  · simpa only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Category.id_comp] using
      inl_corner α (Arrow.mk i)
  · simp
  · exact map_square α (cobaseArrow sq)
  · simpa only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Category.id_comp] using
      inl_corner α (Arrow.mk j)
  · exact hLeg
  · exact hQi

end Weak
end HomotopicalAlgebra.NaturalTransformationCorner
