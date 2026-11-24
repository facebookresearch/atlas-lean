/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Restriction and extension by zero

For an embedding whose image is closed under incoming differentials,
restriction is left adjoint to extension by zero. The unit is the brutal
cotruncation projection; its components are the canonical projection on
supported degrees and the map to zero elsewhere. These projections are
epimorphisms, and the category and index universes remain independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v i j

namespace ComplexShape.Embedding

variable {I : Type i} {J : Type j} {c : ComplexShape I} {d : ComplexShape J}
  (e : c.Embedding d) [e.IsTruncLE]
  {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

omit [HasZeroObject C] in
/-- Actual incoming-closure eliminates the native boundary obstruction. -/
theorem hasLift_of_isTruncLE {K : HomologicalComplex C d} {L : HomologicalComplex C c}
    (f : K.restriction e ⟶ L) : e.HasLift f := by
  intro q hq p hpq
  obtain ⟨r, hr⟩ := e.mem_prev hpq
  exact (hq.notMem hpq r hr).elim

/-- Native restriction and extension maps give the genuine unrestricted Hom equivalence. -/
def restrictionExtendHomEquiv (K : HomologicalComplex C d) (L : HomologicalComplex C c) :
    (K.restriction e ⟶ L) ≃ (K ⟶ L.extend e) where
  toFun f := e.liftExtend f (e.hasLift_of_isTruncLE f)
  invFun f := e.homRestrict f
  left_inv f := e.homRestrict_liftExtend f (e.hasLift_of_isTruncLE f)
  right_inv f := e.liftExtend_homRestrict f

@[simp]
theorem restrictionExtendHomEquiv_apply {K : HomologicalComplex C d}
    {L : HomologicalComplex C c} (f : K.restriction e ⟶ L) :
    e.restrictionExtendHomEquiv K L f = e.liftExtend f (e.hasLift_of_isTruncLE f) := rfl

@[simp]
theorem restrictionExtendHomEquiv_symm_apply {K : HomologicalComplex C d}
    {L : HomologicalComplex C c} (f : K ⟶ L.extend e) :
    (e.restrictionExtendHomEquiv K L).symm f = e.homRestrict f := rfl

/-- The original range condition earns a genuine categorical adjunction. -/
def restrictionExtendAdjunction : e.restrictionFunctor C ⊣ e.extendFunctor C :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun K L => e.restrictionExtendHomEquiv K L
      homEquiv_naturality_left_symm := fun f g => e.homRestrict_precomp f g
      homEquiv_naturality_right := by
        intro K L L' f g
        apply (e.restrictionExtendHomEquiv K L').symm.injective
        change e.homRestrict (e.liftExtend (f ≫ g) (e.hasLift_of_isTruncLE (f ≫ g))) =
          e.homRestrict (e.liftExtend f (e.hasLift_of_isTruncLE f) ≫
            HomologicalComplex.extendMap g e)
        exact (e.homRestrict_liftExtend (f ≫ g) (e.hasLift_of_isTruncLE _)).trans
          ((congrArg (fun z => z ≫ g)
            (e.homRestrict_liftExtend f (e.hasLift_of_isTruncLE _))).symm.trans
              (e.homRestrict_comp_extendMap _ g).symm) }

end ComplexShape.Embedding

namespace HomologicalComplex

variable {I : Type i} {J : Type j} {c : ComplexShape I} {d : ComplexShape J}
  {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  (K : HomologicalComplex C d) (e : c.Embedding d) [e.IsTruncLE]

/-- The projection is the genuine unit of the earned restriction/extension adjunction. -/
theorem πStupidTrunc_eq_unit :
    K.πStupidTrunc e = (e.restrictionExtendAdjunction (C := C)).unit.app K := by
  change K.πStupidTrunc e =
    e.liftExtend (𝟙 (K.restriction e)) (e.hasLift_of_isTruncLE _)
  ext q
  by_cases hq : ∃ p, e.f p = q
  · obtain ⟨p, rfl⟩ := hq
    rw [HomologicalComplex.πStupidTrunc_f, HomologicalComplex.πStupidTruncf_eq,
      e.liftExtend_f (𝟙 (K.restriction e)) (e.hasLift_of_isTruncLE _) (i := p) rfl]
    change ((K.restriction e).extendXIso e (i := p) rfl).inv =
      𝟙 _ ≫ 𝟙 _ ≫ ((K.restriction e).extendXIso e (i := p) rfl).inv
    simp only [Category.id_comp]
  · exact (K.isZero_stupidTrunc_X e q (by simpa using hq)).eq_of_tgt _ _

/-- On the retained original range, the projection is the inverse actual coordinate. -/
theorem πStupidTrunc_f_eq {p : I} {q : J} (h : e.f p = q) :
    (K.πStupidTrunc e).f q = (K.stupidTruncXIso e h).inv := by
  subst q
  rw [HomologicalComplex.πStupidTrunc_f, HomologicalComplex.πStupidTruncf_eq,
    HomologicalComplex.stupidTruncXIso_rfl]

/-- Off the original range, the projection has the actual zero target. -/
theorem πStupidTrunc_f_zero (q : J) (h : ∀ p, e.f p ≠ q) :
    (K.πStupidTrunc e).f q = 0 :=
  (K.isZero_stupidTrunc_X e q h).eq_of_tgt _ _

instance πStupidTrunc_f_epi (q : J) : Epi ((K.πStupidTrunc e).f q) := inferInstance

instance πStupidTrunc_epi : Epi (K.πStupidTrunc e) := inferInstance

variable {K}

/-- Agreement after the actual projection determines a map out of the cotruncation. -/
theorem πStupidTrunc_hom_ext {X : HomologicalComplex C d}
    {f g : K.stupidTrunc e ⟶ X} (h : K.πStupidTrunc e ≫ f = K.πStupidTrunc e ≫ g) :
    f = g := (cancel_epi (K.πStupidTrunc e)).1 h

end HomologicalComplex
