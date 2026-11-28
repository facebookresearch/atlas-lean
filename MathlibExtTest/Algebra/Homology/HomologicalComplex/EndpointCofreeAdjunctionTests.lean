/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/

module

import MathlibExt.Algebra.Homology.HomologicalComplex.EndpointCofreeAdjunction
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.ZMod.Basic

/-!
# Nonzero coordinates of the endpoint cofree adjunction

Work in ModuleCat.{1} ℤ with the lifted coefficient ℤ/6. A chain complex
indexed by ℕ has multiplication by two from degree one to degree zero and
zero differentials elsewhere. Its adjunction unit has a nonzero first
coefficient at the endpoint and a nonzero second coefficient along that edge.

The native counit recovers the endpoint coefficient. The native right triangle
recovers the unit's nonzero second coordinate. A coefficient family given by
multiplication by two has a native adjunction mate whose corresponding second
coordinate is four; the inverse equivalence recovers its coefficient two.
The category object, morphism and index universes are distinct.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace MathlibExtTest.EndpointCofreeAdjunction

private abbrev A := ModuleCat.{1} ℤ
private abbrev V := ULift.{1} (ZMod 6)
private abbrev N : A := ModuleCat.of ℤ V
private abbrev c := ComplexShape.down ℕ
private abbrev one : V := ULift.up (1 : ZMod 6)
private abbrev twice : N ⟶ N := (2 : ℤ) • 𝟙 N

private abbrev K : HomologicalComplex A c where
  X _ := N
  d i j := if i = 1 ∧ j = 0 then twice else 0
  shape i j hij := by
    by_cases h : i = 1 ∧ j = 0
    · rcases h with ⟨rfl, rfl⟩
      exact (hij (by decide)).elim
    · exact if_neg h
  d_comp_d' i j k _ _ := by
    by_cases h : i = 1 ∧ j = 0
    · have h' : ¬ (j = 1 ∧ k = 0) := by
        intro hj
        exact Nat.zero_ne_one (h.2.symm.trans hj.1)
      simp only [if_pos h, if_neg h', comp_zero]
    · simp only [if_neg h, zero_comp]

private abbrev I : GradedObject ℕ A := K.X
private abbrev D : HomologicalComplex A c := (endpointCofreeFunctor A c).obj I
private abbrev U : K ⟶ D := (endpointCofreeUnit A c).app K

private lemma rel_one_zero : c.Rel 1 0 := by decide

private lemma no_next_zero : ¬ c.Rel 0 (c.next 0) := by
  intro h
  change c.next 0 + 1 = 0 at h
  exact Nat.succ_ne_zero (c.next 0) h

private lemma twice_one : twice.hom one = ULift.up (2 : ZMod 6) := by
  change (2 : ℤ) • (ULift.up (1 : ZMod 6) : V) = ULift.up (2 : ZMod 6)
  apply ULift.ext
  decide

private lemma differential_one_zero :
    (K.d 1 0).hom one = ULift.up (2 : ZMod 6) := by
  change (if (1 : ℕ) = 1 ∧ (0 : ℕ) = 0 then twice else 0).hom one = _
  rw [if_pos (by decide)]
  exact twice_one

private lemma unit_first_value :
    (U.f 0 ≫ endpointCofreeProjection (c := c) I 0).hom one = one := by
  change (((endpointCofreeUnit A c).app K).f 0 ≫
    endpointCofreeProjection (c := c) K.X 0).hom one = one
  rw [endpointCofreeUnit_fst A c K 0]
  rfl

private lemma unit_second_value :
    ((U.f 1 ≫ endpointCofreeSecondProjection (c := c) I 1) ≫
      (endpointCofreeNextTermIso I rel_one_zero).hom).hom one =
        ULift.up (2 : ZMod 6) := by
  change ((((endpointCofreeUnit A c).app K).f 1 ≫
    endpointCofreeSecondProjection (c := c) K.X 1) ≫
      (endpointCofreeNextTermIso K.X rel_one_zero).hom).hom one = _
  rw [endpointCofreeUnit_snd_of_rel A c K rel_one_zero]
  exact differential_one_zero

example : (endpointCofreeFunctor A c).IsRightAdjoint := inferInstance

example : Mono U := endpointCofreeUnit_mono A c K

example : (U.f 0 ≫ endpointCofreeSecondProjection (c := c) I 0) = 0 :=
  endpointCofreeUnit_snd_of_no_next A c K 0 no_next_zero

example : (U.f 0 ≫ endpointCofreeProjection (c := c) I 0).hom one = one :=
  unit_first_value

example : (U.f 0 ≫ endpointCofreeProjection (c := c) I 0).hom one ≠ 0 := by
  rw [unit_first_value]
  intro h
  exact (by decide : (1 : ZMod 6) ≠ 0) (congrArg ULift.down h)

example :
    ((U.f 1 ≫ endpointCofreeSecondProjection (c := c) I 1) ≫
      (endpointCofreeNextTermIso I rel_one_zero).hom).hom one =
        ULift.up (2 : ZMod 6) :=
  unit_second_value

example : (U.f 1).hom one ≠ 0 := by
  intro h
  have hv := unit_second_value
  change (endpointCofreeNextTermIso I rel_one_zero).hom.hom
    ((endpointCofreeSecondProjection (c := c) I 1).hom ((U.f 1).hom one)) =
      ULift.up (2 : ZMod 6) at hv
  rw [h, map_zero, map_zero] at hv
  exact (by decide : (0 : ZMod 6) ≠ 2) (congrArg ULift.down hv)

example :
    (((endpointCofreeCounit A c).app I) 0).hom ((U.f 0).hom one) = one := by
  rw [endpointCofreeCounit_app]
  change (U.f 0 ≫ endpointCofreeProjection (c := c) I 0).hom one = one
  exact unit_first_value

private abbrev recovered : D ⟶ D :=
  (endpointCofreeUnit A c).app D ≫
    (endpointCofreeFunctor A c).map ((endpointCofreeCounit A c).app I)

private lemma recovered_id : recovered = 𝟙 D :=
  (endpointCofreeAdjunction A c).right_triangle_components I

example : recovered = 𝟙 D := recovered_id

example :
    ((recovered.f 1 ≫ endpointCofreeSecondProjection (c := c) I 1) ≫
      (endpointCofreeNextTermIso I rel_one_zero).hom).hom ((U.f 1).hom one) =
        ULift.up (2 : ZMod 6) := by
  rw [recovered_id]
  simp only [HomologicalComplex.id_f, Category.id_comp]
  change ((U.f 1 ≫ endpointCofreeSecondProjection (c := c) I 1) ≫
    (endpointCofreeNextTermIso I rel_one_zero).hom).hom one = _
  exact unit_second_value

private abbrev doubleCoefficients : I ⟶ I := fun _ => twice

private abbrev mate : K ⟶ D :=
  (endpointCofreeAdjunction A c).homEquiv K I doubleCoefficients

example : U ≫ (endpointCofreeFunctor A c).map doubleCoefficients = mate := rfl

example :
    (mate.f 0 ≫ endpointCofreeProjection (c := c) I 0).hom one =
      ULift.up (2 : ZMod 6) := by
  change (((endpointCofreeAdjunction A c).homEquiv K I doubleCoefficients).f 0 ≫
    endpointCofreeProjection (c := c) I 0).hom one = _
  rw [endpointCofreeAdjunction_homEquiv_apply, endpointCofreeHom_fst]
  exact twice_one

example :
    ((mate.f 1 ≫ endpointCofreeSecondProjection (c := c) I 1) ≫
      (endpointCofreeNextTermIso I rel_one_zero).hom).hom one =
        ULift.up (4 : ZMod 6) := by
  change ((((endpointCofreeAdjunction A c).homEquiv K I doubleCoefficients).f 1 ≫
    endpointCofreeSecondProjection (c := c) I 1) ≫
      (endpointCofreeNextTermIso I rel_one_zero).hom).hom one = _
  rw [endpointCofreeAdjunction_homEquiv_apply,
    endpointCofreeHom_snd_of_rel K I doubleCoefficients rel_one_zero]
  change twice.hom ((K.d 1 0).hom one) = _
  rw [differential_one_zero]
  change (2 : ℤ) • (ULift.up (2 : ZMod 6) : V) = ULift.up (4 : ZMod 6)
  apply ULift.ext
  decide

example :
    ((((endpointCofreeAdjunction A c).homEquiv K I).symm mate) 0).hom one =
      ULift.up (2 : ZMod 6) := by
  change ((((endpointCofreeAdjunction A c).homEquiv K I).symm
    ((endpointCofreeAdjunction A c).homEquiv K I doubleCoefficients)) 0).hom one = _
  rw [Equiv.symm_apply_apply]
  exact twice_one

end MathlibExtTest.EndpointCofreeAdjunction
