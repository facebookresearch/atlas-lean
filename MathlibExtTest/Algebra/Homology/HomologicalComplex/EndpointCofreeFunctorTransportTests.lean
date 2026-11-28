/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/

module

import MathlibExt.Algebra.Homology.HomologicalComplex.EndpointCofreeFunctorTransport
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.Data.ZMod.Basic

/-!
# Transporting a nonzero endpoint injective presentation

Take the integer module ℤ/6 and the natural-number chain with multiplication by
two from degree one to degree zero, and zero differentials elsewhere. An
injective presentation of its graded family gives an injective presentation of
the chain through the cofree adjunction. Its value at one in degree zero
is nonzero, as is its endpoint coefficient under the comonad counit.

The additive universe-lift functor from integer modules with carriers in
universe zero to carriers in universe one transports this cofree target. The
canonical cofree comparison preserves the nonzero lifted point. It also
commutes with the unit, whose outgoing second coefficient retains the value two.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject

namespace MathlibExtTest.EndpointCofreeFunctorTransport

private abbrev C₀ := ModuleCat.{0} ℤ
private abbrev C₁ := ModuleCat.{1} ℤ
private abbrev N : C₀ := ModuleCat.of ℤ (ZMod 6)
private abbrev c := ComplexShape.down ℕ
private abbrev twice : N ⟶ N := (2 : ℤ) • 𝟙 N

private abbrev K : HomologicalComplex C₀ c where
  X _ := N
  d i j := if i = 1 ∧ j = 0 then twice else 0
  shape i j hij := by
    by_cases h : i = 1 ∧ j = 0
    · rcases h with ⟨rfl, rfl⟩
      exact (hij (by decide)).elim
    · exact ite_eq_right h
  d_comp_d' i j k _ _ := by
    by_cases h : i = 1 ∧ j = 0
    · have h' : ¬ (j = 1 ∧ k = 0) := by
        intro hj
        exact Nat.zero_ne_one (h.2.symm.trans hj.1)
      simp only [ite_eq_left h, ite_eq_right h', comp_zero]
    · simp only [ite_eq_right h, zero_comp]

private lemma no_next_zero : ¬ c.Rel 0 (c.next 0) := by
  intro h
  change c.next 0 + 1 = 0 at h
  exact Nat.succ_ne_zero (c.next 0) h

private lemma rel_one_zero : c.Rel 1 0 := by decide

private lemma differential_value : (K.d 1 0).hom (1 : ZMod 6) = 2 := by
  change (if (1 : ℕ) = 1 ∧ (0 : ℕ) = 0 then twice else 0).hom (1 : ZMod 6) = _
  rw [ite_eq_left (by decide)]
  change (2 : ℤ) • (1 : ZMod 6) = 2
  decide

private instance gradedEnoughInjectives : EnoughInjectives (GradedObject ℕ C₀) := by
  letI : EnoughInjectives (Discrete ℕ ⥤ C₀) := enoughInjectives_discrete ℕ
  exact EnoughInjectives.of_equivalence (piEquivalenceFunctorDiscrete ℕ C₀).functor

private def gradedPresentation : InjectivePresentation ((forget C₀ c).obj K) where
  J := Injective.under ((forget C₀ c).obj K)
  f := Injective.ι ((forget C₀ c).obj K)

private abbrev I : GradedObject ℕ C₀ := gradedPresentation.J
private abbrev E : HomologicalComplex C₀ c := (endpointCofreeFunctor C₀ c).obj I

private def presentation : InjectivePresentation K :=
  (endpointCofreeAdjunction C₀ c).injectivePresentationOfMap K gradedPresentation

private instance presentationMono : Mono presentation.f := presentation.mono

private def originalPoint : E.X 0 := (presentation.f.f 0).hom (1 : ZMod 6)

private lemma originalPoint_ne_zero : originalPoint ≠ 0 := by
  intro h
  have hinj := (ModuleCat.mono_iff_injective (presentation.f.f 0)).1 inferInstance
  have hzero : (1 : ZMod 6) = 0 :=
    hinj (h.trans ((presentation.f.f 0).hom.map_zero).symm)
  exact (by decide : (1 : ZMod 6) ≠ 0) hzero

example : Injective E := presentation.injective

example : Mono presentation.f := presentation.mono

example : originalPoint ≠ 0 := originalPoint_ne_zero

example (i : ℕ) :
    presentation.f.f i ≫ endpointCofreeProjection c I i = gradedPresentation.f i := by
  change ((endpointCofreeAdjunction C₀ c).homEquiv K I gradedPresentation.f).f i ≫
    endpointCofreeProjection c I i = gradedPresentation.f i
  rw [endpointCofreeAdjunction_homEquiv_apply]
  exact endpointCofreeHom_fst K I gradedPresentation.f i

example : endpointCofreeNextTerm c I 0 = (0 : C₀) :=
  endpointCofreeNextTerm_of_no_next I 0 no_next_zero

example : (endpointCofreeFunctor C₀ c).PreservesInjectiveObjects := inferInstance

example : PreservesLimitsOfSize.{1, 1} (endpointCofreeFunctor C₀ c) := inferInstance

private abbrev T : Comonad (GradedObject ℕ C₀) := (endpointCofreeAdjunction C₀ c).toComonad

example : (T.ε.app I) 0 = endpointCofreeProjection c I 0 :=
  endpointCofreeCounit_app C₀ c I 0

example : ((T.ε.app I) 0).hom originalPoint ≠ 0 := by
  change (endpointCofreeProjection c I 0).hom originalPoint ≠ 0
  let e : E.X 0 ≅ I 0 := endpointCofreeXIsoOfNoNext I 0 no_next_zero
  intro h
  change e.hom.hom originalPoint = 0 at h
  have hinj := (ModuleCat.mono_iff_injective e.hom).1 inferInstance
  exact originalPoint_ne_zero (hinj (h.trans (e.hom.hom.map_zero).symm))

example : (T.δ.app I) 0 ≫ (T.ε.app (T.obj I)) 0 = 𝟙 ((T.obj I) 0) := by
  change ((endpointCofreeUnit C₀ c).app E).f 0 ≫
    endpointCofreeProjection c E.X 0 = 𝟙 (E.X 0)
  exact endpointCofreeUnit_fst C₀ c E 0

private abbrev F : C₀ ⥤ C₁ := ModuleCat.uliftFunctor.{1, 0} ℤ
private abbrev liftedCoefficients : GradedObject ℕ C₁ := (Functor.pi (fun _ : ℕ => F)).obj I

private def transport :
    (F.mapHomologicalComplex c).obj E ≅ (endpointCofreeFunctor C₁ c).obj liftedCoefficients :=
  (endpointCofreeFunctorTransportIso F c).app I

private def liftedPoint : ((endpointCofreeFunctor C₁ c).obj liftedCoefficients).X 0 :=
  (transport.hom.f 0).hom (ULift.up originalPoint)

example : liftedPoint ≠ 0 := by
  intro h
  have hinj := (ModuleCat.mono_iff_injective (transport.hom.f 0)).1 inferInstance
  have hzero := hinj (h.trans ((transport.hom.f 0).hom.map_zero).symm)
  exact originalPoint_ne_zero (congrArg ULift.down hzero)

example :
    (F.mapHomologicalComplex c).map ((endpointCofreeUnit C₀ c).app K) ≫
        (endpointCofreeFunctorTransportIso F c).hom.app ((forget C₀ c).obj K) =
      (endpointCofreeUnit C₁ c).app ((F.mapHomologicalComplex c).obj K) :=
  endpointCofreeFunctorTransportIso_unit F c K

example :
    let KL := (F.mapHomologicalComplex c).obj K
    let J : GradedObject ℕ C₁ := KL.X
    (((((endpointCofreeUnit C₁ c).app KL).f 1 ≫
      endpointCofreeSecondProjection c J 1) ≫
        (endpointCofreeNextTermIso J rel_one_zero).hom).hom
          (ULift.up (1 : ZMod 6))) = ULift.up (2 : ZMod 6) := by
  dsimp only
  rw [endpointCofreeUnit_snd_of_rel]
  change ULift.up ((K.d 1 0).hom (1 : ZMod 6)) = ULift.up (2 : ZMod 6)
  rw [differential_value]

example (i : ℕ) :
    (transport.hom.f i) ≫ ((endpointCofreeCounit C₁ c).app liftedCoefficients) i =
      F.map (((endpointCofreeCounit C₀ c).app I) i) :=
  endpointCofreeFunctorTransportIso_counit F c I i

end MathlibExtTest.EndpointCofreeFunctorTransport
