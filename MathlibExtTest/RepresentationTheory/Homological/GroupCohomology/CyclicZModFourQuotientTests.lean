/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.Homological.GroupCohomology.FiniteCyclicH3Invariant
import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CyclicEvenResolutionIso
import Mathlib.Algebra.Group.TypeTags.Finite
meta import Mathlib.Tactic.NormNum

/-!
# Genuine cyclic quotient classes over a ring with zero divisors

For the trivial `ZMod 4` representation of the order-two group, the norm is multiplication
by two and the generator difference is zero. The coefficient two gives a nonzero odd
quotient class in ker(norm)/im(difference). The coefficient one gives a nonzero even quotient
class; reduction modulo two proves it cannot belong to the norm image. These are actual
quotient maps over a nonfield coefficient ring.
-/

open CategoryTheory groupCohomology
open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace CyclicZModFourQuotientTests

private abbrev R := ZMod 4
private abbrev G := Multiplicative (ZMod 2)
private abbrev A : Rep R G := Rep.trivial R G R
private def s : G := Multiplicative.ofAdd (1 : ZMod 2)
private def enumerate : Fin 2 ≃ G where
  toFun i := Multiplicative.ofAdd i
  invFun g := g.toAdd
  left_inv _ := rfl
  right_inv _ := rfl

private lemma norm_value (a : R) : A.norm.asHom.hom a = 2 * a := by
  rw [Rep.norm_apply]
  change (∑ g : G, A.ρ g a) = 2 * a
  have h := enumerate.sum_comp (fun g : G => A.ρ g a)
  rw [Fin.sum_univ_two] at h
  change a + a = ∑ g : G, A.ρ g a at h
  rw [← h]
  exact (two_mul a).symm

private lemma difference_value (a : R) : (Rep.applyAsHom A s - 𝟙 A).hom a = 0 := by
  change a - a = 0
  exact sub_self a

private def oddTwo : LinearMap.ker A.norm.asHom.hom.toLinearMap :=
  ⟨(2 : R), by
    rw [LinearMap.mem_ker]
    change A.norm.asHom.hom (2 : R) = 0
    rw [norm_value]
    decide⟩

example : A.norm.asHom.hom (2 : R) = 0 := by rw [norm_value]; decide
example : (oddTwo : R) ≠ 0 := by change (2 : R) ≠ 0; decide

example : cyclicOddHomologyπ A s oddTwo ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := (cyclicOddHomologyπ_eq_zero_iff A s oddTwo).1 h
  change (Rep.applyAsHom A s - 𝟙 A).hom a = (2 : R) at ha
  rw [difference_value] at ha
  exact (by decide : (0 : R) ≠ 2) ha

private def fixedOne : LinearMap.ker (Rep.applyAsHom A s - 𝟙 A).hom.toLinearMap :=
  ⟨(1 : R), by rw [LinearMap.mem_ker]; exact difference_value 1⟩

private def fixedZero : LinearMap.ker (Rep.applyAsHom A s - 𝟙 A).hom.toLinearMap := 0

private abbrev E := Rep.FiniteCyclicGroup.normHomCompSub A s
private def evenOne : E.moduleCatLeftHomologyData.H := E.moduleCatLeftHomologyData.π fixedOne

private def modTwo : R →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)

private lemma one_not_norm_image : (1 : R) ∉ LinearMap.range A.norm.asHom.hom.toLinearMap := by
  rintro ⟨a, ha⟩
  change A.norm.asHom.hom a = (1 : R) at ha
  rw [norm_value] at ha
  have h := congrArg modTwo ha
  rw [map_mul] at h
  have ht : modTwo (2 : R) = 0 := by decide
  have ho : modTwo (1 : R) = 1 := map_one modTwo
  rw [ht, ho, zero_mul] at h
  exact (by decide : (0 : ZMod 2) ≠ 1) h

example : evenOne ≠ 0 := by
  intro h
  have he : E.moduleCatLeftHomologyData.π fixedOne =
      E.moduleCatLeftHomologyData.π fixedZero := by
    simpa only [evenOne, fixedZero, map_zero] using h
  have hn := (cyclicEvenQuotient_π_eq_iff_norm A s fixedOne fixedZero).1 he
  apply one_not_norm_image
  simpa only [fixedOne, fixedZero, sub_zero] using hn

example : E.moduleCatLeftHomologyData.π fixedOne = evenOne := rfl

end CyclicZModFourQuotientTests
