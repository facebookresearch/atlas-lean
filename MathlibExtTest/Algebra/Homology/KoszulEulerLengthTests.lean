/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Homology.KoszulComplexPairCoordinates
import MathlibExt.Algebra.Homology.KoszulComplexFamilyEuler
import MathlibExt.Algebra.Homology.FiniteSupportLengthEuler
import MathlibExt.RingTheory.Length.FiniteColength
import MathlibExt.RingTheory.Length.FiniteFractionSubmodule
import MathlibExt.RingTheory.Length.DoubleQuotient
import MathlibExt.RingTheory.Length.ExactEulerChain
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Nonzero Koszul, length and support clients

The pair `(3,2)` over `ZMod 6` exercises the new ordered coordinate comparison.
The empty family over the infinite field `ℚ` has chosen cutoff one and Euler value
one. A two-coordinate rational module has a nonzero finite-colength quotient.
A two-term identity differential cancels opposite weights with a nonzero range;
the other shape-allowed differential is zero and has opposite weights as well.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators

namespace MathlibExtTest.KoszulEulerLength

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private abbrev R6 := ZMod 6
private def standardPair : Fin 2 → (Fin 2 → R6) := fun i => Pi.single i 1
private def orderedWedge : ⋀[R6]^2 (Fin 2 → R6) :=
  exteriorPower.ιMulti R6 2 standardPair

private lemma shortComplexIso_f_value {R : Type*} [Ring R]
    {S T : ShortComplex (ModuleCat R)} (e : S ≅ T) (x : T.X₁) :
    e.hom.τ₂ (S.f (e.inv.τ₁ x)) = T.f x := by
  have hτ : e.inv.τ₁ ≫ e.hom.τ₁ = 𝟙 T.X₁ :=
    congrArg (fun f : T ⟶ T => f.τ₁) e.inv_hom_id
  have he : e.inv.τ₁ ≫ (S.f ≫ e.hom.τ₂) = T.f := by
    calc
      e.inv.τ₁ ≫ (S.f ≫ e.hom.τ₂) = e.inv.τ₁ ≫ (e.hom.τ₁ ≫ T.f) :=
        congrArg (fun f : S.X₁ ⟶ T.X₂ => e.inv.τ₁ ≫ f) e.hom.comm₁₂.symm
      _ = T.f := by rw [← Category.assoc, hτ, Category.id_comp]
  simpa only [ModuleCat.comp_apply] using ConcreteCategory.congr_hom he x

private lemma top_one : KoszulComplex.pairTopEquiv R6 orderedWedge = 1 := by
  rw [orderedWedge, KoszulComplex.pairTopEquiv_apply_ιMulti]
  norm_num [standardPair, Pi.single_apply]

private lemma coordinate_top_one :
    (KoszulComplex.pairCoordinateShortComplex R6 3 2).f.hom (1 : R6) =
      KoszulComplex.pairFamily R6 4 3 := by
  change LinearMap.toSpanSingleton R6 (Fin 2 → R6)
      (KoszulComplex.pairFamily R6 (-2) 3) (1 : R6) =
    KoszulComplex.pairFamily R6 4 3
  rw [LinearMap.toSpanSingleton_apply_one, show (-2 : R6) = 4 from by decide]

example :
    (KoszulComplex.pairCoordinateShortComplex R6 3 2).f.hom (1 : R6) =
      KoszulComplex.pairFamily R6 4 3 := coordinate_top_one

example :
    let K := KoszulComplex.familyComplex R6 (KoszulComplex.pairFamily R6 3 2)
    let e := KoszulComplex.pairCoordinateShortComplexIso R6 3 2
    e.hom.τ₂.hom ((K.sc 1).f.hom (e.inv.τ₁.hom (1 : R6))) =
      KoszulComplex.pairFamily R6 4 3 := by
  dsimp only
  exact (shortComplexIso_f_value (KoszulComplex.pairCoordinateShortComplexIso R6 3 2)
    (1 : R6)).trans coordinate_top_one

example :
    exteriorPower.oneEquiv R6 (Fin 2 → R6)
        (KoszulComplex.differential R6 (Fin 2 → R6)
          (KoszulComplex.familyFunctional R6 (KoszulComplex.pairFamily R6 3 2))
          1 orderedWedge) = KoszulComplex.pairFamily R6 4 3 := by
  have h := LinearMap.congr_fun
    (KoszulComplex.pair_differential_one_coordinates R6 3 2) orderedWedge
  simp only [LinearMap.comp_apply] at h
  have ht : (KoszulComplex.pairTopEquiv R6).toLinearMap orderedWedge = (1 : R6) :=
    top_one
  have hv := congrArg
    (LinearMap.toSpanSingleton R6 (Fin 2 → R6) (KoszulComplex.pairFamily R6 (-2) 3)) ht
  simpa only [LinearEquiv.coe_toLinearMap, LinearEquiv.coe_coe,
    LinearMap.toSpanSingleton_apply_one,
    show (-2 : R6) = 4 from by decide] using h.trans hv

section EmptyFamily

private def emptyFamily : Fin 0 → ℚ := Fin.elim0
private abbrev emptyK := KoszulComplex.familyComplex ℚ emptyFamily

private lemma quotient_finite :
    Module.length ℚ (ℚ ⧸ Ideal.span (Set.range emptyFamily)) ≠ ⊤ :=
  Module.length_ne_top

private lemma empty_incoming : (emptyK.sc 0).f = 0 := by
  have hp : (ComplexShape.down ℕ).prev 0 = 1 :=
    (ComplexShape.down ℕ).prev_eq' (by decide : (ComplexShape.down ℕ).Rel 1 0)
  have hz : IsZero (emptyK.X ((ComplexShape.down ℕ).prev 0)) := by
    rw [hp]
    exact KoszulComplex.familyComplex_isZero_above ℚ emptyFamily 1 (by simp)
  exact hz.eq_of_src _ _

private lemma empty_outgoing : (emptyK.sc 0).g = 0 :=
  emptyK.shape 0 _ (by simp [ComplexShape.down_Rel])

private lemma empty_homology_length : Module.length ℚ (emptyK.homology 0) = 1 := by
  let e : emptyK.homology 0 ≅ emptyK.X 0 :=
    (ShortComplex.LeftHomologyData.ofZeros (emptyK.sc 0)
      empty_incoming empty_outgoing).homologyIso
  have h := e.toLinearEquiv.length_eq
  change Module.length ℚ (emptyK.homology 0) =
    Module.length ℚ (⋀[ℚ]^0 (Fin 0 → ℚ)) at h
  exact h.trans ((exteriorPower.zeroEquiv ℚ (Fin 0 → ℚ)).length_eq.trans
    (Module.length_eq_one (R := ℚ) (M := ℚ)))

example :
    (KoszulComplex.familyFiniteLengthHomologyDataOfQuotient ℚ
      emptyFamily quotient_finite).cutoff = 1 := by
  simp [KoszulComplex.familyFiniteLengthHomologyDataOfQuotient]

example :
    KoszulComplex.familyEulerCharacteristicOfQuotient ℚ emptyFamily quotient_finite = 1 := by
  rw [KoszulComplex.familyEulerCharacteristicOfQuotient_eq]
  simpa only [Fintype.card_fin, zero_add, Finset.sum_range_one, pow_zero,
    one_mul, empty_homology_length, ENat.toNat_one, Nat.cast_one] using (show (1 : ℤ) = 1 from rfl)

end EmptyFamily

section FiniteColength

private abbrev M := ℚ × ℚ
private def axis : Submodule ℚ M := (LinearMap.snd ℚ ℚ ℚ).ker

private def axisEquiv : ℚ ≃ₗ[ℚ] axis where
  toFun x := ⟨(x, 0), rfl⟩
  invFun x := x.1.1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl (show x.1.2 = 0 from x.2).symm
  map_add' _ _ := by
    apply Subtype.ext
    simp
  map_smul' r x := by
    apply Subtype.ext
    simp

private lemma axis_length : Module.length ℚ axis = 1 :=
  axisEquiv.length_eq.symm.trans (Module.length_eq_one (R := ℚ) (M := ℚ))

private lemma axis_quotient_length : Module.length ℚ (M ⧸ axis) = 1 :=
  ((LinearMap.snd ℚ ℚ ℚ).quotKerEquivOfSurjective
    LinearMap.snd_surjective).length_eq.trans
      (Module.length_eq_one (R := ℚ) (M := ℚ))

example : Module.length ℚ M = 2 ∧ Module.length ℚ axis = 1 ∧
    Module.length ℚ (M ⧸ axis) = 1 := by
  refine ⟨?_, axis_length, axis_quotient_length⟩
  rw [Module.length_prod, Module.length_eq_one]
  norm_num

example :
    Module.length ℚ (M ⧸ (⊥ : Submodule ℚ M)) =
      Module.length ℚ (axis ⧸ (⊥ : Submodule ℚ axis)) + 1 := by
  let e : (axis ⧸ axis.subtype.ker) ≃ₗ[ℚ] (axis ⧸ (⊥ : Submodule ℚ axis)) :=
    Submodule.quotEquivOfEq axis.subtype.ker ⊥ (by simp only [Submodule.ker_subtype])
  have h : Module.length ℚ (M ⧸ (⊥ : Submodule ℚ M)) =
      Module.length ℚ (axis ⧸ axis.subtype.ker) + Module.length ℚ (M ⧸ axis) :=
    Submodule.length_quotient_eq_add_of_le (⊥ : Submodule ℚ M) axis bot_le
  exact h.trans (congrArg₂ (fun a b : ENat => a + b) e.length_eq axis_quotient_length)

example :
    Module.length ℚ (axis ⧸ (axis.map (LinearMap.id : M →ₗ[ℚ] M)).comap axis.subtype) =
      Module.length ℚ (M ⧸ (LinearMap.id : M →ₗ[ℚ] M).range) := by
  have hfinite : IsFiniteLength ℚ (M ⧸ axis) :=
    Module.length_ne_top_iff.mp (by rw [axis_quotient_length]; simp)
  exact Submodule.length_quotient_map_eq_of_finite_colength axis hfinite
    LinearMap.id Function.injective_id (by simp)

example :
    Submodule.fractionScalarMap (R := ℤ) (K := ZMod 2) ⊤ (by simp) 0 =
      Submodule.fractionScalarMap (R := ℤ) (K := ZMod 2) ⊤ (by simp) 2 := by
  apply Subtype.ext
  change algebraMap ℤ (ZMod 2) (0 : ℤ) = algebraMap ℤ (ZMod 2) (2 : ℤ)
  decide

example :
    Module.length ℤ ((ℤ ⧸ Ideal.span {(4 : ℤ)}) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.span {(4 : ℤ)}) (2 : ℤ)}) =
      Module.length ℤ ((ℤ ⧸ Ideal.span {(2 : ℤ)}) ⧸
        Ideal.span {Ideal.Quotient.mk (Ideal.span {(2 : ℤ)}) (4 : ℤ)}) :=
  Ideal.length_quotient_span_quotient_span_comm ℤ 4 2

end FiniteColength

section IndependentWorlds

private def between : ULift.{1} ℚ →ₗ[ℚ] ULift.{2} ℚ where
  toFun x := ULift.up x.down
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma between_exact :
    Function.Exact (0 : ℚ →ₗ[ℚ] ULift.{1} ℚ) between := by
  intro x
  change ULift.up x.down = (0 : ULift.{2} ℚ) ↔ ∃ q : ℚ, (0 : ULift.{1} ℚ) = x
  constructor
  · intro h
    have hd : x.down = 0 := congrArg (fun y : ULift.{2} ℚ => y.down) h
    exact ⟨0, (ULift.ext hd).symm⟩
  · rintro ⟨q, hq⟩
    rw [← hq]
    rfl

example :
    (Module.length ℚ (ULift.{1} ℚ)).toNat =
      (Module.length ℚ (0 : ℚ →ₗ[ℚ] ULift.{1} ℚ).range).toNat +
        (Module.length ℚ between.range).toNat := by
  have hm : Module.length ℚ (ULift.{1} ℚ) = 1 :=
    (ULift.moduleEquiv : ULift.{1} ℚ ≃ₗ[ℚ] ℚ).length_eq.trans
      (Module.length_eq_one (R := ℚ) (M := ℚ))
  exact Module.exactPair_length_toNat ℚ 0 between between_exact (by rw [hm]; simp)

end IndependentWorlds

section Support

private abbrev Q : ModuleCat.{0} ℚ := ModuleCat.of ℚ ℚ
private def edge (i j : ZMod 2) : Q ⟶ Q := if i = 1 ∧ j = 0 then 𝟙 Q else 0
private def identityComplex : HomologicalComplex (ModuleCat.{0} ℚ)
    (ComplexShape.down (ZMod 2)) where
  X _ := Q
  d := edge
  shape i j hij := by
    by_cases h : i = 1 ∧ j = 0
    · rcases h with ⟨rfl, rfl⟩
      exact False.elim (hij (by decide))
    · simp [edge, h]
  d_comp_d' i j k _ _ := by
    by_cases hij : i = 1 ∧ j = 0
    · have hjk : ¬ (j = 1 ∧ k = 0) := by
        rintro ⟨hj, _⟩
        exact zero_ne_one (hij.2.symm.trans hj)
      simp only [edge, if_pos hij, if_neg hjk, comp_zero]
    · simp only [edge, if_neg hij, zero_comp]

private def weight (i : ZMod 2) : ℤ := if i = 0 then 1 else -1
private lemma weight_opposite (i j : ZMod 2)
    (h : (ComplexShape.down (ZMod 2)).Rel i j) : weight i + weight j = 0 := by
  have hrel : j + 1 = i := h
  have hne : i ≠ j := by
    intro hij
    have hh : j + 1 = j + 0 := by simpa only [hij, add_zero] using hrel
    exact one_ne_zero (add_left_cancel hh)
  have hi : i = 0 ∨ i = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) i
  have hj : j = 0 ∨ j = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) j
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hne rfl).elim
  · simp only [weight, if_pos rfl, if_neg (show (1 : ZMod 2) ≠ 0 from one_ne_zero)]
    norm_num
  · simp only [weight, if_pos rfl, if_neg (show (1 : ZMod 2) ≠ 0 from one_ne_zero)]
    norm_num
  · exact (hne rfl).elim

example : (identityComplex.d 1 0).hom (1 : ℚ) = (1 : ℚ) ∧
    identityComplex.d 0 1 = 0 := by
  constructor
  · change (edge (1 : ZMod 2) 0).hom (1 : ℚ) = (1 : ℚ)
    simp [edge]
  · change edge (0 : ZMod 2) 1 = 0
    have hbad : ¬ ((0 : ZMod 2) = 1 ∧ (1 : ZMod 2) = 0) := fun h => zero_ne_one h.1
    simp only [edge, if_neg hbad]

example : Module.length ℚ (identityComplex.d 1 0).hom.range = 1 := by
  change Module.length ℚ (LinearMap.id : ℚ →ₗ[ℚ] ℚ).range = 1
  rw [LinearMap.range_id, Module.length_top]
  exact Module.length_eq_one (R := ℚ) (M := ℚ)

example :
    (∑ i : ZMod 2, weight i * (Module.length ℚ (identityComplex.homology i)).toNat) = 0 := by
  have hz (i : ZMod 2) (hi : i ∉ (Finset.univ : Finset (ZMod 2))) :
      IsZero (identityComplex.X i) := False.elim (hi (Finset.mem_univ i))
  have hl (i : ZMod 2) (_ : i ∈ (Finset.univ : Finset (ZMod 2))) :
      Module.length ℚ (identityComplex.X i) ≠ ⊤ := by
    change Module.length ℚ ℚ ≠ ⊤
    rw [Module.length_eq_one]
    simp
  have h := identityComplex.lengthEuler_eq_homology_of_finite_support
    Finset.univ weight hz hl weight_opposite
  have hterm :
      (∑ i : ZMod 2, weight i * (Module.length ℚ (identityComplex.X i)).toNat) = 0 := by
    change (∑ i : ZMod 2, weight i * (Module.length ℚ ℚ).toNat) = 0
    rw [Module.length_eq_one]
    have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    rw [huniv]
    norm_num [weight]
  exact h.2.2.symm.trans hterm

end Support

end MathlibExtTest.KoszulEulerLength
