/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiPairData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialPairSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortCoordinates

/-! Finite physical Xi pair addresses are bound to the intrinsic short catalogue. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- A physical pair address gives its genuine index, with an unused equal-coordinate fallback. -/
def generatedSixthXiPairShort (x : Fin 2 × Fin 24 × Fin 24) : GriessShortIndex :=
  Sum.inl (x.1, if h : x.2.1 ≠ x.2.2 then griessPairIndex x.2.1 x.2.2 h else 0)

/-- The physical integer formula on a sorted preferred pair address. -/
def generatedSixthXiPairIntegral (x : Fin 2 × Fin 24 × Fin 24) (i : Fin 24) : ℤ :=
  4 * (if i = x.2.1 then 1 else 0) +
    (if x.1 = 0 then -4 else 4) * (if i = x.2.2 then 1 else 0)

/-- Actual pair-index inversion binds the preferred physical integer vector. -/
theorem generatedSixth_xi_pair_short_integral (x : Fin 2 × Fin 24 × Fin 24)
    (hx : x.2.1 < x.2.2) :
    griessShortIntegral (generatedSixthXiPairShort x) = generatedSixthXiPairIntegral x := by
  have hn : x.2.1 ≠ x.2.2 := ne_of_lt hx
  rw [generatedSixthXiPairShort, dite_eq_left hn]
  simp only [griessShortIntegral, griessPairIndex_coordinates, hx, ite_true]
  rfl

/-- All displayed source addresses are ordered genuine physical pairs. -/
theorem generatedSixth_xi_pair_source_ordered : ∀ j : Fin 552,
    (generatedSixthXiPairSourceCoordinates j).2.1 <
      (generatedSixthXiPairSourceCoordinates j).2.2 := by
  decide +kernel

/-- The finite physical-order predicate, including already bound octad outputs. -/
def generatedSixthXiPairOutputOrdered (j : Fin 552) : Bool :=
  match generatedSixthXiPairOutputAddress j with
  | Sum.inl x => decide (x.2.1 < x.2.2)
  | Sum.inr _ => true

/-- Every displayed physical pair output has been checked in increasing order. -/
theorem generatedSixth_xi_pair_output_ordered_certificate : ∀ j : Fin 552,
    generatedSixthXiPairOutputOrdered j = true := by
  decide +kernel

/-- All displayed physical pair outputs are ordered genuine addresses. -/
theorem generatedSixth_xi_pair_output_ordered (j : Fin 552) :
    match generatedSixthXiPairOutputAddress j with
    | Sum.inl x => x.2.1 < x.2.2
    | Sum.inr _ => True := by
  have h := generatedSixth_xi_pair_output_ordered_certificate j
  unfold generatedSixthXiPairOutputOrdered at h
  cases he : generatedSixthXiPairOutputAddress j with
  | inl x => simpa only [he, decide_eq_true_eq] using h
  | inr _ => trivial

/-- Every source is an intrinsic actual preferred pair label. -/
def generatedSixthXiPairInput (j : Fin 552) : GriessShortIndex :=
  generatedSixthXiPairShort (generatedSixthXiPairSourceCoordinates j)

/-- Every output uses an intrinsic pair index or a previously bound actual octad index. -/
def generatedSixthXiPairOutput (j : Fin 552) : GriessShortIndex :=
  match generatedSixthXiPairOutputAddress j with
  | Sum.inl x => generatedSixthXiPairShort x
  | Sum.inr (f, e) => Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad f, e))

/-- The complete physical source vector is finite original coordinate arithmetic. -/
def generatedSixthXiPairInputIntegral (j : Fin 552) : Fin 24 → ℤ :=
  generatedSixthXiPairIntegral (generatedSixthXiPairSourceCoordinates j)

/-- The complete output vector uses genuine ordered coordinates and all preferred signs. -/
def generatedSixthXiPairOutputIntegral (j : Fin 552) : Fin 24 → ℤ :=
  match generatedSixthXiPairOutputAddress j with
  | Sum.inl x => generatedSixthXiPairIntegral x
  | Sum.inr (f, e) => generatedSixthMonomialOctadIntegral f e

/-- The executable source vector is the genuine preferred integer vector. -/
theorem generatedSixth_xi_pair_input_integral (j : Fin 552) :
    griessShortIntegral (generatedSixthXiPairInput j) =
      generatedSixthXiPairInputIntegral j :=
  generatedSixth_xi_pair_short_integral _ (generatedSixth_xi_pair_source_ordered j)

/-- The executable output vector is the genuine preferred integer vector. -/
theorem generatedSixth_xi_pair_output_integral (j : Fin 552) :
    griessShortIntegral (generatedSixthXiPairOutput j) =
      generatedSixthXiPairOutputIntegral j := by
  unfold generatedSixthXiPairOutput generatedSixthXiPairOutputIntegral
  cases he : generatedSixthXiPairOutputAddress j with
  | inl x =>
    apply generatedSixth_xi_pair_short_integral x
    simpa only [he] using generatedSixth_xi_pair_output_ordered j
  | inr x =>
    obtain ⟨f, e⟩ := x
    funext i
    exact generatedSixth_monomial_octad_integral f e i

/-- The original finite inverse lattice matrix computes the full intrinsic preferred Q lift. -/
def generatedSixthXiShortIntegerQ (u : Fin 24 → ℤ) : Q :=
  ⟨ofAdd (leechHyperbolicInverse *ᵥ integerParity (monsterNortonLeechCoordinates u)), 1⟩

/-- Exact original integral vector equality binds every component of preferred Q. -/
theorem generatedSixth_xi_short_integer_Q (r : GriessShortIndex) (u : Fin 24 → ℤ)
    (hu : griessShortIntegral r = u) :
    griessShortQ r = generatedSixthXiShortIntegerQ u := by
  rw [← monsterNortonShortQ_eq, monsterNortonShortQ, hu]
  rfl

/-- A displayed two-mask address represents all genuine Q coordinates and central bit zero. -/
def generatedSixthXiPackedQ (x : Fin 4096 × Fin 4096) : Q :=
  generatedAxisFourthQFromSpin (golayLabelCoefficients x.1) (golayLabelCoefficients x.2) 0

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
