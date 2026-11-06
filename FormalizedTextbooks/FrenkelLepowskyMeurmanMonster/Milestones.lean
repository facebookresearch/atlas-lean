/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Six FLM Monster milestone theorem statements (T1–T6), mapping to
`HUMAN_REVIEW.md`: T1 local subgroup structure and faithful action, T2 extra
symmetry and generated group, T3 finiteness, T4 Monster order, T5 simplicity,
T6 identification with the classical Monster.

Status: PARTIAL PROOFS. T1–T3 and T5 are proved in full. T4 and T6 retain documented
`sorry` proof holes. All six refer to the SAME named construction objects
from `Definitions.lean` (`Q`, `H`, `Co1`, `rhoLocal`, `sExtra`, `G`,
`classicalMonster`). No theorem assumes finiteness, simplicity, order, or any
isomorphism as a hypothesis: such hypotheses would make the endpoints circular.
In particular, `centerMap` is a raw hom here; its bijectivity is a T1
conclusion, not a definition.

Reviewing endpoint signatures alone is NOT sufficient for faithfulness:
the implemented supplementary coordinate model still needs comparison
with FLM. See `GAPS.md` for the proof and source-comparison inventory.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalStructure
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalProductInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityFullProduct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFiniteness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalCompletion
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- T1: the concrete local subgroup has the
claimed extraspecial structure (`|Q| = 2^25`, center = derived = Frattini,
center of order two, quotient `Q/Z(Q) ≅ (F₂^24, +)`), the raw center hom is
bijective, the squares-induced form has plus type (isometric to the explicit
hyperbolic `hyperbolicFun`), the raw maps are exact (`inclQ` injective,
`projH` surjective, image = kernel), and the local action `rhoLocal` is
injective and preserves the specified Griess product and form. No splitting
is asserted. -/
theorem local_subgroup_structure :
    Nat.card Q = 2 ^ 25 ∧
    centerQ = commutator Q ∧
    commutator Q = frattini Q ∧
    Nat.card ↥centerQ = 2 ∧
    Function.Bijective ⇑centerMap ∧
    Nonempty ((Q ⧸ centerQ) ≃* Multiplicative (Fin 24 → ZMod 2)) ∧
    qQuotHom.ker = centerQ ∧
    qQuotHom.range = ⊤ ∧
    (∀ g : Q, ∃ _hz : g * g ∈ centerQ,
      squareQuad (Multiplicative.toAdd (qQuotHom g)) =
        Multiplicative.toAdd (centerMap ⟨g * g, _hz⟩)) ∧
    (∃ _e : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2]
        ((Fin 12 → ZMod 2) × (Fin 12 → ZMod 2)),
      ∀ v, squareQuad v = hyperbolicFun (_e v)) ∧
    Function.Injective ⇑inclQ ∧
    Function.Surjective ⇑projH ∧
    inclQ.range = projH.ker ∧
    Function.Injective ⇑rhoLocal ∧
    (∀ h x y, rhoLocal h (griessProd x y) =
      griessProd (rhoLocal h x) (rhoLocal h y)) ∧
    (∀ h x y, griessForm (rhoLocal h x) (rhoLocal h y) =
      griessForm x y) := by
  obtain ⟨hcard, hcenter, hfrattini, hcenterCard, hcenterMap, hquotient,
    hkernel, hrange, hsquares, hhyperbolic⟩ := q_extraspecial_structure
  refine ⟨hcard, hcenter, hfrattini, hcenterCard, hcenterMap, hquotient,
    hkernel, hrange, hsquares, hhyperbolic, inclQ_injective, projH_surjective,
    inclQ_range_eq_projH_ker,
    rhoLocal_injective, rhoLocal_product, rhoLocal_form⟩

/-- T2: the source-specified extra symmetry
`sExtra` preserves the Griess product and form (a genuine property of the raw
ambient-GL element, not a typing tautology), and the generated group `G` lies
in the product-and-form preserving subgroup. `G` is defined by
`Subgroup.closure`, so no exactness or membership conclusion is built in. -/
theorem extra_symmetry_preserves_griess :
    IsGriessAuto sExtra ∧ G ≤ griessAutSubgroup := by
  have hproduct : ∀ x y, sExtra (griessProd x y) =
      griessProd (sExtra x) (sExtra y) := by
    exact sExtra_preserves_griessProd
  have hextra : IsGriessAuto sExtra := ⟨hproduct, sExtra_preserves_griessForm⟩
  exact ⟨hextra, G_le_griessAutSubgroup_of_generator_invariance
    rhoLocal_isGriessAuto hextra⟩

/-- T3: the generated group `G` is finite, by the actual spanning axial orbit
and its proved isolation properties, using full triality product preservation.
No `[Finite G]` hypothesis appears in the statement. -/
theorem generated_group_finite :
    Finite ↥G := by
  exact generated_group_finite_of_triality_product
    extra_symmetry_preserves_griess.1.1

/-- T4 (statement-only, proof `sorry`): `G` has the Monster order. No
finiteness or order hypothesis is assumed (T3 is separate, so `Nat.card`
being zero on infinite types cannot accidentally satisfy this positive
numeral). -/
theorem generated_group_order :
    Nat.card ↥G =
      2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 *
      17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71 := by
  sorry

/-- T5: `G` is simple, using the proved full centralizer and actual normal generation.
`IsSimpleGroup`
includes nontriviality, so the trivial group cannot satisfy this. -/
theorem generated_group_simple :
    IsSimpleGroup ↥G := by
  exact generated_simple_of_centralizer_le_local generatedCentralizer_eq_local_range.le

/-- T6 (statement-only, proof `sorry`): `G` is isomorphic to the
independently source-bound classical Monster model. The reference model is a
separate object (`classicalMonster`, hole S-classicalMonster), not `G`
itself, and no isomorphism is assumed: only `Nonempty` of the isomorphism
type is claimed. Order and simplicity alone do not prove this. -/
theorem generated_group_iso_classical_monster :
    Nonempty (classicalMonster ≃* ↥G) := by
  sorry

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
