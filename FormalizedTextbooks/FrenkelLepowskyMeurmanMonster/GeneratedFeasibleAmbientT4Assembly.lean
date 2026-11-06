/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFinal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTwelveAssembly
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientEighthZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCLocalOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadCovered
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingOctadOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOutsideOctadOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSixteenOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingSixteenInputRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingEighthActualOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingNewDestinationSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleFifthSlotOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSixthSlotOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSeventhSlotOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleRootEightSlotOrbitCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleTransitionFirstRow
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisEnumerationFeasibleSecondaryCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryNonPairClasses
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryOutsideOctadSigns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryContainingOctadSupport

/-! The Monster order of the generated group from the feasible-count bridge.

The ten actual feasible classes give ten actual feasible vectors for the physical root pair,
with pairwise distinct actual local stabilizer orbit sizes adding up to 11707448673375.
Together with the twelve exact local orbit lengths (the Tenth stabilizer order is closed), the
closed coverage of the First, Octad and Odd families, the closed orthogonal axis counts, and
double counting, this fixes the actual feasible count and hence the order of the generated
group. The explicit hypotheses are exactly the coverage predicates of families 3 to 11 and the
orthogonal axis counts of the Root8 and Tenth representatives; none of them is asserted here.
The two axis counts are proved in `GeneratedFeasibleAmbientRootEightZero` and
`GeneratedFeasibleAmbientTenthZero` and discharged in `GeneratedFeasibleAmbientT4Coverage`. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
-- The ten-class witness family unfolds deep literal vectors.
set_option maxRecDepth 20000

/-- The physical root pair of the actual feasible classes. -/
abbrev generatedFeasibleAmbientT4Pair : Fin 276 := generatedFeasiblePhysicalRootPair

/-- One actual feasible vector in each of the ten actual feasible classes. -/
noncomputable def generatedFeasibleAmbientT4Witness : Fin 10 → GriessSpace :=
  ![conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 1,
    generatedFeasibleSecondaryAxis generatedFeasibleAmbientT4Pair,
    generatedFeasibleContainingOctadDestination,
    generatedFeasibleOutsideOctadDestination,
    generatedFeasibleContainingSixteenDestination,
    generatedFeasibleContainingNewDestination,
    generatedFeasibleFifthSlotPrototype,
    generatedFeasibleSixthSlotPrototype,
    generatedFeasibleSeventhSlotPrototype,
    generatedFeasibleRootEightSlotPrototype]

/-- The actual local stabilizer orbit sizes of the ten witnesses. -/
def generatedFeasibleAmbientT4Size : Fin 10 → ℕ :=
  ![1, 93150, 7286400, 262310400, 4196966400, 470060236800, 537211699200, 9646899200,
    6685301145600, 4000762036224]

private theorem triality_fix :
    extraIntoGenerated.val (conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 0 := by
  change sExtra (conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 0) = _
  rw [conwayShortAxis_pair_zero, conwayAxis_triality]

/-- A generated element fixing the first axis preserves the actual feasible vectors. -/
theorem generatedFeasibleAmbientT4_word (k : G)
    (hk : k.val (conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 0) =
      conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 0)
    (x : GriessSpace)
    (hx : x ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 0)
      (conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 1)) :
    k.val x ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 0)
      (conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 1) := by
  obtain ⟨a, ha⟩ := hx
  have hfix := a.property
  change a.val.val (conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 0) =
    conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 0 at hfix
  refine ⟨⟨k * a.val, ?_⟩, ?_⟩
  · change k.val (a.val.val _) = _
    rw [hfix, hk]
  · change k.val (a.val.val _) = k.val x
    change a.val.val _ = x at ha
    rw [ha]

/-- The containing-octad destination is an actual feasible vector. -/
theorem generatedFeasibleAmbientT4_containing_mem :
    generatedFeasibleContainingOctadDestination ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 0)
      (conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 1) := by
  have hs := generatedFeasibleSecondaryNonPair_axis_mem 0
    generatedFeasibleContainingOctadPrototypeLabel
    generatedFeasibleContainingOctadPrototypeLabel_mem 0
  have hbase := generatedFeasibleSecondaryLocalOrbit_subset generatedFeasiblePhysicalRootPair hs
  exact generatedFeasibleAmbientT4_word extraIntoGenerated triality_fix _ hbase

/-- The outside-octad destination is an actual feasible vector. -/
theorem generatedFeasibleAmbientT4_outside_mem :
    generatedFeasibleOutsideOctadDestination ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 0)
      (conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 1) := by
  have hs := generatedFeasibleSecondaryNonPair_axis_mem 1
    generatedFeasibleOutsideOctadPrototypeLabel
    generatedFeasibleOutsideOctadPrototypeLabel_mem 0
  have hbase := generatedFeasibleSecondaryLocalOrbit_subset generatedFeasiblePhysicalRootPair hs
  exact generatedFeasibleAmbientT4_word extraIntoGenerated triality_fix _ hbase

/-- All ten witnesses are actual feasible vectors. -/
theorem generatedFeasibleAmbientT4_witness_mem (j : Fin 10) :
    generatedFeasibleAmbientT4Witness j ∈ generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 0)
      (conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 1) := by
  fin_cases j
  · exact MulAction.mem_orbit_self _
  · exact generatedFeasibleSecondaryLocalOrbit_subset _ (MulAction.mem_orbit_self _)
  · exact generatedFeasibleAmbientT4_containing_mem
  · exact generatedFeasibleAmbientT4_outside_mem
  · exact generatedFeasibleContainingSixteenDestination_feasible
  · exact generatedFeasibleContainingNewDestination_feasible
  · exact generatedFeasibleFifthSlotPrototype_feasible
  · exact generatedFeasibleSixthSlotPrototype_feasible
  · exact generatedFeasibleSeventhSlotPrototype_feasible
  · exact generatedFeasibleRootEightSlotPrototype_feasible

/-- The actual local stabilizer orbit sizes of the ten witnesses. -/
theorem generatedFeasibleAmbientT4_witness_card (j : Fin 10) :
    Nat.card (MulAction.orbit (localAxisStabilizer generatedFeasibleAmbientT4Pair)
      (generatedFeasibleAmbientT4Witness j)) = generatedFeasibleAmbientT4Size j := by
  fin_cases j
  · exact generatedFeasibleActualOrbit_first_card _
  · exact generatedFeasibleSecondaryLocalOrbit_card _
  · exact generatedFeasibleContainingOctad_actual_A_orbit_card
  · exact generatedFeasibleOutsideOctad_actual_A_orbit_card
  · exact generatedFeasibleContainingSixteen_actual_A_orbit_card
  · exact generatedFeasibleContainingEighth_actual_A_orbit_card
  · exact generatedFeasibleFifthSlot_actual_A_orbit_card
  · exact generatedFeasibleSixthSlot_actual_A_orbit_card
  · exact generatedFeasibleSeventhSlot_actual_A_orbit_card
  · exact generatedFeasibleRootEightSlot_actual_A_orbit_card

theorem generatedFeasibleAmbientT4_size_injective :
    Function.Injective generatedFeasibleAmbientT4Size := by
  decide

theorem generatedFeasibleAmbientT4_size_sum :
    11707448673375 ≤ ∑ j, generatedFeasibleAmbientT4Size j := by
  simp only [generatedFeasibleAmbientT4Size, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

/-- The First, Octad and Odd coverages are closed; the other nine are the inputs. -/
theorem generatedFeasibleAmbientT4_covered
    (hcov : ∀ i ∈ ({3, 4, 5, 6, 7, 8, 9, 10, 11} : Finset (Fin 12)),
      GeneratedAxisGlobalTwelveFamilyCovered i) (i : Fin 12) :
    GeneratedAxisGlobalTwelveFamilyCovered i := by
  by_cases h0 : i = 0
  · subst h0
    exact generatedAxisGlobalTwelve_first_covered
  by_cases h1 : i = 1
  · subst h1
    exact generatedAxisGlobalTwelve_octad_covered
  by_cases h2 : i = 2
  · subst h2
    exact generatedAxisGlobalTwelve_odd_covered
  exact hcov i (by fin_cases i <;> simp_all)

/-- The actual feasible count from the coverages of families 3 to 11 and the Root8 and Tenth
orthogonal axis counts, all as explicit hypotheses. -/
theorem generatedFeasibleAmbientT4_feasible_card
    (hcov : ∀ i ∈ ({3, 4, 5, 6, 7, 8, 9, 10, 11} : Finset (Fin 12)),
      GeneratedAxisGlobalTwelveFamilyCovered i)
    (hroot : generatedFeasibleAmbientAxisZeroCount generatedFifthRootEightAxis ≤ 1)
    (htenth : generatedFeasibleAmbientAxisZeroCount generatedTenthAxis ≤ 0) :
    Nat.card (generatedFeasibleVectorOrbit
      (conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 0)
      (conwayShortAxis (Sum.inl (0, generatedFeasibleAmbientT4Pair)) 1)) = 11707448673375 :=
  generatedFeasibleAmbient_twelve_feasible_card
    (generatedAxisGlobalTwelveCounted_of_tenth generatedTenth_actual_local_axis_stabilizer_card)
    (generatedFeasibleAmbientT4_covered hcov)
    generatedFeasibleAmbientAxisZeroCount_eighth.le hroot htenth generatedFeasibleAmbientT4Pair
    generatedFeasibleAmbientT4Witness generatedFeasibleAmbientT4Size
    generatedFeasibleAmbientT4_witness_mem generatedFeasibleAmbientT4_witness_card
    generatedFeasibleAmbientT4_size_injective generatedFeasibleAmbientT4_size_sum

/-- The Monster order of the generated group, from the coverages of families 3 to 11 and the
Root8 and Tenth orthogonal axis counts only, all as explicit hypotheses. -/
theorem generatedFeasibleAmbientT4_order
    (hcov : ∀ i ∈ ({3, 4, 5, 6, 7, 8, 9, 10, 11} : Finset (Fin 12)),
      GeneratedAxisGlobalTwelveFamilyCovered i)
    (hroot : generatedFeasibleAmbientAxisZeroCount generatedFifthRootEightAxis ≤ 1)
    (htenth : generatedFeasibleAmbientAxisZeroCount generatedTenthAxis ≤ 0) :
    Nat.card ↥G =
      2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 *
      17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71 :=
  generatedAxisGlobalTwelve_order_of_families generatedTenth_actual_local_axis_stabilizer_card
    (fun i _ => generatedFeasibleAmbientT4_covered hcov i) generatedFeasibleAmbientT4Pair
    (generatedFeasibleAmbientT4_feasible_card hcov hroot htenth)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
