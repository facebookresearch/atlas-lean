/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisCountedLocalOrbits
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthLocalOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthLocalOrder
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhExact
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthLocalOrder
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthThreeAxisFixation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOrbitCoverage

/-! The twelve literal local axis representatives in the order of Höhn--Seysen,
arXiv:2508.01037, Table 1: First, Octad, Odd, Fourth, Fifth, Sixth, Seventh, Eighth,
Ninth, Root8, Twelfth and Tenth.

Every representative is a literal generated-group word applied to a signed-short axis.
The local orbit lengths of nine families are proved here from the existing closed local
counts; the Ninth, Root8 and Tenth lengths enter only through the explicit predicate
`GeneratedAxisGlobalTwelveCounted`. Disjointness, the disjoint-union cardinality and the
global orbit length are then derived. Triality coverage of the union is the explicit
per-family predicate `GeneratedAxisGlobalTwelveFamilyCovered`; it is not asserted here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The twelve literal local representatives, in source Table 1 order. -/
def generatedAxisGlobalTwelveRepresentative : Fin 12 → GriessSpace :=
  ![conwayShortAxis (Sum.inl (0, 0)) 0, generatedOctadLocalAxis 0 0, generatedOddAxis,
    generatedFourthAxis, generatedFifthAxis, generatedSixthAxis, generatedSeventhAxis,
    generatedEighthAxis, generatedNinthAxis, generatedFifthRootEightAxis,
    generatedTwelfthAxis, generatedTenthAxis]

/-- The source Table 1 local orbit lengths, in the same order. -/
def generatedAxisGlobalTwelveCount : Fin 12 → ℕ :=
  ![196560, 11935123200, 1630347264000, 1466587938816000, 6599645724672000,
    1896194506752000, 438020931059712000, 8601138282627072000, 1501786049347584000,
    786389785840189440, 37845008443559116800, 48057153579122688000]

/-- The genuine H orbit of each literal representative. -/
def generatedAxisGlobalTwelveOrbit (i : Fin 12) : Set GriessSpace :=
  MulAction.orbit H (generatedAxisGlobalTwelveRepresentative i)

/-- The twelve source lengths add up to the source global axis count. -/
theorem generatedAxisGlobalTwelveCount_sum :
    ∑ i, generatedAxisGlobalTwelveCount i = 97239461142009186000 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, generatedAxisGlobalTwelveCount]
  norm_num

/-- The twelve source lengths are pairwise different. -/
theorem generatedAxisGlobalTwelveCount_injective :
    Function.Injective generatedAxisGlobalTwelveCount := by
  decide +kernel

/-- Every representative lies in the actual global orbit of every signed-short axis. -/
theorem generatedAxisGlobalTwelveRepresentative_mem_generated (i : Fin 12)
    (r : GriessShortIndex) (c : ZMod 2) :
    generatedAxisGlobalTwelveRepresentative i ∈ generatedVectorOrbit (conwayShortAxis r c) := by
  fin_cases i
  · exact generatedCountedAxisRepresentative_mem_generated 0 r c
  · exact generatedCountedAxisRepresentative_mem_generated 1 r c
  · exact generatedCountedAxisRepresentative_mem_generated 2 r c
  · exact generatedCountedAxisRepresentative_mem_generated 3 r c
  · exact generatedFifthAxis_mem_generatedOrbit r c
  · exact generatedSixthAxis_mem_generatedOrbit r c
  · exact generatedSeventhAxis_mem_generatedOrbit r c
  · exact generatedEighthAxis_mem_generatedOrbit r c
  · exact generatedNinthAxis_mem_generatedOrbit r c
  · exact generatedFifthRootEightAxis_mem_generatedOrbit r c
  · exact generatedTwelfthAxis_mem_generatedOrbit r c
  · exact generatedTenthAxis_mem_generatedOrbit r c

/-- The closed Twelfth stabilizer order gives the exact Twelfth local orbit length. -/
theorem generatedAxisGlobalTwelve_twelfth_orbit_card :
    Nat.card (MulAction.orbit H generatedTwelfthAxis) = 37845008443559116800 := by
  have h := generatedTwelfthLocalAxisStabilizer.card_mul_index
  rw [generatedTwelfth_three_closed_actual_local_axis_stabilizer_card, local_h_card_exact] at h
  have hi : generatedTwelfthLocalAxisStabilizer.index = 37845008443559116800 := by omega
  rw [generatedTwelfthLocalAxisStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at hi
  exact hi

/-- The Tenth stabilizer order, once proved, gives the exact Tenth local orbit length. -/
theorem generatedAxisGlobalTwelve_tenth_orbit_card
    (htenth : Nat.card (MulAction.stabilizer H generatedTenthAxis) = 2903040) :
    Nat.card (MulAction.orbit H generatedTenthAxis) = 48057153579122688000 := by
  have h := (MulAction.stabilizer H generatedTenthAxis).card_mul_index
  rw [htenth, local_h_card_exact] at h
  have hi : (MulAction.stabilizer H generatedTenthAxis).index = 48057153579122688000 := by
    omega
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at hi
  exact hi

/-- The eleven lengths other than Tenth, with the Ninth and Root8 inputs explicit. -/
theorem generatedAxisGlobalTwelve_card_of_ne_tenth
    (hninth : Nat.card (MulAction.orbit H generatedNinthAxis) = 1501786049347584000)
    (hroot : Nat.card (MulAction.orbit H generatedFifthRootEightAxis) = 786389785840189440)
    (i : Fin 12) (hi : i ≠ 11) :
    Nat.card (generatedAxisGlobalTwelveOrbit i) = generatedAxisGlobalTwelveCount i := by
  fin_cases i
  · exact generatedCountedAxisOrbit_card 0
  · exact generatedCountedAxisOrbit_card 1
  · exact generatedCountedAxisOrbit_card 2
  · exact generatedCountedAxisOrbit_card 3
  · exact generatedFifth_local_axis_orbit_card
  · exact generatedSixth_local_axis_orbit_card
  · exact generatedSeventhLocalAxisOrbit_card
  · exact generatedEighth_local_axis_orbit_card
  · exact hninth
  · exact hroot
  · exact generatedAxisGlobalTwelve_twelfth_orbit_card
  · exact absurd rfl hi

/-- All twelve exact local orbit lengths. -/
def GeneratedAxisGlobalTwelveCounted : Prop :=
  ∀ i, Nat.card (generatedAxisGlobalTwelveOrbit i) = generatedAxisGlobalTwelveCount i

/-- Nine lengths are already closed; the Ninth, Root8 and Tenth inputs are explicit. -/
theorem generatedAxisGlobalTwelveCounted_of
    (hninth : Nat.card (MulAction.orbit H generatedNinthAxis) = 1501786049347584000)
    (hroot : Nat.card (MulAction.orbit H generatedFifthRootEightAxis) = 786389785840189440)
    (htenth : Nat.card (MulAction.stabilizer H generatedTenthAxis) = 2903040) :
    GeneratedAxisGlobalTwelveCounted := by
  intro i
  by_cases hi : i = 11
  · subst hi
    exact generatedAxisGlobalTwelve_tenth_orbit_card htenth
  · exact generatedAxisGlobalTwelve_card_of_ne_tenth hninth hroot i hi

/-- Exact lengths force the twelve actual local orbits to be pairwise disjoint. -/
theorem generatedAxisGlobalTwelveOrbit_pairwise_disjoint (hc : GeneratedAxisGlobalTwelveCounted) :
    Pairwise (fun i j => Disjoint (generatedAxisGlobalTwelveOrbit i)
      (generatedAxisGlobalTwelveOrbit j)) := by
  intro i j hij
  refine (MulAction.orbit.eq_or_disjoint (generatedAxisGlobalTwelveRepresentative i)
    (generatedAxisGlobalTwelveRepresentative j)).resolve_left ?_
  intro he
  apply hij
  apply generatedAxisGlobalTwelveCount_injective
  have hn := congrArg (fun s : Set GriessSpace => Nat.card s) he
  change Nat.card (generatedAxisGlobalTwelveOrbit i) = Nat.card (generatedAxisGlobalTwelveOrbit j)
    at hn
  rw [hc i, hc j] at hn
  exact hn

/-- The union of actual local orbits is the indexed union of the twelve orbits. -/
theorem generatedAxisGlobalTwelve_union_eq_iUnion :
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative =
      ⋃ i, generatedAxisGlobalTwelveOrbit i := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, h, hh⟩
    exact ⟨i, h, hh⟩
  · rintro ⟨i, h, hh⟩
    exact ⟨i, h, hh⟩

/-- The disjoint union of the twelve actual local orbits has the source global length. -/
theorem generatedAxisGlobalTwelve_union_card (hc : GeneratedAxisGlobalTwelveCounted) :
    Nat.card (generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) =
      97239461142009186000 := by
  have hfin (i : Fin 12) : Finite (generatedAxisGlobalTwelveOrbit i) := by
    apply Nat.finite_of_card_ne_zero
    rw [hc i]
    fin_cases i <;> decide
  rw [generatedAxisGlobalTwelve_union_eq_iUnion,
    Nat.card_congr (Set.unionEqSigmaOfDisjoint
      (generatedAxisGlobalTwelveOrbit_pairwise_disjoint hc)),
    Nat.card_sigma]
  exact (Finset.sum_congr rfl fun i _ => hc i).trans generatedAxisGlobalTwelveCount_sum

/-- Triality coverage of one listed family by the twelve-family union. -/
def GeneratedAxisGlobalTwelveFamilyCovered (i : Fin 12) : Prop :=
  ∀ h : H, sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative i)) ∈
    generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative

/-- An explicit local transport to a listed representative gives union membership. -/
theorem generatedAxisGlobalTwelve_mem_of_transport {y : GriessSpace} (j : Fin 12) (h : H)
    (hy : y = rhoLocal h (generatedAxisGlobalTwelveRepresentative j)) :
    y ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  ⟨j, h, hy.symm⟩

/-- Equality of actual local classes with a listed representative gives union membership. -/
theorem generatedAxisGlobalTwelve_mem_of_class {y : GriessSpace} (j : Fin 12)
    (hy : Quotient.mk (MulAction.orbitRel H GriessSpace) y =
      Quotient.mk (MulAction.orbitRel H GriessSpace) (generatedAxisGlobalTwelveRepresentative j)) :
    y ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  (generatedAxisGlobal_mem_union_iff _ _).mpr ⟨j, hy⟩

/-- The actual octad-image class is the class of the listed Octad representative. -/
theorem generatedAxisGlobalTwelve_octad_destination :
    Quotient.mk (MulAction.orbitRel H GriessSpace) (generatedAxisGlobalTwelveRepresentative 1) =
      generatedAxisOctadDestination :=
  (generatedAxis_triality_octad_class_iff _ _).mpr ⟨generatedOctadBasisOctad, 0, rfl⟩

/-- Every vector with the actual octad-image class lies in the twelve-family union. -/
theorem generatedAxisGlobalTwelve_mem_of_octad_class {y : GriessSpace}
    (hy : Quotient.mk (MulAction.orbitRel H GriessSpace) y = generatedAxisOctadDestination) :
    y ∈ generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelve_mem_of_class 1
    (hy.trans generatedAxisGlobalTwelve_octad_destination.symm)

/-- Coverage of all twelve families is triality invariance of the union. -/
theorem generatedAxisGlobalTwelve_triality_of_covered
    (hcov : ∀ i, GeneratedAxisGlobalTwelveFamilyCovered i) :
    Set.MapsTo sExtra (generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
      (generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) := by
  rintro x ⟨i, h, rfl⟩
  exact hcov i h

/-- Under twelve-family coverage the actual global orbit is exactly the union. -/
theorem generatedAxisGlobalTwelve_orbit_eq_union
    (hcov : ∀ i, GeneratedAxisGlobalTwelveFamilyCovered i) (p : Fin 276) :
    generatedVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0) =
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative := by
  apply generatedVectorOrbit_eq_localOrbitUnion
  · obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive (Sum.inl (0, 0)) (Sum.inl (0, p)) 0 0
    exact ⟨0, h, hh⟩
  · intro i
    exact generatedAxisGlobalTwelveRepresentative_mem_generated i _ _
  · exact generatedAxisGlobalTwelve_triality_of_covered hcov

/-- The global axis length from exact local lengths and twelve-family coverage. -/
theorem generatedAxisGlobalTwelve_axis_card (hc : GeneratedAxisGlobalTwelveCounted)
    (hcov : ∀ i, GeneratedAxisGlobalTwelveFamilyCovered i) (p : Fin 276) :
    Nat.card (generatedVectorOrbit (conwayShortAxis (Sum.inl (0, p)) 0)) =
      97239461142009186000 := by
  rw [generatedAxisGlobalTwelve_orbit_eq_union hcov p]
  exact generatedAxisGlobalTwelve_union_card hc

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
