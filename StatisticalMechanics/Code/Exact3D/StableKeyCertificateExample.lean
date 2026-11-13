/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.StableKeyCertificate














namespace StatMech
namespace Exact3D
namespace BoundedPolymerCase
namespace StableKeyCertificateExample

open StatMech.Lattice


def zeroInterval : RatInterval :=
  RatInterval.point 0


def rowOfKey {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) :
    StableKeyIntervalRow maxDegree maxRange :=
  StableKeyIntervalRow.ofKey (fun _ => zeroInterval) k


theorem rowOfKey_memR_zero {maxDegree maxRange : ℕ}
    (k : StableKey maxDegree maxRange) :
    (rowOfKey k).interval.MemR (0 : ℝ) := by
  simp [rowOfKey, zeroInterval, RatInterval.point, RatInterval.MemR]



theorem mem_rowKeyFinset_map_rowOfKey {maxDegree maxRange : ℕ}
    (s : Finset (StableKey maxDegree maxRange))
    (k : StableKey maxDegree maxRange) :
    k ∈ stableKeyIntervalRowKeyFinset (s.toList.map rowOfKey) ↔ k ∈ s := by
  classical
  simpa [rowOfKey] using
    StableKeyIntervalRow.mem_keyFinset_map_ofKeyInterval
      s (fun _ => zeroInterval) k


noncomputable def rawRows (d R maxDegree maxRange : ℕ) :
    List (StableKeyIntervalRow maxDegree maxRange) :=
  StableKeyIntervalRow.rowsOfKeys
    ((exhaustiveTable d R maxDegree maxRange).image stableKey)
    (fun _ => zeroInterval)


noncomputable def minimalCubicRows (d R maxDegree maxRange : ℕ) :
    List (StableKeyIntervalRow maxDegree maxRange) :=
  StableKeyIntervalRow.rowsOfKeys
    ((exhaustiveCubicClassTable d R maxDegree maxRange).image
      minimalCubicStableKey)
    (fun _ => zeroInterval)



theorem rawRows_exactKeySet (d R maxDegree maxRange : ℕ) :
    StableKeyIntervalRow.ExactKeySet
      (rawRows d R maxDegree maxRange)
      ((exhaustiveTable d R maxDegree maxRange).image stableKey) := by
  simpa [rawRows] using
    StableKeyIntervalRow.exactKeySet_rowsOfKeys
      ((exhaustiveTable d R maxDegree maxRange).image stableKey)
      (fun _ => zeroInterval)



theorem minimalCubicRows_exactKeySet (d R maxDegree maxRange : ℕ) :
    StableKeyIntervalRow.ExactKeySet
      (minimalCubicRows d R maxDegree maxRange)
      ((exhaustiveCubicClassTable d R maxDegree maxRange).image
        minimalCubicStableKey) := by
  simpa [minimalCubicRows] using
    StableKeyIntervalRow.exactKeySet_rowsOfKeys
      ((exhaustiveCubicClassTable d R maxDegree maxRange).image
        minimalCubicStableKey)
      (fun _ => zeroInterval)


theorem rawRows_cover (d R maxDegree maxRange : ℕ)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    stableKey c ∈ stableKeyIntervalRowKeyFinset (rawRows d R maxDegree maxRange) := by
  classical
  rw [rawRows]
  exact (StableKeyIntervalRow.mem_keyFinset_rowsOfKeys _ _ (stableKey c)).2
    (Finset.mem_image.mpr
      ⟨c, exhaustiveTable_covers d R maxDegree maxRange c, rfl⟩)


theorem minimalCubicRows_cover (d R maxDegree maxRange : ℕ)
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    classifyByMinimalCubicStableKey c ∈
      stableKeyIntervalRowKeyFinset (minimalCubicRows d R maxDegree maxRange) := by
  classical
  rw [minimalCubicRows]
  exact
    (StableKeyIntervalRow.mem_keyFinset_rowsOfKeys _
      _ (classifyByMinimalCubicStableKey c)).2
    (Finset.mem_image.mpr
      ⟨cubicClass c, exhaustiveCubicClassTable_covers d R maxDegree maxRange c, rfl⟩)


theorem rawRows_row_key_mem_generatedKeys (d R maxDegree maxRange : ℕ)
    {row : StableKeyIntervalRow maxDegree maxRange}
    (hrow : row ∈ rawRows d R maxDegree maxRange) :
    row.key.toKey ∈
      (exhaustiveTable d R maxDegree maxRange).image stableKey :=
  StableKeyIntervalRow.row_key_mem_expected_of_exactKeySet
    (rawRows_exactKeySet d R maxDegree maxRange) hrow



theorem minimalCubicRows_row_key_mem_generatedKeys
    (d R maxDegree maxRange : ℕ)
    {row : StableKeyIntervalRow maxDegree maxRange}
    (hrow : row ∈ minimalCubicRows d R maxDegree maxRange) :
    row.key.toKey ∈
      (exhaustiveCubicClassTable d R maxDegree maxRange).image
        minimalCubicStableKey :=
  StableKeyIntervalRow.row_key_mem_expected_of_exactKeySet
    (minimalCubicRows_exactKeySet d R maxDegree maxRange) hrow



theorem minimalCubicRows_cover_cubicTransformLocalCoordinate
    {d R maxDegree maxRange : ℕ}
    (c : LocalPolymerCoordinate d) (v : Site d)
    (σ : Equiv.Perm (Fin d))
    (ε : PolymerSupport.CoordinateReflection d)
    (hbox : c.support.containedInBox R)
    (hbox' :
      (cubicTransformLocalCoordinate c v σ ε).support.containedInBox R)
    (hdegree : c.degree ≤ maxDegree)
    (hrange : c.range ≤ maxRange) :
    classifyByMinimalCubicStableKey
        (ofLocalCoordinate (cubicTransformLocalCoordinate c v σ ε)
          hbox' (by simpa using hdegree) (by simpa using hrange)) ∈
      stableKeyIntervalRowKeyFinset
        (minimalCubicRows d R maxDegree maxRange) := by
  rw [← classifyByMinimalCubicStableKey_ofLocalCoordinate_cubicTransform
    c v σ ε hbox hbox' hdegree hrange]
  exact minimalCubicRows_cover d R maxDegree maxRange
    (ofLocalCoordinate c hbox hdegree hrange)


theorem rawRows_row_sound (d R maxDegree maxRange : ℕ)
    (row : StableKeyIntervalRow maxDegree maxRange)
    (hrow : row ∈ rawRows d R maxDegree maxRange) :
    row.interval.MemR (0 : ℝ) := by
  exact StableKeyIntervalRow.memR_of_mem_rowsOfKeys
    ((exhaustiveTable d R maxDegree maxRange).image stableKey)
    (fun _ => zeroInterval) (fun _ => (0 : ℝ))
    (fun _ _ => by
      simp [zeroInterval, RatInterval.point, RatInterval.MemR])
    (by simpa [rawRows] using hrow)


theorem minimalCubicRows_row_sound (d R maxDegree maxRange : ℕ)
    (row : StableKeyIntervalRow maxDegree maxRange)
    (hrow : row ∈ minimalCubicRows d R maxDegree maxRange) :
    row.interval.MemR (0 : ℝ) := by
  exact StableKeyIntervalRow.memR_of_mem_rowsOfKeys
    ((exhaustiveCubicClassTable d R maxDegree maxRange).image
      minimalCubicStableKey)
    (fun _ => zeroInterval) (fun _ => (0 : ℝ))
    (fun _ _ => by
      simp [zeroInterval, RatInterval.point, RatInterval.MemR])
    (by simpa [minimalCubicRows] using hrow)


theorem rawRows_zero_covers_and_sound_boundedLocal
    (d R maxDegree maxRange : ℕ) :
    RatInterval.CaseTable.Covers
        (externalStableKeyIntervalRowTable
          (rawRows d R maxDegree maxRange) zeroInterval)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          stableKey (classifyBoundedLocalCoordinate c)) ∧
      RatInterval.CaseTable.Sound
        (externalStableKeyIntervalRowTable
          (rawRows d R maxDegree maxRange) zeroInterval)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          stableKey (classifyBoundedLocalCoordinate c))
        (fun _ => (0 : ℝ)) := by
  exact externalStableKeyIntervalRows_covers_and_sound_boundedLocal_of_keyValue
    (rawRows d R maxDegree maxRange) zeroInterval (fun _ => (0 : ℝ))
    (fun _ => (0 : ℝ))
    (rawRows_cover d R maxDegree maxRange)
    (fun _ => rfl)
    (rawRows_row_sound d R maxDegree maxRange)



theorem minimalCubicRows_zero_covers_and_sound_boundedLocal
    (d R maxDegree maxRange : ℕ) :
    RatInterval.CaseTable.Covers
        (externalStableKeyIntervalRowTable
          (minimalCubicRows d R maxDegree maxRange) zeroInterval)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c)) ∧
      RatInterval.CaseTable.Sound
        (externalStableKeyIntervalRowTable
          (minimalCubicRows d R maxDegree maxRange) zeroInterval)
        (fun c : BoundedLocalCoordinate d R maxDegree maxRange =>
          classifyByMinimalCubicStableKey (classifyBoundedLocalCoordinate c))
        (fun _ => (0 : ℝ)) := by
  exact externalStableKeyIntervalRows_covers_and_sound_minimalCubicBoundedLocal_of_keyValue
    (minimalCubicRows d R maxDegree maxRange) zeroInterval (fun _ => (0 : ℝ))
    (fun _ => (0 : ℝ))
    (minimalCubicRows_cover d R maxDegree maxRange)
    (fun _ => rfl)
    (minimalCubicRows_row_sound d R maxDegree maxRange)

end StableKeyCertificateExample
end BoundedPolymerCase
end Exact3D
end StatMech
