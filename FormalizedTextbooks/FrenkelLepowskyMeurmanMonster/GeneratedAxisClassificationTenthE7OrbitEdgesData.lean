/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OrbitMonomialFlag
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootCatalogueSection

/-! Complete original root-orbit addresses for the genuine two-generator E7 orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option maxRecDepth 100000

/-- The original finite root addresses in earlier-parent traversal order. -/
def generatedTenthE7OrbitOrder : Fin 63 → Fin 63 :=
  ![14, 10, 33, 13, 9, 47, 43, 1, 20, 60, 50, 32,
    8, 28, 58, 3, 45, 34, 62, 21, 49, 36, 16, 39,
    27, 15, 35, 30, 5, 59, 38, 46, 40, 0, 6, 12,
    31, 4, 23, 53, 37, 18, 57, 26, 29, 22, 54, 48,
    17, 55, 44, 7, 2, 11, 56, 19, 61, 24, 25, 52,
    41, 42, 51]

/-- The original incoming parent address for every traversal node. -/
def generatedTenthE7OrbitParent : Fin 63 → Fin 63 :=
  ![0, 0, 1, 1, 2, 2, 3, 3, 4, 5, 6, 6,
    7, 7, 8, 8, 9, 10, 10, 11, 11, 12, 12, 13,
    13, 14, 14, 15, 16, 16, 17, 17, 18, 19, 19, 20,
    20, 22, 22, 23, 24, 24, 26, 27, 28, 28, 29, 29,
    30, 30, 31, 33, 34, 35, 36, 37, 39, 45, 50, 51,
    54, 55, 59]

/-- The genuine correcting Xi or monomial letter on each incoming edge. -/
def generatedTenthE7OrbitLetter : Fin 63 → Fin 2 :=
  ![0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1,
    0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0,
    1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0,
    1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0,
    0, 0, 0]

/-- The exact full integral orientation of each incoming source root. -/
def generatedTenthE7OrbitSign : Fin 63 → ℤ :=
  ![1, -1, -1, 1, 1, 1, 1, -1, -1, 1, 1, -1,
    -1, -1, 1, 1, 1, -1, -1, 1, 1, 1, -1, 1,
    1, 1, 1, -1, -1, 1, -1, -1, -1, -1, -1, -1,
    1, -1, -1, 1, -1, 1, 1, 1, 1, -1, 1, -1,
    1, 1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1,
    -1, 1, 1]

/-- Every incoming parent genuinely precedes its noninitial node. -/
theorem generatedTenth_e7_orbit_parent_lt : ∀ n : Fin 63, n ≠ 0 →
    (generatedTenthE7OrbitParent n).val < n.val := by
  decide +kernel

/-- The entire original traversal contains every finite root address exactly once. -/
theorem generatedTenth_e7_orbit_order_injective :
    Function.Injective generatedTenthE7OrbitOrder := by
  decide +kernel

/-- The entire original traversal is a bijection, with no coverage hypothesis. -/
def generatedTenthE7OrbitOrderEquiv : Fin 63 ≃ Fin 63 :=
  Equiv.ofBijective generatedTenthE7OrbitOrder
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨generatedTenth_e7_orbit_order_injective, rfl⟩)

/-- Complete physical integral root coordinates at each original traversal address. -/
def generatedTenthE7OrbitNodeVector (n : Fin 63) : Fin 24 → ℤ :=
  generatedTenthE7RootCatalogueInsert (leechSeventhE8RootLocal
    (generatedTenthE7OrbitRootIndex (generatedTenthE7OrbitOrder n)))

/-- The two genuine full-source physical matrices, retaining the Xi denominator. -/
def generatedTenthE7OrbitLetterNumerator (k : Fin 2) : Matrix (Fin 24) (Fin 24) ℤ :=
  if k = 0 then generatedTenthE7XiCorrectedNumerator else generatedTenthE7OrbitMonoMatrix

/-- Original physical denominators of the two genuine isometries. -/
def generatedTenthE7OrbitLetterDenominator (k : Fin 2) : ℤ := if k = 0 then 2 else 1

/-- The unchanged complete incoming integer-source condition for each original root address. -/
def generatedTenthE7OrbitEdgeCondition (n : Fin 63) : Prop :=
  generatedTenthE7OrbitLetterNumerator (generatedTenthE7OrbitLetter n) *ᵥ
      generatedTenthE7OrbitNodeVector (generatedTenthE7OrbitParent n) =
    (generatedTenthE7OrbitLetterDenominator (generatedTenthE7OrbitLetter n) *
      generatedTenthE7OrbitSign n) • generatedTenthE7OrbitNodeVector n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
