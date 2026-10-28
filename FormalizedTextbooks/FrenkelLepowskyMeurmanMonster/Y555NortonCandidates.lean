/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Sixteen concrete candidate reflections in the actual G wreath C2.
The labels are the Y555 subdiagram of Norton's projective-plane construction:
center P0; arms L0,P1,L8,P5,L4; L1,P2,L7,P7,L6; L3,P11,L5,P4,L10.
Source: Norton (2002), reproduced in Farooq's thesis pp.69–82, and pinned public
mmgroup bimm/bimm.py at commit 728688938a1c9fd27f3aee9b63464ea6b8d17965.
All involution relations below hold for any actual tau. The source comparison of tau,
the remaining Coxeter and spider relations, generation and recognition remain open.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555NortonU
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555NortonV
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555NortonPoints
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555WreathGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Source right conjugation, evaluated as an actual group word in G. -/
noncomputable def y555NortonConjugate (g h : ↥G) : ↥G := h⁻¹ * g * h

/-- A normalized line parameter; its label uses the source projective-plane numbering. -/
noncomputable def y555NortonLine (tau : ↥G) (i : Fin 13) : ↥G :=
  y555NortonV * (y555NortonConjugate (y555NortonV * tau) (y555NortonU tau ^ i.val))⁻¹

/-- The three line labels on each arm, from the center outwards. -/
def y555NortonLineLabels : Fin 3 → Fin 3 → Fin 13 :=
  ![![0, 8, 4], ![1, 7, 6], ![3, 5, 10]]

/-- The first coordinate of each candidate outer involution, in the named group. -/
noncomputable def y555NortonParameter (tau : ↥G) : Y555Vertex → ↥G
  | none => 1
  | some (a, d) => match d with
    | 0 => y555NortonLine tau (y555NortonLineLabels a 0)
    | 1 => y555NortonPoint ⟨a.val, by omega⟩
    | 2 => y555NortonLine tau (y555NortonLineLabels a 1)
    | 3 => y555NortonPoint ⟨a.val + 3, by omega⟩
    | _ => y555NortonLine tau (y555NortonLineLabels a 2)

/-- The complete candidate family consists of explicit elements of the actual wreath product. -/
noncomputable def y555NortonCandidate (tau : ↥G) (v : Y555Vertex) : ↥G ≀ᵣ WreathParity :=
  y555WreathReflection (y555NortonParameter tau v)

/-- Every candidate satisfies its involution relation in the actual wreath product. -/
theorem y555NortonCandidate_square (tau : ↥G) (v : Y555Vertex) :
    y555NortonCandidate tau v ^ 2 = 1 := y555WreathReflection_sq _

/-- The distinguished candidate is exactly the factor swap. -/
theorem y555NortonCandidate_center (tau : ↥G) :
    y555NortonCandidate tau none = wreathSwap ↥G := y555WreathReflection_one

/-- The six point vertices, ordered c1,c2,c3,e1,e2,e3. -/
def y555NortonPointVertex (i : Fin 6) : Y555Vertex :=
  some (⟨i.val % 3, Nat.mod_lt _ (by decide)⟩, if i.val < 3 then 1 else 3)

/-- The point vertices use the already verified actual extraspecial parameters. -/
theorem y555NortonParameter_point (tau : ↥G) (i : Fin 6) :
    y555NortonParameter tau (y555NortonPointVertex i) = y555NortonPoint i := by
  fin_cases i <;> rfl

/-- The actual point parameters obey every required pairwise order-two word check. -/
theorem y555NortonPoint_pair_square (i j : Fin 6) :
    (y555NortonPoint i * (y555NortonPoint j)⁻¹) ^ 2 = 1 := by
  have hi : (y555NortonPoint j)⁻¹ = y555NortonPoint j := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two, y555NortonPoint_sq]
  rw [hi, (show Commute (y555NortonPoint i) (y555NortonPoint j) from
    y555NortonPoint_commute i j).mul_pow, y555NortonPoint_sq, y555NortonPoint_sq, one_mul]

/-- The six point reflections satisfy their pairwise Coxeter relations in the actual wreath. -/
theorem y555NortonCandidate_points_square (tau : ↥G) (i j : Fin 6) :
    (y555NortonCandidate tau (y555NortonPointVertex i) *
      y555NortonCandidate tau (y555NortonPointVertex j)) ^ 2 = 1 := by
  apply (y555WreathReflection_mul_pow _ _ _).mpr
  rw [y555NortonParameter_point, y555NortonParameter_point]
  exact y555NortonPoint_pair_square i j

/-- Each point reflection commutes with the central swap, as its diagram requires. -/
theorem y555NortonCandidate_center_point_square (tau : ↥G) (i : Fin 6) :
    (y555NortonCandidate tau none *
      y555NortonCandidate tau (y555NortonPointVertex i)) ^ 2 = 1 := by
  apply (y555WreathReflection_mul_pow _ _ _).mpr
  change (1 * (y555NortonParameter tau (y555NortonPointVertex i))⁻¹) ^ 2 = 1
  rw [one_mul, y555NortonParameter_point, inv_pow, y555NortonPoint_sq, inv_one]

/-- A Coxeter check for these concrete candidates is exactly a word check in the named G. -/
theorem y555NortonCandidate_coxeter_iff (tau : ↥G) (u v : Y555Vertex) (k : ℕ) :
    (y555NortonCandidate tau u * y555NortonCandidate tau v) ^ k = 1 ↔
      (y555NortonParameter tau u * (y555NortonParameter tau v)⁻¹) ^ k = 1 :=
  y555WreathReflection_mul_pow _ _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
