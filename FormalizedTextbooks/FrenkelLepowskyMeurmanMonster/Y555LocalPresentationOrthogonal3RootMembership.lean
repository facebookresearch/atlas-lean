/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite source root membership from injective coordinate codes and actual matrix actions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3RootMembershipData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix Pointwise

/-- The standard single column matrix of an actual finite field vector. -/
def y322Orthogonal3VectorColumn (v : Fin 7 → ZMod 3) : Matrix (Fin 7) Unit (ZMod 3) :=
  fun r _ => v r

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- Every literal root coordinate code is checked against the actual source root vector.
/-- The 126 literal finite root labels are exactly the actual source coordinate codes. -/
theorem y322Orthogonal3E7RootCode_checked (i : Fin 126) :
    y322Orthogonal3VectorCode (y322Orthogonal3E7RootCoordinates i) =
      y322Orthogonal3E7RootCode i := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
-- The exact list order is verified on every literal finite root label.
/-- The finite lookup list contains exactly the 126 literal source root coordinate labels. -/
theorem y322Orthogonal3E7RootCodeList_eq :
    y322Orthogonal3E7RootCodeList = List.ofFn y322Orthogonal3E7RootCode := by
  decide +kernel

/-- Natural lookup is equivalent to membership of the actual finite source root column set. -/
theorem y322Orthogonal3E7RootCode_mem_iff (v : Fin 7 → ZMod 3) :
    y322Orthogonal3VectorCode v ∈ y322Orthogonal3E7RootCodeList ↔
      y322Orthogonal3VectorColumn v ∈ y322Orthogonal3E7Roots := by
  rw [y322Orthogonal3E7RootCodeList_eq, List.mem_ofFn,
    y322Orthogonal3E7Roots, Finset.mem_image]
  constructor
  · rintro ⟨i, hi⟩
    have hv : y322Orthogonal3E7RootCoordinates i = v :=
      y322Orthogonal3VectorCode_injective ((y322Orthogonal3E7RootCode_checked i).trans hi)
    refine ⟨i, Finset.mem_univ _, ?_⟩
    change y322Orthogonal3VectorColumn (y322Orthogonal3E7RootCoordinates i) =
      y322Orthogonal3VectorColumn v
    rw [hv]
  · rintro ⟨i, _, hi⟩
    have hv : y322Orthogonal3E7RootCoordinates i = v := by
      funext r
      exact congrArg (fun m : Matrix (Fin 7) Unit (ZMod 3) => m r ()) hi
    exact ⟨i, (y322Orthogonal3E7RootCode_checked i).symm.trans
      (congrArg y322Orthogonal3VectorCode hv)⟩

/-- The standard column construction respects the genuine invertible matrix group action. -/
theorem y322Orthogonal3VectorColumn_action
    (g : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) (v : Fin 7 → ZMod 3) :
    g • y322Orthogonal3VectorColumn v = y322Orthogonal3VectorColumn (g.val *ᵥ v) := rfl

/-- Forward matrix root lookup tests exact membership in the inverse transported source root set. -/
theorem y322Orthogonal3E7RootCode_inverse_mem_iff
    (g : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) (v : Fin 7 → ZMod 3) :
    y322Orthogonal3VectorCode (g.val *ᵥ v) ∈ y322Orthogonal3E7RootCodeList ↔
      y322Orthogonal3VectorColumn v ∈ g⁻¹ • y322Orthogonal3E7Roots := by
  rw [y322Orthogonal3E7RootCode_mem_iff, ← y322Orthogonal3VectorColumn_action]
  constructor
  · intro h
    exact Finset.mem_smul_finset.mpr ⟨g • y322Orthogonal3VectorColumn v, h,
      inv_smul_smul g _⟩
  · intro h
    obtain ⟨x, hx, he⟩ := Finset.mem_smul_finset.mp h
    have hh := congrArg (fun m : Matrix (Fin 7) Unit (ZMod 3) => g • m) he
    have hpoint : g • y322Orthogonal3VectorColumn v = x := by
      simpa only [smul_inv_smul] using hh.symm
    rw [hpoint]
    exact hx

/-- Exact bounded root membership evaluation using ordinary natural residues. -/
def y322Orthogonal3RootMembershipNat (matrix : Matrix (Fin 7) (Fin 7) (ZMod 3))
    (vector : Fin 7 → ZMod 3) : Bool :=
  y322Orthogonal3E7RootCodeList.contains (y322Orthogonal3MatrixVectorCodeNat matrix vector)

/-- The bounded Boolean lookup is precisely actual inverse source root-set membership. -/
theorem y322Orthogonal3RootMembershipNat_eq
    (g : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) (v : Fin 7 → ZMod 3) :
    y322Orthogonal3RootMembershipNat g.val v = true ↔
      y322Orthogonal3VectorColumn v ∈ g⁻¹ • y322Orthogonal3E7Roots := by
  rw [y322Orthogonal3RootMembershipNat, List.contains_iff_mem,
    y322Orthogonal3MatrixVectorCodeNat_eq]
  exact y322Orthogonal3E7RootCode_inverse_mem_iff g v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
