/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskProducts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRepresentativeWordsPlan

/-! Exact binary row products and coefficient bits certify the full original spin phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Integer row masks for both parts of a full signed spin model. -/
structure generatedFifthSpinMaskRows where
  /-- Rows of the genuine coordinate matrix. -/
  coordinate : Fin 12 → ℕ
  /-- Rows of the complete quadratic coefficient matrix. -/
  phase : Fin 12 → ℕ

/-- Decode both complete matrices without any approximation. -/
def generatedFifthSpinMaskRowsModel (a : generatedFifthSpinMaskRows) : RepresentativeSpinModel :=
  ⟨monsterCo1GeometryBinaryMaskMatrix a.coordinate,
    monsterCo1GeometryBinaryMaskMatrix a.phase⟩

/-- Bounded exact mask checks for an original signed multiplication edge. -/
def generatedFifthSpinMaskEdgeCheck (a b c : generatedFifthSpinMaskRows)
    (transposeRows raw : Fin 12 → ℕ) : Prop :=
  monsterCo1GeometryBinaryMaskProduct b.coordinate a.coordinate = c.coordinate ∧
  (∀ i j : Fin 12, (transposeRows i).testBit j.val = (a.coordinate j).testBit i.val) ∧
  (∀ i : Fin 12, raw i = Nat.xor (a.phase i)
    (monsterCo1GeometryBinaryMaskProduct transposeRows
      (monsterCo1GeometryBinaryMaskProduct b.phase a.coordinate) i)) ∧
  (∀ i : Fin 12, (raw i).testBit i.val = (c.phase i).testBit i.val) ∧
  (∀ i j : Fin 12, Bool.xor ((raw i).testBit j.val) ((raw j).testBit i.val) =
    Bool.xor ((c.phase i).testBit j.val) ((c.phase j).testBit i.val))

/-- The bounded mask predicates use ordinary finite decision procedures. -/
instance generatedFifthSpinMaskEdgeDecidable (a b c : generatedFifthSpinMaskRows)
    (transposeRows raw : Fin 12 → ℕ) :
    Decidable (generatedFifthSpinMaskEdgeCheck a b c transposeRows raw) := by
  unfold generatedFifthSpinMaskEdgeCheck
  infer_instance

private theorem bit_xor (a b : Bool) :
    (if Bool.xor a b then (1 : ZMod 2) else 0) =
      (if a then (1 : ZMod 2) else 0) + (if b then (1 : ZMod 2) else 0) := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide +kernel
  cases a <;> cases b <;> simp [h11]

private theorem edge_of_phase (A B C : RepresentativeSpinModel)
    (hP : C.coordinate = B.coordinate * A.coordinate)
    (hv : ∀ t : SpinIndex,
      monsterMonomialQuadratic (A.phase + A.coordinateᵀ * B.phase * A.coordinate) t =
        monsterMonomialQuadratic C.phase t) : representativeSpinEdge A B C := by
  refine ⟨hP, ?_, ?_⟩
  · intro i
    have h := hv (Pi.single i 1)
    rw [representativeQuadratic_add_matrix, representativeQuadratic_pullback,
      Matrix.mulVec_single_one] at h
    exact h
  · intro i j
    have h := hv (Pi.single i 1 + Pi.single j 1)
    rw [representativeQuadratic_add_matrix, representativeQuadratic_pullback,
      Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    exact h

/-- Every checked bit and XOR product implies the entire genuine signed spin edge. -/
theorem generatedFifth_spin_mask_edge_sound (a b c : generatedFifthSpinMaskRows)
    (transposeRows raw : Fin 12 → ℕ)
    (hc : generatedFifthSpinMaskEdgeCheck a b c transposeRows raw) :
    representativeSpinEdge (generatedFifthSpinMaskRowsModel a)
      (generatedFifthSpinMaskRowsModel b) (generatedFifthSpinMaskRowsModel c) := by
  rcases hc with ⟨hP, hT, hR, hd, hs⟩
  let A := generatedFifthSpinMaskRowsModel a
  let B := generatedFifthSpinMaskRowsModel b
  let C := generatedFifthSpinMaskRowsModel c
  have ht : monsterCo1GeometryBinaryMaskMatrix transposeRows = A.coordinateᵀ := by
    ext i j
    change (if (transposeRows i).testBit j.val then (1 : ZMod 2) else 0) =
      (if (a.coordinate j).testBit i.val then 1 else 0)
    rw [hT]
  have hr : A.phase + A.coordinateᵀ * B.phase * A.coordinate =
      monsterCo1GeometryBinaryMaskMatrix raw := by
    rw [← ht]
    change monsterCo1GeometryBinaryMaskMatrix a.phase +
      monsterCo1GeometryBinaryMaskMatrix transposeRows *
        monsterCo1GeometryBinaryMaskMatrix b.phase *
        monsterCo1GeometryBinaryMaskMatrix a.coordinate = _
    rw [Matrix.mul_assoc, ← monsterCo1GeometryBinaryMaskMatrix_product,
      ← monsterCo1GeometryBinaryMaskMatrix_product]
    ext i j
    change monsterCo1GeometryBinaryMaskDecode (a.phase i) j +
      monsterCo1GeometryBinaryMaskDecode
        (monsterCo1GeometryBinaryMaskProduct transposeRows
          (monsterCo1GeometryBinaryMaskProduct b.phase a.coordinate) i) j =
      monsterCo1GeometryBinaryMaskDecode (raw i) j
    rw [hR i]
    symm
    exact congrFun (monsterCo1GeometryBinaryMaskDecode_xor _ _) j
  have hv (t : SpinIndex) :
      monsterMonomialQuadratic (A.phase + A.coordinateᵀ * B.phase * A.coordinate) t =
        monsterMonomialQuadratic C.phase t := by
    rw [hr]
    apply representativeQuadratic_coefficients
    · intro i
      change (if (raw i).testBit i.val then (1 : ZMod 2) else 0) =
        (if (c.phase i).testBit i.val then 1 else 0)
      rw [hd]
    · intro i j
      change (if (raw i).testBit j.val then (1 : ZMod 2) else 0) +
          (if (raw j).testBit i.val then 1 else 0) =
        (if (c.phase i).testBit j.val then 1 else 0) +
          (if (c.phase j).testBit i.val then 1 else 0)
      rw [← bit_xor, ← bit_xor, hs]
  apply edge_of_phase A B C _ hv
  exact (congrArg monsterCo1GeometryBinaryMaskMatrix hP).symm.trans
    (monsterCo1GeometryBinaryMaskMatrix_product b.coordinate a.coordinate)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
