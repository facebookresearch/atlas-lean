/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQMask
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1AutomorphismNonsplitMaskCorrections

/-! Actual extraspecial automorphisms evaluated by checked linear and quadratic bit masks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The complete actual vector map, evaluated by XOR of selected certified columns. -/
def generatedAxisGlobalQMaskVector (cols : Fin 24 → ℕ) (v : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 24 =>
    if v.testBit i.val then cols i else 0))

/-- The triangular central cochain evaluated by exact finite bit parities. -/
def generatedAxisGlobalQMaskPhase (rows : Fin 24 → ℕ) (v : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 24 =>
    if v.testBit i.val then monsterCo1GeometryBinaryMaskDot 24 (rows i) v else 0))

/-- The constant central bit produced by the cochain and its actual linear correction. -/
def generatedAxisGlobalQMaskCentral (rows : Fin 24 → ℕ) (coeff : ℕ) (v : ℕ) : ℕ :=
  Nat.xor (generatedAxisGlobalQMaskPhase rows v) (monsterCo1GeometryBinaryMaskDot 24 coeff v)

/-- The image belongs to the original Q extension and retains its full central coefficient. -/
def generatedAxisGlobalQMaskImage (cols rows : Fin 24 → ℕ) (coeff : ℕ) (v : ℕ) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalQMaskVector cols v)),
    ofAdd (if (generatedAxisGlobalQMaskCentral rows coeff v).testBit 0 then 1 else 0)⟩

/-- Certified columns determine the entire original linear action on every binary mask. -/
theorem generatedAxisGlobalQMaskVector_actual
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)) (cols : Fin 24 → ℕ)
    (hc : ∀ i, R (Pi.single i 1) = monsterCo1GeometryBinaryMaskDecode (cols i)) (v : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (generatedAxisGlobalQMaskVector cols v) =
      R (monsterCo1GeometryBinaryMaskDecode v) := by
  unfold generatedAxisGlobalQMaskVector
  rw [monsterCo1GeometryBinaryMaskDecode_sum, List.map_ofFn, List.sum_ofFn]
  have hv : monsterCo1GeometryBinaryMaskDecode v =
      ∑ i : Fin 24, monsterCo1GeometryBinaryMaskDecode v i • (Pi.single i 1) := by
    ext j
    simp [Pi.single_apply]
  rw [hv, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases h : v.testBit i.val <;>
    simp [monsterCo1GeometryBinaryMaskDecode_zero, monsterCo1GeometryBinaryMaskDecode, h, hc]

/-- Bit-parity cochain evaluation is the actual quadratic polynomial of the certified matrix. -/
theorem generatedAxisGlobalQMaskPhase_polynomial (rows : Fin 24 → ℕ) (v : ℕ) :
    (if (generatedAxisGlobalQMaskPhase rows v).testBit 0 then (1 : ZMod 2) else 0) =
      ∑ i : Fin 24, ∑ j : Fin 24,
        monsterCo1GeometryBinaryMaskDecode v i *
          monsterCo1GeometryBinaryMaskDecode (rows i) j *
            monsterCo1GeometryBinaryMaskDecode v j := by
  unfold generatedAxisGlobalQMaskPhase
  rw [monsterCo1GeometryBinaryMaskSum_parity, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  cases h : v.testBit i.val
  · simp [monsterCo1GeometryBinaryMaskDecode, h]
  · simpa [monsterCo1GeometryBinaryMaskDecode, h] using
      monsterCo1GeometryBinaryMaskDot_decode 24 (rows i) v

/-- A checked phase matrix gives the complete original canonical central correction. -/
theorem generatedAxisGlobalQMaskPhase_actual
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)) (rows : Fin 24 → ℕ)
    (hr : qCorrectionMatrix R = monsterCo1GeometryBinaryMaskMatrix rows) (v : ℕ) :
    qCentralCorrection R (monsterCo1GeometryBinaryMaskDecode v) =
      if (generatedAxisGlobalQMaskPhase rows v).testBit 0 then 1 else 0 := by
  rw [qCentralCorrection, LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toBilin'_apply, hr]
  exact (generatedAxisGlobalQMaskPhase_polynomial rows v).symm

/-- Actual unit coefficients determine the entire genuine linear central correction. -/
theorem generatedAxisGlobalQMaskLinear_actual (a : MulAut Q)
    (hR : ∀ v, squareQuad (qBinaryAction a v) = squareQuad v) (coeff : ℕ)
    (hc : ∀ i, co1NonsplitAutPhase a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode coeff i) (v : ℕ) :
    co1NonsplitAutCorrection a hR (monsterCo1GeometryBinaryMaskDecode v) =
      if (monsterCo1GeometryBinaryMaskDot 24 coeff v).testBit 0 then 1 else 0 := by
  rw [co1NonsplitLinear_unit_sum, monsterCo1GeometryBinaryMaskDot_decode]
  apply Finset.sum_congr rfl
  intro i _
  have hi : co1NonsplitAutCorrection a hR (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode coeff i := by
    change co1NonsplitAutPhase a (Pi.single i 1) +
      qCentralCorrection (qBinaryAction a) (Pi.single i 1) = _
    rw [co1NonsplitCentralCorrection_unit, add_zero]
    exact hc i
  rw [hi, mul_comm]

/-- Checked columns, phase matrix, and unit coefficients determine the actual image. -/
theorem generatedAxisGlobalQMaskImage_actual (a : MulAut Q)
    (hR : ∀ v, squareQuad (qBinaryAction a v) = squareQuad v)
    (cols rows : Fin 24 → ℕ) (coeff : ℕ)
    (hb : ∀ i, qBinaryAction a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode (cols i))
    (hr : qCorrectionMatrix (qBinaryAction a) = monsterCo1GeometryBinaryMaskMatrix rows)
    (hc : ∀ i, co1NonsplitAutPhase a (Pi.single i 1) =
      monsterCo1GeometryBinaryMaskDecode coeff i) (v : ℕ) :
    a (generatedAxisGlobalQMask v) = generatedAxisGlobalQMaskImage cols rows coeff v := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    rw [co1NonsplitAut_base]
    exact (generatedAxisGlobalQMaskVector_actual (qBinaryAction a) cols hb v).symm
  · apply toAdd.injective
    rw [co1NonsplitAut_coeff]
    change 0 + co1NonsplitAutPhase a (monsterCo1GeometryBinaryMaskDecode v) = _
    rw [zero_add, co1NonsplitAutPhase_correction a hR,
      generatedAxisGlobalQMaskPhase_actual _ rows hr,
      generatedAxisGlobalQMaskLinear_actual a hR coeff hc]
    exact (congrFun (monsterCo1GeometryBinaryMaskDecode_xor (n := 1)
      (generatedAxisGlobalQMaskPhase rows v) (monsterCo1GeometryBinaryMaskDot 24 coeff v)) 0).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
