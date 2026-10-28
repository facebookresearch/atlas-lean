/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1AutomorphismNonsplitWords

/-! Every hypothetical lift satisfies the literal finite correction equations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The genuine linear correction of a lift of an original Conway generator. -/
def co1NonsplitLiftCorrection (a : Fin 5 → MulAut Q)
    (h : ∀ k, qBinaryAction (a k) = co1BinaryAction (monsterCo1FiveGenerator k))
    (k : Fin 5) : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  co1NonsplitAutCorrection (a k) (fun v => by
    rw [h k]
    exact co1BinaryAction_squareQuad_invariant (monsterCo1FiveGenerator k) v)

/-- A coordinate function stores all five independent 24-dimensional linear corrections. -/
def co1NonsplitLiftParameters (a : Fin 5 → MulAut Q)
    (h : ∀ k, qBinaryAction (a k) = co1BinaryAction (monsterCo1FiveGenerator k)) :
    Fin 120 → ZMod 2 := fun j =>
  co1NonsplitLiftCorrection a h ⟨j.val / 24, by omega⟩
    (Pi.single ⟨j.val % 24, Nat.mod_lt _ (by decide)⟩ 1)

/-- The packed parameters retain the actual value of each correction on every unit. -/
theorem co1NonsplitLiftParameters_unit (a : Fin 5 → MulAut Q)
    (h : ∀ k, qBinaryAction (a k) = co1BinaryAction (monsterCo1FiveGenerator k))
    (k : Fin 5) (i : Fin 24) :
    co1NonsplitLiftParameters a h (co1NonsplitVariableIndex k i) =
      co1NonsplitLiftCorrection a h k (Pi.single i 1) := by
  unfold co1NonsplitLiftParameters
  have hk : ((co1NonsplitVariableIndex k i).val / 24 : ℕ) = k.val := by
    simp only [co1NonsplitVariableIndex]
    omega
  have hi : ((co1NonsplitVariableIndex k i).val % 24 : ℕ) = i.val := by
    simp only [co1NonsplitVariableIndex]
    omega
  have hke : (⟨(co1NonsplitVariableIndex k i).val / 24, by omega⟩ : Fin 5) = k :=
    Fin.ext hk
  have hie : (⟨(co1NonsplitVariableIndex k i).val % 24,
      Nat.mod_lt _ (by decide)⟩ : Fin 24) = i := Fin.ext hi
  rw [hke, hie]

/-- Actual generator phases agree with the finite cochain and all selected correction bits. -/
theorem co1NonsplitLift_phase (a : Fin 5 → MulAut Q)
    (h : ∀ k, qBinaryAction (a k) = co1BinaryAction (monsterCo1FiveGenerator k))
    (k : Fin 5) (v : ℕ) :
    co1NonsplitAutPhase (a k) (monsterCo1GeometryBinaryMaskDecode v) =
      (if (co1NonsplitMaskPhase k v).testBit 0 then (1 : ZMod 2) else 0) +
        monsterCo1GeometryBinaryMaskDecode (co1NonsplitMaskVariables k v) ⬝ᵥ
          co1NonsplitLiftParameters a h := by
  have hR : ∀ v, squareQuad (qBinaryAction (a k) v) = squareQuad v := by
    intro v
    rw [h k]
    exact co1BinaryAction_squareQuad_invariant (monsterCo1FiveGenerator k) v
  have hcorr : co1NonsplitAutCorrection (a k) hR
      (monsterCo1GeometryBinaryMaskDecode v) =
        monsterCo1GeometryBinaryMaskDecode (co1NonsplitMaskVariables k v) ⬝ᵥ
          co1NonsplitLiftParameters a h := by
    change co1NonsplitLiftCorrection a h k (monsterCo1GeometryBinaryMaskDecode v) = _
    rw [co1NonsplitLinear_unit_sum, co1NonsplitMaskVariables_dot]
    apply Finset.sum_congr rfl
    intro i _
    rw [co1NonsplitLiftParameters_unit]
  have htheta : qCentralCorrection (qBinaryAction (a k))
      (monsterCo1GeometryBinaryMaskDecode v) =
        if (co1NonsplitMaskPhase k v).testBit 0 then (1 : ZMod 2) else 0 := by
    rw [h k]
    exact co1NonsplitFive_correction k v
  rw [co1NonsplitAutPhase_correction (a k) hR, htheta, hcorr]

/-- The original generator lifts compose in the same left-action order as the source words. -/
def co1NonsplitLiftWord (a : Fin 5 → MulAut Q) : List (Fin 5) → MulAut Q
  | [] => 1
  | k :: w => co1NonsplitLiftWord a w * a k

/-- A bitwise XOR constant is exact addition of actual central field coordinates. -/
theorem co1NonsplitBit_xor (x y : ℕ) :
    (if (Nat.xor x y).testBit 0 then (1 : ZMod 2) else 0) =
      (if x.testBit 0 then 1 else 0) + (if y.testBit 0 then 1 else 0) :=
  congrFun (monsterCo1GeometryBinaryMaskDecode_xor (n := 1) x y) 0

/-- Every symbolic word state retains the actual base and central coefficient of its lift. -/
theorem co1NonsplitLiftWord_state (a : Fin 5 → MulAut Q)
    (h : ∀ k, qBinaryAction (a k) = co1BinaryAction (monsterCo1FiveGenerator k))
    (w : List (Fin 5)) (s : Co1NonsplitMaskState) (q : Q)
    (hb : toAdd q.base = monsterCo1GeometryBinaryMaskDecode s.1)
    (hc : toAdd q.coeff = (if s.2.1.testBit 0 then (1 : ZMod 2) else 0) +
      monsterCo1GeometryBinaryMaskDecode s.2.2 ⬝ᵥ co1NonsplitLiftParameters a h) :
    toAdd (co1NonsplitLiftWord a w q).base =
        monsterCo1GeometryBinaryMaskDecode (co1NonsplitMaskRun w s).1 ∧
      toAdd (co1NonsplitLiftWord a w q).coeff =
        (if (co1NonsplitMaskRun w s).2.1.testBit 0 then (1 : ZMod 2) else 0) +
          monsterCo1GeometryBinaryMaskDecode (co1NonsplitMaskRun w s).2.2 ⬝ᵥ
            co1NonsplitLiftParameters a h := by
  induction w generalizing s q with
  | nil => exact ⟨hb, hc⟩
  | cons k w ih =>
    have hbase : toAdd (a k q).base =
        monsterCo1GeometryBinaryMaskDecode (co1NonsplitMaskStep k s).1 := by
      rw [co1NonsplitAut_base, h k, hb, co1NonsplitFive_action]
      exact (co1NonsplitMaskVector_decode k s.1).symm
    have hcoeff : toAdd (a k q).coeff =
        (if (co1NonsplitMaskStep k s).2.1.testBit 0 then (1 : ZMod 2) else 0) +
          monsterCo1GeometryBinaryMaskDecode (co1NonsplitMaskStep k s).2.2 ⬝ᵥ
            co1NonsplitLiftParameters a h := by
      rw [co1NonsplitAut_coeff, hc, hb, co1NonsplitLift_phase a h k s.1]
      simp only [co1NonsplitMaskStep, co1NonsplitBit_xor,
        monsterCo1GeometryBinaryMaskDecode_xor, add_dotProduct]
      abel
    exact ih (co1NonsplitMaskStep k s) (a k q) hbase hcoeff

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
