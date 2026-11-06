/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1BinaryInvariantQuadratics

/-! Central coordinates of arbitrary automorphisms of the actual extraspecial group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative NormalizedCocycleExtension
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Every actual automorphism fixes the two central coordinates individually. -/
theorem co1NonsplitAut_central (a : MulAut Q) (c : ZMod 2) :
    a (qCentral c) = qCentral c := by
  have hb (d : ZMod 2) : (a (qCentral d)).base = 1 := by
    have h := qBinaryAction_apply a (qCentral d)
    change qBinaryAction a 0 = toAdd (a (qCentral d)).base at h
    rw [map_zero] at h
    exact toAdd.injective h.symm
  have hbits : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide +kernel
  have hz : qCentral (0 : ZMod 2) = 1 := rfl
  have ho : a (qCentral 1) = qCentral 1 := by
    rcases hbits (toAdd (a (qCentral 1)).coeff) with h | h
    · have he : a (qCentral 1) = 1 := by
        apply Extension.ext
        · exact hb 1
        · exact toAdd.injective h
      have hn : qCentral (1 : ZMod 2) ≠ 1 := by
        intro he
        have h := congrArg (fun q : Q => toAdd q.coeff) he
        exact (by decide : (1 : ZMod 2) ≠ 0) h
      exact False.elim (hn (a.injective (he.trans (map_one a).symm)))
    · apply Extension.ext
      · exact hb 1
      · exact toAdd.injective h
  rcases hbits c with rfl | rfl
  · rw [hz, map_one]
  · exact ho

/-- The actual central coefficient of the image of a coefficient-zero base lift. -/
def co1NonsplitAutPhase (a : MulAut Q) (v : Fin 24 → ZMod 2) : ZMod 2 :=
  toAdd (a (qSection v)).coeff

/-- The induced binary action is the actual base coordinate of an automorphism image. -/
theorem co1NonsplitAut_base (a : MulAut Q) (q : Q) :
    toAdd (a q).base = qBinaryAction a (toAdd q.base) :=
  (qBinaryAction_apply a q).symm

/-- Actual central coordinates separate from the image of a coefficient-zero lift. -/
theorem co1NonsplitAut_coeff (a : MulAut Q) (q : Q) :
    toAdd (a q).coeff = toAdd q.coeff + co1NonsplitAutPhase a (toAdd q.base) := by
  conv_lhs => rw [← qCentral_section q]
  rw [map_mul, co1NonsplitAut_central, qCentral_mul_coeff]
  rfl

/-- The actual phase satisfies precisely the transported cocycle difference law. -/
theorem co1NonsplitAutPhase_add (a : MulAut Q) (v w : Fin 24 → ZMod 2) :
    co1NonsplitAutPhase a (v + w) = co1NonsplitAutPhase a v + co1NonsplitAutPhase a w +
      qBeta (qBinaryAction a v) (qBinaryAction a w) + qBeta v w := by
  have h := congrArg (fun q : Q => toAdd q.coeff) (a.map_mul (qSection v) (qSection w))
  rw [qSection_mul, map_mul, co1NonsplitAut_central, qCentral_mul_coeff] at h
  change qBeta v w + co1NonsplitAutPhase a (v + w) =
    (co1NonsplitAutPhase a v + co1NonsplitAutPhase a w) +
      qBeta (toAdd (a (qSection v)).base) (toAdd (a (qSection w)).base) at h
  rw [co1NonsplitAut_base, co1NonsplitAut_base] at h
  change qBeta v w + co1NonsplitAutPhase a (v + w) =
    (co1NonsplitAutPhase a v + co1NonsplitAutPhase a w) +
      qBeta (qBinaryAction a v) (qBinaryAction a w) at h
  have he := congrArg (fun z : ZMod 2 => z + qBeta v w) h
  have hc : (qBeta v w + co1NonsplitAutPhase a (v + w)) + qBeta v w =
      co1NonsplitAutPhase a (v + w) := by
    calc
      _ = co1NonsplitAutPhase a (v + w) + (qBeta v w + qBeta v w) := by abel
      _ = _ := by rw [ZModModule.add_self, add_zero]
  rw [hc] at he
  exact he.trans (by abel)

/-- A canonical transported cocycle cochain vanishes on the original coordinate units. -/
theorem co1NonsplitCentralCorrection_unit
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)) (i : Fin 24) :
    qCentralCorrection R (Pi.single i 1) = 0 := by
  simp only [qCentralCorrection, LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toBilin'_single, qCorrectionMatrix, lt_self_iff_false, ite_false]

/-- Removing the canonical cocycle cochain leaves an ordinary linear correction. -/
def co1NonsplitAutCorrection (a : MulAut Q)
    (hR : ∀ v, squareQuad (qBinaryAction a v) = squareQuad v) :
    (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun v => co1NonsplitAutPhase a v + qCentralCorrection (qBinaryAction a) v
      map_zero' := by
        have h : qSection (0 : Fin 24 → ZMod 2) = 1 := rfl
        simp only [co1NonsplitAutPhase, h, map_one, QuadraticMap.map_zero, add_zero]
        rfl
      map_add' := fun v w => by
        rw [co1NonsplitAutPhase_add, qCentralCorrection_add _ hR]
        calc
          _ = (co1NonsplitAutPhase a v + qCentralCorrection (qBinaryAction a) v) +
              (co1NonsplitAutPhase a w + qCentralCorrection (qBinaryAction a) w) +
              (qBeta (qBinaryAction a v) (qBinaryAction a w) +
                qBeta (qBinaryAction a v) (qBinaryAction a w)) +
              (qBeta v w + qBeta v w) := by abel
          _ = _ := by rw [ZModModule.add_self, ZModModule.add_self, add_zero, add_zero] }

/-- The phase is the canonical cochain plus its genuine linear correction. -/
theorem co1NonsplitAutPhase_correction (a : MulAut Q)
    (hR : ∀ v, squareQuad (qBinaryAction a v) = squareQuad v) (v : Fin 24 → ZMod 2) :
    co1NonsplitAutPhase a v = qCentralCorrection (qBinaryAction a) v +
      co1NonsplitAutCorrection a hR v := by
  change co1NonsplitAutPhase a v = qCentralCorrection (qBinaryAction a) v +
    (co1NonsplitAutPhase a v + qCentralCorrection (qBinaryAction a) v)
  symm
  calc
    _ = co1NonsplitAutPhase a v +
        (qCentralCorrection (qBinaryAction a) v + qCentralCorrection (qBinaryAction a) v) := by abel
    _ = _ := by rw [ZModModule.add_self, add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
