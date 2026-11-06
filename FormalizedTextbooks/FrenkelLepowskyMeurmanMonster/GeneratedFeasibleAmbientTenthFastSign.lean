/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthSignCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceSignCacheSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthPack

/-! The five root-two source signs as compact formulas with packed phase tables. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The five root-two source sign codes. -/
def generatedFeasibleAmbientTenthSignCodeF : Fin 5 → Fin 4096 := ![0, 1024, 2304, 3072, 2048]

set_option maxRecDepth 100000 in
/-- The Y and Z phase bits of the five codes on the 2048 low labels (bit set for `-1`). -/
def generatedFeasibleAmbientTenthSignPhaseNat : Fin 5 → Fin 2 → ℕ :=
  ![![generatedFeasibleAmbientTenthPack [0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
      0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
      0x0, 0x0, 0x0], generatedFeasibleAmbientTenthPack [0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
      0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
      0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]],
      ![generatedFeasibleAmbientTenthPack [0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
      0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
      0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117],
      generatedFeasibleAmbientTenthPack [0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
      0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
      0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117]],
      ![generatedFeasibleAmbientTenthPack [0xcc33c3c3f00fffff, 0x3c3c33ccfffff00f,
      0xffff0ff03c3ccc33, 0xff0ffff33ccc3c3, 0xcc33c3c3f00fffff, 0x3c3c33ccfffff00f,
      0xffff0ff03c3ccc33, 0xff0ffff33ccc3c3, 0x669969695aa55555, 0x9696996655555aa5,
      0x5555a55a96966699, 0xa55a555599666969, 0x669969695aa55555, 0x9696996655555aa5,
      0x5555a55a96966699, 0xa55a555599666969, 0xcc33c3c3f00fffff, 0x3c3c33ccfffff00f,
      0xffff0ff03c3ccc33, 0xff0ffff33ccc3c3, 0xcc33c3c3f00fffff, 0x3c3c33ccfffff00f,
      0xffff0ff03c3ccc33, 0xff0ffff33ccc3c3, 0x99669696a55aaaaa, 0x69696699aaaaa55a,
      0xaaaa5aa569699966, 0x5aa5aaaa66999696, 0x99669696a55aaaaa, 0x69696699aaaaa55a,
      0xaaaa5aa569699966, 0x5aa5aaaa66999696],
      generatedFeasibleAmbientTenthPack [0x99669696a55aaaaa, 0x69696699aaaaa55a,
      0xaaaa5aa569699966, 0x5aa5aaaa66999696, 0x99669696a55aaaaa, 0x69696699aaaaa55a,
      0xaaaa5aa569699966, 0x5aa5aaaa66999696, 0x33cc3c3c0ff00000, 0xc3c3cc3300000ff0,
      0xf00fc3c333cc, 0xf00f0000cc333c3c, 0x33cc3c3c0ff00000, 0xc3c3cc3300000ff0,
      0xf00fc3c333cc, 0xf00f0000cc333c3c, 0x669969695aa55555, 0x9696996655555aa5,
      0x5555a55a96966699, 0xa55a555599666969, 0x669969695aa55555, 0x9696996655555aa5,
      0x5555a55a96966699, 0xa55a555599666969, 0x33cc3c3c0ff00000, 0xc3c3cc3300000ff0,
      0xf00fc3c333cc, 0xf00f0000cc333c3c, 0x33cc3c3c0ff00000, 0xc3c3cc3300000ff0,
      0xf00fc3c333cc, 0xf00f0000cc333c3c]],
      ![generatedFeasibleAmbientTenthPack [0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
      0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
      0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
      0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
      0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
      0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
      0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8],
      generatedFeasibleAmbientTenthPack [0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
      0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8,
      0x7ee87ee87ee87ee8, 0x7ee87ee87ee87ee8, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117, 0x8117811781178117, 0x8117811781178117,
      0x8117811781178117, 0x8117811781178117]],
      ![generatedFeasibleAmbientTenthPack [0xffffffffffffffff, 0xffffffffffffffff,
      0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
      0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
      0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
      0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
      0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
      0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
      0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff,
      0xffffffffffffffff, 0xffffffffffffffff], generatedFeasibleAmbientTenthPack [0x0, 0x0,
      0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
      0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]]]

/-- The packed source Y or Z phase sign. -/
def generatedFeasibleAmbientTenthSignPhaseF (c : Fin 5) (p : Fin 2) (e : Fin 2048) : ℤ :=
  1 - 2 * ((((generatedFeasibleAmbientTenthSignPhaseNat c p) >>> e.val) % 2 : ℕ) : ℤ)

/-- The compact four-input source sign with packed phases. -/
def generatedFeasibleAmbientTenthSignSpinCompactF (c : Fin 5) (u : Fin 4096 → ℤ) (k : Fin 4096) :
    ℤ :=
  let e := generatedAxisGlobalSpinLabelLow k
  let d := generatedAxisGlobalSignInputCode (generatedFeasibleAmbientTenthSignCodeF c) e
  generatedAxisGlobalIntSign (golayLabelCoefficients k 11) *
      generatedFeasibleAmbientTenthSignPhaseF c 0 e *
      (u (generatedAxisGlobalTensorLowLabel d) - u (generatedAxisGlobalTensorHighLabel d)) +
    generatedFeasibleAmbientTenthSignPhaseF c 1 e *
      (u (generatedAxisGlobalTensorLowLabel e) + u (generatedAxisGlobalTensorHighLabel e))

/-- The low label with block `q` and offset `a`. -/
private def lowLabel (q : Fin 4) (a : Fin 512) : Fin 2048 :=
  ⟨q.val * 512 + a.val, by have := q.isLt; have := a.isLt; omega⟩

private theorem lowBlocks {P : Fin 2048 → Prop} (h : ∀ q : Fin 4, ∀ a : Fin 512, P (lowLabel q a))
    (e : Fin 2048) : P e := by
  have h' := h ⟨e.val / 512, by have := e.isLt; omega⟩ ⟨e.val % 512, Nat.mod_lt _ (by decide)⟩
  have he : lowLabel ⟨e.val / 512, by have := e.isLt; omega⟩
      ⟨e.val % 512, Nat.mod_lt _ (by decide)⟩ = e := by
    apply Fin.ext
    change e.val / 512 * 512 + e.val % 512 = e.val
    omega
  rw [he] at h'
  exact h'

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 0 to 511 of code 0 are compared.
private theorem ph0_0 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 0 p (lowLabel 0 a) =
        generatedFeasibleAmbientTenthSignPhase 0 p (lowLabel 0 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 512 to 1023 of code 0 are compared.
private theorem ph0_1 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 0 p (lowLabel 1 a) =
        generatedFeasibleAmbientTenthSignPhase 0 p (lowLabel 1 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 1024 to 1535 of code 0 are compared.
private theorem ph0_2 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 0 p (lowLabel 2 a) =
        generatedFeasibleAmbientTenthSignPhase 0 p (lowLabel 2 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 1536 to 2047 of code 0 are compared.
private theorem ph0_3 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 0 p (lowLabel 3 a) =
        generatedFeasibleAmbientTenthSignPhase 0 p (lowLabel 3 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 0 to 511 of code 1024 are compared.
private theorem ph1_0 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 1 p (lowLabel 0 a) =
        generatedFeasibleAmbientTenthSignPhase 1 p (lowLabel 0 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 512 to 1023 of code 1024 are compared.
private theorem ph1_1 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 1 p (lowLabel 1 a) =
        generatedFeasibleAmbientTenthSignPhase 1 p (lowLabel 1 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 1024 to 1535 of code 1024 are compared.
private theorem ph1_2 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 1 p (lowLabel 2 a) =
        generatedFeasibleAmbientTenthSignPhase 1 p (lowLabel 2 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 1536 to 2047 of code 1024 are compared.
private theorem ph1_3 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 1 p (lowLabel 3 a) =
        generatedFeasibleAmbientTenthSignPhase 1 p (lowLabel 3 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 0 to 511 of code 2304 are compared.
private theorem ph2_0 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 2 p (lowLabel 0 a) =
        generatedFeasibleAmbientTenthSignPhase 2 p (lowLabel 0 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 512 to 1023 of code 2304 are compared.
private theorem ph2_1 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 2 p (lowLabel 1 a) =
        generatedFeasibleAmbientTenthSignPhase 2 p (lowLabel 1 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 1024 to 1535 of code 2304 are compared.
private theorem ph2_2 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 2 p (lowLabel 2 a) =
        generatedFeasibleAmbientTenthSignPhase 2 p (lowLabel 2 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 1536 to 2047 of code 2304 are compared.
private theorem ph2_3 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 2 p (lowLabel 3 a) =
        generatedFeasibleAmbientTenthSignPhase 2 p (lowLabel 3 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 0 to 511 of code 3072 are compared.
private theorem ph3_0 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 3 p (lowLabel 0 a) =
        generatedTwelfthTensorSourceSignPhase 1 p (lowLabel 0 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 512 to 1023 of code 3072 are compared.
private theorem ph3_1 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 3 p (lowLabel 1 a) =
        generatedTwelfthTensorSourceSignPhase 1 p (lowLabel 1 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 1024 to 1535 of code 3072 are compared.
private theorem ph3_2 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 3 p (lowLabel 2 a) =
        generatedTwelfthTensorSourceSignPhase 1 p (lowLabel 2 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 1536 to 2047 of code 3072 are compared.
private theorem ph3_3 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 3 p (lowLabel 3 a) =
        generatedTwelfthTensorSourceSignPhase 1 p (lowLabel 3 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 0 to 511 of code 2048 are compared.
private theorem ph4_0 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 4 p (lowLabel 0 a) =
        generatedTwelfthTensorSourceSignPhase 2 p (lowLabel 0 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 512 to 1023 of code 2048 are compared.
private theorem ph4_1 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 4 p (lowLabel 1 a) =
        generatedTwelfthTensorSourceSignPhase 2 p (lowLabel 1 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 1024 to 1535 of code 2048 are compared.
private theorem ph4_2 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 4 p (lowLabel 2 a) =
        generatedTwelfthTensorSourceSignPhase 2 p (lowLabel 2 a) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- Low labels 1536 to 2047 of code 2048 are compared.
private theorem ph4_3 : ∀ a : Fin 512, ∀ p : Fin 2,
    generatedFeasibleAmbientTenthSignPhaseF 4 p (lowLabel 3 a) =
        generatedTwelfthTensorSourceSignPhase 2 p (lowLabel 3 a) := by
  decide +kernel

/-- The code-0 source sign. -/
theorem generatedFeasibleAmbientTenth_sign_fast0 (u : Fin 4096 → ℤ) :
    generatedFeasibleAmbientTenthSignSpinCompact 0 u =
        generatedFeasibleAmbientTenthSignSpinCompactF 0 u := by
  have hp : ∀ p : Fin 2, ∀ e : Fin 2048, generatedFeasibleAmbientTenthSignPhaseF 0 p e =
      generatedFeasibleAmbientTenthSignPhase 0 p e := by
    intro p e
    revert e
    apply lowBlocks (P := fun e => generatedFeasibleAmbientTenthSignPhaseF 0 p e =
        generatedFeasibleAmbientTenthSignPhase 0 p e)
    intro q a
    fin_cases q
    · exact ph0_0 a p
    · exact ph0_1 a p
    · exact ph0_2 a p
    · exact ph0_3 a p
  funext k
  simp only [generatedFeasibleAmbientTenthSignSpinCompactF,
      generatedFeasibleAmbientTenthSignSpinCompact, hp]
  rfl

/-- The code-1024 source sign. -/
theorem generatedFeasibleAmbientTenth_sign_fast1 (u : Fin 4096 → ℤ) :
    generatedFeasibleAmbientTenthSignSpinCompact 1 u =
        generatedFeasibleAmbientTenthSignSpinCompactF 1 u := by
  have hp : ∀ p : Fin 2, ∀ e : Fin 2048, generatedFeasibleAmbientTenthSignPhaseF 1 p e =
      generatedFeasibleAmbientTenthSignPhase 1 p e := by
    intro p e
    revert e
    apply lowBlocks (P := fun e => generatedFeasibleAmbientTenthSignPhaseF 1 p e =
        generatedFeasibleAmbientTenthSignPhase 1 p e)
    intro q a
    fin_cases q
    · exact ph1_0 a p
    · exact ph1_1 a p
    · exact ph1_2 a p
    · exact ph1_3 a p
  funext k
  simp only [generatedFeasibleAmbientTenthSignSpinCompactF,
      generatedFeasibleAmbientTenthSignSpinCompact, hp]
  rfl

/-- The code-2304 source sign. -/
theorem generatedFeasibleAmbientTenth_sign_fast2 (u : Fin 4096 → ℤ) :
    generatedFeasibleAmbientTenthSignSpinCompact 2 u =
        generatedFeasibleAmbientTenthSignSpinCompactF 2 u := by
  have hp : ∀ p : Fin 2, ∀ e : Fin 2048, generatedFeasibleAmbientTenthSignPhaseF 2 p e =
      generatedFeasibleAmbientTenthSignPhase 2 p e := by
    intro p e
    revert e
    apply lowBlocks (P := fun e => generatedFeasibleAmbientTenthSignPhaseF 2 p e =
        generatedFeasibleAmbientTenthSignPhase 2 p e)
    intro q a
    fin_cases q
    · exact ph2_0 a p
    · exact ph2_1 a p
    · exact ph2_2 a p
    · exact ph2_3 a p
  funext k
  simp only [generatedFeasibleAmbientTenthSignSpinCompactF,
      generatedFeasibleAmbientTenthSignSpinCompact, hp]
  rfl

/-- The code-3072 source sign. -/
theorem generatedFeasibleAmbientTenth_sign_fast3 (u : Fin 4096 → ℤ) :
    generatedTwelfthTensorSourceSignSpinCompact 1 u =
        generatedFeasibleAmbientTenthSignSpinCompactF 3 u := by
  have hp : ∀ p : Fin 2, ∀ e : Fin 2048, generatedFeasibleAmbientTenthSignPhaseF 3 p e =
      generatedTwelfthTensorSourceSignPhase 1 p e := by
    intro p e
    revert e
    apply lowBlocks (P := fun e => generatedFeasibleAmbientTenthSignPhaseF 3 p e =
        generatedTwelfthTensorSourceSignPhase 1 p e)
    intro q a
    fin_cases q
    · exact ph3_0 a p
    · exact ph3_1 a p
    · exact ph3_2 a p
    · exact ph3_3 a p
  funext k
  simp only [generatedFeasibleAmbientTenthSignSpinCompactF,
      generatedTwelfthTensorSourceSignSpinCompact, hp]
  rfl

/-- The code-2048 source sign. -/
theorem generatedFeasibleAmbientTenth_sign_fast4 (u : Fin 4096 → ℤ) :
    generatedTwelfthTensorSourceSignSpinCompact 2 u =
        generatedFeasibleAmbientTenthSignSpinCompactF 4 u := by
  have hp : ∀ p : Fin 2, ∀ e : Fin 2048, generatedFeasibleAmbientTenthSignPhaseF 4 p e =
      generatedTwelfthTensorSourceSignPhase 2 p e := by
    intro p e
    revert e
    apply lowBlocks (P := fun e => generatedFeasibleAmbientTenthSignPhaseF 4 p e =
        generatedTwelfthTensorSourceSignPhase 2 p e)
    intro q a
    fin_cases q
    · exact ph4_0 a p
    · exact ph4_1 a p
    · exact ph4_2 a p
    · exact ph4_3 a p
  funext k
  simp only [generatedFeasibleAmbientTenthSignSpinCompactF,
      generatedTwelfthTensorSourceSignSpinCompact, hp]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
