/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskQuadratic

/-! Two finite parity lookups compute the genuine hyperbolic singularity test exactly. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The exact odd-parity bits for all 256 bytes. -/
def generatedAxisGlobalOddByteParity : ℕ :=
  47758914269546354982683078068829456704164423862093743397580034411621752859030

/-- Parity of the twelve low bits, read with an exact byte and nibble lookup. -/
def generatedAxisGlobalFastParityTwelve (b : ℕ) : Bool :=
  !(Bool.xor (generatedAxisGlobalOddByteParity.testBit (b % 256))
    (Nat.testBit 27030 ((b / 256) % 16)))

/-- Direct parity of precisely the twelve actual coefficient bits. -/
def generatedAxisGlobalParityTwelve (b : ℕ) : Bool :=
  !((List.ofFn (fun i : Fin 12 => b.testBit i.val)).foldl Bool.xor false)

set_option maxHeartbeats 10000000 in
-- Check all4096 byte-nibble pairs in a bounded product of16 and256 labels.
/-- Both finite lookup tables agree with direct parity on all 4096 twelve-bit inputs. -/
theorem generatedAxisGlobalFastParity_certificate : ∀ b : Fin 4096,
    generatedAxisGlobalParityTwelve b.val = generatedAxisGlobalFastParityTwelve b.val := by
  have h : ∀ a : Fin 16, ∀ c : Fin 256,
      generatedAxisGlobalParityTwelve (256 * a.val + c.val) =
        generatedAxisGlobalFastParityTwelve (256 * a.val + c.val) := by
    decide +kernel
  intro b
  have hb : b.val / 256 < 16 := by have h := b.isLt; omega
  have hx := h ⟨b.val / 256, hb⟩ ⟨b.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : 256 * (b.val / 256) + b.val % 256 = b.val := by omega
  simpa only [he] using hx

/-- Direct twelve-bit parity ignores every higher coordinate bit. -/
theorem generatedAxisGlobalParityTwelve_mod (b : ℕ) :
    generatedAxisGlobalParityTwelve b = generatedAxisGlobalParityTwelve (b % 4096) := by
  unfold generatedAxisGlobalParityTwelve
  apply congrArg (fun bits : List Bool => !(bits.foldl Bool.xor false))
  apply congrArg List.ofFn
  funext i
  change b.testBit i.val = (b % 2 ^ 12).testBit i.val
  rw [Nat.testBit_mod_two_pow]
  simp only [i.isLt, decide_true, Bool.true_and]

/-- Pairing the actual low and high hyperbolic bits is exactly their bitwise conjunction. -/
theorem generatedAxisGlobalMaskSingular_parity (b : ℕ) :
    generatedAxisGlobalMaskSingular b =
      generatedAxisGlobalParityTwelve (b &&& (b >>> 12)) := by
  unfold generatedAxisGlobalMaskSingular generatedAxisGlobalParityTwelve
  apply congrArg (fun bits : List Bool => !(bits.foldl Bool.xor false))
  apply congrArg List.ofFn
  funext i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_comm]

/-- A two-lookup singularity check on the genuine paired hyperbolic coordinates. -/
def generatedAxisGlobalFastSingular (b : ℕ) : Bool :=
  generatedAxisGlobalFastParityTwelve ((b &&& (b >>> 12)) % 4096)

/-- The fast finite check is exactly the existing genuine quadratic-form test. -/
theorem generatedAxisGlobalFastSingular_eq (b : ℕ) :
    generatedAxisGlobalFastSingular b = generatedAxisGlobalMaskSingular b := by
  rw [generatedAxisGlobalMaskSingular_parity, generatedAxisGlobalParityTwelve_mod]
  exact (generatedAxisGlobalFastParity_certificate
    ⟨(b &&& (b >>> 12)) % 4096, Nat.mod_lt _ (by decide)⟩).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
