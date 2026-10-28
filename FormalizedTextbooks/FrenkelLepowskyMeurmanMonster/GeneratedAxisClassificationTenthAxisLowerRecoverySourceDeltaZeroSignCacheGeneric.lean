/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaZeroSignCacheData

/-! Ungated complete finite source sign certificate schema. No source orientation is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every block has exactly256 original labels, with no omitted endpoint. -/
def generatedTenthSourceDeltaZeroSignCacheBlockLabel (b : Fin 16) (u : Fin 256) : Fin 4096 :=
  ⟨256 * b.val + u.val, by have hb := b.isLt; have hu := u.isLt; omega⟩

/-- Complete source-specific phase equality on one closed256-label domain. -/
def GeneratedTenthSourceDeltaZeroSignCacheBlockCertificate (b : Fin 16) : Prop :=
  ∀ u : Fin 256,
    generatedTenthSourceDeltaZeroSignCache (generatedTenthSourceDeltaZeroSignCacheBlockLabel b u) =
      generatedAxisGlobalIntSign (generatedTenthSourceSparseFastDeltaZeroPhase
        (golayLabelCoefficients (generatedTenthSourceDeltaZeroSignCacheBlockLabel b u)))

/-- All4096 original source delta0 signs require their complete actual compact phase. -/
def GeneratedTenthSourceDeltaZeroSignCacheCertificate : Prop :=
  ∀ n : Fin 4096, generatedTenthSourceDeltaZeroSignCache n =
    generatedAxisGlobalIntSign
      (generatedTenthSourceSparseFastDeltaZeroPhase (golayLabelCoefficients n))

/-- All closed blocks cover the entire original spin label domain. -/
theorem generatedTenth_source_delta_zero_sign_cache_of_blocks
    (h : ∀ b : Fin 16, GeneratedTenthSourceDeltaZeroSignCacheBlockCertificate b) :
    GeneratedTenthSourceDeltaZeroSignCacheCertificate := by
  intro n
  let b : Fin 16 := ⟨n.val / 256, by have hn := n.isLt; omega⟩
  let u : Fin 256 := ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : generatedTenthSourceDeltaZeroSignCacheBlockLabel b u = n := by
    apply Fin.ext
    dsimp [generatedTenthSourceDeltaZeroSignCacheBlockLabel, b, u]
    omega
  have hh := h b u
  simpa only [he] using hh

/-- The computable label inverse binds the cache at every arbitrary genuine spin coordinate. -/
theorem generatedTenth_source_delta_zero_sign_cache_spin
    (h : GeneratedTenthSourceDeltaZeroSignCacheCertificate) (t : SpinIndex) :
    generatedTenthSourceDeltaZeroSignCache (generatedAxisGlobalSpinLabel t) =
      generatedAxisGlobalIntSign (generatedTenthSourceSparseFastDeltaZeroPhase t) := by
  have hh := h (generatedAxisGlobalSpinLabel t)
  rw [generatedAxisGlobalSpinLabel_decode] at hh
  exact hh

/-- The actual explicit source compact delta0 vector has the cached sign at normalization64. -/
theorem generatedTenth_source_delta_zero_sign_cache_actual
    (h : GeneratedTenthSourceDeltaZeroSignCacheCertificate) (t : SpinIndex) :
    (generatedTenthAxisLowerRecoverySourceCompactSpin 0).val
        (Pi.single (0 : SpinIndex) (1 : ℝ)) t =
      (generatedTenthSourceDeltaZeroSignCache (generatedAxisGlobalSpinLabel t) : ℝ) / 64 := by
  rw [generatedTenth_source_compact_delta_zero_phase,
    ← generatedTenth_source_sparse_fast_delta_zero_phase,
    ← generatedAxisGlobalIntSign_real,
    ← generatedTenth_source_delta_zero_sign_cache_spin h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

