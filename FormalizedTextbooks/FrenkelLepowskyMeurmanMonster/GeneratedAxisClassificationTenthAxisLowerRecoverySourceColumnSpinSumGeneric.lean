/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceDeltaZeroCachedB

/-! Ungated exact regrouping by the original first atom index, which selects the physical column. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original physical coordinate is determined by p.1; p.2 is the spin term in that column. -/
theorem generatedTenth_source_column_spin_sum_coordinate (r n : Fin 8) :
    generatedTenthSourceInitialTensorSparseCoordinate (r, n) =
      generatedTwelfthTensorSourceCoordinate r := by
  rfl

/-- Eight original paired spin contributions make the complete integer spin sum in one column. -/
def generatedTenthSourceColumnSpinSum (r : Fin 8) (k : Fin 4096) : ℤ :=
  ∑ n : Fin 8, generatedTenthSourceInitialTensorSparseSign (r, n) *
    (generatedTenthSourceDeltaZeroCachedSign (r, n) 0 (golayLabelCoefficients k) -
      generatedTenthSourceDeltaZeroCachedSign (r, n) 1 (golayLabelCoefficients k))

/-- Six packed bit planes with offset32 give a complete signed lookup at all4096 labels. -/
def generatedTenthSourceColumnSpinSumDecode
    (planes : Fin 4 → Fin 4 → Fin 6 → ℕ) (k : Fin 4096) : ℤ :=
  let row : Fin 4 := ⟨k.val / 1024, by have h := k.isLt; omega⟩
  let column : Fin 4 := ⟨(k.val / 256) % 4, Nat.mod_lt _ (by decide)⟩
  ((∑ bit : Fin 6, if (planes row column bit).testBit (k.val % 256) then
      2 ^ bit.val else 0 : ℕ) : ℤ) - 32

/-- Every closed block retains complete original source equality and useful integer bounds. -/
def GeneratedTenthSourceColumnSpinSumBlockCertificate (r : Fin 8)
    (cache : Fin 4096 → ℤ) (b : Fin 16) : Prop :=
  ∀ u : Fin 256,
    let k := generatedTenthSourceDeltaZeroSignCacheBlockLabel b u
    cache k = generatedTenthSourceColumnSpinSum r k ∧ 4 ∣ cache k ∧ |cache k| ≤ 16

/-- The full32768-entry finite cache certificate retains source, divisibility, and bounds. -/
def GeneratedTenthSourceColumnSpinSumCacheCertificate (cache : Fin 8 → Fin 4096 → ℤ) : Prop :=
  ∀ r k, cache r k = generatedTenthSourceColumnSpinSum r k ∧
    4 ∣ cache r k ∧ |cache r k| ≤ 16

/-- Exact source equality alone suffices for the genuine tensor regrouping. -/
def GeneratedTenthSourceColumnSpinSumSourceCertificate (cache : Fin 8 → Fin 4096 → ℤ) : Prop :=
  ∀ r k, cache r k = generatedTenthSourceColumnSpinSum r k

/-- The closed128 blocks cover all8times4096 original source values. -/
theorem generatedTenth_source_column_spin_sum_of_blocks
    (cache : Fin 8 → Fin 4096 → ℤ)
    (h : ∀ r b, GeneratedTenthSourceColumnSpinSumBlockCertificate r (cache r) b) :
    GeneratedTenthSourceColumnSpinSumCacheCertificate cache := by
  intro r k
  let b : Fin 16 := ⟨k.val / 256, by have hk := k.isLt; omega⟩
  let u : Fin 256 := ⟨k.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : generatedTenthSourceDeltaZeroSignCacheBlockLabel b u = k := by
    apply Fin.ext
    dsimp [generatedTenthSourceDeltaZeroSignCacheBlockLabel, b, u]
    omega
  have hh := h r b u
  simpa only [he] using hh

/-- The original64 paired terms regroup exactly into their8 genuine physical columns. -/
theorem generatedTenth_source_column_spin_sum_regroup
    (P : Matrix (Fin 24) (Fin 24) ℚ) (k : Fin 4096) (i : Fin 24) :
    generatedTenthSourceDeltaZeroCachedIncomingQ P k i =
      ∑ r : Fin 8, (generatedTenthSourceColumnSpinSum r k : ℚ) *
        P i (generatedTwelfthTensorSourceCoordinate r) := by
  unfold generatedTenthSourceDeltaZeroCachedIncomingQ generatedTenthSourceColumnSpinSum
  rw [Fintype.sum_prod_type]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_sub, Finset.sum_mul,
    generatedTenthSourceInitialTensorSparseCoordinate]

/-- Every cached source spin sum is multiplied by its exact original physical source column. -/
def generatedTenthSourceColumnSpinSumIncomingQ
    (cache : Fin 8 → Fin 4096 → ℤ) (P : Matrix (Fin 24) (Fin 24) ℚ)
    (k : Fin 4096) (i : Fin 24) : ℚ :=
  ∑ r : Fin 8, (cache r k : ℚ) * P i (generatedTwelfthTensorSourceCoordinate r)

/-- Source cache equality proves every rational8-column value equals the original64-pair sum. -/
theorem generatedTenth_source_column_spin_sum_incoming_eq
    (cache : Fin 8 → Fin 4096 → ℤ)
    (hcache : GeneratedTenthSourceColumnSpinSumSourceCertificate cache)
    (P : Matrix (Fin 24) (Fin 24) ℚ) (k : Fin 4096) (i : Fin 24) :
    generatedTenthSourceColumnSpinSumIncomingQ cache P k i =
      generatedTenthSourceDeltaZeroCachedIncomingQ P k i := by
  have hc : cache = generatedTenthSourceColumnSpinSum :=
    funext (fun r => funext (hcache r))
  rw [hc, generatedTenth_source_column_spin_sum_regroup]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

