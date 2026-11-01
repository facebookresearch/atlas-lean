/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerCSupportCertificateData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerCGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortBalancedMask
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinParityCircuit

/-! Ungated exact support enumeration and full preferred signed-Q certificate assemblers.
Only the required joint 9*1 and original 10 fibers are used. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Packed source addresses retain all 17 bits before the explicit finite domain check. -/
def generatedTenthTwoFixerCSupportRawSource (r : Fin 46082) : ℕ :=
  (generatedNinthLowerSpinShortWord generatedTenthTwoFixerCSupportSourceWords
    ⟨r.val, by omega⟩ >>> (17 * (r.val % 16))) % 2 ^ 17

/-- Both required targets retain their original 17-bit address and complete central phase. -/
def generatedTenthTwoFixerCSupportRawTarget (g : Fin 2) (r : Fin 46082) : ℕ :=
  (generatedNinthLowerSpinShortWord (generatedTenthTwoFixerCSupportTargetWords g)
    ⟨r.val, by omega⟩ >>> (18 * (r.val % 16))) % 2 ^ 17

/-- Bounded preferred-short source address; the raw-domain certificate remains separate. -/
def generatedTenthTwoFixerCSupportSource (r : Fin 46082) : Fin 98280 :=
  ⟨generatedTenthTwoFixerCSupportRawSource r % 98280, Nat.mod_lt _ (by decide)⟩

/-- Bounded preferred-short target address; the raw-domain certificate remains separate. -/
def generatedTenthTwoFixerCSupportTarget (g : Fin 2) (r : Fin 46082) : Fin 98280 :=
  ⟨generatedTenthTwoFixerCSupportRawTarget g r % 98280, Nat.mod_lt _ (by decide)⟩

/-- The full central phase is the original eighteenth bit of the packed target row. -/
def generatedTenthTwoFixerCSupportRowPhase (g : Fin 2) (r : Fin 46082) : ZMod 2 :=
  if (generatedNinthLowerSpinShortWord (generatedTenthTwoFixerCSupportTargetWords g)
    ⟨r.val, by omega⟩).testBit (18 * (r.val % 16) + 17) then 1 else 0

/-- Balanced lookup uses the complete original source address as the 17-bit dictionary key. -/
def generatedTenthTwoFixerCSupportRank (a : Fin 98280) : Fin 46082 :=
  match (generatedTenthTwoFixerCSupportDictionary ⟨a.val / 4096, by omega⟩).lookup
      (fun word => word % 2 ^ 17) a.val with
  | none => 0
  | some word => ⟨(word / 2 ^ 17) % 46082, Nat.mod_lt _ (by decide)⟩

/-- The zero-source default remains explicit and receives no unsupported transport claim. -/
def generatedTenthTwoFixerCSupportDestination (g : Fin 2) (a : Fin 98280) : Fin 98280 :=
  generatedTenthTwoFixerCSupportTarget g (generatedTenthTwoFixerCSupportRank a)

/-- The complete source-rank lookup selects its retained full central phase. -/
def generatedTenthTwoFixerCSupportPhase (g : Fin 2) (a : Fin 98280) : ZMod 2 :=
  generatedTenthTwoFixerCSupportRowPhase g (generatedTenthTwoFixerCSupportRank a)

/-- Every nonzero original address must occur in the retained complete support table. -/
def GeneratedTenthTwoFixerCSupportCoverage (a : Fin 98280) : Prop :=
  generatedTenthFinalShortPackedCacheCoefficient (generatedNinthLowerSpinShortIndex a) ≠ 0 →
    generatedTenthTwoFixerCSupportSource (generatedTenthTwoFixerCSupportRank a) = a

/-- Raw source/target domains, actual nonzero cache value, and the unchanged full-Q condition. -/
def GeneratedTenthTwoFixerCSupportRowCertificate (g : Fin 2) (r : Fin 46082) : Prop :=
  generatedTenthTwoFixerCSupportRawSource r < 98280 ∧
    generatedTenthTwoFixerCSupportRawTarget g r < 98280 ∧
    generatedTenthFinalShortPackedCacheCoefficient
      (generatedNinthLowerSpinShortIndex (generatedTenthTwoFixerCSupportSource r)) ≠ 0 ∧
    GeneratedTenthTwoFixerCPackedCondition g
      (fun _ => generatedTenthTwoFixerCSupportTarget g r)
      (fun _ => generatedTenthTwoFixerCSupportRowPhase g r)
      (generatedTenthTwoFixerCSupportSource r)

/-- The first 95 complete 1,024-address blocks retain every original source coordinate. -/
def generatedTenthTwoFixerCSupportCoverageLabel (b : Fin 95) (u : Fin 1024) : Fin 98280 :=
  ⟨1024 * b.val + u.val, by omega⟩

/-- The final source block has exactly 1,000 addresses, with no fabricated padding. -/
def generatedTenthTwoFixerCSupportCoverageTail (u : Fin 1000) : Fin 98280 :=
  ⟨97280 + u.val, by omega⟩

/-- The first 180 support blocks retain 256 genuine nonzero rows each. -/
def generatedTenthTwoFixerCSupportRowLabel (b : Fin 180) (u : Fin 256) : Fin 46082 :=
  ⟨256 * b.val + u.val, by omega⟩

/-- Exactly two rows form the final nonzero-support block. -/
def generatedTenthTwoFixerCSupportRowTail (u : Fin 2) : Fin 46082 :=
  ⟨46080 + u.val, by omega⟩

/-- Complete original source-address coverage follows from the independent finite packets. -/
theorem generatedTenth_two_fixer_c_support_coverage_of_blocks
    (h : ∀ b u, GeneratedTenthTwoFixerCSupportCoverage
      (generatedTenthTwoFixerCSupportCoverageLabel b u))
    (ht : ∀ u, GeneratedTenthTwoFixerCSupportCoverage
      (generatedTenthTwoFixerCSupportCoverageTail u)) :
    ∀ a, GeneratedTenthTwoFixerCSupportCoverage a := by
  intro a
  by_cases ha : a.val < 97280
  · let b : Fin 95 := ⟨a.val / 1024, by omega⟩
    let u : Fin 1024 := ⟨a.val % 1024, Nat.mod_lt _ (by decide)⟩
    have he : generatedTenthTwoFixerCSupportCoverageLabel b u = a := by
      apply Fin.ext
      dsimp [generatedTenthTwoFixerCSupportCoverageLabel, b, u]
      omega
    simpa only [he] using h b u
  · let u : Fin 1000 := ⟨a.val - 97280, by omega⟩
    have he : generatedTenthTwoFixerCSupportCoverageTail u = a := by
      apply Fin.ext
      dsimp [generatedTenthTwoFixerCSupportCoverageTail, u]
      omega
    simpa only [he] using ht u

/-- All 46,082 nonzero rows follow from bounded packets with an exact two-row tail. -/
theorem generatedTenth_two_fixer_c_support_rows_of_blocks (g : Fin 2)
    (h : ∀ b u, GeneratedTenthTwoFixerCSupportRowCertificate g
      (generatedTenthTwoFixerCSupportRowLabel b u))
    (ht : ∀ u, GeneratedTenthTwoFixerCSupportRowCertificate g
      (generatedTenthTwoFixerCSupportRowTail u)) :
    ∀ r, GeneratedTenthTwoFixerCSupportRowCertificate g r := by
  intro r
  by_cases hr : r.val < 46080
  · let b : Fin 180 := ⟨r.val / 256, by omega⟩
    let u : Fin 256 := ⟨r.val % 256, Nat.mod_lt _ (by decide)⟩
    have he : generatedTenthTwoFixerCSupportRowLabel b u = r := by
      apply Fin.ext
      dsimp [generatedTenthTwoFixerCSupportRowLabel, b, u]
      omega
    simpa only [he] using h b u
  · let u : Fin 2 := ⟨r.val - 46080, by omega⟩
    have he : generatedTenthTwoFixerCSupportRowTail u = r := by
      apply Fin.ext
      dsimp [generatedTenthTwoFixerCSupportRowTail, u]
      omega
    simpa only [he] using ht u

/-- Complete support coverage and full preferred row checks discharge the unchanged condition. -/
theorem generatedTenth_two_fixer_c_support_condition_of_rows (g : Fin 2)
    (hc : ∀ a, GeneratedTenthTwoFixerCSupportCoverage a)
    (hr : ∀ r, GeneratedTenthTwoFixerCSupportRowCertificate g r) :
    GeneratedTenthTwoFixerCSupportCondition g
      (generatedTenthTwoFixerCSupportDestination g) (generatedTenthTwoFixerCSupportPhase g) := by
  intro a ha
  have he := hc a ha
  have hp := (hr (generatedTenthTwoFixerCSupportRank a)).2.2.2
  dsimp only [GeneratedTenthTwoFixerCPackedCondition,
    generatedTenthTwoFixerCSupportDestination, generatedTenthTwoFixerCSupportPhase] at hp ⊢
  simpa only [he] using hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
