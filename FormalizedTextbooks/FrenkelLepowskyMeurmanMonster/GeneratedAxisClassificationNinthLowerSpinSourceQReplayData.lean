/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacketData00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacketData01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacketData02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacketData03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacketData04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacketData05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacketData06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacketData07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacketData08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacketData09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayPacketData10

/-! Bounded full extraspecial prefix replay with actual central phases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000

/-- The complete original source word data for all eleven generators. -/
def generatedNinthLowerSpinSourceQReplayWord : Fin 11 → Fin 379 → Fin 24 → ℕ :=
  ![generatedNinthLowerSpinSourceQReplayWord00,
    generatedNinthLowerSpinSourceQReplayWord01,
    generatedNinthLowerSpinSourceQReplayWord02,
    generatedNinthLowerSpinSourceQReplayWord03,
    generatedNinthLowerSpinSourceQReplayWord04,
    generatedNinthLowerSpinSourceQReplayWord05,
    generatedNinthLowerSpinSourceQReplayWord06,
    generatedNinthLowerSpinSourceQReplayWord07,
    generatedNinthLowerSpinSourceQReplayWord08,
    generatedNinthLowerSpinSourceQReplayWord09,
    generatedNinthLowerSpinSourceQReplayWord10]

/-- The complete original source letter data for all eleven generators. -/
def generatedNinthLowerSpinSourceQReplayLetter : Fin 11 → Fin 378 → GeneratedNinthLowerSpinLetter :=
  ![generatedNinthLowerSpinSourceQReplayLetter00,
    generatedNinthLowerSpinSourceQReplayLetter01,
    generatedNinthLowerSpinSourceQReplayLetter02,
    generatedNinthLowerSpinSourceQReplayLetter03,
    generatedNinthLowerSpinSourceQReplayLetter04,
    generatedNinthLowerSpinSourceQReplayLetter05,
    generatedNinthLowerSpinSourceQReplayLetter06,
    generatedNinthLowerSpinSourceQReplayLetter07,
    generatedNinthLowerSpinSourceQReplayLetter08,
    generatedNinthLowerSpinSourceQReplayLetter09,
    generatedNinthLowerSpinSourceQReplayLetter10]

/-- Decode both full binary halves and the genuine central bit of a cached Q prefix. -/
def generatedNinthLowerSpinSourceQReplayDecode (w : ℕ) : Q :=
  ⟨ofAdd (Fin.append
    (golayLabelCoefficients ⟨w % 4096, Nat.mod_lt _ (by decide)⟩)
    (golayLabelCoefficients ⟨(w / 4096) % 4096, Nat.mod_lt _ (by decide)⟩)),
    ofAdd ((w / 16777216 : ℕ) : ZMod 2)⟩

/-- The complete actual Q prefix at every source stage and original coordinate. -/
def generatedNinthLowerSpinSourceQReplayPrefix (i : Fin 11) (n : Fin 379) (j : Fin 24) : Q :=
  generatedNinthLowerSpinSourceQReplayDecode (generatedNinthLowerSpinSourceQReplayWord i n j)

/-- All actual source words fit in the bounded379 normalized prefixes. -/
theorem generatedNinth_lower_spin_source_q_replay_length : ∀ i : Fin 11,
    (generatedNinthLowerSpinSourceWord i).length < 379 := by
  decide +kernel

/-- Every literal chronological primitive is the identical original source word letter. -/
def generatedNinthLowerSpinSourceQReplayLetterCondition (i : Fin 11) (n : Fin 378) : Prop :=
  n.val < (generatedNinthLowerSpinSourceWord i).length →
    (generatedNinthLowerSpinSourceWord i).reverse[n.val]? =
      some (generatedNinthLowerSpinSourceQReplayLetter i n)

/-- The entire initial Q prefix is the actual original coordinate lift. -/
def generatedNinthLowerSpinSourceQReplayBaseCondition (i : Fin 11) (j : Fin 24) : Prop :=
  generatedNinthLowerSpinSourceQReplayPrefix i 0 j = qCoordinateGenerator j

/-- One source replay step checks the original full-Q primitive action on a literal full-Q
prefix. Every actual stage is included; positions beyond the original length are vacuous. -/
def generatedNinthLowerSpinSourceQReplayStepCondition (i : Fin 11) (n : Fin 378)
    (j : Fin 24) : Prop :=
  n.val < (generatedNinthLowerSpinSourceWord i).length →
    generatedNinthLowerSpinPrimitiveQEvaluation (generatedNinthLowerSpinSourceQReplayLetter i n)
      (generatedNinthLowerSpinSourceQReplayPrefix i (Fin.castAdd 1 n) j) =
        generatedNinthLowerSpinSourceQReplayPrefix i ⟨n.val + 1, by omega⟩ j

/-- The entire final normalized prefix is the full original proposed Q image. -/
def generatedNinthLowerSpinSourceQReplayFinishCondition (i : Fin 11) (j : Fin 24) : Prop :=
  generatedNinthLowerSpinSourceQReplayPrefix i
    ⟨(generatedNinthLowerSpinSourceWord i).length,
      generatedNinth_lower_spin_source_q_replay_length i⟩ j =
    generatedNinthLowerSpinQImage i j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
