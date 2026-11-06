/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthForestData15

/-! The complete proposed Twelfth binary-forest code table and its fast readers.

The sixteen parts form one balanced tree of depth twelve whose address bits are consumed from
the least significant end, so the leaf of a mask `b` is addressed by `b >>> 12` and holds the
code bytes of the 4096 masks with that high part. The readers are recursor-form arithmetic; the
proposed ranks and edges carry no meaning until the separate descent checks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The complete proposed code tree. -/
def generatedAxisGlobalTwelveTwelfthForestTree : GeneratedAxisGlobalMaskTree :=
  (.node
    (.node
      (.node
        (.node
          generatedAxisGlobalTwelveTwelfthForestData00
          generatedAxisGlobalTwelveTwelfthForestData08)
        (.node
          generatedAxisGlobalTwelveTwelfthForestData04
          generatedAxisGlobalTwelveTwelfthForestData12))
      (.node
        (.node
          generatedAxisGlobalTwelveTwelfthForestData02
          generatedAxisGlobalTwelveTwelfthForestData10)
        (.node
          generatedAxisGlobalTwelveTwelfthForestData06
          generatedAxisGlobalTwelveTwelfthForestData14)))
    (.node
      (.node
        (.node
          generatedAxisGlobalTwelveTwelfthForestData01
          generatedAxisGlobalTwelveTwelfthForestData09)
        (.node
          generatedAxisGlobalTwelveTwelfthForestData05
          generatedAxisGlobalTwelveTwelfthForestData13))
      (.node
        (.node
          generatedAxisGlobalTwelveTwelfthForestData03
          generatedAxisGlobalTwelveTwelfthForestData11)
        (.node
          generatedAxisGlobalTwelveTwelfthForestData07
          generatedAxisGlobalTwelveTwelfthForestData15))))

/-- Read a leaf, consuming address bits from the least significant end. -/
def generatedAxisGlobalTwelveTwelfthLeaf : GeneratedAxisGlobalMaskTree → ℕ → ℕ :=
  fun t => GeneratedAxisGlobalMaskTree.rec (motive := fun _ => ℕ → ℕ) (fun v _ => v)
    (fun _ _ il ir b => Bool.rec (il (Nat.shiftRight b 1)) (ir (Nat.shiftRight b 1))
      (Nat.beq (Nat.land b 1) 1)) t

/-- The proposed code byte of a coordinate mask. -/
def generatedAxisGlobalTwelveTwelfthCode (b : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight
    (generatedAxisGlobalTwelveTwelfthLeaf generatedAxisGlobalTwelveTwelfthForestTree
      (Nat.shiftRight b 12)) (Nat.mul 8 (Nat.land b 4095))) 255

/-- The proposed descent rank of a coordinate mask: the low four code bits. -/
def generatedAxisGlobalTwelveTwelfthRank (b : ℕ) : ℕ :=
  Nat.land (generatedAxisGlobalTwelveTwelfthCode b) 15

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
