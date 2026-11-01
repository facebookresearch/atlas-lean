/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact interval assembly of checked finite sources data. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceBindings00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceBindings01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceBindings02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceBindings03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceBindings04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceBindings05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceBindings06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceBindings07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceBindings08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceBindings09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceBindings10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceBindings11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceBindings12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceBindings13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC522CosetSourceBindings14

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A finite source interval retaining its exact offset, size, data, and checked evidence. -/
structure Y522CosetSourceChunk where
  /-- Exact first global index in the interval. -/
  offset : ℕ
  /-- Exact number of entries in the interval. -/
  size : ℕ
  /-- Literal source equations in this interval. -/
  data : Fin size → Y322WordEquation (Fin 1806)
  /-- Each equation has an independently proved original-source value. -/
  valid : ∀ j, (data j).Valid y522CosetSymbol

/-- Independently checked intervals covering the exact finite certificate alphabet. -/
def y522CosetSourcesChunks : Fin 15 → Y522CosetSourceChunk :=
  ![⟨0, 128, y522CosetSourceEquation00, y522CosetSourceEquation00_valid⟩,
    ⟨128, 128, y522CosetSourceEquation01, y522CosetSourceEquation01_valid⟩,
    ⟨256, 128, y522CosetSourceEquation02, y522CosetSourceEquation02_valid⟩,
    ⟨384, 128, y522CosetSourceEquation03, y522CosetSourceEquation03_valid⟩,
    ⟨512, 128, y522CosetSourceEquation04, y522CosetSourceEquation04_valid⟩,
    ⟨640, 128, y522CosetSourceEquation05, y522CosetSourceEquation05_valid⟩,
    ⟨768, 128, y522CosetSourceEquation06, y522CosetSourceEquation06_valid⟩,
    ⟨896, 128, y522CosetSourceEquation07, y522CosetSourceEquation07_valid⟩,
    ⟨1024, 128, y522CosetSourceEquation08, y522CosetSourceEquation08_valid⟩,
    ⟨1152, 128, y522CosetSourceEquation09, y522CosetSourceEquation09_valid⟩,
    ⟨1280, 128, y522CosetSourceEquation10, y522CosetSourceEquation10_valid⟩,
    ⟨1408, 128, y522CosetSourceEquation11, y522CosetSourceEquation11_valid⟩,
    ⟨1536, 128, y522CosetSourceEquation12, y522CosetSourceEquation12_valid⟩,
    ⟨1664, 128, y522CosetSourceEquation13, y522CosetSourceEquation13_valid⟩,
    ⟨1792, 71, y522CosetSourceEquation14, y522CosetSourceEquation14_valid⟩]

/-- Interval offsets agree with the exact uniform indexing, including the final interval. -/
theorem y522CosetSourcesChunks_offset (b : Fin 15) :
    (y522CosetSourcesChunks b).offset = 128 * b.val := by
  revert b
  decide +kernel

/-- The final interval retains its actual size rather than padding extra entries. -/
theorem y522CosetSourcesChunks_size (b : Fin 15) :
    (y522CosetSourcesChunks b).size = if b.val < 14 then 128 else 71 := by
  revert b
  decide +kernel

/-- Every actual interval lies inside the exact global finite bound. -/
theorem y522CosetSourcesChunks_end (b : Fin 15) :
    (y522CosetSourcesChunks b).offset + (y522CosetSourcesChunks b).size ≤ 1863 := by
  rw [y522CosetSourcesChunks_offset, y522CosetSourcesChunks_size]
  split_ifs <;> omega

/-- The unique interval containing a given actual finite index. -/
def y522CosetSourcesBlock (i : Fin 1863) : Fin 15 := ⟨i.val / 128, by omega⟩

/-- The exact local index inside that interval, with the final shorter bound checked. -/
def y522CosetSourcesLocal (i : Fin 1863) :
    Fin (y522CosetSourcesChunks (y522CosetSourcesBlock i)).size :=
  ⟨i.val % 128, by
    rw [y522CosetSourcesChunks_size]
    unfold y522CosetSourcesBlock
    dsimp only
    split_ifs <;> omega⟩

/-- Assemble a local interval index into its exact original global index. -/
def y522CosetSourcesGlobal (b : Fin 15) (j : Fin (y522CosetSourcesChunks b).size) : Fin 1863 :=
  ⟨(y522CosetSourcesChunks b).offset + j.val,
    (Nat.add_lt_add_left j.isLt _).trans_le (y522CosetSourcesChunks_end b)⟩

/-- Interval lookup and assembly preserve the original index exactly. -/
theorem y522CosetSourcesGlobal_local (i : Fin 1863) :
    y522CosetSourcesGlobal (y522CosetSourcesBlock i) (y522CosetSourcesLocal i) = i := by
  apply Fin.ext
  change (y522CosetSourcesChunks (y522CosetSourcesBlock i)).offset + i.val % 128 = i.val
  rw [y522CosetSourcesChunks_offset]
  unfold y522CosetSourcesBlock
  dsimp only
  omega

/-- Lookup retains the actual literal entry, with no out-of-range fallback. -/
def y522CosetSourcesData (i : Fin 1863) :=
  (y522CosetSourcesChunks (y522CosetSourcesBlock i)).data (y522CosetSourcesLocal i)

/-- Every assembled source is independently valid in the actual original Y555 group. -/
theorem y522CosetSourcesData_valid (i : Fin 1863) :
    (y522CosetSourcesData i).Valid y522CosetSymbol :=
  (y522CosetSourcesChunks (y522CosetSourcesBlock i)).valid (y522CosetSourcesLocal i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
