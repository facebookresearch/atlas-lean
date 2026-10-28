/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact unpadded interval lookup for finite source-path vector candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData15
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData16
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData17
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData18
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData19
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData20
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData21
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData22
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData23
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData24
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData25
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData26
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData27
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData28
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData29
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData30
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData31
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData32
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData33
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData34
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData35
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData36
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData37
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData38
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData39
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData40
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData41
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData42
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData43
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData44
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData45
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData46
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData47
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData48
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData49
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData50
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData51
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData52
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData53
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData54
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData55
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData56
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData57
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData58
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData59
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData60
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData61
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData62
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData63
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData64
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData65
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData66
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData67
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData68
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData69
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3VectorData70

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422TPathData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A coordinate interval with its exact source-path offset and actual finite size. -/
structure Y422Orthogonal3VectorChunk where
  /-- Exact first original path index. -/
  offset : ℕ
  /-- Exact number of path vectors. -/
  size : ℕ
  /-- Literal finite vector coordinates. -/
  data : Fin size → Fin 8 → ZMod 3

set_option maxRecDepth 100000 in
/-- All exact coordinate intervals, retaining the final 73-entry interval. -/
def y422Orthogonal3VectorChunks : Fin 71 → Y422Orthogonal3VectorChunk :=
  ![⟨0, 128, y422Orthogonal3VectorData00⟩,
    ⟨128, 128, y422Orthogonal3VectorData01⟩,
    ⟨256, 128, y422Orthogonal3VectorData02⟩,
    ⟨384, 128, y422Orthogonal3VectorData03⟩,
    ⟨512, 128, y422Orthogonal3VectorData04⟩,
    ⟨640, 128, y422Orthogonal3VectorData05⟩,
    ⟨768, 128, y422Orthogonal3VectorData06⟩,
    ⟨896, 128, y422Orthogonal3VectorData07⟩,
    ⟨1024, 128, y422Orthogonal3VectorData08⟩,
    ⟨1152, 128, y422Orthogonal3VectorData09⟩,
    ⟨1280, 128, y422Orthogonal3VectorData10⟩,
    ⟨1408, 128, y422Orthogonal3VectorData11⟩,
    ⟨1536, 128, y422Orthogonal3VectorData12⟩,
    ⟨1664, 128, y422Orthogonal3VectorData13⟩,
    ⟨1792, 128, y422Orthogonal3VectorData14⟩,
    ⟨1920, 128, y422Orthogonal3VectorData15⟩,
    ⟨2048, 128, y422Orthogonal3VectorData16⟩,
    ⟨2176, 128, y422Orthogonal3VectorData17⟩,
    ⟨2304, 128, y422Orthogonal3VectorData18⟩,
    ⟨2432, 128, y422Orthogonal3VectorData19⟩,
    ⟨2560, 128, y422Orthogonal3VectorData20⟩,
    ⟨2688, 128, y422Orthogonal3VectorData21⟩,
    ⟨2816, 128, y422Orthogonal3VectorData22⟩,
    ⟨2944, 128, y422Orthogonal3VectorData23⟩,
    ⟨3072, 128, y422Orthogonal3VectorData24⟩,
    ⟨3200, 128, y422Orthogonal3VectorData25⟩,
    ⟨3328, 128, y422Orthogonal3VectorData26⟩,
    ⟨3456, 128, y422Orthogonal3VectorData27⟩,
    ⟨3584, 128, y422Orthogonal3VectorData28⟩,
    ⟨3712, 128, y422Orthogonal3VectorData29⟩,
    ⟨3840, 128, y422Orthogonal3VectorData30⟩,
    ⟨3968, 128, y422Orthogonal3VectorData31⟩,
    ⟨4096, 128, y422Orthogonal3VectorData32⟩,
    ⟨4224, 128, y422Orthogonal3VectorData33⟩,
    ⟨4352, 128, y422Orthogonal3VectorData34⟩,
    ⟨4480, 128, y422Orthogonal3VectorData35⟩,
    ⟨4608, 128, y422Orthogonal3VectorData36⟩,
    ⟨4736, 128, y422Orthogonal3VectorData37⟩,
    ⟨4864, 128, y422Orthogonal3VectorData38⟩,
    ⟨4992, 128, y422Orthogonal3VectorData39⟩,
    ⟨5120, 128, y422Orthogonal3VectorData40⟩,
    ⟨5248, 128, y422Orthogonal3VectorData41⟩,
    ⟨5376, 128, y422Orthogonal3VectorData42⟩,
    ⟨5504, 128, y422Orthogonal3VectorData43⟩,
    ⟨5632, 128, y422Orthogonal3VectorData44⟩,
    ⟨5760, 128, y422Orthogonal3VectorData45⟩,
    ⟨5888, 128, y422Orthogonal3VectorData46⟩,
    ⟨6016, 128, y422Orthogonal3VectorData47⟩,
    ⟨6144, 128, y422Orthogonal3VectorData48⟩,
    ⟨6272, 128, y422Orthogonal3VectorData49⟩,
    ⟨6400, 128, y422Orthogonal3VectorData50⟩,
    ⟨6528, 128, y422Orthogonal3VectorData51⟩,
    ⟨6656, 128, y422Orthogonal3VectorData52⟩,
    ⟨6784, 128, y422Orthogonal3VectorData53⟩,
    ⟨6912, 128, y422Orthogonal3VectorData54⟩,
    ⟨7040, 128, y422Orthogonal3VectorData55⟩,
    ⟨7168, 128, y422Orthogonal3VectorData56⟩,
    ⟨7296, 128, y422Orthogonal3VectorData57⟩,
    ⟨7424, 128, y422Orthogonal3VectorData58⟩,
    ⟨7552, 128, y422Orthogonal3VectorData59⟩,
    ⟨7680, 128, y422Orthogonal3VectorData60⟩,
    ⟨7808, 128, y422Orthogonal3VectorData61⟩,
    ⟨7936, 128, y422Orthogonal3VectorData62⟩,
    ⟨8064, 128, y422Orthogonal3VectorData63⟩,
    ⟨8192, 128, y422Orthogonal3VectorData64⟩,
    ⟨8320, 128, y422Orthogonal3VectorData65⟩,
    ⟨8448, 128, y422Orthogonal3VectorData66⟩,
    ⟨8576, 128, y422Orthogonal3VectorData67⟩,
    ⟨8704, 128, y422Orthogonal3VectorData68⟩,
    ⟨8832, 128, y422Orthogonal3VectorData69⟩,
    ⟨8960, 73, y422Orthogonal3VectorData70⟩]

/-- The coordinate interval begins at its original source-path index. -/
theorem y422Orthogonal3VectorChunks_offset (b : Fin 71) :
    (y422Orthogonal3VectorChunks b).offset = 128 * b.val := by
  revert b
  decide +kernel

/-- The final interval has its actual finite size. -/
theorem y422Orthogonal3VectorChunks_size (b : Fin 71) :
    (y422Orthogonal3VectorChunks b).size = if b.val < 70 then 128 else 73 := by
  revert b
  decide +kernel

/-- The unique finite interval containing an original source path. -/
def y422Orthogonal3VectorBlock (i : Fin 9033) : Fin 71 := ⟨i.val / 128, by omega⟩

/-- The exact finite local coordinate index, including the final shorter interval. -/
def y422Orthogonal3VectorLocal (i : Fin 9033) :
    Fin (y422Orthogonal3VectorChunks (y422Orthogonal3VectorBlock i)).size :=
  ⟨i.val % 128, by
    rw [y422Orthogonal3VectorChunks_size]
    unfold y422Orthogonal3VectorBlock
    dsimp only
    split_ifs <;> omega⟩

/-- Literal candidate vector at an exact original source-path index. -/
def y422Orthogonal3VectorCache (i : Fin 9033) : Fin 8 → ZMod 3 :=
  (y422Orthogonal3VectorChunks (y422Orthogonal3VectorBlock i)).data
    (y422Orthogonal3VectorLocal i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
