/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1AutomorphismNonsplitCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMaskVectors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorOperatorsFive

/-! Finite binary data for original Conway generators and a possible lifting obstruction. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Full binary column masks of the five original Conway operators. -/
def co1NonsplitColumnMasks : Fin 5 → Fin 24 → ℕ := ![![57344, 53248, 45056, 28672, 16, 32, 64,
    128, 256, 512, 8388608, 4194304, 4110, 8205, 16395, 32775, 65536, 131072, 262144, 524288,
    1048576, 2097152, 4196352, 8389632],
    ![133121, 2754562, 1968132, 3541000, 16, 61472, 2146368, 3170432, 573696, 827904, 1024, 2048,
    4096, 8192, 16384, 32768, 67584, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8450064],
    ![67585, 1378306, 3737604, 2951176, 61456, 32, 3186752, 1097856, 811264, 311808, 1024, 2048,
    4096, 8192, 16384, 32768, 65536, 133120, 262144, 524288, 1048576, 2097152, 4194304, 8450080],
    ![4259837, 3150606, 7325964, 6277644, 4129584, 2550305, 4129728, 1505615, 49164, 4241412,
    51198, 2048, 987136, 4403200, 1454080, 2699264, 4259840, 196608, 4718592, 786432, 3190784,
    49152, 5181440, 12570624],
    ![377516, 1033212, 46084, 29704, 2109456, 2105408, 1060896, 1056896, 786483, 196813, 1024,
    2048, 3145728, 1048576, 2125824, 2142208, 1122304, 1323008, 2236416, 2633728, 8192, 12288,
    4243456, 8388608]]

/-- Upper-triangular cocycle difference masks for the canonical central cochains. -/
def co1NonsplitPhaseMasks : Fin 5 → Fin 24 → ℕ := ![![4096, 8192, 16384, 32768, 0, 0, 0, 0, 0, 0,
    4194304, 8388608, 57344, 49152, 32768, 0, 0, 0, 0, 0, 0, 0, 8388608, 0],
    ![32, 672, 480, 864, 0, 0, 512, 768, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0, 0],
    ![16, 336, 912, 720, 0, 0, 768, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8388608, 0, 0, 0, 0, 0, 0],
    ![546, 12, 728, 624, 0, 512, 0, 512, 512, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![828, 252, 8, 0, 512, 256, 512, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- The ordinary vector action, evaluated using exact XOR of selected original columns. -/
def co1NonsplitMaskVector (k : Fin 5) (v : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 24 =>
    if v.testBit i.val then co1NonsplitColumnMasks k i else 0))

/-- The canonical central cochain evaluated by finite exact bit parities. -/
def co1NonsplitMaskPhase (k : Fin 5) (v : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 24 =>
    if v.testBit i.val then monsterCo1GeometryBinaryMaskDot 24
      (co1NonsplitPhaseMasks k i) v else 0))

/-- The correction coordinates selected by a base input to one original generator. -/
def co1NonsplitMaskVariables (k : Fin 5) (v : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 24 =>
    if v.testBit i.val then 2 ^ (24 * k.val + i.val) else 0))

/-- A symbolic lifted state retains base, constant central bit and all 120 correction bits. -/
abbrev Co1NonsplitMaskState := ℕ × (ℕ × ℕ)

/-- One original generator acts on the exact symbolic phase state. -/
def co1NonsplitMaskStep (k : Fin 5) (s : Co1NonsplitMaskState) : Co1NonsplitMaskState :=
  (co1NonsplitMaskVector k s.1,
    (Nat.xor s.2.1 (co1NonsplitMaskPhase k s.1),
      Nat.xor s.2.2 (co1NonsplitMaskVariables k s.1)))

/-- Evaluate an original positive word in left-action order on a symbolic state. -/
def co1NonsplitMaskRun (w : List (Fin 5)) (s : Co1NonsplitMaskState) :
    Co1NonsplitMaskState := w.foldl (fun s k => co1NonsplitMaskStep k s) s

/-- Fourteen explicit original binary word-power relations used by the phase equations. -/
def co1NonsplitRelationWords : Fin 14 → List (Fin 5) := ![List.flatten (List.replicate 2 [1]),
    List.flatten (List.replicate 2 [2]),
    List.flatten (List.replicate 7 [3]),
    List.flatten (List.replicate 2 [4]),
    List.flatten (List.replicate 6 [0, 1]),
    List.flatten (List.replicate 6 [0, 2]),
    List.flatten (List.replicate 2 [1, 2]),
    List.flatten (List.replicate 14 [1, 3]),
    List.flatten (List.replicate 2 [1, 4]),
    List.flatten (List.replicate 14 [2, 3]),
    List.flatten (List.replicate 4 [2, 4]),
    List.flatten (List.replicate 6 [3, 4]),
    List.flatten (List.replicate 7 [1, 3, 3, 2, 3, 3, 3]),
    List.flatten (List.replicate 12 [2, 4, 2, 1, 3])]

/-- Relation index and original coordinate unit for each selected central-phase equation. -/
def co1NonsplitEquationInput : Fin 28 → Fin 14 × Fin 24 := ![(0, 1), (0, 2), (0, 6), (0, 16), (1,
    1), (1, 2), (1, 6), (1, 17), (2, 0), (2, 2), (2, 3), (3, 4), (4, 7), (5, 7), (6, 0), (7, 23),
    (8, 0), (8, 2), (8, 3), (8, 6), (8, 7), (8, 9), (9, 23), (10, 0), (11, 23), (12, 0), (12, 3),
    (13, 23)]

/-- Literal correction-variable row and constant bit for each selected equation. -/
def co1NonsplitEquationMasks : Fin 28 → ℕ × ℕ := ![(46213848104960, 0),
    (33019708571648, 0),
    (36009005809664, 0),
    (34359738368, 0),
    (387958086300204007424, 0),
    (1052040872953747865600, 0),
    (896972930584126947328, 0),
    (576460752303423488, 0),
    (21093337700636049840273358848, 0),
    (28366235431437658955305713664, 0),
    (23329888245854976770641494016, 1),
    (167127055134089764293325350596771840, 0),
    (4398046773248, 0),
    (73786976294838468608, 0),
    (55340235554023276544, 0),
    (15379992056069187489845215232, 0),
    (40456831221796398555774270509678592, 0),
    (159581998761531342895650765921058816, 0),
    (282899049151733499073276167141195776, 0),
    (254105633418149496447638562760818688, 0),
    (167451573687748191020143965867343872, 0),
    (81186445007129409225906947543269376, 0),
    (19732125412656576956215590912, 0),
    (83725786843874392963802441875193856, 0),
    (649686167906345427214435442686427136, 0),
    (21093338957897025552629366784, 0),
    (9499778924116150098971328512, 1),
    (649848427192847057094065515137073152, 1)]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
