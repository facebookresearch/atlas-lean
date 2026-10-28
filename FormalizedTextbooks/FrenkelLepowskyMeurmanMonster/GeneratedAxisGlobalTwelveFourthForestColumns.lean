/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthForestActions
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionMaskRows

/-! Exact compact forward and inverse columns for the five genuine Fourth forest actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Candidate genuine hyperbolic binary columns of the five generators. -/
def generatedAxisGlobalTwelveFourthBinaryColumns : Fin 5 → Fin 24 → ℕ :=
  ![![5345249, 3197446, 305408, 8221448, 1349108, 789028, 249643, 5408356, 636932, 4238084, 2660235,
      2048, 4460544, 4464640, 3874816, 4489216, 65536, 987136, 593920, 4263936, 6672384, 7254016,
      5050368, 11956224],
    ![3342337, 7340034, 1900552, 3014660, 544805, 299033, 6471820, 5357644, 4749832, 4503812,
      3944253, 2048, 4395008, 8192, 7176192, 6176768, 4325376, 4259840, 524288, 262144, 6291456,
      5242880, 4194304, 15728640],
    ![6825043, 2756878, 3801858, 1704450, 2097436, 7399284, 2097484, 5306004, 704524, 4681990,
      2757900, 2048, 4096, 2158592, 8331264, 5578752, 724992, 131072, 397312, 524288, 6774784,
      704512, 4853760, 8388608],
    ![2293761, 3473410, 6291460, 1441800, 536595, 823337, 5414986, 2293888, 303370, 4749832,
      2379067, 2048, 4395008, 5578752, 16384, 7766016, 4259840, 4325376, 262144, 524288, 5242880,
      2097152, 4194304, 14680064],
    ![57344, 7000064, 7976960, 5994496, 655388, 3012650, 2146368, 3303553, 180492, 2861574,
      10539088, 4194304, 659470, 534541, 3096587, 2457607, 67584, 131072, 4458496, 524288, 1048576,
      2097152, 4196352, 8584209]]

/-- The candidate column bits, interpreted in the actual hyperbolic coordinate convention. -/
def generatedAxisGlobalTwelveFourthCachedMatrix (k : Fin 5) : Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  fun i j => if (generatedAxisGlobalTwelveFourthBinaryColumns k j).testBit i.val then 1 else 0

set_option maxHeartbeats 40000000 in
-- Verify all 2880 entries of the five actual binary generator actions.
/-- Every candidate bit is equal to the genuine lattice-induced binary action. -/
theorem generatedAxisGlobalTwelveFourthCachedMatrix_certificate : ∀ k : Fin 5,
    generatedAxisGlobalTwelveFourthCachedMatrix k =
      generatedAxisGlobalTwelveFourthBinaryMatrix k := by
  decide +kernel

/-- Compact column-matrix evaluation is exactly the actual binary action. -/
theorem generatedAxisGlobalTwelveFourthBinaryColumns_certificate (k : Fin 5) :
    generatedAxisGlobalTwelveFourthBinaryMatrix k =
      generatedAxisGlobalMaskColumnMatrix (generatedAxisGlobalTwelveFourthBinaryColumns k) :=
  (generatedAxisGlobalTwelveFourthCachedMatrix_certificate k).symm

/-- Forward columns with explicit coordinate indices. -/
def generatedAxisGlobalTwelveFourthBinaryRows : Fin 5 → List (ℕ × ℕ) :=
  ![[(0, 5345249), (1, 3197446), (2, 305408), (3, 8221448), (4, 1349108), (5, 789028), (6, 249643),
      (7, 5408356), (8, 636932), (9, 4238084), (10, 2660235), (11, 2048), (12, 4460544),
      (13, 4464640), (14, 3874816), (15, 4489216), (16, 65536), (17, 987136), (18, 593920),
      (19, 4263936), (20, 6672384), (21, 7254016), (22, 5050368), (23, 11956224)],
    [(0, 3342337), (1, 7340034), (2, 1900552), (3, 3014660), (4, 544805), (5, 299033), (6, 6471820),
      (7, 5357644), (8, 4749832), (9, 4503812), (10, 3944253), (11, 2048), (12, 4395008),
      (13, 8192), (14, 7176192), (15, 6176768), (16, 4325376), (17, 4259840), (18, 524288),
      (19, 262144), (20, 6291456), (21, 5242880), (22, 4194304), (23, 15728640)],
    [(0, 6825043), (1, 2756878), (2, 3801858), (3, 1704450), (4, 2097436), (5, 7399284),
      (6, 2097484), (7, 5306004), (8, 704524), (9, 4681990), (10, 2757900), (11, 2048), (12, 4096),
      (13, 2158592), (14, 8331264), (15, 5578752), (16, 724992), (17, 131072), (18, 397312),
      (19, 524288), (20, 6774784), (21, 704512), (22, 4853760), (23, 8388608)],
    [(0, 2293761), (1, 3473410), (2, 6291460), (3, 1441800), (4, 536595), (5, 823337), (6, 5414986),
      (7, 2293888), (8, 303370), (9, 4749832), (10, 2379067), (11, 2048), (12, 4395008),
      (13, 5578752), (14, 16384), (15, 7766016), (16, 4259840), (17, 4325376), (18, 262144),
      (19, 524288), (20, 5242880), (21, 2097152), (22, 4194304), (23, 14680064)],
    [(0, 57344), (1, 7000064), (2, 7976960), (3, 5994496), (4, 655388), (5, 3012650), (6, 2146368),
      (7, 3303553), (8, 180492), (9, 2861574), (10, 10539088), (11, 4194304), (12, 659470),
      (13, 534541), (14, 3096587), (15, 2457607), (16, 67584), (17, 131072), (18, 4458496),
      (19, 524288), (20, 1048576), (21, 2097152), (22, 4196352), (23, 8584209)]]

/-- Forward column-XOR evaluation equals the genuine matrix action. -/
theorem generatedAxisGlobalTwelveFourthBinaryColumns_action (k : Fin 5) (b : ℕ) :
    generatedAxisGlobalTwelveFourthBinaryMatrix k *ᵥ monsterCo1GeometryBinaryMaskDecode b =
      monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalMaskColumnAction
          (generatedAxisGlobalTwelveFourthBinaryColumns k) b) := by
  rw [generatedAxisGlobalTwelveFourthBinaryColumns_certificate,
    ← generatedAxisGlobalMaskColumnAction_decode]

/-- Every indexed forward list retains the exact column order. -/
theorem generatedAxisGlobalTwelveFourthBinaryRows_certificate : ∀ k : Fin 5,
    generatedAxisGlobalTwelveFourthBinaryRows k =
      List.ofFn (fun j : Fin 24 => (j.val, generatedAxisGlobalTwelveFourthBinaryColumns k j)) := by
  decide +kernel

/-- Indexed forward evaluation has the actual column-matrix action. -/
theorem generatedAxisGlobalTwelveFourthBinaryRows_action (k : Fin 5) (b : ℕ) :
    generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveFourthBinaryRows k) b =
      generatedAxisGlobalMaskColumnAction (generatedAxisGlobalTwelveFourthBinaryColumns k) b := by
  rw [generatedAxisGlobalTwelveFourthBinaryRows_certificate, generatedAxisGlobalMaskRowsAction_ofFn]

/-- Candidate bounded inverse columns, separately checked against the forward action. -/
def generatedAxisGlobalTwelveFourthInverseColumns : Fin 5 → Fin 24 → ℕ :=
  ![![5345249, 3197446, 305408, 8221448, 1349108, 789028, 249643, 5408356, 636932, 4238084, 2660235,
      2048, 4460544, 4464640, 3874816, 4489216, 65536, 987136, 593920, 4263936, 6672384, 7254016,
      5050368, 11956224],
    ![3342337, 7340034, 1900552, 3014660, 544805, 299033, 6471820, 5357644, 4749832, 4503812,
      3944253, 2048, 4395008, 8192, 7176192, 6176768, 4325376, 4259840, 524288, 262144, 6291456,
      5242880, 4194304, 15728640],
    ![6825043, 2756878, 3801858, 1704450, 2097436, 7399284, 2097484, 5306004, 704524, 4681990,
      2757900, 2048, 4096, 2158592, 8331264, 5578752, 724992, 131072, 397312, 524288, 6774784,
      704512, 4853760, 8388608],
    ![2293761, 3473410, 6291460, 1441800, 536595, 823337, 5414986, 2293888, 303370, 4749832,
      2379067, 2048, 4395008, 5578752, 16384, 7766016, 4259840, 4325376, 262144, 524288, 5242880,
      2097152, 4194304, 14680064],
    ![4384769, 2807810, 6207492, 7763976, 2277404, 3778597, 131148, 2351239, 573696, 7234060,
      8447040, 4196352, 526350, 2228237, 3211275, 1245191, 4261888, 131072, 4456448, 524288,
      1048576, 2097152, 2048, 2804818]]

/-- Candidate inverse columns with their exact coordinate indices. -/
def generatedAxisGlobalTwelveFourthInverseRows : Fin 5 → List (ℕ × ℕ) :=
  ![[(0, 5345249), (1, 3197446), (2, 305408), (3, 8221448), (4, 1349108), (5, 789028), (6, 249643),
      (7, 5408356), (8, 636932), (9, 4238084), (10, 2660235), (11, 2048), (12, 4460544),
      (13, 4464640), (14, 3874816), (15, 4489216), (16, 65536), (17, 987136), (18, 593920),
      (19, 4263936), (20, 6672384), (21, 7254016), (22, 5050368), (23, 11956224)],
    [(0, 3342337), (1, 7340034), (2, 1900552), (3, 3014660), (4, 544805), (5, 299033), (6, 6471820),
      (7, 5357644), (8, 4749832), (9, 4503812), (10, 3944253), (11, 2048), (12, 4395008),
      (13, 8192), (14, 7176192), (15, 6176768), (16, 4325376), (17, 4259840), (18, 524288),
      (19, 262144), (20, 6291456), (21, 5242880), (22, 4194304), (23, 15728640)],
    [(0, 6825043), (1, 2756878), (2, 3801858), (3, 1704450), (4, 2097436), (5, 7399284),
      (6, 2097484), (7, 5306004), (8, 704524), (9, 4681990), (10, 2757900), (11, 2048), (12, 4096),
      (13, 2158592), (14, 8331264), (15, 5578752), (16, 724992), (17, 131072), (18, 397312),
      (19, 524288), (20, 6774784), (21, 704512), (22, 4853760), (23, 8388608)],
    [(0, 2293761), (1, 3473410), (2, 6291460), (3, 1441800), (4, 536595), (5, 823337), (6, 5414986),
      (7, 2293888), (8, 303370), (9, 4749832), (10, 2379067), (11, 2048), (12, 4395008),
      (13, 5578752), (14, 16384), (15, 7766016), (16, 4259840), (17, 4325376), (18, 262144),
      (19, 524288), (20, 5242880), (21, 2097152), (22, 4194304), (23, 14680064)],
    [(0, 4384769), (1, 2807810), (2, 6207492), (3, 7763976), (4, 2277404), (5, 3778597),
      (6, 131148), (7, 2351239), (8, 573696), (9, 7234060), (10, 8447040), (11, 4196352),
      (12, 526350), (13, 2228237), (14, 3211275), (15, 1245191), (16, 4261888), (17, 131072),
      (18, 4456448), (19, 524288), (20, 1048576), (21, 2097152), (22, 2048), (23, 2804818)]]

set_option maxHeartbeats 12000000 in
-- Check all 120 forward images of inverse columns and their exact bounded indexed lists.
/-- Each inverse column maps to the corresponding unit under the genuine forward action. -/
theorem generatedAxisGlobalTwelveFourthInverse_certificate : ∀ k : Fin 5,
    (∀ j : Fin 24, generatedAxisGlobalTwelveFourthInverseColumns k j < 2 ^ 24 ∧
      generatedAxisGlobalMaskRowsAction (generatedAxisGlobalTwelveFourthBinaryRows k)
        (generatedAxisGlobalTwelveFourthInverseColumns k j) = 2 ^ j.val) ∧
    generatedAxisGlobalTwelveFourthInverseRows k =
      List.ofFn (fun j : Fin 24 => (j.val, generatedAxisGlobalTwelveFourthInverseColumns k j)) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
