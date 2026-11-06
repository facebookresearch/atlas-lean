/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightQSourceWords

/-! Complete original full-Q prefixes with bounded exact lookup. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Original chronological letters, looked up in literal blocks of at most sixteen entries. -/
def generatedRootEightQReplayLetterLookup00 (n : ℕ) : Fin 11 :=
  [1, 0, 0, 1, 2, 2, 1].getD (n - 0) 0

/-- Complete original prefix images, looked up in literal blocks of at most sixteen rows. -/
def generatedRootEightQReplayLookup00 (n : ℕ) : Fin 24 → ℕ :=
  [
    ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072,
      262144, 524288, 1048576, 2097152, 4194304, 8388608],
    ![377516, 1033212, 46084, 29704, 2109456, 2105408, 1060896, 1056896, 786483, 196813, 1024,
      2048, 3145728, 1048576, 2125824, 2142208, 1122304, 1323008, 2236416, 2633728, 8192, 12288,
      4243456, 8388608],
    ![24553578, 7956630, 663282, 335346, 7594800, 8188864, 5929505, 6650191, 2950626, 1771122,
      51198, 2048, 3174400, 3190784, 5951488, 6672384, 3309568, 3444736, 4255744, 4251648, 4403200,
      4988928, 7344128, 12570624],
    ![2644195, 17909885, 20997994, 401250, 1622297, 2212487, 17569240, 6546495, 3851346, 2635301,
      22002790, 2048, 6971392, 5595136, 4239360, 7782400, 1720320, 6180864, 3944448, 3350528,
      4272128, 4726784, 7368704, 12169216],
    ![1198512, 2382544, 4199274, 3592034, 16864903, 541977, 1458315, 23065868, 202700, 19812901,
      7347096, 2048, 5013504, 4427776, 4222976, 7733248, 1855488, 5156864, 2752512, 1376256,
      7462912, 7925760, 4235264, 12169216],
    ![7667153, 7466367, 1051296, 2477554, 4814738, 21411682, 4701128, 6827094, 525586, 262688,
      3199998, 2048, 1105920, 1110016, 8048640, 4575232, 3641344, 1163264, 4239360, 4222976,
      6545408, 7139328, 5292032, 12570624],
    ![7238702, 6911182, 20976102, 7197704, 8377762, 22402546, 24040256, 5343202, 4632675, 4502831,
      2097234, 2048, 2445312, 3096576, 6799360, 6750208, 1454080, 2908160, 5951488, 8048640,
      7176192, 7180288, 2973696, 8388608],
    ![7440304, 24545104, 22251307, 7041032, 5035791, 21030719, 7413982, 5343202, 21786928,
      21280047, 4191180, 2048, 2310144, 3096576, 6750208, 6799360, 1454080, 3821568, 4988928,
      4984832, 8089600, 4943872, 2846720, 8388608]
  ].getD (n - 0) (fun _ => 0)

/-- Each actual basis image after every original primitive, retaining its central bit. -/
def generatedRootEightQReplayData00 (n : Fin 8) : Fin 24 → ℕ :=
  generatedRootEightQReplayLookup00 n.val

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
