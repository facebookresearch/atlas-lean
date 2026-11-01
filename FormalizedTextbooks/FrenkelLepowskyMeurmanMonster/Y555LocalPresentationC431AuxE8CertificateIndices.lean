/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite interval metadata for the original-source E8 certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC431CoxeterChains

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

-- The literal finite metadata tables contain more than the default recursive elaboration limit.
set_option maxRecDepth 100000

/-- Literal finite data for the exact start metadata. -/
def y431AuxE8CertificateStartData : List ℕ :=
  [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
    25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 38, 39, 41, 42, 43, 47, 48, 49, 51, 52, 53,
    56, 57, 60, 64, 65, 66, 70, 71, 77, 78, 80, 84, 85, 86, 87, 92, 96, 99, 100, 102, 106,
    107, 110, 111, 112, 113, 114, 117, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130,
    131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 149, 150, 153, 154,
    155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 170, 171, 173, 174, 179,
    181, 183, 185, 187, 189, 190, 191, 192, 193, 194, 195, 196, 197, 199, 201, 203, 206, 207,
    209, 212, 213, 214, 215, 216, 217, 218, 221, 223, 225, 226, 227, 228, 229, 230, 231, 232,
    233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250,
    251, 252, 257, 258, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273,
    274, 276, 277, 279, 280, 285, 288, 292, 295, 298, 301, 302, 303, 306, 309, 310, 311, 316,
    321, 325, 329, 330, 335, 336, 342, 347, 348, 353, 354, 356, 357, 358, 359, 360, 361, 362,
    363, 364, 365, 366, 367, 368, 369, 374, 375, 377, 378, 379, 380, 381, 382, 383, 384, 385,
    386, 387, 388, 389, 390, 391, 393, 394, 396, 397, 401, 406, 411, 416, 420, 424, 425, 431,
    437, 438, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459,
    460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 474, 475, 476, 477, 478,
    479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496,
    497, 500, 501, 502, 503, 504, 505, 508, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520,
    521, 526, 527, 528, 529, 530, 531, 532, 533, 534, 536, 538, 539, 540, 541, 542, 543, 544,
    545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 563,
    564, 565, 566, 567, 568, 569, 571, 572, 573, 574, 575, 576, 577, 580, 581, 582, 583, 584,
    585, 586, 591, 592, 593, 594, 595, 596, 597, 605, 606, 607, 608, 609, 610, 611, 629, 630,
    631, 632, 633, 634, 635, 636, 655, 656, 657, 658, 659, 660, 661, 674, 675, 676, 677, 678,
    679, 680, 689, 690, 691, 692, 693, 694, 695, 702, 703, 704, 705, 706, 707, 708, 715, 716,
    717, 718, 719, 720, 721, 728, 729, 730, 731, 732, 733, 734, 739, 740, 741, 742, 743, 744,
    745, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763,
    764, 765, 766, 767, 768, 771, 772, 773, 774, 775, 776, 777, 784, 785, 786, 787, 788, 789,
    790, 802, 803, 804, 805, 806, 807, 808, 827, 828, 829, 830, 831, 832, 833, 856, 857, 858,
    859, 860, 861, 862, 895, 896, 897, 898, 899, 900, 902, 942, 943, 944, 945, 946, 947, 949,
    1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1043, 1052, 1056, 1060, 1061, 1062,
    1063, 1077, 1080, 1081, 1082, 1083, 1103, 1104, 1105, 1118, 1119, 1120, 1121, 1122, 1123,
    1124, 1125, 1126, 1127, 1128, 1145, 1146, 1163
  ]

/-- The first literal chunk of each E8 normalization certificate. -/
def y431AuxE8CertificateStart (i : Fin 574) : ℕ :=
  y431AuxE8CertificateStartData.getD i.val 0

/-- Literal finite data for the exact length metadata. -/
def y431AuxE8CertificateLengthData : List ℕ :=
  [
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 1, 4, 1, 6, 1, 2, 4, 1, 1,
    1, 5, 4, 3, 1, 2, 4, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1,
    5, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 2, 2,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 4, 3, 3, 3, 1, 1, 3, 3, 1, 1,
    5, 5, 4, 4, 1, 5, 1, 6, 5, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 5, 5, 4, 4, 1, 6, 6, 1, 6, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1,
    1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 18, 1, 1, 1, 1, 1, 1, 1, 19, 1, 1, 1,
    1, 1, 1, 13, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1,
    1, 7, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 12, 1, 1, 1, 1, 1, 1, 19,
    1, 1, 1, 1, 1, 1, 23, 1, 1, 1, 1, 1, 1, 33, 1, 1, 1, 1, 1, 2, 40, 1, 1, 1, 1, 1, 2, 82, 1,
    1, 1, 1, 1, 1, 1, 1, 4, 9, 4, 4, 1, 1, 1, 14, 3, 1, 1, 1, 20, 1, 1, 13, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 17, 1, 17, 51
  ]

/-- The positive number of chunks in each E8 normalization certificate. -/
def y431AuxE8CertificateLength (i : Fin 574) : ℕ :=
  y431AuxE8CertificateLengthData.getD i.val 0

/-- Literal finite data for the exact continues metadata. -/
def y431AuxE8ChunkContinuesData : List Bool :=
  [
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, true, false, false, false, false, true, false, false,
    true, false, false, false, true, true, true, false, false, false, true, false, false,
    false, true, true, false, false, true, true, false, true, true, true, false, false, false,
    true, true, true, false, false, true, true, true, true, true, false, false, true, false,
    true, true, true, false, false, false, false, true, true, true, true, false, true, true,
    true, false, true, true, false, false, true, false, true, true, true, false, false, true,
    true, false, false, false, false, false, true, true, false, true, true, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, true, true, true,
    true, false, false, true, true, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, true, true, false, false, true, false,
    false, true, true, true, true, false, true, false, true, false, true, false, true, false,
    true, false, false, false, false, false, false, false, false, false, true, false, true,
    false, true, false, true, true, false, false, true, false, true, true, false, false,
    false, false, false, false, false, true, true, false, true, false, true, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    true, true, true, true, false, false, true, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, true, false, false, true,
    false, false, true, true, true, true, false, true, true, false, true, true, true, false,
    true, true, false, true, true, false, true, true, false, false, false, true, true, false,
    true, true, false, false, false, true, true, true, true, false, true, true, true, true,
    false, true, true, true, false, true, true, true, false, false, true, true, true, true,
    false, false, true, true, true, true, true, false, true, true, true, true, false, false,
    true, true, true, true, false, false, true, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, true, true, true, true, false,
    false, true, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, true, false, false, true, false, false, true, true, true,
    false, true, true, true, true, false, true, true, true, true, false, true, true, true,
    true, false, true, true, true, false, true, true, true, false, false, true, true, true,
    true, true, false, true, true, true, true, true, false, false, true, true, true, true,
    true, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, true, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, true, true, false, false, false, false, false, false, true, true,
    false, true, true, false, false, false, false, false, false, false, false, false, false,
    false, true, true, true, true, false, false, false, false, false, false, false, false,
    false, true, false, true, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, true, false, false, false, false, false, false, false, true, false, false,
    false, false, false, false, false, true, true, false, false, false, false, false, false,
    false, true, true, true, true, false, false, false, false, false, false, false, true,
    true, true, true, true, true, true, false, false, false, false, false, false, false, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, false, false, false, false, false, false, false, false, true, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, false,
    false, false, false, false, false, false, true, true, true, true, true, true, true, true,
    true, true, true, true, false, false, false, false, false, false, false, true, true, true,
    true, true, true, true, true, false, false, false, false, false, false, false, true, true,
    true, true, true, true, false, false, false, false, false, false, false, true, true, true,
    true, true, true, false, false, false, false, false, false, false, true, true, true, true,
    true, true, false, false, false, false, false, false, false, true, true, true, true,
    false, false, false, false, false, false, false, true, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, true, true, false, false, false, false, false, false, false,
    true, true, true, true, true, true, false, false, false, false, false, false, false, true,
    true, true, true, true, true, true, true, true, true, true, false, false, false, false,
    false, false, false, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, false, false, false, false, false, false, false,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, false, false, false, false, false, false, false,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, false, false, false, false, false, false, true, false, true, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, false, false, false, false, false, false, true, false, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, false, false, false, false, false, false, false, false,
    false, true, true, true, false, true, true, true, true, true, true, true, true, false,
    true, true, true, false, true, true, true, false, false, false, false, true, true, true,
    true, true, true, true, true, true, true, true, true, true, false, true, true, false,
    false, false, false, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, false, false, false, true, true, true,
    true, true, true, true, true, true, true, true, true, false, false, false, false, false,
    false, false, false, false, false, false, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, false, false, true, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, false, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, true, true, true, true, true, true, true, true, true, true, true, true,
    true, true, true, false
  ]

/-- Exactly the chunks followed by another chunk of the same literal certificate. -/
def y431AuxE8ChunkContinues (i : Fin 1214) : Bool :=
  y431AuxE8ChunkContinuesData.getD i.val false

/-- Every declared certificate interval is nonempty, bounded and has at most eighty-two chunks. -/
theorem y431AuxE8Certificate_bounds (c : Fin 574) :
    0 < y431AuxE8CertificateLength c ∧ y431AuxE8CertificateLength c ≤ 82 ∧
      y431AuxE8CertificateStart c + y431AuxE8CertificateLength c ≤ 1214 := by
  revert c
  decide +kernel

/-- The global row for a bounded local position stays within the literal chunk table. -/
def y431AuxE8CertificateRow (c : Fin 574) (i : Fin (y431AuxE8CertificateLength c)) :
    Fin 1214 :=
  ⟨y431AuxE8CertificateStart c + i.val, by
    have h := y431AuxE8Certificate_bounds c
    omega⟩

set_option maxHeartbeats 4000000 in
-- This finite check visits precisely the actual nonfinal positions of each literal certificate.
/-- The continuation flags hold at every position of the exact bounded interval. -/
theorem y431AuxE8Certificate_continuations_checked (c : Fin 574) :
    (List.range (y431AuxE8CertificateLength c - 1)).all (fun i =>
      y431AuxE8ChunkContinuesData.getD (y431AuxE8CertificateStart c + i) false) = true := by
  revert c
  decide +kernel

/-- Every nonfinal bounded position continues within its own exact certificate. -/
theorem y431AuxE8Certificate_continues_small (c : Fin 574) (i : Fin 82)
    (h : i.val + 1 < y431AuxE8CertificateLength c) :
    y431AuxE8ChunkContinues (y431AuxE8CertificateRow c ⟨i.val, by omega⟩) = true := by
  have hp : i.val < y431AuxE8CertificateLength c - 1 := by omega
  have hc := y431AuxE8Certificate_continuations_checked c
  rw [List.all_eq_true] at hc
  exact hc i.val (List.mem_range.mpr hp)

/-- Continuation flags apply to all nonfinal positions of the dependent certificate interval. -/
theorem y431AuxE8Certificate_continues (c : Fin 574)
    (i : Fin (y431AuxE8CertificateLength c))
    (h : i.val + 1 < y431AuxE8CertificateLength c) :
    y431AuxE8ChunkContinues (y431AuxE8CertificateRow c i) = true := by
  have hi : i.val < 82 := lt_of_lt_of_le i.isLt (y431AuxE8Certificate_bounds c).2.1
  exact y431AuxE8Certificate_continues_small c ⟨i.val, hi⟩ h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
