/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthPauliBasisData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthQCoordinateEvaluation

/-! Candidate full-phase images of the finite input-reconstruction Q witnesses.
The separate certificate must bind every image to the proved original automorphism. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Translation, modulation and central coefficient candidates of all128 input witnesses. -/
def generatedNinthPauliImageLabels : Fin 128 → Fin 4096 × Fin 4096 × ZMod 2 :=
  ![(0, 0, 0), (273, 3352, 1), (655, 3721, 1), (926, 913, 1), (3880, 1166, 0), (3641, 2454,
    1), (3495, 2567, 1), (3912, 1055, 0), (765, 74, 0), (1004, 3410, 1), (114, 3779, 1), (355,
    987, 1), (3541, 1220, 1), (3268, 2524, 0), (3930, 2637, 0), (3509, 1109, 0), (1388, 1765,
    0), (1149, 3069, 0), (2019, 2156, 1), (1778, 1396, 0), (227, 1540, 0), (498, 2844, 1),
    (620, 2189, 1), (893, 1429, 1), (542, 1614, 0), (783, 2902, 1), (145, 2247, 1), (384,
    1503, 1), (2865, 1038, 1), (2592, 2326, 1), (2494, 2695, 1), (2223, 1951, 0), (1049, 128,
    1), (1686, 3593, 1), (2508, 1092, 1), (2883, 2765, 1), (3023, 1039, 1), (2782, 2327, 1),
    (2368, 2694, 1), (2129, 1950, 0), (1255, 129, 1), (1526, 3481, 1), (1640, 3592, 1), (1159,
    16, 1), (2354, 1093, 0), (2083, 2397, 0), (3005, 2764, 0), (2732, 2004, 1), (1562, 203,
    1), (1803, 3539, 1), (1173, 3650, 1), (1658, 90, 0), (3747, 746, 0), (4018, 4082, 1),
    (3116, 3171, 0), (3389, 379, 0), (2860, 523, 1), (2621, 3859, 1), (2467, 3202, 1), (2226,
    410, 0), (2513, 577, 0), (2240, 3929, 0), (2910, 3272, 0), (2639, 464, 1), (254, 1, 1),
    (495, 3353, 0), (625, 3720, 0), (864, 912, 0), (4054, 1167, 1), (3417, 2566, 0), (515, 75,
    0), (140, 3778, 1), (2543, 1375, 1), (2302, 2119, 1), (2912, 3030, 0), (2673, 1742, 1),
    (1735, 465, 1), (1096, 3928, 0), (2834, 1301, 0), (2563, 2061, 0), (2461, 2972, 1), (2188,
    1668, 0), (1082, 411, 1), (1717, 3858, 0), (3203, 954, 0), (3474, 3746, 1), (3596, 3379,
    1), (3869, 43, 1), (2316, 859, 0), (2077, 3651, 0), (3057, 785, 1), (2784, 3593, 1), (734,
    337, 1), (975, 3145, 0), (81, 4056, 1), (320, 704, 1), (3574, 1503, 1), (3961, 2902, 1),
    (35, 283, 0), (684, 3986, 0), (544, 336, 0), (817, 3144, 1), (175, 4057, 0), (446, 705,
    0), (3336, 1502, 0), (3975, 2903, 0), (221, 282, 0), (460, 3074, 1), (594, 3987, 0), (835,
    651, 0), (4085, 1428, 1), (3450, 2845, 1), (1868, 1973, 0), (1629, 2733, 0), (1475, 2364,
    0), (1234, 1060, 1), (707, 1876, 1), (978, 2636, 0), (62, 1822, 1), (303, 2566, 0), (2321,
    1374, 1), (2048, 2118, 1), (2974, 3031, 0), (2703, 1743, 1), (1593, 464, 1), (1206, 3929,
    0), (3052, 1300, 1), (2403, 2973, 0)]

/-- Full candidate Q images retain the displayed central coefficients. -/
def generatedNinthPauliImage (q : Fin 128) : Q :=
  ⟨ofAdd (Fin.append (golayLabelCoefficients (generatedNinthPauliImageLabels q).1)
    (golayLabelCoefficients (generatedNinthPauliImageLabels q).2.1)),
    ofAdd (generatedNinthPauliImageLabels q).2.2⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
