/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal bounded contextual equation certificates of the independent C322 derivation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawContextPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact literal claimed equations and contextual derivations, block 064. -/
def y322TCContextRaw064 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77703, 1], [77701], .contexts [
        ⟨4095, false, false, [], []⟩,
        ⟨3908, false, false, [], []⟩,
        ⟨3884, false, false, [], []⟩,
        ⟨3884, false, false, [], []⟩
      ]⟩,
    ⟨[77703, 0], [77703, 1], .contexts [
        ⟨19, false, false, [77703], []⟩
      ]⟩,
    ⟨[77701, 15], [77701, 15], .contexts []⟩,
    ⟨[841, 77705], [841, 77705], .contexts []⟩,
    ⟨[77703, 5], [77703, 5], .contexts []⟩,
    ⟨[831, 77701], [831, 77701], .contexts []⟩,
    ⟨[77701, 15], [831, 77701], .contexts [
        ⟨4098, false, false, [], []⟩,
        ⟨4098, false, false, [], []⟩,
        ⟨3885, true, false, [], [15]⟩,
        ⟨4094, true, false, [848], [1, 15]⟩,
        ⟨4094, true, false, [848], [1, 15]⟩,
        ⟨4090, true, false, [848], [1, 15]⟩,
        ⟨4088, true, false, [848], [1, 15]⟩,
        ⟨2778, false, false, [848, 77703], []⟩,
        ⟨4097, false, false, [848], []⟩,
        ⟨4096, false, false, [848], []⟩,
        ⟨4079, true, false, [], [77701]⟩,
        ⟨4101, false, false, [], []⟩,
        ⟨4101, false, false, [], []⟩
      ]⟩,
    ⟨[77699, 15], [77699, 15], .contexts []⟩,
    ⟨[77699], [77699], .contexts []⟩,
    ⟨[843, 77703], [843, 77703], .contexts []⟩,
    ⟨[77703, 5], [843, 77703], .contexts [
        ⟨4100, false, false, [], []⟩,
        ⟨4100, false, false, [], []⟩,
        ⟨3889, true, false, [], [5]⟩,
        ⟨4099, true, false, [840], [9, 5]⟩,
        ⟨4099, true, false, [840], [9, 5]⟩,
        ⟨4093, true, false, [840], [9, 5]⟩,
        ⟨4092, true, false, [840], [9, 5]⟩,
        ⟨1672, false, false, [840, 77705], []⟩,
        ⟨4087, false, false, [840], []⟩,
        ⟨4086, false, false, [840], []⟩,
        ⟨4089, false, false, [840], []⟩,
        ⟨4048, true, false, [], [77703]⟩,
        ⟨4105, false, false, [], []⟩,
        ⟨4105, false, false, [], []⟩
      ]⟩,
    ⟨[843, 77699], [843, 77699], .contexts []⟩,
    ⟨[843, 77699], [843, 77699], .contexts []⟩,
    ⟨[77699, 1], [841, 77703], .contexts [
        ⟨4108, true, false, [842], [1]⟩,
        ⟨4107, true, false, [842], [1]⟩,
        ⟨3882, true, false, [], [1]⟩,
        ⟨3885, true, false, [], [5, 1]⟩,
        ⟨4106, true, false, [842], [1, 5, 1]⟩,
        ⟨1485, false, false, [842, 77703], []⟩,
        ⟨4089, false, false, [842], []⟩,
        ⟨4070, true, false, [], [77703]⟩
      ]⟩,
    ⟨[77701], [843, 77699], .contexts [
        ⟨4096, true, false, [], []⟩,
        ⟨4109, true, false, [840], [1]⟩,
        ⟨18, false, false, [840, 77699], []⟩,
        ⟨4045, true, false, [], [77699]⟩,
        ⟨4107, false, false, [], []⟩,
        ⟨4046, true, false, [], [77699]⟩,
        ⟨4108, false, false, [], []⟩
      ]⟩,
    ⟨[849, 77699], [849, 77699], .contexts []⟩,
    ⟨[77699, 15, 3], [849, 77697], .contexts [
        ⟨4103, false, false, [], [3]⟩,
        ⟨4103, false, false, [], [3]⟩,
        ⟨3882, true, false, [], [15, 3]⟩,
        ⟨4102, true, false, [830], [5, 15, 3]⟩,
        ⟨3532, false, false, [830, 77701], [3]⟩,
        ⟨50, false, false, [830, 77701], [3]⟩,
        ⟨3909, false, false, [830], [3]⟩,
        ⟨3910, false, false, [830], [3]⟩,
        ⟨3881, false, false, [830], [3]⟩,
        ⟨3881, false, false, [830], [3]⟩,
        ⟨4104, false, false, [830], [3]⟩,
        ⟨4062, true, false, [], [77699, 3]⟩,
        ⟨4111, false, false, [], [3]⟩,
        ⟨4111, false, false, [], [3]⟩,
        ⟨3878, false, false, [849], []⟩
      ]⟩,
    ⟨[77699, 3], [77697], .contexts [
        ⟨3911, false, false, [], []⟩
      ]⟩,
    ⟨[77699, 3], [77697], .contexts [
        ⟨4113, false, false, [], []⟩,
        ⟨3912, false, false, [], []⟩,
        ⟨3877, false, false, [], []⟩,
        ⟨3877, false, false, [], []⟩
      ]⟩,
    ⟨[77699, 2], [77699, 3], .contexts [
        ⟨36, false, false, [77699], []⟩
      ]⟩,
    ⟨[77697, 15], [77697, 15], .contexts []⟩,
    ⟨[77697], [77697], .contexts []⟩,
    ⟨[831, 77697], [831, 77697], .contexts []⟩,
    ⟨[831, 77693], [831, 77693], .contexts []⟩,
    ⟨[831, 77693], [831, 77693], .contexts []⟩,
    ⟨[77697, 15, 1, 15], [831, 77693], .contexts [
        ⟨4116, false, false, [], [1, 15]⟩,
        ⟨4116, false, false, [], [1, 15]⟩,
        ⟨4112, true, false, [848], [15, 1, 15]⟩,
        ⟨1893, false, false, [848, 77699], [1, 15]⟩,
        ⟨4115, false, false, [848], [1, 15]⟩,
        ⟨4114, false, false, [848], [1, 15]⟩,
        ⟨4117, false, false, [848], [1, 15]⟩,
        ⟨4079, true, false, [], [77697, 1, 15]⟩,
        ⟨4118, false, false, [], [1, 15]⟩,
        ⟨4118, false, false, [], [1, 15]⟩,
        ⟨3875, false, false, [831], [15]⟩,
        ⟨3872, false, false, [831], []⟩,
        ⟨4119, false, false, [], []⟩,
        ⟨4120, false, false, [], []⟩
      ]⟩,
    ⟨[77693, 1], [77693, 1], .contexts []⟩,
    ⟨[77693, 1], [849, 77697], .contexts [
        ⟨4122, false, false, [], []⟩,
        ⟨4121, true, false, [830], [1]⟩,
        ⟨911, false, false, [830, 77697], []⟩,
        ⟨4117, false, false, [830], []⟩,
        ⟨4062, true, false, [], [77697]⟩
      ]⟩,
    ⟨[77713], [77485, 7], .source 38921⟩,
    ⟨[77485, 7], [77713], .contexts [
        ⟨4124, true, false, [], []⟩
      ]⟩,
    ⟨[77485, 7], [77713], .contexts [
        ⟨4125, false, false, [], []⟩
      ]⟩,
    ⟨[77713], [77713], .contexts []⟩,
    ⟨[77713], [77713], .contexts []⟩,
    ⟨[77485, 7], [77713], .contexts [
        ⟨4126, false, false, [], []⟩,
        ⟨4127, false, false, [], []⟩,
        ⟨4128, false, false, [], []⟩,
        ⟨4128, false, false, [], []⟩
      ]⟩,
    ⟨[77713], [77713], .contexts []⟩,
    ⟨[77713, 1], [257, 77713], .contexts [
        ⟨4129, true, false, [], [1]⟩,
        ⟨1764, false, false, [77485], []⟩,
        ⟨1765, false, false, [77485], []⟩,
        ⟨2682, false, false, [], [7]⟩,
        ⟨2685, false, false, [], [7]⟩,
        ⟨2680, false, false, [], [7]⟩,
        ⟨2681, false, false, [], [7]⟩,
        ⟨2681, false, false, [], [7]⟩,
        ⟨4125, false, false, [257], []⟩,
        ⟨4130, false, false, [257], []⟩,
        ⟨2684, true, false, [], [77713]⟩
      ]⟩,
    ⟨[77715], [77605, 9], .source 38922⟩,
    ⟨[77605, 9], [77715], .contexts [
        ⟨4132, true, false, [], []⟩
      ]⟩,
    ⟨[77605, 9], [77715], .contexts [
        ⟨4133, false, false, [], []⟩
      ]⟩,
    ⟨[77715], [77715], .contexts []⟩,
    ⟨[77715], [77715], .contexts []⟩,
    ⟨[77605, 9], [77715], .contexts [
        ⟨4134, false, false, [], []⟩,
        ⟨4135, false, false, [], []⟩,
        ⟨4136, false, false, [], []⟩,
        ⟨4136, false, false, [], []⟩
      ]⟩,
    ⟨[77605, 1], [77483], .contexts [
        ⟨3581, false, false, [], []⟩,
        ⟨3582, false, false, [], []⟩,
        ⟨2664, false, false, [], []⟩,
        ⟨2665, false, false, [], []⟩,
        ⟨2665, false, false, [], []⟩
      ]⟩,
    ⟨[77715], [77715], .contexts []⟩,
    ⟨[77715, 1], [11, 77715], .contexts [
        ⟨4137, true, false, [], [1]⟩,
        ⟨1143, false, false, [77605], []⟩,
        ⟨1146, false, false, [77605], []⟩,
        ⟨4138, false, false, [], [9, 1, 9]⟩,
        ⟨2671, false, false, [], [1, 9]⟩,
        ⟨2669, false, false, [], [1, 9]⟩,
        ⟨2670, false, false, [], [1, 9]⟩,
        ⟨2670, false, false, [], [1, 9]⟩,
        ⟨3583, false, false, [11], [9]⟩,
        ⟨4133, false, false, [11], []⟩,
        ⟨4139, false, false, [11], []⟩,
        ⟨94, true, false, [], [77715]⟩
      ]⟩,
    ⟨[77605, 5], [759, 77605], .contexts [
        ⟨3590, false, false, [], []⟩,
        ⟨3593, false, false, [], []⟩,
        ⟨3588, false, false, [], []⟩,
        ⟨3589, false, false, [], []⟩,
        ⟨3589, false, false, [], []⟩
      ]⟩,
    ⟨[77605, 7], [77113], .contexts [
        ⟨3576, true, false, [], [7]⟩,
        ⟨62, false, false, [77113], []⟩,
        ⟨367, false, false, [], []⟩,
        ⟨366, false, false, [], []⟩,
        ⟨367, false, false, [], []⟩,
        ⟨367, false, false, [], []⟩
      ]⟩,
    ⟨[77605, 11], [211, 77479], .contexts [
        ⟨3600, false, false, [], []⟩
      ]⟩,
    ⟨[851], [211, 217], .source 490⟩,
    ⟨[853], [851, 209], .source 491⟩,
    ⟨[77605, 11, 9, 11, 9], [853, 77715], .contexts [
        ⟨3596, false, false, [], [9, 11, 9]⟩,
        ⟨4143, false, false, [], [9, 11, 9]⟩,
        ⟨3594, false, false, [], [9, 11, 9]⟩,
        ⟨3595, false, false, [], [9, 11, 9]⟩,
        ⟨3595, false, false, [], [9, 11, 9]⟩,
        ⟨2568, true, false, [211], [9, 11, 9]⟩,
        ⟨2574, false, false, [211, 77355], [11, 9]⟩,
        ⟨2575, false, false, [211, 77355], [11, 9]⟩,
        ⟨1528, false, false, [211], [7, 11, 9]⟩,
        ⟨2566, false, false, [211, 217], [11, 9]⟩,
        ⟨2573, false, false, [211, 217], [11, 9]⟩,
        ⟨2576, true, false, [211], [77479, 11, 9]⟩,
        ⟨4144, true, false, [], [77479, 11, 9]⟩,
        ⟨3601, false, false, [851], [9]⟩,
        ⟨4145, true, false, [], [77605, 9]⟩,
        ⟨4133, false, false, [853], []⟩
      ]⟩,
    ⟨[9, 11], [10, 8, 10, 8], .contexts [
        ⟨965, false, false, [], [10, 8, 10, 8]⟩
      ]⟩,
    ⟨[10, 8, 10], [11, 9, 11], .contexts [
        ⟨967, false, false, [], [10]⟩,
        ⟨91, false, false, [11, 9], []⟩
      ]⟩,
    ⟨[10, 8, 10, 8], [11, 9, 11, 9], .contexts [
        ⟨4148, false, false, [], [8]⟩,
        ⟨77, false, false, [11, 9, 11], []⟩
      ]⟩,
    ⟨[77717], [77605, 13], .source 38923⟩,
    ⟨[77605, 13], [77717], .contexts [
        ⟨4150, true, false, [], []⟩
      ]⟩,
    ⟨[77717], [77717], .contexts []⟩,
    ⟨[77717], [77717], .contexts []⟩,
    ⟨[77605, 13], [77717], .contexts [
        ⟨4151, false, false, [], []⟩,
        ⟨4152, false, false, [], []⟩,
        ⟨4153, false, false, [], []⟩,
        ⟨4153, false, false, [], []⟩
      ]⟩,
    ⟨[77605, 1, 13, 1], [1, 77605], .contexts [
        ⟨4138, false, false, [], [13, 1]⟩,
        ⟨2666, true, false, [], [13, 1]⟩,
        ⟨352, false, false, [77359], [1]⟩,
        ⟨353, false, false, [77359], [1]⟩,
        ⟨1815, false, false, [], [11, 1]⟩,
        ⟨1817, false, false, [], [11, 1]⟩,
        ⟨1813, false, false, [], [11, 1]⟩,
        ⟨1814, false, false, [], [11, 1]⟩,
        ⟨1814, false, false, [], [11, 1]⟩,
        ⟨2663, false, false, [1], [1]⟩,
        ⟨2672, false, false, [], [1]⟩,
        ⟨2673, false, false, [], [1]⟩,
        ⟨2667, false, false, [1], [1]⟩,
        ⟨25, true, false, [], [77483, 1]⟩,
        ⟨2672, false, false, [], [1]⟩,
        ⟨2673, false, false, [], [1]⟩,
        ⟨2673, false, false, [], [1]⟩,
        ⟨3583, false, false, [1], []⟩
      ]⟩,
    ⟨[1, 77717], [1, 77717], .contexts []⟩,
    ⟨[1, 77717], [1, 77717], .contexts []⟩,
    ⟨[77717, 1], [77717, 1], .contexts []⟩,
    ⟨[77717], [77717], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 065. -/
def y322TCContextRaw065 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77717, 1], [1, 77717], .contexts [
        ⟨4158, false, false, [], []⟩,
        ⟨4154, true, false, [], [1]⟩,
        ⟨387, false, false, [77605], []⟩,
        ⟨390, false, false, [77605], []⟩,
        ⟨4155, false, false, [], [13]⟩,
        ⟨4151, false, false, [1], []⟩,
        ⟨4156, false, false, [], []⟩,
        ⟨4157, false, false, [], []⟩,
        ⟨4159, false, false, [1], []⟩,
        ⟨25, true, false, [], [77717]⟩
      ]⟩,
    ⟨[759, 77717], [759, 77717], .contexts []⟩,
    ⟨[759, 77717], [759, 77717], .contexts []⟩,
    ⟨[77717, 5], [77717, 5], .contexts []⟩,
    ⟨[77717, 7], [77717, 7], .contexts []⟩,
    ⟨[77719], [77213, 15], .source 38924⟩,
    ⟨[77213, 15], [77719], .contexts [
        ⟨4165, true, false, [], []⟩
      ]⟩,
    ⟨[77719, 15], [77213], .contexts [
        ⟨4166, true, false, [], [15]⟩,
        ⟨3, false, false, [77213], []⟩,
        ⟨592, false, false, [], []⟩
      ]⟩,
    ⟨[77719], [77719], .contexts []⟩,
    ⟨[77719], [77719], .contexts []⟩,
    ⟨[77213, 15], [77719], .contexts [
        ⟨4166, false, false, [], []⟩,
        ⟨4168, false, false, [], []⟩,
        ⟨4169, false, false, [], []⟩,
        ⟨4169, false, false, [], []⟩
      ]⟩,
    ⟨[145, 77213], [145, 77213], .contexts []⟩,
    ⟨[145, 77719], [145, 77719], .contexts []⟩,
    ⟨[145, 77719], [145, 77719], .contexts []⟩,
    ⟨[77719], [77719], .contexts []⟩,
    ⟨[145], [145], .contexts [
        ⟨24, false, false, [], [145]⟩
      ]⟩,
    ⟨[293, 77243], [293, 77243], .contexts []⟩,
    ⟨[293, 77243], [293, 77243], .contexts []⟩,
    ⟨[77719, 5], [77719, 5], .contexts []⟩,
    ⟨[293], [293], .contexts [
        ⟨24, false, false, [], [293]⟩
      ]⟩,
    ⟨[149, 77719], [149, 77719], .contexts []⟩,
    ⟨[149, 77719], [149, 77719], .contexts []⟩,
    ⟨[77213, 7, 15], [149, 77719], .contexts [
        ⟨1019, false, false, [], [15]⟩,
        ⟨1019, false, false, [], [15]⟩,
        ⟨593, true, false, [], [7, 15]⟩,
        ⟨1016, true, false, [154], [9, 7, 15]⟩,
        ⟨1018, false, false, [154, 77215], [15]⟩,
        ⟨1011, false, false, [154], [15]⟩,
        ⟨1008, false, false, [154], [15]⟩,
        ⟨969, false, false, [154], [15]⟩,
        ⟨1020, true, false, [], [77213, 15]⟩,
        ⟨1020, true, false, [], [77213, 15]⟩,
        ⟨987, false, true, [], [77213, 15]⟩,
        ⟨1032, false, false, [], [15]⟩,
        ⟨1032, false, false, [], [15]⟩,
        ⟨4166, false, false, [149], []⟩,
        ⟨4180, false, false, [], []⟩,
        ⟨4181, false, false, [], []⟩
      ]⟩,
    ⟨[77719, 7], [77719, 7], .contexts []⟩,
    ⟨[149], [149], .contexts [
        ⟨24, false, false, [], [149]⟩
      ]⟩,
    ⟨[77719, 9], [77719, 9], .contexts []⟩,
    ⟨[77719, 9], [77363], .contexts [
        ⟨4185, false, false, [], []⟩,
        ⟨4170, true, false, [], [9]⟩,
        ⟨75, false, false, [77213], []⟩,
        ⟨78, false, false, [77213], []⟩,
        ⟨591, false, false, [], [15]⟩,
        ⟨635, false, false, [], [15]⟩,
        ⟨596, false, false, [], [15]⟩,
        ⟨596, false, false, [], [15]⟩,
        ⟨1914, false, false, [], []⟩,
        ⟨1915, false, false, [], []⟩,
        ⟨1916, false, false, [], []⟩,
        ⟨1916, false, false, [], []⟩,
        ⟨1920, false, false, [], []⟩,
        ⟨1118, true, false, [], [77363]⟩
      ]⟩,
    ⟨[77363, 9], [77719], .contexts [
        ⟨4186, true, false, [], [9]⟩,
        ⟨76, false, false, [77719], []⟩,
        ⟨4169, false, false, [], []⟩
      ]⟩,
    ⟨[151, 77719], [151, 77719], .contexts []⟩,
    ⟨[151, 77719], [151, 77719], .contexts []⟩,
    ⟨[77719, 11], [77719, 11], .contexts []⟩,
    ⟨[151], [151], .contexts [
        ⟨24, false, false, [], [151]⟩,
        ⟨1070, false, false, [], []⟩,
        ⟨1071, false, false, [], []⟩
      ]⟩,
    ⟨[77719, 11], [151, 77719], .contexts [
        ⟨4190, false, false, [], []⟩,
        ⟨4170, true, false, [], [11]⟩,
        ⟨89, false, false, [77213], []⟩,
        ⟨92, false, false, [77213], []⟩,
        ⟨998, false, false, [], [15]⟩,
        ⟨4166, false, false, [151], []⟩,
        ⟨4188, false, false, [], []⟩,
        ⟨4189, false, false, [], []⟩,
        ⟨4174, false, false, [151], []⟩,
        ⟨4191, true, false, [], [77719]⟩
      ]⟩,
    ⟨[419, 77475], [419, 77475], .contexts []⟩,
    ⟨[855], [419, 423], .source 492⟩,
    ⟨[857], [855, 417], .source 493⟩,
    ⟨[857, 77719], [857, 77719], .contexts []⟩,
    ⟨[857, 77719], [857, 77719], .contexts []⟩,
    ⟨[77719, 13], [857, 77719], .contexts [
        ⟨4170, true, false, [], [13]⟩,
        ⟨408, false, false, [77213], []⟩,
        ⟨410, false, false, [77213], []⟩,
        ⟨2441, false, false, [], [15, 13, 15]⟩,
        ⟨2444, false, false, [], [15, 13, 15]⟩,
        ⟨4193, false, false, [], [15, 13, 15]⟩,
        ⟨4193, false, false, [], [15, 13, 15]⟩,
        ⟨2449, false, false, [419], [13, 15]⟩,
        ⟨4194, true, false, [], [77475, 13, 15]⟩,
        ⟨2445, false, false, [855], [15]⟩,
        ⟨4195, true, false, [], [77213, 15]⟩,
        ⟨4166, false, false, [857], []⟩,
        ⟨4196, false, false, [], []⟩,
        ⟨4197, false, false, [], []⟩,
        ⟨4174, false, false, [857], []⟩
      ]⟩,
    ⟨[857], [857], .contexts [
        ⟨24, false, false, [], [857]⟩
      ]⟩,
    ⟨[77721], [77719, 1], .source 38925⟩,
    ⟨[77719, 1], [77721], .contexts [
        ⟨4200, true, false, [], []⟩
      ]⟩,
    ⟨[77721, 1], [77719], .contexts [
        ⟨4201, true, false, [], [1]⟩,
        ⟨18, false, false, [77719], []⟩,
        ⟨4169, false, false, [], []⟩
      ]⟩,
    ⟨[77721], [77721], .contexts []⟩,
    ⟨[77721], [77721], .contexts []⟩,
    ⟨[77719, 1], [77721], .contexts [
        ⟨4201, false, false, [], []⟩,
        ⟨4203, false, false, [], []⟩,
        ⟨4204, false, false, [], []⟩,
        ⟨4204, false, false, [], []⟩
      ]⟩,
    ⟨[77721, 5], [77721, 5], .contexts []⟩,
    ⟨[77721, 5], [293, 77245], .contexts [
        ⟨4206, false, false, [], []⟩,
        ⟨4205, true, false, [], [5]⟩,
        ⟨165, false, false, [77719], []⟩,
        ⟨166, false, false, [77719], []⟩,
        ⟨4178, false, false, [], [1]⟩,
        ⟨4178, false, false, [], [1]⟩,
        ⟨4170, true, false, [], [5, 1]⟩,
        ⟨48, false, false, [77213], [1]⟩,
        ⟨51, false, false, [77213], [1]⟩,
        ⟨1859, false, false, [], [15, 1]⟩,
        ⟨1171, false, false, [293], [1]⟩,
        ⟨4176, false, false, [], [1]⟩,
        ⟨4177, false, false, [], [1]⟩,
        ⟨1181, false, false, [293], [1]⟩,
        ⟨4179, true, false, [], [77243, 1]⟩,
        ⟨4176, false, false, [], [1]⟩,
        ⟨4177, false, false, [], [1]⟩,
        ⟨4177, false, false, [], [1]⟩,
        ⟨1183, false, false, [293], []⟩,
        ⟨1887, false, false, [], []⟩,
        ⟨1888, false, false, [], []⟩
      ]⟩,
    ⟨[77721, 5], [293, 77245], .contexts [
        ⟨4207, false, false, [], []⟩,
        ⟨1663, false, false, [293], []⟩,
        ⟨4179, true, false, [], [77245]⟩
      ]⟩,
    ⟨[149, 77721], [149, 77721], .contexts []⟩,
    ⟨[149, 77721], [149, 77721], .contexts []⟩,
    ⟨[77721, 7], [77721, 7], .contexts []⟩,
    ⟨[77721], [77721], .contexts []⟩,
    ⟨[77721, 7], [149, 77721], .contexts [
        ⟨4211, false, false, [], []⟩,
        ⟨4205, true, false, [], [7]⟩,
        ⟨173, false, false, [77719], []⟩,
        ⟨174, false, false, [77719], []⟩,
        ⟨4183, false, false, [], [1]⟩,
        ⟨4183, false, false, [], [1]⟩,
        ⟨4170, true, false, [], [7, 1]⟩,
        ⟨61, false, false, [77213], [1]⟩,
        ⟨64, false, false, [77213], [1]⟩,
        ⟨4182, false, false, [], [1]⟩,
        ⟨4174, false, false, [149], [1]⟩,
        ⟨4184, true, false, [], [77719, 1]⟩,
        ⟨4180, false, false, [], [1]⟩,
        ⟨4181, false, false, [], [1]⟩,
        ⟨4181, false, false, [], [1]⟩,
        ⟨4201, false, false, [149], []⟩,
        ⟨4209, false, false, [], []⟩,
        ⟨4210, false, false, [], []⟩,
        ⟨4212, false, false, [149], []⟩
      ]⟩,
    ⟨[135, 77721], [135, 77721], .contexts []⟩,
    ⟨[135, 77721], [135, 77721], .contexts []⟩,
    ⟨[77721, 9], [77721, 9], .contexts []⟩,
    ⟨[77721, 9], [135, 77721], .contexts [
        ⟨4216, false, false, [], []⟩,
        ⟨4205, true, false, [], [9]⟩,
        ⟨786, false, false, [77719], []⟩,
        ⟨788, false, false, [77719], []⟩,
        ⟨4185, false, false, [], [1, 9, 1]⟩,
        ⟨4186, false, false, [], [1, 9, 1]⟩,
        ⟨1915, false, false, [], [1, 9, 1]⟩,
        ⟨1916, false, false, [], [1, 9, 1]⟩,
        ⟨1916, false, false, [], [1, 9, 1]⟩,
        ⟨1921, false, false, [], [9, 1]⟩,
        ⟨1918, false, false, [], [9, 1]⟩,
        ⟨1919, false, false, [], [9, 1]⟩,
        ⟨1919, false, false, [], [9, 1]⟩,
        ⟨4187, false, false, [135], [1]⟩,
        ⟨4201, false, false, [135], []⟩,
        ⟨4214, false, false, [], []⟩,
        ⟨4215, false, false, [], []⟩,
        ⟨4212, false, false, [135], []⟩
      ]⟩,
    ⟨[151, 77721], [151, 77721], .contexts []⟩,
    ⟨[151, 77721], [151, 77721], .contexts []⟩,
    ⟨[77721, 11], [77721, 11], .contexts []⟩,
    ⟨[77721, 15], [77721, 15], .contexts []⟩,
    ⟨[77721, 15], [77211], .contexts [
        ⟨4221, false, false, [], []⟩,
        ⟨4205, true, false, [], [15]⟩,
        ⟨199, false, false, [77719], []⟩,
        ⟨200, false, false, [77719], []⟩,
        ⟨4167, false, false, [], [1]⟩,
        ⟨637, false, false, [], [1]⟩,
        ⟨592, false, false, [], [1]⟩,
        ⟨592, false, false, [], [1]⟩,
        ⟨638, false, false, [], []⟩,
        ⟨639, false, false, [], []⟩,
        ⟨588, false, false, [], []⟩,
        ⟨588, false, false, [], []⟩,
        ⟨1002, false, false, [], []⟩,
        ⟨1118, true, false, [], [77211]⟩
      ]⟩,
    ⟨[77723], [77721, 3], .source 38926⟩]

/-- Exact literal claimed equations and contextual derivations, block 066. -/
def y322TCContextRaw066 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77721, 3], [77723], .contexts [
        ⟨4223, true, false, [], []⟩
      ]⟩,
    ⟨[77723, 3], [77721], .contexts [
        ⟨4224, true, false, [], [3]⟩,
        ⟨35, false, false, [77721], []⟩,
        ⟨4204, false, false, [], []⟩
      ]⟩,
    ⟨[77721, 3], [77723], .contexts [
        ⟨4224, false, false, [], []⟩
      ]⟩,
    ⟨[77723], [77723], .contexts []⟩,
    ⟨[77723], [77723], .contexts []⟩,
    ⟨[77721, 3], [77723], .contexts [
        ⟨4226, false, false, [], []⟩,
        ⟨4227, false, false, [], []⟩,
        ⟨4228, false, false, [], []⟩,
        ⟨4228, false, false, [], []⟩
      ]⟩,
    ⟨[77721, 1], [77719], .contexts [
        ⟨4202, false, false, [], []⟩,
        ⟨4168, false, false, [], []⟩,
        ⟨4169, false, false, [], []⟩,
        ⟨4169, false, false, [], []⟩
      ]⟩,
    ⟨[77721, 1, 3, 1], [145, 77721], .contexts [
        ⟨4230, false, false, [], [3, 1]⟩,
        ⟨4170, true, false, [], [3, 1]⟩,
        ⟨34, false, false, [77213], [1]⟩,
        ⟨37, false, false, [77213], [1]⟩,
        ⟨1012, false, false, [], [15, 1]⟩,
        ⟨1014, false, false, [], [15, 1]⟩,
        ⟨4171, false, false, [], [15, 1]⟩,
        ⟨4171, false, false, [], [15, 1]⟩,
        ⟨4166, false, false, [145], [1]⟩,
        ⟨4172, false, false, [], [1]⟩,
        ⟨4173, false, false, [], [1]⟩,
        ⟨4174, false, false, [145], [1]⟩,
        ⟨4175, true, false, [], [77719, 1]⟩,
        ⟨4172, false, false, [], [1]⟩,
        ⟨4173, false, false, [], [1]⟩,
        ⟨4173, false, false, [], [1]⟩,
        ⟨4201, false, false, [145], []⟩
      ]⟩,
    ⟨[145, 77723], [145, 77723], .contexts []⟩,
    ⟨[145, 77723], [145, 77723], .contexts []⟩,
    ⟨[77723, 1], [77723, 1], .contexts []⟩,
    ⟨[77723], [77723], .contexts []⟩,
    ⟨[77723, 1], [145, 77723], .contexts [
        ⟨4234, false, false, [], []⟩,
        ⟨4229, true, false, [], [1]⟩,
        ⟨213, false, false, [77721], []⟩,
        ⟨216, false, false, [77721], []⟩,
        ⟨4231, false, false, [], [3]⟩,
        ⟨4224, false, false, [145], []⟩,
        ⟨4232, false, false, [], []⟩,
        ⟨4233, false, false, [], []⟩,
        ⟨4235, false, false, [145], []⟩,
        ⟨4175, true, false, [], [77723]⟩
      ]⟩,
    ⟨[77721, 9], [135, 77721], .contexts [
        ⟨4216, false, false, [], []⟩,
        ⟨4217, false, false, [], []⟩,
        ⟨995, true, false, [], [77721]⟩,
        ⟨4214, false, false, [], []⟩,
        ⟨4215, false, false, [], []⟩,
        ⟨4215, false, false, [], []⟩
      ]⟩,
    ⟨[135, 77723], [135, 77723], .contexts []⟩,
    ⟨[135, 77723], [135, 77723], .contexts []⟩,
    ⟨[77723, 9], [77723, 9], .contexts []⟩,
    ⟨[77721, 11], [151, 77721], .contexts [
        ⟨4220, false, false, [], []⟩,
        ⟨4220, false, false, [], []⟩,
        ⟨4205, true, false, [], [11]⟩,
        ⟨181, false, false, [77719], []⟩,
        ⟨182, false, false, [77719], []⟩,
        ⟨4190, false, false, [], [1]⟩,
        ⟨4192, false, false, [], [1]⟩,
        ⟨4188, false, false, [], [1]⟩,
        ⟨4189, false, false, [], [1]⟩,
        ⟨4189, false, false, [], [1]⟩,
        ⟨4201, false, false, [151], []⟩,
        ⟨4218, false, false, [], []⟩,
        ⟨4219, false, false, [], []⟩,
        ⟨4212, false, false, [151], []⟩,
        ⟨4191, true, false, [], [77721]⟩,
        ⟨4218, false, false, [], []⟩,
        ⟨4219, false, false, [], []⟩,
        ⟨4219, false, false, [], []⟩
      ]⟩,
    ⟨[151, 77723], [151, 77723], .contexts []⟩,
    ⟨[151, 77723], [151, 77723], .contexts []⟩,
    ⟨[77723, 11], [77723, 11], .contexts []⟩,
    ⟨[77725], [77723, 5], .source 38927⟩,
    ⟨[77723, 5], [77725], .contexts [
        ⟨4245, true, false, [], []⟩
      ]⟩,
    ⟨[77725], [77725], .contexts []⟩,
    ⟨[77725], [77725], .contexts []⟩,
    ⟨[77723, 5], [77725], .contexts [
        ⟨4246, false, false, [], []⟩,
        ⟨4247, false, false, [], []⟩,
        ⟨4248, false, false, [], []⟩,
        ⟨4248, false, false, [], []⟩
      ]⟩,
    ⟨[145, 77725], [145, 77725], .contexts []⟩,
    ⟨[145, 77725], [145, 77725], .contexts []⟩,
    ⟨[77725], [77725], .contexts []⟩,
    ⟨[77725, 1], [145, 77725], .contexts [
        ⟨4249, true, false, [], [1]⟩,
        ⟨256, false, false, [77723], []⟩,
        ⟨257, false, false, [77723], []⟩,
        ⟨4234, false, false, [], [5]⟩,
        ⟨4236, false, false, [], [5]⟩,
        ⟨4232, false, false, [], [5]⟩,
        ⟨4233, false, false, [], [5]⟩,
        ⟨4233, false, false, [], [5]⟩,
        ⟨4246, false, false, [145], []⟩,
        ⟨4250, false, false, [], []⟩,
        ⟨4251, false, false, [], []⟩,
        ⟨4252, false, false, [145], []⟩,
        ⟨4175, true, false, [], [77725]⟩
      ]⟩,
    ⟨[77721, 5], [293, 77245], .contexts [
        ⟨4208, false, false, [], []⟩
      ]⟩,
    ⟨[77725, 3], [77725, 3], .contexts []⟩,
    ⟨[77725, 3], [293, 77249], .contexts [
        ⟨4255, false, false, [], []⟩,
        ⟨4249, true, false, [], [3]⟩,
        ⟨264, false, false, [77723], []⟩,
        ⟨267, false, false, [77723], []⟩,
        ⟨4225, false, false, [], [5, 3, 5]⟩,
        ⟨4203, false, false, [], [5, 3, 5]⟩,
        ⟨4204, false, false, [], [5, 3, 5]⟩,
        ⟨4204, false, false, [], [5, 3, 5]⟩,
        ⟨4254, false, false, [], [3, 5]⟩,
        ⟨1887, false, false, [], [3, 5]⟩,
        ⟨1888, false, false, [], [3, 5]⟩,
        ⟨1888, false, false, [], [3, 5]⟩,
        ⟨1889, false, false, [], [5]⟩,
        ⟨1890, false, false, [], [5]⟩,
        ⟨1891, false, false, [], [5]⟩,
        ⟨1892, false, false, [], [5]⟩,
        ⟨1903, false, false, [], []⟩,
        ⟨1904, false, false, [], []⟩,
        ⟨1905, false, false, [], []⟩,
        ⟨1906, false, false, [], []⟩,
        ⟨1710, false, false, [293], []⟩
      ]⟩,
    ⟨[135, 77725], [135, 77725], .contexts []⟩,
    ⟨[135, 77725], [135, 77725], .contexts []⟩,
    ⟨[77725, 9], [77725, 9], .contexts []⟩,
    ⟨[77725, 9], [135, 77725], .contexts [
        ⟨4259, false, false, [], []⟩,
        ⟨4249, true, false, [], [9]⟩,
        ⟨2076, false, false, [77723], []⟩,
        ⟨2077, false, false, [77723], []⟩,
        ⟨4240, false, false, [], [5]⟩,
        ⟨4240, false, false, [], [5]⟩,
        ⟨4229, true, false, [], [9, 5]⟩,
        ⟨1112, false, false, [77721], [5]⟩,
        ⟨1113, false, false, [77721], [5]⟩,
        ⟨4237, false, false, [], [3, 5]⟩,
        ⟨4224, false, false, [135], [5]⟩,
        ⟨4238, false, false, [], [5]⟩,
        ⟨4239, false, false, [], [5]⟩,
        ⟨4235, false, false, [135], [5]⟩,
        ⟨995, true, false, [], [77723, 5]⟩,
        ⟨4238, false, false, [], [5]⟩,
        ⟨4239, false, false, [], [5]⟩,
        ⟨4239, false, false, [], [5]⟩,
        ⟨4246, false, false, [135], []⟩,
        ⟨4257, false, false, [], []⟩,
        ⟨4258, false, false, [], []⟩
      ]⟩,
    ⟨[77725, 9], [135, 77725], .contexts [
        ⟨4260, false, false, [], []⟩,
        ⟨4252, false, false, [135], []⟩,
        ⟨995, true, false, [], [77725]⟩
      ]⟩,
    ⟨[151, 77725], [151, 77725], .contexts []⟩,
    ⟨[151, 77725], [151, 77725], .contexts []⟩,
    ⟨[77725, 11], [77725, 11], .contexts []⟩,
    ⟨[77725, 11], [151, 77725], .contexts [
        ⟨4264, false, false, [], []⟩,
        ⟨4249, true, false, [], [11]⟩,
        ⟨275, false, false, [77723], []⟩,
        ⟨276, false, false, [77723], []⟩,
        ⟨4244, false, false, [], [5]⟩,
        ⟨4244, false, false, [], [5]⟩,
        ⟨4229, true, false, [], [11, 5]⟩,
        ⟨231, false, false, [77721], [5]⟩,
        ⟨232, false, false, [77721], [5]⟩,
        ⟨4241, false, false, [], [3, 5]⟩,
        ⟨4224, false, false, [151], [5]⟩,
        ⟨4242, false, false, [], [5]⟩,
        ⟨4243, false, false, [], [5]⟩,
        ⟨4235, false, false, [151], [5]⟩,
        ⟨4191, true, false, [], [77723, 5]⟩,
        ⟨4242, false, false, [], [5]⟩,
        ⟨4243, false, false, [], [5]⟩,
        ⟨4243, false, false, [], [5]⟩,
        ⟨4246, false, false, [151], []⟩,
        ⟨4262, false, false, [], []⟩,
        ⟨4263, false, false, [], []⟩
      ]⟩,
    ⟨[77725, 11], [151, 77725], .contexts [
        ⟨4265, false, false, [], []⟩,
        ⟨4252, false, false, [151], []⟩,
        ⟨4191, true, false, [], [77725]⟩
      ]⟩,
    ⟨[77727], [77725, 13], .source 38928⟩,
    ⟨[77725, 13], [77727], .contexts [
        ⟨4267, true, false, [], []⟩
      ]⟩,
    ⟨[77727, 13], [77725], .contexts [
        ⟨4268, true, false, [], [13]⟩,
        ⟨98, false, false, [77725], []⟩,
        ⟨4248, false, false, [], []⟩
      ]⟩,
    ⟨[77727], [77727], .contexts []⟩,
    ⟨[77727], [77727], .contexts []⟩,
    ⟨[77725, 13], [77727], .contexts [
        ⟨4268, false, false, [], []⟩,
        ⟨4270, false, false, [], []⟩,
        ⟨4271, false, false, [], []⟩,
        ⟨4271, false, false, [], []⟩
      ]⟩,
    ⟨[293, 77369], [293, 77369], .contexts []⟩,
    ⟨[293, 77369], [293, 77369], .contexts []⟩,
    ⟨[293, 77369], [293, 77369], .contexts []⟩,
    ⟨[77727, 3], [77727, 3], .contexts []⟩,
    ⟨[77727, 3], [293, 77369], .contexts [
        ⟨4276, false, false, [], []⟩,
        ⟨4272, true, false, [], [3]⟩,
        ⟨107, false, false, [77725], []⟩,
        ⟨109, false, false, [77725], []⟩,
        ⟨4255, false, false, [], [13]⟩,
        ⟨4256, false, false, [], [13]⟩,
        ⟨4179, true, false, [], [77249, 13]⟩,
        ⟨1904, false, false, [], [13]⟩,
        ⟨1906, false, false, [], [13]⟩,
        ⟨1906, false, false, [], [13]⟩,
        ⟨2084, false, false, [293], []⟩,
        ⟨4273, false, false, [], []⟩,
        ⟨4274, false, false, [], []⟩,
        ⟨4275, false, false, [], []⟩,
        ⟨2078, false, false, [293], []⟩,
        ⟨4179, true, false, [], [77369]⟩
      ]⟩,
    ⟨[77369, 3], [295, 77727], .contexts [
        ⟨4277, true, false, [292], [3]⟩,
        ⟨35, false, false, [292, 77727], []⟩,
        ⟨1856, true, false, [], [77727]⟩
      ]⟩,
    ⟨[135, 77727], [135, 77727], .contexts []⟩,
    ⟨[135, 77727], [135, 77727], .contexts []⟩,
    ⟨[77727], [77727], .contexts []⟩,
    ⟨[151, 77727], [151, 77727], .contexts []⟩,
    ⟨[151, 77727], [151, 77727], .contexts []⟩,
    ⟨[77727, 11], [77727, 11], .contexts []⟩,
    ⟨[859], [293, 329], .source 494⟩,
    ⟨[861], [859, 295], .source 495⟩,
    ⟨[77727, 15], [77727, 15], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 067. -/
def y322TCContextRaw067 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[863], [860], .source 496⟩,
    ⟨[860], [860], .contexts []⟩,
    ⟨[77727, 15], [863, 77727], .contexts [
        ⟨4287, false, false, [], []⟩,
        ⟨4286, false, false, [860], [77727, 15]⟩,
        ⟨4278, true, false, [860, 859], [15]⟩,
        ⟨4285, false, false, [860], [77369, 3, 15]⟩,
        ⟨2089, true, false, [860, 293], [3, 15]⟩,
        ⟨4275, true, false, [860], [15, 3, 15]⟩,
        ⟨4275, true, false, [860], [15, 3, 15]⟩,
        ⟨4273, true, false, [860], [15, 3, 15]⟩,
        ⟨4277, true, false, [860], [15, 3, 15]⟩,
        ⟨4276, true, false, [860], [15, 3, 15]⟩,
        ⟨2767, false, false, [860, 77727], []⟩,
        ⟨4281, false, false, [860], []⟩,
        ⟨4289, true, false, [], [77727]⟩,
        ⟨4289, true, false, [], [77727]⟩,
        ⟨4288, true, false, [], [77727]⟩
      ]⟩,
    ⟨[77729], [77727, 1], .source 38929⟩,
    ⟨[77727, 1], [77729], .contexts [
        ⟨4291, true, false, [], []⟩
      ]⟩,
    ⟨[77729, 1], [77727], .contexts [
        ⟨4292, true, false, [], [1]⟩,
        ⟨18, false, false, [77727], []⟩,
        ⟨4271, false, false, [], []⟩
      ]⟩,
    ⟨[77729], [77729], .contexts []⟩,
    ⟨[77729], [77729], .contexts []⟩,
    ⟨[77727, 1], [77729], .contexts [
        ⟨4292, false, false, [], []⟩,
        ⟨4294, false, false, [], []⟩,
        ⟨4295, false, false, [], []⟩,
        ⟨4295, false, false, [], []⟩
      ]⟩,
    ⟨[151, 77729], [151, 77729], .contexts []⟩,
    ⟨[77727, 11, 1], [151, 77729], .contexts [
        ⟨4284, false, false, [], [1]⟩,
        ⟨4284, false, false, [], [1]⟩,
        ⟨4272, true, false, [], [11, 1]⟩,
        ⟨137, false, false, [77725], [1]⟩,
        ⟨138, false, false, [77725], [1]⟩,
        ⟨4264, false, false, [], [13, 1]⟩,
        ⟨4266, false, false, [], [13, 1]⟩,
        ⟨4262, false, false, [], [13, 1]⟩,
        ⟨4263, false, false, [], [13, 1]⟩,
        ⟨4263, false, false, [], [13, 1]⟩,
        ⟨4268, false, false, [151], [1]⟩,
        ⟨4282, false, false, [], [1]⟩,
        ⟨4283, false, false, [], [1]⟩,
        ⟨4281, false, false, [151], [1]⟩,
        ⟨4191, true, false, [], [77727, 1]⟩,
        ⟨4282, false, false, [], [1]⟩,
        ⟨4283, false, false, [], [1]⟩,
        ⟨4283, false, false, [], [1]⟩,
        ⟨4292, false, false, [151], []⟩,
        ⟨4297, false, false, [], []⟩
      ]⟩,
    ⟨[151, 77729], [151, 77729], .contexts []⟩,
    ⟨[77729, 11], [77729, 11], .contexts []⟩,
    ⟨[77729], [77729], .contexts []⟩,
    ⟨[145, 77729], [145, 77729], .contexts []⟩,
    ⟨[145, 77729], [145, 77729], .contexts []⟩,
    ⟨[77729, 13], [77729, 13], .contexts []⟩,
    ⟨[77729, 13], [145, 77729], .contexts [
        ⟨4304, false, false, [], []⟩,
        ⟨4296, true, false, [], [13]⟩,
        ⟨189, false, false, [77727], []⟩,
        ⟨192, false, false, [77727], []⟩,
        ⟨4269, false, false, [], [1, 13, 1]⟩,
        ⟨4247, false, false, [], [1, 13, 1]⟩,
        ⟨4248, false, false, [], [1, 13, 1]⟩,
        ⟨4248, false, false, [], [1, 13, 1]⟩,
        ⟨4253, false, false, [], [13, 1]⟩,
        ⟨4250, false, false, [], [13, 1]⟩,
        ⟨4251, false, false, [], [13, 1]⟩,
        ⟨4251, false, false, [], [13, 1]⟩,
        ⟨4268, false, false, [145], [1]⟩,
        ⟨4292, false, false, [145], []⟩,
        ⟨4302, false, false, [], []⟩,
        ⟨4303, false, false, [], []⟩,
        ⟨4301, false, false, [145], []⟩
      ]⟩,
    ⟨[77727, 15], [863, 77727], .contexts [
        ⟨4290, false, false, [], []⟩
      ]⟩,
    ⟨[863, 77727], [863, 77727], .contexts []⟩,
    ⟨[863, 77727], [863, 77727], .contexts []⟩,
    ⟨[863, 77729], [863, 77729], .contexts []⟩,
    ⟨[863, 77729], [863, 77729], .contexts []⟩,
    ⟨[77729, 15], [77729, 15], .contexts []⟩,
    ⟨[863], [863], .contexts [
        ⟨24, false, false, [], [863]⟩
      ]⟩,
    ⟨[77731], [77729, 3], .source 38930⟩,
    ⟨[77729, 3], [77731], .contexts [
        ⟨4313, true, false, [], []⟩
      ]⟩,
    ⟨[77731, 3], [77729], .contexts [
        ⟨4314, true, false, [], [3]⟩,
        ⟨35, false, false, [77729], []⟩,
        ⟨4295, false, false, [], []⟩
      ]⟩,
    ⟨[77731], [77731], .contexts []⟩,
    ⟨[77731], [77731], .contexts []⟩,
    ⟨[77729, 3], [77731], .contexts [
        ⟨4314, false, false, [], []⟩,
        ⟨4316, false, false, [], []⟩,
        ⟨4317, false, false, [], []⟩,
        ⟨4317, false, false, [], []⟩
      ]⟩,
    ⟨[77729, 11], [151, 77729], .contexts [
        ⟨4300, false, false, [], []⟩,
        ⟨4296, true, false, [], [11]⟩,
        ⟨181, false, false, [77727], []⟩,
        ⟨182, false, false, [77727], []⟩,
        ⟨4298, false, false, [], []⟩,
        ⟨4299, false, false, [], []⟩,
        ⟨4301, false, false, [151], []⟩,
        ⟨4191, true, false, [], [77729]⟩
      ]⟩,
    ⟨[151, 77731], [151, 77731], .contexts []⟩,
    ⟨[151, 77731], [151, 77731], .contexts []⟩,
    ⟨[77731, 11], [77731, 11], .contexts []⟩,
    ⟨[77731], [77731], .contexts []⟩,
    ⟨[77731, 11], [151, 77731], .contexts [
        ⟨4322, false, false, [], []⟩,
        ⟨4318, true, false, [], [11]⟩,
        ⟨231, false, false, [77729], []⟩,
        ⟨232, false, false, [77729], []⟩,
        ⟨4300, false, false, [], [3]⟩,
        ⟨4319, false, false, [], [3]⟩,
        ⟨4297, false, false, [], [3]⟩,
        ⟨4299, false, false, [], [3]⟩,
        ⟨4299, false, false, [], [3]⟩,
        ⟨4314, false, false, [151], []⟩,
        ⟨4320, false, false, [], []⟩,
        ⟨4321, false, false, [], []⟩,
        ⟨4323, false, false, [151], []⟩,
        ⟨4191, true, false, [], [77731]⟩
      ]⟩,
    ⟨[77729, 13], [145, 77729], .contexts [
        ⟨4304, false, false, [], []⟩,
        ⟨4305, false, false, [], []⟩,
        ⟨4175, true, false, [], [77729]⟩,
        ⟨4302, false, false, [], []⟩,
        ⟨4303, false, false, [], []⟩,
        ⟨4303, false, false, [], []⟩
      ]⟩,
    ⟨[145, 77731], [145, 77731], .contexts []⟩,
    ⟨[145, 77731], [145, 77731], .contexts []⟩,
    ⟨[77731, 13], [77731, 13], .contexts []⟩,
    ⟨[77729, 15], [863, 77729], .contexts [
        ⟨4311, false, false, [], []⟩,
        ⟨4311, false, false, [], []⟩,
        ⟨4296, true, false, [], [15]⟩,
        ⟨199, false, false, [77727], []⟩,
        ⟨200, false, false, [77727], []⟩,
        ⟨4287, false, false, [], [1]⟩,
        ⟨4306, false, false, [], [1]⟩,
        ⟨4307, false, false, [], [1]⟩,
        ⟨4308, false, false, [], [1]⟩,
        ⟨4308, false, false, [], [1]⟩,
        ⟨4292, false, false, [863], []⟩,
        ⟨4309, false, false, [], []⟩,
        ⟨4310, false, false, [], []⟩,
        ⟨4301, false, false, [863], []⟩,
        ⟨4312, true, false, [], [77729]⟩,
        ⟨4309, false, false, [], []⟩,
        ⟨4310, false, false, [], []⟩,
        ⟨4310, false, false, [], []⟩
      ]⟩,
    ⟨[863, 77731], [863, 77731], .contexts []⟩,
    ⟨[863, 77731], [863, 77731], .contexts []⟩,
    ⟨[77731, 15], [77731, 15], .contexts []⟩,
    ⟨[77733], [77731, 5], .source 38931⟩,
    ⟨[77731, 5], [77733], .contexts [
        ⟨4333, true, false, [], []⟩
      ]⟩,
    ⟨[77731, 5], [77733], .contexts [
        ⟨4334, false, false, [], []⟩
      ]⟩,
    ⟨[77733], [77733], .contexts []⟩,
    ⟨[77733], [77733], .contexts []⟩,
    ⟨[77731, 5], [77733], .contexts [
        ⟨4335, false, false, [], []⟩,
        ⟨4336, false, false, [], []⟩,
        ⟨4337, false, false, [], []⟩,
        ⟨4337, false, false, [], []⟩
      ]⟩,
    ⟨[151, 77733], [151, 77733], .contexts []⟩,
    ⟨[151, 77733], [151, 77733], .contexts []⟩,
    ⟨[77733, 11], [77733, 11], .contexts []⟩,
    ⟨[77733], [77733], .contexts []⟩,
    ⟨[77731, 13], [145, 77731], .contexts [
        ⟨4328, false, false, [], []⟩,
        ⟨4328, false, false, [], []⟩,
        ⟨4318, true, false, [], [13]⟩,
        ⟨238, false, false, [77729], []⟩,
        ⟨239, false, false, [77729], []⟩,
        ⟨4325, false, false, [], [3]⟩,
        ⟨4314, false, false, [145], []⟩,
        ⟨4326, false, false, [], []⟩,
        ⟨4327, false, false, [], []⟩,
        ⟨4323, false, false, [145], []⟩,
        ⟨4175, true, false, [], [77731]⟩,
        ⟨4326, false, false, [], []⟩,
        ⟨4327, false, false, [], []⟩,
        ⟨4327, false, false, [], []⟩
      ]⟩,
    ⟨[145, 77733], [145, 77733], .contexts []⟩,
    ⟨[145, 77733], [145, 77733], .contexts []⟩,
    ⟨[145, 77733], [145, 77733], .contexts []⟩,
    ⟨[77733, 13], [77733, 13], .contexts []⟩,
    ⟨[863, 77733], [863, 77733], .contexts []⟩,
    ⟨[863, 77733], [863, 77733], .contexts []⟩,
    ⟨[77733, 15], [77733, 15], .contexts []⟩,
    ⟨[77733, 15], [863, 77733], .contexts [
        ⟨4350, false, false, [], []⟩,
        ⟨4338, true, false, [], [15]⟩,
        ⟨290, false, false, [77731], []⟩,
        ⟨291, false, false, [77731], []⟩,
        ⟨4332, false, false, [], [5]⟩,
        ⟨4332, false, false, [], [5]⟩,
        ⟨4318, true, false, [], [15, 5]⟩,
        ⟨245, false, false, [77729], [5]⟩,
        ⟨246, false, false, [77729], [5]⟩,
        ⟨4329, false, false, [], [3, 5]⟩,
        ⟨4314, false, false, [863], [5]⟩,
        ⟨4330, false, false, [], [5]⟩,
        ⟨4331, false, false, [], [5]⟩,
        ⟨4323, false, false, [863], [5]⟩,
        ⟨4312, true, false, [], [77731, 5]⟩,
        ⟨4330, false, false, [], [5]⟩,
        ⟨4331, false, false, [], [5]⟩,
        ⟨4331, false, false, [], [5]⟩,
        ⟨4334, false, false, [863], []⟩,
        ⟨4348, false, false, [], []⟩,
        ⟨4349, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 068. -/
def y322TCContextRaw068 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77735], [77733, 1], .source 38932⟩,
    ⟨[77733, 1], [77735], .contexts [
        ⟨4352, true, false, [], []⟩
      ]⟩,
    ⟨[77735, 1], [77733], .contexts [
        ⟨4353, true, false, [], [1]⟩,
        ⟨18, false, false, [77733], []⟩,
        ⟨4337, false, false, [], []⟩
      ]⟩,
    ⟨[77735], [77735], .contexts []⟩,
    ⟨[77735], [77735], .contexts []⟩,
    ⟨[77733, 1], [77735], .contexts [
        ⟨4353, false, false, [], []⟩,
        ⟨4355, false, false, [], []⟩,
        ⟨4356, false, false, [], []⟩,
        ⟨4356, false, false, [], []⟩
      ]⟩,
    ⟨[151, 77735], [151, 77735], .contexts []⟩,
    ⟨[77733, 11, 1], [151, 77735], .contexts [
        ⟨4341, false, false, [], [1]⟩,
        ⟨4341, false, false, [], [1]⟩,
        ⟨4338, true, false, [], [11, 1]⟩,
        ⟨275, false, false, [77731], [1]⟩,
        ⟨276, false, false, [77731], [1]⟩,
        ⟨4322, false, false, [], [5, 1]⟩,
        ⟨4324, false, false, [], [5, 1]⟩,
        ⟨4320, false, false, [], [5, 1]⟩,
        ⟨4321, false, false, [], [5, 1]⟩,
        ⟨4321, false, false, [], [5, 1]⟩,
        ⟨4334, false, false, [151], [1]⟩,
        ⟨4339, false, false, [], [1]⟩,
        ⟨4340, false, false, [], [1]⟩,
        ⟨4342, false, false, [151], [1]⟩,
        ⟨4191, true, false, [], [77733, 1]⟩,
        ⟨4339, false, false, [], [1]⟩,
        ⟨4340, false, false, [], [1]⟩,
        ⟨4340, false, false, [], [1]⟩,
        ⟨4353, false, false, [151], []⟩,
        ⟨4358, false, false, [], []⟩
      ]⟩,
    ⟨[151, 77735], [151, 77735], .contexts []⟩,
    ⟨[77735, 11], [77735, 11], .contexts []⟩,
    ⟨[77735], [77735], .contexts []⟩,
    ⟨[77733, 15], [863, 77733], .contexts [
        ⟨4350, false, false, [], []⟩,
        ⟨4351, false, false, [], []⟩,
        ⟨4342, false, false, [863], []⟩,
        ⟨4312, true, false, [], [77733]⟩,
        ⟨4348, false, false, [], []⟩,
        ⟨4349, false, false, [], []⟩,
        ⟨4349, false, false, [], []⟩
      ]⟩,
    ⟨[77737], [77735, 9], .source 38933⟩,
    ⟨[77735, 9], [77737], .contexts [
        ⟨4364, true, false, [], []⟩
      ]⟩,
    ⟨[77737], [77737], .contexts []⟩,
    ⟨[77737], [77737], .contexts []⟩,
    ⟨[77735, 9], [77737], .contexts [
        ⟨4365, false, false, [], []⟩,
        ⟨4366, false, false, [], []⟩,
        ⟨4367, false, false, [], []⟩,
        ⟨4367, false, false, [], []⟩
      ]⟩,
    ⟨[77737], [77737], .contexts []⟩,
    ⟨[77739], [77737, 11], .source 38934⟩,
    ⟨[77737, 11], [77739], .contexts [
        ⟨4370, true, false, [], []⟩
      ]⟩,
    ⟨[77739], [77739], .contexts []⟩,
    ⟨[77739], [77739], .contexts []⟩,
    ⟨[77741], [77739, 1], .source 38935⟩,
    ⟨[77739, 1], [77741], .contexts [
        ⟨4374, true, false, [], []⟩
      ]⟩,
    ⟨[77741], [77741], .contexts []⟩,
    ⟨[77741], [77741], .contexts []⟩,
    ⟨[77739, 1], [77741], .contexts [
        ⟨4375, false, false, [], []⟩,
        ⟨4376, false, false, [], []⟩,
        ⟨4377, false, false, [], []⟩,
        ⟨4377, false, false, [], []⟩
      ]⟩,
    ⟨[77741], [77741], .contexts []⟩,
    ⟨[77743], [77741, 13], .source 38936⟩,
    ⟨[77741, 13], [77743], .contexts [
        ⟨4380, true, false, [], []⟩
      ]⟩,
    ⟨[77745], [77743, 15], .source 38937⟩,
    ⟨[77743, 15], [77745], .contexts [
        ⟨4382, true, false, [], []⟩
      ]⟩,
    ⟨[77743], [77743], .contexts []⟩,
    ⟨[77745], [77745], .contexts []⟩,
    ⟨[77745], [77745], .contexts []⟩,
    ⟨[77743, 15], [77745], .contexts [
        ⟨4383, false, false, [], []⟩,
        ⟨4385, false, false, [], []⟩,
        ⟨4386, false, false, [], []⟩,
        ⟨4386, false, false, [], []⟩
      ]⟩,
    ⟨[77745], [77745], .contexts []⟩,
    ⟨[77747], [77745, 1], .source 38938⟩,
    ⟨[77745, 1], [77747], .contexts [
        ⟨4389, true, false, [], []⟩
      ]⟩,
    ⟨[77749], [77747, 3], .source 38939⟩,
    ⟨[77747, 3], [77749], .contexts [
        ⟨4391, true, false, [], []⟩
      ]⟩,
    ⟨[77747], [77747], .contexts []⟩,
    ⟨[77751], [77749, 5], .source 38940⟩,
    ⟨[77749, 5], [77751], .contexts [
        ⟨4394, true, false, [], []⟩
      ]⟩,
    ⟨[77749], [77749], .contexts []⟩,
    ⟨[77753], [77751, 1], .source 38941⟩,
    ⟨[77751, 1], [77753], .contexts [
        ⟨4397, true, false, [], []⟩
      ]⟩,
    ⟨[77751], [77751], .contexts []⟩,
    ⟨[77755], [77753, 9], .source 38942⟩,
    ⟨[77753, 9], [77755], .contexts [
        ⟨4400, true, false, [], []⟩
      ]⟩,
    ⟨[77753], [77753], .contexts []⟩,
    ⟨[77757], [77755, 11], .source 38943⟩,
    ⟨[77755, 11], [77757], .contexts [
        ⟨4403, true, false, [], []⟩
      ]⟩,
    ⟨[77755], [77755], .contexts []⟩,
    ⟨[77759], [77757, 1], .source 38944⟩,
    ⟨[77757, 1], [77759], .contexts [
        ⟨4406, true, false, [], []⟩
      ]⟩,
    ⟨[77757], [77757], .contexts []⟩,
    ⟨[77761], [77759, 13], .source 38945⟩,
    ⟨[77759, 13], [77761], .contexts [
        ⟨4409, true, false, [], []⟩
      ]⟩,
    ⟨[77759], [77759], .contexts []⟩,
    ⟨[77763], [77761, 15], .source 38946⟩,
    ⟨[77761, 15], [77763], .contexts [
        ⟨4412, true, false, [], []⟩
      ]⟩,
    ⟨[77761], [77761], .contexts []⟩,
    ⟨[77765], [77763, 1], .source 38947⟩]

/-- Exact literal claimed equations and contextual derivations, block 069. -/
def y322TCContextRaw069 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77763, 1], [77765], .contexts [
        ⟨4415, true, false, [], []⟩
      ]⟩,
    ⟨[77763], [77763], .contexts []⟩,
    ⟨[77767], [77765, 3], .source 38948⟩,
    ⟨[77765, 3], [77767], .contexts [
        ⟨4418, true, false, [], []⟩
      ]⟩,
    ⟨[77765], [77765], .contexts []⟩,
    ⟨[77769], [77767, 5], .source 38949⟩,
    ⟨[77767, 5], [77769], .contexts [
        ⟨4421, true, false, [], []⟩
      ]⟩,
    ⟨[77767], [77767], .contexts []⟩,
    ⟨[77771], [77769, 1], .source 38950⟩,
    ⟨[77769, 1], [77771], .contexts [
        ⟨4424, true, false, [], []⟩
      ]⟩,
    ⟨[77769], [77769], .contexts []⟩,
    ⟨[77773], [77771, 9], .source 38951⟩,
    ⟨[77771, 9], [77773], .contexts [
        ⟨4427, true, false, [], []⟩
      ]⟩,
    ⟨[77771], [77771], .contexts []⟩,
    ⟨[77775], [77773, 11], .source 38952⟩,
    ⟨[77773, 11], [77775], .contexts [
        ⟨4430, true, false, [], []⟩
      ]⟩,
    ⟨[77773], [77773], .contexts []⟩,
    ⟨[77777], [77775, 1], .source 38953⟩,
    ⟨[77775, 1], [77777], .contexts [
        ⟨4433, true, false, [], []⟩
      ]⟩,
    ⟨[77775], [77775], .contexts []⟩,
    ⟨[77779], [77777, 13], .source 38954⟩,
    ⟨[77777, 13], [77779], .contexts [
        ⟨4436, true, false, [], []⟩
      ]⟩,
    ⟨[77777], [77777], .contexts []⟩,
    ⟨[77781], [77779, 15], .source 38955⟩,
    ⟨[77779, 15], [77781], .contexts [
        ⟨4439, true, false, [], []⟩
      ]⟩,
    ⟨[77779], [77779], .contexts []⟩,
    ⟨[77783], [77781, 1], .source 38956⟩,
    ⟨[77781, 1], [77783], .contexts [
        ⟨4442, true, false, [], []⟩
      ]⟩,
    ⟨[77781], [77781], .contexts []⟩,
    ⟨[77785], [77783, 3], .source 38957⟩,
    ⟨[77783, 3], [77785], .contexts [
        ⟨4445, true, false, [], []⟩
      ]⟩,
    ⟨[77783], [77783], .contexts []⟩,
    ⟨[77787], [77785, 5], .source 38958⟩,
    ⟨[77785, 5], [77787], .contexts [
        ⟨4448, true, false, [], []⟩
      ]⟩,
    ⟨[77785], [77785], .contexts []⟩,
    ⟨[77789], [77787, 1], .source 38959⟩,
    ⟨[77787, 1], [77789], .contexts [
        ⟨4451, true, false, [], []⟩
      ]⟩,
    ⟨[77787], [77787], .contexts []⟩,
    ⟨[77791], [77789, 9], .source 38960⟩,
    ⟨[77789], [77789], .contexts []⟩,
    ⟨[77793], [77791, 11], .source 38961⟩,
    ⟨[77791], [77791], .contexts []⟩,
    ⟨[77795], [77793, 1], .source 38962⟩,
    ⟨[77793], [77793], .contexts []⟩,
    ⟨[77797], [77795, 13], .source 38963⟩,
    ⟨[77795], [77795], .contexts []⟩,
    ⟨[77799], [77797, 15], .source 38964⟩,
    ⟨[77797], [77797], .contexts []⟩,
    ⟨[77801], [77799, 1], .source 38965⟩,
    ⟨[77799], [77799], .contexts []⟩,
    ⟨[77803], [77801, 3], .source 38966⟩,
    ⟨[77801], [77801], .contexts []⟩,
    ⟨[77805], [77803, 5], .source 38967⟩,
    ⟨[77803], [77803], .contexts []⟩,
    ⟨[77807], [77805, 1], .source 38968⟩,
    ⟨[77805], [77805], .contexts []⟩,
    ⟨[77809], [77807, 9], .source 38969⟩,
    ⟨[77807], [77807], .contexts []⟩,
    ⟨[77811], [77809, 11], .source 38970⟩,
    ⟨[77809], [77809], .contexts []⟩,
    ⟨[77813], [77811, 1], .source 38971⟩,
    ⟨[77811], [77811], .contexts []⟩,
    ⟨[77815], [77813, 13], .source 38972⟩,
    ⟨[77813], [77813], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 070. -/
def y322TCContextRaw070 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77817], [77815, 15], .source 38973⟩,
    ⟨[77815], [77815], .contexts []⟩,
    ⟨[77819], [77817, 1], .source 38974⟩,
    ⟨[77817], [77817], .contexts []⟩,
    ⟨[77819, 1], [77817], .contexts [
        ⟨4482, false, false, [], [1]⟩,
        ⟨18, false, false, [77817], []⟩,
        ⟨4483, false, false, [], []⟩
      ]⟩,
    ⟨[77821], [77819, 3], .source 38975⟩,
    ⟨[77819], [77819], .contexts []⟩,
    ⟨[77821, 3], [77819], .contexts [
        ⟨4485, false, false, [], [3]⟩,
        ⟨35, false, false, [77819], []⟩,
        ⟨4486, false, false, [], []⟩
      ]⟩,
    ⟨[77823], [77821, 5], .source 38976⟩,
    ⟨[77821], [77821], .contexts []⟩,
    ⟨[77823, 5], [77821], .contexts [
        ⟨4488, false, false, [], [5]⟩,
        ⟨49, false, false, [77821], []⟩,
        ⟨4489, false, false, [], []⟩
      ]⟩,
    ⟨[77825], [77823, 1], .source 38977⟩,
    ⟨[77823], [77823], .contexts []⟩,
    ⟨[77825, 1], [77823], .contexts [
        ⟨4491, false, false, [], [1]⟩,
        ⟨18, false, false, [77823], []⟩,
        ⟨4492, false, false, [], []⟩
      ]⟩,
    ⟨[77827], [77825, 9], .source 38978⟩,
    ⟨[77825], [77825], .contexts []⟩,
    ⟨[77827, 9], [77825], .contexts [
        ⟨4494, false, false, [], [9]⟩,
        ⟨76, false, false, [77825], []⟩,
        ⟨4495, false, false, [], []⟩
      ]⟩,
    ⟨[77829], [77827, 11], .source 38979⟩,
    ⟨[77827], [77827], .contexts []⟩,
    ⟨[77829, 11], [77827], .contexts [
        ⟨4497, false, false, [], [11]⟩,
        ⟨90, false, false, [77827], []⟩,
        ⟨4498, false, false, [], []⟩
      ]⟩,
    ⟨[77831], [77829, 1], .source 38980⟩,
    ⟨[77829, 1], [77831], .contexts [
        ⟨4500, true, false, [], []⟩
      ]⟩,
    ⟨[77829], [77829], .contexts []⟩,
    ⟨[77831, 1], [77829], .contexts [
        ⟨4501, true, false, [], [1]⟩,
        ⟨18, false, false, [77829], []⟩,
        ⟨4502, false, false, [], []⟩
      ]⟩,
    ⟨[77833], [77831, 13], .source 38981⟩,
    ⟨[77831], [77831], .contexts []⟩,
    ⟨[77833, 13], [77831], .contexts [
        ⟨4504, false, false, [], [13]⟩,
        ⟨98, false, false, [77831], []⟩,
        ⟨4505, false, false, [], []⟩
      ]⟩,
    ⟨[77835], [77833, 15], .source 38982⟩,
    ⟨[77833], [77833], .contexts []⟩,
    ⟨[77835, 15], [77833], .contexts [
        ⟨4507, false, false, [], [15]⟩,
        ⟨3, false, false, [77833], []⟩,
        ⟨4508, false, false, [], []⟩
      ]⟩,
    ⟨[77837], [77835, 1], .source 38983⟩,
    ⟨[77835], [77835], .contexts []⟩,
    ⟨[77837, 1], [77835], .contexts [
        ⟨4510, false, false, [], [1]⟩,
        ⟨18, false, false, [77835], []⟩,
        ⟨4511, false, false, [], []⟩
      ]⟩,
    ⟨[77839], [77837, 3], .source 38984⟩,
    ⟨[77837], [77837], .contexts []⟩,
    ⟨[77839, 3], [77837], .contexts [
        ⟨4513, false, false, [], [3]⟩,
        ⟨35, false, false, [77837], []⟩,
        ⟨4514, false, false, [], []⟩
      ]⟩,
    ⟨[77841], [77839, 5], .source 38985⟩,
    ⟨[77839], [77839], .contexts []⟩,
    ⟨[77841, 5], [77839], .contexts [
        ⟨4516, false, false, [], [5]⟩,
        ⟨49, false, false, [77839], []⟩,
        ⟨4517, false, false, [], []⟩
      ]⟩,
    ⟨[77843], [77841, 1], .source 38986⟩,
    ⟨[77841], [77841], .contexts []⟩,
    ⟨[77843, 1], [77841], .contexts [
        ⟨4519, false, false, [], [1]⟩,
        ⟨18, false, false, [77841], []⟩,
        ⟨4520, false, false, [], []⟩
      ]⟩,
    ⟨[77845], [77843, 9], .source 38987⟩,
    ⟨[77843], [77843], .contexts []⟩,
    ⟨[77845, 9], [77843], .contexts [
        ⟨4522, false, false, [], [9]⟩,
        ⟨76, false, false, [77843], []⟩,
        ⟨4523, false, false, [], []⟩
      ]⟩,
    ⟨[77847], [77845, 11], .source 38988⟩,
    ⟨[77845], [77845], .contexts []⟩,
    ⟨[77849], [77847, 1], .source 38989⟩,
    ⟨[77847, 1], [77849], .contexts [
        ⟨4527, true, false, [], []⟩
      ]⟩,
    ⟨[77847], [77847], .contexts []⟩,
    ⟨[77849, 1], [77847], .contexts [
        ⟨4528, true, false, [], [1]⟩,
        ⟨18, false, false, [77847], []⟩,
        ⟨4529, false, false, [], []⟩
      ]⟩,
    ⟨[77851], [77849, 13], .source 38990⟩,
    ⟨[77849, 13], [77851], .contexts [
        ⟨4531, true, false, [], []⟩
      ]⟩,
    ⟨[77849], [77849], .contexts []⟩,
    ⟨[77851], [77851], .contexts []⟩,
    ⟨[77847, 11], [77845], .contexts [
        ⟨4525, false, false, [], [11]⟩,
        ⟨90, false, false, [77845], []⟩,
        ⟨4526, false, false, [], []⟩
      ]⟩,
    ⟨[77845], [77845], .contexts []⟩,
    ⟨[77843], [77843], .contexts []⟩,
    ⟨[77841], [77841], .contexts []⟩,
    ⟨[77839], [77839], .contexts []⟩,
    ⟨[77849, 1, 11, 9, 1, 5], [77839], .contexts [
        ⟨4530, false, false, [], [11, 9, 1, 5]⟩,
        ⟨4529, false, false, [], [11, 9, 1, 5]⟩,
        ⟨4529, false, false, [], [11, 9, 1, 5]⟩,
        ⟨4535, false, false, [], [9, 1, 5]⟩,
        ⟨4536, false, false, [], [9, 1, 5]⟩,
        ⟨4526, false, false, [], [9, 1, 5]⟩,
        ⟨4526, false, false, [], [9, 1, 5]⟩,
        ⟨4524, false, false, [], [1, 5]⟩,
        ⟨4537, false, false, [], [1, 5]⟩,
        ⟨4523, false, false, [], [1, 5]⟩,
        ⟨4523, false, false, [], [1, 5]⟩,
        ⟨4521, false, false, [], [5]⟩,
        ⟨4538, false, false, [], [5]⟩,
        ⟨4520, false, false, [], [5]⟩,
        ⟨4520, false, false, [], [5]⟩,
        ⟨4518, false, false, [], []⟩,
        ⟨4539, false, false, [], []⟩,
        ⟨4517, false, false, [], []⟩,
        ⟨4517, false, false, [], []⟩
      ]⟩,
    ⟨[77837], [77837], .contexts []⟩,
    ⟨[77835], [77835], .contexts []⟩,
    ⟨[77833], [77833], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 071. -/
def y322TCContextRaw071 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77831], [77831], .contexts []⟩,
    ⟨[77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1], [77829], .contexts [
        ⟨4540, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨4515, false, false, [], [1, 15, 13, 1]⟩,
        ⟨4541, false, false, [], [1, 15, 13, 1]⟩,
        ⟨4514, false, false, [], [1, 15, 13, 1]⟩,
        ⟨4514, false, false, [], [1, 15, 13, 1]⟩,
        ⟨4512, false, false, [], [15, 13, 1]⟩,
        ⟨4542, false, false, [], [15, 13, 1]⟩,
        ⟨4511, false, false, [], [15, 13, 1]⟩,
        ⟨4511, false, false, [], [15, 13, 1]⟩,
        ⟨4509, false, false, [], [13, 1]⟩,
        ⟨4543, false, false, [], [13, 1]⟩,
        ⟨4508, false, false, [], [13, 1]⟩,
        ⟨4508, false, false, [], [13, 1]⟩,
        ⟨4506, false, false, [], [1]⟩,
        ⟨4544, false, false, [], [1]⟩,
        ⟨4505, false, false, [], [1]⟩,
        ⟨4505, false, false, [], [1]⟩,
        ⟨4503, false, false, [], []⟩,
        ⟨4502, false, false, [], []⟩,
        ⟨4502, false, false, [], []⟩
      ]⟩,
    ⟨[77827, 9], [77825], .contexts [
        ⟨4496, false, false, [], []⟩
      ]⟩,
    ⟨[77825], [77825], .contexts []⟩,
    ⟨[77823], [77823], .contexts []⟩,
    ⟨[77821], [77821], .contexts []⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3
    ], [77819], .contexts [
        ⟨4545, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨4499, false, false, [], [9, 1, 5, 3]⟩,
        ⟨4498, false, false, [], [9, 1, 5, 3]⟩,
        ⟨4498, false, false, [], [9, 1, 5, 3]⟩,
        ⟨4546, false, false, [], [1, 5, 3]⟩,
        ⟨4547, false, false, [], [1, 5, 3]⟩,
        ⟨4495, false, false, [], [1, 5, 3]⟩,
        ⟨4495, false, false, [], [1, 5, 3]⟩,
        ⟨4493, false, false, [], [5, 3]⟩,
        ⟨4548, false, false, [], [5, 3]⟩,
        ⟨4492, false, false, [], [5, 3]⟩,
        ⟨4492, false, false, [], [5, 3]⟩,
        ⟨4490, false, false, [], [3]⟩,
        ⟨4549, false, false, [], [3]⟩,
        ⟨4489, false, false, [], [3]⟩,
        ⟨4489, false, false, [], [3]⟩,
        ⟨4487, false, false, [], []⟩,
        ⟨4486, false, false, [], []⟩,
        ⟨4486, false, false, [], []⟩
      ]⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [77809], .contexts [
        ⟨4550, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨4484, false, false, [], [15, 13, 1, 11]⟩,
        ⟨4483, false, false, [], [15, 13, 1, 11]⟩,
        ⟨4483, false, false, [], [15, 13, 1, 11]⟩,
        ⟨4480, false, false, [], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [77815], [13, 1, 11]⟩,
        ⟨4481, false, false, [], [13, 1, 11]⟩,
        ⟨4481, false, false, [], [13, 1, 11]⟩,
        ⟨4481, false, false, [], [13, 1, 11]⟩,
        ⟨4478, false, false, [], [13, 1, 11]⟩,
        ⟨98, false, false, [77813], [1, 11]⟩,
        ⟨4479, false, false, [], [1, 11]⟩,
        ⟨4479, false, false, [], [1, 11]⟩,
        ⟨4479, false, false, [], [1, 11]⟩,
        ⟨4476, false, false, [], [1, 11]⟩,
        ⟨18, false, false, [77811], [11]⟩,
        ⟨4477, false, false, [], [11]⟩,
        ⟨4477, false, false, [], [11]⟩,
        ⟨4477, false, false, [], [11]⟩,
        ⟨4474, false, false, [], [11]⟩,
        ⟨90, false, false, [77809], []⟩,
        ⟨4475, false, false, [], []⟩,
        ⟨4475, false, false, [], []⟩,
        ⟨4475, false, false, [], []⟩
      ]⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3
    ], [77801], .contexts [
        ⟨4551, false, false, [], [9, 1, 5, 3]⟩,
        ⟨4472, false, false, [], [9, 1, 5, 3]⟩,
        ⟨76, false, false, [77807], [1, 5, 3]⟩,
        ⟨4473, false, false, [], [1, 5, 3]⟩,
        ⟨4473, false, false, [], [1, 5, 3]⟩,
        ⟨4473, false, false, [], [1, 5, 3]⟩,
        ⟨4470, false, false, [], [1, 5, 3]⟩,
        ⟨18, false, false, [77805], [5, 3]⟩,
        ⟨4471, false, false, [], [5, 3]⟩,
        ⟨4471, false, false, [], [5, 3]⟩,
        ⟨4471, false, false, [], [5, 3]⟩,
        ⟨4468, false, false, [], [5, 3]⟩,
        ⟨49, false, false, [77803], [3]⟩,
        ⟨4469, false, false, [], [3]⟩,
        ⟨4469, false, false, [], [3]⟩,
        ⟨4469, false, false, [], [3]⟩,
        ⟨4466, false, false, [], [3]⟩,
        ⟨35, false, false, [77801], []⟩,
        ⟨4467, false, false, [], []⟩,
        ⟨4467, false, false, [], []⟩,
        ⟨4467, false, false, [], []⟩
      ]⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1
    ], [77793], .contexts [
        ⟨4552, false, false, [], [1, 15, 13, 1]⟩,
        ⟨4464, false, false, [], [1, 15, 13, 1]⟩,
        ⟨18, false, false, [77799], [15, 13, 1]⟩,
        ⟨4465, false, false, [], [15, 13, 1]⟩,
        ⟨4465, false, false, [], [15, 13, 1]⟩,
        ⟨4465, false, false, [], [15, 13, 1]⟩,
        ⟨4462, false, false, [], [15, 13, 1]⟩,
        ⟨3, false, false, [77797], [13, 1]⟩,
        ⟨4463, false, false, [], [13, 1]⟩,
        ⟨4463, false, false, [], [13, 1]⟩,
        ⟨4463, false, false, [], [13, 1]⟩,
        ⟨4460, false, false, [], [13, 1]⟩,
        ⟨98, false, false, [77795], [1]⟩,
        ⟨4461, false, false, [], [1]⟩,
        ⟨4461, false, false, [], [1]⟩,
        ⟨4461, false, false, [], [1]⟩,
        ⟨4458, false, false, [], [1]⟩,
        ⟨18, false, false, [77793], []⟩,
        ⟨4459, false, false, [], []⟩,
        ⟨4459, false, false, [], []⟩,
        ⟨4459, false, false, [], []⟩
      ]⟩,
    ⟨[77787], [77787], .contexts []⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [77785], .contexts [
        ⟨4553, false, false, [], [11, 9, 1, 5]⟩,
        ⟨4456, false, false, [], [11, 9, 1, 5]⟩,
        ⟨90, false, false, [77791], [9, 1, 5]⟩,
        ⟨4457, false, false, [], [9, 1, 5]⟩,
        ⟨4457, false, false, [], [9, 1, 5]⟩,
        ⟨4457, false, false, [], [9, 1, 5]⟩,
        ⟨4454, false, false, [], [9, 1, 5]⟩,
        ⟨76, false, false, [77789], [1, 5]⟩,
        ⟨4455, false, false, [], [1, 5]⟩,
        ⟨4455, false, false, [], [1, 5]⟩,
        ⟨4455, false, false, [], [1, 5]⟩,
        ⟨4452, true, false, [], [1, 5]⟩,
        ⟨18, false, false, [77787], [5]⟩,
        ⟨4453, false, false, [], [5]⟩,
        ⟨4554, false, false, [], [5]⟩,
        ⟨4453, false, false, [], [5]⟩,
        ⟨4453, false, false, [], [5]⟩,
        ⟨4449, true, false, [], [5]⟩,
        ⟨49, false, false, [77785], []⟩,
        ⟨4450, false, false, [], []⟩,
        ⟨4450, false, false, [], []⟩,
        ⟨4450, false, false, [], []⟩
      ]⟩,
    ⟨[77783], [77783], .contexts []⟩,
    ⟨[77781], [77781], .contexts []⟩,
    ⟨[77779], [77779], .contexts []⟩,
    ⟨[77777], [77777], .contexts []⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13
    ], [77777], .contexts [
        ⟨4555, false, false, [], [3, 1, 15, 13]⟩,
        ⟨4446, true, false, [], [3, 1, 15, 13]⟩,
        ⟨35, false, false, [77783], [1, 15, 13]⟩,
        ⟨4447, false, false, [], [1, 15, 13]⟩,
        ⟨4556, false, false, [], [1, 15, 13]⟩,
        ⟨4447, false, false, [], [1, 15, 13]⟩,
        ⟨4447, false, false, [], [1, 15, 13]⟩,
        ⟨4443, true, false, [], [1, 15, 13]⟩,
        ⟨18, false, false, [77781], [15, 13]⟩,
        ⟨4444, false, false, [], [15, 13]⟩,
        ⟨4557, false, false, [], [15, 13]⟩,
        ⟨4444, false, false, [], [15, 13]⟩,
        ⟨4444, false, false, [], [15, 13]⟩,
        ⟨4440, true, false, [], [15, 13]⟩,
        ⟨3, false, false, [77779], [13]⟩,
        ⟨4441, false, false, [], [13]⟩,
        ⟨4558, false, false, [], [13]⟩,
        ⟨4441, false, false, [], [13]⟩,
        ⟨4441, false, false, [], [13]⟩,
        ⟨4437, true, false, [], [13]⟩,
        ⟨98, false, false, [77777], []⟩,
        ⟨4438, false, false, [], []⟩,
        ⟨4559, false, false, [], []⟩,
        ⟨4438, false, false, [], []⟩,
        ⟨4438, false, false, [], []⟩
      ]⟩,
    ⟨[77775], [77775], .contexts []⟩,
    ⟨[77773], [77773], .contexts []⟩,
    ⟨[77771], [77771], .contexts []⟩,
    ⟨[77769], [77769], .contexts []⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1
    ], [77769], .contexts [
        ⟨4560, false, false, [], [1, 11, 9, 1]⟩,
        ⟨4434, true, false, [], [1, 11, 9, 1]⟩,
        ⟨18, false, false, [77775], [11, 9, 1]⟩,
        ⟨4435, false, false, [], [11, 9, 1]⟩,
        ⟨4561, false, false, [], [11, 9, 1]⟩,
        ⟨4435, false, false, [], [11, 9, 1]⟩,
        ⟨4435, false, false, [], [11, 9, 1]⟩,
        ⟨4431, true, false, [], [11, 9, 1]⟩,
        ⟨90, false, false, [77773], [9, 1]⟩,
        ⟨4432, false, false, [], [9, 1]⟩,
        ⟨4562, false, false, [], [9, 1]⟩,
        ⟨4432, false, false, [], [9, 1]⟩,
        ⟨4432, false, false, [], [9, 1]⟩,
        ⟨4428, true, false, [], [9, 1]⟩,
        ⟨76, false, false, [77771], [1]⟩,
        ⟨4429, false, false, [], [1]⟩,
        ⟨4563, false, false, [], [1]⟩,
        ⟨4429, false, false, [], [1]⟩,
        ⟨4429, false, false, [], [1]⟩,
        ⟨4425, true, false, [], [1]⟩,
        ⟨18, false, false, [77769], []⟩,
        ⟨4426, false, false, [], []⟩,
        ⟨4564, false, false, [], []⟩,
        ⟨4426, false, false, [], []⟩,
        ⟨4426, false, false, [], []⟩
      ]⟩,
    ⟨[77767], [77767], .contexts []⟩,
    ⟨[77765], [77765], .contexts []⟩,
    ⟨[77763], [77763], .contexts []⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [77761], .contexts [
        ⟨4565, false, false, [], [5, 3, 1, 15]⟩,
        ⟨4422, true, false, [], [5, 3, 1, 15]⟩,
        ⟨49, false, false, [77767], [3, 1, 15]⟩,
        ⟨4423, false, false, [], [3, 1, 15]⟩,
        ⟨4566, false, false, [], [3, 1, 15]⟩,
        ⟨4423, false, false, [], [3, 1, 15]⟩,
        ⟨4423, false, false, [], [3, 1, 15]⟩,
        ⟨4419, true, false, [], [3, 1, 15]⟩,
        ⟨35, false, false, [77765], [1, 15]⟩,
        ⟨4420, false, false, [], [1, 15]⟩,
        ⟨4567, false, false, [], [1, 15]⟩,
        ⟨4420, false, false, [], [1, 15]⟩,
        ⟨4420, false, false, [], [1, 15]⟩,
        ⟨4416, true, false, [], [1, 15]⟩,
        ⟨18, false, false, [77763], [15]⟩,
        ⟨4417, false, false, [], [15]⟩,
        ⟨4568, false, false, [], [15]⟩,
        ⟨4417, false, false, [], [15]⟩,
        ⟨4417, false, false, [], [15]⟩,
        ⟨4413, true, false, [], [15]⟩,
        ⟨3, false, false, [77761], []⟩,
        ⟨4414, false, false, [], []⟩,
        ⟨4414, false, false, [], []⟩,
        ⟨4414, false, false, [], []⟩
      ]⟩,
    ⟨[77759], [77759], .contexts []⟩,
    ⟨[77755], [77755], .contexts []⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9
    ], [77753], .contexts [
        ⟨4569, false, false, [], [13, 1, 11, 9]⟩,
        ⟨4410, true, false, [], [13, 1, 11, 9]⟩,
        ⟨98, false, false, [77759], [1, 11, 9]⟩,
        ⟨4411, false, false, [], [1, 11, 9]⟩,
        ⟨4570, false, false, [], [1, 11, 9]⟩,
        ⟨4411, false, false, [], [1, 11, 9]⟩,
        ⟨4411, false, false, [], [1, 11, 9]⟩,
        ⟨4407, true, false, [], [1, 11, 9]⟩,
        ⟨18, false, false, [77757], [11, 9]⟩,
        ⟨4408, false, false, [], [11, 9]⟩,
        ⟨4408, false, false, [], [11, 9]⟩,
        ⟨4408, false, false, [], [11, 9]⟩,
        ⟨4404, true, false, [], [11, 9]⟩,
        ⟨90, false, false, [77755], [9]⟩,
        ⟨4405, false, false, [], [9]⟩,
        ⟨4571, false, false, [], [9]⟩,
        ⟨4405, false, false, [], [9]⟩,
        ⟨4405, false, false, [], [9]⟩,
        ⟨4401, true, false, [], [9]⟩,
        ⟨76, false, false, [77753], []⟩,
        ⟨4402, false, false, [], []⟩,
        ⟨4402, false, false, [], []⟩,
        ⟨4402, false, false, [], []⟩
      ]⟩,
    ⟨[77751], [77751], .contexts []⟩,
    ⟨[77749], [77749], .contexts []⟩,
    ⟨[77747], [77747], .contexts []⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1
    ], [77745], .contexts [
        ⟨4572, false, false, [], [1, 5, 3, 1]⟩,
        ⟨4398, true, false, [], [1, 5, 3, 1]⟩,
        ⟨18, false, false, [77751], [5, 3, 1]⟩,
        ⟨4399, false, false, [], [5, 3, 1]⟩,
        ⟨4573, false, false, [], [5, 3, 1]⟩,
        ⟨4399, false, false, [], [5, 3, 1]⟩,
        ⟨4399, false, false, [], [5, 3, 1]⟩,
        ⟨4395, true, false, [], [5, 3, 1]⟩,
        ⟨49, false, false, [77749], [3, 1]⟩,
        ⟨4396, false, false, [], [3, 1]⟩,
        ⟨4574, false, false, [], [3, 1]⟩,
        ⟨4396, false, false, [], [3, 1]⟩,
        ⟨4396, false, false, [], [3, 1]⟩,
        ⟨4392, true, false, [], [3, 1]⟩,
        ⟨35, false, false, [77747], [1]⟩,
        ⟨4393, false, false, [], [1]⟩,
        ⟨4575, false, false, [], [1]⟩,
        ⟨4393, false, false, [], [1]⟩,
        ⟨4393, false, false, [], [1]⟩,
        ⟨4390, true, false, [], [1]⟩,
        ⟨18, false, false, [77745], []⟩,
        ⟨4386, false, false, [], []⟩,
        ⟨4385, false, false, [], []⟩,
        ⟨4386, false, false, [], []⟩,
        ⟨4386, false, false, [], []⟩
      ]⟩,
    ⟨[77743], [77743], .contexts []⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [77737], .contexts [
        ⟨4576, false, false, [], [15, 13, 1, 11]⟩,
        ⟨4383, true, false, [], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [77743], [13, 1, 11]⟩,
        ⟨4384, false, false, [], [13, 1, 11]⟩,
        ⟨4577, false, false, [], [13, 1, 11]⟩,
        ⟨4384, false, false, [], [13, 1, 11]⟩,
        ⟨4384, false, false, [], [13, 1, 11]⟩,
        ⟨4381, true, false, [], [13, 1, 11]⟩,
        ⟨98, false, false, [77741], [1, 11]⟩,
        ⟨4377, false, false, [], [1, 11]⟩,
        ⟨4376, false, false, [], [1, 11]⟩,
        ⟨4377, false, false, [], [1, 11]⟩,
        ⟨4377, false, false, [], [1, 11]⟩,
        ⟨4375, true, false, [], [1, 11]⟩,
        ⟨18, false, false, [77739], [11]⟩,
        ⟨4373, false, false, [], [11]⟩,
        ⟨4372, false, false, [], [11]⟩,
        ⟨4373, false, false, [], [11]⟩,
        ⟨4373, false, false, [], [11]⟩,
        ⟨4371, true, false, [], [11]⟩,
        ⟨90, false, false, [77737], []⟩,
        ⟨4367, false, false, [], []⟩,
        ⟨4366, false, false, [], []⟩,
        ⟨4367, false, false, [], []⟩,
        ⟨4367, false, false, [], []⟩
      ]⟩,
    ⟨[77731, 3], [77729], .contexts [
        ⟨4315, false, false, [], []⟩
      ]⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3
    ], [77729], .contexts [
        ⟨4578, false, false, [], [9, 1, 5, 3]⟩,
        ⟨4365, true, false, [], [9, 1, 5, 3]⟩,
        ⟨76, false, false, [77735], [1, 5, 3]⟩,
        ⟨4356, false, false, [], [1, 5, 3]⟩,
        ⟨4355, false, false, [], [1, 5, 3]⟩,
        ⟨4356, false, false, [], [1, 5, 3]⟩,
        ⟨4356, false, false, [], [1, 5, 3]⟩,
        ⟨4354, false, false, [], [5, 3]⟩,
        ⟨4336, false, false, [], [5, 3]⟩,
        ⟨4337, false, false, [], [5, 3]⟩,
        ⟨4337, false, false, [], [5, 3]⟩,
        ⟨4334, true, false, [], [5, 3]⟩,
        ⟨49, false, false, [77731], [3]⟩,
        ⟨4317, false, false, [], [3]⟩,
        ⟨4316, false, false, [], [3]⟩,
        ⟨4317, false, false, [], [3]⟩,
        ⟨4317, false, false, [], [3]⟩,
        ⟨4579, false, false, [], []⟩,
        ⟨4294, false, false, [], []⟩,
        ⟨4295, false, false, [], []⟩,
        ⟨4295, false, false, [], []⟩
      ]⟩,
    ⟨[77729, 1], [77727], .contexts [
        ⟨4293, false, false, [], []⟩
      ]⟩,
    ⟨[865], [863, 145], .source 497⟩,
    ⟨[867], [865, 151], .source 498⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11
    ], [867, 77725], .contexts [
        ⟨4580, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨4581, false, false, [], [15, 13, 1, 11]⟩,
        ⟨4270, false, false, [], [15, 13, 1, 11]⟩,
        ⟨4271, false, false, [], [15, 13, 1, 11]⟩,
        ⟨4271, false, false, [], [15, 13, 1, 11]⟩,
        ⟨4306, false, false, [], [13, 1, 11]⟩,
        ⟨4307, false, false, [], [13, 1, 11]⟩,
        ⟨4308, false, false, [], [13, 1, 11]⟩,
        ⟨4308, false, false, [], [13, 1, 11]⟩,
        ⟨4269, false, false, [863], [1, 11]⟩,
        ⟨4253, false, false, [863], [11]⟩,
        ⟨4582, true, false, [], [77725, 11]⟩,
        ⟨4266, false, false, [865], []⟩,
        ⟨4583, true, false, [], [77725]⟩
      ]⟩,
    ⟨[869], [867, 135], .source 499⟩,
    ⟨[871], [869, 145], .source 500⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [871, 77719], .contexts [
        ⟨4584, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨4261, false, false, [867], [1, 5, 3, 1]⟩,
        ⟨4585, true, false, [], [77725, 1, 5, 3, 1]⟩,
        ⟨4253, false, false, [869], [5, 3, 1]⟩,
        ⟨4586, true, false, [], [77725, 5, 3, 1]⟩,
        ⟨4246, true, false, [871], [5, 3, 1]⟩,
        ⟨49, false, false, [871, 77723], [3, 1]⟩,
        ⟨4228, false, false, [871], [3, 1]⟩,
        ⟨4225, false, false, [871], [1]⟩,
        ⟨4202, false, false, [871], []⟩
      ]⟩,
    ⟨[873], [871, 419], .source 501⟩,
    ⟨[875], [873, 387], .source 502⟩,
    ⟨[877], [875, 415], .source 503⟩,
    ⟨[879], [877, 383], .source 504⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9
    ], [879, 77361], .contexts [
        ⟨4587, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨4167, false, false, [871], [13, 1, 11, 9]⟩,
        ⟨2444, false, false, [871], [1, 11, 9]⟩,
        ⟨4588, true, false, [], [77475, 1, 11, 9]⟩,
        ⟨2295, false, false, [873], [11, 9]⟩,
        ⟨2412, false, false, [873], [11, 9]⟩,
        ⟨4589, true, false, [], [77475, 11, 9]⟩,
        ⟨2437, false, false, [875, 412], [9]⟩,
        ⟨2418, false, false, [875, 412], [9]⟩,
        ⟨2439, true, false, [875], [77475, 9]⟩,
        ⟨2439, true, false, [875], [77475, 9]⟩,
        ⟨2438, true, false, [875], [77475, 9]⟩,
        ⟨4590, true, false, [], [77475, 9]⟩,
        ⟨2406, false, false, [877], []⟩,
        ⟨4591, true, false, [], [77361]⟩
      ]⟩,
    ⟨[881], [879, 111], .source 505⟩,
    ⟨[883], [881, 23], .source 506⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [883, 13, 77113], .contexts [
        ⟨4592, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨1821, false, false, [879], [5, 3, 1, 15]⟩,
        ⟨1129, false, false, [879], [3, 1, 15]⟩,
        ⟨4593, true, false, [], [77111, 3, 1, 15]⟩,
        ⟨332, true, false, [881], [3, 1, 15]⟩,
        ⟨335, false, false, [881, 77109], [1, 15]⟩,
        ⟨336, false, false, [881, 77109], [1, 15]⟩,
        ⟨333, false, false, [881], [11, 1, 15]⟩,
        ⟨328, false, false, [881, 5], [1, 15]⟩,
        ⟨337, false, false, [881, 5], [1, 15]⟩,
        ⟨53, true, false, [881], [77111, 1, 15]⟩,
        ⟨749, true, false, [881], [77111, 1, 15]⟩,
        ⟨4594, true, false, [], [77111, 1, 15]⟩,
        ⟨363, false, false, [883], [15]⟩,
        ⟨372, false, false, [883], []⟩
      ]⟩,
    ⟨[885], [883, 31], .source 507⟩,
    ⟨[887], [885, 19], .source 508⟩,
    ⟨[889], [887, 211], .source 509⟩,
    ⟨[891], [889, 217], .source 510⟩,
    ⟨[
      77849, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1
    ], [891, 77481, 1], .contexts [
        ⟨4595, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨740, true, false, [883], [77113, 13, 1, 11, 9, 1]⟩,
        ⟨4596, true, false, [], [77113, 13, 1, 11, 9, 1]⟩,
        ⟨374, false, false, [885], [1, 11, 9, 1]⟩,
        ⟨393, false, false, [885], [11, 9, 1]⟩,
        ⟨735, true, false, [885], [77115, 11, 9, 1]⟩,
        ⟨4597, true, false, [], [77115, 11, 9, 1]⟩,
        ⟨2608, false, false, [887], [9, 1]⟩,
        ⟨4598, true, false, [], [77481, 9, 1]⟩,
        ⟨2603, false, false, [889], [1]⟩,
        ⟨4599, true, false, [], [77481, 1]⟩
      ]⟩,
    ⟨[893], [891, 479], .source 511⟩,
    ⟨[895], [893, 483], .source 512⟩,
    ⟨[897], [895, 145], .source 513⟩,
    ⟨[899], [897, 135], .source 514⟩,
    ⟨[77851, 15], [77851, 15], .contexts []⟩,
    ⟨[77851, 15], [899, 77217], .contexts [
        ⟨4605, false, false, [], []⟩,
        ⟨4534, true, false, [], [15]⟩,
        ⟨4534, true, false, [], [15]⟩,
        ⟨4532, true, false, [], [15]⟩,
        ⟨4009, false, false, [77849], []⟩,
        ⟨4017, false, false, [77849], []⟩,
        ⟨4600, false, false, [], [5, 3, 1]⟩,
        ⟨2588, false, false, [891], [5, 3, 1]⟩,
        ⟨4601, true, false, [], [77481, 5, 3, 1]⟩,
        ⟨2598, false, false, [893], [3, 1]⟩,
        ⟨4602, true, false, [], [77217, 3, 1]⟩,
        ⟨960, false, false, [895], [1]⟩,
        ⟨4603, true, false, [], [77217, 1]⟩,
        ⟨599, false, false, [897], []⟩,
        ⟨954, false, false, [897], []⟩,
        ⟨4604, true, false, [], [77217]⟩,
        ⟨2597, false, false, [899], []⟩
      ]⟩,
    ⟨[77851, 15], [899, 77217], .contexts [
        ⟨4606, false, false, [], []⟩,
        ⟨24, true, false, [], [899, 77217]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 072. -/
def y322TCContextRaw072 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[901], [898], .source 515⟩,
    ⟨[77217, 15], [901, 77851], .contexts [
        ⟨4607, true, false, [898], [15]⟩,
        ⟨3, false, false, [898, 77851], []⟩,
        ⟨4608, true, false, [], [77851]⟩
      ]⟩,
    ⟨[899, 77217], [899, 77217], .contexts []⟩,
    ⟨[903], [899, 137], .source 516⟩,
    ⟨[905], [903, 109], .source 517⟩,
    ⟨[907], [905, 135], .source 518⟩,
    ⟨[77849, 15], [77849, 15], .contexts []⟩,
    ⟨[77849, 15], [907, 77217], .contexts [
        ⟨4614, false, false, [], []⟩,
        ⟨4533, true, false, [], [15]⟩,
        ⟨4533, true, false, [], [15]⟩,
        ⟨4533, true, false, [], [15]⟩,
        ⟨98, true, false, [77849], [15]⟩,
        ⟨4532, false, false, [], [13, 15]⟩,
        ⟨148, false, false, [77851], []⟩,
        ⟨150, false, false, [77851], []⟩,
        ⟨4605, false, false, [], [13, 15, 13]⟩,
        ⟨4607, false, false, [], [13, 15, 13]⟩,
        ⟨4610, false, false, [], [13, 15, 13]⟩,
        ⟨4610, false, false, [], [13, 15, 13]⟩,
        ⟨948, false, false, [899], [15, 13]⟩,
        ⟨4611, true, false, [], [77221, 15, 13]⟩,
        ⟨606, false, false, [903], [13]⟩,
        ⟨917, false, false, [903], [13]⟩,
        ⟨4612, true, false, [], [77221, 13]⟩,
        ⟨604, false, false, [905], []⟩,
        ⟨954, false, false, [905], []⟩,
        ⟨4613, true, false, [], [77217]⟩,
        ⟨2597, false, false, [907], []⟩
      ]⟩,
    ⟨[77849, 15], [907, 77217], .contexts [
        ⟨4615, false, false, [], []⟩,
        ⟨24, true, false, [], [907, 77217]⟩
      ]⟩,
    ⟨[909], [906], .source 519⟩,
    ⟨[901, 77851], [901, 77851], .contexts []⟩,
    ⟨[911], [899, 909], .source 520⟩,
    ⟨[907, 77217], [907, 77217], .contexts []⟩,
    ⟨[907, 77217], [907, 77217], .contexts []⟩,
    ⟨[913], [907, 135], .source 521⟩,
    ⟨[77851], [911, 77849], .contexts [
        ⟨4618, true, false, [900], []⟩,
        ⟨4618, true, false, [900], []⟩,
        ⟨4609, true, false, [900], []⟩,
        ⟨4616, true, false, [900, 906], [15]⟩,
        ⟨3, false, false, [900, 906, 77849], []⟩,
        ⟨4617, true, false, [900], [77849]⟩,
        ⟨4608, false, true, [], [909, 77849]⟩,
        ⟨4619, true, false, [], [77849]⟩
      ]⟩,
    ⟨[915], [901, 911], .source 522⟩,
    ⟨[917], [913, 915], .source 523⟩,
    ⟨[917, 77847], [917, 77847], .contexts []⟩,
    ⟨[77849], [917, 77847], .contexts [
        ⟨16, true, false, [77849], []⟩,
        ⟨4614, false, false, [], [1, 15, 1]⟩,
        ⟨4616, false, false, [], [1, 15, 1]⟩,
        ⟨4620, false, false, [], [1, 15, 1]⟩,
        ⟨4621, false, false, [], [1, 15, 1]⟩,
        ⟨4621, false, false, [], [1, 15, 1]⟩,
        ⟨599, false, false, [907], [15, 1]⟩,
        ⟨954, false, false, [907], [15, 1]⟩,
        ⟨4622, true, false, [], [77217, 15, 1]⟩,
        ⟨4609, false, false, [913], [1]⟩,
        ⟨4623, false, false, [913, 901], [1]⟩,
        ⟨4624, true, false, [913], [77849, 1]⟩,
        ⟨4625, true, false, [], [77849, 1]⟩,
        ⟨4530, false, false, [917], []⟩,
        ⟨4626, false, false, [], []⟩
      ]⟩,
    ⟨[919], [911, 917], .source 524⟩,
    ⟨[77851], [919, 77847], .contexts [
        ⟨4623, false, false, [], []⟩,
        ⟨4627, false, false, [911], []⟩,
        ⟨4628, true, false, [], [77847]⟩
      ]⟩,
    ⟨[921], [916], .source 525⟩,
    ⟨[925], [921, 907], .source 527⟩,
    ⟨[77847, 15], [925, 77217], .contexts [
        ⟨4627, true, false, [916], [15]⟩,
        ⟨4616, false, false, [916], []⟩,
        ⟨4620, false, false, [916], []⟩,
        ⟨4630, true, false, [], [907, 77217]⟩,
        ⟨4631, true, false, [], [77217]⟩
      ]⟩,
    ⟨[925, 77217], [925, 77217], .contexts []⟩,
    ⟨[77847, 15], [925, 77217], .contexts [
        ⟨4632, false, false, [], []⟩,
        ⟨4633, false, false, [], []⟩,
        ⟨4633, false, false, [], []⟩
      ]⟩,
    ⟨[927], [925, 145], .source 528⟩,
    ⟨[929], [901, 919], .source 529⟩,
    ⟨[931], [927, 929], .source 530⟩,
    ⟨[77847], [77847], .contexts []⟩,
    ⟨[77847], [77847], .contexts []⟩,
    ⟨[933], [930], .source 531⟩,
    ⟨[930], [930], .contexts []⟩,
    ⟨[77847, 3], [933, 77847], .contexts [
        ⟨4637, false, false, [930], [77847, 3]⟩,
        ⟨4636, false, false, [930, 927], [77847, 3]⟩,
        ⟨4629, true, false, [930, 927, 901], [3]⟩,
        ⟨4609, true, false, [930, 927], [3]⟩,
        ⟨4635, false, false, [930], [77217, 15, 3]⟩,
        ⟨960, true, false, [930, 925], [15, 3]⟩,
        ⟨4634, true, false, [930], [3, 15, 3]⟩,
        ⟨1555, false, false, [930, 77847], []⟩,
        ⟨4638, false, false, [930], []⟩,
        ⟨4639, false, false, [930], []⟩,
        ⟨4641, true, false, [], [77847]⟩,
        ⟨4641, true, false, [], [77847]⟩,
        ⟨4640, true, false, [], [77847]⟩
      ]⟩,
    ⟨[15, 9, 15, 9], [], .contexts [
        ⟨74, false, false, [], []⟩
      ]⟩,
    ⟨[925, 77363], [925, 77363], .contexts []⟩,
    ⟨[925, 77363], [925, 77363], .contexts []⟩,
    ⟨[947], [924], .source 538⟩,
    ⟨[947], [924], .contexts [
        ⟨4646, false, false, [], []⟩
      ]⟩,
    ⟨[924], [924], .contexts []⟩,
    ⟨[925], [946], .contexts [
        ⟨4646, true, true, [], []⟩
      ]⟩,
    ⟨[77845], [925, 77363], .contexts [
        ⟨4526, true, false, [], []⟩,
        ⟨4526, true, false, [], []⟩,
        ⟨4536, true, false, [], []⟩,
        ⟨4535, true, false, [], []⟩,
        ⟨4647, false, false, [946], [77847, 11]⟩,
        ⟨4648, false, false, [946], [77847, 11]⟩,
        ⟨4648, false, false, [946], [77847, 11]⟩,
        ⟨4639, true, false, [946, 924], [11]⟩,
        ⟨4638, true, false, [946, 924], [11]⟩,
        ⟨4051, true, false, [946, 924, 77847], [11]⟩,
        ⟨4634, false, false, [946, 924], [11, 15, 11, 11]⟩,
        ⟨597, false, false, [946], [15, 11, 11]⟩,
        ⟨1913, false, false, [946], [11, 11]⟩,
        ⟨4644, false, false, [946, 924], [11, 11]⟩,
        ⟨4645, false, false, [946, 924], [11, 11]⟩,
        ⟨90, false, false, [946, 77363], []⟩,
        ⟨4649, true, false, [], [77363]⟩
      ]⟩,
    ⟨[925, 77719], [925, 77719], .contexts []⟩,
    ⟨[947], [924], .contexts [
        ⟨4647, false, false, [], []⟩,
        ⟨24, false, false, [924], []⟩
      ]⟩,
    ⟨[77843], [925, 77719], .contexts [
        ⟨4652, false, false, [946], [77843]⟩,
        ⟨4537, true, false, [946, 924], []⟩,
        ⟨4524, true, false, [946, 924], []⟩,
        ⟨4650, false, false, [946, 924], [9]⟩,
        ⟨4644, false, false, [946, 924], [9]⟩,
        ⟨4645, false, false, [946, 924], [9]⟩,
        ⟨4187, false, false, [946], []⟩,
        ⟨4651, false, false, [946, 924], []⟩,
        ⟨4649, true, false, [], [77719]⟩
      ]⟩,
    ⟨[925, 77721], [925, 77721], .contexts []⟩,
    ⟨[949], [925, 293], .source 539⟩,
    ⟨[77245], [948, 77839], .contexts [
        ⟨4655, false, false, [948], [77245]⟩,
        ⟨4208, true, false, [948, 925], []⟩,
        ⟨4654, true, false, [948], [5]⟩,
        ⟨4649, false, false, [948], [77721, 5]⟩,
        ⟨4654, true, false, [948, 946, 924], [5]⟩,
        ⟨4201, true, false, [948, 946], [5]⟩,
        ⟨4651, true, false, [948, 946, 924], [1, 5]⟩,
        ⟨4653, true, false, [948, 946, 924], [1, 5]⟩,
        ⟨4521, false, false, [948, 946, 924], [5]⟩,
        ⟨4538, false, false, [948, 946, 924], [5]⟩,
        ⟨4652, true, false, [948, 946], [77841, 5]⟩,
        ⟨4518, false, false, [948], []⟩,
        ⟨4539, false, false, [948], []⟩
      ]⟩,
    ⟨[951], [948], .source 540⟩,
    ⟨[951], [948], .contexts [
        ⟨4657, false, false, [], []⟩,
        ⟨24, false, false, [948], []⟩
      ]⟩,
    ⟨[949], [950], .contexts [
        ⟨4657, true, true, [], []⟩
      ]⟩,
    ⟨[949, 77247], [949, 77247], .contexts []⟩,
    ⟨[77837, 1], [949, 295, 77203], .contexts [
        ⟨4658, false, false, [950], [77837, 1]⟩,
        ⟨4541, true, false, [950, 948], [1]⟩,
        ⟨4515, true, false, [950, 948], [1]⟩,
        ⟨4658, false, false, [950, 948, 950], [77839, 3, 1]⟩,
        ⟨4656, true, false, [950, 948, 950], [3, 1]⟩,
        ⟨4659, true, false, [950, 948], [77245, 3, 1]⟩,
        ⟨1186, false, false, [950], [1]⟩,
        ⟨4660, false, false, [950, 948], [1]⟩,
        ⟨4659, true, false, [], [77247, 1]⟩,
        ⟨4660, false, false, [], [1]⟩,
        ⟨1902, false, false, [949], []⟩
      ]⟩,
    ⟨[953], [949, 295], .source 541⟩,
    ⟨[955], [952], .source 542⟩,
    ⟨[955], [952], .contexts [
        ⟨4663, false, false, [], []⟩
      ]⟩,
    ⟨[955], [952], .contexts [
        ⟨4664, false, false, [], []⟩,
        ⟨24, false, false, [952], []⟩
      ]⟩,
    ⟨[953], [954], .contexts [
        ⟨4663, true, true, [], []⟩
      ]⟩,
    ⟨[77833], [953, 77205], .contexts [
        ⟨4665, false, false, [954], [77833]⟩,
        ⟨4543, true, false, [954, 952], []⟩,
        ⟨4509, true, false, [954, 952], []⟩,
        ⟨4665, false, false, [954, 952, 954], [77835, 15]⟩,
        ⟨4542, true, false, [954, 952, 954, 952], [15]⟩,
        ⟨4512, true, false, [954, 952, 954, 952], [15]⟩,
        ⟨4661, false, false, [954, 952, 954, 952], [15]⟩,
        ⟨4662, true, false, [954, 952, 954, 952], [77203, 15]⟩,
        ⟨4666, true, false, [954, 952], [77203, 15]⟩,
        ⟨572, false, false, [954], []⟩,
        ⟨4666, true, false, [], [77205]⟩
      ]⟩,
    ⟨[952], [952], .contexts []⟩,
    ⟨[77205, 13], [955, 77831], .contexts [
        ⟨4667, true, false, [952], [13]⟩,
        ⟨4506, false, false, [952], []⟩,
        ⟨4544, false, false, [952], []⟩,
        ⟨4668, true, false, [], [77831]⟩,
        ⟨4668, true, false, [], [77831]⟩,
        ⟨4664, true, false, [], [77831]⟩
      ]⟩,
    ⟨[543, 77497], [543, 77497], .contexts []⟩,
    ⟨[957], [543, 765], .source 543⟩]

/-- Exact literal claimed equations and contextual derivations, block 073. -/
def y322TCContextRaw073 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77205, 13], [955, 77831], .contexts [
        ⟨4669, false, false, [], []⟩
      ]⟩,
    ⟨[955, 77831], [955, 77831], .contexts []⟩,
    ⟨[955, 77831], [955, 77831], .contexts []⟩,
    ⟨[959], [956], .source 544⟩,
    ⟨[961], [959, 955], .source 545⟩,
    ⟨[77611, 15], [961, 77831], .contexts [
        ⟨4671, false, false, [956], [77611, 15]⟩,
        ⟨3679, true, false, [956, 543], [15]⟩,
        ⟨4670, true, false, [956], [13, 15]⟩,
        ⟨4670, true, false, [956], [13, 15]⟩,
        ⟨2979, true, false, [956], [13, 15]⟩,
        ⟨1059, true, false, [956], [15, 13, 15]⟩,
        ⟨3449, false, false, [956, 77203], []⟩,
        ⟨149, false, false, [956, 77203], []⟩,
        ⟨572, false, false, [956], [13]⟩,
        ⟨646, false, false, [956], [13]⟩,
        ⟨577, false, false, [956], [13]⟩,
        ⟨577, false, false, [956], [13]⟩,
        ⟨4672, false, false, [956], []⟩,
        ⟨4673, false, false, [956], []⟩,
        ⟨4674, false, false, [956], []⟩,
        ⟨4674, false, false, [956], []⟩,
        ⟨4675, true, false, [], [955, 77831]⟩,
        ⟨4676, true, false, [], [77831]⟩
      ]⟩,
    ⟨[963], [960], .source 546⟩,
    ⟨[305, 77207], [305, 77207], .contexts []⟩,
    ⟨[965], [305, 955], .source 547⟩,
    ⟨[965, 77829], [965, 77829], .contexts []⟩,
    ⟨[77205, 1, 13, 1, 13, 1], [965, 77829], .contexts [
        ⟨576, false, false, [], [13, 1, 13, 1]⟩,
        ⟨644, false, false, [], [13, 1, 13, 1]⟩,
        ⟨580, false, false, [], [13, 1, 13, 1]⟩,
        ⟨580, false, false, [], [13, 1, 13, 1]⟩,
        ⟨1885, false, false, [], [1, 13, 1]⟩,
        ⟨4679, false, false, [], [1, 13, 1]⟩,
        ⟨4679, false, false, [], [1, 13, 1]⟩,
        ⟨578, false, false, [305], [13, 1]⟩,
        ⟨4669, false, false, [305], [1]⟩,
        ⟨4680, true, false, [], [77831, 1]⟩,
        ⟨4503, false, false, [965], []⟩,
        ⟨4681, false, false, [], []⟩
      ]⟩,
    ⟨[77205], [77205], .contexts []⟩,
    ⟨[967], [964], .source 548⟩,
    ⟨[964], [964], .contexts []⟩,
    ⟨[77205, 13], [955, 77831], .contexts [
        ⟨4672, false, false, [], []⟩
      ]⟩,
    ⟨[969], [953, 965], .source 549⟩,
    ⟨[77831], [969, 77829], .contexts [
        ⟨4674, true, false, [954], []⟩,
        ⟨4674, true, false, [954], []⟩,
        ⟨4673, true, false, [954], []⟩,
        ⟨4686, true, false, [954], []⟩,
        ⟨4684, false, false, [954, 966], [77205, 13]⟩,
        ⟨4685, false, false, [954, 966], [77205, 13]⟩,
        ⟨4685, false, false, [954, 966], [77205, 13]⟩,
        ⟨1050, true, false, [954, 966, 964], [13]⟩,
        ⟨4683, true, false, [954, 966, 964], [13]⟩,
        ⟨944, true, false, [954, 966, 964, 77205], [13]⟩,
        ⟨4682, false, false, [954, 966, 964], [13, 13]⟩,
        ⟨98, false, false, [954, 966, 77829], []⟩,
        ⟨4684, false, true, [954], [77829]⟩,
        ⟨4681, false, false, [954], []⟩,
        ⟨4666, true, false, [], [965, 77829]⟩,
        ⟨4687, true, false, [], [77829]⟩
      ]⟩,
    ⟨[971], [968], .source 550⟩,
    ⟨[973], [971, 963], .source 551⟩,
    ⟨[77831], [969, 77829], .contexts [
        ⟨4688, false, false, [], []⟩
      ]⟩,
    ⟨[975], [955, 969], .source 552⟩,
    ⟨[977], [151, 975], .source 553⟩,
    ⟨[977, 77827], [977, 77827], .contexts []⟩,
    ⟨[77827, 13], [77827, 13], .contexts []⟩,
    ⟨[979], [976], .source 554⟩,
    ⟨[976], [976], .contexts []⟩,
    ⟨[77827, 13], [979, 77205], .contexts [
        ⟨4695, false, false, [], []⟩,
        ⟨4694, true, false, [976], [13]⟩,
        ⟨4499, true, false, [], [13]⟩,
        ⟨4693, false, false, [976], [77829, 11, 13]⟩,
        ⟨4692, false, false, [976, 151], [77829, 11, 13]⟩,
        ⟨4691, true, false, [976, 151, 955], [11, 13]⟩,
        ⟨4669, true, false, [976, 151], [11, 13]⟩,
        ⟨1053, true, false, [976], [13, 11, 13]⟩,
        ⟨1836, false, false, [976, 77205], []⟩,
        ⟨4683, false, false, [976], []⟩,
        ⟨1050, false, false, [976], []⟩,
        ⟨4697, true, false, [], [77205]⟩,
        ⟨4697, true, false, [], [77205]⟩,
        ⟨4696, true, false, [], [77205]⟩
      ]⟩,
    ⟨[981], [974], .source 555⟩,
    ⟨[983], [981, 977], .source 556⟩,
    ⟨[77829], [983, 77827], .contexts [
        ⟨4692, false, false, [974], [77829]⟩,
        ⟨4691, true, false, [974, 955], []⟩,
        ⟨4686, true, false, [974], []⟩,
        ⟨4698, true, false, [974, 978], [13]⟩,
        ⟨98, false, false, [974, 978, 77827], []⟩,
        ⟨4696, false, true, [974], [77827]⟩,
        ⟨4694, false, false, [974], []⟩,
        ⟨4699, true, false, [], [977, 77827]⟩,
        ⟨4700, true, false, [], [77827]⟩
      ]⟩,
    ⟨[985], [969, 983], .source 557⟩,
    ⟨[77831], [985, 77827], .contexts [
        ⟨4691, false, false, [], []⟩,
        ⟨4701, false, false, [969], []⟩,
        ⟨4702, true, false, [], [77827]⟩
      ]⟩,
    ⟨[987], [982], .source 558⟩,
    ⟨[989], [987, 985], .source 559⟩,
    ⟨[991], [987, 973], .source 560⟩,
    ⟨[631, 77601], [631, 77601], .contexts []⟩,
    ⟨[993], [631, 683], .source 561⟩,
    ⟨[995], [955, 985], .source 562⟩,
    ⟨[77205, 13], [995, 77827], .contexts [
        ⟨4686, false, false, [], []⟩,
        ⟨4703, false, false, [955], []⟩,
        ⟨4709, true, false, [], [77827]⟩
      ]⟩,
    ⟨[77205, 12], [77205, 13], .contexts [
        ⟨108, false, false, [77205], []⟩
      ]⟩,
    ⟨[77827], [77827], .contexts []⟩,
    ⟨[997], [992], .source 563⟩,
    ⟨[999], [997, 995], .source 564⟩,
    ⟨[77461, 3], [999, 77827], .contexts [
        ⟨4708, false, false, [992], [77461, 3]⟩,
        ⟨3341, true, false, [992, 631], [3]⟩,
        ⟨4707, true, false, [992], [13, 3]⟩,
        ⟨4707, true, false, [992], [13, 3]⟩,
        ⟨3263, true, false, [992], [13, 3]⟩,
        ⟨932, false, false, [992, 77205], []⟩,
        ⟨4711, false, false, [992], []⟩,
        ⟨4710, false, false, [992], []⟩,
        ⟨4712, false, false, [992, 995], []⟩,
        ⟨4713, true, false, [], [995, 77827]⟩,
        ⟨4714, true, false, [], [77827]⟩
      ]⟩,
    ⟨[705, 77333], [705, 77333], .contexts []⟩,
    ⟨[1003], [705, 719], .source 566⟩,
    ⟨[1005], [1002], .source 567⟩,
    ⟨[1007], [1005, 995], .source 568⟩,
    ⟨[1009], [1006], .source 569⟩,
    ⟨[77827, 9], [77825], .contexts [
        ⟨4546, false, false, [], []⟩
      ]⟩,
    ⟨[77825], [1009, 77453], .contexts [
        ⟨4495, true, false, [], []⟩,
        ⟨4495, true, false, [], []⟩,
        ⟨4547, true, false, [], []⟩,
        ⟨4721, true, false, [], []⟩,
        ⟨4719, false, false, [1006], [77827, 9]⟩,
        ⟨4718, false, false, [1006], [995, 77827, 9]⟩,
        ⟨4712, true, false, [1006, 1002, 995], [9]⟩,
        ⟨4710, true, false, [1006, 1002], [9]⟩,
        ⟨4711, true, false, [1006, 1002], [9]⟩,
        ⟨926, true, false, [1006, 1002, 77205], [9]⟩,
        ⟨3369, false, false, [1006, 1002], [13, 9, 9]⟩,
        ⟨4716, false, false, [1006, 1002], [13, 9, 9]⟩,
        ⟨4716, false, false, [1006, 1002], [13, 9, 9]⟩,
        ⟨3402, false, false, [1006, 1002, 705], [9, 9]⟩,
        ⟨4717, true, false, [1006, 1002], [77453, 9, 9]⟩,
        ⟨76, false, false, [1006, 77453], []⟩,
        ⟨4720, true, false, [], [77453]⟩
      ]⟩,
    ⟨[1009, 77453], [1009, 77453], .contexts []⟩,
    ⟨[77825], [1009, 77453], .contexts [
        ⟨4722, false, false, [], []⟩,
        ⟨4723, false, false, [], []⟩
      ]⟩,
    ⟨[1009, 77453, 1], [1009, 77451], .contexts [
        ⟨2256, false, false, [1009], []⟩
      ]⟩,
    ⟨[1009, 77451], [1009, 77451], .contexts []⟩,
    ⟨[1009, 77451], [1009, 77451], .contexts []⟩,
    ⟨[1009, 77451], [1009, 77451], .contexts []⟩,
    ⟨[1007], [1008], .contexts [
        ⟨4720, true, true, [], []⟩
      ]⟩,
    ⟨[1008], [1008], .contexts []⟩,
    ⟨[77451, 5], [1007, 77821], .contexts [
        ⟨4720, false, false, [1008], [77451, 5]⟩,
        ⟨4728, true, false, [1008, 1006, 1008], [5]⟩,
        ⟨4727, true, false, [1008, 1006, 1008], [5]⟩,
        ⟨4726, true, false, [1008, 1006, 1008], [5]⟩,
        ⟨4725, true, false, [1008, 1006, 1008], [5]⟩,
        ⟨4724, true, false, [1008, 1006, 1008], [1, 5]⟩,
        ⟨4493, false, false, [1008, 1006, 1008], [5]⟩,
        ⟨4548, false, false, [1008, 1006, 1008], [5]⟩,
        ⟨24, true, false, [1008, 1006, 1008], [77823, 5]⟩,
        ⟨4729, true, false, [1008, 1006], [77823, 5]⟩,
        ⟨4490, false, false, [1008], []⟩,
        ⟨4549, false, false, [1008], []⟩,
        ⟨4730, true, false, [], [77821]⟩,
        ⟨4730, true, false, [], [77821]⟩,
        ⟨4729, true, false, [], [77821]⟩
      ]⟩,
    ⟨[989, 77827], [989, 77827], .contexts []⟩,
    ⟨[1011], [989, 1009], .source 570⟩,
    ⟨[1011, 77451, 9], [77827, 1, 9, 1, 9], .contexts [
        ⟨2256, true, false, [1011], [9]⟩,
        ⟨4733, false, false, [], [77453, 1, 9]⟩,
        ⟨4724, true, false, [989], [1, 9]⟩,
        ⟨4496, true, false, [989], [1, 9]⟩,
        ⟨4732, true, false, [], [9, 1, 9]⟩,
        ⟨4732, true, false, [], [9, 1, 9]⟩,
        ⟨4705, false, false, [], [77827, 9, 1, 9]⟩,
        ⟨4704, false, false, [], [985, 77827, 9, 1, 9]⟩,
        ⟨4703, true, false, [982], [9, 1, 9]⟩,
        ⟨4501, true, false, [982], [9, 1, 9]⟩,
        ⟨4701, false, false, [982], [1, 9, 1, 9]⟩
      ]⟩,
    ⟨[77451, 9], [77451, 9], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 074. -/
def y322TCContextRaw074 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1013], [1010], .source 571⟩,
    ⟨[1015], [1013, 1009], .source 572⟩,
    ⟨[77451, 9], [1015, 77451], .contexts [
        ⟨4735, false, false, [], []⟩,
        ⟨4734, false, false, [1010], []⟩,
        ⟨1022, false, false, [1010, 77827], []⟩,
        ⟨787, false, false, [1010, 77827], []⟩,
        ⟨4721, false, false, [1010], [1]⟩,
        ⟨4724, false, false, [1010], [1]⟩,
        ⟨4723, false, false, [1010], [1]⟩,
        ⟨4723, false, false, [1010], [1]⟩,
        ⟨4725, false, false, [1010], []⟩,
        ⟨4726, false, false, [1010], []⟩,
        ⟨4727, false, false, [1010], []⟩,
        ⟨4728, false, false, [1010], []⟩,
        ⟨2744, false, false, [1010, 1009], []⟩,
        ⟨4736, true, false, [], [1009, 77451]⟩,
        ⟨4737, true, false, [], [77451]⟩
      ]⟩,
    ⟨[1015, 77451], [1015, 77451], .contexts []⟩,
    ⟨[1015, 77449], [1015, 77449], .contexts []⟩,
    ⟨[1015, 77449], [1015, 77449], .contexts []⟩,
    ⟨[77449, 9], [77449, 9], .contexts []⟩,
    ⟨[1007, 77821], [1007, 77821], .contexts []⟩,
    ⟨[3, 5, 3, 5], [4, 2], .contexts [
        ⟨1478, false, false, [], [4, 2]⟩
      ]⟩,
    ⟨[1023], [729, 1007], .source 576⟩,
    ⟨[1025], [1022], .source 577⟩,
    ⟨[1027], [1025, 1007], .source 578⟩,
    ⟨[77449, 9], [1015, 77449], .contexts [
        ⟨4742, false, false, [], []⟩,
        ⟨4742, false, false, [], []⟩,
        ⟨2746, true, false, [], [9]⟩,
        ⟨75, false, false, [77451], []⟩,
        ⟨78, false, false, [77451], []⟩,
        ⟨4735, false, false, [], [15]⟩,
        ⟨4738, false, false, [], [15]⟩,
        ⟨4739, false, false, [], [15]⟩,
        ⟨4739, false, false, [], [15]⟩,
        ⟨2252, false, false, [1015], []⟩,
        ⟨4740, false, false, [], []⟩,
        ⟨4741, false, false, [], []⟩,
        ⟨2748, false, false, [1015], []⟩,
        ⟨24, true, false, [], [1015, 77449]⟩,
        ⟨4740, false, false, [], []⟩,
        ⟨4741, false, false, [], []⟩,
        ⟨4741, false, false, [], []⟩
      ]⟩,
    ⟨[77447, 9], [77447, 9], .contexts []⟩,
    ⟨[1033], [1014], .source 581⟩,
    ⟨[1014], [1014], .contexts []⟩,
    ⟨[77447, 9], [1033, 77447], .contexts [
        ⟨4749, false, false, [], []⟩,
        ⟨2248, true, false, [], [9]⟩,
        ⟨4748, true, false, [1014], [13, 9]⟩,
        ⟨926, false, false, [1014, 77449], []⟩,
        ⟨108, false, false, [1014, 77449], []⟩,
        ⟨2321, false, false, [1014], []⟩,
        ⟨2322, false, false, [1014], []⟩,
        ⟨2247, false, false, [1014], []⟩,
        ⟨2247, false, false, [1014], []⟩,
        ⟨2752, false, false, [1014], []⟩,
        ⟨4751, true, false, [], [77447]⟩,
        ⟨4751, true, false, [], [77447]⟩,
        ⟨4750, true, false, [], [77447]⟩
      ]⟩,
    ⟨[77853], [77487, 7], .source 38991⟩,
    ⟨[77487, 7], [77853], .contexts [
        ⟨4753, true, false, [], []⟩
      ]⟩,
    ⟨[77487, 7], [77853], .contexts [
        ⟨4754, false, false, [], []⟩
      ]⟩,
    ⟨[77853], [77853], .contexts []⟩,
    ⟨[77853], [77853], .contexts []⟩,
    ⟨[77713], [77713], .contexts [
        ⟨4130, false, false, [], []⟩
      ]⟩,
    ⟨[77713], [77713], .contexts [
        ⟨1118, true, false, [], [77713]⟩
      ]⟩,
    ⟨[77853, 13], [77713], .contexts [
        ⟨4757, true, false, [], [13]⟩,
        ⟨4757, true, false, [], [13]⟩,
        ⟨4756, true, false, [], [13]⟩,
        ⟨4755, true, false, [], [13]⟩,
        ⟨1785, false, false, [77487], []⟩,
        ⟨1786, false, false, [77487], []⟩,
        ⟨2755, false, false, [], [7]⟩,
        ⟨2677, false, false, [], [7]⟩,
        ⟨2678, false, false, [], [7]⟩,
        ⟨2678, false, false, [], [7]⟩,
        ⟨4126, false, false, [], []⟩,
        ⟨4127, false, false, [], []⟩,
        ⟨4128, false, false, [], []⟩,
        ⟨4128, false, false, [], []⟩,
        ⟨4758, false, false, [], []⟩,
        ⟨4759, false, false, [], []⟩
      ]⟩,
    ⟨[77713, 13], [77853], .contexts [
        ⟨4760, true, false, [], [13]⟩,
        ⟨98, false, false, [77853], []⟩,
        ⟨4757, false, false, [], []⟩
      ]⟩,
    ⟨[77855], [77717, 9], .source 38992⟩,
    ⟨[77717, 9], [77855], .contexts [
        ⟨4762, true, false, [], []⟩
      ]⟩,
    ⟨[77717, 9], [77855], .contexts [
        ⟨4763, false, false, [], []⟩
      ]⟩,
    ⟨[77855], [77855], .contexts []⟩,
    ⟨[77855], [77855], .contexts []⟩,
    ⟨[77717, 9], [77855], .contexts [
        ⟨4764, false, false, [], []⟩,
        ⟨4765, false, false, [], []⟩,
        ⟨4766, false, false, [], []⟩,
        ⟨4766, false, false, [], []⟩
      ]⟩,
    ⟨[77717, 5], [759, 77717], .contexts [
        ⟨4163, false, false, [], []⟩,
        ⟨4163, false, false, [], []⟩,
        ⟨4154, true, false, [], [5]⟩,
        ⟨116, false, false, [77605], []⟩,
        ⟨117, false, false, [77605], []⟩,
        ⟨4141, false, false, [], [13]⟩,
        ⟨4151, false, false, [759], []⟩,
        ⟨4161, false, false, [], []⟩,
        ⟨4162, false, false, [], []⟩,
        ⟨4159, false, false, [759], []⟩,
        ⟨3592, true, false, [], [77717]⟩,
        ⟨4161, false, false, [], []⟩,
        ⟨4162, false, false, [], []⟩,
        ⟨4162, false, false, [], []⟩
      ]⟩,
    ⟨[77855], [77855], .contexts []⟩,
    ⟨[77717, 7], [77115], .contexts [
        ⟨4164, false, false, [], []⟩,
        ⟨4164, false, false, [], []⟩,
        ⟨4154, true, false, [], [7]⟩,
        ⟨124, false, false, [77605], []⟩,
        ⟨125, false, false, [77605], []⟩,
        ⟨4142, false, false, [], [13]⟩,
        ⟨376, false, false, [], []⟩,
        ⟨377, false, false, [], []⟩,
        ⟨378, false, false, [], []⟩,
        ⟨378, false, false, [], []⟩,
        ⟨392, false, false, [], []⟩,
        ⟨1118, true, false, [], [77115]⟩,
        ⟨377, false, false, [], []⟩,
        ⟨378, false, false, [], []⟩,
        ⟨378, false, false, [], []⟩
      ]⟩,
    ⟨[77855, 7], [77855, 7], .contexts []⟩,
    ⟨[77855, 7], [245, 77241], .contexts [
        ⟨4771, false, false, [], []⟩,
        ⟨4767, true, false, [], [7]⟩,
        ⟨1809, false, false, [77717], []⟩,
        ⟨1810, false, false, [77717], []⟩,
        ⟨4770, false, false, [], [9]⟩,
        ⟨1630, false, false, [], []⟩,
        ⟨1599, false, false, [], []⟩,
        ⟨1600, false, false, [], []⟩,
        ⟨1600, false, false, [], []⟩,
        ⟨1605, false, false, [], []⟩,
        ⟨1607, false, false, [], []⟩
      ]⟩,
    ⟨[77241, 7], [243, 77855], .contexts [
        ⟨4772, true, false, [244], [7]⟩,
        ⟨62, false, false, [244, 77855], []⟩,
        ⟨1544, true, false, [], [77855]⟩
      ]⟩,
    ⟨[77717, 13], [77605], .contexts [
        ⟨4151, true, false, [], [13]⟩,
        ⟨98, false, false, [77605], []⟩,
        ⟨3578, false, false, [], []⟩,
        ⟨3577, false, false, [], []⟩,
        ⟨3578, false, false, [], []⟩,
        ⟨3578, false, false, [], []⟩
      ]⟩,
    ⟨[1041], [245, 245], .source 585⟩,
    ⟨[1043], [1041, 243], .source 586⟩,
    ⟨[7, 11, 7, 11], [], .contexts [
        ⟨985, false, false, [], []⟩
      ]⟩,
    ⟨[1045], [1042], .source 587⟩,
    ⟨[1042], [1042], .contexts []⟩,
    ⟨[77855, 11], [1045, 77855], .contexts [
        ⟨4776, false, false, [1042], [77855, 11]⟩,
        ⟨4773, true, false, [1042, 1041], [11]⟩,
        ⟨4775, false, false, [1042], [77241, 7, 11]⟩,
        ⟨1612, true, false, [1042, 245], [7, 11]⟩,
        ⟨1600, true, false, [1042], [11, 7, 11]⟩,
        ⟨1600, true, false, [1042], [11, 7, 11]⟩,
        ⟨1599, true, false, [1042], [11, 7, 11]⟩,
        ⟨4772, true, false, [1042], [11, 7, 11]⟩,
        ⟨4771, true, false, [1042], [11, 7, 11]⟩,
        ⟨4777, false, false, [1042, 77855], []⟩,
        ⟨4769, false, false, [1042], []⟩,
        ⟨4779, true, false, [], [77855]⟩,
        ⟨4779, true, false, [], [77855]⟩,
        ⟨4778, true, false, [], [77855]⟩
      ]⟩,
    ⟨[77857], [77717, 11], .source 38993⟩,
    ⟨[77717, 11], [77857], .contexts [
        ⟨4781, true, false, [], []⟩
      ]⟩,
    ⟨[77717, 11], [77857], .contexts [
        ⟨4782, false, false, [], []⟩
      ]⟩,
    ⟨[77857], [77857], .contexts []⟩,
    ⟨[77857], [77857], .contexts []⟩,
    ⟨[77717, 11], [77857], .contexts [
        ⟨4783, false, false, [], []⟩,
        ⟨4784, false, false, [], []⟩,
        ⟨4785, false, false, [], []⟩,
        ⟨4785, false, false, [], []⟩
      ]⟩,
    ⟨[77717, 1], [1, 77717], .contexts [
        ⟨4158, false, false, [], []⟩,
        ⟨4160, false, false, [], []⟩,
        ⟨4156, false, false, [], []⟩,
        ⟨4157, false, false, [], []⟩,
        ⟨4157, false, false, [], []⟩
      ]⟩,
    ⟨[77857], [77857], .contexts []⟩,
    ⟨[77857, 5], [759, 77857], .contexts [
        ⟨4786, true, false, [], [5]⟩,
        ⟨1083, false, false, [77717], []⟩,
        ⟨1084, false, false, [77717], []⟩,
        ⟨4768, false, false, [], [11]⟩,
        ⟨4782, false, false, [759], []⟩,
        ⟨4788, false, false, [759], []⟩,
        ⟨3592, true, false, [], [77857]⟩
      ]⟩,
    ⟨[211, 77481], [211, 77481], .contexts []⟩,
    ⟨[1045, 77855], [1045, 77855], .contexts []⟩,
    ⟨[77857, 13], [211, 77479], .contexts [
        ⟨4786, true, false, [], [13]⟩,
        ⟨352, false, false, [77717], []⟩,
        ⟨353, false, false, [77717], []⟩,
        ⟨4774, false, false, [], [11]⟩,
        ⟨4143, false, false, [], []⟩,
        ⟨3594, false, false, [], []⟩,
        ⟨3595, false, false, [], []⟩,
        ⟨3595, false, false, [], []⟩,
        ⟨3597, false, false, [], []⟩,
        ⟨3599, false, false, [], []⟩
      ]⟩,
    ⟨[77859], [77717, 15], .source 38994⟩,
    ⟨[77717, 15], [77859], .contexts [
        ⟨4793, true, false, [], []⟩
      ]⟩,
    ⟨[77859], [77859], .contexts []⟩,
    ⟨[77859], [77859], .contexts []⟩,
    ⟨[77717, 15], [77859], .contexts [
        ⟨4794, false, false, [], []⟩,
        ⟨4795, false, false, [], []⟩,
        ⟨4796, false, false, [], []⟩,
        ⟨4796, false, false, [], []⟩
      ]⟩,
    ⟨[1, 77859], [1, 77859], .contexts []⟩,
    ⟨[1, 77859], [1, 77859], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 075. -/
def y322TCContextRaw075 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77859, 1], [77859, 1], .contexts []⟩,
    ⟨[77859], [77859], .contexts []⟩,
    ⟨[77859, 1], [1, 77859], .contexts [
        ⟨4800, false, false, [], []⟩,
        ⟨4797, true, false, [], [1]⟩,
        ⟨17, false, false, [77717], []⟩,
        ⟨21, false, false, [77717], []⟩,
        ⟨4787, false, false, [], [15]⟩,
        ⟨4794, false, false, [1], []⟩,
        ⟨4798, false, false, [], []⟩,
        ⟨4799, false, false, [], []⟩,
        ⟨4801, false, false, [1], []⟩,
        ⟨25, true, false, [], [77859]⟩
      ]⟩,
    ⟨[759, 77859], [759, 77859], .contexts []⟩,
    ⟨[759, 77859], [759, 77859], .contexts []⟩,
    ⟨[77859, 5], [759, 77859], .contexts [
        ⟨4797, true, false, [], [5]⟩,
        ⟨48, false, false, [77717], []⟩,
        ⟨51, false, false, [77717], []⟩,
        ⟨4768, false, false, [], [15]⟩,
        ⟨4794, false, false, [759], []⟩,
        ⟨4803, false, false, [], []⟩,
        ⟨4804, false, false, [], []⟩,
        ⟨4801, false, false, [759], []⟩,
        ⟨3592, true, false, [], [77859]⟩
      ]⟩,
    ⟨[77859, 7], [77859, 7], .contexts []⟩,
    ⟨[77859, 7], [77117], .contexts [
        ⟨4806, false, false, [], []⟩,
        ⟨4797, true, false, [], [7]⟩,
        ⟨61, false, false, [77717], []⟩,
        ⟨64, false, false, [77717], []⟩,
        ⟨4770, false, false, [], [15]⟩,
        ⟨396, false, false, [], []⟩,
        ⟨397, false, false, [], []⟩,
        ⟨398, false, false, [], []⟩,
        ⟨398, false, false, [], []⟩,
        ⟨402, false, false, [], []⟩,
        ⟨1118, true, false, [], [77117]⟩
      ]⟩,
    ⟨[13, 77859], [13, 77859], .contexts []⟩,
    ⟨[13, 77859], [13, 77859], .contexts []⟩,
    ⟨[77859, 13], [77859, 13], .contexts []⟩,
    ⟨[77861], [77481, 15], .source 38995⟩,
    ⟨[77481, 15], [77861], .contexts [
        ⟨4811, true, false, [], []⟩
      ]⟩,
    ⟨[77861], [77861], .contexts []⟩,
    ⟨[77481, 15], [77861], .contexts [
        ⟨4812, false, false, [], []⟩,
        ⟨4813, false, false, [], []⟩,
        ⟨4813, false, false, [], []⟩
      ]⟩,
    ⟨[77861], [77861], .contexts []⟩,
    ⟨[77861, 1], [479, 77861], .contexts [
        ⟨4814, true, false, [], [1]⟩,
        ⟨17, false, false, [77481], []⟩,
        ⟨21, false, false, [77481], []⟩,
        ⟨2609, false, false, [], [15]⟩,
        ⟨4812, false, false, [479], []⟩,
        ⟨4815, false, false, [479], []⟩,
        ⟨2587, true, false, [], [77861]⟩
      ]⟩,
    ⟨[483, 77217], [483, 77217], .contexts []⟩,
    ⟨[1047], [483, 929], .source 588⟩,
    ⟨[77861, 5], [1047, 77847], .contexts [
        ⟨4814, true, false, [], [5]⟩,
        ⟨48, false, false, [77481], []⟩,
        ⟨51, false, false, [77481], []⟩,
        ⟨2596, false, false, [], [15]⟩,
        ⟨2598, false, false, [], [15]⟩,
        ⟨4817, false, false, [], [15]⟩,
        ⟨4817, false, false, [], [15]⟩,
        ⟨4609, false, false, [483], []⟩,
        ⟨4629, false, false, [483, 901], []⟩,
        ⟨4636, true, false, [483], [77847]⟩,
        ⟨4818, true, false, [], [77847]⟩,
        ⟨4639, false, false, [1047], []⟩,
        ⟨24, true, false, [], [1047, 77847]⟩
      ]⟩,
    ⟨[77861, 9], [217, 77861], .contexts [
        ⟨4814, true, false, [], [9]⟩,
        ⟨75, false, false, [77481], []⟩,
        ⟨78, false, false, [77481], []⟩,
        ⟨2602, false, false, [], [15]⟩,
        ⟨2603, false, false, [], [15]⟩,
        ⟨2600, false, false, [], [15]⟩,
        ⟨2601, false, false, [], [15]⟩,
        ⟨2601, false, false, [], [15]⟩,
        ⟨4812, false, false, [217], []⟩,
        ⟨4815, false, false, [217], []⟩,
        ⟨2576, true, false, [], [77861]⟩
      ]⟩,
    ⟨[77117, 11], [211, 77861], .contexts [
        ⟨2571, false, false, [208], [77117, 11]⟩,
        ⟨402, true, false, [], [11]⟩,
        ⟨395, true, false, [], [11]⟩,
        ⟨2605, true, false, [208], [15, 11]⟩,
        ⟨2605, true, false, [208], [15, 11]⟩,
        ⟨2604, true, false, [208], [15, 11]⟩,
        ⟨2607, true, false, [208], [15, 11]⟩,
        ⟨2606, true, false, [208], [15, 11]⟩,
        ⟨92, true, false, [208, 77481], [11]⟩,
        ⟨89, true, false, [208, 77481], [11]⟩,
        ⟨4814, false, false, [208], [11, 11]⟩,
        ⟨90, false, false, [208, 77861], []⟩,
        ⟨1489, true, false, [], [77861]⟩
      ]⟩,
    ⟨[77863], [77341, 11], .source 38996⟩,
    ⟨[77341, 11], [77863], .contexts [
        ⟨4822, true, false, [], []⟩
      ]⟩,
    ⟨[77863, 11], [77341], .contexts [
        ⟨4823, true, false, [], [11]⟩,
        ⟨90, false, false, [77341], []⟩,
        ⟨1333, false, false, [], []⟩
      ]⟩,
    ⟨[77863], [77863], .contexts []⟩,
    ⟨[77863], [77863], .contexts []⟩,
    ⟨[77341, 11], [77863], .contexts [
        ⟨4823, false, false, [], []⟩,
        ⟨4825, false, false, [], []⟩,
        ⟨4826, false, false, [], []⟩,
        ⟨4826, false, false, [], []⟩
      ]⟩,
    ⟨[77863], [77863], .contexts []⟩,
    ⟨[77863, 3], [491, 77863], .contexts [
        ⟨4827, true, false, [], [3]⟩,
        ⟨335, false, false, [77341], []⟩,
        ⟨336, false, false, [77341], []⟩,
        ⟨2625, false, false, [], [11]⟩,
        ⟨4823, false, false, [491], []⟩,
        ⟨4828, false, false, [491], []⟩,
        ⟨24, true, false, [], [491, 77863]⟩
      ]⟩,
    ⟨[261, 77863], [261, 77863], .contexts []⟩,
    ⟨[261, 77863], [261, 77863], .contexts []⟩,
    ⟨[77863, 5], [77863, 5], .contexts []⟩,
    ⟨[77863, 5], [261, 77863], .contexts [
        ⟨4832, false, false, [], []⟩,
        ⟨4827, true, false, [], [5]⟩,
        ⟨1083, false, false, [77341], []⟩,
        ⟨1084, false, false, [77341], []⟩,
        ⟨1698, false, false, [], [11]⟩,
        ⟨4823, false, false, [261], []⟩,
        ⟨4830, false, false, [], []⟩,
        ⟨4831, false, false, [], []⟩,
        ⟨4828, false, false, [261], []⟩,
        ⟨2696, true, false, [], [77863]⟩
      ]⟩,
    ⟨[269, 77341], [269, 77341], .contexts []⟩,
    ⟨[269, 77863], [269, 77863], .contexts []⟩,
    ⟨[269, 77863], [269, 77863], .contexts []⟩,
    ⟨[269], [269], .contexts [
        ⟨24, false, false, [], [269]⟩
      ]⟩,
    ⟨[77863, 13], [269, 77863], .contexts [
        ⟨4827, true, false, [], [13]⟩,
        ⟨352, false, false, [77341], []⟩,
        ⟨353, false, false, [77341], []⟩,
        ⟨1652, false, false, [], [11]⟩,
        ⟨1654, false, false, [], [11]⟩,
        ⟨4834, false, false, [], [11]⟩,
        ⟨4834, false, false, [], [11]⟩,
        ⟨4823, false, false, [269], []⟩,
        ⟨4835, false, false, [], []⟩,
        ⟨4836, false, false, [], []⟩,
        ⟨4828, false, false, [269], []⟩,
        ⟨4837, true, false, [], [77863]⟩
      ]⟩,
    ⟨[537, 77127], [537, 77127], .contexts []⟩,
    ⟨[537, 77127], [537, 77127], .contexts []⟩,
    ⟨[77863, 15], [77863, 15], .contexts []⟩,
    ⟨[537], [537], .contexts [
        ⟨24, false, false, [], [537]⟩
      ]⟩,
    ⟨[77863, 15], [537, 77127], .contexts [
        ⟨4841, false, false, [], []⟩,
        ⟨4827, true, false, [], [15]⟩,
        ⟨358, false, false, [77341], []⟩,
        ⟨359, false, false, [77341], []⟩,
        ⟨2793, false, false, [], [11]⟩,
        ⟨2785, false, false, [], [11]⟩,
        ⟨2786, false, false, [], [11]⟩,
        ⟨2786, false, false, [], [11]⟩,
        ⟨434, false, false, [537], []⟩,
        ⟨4839, false, false, [], []⟩,
        ⟨4840, false, false, [], []⟩,
        ⟨1982, false, false, [537], []⟩,
        ⟨4842, true, false, [], [77127]⟩
      ]⟩,
    ⟨[77127, 15], [539, 77863], .contexts [
        ⟨4843, true, false, [536], [15]⟩,
        ⟨3, false, false, [536, 77863], []⟩,
        ⟨2782, true, false, [], [77863]⟩
      ]⟩,
    ⟨[77865], [77863, 1], .source 38997⟩,
    ⟨[77863, 1], [77865], .contexts [
        ⟨4845, true, false, [], []⟩
      ]⟩,
    ⟨[77865, 1], [77863], .contexts [
        ⟨4846, true, false, [], [1]⟩,
        ⟨18, false, false, [77863], []⟩,
        ⟨4826, false, false, [], []⟩
      ]⟩,
    ⟨[77865], [77865], .contexts []⟩,
    ⟨[77865], [77865], .contexts []⟩,
    ⟨[77863, 1], [77865], .contexts [
        ⟨4846, false, false, [], []⟩,
        ⟨4848, false, false, [], []⟩,
        ⟨4849, false, false, [], []⟩,
        ⟨4849, false, false, [], []⟩
      ]⟩,
    ⟨[261, 77865], [261, 77865], .contexts []⟩,
    ⟨[261, 77865], [261, 77865], .contexts []⟩,
    ⟨[77865, 5], [77865, 5], .contexts []⟩,
    ⟨[77865], [77865], .contexts []⟩,
    ⟨[77865, 5], [261, 77865], .contexts [
        ⟨4853, false, false, [], []⟩,
        ⟨4850, true, false, [], [5]⟩,
        ⟨165, false, false, [77863], []⟩,
        ⟨166, false, false, [77863], []⟩,
        ⟨4832, false, false, [], [1]⟩,
        ⟨4833, false, false, [], [1]⟩,
        ⟨4830, false, false, [], [1]⟩,
        ⟨4831, false, false, [], [1]⟩,
        ⟨4831, false, false, [], [1]⟩,
        ⟨4846, false, false, [261], []⟩,
        ⟨4851, false, false, [], []⟩,
        ⟨4852, false, false, [], []⟩,
        ⟨4854, false, false, [261], []⟩,
        ⟨2696, true, false, [], [77865]⟩
      ]⟩,
    ⟨[77865, 11], [77865, 11], .contexts []⟩,
    ⟨[77865, 11], [261, 77337], .contexts [
        ⟨4856, false, false, [], []⟩,
        ⟨4850, true, false, [], [11]⟩,
        ⟨181, false, false, [77863], []⟩,
        ⟨182, false, false, [77863], []⟩,
        ⟨4824, false, false, [], [1]⟩,
        ⟨1369, false, false, [], [1]⟩,
        ⟨1333, false, false, [], [1]⟩,
        ⟨1333, false, false, [], [1]⟩,
        ⟨1371, false, false, [], []⟩,
        ⟨2628, false, false, [], []⟩,
        ⟨1700, false, false, [], []⟩,
        ⟨1700, false, false, [], []⟩,
        ⟨2629, false, false, [261], []⟩,
        ⟨2696, true, false, [], [77337]⟩
      ]⟩,
    ⟨[77337, 11], [267, 77865], .contexts [
        ⟨4857, true, false, [260], [11]⟩,
        ⟨90, false, false, [260, 77865], []⟩,
        ⟨1582, true, false, [], [77865]⟩
      ]⟩,
    ⟨[537, 77129], [537, 77129], .contexts []⟩,
    ⟨[537, 77129], [537, 77129], .contexts []⟩,
    ⟨[77865, 15], [77865, 15], .contexts []⟩,
    ⟨[77865, 15], [537, 77129], .contexts [
        ⟨4861, false, false, [], []⟩,
        ⟨4850, true, false, [], [15]⟩,
        ⟨199, false, false, [77863], []⟩,
        ⟨200, false, false, [77863], []⟩,
        ⟨4841, false, false, [], [1]⟩,
        ⟨4843, false, false, [], [1]⟩,
        ⟨4839, false, false, [], [1]⟩,
        ⟨4840, false, false, [], [1]⟩,
        ⟨4840, false, false, [], [1]⟩,
        ⟨437, false, false, [537], []⟩,
        ⟨4859, false, false, [], []⟩,
        ⟨4860, false, false, [], []⟩,
        ⟨1994, false, false, [537], []⟩,
        ⟨4842, true, false, [], [77129]⟩
      ]⟩,
    ⟨[77129, 15], [539, 77865], .contexts [
        ⟨4862, true, false, [536], [15]⟩,
        ⟨3, false, false, [536, 77865], []⟩,
        ⟨2782, true, false, [], [77865]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 076. -/
def y322TCContextRaw076 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77865, 11], [261, 77337], .contexts [
        ⟨4856, false, false, [], []⟩,
        ⟨4857, false, false, [], []⟩,
        ⟨1699, false, false, [], []⟩,
        ⟨1700, false, false, [], []⟩,
        ⟨1700, false, false, [], []⟩
      ]⟩,
    ⟨[1051], [261, 679], .source 590⟩,
    ⟨[1053], [1051, 663], .source 591⟩,
    ⟨[1055], [1053, 677], .source 592⟩,
    ⟨[1057], [1055, 267], .source 593⟩,
    ⟨[11, 9, 11, 9, 11, 9], [], .contexts [
        ⟨343, false, false, [], []⟩
      ]⟩,
    ⟨[1057, 77865, 9], [77865], .contexts [
        ⟨4868, false, false, [], [77865, 9]⟩,
        ⟨4858, true, false, [1055], [9]⟩,
        ⟨4867, false, false, [], [77337, 11, 9]⟩,
        ⟨3329, true, false, [1053], [11, 9]⟩,
        ⟨4866, false, false, [], [77601, 9, 11, 9]⟩,
        ⟨3306, true, false, [1051], [9, 11, 9]⟩,
        ⟨4865, false, false, [], [77601, 11, 9, 11, 9]⟩,
        ⟨3331, true, false, [261], [11, 9, 11, 9]⟩,
        ⟨4864, true, false, [], [9, 11, 9, 11, 9]⟩,
        ⟨4869, false, false, [77865], []⟩
      ]⟩,
    ⟨[77865, 9], [77865, 9], .contexts []⟩,
    ⟨[1059], [1056], .source 594⟩,
    ⟨[1056], [1056], .contexts []⟩,
    ⟨[77865, 9], [1059, 77865], .contexts [
        ⟨4871, false, false, [], []⟩,
        ⟨4870, false, false, [1056], []⟩,
        ⟨4854, false, false, [1056], []⟩,
        ⟨4873, true, false, [], [77865]⟩,
        ⟨4873, true, false, [], [77865]⟩,
        ⟨4872, true, false, [], [77865]⟩
      ]⟩,
    ⟨[77865, 15], [537, 77129], .contexts [
        ⟨4862, false, false, [], []⟩
      ]⟩,
    ⟨[1059, 77865], [1059, 77865], .contexts []⟩,
    ⟨[77865, 9], [1059, 77865], .contexts [
        ⟨4871, false, false, [], []⟩,
        ⟨4874, false, false, [], []⟩,
        ⟨4876, false, false, [], []⟩,
        ⟨4876, false, false, [], []⟩
      ]⟩,
    ⟨[1061], [1059, 537], .source 595⟩,
    ⟨[77129, 9], [77129, 9], .contexts []⟩,
    ⟨[1063], [539, 1061], .source 596⟩,
    ⟨[77129, 9], [1063, 77129], .contexts [
        ⟨4879, false, false, [], []⟩,
        ⟨4860, true, false, [536], [9]⟩,
        ⟨4860, true, false, [536], [9]⟩,
        ⟨4859, true, false, [536], [9]⟩,
        ⟨4875, true, false, [536], [9]⟩,
        ⟨4861, true, false, [536], [9]⟩,
        ⟨75, false, false, [536, 77865], []⟩,
        ⟨78, false, false, [536, 77865], []⟩,
        ⟨4877, false, false, [536], [15]⟩,
        ⟨4862, false, false, [536, 1059], []⟩,
        ⟨4878, true, false, [536], [77129]⟩,
        ⟨1994, false, false, [536, 1061], []⟩,
        ⟨2789, true, false, [], [1061, 77129]⟩,
        ⟨4880, true, false, [], [77129]⟩
      ]⟩,
    ⟨[1063, 77129], [1063, 77129], .contexts []⟩,
    ⟨[77129, 9], [1063, 77129], .contexts [
        ⟨4879, false, false, [], []⟩,
        ⟨4881, false, false, [], []⟩,
        ⟨4882, false, false, [], []⟩,
        ⟨4882, false, false, [], []⟩
      ]⟩,
    ⟨[77131, 9], [77131, 9], .contexts []⟩,
    ⟨[1065], [1062], .source 597⟩,
    ⟨[1062], [1062], .contexts []⟩,
    ⟨[77131, 9], [1065, 77131], .contexts [
        ⟨4884, false, false, [], []⟩,
        ⟨441, true, false, [], [9]⟩,
        ⟨4883, true, false, [1062], [13, 9]⟩,
        ⟨926, false, false, [1062, 77129], []⟩,
        ⟨1999, false, false, [1062], []⟩,
        ⟨1998, false, false, [1062], []⟩,
        ⟨2001, false, false, [1062], []⟩,
        ⟨4886, true, false, [], [77131]⟩,
        ⟨4886, true, false, [], [77131]⟩,
        ⟨4885, true, false, [], [77131]⟩
      ]⟩,
    ⟨[1065, 77131], [1065, 77131], .contexts []⟩,
    ⟨[1064], [1064], .contexts []⟩,
    ⟨[77133, 9], [1063, 77133], .contexts [
        ⟨445, true, false, [], [9]⟩,
        ⟨4888, true, false, [1064], [15, 9]⟩,
        ⟨4888, true, false, [1064], [15, 9]⟩,
        ⟨4887, true, false, [1064], [15, 9]⟩,
        ⟨4884, true, false, [1064], [15, 9]⟩,
        ⟨1636, false, false, [1064, 77131], []⟩,
        ⟨2007, false, false, [1064], []⟩,
        ⟨2005, false, false, [1064], []⟩,
        ⟨2009, false, false, [1064], []⟩,
        ⟨4889, true, false, [], [77133]⟩,
        ⟨4889, true, false, [], [77133]⟩,
        ⟨4885, false, true, [], [77133]⟩
      ]⟩,
    ⟨[77867], [77865, 13], .source 38998⟩,
    ⟨[77865, 13], [77867], .contexts [
        ⟨4891, true, false, [], []⟩
      ]⟩,
    ⟨[77867, 13], [77865], .contexts [
        ⟨4892, true, false, [], [13]⟩,
        ⟨98, false, false, [77865], []⟩,
        ⟨4849, false, false, [], []⟩
      ]⟩,
    ⟨[77867], [77867], .contexts []⟩,
    ⟨[77865, 13], [77867], .contexts [
        ⟨4892, false, false, [], []⟩,
        ⟨4894, false, false, [], []⟩,
        ⟨4894, false, false, [], []⟩
      ]⟩,
    ⟨[269, 77867], [269, 77867], .contexts []⟩,
    ⟨[269, 77867], [269, 77867], .contexts []⟩,
    ⟨[77867, 1], [77867, 1], .contexts []⟩,
    ⟨[77867], [77867], .contexts []⟩,
    ⟨[77867, 1], [269, 77867], .contexts [
        ⟨4898, false, false, [], []⟩,
        ⟨4895, true, false, [], [1]⟩,
        ⟨387, false, false, [77865], []⟩,
        ⟨390, false, false, [77865], []⟩,
        ⟨4847, false, false, [], [13, 1, 13]⟩,
        ⟨4825, false, false, [], [13, 1, 13]⟩,
        ⟨4826, false, false, [], [13, 1, 13]⟩,
        ⟨4826, false, false, [], [13, 1, 13]⟩,
        ⟨4838, false, false, [], [1, 13]⟩,
        ⟨4835, false, false, [], [1, 13]⟩,
        ⟨4836, false, false, [], [1, 13]⟩,
        ⟨4836, false, false, [], [1, 13]⟩,
        ⟨4846, false, false, [269], [13]⟩,
        ⟨4892, false, false, [269], []⟩,
        ⟨4896, false, false, [], []⟩,
        ⟨4897, false, false, [], []⟩,
        ⟨4899, false, false, [269], []⟩
      ]⟩,
    ⟨[77867, 1], [269, 77867], .contexts [
        ⟨4900, false, false, [], []⟩,
        ⟨4837, true, false, [], [77867]⟩
      ]⟩,
    ⟨[1059, 77867], [1059, 77867], .contexts []⟩,
    ⟨[1059, 77867], [1059, 77867], .contexts []⟩,
    ⟨[77867, 9], [77867, 9], .contexts []⟩,
    ⟨[1059], [1059], .contexts [
        ⟨24, false, false, [], [1059]⟩
      ]⟩,
    ⟨[77867, 9], [1059, 77867], .contexts [
        ⟨4904, false, false, [], []⟩,
        ⟨4895, true, false, [], [9]⟩,
        ⟨130, false, false, [77865], []⟩,
        ⟨131, false, false, [77865], []⟩,
        ⟨4877, false, false, [], [13]⟩,
        ⟨4892, false, false, [1059], []⟩,
        ⟨4902, false, false, [], []⟩,
        ⟨4903, false, false, [], []⟩,
        ⟨4899, false, false, [1059], []⟩,
        ⟨4905, true, false, [], [77867]⟩
      ]⟩,
    ⟨[1067], [261, 709], .source 598⟩,
    ⟨[77867, 11], [1067, 77455], .contexts [
        ⟨4895, true, false, [], [11]⟩,
        ⟨137, false, false, [77865], []⟩,
        ⟨138, false, false, [77865], []⟩,
        ⟨4864, false, false, [], [13]⟩,
        ⟨3375, false, false, [261], []⟩,
        ⟨4907, true, false, [], [77455]⟩,
        ⟨3373, false, false, [1067], []⟩,
        ⟨24, true, false, [], [1067, 77455]⟩
      ]⟩,
    ⟨[1069], [1066], .source 599⟩,
    ⟨[77455, 11], [1069, 77867], .contexts [
        ⟨4908, true, false, [1066], [11]⟩,
        ⟨90, false, false, [1066, 77867], []⟩,
        ⟨4909, true, false, [], [77867]⟩
      ]⟩,
    ⟨[77869], [77867, 15], .source 38999⟩,
    ⟨[77867, 15], [77869], .contexts [
        ⟨4911, true, false, [], []⟩
      ]⟩,
    ⟨[77869, 15], [77867], .contexts [
        ⟨4912, true, false, [], [15]⟩,
        ⟨3, false, false, [77867], []⟩,
        ⟨4894, false, false, [], []⟩
      ]⟩,
    ⟨[77869], [77869], .contexts []⟩,
    ⟨[77867, 15], [77869], .contexts [
        ⟨4912, false, false, [], []⟩,
        ⟨4914, false, false, [], []⟩,
        ⟨4914, false, false, [], []⟩
      ]⟩,
    ⟨[269, 77869], [269, 77869], .contexts []⟩,
    ⟨[269, 77869], [269, 77869], .contexts []⟩,
    ⟨[77869, 1], [77869, 1], .contexts []⟩,
    ⟨[77869], [77869], .contexts []⟩,
    ⟨[77869, 1], [269, 77869], .contexts [
        ⟨4918, false, false, [], []⟩,
        ⟨4915, true, false, [], [1]⟩,
        ⟨17, false, false, [77867], []⟩,
        ⟨21, false, false, [77867], []⟩,
        ⟨4898, false, false, [], [15]⟩,
        ⟨4901, false, false, [], [15]⟩,
        ⟨4896, false, false, [], [15]⟩,
        ⟨4897, false, false, [], [15]⟩,
        ⟨4897, false, false, [], [15]⟩,
        ⟨4912, false, false, [269], []⟩,
        ⟨4916, false, false, [], []⟩,
        ⟨4917, false, false, [], []⟩,
        ⟨4919, false, false, [269], []⟩,
        ⟨4837, true, false, [], [77869]⟩
      ]⟩,
    ⟨[1059, 77869], [1059, 77869], .contexts []⟩,
    ⟨[1059, 77869], [1059, 77869], .contexts []⟩,
    ⟨[1059, 77869], [1059, 77869], .contexts []⟩,
    ⟨[77869, 9], [77869, 9], .contexts []⟩,
    ⟨[77867, 13], [77865], .contexts [
        ⟨4893, false, false, [], []⟩,
        ⟨4848, false, false, [], []⟩,
        ⟨4849, false, false, [], []⟩,
        ⟨4849, false, false, [], []⟩
      ]⟩,
    ⟨[537, 77133], [537, 77133], .contexts []⟩,
    ⟨[537, 77133], [537, 77133], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 077. -/
def y322TCContextRaw077 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77869, 13], [77869, 13], .contexts []⟩,
    ⟨[77869, 13], [537, 77133], .contexts [
        ⟨4928, false, false, [], []⟩,
        ⟨4915, true, false, [], [13]⟩,
        ⟨408, false, false, [77867], []⟩,
        ⟨410, false, false, [77867], []⟩,
        ⟨4925, false, false, [], [15, 13, 15]⟩,
        ⟨4875, false, false, [], [13, 15]⟩,
        ⟨4859, false, false, [], [13, 15]⟩,
        ⟨4860, false, false, [], [13, 15]⟩,
        ⟨4860, false, false, [], [13, 15]⟩,
        ⟨441, false, false, [537], [15]⟩,
        ⟨445, false, false, [537], []⟩,
        ⟨4926, false, false, [], []⟩,
        ⟨4927, false, false, [], []⟩,
        ⟨2009, false, false, [537], []⟩,
        ⟨4842, true, false, [], [77133]⟩
      ]⟩,
    ⟨[77133, 13], [539, 77869], .contexts [
        ⟨4929, true, false, [536], [13]⟩,
        ⟨98, false, false, [536, 77869], []⟩,
        ⟨2782, true, false, [], [77869]⟩
      ]⟩,
    ⟨[1071], [269, 537], .source 600⟩,
    ⟨[77135, 13], [77135, 13], .contexts []⟩,
    ⟨[1073], [1070], .source 601⟩,
    ⟨[1075], [1073, 537], .source 602⟩,
    ⟨[77135, 13], [1075, 77135], .contexts [
        ⟨4932, false, false, [], []⟩,
        ⟨448, true, false, [], [13]⟩,
        ⟨4931, false, false, [1070], [77133, 1, 13]⟩,
        ⟨4929, true, false, [1070, 269], [1, 13]⟩,
        ⟨4917, true, false, [1070], [13, 1, 13]⟩,
        ⟨4917, true, false, [1070], [13, 1, 13]⟩,
        ⟨4916, true, false, [1070], [13, 1, 13]⟩,
        ⟨4920, true, false, [1070], [13, 1, 13]⟩,
        ⟨4918, true, false, [1070], [13, 1, 13]⟩,
        ⟨1587, false, false, [1070, 77869], []⟩,
        ⟨190, false, false, [1070, 77869], []⟩,
        ⟨4928, false, false, [1070], [1]⟩,
        ⟨4929, false, false, [1070], [1]⟩,
        ⟨4926, false, false, [1070], [1]⟩,
        ⟨4927, false, false, [1070], [1]⟩,
        ⟨4927, false, false, [1070], [1]⟩,
        ⟨448, false, false, [1070, 537], []⟩,
        ⟨2013, false, false, [1070, 537], []⟩,
        ⟨4933, true, false, [], [537, 77135]⟩,
        ⟨4934, true, false, [], [77135]⟩
      ]⟩,
    ⟨[1075, 77135], [1075, 77135], .contexts []⟩,
    ⟨[77135, 13], [1075, 77135], .contexts [
        ⟨4932, false, false, [], []⟩,
        ⟨4935, false, false, [], []⟩,
        ⟨4936, false, false, [], []⟩,
        ⟨4936, false, false, [], []⟩
      ]⟩,
    ⟨[77137, 13], [77137, 13], .contexts []⟩,
    ⟨[77137], [77137], .contexts []⟩,
    ⟨[1077], [1074], .source 603⟩,
    ⟨[1074], [1074], .contexts []⟩,
    ⟨[77137, 13], [1077, 77137], .contexts [
        ⟨4938, false, false, [], []⟩,
        ⟨452, true, false, [], [13]⟩,
        ⟨4937, true, false, [1074], [3, 13]⟩,
        ⟨1881, false, false, [1074, 77135], []⟩,
        ⟨36, false, false, [1074, 77135], []⟩,
        ⟨2016, false, false, [1074], []⟩,
        ⟨4939, false, false, [1074], []⟩,
        ⟨4941, true, false, [], [77137]⟩,
        ⟨4941, true, false, [], [77137]⟩,
        ⟨4940, true, false, [], [77137]⟩
      ]⟩,
    ⟨[1077, 77137], [1077, 77137], .contexts []⟩,
    ⟨[77137, 13], [1077, 77137], .contexts [
        ⟨4938, false, false, [], []⟩,
        ⟨4942, false, false, [], []⟩,
        ⟨4943, false, false, [], []⟩,
        ⟨4943, false, false, [], []⟩
      ]⟩,
    ⟨[77137, 5], [77139], .contexts [
        ⟨2017, false, false, [], []⟩,
        ⟨712, false, false, [], []⟩,
        ⟨460, false, false, [], []⟩,
        ⟨460, false, false, [], []⟩
      ]⟩,
    ⟨[77139, 13], [77139, 13], .contexts []⟩,
    ⟨[1076], [1076], .contexts []⟩,
    ⟨[77871], [77869, 3], .source 39000⟩,
    ⟨[77869, 3], [77871], .contexts [
        ⟨4948, true, false, [], []⟩
      ]⟩,
    ⟨[77871, 3], [77869], .contexts [
        ⟨4949, true, false, [], [3]⟩,
        ⟨35, false, false, [77869], []⟩,
        ⟨4914, false, false, [], []⟩
      ]⟩,
    ⟨[77869, 3], [77871], .contexts [
        ⟨4949, false, false, [], []⟩
      ]⟩,
    ⟨[77871], [77871], .contexts []⟩,
    ⟨[77871], [77871], .contexts []⟩,
    ⟨[1059, 77871], [1059, 77871], .contexts []⟩,
    ⟨[1059, 77871], [1059, 77871], .contexts []⟩,
    ⟨[77869, 9, 3], [1059, 77871], .contexts [
        ⟨4924, false, false, [], [3]⟩,
        ⟨4924, false, false, [], [3]⟩,
        ⟨4915, true, false, [], [9, 3]⟩,
        ⟨75, false, false, [77867], [3]⟩,
        ⟨78, false, false, [77867], [3]⟩,
        ⟨4904, false, false, [], [15, 3]⟩,
        ⟨4906, false, false, [], [15, 3]⟩,
        ⟨4902, false, false, [], [15, 3]⟩,
        ⟨4903, false, false, [], [15, 3]⟩,
        ⟨4903, false, false, [], [15, 3]⟩,
        ⟨4912, false, false, [1059], [3]⟩,
        ⟨4921, false, false, [], [3]⟩,
        ⟨4922, false, false, [], [3]⟩,
        ⟨4923, false, false, [], [3]⟩,
        ⟨4919, false, false, [1059], [3]⟩,
        ⟨4905, true, false, [], [77869, 3]⟩,
        ⟨4921, false, false, [], [3]⟩,
        ⟨4923, false, false, [], [3]⟩,
        ⟨4923, false, false, [], [3]⟩,
        ⟨4949, false, false, [1059], []⟩,
        ⟨4954, false, false, [], []⟩,
        ⟨4955, false, false, [], []⟩
      ]⟩,
    ⟨[1059, 77871], [1059, 77871], .contexts []⟩,
    ⟨[77871, 9], [77871, 9], .contexts []⟩,
    ⟨[77871], [77871], .contexts []⟩,
    ⟨[77871, 9], [1059, 77871], .contexts [
        ⟨4958, false, false, [], []⟩,
        ⟨4953, true, false, [], [9]⟩,
        ⟨4953, true, false, [], [9]⟩,
        ⟨4952, true, false, [], [9]⟩,
        ⟨4951, true, false, [], [9]⟩,
        ⟨1112, false, false, [77869], []⟩,
        ⟨1113, false, false, [77869], []⟩,
        ⟨4956, false, false, [], []⟩,
        ⟨4957, false, false, [], []⟩,
        ⟨4959, false, false, [1059], []⟩,
        ⟨4905, true, false, [], [77871]⟩
      ]⟩,
    ⟨[77873], [77871, 5], .source 39001⟩,
    ⟨[77871, 5], [77873], .contexts [
        ⟨4961, true, false, [], []⟩
      ]⟩,
    ⟨[77873, 5], [77871], .contexts [
        ⟨4962, true, false, [], [5]⟩,
        ⟨49, false, false, [77871], []⟩,
        ⟨4953, false, false, [], []⟩
      ]⟩,
    ⟨[77873], [77873], .contexts []⟩,
    ⟨[77873], [77873], .contexts []⟩,
    ⟨[77873], [77873], .contexts []⟩,
    ⟨[1059, 77873], [1059, 77873], .contexts []⟩,
    ⟨[1059, 77873], [1059, 77873], .contexts []⟩,
    ⟨[1059, 77873], [1059, 77873], .contexts []⟩,
    ⟨[77875], [77873, 1], .source 39002⟩,
    ⟨[77873, 1], [77875], .contexts [
        ⟨4970, true, false, [], []⟩
      ]⟩,
    ⟨[77875, 1], [77873], .contexts [
        ⟨4971, true, false, [], [1]⟩,
        ⟨18, false, false, [77873], []⟩,
        ⟨4965, false, false, [], []⟩
      ]⟩,
    ⟨[77877], [77875, 9], .source 39003⟩,
    ⟨[77875, 9], [77877], .contexts [
        ⟨4973, true, false, [], []⟩
      ]⟩,
    ⟨[77877, 9], [77875], .contexts [
        ⟨4974, true, false, [], [9]⟩,
        ⟨76, false, false, [77875], []⟩
      ]⟩,
    ⟨[77877], [77877], .contexts []⟩,
    ⟨[77877], [77877], .contexts []⟩,
    ⟨[1059, 77875], [1059, 77875], .contexts []⟩,
    ⟨[1059, 77875], [1059, 77875], .contexts []⟩,
    ⟨[77875, 1, 9, 1], [1059, 77875], .contexts [
        ⟨4972, false, false, [], [9, 1]⟩,
        ⟨4964, false, false, [], [9, 1]⟩,
        ⟨4965, false, false, [], [9, 1]⟩,
        ⟨4965, false, false, [], [9, 1]⟩,
        ⟨4965, true, false, [], [9, 1]⟩,
        ⟨4965, true, false, [], [9, 1]⟩,
        ⟨4964, true, false, [], [9, 1]⟩,
        ⟨4962, true, false, [], [9, 1]⟩,
        ⟨2076, false, false, [77871], [1]⟩,
        ⟨2077, false, false, [77871], [1]⟩,
        ⟨4958, false, false, [], [5, 1]⟩,
        ⟨4960, false, false, [], [5, 1]⟩,
        ⟨4954, false, false, [], [5, 1]⟩,
        ⟨4957, false, false, [], [5, 1]⟩,
        ⟨4957, false, false, [], [5, 1]⟩,
        ⟨4962, false, false, [1059], [1]⟩,
        ⟨4967, false, false, [], [1]⟩,
        ⟨4968, false, false, [], [1]⟩,
        ⟨4969, false, false, [], [1]⟩,
        ⟨4966, false, false, [1059], [1]⟩,
        ⟨4905, true, false, [], [77873, 1]⟩,
        ⟨4967, false, false, [], [1]⟩,
        ⟨4969, false, false, [], [1]⟩,
        ⟨4969, false, false, [], [1]⟩,
        ⟨4971, false, false, [1059], []⟩,
        ⟨4978, false, false, [], []⟩,
        ⟨4979, false, false, [], []⟩
      ]⟩,
    ⟨[1059, 77875], [1059, 77875], .contexts []⟩,
    ⟨[1059, 77877], [1059, 77877], .contexts []⟩,
    ⟨[1059, 77877], [1059, 77877], .contexts []⟩,
    ⟨[1059, 77877], [1059, 77877], .contexts []⟩,
    ⟨[77877, 1], [77877, 1], .contexts []⟩,
    ⟨[77877], [77877], .contexts []⟩,
    ⟨[77879], [77877, 11], .source 39004⟩,
    ⟨[77877, 11], [77879], .contexts [
        ⟨4987, true, false, [], []⟩
      ]⟩,
    ⟨[77879], [77879], .contexts []⟩,
    ⟨[77879], [77879], .contexts []⟩,
    ⟨[77877, 1], [1059, 77877], .contexts [
        ⟨4985, false, false, [], []⟩,
        ⟨4985, false, false, [], []⟩,
        ⟨4977, true, false, [], [1]⟩,
        ⟨4977, true, false, [], [1]⟩,
        ⟨4976, true, false, [], [1]⟩,
        ⟨4974, true, false, [], [1]⟩,
        ⟨1143, false, false, [77875], []⟩,
        ⟨1146, false, false, [77875], []⟩,
        ⟨4980, false, false, [], [9]⟩,
        ⟨4981, false, false, [], [9]⟩,
        ⟨4974, false, false, [1059], []⟩,
        ⟨4982, false, false, [], []⟩,
        ⟨4983, false, false, [], []⟩,
        ⟨4984, false, false, [], []⟩,
        ⟨4986, false, false, [1059], []⟩,
        ⟨4905, true, false, [], [77877]⟩,
        ⟨4982, false, false, [], []⟩,
        ⟨4984, false, false, [], []⟩,
        ⟨4984, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 078. -/
def y322TCContextRaw078 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1059, 77879], [1059, 77879], .contexts []⟩,
    ⟨[1059, 77879], [1059, 77879], .contexts []⟩,
    ⟨[77881], [77879, 13], .source 39005⟩,
    ⟨[77879, 13], [77881], .contexts [
        ⟨4994, true, false, [], []⟩
      ]⟩,
    ⟨[77883], [77881, 15], .source 39006⟩,
    ⟨[77881, 15], [77883], .contexts [
        ⟨4996, true, false, [], []⟩
      ]⟩,
    ⟨[77881], [77881], .contexts []⟩,
    ⟨[77885], [77883, 1], .source 39007⟩,
    ⟨[77883, 1], [77885], .contexts [
        ⟨4999, true, false, [], []⟩
      ]⟩,
    ⟨[77883], [77883], .contexts []⟩,
    ⟨[77887], [77885, 3], .source 39008⟩,
    ⟨[77885, 3], [77887], .contexts [
        ⟨5002, true, false, [], []⟩
      ]⟩,
    ⟨[77885], [77885], .contexts []⟩,
    ⟨[77889], [77887, 5], .source 39009⟩,
    ⟨[77887, 5], [77889], .contexts [
        ⟨5005, true, false, [], []⟩
      ]⟩,
    ⟨[77887], [77887], .contexts []⟩,
    ⟨[77889, 5], [77887], .contexts [
        ⟨5006, true, false, [], [5]⟩,
        ⟨49, false, false, [77887], []⟩,
        ⟨5007, false, false, [], []⟩
      ]⟩,
    ⟨[77891], [77889, 1], .source 39010⟩,
    ⟨[77889, 1], [77891], .contexts [
        ⟨5009, true, false, [], []⟩
      ]⟩,
    ⟨[77889], [77889], .contexts []⟩,
    ⟨[77891, 1], [77889], .contexts [
        ⟨5010, true, false, [], [1]⟩,
        ⟨18, false, false, [77889], []⟩,
        ⟨5011, false, false, [], []⟩
      ]⟩,
    ⟨[77893], [77891, 9], .source 39011⟩,
    ⟨[77891, 9], [77893], .contexts [
        ⟨5013, true, false, [], []⟩
      ]⟩,
    ⟨[77891], [77891], .contexts []⟩,
    ⟨[77895], [77893, 11], .source 39012⟩,
    ⟨[77893, 11], [77895], .contexts [
        ⟨5016, true, false, [], []⟩
      ]⟩,
    ⟨[77893], [77893], .contexts []⟩,
    ⟨[77897], [77895, 1], .source 39013⟩,
    ⟨[77895, 1], [77897], .contexts [
        ⟨5019, true, false, [], []⟩
      ]⟩,
    ⟨[77895], [77895], .contexts []⟩,
    ⟨[77899], [77897, 13], .source 39014⟩,
    ⟨[77897, 13], [77899], .contexts [
        ⟨5022, true, false, [], []⟩
      ]⟩,
    ⟨[77897], [77897], .contexts []⟩,
    ⟨[77901], [77899, 15], .source 39015⟩,
    ⟨[77899, 15], [77901], .contexts [
        ⟨5025, true, false, [], []⟩
      ]⟩,
    ⟨[77899], [77899], .contexts []⟩,
    ⟨[77903], [77901, 1], .source 39016⟩,
    ⟨[77901, 1], [77903], .contexts [
        ⟨5028, true, false, [], []⟩
      ]⟩,
    ⟨[77901], [77901], .contexts []⟩,
    ⟨[77905], [77903, 3], .source 39017⟩,
    ⟨[77903, 3], [77905], .contexts [
        ⟨5031, true, false, [], []⟩
      ]⟩,
    ⟨[77903], [77903], .contexts []⟩,
    ⟨[77907], [77905, 5], .source 39018⟩,
    ⟨[77905, 5], [77907], .contexts [
        ⟨5034, true, false, [], []⟩
      ]⟩,
    ⟨[77905], [77905], .contexts []⟩,
    ⟨[77909], [77907, 1], .source 39019⟩,
    ⟨[77907, 1], [77909], .contexts [
        ⟨5037, true, false, [], []⟩
      ]⟩,
    ⟨[77907], [77907], .contexts []⟩,
    ⟨[77911], [77909, 9], .source 39020⟩,
    ⟨[77909, 9], [77911], .contexts [
        ⟨5040, true, false, [], []⟩
      ]⟩,
    ⟨[77909], [77909], .contexts []⟩,
    ⟨[77913], [77911, 11], .source 39021⟩,
    ⟨[77911, 11], [77913], .contexts [
        ⟨5043, true, false, [], []⟩
      ]⟩,
    ⟨[77911], [77911], .contexts []⟩,
    ⟨[77915], [77913, 1], .source 39022⟩,
    ⟨[77913, 1], [77915], .contexts [
        ⟨5046, true, false, [], []⟩
      ]⟩,
    ⟨[77913], [77913], .contexts []⟩,
    ⟨[77917], [77915, 13], .source 39023⟩,
    ⟨[77915, 13], [77917], .contexts [
        ⟨5049, true, false, [], []⟩
      ]⟩,
    ⟨[77915], [77915], .contexts []⟩,
    ⟨[77919], [77917, 15], .source 39024⟩,
    ⟨[77917, 15], [77919], .contexts [
        ⟨5052, true, false, [], []⟩
      ]⟩,
    ⟨[77917], [77917], .contexts []⟩,
    ⟨[77921], [77919, 1], .source 39025⟩]

/-- Exact literal claimed equations and contextual derivations, block 079. -/
def y322TCContextRaw079 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77919, 1], [77921], .contexts [
        ⟨5055, true, false, [], []⟩
      ]⟩,
    ⟨[77919], [77919], .contexts []⟩,
    ⟨[77923], [77921, 3], .source 39026⟩,
    ⟨[77921, 3], [77923], .contexts [
        ⟨5058, true, false, [], []⟩
      ]⟩,
    ⟨[77921], [77921], .contexts []⟩,
    ⟨[77925], [77923, 5], .source 39027⟩,
    ⟨[77923], [77923], .contexts []⟩,
    ⟨[77925, 5], [77923], .contexts [
        ⟨5061, false, false, [], [5]⟩,
        ⟨49, false, false, [77923], []⟩,
        ⟨5062, false, false, [], []⟩
      ]⟩,
    ⟨[77927], [77925, 1], .source 39028⟩,
    ⟨[77925], [77925], .contexts []⟩,
    ⟨[77927, 1], [77925], .contexts [
        ⟨5064, false, false, [], [1]⟩,
        ⟨18, false, false, [77925], []⟩,
        ⟨5065, false, false, [], []⟩
      ]⟩,
    ⟨[77929], [77927, 9], .source 39029⟩,
    ⟨[77927, 9], [77929], .contexts [
        ⟨5067, true, false, [], []⟩
      ]⟩,
    ⟨[77927], [77927], .contexts []⟩,
    ⟨[77929, 9], [77927], .contexts [
        ⟨5068, true, false, [], [9]⟩,
        ⟨76, false, false, [77927], []⟩,
        ⟨5069, false, false, [], []⟩
      ]⟩,
    ⟨[77931], [77929, 11], .source 39030⟩,
    ⟨[77929, 11], [77931], .contexts [
        ⟨5071, true, false, [], []⟩
      ]⟩,
    ⟨[77929], [77929], .contexts []⟩,
    ⟨[77931, 11], [77929], .contexts [
        ⟨5072, true, false, [], [11]⟩,
        ⟨90, false, false, [77929], []⟩,
        ⟨5073, false, false, [], []⟩
      ]⟩,
    ⟨[77933], [77931, 1], .source 39031⟩,
    ⟨[77931, 1], [77933], .contexts [
        ⟨5075, true, false, [], []⟩
      ]⟩,
    ⟨[77931], [77931], .contexts []⟩,
    ⟨[77933, 1], [77931], .contexts [
        ⟨5076, true, false, [], [1]⟩,
        ⟨18, false, false, [77931], []⟩,
        ⟨5077, false, false, [], []⟩
      ]⟩,
    ⟨[77935], [77933, 13], .source 39032⟩,
    ⟨[77933, 13], [77935], .contexts [
        ⟨5079, true, false, [], []⟩
      ]⟩,
    ⟨[77933], [77933], .contexts []⟩,
    ⟨[77935, 13], [77933], .contexts [
        ⟨5080, true, false, [], [13]⟩,
        ⟨98, false, false, [77933], []⟩,
        ⟨5081, false, false, [], []⟩
      ]⟩,
    ⟨[77937], [77935, 15], .source 39033⟩,
    ⟨[77935, 15], [77937], .contexts [
        ⟨5083, true, false, [], []⟩
      ]⟩,
    ⟨[77935], [77935], .contexts []⟩,
    ⟨[77937, 15], [77935], .contexts [
        ⟨5084, true, false, [], [15]⟩,
        ⟨3, false, false, [77935], []⟩,
        ⟨5085, false, false, [], []⟩
      ]⟩,
    ⟨[77939], [77937, 1], .source 39034⟩,
    ⟨[77937, 1], [77939], .contexts [
        ⟨5087, true, false, [], []⟩
      ]⟩,
    ⟨[77937], [77937], .contexts []⟩,
    ⟨[77939, 1], [77937], .contexts [
        ⟨5088, true, false, [], [1]⟩,
        ⟨18, false, false, [77937], []⟩,
        ⟨5089, false, false, [], []⟩
      ]⟩,
    ⟨[77941], [77939, 3], .source 39035⟩,
    ⟨[77939], [77939], .contexts []⟩,
    ⟨[77941, 3], [77939], .contexts [
        ⟨5091, false, false, [], [3]⟩,
        ⟨35, false, false, [77939], []⟩,
        ⟨5092, false, false, [], []⟩
      ]⟩,
    ⟨[77943], [77941, 5], .source 39036⟩,
    ⟨[77941, 5], [77943], .contexts [
        ⟨5094, true, false, [], []⟩
      ]⟩,
    ⟨[77941], [77941], .contexts []⟩,
    ⟨[77943, 5], [77941], .contexts [
        ⟨5095, true, false, [], [5]⟩,
        ⟨49, false, false, [77941], []⟩,
        ⟨5096, false, false, [], []⟩
      ]⟩,
    ⟨[77945], [77943, 1], .source 39037⟩,
    ⟨[77943, 1], [77945], .contexts [
        ⟨5098, true, false, [], []⟩
      ]⟩,
    ⟨[77943], [77943], .contexts []⟩,
    ⟨[77945, 1], [77943], .contexts [
        ⟨5099, true, false, [], [1]⟩,
        ⟨18, false, false, [77943], []⟩,
        ⟨5100, false, false, [], []⟩
      ]⟩,
    ⟨[77947], [77945, 9], .source 39038⟩,
    ⟨[77945, 9], [77947], .contexts [
        ⟨5102, true, false, [], []⟩
      ]⟩,
    ⟨[77945], [77945], .contexts []⟩,
    ⟨[77947, 9], [77945], .contexts [
        ⟨5103, true, false, [], [9]⟩,
        ⟨76, false, false, [77945], []⟩,
        ⟨5104, false, false, [], []⟩
      ]⟩,
    ⟨[77949], [77947, 11], .source 39039⟩,
    ⟨[77947], [77947], .contexts []⟩,
    ⟨[77949, 11], [77947], .contexts [
        ⟨5106, false, false, [], [11]⟩,
        ⟨90, false, false, [77947], []⟩,
        ⟨5107, false, false, [], []⟩
      ]⟩,
    ⟨[77951], [77949, 1], .source 39040⟩,
    ⟨[77949], [77949], .contexts []⟩,
    ⟨[77951, 1], [77949], .contexts [
        ⟨5109, false, false, [], [1]⟩,
        ⟨18, false, false, [77949], []⟩,
        ⟨5110, false, false, [], []⟩
      ]⟩,
    ⟨[77953], [77951, 13], .source 39041⟩,
    ⟨[77951, 13], [77953], .contexts [
        ⟨5112, true, false, [], []⟩
      ]⟩,
    ⟨[77951], [77951], .contexts []⟩,
    ⟨[77953, 13], [77951], .contexts [
        ⟨5113, true, false, [], [13]⟩,
        ⟨98, false, false, [77951], []⟩,
        ⟨5114, false, false, [], []⟩
      ]⟩,
    ⟨[77955], [77953, 15], .source 39042⟩,
    ⟨[77953, 15], [77955], .contexts [
        ⟨5116, true, false, [], []⟩
      ]⟩,
    ⟨[77953], [77953], .contexts []⟩,
    ⟨[77955, 15], [77953], .contexts [
        ⟨5117, true, false, [], [15]⟩,
        ⟨3, false, false, [77953], []⟩,
        ⟨5118, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 080. -/
def y322TCContextRaw080 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77957], [77955, 1], .source 39043⟩,
    ⟨[77955], [77955], .contexts []⟩,
    ⟨[77957, 1], [77955], .contexts [
        ⟨5120, false, false, [], [1]⟩,
        ⟨18, false, false, [77955], []⟩,
        ⟨5121, false, false, [], []⟩
      ]⟩,
    ⟨[77959], [77957, 3], .source 39044⟩,
    ⟨[77957, 3], [77959], .contexts [
        ⟨5123, true, false, [], []⟩
      ]⟩,
    ⟨[77957], [77957], .contexts []⟩,
    ⟨[77959, 3], [77957], .contexts [
        ⟨5124, true, false, [], [3]⟩,
        ⟨35, false, false, [77957], []⟩,
        ⟨5125, false, false, [], []⟩
      ]⟩,
    ⟨[77961], [77959, 5], .source 39045⟩,
    ⟨[77959], [77959], .contexts []⟩,
    ⟨[77961, 5], [77959], .contexts [
        ⟨5127, false, false, [], [5]⟩,
        ⟨49, false, false, [77959], []⟩,
        ⟨5128, false, false, [], []⟩
      ]⟩,
    ⟨[77963], [77961, 1], .source 39046⟩,
    ⟨[77961], [77961], .contexts []⟩,
    ⟨[77963, 1], [77961], .contexts [
        ⟨5130, false, false, [], [1]⟩,
        ⟨18, false, false, [77961], []⟩,
        ⟨5131, false, false, [], []⟩
      ]⟩,
    ⟨[77965], [77963, 9], .source 39047⟩,
    ⟨[77963, 9], [77965], .contexts [
        ⟨5133, true, false, [], []⟩
      ]⟩,
    ⟨[77963], [77963], .contexts []⟩,
    ⟨[77965, 9], [77963], .contexts [
        ⟨5134, true, false, [], [9]⟩,
        ⟨76, false, false, [77963], []⟩,
        ⟨5135, false, false, [], []⟩
      ]⟩,
    ⟨[77967], [77965, 11], .source 39048⟩,
    ⟨[77965, 11], [77967], .contexts [
        ⟨5137, true, false, [], []⟩
      ]⟩,
    ⟨[77965], [77965], .contexts []⟩,
    ⟨[77967, 11], [77965], .contexts [
        ⟨5138, true, false, [], [11]⟩,
        ⟨90, false, false, [77965], []⟩,
        ⟨5139, false, false, [], []⟩
      ]⟩,
    ⟨[77969], [77967, 1], .source 39049⟩,
    ⟨[77967], [77967], .contexts []⟩,
    ⟨[77969, 1], [77967], .contexts [
        ⟨5141, false, false, [], [1]⟩,
        ⟨18, false, false, [77967], []⟩,
        ⟨5142, false, false, [], []⟩
      ]⟩,
    ⟨[77971], [77969, 13], .source 39050⟩,
    ⟨[77969], [77969], .contexts []⟩,
    ⟨[77971, 13], [77969], .contexts [
        ⟨5144, false, false, [], [13]⟩,
        ⟨98, false, false, [77969], []⟩,
        ⟨5145, false, false, [], []⟩
      ]⟩,
    ⟨[77973], [77971, 15], .source 39051⟩,
    ⟨[77971, 15], [77973], .contexts [
        ⟨5147, true, false, [], []⟩
      ]⟩,
    ⟨[77971], [77971], .contexts []⟩,
    ⟨[77973, 15], [77971], .contexts [
        ⟨5148, true, false, [], [15]⟩,
        ⟨3, false, false, [77971], []⟩,
        ⟨5149, false, false, [], []⟩
      ]⟩,
    ⟨[77975], [77973, 1], .source 39052⟩,
    ⟨[77973, 1], [77975], .contexts [
        ⟨5151, true, false, [], []⟩
      ]⟩,
    ⟨[77973], [77973], .contexts []⟩,
    ⟨[77975, 1], [77973], .contexts [
        ⟨5152, true, false, [], [1]⟩,
        ⟨18, false, false, [77973], []⟩,
        ⟨5153, false, false, [], []⟩
      ]⟩,
    ⟨[77977], [77975, 3], .source 39053⟩,
    ⟨[77975, 3], [77977], .contexts [
        ⟨5155, true, false, [], []⟩
      ]⟩,
    ⟨[77975], [77975], .contexts []⟩,
    ⟨[77977, 3], [77975], .contexts [
        ⟨5156, true, false, [], [3]⟩,
        ⟨35, false, false, [77975], []⟩,
        ⟨5157, false, false, [], []⟩
      ]⟩,
    ⟨[77979], [77977, 5], .source 39054⟩,
    ⟨[77977, 5], [77979], .contexts [
        ⟨5159, true, false, [], []⟩
      ]⟩,
    ⟨[77977], [77977], .contexts []⟩,
    ⟨[77979, 5], [77977], .contexts [
        ⟨5160, true, false, [], [5]⟩,
        ⟨49, false, false, [77977], []⟩,
        ⟨5161, false, false, [], []⟩
      ]⟩,
    ⟨[77981], [77979, 1], .source 39055⟩,
    ⟨[77979, 1], [77981], .contexts [
        ⟨5163, true, false, [], []⟩
      ]⟩,
    ⟨[77979], [77979], .contexts []⟩,
    ⟨[77981], [77981], .contexts []⟩,
    ⟨[77973, 15], [77971], .contexts [
        ⟨5150, false, false, [], []⟩
      ]⟩,
    ⟨[77971], [77971], .contexts []⟩,
    ⟨[77971, 13], [77969], .contexts [
        ⟨5146, false, false, [], []⟩
      ]⟩,
    ⟨[77969], [77969], .contexts []⟩,
    ⟨[77979, 5, 3, 1, 15, 13], [77969], .contexts [
        ⟨5162, false, false, [], [3, 1, 15, 13]⟩,
        ⟨5161, false, false, [], [3, 1, 15, 13]⟩,
        ⟨5161, false, false, [], [3, 1, 15, 13]⟩,
        ⟨5158, false, false, [], [1, 15, 13]⟩,
        ⟨5157, false, false, [], [1, 15, 13]⟩,
        ⟨5157, false, false, [], [1, 15, 13]⟩,
        ⟨5154, false, false, [], [15, 13]⟩,
        ⟨5153, false, false, [], [15, 13]⟩,
        ⟨5153, false, false, [], [15, 13]⟩,
        ⟨5167, false, false, [], [13]⟩,
        ⟨5168, false, false, [], [13]⟩,
        ⟨5149, false, false, [], [13]⟩,
        ⟨5149, false, false, [], [13]⟩,
        ⟨5169, false, false, [], []⟩,
        ⟨5170, false, false, [], []⟩,
        ⟨5145, false, false, [], []⟩,
        ⟨5145, false, false, [], []⟩
      ]⟩,
    ⟨[77969, 1], [77967], .contexts [
        ⟨5143, false, false, [], []⟩
      ]⟩,
    ⟨[77967], [77967], .contexts []⟩,
    ⟨[77967, 11], [77965], .contexts [
        ⟨5140, false, false, [], []⟩
      ]⟩,
    ⟨[77965], [77965], .contexts []⟩,
    ⟨[77965, 9], [77963], .contexts [
        ⟨5136, false, false, [], []⟩
      ]⟩,
    ⟨[77963], [77963], .contexts []⟩,
    ⟨[77963, 1], [77961], .contexts [
        ⟨5132, false, false, [], []⟩
      ]⟩,
    ⟨[77961], [77961], .contexts []⟩,
    ⟨[77959], [77959], .contexts []⟩,
    ⟨[77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5], [77959], .contexts [
        ⟨5171, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨5172, false, false, [], [11, 9, 1, 5]⟩,
        ⟨5173, false, false, [], [11, 9, 1, 5]⟩,
        ⟨5142, false, false, [], [11, 9, 1, 5]⟩,
        ⟨5142, false, false, [], [11, 9, 1, 5]⟩,
        ⟨5174, false, false, [], [9, 1, 5]⟩,
        ⟨5175, false, false, [], [9, 1, 5]⟩,
        ⟨5139, false, false, [], [9, 1, 5]⟩,
        ⟨5139, false, false, [], [9, 1, 5]⟩,
        ⟨5176, false, false, [], [1, 5]⟩,
        ⟨5177, false, false, [], [1, 5]⟩,
        ⟨5135, false, false, [], [1, 5]⟩,
        ⟨5135, false, false, [], [1, 5]⟩,
        ⟨5178, false, false, [], [5]⟩,
        ⟨5179, false, false, [], [5]⟩,
        ⟨5131, false, false, [], [5]⟩,
        ⟨5131, false, false, [], [5]⟩,
        ⟨5129, false, false, [], []⟩,
        ⟨5180, false, false, [], []⟩,
        ⟨5128, false, false, [], []⟩,
        ⟨5128, false, false, [], []⟩
      ]⟩,
    ⟨[77959, 3], [77957], .contexts [
        ⟨5126, false, false, [], []⟩
      ]⟩,
    ⟨[77957], [77957], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 081. -/
def y322TCContextRaw081 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77957, 1], [77955], .contexts [
        ⟨5122, false, false, [], []⟩
      ]⟩,
    ⟨[77955], [77955], .contexts []⟩,
    ⟨[77953, 13], [77951], .contexts [
        ⟨5115, false, false, [], []⟩
      ]⟩,
    ⟨[77951], [77951], .contexts []⟩,
    ⟨[77951, 1], [77949], .contexts [
        ⟨5111, false, false, [], []⟩
      ]⟩,
    ⟨[77949], [77949], .contexts []⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1
    ], [77949], .contexts [
        ⟨5181, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨5182, false, false, [], [1, 15, 13, 1]⟩,
        ⟨5183, false, false, [], [1, 15, 13, 1]⟩,
        ⟨5125, false, false, [], [1, 15, 13, 1]⟩,
        ⟨5125, false, false, [], [1, 15, 13, 1]⟩,
        ⟨5184, false, false, [], [15, 13, 1]⟩,
        ⟨5185, false, false, [], [15, 13, 1]⟩,
        ⟨5121, false, false, [], [15, 13, 1]⟩,
        ⟨5121, false, false, [], [15, 13, 1]⟩,
        ⟨5119, false, false, [], [13, 1]⟩,
        ⟨5118, false, false, [], [13, 1]⟩,
        ⟨5118, false, false, [], [13, 1]⟩,
        ⟨5186, false, false, [], [1]⟩,
        ⟨5187, false, false, [], [1]⟩,
        ⟨5114, false, false, [], [1]⟩,
        ⟨5114, false, false, [], [1]⟩,
        ⟨5188, false, false, [], []⟩,
        ⟨5189, false, false, [], []⟩,
        ⟨5110, false, false, [], []⟩,
        ⟨5110, false, false, [], []⟩
      ]⟩,
    ⟨[77947], [77947], .contexts []⟩,
    ⟨[77947, 9], [77945], .contexts [
        ⟨5105, false, false, [], []⟩
      ]⟩,
    ⟨[77945], [77945], .contexts []⟩,
    ⟨[77943, 5], [77941], .contexts [
        ⟨5097, false, false, [], []⟩
      ]⟩,
    ⟨[77941], [77941], .contexts []⟩,
    ⟨[77941, 3], [77939], .contexts [
        ⟨5093, false, false, [], []⟩
      ]⟩,
    ⟨[77939], [77939], .contexts []⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [77939], .contexts [
        ⟨5190, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨5108, false, false, [], [9, 1, 5, 3]⟩,
        ⟨5191, false, false, [], [9, 1, 5, 3]⟩,
        ⟨5107, false, false, [], [9, 1, 5, 3]⟩,
        ⟨5107, false, false, [], [9, 1, 5, 3]⟩,
        ⟨5192, false, false, [], [1, 5, 3]⟩,
        ⟨5193, false, false, [], [1, 5, 3]⟩,
        ⟨5104, false, false, [], [1, 5, 3]⟩,
        ⟨5104, false, false, [], [1, 5, 3]⟩,
        ⟨5101, false, false, [], [5, 3]⟩,
        ⟨5100, false, false, [], [5, 3]⟩,
        ⟨5100, false, false, [], [5, 3]⟩,
        ⟨5194, false, false, [], [3]⟩,
        ⟨5195, false, false, [], [3]⟩,
        ⟨5096, false, false, [], [3]⟩,
        ⟨5096, false, false, [], [3]⟩,
        ⟨5196, false, false, [], []⟩,
        ⟨5197, false, false, [], []⟩,
        ⟨5092, false, false, [], []⟩,
        ⟨5092, false, false, [], []⟩
      ]⟩,
    ⟨[77939, 1], [77937], .contexts [
        ⟨5090, false, false, [], []⟩
      ]⟩,
    ⟨[77937], [77937], .contexts []⟩,
    ⟨[77937, 15], [77935], .contexts [
        ⟨5086, false, false, [], []⟩
      ]⟩,
    ⟨[77935], [77935], .contexts []⟩,
    ⟨[77935, 13], [77933], .contexts [
        ⟨5082, false, false, [], []⟩
      ]⟩,
    ⟨[77933], [77933], .contexts []⟩,
    ⟨[77933, 1], [77931], .contexts [
        ⟨5078, false, false, [], []⟩
      ]⟩,
    ⟨[77931], [77931], .contexts []⟩,
    ⟨[77931, 11], [77929], .contexts [
        ⟨5074, false, false, [], []⟩
      ]⟩,
    ⟨[77929], [77929], .contexts []⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11
    ], [77929], .contexts [
        ⟨5198, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨5199, false, false, [], [15, 13, 1, 11]⟩,
        ⟨5200, false, false, [], [15, 13, 1, 11]⟩,
        ⟨5089, false, false, [], [15, 13, 1, 11]⟩,
        ⟨5089, false, false, [], [15, 13, 1, 11]⟩,
        ⟨5201, false, false, [], [13, 1, 11]⟩,
        ⟨5202, false, false, [], [13, 1, 11]⟩,
        ⟨5085, false, false, [], [13, 1, 11]⟩,
        ⟨5085, false, false, [], [13, 1, 11]⟩,
        ⟨5203, false, false, [], [1, 11]⟩,
        ⟨5204, false, false, [], [1, 11]⟩,
        ⟨5081, false, false, [], [1, 11]⟩,
        ⟨5081, false, false, [], [1, 11]⟩,
        ⟨5205, false, false, [], [11]⟩,
        ⟨5206, false, false, [], [11]⟩,
        ⟨5077, false, false, [], [11]⟩,
        ⟨5077, false, false, [], [11]⟩,
        ⟨5207, false, false, [], []⟩,
        ⟨5208, false, false, [], []⟩,
        ⟨5073, false, false, [], []⟩,
        ⟨5073, false, false, [], []⟩
      ]⟩,
    ⟨[77929, 9], [77927], .contexts [
        ⟨5070, false, false, [], []⟩
      ]⟩,
    ⟨[77927], [77927], .contexts []⟩,
    ⟨[77923], [77923], .contexts []⟩,
    ⟨[77921], [77921], .contexts []⟩,
    ⟨[77919], [77919], .contexts []⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1
    ], [77919], .contexts [
        ⟨5209, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨5210, false, false, [], [1, 5, 3, 1]⟩,
        ⟨5211, false, false, [], [1, 5, 3, 1]⟩,
        ⟨5069, false, false, [], [1, 5, 3, 1]⟩,
        ⟨5069, false, false, [], [1, 5, 3, 1]⟩,
        ⟨5066, false, false, [], [5, 3, 1]⟩,
        ⟨5065, false, false, [], [5, 3, 1]⟩,
        ⟨5065, false, false, [], [5, 3, 1]⟩,
        ⟨5063, false, false, [], [3, 1]⟩,
        ⟨5212, false, false, [], [3, 1]⟩,
        ⟨5062, false, false, [], [3, 1]⟩,
        ⟨5062, false, false, [], [3, 1]⟩,
        ⟨5059, true, false, [], [3, 1]⟩,
        ⟨35, false, false, [77921], [1]⟩,
        ⟨5060, false, false, [], [1]⟩,
        ⟨5213, false, false, [], [1]⟩,
        ⟨5060, false, false, [], [1]⟩,
        ⟨5060, false, false, [], [1]⟩,
        ⟨5056, true, false, [], [1]⟩,
        ⟨18, false, false, [77919], []⟩,
        ⟨5057, false, false, [], []⟩,
        ⟨5214, false, false, [], []⟩,
        ⟨5057, false, false, [], []⟩,
        ⟨5057, false, false, [], []⟩
      ]⟩,
    ⟨[77917], [77917], .contexts []⟩,
    ⟨[77913], [77913], .contexts []⟩,
    ⟨[77911], [77911], .contexts []⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [77911], .contexts [
        ⟨5215, false, false, [], [15, 13, 1, 11]⟩,
        ⟨5053, true, false, [], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [77917], [13, 1, 11]⟩,
        ⟨5054, false, false, [], [13, 1, 11]⟩,
        ⟨5216, false, false, [], [13, 1, 11]⟩,
        ⟨5054, false, false, [], [13, 1, 11]⟩,
        ⟨5054, false, false, [], [13, 1, 11]⟩,
        ⟨5050, true, false, [], [13, 1, 11]⟩,
        ⟨98, false, false, [77915], [1, 11]⟩,
        ⟨5051, false, false, [], [1, 11]⟩,
        ⟨5051, false, false, [], [1, 11]⟩,
        ⟨5051, false, false, [], [1, 11]⟩,
        ⟨5047, true, false, [], [1, 11]⟩,
        ⟨18, false, false, [77913], [11]⟩,
        ⟨5048, false, false, [], [11]⟩,
        ⟨5217, false, false, [], [11]⟩,
        ⟨5048, false, false, [], [11]⟩,
        ⟨5048, false, false, [], [11]⟩,
        ⟨5044, true, false, [], [11]⟩,
        ⟨90, false, false, [77911], []⟩,
        ⟨5045, false, false, [], []⟩,
        ⟨5218, false, false, [], []⟩,
        ⟨5045, false, false, [], []⟩,
        ⟨5045, false, false, [], []⟩
      ]⟩,
    ⟨[77909], [77909], .contexts []⟩,
    ⟨[77907], [77907], .contexts []⟩,
    ⟨[77905], [77905], .contexts []⟩,
    ⟨[77903], [77903], .contexts []⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3
    ], [77903], .contexts [
        ⟨5219, false, false, [], [9, 1, 5, 3]⟩,
        ⟨5041, true, false, [], [9, 1, 5, 3]⟩,
        ⟨76, false, false, [77909], [1, 5, 3]⟩,
        ⟨5042, false, false, [], [1, 5, 3]⟩,
        ⟨5220, false, false, [], [1, 5, 3]⟩,
        ⟨5042, false, false, [], [1, 5, 3]⟩,
        ⟨5042, false, false, [], [1, 5, 3]⟩,
        ⟨5038, true, false, [], [1, 5, 3]⟩,
        ⟨18, false, false, [77907], [5, 3]⟩,
        ⟨5039, false, false, [], [5, 3]⟩,
        ⟨5221, false, false, [], [5, 3]⟩,
        ⟨5039, false, false, [], [5, 3]⟩,
        ⟨5039, false, false, [], [5, 3]⟩,
        ⟨5035, true, false, [], [5, 3]⟩,
        ⟨49, false, false, [77905], [3]⟩,
        ⟨5036, false, false, [], [3]⟩,
        ⟨5222, false, false, [], [3]⟩,
        ⟨5036, false, false, [], [3]⟩,
        ⟨5036, false, false, [], [3]⟩,
        ⟨5032, true, false, [], [3]⟩,
        ⟨35, false, false, [77903], []⟩,
        ⟨5033, false, false, [], []⟩,
        ⟨5223, false, false, [], []⟩,
        ⟨5033, false, false, [], []⟩,
        ⟨5033, false, false, [], []⟩
      ]⟩,
    ⟨[77901], [77901], .contexts []⟩,
    ⟨[77899], [77899], .contexts []⟩,
    ⟨[77897], [77897], .contexts []⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1
    ], [77895], .contexts [
        ⟨5224, false, false, [], [1, 15, 13, 1]⟩,
        ⟨5029, true, false, [], [1, 15, 13, 1]⟩,
        ⟨18, false, false, [77901], [15, 13, 1]⟩,
        ⟨5030, false, false, [], [15, 13, 1]⟩,
        ⟨5225, false, false, [], [15, 13, 1]⟩,
        ⟨5030, false, false, [], [15, 13, 1]⟩,
        ⟨5030, false, false, [], [15, 13, 1]⟩,
        ⟨5026, true, false, [], [15, 13, 1]⟩,
        ⟨3, false, false, [77899], [13, 1]⟩,
        ⟨5027, false, false, [], [13, 1]⟩,
        ⟨5226, false, false, [], [13, 1]⟩,
        ⟨5027, false, false, [], [13, 1]⟩,
        ⟨5027, false, false, [], [13, 1]⟩,
        ⟨5023, true, false, [], [13, 1]⟩,
        ⟨98, false, false, [77897], [1]⟩,
        ⟨5024, false, false, [], [1]⟩,
        ⟨5227, false, false, [], [1]⟩,
        ⟨5024, false, false, [], [1]⟩,
        ⟨5024, false, false, [], [1]⟩,
        ⟨5020, true, false, [], [1]⟩,
        ⟨18, false, false, [77895], []⟩,
        ⟨5021, false, false, [], []⟩,
        ⟨5021, false, false, [], []⟩,
        ⟨5021, false, false, [], []⟩
      ]⟩,
    ⟨[77893], [77893], .contexts []⟩,
    ⟨[77891], [77891], .contexts []⟩,
    ⟨[77889], [77889], .contexts []⟩,
    ⟨[77887], [77887], .contexts []⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [77887], .contexts [
        ⟨5228, false, false, [], [11, 9, 1, 5]⟩,
        ⟨5017, true, false, [], [11, 9, 1, 5]⟩,
        ⟨90, false, false, [77893], [9, 1, 5]⟩,
        ⟨5018, false, false, [], [9, 1, 5]⟩,
        ⟨5229, false, false, [], [9, 1, 5]⟩,
        ⟨5018, false, false, [], [9, 1, 5]⟩,
        ⟨5018, false, false, [], [9, 1, 5]⟩,
        ⟨5014, true, false, [], [9, 1, 5]⟩,
        ⟨76, false, false, [77891], [1, 5]⟩,
        ⟨5015, false, false, [], [1, 5]⟩,
        ⟨5230, false, false, [], [1, 5]⟩,
        ⟨5015, false, false, [], [1, 5]⟩,
        ⟨5015, false, false, [], [1, 5]⟩,
        ⟨5012, false, false, [], [5]⟩,
        ⟨5231, false, false, [], [5]⟩,
        ⟨5011, false, false, [], [5]⟩,
        ⟨5011, false, false, [], [5]⟩,
        ⟨5008, false, false, [], []⟩,
        ⟨5232, false, false, [], []⟩,
        ⟨5007, false, false, [], []⟩,
        ⟨5007, false, false, [], []⟩
      ]⟩,
    ⟨[77885], [77885], .contexts []⟩,
    ⟨[77881], [77881], .contexts []⟩,
    ⟨[77881, 13], [77879], .contexts [
        ⟨4995, true, false, [], [13]⟩,
        ⟨98, false, false, [77879], []⟩,
        ⟨4990, false, false, [], []⟩
      ]⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13
    ], [77879], .contexts [
        ⟨5233, false, false, [], [3, 1, 15, 13]⟩,
        ⟨5003, true, false, [], [3, 1, 15, 13]⟩,
        ⟨35, false, false, [77885], [1, 15, 13]⟩,
        ⟨5004, false, false, [], [1, 15, 13]⟩,
        ⟨5234, false, false, [], [1, 15, 13]⟩,
        ⟨5004, false, false, [], [1, 15, 13]⟩,
        ⟨5004, false, false, [], [1, 15, 13]⟩,
        ⟨5000, true, false, [], [1, 15, 13]⟩,
        ⟨18, false, false, [77883], [15, 13]⟩,
        ⟨5001, false, false, [], [15, 13]⟩,
        ⟨5001, false, false, [], [15, 13]⟩,
        ⟨5001, false, false, [], [15, 13]⟩,
        ⟨4997, true, false, [], [15, 13]⟩,
        ⟨3, false, false, [77881], [13]⟩,
        ⟨4998, false, false, [], [13]⟩,
        ⟨5235, false, false, [], [13]⟩,
        ⟨4998, false, false, [], [13]⟩,
        ⟨4998, false, false, [], [13]⟩,
        ⟨5236, false, false, [], []⟩,
        ⟨4989, false, false, [], []⟩,
        ⟨4990, false, false, [], []⟩,
        ⟨4990, false, false, [], []⟩
      ]⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11
    ], [1059, 77877], .contexts [
        ⟨5237, false, false, [], [1, 11]⟩,
        ⟨4990, true, false, [], [1, 11]⟩,
        ⟨4990, true, false, [], [1, 11]⟩,
        ⟨4989, true, false, [], [1, 11]⟩,
        ⟨4988, true, false, [], [1, 11]⟩,
        ⟨992, false, false, [77877], [11]⟩,
        ⟨993, false, false, [77877], [11]⟩,
        ⟨4991, false, false, [], [11, 11]⟩,
        ⟨4988, false, false, [1059], [11]⟩,
        ⟨4992, false, false, [], [11]⟩,
        ⟨4993, false, false, [], [11]⟩,
        ⟨4905, true, false, [], [77879, 11]⟩,
        ⟨4992, false, false, [], [11]⟩,
        ⟨4993, false, false, [], [11]⟩,
        ⟨4993, false, false, [], [11]⟩,
        ⟨4988, true, false, [1059], [11]⟩,
        ⟨90, false, false, [1059, 77877], []⟩,
        ⟨4977, false, false, [1059], []⟩,
        ⟨4982, false, false, [], []⟩,
        ⟨4983, false, false, [], []⟩,
        ⟨4984, false, false, [], []⟩
      ]⟩,
    ⟨[1079], [1059, 269], .source 604⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [1079, 77869], .contexts [
        ⟨5238, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨4975, false, false, [1059], [1, 5, 3, 1]⟩,
        ⟨4978, false, false, [], [1, 5, 3, 1]⟩,
        ⟨4979, false, false, [], [1, 5, 3, 1]⟩,
        ⟨4981, false, false, [], [1, 5, 3, 1]⟩,
        ⟨4972, false, false, [1059], [5, 3, 1]⟩,
        ⟨4967, false, false, [], [5, 3, 1]⟩,
        ⟨4968, false, false, [], [5, 3, 1]⟩,
        ⟨4969, false, false, [], [5, 3, 1]⟩,
        ⟨4963, false, false, [1059], [3, 1]⟩,
        ⟨4954, false, false, [], [3, 1]⟩,
        ⟨4955, false, false, [], [3, 1]⟩,
        ⟨4957, false, false, [], [3, 1]⟩,
        ⟨4950, false, false, [1059], [1]⟩,
        ⟨4921, false, false, [], [1]⟩,
        ⟨4922, false, false, [], [1]⟩,
        ⟨4923, false, false, [], [1]⟩,
        ⟨4920, false, false, [1059], []⟩,
        ⟨5239, true, false, [], [77869]⟩
      ]⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9
    ], [1079, 77343], .contexts [
        ⟨5240, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨4913, false, false, [1079], [13, 1, 11, 9]⟩,
        ⟨4893, false, false, [1079], [1, 11, 9]⟩,
        ⟨4847, false, false, [1079], [11, 9]⟩,
        ⟨4824, false, false, [1079], [9]⟩,
        ⟨1332, false, false, [1079], []⟩
      ]⟩,
    ⟨[1081], [1079, 261], .source 605⟩,
    ⟨[1083], [1081, 503], .source 606⟩,
    ⟨[1085], [1083, 19], .source 607⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15
    ], [1085, 77117], .contexts [
        ⟨5241, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨2774, false, false, [1079], [5, 3, 1, 15]⟩,
        ⟨2764, false, false, [1079], [3, 1, 15]⟩,
        ⟨5242, true, false, [], [77487, 3, 1, 15]⟩,
        ⟨2762, false, false, [1081], [1, 15]⟩,
        ⟨5243, true, false, [], [77115, 1, 15]⟩,
        ⟨393, false, false, [1083], [15]⟩,
        ⟨735, true, false, [1083], [77115, 15]⟩,
        ⟨5244, true, false, [], [77115, 15]⟩,
        ⟨395, false, false, [1085], []⟩
      ]⟩,
    ⟨[1087], [1085, 31], .source 608⟩,
    ⟨[1089], [1087, 19], .source 609⟩]

/-- Exact literal claimed equations and contextual derivations, block 082. -/
def y322TCContextRaw082 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1091], [1089, 211], .source 610⟩,
    ⟨[1093], [1091, 217], .source 611⟩,
    ⟨[1095], [1093, 479], .source 612⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1
    ], [1095, 77861], .contexts [
        ⟨5245, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨413, false, false, [1085], [1, 11, 9, 1]⟩,
        ⟨740, true, false, [1085], [77117, 1, 11, 9, 1]⟩,
        ⟨5246, true, false, [], [77117, 1, 11, 9, 1]⟩,
        ⟨403, false, false, [1087], [11, 9, 1]⟩,
        ⟨735, true, false, [1087], [77117, 11, 9, 1]⟩,
        ⟨5247, true, false, [], [77117, 11, 9, 1]⟩,
        ⟨4821, false, false, [1089], [9, 1]⟩,
        ⟨5248, true, false, [], [77861, 9, 1]⟩,
        ⟨4820, false, false, [1091], [1]⟩,
        ⟨5249, true, false, [], [77861, 1]⟩,
        ⟨4816, false, false, [1093], []⟩,
        ⟨5250, true, false, [], [77861]⟩
      ]⟩,
    ⟨[1097], [1095, 1047], .source 613⟩,
    ⟨[1099], [1097, 933], .source 614⟩,
    ⟨[77849], [917, 77847], .contexts [
        ⟨4627, false, false, [], []⟩,
        ⟨4626, false, false, [], []⟩
      ]⟩,
    ⟨[1101], [1099, 917], .source 615⟩,
    ⟨[1103], [1101, 925], .source 616⟩,
    ⟨[1105], [1103, 137], .source 617⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13
    ], [1105, 77221], .contexts [
        ⟨5251, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨4819, false, false, [1095], [3, 1, 15, 13]⟩,
        ⟨5252, true, false, [], [77847, 3, 1, 15, 13]⟩,
        ⟨4642, false, false, [1097], [1, 15, 13]⟩,
        ⟨5253, true, false, [], [77847, 1, 15, 13]⟩,
        ⟨4528, false, false, [1099], [15, 13]⟩,
        ⟨5254, false, false, [1099], [15, 13]⟩,
        ⟨5255, true, false, [], [77847, 15, 13]⟩,
        ⟨4632, false, false, [1101], [13]⟩,
        ⟨5256, true, false, [], [77217, 13]⟩,
        ⟨948, false, false, [1103], []⟩,
        ⟨5257, true, false, [], [77221]⟩
      ]⟩,
    ⟨[1107], [1105, 107], .source 618⟩,
    ⟨[1109], [1107, 159], .source 619⟩,
    ⟨[1111], [1109, 111], .source 620⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [1111, 77113], .contexts [
        ⟨5258, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨915, false, false, [1105], [11, 9, 1, 5]⟩,
        ⟨5259, true, false, [], [77225, 11, 9, 1, 5]⟩,
        ⟨1120, false, false, [1107], [9, 1, 5]⟩,
        ⟨1114, false, false, [1107], [1, 5]⟩,
        ⟨5260, true, false, [], [77235, 1, 5]⟩,
        ⟨1820, false, false, [1109], [5]⟩,
        ⟨1829, false, false, [1109], []⟩,
        ⟨5261, true, false, [], [77113]⟩
      ]⟩,
    ⟨[1113], [1111, 505], .source 621⟩,
    ⟨[1115], [1113, 257], .source 622⟩,
    ⟨[1117], [1115, 251], .source 623⟩,
    ⟨[
      77979, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1
    ], [1117, 77343], .contexts [
        ⟨5262, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨2692, false, false, [1111], [1, 15, 13, 1]⟩,
        ⟨5263, true, false, [], [77485, 1, 15, 13, 1]⟩,
        ⟨2685, false, false, [1113], [15, 13, 1]⟩,
        ⟨5264, true, false, [], [77485, 15, 13, 1]⟩,
        ⟨2702, false, false, [1115], [13, 1]⟩,
        ⟨5265, true, false, [], [77485, 13, 1]⟩,
        ⟨2754, false, false, [1117], [1]⟩,
        ⟨2775, false, false, [1117], []⟩
      ]⟩,
    ⟨[1117, 77345], [1117, 77345], .contexts []⟩,
    ⟨[1117, 77345], [1117, 77345], .contexts []⟩,
    ⟨[77981, 9], [77981, 9], .contexts []⟩,
    ⟨[77981, 9], [1117, 77345], .contexts [
        ⟨5269, false, false, [], []⟩,
        ⟨5166, true, false, [], [9]⟩,
        ⟨5166, true, false, [], [9]⟩,
        ⟨5164, true, false, [], [9]⟩,
        ⟨765, false, false, [77979], []⟩,
        ⟨774, false, false, [77979], []⟩,
        ⟨5266, false, false, [], [11]⟩,
        ⟨1336, false, false, [1117], []⟩,
        ⟨5267, false, false, [], []⟩,
        ⟨5268, false, false, [], []⟩,
        ⟨1589, false, false, [1117], []⟩,
        ⟨24, true, false, [], [1117, 77345]⟩
      ]⟩,
    ⟨[1119], [1116], .source 624⟩,
    ⟨[77345, 9], [1119, 77981], .contexts [
        ⟨5270, true, false, [1116], [9]⟩,
        ⟨76, false, false, [1116, 77981], []⟩,
        ⟨5271, true, false, [], [77981]⟩
      ]⟩,
    ⟨[1121], [1117, 271], .source 625⟩,
    ⟨[1121, 77345], [1121, 77345], .contexts []⟩,
    ⟨[1121, 77345], [1121, 77345], .contexts []⟩,
    ⟨[77979, 9], [77979, 9], .contexts []⟩,
    ⟨[77979, 9], [1121, 77345], .contexts [
        ⟨5276, false, false, [], []⟩,
        ⟨5165, true, false, [], [9]⟩,
        ⟨5165, true, false, [], [9]⟩,
        ⟨5165, true, false, [], [9]⟩,
        ⟨18, true, false, [77979], [9]⟩,
        ⟨5164, false, false, [], [1, 9]⟩,
        ⟨786, false, false, [77981], []⟩,
        ⟨788, false, false, [77981], []⟩,
        ⟨5269, false, false, [], [1, 9, 1]⟩,
        ⟨5270, false, false, [], [1, 9, 1]⟩,
        ⟨5267, false, false, [], [1, 9, 1]⟩,
        ⟨5268, false, false, [], [1, 9, 1]⟩,
        ⟨5268, false, false, [], [1, 9, 1]⟩,
        ⟨1340, false, false, [1117], [9, 1]⟩,
        ⟨1598, false, false, [1117], [1]⟩,
        ⟨5273, true, false, [], [77347, 1]⟩,
        ⟨1342, false, false, [1121], []⟩,
        ⟨5274, false, false, [], []⟩,
        ⟨5275, false, false, [], []⟩,
        ⟨1589, false, false, [1121], []⟩
      ]⟩,
    ⟨[77979, 9], [1121, 77345], .contexts [
        ⟨5277, false, false, [], []⟩,
        ⟨24, true, false, [], [1121, 77345]⟩
      ]⟩,
    ⟨[1123], [1120], .source 626⟩,
    ⟨[1119, 77981], [1119, 77981], .contexts []⟩,
    ⟨[1125], [1117, 1123], .source 627⟩,
    ⟨[77979, 9], [1121, 77345], .contexts [
        ⟨5276, false, false, [], []⟩,
        ⟨5278, false, false, [], []⟩,
        ⟨5274, false, false, [], []⟩,
        ⟨5275, false, false, [], []⟩,
        ⟨5275, false, false, [], []⟩
      ]⟩,
    ⟨[1127], [1121, 491], .source 628⟩,
    ⟨[77981], [1125, 77979], .contexts [
        ⟨5280, true, false, [1118], []⟩,
        ⟨5280, true, false, [1118], []⟩,
        ⟨5272, true, false, [1118], []⟩,
        ⟨5278, true, false, [1118, 1120], [9]⟩,
        ⟨76, false, false, [1118, 1120, 77979], []⟩,
        ⟨5279, true, false, [1118], [77979]⟩,
        ⟨5271, false, true, [], [1123, 77979]⟩,
        ⟨5281, true, false, [], [77979]⟩
      ]⟩,
    ⟨[1129], [1119, 1125], .source 629⟩,
    ⟨[1131], [1127, 1129], .source 630⟩,
    ⟨[77979], [77979], .contexts []⟩,
    ⟨[1133], [1130], .source 631⟩,
    ⟨[1130], [1130], .contexts []⟩,
    ⟨[1135], [1121, 261], .source 632⟩,
    ⟨[1137], [1135, 1129], .source 633⟩,
    ⟨[1137, 77977], [1137, 77977], .contexts []⟩,
    ⟨[77979], [1137, 77977], .contexts [
        ⟨5287, false, false, [], []⟩,
        ⟨802, true, false, [77979], []⟩,
        ⟨5282, false, false, [], [5, 9, 5]⟩,
        ⟨1621, false, false, [1121], [9, 5]⟩,
        ⟨5290, true, false, [], [77345, 9, 5]⟩,
        ⟨5272, false, false, [1135], [5]⟩,
        ⟨5284, false, false, [1135, 1119], [5]⟩,
        ⟨5285, true, false, [1135], [77979, 5]⟩,
        ⟨5291, true, false, [], [77979, 5]⟩,
        ⟨5162, false, false, [1137], []⟩,
        ⟨5292, false, false, [], []⟩
      ]⟩,
    ⟨[1139], [1125, 1137], .source 634⟩,
    ⟨[77981], [1139, 77977], .contexts [
        ⟨5284, false, false, [], []⟩,
        ⟨5293, false, false, [1125], []⟩,
        ⟨5294, true, false, [], [77977]⟩
      ]⟩,
    ⟨[1141], [1136], .source 635⟩,
    ⟨[1143], [1141, 1139], .source 636⟩,
    ⟨[1145], [1141, 1121], .source 637⟩,
    ⟨[77979], [1137, 77977], .contexts [
        ⟨5293, false, false, [], []⟩,
        ⟨5292, false, false, [], []⟩
      ]⟩,
    ⟨[1147], [1133, 1137], .source 638⟩,
    ⟨[1149], [1141, 1147], .source 639⟩,
    ⟨[77977], [1148, 77975], .contexts [
        ⟨5301, false, false, [1148], [77977]⟩,
        ⟨5296, false, false, [1148], [1147, 77977]⟩,
        ⟨5300, false, false, [1148, 1136], [77977]⟩,
        ⟨5299, true, false, [1148, 1136, 1133], []⟩,
        ⟨5288, false, false, [1148, 1136], [77979]⟩,
        ⟨5289, false, false, [1148, 1136], [77979]⟩,
        ⟨5289, false, false, [1148, 1136], [77979]⟩,
        ⟨5287, true, false, [1148, 1136, 1130], []⟩,
        ⟨2415, true, false, [1148, 1136, 1130, 77979], []⟩,
        ⟨5282, false, false, [1148, 1136, 1130], [3, 9, 3]⟩,
        ⟨2614, false, false, [1148, 1136, 1130, 1121], [9, 3]⟩,
        ⟨5283, true, false, [1148, 1136, 1130], [77345, 9, 3]⟩,
        ⟨5272, false, false, [1148, 1136, 1130, 1127], [3]⟩,
        ⟨5284, false, false, [1148, 1136, 1130, 1127, 1119], [3]⟩,
        ⟨5285, true, false, [1148, 1136, 1130, 1127], [77979, 3]⟩,
        ⟨5286, true, false, [1148, 1136, 1130], [77979, 3]⟩,
        ⟨5299, false, false, [1148, 1136], [3]⟩,
        ⟨5158, false, false, [1148], []⟩
      ]⟩,
    ⟨[1151], [1148], .source 640⟩,
    ⟨[77977], [1151, 77975], .contexts [
        ⟨5302, false, false, [], []⟩,
        ⟨5303, true, false, [], [77975]⟩
      ]⟩,
    ⟨[1153], [1137, 1151], .source 641⟩,
    ⟨[1149], [1150], .contexts [
        ⟨5303, true, true, [], []⟩
      ]⟩,
    ⟨[1155], [1149, 1153], .source 642⟩,
    ⟨[77977], [1151, 77975], .contexts [
        ⟨5304, false, false, [], []⟩
      ]⟩,
    ⟨[1157], [1149, 1145], .source 643⟩,
    ⟨[1159], [1143, 1151], .source 644⟩,
    ⟨[1161], [1149, 1159], .source 645⟩]

/-- Exact literal claimed equations and contextual derivations, block 083. -/
def y322TCContextRaw083 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1163], [1160], .source 646⟩,
    ⟨[77975], [1163, 77973], .contexts [
        ⟨5311, false, false, [1160], [77975]⟩,
        ⟨5306, false, false, [1160], [1159, 77975]⟩,
        ⟨5310, false, false, [1160, 1150], [77975]⟩,
        ⟨5308, true, false, [1160, 1150, 1143], []⟩,
        ⟨5297, false, false, [1160, 1150], [77977]⟩,
        ⟨5296, false, false, [1160, 1150], [1139, 77977]⟩,
        ⟨5295, true, false, [1160, 1150, 1136], []⟩,
        ⟨5164, true, false, [1160, 1150, 1136], []⟩,
        ⟨5293, false, false, [1160, 1150, 1136], [1]⟩,
        ⟨5308, false, false, [1160, 1150], [1]⟩,
        ⟨5154, false, false, [1160], []⟩,
        ⟨5312, true, false, [], [77973]⟩
      ]⟩,
    ⟨[1165], [1151, 1163], .source 647⟩,
    ⟨[1161], [1162], .contexts [
        ⟨5312, true, true, [], []⟩
      ]⟩,
    ⟨[1161], [1162], .contexts [
        ⟨5315, false, false, [], []⟩
      ]⟩,
    ⟨[1162], [1162], .contexts []⟩,
    ⟨[1167], [1161, 1165], .source 648⟩,
    ⟨[1163, 77973], [1163, 77973], .contexts []⟩,
    ⟨[77975], [1163, 77973], .contexts [
        ⟨5313, false, false, [], []⟩,
        ⟨5319, false, false, [], []⟩
      ]⟩,
    ⟨[1169], [1161, 1155], .source 649⟩,
    ⟨[1171], [1169, 1163], .source 650⟩,
    ⟨[1173], [1161, 1157], .source 651⟩,
    ⟨[1173, 77345], [1173, 77345], .contexts []⟩,
    ⟨[77973, 9], [1173, 77345], .contexts [
        ⟨5313, true, false, [1162], [9]⟩,
        ⟨5304, true, false, [1162, 1150], [9]⟩,
        ⟨5293, true, false, [1162, 1150, 1136], [9]⟩,
        ⟨5278, false, false, [1162, 1150, 1136], []⟩,
        ⟨5274, false, false, [1162, 1150, 1136], []⟩,
        ⟨5296, true, false, [1162, 1150], [1121, 77345]⟩,
        ⟨5298, true, false, [1162, 1150], [77345]⟩,
        ⟨5306, true, false, [1162], [1145, 77345]⟩,
        ⟨5309, true, false, [1162], [77345]⟩,
        ⟨5315, true, false, [], [1157, 77345]⟩,
        ⟨5323, true, false, [], [77345]⟩,
        ⟨5324, false, false, [], []⟩,
        ⟨5324, false, false, [], []⟩
      ]⟩,
    ⟨[1175], [1173, 269], .source 652⟩,
    ⟨[1177], [1139, 1151], .source 653⟩,
    ⟨[1179], [1177, 1163], .source 654⟩,
    ⟨[77981], [1179, 77973], .contexts [
        ⟨5295, false, false, [], []⟩,
        ⟨5304, false, false, [1139], []⟩,
        ⟨5327, true, false, [], [77975]⟩,
        ⟨5313, false, false, [1177], []⟩,
        ⟨5328, true, false, [], [77973]⟩
      ]⟩,
    ⟨[1181], [1119, 1179], .source 655⟩,
    ⟨[1183], [1175, 1181], .source 656⟩,
    ⟨[77973, 13], [77973, 13], .contexts []⟩,
    ⟨[77973], [77973], .contexts []⟩,
    ⟨[1185], [1182], .source 657⟩,
    ⟨[1182], [1182], .contexts []⟩,
    ⟨[1185], [1182], .contexts [
        ⟨5334, false, false, [], []⟩,
        ⟨5335, false, false, [], []⟩,
        ⟨5335, false, false, [], []⟩
      ]⟩,
    ⟨[77973, 13], [1185, 77973], .contexts [
        ⟨5332, false, false, [], []⟩,
        ⟨5331, false, false, [1182], [77973, 13]⟩,
        ⟨5330, false, false, [1182, 1175], [77973, 13]⟩,
        ⟨5329, true, false, [1182, 1175, 1119], [13]⟩,
        ⟨5272, true, false, [1182, 1175], [13]⟩,
        ⟨5326, false, false, [1182], [77345, 9, 13]⟩,
        ⟨1593, true, false, [1182, 1173], [9, 13]⟩,
        ⟨5325, true, false, [1182], [13, 9, 13]⟩,
        ⟨828, false, false, [1182, 77973], []⟩,
        ⟨5333, false, false, [1182], []⟩,
        ⟨5336, true, false, [], [77973]⟩
      ]⟩,
    ⟨[1187], [1173, 827], .source 658⟩,
    ⟨[77973, 15], [77971], .contexts [
        ⟨5167, false, false, [], []⟩,
        ⟨5168, false, false, [], []⟩,
        ⟨5149, false, false, [], []⟩,
        ⟨5149, false, false, [], []⟩
      ]⟩,
    ⟨[77973, 14], [77973, 15], .contexts [
        ⟨20, false, false, [77973], []⟩
      ]⟩,
    ⟨[77711, 9], [77711, 9], .contexts []⟩,
    ⟨[77971], [77971], .contexts []⟩,
    ⟨[1189], [1186], .source 659⟩,
    ⟨[1186], [1186], .contexts []⟩,
    ⟨[77711, 9], [1189, 77971], .contexts [
        ⟨5341, false, false, [], []⟩,
        ⟨5338, false, false, [1186], [77711, 9]⟩,
        ⟨4021, true, false, [1186, 1173], [9]⟩,
        ⟨5325, true, false, [1186], [15, 9]⟩,
        ⟨1636, false, false, [1186, 77973], []⟩,
        ⟨5340, false, false, [1186], []⟩,
        ⟨5339, false, false, [1186], []⟩,
        ⟨5342, false, false, [1186], []⟩,
        ⟨5344, true, false, [], [77971]⟩,
        ⟨5344, true, false, [], [77971]⟩,
        ⟨5343, true, false, [], [77971]⟩
      ]⟩,
    ⟨[1171, 77973], [1171, 77973], .contexts []⟩,
    ⟨[1171, 77971, 5], [77973, 14], .contexts [
        ⟨5150, true, false, [1171], [5]⟩,
        ⟨5346, true, false, [], [15, 5]⟩,
        ⟨5346, true, false, [], [15, 5]⟩,
        ⟨5322, false, false, [], [77973, 15, 5]⟩,
        ⟨5321, false, false, [], [1163, 77973, 15, 5]⟩,
        ⟨5315, false, false, [], [1155, 1163, 77973, 15, 5]⟩,
        ⟨5320, true, false, [1162, 1155], [15, 5]⟩,
        ⟨5307, false, false, [1162], [77975, 15, 5]⟩,
        ⟨5306, false, false, [1162], [1153, 77975, 15, 5]⟩,
        ⟨5305, false, false, [1162, 1150], [77975, 15, 5]⟩,
        ⟨5304, true, false, [1162, 1150, 1137], [15, 5]⟩,
        ⟨5299, true, false, [1162, 1150], [15, 5]⟩,
        ⟨5160, true, false, [1162, 1150], [15, 5]⟩,
        ⟨5304, false, false, [1162, 1150], [5, 15, 5]⟩,
        ⟨5313, false, false, [1162], [5, 15, 5]⟩,
        ⟨2006, false, false, [77973], []⟩
      ]⟩,
    ⟨[77971, 5], [77971, 5], .contexts []⟩,
    ⟨[1191], [1170], .source 660⟩,
    ⟨[1191], [1191], .contexts []⟩,
    ⟨[1170], [1170], .contexts []⟩,
    ⟨[1191], [1170], .contexts [
        ⟨5350, false, false, [], []⟩,
        ⟨5349, false, false, [], []⟩,
        ⟨5351, false, false, [], []⟩,
        ⟨5351, false, false, [], []⟩
      ]⟩,
    ⟨[77971, 5], [1191, 77971], .contexts [
        ⟨5348, false, false, [], []⟩,
        ⟨5347, false, false, [1170], []⟩,
        ⟨5340, false, false, [1170], []⟩,
        ⟨5339, false, false, [1170], []⟩,
        ⟨5342, false, false, [1170], []⟩,
        ⟨5352, true, false, [], [77971]⟩
      ]⟩,
    ⟨[1, 15, 1], [14], .contexts [
        ⟨198, false, false, [], [14]⟩
      ]⟩,
    ⟨[77971, 1], [77971, 1], .contexts []⟩,
    ⟨[1161], [1162], .contexts [
        ⟨5316, false, false, [], []⟩,
        ⟨5317, false, false, [], []⟩,
        ⟨5317, false, false, [], []⟩
      ]⟩,
    ⟨[77971, 1], [1161, 77971], .contexts [
        ⟨5355, false, false, [], []⟩,
        ⟨5150, true, false, [], [1]⟩,
        ⟨5319, true, false, [1162], [15, 1]⟩,
        ⟨5319, true, false, [1162], [15, 1]⟩,
        ⟨5320, true, false, [1162], [15, 1]⟩,
        ⟨5152, true, false, [1162], [15, 1]⟩,
        ⟨5354, false, false, [1162, 77973], []⟩,
        ⟨5340, false, false, [1162], []⟩,
        ⟨5339, false, false, [1162], []⟩,
        ⟨5342, false, false, [1162], []⟩,
        ⟨5356, true, false, [], [77971]⟩
      ]⟩,
    ⟨[1167, 77973], [1167, 77973], .contexts []⟩,
    ⟨[77971, 3], [1166, 77971], .contexts [
        ⟨5150, true, false, [], [3]⟩,
        ⟨5358, true, false, [1166], [15, 3]⟩,
        ⟨5358, true, false, [1166], [15, 3]⟩,
        ⟨5318, false, false, [1166], [77973, 15, 3]⟩,
        ⟨5316, false, false, [1166], [1165, 77973, 15, 3]⟩,
        ⟨5317, false, false, [1166], [1165, 77973, 15, 3]⟩,
        ⟨5314, false, false, [1166, 1162], [77973, 15, 3]⟩,
        ⟨5313, true, false, [1166, 1162, 1151], [15, 3]⟩,
        ⟨5308, true, false, [1166, 1162], [15, 3]⟩,
        ⟨5156, true, false, [1166, 1162], [15, 3]⟩,
        ⟨5313, false, false, [1166, 1162], [3, 15, 3]⟩,
        ⟨900, false, false, [1166, 77973], []⟩,
        ⟨5340, false, false, [1166], []⟩,
        ⟨5339, false, false, [1166], []⟩
      ]⟩,
    ⟨[1193], [1166], .source 661⟩,
    ⟨[1166], [1166], .contexts []⟩,
    ⟨[1185, 77973], [1185, 77973], .contexts []⟩,
    ⟨[1185, 77969], [1185, 77969], .contexts []⟩,
    ⟨[1185, 77969], [1185, 77969], .contexts []⟩,
    ⟨[15, 13, 15], [12, 14, 12], .contexts [
        ⟨407, false, false, [], [12, 14, 12]⟩
      ]⟩,
    ⟨[77969, 15], [77969, 15], .contexts []⟩,
    ⟨[77969], [77969], .contexts []⟩,
    ⟨[77969, 15], [1185, 77969], .contexts [
        ⟨5366, false, false, [], []⟩,
        ⟨5145, true, false, [], [15]⟩,
        ⟨5145, true, false, [], [15]⟩,
        ⟨5170, true, false, [], [15]⟩,
        ⟨5169, true, false, [], [15]⟩,
        ⟨5339, true, false, [], [13, 15]⟩,
        ⟨5365, false, false, [77973], []⟩,
        ⟨409, false, false, [77973], []⟩,
        ⟨5332, false, false, [], [15, 13]⟩,
        ⟨5337, false, false, [], [15, 13]⟩,
        ⟨5362, false, false, [], [15, 13]⟩,
        ⟨5362, false, false, [], [15, 13]⟩,
        ⟨5150, false, false, [1185], [13]⟩,
        ⟨5146, false, false, [1185], []⟩,
        ⟨5363, false, false, [], []⟩,
        ⟨5364, false, false, [], []⟩,
        ⟨5367, false, false, [1185], []⟩,
        ⟨24, true, false, [], [1185, 77969]⟩
      ]⟩,
    ⟨[1189, 77971], [1189, 77971], .contexts []⟩,
    ⟨[1189, 77969], [1189, 77969], .contexts []⟩,
    ⟨[1188], [1188], .contexts []⟩,
    ⟨[77969, 9], [1187, 77709], .contexts [
        ⟨5370, true, false, [1188], [9]⟩,
        ⟨5146, true, false, [], [9]⟩,
        ⟨5369, true, false, [1188], [13, 9]⟩,
        ⟨5369, true, false, [1188], [13, 9]⟩,
        ⟨5345, true, false, [1188], [13, 9]⟩,
        ⟨5341, true, false, [1188], [13, 9]⟩,
        ⟨926, false, false, [1188, 77711], []⟩,
        ⟨4065, false, false, [1188], []⟩,
        ⟨4022, false, false, [1188], []⟩,
        ⟨4029, false, false, [1188], []⟩,
        ⟨5371, true, false, [], [77709]⟩,
        ⟨5371, true, false, [], [77709]⟩,
        ⟨5343, false, true, [], [77709]⟩
      ]⟩,
    ⟨[1191, 77971], [1191, 77971], .contexts []⟩,
    ⟨[77971, 13], [77969], .contexts [
        ⟨5169, false, false, [], []⟩,
        ⟨5170, false, false, [], []⟩,
        ⟨5145, false, false, [], []⟩,
        ⟨5145, false, false, [], []⟩
      ]⟩,
    ⟨[77969, 5], [77969, 5], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 084. -/
def y322TCContextRaw084 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1171], [1190], .contexts [
        ⟨5349, true, true, [], []⟩
      ]⟩,
    ⟨[1190], [1190], .contexts []⟩,
    ⟨[1171], [1190], .contexts [
        ⟨5376, false, false, [], []⟩,
        ⟨5377, false, false, [], []⟩,
        ⟨5377, false, false, [], []⟩
      ]⟩,
    ⟨[1161, 77971], [1161, 77971], .contexts []⟩,
    ⟨[77967, 13], [77967, 13], .contexts []⟩,
    ⟨[77967], [77967], .contexts []⟩,
    ⟨[1160], [1160], .contexts []⟩,
    ⟨[77967, 13], [1163, 77967], .contexts [
        ⟨5380, false, false, [], []⟩,
        ⟨5143, true, false, [], [13]⟩,
        ⟨5146, true, false, [], [1, 13]⟩,
        ⟨5379, true, false, [1160], [13, 1, 13]⟩,
        ⟨5379, true, false, [1160], [13, 1, 13]⟩,
        ⟨5357, true, false, [1160], [13, 1, 13]⟩,
        ⟨5355, true, false, [1160], [13, 1, 13]⟩,
        ⟨1587, false, false, [1160, 77971], []⟩,
        ⟨190, false, false, [1160, 77971], []⟩,
        ⟨5374, false, false, [1160], [1]⟩,
        ⟨5172, false, false, [1160], []⟩,
        ⟨5173, false, false, [1160], []⟩,
        ⟨5142, false, false, [1160], []⟩,
        ⟨5142, false, false, [1160], []⟩,
        ⟨5381, false, false, [1160], []⟩,
        ⟨5382, true, false, [], [77967]⟩,
        ⟨5382, true, false, [], [77967]⟩,
        ⟨5312, true, false, [], [77967]⟩
      ]⟩,
    ⟨[77969, 1], [77967], .contexts [
        ⟨5172, false, false, [], []⟩,
        ⟨5173, false, false, [], []⟩,
        ⟨5142, false, false, [], []⟩,
        ⟨5142, false, false, [], []⟩
      ]⟩,
    ⟨[77969, 0], [77969, 1], .contexts [
        ⟨19, false, false, [77969], []⟩
      ]⟩,
    ⟨[77967, 15], [77967, 15], .contexts []⟩,
    ⟨[1184], [1184], .contexts []⟩,
    ⟨[1183], [1184], .contexts [
        ⟨5334, true, true, [], []⟩,
        ⟨5387, false, false, [], []⟩,
        ⟨5387, false, false, [], []⟩
      ]⟩,
    ⟨[1171, 77969], [1171, 77969], .contexts []⟩,
    ⟨[77969, 5], [1171, 77969], .contexts [
        ⟨5375, false, false, [], []⟩,
        ⟨5375, false, false, [], []⟩,
        ⟨5146, true, false, [], [5]⟩,
        ⟨5373, true, false, [1190], [13, 5]⟩,
        ⟨5373, true, false, [1190], [13, 5]⟩,
        ⟨5353, true, false, [1190], [13, 5]⟩,
        ⟨5348, true, false, [1190], [13, 5]⟩,
        ⟨1578, false, false, [1190, 77971], []⟩,
        ⟨108, false, false, [1190, 77971], []⟩,
        ⟨5374, false, false, [1190], []⟩,
        ⟨5367, false, false, [1190], []⟩,
        ⟨5378, true, false, [], [77969]⟩,
        ⟨5389, false, false, [], []⟩,
        ⟨5389, false, false, [], []⟩
      ]⟩,
    ⟨[77967, 5], [77967, 5], .contexts []⟩,
    ⟨[1163, 77967], [1163, 77967], .contexts []⟩,
    ⟨[77967, 11], [77965], .contexts [
        ⟨5174, false, false, [], []⟩,
        ⟨5175, false, false, [], []⟩,
        ⟨5139, false, false, [], []⟩,
        ⟨5139, false, false, [], []⟩
      ]⟩,
    ⟨[77967, 10], [77967, 11], .contexts [
        ⟨91, false, false, [77967], []⟩
      ]⟩,
    ⟨[77965], [77965], .contexts []⟩,
    ⟨[1183, 77967], [1183, 77967], .contexts []⟩,
    ⟨[77967, 15], [1183, 77967], .contexts [
        ⟨5386, false, false, [], []⟩,
        ⟨5386, false, false, [], []⟩,
        ⟨5143, true, false, [], [15]⟩,
        ⟨5364, true, false, [1184], [1, 15]⟩,
        ⟨5364, true, false, [1184], [1, 15]⟩,
        ⟨5363, true, false, [1184], [1, 15]⟩,
        ⟨5368, true, false, [1184], [1, 15]⟩,
        ⟨5366, true, false, [1184], [1, 15]⟩,
        ⟨2778, false, false, [1184, 77969], []⟩,
        ⟨5385, false, false, [1184], []⟩,
        ⟨5384, false, false, [1184], []⟩,
        ⟨5381, false, false, [1184], []⟩,
        ⟨5388, true, false, [], [77967]⟩,
        ⟨5396, false, false, [], []⟩,
        ⟨5396, false, false, [], []⟩
      ]⟩,
    ⟨[77965, 15], [77965, 15], .contexts []⟩,
    ⟨[77965, 15], [1185, 77965], .contexts [
        ⟨5398, false, false, [], []⟩,
        ⟨5140, true, false, [], [15]⟩,
        ⟨5397, true, false, [1182], [11, 15]⟩,
        ⟨3495, false, false, [1182, 77967], []⟩,
        ⟨5394, false, false, [1182], []⟩,
        ⟨5393, false, false, [1182], []⟩,
        ⟨5395, false, false, [1182], []⟩,
        ⟨5336, true, false, [], [77965]⟩
      ]⟩,
    ⟨[1191, 77967], [1191, 77967], .contexts []⟩,
    ⟨[77967, 5, 11], [1191, 77965], .contexts [
        ⟨5391, false, false, [], [11]⟩,
        ⟨5391, false, false, [], [11]⟩,
        ⟨5143, true, false, [], [5, 11]⟩,
        ⟨5390, true, false, [1170], [1, 5, 11]⟩,
        ⟨1509, false, false, [1170, 77969], [11]⟩,
        ⟨5385, false, false, [1170], [11]⟩,
        ⟨5384, false, false, [1170], [11]⟩,
        ⟨5381, false, false, [1170], [11]⟩,
        ⟨5352, true, false, [], [77967, 11]⟩,
        ⟨5400, false, false, [], [11]⟩,
        ⟨5400, false, false, [], [11]⟩,
        ⟨5140, false, false, [1191], []⟩
      ]⟩,
    ⟨[77965, 5], [77965, 5], .contexts []⟩,
    ⟨[77965, 9], [77963], .contexts [
        ⟨5176, false, false, [], []⟩,
        ⟨5177, false, false, [], []⟩,
        ⟨5135, false, false, [], []⟩,
        ⟨5135, false, false, [], []⟩
      ]⟩,
    ⟨[77965, 8], [77965, 9], .contexts [
        ⟨77, false, false, [77965], []⟩
      ]⟩,
    ⟨[77963], [77963], .contexts []⟩,
    ⟨[1185, 77965], [1185, 77965], .contexts []⟩,
    ⟨[77963, 15], [77963, 15], .contexts []⟩,
    ⟨[1171, 77965], [1171, 77965], .contexts []⟩,
    ⟨[77965, 5], [1171, 77965], .contexts [
        ⟨5402, false, false, [], []⟩,
        ⟨5402, false, false, [], []⟩,
        ⟨5401, true, false, [1190], [5]⟩,
        ⟨1645, false, false, [1190, 77967], []⟩,
        ⟨5394, false, false, [1190], []⟩,
        ⟨5393, false, false, [1190], []⟩,
        ⟨5395, false, false, [1190], []⟩,
        ⟨5378, true, false, [], [77965]⟩,
        ⟨5408, false, false, [], []⟩,
        ⟨5408, false, false, [], []⟩
      ]⟩,
    ⟨[1171, 77963], [1171, 77963], .contexts []⟩,
    ⟨[77963, 5], [77963, 5], .contexts []⟩,
    ⟨[1183, 77963], [1183, 77963], .contexts []⟩,
    ⟨[77963, 15], [1183, 77963], .contexts [
        ⟨5407, false, false, [], []⟩,
        ⟨5407, false, false, [], []⟩,
        ⟨5136, true, false, [], [15]⟩,
        ⟨5406, true, false, [1184], [9, 15]⟩,
        ⟨5406, true, false, [1184], [9, 15]⟩,
        ⟨5399, true, false, [1184], [9, 15]⟩,
        ⟨5398, true, false, [1184], [9, 15]⟩,
        ⟨2787, false, false, [1184, 77965], []⟩,
        ⟨5404, false, false, [1184], []⟩,
        ⟨5403, false, false, [1184], []⟩,
        ⟨5405, false, false, [1184], []⟩,
        ⟨5388, true, false, [], [77963]⟩,
        ⟨5412, false, false, [], []⟩,
        ⟨5412, false, false, [], []⟩
      ]⟩,
    ⟨[77963, 1], [77961], .contexts [
        ⟨5178, false, false, [], []⟩
      ]⟩,
    ⟨[77963, 1], [77961], .contexts [
        ⟨5414, false, false, [], []⟩,
        ⟨5179, false, false, [], []⟩,
        ⟨5131, false, false, [], []⟩,
        ⟨5131, false, false, [], []⟩
      ]⟩,
    ⟨[77963, 0], [77963, 1], .contexts [
        ⟨19, false, false, [77963], []⟩
      ]⟩,
    ⟨[1191, 77963], [1191, 77963], .contexts []⟩,
    ⟨[77963, 5, 1], [1191, 77961], .contexts [
        ⟨5411, false, false, [], [1]⟩,
        ⟨5411, false, false, [], [1]⟩,
        ⟨5410, true, false, [1170], [5, 1]⟩,
        ⟨5136, true, false, [], [5, 1]⟩,
        ⟨5409, true, false, [1170], [9, 5, 1]⟩,
        ⟨1672, false, false, [1170, 77965], [1]⟩,
        ⟨5404, false, false, [1170], [1]⟩,
        ⟨5403, false, false, [1170], [1]⟩,
        ⟨5405, false, false, [1170], [1]⟩,
        ⟨5352, true, false, [], [77963, 1]⟩,
        ⟨5417, false, false, [], [1]⟩,
        ⟨5417, false, false, [], [1]⟩,
        ⟨5132, false, false, [1191], []⟩
      ]⟩,
    ⟨[1191, 77959], [1191, 77959], .contexts []⟩,
    ⟨[1191, 77959], [1191, 77959], .contexts []⟩,
    ⟨[77959, 1], [1171, 77963], .contexts [
        ⟨5420, true, false, [1190], [1]⟩,
        ⟨5419, true, false, [1190], [1]⟩,
        ⟨5129, true, false, [], [1]⟩,
        ⟨5418, true, false, [1190], [5, 1]⟩,
        ⟨1485, false, false, [1190, 77963], []⟩,
        ⟨5405, false, false, [1190], []⟩,
        ⟨5378, true, false, [], [77963]⟩
      ]⟩,
    ⟨[77961], [1191, 77959], .contexts [
        ⟨5415, true, false, [], []⟩,
        ⟨5421, true, false, [1170], [1]⟩,
        ⟨18, false, false, [1170, 77959], []⟩,
        ⟨5349, true, false, [], [77959]⟩,
        ⟨5419, false, false, [], []⟩,
        ⟨5350, true, false, [], [77959]⟩
      ]⟩,
    ⟨[77961], [1191, 77959], .contexts [
        ⟨5422, false, false, [], []⟩,
        ⟨5420, false, false, [], []⟩
      ]⟩,
    ⟨[1195], [1171, 1185], .source 662⟩,
    ⟨[1197], [1195, 1191], .source 663⟩,
    ⟨[1197, 77959], [1197, 77959], .contexts []⟩,
    ⟨[1197, 77959], [1197, 77959], .contexts []⟩,
    ⟨[77959, 15, 3], [1197, 77959, 3], .contexts [
        ⟨5422, true, false, [1190], [15, 3]⟩,
        ⟨5132, true, false, [1190], [15, 3]⟩,
        ⟨5413, true, false, [1190, 1182], [1, 15, 3]⟩,
        ⟨2778, false, false, [1190, 1182, 77963], [3]⟩,
        ⟨5416, false, false, [1190, 1182], [3]⟩,
        ⟨5415, false, false, [1190, 1182], [3]⟩,
        ⟨5336, true, false, [1190], [77961, 3]⟩,
        ⟨5423, false, false, [1190, 1185], [3]⟩,
        ⟨5376, true, false, [], [1185, 1191, 77959, 3]⟩,
        ⟨5424, true, false, [], [1191, 77959, 3]⟩,
        ⟨5425, true, false, [], [77959, 3]⟩,
        ⟨5426, false, false, [], [3]⟩,
        ⟨5427, false, false, [], [3]⟩,
        ⟨5427, false, false, [], [3]⟩
      ]⟩,
    ⟨[1197, 77957], [1197, 77957], .contexts []⟩,
    ⟨[1197, 77957], [1197, 77957], .contexts []⟩,
    ⟨[77959, 3], [77957], .contexts [
        ⟨5182, false, false, [], []⟩,
        ⟨5183, false, false, [], []⟩,
        ⟨5125, false, false, [], []⟩,
        ⟨5125, false, false, [], []⟩
      ]⟩,
    ⟨[77959, 2], [77959, 3], .contexts [
        ⟨36, false, false, [77959], []⟩
      ]⟩,
    ⟨[77957, 15], [77957, 15], .contexts []⟩,
    ⟨[77957], [77957], .contexts []⟩,
    ⟨[1199], [1196], .source 664⟩,
    ⟨[1199], [1199], .contexts []⟩,
    ⟨[1196], [1196], .contexts []⟩,
    ⟨[1199, 77957], [1199, 77957], .contexts []⟩,
    ⟨[77957, 15, 1], [1199, 77955], .contexts [
        ⟨5433, false, false, [], [1]⟩,
        ⟨5433, false, false, [], [1]⟩,
        ⟨5430, true, false, [1196], [15, 1]⟩,
        ⟨5429, true, false, [1196], [15, 1]⟩,
        ⟨5126, true, false, [], [15, 1]⟩,
        ⟨5428, true, false, [1196], [15, 1]⟩,
        ⟨1893, false, false, [1196, 77959], [1]⟩,
        ⟨5432, false, false, [1196], [1]⟩,
        ⟨5431, false, false, [1196], [1]⟩,
        ⟨5434, false, false, [1196], [1]⟩,
        ⟨5437, true, false, [], [77957, 1]⟩,
        ⟨5437, true, false, [], [77957, 1]⟩,
        ⟨5435, true, false, [], [77957, 1]⟩,
        ⟨5436, true, false, [], [77957, 1]⟩,
        ⟨5438, false, false, [], [1]⟩,
        ⟨5438, false, false, [], [1]⟩,
        ⟨5122, false, false, [1199], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 085. -/
def y322TCContextRaw085 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1199, 77953], [1199, 77953], .contexts []⟩,
    ⟨[1199, 77953], [1199, 77953], .contexts []⟩,
    ⟨[77953, 1], [77953, 1], .contexts []⟩,
    ⟨[1198], [1198], .contexts []⟩,
    ⟨[77953, 1], [1197, 77957], .contexts [
        ⟨5442, false, false, [], []⟩,
        ⟨5441, true, false, [1198], [1]⟩,
        ⟨5440, true, false, [1198], [1]⟩,
        ⟨5119, true, false, [], [1]⟩,
        ⟨5439, true, false, [1198], [15, 1]⟩,
        ⟨911, false, false, [1198, 77957], []⟩,
        ⟨5434, false, false, [1198], []⟩,
        ⟨5443, true, false, [], [77957]⟩,
        ⟨5443, true, false, [], [77957]⟩,
        ⟨5435, false, true, [], [77957]⟩
      ]⟩,
    ⟨[77957, 1], [77955], .contexts [
        ⟨5184, false, false, [], []⟩
      ]⟩,
    ⟨[77983], [77119, 7], .source 39056⟩,
    ⟨[77119, 7], [77983], .contexts [
        ⟨5446, true, false, [], []⟩
      ]⟩,
    ⟨[77983], [77983], .contexts []⟩,
    ⟨[77119, 7], [77983], .contexts [
        ⟨5447, false, false, [], []⟩,
        ⟨5448, false, false, [], []⟩,
        ⟨5448, false, false, [], []⟩
      ]⟩,
    ⟨[77983, 3], [77983, 3], .contexts []⟩,
    ⟨[77983, 3], [77859], .contexts [
        ⟨5450, false, false, [], []⟩,
        ⟨5449, true, false, [], [3]⟩,
        ⟨1769, false, false, [77119], []⟩,
        ⟨1770, false, false, [77119], []⟩,
        ⟨1946, false, false, [], [7]⟩,
        ⟨4807, true, false, [], [7]⟩,
        ⟨62, false, false, [77859], []⟩,
        ⟨4796, false, false, [], []⟩,
        ⟨4795, false, false, [], []⟩,
        ⟨4796, false, false, [], []⟩,
        ⟨4796, false, false, [], []⟩,
        ⟨4801, false, false, [], []⟩,
        ⟨1118, true, false, [], [77859]⟩
      ]⟩,
    ⟨[77859, 3], [77983], .contexts [
        ⟨5451, true, false, [], [3]⟩,
        ⟨35, false, false, [77983], []⟩,
        ⟨5448, false, false, [], []⟩
      ]⟩,
    ⟨[13, 77983], [13, 77983], .contexts []⟩,
    ⟨[13, 77983], [13, 77983], .contexts []⟩,
    ⟨[77983, 13], [77983, 13], .contexts []⟩,
    ⟨[77983], [77983], .contexts []⟩,
    ⟨[77983, 13], [13, 77983], .contexts [
        ⟨5455, false, false, [], []⟩,
        ⟨5449, true, false, [], [13]⟩,
        ⟨1785, false, false, [77119], []⟩,
        ⟨1786, false, false, [77119], []⟩,
        ⟨426, false, false, [], [7]⟩,
        ⟨5447, false, false, [13], []⟩,
        ⟨5453, false, false, [], []⟩,
        ⟨5454, false, false, [], []⟩,
        ⟨5456, false, false, [13], []⟩,
        ⟨153, true, false, [], [77983]⟩
      ]⟩,
    ⟨[77853], [77853], .contexts []⟩,
    ⟨[505], [505], .contexts [
        ⟨24, false, false, [], [505]⟩
      ]⟩,
    ⟨[77983, 15], [505, 77853], .contexts [
        ⟨5449, true, false, [], [15]⟩,
        ⟨1791, false, false, [77119], []⟩,
        ⟨1792, false, false, [77119], []⟩,
        ⟨2777, false, false, [], [7]⟩,
        ⟨4754, false, false, [505], []⟩,
        ⟨5458, false, false, [505], []⟩,
        ⟨5459, true, false, [], [77853]⟩
      ]⟩,
    ⟨[77853, 15], [503, 77983], .contexts [
        ⟨5460, true, false, [504], [15]⟩,
        ⟨3, false, false, [504, 77983], []⟩,
        ⟨2773, true, false, [], [77983]⟩
      ]⟩,
    ⟨[77985], [77119, 11], .source 39057⟩,
    ⟨[77119, 11], [77985], .contexts [
        ⟨5462, true, false, [], []⟩
      ]⟩,
    ⟨[77119, 11], [77985], .contexts [
        ⟨5463, false, false, [], []⟩
      ]⟩,
    ⟨[77985], [77985], .contexts []⟩,
    ⟨[77985], [77985], .contexts []⟩,
    ⟨[77119, 11], [77985], .contexts [
        ⟨5464, false, false, [], []⟩,
        ⟨5465, false, false, [], []⟩,
        ⟨5466, false, false, [], []⟩,
        ⟨5466, false, false, [], []⟩
      ]⟩,
    ⟨[1201], [317, 847], .source 665⟩,
    ⟨[77985, 1], [77985, 1], .contexts []⟩,
    ⟨[77985, 1], [1201, 77711], .contexts [
        ⟨5469, false, false, [], []⟩,
        ⟨5467, true, false, [], [1]⟩,
        ⟨992, false, false, [77119], []⟩,
        ⟨993, false, false, [77119], []⟩,
        ⟨1950, false, false, [], [11]⟩,
        ⟨4054, false, false, [317], []⟩,
        ⟨5468, true, false, [], [77711]⟩,
        ⟨4037, false, false, [1201], []⟩,
        ⟨24, true, false, [], [1201, 77711]⟩
      ]⟩,
    ⟨[1203], [1200], .source 666⟩,
    ⟨[77711, 1], [1203, 77985], .contexts [
        ⟨5470, true, false, [1200], [1]⟩,
        ⟨18, false, false, [1200, 77985], []⟩,
        ⟨5471, true, false, [], [77985]⟩
      ]⟩,
    ⟨[315, 77985], [315, 77985], .contexts []⟩,
    ⟨[315, 77985], [315, 77985], .contexts []⟩,
    ⟨[77985], [77985], .contexts []⟩,
    ⟨[77985, 9], [245, 77985], .contexts [
        ⟨5467, true, false, [], [9]⟩,
        ⟨344, false, false, [77119], []⟩,
        ⟨346, false, false, [77119], []⟩,
        ⟨2799, false, false, [], [11, 9, 11]⟩,
        ⟨2846, false, false, [], [9, 11]⟩,
        ⟨2847, false, false, [], [9, 11]⟩,
        ⟨2848, false, false, [], [9, 11]⟩,
        ⟨2848, false, false, [], [9, 11]⟩,
        ⟨2796, false, false, [245], [11]⟩,
        ⟨5463, false, false, [245], []⟩,
        ⟨5475, false, false, [245], []⟩,
        ⟨1606, true, false, [], [77985]⟩
      ]⟩,
    ⟨[13, 77985], [13, 77985], .contexts []⟩,
    ⟨[13, 77985], [13, 77985], .contexts []⟩,
    ⟨[77985, 13], [77985, 13], .contexts []⟩,
    ⟨[77985, 13], [13, 77985], .contexts [
        ⟨5479, false, false, [], []⟩,
        ⟨5467, true, false, [], [13]⟩,
        ⟨352, false, false, [77119], []⟩,
        ⟨353, false, false, [77119], []⟩,
        ⟨426, false, false, [], [11]⟩,
        ⟨5463, false, false, [13], []⟩,
        ⟨5477, false, false, [], []⟩,
        ⟨5478, false, false, [], []⟩,
        ⟨5475, false, false, [13], []⟩,
        ⟨153, true, false, [], [77985]⟩
      ]⟩,
    ⟨[77985, 15], [505, 77347], .contexts [
        ⟨5467, true, false, [], [15]⟩,
        ⟨358, false, false, [77119], []⟩,
        ⟨359, false, false, [77119], []⟩,
        ⟨2777, false, false, [], [11]⟩,
        ⟨2766, false, false, [505], []⟩,
        ⟨1581, false, false, [505], []⟩,
        ⟨5459, true, false, [], [77347]⟩
      ]⟩,
    ⟨[77347, 15], [503, 77985], .contexts [
        ⟨5481, true, false, [504], [15]⟩,
        ⟨3, false, false, [504, 77985], []⟩,
        ⟨2773, true, false, [], [77985]⟩
      ]⟩,
    ⟨[1201, 77711], [1201, 77711], .contexts []⟩,
    ⟨[1205], [31, 1201], .source 667⟩,
    ⟨[77707, 13], [77707, 13], .contexts []⟩,
    ⟨[1207], [1203, 1205], .source 668⟩,
    ⟨[77707, 13], [1207, 77711], .contexts [
        ⟨5485, false, false, [], []⟩,
        ⟨3896, true, false, [], [13]⟩,
        ⟨3900, true, false, [], [1, 13]⟩,
        ⟨5483, true, false, [1200], [13, 1, 13]⟩,
        ⟨5483, true, false, [1200], [13, 1, 13]⟩,
        ⟨5470, true, false, [1200], [13, 1, 13]⟩,
        ⟨5469, true, false, [1200], [13, 1, 13]⟩,
        ⟨1587, false, false, [1200, 77985], []⟩,
        ⟨190, false, false, [1200, 77985], []⟩,
        ⟨5479, false, false, [1200], [1]⟩,
        ⟨5480, false, false, [1200], [1]⟩,
        ⟨5477, false, false, [1200], [1]⟩,
        ⟨5478, false, false, [1200], [1]⟩,
        ⟨5478, false, false, [1200], [1]⟩,
        ⟨5470, false, false, [1200, 13], []⟩,
        ⟨740, true, false, [1200], [1201, 77711]⟩,
        ⟨5484, true, false, [1200], [77711]⟩,
        ⟨4037, false, false, [1200, 1205], []⟩,
        ⟨5471, true, false, [], [1205, 77711]⟩,
        ⟨5486, true, false, [], [77711]⟩
      ]⟩,
    ⟨[1209], [1206], .source 669⟩,
    ⟨[1209], [1209], .contexts []⟩,
    ⟨[1209], [1209], .contexts []⟩,
    ⟨[77709], [1209, 77707], .contexts [
        ⟨4022, true, false, [], []⟩,
        ⟨5487, true, false, [1206], [13]⟩,
        ⟨98, false, false, [1206, 77707], []⟩,
        ⟨5488, true, false, [], [77707]⟩,
        ⟨5490, true, false, [], [77707]⟩,
        ⟨5489, true, false, [], [77707]⟩
      ]⟩,
    ⟨[1209, 77707], [1209, 77707], .contexts []⟩,
    ⟨[77709], [1209, 77707], .contexts [
        ⟨5491, false, false, [], []⟩,
        ⟨5492, false, false, [], []⟩
      ]⟩,
    ⟨[1207], [1208], .contexts [
        ⟨5488, true, true, [], []⟩
      ]⟩,
    ⟨[1211], [1207, 835], .source 670⟩,
    ⟨[1213], [1211, 1209], .source 671⟩,
    ⟨[77707, 3], [1213, 77707], .contexts [
        ⟨5491, true, false, [1208], [3]⟩,
        ⟨3900, true, false, [1208], [3]⟩,
        ⟨4064, true, false, [1208, 836], [13, 3]⟩,
        ⟨4064, true, false, [1208, 836], [13, 3]⟩,
        ⟨4040, true, false, [1208, 836], [13, 3]⟩,
        ⟨4036, true, false, [1208, 836], [13, 3]⟩,
        ⟨932, false, false, [1208, 836, 77711], []⟩,
        ⟨4065, false, false, [1208, 836], []⟩,
        ⟨4022, false, false, [1208, 836], []⟩,
        ⟨4029, false, false, [1208, 836], []⟩,
        ⟨4066, true, false, [1208], [77709]⟩,
        ⟨4066, true, false, [1208], [77709]⟩,
        ⟨4038, false, true, [1208], [77709]⟩,
        ⟨5493, false, false, [1208, 835], []⟩,
        ⟨5494, true, false, [], [835, 1209, 77707]⟩,
        ⟨5495, true, false, [], [1209, 77707]⟩,
        ⟨5496, true, false, [], [77707]⟩
      ]⟩,
    ⟨[1215], [1207, 1189], .source 672⟩,
    ⟨[77707, 9], [1215, 77969], .contexts [
        ⟨5491, true, false, [1208], [9]⟩,
        ⟨5372, true, false, [1208, 1186], [9]⟩,
        ⟨76, false, false, [1208, 1186, 77969], []⟩,
        ⟨5343, true, false, [1208], [77969]⟩,
        ⟨5370, false, false, [1208], []⟩,
        ⟨5494, true, false, [], [1189, 77969]⟩,
        ⟨5498, true, false, [], [77969]⟩
      ]⟩,
    ⟨[1207, 77711], [1207, 77711], .contexts []⟩,
    ⟨[1217], [1207, 845], .source 673⟩,
    ⟨[77123, 13], [77123, 13], .contexts []⟩,
    ⟨[1219], [1216], .source 674⟩]

/-- Exact literal claimed equations and contextual derivations, block 086. -/
def y322TCContextRaw086 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1216], [1216], .contexts []⟩,
    ⟨[77123, 13], [1219, 77705], .contexts [
        ⟨5502, false, false, [], []⟩,
        ⟨5501, false, false, [1216], [77123, 13]⟩,
        ⟨4055, true, false, [1216, 1207], [13]⟩,
        ⟨5500, true, false, [1216], [11, 13]⟩,
        ⟨5500, true, false, [1216], [11, 13]⟩,
        ⟨5487, true, false, [1216], [11, 13]⟩,
        ⟨5485, true, false, [1216], [11, 13]⟩,
        ⟨1624, false, false, [1216, 77707], []⟩,
        ⟨4073, false, false, [1216], []⟩,
        ⟨4072, false, false, [1216], []⟩,
        ⟨4075, false, false, [1216], []⟩,
        ⟨5504, true, false, [], [77705]⟩,
        ⟨5504, true, false, [], [77705]⟩,
        ⟨5503, true, false, [], [77705]⟩
      ]⟩,
    ⟨[1217], [1218], .contexts [
        ⟨5503, true, true, [], []⟩
      ]⟩,
    ⟨[77705, 13], [1217, 77123], .contexts [
        ⟨5505, true, false, [1218], [13]⟩,
        ⟨98, false, false, [1218, 77123], []⟩,
        ⟨5506, true, false, [], [77123]⟩
      ]⟩,
    ⟨[77707, 1], [1209, 77707], .contexts [
        ⟨3894, false, false, [], []⟩,
        ⟨5493, false, false, [], []⟩,
        ⟨5492, false, false, [], []⟩,
        ⟨5492, false, false, [], []⟩
      ]⟩,
    ⟨[1209, 77705], [1209, 77705], .contexts []⟩,
    ⟨[1209, 77705], [1209, 77705], .contexts []⟩,
    ⟨[77705, 1], [77705, 1], .contexts []⟩,
    ⟨[77705, 1], [1209, 77705], .contexts [
        ⟨5511, false, false, [], []⟩,
        ⟨4072, true, false, [], [1]⟩,
        ⟨992, false, false, [77707], []⟩,
        ⟨993, false, false, [77707], []⟩,
        ⟨5508, false, false, [], [11]⟩,
        ⟨3892, false, false, [1209], []⟩,
        ⟨5509, false, false, [], []⟩,
        ⟨5510, false, false, [], []⟩,
        ⟨4075, false, false, [1209], []⟩,
        ⟨5490, true, false, [], [77705]⟩,
        ⟨5489, true, false, [], [77705]⟩,
        ⟨24, true, false, [], [1209, 77705]⟩
      ]⟩,
    ⟨[1213, 77707], [1213, 77707], .contexts []⟩,
    ⟨[1213, 77705], [1213, 77705], .contexts []⟩,
    ⟨[1213, 77705], [1213, 77705], .contexts []⟩,
    ⟨[77705, 3], [77705, 3], .contexts []⟩,
    ⟨[77705, 3], [1213, 77705], .contexts [
        ⟨5516, false, false, [], []⟩,
        ⟨4072, true, false, [], [3]⟩,
        ⟨335, false, false, [77707], []⟩,
        ⟨336, false, false, [77707], []⟩,
        ⟨5497, false, false, [], [11]⟩,
        ⟨5513, false, false, [], [11]⟩,
        ⟨5513, false, false, [], [11]⟩,
        ⟨3892, false, false, [1213], []⟩,
        ⟨5514, false, false, [], []⟩,
        ⟨5515, false, false, [], []⟩,
        ⟨4075, false, false, [1213], []⟩,
        ⟨24, true, false, [], [1213, 77705]⟩
      ]⟩,
    ⟨[1221], [1209, 1215], .source 675⟩,
    ⟨[1215, 77969], [1215, 77969], .contexts []⟩,
    ⟨[77967, 9], [77967, 9], .contexts []⟩,
    ⟨[1223], [1220], .source 676⟩,
    ⟨[1225], [1223, 1215], .source 677⟩,
    ⟨[77123, 13], [1219, 77705], .contexts [
        ⟨5505, false, false, [], []⟩
      ]⟩,
    ⟨[1219, 77705], [1219, 77705], .contexts []⟩,
    ⟨[1219, 77705], [1219, 77705], .contexts []⟩,
    ⟨[1219, 77703], [1219, 77703], .contexts []⟩,
    ⟨[1219, 77703], [1219, 77703], .contexts []⟩,
    ⟨[1218], [1218], .contexts []⟩,
    ⟨[77703, 13], [1217, 77125], .contexts [
        ⟨5527, true, false, [1218], [13]⟩,
        ⟨5526, true, false, [1218], [13]⟩,
        ⟨3889, true, false, [], [13]⟩,
        ⟨5525, true, false, [1218], [9, 13]⟩,
        ⟨5525, true, false, [1218], [9, 13]⟩,
        ⟨5524, true, false, [1218], [9, 13]⟩,
        ⟨5523, true, false, [1218], [9, 13]⟩,
        ⟨5502, true, false, [1218], [9, 13]⟩,
        ⟨1650, false, false, [1218, 77123], []⟩,
        ⟨1967, false, false, [1218], []⟩,
        ⟨1966, false, false, [1218], []⟩,
        ⟨1969, false, false, [1218], []⟩,
        ⟨5528, true, false, [], [77125]⟩,
        ⟨5528, true, false, [], [77125]⟩,
        ⟨5506, true, false, [], [77125]⟩
      ]⟩,
    ⟨[77125, 13], [1219, 77703], .contexts [
        ⟨5529, true, false, [1216], [13]⟩,
        ⟨98, false, false, [1216, 77703], []⟩,
        ⟨5503, true, false, [], [77703]⟩
      ]⟩,
    ⟨[1227], [1209, 843], .source 678⟩,
    ⟨[77701], [843, 77699], .contexts [
        ⟨4110, false, false, [], []⟩
      ]⟩,
    ⟨[77699, 9], [77699, 9], .contexts []⟩,
    ⟨[1229], [1226], .source 679⟩,
    ⟨[1231], [1229, 843], .source 680⟩,
    ⟨[77699, 9], [1231, 77699], .contexts [
        ⟨5533, false, false, [], []⟩,
        ⟨5531, false, false, [1226], [77699, 9]⟩,
        ⟨4110, true, false, [1226, 1209], [9]⟩,
        ⟨3885, true, false, [1226, 1209], [9]⟩,
        ⟨3889, true, false, [1226, 1209], [1, 9]⟩,
        ⟨5510, true, false, [1226], [9, 1, 9]⟩,
        ⟨5510, true, false, [1226], [9, 1, 9]⟩,
        ⟨5509, true, false, [1226], [9, 1, 9]⟩,
        ⟨5512, true, false, [1226], [9, 1, 9]⟩,
        ⟨5511, true, false, [1226], [9, 1, 9]⟩,
        ⟨1022, false, false, [1226, 77705], []⟩,
        ⟨787, false, false, [1226, 77705], []⟩,
        ⟨4086, false, false, [1226], [1]⟩,
        ⟨3907, false, false, [1226], []⟩,
        ⟨5532, false, false, [1226], []⟩,
        ⟨4108, false, false, [1226], []⟩,
        ⟨4108, false, false, [1226], []⟩,
        ⟨4104, false, false, [1226, 843], []⟩,
        ⟨5534, true, false, [], [843, 77699]⟩,
        ⟨5535, true, false, [], [77699]⟩
      ]⟩,
    ⟨[77703, 3], [77703, 3], .contexts []⟩,
    ⟨[1233], [1212], .source 681⟩,
    ⟨[1212], [1212], .contexts []⟩,
    ⟨[1225, 77967], [1225, 77967], .contexts []⟩,
    ⟨[77967, 9], [1225, 77967], .contexts [
        ⟨5520, false, false, [], []⟩,
        ⟨5520, false, false, [], []⟩,
        ⟨5143, true, false, [], [9]⟩,
        ⟨5518, false, false, [1220], [77969, 1, 9]⟩,
        ⟨5499, true, false, [1220, 1209], [1, 9]⟩,
        ⟨5508, true, false, [1220], [9, 1, 9]⟩,
        ⟨1022, false, false, [1220, 77707], []⟩,
        ⟨787, false, false, [1220, 77707], []⟩,
        ⟨5499, false, false, [1220], [1]⟩,
        ⟨5519, false, false, [1220], [1]⟩,
        ⟨5519, false, false, [1220], [1]⟩,
        ⟨5143, false, false, [1220, 1215], []⟩,
        ⟨5381, false, false, [1220, 1215], []⟩,
        ⟨5521, true, false, [], [1215, 77967]⟩,
        ⟨5522, true, false, [], [77967]⟩,
        ⟨5540, false, false, [], []⟩,
        ⟨5540, false, false, [], []⟩
      ]⟩,
    ⟨[77963, 11], [77963, 11], .contexts []⟩,
    ⟨[1235], [1224], .source 682⟩,
    ⟨[1224], [1224], .contexts []⟩,
    ⟨[1231, 77699], [1231, 77699], .contexts []⟩,
    ⟨[1237], [1230], .source 683⟩,
    ⟨[1230], [1230], .contexts []⟩,
    ⟨[1233, 77703], [1233, 77703], .contexts []⟩,
    ⟨[77703, 3], [1233, 77703], .contexts [
        ⟨5537, false, false, [], []⟩,
        ⟨5537, false, false, [], []⟩,
        ⟨3889, true, false, [], [3]⟩,
        ⟨5515, true, false, [1212], [9, 3]⟩,
        ⟨5515, true, false, [1212], [9, 3]⟩,
        ⟨5514, true, false, [1212], [9, 3]⟩,
        ⟨5517, true, false, [1212], [9, 3]⟩,
        ⟨5516, true, false, [1212], [9, 3]⟩,
        ⟨1010, false, false, [1212, 77705], []⟩,
        ⟨4087, false, false, [1212], []⟩,
        ⟨4086, false, false, [1212], []⟩,
        ⟨4089, false, false, [1212], []⟩,
        ⟨5539, true, false, [], [77703]⟩,
        ⟨5539, true, false, [], [77703]⟩,
        ⟨5538, true, false, [], [77703]⟩,
        ⟨5548, false, false, [], []⟩,
        ⟨5548, false, false, [], []⟩
      ]⟩,
    ⟨[1239], [1233, 843], .source 684⟩,
    ⟨[77695], [831, 77693], .contexts [
        ⟨3874, true, false, [], []⟩,
        ⟨3874, true, false, [], []⟩,
        ⟨3915, true, false, [], []⟩,
        ⟨3914, true, false, [], []⟩,
        ⟨4123, true, false, [848], [1]⟩,
        ⟨18, false, false, [848, 77693], []⟩,
        ⟨4076, true, false, [], [77693]⟩,
        ⟨4119, false, false, [], []⟩,
        ⟨4031, true, false, [], [77693]⟩,
        ⟨4030, true, false, [], [77693]⟩,
        ⟨4077, true, false, [], [77693]⟩,
        ⟨4120, false, false, [], []⟩
      ]⟩,
    ⟨[1241], [1239, 831], .source 685⟩,
    ⟨[77693, 3], [77693, 3], .contexts []⟩,
    ⟨[1243], [1240], .source 686⟩,
    ⟨[1245], [1243, 843], .source 687⟩,
    ⟨[77693, 3], [1245, 77699], .contexts [
        ⟨5553, false, false, [], []⟩,
        ⟨5552, false, false, [1240], [77693, 3]⟩,
        ⟨5551, true, false, [1240, 1239], [3]⟩,
        ⟨3875, true, false, [1240, 1239], [3]⟩,
        ⟨3878, true, false, [1240, 1239], [1, 3]⟩,
        ⟨5550, false, false, [1240], [77699, 3, 1, 3]⟩,
        ⟨4110, true, false, [1240, 1233], [3, 1, 3]⟩,
        ⟨3885, true, false, [1240, 1233], [3, 1, 3]⟩,
        ⟨5549, true, false, [1240], [1, 3, 1, 3]⟩,
        ⟨1951, false, false, [1240, 77703], []⟩,
        ⟨4097, false, false, [1240], []⟩,
        ⟨4095, false, false, [1240], []⟩,
        ⟨5532, false, false, [1240], []⟩,
        ⟨4108, false, false, [1240], []⟩,
        ⟨4108, false, false, [1240], []⟩,
        ⟨4104, false, false, [1240, 843], []⟩,
        ⟨5554, true, false, [], [843, 77699]⟩,
        ⟨5555, true, false, [], [77699]⟩
      ]⟩,
    ⟨[1247], [1244], .source 688⟩,
    ⟨[77697], [1247, 77693], .contexts [
        ⟨4114, true, false, [], []⟩,
        ⟨5556, true, false, [1244], [3]⟩,
        ⟨35, false, false, [1244, 77693], []⟩,
        ⟨5557, true, false, [], [77693]⟩
      ]⟩,
    ⟨[1247, 77693], [1247, 77693], .contexts []⟩,
    ⟨[77697], [1247, 77693], .contexts [
        ⟨5558, false, false, [], []⟩,
        ⟨5559, false, false, [], []⟩
      ]⟩,
    ⟨[1249], [1245, 1237], .source 689⟩,
    ⟨[1251], [1249, 1247], .source 690⟩,
    ⟨[77693, 9], [1251, 77693], .contexts [
        ⟨5558, true, false, [1246], [9]⟩,
        ⟨3878, true, false, [1246], [9]⟩,
        ⟨5545, true, false, [1246, 1230], [3, 9]⟩,
        ⟨5545, true, false, [1246, 1230], [3, 9]⟩,
        ⟨5536, true, false, [1246, 1230], [3, 9]⟩,
        ⟨5533, true, false, [1246, 1230], [3, 9]⟩,
        ⟨841, false, false, [1246, 1230, 77699], []⟩,
        ⟨4115, false, false, [1246, 1230], []⟩,
        ⟨4114, false, false, [1246, 1230], []⟩,
        ⟨4117, false, false, [1246, 1230], []⟩,
        ⟨5547, true, false, [1246], [77697]⟩,
        ⟨5547, true, false, [1246], [77697]⟩,
        ⟨5546, true, false, [1246], [77697]⟩,
        ⟨5560, false, false, [1246, 1237], []⟩,
        ⟨5557, false, true, [], [1237, 1247, 77693]⟩,
        ⟨5561, true, false, [], [1247, 77693]⟩,
        ⟨5562, true, false, [], [77693]⟩
      ]⟩,
    ⟨[1235, 77963], [1235, 77963], .contexts []⟩,
    ⟨[77963, 11], [1235, 77963], .contexts [
        ⟨5542, false, false, [], []⟩,
        ⟨5542, false, false, [], []⟩,
        ⟨5136, true, false, [], [11]⟩,
        ⟨5140, true, false, [], [9, 11]⟩,
        ⟨5541, true, false, [1224], [11, 9, 11]⟩,
        ⟨966, false, false, [1224, 77967], []⟩,
        ⟨967, false, false, [1224, 77967], []⟩,
        ⟨5393, false, false, [1224], [9]⟩,
        ⟨5176, false, false, [1224], []⟩,
        ⟨5177, false, false, [1224], []⟩,
        ⟨5135, false, false, [1224], []⟩,
        ⟨5135, false, false, [1224], []⟩,
        ⟨5405, false, false, [1224], []⟩,
        ⟨5544, true, false, [], [77963]⟩,
        ⟨5544, true, false, [], [77963]⟩,
        ⟨5543, true, false, [], [77963]⟩,
        ⟨5564, false, false, [], []⟩,
        ⟨5564, false, false, [], []⟩
      ]⟩,
    ⟨[1253], [1235, 1191], .source 691⟩,
    ⟨[77961], [1191, 77959], .contexts [
        ⟨5423, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 087. -/
def y322TCContextRaw087 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77959, 11], [77959, 11], .contexts []⟩,
    ⟨[77959], [77959], .contexts []⟩,
    ⟨[1255], [1252], .source 692⟩,
    ⟨[1257], [1255, 1191], .source 693⟩,
    ⟨[1251, 77693], [1251, 77693], .contexts []⟩,
    ⟨[77693, 13], [77691], .contexts [
        ⟨3916, false, false, [], []⟩,
        ⟨3917, false, false, [], []⟩,
        ⟨3867, false, false, [], []⟩,
        ⟨3867, false, false, [], []⟩
      ]⟩,
    ⟨[1261], [849, 1247], .source 695⟩,
    ⟨[77693, 1], [1261, 77693], .contexts [
        ⟨4122, false, false, [], []⟩,
        ⟨4123, false, false, [], []⟩,
        ⟨5560, false, false, [849], []⟩,
        ⟨5574, true, false, [], [77693]⟩
      ]⟩,
    ⟨[1261, 77689], [1261, 77689], .contexts []⟩,
    ⟨[1261, 77689], [1261, 77689], .contexts []⟩,
    ⟨[77689, 13], [77689, 13], .contexts []⟩,
    ⟨[1261], [1261], .contexts [
        ⟨24, false, false, [], [1261]⟩
      ]⟩,
    ⟨[1257, 77959], [1257, 77959], .contexts []⟩,
    ⟨[77959, 11, 3], [1257, 77957], .contexts [
        ⟨5568, false, false, [], [3]⟩,
        ⟨5568, false, false, [], [3]⟩,
        ⟨5566, false, false, [1252], [77959, 11, 3]⟩,
        ⟨5423, true, false, [1252, 1235], [11, 3]⟩,
        ⟨5132, true, false, [1252, 1235], [11, 3]⟩,
        ⟨5565, true, false, [1252], [1, 11, 3]⟩,
        ⟨1000, false, false, [1252, 77963], [3]⟩,
        ⟨5416, false, false, [1252], [3]⟩,
        ⟨5414, false, false, [1252], [3]⟩,
        ⟨5567, false, false, [1252], [3]⟩,
        ⟨5420, false, false, [1252], [3]⟩,
        ⟨5420, false, false, [1252], [3]⟩,
        ⟨5569, false, false, [1252, 1191], [3]⟩,
        ⟨5570, true, false, [], [1191, 77959, 3]⟩,
        ⟨5571, true, false, [], [77959, 3]⟩,
        ⟨5580, false, false, [], [3]⟩,
        ⟨5580, false, false, [], [3]⟩,
        ⟨5126, false, false, [1257], []⟩
      ]⟩,
    ⟨[77957, 11], [77957, 11], .contexts []⟩,
    ⟨[1263], [1256], .source 696⟩,
    ⟨[1256], [1256], .contexts []⟩,
    ⟨[77689, 13, 11], [1261, 77687], .contexts [
        ⟨5578, false, false, [], [11]⟩,
        ⟨5578, false, false, [], [11]⟩,
        ⟨3864, true, false, [], [13, 11]⟩,
        ⟨3864, true, false, [], [13, 11]⟩,
        ⟨3919, true, false, [], [13, 11]⟩,
        ⟨3918, true, false, [], [13, 11]⟩,
        ⟨5573, true, false, [], [1, 13, 11]⟩,
        ⟨3338, false, false, [77693], [11]⟩,
        ⟨389, false, false, [77693], [11]⟩,
        ⟨5575, false, false, [], [13, 1, 11]⟩,
        ⟨3868, false, false, [1261], [1, 11]⟩,
        ⟨3865, false, false, [1261], [11]⟩,
        ⟨5576, false, false, [], [11]⟩,
        ⟨5577, false, false, [], [11]⟩,
        ⟨5579, true, false, [], [77689, 11]⟩,
        ⟨5576, false, false, [], [11]⟩,
        ⟨5577, false, false, [], [11]⟩,
        ⟨5577, false, false, [], [11]⟩,
        ⟨3862, false, false, [1261], []⟩
      ]⟩,
    ⟨[77687, 13], [77687, 13], .contexts []⟩,
    ⟨[77687], [77687], .contexts []⟩,
    ⟨[1265], [1260], .source 697⟩,
    ⟨[1260], [1260], .contexts []⟩,
    ⟨[77687, 13], [1265, 77687], .contexts [
        ⟨5586, false, false, [], []⟩,
        ⟨5585, true, false, [1260], [13]⟩,
        ⟨1624, false, false, [1260, 77689], []⟩,
        ⟨91, false, false, [1260, 77689], []⟩,
        ⟨3920, false, false, [1260], []⟩,
        ⟨3921, false, false, [1260], []⟩,
        ⟨3861, false, false, [1260], []⟩,
        ⟨3861, false, false, [1260], []⟩,
        ⟨5587, false, false, [1260], []⟩,
        ⟨5589, true, false, [], [77687]⟩,
        ⟨5589, true, false, [], [77687]⟩,
        ⟨5588, true, false, [], [77687]⟩
      ]⟩,
    ⟨[1263, 77957], [1263, 77957], .contexts []⟩,
    ⟨[77955], [1199, 77953], .contexts [
        ⟨5121, true, false, [], []⟩,
        ⟨5121, true, false, [], []⟩,
        ⟨5185, true, false, [], []⟩,
        ⟨5445, true, false, [], []⟩,
        ⟨5444, true, false, [1196], [1]⟩,
        ⟨18, false, false, [1196, 77953], []⟩,
        ⟨5435, true, false, [], [77953]⟩,
        ⟨5440, false, false, [], []⟩,
        ⟨5436, true, false, [], [77953]⟩,
        ⟨5441, false, false, [], []⟩
      ]⟩,
    ⟨[1267], [1263, 1199], .source 698⟩,
    ⟨[1267, 77953, 11], [77957, 1], .contexts [
        ⟨5593, false, false, [], [77953, 11]⟩,
        ⟨5592, true, false, [1263], [11]⟩,
        ⟨5122, true, false, [1263], [11]⟩,
        ⟨5591, true, false, [], [1, 11]⟩,
        ⟨5591, true, false, [], [1, 11]⟩,
        ⟨5583, false, false, [], [77957, 1, 11]⟩,
        ⟨5584, false, false, [], [77957, 1, 11]⟩,
        ⟨5584, false, false, [], [77957, 1, 11]⟩,
        ⟨5434, true, false, [1256], [1, 11]⟩,
        ⟨5431, true, false, [1256], [1, 11]⟩,
        ⟨5432, true, false, [1256], [1, 11]⟩,
        ⟨1040, true, false, [1256, 77959], [1, 11]⟩,
        ⟨5581, false, false, [1256], [11, 1, 11]⟩,
        ⟨5582, true, false, [], [1, 11]⟩,
        ⟨5582, true, false, [], [1, 11]⟩,
        ⟨1000, false, false, [77957], []⟩,
        ⟨19, false, false, [77957], []⟩
      ]⟩,
    ⟨[77953, 11], [77953, 11], .contexts []⟩,
    ⟨[1269], [1266], .source 699⟩,
    ⟨[1271], [1269, 1199], .source 700⟩,
    ⟨[1265, 77687], [1265, 77687], .contexts []⟩,
    ⟨[77685], [77685], .contexts []⟩,
    ⟨[1264], [1264], .contexts []⟩,
    ⟨[1271, 77953], [1271, 77953], .contexts []⟩,
    ⟨[1271, 77951], [1271, 77951], .contexts []⟩,
    ⟨[1271, 77951], [1271, 77951], .contexts []⟩,
    ⟨[1271, 77951, 11], [77953, 13], .contexts [
        ⟨5603, true, false, [], [11]⟩,
        ⟨5602, true, false, [], [11]⟩,
        ⟨5115, true, false, [1271], [11]⟩,
        ⟨5601, true, false, [], [13, 11]⟩,
        ⟨5601, true, false, [], [13, 11]⟩,
        ⟨5597, false, false, [], [77953, 13, 11]⟩,
        ⟨5596, false, false, [], [1199, 77953, 13, 11]⟩,
        ⟨5441, true, false, [1266], [13, 11]⟩,
        ⟨5441, true, false, [1266], [13, 11]⟩,
        ⟨5592, true, false, [1266], [13, 11]⟩,
        ⟨5445, true, false, [1266], [13, 11]⟩,
        ⟨5594, true, false, [1266], [13, 11]⟩,
        ⟨5595, true, false, [], [13, 11]⟩,
        ⟨5595, true, false, [], [13, 11]⟩,
        ⟨1060, false, false, [77953], []⟩,
        ⟨108, false, false, [77953], []⟩
      ]⟩,
    ⟨[77951, 11], [77951, 11], .contexts []⟩,
    ⟨[77951], [77951], .contexts []⟩,
    ⟨[1273], [1270], .source 701⟩,
    ⟨[1273], [1273], .contexts []⟩,
    ⟨[1273], [1270], .contexts [
        ⟨5608, false, false, [], []⟩,
        ⟨5607, false, false, [], []⟩
      ]⟩,
    ⟨[1270], [1270], .contexts []⟩,
    ⟨[1273, 77951], [1273, 77951], .contexts []⟩,
    ⟨[77951, 11], [1273, 77951], .contexts [
        ⟨5605, false, false, [], []⟩,
        ⟨5605, false, false, [], []⟩,
        ⟨5604, false, false, [1270], []⟩,
        ⟨5186, false, false, [1270], []⟩,
        ⟨5187, false, false, [1270], []⟩,
        ⟨5114, false, false, [1270], []⟩,
        ⟨5114, false, false, [1270], []⟩,
        ⟨5606, false, false, [1270], []⟩,
        ⟨5610, true, false, [], [77951]⟩,
        ⟨5610, true, false, [], [77951]⟩,
        ⟨5609, true, false, [], [77951]⟩,
        ⟨5611, false, false, [], []⟩,
        ⟨5611, false, false, [], []⟩
      ]⟩,
    ⟨[1273, 77947], [1273, 77947], .contexts []⟩,
    ⟨[1273, 77947], [1273, 77947], .contexts []⟩,
    ⟨[77951], [77951], .contexts []⟩,
    ⟨[77947, 1], [77947, 1], .contexts []⟩,
    ⟨[1272], [1272], .contexts []⟩,
    ⟨[77947, 1], [1271, 77951], .contexts [
        ⟨5616, false, false, [], []⟩,
        ⟨5614, true, false, [1272], [1]⟩,
        ⟨5613, true, false, [1272], [1]⟩,
        ⟨5108, true, false, [], [1]⟩,
        ⟨5111, true, false, [], [11, 1]⟩,
        ⟨5612, true, false, [1272], [1, 11, 1]⟩,
        ⟨1068, false, false, [1272, 77951], []⟩,
        ⟨5615, false, false, [1272], []⟩,
        ⟨5606, false, false, [1272], []⟩,
        ⟨5617, true, false, [], [77951]⟩,
        ⟨5617, true, false, [], [77951]⟩,
        ⟨5607, false, true, [], [77951]⟩
      ]⟩,
    ⟨[77951, 1], [77949], .contexts [
        ⟨5188, false, false, [], []⟩
      ]⟩,
    ⟨[77987], [77859, 9], .source 39058⟩,
    ⟨[77859, 9], [77987], .contexts [
        ⟨5620, true, false, [], []⟩
      ]⟩,
    ⟨[77859, 9], [77987], .contexts [
        ⟨5621, false, false, [], []⟩
      ]⟩,
    ⟨[77987], [77987], .contexts []⟩,
    ⟨[77987], [77987], .contexts []⟩,
    ⟨[77859, 9], [77987], .contexts [
        ⟨5622, false, false, [], []⟩,
        ⟨5623, false, false, [], []⟩,
        ⟨5624, false, false, [], []⟩,
        ⟨5624, false, false, [], []⟩
      ]⟩,
    ⟨[77987], [77987], .contexts []⟩,
    ⟨[77987, 7], [77987, 7], .contexts []⟩,
    ⟨[77987, 7], [245, 77243], .contexts [
        ⟨5627, false, false, [], []⟩,
        ⟨5625, true, false, [], [7]⟩,
        ⟨1809, false, false, [77859], []⟩,
        ⟨1810, false, false, [77859], []⟩,
        ⟨4806, false, false, [], [9]⟩,
        ⟨4807, false, false, [], [9]⟩,
        ⟨397, false, false, [], [9]⟩,
        ⟨398, false, false, [], [9]⟩,
        ⟨398, false, false, [], [9]⟩,
        ⟨2800, false, false, [], []⟩,
        ⟨1633, false, false, [], []⟩,
        ⟨1635, false, false, [], []⟩,
        ⟨1635, false, false, [], []⟩,
        ⟨2802, false, false, [], []⟩,
        ⟨2803, false, false, [], []⟩
      ]⟩,
    ⟨[77859, 13], [13, 77859], .contexts [
        ⟨4810, false, false, [], []⟩,
        ⟨4810, false, false, [], []⟩,
        ⟨4797, true, false, [], [13]⟩,
        ⟨408, false, false, [77717], []⟩,
        ⟨410, false, false, [77717], []⟩,
        ⟨4774, false, false, [], [15, 13, 15]⟩,
        ⟨3604, false, false, [], [13, 15]⟩,
        ⟨3602, false, false, [], [13, 15]⟩,
        ⟨3603, false, false, [], [13, 15]⟩,
        ⟨3603, false, false, [], [13, 15]⟩,
        ⟨4151, false, false, [13], [15]⟩,
        ⟨4794, false, false, [13], []⟩,
        ⟨4808, false, false, [], []⟩,
        ⟨4809, false, false, [], []⟩,
        ⟨4801, false, false, [13], []⟩,
        ⟨153, true, false, [], [77859]⟩,
        ⟨4808, false, false, [], []⟩,
        ⟨4809, false, false, [], []⟩
      ]⟩,
    ⟨[77859, 15], [77717], .contexts [
        ⟨4794, true, false, [], [15]⟩,
        ⟨3, false, false, [77717], []⟩,
        ⟨4153, false, false, [], []⟩,
        ⟨4152, false, false, [], []⟩,
        ⟨4153, false, false, [], []⟩,
        ⟨4153, false, false, [], []⟩
      ]⟩,
    ⟨[77987, 15], [77855], .contexts [
        ⟨5625, true, false, [], [15]⟩,
        ⟨323, false, false, [77859], []⟩,
        ⟨324, false, false, [77859], []⟩,
        ⟨5630, false, false, [], [9]⟩,
        ⟨4764, false, false, [], []⟩,
        ⟨4765, false, false, [], []⟩,
        ⟨4766, false, false, [], []⟩,
        ⟨4766, false, false, [], []⟩,
        ⟨4769, false, false, [], []⟩,
        ⟨1118, true, false, [], [77855]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 088. -/
def y322TCContextRaw088 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[243, 77987], [243, 77987], .contexts []⟩,
    ⟨[77987, 11], [245, 77987], .contexts [
        ⟨5632, true, false, [242], [11]⟩,
        ⟨5632, true, false, [242], [11]⟩,
        ⟨1544, false, false, [242], [77987, 11]⟩,
        ⟨62, true, false, [242, 244, 77987], [11]⟩,
        ⟨5628, false, false, [242, 244], [7, 11]⟩,
        ⟨2821, true, false, [242], [7, 11]⟩,
        ⟨2820, true, false, [242], [7, 11]⟩,
        ⟨2819, true, false, [242], [7, 11]⟩,
        ⟨2818, true, false, [242], [7, 11]⟩,
        ⟨1635, true, false, [242], [11, 7, 11]⟩,
        ⟨1635, true, false, [242], [11, 7, 11]⟩,
        ⟨1633, true, false, [242], [11, 7, 11]⟩,
        ⟨5628, true, false, [242], [11, 7, 11]⟩,
        ⟨5627, true, false, [242], [11, 7, 11]⟩,
        ⟨4777, false, false, [242, 77987], []⟩,
        ⟨5626, false, false, [242], []⟩,
        ⟨1670, true, false, [], [77987]⟩
      ]⟩,
    ⟨[77989], [77859, 11], .source 39059⟩,
    ⟨[77859, 11], [77989], .contexts [
        ⟨5634, true, false, [], []⟩
      ]⟩,
    ⟨[77859, 11], [77989], .contexts [
        ⟨5635, false, false, [], []⟩
      ]⟩,
    ⟨[77989], [77989], .contexts []⟩,
    ⟨[77989], [77989], .contexts []⟩,
    ⟨[77859, 11], [77989], .contexts [
        ⟨5636, false, false, [], []⟩,
        ⟨5637, false, false, [], []⟩,
        ⟨5638, false, false, [], []⟩,
        ⟨5638, false, false, [], []⟩
      ]⟩,
    ⟨[77989], [77989], .contexts []⟩,
    ⟨[245, 77987], [245, 77987], .contexts []⟩,
    ⟨[77991], [77123, 7], .source 39060⟩,
    ⟨[77123, 7], [77991], .contexts [
        ⟨5642, true, false, [], []⟩
      ]⟩,
    ⟨[77991], [77991], .contexts []⟩,
    ⟨[77991], [77991], .contexts []⟩,
    ⟨[77123, 7], [77991], .contexts [
        ⟨5643, false, false, [], []⟩,
        ⟨5644, false, false, [], []⟩,
        ⟨5645, false, false, [], []⟩,
        ⟨5645, false, false, [], []⟩
      ]⟩,
    ⟨[315, 77983], [315, 77983], .contexts []⟩,
    ⟨[315, 77983], [315, 77983], .contexts []⟩,
    ⟨[77991, 1], [77991, 1], .contexts []⟩,
    ⟨[77991, 1], [315, 77983], .contexts [
        ⟨5649, false, false, [], []⟩,
        ⟨5646, true, false, [], [1]⟩,
        ⟨1764, false, false, [77123], []⟩,
        ⟨1765, false, false, [77123], []⟩,
        ⟨729, false, false, [], [7]⟩,
        ⟨1958, false, false, [], [7]⟩,
        ⟨1941, false, false, [], [7]⟩,
        ⟨1941, false, false, [], [7]⟩,
        ⟨5447, false, false, [315], []⟩,
        ⟨5647, false, false, [], []⟩,
        ⟨5648, false, false, [], []⟩,
        ⟨5456, false, false, [315], []⟩,
        ⟨2812, true, false, [], [77983]⟩
      ]⟩,
    ⟨[77983, 1], [317, 77991], .contexts [
        ⟨5650, true, false, [314], [1]⟩,
        ⟨18, false, false, [314, 77991], []⟩,
        ⟨1935, true, false, [], [77991]⟩
      ]⟩,
    ⟨[323, 77991], [323, 77991], .contexts []⟩,
    ⟨[323, 77991], [323, 77991], .contexts []⟩,
    ⟨[77991, 3], [77991, 3], .contexts []⟩,
    ⟨[323], [323], .contexts [
        ⟨24, false, false, [], [323]⟩
      ]⟩,
    ⟨[77993], [77125, 1], .source 39061⟩,
    ⟨[77125, 1], [77993], .contexts [
        ⟨5656, true, false, [], []⟩
      ]⟩,
    ⟨[77993, 1], [77125], .contexts [
        ⟨5657, true, false, [], [1]⟩,
        ⟨18, false, false, [77125], []⟩,
        ⟨435, false, false, [], []⟩
      ]⟩,
    ⟨[77993], [77993], .contexts []⟩,
    ⟨[77993], [77993], .contexts []⟩,
    ⟨[77125, 1], [77993], .contexts [
        ⟨5657, false, false, [], []⟩,
        ⟨5659, false, false, [], []⟩,
        ⟨5660, false, false, [], []⟩,
        ⟨5660, false, false, [], []⟩
      ]⟩,
    ⟨[77993], [77993], .contexts []⟩,
    ⟨[77993, 9], [77993, 9], .contexts []⟩,
    ⟨[77993, 9], [315, 77491], .contexts [
        ⟨5663, false, false, [], []⟩,
        ⟨5661, true, false, [], [9]⟩,
        ⟨786, false, false, [77125], []⟩,
        ⟨788, false, false, [77125], []⟩,
        ⟨727, false, false, [], [1, 9, 1]⟩,
        ⟨728, false, false, [], [1, 9, 1]⟩,
        ⟨432, false, false, [], [1, 9, 1]⟩,
        ⟨432, false, false, [], [1, 9, 1]⟩,
        ⟨729, false, false, [], [9, 1]⟩,
        ⟨1958, false, false, [], [9, 1]⟩,
        ⟨1941, false, false, [], [9, 1]⟩,
        ⟨1941, false, false, [], [9, 1]⟩,
        ⟨2806, false, false, [], [1]⟩,
        ⟨2807, false, false, [], [1]⟩,
        ⟨2808, false, false, [], [1]⟩,
        ⟨2809, false, false, [], [1]⟩,
        ⟨2836, false, false, [], []⟩,
        ⟨2837, false, false, [], []⟩,
        ⟨2838, false, false, [], []⟩,
        ⟨2839, false, false, [], []⟩,
        ⟨2843, false, false, [], []⟩
      ]⟩,
    ⟨[77993, 9], [315, 77491], .contexts [
        ⟨5664, false, false, [], []⟩,
        ⟨2844, false, false, [], []⟩
      ]⟩,
    ⟨[77491, 9], [317, 77993], .contexts [
        ⟨5665, true, false, [314], [9]⟩,
        ⟨76, false, false, [314, 77993], []⟩,
        ⟨1935, true, false, [], [77993]⟩
      ]⟩,
    ⟨[77993, 11], [77993, 11], .contexts []⟩,
    ⟨[77993, 11], [77129], .contexts [
        ⟨5667, false, false, [], []⟩,
        ⟨5661, true, false, [], [11]⟩,
        ⟨181, false, false, [77125], []⟩,
        ⟨182, false, false, [77125], []⟩,
        ⟨1979, false, false, [], [1]⟩,
        ⟨1992, false, false, [], []⟩,
        ⟨721, false, false, [], []⟩,
        ⟨442, false, false, [], []⟩,
        ⟨442, false, false, [], []⟩,
        ⟨1994, false, false, [], []⟩,
        ⟨1118, true, false, [], [77129]⟩
      ]⟩,
    ⟨[539, 77341], [539, 77341], .contexts []⟩,
    ⟨[1275], [539, 261], .source 702⟩,
    ⟨[77993, 15], [1275, 77337], .contexts [
        ⟨5661, true, false, [], [15]⟩,
        ⟨199, false, false, [77125], []⟩,
        ⟨200, false, false, [77125], []⟩,
        ⟨2788, false, false, [], [1]⟩,
        ⟨2791, false, false, [], [1]⟩,
        ⟨5669, false, false, [], [1]⟩,
        ⟨5669, false, false, [], [1]⟩,
        ⟨1330, false, false, [539], []⟩,
        ⟨2626, false, false, [539], []⟩,
        ⟨5670, true, false, [], [77337]⟩,
        ⟨2629, false, false, [1275], []⟩,
        ⟨24, true, false, [], [1275, 77337]⟩
      ]⟩,
    ⟨[1277], [1274], .source 703⟩,
    ⟨[77337, 15], [1277, 77993], .contexts [
        ⟨5671, true, false, [1274], [15]⟩,
        ⟨3, false, false, [1274, 77993], []⟩,
        ⟨5672, true, false, [], [77993]⟩
      ]⟩,
    ⟨[77993, 9], [315, 77491], .contexts [
        ⟨5663, false, false, [], []⟩,
        ⟨5665, false, false, [], []⟩,
        ⟨2837, false, false, [], []⟩,
        ⟨2839, false, false, [], []⟩,
        ⟨2839, false, false, [], []⟩
      ]⟩,
    ⟨[1279], [547, 705], .source 704⟩,
    ⟨[77993], [77993], .contexts []⟩,
    ⟨[1281], [1278], .source 705⟩,
    ⟨[1278], [1278], .contexts []⟩,
    ⟨[1281], [1278], .contexts [
        ⟨5677, false, false, [], []⟩,
        ⟨5678, false, false, [], []⟩,
        ⟨5678, false, false, [], []⟩
      ]⟩,
    ⟨[77331, 3], [1281, 77993], .contexts [
        ⟨5675, false, false, [1278], [77331, 3]⟩,
        ⟨3395, true, false, [1278, 547], [3]⟩,
        ⟨2861, true, false, [1278], [9, 3]⟩,
        ⟨2859, true, false, [1278], [9, 3]⟩,
        ⟨2858, true, false, [1278], [9, 3]⟩,
        ⟨2857, true, false, [1278], [9, 3]⟩,
        ⟨5674, true, false, [1278], [3, 9, 3]⟩,
        ⟨2415, false, false, [1278, 77993], []⟩,
        ⟨5676, false, false, [1278], []⟩,
        ⟨5662, false, false, [1278], []⟩,
        ⟨5679, true, false, [], [77993]⟩
      ]⟩,
    ⟨[1279], [1280], .contexts [
        ⟨5677, true, true, [], []⟩
      ]⟩,
    ⟨[77993, 3], [1279, 77331], .contexts [
        ⟨5680, true, false, [1280], [3]⟩,
        ⟨35, false, false, [1280, 77331], []⟩,
        ⟨5681, true, false, [], [77331]⟩
      ]⟩,
    ⟨[77591, 13], [77591, 13], .contexts []⟩,
    ⟨[692], [692], .contexts []⟩,
    ⟨[77591, 13], [695, 77993], .contexts [
        ⟨5683, false, false, [], []⟩,
        ⟨3354, true, false, [692], [13]⟩,
        ⟨3352, true, false, [692], [13]⟩,
        ⟨3351, true, false, [692], [13]⟩,
        ⟨3350, true, false, [692], [13]⟩,
        ⟨2930, true, false, [692], [9, 13]⟩,
        ⟨2929, true, false, [692], [9, 13]⟩,
        ⟨2928, true, false, [692], [9, 13]⟩,
        ⟨2927, true, false, [692], [9, 13]⟩,
        ⟨5674, true, false, [692], [13, 9, 13]⟩,
        ⟨828, false, false, [692, 77993], []⟩,
        ⟨5676, false, false, [692], []⟩,
        ⟨5662, false, false, [692], []⟩,
        ⟨5684, true, false, [], [77993]⟩,
        ⟨5684, true, false, [], [77993]⟩,
        ⟨3358, true, false, [], [77993]⟩
      ]⟩,
    ⟨[77993, 13], [693, 77591], .contexts [
        ⟨5685, true, false, [694], [13]⟩,
        ⟨98, false, false, [694, 77591], []⟩,
        ⟨3357, false, true, [], [77591]⟩
      ]⟩,
    ⟨[693, 77591], [693, 77591], .contexts []⟩,
    ⟨[77131, 11], [693, 77591], .contexts [
        ⟨446, true, false, [], [11]⟩,
        ⟨446, true, false, [], [11]⟩,
        ⟨720, true, false, [], [11]⟩,
        ⟨1997, true, false, [], [11]⟩,
        ⟨442, true, false, [], [13, 11]⟩,
        ⟨442, true, false, [], [13, 11]⟩,
        ⟨721, true, false, [], [13, 11]⟩,
        ⟨5668, true, false, [], [13, 11]⟩,
        ⟨5667, true, false, [], [13, 11]⟩,
        ⟨1060, false, false, [77993], []⟩,
        ⟨108, false, false, [77993], []⟩,
        ⟨5686, false, false, [], []⟩,
        ⟨5687, false, false, [], []⟩,
        ⟨5687, false, false, [], []⟩,
        ⟨3356, false, false, [693], []⟩,
        ⟨24, true, false, [], [693, 77591]⟩
      ]⟩,
    ⟨[77591, 11], [695, 77131], .contexts [
        ⟨5688, true, false, [692], [11]⟩,
        ⟨90, false, false, [692, 77131], []⟩,
        ⟨3357, true, false, [], [77131]⟩
      ]⟩,
    ⟨[695, 77993], [695, 77993], .contexts []⟩,
    ⟨[1283], [695, 1219], .source 706⟩,
    ⟨[1285], [1283, 843], .source 707⟩,
    ⟨[77591, 0], [77591, 1], .contexts [
        ⟨19, false, false, [77591], []⟩
      ]⟩,
    ⟨[1285, 77699, 13], [697, 77587], .contexts [
        ⟨5692, false, false, [], [77699, 13]⟩,
        ⟨4110, true, false, [1283], [13]⟩,
        ⟨3885, true, false, [1283], [13]⟩,
        ⟨5691, false, false, [], [77703, 1, 13]⟩,
        ⟨5530, true, false, [695], [1, 13]⟩,
        ⟨5658, true, false, [695], [13, 1, 13]⟩,
        ⟨5690, true, false, [], [1, 13, 1, 13]⟩,
        ⟨5690, true, false, [], [1, 13, 1, 13]⟩,
        ⟨5685, true, false, [], [1, 13, 1, 13]⟩,
        ⟨5683, true, false, [], [1, 13, 1, 13]⟩,
        ⟨3422, false, false, [77591], []⟩,
        ⟨5693, false, false, [], []⟩,
        ⟨3466, false, false, [], []⟩
      ]⟩,
    ⟨[77699, 13], [77699, 13], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 089. -/
def y322TCContextRaw089 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1287], [1284], .source 708⟩,
    ⟨[1289], [1287, 697], .source 709⟩,
    ⟨[1291], [1288], .source 710⟩,
    ⟨[1289, 77587], [1289, 77587], .contexts []⟩,
    ⟨[1289, 77585, 13], [77699, 3], .contexts [
        ⟨3125, true, false, [1289], [13]⟩,
        ⟨5699, true, false, [], [3, 13]⟩,
        ⟨5699, true, false, [], [3, 13]⟩,
        ⟨5697, false, false, [], [77587, 3, 13]⟩,
        ⟨5696, false, false, [], [697, 77587, 3, 13]⟩,
        ⟨3380, true, false, [1284, 697], [3, 13]⟩,
        ⟨5694, true, false, [1284], [3, 13]⟩,
        ⟨5695, true, false, [], [3, 13]⟩,
        ⟨5695, true, false, [], [3, 13]⟩,
        ⟨1881, false, false, [77699], []⟩,
        ⟨4115, false, false, [], []⟩
      ]⟩,
    ⟨[77693], [77693], .contexts []⟩,
    ⟨[1293], [1291, 1247], .source 711⟩,
    ⟨[77585, 13], [1293, 77693], .contexts [
        ⟨5700, false, false, [1288], []⟩,
        ⟨4113, false, false, [1288], []⟩,
        ⟨5560, false, false, [1288], []⟩,
        ⟨5559, false, false, [1288], []⟩,
        ⟨5559, false, false, [1288], []⟩,
        ⟨5701, false, false, [1288, 1247], []⟩,
        ⟨5698, true, false, [], [1247, 77693]⟩,
        ⟨5702, true, false, [], [77693]⟩
      ]⟩,
    ⟨[1295], [1292], .source 712⟩,
    ⟨[1295], [1295], .contexts []⟩,
    ⟨[77691], [1295, 77585], .contexts [
        ⟨5573, true, false, [], []⟩,
        ⟨5703, true, false, [1292], [13]⟩,
        ⟨98, false, false, [1292, 77585], []⟩,
        ⟨5704, true, false, [], [77585]⟩,
        ⟨5705, true, false, [], [77585]⟩
      ]⟩,
    ⟨[1293], [1294], .contexts [
        ⟨5704, true, true, [], []⟩
      ]⟩,
    ⟨[1294], [1294], .contexts []⟩,
    ⟨[77583, 11], [1293, 77687], .contexts [
        ⟨5704, false, false, [1294], [77583, 11]⟩,
        ⟨3121, true, false, [1294, 1292], [11]⟩,
        ⟨5706, true, false, [1294, 1292, 1294], [1, 11]⟩,
        ⟨3865, false, false, [1294, 1292, 1294], [11]⟩,
        ⟨3919, false, false, [1294, 1292, 1294], [11]⟩,
        ⟨24, true, false, [1294, 1292, 1294], [77689, 11]⟩,
        ⟨5707, true, false, [1294, 1292], [77689, 11]⟩,
        ⟨3862, false, false, [1294], []⟩,
        ⟨3921, false, false, [1294], []⟩,
        ⟨5708, true, false, [], [77687]⟩,
        ⟨5708, true, false, [], [77687]⟩,
        ⟨5707, true, false, [], [77687]⟩
      ]⟩,
    ⟨[749, 77327], [749, 77327], .contexts []⟩,
    ⟨[1293, 77687], [1293, 77687], .contexts []⟩,
    ⟨[77583, 11], [1293, 77687], .contexts [
        ⟨5709, false, false, [], []⟩,
        ⟨5711, false, false, [], []⟩,
        ⟨5711, false, false, [], []⟩
      ]⟩,
    ⟨[77583, 10], [77583, 11], .contexts [
        ⟨91, false, false, [77583], []⟩
      ]⟩,
    ⟨[77325, 3], [77325, 3], .contexts []⟩,
    ⟨[1297], [747, 1293], .source 713⟩,
    ⟨[77325, 3], [1297, 77687], .contexts [
        ⟨5714, false, false, [], []⟩,
        ⟨1305, true, false, [], [3]⟩,
        ⟨5710, true, false, [748], [11, 3]⟩,
        ⟨5710, true, false, [748], [11, 3]⟩,
        ⟨3472, true, false, [748], [11, 3]⟩,
        ⟨976, false, false, [748, 77583], []⟩,
        ⟨5713, false, false, [748], []⟩,
        ⟨5712, false, false, [748], []⟩,
        ⟨5587, false, false, [748, 1293], []⟩,
        ⟨3471, false, true, [], [1293, 77687]⟩,
        ⟨5715, true, false, [], [77687]⟩
      ]⟩,
    ⟨[1299], [1296], .source 714⟩,
    ⟨[77687, 3], [1299, 77325], .contexts [
        ⟨5716, true, false, [1296], [3]⟩,
        ⟨35, false, false, [1296, 77325], []⟩,
        ⟨5717, true, false, [], [77325]⟩
      ]⟩,
    ⟨[1297, 77687], [1297, 77687], .contexts []⟩,
    ⟨[1297, 77687], [1297, 77687], .contexts []⟩,
    ⟨[1297, 77685], [1297, 77685], .contexts []⟩,
    ⟨[77685, 3], [77685, 3], .contexts []⟩,
    ⟨[1296], [1296], .contexts []⟩,
    ⟨[77685, 3], [1299, 77323], .contexts [
        ⟨5722, false, false, [], []⟩,
        ⟨5721, true, false, [1296], [3]⟩,
        ⟨3859, true, false, [], [3]⟩,
        ⟨5720, true, false, [1296], [9, 3]⟩,
        ⟨5720, true, false, [1296], [9, 3]⟩,
        ⟨5719, true, false, [1296], [9, 3]⟩,
        ⟨5716, true, false, [1296], [9, 3]⟩,
        ⟨5714, true, false, [1296], [9, 3]⟩,
        ⟨1010, false, false, [1296, 77325], []⟩,
        ⟨2660, false, false, [1296], []⟩,
        ⟨2659, false, false, [1296], []⟩,
        ⟨2661, false, false, [1296], []⟩,
        ⟨5723, true, false, [], [77323]⟩,
        ⟨5723, true, false, [], [77323]⟩,
        ⟨5717, true, false, [], [77323]⟩
      ]⟩,
    ⟨[77995], [77983, 5], .source 39062⟩,
    ⟨[77983, 5], [77995], .contexts [
        ⟨5725, true, false, [], []⟩
      ]⟩,
    ⟨[77995], [77995], .contexts []⟩,
    ⟨[77983, 3], [77859], .contexts [
        ⟨5450, false, false, [], []⟩,
        ⟨5451, false, false, [], []⟩,
        ⟨4795, false, false, [], []⟩,
        ⟨4796, false, false, [], []⟩,
        ⟨4796, false, false, [], []⟩
      ]⟩,
    ⟨[77995], [77995], .contexts []⟩,
    ⟨[315, 77995], [315, 77995], .contexts []⟩,
    ⟨[315, 77995], [315, 77995], .contexts []⟩,
    ⟨[5, 7], [6, 4, 6, 4], .contexts [
        ⟨1775, false, false, [], [6, 4, 6, 4]⟩
      ]⟩,
    ⟨[6, 4, 6, 4], [7, 5, 7, 5], .contexts [
        ⟨63, false, false, [], [4, 6, 4]⟩,
        ⟨50, false, false, [7], [6, 4]⟩,
        ⟨63, false, false, [7, 5], [4]⟩,
        ⟨50, false, false, [7, 5, 7], []⟩
      ]⟩,
    ⟨[77997], [77983, 9], .source 39063⟩,
    ⟨[77983, 9], [77997], .contexts [
        ⟨5734, true, false, [], []⟩
      ]⟩,
    ⟨[77997], [77997], .contexts []⟩,
    ⟨[77983, 9], [77997], .contexts [
        ⟨5735, false, false, [], []⟩,
        ⟨5736, false, false, [], []⟩,
        ⟨5736, false, false, [], []⟩
      ]⟩,
    ⟨[77997, 3], [77997, 3], .contexts []⟩,
    ⟨[77997, 3], [77987], .contexts [
        ⟨5738, false, false, [], []⟩,
        ⟨5737, true, false, [], [3]⟩,
        ⟨306, false, false, [77983], []⟩,
        ⟨307, false, false, [77983], []⟩,
        ⟨5728, false, false, [], [9]⟩,
        ⟨5622, false, false, [], []⟩,
        ⟨5623, false, false, [], []⟩,
        ⟨5624, false, false, [], []⟩,
        ⟨5624, false, false, [], []⟩,
        ⟨5626, false, false, [], []⟩,
        ⟨1118, true, false, [], [77987]⟩
      ]⟩,
    ⟨[77997, 11], [243, 77997], .contexts [
        ⟨5736, true, false, [], [11]⟩,
        ⟨35, true, false, [77997], [11]⟩,
        ⟨5739, false, false, [], [3, 11]⟩,
        ⟨5641, true, false, [244], [3, 11]⟩,
        ⟨5641, true, false, [244], [3, 11]⟩,
        ⟨5633, true, false, [244], [3, 11]⟩,
        ⟨5624, true, false, [244], [11, 3, 11]⟩,
        ⟨5624, true, false, [244], [11, 3, 11]⟩,
        ⟨5623, true, false, [244], [11, 3, 11]⟩,
        ⟨5739, true, false, [244], [11, 3, 11]⟩,
        ⟨5738, true, false, [244], [11, 3, 11]⟩,
        ⟨2823, false, false, [244, 77997], []⟩,
        ⟨1639, true, false, [], [77997]⟩
      ]⟩,
    ⟨[77999], [77983, 11], .source 39064⟩,
    ⟨[77983, 11], [77999], .contexts [
        ⟨5741, true, false, [], []⟩
      ]⟩,
    ⟨[77999], [77999], .contexts []⟩,
    ⟨[77983, 11], [77999], .contexts [
        ⟨5742, false, false, [], []⟩,
        ⟨5743, false, false, [], []⟩,
        ⟨5743, false, false, [], []⟩
      ]⟩,
    ⟨[77999, 7], [77999, 7], .contexts []⟩,
    ⟨[77999, 7], [77985], .contexts [
        ⟨5745, false, false, [], []⟩,
        ⟨5744, true, false, [], [7]⟩,
        ⟨1088, false, false, [77983], []⟩,
        ⟨1089, false, false, [77983], []⟩,
        ⟨5447, true, false, [], [7, 11]⟩,
        ⟨62, false, false, [77119], [11]⟩,
        ⟨417, false, false, [], [11]⟩,
        ⟨416, false, false, [], [11]⟩,
        ⟨417, false, false, [], [11]⟩,
        ⟨417, false, false, [], [11]⟩,
        ⟨5464, false, false, [], []⟩,
        ⟨5465, false, false, [], []⟩,
        ⟨5466, false, false, [], []⟩,
        ⟨5466, false, false, [], []⟩,
        ⟨5475, false, false, [], []⟩,
        ⟨1118, true, false, [], [77985]⟩
      ]⟩,
    ⟨[77985, 7], [77999], .contexts [
        ⟨5746, true, false, [], [7]⟩,
        ⟨62, false, false, [77999], []⟩,
        ⟨5743, false, false, [], []⟩
      ]⟩,
    ⟨[243, 77997], [243, 77997], .contexts []⟩,
    ⟨[243, 77999], [243, 77999], .contexts []⟩,
    ⟨[243, 77999], [243, 77999], .contexts []⟩,
    ⟨[77999, 9], [77999, 9], .contexts []⟩,
    ⟨[77999], [77999], .contexts []⟩,
    ⟨[243], [243], .contexts [
        ⟨24, false, false, [], [243]⟩
      ]⟩,
    ⟨[77999, 9], [243, 77999], .contexts [
        ⟨5751, false, false, [], []⟩,
        ⟨5744, true, false, [], [9]⟩,
        ⟨344, false, false, [77983], []⟩,
        ⟨346, false, false, [77983], []⟩,
        ⟨5737, false, false, [], [11, 9, 11]⟩,
        ⟨5740, false, false, [], [9, 11]⟩,
        ⟨5748, false, false, [], [9, 11]⟩,
        ⟨5748, false, false, [], [9, 11]⟩,
        ⟨5735, true, false, [243], [9, 11]⟩,
        ⟨76, false, false, [243, 77983], [11]⟩,
        ⟨5448, false, false, [243], [11]⟩,
        ⟨5742, false, false, [243], []⟩,
        ⟨5749, false, false, [], []⟩,
        ⟨5750, false, false, [], []⟩,
        ⟨5752, false, false, [243], []⟩,
        ⟨5753, true, false, [], [77999]⟩
      ]⟩,
    ⟨[78001], [77991, 5], .source 39065⟩,
    ⟨[77991, 5], [78001], .contexts [
        ⟨5755, true, false, [], []⟩
      ]⟩,
    ⟨[77991, 5], [78001], .contexts [
        ⟨5756, false, false, [], []⟩
      ]⟩,
    ⟨[78001], [78001], .contexts []⟩,
    ⟨[78001], [78001], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 090. -/
def y322TCContextRaw090 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77991, 1], [315, 77983], .contexts [
        ⟨5649, false, false, [], []⟩,
        ⟨5650, false, false, [], []⟩,
        ⟨5647, false, false, [], []⟩,
        ⟨5648, false, false, [], []⟩,
        ⟨5648, false, false, [], []⟩
      ]⟩,
    ⟨[78001, 1], [78001, 1], .contexts []⟩,
    ⟨[78001, 1], [315, 77995], .contexts [
        ⟨5761, false, false, [], []⟩,
        ⟨5759, true, false, [], [1]⟩,
        ⟨5759, true, false, [], [1]⟩,
        ⟨5758, true, false, [], [1]⟩,
        ⟨5757, true, false, [], [1]⟩,
        ⟨256, false, false, [77991], []⟩,
        ⟨257, false, false, [77991], []⟩,
        ⟨5760, false, false, [], [5]⟩,
        ⟨5726, false, false, [315], []⟩,
        ⟨5730, false, false, [], []⟩,
        ⟨5731, false, false, [], []⟩,
        ⟨5729, false, false, [315], []⟩,
        ⟨2812, true, false, [], [77995]⟩
      ]⟩,
    ⟨[77991, 7], [77123], .contexts [
        ⟨5643, true, false, [], [7]⟩,
        ⟨62, false, false, [77123], []⟩,
        ⟨432, false, false, [], []⟩,
        ⟨728, false, false, [], []⟩,
        ⟨432, false, false, [], []⟩,
        ⟨432, false, false, [], []⟩
      ]⟩,
    ⟨[78003], [77991, 9], .source 39066⟩,
    ⟨[77991, 9], [78003], .contexts [
        ⟨5764, true, false, [], []⟩
      ]⟩,
    ⟨[77991, 9], [78003], .contexts [
        ⟨5765, false, false, [], []⟩
      ]⟩,
    ⟨[78003], [78003], .contexts []⟩,
    ⟨[78003], [78003], .contexts []⟩,
    ⟨[77991, 3], [323, 77991], .contexts [
        ⟨5654, false, false, [], []⟩,
        ⟨5646, true, false, [], [3]⟩,
        ⟨1769, false, false, [77123], []⟩,
        ⟨1770, false, false, [77123], []⟩,
        ⟨1964, false, false, [], [7]⟩,
        ⟨5643, false, false, [323], []⟩,
        ⟨5652, false, false, [], []⟩,
        ⟨5653, false, false, [], []⟩,
        ⟨5655, true, false, [], [77991]⟩
      ]⟩,
    ⟨[78003, 7], [78003, 7], .contexts []⟩,
    ⟨[78005], [77991, 11], .source 39067⟩,
    ⟨[77991, 11], [78005], .contexts [
        ⟨5771, true, false, [], []⟩
      ]⟩,
    ⟨[78005, 11], [77991], .contexts [
        ⟨5772, true, false, [], [11]⟩,
        ⟨90, false, false, [77991], []⟩,
        ⟨5645, false, false, [], []⟩
      ]⟩,
    ⟨[77991, 11], [78005], .contexts [
        ⟨5772, false, false, [], []⟩
      ]⟩,
    ⟨[78005], [78005], .contexts []⟩,
    ⟨[78005], [78005], .contexts []⟩,
    ⟨[77991, 11], [78005], .contexts [
        ⟨5774, false, false, [], []⟩,
        ⟨5775, false, false, [], []⟩,
        ⟨5776, false, false, [], []⟩,
        ⟨5776, false, false, [], []⟩
      ]⟩,
    ⟨[315, 77999], [315, 77999], .contexts []⟩,
    ⟨[315, 77999], [315, 77999], .contexts []⟩,
    ⟨[315, 77999], [315, 77999], .contexts []⟩,
    ⟨[78005, 1], [78005, 1], .contexts []⟩,
    ⟨[78005, 1], [315, 77999], .contexts [
        ⟨5781, false, false, [], []⟩,
        ⟨5777, true, false, [], [1]⟩,
        ⟨992, false, false, [77991], []⟩,
        ⟨993, false, false, [77991], []⟩,
        ⟨5760, false, false, [], [11]⟩,
        ⟨5742, false, false, [315], []⟩,
        ⟨5778, false, false, [], []⟩,
        ⟨5779, false, false, [], []⟩,
        ⟨5780, false, false, [], []⟩,
        ⟨5752, false, false, [315], []⟩,
        ⟨2812, true, false, [], [77999]⟩
      ]⟩,
    ⟨[77999, 1], [317, 78005], .contexts [
        ⟨5782, true, false, [314], [1]⟩,
        ⟨18, false, false, [314, 78005], []⟩,
        ⟨1935, true, false, [], [78005]⟩
      ]⟩,
    ⟨[78005], [78005], .contexts []⟩,
    ⟨[77123, 11], [847, 77711], .contexts [
        ⟨4054, false, false, [], []⟩
      ]⟩,
    ⟨[847, 77711], [847, 77711], .contexts []⟩,
    ⟨[847, 77711], [847, 77711], .contexts []⟩,
    ⟨[78007], [77991, 13], .source 39068⟩,
    ⟨[77991, 13], [78007], .contexts [
        ⟨5788, true, false, [], []⟩
      ]⟩,
    ⟨[78007, 13], [77991], .contexts [
        ⟨5789, true, false, [], [13]⟩,
        ⟨98, false, false, [77991], []⟩,
        ⟨5645, false, false, [], []⟩
      ]⟩,
    ⟨[77991, 13], [78007], .contexts [
        ⟨5789, false, false, [], []⟩
      ]⟩,
    ⟨[78007], [78007], .contexts []⟩,
    ⟨[78007], [78007], .contexts []⟩,
    ⟨[77991, 13], [78007], .contexts [
        ⟨5791, false, false, [], []⟩,
        ⟨5792, false, false, [], []⟩,
        ⟨5793, false, false, [], []⟩,
        ⟨5793, false, false, [], []⟩
      ]⟩,
    ⟨[1301], [315, 31], .source 715⟩,
    ⟨[1303], [1301, 317], .source 716⟩,
    ⟨[78007], [78007], .contexts []⟩,
    ⟨[78007, 7], [78007, 7], .contexts []⟩,
    ⟨[1219], [1219], .contexts [
        ⟨24, false, false, [], [1219]⟩
      ]⟩,
    ⟨[78007, 7], [1219, 77705], .contexts [
        ⟨5798, false, false, [], []⟩,
        ⟨5794, true, false, [], [7]⟩,
        ⟨124, false, false, [77991], []⟩,
        ⟨125, false, false, [77991], []⟩,
        ⟨5763, false, false, [], [13]⟩,
        ⟨5523, false, false, [], []⟩,
        ⟨5524, false, false, [], []⟩,
        ⟨5525, false, false, [], []⟩,
        ⟨5525, false, false, [], []⟩,
        ⟨4075, false, false, [1219], []⟩,
        ⟨5799, true, false, [], [77705]⟩
      ]⟩,
    ⟨[1305], [1219, 831], .source 717⟩,
    ⟨[1307], [1305, 1217], .source 718⟩,
    ⟨[7, 15, 7, 15], [], .contexts [
        ⟨1790, false, false, [], []⟩
      ]⟩,
    ⟨[1309], [1306], .source 719⟩,
    ⟨[1306], [1306], .contexts []⟩,
    ⟨[78007, 15], [1309, 78007], .contexts [
        ⟨5802, false, false, [1306], [78007, 15]⟩,
        ⟨5506, false, false, [1306, 1305], [78007, 15]⟩,
        ⟨62, true, false, [1306, 1305, 1218, 78007], [15]⟩,
        ⟨5800, false, false, [1306, 1305, 1218], [7, 15]⟩,
        ⟨5801, false, false, [1306], [77705, 7, 15]⟩,
        ⟨4080, true, false, [1306, 1219], [7, 15]⟩,
        ⟨5525, true, false, [1306], [15, 7, 15]⟩,
        ⟨5525, true, false, [1306], [15, 7, 15]⟩,
        ⟨5524, true, false, [1306], [15, 7, 15]⟩,
        ⟨5800, true, false, [1306], [15, 7, 15]⟩,
        ⟨5798, true, false, [1306], [15, 7, 15]⟩,
        ⟨5803, false, false, [1306, 78007], []⟩,
        ⟨5797, false, false, [1306], []⟩,
        ⟨5805, true, false, [], [78007]⟩,
        ⟨5805, true, false, [], [78007]⟩,
        ⟨5804, true, false, [], [78007]⟩
      ]⟩,
    ⟨[78009], [77991, 15], .source 39069⟩,
    ⟨[77991, 15], [78009], .contexts [
        ⟨5807, true, false, [], []⟩
      ]⟩,
    ⟨[78009], [78009], .contexts []⟩,
    ⟨[77991, 15], [78009], .contexts [
        ⟨5808, false, false, [], []⟩,
        ⟨5809, false, false, [], []⟩,
        ⟨5809, false, false, [], []⟩
      ]⟩,
    ⟨[1311], [315, 505], .source 720⟩,
    ⟨[78009, 1], [1311, 77853], .contexts [
        ⟨5810, true, false, [], [1]⟩,
        ⟨17, false, false, [77991], []⟩,
        ⟨21, false, false, [77991], []⟩,
        ⟨5760, false, false, [], [15]⟩,
        ⟨5460, false, false, [315], []⟩,
        ⟨5811, true, false, [], [77853]⟩,
        ⟨5458, false, false, [1311], []⟩,
        ⟨24, true, false, [], [1311, 77853]⟩
      ]⟩,
    ⟨[1313], [1310], .source 721⟩,
    ⟨[77853, 1], [1313, 78009], .contexts [
        ⟨5812, true, false, [1310], [1]⟩,
        ⟨18, false, false, [1310, 78009], []⟩,
        ⟨5813, true, false, [], [78009]⟩
      ]⟩,
    ⟨[323, 78009], [323, 78009], .contexts []⟩,
    ⟨[323, 78009], [323, 78009], .contexts []⟩,
    ⟨[78009, 3], [78009, 3], .contexts []⟩,
    ⟨[78009], [78009], .contexts []⟩,
    ⟨[78009, 3], [323, 78009], .contexts [
        ⟨5817, false, false, [], []⟩,
        ⟨5810, true, false, [], [3]⟩,
        ⟨34, false, false, [77991], []⟩,
        ⟨37, false, false, [77991], []⟩,
        ⟨5654, false, false, [], [15]⟩,
        ⟨5769, false, false, [], [15]⟩,
        ⟨5652, false, false, [], [15]⟩,
        ⟨5653, false, false, [], [15]⟩,
        ⟨5653, false, false, [], [15]⟩,
        ⟨5808, false, false, [323], []⟩,
        ⟨5815, false, false, [], []⟩,
        ⟨5816, false, false, [], []⟩,
        ⟨5818, false, false, [323], []⟩,
        ⟨5655, true, false, [], [78009]⟩
      ]⟩,
    ⟨[539, 77343], [539, 77343], .contexts []⟩,
    ⟨[539, 77343], [539, 77343], .contexts []⟩,
    ⟨[78009, 7], [78009, 7], .contexts []⟩,
    ⟨[539], [539], .contexts [
        ⟨24, false, false, [], [539]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 091. -/
def y322TCContextRaw091 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1309, 78007], [1309, 78007], .contexts []⟩,
    ⟨[1309, 78009], [1309, 78009], .contexts []⟩,
    ⟨[1309, 78009], [1309, 78009], .contexts []⟩,
    ⟨[78009, 13], [78009, 13], .contexts []⟩,
    ⟨[1309], [1309], .contexts [
        ⟨24, false, false, [], [1309]⟩
      ]⟩,
    ⟨[78009, 13], [1309, 78009], .contexts [
        ⟨5827, false, false, [], []⟩,
        ⟨5810, true, false, [], [13]⟩,
        ⟨408, false, false, [77991], []⟩,
        ⟨410, false, false, [77991], []⟩,
        ⟨5794, false, false, [], [15, 13, 15]⟩,
        ⟨5806, false, false, [], [13, 15]⟩,
        ⟨5824, false, false, [], [13, 15]⟩,
        ⟨5824, false, false, [], [13, 15]⟩,
        ⟨5790, false, false, [1309], [15]⟩,
        ⟨5808, false, false, [1309], []⟩,
        ⟨5825, false, false, [], []⟩,
        ⟨5826, false, false, [], []⟩,
        ⟨5818, false, false, [1309], []⟩,
        ⟨5828, true, false, [], [78009]⟩
      ]⟩,
    ⟨[78011], [77127, 9], .source 39070⟩,
    ⟨[77127, 9], [78011], .contexts [
        ⟨5830, true, false, [], []⟩
      ]⟩,
    ⟨[77127, 9], [78011], .contexts [
        ⟨5831, false, false, [], []⟩
      ]⟩,
    ⟨[78011], [78011], .contexts []⟩,
    ⟨[78011], [78011], .contexts []⟩,
    ⟨[77127, 9], [78011], .contexts [
        ⟨5832, false, false, [], []⟩,
        ⟨5833, false, false, [], []⟩,
        ⟨5834, false, false, [], []⟩,
        ⟨5834, false, false, [], []⟩
      ]⟩,
    ⟨[78011], [78011], .contexts []⟩,
    ⟨[1063], [1063], .contexts [
        ⟨24, false, false, [], [1063]⟩
      ]⟩,
    ⟨[77127, 3], [323, 77127], .contexts [
        ⟨1984, false, false, [], []⟩
      ]⟩,
    ⟨[323, 77127], [323, 77127], .contexts []⟩,
    ⟨[323, 77127], [323, 77127], .contexts []⟩,
    ⟨[323, 78011], [323, 78011], .contexts []⟩,
    ⟨[323, 78011], [323, 78011], .contexts []⟩,
    ⟨[78011, 3], [78011, 3], .contexts []⟩,
    ⟨[317, 78011], [317, 78011], .contexts []⟩,
    ⟨[317, 78011], [317, 78011], .contexts []⟩,
    ⟨[78011, 5], [78011, 5], .contexts []⟩,
    ⟨[77127, 11], [77125], .contexts [
        ⟨725, false, false, [], []⟩,
        ⟨726, false, false, [], []⟩,
        ⟨435, false, false, [], []⟩,
        ⟨435, false, false, [], []⟩
      ]⟩,
    ⟨[1315], [847, 1189], .source 722⟩,
    ⟨[78011, 11], [78011, 11], .contexts []⟩,
    ⟨[1315], [1315], .contexts [
        ⟨24, false, false, [], [1315]⟩
      ]⟩,
    ⟨[78011, 11], [1315, 77971], .contexts [
        ⟨5849, false, false, [], []⟩,
        ⟨5835, true, false, [], [11]⟩,
        ⟨4147, false, false, [77127], []⟩,
        ⟨4149, false, false, [77127], []⟩,
        ⟨5847, false, false, [], [9, 11, 9]⟩,
        ⟨727, false, false, [], [11, 9]⟩,
        ⟨728, false, false, [], [11, 9]⟩,
        ⟨432, false, false, [], [11, 9]⟩,
        ⟨432, false, false, [], [11, 9]⟩,
        ⟨5785, false, false, [], [9]⟩,
        ⟨5786, false, false, [], [9]⟩,
        ⟨5787, false, false, [], [9]⟩,
        ⟨5787, false, false, [], [9]⟩,
        ⟨5345, false, false, [847], []⟩,
        ⟨5848, true, false, [], [77971]⟩,
        ⟨5342, false, false, [1315], []⟩,
        ⟨5850, true, false, [], [77971]⟩
      ]⟩,
    ⟨[1317], [1314], .source 723⟩,
    ⟨[78013], [77721, 13], .source 39071⟩,
    ⟨[77721, 13], [78013], .contexts [
        ⟨5853, true, false, [], []⟩
      ]⟩,
    ⟨[78013, 13], [77721], .contexts [
        ⟨5854, true, false, [], [13]⟩,
        ⟨98, false, false, [77721], []⟩,
        ⟨4204, false, false, [], []⟩
      ]⟩,
    ⟨[78013], [78013], .contexts []⟩,
    ⟨[77721, 13], [78013], .contexts [
        ⟨5854, false, false, [], []⟩,
        ⟨5856, false, false, [], []⟩,
        ⟨5856, false, false, [], []⟩
      ]⟩,
    ⟨[78013], [78013], .contexts []⟩,
    ⟨[78013, 1], [857, 78013], .contexts [
        ⟨5857, true, false, [], [1]⟩,
        ⟨387, false, false, [77721], []⟩,
        ⟨390, false, false, [77721], []⟩,
        ⟨4230, false, false, [], [13, 1, 13]⟩,
        ⟨4198, false, false, [], [1, 13]⟩,
        ⟨4199, true, false, [], [77719, 1, 13]⟩,
        ⟨4196, false, false, [], [1, 13]⟩,
        ⟨4197, false, false, [], [1, 13]⟩,
        ⟨4197, false, false, [], [1, 13]⟩,
        ⟨4201, false, false, [857], [13]⟩,
        ⟨5854, false, false, [857], []⟩,
        ⟨5858, false, false, [857], []⟩,
        ⟨4199, true, false, [], [78013]⟩
      ]⟩,
    ⟨[293, 77365], [293, 77365], .contexts []⟩,
    ⟨[293, 77365], [293, 77365], .contexts []⟩,
    ⟨[78013, 5], [78013, 5], .contexts []⟩,
    ⟨[78013, 5], [293, 77365], .contexts [
        ⟨5862, false, false, [], []⟩,
        ⟨5857, true, false, [], [5]⟩,
        ⟨116, false, false, [77721], []⟩,
        ⟨117, false, false, [77721], []⟩,
        ⟨4206, false, false, [], [13]⟩,
        ⟨4254, false, false, [], [13]⟩,
        ⟨1887, false, false, [], [13]⟩,
        ⟨1888, false, false, [], [13]⟩,
        ⟨1888, false, false, [], [13]⟩,
        ⟨2023, false, false, [293], []⟩,
        ⟨5860, false, false, [], []⟩,
        ⟨5861, false, false, [], []⟩,
        ⟨2028, false, false, [293], []⟩,
        ⟨4179, true, false, [], [77365]⟩
      ]⟩,
    ⟨[77365, 5], [295, 78013], .contexts [
        ⟨5863, true, false, [292], [5]⟩,
        ⟨49, false, false, [292, 78013], []⟩,
        ⟨1856, true, false, [], [78013]⟩
      ]⟩,
    ⟨[149, 78013], [149, 78013], .contexts []⟩,
    ⟨[149, 78013], [149, 78013], .contexts []⟩,
    ⟨[78013, 7], [78013, 7], .contexts []⟩,
    ⟨[135, 78013], [135, 78013], .contexts []⟩,
    ⟨[135, 78013], [135, 78013], .contexts []⟩,
    ⟨[78013, 9], [78013, 9], .contexts []⟩,
    ⟨[151, 78013], [151, 78013], .contexts []⟩,
    ⟨[151, 78013], [151, 78013], .contexts []⟩,
    ⟨[78013, 11], [78013, 11], .contexts []⟩,
    ⟨[305, 77211], [305, 77211], .contexts []⟩,
    ⟨[77721, 15, 13, 15], [305, 77721], .contexts [
        ⟨4221, false, false, [], [13, 15]⟩,
        ⟨4222, false, false, [], [13, 15]⟩,
        ⟨639, false, false, [], [13, 15]⟩,
        ⟨588, false, false, [], [13, 15]⟩,
        ⟨588, false, false, [], [13, 15]⟩,
        ⟨583, true, false, [], [13, 15]⟩,
        ⟨1880, true, false, [302], [5, 13, 15]⟩,
        ⟨1886, false, false, [302, 77209], [15]⟩,
        ⟨50, false, false, [302, 77209], [15]⟩,
        ⟨583, false, false, [302], [15]⟩,
        ⟨639, false, false, [302], [15]⟩,
        ⟨588, false, false, [302], [15]⟩,
        ⟨588, false, false, [302], [15]⟩,
        ⟨1002, false, false, [302], [15]⟩,
        ⟨1884, true, false, [], [77211, 15]⟩,
        ⟨5874, false, false, [], [15]⟩,
        ⟨5874, false, false, [], [15]⟩,
        ⟨4222, true, false, [305], [15]⟩,
        ⟨3, false, false, [305, 77721], []⟩,
        ⟨4204, false, false, [305], []⟩
      ]⟩,
    ⟨[305, 78013], [305, 78013], .contexts []⟩,
    ⟨[305, 78013], [305, 78013], .contexts []⟩,
    ⟨[78013, 15], [78013, 15], .contexts []⟩,
    ⟨[305], [305], .contexts [
        ⟨24, false, false, [], [305]⟩
      ]⟩,
    ⟨[78013, 15], [305, 78013], .contexts [
        ⟨5878, false, false, [], []⟩,
        ⟨5857, true, false, [], [15]⟩,
        ⟨148, false, false, [77721], []⟩,
        ⟨150, false, false, [77721], []⟩,
        ⟨5875, false, false, [], [13]⟩,
        ⟨5854, false, false, [305], []⟩,
        ⟨5876, false, false, [], []⟩,
        ⟨5877, false, false, [], []⟩,
        ⟨5858, false, false, [305], []⟩,
        ⟨5879, true, false, [], [78013]⟩
      ]⟩,
    ⟨[78015], [78013, 3], .source 39072⟩,
    ⟨[78013, 3], [78015], .contexts [
        ⟨5881, true, false, [], []⟩
      ]⟩,
    ⟨[78015, 3], [78013], .contexts [
        ⟨5882, true, false, [], [3]⟩,
        ⟨35, false, false, [78013], []⟩,
        ⟨5856, false, false, [], []⟩
      ]⟩,
    ⟨[78015], [78015], .contexts []⟩,
    ⟨[78013, 3], [78015], .contexts [
        ⟨5882, false, false, [], []⟩,
        ⟨5884, false, false, [], []⟩,
        ⟨5884, false, false, [], []⟩
      ]⟩,
    ⟨[78015, 5], [77727], .contexts [
        ⟨5885, true, false, [], [5]⟩,
        ⟨1479, false, false, [78013], []⟩,
        ⟨1481, false, false, [78013], []⟩,
        ⟨5862, false, false, [], [3, 5, 3]⟩,
        ⟨5863, false, false, [], [3, 5, 3]⟩,
        ⟨5860, false, false, [], [3, 5, 3]⟩,
        ⟨5861, false, false, [], [3, 5, 3]⟩,
        ⟨5861, false, false, [], [3, 5, 3]⟩,
        ⟨2049, false, false, [293], [5, 3]⟩,
        ⟨2067, false, false, [293], [3]⟩,
        ⟨4273, false, false, [], [3]⟩,
        ⟨4274, false, false, [], [3]⟩,
        ⟨4275, false, false, [], [3]⟩,
        ⟨4278, false, false, [293], []⟩,
        ⟨1856, false, false, [293], [77727]⟩,
        ⟨4281, false, false, [], []⟩
      ]⟩,
    ⟨[78015, 5], [77727], .contexts [
        ⟨5886, false, false, [], []⟩,
        ⟨1118, true, false, [], [77727]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 092. -/
def y322TCContextRaw092 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78013, 7, 3], [149, 78015], .contexts [
        ⟨5867, false, false, [], [3]⟩,
        ⟨5867, false, false, [], [3]⟩,
        ⟨5857, true, false, [], [7, 3]⟩,
        ⟨124, false, false, [77721], [3]⟩,
        ⟨125, false, false, [77721], [3]⟩,
        ⟨4211, false, false, [], [13, 3]⟩,
        ⟨4213, false, false, [], [13, 3]⟩,
        ⟨4184, true, false, [], [77721, 13, 3]⟩,
        ⟨4209, false, false, [], [13, 3]⟩,
        ⟨4210, false, false, [], [13, 3]⟩,
        ⟨4210, false, false, [], [13, 3]⟩,
        ⟨5854, false, false, [149], [3]⟩,
        ⟨5865, false, false, [], [3]⟩,
        ⟨5866, false, false, [], [3]⟩,
        ⟨5858, false, false, [149], [3]⟩,
        ⟨4184, true, false, [], [78013, 3]⟩,
        ⟨5865, false, false, [], [3]⟩,
        ⟨5866, false, false, [], [3]⟩,
        ⟨5866, false, false, [], [3]⟩,
        ⟨5882, false, false, [149], []⟩
      ]⟩,
    ⟨[78015], [78015], .contexts []⟩,
    ⟨[78015, 9], [135, 78015], .contexts [
        ⟨5885, true, false, [], [9]⟩,
        ⟨1112, false, false, [78013], []⟩,
        ⟨1113, false, false, [78013], []⟩,
        ⟨5870, false, false, [], [3]⟩,
        ⟨5870, false, false, [], [3]⟩,
        ⟨5857, true, false, [], [9, 3]⟩,
        ⟨130, false, false, [77721], [3]⟩,
        ⟨131, false, false, [77721], [3]⟩,
        ⟨4237, false, false, [], [13, 3]⟩,
        ⟨5854, false, false, [135], [3]⟩,
        ⟨5868, false, false, [], [3]⟩,
        ⟨5869, false, false, [], [3]⟩,
        ⟨5858, false, false, [135], [3]⟩,
        ⟨995, true, false, [], [78013, 3]⟩,
        ⟨5868, false, false, [], [3]⟩,
        ⟨5869, false, false, [], [3]⟩,
        ⟨5869, false, false, [], [3]⟩,
        ⟨5882, false, false, [135], []⟩
      ]⟩,
    ⟨[78015, 9], [135, 78015], .contexts [
        ⟨5890, false, false, [], []⟩,
        ⟨5889, false, false, [135], []⟩,
        ⟨995, true, false, [], [78015]⟩
      ]⟩,
    ⟨[78015, 11], [151, 78015], .contexts [
        ⟨5885, true, false, [], [11]⟩,
        ⟨231, false, false, [78013], []⟩,
        ⟨232, false, false, [78013], []⟩,
        ⟨5873, false, false, [], [3]⟩,
        ⟨5873, false, false, [], [3]⟩,
        ⟨5857, true, false, [], [11, 3]⟩,
        ⟨137, false, false, [77721], [3]⟩,
        ⟨138, false, false, [77721], [3]⟩,
        ⟨4241, false, false, [], [13, 3]⟩,
        ⟨5854, false, false, [151], [3]⟩,
        ⟨5871, false, false, [], [3]⟩,
        ⟨5872, false, false, [], [3]⟩,
        ⟨5858, false, false, [151], [3]⟩,
        ⟨4191, true, false, [], [78013, 3]⟩,
        ⟨5871, false, false, [], [3]⟩,
        ⟨5872, false, false, [], [3]⟩,
        ⟨5872, false, false, [], [3]⟩,
        ⟨5882, false, false, [151], []⟩
      ]⟩,
    ⟨[78015, 11], [151, 78015], .contexts [
        ⟨5892, false, false, [], []⟩,
        ⟨5889, false, false, [151], []⟩,
        ⟨4191, true, false, [], [78015]⟩
      ]⟩,
    ⟨[78015, 13], [77723], .contexts [
        ⟨5885, true, false, [], [13]⟩,
        ⟨238, false, false, [78013], []⟩,
        ⟨239, false, false, [78013], []⟩,
        ⟨5855, false, false, [], [3]⟩,
        ⟨4203, false, false, [], [3]⟩,
        ⟨4204, false, false, [], [3]⟩,
        ⟨4204, false, false, [], [3]⟩,
        ⟨4226, false, false, [], []⟩,
        ⟨4227, false, false, [], []⟩,
        ⟨4228, false, false, [], []⟩,
        ⟨4228, false, false, [], []⟩,
        ⟨4235, false, false, [], []⟩,
        ⟨1118, true, false, [], [77723]⟩
      ]⟩,
    ⟨[78017], [77729, 9], .source 39073⟩,
    ⟨[77729, 9], [78017], .contexts [
        ⟨5895, true, false, [], []⟩
      ]⟩,
    ⟨[78017, 9], [77729], .contexts [
        ⟨5896, true, false, [], [9]⟩,
        ⟨76, false, false, [77729], []⟩,
        ⟨4295, false, false, [], []⟩
      ]⟩,
    ⟨[78017], [78017], .contexts []⟩,
    ⟨[77729, 9], [78017], .contexts [
        ⟨5896, false, false, [], []⟩,
        ⟨5898, false, false, [], []⟩,
        ⟨5898, false, false, [], []⟩
      ]⟩,
    ⟨[77729, 1, 9, 1], [135, 77729], .contexts [
        ⟨4581, false, false, [], [9, 1]⟩,
        ⟨4270, false, false, [], [9, 1]⟩,
        ⟨4271, false, false, [], [9, 1]⟩,
        ⟨4271, false, false, [], [9, 1]⟩,
        ⟨4272, true, false, [], [9, 1]⟩,
        ⟨130, false, false, [77725], [1]⟩,
        ⟨131, false, false, [77725], [1]⟩,
        ⟨4259, false, false, [], [13, 1]⟩,
        ⟨4261, false, false, [], [13, 1]⟩,
        ⟨4257, false, false, [], [13, 1]⟩,
        ⟨4258, false, false, [], [13, 1]⟩,
        ⟨4258, false, false, [], [13, 1]⟩,
        ⟨4268, false, false, [135], [1]⟩,
        ⟨4279, false, false, [], [1]⟩,
        ⟨4280, false, false, [], [1]⟩,
        ⟨4281, false, false, [135], [1]⟩,
        ⟨995, true, false, [], [77727, 1]⟩,
        ⟨4279, false, false, [], [1]⟩,
        ⟨4280, false, false, [], [1]⟩,
        ⟨4280, false, false, [], [1]⟩,
        ⟨4292, false, false, [135], []⟩
      ]⟩,
    ⟨[135, 78017], [135, 78017], .contexts []⟩,
    ⟨[135, 78017], [135, 78017], .contexts []⟩,
    ⟨[78017, 1], [78017, 1], .contexts []⟩,
    ⟨[78017], [78017], .contexts []⟩,
    ⟨[78017, 1], [135, 78017], .contexts [
        ⟨5903, false, false, [], []⟩,
        ⟨5899, true, false, [], [1]⟩,
        ⟨1143, false, false, [77729], []⟩,
        ⟨1146, false, false, [77729], []⟩,
        ⟨5900, false, false, [], [9]⟩,
        ⟨5896, false, false, [135], []⟩,
        ⟨5901, false, false, [], []⟩,
        ⟨5902, false, false, [], []⟩,
        ⟨5904, false, false, [135], []⟩,
        ⟨995, true, false, [], [78017]⟩
      ]⟩,
    ⟨[145, 78017], [145, 78017], .contexts []⟩,
    ⟨[145, 78017], [145, 78017], .contexts []⟩,
    ⟨[78017, 13], [78017, 13], .contexts []⟩,
    ⟨[863, 78017], [863, 78017], .contexts []⟩,
    ⟨[863, 78017], [863, 78017], .contexts []⟩,
    ⟨[78017, 15], [78017, 15], .contexts []⟩,
    ⟨[78019], [78017, 11], .source 39074⟩,
    ⟨[78017, 11], [78019], .contexts [
        ⟨5912, true, false, [], []⟩
      ]⟩,
    ⟨[78019], [78019], .contexts []⟩,
    ⟨[78019], [78019], .contexts []⟩,
    ⟨[78017, 11], [78019], .contexts [
        ⟨5913, false, false, [], []⟩,
        ⟨5914, false, false, [], []⟩,
        ⟨5915, false, false, [], []⟩,
        ⟨5915, false, false, [], []⟩
      ]⟩,
    ⟨[135, 78019], [135, 78019], .contexts []⟩,
    ⟨[135, 78019], [135, 78019], .contexts []⟩,
    ⟨[78019], [78019], .contexts []⟩,
    ⟨[78019, 1], [135, 78019], .contexts [
        ⟨5916, true, false, [], [1]⟩,
        ⟨992, false, false, [78017], []⟩,
        ⟨993, false, false, [78017], []⟩,
        ⟨5903, false, false, [], [11]⟩,
        ⟨5905, false, false, [], [11]⟩,
        ⟨5901, false, false, [], [11]⟩,
        ⟨5902, false, false, [], [11]⟩,
        ⟨5902, false, false, [], [11]⟩,
        ⟨5913, false, false, [135], []⟩,
        ⟨5917, false, false, [], []⟩,
        ⟨5918, false, false, [], []⟩,
        ⟨5919, false, false, [135], []⟩,
        ⟨995, true, false, [], [78019]⟩
      ]⟩,
    ⟨[151, 78019], [151, 78019], .contexts []⟩,
    ⟨[151, 78019], [151, 78019], .contexts []⟩,
    ⟨[151, 78019], [151, 78019], .contexts []⟩,
    ⟨[78019, 9], [78019, 9], .contexts []⟩,
    ⟨[78019, 9], [151, 78019], .contexts [
        ⟨5924, false, false, [], []⟩,
        ⟨5916, true, false, [], [9]⟩,
        ⟨344, false, false, [78017], []⟩,
        ⟨346, false, false, [78017], []⟩,
        ⟨5897, false, false, [], [11, 9, 11]⟩,
        ⟨4294, false, false, [], [11, 9, 11]⟩,
        ⟨4295, false, false, [], [11, 9, 11]⟩,
        ⟨4295, false, false, [], [11, 9, 11]⟩,
        ⟨4319, false, false, [], [9, 11]⟩,
        ⟨4297, false, false, [], [9, 11]⟩,
        ⟨4299, false, false, [], [9, 11]⟩,
        ⟨4299, false, false, [], [9, 11]⟩,
        ⟨5896, false, false, [151], [11]⟩,
        ⟨5913, false, false, [151], []⟩,
        ⟨5921, false, false, [], []⟩,
        ⟨5922, false, false, [], []⟩,
        ⟨5923, false, false, [], []⟩,
        ⟨5919, false, false, [151], []⟩
      ]⟩,
    ⟨[78019, 13], [145, 78019], .contexts [
        ⟨5916, true, false, [], [13]⟩,
        ⟨352, false, false, [78017], []⟩,
        ⟨353, false, false, [78017], []⟩,
        ⟨5908, false, false, [], [11]⟩,
        ⟨5908, false, false, [], [11]⟩,
        ⟨5899, true, false, [], [13, 11]⟩,
        ⟨315, false, false, [77729], [11]⟩,
        ⟨316, false, false, [77729], [11]⟩,
        ⟨4325, false, false, [], [9, 11]⟩,
        ⟨5896, false, false, [145], [11]⟩,
        ⟨5906, false, false, [], [11]⟩,
        ⟨5907, false, false, [], [11]⟩,
        ⟨5904, false, false, [145], [11]⟩,
        ⟨4175, true, false, [], [78017, 11]⟩,
        ⟨5906, false, false, [], [11]⟩,
        ⟨5907, false, false, [], [11]⟩,
        ⟨5907, false, false, [], [11]⟩,
        ⟨5913, false, false, [145], []⟩
      ]⟩,
    ⟨[78019, 15], [863, 78019], .contexts [
        ⟨5916, true, false, [], [15]⟩,
        ⟨358, false, false, [78017], []⟩,
        ⟨359, false, false, [78017], []⟩,
        ⟨5911, false, false, [], [11]⟩,
        ⟨5911, false, false, [], [11]⟩,
        ⟨5899, true, false, [], [15, 11]⟩,
        ⟨323, false, false, [77729], [11]⟩,
        ⟨324, false, false, [77729], [11]⟩,
        ⟨4329, false, false, [], [9, 11]⟩,
        ⟨5896, false, false, [863], [11]⟩,
        ⟨5909, false, false, [], [11]⟩,
        ⟨5910, false, false, [], [11]⟩,
        ⟨5904, false, false, [863], [11]⟩,
        ⟨4312, true, false, [], [78017, 11]⟩,
        ⟨5909, false, false, [], [11]⟩,
        ⟨5910, false, false, [], [11]⟩,
        ⟨5910, false, false, [], [11]⟩,
        ⟨5913, false, false, [863], []⟩
      ]⟩,
    ⟨[78021], [78019, 3], .source 39075⟩,
    ⟨[78019, 3], [78021], .contexts [
        ⟨5928, true, false, [], []⟩
      ]⟩,
    ⟨[78021, 3], [78019], .contexts [
        ⟨5929, true, false, [], [3]⟩,
        ⟨35, false, false, [78019], []⟩,
        ⟨5915, false, false, [], []⟩
      ]⟩,
    ⟨[78019, 3], [78021], .contexts [
        ⟨5929, false, false, [], []⟩
      ]⟩,
    ⟨[78021], [78021], .contexts []⟩,
    ⟨[151, 78021], [151, 78021], .contexts []⟩,
    ⟨[151, 78021], [151, 78021], .contexts []⟩,
    ⟨[151, 78021], [151, 78021], .contexts []⟩,
    ⟨[78021, 9], [78021, 9], .contexts []⟩,
    ⟨[78023], [78021, 5], .source 39076⟩,
    ⟨[78021, 5], [78023], .contexts [
        ⟨5937, true, false, [], []⟩
      ]⟩,
    ⟨[78021, 5], [78023], .contexts [
        ⟨5938, false, false, [], []⟩
      ]⟩,
    ⟨[78021, 5], [78023], .contexts [
        ⟨5939, false, false, [], []⟩
      ]⟩,
    ⟨[78023], [78023], .contexts []⟩,
    ⟨[78023], [78023], .contexts []⟩,
    ⟨[78021, 9, 5], [151, 78023], .contexts [
        ⟨5936, false, false, [], [5]⟩,
        ⟨5936, false, false, [], [5]⟩,
        ⟨5932, true, false, [], [9, 5]⟩,
        ⟨5932, true, false, [], [9, 5]⟩,
        ⟨5931, true, false, [], [9, 5]⟩,
        ⟨1112, false, false, [78019], [5]⟩,
        ⟨1113, false, false, [78019], [5]⟩,
        ⟨5924, false, false, [], [3, 5]⟩,
        ⟨5925, false, false, [], [3, 5]⟩,
        ⟨4191, true, false, [], [78019, 3, 5]⟩,
        ⟨5921, false, false, [], [3, 5]⟩,
        ⟨5923, false, false, [], [3, 5]⟩,
        ⟨5923, false, false, [], [3, 5]⟩,
        ⟨5929, false, false, [151], [5]⟩,
        ⟨5933, false, false, [], [5]⟩,
        ⟨5934, false, false, [], [5]⟩,
        ⟨5935, false, false, [], [5]⟩,
        ⟨4191, true, false, [], [78021, 5]⟩,
        ⟨5933, false, false, [], [5]⟩,
        ⟨5935, false, false, [], [5]⟩,
        ⟨5935, false, false, [], [5]⟩,
        ⟨5938, false, false, [151], []⟩
      ]⟩,
    ⟨[151, 78023], [151, 78023], .contexts []⟩,
    ⟨[151, 78023], [151, 78023], .contexts []⟩,
    ⟨[151, 78023], [151, 78023], .contexts []⟩,
    ⟨[78025], [78023, 1], .source 39077⟩,
    ⟨[78023, 1], [78025], .contexts [
        ⟨5947, true, false, [], []⟩
      ]⟩,
    ⟨[78025, 1], [78023], .contexts [
        ⟨5948, true, false, [], [1]⟩,
        ⟨18, false, false, [78023], []⟩,
        ⟨5942, false, false, [], []⟩
      ]⟩,
    ⟨[78025], [78025], .contexts []⟩,
    ⟨[78025], [78025], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 093. -/
def y322TCContextRaw093 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78027], [78025, 9], .source 39078⟩,
    ⟨[78025, 9], [78027], .contexts [
        ⟨5952, true, false, [], []⟩
      ]⟩,
    ⟨[78027], [78027], .contexts []⟩,
    ⟨[151, 78025], [151, 78025], .contexts []⟩,
    ⟨[151, 78025], [151, 78025], .contexts []⟩,
    ⟨[151, 78025], [151, 78025], .contexts []⟩,
    ⟨[78025, 1, 9, 1, 9], [151, 78027], .contexts [
        ⟨5949, false, false, [], [9, 1, 9]⟩,
        ⟨5941, false, false, [], [9, 1, 9]⟩,
        ⟨5942, false, false, [], [9, 1, 9]⟩,
        ⟨5942, false, false, [], [9, 1, 9]⟩,
        ⟨5942, true, false, [], [9, 1, 9]⟩,
        ⟨5942, true, false, [], [9, 1, 9]⟩,
        ⟨5941, true, false, [], [9, 1, 9]⟩,
        ⟨5940, true, false, [], [9, 1, 9]⟩,
        ⟨2076, false, false, [78021], [1, 9]⟩,
        ⟨2077, false, false, [78021], [1, 9]⟩,
        ⟨5943, false, false, [], [1, 9]⟩,
        ⟨5944, false, false, [], [1, 9]⟩,
        ⟨5945, false, false, [], [1, 9]⟩,
        ⟨5946, false, false, [], [1, 9]⟩,
        ⟨4191, true, false, [], [78023, 1, 9]⟩,
        ⟨5944, false, false, [], [1, 9]⟩,
        ⟨5946, false, false, [], [1, 9]⟩,
        ⟨5946, false, false, [], [1, 9]⟩,
        ⟨5948, false, false, [151], [9]⟩,
        ⟨5955, false, false, [], [9]⟩,
        ⟨5956, false, false, [], [9]⟩,
        ⟨5957, false, false, [], [9]⟩,
        ⟨5953, false, false, [151], []⟩
      ]⟩,
    ⟨[151, 78027], [151, 78027], .contexts []⟩,
    ⟨[151, 78027], [151, 78027], .contexts []⟩,
    ⟨[151, 78027], [151, 78027], .contexts []⟩,
    ⟨[78027, 1], [78027, 1], .contexts []⟩,
    ⟨[78029], [78027, 11], .source 39079⟩,
    ⟨[78027, 11], [78029], .contexts [
        ⟨5963, true, false, [], []⟩
      ]⟩,
    ⟨[78029], [78029], .contexts []⟩,
    ⟨[78029], [78029], .contexts []⟩,
    ⟨[151, 78029], [151, 78029], .contexts []⟩,
    ⟨[151, 78029], [151, 78029], .contexts []⟩,
    ⟨[78027, 1, 11], [151, 78029], .contexts [
        ⟨5962, false, false, [], [11]⟩,
        ⟨5962, false, false, [], [11]⟩,
        ⟨5954, true, false, [], [1, 11]⟩,
        ⟨5954, true, false, [], [1, 11]⟩,
        ⟨5953, true, false, [], [1, 11]⟩,
        ⟨1143, false, false, [78025], [11]⟩,
        ⟨1146, false, false, [78025], [11]⟩,
        ⟨5958, false, false, [], [11]⟩,
        ⟨5959, false, false, [], [11]⟩,
        ⟨5960, false, false, [], [11]⟩,
        ⟨5961, false, false, [], [11]⟩,
        ⟨4191, true, false, [], [78027, 11]⟩,
        ⟨5959, false, false, [], [11]⟩,
        ⟨5961, false, false, [], [11]⟩,
        ⟨5961, false, false, [], [11]⟩,
        ⟨5964, false, false, [151], []⟩,
        ⟨5967, false, false, [], []⟩,
        ⟨5968, false, false, [], []⟩
      ]⟩,
    ⟨[78031], [78029, 13], .source 39080⟩,
    ⟨[78033], [78031, 15], .source 39081⟩,
    ⟨[78031], [78031], .contexts []⟩,
    ⟨[78033], [78033], .contexts []⟩,
    ⟨[78035], [78033, 1], .source 39082⟩,
    ⟨[78037], [78035, 3], .source 39083⟩,
    ⟨[78035], [78035], .contexts []⟩,
    ⟨[78039], [78037, 5], .source 39084⟩,
    ⟨[78037], [78037], .contexts []⟩,
    ⟨[78041], [78039, 1], .source 39085⟩,
    ⟨[78039], [78039], .contexts []⟩,
    ⟨[78043], [78041, 9], .source 39086⟩,
    ⟨[78041], [78041], .contexts []⟩,
    ⟨[78045], [78043, 11], .source 39087⟩,
    ⟨[78043], [78043], .contexts []⟩,
    ⟨[78047], [78045, 1], .source 39088⟩,
    ⟨[78045], [78045], .contexts []⟩,
    ⟨[78049], [78047, 13], .source 39089⟩,
    ⟨[78047], [78047], .contexts []⟩,
    ⟨[78051], [78049, 15], .source 39090⟩,
    ⟨[78049], [78049], .contexts []⟩,
    ⟨[78053], [78051, 1], .source 39091⟩,
    ⟨[78051], [78051], .contexts []⟩,
    ⟨[78055], [78053, 3], .source 39092⟩,
    ⟨[78053], [78053], .contexts []⟩,
    ⟨[78057], [78055, 5], .source 39093⟩,
    ⟨[78055], [78055], .contexts []⟩,
    ⟨[78059], [78057, 1], .source 39094⟩,
    ⟨[78057], [78057], .contexts []⟩,
    ⟨[78061], [78059, 9], .source 39095⟩,
    ⟨[78059], [78059], .contexts []⟩,
    ⟨[78063], [78061, 11], .source 39096⟩,
    ⟨[78061], [78061], .contexts []⟩,
    ⟨[78065], [78063, 1], .source 39097⟩,
    ⟨[78063], [78063], .contexts []⟩,
    ⟨[78067], [78065, 13], .source 39098⟩,
    ⟨[78065], [78065], .contexts []⟩,
    ⟨[78069], [78067, 15], .source 39099⟩,
    ⟨[78067], [78067], .contexts []⟩,
    ⟨[78071], [78069, 1], .source 39100⟩,
    ⟨[78069], [78069], .contexts []⟩,
    ⟨[78073], [78071, 3], .source 39101⟩,
    ⟨[78071], [78071], .contexts []⟩,
    ⟨[78075], [78073, 5], .source 39102⟩,
    ⟨[78073], [78073], .contexts []⟩,
    ⟨[78077], [78075, 1], .source 39103⟩]

/-- Exact literal claimed equations and contextual derivations, block 094. -/
def y322TCContextRaw094 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78075], [78075], .contexts []⟩,
    ⟨[78079], [78077, 9], .source 39104⟩,
    ⟨[78077], [78077], .contexts []⟩,
    ⟨[78081], [78079, 11], .source 39105⟩,
    ⟨[78079], [78079], .contexts []⟩,
    ⟨[78083], [78081, 1], .source 39106⟩,
    ⟨[78081], [78081], .contexts []⟩,
    ⟨[78085], [78083, 13], .source 39107⟩,
    ⟨[78083], [78083], .contexts []⟩,
    ⟨[78087], [78085, 15], .source 39108⟩,
    ⟨[78085], [78085], .contexts []⟩,
    ⟨[78089], [78087, 1], .source 39109⟩,
    ⟨[78087], [78087], .contexts []⟩,
    ⟨[78089, 1], [78087], .contexts [
        ⟨6027, false, false, [], [1]⟩,
        ⟨18, false, false, [78087], []⟩,
        ⟨6028, false, false, [], []⟩
      ]⟩,
    ⟨[78091], [78089, 3], .source 39110⟩,
    ⟨[78089], [78089], .contexts []⟩,
    ⟨[78091, 3], [78089], .contexts [
        ⟨6030, false, false, [], [3]⟩,
        ⟨35, false, false, [78089], []⟩,
        ⟨6031, false, false, [], []⟩
      ]⟩,
    ⟨[78093], [78091, 5], .source 39111⟩,
    ⟨[78091, 5], [78093], .contexts [
        ⟨6033, true, false, [], []⟩
      ]⟩,
    ⟨[78091], [78091], .contexts []⟩,
    ⟨[78093, 5], [78091], .contexts [
        ⟨6034, true, false, [], [5]⟩,
        ⟨49, false, false, [78091], []⟩,
        ⟨6035, false, false, [], []⟩
      ]⟩,
    ⟨[78095], [78093, 1], .source 39112⟩,
    ⟨[78093], [78093], .contexts []⟩,
    ⟨[78095, 1], [78093], .contexts [
        ⟨6037, false, false, [], [1]⟩,
        ⟨18, false, false, [78093], []⟩,
        ⟨6038, false, false, [], []⟩
      ]⟩,
    ⟨[78097], [78095, 9], .source 39113⟩,
    ⟨[78095], [78095], .contexts []⟩,
    ⟨[78097, 9], [78095], .contexts [
        ⟨6040, false, false, [], [9]⟩,
        ⟨76, false, false, [78095], []⟩,
        ⟨6041, false, false, [], []⟩
      ]⟩,
    ⟨[78099], [78097, 11], .source 39114⟩,
    ⟨[78097], [78097], .contexts []⟩,
    ⟨[78099, 11], [78097], .contexts [
        ⟨6043, false, false, [], [11]⟩,
        ⟨90, false, false, [78097], []⟩,
        ⟨6044, false, false, [], []⟩
      ]⟩,
    ⟨[78101], [78099, 1], .source 39115⟩,
    ⟨[78099], [78099], .contexts []⟩,
    ⟨[78101, 1], [78099], .contexts [
        ⟨6046, false, false, [], [1]⟩,
        ⟨18, false, false, [78099], []⟩,
        ⟨6047, false, false, [], []⟩
      ]⟩,
    ⟨[78103], [78101, 13], .source 39116⟩,
    ⟨[78101], [78101], .contexts []⟩,
    ⟨[78103, 13], [78101], .contexts [
        ⟨6049, false, false, [], [13]⟩,
        ⟨98, false, false, [78101], []⟩,
        ⟨6050, false, false, [], []⟩
      ]⟩,
    ⟨[78105], [78103, 15], .source 39117⟩,
    ⟨[78103, 15], [78105], .contexts [
        ⟨6052, true, false, [], []⟩
      ]⟩,
    ⟨[78103], [78103], .contexts []⟩,
    ⟨[78105, 15], [78103], .contexts [
        ⟨6053, true, false, [], [15]⟩,
        ⟨3, false, false, [78103], []⟩,
        ⟨6054, false, false, [], []⟩
      ]⟩,
    ⟨[78107], [78105, 1], .source 39118⟩,
    ⟨[78105, 1], [78107], .contexts [
        ⟨6056, true, false, [], []⟩
      ]⟩,
    ⟨[78105], [78105], .contexts []⟩,
    ⟨[78107, 1], [78105], .contexts [
        ⟨6057, true, false, [], [1]⟩,
        ⟨18, false, false, [78105], []⟩,
        ⟨6058, false, false, [], []⟩
      ]⟩,
    ⟨[78109], [78107, 3], .source 39119⟩,
    ⟨[78107, 3], [78109], .contexts [
        ⟨6060, true, false, [], []⟩
      ]⟩,
    ⟨[78107], [78107], .contexts []⟩,
    ⟨[78109, 3], [78107], .contexts [
        ⟨6061, true, false, [], [3]⟩,
        ⟨35, false, false, [78107], []⟩,
        ⟨6062, false, false, [], []⟩
      ]⟩,
    ⟨[78111], [78109, 5], .source 39120⟩,
    ⟨[78109, 5], [78111], .contexts [
        ⟨6064, true, false, [], []⟩
      ]⟩,
    ⟨[78109], [78109], .contexts []⟩,
    ⟨[78111, 5], [78109], .contexts [
        ⟨6065, true, false, [], [5]⟩,
        ⟨49, false, false, [78109], []⟩,
        ⟨6066, false, false, [], []⟩
      ]⟩,
    ⟨[78113], [78111, 1], .source 39121⟩,
    ⟨[78111], [78111], .contexts []⟩,
    ⟨[78113, 1], [78111], .contexts [
        ⟨6068, false, false, [], [1]⟩,
        ⟨18, false, false, [78111], []⟩,
        ⟨6069, false, false, [], []⟩
      ]⟩,
    ⟨[78115], [78113, 9], .source 39122⟩,
    ⟨[78113, 9], [78115], .contexts [
        ⟨6071, true, false, [], []⟩
      ]⟩,
    ⟨[78113], [78113], .contexts []⟩,
    ⟨[78115, 9], [78113], .contexts [
        ⟨6072, true, false, [], [9]⟩,
        ⟨76, false, false, [78113], []⟩,
        ⟨6073, false, false, [], []⟩
      ]⟩,
    ⟨[78115], [78115], .contexts []⟩,
    ⟨[78115], [78115], .contexts []⟩,
    ⟨[78113, 1], [78111], .contexts [
        ⟨6070, false, false, [], []⟩,
        ⟨6069, false, false, [], []⟩,
        ⟨6069, false, false, [], []⟩
      ]⟩,
    ⟨[78111, 5], [78109], .contexts [
        ⟨6067, false, false, [], []⟩
      ]⟩,
    ⟨[78109], [78109], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 095. -/
def y322TCContextRaw095 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78109, 3], [78107], .contexts [
        ⟨6063, false, false, [], []⟩
      ]⟩,
    ⟨[78107], [78107], .contexts []⟩,
    ⟨[78107, 1], [78105], .contexts [
        ⟨6059, false, false, [], []⟩
      ]⟩,
    ⟨[78105], [78105], .contexts []⟩,
    ⟨[78105, 15], [78103], .contexts [
        ⟨6055, false, false, [], []⟩
      ]⟩,
    ⟨[78103], [78103], .contexts []⟩,
    ⟨[78103, 13], [78101], .contexts [
        ⟨6051, false, false, [], []⟩
      ]⟩,
    ⟨[78101], [78101], .contexts []⟩,
    ⟨[78113, 1, 5, 3, 1, 15, 13], [78101], .contexts [
        ⟨6077, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨6078, false, false, [], [3, 1, 15, 13]⟩,
        ⟨6079, false, false, [], [3, 1, 15, 13]⟩,
        ⟨6066, false, false, [], [3, 1, 15, 13]⟩,
        ⟨6066, false, false, [], [3, 1, 15, 13]⟩,
        ⟨6080, false, false, [], [1, 15, 13]⟩,
        ⟨6081, false, false, [], [1, 15, 13]⟩,
        ⟨6062, false, false, [], [1, 15, 13]⟩,
        ⟨6062, false, false, [], [1, 15, 13]⟩,
        ⟨6082, false, false, [], [15, 13]⟩,
        ⟨6083, false, false, [], [15, 13]⟩,
        ⟨6058, false, false, [], [15, 13]⟩,
        ⟨6058, false, false, [], [15, 13]⟩,
        ⟨6084, false, false, [], [13]⟩,
        ⟨6085, false, false, [], [13]⟩,
        ⟨6054, false, false, [], [13]⟩,
        ⟨6054, false, false, [], [13]⟩,
        ⟨6086, false, false, [], []⟩,
        ⟨6087, false, false, [], []⟩,
        ⟨6050, false, false, [], []⟩,
        ⟨6050, false, false, [], []⟩
      ]⟩,
    ⟨[78101, 1], [78099], .contexts [
        ⟨6048, false, false, [], []⟩
      ]⟩,
    ⟨[78099], [78099], .contexts []⟩,
    ⟨[78097, 9], [78095], .contexts [
        ⟨6042, false, false, [], []⟩
      ]⟩,
    ⟨[78095], [78095], .contexts []⟩,
    ⟨[78095, 1], [78093], .contexts [
        ⟨6039, false, false, [], []⟩
      ]⟩,
    ⟨[78093], [78093], .contexts []⟩,
    ⟨[78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5], [78091], .contexts [
        ⟨6088, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨6089, false, false, [], [11, 9, 1, 5]⟩,
        ⟨6090, false, false, [], [11, 9, 1, 5]⟩,
        ⟨6047, false, false, [], [11, 9, 1, 5]⟩,
        ⟨6047, false, false, [], [11, 9, 1, 5]⟩,
        ⟨6045, false, false, [], [9, 1, 5]⟩,
        ⟨6044, false, false, [], [9, 1, 5]⟩,
        ⟨6044, false, false, [], [9, 1, 5]⟩,
        ⟨6091, false, false, [], [1, 5]⟩,
        ⟨6092, false, false, [], [1, 5]⟩,
        ⟨6041, false, false, [], [1, 5]⟩,
        ⟨6041, false, false, [], [1, 5]⟩,
        ⟨6093, false, false, [], [5]⟩,
        ⟨6094, false, false, [], [5]⟩,
        ⟨6038, false, false, [], [5]⟩,
        ⟨6038, false, false, [], [5]⟩,
        ⟨6036, false, false, [], []⟩,
        ⟨6035, false, false, [], []⟩,
        ⟨6035, false, false, [], []⟩
      ]⟩,
    ⟨[78087], [78087], .contexts []⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1
    ], [78081], .contexts [
        ⟨6095, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨6032, false, false, [], [1, 15, 13, 1]⟩,
        ⟨6031, false, false, [], [1, 15, 13, 1]⟩,
        ⟨6031, false, false, [], [1, 15, 13, 1]⟩,
        ⟨6029, false, false, [], [15, 13, 1]⟩,
        ⟨6096, false, false, [], [15, 13, 1]⟩,
        ⟨6028, false, false, [], [15, 13, 1]⟩,
        ⟨6028, false, false, [], [15, 13, 1]⟩,
        ⟨6025, false, false, [], [15, 13, 1]⟩,
        ⟨3, false, false, [78085], [13, 1]⟩,
        ⟨6026, false, false, [], [13, 1]⟩,
        ⟨6026, false, false, [], [13, 1]⟩,
        ⟨6026, false, false, [], [13, 1]⟩,
        ⟨6023, false, false, [], [13, 1]⟩,
        ⟨98, false, false, [78083], [1]⟩,
        ⟨6024, false, false, [], [1]⟩,
        ⟨6024, false, false, [], [1]⟩,
        ⟨6024, false, false, [], [1]⟩,
        ⟨6021, false, false, [], [1]⟩,
        ⟨18, false, false, [78081], []⟩,
        ⟨6022, false, false, [], []⟩,
        ⟨6022, false, false, [], []⟩,
        ⟨6022, false, false, [], []⟩
      ]⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [78073], .contexts [
        ⟨6097, false, false, [], [11, 9, 1, 5]⟩,
        ⟨6019, false, false, [], [11, 9, 1, 5]⟩,
        ⟨90, false, false, [78079], [9, 1, 5]⟩,
        ⟨6020, false, false, [], [9, 1, 5]⟩,
        ⟨6020, false, false, [], [9, 1, 5]⟩,
        ⟨6020, false, false, [], [9, 1, 5]⟩,
        ⟨6017, false, false, [], [9, 1, 5]⟩,
        ⟨76, false, false, [78077], [1, 5]⟩,
        ⟨6018, false, false, [], [1, 5]⟩,
        ⟨6018, false, false, [], [1, 5]⟩,
        ⟨6018, false, false, [], [1, 5]⟩,
        ⟨6015, false, false, [], [1, 5]⟩,
        ⟨18, false, false, [78075], [5]⟩,
        ⟨6016, false, false, [], [5]⟩,
        ⟨6016, false, false, [], [5]⟩,
        ⟨6016, false, false, [], [5]⟩,
        ⟨6013, false, false, [], [5]⟩,
        ⟨49, false, false, [78073], []⟩,
        ⟨6014, false, false, [], []⟩,
        ⟨6014, false, false, [], []⟩,
        ⟨6014, false, false, [], []⟩
      ]⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13
    ], [78065], .contexts [
        ⟨6098, false, false, [], [3, 1, 15, 13]⟩,
        ⟨6011, false, false, [], [3, 1, 15, 13]⟩,
        ⟨35, false, false, [78071], [1, 15, 13]⟩,
        ⟨6012, false, false, [], [1, 15, 13]⟩,
        ⟨6012, false, false, [], [1, 15, 13]⟩,
        ⟨6012, false, false, [], [1, 15, 13]⟩,
        ⟨6009, false, false, [], [1, 15, 13]⟩,
        ⟨18, false, false, [78069], [15, 13]⟩,
        ⟨6010, false, false, [], [15, 13]⟩,
        ⟨6010, false, false, [], [15, 13]⟩,
        ⟨6010, false, false, [], [15, 13]⟩,
        ⟨6007, false, false, [], [15, 13]⟩,
        ⟨3, false, false, [78067], [13]⟩,
        ⟨6008, false, false, [], [13]⟩,
        ⟨6008, false, false, [], [13]⟩,
        ⟨6008, false, false, [], [13]⟩,
        ⟨6005, false, false, [], [13]⟩,
        ⟨98, false, false, [78065], []⟩,
        ⟨6006, false, false, [], []⟩,
        ⟨6006, false, false, [], []⟩,
        ⟨6006, false, false, [], []⟩
      ]⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1
    ], [78057], .contexts [
        ⟨6099, false, false, [], [1, 11, 9, 1]⟩,
        ⟨6003, false, false, [], [1, 11, 9, 1]⟩,
        ⟨18, false, false, [78063], [11, 9, 1]⟩,
        ⟨6004, false, false, [], [11, 9, 1]⟩,
        ⟨6004, false, false, [], [11, 9, 1]⟩,
        ⟨6004, false, false, [], [11, 9, 1]⟩,
        ⟨6001, false, false, [], [11, 9, 1]⟩,
        ⟨90, false, false, [78061], [9, 1]⟩,
        ⟨6002, false, false, [], [9, 1]⟩,
        ⟨6002, false, false, [], [9, 1]⟩,
        ⟨6002, false, false, [], [9, 1]⟩,
        ⟨5999, false, false, [], [9, 1]⟩,
        ⟨76, false, false, [78059], [1]⟩,
        ⟨6000, false, false, [], [1]⟩,
        ⟨6000, false, false, [], [1]⟩,
        ⟨6000, false, false, [], [1]⟩,
        ⟨5997, false, false, [], [1]⟩,
        ⟨18, false, false, [78057], []⟩,
        ⟨5998, false, false, [], []⟩,
        ⟨5998, false, false, [], []⟩,
        ⟨5998, false, false, [], []⟩
      ]⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [78049], .contexts [
        ⟨6100, false, false, [], [5, 3, 1, 15]⟩,
        ⟨5995, false, false, [], [5, 3, 1, 15]⟩,
        ⟨49, false, false, [78055], [3, 1, 15]⟩,
        ⟨5996, false, false, [], [3, 1, 15]⟩,
        ⟨5996, false, false, [], [3, 1, 15]⟩,
        ⟨5996, false, false, [], [3, 1, 15]⟩,
        ⟨5993, false, false, [], [3, 1, 15]⟩,
        ⟨35, false, false, [78053], [1, 15]⟩,
        ⟨5994, false, false, [], [1, 15]⟩,
        ⟨5994, false, false, [], [1, 15]⟩,
        ⟨5994, false, false, [], [1, 15]⟩,
        ⟨5991, false, false, [], [1, 15]⟩,
        ⟨18, false, false, [78051], [15]⟩,
        ⟨5992, false, false, [], [15]⟩,
        ⟨5992, false, false, [], [15]⟩,
        ⟨5992, false, false, [], [15]⟩,
        ⟨5989, false, false, [], [15]⟩,
        ⟨3, false, false, [78049], []⟩,
        ⟨5990, false, false, [], []⟩,
        ⟨5990, false, false, [], []⟩,
        ⟨5990, false, false, [], []⟩
      ]⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9
    ], [78041], .contexts [
        ⟨6101, false, false, [], [13, 1, 11, 9]⟩,
        ⟨5987, false, false, [], [13, 1, 11, 9]⟩,
        ⟨98, false, false, [78047], [1, 11, 9]⟩,
        ⟨5988, false, false, [], [1, 11, 9]⟩,
        ⟨5988, false, false, [], [1, 11, 9]⟩,
        ⟨5988, false, false, [], [1, 11, 9]⟩,
        ⟨5985, false, false, [], [1, 11, 9]⟩,
        ⟨18, false, false, [78045], [11, 9]⟩,
        ⟨5986, false, false, [], [11, 9]⟩,
        ⟨5986, false, false, [], [11, 9]⟩,
        ⟨5986, false, false, [], [11, 9]⟩,
        ⟨5983, false, false, [], [11, 9]⟩,
        ⟨90, false, false, [78043], [9]⟩,
        ⟨5984, false, false, [], [9]⟩,
        ⟨5984, false, false, [], [9]⟩,
        ⟨5984, false, false, [], [9]⟩,
        ⟨5981, false, false, [], [9]⟩,
        ⟨76, false, false, [78041], []⟩,
        ⟨5982, false, false, [], []⟩,
        ⟨5982, false, false, [], []⟩,
        ⟨5982, false, false, [], []⟩
      ]⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1
    ], [78033], .contexts [
        ⟨6102, false, false, [], [1, 5, 3, 1]⟩,
        ⟨5979, false, false, [], [1, 5, 3, 1]⟩,
        ⟨18, false, false, [78039], [5, 3, 1]⟩,
        ⟨5980, false, false, [], [5, 3, 1]⟩,
        ⟨5980, false, false, [], [5, 3, 1]⟩,
        ⟨5980, false, false, [], [5, 3, 1]⟩,
        ⟨5977, false, false, [], [5, 3, 1]⟩,
        ⟨49, false, false, [78037], [3, 1]⟩,
        ⟨5978, false, false, [], [3, 1]⟩,
        ⟨5978, false, false, [], [3, 1]⟩,
        ⟨5978, false, false, [], [3, 1]⟩,
        ⟨5975, false, false, [], [3, 1]⟩,
        ⟨35, false, false, [78035], [1]⟩,
        ⟨5976, false, false, [], [1]⟩,
        ⟨5976, false, false, [], [1]⟩,
        ⟨5976, false, false, [], [1]⟩,
        ⟨5974, false, false, [], [1]⟩,
        ⟨18, false, false, [78033], []⟩,
        ⟨5973, false, false, [], []⟩,
        ⟨5973, false, false, [], []⟩,
        ⟨5973, false, false, [], []⟩
      ]⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [151, 78027], .contexts [
        ⟨6103, false, false, [], [15, 13, 1, 11]⟩,
        ⟨5971, false, false, [], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [78031], [13, 1, 11]⟩,
        ⟨5972, false, false, [], [13, 1, 11]⟩,
        ⟨5972, false, false, [], [13, 1, 11]⟩,
        ⟨5972, false, false, [], [13, 1, 11]⟩,
        ⟨5970, false, false, [], [13, 1, 11]⟩,
        ⟨98, false, false, [78029], [1, 11]⟩,
        ⟨5966, false, false, [], [1, 11]⟩,
        ⟨5965, false, false, [], [1, 11]⟩,
        ⟨5966, false, false, [], [1, 11]⟩,
        ⟨5966, false, false, [], [1, 11]⟩,
        ⟨5966, true, false, [], [1, 11]⟩,
        ⟨5966, true, false, [], [1, 11]⟩,
        ⟨5965, true, false, [], [1, 11]⟩,
        ⟨5964, true, false, [], [1, 11]⟩,
        ⟨992, false, false, [78027], [11]⟩,
        ⟨993, false, false, [78027], [11]⟩,
        ⟨5969, false, false, [], [11]⟩,
        ⟨4191, true, false, [], [78029, 11]⟩,
        ⟨5967, false, false, [], [11]⟩,
        ⟨5968, false, false, [], [11]⟩,
        ⟨5968, false, false, [], [11]⟩,
        ⟨5964, true, false, [151], [11]⟩,
        ⟨90, false, false, [151, 78027], []⟩,
        ⟨5954, false, false, [151], []⟩,
        ⟨5959, false, false, [], []⟩,
        ⟨5960, false, false, [], []⟩,
        ⟨5961, false, false, [], []⟩
      ]⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3
    ], [151, 78019], .contexts [
        ⟨6104, false, false, [], [9, 1, 5, 3]⟩,
        ⟨5953, true, false, [151], [9, 1, 5, 3]⟩,
        ⟨76, false, false, [151, 78025], [1, 5, 3]⟩,
        ⟨5950, false, false, [151], [1, 5, 3]⟩,
        ⟨5955, false, false, [], [1, 5, 3]⟩,
        ⟨5956, false, false, [], [1, 5, 3]⟩,
        ⟨5957, false, false, [], [1, 5, 3]⟩,
        ⟨5949, false, false, [151], [5, 3]⟩,
        ⟨5944, false, false, [], [5, 3]⟩,
        ⟨5945, false, false, [], [5, 3]⟩,
        ⟨5946, false, false, [], [5, 3]⟩,
        ⟨5938, true, false, [151], [5, 3]⟩,
        ⟨49, false, false, [151, 78021], [3]⟩,
        ⟨5932, false, false, [151], [3]⟩,
        ⟨5933, false, false, [], [3]⟩,
        ⟨5934, false, false, [], [3]⟩,
        ⟨5935, false, false, [], [3]⟩,
        ⟨5930, false, false, [151], []⟩,
        ⟨5921, false, false, [], []⟩,
        ⟨5922, false, false, [], []⟩,
        ⟨5923, false, false, [], []⟩
      ]⟩,
    ⟨[1319], [151, 135], .source 724⟩,
    ⟨[1321], [1319, 863], .source 725⟩,
    ⟨[1323], [1321, 145], .source 726⟩,
    ⟨[1325], [1323, 135], .source 727⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11
    ], [1325, 78017], .contexts [
        ⟨6105, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨5920, false, false, [151], [15, 13, 1, 11]⟩,
        ⟨6106, true, false, [], [78019, 15, 13, 1, 11]⟩,
        ⟨5927, false, false, [1319], [13, 1, 11]⟩,
        ⟨5919, false, false, [1319, 863], [13, 1, 11]⟩,
        ⟨4312, true, false, [1319], [78019, 13, 1, 11]⟩,
        ⟨6107, true, false, [], [78019, 13, 1, 11]⟩,
        ⟨5926, false, false, [1321], [1, 11]⟩,
        ⟨5919, false, false, [1321, 145], [1, 11]⟩,
        ⟨4175, true, false, [1321], [78019, 1, 11]⟩,
        ⟨6108, true, false, [], [78019, 1, 11]⟩,
        ⟨5920, false, false, [1323], [11]⟩,
        ⟨6109, true, false, [], [78019, 11]⟩,
        ⟨5913, true, false, [1325], [11]⟩,
        ⟨90, false, false, [1325, 78017], []⟩,
        ⟨5898, false, false, [1325], []⟩
      ]⟩,
    ⟨[1327], [1325, 857], .source 728⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [1327, 78013], .contexts [
        ⟨6110, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨5897, false, false, [1325], [1, 5, 3, 1]⟩,
        ⟨4293, false, false, [1325], [5, 3, 1]⟩,
        ⟨5887, true, false, [1325], [5, 3, 1]⟩,
        ⟨49, false, false, [1325, 78015], [3, 1]⟩,
        ⟨5884, false, false, [1325], [3, 1]⟩,
        ⟨5883, false, false, [1325], [1]⟩,
        ⟨5859, false, false, [1325], []⟩,
        ⟨6111, true, false, [], [78013]⟩
      ]⟩,
    ⟨[1329], [1327, 305], .source 729⟩,
    ⟨[1331], [1329, 151], .source 730⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9
    ], [1331, 77363], .contexts [
        ⟨6112, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨5880, false, false, [1327], [13, 1, 11, 9]⟩,
        ⟨6113, true, false, [], [78013, 13, 1, 11, 9]⟩,
        ⟨5855, false, false, [1329], [1, 11, 9]⟩,
        ⟨4202, false, false, [1329], [11, 9]⟩,
        ⟨4192, false, false, [1329], [9]⟩,
        ⟨6114, true, false, [], [77719, 9]⟩,
        ⟨4186, false, false, [1331], []⟩
      ]⟩,
    ⟨[1333], [1331, 135], .source 731⟩,
    ⟨[1335], [1333, 289], .source 732⟩,
    ⟨[1337], [1335, 317], .source 733⟩,
    ⟨[1339], [1337, 539], .source 734⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [1339, 77343], .contexts [
        ⟨6115, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨1921, false, false, [1331], [5, 3, 1, 15]⟩,
        ⟨6116, true, false, [], [77363, 5, 3, 1, 15]⟩,
        ⟨1929, false, false, [1333], [3, 1, 15]⟩,
        ⟨6117, true, false, [], [77117, 3, 1, 15]⟩,
        ⟨415, false, false, [1335], [1, 15]⟩,
        ⟨1945, false, false, [1335], [15]⟩,
        ⟨6118, true, false, [], [77123, 15]⟩,
        ⟨2783, false, false, [1337], []⟩,
        ⟨6119, true, false, [], [77343]⟩
      ]⟩,
    ⟨[1341], [1339, 257], .source 735⟩,
    ⟨[1343], [1341, 271], .source 736⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1
    ], [1343, 77345], .contexts [
        ⟨6120, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨1629, false, false, [1339], [1, 11, 9, 1]⟩,
        ⟨6121, true, false, [], [77343, 1, 11, 9, 1]⟩,
        ⟨2774, false, false, [1341], [11, 9, 1]⟩,
        ⟨2766, false, false, [1341], [9, 1]⟩,
        ⟨1598, false, false, [1341], [1]⟩,
        ⟨6122, true, false, [], [77347, 1]⟩,
        ⟨1342, false, false, [1343], []⟩
      ]⟩,
    ⟨[1345], [1343, 261], .source 737⟩,
    ⟨[1347], [1345, 491], .source 738⟩,
    ⟨[1349], [1347, 503], .source 739⟩,
    ⟨[1351], [1349, 31], .source 740⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13
    ], [1351, 77985], .contexts [
        ⟨6123, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨1621, false, false, [1343], [3, 1, 15, 13]⟩,
        ⟨6124, true, false, [], [77345, 3, 1, 15, 13]⟩,
        ⟨2614, false, false, [1345], [1, 15, 13]⟩,
        ⟨6125, true, false, [], [77345, 1, 15, 13]⟩,
        ⟨1340, false, false, [1347], [15, 13]⟩,
        ⟨5482, false, false, [1347], [13]⟩,
        ⟨6126, true, false, [], [77985, 13]⟩,
        ⟨5480, false, false, [1349], []⟩,
        ⟨740, true, false, [1349], [77985]⟩,
        ⟨6127, true, false, [], [77985]⟩
      ]⟩,
    ⟨[1353], [1351, 1201], .source 741⟩,
    ⟨[1355], [1353, 845], .source 742⟩,
    ⟨[1357], [1355, 315], .source 743⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [1357, 77993], .contexts [
        ⟨6128, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨5470, false, false, [1351], [11, 9, 1, 5]⟩,
        ⟨6129, true, false, [], [77711, 11, 9, 1, 5]⟩,
        ⟨4055, false, false, [1353], [9, 1, 5]⟩,
        ⟨6130, true, false, [], [77123, 9, 1, 5]⟩,
        ⟨431, false, false, [1355], [1, 5]⟩,
        ⟨5657, false, false, [1355], [5]⟩,
        ⟨5661, true, false, [1355], [5]⟩,
        ⟨165, false, false, [1355, 77125], []⟩,
        ⟨166, false, false, [1355, 77125], []⟩,
        ⟨1986, false, false, [1355], [1]⟩,
        ⟨5657, false, false, [1355, 315], []⟩,
        ⟨5662, false, false, [1355, 315], []⟩,
        ⟨2812, true, false, [1355], [77993]⟩,
        ⟨6131, true, false, [], [77993]⟩
      ]⟩,
    ⟨[1359], [1357, 1279], .source 744⟩,
    ⟨[1361], [1359, 501], .source 745⟩,
    ⟨[1363], [1361, 719], .source 746⟩,
    ⟨[1363, 77451], [1363, 77451], .contexts []⟩,
    ⟨[1363, 77451], [1363, 77451], .contexts []⟩,
    ⟨[
      78113, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1
    ], [1363, 77451], .contexts [
        ⟨6132, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨5682, false, false, [1357], [1, 15, 13, 1]⟩,
        ⟨6133, true, false, [], [77331, 1, 15, 13, 1]⟩,
        ⟨2646, false, false, [1359], [15, 13, 1]⟩,
        ⟨6134, true, false, [], [77331, 15, 13, 1]⟩,
        ⟨1315, false, false, [1361], [13, 1]⟩,
        ⟨3402, false, false, [1361], [1]⟩,
        ⟨6135, true, false, [], [77453, 1]⟩,
        ⟨2256, false, false, [1363], []⟩,
        ⟨6136, false, false, [], []⟩,
        ⟨6137, false, false, [], []⟩
      ]⟩,
    ⟨[9, 11], [
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0
    ], .contexts [
        ⟨764, false, false, [0, 4, 2, 0], [
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0
        ]⟩
      ]⟩,
    ⟨[
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12
    ], [
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 12
    ], .contexts [
        ⟨257, false, false, [], [
          2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
          12
        ]⟩,
        ⟨36, false, false, [1, 5], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [1, 5, 3], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨20, false, false, [1, 5, 3, 1], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨108, false, false, [1, 5, 3, 1, 15], [0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [1, 5, 3, 1, 15, 13], [10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨91, false, false, [1, 5, 3, 1, 15, 13, 1], [8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨77, false, false, [1, 5, 3, 1, 15, 13, 1, 11], [0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [1, 5, 3, 1, 15, 13, 1, 11, 9], [4, 2, 0, 14, 12]⟩,
        ⟨50, false, false, [1, 5, 3, 1, 15, 13, 1, 11, 9, 1], [2, 0, 14, 12]⟩,
        ⟨36, false, false, [1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5], [0, 14, 12]⟩,
        ⟨19, false, false, [1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3], [14, 12]⟩,
        ⟨20, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1
        ], [12]⟩
      ]⟩,
    ⟨[
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8
    ], [
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 8
    ], .contexts [
        ⟨6140, false, false, [], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨108, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨91, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨77, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨50, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨36, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8]⟩,
        ⟨20, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8]⟩,
        ⟨108, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8]⟩,
        ⟨91, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1
        ], [8]⟩
      ]⟩,
    ⟨[
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2
    ], [
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 2
    ], .contexts [
        ⟨6141, false, false, [], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨77, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨50, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨36, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨20, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨108, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2]⟩,
        ⟨91, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2]⟩,
        ⟨77, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2]⟩,
        ⟨50, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1
        ], [2]⟩
      ]⟩,
    ⟨[
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12
    ], [
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 12
    ], .contexts [
        ⟨6142, false, false, [], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨36, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨20, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨108, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨91, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨77, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12]⟩,
        ⟨50, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12]⟩,
        ⟨36, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12]⟩,
        ⟨20, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1
        ], [12]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 096. -/
def y322TCContextRaw096 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8
    ], [
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 8
    ], .contexts [
        ⟨6143, false, false, [], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨108, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨91, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨77, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨50, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8]⟩,
        ⟨36, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8]⟩,
        ⟨20, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8]⟩,
        ⟨108, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8]⟩,
        ⟨91, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1
        ], [8]⟩
      ]⟩,
    ⟨[
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2
    ], [
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 2
    ], .contexts [
        ⟨6144, false, false, [], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨77, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨50, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨36, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨20, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2]⟩,
        ⟨108, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2]⟩,
        ⟨91, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2]⟩,
        ⟨77, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2]⟩,
        ⟨50, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1
        ], [2]⟩
      ]⟩,
    ⟨[
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12
    ], [
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 12
    ], .contexts [
        ⟨6145, false, false, [], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨36, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨20, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨108, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨91, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12]⟩,
        ⟨77, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12]⟩,
        ⟨50, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12]⟩,
        ⟨36, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12]⟩,
        ⟨20, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1
        ], [12]⟩
      ]⟩,
    ⟨[
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12,
      0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8,
      0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2,
      0, 14, 12, 0
    ], [
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1
    ], .contexts [
        ⟨6146, false, false, [], [0]⟩,
        ⟨108, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15
        ], [0]⟩,
        ⟨19, false, false, [
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
          1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
          1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
          1, 15, 13
        ], []⟩
      ]⟩,
    ⟨[78115, 11], [78115, 11], .contexts []⟩,
    ⟨[78115, 11], [1363, 77451], .contexts [
        ⟨6148, false, false, [], []⟩,
        ⟨6076, true, false, [], [11]⟩,
        ⟨6076, true, false, [], [11]⟩,
        ⟨6075, true, false, [], [11]⟩,
        ⟨6072, true, false, [], [11]⟩,
        ⟨6139, false, false, [78113], []⟩,
        ⟨6147, false, false, [78113], []⟩,
        ⟨6138, false, false, [], []⟩,
        ⟨2744, false, false, [1363], []⟩,
        ⟨24, true, false, [], [1363, 77451]⟩
      ]⟩,
    ⟨[1365], [1362], .source 747⟩,
    ⟨[77451, 11], [1365, 78115], .contexts [
        ⟨6149, true, false, [1362], [11]⟩,
        ⟨90, false, false, [1362, 78115], []⟩,
        ⟨6150, true, false, [], [78115]⟩
      ]⟩,
    ⟨[78115, 9], [78113], .contexts [
        ⟨6074, false, false, [], []⟩,
        ⟨6073, false, false, [], []⟩,
        ⟨6073, false, false, [], []⟩
      ]⟩,
    ⟨[78115, 11], [1363, 77451], .contexts [
        ⟨6148, false, false, [], []⟩,
        ⟨6149, false, false, [], []⟩,
        ⟨6136, false, false, [], []⟩,
        ⟨6137, false, false, [], []⟩,
        ⟨6137, false, false, [], []⟩
      ]⟩,
    ⟨[1367], [1363, 1015], .source 748⟩,
    ⟨[1369], [1367, 1365], .source 749⟩,
    ⟨[1369, 78113], [1369, 78113], .contexts []⟩,
    ⟨[1369, 78113], [1369, 78113], .contexts []⟩,
    ⟨[78113, 11], [78113, 11], .contexts []⟩,
    ⟨[78113], [78113], .contexts []⟩,
    ⟨[1369], [1369], .contexts []⟩,
    ⟨[1369], [1369], .contexts []⟩,
    ⟨[11, 3, 11, 3], [], .contexts [
        ⟨334, false, false, [], []⟩
      ]⟩,
    ⟨[1377], [1363, 729], .source 753⟩,
    ⟨[1379], [1377, 1365], .source 754⟩,
    ⟨[78115, 13], [78115, 13], .contexts []⟩,
    ⟨[1381], [1378], .source 755⟩,
    ⟨[1378], [1378], .contexts []⟩,
    ⟨[78115, 13], [1381, 78115], .contexts [
        ⟨6165, false, false, [], []⟩,
        ⟨6164, false, false, [1378], [78115, 13]⟩,
        ⟨6151, true, false, [1378, 1377], [13]⟩,
        ⟨6163, false, false, [1378], [77451, 11, 13]⟩,
        ⟨3429, true, false, [1378, 1363], [11, 13]⟩,
        ⟨6153, true, false, [1378], [13, 11, 13]⟩,
        ⟨1836, false, false, [1378, 78115], []⟩,
        ⟨6167, true, false, [], [78115]⟩,
        ⟨6167, true, false, [], [78115]⟩,
        ⟨6166, true, false, [], [78115]⟩
      ]⟩,
    ⟨[78113, 11], [1369, 78113], .contexts [
        ⟨6158, false, false, [], []⟩,
        ⟨6158, false, false, [], []⟩,
        ⟨6152, true, false, [], [11]⟩,
        ⟨4147, false, false, [78115], []⟩,
        ⟨4149, false, false, [78115], []⟩,
        ⟨6153, false, false, [], [9, 11, 9]⟩,
        ⟨4738, false, false, [1363], [11, 9]⟩,
        ⟨6154, true, false, [], [77451, 11, 9]⟩,
        ⟨6151, false, false, [1367], [9]⟩,
        ⟨6155, true, false, [], [78115, 9]⟩,
        ⟨6074, false, false, [1369], []⟩,
        ⟨6156, false, false, [], []⟩,
        ⟨6157, false, false, [], []⟩,
        ⟨6159, false, false, [1369], []⟩,
        ⟨6161, true, false, [], [78113]⟩,
        ⟨6160, true, false, [], [78113]⟩,
        ⟨24, true, false, [], [1369, 78113]⟩,
        ⟨6156, false, false, [], []⟩,
        ⟨6157, false, false, [], []⟩
      ]⟩,
    ⟨[78111, 11], [78111, 11], .contexts []⟩,
    ⟨[1383], [1368], .source 756⟩,
    ⟨[1368], [1368], .contexts []⟩,
    ⟨[1383], [1368], .contexts [
        ⟨6171, false, false, [], []⟩,
        ⟨6172, false, false, [], []⟩,
        ⟨6172, false, false, [], []⟩
      ]⟩,
    ⟨[1381, 78115], [1381, 78115], .contexts []⟩,
    ⟨[1380], [1380], .contexts []⟩,
    ⟨[1383, 78111], [1383, 78111], .contexts []⟩,
    ⟨[78111, 11, 5], [1383, 78109], .contexts [
        ⟨6170, false, false, [], [5]⟩,
        ⟨6170, false, false, [], [5]⟩,
        ⟨6070, true, false, [], [11, 5]⟩,
        ⟨6157, true, false, [1368], [1, 11, 5]⟩,
        ⟨6169, true, false, [1368], [1, 11, 5]⟩,
        ⟨1000, false, false, [1368, 78113], [5]⟩,
        ⟨19, false, false, [1368, 78113], [5]⟩,
        ⟨6077, false, false, [1368], [5]⟩,
        ⟨6173, true, false, [], [78111, 5]⟩,
        ⟨6176, false, false, [], [5]⟩,
        ⟨6176, false, false, [], [5]⟩,
        ⟨6067, false, false, [1383], []⟩
      ]⟩,
    ⟨[78111, 5], [78109], .contexts [
        ⟨6078, false, false, [], []⟩,
        ⟨6079, false, false, [], []⟩,
        ⟨6066, false, false, [], []⟩,
        ⟨6066, false, false, [], []⟩
      ]⟩,
    ⟨[78109, 11], [78109, 11], .contexts []⟩,
    ⟨[78109], [78109], .contexts []⟩,
    ⟨[1369], [1382], .contexts [
        ⟨6171, true, true, [], []⟩
      ]⟩,
    ⟨[1369], [1369], .contexts []⟩,
    ⟨[1382], [1382], .contexts []⟩,
    ⟨[1369], [1382], .contexts [
        ⟨6182, false, false, [], []⟩,
        ⟨6181, false, false, [], []⟩,
        ⟨6183, false, false, [], []⟩,
        ⟨6183, false, false, [], []⟩
      ]⟩,
    ⟨[1369, 78109], [1369, 78109], .contexts []⟩,
    ⟨[78109, 3], [78107], .contexts [
        ⟨6080, false, false, [], []⟩,
        ⟨6081, false, false, [], []⟩,
        ⟨6062, false, false, [], []⟩,
        ⟨6062, false, false, [], []⟩
      ]⟩,
    ⟨[78109, 2], [78109, 3], .contexts [
        ⟨36, false, false, [78109], []⟩
      ]⟩,
    ⟨[1369, 78107, 11], [78109, 2], .contexts [
        ⟨6063, true, false, [1369], [11]⟩,
        ⟨6185, true, false, [], [3, 11]⟩,
        ⟨6185, true, false, [], [3, 11]⟩,
        ⟨6184, false, false, [], [78109, 3, 11]⟩,
        ⟨6180, true, false, [1382], [3, 11]⟩,
        ⟨6178, true, false, [1382], [3, 11]⟩,
        ⟨50, true, false, [1382, 78111], [3, 11]⟩,
        ⟨1028, true, false, [1382, 78111], [3, 11]⟩,
        ⟨6177, false, false, [1382], [11, 3, 11]⟩,
        ⟨6179, true, false, [], [3, 11]⟩,
        ⟨6179, true, false, [], [3, 11]⟩,
        ⟨1040, false, false, [78109], []⟩
      ]⟩,
    ⟨[78107, 11], [78107, 11], .contexts []⟩,
    ⟨[78107], [78107], .contexts []⟩,
    ⟨[1383, 78107], [1383, 78107], .contexts []⟩,
    ⟨[78105, 11], [78105, 11], .contexts []⟩,
    ⟨[78105, 11], [1382, 78105], .contexts [
        ⟨6192, false, false, [], []⟩,
        ⟨6059, true, false, [], [11]⟩,
        ⟨6191, true, false, [1382], [1, 11]⟩,
        ⟨6191, true, false, [1382], [1, 11]⟩,
        ⟨6173, false, false, [1382], [78107, 1, 11]⟩,
        ⟨6190, true, false, [1382, 1368], [1, 11]⟩,
        ⟨6186, true, false, [1382, 1368], [1, 11]⟩,
        ⟨6187, true, false, [1382, 1368], [1, 11]⟩,
        ⟨6188, true, false, [1382, 1368], [1, 11]⟩,
        ⟨6189, true, false, [1382], [1, 11]⟩,
        ⟨6189, true, false, [1382], [1, 11]⟩,
        ⟨1000, false, false, [1382, 78107], []⟩,
        ⟨19, false, false, [1382, 78107], []⟩,
        ⟨6082, false, false, [1382], []⟩,
        ⟨6083, false, false, [1382], []⟩,
        ⟨6058, false, false, [1382], []⟩,
        ⟨6058, false, false, [1382], []⟩
      ]⟩,
    ⟨[78105], [78105], .contexts []⟩,
    ⟨[1369, 78105], [1369, 78105], .contexts []⟩,
    ⟨[78105, 11], [1369, 78105], .contexts [
        ⟨6192, false, false, [], []⟩,
        ⟨6193, false, false, [], []⟩,
        ⟨6194, false, false, [1382], []⟩,
        ⟨6184, true, false, [], [78105]⟩,
        ⟨6195, false, false, [], []⟩,
        ⟨6195, false, false, [], []⟩
      ]⟩,
    ⟨[78103, 11], [78103, 11], .contexts []⟩,
    ⟨[1383, 78103], [1383, 78103], .contexts []⟩,
    ⟨[1383, 78101], [1383, 78101], .contexts []⟩,
    ⟨[1383, 78101], [1383, 78101], .contexts []⟩,
    ⟨[78103, 11, 13], [1383, 78101], .contexts [
        ⟨6197, false, false, [], [13]⟩,
        ⟨6197, false, false, [], [13]⟩,
        ⟨6055, true, false, [], [11, 13]⟩,
        ⟨6196, true, false, [1368], [15, 11, 13]⟩,
        ⟨1054, false, false, [1368, 78105], [13]⟩,
        ⟨20, false, false, [1368, 78105], [13]⟩,
        ⟨6084, false, false, [1368], [13]⟩,
        ⟨6085, false, false, [1368], [13]⟩,
        ⟨6054, false, false, [1368], [13]⟩,
        ⟨6054, false, false, [1368], [13]⟩,
        ⟨6173, true, false, [], [78103, 13]⟩,
        ⟨6198, false, false, [], [13]⟩,
        ⟨6198, false, false, [], [13]⟩,
        ⟨6051, false, false, [1383], []⟩,
        ⟨6199, false, false, [], []⟩,
        ⟨6200, false, false, [], []⟩
      ]⟩,
    ⟨[78103, 13], [78101], .contexts [
        ⟨6086, false, false, [], []⟩,
        ⟨6087, false, false, [], []⟩,
        ⟨6050, false, false, [], []⟩,
        ⟨6050, false, false, [], []⟩
      ]⟩,
    ⟨[78103, 12], [78103, 13], .contexts [
        ⟨108, false, false, [78103], []⟩
      ]⟩,
    ⟨[78101, 11], [78101, 11], .contexts []⟩,
    ⟨[78101], [78101], .contexts []⟩,
    ⟨[78101, 11], [1369, 78101], .contexts [
        ⟨6204, false, false, [], []⟩,
        ⟨6201, true, false, [1382], [11]⟩,
        ⟨1060, false, false, [1382, 78103], []⟩,
        ⟨6203, false, false, [1382], []⟩,
        ⟨6202, false, false, [1382], []⟩,
        ⟨6205, false, false, [1382], []⟩,
        ⟨6184, true, false, [], [78101]⟩
      ]⟩,
    ⟨[1369, 78101], [1369, 78101], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 097. -/
def y322TCContextRaw097 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1369, 78097], [1369, 78097], .contexts []⟩,
    ⟨[1369, 78097], [1369, 78097], .contexts []⟩,
    ⟨[78097, 1], [78097, 1], .contexts []⟩,
    ⟨[78097, 1], [1383, 78101], .contexts [
        ⟨6210, false, false, [], []⟩,
        ⟨6209, true, false, [1368], [1]⟩,
        ⟨6208, true, false, [1368], [1]⟩,
        ⟨6045, true, false, [], [1]⟩,
        ⟨6048, true, false, [], [11, 1]⟩,
        ⟨6207, true, false, [1368], [1, 11, 1]⟩,
        ⟨6207, true, false, [1368], [1, 11, 1]⟩,
        ⟨6206, true, false, [1368], [1, 11, 1]⟩,
        ⟨6204, true, false, [1368], [1, 11, 1]⟩,
        ⟨1068, false, false, [1368, 78101], []⟩,
        ⟨6205, false, false, [1368], []⟩,
        ⟨6173, true, false, [], [78101]⟩
      ]⟩,
    ⟨[78101, 1], [78099], .contexts [
        ⟨6089, false, false, [], []⟩
      ]⟩,
    ⟨[78117], [77993, 7], .source 39123⟩,
    ⟨[77993, 7], [78117], .contexts [
        ⟨6213, true, false, [], []⟩
      ]⟩,
    ⟨[78117], [78117], .contexts []⟩,
    ⟨[78117], [78117], .contexts []⟩,
    ⟨[78119], [78003, 5], .source 39124⟩,
    ⟨[78003, 5], [78119], .contexts [
        ⟨6217, true, false, [], []⟩
      ]⟩,
    ⟨[78119], [78119], .contexts []⟩,
    ⟨[78119], [78119], .contexts []⟩,
    ⟨[78003, 7], [77125], .contexts [
        ⟨5770, false, false, [], []⟩,
        ⟨5770, false, false, [], []⟩,
        ⟨5768, true, false, [], [7]⟩,
        ⟨5768, true, false, [], [7]⟩,
        ⟨5767, true, false, [], [7]⟩,
        ⟨5766, true, false, [], [7]⟩,
        ⟨1809, false, false, [77991], []⟩,
        ⟨1810, false, false, [77991], []⟩,
        ⟨5763, false, false, [], [9]⟩,
        ⟨1965, false, false, [], []⟩,
        ⟨726, false, false, [], []⟩,
        ⟨435, false, false, [], []⟩,
        ⟨435, false, false, [], []⟩,
        ⟨1969, false, false, [], []⟩,
        ⟨1118, true, false, [], [77125]⟩,
        ⟨726, false, false, [], []⟩,
        ⟨435, false, false, [], []⟩,
        ⟨435, false, false, [], []⟩
      ]⟩,
    ⟨[78001], [78001], .contexts []⟩,
    ⟨[78001], [78001], .contexts [
        ⟨1118, true, false, [], [78001]⟩
      ]⟩,
    ⟨[78121], [78003, 11], .source 39125⟩,
    ⟨[78003, 11], [78121], .contexts [
        ⟨6224, true, false, [], []⟩
      ]⟩,
    ⟨[78003, 11], [78121], .contexts [
        ⟨6225, false, false, [], []⟩
      ]⟩,
    ⟨[78121], [78121], .contexts []⟩,
    ⟨[78121], [78121], .contexts []⟩,
    ⟨[78121, 7], [78121, 7], .contexts []⟩,
    ⟨[78121, 7], [77127], .contexts [
        ⟨6229, false, false, [], []⟩,
        ⟨6228, true, false, [], [7]⟩,
        ⟨6228, true, false, [], [7]⟩,
        ⟨6227, true, false, [], [7]⟩,
        ⟨6226, true, false, [], [7]⟩,
        ⟨1088, false, false, [78003], []⟩,
        ⟨1089, false, false, [78003], []⟩,
        ⟨6221, false, false, [], [11]⟩,
        ⟨1978, false, false, [], []⟩,
        ⟨724, false, false, [], []⟩,
        ⟨438, false, false, [], []⟩,
        ⟨438, false, false, [], []⟩,
        ⟨1982, false, false, [], []⟩,
        ⟨1118, true, false, [], [77127]⟩
      ]⟩,
    ⟨[78123], [78003, 13], .source 39126⟩,
    ⟨[78003, 13], [78123], .contexts [
        ⟨6231, true, false, [], []⟩
      ]⟩,
    ⟨[78003, 13], [78123], .contexts [
        ⟨6232, false, false, [], []⟩
      ]⟩,
    ⟨[78123], [78123], .contexts []⟩,
    ⟨[78123], [78123], .contexts []⟩,
    ⟨[78003, 13], [78123], .contexts [
        ⟨6233, false, false, [], []⟩,
        ⟨6234, false, false, [], []⟩,
        ⟨6235, false, false, [], []⟩,
        ⟨6235, false, false, [], []⟩
      ]⟩,
    ⟨[78123], [78123], .contexts []⟩,
    ⟨[77125, 13], [1219, 77703], .contexts [
        ⟨5530, false, false, [], []⟩
      ]⟩,
    ⟨[78123, 7], [78123, 7], .contexts []⟩,
    ⟨[1219, 77703], [1219, 77703], .contexts [
        ⟨4089, false, false, [1219], []⟩
      ]⟩,
    ⟨[1219, 77703], [1219, 77703], .contexts [
        ⟨5799, true, false, [], [77703]⟩
      ]⟩,
    ⟨[78123, 7], [1219, 77703], .contexts [
        ⟨6239, false, false, [], []⟩,
        ⟨6236, true, false, [], [7]⟩,
        ⟨124, false, false, [78003], []⟩,
        ⟨125, false, false, [78003], []⟩,
        ⟨6221, false, false, [], [13]⟩,
        ⟨6238, false, false, [], []⟩,
        ⟨5526, false, false, [], []⟩,
        ⟨5527, false, false, [], []⟩,
        ⟨5527, false, false, [], []⟩,
        ⟨6240, false, false, [], []⟩,
        ⟨6241, false, false, [], []⟩
      ]⟩,
    ⟨[1385], [1219, 849], .source 757⟩,
    ⟨[1387], [1385, 1217], .source 758⟩,
    ⟨[1389], [1386], .source 759⟩,
    ⟨[1386], [1386], .contexts []⟩,
    ⟨[78123, 15], [1389, 78123], .contexts [
        ⟨6244, false, false, [1386], [78123, 15]⟩,
        ⟨5506, false, false, [1386, 1385], [78123, 15]⟩,
        ⟨62, true, false, [1386, 1385, 1218, 78123], [15]⟩,
        ⟨6242, false, false, [1386, 1385, 1218], [7, 15]⟩,
        ⟨6243, false, false, [1386], [77703, 7, 15]⟩,
        ⟨4090, true, false, [1386, 1219], [7, 15]⟩,
        ⟨5527, true, false, [1386], [15, 7, 15]⟩,
        ⟨5527, true, false, [1386], [15, 7, 15]⟩,
        ⟨5526, true, false, [1386], [15, 7, 15]⟩,
        ⟨6242, true, false, [1386], [15, 7, 15]⟩,
        ⟨6239, true, false, [1386], [15, 7, 15]⟩,
        ⟨5803, false, false, [1386, 78123], []⟩,
        ⟨6237, false, false, [1386], []⟩,
        ⟨6246, true, false, [], [78123]⟩,
        ⟨6246, true, false, [], [78123]⟩,
        ⟨6245, true, false, [], [78123]⟩
      ]⟩,
    ⟨[78125], [78003, 15], .source 39127⟩,
    ⟨[78003, 15], [78125], .contexts [
        ⟨6248, true, false, [], []⟩
      ]⟩,
    ⟨[78003, 15], [78125], .contexts [
        ⟨6249, false, false, [], []⟩
      ]⟩,
    ⟨[78125], [78125], .contexts []⟩,
    ⟨[78125], [78125], .contexts []⟩,
    ⟨[78125], [78125], .contexts []⟩,
    ⟨[1389, 78123], [1389, 78123], .contexts []⟩,
    ⟨[1389, 78125], [1389, 78125], .contexts []⟩,
    ⟨[1389, 78125], [1389, 78125], .contexts []⟩,
    ⟨[78125, 13], [78125, 13], .contexts []⟩,
    ⟨[1389], [1389], .contexts [
        ⟨24, false, false, [], [1389]⟩
      ]⟩,
    ⟨[78127], [77127, 13], .source 39128⟩,
    ⟨[77127, 13], [78127], .contexts [
        ⟨6259, true, false, [], []⟩
      ]⟩,
    ⟨[77127, 13], [78127], .contexts [
        ⟨6260, false, false, [], []⟩
      ]⟩,
    ⟨[78127], [78127], .contexts []⟩,
    ⟨[78127], [78127], .contexts []⟩,
    ⟨[78127], [78127], .contexts []⟩,
    ⟨[78127, 11], [1219, 77703], .contexts [
        ⟨6263, true, false, [], [11]⟩,
        ⟨6263, true, false, [], [11]⟩,
        ⟨6262, true, false, [], [11]⟩,
        ⟨6261, true, false, [], [11]⟩,
        ⟨137, false, false, [77127], []⟩,
        ⟨138, false, false, [77127], []⟩,
        ⟨5847, false, false, [], [13]⟩,
        ⟨6238, false, false, [], []⟩,
        ⟨5526, false, false, [], []⟩,
        ⟨5527, false, false, [], []⟩,
        ⟨5527, false, false, [], []⟩,
        ⟨6240, false, false, [], []⟩,
        ⟨6241, false, false, [], []⟩
      ]⟩,
    ⟨[539, 77863], [539, 77863], .contexts []⟩,
    ⟨[78129], [77371, 3], .source 39129⟩,
    ⟨[77371, 3], [78129], .contexts [
        ⟨6267, true, false, [], []⟩
      ]⟩,
    ⟨[78129, 3], [77371], .contexts [
        ⟨6268, true, false, [], [3]⟩,
        ⟨35, false, false, [77371], []⟩,
        ⟨2094, false, false, [], []⟩
      ]⟩,
    ⟨[78129], [78129], .contexts []⟩,
    ⟨[77371, 3], [78129], .contexts [
        ⟨6268, false, false, [], []⟩,
        ⟨6270, false, false, [], []⟩,
        ⟨6270, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 098. -/
def y322TCContextRaw098 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[295, 77727], [295, 77727], .contexts []⟩,
    ⟨[295, 77731], [295, 77731], .contexts []⟩,
    ⟨[295, 77731], [295, 77731], .contexts []⟩,
    ⟨[78129, 1], [78129, 1], .contexts []⟩,
    ⟨[295], [295], .contexts [
        ⟨24, false, false, [], [295]⟩
      ]⟩,
    ⟨[78129, 1], [295, 77731], .contexts [
        ⟨6275, false, false, [], []⟩,
        ⟨6271, true, false, [], [1]⟩,
        ⟨213, false, false, [77371], []⟩,
        ⟨216, false, false, [77371], []⟩,
        ⟨2107, false, false, [], [3, 1, 3]⟩,
        ⟨4278, false, false, [], [1, 3]⟩,
        ⟨6272, false, false, [], [1, 3]⟩,
        ⟨6272, false, false, [], [1, 3]⟩,
        ⟨4292, false, false, [295], [3]⟩,
        ⟨4314, false, false, [295], []⟩,
        ⟨6273, false, false, [], []⟩,
        ⟨6274, false, false, [], []⟩,
        ⟨4323, false, false, [295], []⟩,
        ⟨6276, true, false, [], [77731]⟩
      ]⟩,
    ⟨[77731, 1], [293, 78129], .contexts [
        ⟨6277, true, false, [294], [1]⟩,
        ⟨18, false, false, [294, 78129], []⟩,
        ⟨1864, true, false, [], [78129]⟩
      ]⟩,
    ⟨[78129], [78129], .contexts []⟩,
    ⟨[77371, 15, 3], [329, 78129], .contexts [
        ⟨2102, false, false, [], [3]⟩,
        ⟨2102, false, false, [], [3]⟩,
        ⟨2095, true, false, [], [15, 3]⟩,
        ⟨199, false, false, [77369], [3]⟩,
        ⟨200, false, false, [77369], [3]⟩,
        ⟨2088, false, false, [], [1, 3]⟩,
        ⟨2089, false, false, [], [1, 3]⟩,
        ⟨2085, false, false, [], [1, 3]⟩,
        ⟨2087, false, false, [], [1, 3]⟩,
        ⟨2087, false, false, [], [1, 3]⟩,
        ⟨2091, false, false, [329], [3]⟩,
        ⟨2100, false, false, [], [3]⟩,
        ⟨2101, false, false, [], [3]⟩,
        ⟨2098, false, false, [329], [3]⟩,
        ⟨2046, true, false, [], [77371, 3]⟩,
        ⟨2100, false, false, [], [3]⟩,
        ⟨2101, false, false, [], [3]⟩,
        ⟨2101, false, false, [], [3]⟩,
        ⟨6268, false, false, [329], []⟩
      ]⟩,
    ⟨[77735, 5], [77735, 5], .contexts []⟩,
    ⟨[77735, 5], [293, 78129], .contexts [
        ⟨6281, false, false, [], []⟩,
        ⟨4353, true, false, [], [5]⟩,
        ⟨4334, true, false, [], [1, 5]⟩,
        ⟨6274, true, false, [294], [5, 1, 5]⟩,
        ⟨6274, true, false, [294], [5, 1, 5]⟩,
        ⟨6273, true, false, [294], [5, 1, 5]⟩,
        ⟨6277, true, false, [294], [5, 1, 5]⟩,
        ⟨6275, true, false, [294], [5, 1, 5]⟩,
        ⟨1909, false, false, [294, 78129], []⟩,
        ⟨6279, false, false, [294], []⟩,
        ⟨1877, true, false, [], [78129]⟩
      ]⟩,
    ⟨[78131], [77733, 9], .source 39130⟩,
    ⟨[77733, 9], [78131], .contexts [
        ⟨6283, true, false, [], []⟩
      ]⟩,
    ⟨[78131], [78131], .contexts []⟩,
    ⟨[78131], [78131], .contexts []⟩,
    ⟨[77733, 9], [78131], .contexts [
        ⟨6284, false, false, [], []⟩,
        ⟨6285, false, false, [], []⟩,
        ⟨6286, false, false, [], []⟩,
        ⟨6286, false, false, [], []⟩
      ]⟩,
    ⟨[145, 78131], [145, 78131], .contexts []⟩,
    ⟨[145, 78131], [145, 78131], .contexts []⟩,
    ⟨[145, 78131], [145, 78131], .contexts []⟩,
    ⟨[78131, 13], [78131, 13], .contexts []⟩,
    ⟨[78131, 13], [145, 78131], .contexts [
        ⟨6291, false, false, [], []⟩,
        ⟨6287, true, false, [], [13]⟩,
        ⟨315, false, false, [77733], []⟩,
        ⟨316, false, false, [77733], []⟩,
        ⟨4347, false, false, [], [9]⟩,
        ⟨4347, false, false, [], [9]⟩,
        ⟨4338, true, false, [], [13, 9]⟩,
        ⟨283, false, false, [77731], [9]⟩,
        ⟨284, false, false, [77731], [9]⟩,
        ⟨4343, false, false, [], [5, 9]⟩,
        ⟨4334, false, false, [145], [9]⟩,
        ⟨4344, false, false, [], [9]⟩,
        ⟨4345, false, false, [], [9]⟩,
        ⟨4346, false, false, [], [9]⟩,
        ⟨4342, false, false, [145], [9]⟩,
        ⟨4175, true, false, [], [77733, 9]⟩,
        ⟨4344, false, false, [], [9]⟩,
        ⟨4346, false, false, [], [9]⟩,
        ⟨4346, false, false, [], [9]⟩,
        ⟨6284, false, false, [145], []⟩,
        ⟨6288, false, false, [], []⟩,
        ⟨6289, false, false, [], []⟩,
        ⟨6290, false, false, [], []⟩
      ]⟩,
    ⟨[78131], [78131], .contexts []⟩,
    ⟨[863, 78131], [863, 78131], .contexts []⟩,
    ⟨[863, 78131], [863, 78131], .contexts []⟩,
    ⟨[78131, 15], [78131, 15], .contexts []⟩,
    ⟨[78133], [78131, 11], .source 39131⟩,
    ⟨[78131, 11], [78133], .contexts [
        ⟨6297, true, false, [], []⟩
      ]⟩,
    ⟨[78131, 11], [78133], .contexts [
        ⟨6298, false, false, [], []⟩
      ]⟩,
    ⟨[78133], [78133], .contexts []⟩,
    ⟨[78133], [78133], .contexts []⟩,
    ⟨[78131, 11], [78133], .contexts [
        ⟨6299, false, false, [], []⟩,
        ⟨6300, false, false, [], []⟩,
        ⟨6301, false, false, [], []⟩,
        ⟨6301, false, false, [], []⟩
      ]⟩,
    ⟨[78133], [78133], .contexts []⟩,
    ⟨[145, 78133], [145, 78133], .contexts []⟩,
    ⟨[145, 78133], [145, 78133], .contexts []⟩,
    ⟨[145, 78133], [145, 78133], .contexts []⟩,
    ⟨[863, 78133], [863, 78133], .contexts []⟩,
    ⟨[863, 78133], [863, 78133], .contexts []⟩,
    ⟨[78133, 15], [78133, 15], .contexts []⟩,
    ⟨[78133, 15], [863, 78133], .contexts [
        ⟨6309, false, false, [], []⟩,
        ⟨6302, true, false, [], [15]⟩,
        ⟨358, false, false, [78131], []⟩,
        ⟨359, false, false, [78131], []⟩,
        ⟨6296, false, false, [], [11]⟩,
        ⟨6296, false, false, [], [11]⟩,
        ⟨6287, true, false, [], [15, 11]⟩,
        ⟨323, false, false, [77733], [11]⟩,
        ⟨324, false, false, [77733], [11]⟩,
        ⟨4363, false, false, [], [9, 11]⟩,
        ⟨6284, false, false, [863], [11]⟩,
        ⟨6294, false, false, [], [11]⟩,
        ⟨6295, false, false, [], [11]⟩,
        ⟨6293, false, false, [863], [11]⟩,
        ⟨4312, true, false, [], [78131, 11]⟩,
        ⟨6294, false, false, [], [11]⟩,
        ⟨6295, false, false, [], [11]⟩,
        ⟨6295, false, false, [], [11]⟩,
        ⟨6298, false, false, [863], []⟩,
        ⟨6307, false, false, [], []⟩,
        ⟨6308, false, false, [], []⟩
      ]⟩,
    ⟨[78135], [78133, 1], .source 39132⟩,
    ⟨[78133, 1], [78135], .contexts [
        ⟨6311, true, false, [], []⟩
      ]⟩,
    ⟨[78135, 1], [78133], .contexts [
        ⟨6312, true, false, [], [1]⟩,
        ⟨18, false, false, [78133], []⟩,
        ⟨6301, false, false, [], []⟩
      ]⟩,
    ⟨[78135], [78135], .contexts []⟩,
    ⟨[78135], [78135], .contexts []⟩,
    ⟨[863, 78135], [863, 78135], .contexts []⟩,
    ⟨[863, 78135], [863, 78135], .contexts []⟩,
    ⟨[78137], [78135, 13], .source 39133⟩,
    ⟨[78135, 13], [78137], .contexts [
        ⟨6318, true, false, [], []⟩
      ]⟩,
    ⟨[78137, 13], [78135], .contexts [
        ⟨6319, true, false, [], [13]⟩,
        ⟨98, false, false, [78135], []⟩,
        ⟨6315, false, false, [], []⟩
      ]⟩,
    ⟨[78137], [78137], .contexts []⟩,
    ⟨[78137], [78137], .contexts []⟩,
    ⟨[78135, 1, 13, 1], [145, 78133, 1], .contexts [
        ⟨6313, false, false, [], [13, 1]⟩,
        ⟨6300, false, false, [], [13, 1]⟩,
        ⟨6301, false, false, [], [13, 1]⟩,
        ⟨6301, false, false, [], [13, 1]⟩,
        ⟨6302, true, false, [], [13, 1]⟩,
        ⟨352, false, false, [78131], [1]⟩,
        ⟨353, false, false, [78131], [1]⟩,
        ⟨6291, false, false, [], [11, 1]⟩,
        ⟨6292, false, false, [], [11, 1]⟩,
        ⟨6293, false, false, [145], [11, 1]⟩,
        ⟨4175, true, false, [], [78131, 11, 1]⟩,
        ⟨6288, false, false, [], [11, 1]⟩,
        ⟨6290, false, false, [], [11, 1]⟩,
        ⟨6290, false, false, [], [11, 1]⟩,
        ⟨6298, false, false, [145], [1]⟩,
        ⟨6304, false, false, [], [1]⟩,
        ⟨6305, false, false, [], [1]⟩,
        ⟨6306, false, false, [], [1]⟩,
        ⟨6303, false, false, [145], [1]⟩,
        ⟨4175, true, false, [], [78133, 1]⟩,
        ⟨6304, false, false, [], [1]⟩,
        ⟨6306, false, false, [], [1]⟩,
        ⟨6306, false, false, [], [1]⟩
      ]⟩,
    ⟨[145, 78135], [145, 78135], .contexts []⟩,
    ⟨[145, 78135], [145, 78135], .contexts []⟩,
    ⟨[145, 78135], [145, 78135], .contexts []⟩,
    ⟨[145, 78137], [145, 78137], .contexts []⟩,
    ⟨[145, 78137], [145, 78137], .contexts []⟩,
    ⟨[145, 78137], [145, 78137], .contexts []⟩,
    ⟨[78137, 1], [78137, 1], .contexts []⟩,
    ⟨[78137], [78137], .contexts []⟩,
    ⟨[78139], [78137, 15], .source 39134⟩,
    ⟨[78137, 15], [78139], .contexts [
        ⟨6332, true, false, [], []⟩
      ]⟩,
    ⟨[78139, 15], [78137], .contexts [
        ⟨6333, true, false, [], [15]⟩,
        ⟨3, false, false, [78137], []⟩,
        ⟨6322, false, false, [], []⟩
      ]⟩,
    ⟨[78139], [78139], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 099. -/
def y322TCContextRaw099 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78139], [78139], .contexts []⟩,
    ⟨[78137, 15], [78139], .contexts [
        ⟨6333, false, false, [], []⟩,
        ⟨6335, false, false, [], []⟩,
        ⟨6336, false, false, [], []⟩,
        ⟨6336, false, false, [], []⟩
      ]⟩,
    ⟨[145, 78139], [145, 78139], .contexts []⟩,
    ⟨[78137, 1, 15], [145, 78139], .contexts [
        ⟨6330, false, false, [], [15]⟩,
        ⟨6330, false, false, [], [15]⟩,
        ⟨6322, true, false, [], [1, 15]⟩,
        ⟨6322, true, false, [], [1, 15]⟩,
        ⟨6321, true, false, [], [1, 15]⟩,
        ⟨6319, true, false, [], [1, 15]⟩,
        ⟨387, false, false, [78135], [15]⟩,
        ⟨390, false, false, [78135], [15]⟩,
        ⟨6323, false, false, [], [13, 15]⟩,
        ⟨6312, false, false, [145], [13, 15]⟩,
        ⟨6324, false, false, [], [13, 15]⟩,
        ⟨6325, false, false, [], [13, 15]⟩,
        ⟨6326, false, false, [], [13, 15]⟩,
        ⟨6319, false, false, [145], [15]⟩,
        ⟨6327, false, false, [], [15]⟩,
        ⟨6328, false, false, [], [15]⟩,
        ⟨6329, false, false, [], [15]⟩,
        ⟨6331, false, false, [145], [15]⟩,
        ⟨4175, true, false, [], [78137, 15]⟩,
        ⟨6327, false, false, [], [15]⟩,
        ⟨6329, false, false, [], [15]⟩,
        ⟨6329, false, false, [], [15]⟩,
        ⟨6333, false, false, [145], []⟩,
        ⟨6338, false, false, [], []⟩
      ]⟩,
    ⟨[145, 78139], [145, 78139], .contexts []⟩,
    ⟨[78139], [78139], .contexts []⟩,
    ⟨[78139, 1], [145, 78139], .contexts [
        ⟨6337, true, false, [], [1]⟩,
        ⟨17, false, false, [78137], []⟩,
        ⟨21, false, false, [78137], []⟩,
        ⟨6339, false, false, [], []⟩,
        ⟨6340, false, false, [], []⟩,
        ⟨6341, false, false, [145], []⟩,
        ⟨4175, true, false, [], [78139]⟩
      ]⟩,
    ⟨[78137, 13, 15, 13], [863, 78135, 13], .contexts [
        ⟨6320, false, false, [], [15, 13]⟩,
        ⟨6314, false, false, [], [15, 13]⟩,
        ⟨6315, false, false, [], [15, 13]⟩,
        ⟨6315, false, false, [], [15, 13]⟩,
        ⟨6315, true, false, [], [15, 13]⟩,
        ⟨6315, true, false, [], [15, 13]⟩,
        ⟨6314, true, false, [], [15, 13]⟩,
        ⟨6312, true, false, [], [15, 13]⟩,
        ⟨199, false, false, [78133], [13]⟩,
        ⟨200, false, false, [78133], [13]⟩,
        ⟨6309, false, false, [], [1, 13]⟩,
        ⟨6310, false, false, [], [1, 13]⟩,
        ⟨6303, false, false, [863], [1, 13]⟩,
        ⟨4312, true, false, [], [78133, 1, 13]⟩,
        ⟨6307, false, false, [], [1, 13]⟩,
        ⟨6308, false, false, [], [1, 13]⟩,
        ⟨6308, false, false, [], [1, 13]⟩,
        ⟨6312, false, false, [863], [13]⟩,
        ⟨6316, false, false, [], [13]⟩,
        ⟨6317, false, false, [], [13]⟩,
        ⟨4312, true, false, [], [78135, 13]⟩,
        ⟨6316, false, false, [], [13]⟩,
        ⟨6317, false, false, [], [13]⟩,
        ⟨6317, false, false, [], [13]⟩
      ]⟩,
    ⟨[863, 78139], [863, 78139], .contexts []⟩,
    ⟨[863, 78139], [863, 78139], .contexts []⟩,
    ⟨[78139, 13], [78139, 13], .contexts []⟩,
    ⟨[78141], [78139, 3], .source 39135⟩,
    ⟨[78139, 3], [78141], .contexts [
        ⟨6347, true, false, [], []⟩
      ]⟩,
    ⟨[78141], [78141], .contexts []⟩,
    ⟨[78143], [78141, 5], .source 39136⟩,
    ⟨[78141, 5], [78143], .contexts [
        ⟨6350, true, false, [], []⟩
      ]⟩,
    ⟨[78143], [78143], .contexts []⟩,
    ⟨[78143], [78143], .contexts []⟩,
    ⟨[78145], [78143, 1], .source 39137⟩,
    ⟨[78143, 1], [78145], .contexts [
        ⟨6354, true, false, [], []⟩
      ]⟩,
    ⟨[78147], [78145, 9], .source 39138⟩,
    ⟨[78145, 9], [78147], .contexts [
        ⟨6356, true, false, [], []⟩
      ]⟩,
    ⟨[78145], [78145], .contexts []⟩,
    ⟨[78147, 9], [78145], .contexts [
        ⟨6357, true, false, [], [9]⟩,
        ⟨76, false, false, [78145], []⟩,
        ⟨6358, false, false, [], []⟩
      ]⟩,
    ⟨[78149], [78147, 11], .source 39139⟩,
    ⟨[78147, 11], [78149], .contexts [
        ⟨6360, true, false, [], []⟩
      ]⟩,
    ⟨[78147], [78147], .contexts []⟩,
    ⟨[78149, 11], [78147], .contexts [
        ⟨6361, true, false, [], [11]⟩,
        ⟨90, false, false, [78147], []⟩,
        ⟨6362, false, false, [], []⟩
      ]⟩,
    ⟨[78151], [78149, 1], .source 39140⟩,
    ⟨[78149, 1], [78151], .contexts [
        ⟨6364, true, false, [], []⟩
      ]⟩,
    ⟨[78149], [78149], .contexts []⟩,
    ⟨[78151, 1], [78149], .contexts [
        ⟨6365, true, false, [], [1]⟩,
        ⟨18, false, false, [78149], []⟩,
        ⟨6366, false, false, [], []⟩
      ]⟩,
    ⟨[78153], [78151, 13], .source 39141⟩,
    ⟨[78151, 13], [78153], .contexts [
        ⟨6368, true, false, [], []⟩
      ]⟩,
    ⟨[78151], [78151], .contexts []⟩,
    ⟨[78153, 13], [78151], .contexts [
        ⟨6369, true, false, [], [13]⟩,
        ⟨98, false, false, [78151], []⟩,
        ⟨6370, false, false, [], []⟩
      ]⟩,
    ⟨[78155], [78153, 15], .source 39142⟩,
    ⟨[78153, 15], [78155], .contexts [
        ⟨6372, true, false, [], []⟩
      ]⟩,
    ⟨[78153], [78153], .contexts []⟩,
    ⟨[78155, 15], [78153], .contexts [
        ⟨6373, true, false, [], [15]⟩,
        ⟨3, false, false, [78153], []⟩,
        ⟨6374, false, false, [], []⟩
      ]⟩,
    ⟨[78157], [78155, 1], .source 39143⟩,
    ⟨[78155, 1], [78157], .contexts [
        ⟨6376, true, false, [], []⟩
      ]⟩,
    ⟨[78155], [78155], .contexts []⟩,
    ⟨[78159], [78157, 3], .source 39144⟩,
    ⟨[78157], [78157], .contexts []⟩,
    ⟨[78159, 3], [78157], .contexts [
        ⟨6379, false, false, [], [3]⟩,
        ⟨35, false, false, [78157], []⟩,
        ⟨6380, false, false, [], []⟩
      ]⟩,
    ⟨[78161], [78159, 5], .source 39145⟩,
    ⟨[78159], [78159], .contexts []⟩,
    ⟨[78161, 5], [78159], .contexts [
        ⟨6382, false, false, [], [5]⟩,
        ⟨49, false, false, [78159], []⟩,
        ⟨6383, false, false, [], []⟩
      ]⟩,
    ⟨[78163], [78161, 1], .source 39146⟩,
    ⟨[78161], [78161], .contexts []⟩,
    ⟨[78163, 1], [78161], .contexts [
        ⟨6385, false, false, [], [1]⟩,
        ⟨18, false, false, [78161], []⟩,
        ⟨6386, false, false, [], []⟩
      ]⟩,
    ⟨[78165], [78163, 9], .source 39147⟩,
    ⟨[78163], [78163], .contexts []⟩,
    ⟨[78165, 9], [78163], .contexts [
        ⟨6388, false, false, [], [9]⟩,
        ⟨76, false, false, [78163], []⟩,
        ⟨6389, false, false, [], []⟩
      ]⟩,
    ⟨[78167], [78165, 11], .source 39148⟩,
    ⟨[78165], [78165], .contexts []⟩,
    ⟨[78167, 11], [78165], .contexts [
        ⟨6391, false, false, [], [11]⟩,
        ⟨90, false, false, [78165], []⟩,
        ⟨6392, false, false, [], []⟩
      ]⟩,
    ⟨[78169], [78167, 1], .source 39149⟩,
    ⟨[78167], [78167], .contexts []⟩,
    ⟨[78169, 1], [78167], .contexts [
        ⟨6394, false, false, [], [1]⟩,
        ⟨18, false, false, [78167], []⟩,
        ⟨6395, false, false, [], []⟩
      ]⟩,
    ⟨[78171], [78169, 13], .source 39150⟩,
    ⟨[78169], [78169], .contexts []⟩,
    ⟨[78171, 13], [78169], .contexts [
        ⟨6397, false, false, [], [13]⟩,
        ⟨98, false, false, [78169], []⟩,
        ⟨6398, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 100. -/
def y322TCContextRaw100 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78173], [78171, 15], .source 39151⟩,
    ⟨[78171], [78171], .contexts []⟩,
    ⟨[78173, 15], [78171], .contexts [
        ⟨6400, false, false, [], [15]⟩,
        ⟨3, false, false, [78171], []⟩,
        ⟨6401, false, false, [], []⟩
      ]⟩,
    ⟨[78175], [78173, 1], .source 39152⟩,
    ⟨[78173], [78173], .contexts []⟩,
    ⟨[78175, 1], [78173], .contexts [
        ⟨6403, false, false, [], [1]⟩,
        ⟨18, false, false, [78173], []⟩,
        ⟨6404, false, false, [], []⟩
      ]⟩,
    ⟨[78177], [78175, 3], .source 39153⟩,
    ⟨[78175], [78175], .contexts []⟩,
    ⟨[78177, 3], [78175], .contexts [
        ⟨6406, false, false, [], [3]⟩,
        ⟨35, false, false, [78175], []⟩,
        ⟨6407, false, false, [], []⟩
      ]⟩,
    ⟨[78179], [78177, 5], .source 39154⟩,
    ⟨[78177], [78177], .contexts []⟩,
    ⟨[78179, 5], [78177], .contexts [
        ⟨6409, false, false, [], [5]⟩,
        ⟨49, false, false, [78177], []⟩,
        ⟨6410, false, false, [], []⟩
      ]⟩,
    ⟨[78181], [78179, 1], .source 39155⟩,
    ⟨[78179], [78179], .contexts []⟩,
    ⟨[78181, 1], [78179], .contexts [
        ⟨6412, false, false, [], [1]⟩,
        ⟨18, false, false, [78179], []⟩,
        ⟨6413, false, false, [], []⟩
      ]⟩,
    ⟨[78183], [78181, 9], .source 39156⟩,
    ⟨[78181], [78181], .contexts []⟩,
    ⟨[78183, 9], [78181], .contexts [
        ⟨6415, false, false, [], [9]⟩,
        ⟨76, false, false, [78181], []⟩,
        ⟨6416, false, false, [], []⟩
      ]⟩,
    ⟨[78185], [78183, 11], .source 39157⟩,
    ⟨[78183], [78183], .contexts []⟩,
    ⟨[78185, 11], [78183], .contexts [
        ⟨6418, false, false, [], [11]⟩,
        ⟨90, false, false, [78183], []⟩,
        ⟨6419, false, false, [], []⟩
      ]⟩,
    ⟨[78187], [78185, 1], .source 39158⟩,
    ⟨[78185], [78185], .contexts []⟩,
    ⟨[78187, 1], [78185], .contexts [
        ⟨6421, false, false, [], [1]⟩,
        ⟨18, false, false, [78185], []⟩,
        ⟨6422, false, false, [], []⟩
      ]⟩,
    ⟨[78189], [78187, 13], .source 39159⟩,
    ⟨[78187], [78187], .contexts []⟩,
    ⟨[78189, 13], [78187], .contexts [
        ⟨6424, false, false, [], [13]⟩,
        ⟨98, false, false, [78187], []⟩,
        ⟨6425, false, false, [], []⟩
      ]⟩,
    ⟨[78191], [78189, 15], .source 39160⟩,
    ⟨[78189], [78189], .contexts []⟩,
    ⟨[78191, 15], [78189], .contexts [
        ⟨6427, false, false, [], [15]⟩,
        ⟨3, false, false, [78189], []⟩,
        ⟨6428, false, false, [], []⟩
      ]⟩,
    ⟨[78193], [78191, 1], .source 39161⟩,
    ⟨[78191], [78191], .contexts []⟩,
    ⟨[78193, 1], [78191], .contexts [
        ⟨6430, false, false, [], [1]⟩,
        ⟨18, false, false, [78191], []⟩,
        ⟨6431, false, false, [], []⟩
      ]⟩,
    ⟨[78195], [78193, 3], .source 39162⟩,
    ⟨[78193], [78193], .contexts []⟩,
    ⟨[78195, 3], [78193], .contexts [
        ⟨6433, false, false, [], [3]⟩,
        ⟨35, false, false, [78193], []⟩,
        ⟨6434, false, false, [], []⟩
      ]⟩,
    ⟨[78197], [78195, 5], .source 39163⟩,
    ⟨[78195], [78195], .contexts []⟩,
    ⟨[78197, 5], [78195], .contexts [
        ⟨6436, false, false, [], [5]⟩,
        ⟨49, false, false, [78195], []⟩,
        ⟨6437, false, false, [], []⟩
      ]⟩,
    ⟨[78199], [78197, 1], .source 39164⟩,
    ⟨[78197], [78197], .contexts []⟩,
    ⟨[78199, 1], [78197], .contexts [
        ⟨6439, false, false, [], [1]⟩,
        ⟨18, false, false, [78197], []⟩,
        ⟨6440, false, false, [], []⟩
      ]⟩,
    ⟨[78201], [78199, 9], .source 39165⟩,
    ⟨[78199], [78199], .contexts []⟩,
    ⟨[78201, 9], [78199], .contexts [
        ⟨6442, false, false, [], [9]⟩,
        ⟨76, false, false, [78199], []⟩,
        ⟨6443, false, false, [], []⟩
      ]⟩,
    ⟨[78203], [78201, 11], .source 39166⟩,
    ⟨[78201], [78201], .contexts []⟩,
    ⟨[78203, 11], [78201], .contexts [
        ⟨6445, false, false, [], [11]⟩,
        ⟨90, false, false, [78201], []⟩,
        ⟨6446, false, false, [], []⟩
      ]⟩,
    ⟨[78205], [78203, 1], .source 39167⟩,
    ⟨[78203], [78203], .contexts []⟩,
    ⟨[78205, 1], [78203], .contexts [
        ⟨6448, false, false, [], [1]⟩,
        ⟨18, false, false, [78203], []⟩,
        ⟨6449, false, false, [], []⟩
      ]⟩,
    ⟨[78207], [78205, 13], .source 39168⟩,
    ⟨[78205], [78205], .contexts []⟩,
    ⟨[78207, 13], [78205], .contexts [
        ⟨6451, false, false, [], [13]⟩,
        ⟨98, false, false, [78205], []⟩,
        ⟨6452, false, false, [], []⟩
      ]⟩,
    ⟨[78209], [78207, 15], .source 39169⟩,
    ⟨[78207], [78207], .contexts []⟩,
    ⟨[78209, 15], [78207], .contexts [
        ⟨6454, false, false, [], [15]⟩,
        ⟨3, false, false, [78207], []⟩,
        ⟨6455, false, false, [], []⟩
      ]⟩,
    ⟨[78211], [78209, 1], .source 39170⟩,
    ⟨[78209], [78209], .contexts []⟩,
    ⟨[78211, 1], [78209], .contexts [
        ⟨6457, false, false, [], [1]⟩,
        ⟨18, false, false, [78209], []⟩,
        ⟨6458, false, false, [], []⟩
      ]⟩,
    ⟨[78213], [78211, 3], .source 39171⟩,
    ⟨[78211], [78211], .contexts []⟩,
    ⟨[78213, 3], [78211], .contexts [
        ⟨6460, false, false, [], [3]⟩,
        ⟨35, false, false, [78211], []⟩,
        ⟨6461, false, false, [], []⟩
      ]⟩,
    ⟨[78215], [78213, 5], .source 39172⟩]

/-- Exact literal claimed equations and contextual derivations, block 101. -/
def y322TCContextRaw101 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78213], [78213], .contexts []⟩,
    ⟨[78215, 5], [78213], .contexts [
        ⟨6463, false, false, [], [5]⟩,
        ⟨49, false, false, [78213], []⟩,
        ⟨6464, false, false, [], []⟩
      ]⟩,
    ⟨[78217], [78215, 1], .source 39173⟩,
    ⟨[78215], [78215], .contexts []⟩,
    ⟨[78217, 1], [78215], .contexts [
        ⟨6466, false, false, [], [1]⟩,
        ⟨18, false, false, [78215], []⟩,
        ⟨6467, false, false, [], []⟩
      ]⟩,
    ⟨[78219], [78217, 9], .source 39174⟩,
    ⟨[78217], [78217], .contexts []⟩,
    ⟨[78219, 9], [78217], .contexts [
        ⟨6469, false, false, [], [9]⟩,
        ⟨76, false, false, [78217], []⟩,
        ⟨6470, false, false, [], []⟩
      ]⟩,
    ⟨[78221], [78219, 11], .source 39175⟩,
    ⟨[78219], [78219], .contexts []⟩,
    ⟨[78221, 11], [78219], .contexts [
        ⟨6472, false, false, [], [11]⟩,
        ⟨90, false, false, [78219], []⟩,
        ⟨6473, false, false, [], []⟩
      ]⟩,
    ⟨[78223], [78221, 1], .source 39176⟩,
    ⟨[78221], [78221], .contexts []⟩,
    ⟨[78223, 1], [78221], .contexts [
        ⟨6475, false, false, [], [1]⟩,
        ⟨18, false, false, [78221], []⟩,
        ⟨6476, false, false, [], []⟩
      ]⟩,
    ⟨[78225], [78223, 13], .source 39177⟩,
    ⟨[78223], [78223], .contexts []⟩,
    ⟨[78225, 13], [78223], .contexts [
        ⟨6478, false, false, [], [13]⟩,
        ⟨98, false, false, [78223], []⟩,
        ⟨6479, false, false, [], []⟩
      ]⟩,
    ⟨[78227], [78225, 15], .source 39178⟩,
    ⟨[78225], [78225], .contexts []⟩,
    ⟨[78227, 15], [78225], .contexts [
        ⟨6481, false, false, [], [15]⟩,
        ⟨3, false, false, [78225], []⟩,
        ⟨6482, false, false, [], []⟩
      ]⟩,
    ⟨[78229], [78227, 1], .source 39179⟩,
    ⟨[78227], [78227], .contexts []⟩,
    ⟨[78229, 1], [78227], .contexts [
        ⟨6484, false, false, [], [1]⟩,
        ⟨18, false, false, [78227], []⟩,
        ⟨6485, false, false, [], []⟩
      ]⟩,
    ⟨[78231], [78229, 3], .source 39180⟩,
    ⟨[78229], [78229], .contexts []⟩,
    ⟨[78231, 3], [78229], .contexts [
        ⟨6487, false, false, [], [3]⟩,
        ⟨35, false, false, [78229], []⟩,
        ⟨6488, false, false, [], []⟩
      ]⟩,
    ⟨[78233], [78231, 5], .source 39181⟩,
    ⟨[78231], [78231], .contexts []⟩,
    ⟨[78233, 5], [78231], .contexts [
        ⟨6490, false, false, [], [5]⟩,
        ⟨49, false, false, [78231], []⟩,
        ⟨6491, false, false, [], []⟩
      ]⟩,
    ⟨[78235], [78233, 1], .source 39182⟩,
    ⟨[78233, 1], [78235], .contexts [
        ⟨6493, true, false, [], []⟩
      ]⟩,
    ⟨[78233], [78233], .contexts []⟩,
    ⟨[78235, 1], [78233], .contexts [
        ⟨6494, true, false, [], [1]⟩,
        ⟨18, false, false, [78233], []⟩,
        ⟨6495, false, false, [], []⟩
      ]⟩,
    ⟨[78237], [78235, 9], .source 39183⟩,
    ⟨[78235, 9], [78237], .contexts [
        ⟨6497, true, false, [], []⟩
      ]⟩,
    ⟨[78235], [78235], .contexts []⟩,
    ⟨[78237, 9], [78235], .contexts [
        ⟨6498, true, false, [], [9]⟩,
        ⟨76, false, false, [78235], []⟩,
        ⟨6499, false, false, [], []⟩
      ]⟩,
    ⟨[78239], [78237, 11], .source 39184⟩,
    ⟨[78237, 11], [78239], .contexts [
        ⟨6501, true, false, [], []⟩
      ]⟩,
    ⟨[78237], [78237], .contexts []⟩,
    ⟨[78239, 11], [78237], .contexts [
        ⟨6502, true, false, [], [11]⟩,
        ⟨90, false, false, [78237], []⟩,
        ⟨6503, false, false, [], []⟩
      ]⟩,
    ⟨[78241], [78239, 1], .source 39185⟩,
    ⟨[78239, 1], [78241], .contexts [
        ⟨6505, true, false, [], []⟩
      ]⟩,
    ⟨[78239], [78239], .contexts []⟩,
    ⟨[78241, 1], [78239], .contexts [
        ⟨6506, true, false, [], [1]⟩,
        ⟨18, false, false, [78239], []⟩,
        ⟨6507, false, false, [], []⟩
      ]⟩,
    ⟨[78243], [78241, 13], .source 39186⟩,
    ⟨[78241, 13], [78243], .contexts [
        ⟨6509, true, false, [], []⟩
      ]⟩,
    ⟨[78241], [78241], .contexts []⟩,
    ⟨[78243, 13], [78241], .contexts [
        ⟨6510, true, false, [], [13]⟩,
        ⟨98, false, false, [78241], []⟩,
        ⟨6511, false, false, [], []⟩
      ]⟩,
    ⟨[78245], [78243, 15], .source 39187⟩,
    ⟨[78243], [78243], .contexts []⟩,
    ⟨[78245, 15], [78243], .contexts [
        ⟨6513, false, false, [], [15]⟩,
        ⟨3, false, false, [78243], []⟩,
        ⟨6514, false, false, [], []⟩
      ]⟩,
    ⟨[78247], [78245, 1], .source 39188⟩,
    ⟨[78245], [78245], .contexts []⟩,
    ⟨[78247, 1], [78245], .contexts [
        ⟨6516, false, false, [], [1]⟩,
        ⟨18, false, false, [78245], []⟩,
        ⟨6517, false, false, [], []⟩
      ]⟩,
    ⟨[78249], [78247, 3], .source 39189⟩,
    ⟨[78247], [78247], .contexts []⟩,
    ⟨[78249, 3], [78247], .contexts [
        ⟨6519, false, false, [], [3]⟩,
        ⟨35, false, false, [78247], []⟩,
        ⟨6520, false, false, [], []⟩
      ]⟩,
    ⟨[78251], [78249, 5], .source 39190⟩,
    ⟨[78249], [78249], .contexts []⟩,
    ⟨[78251, 5], [78249], .contexts [
        ⟨6522, false, false, [], [5]⟩,
        ⟨49, false, false, [78249], []⟩,
        ⟨6523, false, false, [], []⟩
      ]⟩,
    ⟨[78253], [78251, 1], .source 39191⟩,
    ⟨[78251], [78251], .contexts []⟩,
    ⟨[78253, 1], [78251], .contexts [
        ⟨6525, false, false, [], [1]⟩,
        ⟨18, false, false, [78251], []⟩,
        ⟨6526, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 102. -/
def y322TCContextRaw102 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78255], [78253, 9], .source 39192⟩,
    ⟨[78253], [78253], .contexts []⟩,
    ⟨[78255, 9], [78253], .contexts [
        ⟨6528, false, false, [], [9]⟩,
        ⟨76, false, false, [78253], []⟩,
        ⟨6529, false, false, [], []⟩
      ]⟩,
    ⟨[78257], [78255, 11], .source 39193⟩,
    ⟨[78255, 11], [78257], .contexts [
        ⟨6531, true, false, [], []⟩
      ]⟩,
    ⟨[78255], [78255], .contexts []⟩,
    ⟨[78257, 11], [78255], .contexts [
        ⟨6532, true, false, [], [11]⟩,
        ⟨90, false, false, [78255], []⟩,
        ⟨6533, false, false, [], []⟩
      ]⟩,
    ⟨[78257], [78257], .contexts []⟩,
    ⟨[78257], [78257], .contexts []⟩,
    ⟨[78253], [78253], .contexts []⟩,
    ⟨[78251], [78251], .contexts []⟩,
    ⟨[78249], [78249], .contexts []⟩,
    ⟨[78247], [78247], .contexts []⟩,
    ⟨[78245], [78245], .contexts []⟩,
    ⟨[78255, 9, 1, 5, 3, 1], [78245], .contexts [
        ⟨6530, false, false, [], [1, 5, 3, 1]⟩,
        ⟨6537, false, false, [], [1, 5, 3, 1]⟩,
        ⟨6529, false, false, [], [1, 5, 3, 1]⟩,
        ⟨6529, false, false, [], [1, 5, 3, 1]⟩,
        ⟨6527, false, false, [], [5, 3, 1]⟩,
        ⟨6538, false, false, [], [5, 3, 1]⟩,
        ⟨6526, false, false, [], [5, 3, 1]⟩,
        ⟨6526, false, false, [], [5, 3, 1]⟩,
        ⟨6524, false, false, [], [3, 1]⟩,
        ⟨6539, false, false, [], [3, 1]⟩,
        ⟨6523, false, false, [], [3, 1]⟩,
        ⟨6523, false, false, [], [3, 1]⟩,
        ⟨6521, false, false, [], [1]⟩,
        ⟨6540, false, false, [], [1]⟩,
        ⟨6520, false, false, [], [1]⟩,
        ⟨6520, false, false, [], [1]⟩,
        ⟨6518, false, false, [], []⟩,
        ⟨6541, false, false, [], []⟩,
        ⟨6517, false, false, [], []⟩,
        ⟨6517, false, false, [], []⟩
      ]⟩,
    ⟨[78243], [78243], .contexts []⟩,
    ⟨[78243, 13], [78241], .contexts [
        ⟨6512, false, false, [], []⟩
      ]⟩,
    ⟨[78241], [78241], .contexts []⟩,
    ⟨[78241, 1], [78239], .contexts [
        ⟨6508, false, false, [], []⟩
      ]⟩,
    ⟨[78239], [78239], .contexts []⟩,
    ⟨[78239, 11], [78237], .contexts [
        ⟨6504, false, false, [], []⟩
      ]⟩,
    ⟨[78237], [78237], .contexts []⟩,
    ⟨[78237, 9], [78235], .contexts [
        ⟨6500, false, false, [], []⟩
      ]⟩,
    ⟨[78235], [78235], .contexts []⟩,
    ⟨[78255, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9], [78235], .contexts [
        ⟨6542, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨6515, false, false, [], [13, 1, 11, 9]⟩,
        ⟨6543, false, false, [], [13, 1, 11, 9]⟩,
        ⟨6514, false, false, [], [13, 1, 11, 9]⟩,
        ⟨6514, false, false, [], [13, 1, 11, 9]⟩,
        ⟨6544, false, false, [], [1, 11, 9]⟩,
        ⟨6545, false, false, [], [1, 11, 9]⟩,
        ⟨6511, false, false, [], [1, 11, 9]⟩,
        ⟨6511, false, false, [], [1, 11, 9]⟩,
        ⟨6546, false, false, [], [11, 9]⟩,
        ⟨6547, false, false, [], [11, 9]⟩,
        ⟨6507, false, false, [], [11, 9]⟩,
        ⟨6507, false, false, [], [11, 9]⟩,
        ⟨6548, false, false, [], [9]⟩,
        ⟨6549, false, false, [], [9]⟩,
        ⟨6503, false, false, [], [9]⟩,
        ⟨6503, false, false, [], [9]⟩,
        ⟨6550, false, false, [], []⟩,
        ⟨6551, false, false, [], []⟩,
        ⟨6499, false, false, [], []⟩,
        ⟨6499, false, false, [], []⟩
      ]⟩,
    ⟨[78235, 1], [78233], .contexts [
        ⟨6496, false, false, [], []⟩
      ]⟩,
    ⟨[78233], [78233], .contexts []⟩,
    ⟨[78233, 5], [78231], .contexts [
        ⟨6492, false, false, [], []⟩
      ]⟩,
    ⟨[78231], [78231], .contexts []⟩,
    ⟨[78231, 3], [78229], .contexts [
        ⟨6489, false, false, [], []⟩
      ]⟩,
    ⟨[78229], [78229], .contexts []⟩,
    ⟨[78229, 1], [78227], .contexts [
        ⟨6486, false, false, [], []⟩
      ]⟩,
    ⟨[78227], [78227], .contexts []⟩,
    ⟨[
      78255, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15
    ], [78225], .contexts [
        ⟨6552, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨6553, false, false, [], [5, 3, 1, 15]⟩,
        ⟨6554, false, false, [], [5, 3, 1, 15]⟩,
        ⟨6495, false, false, [], [5, 3, 1, 15]⟩,
        ⟨6495, false, false, [], [5, 3, 1, 15]⟩,
        ⟨6555, false, false, [], [3, 1, 15]⟩,
        ⟨6556, false, false, [], [3, 1, 15]⟩,
        ⟨6491, false, false, [], [3, 1, 15]⟩,
        ⟨6491, false, false, [], [3, 1, 15]⟩,
        ⟨6557, false, false, [], [1, 15]⟩,
        ⟨6558, false, false, [], [1, 15]⟩,
        ⟨6488, false, false, [], [1, 15]⟩,
        ⟨6488, false, false, [], [1, 15]⟩,
        ⟨6559, false, false, [], [15]⟩,
        ⟨6560, false, false, [], [15]⟩,
        ⟨6485, false, false, [], [15]⟩,
        ⟨6485, false, false, [], [15]⟩,
        ⟨6483, false, false, [], []⟩,
        ⟨6482, false, false, [], []⟩,
        ⟨6482, false, false, [], []⟩
      ]⟩,
    ⟨[78225, 13], [78223], .contexts [
        ⟨6480, false, false, [], []⟩
      ]⟩,
    ⟨[78223], [78223], .contexts []⟩,
    ⟨[78215], [78215], .contexts []⟩,
    ⟨[
      78255, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [78215], .contexts [
        ⟨6561, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨6562, false, false, [], [1, 11, 9, 1]⟩,
        ⟨6563, false, false, [], [1, 11, 9, 1]⟩,
        ⟨6479, false, false, [], [1, 11, 9, 1]⟩,
        ⟨6479, false, false, [], [1, 11, 9, 1]⟩,
        ⟨6477, false, false, [], [11, 9, 1]⟩,
        ⟨6476, false, false, [], [11, 9, 1]⟩,
        ⟨6476, false, false, [], [11, 9, 1]⟩,
        ⟨6474, false, false, [], [9, 1]⟩,
        ⟨6473, false, false, [], [9, 1]⟩,
        ⟨6473, false, false, [], [9, 1]⟩,
        ⟨6471, false, false, [], [1]⟩,
        ⟨6470, false, false, [], [1]⟩,
        ⟨6470, false, false, [], [1]⟩,
        ⟨6468, false, false, [], []⟩,
        ⟨6564, false, false, [], []⟩,
        ⟨6467, false, false, [], []⟩,
        ⟨6467, false, false, [], []⟩
      ]⟩,
    ⟨[78213], [78213], .contexts []⟩,
    ⟨[78211], [78211], .contexts []⟩,
    ⟨[78209], [78209], .contexts []⟩,
    ⟨[78207], [78207], .contexts []⟩,
    ⟨[78205], [78205], .contexts []⟩,
    ⟨[
      78255, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13
    ], [78205], .contexts [
        ⟨6565, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨6465, false, false, [], [3, 1, 15, 13]⟩,
        ⟨6566, false, false, [], [3, 1, 15, 13]⟩,
        ⟨6464, false, false, [], [3, 1, 15, 13]⟩,
        ⟨6464, false, false, [], [3, 1, 15, 13]⟩,
        ⟨6462, false, false, [], [1, 15, 13]⟩,
        ⟨6567, false, false, [], [1, 15, 13]⟩,
        ⟨6461, false, false, [], [1, 15, 13]⟩,
        ⟨6461, false, false, [], [1, 15, 13]⟩,
        ⟨6459, false, false, [], [15, 13]⟩,
        ⟨6568, false, false, [], [15, 13]⟩,
        ⟨6458, false, false, [], [15, 13]⟩,
        ⟨6458, false, false, [], [15, 13]⟩,
        ⟨6456, false, false, [], [13]⟩,
        ⟨6569, false, false, [], [13]⟩,
        ⟨6455, false, false, [], [13]⟩,
        ⟨6455, false, false, [], [13]⟩,
        ⟨6453, false, false, [], []⟩,
        ⟨6570, false, false, [], []⟩,
        ⟨6452, false, false, [], []⟩,
        ⟨6452, false, false, [], []⟩
      ]⟩,
    ⟨[78203], [78203], .contexts []⟩,
    ⟨[78201], [78201], .contexts []⟩,
    ⟨[78199], [78199], .contexts []⟩,
    ⟨[78197], [78197], .contexts []⟩,
    ⟨[78195], [78195], .contexts []⟩,
    ⟨[
      78255, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5
    ], [78195], .contexts [
        ⟨6571, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨6450, false, false, [], [11, 9, 1, 5]⟩,
        ⟨6572, false, false, [], [11, 9, 1, 5]⟩,
        ⟨6449, false, false, [], [11, 9, 1, 5]⟩,
        ⟨6449, false, false, [], [11, 9, 1, 5]⟩,
        ⟨6447, false, false, [], [9, 1, 5]⟩,
        ⟨6573, false, false, [], [9, 1, 5]⟩,
        ⟨6446, false, false, [], [9, 1, 5]⟩,
        ⟨6446, false, false, [], [9, 1, 5]⟩,
        ⟨6444, false, false, [], [1, 5]⟩,
        ⟨6574, false, false, [], [1, 5]⟩,
        ⟨6443, false, false, [], [1, 5]⟩,
        ⟨6443, false, false, [], [1, 5]⟩,
        ⟨6441, false, false, [], [5]⟩,
        ⟨6575, false, false, [], [5]⟩,
        ⟨6440, false, false, [], [5]⟩,
        ⟨6440, false, false, [], [5]⟩,
        ⟨6438, false, false, [], []⟩,
        ⟨6576, false, false, [], []⟩,
        ⟨6437, false, false, [], []⟩,
        ⟨6437, false, false, [], []⟩
      ]⟩,
    ⟨[78193], [78193], .contexts []⟩,
    ⟨[78191], [78191], .contexts []⟩,
    ⟨[78189], [78189], .contexts []⟩,
    ⟨[78187], [78187], .contexts []⟩,
    ⟨[78185], [78185], .contexts []⟩,
    ⟨[
      78255, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [78185], .contexts [
        ⟨6577, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨6435, false, false, [], [1, 15, 13, 1]⟩,
        ⟨6578, false, false, [], [1, 15, 13, 1]⟩,
        ⟨6434, false, false, [], [1, 15, 13, 1]⟩,
        ⟨6434, false, false, [], [1, 15, 13, 1]⟩,
        ⟨6432, false, false, [], [15, 13, 1]⟩,
        ⟨6579, false, false, [], [15, 13, 1]⟩,
        ⟨6431, false, false, [], [15, 13, 1]⟩,
        ⟨6431, false, false, [], [15, 13, 1]⟩,
        ⟨6429, false, false, [], [13, 1]⟩,
        ⟨6580, false, false, [], [13, 1]⟩,
        ⟨6428, false, false, [], [13, 1]⟩,
        ⟨6428, false, false, [], [13, 1]⟩,
        ⟨6426, false, false, [], [1]⟩,
        ⟨6581, false, false, [], [1]⟩,
        ⟨6425, false, false, [], [1]⟩,
        ⟨6425, false, false, [], [1]⟩,
        ⟨6423, false, false, [], []⟩,
        ⟨6582, false, false, [], []⟩,
        ⟨6422, false, false, [], []⟩,
        ⟨6422, false, false, [], []⟩
      ]⟩,
    ⟨[78183], [78183], .contexts []⟩,
    ⟨[78181], [78181], .contexts []⟩,
    ⟨[78179], [78179], .contexts []⟩,
    ⟨[78177], [78177], .contexts []⟩,
    ⟨[78175], [78175], .contexts []⟩,
    ⟨[
      78255, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3
    ], [78175], .contexts [
        ⟨6583, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨6420, false, false, [], [9, 1, 5, 3]⟩,
        ⟨6584, false, false, [], [9, 1, 5, 3]⟩,
        ⟨6419, false, false, [], [9, 1, 5, 3]⟩,
        ⟨6419, false, false, [], [9, 1, 5, 3]⟩,
        ⟨6417, false, false, [], [1, 5, 3]⟩,
        ⟨6585, false, false, [], [1, 5, 3]⟩,
        ⟨6416, false, false, [], [1, 5, 3]⟩,
        ⟨6416, false, false, [], [1, 5, 3]⟩,
        ⟨6414, false, false, [], [5, 3]⟩,
        ⟨6586, false, false, [], [5, 3]⟩,
        ⟨6413, false, false, [], [5, 3]⟩,
        ⟨6413, false, false, [], [5, 3]⟩,
        ⟨6411, false, false, [], [3]⟩,
        ⟨6587, false, false, [], [3]⟩,
        ⟨6410, false, false, [], [3]⟩,
        ⟨6410, false, false, [], [3]⟩,
        ⟨6408, false, false, [], []⟩,
        ⟨6588, false, false, [], []⟩,
        ⟨6407, false, false, [], []⟩,
        ⟨6407, false, false, [], []⟩
      ]⟩,
    ⟨[78173], [78173], .contexts []⟩,
    ⟨[78171], [78171], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 103. -/
def y322TCContextRaw103 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78169], [78169], .contexts []⟩,
    ⟨[78167], [78167], .contexts []⟩,
    ⟨[78165], [78165], .contexts []⟩,
    ⟨[
      78255, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [78165], .contexts [
        ⟨6589, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨6405, false, false, [], [15, 13, 1, 11]⟩,
        ⟨6590, false, false, [], [15, 13, 1, 11]⟩,
        ⟨6404, false, false, [], [15, 13, 1, 11]⟩,
        ⟨6404, false, false, [], [15, 13, 1, 11]⟩,
        ⟨6402, false, false, [], [13, 1, 11]⟩,
        ⟨6591, false, false, [], [13, 1, 11]⟩,
        ⟨6401, false, false, [], [13, 1, 11]⟩,
        ⟨6401, false, false, [], [13, 1, 11]⟩,
        ⟨6399, false, false, [], [1, 11]⟩,
        ⟨6592, false, false, [], [1, 11]⟩,
        ⟨6398, false, false, [], [1, 11]⟩,
        ⟨6398, false, false, [], [1, 11]⟩,
        ⟨6396, false, false, [], [11]⟩,
        ⟨6593, false, false, [], [11]⟩,
        ⟨6395, false, false, [], [11]⟩,
        ⟨6395, false, false, [], [11]⟩,
        ⟨6393, false, false, [], []⟩,
        ⟨6594, false, false, [], []⟩,
        ⟨6392, false, false, [], []⟩,
        ⟨6392, false, false, [], []⟩
      ]⟩,
    ⟨[78163], [78163], .contexts []⟩,
    ⟨[78161], [78161], .contexts []⟩,
    ⟨[78159], [78159], .contexts []⟩,
    ⟨[78155], [78155], .contexts []⟩,
    ⟨[
      78255, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1
    ], [78155], .contexts [
        ⟨6595, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨6390, false, false, [], [1, 5, 3, 1]⟩,
        ⟨6596, false, false, [], [1, 5, 3, 1]⟩,
        ⟨6389, false, false, [], [1, 5, 3, 1]⟩,
        ⟨6389, false, false, [], [1, 5, 3, 1]⟩,
        ⟨6387, false, false, [], [5, 3, 1]⟩,
        ⟨6597, false, false, [], [5, 3, 1]⟩,
        ⟨6386, false, false, [], [5, 3, 1]⟩,
        ⟨6386, false, false, [], [5, 3, 1]⟩,
        ⟨6384, false, false, [], [3, 1]⟩,
        ⟨6598, false, false, [], [3, 1]⟩,
        ⟨6383, false, false, [], [3, 1]⟩,
        ⟨6383, false, false, [], [3, 1]⟩,
        ⟨6381, false, false, [], [1]⟩,
        ⟨6380, false, false, [], [1]⟩,
        ⟨6380, false, false, [], [1]⟩,
        ⟨6377, true, false, [], [1]⟩,
        ⟨18, false, false, [78155], []⟩,
        ⟨6378, false, false, [], []⟩,
        ⟨6599, false, false, [], []⟩,
        ⟨6378, false, false, [], []⟩,
        ⟨6378, false, false, [], []⟩
      ]⟩,
    ⟨[78153], [78153], .contexts []⟩,
    ⟨[78151], [78151], .contexts []⟩,
    ⟨[78149], [78149], .contexts []⟩,
    ⟨[78147], [78147], .contexts []⟩,
    ⟨[78145], [78145], .contexts []⟩,
    ⟨[
      78255, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9
    ], [78145], .contexts [
        ⟨6600, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨6375, false, false, [], [13, 1, 11, 9]⟩,
        ⟨6601, false, false, [], [13, 1, 11, 9]⟩,
        ⟨6374, false, false, [], [13, 1, 11, 9]⟩,
        ⟨6374, false, false, [], [13, 1, 11, 9]⟩,
        ⟨6371, false, false, [], [1, 11, 9]⟩,
        ⟨6602, false, false, [], [1, 11, 9]⟩,
        ⟨6370, false, false, [], [1, 11, 9]⟩,
        ⟨6370, false, false, [], [1, 11, 9]⟩,
        ⟨6367, false, false, [], [11, 9]⟩,
        ⟨6603, false, false, [], [11, 9]⟩,
        ⟨6366, false, false, [], [11, 9]⟩,
        ⟨6366, false, false, [], [11, 9]⟩,
        ⟨6363, false, false, [], [9]⟩,
        ⟨6604, false, false, [], [9]⟩,
        ⟨6362, false, false, [], [9]⟩,
        ⟨6362, false, false, [], [9]⟩,
        ⟨6359, false, false, [], []⟩,
        ⟨6605, false, false, [], []⟩,
        ⟨6358, false, false, [], []⟩,
        ⟨6358, false, false, [], []⟩
      ]⟩,
    ⟨[
      78255, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [145, 78139], .contexts [
        ⟨6606, false, false, [], [1, 5, 3, 1]⟩,
        ⟨6355, true, false, [], [1, 5, 3, 1]⟩,
        ⟨18, false, false, [78143], [5, 3, 1]⟩,
        ⟨6353, false, false, [], [5, 3, 1]⟩,
        ⟨6352, false, false, [], [5, 3, 1]⟩,
        ⟨6353, false, false, [], [5, 3, 1]⟩,
        ⟨6353, false, false, [], [5, 3, 1]⟩,
        ⟨6351, true, false, [], [5, 3, 1]⟩,
        ⟨49, false, false, [78141], [3, 1]⟩,
        ⟨6349, false, false, [], [3, 1]⟩,
        ⟨6349, false, false, [], [3, 1]⟩,
        ⟨6349, false, false, [], [3, 1]⟩,
        ⟨6348, true, false, [], [3, 1]⟩,
        ⟨35, false, false, [78139], [1]⟩,
        ⟨6336, false, false, [], [1]⟩,
        ⟨6335, false, false, [], [1]⟩,
        ⟨6336, false, false, [], [1]⟩,
        ⟨6336, false, false, [], [1]⟩,
        ⟨6342, false, false, [], []⟩,
        ⟨6338, false, false, [], []⟩,
        ⟨6340, false, false, [], []⟩,
        ⟨6340, false, false, [], []⟩
      ]⟩,
    ⟨[
      78255, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9
    ], [145, 77733], .contexts [
        ⟨6607, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨6334, false, false, [145], [13, 1, 11, 9]⟩,
        ⟨6327, false, false, [], [13, 1, 11, 9]⟩,
        ⟨6328, false, false, [], [13, 1, 11, 9]⟩,
        ⟨6329, false, false, [], [13, 1, 11, 9]⟩,
        ⟨6320, false, false, [145], [1, 11, 9]⟩,
        ⟨6324, false, false, [], [1, 11, 9]⟩,
        ⟨6325, false, false, [], [1, 11, 9]⟩,
        ⟨6326, false, false, [], [1, 11, 9]⟩,
        ⟨6313, false, false, [145], [11, 9]⟩,
        ⟨6304, false, false, [], [11, 9]⟩,
        ⟨6305, false, false, [], [11, 9]⟩,
        ⟨6306, false, false, [], [11, 9]⟩,
        ⟨6298, true, false, [145], [11, 9]⟩,
        ⟨90, false, false, [145, 78131], [9]⟩,
        ⟨6286, false, false, [145], [9]⟩,
        ⟨6288, false, false, [], [9]⟩,
        ⟨6289, false, false, [], [9]⟩,
        ⟨6290, false, false, [], [9]⟩,
        ⟨6284, true, false, [145], [9]⟩,
        ⟨76, false, false, [145, 77733], []⟩,
        ⟨4337, false, false, [145], []⟩,
        ⟨4344, false, false, [], []⟩,
        ⟨4345, false, false, [], []⟩,
        ⟨4346, false, false, [], []⟩
      ]⟩,
    ⟨[1395], [145, 293], .source 762⟩,
    ⟨[1397], [1395, 329], .source 763⟩,
    ⟨[
      78255, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [1397, 77369], .contexts [
        ⟨6608, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨4353, false, false, [145], [5, 3, 1, 15]⟩,
        ⟨6282, false, false, [145], [3, 1, 15]⟩,
        ⟨6609, true, false, [], [78129, 3, 1, 15]⟩,
        ⟨6269, false, false, [1395], [1, 15]⟩,
        ⟨2092, false, false, [1395], [15]⟩,
        ⟨2089, false, false, [1395], []⟩,
        ⟨6610, true, false, [], [77369]⟩
      ]⟩,
    ⟨[1399], [1397, 243], .source 764⟩,
    ⟨[1401], [1399, 275], .source 765⟩,
    ⟨[
      78255, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1
    ], [1401, 77253], .contexts [
        ⟨6611, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨2083, false, false, [1397], [1, 11, 9, 1]⟩,
        ⟨1192, false, false, [1397], [11, 9, 1]⟩,
        ⟨1725, false, false, [1397], [9, 1]⟩,
        ⟨6612, true, false, [], [77251, 9, 1]⟩,
        ⟨1195, false, false, [1399], [1]⟩,
        ⟨1720, false, false, [1399], []⟩,
        ⟨6613, true, false, [], [77253]⟩
      ]⟩,
    ⟨[1403], [1401, 723], .source 766⟩,
    ⟨[1405], [1403, 1281], .source 767⟩,
    ⟨[1407], [1405, 539], .source 768⟩,
    ⟨[1409], [1407, 269], .source 769⟩,
    ⟨[
      78255, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13
    ], [1409, 77341], .contexts [
        ⟨6614, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨3414, false, false, [1401], [3, 1, 15, 13]⟩,
        ⟨6615, true, false, [], [77331, 3, 1, 15, 13]⟩,
        ⟨5680, false, false, [1403], [1, 15, 13]⟩,
        ⟨6616, true, false, [], [77993, 1, 15, 13]⟩,
        ⟨5658, false, false, [1405], [15, 13]⟩,
        ⟨2791, false, false, [1405], [13]⟩,
        ⟨6617, true, false, [], [77341, 13]⟩,
        ⟨1654, false, false, [1407], []⟩,
        ⟨6618, true, false, [], [77341]⟩
      ]⟩,
    ⟨[1411], [1409, 261], .source 770⟩,
    ⟨[1413], [1411, 267], .source 771⟩,
    ⟨[1415], [1413, 1059], .source 772⟩,
    ⟨[1417], [1415, 261], .source 773⟩,
    ⟨[
      78255, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5
    ], [1417, 77863], .contexts [
        ⟨6619, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨1330, false, false, [1409], [11, 9, 1, 5]⟩,
        ⟨2626, false, false, [1409], [11, 9, 1, 5]⟩,
        ⟨6620, true, false, [], [77337, 11, 9, 1, 5]⟩,
        ⟨4858, false, false, [1411], [9, 1, 5]⟩,
        ⟨6621, true, false, [], [77865, 9, 1, 5]⟩,
        ⟨4874, false, false, [1413], [1, 5]⟩,
        ⟨6622, true, false, [], [77865, 1, 5]⟩,
        ⟨4847, false, false, [1415], [5]⟩,
        ⟨4833, false, false, [1415], []⟩,
        ⟨6623, true, false, [], [77863]⟩
      ]⟩,
    ⟨[1419], [1417, 491], .source 774⟩,
    ⟨[1421], [1419, 537], .source 775⟩,
    ⟨[1421, 77131], [1421, 77131], .contexts []⟩,
    ⟨[1421, 77131], [1421, 77131], .contexts []⟩,
    ⟨[11, 1], [
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12
    ], .contexts [
        ⟨764, false, false, [8, 0, 4, 2, 0], [
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12
        ]⟩
      ]⟩,
    ⟨[
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14
    ], [
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 14
    ], .contexts [
        ⟨787, false, false, [], [
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14
        ]⟩,
        ⟨50, false, false, [9, 1], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨36, false, false, [9, 1, 5], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨19, false, false, [9, 1, 5, 3], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨20, false, false, [9, 1, 5, 3, 1], [12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨108, false, false, [9, 1, 5, 3, 1, 15], [0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨19, false, false, [9, 1, 5, 3, 1, 15, 13], [10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨91, false, false, [9, 1, 5, 3, 1, 15, 13, 1], [8, 0, 4, 2, 0, 14]⟩,
        ⟨77, false, false, [9, 1, 5, 3, 1, 15, 13, 1, 11], [0, 4, 2, 0, 14]⟩,
        ⟨19, false, false, [9, 1, 5, 3, 1, 15, 13, 1, 11, 9], [4, 2, 0, 14]⟩,
        ⟨50, false, false, [9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1], [2, 0, 14]⟩,
        ⟨36, false, false, [9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5], [0, 14]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3
        ], [14]⟩
      ]⟩,
    ⟨[
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10
    ], [
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 10
    ], .contexts [
        ⟨6630, false, false, [], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨20, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨108, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨91, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨77, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨50, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10]⟩,
        ⟨36, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10]⟩,
        ⟨20, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10]⟩,
        ⟨108, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13
        ], [10]⟩
      ]⟩,
    ⟨[
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4
    ], [
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 4
    ], .contexts [
        ⟨6631, false, false, [], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨91, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨77, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨50, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨36, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨20, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4]⟩,
        ⟨108, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4]⟩,
        ⟨91, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4]⟩,
        ⟨77, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9
        ], [4]⟩
      ]⟩,
    ⟨[
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14
    ], [
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 14
    ], .contexts [
        ⟨6632, false, false, [], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨50, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨36, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨20, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨108, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨91, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14]⟩,
        ⟨77, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14]⟩,
        ⟨50, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14]⟩,
        ⟨36, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3
        ], [14]⟩
      ]⟩,
    ⟨[
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10
    ], [
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 10
    ], .contexts [
        ⟨6633, false, false, [], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨20, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨108, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨91, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨77, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨50, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10]⟩,
        ⟨36, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10]⟩,
        ⟨20, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10]⟩,
        ⟨108, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13
        ], [10]⟩
      ]⟩,
    ⟨[
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4
    ], [
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 4
    ], .contexts [
        ⟨6634, false, false, [], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨91, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨77, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨50, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨36, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨20, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4]⟩,
        ⟨108, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4]⟩,
        ⟨91, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4]⟩,
        ⟨77, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9
        ], [4]⟩
      ]⟩,
    ⟨[
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14
    ], [
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 14
    ], .contexts [
        ⟨6635, false, false, [], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨50, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨36, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨20, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨108, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨91, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14]⟩,
        ⟨77, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14]⟩,
        ⟨50, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14]⟩,
        ⟨36, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14]⟩,
        ⟨19, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3
        ], [14]⟩
      ]⟩,
    ⟨[
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12
    ], [
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13
    ], .contexts [
        ⟨6636, false, false, [], [12]⟩,
        ⟨20, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1
        ], [12]⟩,
        ⟨108, false, false, [
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15
        ], []⟩
      ]⟩,
    ⟨[78257, 1], [78257, 1], .contexts []⟩,
    ⟨[78257, 1], [1421, 77131], .contexts [
        ⟨6638, false, false, [], []⟩,
        ⟨6536, true, false, [], [1]⟩,
        ⟨6536, true, false, [], [1]⟩,
        ⟨6535, true, false, [], [1]⟩,
        ⟨6532, true, false, [], [1]⟩,
        ⟨6629, false, false, [78255], []⟩,
        ⟨6637, false, false, [78255], []⟩,
        ⟨6624, false, false, [], [3, 1, 15, 13]⟩,
        ⟨4829, false, false, [1417], [1, 15, 13]⟩,
        ⟨6625, true, false, [], [77863, 1, 15, 13]⟩,
        ⟨4846, false, false, [1419], [15, 13]⟩,
        ⟨4862, false, false, [1419], [13]⟩,
        ⟨6626, true, false, [], [77129, 13]⟩,
        ⟨441, false, false, [1421], []⟩,
        ⟨6627, false, false, [], []⟩,
        ⟨6628, false, false, [], []⟩,
        ⟨2001, false, false, [1421], []⟩
      ]⟩,
    ⟨[1421], [1421], .contexts []⟩,
    ⟨[1421], [1421], .contexts []⟩,
    ⟨[1421], [1421], .contexts [
        ⟨24, false, false, [], [1421]⟩,
        ⟨6640, false, false, [], []⟩,
        ⟨6641, false, false, [], []⟩
      ]⟩,
    ⟨[78257, 1], [1421, 77131], .contexts [
        ⟨6639, false, false, [], []⟩,
        ⟨6642, true, false, [], [77131]⟩
      ]⟩,
    ⟨[1423], [1420], .source 776⟩,
    ⟨[77131, 1], [1423, 78257], .contexts [
        ⟨6643, true, false, [1420], [1]⟩,
        ⟨18, false, false, [1420, 78257], []⟩,
        ⟨6644, true, false, [], [78257]⟩
      ]⟩,
    ⟨[78257, 11], [78255], .contexts [
        ⟨6534, false, false, [], []⟩
      ]⟩,
    ⟨[78257, 1], [1421, 77131], .contexts [
        ⟨6638, false, false, [], []⟩,
        ⟨6643, false, false, [], []⟩,
        ⟨6627, false, false, [], []⟩,
        ⟨6628, false, false, [], []⟩,
        ⟨6628, false, false, [], []⟩
      ]⟩,
    ⟨[1425], [1421, 693], .source 777⟩,
    ⟨[1427], [1424], .source 778⟩,
    ⟨[1429], [715, 1427], .source 779⟩,
    ⟨[1431], [1428], .source 780⟩,
    ⟨[78255], [1431, 77587], .contexts [
        ⟨6650, false, false, [1428], [78255]⟩,
        ⟨3387, false, false, [1428], [1427, 78255]⟩,
        ⟨6649, false, false, [1428, 696], [78255]⟩,
        ⟨18, true, false, [1428, 696, 1424, 78255], []⟩,
        ⟨6533, true, false, [1428, 696, 1424], [1, 1]⟩,
        ⟨6533, true, false, [1428, 696, 1424], [1, 1]⟩,
        ⟨6646, true, false, [1428, 696, 1424], [1, 1]⟩,
        ⟨992, false, false, [1428, 696, 1424, 78257], [1]⟩,
        ⟨993, false, false, [1428, 696, 1424, 78257], [1]⟩,
        ⟨6647, false, false, [1428, 696, 1424], [11, 1]⟩,
        ⟨5688, false, false, [1428, 696, 1424, 1421], [1]⟩,
        ⟨6648, true, false, [1428, 696, 1424], [77591, 1]⟩,
        ⟨3356, false, false, [1428, 696], [1]⟩,
        ⟨24, true, false, [1428, 696, 1424], [1425, 77591, 1]⟩,
        ⟨3466, false, false, [1428, 696], []⟩,
        ⟨6651, true, false, [], [77587]⟩
      ]⟩,
    ⟨[1430], [1430], .contexts []⟩,
    ⟨[77587, 11], [1429, 78257], .contexts [
        ⟨6652, true, false, [1430], [11]⟩,
        ⟨6532, false, false, [1430], []⟩,
        ⟨6535, false, false, [1430], []⟩,
        ⟨6653, true, false, [], [78257]⟩,
        ⟨6653, true, false, [], [78257]⟩,
        ⟨6651, false, true, [], [78257]⟩
      ]⟩,
    ⟨[1431, 77587], [1431, 77587], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 104. -/
def y322TCContextRaw104 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78255], [1431, 77587], .contexts [
        ⟨6652, false, false, [], []⟩,
        ⟨6655, false, false, [], []⟩
      ]⟩,
    ⟨[1433], [1431, 713], .source 781⟩,
    ⟨[1435], [1432], .source 782⟩,
    ⟨[1437], [1433, 715], .source 783⟩,
    ⟨[1439], [1436], .source 784⟩,
    ⟨[77591], [1439, 78251], .contexts [
        ⟨6659, false, false, [1436], [77591]⟩,
        ⟨3389, true, false, [1436, 1433], []⟩,
        ⟨6658, true, true, [1436], [77587, 1]⟩,
        ⟨6657, false, false, [1436, 1434, 1432], [77587, 1]⟩,
        ⟨3383, true, false, [1436, 1434, 1432, 1431], [1]⟩,
        ⟨6656, true, false, [1436, 1434, 1432], [9, 1]⟩,
        ⟨6530, false, false, [1436, 1434, 1432], [1]⟩,
        ⟨6537, false, false, [1436, 1434, 1432], [1]⟩,
        ⟨24, true, false, [1436, 1434, 1432], [78253, 1]⟩,
        ⟨6658, true, false, [1436, 1434], [78253, 1]⟩,
        ⟨6527, false, false, [1436], []⟩,
        ⟨6538, false, false, [1436], []⟩,
        ⟨24, true, false, [1436], [78251]⟩,
        ⟨6660, true, false, [], [78251]⟩
      ]⟩,
    ⟨[1441], [1437, 697], .source 785⟩,
    ⟨[1443], [1440], .source 786⟩,
    ⟨[78249, 3], [1441, 739, 77329], .contexts [
        ⟨6663, false, false, [1442], [78249, 3]⟩,
        ⟨24, false, false, [1442, 1440], [78249, 3]⟩,
        ⟨6539, true, false, [1442, 1440], [3]⟩,
        ⟨6524, true, false, [1442, 1440], [3]⟩,
        ⟨6661, true, false, [1442, 1440, 1438], [5, 3]⟩,
        ⟨6660, false, true, [1442, 1440], [77591, 5, 3]⟩,
        ⟨3360, false, false, [1442, 1440, 1437], [3]⟩,
        ⟨6662, true, false, [1442, 1440], [77591, 3]⟩,
        ⟨6663, false, true, [], [77591, 3]⟩,
        ⟨3444, false, false, [1441], []⟩
      ]⟩,
    ⟨[1445], [1441, 739], .source 787⟩,
    ⟨[1447], [1444], .source 788⟩,
    ⟨[1447], [1444], .contexts [
        ⟨6666, false, false, [], []⟩
      ]⟩,
    ⟨[1447], [1444], .contexts [
        ⟨6667, false, false, [], []⟩,
        ⟨24, false, false, [1444], []⟩
      ]⟩,
    ⟨[1445], [1446], .contexts [
        ⟨6666, true, true, [], []⟩
      ]⟩,
    ⟨[78245, 15], [1445, 77327, 15], .contexts [
        ⟨6668, false, false, [1446], [78245, 15]⟩,
        ⟨6541, true, false, [1446, 1444], [15]⟩,
        ⟨6518, true, false, [1446, 1444], [15]⟩,
        ⟨6668, false, false, [1446, 1444, 1446], [78247, 1, 15]⟩,
        ⟨6540, true, false, [1446, 1444, 1446, 1444], [1, 15]⟩,
        ⟨6521, true, false, [1446, 1444, 1446, 1444], [1, 15]⟩,
        ⟨6664, false, false, [1446, 1444, 1446, 1444], [1, 15]⟩,
        ⟨6665, true, false, [1446, 1444, 1446, 1444], [77329, 1, 15]⟩,
        ⟨6669, true, false, [1446, 1444], [77329, 1, 15]⟩,
        ⟨1309, false, false, [1446], [15]⟩,
        ⟨6669, true, false, [], [77327, 15]⟩
      ]⟩,
    ⟨[1444], [1444], .contexts []⟩,
    ⟨[77327, 15], [1447, 78243], .contexts [
        ⟨6670, true, false, [1444], []⟩,
        ⟨6515, false, false, [1444], []⟩,
        ⟨6543, false, false, [1444], []⟩,
        ⟨6671, true, false, [], [78243]⟩,
        ⟨6671, true, false, [], [78243]⟩,
        ⟨6667, true, false, [], [78243]⟩
      ]⟩,
    ⟨[1449], [1431, 697], .source 789⟩,
    ⟨[1451], [1449, 1429], .source 790⟩,
    ⟨[78257], [78257], .contexts []⟩,
    ⟨[78257, 5], [78257, 5], .contexts []⟩,
    ⟨[78257], [78257], .contexts []⟩,
    ⟨[1453], [1450], .source 791⟩,
    ⟨[1450], [1450], .contexts []⟩,
    ⟨[77135, 15], [77135, 15], .contexts []⟩,
    ⟨[1420], [1420], .contexts []⟩,
    ⟨[77135, 15], [1423, 78257], .contexts [
        ⟨6680, false, false, [], []⟩,
        ⟨448, true, false, [], [15]⟩,
        ⟨445, true, false, [], [1, 15]⟩,
        ⟨6647, true, false, [1420], [15, 1, 15]⟩,
        ⟨3731, false, false, [1420, 78257], []⟩,
        ⟨6675, false, false, [1420], []⟩,
        ⟨6677, false, false, [1420], []⟩,
        ⟨6681, true, false, [], [78257]⟩,
        ⟨6681, true, false, [], [78257]⟩,
        ⟨6644, true, false, [], [78257]⟩
      ]⟩,
    ⟨[1455], [499, 1447], .source 792⟩,
    ⟨[1447, 78243], [1447, 78243], .contexts []⟩,
    ⟨[77327, 15], [1447, 78243], .contexts [
        ⟨6672, false, false, [], []⟩,
        ⟨6684, false, false, [], []⟩,
        ⟨6684, false, false, [], []⟩
      ]⟩,
    ⟨[78241, 15], [78241, 15], .contexts []⟩,
    ⟨[78241], [78241], .contexts []⟩,
    ⟨[1457], [1454], .source 793⟩,
    ⟨[1459], [1457, 1447], .source 794⟩,
    ⟨[78241, 15], [1459, 78241], .contexts [
        ⟨6686, false, false, [], []⟩,
        ⟨6512, true, false, [], [15]⟩,
        ⟨6683, false, false, [1454], [78243, 13, 15]⟩,
        ⟨6672, true, false, [1454, 499], [13, 15]⟩,
        ⟨2653, true, false, [1454], [15, 13, 15]⟩,
        ⟨3449, false, false, [1454, 77327], []⟩,
        ⟨149, false, false, [1454, 77327], []⟩,
        ⟨6685, false, false, [1454], [13]⟩,
        ⟨6512, false, false, [1454, 1447], []⟩,
        ⟨6687, false, false, [1454, 1447], []⟩,
        ⟨6688, true, false, [], [1447, 78241]⟩,
        ⟨6689, true, false, [], [78241]⟩
      ]⟩,
    ⟨[77581, 3], [77581, 3], .contexts []⟩,
    ⟨[78243], [78243], .contexts []⟩,
    ⟨[1461], [749, 1447], .source 795⟩,
    ⟨[77581, 3], [1461, 78243], .contexts [
        ⟨6691, false, false, [], []⟩,
        ⟨3117, true, false, [], [3]⟩,
        ⟨3486, true, false, [746], [15, 3]⟩,
        ⟨900, false, false, [746, 77327], []⟩,
        ⟨20, false, false, [746, 77327], []⟩,
        ⟨6685, false, false, [746], []⟩,
        ⟨6692, false, false, [746, 1447], []⟩,
        ⟨3489, true, false, [], [1447, 78243]⟩,
        ⟨6693, true, false, [], [78243]⟩
      ]⟩,
    ⟨[1463], [1460], .source 796⟩,
    ⟨[1459, 78241], [1459, 78241], .contexts []⟩,
    ⟨[78239, 15], [78239, 15], .contexts []⟩,
    ⟨[78239], [78239], .contexts []⟩,
    ⟨[1465], [1458], .source 797⟩,
    ⟨[1458], [1458], .contexts []⟩,
    ⟨[1465], [1458], .contexts [
        ⟨6699, false, false, [], []⟩,
        ⟨6700, false, false, [], []⟩,
        ⟨6700, false, false, [], []⟩
      ]⟩,
    ⟨[1461, 78243], [1461, 78243], .contexts []⟩,
    ⟨[1461, 78243], [1461, 78243], .contexts []⟩,
    ⟨[1461, 78241], [1461, 78241], .contexts []⟩,
    ⟨[77581, 13], [77579], .contexts [
        ⟨3169, false, false, [], []⟩,
        ⟨3170, false, false, [], []⟩,
        ⟨3112, false, false, [], []⟩,
        ⟨3112, false, false, [], []⟩
      ]⟩,
    ⟨[1460], [1460], .contexts []⟩,
    ⟨[78241, 3], [1463, 77579], .contexts [
        ⟨6704, true, false, [1460], [3]⟩,
        ⟨6512, true, false, [], [3]⟩,
        ⟨6703, true, false, [1460], [13, 3]⟩,
        ⟨6703, true, false, [1460], [13, 3]⟩,
        ⟨6702, true, false, [1460], [13, 3]⟩,
        ⟨6694, true, false, [1460], [13, 3]⟩,
        ⟨6691, true, false, [1460], [13, 3]⟩,
        ⟨932, false, false, [1460, 77581], []⟩,
        ⟨108, false, false, [1460, 77581], []⟩,
        ⟨6705, false, false, [1460], []⟩,
        ⟨3503, false, false, [1460], []⟩,
        ⟨6706, true, false, [], [77579]⟩,
        ⟨6706, true, false, [], [77579]⟩,
        ⟨6695, true, false, [], [77579]⟩
      ]⟩,
    ⟨[1465, 78239], [1465, 78239], .contexts []⟩,
    ⟨[78239, 15], [1465, 78239], .contexts [
        ⟨6697, false, false, [], []⟩,
        ⟨6697, false, false, [], []⟩,
        ⟨6508, true, false, [], [15]⟩,
        ⟨6696, true, false, [1458], [1, 15]⟩,
        ⟨6696, true, false, [1458], [1, 15]⟩,
        ⟨6690, true, false, [1458], [1, 15]⟩,
        ⟨6686, true, false, [1458], [1, 15]⟩,
        ⟨2778, false, false, [1458, 78241], []⟩,
        ⟨19, false, false, [1458, 78241], []⟩,
        ⟨6546, false, false, [1458], []⟩,
        ⟨6547, false, false, [1458], []⟩,
        ⟨6507, false, false, [1458], []⟩,
        ⟨6507, false, false, [1458], []⟩,
        ⟨6698, false, false, [1458], []⟩,
        ⟨6701, true, false, [], [78239]⟩,
        ⟨6708, false, false, [], []⟩,
        ⟨6708, false, false, [], []⟩
      ]⟩,
    ⟨[78239, 11], [78237], .contexts [
        ⟨6548, false, false, [], []⟩,
        ⟨6549, false, false, [], []⟩,
        ⟨6503, false, false, [], []⟩,
        ⟨6503, false, false, [], []⟩
      ]⟩,
    ⟨[78239, 10], [78239, 11], .contexts [
        ⟨91, false, false, [78239], []⟩
      ]⟩,
    ⟨[78237, 15], [78237, 15], .contexts []⟩,
    ⟨[78237], [78237], .contexts []⟩,
    ⟨[1459], [1464], .contexts [
        ⟨6699, true, true, [], []⟩
      ]⟩,
    ⟨[1459], [1459], .contexts []⟩,
    ⟨[1464], [1464], .contexts []⟩,
    ⟨[1459], [1464], .contexts [
        ⟨6715, false, false, [], []⟩,
        ⟨6714, false, false, [], []⟩,
        ⟨6716, false, false, [], []⟩,
        ⟨6716, false, false, [], []⟩
      ]⟩,
    ⟨[78237, 15], [1459, 78237], .contexts [
        ⟨6712, false, false, [], []⟩,
        ⟨6504, true, false, [], [15]⟩,
        ⟨6709, true, false, [1464], [11, 15]⟩,
        ⟨3495, false, false, [1464, 78239], []⟩,
        ⟨6711, false, false, [1464], []⟩,
        ⟨6710, false, false, [1464], []⟩,
        ⟨6713, false, false, [1464], []⟩,
        ⟨6717, true, false, [], [78237]⟩
      ]⟩,
    ⟨[1459, 78237], [1459, 78237], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 105. -/
def y322TCContextRaw105 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78237, 15], [1459, 78237], .contexts [
        ⟨6712, false, false, [], []⟩,
        ⟨6718, false, false, [], []⟩,
        ⟨6719, false, false, [], []⟩,
        ⟨6719, false, false, [], []⟩
      ]⟩,
    ⟨[78237, 9], [78235], .contexts [
        ⟨6550, false, false, [], []⟩,
        ⟨6551, false, false, [], []⟩,
        ⟨6499, false, false, [], []⟩,
        ⟨6499, false, false, [], []⟩
      ]⟩,
    ⟨[78237, 8], [78237, 9], .contexts [
        ⟨77, false, false, [78237], []⟩
      ]⟩,
    ⟨[78235, 15], [78235, 15], .contexts []⟩,
    ⟨[78235], [78235], .contexts []⟩,
    ⟨[78235, 15], [1465, 78235], .contexts [
        ⟨6723, false, false, [], []⟩,
        ⟨6500, true, false, [], [15]⟩,
        ⟨6720, true, false, [1458], [9, 15]⟩,
        ⟨2787, false, false, [1458, 78237], []⟩,
        ⟨6722, false, false, [1458], []⟩,
        ⟨6721, false, false, [1458], []⟩,
        ⟨6724, false, false, [1458], []⟩,
        ⟨6701, true, false, [], [78235]⟩
      ]⟩,
    ⟨[1465, 78235], [1465, 78235], .contexts []⟩,
    ⟨[78235, 1], [78233], .contexts [
        ⟨6553, false, false, [], []⟩,
        ⟨6554, false, false, [], []⟩,
        ⟨6495, false, false, [], []⟩,
        ⟨6495, false, false, [], []⟩
      ]⟩,
    ⟨[78235, 0], [78235, 1], .contexts [
        ⟨19, false, false, [78235], []⟩
      ]⟩,
    ⟨[78233, 15], [78233, 15], .contexts []⟩,
    ⟨[78233], [78233], .contexts []⟩,
    ⟨[1459, 78233], [1459, 78233], .contexts []⟩,
    ⟨[78233, 15], [1459, 78233], .contexts [
        ⟨6729, false, false, [], []⟩,
        ⟨6729, false, false, [], []⟩,
        ⟨6496, true, false, [], [15]⟩,
        ⟨6726, true, false, [1464], [1, 15]⟩,
        ⟨6726, true, false, [1464], [1, 15]⟩,
        ⟨6725, true, false, [1464], [1, 15]⟩,
        ⟨6723, true, false, [1464], [1, 15]⟩,
        ⟨2778, false, false, [1464, 78235], []⟩,
        ⟨6728, false, false, [1464], []⟩,
        ⟨6727, false, false, [1464], []⟩,
        ⟨6730, false, false, [1464], []⟩,
        ⟨6717, true, false, [], [78233]⟩,
        ⟨6731, false, false, [], []⟩,
        ⟨6731, false, false, [], []⟩
      ]⟩,
    ⟨[78233, 5], [78231], .contexts [
        ⟨6555, false, false, [], []⟩
      ]⟩,
    ⟨[78233, 5], [78231], .contexts [
        ⟨6733, false, false, [], []⟩,
        ⟨6556, false, false, [], []⟩,
        ⟨6491, false, false, [], []⟩,
        ⟨6491, false, false, [], []⟩
      ]⟩,
    ⟨[78233, 4], [78233, 5], .contexts [
        ⟨50, false, false, [78233], []⟩
      ]⟩,
    ⟨[78231, 15], [78231, 15], .contexts []⟩,
    ⟨[78231], [78231], .contexts []⟩,
    ⟨[1465, 78231], [1465, 78231], .contexts []⟩,
    ⟨[78231, 15, 3], [1465, 78229], .contexts [
        ⟨6736, false, false, [], [3]⟩,
        ⟨6736, false, false, [], [3]⟩,
        ⟨6492, true, false, [], [15, 3]⟩,
        ⟨6732, true, false, [1458], [5, 15, 3]⟩,
        ⟨3532, false, false, [1458, 78233], [3]⟩,
        ⟨6735, false, false, [1458], [3]⟩,
        ⟨6734, false, false, [1458], [3]⟩,
        ⟨6737, false, false, [1458], [3]⟩,
        ⟨6701, true, false, [], [78231, 3]⟩,
        ⟨6738, false, false, [], [3]⟩,
        ⟨6738, false, false, [], [3]⟩,
        ⟨6489, false, false, [1465], []⟩
      ]⟩,
    ⟨[78229, 15], [78229, 15], .contexts []⟩,
    ⟨[78229], [78229], .contexts []⟩,
    ⟨[1459, 78229], [1459, 78229], .contexts []⟩,
    ⟨[1459, 78225], [1459, 78225], .contexts []⟩,
    ⟨[78229, 15, 1, 15], [1459, 78225], .contexts [
        ⟨6740, false, false, [], [1, 15]⟩,
        ⟨6740, false, false, [], [1, 15]⟩,
        ⟨6739, true, false, [1464], [15, 1, 15]⟩,
        ⟨1893, false, false, [1464, 78231], [1, 15]⟩,
        ⟨36, false, false, [1464, 78231], [1, 15]⟩,
        ⟨6557, false, false, [1464], [1, 15]⟩,
        ⟨6558, false, false, [1464], [1, 15]⟩,
        ⟨6488, false, false, [1464], [1, 15]⟩,
        ⟨6488, false, false, [1464], [1, 15]⟩,
        ⟨6741, false, false, [1464], [1, 15]⟩,
        ⟨6717, true, false, [], [78229, 1, 15]⟩,
        ⟨6742, false, false, [], [1, 15]⟩,
        ⟨6742, false, false, [], [1, 15]⟩,
        ⟨6486, false, false, [1459], [15]⟩,
        ⟨6483, false, false, [1459], []⟩,
        ⟨6743, false, false, [], []⟩
      ]⟩,
    ⟨[1459, 78225], [1459, 78225], .contexts []⟩,
    ⟨[78259], [77129, 3], .source 39194⟩,
    ⟨[77129, 3], [78259], .contexts [
        ⟨6746, true, false, [], []⟩
      ]⟩,
    ⟨[78259, 3], [77129], .contexts [
        ⟨6747, true, false, [], [3]⟩,
        ⟨35, false, false, [77129], []⟩,
        ⟨442, false, false, [], []⟩
      ]⟩,
    ⟨[78259], [78259], .contexts []⟩,
    ⟨[78259], [78259], .contexts []⟩,
    ⟨[77129, 3], [78259], .contexts [
        ⟨6747, false, false, [], []⟩,
        ⟨6749, false, false, [], []⟩,
        ⟨6750, false, false, [], []⟩,
        ⟨6750, false, false, [], []⟩
      ]⟩,
    ⟨[77129, 1], [77127], .contexts [
        ⟨723, false, false, [], []⟩,
        ⟨724, false, false, [], []⟩,
        ⟨438, false, false, [], []⟩,
        ⟨438, false, false, [], []⟩
      ]⟩,
    ⟨[323, 78259], [323, 78259], .contexts []⟩,
    ⟨[323, 78259], [323, 78259], .contexts []⟩,
    ⟨[78259, 1], [78259, 1], .contexts []⟩,
    ⟨[78259], [78259], .contexts []⟩,
    ⟨[78259, 1], [323, 78259], .contexts [
        ⟨6755, false, false, [], []⟩,
        ⟨6751, true, false, [], [1]⟩,
        ⟨213, false, false, [77129], []⟩,
        ⟨216, false, false, [77129], []⟩,
        ⟨6752, false, false, [], [3, 1, 3]⟩,
        ⟨5838, false, false, [], [1, 3]⟩,
        ⟨5839, false, false, [], [1, 3]⟩,
        ⟨5840, false, false, [], [1, 3]⟩,
        ⟨5840, false, false, [], [1, 3]⟩,
        ⟨437, false, false, [323], [3]⟩,
        ⟨6747, false, false, [323], []⟩,
        ⟨6753, false, false, [], []⟩,
        ⟨6754, false, false, [], []⟩,
        ⟨6756, false, false, [323], []⟩,
        ⟨5655, true, false, [], [78259]⟩
      ]⟩,
    ⟨[1063, 78259], [1063, 78259], .contexts []⟩,
    ⟨[1063, 78259], [1063, 78259], .contexts []⟩,
    ⟨[78259, 9], [78259, 9], .contexts []⟩,
    ⟨[77129, 11], [77993], .contexts [
        ⟨5668, true, false, [], [11]⟩,
        ⟨90, false, false, [77993], []⟩,
        ⟨5660, false, false, [], []⟩,
        ⟨5659, false, false, [], []⟩,
        ⟨5660, false, false, [], []⟩,
        ⟨5660, false, false, [], []⟩
      ]⟩,
    ⟨[1279, 77331], [1279, 77331], .contexts []⟩,
    ⟨[1279, 77331], [1279, 77331], .contexts []⟩,
    ⟨[78259, 11], [78259, 11], .contexts []⟩,
    ⟨[1279], [1279], .contexts [
        ⟨24, false, false, [], [1279]⟩
      ]⟩,
    ⟨[78259, 11], [1279, 77331], .contexts [
        ⟨6764, false, false, [], []⟩,
        ⟨6764, false, false, [], []⟩,
        ⟨6751, true, false, [], [11]⟩,
        ⟨231, false, false, [77129], []⟩,
        ⟨232, false, false, [77129], []⟩,
        ⟨6761, false, false, [], [3]⟩,
        ⟨5682, false, false, [], []⟩,
        ⟨6762, false, false, [], []⟩,
        ⟨6763, false, false, [], []⟩,
        ⟨6763, false, false, [], []⟩,
        ⟨2645, false, false, [1279], []⟩,
        ⟨6765, true, false, [], [77331]⟩,
        ⟨6762, false, false, [], []⟩,
        ⟨6763, false, false, [], []⟩,
        ⟨6763, false, false, [], []⟩
      ]⟩,
    ⟨[1467], [1279, 721], .source 798⟩,
    ⟨[1467, 77255], [1467, 77255], .contexts []⟩,
    ⟨[1467, 77255], [1467, 77255], .contexts []⟩,
    ⟨[1469], [1466], .source 799⟩,
    ⟨[1466], [1466], .contexts []⟩,
    ⟨[77255, 5], [1469, 78259], .contexts [
        ⟨6769, true, false, [1466], [5]⟩,
        ⟨6768, true, false, [1466], [5]⟩,
        ⟨1198, true, false, [], [5]⟩,
        ⟨6767, false, false, [1466], [77253, 11, 5]⟩,
        ⟨3412, true, false, [1466, 1279], [11, 5]⟩,
        ⟨6766, true, false, [1466], [5, 11, 5]⟩,
        ⟨1127, false, false, [1466, 78259], []⟩,
        ⟨6756, false, false, [1466], []⟩,
        ⟨6771, true, false, [], [78259]⟩,
        ⟨6771, true, false, [], [78259]⟩,
        ⟨6770, true, false, [], [78259]⟩
      ]⟩,
    ⟨[78261], [77129, 7], .source 39195⟩,
    ⟨[77129, 7], [78261], .contexts [
        ⟨6773, true, false, [], []⟩
      ]⟩,
    ⟨[77129, 7], [78261], .contexts [
        ⟨6774, false, false, [], []⟩
      ]⟩,
    ⟨[78261], [78261], .contexts []⟩,
    ⟨[78261], [78261], .contexts []⟩,
    ⟨[77129, 7], [78261], .contexts [
        ⟨6775, false, false, [], []⟩,
        ⟨6776, false, false, [], []⟩,
        ⟨6777, false, false, [], []⟩,
        ⟨6777, false, false, [], []⟩
      ]⟩,
    ⟨[78261, 1], [78261, 1], .contexts []⟩,
    ⟨[78117], [78117], .contexts []⟩,
    ⟨[78117], [78117], .contexts [
        ⟨6780, false, false, [], []⟩
      ]⟩,
    ⟨[78117], [78117], .contexts [
        ⟨1118, true, false, [], [78117]⟩
      ]⟩,
    ⟨[78261, 11], [78117], .contexts [
        ⟨6778, true, false, [], [11]⟩,
        ⟨1781, false, false, [77129], []⟩,
        ⟨1782, false, false, [77129], []⟩,
        ⟨6761, false, false, [], [7]⟩,
        ⟨6214, false, false, [], []⟩,
        ⟨6215, false, false, [], []⟩,
        ⟨6216, false, false, [], []⟩,
        ⟨6216, false, false, [], []⟩,
        ⟨6781, false, false, [], []⟩,
        ⟨6782, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 106. -/
def y322TCContextRaw106 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78263], [78257, 13], .source 39196⟩,
    ⟨[78257, 13], [78263], .contexts [
        ⟨6784, true, false, [], []⟩
      ]⟩,
    ⟨[78263], [78263], .contexts []⟩,
    ⟨[78257, 13], [78263], .contexts [
        ⟨6785, false, false, [], []⟩,
        ⟨6786, false, false, [], []⟩,
        ⟨6786, false, false, [], []⟩
      ]⟩,
    ⟨[1421, 78127], [1421, 78127], .contexts []⟩,
    ⟨[78263, 1], [1421, 78127], .contexts [
        ⟨6787, true, false, [], [1]⟩,
        ⟨387, false, false, [78257], []⟩,
        ⟨390, false, false, [78257], []⟩,
        ⟨6647, false, false, [], [13, 1, 13]⟩,
        ⟨443, false, false, [1421], [1, 13]⟩,
        ⟨439, false, false, [1421], [13]⟩,
        ⟨6260, false, false, [1421], []⟩,
        ⟨6788, false, false, [], []⟩,
        ⟨6264, false, false, [1421], []⟩,
        ⟨6642, true, false, [], [78127]⟩
      ]⟩,
    ⟨[78257, 5], [1453, 78257], .contexts [
        ⟨6676, false, false, [], []⟩,
        ⟨6674, false, false, [1450], [78257, 5]⟩,
        ⟨6654, true, false, [1450, 1449], [5]⟩,
        ⟨6673, false, false, [1450], [77587, 11, 5]⟩,
        ⟨3391, true, false, [1450, 1431], [11, 5]⟩,
        ⟨3127, true, false, [1450, 1431], [11, 5]⟩,
        ⟨6655, true, false, [1450], [5, 11, 5]⟩,
        ⟨6655, true, false, [1450], [5, 11, 5]⟩,
        ⟨6656, true, false, [1450], [5, 11, 5]⟩,
        ⟨6646, true, false, [1450], [5, 11, 5]⟩,
        ⟨1127, false, false, [1450, 78257], []⟩,
        ⟨6675, false, false, [1450], []⟩,
        ⟨6677, false, false, [1450], []⟩,
        ⟨6679, true, false, [], [78257]⟩,
        ⟨6679, true, false, [], [78257]⟩,
        ⟨6678, true, false, [], [78257]⟩
      ]⟩,
    ⟨[1453, 78257], [1453, 78257], .contexts []⟩,
    ⟨[78265], [78121, 5], .source 39197⟩,
    ⟨[78121, 5], [78265], .contexts [
        ⟨6792, true, false, [], []⟩
      ]⟩,
    ⟨[78265], [78265], .contexts []⟩,
    ⟨[78265], [78265], .contexts []⟩,
    ⟨[78121, 7], [77127], .contexts [
        ⟨6229, false, false, [], []⟩,
        ⟨6230, false, false, [], []⟩,
        ⟨724, false, false, [], []⟩,
        ⟨438, false, false, [], []⟩,
        ⟨438, false, false, [], []⟩
      ]⟩,
    ⟨[78121, 11], [78003], .contexts [
        ⟨6225, true, false, [], [11]⟩,
        ⟨90, false, false, [78003], []⟩,
        ⟨5768, false, false, [], []⟩,
        ⟨5767, false, false, [], []⟩,
        ⟨5768, false, false, [], []⟩,
        ⟨5768, false, false, [], []⟩
      ]⟩,
    ⟨[78119], [78119], .contexts []⟩,
    ⟨[78119], [78119], .contexts [
        ⟨1118, true, false, [], [78119]⟩
      ]⟩,
    ⟨[78267], [78121, 9], .source 39198⟩,
    ⟨[78121, 9], [78267], .contexts [
        ⟨6800, true, false, [], []⟩
      ]⟩,
    ⟨[78267], [78267], .contexts []⟩,
    ⟨[78267], [78267], .contexts []⟩,
    ⟨[78269], [78121, 13], .source 39199⟩,
    ⟨[78269], [78269], .contexts []⟩,
    ⟨[78121, 13], [78269], .contexts [
        ⟨6804, true, false, [], []⟩,
        ⟨6805, false, false, [], []⟩,
        ⟨6805, false, false, [], []⟩
      ]⟩,
    ⟨[78127], [78127], .contexts [
        ⟨6264, false, false, [], []⟩
      ]⟩,
    ⟨[78127], [78127], .contexts [
        ⟨1118, true, false, [], [78127]⟩
      ]⟩,
    ⟨[78271], [78121, 15], .source 39200⟩,
    ⟨[78121, 15], [78271], .contexts [
        ⟨6809, true, false, [], []⟩
      ]⟩,
    ⟨[78271], [78271], .contexts []⟩,
    ⟨[78271], [78271], .contexts []⟩,
    ⟨[78273], [78011, 13], .source 39201⟩,
    ⟨[78011, 13], [78273], .contexts [
        ⟨6813, true, false, [], []⟩
      ]⟩,
    ⟨[78273], [78273], .contexts []⟩,
    ⟨[78011, 13], [78273], .contexts [
        ⟨6814, false, false, [], []⟩,
        ⟨6815, false, false, [], []⟩,
        ⟨6815, false, false, [], []⟩
      ]⟩,
    ⟨[78011, 3, 13], [323, 78273], .contexts [
        ⟨5843, false, false, [], [13]⟩,
        ⟨5843, false, false, [], [13]⟩,
        ⟨5835, true, false, [], [3, 13]⟩,
        ⟨306, false, false, [77127], [13]⟩,
        ⟨307, false, false, [77127], [13]⟩,
        ⟨1981, false, false, [], [9, 13]⟩,
        ⟨5838, false, false, [], [9, 13]⟩,
        ⟨5839, false, false, [], [9, 13]⟩,
        ⟨5840, false, false, [], [9, 13]⟩,
        ⟨5840, false, false, [], [9, 13]⟩,
        ⟨5831, false, false, [323], [13]⟩,
        ⟨5841, false, false, [], [13]⟩,
        ⟨5842, false, false, [], [13]⟩,
        ⟨5836, false, false, [323], [13]⟩,
        ⟨5655, true, false, [], [78011, 13]⟩,
        ⟨5841, false, false, [], [13]⟩,
        ⟨5842, false, false, [], [13]⟩,
        ⟨5842, false, false, [], [13]⟩,
        ⟨6814, false, false, [323], []⟩
      ]⟩,
    ⟨[78273], [78273], .contexts []⟩,
    ⟨[78273, 5], [317, 78273], .contexts [
        ⟨6816, true, false, [], [5]⟩,
        ⟨116, false, false, [78011], []⟩,
        ⟨117, false, false, [78011], []⟩,
        ⟨5846, false, false, [], [13]⟩,
        ⟨5846, false, false, [], [13]⟩,
        ⟨5835, true, false, [], [5, 13]⟩,
        ⟨1805, false, false, [77127], [13]⟩,
        ⟨1806, false, false, [77127], [13]⟩,
        ⟨1991, false, false, [], [9, 13]⟩,
        ⟨5831, false, false, [317], [13]⟩,
        ⟨5844, false, false, [], [13]⟩,
        ⟨5845, false, false, [], [13]⟩,
        ⟨5836, false, false, [317], [13]⟩,
        ⟨1961, true, false, [], [78011, 13]⟩,
        ⟨5844, false, false, [], [13]⟩,
        ⟨5845, false, false, [], [13]⟩,
        ⟨5845, false, false, [], [13]⟩,
        ⟨6814, false, false, [317], []⟩
      ]⟩,
    ⟨[78011, 9], [77127], .contexts [
        ⟨5831, true, false, [], [9]⟩,
        ⟨76, false, false, [77127], []⟩,
        ⟨438, false, false, [], []⟩,
        ⟨724, false, false, [], []⟩,
        ⟨438, false, false, [], []⟩,
        ⟨438, false, false, [], []⟩
      ]⟩,
    ⟨[1315, 77971], [1315, 77971], .contexts []⟩,
    ⟨[78011, 11], [1315, 77971], .contexts [
        ⟨5849, false, false, [], []⟩,
        ⟨5851, false, false, [], []⟩,
        ⟨6821, false, false, [], []⟩,
        ⟨6821, false, false, [], []⟩
      ]⟩,
    ⟨[1315, 77969], [1315, 77969], .contexts []⟩,
    ⟨[1315, 77969], [1315, 77969], .contexts []⟩,
    ⟨[78273, 11], [78273, 11], .contexts []⟩,
    ⟨[78273, 11], [1315, 77969], .contexts [
        ⟨6825, false, false, [], []⟩,
        ⟨6816, true, false, [], [11]⟩,
        ⟨137, false, false, [78011], []⟩,
        ⟨138, false, false, [78011], []⟩,
        ⟨6822, false, false, [], [13]⟩,
        ⟨5146, false, false, [1315], []⟩,
        ⟨6823, false, false, [], []⟩,
        ⟨6824, false, false, [], []⟩,
        ⟨5367, false, false, [1315], []⟩,
        ⟨5850, true, false, [], [77969]⟩
      ]⟩,
    ⟨[78273, 11], [1315, 77969], .contexts [
        ⟨6825, false, false, [], []⟩,
        ⟨6826, false, false, [], []⟩,
        ⟨6823, false, false, [], []⟩,
        ⟨6824, false, false, [], []⟩,
        ⟨6824, false, false, [], []⟩
      ]⟩,
    ⟨[1315, 77965], [1315, 77965], .contexts []⟩,
    ⟨[1315, 77965], [1315, 77965], .contexts []⟩,
    ⟨[77965, 1], [77965, 1], .contexts []⟩,
    ⟨[1314], [1314], .contexts []⟩,
    ⟨[77965, 1], [1317, 78273], .contexts [
        ⟨6830, false, false, [], []⟩,
        ⟨6829, true, false, [1314], [1]⟩,
        ⟨6828, true, false, [1314], [1]⟩,
        ⟨5140, true, false, [], [1]⟩,
        ⟨5143, true, false, [], [11, 1]⟩,
        ⟨6827, true, false, [1314], [1, 11, 1]⟩,
        ⟨1068, false, false, [1314, 78273], []⟩,
        ⟨6818, false, false, [1314], []⟩,
        ⟨6831, true, false, [], [78273]⟩,
        ⟨6831, true, false, [], [78273]⟩,
        ⟨5852, true, false, [], [78273]⟩
      ]⟩,
    ⟨[78273, 1], [1315, 77965], .contexts [
        ⟨6832, true, false, [1316], [1]⟩,
        ⟨18, false, false, [1316, 77965], []⟩,
        ⟨5852, false, true, [], [77965]⟩
      ]⟩,
    ⟨[1317, 78273], [1317, 78273], .contexts []⟩,
    ⟨[1481], [1317, 1423], .source 805⟩,
    ⟨[1481, 78263, 9], [77965, 9, 1], .contexts [
        ⟨6835, false, false, [], [78263, 9]⟩,
        ⟨6644, false, false, [1317], [78263, 9]⟩,
        ⟨18, true, false, [1317, 1420, 78263], [9]⟩,
        ⟨6789, false, false, [1317, 1420], [1, 9]⟩,
        ⟨6808, true, false, [1317], [1, 9]⟩,
        ⟨6807, true, false, [1317], [1, 9]⟩,
        ⟨6263, true, false, [1317], [1, 9]⟩,
        ⟨6263, true, false, [1317], [1, 9]⟩,
        ⟨6262, true, false, [1317], [1, 9]⟩,
        ⟨6261, true, false, [1317], [1, 9]⟩,
        ⟨6820, true, false, [1317], [13, 1, 9]⟩,
        ⟨131, true, false, [1317, 78011], [1, 9]⟩,
        ⟨130, true, false, [1317, 78011], [1, 9]⟩,
        ⟨6816, false, false, [1317], [9, 1, 9]⟩,
        ⟨6834, true, false, [], [9, 1, 9]⟩,
        ⟨6834, true, false, [], [9, 1, 9]⟩,
        ⟨6832, true, false, [], [9, 1, 9]⟩,
        ⟨6830, true, false, [], [9, 1, 9]⟩,
        ⟨1022, false, false, [77965], []⟩,
        ⟨787, false, false, [77965], []⟩
      ]⟩,
    ⟨[1483], [1480], .source 806⟩,
    ⟨[1485], [1483, 1191], .source 807⟩,
    ⟨[1487], [1484], .source 808⟩,
    ⟨[78275], [78011, 15], .source 39202⟩,
    ⟨[78275], [78275], .contexts []⟩,
    ⟨[78011, 15], [78275], .contexts [
        ⟨6840, true, false, [], []⟩,
        ⟨6841, false, false, [], []⟩,
        ⟨6841, false, false, [], []⟩
      ]⟩,
    ⟨[78277], [77253, 13], .source 39203⟩,
    ⟨[77253, 13], [78277], .contexts [
        ⟨6843, true, false, [], []⟩
      ]⟩,
    ⟨[78277], [78277], .contexts []⟩,
    ⟨[77253, 13], [78277], .contexts [
        ⟨6844, false, false, [], []⟩,
        ⟨6845, false, false, [], []⟩,
        ⟨6845, false, false, [], []⟩
      ]⟩,
    ⟨[555, 78277], [555, 78277], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 107. -/
def y322TCContextRaw107 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[555, 78277], [555, 78277], .contexts []⟩,
    ⟨[555, 78277], [555, 78277], .contexts []⟩,
    ⟨[78277, 3], [78277, 3], .contexts []⟩,
    ⟨[555], [555], .contexts [
        ⟨24, false, false, [], [555]⟩
      ]⟩,
    ⟨[78277, 3], [555, 78277], .contexts [
        ⟨6850, false, false, [], []⟩,
        ⟨6846, true, false, [], [3]⟩,
        ⟨107, false, false, [77253], []⟩,
        ⟨109, false, false, [77253], []⟩,
        ⟨2874, false, false, [], [13]⟩,
        ⟨6844, false, false, [555], []⟩,
        ⟨6847, false, false, [], []⟩,
        ⟨6848, false, false, [], []⟩,
        ⟨6849, false, false, [], []⟩,
        ⟨6851, true, false, [], [78277]⟩
      ]⟩,
    ⟨[723, 77331], [723, 77331], .contexts []⟩,
    ⟨[78277, 11], [78277, 11], .contexts []⟩,
    ⟨[275], [275], .contexts [
        ⟨24, false, false, [], [275]⟩,
        ⟨1732, false, false, [], []⟩,
        ⟨1733, false, false, [], []⟩
      ]⟩,
    ⟨[78277, 11], [275, 77259], .contexts [
        ⟨6854, false, false, [], []⟩,
        ⟨6846, true, false, [], [11]⟩,
        ⟨137, false, false, [77253], []⟩,
        ⟨138, false, false, [77253], []⟩,
        ⟨1731, false, false, [], [13]⟩,
        ⟨1742, false, false, [], []⟩,
        ⟨1743, false, false, [], []⟩,
        ⟨1744, false, false, [], []⟩,
        ⟨1744, false, false, [], []⟩,
        ⟨1749, false, false, [275], []⟩,
        ⟨6855, true, false, [], [77259]⟩
      ]⟩,
    ⟨[77259, 11], [277, 78277], .contexts [
        ⟨6856, true, false, [274], [11]⟩,
        ⟨90, false, false, [274, 78277], []⟩,
        ⟨1664, true, false, [], [78277]⟩
      ]⟩,
    ⟨[78279], [78277, 15], .source 39204⟩,
    ⟨[78277, 15], [78279], .contexts [
        ⟨6858, true, false, [], []⟩
      ]⟩,
    ⟨[78279], [78279], .contexts []⟩,
    ⟨[78279], [78279], .contexts []⟩,
    ⟨[78277, 15], [78279], .contexts [
        ⟨6859, false, false, [], []⟩,
        ⟨6860, false, false, [], []⟩,
        ⟨6861, false, false, [], []⟩,
        ⟨6861, false, false, [], []⟩
      ]⟩,
    ⟨[555, 78279], [555, 78279], .contexts []⟩,
    ⟨[555, 78279], [555, 78279], .contexts []⟩,
    ⟨[555, 78279], [555, 78279], .contexts []⟩,
    ⟨[78279], [78279], .contexts []⟩,
    ⟨[275, 77261], [275, 77261], .contexts []⟩,
    ⟨[275, 77261], [275, 77261], .contexts []⟩,
    ⟨[78279, 11], [78279, 11], .contexts []⟩,
    ⟨[78279, 11], [275, 77261], .contexts [
        ⟨6869, false, false, [], []⟩,
        ⟨6862, true, false, [], [11]⟩,
        ⟨89, false, false, [78277], []⟩,
        ⟨92, false, false, [78277], []⟩,
        ⟨6854, false, false, [], [15]⟩,
        ⟨6856, false, false, [], [15]⟩,
        ⟨1743, false, false, [], [15]⟩,
        ⟨1744, false, false, [], [15]⟩,
        ⟨1744, false, false, [], [15]⟩,
        ⟨1207, false, false, [275], []⟩,
        ⟨6867, false, false, [], []⟩,
        ⟨6868, false, false, [], []⟩,
        ⟨1755, false, false, [275], []⟩,
        ⟨6855, true, false, [], [77261]⟩
      ]⟩,
    ⟨[78281], [78279, 1], .source 39205⟩,
    ⟨[78279, 1], [78281], .contexts [
        ⟨6871, true, false, [], []⟩
      ]⟩,
    ⟨[78281, 1], [78279], .contexts [
        ⟨6872, true, false, [], [1]⟩,
        ⟨18, false, false, [78279], []⟩,
        ⟨6861, false, false, [], []⟩
      ]⟩,
    ⟨[78281], [78281], .contexts []⟩,
    ⟨[275, 77263], [275, 77263], .contexts []⟩,
    ⟨[275, 77263], [275, 77263], .contexts []⟩,
    ⟨[78281, 11], [78281, 11], .contexts []⟩,
    ⟨[78281, 11], [275, 77263], .contexts [
        ⟨6877, false, false, [], []⟩,
        ⟨6874, true, false, [], [11]⟩,
        ⟨6874, true, false, [], [11]⟩,
        ⟨6872, true, false, [], [11]⟩,
        ⟨181, false, false, [78279], []⟩,
        ⟨182, false, false, [78279], []⟩,
        ⟨6869, false, false, [], [1]⟩,
        ⟨6870, false, false, [], [1]⟩,
        ⟨6867, false, false, [], [1]⟩,
        ⟨6868, false, false, [], [1]⟩,
        ⟨6868, false, false, [], [1]⟩,
        ⟨1211, false, false, [275], []⟩,
        ⟨6875, false, false, [], []⟩,
        ⟨6876, false, false, [], []⟩,
        ⟨6855, true, false, [], [77263]⟩
      ]⟩,
    ⟨[77263, 11], [277, 78281], .contexts [
        ⟨6878, true, false, [274], [11]⟩,
        ⟨90, false, false, [274, 78281], []⟩,
        ⟨1664, true, false, [], [78281]⟩
      ]⟩,
    ⟨[78283], [78281, 3], .source 39206⟩,
    ⟨[78281, 3], [78283], .contexts [
        ⟨6880, true, false, [], []⟩
      ]⟩,
    ⟨[78283], [78283], .contexts []⟩,
    ⟨[78281, 3], [78283], .contexts [
        ⟨6881, false, false, [], []⟩,
        ⟨6882, false, false, [], []⟩,
        ⟨6882, false, false, [], []⟩
      ]⟩,
    ⟨[555, 78281], [555, 78281], .contexts []⟩,
    ⟨[555, 78281], [555, 78281], .contexts []⟩,
    ⟨[78281, 1, 3, 1], [555, 78281], .contexts [
        ⟨6873, false, false, [], [3, 1]⟩,
        ⟨6860, false, false, [], [3, 1]⟩,
        ⟨6861, false, false, [], [3, 1]⟩,
        ⟨6861, false, false, [], [3, 1]⟩,
        ⟨6862, true, false, [], [3, 1]⟩,
        ⟨34, false, false, [78277], [1]⟩,
        ⟨37, false, false, [78277], [1]⟩,
        ⟨6850, false, false, [], [15, 1]⟩,
        ⟨6852, false, false, [], [15, 1]⟩,
        ⟨6847, false, false, [], [15, 1]⟩,
        ⟨6849, false, false, [], [15, 1]⟩,
        ⟨6849, false, false, [], [15, 1]⟩,
        ⟨6859, false, false, [555], [1]⟩,
        ⟨6863, false, false, [], [1]⟩,
        ⟨6864, false, false, [], [1]⟩,
        ⟨6865, false, false, [], [1]⟩,
        ⟨6866, false, false, [555], [1]⟩,
        ⟨6851, true, false, [], [78279, 1]⟩,
        ⟨6863, false, false, [], [1]⟩,
        ⟨6865, false, false, [], [1]⟩,
        ⟨6865, false, false, [], [1]⟩,
        ⟨6872, false, false, [555], []⟩,
        ⟨6884, false, false, [], []⟩,
        ⟨6885, false, false, [], []⟩
      ]⟩,
    ⟨[555, 78281], [555, 78281], .contexts []⟩,
    ⟨[555, 78283], [555, 78283], .contexts []⟩,
    ⟨[555, 78283], [555, 78283], .contexts []⟩,
    ⟨[555, 78283], [555, 78283], .contexts []⟩,
    ⟨[78283, 1], [78283, 1], .contexts []⟩,
    ⟨[275, 77265], [275, 77265], .contexts []⟩,
    ⟨[275, 77265], [275, 77265], .contexts []⟩,
    ⟨[78283, 11], [78283, 11], .contexts []⟩,
    ⟨[78283, 11], [275, 77265], .contexts [
        ⟨6894, false, false, [], []⟩,
        ⟨6883, true, false, [], [11]⟩,
        ⟨231, false, false, [78281], []⟩,
        ⟨232, false, false, [78281], []⟩,
        ⟨6877, false, false, [], [3]⟩,
        ⟨6878, false, false, [], [3]⟩,
        ⟨6875, false, false, [], [3]⟩,
        ⟨6876, false, false, [], [3]⟩,
        ⟨6876, false, false, [], [3]⟩,
        ⟨1215, false, false, [275], []⟩,
        ⟨6892, false, false, [], []⟩,
        ⟨6893, false, false, [], []⟩,
        ⟨2894, false, false, [275], []⟩,
        ⟨6855, true, false, [], [77265]⟩
      ]⟩,
    ⟨[77265, 11], [277, 78283], .contexts [
        ⟨6895, true, false, [274], [11]⟩,
        ⟨90, false, false, [274, 78283], []⟩,
        ⟨1664, true, false, [], [78283]⟩
      ]⟩,
    ⟨[78285], [78283, 5], .source 39207⟩,
    ⟨[78283, 5], [78285], .contexts [
        ⟨6897, true, false, [], []⟩
      ]⟩,
    ⟨[78285], [78285], .contexts []⟩,
    ⟨[78285], [78285], .contexts []⟩,
    ⟨[78283, 5], [78285], .contexts [
        ⟨6898, false, false, [], []⟩,
        ⟨6899, false, false, [], []⟩,
        ⟨6900, false, false, [], []⟩,
        ⟨6900, false, false, [], []⟩
      ]⟩,
    ⟨[78283, 1], [555, 78283], .contexts [
        ⟨6891, false, false, [], []⟩,
        ⟨6891, false, false, [], []⟩,
        ⟨6883, true, false, [], [1]⟩,
        ⟨213, false, false, [78281], []⟩,
        ⟨216, false, false, [78281], []⟩,
        ⟨6886, false, false, [], [3]⟩,
        ⟨6887, false, false, [], [3]⟩,
        ⟨6881, false, false, [555], []⟩,
        ⟨6888, false, false, [], []⟩,
        ⟨6889, false, false, [], []⟩,
        ⟨6890, false, false, [], []⟩,
        ⟨6851, true, false, [], [78283]⟩,
        ⟨6888, false, false, [], []⟩,
        ⟨6890, false, false, [], []⟩,
        ⟨6890, false, false, [], []⟩
      ]⟩,
    ⟨[555, 78285], [555, 78285], .contexts []⟩,
    ⟨[555, 78285], [555, 78285], .contexts []⟩,
    ⟨[78285], [78285], .contexts []⟩,
    ⟨[78283, 11], [275, 77265], .contexts [
        ⟨6894, false, false, [], []⟩,
        ⟨6895, false, false, [], []⟩,
        ⟨6892, false, false, [], []⟩,
        ⟨6893, false, false, [], []⟩,
        ⟨6893, false, false, [], []⟩
      ]⟩,
    ⟨[275, 77267], [275, 77267], .contexts []⟩,
    ⟨[275, 77267], [275, 77267], .contexts []⟩,
    ⟨[77267], [77267], .contexts []⟩,
    ⟨[78285, 11], [275, 77267], .contexts [
        ⟨6901, true, false, [], [11]⟩,
        ⟨275, false, false, [78283], []⟩,
        ⟨276, false, false, [78283], []⟩,
        ⟨6906, false, false, [], [5]⟩,
        ⟨1218, false, false, [275], []⟩,
        ⟨6907, false, false, [], []⟩,
        ⟨6908, false, false, [], []⟩,
        ⟨6909, false, false, [275], []⟩,
        ⟨6855, true, false, [], [77267]⟩
      ]⟩,
    ⟨[77267, 11], [277, 78285], .contexts [
        ⟨6910, true, false, [274], [11]⟩,
        ⟨90, false, false, [274, 78285], []⟩,
        ⟨1664, true, false, [], [78285]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 108. -/
def y322TCContextRaw108 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78287], [78285, 9], .source 39208⟩,
    ⟨[78285, 9], [78287], .contexts [
        ⟨6912, true, false, [], []⟩
      ]⟩,
    ⟨[78289], [78287, 11], .source 39209⟩,
    ⟨[78287, 11], [78289], .contexts [
        ⟨6914, true, false, [], []⟩
      ]⟩,
    ⟨[78287], [78287], .contexts []⟩,
    ⟨[78289, 11], [78287], .contexts [
        ⟨6915, true, false, [], [11]⟩,
        ⟨90, false, false, [78287], []⟩,
        ⟨6916, false, false, [], []⟩
      ]⟩,
    ⟨[78289], [78289], .contexts []⟩,
    ⟨[78289], [78289], .contexts []⟩,
    ⟨[78287, 11], [78289], .contexts [
        ⟨6915, false, false, [], []⟩,
        ⟨6918, false, false, [], []⟩,
        ⟨6919, false, false, [], []⟩,
        ⟨6919, false, false, [], []⟩
      ]⟩,
    ⟨[78287, 9], [78285], .contexts [
        ⟨6913, true, false, [], [9]⟩,
        ⟨76, false, false, [78285], []⟩,
        ⟨6900, false, false, [], []⟩
      ]⟩,
    ⟨[1489], [275, 561], .source 809⟩,
    ⟨[77273], [77273], .contexts []⟩,
    ⟨[78289, 9], [1489, 77273], .contexts [
        ⟨6920, true, false, [], [9]⟩,
        ⟨344, false, false, [78287], []⟩,
        ⟨346, false, false, [78287], []⟩,
        ⟨6921, false, false, [], [11, 9, 11]⟩,
        ⟨6899, false, false, [], [11, 9, 11]⟩,
        ⟨6900, false, false, [], [11, 9, 11]⟩,
        ⟨6900, false, false, [], [11, 9, 11]⟩,
        ⟨6910, false, false, [], [9, 11]⟩,
        ⟨6907, false, false, [], [9, 11]⟩,
        ⟨6908, false, false, [], [9, 11]⟩,
        ⟨6908, false, false, [], [9, 11]⟩,
        ⟨2905, false, false, [275], [11]⟩,
        ⟨6922, true, false, [], [77271, 11]⟩,
        ⟨1229, false, false, [1489], []⟩,
        ⟨6923, false, false, [1489], []⟩
      ]⟩,
    ⟨[1491], [1488], .source 810⟩,
    ⟨[78291], [78289, 1], .source 39210⟩,
    ⟨[78289, 1], [78291], .contexts [
        ⟨6926, true, false, [], []⟩
      ]⟩,
    ⟨[78293], [78291, 13], .source 39211⟩,
    ⟨[78291, 13], [78293], .contexts [
        ⟨6928, true, false, [], []⟩
      ]⟩,
    ⟨[78291], [78291], .contexts []⟩,
    ⟨[78295], [78293, 15], .source 39212⟩,
    ⟨[78293, 15], [78295], .contexts [
        ⟨6931, true, false, [], []⟩
      ]⟩,
    ⟨[78293], [78293], .contexts []⟩,
    ⟨[78297], [78295, 1], .source 39213⟩,
    ⟨[78295, 1], [78297], .contexts [
        ⟨6934, true, false, [], []⟩
      ]⟩,
    ⟨[78295], [78295], .contexts []⟩,
    ⟨[78299], [78297, 3], .source 39214⟩,
    ⟨[78297, 3], [78299], .contexts [
        ⟨6937, true, false, [], []⟩
      ]⟩,
    ⟨[78297], [78297], .contexts []⟩,
    ⟨[78299, 3], [78297], .contexts [
        ⟨6938, true, false, [], [3]⟩,
        ⟨35, false, false, [78297], []⟩,
        ⟨6939, false, false, [], []⟩
      ]⟩,
    ⟨[78301], [78299, 5], .source 39215⟩,
    ⟨[78299, 5], [78301], .contexts [
        ⟨6941, true, false, [], []⟩
      ]⟩,
    ⟨[78299], [78299], .contexts []⟩,
    ⟨[78303], [78301, 1], .source 39216⟩,
    ⟨[78301, 1], [78303], .contexts [
        ⟨6944, true, false, [], []⟩
      ]⟩,
    ⟨[78301], [78301], .contexts []⟩,
    ⟨[78305], [78303, 9], .source 39217⟩,
    ⟨[78303, 9], [78305], .contexts [
        ⟨6947, true, false, [], []⟩
      ]⟩,
    ⟨[78303], [78303], .contexts []⟩,
    ⟨[78307], [78305, 11], .source 39218⟩,
    ⟨[78305, 11], [78307], .contexts [
        ⟨6950, true, false, [], []⟩
      ]⟩,
    ⟨[78305], [78305], .contexts []⟩,
    ⟨[78307, 11], [78305], .contexts [
        ⟨6951, true, false, [], [11]⟩,
        ⟨90, false, false, [78305], []⟩,
        ⟨6952, false, false, [], []⟩
      ]⟩,
    ⟨[78309], [78307, 1], .source 39219⟩,
    ⟨[78307, 1], [78309], .contexts [
        ⟨6954, true, false, [], []⟩
      ]⟩,
    ⟨[78307], [78307], .contexts []⟩,
    ⟨[78311], [78309, 13], .source 39220⟩,
    ⟨[78309, 13], [78311], .contexts [
        ⟨6957, true, false, [], []⟩
      ]⟩,
    ⟨[78309], [78309], .contexts []⟩,
    ⟨[78311, 13], [78309], .contexts [
        ⟨6958, true, false, [], [13]⟩,
        ⟨98, false, false, [78309], []⟩,
        ⟨6959, false, false, [], []⟩
      ]⟩,
    ⟨[78313], [78311, 15], .source 39221⟩,
    ⟨[78311, 15], [78313], .contexts [
        ⟨6961, true, false, [], []⟩
      ]⟩,
    ⟨[78311], [78311], .contexts []⟩,
    ⟨[78313, 15], [78311], .contexts [
        ⟨6962, true, false, [], [15]⟩,
        ⟨3, false, false, [78311], []⟩,
        ⟨6963, false, false, [], []⟩
      ]⟩,
    ⟨[78315], [78313, 1], .source 39222⟩,
    ⟨[78313, 1], [78315], .contexts [
        ⟨6965, true, false, [], []⟩
      ]⟩,
    ⟨[78313], [78313], .contexts []⟩,
    ⟨[78317], [78315, 3], .source 39223⟩,
    ⟨[78315, 3], [78317], .contexts [
        ⟨6968, true, false, [], []⟩
      ]⟩,
    ⟨[78315], [78315], .contexts []⟩,
    ⟨[78319], [78317, 5], .source 39224⟩,
    ⟨[78317, 5], [78319], .contexts [
        ⟨6971, true, false, [], []⟩
      ]⟩,
    ⟨[78317], [78317], .contexts []⟩,
    ⟨[78321], [78319, 1], .source 39225⟩,
    ⟨[78319, 1], [78321], .contexts [
        ⟨6974, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 109. -/
def y322TCContextRaw109 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78319], [78319], .contexts []⟩,
    ⟨[78323], [78321, 9], .source 39226⟩,
    ⟨[78321, 9], [78323], .contexts [
        ⟨6977, true, false, [], []⟩
      ]⟩,
    ⟨[78321], [78321], .contexts []⟩,
    ⟨[78325], [78323, 11], .source 39227⟩,
    ⟨[78323, 11], [78325], .contexts [
        ⟨6980, true, false, [], []⟩
      ]⟩,
    ⟨[78323], [78323], .contexts []⟩,
    ⟨[78327], [78325, 1], .source 39228⟩,
    ⟨[78325, 1], [78327], .contexts [
        ⟨6983, true, false, [], []⟩
      ]⟩,
    ⟨[78325], [78325], .contexts []⟩,
    ⟨[78329], [78327, 13], .source 39229⟩,
    ⟨[78327, 13], [78329], .contexts [
        ⟨6986, true, false, [], []⟩
      ]⟩,
    ⟨[78327], [78327], .contexts []⟩,
    ⟨[78331], [78329, 15], .source 39230⟩,
    ⟨[78329, 15], [78331], .contexts [
        ⟨6989, true, false, [], []⟩
      ]⟩,
    ⟨[78329], [78329], .contexts []⟩,
    ⟨[78333], [78331, 1], .source 39231⟩,
    ⟨[78331, 1], [78333], .contexts [
        ⟨6992, true, false, [], []⟩
      ]⟩,
    ⟨[78331], [78331], .contexts []⟩,
    ⟨[78335], [78333, 3], .source 39232⟩,
    ⟨[78333, 3], [78335], .contexts [
        ⟨6995, true, false, [], []⟩
      ]⟩,
    ⟨[78333], [78333], .contexts []⟩,
    ⟨[78337], [78335, 5], .source 39233⟩,
    ⟨[78335, 5], [78337], .contexts [
        ⟨6998, true, false, [], []⟩
      ]⟩,
    ⟨[78335], [78335], .contexts []⟩,
    ⟨[78339], [78337, 1], .source 39234⟩,
    ⟨[78337, 1], [78339], .contexts [
        ⟨7001, true, false, [], []⟩
      ]⟩,
    ⟨[78337], [78337], .contexts []⟩,
    ⟨[78339, 1], [78337], .contexts [
        ⟨7002, true, false, [], [1]⟩,
        ⟨18, false, false, [78337], []⟩,
        ⟨7003, false, false, [], []⟩
      ]⟩,
    ⟨[78341], [78339, 9], .source 39235⟩,
    ⟨[78339, 9], [78341], .contexts [
        ⟨7005, true, false, [], []⟩
      ]⟩,
    ⟨[78339], [78339], .contexts []⟩,
    ⟨[78343], [78341, 11], .source 39236⟩,
    ⟨[78341, 11], [78343], .contexts [
        ⟨7008, true, false, [], []⟩
      ]⟩,
    ⟨[78341], [78341], .contexts []⟩,
    ⟨[78345], [78343, 1], .source 39237⟩,
    ⟨[78343, 1], [78345], .contexts [
        ⟨7011, true, false, [], []⟩
      ]⟩,
    ⟨[78343], [78343], .contexts []⟩,
    ⟨[78347], [78345, 13], .source 39238⟩,
    ⟨[78345, 13], [78347], .contexts [
        ⟨7014, true, false, [], []⟩
      ]⟩,
    ⟨[78345], [78345], .contexts []⟩,
    ⟨[78349], [78347, 15], .source 39239⟩,
    ⟨[78347, 15], [78349], .contexts [
        ⟨7017, true, false, [], []⟩
      ]⟩,
    ⟨[78347], [78347], .contexts []⟩,
    ⟨[78351], [78349, 1], .source 39240⟩,
    ⟨[78349, 1], [78351], .contexts [
        ⟨7020, true, false, [], []⟩
      ]⟩,
    ⟨[78349], [78349], .contexts []⟩,
    ⟨[78353], [78351, 3], .source 39241⟩,
    ⟨[78351, 3], [78353], .contexts [
        ⟨7023, true, false, [], []⟩
      ]⟩,
    ⟨[78351], [78351], .contexts []⟩,
    ⟨[78355], [78353, 5], .source 39242⟩,
    ⟨[78353, 5], [78355], .contexts [
        ⟨7026, true, false, [], []⟩
      ]⟩,
    ⟨[78353], [78353], .contexts []⟩,
    ⟨[78357], [78355, 1], .source 39243⟩,
    ⟨[78355, 1], [78357], .contexts [
        ⟨7029, true, false, [], []⟩
      ]⟩,
    ⟨[78355], [78355], .contexts []⟩,
    ⟨[78359], [78357, 9], .source 39244⟩,
    ⟨[78357, 9], [78359], .contexts [
        ⟨7032, true, false, [], []⟩
      ]⟩,
    ⟨[78357], [78357], .contexts []⟩,
    ⟨[78361], [78359, 11], .source 39245⟩,
    ⟨[78359, 11], [78361], .contexts [
        ⟨7035, true, false, [], []⟩
      ]⟩,
    ⟨[78359], [78359], .contexts []⟩,
    ⟨[78363], [78361, 1], .source 39246⟩,
    ⟨[78361, 1], [78363], .contexts [
        ⟨7038, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 110. -/
def y322TCContextRaw110 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78361], [78361], .contexts []⟩,
    ⟨[78365], [78363, 13], .source 39247⟩,
    ⟨[78363, 13], [78365], .contexts [
        ⟨7041, true, false, [], []⟩
      ]⟩,
    ⟨[78363], [78363], .contexts []⟩,
    ⟨[78367], [78365, 15], .source 39248⟩,
    ⟨[78365, 15], [78367], .contexts [
        ⟨7044, true, false, [], []⟩
      ]⟩,
    ⟨[78365], [78365], .contexts []⟩,
    ⟨[78369], [78367, 1], .source 39249⟩,
    ⟨[78367, 1], [78369], .contexts [
        ⟨7047, true, false, [], []⟩
      ]⟩,
    ⟨[78367], [78367], .contexts []⟩,
    ⟨[78371], [78369, 3], .source 39250⟩,
    ⟨[78369, 3], [78371], .contexts [
        ⟨7050, true, false, [], []⟩
      ]⟩,
    ⟨[78369], [78369], .contexts []⟩,
    ⟨[78373], [78371, 5], .source 39251⟩,
    ⟨[78371], [78371], .contexts []⟩,
    ⟨[78373, 5], [78371], .contexts [
        ⟨7053, false, false, [], [5]⟩,
        ⟨49, false, false, [78371], []⟩,
        ⟨7054, false, false, [], []⟩
      ]⟩,
    ⟨[78375], [78373, 1], .source 39252⟩,
    ⟨[78373], [78373], .contexts []⟩,
    ⟨[78375, 1], [78373], .contexts [
        ⟨7056, false, false, [], [1]⟩,
        ⟨18, false, false, [78373], []⟩,
        ⟨7057, false, false, [], []⟩
      ]⟩,
    ⟨[78377], [78375, 9], .source 39253⟩,
    ⟨[78375], [78375], .contexts []⟩,
    ⟨[78377, 9], [78375], .contexts [
        ⟨7059, false, false, [], [9]⟩,
        ⟨76, false, false, [78375], []⟩,
        ⟨7060, false, false, [], []⟩
      ]⟩,
    ⟨[78379], [78377, 11], .source 39254⟩,
    ⟨[78377, 11], [78379], .contexts [
        ⟨7062, true, false, [], []⟩
      ]⟩,
    ⟨[78377], [78377], .contexts []⟩,
    ⟨[78379, 11], [78377], .contexts [
        ⟨7063, true, false, [], [11]⟩,
        ⟨90, false, false, [78377], []⟩,
        ⟨7064, false, false, [], []⟩
      ]⟩,
    ⟨[78381], [78379, 1], .source 39255⟩,
    ⟨[78379, 1], [78381], .contexts [
        ⟨7066, true, false, [], []⟩
      ]⟩,
    ⟨[78379], [78379], .contexts []⟩,
    ⟨[78381, 1], [78379], .contexts [
        ⟨7067, true, false, [], [1]⟩,
        ⟨18, false, false, [78379], []⟩,
        ⟨7068, false, false, [], []⟩
      ]⟩,
    ⟨[78383], [78381, 13], .source 39256⟩,
    ⟨[78381], [78381], .contexts []⟩,
    ⟨[78383, 13], [78381], .contexts [
        ⟨7070, false, false, [], [13]⟩,
        ⟨98, false, false, [78381], []⟩,
        ⟨7071, false, false, [], []⟩
      ]⟩,
    ⟨[78385], [78383, 15], .source 39257⟩,
    ⟨[78383], [78383], .contexts []⟩,
    ⟨[78385, 15], [78383], .contexts [
        ⟨7073, false, false, [], [15]⟩,
        ⟨3, false, false, [78383], []⟩,
        ⟨7074, false, false, [], []⟩
      ]⟩,
    ⟨[78387], [78385, 1], .source 39258⟩,
    ⟨[78385], [78385], .contexts []⟩,
    ⟨[78387, 1], [78385], .contexts [
        ⟨7076, false, false, [], [1]⟩,
        ⟨18, false, false, [78385], []⟩,
        ⟨7077, false, false, [], []⟩
      ]⟩,
    ⟨[78389], [78387, 3], .source 39259⟩,
    ⟨[78387], [78387], .contexts []⟩,
    ⟨[78389, 3], [78387], .contexts [
        ⟨7079, false, false, [], [3]⟩,
        ⟨35, false, false, [78387], []⟩,
        ⟨7080, false, false, [], []⟩
      ]⟩,
    ⟨[78391], [78389, 5], .source 39260⟩,
    ⟨[78389], [78389], .contexts []⟩,
    ⟨[78391, 5], [78389], .contexts [
        ⟨7082, false, false, [], [5]⟩,
        ⟨49, false, false, [78389], []⟩,
        ⟨7083, false, false, [], []⟩
      ]⟩,
    ⟨[78393], [78391, 1], .source 39261⟩,
    ⟨[78391, 1], [78393], .contexts [
        ⟨7085, true, false, [], []⟩
      ]⟩,
    ⟨[78391], [78391], .contexts []⟩,
    ⟨[78393, 1], [78391], .contexts [
        ⟨7086, true, false, [], [1]⟩,
        ⟨18, false, false, [78391], []⟩,
        ⟨7087, false, false, [], []⟩
      ]⟩,
    ⟨[78395], [78393, 9], .source 39262⟩,
    ⟨[78393], [78393], .contexts []⟩,
    ⟨[78395, 9], [78393], .contexts [
        ⟨7089, false, false, [], [9]⟩,
        ⟨76, false, false, [78393], []⟩,
        ⟨7090, false, false, [], []⟩
      ]⟩,
    ⟨[78397], [78395, 11], .source 39263⟩,
    ⟨[78395], [78395], .contexts []⟩,
    ⟨[78397, 11], [78395], .contexts [
        ⟨7092, false, false, [], [11]⟩,
        ⟨90, false, false, [78395], []⟩,
        ⟨7093, false, false, [], []⟩
      ]⟩,
    ⟨[78399], [78397, 1], .source 39264⟩,
    ⟨[78397], [78397], .contexts []⟩,
    ⟨[78399, 1], [78397], .contexts [
        ⟨7095, false, false, [], [1]⟩,
        ⟨18, false, false, [78397], []⟩,
        ⟨7096, false, false, [], []⟩
      ]⟩,
    ⟨[78401], [78399, 13], .source 39265⟩,
    ⟨[78399, 13], [78401], .contexts [
        ⟨7098, true, false, [], []⟩
      ]⟩,
    ⟨[78399], [78399], .contexts []⟩,
    ⟨[78401, 13], [78399], .contexts [
        ⟨7099, true, false, [], [13]⟩,
        ⟨98, false, false, [78399], []⟩,
        ⟨7100, false, false, [], []⟩
      ]⟩,
    ⟨[78403], [78401, 15], .source 39266⟩,
    ⟨[78401, 15], [78403], .contexts [
        ⟨7102, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 111. -/
def y322TCContextRaw111 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78401], [78401], .contexts []⟩,
    ⟨[78403], [78403], .contexts []⟩,
    ⟨[78395], [78395], .contexts []⟩,
    ⟨[78393], [78393], .contexts []⟩,
    ⟨[78391], [78391], .contexts []⟩,
    ⟨[78401, 13, 1, 11, 9, 1], [78391], .contexts [
        ⟨7101, false, false, [], [1, 11, 9, 1]⟩,
        ⟨7100, false, false, [], [1, 11, 9, 1]⟩,
        ⟨7100, false, false, [], [1, 11, 9, 1]⟩,
        ⟨7097, false, false, [], [11, 9, 1]⟩,
        ⟨7096, false, false, [], [11, 9, 1]⟩,
        ⟨7096, false, false, [], [11, 9, 1]⟩,
        ⟨7094, false, false, [], [9, 1]⟩,
        ⟨7106, false, false, [], [9, 1]⟩,
        ⟨7093, false, false, [], [9, 1]⟩,
        ⟨7093, false, false, [], [9, 1]⟩,
        ⟨7091, false, false, [], [1]⟩,
        ⟨7107, false, false, [], [1]⟩,
        ⟨7090, false, false, [], [1]⟩,
        ⟨7090, false, false, [], [1]⟩,
        ⟨7088, false, false, [], []⟩,
        ⟨7108, false, false, [], []⟩,
        ⟨7087, false, false, [], []⟩,
        ⟨7087, false, false, [], []⟩
      ]⟩,
    ⟨[78391, 5], [78389], .contexts [
        ⟨7084, false, false, [], []⟩
      ]⟩,
    ⟨[78387], [78387], .contexts []⟩,
    ⟨[78385], [78385], .contexts []⟩,
    ⟨[78383], [78383], .contexts []⟩,
    ⟨[78381], [78381], .contexts []⟩,
    ⟨[78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13], [78381], .contexts [
        ⟨7109, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨7110, false, false, [], [3, 1, 15, 13]⟩,
        ⟨7083, false, false, [], [3, 1, 15, 13]⟩,
        ⟨7083, false, false, [], [3, 1, 15, 13]⟩,
        ⟨7081, false, false, [], [1, 15, 13]⟩,
        ⟨7111, false, false, [], [1, 15, 13]⟩,
        ⟨7080, false, false, [], [1, 15, 13]⟩,
        ⟨7080, false, false, [], [1, 15, 13]⟩,
        ⟨7078, false, false, [], [15, 13]⟩,
        ⟨7112, false, false, [], [15, 13]⟩,
        ⟨7077, false, false, [], [15, 13]⟩,
        ⟨7077, false, false, [], [15, 13]⟩,
        ⟨7075, false, false, [], [13]⟩,
        ⟨7113, false, false, [], [13]⟩,
        ⟨7074, false, false, [], [13]⟩,
        ⟨7074, false, false, [], [13]⟩,
        ⟨7072, false, false, [], []⟩,
        ⟨7114, false, false, [], []⟩,
        ⟨7071, false, false, [], []⟩,
        ⟨7071, false, false, [], []⟩
      ]⟩,
    ⟨[78377, 9], [78375], .contexts [
        ⟨7061, false, false, [], []⟩
      ]⟩,
    ⟨[78375], [78375], .contexts []⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5
    ], [78371], .contexts [
        ⟨7115, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨7069, false, false, [], [11, 9, 1, 5]⟩,
        ⟨7068, false, false, [], [11, 9, 1, 5]⟩,
        ⟨7068, false, false, [], [11, 9, 1, 5]⟩,
        ⟨7065, false, false, [], [9, 1, 5]⟩,
        ⟨7064, false, false, [], [9, 1, 5]⟩,
        ⟨7064, false, false, [], [9, 1, 5]⟩,
        ⟨7116, false, false, [], [1, 5]⟩,
        ⟨7117, false, false, [], [1, 5]⟩,
        ⟨7060, false, false, [], [1, 5]⟩,
        ⟨7060, false, false, [], [1, 5]⟩,
        ⟨7058, false, false, [], [5]⟩,
        ⟨7057, false, false, [], [5]⟩,
        ⟨7057, false, false, [], [5]⟩,
        ⟨7055, false, false, [], []⟩,
        ⟨7054, false, false, [], []⟩,
        ⟨7054, false, false, [], []⟩
      ]⟩,
    ⟨[78369], [78369], .contexts []⟩,
    ⟨[78365], [78365], .contexts []⟩,
    ⟨[78363], [78363], .contexts []⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13
    ], [78363], .contexts [
        ⟨7118, false, false, [], [3, 1, 15, 13]⟩,
        ⟨7051, true, false, [], [3, 1, 15, 13]⟩,
        ⟨35, false, false, [78369], [1, 15, 13]⟩,
        ⟨7052, false, false, [], [1, 15, 13]⟩,
        ⟨7119, false, false, [], [1, 15, 13]⟩,
        ⟨7052, false, false, [], [1, 15, 13]⟩,
        ⟨7052, false, false, [], [1, 15, 13]⟩,
        ⟨7048, true, false, [], [1, 15, 13]⟩,
        ⟨18, false, false, [78367], [15, 13]⟩,
        ⟨7049, false, false, [], [15, 13]⟩,
        ⟨7049, false, false, [], [15, 13]⟩,
        ⟨7049, false, false, [], [15, 13]⟩,
        ⟨7045, true, false, [], [15, 13]⟩,
        ⟨3, false, false, [78365], [13]⟩,
        ⟨7046, false, false, [], [13]⟩,
        ⟨7120, false, false, [], [13]⟩,
        ⟨7046, false, false, [], [13]⟩,
        ⟨7046, false, false, [], [13]⟩,
        ⟨7042, true, false, [], [13]⟩,
        ⟨98, false, false, [78363], []⟩,
        ⟨7043, false, false, [], []⟩,
        ⟨7121, false, false, [], []⟩,
        ⟨7043, false, false, [], []⟩,
        ⟨7043, false, false, [], []⟩
      ]⟩,
    ⟨[78361], [78361], .contexts []⟩,
    ⟨[78359], [78359], .contexts []⟩,
    ⟨[78357], [78357], .contexts []⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [78355], .contexts [
        ⟨7122, false, false, [], [1, 11, 9, 1]⟩,
        ⟨7039, true, false, [], [1, 11, 9, 1]⟩,
        ⟨18, false, false, [78361], [11, 9, 1]⟩,
        ⟨7040, false, false, [], [11, 9, 1]⟩,
        ⟨7123, false, false, [], [11, 9, 1]⟩,
        ⟨7040, false, false, [], [11, 9, 1]⟩,
        ⟨7040, false, false, [], [11, 9, 1]⟩,
        ⟨7036, true, false, [], [11, 9, 1]⟩,
        ⟨90, false, false, [78359], [9, 1]⟩,
        ⟨7037, false, false, [], [9, 1]⟩,
        ⟨7124, false, false, [], [9, 1]⟩,
        ⟨7037, false, false, [], [9, 1]⟩,
        ⟨7037, false, false, [], [9, 1]⟩,
        ⟨7033, true, false, [], [9, 1]⟩,
        ⟨76, false, false, [78357], [1]⟩,
        ⟨7034, false, false, [], [1]⟩,
        ⟨7125, false, false, [], [1]⟩,
        ⟨7034, false, false, [], [1]⟩,
        ⟨7034, false, false, [], [1]⟩,
        ⟨7030, true, false, [], [1]⟩,
        ⟨18, false, false, [78355], []⟩,
        ⟨7031, false, false, [], []⟩,
        ⟨7031, false, false, [], []⟩,
        ⟨7031, false, false, [], []⟩
      ]⟩,
    ⟨[78353], [78353], .contexts []⟩,
    ⟨[78349], [78349], .contexts []⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15
    ], [78347], .contexts [
        ⟨7126, false, false, [], [5, 3, 1, 15]⟩,
        ⟨7027, true, false, [], [5, 3, 1, 15]⟩,
        ⟨49, false, false, [78353], [3, 1, 15]⟩,
        ⟨7028, false, false, [], [3, 1, 15]⟩,
        ⟨7127, false, false, [], [3, 1, 15]⟩,
        ⟨7028, false, false, [], [3, 1, 15]⟩,
        ⟨7028, false, false, [], [3, 1, 15]⟩,
        ⟨7024, true, false, [], [3, 1, 15]⟩,
        ⟨35, false, false, [78351], [1, 15]⟩,
        ⟨7025, false, false, [], [1, 15]⟩,
        ⟨7025, false, false, [], [1, 15]⟩,
        ⟨7025, false, false, [], [1, 15]⟩,
        ⟨7021, true, false, [], [1, 15]⟩,
        ⟨18, false, false, [78349], [15]⟩,
        ⟨7022, false, false, [], [15]⟩,
        ⟨7128, false, false, [], [15]⟩,
        ⟨7022, false, false, [], [15]⟩,
        ⟨7022, false, false, [], [15]⟩,
        ⟨7018, true, false, [], [15]⟩,
        ⟨3, false, false, [78347], []⟩,
        ⟨7019, false, false, [], []⟩,
        ⟨7019, false, false, [], []⟩,
        ⟨7019, false, false, [], []⟩
      ]⟩,
    ⟨[78345], [78345], .contexts []⟩,
    ⟨[78343], [78343], .contexts []⟩,
    ⟨[78339], [78339], .contexts []⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9
    ], [78339], .contexts [
        ⟨7129, false, false, [], [13, 1, 11, 9]⟩,
        ⟨7015, true, false, [], [13, 1, 11, 9]⟩,
        ⟨98, false, false, [78345], [1, 11, 9]⟩,
        ⟨7016, false, false, [], [1, 11, 9]⟩,
        ⟨7130, false, false, [], [1, 11, 9]⟩,
        ⟨7016, false, false, [], [1, 11, 9]⟩,
        ⟨7016, false, false, [], [1, 11, 9]⟩,
        ⟨7012, true, false, [], [1, 11, 9]⟩,
        ⟨18, false, false, [78343], [11, 9]⟩,
        ⟨7013, false, false, [], [11, 9]⟩,
        ⟨7131, false, false, [], [11, 9]⟩,
        ⟨7013, false, false, [], [11, 9]⟩,
        ⟨7013, false, false, [], [11, 9]⟩,
        ⟨7009, true, false, [], [11, 9]⟩,
        ⟨90, false, false, [78341], [9]⟩,
        ⟨7010, false, false, [], [9]⟩,
        ⟨7010, false, false, [], [9]⟩,
        ⟨7010, false, false, [], [9]⟩,
        ⟨7006, true, false, [], [9]⟩,
        ⟨76, false, false, [78339], []⟩,
        ⟨7007, false, false, [], []⟩,
        ⟨7132, false, false, [], []⟩,
        ⟨7007, false, false, [], []⟩,
        ⟨7007, false, false, [], []⟩
      ]⟩,
    ⟨[78339, 1], [78337], .contexts [
        ⟨7004, false, false, [], []⟩
      ]⟩,
    ⟨[78337], [78337], .contexts []⟩,
    ⟨[78335], [78335], .contexts []⟩,
    ⟨[78333], [78333], .contexts []⟩,
    ⟨[78331], [78331], .contexts []⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15
    ], [78329], .contexts [
        ⟨7133, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨7134, false, false, [], [5, 3, 1, 15]⟩,
        ⟨7135, false, false, [], [5, 3, 1, 15]⟩,
        ⟨7003, false, false, [], [5, 3, 1, 15]⟩,
        ⟨7003, false, false, [], [5, 3, 1, 15]⟩,
        ⟨6999, true, false, [], [5, 3, 1, 15]⟩,
        ⟨49, false, false, [78335], [3, 1, 15]⟩,
        ⟨7000, false, false, [], [3, 1, 15]⟩,
        ⟨7136, false, false, [], [3, 1, 15]⟩,
        ⟨7000, false, false, [], [3, 1, 15]⟩,
        ⟨7000, false, false, [], [3, 1, 15]⟩,
        ⟨6996, true, false, [], [3, 1, 15]⟩,
        ⟨35, false, false, [78333], [1, 15]⟩,
        ⟨6997, false, false, [], [1, 15]⟩,
        ⟨7137, false, false, [], [1, 15]⟩,
        ⟨6997, false, false, [], [1, 15]⟩,
        ⟨6997, false, false, [], [1, 15]⟩,
        ⟨6993, true, false, [], [1, 15]⟩,
        ⟨18, false, false, [78331], [15]⟩,
        ⟨6994, false, false, [], [15]⟩,
        ⟨7138, false, false, [], [15]⟩,
        ⟨6994, false, false, [], [15]⟩,
        ⟨6994, false, false, [], [15]⟩,
        ⟨6990, true, false, [], [15]⟩,
        ⟨3, false, false, [78329], []⟩,
        ⟨6991, false, false, [], []⟩,
        ⟨6991, false, false, [], []⟩,
        ⟨6991, false, false, [], []⟩
      ]⟩,
    ⟨[78321], [78321], .contexts []⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9
    ], [78321], .contexts [
        ⟨7139, false, false, [], [13, 1, 11, 9]⟩,
        ⟨6987, true, false, [], [13, 1, 11, 9]⟩,
        ⟨98, false, false, [78327], [1, 11, 9]⟩,
        ⟨6988, false, false, [], [1, 11, 9]⟩,
        ⟨6988, false, false, [], [1, 11, 9]⟩,
        ⟨6988, false, false, [], [1, 11, 9]⟩,
        ⟨6984, true, false, [], [1, 11, 9]⟩,
        ⟨18, false, false, [78325], [11, 9]⟩,
        ⟨6985, false, false, [], [11, 9]⟩,
        ⟨6985, false, false, [], [11, 9]⟩,
        ⟨6985, false, false, [], [11, 9]⟩,
        ⟨6981, true, false, [], [11, 9]⟩,
        ⟨90, false, false, [78323], [9]⟩,
        ⟨6982, false, false, [], [9]⟩,
        ⟨6982, false, false, [], [9]⟩,
        ⟨6982, false, false, [], [9]⟩,
        ⟨6978, true, false, [], [9]⟩,
        ⟨76, false, false, [78321], []⟩,
        ⟨6979, false, false, [], []⟩,
        ⟨7140, false, false, [], []⟩,
        ⟨6979, false, false, [], []⟩,
        ⟨6979, false, false, [], []⟩
      ]⟩,
    ⟨[78319], [78319], .contexts []⟩,
    ⟨[78317], [78317], .contexts []⟩,
    ⟨[78315], [78315], .contexts []⟩,
    ⟨[78313], [78313], .contexts []⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [78313], .contexts [
        ⟨7141, false, false, [], [1, 5, 3, 1]⟩,
        ⟨6975, true, false, [], [1, 5, 3, 1]⟩,
        ⟨18, false, false, [78319], [5, 3, 1]⟩,
        ⟨6976, false, false, [], [5, 3, 1]⟩,
        ⟨7142, false, false, [], [5, 3, 1]⟩,
        ⟨6976, false, false, [], [5, 3, 1]⟩,
        ⟨6976, false, false, [], [5, 3, 1]⟩,
        ⟨6972, true, false, [], [5, 3, 1]⟩,
        ⟨49, false, false, [78317], [3, 1]⟩,
        ⟨6973, false, false, [], [3, 1]⟩,
        ⟨7143, false, false, [], [3, 1]⟩,
        ⟨6973, false, false, [], [3, 1]⟩,
        ⟨6973, false, false, [], [3, 1]⟩,
        ⟨6969, true, false, [], [3, 1]⟩,
        ⟨35, false, false, [78315], [1]⟩,
        ⟨6970, false, false, [], [1]⟩,
        ⟨7144, false, false, [], [1]⟩,
        ⟨6970, false, false, [], [1]⟩,
        ⟨6970, false, false, [], [1]⟩,
        ⟨6966, true, false, [], [1]⟩,
        ⟨18, false, false, [78313], []⟩,
        ⟨6967, false, false, [], []⟩,
        ⟨7145, false, false, [], []⟩,
        ⟨6967, false, false, [], []⟩,
        ⟨6967, false, false, [], []⟩
      ]⟩,
    ⟨[78305], [78305], .contexts []⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9
    ], [78303], .contexts [
        ⟨7146, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨6964, false, false, [], [13, 1, 11, 9]⟩,
        ⟨6963, false, false, [], [13, 1, 11, 9]⟩,
        ⟨6963, false, false, [], [13, 1, 11, 9]⟩,
        ⟨6960, false, false, [], [1, 11, 9]⟩,
        ⟨6959, false, false, [], [1, 11, 9]⟩,
        ⟨6959, false, false, [], [1, 11, 9]⟩,
        ⟨6955, true, false, [], [1, 11, 9]⟩,
        ⟨18, false, false, [78307], [11, 9]⟩,
        ⟨6956, false, false, [], [11, 9]⟩,
        ⟨6956, false, false, [], [11, 9]⟩,
        ⟨6956, false, false, [], [11, 9]⟩,
        ⟨6953, false, false, [], [9]⟩,
        ⟨7147, false, false, [], [9]⟩,
        ⟨6952, false, false, [], [9]⟩,
        ⟨6952, false, false, [], [9]⟩,
        ⟨6948, true, false, [], [9]⟩,
        ⟨76, false, false, [78303], []⟩,
        ⟨6949, false, false, [], []⟩,
        ⟨6949, false, false, [], []⟩,
        ⟨6949, false, false, [], []⟩
      ]⟩,
    ⟨[78301], [78301], .contexts []⟩,
    ⟨[78299], [78299], .contexts []⟩,
    ⟨[78297], [78297], .contexts []⟩,
    ⟨[78295], [78295], .contexts []⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1
    ], [78295], .contexts [
        ⟨7148, false, false, [], [1, 5, 3, 1]⟩,
        ⟨6945, true, false, [], [1, 5, 3, 1]⟩,
        ⟨18, false, false, [78301], [5, 3, 1]⟩,
        ⟨6946, false, false, [], [5, 3, 1]⟩,
        ⟨7149, false, false, [], [5, 3, 1]⟩,
        ⟨6946, false, false, [], [5, 3, 1]⟩,
        ⟨6946, false, false, [], [5, 3, 1]⟩,
        ⟨6942, true, false, [], [5, 3, 1]⟩,
        ⟨49, false, false, [78299], [3, 1]⟩,
        ⟨6943, false, false, [], [3, 1]⟩,
        ⟨7150, false, false, [], [3, 1]⟩,
        ⟨6943, false, false, [], [3, 1]⟩,
        ⟨6943, false, false, [], [3, 1]⟩,
        ⟨6940, false, false, [], [1]⟩,
        ⟨7151, false, false, [], [1]⟩,
        ⟨6939, false, false, [], [1]⟩,
        ⟨6939, false, false, [], [1]⟩,
        ⟨6935, true, false, [], [1]⟩,
        ⟨18, false, false, [78295], []⟩,
        ⟨6936, false, false, [], []⟩,
        ⟨7152, false, false, [], []⟩,
        ⟨6936, false, false, [], []⟩,
        ⟨6936, false, false, [], []⟩
      ]⟩,
    ⟨[78293], [78293], .contexts []⟩,
    ⟨[78291], [78291], .contexts []⟩,
    ⟨[78291, 1], [78289], .contexts [
        ⟨6927, true, false, [], [1]⟩,
        ⟨18, false, false, [78289], []⟩,
        ⟨6919, false, false, [], []⟩
      ]⟩,
    ⟨[78287], [78287], .contexts []⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [78287], .contexts [
        ⟨7153, false, false, [], [15, 13, 1, 11]⟩,
        ⟨6932, true, false, [], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [78293], [13, 1, 11]⟩,
        ⟨6933, false, false, [], [13, 1, 11]⟩,
        ⟨7154, false, false, [], [13, 1, 11]⟩,
        ⟨6933, false, false, [], [13, 1, 11]⟩,
        ⟨6933, false, false, [], [13, 1, 11]⟩,
        ⟨6929, true, false, [], [13, 1, 11]⟩,
        ⟨98, false, false, [78291], [1, 11]⟩,
        ⟨6930, false, false, [], [1, 11]⟩,
        ⟨7155, false, false, [], [1, 11]⟩,
        ⟨6930, false, false, [], [1, 11]⟩,
        ⟨6930, false, false, [], [1, 11]⟩,
        ⟨7156, false, false, [], [11]⟩,
        ⟨6918, false, false, [], [11]⟩,
        ⟨6919, false, false, [], [11]⟩,
        ⟨6919, false, false, [], [11]⟩,
        ⟨6917, false, false, [], []⟩,
        ⟨7157, false, false, [], []⟩,
        ⟨6916, false, false, [], []⟩,
        ⟨6916, false, false, [], []⟩
      ]⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3
    ], [555, 78281], .contexts [
        ⟨7158, false, false, [], [9, 1, 5, 3]⟩,
        ⟨6921, false, false, [], [1, 5, 3]⟩,
        ⟨6899, false, false, [], [1, 5, 3]⟩,
        ⟨6900, false, false, [], [1, 5, 3]⟩,
        ⟨6900, false, false, [], [1, 5, 3]⟩,
        ⟨6901, true, false, [], [1, 5, 3]⟩,
        ⟨256, false, false, [78283], [5, 3]⟩,
        ⟨257, false, false, [78283], [5, 3]⟩,
        ⟨6902, false, false, [], [5, 5, 3]⟩,
        ⟨6898, false, false, [555], [5, 3]⟩,
        ⟨6903, false, false, [], [5, 3]⟩,
        ⟨6904, false, false, [], [5, 3]⟩,
        ⟨6905, false, false, [555], [5, 3]⟩,
        ⟨6851, true, false, [], [78285, 5, 3]⟩,
        ⟨6903, false, false, [], [5, 3]⟩,
        ⟨6904, false, false, [], [5, 3]⟩,
        ⟨6904, false, false, [], [5, 3]⟩,
        ⟨6898, true, false, [555], [5, 3]⟩,
        ⟨49, false, false, [555, 78283], [3]⟩,
        ⟨6882, false, false, [555], [3]⟩,
        ⟨6888, false, false, [], [3]⟩,
        ⟨6889, false, false, [], [3]⟩,
        ⟨6890, false, false, [], [3]⟩,
        ⟨6881, true, false, [555], [3]⟩,
        ⟨35, false, false, [555, 78281], []⟩,
        ⟨6874, false, false, [555], []⟩,
        ⟨6884, false, false, [], []⟩,
        ⟨6885, false, false, [], []⟩
      ]⟩,
    ⟨[1493], [555, 275], .source 811⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11
    ], [1493, 77255], .contexts [
        ⟨7159, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨6887, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨6873, false, false, [555], [15, 13, 1, 11]⟩,
        ⟨6863, false, false, [], [15, 13, 1, 11]⟩,
        ⟨6864, false, false, [], [15, 13, 1, 11]⟩,
        ⟨6865, false, false, [], [15, 13, 1, 11]⟩,
        ⟨6859, true, false, [555], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [555, 78277], [13, 1, 11]⟩,
        ⟨6845, false, false, [555], [13, 1, 11]⟩,
        ⟨6847, false, false, [], [13, 1, 11]⟩,
        ⟨6848, false, false, [], [13, 1, 11]⟩,
        ⟨6849, false, false, [], [13, 1, 11]⟩,
        ⟨6844, true, false, [555], [13, 1, 11]⟩,
        ⟨98, false, false, [555, 77253], [1, 11]⟩,
        ⟨1199, false, false, [555], [1, 11]⟩,
        ⟨2872, false, false, [], [1, 11]⟩,
        ⟨2873, false, false, [], [1, 11]⟩,
        ⟨1720, false, false, [555], [11]⟩,
        ⟨7160, true, false, [], [77253, 11]⟩,
        ⟨1198, false, false, [1493], []⟩
      ]⟩,
    ⟨[1495], [1493, 245], .source 812⟩,
    ⟨[77257], [277, 77255], .contexts [
        ⟨1734, false, false, [], []⟩
      ]⟩,
    ⟨[1497], [1495, 277], .source 813⟩,
    ⟨[1499], [1497, 1469], .source 814⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [1499, 77127], .contexts [
        ⟨7161, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨1741, false, false, [1493], [1, 5, 3, 1]⟩,
        ⟨7162, true, false, [], [77255, 1, 5, 3, 1]⟩,
        ⟨1201, false, false, [1495], [5, 3, 1]⟩,
        ⟨7163, false, false, [1495], [5, 3, 1]⟩,
        ⟨7164, true, false, [], [77255, 5, 3, 1]⟩,
        ⟨6772, false, false, [1497], [3, 1]⟩,
        ⟨7165, true, false, [], [78259, 3, 1]⟩,
        ⟨6748, false, false, [1499], [1]⟩,
        ⟨439, false, false, [1499], []⟩
      ]⟩,
    ⟨[1501], [1499, 539], .source 815⟩]

/-- Exact literal claimed equations and contextual derivations, block 112. -/
def y322TCContextRaw112 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1503], [1501, 269], .source 816⟩,
    ⟨[1505], [1503, 261], .source 817⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9
    ], [1505, 679, 77601], .contexts [
        ⟨7166, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨4844, false, false, [1499], [13, 1, 11, 9]⟩,
        ⟨7167, true, false, [], [77863, 13, 1, 11, 9]⟩,
        ⟨4838, false, false, [1501], [1, 11, 9]⟩,
        ⟨7168, true, false, [], [77863, 1, 11, 9]⟩,
        ⟨4846, false, false, [1503], [11, 9]⟩,
        ⟨4857, false, false, [1503], [9]⟩,
        ⟨7169, true, false, [], [77337, 9]⟩,
        ⟨3331, false, false, [1505], []⟩
      ]⟩,
    ⟨[1507], [1505, 679], .source 818⟩,
    ⟨[1509], [1507, 639], .source 819⟩,
    ⟨[1511], [1509, 625], .source 820⟩,
    ⟨[1513], [1511, 295], .source 821⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [1513, 77209, 15], .contexts [
        ⟨7170, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨7171, true, false, [], [77601, 1, 5, 3, 1, 15]⟩,
        ⟨3149, false, false, [1507], [5, 3, 1, 15]⟩,
        ⟨3274, false, false, [1507], [3, 1, 15]⟩,
        ⟨7172, true, false, [], [77603, 3, 1, 15]⟩,
        ⟨3251, false, false, [1509], [1, 15]⟩,
        ⟨7173, true, false, [], [77241, 1, 15]⟩,
        ⟨1863, false, false, [1511], [15]⟩,
        ⟨7174, true, false, [], [77209, 15]⟩
      ]⟩,
    ⟨[1515], [1513, 293], .source 822⟩,
    ⟨[1517], [1515, 31], .source 823⟩,
    ⟨[1519], [1517, 245], .source 824⟩,
    ⟨[1521], [1519, 277], .source 825⟩,
    ⟨[
      78401, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9
    ], [1521, 77365], .contexts [
        ⟨7175, false, false, [], [13, 1, 11, 9]⟩,
        ⟨1878, false, false, [1513], [13, 1, 11, 9]⟩,
        ⟨7176, true, false, [], [77245, 13, 1, 11, 9]⟩,
        ⟨2023, false, false, [1515], [1, 11, 9]⟩,
        ⟨2029, false, false, [1515], [11, 9]⟩,
        ⟨740, true, false, [1515], [77365, 11, 9]⟩,
        ⟨7177, true, false, [], [77365, 11, 9]⟩,
        ⟨2039, false, false, [1517], [9]⟩,
        ⟨7178, true, false, [], [77365, 9]⟩,
        ⟨2035, false, false, [1519], []⟩,
        ⟨7179, true, false, [], [77365]⟩
      ]⟩,
    ⟨[1523], [1521, 31], .source 826⟩,
    ⟨[1525], [1523, 295], .source 827⟩,
    ⟨[1525, 78015], [1525, 78015], .contexts []⟩,
    ⟨[1525, 78015], [1525, 78015], .contexts []⟩,
    ⟨[15, 1], [
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2
    ], .contexts [
        ⟨764, false, false, [12, 0, 10, 8, 0, 4, 2, 0], [
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14, 12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0,
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4, 2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0,
          14, 12, 0, 10, 8, 0, 4, 2
        ]⟩
      ]⟩,
    ⟨[
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4
    ], [
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 4
    ], .contexts [
        ⟨190, false, false, [], [
          10, 8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0,
          4
        ]⟩,
        ⟨91, false, false, [13, 1], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨77, false, false, [13, 1, 11], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨19, false, false, [13, 1, 11, 9], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨50, false, false, [13, 1, 11, 9, 1], [2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨36, false, false, [13, 1, 11, 9, 1, 5], [0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨19, false, false, [13, 1, 11, 9, 1, 5, 3], [14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨20, false, false, [13, 1, 11, 9, 1, 5, 3, 1], [12, 0, 10, 8, 0, 4]⟩,
        ⟨108, false, false, [13, 1, 11, 9, 1, 5, 3, 1, 15], [0, 10, 8, 0, 4]⟩,
        ⟨19, false, false, [13, 1, 11, 9, 1, 5, 3, 1, 15, 13], [10, 8, 0, 4]⟩,
        ⟨91, false, false, [13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1], [8, 0, 4]⟩,
        ⟨77, false, false, [13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11], [0, 4]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9
        ], [4]⟩
      ]⟩,
    ⟨[
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14
    ], [
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 14
    ], .contexts [
        ⟨7186, false, false, [], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨50, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨36, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨20, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨108, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨91, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14]⟩,
        ⟨77, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14]⟩,
        ⟨50, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14]⟩,
        ⟨36, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3
        ], [14]⟩
      ]⟩,
    ⟨[
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10
    ], [
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 10
    ], .contexts [
        ⟨7187, false, false, [], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨20, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨108, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨91, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨77, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨50, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10]⟩,
        ⟨36, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10]⟩,
        ⟨20, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10]⟩,
        ⟨108, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13
        ], [10]⟩
      ]⟩,
    ⟨[
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4
    ], [
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 4
    ], .contexts [
        ⟨7188, false, false, [], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨91, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨77, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨50, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨36, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨20, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4]⟩,
        ⟨108, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4]⟩,
        ⟨91, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4]⟩,
        ⟨77, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9
        ], [4]⟩
      ]⟩,
    ⟨[
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14
    ], [
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 14
    ], .contexts [
        ⟨7189, false, false, [], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨50, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨36, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨20, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨108, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14]⟩,
        ⟨91, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14]⟩,
        ⟨77, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14]⟩,
        ⟨50, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14]⟩,
        ⟨36, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3
        ], [14]⟩
      ]⟩,
    ⟨[
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10
    ], [
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 10
    ], .contexts [
        ⟨7190, false, false, [], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨20, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1
        ], [12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨108, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15
        ], [0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13
        ], [10, 8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨91, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨77, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10]⟩,
        ⟨50, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10]⟩,
        ⟨36, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10]⟩,
        ⟨20, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10]⟩,
        ⟨108, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13
        ], [10]⟩
      ]⟩,
    ⟨[
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4
    ], [
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 4
    ], .contexts [
        ⟨7191, false, false, [], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨91, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1
        ], [8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨77, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11
        ], [0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9
        ], [4, 2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨50, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1
        ], [2, 0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨36, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5
        ], [0, 14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3
        ], [14, 12, 0, 10, 8, 0, 4]⟩,
        ⟨20, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1
        ], [12, 0, 10, 8, 0, 4]⟩,
        ⟨108, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15
        ], [0, 10, 8, 0, 4]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13
        ], [10, 8, 0, 4]⟩,
        ⟨91, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
        ], [8, 0, 4]⟩,
        ⟨77, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
        ], [0, 4]⟩,
        ⟨19, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9
        ], [4]⟩
      ]⟩,
    ⟨[
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2, 0, 14, 12, 0, 10, 8, 0, 4,
      2, 0, 14, 12, 0, 10, 8, 0, 4, 2, 0, 14,
      12, 0, 10, 8, 0, 4, 2, 0, 14, 12, 0, 10,
      8, 0, 4, 2
    ], [
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3
    ], .contexts [
        ⟨7192, false, false, [], [2]⟩,
        ⟨50, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1
        ], [2]⟩,
        ⟨36, false, false, [
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
          3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
          13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
          9, 1, 5
        ], []⟩
      ]⟩,
    ⟨[78403, 1], [78403, 1], .contexts []⟩,
    ⟨[78403, 1], [1525, 78015], .contexts [
        ⟨7194, false, false, [], []⟩,
        ⟨7105, true, false, [], [1]⟩,
        ⟨7105, true, false, [], [1]⟩,
        ⟨7103, true, false, [], [1]⟩,
        ⟨7185, false, false, [78401], []⟩,
        ⟨7193, false, false, [78401], []⟩,
        ⟨7180, false, false, [], [1, 5, 3]⟩,
        ⟨2029, false, false, [1521], [5, 3]⟩,
        ⟨740, true, false, [1521], [77365, 5, 3]⟩,
        ⟨7181, true, false, [], [77365, 5, 3]⟩,
        ⟨5864, false, false, [1523], [3]⟩,
        ⟨7182, true, false, [], [78013, 3]⟩,
        ⟨5882, false, false, [1525], []⟩,
        ⟨7183, false, false, [], []⟩,
        ⟨7184, false, false, [], []⟩,
        ⟨5889, false, false, [1525], []⟩,
        ⟨24, true, false, [], [1525, 78015]⟩
      ]⟩,
    ⟨[1527], [1524], .source 828⟩,
    ⟨[78015, 1], [1527, 78403], .contexts [
        ⟨7195, true, false, [1524], [1]⟩,
        ⟨18, false, false, [1524, 78403], []⟩,
        ⟨7196, true, false, [], [78403]⟩
      ]⟩,
    ⟨[1529], [1525, 305], .source 829⟩,
    ⟨[78401, 1], [78401, 1], .contexts []⟩,
    ⟨[78401, 1], [1529, 78015], .contexts [
        ⟨7199, false, false, [], []⟩,
        ⟨7104, true, false, [], [1]⟩,
        ⟨7104, true, false, [], [1]⟩,
        ⟨7104, true, false, [], [1]⟩,
        ⟨3, true, false, [78401], [1]⟩,
        ⟨7103, false, false, [], [15, 1]⟩,
        ⟨17, false, false, [78403], []⟩,
        ⟨21, false, false, [78403], []⟩,
        ⟨7194, false, false, [], [15]⟩,
        ⟨7195, false, false, [], [15]⟩,
        ⟨7183, false, false, [], [15]⟩,
        ⟨7184, false, false, [], [15]⟩,
        ⟨7184, false, false, [], [15]⟩,
        ⟨5885, true, false, [1525], [15]⟩,
        ⟨245, false, false, [1525, 78013], []⟩,
        ⟨246, false, false, [1525, 78013], []⟩,
        ⟨5878, false, false, [1525], [3]⟩,
        ⟨5880, false, false, [1525], [3]⟩,
        ⟨5876, false, false, [1525], [3]⟩,
        ⟨5877, false, false, [1525], [3]⟩,
        ⟨5877, false, false, [1525], [3]⟩,
        ⟨5882, false, false, [1525, 305], []⟩,
        ⟨5889, false, false, [1525, 305], []⟩,
        ⟨5879, true, false, [1525], [78015]⟩,
        ⟨7198, true, false, [], [78015]⟩
      ]⟩,
    ⟨[1529], [1529], .contexts []⟩,
    ⟨[1529], [1529], .contexts []⟩,
    ⟨[78401, 1], [1529, 78015], .contexts [
        ⟨7200, false, false, [], []⟩,
        ⟨5889, false, false, [1529], []⟩,
        ⟨7202, true, false, [], [78015]⟩,
        ⟨7201, true, false, [], [78015]⟩,
        ⟨24, true, false, [], [1529, 78015]⟩
      ]⟩,
    ⟨[1531], [1528], .source 830⟩,
    ⟨[1527, 78403], [1527, 78403], .contexts []⟩,
    ⟨[1533], [1525, 1531], .source 831⟩,
    ⟨[1529, 78015], [1529, 78015], .contexts []⟩,
    ⟨[1529, 78015], [1529, 78015], .contexts []⟩,
    ⟨[78401, 1], [1529, 78015], .contexts [
        ⟨7199, false, false, [], []⟩,
        ⟨7203, false, false, [], []⟩,
        ⟨7207, false, false, [], []⟩,
        ⟨7208, false, false, [], []⟩,
        ⟨7208, false, false, [], []⟩
      ]⟩,
    ⟨[1535], [1529, 857], .source 832⟩,
    ⟨[78403], [1533, 78401], .contexts [
        ⟨7205, true, false, [1526], []⟩,
        ⟨7205, true, false, [1526], []⟩,
        ⟨7197, true, false, [1526], []⟩,
        ⟨7203, true, false, [1526, 1528], [1]⟩,
        ⟨18, false, false, [1526, 1528, 78401], []⟩,
        ⟨7204, true, false, [1526], [78401]⟩,
        ⟨7196, false, true, [], [1531, 78401]⟩,
        ⟨7206, true, false, [], [78401]⟩
      ]⟩,
    ⟨[1537], [1527, 1533], .source 833⟩,
    ⟨[1539], [1535, 1537], .source 834⟩,
    ⟨[1, 3, 1, 3, 1, 3], [], .contexts [
        ⟨851, false, false, [], []⟩
      ]⟩,
    ⟨[78401], [78401], .contexts []⟩,
    ⟨[1539, 78401, 3], [78401], .contexts [
        ⟨7213, false, false, [], [78401, 3]⟩,
        ⟨7212, false, false, [1535], [78401, 3]⟩,
        ⟨7211, true, false, [1535, 1527], [3]⟩,
        ⟨7197, true, false, [1535], [3]⟩,
        ⟨5882, true, false, [1535], [1, 3]⟩,
        ⟨7210, false, false, [], [78013, 3, 1, 3]⟩,
        ⟨5859, true, false, [1529], [3, 1, 3]⟩,
        ⟨5883, true, false, [1529], [1, 3, 1, 3]⟩,
        ⟨7209, true, false, [], [3, 1, 3, 1, 3]⟩,
        ⟨7214, false, false, [78401], []⟩,
        ⟨7215, false, false, [], []⟩
      ]⟩,
    ⟨[78401], [78401], .contexts []⟩,
    ⟨[1541], [1538], .source 835⟩,
    ⟨[1538], [1538], .contexts []⟩,
    ⟨[1529, 77729], [1529, 77729], .contexts []⟩,
    ⟨[77729, 5], [77729, 5], .contexts []⟩,
    ⟨[1528], [1528], .contexts []⟩,
    ⟨[77729, 5], [1531, 78401], .contexts [
        ⟨7221, false, false, [], []⟩,
        ⟨7220, true, false, [1528], [5]⟩,
        ⟨4292, true, false, [], [5]⟩,
        ⟨5887, true, false, [], [1, 5]⟩,
        ⟨7209, true, false, [1528], [5, 1, 5]⟩,
        ⟨1909, false, false, [1528, 78401], []⟩,
        ⟨7215, false, false, [1528], []⟩,
        ⟨7217, false, false, [1528], []⟩,
        ⟨7222, true, false, [], [78401]⟩,
        ⟨7222, true, false, [], [78401]⟩,
        ⟨7204, true, false, [], [78401]⟩
      ]⟩,
    ⟨[1543], [1529, 149], .source 836⟩,
    ⟨[1545], [1543, 1537], .source 837⟩,
    ⟨[1545, 78401, 7], [78401], .contexts [
        ⟨7225, false, false, [], [78401, 7]⟩,
        ⟨7212, false, false, [1543], [78401, 7]⟩,
        ⟨7211, true, false, [1543, 1527], [7]⟩,
        ⟨7197, true, false, [1543], [7]⟩,
        ⟨7224, false, false, [], [78015, 1, 7]⟩,
        ⟨4184, false, false, [1529], [78015, 1, 7]⟩,
        ⟨5889, true, false, [1529, 149], [1, 7]⟩,
        ⟨5888, true, false, [1529], [1, 7]⟩,
        ⟨226, true, false, [1529, 78013], [1, 7]⟩,
        ⟨225, true, false, [1529, 78013], [1, 7]⟩,
        ⟨5885, false, false, [1529], [7, 1, 7]⟩,
        ⟨7209, true, false, [], [7, 1, 7]⟩,
        ⟨172, false, false, [78401], []⟩,
        ⟨7215, false, false, [], []⟩
      ]⟩,
    ⟨[1547], [1544], .source 838⟩,
    ⟨[1544], [1544], .contexts []⟩,
    ⟨[1555], [1529, 145], .source 842⟩,
    ⟨[1557], [1555, 1537], .source 843⟩,
    ⟨[1557, 78399], [1557, 78399], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 113. -/
def y322TCContextRaw113 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78401, 1, 13, 1, 13, 1, 13], [1557, 78399], .contexts [
        ⟨7209, false, false, [], [13, 1, 13, 1, 13]⟩,
        ⟨5894, false, false, [1529], [1, 13, 1, 13]⟩,
        ⟨4236, false, false, [1529], [13, 1, 13]⟩,
        ⟨7229, true, false, [], [77723, 13, 1, 13]⟩,
        ⟨5894, true, false, [1555], [13, 1, 13]⟩,
        ⟨98, false, false, [1555, 78015], [1, 13]⟩,
        ⟨5884, false, false, [1555], [1, 13]⟩,
        ⟨7197, false, false, [1555], [13]⟩,
        ⟨7211, false, false, [1555, 1527], [13]⟩,
        ⟨7212, true, false, [1555], [78401, 13]⟩,
        ⟨7230, true, false, [], [78401, 13]⟩,
        ⟨7101, false, false, [1557], []⟩,
        ⟨7231, false, false, [], []⟩
      ]⟩,
    ⟨[78401], [1557, 78399], .contexts [
        ⟨7217, false, false, [], []⟩,
        ⟨188, true, false, [78401], []⟩,
        ⟨7232, false, false, [], []⟩
      ]⟩,
    ⟨[1559], [1533, 1557], .source 844⟩,
    ⟨[78403], [1559, 78399], .contexts [
        ⟨7211, false, false, [], []⟩,
        ⟨7233, false, false, [1533], []⟩,
        ⟨7234, true, false, [], [78399]⟩
      ]⟩,
    ⟨[1561], [1556], .source 845⟩,
    ⟨[1563], [1561, 1559], .source 846⟩,
    ⟨[78401], [1557, 78399], .contexts [
        ⟨7233, false, false, [], []⟩,
        ⟨7231, false, false, [], []⟩
      ]⟩,
    ⟨[1565], [1561, 1541], .source 847⟩,
    ⟨[1567], [1565, 1557], .source 848⟩,
    ⟨[1569], [1561, 1529], .source 849⟩,
    ⟨[1561, 1529], [1556, 1529], .contexts [
        ⟨7236, false, false, [], [1529]⟩
      ]⟩,
    ⟨[1571], [1561, 1547], .source 850⟩,
    ⟨[1573], [1571, 1557], .source 851⟩,
    ⟨[1579], [1569, 151], .source 854⟩,
    ⟨[1581], [1578], .source 855⟩,
    ⟨[78395], [1579, 78015], .contexts [
        ⟨7246, false, false, [1580], [78395]⟩,
        ⟨24, false, false, [1580, 1578], [78395]⟩,
        ⟨7106, true, false, [1580, 1578], []⟩,
        ⟨7094, true, false, [1580, 1578], []⟩,
        ⟨7097, true, false, [1580, 1578], [11]⟩,
        ⟨7238, true, false, [1580, 1578, 1556], [1, 11]⟩,
        ⟨7203, false, false, [1580, 1578, 1556], [11]⟩,
        ⟨7207, false, false, [1580, 1578, 1556], [11]⟩,
        ⟨7202, true, false, [1580, 1578, 1556], [78015, 11]⟩,
        ⟨7201, true, false, [1580, 1578, 1556], [78015, 11]⟩,
        ⟨7242, true, false, [1580, 1578], [78015, 11]⟩,
        ⟨7241, true, false, [1580, 1578], [78015, 11]⟩,
        ⟨5893, false, false, [1580, 1578, 1569], []⟩,
        ⟨7245, true, false, [1580, 1578], [78015]⟩,
        ⟨7246, false, true, [], [78015]⟩
      ]⟩,
    ⟨[1583], [1579, 135], .source 856⟩,
    ⟨[1585], [1582], .source 857⟩,
    ⟨[78393], [1583, 78015], .contexts [
        ⟨7249, false, false, [1584], [78393]⟩,
        ⟨24, false, false, [1584, 1582], [78393]⟩,
        ⟨7107, true, false, [1584, 1582], []⟩,
        ⟨7091, true, false, [1584, 1582], []⟩,
        ⟨7247, false, false, [1584, 1582], [9]⟩,
        ⟨5891, false, false, [1584, 1582, 1579], []⟩,
        ⟨7248, true, false, [1584, 1582], [78015]⟩,
        ⟨7249, false, true, [], [78015]⟩
      ]⟩,
    ⟨[1587], [1527, 1559], .source 858⟩,
    ⟨[1589], [1583, 1587], .source 859⟩,
    ⟨[1591], [1588], .source 860⟩,
    ⟨[78399], [1591, 78391], .contexts [
        ⟨7252, false, false, [1588], [78399]⟩,
        ⟨7251, false, false, [1588, 1583], [78399]⟩,
        ⟨7235, true, false, [1588, 1583, 1527], []⟩,
        ⟨7197, true, false, [1588, 1583], []⟩,
        ⟨7250, true, false, [1588], [1]⟩,
        ⟨7088, false, false, [1588], []⟩,
        ⟨7108, false, false, [1588], []⟩,
        ⟨24, true, false, [1588], [78391]⟩,
        ⟨7253, true, false, [], [78391]⟩
      ]⟩,
    ⟨[1593], [1557, 1591], .source 861⟩,
    ⟨[78401], [1593, 78391], .contexts [
        ⟨7238, false, false, [], []⟩,
        ⟨7254, false, false, [1557], []⟩,
        ⟨7255, true, false, [], [78391]⟩
      ]⟩,
    ⟨[1589], [1590], .contexts [
        ⟨7253, true, true, [], []⟩
      ]⟩,
    ⟨[1595], [1589, 1593], .source 862⟩,
    ⟨[78399], [1591, 78391], .contexts [
        ⟨7254, false, false, [], []⟩
      ]⟩,
    ⟨[1597], [1589, 1563], .source 863⟩,
    ⟨[1599], [1597, 1591], .source 864⟩,
    ⟨[1601], [1589, 1567], .source 865⟩,
    ⟨[1603], [1601, 1591], .source 866⟩,
    ⟨[1605], [1589, 1573], .source 867⟩,
    ⟨[1607], [1605, 1591], .source 868⟩,
    ⟨[78391, 7], [1607, 78391], .contexts [
        ⟨7254, true, false, [1590], [7]⟩,
        ⟨7233, true, false, [1590, 1556], [7]⟩,
        ⟨7226, false, false, [1590, 1556, 1544], []⟩,
        ⟨7217, false, false, [1590, 1556, 1544], []⟩,
        ⟨7228, true, false, [1590, 1556], [78401]⟩,
        ⟨7228, true, false, [1590, 1556], [78401]⟩,
        ⟨7227, true, false, [1590, 1556], [78401]⟩,
        ⟨7238, false, false, [1590, 1556, 1547], []⟩,
        ⟨7236, true, false, [1590], [1547, 1557, 78399]⟩,
        ⟨7243, true, false, [1590], [1557, 78399]⟩,
        ⟨7244, true, false, [1590], [78399]⟩,
        ⟨7259, false, false, [1590, 1573], []⟩,
        ⟨7257, true, false, [], [1573, 1591, 78391]⟩,
        ⟨7264, true, false, [], [1591, 78391]⟩,
        ⟨7265, true, false, [], [78391]⟩
      ]⟩,
    ⟨[1613], [1589, 1569], .source 871⟩,
    ⟨[1613, 77729], [1613, 77729], .contexts []⟩,
    ⟨[78389], [1613, 77729], .contexts [
        ⟨7084, true, false, [], []⟩,
        ⟨7259, true, false, [1590], [5]⟩,
        ⟨7233, true, false, [1590, 1556], [5]⟩,
        ⟨7223, true, false, [1590, 1556, 1530], [5]⟩,
        ⟨49, false, false, [1590, 1556, 1530, 77729], []⟩,
        ⟨7204, false, true, [1590, 1556], [77729]⟩,
        ⟨7220, false, false, [1590, 1556], []⟩,
        ⟨7242, true, false, [1590], [77729]⟩,
        ⟨7241, true, false, [1590], [77729]⟩,
        ⟨7257, true, false, [], [1569, 77729]⟩,
        ⟨7267, true, false, [], [77729]⟩,
        ⟨7268, false, false, [], []⟩
      ]⟩,
    ⟨[1613, 77731], [1613, 77731], .contexts []⟩,
    ⟨[1615], [1612], .source 872⟩,
    ⟨[1617], [1613, 293], .source 873⟩,
    ⟨[1619], [1616], .source 874⟩,
    ⟨[78129], [1619, 78385], .contexts [
        ⟨7272, false, false, [1616], [78129]⟩,
        ⟨6278, true, false, [1616, 1613], []⟩,
        ⟨7270, true, false, [1616], [1]⟩,
        ⟨7271, true, true, [1616], [77731, 1]⟩,
        ⟨7270, true, false, [1616, 1614, 1612], [1]⟩,
        ⟨4314, true, false, [1616, 1614], [1]⟩,
        ⟨7269, true, false, [1616, 1614, 1612], [3, 1]⟩,
        ⟨7081, false, false, [1616, 1614, 1612], [1]⟩,
        ⟨7111, false, false, [1616, 1614, 1612], [1]⟩,
        ⟨24, true, false, [1616, 1614, 1612], [78387, 1]⟩,
        ⟨7271, true, false, [1616, 1614], [78387, 1]⟩,
        ⟨7078, false, false, [1616], []⟩,
        ⟨7112, false, false, [1616], []⟩,
        ⟨24, true, false, [1616], [78385]⟩,
        ⟨7273, true, false, [], [78385]⟩
      ]⟩,
    ⟨[1621], [1617, 329], .source 875⟩,
    ⟨[1623], [1620], .source 876⟩,
    ⟨[1623], [1620], .contexts [
        ⟨7276, false, false, [], []⟩
      ]⟩,
    ⟨[1621, 78129, 13], [78381], .contexts [
        ⟨7276, true, true, [], [78129, 13]⟩,
        ⟨7275, false, false, [1622, 1620], [78129, 13]⟩,
        ⟨2046, false, false, [1622, 1620, 1617], [78129, 13]⟩,
        ⟨6279, true, false, [1622, 1620, 1617, 329], [13]⟩,
        ⟨6280, true, false, [1622, 1620, 1617], [13]⟩,
        ⟨246, true, false, [1622, 1620, 1617, 77371], [13]⟩,
        ⟨245, true, false, [1622, 1620, 1617, 77371], [13]⟩,
        ⟨6271, false, false, [1622, 1620, 1617], [15, 13]⟩,
        ⟨7273, true, true, [1622, 1620], [78129, 15, 13]⟩,
        ⟨7274, false, false, [1622, 1620, 1618], [15, 13]⟩,
        ⟨7075, false, false, [1622, 1620], [13]⟩,
        ⟨7113, false, false, [1622, 1620], [13]⟩,
        ⟨24, true, false, [1622, 1620], [78383, 13]⟩,
        ⟨7277, true, false, [1622], [78383, 13]⟩,
        ⟨7072, false, false, [], []⟩
      ]⟩,
    ⟨[1620], [1620], .contexts []⟩,
    ⟨[1603, 78391], [1603, 78391], .contexts []⟩,
    ⟨[78391, 3, 5], [1603, 78391, 5], .contexts [
        ⟨7254, true, false, [1590], [3, 5]⟩,
        ⟨7233, true, false, [1590, 1556], [3, 5]⟩,
        ⟨7216, false, false, [1590, 1556, 1538], [5]⟩,
        ⟨7217, false, false, [1590, 1556, 1538], [5]⟩,
        ⟨7219, true, false, [1590, 1556], [78401, 5]⟩,
        ⟨7219, true, false, [1590, 1556], [78401, 5]⟩,
        ⟨7218, true, false, [1590, 1556], [78401, 5]⟩,
        ⟨7238, false, false, [1590, 1556, 1541], [5]⟩,
        ⟨7236, true, false, [1590], [1541, 1557, 78399, 5]⟩,
        ⟨7239, true, false, [1590], [1557, 78399, 5]⟩,
        ⟨7240, true, false, [1590], [78399, 5]⟩,
        ⟨7259, false, false, [1590, 1567], [5]⟩,
        ⟨7257, true, false, [], [1567, 1591, 78391, 5]⟩,
        ⟨7262, true, false, [], [1591, 78391, 5]⟩,
        ⟨7263, true, false, [], [78391, 5]⟩,
        ⟨7280, false, false, [], [5]⟩,
        ⟨7280, false, false, [], [5]⟩
      ]⟩,
    ⟨[1625], [1603, 1613], .source 877⟩,
    ⟨[1627], [1624], .source 878⟩,
    ⟨[1629], [1627, 1613], .source 879⟩,
    ⟨[77733, 3], [1629, 77729], .contexts [
        ⟨4334, true, false, [], [3]⟩,
        ⟨4314, true, false, [], [5, 3]⟩,
        ⟨7282, false, false, [1624], [77729, 3, 5, 3]⟩,
        ⟨7269, true, false, [1624, 1603], [3, 5, 3]⟩,
        ⟨7084, true, false, [1624, 1603], [3, 5, 3]⟩,
        ⟨7281, true, false, [1624], [3, 5, 3]⟩,
        ⟨1931, false, false, [1624, 78391], []⟩,
        ⟨50, false, false, [1624, 78391], []⟩,
        ⟨7110, false, false, [1624], []⟩,
        ⟨7269, false, false, [1624], []⟩,
        ⟨7268, false, false, [1624], []⟩,
        ⟨7268, false, false, [1624], []⟩,
        ⟨4301, false, false, [1624, 1613], []⟩,
        ⟨7283, true, false, [], [1613, 77729]⟩,
        ⟨7284, true, false, [], [77729]⟩
      ]⟩,
    ⟨[1631], [1628], .source 880⟩,
    ⟨[1631], [1631], .contexts []⟩,
    ⟨[1631], [1631], .contexts []⟩,
    ⟨[1631], [1631], .contexts []⟩,
    ⟨[1629], [1630], .contexts [
        ⟨7286, true, true, [], []⟩
      ]⟩,
    ⟨[77733], [1629, 77731], .contexts [
        ⟨7287, false, false, [1630], [77733]⟩,
        ⟨7288, false, false, [1630], [77733]⟩,
        ⟨7289, false, false, [1630], [77733]⟩,
        ⟨7286, false, false, [1630], [77733]⟩,
        ⟨35, true, false, [1630, 1628, 77733], []⟩,
        ⟨7285, false, false, [1630, 1628], [3]⟩,
        ⟨4318, false, false, [1630], []⟩,
        ⟨7290, true, false, [], [77731]⟩
      ]⟩,
    ⟨[1629, 77731], [1629, 77731], .contexts []⟩,
    ⟨[77733], [1629, 77731], .contexts [
        ⟨7291, false, false, [], []⟩,
        ⟨7292, false, false, [], []⟩
      ]⟩,
    ⟨[1631], [1628], .contexts [
        ⟨7286, false, false, [], []⟩
      ]⟩,
    ⟨[1628], [1628], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 114. -/
def y322TCContextRaw114 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1631], [1628], .contexts [
        ⟨7294, false, false, [], []⟩,
        ⟨7295, false, false, [], []⟩,
        ⟨7295, false, false, [], []⟩
      ]⟩,
    ⟨[77731, 9], [1631, 78131], .contexts [
        ⟨7291, true, false, [1628], [9]⟩,
        ⟨6284, false, false, [1628], []⟩,
        ⟨6285, false, false, [1628], []⟩,
        ⟨7296, true, false, [], [78131]⟩
      ]⟩,
    ⟨[1633], [1629, 293], .source 881⟩,
    ⟨[1635], [1632], .source 882⟩,
    ⟨[1635], [1632], .contexts [
        ⟨7299, false, false, [], []⟩
      ]⟩,
    ⟨[78129], [1635, 77735], .contexts [
        ⟨7298, false, false, [1632], [78129]⟩,
        ⟨6278, true, false, [1632, 1629], []⟩,
        ⟨7293, true, false, [1632], [1]⟩,
        ⟨4353, false, false, [1632], []⟩,
        ⟨4355, false, false, [1632], []⟩,
        ⟨24, true, false, [1632], [77735]⟩,
        ⟨7300, true, false, [], [77735]⟩
      ]⟩,
    ⟨[1633], [1634], .contexts [
        ⟨7299, true, true, [], []⟩
      ]⟩,
    ⟨[1633], [1634], .contexts [
        ⟨7302, false, false, [], []⟩
      ]⟩,
    ⟨[1634], [1634], .contexts []⟩,
    ⟨[78129], [1635, 77735], .contexts [
        ⟨7301, false, false, [], []⟩
      ]⟩,
    ⟨[1637], [1633, 1623], .source 883⟩,
    ⟨[77735, 13], [1637, 78381], .contexts [
        ⟨7301, true, false, [1634], [13]⟩,
        ⟨7278, false, false, [1634, 1620], []⟩,
        ⟨7114, false, false, [1634, 1620], []⟩,
        ⟨7279, true, false, [1634], [78381]⟩,
        ⟨7279, true, false, [1634], [78381]⟩,
        ⟨7277, true, false, [1634], [78381]⟩,
        ⟨7302, true, false, [], [1623, 78381]⟩,
        ⟨7306, true, false, [], [78381]⟩
      ]⟩,
    ⟨[77731, 9], [1631, 78131], .contexts [
        ⟨7297, false, false, [], []⟩
      ]⟩,
    ⟨[1631, 78131], [1631, 78131], .contexts []⟩,
    ⟨[1631, 78131], [1631, 78131], .contexts []⟩,
    ⟨[78131, 3], [78131, 3], .contexts []⟩,
    ⟨[1629], [1629], .contexts []⟩,
    ⟨[1630], [1630], .contexts []⟩,
    ⟨[78131, 3], [1629, 78017], .contexts [
        ⟨7311, false, false, [], []⟩,
        ⟨7310, true, false, [1630], [3]⟩,
        ⟨7310, true, false, [1630], [3]⟩,
        ⟨7309, true, false, [1630], [3]⟩,
        ⟨7308, true, false, [1630], [3]⟩,
        ⟨4318, true, false, [1630], [9, 3]⟩,
        ⟨1010, false, false, [1630, 77729], []⟩,
        ⟨77, false, false, [1630, 77729], []⟩,
        ⟨5899, false, false, [1630], []⟩,
        ⟨5904, false, false, [1630], []⟩,
        ⟨7313, true, false, [], [78017]⟩,
        ⟨7313, true, false, [], [78017]⟩,
        ⟨7290, true, false, [], [78017]⟩,
        ⟨7312, true, false, [], [78017]⟩
      ]⟩,
    ⟨[1639], [293, 1635], .source 884⟩,
    ⟨[1641], [145, 1639], .source 885⟩,
    ⟨[1643], [1641, 1637], .source 886⟩,
    ⟨[293, 78129], [293, 1635, 77735], .contexts [
        ⟨7305, false, false, [293], []⟩
      ]⟩,
    ⟨[293, 1635, 77735], [1639, 77735], .contexts [
        ⟨7315, true, false, [], [77735]⟩
      ]⟩,
    ⟨[1639, 77735], [1639, 77735], .contexts []⟩,
    ⟨[1645], [1642], .source 887⟩,
    ⟨[1647], [1645, 1639], .source 888⟩,
    ⟨[78379, 13], [1647, 77735], .contexts [
        ⟨7069, true, false, [], [13]⟩,
        ⟨7317, false, false, [1642], [78381, 1, 13]⟩,
        ⟨7307, true, false, [1642, 1641], [1, 13]⟩,
        ⟨7316, false, false, [1642], [77735, 13, 1, 13]⟩,
        ⟨7315, false, false, [1642, 145], [77735, 13, 1, 13]⟩,
        ⟨7305, true, false, [1642, 145, 293], [13, 1, 13]⟩,
        ⟨6278, true, false, [1642, 145], [13, 1, 13]⟩,
        ⟨4343, true, false, [1642], [1, 13, 1, 13]⟩,
        ⟨3422, false, false, [1642, 77731], []⟩,
        ⟨19, false, false, [1642, 77731], []⟩,
        ⟨6278, false, false, [1642], []⟩,
        ⟨7318, false, false, [1642], []⟩,
        ⟨7319, false, false, [1642], []⟩,
        ⟨7320, false, false, [1642], []⟩,
        ⟨4362, false, false, [1642, 1639], []⟩,
        ⟨7321, true, false, [], [1639, 77735]⟩,
        ⟨7322, true, false, [], [77735]⟩
      ]⟩,
    ⟨[1651], [1646], .source 890⟩,
    ⟨[77735, 13], [1637, 78381], .contexts [
        ⟨7307, false, false, [], []⟩
      ]⟩,
    ⟨[1637, 78381], [1637, 78381], .contexts []⟩,
    ⟨[1649], [1636], .source 889⟩,
    ⟨[1653], [1649, 1651], .source 891⟩,
    ⟨[], [1629, 1631], .contexts [
        ⟨7286, true, false, [1629], []⟩
      ]⟩,
    ⟨[78131, 5], [78131, 5], .contexts []⟩,
    ⟨[1631], [1631], .contexts [
        ⟨24, false, false, [], [1631]⟩,
        ⟨7288, false, false, [], []⟩,
        ⟨7289, false, false, [], []⟩
      ]⟩,
    ⟨[1633, 77371], [1633, 77371], .contexts []⟩,
    ⟨[77735, 8], [77735, 9], .contexts [
        ⟨77, false, false, [77735], []⟩
      ]⟩,
    ⟨[77373, 3], [77373, 3], .contexts []⟩,
    ⟨[77373, 3], [1632, 77737], .contexts [
        ⟨7334, false, false, [], []⟩,
        ⟨2104, true, false, [], [3]⟩,
        ⟨7332, true, false, [1632], [9, 3]⟩,
        ⟨7332, true, false, [1632], [9, 3]⟩,
        ⟨7303, false, false, [1632], [77371, 9, 3]⟩,
        ⟨7304, false, false, [1632], [77371, 9, 3]⟩,
        ⟨7304, false, false, [1632], [77371, 9, 3]⟩,
        ⟨2093, true, false, [1632, 1634], [9, 3]⟩,
        ⟨6269, true, false, [1632, 1634], [9, 3]⟩,
        ⟨7301, false, false, [1632, 1634], [3, 9, 3]⟩,
        ⟨1010, false, false, [1632, 77735], []⟩,
        ⟨7333, false, false, [1632], []⟩,
        ⟨4368, false, false, [1632], []⟩
      ]⟩,
    ⟨[1632], [1632], .contexts []⟩,
    ⟨[77373, 3], [1635, 77737], .contexts [
        ⟨7335, false, false, [], []⟩,
        ⟨4369, false, false, [1632], []⟩,
        ⟨7336, true, false, [], [77737]⟩,
        ⟨7336, true, false, [], [77737]⟩,
        ⟨7300, true, false, [], [77737]⟩
      ]⟩,
    ⟨[78381], [1653, 78379], .contexts [
        ⟨7326, true, false, [1636], []⟩,
        ⟨7326, true, false, [1636], []⟩,
        ⟨7325, true, false, [1636], []⟩,
        ⟨7323, true, false, [1636, 1646], [13]⟩,
        ⟨98, false, false, [1636, 1646, 78379], []⟩,
        ⟨7324, true, false, [1636], [78379]⟩,
        ⟨7327, true, false, [], [1651, 78379]⟩,
        ⟨7328, true, false, [], [78379]⟩
      ]⟩,
    ⟨[1657], [1637, 1653], .source 893⟩,
    ⟨[1659], [151, 1657], .source 894⟩,
    ⟨[1659, 78377], [1659, 78377], .contexts []⟩,
    ⟨[77735, 11, 13, 11], [1659, 78377], .contexts [
        ⟨4361, false, false, [], [13, 11]⟩,
        ⟨4361, false, false, [], [13, 11]⟩,
        ⟨4357, true, false, [], [11, 13, 11]⟩,
        ⟨181, false, false, [77733], [13, 11]⟩,
        ⟨182, false, false, [77733], [13, 11]⟩,
        ⟨4359, false, false, [], [13, 11]⟩,
        ⟨4360, false, false, [], [13, 11]⟩,
        ⟨4362, false, false, [151], [13, 11]⟩,
        ⟨4191, true, false, [], [77735, 13, 11]⟩,
        ⟨4358, false, false, [], [13, 11]⟩,
        ⟨4360, false, false, [], [13, 11]⟩,
        ⟨4360, false, false, [], [13, 11]⟩,
        ⟨7307, false, false, [151], [11]⟩,
        ⟨7338, false, false, [151, 1637], [11]⟩,
        ⟨7339, true, false, [151], [78379, 11]⟩,
        ⟨7340, true, false, [], [78379, 11]⟩,
        ⟨7065, false, false, [1659], []⟩,
        ⟨7341, false, false, [], []⟩
      ]⟩,
    ⟨[1661], [1658], .source 895⟩,
    ⟨[1658], [1658], .contexts []⟩,
    ⟨[78377, 13], [1661, 77735], .contexts [
        ⟨7342, true, false, [1658], [13]⟩,
        ⟨1836, false, false, [1658, 77735], []⟩,
        ⟨4362, false, false, [1658], []⟩,
        ⟨7344, true, false, [], [77735]⟩,
        ⟨7344, true, false, [], [77735]⟩,
        ⟨7343, true, false, [], [77735]⟩
      ]⟩,
    ⟨[1663], [1656], .source 896⟩,
    ⟨[1665], [1663, 1659], .source 897⟩,
    ⟨[78379], [1665, 78377], .contexts [
        ⟨7339, false, false, [1656], [78379]⟩,
        ⟨7338, true, false, [1656, 1637], []⟩,
        ⟨7325, true, false, [1656], []⟩,
        ⟨7345, true, false, [1656, 1660], [13]⟩,
        ⟨98, false, false, [1656, 1660, 78377], []⟩,
        ⟨7343, false, true, [1656], [78377]⟩,
        ⟨7341, false, false, [1656], []⟩,
        ⟨7346, true, false, [], [1659, 78377]⟩,
        ⟨7347, true, false, [], [78377]⟩
      ]⟩,
    ⟨[1667], [1653, 1665], .source 898⟩,
    ⟨[78381], [1667, 78377], .contexts [
        ⟨7338, false, false, [], []⟩,
        ⟨7348, false, false, [1653], []⟩,
        ⟨7349, true, false, [], [78377]⟩
      ]⟩,
    ⟨[1669], [1664], .source 899⟩,
    ⟨[1671], [1669, 1667], .source 900⟩,
    ⟨[77735, 5], [1639, 77735], .contexts [
        ⟨6281, false, false, [], []⟩,
        ⟨6282, false, false, [], []⟩,
        ⟨7318, false, false, [], []⟩,
        ⟨7319, false, false, [], []⟩,
        ⟨7320, false, false, [], []⟩
      ]⟩,
    ⟨[77737, 5], [77737, 5], .contexts []⟩,
    ⟨[1673], [1638], .source 901⟩,
    ⟨[1638], [1638], .contexts []⟩,
    ⟨[1673], [1638], .contexts [
        ⟨7355, false, false, [], []⟩,
        ⟨7356, false, false, [], []⟩,
        ⟨7356, false, false, [], []⟩
      ]⟩,
    ⟨[1675], [1637, 1667], .source 902⟩,
    ⟨[1677], [1639, 1675], .source 903⟩]

/-- Exact literal claimed equations and contextual derivations, block 115. -/
def y322TCContextRaw115 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77735, 13], [1675, 78377], .contexts [
        ⟨7325, false, false, [], []⟩,
        ⟨7350, false, false, [1637], []⟩,
        ⟨7358, true, false, [], [78377]⟩
      ]⟩,
    ⟨[78377, 5], [78377, 5], .contexts []⟩,
    ⟨[1679], [1676], .source 904⟩,
    ⟨[1681], [1679, 1675], .source 905⟩,
    ⟨[1683], [1674], .source 906⟩,
    ⟨[1674], [1674], .contexts []⟩,
    ⟨[78375, 13], [1683, 77737], .contexts [
        ⟨7061, true, false, [], [13]⟩,
        ⟨7360, true, false, [1674], [9, 13]⟩,
        ⟨1650, false, false, [1674, 77735], []⟩,
        ⟨7333, false, false, [1674], []⟩,
        ⟨4368, false, false, [1674], []⟩,
        ⟨4369, false, false, [1674], []⟩,
        ⟨7365, true, false, [], [77737]⟩,
        ⟨7365, true, false, [], [77737]⟩,
        ⟨7364, true, false, [], [77737]⟩
      ]⟩,
    ⟨[1629, 78017], [1629, 78017], .contexts []⟩,
    ⟨[1629, 78017], [1629, 78017], .contexts []⟩,
    ⟨[1629, 78021], [1629, 78021], .contexts []⟩,
    ⟨[1629, 78021], [1629, 78021], .contexts []⟩,
    ⟨[78131], [78131], .contexts []⟩,
    ⟨[78021, 11], [1631, 78131], .contexts [
        ⟨7370, true, false, [1628], [11]⟩,
        ⟨7369, true, false, [1628], [11]⟩,
        ⟨5929, true, false, [], [11]⟩,
        ⟨5913, true, false, [], [3, 11]⟩,
        ⟨7368, true, false, [1628], [11, 3, 11]⟩,
        ⟨7368, true, false, [1628], [11, 3, 11]⟩,
        ⟨7367, true, false, [1628], [11, 3, 11]⟩,
        ⟨7314, true, false, [1628], [11, 3, 11]⟩,
        ⟨7311, true, false, [1628], [11, 3, 11]⟩,
        ⟨2823, false, false, [1628, 78131], []⟩,
        ⟨7371, false, false, [1628], []⟩,
        ⟨6293, false, false, [1628], []⟩,
        ⟨7295, true, false, [], [78131]⟩,
        ⟨7295, true, false, [], [78131]⟩,
        ⟨7294, true, false, [], [78131]⟩,
        ⟨7287, true, false, [], [78131]⟩
      ]⟩,
    ⟨[1630, 78021], [1629, 78021], .contexts [
        ⟨7290, true, false, [], [78021]⟩
      ]⟩,
    ⟨[1629], [1629], .contexts []⟩,
    ⟨[1629], [1629], .contexts [
        ⟨7312, false, false, [], []⟩,
        ⟨7374, false, false, [], []⟩
      ]⟩,
    ⟨[1629], [1629], .contexts []⟩,
    ⟨[78133], [1629, 78021], .contexts [
        ⟨6302, true, false, [], []⟩,
        ⟨7372, true, false, [1630], [11]⟩,
        ⟨90, false, false, [1630, 78021], []⟩,
        ⟨7373, false, false, [], []⟩,
        ⟨7369, false, false, [], []⟩,
        ⟨7376, true, false, [], [78021]⟩,
        ⟨7375, true, false, [], [78021]⟩
      ]⟩,
    ⟨[78133], [1629, 78021], .contexts [
        ⟨7377, false, false, [], []⟩,
        ⟨7370, false, false, [], []⟩
      ]⟩,
    ⟨[78021, 1], [1631, 78135], .contexts [
        ⟨7377, true, false, [1628], [1]⟩,
        ⟨6312, false, false, [1628], []⟩,
        ⟨6314, false, false, [1628], []⟩,
        ⟨7296, true, false, [], [78135]⟩
      ]⟩,
    ⟨[78131, 5, 11], [1631, 78131, 11], .contexts [
        ⟨7330, false, false, [], [11]⟩,
        ⟨7330, false, false, [], [11]⟩,
        ⟨7329, false, false, [], [78131, 5, 11]⟩,
        ⟨7297, true, false, [1629], [5, 11]⟩,
        ⟨7292, true, false, [], [9, 5, 11]⟩,
        ⟨7292, true, false, [], [9, 5, 11]⟩,
        ⟨7293, true, false, [], [9, 5, 11]⟩,
        ⟨4335, true, false, [], [9, 5, 11]⟩,
        ⟨1672, false, false, [77731], [11]⟩,
        ⟨77, false, false, [77731], [11]⟩,
        ⟨7308, false, false, [], [11]⟩,
        ⟨7309, false, false, [], [11]⟩,
        ⟨7310, false, false, [], [11]⟩,
        ⟨7310, false, false, [], [11]⟩,
        ⟨6293, false, false, [1631], [11]⟩,
        ⟨7331, true, false, [], [78131, 11]⟩,
        ⟨7309, false, false, [], [11]⟩,
        ⟨7310, false, false, [], [11]⟩,
        ⟨7310, false, false, [], [11]⟩
      ]⟩,
    ⟨[5, 11, 5, 11], [], .contexts [
        ⟨274, false, false, [], []⟩
      ]⟩,
    ⟨[1629, 78021], [78023], .contexts [
        ⟨7370, true, false, [], []⟩,
        ⟨7370, true, false, [], []⟩,
        ⟨7378, true, false, [], []⟩,
        ⟨6299, true, false, [], []⟩,
        ⟨1118, false, false, [], [78131, 11]⟩,
        ⟨6293, true, false, [], [11]⟩,
        ⟨7371, true, false, [], [11]⟩,
        ⟨7381, true, false, [78131], [11]⟩,
        ⟨7380, false, false, [], [5, 11, 11]⟩,
        ⟨6298, false, false, [1631], [5, 11, 11]⟩,
        ⟨7378, false, false, [1631], [5, 11, 11]⟩,
        ⟨7286, false, false, [], [1629, 78021, 5, 11, 11]⟩,
        ⟨5939, false, false, [], [11, 11]⟩,
        ⟨5941, false, false, [], [11, 11]⟩,
        ⟨5942, false, false, [], [11, 11]⟩,
        ⟨5942, false, false, [], [11, 11]⟩,
        ⟨90, false, false, [78023], []⟩,
        ⟨5942, false, false, [], []⟩
      ]⟩,
    ⟨[78023], [1629, 78021], .contexts [
        ⟨7296, false, false, [1630], [78023]⟩,
        ⟨5941, true, false, [1630, 1628], []⟩,
        ⟨7382, true, false, [1630, 1628], []⟩,
        ⟨7373, false, false, [], []⟩,
        ⟨7370, false, false, [], []⟩
      ]⟩,
    ⟨[1629, 78021, 1], [1629, 1631, 78135], .contexts [
        ⟨7379, false, false, [1629], []⟩
      ]⟩,
    ⟨[78135], [78025], .contexts [
        ⟨7329, false, false, [], [78135]⟩,
        ⟨7384, true, false, [], []⟩,
        ⟨7383, true, false, [], [1]⟩,
        ⟨5948, false, false, [], []⟩,
        ⟨1116, true, false, [], [78025]⟩,
        ⟨23, true, false, [], [78025]⟩
      ]⟩,
    ⟨[78135], [78025], .contexts [
        ⟨7385, false, false, [], []⟩,
        ⟨5950, false, false, [], []⟩
      ]⟩,
    ⟨[78025, 13], [78137], .contexts [
        ⟨7385, true, false, [], [13]⟩,
        ⟨6319, false, false, [], []⟩,
        ⟨6321, false, false, [], []⟩,
        ⟨1117, true, false, [], [78137]⟩
      ]⟩,
    ⟨[1635, 77737], [1635, 77737], .contexts []⟩,
    ⟨[77739, 3], [77739, 3], .contexts []⟩,
    ⟨[77739, 3], [1633, 77375], .contexts [
        ⟨7389, false, false, [], []⟩,
        ⟨4371, true, false, [], [3]⟩,
        ⟨7388, true, false, [1634], [11, 3]⟩,
        ⟨7388, true, false, [1634], [11, 3]⟩,
        ⟨7337, true, false, [1634], [11, 3]⟩,
        ⟨7334, true, false, [1634], [11, 3]⟩,
        ⟨976, false, false, [1634, 77373], []⟩,
        ⟨91, false, false, [1634, 77373], []⟩,
        ⟨2120, false, false, [1634], []⟩,
        ⟨2124, false, false, [1634], []⟩,
        ⟨7304, true, false, [], [77375]⟩,
        ⟨7304, true, false, [], [77375]⟩,
        ⟨7303, true, false, [], [77375]⟩
      ]⟩,
    ⟨[77375, 3], [1635, 77739], .contexts [
        ⟨7390, true, false, [1632], [3]⟩,
        ⟨35, false, false, [1632, 77739], []⟩,
        ⟨7299, true, false, [], [77739]⟩
      ]⟩,
    ⟨[1681, 78377], [1681, 78377], .contexts []⟩,
    ⟨[1681, 78375], [1681, 78375], .contexts []⟩,
    ⟨[1681, 78375], [1681, 78375], .contexts []⟩,
    ⟨[78377, 5, 9], [1681, 78375], .contexts [
        ⟨7361, false, false, [], [9]⟩,
        ⟨7361, false, false, [], [9]⟩,
        ⟨7359, false, false, [1676], [78377, 5, 9]⟩,
        ⟨7358, false, false, [1676, 1639], [78377, 5, 9]⟩,
        ⟨7350, true, false, [1676, 1639, 1637], [5, 9]⟩,
        ⟨7307, true, false, [1676, 1639], [5, 9]⟩,
        ⟨7353, true, false, [1676], [13, 5, 9]⟩,
        ⟨1578, false, false, [1676, 77735], [9]⟩,
        ⟨108, false, false, [1676, 77735], [9]⟩,
        ⟨7360, false, false, [1676], [9]⟩,
        ⟨7362, true, false, [], [1675, 78377, 9]⟩,
        ⟨7363, true, false, [], [78377, 9]⟩,
        ⟨7392, false, false, [], [9]⟩,
        ⟨7392, false, false, [], [9]⟩,
        ⟨7061, false, false, [1681], []⟩,
        ⟨7393, false, false, [], []⟩,
        ⟨7394, false, false, [], []⟩
      ]⟩,
    ⟨[78375, 5], [78375, 5], .contexts []⟩,
    ⟨[78375], [78375], .contexts []⟩,
    ⟨[1673, 77737], [1673, 77737], .contexts []⟩,
    ⟨[77737, 5, 11], [1673, 77739], .contexts [
        ⟨7354, false, false, [], [11]⟩,
        ⟨7354, false, false, [], [11]⟩,
        ⟨4365, true, false, [], [5, 11]⟩,
        ⟨7353, true, false, [1638], [9, 5, 11]⟩,
        ⟨1672, false, false, [1638, 77735], [11]⟩,
        ⟨7333, false, false, [1638], [11]⟩,
        ⟨4368, false, false, [1638], [11]⟩,
        ⟨4369, false, false, [1638], [11]⟩,
        ⟨7357, true, false, [], [77737, 11]⟩,
        ⟨7398, false, false, [], [11]⟩,
        ⟨7398, false, false, [], [11]⟩,
        ⟨4371, false, false, [1673], []⟩
      ]⟩,
    ⟨[77739, 5], [77739, 5], .contexts []⟩,
    ⟨[1672], [1672], .contexts []⟩,
    ⟨[1639], [1672], .contexts [
        ⟨7355, true, true, [], []⟩,
        ⟨7401, false, false, [], []⟩,
        ⟨7401, false, false, [], []⟩
      ]⟩,
    ⟨[1687], [135, 1631], .source 908⟩,
    ⟨[1631, 78025], [1631, 78025], .contexts []⟩,
    ⟨[78021, 1], [1631, 78025], .contexts [
        ⟨7379, false, false, [], []⟩,
        ⟨7386, false, false, [1631], []⟩,
        ⟨7404, false, false, [], []⟩,
        ⟨7404, false, false, [], []⟩
      ]⟩,
    ⟨[78021, 0], [78021, 1], .contexts [
        ⟨19, false, false, [78021], []⟩
      ]⟩,
    ⟨[1687, 78025, 3], [1631, 78025], .contexts [
        ⟨7403, false, false, [], [78025, 3]⟩,
        ⟨7386, true, false, [135, 1631], [3]⟩,
        ⟨7379, true, false, [135], [3]⟩,
        ⟨5929, true, false, [135], [1, 3]⟩,
        ⟨5918, true, false, [], [3, 1, 3]⟩,
        ⟨5918, true, false, [], [3, 1, 3]⟩,
        ⟨5917, true, false, [], [3, 1, 3]⟩,
        ⟨5920, true, false, [], [3, 1, 3]⟩,
        ⟨5915, true, false, [], [1, 3, 1, 3]⟩,
        ⟨5915, true, false, [], [1, 3, 1, 3]⟩,
        ⟨5914, true, false, [], [1, 3, 1, 3]⟩,
        ⟨5930, true, false, [], [1, 3, 1, 3]⟩,
        ⟨1951, false, false, [78021], []⟩,
        ⟨7406, false, false, [], []⟩,
        ⟨7405, false, false, [], []⟩
      ]⟩,
    ⟨[78025, 3], [78025, 3], .contexts []⟩,
    ⟨[1689], [1686], .source 909⟩,
    ⟨[1691], [1689, 1631], .source 910⟩,
    ⟨[78023], [1629, 78021], .contexts [
        ⟨7383, false, false, [], []⟩
      ]⟩,
    ⟨[78025, 5], [78025, 5], .contexts []⟩,
    ⟨[1691, 78025], [1691, 78025], .contexts []⟩,
    ⟨[1691], [1691], .contexts []⟩,
    ⟨[1691], [1691], .contexts []⟩,
    ⟨[78025, 13], [78137], .contexts [
        ⟨7387, false, false, [], []⟩,
        ⟨6321, false, false, [], []⟩,
        ⟨6322, false, false, [], []⟩,
        ⟨6322, false, false, [], []⟩
      ]⟩,
    ⟨[1691, 78137], [1691, 78137], .contexts []⟩,
    ⟨[1691, 78137], [1691, 78137], .contexts []⟩,
    ⟨[78137, 3], [78137, 3], .contexts []⟩,
    ⟨[78137, 3], [1691, 78137], .contexts [
        ⟨7419, false, false, [], []⟩,
        ⟨7416, true, false, [], [3]⟩,
        ⟨107, false, false, [78025], []⟩,
        ⟨109, false, false, [78025], []⟩,
        ⟨7408, false, false, [], [13]⟩,
        ⟨7408, false, false, [], [13]⟩,
        ⟨7407, false, false, [1686], [13]⟩,
        ⟨5951, false, false, [1686, 1631], [13]⟩,
        ⟨7409, true, false, [], [1631, 78025, 13]⟩,
        ⟨7410, true, false, [], [78025, 13]⟩,
        ⟨7413, false, false, [], [13]⟩,
        ⟨7413, false, false, [], [13]⟩,
        ⟨7387, false, false, [1691], []⟩,
        ⟨7417, false, false, [], []⟩,
        ⟨7418, false, false, [], []⟩
      ]⟩,
    ⟨[78025, 5, 13], [1631, 78137], .contexts [
        ⟨7412, false, false, [], [13]⟩,
        ⟨7412, false, false, [], [13]⟩,
        ⟨7329, false, false, [], [78025, 5, 13]⟩,
        ⟨7386, true, false, [1629, 1631], [5, 13]⟩,
        ⟨7384, true, false, [], [5, 13]⟩,
        ⟨7370, true, false, [], [1, 5, 13]⟩,
        ⟨7370, true, false, [], [1, 5, 13]⟩,
        ⟨7411, true, false, [], [1, 5, 13]⟩,
        ⟨5940, true, false, [], [1, 5, 13]⟩,
        ⟨1509, false, false, [78021], [13]⟩,
        ⟨7406, false, false, [], [13]⟩,
        ⟨7405, false, false, [], [13]⟩,
        ⟨5951, false, false, [1631], [13]⟩,
        ⟨7331, true, false, [], [78025, 13]⟩,
        ⟨7404, false, false, [], [13]⟩,
        ⟨7404, false, false, [], [13]⟩,
        ⟨7387, false, false, [1631], []⟩
      ]⟩,
    ⟨[1631, 78137], [1631, 78137], .contexts []⟩,
    ⟨[1631, 78137], [1631, 78137], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 116. -/
def y322TCContextRaw116 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78137, 5], [78137, 5], .contexts []⟩,
    ⟨[1633, 77375], [1633, 77375], .contexts []⟩,
    ⟨[1693], [1633, 277], .source 911⟩,
    ⟨[1695], [1693, 1635], .source 912⟩,
    ⟨[77739, 0], [77739, 1], .contexts [
        ⟨19, false, false, [77739], []⟩
      ]⟩,
    ⟨[1695, 77741, 3], [77741], .contexts [
        ⟨4375, true, false, [1695], [3]⟩,
        ⟨7427, false, false, [], [77739, 1, 3]⟩,
        ⟨7391, true, false, [1693], [1, 3]⟩,
        ⟨7426, false, false, [], [77375, 3, 1, 3]⟩,
        ⟨2125, true, false, [1633], [3, 1, 3]⟩,
        ⟨7425, true, false, [], [1, 3, 1, 3]⟩,
        ⟨7425, true, false, [], [1, 3, 1, 3]⟩,
        ⟨7390, true, false, [], [1, 3, 1, 3]⟩,
        ⟨7389, true, false, [], [1, 3, 1, 3]⟩,
        ⟨1951, false, false, [77739], []⟩,
        ⟨7428, false, false, [], []⟩,
        ⟨4378, false, false, [], []⟩
      ]⟩,
    ⟨[77741, 3], [77741, 3], .contexts []⟩,
    ⟨[1697], [1694], .source 913⟩,
    ⟨[1694], [1694], .contexts []⟩,
    ⟨[1697], [1694], .contexts [
        ⟨7431, false, false, [], []⟩,
        ⟨7432, false, false, [], []⟩,
        ⟨7432, false, false, [], []⟩
      ]⟩,
    ⟨[78375, 5, 1], [1681, 78373], .contexts [
        ⟨7396, false, false, [], [1]⟩,
        ⟨7396, false, false, [], [1]⟩,
        ⟨7060, true, false, [], [5, 1]⟩,
        ⟨7060, true, false, [], [5, 1]⟩,
        ⟨7117, true, false, [], [5, 1]⟩,
        ⟨7116, true, false, [], [5, 1]⟩,
        ⟨1805, false, false, [78377], [1]⟩,
        ⟨1806, false, false, [78377], [1]⟩,
        ⟨7395, false, false, [], [1]⟩,
        ⟨7397, false, false, [1681], [1]⟩,
        ⟨24, true, false, [], [1681, 78375, 1]⟩,
        ⟨7393, false, false, [], [1]⟩,
        ⟨7394, false, false, [], [1]⟩,
        ⟨7394, false, false, [], [1]⟩,
        ⟨7058, false, false, [1681], []⟩
      ]⟩,
    ⟨[1699], [1680], .source 914⟩,
    ⟨[1680], [1680], .contexts []⟩,
    ⟨[1639, 77739], [1639, 77739], .contexts []⟩,
    ⟨[1639, 77741, 5], [77739, 1], .contexts [
        ⟨4375, true, false, [1639], [5]⟩,
        ⟨7437, true, false, [], [1, 5]⟩,
        ⟨7437, true, false, [], [1, 5]⟩,
        ⟨7402, false, false, [], [77739, 1, 5]⟩,
        ⟨4373, true, false, [1672], [1, 5]⟩,
        ⟨4373, true, false, [1672], [1, 5]⟩,
        ⟨4372, true, false, [1672], [1, 5]⟩,
        ⟨4371, true, false, [1672], [1, 5]⟩,
        ⟨91, true, false, [1672, 77737], [1, 5]⟩,
        ⟨1645, true, false, [1672, 77737], [1, 5]⟩,
        ⟨7399, false, false, [1672], [5, 1, 5]⟩,
        ⟨7400, true, false, [], [1, 5]⟩,
        ⟨7400, true, false, [], [1, 5]⟩,
        ⟨1509, false, false, [77739], []⟩,
        ⟨7428, false, false, [], []⟩
      ]⟩,
    ⟨[77741, 5], [77741, 5], .contexts []⟩,
    ⟨[1701], [1690], .source 915⟩,
    ⟨[1690], [1690], .contexts []⟩,
    ⟨[1691, 78141], [1691, 78141], .contexts []⟩,
    ⟨[1691, 78141, 15], [78137, 3, 15, 3, 15], .contexts [
        ⟨7442, true, false, [], [15]⟩,
        ⟨6348, true, false, [1691], [15]⟩,
        ⟨6333, true, false, [1691], [3, 15]⟩,
        ⟨7418, true, false, [], [15, 3, 15]⟩,
        ⟨7418, true, false, [], [15, 3, 15]⟩,
        ⟨7417, true, false, [], [15, 3, 15]⟩,
        ⟨24, false, false, [], [1691, 78137, 15, 3, 15]⟩,
        ⟨7414, false, false, [], [78137, 15, 3, 15]⟩,
        ⟨7415, false, false, [], [78137, 15, 3, 15]⟩,
        ⟨6331, true, false, [1691], [15, 3, 15]⟩,
        ⟨7420, true, false, [], [15, 3, 15]⟩,
        ⟨7419, true, false, [], [15, 3, 15]⟩
      ]⟩,
    ⟨[78137], [78137], .contexts []⟩,
    ⟨[1691], [1700], .contexts [
        ⟨7440, true, true, [], []⟩
      ]⟩,
    ⟨[78139], [78137, 15], .contexts [
        ⟨6337, true, false, [], []⟩
      ]⟩,
    ⟨[1701, 78139, 5], [78143], .contexts [
        ⟨7440, false, false, [], [78139, 5]⟩,
        ⟨7446, false, false, [1690], [5]⟩,
        ⟨7440, false, false, [1690, 1700], [78137, 15, 5]⟩,
        ⟨7441, false, false, [1690, 1700], [78137, 15, 5]⟩,
        ⟨7441, false, false, [1690, 1700], [78137, 15, 5]⟩,
        ⟨6331, true, false, [1690, 1700, 1690], [15, 5]⟩,
        ⟨7444, true, false, [1690, 1700, 1690], [15, 5]⟩,
        ⟨2767, true, false, [1690, 1700, 1690, 78137], [15, 5]⟩,
        ⟨7443, true, false, [1690, 1700, 1690], [15, 5]⟩,
        ⟨3, false, false, [1690, 1700, 78141], [5]⟩,
        ⟨7445, true, false, [1690], [78141, 5]⟩,
        ⟨7442, false, false, [1690], [5]⟩,
        ⟨7415, true, false, [1690], [78141, 5]⟩,
        ⟨7414, true, false, [1690], [78141, 5]⟩,
        ⟨6351, false, false, [], []⟩,
        ⟨6352, false, false, [], []⟩
      ]⟩,
    ⟨[1700], [1700], .contexts []⟩,
    ⟨[1703], [1631, 1691], .source 916⟩,
    ⟨[78137, 5, 15, 5], [1703, 78143], .contexts [
        ⟨7424, false, false, [], [15, 5]⟩,
        ⟨7424, false, false, [], [15, 5]⟩,
        ⟨7416, true, false, [], [5, 15, 5]⟩,
        ⟨116, false, false, [78025], [15, 5]⟩,
        ⟨117, false, false, [78025], [15, 5]⟩,
        ⟨7421, false, false, [], [15, 5]⟩,
        ⟨7422, false, false, [], [15, 5]⟩,
        ⟨7423, false, false, [], [15, 5]⟩,
        ⟨6331, false, false, [1631], [15, 5]⟩,
        ⟨7331, true, false, [], [78137, 15, 5]⟩,
        ⟨7422, false, false, [], [15, 5]⟩,
        ⟨7423, false, false, [], [15, 5]⟩,
        ⟨7423, false, false, [], [15, 5]⟩,
        ⟨6333, false, false, [1631], [5]⟩,
        ⟨7447, false, false, [1631, 1700], []⟩,
        ⟨7448, true, false, [1631], [78143]⟩,
        ⟨7448, true, false, [1631], [78143]⟩,
        ⟨7445, true, false, [1631], [78143]⟩,
        ⟨7449, true, false, [], [78143]⟩
      ]⟩,
    ⟨[1705], [1702], .source 917⟩,
    ⟨[1702], [1702], .contexts []⟩,
    ⟨[78143, 1], [1705, 78139, 1], .contexts [
        ⟨7451, true, true, [1702], [78143, 1]⟩,
        ⟨3, true, false, [1702, 1704, 78143], [1]⟩,
        ⟨7450, true, false, [1702, 1704, 1702], [15, 15, 1]⟩,
        ⟨1504, false, false, [1702, 1704, 1702, 78137], [15, 1]⟩,
        ⟨7444, false, false, [1702, 1704, 1702], [15, 1]⟩,
        ⟨6331, false, false, [1702, 1704, 1702], [15, 1]⟩,
        ⟨7452, true, false, [1702, 1704], [78137, 15, 1]⟩,
        ⟨7452, true, false, [1702, 1704], [78137, 15, 1]⟩,
        ⟨7451, true, false, [1702, 1704], [78137, 15, 1]⟩,
        ⟨7446, true, false, [1702], [1]⟩,
        ⟨7451, true, false, [], [78139, 1]⟩
      ]⟩,
    ⟨[1707], [1705, 145], .source 918⟩,
    ⟨[1709], [1706], .source 919⟩,
    ⟨[1709], [1706], .contexts [
        ⟨7455, false, false, [], []⟩
      ]⟩,
    ⟨[78145], [1707, 78139], .contexts [
        ⟨7456, false, false, [1708], [78145]⟩,
        ⟨24, false, false, [1708, 1706], [78145]⟩,
        ⟨6605, true, false, [1708, 1706], []⟩,
        ⟨6355, true, false, [1708, 1706], []⟩,
        ⟨7453, false, false, [1708, 1706], []⟩,
        ⟨6342, false, false, [1708, 1706, 1705], []⟩,
        ⟨7454, true, false, [1708, 1706], [78139]⟩,
        ⟨7455, false, true, [], [78139]⟩
      ]⟩,
    ⟨[1706], [1706], .contexts []⟩,
    ⟨[78139, 9], [1709, 78147], .contexts [
        ⟨7457, true, false, [1706], [9]⟩,
        ⟨6357, false, false, [1706], []⟩,
        ⟨6604, false, false, [1706], []⟩,
        ⟨7458, true, false, [], [78147]⟩,
        ⟨7458, true, false, [], [78147]⟩,
        ⟨7456, true, false, [], [78147]⟩
      ]⟩,
    ⟨[1697, 77741], [1697, 77741], .contexts []⟩,
    ⟨[77741, 13], [77743], .contexts [
        ⟨4381, false, false, [], []⟩,
        ⟨4577, false, false, [], []⟩,
        ⟨4384, false, false, [], []⟩,
        ⟨4384, false, false, [], []⟩
      ]⟩,
    ⟨[77741, 12], [77741, 13], .contexts [
        ⟨108, false, false, [77741], []⟩
      ]⟩,
    ⟨[77743, 3], [77743, 3], .contexts []⟩,
    ⟨[77743], [77743], .contexts []⟩,
    ⟨[1695], [1696], .contexts [
        ⟨7431, true, true, [], []⟩
      ]⟩,
    ⟨[1695], [1695], .contexts []⟩,
    ⟨[1695], [1696], .contexts [
        ⟨7465, false, false, [], []⟩
      ]⟩,
    ⟨[1696], [1696], .contexts []⟩,
    ⟨[1695], [1696], .contexts [
        ⟨7466, false, false, [], []⟩,
        ⟨7467, false, false, [], []⟩,
        ⟨7468, false, false, [], []⟩,
        ⟨7468, false, false, [], []⟩
      ]⟩,
    ⟨[77743, 3], [1695, 77743], .contexts [
        ⟨7463, false, false, [], []⟩,
        ⟨4381, true, false, [], [3]⟩,
        ⟨7460, true, false, [1696], [13, 3]⟩,
        ⟨7460, true, false, [1696], [13, 3]⟩,
        ⟨7433, false, false, [1696], [77741, 13, 3]⟩,
        ⟨4379, true, false, [1696, 1694], [13, 3]⟩,
        ⟨7429, true, false, [1696, 1694], [13, 3]⟩,
        ⟨7430, true, false, [1696], [13, 3]⟩,
        ⟨7430, true, false, [1696], [13, 3]⟩,
        ⟨932, false, false, [1696, 77741], []⟩,
        ⟨7462, false, false, [1696], []⟩,
        ⟨7461, false, false, [1696], []⟩,
        ⟨7464, false, false, [1696], []⟩,
        ⟨7469, true, false, [], [77743]⟩
      ]⟩,
    ⟨[1673, 77741], [1673, 77741], .contexts []⟩,
    ⟨[77743, 5], [77743, 5], .contexts []⟩,
    ⟨[77743, 5], [1672, 77743], .contexts [
        ⟨7472, false, false, [], []⟩,
        ⟨4381, true, false, [], [5]⟩,
        ⟨7471, true, false, [1672], [13, 5]⟩,
        ⟨7471, true, false, [1672], [13, 5]⟩,
        ⟨7357, false, false, [1672], [77741, 13, 5]⟩,
        ⟨4379, true, false, [1672, 1638], [13, 5]⟩,
        ⟨4378, true, false, [1672, 1638], [13, 5]⟩,
        ⟨7438, true, false, [1672, 1638], [13, 5]⟩,
        ⟨7439, true, false, [1672], [13, 5]⟩,
        ⟨7439, true, false, [1672], [13, 5]⟩,
        ⟨1578, false, false, [1672, 77741], []⟩,
        ⟨7462, false, false, [1672], []⟩,
        ⟨7461, false, false, [1672], []⟩,
        ⟨7464, false, false, [1672], []⟩
      ]⟩,
    ⟨[78139, 13, 9], [863, 1709, 78147], .contexts [
        ⟨6346, false, false, [], [9]⟩,
        ⟨6346, false, false, [], [9]⟩,
        ⟨6337, true, false, [], [13, 9]⟩,
        ⟨408, false, false, [78137], [9]⟩,
        ⟨410, false, false, [78137], [9]⟩,
        ⟨6343, false, false, [], [15, 9]⟩,
        ⟨6319, false, false, [863], [15, 9]⟩,
        ⟨6333, false, false, [863], [9]⟩,
        ⟨6344, false, false, [], [9]⟩,
        ⟨6345, false, false, [], [9]⟩,
        ⟨6341, false, false, [863], [9]⟩,
        ⟨4312, true, false, [], [78139, 9]⟩,
        ⟨6344, false, false, [], [9]⟩,
        ⟨6345, false, false, [], [9]⟩,
        ⟨6345, false, false, [], [9]⟩,
        ⟨7459, false, false, [863], []⟩
      ]⟩,
    ⟨[1711], [863, 1709], .source 920⟩,
    ⟨[1709, 78147], [1709, 78147], .contexts []⟩,
    ⟨[78147, 13], [78147, 13], .contexts []⟩,
    ⟨[1713], [1710], .source 921⟩,
    ⟨[1715], [1713, 1709], .source 922⟩,
    ⟨[1695, 77743], [1695, 77743], .contexts []⟩,
    ⟨[77743, 14], [77743, 15], .contexts [
        ⟨20, false, false, [77743], []⟩
      ]⟩,
    ⟨[77745, 3], [77745, 3], .contexts []⟩,
    ⟨[1639, 77743], [1639, 77743], .contexts []⟩,
    ⟨[77745, 5], [77745, 5], .contexts []⟩,
    ⟨[1715, 78147], [1715, 78147], .contexts []⟩,
    ⟨[1715, 78149, 13], [78147, 10], .contexts [
        ⟨6361, true, false, [1715], [13]⟩,
        ⟨7485, true, false, [], [11, 13]⟩,
        ⟨7485, true, false, [], [11, 13]⟩,
        ⟨7479, false, false, [], [78147, 11, 13]⟩,
        ⟨7478, false, false, [], [1709, 78147, 11, 13]⟩,
        ⟨7476, true, false, [1710], [11, 13]⟩,
        ⟨7476, true, false, [1710], [11, 13]⟩,
        ⟨7459, true, false, [1710], [11, 13]⟩,
        ⟨77, true, false, [1710, 78139], [11, 13]⟩,
        ⟨1650, true, false, [1710, 78139], [11, 13]⟩,
        ⟨7474, false, false, [1710], [13, 11, 13]⟩,
        ⟨7475, true, false, [1710], [78147, 13, 11, 13]⟩,
        ⟨7477, true, false, [], [11, 13]⟩,
        ⟨7477, true, false, [], [11, 13]⟩,
        ⟨1624, false, false, [78147], []⟩
      ]⟩,
    ⟨[78149, 13], [78149, 13], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 117. -/
def y322TCContextRaw117 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1731], [1714], .source 930⟩,
    ⟨[1731], [1731], .contexts []⟩,
    ⟨[1714], [1714], .contexts []⟩,
    ⟨[1731], [1714], .contexts [
        ⟨7489, false, false, [], []⟩,
        ⟨7488, false, false, [], []⟩,
        ⟨7490, false, false, [], []⟩,
        ⟨7490, false, false, [], []⟩
      ]⟩,
    ⟨[1697, 77745], [1697, 77745], .contexts []⟩,
    ⟨[77745, 3], [1697, 77745], .contexts [
        ⟨7482, false, false, [], []⟩,
        ⟨7482, false, false, [], []⟩,
        ⟨4383, true, false, [], [3]⟩,
        ⟨7480, true, false, [1694], [15, 3]⟩,
        ⟨7480, true, false, [1694], [15, 3]⟩,
        ⟨7470, true, false, [1694], [15, 3]⟩,
        ⟨7463, true, false, [1694], [15, 3]⟩,
        ⟨900, false, false, [1694, 77743], []⟩,
        ⟨7481, false, false, [1694], []⟩,
        ⟨4387, false, false, [1694], []⟩,
        ⟨4388, false, false, [1694], []⟩,
        ⟨7433, true, false, [], [77745]⟩,
        ⟨7492, false, false, [], []⟩,
        ⟨7492, false, false, [], []⟩
      ]⟩,
    ⟨[77745, 1], [77747], .contexts [
        ⟨4390, false, false, [], []⟩,
        ⟨4575, false, false, [], []⟩,
        ⟨4393, false, false, [], []⟩,
        ⟨4393, false, false, [], []⟩
      ]⟩,
    ⟨[77747, 3], [77749], .contexts [
        ⟨4392, false, false, [], []⟩
      ]⟩,
    ⟨[77749, 1], [77749, 1], .contexts []⟩,
    ⟨[77749], [77749], .contexts []⟩,
    ⟨[77745, 5], [1673, 77745], .contexts [
        ⟨7484, false, false, [], []⟩,
        ⟨7484, false, false, [], []⟩,
        ⟨4383, true, false, [], [5]⟩,
        ⟨7483, true, false, [1638], [15, 5]⟩,
        ⟨7483, true, false, [1638], [15, 5]⟩,
        ⟨7402, false, false, [1638], [77743, 15, 5]⟩,
        ⟨7473, true, false, [1638], [15, 5]⟩,
        ⟨7472, true, false, [1638], [15, 5]⟩,
        ⟨2006, false, false, [1638, 77743], []⟩,
        ⟨7481, false, false, [1638], []⟩,
        ⟨4387, false, false, [1638], []⟩,
        ⟨4388, false, false, [1638], []⟩,
        ⟨7357, true, false, [], [77745]⟩
      ]⟩,
    ⟨[1673, 77745], [1673, 77745], .contexts []⟩,
    ⟨[77747, 5], [77747, 5], .contexts []⟩,
    ⟨[1731, 78149], [1731, 78149], .contexts []⟩,
    ⟨[78149, 13, 1, 13], [1731, 78153], .contexts [
        ⟨7487, false, false, [], [1, 13]⟩,
        ⟨7487, false, false, [], [1, 13]⟩,
        ⟨7486, false, false, [1714], [1, 13]⟩,
        ⟨91, false, false, [1714, 78147], [1, 13]⟩,
        ⟨6361, false, false, [1714], [1, 13]⟩,
        ⟨6603, false, false, [1714], [1, 13]⟩,
        ⟨6366, false, false, [1714], [1, 13]⟩,
        ⟨6366, false, false, [1714], [1, 13]⟩,
        ⟨7491, true, false, [], [78149, 1, 13]⟩,
        ⟨7501, false, false, [], [1, 13]⟩,
        ⟨7501, false, false, [], [1, 13]⟩,
        ⟨6365, false, false, [1731], [13]⟩,
        ⟨6369, false, false, [1731], []⟩
      ]⟩,
    ⟨[78153, 1], [78153, 1], .contexts []⟩,
    ⟨[78153], [78153], .contexts []⟩,
    ⟨[1715], [1730], .contexts [
        ⟨7488, true, true, [], []⟩
      ]⟩,
    ⟨[1715], [1715], .contexts []⟩,
    ⟨[1730], [1730], .contexts []⟩,
    ⟨[1695, 77749], [1695, 77749], .contexts []⟩,
    ⟨[77749, 1], [1695, 77749], .contexts [
        ⟨7496, false, false, [], []⟩,
        ⟨7496, false, false, [], []⟩,
        ⟨4392, true, false, [], [1]⟩,
        ⟨4390, true, false, [], [3, 1]⟩,
        ⟨7493, true, false, [1696], [1, 3, 1]⟩,
        ⟨2891, false, false, [1696, 77745], []⟩,
        ⟨214, false, false, [1696, 77745], []⟩,
        ⟨7494, false, false, [1696], [3]⟩,
        ⟨7495, false, false, [1696], []⟩,
        ⟨4574, false, false, [1696], []⟩,
        ⟨4396, false, false, [1696], []⟩,
        ⟨4396, false, false, [1696], []⟩,
        ⟨7497, false, false, [1696], []⟩,
        ⟨7469, true, false, [], [77749]⟩,
        ⟨7508, false, false, [], []⟩,
        ⟨7508, false, false, [], []⟩
      ]⟩,
    ⟨[1695, 77753], [1695, 77753], .contexts []⟩,
    ⟨[77749, 5], [77751], .contexts [
        ⟨4395, false, false, [], []⟩
      ]⟩,
    ⟨[77751], [1695, 77753], .contexts [
        ⟨4399, true, false, [], []⟩,
        ⟨4399, true, false, [], []⟩,
        ⟨4573, true, false, [], []⟩,
        ⟨7511, true, false, [], []⟩,
        ⟨7433, false, false, [1696], [77749, 5]⟩,
        ⟨7497, true, false, [1696, 1694], [5]⟩,
        ⟨1909, true, false, [1696, 1694, 77749], [5]⟩,
        ⟨7509, false, false, [1696, 1694], [5, 1, 5, 5]⟩,
        ⟨4395, false, false, [1696], [1, 5, 5]⟩,
        ⟨4398, false, false, [1696], [5, 5]⟩,
        ⟨7510, false, false, [1696, 1694], [5, 5]⟩,
        ⟨49, false, false, [1696, 77753], []⟩,
        ⟨7465, true, false, [], [77753]⟩
      ]⟩,
    ⟨[77753], [1697, 77751], .contexts [
        ⟨7466, false, false, [1694], [77753]⟩,
        ⟨7510, true, false, [1694], []⟩,
        ⟨7512, true, false, [1694], []⟩,
        ⟨7431, true, false, [], [77751]⟩
      ]⟩,
    ⟨[1639, 77747], [1639, 77747], .contexts []⟩,
    ⟨[77747, 5, 3], [1639, 77749], .contexts [
        ⟨7500, false, false, [], [3]⟩,
        ⟨7500, false, false, [], [3]⟩,
        ⟨4390, true, false, [], [5, 3]⟩,
        ⟨7499, true, false, [1672], [1, 5, 3]⟩,
        ⟨7499, true, false, [1672], [1, 5, 3]⟩,
        ⟨7498, true, false, [1672], [1, 5, 3]⟩,
        ⟨1509, false, false, [1672, 77745], [3]⟩,
        ⟨19, false, false, [1672, 77745], [3]⟩,
        ⟨7494, false, false, [1672], [3]⟩,
        ⟨7402, true, false, [], [77747, 3]⟩,
        ⟨7514, false, false, [], [3]⟩,
        ⟨7514, false, false, [], [3]⟩,
        ⟨4392, false, false, [1639], []⟩
      ]⟩,
    ⟨[1715, 78153], [1715, 78153], .contexts []⟩,
    ⟨[78153, 1, 15], [1715, 78155], .contexts [
        ⟨7503, false, false, [], [15]⟩,
        ⟨7503, false, false, [], [15]⟩,
        ⟨7502, true, false, [1730], [1, 15]⟩,
        ⟨3725, false, false, [1730, 78149], [15]⟩,
        ⟨388, false, false, [1730, 78149], [15]⟩,
        ⟨6365, false, false, [1730], [13, 15]⟩,
        ⟨6602, false, false, [1730], [13, 15]⟩,
        ⟨6370, false, false, [1730], [13, 15]⟩,
        ⟨6370, false, false, [1730], [13, 15]⟩,
        ⟨6369, false, false, [1730], [15]⟩,
        ⟨6601, false, false, [1730], [15]⟩,
        ⟨6374, false, false, [1730], [15]⟩,
        ⟨6374, false, false, [1730], [15]⟩,
        ⟨7504, false, false, [1730], [15]⟩,
        ⟨7507, true, false, [], [78153, 15]⟩,
        ⟨7507, true, false, [], [78153, 15]⟩,
        ⟨7505, true, false, [], [78153, 15]⟩,
        ⟨7506, true, false, [], [78153, 15]⟩,
        ⟨7516, false, false, [], [15]⟩,
        ⟨7516, false, false, [], [15]⟩,
        ⟨6373, false, false, [1715], []⟩
      ]⟩,
    ⟨[1715, 78157], [1715, 78157], .contexts []⟩,
    ⟨[78155], [1715, 78157], .contexts [
        ⟨6378, true, false, [], []⟩,
        ⟨6378, true, false, [], []⟩,
        ⟨6599, true, false, [], []⟩,
        ⟨6373, true, false, [], []⟩,
        ⟨7491, false, false, [1730], [78153, 15]⟩,
        ⟨7504, true, false, [1730, 1714], [15]⟩,
        ⟨3731, true, false, [1730, 1714, 78153], [15]⟩,
        ⟨7517, false, false, [1730, 1714], [1, 15, 15]⟩,
        ⟨6377, false, false, [1730], [15, 15]⟩,
        ⟨7518, false, false, [1730, 1714], [15, 15]⟩,
        ⟨3, false, false, [1730, 78157], []⟩,
        ⟨7505, true, false, [], [78157]⟩,
        ⟨7518, false, false, [], []⟩,
        ⟨7506, true, false, [], [78157]⟩
      ]⟩,
    ⟨[78405], [78259, 7], .source 39267⟩,
    ⟨[78259, 7], [78405], .contexts [
        ⟨7520, true, false, [], []⟩
      ]⟩,
    ⟨[78259, 7], [78405], .contexts [
        ⟨7521, false, false, [], []⟩
      ]⟩,
    ⟨[78405], [78405], .contexts []⟩,
    ⟨[78405], [78405], .contexts []⟩,
    ⟨[78259, 7], [78405], .contexts [
        ⟨7522, false, false, [], []⟩,
        ⟨7523, false, false, [], []⟩,
        ⟨7524, false, false, [], []⟩,
        ⟨7524, false, false, [], []⟩
      ]⟩,
    ⟨[78259, 1], [323, 78259], .contexts [
        ⟨6755, false, false, [], []⟩,
        ⟨6757, false, false, [], []⟩,
        ⟨6753, false, false, [], []⟩,
        ⟨6754, false, false, [], []⟩,
        ⟨6754, false, false, [], []⟩
      ]⟩,
    ⟨[323, 78405], [323, 78405], .contexts []⟩,
    ⟨[323, 78405], [323, 78405], .contexts []⟩,
    ⟨[78405, 1], [78405, 1], .contexts []⟩,
    ⟨[78405], [78405], .contexts []⟩,
    ⟨[78259, 3], [77129], .contexts [
        ⟨6748, false, false, [], []⟩,
        ⟨721, false, false, [], []⟩,
        ⟨442, false, false, [], []⟩,
        ⟨442, false, false, [], []⟩
      ]⟩,
    ⟨[78407], [78259, 13], .source 39268⟩,
    ⟨[78259, 13], [78407], .contexts [
        ⟨7532, true, false, [], []⟩
      ]⟩,
    ⟨[78407], [78407], .contexts []⟩,
    ⟨[78407], [78407], .contexts []⟩,
    ⟨[78259, 13], [78407], .contexts [
        ⟨7533, false, false, [], []⟩,
        ⟨7534, false, false, [], []⟩,
        ⟨7535, false, false, [], []⟩,
        ⟨7535, false, false, [], []⟩
      ]⟩,
    ⟨[78407, 3], [78407, 3], .contexts []⟩,
    ⟨[77131], [77131], .contexts [
        ⟨2001, false, false, [], []⟩
      ]⟩,
    ⟨[77131], [77131], .contexts [
        ⟨1118, true, false, [], [77131]⟩
      ]⟩,
    ⟨[78407, 3], [77131], .contexts [
        ⟨7537, false, false, [], []⟩,
        ⟨7536, true, false, [], [3]⟩,
        ⟨107, false, false, [78259], []⟩,
        ⟨109, false, false, [78259], []⟩,
        ⟨7531, false, false, [], [13]⟩,
        ⟨1997, false, false, [], []⟩,
        ⟨720, false, false, [], []⟩,
        ⟨446, false, false, [], []⟩,
        ⟨446, false, false, [], []⟩,
        ⟨7538, false, false, [], []⟩,
        ⟨7539, false, false, [], []⟩
      ]⟩,
    ⟨[1753], [1467, 275], .source 941⟩,
    ⟨[78407, 5], [78407, 5], .contexts []⟩,
    ⟨[1753], [1753], .contexts [
        ⟨24, false, false, [], [1753]⟩
      ]⟩,
    ⟨[78407, 5], [1753, 77259], .contexts [
        ⟨7542, false, false, [], []⟩,
        ⟨7536, true, false, [], [5]⟩,
        ⟨116, false, false, [78259], []⟩,
        ⟨117, false, false, [78259], []⟩,
        ⟨6772, true, false, [1468], [5, 13]⟩,
        ⟨49, false, false, [1468, 77255], [13]⟩,
        ⟨6770, false, true, [], [77255, 13]⟩,
        ⟨6768, false, false, [], [13]⟩,
        ⟨6769, false, false, [], [13]⟩,
        ⟨6769, false, false, [], [13]⟩,
        ⟨1735, false, false, [1467], []⟩,
        ⟨7541, true, false, [], [77259]⟩,
        ⟨1749, false, false, [1753], []⟩,
        ⟨7543, true, false, [], [77259]⟩
      ]⟩,
    ⟨[1755], [1752], .source 942⟩,
    ⟨[77259, 5], [1755, 78407], .contexts [
        ⟨7544, true, false, [1752], [5]⟩,
        ⟨49, false, false, [1752, 78407], []⟩,
        ⟨7545, true, false, [], [78407]⟩
      ]⟩,
    ⟨[78407, 9], [1063, 78407], .contexts [
        ⟨7536, true, false, [], [9]⟩,
        ⟨130, false, false, [78259], []⟩,
        ⟨131, false, false, [78259], []⟩,
        ⟨6760, false, false, [], [13]⟩,
        ⟨6760, false, false, [], [13]⟩,
        ⟨6751, true, false, [], [9, 13]⟩,
        ⟨1112, false, false, [77129], [13]⟩,
        ⟨1113, false, false, [77129], [13]⟩,
        ⟨4883, false, false, [], [3, 13]⟩,
        ⟨6747, false, false, [1063], [13]⟩,
        ⟨6758, false, false, [], [13]⟩,
        ⟨6759, false, false, [], [13]⟩,
        ⟨6756, false, false, [1063], [13]⟩,
        ⟨5837, true, false, [], [78259, 13]⟩,
        ⟨6758, false, false, [], [13]⟩,
        ⟨6759, false, false, [], [13]⟩,
        ⟨6759, false, false, [], [13]⟩,
        ⟨7533, false, false, [1063], []⟩
      ]⟩,
    ⟨[78407], [78407], .contexts []⟩,
    ⟨[1279, 77329], [1279, 77329], .contexts []⟩,
    ⟨[1279, 77329], [1279, 77329], .contexts []⟩,
    ⟨[78407, 11], [78407, 11], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 118. -/
def y322TCContextRaw118 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1279, 77329], [1279, 77329], .contexts [
        ⟨3441, false, false, [1279], []⟩
      ]⟩,
    ⟨[1279, 77329], [1279, 77329], .contexts [
        ⟨6765, true, false, [], [77329]⟩
      ]⟩,
    ⟨[78407, 11], [1279, 77329], .contexts [
        ⟨7551, false, false, [], []⟩,
        ⟨7536, true, false, [], [11]⟩,
        ⟨137, false, false, [78259], []⟩,
        ⟨138, false, false, [78259], []⟩,
        ⟨6766, false, false, [], [13]⟩,
        ⟨1313, false, false, [1279], []⟩,
        ⟨7549, false, false, [], []⟩,
        ⟨7550, false, false, [], []⟩,
        ⟨7552, false, false, [], []⟩,
        ⟨7553, false, false, [], []⟩
      ]⟩,
    ⟨[78407, 11], [1279, 77329], .contexts [
        ⟨7554, false, false, [], []⟩
      ]⟩,
    ⟨[77325, 1], [77325, 1], .contexts []⟩,
    ⟨[77325, 1], [1281, 78407], .contexts [
        ⟨7556, false, false, [], []⟩,
        ⟨1305, true, false, [], [1]⟩,
        ⟨1309, true, false, [], [11, 1]⟩,
        ⟨7550, true, false, [1278], [1, 11, 1]⟩,
        ⟨7550, true, false, [1278], [1, 11, 1]⟩,
        ⟨7549, true, false, [1278], [1, 11, 1]⟩,
        ⟨7555, true, false, [1278], [1, 11, 1]⟩,
        ⟨7551, true, false, [1278], [1, 11, 1]⟩,
        ⟨1068, false, false, [1278, 78407], []⟩,
        ⟨7548, false, false, [1278], []⟩,
        ⟨5679, true, false, [], [78407]⟩
      ]⟩,
    ⟨[78407, 1], [1279, 77325], .contexts [
        ⟨7557, true, false, [1280], [1]⟩,
        ⟨18, false, false, [1280, 77325], []⟩,
        ⟨5681, true, false, [], [77325]⟩
      ]⟩,
    ⟨[1281, 78407], [1281, 78407], .contexts []⟩,
    ⟨[1757], [1281, 1063], .source 943⟩,
    ⟨[1759], [1757, 1279], .source 944⟩,
    ⟨[1759, 77321], [1759, 77321], .contexts []⟩,
    ⟨[1759, 77321], [1759, 77321], .contexts []⟩,
    ⟨[77325, 1, 9, 1, 9, 1], [1759, 77321], .contexts [
        ⟨7556, false, false, [], [9, 1, 9, 1]⟩,
        ⟨7557, false, false, [], [9, 1, 9, 1]⟩,
        ⟨7559, false, false, [], [9, 1, 9, 1]⟩,
        ⟨7559, false, false, [], [9, 1, 9, 1]⟩,
        ⟨7547, false, false, [1281], [1, 9, 1]⟩,
        ⟨7548, false, false, [1281, 1063], [1, 9, 1]⟩,
        ⟨5837, true, false, [1281], [78407, 1, 9, 1]⟩,
        ⟨7560, true, false, [], [78407, 1, 9, 1]⟩,
        ⟨7558, false, false, [1757], [9, 1]⟩,
        ⟨7561, true, false, [], [77325, 9, 1]⟩,
        ⟨1301, false, false, [1759], [1]⟩,
        ⟨1298, false, false, [1759], []⟩,
        ⟨7562, false, false, [], []⟩,
        ⟨7563, false, false, [], []⟩
      ]⟩,
    ⟨[1, 9, 1, 9, 1, 9], [], .contexts [
        ⟨785, false, false, [], []⟩
      ]⟩,
    ⟨[1761], [1758], .source 945⟩,
    ⟨[1758], [1758], .contexts []⟩,
    ⟨[1761], [1758], .contexts [
        ⟨7566, false, false, [], []⟩,
        ⟨7567, false, false, [], []⟩,
        ⟨7567, false, false, [], []⟩
      ]⟩,
    ⟨[1759], [1760], .contexts [
        ⟨7566, true, true, [], []⟩
      ]⟩,
    ⟨[1759], [1759], .contexts []⟩,
    ⟨[1759], [1759], .contexts []⟩,
    ⟨[1759], [1759], .contexts []⟩,
    ⟨[77323], [1759, 77321], .contexts [
        ⟨2659, true, false, [], []⟩,
        ⟨7568, false, false, [1760], [77325, 9]⟩,
        ⟨2655, true, false, [1760, 1758], [9]⟩,
        ⟨7565, true, false, [1760, 1758, 77325], [9]⟩,
        ⟨7564, false, false, [1760, 1758], [9, 9]⟩,
        ⟨76, false, false, [1760, 77321], []⟩,
        ⟨7569, true, false, [], [77321]⟩,
        ⟨7562, false, false, [], []⟩,
        ⟨7572, true, false, [], [77321]⟩,
        ⟨7571, true, false, [], [77321]⟩,
        ⟨7570, true, false, [], [77321]⟩
      ]⟩,
    ⟨[77323], [1759, 77321], .contexts [
        ⟨7573, false, false, [], []⟩,
        ⟨7563, false, false, [], []⟩
      ]⟩,
    ⟨[1763], [1761, 499], .source 946⟩,
    ⟨[1765], [1763, 1759], .source 947⟩,
    ⟨[77321, 13], [1765, 77321], .contexts [
        ⟨7573, true, false, [1758], [13]⟩,
        ⟨1301, true, false, [1758], [13]⟩,
        ⟨2658, true, false, [1758, 500], [9, 13]⟩,
        ⟨2658, true, false, [1758, 500], [9, 13]⟩,
        ⟨2657, true, false, [1758, 500], [9, 13]⟩,
        ⟨2654, true, false, [1758, 500], [9, 13]⟩,
        ⟨1650, false, false, [1758, 500, 77325], []⟩,
        ⟨2660, false, false, [1758, 500], []⟩,
        ⟨2659, false, false, [1758, 500], []⟩,
        ⟨2661, false, false, [1758, 500], []⟩,
        ⟨2650, true, false, [1758], [77323]⟩,
        ⟨7574, false, false, [1758, 499], []⟩,
        ⟨7566, true, false, [], [499, 1759, 77321]⟩,
        ⟨7575, true, false, [], [1759, 77321]⟩,
        ⟨7576, true, false, [], [77321]⟩
      ]⟩,
    ⟨[1767], [1761, 1297], .source 948⟩,
    ⟨[77321, 3], [1767, 77685], .contexts [
        ⟨7573, true, false, [1758], [3]⟩,
        ⟨5724, true, false, [1758, 1298], [3]⟩,
        ⟨35, false, false, [1758, 1298, 77685], []⟩,
        ⟨5717, false, true, [1758], [77685]⟩,
        ⟨5721, false, false, [1758], []⟩,
        ⟨7566, true, false, [], [1297, 77685]⟩,
        ⟨7578, true, false, [], [77685]⟩
      ]⟩,
    ⟨[77321, 5], [77319], .contexts [
        ⟨1387, false, false, [], []⟩,
        ⟨1388, false, false, [], []⟩,
        ⟨1293, false, false, [], []⟩,
        ⟨1293, false, false, [], []⟩
      ]⟩,
    ⟨[77321, 1], [1759, 77321], .contexts [
        ⟨1296, false, false, [], []⟩,
        ⟨7574, false, false, [], []⟩,
        ⟨7563, false, false, [], []⟩,
        ⟨7563, false, false, [], []⟩
      ]⟩,
    ⟨[1759, 77319], [1759, 77319], .contexts []⟩,
    ⟨[1759, 77319], [1759, 77319], .contexts []⟩,
    ⟨[77319, 1], [77319, 1], .contexts []⟩,
    ⟨[77319], [77319], .contexts []⟩,
    ⟨[1765, 77321], [1765, 77321], .contexts []⟩,
    ⟨[1765, 77319], [1765, 77319], .contexts []⟩,
    ⟨[1765, 77319], [1765, 77319], .contexts []⟩,
    ⟨[77319, 13], [77319, 13], .contexts []⟩,
    ⟨[1769], [1759, 1767], .source 949⟩,
    ⟨[1767, 77685], [1767, 77685], .contexts []⟩,
    ⟨[77683, 3], [77683, 3], .contexts []⟩,
    ⟨[77683], [77683], .contexts []⟩,
    ⟨[1771], [1768], .source 950⟩,
    ⟨[1773], [1771, 1767], .source 951⟩,
    ⟨[77683, 3], [1773, 77683], .contexts [
        ⟨7592, false, false, [], []⟩,
        ⟨3856, true, false, [], [3]⟩,
        ⟨7590, false, false, [1768], [77685, 1, 3]⟩,
        ⟨7579, true, false, [1768, 1759], [1, 3]⟩,
        ⟨7581, true, false, [1768], [3, 1, 3]⟩,
        ⟨852, false, false, [1768, 77321], []⟩,
        ⟨853, false, false, [1768, 77321], []⟩,
        ⟨7579, false, false, [1768], [1]⟩,
        ⟨7591, false, false, [1768], [1]⟩,
        ⟨7591, false, false, [1768], [1]⟩,
        ⟨3856, false, false, [1768, 1767], []⟩,
        ⟨7593, false, false, [1768, 1767], []⟩,
        ⟨7594, true, false, [], [1767, 77683]⟩,
        ⟨7595, true, false, [], [77683]⟩
      ]⟩,
    ⟨[77319, 1, 3, 1], [1759, 77315], .contexts [
        ⟨7584, false, false, [], [3, 1]⟩,
        ⟨7584, false, false, [], [3, 1]⟩,
        ⟨7580, true, false, [], [1, 3, 1]⟩,
        ⟨256, false, false, [77321], [3, 1]⟩,
        ⟨257, false, false, [77321], [3, 1]⟩,
        ⟨7581, false, false, [], [5, 3, 1]⟩,
        ⟨1294, false, false, [1759], [3, 1]⟩,
        ⟨7582, false, false, [], [3, 1]⟩,
        ⟨7583, false, false, [], [3, 1]⟩,
        ⟨7585, false, false, [1759], [3, 1]⟩,
        ⟨7572, true, false, [], [77319, 3, 1]⟩,
        ⟨7571, true, false, [], [77319, 3, 1]⟩,
        ⟨24, true, false, [], [1759, 77319, 3, 1]⟩,
        ⟨7582, false, false, [], [3, 1]⟩,
        ⟨7583, false, false, [], [3, 1]⟩,
        ⟨7583, false, false, [], [3, 1]⟩,
        ⟨1291, false, false, [1759], [1]⟩,
        ⟨1288, false, false, [1759], []⟩
      ]⟩,
    ⟨[77319, 3], [77317], .contexts [
        ⟨1389, false, false, [], []⟩,
        ⟨1390, false, false, [], []⟩,
        ⟨1290, false, false, [], []⟩,
        ⟨1290, false, false, [], []⟩
      ]⟩,
    ⟨[77315, 3], [77315, 3], .contexts []⟩,
    ⟨[77315], [77315], .contexts []⟩,
    ⟨[77319, 13, 3], [1765, 77317], .contexts [
        ⟨7589, false, false, [], [3]⟩,
        ⟨7589, false, false, [], [3]⟩,
        ⟨7580, true, false, [], [13, 3]⟩,
        ⟨283, false, false, [77321], [3]⟩,
        ⟨284, false, false, [77321], [3]⟩,
        ⟨7577, false, false, [], [5, 3]⟩,
        ⟨7586, false, false, [], [5, 3]⟩,
        ⟨7586, false, false, [], [5, 3]⟩,
        ⟨1294, false, false, [1765], [3]⟩,
        ⟨7587, false, false, [], [3]⟩,
        ⟨7588, false, false, [], [3]⟩,
        ⟨7585, false, false, [1765], [3]⟩,
        ⟨24, true, false, [], [1765, 77319, 3]⟩,
        ⟨7587, false, false, [], [3]⟩,
        ⟨7588, false, false, [], [3]⟩,
        ⟨7588, false, false, [], [3]⟩,
        ⟨1291, false, false, [1765], []⟩
      ]⟩,
    ⟨[77317], [77317], .contexts []⟩,
    ⟨[1775], [1764], .source 952⟩,
    ⟨[1764], [1764], .contexts []⟩,
    ⟨[1773, 77683], [1773, 77683], .contexts []⟩,
    ⟨[77683, 3], [1773, 77683], .contexts [
        ⟨7592, false, false, [], []⟩,
        ⟨7596, false, false, [], []⟩,
        ⟨7605, false, false, [], []⟩,
        ⟨7605, false, false, [], []⟩
      ]⟩,
    ⟨[77683, 5], [77681], .contexts [
        ⟨3925, false, false, [], []⟩,
        ⟨3926, false, false, [], []⟩,
        ⟨3851, false, false, [], []⟩,
        ⟨3851, false, false, [], []⟩
      ]⟩,
    ⟨[77679, 5], [77679, 5], .contexts []⟩,
    ⟨[77679], [77679], .contexts []⟩,
    ⟨[1777], [1772], .source 953⟩,
    ⟨[1772], [1772], .contexts []⟩,
    ⟨[1777], [1772], .contexts [
        ⟨7610, false, false, [], []⟩,
        ⟨7611, false, false, [], []⟩,
        ⟨7611, false, false, [], []⟩
      ]⟩,
    ⟨[1761, 77315], [1761, 77315], .contexts []⟩,
    ⟨[1761, 77313, 3], [77315, 14], .contexts [
        ⟨1284, true, false, [1761], [3]⟩,
        ⟨7613, true, false, [], [15, 3]⟩,
        ⟨7613, true, false, [], [15, 3]⟩,
        ⟨7568, false, false, [], [77315, 15, 3]⟩,
        ⟨7600, true, false, [1758], [15, 3]⟩,
        ⟨1287, true, false, [1758], [15, 3]⟩,
        ⟨1287, true, false, [1758], [15, 3]⟩,
        ⟨1392, true, false, [1758], [15, 3]⟩,
        ⟨1391, true, false, [1758], [15, 3]⟩,
        ⟨7598, true, false, [1758], [1, 15, 3]⟩,
        ⟨853, true, false, [1758, 77319], [15, 3]⟩,
        ⟨852, true, false, [1758, 77319], [15, 3]⟩,
        ⟨7597, false, false, [1758], [3, 15, 3]⟩,
        ⟨7599, true, false, [], [15, 3]⟩,
        ⟨7599, true, false, [], [15, 3]⟩,
        ⟨900, false, false, [77315], []⟩
      ]⟩,
    ⟨[77313, 3], [77313, 3], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 119. -/
def y322TCContextRaw119 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[77313], [77313], .contexts []⟩,
    ⟨[1760], [1760], .contexts []⟩,
    ⟨[1777, 77679], [1777, 77679], .contexts []⟩,
    ⟨[77679, 5], [1777, 77679], .contexts [
        ⟨7608, false, false, [], []⟩,
        ⟨7608, false, false, [], []⟩,
        ⟨3848, true, false, [], [5]⟩,
        ⟨3852, true, false, [], [3, 5]⟩,
        ⟨7606, true, false, [1772], [5, 3, 5]⟩,
        ⟨4744, false, false, [1772, 77683], []⟩,
        ⟨766, false, false, [1772, 77683], []⟩,
        ⟨7607, false, false, [1772], [3]⟩,
        ⟨3927, false, false, [1772], []⟩,
        ⟨3928, false, false, [1772], []⟩,
        ⟨3847, false, false, [1772], []⟩,
        ⟨3847, false, false, [1772], []⟩,
        ⟨7609, false, false, [1772], []⟩,
        ⟨7612, true, false, [], [77679]⟩,
        ⟨7618, false, false, [], []⟩,
        ⟨7618, false, false, [], []⟩
      ]⟩,
    ⟨[77677, 5], [77677, 5], .contexts []⟩,
    ⟨[77677], [77677], .contexts []⟩,
    ⟨[1776], [1776], .contexts []⟩,
    ⟨[1773], [1776], .contexts [
        ⟨7610, true, true, [], []⟩,
        ⟨7622, false, false, [], []⟩,
        ⟨7622, false, false, [], []⟩
      ]⟩,
    ⟨[1759, 77313], [1759, 77313], .contexts []⟩,
    ⟨[77313, 13], [77311], .contexts [
        ⟨1395, false, false, [], []⟩,
        ⟨1396, false, false, [], []⟩,
        ⟨1280, false, false, [], []⟩,
        ⟨1280, false, false, [], []⟩
      ]⟩,
    ⟨[77313, 12], [77313, 13], .contexts [
        ⟨108, false, false, [77313], []⟩
      ]⟩,
    ⟨[1759, 77311, 3], [77313, 13], .contexts [
        ⟨1281, true, false, [1759], [3]⟩,
        ⟨7624, true, false, [], [13, 3]⟩,
        ⟨7624, true, false, [], [13, 3]⟩,
        ⟨7570, false, false, [], [77313, 13, 3]⟩,
        ⟨7569, false, false, [], [77313, 13, 3]⟩,
        ⟨7617, false, false, [], [77313, 13, 3]⟩,
        ⟨7617, false, false, [], [77313, 13, 3]⟩,
        ⟨7616, true, false, [1760], [13, 3]⟩,
        ⟨1283, true, false, [1760], [13, 3]⟩,
        ⟨1283, true, false, [1760], [13, 3]⟩,
        ⟨1394, true, false, [1760], [13, 3]⟩,
        ⟨1393, true, false, [1760], [13, 3]⟩,
        ⟨20, true, false, [1760, 77315], [13, 3]⟩,
        ⟨7614, true, false, [1760], [13, 3]⟩,
        ⟨7615, true, false, [], [13, 3]⟩,
        ⟨7615, true, false, [], [13, 3]⟩,
        ⟨932, false, false, [77313], []⟩,
        ⟨7626, false, false, [], []⟩
      ]⟩,
    ⟨[77311], [77311], .contexts []⟩,
    ⟨[1773, 77677], [1773, 77677], .contexts []⟩,
    ⟨[77677, 5, 15], [1773, 77675], .contexts [
        ⟨7620, false, false, [], [15]⟩,
        ⟨7620, false, false, [], [15]⟩,
        ⟨3845, true, false, [], [5, 15]⟩,
        ⟨7619, true, false, [1776], [1, 5, 15]⟩,
        ⟨1509, false, false, [1776, 77679], [15]⟩,
        ⟨19, false, false, [1776, 77679], [15]⟩,
        ⟨3929, false, false, [1776], [15]⟩,
        ⟨3930, false, false, [1776], [15]⟩,
        ⟨3844, false, false, [1776], [15]⟩,
        ⟨3844, false, false, [1776], [15]⟩,
        ⟨7621, false, false, [1776], [15]⟩,
        ⟨7623, true, false, [], [77677, 15]⟩,
        ⟨7629, false, false, [], [15]⟩,
        ⟨7629, false, false, [], [15]⟩,
        ⟨3841, false, false, [1773], []⟩
      ]⟩,
    ⟨[77677, 15], [77675], .contexts [
        ⟨3932, false, false, [], []⟩,
        ⟨3933, false, false, [], []⟩,
        ⟨3840, false, false, [], []⟩,
        ⟨3840, false, false, [], []⟩
      ]⟩,
    ⟨[77677, 14], [77677, 15], .contexts [
        ⟨20, false, false, [77677], []⟩
      ]⟩,
    ⟨[77675, 5], [77675, 5], .contexts []⟩,
    ⟨[77675], [77675], .contexts []⟩,
    ⟨[1777, 77675], [1777, 77675], .contexts []⟩,
    ⟨[77675, 5], [1777, 77675], .contexts [
        ⟨7633, false, false, [], []⟩,
        ⟨7633, false, false, [], []⟩,
        ⟨7630, true, false, [1772], [5]⟩,
        ⟨2006, false, false, [1772, 77677], []⟩,
        ⟨7632, false, false, [1772], []⟩,
        ⟨7631, false, false, [1772], []⟩,
        ⟨7634, false, false, [1772], []⟩,
        ⟨7612, true, false, [], [77675]⟩,
        ⟨7635, false, false, [], []⟩,
        ⟨7635, false, false, [], []⟩
      ]⟩,
    ⟨[77673, 5], [77673, 5], .contexts []⟩,
    ⟨[1773, 77673], [1773, 77673], .contexts []⟩,
    ⟨[77673, 5, 1], [1773, 77671], .contexts [
        ⟨7637, false, false, [], [1]⟩,
        ⟨7637, false, false, [], [1]⟩,
        ⟨3838, true, false, [], [5, 1]⟩,
        ⟨7636, true, false, [1776], [13, 5, 1]⟩,
        ⟨1578, false, false, [1776, 77675], [1]⟩,
        ⟨108, false, false, [1776, 77675], [1]⟩,
        ⟨3934, false, false, [1776], [1]⟩,
        ⟨3935, false, false, [1776], [1]⟩,
        ⟨3837, false, false, [1776], [1]⟩,
        ⟨3837, false, false, [1776], [1]⟩,
        ⟨7623, true, false, [], [77673, 1]⟩,
        ⟨7638, false, false, [], [1]⟩,
        ⟨7638, false, false, [], [1]⟩,
        ⟨3835, false, false, [1773], []⟩
      ]⟩,
    ⟨[77671, 5], [77671, 5], .contexts []⟩,
    ⟨[1777, 77671], [1777, 77671], .contexts []⟩,
    ⟨[1777, 77669, 5], [77671, 11], .contexts [
        ⟨3832, true, false, [1777], [5]⟩,
        ⟨7641, true, false, [], [11, 5]⟩,
        ⟨7641, true, false, [], [11, 5]⟩,
        ⟨7612, false, false, [], [77671, 11, 5]⟩,
        ⟨3834, true, false, [1772], [11, 5]⟩,
        ⟨3834, true, false, [1772], [11, 5]⟩,
        ⟨3937, true, false, [1772], [11, 5]⟩,
        ⟨3936, true, false, [1772], [11, 5]⟩,
        ⟨19, true, false, [1772, 77673], [11, 5]⟩,
        ⟨1509, true, false, [1772, 77673], [11, 5]⟩,
        ⟨7639, false, false, [1772], [5, 11, 5]⟩,
        ⟨7640, true, false, [], [11, 5]⟩,
        ⟨7640, true, false, [], [11, 5]⟩,
        ⟨1645, false, false, [77671], []⟩,
        ⟨91, false, false, [77671], []⟩
      ]⟩,
    ⟨[77669, 5], [77669, 5], .contexts []⟩,
    ⟨[1773, 77669], [1773, 77669], .contexts []⟩,
    ⟨[1773, 77667], [1773, 77667], .contexts []⟩,
    ⟨[1773, 77667, 5], [77669, 9], .contexts [
        ⟨7645, true, false, [], [5]⟩,
        ⟨3828, true, false, [1773], [5]⟩,
        ⟨7644, true, false, [], [9, 5]⟩,
        ⟨7644, true, false, [], [9, 5]⟩,
        ⟨7623, false, false, [], [77669, 9, 5]⟩,
        ⟨3831, true, false, [1776], [9, 5]⟩,
        ⟨3831, true, false, [1776], [9, 5]⟩,
        ⟨3939, true, false, [1776], [9, 5]⟩,
        ⟨3938, true, false, [1776], [9, 5]⟩,
        ⟨7642, true, false, [1776], [9, 5]⟩,
        ⟨7643, true, false, [], [9, 5]⟩,
        ⟨7643, true, false, [], [9, 5]⟩,
        ⟨1672, false, false, [77669], []⟩,
        ⟨77, false, false, [77669], []⟩
      ]⟩,
    ⟨[77667, 5], [77667, 5], .contexts []⟩,
    ⟨[77667], [77667], .contexts []⟩,
    ⟨[1777, 77667], [1777, 77667], .contexts []⟩,
    ⟨[77667, 5, 1, 5], [1777, 77663], .contexts [
        ⟨7647, false, false, [], [1, 5]⟩,
        ⟨7647, false, false, [], [1, 5]⟩,
        ⟨7646, false, false, [1772], [1, 5]⟩,
        ⟨3940, false, false, [1772], [1, 5]⟩,
        ⟨3941, false, false, [1772], [1, 5]⟩,
        ⟨3827, false, false, [1772], [1, 5]⟩,
        ⟨3827, false, false, [1772], [1, 5]⟩,
        ⟨7648, false, false, [1772], [1, 5]⟩,
        ⟨7612, true, false, [], [77667, 1, 5]⟩,
        ⟨7649, false, false, [], [1, 5]⟩,
        ⟨7649, false, false, [], [1, 5]⟩,
        ⟨3824, false, false, [1777], [5]⟩,
        ⟨3821, false, false, [1777], []⟩
      ]⟩,
    ⟨[78409], [78259, 15], .source 39269⟩,
    ⟨[78259, 15], [78409], .contexts [
        ⟨7651, true, false, [], []⟩
      ]⟩,
    ⟨[78409, 15], [78259], .contexts [
        ⟨7652, true, false, [], [15]⟩,
        ⟨3, false, false, [78259], []⟩,
        ⟨6750, false, false, [], []⟩
      ]⟩,
    ⟨[78409], [78409], .contexts []⟩,
    ⟨[78259, 15], [78409], .contexts [
        ⟨7652, false, false, [], []⟩,
        ⟨7654, false, false, [], []⟩,
        ⟨7654, false, false, [], []⟩
      ]⟩,
    ⟨[77129, 15], [539, 77865], .contexts [
        ⟨4863, false, false, [], []⟩
      ]⟩,
    ⟨[539, 77865], [539, 77865], .contexts []⟩,
    ⟨[539, 77865], [539, 77865], .contexts []⟩,
    ⟨[539, 77865], [539, 77865], .contexts [
        ⟨4854, false, false, [539], []⟩
      ]⟩,
    ⟨[539, 77865], [539, 77865], .contexts [
        ⟨5823, true, false, [], [77865]⟩
      ]⟩,
    ⟨[77865, 3], [537, 78409], .contexts [
        ⟨7660, true, false, [538], [3]⟩,
        ⟨7659, true, false, [538], [3]⟩,
        ⟨7658, true, false, [538], [3]⟩,
        ⟨7658, true, false, [538], [3]⟩,
        ⟨7657, true, false, [538], [3]⟩,
        ⟨7656, true, false, [538], [3]⟩,
        ⟨7531, true, false, [538], [15, 3]⟩,
        ⟨37, true, false, [538, 78259], [3]⟩,
        ⟨34, true, false, [538, 78259], [3]⟩,
        ⟨7655, false, false, [538], [3, 3]⟩,
        ⟨35, false, false, [538, 78409], []⟩,
        ⟨2792, true, false, [], [78409]⟩
      ]⟩,
    ⟨[78409, 11], [1279, 77333], .contexts [
        ⟨7655, true, false, [], [11]⟩,
        ⟨89, false, false, [78259], []⟩,
        ⟨92, false, false, [78259], []⟩,
        ⟨6766, false, false, [], [15]⟩,
        ⟨1315, false, false, [1279], []⟩,
        ⟨3398, false, false, [1279], []⟩,
        ⟨6765, true, false, [], [77333]⟩
      ]⟩,
    ⟨[78411], [78261, 5], .source 39270⟩,
    ⟨[78261, 5], [78411], .contexts [
        ⟨7663, true, false, [], []⟩
      ]⟩,
    ⟨[78411], [78411], .contexts []⟩,
    ⟨[78411], [78411], .contexts []⟩,
    ⟨[78261, 1], [78121], .contexts [
        ⟨6779, false, false, [], []⟩,
        ⟨6779, false, false, [], []⟩,
        ⟨6778, true, false, [], [1]⟩,
        ⟨1764, false, false, [77129], []⟩,
        ⟨1765, false, false, [77129], []⟩,
        ⟨6752, false, false, [], [7]⟩,
        ⟨6230, true, false, [], [7]⟩,
        ⟨62, false, false, [78121], []⟩,
        ⟨6228, false, false, [], []⟩,
        ⟨6227, false, false, [], []⟩,
        ⟨6228, false, false, [], []⟩,
        ⟨6228, false, false, [], []⟩,
        ⟨1118, true, false, [], [78121]⟩,
        ⟨6227, false, false, [], []⟩,
        ⟨6228, false, false, [], []⟩,
        ⟨6228, false, false, [], []⟩
      ]⟩,
    ⟨[78265], [78265], .contexts []⟩,
    ⟨[78265], [78265], .contexts [
        ⟨1118, true, false, [], [78265]⟩
      ]⟩,
    ⟨[78261, 7], [77129], .contexts [
        ⟨6774, true, false, [], [7]⟩,
        ⟨62, false, false, [77129], []⟩,
        ⟨442, false, false, [], []⟩,
        ⟨721, false, false, [], []⟩,
        ⟨442, false, false, [], []⟩,
        ⟨442, false, false, [], []⟩
      ]⟩,
    ⟨[78413], [78261, 13], .source 39271⟩,
    ⟨[78261, 13], [78413], .contexts [
        ⟨7671, true, false, [], []⟩
      ]⟩,
    ⟨[78413], [78413], .contexts []⟩,
    ⟨[78413], [78413], .contexts []⟩,
    ⟨[78413, 7], [78413, 7], .contexts []⟩,
    ⟨[78413, 7], [77131], .contexts [
        ⟨7675, false, false, [], []⟩,
        ⟨7674, true, false, [], [7]⟩,
        ⟨7674, true, false, [], [7]⟩,
        ⟨7673, true, false, [], [7]⟩,
        ⟨7672, true, false, [], [7]⟩,
        ⟨124, false, false, [78261], []⟩,
        ⟨125, false, false, [78261], []⟩,
        ⟨7670, false, false, [], [13]⟩,
        ⟨1997, false, false, [], []⟩,
        ⟨720, false, false, [], []⟩,
        ⟨446, false, false, [], []⟩,
        ⟨446, false, false, [], []⟩,
        ⟨7538, false, false, [], []⟩,
        ⟨7539, false, false, [], []⟩
      ]⟩,
    ⟨[78415], [78261, 15], .source 39272⟩,
    ⟨[78415], [78415], .contexts []⟩,
    ⟨[78415], [78415], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 120. -/
def y322TCContextRaw120 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78261, 15], [78415], .contexts [
        ⟨7677, true, false, [], []⟩,
        ⟨7678, false, false, [], []⟩,
        ⟨7679, false, false, [], []⟩,
        ⟨7679, false, false, [], []⟩
      ]⟩,
    ⟨[78271], [78271], .contexts []⟩,
    ⟨[78271], [78271], .contexts [
        ⟨1118, true, false, [], [78271]⟩
      ]⟩,
    ⟨[78415], [78415], .contexts []⟩,
    ⟨[78417], [77693, 5], .source 39273⟩,
    ⟨[77693, 5], [78417], .contexts [
        ⟨7684, true, false, [], []⟩
      ]⟩,
    ⟨[78417, 5], [77693], .contexts [
        ⟨7685, true, false, [], [5]⟩,
        ⟨49, false, false, [77693], []⟩,
        ⟨3871, false, false, [], []⟩
      ]⟩,
    ⟨[78417], [78417], .contexts []⟩,
    ⟨[77693, 5], [78417], .contexts [
        ⟨7685, false, false, [], []⟩,
        ⟨7687, false, false, [], []⟩,
        ⟨7687, false, false, [], []⟩
      ]⟩,
    ⟨[1261, 78417], [1261, 78417], .contexts []⟩,
    ⟨[1261, 78417], [1261, 78417], .contexts []⟩,
    ⟨[78417, 1], [78417, 1], .contexts []⟩,
    ⟨[78417], [78417], .contexts []⟩,
    ⟨[78417, 1], [1261, 78417], .contexts [
        ⟨7691, false, false, [], []⟩,
        ⟨7688, true, false, [], [1]⟩,
        ⟨256, false, false, [77693], []⟩,
        ⟨257, false, false, [77693], []⟩,
        ⟨5575, false, false, [], [5]⟩,
        ⟨7685, false, false, [1261], []⟩,
        ⟨7689, false, false, [], []⟩,
        ⟨7690, false, false, [], []⟩,
        ⟨7692, false, false, [1261], []⟩,
        ⟨5579, true, false, [], [78417]⟩
      ]⟩,
    ⟨[1245, 77699], [1245, 77699], .contexts []⟩,
    ⟨[1245, 77699], [1245, 77699], .contexts []⟩,
    ⟨[1779], [1245, 843], .source 954⟩,
    ⟨[1781], [1779, 1247], .source 955⟩,
    ⟨[1781, 78417], [1781, 78417], .contexts []⟩,
    ⟨[1781, 78417], [1781, 78417], .contexts []⟩,
    ⟨[78417, 3], [78417, 3], .contexts []⟩,
    ⟨[78417, 3], [1781, 78417], .contexts [
        ⟨7700, false, false, [], []⟩,
        ⟨7688, true, false, [], [3]⟩,
        ⟨264, false, false, [77693], []⟩,
        ⟨267, false, false, [77693], []⟩,
        ⟨5553, false, false, [], [5, 3, 5]⟩,
        ⟨5556, false, false, [], [5, 3, 5]⟩,
        ⟨7694, false, false, [], [5, 3, 5]⟩,
        ⟨7695, false, false, [], [5, 3, 5]⟩,
        ⟨7695, false, false, [], [5, 3, 5]⟩,
        ⟨3880, false, false, [1245], [3, 5]⟩,
        ⟨4110, false, false, [1245], [3, 5]⟩,
        ⟨7696, true, false, [], [77699, 3, 5]⟩,
        ⟨3878, false, false, [1779], [5]⟩,
        ⟨5560, false, false, [1779], [5]⟩,
        ⟨7697, true, false, [], [77693, 5]⟩,
        ⟨7685, false, false, [1781], []⟩,
        ⟨7698, false, false, [], []⟩,
        ⟨7699, false, false, [], []⟩,
        ⟨7692, false, false, [1781], []⟩
      ]⟩,
    ⟨[1781], [1781], .contexts [
        ⟨24, false, false, [], [1781]⟩
      ]⟩,
    ⟨[78417, 3], [1781, 78417], .contexts [
        ⟨7701, false, false, [], []⟩,
        ⟨7702, true, false, [], [78417]⟩
      ]⟩,
    ⟨[78417, 9], [1251, 78417], .contexts [
        ⟨7688, true, false, [], [9]⟩,
        ⟨2076, false, false, [77693], []⟩,
        ⟨2077, false, false, [77693], []⟩,
        ⟨5563, false, false, [], [5]⟩,
        ⟨5572, false, false, [], [5]⟩,
        ⟨5572, false, false, [], [5]⟩,
        ⟨7685, false, false, [1251], []⟩,
        ⟨7692, false, false, [1251], []⟩,
        ⟨24, true, false, [], [1251, 78417]⟩
      ]⟩,
    ⟨[78419], [78417, 11], .source 39274⟩,
    ⟨[78417, 11], [78419], .contexts [
        ⟨7705, true, false, [], []⟩
      ]⟩,
    ⟨[78419], [78419], .contexts []⟩,
    ⟨[78417, 11], [78419], .contexts [
        ⟨7706, false, false, [], []⟩,
        ⟨7707, false, false, [], []⟩,
        ⟨7707, false, false, [], []⟩
      ]⟩,
    ⟨[78419], [78419], .contexts []⟩,
    ⟨[1781, 78419], [1781, 78419], .contexts []⟩,
    ⟨[1781, 78419], [1781, 78419], .contexts []⟩,
    ⟨[1781, 78419], [1781, 78419], .contexts []⟩,
    ⟨[78419, 3], [78419, 3], .contexts []⟩,
    ⟨[78421], [78419, 13], .source 39275⟩,
    ⟨[78419, 13], [78421], .contexts [
        ⟨7714, true, false, [], []⟩
      ]⟩,
    ⟨[78421], [78421], .contexts []⟩,
    ⟨[78419, 13], [78421], .contexts [
        ⟨7715, false, false, [], []⟩,
        ⟨7716, false, false, [], []⟩,
        ⟨7716, false, false, [], []⟩
      ]⟩,
    ⟨[1781, 78421], [1781, 78421], .contexts []⟩,
    ⟨[1781, 78421], [1781, 78421], .contexts []⟩,
    ⟨[78419, 3, 13], [1781, 78421], .contexts [
        ⟨7713, false, false, [], [13]⟩,
        ⟨7713, false, false, [], [13]⟩,
        ⟨7708, true, false, [], [3, 13]⟩,
        ⟨335, false, false, [78417], [13]⟩,
        ⟨336, false, false, [78417], [13]⟩,
        ⟨7700, false, false, [], [11, 13]⟩,
        ⟨7703, false, false, [], [11, 13]⟩,
        ⟨7698, false, false, [], [11, 13]⟩,
        ⟨7699, false, false, [], [11, 13]⟩,
        ⟨7699, false, false, [], [11, 13]⟩,
        ⟨7706, false, false, [1781], [13]⟩,
        ⟨7710, false, false, [], [13]⟩,
        ⟨7711, false, false, [], [13]⟩,
        ⟨7712, false, false, [], [13]⟩,
        ⟨7709, false, false, [1781], [13]⟩,
        ⟨7702, true, false, [], [78419, 13]⟩,
        ⟨7710, false, false, [], [13]⟩,
        ⟨7712, false, false, [], [13]⟩,
        ⟨7712, false, false, [], [13]⟩,
        ⟨7715, false, false, [1781], []⟩,
        ⟨7718, false, false, [], []⟩,
        ⟨7719, false, false, [], []⟩
      ]⟩,
    ⟨[1781, 78421], [1781, 78421], .contexts []⟩,
    ⟨[78421, 3], [78421, 3], .contexts []⟩,
    ⟨[78421], [78421], .contexts []⟩,
    ⟨[78423], [78421, 15], .source 39276⟩,
    ⟨[78421, 15], [78423], .contexts [
        ⟨7724, true, false, [], []⟩
      ]⟩,
    ⟨[78423], [78423], .contexts []⟩,
    ⟨[78423], [78423], .contexts []⟩,
    ⟨[1781, 78423], [1781, 78423], .contexts []⟩,
    ⟨[1781, 78423], [1781, 78423], .contexts []⟩,
    ⟨[1781, 78423], [1781, 78423], .contexts []⟩,
    ⟨[78423, 3], [1781, 78423], .contexts [
        ⟨7727, true, false, [], [3]⟩,
        ⟨7727, true, false, [], [3]⟩,
        ⟨7726, true, false, [], [3]⟩,
        ⟨7725, true, false, [], [3]⟩,
        ⟨34, false, false, [78421], []⟩,
        ⟨37, false, false, [78421], []⟩,
        ⟨7722, false, false, [], [15]⟩,
        ⟨7722, false, false, [], [15]⟩,
        ⟨7717, true, false, [], [3, 15]⟩,
        ⟨107, false, false, [78419], [15]⟩,
        ⟨109, false, false, [78419], [15]⟩,
        ⟨7720, false, false, [], [15]⟩,
        ⟨7721, false, false, [], [15]⟩,
        ⟨7723, false, false, [1781], [15]⟩,
        ⟨7702, true, false, [], [78421, 15]⟩,
        ⟨7718, false, false, [], [15]⟩,
        ⟨7721, false, false, [], [15]⟩,
        ⟨7721, false, false, [], [15]⟩,
        ⟨7725, false, false, [1781], []⟩,
        ⟨7728, false, false, [], []⟩,
        ⟨7729, false, false, [], []⟩,
        ⟨7730, false, false, [], []⟩
      ]⟩,
    ⟨[78425], [78423, 1], .source 39277⟩,
    ⟨[78423, 1], [78425], .contexts [
        ⟨7732, true, false, [], []⟩
      ]⟩,
    ⟨[78425, 1], [78423], .contexts [
        ⟨7733, true, false, [], [1]⟩,
        ⟨18, false, false, [78423], []⟩,
        ⟨7727, false, false, [], []⟩
      ]⟩,
    ⟨[78427], [78425, 3], .source 39278⟩,
    ⟨[78425, 3], [78427], .contexts [
        ⟨7735, true, false, [], []⟩
      ]⟩,
    ⟨[78427], [78427], .contexts []⟩,
    ⟨[78427], [78427], .contexts []⟩,
    ⟨[1781, 78425], [1781, 78425], .contexts []⟩,
    ⟨[1781, 78425], [1781, 78425], .contexts []⟩,
    ⟨[1781, 78425], [1781, 78425], .contexts []⟩,
    ⟨[1781, 78427], [1781, 78427], .contexts []⟩,
    ⟨[1781, 78427], [1781, 78427], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 121. -/
def y322TCContextRaw121 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1781, 78427], [1781, 78427], .contexts []⟩,
    ⟨[78427, 1], [78427, 1], .contexts []⟩,
    ⟨[78427, 1], [1781, 78427], .contexts [
        ⟨7745, false, false, [], []⟩,
        ⟨7738, true, false, [], [1]⟩,
        ⟨7738, true, false, [], [1]⟩,
        ⟨7737, true, false, [], [1]⟩,
        ⟨7736, true, false, [], [1]⟩,
        ⟨213, false, false, [78425], []⟩,
        ⟨216, false, false, [78425], []⟩,
        ⟨7734, false, false, [], [3, 1, 3]⟩,
        ⟨7726, false, false, [], [3, 1, 3]⟩,
        ⟨7727, false, false, [], [3, 1, 3]⟩,
        ⟨7727, false, false, [], [3, 1, 3]⟩,
        ⟨7731, false, false, [], [1, 3]⟩,
        ⟨7702, true, false, [], [78423, 1, 3]⟩,
        ⟨7728, false, false, [], [1, 3]⟩,
        ⟨7730, false, false, [], [1, 3]⟩,
        ⟨7730, false, false, [], [1, 3]⟩,
        ⟨7733, false, false, [1781], [3]⟩,
        ⟨7739, false, false, [], [3]⟩,
        ⟨7740, false, false, [], [3]⟩,
        ⟨7741, false, false, [], [3]⟩,
        ⟨7736, false, false, [1781], []⟩,
        ⟨7742, false, false, [], []⟩,
        ⟨7743, false, false, [], []⟩,
        ⟨7744, false, false, [], []⟩
      ]⟩,
    ⟨[78429], [78427, 5], .source 39279⟩,
    ⟨[78427, 5], [78429], .contexts [
        ⟨7747, true, false, [], []⟩
      ]⟩,
    ⟨[78429], [78429], .contexts []⟩,
    ⟨[78429], [78429], .contexts []⟩,
    ⟨[1781, 78429], [1781, 78429], .contexts []⟩,
    ⟨[1781, 78429], [1781, 78429], .contexts []⟩,
    ⟨[78431], [78429, 9], .source 39280⟩,
    ⟨[78429, 9], [78431], .contexts [
        ⟨7753, true, false, [], []⟩
      ]⟩,
    ⟨[78431, 9], [78429], .contexts [
        ⟨7754, true, false, [], [9]⟩,
        ⟨76, false, false, [78429], []⟩,
        ⟨7750, false, false, [], []⟩
      ]⟩,
    ⟨[78433], [78431, 11], .source 39281⟩,
    ⟨[78431, 11], [78433], .contexts [
        ⟨7756, true, false, [], []⟩
      ]⟩,
    ⟨[78431], [78431], .contexts []⟩,
    ⟨[78435], [78433, 1], .source 39282⟩,
    ⟨[78433, 1], [78435], .contexts [
        ⟨7759, true, false, [], []⟩
      ]⟩,
    ⟨[78433], [78433], .contexts []⟩,
    ⟨[78435, 1], [78433], .contexts [
        ⟨7760, true, false, [], [1]⟩,
        ⟨18, false, false, [78433], []⟩,
        ⟨7761, false, false, [], []⟩
      ]⟩,
    ⟨[78437], [78435, 13], .source 39283⟩,
    ⟨[78435, 13], [78437], .contexts [
        ⟨7763, true, false, [], []⟩
      ]⟩,
    ⟨[78435], [78435], .contexts []⟩,
    ⟨[78439], [78437, 15], .source 39284⟩,
    ⟨[78437, 15], [78439], .contexts [
        ⟨7766, true, false, [], []⟩
      ]⟩,
    ⟨[78437], [78437], .contexts []⟩,
    ⟨[78441], [78439, 1], .source 39285⟩,
    ⟨[78439, 1], [78441], .contexts [
        ⟨7769, true, false, [], []⟩
      ]⟩,
    ⟨[78439], [78439], .contexts []⟩,
    ⟨[78443], [78441, 3], .source 39286⟩,
    ⟨[78441, 3], [78443], .contexts [
        ⟨7772, true, false, [], []⟩
      ]⟩,
    ⟨[78441], [78441], .contexts []⟩,
    ⟨[78445], [78443, 5], .source 39287⟩,
    ⟨[78443], [78443], .contexts []⟩,
    ⟨[78447], [78445, 1], .source 39288⟩,
    ⟨[78445], [78445], .contexts []⟩,
    ⟨[78449], [78447, 9], .source 39289⟩,
    ⟨[78447], [78447], .contexts []⟩,
    ⟨[78451], [78449, 11], .source 39290⟩,
    ⟨[78449], [78449], .contexts []⟩,
    ⟨[78453], [78451, 1], .source 39291⟩,
    ⟨[78451], [78451], .contexts []⟩,
    ⟨[78455], [78453, 13], .source 39292⟩,
    ⟨[78453], [78453], .contexts []⟩,
    ⟨[78457], [78455, 15], .source 39293⟩,
    ⟨[78455], [78455], .contexts []⟩,
    ⟨[78459], [78457, 1], .source 39294⟩,
    ⟨[78457], [78457], .contexts []⟩,
    ⟨[78461], [78459, 3], .source 39295⟩,
    ⟨[78459], [78459], .contexts []⟩,
    ⟨[78463], [78461, 5], .source 39296⟩,
    ⟨[78461], [78461], .contexts []⟩,
    ⟨[78465], [78463, 1], .source 39297⟩,
    ⟨[78463], [78463], .contexts []⟩,
    ⟨[78467], [78465, 9], .source 39298⟩,
    ⟨[78465], [78465], .contexts []⟩,
    ⟨[78469], [78467, 11], .source 39299⟩,
    ⟨[78467], [78467], .contexts []⟩,
    ⟨[78471], [78469, 1], .source 39300⟩,
    ⟨[78469], [78469], .contexts []⟩,
    ⟨[78473], [78471, 13], .source 39301⟩,
    ⟨[78471], [78471], .contexts []⟩,
    ⟨[78475], [78473, 15], .source 39302⟩,
    ⟨[78473], [78473], .contexts []⟩,
    ⟨[78477], [78475, 1], .source 39303⟩]

/-- Exact literal claimed equations and contextual derivations, block 122. -/
def y322TCContextRaw122 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78475], [78475], .contexts []⟩,
    ⟨[78479], [78477, 3], .source 39304⟩,
    ⟨[78477], [78477], .contexts []⟩,
    ⟨[78481], [78479, 5], .source 39305⟩,
    ⟨[78479], [78479], .contexts []⟩,
    ⟨[78483], [78481, 1], .source 39306⟩,
    ⟨[78481], [78481], .contexts []⟩,
    ⟨[78485], [78483, 9], .source 39307⟩,
    ⟨[78483], [78483], .contexts []⟩,
    ⟨[78487], [78485, 11], .source 39308⟩,
    ⟨[78485], [78485], .contexts []⟩,
    ⟨[78489], [78487, 1], .source 39309⟩,
    ⟨[78487], [78487], .contexts []⟩,
    ⟨[78491], [78489, 13], .source 39310⟩,
    ⟨[78489], [78489], .contexts []⟩,
    ⟨[78493], [78491, 15], .source 39311⟩,
    ⟨[78491], [78491], .contexts []⟩,
    ⟨[78495], [78493, 1], .source 39312⟩,
    ⟨[78493], [78493], .contexts []⟩,
    ⟨[78497], [78495, 3], .source 39313⟩,
    ⟨[78495], [78495], .contexts []⟩,
    ⟨[78499], [78497, 5], .source 39314⟩,
    ⟨[78497], [78497], .contexts []⟩,
    ⟨[78501], [78499, 1], .source 39315⟩,
    ⟨[78499], [78499], .contexts []⟩,
    ⟨[78503], [78501, 9], .source 39316⟩,
    ⟨[78501], [78501], .contexts []⟩,
    ⟨[78505], [78503, 11], .source 39317⟩,
    ⟨[78503], [78503], .contexts []⟩,
    ⟨[78507], [78505, 1], .source 39318⟩,
    ⟨[78505], [78505], .contexts []⟩,
    ⟨[78509], [78507, 13], .source 39319⟩,
    ⟨[78507], [78507], .contexts []⟩,
    ⟨[78511], [78509, 15], .source 39320⟩,
    ⟨[78509], [78509], .contexts []⟩,
    ⟨[78513], [78511, 1], .source 39321⟩,
    ⟨[78511, 1], [78513], .contexts [
        ⟨7843, true, false, [], []⟩
      ]⟩,
    ⟨[78511], [78511], .contexts []⟩,
    ⟨[78513, 1], [78511], .contexts [
        ⟨7844, true, false, [], [1]⟩,
        ⟨18, false, false, [78511], []⟩,
        ⟨7845, false, false, [], []⟩
      ]⟩,
    ⟨[78515], [78513, 3], .source 39322⟩,
    ⟨[78513], [78513], .contexts []⟩,
    ⟨[78515, 3], [78513], .contexts [
        ⟨7847, false, false, [], [3]⟩,
        ⟨35, false, false, [78513], []⟩,
        ⟨7848, false, false, [], []⟩
      ]⟩,
    ⟨[78517], [78515, 5], .source 39323⟩,
    ⟨[78515], [78515], .contexts []⟩,
    ⟨[78517, 5], [78515], .contexts [
        ⟨7850, false, false, [], [5]⟩,
        ⟨49, false, false, [78515], []⟩,
        ⟨7851, false, false, [], []⟩
      ]⟩,
    ⟨[78519], [78517, 1], .source 39324⟩,
    ⟨[78517, 1], [78519], .contexts [
        ⟨7853, true, false, [], []⟩
      ]⟩,
    ⟨[78517], [78517], .contexts []⟩,
    ⟨[78519, 1], [78517], .contexts [
        ⟨7854, true, false, [], [1]⟩,
        ⟨18, false, false, [78517], []⟩,
        ⟨7855, false, false, [], []⟩
      ]⟩,
    ⟨[78521], [78519, 9], .source 39325⟩,
    ⟨[78519], [78519], .contexts []⟩,
    ⟨[78521, 9], [78519], .contexts [
        ⟨7857, false, false, [], [9]⟩,
        ⟨76, false, false, [78519], []⟩,
        ⟨7858, false, false, [], []⟩
      ]⟩,
    ⟨[78523], [78521, 11], .source 39326⟩,
    ⟨[78521, 11], [78523], .contexts [
        ⟨7860, true, false, [], []⟩
      ]⟩,
    ⟨[78521], [78521], .contexts []⟩,
    ⟨[78523, 11], [78521], .contexts [
        ⟨7861, true, false, [], [11]⟩,
        ⟨90, false, false, [78521], []⟩,
        ⟨7862, false, false, [], []⟩
      ]⟩,
    ⟨[78525], [78523, 1], .source 39327⟩,
    ⟨[78523], [78523], .contexts []⟩,
    ⟨[78525, 1], [78523], .contexts [
        ⟨7864, false, false, [], [1]⟩,
        ⟨18, false, false, [78523], []⟩,
        ⟨7865, false, false, [], []⟩
      ]⟩,
    ⟨[78527], [78525, 13], .source 39328⟩,
    ⟨[78525], [78525], .contexts []⟩,
    ⟨[78527, 13], [78525], .contexts [
        ⟨7867, false, false, [], [13]⟩,
        ⟨98, false, false, [78525], []⟩,
        ⟨7868, false, false, [], []⟩
      ]⟩,
    ⟨[78529], [78527, 15], .source 39329⟩,
    ⟨[78527], [78527], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 123. -/
def y322TCContextRaw123 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78529, 15], [78527], .contexts [
        ⟨7870, false, false, [], [15]⟩,
        ⟨3, false, false, [78527], []⟩,
        ⟨7871, false, false, [], []⟩
      ]⟩,
    ⟨[78531], [78529, 1], .source 39330⟩,
    ⟨[78529], [78529], .contexts []⟩,
    ⟨[78531, 1], [78529], .contexts [
        ⟨7873, false, false, [], [1]⟩,
        ⟨18, false, false, [78529], []⟩,
        ⟨7874, false, false, [], []⟩
      ]⟩,
    ⟨[78533], [78531, 3], .source 39331⟩,
    ⟨[78531], [78531], .contexts []⟩,
    ⟨[78535], [78533, 5], .source 39332⟩,
    ⟨[78533], [78533], .contexts []⟩,
    ⟨[78535, 5], [78533], .contexts [
        ⟨7878, false, false, [], [5]⟩,
        ⟨49, false, false, [78533], []⟩,
        ⟨7879, false, false, [], []⟩
      ]⟩,
    ⟨[78537], [78535, 1], .source 39333⟩,
    ⟨[78535, 1], [78537], .contexts [
        ⟨7881, true, false, [], []⟩
      ]⟩,
    ⟨[78535], [78535], .contexts []⟩,
    ⟨[78537, 1], [78535], .contexts [
        ⟨7882, true, false, [], [1]⟩,
        ⟨18, false, false, [78535], []⟩,
        ⟨7883, false, false, [], []⟩
      ]⟩,
    ⟨[78537], [78537], .contexts []⟩,
    ⟨[78535, 5], [78533], .contexts [
        ⟨7880, false, false, [], []⟩,
        ⟨7879, false, false, [], []⟩,
        ⟨7879, false, false, [], []⟩
      ]⟩,
    ⟨[78533, 3], [78531], .contexts [
        ⟨7876, false, false, [], [3]⟩,
        ⟨35, false, false, [78531], []⟩,
        ⟨7877, false, false, [], []⟩
      ]⟩,
    ⟨[78531], [78531], .contexts []⟩,
    ⟨[78531, 1], [78529], .contexts [
        ⟨7875, false, false, [], []⟩
      ]⟩,
    ⟨[78529], [78529], .contexts []⟩,
    ⟨[78527], [78527], .contexts []⟩,
    ⟨[78525], [78525], .contexts []⟩,
    ⟨[78523], [78523], .contexts []⟩,
    ⟨[78535, 5, 3, 1, 15, 13, 1], [78523], .contexts [
        ⟨7886, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨7887, false, false, [], [1, 15, 13, 1]⟩,
        ⟨7888, false, false, [], [1, 15, 13, 1]⟩,
        ⟨7877, false, false, [], [1, 15, 13, 1]⟩,
        ⟨7877, false, false, [], [1, 15, 13, 1]⟩,
        ⟨7889, false, false, [], [15, 13, 1]⟩,
        ⟨7890, false, false, [], [15, 13, 1]⟩,
        ⟨7874, false, false, [], [15, 13, 1]⟩,
        ⟨7874, false, false, [], [15, 13, 1]⟩,
        ⟨7872, false, false, [], [13, 1]⟩,
        ⟨7891, false, false, [], [13, 1]⟩,
        ⟨7871, false, false, [], [13, 1]⟩,
        ⟨7871, false, false, [], [13, 1]⟩,
        ⟨7869, false, false, [], [1]⟩,
        ⟨7892, false, false, [], [1]⟩,
        ⟨7868, false, false, [], [1]⟩,
        ⟨7868, false, false, [], [1]⟩,
        ⟨7866, false, false, [], []⟩,
        ⟨7893, false, false, [], []⟩,
        ⟨7865, false, false, [], []⟩,
        ⟨7865, false, false, [], []⟩
      ]⟩,
    ⟨[78521], [78521], .contexts []⟩,
    ⟨[78521, 9], [78519], .contexts [
        ⟨7859, false, false, [], []⟩
      ]⟩,
    ⟨[78519], [78519], .contexts []⟩,
    ⟨[78519, 1], [78517], .contexts [
        ⟨7856, false, false, [], []⟩
      ]⟩,
    ⟨[78517], [78517], .contexts []⟩,
    ⟨[78517, 5], [78515], .contexts [
        ⟨7852, false, false, [], []⟩
      ]⟩,
    ⟨[78515], [78515], .contexts []⟩,
    ⟨[78515, 3], [78513], .contexts [
        ⟨7849, false, false, [], []⟩
      ]⟩,
    ⟨[78513], [78513], .contexts []⟩,
    ⟨[78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3], [78513], .contexts [
        ⟨7894, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨7863, false, false, [], [9, 1, 5, 3]⟩,
        ⟨7895, false, false, [], [9, 1, 5, 3]⟩,
        ⟨7862, false, false, [], [9, 1, 5, 3]⟩,
        ⟨7862, false, false, [], [9, 1, 5, 3]⟩,
        ⟨7896, false, false, [], [1, 5, 3]⟩,
        ⟨7897, false, false, [], [1, 5, 3]⟩,
        ⟨7858, false, false, [], [1, 5, 3]⟩,
        ⟨7858, false, false, [], [1, 5, 3]⟩,
        ⟨7898, false, false, [], [5, 3]⟩,
        ⟨7899, false, false, [], [5, 3]⟩,
        ⟨7855, false, false, [], [5, 3]⟩,
        ⟨7855, false, false, [], [5, 3]⟩,
        ⟨7900, false, false, [], [3]⟩,
        ⟨7901, false, false, [], [3]⟩,
        ⟨7851, false, false, [], [3]⟩,
        ⟨7851, false, false, [], [3]⟩,
        ⟨7902, false, false, [], []⟩,
        ⟨7903, false, false, [], []⟩,
        ⟨7848, false, false, [], []⟩,
        ⟨7848, false, false, [], []⟩
      ]⟩,
    ⟨[78513, 1], [78511], .contexts [
        ⟨7846, false, false, [], []⟩
      ]⟩,
    ⟨[78511], [78511], .contexts []⟩,
    ⟨[78511, 15], [78509], .contexts [
        ⟨7841, false, false, [], [15]⟩,
        ⟨3, false, false, [78509], []⟩,
        ⟨7842, false, false, [], []⟩
      ]⟩,
    ⟨[78509], [78509], .contexts []⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11
    ], [78503], .contexts [
        ⟨7904, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨7905, false, false, [], [15, 13, 1, 11]⟩,
        ⟨7906, false, false, [], [15, 13, 1, 11]⟩,
        ⟨7845, false, false, [], [15, 13, 1, 11]⟩,
        ⟨7845, false, false, [], [15, 13, 1, 11]⟩,
        ⟨7907, false, false, [], [13, 1, 11]⟩,
        ⟨7908, false, false, [], [13, 1, 11]⟩,
        ⟨7842, false, false, [], [13, 1, 11]⟩,
        ⟨7842, false, false, [], [13, 1, 11]⟩,
        ⟨7839, false, false, [], [13, 1, 11]⟩,
        ⟨98, false, false, [78507], [1, 11]⟩,
        ⟨7840, false, false, [], [1, 11]⟩,
        ⟨7840, false, false, [], [1, 11]⟩,
        ⟨7840, false, false, [], [1, 11]⟩,
        ⟨7837, false, false, [], [1, 11]⟩,
        ⟨18, false, false, [78505], [11]⟩,
        ⟨7838, false, false, [], [11]⟩,
        ⟨7838, false, false, [], [11]⟩,
        ⟨7838, false, false, [], [11]⟩,
        ⟨7835, false, false, [], [11]⟩,
        ⟨90, false, false, [78503], []⟩,
        ⟨7836, false, false, [], []⟩,
        ⟨7836, false, false, [], []⟩,
        ⟨7836, false, false, [], []⟩
      ]⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [78495], .contexts [
        ⟨7909, false, false, [], [9, 1, 5, 3]⟩,
        ⟨7833, false, false, [], [9, 1, 5, 3]⟩,
        ⟨76, false, false, [78501], [1, 5, 3]⟩,
        ⟨7834, false, false, [], [1, 5, 3]⟩,
        ⟨7834, false, false, [], [1, 5, 3]⟩,
        ⟨7834, false, false, [], [1, 5, 3]⟩,
        ⟨7831, false, false, [], [1, 5, 3]⟩,
        ⟨18, false, false, [78499], [5, 3]⟩,
        ⟨7832, false, false, [], [5, 3]⟩,
        ⟨7832, false, false, [], [5, 3]⟩,
        ⟨7832, false, false, [], [5, 3]⟩,
        ⟨7829, false, false, [], [5, 3]⟩,
        ⟨49, false, false, [78497], [3]⟩,
        ⟨7830, false, false, [], [3]⟩,
        ⟨7830, false, false, [], [3]⟩,
        ⟨7830, false, false, [], [3]⟩,
        ⟨7827, false, false, [], [3]⟩,
        ⟨35, false, false, [78495], []⟩,
        ⟨7828, false, false, [], []⟩,
        ⟨7828, false, false, [], []⟩,
        ⟨7828, false, false, [], []⟩
      ]⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1
    ], [78487], .contexts [
        ⟨7910, false, false, [], [1, 15, 13, 1]⟩,
        ⟨7825, false, false, [], [1, 15, 13, 1]⟩,
        ⟨18, false, false, [78493], [15, 13, 1]⟩,
        ⟨7826, false, false, [], [15, 13, 1]⟩,
        ⟨7826, false, false, [], [15, 13, 1]⟩,
        ⟨7826, false, false, [], [15, 13, 1]⟩,
        ⟨7823, false, false, [], [15, 13, 1]⟩,
        ⟨3, false, false, [78491], [13, 1]⟩,
        ⟨7824, false, false, [], [13, 1]⟩,
        ⟨7824, false, false, [], [13, 1]⟩,
        ⟨7824, false, false, [], [13, 1]⟩,
        ⟨7821, false, false, [], [13, 1]⟩,
        ⟨98, false, false, [78489], [1]⟩,
        ⟨7822, false, false, [], [1]⟩,
        ⟨7822, false, false, [], [1]⟩,
        ⟨7822, false, false, [], [1]⟩,
        ⟨7819, false, false, [], [1]⟩,
        ⟨18, false, false, [78487], []⟩,
        ⟨7820, false, false, [], []⟩,
        ⟨7820, false, false, [], []⟩,
        ⟨7820, false, false, [], []⟩
      ]⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5
    ], [78479], .contexts [
        ⟨7911, false, false, [], [11, 9, 1, 5]⟩,
        ⟨7817, false, false, [], [11, 9, 1, 5]⟩,
        ⟨90, false, false, [78485], [9, 1, 5]⟩,
        ⟨7818, false, false, [], [9, 1, 5]⟩,
        ⟨7818, false, false, [], [9, 1, 5]⟩,
        ⟨7818, false, false, [], [9, 1, 5]⟩,
        ⟨7815, false, false, [], [9, 1, 5]⟩,
        ⟨76, false, false, [78483], [1, 5]⟩,
        ⟨7816, false, false, [], [1, 5]⟩,
        ⟨7816, false, false, [], [1, 5]⟩,
        ⟨7816, false, false, [], [1, 5]⟩,
        ⟨7813, false, false, [], [1, 5]⟩,
        ⟨18, false, false, [78481], [5]⟩,
        ⟨7814, false, false, [], [5]⟩,
        ⟨7814, false, false, [], [5]⟩,
        ⟨7814, false, false, [], [5]⟩,
        ⟨7811, false, false, [], [5]⟩,
        ⟨49, false, false, [78479], []⟩,
        ⟨7812, false, false, [], []⟩,
        ⟨7812, false, false, [], []⟩,
        ⟨7812, false, false, [], []⟩
      ]⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [78471], .contexts [
        ⟨7912, false, false, [], [3, 1, 15, 13]⟩,
        ⟨7809, false, false, [], [3, 1, 15, 13]⟩,
        ⟨35, false, false, [78477], [1, 15, 13]⟩,
        ⟨7810, false, false, [], [1, 15, 13]⟩,
        ⟨7810, false, false, [], [1, 15, 13]⟩,
        ⟨7810, false, false, [], [1, 15, 13]⟩,
        ⟨7807, false, false, [], [1, 15, 13]⟩,
        ⟨18, false, false, [78475], [15, 13]⟩,
        ⟨7808, false, false, [], [15, 13]⟩,
        ⟨7808, false, false, [], [15, 13]⟩,
        ⟨7808, false, false, [], [15, 13]⟩,
        ⟨7805, false, false, [], [15, 13]⟩,
        ⟨3, false, false, [78473], [13]⟩,
        ⟨7806, false, false, [], [13]⟩,
        ⟨7806, false, false, [], [13]⟩,
        ⟨7806, false, false, [], [13]⟩,
        ⟨7803, false, false, [], [13]⟩,
        ⟨98, false, false, [78471], []⟩,
        ⟨7804, false, false, [], []⟩,
        ⟨7804, false, false, [], []⟩,
        ⟨7804, false, false, [], []⟩
      ]⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1
    ], [78463], .contexts [
        ⟨7913, false, false, [], [1, 11, 9, 1]⟩,
        ⟨7801, false, false, [], [1, 11, 9, 1]⟩,
        ⟨18, false, false, [78469], [11, 9, 1]⟩,
        ⟨7802, false, false, [], [11, 9, 1]⟩,
        ⟨7802, false, false, [], [11, 9, 1]⟩,
        ⟨7802, false, false, [], [11, 9, 1]⟩,
        ⟨7799, false, false, [], [11, 9, 1]⟩,
        ⟨90, false, false, [78467], [9, 1]⟩,
        ⟨7800, false, false, [], [9, 1]⟩,
        ⟨7800, false, false, [], [9, 1]⟩,
        ⟨7800, false, false, [], [9, 1]⟩,
        ⟨7797, false, false, [], [9, 1]⟩,
        ⟨76, false, false, [78465], [1]⟩,
        ⟨7798, false, false, [], [1]⟩,
        ⟨7798, false, false, [], [1]⟩,
        ⟨7798, false, false, [], [1]⟩,
        ⟨7795, false, false, [], [1]⟩,
        ⟨18, false, false, [78463], []⟩,
        ⟨7796, false, false, [], []⟩,
        ⟨7796, false, false, [], []⟩,
        ⟨7796, false, false, [], []⟩
      ]⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15
    ], [78455], .contexts [
        ⟨7914, false, false, [], [5, 3, 1, 15]⟩,
        ⟨7793, false, false, [], [5, 3, 1, 15]⟩,
        ⟨49, false, false, [78461], [3, 1, 15]⟩,
        ⟨7794, false, false, [], [3, 1, 15]⟩,
        ⟨7794, false, false, [], [3, 1, 15]⟩,
        ⟨7794, false, false, [], [3, 1, 15]⟩,
        ⟨7791, false, false, [], [3, 1, 15]⟩,
        ⟨35, false, false, [78459], [1, 15]⟩,
        ⟨7792, false, false, [], [1, 15]⟩,
        ⟨7792, false, false, [], [1, 15]⟩,
        ⟨7792, false, false, [], [1, 15]⟩,
        ⟨7789, false, false, [], [1, 15]⟩,
        ⟨18, false, false, [78457], [15]⟩,
        ⟨7790, false, false, [], [15]⟩,
        ⟨7790, false, false, [], [15]⟩,
        ⟨7790, false, false, [], [15]⟩,
        ⟨7787, false, false, [], [15]⟩,
        ⟨3, false, false, [78455], []⟩,
        ⟨7788, false, false, [], []⟩,
        ⟨7788, false, false, [], []⟩,
        ⟨7788, false, false, [], []⟩
      ]⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [78447], .contexts [
        ⟨7915, false, false, [], [13, 1, 11, 9]⟩,
        ⟨7785, false, false, [], [13, 1, 11, 9]⟩,
        ⟨98, false, false, [78453], [1, 11, 9]⟩,
        ⟨7786, false, false, [], [1, 11, 9]⟩,
        ⟨7786, false, false, [], [1, 11, 9]⟩,
        ⟨7786, false, false, [], [1, 11, 9]⟩,
        ⟨7783, false, false, [], [1, 11, 9]⟩,
        ⟨18, false, false, [78451], [11, 9]⟩,
        ⟨7784, false, false, [], [11, 9]⟩,
        ⟨7784, false, false, [], [11, 9]⟩,
        ⟨7784, false, false, [], [11, 9]⟩,
        ⟨7781, false, false, [], [11, 9]⟩,
        ⟨90, false, false, [78449], [9]⟩,
        ⟨7782, false, false, [], [9]⟩,
        ⟨7782, false, false, [], [9]⟩,
        ⟨7782, false, false, [], [9]⟩,
        ⟨7779, false, false, [], [9]⟩,
        ⟨76, false, false, [78447], []⟩,
        ⟨7780, false, false, [], []⟩,
        ⟨7780, false, false, [], []⟩,
        ⟨7780, false, false, [], []⟩
      ]⟩,
    ⟨[78443], [78443], .contexts []⟩,
    ⟨[78441], [78441], .contexts []⟩,
    ⟨[78439], [78439], .contexts []⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1
    ], [78439], .contexts [
        ⟨7916, false, false, [], [1, 5, 3, 1]⟩,
        ⟨7777, false, false, [], [1, 5, 3, 1]⟩,
        ⟨18, false, false, [78445], [5, 3, 1]⟩,
        ⟨7778, false, false, [], [5, 3, 1]⟩,
        ⟨7778, false, false, [], [5, 3, 1]⟩,
        ⟨7778, false, false, [], [5, 3, 1]⟩,
        ⟨7775, false, false, [], [5, 3, 1]⟩,
        ⟨49, false, false, [78443], [3, 1]⟩,
        ⟨7776, false, false, [], [3, 1]⟩,
        ⟨7917, false, false, [], [3, 1]⟩,
        ⟨7776, false, false, [], [3, 1]⟩,
        ⟨7776, false, false, [], [3, 1]⟩,
        ⟨7773, true, false, [], [3, 1]⟩,
        ⟨35, false, false, [78441], [1]⟩,
        ⟨7774, false, false, [], [1]⟩,
        ⟨7918, false, false, [], [1]⟩,
        ⟨7774, false, false, [], [1]⟩,
        ⟨7774, false, false, [], [1]⟩,
        ⟨7770, true, false, [], [1]⟩,
        ⟨18, false, false, [78439], []⟩,
        ⟨7771, false, false, [], []⟩,
        ⟨7919, false, false, [], []⟩,
        ⟨7771, false, false, [], []⟩,
        ⟨7771, false, false, [], []⟩
      ]⟩,
    ⟨[78437], [78437], .contexts []⟩,
    ⟨[78435], [78435], .contexts []⟩,
    ⟨[78433], [78433], .contexts []⟩,
    ⟨[78431], [78431], .contexts []⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11
    ], [78431], .contexts [
        ⟨7920, false, false, [], [15, 13, 1, 11]⟩,
        ⟨7767, true, false, [], [15, 13, 1, 11]⟩,
        ⟨3, false, false, [78437], [13, 1, 11]⟩,
        ⟨7768, false, false, [], [13, 1, 11]⟩,
        ⟨7921, false, false, [], [13, 1, 11]⟩,
        ⟨7768, false, false, [], [13, 1, 11]⟩,
        ⟨7768, false, false, [], [13, 1, 11]⟩,
        ⟨7764, true, false, [], [13, 1, 11]⟩,
        ⟨98, false, false, [78435], [1, 11]⟩,
        ⟨7765, false, false, [], [1, 11]⟩,
        ⟨7922, false, false, [], [1, 11]⟩,
        ⟨7765, false, false, [], [1, 11]⟩,
        ⟨7765, false, false, [], [1, 11]⟩,
        ⟨7762, false, false, [], [11]⟩,
        ⟨7923, false, false, [], [11]⟩,
        ⟨7761, false, false, [], [11]⟩,
        ⟨7761, false, false, [], [11]⟩,
        ⟨7757, true, false, [], [11]⟩,
        ⟨90, false, false, [78431], []⟩,
        ⟨7758, false, false, [], []⟩,
        ⟨7924, false, false, [], []⟩,
        ⟨7758, false, false, [], []⟩,
        ⟨7758, false, false, [], []⟩
      ]⟩,
    ⟨[78431, 9], [78429], .contexts [
        ⟨7755, false, false, [], []⟩
      ]⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5
    ], [1781, 78427], .contexts [
        ⟨7925, false, false, [], [9, 1, 5]⟩,
        ⟨7926, false, false, [], [1, 5]⟩,
        ⟨7749, false, false, [], [1, 5]⟩,
        ⟨7750, false, false, [], [1, 5]⟩,
        ⟨7750, false, false, [], [1, 5]⟩,
        ⟨7750, true, false, [], [1, 5]⟩,
        ⟨7750, true, false, [], [1, 5]⟩,
        ⟨7749, true, false, [], [1, 5]⟩,
        ⟨7748, true, false, [], [1, 5]⟩,
        ⟨256, false, false, [78427], [5]⟩,
        ⟨257, false, false, [78427], [5]⟩,
        ⟨7745, false, false, [], [5, 5]⟩,
        ⟨7746, false, false, [], [5, 5]⟩,
        ⟨7702, true, false, [], [78427, 5, 5]⟩,
        ⟨7742, false, false, [], [5, 5]⟩,
        ⟨7744, false, false, [], [5, 5]⟩,
        ⟨7744, false, false, [], [5, 5]⟩,
        ⟨7748, false, false, [1781], [5]⟩,
        ⟨7751, false, false, [], [5]⟩,
        ⟨7752, false, false, [], [5]⟩,
        ⟨7702, true, false, [], [78429, 5]⟩,
        ⟨7751, false, false, [], [5]⟩,
        ⟨7752, false, false, [], [5]⟩,
        ⟨7752, false, false, [], [5]⟩,
        ⟨7748, true, false, [1781], [5]⟩,
        ⟨49, false, false, [1781, 78427], []⟩,
        ⟨7738, false, false, [1781], []⟩
      ]⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [1781, 78419], .contexts [
        ⟨7927, false, false, [], [3, 1, 15, 13]⟩,
        ⟨7742, false, false, [], [3, 1, 15, 13]⟩,
        ⟨7743, false, false, [], [3, 1, 15, 13]⟩,
        ⟨7744, false, false, [], [3, 1, 15, 13]⟩,
        ⟨7736, true, false, [1781], [3, 1, 15, 13]⟩,
        ⟨35, false, false, [1781, 78425], [1, 15, 13]⟩,
        ⟨7739, false, false, [], [1, 15, 13]⟩,
        ⟨7740, false, false, [], [1, 15, 13]⟩,
        ⟨7741, false, false, [], [1, 15, 13]⟩,
        ⟨7734, false, false, [1781], [15, 13]⟩,
        ⟨7728, false, false, [], [15, 13]⟩,
        ⟨7729, false, false, [], [15, 13]⟩,
        ⟨7730, false, false, [], [15, 13]⟩,
        ⟨7725, true, false, [1781], [15, 13]⟩,
        ⟨3, false, false, [1781, 78421], [13]⟩,
        ⟨7716, false, false, [1781], [13]⟩,
        ⟨7718, false, false, [], [13]⟩,
        ⟨7719, false, false, [], [13]⟩,
        ⟨7721, false, false, [], [13]⟩,
        ⟨7715, true, false, [1781], [13]⟩,
        ⟨98, false, false, [1781, 78419], []⟩,
        ⟨7707, false, false, [1781], []⟩,
        ⟨7710, false, false, [], []⟩,
        ⟨7711, false, false, [], []⟩,
        ⟨7712, false, false, [], []⟩
      ]⟩,
    ⟨[1783], [1781, 1261], .source 956⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11
    ], [1783, 78417], .contexts [
        ⟨7928, false, false, [], [1, 11]⟩,
        ⟨7708, true, false, [1781], [1, 11]⟩,
        ⟨992, false, false, [1781, 78417], [11]⟩,
        ⟨993, false, false, [1781, 78417], [11]⟩,
        ⟨7691, false, false, [1781], [11, 11]⟩,
        ⟨7693, false, false, [1781], [11, 11]⟩,
        ⟨7689, false, false, [1781], [11, 11]⟩,
        ⟨7690, false, false, [1781], [11, 11]⟩,
        ⟨7690, false, false, [1781], [11, 11]⟩,
        ⟨7706, false, false, [1781, 1261], [11]⟩,
        ⟨7709, false, false, [1781, 1261], [11]⟩,
        ⟨5579, true, false, [1781], [78419, 11]⟩,
        ⟨7929, true, false, [], [78419, 11]⟩,
        ⟨7706, true, false, [1783], [11]⟩,
        ⟨90, false, false, [1783, 78417], []⟩,
        ⟨7687, false, false, [1783], []⟩
      ]⟩,
    ⟨[1785], [1783, 1251], .source 957⟩,
    ⟨[1787], [1785, 1261], .source 958⟩,
    ⟨[1789], [1787, 1245], .source 959⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1
    ], [1789, 841, 77703], .contexts [
        ⟨7930, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨7704, false, false, [1783], [1, 5, 3, 1]⟩,
        ⟨7931, true, false, [], [78417, 1, 5, 3, 1]⟩,
        ⟨7693, false, false, [1785], [5, 3, 1]⟩,
        ⟨7932, true, false, [], [78417, 5, 3, 1]⟩,
        ⟨7686, false, false, [1787], [3, 1]⟩,
        ⟨5556, false, false, [1787], [1]⟩,
        ⟨7933, true, false, [], [77699, 1]⟩,
        ⟨4109, false, false, [1789], []⟩
      ]⟩,
    ⟨[1791], [1789, 841], .source 960⟩]

/-- Exact literal claimed equations and contextual derivations, block 124. -/
def y322TCContextRaw124 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1793], [1791, 849], .source 961⟩,
    ⟨[1795], [1793, 1217], .source 962⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [1795, 1063, 77129], .contexts [
        ⟨7934, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨7935, true, false, [], [77703, 15, 13, 1, 11, 9]⟩,
        ⟨4090, false, false, [1791], [13, 1, 11, 9]⟩,
        ⟨7936, true, false, [], [77703, 13, 1, 11, 9]⟩,
        ⟨5529, false, false, [1793], [1, 11, 9]⟩,
        ⟨7937, true, false, [], [77125, 1, 11, 9]⟩,
        ⟨5657, false, false, [1795], [11, 9]⟩,
        ⟨5668, false, false, [1795], [9]⟩,
        ⟨4881, false, false, [1795], []⟩
      ]⟩,
    ⟨[1797], [1795, 1063], .source 963⟩,
    ⟨[1799], [1797, 317], .source 964⟩,
    ⟨[1801], [1799, 323], .source 965⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15
    ], [1801, 77129, 15], .contexts [
        ⟨7938, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨7939, true, false, [], [77129, 1, 5, 3, 1, 15]⟩,
        ⟨439, false, false, [1797], [5, 3, 1, 15]⟩,
        ⟨1989, false, false, [1797], [3, 1, 15]⟩,
        ⟨7940, true, false, [], [77127, 3, 1, 15]⟩,
        ⟨1984, false, false, [1799], [1, 15]⟩,
        ⟨7941, true, false, [], [77127, 1, 15]⟩,
        ⟨437, false, false, [1801], [15]⟩
      ]⟩,
    ⟨[1803], [1801, 539], .source 966⟩,
    ⟨[1805], [1803, 269], .source 967⟩,
    ⟨[1807], [1805, 1067], .source 968⟩,
    ⟨[1809], [1807, 529], .source 969⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [1809, 77461], .contexts [
        ⟨7942, false, false, [], [13, 1, 11, 9]⟩,
        ⟨4863, false, false, [1801], [13, 1, 11, 9]⟩,
        ⟨7943, true, false, [], [77865, 13, 1, 11, 9]⟩,
        ⟨4892, false, false, [1803], [1, 11, 9]⟩,
        ⟨4901, false, false, [1803], [11, 9]⟩,
        ⟨7944, true, false, [], [77867, 11, 9]⟩,
        ⟨4908, false, false, [1805], [9]⟩,
        ⟨7945, true, false, [], [77455, 9]⟩,
        ⟨2735, false, false, [1807], []⟩,
        ⟨7946, true, false, [], [77461]⟩
      ]⟩,
    ⟨[1811], [1809, 465], .source 970⟩,
    ⟨[1813], [1811, 463], .source 971⟩,
    ⟨[1815], [1813, 433], .source 972⟩,
    ⟨[1817], [1815, 461], .source 973⟩,
    ⟨[1819], [1817, 465], .source 974⟩,
    ⟨[
      78535, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15
    ], [1819, 77609], .contexts [
        ⟨7947, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨2545, false, false, [1809], [5, 3, 1, 15]⟩,
        ⟨7948, true, false, [], [77465, 5, 3, 1, 15]⟩,
        ⟨2521, false, false, [1811], [3, 1, 15]⟩,
        ⟨7949, true, false, [], [77465, 3, 1, 15]⟩,
        ⟨2525, false, false, [1813], [1, 15]⟩,
        ⟨7950, true, false, [], [77465, 1, 15]⟩,
        ⟨2275, false, false, [1815], [15]⟩,
        ⟨2547, false, false, [1815], [15]⟩,
        ⟨7951, true, false, [], [77461, 15]⟩,
        ⟨3643, true, false, [1817, 460], [15]⟩,
        ⟨3, false, false, [1817, 460, 77609], []⟩,
        ⟨2543, true, false, [1817], [77609]⟩,
        ⟨7952, true, false, [], [77609]⟩
      ]⟩,
    ⟨[1821], [1819, 763], .source 975⟩,
    ⟨[1823], [1821, 31], .source 976⟩,
    ⟨[1825], [1823, 245], .source 977⟩,
    ⟨[78537, 9], [78537, 9], .contexts []⟩,
    ⟨[78537, 9], [1825, 77495], .contexts [
        ⟨7957, false, false, [], []⟩,
        ⟨7885, true, false, [], [9]⟩,
        ⟨7885, true, false, [], [9]⟩,
        ⟨7882, true, false, [], [9]⟩,
        ⟨765, false, false, [78535], []⟩,
        ⟨774, false, false, [78535], []⟩,
        ⟨7953, false, false, [], [13, 1, 11]⟩,
        ⟨3655, false, false, [1819], [1, 11]⟩,
        ⟨7954, true, false, [], [77495, 1, 11]⟩,
        ⟨2962, false, false, [1821], [11]⟩,
        ⟨740, true, false, [1821], [77495, 11]⟩,
        ⟨7955, true, false, [], [77495, 11]⟩,
        ⟨2967, false, false, [1823], []⟩,
        ⟨7956, true, false, [], [77495]⟩,
        ⟨2961, false, false, [1825], []⟩,
        ⟨24, true, false, [], [1825, 77495]⟩
      ]⟩,
    ⟨[1827], [1824], .source 978⟩,
    ⟨[77495, 9], [1827, 78537], .contexts [
        ⟨7958, true, false, [1824], [9]⟩,
        ⟨76, false, false, [1824, 78537], []⟩,
        ⟨7959, true, false, [], [78537]⟩
      ]⟩,
    ⟨[78537, 1], [78535], .contexts [
        ⟨7884, false, false, [], []⟩,
        ⟨7883, false, false, [], []⟩,
        ⟨7883, false, false, [], []⟩
      ]⟩,
    ⟨[1825, 77495], [1825, 77495], .contexts []⟩,
    ⟨[78537, 9], [1825, 77495], .contexts [
        ⟨7957, false, false, [], []⟩,
        ⟨7958, false, false, [], []⟩,
        ⟨7962, false, false, [], []⟩,
        ⟨7962, false, false, [], []⟩
      ]⟩,
    ⟨[1829], [1825, 31], .source 979⟩,
    ⟨[1831], [1829, 1827], .source 980⟩,
    ⟨[1831, 78535], [1831, 78535], .contexts []⟩,
    ⟨[1831, 78535], [1831, 78535], .contexts []⟩,
    ⟨[78535, 9], [78535, 9], .contexts []⟩,
    ⟨[1833], [1825, 315], .source 981⟩,
    ⟨[1835], [1833, 1827], .source 982⟩,
    ⟨[78537], [78537], .contexts []⟩,
    ⟨[1835, 78537, 5], [78537], .contexts [
        ⟨7970, false, false, [], [78537, 5]⟩,
        ⟨7960, true, false, [1833], [5]⟩,
        ⟨7969, false, false, [], [77495, 9, 5]⟩,
        ⟨2812, false, false, [1825], [77495, 9, 5]⟩,
        ⟨2961, true, false, [1825, 315], [9, 5]⟩,
        ⟨2954, true, false, [1825, 315], [9, 5]⟩,
        ⟨2963, true, false, [1825], [15, 9, 5]⟩,
        ⟨51, true, false, [1825, 77493], [9, 5]⟩,
        ⟨48, true, false, [1825, 77493], [9, 5]⟩,
        ⟨2958, false, false, [1825], [5, 9, 5]⟩,
        ⟨7963, true, false, [], [5, 9, 5]⟩,
        ⟨892, false, false, [78537], []⟩,
        ⟨7971, false, false, [], []⟩
      ]⟩,
    ⟨[78537, 5], [78537, 5], .contexts []⟩,
    ⟨[78537], [78537], .contexts []⟩,
    ⟨[1837], [1834], .source 983⟩,
    ⟨[1837], [1837], .contexts []⟩,
    ⟨[1834], [1834], .contexts []⟩,
    ⟨[1839], [1825, 675], .source 984⟩,
    ⟨[77591, 15], [77591, 15], .contexts []⟩,
    ⟨[1841], [1838], .source 985⟩,
    ⟨[1838], [1838], .contexts []⟩,
    ⟨[78535, 9], [1831, 78535], .contexts [
        ⟨7968, false, false, [], []⟩,
        ⟨7968, false, false, [], []⟩,
        ⟨7961, true, false, [], [9]⟩,
        ⟨786, false, false, [78537], []⟩,
        ⟨788, false, false, [78537], []⟩,
        ⟨7963, false, false, [], [1, 9, 1]⟩,
        ⟨2962, false, false, [1825], [9, 1]⟩,
        ⟨740, true, false, [1825], [77495, 9, 1]⟩,
        ⟨7964, true, false, [], [77495, 9, 1]⟩,
        ⟨7960, false, false, [1829], [1]⟩,
        ⟨7965, true, false, [], [78537, 1]⟩,
        ⟨7884, false, false, [1831], []⟩,
        ⟨7966, false, false, [], []⟩,
        ⟨7967, false, false, [], []⟩,
        ⟨24, true, false, [], [1831, 78535]⟩,
        ⟨7966, false, false, [], []⟩,
        ⟨7967, false, false, [], []⟩
      ]⟩,
    ⟨[78533], [78533], .contexts []⟩,
    ⟨[1843], [1830], .source 986⟩,
    ⟨[1830], [1830], .contexts []⟩,
    ⟨[1837, 78537], [1837, 78537], .contexts []⟩,
    ⟨[1837, 78533], [1837, 78533], .contexts []⟩,
    ⟨[78537, 5, 1, 5], [1837, 78533], .contexts [
        ⟨7973, false, false, [], [1, 5]⟩,
        ⟨7973, false, false, [], [1, 5]⟩,
        ⟨7972, false, false, [1834], [1, 5]⟩,
        ⟨7974, false, false, [1834], [1, 5]⟩,
        ⟨7977, true, false, [], [78537, 1, 5]⟩,
        ⟨7977, true, false, [], [78537, 1, 5]⟩,
        ⟨7975, true, false, [], [78537, 1, 5]⟩,
        ⟨7976, true, false, [], [78537, 1, 5]⟩,
        ⟨7986, false, false, [], [1, 5]⟩,
        ⟨7986, false, false, [], [1, 5]⟩,
        ⟨7884, false, false, [1837], [5]⟩,
        ⟨7880, false, false, [1837], []⟩,
        ⟨7987, false, false, [], []⟩
      ]⟩,
    ⟨[1837, 78533], [1837, 78533], .contexts []⟩,
    ⟨[78533, 1], [78533, 1], .contexts []⟩,
    ⟨[1836], [1836], .contexts []⟩,
    ⟨[78533, 1], [1835, 78537], .contexts [
        ⟨7990, false, false, [], []⟩,
        ⟨7989, true, false, [1836], [1]⟩,
        ⟨7988, true, false, [1836], [1]⟩,
        ⟨1485, false, false, [1836, 78537], []⟩,
        ⟨7971, false, false, [1836], []⟩,
        ⟨7974, false, false, [1836], []⟩,
        ⟨7991, true, false, [], [78537]⟩,
        ⟨7991, true, false, [], [78537]⟩,
        ⟨7975, false, true, [], [78537]⟩
      ]⟩,
    ⟨[1841, 78537], [1841, 78537], .contexts []⟩,
    ⟨[77591, 15], [1841, 78537], .contexts [
        ⟨7979, false, false, [], []⟩,
        ⟨7979, false, false, [], []⟩,
        ⟨7978, false, false, [1838], [77591, 15]⟩,
        ⟨3322, true, false, [1838, 1825], [15]⟩,
        ⟨2955, true, false, [1838, 1825], [9, 15]⟩,
        ⟨7963, true, false, [1838], [15, 9, 15]⟩,
        ⟨835, false, false, [1838, 78537], []⟩,
        ⟨7971, false, false, [1838], []⟩,
        ⟨7974, false, false, [1838], []⟩,
        ⟨7981, true, false, [], [78537]⟩,
        ⟨7981, true, false, [], [78537]⟩,
        ⟨7980, true, false, [], [78537]⟩,
        ⟨7993, false, false, [], []⟩,
        ⟨7993, false, false, [], []⟩
      ]⟩,
    ⟨[1845], [1841, 1837], .source 987⟩,
    ⟨[78533, 15], [78533, 15], .contexts []⟩,
    ⟨[78533, 15], [1844, 697, 77587], .contexts [
        ⟨7996, false, false, [], []⟩,
        ⟨7995, false, false, [1844], [78533, 15]⟩,
        ⟨7989, true, false, [1844, 1841], [15]⟩,
        ⟨7976, false, false, [1844, 1841], [78533, 15]⟩,
        ⟨7987, true, false, [1844, 1841], [15]⟩,
        ⟨7975, false, false, [1844, 1841], [78533, 15]⟩,
        ⟨18, true, false, [1844, 1841, 1834, 78533], [15]⟩,
        ⟨7992, false, false, [1844, 1841, 1834], [1, 15]⟩,
        ⟨7961, false, false, [1844, 1841], [15]⟩,
        ⟨7884, true, false, [1844, 1841], [15]⟩,
        ⟨7994, true, false, [1844], [1, 15]⟩,
        ⟨2778, false, false, [1844, 77591], []⟩,
        ⟨5693, false, false, [1844], []⟩,
        ⟨3466, false, false, [1844], []⟩,
        ⟨3380, false, false, [1844, 697], []⟩
      ]⟩,
    ⟨[1847], [1844], .source 988⟩,
    ⟨[1849], [1847, 697], .source 989⟩]

/-- Exact literal claimed equations and contextual derivations, block 125. -/
def y322TCContextRaw125 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1851], [1848], .source 990⟩,
    ⟨[695, 77131], [695, 77131], .contexts []⟩,
    ⟨[1853], [1839, 695], .source 991⟩,
    ⟨[78537, 11], [1853, 77133], .contexts [
        ⟨7994, true, false, [1840], [11]⟩,
        ⟨89, false, false, [1840, 77591], []⟩,
        ⟨92, false, false, [1840, 77591], []⟩,
        ⟨5689, false, false, [1840], [15]⟩,
        ⟨8001, false, false, [1840], [15]⟩,
        ⟨8001, false, false, [1840], [15]⟩,
        ⟨445, false, false, [1840, 695], []⟩,
        ⟨2009, false, false, [1840, 695], []⟩,
        ⟨7980, false, true, [], [695, 77133]⟩,
        ⟨8002, true, false, [], [77133]⟩
      ]⟩,
    ⟨[1855], [1852], .source 992⟩,
    ⟨[77133, 11], [1855, 78537], .contexts [
        ⟨8003, true, false, [1852], [11]⟩,
        ⟨90, false, false, [1852, 78537], []⟩,
        ⟨8004, true, false, [], [78537]⟩
      ]⟩,
    ⟨[78533, 3], [78531], .contexts [
        ⟨7887, false, false, [], []⟩,
        ⟨7888, false, false, [], []⟩,
        ⟨7877, false, false, [], []⟩,
        ⟨7877, false, false, [], []⟩
      ]⟩,
    ⟨[78531], [78531], .contexts []⟩,
    ⟨[1835, 78537], [1835, 78537], .contexts []⟩,
    ⟨[1857], [1835, 1853], .source 993⟩,
    ⟨[1857, 77135], [1857, 77135], .contexts []⟩,
    ⟨[1857, 77135], [1857, 77135], .contexts []⟩,
    ⟨[77135, 11], [77135, 11], .contexts []⟩,
    ⟨[1859], [1856], .source 994⟩,
    ⟨[1856], [1856], .contexts []⟩,
    ⟨[77135, 11], [1859, 78533], .contexts [
        ⟨8012, false, false, [], []⟩,
        ⟨8011, true, false, [1856], [11]⟩,
        ⟨8010, true, false, [1856], [11]⟩,
        ⟨448, true, false, [], [11]⟩,
        ⟨8009, false, false, [1856], [77133, 1, 11]⟩,
        ⟨8003, true, false, [1856, 1835], [1, 11]⟩,
        ⟨8008, true, false, [1856], [11, 1, 11]⟩,
        ⟨8008, true, false, [1856], [11, 1, 11]⟩,
        ⟨7992, true, false, [1856], [11, 1, 11]⟩,
        ⟨7990, true, false, [1856], [11, 1, 11]⟩,
        ⟨1728, false, false, [1856, 78533], []⟩,
        ⟨7983, false, false, [1856], []⟩,
        ⟨8014, true, false, [], [78533]⟩,
        ⟨8014, true, false, [], [78533]⟩,
        ⟨8013, true, false, [], [78533]⟩
      ]⟩,
    ⟨[1857], [1858], .contexts [
        ⟨8013, true, true, [], []⟩
      ]⟩,
    ⟨[78533, 11], [1857, 77135], .contexts [
        ⟨8015, true, false, [1858], [11]⟩,
        ⟨90, false, false, [1858, 77135], []⟩,
        ⟨8016, true, false, [], [77135]⟩
      ]⟩,
    ⟨[1857, 77137], [1857, 77137], .contexts []⟩,
    ⟨[1857, 77137], [1857, 77137], .contexts []⟩,
    ⟨[78531, 11], [78531, 11], .contexts []⟩,
    ⟨[78531, 11], [1857, 77137], .contexts [
        ⟨8020, false, false, [], []⟩,
        ⟨8006, true, false, [], [11]⟩,
        ⟨231, false, false, [78533], []⟩,
        ⟨232, false, false, [78533], []⟩,
        ⟨8017, false, false, [], [3]⟩,
        ⟨8010, false, false, [], [3]⟩,
        ⟨8011, false, false, [], [3]⟩,
        ⟨8011, false, false, [], [3]⟩,
        ⟨452, false, false, [1857], []⟩,
        ⟨8018, false, false, [], []⟩,
        ⟨8019, false, false, [], []⟩,
        ⟨4939, false, false, [1857], []⟩,
        ⟨24, true, false, [], [1857, 77137]⟩
      ]⟩,
    ⟨[77137, 11], [1859, 78531], .contexts [
        ⟨8021, true, false, [1856], [11]⟩,
        ⟨90, false, false, [1856, 78531], []⟩,
        ⟨8013, true, false, [], [78531]⟩
      ]⟩,
    ⟨[1849, 77587], [1849, 77587], .contexts []⟩,
    ⟨[1849, 77585], [1849, 77585], .contexts []⟩,
    ⟨[1849, 77585], [1849, 77585], .contexts []⟩,
    ⟨[78531, 15], [78531, 15], .contexts []⟩,
    ⟨[78531, 15], [1849, 77585], .contexts [
        ⟨8026, false, false, [], []⟩,
        ⟨8006, true, false, [], [15]⟩,
        ⟨245, false, false, [78533], []⟩,
        ⟨246, false, false, [78533], []⟩,
        ⟨7996, false, false, [], [3]⟩,
        ⟨7997, false, false, [], [3]⟩,
        ⟨7998, true, false, [], [697, 77587, 3]⟩,
        ⟨7999, true, false, [], [77587, 3]⟩,
        ⟨8023, false, false, [], [3]⟩,
        ⟨8023, false, false, [], [3]⟩,
        ⟨3125, false, false, [1849], []⟩,
        ⟨8024, false, false, [], []⟩,
        ⟨8025, false, false, [], []⟩
      ]⟩,
    ⟨[1849], [1849], .contexts []⟩,
    ⟨[1849], [1849], .contexts []⟩,
    ⟨[78531, 15], [1849, 77585], .contexts [
        ⟨8027, false, false, [], []⟩,
        ⟨3405, false, false, [1849], []⟩,
        ⟨8029, true, false, [], [77585]⟩,
        ⟨8028, true, false, [], [77585]⟩,
        ⟨24, true, false, [], [1849, 77585]⟩
      ]⟩,
    ⟨[77585, 15], [1851, 78531], .contexts [
        ⟨8030, true, false, [1848], [15]⟩,
        ⟨3, false, false, [1848, 78531], []⟩,
        ⟨8000, true, false, [], [78531]⟩
      ]⟩,
    ⟨[78531, 11], [1857, 77137], .contexts [
        ⟨8020, false, false, [], []⟩,
        ⟨8021, false, false, [], []⟩,
        ⟨8018, false, false, [], []⟩,
        ⟨8019, false, false, [], []⟩,
        ⟨8019, false, false, [], []⟩
      ]⟩,
    ⟨[1871], [1857, 1077], .source 1000⟩,
    ⟨[1873], [1871, 1859], .source 1001⟩,
    ⟨[78531], [78531], .contexts []⟩,
    ⟨[78531, 13], [78531, 13], .contexts []⟩,
    ⟨[1875], [1872], .source 1002⟩,
    ⟨[1872], [1872], .contexts []⟩,
    ⟨[78531, 15], [1849, 77585], .contexts [
        ⟨8026, false, false, [], []⟩,
        ⟨8030, false, false, [], []⟩,
        ⟨8024, false, false, [], []⟩,
        ⟨8025, false, false, [], []⟩,
        ⟨8025, false, false, [], []⟩
      ]⟩,
    ⟨[1849, 77583], [1849, 77583], .contexts []⟩,
    ⟨[1849, 77583], [1849, 77583], .contexts []⟩,
    ⟨[1849, 77583], [1849, 77583], .contexts []⟩,
    ⟨[1849, 77581], [1849, 77581], .contexts []⟩,
    ⟨[1849, 77581], [1849, 77581], .contexts []⟩,
    ⟨[1851], [1848], .contexts [
        ⟨8000, false, false, [], []⟩
      ]⟩,
    ⟨[1848], [1848], .contexts []⟩,
    ⟨[1849], [1850], .contexts [
        ⟨8000, true, true, [], []⟩
      ]⟩,
    ⟨[78531, 1], [78529], .contexts [
        ⟨7889, false, false, [], []⟩
      ]⟩,
    ⟨[78529], [1849, 77581], .contexts [
        ⟨7874, true, false, [], []⟩,
        ⟨7874, true, false, [], []⟩,
        ⟨7890, true, false, [], []⟩,
        ⟨8048, true, false, [], []⟩,
        ⟨8045, false, false, [1850], [78531, 1]⟩,
        ⟨8046, false, false, [1850], [78531, 1]⟩,
        ⟨8046, false, false, [1850], [78531, 1]⟩,
        ⟨8007, true, false, [1850, 1848], [1]⟩,
        ⟨8035, true, false, [1850, 1848], [1]⟩,
        ⟨911, true, false, [1850, 1848, 78531], [1]⟩,
        ⟨8039, false, false, [1850, 1848], [1, 15, 1, 1]⟩,
        ⟨3121, false, false, [1850], [15, 1, 1]⟩,
        ⟨8040, false, false, [1850, 1848], [15, 1, 1]⟩,
        ⟨8041, false, false, [1850, 1848], [15, 1, 1]⟩,
        ⟨8042, false, false, [1850, 1848], [15, 1, 1]⟩,
        ⟨3117, false, false, [1850], [1, 1]⟩,
        ⟨8043, false, false, [1850, 1848], [1, 1]⟩,
        ⟨8044, false, false, [1850, 1848], [1, 1]⟩,
        ⟨18, false, false, [1850, 77581], []⟩,
        ⟨8047, true, false, [], [77581]⟩
      ]⟩,
    ⟨[1849], [1849], .contexts [
        ⟨8028, false, false, [], []⟩
      ]⟩,
    ⟨[78529], [1849, 77581], .contexts [
        ⟨8049, false, false, [], []⟩,
        ⟨8043, false, false, [], []⟩,
        ⟨8029, true, false, [], [77581]⟩,
        ⟨8050, true, false, [], [77581]⟩,
        ⟨8044, false, false, [], []⟩
      ]⟩,
    ⟨[1877], [1849, 753], .source 1003⟩,
    ⟨[1879], [1876], .source 1004⟩,
    ⟨[1879], [1876], .contexts [
        ⟨8053, false, false, [], []⟩
      ]⟩,
    ⟨[1879], [1876], .contexts [
        ⟨8054, false, false, [], []⟩,
        ⟨24, false, false, [1876], []⟩
      ]⟩,
    ⟨[77583], [1879, 78525], .contexts [
        ⟨8052, false, false, [1876], [77583]⟩,
        ⟨3491, true, false, [1876, 1849], []⟩,
        ⟨8042, true, false, [1876], [13]⟩,
        ⟨8047, false, false, [1876], [77583, 13]⟩,
        ⟨8042, true, false, [1876, 1850, 1848], [13]⟩,
        ⟨8041, true, false, [1876, 1850, 1848], [13]⟩,
        ⟨8040, true, false, [1876, 1850, 1848], [13]⟩,
        ⟨3115, true, false, [1876, 1850], [13]⟩,
        ⟨8051, true, false, [1876, 1850, 1848], [15, 13]⟩,
        ⟨7872, false, false, [1876, 1850, 1848], [13]⟩,
        ⟨7891, false, false, [1876, 1850, 1848], [13]⟩,
        ⟨24, true, false, [1876, 1850, 1848], [78527, 13]⟩,
        ⟨8045, true, false, [1876, 1850], [78527, 13]⟩,
        ⟨7869, false, false, [1876], []⟩,
        ⟨7892, false, false, [1876], []⟩,
        ⟨8055, true, false, [], [78525]⟩
      ]⟩,
    ⟨[1877], [1878], .contexts [
        ⟨8053, true, true, [], []⟩
      ]⟩,
    ⟨[1877, 77585], [1877, 77585], .contexts []⟩,
    ⟨[78523], [1877, 77585], .contexts [
        ⟨8055, false, false, [1878], [78523]⟩,
        ⟨7893, true, false, [1878, 1876], []⟩,
        ⟨7866, true, false, [1878, 1876], []⟩,
        ⟨8056, true, false, [1878, 1876, 1878], [1]⟩,
        ⟨8057, true, false, [1878, 1876], [77583, 1]⟩,
        ⟨3119, false, false, [1878], []⟩,
        ⟨8058, false, false, [1878, 1876], []⟩,
        ⟨8057, true, false, [], [77585]⟩
      ]⟩,
    ⟨[1876], [1876], .contexts []⟩,
    ⟨[77585, 11], [1879, 78521], .contexts [
        ⟨8059, true, false, [1876], [11]⟩,
        ⟨7863, false, false, [1876], []⟩,
        ⟨7895, false, false, [1876], []⟩,
        ⟨8060, true, false, [], [78521]⟩,
        ⟨8060, true, false, [], [78521]⟩,
        ⟨8054, true, false, [], [78521]⟩
      ]⟩,
    ⟨[1881], [1849, 1879], .source 1005⟩,
    ⟨[78521, 15], [78521, 15], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 126. -/
def y322TCContextRaw126 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1883], [1880], .source 1006⟩,
    ⟨[1885], [1883, 1857], .source 1007⟩,
    ⟨[78521, 15], [1885, 77137], .contexts [
        ⟨8063, false, false, [], []⟩,
        ⟨8062, false, false, [1880], [78521, 15]⟩,
        ⟨8061, true, false, [1880, 1849], [15]⟩,
        ⟨8039, true, false, [1880], [11, 15]⟩,
        ⟨3495, false, false, [1880, 78531], []⟩,
        ⟨91, false, false, [1880, 78531], []⟩,
        ⟨8032, false, false, [1880], []⟩,
        ⟨4939, false, false, [1880, 1857], []⟩,
        ⟨8064, true, false, [], [1857, 77137]⟩,
        ⟨8065, true, false, [], [77137]⟩
      ]⟩,
    ⟨[1887], [1884], .source 1008⟩,
    ⟨[77137, 15], [1887, 78521], .contexts [
        ⟨8066, true, false, [1884], [15]⟩,
        ⟨3, false, false, [1884, 78521], []⟩,
        ⟨8067, true, false, [], [78521]⟩
      ]⟩,
    ⟨[1875, 78531], [1875, 78531], .contexts []⟩,
    ⟨[78531, 13], [1875, 78531], .contexts [
        ⟨8036, false, false, [], []⟩,
        ⟨8036, false, false, [], []⟩,
        ⟨8034, false, false, [1872], [78531, 13]⟩,
        ⟨8022, true, false, [1872, 1871], [13]⟩,
        ⟨8033, false, false, [1872], [77137, 11, 13]⟩,
        ⟨4942, true, false, [1872, 1857], [11, 13]⟩,
        ⟨8032, true, false, [1872], [13, 11, 13]⟩,
        ⟨1836, false, false, [1872, 78531], []⟩,
        ⟨8035, false, false, [1872], []⟩,
        ⟨8007, false, false, [1872], []⟩,
        ⟨8038, true, false, [], [78531]⟩,
        ⟨8038, true, false, [], [78531]⟩,
        ⟨8037, true, false, [], [78531]⟩,
        ⟨8069, false, false, [], []⟩,
        ⟨8069, false, false, [], []⟩
      ]⟩,
    ⟨[1889], [1875, 1849], .source 1009⟩,
    ⟨[78529], [1849, 77581], .contexts [
        ⟨8051, false, false, [], []⟩
      ]⟩,
    ⟨[77581], [77581], .contexts []⟩,
    ⟨[1891], [1888], .source 1010⟩,
    ⟨[1893], [1891, 1849], .source 1011⟩,
    ⟨[77577, 13], [1893, 77581], .contexts [
        ⟨3110, true, false, [], [13]⟩,
        ⟨3113, true, false, [], [1, 13]⟩,
        ⟨8071, false, false, [1888], [77581, 13, 1, 13]⟩,
        ⟨8051, true, false, [1888, 1875], [13, 1, 13]⟩,
        ⟨7875, true, false, [1888, 1875], [13, 1, 13]⟩,
        ⟨8070, true, false, [1888], [1, 13, 1, 13]⟩,
        ⟨3422, false, false, [1888, 78531], []⟩,
        ⟨19, false, false, [1888, 78531], []⟩,
        ⟨8048, false, false, [1888], []⟩,
        ⟨8072, false, false, [1888], []⟩,
        ⟨8044, false, false, [1888], []⟩,
        ⟨8044, false, false, [1888], []⟩,
        ⟨8073, false, false, [1888, 1849], []⟩,
        ⟨8074, true, false, [], [1849, 77581]⟩,
        ⟨8075, true, false, [], [77581]⟩
      ]⟩,
    ⟨[1895], [1892], .source 1012⟩,
    ⟨[1895], [1895], .contexts []⟩,
    ⟨[1895], [1895], .contexts []⟩,
    ⟨[1895], [1895], .contexts []⟩,
    ⟨[77579], [1895, 77577], .contexts [
        ⟨6705, true, false, [], []⟩,
        ⟨8076, true, false, [1892], [13]⟩,
        ⟨98, false, false, [1892, 77577], []⟩,
        ⟨8077, true, false, [], [77577]⟩,
        ⟨8080, true, false, [], [77577]⟩,
        ⟨8079, true, false, [], [77577]⟩,
        ⟨8078, true, false, [], [77577]⟩
      ]⟩,
    ⟨[1895, 77577], [1895, 77577], .contexts []⟩,
    ⟨[77579], [1895, 77577], .contexts [
        ⟨8081, false, false, [], []⟩,
        ⟨8082, false, false, [], []⟩
      ]⟩,
    ⟨[1893], [1894], .contexts [
        ⟨8077, true, true, [], []⟩
      ]⟩,
    ⟨[1897], [1893, 1461], .source 1013⟩,
    ⟨[77577, 3], [1897, 78241], .contexts [
        ⟨8081, true, false, [1894], [3]⟩,
        ⟨6707, true, false, [1894, 1462], [3]⟩,
        ⟨35, false, false, [1894, 1462, 78241], []⟩,
        ⟨6695, false, true, [1894], [78241]⟩,
        ⟨6704, false, false, [1894], []⟩,
        ⟨8084, true, false, [], [1461, 78241]⟩,
        ⟨8085, true, false, [], [78241]⟩
      ]⟩,
    ⟨[77585, 11], [1879, 78521], .contexts [
        ⟨8061, false, false, [], []⟩
      ]⟩,
    ⟨[1879, 78521], [1879, 78521], .contexts []⟩,
    ⟨[1879, 78521], [1879, 78521], .contexts []⟩,
    ⟨[1, 11, 1], [10], .contexts [
        ⟨180, false, false, [], [10]⟩
      ]⟩,
    ⟨[78521, 1], [78521, 1], .contexts []⟩,
    ⟨[1899], [1877, 1293], .source 1014⟩,
    ⟨[78521, 1], [1899, 77687], .contexts [
        ⟨8091, false, false, [], []⟩,
        ⟨8089, true, false, [1878], [1]⟩,
        ⟨8089, true, false, [1878], [1]⟩,
        ⟨8088, true, false, [1878], [1]⟩,
        ⟨8087, true, false, [1878], [1]⟩,
        ⟨3124, true, false, [1878], [11, 1]⟩,
        ⟨3124, true, false, [1878], [11, 1]⟩,
        ⟨3164, true, false, [1878], [11, 1]⟩,
        ⟨3119, true, false, [1878], [11, 1]⟩,
        ⟨8090, false, false, [1878, 77583], []⟩,
        ⟨5713, false, false, [1878], []⟩,
        ⟨5712, false, false, [1878], []⟩,
        ⟨5587, false, false, [1878, 1293], []⟩,
        ⟨8057, true, false, [], [1293, 77687]⟩,
        ⟨8092, true, false, [], [77687]⟩
      ]⟩,
    ⟨[1901], [1898], .source 1015⟩,
    ⟨[1429, 78257], [1429, 78257], .contexts []⟩,
    ⟨[77585, 11], [1879, 78521], .contexts [
        ⟨8087, false, false, [], []⟩,
        ⟨8088, false, false, [], []⟩,
        ⟨8089, false, false, [], []⟩,
        ⟨8089, false, false, [], []⟩
      ]⟩,
    ⟨[78257, 3], [78257, 3], .contexts []⟩,
    ⟨[78521], [78521], .contexts []⟩,
    ⟨[1903], [1431, 1879], .source 1016⟩,
    ⟨[78257, 3], [1903, 78521], .contexts [
        ⟨8097, false, false, [], []⟩,
        ⟨8095, true, false, [1428], [3]⟩,
        ⟨8095, true, false, [1428], [3]⟩,
        ⟨6654, true, false, [1428], [3]⟩,
        ⟨3128, true, false, [1428], [11, 3]⟩,
        ⟨3128, true, false, [1428], [11, 3]⟩,
        ⟨3162, true, false, [1428], [11, 3]⟩,
        ⟨3123, true, false, [1428], [11, 3]⟩,
        ⟨976, false, false, [1428, 77585], []⟩,
        ⟨91, false, false, [1428, 77585], []⟩,
        ⟨8096, false, false, [1428], []⟩,
        ⟨8098, false, false, [1428, 1879], []⟩,
        ⟨6651, true, false, [], [1879, 78521]⟩,
        ⟨8099, true, false, [], [78521]⟩
      ]⟩,
    ⟨[1905], [1902], .source 1017⟩,
    ⟨[78521, 3], [1905, 78257], .contexts [
        ⟨8100, true, false, [1902], [3]⟩,
        ⟨35, false, false, [1902, 78257], []⟩,
        ⟨8101, true, false, [], [78257]⟩
      ]⟩,
    ⟨[691, 77585], [691, 77585], .contexts []⟩,
    ⟨[77585, 9], [691, 77585], .contexts [
        ⟨3404, false, false, [], []⟩,
        ⟨3404, false, false, [], []⟩,
        ⟨3125, true, false, [], [9]⟩,
        ⟨3403, true, false, [712], [3, 9]⟩,
        ⟨3403, true, false, [712], [3, 9]⟩,
        ⟨3383, true, false, [712], [3, 9]⟩,
        ⟨3379, true, false, [712], [3, 9]⟩,
        ⟨841, false, false, [712, 77587], []⟩,
        ⟨36, false, false, [712, 77587], []⟩,
        ⟨3163, false, false, [712], []⟩,
        ⟨3164, false, false, [712], []⟩,
        ⟨3124, false, false, [712], []⟩,
        ⟨3124, false, false, [712], []⟩,
        ⟨3405, false, false, [712], []⟩,
        ⟨3406, true, false, [], [77585]⟩,
        ⟨3406, true, false, [], [77585]⟩,
        ⟨3381, false, true, [], [77585]⟩,
        ⟨8103, false, false, [], []⟩,
        ⟨8103, false, false, [], []⟩
      ]⟩,
    ⟨[1907], [691, 1879], .source 1018⟩,
    ⟨[78519, 11], [78519, 11], .contexts []⟩,
    ⟨[78519], [78519], .contexts []⟩,
    ⟨[1909], [1906], .source 1019⟩,
    ⟨[1911], [1909, 1879], .source 1020⟩,
    ⟨[77577, 1], [1895, 77577], .contexts [
        ⟨3108, false, false, [], []⟩,
        ⟨8083, false, false, [], []⟩,
        ⟨8082, false, false, [], []⟩,
        ⟨8082, false, false, [], []⟩
      ]⟩,
    ⟨[1895, 77575], [1895, 77575], .contexts []⟩,
    ⟨[1895, 77575], [1895, 77575], .contexts []⟩,
    ⟨[77575, 1], [77575, 1], .contexts []⟩,
    ⟨[1913], [1895, 1897], .source 1021⟩,
    ⟨[1897, 78241], [1897, 78241], .contexts []⟩,
    ⟨[78239, 3], [78239, 3], .contexts []⟩,
    ⟨[1915], [1912], .source 1022⟩,
    ⟨[1917], [1915, 1897], .source 1023⟩,
    ⟨[78239, 3], [1917, 78239], .contexts [
        ⟨8116, false, false, [], []⟩,
        ⟨6508, true, false, [], [3]⟩,
        ⟨8114, false, false, [1912], [78241, 1, 3]⟩,
        ⟨8086, true, false, [1912, 1895], [1, 3]⟩,
        ⟨8110, true, false, [1912], [3, 1, 3]⟩,
        ⟨852, false, false, [1912, 77577], []⟩,
        ⟨853, false, false, [1912, 77577], []⟩,
        ⟨8086, false, false, [1912], [1]⟩,
        ⟨8115, false, false, [1912], [1]⟩,
        ⟨8115, false, false, [1912], [1]⟩,
        ⟨6508, false, false, [1912, 1897], []⟩,
        ⟨6698, false, false, [1912, 1897], []⟩,
        ⟨8117, true, false, [], [1897, 78239]⟩,
        ⟨8118, true, false, [], [78239]⟩
      ]⟩,
    ⟨[78521, 1], [1899, 77687], .contexts [
        ⟨8093, false, false, [], []⟩
      ]⟩,
    ⟨[1899, 77687], [1899, 77687], .contexts []⟩,
    ⟨[1899, 77687], [1899, 77687], .contexts []⟩,
    ⟨[78521, 1], [1899, 77687], .contexts [
        ⟨8091, false, false, [], []⟩,
        ⟨8120, false, false, [], []⟩,
        ⟨8121, false, false, [], []⟩,
        ⟨8122, false, false, [], []⟩,
        ⟨8122, false, false, [], []⟩
      ]⟩,
    ⟨[1899, 77687, 9], [1899, 77685], .contexts [
        ⟨3859, false, false, [1899], []⟩
      ]⟩,
    ⟨[1899, 77685], [1899, 77685], .contexts []⟩,
    ⟨[1899, 77685], [1899, 77685], .contexts []⟩,
    ⟨[1899, 77685], [1899, 77685], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 127. -/
def y322TCContextRaw127 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[1899, 77685, 1], [1899, 77683], .contexts [
        ⟨3856, false, false, [1899], []⟩
      ]⟩,
    ⟨[1899, 77683], [1899, 77683], .contexts []⟩,
    ⟨[1899, 77683], [1899, 77683], .contexts []⟩,
    ⟨[1899, 77683], [1899, 77683], .contexts []⟩,
    ⟨[78521, 9], [78519], .contexts [
        ⟨7896, false, false, [], []⟩,
        ⟨7897, false, false, [], []⟩,
        ⟨7858, false, false, [], []⟩,
        ⟨7858, false, false, [], []⟩
      ]⟩,
    ⟨[77683, 9], [77683, 9], .contexts []⟩,
    ⟨[78517], [78517], .contexts []⟩,
    ⟨[1901], [1901], .contexts []⟩,
    ⟨[1901], [1898], .contexts [
        ⟨8094, false, false, [], []⟩
      ]⟩,
    ⟨[1898], [1898], .contexts []⟩,
    ⟨[1901], [1898], .contexts [
        ⟨8135, false, false, [], []⟩,
        ⟨8136, false, false, [], []⟩,
        ⟨8137, false, false, [], []⟩,
        ⟨8137, false, false, [], []⟩
      ]⟩,
    ⟨[77683, 9], [1901, 78517], .contexts [
        ⟨8133, false, false, [], []⟩,
        ⟨8131, true, false, [1898], [9]⟩,
        ⟨8130, true, false, [1898], [9]⟩,
        ⟨8129, true, false, [1898], [9]⟩,
        ⟨8128, true, false, [1898], [9]⟩,
        ⟨8127, true, false, [1898], [1, 9]⟩,
        ⟨8126, true, false, [1898], [1, 9]⟩,
        ⟨8125, true, false, [1898], [1, 9]⟩,
        ⟨8124, true, false, [1898], [1, 9]⟩,
        ⟨8123, true, false, [1898], [9, 1, 9]⟩,
        ⟨1022, false, false, [1898, 78521], []⟩,
        ⟨787, false, false, [1898, 78521], []⟩,
        ⟨8132, false, false, [1898], [1]⟩,
        ⟨7898, false, false, [1898], []⟩,
        ⟨7899, false, false, [1898], []⟩,
        ⟨7855, false, false, [1898], []⟩,
        ⟨7855, false, false, [1898], []⟩,
        ⟨8134, false, false, [1898], []⟩,
        ⟨8138, true, false, [], [78517]⟩
      ]⟩,
    ⟨[1899], [1900], .contexts [
        ⟨8094, true, true, [], []⟩
      ]⟩,
    ⟨[1911, 78519], [1911, 78519], .contexts []⟩,
    ⟨[78519, 11], [1911, 78519], .contexts [
        ⟨8106, false, false, [], []⟩,
        ⟨8106, false, false, [], []⟩,
        ⟨7859, true, false, [], [11]⟩,
        ⟨8105, false, false, [1906], [78521, 9, 11]⟩,
        ⟨8061, true, false, [1906, 691], [9, 11]⟩,
        ⟨8104, true, false, [1906], [11, 9, 11]⟩,
        ⟨966, false, false, [1906, 77585], []⟩,
        ⟨967, false, false, [1906, 77585], []⟩,
        ⟨8096, false, false, [1906], [9]⟩,
        ⟨7859, false, false, [1906, 1879], []⟩,
        ⟨8107, false, false, [1906, 1879], []⟩,
        ⟨8108, true, false, [], [1879, 78519]⟩,
        ⟨8109, true, false, [], [78519]⟩,
        ⟨8141, false, false, [], []⟩,
        ⟨8141, false, false, [], []⟩
      ]⟩,
    ⟨[78519, 1], [78517], .contexts [
        ⟨7898, false, false, [], []⟩,
        ⟨7899, false, false, [], []⟩,
        ⟨7855, false, false, [], []⟩,
        ⟨7855, false, false, [], []⟩
      ]⟩,
    ⟨[78519, 0], [78519, 1], .contexts [
        ⟨19, false, false, [78519], []⟩
      ]⟩,
    ⟨[78517, 11], [78517, 11], .contexts []⟩,
    ⟨[1919], [1910], .source 1024⟩,
    ⟨[1910], [1910], .contexts []⟩,
    ⟨[78517, 11], [1919, 78517], .contexts [
        ⟨8145, false, false, [], []⟩,
        ⟨7856, true, false, [], [11]⟩,
        ⟨8142, true, false, [1910], [1, 11]⟩,
        ⟨1000, false, false, [1910, 78519], []⟩,
        ⟨8144, false, false, [1910], []⟩,
        ⟨8143, false, false, [1910], []⟩,
        ⟨8134, false, false, [1910], []⟩,
        ⟨8147, true, false, [], [78517]⟩,
        ⟨8147, true, false, [], [78517]⟩,
        ⟨8146, true, false, [], [78517]⟩
      ]⟩,
    ⟨[77575, 1, 9, 1], [1895, 77571], .contexts [
        ⟨8113, false, false, [], [9, 1]⟩,
        ⟨8113, false, false, [], [9, 1]⟩,
        ⟨3526, true, false, [], [1, 9, 1]⟩,
        ⟨992, false, false, [77577], [9, 1]⟩,
        ⟨993, false, false, [77577], [9, 1]⟩,
        ⟨8110, false, false, [], [11, 9, 1]⟩,
        ⟨3106, false, false, [1895], [9, 1]⟩,
        ⟨8111, false, false, [], [9, 1]⟩,
        ⟨8112, false, false, [], [9, 1]⟩,
        ⟨3528, false, false, [1895], [9, 1]⟩,
        ⟨8080, true, false, [], [77575, 9, 1]⟩,
        ⟨8079, true, false, [], [77575, 9, 1]⟩,
        ⟨24, true, false, [], [1895, 77575, 9, 1]⟩,
        ⟨8111, false, false, [], [9, 1]⟩,
        ⟨8112, false, false, [], [9, 1]⟩,
        ⟨8112, false, false, [], [9, 1]⟩,
        ⟨3102, false, false, [1895], [1]⟩,
        ⟨3099, false, false, [1895], []⟩
      ]⟩,
    ⟨[77571, 9], [77571, 9], .contexts []⟩,
    ⟨[1894], [1894], .contexts []⟩,
    ⟨[1893], [1894], .contexts [
        ⟨8084, false, false, [], []⟩,
        ⟨8151, false, false, [], []⟩,
        ⟨8151, false, false, [], []⟩
      ]⟩,
    ⟨[1917, 78239], [1917, 78239], .contexts []⟩,
    ⟨[78237, 3], [78237, 3], .contexts []⟩,
    ⟨[1921], [1916], .source 1025⟩,
    ⟨[1916], [1916], .contexts []⟩,
    ⟨[1901, 78517], [1901, 78517], .contexts []⟩,
    ⟨[77683, 9], [1901, 78517], .contexts [
        ⟨8133, false, false, [], []⟩,
        ⟨8139, false, false, [], []⟩,
        ⟨8157, false, false, [], []⟩,
        ⟨8157, false, false, [], []⟩
      ]⟩,
    ⟨[1923], [1773, 1901], .source 1026⟩,
    ⟨[78517, 3], [78517, 3], .contexts []⟩,
    ⟨[1899], [1900], .contexts [
        ⟨8140, false, false, [], []⟩
      ]⟩,
    ⟨[1925], [1899, 1923], .source 1027⟩,
    ⟨[78517, 3], [1925, 78517], .contexts [
        ⟨8160, false, false, [], []⟩,
        ⟨8158, true, false, [1900], [3]⟩,
        ⟨306, false, false, [1900, 77683], []⟩,
        ⟨307, false, false, [1900, 77683], []⟩,
        ⟨7606, false, false, [1900], [9]⟩,
        ⟨8139, false, false, [1900, 1773], []⟩,
        ⟨8159, true, false, [1900], [78517]⟩,
        ⟨8134, false, false, [1900, 1923], []⟩,
        ⟨8161, true, false, [], [1923, 78517]⟩,
        ⟨8162, true, false, [], [78517]⟩
      ]⟩,
    ⟨[77683, 4], [77683, 5], .contexts [
        ⟨50, false, false, [77683], []⟩
      ]⟩,
    ⟨[78515, 9], [78515, 9], .contexts []⟩,
    ⟨[77681], [77681], .contexts []⟩,
    ⟨[1900], [1900], .contexts []⟩,
    ⟨[1899], [1900], .contexts [
        ⟨8161, false, false, [], []⟩,
        ⟨8167, false, false, [], []⟩,
        ⟨8167, false, false, [], []⟩
      ]⟩,
    ⟨[78515, 9], [1899, 77681], .contexts [
        ⟨8165, false, false, [], []⟩,
        ⟨7852, true, false, [], [9]⟩,
        ⟨8158, true, false, [1900], [5, 9]⟩,
        ⟨1034, false, false, [1900, 77683], []⟩,
        ⟨8164, false, false, [1900], []⟩,
        ⟨7607, false, false, [1900], []⟩,
        ⟨8166, false, false, [1900], []⟩,
        ⟨8168, true, false, [], [77681]⟩
      ]⟩,
    ⟨[77681, 9], [1901, 78515], .contexts [
        ⟨8169, true, false, [1898], [9]⟩,
        ⟨76, false, false, [1898, 78515], []⟩,
        ⟨8094, true, false, [], [78515]⟩
      ]⟩,
    ⟨[1919, 78517], [1919, 78517], .contexts []⟩,
    ⟨[78517, 5], [78515], .contexts [
        ⟨7900, false, false, [], []⟩,
        ⟨7901, false, false, [], []⟩,
        ⟨7851, false, false, [], []⟩,
        ⟨7851, false, false, [], []⟩
      ]⟩,
    ⟨[78515], [78515], .contexts []⟩,
    ⟨[1918], [1918], .contexts []⟩,
    ⟨[1893, 77571], [1893, 77571], .contexts []⟩,
    ⟨[77571, 9], [1893, 77571], .contexts [
        ⟨8150, false, false, [], []⟩,
        ⟨8150, false, false, [], []⟩,
        ⟨8149, true, false, [1894], [9]⟩,
        ⟨1022, false, false, [1894, 77575], []⟩,
        ⟨787, false, false, [1894, 77575], []⟩,
        ⟨3538, false, false, [1894], [1]⟩,
        ⟨3178, false, false, [1894], []⟩,
        ⟨3179, false, false, [1894], []⟩,
        ⟨3098, false, false, [1894], []⟩,
        ⟨3098, false, false, [1894], []⟩,
        ⟨3548, false, false, [1894], []⟩,
        ⟨8152, true, false, [], [77571]⟩,
        ⟨8175, false, false, [], []⟩,
        ⟨8175, false, false, [], []⟩
      ]⟩,
    ⟨[77569, 9], [77569, 9], .contexts []⟩,
    ⟨[1892], [1892], .contexts []⟩,
    ⟨[1921, 78237], [1921, 78237], .contexts []⟩,
    ⟨[78237, 3], [1921, 78237], .contexts [
        ⟨8154, false, false, [], []⟩,
        ⟨8154, false, false, [], []⟩,
        ⟨6504, true, false, [], [3]⟩,
        ⟨8153, true, false, [1916], [11, 3]⟩,
        ⟨8153, true, false, [1916], [11, 3]⟩,
        ⟨8119, true, false, [1916], [11, 3]⟩,
        ⟨8116, true, false, [1916], [11, 3]⟩,
        ⟨976, false, false, [1916, 78239], []⟩,
        ⟨6711, false, false, [1916], []⟩,
        ⟨6710, false, false, [1916], []⟩,
        ⟨6713, false, false, [1916], []⟩,
        ⟨8156, true, false, [], [78237]⟩,
        ⟨8156, true, false, [], [78237]⟩,
        ⟨8155, true, false, [], [78237]⟩,
        ⟨8179, false, false, [], []⟩,
        ⟨8179, false, false, [], []⟩
      ]⟩,
    ⟨[78235, 3], [78235, 3], .contexts []⟩,
    ⟨[1920], [1920], .contexts []⟩,
    ⟨[1925, 78517], [1925, 78517], .contexts []⟩,
    ⟨[78513, 5], [78513, 5], .contexts []⟩,
    ⟨[78513], [78513], .contexts []⟩,
    ⟨[1927], [1924], .source 1028⟩,
    ⟨[1924], [1924], .contexts []⟩,
    ⟨[78513, 5], [1927, 78513], .contexts [
        ⟨8184, false, false, [], []⟩,
        ⟨7849, true, false, [], [5]⟩,
        ⟨7852, true, false, [], [3, 5]⟩,
        ⟨8183, true, false, [1924], [5, 3, 5]⟩,
        ⟨8183, true, false, [1924], [5, 3, 5]⟩,
        ⟨8163, true, false, [1924], [5, 3, 5]⟩,
        ⟨8160, true, false, [1924], [5, 3, 5]⟩,
        ⟨4744, false, false, [1924, 78517], []⟩,
        ⟨766, false, false, [1924, 78517], []⟩,
        ⟨8172, false, false, [1924], [3]⟩,
        ⟨7902, false, false, [1924], []⟩,
        ⟨7903, false, false, [1924], []⟩,
        ⟨7848, false, false, [1924], []⟩,
        ⟨7848, false, false, [1924], []⟩,
        ⟨8185, false, false, [1924], []⟩,
        ⟨8187, true, false, [], [78513]⟩,
        ⟨8187, true, false, [], [78513]⟩,
        ⟨8186, true, false, [], [78513]⟩
      ]⟩,
    ⟨[1899, 77681], [1899, 77681], .contexts []⟩,
    ⟨[1899, 77681], [1899, 77681], .contexts []⟩,
    ⟨[1899, 77679], [1899, 77679], .contexts []⟩]

/-- Literal contextual derivation data in chronological chunk 01. -/
def y322TCContextRawChunk01 (i : Fin 4096) : Y322RawContextCertificate :=
  if i.val < 2048 then
    if i.val < 1024 then
      if i.val < 512 then
        if i.val < 256 then
          if i.val < 128 then
            if i.val < 64 then
              y322TCContextRaw064 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw065 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 192 then
              y322TCContextRaw066 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw067 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 384 then
            if i.val < 320 then
              y322TCContextRaw068 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw069 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 448 then
              y322TCContextRaw070 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw071 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 768 then
          if i.val < 640 then
            if i.val < 576 then
              y322TCContextRaw072 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw073 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 704 then
              y322TCContextRaw074 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw075 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 896 then
            if i.val < 832 then
              y322TCContextRaw076 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw077 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 960 then
              y322TCContextRaw078 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw079 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 1536 then
        if i.val < 1280 then
          if i.val < 1152 then
            if i.val < 1088 then
              y322TCContextRaw080 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw081 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1216 then
              y322TCContextRaw082 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw083 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1408 then
            if i.val < 1344 then
              y322TCContextRaw084 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw085 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1472 then
              y322TCContextRaw086 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw087 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 1792 then
          if i.val < 1664 then
            if i.val < 1600 then
              y322TCContextRaw088 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw089 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1728 then
              y322TCContextRaw090 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw091 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1920 then
            if i.val < 1856 then
              y322TCContextRaw092 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw093 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1984 then
              y322TCContextRaw094 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw095 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  else
    if i.val < 3072 then
      if i.val < 2560 then
        if i.val < 2304 then
          if i.val < 2176 then
            if i.val < 2112 then
              y322TCContextRaw096 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw097 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2240 then
              y322TCContextRaw098 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw099 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2432 then
            if i.val < 2368 then
              y322TCContextRaw100 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw101 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2496 then
              y322TCContextRaw102 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw103 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 2816 then
          if i.val < 2688 then
            if i.val < 2624 then
              y322TCContextRaw104 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw105 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2752 then
              y322TCContextRaw106 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw107 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2944 then
            if i.val < 2880 then
              y322TCContextRaw108 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw109 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3008 then
              y322TCContextRaw110 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw111 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 3584 then
        if i.val < 3328 then
          if i.val < 3200 then
            if i.val < 3136 then
              y322TCContextRaw112 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw113 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3264 then
              y322TCContextRaw114 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw115 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3456 then
            if i.val < 3392 then
              y322TCContextRaw116 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw117 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3520 then
              y322TCContextRaw118 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw119 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 3840 then
          if i.val < 3712 then
            if i.val < 3648 then
              y322TCContextRaw120 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw121 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3776 then
              y322TCContextRaw122 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw123 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3968 then
            if i.val < 3904 then
              y322TCContextRaw124 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw125 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 4032 then
              y322TCContextRaw126 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCContextRaw127 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
