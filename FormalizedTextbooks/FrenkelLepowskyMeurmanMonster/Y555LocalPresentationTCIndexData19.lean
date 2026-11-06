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

/-- Exact literal claimed equations and contextual derivations, block 1216. -/
def y322TCIndexRaw1216 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93183, 15], [93183, 15], .contexts []⟩,
    ⟨[25053], [25053], .contexts [
        ⟨13, false, false, [], [25053]⟩
      ]⟩,
    ⟨[93183, 15], [25053, 93183], .contexts [
        ⟨77824, false, false, [], []⟩,
        ⟨77812, true, false, [], [15]⟩,
        ⟨231, false, false, [90467], []⟩,
        ⟨232, false, false, [90467], []⟩,
        ⟨61021, false, false, [], [11]⟩,
        ⟨77808, false, false, [25053], []⟩,
        ⟨77822, false, false, [], []⟩,
        ⟨77823, false, false, [], []⟩,
        ⟨77814, false, false, [25053], []⟩,
        ⟨77825, true, false, [], [93183]⟩
      ]⟩,
    ⟨[93185], [93183, 1], .source 46657⟩,
    ⟨[93183, 1], [93185], .contexts [
        ⟨77827, true, false, [], []⟩
      ]⟩,
    ⟨[93185, 1], [93183], .contexts [
        ⟨77828, true, false, [], [1]⟩,
        ⟨8, false, false, [93183], []⟩,
        ⟨77811, false, false, [], []⟩
      ]⟩,
    ⟨[93185], [93185], .contexts []⟩,
    ⟨[93185], [93185], .contexts []⟩,
    ⟨[93183, 1], [93185], .contexts [
        ⟨77828, false, false, [], []⟩,
        ⟨77830, false, false, [], []⟩,
        ⟨77831, false, false, [], []⟩,
        ⟨77831, false, false, [], []⟩
      ]⟩,
    ⟨[25059, 93185], [25059, 93185], .contexts []⟩,
    ⟨[25059, 93185], [25059, 93185], .contexts []⟩,
    ⟨[93185, 5], [93185, 5], .contexts []⟩,
    ⟨[93185], [93185], .contexts []⟩,
    ⟨[93185, 5], [25059, 93185], .contexts [
        ⟨77835, false, false, [], []⟩,
        ⟨77832, true, false, [], [5]⟩,
        ⟨98, false, false, [93183], []⟩,
        ⟨99, false, false, [93183], []⟩,
        ⟨77817, false, false, [], [1]⟩,
        ⟨77818, false, false, [], [1]⟩,
        ⟨77815, false, false, [], [1]⟩,
        ⟨77816, false, false, [], [1]⟩,
        ⟨77816, false, false, [], [1]⟩,
        ⟨77828, false, false, [25059], []⟩,
        ⟨77833, false, false, [], []⟩,
        ⟨77834, false, false, [], []⟩,
        ⟨77836, false, false, [25059], []⟩,
        ⟨61017, true, false, [], [93185]⟩
      ]⟩,
    ⟨[93183, 11], [90467], .contexts [
        ⟨77809, false, false, [], []⟩
      ]⟩,
    ⟨[90465], [25059, 90463], .contexts [
        ⟨61038, false, false, [], []⟩
      ]⟩,
    ⟨[93185, 11], [93185, 11], .contexts []⟩,
    ⟨[93185, 11], [25059, 90463], .contexts [
        ⟨77840, false, false, [], []⟩,
        ⟨77832, true, false, [], [11]⟩,
        ⟨110, false, false, [93183], []⟩,
        ⟨111, false, false, [93183], []⟩,
        ⟨77838, false, false, [], [1]⟩,
        ⟨60722, false, false, [], [1]⟩,
        ⟨60689, false, false, [], [1]⟩,
        ⟨60689, false, false, [], [1]⟩,
        ⟨60723, false, false, [], []⟩,
        ⟨77839, false, false, [], []⟩,
        ⟨61030, false, false, [], []⟩,
        ⟨61030, false, false, [], []⟩,
        ⟨61056, false, false, [25059], []⟩,
        ⟨61017, true, false, [], [90463]⟩
      ]⟩,
    ⟨[90463, 11], [25073, 93185], .contexts [
        ⟨77841, true, false, [25058], [11]⟩,
        ⟨53, false, false, [25058, 93185], []⟩,
        ⟨61032, true, false, [], [93185]⟩
      ]⟩,
    ⟨[25053, 93185], [25053, 93185], .contexts []⟩,
    ⟨[25053, 93185], [25053, 93185], .contexts []⟩,
    ⟨[93185, 15], [25053, 93185], .contexts [
        ⟨77832, true, false, [], [15]⟩,
        ⟨121, false, false, [93183], []⟩,
        ⟨122, false, false, [93183], []⟩,
        ⟨77824, false, false, [], [1]⟩,
        ⟨77826, false, false, [], [1]⟩,
        ⟨77822, false, false, [], [1]⟩,
        ⟨77823, false, false, [], [1]⟩,
        ⟨77823, false, false, [], [1]⟩,
        ⟨77828, false, false, [25053], []⟩,
        ⟨77843, false, false, [], []⟩,
        ⟨77844, false, false, [], []⟩,
        ⟨77836, false, false, [25053], []⟩,
        ⟨77825, true, false, [], [93185]⟩
      ]⟩,
    ⟨[93187], [93185, 13], .source 46658⟩,
    ⟨[93185, 13], [93187], .contexts [
        ⟨77846, true, false, [], []⟩
      ]⟩,
    ⟨[93187, 13], [93185], .contexts [
        ⟨77847, true, false, [], [13]⟩,
        ⟨59, false, false, [93185], []⟩,
        ⟨77831, false, false, [], []⟩
      ]⟩,
    ⟨[93187], [93187], .contexts []⟩,
    ⟨[93187], [93187], .contexts []⟩,
    ⟨[93185, 13], [93187], .contexts [
        ⟨77847, false, false, [], []⟩,
        ⟨77849, false, false, [], []⟩,
        ⟨77850, false, false, [], []⟩,
        ⟨77850, false, false, [], []⟩
      ]⟩,
    ⟨[25059, 93187], [25059, 93187], .contexts []⟩,
    ⟨[25059, 93187], [25059, 93187], .contexts []⟩,
    ⟨[93187, 5], [93187, 5], .contexts []⟩,
    ⟨[93187], [93187], .contexts []⟩,
    ⟨[93187, 5], [25059, 93187], .contexts [
        ⟨77854, false, false, [], []⟩,
        ⟨77851, true, false, [], [5]⟩,
        ⟨68, false, false, [93185], []⟩,
        ⟨69, false, false, [93185], []⟩,
        ⟨77835, false, false, [], [13]⟩,
        ⟨77837, false, false, [], [13]⟩,
        ⟨77833, false, false, [], [13]⟩,
        ⟨77834, false, false, [], [13]⟩,
        ⟨77834, false, false, [], [13]⟩,
        ⟨77847, false, false, [25059], []⟩,
        ⟨77852, false, false, [], []⟩,
        ⟨77853, false, false, [], []⟩,
        ⟨77855, false, false, [25059], []⟩,
        ⟨61017, true, false, [], [93187]⟩
      ]⟩,
    ⟨[29701], [25059, 25085], .source 14915⟩,
    ⟨[93187, 11], [93187, 11], .contexts []⟩,
    ⟨[93187, 11], [29701, 89423], .contexts [
        ⟨77858, false, false, [], []⟩,
        ⟨77851, true, false, [], [11]⟩,
        ⟨82, false, false, [93185], []⟩,
        ⟨83, false, false, [93185], []⟩,
        ⟨77840, false, false, [], [13]⟩,
        ⟨77841, false, false, [], [13]⟩,
        ⟨61029, false, false, [], [13]⟩,
        ⟨61030, false, false, [], [13]⟩,
        ⟨61030, false, false, [], [13]⟩,
        ⟨61060, false, false, [25059], []⟩,
        ⟨77857, true, false, [], [89423]⟩,
        ⟨61088, false, false, [29701], []⟩,
        ⟨13, true, false, [], [29701, 89423]⟩
      ]⟩,
    ⟨[29703], [29700], .source 14916⟩,
    ⟨[93187, 11], [29701, 89423], .contexts [
        ⟨77859, false, false, [], []⟩
      ]⟩,
    ⟨[29701, 89423], [29701, 89423], .contexts []⟩,
    ⟨[29705], [29701, 24091], .source 14917⟩,
    ⟨[29705, 83615], [29705, 83615], .contexts []⟩,
    ⟨[29705, 83615], [29705, 83615], .contexts []⟩,
    ⟨[29707], [29704], .source 14918⟩,
    ⟨[29704], [29704], .contexts []⟩,
    ⟨[83615, 7], [29707, 93187], .contexts [
        ⟨77865, true, false, [29704], [7]⟩,
        ⟨77864, true, false, [29704], [7]⟩,
        ⟨22159, true, false, [], [7]⟩,
        ⟨77863, false, false, [29704], [83617, 11, 7]⟩,
        ⟨56087, true, false, [29704, 29701], [11, 7]⟩,
        ⟨77862, true, false, [29704], [7, 11, 7]⟩,
        ⟨77862, true, false, [29704], [7, 11, 7]⟩,
        ⟨77861, true, false, [29704], [7, 11, 7]⟩,
        ⟨77858, true, false, [29704], [7, 11, 7]⟩,
        ⟨14923, false, false, [29704, 93187], []⟩,
        ⟨77855, false, false, [29704], []⟩,
        ⟨77867, true, false, [], [93187]⟩,
        ⟨77867, true, false, [], [93187]⟩,
        ⟨77866, true, false, [], [93187]⟩
      ]⟩,
    ⟨[93187, 7], [29705, 83615], .contexts [
        ⟨77868, true, false, [29706], [7]⟩,
        ⟨38, false, false, [29706, 83615], []⟩,
        ⟨77866, false, true, [], [83615]⟩
      ]⟩,
    ⟨[93189], [93187, 15], .source 46659⟩,
    ⟨[93187, 15], [93189], .contexts [
        ⟨77870, true, false, [], []⟩
      ]⟩,
    ⟨[93189, 15], [93187], .contexts [
        ⟨77871, true, false, [], [15]⟩,
        ⟨1, false, false, [93187], []⟩,
        ⟨77850, false, false, [], []⟩
      ]⟩,
    ⟨[93189], [93189], .contexts []⟩,
    ⟨[93189], [93189], .contexts []⟩,
    ⟨[93187, 15], [93189], .contexts [
        ⟨77871, false, false, [], []⟩,
        ⟨77873, false, false, [], []⟩,
        ⟨77874, false, false, [], []⟩,
        ⟨77874, false, false, [], []⟩
      ]⟩,
    ⟨[25059, 93189], [25059, 93189], .contexts []⟩,
    ⟨[25059, 93189], [25059, 93189], .contexts []⟩,
    ⟨[93189, 5], [93189, 5], .contexts []⟩,
    ⟨[93189], [93189], .contexts []⟩,
    ⟨[93189, 5], [25059, 93189], .contexts [
        ⟨77878, false, false, [], []⟩,
        ⟨77875, true, false, [], [5]⟩,
        ⟨27, false, false, [93187], []⟩,
        ⟨30, false, false, [93187], []⟩,
        ⟨77854, false, false, [], [15]⟩,
        ⟨77856, false, false, [], [15]⟩,
        ⟨77852, false, false, [], [15]⟩,
        ⟨77853, false, false, [], [15]⟩,
        ⟨77853, false, false, [], [15]⟩,
        ⟨77871, false, false, [25059], []⟩,
        ⟨77876, false, false, [], []⟩,
        ⟨77877, false, false, [], []⟩,
        ⟨77879, false, false, [25059], []⟩,
        ⟨61017, true, false, [], [93189]⟩
      ]⟩,
    ⟨[93187, 7], [29705, 83615], .contexts [
        ⟨77869, false, false, [], []⟩
      ]⟩,
    ⟨[29709], [29705, 20717], .source 14919⟩,
    ⟨[93189, 7], [93189, 7], .contexts []⟩,
    ⟨[29709], [29709], .contexts [
        ⟨13, false, false, [], [29709]⟩
      ]⟩,
    ⟨[93189, 7], [29709, 83239], .contexts [
        ⟨77883, false, false, [], []⟩,
        ⟨77875, true, false, [], [7]⟩,
        ⟨37, false, false, [93187], []⟩,
        ⟨40, false, false, [93187], []⟩,
        ⟨77881, false, false, [], [15]⟩,
        ⟨77864, false, false, [], [15]⟩,
        ⟨77865, false, false, [], [15]⟩,
        ⟨77865, false, false, [], [15]⟩,
        ⟨43435, false, false, [29705], []⟩,
        ⟨77882, true, false, [], [83239]⟩,
        ⟨43434, false, false, [29709], []⟩,
        ⟨77884, true, false, [], [83239]⟩
      ]⟩,
    ⟨[29711], [29708], .source 14920⟩,
    ⟨[93187, 13], [93185], .contexts [
        ⟨77848, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1217. -/
def y322TCIndexRaw1217 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93187, 13], [93185], .contexts [
        ⟨77887, false, false, [], []⟩,
        ⟨77830, false, false, [], []⟩,
        ⟨77831, false, false, [], []⟩,
        ⟨77831, false, false, [], []⟩
      ]⟩,
    ⟨[25053, 93189], [25053, 93189], .contexts []⟩,
    ⟨[25053, 93189], [25053, 93189], .contexts []⟩,
    ⟨[93189, 13], [93189, 13], .contexts []⟩,
    ⟨[93189, 13], [25053, 93189], .contexts [
        ⟨77891, false, false, [], []⟩,
        ⟨77875, true, false, [], [13]⟩,
        ⟨259, false, false, [93187], []⟩,
        ⟨262, false, false, [93187], []⟩,
        ⟨77888, false, false, [], [15, 13, 15]⟩,
        ⟨77845, false, false, [], [13, 15]⟩,
        ⟨77843, false, false, [], [13, 15]⟩,
        ⟨77844, false, false, [], [13, 15]⟩,
        ⟨77844, false, false, [], [13, 15]⟩,
        ⟨77847, false, false, [25053], [15]⟩,
        ⟨77871, false, false, [25053], []⟩,
        ⟨77889, false, false, [], []⟩,
        ⟨77890, false, false, [], []⟩,
        ⟨77879, false, false, [25053], []⟩,
        ⟨77825, true, false, [], [93189]⟩
      ]⟩,
    ⟨[93191], [93189, 1], .source 46660⟩,
    ⟨[93189, 1], [93191], .contexts [
        ⟨77893, true, false, [], []⟩
      ]⟩,
    ⟨[93191, 1], [93189], .contexts [
        ⟨77894, true, false, [], [1]⟩,
        ⟨8, false, false, [93189], []⟩,
        ⟨77874, false, false, [], []⟩
      ]⟩,
    ⟨[93189, 1], [93191], .contexts [
        ⟨77894, false, false, [], []⟩
      ]⟩,
    ⟨[93191], [93191], .contexts []⟩,
    ⟨[93191], [93191], .contexts []⟩,
    ⟨[93189, 1], [93191], .contexts [
        ⟨77896, false, false, [], []⟩,
        ⟨77897, false, false, [], []⟩,
        ⟨77898, false, false, [], []⟩,
        ⟨77898, false, false, [], []⟩
      ]⟩,
    ⟨[93189, 5], [25059, 93189], .contexts [
        ⟨77878, false, false, [], []⟩,
        ⟨77880, false, false, [], []⟩,
        ⟨77876, false, false, [], []⟩,
        ⟨77877, false, false, [], []⟩,
        ⟨77877, false, false, [], []⟩
      ]⟩,
    ⟨[25059, 93191], [25059, 93191], .contexts []⟩,
    ⟨[93191], [93191], .contexts []⟩,
    ⟨[29709, 83239], [29709, 83239], .contexts []⟩,
    ⟨[29709, 83239], [29709, 83239], .contexts []⟩,
    ⟨[93189, 7], [29709, 83239], .contexts [
        ⟨77883, false, false, [], []⟩,
        ⟨77885, false, false, [], []⟩,
        ⟨77903, false, false, [], []⟩,
        ⟨77904, false, false, [], []⟩,
        ⟨77904, false, false, [], []⟩
      ]⟩,
    ⟨[29709, 83237], [29709, 83237], .contexts []⟩,
    ⟨[29709, 83237], [29709, 83237], .contexts []⟩,
    ⟨[93191, 7], [93191, 7], .contexts []⟩,
    ⟨[93191, 7], [29709, 83237], .contexts [
        ⟨77908, false, false, [], []⟩,
        ⟨77899, true, false, [], [7]⟩,
        ⟨104, false, false, [93189], []⟩,
        ⟨105, false, false, [93189], []⟩,
        ⟨77905, false, false, [], [1]⟩,
        ⟨20195, false, false, [29709], []⟩,
        ⟨77906, false, false, [], []⟩,
        ⟨77907, false, false, [], []⟩,
        ⟨43317, false, false, [29709], []⟩,
        ⟨77884, true, false, [], [83237]⟩
      ]⟩,
    ⟨[83237, 7], [29711, 93191], .contexts [
        ⟨77909, true, false, [29708], [7]⟩,
        ⟨38, false, false, [29708, 93191], []⟩,
        ⟨77886, true, false, [], [93191]⟩
      ]⟩,
    ⟨[93193], [93191, 3], .source 46661⟩,
    ⟨[93191, 3], [93193], .contexts [
        ⟨77911, true, false, [], []⟩
      ]⟩,
    ⟨[93193, 3], [93191], .contexts [
        ⟨77912, true, false, [], [3]⟩,
        ⟨20, false, false, [93191], []⟩,
        ⟨77898, false, false, [], []⟩
      ]⟩,
    ⟨[93193], [93193], .contexts []⟩,
    ⟨[93193], [93193], .contexts []⟩,
    ⟨[29713], [29709, 20863], .source 14921⟩,
    ⟨[93193, 7], [93193, 7], .contexts []⟩,
    ⟨[29713], [29713], .contexts []⟩,
    ⟨[29713], [29713], .contexts []⟩,
    ⟨[93193, 7], [29713, 86441], .contexts [
        ⟨77917, false, false, [], []⟩,
        ⟨77915, true, false, [], [7]⟩,
        ⟨77915, true, false, [], [7]⟩,
        ⟨77914, true, false, [], [7]⟩,
        ⟨77912, true, false, [], [7]⟩,
        ⟨140, false, false, [93191], []⟩,
        ⟨141, false, false, [93191], []⟩,
        ⟨77908, false, false, [], [3]⟩,
        ⟨77909, false, false, [], [3]⟩,
        ⟨77906, false, false, [], [3]⟩,
        ⟨77907, false, false, [], [3]⟩,
        ⟨77907, false, false, [], [3]⟩,
        ⟨43322, false, false, [29709], []⟩,
        ⟨77916, true, false, [], [86441]⟩,
        ⟨37133, false, false, [29713], []⟩,
        ⟨77919, true, false, [], [86441]⟩,
        ⟨77918, true, false, [], [86441]⟩,
        ⟨13, true, false, [], [29713, 86441]⟩
      ]⟩,
    ⟨[29715], [29712], .source 14922⟩,
    ⟨[86441, 7], [29715, 93193], .contexts [
        ⟨77920, true, false, [29712], [7]⟩,
        ⟨38, false, false, [29712, 93193], []⟩,
        ⟨77921, true, false, [], [93193]⟩
      ]⟩,
    ⟨[93195], [93193, 5], .source 46662⟩,
    ⟨[93193, 5], [93195], .contexts [
        ⟨77923, true, false, [], []⟩
      ]⟩,
    ⟨[93195], [93195], .contexts []⟩,
    ⟨[93195], [93195], .contexts []⟩,
    ⟨[93193, 5], [93195], .contexts [
        ⟨77924, false, false, [], []⟩,
        ⟨77925, false, false, [], []⟩,
        ⟨77926, false, false, [], []⟩,
        ⟨77926, false, false, [], []⟩
      ]⟩,
    ⟨[93195], [93195], .contexts []⟩,
    ⟨[29713, 86441], [29713, 86441], .contexts []⟩,
    ⟨[29713, 86441], [29713, 86441], .contexts []⟩,
    ⟨[29717], [29713, 17027], .source 14923⟩,
    ⟨[29719], [29717, 29715], .source 14924⟩,
    ⟨[29719, 93195], [29719, 93195], .contexts []⟩,
    ⟨[29719, 93195], [29719, 93195], .contexts []⟩,
    ⟨[93195, 7], [93195, 7], .contexts []⟩,
    ⟨[93195, 7], [29719, 93195], .contexts [
        ⟨77935, false, false, [], []⟩,
        ⟨77927, true, false, [], [7]⟩,
        ⟨3272, false, false, [93193], []⟩,
        ⟨3275, false, false, [93193], []⟩,
        ⟨77917, false, false, [], [5, 7, 5]⟩,
        ⟨77920, false, false, [], [5, 7, 5]⟩,
        ⟨77929, false, false, [], [5, 7, 5]⟩,
        ⟨77930, false, false, [], [5, 7, 5]⟩,
        ⟨77930, false, false, [], [5, 7, 5]⟩,
        ⟨37134, false, false, [29713], [7, 5]⟩,
        ⟨77931, true, false, [], [86441, 7, 5]⟩,
        ⟨77922, false, false, [29717], [5]⟩,
        ⟨77932, true, false, [], [93193, 5]⟩,
        ⟨77924, false, false, [29719], []⟩,
        ⟨77933, false, false, [], []⟩,
        ⟨77934, false, false, [], []⟩,
        ⟨77928, false, false, [29719], []⟩
      ]⟩,
    ⟨[29719], [29719], .contexts [
        ⟨13, false, false, [], [29719]⟩
      ]⟩,
    ⟨[93197], [93195, 1], .source 46663⟩,
    ⟨[93195, 1], [93197], .contexts [
        ⟨77938, true, false, [], []⟩
      ]⟩,
    ⟨[93197], [93197], .contexts []⟩,
    ⟨[93197], [93197], .contexts []⟩,
    ⟨[29719, 93197], [29719, 93197], .contexts []⟩,
    ⟨[29719, 93197], [29719, 93197], .contexts []⟩,
    ⟨[93197, 7], [93197, 7], .contexts []⟩,
    ⟨[93199], [93197, 9], .source 46664⟩,
    ⟨[93197, 9], [93199], .contexts [
        ⟨77945, true, false, [], []⟩
      ]⟩,
    ⟨[93199], [93199], .contexts []⟩,
    ⟨[93199], [93199], .contexts []⟩,
    ⟨[93197, 7, 9], [29719, 93199], .contexts [
        ⟨77944, false, false, [], [9]⟩,
        ⟨77944, false, false, [], [9]⟩,
        ⟨77941, true, false, [], [7, 9]⟩,
        ⟨77941, true, false, [], [7, 9]⟩,
        ⟨77940, true, false, [], [7, 9]⟩,
        ⟨77939, true, false, [], [7, 9]⟩,
        ⟨104, false, false, [93195], [9]⟩,
        ⟨105, false, false, [93195], [9]⟩,
        ⟨77935, false, false, [], [1, 9]⟩,
        ⟨77936, false, false, [], [1, 9]⟩,
        ⟨77937, true, false, [], [93195, 1, 9]⟩,
        ⟨77933, false, false, [], [1, 9]⟩,
        ⟨77934, false, false, [], [1, 9]⟩,
        ⟨77934, false, false, [], [1, 9]⟩,
        ⟨77939, false, false, [29719], [9]⟩,
        ⟨77942, false, false, [], [9]⟩,
        ⟨77943, false, false, [], [9]⟩,
        ⟨77937, true, false, [], [93197, 9]⟩,
        ⟨77942, false, false, [], [9]⟩,
        ⟨77943, false, false, [], [9]⟩,
        ⟨77943, false, false, [], [9]⟩,
        ⟨77946, false, false, [29719], []⟩
      ]⟩,
    ⟨[29719, 93199], [29719, 93199], .contexts []⟩,
    ⟨[29719, 93199], [29719, 93199], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1218. -/
def y322TCIndexRaw1218 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93199, 7], [93199, 7], .contexts []⟩,
    ⟨[93201], [93199, 11], .source 46665⟩,
    ⟨[93199, 11], [93201], .contexts [
        ⟨77953, true, false, [], []⟩
      ]⟩,
    ⟨[93201], [93201], .contexts []⟩,
    ⟨[93201], [93201], .contexts []⟩,
    ⟨[29719, 93201], [29719, 93201], .contexts []⟩,
    ⟨[29719, 93201], [29719, 93201], .contexts []⟩,
    ⟨[93199, 7, 11], [29719, 93201], .contexts [
        ⟨77952, false, false, [], [11]⟩,
        ⟨77952, false, false, [], [11]⟩,
        ⟨77948, true, false, [], [7, 11]⟩,
        ⟨77948, true, false, [], [7, 11]⟩,
        ⟨77947, true, false, [], [7, 11]⟩,
        ⟨77946, true, false, [], [7, 11]⟩,
        ⟨1084, false, false, [93197], [11]⟩,
        ⟨1085, false, false, [93197], [11]⟩,
        ⟨77949, false, false, [], [11]⟩,
        ⟨77950, false, false, [], [11]⟩,
        ⟨77951, false, false, [], [11]⟩,
        ⟨77937, true, false, [], [93199, 11]⟩,
        ⟨77950, false, false, [], [11]⟩,
        ⟨77951, false, false, [], [11]⟩,
        ⟨77951, false, false, [], [11]⟩,
        ⟨77954, false, false, [29719], []⟩,
        ⟨77957, false, false, [], []⟩,
        ⟨77958, false, false, [], []⟩
      ]⟩,
    ⟨[93201, 7], [93201, 7], .contexts []⟩,
    ⟨[93203], [93201, 1], .source 46666⟩,
    ⟨[93201, 1], [93203], .contexts [
        ⟨77961, true, false, [], []⟩
      ]⟩,
    ⟨[93203, 1], [93201], .contexts [
        ⟨77962, true, false, [], [1]⟩,
        ⟨8, false, false, [93201], []⟩,
        ⟨77956, false, false, [], []⟩
      ]⟩,
    ⟨[93203], [93203], .contexts []⟩,
    ⟨[93203], [93203], .contexts []⟩,
    ⟨[29719, 93203], [29719, 93203], .contexts []⟩,
    ⟨[93201, 7, 1], [29719, 93203], .contexts [
        ⟨77960, false, false, [], [1]⟩,
        ⟨77960, false, false, [], [1]⟩,
        ⟨77956, true, false, [], [7, 1]⟩,
        ⟨77956, true, false, [], [7, 1]⟩,
        ⟨77955, true, false, [], [7, 1]⟩,
        ⟨77954, true, false, [], [7, 1]⟩,
        ⟨647, false, false, [93199], [1]⟩,
        ⟨648, false, false, [93199], [1]⟩,
        ⟨77959, false, false, [], [1]⟩,
        ⟨77937, true, false, [], [93201, 1]⟩,
        ⟨77957, false, false, [], [1]⟩,
        ⟨77958, false, false, [], [1]⟩,
        ⟨77958, false, false, [], [1]⟩,
        ⟨77962, false, false, [29719], []⟩,
        ⟨77966, false, false, [], []⟩
      ]⟩,
    ⟨[93203], [93203], .contexts []⟩,
    ⟨[93203, 7], [29719, 93203], .contexts [
        ⟨77965, true, false, [], [7]⟩,
        ⟨77965, true, false, [], [7]⟩,
        ⟨77964, true, false, [], [7]⟩,
        ⟨77962, true, false, [], [7]⟩,
        ⟨104, false, false, [93201], []⟩,
        ⟨105, false, false, [93201], []⟩,
        ⟨77967, false, false, [], []⟩,
        ⟨77968, false, false, [29719], []⟩,
        ⟨77937, true, false, [], [93203]⟩
      ]⟩,
    ⟨[93205], [93203, 13], .source 46667⟩,
    ⟨[93203, 13], [93205], .contexts [
        ⟨77970, true, false, [], []⟩
      ]⟩,
    ⟨[93205, 13], [93203], .contexts [
        ⟨77971, true, false, [], [13]⟩,
        ⟨59, false, false, [93203], []⟩,
        ⟨77965, false, false, [], []⟩
      ]⟩,
    ⟨[93205], [93205], .contexts []⟩,
    ⟨[93205], [93205], .contexts []⟩,
    ⟨[93207], [93205, 15], .source 46668⟩,
    ⟨[93207, 15], [93205], .contexts [
        ⟨77975, false, false, [], [15]⟩,
        ⟨1, false, false, [93205], []⟩,
        ⟨77974, false, false, [], []⟩
      ]⟩,
    ⟨[93207], [93207], .contexts []⟩,
    ⟨[93207], [93207], .contexts []⟩,
    ⟨[93209], [93207, 1], .source 46669⟩,
    ⟨[93209, 1], [93207], .contexts [
        ⟨77979, false, false, [], [1]⟩,
        ⟨8, false, false, [93207], []⟩,
        ⟨77978, false, false, [], []⟩
      ]⟩,
    ⟨[93209], [93209], .contexts []⟩,
    ⟨[93209], [93209], .contexts []⟩,
    ⟨[93211], [93209, 3], .source 46670⟩,
    ⟨[93211, 3], [93209], .contexts [
        ⟨77983, false, false, [], [3]⟩,
        ⟨20, false, false, [93209], []⟩,
        ⟨77982, false, false, [], []⟩
      ]⟩,
    ⟨[93211], [93211], .contexts []⟩,
    ⟨[93211], [93211], .contexts []⟩,
    ⟨[93213], [93211, 5], .source 46671⟩,
    ⟨[93213, 5], [93211], .contexts [
        ⟨77987, false, false, [], [5]⟩,
        ⟨28, false, false, [93211], []⟩,
        ⟨77986, false, false, [], []⟩
      ]⟩,
    ⟨[93215], [93213, 1], .source 46672⟩,
    ⟨[93213], [93213], .contexts []⟩,
    ⟨[93215, 1], [93213], .contexts [
        ⟨77989, false, false, [], [1]⟩,
        ⟨8, false, false, [93213], []⟩,
        ⟨77990, false, false, [], []⟩
      ]⟩,
    ⟨[93217], [93215, 9], .source 46673⟩,
    ⟨[93215], [93215], .contexts []⟩,
    ⟨[93217, 9], [93215], .contexts [
        ⟨77992, false, false, [], [9]⟩,
        ⟨46, false, false, [93215], []⟩,
        ⟨77993, false, false, [], []⟩
      ]⟩,
    ⟨[93219], [93217, 11], .source 46674⟩,
    ⟨[93217], [93217], .contexts []⟩,
    ⟨[93219, 11], [93217], .contexts [
        ⟨77995, false, false, [], [11]⟩,
        ⟨53, false, false, [93217], []⟩,
        ⟨77996, false, false, [], []⟩
      ]⟩,
    ⟨[93221], [93219, 1], .source 46675⟩,
    ⟨[93219], [93219], .contexts []⟩,
    ⟨[93221, 1], [93219], .contexts [
        ⟨77998, false, false, [], [1]⟩,
        ⟨8, false, false, [93219], []⟩,
        ⟨77999, false, false, [], []⟩
      ]⟩,
    ⟨[93223], [93221, 13], .source 46676⟩,
    ⟨[93221], [93221], .contexts []⟩,
    ⟨[93223, 13], [93221], .contexts [
        ⟨78001, false, false, [], [13]⟩,
        ⟨59, false, false, [93221], []⟩,
        ⟨78002, false, false, [], []⟩
      ]⟩,
    ⟨[93225], [93223, 15], .source 46677⟩,
    ⟨[93223], [93223], .contexts []⟩,
    ⟨[93225, 15], [93223], .contexts [
        ⟨78004, false, false, [], [15]⟩,
        ⟨1, false, false, [93223], []⟩,
        ⟨78005, false, false, [], []⟩
      ]⟩,
    ⟨[93227], [93225, 1], .source 46678⟩,
    ⟨[93225], [93225], .contexts []⟩,
    ⟨[93227, 1], [93225], .contexts [
        ⟨78007, false, false, [], [1]⟩,
        ⟨8, false, false, [93225], []⟩,
        ⟨78008, false, false, [], []⟩
      ]⟩,
    ⟨[93229], [93227, 3], .source 46679⟩,
    ⟨[93227], [93227], .contexts []⟩,
    ⟨[93229, 3], [93227], .contexts [
        ⟨78010, false, false, [], [3]⟩,
        ⟨20, false, false, [93227], []⟩,
        ⟨78011, false, false, [], []⟩
      ]⟩,
    ⟨[93231], [93229, 5], .source 46680⟩,
    ⟨[93229], [93229], .contexts []⟩,
    ⟨[93231, 5], [93229], .contexts [
        ⟨78013, false, false, [], [5]⟩,
        ⟨28, false, false, [93229], []⟩,
        ⟨78014, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1219. -/
def y322TCIndexRaw1219 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93233], [93231, 1], .source 46681⟩,
    ⟨[93231], [93231], .contexts []⟩,
    ⟨[93233, 1], [93231], .contexts [
        ⟨78016, false, false, [], [1]⟩,
        ⟨8, false, false, [93231], []⟩,
        ⟨78017, false, false, [], []⟩
      ]⟩,
    ⟨[93235], [93233, 9], .source 46682⟩,
    ⟨[93233], [93233], .contexts []⟩,
    ⟨[93235, 9], [93233], .contexts [
        ⟨78019, false, false, [], [9]⟩,
        ⟨46, false, false, [93233], []⟩,
        ⟨78020, false, false, [], []⟩
      ]⟩,
    ⟨[93237], [93235, 11], .source 46683⟩,
    ⟨[93235], [93235], .contexts []⟩,
    ⟨[93237, 11], [93235], .contexts [
        ⟨78022, false, false, [], [11]⟩,
        ⟨53, false, false, [93235], []⟩,
        ⟨78023, false, false, [], []⟩
      ]⟩,
    ⟨[93239], [93237, 1], .source 46684⟩,
    ⟨[93237], [93237], .contexts []⟩,
    ⟨[93239, 1], [93237], .contexts [
        ⟨78025, false, false, [], [1]⟩,
        ⟨8, false, false, [93237], []⟩,
        ⟨78026, false, false, [], []⟩
      ]⟩,
    ⟨[93241], [93239, 13], .source 46685⟩,
    ⟨[93239], [93239], .contexts []⟩,
    ⟨[93241, 13], [93239], .contexts [
        ⟨78028, false, false, [], [13]⟩,
        ⟨59, false, false, [93239], []⟩,
        ⟨78029, false, false, [], []⟩
      ]⟩,
    ⟨[93243], [93241, 15], .source 46686⟩,
    ⟨[93241], [93241], .contexts []⟩,
    ⟨[93243, 15], [93241], .contexts [
        ⟨78031, false, false, [], [15]⟩,
        ⟨1, false, false, [93241], []⟩,
        ⟨78032, false, false, [], []⟩
      ]⟩,
    ⟨[93245], [93243, 1], .source 46687⟩,
    ⟨[93243], [93243], .contexts []⟩,
    ⟨[93245, 1], [93243], .contexts [
        ⟨78034, false, false, [], [1]⟩,
        ⟨8, false, false, [93243], []⟩,
        ⟨78035, false, false, [], []⟩
      ]⟩,
    ⟨[93247], [93245, 3], .source 46688⟩,
    ⟨[93245], [93245], .contexts []⟩,
    ⟨[93247, 3], [93245], .contexts [
        ⟨78037, false, false, [], [3]⟩,
        ⟨20, false, false, [93245], []⟩,
        ⟨78038, false, false, [], []⟩
      ]⟩,
    ⟨[93249], [93247, 5], .source 46689⟩,
    ⟨[93247], [93247], .contexts []⟩,
    ⟨[93249, 5], [93247], .contexts [
        ⟨78040, false, false, [], [5]⟩,
        ⟨28, false, false, [93247], []⟩,
        ⟨78041, false, false, [], []⟩
      ]⟩,
    ⟨[93251], [93249, 1], .source 46690⟩,
    ⟨[93249, 1], [93251], .contexts [
        ⟨78043, true, false, [], []⟩
      ]⟩,
    ⟨[93249], [93249], .contexts []⟩,
    ⟨[93251, 1], [93249], .contexts [
        ⟨78044, true, false, [], [1]⟩,
        ⟨8, false, false, [93249], []⟩,
        ⟨78045, false, false, [], []⟩
      ]⟩,
    ⟨[93253], [93251, 9], .source 46691⟩,
    ⟨[93251, 9], [93253], .contexts [
        ⟨78047, true, false, [], []⟩
      ]⟩,
    ⟨[93251], [93251], .contexts []⟩,
    ⟨[93253, 9], [93251], .contexts [
        ⟨78048, true, false, [], [9]⟩,
        ⟨46, false, false, [93251], []⟩,
        ⟨78049, false, false, [], []⟩
      ]⟩,
    ⟨[93255], [93253, 11], .source 46692⟩,
    ⟨[93253], [93253], .contexts []⟩,
    ⟨[93255, 11], [93253], .contexts [
        ⟨78051, false, false, [], [11]⟩,
        ⟨53, false, false, [93253], []⟩,
        ⟨78052, false, false, [], []⟩
      ]⟩,
    ⟨[93257], [93255, 1], .source 46693⟩,
    ⟨[93255], [93255], .contexts []⟩,
    ⟨[93257, 1], [93255], .contexts [
        ⟨78054, false, false, [], [1]⟩,
        ⟨8, false, false, [93255], []⟩,
        ⟨78055, false, false, [], []⟩
      ]⟩,
    ⟨[93259], [93257, 13], .source 46694⟩,
    ⟨[93257], [93257], .contexts []⟩,
    ⟨[93259, 13], [93257], .contexts [
        ⟨78057, false, false, [], [13]⟩,
        ⟨59, false, false, [93257], []⟩,
        ⟨78058, false, false, [], []⟩
      ]⟩,
    ⟨[93261], [93259, 15], .source 46695⟩,
    ⟨[93259], [93259], .contexts []⟩,
    ⟨[93261, 15], [93259], .contexts [
        ⟨78060, false, false, [], [15]⟩,
        ⟨1, false, false, [93259], []⟩,
        ⟨78061, false, false, [], []⟩
      ]⟩,
    ⟨[93263], [93261, 1], .source 46696⟩,
    ⟨[93261], [93261], .contexts []⟩,
    ⟨[93263, 1], [93261], .contexts [
        ⟨78063, false, false, [], [1]⟩,
        ⟨8, false, false, [93261], []⟩,
        ⟨78064, false, false, [], []⟩
      ]⟩,
    ⟨[93265], [93263, 3], .source 46697⟩,
    ⟨[93263], [93263], .contexts []⟩,
    ⟨[93265, 3], [93263], .contexts [
        ⟨78066, false, false, [], [3]⟩,
        ⟨20, false, false, [93263], []⟩,
        ⟨78067, false, false, [], []⟩
      ]⟩,
    ⟨[93267], [93265, 5], .source 46698⟩,
    ⟨[93265, 5], [93267], .contexts [
        ⟨78069, true, false, [], []⟩
      ]⟩,
    ⟨[93265], [93265], .contexts []⟩,
    ⟨[93267, 5], [93265], .contexts [
        ⟨78070, true, false, [], [5]⟩,
        ⟨28, false, false, [93265], []⟩,
        ⟨78071, false, false, [], []⟩
      ]⟩,
    ⟨[93269], [93267, 1], .source 46699⟩,
    ⟨[93267, 1], [93269], .contexts [
        ⟨78073, true, false, [], []⟩
      ]⟩,
    ⟨[93267], [93267], .contexts []⟩,
    ⟨[93269, 1], [93267], .contexts [
        ⟨78074, true, false, [], [1]⟩,
        ⟨8, false, false, [93267], []⟩,
        ⟨78075, false, false, [], []⟩
      ]⟩,
    ⟨[93271], [93269, 9], .source 46700⟩,
    ⟨[93269], [93269], .contexts []⟩,
    ⟨[93271, 9], [93269], .contexts [
        ⟨78077, false, false, [], [9]⟩,
        ⟨46, false, false, [93269], []⟩,
        ⟨78078, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1220. -/
def y322TCIndexRaw1220 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93273], [93271, 11], .source 46701⟩,
    ⟨[93271], [93271], .contexts []⟩,
    ⟨[93273, 11], [93271], .contexts [
        ⟨78080, false, false, [], [11]⟩,
        ⟨53, false, false, [93271], []⟩,
        ⟨78081, false, false, [], []⟩
      ]⟩,
    ⟨[93275], [93273, 1], .source 46702⟩,
    ⟨[93273], [93273], .contexts []⟩,
    ⟨[93275, 1], [93273], .contexts [
        ⟨78083, false, false, [], [1]⟩,
        ⟨8, false, false, [93273], []⟩,
        ⟨78084, false, false, [], []⟩
      ]⟩,
    ⟨[93277], [93275, 13], .source 46703⟩,
    ⟨[93275], [93275], .contexts []⟩,
    ⟨[93277, 13], [93275], .contexts [
        ⟨78086, false, false, [], [13]⟩,
        ⟨59, false, false, [93275], []⟩,
        ⟨78087, false, false, [], []⟩
      ]⟩,
    ⟨[93279], [93277, 15], .source 46704⟩,
    ⟨[93277, 15], [93279], .contexts [
        ⟨78089, true, false, [], []⟩
      ]⟩,
    ⟨[93277], [93277], .contexts []⟩,
    ⟨[93279, 15], [93277], .contexts [
        ⟨78090, true, false, [], [15]⟩,
        ⟨1, false, false, [93277], []⟩,
        ⟨78091, false, false, [], []⟩
      ]⟩,
    ⟨[93281], [93279, 1], .source 46705⟩,
    ⟨[93279, 1], [93281], .contexts [
        ⟨78093, true, false, [], []⟩
      ]⟩,
    ⟨[93279], [93279], .contexts []⟩,
    ⟨[93281, 1], [93279], .contexts [
        ⟨78094, true, false, [], [1]⟩,
        ⟨8, false, false, [93279], []⟩,
        ⟨78095, false, false, [], []⟩
      ]⟩,
    ⟨[93281], [93281], .contexts []⟩,
    ⟨[93281], [93281], .contexts []⟩,
    ⟨[93273], [93273], .contexts []⟩,
    ⟨[93271], [93271], .contexts []⟩,
    ⟨[93269], [93269], .contexts []⟩,
    ⟨[93279, 15, 13, 1, 11, 9], [93269], .contexts [
        ⟨78092, false, false, [], [13, 1, 11, 9]⟩,
        ⟨78091, false, false, [], [13, 1, 11, 9]⟩,
        ⟨78091, false, false, [], [13, 1, 11, 9]⟩,
        ⟨78088, false, false, [], [1, 11, 9]⟩,
        ⟨78087, false, false, [], [1, 11, 9]⟩,
        ⟨78087, false, false, [], [1, 11, 9]⟩,
        ⟨78085, false, false, [], [11, 9]⟩,
        ⟨78099, false, false, [], [11, 9]⟩,
        ⟨78084, false, false, [], [11, 9]⟩,
        ⟨78084, false, false, [], [11, 9]⟩,
        ⟨78082, false, false, [], [9]⟩,
        ⟨78100, false, false, [], [9]⟩,
        ⟨78081, false, false, [], [9]⟩,
        ⟨78081, false, false, [], [9]⟩,
        ⟨78079, false, false, [], []⟩,
        ⟨78101, false, false, [], []⟩,
        ⟨78078, false, false, [], []⟩,
        ⟨78078, false, false, [], []⟩
      ]⟩,
    ⟨[93269, 1], [93267], .contexts [
        ⟨78076, false, false, [], []⟩
      ]⟩,
    ⟨[93267], [93267], .contexts []⟩,
    ⟨[93265, 3], [93263], .contexts [
        ⟨78068, false, false, [], []⟩
      ]⟩,
    ⟨[93263], [93263], .contexts []⟩,
    ⟨[93263, 1], [93261], .contexts [
        ⟨78065, false, false, [], []⟩
      ]⟩,
    ⟨[93261], [93261], .contexts []⟩,
    ⟨[93261, 15], [93259], .contexts [
        ⟨78062, false, false, [], []⟩
      ]⟩,
    ⟨[93259], [93259], .contexts []⟩,
    ⟨[93279, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15], [93259], .contexts [
        ⟨78102, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨78103, false, false, [], [5, 3, 1, 15]⟩,
        ⟨78104, false, false, [], [5, 3, 1, 15]⟩,
        ⟨78075, false, false, [], [5, 3, 1, 15]⟩,
        ⟨78075, false, false, [], [5, 3, 1, 15]⟩,
        ⟨78072, false, false, [], [3, 1, 15]⟩,
        ⟨78071, false, false, [], [3, 1, 15]⟩,
        ⟨78071, false, false, [], [3, 1, 15]⟩,
        ⟨78105, false, false, [], [1, 15]⟩,
        ⟨78106, false, false, [], [1, 15]⟩,
        ⟨78067, false, false, [], [1, 15]⟩,
        ⟨78067, false, false, [], [1, 15]⟩,
        ⟨78107, false, false, [], [15]⟩,
        ⟨78108, false, false, [], [15]⟩,
        ⟨78064, false, false, [], [15]⟩,
        ⟨78064, false, false, [], [15]⟩,
        ⟨78109, false, false, [], []⟩,
        ⟨78110, false, false, [], []⟩,
        ⟨78061, false, false, [], []⟩,
        ⟨78061, false, false, [], []⟩
      ]⟩,
    ⟨[93259, 13], [93257], .contexts [
        ⟨78059, false, false, [], []⟩
      ]⟩,
    ⟨[93257], [93257], .contexts []⟩,
    ⟨[93257, 1], [93255], .contexts [
        ⟨78056, false, false, [], []⟩
      ]⟩,
    ⟨[93255], [93255], .contexts []⟩,
    ⟨[93255, 11], [93253], .contexts [
        ⟨78053, false, false, [], []⟩
      ]⟩,
    ⟨[93253], [93253], .contexts []⟩,
    ⟨[93253, 9], [93251], .contexts [
        ⟨78050, false, false, [], []⟩
      ]⟩,
    ⟨[93251], [93251], .contexts []⟩,
    ⟨[93251, 1], [93249], .contexts [
        ⟨78046, false, false, [], []⟩
      ]⟩,
    ⟨[93249], [93249], .contexts []⟩,
    ⟨[
      93279, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1
    ], [93249], .contexts [
        ⟨78111, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨78112, false, false, [], [1, 11, 9, 1]⟩,
        ⟨78113, false, false, [], [1, 11, 9, 1]⟩,
        ⟨78058, false, false, [], [1, 11, 9, 1]⟩,
        ⟨78058, false, false, [], [1, 11, 9, 1]⟩,
        ⟨78114, false, false, [], [11, 9, 1]⟩,
        ⟨78115, false, false, [], [11, 9, 1]⟩,
        ⟨78055, false, false, [], [11, 9, 1]⟩,
        ⟨78055, false, false, [], [11, 9, 1]⟩,
        ⟨78116, false, false, [], [9, 1]⟩,
        ⟨78117, false, false, [], [9, 1]⟩,
        ⟨78052, false, false, [], [9, 1]⟩,
        ⟨78052, false, false, [], [9, 1]⟩,
        ⟨78118, false, false, [], [1]⟩,
        ⟨78119, false, false, [], [1]⟩,
        ⟨78049, false, false, [], [1]⟩,
        ⟨78049, false, false, [], [1]⟩,
        ⟨78120, false, false, [], []⟩,
        ⟨78121, false, false, [], []⟩,
        ⟨78045, false, false, [], []⟩,
        ⟨78045, false, false, [], []⟩
      ]⟩,
    ⟨[93249, 5], [93247], .contexts [
        ⟨78042, false, false, [], []⟩
      ]⟩,
    ⟨[93247], [93247], .contexts []⟩,
    ⟨[93247, 3], [93245], .contexts [
        ⟨78039, false, false, [], []⟩
      ]⟩,
    ⟨[93245], [93245], .contexts []⟩,
    ⟨[93245, 1], [93243], .contexts [
        ⟨78036, false, false, [], []⟩
      ]⟩,
    ⟨[93243], [93243], .contexts []⟩,
    ⟨[93239], [93239], .contexts []⟩,
    ⟨[
      93279, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [93239], .contexts [
        ⟨78122, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨78123, false, false, [], [3, 1, 15, 13]⟩,
        ⟨78124, false, false, [], [3, 1, 15, 13]⟩,
        ⟨78041, false, false, [], [3, 1, 15, 13]⟩,
        ⟨78041, false, false, [], [3, 1, 15, 13]⟩,
        ⟨78125, false, false, [], [1, 15, 13]⟩,
        ⟨78126, false, false, [], [1, 15, 13]⟩,
        ⟨78038, false, false, [], [1, 15, 13]⟩,
        ⟨78038, false, false, [], [1, 15, 13]⟩,
        ⟨78127, false, false, [], [15, 13]⟩,
        ⟨78128, false, false, [], [15, 13]⟩,
        ⟨78035, false, false, [], [15, 13]⟩,
        ⟨78035, false, false, [], [15, 13]⟩,
        ⟨78033, false, false, [], [13]⟩,
        ⟨78032, false, false, [], [13]⟩,
        ⟨78032, false, false, [], [13]⟩,
        ⟨78030, false, false, [], []⟩,
        ⟨78129, false, false, [], []⟩,
        ⟨78029, false, false, [], []⟩,
        ⟨78029, false, false, [], []⟩
      ]⟩,
    ⟨[93237], [93237], .contexts []⟩,
    ⟨[93235], [93235], .contexts []⟩,
    ⟨[93233], [93233], .contexts []⟩,
    ⟨[93231], [93231], .contexts []⟩,
    ⟨[93229], [93229], .contexts []⟩,
    ⟨[
      93279, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5
    ], [93229], .contexts [
        ⟨78130, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨78027, false, false, [], [11, 9, 1, 5]⟩,
        ⟨78131, false, false, [], [11, 9, 1, 5]⟩,
        ⟨78026, false, false, [], [11, 9, 1, 5]⟩,
        ⟨78026, false, false, [], [11, 9, 1, 5]⟩,
        ⟨78024, false, false, [], [9, 1, 5]⟩,
        ⟨78132, false, false, [], [9, 1, 5]⟩,
        ⟨78023, false, false, [], [9, 1, 5]⟩,
        ⟨78023, false, false, [], [9, 1, 5]⟩,
        ⟨78021, false, false, [], [1, 5]⟩,
        ⟨78133, false, false, [], [1, 5]⟩,
        ⟨78020, false, false, [], [1, 5]⟩,
        ⟨78020, false, false, [], [1, 5]⟩,
        ⟨78018, false, false, [], [5]⟩,
        ⟨78134, false, false, [], [5]⟩,
        ⟨78017, false, false, [], [5]⟩,
        ⟨78017, false, false, [], [5]⟩,
        ⟨78015, false, false, [], []⟩,
        ⟨78135, false, false, [], []⟩,
        ⟨78014, false, false, [], []⟩,
        ⟨78014, false, false, [], []⟩
      ]⟩,
    ⟨[93227], [93227], .contexts []⟩,
    ⟨[93225], [93225], .contexts []⟩,
    ⟨[93223], [93223], .contexts []⟩,
    ⟨[93221], [93221], .contexts []⟩,
    ⟨[93219], [93219], .contexts []⟩,
    ⟨[
      93279, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1
    ], [93219], .contexts [
        ⟨78136, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨78012, false, false, [], [1, 15, 13, 1]⟩,
        ⟨78137, false, false, [], [1, 15, 13, 1]⟩,
        ⟨78011, false, false, [], [1, 15, 13, 1]⟩,
        ⟨78011, false, false, [], [1, 15, 13, 1]⟩,
        ⟨78009, false, false, [], [15, 13, 1]⟩,
        ⟨78138, false, false, [], [15, 13, 1]⟩,
        ⟨78008, false, false, [], [15, 13, 1]⟩,
        ⟨78008, false, false, [], [15, 13, 1]⟩,
        ⟨78006, false, false, [], [13, 1]⟩,
        ⟨78139, false, false, [], [13, 1]⟩,
        ⟨78005, false, false, [], [13, 1]⟩,
        ⟨78005, false, false, [], [13, 1]⟩,
        ⟨78003, false, false, [], [1]⟩,
        ⟨78140, false, false, [], [1]⟩,
        ⟨78002, false, false, [], [1]⟩,
        ⟨78002, false, false, [], [1]⟩,
        ⟨78000, false, false, [], []⟩,
        ⟨78141, false, false, [], []⟩,
        ⟨77999, false, false, [], []⟩,
        ⟨77999, false, false, [], []⟩
      ]⟩,
    ⟨[93217], [93217], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1221. -/
def y322TCIndexRaw1221 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93215], [93215], .contexts []⟩,
    ⟨[93213], [93213], .contexts []⟩,
    ⟨[
      93279, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [93209], .contexts [
        ⟨78142, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨77997, false, false, [], [9, 1, 5, 3]⟩,
        ⟨78143, false, false, [], [9, 1, 5, 3]⟩,
        ⟨77996, false, false, [], [9, 1, 5, 3]⟩,
        ⟨77996, false, false, [], [9, 1, 5, 3]⟩,
        ⟨77994, false, false, [], [1, 5, 3]⟩,
        ⟨78144, false, false, [], [1, 5, 3]⟩,
        ⟨77993, false, false, [], [1, 5, 3]⟩,
        ⟨77993, false, false, [], [1, 5, 3]⟩,
        ⟨77991, false, false, [], [5, 3]⟩,
        ⟨78145, false, false, [], [5, 3]⟩,
        ⟨77990, false, false, [], [5, 3]⟩,
        ⟨77990, false, false, [], [5, 3]⟩,
        ⟨77988, false, false, [], [3]⟩,
        ⟨77985, false, false, [], [3]⟩,
        ⟨77986, false, false, [], [3]⟩,
        ⟨77986, false, false, [], [3]⟩,
        ⟨77984, false, false, [], []⟩,
        ⟨77981, false, false, [], []⟩,
        ⟨77982, false, false, [], []⟩,
        ⟨77982, false, false, [], []⟩
      ]⟩,
    ⟨[93203, 1], [93201], .contexts [
        ⟨77963, false, false, [], []⟩
      ]⟩,
    ⟨[
      93279, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11
    ], [93199], .contexts [
        ⟨78146, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨77980, false, false, [], [15, 13, 1, 11]⟩,
        ⟨77977, false, false, [], [15, 13, 1, 11]⟩,
        ⟨77978, false, false, [], [15, 13, 1, 11]⟩,
        ⟨77978, false, false, [], [15, 13, 1, 11]⟩,
        ⟨77976, false, false, [], [13, 1, 11]⟩,
        ⟨77973, false, false, [], [13, 1, 11]⟩,
        ⟨77974, false, false, [], [13, 1, 11]⟩,
        ⟨77974, false, false, [], [13, 1, 11]⟩,
        ⟨77972, false, false, [], [1, 11]⟩,
        ⟨77964, false, false, [], [1, 11]⟩,
        ⟨77965, false, false, [], [1, 11]⟩,
        ⟨77965, false, false, [], [1, 11]⟩,
        ⟨78147, false, false, [], [11]⟩,
        ⟨77955, false, false, [], [11]⟩,
        ⟨77956, false, false, [], [11]⟩,
        ⟨77956, false, false, [], [11]⟩,
        ⟨77954, true, false, [], [11]⟩,
        ⟨53, false, false, [93199], []⟩,
        ⟨77948, false, false, [], []⟩,
        ⟨77947, false, false, [], []⟩,
        ⟨77948, false, false, [], []⟩,
        ⟨77948, false, false, [], []⟩
      ]⟩,
    ⟨[
      93279, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [93191], .contexts [
        ⟨78148, false, false, [], [9, 1, 5, 3]⟩,
        ⟨77946, true, false, [], [9, 1, 5, 3]⟩,
        ⟨46, false, false, [93197], [1, 5, 3]⟩,
        ⟨77941, false, false, [], [1, 5, 3]⟩,
        ⟨77940, false, false, [], [1, 5, 3]⟩,
        ⟨77941, false, false, [], [1, 5, 3]⟩,
        ⟨77941, false, false, [], [1, 5, 3]⟩,
        ⟨77939, true, false, [], [1, 5, 3]⟩,
        ⟨8, false, false, [93195], [5, 3]⟩,
        ⟨77926, false, false, [], [5, 3]⟩,
        ⟨77925, false, false, [], [5, 3]⟩,
        ⟨77926, false, false, [], [5, 3]⟩,
        ⟨77926, false, false, [], [5, 3]⟩,
        ⟨77924, true, false, [], [5, 3]⟩,
        ⟨28, false, false, [93193], [3]⟩,
        ⟨77915, false, false, [], [3]⟩,
        ⟨77914, false, false, [], [3]⟩,
        ⟨77915, false, false, [], [3]⟩,
        ⟨77915, false, false, [], [3]⟩,
        ⟨77913, false, false, [], []⟩,
        ⟨77897, false, false, [], []⟩,
        ⟨77898, false, false, [], []⟩,
        ⟨77898, false, false, [], []⟩
      ]⟩,
    ⟨[93189, 15], [93187], .contexts [
        ⟨77872, false, false, [], []⟩
      ]⟩,
    ⟨[
      93279, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11
    ], [90467], .contexts [
        ⟨78149, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨77895, false, false, [], [15, 13, 1, 11]⟩,
        ⟨77873, false, false, [], [15, 13, 1, 11]⟩,
        ⟨77874, false, false, [], [15, 13, 1, 11]⟩,
        ⟨77874, false, false, [], [15, 13, 1, 11]⟩,
        ⟨78150, false, false, [], [13, 1, 11]⟩,
        ⟨77849, false, false, [], [13, 1, 11]⟩,
        ⟨77850, false, false, [], [13, 1, 11]⟩,
        ⟨77850, false, false, [], [13, 1, 11]⟩,
        ⟨77887, false, false, [], [1, 11]⟩,
        ⟨77830, false, false, [], [1, 11]⟩,
        ⟨77831, false, false, [], [1, 11]⟩,
        ⟨77831, false, false, [], [1, 11]⟩,
        ⟨77829, false, false, [], [11]⟩,
        ⟨77810, false, false, [], [11]⟩,
        ⟨77811, false, false, [], [11]⟩,
        ⟨77811, false, false, [], [11]⟩,
        ⟨77838, false, false, [], []⟩,
        ⟨60722, false, false, [], []⟩,
        ⟨60689, false, false, [], []⟩,
        ⟨60689, false, false, [], []⟩
      ]⟩,
    ⟨[90469, 1], [25033, 90473], .contexts [
        ⟨60957, false, false, [], []⟩
      ]⟩,
    ⟨[29721], [25033, 25007], .source 14925⟩,
    ⟨[29723], [25939, 25955], .source 14926⟩,
    ⟨[29725], [29721, 29723], .source 14927⟩,
    ⟨[29727], [29725, 25961], .source 14928⟩,
    ⟨[
      93279, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1
    ], [29727, 91247], .contexts [
        ⟨78151, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨77819, false, false, [], [1, 5, 3, 1]⟩,
        ⟨60720, false, false, [], [1, 5, 3, 1]⟩,
        ⟨60693, false, false, [], [1, 5, 3, 1]⟩,
        ⟨60693, false, false, [], [1, 5, 3, 1]⟩,
        ⟨78152, false, false, [], [5, 3, 1]⟩,
        ⟨60931, false, false, [], [5, 3, 1]⟩,
        ⟨60932, false, false, [], [5, 3, 1]⟩,
        ⟨60932, false, false, [], [5, 3, 1]⟩,
        ⟨60945, false, false, [25033], [3, 1]⟩,
        ⟨78153, true, false, [], [90473, 3, 1]⟩,
        ⟨64939, false, false, [29721], [1]⟩,
        ⟨64963, false, false, [29721, 25939], [1]⟩,
        ⟨78154, true, false, [29721], [91247, 1]⟩,
        ⟨78155, true, false, [], [91247, 1]⟩,
        ⟨64961, false, false, [29725], []⟩,
        ⟨78156, true, false, [], [91247]⟩
      ]⟩,
    ⟨[29729], [29727, 25965], .source 14929⟩,
    ⟨[29731], [29729, 25953], .source 14930⟩,
    ⟨[29733], [29731, 25911], .source 14931⟩,
    ⟨[29735], [29733, 2241], .source 14932⟩,
    ⟨[
      93279, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [29735, 82877], .contexts [
        ⟨78157, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨64966, false, false, [29727], [13, 1, 11, 9]⟩,
        ⟨78158, true, false, [], [91247, 13, 1, 11, 9]⟩,
        ⟨64953, false, false, [29729], [1, 11, 9]⟩,
        ⟨78159, true, false, [], [91253, 1, 11, 9]⟩,
        ⟨64901, false, false, [29731], [11, 9]⟩,
        ⟨78160, true, false, [], [87941, 11, 9]⟩,
        ⟨47421, false, false, [29733], [9]⟩,
        ⟨78161, true, false, [], [87941, 9]⟩,
        ⟨47418, false, false, [29735], []⟩
      ]⟩,
    ⟨[29737], [29735, 17755], .source 14933⟩,
    ⟨[
      93279, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15
    ], [29737, 86571], .contexts [
        ⟨78162, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨17804, false, false, [29735], [5, 3, 1, 15]⟩,
        ⟨44191, false, false, [29735], [3, 1, 15]⟩,
        ⟨44212, false, false, [29735], [1, 15]⟩,
        ⟨44219, false, false, [29735], [15]⟩,
        ⟨37991, false, false, [29735], []⟩,
        ⟨78163, true, false, [], [86571]⟩
      ]⟩,
    ⟨[29739], [29737, 20313], .source 14934⟩,
    ⟨[29741], [29739, 20317], .source 14935⟩,
    ⟨[29743], [29741, 16661], .source 14936⟩,
    ⟨[29745], [29743, 17777], .source 14937⟩,
    ⟨[
      93279, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [29745, 84963], .contexts [
        ⟨78164, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨37946, false, false, [29737], [1, 11, 9, 1]⟩,
        ⟨41830, false, false, [29737], [1, 11, 9, 1]⟩,
        ⟨78165, true, false, [], [83641, 1, 11, 9, 1]⟩,
        ⟨22206, false, false, [29739], [11, 9, 1]⟩,
        ⟨41819, false, false, [29739], [9, 1]⟩,
        ⟨78166, true, false, [], [82977, 9, 1]⟩,
        ⟨23606, false, false, [29741], [1]⟩,
        ⟨78167, true, false, [], [82977, 1]⟩,
        ⟨29452, false, false, [29743], []⟩,
        ⟨78168, true, false, [], [84963]⟩
      ]⟩,
    ⟨[29747], [29745, 17759], .source 14938⟩,
    ⟨[29749], [29747, 16489], .source 14939⟩,
    ⟨[29751], [29749, 15349], .source 14940⟩,
    ⟨[29753], [29751, 15643], .source 14941⟩,
    ⟨[29755], [29753, 15157], .source 14942⟩,
    ⟨[
      93279, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13
    ], [29755, 80791], .contexts [
        ⟨78169, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨29412, false, false, [29745], [3, 1, 15, 13]⟩,
        ⟨78170, true, false, [], [83669, 3, 1, 15, 13]⟩,
        ⟨22537, false, false, [29747], [1, 15, 13]⟩,
        ⟨78171, true, false, [], [82769, 1, 15, 13]⟩,
        ⟨16410, false, false, [29749], [15, 13]⟩,
        ⟨78172, true, false, [], [82769, 15, 13]⟩,
        ⟨17519, false, false, [29751], [13]⟩,
        ⟨78173, true, false, [], [82851, 13]⟩,
        ⟨17511, false, false, [29753], []⟩,
        ⟨78174, true, false, [], [80791]⟩
      ]⟩,
    ⟨[29757], [29755, 3153], .source 14943⟩,
    ⟨[29759], [29757, 8295], .source 14944⟩,
    ⟨[29761], [29759, 2007], .source 14945⟩,
    ⟨[
      93279, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5
    ], [29761, 79921], .contexts [
        ⟨78175, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨8392, false, false, [29755], [11, 9, 1, 5]⟩,
        ⟨78176, true, false, [], [80981, 11, 9, 1, 5]⟩,
        ⟨14837, false, false, [29757], [9, 1, 5]⟩,
        ⟨78177, true, false, [], [79915, 9, 1, 5]⟩,
        ⟨31632, false, false, [29759], [1, 5]⟩,
        ⟨31629, false, false, [29759], [5]⟩,
        ⟨78178, true, false, [], [85345, 5]⟩,
        ⟨31621, false, false, [29761], []⟩
      ]⟩,
    ⟨[29763], [29761, 7829], .source 14946⟩,
    ⟨[29765], [29763, 2007], .source 14947⟩,
    ⟨[29767], [29765, 15141], .source 14948⟩,
    ⟨[29769], [29767, 17061], .source 14949⟩,
    ⟨[29771], [29769, 14161], .source 14950⟩,
    ⟨[
      93279, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1
    ], [29771, 83191], .contexts [
        ⟨78179, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨7679, false, false, [29761], [1, 15, 13, 1]⟩,
        ⟨11233, false, false, [29761], [1, 15, 13, 1]⟩,
        ⟨78180, true, false, [], [79921, 1, 15, 13, 1]⟩,
        ⟨7543, false, false, [29763], [15, 13, 1]⟩,
        ⟨78181, true, false, [], [79921, 15, 13, 1]⟩,
        ⟨14828, false, false, [29765], [13, 1]⟩,
        ⟨78182, true, false, [], [82319, 13, 1]⟩,
        ⟨26220, false, false, [29767], [1]⟩,
        ⟨78183, true, false, [], [84355, 1]⟩,
        ⟨26199, false, false, [29769], []⟩,
        ⟨78184, true, false, [], [83191]⟩
      ]⟩,
    ⟨[29773], [29771, 16023], .source 14951⟩,
    ⟨[29773, 83173], [29773, 83173], .contexts []⟩,
    ⟨[29773, 83173], [29773, 83173], .contexts []⟩,
    ⟨[29773, 83173], [29773, 83173], .contexts []⟩,
    ⟨[29773, 83175], [29773, 83175], .contexts []⟩,
    ⟨[29773, 83175], [29773, 83175], .contexts []⟩,
    ⟨[93281, 3], [93281, 3], .contexts []⟩,
    ⟨[93281, 3], [29773, 83175], .contexts [
        ⟨78192, false, false, [], []⟩,
        ⟨78098, true, false, [], [3]⟩,
        ⟨78098, true, false, [], [3]⟩,
        ⟨78097, true, false, [], [3]⟩,
        ⟨78094, true, false, [], [3]⟩,
        ⟨1908, false, false, [93279], []⟩,
        ⟨1909, false, false, [93279], []⟩,
        ⟨78185, false, false, [], [11, 9, 1, 5]⟩,
        ⟨19763, false, false, [29771], [9, 1, 5]⟩,
        ⟨78186, true, false, [], [83191, 9, 1, 5]⟩,
        ⟨19741, false, false, [29773], [1, 5]⟩,
        ⟨19599, false, false, [29773], [5]⟩,
        ⟨78187, false, false, [], [5]⟩,
        ⟨78188, false, false, [], [5]⟩,
        ⟨78189, false, false, [], [5]⟩,
        ⟨19558, false, false, [29773], []⟩,
        ⟨78190, false, false, [], []⟩,
        ⟨78191, false, false, [], []⟩,
        ⟨19573, false, false, [29773], []⟩
      ]⟩,
    ⟨[93281, 3], [29773, 83175], .contexts [
        ⟨78193, false, false, [], []⟩,
        ⟨13, true, false, [], [29773, 83175]⟩
      ]⟩,
    ⟨[29775], [29772], .source 14952⟩,
    ⟨[83175, 3], [29775, 93281], .contexts [
        ⟨78194, true, false, [29772], [3]⟩,
        ⟨20, false, false, [29772, 93281], []⟩,
        ⟨78195, true, false, [], [93281]⟩
      ]⟩,
    ⟨[93281, 3], [29773, 83175], .contexts [
        ⟨78192, false, false, [], []⟩,
        ⟨78194, false, false, [], []⟩,
        ⟨78190, false, false, [], []⟩,
        ⟨78191, false, false, [], []⟩,
        ⟨78191, false, false, [], []⟩
      ]⟩,
    ⟨[29777], [29773, 17527], .source 14953⟩,
    ⟨[29779], [29777, 17539], .source 14954⟩,
    ⟨[93279, 3], [93279, 3], .contexts []⟩,
    ⟨[93279, 3], [29779, 84713], .contexts [
        ⟨78200, false, false, [], []⟩,
        ⟨78095, true, false, [], [3]⟩,
        ⟨78095, true, false, [], [3]⟩,
        ⟨78096, true, false, [], [3]⟩,
        ⟨1098, false, false, [93281], []⟩,
        ⟨1100, false, false, [93281], []⟩,
        ⟨78197, false, false, [], [1, 3, 1]⟩,
        ⟨19622, false, false, [29773], [3, 1]⟩,
        ⟨28275, false, false, [29773], [1]⟩,
        ⟨78198, true, false, [], [84717, 1]⟩,
        ⟨28155, false, false, [29777], []⟩,
        ⟨28308, false, false, [29777], []⟩,
        ⟨78199, true, false, [], [84713]⟩,
        ⟨28315, false, false, [29779], []⟩,
        ⟨13, true, false, [], [29779, 84713]⟩
      ]⟩,
    ⟨[29781], [29778], .source 14955⟩,
    ⟨[84713, 3], [29781, 93279], .contexts [
        ⟨78201, true, false, [29778], [3]⟩,
        ⟨20, false, false, [29778, 93279], []⟩,
        ⟨78202, true, false, [], [93279]⟩
      ]⟩,
    ⟨[29783], [29773, 15983], .source 14956⟩,
    ⟨[29785], [29783, 16221], .source 14957⟩,
    ⟨[93281], [93281], .contexts []⟩,
    ⟨[29785, 90615, 5], [93281], .contexts [
        ⟨78205, false, false, [], [90615, 5]⟩,
        ⟨62098, true, false, [29783], [5]⟩,
        ⟨19838, true, false, [29783], [3, 5]⟩,
        ⟨78204, false, false, [], [82819, 5, 3, 5]⟩,
        ⟨19533, true, false, [29773], [5, 3, 5]⟩,
        ⟨78189, true, false, [], [3, 5, 3, 5]⟩,
        ⟨78188, true, false, [], [3, 5, 3, 5]⟩,
        ⟨78187, true, false, [], [3, 5, 3, 5]⟩,
        ⟨19559, true, false, [29773], [3, 5, 3, 5]⟩,
        ⟨78197, true, false, [], [5, 3, 5, 3, 5]⟩,
        ⟨1919, false, false, [93281], []⟩,
        ⟨78206, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1222. -/
def y322TCIndexRaw1222 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93281], [93281], .contexts []⟩,
    ⟨[29787], [29784], .source 14958⟩,
    ⟨[29784], [29784], .contexts []⟩,
    ⟨[90615, 5], [29787, 93281], .contexts [
        ⟨78207, false, false, [29784], []⟩,
        ⟨78208, false, false, [29784], []⟩,
        ⟨78210, true, false, [], [93281]⟩,
        ⟨78210, true, false, [], [93281]⟩,
        ⟨78209, true, false, [], [93281]⟩
      ]⟩,
    ⟨[93281, 5], [29785, 90615], .contexts [
        ⟨78211, true, false, [29786], [5]⟩,
        ⟨28, false, false, [29786, 90615], []⟩,
        ⟨78209, false, true, [], [90615]⟩
      ]⟩,
    ⟨[29789], [29773, 15995], .source 14959⟩,
    ⟨[29791], [29789, 24781], .source 14960⟩,
    ⟨[90225, 9], [90225, 9], .contexts []⟩,
    ⟨[29793], [29790], .source 14961⟩,
    ⟨[29790], [29790], .contexts []⟩,
    ⟨[90225, 9], [29793, 93281], .contexts [
        ⟨78215, false, false, [], []⟩,
        ⟨78214, false, false, [29790], [90225, 9]⟩,
        ⟨59715, true, false, [29790, 29789], [9]⟩,
        ⟨78213, false, false, [29790], [83197, 3, 9]⟩,
        ⟨19832, true, false, [29790, 29773], [3, 9]⟩,
        ⟨78197, true, false, [29790], [9, 3, 9]⟩,
        ⟨1612, false, false, [29790, 93281], []⟩,
        ⟨78206, false, false, [29790], []⟩,
        ⟨78208, false, false, [29790], []⟩,
        ⟨78217, true, false, [], [93281]⟩,
        ⟨78217, true, false, [], [93281]⟩,
        ⟨78216, true, false, [], [93281]⟩
      ]⟩,
    ⟨[29795], [29773, 16373], .source 14962⟩,
    ⟨[29797], [29795, 23217], .source 14963⟩,
    ⟨[29799], [29796], .source 14964⟩,
    ⟨[29796], [29796], .contexts []⟩,
    ⟨[88707, 11], [29799, 93281], .contexts [
        ⟨78220, false, false, [29796], [88707, 11]⟩,
        ⟨52192, true, false, [29796, 29795], [11]⟩,
        ⟨78219, false, false, [29796], [83503, 3, 11]⟩,
        ⟨21689, true, false, [29796, 29773], [3, 11]⟩,
        ⟨78197, true, false, [29796], [11, 3, 11]⟩,
        ⟨1693, false, false, [29796, 93281], []⟩,
        ⟨78206, false, false, [29796], []⟩,
        ⟨78208, false, false, [29796], []⟩,
        ⟨78222, true, false, [], [93281]⟩,
        ⟨78222, true, false, [], [93281]⟩,
        ⟨78221, true, false, [], [93281]⟩
      ]⟩,
    ⟨[29801], [29773, 15991], .source 14965⟩,
    ⟨[29803], [29801, 21049], .source 14966⟩,
    ⟨[29805], [29802], .source 14967⟩,
    ⟨[29802], [29802], .contexts []⟩,
    ⟨[87567, 13], [29805, 93281], .contexts [
        ⟨78225, false, false, [29802], [87567, 13]⟩,
        ⟨44085, true, false, [29802, 29801], [13]⟩,
        ⟨78224, false, false, [29802], [83165, 3, 13]⟩,
        ⟨19569, true, false, [29802, 29773], [3, 13]⟩,
        ⟨78197, true, false, [29802], [13, 3, 13]⟩,
        ⟨1930, false, false, [29802, 93281], []⟩,
        ⟨78206, false, false, [29802], []⟩,
        ⟨78208, false, false, [29802], []⟩,
        ⟨78227, true, false, [], [93281]⟩,
        ⟨78227, true, false, [], [93281]⟩,
        ⟨78226, true, false, [], [93281]⟩
      ]⟩,
    ⟨[29807], [29773, 729], .source 14968⟩,
    ⟨[29809], [29807, 29775], .source 14969⟩,
    ⟨[29811], [29808], .source 14970⟩,
    ⟨[29808], [29808], .contexts []⟩,
    ⟨[29779, 84713], [29779, 84713], .contexts []⟩,
    ⟨[29779, 84713], [29779, 84713], .contexts []⟩,
    ⟨[93279, 3], [29779, 84713], .contexts [
        ⟨78200, false, false, [], []⟩,
        ⟨78201, false, false, [], []⟩,
        ⟨78233, false, false, [], []⟩,
        ⟨78234, false, false, [], []⟩,
        ⟨78234, false, false, [], []⟩
      ]⟩,
    ⟨[29813], [29779, 24713], .source 14971⟩,
    ⟨[29815], [29813, 24705], .source 14972⟩,
    ⟨[93279], [93279], .contexts []⟩,
    ⟨[93279], [93279], .contexts []⟩,
    ⟨[29817], [29814], .source 14973⟩,
    ⟨[29814], [29814], .contexts []⟩,
    ⟨[88703, 11], [29817, 93279], .contexts [
        ⟨78237, false, false, [29814], [88703, 11]⟩,
        ⟨59547, true, false, [29814, 29813], [11]⟩,
        ⟨78236, false, false, [29814], [90219, 3, 11]⟩,
        ⟨59558, true, false, [29814, 29779], [3, 11]⟩,
        ⟨78235, true, false, [29814], [11, 3, 11]⟩,
        ⟨1693, false, false, [29814, 93279], []⟩,
        ⟨78238, false, false, [29814], []⟩,
        ⟨78239, false, false, [29814], []⟩,
        ⟨78241, true, false, [], [93279]⟩,
        ⟨78241, true, false, [], [93279]⟩,
        ⟨78240, true, false, [], [93279]⟩
      ]⟩,
    ⟨[29819], [29779, 17543], .source 14974⟩,
    ⟨[29821], [29819, 24741], .source 14975⟩,
    ⟨[29823], [29820], .source 14976⟩,
    ⟨[29820], [29820], .contexts []⟩,
    ⟨[84477, 13], [29823, 93279], .contexts [
        ⟨78244, false, false, [29820], [84477, 13]⟩,
        ⟨59612, true, false, [29820, 29819], [13]⟩,
        ⟨78243, false, false, [29820], [84709, 3, 13]⟩,
        ⟨28327, true, false, [29820, 29779], [3, 13]⟩,
        ⟨28147, true, false, [29820, 29779], [3, 13]⟩,
        ⟨78235, true, false, [29820], [13, 3, 13]⟩,
        ⟨1930, false, false, [29820, 93279], []⟩,
        ⟨78238, false, false, [29820], []⟩,
        ⟨78239, false, false, [29820], []⟩,
        ⟨78246, true, false, [], [93279]⟩,
        ⟨78246, true, false, [], [93279]⟩,
        ⟨78245, true, false, [], [93279]⟩
      ]⟩,
    ⟨[29825], [29779, 17539], .source 14977⟩,
    ⟨[29827], [29825, 29781], .source 14978⟩,
    ⟨[29827, 93277], [29827, 93277], .contexts []⟩,
    ⟨[93279], [29827, 93277], .contexts [
        ⟨78239, false, false, [], []⟩,
        ⟨150, true, false, [93279], []⟩,
        ⟨78235, false, false, [], [15, 3, 15]⟩,
        ⟨28149, false, false, [29779], [3, 15]⟩,
        ⟨28308, false, false, [29779], [3, 15]⟩,
        ⟨78248, true, false, [], [84713, 3, 15]⟩,
        ⟨78203, false, false, [29825], [15]⟩,
        ⟨78249, true, false, [], [93279, 15]⟩,
        ⟨78092, false, false, [29827], []⟩,
        ⟨78250, false, false, [], []⟩
      ]⟩,
    ⟨[29829], [29826], .source 14979⟩,
    ⟨[29826], [29826], .contexts []⟩,
    ⟨[29831], [29829, 29779], .source 14980⟩,
    ⟨[29833], [29829, 29815], .source 14981⟩,
    ⟨[93279], [29827, 93277], .contexts [
        ⟨78251, false, false, [], []⟩
      ]⟩,
    ⟨[93279], [29827, 93277], .contexts [
        ⟨78256, false, false, [], []⟩,
        ⟨78250, false, false, [], []⟩
      ]⟩,
    ⟨[29835], [29829, 29821], .source 14982⟩,
    ⟨[93275], [29835, 84477], .contexts [
        ⟨78088, true, false, [], []⟩,
        ⟨78257, true, false, [29826], [13]⟩,
        ⟨78247, true, false, [29826, 29822], [13]⟩,
        ⟨59, false, false, [29826, 29822, 84477], []⟩,
        ⟨78245, false, true, [29826], [84477]⟩,
        ⟨78252, true, false, [], [29821, 84477]⟩,
        ⟨78258, true, false, [], [84477]⟩
      ]⟩,
    ⟨[29835, 84479], [29835, 84479], .contexts []⟩,
    ⟨[29837], [29834], .source 14983⟩,
    ⟨[29839], [29835, 23903], .source 14984⟩,
    ⟨[29839, 88699], [93271], .contexts [
        ⟨78262, false, false, [], [88699]⟩,
        ⟨55339, true, false, [29835], []⟩,
        ⟨78260, true, false, [], [11]⟩,
        ⟨78261, true, true, [], [84479, 11]⟩,
        ⟨78260, true, false, [29836, 29834], [11]⟩,
        ⟨26904, true, false, [29836], [11]⟩,
        ⟨78259, true, false, [29836, 29834], [1, 11]⟩,
        ⟨78085, false, false, [29836, 29834], [11]⟩,
        ⟨78099, false, false, [29836, 29834], [11]⟩,
        ⟨13, true, false, [29836, 29834], [93273, 11]⟩,
        ⟨78261, true, false, [29836], [93273, 11]⟩,
        ⟨78082, false, false, [], []⟩,
        ⟨78100, false, false, [], []⟩
      ]⟩,
    ⟨[29841], [29838], .source 14985⟩,
    ⟨[29841], [29838], .contexts [
        ⟨78264, false, false, [], []⟩
      ]⟩,
    ⟨[29838], [29838], .contexts []⟩,
    ⟨[88699, 9], [29841, 93269], .contexts [
        ⟨78264, true, true, [29838], [88699, 9]⟩,
        ⟨78263, false, false, [29838, 29840, 29838], [9]⟩,
        ⟨13, true, false, [29838, 29840, 29838], [93271, 9]⟩,
        ⟨78265, true, false, [29838, 29840], [93271, 9]⟩,
        ⟨78079, false, false, [29838], []⟩,
        ⟨78101, false, false, [29838], []⟩,
        ⟨78266, true, false, [], [93269]⟩,
        ⟨78266, true, false, [], [93269]⟩,
        ⟨78265, true, false, [], [93269]⟩
      ]⟩,
    ⟨[29793, 93281], [29793, 93281], .contexts []⟩,
    ⟨[29793, 93281], [29793, 93281], .contexts []⟩,
    ⟨[29843], [29793, 29827], .source 14986⟩,
    ⟨[24789, 86911], [24789, 86911], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1223. -/
def y322TCIndexRaw1223 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[24789, 86911], [24789, 86911], .contexts []⟩,
    ⟨[93277, 9], [93277, 9], .contexts []⟩,
    ⟨[29845], [29842], .source 14987⟩,
    ⟨[29847], [29845, 24789], .source 14988⟩,
    ⟨[93277, 9], [29847, 86907], .contexts [
        ⟨78273, false, false, [], []⟩,
        ⟨78270, false, false, [29842], [93277, 9]⟩,
        ⟨78257, true, false, [29842, 29793], [9]⟩,
        ⟨78096, true, false, [29842, 29793], [9]⟩,
        ⟨78269, true, false, [29842], [1, 9]⟩,
        ⟨78269, true, false, [29842], [1, 9]⟩,
        ⟨78268, true, false, [29842], [1, 9]⟩,
        ⟨78218, true, false, [29842], [1, 9]⟩,
        ⟨78215, true, false, [29842], [1, 9]⟩,
        ⟨1964, false, false, [29842, 90225], []⟩,
        ⟨693, false, false, [29842, 90225], []⟩,
        ⟨59731, false, false, [29842], [9, 1]⟩,
        ⟨78271, false, false, [29842], [9, 1]⟩,
        ⟨78272, false, false, [29842], [9, 1]⟩,
        ⟨78272, false, false, [29842], [9, 1]⟩,
        ⟨39385, false, false, [29842, 24789], [1]⟩,
        ⟨39381, false, false, [29842, 24789], []⟩,
        ⟨40508, false, false, [29842, 24789], []⟩,
        ⟨78274, true, false, [], [24789, 86907]⟩,
        ⟨78275, true, false, [], [86907]⟩
      ]⟩,
    ⟨[29849], [29846], .source 14989⟩,
    ⟨[29851], [23135, 23107], .source 14990⟩,
    ⟨[29853], [29851, 22271], .source 14991⟩,
    ⟨[23903, 88699], [23903, 88699], .contexts []⟩,
    ⟨[29855], [23903, 29841], .source 14992⟩,
    ⟨[87211, 11], [87211, 11], .contexts []⟩,
    ⟨[93269], [93269], .contexts []⟩,
    ⟨[29857], [29852], .source 14993⟩,
    ⟨[29859], [29857, 29855], .source 14994⟩,
    ⟨[87211, 11], [29859, 93269], .contexts [
        ⟨78282, false, false, [], []⟩,
        ⟨78279, false, false, [29852], [87211, 11]⟩,
        ⟨48344, true, false, [29852, 29851], [11]⟩,
        ⟨78278, false, false, [29852], [85727, 9, 11]⟩,
        ⟨51758, true, false, [29852, 23135], [9, 11]⟩,
        ⟨57173, true, false, [29852], [11, 9, 11]⟩,
        ⟨536, false, false, [29852, 84479], []⟩,
        ⟨537, false, false, [29852, 84479], []⟩,
        ⟨55339, false, false, [29852], [9]⟩,
        ⟨78280, false, false, [29852], [9]⟩,
        ⟨78280, false, false, [29852], [9]⟩,
        ⟨78267, false, false, [29852, 23903], []⟩,
        ⟨78281, true, false, [29852], [93269]⟩,
        ⟨78283, false, false, [29852, 29855], []⟩,
        ⟨78284, true, false, [], [29855, 93269]⟩,
        ⟨78285, true, false, [], [93269]⟩
      ]⟩,
    ⟨[88701], [23913, 84475], .contexts [
        ⟨59581, false, false, [], []⟩
      ]⟩,
    ⟨[29841, 93269], [29841, 93269], .contexts []⟩,
    ⟨[88699, 9], [29841, 93269], .contexts [
        ⟨78267, false, false, [], []⟩,
        ⟨78288, false, false, [], []⟩,
        ⟨78288, false, false, [], []⟩
      ]⟩,
    ⟨[84471, 9], [84471, 9], .contexts []⟩,
    ⟨[93267], [93267], .contexts []⟩,
    ⟨[29863], [23915, 29841], .source 14996⟩,
    ⟨[84471, 9], [29863, 93267], .contexts [
        ⟨78290, false, false, [], []⟩,
        ⟨26895, true, false, [], [9]⟩,
        ⟨26899, true, false, [], [1, 9]⟩,
        ⟨59580, true, false, [23912], [9, 1, 9]⟩,
        ⟨59580, true, false, [23912], [9, 1, 9]⟩,
        ⟨78287, true, false, [23912], [9, 1, 9]⟩,
        ⟨55370, true, false, [23912], [9, 1, 9]⟩,
        ⟨582, false, false, [23912, 88699], []⟩,
        ⟨453, false, false, [23912, 88699], []⟩,
        ⟨78289, false, false, [23912], [1]⟩,
        ⟨78076, false, false, [23912, 29841], []⟩,
        ⟨78291, false, false, [23912, 29841], []⟩,
        ⟨55366, true, false, [], [29841, 93267]⟩,
        ⟨78292, true, false, [], [93267]⟩
      ]⟩,
    ⟨[29865], [29862], .source 14997⟩,
    ⟨[93267, 9], [29865, 84471], .contexts [
        ⟨78293, true, false, [29862], [9]⟩,
        ⟨46, false, false, [29862, 84471], []⟩,
        ⟨78294, true, false, [], [84471]⟩
      ]⟩,
    ⟨[23887, 89307], [23887, 89307], .contexts []⟩,
    ⟨[23887, 89307], [23887, 89307], .contexts []⟩,
    ⟨[29867], [23887, 23873], .source 14998⟩,
    ⟨[88699, 8], [88699, 9], .contexts [
        ⟨47, false, false, [88699], []⟩
      ]⟩,
    ⟨[29869], [29866], .source 14999⟩,
    ⟨[29871], [29869, 29841], .source 15000⟩,
    ⟨[87057, 13], [29871, 93269], .contexts [
        ⟨78298, false, false, [29866], [87057, 13]⟩,
        ⟨55273, true, false, [29866, 23887], [13]⟩,
        ⟨78297, true, false, [29866], [9, 13]⟩,
        ⟨78297, true, false, [29866], [9, 13]⟩,
        ⟨78296, true, false, [29866], [9, 13]⟩,
        ⟨55291, true, false, [29866], [9, 13]⟩,
        ⟨55288, true, false, [29866], [9, 13]⟩,
        ⟨942, false, false, [29866, 88699], []⟩,
        ⟨78299, false, false, [29866], []⟩,
        ⟨78289, false, false, [29866], []⟩,
        ⟨78283, false, false, [29866, 29841], []⟩,
        ⟨78300, true, false, [], [29841, 93269]⟩,
        ⟨78301, true, false, [], [93269]⟩
      ]⟩,
    ⟨[29873], [29870], .source 15001⟩,
    ⟨[23893, 88699], [23893, 88699], .contexts []⟩,
    ⟨[23893, 88699], [23893, 88699], .contexts []⟩,
    ⟨[88699, 3], [23893, 88699], .contexts [
        ⟨55297, false, false, [], []⟩,
        ⟨55301, false, false, [], []⟩,
        ⟨78304, false, false, [], []⟩,
        ⟨78305, false, false, [], []⟩,
        ⟨78305, false, false, [], []⟩
      ]⟩,
    ⟨[29875], [23893, 29841], .source 15002⟩,
    ⟨[29877], [29874], .source 15003⟩,
    ⟨[29879], [29877, 29841], .source 15004⟩,
    ⟨[88091, 5], [88091, 5], .contexts []⟩,
    ⟨[29881], [23895, 29841], .source 15005⟩,
    ⟨[88091, 5], [29881, 93269], .contexts [
        ⟨78310, false, false, [], []⟩,
        ⟨48368, true, false, [], [5]⟩,
        ⟨55361, true, false, [23896], [9, 5]⟩,
        ⟨960, false, false, [23896, 88699], []⟩,
        ⟨78299, false, false, [23896], []⟩,
        ⟨78289, false, false, [23896], []⟩,
        ⟨78283, false, false, [23896, 29841], []⟩,
        ⟨55314, true, false, [], [29841, 93269]⟩,
        ⟨78311, true, false, [], [93269]⟩
      ]⟩,
    ⟨[29883], [29880], .source 15006⟩,
    ⟨[29863, 93267], [29863, 93267], .contexts []⟩,
    ⟨[29863, 93267], [29863, 93267], .contexts []⟩,
    ⟨[84471, 9], [29863, 93267], .contexts [
        ⟨78290, false, false, [], []⟩,
        ⟨78293, false, false, [], []⟩,
        ⟨78314, false, false, [], []⟩,
        ⟨78315, false, false, [], []⟩,
        ⟨78315, false, false, [], []⟩
      ]⟩,
    ⟨[93265, 9], [93265, 9], .contexts []⟩,
    ⟨[84469], [84469], .contexts []⟩,
    ⟨[29865], [29862], .contexts [
        ⟨78294, false, false, [], []⟩
      ]⟩,
    ⟨[29862], [29862], .contexts []⟩,
    ⟨[93265, 9], [29865, 84469], .contexts [
        ⟨78317, false, false, [], []⟩,
        ⟨78072, true, false, [], [9]⟩,
        ⟨78316, true, false, [29862], [5, 9]⟩,
        ⟨598, false, false, [29862, 84471], []⟩,
        ⟨29, false, false, [29862, 84471], []⟩,
        ⟨26933, false, false, [29862], []⟩,
        ⟨26934, false, false, [29862], []⟩,
        ⟨26890, false, false, [29862], []⟩,
        ⟨26890, false, false, [29862], []⟩,
        ⟨78318, false, false, [29862], []⟩,
        ⟨78320, true, false, [], [84469]⟩,
        ⟨78320, true, false, [], [84469]⟩,
        ⟨78319, true, false, [], [84469]⟩
      ]⟩,
    ⟨[29885], [25287, 24275], .source 15007⟩,
    ⟨[93267, 13], [93267, 13], .contexts []⟩,
    ⟨[29887], [29865, 29885], .source 15008⟩,
    ⟨[93267, 13], [29887, 89693], .contexts [
        ⟨78323, false, false, [], []⟩,
        ⟨78316, true, false, [29862], [13]⟩,
        ⟨201, false, false, [29862, 84471], []⟩,
        ⟨202, false, false, [29862, 84471], []⟩,
        ⟨61820, false, false, [29862], [9]⟩,
        ⟨61815, false, false, [29862], [9]⟩,
        ⟨61816, false, false, [29862], [9]⟩,
        ⟨61816, false, false, [29862], [9]⟩,
        ⟨57183, false, false, [29862, 25287], []⟩,
        ⟨78322, true, false, [29862], [89693]⟩,
        ⟨57181, false, false, [29862, 29885], []⟩,
        ⟨78319, true, false, [], [29885, 89693]⟩,
        ⟨78324, true, false, [], [89693]⟩
      ]⟩,
    ⟨[29889], [29886], .source 15009⟩,
    ⟨[29881, 93269], [29881, 93269], .contexts []⟩,
    ⟨[29881, 93265], [29881, 93265], .contexts []⟩,
    ⟨[29881, 93265], [29881, 93265], .contexts []⟩,
    ⟨[93265, 1], [93265, 1], .contexts []⟩,
    ⟨[29883], [29880], .contexts [
        ⟨78313, false, false, [], []⟩
      ]⟩,
    ⟨[29880], [29880], .contexts []⟩,
    ⟨[29883], [29880], .contexts [
        ⟨78331, false, false, [], []⟩,
        ⟨78332, false, false, [], []⟩,
        ⟨78332, false, false, [], []⟩
      ]⟩,
    ⟨[93265, 1], [29883, 88091], .contexts [
        ⟨78330, false, false, [], []⟩,
        ⟨78329, true, false, [29880], [1]⟩,
        ⟨78328, true, false, [29880], [1]⟩,
        ⟨78072, true, false, [], [1]⟩,
        ⟨78076, true, false, [], [5, 1]⟩,
        ⟨78327, true, false, [29880], [1, 5, 1]⟩,
        ⟨78327, true, false, [29880], [1, 5, 1]⟩,
        ⟨78312, true, false, [29880], [1, 5, 1]⟩,
        ⟨78310, true, false, [29880], [1, 5, 1]⟩,
        ⟨874, false, false, [29880, 88091], []⟩,
        ⟨78333, true, false, [], [88091]⟩
      ]⟩,
    ⟨[29881], [29882], .contexts [
        ⟨78313, true, true, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1224. -/
def y322TCIndexRaw1224 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88091, 1], [29881, 93265], .contexts [
        ⟨78334, true, false, [29882], [1]⟩,
        ⟨8, false, false, [29882, 93265], []⟩,
        ⟨78335, true, false, [], [93265]⟩
      ]⟩,
    ⟨[29865, 84469], [29865, 84469], .contexts []⟩,
    ⟨[93265, 9], [29865, 84469], .contexts [
        ⟨78317, false, false, [], []⟩,
        ⟨78321, false, false, [], []⟩,
        ⟨78337, false, false, [], []⟩,
        ⟨78337, false, false, [], []⟩
      ]⟩,
    ⟨[84467, 9], [84467, 9], .contexts []⟩,
    ⟨[29864], [29864], .contexts []⟩,
    ⟨[84467, 9], [29863, 93263], .contexts [
        ⟨78339, false, false, [], []⟩,
        ⟨26887, true, false, [], [9]⟩,
        ⟨78338, true, false, [29864], [3, 9]⟩,
        ⟨479, false, false, [29864, 93265], []⟩,
        ⟨21, false, false, [29864, 93265], []⟩,
        ⟨78105, false, false, [29864], []⟩,
        ⟨78106, false, false, [29864], []⟩,
        ⟨78067, false, false, [29864], []⟩,
        ⟨78067, false, false, [29864], []⟩,
        ⟨78340, true, false, [], [93263]⟩,
        ⟨78340, true, false, [], [93263]⟩,
        ⟨78294, false, true, [], [93263]⟩
      ]⟩,
    ⟨[29891], [29865, 21783], .source 15010⟩,
    ⟨[29893], [29891, 18941], .source 15011⟩,
    ⟨[93265], [93265], .contexts []⟩,
    ⟨[85931, 7], [29892, 93265], .contexts [
        ⟨78343, false, false, [29892], [85931, 7]⟩,
        ⟨35911, true, false, [29892, 29891], [7]⟩,
        ⟨78342, false, false, [29892], [86209, 9, 7]⟩,
        ⟨46401, false, false, [29892, 29865], [86209, 9, 7]⟩,
        ⟨46180, false, false, [29892, 29865], [21765, 86209, 9, 7]⟩,
        ⟨46371, true, false, [29892, 29865, 21726], [9, 7]⟩,
        ⟨46333, false, false, [29892, 29865, 21726], [86209, 9, 7]⟩,
        ⟨38, true, false, [29892, 29865, 21726, 21766, 86209], [9, 7]⟩,
        ⟨46373, false, false, [29892, 29865, 21726, 21766], [7, 9, 7]⟩,
        ⟨46400, false, false, [29892, 29865, 21726], [7, 9, 7]⟩,
        ⟨78338, true, false, [29892], [7, 9, 7]⟩,
        ⟨469, false, false, [29892, 93265], []⟩,
        ⟨78344, false, false, [29892], []⟩
      ]⟩,
    ⟨[93265], [93265], .contexts []⟩,
    ⟨[29895], [29892], .source 15012⟩,
    ⟨[29895], [29892], .contexts [
        ⟨78347, false, false, [], []⟩
      ]⟩,
    ⟨[29892], [29892], .contexts []⟩,
    ⟨[85931, 7], [29895, 93265], .contexts [
        ⟨78345, false, false, [], []⟩,
        ⟨78346, false, false, [29892], []⟩,
        ⟨78349, true, false, [], [93265]⟩,
        ⟨78349, true, false, [], [93265]⟩,
        ⟨78348, true, false, [], [93265]⟩
      ]⟩,
    ⟨[93265, 7], [29893, 85931], .contexts [
        ⟨78350, true, false, [29894], [7]⟩,
        ⟨38, false, false, [29894, 85931], []⟩,
        ⟨78347, false, true, [], [85931]⟩
      ]⟩,
    ⟨[29897], [29865, 25287], .source 15013⟩,
    ⟨[29899], [29897, 24275], .source 15014⟩,
    ⟨[29901], [29898], .source 15015⟩,
    ⟨[29898], [29898], .contexts []⟩,
    ⟨[29883, 88091], [29883, 88091], .contexts []⟩,
    ⟨[29883, 88091], [29883, 88091], .contexts []⟩,
    ⟨[29883, 88095], [29883, 88095], .contexts []⟩,
    ⟨[29883, 88095], [29883, 88095], .contexts []⟩,
    ⟨[88095, 15], [88095, 15], .contexts []⟩,
    ⟨[29882], [29882], .contexts []⟩,
    ⟨[29881], [29882], .contexts [
        ⟨78335, false, false, [], []⟩,
        ⟨78361, false, false, [], []⟩,
        ⟨78361, false, false, [], []⟩
      ]⟩,
    ⟨[88095, 15], [29881, 93265], .contexts [
        ⟨78360, false, false, [], []⟩,
        ⟨78359, true, false, [29882], [15]⟩,
        ⟨78358, true, false, [29882], [15]⟩,
        ⟨48386, true, false, [], [15]⟩,
        ⟨48374, true, false, [], [1, 15]⟩,
        ⟨78357, true, false, [29882], [15, 1, 15]⟩,
        ⟨78357, true, false, [29882], [15, 1, 15]⟩,
        ⟨78356, true, false, [29882], [15, 1, 15]⟩,
        ⟨78334, true, false, [29882], [15, 1, 15]⟩,
        ⟨78330, true, false, [29882], [15, 1, 15]⟩,
        ⟨2185, false, false, [29882, 93265], []⟩,
        ⟨78344, false, false, [29882], []⟩,
        ⟨78346, false, false, [29882], []⟩,
        ⟨78362, true, false, [], [93265]⟩
      ]⟩,
    ⟨[93265, 15], [29883, 88095], .contexts [
        ⟨78363, true, false, [29880], [15]⟩,
        ⟨1, false, false, [29880, 88095], []⟩,
        ⟨78313, true, false, [], [88095]⟩
      ]⟩,
    ⟨[29863, 93263], [29863, 93263], .contexts []⟩,
    ⟨[84467, 9], [29863, 93263], .contexts [
        ⟨78339, false, false, [], []⟩,
        ⟨78341, false, false, [], []⟩,
        ⟨78365, false, false, [], []⟩,
        ⟨78365, false, false, [], []⟩
      ]⟩,
    ⟨[93261, 9], [93261, 9], .contexts []⟩,
    ⟨[29903], [29865, 22867], .source 15016⟩,
    ⟨[93261, 9], [29903, 86311], .contexts [
        ⟨78367, false, false, [], []⟩,
        ⟨78065, true, false, [], [9]⟩,
        ⟨78366, true, false, [29862], [1, 9]⟩,
        ⟨1964, false, false, [29862, 84467], []⟩,
        ⟨693, false, false, [29862, 84467], []⟩,
        ⟨46429, false, false, [29862], [9, 1]⟩,
        ⟨50668, false, false, [29862], [1]⟩,
        ⟨50669, false, false, [29862], [1]⟩,
        ⟨50670, false, false, [29862], [1]⟩,
        ⟨50670, false, false, [29862], [1]⟩,
        ⟨36302, false, false, [29862, 22867], []⟩,
        ⟨50572, false, false, [29862, 22867], []⟩,
        ⟨78319, true, false, [], [22867, 86311]⟩,
        ⟨78368, true, false, [], [86311]⟩
      ]⟩,
    ⟨[29905], [29902], .source 15017⟩,
    ⟨[86311, 9], [29905, 93261], .contexts [
        ⟨78369, true, false, [29902], [9]⟩,
        ⟨46, false, false, [29902, 93261], []⟩,
        ⟨78370, true, false, [], [93261]⟩
      ]⟩,
    ⟨[29907], [21789, 21239], .source 15018⟩,
    ⟨[93263, 7], [93263, 7], .contexts []⟩,
    ⟨[29909], [29865, 29907], .source 15019⟩,
    ⟨[93263, 7], [29909, 83087], .contexts [
        ⟨78373, false, false, [], []⟩,
        ⟨78366, true, false, [29862], [7]⟩,
        ⟨1084, false, false, [29862, 84467], []⟩,
        ⟨1085, false, false, [29862, 84467], []⟩,
        ⟨46426, false, false, [29862], [9]⟩,
        ⟨44578, false, false, [29862, 21789], []⟩,
        ⟨78372, true, false, [29862], [83087]⟩,
        ⟨44493, false, false, [29862, 29907], []⟩,
        ⟨78319, true, false, [], [29907, 83087]⟩,
        ⟨78374, true, false, [], [83087]⟩
      ]⟩,
    ⟨[29911], [29908], .source 15020⟩,
    ⟨[83087, 7], [29911, 93263], .contexts [
        ⟨78375, true, false, [29908], [7]⟩,
        ⟨38, false, false, [29908, 93263], []⟩,
        ⟨78376, true, false, [], [93263]⟩
      ]⟩,
    ⟨[25299, 83311], [25299, 83311], .contexts []⟩,
    ⟨[25299, 83311], [25299, 83311], .contexts []⟩,
    ⟨[29913], [25299, 28253], .source 15021⟩,
    ⟨[29915], [29865, 29913], .source 15022⟩,
    ⟨[93263, 13], [29915, 92573], .contexts [
        ⟨78366, true, false, [29862], [13]⟩,
        ⟨201, false, false, [29862, 84467], []⟩,
        ⟨202, false, false, [29862, 84467], []⟩,
        ⟨61787, false, false, [29862], [9]⟩,
        ⟨61791, false, false, [29862], [9]⟩,
        ⟨78378, false, false, [29862], [9]⟩,
        ⟨78379, false, false, [29862], [9]⟩,
        ⟨78379, false, false, [29862], [9]⟩,
        ⟨73234, false, false, [29862, 25299], []⟩,
        ⟨78380, true, false, [29862], [92573]⟩,
        ⟨73225, false, false, [29862, 29913], []⟩,
        ⟨78319, true, false, [], [29913, 92573]⟩,
        ⟨78381, true, false, [], [92573]⟩
      ]⟩,
    ⟨[29917], [29914], .source 15023⟩,
    ⟨[88095, 15], [29881, 93265], .contexts [
        ⟨78360, false, false, [], []⟩,
        ⟨78363, false, false, [], []⟩,
        ⟨78328, false, false, [], []⟩,
        ⟨78329, false, false, [], []⟩,
        ⟨78329, false, false, [], []⟩
      ]⟩,
    ⟨[29881, 93263], [29881, 93263], .contexts []⟩,
    ⟨[29881, 93263], [29881, 93263], .contexts []⟩,
    ⟨[93263, 15], [93263, 15], .contexts []⟩,
    ⟨[88097], [88097], .contexts []⟩,
    ⟨[93263, 15], [29883, 88097], .contexts [
        ⟨78387, false, false, [], []⟩,
        ⟨78386, true, false, [29880], [15]⟩,
        ⟨78385, true, false, [29880], [15]⟩,
        ⟨78068, true, false, [], [15]⟩,
        ⟨78384, true, false, [29880], [3, 15]⟩,
        ⟨1141, false, false, [29880, 88095], []⟩,
        ⟨21, false, false, [29880, 88095], []⟩,
        ⟨48400, false, false, [29880], []⟩,
        ⟨78388, false, false, [29880], []⟩,
        ⟨78333, true, false, [], [88097]⟩
      ]⟩,
    ⟨[29903, 86311], [29903, 86311], .contexts []⟩,
    ⟨[93261, 9], [29903, 86311], .contexts [
        ⟨78367, false, false, [], []⟩,
        ⟨78369, false, false, [], []⟩,
        ⟨78390, false, false, [], []⟩,
        ⟨78390, false, false, [], []⟩
      ]⟩,
    ⟨[29919], [29903, 22817], .source 15024⟩,
    ⟨[29921], [29919, 21159], .source 15025⟩,
    ⟨[93261], [93261], .contexts []⟩,
    ⟨[83089, 7], [83089, 7], .contexts []⟩,
    ⟨[93261], [93261], .contexts []⟩,
    ⟨[29923], [29920], .source 15026⟩,
    ⟨[29920], [29920], .contexts []⟩,
    ⟨[83089, 7], [29923, 93261], .contexts [
        ⟨78395, false, false, [], []⟩,
        ⟨78393, false, false, [29920], [83089, 7]⟩,
        ⟨44472, true, false, [29920, 29919], [7]⟩,
        ⟨78392, false, false, [29920], [85597, 9, 7]⟩,
        ⟨50576, true, false, [29920, 29903], [9, 7]⟩,
        ⟨78391, true, false, [29920], [7, 9, 7]⟩,
        ⟨469, false, false, [29920, 93261], []⟩,
        ⟨78394, false, false, [29920], []⟩,
        ⟨78396, false, false, [29920], []⟩,
        ⟨78398, true, false, [], [93261]⟩,
        ⟨78398, true, false, [], [93261]⟩,
        ⟨78397, true, false, [], [93261]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1225. -/
def y322TCIndexRaw1225 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[29921], [29922], .contexts [
        ⟨78397, true, true, [], []⟩
      ]⟩,
    ⟨[29925], [29903, 22855], .source 15027⟩,
    ⟨[29927], [29925, 29905], .source 15028⟩,
    ⟨[93261, 13], [93261, 13], .contexts []⟩,
    ⟨[29929], [29926], .source 15029⟩,
    ⟨[29926], [29926], .contexts []⟩,
    ⟨[29929], [29926], .contexts [
        ⟨78404, false, false, [], []⟩,
        ⟨78405, false, false, [], []⟩,
        ⟨78405, false, false, [], []⟩
      ]⟩,
    ⟨[29909, 83087], [29909, 83087], .contexts []⟩,
    ⟨[29883, 88097], [29883, 88097], .contexts []⟩,
    ⟨[29883, 88097], [29883, 88097], .contexts []⟩,
    ⟨[93263, 15], [29883, 88097], .contexts [
        ⟨78387, false, false, [], []⟩,
        ⟨78389, false, false, [], []⟩,
        ⟨78408, false, false, [], []⟩,
        ⟨78409, false, false, [], []⟩,
        ⟨78409, false, false, [], []⟩
      ]⟩,
    ⟨[29931], [29911, 29883], .source 15030⟩,
    ⟨[83085, 7], [29931, 88097], .contexts [
        ⟨18547, true, false, [], [7]⟩,
        ⟨78407, true, false, [29908], [15, 7]⟩,
        ⟨78407, true, false, [29908], [15, 7]⟩,
        ⟨78375, true, false, [29908], [15, 7]⟩,
        ⟨78373, true, false, [29908], [15, 7]⟩,
        ⟨18155, false, false, [29908, 93263], []⟩,
        ⟨10, false, false, [29908, 93263], []⟩,
        ⟨78410, false, false, [29908], []⟩,
        ⟨78388, false, false, [29908, 29883], []⟩,
        ⟨78376, true, false, [], [29883, 88097]⟩,
        ⟨78411, true, false, [], [88097]⟩
      ]⟩,
    ⟨[29933], [29930], .source 15031⟩,
    ⟨[88097, 1], [88097, 1], .contexts []⟩,
    ⟨[29923, 93261], [29923, 93261], .contexts []⟩,
    ⟨[29935], [29921, 18503], .source 15032⟩,
    ⟨[29937], [29934], .source 15033⟩,
    ⟨[85819, 7], [29937, 93259], .contexts [
        ⟨78416, false, false, [29934], [85819, 7]⟩,
        ⟨78400, false, false, [29934], [18503, 85819, 7]⟩,
        ⟨33873, true, false, [29934, 29922, 18503], [7]⟩,
        ⟨33877, true, false, [29934, 29922], [7]⟩,
        ⟨10, true, false, [29934, 29922, 83089], [7]⟩,
        ⟨18155, true, false, [29934, 29922, 83089], [7]⟩,
        ⟨78395, false, false, [29934, 29922], [15, 7, 7]⟩,
        ⟨78399, false, false, [29934, 29922], [15, 7, 7]⟩,
        ⟨78415, false, false, [29934, 29922], [15, 7, 7]⟩,
        ⟨78415, false, false, [29934, 29922], [15, 7, 7]⟩,
        ⟨78062, false, false, [29934], [7, 7]⟩,
        ⟨38, false, false, [29934, 93259], []⟩,
        ⟨78417, true, false, [], [93259]⟩
      ]⟩,
    ⟨[29929, 93261], [29929, 93261], .contexts []⟩,
    ⟨[93261, 13], [29929, 93261], .contexts [
        ⟨78403, false, false, [], []⟩,
        ⟨78403, false, false, [], []⟩,
        ⟨78402, false, false, [29926], [93261, 13]⟩,
        ⟨78371, true, false, [29926, 29925], [13]⟩,
        ⟨78401, false, false, [29926], [86311, 9, 13]⟩,
        ⟨50618, true, false, [29926, 29903], [9, 13]⟩,
        ⟨78391, true, false, [29926], [13, 9, 13]⟩,
        ⟨475, false, false, [29926, 93261], []⟩,
        ⟨78394, false, false, [29926], []⟩,
        ⟨78396, false, false, [29926], []⟩,
        ⟨78406, true, false, [], [93261]⟩,
        ⟨78419, false, false, [], []⟩,
        ⟨78419, false, false, [], []⟩
      ]⟩,
    ⟨[93257, 15], [93257, 15], .contexts []⟩,
    ⟨[29927], [29928], .contexts [
        ⟨78404, true, true, [], []⟩
      ]⟩,
    ⟨[29927], [29927], .contexts []⟩,
    ⟨[29928], [29928], .contexts []⟩,
    ⟨[29927], [29928], .contexts [
        ⟨78423, false, false, [], []⟩,
        ⟨78422, false, false, [], []⟩,
        ⟨78424, false, false, [], []⟩,
        ⟨78424, false, false, [], []⟩
      ]⟩,
    ⟨[29881, 93259], [29881, 93259], .contexts []⟩,
    ⟨[88097, 1], [29881, 93259], .contexts [
        ⟨78414, false, false, [], []⟩,
        ⟨78414, false, false, [], []⟩,
        ⟨78410, true, false, [29882], [1]⟩,
        ⟨7, false, false, [29882, 93263], []⟩,
        ⟨11, false, false, [29882, 93263], []⟩,
        ⟨78107, false, false, [29882], [15]⟩,
        ⟨78108, false, false, [29882], [15]⟩,
        ⟨78064, false, false, [29882], [15]⟩,
        ⟨78064, false, false, [29882], [15]⟩,
        ⟨78109, false, false, [29882], []⟩,
        ⟨78110, false, false, [29882], []⟩,
        ⟨78061, false, false, [29882], []⟩,
        ⟨78061, false, false, [29882], []⟩,
        ⟨78362, true, false, [], [93259]⟩,
        ⟨78426, false, false, [], []⟩,
        ⟨78426, false, false, [], []⟩
      ]⟩,
    ⟨[29939], [18273, 26051], .source 15034⟩,
    ⟨[29941], [29883, 29939], .source 15035⟩,
    ⟨[93259, 11], [29941, 91269], .contexts [
        ⟨78427, true, false, [29880], [11]⟩,
        ⟨110, false, false, [29880, 88097], []⟩,
        ⟨111, false, false, [29880, 88097], []⟩,
        ⟨48412, false, false, [29880], [1]⟩,
        ⟨65306, false, false, [29880, 18273], []⟩,
        ⟨78428, true, false, [29880], [91269]⟩,
        ⟨65314, false, false, [29880, 29939], []⟩,
        ⟨78331, true, false, [], [29939, 91269]⟩,
        ⟨78429, true, false, [], [91269]⟩
      ]⟩,
    ⟨[29943], [29940], .source 15036⟩,
    ⟨[29927, 93257], [29927, 93257], .contexts []⟩,
    ⟨[93257, 15], [29927, 93257], .contexts [
        ⟨78421, false, false, [], []⟩,
        ⟨78421, false, false, [], []⟩,
        ⟨78059, true, false, [], [15]⟩,
        ⟨78062, true, false, [], [13, 15]⟩,
        ⟨78420, true, false, [29928], [15, 13, 15]⟩,
        ⟨2022, false, false, [29928, 93261], []⟩,
        ⟨89, false, false, [29928, 93261], []⟩,
        ⟨78109, false, false, [29928], [13]⟩,
        ⟨78110, false, false, [29928], [13]⟩,
        ⟨78061, false, false, [29928], [13]⟩,
        ⟨78061, false, false, [29928], [13]⟩,
        ⟨78112, false, false, [29928], []⟩,
        ⟨78113, false, false, [29928], []⟩,
        ⟨78058, false, false, [29928], []⟩,
        ⟨78058, false, false, [29928], []⟩,
        ⟨78425, true, false, [], [93257]⟩,
        ⟨78432, false, false, [], []⟩,
        ⟨78432, false, false, [], []⟩
      ]⟩,
    ⟨[93255, 15], [93255, 15], .contexts []⟩,
    ⟨[29929, 93255], [29929, 93255], .contexts []⟩,
    ⟨[93255, 15, 11], [29929, 93253], .contexts [
        ⟨78434, false, false, [], [11]⟩,
        ⟨78434, false, false, [], [11]⟩,
        ⟨78056, true, false, [], [15, 11]⟩,
        ⟨78433, true, false, [29926], [1, 15, 11]⟩,
        ⟨1666, false, false, [29926, 93257], [11]⟩,
        ⟨9, false, false, [29926, 93257], [11]⟩,
        ⟨78114, false, false, [29926], [11]⟩,
        ⟨78115, false, false, [29926], [11]⟩,
        ⟨78055, false, false, [29926], [11]⟩,
        ⟨78055, false, false, [29926], [11]⟩,
        ⟨78406, true, false, [], [93255, 11]⟩,
        ⟨78435, false, false, [], [11]⟩,
        ⟨78435, false, false, [], [11]⟩,
        ⟨78053, false, false, [29929], []⟩
      ]⟩,
    ⟨[93253, 15], [93253, 15], .contexts []⟩,
    ⟨[29927, 93253], [29927, 93253], .contexts []⟩,
    ⟨[29927, 93251, 15], [93253, 9], .contexts [
        ⟨78050, true, false, [29927], [15]⟩,
        ⟨78438, true, false, [], [9, 15]⟩,
        ⟨78438, true, false, [], [9, 15]⟩,
        ⟨78425, false, false, [], [93253, 9, 15]⟩,
        ⟨78052, true, false, [29928], [9, 15]⟩,
        ⟨78052, true, false, [29928], [9, 15]⟩,
        ⟨78117, true, false, [29928], [9, 15]⟩,
        ⟨78116, true, false, [29928], [9, 15]⟩,
        ⟨54, true, false, [29928, 93255], [9, 15]⟩,
        ⟨2046, true, false, [29928, 93255], [9, 15]⟩,
        ⟨78436, false, false, [29928], [15, 9, 15]⟩,
        ⟨78437, true, false, [], [9, 15]⟩,
        ⟨78437, true, false, [], [9, 15]⟩,
        ⟨1671, false, false, [93253], []⟩,
        ⟨47, false, false, [93253], []⟩
      ]⟩,
    ⟨[93251, 15], [93251, 15], .contexts []⟩,
    ⟨[93251, 15], [29929, 93251], .contexts [
        ⟨78440, false, false, [], []⟩,
        ⟨78439, false, false, [29926], []⟩,
        ⟨78118, false, false, [29926], []⟩,
        ⟨78119, false, false, [29926], []⟩,
        ⟨78049, false, false, [29926], []⟩,
        ⟨78049, false, false, [29926], []⟩,
        ⟨78406, true, false, [], [93251]⟩
      ]⟩,
    ⟨[29929, 93251], [29929, 93251], .contexts []⟩,
    ⟨[29929, 93251], [29929, 93251], .contexts []⟩,
    ⟨[93249, 15], [93249, 15], .contexts []⟩,
    ⟨[93249, 15], [29927, 93249], .contexts [
        ⟨78444, false, false, [], []⟩,
        ⟨78046, true, false, [], [15]⟩,
        ⟨78443, true, false, [29928], [1, 15]⟩,
        ⟨78443, true, false, [29928], [1, 15]⟩,
        ⟨78442, true, false, [29928], [1, 15]⟩,
        ⟨78441, true, false, [29928], [1, 15]⟩,
        ⟨78440, true, false, [29928], [1, 15]⟩,
        ⟨1666, false, false, [29928, 93251], []⟩,
        ⟨9, false, false, [29928, 93251], []⟩,
        ⟨78120, false, false, [29928], []⟩,
        ⟨78121, false, false, [29928], []⟩,
        ⟨78045, false, false, [29928], []⟩,
        ⟨78045, false, false, [29928], []⟩,
        ⟨78425, true, false, [], [93249]⟩
      ]⟩,
    ⟨[29927, 93249], [29927, 93249], .contexts []⟩,
    ⟨[29927, 93249], [29927, 93249], .contexts []⟩,
    ⟨[93247, 15], [93247, 15], .contexts []⟩,
    ⟨[29929, 93247], [29929, 93247], .contexts []⟩,
    ⟨[93247, 15], [29929, 93247], .contexts [
        ⟨78448, false, false, [], []⟩,
        ⟨78448, false, false, [], []⟩,
        ⟨78042, true, false, [], [15]⟩,
        ⟨78447, true, false, [29926], [5, 15]⟩,
        ⟨78447, true, false, [29926], [5, 15]⟩,
        ⟨78446, true, false, [29926], [5, 15]⟩,
        ⟨78445, true, false, [29926], [5, 15]⟩,
        ⟨78444, true, false, [29926], [5, 15]⟩,
        ⟨2072, false, false, [29926, 93249], []⟩,
        ⟨29, false, false, [29926, 93249], []⟩,
        ⟨78123, false, false, [29926], []⟩,
        ⟨78124, false, false, [29926], []⟩,
        ⟨78041, false, false, [29926], []⟩,
        ⟨78041, false, false, [29926], []⟩,
        ⟨78406, true, false, [], [93247]⟩,
        ⟨78449, false, false, [], []⟩,
        ⟨78449, false, false, [], []⟩
      ]⟩,
    ⟨[93245, 15], [93245, 15], .contexts []⟩,
    ⟨[93245], [93245], .contexts []⟩,
    ⟨[29927, 93245], [29927, 93245], .contexts []⟩,
    ⟨[93245, 15, 1], [29927, 93243], .contexts [
        ⟨78451, false, false, [], [1]⟩,
        ⟨78451, false, false, [], [1]⟩,
        ⟨78039, true, false, [], [15, 1]⟩,
        ⟨78450, true, false, [29928], [3, 15, 1]⟩,
        ⟨1141, false, false, [29928, 93247], [1]⟩,
        ⟨21, false, false, [29928, 93247], [1]⟩,
        ⟨78125, false, false, [29928], [1]⟩,
        ⟨78126, false, false, [29928], [1]⟩,
        ⟨78038, false, false, [29928], [1]⟩,
        ⟨78038, false, false, [29928], [1]⟩,
        ⟨78452, false, false, [29928], [1]⟩,
        ⟨78425, true, false, [], [93245, 1]⟩,
        ⟨78453, false, false, [], [1]⟩,
        ⟨78453, false, false, [], [1]⟩,
        ⟨78036, false, false, [29927], []⟩
      ]⟩,
    ⟨[29927, 93241], [29927, 93241], .contexts []⟩,
    ⟨[29927, 93241], [29927, 93241], .contexts []⟩,
    ⟨[29927], [29927], .contexts [
        ⟨78423, false, false, [], []⟩
      ]⟩,
    ⟨[93283], [92181, 1], .source 46706⟩,
    ⟨[92181, 1], [93283], .contexts [
        ⟨78458, true, false, [], []⟩
      ]⟩,
    ⟨[93283, 1], [92181], .contexts [
        ⟨78459, true, false, [], [1]⟩,
        ⟨8, false, false, [92181], []⟩,
        ⟨70426, false, false, [], []⟩
      ]⟩,
    ⟨[93283], [93283], .contexts []⟩,
    ⟨[92181, 1], [93283], .contexts [
        ⟨78459, false, false, [], []⟩,
        ⟨78461, false, false, [], []⟩,
        ⟨78461, false, false, [], []⟩
      ]⟩,
    ⟨[2373, 93283], [2373, 93283], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1226. -/
def y322TCIndexRaw1226 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[2373, 93283], [2373, 93283], .contexts []⟩,
    ⟨[93283, 5], [93283, 5], .contexts []⟩,
    ⟨[27439, 86593], [27439, 86593], .contexts []⟩,
    ⟨[27439, 86593], [27439, 86593], .contexts []⟩,
    ⟨[92181, 7], [27439, 86593], .contexts [
        ⟨70444, false, false, [], []⟩,
        ⟨70448, false, false, [], []⟩,
        ⟨78466, false, false, [], []⟩,
        ⟨78467, false, false, [], []⟩,
        ⟨78467, false, false, [], []⟩
      ]⟩,
    ⟨[29945], [27439, 21549], .source 15037⟩,
    ⟨[93283, 7], [93283, 7], .contexts []⟩,
    ⟨[93283, 7], [29945, 85319], .contexts [
        ⟨78470, false, false, [], []⟩,
        ⟨78462, true, false, [], [7]⟩,
        ⟨104, false, false, [92181], []⟩,
        ⟨105, false, false, [92181], []⟩,
        ⟨78468, false, false, [], [1]⟩,
        ⟨38198, false, false, [27439], []⟩,
        ⟨45486, false, false, [27439], []⟩,
        ⟨78469, true, false, [], [85319]⟩,
        ⟨31224, false, false, [29945], []⟩,
        ⟨13, true, false, [], [29945, 85319]⟩
      ]⟩,
    ⟨[29947], [29944], .source 15038⟩,
    ⟨[9189, 92179], [9189, 92179], .contexts []⟩,
    ⟨[9189], [9189], .contexts [
        ⟨13, false, false, [], [9189]⟩
      ]⟩,
    ⟨[92179, 11], [9191, 93283], .contexts [
        ⟨78474, false, false, [9188], [92179, 11]⟩,
        ⟨70421, true, false, [], [11]⟩,
        ⟨78473, true, false, [9188], [11]⟩,
        ⟨78473, true, false, [9188], [11]⟩,
        ⟨70409, true, false, [9188], [11]⟩,
        ⟨67778, true, false, [9188], [1, 11]⟩,
        ⟨67778, true, false, [9188], [1, 11]⟩,
        ⟨67777, true, false, [9188], [1, 11]⟩,
        ⟨67778, true, false, [9188], [1, 11]⟩,
        ⟨53, true, false, [9188, 91833], [1, 11]⟩,
        ⟨70423, false, false, [9188], [11, 1, 11]⟩,
        ⟨111, true, false, [9188, 92181], [11]⟩,
        ⟨110, true, false, [9188, 92181], [11]⟩,
        ⟨78462, false, false, [9188], [11, 11]⟩,
        ⟨53, false, false, [9188, 93283], []⟩,
        ⟨11992, true, false, [], [93283]⟩
      ]⟩,
    ⟨[92181, 13], [23677, 89207], .contexts [
        ⟨70450, false, false, [], []⟩,
        ⟨70450, false, false, [], []⟩,
        ⟨70427, true, false, [], [13]⟩,
        ⟨227, false, false, [91833], []⟩,
        ⟨228, false, false, [91833], []⟩,
        ⟨67776, false, false, [], [11]⟩,
        ⟨65107, false, false, [], [11]⟩,
        ⟨65108, false, false, [], [11]⟩,
        ⟨65108, false, false, [], [11]⟩,
        ⟨65132, false, false, [], []⟩,
        ⟨65128, false, false, [], []⟩,
        ⟨65129, false, false, [], []⟩,
        ⟨65129, false, false, [], []⟩,
        ⟨65130, false, false, [], []⟩,
        ⟨65131, false, false, [], []⟩,
        ⟨65128, false, false, [], []⟩,
        ⟨65129, false, false, [], []⟩,
        ⟨65129, false, false, [], []⟩
      ]⟩,
    ⟨[29949], [23677, 23687], .source 15039⟩,
    ⟨[29949, 86321], [29949, 86321], .contexts []⟩,
    ⟨[29949, 86321], [29949, 86321], .contexts []⟩,
    ⟨[93283, 13], [93283, 13], .contexts []⟩,
    ⟨[29949], [29949], .contexts []⟩,
    ⟨[29949], [29949], .contexts []⟩,
    ⟨[93283, 13], [29949, 86321], .contexts [
        ⟨78480, false, false, [], []⟩,
        ⟨78462, true, false, [], [13]⟩,
        ⟨115, false, false, [92181], []⟩,
        ⟨118, false, false, [92181], []⟩,
        ⟨78476, false, false, [], [1, 13, 1]⟩,
        ⟨54526, false, false, [23677], [13, 1]⟩,
        ⟨54646, false, false, [23677], [13, 1]⟩,
        ⟨78477, true, false, [], [86325, 13, 1]⟩,
        ⟨36331, false, false, [29949], [1]⟩,
        ⟨36327, false, false, [29949], []⟩,
        ⟨78478, false, false, [], []⟩,
        ⟨78479, false, false, [], []⟩,
        ⟨36478, false, false, [29949], []⟩,
        ⟨78482, true, false, [], [86321]⟩,
        ⟨78481, true, false, [], [86321]⟩,
        ⟨13, true, false, [], [29949, 86321]⟩
      ]⟩,
    ⟨[29951], [29948], .source 15040⟩,
    ⟨[93285], [93283, 9], .source 46707⟩,
    ⟨[93283, 9], [93285], .contexts [
        ⟨78485, true, false, [], []⟩
      ]⟩,
    ⟨[93285, 9], [93283], .contexts [
        ⟨78486, true, false, [], [9]⟩,
        ⟨46, false, false, [93283], []⟩,
        ⟨78461, false, false, [], []⟩
      ]⟩,
    ⟨[93285], [93285], .contexts []⟩,
    ⟨[93285], [93285], .contexts []⟩,
    ⟨[93283, 9], [93285], .contexts [
        ⟨78486, false, false, [], []⟩,
        ⟨78488, false, false, [], []⟩,
        ⟨78489, false, false, [], []⟩,
        ⟨78489, false, false, [], []⟩
      ]⟩,
    ⟨[2373, 93285], [2373, 93285], .contexts []⟩,
    ⟨[93283, 5, 9], [2373, 93285], .contexts [
        ⟨78465, false, false, [], [9]⟩,
        ⟨78465, false, false, [], [9]⟩,
        ⟨78462, true, false, [], [5, 9]⟩,
        ⟨98, false, false, [92181], [9]⟩,
        ⟨99, false, false, [92181], [9]⟩,
        ⟨70438, false, false, [], [1, 9]⟩,
        ⟨70440, false, false, [], [1, 9]⟩,
        ⟨70436, false, false, [], [1, 9]⟩,
        ⟨70437, false, false, [], [1, 9]⟩,
        ⟨70437, false, false, [], [1, 9]⟩,
        ⟨78459, false, false, [2373], [9]⟩,
        ⟨78463, false, false, [], [9]⟩,
        ⟨78464, false, false, [], [9]⟩,
        ⟨5664, true, false, [], [93283, 9]⟩,
        ⟨78463, false, false, [], [9]⟩,
        ⟨78464, false, false, [], [9]⟩,
        ⟨78464, false, false, [], [9]⟩,
        ⟨78486, false, false, [2373], []⟩,
        ⟨78491, false, false, [], []⟩
      ]⟩,
    ⟨[2373, 93285], [2373, 93285], .contexts []⟩,
    ⟨[93285, 5], [93285, 5], .contexts []⟩,
    ⟨[93285], [93285], .contexts []⟩,
    ⟨[93285, 5], [2373, 93285], .contexts [
        ⟨78494, false, false, [], []⟩,
        ⟨78490, true, false, [], [5]⟩,
        ⟨1079, false, false, [93283], []⟩,
        ⟨1080, false, false, [93283], []⟩,
        ⟨78492, false, false, [], []⟩,
        ⟨78493, false, false, [], []⟩,
        ⟨78495, false, false, [2373], []⟩,
        ⟨5664, true, false, [], [93285]⟩
      ]⟩,
    ⟨[29945, 85319], [29945, 85319], .contexts []⟩,
    ⟨[93283, 7], [29945, 85319], .contexts [
        ⟨78470, false, false, [], []⟩,
        ⟨78471, false, false, [], []⟩,
        ⟨78497, false, false, [], []⟩,
        ⟨78497, false, false, [], []⟩
      ]⟩,
    ⟨[29953], [29945, 20523], .source 15041⟩,
    ⟨[93285, 7], [93285, 7], .contexts []⟩,
    ⟨[93285, 7], [29953, 83621], .contexts [
        ⟨78500, false, false, [], []⟩,
        ⟨78490, true, false, [], [7]⟩,
        ⟨1084, false, false, [93283], []⟩,
        ⟨1085, false, false, [93283], []⟩,
        ⟨78498, false, false, [], [9]⟩,
        ⟨42356, false, false, [29945], []⟩,
        ⟨78499, true, false, [], [83621]⟩,
        ⟨42354, false, false, [29953], []⟩,
        ⟨13, true, false, [], [29953, 83621]⟩
      ]⟩,
    ⟨[29955], [29952], .source 15042⟩,
    ⟨[83621, 7], [29955, 93285], .contexts [
        ⟨78501, true, false, [29952], [7]⟩,
        ⟨38, false, false, [29952, 93285], []⟩,
        ⟨78502, true, false, [], [93285]⟩
      ]⟩,
    ⟨[29957], [29949, 24071], .source 15043⟩,
    ⟨[93285, 13], [29957, 89427], .contexts [
        ⟨78490, true, false, [], [13]⟩,
        ⟨201, false, false, [93283], []⟩,
        ⟨202, false, false, [93283], []⟩,
        ⟨78480, false, false, [], [9]⟩,
        ⟨78483, false, false, [], [9]⟩,
        ⟨78478, false, false, [], [9]⟩,
        ⟨78479, false, false, [], [9]⟩,
        ⟨78479, false, false, [], [9]⟩,
        ⟨56059, false, false, [29949], []⟩,
        ⟨78504, true, false, [], [89427]⟩,
        ⟨56065, false, false, [29957], []⟩,
        ⟨13, true, false, [], [29957, 89427]⟩
      ]⟩,
    ⟨[29959], [29956], .source 15044⟩,
    ⟨[93287], [93285, 11], .source 46708⟩,
    ⟨[93285, 11], [93287], .contexts [
        ⟨78507, true, false, [], []⟩
      ]⟩,
    ⟨[93287, 11], [93285], .contexts [
        ⟨78508, true, false, [], [11]⟩,
        ⟨53, false, false, [93285], []⟩,
        ⟨78489, false, false, [], []⟩
      ]⟩,
    ⟨[93287], [93287], .contexts []⟩,
    ⟨[93287], [93287], .contexts []⟩,
    ⟨[93285, 11], [93287], .contexts [
        ⟨78508, false, false, [], []⟩,
        ⟨78510, false, false, [], []⟩,
        ⟨78511, false, false, [], []⟩,
        ⟨78511, false, false, [], []⟩
      ]⟩,
    ⟨[2373, 93287], [2373, 93287], .contexts []⟩,
    ⟨[2373, 93287], [2373, 93287], .contexts []⟩,
    ⟨[93287, 5], [93287, 5], .contexts []⟩,
    ⟨[93287], [93287], .contexts []⟩,
    ⟨[93287, 5], [2373, 93287], .contexts [
        ⟨78515, false, false, [], []⟩,
        ⟨78512, true, false, [], [5]⟩,
        ⟨642, false, false, [93285], []⟩,
        ⟨643, false, false, [93285], []⟩,
        ⟨78494, false, false, [], [11]⟩,
        ⟨78496, false, false, [], [11]⟩,
        ⟨78491, false, false, [], [11]⟩,
        ⟨78493, false, false, [], [11]⟩,
        ⟨78493, false, false, [], [11]⟩,
        ⟨78508, false, false, [2373], []⟩,
        ⟨78513, false, false, [], []⟩,
        ⟨78514, false, false, [], []⟩,
        ⟨78516, false, false, [2373], []⟩,
        ⟨5664, true, false, [], [93287]⟩
      ]⟩,
    ⟨[29953, 83621], [29953, 83621], .contexts []⟩,
    ⟨[29953, 83621], [29953, 83621], .contexts []⟩,
    ⟨[29961], [29953, 20717], .source 15045⟩,
    ⟨[93287, 7], [93287, 7], .contexts []⟩,
    ⟨[29961], [29961], .contexts [
        ⟨13, false, false, [], [29961]⟩
      ]⟩,
    ⟨[93287, 7], [29961, 83233], .contexts [
        ⟨78521, false, false, [], []⟩,
        ⟨78512, true, false, [], [7]⟩,
        ⟨647, false, false, [93285], []⟩,
        ⟨648, false, false, [93285], []⟩,
        ⟨78500, false, false, [], [11]⟩,
        ⟨78501, false, false, [], [11]⟩,
        ⟨78518, false, false, [], [11]⟩,
        ⟨78519, false, false, [], [11]⟩,
        ⟨78519, false, false, [], [11]⟩,
        ⟨42898, false, false, [29953], []⟩,
        ⟨78520, true, false, [], [83233]⟩,
        ⟨42904, false, false, [29961], []⟩,
        ⟨78522, true, false, [], [83233]⟩
      ]⟩,
    ⟨[29963], [29960], .source 15046⟩,
    ⟨[93289], [93287, 1], .source 46709⟩,
    ⟨[93287, 1], [93289], .contexts [
        ⟨78525, true, false, [], []⟩
      ]⟩,
    ⟨[93289, 1], [93287], .contexts [
        ⟨78526, true, false, [], [1]⟩,
        ⟨8, false, false, [93287], []⟩,
        ⟨78511, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1227. -/
def y322TCIndexRaw1227 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93289], [93289], .contexts []⟩,
    ⟨[93289], [93289], .contexts []⟩,
    ⟨[93287, 1], [93289], .contexts [
        ⟨78526, false, false, [], []⟩,
        ⟨78528, false, false, [], []⟩,
        ⟨78529, false, false, [], []⟩,
        ⟨78529, false, false, [], []⟩
      ]⟩,
    ⟨[2373, 93289], [2373, 93289], .contexts []⟩,
    ⟨[2373, 93289], [2373, 93289], .contexts []⟩,
    ⟨[93289, 5], [93289, 5], .contexts []⟩,
    ⟨[93289], [93289], .contexts []⟩,
    ⟨[93289, 5], [2373, 93289], .contexts [
        ⟨78533, false, false, [], []⟩,
        ⟨78530, true, false, [], [5]⟩,
        ⟨98, false, false, [93287], []⟩,
        ⟨99, false, false, [93287], []⟩,
        ⟨78515, false, false, [], [1]⟩,
        ⟨78517, false, false, [], [1]⟩,
        ⟨78513, false, false, [], [1]⟩,
        ⟨78514, false, false, [], [1]⟩,
        ⟨78514, false, false, [], [1]⟩,
        ⟨78526, false, false, [2373], []⟩,
        ⟨78531, false, false, [], []⟩,
        ⟨78532, false, false, [], []⟩,
        ⟨78534, false, false, [2373], []⟩,
        ⟨5664, true, false, [], [93289]⟩
      ]⟩,
    ⟨[29961, 83233], [29961, 83233], .contexts []⟩,
    ⟨[29961, 83233], [29961, 83233], .contexts []⟩,
    ⟨[93287, 7], [29961, 83233], .contexts [
        ⟨78521, false, false, [], []⟩,
        ⟨78523, false, false, [], []⟩,
        ⟨78536, false, false, [], []⟩,
        ⟨78537, false, false, [], []⟩,
        ⟨78537, false, false, [], []⟩
      ]⟩,
    ⟨[29961, 83231], [29961, 83231], .contexts []⟩,
    ⟨[29961, 83231], [29961, 83231], .contexts []⟩,
    ⟨[93289, 7], [93289, 7], .contexts []⟩,
    ⟨[93289, 7], [29961, 83231], .contexts [
        ⟨78541, false, false, [], []⟩,
        ⟨78530, true, false, [], [7]⟩,
        ⟨104, false, false, [93287], []⟩,
        ⟨105, false, false, [93287], []⟩,
        ⟨78538, false, false, [], [1]⟩,
        ⟨20183, false, false, [29961], []⟩,
        ⟨78539, false, false, [], []⟩,
        ⟨78540, false, false, [], []⟩,
        ⟨20178, false, false, [29961], []⟩,
        ⟨78522, true, false, [], [83231]⟩
      ]⟩,
    ⟨[83231, 7], [29963, 93289], .contexts [
        ⟨78542, true, false, [29960], [7]⟩,
        ⟨38, false, false, [29960, 93289], []⟩,
        ⟨78524, true, false, [], [93289]⟩
      ]⟩,
    ⟨[93289, 7], [29961, 83231], .contexts [
        ⟨78541, false, false, [], []⟩,
        ⟨78542, false, false, [], []⟩,
        ⟨78539, false, false, [], []⟩,
        ⟨78540, false, false, [], []⟩,
        ⟨78540, false, false, [], []⟩
      ]⟩,
    ⟨[29965], [29961, 16343], .source 15047⟩,
    ⟨[29967], [29965, 29963], .source 15048⟩,
    ⟨[93289], [93289], .contexts []⟩,
    ⟨[93289, 3], [93289, 3], .contexts []⟩,
    ⟨[29969], [29966], .source 15049⟩,
    ⟨[29966], [29966], .contexts []⟩,
    ⟨[93289, 3], [29969, 93289], .contexts [
        ⟨78548, false, false, [], []⟩,
        ⟨78546, false, false, [29966], [93289, 3]⟩,
        ⟨78543, true, false, [29966, 29965], [3]⟩,
        ⟨78545, false, false, [29966], [83231, 7, 3]⟩,
        ⟨21580, true, false, [29966, 29961], [7, 3]⟩,
        ⟨78544, true, false, [29966], [3, 7, 3]⟩,
        ⟨40656, false, false, [29966, 93289], []⟩,
        ⟨78547, false, false, [29966], []⟩,
        ⟨78534, false, false, [29966], []⟩,
        ⟨78550, true, false, [], [93289]⟩,
        ⟨78550, true, false, [], [93289]⟩,
        ⟨78549, true, false, [], [93289]⟩
      ]⟩,
    ⟨[29971], [29961, 15817], .source 15050⟩,
    ⟨[29973], [29971, 29963], .source 15051⟩,
    ⟨[29975], [29972], .source 15052⟩,
    ⟨[29972], [29972], .contexts []⟩,
    ⟨[93291], [93289, 13], .source 46710⟩,
    ⟨[93289, 13], [93291], .contexts [
        ⟨78556, true, false, [], []⟩
      ]⟩,
    ⟨[93291, 13], [93289], .contexts [
        ⟨78557, true, false, [], [13]⟩,
        ⟨59, false, false, [93289], []⟩,
        ⟨78529, false, false, [], []⟩
      ]⟩,
    ⟨[93289, 13], [93291], .contexts [
        ⟨78557, false, false, [], []⟩
      ]⟩,
    ⟨[93291], [93291], .contexts []⟩,
    ⟨[93291], [93291], .contexts []⟩,
    ⟨[93289, 13], [93291], .contexts [
        ⟨78559, false, false, [], []⟩,
        ⟨78560, false, false, [], []⟩,
        ⟨78561, false, false, [], []⟩,
        ⟨78561, false, false, [], []⟩
      ]⟩,
    ⟨[93289, 3], [29969, 93289], .contexts [
        ⟨78551, false, false, [], []⟩
      ]⟩,
    ⟨[29969, 93289], [29969, 93289], .contexts []⟩,
    ⟨[29969, 93289], [29969, 93289], .contexts []⟩,
    ⟨[29969, 93291], [29969, 93291], .contexts []⟩,
    ⟨[29969, 93291], [29969, 93291], .contexts []⟩,
    ⟨[29969, 93291], [29969, 93291], .contexts []⟩,
    ⟨[93291, 3], [93291, 3], .contexts []⟩,
    ⟨[93291], [93291], .contexts []⟩,
    ⟨[29969], [29969], .contexts [
        ⟨13, false, false, [], [29969]⟩
      ]⟩,
    ⟨[2373, 93291], [2373, 93291], .contexts []⟩,
    ⟨[2373, 93291], [2373, 93291], .contexts []⟩,
    ⟨[93291, 5], [93291, 5], .contexts []⟩,
    ⟨[93293], [93291, 15], .source 46711⟩,
    ⟨[93291, 15], [93293], .contexts [
        ⟨78575, true, false, [], []⟩
      ]⟩,
    ⟨[93291, 15], [93293], .contexts [
        ⟨78576, false, false, [], []⟩
      ]⟩,
    ⟨[93293], [93293], .contexts []⟩,
    ⟨[93293], [93293], .contexts []⟩,
    ⟨[93291, 15], [93293], .contexts [
        ⟨78577, false, false, [], []⟩,
        ⟨78578, false, false, [], []⟩,
        ⟨78579, false, false, [], []⟩,
        ⟨78579, false, false, [], []⟩
      ]⟩,
    ⟨[29969, 93293], [29969, 93293], .contexts []⟩,
    ⟨[29969, 93293], [29969, 93293], .contexts []⟩,
    ⟨[29969, 93293], [29969, 93293], .contexts []⟩,
    ⟨[93291, 3, 15], [29969, 93293], .contexts [
        ⟨78569, false, false, [], [15]⟩,
        ⟨78569, false, false, [], [15]⟩,
        ⟨78562, true, false, [], [3, 15]⟩,
        ⟨63, false, false, [93289], [15]⟩,
        ⟨65, false, false, [93289], [15]⟩,
        ⟨78548, false, false, [], [13, 15]⟩,
        ⟨78563, false, false, [], [13, 15]⟩,
        ⟨78564, false, false, [], [13, 15]⟩,
        ⟨78565, false, false, [], [13, 15]⟩,
        ⟨78565, false, false, [], [13, 15]⟩,
        ⟨78557, false, false, [29969], [15]⟩,
        ⟨78566, false, false, [], [15]⟩,
        ⟨78567, false, false, [], [15]⟩,
        ⟨78568, false, false, [], [15]⟩,
        ⟨78570, false, false, [29969], [15]⟩,
        ⟨78571, true, false, [], [93291, 15]⟩,
        ⟨78566, false, false, [], [15]⟩,
        ⟨78568, false, false, [], [15]⟩,
        ⟨78568, false, false, [], [15]⟩,
        ⟨78576, false, false, [29969], []⟩,
        ⟨78581, false, false, [], []⟩,
        ⟨78582, false, false, [], []⟩,
        ⟨78583, false, false, [], []⟩
      ]⟩,
    ⟨[93293], [93293], .contexts []⟩,
    ⟨[2373, 93293], [2373, 93293], .contexts []⟩,
    ⟨[93291, 5, 15], [2373, 93293], .contexts [
        ⟨78574, false, false, [], [15]⟩,
        ⟨78574, false, false, [], [15]⟩,
        ⟨78562, true, false, [], [5, 15]⟩,
        ⟨68, false, false, [93289], [15]⟩,
        ⟨69, false, false, [93289], [15]⟩,
        ⟨78533, false, false, [], [13, 15]⟩,
        ⟨78535, false, false, [], [13, 15]⟩,
        ⟨78531, false, false, [], [13, 15]⟩,
        ⟨78532, false, false, [], [13, 15]⟩,
        ⟨78532, false, false, [], [13, 15]⟩,
        ⟨78557, false, false, [2373], [15]⟩,
        ⟨78572, false, false, [], [15]⟩,
        ⟨78573, false, false, [], [15]⟩,
        ⟨78570, false, false, [2373], [15]⟩,
        ⟨5664, true, false, [], [93291, 15]⟩,
        ⟨78572, false, false, [], [15]⟩,
        ⟨78573, false, false, [], [15]⟩,
        ⟨78573, false, false, [], [15]⟩,
        ⟨78576, false, false, [2373], []⟩,
        ⟨78586, false, false, [], []⟩
      ]⟩,
    ⟨[2373, 93293], [2373, 93293], .contexts []⟩,
    ⟨[93293, 5], [93293, 5], .contexts []⟩,
    ⟨[93295], [93293, 1], .source 46712⟩,
    ⟨[93293, 1], [93295], .contexts [
        ⟨78590, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1228. -/
def y322TCIndexRaw1228 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93295, 1], [93293], .contexts [
        ⟨78591, true, false, [], [1]⟩,
        ⟨8, false, false, [93293], []⟩,
        ⟨78579, false, false, [], []⟩
      ]⟩,
    ⟨[93295], [93295], .contexts []⟩,
    ⟨[93295], [93295], .contexts []⟩,
    ⟨[2373, 93295], [2373, 93295], .contexts []⟩,
    ⟨[2373, 93295], [2373, 93295], .contexts []⟩,
    ⟨[93295], [93295], .contexts []⟩,
    ⟨[93295, 5], [2373, 93295], .contexts [
        ⟨78594, true, false, [], [5]⟩,
        ⟨78594, true, false, [], [5]⟩,
        ⟨78593, true, false, [], [5]⟩,
        ⟨78591, true, false, [], [5]⟩,
        ⟨98, false, false, [93293], []⟩,
        ⟨99, false, false, [93293], []⟩,
        ⟨78589, false, false, [], [1]⟩,
        ⟨78589, false, false, [], [1]⟩,
        ⟨78580, true, false, [], [5, 1]⟩,
        ⟨27, false, false, [93291], [1]⟩,
        ⟨30, false, false, [93291], [1]⟩,
        ⟨78587, false, false, [], [1]⟩,
        ⟨78588, false, false, [], [1]⟩,
        ⟨78585, false, false, [2373], [1]⟩,
        ⟨5664, true, false, [], [93293, 1]⟩,
        ⟨78586, false, false, [], [1]⟩,
        ⟨78588, false, false, [], [1]⟩,
        ⟨78588, false, false, [], [1]⟩,
        ⟨78591, false, false, [2373], []⟩,
        ⟨78595, false, false, [], []⟩,
        ⟨78596, false, false, [], []⟩,
        ⟨78597, false, false, [2373], []⟩
      ]⟩,
    ⟨[93297], [93295, 3], .source 46713⟩,
    ⟨[93295, 3], [93297], .contexts [
        ⟨78599, true, false, [], []⟩
      ]⟩,
    ⟨[93297, 3], [93295], .contexts [
        ⟨78600, true, false, [], [3]⟩,
        ⟨20, false, false, [93295], []⟩,
        ⟨78594, false, false, [], []⟩
      ]⟩,
    ⟨[93297], [93297], .contexts []⟩,
    ⟨[93297], [93297], .contexts []⟩,
    ⟨[93295, 3], [93297], .contexts [
        ⟨78600, false, false, [], []⟩,
        ⟨78602, false, false, [], []⟩,
        ⟨78603, false, false, [], []⟩,
        ⟨78603, false, false, [], []⟩
      ]⟩,
    ⟨[29969, 93295], [29969, 93295], .contexts []⟩,
    ⟨[29969, 93295], [29969, 93295], .contexts []⟩,
    ⟨[29969, 93295], [29969, 93295], .contexts []⟩,
    ⟨[29969, 93297], [29969, 93297], .contexts []⟩,
    ⟨[29969, 93297], [29969, 93297], .contexts []⟩,
    ⟨[29969, 93297], [29969, 93297], .contexts []⟩,
    ⟨[93295, 1, 3, 1, 3], [29969, 93297], .contexts [
        ⟨78592, false, false, [], [3, 1, 3]⟩,
        ⟨78578, false, false, [], [3, 1, 3]⟩,
        ⟨78579, false, false, [], [3, 1, 3]⟩,
        ⟨78579, false, false, [], [3, 1, 3]⟩,
        ⟨78580, true, false, [], [3, 1, 3]⟩,
        ⟨19, false, false, [93291], [1, 3]⟩,
        ⟨22, false, false, [93291], [1, 3]⟩,
        ⟨78584, false, false, [], [1, 3]⟩,
        ⟨78585, false, false, [29969], [1, 3]⟩,
        ⟨78571, true, false, [], [93293, 1, 3]⟩,
        ⟨78581, false, false, [], [1, 3]⟩,
        ⟨78583, false, false, [], [1, 3]⟩,
        ⟨78583, false, false, [], [1, 3]⟩,
        ⟨78591, false, false, [29969], [3]⟩,
        ⟨78605, false, false, [], [3]⟩,
        ⟨78606, false, false, [], [3]⟩,
        ⟨78607, false, false, [], [3]⟩,
        ⟨78600, false, false, [29969], []⟩,
        ⟨78608, false, false, [], []⟩,
        ⟨78609, false, false, [], []⟩,
        ⟨78610, false, false, [], []⟩
      ]⟩,
    ⟨[93297, 1], [93297, 1], .contexts []⟩,
    ⟨[93297], [93297], .contexts []⟩,
    ⟨[93297, 1], [29969, 93297], .contexts [
        ⟨78612, false, false, [], []⟩,
        ⟨78604, true, false, [], [1]⟩,
        ⟨130, false, false, [93295], []⟩,
        ⟨133, false, false, [93295], []⟩,
        ⟨78611, false, false, [], []⟩,
        ⟨78613, false, false, [29969], []⟩,
        ⟨78571, true, false, [], [93297]⟩
      ]⟩,
    ⟨[93299], [93297, 5], .source 46714⟩,
    ⟨[93297, 5], [93299], .contexts [
        ⟨78615, true, false, [], []⟩
      ]⟩,
    ⟨[93299, 5], [93297], .contexts [
        ⟨78616, true, false, [], [5]⟩,
        ⟨28, false, false, [93297], []⟩,
        ⟨78603, false, false, [], []⟩
      ]⟩,
    ⟨[93299], [93299], .contexts []⟩,
    ⟨[93299], [93299], .contexts []⟩,
    ⟨[93297, 5], [93299], .contexts [
        ⟨78616, false, false, [], []⟩,
        ⟨78618, false, false, [], []⟩,
        ⟨78619, false, false, [], []⟩,
        ⟨78619, false, false, [], []⟩
      ]⟩,
    ⟨[29969, 93299], [29969, 93299], .contexts []⟩,
    ⟨[29969, 93299], [29969, 93299], .contexts []⟩,
    ⟨[93299], [93299], .contexts []⟩,
    ⟨[93299, 1], [29969, 93299], .contexts [
        ⟨78620, true, false, [], [1]⟩,
        ⟨161, false, false, [93297], []⟩,
        ⟨162, false, false, [93297], []⟩,
        ⟨78612, false, false, [], [5]⟩,
        ⟨78614, false, false, [], [5]⟩,
        ⟨78608, false, false, [], [5]⟩,
        ⟨78610, false, false, [], [5]⟩,
        ⟨78610, false, false, [], [5]⟩,
        ⟨78616, false, false, [29969], []⟩,
        ⟨78621, false, false, [], []⟩,
        ⟨78622, false, false, [], []⟩,
        ⟨78623, false, false, [29969], []⟩,
        ⟨78571, true, false, [], [93299]⟩
      ]⟩,
    ⟨[2373, 93299], [2373, 93299], .contexts []⟩,
    ⟨[93299, 3], [2373, 93299], .contexts [
        ⟨78620, true, false, [], [3]⟩,
        ⟨166, false, false, [93297], []⟩,
        ⟨169, false, false, [93297], []⟩,
        ⟨78601, false, false, [], [5, 3, 5]⟩,
        ⟨78593, false, false, [], [5, 3, 5]⟩,
        ⟨78594, false, false, [], [5, 3, 5]⟩,
        ⟨78594, false, false, [], [5, 3, 5]⟩,
        ⟨78598, false, false, [], [3, 5]⟩,
        ⟨5664, true, false, [], [93295, 3, 5]⟩,
        ⟨78595, false, false, [], [3, 5]⟩,
        ⟨78596, false, false, [], [3, 5]⟩,
        ⟨78596, false, false, [], [3, 5]⟩,
        ⟨78600, false, false, [2373], [5]⟩,
        ⟨78616, false, false, [2373], []⟩,
        ⟨78625, false, false, [], []⟩,
        ⟨78623, false, false, [2373], []⟩
      ]⟩,
    ⟨[93301], [93299, 9], .source 46715⟩,
    ⟨[93299, 9], [93301], .contexts [
        ⟨78627, true, false, [], []⟩
      ]⟩,
    ⟨[93301, 9], [93299], .contexts [
        ⟨78628, true, false, [], [9]⟩,
        ⟨46, false, false, [93299], []⟩,
        ⟨78619, false, false, [], []⟩
      ]⟩,
    ⟨[93301], [93301], .contexts []⟩,
    ⟨[93301], [93301], .contexts []⟩,
    ⟨[93303], [93301, 11], .source 46716⟩,
    ⟨[93301, 11], [93303], .contexts [
        ⟨78632, true, false, [], []⟩
      ]⟩,
    ⟨[93303], [93303], .contexts []⟩,
    ⟨[93303], [93303], .contexts []⟩,
    ⟨[93305], [93303, 1], .source 46717⟩,
    ⟨[93303, 1], [93305], .contexts [
        ⟨78636, true, false, [], []⟩
      ]⟩,
    ⟨[93307], [93305, 13], .source 46718⟩,
    ⟨[93305, 13], [93307], .contexts [
        ⟨78638, true, false, [], []⟩
      ]⟩,
    ⟨[93305], [93305], .contexts []⟩,
    ⟨[93307, 13], [93305], .contexts [
        ⟨78639, true, false, [], [13]⟩,
        ⟨59, false, false, [93305], []⟩,
        ⟨78640, false, false, [], []⟩
      ]⟩,
    ⟨[93309], [93307, 15], .source 46719⟩,
    ⟨[93307, 15], [93309], .contexts [
        ⟨78642, true, false, [], []⟩
      ]⟩,
    ⟨[93307], [93307], .contexts []⟩,
    ⟨[93309, 15], [93307], .contexts [
        ⟨78643, true, false, [], [15]⟩,
        ⟨1, false, false, [93307], []⟩,
        ⟨78644, false, false, [], []⟩
      ]⟩,
    ⟨[93311], [93309, 1], .source 46720⟩,
    ⟨[93309, 1], [93311], .contexts [
        ⟨78646, true, false, [], []⟩
      ]⟩,
    ⟨[93309], [93309], .contexts []⟩,
    ⟨[93311, 1], [93309], .contexts [
        ⟨78647, true, false, [], [1]⟩,
        ⟨8, false, false, [93309], []⟩,
        ⟨78648, false, false, [], []⟩
      ]⟩,
    ⟨[93313], [93311, 3], .source 46721⟩,
    ⟨[93311, 3], [93313], .contexts [
        ⟨78650, true, false, [], []⟩
      ]⟩,
    ⟨[93311], [93311], .contexts []⟩,
    ⟨[93313, 3], [93311], .contexts [
        ⟨78651, true, false, [], [3]⟩,
        ⟨20, false, false, [93311], []⟩,
        ⟨78652, false, false, [], []⟩
      ]⟩,
    ⟨[93315], [93313, 5], .source 46722⟩,
    ⟨[93313, 5], [93315], .contexts [
        ⟨78654, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1229. -/
def y322TCIndexRaw1229 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93313], [93313], .contexts []⟩,
    ⟨[93315, 5], [93313], .contexts [
        ⟨78655, true, false, [], [5]⟩,
        ⟨28, false, false, [93313], []⟩,
        ⟨78656, false, false, [], []⟩
      ]⟩,
    ⟨[93317], [93315, 1], .source 46723⟩,
    ⟨[93315], [93315], .contexts []⟩,
    ⟨[93317, 1], [93315], .contexts [
        ⟨78658, false, false, [], [1]⟩,
        ⟨8, false, false, [93315], []⟩,
        ⟨78659, false, false, [], []⟩
      ]⟩,
    ⟨[93319], [93317, 9], .source 46724⟩,
    ⟨[93317], [93317], .contexts []⟩,
    ⟨[93319, 9], [93317], .contexts [
        ⟨78661, false, false, [], [9]⟩,
        ⟨46, false, false, [93317], []⟩,
        ⟨78662, false, false, [], []⟩
      ]⟩,
    ⟨[93321], [93319, 11], .source 46725⟩,
    ⟨[93319, 11], [93321], .contexts [
        ⟨78664, true, false, [], []⟩
      ]⟩,
    ⟨[93319], [93319], .contexts []⟩,
    ⟨[93321, 11], [93319], .contexts [
        ⟨78665, true, false, [], [11]⟩,
        ⟨53, false, false, [93319], []⟩,
        ⟨78666, false, false, [], []⟩
      ]⟩,
    ⟨[93323], [93321, 1], .source 46726⟩,
    ⟨[93321, 1], [93323], .contexts [
        ⟨78668, true, false, [], []⟩
      ]⟩,
    ⟨[93321], [93321], .contexts []⟩,
    ⟨[93323, 1], [93321], .contexts [
        ⟨78669, true, false, [], [1]⟩,
        ⟨8, false, false, [93321], []⟩,
        ⟨78670, false, false, [], []⟩
      ]⟩,
    ⟨[93325], [93323, 13], .source 46727⟩,
    ⟨[93323, 13], [93325], .contexts [
        ⟨78672, true, false, [], []⟩
      ]⟩,
    ⟨[93323], [93323], .contexts []⟩,
    ⟨[93325, 13], [93323], .contexts [
        ⟨78673, true, false, [], [13]⟩,
        ⟨59, false, false, [93323], []⟩,
        ⟨78674, false, false, [], []⟩
      ]⟩,
    ⟨[93327], [93325, 15], .source 46728⟩,
    ⟨[93325], [93325], .contexts []⟩,
    ⟨[93327, 15], [93325], .contexts [
        ⟨78676, false, false, [], [15]⟩,
        ⟨1, false, false, [93325], []⟩,
        ⟨78677, false, false, [], []⟩
      ]⟩,
    ⟨[93329], [93327, 1], .source 46729⟩,
    ⟨[93327], [93327], .contexts []⟩,
    ⟨[93329, 1], [93327], .contexts [
        ⟨78679, false, false, [], [1]⟩,
        ⟨8, false, false, [93327], []⟩,
        ⟨78680, false, false, [], []⟩
      ]⟩,
    ⟨[93331], [93329, 3], .source 46730⟩,
    ⟨[93329, 3], [93331], .contexts [
        ⟨78682, true, false, [], []⟩
      ]⟩,
    ⟨[93329], [93329], .contexts []⟩,
    ⟨[93331, 3], [93329], .contexts [
        ⟨78683, true, false, [], [3]⟩,
        ⟨20, false, false, [93329], []⟩,
        ⟨78684, false, false, [], []⟩
      ]⟩,
    ⟨[93333], [93331, 5], .source 46731⟩,
    ⟨[93331, 5], [93333], .contexts [
        ⟨78686, true, false, [], []⟩
      ]⟩,
    ⟨[93331], [93331], .contexts []⟩,
    ⟨[93333, 5], [93331], .contexts [
        ⟨78687, true, false, [], [5]⟩,
        ⟨28, false, false, [93331], []⟩,
        ⟨78688, false, false, [], []⟩
      ]⟩,
    ⟨[93335], [93333, 1], .source 46732⟩,
    ⟨[93333], [93333], .contexts []⟩,
    ⟨[93335, 1], [93333], .contexts [
        ⟨78690, false, false, [], [1]⟩,
        ⟨8, false, false, [93333], []⟩,
        ⟨78691, false, false, [], []⟩
      ]⟩,
    ⟨[93337], [93335, 9], .source 46733⟩,
    ⟨[93335], [93335], .contexts []⟩,
    ⟨[93337, 9], [93335], .contexts [
        ⟨78693, false, false, [], [9]⟩,
        ⟨46, false, false, [93335], []⟩,
        ⟨78694, false, false, [], []⟩
      ]⟩,
    ⟨[93339], [93337, 11], .source 46734⟩,
    ⟨[93337], [93337], .contexts []⟩,
    ⟨[93339, 11], [93337], .contexts [
        ⟨78696, false, false, [], [11]⟩,
        ⟨53, false, false, [93337], []⟩,
        ⟨78697, false, false, [], []⟩
      ]⟩,
    ⟨[93341], [93339, 1], .source 46735⟩,
    ⟨[93339], [93339], .contexts []⟩,
    ⟨[93341, 1], [93339], .contexts [
        ⟨78699, false, false, [], [1]⟩,
        ⟨8, false, false, [93339], []⟩,
        ⟨78700, false, false, [], []⟩
      ]⟩,
    ⟨[93343], [93341, 13], .source 46736⟩,
    ⟨[93341], [93341], .contexts []⟩,
    ⟨[93343, 13], [93341], .contexts [
        ⟨78702, false, false, [], [13]⟩,
        ⟨59, false, false, [93341], []⟩,
        ⟨78703, false, false, [], []⟩
      ]⟩,
    ⟨[93345], [93343, 15], .source 46737⟩,
    ⟨[93343], [93343], .contexts []⟩,
    ⟨[93345, 15], [93343], .contexts [
        ⟨78705, false, false, [], [15]⟩,
        ⟨1, false, false, [93343], []⟩,
        ⟨78706, false, false, [], []⟩
      ]⟩,
    ⟨[93347], [93345, 1], .source 46738⟩,
    ⟨[93345], [93345], .contexts []⟩,
    ⟨[93347, 1], [93345], .contexts [
        ⟨78708, false, false, [], [1]⟩,
        ⟨8, false, false, [93345], []⟩,
        ⟨78709, false, false, [], []⟩
      ]⟩,
    ⟨[93349], [93347, 3], .source 46739⟩,
    ⟨[93347], [93347], .contexts []⟩,
    ⟨[93349, 3], [93347], .contexts [
        ⟨78711, false, false, [], [3]⟩,
        ⟨20, false, false, [93347], []⟩,
        ⟨78712, false, false, [], []⟩
      ]⟩,
    ⟨[93351], [93349, 5], .source 46740⟩,
    ⟨[93349], [93349], .contexts []⟩,
    ⟨[93351, 5], [93349], .contexts [
        ⟨78714, false, false, [], [5]⟩,
        ⟨28, false, false, [93349], []⟩,
        ⟨78715, false, false, [], []⟩
      ]⟩,
    ⟨[93353], [93351, 1], .source 46741⟩,
    ⟨[93351], [93351], .contexts []⟩,
    ⟨[93353, 1], [93351], .contexts [
        ⟨78717, false, false, [], [1]⟩,
        ⟨8, false, false, [93351], []⟩,
        ⟨78718, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1230. -/
def y322TCIndexRaw1230 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93355], [93353, 9], .source 46742⟩,
    ⟨[93353], [93353], .contexts []⟩,
    ⟨[93355, 9], [93353], .contexts [
        ⟨78720, false, false, [], [9]⟩,
        ⟨46, false, false, [93353], []⟩,
        ⟨78721, false, false, [], []⟩
      ]⟩,
    ⟨[93357], [93355, 11], .source 46743⟩,
    ⟨[93355], [93355], .contexts []⟩,
    ⟨[93357, 11], [93355], .contexts [
        ⟨78723, false, false, [], [11]⟩,
        ⟨53, false, false, [93355], []⟩,
        ⟨78724, false, false, [], []⟩
      ]⟩,
    ⟨[93359], [93357, 1], .source 46744⟩,
    ⟨[93357], [93357], .contexts []⟩,
    ⟨[93359, 1], [93357], .contexts [
        ⟨78726, false, false, [], [1]⟩,
        ⟨8, false, false, [93357], []⟩,
        ⟨78727, false, false, [], []⟩
      ]⟩,
    ⟨[93361], [93359, 13], .source 46745⟩,
    ⟨[93359], [93359], .contexts []⟩,
    ⟨[93361, 13], [93359], .contexts [
        ⟨78729, false, false, [], [13]⟩,
        ⟨59, false, false, [93359], []⟩,
        ⟨78730, false, false, [], []⟩
      ]⟩,
    ⟨[93363], [93361, 15], .source 46746⟩,
    ⟨[93361], [93361], .contexts []⟩,
    ⟨[93363, 15], [93361], .contexts [
        ⟨78732, false, false, [], [15]⟩,
        ⟨1, false, false, [93361], []⟩,
        ⟨78733, false, false, [], []⟩
      ]⟩,
    ⟨[93365], [93363, 1], .source 46747⟩,
    ⟨[93363], [93363], .contexts []⟩,
    ⟨[93365, 1], [93363], .contexts [
        ⟨78735, false, false, [], [1]⟩,
        ⟨8, false, false, [93363], []⟩,
        ⟨78736, false, false, [], []⟩
      ]⟩,
    ⟨[93367], [93365, 3], .source 46748⟩,
    ⟨[93365], [93365], .contexts []⟩,
    ⟨[93367, 3], [93365], .contexts [
        ⟨78738, false, false, [], [3]⟩,
        ⟨20, false, false, [93365], []⟩,
        ⟨78739, false, false, [], []⟩
      ]⟩,
    ⟨[93369], [93367, 5], .source 46749⟩,
    ⟨[93367, 5], [93369], .contexts [
        ⟨78741, true, false, [], []⟩
      ]⟩,
    ⟨[93367], [93367], .contexts []⟩,
    ⟨[93369, 5], [93367], .contexts [
        ⟨78742, true, false, [], [5]⟩,
        ⟨28, false, false, [93367], []⟩,
        ⟨78743, false, false, [], []⟩
      ]⟩,
    ⟨[93371], [93369, 1], .source 46750⟩,
    ⟨[93369], [93369], .contexts []⟩,
    ⟨[93371, 1], [93369], .contexts [
        ⟨78745, false, false, [], [1]⟩,
        ⟨8, false, false, [93369], []⟩,
        ⟨78746, false, false, [], []⟩
      ]⟩,
    ⟨[93373], [93371, 9], .source 46751⟩,
    ⟨[93371], [93371], .contexts []⟩,
    ⟨[93373, 9], [93371], .contexts [
        ⟨78748, false, false, [], [9]⟩,
        ⟨46, false, false, [93371], []⟩,
        ⟨78749, false, false, [], []⟩
      ]⟩,
    ⟨[93375], [93373, 11], .source 46752⟩,
    ⟨[93373, 11], [93375], .contexts [
        ⟨78751, true, false, [], []⟩
      ]⟩,
    ⟨[93373], [93373], .contexts []⟩,
    ⟨[93375, 11], [93373], .contexts [
        ⟨78752, true, false, [], [11]⟩,
        ⟨53, false, false, [93373], []⟩,
        ⟨78753, false, false, [], []⟩
      ]⟩,
    ⟨[93377], [93375, 1], .source 46753⟩,
    ⟨[93375, 1], [93377], .contexts [
        ⟨78755, true, false, [], []⟩
      ]⟩,
    ⟨[93375], [93375], .contexts []⟩,
    ⟨[93377, 1], [93375], .contexts [
        ⟨78756, true, false, [], [1]⟩,
        ⟨8, false, false, [93375], []⟩,
        ⟨78757, false, false, [], []⟩
      ]⟩,
    ⟨[93379], [93377, 13], .source 46754⟩,
    ⟨[93377, 13], [93379], .contexts [
        ⟨78759, true, false, [], []⟩
      ]⟩,
    ⟨[93377], [93377], .contexts []⟩,
    ⟨[93379, 13], [93377], .contexts [
        ⟨78760, true, false, [], [13]⟩,
        ⟨59, false, false, [93377], []⟩,
        ⟨78761, false, false, [], []⟩
      ]⟩,
    ⟨[93381], [93379, 15], .source 46755⟩,
    ⟨[93379], [93379], .contexts []⟩,
    ⟨[93381, 15], [93379], .contexts [
        ⟨78763, false, false, [], [15]⟩,
        ⟨1, false, false, [93379], []⟩,
        ⟨78764, false, false, [], []⟩
      ]⟩,
    ⟨[93383], [93381, 1], .source 46756⟩,
    ⟨[93381], [93381], .contexts []⟩,
    ⟨[93383, 1], [93381], .contexts [
        ⟨78766, false, false, [], [1]⟩,
        ⟨8, false, false, [93381], []⟩,
        ⟨78767, false, false, [], []⟩
      ]⟩,
    ⟨[93385], [93383, 3], .source 46757⟩,
    ⟨[93383], [93383], .contexts []⟩,
    ⟨[93385, 3], [93383], .contexts [
        ⟨78769, false, false, [], [3]⟩,
        ⟨20, false, false, [93383], []⟩,
        ⟨78770, false, false, [], []⟩
      ]⟩,
    ⟨[93387], [93385, 5], .source 46758⟩,
    ⟨[93385], [93385], .contexts []⟩,
    ⟨[93387, 5], [93385], .contexts [
        ⟨78772, false, false, [], [5]⟩,
        ⟨28, false, false, [93385], []⟩,
        ⟨78773, false, false, [], []⟩
      ]⟩,
    ⟨[93389], [93387, 1], .source 46759⟩,
    ⟨[93387], [93387], .contexts []⟩,
    ⟨[93389, 1], [93387], .contexts [
        ⟨78775, false, false, [], [1]⟩,
        ⟨8, false, false, [93387], []⟩,
        ⟨78776, false, false, [], []⟩
      ]⟩,
    ⟨[93391], [93389, 9], .source 46760⟩,
    ⟨[93389], [93389], .contexts []⟩,
    ⟨[93391, 9], [93389], .contexts [
        ⟨78778, false, false, [], [9]⟩,
        ⟨46, false, false, [93389], []⟩,
        ⟨78779, false, false, [], []⟩
      ]⟩,
    ⟨[93393], [93391, 11], .source 46761⟩,
    ⟨[93391], [93391], .contexts []⟩,
    ⟨[93393, 11], [93391], .contexts [
        ⟨78781, false, false, [], [11]⟩,
        ⟨53, false, false, [93391], []⟩,
        ⟨78782, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1231. -/
def y322TCIndexRaw1231 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93395], [93393, 1], .source 46762⟩,
    ⟨[93393, 1], [93395], .contexts [
        ⟨78784, true, false, [], []⟩
      ]⟩,
    ⟨[93393], [93393], .contexts []⟩,
    ⟨[93395, 1], [93393], .contexts [
        ⟨78785, true, false, [], [1]⟩,
        ⟨8, false, false, [93393], []⟩,
        ⟨78786, false, false, [], []⟩
      ]⟩,
    ⟨[93397], [93395, 13], .source 46763⟩,
    ⟨[93395, 13], [93397], .contexts [
        ⟨78788, true, false, [], []⟩
      ]⟩,
    ⟨[93395], [93395], .contexts []⟩,
    ⟨[93397, 13], [93395], .contexts [
        ⟨78789, true, false, [], [13]⟩,
        ⟨59, false, false, [93395], []⟩,
        ⟨78790, false, false, [], []⟩
      ]⟩,
    ⟨[93399], [93397, 15], .source 46764⟩,
    ⟨[93397, 15], [93399], .contexts [
        ⟨78792, true, false, [], []⟩
      ]⟩,
    ⟨[93397], [93397], .contexts []⟩,
    ⟨[93399, 15], [93397], .contexts [
        ⟨78793, true, false, [], [15]⟩,
        ⟨1, false, false, [93397], []⟩,
        ⟨78794, false, false, [], []⟩
      ]⟩,
    ⟨[93401], [93399, 1], .source 46765⟩,
    ⟨[93399, 1], [93401], .contexts [
        ⟨78796, true, false, [], []⟩
      ]⟩,
    ⟨[93399], [93399], .contexts []⟩,
    ⟨[93401, 1], [93399], .contexts [
        ⟨78797, true, false, [], [1]⟩,
        ⟨8, false, false, [93399], []⟩,
        ⟨78798, false, false, [], []⟩
      ]⟩,
    ⟨[93403], [93401, 3], .source 46766⟩,
    ⟨[93401, 3], [93403], .contexts [
        ⟨78800, true, false, [], []⟩
      ]⟩,
    ⟨[93401], [93401], .contexts []⟩,
    ⟨[93403, 3], [93401], .contexts [
        ⟨78801, true, false, [], [3]⟩,
        ⟨20, false, false, [93401], []⟩,
        ⟨78802, false, false, [], []⟩
      ]⟩,
    ⟨[93405], [93403, 5], .source 46767⟩,
    ⟨[93403], [93403], .contexts []⟩,
    ⟨[93405, 5], [93403], .contexts [
        ⟨78804, false, false, [], [5]⟩,
        ⟨28, false, false, [93403], []⟩,
        ⟨78805, false, false, [], []⟩
      ]⟩,
    ⟨[93407], [93405, 1], .source 46768⟩,
    ⟨[93405], [93405], .contexts []⟩,
    ⟨[93407, 1], [93405], .contexts [
        ⟨78807, false, false, [], [1]⟩,
        ⟨8, false, false, [93405], []⟩,
        ⟨78808, false, false, [], []⟩
      ]⟩,
    ⟨[93409], [93407, 9], .source 46769⟩,
    ⟨[93407, 9], [93409], .contexts [
        ⟨78810, true, false, [], []⟩
      ]⟩,
    ⟨[93407], [93407], .contexts []⟩,
    ⟨[93409, 9], [93407], .contexts [
        ⟨78811, true, false, [], [9]⟩,
        ⟨46, false, false, [93407], []⟩,
        ⟨78812, false, false, [], []⟩
      ]⟩,
    ⟨[93411], [93409, 11], .source 46770⟩,
    ⟨[93409, 11], [93411], .contexts [
        ⟨78814, true, false, [], []⟩
      ]⟩,
    ⟨[93409], [93409], .contexts []⟩,
    ⟨[93411, 11], [93409], .contexts [
        ⟨78815, true, false, [], [11]⟩,
        ⟨53, false, false, [93409], []⟩,
        ⟨78816, false, false, [], []⟩
      ]⟩,
    ⟨[93413], [93411, 1], .source 46771⟩,
    ⟨[93411, 1], [93413], .contexts [
        ⟨78818, true, false, [], []⟩
      ]⟩,
    ⟨[93411], [93411], .contexts []⟩,
    ⟨[93413], [93413], .contexts []⟩,
    ⟨[93409], [93409], .contexts []⟩,
    ⟨[93409, 9], [93407], .contexts [
        ⟨78813, false, false, [], []⟩
      ]⟩,
    ⟨[93407], [93407], .contexts []⟩,
    ⟨[93407, 1], [93405], .contexts [
        ⟨78809, false, false, [], []⟩
      ]⟩,
    ⟨[93405], [93405], .contexts []⟩,
    ⟨[93403], [93403], .contexts []⟩,
    ⟨[93401], [93401], .contexts []⟩,
    ⟨[93411, 11, 9, 1, 5, 3], [93401], .contexts [
        ⟨78817, false, false, [], [9, 1, 5, 3]⟩,
        ⟨78822, false, false, [], [9, 1, 5, 3]⟩,
        ⟨78816, false, false, [], [9, 1, 5, 3]⟩,
        ⟨78816, false, false, [], [9, 1, 5, 3]⟩,
        ⟨78823, false, false, [], [1, 5, 3]⟩,
        ⟨78824, false, false, [], [1, 5, 3]⟩,
        ⟨78812, false, false, [], [1, 5, 3]⟩,
        ⟨78812, false, false, [], [1, 5, 3]⟩,
        ⟨78825, false, false, [], [5, 3]⟩,
        ⟨78826, false, false, [], [5, 3]⟩,
        ⟨78808, false, false, [], [5, 3]⟩,
        ⟨78808, false, false, [], [5, 3]⟩,
        ⟨78806, false, false, [], [3]⟩,
        ⟨78827, false, false, [], [3]⟩,
        ⟨78805, false, false, [], [3]⟩,
        ⟨78805, false, false, [], [3]⟩,
        ⟨78803, false, false, [], []⟩,
        ⟨78828, false, false, [], []⟩,
        ⟨78802, false, false, [], []⟩,
        ⟨78802, false, false, [], []⟩
      ]⟩,
    ⟨[93399], [93399], .contexts []⟩,
    ⟨[93399, 15], [93397], .contexts [
        ⟨78795, false, false, [], []⟩
      ]⟩,
    ⟨[93397], [93397], .contexts []⟩,
    ⟨[93397, 13], [93395], .contexts [
        ⟨78791, false, false, [], []⟩
      ]⟩,
    ⟨[93395], [93395], .contexts []⟩,
    ⟨[93393, 11], [93391], .contexts [
        ⟨78783, false, false, [], []⟩
      ]⟩,
    ⟨[93391], [93391], .contexts []⟩,
    ⟨[93411, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11], [93391], .contexts [
        ⟨78829, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨78799, false, false, [], [15, 13, 1, 11]⟩,
        ⟨78830, false, false, [], [15, 13, 1, 11]⟩,
        ⟨78798, false, false, [], [15, 13, 1, 11]⟩,
        ⟨78798, false, false, [], [15, 13, 1, 11]⟩,
        ⟨78831, false, false, [], [13, 1, 11]⟩,
        ⟨78832, false, false, [], [13, 1, 11]⟩,
        ⟨78794, false, false, [], [13, 1, 11]⟩,
        ⟨78794, false, false, [], [13, 1, 11]⟩,
        ⟨78833, false, false, [], [1, 11]⟩,
        ⟨78834, false, false, [], [1, 11]⟩,
        ⟨78790, false, false, [], [1, 11]⟩,
        ⟨78790, false, false, [], [1, 11]⟩,
        ⟨78787, false, false, [], [11]⟩,
        ⟨78786, false, false, [], [11]⟩,
        ⟨78786, false, false, [], [11]⟩,
        ⟨78835, false, false, [], []⟩,
        ⟨78836, false, false, [], []⟩,
        ⟨78782, false, false, [], []⟩,
        ⟨78782, false, false, [], []⟩
      ]⟩,
    ⟨[93391, 9], [93389], .contexts [
        ⟨78780, false, false, [], []⟩
      ]⟩,
    ⟨[93389], [93389], .contexts []⟩,
    ⟨[93389, 1], [93387], .contexts [
        ⟨78777, false, false, [], []⟩
      ]⟩,
    ⟨[93387], [93387], .contexts []⟩,
    ⟨[93385, 3], [93383], .contexts [
        ⟨78771, false, false, [], []⟩
      ]⟩,
    ⟨[93383], [93383], .contexts []⟩,
    ⟨[
      93411, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1
    ], [93381], .contexts [
        ⟨78837, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨78838, false, false, [], [1, 5, 3, 1]⟩,
        ⟨78839, false, false, [], [1, 5, 3, 1]⟩,
        ⟨78779, false, false, [], [1, 5, 3, 1]⟩,
        ⟨78779, false, false, [], [1, 5, 3, 1]⟩,
        ⟨78840, false, false, [], [5, 3, 1]⟩,
        ⟨78841, false, false, [], [5, 3, 1]⟩,
        ⟨78776, false, false, [], [5, 3, 1]⟩,
        ⟨78776, false, false, [], [5, 3, 1]⟩,
        ⟨78774, false, false, [], [3, 1]⟩,
        ⟨78773, false, false, [], [3, 1]⟩,
        ⟨78773, false, false, [], [3, 1]⟩,
        ⟨78842, false, false, [], [1]⟩,
        ⟨78843, false, false, [], [1]⟩,
        ⟨78770, false, false, [], [1]⟩,
        ⟨78770, false, false, [], [1]⟩,
        ⟨78768, false, false, [], []⟩,
        ⟨78767, false, false, [], []⟩,
        ⟨78767, false, false, [], []⟩
      ]⟩,
    ⟨[93377], [93377], .contexts []⟩,
    ⟨[93377, 1], [93375], .contexts [
        ⟨78758, false, false, [], []⟩
      ]⟩,
    ⟨[93375], [93375], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1232. -/
def y322TCIndexRaw1232 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93371], [93371], .contexts []⟩,
    ⟨[
      93411, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [93371], .contexts [
        ⟨78844, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨78765, false, false, [], [13, 1, 11, 9]⟩,
        ⟨78764, false, false, [], [13, 1, 11, 9]⟩,
        ⟨78764, false, false, [], [13, 1, 11, 9]⟩,
        ⟨78762, false, false, [], [1, 11, 9]⟩,
        ⟨78845, false, false, [], [1, 11, 9]⟩,
        ⟨78761, false, false, [], [1, 11, 9]⟩,
        ⟨78761, false, false, [], [1, 11, 9]⟩,
        ⟨78846, false, false, [], [11, 9]⟩,
        ⟨78847, false, false, [], [11, 9]⟩,
        ⟨78757, false, false, [], [11, 9]⟩,
        ⟨78757, false, false, [], [11, 9]⟩,
        ⟨78754, false, false, [], [9]⟩,
        ⟨78753, false, false, [], [9]⟩,
        ⟨78753, false, false, [], [9]⟩,
        ⟨78750, false, false, [], []⟩,
        ⟨78848, false, false, [], []⟩,
        ⟨78749, false, false, [], []⟩,
        ⟨78749, false, false, [], []⟩
      ]⟩,
    ⟨[93369], [93369], .contexts []⟩,
    ⟨[93367], [93367], .contexts []⟩,
    ⟨[93363], [93363], .contexts []⟩,
    ⟨[93361], [93361], .contexts []⟩,
    ⟨[
      93411, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15
    ], [93361], .contexts [
        ⟨78849, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨78747, false, false, [], [5, 3, 1, 15]⟩,
        ⟨78850, false, false, [], [5, 3, 1, 15]⟩,
        ⟨78746, false, false, [], [5, 3, 1, 15]⟩,
        ⟨78746, false, false, [], [5, 3, 1, 15]⟩,
        ⟨78744, false, false, [], [3, 1, 15]⟩,
        ⟨78851, false, false, [], [3, 1, 15]⟩,
        ⟨78743, false, false, [], [3, 1, 15]⟩,
        ⟨78743, false, false, [], [3, 1, 15]⟩,
        ⟨78740, false, false, [], [1, 15]⟩,
        ⟨78739, false, false, [], [1, 15]⟩,
        ⟨78739, false, false, [], [1, 15]⟩,
        ⟨78737, false, false, [], [15]⟩,
        ⟨78852, false, false, [], [15]⟩,
        ⟨78736, false, false, [], [15]⟩,
        ⟨78736, false, false, [], [15]⟩,
        ⟨78734, false, false, [], []⟩,
        ⟨78853, false, false, [], []⟩,
        ⟨78733, false, false, [], []⟩,
        ⟨78733, false, false, [], []⟩
      ]⟩,
    ⟨[93359], [93359], .contexts []⟩,
    ⟨[93357], [93357], .contexts []⟩,
    ⟨[93355], [93355], .contexts []⟩,
    ⟨[93353], [93353], .contexts []⟩,
    ⟨[93351], [93351], .contexts []⟩,
    ⟨[
      93411, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1
    ], [93351], .contexts [
        ⟨78854, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨78731, false, false, [], [1, 11, 9, 1]⟩,
        ⟨78855, false, false, [], [1, 11, 9, 1]⟩,
        ⟨78730, false, false, [], [1, 11, 9, 1]⟩,
        ⟨78730, false, false, [], [1, 11, 9, 1]⟩,
        ⟨78728, false, false, [], [11, 9, 1]⟩,
        ⟨78856, false, false, [], [11, 9, 1]⟩,
        ⟨78727, false, false, [], [11, 9, 1]⟩,
        ⟨78727, false, false, [], [11, 9, 1]⟩,
        ⟨78725, false, false, [], [9, 1]⟩,
        ⟨78857, false, false, [], [9, 1]⟩,
        ⟨78724, false, false, [], [9, 1]⟩,
        ⟨78724, false, false, [], [9, 1]⟩,
        ⟨78722, false, false, [], [1]⟩,
        ⟨78858, false, false, [], [1]⟩,
        ⟨78721, false, false, [], [1]⟩,
        ⟨78721, false, false, [], [1]⟩,
        ⟨78719, false, false, [], []⟩,
        ⟨78859, false, false, [], []⟩,
        ⟨78718, false, false, [], []⟩,
        ⟨78718, false, false, [], []⟩
      ]⟩,
    ⟨[93349], [93349], .contexts []⟩,
    ⟨[93347], [93347], .contexts []⟩,
    ⟨[93345], [93345], .contexts []⟩,
    ⟨[93343], [93343], .contexts []⟩,
    ⟨[93341], [93341], .contexts []⟩,
    ⟨[
      93411, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [93341], .contexts [
        ⟨78860, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨78716, false, false, [], [3, 1, 15, 13]⟩,
        ⟨78861, false, false, [], [3, 1, 15, 13]⟩,
        ⟨78715, false, false, [], [3, 1, 15, 13]⟩,
        ⟨78715, false, false, [], [3, 1, 15, 13]⟩,
        ⟨78713, false, false, [], [1, 15, 13]⟩,
        ⟨78862, false, false, [], [1, 15, 13]⟩,
        ⟨78712, false, false, [], [1, 15, 13]⟩,
        ⟨78712, false, false, [], [1, 15, 13]⟩,
        ⟨78710, false, false, [], [15, 13]⟩,
        ⟨78863, false, false, [], [15, 13]⟩,
        ⟨78709, false, false, [], [15, 13]⟩,
        ⟨78709, false, false, [], [15, 13]⟩,
        ⟨78707, false, false, [], [13]⟩,
        ⟨78864, false, false, [], [13]⟩,
        ⟨78706, false, false, [], [13]⟩,
        ⟨78706, false, false, [], [13]⟩,
        ⟨78704, false, false, [], []⟩,
        ⟨78865, false, false, [], []⟩,
        ⟨78703, false, false, [], []⟩,
        ⟨78703, false, false, [], []⟩
      ]⟩,
    ⟨[93339], [93339], .contexts []⟩,
    ⟨[93337], [93337], .contexts []⟩,
    ⟨[93335], [93335], .contexts []⟩,
    ⟨[93333], [93333], .contexts []⟩,
    ⟨[93331], [93331], .contexts []⟩,
    ⟨[
      93411, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5
    ], [93331], .contexts [
        ⟨78866, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨78701, false, false, [], [11, 9, 1, 5]⟩,
        ⟨78867, false, false, [], [11, 9, 1, 5]⟩,
        ⟨78700, false, false, [], [11, 9, 1, 5]⟩,
        ⟨78700, false, false, [], [11, 9, 1, 5]⟩,
        ⟨78698, false, false, [], [9, 1, 5]⟩,
        ⟨78868, false, false, [], [9, 1, 5]⟩,
        ⟨78697, false, false, [], [9, 1, 5]⟩,
        ⟨78697, false, false, [], [9, 1, 5]⟩,
        ⟨78695, false, false, [], [1, 5]⟩,
        ⟨78869, false, false, [], [1, 5]⟩,
        ⟨78694, false, false, [], [1, 5]⟩,
        ⟨78694, false, false, [], [1, 5]⟩,
        ⟨78692, false, false, [], [5]⟩,
        ⟨78870, false, false, [], [5]⟩,
        ⟨78691, false, false, [], [5]⟩,
        ⟨78691, false, false, [], [5]⟩,
        ⟨78689, false, false, [], []⟩,
        ⟨78871, false, false, [], []⟩,
        ⟨78688, false, false, [], []⟩,
        ⟨78688, false, false, [], []⟩
      ]⟩,
    ⟨[93327], [93327], .contexts []⟩,
    ⟨[93325], [93325], .contexts []⟩,
    ⟨[93323], [93323], .contexts []⟩,
    ⟨[
      93411, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [93321], .contexts [
        ⟨78872, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨78685, false, false, [], [1, 15, 13, 1]⟩,
        ⟨78684, false, false, [], [1, 15, 13, 1]⟩,
        ⟨78684, false, false, [], [1, 15, 13, 1]⟩,
        ⟨78681, false, false, [], [15, 13, 1]⟩,
        ⟨78873, false, false, [], [15, 13, 1]⟩,
        ⟨78680, false, false, [], [15, 13, 1]⟩,
        ⟨78680, false, false, [], [15, 13, 1]⟩,
        ⟨78678, false, false, [], [13, 1]⟩,
        ⟨78874, false, false, [], [13, 1]⟩,
        ⟨78677, false, false, [], [13, 1]⟩,
        ⟨78677, false, false, [], [13, 1]⟩,
        ⟨78675, false, false, [], [1]⟩,
        ⟨78875, false, false, [], [1]⟩,
        ⟨78674, false, false, [], [1]⟩,
        ⟨78674, false, false, [], [1]⟩,
        ⟨78671, false, false, [], []⟩,
        ⟨78670, false, false, [], []⟩,
        ⟨78670, false, false, [], []⟩
      ]⟩,
    ⟨[93319, 9], [93317], .contexts [
        ⟨78663, false, false, [], []⟩
      ]⟩,
    ⟨[93315], [93315], .contexts []⟩,
    ⟨[93313], [93313], .contexts []⟩,
    ⟨[93311], [93311], .contexts []⟩,
    ⟨[
      93411, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3
    ], [93311], .contexts [
        ⟨78876, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨78667, false, false, [], [9, 1, 5, 3]⟩,
        ⟨78666, false, false, [], [9, 1, 5, 3]⟩,
        ⟨78666, false, false, [], [9, 1, 5, 3]⟩,
        ⟨78877, false, false, [], [1, 5, 3]⟩,
        ⟨78662, false, false, [], [1, 5, 3]⟩,
        ⟨78662, false, false, [], [1, 5, 3]⟩,
        ⟨78660, false, false, [], [5, 3]⟩,
        ⟨78878, false, false, [], [5, 3]⟩,
        ⟨78659, false, false, [], [5, 3]⟩,
        ⟨78659, false, false, [], [5, 3]⟩,
        ⟨78657, false, false, [], [3]⟩,
        ⟨78879, false, false, [], [3]⟩,
        ⟨78656, false, false, [], [3]⟩,
        ⟨78656, false, false, [], [3]⟩,
        ⟨78653, false, false, [], []⟩,
        ⟨78880, false, false, [], []⟩,
        ⟨78652, false, false, [], []⟩,
        ⟨78652, false, false, [], []⟩
      ]⟩,
    ⟨[93309], [93309], .contexts []⟩,
    ⟨[93309, 15], [93307], .contexts [
        ⟨78645, false, false, [], []⟩
      ]⟩,
    ⟨[93307], [93307], .contexts []⟩,
    ⟨[93305], [93305], .contexts []⟩,
    ⟨[
      93411, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11
    ], [93301], .contexts [
        ⟨78881, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨78649, false, false, [], [15, 13, 1, 11]⟩,
        ⟨78882, false, false, [], [15, 13, 1, 11]⟩,
        ⟨78648, false, false, [], [15, 13, 1, 11]⟩,
        ⟨78648, false, false, [], [15, 13, 1, 11]⟩,
        ⟨78883, false, false, [], [13, 1, 11]⟩,
        ⟨78884, false, false, [], [13, 1, 11]⟩,
        ⟨78644, false, false, [], [13, 1, 11]⟩,
        ⟨78644, false, false, [], [13, 1, 11]⟩,
        ⟨78641, false, false, [], [1, 11]⟩,
        ⟨78885, false, false, [], [1, 11]⟩,
        ⟨78640, false, false, [], [1, 11]⟩,
        ⟨78640, false, false, [], [1, 11]⟩,
        ⟨78637, true, false, [], [1, 11]⟩,
        ⟨8, false, false, [93303], [11]⟩,
        ⟨78635, false, false, [], [11]⟩,
        ⟨78634, false, false, [], [11]⟩,
        ⟨78635, false, false, [], [11]⟩,
        ⟨78635, false, false, [], [11]⟩,
        ⟨78633, true, false, [], [11]⟩,
        ⟨53, false, false, [93301], []⟩,
        ⟨78631, false, false, [], []⟩,
        ⟨78630, false, false, [], []⟩,
        ⟨78631, false, false, [], []⟩,
        ⟨78631, false, false, [], []⟩
      ]⟩,
    ⟨[
      93411, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1
    ], [29969, 93293], .contexts [
        ⟨78886, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨78629, false, false, [], [1, 5, 3, 1]⟩,
        ⟨78618, false, false, [], [1, 5, 3, 1]⟩,
        ⟨78619, false, false, [], [1, 5, 3, 1]⟩,
        ⟨78619, false, false, [], [1, 5, 3, 1]⟩,
        ⟨78624, false, false, [], [5, 3, 1]⟩,
        ⟨78621, false, false, [], [5, 3, 1]⟩,
        ⟨78622, false, false, [], [5, 3, 1]⟩,
        ⟨78622, false, false, [], [5, 3, 1]⟩,
        ⟨78617, false, false, [29969], [3, 1]⟩,
        ⟨78608, false, false, [], [3, 1]⟩,
        ⟨78609, false, false, [], [3, 1]⟩,
        ⟨78610, false, false, [], [3, 1]⟩,
        ⟨78601, false, false, [29969], [1]⟩,
        ⟨78605, false, false, [], [1]⟩,
        ⟨78606, false, false, [], [1]⟩,
        ⟨78607, false, false, [], [1]⟩,
        ⟨78592, false, false, [29969], []⟩,
        ⟨78581, false, false, [], []⟩,
        ⟨78582, false, false, [], []⟩,
        ⟨78583, false, false, [], []⟩
      ]⟩,
    ⟨[29969, 93289, 1], [29969, 93287], .contexts [
        ⟨78527, false, false, [29969], []⟩
      ]⟩,
    ⟨[29969, 93287], [29969, 93287], .contexts []⟩,
    ⟨[29969, 93287], [29969, 93287], .contexts []⟩,
    ⟨[29969, 93287], [29969, 93287], .contexts []⟩,
    ⟨[
      93411, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11
    ], [29969, 93285], .contexts [
        ⟨78887, false, false, [], [15, 13, 1, 11]⟩,
        ⟨78576, true, false, [29969], [15, 13, 1, 11]⟩,
        ⟨1, false, false, [29969, 93291], [13, 1, 11]⟩,
        ⟨78561, false, false, [29969], [13, 1, 11]⟩,
        ⟨78566, false, false, [], [13, 1, 11]⟩,
        ⟨78567, false, false, [], [13, 1, 11]⟩,
        ⟨78568, false, false, [], [13, 1, 11]⟩,
        ⟨78558, false, false, [29969], [1, 11]⟩,
        ⟨78564, false, false, [], [1, 11]⟩,
        ⟨78565, false, false, [], [1, 11]⟩,
        ⟨78888, false, false, [], [11]⟩,
        ⟨78889, false, false, [], [11]⟩,
        ⟨78890, false, false, [], [11]⟩,
        ⟨78891, false, false, [], [11]⟩,
        ⟨78509, false, false, [29969], []⟩
      ]⟩,
    ⟨[29977], [29969, 2373], .source 15053⟩,
    ⟨[29979], [29977, 15167], .source 15054⟩,
    ⟨[
      93411, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [29979, 81365], .contexts [
        ⟨78892, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨78487, false, false, [29969], [1, 5, 3, 1]⟩,
        ⟨78460, false, false, [29969], [5, 3, 1]⟩,
        ⟨70440, false, false, [29969], [3, 1]⟩,
        ⟨78893, true, false, [], [92181, 3, 1]⟩,
        ⟨70433, false, false, [29977], [1]⟩,
        ⟨78894, true, false, [], [81393, 1]⟩,
        ⟨9015, false, false, [29979], []⟩
      ]⟩,
    ⟨[29981], [29979, 8439], .source 15055⟩,
    ⟨[29983], [29981, 8439], .source 15056⟩,
    ⟨[29985], [29983, 3155], .source 15057⟩,
    ⟨[29987], [29985, 12835], .source 15058⟩,
    ⟨[29989], [29987, 2009], .source 15059⟩,
    ⟨[
      93411, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9
    ], [29989, 79891], .contexts [
        ⟨78895, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨8938, false, false, [29979], [13, 1, 11, 9]⟩,
        ⟨11552, false, false, [29979], [13, 1, 11, 9]⟩,
        ⟨78896, true, false, [], [80983, 13, 1, 11, 9]⟩,
        ⟨8626, false, false, [29981], [1, 11, 9]⟩,
        ⟨11552, false, false, [29981], [1, 11, 9]⟩,
        ⟨78897, true, false, [], [80983, 1, 11, 9]⟩,
        ⟨8409, false, false, [29983], [11, 9]⟩,
        ⟨78898, true, false, [], [80793, 11, 9]⟩,
        ⟨8243, false, false, [29985], [9]⟩,
        ⟨13764, false, false, [29985], [9]⟩,
        ⟨78899, true, false, [], [79891, 9]⟩,
        ⟨7356, false, false, [29987], []⟩,
        ⟨78900, true, false, [], [79891]⟩
      ]⟩,
    ⟨[29991], [29989, 12841], .source 15060⟩,
    ⟨[29993], [29991, 2373], .source 15061⟩,
    ⟨[29995], [29993, 16357], .source 15062⟩,
    ⟨[
      93411, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15
    ], [29995, 83497], .contexts [
        ⟨78901, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨7507, false, false, [29989], [5, 3, 1, 15]⟩,
        ⟨7499, false, false, [29989], [3, 1, 15]⟩,
        ⟨13791, false, false, [29989], [1, 15]⟩,
        ⟨78902, true, false, [], [80253, 1, 15]⟩,
        ⟨7749, false, false, [29991], [15]⟩,
        ⟨78903, true, false, [], [80253, 15]⟩,
        ⟨21615, false, false, [29993], []⟩,
        ⟨78904, true, false, [], [83497]⟩
      ]⟩,
    ⟨[29997], [29995, 14141], .source 15063⟩,
    ⟨[29999], [29997, 1035], .source 15064⟩,
    ⟨[30001], [29999, 12947], .source 15065⟩,
    ⟨[30003], [30001, 12505], .source 15066⟩,
    ⟨[
      93411, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1
    ], [30003, 83945], .contexts [
        ⟨78905, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨21607, false, false, [29995], [1, 11, 9, 1]⟩,
        ⟨78906, true, false, [], [83349, 1, 11, 9, 1]⟩,
        ⟨23855, false, false, [29997], [11, 9, 1]⟩,
        ⟨78907, true, false, [], [83935, 11, 9, 1]⟩,
        ⟨23870, false, false, [29999], [9, 1]⟩,
        ⟨78908, true, false, [], [83189, 9, 1]⟩,
        ⟨23978, false, false, [30001], [1]⟩,
        ⟨23989, false, false, [30001], []⟩,
        ⟨78909, true, false, [], [83945]⟩
      ]⟩,
    ⟨[30005], [30003, 16015], .source 15067⟩]

/-- Exact literal claimed equations and contextual derivations, block 1233. -/
def y322TCIndexRaw1233 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[30007], [30005, 727], .source 15068⟩,
    ⟨[93413, 13], [93413, 13], .contexts []⟩,
    ⟨[93413, 13], [30007, 87719], .contexts [
        ⟨78913, false, false, [], []⟩,
        ⟨78821, true, false, [], [13]⟩,
        ⟨78821, true, false, [], [13]⟩,
        ⟨78819, true, false, [], [13]⟩,
        ⟨5361, false, false, [93411], []⟩,
        ⟨5362, false, false, [93411], []⟩,
        ⟨78910, false, false, [], [5, 3, 1, 15]⟩,
        ⟨52795, false, false, [30003], [3, 1, 15]⟩,
        ⟨52808, false, false, [30003], [1, 15]⟩,
        ⟨78911, true, false, [], [87717, 1, 15]⟩,
        ⟨45859, false, false, [30005], [15]⟩,
        ⟨45871, false, false, [30005], []⟩,
        ⟨78912, true, false, [], [87719]⟩,
        ⟨45866, false, false, [30007], []⟩
      ]⟩,
    ⟨[93413, 13], [30007, 87719], .contexts [
        ⟨78914, false, false, [], []⟩,
        ⟨13, true, false, [], [30007, 87719]⟩
      ]⟩,
    ⟨[30009], [30006], .source 15069⟩,
    ⟨[87719, 13], [30009, 93413], .contexts [
        ⟨78915, true, false, [30006], [13]⟩,
        ⟨59, false, false, [30006, 93413], []⟩,
        ⟨78916, true, false, [], [93413]⟩
      ]⟩,
    ⟨[30007, 87719], [30007, 87719], .contexts []⟩,
    ⟨[30011], [30007, 2797], .source 15070⟩,
    ⟨[30011, 87719], [30011, 87719], .contexts []⟩,
    ⟨[30011, 87719], [30011, 87719], .contexts []⟩,
    ⟨[93411, 13], [93411, 13], .contexts []⟩,
    ⟨[93411, 13], [30011, 87719], .contexts [
        ⟨78922, false, false, [], []⟩,
        ⟨78820, true, false, [], [13]⟩,
        ⟨78820, true, false, [], [13]⟩,
        ⟨78820, true, false, [], [13]⟩,
        ⟨8, true, false, [93411], [13]⟩,
        ⟨78819, false, false, [], [1, 13]⟩,
        ⟨115, false, false, [93413], []⟩,
        ⟨118, false, false, [93413], []⟩,
        ⟨78913, false, false, [], [1, 13, 1]⟩,
        ⟨78915, false, false, [], [1, 13, 1]⟩,
        ⟨78918, false, false, [], [1, 13, 1]⟩,
        ⟨78918, false, false, [], [1, 13, 1]⟩,
        ⟨45860, false, false, [30007], [13, 1]⟩,
        ⟨45853, false, false, [30007], [1]⟩,
        ⟨78919, true, false, [], [87717, 1]⟩,
        ⟨45859, false, false, [30011], []⟩,
        ⟨78920, false, false, [], []⟩,
        ⟨78921, false, false, [], []⟩,
        ⟨45866, false, false, [30011], []⟩
      ]⟩,
    ⟨[93411, 13], [30011, 87719], .contexts [
        ⟨78923, false, false, [], []⟩,
        ⟨13, true, false, [], [30011, 87719]⟩
      ]⟩,
    ⟨[30013], [30010], .source 15071⟩,
    ⟨[87719, 13], [30009, 93413], .contexts [
        ⟨78917, false, false, [], []⟩
      ]⟩,
    ⟨[30009, 93413], [30009, 93413], .contexts []⟩,
    ⟨[30015], [30007, 30013], .source 15072⟩,
    ⟨[93411, 13], [30011, 87719], .contexts [
        ⟨78922, false, false, [], []⟩,
        ⟨78924, false, false, [], []⟩,
        ⟨78920, false, false, [], []⟩,
        ⟨78921, false, false, [], []⟩,
        ⟨78921, false, false, [], []⟩
      ]⟩,
    ⟨[30017], [30011, 23347], .source 15073⟩,
    ⟨[93413], [30015, 93411], .contexts [
        ⟨78927, true, false, [30008], []⟩,
        ⟨78927, true, false, [30008], []⟩,
        ⟨78926, true, false, [30008], []⟩,
        ⟨78924, true, false, [30008, 30010], [13]⟩,
        ⟨59, false, false, [30008, 30010, 93411], []⟩,
        ⟨78925, true, false, [30008], [93411]⟩,
        ⟨78916, false, true, [], [30013, 93411]⟩,
        ⟨78928, true, false, [], [93411]⟩
      ]⟩,
    ⟨[93413], [30015, 93411], .contexts [
        ⟨78931, false, false, [], []⟩
      ]⟩,
    ⟨[30019], [30009, 30015], .source 15074⟩,
    ⟨[30021], [30017, 30019], .source 15075⟩,
    ⟨[93411], [93411], .contexts []⟩,
    ⟨[93411], [93411], .contexts []⟩,
    ⟨[30023], [30020], .source 15076⟩,
    ⟨[30020], [30020], .contexts []⟩,
    ⟨[30025], [30011, 25815], .source 15077⟩,
    ⟨[30027], [30025, 25851], .source 15078⟩,
    ⟨[91107, 5], [91107, 5], .contexts []⟩,
    ⟨[30029], [30026], .source 15079⟩,
    ⟨[30026], [30026], .contexts []⟩,
    ⟨[91107, 5], [30029, 93411], .contexts [
        ⟨78941, false, false, [], []⟩,
        ⟨78940, false, false, [30026], [91107, 5]⟩,
        ⟨64381, true, false, [30026, 30025], [5]⟩,
        ⟨64225, true, false, [30026, 30025], [5]⟩,
        ⟨78939, false, false, [30026], [91113, 13, 5]⟩,
        ⟨64349, true, false, [30026, 30011], [13, 5]⟩,
        ⟨78929, true, false, [30026], [5, 13, 5]⟩,
        ⟨1116, false, false, [30026, 93411], []⟩,
        ⟨78935, false, false, [30026], []⟩,
        ⟨78936, false, false, [30026], []⟩,
        ⟨78943, true, false, [], [93411]⟩,
        ⟨78943, true, false, [], [93411]⟩,
        ⟨78942, true, false, [], [93411]⟩
      ]⟩,
    ⟨[30031], [30011, 23355], .source 15080⟩,
    ⟨[30033], [30031, 30019], .source 15081⟩,
    ⟨[30035], [30032], .source 15082⟩,
    ⟨[30032], [30032], .contexts []⟩,
    ⟨[30037], [30011, 16023], .source 15083⟩,
    ⟨[30039], [30037, 30019], .source 15084⟩,
    ⟨[30039, 93409], [30039, 93409], .contexts []⟩,
    ⟨[93411], [30039, 93409], .contexts [
        ⟨78936, false, false, [], []⟩,
        ⟨81, true, false, [93411], []⟩,
        ⟨78929, false, false, [], [11, 13, 11]⟩,
        ⟨45867, false, false, [30011], [13, 11]⟩,
        ⟨78949, true, false, [], [87719, 13, 11]⟩,
        ⟨78917, false, false, [30037], [11]⟩,
        ⟨78932, false, false, [30037, 30009], [11]⟩,
        ⟨78933, true, false, [30037], [93411, 11]⟩,
        ⟨78950, true, false, [], [93411, 11]⟩,
        ⟨78817, false, false, [30039], []⟩,
        ⟨78951, false, false, [], []⟩
      ]⟩,
    ⟨[30015, 93411], [30015, 30039, 93409], .contexts [
        ⟨78952, false, false, [30015], []⟩
      ]⟩,
    ⟨[30041], [30015, 30039], .source 15085⟩,
    ⟨[93413], [30041, 93409], .contexts [
        ⟨78932, false, false, [], []⟩,
        ⟨78953, false, false, [], []⟩,
        ⟨78954, true, false, [], [93409]⟩
      ]⟩,
    ⟨[30043], [30038], .source 15086⟩,
    ⟨[30045], [30043, 30041], .source 15087⟩,
    ⟨[93409, 1], [30045, 93409], .contexts [
        ⟨78952, true, false, [30038], [1]⟩,
        ⟨78819, false, false, [30038], []⟩,
        ⟨78955, false, false, [30038], []⟩,
        ⟨78956, true, false, [], [30041, 93409]⟩,
        ⟨78957, true, false, [], [93409]⟩
      ]⟩,
    ⟨[30047], [30043, 30011], .source 15088⟩,
    ⟨[93411], [30039, 93409], .contexts [
        ⟨78952, false, false, [], []⟩
      ]⟩,
    ⟨[93411], [30039, 93409], .contexts [
        ⟨78960, false, false, [], []⟩,
        ⟨78951, false, false, [], []⟩
      ]⟩,
    ⟨[30049], [30043, 30023], .source 15089⟩,
    ⟨[30051], [30049, 30039], .source 15090⟩,
    ⟨[93409, 3], [30051, 93409], .contexts [
        ⟨78952, true, false, [30038], [3]⟩,
        ⟨78934, false, false, [30038, 30020], [93411, 3]⟩,
        ⟨78933, false, false, [30038, 30020, 30017], [93411, 3]⟩,
        ⟨78932, true, false, [30038, 30020, 30017, 30009], [3]⟩,
        ⟨78917, true, false, [30038, 30020, 30017], [3]⟩,
        ⟨78930, false, false, [30038, 30020], [87719, 13, 3]⟩,
        ⟨52825, true, false, [30038, 30020, 30011], [13, 3]⟩,
        ⟨78929, true, false, [30038, 30020], [3, 13, 3]⟩,
        ⟨4550, false, false, [30038, 30020, 93411], []⟩,
        ⟨78935, false, false, [30038, 30020], []⟩,
        ⟨78936, false, false, [30038, 30020], []⟩,
        ⟨78938, true, false, [30038], [93411]⟩,
        ⟨78938, true, false, [30038], [93411]⟩,
        ⟨78937, true, false, [30038], [93411]⟩,
        ⟨78961, false, false, [30038, 30023], []⟩,
        ⟨78956, true, false, [], [30023, 30039, 93409]⟩,
        ⟨78962, true, false, [], [30039, 93409]⟩,
        ⟨78963, true, false, [], [93409]⟩
      ]⟩,
    ⟨[30053], [30043, 30027], .source 15091⟩,
    ⟨[30055], [30043, 30035], .source 15092⟩,
    ⟨[30057], [30055, 30039], .source 15093⟩,
    ⟨[93409, 7], [30057, 93409], .contexts [
        ⟨78952, true, false, [30038], [7]⟩,
        ⟨78946, false, false, [30038, 30032], [93411, 7]⟩,
        ⟨78933, false, false, [30038, 30032, 30031], [93411, 7]⟩,
        ⟨78932, true, false, [30038, 30032, 30031, 30009], [7]⟩,
        ⟨78917, true, false, [30038, 30032, 30031], [7]⟩,
        ⟨78945, false, false, [30038, 30032], [87719, 13, 7]⟩,
        ⟨52843, true, false, [30038, 30032, 30011], [13, 7]⟩,
        ⟨78929, true, false, [30038, 30032], [7, 13, 7]⟩,
        ⟨21371, false, false, [30038, 30032, 93411], []⟩,
        ⟨78935, false, false, [30038, 30032], []⟩,
        ⟨78936, false, false, [30038, 30032], []⟩,
        ⟨78948, true, false, [30038], [93411]⟩,
        ⟨78948, true, false, [30038], [93411]⟩,
        ⟨78947, true, false, [30038], [93411]⟩,
        ⟨78961, false, false, [30038, 30035], []⟩,
        ⟨78956, true, false, [], [30035, 30039, 93409]⟩,
        ⟨78966, true, false, [], [30039, 93409]⟩,
        ⟨78967, true, false, [], [93409]⟩
      ]⟩,
    ⟨[30059], [30009, 30041], .source 15094⟩,
    ⟨[87719, 13], [30059, 93409], .contexts [
        ⟨78926, false, false, [], []⟩,
        ⟨78955, false, false, [30009], []⟩,
        ⟨78969, true, false, [], [93409]⟩
      ]⟩,
    ⟨[93407, 13], [93407, 13], .contexts []⟩,
    ⟨[30061], [30058], .source 15095⟩,
    ⟨[30058], [30058], .contexts []⟩,
    ⟨[93407, 13], [30061, 87721], .contexts [
        ⟨78971, false, false, [], []⟩,
        ⟨78813, true, false, [], [13]⟩,
        ⟨78970, true, false, [30058], [9, 13]⟩,
        ⟨942, false, false, [30058, 87719], []⟩,
        ⟨52832, false, false, [30058], []⟩,
        ⟨45877, false, false, [30058], []⟩,
        ⟨45882, false, false, [30058], []⟩,
        ⟨78973, true, false, [], [87721]⟩,
        ⟨78973, true, false, [], [87721]⟩,
        ⟨78972, true, false, [], [87721]⟩
      ]⟩,
    ⟨[30059], [30060], .contexts [
        ⟨78972, true, true, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1234. -/
def y322TCIndexRaw1234 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93409, 9], [93407], .contexts [
        ⟨78823, false, false, [], []⟩,
        ⟨78824, false, false, [], []⟩,
        ⟨78812, false, false, [], []⟩,
        ⟨78812, false, false, [], []⟩
      ]⟩,
    ⟨[30051, 93409], [30051, 93409], .contexts []⟩,
    ⟨[30051, 93409], [30051, 93409], .contexts []⟩,
    ⟨[93409, 3], [30051, 93409], .contexts [
        ⟨78964, false, false, [], []⟩,
        ⟨78977, false, false, [], []⟩,
        ⟨78978, false, false, [], []⟩,
        ⟨78978, false, false, [], []⟩
      ]⟩,
    ⟨[93409, 8], [93409, 9], .contexts [
        ⟨47, false, false, [93409], []⟩
      ]⟩,
    ⟨[93407], [93407], .contexts []⟩,
    ⟨[30065], [30050], .source 15097⟩,
    ⟨[30050], [30050], .contexts []⟩,
    ⟨[30029, 93411], [30029, 30039, 93409], .contexts [
        ⟨78961, false, false, [30029], []⟩
      ]⟩,
    ⟨[30067], [30029, 30039], .source 15098⟩,
    ⟨[30067, 93407], [30067, 93407], .contexts []⟩,
    ⟨[30067, 93407], [30067, 93407], .contexts []⟩,
    ⟨[91107, 8], [91107, 9], .contexts [
        ⟨47, false, false, [91107], []⟩
      ]⟩,
    ⟨[93407, 5], [93407, 5], .contexts []⟩,
    ⟨[91105], [91105], .contexts []⟩,
    ⟨[30069], [30066], .source 15099⟩,
    ⟨[30069], [30069], .contexts []⟩,
    ⟨[30066], [30066], .contexts []⟩,
    ⟨[93407, 5], [30069, 91105], .contexts [
        ⟨78989, false, false, [], []⟩,
        ⟨78987, true, false, [30066], [5]⟩,
        ⟨78986, true, false, [30066], [5]⟩,
        ⟨78813, true, false, [], [5]⟩,
        ⟨78985, false, false, [30066], [93409, 9, 5]⟩,
        ⟨78984, true, false, [30066], [9, 5]⟩,
        ⟨78944, true, false, [30066], [9, 5]⟩,
        ⟨78941, true, false, [30066], [9, 5]⟩,
        ⟨960, false, false, [30066, 91107], []⟩,
        ⟨78988, false, false, [30066], []⟩,
        ⟨64386, false, false, [30066], []⟩,
        ⟨78990, false, false, [30066], []⟩,
        ⟨78993, true, false, [], [91105]⟩,
        ⟨78993, true, false, [], [91105]⟩,
        ⟨78991, true, false, [], [91105]⟩,
        ⟨78992, true, false, [], [91105]⟩
      ]⟩,
    ⟨[30067], [30068], .contexts [
        ⟨78991, true, true, [], []⟩
      ]⟩,
    ⟨[30057, 93409], [30057, 93409], .contexts []⟩,
    ⟨[30057, 93409], [30057, 93409], .contexts []⟩,
    ⟨[93409, 7], [30057, 93409], .contexts [
        ⟨78968, false, false, [], []⟩,
        ⟨78996, false, false, [], []⟩,
        ⟨78997, false, false, [], []⟩,
        ⟨78997, false, false, [], []⟩
      ]⟩,
    ⟨[93407, 7], [93407, 7], .contexts []⟩,
    ⟨[30071], [30056], .source 15100⟩,
    ⟨[30056], [30056], .contexts []⟩,
    ⟨[30061, 87721], [30061, 87721], .contexts []⟩,
    ⟨[30061, 87721], [30061, 87721], .contexts []⟩,
    ⟨[30061, 89845], [30061, 89845], .contexts []⟩,
    ⟨[93407], [93407], .contexts []⟩,
    ⟨[30060], [30060], .contexts []⟩,
    ⟨[89845, 11], [30059, 93407], .contexts [
        ⟨79004, true, false, [30060], [11]⟩,
        ⟨57927, true, false, [], [11]⟩,
        ⟨45885, true, false, [], [13, 11]⟩,
        ⟨79003, true, false, [30060], [11, 13, 11]⟩,
        ⟨79003, true, false, [30060], [11, 13, 11]⟩,
        ⟨79002, true, false, [30060], [11, 13, 11]⟩,
        ⟨78974, true, false, [30060], [11, 13, 11]⟩,
        ⟨78971, true, false, [30060], [11, 13, 11]⟩,
        ⟨4838, false, false, [30060, 93407], []⟩,
        ⟨79005, false, false, [30060], []⟩,
        ⟨78981, false, false, [30060], []⟩,
        ⟨79006, true, false, [], [93407]⟩,
        ⟨79006, true, false, [], [93407]⟩,
        ⟨78975, true, false, [], [93407]⟩
      ]⟩,
    ⟨[93407, 11], [30061, 89845], .contexts [
        ⟨79007, true, false, [30058], [11]⟩,
        ⟨53, false, false, [30058, 89845], []⟩,
        ⟨78972, true, false, [], [89845]⟩
      ]⟩,
    ⟨[30069, 91105], [30069, 91105], .contexts []⟩,
    ⟨[30069, 91105], [30069, 91105], .contexts []⟩,
    ⟨[30069, 91103], [30069, 91103], .contexts []⟩,
    ⟨[30069, 91103], [30069, 91103], .contexts []⟩,
    ⟨[30069, 91103], [30069, 91103], .contexts []⟩,
    ⟨[30069, 91101], [30069, 91101], .contexts []⟩,
    ⟨[30069, 91101], [30069, 91101], .contexts []⟩,
    ⟨[91101, 1], [91101, 1], .contexts []⟩,
    ⟨[30067], [30068], .contexts [
        ⟨78995, false, false, [], []⟩
      ]⟩,
    ⟨[30068], [30068], .contexts []⟩,
    ⟨[91101, 1], [30067, 93407], .contexts [
        ⟨79016, false, false, [], []⟩,
        ⟨79015, true, false, [30068], [1]⟩,
        ⟨79014, true, false, [30068], [1]⟩,
        ⟨64207, true, false, [], [1]⟩,
        ⟨79013, true, false, [30068], [5, 1]⟩,
        ⟨79012, true, false, [30068], [5, 1]⟩,
        ⟨79011, true, false, [30068], [5, 1]⟩,
        ⟨64211, true, false, [], [5, 1]⟩,
        ⟨79010, true, false, [30068], [1, 5, 1]⟩,
        ⟨79010, true, false, [30068], [1, 5, 1]⟩,
        ⟨79009, true, false, [30068], [1, 5, 1]⟩,
        ⟨78994, true, false, [30068], [1, 5, 1]⟩,
        ⟨78989, true, false, [30068], [1, 5, 1]⟩,
        ⟨874, false, false, [30068, 93407], []⟩,
        ⟨79005, false, false, [30068], []⟩,
        ⟨78981, false, false, [30068], []⟩,
        ⟨79018, true, false, [], [93407]⟩,
        ⟨79018, true, false, [], [93407]⟩,
        ⟨79017, true, false, [], [93407]⟩
      ]⟩,
    ⟨[93407, 1], [93405], .contexts [
        ⟨78825, false, false, [], []⟩
      ]⟩,
    ⟨[93405], [30069, 91101], .contexts [
        ⟨78808, true, false, [], []⟩,
        ⟨78808, true, false, [], []⟩,
        ⟨78826, true, false, [], []⟩,
        ⟨79020, true, false, [], []⟩,
        ⟨79019, true, false, [30066], [1]⟩,
        ⟨8, false, false, [30066, 91101], []⟩,
        ⟨78991, true, false, [], [91101]⟩,
        ⟨79014, false, false, [], []⟩,
        ⟨78992, true, false, [], [91101]⟩,
        ⟨79015, false, false, [], []⟩
      ]⟩,
    ⟨[93403], [30069, 91103], .contexts [
        ⟨79017, false, false, [30066], [93403]⟩,
        ⟨13, false, false, [30066, 30068], [93403]⟩,
        ⟨78827, true, false, [30066, 30068], []⟩,
        ⟨78806, true, false, [30066, 30068], []⟩,
        ⟨79021, false, false, [30066, 30068], [5]⟩,
        ⟨64205, false, false, [30066], []⟩,
        ⟨79011, false, false, [30066, 30068], []⟩,
        ⟨79012, false, false, [30066, 30068], []⟩,
        ⟨79013, false, false, [30066, 30068], []⟩,
        ⟨78991, true, false, [], [91103]⟩
      ]⟩,
    ⟨[91103, 3], [30067, 93401], .contexts [
        ⟨79022, true, false, [30068], [3]⟩,
        ⟨78803, false, false, [30068], []⟩,
        ⟨78828, false, false, [30068], []⟩,
        ⟨79018, true, false, [], [93401]⟩,
        ⟨79018, true, false, [], [93401]⟩,
        ⟨79017, true, false, [], [93401]⟩
      ]⟩,
    ⟨[93403], [30069, 91103], .contexts [
        ⟨79022, false, false, [], []⟩
      ]⟩,
    ⟨[93403], [30069, 91103], .contexts [
        ⟨79024, false, false, [], []⟩,
        ⟨79013, false, false, [], []⟩
      ]⟩,
    ⟨[30071, 93407], [30071, 93407], .contexts []⟩,
    ⟨[30073], [30071, 30069], .source 15101⟩,
    ⟨[93407, 7, 1], [30073, 91101], .contexts [
        ⟨78999, false, false, [], [1]⟩,
        ⟨78999, false, false, [], [1]⟩,
        ⟨78813, true, false, [], [7, 1]⟩,
        ⟨78998, true, false, [30056], [9, 7, 1]⟩,
        ⟨579, false, false, [30056, 93409], [1]⟩,
        ⟨78980, false, false, [30056], [1]⟩,
        ⟨78976, false, false, [30056], [1]⟩,
        ⟨78981, false, false, [30056], [1]⟩,
        ⟨79001, true, false, [], [93407, 1]⟩,
        ⟨79001, true, false, [], [93407, 1]⟩,
        ⟨79000, true, false, [], [93407, 1]⟩,
        ⟨79026, false, false, [], [1]⟩,
        ⟨79026, false, false, [], [1]⟩,
        ⟨78809, false, false, [30071], []⟩,
        ⟨79021, false, false, [30071], []⟩,
        ⟨79027, true, false, [], [91101]⟩
      ]⟩,
    ⟨[91101, 7], [91101, 7], .contexts []⟩,
    ⟨[30075], [30072], .source 15102⟩,
    ⟨[30077], [30075, 30069], .source 15103⟩,
    ⟨[30079], [25859, 30067], .source 15104⟩,
    ⟨[30067, 93401], [30067, 93401], .contexts []⟩,
    ⟨[30067, 93401], [30067, 93401], .contexts []⟩,
    ⟨[93401], [93401], .contexts []⟩,
    ⟨[30081], [30078], .source 15105⟩,
    ⟨[30083], [30081, 30067], .source 15106⟩,
    ⟨[30085], [30067, 30065], .source 15107⟩,
    ⟨[30087], [30085, 30069], .source 15108⟩]

/-- Exact literal claimed equations and contextual derivations, block 1235. -/
def y322TCIndexRaw1235 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[91101, 1, 3, 1], [30087, 91101], .contexts [
        ⟨79016, false, false, [], [3, 1]⟩,
        ⟨79019, false, false, [], [3, 1]⟩,
        ⟨78986, false, false, [], [3, 1]⟩,
        ⟨78987, false, false, [], [3, 1]⟩,
        ⟨78987, false, false, [], [3, 1]⟩,
        ⟨78813, true, false, [30067], [3, 1]⟩,
        ⟨78979, true, false, [30067, 30050], [9, 3, 1]⟩,
        ⟨573, false, false, [30067, 30050, 93409], [1]⟩,
        ⟨78980, false, false, [30067, 30050], [1]⟩,
        ⟨78976, false, false, [30067, 30050], [1]⟩,
        ⟨78981, false, false, [30067, 30050], [1]⟩,
        ⟨78983, true, false, [30067], [93407, 1]⟩,
        ⟨78983, true, false, [30067], [93407, 1]⟩,
        ⟨78982, true, false, [30067], [93407, 1]⟩,
        ⟨79038, true, false, [], [93407, 1]⟩,
        ⟨78809, false, false, [30085], []⟩,
        ⟨79021, false, false, [30085], []⟩,
        ⟨79039, true, false, [], [91101]⟩
      ]⟩,
    ⟨[30087, 91097], [30087, 91097], .contexts []⟩,
    ⟨[30087, 91097], [30087, 91097], .contexts []⟩,
    ⟨[30089], [30086], .source 15109⟩,
    ⟨[30089], [30086], .contexts [
        ⟨79043, false, false, [], []⟩
      ]⟩,
    ⟨[30086], [30086], .contexts []⟩,
    ⟨[30089], [30086], .contexts [
        ⟨79044, false, false, [], []⟩,
        ⟨79045, false, false, [], []⟩,
        ⟨79045, false, false, [], []⟩
      ]⟩,
    ⟨[91097, 3], [30089, 91101], .contexts [
        ⟨79042, true, false, [30086], [3]⟩,
        ⟨79041, true, false, [30086], [3]⟩,
        ⟨64200, true, false, [], [3]⟩,
        ⟨64203, true, false, [], [1, 3]⟩,
        ⟨79040, true, false, [30086], [3, 1, 3]⟩,
        ⟨4083, false, false, [30086, 91101], []⟩,
        ⟨64401, false, false, [30086], []⟩,
        ⟨79046, true, false, [], [91101]⟩
      ]⟩,
    ⟨[30087], [30088], .contexts [
        ⟨79043, true, true, [], []⟩
      ]⟩,
    ⟨[30087], [30087], .contexts []⟩,
    ⟨[30087], [30087], .contexts []⟩,
    ⟨[30087], [30087], .contexts []⟩,
    ⟨[91099], [30087, 91097], .contexts [
        ⟨64406, true, false, [], []⟩,
        ⟨79047, true, false, [30088], [3]⟩,
        ⟨20, false, false, [30088, 91097], []⟩,
        ⟨79048, true, false, [], [91097]⟩,
        ⟨79041, false, false, [], []⟩,
        ⟨79051, true, false, [], [91097]⟩,
        ⟨79050, true, false, [], [91097]⟩,
        ⟨79049, true, false, [], [91097]⟩
      ]⟩,
    ⟨[91099], [30087, 91097], .contexts [
        ⟨79052, false, false, [], []⟩
      ]⟩,
    ⟨[91099], [30087, 91097], .contexts [
        ⟨79053, false, false, [], []⟩,
        ⟨79042, false, false, [], []⟩
      ]⟩,
    ⟨[30091], [30089, 25859], .source 15110⟩,
    ⟨[30093], [30091, 30087], .source 15111⟩,
    ⟨[91097, 9], [30093, 91097], .contexts [
        ⟨79052, true, false, [30086], [9]⟩,
        ⟨64203, true, false, [30086], [9]⟩,
        ⟨64404, true, false, [30086, 25854], [3, 9]⟩,
        ⟨64404, true, false, [30086, 25854], [3, 9]⟩,
        ⟨64403, true, false, [30086, 25854], [3, 9]⟩,
        ⟨64400, true, false, [30086, 25854], [3, 9]⟩,
        ⟨479, false, false, [30086, 25854, 91101], []⟩,
        ⟨21, false, false, [30086, 25854, 91101], []⟩,
        ⟨64406, false, false, [30086, 25854], []⟩,
        ⟨64392, true, false, [30086], [91099]⟩,
        ⟨79054, false, false, [30086, 25859], []⟩,
        ⟨79043, true, false, [], [25859, 30087, 91097]⟩,
        ⟨79055, true, false, [], [30087, 91097]⟩,
        ⟨79056, true, false, [], [91097]⟩
      ]⟩,
    ⟨[91099], [30087, 91097], .contexts [
        ⟨79054, false, false, [], []⟩
      ]⟩,
    ⟨[30077, 91101], [30077, 91101], .contexts []⟩,
    ⟨[30095], [30077, 30087], .source 15112⟩,
    ⟨[91097, 7], [91097, 7], .contexts []⟩,
    ⟨[91097, 7], [30086, 30095, 91097], .contexts [
        ⟨79061, false, false, [], []⟩,
        ⟨79042, true, false, [30086], [7]⟩,
        ⟨79042, true, false, [30086], [7]⟩,
        ⟨79058, true, false, [30086], [7]⟩,
        ⟨64405, true, false, [30086], [7]⟩,
        ⟨140, false, false, [30086, 91101], []⟩,
        ⟨141, false, false, [30086, 91101], []⟩,
        ⟨79029, false, false, [30086], [3]⟩,
        ⟨79029, false, false, [30086], [3]⟩,
        ⟨79028, true, false, [30086, 30072], [7, 3]⟩,
        ⟨502, false, false, [30086, 30072, 93407], [3]⟩,
        ⟨9, false, false, [30086, 30072, 93407], [3]⟩,
        ⟨79020, false, false, [30086, 30072], [3]⟩,
        ⟨79021, false, false, [30086, 30072], [3]⟩,
        ⟨79015, false, false, [30086, 30072], [3]⟩,
        ⟨79015, false, false, [30086, 30072], [3]⟩,
        ⟨64401, false, false, [30086, 30072, 30069], [3]⟩,
        ⟨79030, true, false, [30086], [30069, 91101, 3]⟩,
        ⟨79031, true, false, [30086], [91101, 3]⟩,
        ⟨79059, false, false, [30086], [3]⟩,
        ⟨79059, false, false, [30086], [3]⟩,
        ⟨64203, false, false, [30086, 30077], []⟩,
        ⟨79054, false, false, [30086, 30077], []⟩,
        ⟨79060, true, false, [30086], [91097]⟩
      ]⟩,
    ⟨[91097], [91097], .contexts []⟩,
    ⟨[30097], [30089, 30095], .source 15113⟩,
    ⟨[91097, 7], [30097, 91097], .contexts [
        ⟨79062, false, false, [], []⟩,
        ⟨79063, false, false, [30086, 30095], []⟩,
        ⟨79044, true, false, [], [30095, 91097]⟩,
        ⟨79064, true, false, [], [91097]⟩
      ]⟩,
    ⟨[91097, 15], [91095], .contexts [
        ⟨64242, false, false, [], []⟩,
        ⟨64243, false, false, [], []⟩,
        ⟨64195, false, false, [], []⟩,
        ⟨64195, false, false, [], []⟩
      ]⟩,
    ⟨[91097, 1], [30087, 91097], .contexts [
        ⟨64198, false, false, [], []⟩,
        ⟨79058, false, false, [], []⟩,
        ⟨79042, false, false, [], []⟩,
        ⟨79042, false, false, [], []⟩
      ]⟩,
    ⟨[30087, 91095], [30087, 91095], .contexts []⟩,
    ⟨[30087, 91095], [30087, 91095], .contexts []⟩,
    ⟨[91095, 1], [91095, 1], .contexts []⟩,
    ⟨[91095], [91095], .contexts []⟩,
    ⟨[91095, 1], [30087, 91095], .contexts [
        ⟨79070, false, false, [], []⟩,
        ⟨79066, true, false, [], [1]⟩,
        ⟨7, false, false, [91097], []⟩,
        ⟨11, false, false, [91097], []⟩,
        ⟨79067, false, false, [], [15]⟩,
        ⟨64196, false, false, [30087], []⟩,
        ⟨79068, false, false, [], []⟩,
        ⟨79069, false, false, [], []⟩,
        ⟨79071, false, false, [30087], []⟩,
        ⟨79051, true, false, [], [91095]⟩,
        ⟨79050, true, false, [], [91095]⟩,
        ⟨13, true, false, [], [30087, 91095]⟩
      ]⟩,
    ⟨[30097, 91097], [30097, 91097], .contexts []⟩,
    ⟨[30097, 91097], [30097, 91097], .contexts []⟩,
    ⟨[30097, 91095], [30097, 91095], .contexts []⟩,
    ⟨[30097, 91095], [30097, 91095], .contexts []⟩,
    ⟨[91095, 7], [91095, 7], .contexts []⟩,
    ⟨[91095, 7], [30097, 91095], .contexts [
        ⟨79077, false, false, [], []⟩,
        ⟨79066, true, false, [], [7]⟩,
        ⟨37, false, false, [91097], []⟩,
        ⟨40, false, false, [91097], []⟩,
        ⟨79061, false, false, [], [15]⟩,
        ⟨79065, false, false, [], [15]⟩,
        ⟨79073, false, false, [], [15]⟩,
        ⟨79074, false, false, [], [15]⟩,
        ⟨79074, false, false, [], [15]⟩,
        ⟨64196, false, false, [30097], []⟩,
        ⟨79075, false, false, [], []⟩,
        ⟨79076, false, false, [], []⟩,
        ⟨79071, false, false, [30097], []⟩,
        ⟨13, true, false, [], [30097, 91095]⟩
      ]⟩,
    ⟨[30093, 91097], [30093, 91097], .contexts []⟩,
    ⟨[30093, 91097], [30093, 91097], .contexts []⟩,
    ⟨[30093, 91095], [30093, 91095], .contexts []⟩,
    ⟨[30093, 91095], [30093, 91095], .contexts []⟩,
    ⟨[91095, 9], [91095, 9], .contexts []⟩,
    ⟨[91095, 9], [30093, 91095], .contexts [
        ⟨79083, false, false, [], []⟩,
        ⟨79066, true, false, [], [9]⟩,
        ⟨45, false, false, [91097], []⟩,
        ⟨48, false, false, [91097], []⟩,
        ⟨79057, false, false, [], [15]⟩,
        ⟨79079, false, false, [], [15]⟩,
        ⟨79080, false, false, [], [15]⟩,
        ⟨79080, false, false, [], [15]⟩,
        ⟨64196, false, false, [30093], []⟩,
        ⟨79081, false, false, [], []⟩,
        ⟨79082, false, false, [], []⟩,
        ⟨79071, false, false, [30093], []⟩,
        ⟨13, true, false, [], [30093, 91095]⟩
      ]⟩,
    ⟨[91095, 13], [91093], .contexts [
        ⟨64244, false, false, [], []⟩,
        ⟨64245, false, false, [], []⟩,
        ⟨64191, false, false, [], []⟩,
        ⟨64191, false, false, [], []⟩
      ]⟩,
    ⟨[91091, 13], [91091, 13], .contexts []⟩,
    ⟨[91091], [91091], .contexts []⟩,
    ⟨[91091, 13], [30089, 91091], .contexts [
        ⟨79086, false, false, [], []⟩,
        ⟨64188, true, false, [], [13]⟩,
        ⟨64192, true, false, [], [1, 13]⟩,
        ⟨79069, true, false, [30086], [13, 1, 13]⟩,
        ⟨79069, true, false, [30086], [13, 1, 13]⟩,
        ⟨79068, true, false, [30086], [13, 1, 13]⟩,
        ⟨79072, true, false, [30086], [13, 1, 13]⟩,
        ⟨79070, true, false, [30086], [13, 1, 13]⟩,
        ⟨919, false, false, [30086, 91095], []⟩,
        ⟨116, false, false, [30086, 91095], []⟩,
        ⟨79085, false, false, [30086], [1]⟩,
        ⟨64246, false, false, [30086], []⟩,
        ⟨64247, false, false, [30086], []⟩,
        ⟨64187, false, false, [30086], []⟩,
        ⟨64187, false, false, [30086], []⟩,
        ⟨79087, false, false, [30086], []⟩,
        ⟨79046, true, false, [], [91091]⟩
      ]⟩,
    ⟨[91095, 12], [91095, 13], .contexts [
        ⟨64, false, false, [91095], []⟩
      ]⟩,
    ⟨[91093, 7], [91093, 7], .contexts []⟩,
    ⟨[91093], [91093], .contexts []⟩,
    ⟨[30099], [30096], .source 15114⟩,
    ⟨[30096], [30096], .contexts []⟩,
    ⟨[30099], [30096], .contexts [
        ⟨79092, false, false, [], []⟩,
        ⟨79093, false, false, [], []⟩,
        ⟨79093, false, false, [], []⟩
      ]⟩,
    ⟨[91093, 7], [30099, 91093], .contexts [
        ⟨79090, false, false, [], []⟩,
        ⟨64192, true, false, [], [7]⟩,
        ⟨79076, true, false, [30096], [13, 7]⟩,
        ⟨79076, true, false, [30096], [13, 7]⟩,
        ⟨79075, true, false, [30096], [13, 7]⟩,
        ⟨79078, true, false, [30096], [13, 7]⟩,
        ⟨79077, true, false, [30096], [13, 7]⟩,
        ⟨518, false, false, [30096, 91095], []⟩,
        ⟨79089, false, false, [30096], []⟩,
        ⟨79085, false, false, [30096], []⟩,
        ⟨79091, false, false, [30096], []⟩,
        ⟨79094, true, false, [], [91093]⟩
      ]⟩,
    ⟨[30101], [30092], .source 15115⟩,
    ⟨[30092], [30092], .contexts []⟩,
    ⟨[91093, 9], [30101, 91093], .contexts [
        ⟨64192, true, false, [], [9]⟩,
        ⟨79082, true, false, [30092], [13, 9]⟩,
        ⟨79082, true, false, [30092], [13, 9]⟩,
        ⟨79081, true, false, [30092], [13, 9]⟩,
        ⟨79084, true, false, [30092], [13, 9]⟩,
        ⟨79083, true, false, [30092], [13, 9]⟩,
        ⟨511, false, false, [30092, 91095], []⟩,
        ⟨79089, false, false, [30092], []⟩,
        ⟨79085, false, false, [30092], []⟩,
        ⟨79091, false, false, [30092], []⟩,
        ⟨79097, true, false, [], [91093]⟩,
        ⟨79097, true, false, [], [91093]⟩,
        ⟨79096, true, false, [], [91093]⟩
      ]⟩,
    ⟨[30089, 91091], [30089, 91091], .contexts []⟩,
    ⟨[30089, 91091], [30089, 91091], .contexts []⟩,
    ⟨[91091, 11], [91089], .contexts [
        ⟨64249, false, false, [], []⟩,
        ⟨64250, false, false, [], []⟩,
        ⟨64183, false, false, [], []⟩,
        ⟨64183, false, false, [], []⟩
      ]⟩,
    ⟨[91091, 10], [91091, 11], .contexts [
        ⟨54, false, false, [91091], []⟩
      ]⟩,
    ⟨[91089, 13], [91089, 13], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1236. -/
def y322TCIndexRaw1236 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[91089], [91089], .contexts []⟩,
    ⟨[30088], [30088], .contexts []⟩,
    ⟨[30099, 91093], [30099, 91093], .contexts []⟩,
    ⟨[30099, 91093], [30099, 91093], .contexts []⟩,
    ⟨[91091, 7], [91091, 7], .contexts []⟩,
    ⟨[30098], [30098], .contexts []⟩,
    ⟨[30097], [30098], .contexts [
        ⟨79092, true, true, [], []⟩,
        ⟨79109, false, false, [], []⟩,
        ⟨79109, false, false, [], []⟩
      ]⟩,
    ⟨[91091, 7], [30097, 91091], .contexts [
        ⟨79108, false, false, [], []⟩,
        ⟨64188, true, false, [], [7]⟩,
        ⟨79107, true, false, [30098], [1, 7]⟩,
        ⟨79107, true, false, [30098], [1, 7]⟩,
        ⟨79106, true, false, [30098], [1, 7]⟩,
        ⟨79095, true, false, [30098], [1, 7]⟩,
        ⟨79090, true, false, [30098], [1, 7]⟩,
        ⟨502, false, false, [30098, 91093], []⟩,
        ⟨9, false, false, [30098, 91093], []⟩,
        ⟨64246, false, false, [30098], []⟩,
        ⟨64247, false, false, [30098], []⟩,
        ⟨64187, false, false, [30098], []⟩,
        ⟨64187, false, false, [30098], []⟩,
        ⟨79087, false, false, [30098], []⟩,
        ⟨79110, true, false, [], [91091]⟩
      ]⟩,
    ⟨[30087, 91089], [30087, 91089], .contexts []⟩,
    ⟨[91089, 13], [30087, 91089], .contexts [
        ⟨79103, false, false, [], []⟩,
        ⟨79103, false, false, [], []⟩,
        ⟨64184, true, false, [], [13]⟩,
        ⟨79100, true, false, [30088], [11, 13]⟩,
        ⟨79100, true, false, [30088], [11, 13]⟩,
        ⟨79099, true, false, [30088], [11, 13]⟩,
        ⟨79088, true, false, [30088], [11, 13]⟩,
        ⟨79086, true, false, [30088], [11, 13]⟩,
        ⟨931, false, false, [30088, 91091], []⟩,
        ⟨79102, false, false, [30088], []⟩,
        ⟨79101, false, false, [30088], []⟩,
        ⟨79104, false, false, [30088], []⟩,
        ⟨79105, true, false, [], [91089]⟩,
        ⟨79105, true, false, [], [91089]⟩,
        ⟨79048, true, false, [], [91089]⟩,
        ⟨79049, true, false, [], [91089]⟩,
        ⟨79112, false, false, [], []⟩,
        ⟨79112, false, false, [], []⟩
      ]⟩,
    ⟨[91089, 9], [91087], .contexts [
        ⟨64251, false, false, [], []⟩,
        ⟨64252, false, false, [], []⟩,
        ⟨64179, false, false, [], []⟩,
        ⟨64179, false, false, [], []⟩
      ]⟩,
    ⟨[91089, 8], [91089, 9], .contexts [
        ⟨47, false, false, [91089], []⟩
      ]⟩,
    ⟨[91087], [91087], .contexts []⟩,
    ⟨[91087, 13], [30089, 91087], .contexts [
        ⟨64180, true, false, [], [13]⟩,
        ⟨79113, true, false, [30086], [9, 13]⟩,
        ⟨942, false, false, [30086, 91089], []⟩,
        ⟨79115, false, false, [30086], []⟩,
        ⟨79114, false, false, [30086], []⟩,
        ⟨79116, false, false, [30086], []⟩,
        ⟨79046, true, false, [], [91087]⟩
      ]⟩,
    ⟨[30097, 91091], [30097, 91091], .contexts []⟩,
    ⟨[30097, 91091], [30097, 91091], .contexts []⟩,
    ⟨[91089, 7], [91089, 7], .contexts []⟩,
    ⟨[30099, 91089], [30099, 91089], .contexts []⟩,
    ⟨[91089, 7], [30099, 91089], .contexts [
        ⟨79120, false, false, [], []⟩,
        ⟨79120, false, false, [], []⟩,
        ⟨64184, true, false, [], [7]⟩,
        ⟨79119, true, false, [30096], [11, 7]⟩,
        ⟨79119, true, false, [30096], [11, 7]⟩,
        ⟨79118, true, false, [30096], [11, 7]⟩,
        ⟨79111, true, false, [30096], [11, 7]⟩,
        ⟨79108, true, false, [30096], [11, 7]⟩,
        ⟨555, false, false, [30096, 91091], []⟩,
        ⟨79102, false, false, [30096], []⟩,
        ⟨79101, false, false, [30096], []⟩,
        ⟨79104, false, false, [30096], []⟩,
        ⟨79094, true, false, [], [91089]⟩,
        ⟨79121, false, false, [], []⟩,
        ⟨79121, false, false, [], []⟩
      ]⟩,
    ⟨[91087, 7], [91087, 7], .contexts []⟩,
    ⟨[91087, 7], [30097, 91087], .contexts [
        ⟨79123, false, false, [], []⟩,
        ⟨64180, true, false, [], [7]⟩,
        ⟨79122, true, false, [30098], [9, 7]⟩,
        ⟨579, false, false, [30098, 91089], []⟩,
        ⟨79115, false, false, [30098], []⟩,
        ⟨79114, false, false, [30098], []⟩,
        ⟨79116, false, false, [30098], []⟩,
        ⟨79110, true, false, [], [91087]⟩
      ]⟩,
    ⟨[30097, 91087], [30097, 91087], .contexts []⟩,
    ⟨[30097, 91087], [30097, 91087], .contexts []⟩,
    ⟨[91087, 1], [91085], .contexts [
        ⟨64253, false, false, [], []⟩,
        ⟨64254, false, false, [], []⟩,
        ⟨64175, false, false, [], []⟩,
        ⟨64175, false, false, [], []⟩
      ]⟩,
    ⟨[91085], [91085], .contexts []⟩,
    ⟨[93415], [85335, 3], .source 46772⟩,
    ⟨[85335, 3], [93415], .contexts [
        ⟨79129, true, false, [], []⟩
      ]⟩,
    ⟨[93415, 3], [85335], .contexts [
        ⟨79130, true, false, [], [3]⟩,
        ⟨20, false, false, [85335], []⟩,
        ⟨31485, false, false, [], []⟩
      ]⟩,
    ⟨[93415], [93415], .contexts []⟩,
    ⟨[93415], [93415], .contexts []⟩,
    ⟨[85335, 3], [93415], .contexts [
        ⟨79130, false, false, [], []⟩,
        ⟨79132, false, false, [], []⟩,
        ⟨79133, false, false, [], []⟩,
        ⟨79133, false, false, [], []⟩
      ]⟩,
    ⟨[2909, 93415], [2909, 93415], .contexts []⟩,
    ⟨[2909, 93415], [2909, 93415], .contexts []⟩,
    ⟨[93415, 5], [93415, 5], .contexts []⟩,
    ⟨[93415], [93415], .contexts []⟩,
    ⟨[93415, 5], [2909, 93415], .contexts [
        ⟨79137, false, false, [], []⟩,
        ⟨79134, true, false, [], [5]⟩,
        ⟨871, false, false, [85335], []⟩,
        ⟨873, false, false, [85335], []⟩,
        ⟨31482, false, false, [], [3, 5, 3]⟩,
        ⟨31394, false, false, [], [3, 5, 3]⟩,
        ⟨31395, false, false, [], [3, 5, 3]⟩,
        ⟨31395, false, false, [], [3, 5, 3]⟩,
        ⟨31521, false, false, [], [5, 3]⟩,
        ⟨31400, false, false, [], [5, 3]⟩,
        ⟨31401, false, false, [], [5, 3]⟩,
        ⟨31401, false, false, [], [5, 3]⟩,
        ⟨31481, false, false, [2909], [3]⟩,
        ⟨79130, false, false, [2909], []⟩,
        ⟨79135, false, false, [], []⟩,
        ⟨79136, false, false, [], []⟩,
        ⟨79138, false, false, [2909], []⟩
      ]⟩,
    ⟨[93415, 5], [2909, 93415], .contexts [
        ⟨79139, false, false, [], []⟩,
        ⟨6108, true, false, [], [93415]⟩
      ]⟩,
    ⟨[2939, 93415], [2939, 93415], .contexts []⟩,
    ⟨[2939, 93415], [2939, 93415], .contexts []⟩,
    ⟨[93415, 7], [93415, 7], .contexts []⟩,
    ⟨[93415, 7], [2939, 93415], .contexts [
        ⟨79143, false, false, [], []⟩,
        ⟨79134, true, false, [], [7]⟩,
        ⟨140, false, false, [85335], []⟩,
        ⟨141, false, false, [85335], []⟩,
        ⟨31493, false, false, [], [3]⟩,
        ⟨31496, false, false, [], [3]⟩,
        ⟨31491, false, false, [], [3]⟩,
        ⟨31492, false, false, [], [3]⟩,
        ⟨31492, false, false, [], [3]⟩,
        ⟨79130, false, false, [2939], []⟩,
        ⟨79141, false, false, [], []⟩,
        ⟨79142, false, false, [], []⟩,
        ⟨79138, false, false, [2939], []⟩,
        ⟨31495, true, false, [], [93415]⟩
      ]⟩,
    ⟨[13035, 93415], [13035, 93415], .contexts []⟩,
    ⟨[13035, 93415], [13035, 93415], .contexts []⟩,
    ⟨[93415, 9], [13035, 93415], .contexts [
        ⟨79134, true, false, [], [9]⟩,
        ⟨669, false, false, [85335], []⟩,
        ⟨670, false, false, [85335], []⟩,
        ⟨31500, false, false, [], [3]⟩,
        ⟨31501, false, false, [], [3]⟩,
        ⟨31498, false, false, [], [3]⟩,
        ⟨31499, false, false, [], [3]⟩,
        ⟨31499, false, false, [], [3]⟩,
        ⟨79130, false, false, [13035], []⟩,
        ⟨79145, false, false, [], []⟩,
        ⟨79146, false, false, [], []⟩,
        ⟨79138, false, false, [13035], []⟩,
        ⟨31408, true, false, [], [93415]⟩
      ]⟩,
    ⟨[1369, 93415], [1369, 93415], .contexts []⟩,
    ⟨[1369, 93415], [1369, 93415], .contexts []⟩,
    ⟨[93415, 11], [93415, 11], .contexts []⟩,
    ⟨[93415, 11], [1369, 93415], .contexts [
        ⟨79150, false, false, [], []⟩,
        ⟨79134, true, false, [], [11]⟩,
        ⟨144, false, false, [85335], []⟩,
        ⟨145, false, false, [85335], []⟩,
        ⟨31505, false, false, [], [3]⟩,
        ⟨31506, false, false, [], [3]⟩,
        ⟨31503, false, false, [], [3]⟩,
        ⟨31504, false, false, [], [3]⟩,
        ⟨31504, false, false, [], [3]⟩,
        ⟨79130, false, false, [1369], []⟩,
        ⟨79148, false, false, [], []⟩,
        ⟨79149, false, false, [], []⟩,
        ⟨79138, false, false, [1369], []⟩,
        ⟨3620, true, false, [], [93415]⟩
      ]⟩,
    ⟨[11513, 93415], [11513, 93415], .contexts []⟩,
    ⟨[11513, 93415], [11513, 93415], .contexts []⟩,
    ⟨[93415, 13], [11513, 93415], .contexts [
        ⟨79134, true, false, [], [13]⟩,
        ⟨147, false, false, [85335], []⟩,
        ⟨148, false, false, [85335], []⟩,
        ⟨31510, false, false, [], [3]⟩,
        ⟨31511, false, false, [], [3]⟩,
        ⟨31508, false, false, [], [3]⟩,
        ⟨31509, false, false, [], [3]⟩,
        ⟨31509, false, false, [], [3]⟩,
        ⟨79130, false, false, [11513], []⟩,
        ⟨79152, false, false, [], []⟩,
        ⟨79153, false, false, [], []⟩,
        ⟨79138, false, false, [11513], []⟩,
        ⟨31417, true, false, [], [93415]⟩
      ]⟩,
    ⟨[93417], [93415, 1], .source 46773⟩,
    ⟨[93415, 1], [93417], .contexts [
        ⟨79155, true, false, [], []⟩
      ]⟩,
    ⟨[93417, 1], [93415], .contexts [
        ⟨79156, true, false, [], [1]⟩,
        ⟨8, false, false, [93415], []⟩,
        ⟨79133, false, false, [], []⟩
      ]⟩,
    ⟨[93417], [93417], .contexts []⟩,
    ⟨[93417], [93417], .contexts []⟩,
    ⟨[93415, 1], [93417], .contexts [
        ⟨79156, false, false, [], []⟩,
        ⟨79158, false, false, [], []⟩,
        ⟨79159, false, false, [], []⟩,
        ⟨79159, false, false, [], []⟩
      ]⟩,
    ⟨[30103], [1369, 29141], .source 15116⟩,
    ⟨[30103, 92831], [30103, 92831], .contexts []⟩,
    ⟨[30103, 92831], [30103, 92831], .contexts []⟩,
    ⟨[93417, 3], [93417, 3], .contexts []⟩,
    ⟨[93417, 3], [30103, 92831], .contexts [
        ⟨79164, false, false, [], []⟩,
        ⟨79160, true, false, [], [3]⟩,
        ⟨1098, false, false, [93415], []⟩,
        ⟨1100, false, false, [93415], []⟩,
        ⟨79131, false, false, [], [1, 3, 1]⟩,
        ⟨31484, false, false, [], [1, 3, 1]⟩,
        ⟨31485, false, false, [], [1, 3, 1]⟩,
        ⟨31485, false, false, [], [1, 3, 1]⟩,
        ⟨31488, false, false, [], [3, 1]⟩,
        ⟨31434, false, false, [], [3, 1]⟩,
        ⟨31436, false, false, [], [3, 1]⟩,
        ⟨31436, false, false, [], [3, 1]⟩,
        ⟨75702, false, false, [1369], [1]⟩,
        ⟨79161, true, false, [], [92829, 1]⟩,
        ⟨75710, false, false, [30103], []⟩,
        ⟨79162, false, false, [], []⟩,
        ⟨79163, false, false, [], []⟩
      ]⟩,
    ⟨[30103], [30103], .contexts [
        ⟨13, false, false, [], [30103]⟩
      ]⟩,
    ⟨[93417, 3], [30103, 92831], .contexts [
        ⟨79165, false, false, [], []⟩,
        ⟨79166, true, false, [], [92831]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1237. -/
def y322TCIndexRaw1237 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[30105], [30102], .source 15117⟩,
    ⟨[2909, 93417], [2909, 93417], .contexts []⟩,
    ⟨[2909, 93417], [2909, 93417], .contexts []⟩,
    ⟨[93417, 5], [93417, 5], .contexts []⟩,
    ⟨[93417], [93417], .contexts []⟩,
    ⟨[93417, 5], [2909, 93417], .contexts [
        ⟨79171, false, false, [], []⟩,
        ⟨79160, true, false, [], [5]⟩,
        ⟨98, false, false, [93415], []⟩,
        ⟨99, false, false, [93415], []⟩,
        ⟨79137, false, false, [], [1]⟩,
        ⟨79140, false, false, [], [1]⟩,
        ⟨79135, false, false, [], [1]⟩,
        ⟨79136, false, false, [], [1]⟩,
        ⟨79136, false, false, [], [1]⟩,
        ⟨79156, false, false, [2909], []⟩,
        ⟨79169, false, false, [], []⟩,
        ⟨79170, false, false, [], []⟩,
        ⟨79172, false, false, [2909], []⟩,
        ⟨6108, true, false, [], [93417]⟩
      ]⟩,
    ⟨[2939, 93417], [2939, 93417], .contexts []⟩,
    ⟨[2939, 93417], [2939, 93417], .contexts []⟩,
    ⟨[93417, 7], [93417, 7], .contexts []⟩,
    ⟨[93417, 7], [2939, 93417], .contexts [
        ⟨79176, false, false, [], []⟩,
        ⟨79160, true, false, [], [7]⟩,
        ⟨104, false, false, [93415], []⟩,
        ⟨105, false, false, [93415], []⟩,
        ⟨79143, false, false, [], [1]⟩,
        ⟨79144, false, false, [], [1]⟩,
        ⟨79141, false, false, [], [1]⟩,
        ⟨79142, false, false, [], [1]⟩,
        ⟨79142, false, false, [], [1]⟩,
        ⟨79156, false, false, [2939], []⟩,
        ⟨79174, false, false, [], []⟩,
        ⟨79175, false, false, [], []⟩,
        ⟨79172, false, false, [2939], []⟩,
        ⟨31495, true, false, [], [93417]⟩
      ]⟩,
    ⟨[1369, 93417], [1369, 93417], .contexts []⟩,
    ⟨[1369, 93417], [1369, 93417], .contexts []⟩,
    ⟨[93417, 11], [93417, 11], .contexts []⟩,
    ⟨[93417, 11], [1369, 93417], .contexts [
        ⟨79180, false, false, [], []⟩,
        ⟨79160, true, false, [], [11]⟩,
        ⟨110, false, false, [93415], []⟩,
        ⟨111, false, false, [93415], []⟩,
        ⟨79150, false, false, [], [1]⟩,
        ⟨79151, false, false, [], [1]⟩,
        ⟨79148, false, false, [], [1]⟩,
        ⟨79149, false, false, [], [1]⟩,
        ⟨79149, false, false, [], [1]⟩,
        ⟨79156, false, false, [1369], []⟩,
        ⟨79178, false, false, [], []⟩,
        ⟨79179, false, false, [], []⟩,
        ⟨79172, false, false, [1369], []⟩,
        ⟨3620, true, false, [], [93417]⟩
      ]⟩,
    ⟨[93419], [93417, 9], .source 46774⟩,
    ⟨[93417, 9], [93419], .contexts [
        ⟨79182, true, false, [], []⟩
      ]⟩,
    ⟨[93419, 9], [93417], .contexts [
        ⟨79183, true, false, [], [9]⟩,
        ⟨46, false, false, [93417], []⟩,
        ⟨79159, false, false, [], []⟩
      ]⟩,
    ⟨[93419], [93419], .contexts []⟩,
    ⟨[93419], [93419], .contexts []⟩,
    ⟨[93417, 9], [93419], .contexts [
        ⟨79183, false, false, [], []⟩,
        ⟨79185, false, false, [], []⟩,
        ⟨79186, false, false, [], []⟩,
        ⟨79186, false, false, [], []⟩
      ]⟩,
    ⟨[93417, 1], [93415], .contexts [
        ⟨79157, false, false, [], []⟩,
        ⟨79132, false, false, [], []⟩,
        ⟨79133, false, false, [], []⟩,
        ⟨79133, false, false, [], []⟩
      ]⟩,
    ⟨[13035, 93419], [13035, 93419], .contexts []⟩,
    ⟨[13035, 93419], [13035, 93419], .contexts []⟩,
    ⟨[93419, 1], [93419, 1], .contexts []⟩,
    ⟨[93419], [93419], .contexts []⟩,
    ⟨[93419, 1], [13035, 93419], .contexts [
        ⟨79191, false, false, [], []⟩,
        ⟨79187, true, false, [], [1]⟩,
        ⟨691, false, false, [93417], []⟩,
        ⟨694, false, false, [93417], []⟩,
        ⟨79188, false, false, [], [9, 1, 9]⟩,
        ⟨79147, false, false, [], [1, 9]⟩,
        ⟨79145, false, false, [], [1, 9]⟩,
        ⟨79146, false, false, [], [1, 9]⟩,
        ⟨79146, false, false, [], [1, 9]⟩,
        ⟨79156, false, false, [13035], [9]⟩,
        ⟨79183, false, false, [13035], []⟩,
        ⟨79189, false, false, [], []⟩,
        ⟨79190, false, false, [], []⟩,
        ⟨79192, false, false, [13035], []⟩,
        ⟨31408, true, false, [], [93419]⟩
      ]⟩,
    ⟨[30103, 92833], [30103, 92833], .contexts []⟩,
    ⟨[30103, 92833], [30103, 92833], .contexts []⟩,
    ⟨[93419, 3], [93419, 3], .contexts []⟩,
    ⟨[93419, 3], [30103, 92833], .contexts [
        ⟨79196, false, false, [], []⟩,
        ⟨79187, true, false, [], [3]⟩,
        ⟨196, false, false, [93417], []⟩,
        ⟨197, false, false, [93417], []⟩,
        ⟨79164, false, false, [], [9]⟩,
        ⟨79167, false, false, [], [9]⟩,
        ⟨79162, false, false, [], [9]⟩,
        ⟨79163, false, false, [], [9]⟩,
        ⟨79163, false, false, [], [9]⟩,
        ⟨75713, false, false, [30103], []⟩,
        ⟨79194, false, false, [], []⟩,
        ⟨79195, false, false, [], []⟩,
        ⟨75722, false, false, [30103], []⟩,
        ⟨79166, true, false, [], [92833]⟩
      ]⟩,
    ⟨[93417, 5], [2909, 93417], .contexts [
        ⟨79171, false, false, [], []⟩,
        ⟨79173, false, false, [], []⟩,
        ⟨79169, false, false, [], []⟩,
        ⟨79170, false, false, [], []⟩,
        ⟨79170, false, false, [], []⟩
      ]⟩,
    ⟨[2909, 93419], [2909, 93419], .contexts []⟩,
    ⟨[2909, 93419], [2909, 93419], .contexts []⟩,
    ⟨[93419, 5], [93419, 5], .contexts []⟩,
    ⟨[93419, 5], [2909, 93419], .contexts [
        ⟨79201, false, false, [], []⟩,
        ⟨79187, true, false, [], [5]⟩,
        ⟨1079, false, false, [93417], []⟩,
        ⟨1080, false, false, [93417], []⟩,
        ⟨79198, false, false, [], [9]⟩,
        ⟨79183, false, false, [2909], []⟩,
        ⟨79199, false, false, [], []⟩,
        ⟨79200, false, false, [], []⟩,
        ⟨79192, false, false, [2909], []⟩,
        ⟨6108, true, false, [], [93419]⟩
      ]⟩,
    ⟨[2939, 93419], [2939, 93419], .contexts []⟩,
    ⟨[2939, 93419], [2939, 93419], .contexts []⟩,
    ⟨[93419, 7], [93419, 7], .contexts []⟩,
    ⟨[93419, 7], [2939, 93419], .contexts [
        ⟨79205, false, false, [], []⟩,
        ⟨79187, true, false, [], [7]⟩,
        ⟨1084, false, false, [93417], []⟩,
        ⟨1085, false, false, [93417], []⟩,
        ⟨79176, false, false, [], [9]⟩,
        ⟨79177, false, false, [], [9]⟩,
        ⟨79174, false, false, [], [9]⟩,
        ⟨79175, false, false, [], [9]⟩,
        ⟨79175, false, false, [], [9]⟩,
        ⟨79183, false, false, [2939], []⟩,
        ⟨79203, false, false, [], []⟩,
        ⟨79204, false, false, [], []⟩,
        ⟨79192, false, false, [2939], []⟩,
        ⟨31495, true, false, [], [93419]⟩
      ]⟩,
    ⟨[93421], [93419, 11], .source 46775⟩,
    ⟨[93419, 11], [93421], .contexts [
        ⟨79207, true, false, [], []⟩
      ]⟩,
    ⟨[93421, 11], [93419], .contexts [
        ⟨79208, true, false, [], [11]⟩,
        ⟨53, false, false, [93419], []⟩,
        ⟨79186, false, false, [], []⟩
      ]⟩,
    ⟨[93421], [93421], .contexts []⟩,
    ⟨[93421], [93421], .contexts []⟩,
    ⟨[93419, 11], [93421], .contexts [
        ⟨79208, false, false, [], []⟩,
        ⟨79210, false, false, [], []⟩,
        ⟨79211, false, false, [], []⟩,
        ⟨79211, false, false, [], []⟩
      ]⟩,
    ⟨[93419, 1], [13035, 93419], .contexts [
        ⟨79191, false, false, [], []⟩,
        ⟨79193, false, false, [], []⟩,
        ⟨79189, false, false, [], []⟩,
        ⟨79190, false, false, [], []⟩,
        ⟨79190, false, false, [], []⟩
      ]⟩,
    ⟨[13035, 93421], [13035, 93421], .contexts []⟩,
    ⟨[93421], [93421], .contexts []⟩,
    ⟨[93421, 1], [13035, 93421], .contexts [
        ⟨79212, true, false, [], [1]⟩,
        ⟨562, false, false, [93419], []⟩,
        ⟨563, false, false, [93419], []⟩,
        ⟨79213, false, false, [], [11]⟩,
        ⟨79208, false, false, [13035], []⟩,
        ⟨79214, false, false, [], []⟩,
        ⟨79215, false, false, [13035], []⟩,
        ⟨31408, true, false, [], [93421]⟩
      ]⟩,
    ⟨[93419, 3], [30103, 92833], .contexts [
        ⟨79196, false, false, [], []⟩,
        ⟨79197, false, false, [], []⟩,
        ⟨79194, false, false, [], []⟩,
        ⟨79195, false, false, [], []⟩,
        ⟨79195, false, false, [], []⟩
      ]⟩,
    ⟨[30107], [30103, 16177], .source 15118⟩,
    ⟨[93421, 3], [93421, 3], .contexts []⟩,
    ⟨[30107], [30107], .contexts []⟩,
    ⟨[30107], [30107], .contexts []⟩,
    ⟨[30107], [30107], .contexts [
        ⟨13, false, false, [], [30107]⟩,
        ⟨79220, false, false, [], []⟩,
        ⟨79221, false, false, [], []⟩
      ]⟩,
    ⟨[93421, 3], [30107, 92193], .contexts [
        ⟨79219, false, false, [], []⟩,
        ⟨79212, true, false, [], [3]⟩,
        ⟨215, false, false, [93419], []⟩,
        ⟨216, false, false, [93419], []⟩,
        ⟨79217, false, false, [], [11]⟩,
        ⟨75732, false, false, [30103], []⟩,
        ⟨79218, true, false, [], [92193]⟩,
        ⟨70619, false, false, [30107], []⟩,
        ⟨79222, true, false, [], [92193]⟩
      ]⟩,
    ⟨[30109], [30106], .source 15119⟩,
    ⟨[92193, 3], [30109, 93421], .contexts [
        ⟨79223, true, false, [30106], [3]⟩,
        ⟨20, false, false, [30106, 93421], []⟩,
        ⟨79224, true, false, [], [93421]⟩
      ]⟩,
    ⟨[2909, 93421], [2909, 93421], .contexts []⟩,
    ⟨[2909, 93421], [2909, 93421], .contexts []⟩,
    ⟨[93421, 5], [93421, 5], .contexts []⟩,
    ⟨[93421, 5], [2909, 93421], .contexts [
        ⟨79228, false, false, [], []⟩,
        ⟨79212, true, false, [], [5]⟩,
        ⟨642, false, false, [93419], []⟩,
        ⟨643, false, false, [93419], []⟩,
        ⟨79201, false, false, [], [11]⟩,
        ⟨79202, false, false, [], [11]⟩,
        ⟨79199, false, false, [], [11]⟩,
        ⟨79200, false, false, [], [11]⟩,
        ⟨79200, false, false, [], [11]⟩,
        ⟨79208, false, false, [2909], []⟩,
        ⟨79226, false, false, [], []⟩,
        ⟨79227, false, false, [], []⟩,
        ⟨79215, false, false, [2909], []⟩,
        ⟨6108, true, false, [], [93421]⟩
      ]⟩,
    ⟨[2939, 93421], [2939, 93421], .contexts []⟩,
    ⟨[2939, 93421], [2939, 93421], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1238. -/
def y322TCIndexRaw1238 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93421, 7], [93421, 7], .contexts []⟩,
    ⟨[93421, 7], [2939, 93421], .contexts [
        ⟨79232, false, false, [], []⟩,
        ⟨79212, true, false, [], [7]⟩,
        ⟨647, false, false, [93419], []⟩,
        ⟨648, false, false, [93419], []⟩,
        ⟨79205, false, false, [], [11]⟩,
        ⟨79206, false, false, [], [11]⟩,
        ⟨79203, false, false, [], [11]⟩,
        ⟨79204, false, false, [], [11]⟩,
        ⟨79204, false, false, [], [11]⟩,
        ⟨79208, false, false, [2939], []⟩,
        ⟨79230, false, false, [], []⟩,
        ⟨79231, false, false, [], []⟩,
        ⟨79215, false, false, [2939], []⟩,
        ⟨31495, true, false, [], [93421]⟩
      ]⟩,
    ⟨[93417, 11], [1369, 93417], .contexts [
        ⟨79181, false, false, [], []⟩
      ]⟩,
    ⟨[1369, 93421], [1369, 93421], .contexts []⟩,
    ⟨[1369, 93421], [1369, 93421], .contexts []⟩,
    ⟨[93421, 9], [93421, 9], .contexts []⟩,
    ⟨[93421, 9], [1369, 93421], .contexts [
        ⟨79237, false, false, [], []⟩,
        ⟨79212, true, false, [], [9]⟩,
        ⟨221, false, false, [93419], []⟩,
        ⟨224, false, false, [93419], []⟩,
        ⟨79184, false, false, [], [11, 9, 11]⟩,
        ⟨79158, false, false, [], [11, 9, 11]⟩,
        ⟨79159, false, false, [], [11, 9, 11]⟩,
        ⟨79159, false, false, [], [11, 9, 11]⟩,
        ⟨79234, false, false, [], [9, 11]⟩,
        ⟨79178, false, false, [], [9, 11]⟩,
        ⟨79179, false, false, [], [9, 11]⟩,
        ⟨79179, false, false, [], [9, 11]⟩,
        ⟨79183, false, false, [1369], [11]⟩,
        ⟨79208, false, false, [1369], []⟩,
        ⟨79235, false, false, [], []⟩,
        ⟨79236, false, false, [], []⟩,
        ⟨79215, false, false, [1369], []⟩
      ]⟩,
    ⟨[93421, 9], [1369, 93421], .contexts [
        ⟨79238, false, false, [], []⟩,
        ⟨3620, true, false, [], [93421]⟩
      ]⟩,
    ⟨[93423], [93421, 13], .source 46776⟩,
    ⟨[93421, 13], [93423], .contexts [
        ⟨79240, true, false, [], []⟩
      ]⟩,
    ⟨[93423, 13], [93421], .contexts [
        ⟨79241, true, false, [], [13]⟩,
        ⟨59, false, false, [93421], []⟩,
        ⟨79211, false, false, [], []⟩
      ]⟩,
    ⟨[93421, 13], [93423], .contexts [
        ⟨79241, false, false, [], []⟩
      ]⟩,
    ⟨[93423], [93423], .contexts []⟩,
    ⟨[93423], [93423], .contexts []⟩,
    ⟨[93421, 13], [93423], .contexts [
        ⟨79243, false, false, [], []⟩,
        ⟨79244, false, false, [], []⟩,
        ⟨79245, false, false, [], []⟩,
        ⟨79245, false, false, [], []⟩
      ]⟩,
    ⟨[30107, 92193], [30107, 92193], .contexts []⟩,
    ⟨[30107, 92193], [30107, 92193], .contexts []⟩,
    ⟨[30107, 92195], [30107, 92195], .contexts []⟩,
    ⟨[30107, 92195], [30107, 92195], .contexts []⟩,
    ⟨[93423, 3], [93423, 3], .contexts []⟩,
    ⟨[93423, 3], [30107, 92195], .contexts [
        ⟨79251, false, false, [], []⟩,
        ⟨79246, true, false, [], [3]⟩,
        ⟨63, false, false, [93421], []⟩,
        ⟨65, false, false, [93421], []⟩,
        ⟨79219, false, false, [], [13]⟩,
        ⟨79223, false, false, [], [13]⟩,
        ⟨79247, false, false, [], [13]⟩,
        ⟨79248, false, false, [], [13]⟩,
        ⟨79248, false, false, [], [13]⟩,
        ⟨70634, false, false, [30107], []⟩,
        ⟨79249, false, false, [], []⟩,
        ⟨79250, false, false, [], []⟩,
        ⟨70640, false, false, [30107], []⟩,
        ⟨79222, true, false, [], [92195]⟩
      ]⟩,
    ⟨[93423], [93423], .contexts []⟩,
    ⟨[93425], [93423, 15], .source 46777⟩,
    ⟨[93423, 15], [93425], .contexts [
        ⟨79254, true, false, [], []⟩
      ]⟩,
    ⟨[93425, 15], [93423], .contexts [
        ⟨79255, true, false, [], [15]⟩,
        ⟨1, false, false, [93423], []⟩,
        ⟨79245, false, false, [], []⟩
      ]⟩,
    ⟨[93425], [93425], .contexts []⟩,
    ⟨[93425], [93425], .contexts []⟩,
    ⟨[30107, 92197], [30107, 92197], .contexts []⟩,
    ⟨[30107, 92197], [30107, 92197], .contexts []⟩,
    ⟨[93425, 3], [30107, 92197], .contexts [
        ⟨79258, true, false, [], [3]⟩,
        ⟨79258, true, false, [], [3]⟩,
        ⟨79257, true, false, [], [3]⟩,
        ⟨79255, true, false, [], [3]⟩,
        ⟨19, false, false, [93423], []⟩,
        ⟨22, false, false, [93423], []⟩,
        ⟨79251, false, false, [], [15]⟩,
        ⟨79252, false, false, [], [15]⟩,
        ⟨79249, false, false, [], [15]⟩,
        ⟨79250, false, false, [], [15]⟩,
        ⟨79250, false, false, [], [15]⟩,
        ⟨70645, false, false, [30107], []⟩,
        ⟨79259, false, false, [], []⟩,
        ⟨79260, false, false, [], []⟩,
        ⟨70650, false, false, [30107], []⟩,
        ⟨79222, true, false, [], [92197]⟩
      ]⟩,
    ⟨[93427], [93425, 1], .source 46778⟩,
    ⟨[93427, 1], [93425], .contexts [
        ⟨79262, false, false, [], [1]⟩,
        ⟨8, false, false, [93425], []⟩,
        ⟨79258, false, false, [], []⟩
      ]⟩,
    ⟨[93429], [93427, 3], .source 46779⟩,
    ⟨[93427, 3], [93429], .contexts [
        ⟨79264, true, false, [], []⟩
      ]⟩,
    ⟨[93429], [93429], .contexts []⟩,
    ⟨[30107, 92201], [30107, 92201], .contexts []⟩,
    ⟨[30107, 92201], [30107, 92201], .contexts []⟩,
    ⟨[93429, 1], [93429, 1], .contexts []⟩,
    ⟨[93429, 1], [30107, 92201], .contexts [
        ⟨79269, false, false, [], []⟩,
        ⟨79266, true, false, [], [1]⟩,
        ⟨79266, true, false, [], [1]⟩,
        ⟨79265, true, false, [], [1]⟩,
        ⟨130, false, false, [93427], []⟩,
        ⟨133, false, false, [93427], []⟩,
        ⟨79263, false, false, [], [3, 1, 3]⟩,
        ⟨79257, false, false, [], [3, 1, 3]⟩,
        ⟨79258, false, false, [], [3, 1, 3]⟩,
        ⟨79258, false, false, [], [3, 1, 3]⟩,
        ⟨79261, false, false, [], [1, 3]⟩,
        ⟨79259, false, false, [], [1, 3]⟩,
        ⟨79260, false, false, [], [1, 3]⟩,
        ⟨79260, false, false, [], [1, 3]⟩,
        ⟨70655, false, false, [30107], [3]⟩,
        ⟨70660, false, false, [30107], []⟩,
        ⟨79267, false, false, [], []⟩,
        ⟨79268, false, false, [], []⟩,
        ⟨70663, false, false, [30107], []⟩
      ]⟩,
    ⟨[93429, 1], [30107, 92201], .contexts [
        ⟨79270, false, false, [], []⟩,
        ⟨79222, true, false, [], [92201]⟩
      ]⟩,
    ⟨[30106], [30106], .contexts []⟩,
    ⟨[92205, 5], [30109, 93429], .contexts [
        ⟨70667, true, false, [], [5]⟩,
        ⟨70665, true, false, [], [1, 5]⟩,
        ⟨79268, true, false, [30106], [5, 1, 5]⟩,
        ⟨79268, true, false, [30106], [5, 1, 5]⟩,
        ⟨79267, true, false, [30106], [5, 1, 5]⟩,
        ⟨79271, true, false, [30106], [5, 1, 5]⟩,
        ⟨79269, true, false, [30106], [5, 1, 5]⟩,
        ⟨1152, false, false, [30106, 93429], []⟩,
        ⟨79272, true, false, [], [93429]⟩,
        ⟨79272, true, false, [], [93429]⟩,
        ⟨79224, true, false, [], [93429]⟩
      ]⟩,
    ⟨[30109, 93429], [30109, 93429], .contexts []⟩,
    ⟨[30109, 93429], [30109, 93429], .contexts []⟩,
    ⟨[30111], [30109, 2909], .source 15120⟩,
    ⟨[30113], [30111, 30107], .source 15121⟩,
    ⟨[30115], [30112], .source 15122⟩,
    ⟨[30112], [30112], .contexts []⟩,
    ⟨[93431], [92203, 9], .source 46780⟩,
    ⟨[92203, 9], [93431], .contexts [
        ⟨79280, true, false, [], []⟩
      ]⟩,
    ⟨[93433], [93431, 11], .source 46781⟩,
    ⟨[93431, 11], [93433], .contexts [
        ⟨79282, true, false, [], []⟩
      ]⟩,
    ⟨[93431], [93431], .contexts []⟩,
    ⟨[93435], [93433, 1], .source 46782⟩,
    ⟨[93433, 1], [93435], .contexts [
        ⟨79285, true, false, [], []⟩
      ]⟩,
    ⟨[93433], [93433], .contexts []⟩,
    ⟨[93435, 1], [93433], .contexts [
        ⟨79286, true, false, [], [1]⟩,
        ⟨8, false, false, [93433], []⟩,
        ⟨79287, false, false, [], []⟩
      ]⟩,
    ⟨[93437], [93435, 13], .source 46783⟩,
    ⟨[93435, 13], [93437], .contexts [
        ⟨79289, true, false, [], []⟩
      ]⟩,
    ⟨[93435], [93435], .contexts []⟩,
    ⟨[93439], [93437, 15], .source 46784⟩,
    ⟨[93437, 15], [93439], .contexts [
        ⟨79292, true, false, [], []⟩
      ]⟩,
    ⟨[93437], [93437], .contexts []⟩,
    ⟨[93441], [93439, 1], .source 46785⟩]

/-- Exact literal claimed equations and contextual derivations, block 1239. -/
def y322TCIndexRaw1239 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93439, 1], [93441], .contexts [
        ⟨79295, true, false, [], []⟩
      ]⟩,
    ⟨[93439], [93439], .contexts []⟩,
    ⟨[93443], [93441, 3], .source 46786⟩,
    ⟨[93441, 3], [93443], .contexts [
        ⟨79298, true, false, [], []⟩
      ]⟩,
    ⟨[93441], [93441], .contexts []⟩,
    ⟨[93445], [93443, 5], .source 46787⟩,
    ⟨[93443, 5], [93445], .contexts [
        ⟨79301, true, false, [], []⟩
      ]⟩,
    ⟨[93443], [93443], .contexts []⟩,
    ⟨[93447], [93445, 1], .source 46788⟩,
    ⟨[93445, 1], [93447], .contexts [
        ⟨79304, true, false, [], []⟩
      ]⟩,
    ⟨[93445], [93445], .contexts []⟩,
    ⟨[93449], [93447, 9], .source 46789⟩,
    ⟨[93447, 9], [93449], .contexts [
        ⟨79307, true, false, [], []⟩
      ]⟩,
    ⟨[93447], [93447], .contexts []⟩,
    ⟨[93451], [93449, 11], .source 46790⟩,
    ⟨[93449, 11], [93451], .contexts [
        ⟨79310, true, false, [], []⟩
      ]⟩,
    ⟨[93449], [93449], .contexts []⟩,
    ⟨[93453], [93451, 1], .source 46791⟩,
    ⟨[93451, 1], [93453], .contexts [
        ⟨79313, true, false, [], []⟩
      ]⟩,
    ⟨[93451], [93451], .contexts []⟩,
    ⟨[93455], [93453, 13], .source 46792⟩,
    ⟨[93453, 13], [93455], .contexts [
        ⟨79316, true, false, [], []⟩
      ]⟩,
    ⟨[93453], [93453], .contexts []⟩,
    ⟨[93455, 13], [93453], .contexts [
        ⟨79317, true, false, [], [13]⟩,
        ⟨59, false, false, [93453], []⟩,
        ⟨79318, false, false, [], []⟩
      ]⟩,
    ⟨[93457], [93455, 15], .source 46793⟩,
    ⟨[93455, 15], [93457], .contexts [
        ⟨79320, true, false, [], []⟩
      ]⟩,
    ⟨[93455], [93455], .contexts []⟩,
    ⟨[93457, 15], [93455], .contexts [
        ⟨79321, true, false, [], [15]⟩,
        ⟨1, false, false, [93455], []⟩,
        ⟨79322, false, false, [], []⟩
      ]⟩,
    ⟨[93459], [93457, 1], .source 46794⟩,
    ⟨[93457, 1], [93459], .contexts [
        ⟨79324, true, false, [], []⟩
      ]⟩,
    ⟨[93457], [93457], .contexts []⟩,
    ⟨[93459, 1], [93457], .contexts [
        ⟨79325, true, false, [], [1]⟩,
        ⟨8, false, false, [93457], []⟩,
        ⟨79326, false, false, [], []⟩
      ]⟩,
    ⟨[93461], [93459, 3], .source 46795⟩,
    ⟨[93459, 3], [93461], .contexts [
        ⟨79328, true, false, [], []⟩
      ]⟩,
    ⟨[93459], [93459], .contexts []⟩,
    ⟨[93461, 3], [93459], .contexts [
        ⟨79329, true, false, [], [3]⟩,
        ⟨20, false, false, [93459], []⟩,
        ⟨79330, false, false, [], []⟩
      ]⟩,
    ⟨[93463], [93461, 5], .source 46796⟩,
    ⟨[93461, 5], [93463], .contexts [
        ⟨79332, true, false, [], []⟩
      ]⟩,
    ⟨[93461], [93461], .contexts []⟩,
    ⟨[93463, 5], [93461], .contexts [
        ⟨79333, true, false, [], [5]⟩,
        ⟨28, false, false, [93461], []⟩,
        ⟨79334, false, false, [], []⟩
      ]⟩,
    ⟨[93465], [93463, 1], .source 46797⟩,
    ⟨[93463, 1], [93465], .contexts [
        ⟨79336, true, false, [], []⟩
      ]⟩,
    ⟨[93463], [93463], .contexts []⟩,
    ⟨[93465, 1], [93463], .contexts [
        ⟨79337, true, false, [], [1]⟩,
        ⟨8, false, false, [93463], []⟩,
        ⟨79338, false, false, [], []⟩
      ]⟩,
    ⟨[93467], [93465, 9], .source 46798⟩,
    ⟨[93465, 9], [93467], .contexts [
        ⟨79340, true, false, [], []⟩
      ]⟩,
    ⟨[93465], [93465], .contexts []⟩,
    ⟨[93469], [93467, 11], .source 46799⟩,
    ⟨[93467, 11], [93469], .contexts [
        ⟨79343, true, false, [], []⟩
      ]⟩,
    ⟨[93467], [93467], .contexts []⟩,
    ⟨[93469, 11], [93467], .contexts [
        ⟨79344, true, false, [], [11]⟩,
        ⟨53, false, false, [93467], []⟩,
        ⟨79345, false, false, [], []⟩
      ]⟩,
    ⟨[93471], [93469, 1], .source 46800⟩,
    ⟨[93469, 1], [93471], .contexts [
        ⟨79347, true, false, [], []⟩
      ]⟩,
    ⟨[93469], [93469], .contexts []⟩,
    ⟨[93471, 1], [93469], .contexts [
        ⟨79348, true, false, [], [1]⟩,
        ⟨8, false, false, [93469], []⟩,
        ⟨79349, false, false, [], []⟩
      ]⟩,
    ⟨[93473], [93471, 13], .source 46801⟩,
    ⟨[93471, 13], [93473], .contexts [
        ⟨79351, true, false, [], []⟩
      ]⟩,
    ⟨[93471], [93471], .contexts []⟩,
    ⟨[93473, 13], [93471], .contexts [
        ⟨79352, true, false, [], [13]⟩,
        ⟨59, false, false, [93471], []⟩,
        ⟨79353, false, false, [], []⟩
      ]⟩,
    ⟨[93475], [93473, 15], .source 46802⟩,
    ⟨[93473, 15], [93475], .contexts [
        ⟨79355, true, false, [], []⟩
      ]⟩,
    ⟨[93473], [93473], .contexts []⟩,
    ⟨[93475, 15], [93473], .contexts [
        ⟨79356, true, false, [], [15]⟩,
        ⟨1, false, false, [93473], []⟩,
        ⟨79357, false, false, [], []⟩
      ]⟩,
    ⟨[93477], [93475, 1], .source 46803⟩]

/-- Exact literal claimed equations and contextual derivations, block 1240. -/
def y322TCIndexRaw1240 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93475, 1], [93477], .contexts [
        ⟨79359, true, false, [], []⟩
      ]⟩,
    ⟨[93475], [93475], .contexts []⟩,
    ⟨[93479], [93477, 3], .source 46804⟩,
    ⟨[93477, 3], [93479], .contexts [
        ⟨79362, true, false, [], []⟩
      ]⟩,
    ⟨[93477], [93477], .contexts []⟩,
    ⟨[93479, 3], [93477], .contexts [
        ⟨79363, true, false, [], [3]⟩,
        ⟨20, false, false, [93477], []⟩,
        ⟨79364, false, false, [], []⟩
      ]⟩,
    ⟨[93481], [93479, 5], .source 46805⟩,
    ⟨[93479, 5], [93481], .contexts [
        ⟨79366, true, false, [], []⟩
      ]⟩,
    ⟨[93479], [93479], .contexts []⟩,
    ⟨[93483], [93481, 1], .source 46806⟩,
    ⟨[93481, 1], [93483], .contexts [
        ⟨79369, true, false, [], []⟩
      ]⟩,
    ⟨[93481], [93481], .contexts []⟩,
    ⟨[93483, 1], [93481], .contexts [
        ⟨79370, true, false, [], [1]⟩,
        ⟨8, false, false, [93481], []⟩,
        ⟨79371, false, false, [], []⟩
      ]⟩,
    ⟨[93485], [93483, 9], .source 46807⟩,
    ⟨[93483, 9], [93485], .contexts [
        ⟨79373, true, false, [], []⟩
      ]⟩,
    ⟨[93483], [93483], .contexts []⟩,
    ⟨[93485, 9], [93483], .contexts [
        ⟨79374, true, false, [], [9]⟩,
        ⟨46, false, false, [93483], []⟩,
        ⟨79375, false, false, [], []⟩
      ]⟩,
    ⟨[93487], [93485, 11], .source 46808⟩,
    ⟨[93485], [93485], .contexts []⟩,
    ⟨[93487, 11], [93485], .contexts [
        ⟨79377, false, false, [], [11]⟩,
        ⟨53, false, false, [93485], []⟩,
        ⟨79378, false, false, [], []⟩
      ]⟩,
    ⟨[93489], [93487, 1], .source 46809⟩,
    ⟨[93487], [93487], .contexts []⟩,
    ⟨[93489, 1], [93487], .contexts [
        ⟨79380, false, false, [], [1]⟩,
        ⟨8, false, false, [93487], []⟩,
        ⟨79381, false, false, [], []⟩
      ]⟩,
    ⟨[93491], [93489, 13], .source 46810⟩,
    ⟨[93489], [93489], .contexts []⟩,
    ⟨[93491, 13], [93489], .contexts [
        ⟨79383, false, false, [], [13]⟩,
        ⟨59, false, false, [93489], []⟩,
        ⟨79384, false, false, [], []⟩
      ]⟩,
    ⟨[93493], [93491, 15], .source 46811⟩,
    ⟨[93491], [93491], .contexts []⟩,
    ⟨[93493, 15], [93491], .contexts [
        ⟨79386, false, false, [], [15]⟩,
        ⟨1, false, false, [93491], []⟩,
        ⟨79387, false, false, [], []⟩
      ]⟩,
    ⟨[93495], [93493, 1], .source 46812⟩,
    ⟨[93493, 1], [93495], .contexts [
        ⟨79389, true, false, [], []⟩
      ]⟩,
    ⟨[93493], [93493], .contexts []⟩,
    ⟨[93495, 1], [93493], .contexts [
        ⟨79390, true, false, [], [1]⟩,
        ⟨8, false, false, [93493], []⟩,
        ⟨79391, false, false, [], []⟩
      ]⟩,
    ⟨[93497], [93495, 3], .source 46813⟩,
    ⟨[93495, 3], [93497], .contexts [
        ⟨79393, true, false, [], []⟩
      ]⟩,
    ⟨[93495], [93495], .contexts []⟩,
    ⟨[93497, 3], [93495], .contexts [
        ⟨79394, true, false, [], [3]⟩,
        ⟨20, false, false, [93495], []⟩,
        ⟨79395, false, false, [], []⟩
      ]⟩,
    ⟨[93499], [93497, 5], .source 46814⟩,
    ⟨[93497, 5], [93499], .contexts [
        ⟨79397, true, false, [], []⟩
      ]⟩,
    ⟨[93497], [93497], .contexts []⟩,
    ⟨[93499, 5], [93497], .contexts [
        ⟨79398, true, false, [], [5]⟩,
        ⟨28, false, false, [93497], []⟩,
        ⟨79399, false, false, [], []⟩
      ]⟩,
    ⟨[93501], [93499, 1], .source 46815⟩,
    ⟨[93499], [93499], .contexts []⟩,
    ⟨[93501, 1], [93499], .contexts [
        ⟨79401, false, false, [], [1]⟩,
        ⟨8, false, false, [93499], []⟩,
        ⟨79402, false, false, [], []⟩
      ]⟩,
    ⟨[93503], [93501, 9], .source 46816⟩,
    ⟨[93501, 9], [93503], .contexts [
        ⟨79404, true, false, [], []⟩
      ]⟩,
    ⟨[93501], [93501], .contexts []⟩,
    ⟨[93503, 9], [93501], .contexts [
        ⟨79405, true, false, [], [9]⟩,
        ⟨46, false, false, [93501], []⟩,
        ⟨79406, false, false, [], []⟩
      ]⟩,
    ⟨[93505], [93503, 11], .source 46817⟩,
    ⟨[93503], [93503], .contexts []⟩,
    ⟨[93505, 11], [93503], .contexts [
        ⟨79408, false, false, [], [11]⟩,
        ⟨53, false, false, [93503], []⟩,
        ⟨79409, false, false, [], []⟩
      ]⟩,
    ⟨[93507], [93505, 1], .source 46818⟩,
    ⟨[93505], [93505], .contexts []⟩,
    ⟨[93507, 1], [93505], .contexts [
        ⟨79411, false, false, [], [1]⟩,
        ⟨8, false, false, [93505], []⟩,
        ⟨79412, false, false, [], []⟩
      ]⟩,
    ⟨[93509], [93507, 13], .source 46819⟩,
    ⟨[93507], [93507], .contexts []⟩,
    ⟨[93509, 13], [93507], .contexts [
        ⟨79414, false, false, [], [13]⟩,
        ⟨59, false, false, [93507], []⟩,
        ⟨79415, false, false, [], []⟩
      ]⟩,
    ⟨[93511], [93509, 15], .source 46820⟩,
    ⟨[93509, 15], [93511], .contexts [
        ⟨79417, true, false, [], []⟩
      ]⟩,
    ⟨[93509], [93509], .contexts []⟩,
    ⟨[93511, 15], [93509], .contexts [
        ⟨79418, true, false, [], [15]⟩,
        ⟨1, false, false, [93509], []⟩,
        ⟨79419, false, false, [], []⟩
      ]⟩,
    ⟨[93513], [93511, 1], .source 46821⟩,
    ⟨[93511, 1], [93513], .contexts [
        ⟨79421, true, false, [], []⟩
      ]⟩,
    ⟨[93511], [93511], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1241. -/
def y322TCIndexRaw1241 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93513, 1], [93511], .contexts [
        ⟨79422, true, false, [], [1]⟩,
        ⟨8, false, false, [93511], []⟩,
        ⟨79423, false, false, [], []⟩
      ]⟩,
    ⟨[93515], [93513, 3], .source 46822⟩,
    ⟨[93513, 3], [93515], .contexts [
        ⟨79425, true, false, [], []⟩
      ]⟩,
    ⟨[93513], [93513], .contexts []⟩,
    ⟨[93515, 3], [93513], .contexts [
        ⟨79426, true, false, [], [3]⟩,
        ⟨20, false, false, [93513], []⟩,
        ⟨79427, false, false, [], []⟩
      ]⟩,
    ⟨[93517], [93515, 5], .source 46823⟩,
    ⟨[93515, 5], [93517], .contexts [
        ⟨79429, true, false, [], []⟩
      ]⟩,
    ⟨[93515], [93515], .contexts []⟩,
    ⟨[93517, 5], [93515], .contexts [
        ⟨79430, true, false, [], [5]⟩,
        ⟨28, false, false, [93515], []⟩,
        ⟨79431, false, false, [], []⟩
      ]⟩,
    ⟨[93519], [93517, 1], .source 46824⟩,
    ⟨[93517, 1], [93519], .contexts [
        ⟨79433, true, false, [], []⟩
      ]⟩,
    ⟨[93517], [93517], .contexts []⟩,
    ⟨[93519, 1], [93517], .contexts [
        ⟨79434, true, false, [], [1]⟩,
        ⟨8, false, false, [93517], []⟩,
        ⟨79435, false, false, [], []⟩
      ]⟩,
    ⟨[93521], [93519, 9], .source 46825⟩,
    ⟨[93519, 9], [93521], .contexts [
        ⟨79437, true, false, [], []⟩
      ]⟩,
    ⟨[93519], [93519], .contexts []⟩,
    ⟨[93521, 9], [93519], .contexts [
        ⟨79438, true, false, [], [9]⟩,
        ⟨46, false, false, [93519], []⟩,
        ⟨79439, false, false, [], []⟩
      ]⟩,
    ⟨[93523], [93521, 11], .source 46826⟩,
    ⟨[93521, 11], [93523], .contexts [
        ⟨79441, true, false, [], []⟩
      ]⟩,
    ⟨[93521], [93521], .contexts []⟩,
    ⟨[93523, 11], [93521], .contexts [
        ⟨79442, true, false, [], [11]⟩,
        ⟨53, false, false, [93521], []⟩,
        ⟨79443, false, false, [], []⟩
      ]⟩,
    ⟨[93525], [93523, 1], .source 46827⟩,
    ⟨[93523], [93523], .contexts []⟩,
    ⟨[93525, 1], [93523], .contexts [
        ⟨79445, false, false, [], [1]⟩,
        ⟨8, false, false, [93523], []⟩,
        ⟨79446, false, false, [], []⟩
      ]⟩,
    ⟨[93527], [93525, 13], .source 46828⟩,
    ⟨[93525, 13], [93527], .contexts [
        ⟨79448, true, false, [], []⟩
      ]⟩,
    ⟨[93525], [93525], .contexts []⟩,
    ⟨[93527, 13], [93525], .contexts [
        ⟨79449, true, false, [], [13]⟩,
        ⟨59, false, false, [93525], []⟩,
        ⟨79450, false, false, [], []⟩
      ]⟩,
    ⟨[93529], [93527, 15], .source 46829⟩,
    ⟨[93527], [93527], .contexts []⟩,
    ⟨[93529, 15], [93527], .contexts [
        ⟨79452, false, false, [], [15]⟩,
        ⟨1, false, false, [93527], []⟩,
        ⟨79453, false, false, [], []⟩
      ]⟩,
    ⟨[93531], [93529, 1], .source 46830⟩,
    ⟨[93529], [93529], .contexts []⟩,
    ⟨[93531, 1], [93529], .contexts [
        ⟨79455, false, false, [], [1]⟩,
        ⟨8, false, false, [93529], []⟩,
        ⟨79456, false, false, [], []⟩
      ]⟩,
    ⟨[93533], [93531, 3], .source 46831⟩,
    ⟨[93531], [93531], .contexts []⟩,
    ⟨[93533, 3], [93531], .contexts [
        ⟨79458, false, false, [], [3]⟩,
        ⟨20, false, false, [93531], []⟩,
        ⟨79459, false, false, [], []⟩
      ]⟩,
    ⟨[93535], [93533, 5], .source 46832⟩,
    ⟨[93533, 5], [93535], .contexts [
        ⟨79461, true, false, [], []⟩
      ]⟩,
    ⟨[93533], [93533], .contexts []⟩,
    ⟨[93535, 5], [93533], .contexts [
        ⟨79462, true, false, [], [5]⟩,
        ⟨28, false, false, [93533], []⟩,
        ⟨79463, false, false, [], []⟩
      ]⟩,
    ⟨[93537], [93535, 1], .source 46833⟩,
    ⟨[93535, 1], [93537], .contexts [
        ⟨79465, true, false, [], []⟩
      ]⟩,
    ⟨[93535], [93535], .contexts []⟩,
    ⟨[93537, 1], [93535], .contexts [
        ⟨79466, true, false, [], [1]⟩,
        ⟨8, false, false, [93535], []⟩,
        ⟨79467, false, false, [], []⟩
      ]⟩,
    ⟨[93539], [93537, 9], .source 46834⟩,
    ⟨[93537, 9], [93539], .contexts [
        ⟨79469, true, false, [], []⟩
      ]⟩,
    ⟨[93537], [93537], .contexts []⟩,
    ⟨[93539, 9], [93537], .contexts [
        ⟨79470, true, false, [], [9]⟩,
        ⟨46, false, false, [93537], []⟩,
        ⟨79471, false, false, [], []⟩
      ]⟩,
    ⟨[93541], [93539, 11], .source 46835⟩,
    ⟨[93539], [93539], .contexts []⟩,
    ⟨[93541, 11], [93539], .contexts [
        ⟨79473, false, false, [], [11]⟩,
        ⟨53, false, false, [93539], []⟩,
        ⟨79474, false, false, [], []⟩
      ]⟩,
    ⟨[93543], [93541, 1], .source 46836⟩,
    ⟨[93541, 1], [93543], .contexts [
        ⟨79476, true, false, [], []⟩
      ]⟩,
    ⟨[93541], [93541], .contexts []⟩,
    ⟨[93543, 1], [93541], .contexts [
        ⟨79477, true, false, [], [1]⟩,
        ⟨8, false, false, [93541], []⟩,
        ⟨79478, false, false, [], []⟩
      ]⟩,
    ⟨[93545], [93543, 13], .source 46837⟩,
    ⟨[93543, 13], [93545], .contexts [
        ⟨79480, true, false, [], []⟩
      ]⟩,
    ⟨[93543], [93543], .contexts []⟩,
    ⟨[93545, 13], [93543], .contexts [
        ⟨79481, true, false, [], [13]⟩,
        ⟨59, false, false, [93543], []⟩,
        ⟨79482, false, false, [], []⟩
      ]⟩,
    ⟨[93547], [93545, 15], .source 46838⟩,
    ⟨[93545], [93545], .contexts []⟩,
    ⟨[93547, 15], [93545], .contexts [
        ⟨79484, false, false, [], [15]⟩,
        ⟨1, false, false, [93545], []⟩,
        ⟨79485, false, false, [], []⟩
      ]⟩,
    ⟨[93549], [93547, 1], .source 46839⟩]

/-- Exact literal claimed equations and contextual derivations, block 1242. -/
def y322TCIndexRaw1242 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93547, 1], [93549], .contexts [
        ⟨79487, true, false, [], []⟩
      ]⟩,
    ⟨[93547], [93547], .contexts []⟩,
    ⟨[93549, 1], [93547], .contexts [
        ⟨79488, true, false, [], [1]⟩,
        ⟨8, false, false, [93547], []⟩,
        ⟨79489, false, false, [], []⟩
      ]⟩,
    ⟨[93549], [93549], .contexts []⟩,
    ⟨[93549], [93549], .contexts []⟩,
    ⟨[93545], [93545], .contexts []⟩,
    ⟨[93543], [93543], .contexts []⟩,
    ⟨[93539], [93539], .contexts []⟩,
    ⟨[93537], [93537], .contexts []⟩,
    ⟨[93547, 15, 13, 1, 11, 9], [93537], .contexts [
        ⟨79486, false, false, [], [13, 1, 11, 9]⟩,
        ⟨79493, false, false, [], [13, 1, 11, 9]⟩,
        ⟨79485, false, false, [], [13, 1, 11, 9]⟩,
        ⟨79485, false, false, [], [13, 1, 11, 9]⟩,
        ⟨79483, false, false, [], [1, 11, 9]⟩,
        ⟨79494, false, false, [], [1, 11, 9]⟩,
        ⟨79482, false, false, [], [1, 11, 9]⟩,
        ⟨79482, false, false, [], [1, 11, 9]⟩,
        ⟨79479, false, false, [], [11, 9]⟩,
        ⟨79478, false, false, [], [11, 9]⟩,
        ⟨79478, false, false, [], [11, 9]⟩,
        ⟨79475, false, false, [], [9]⟩,
        ⟨79495, false, false, [], [9]⟩,
        ⟨79474, false, false, [], [9]⟩,
        ⟨79474, false, false, [], [9]⟩,
        ⟨79472, false, false, [], []⟩,
        ⟨79496, false, false, [], []⟩,
        ⟨79471, false, false, [], []⟩,
        ⟨79471, false, false, [], []⟩
      ]⟩,
    ⟨[93535], [93535], .contexts []⟩,
    ⟨[93531], [93531], .contexts []⟩,
    ⟨[93529], [93529], .contexts []⟩,
    ⟨[93527], [93527], .contexts []⟩,
    ⟨[93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15], [93527], .contexts [
        ⟨79497, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨79468, false, false, [], [5, 3, 1, 15]⟩,
        ⟨79498, false, false, [], [5, 3, 1, 15]⟩,
        ⟨79467, false, false, [], [5, 3, 1, 15]⟩,
        ⟨79467, false, false, [], [5, 3, 1, 15]⟩,
        ⟨79464, false, false, [], [3, 1, 15]⟩,
        ⟨79463, false, false, [], [3, 1, 15]⟩,
        ⟨79463, false, false, [], [3, 1, 15]⟩,
        ⟨79460, false, false, [], [1, 15]⟩,
        ⟨79499, false, false, [], [1, 15]⟩,
        ⟨79459, false, false, [], [1, 15]⟩,
        ⟨79459, false, false, [], [1, 15]⟩,
        ⟨79457, false, false, [], [15]⟩,
        ⟨79500, false, false, [], [15]⟩,
        ⟨79456, false, false, [], [15]⟩,
        ⟨79456, false, false, [], [15]⟩,
        ⟨79454, false, false, [], []⟩,
        ⟨79501, false, false, [], []⟩,
        ⟨79453, false, false, [], []⟩,
        ⟨79453, false, false, [], []⟩
      ]⟩,
    ⟨[93521], [93521], .contexts []⟩,
    ⟨[93521, 9], [93519], .contexts [
        ⟨79440, false, false, [], []⟩
      ]⟩,
    ⟨[93519], [93519], .contexts []⟩,
    ⟨[93519, 1], [93517], .contexts [
        ⟨79436, false, false, [], []⟩
      ]⟩,
    ⟨[93517], [93517], .contexts []⟩,
    ⟨[
      93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1
    ], [93517], .contexts [
        ⟨79502, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨79451, false, false, [], [1, 11, 9, 1]⟩,
        ⟨79450, false, false, [], [1, 11, 9, 1]⟩,
        ⟨79450, false, false, [], [1, 11, 9, 1]⟩,
        ⟨79447, false, false, [], [11, 9, 1]⟩,
        ⟨79446, false, false, [], [11, 9, 1]⟩,
        ⟨79446, false, false, [], [11, 9, 1]⟩,
        ⟨79444, false, false, [], [9, 1]⟩,
        ⟨79503, false, false, [], [9, 1]⟩,
        ⟨79443, false, false, [], [9, 1]⟩,
        ⟨79443, false, false, [], [9, 1]⟩,
        ⟨79504, false, false, [], [1]⟩,
        ⟨79505, false, false, [], [1]⟩,
        ⟨79439, false, false, [], [1]⟩,
        ⟨79439, false, false, [], [1]⟩,
        ⟨79506, false, false, [], []⟩,
        ⟨79507, false, false, [], []⟩,
        ⟨79435, false, false, [], []⟩,
        ⟨79435, false, false, [], []⟩
      ]⟩,
    ⟨[93517, 5], [93515], .contexts [
        ⟨79432, false, false, [], []⟩
      ]⟩,
    ⟨[93515], [93515], .contexts []⟩,
    ⟨[93515, 3], [93513], .contexts [
        ⟨79428, false, false, [], []⟩
      ]⟩,
    ⟨[93513], [93513], .contexts []⟩,
    ⟨[93511], [93511], .contexts []⟩,
    ⟨[93507], [93507], .contexts []⟩,
    ⟨[
      93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [93507], .contexts [
        ⟨79508, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨79509, false, false, [], [3, 1, 15, 13]⟩,
        ⟨79510, false, false, [], [3, 1, 15, 13]⟩,
        ⟨79431, false, false, [], [3, 1, 15, 13]⟩,
        ⟨79431, false, false, [], [3, 1, 15, 13]⟩,
        ⟨79511, false, false, [], [1, 15, 13]⟩,
        ⟨79512, false, false, [], [1, 15, 13]⟩,
        ⟨79427, false, false, [], [1, 15, 13]⟩,
        ⟨79427, false, false, [], [1, 15, 13]⟩,
        ⟨79424, false, false, [], [15, 13]⟩,
        ⟨79513, false, false, [], [15, 13]⟩,
        ⟨79423, false, false, [], [15, 13]⟩,
        ⟨79423, false, false, [], [15, 13]⟩,
        ⟨79420, false, false, [], [13]⟩,
        ⟨79419, false, false, [], [13]⟩,
        ⟨79419, false, false, [], [13]⟩,
        ⟨79416, false, false, [], []⟩,
        ⟨79514, false, false, [], []⟩,
        ⟨79415, false, false, [], []⟩,
        ⟨79415, false, false, [], []⟩
      ]⟩,
    ⟨[93505], [93505], .contexts []⟩,
    ⟨[93503], [93503], .contexts []⟩,
    ⟨[93501], [93501], .contexts []⟩,
    ⟨[93501, 1], [93499], .contexts [
        ⟨79403, false, false, [], []⟩
      ]⟩,
    ⟨[93499], [93499], .contexts []⟩,
    ⟨[93497], [93497], .contexts []⟩,
    ⟨[
      93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5
    ], [93497], .contexts [
        ⟨79515, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨79413, false, false, [], [11, 9, 1, 5]⟩,
        ⟨79516, false, false, [], [11, 9, 1, 5]⟩,
        ⟨79412, false, false, [], [11, 9, 1, 5]⟩,
        ⟨79412, false, false, [], [11, 9, 1, 5]⟩,
        ⟨79410, false, false, [], [9, 1, 5]⟩,
        ⟨79517, false, false, [], [9, 1, 5]⟩,
        ⟨79409, false, false, [], [9, 1, 5]⟩,
        ⟨79409, false, false, [], [9, 1, 5]⟩,
        ⟨79407, false, false, [], [1, 5]⟩,
        ⟨79518, false, false, [], [1, 5]⟩,
        ⟨79406, false, false, [], [1, 5]⟩,
        ⟨79406, false, false, [], [1, 5]⟩,
        ⟨79519, false, false, [], [5]⟩,
        ⟨79520, false, false, [], [5]⟩,
        ⟨79402, false, false, [], [5]⟩,
        ⟨79402, false, false, [], [5]⟩,
        ⟨79400, false, false, [], []⟩,
        ⟨79521, false, false, [], []⟩,
        ⟨79399, false, false, [], []⟩,
        ⟨79399, false, false, [], []⟩
      ]⟩,
    ⟨[93495], [93495], .contexts []⟩,
    ⟨[93495, 1], [93493], .contexts [
        ⟨79392, false, false, [], []⟩
      ]⟩,
    ⟨[93493], [93493], .contexts []⟩,
    ⟨[93493, 15], [93491], .contexts [
        ⟨79388, false, false, [], []⟩
      ]⟩,
    ⟨[93489], [93489], .contexts []⟩,
    ⟨[93487], [93487], .contexts []⟩,
    ⟨[
      93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1
    ], [93487], .contexts [
        ⟨79522, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨79396, false, false, [], [1, 15, 13, 1]⟩,
        ⟨79523, false, false, [], [1, 15, 13, 1]⟩,
        ⟨79395, false, false, [], [1, 15, 13, 1]⟩,
        ⟨79395, false, false, [], [1, 15, 13, 1]⟩,
        ⟨79524, false, false, [], [15, 13, 1]⟩,
        ⟨79525, false, false, [], [15, 13, 1]⟩,
        ⟨79391, false, false, [], [15, 13, 1]⟩,
        ⟨79391, false, false, [], [15, 13, 1]⟩,
        ⟨79526, false, false, [], [13, 1]⟩,
        ⟨79387, false, false, [], [13, 1]⟩,
        ⟨79387, false, false, [], [13, 1]⟩,
        ⟨79385, false, false, [], [1]⟩,
        ⟨79527, false, false, [], [1]⟩,
        ⟨79384, false, false, [], [1]⟩,
        ⟨79384, false, false, [], [1]⟩,
        ⟨79382, false, false, [], []⟩,
        ⟨79528, false, false, [], []⟩,
        ⟨79381, false, false, [], []⟩,
        ⟨79381, false, false, [], []⟩
      ]⟩,
    ⟨[93485], [93485], .contexts []⟩,
    ⟨[93483], [93483], .contexts []⟩,
    ⟨[93479], [93479], .contexts []⟩,
    ⟨[93477], [93477], .contexts []⟩,
    ⟨[
      93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [93477], .contexts [
        ⟨79529, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨79379, false, false, [], [9, 1, 5, 3]⟩,
        ⟨79530, false, false, [], [9, 1, 5, 3]⟩,
        ⟨79378, false, false, [], [9, 1, 5, 3]⟩,
        ⟨79378, false, false, [], [9, 1, 5, 3]⟩,
        ⟨79376, false, false, [], [1, 5, 3]⟩,
        ⟨79531, false, false, [], [1, 5, 3]⟩,
        ⟨79375, false, false, [], [1, 5, 3]⟩,
        ⟨79375, false, false, [], [1, 5, 3]⟩,
        ⟨79372, false, false, [], [5, 3]⟩,
        ⟨79371, false, false, [], [5, 3]⟩,
        ⟨79371, false, false, [], [5, 3]⟩,
        ⟨79367, true, false, [], [5, 3]⟩,
        ⟨28, false, false, [93479], [3]⟩,
        ⟨79368, false, false, [], [3]⟩,
        ⟨79532, false, false, [], [3]⟩,
        ⟨79368, false, false, [], [3]⟩,
        ⟨79368, false, false, [], [3]⟩,
        ⟨79365, false, false, [], []⟩,
        ⟨79533, false, false, [], []⟩,
        ⟨79364, false, false, [], []⟩,
        ⟨79364, false, false, [], []⟩
      ]⟩,
    ⟨[93475], [93475], .contexts []⟩,
    ⟨[93473], [93473], .contexts []⟩,
    ⟨[93469], [93469], .contexts []⟩,
    ⟨[
      93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1
    ], [93469], .contexts [
        ⟨79534, false, false, [], [1, 15, 13, 1]⟩,
        ⟨79360, true, false, [], [1, 15, 13, 1]⟩,
        ⟨8, false, false, [93475], [15, 13, 1]⟩,
        ⟨79361, false, false, [], [15, 13, 1]⟩,
        ⟨79535, false, false, [], [15, 13, 1]⟩,
        ⟨79361, false, false, [], [15, 13, 1]⟩,
        ⟨79361, false, false, [], [15, 13, 1]⟩,
        ⟨79358, false, false, [], [13, 1]⟩,
        ⟨79536, false, false, [], [13, 1]⟩,
        ⟨79357, false, false, [], [13, 1]⟩,
        ⟨79357, false, false, [], [13, 1]⟩,
        ⟨79354, false, false, [], [1]⟩,
        ⟨79353, false, false, [], [1]⟩,
        ⟨79353, false, false, [], [1]⟩,
        ⟨79350, false, false, [], []⟩,
        ⟨79537, false, false, [], []⟩,
        ⟨79349, false, false, [], []⟩,
        ⟨79349, false, false, [], []⟩
      ]⟩,
    ⟨[93467], [93467], .contexts []⟩,
    ⟨[93465], [93465], .contexts []⟩,
    ⟨[93463], [93463], .contexts []⟩,
    ⟨[93461], [93461], .contexts []⟩,
    ⟨[93459], [93459], .contexts []⟩,
    ⟨[
      93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [93459], .contexts [
        ⟨79538, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨79346, false, false, [], [9, 1, 5, 3]⟩,
        ⟨79539, false, false, [], [9, 1, 5, 3]⟩,
        ⟨79345, false, false, [], [9, 1, 5, 3]⟩,
        ⟨79345, false, false, [], [9, 1, 5, 3]⟩,
        ⟨79341, true, false, [], [9, 1, 5, 3]⟩,
        ⟨46, false, false, [93465], [1, 5, 3]⟩,
        ⟨79342, false, false, [], [1, 5, 3]⟩,
        ⟨79540, false, false, [], [1, 5, 3]⟩,
        ⟨79342, false, false, [], [1, 5, 3]⟩,
        ⟨79342, false, false, [], [1, 5, 3]⟩,
        ⟨79339, false, false, [], [5, 3]⟩,
        ⟨79541, false, false, [], [5, 3]⟩,
        ⟨79338, false, false, [], [5, 3]⟩,
        ⟨79338, false, false, [], [5, 3]⟩,
        ⟨79335, false, false, [], [3]⟩,
        ⟨79542, false, false, [], [3]⟩,
        ⟨79334, false, false, [], [3]⟩,
        ⟨79334, false, false, [], [3]⟩,
        ⟨79331, false, false, [], []⟩,
        ⟨79543, false, false, [], []⟩,
        ⟨79330, false, false, [], []⟩,
        ⟨79330, false, false, [], []⟩
      ]⟩,
    ⟨[93459, 1], [93457], .contexts [
        ⟨79327, false, false, [], []⟩
      ]⟩,
    ⟨[93457], [93457], .contexts []⟩,
    ⟨[93455], [93455], .contexts []⟩,
    ⟨[93453], [93453], .contexts []⟩,
    ⟨[93451], [93451], .contexts []⟩,
    ⟨[93449], [93449], .contexts []⟩,
    ⟨[
      93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11
    ], [93449], .contexts [
        ⟨79544, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨79545, false, false, [], [15, 13, 1, 11]⟩,
        ⟨79546, false, false, [], [15, 13, 1, 11]⟩,
        ⟨79326, false, false, [], [15, 13, 1, 11]⟩,
        ⟨79326, false, false, [], [15, 13, 1, 11]⟩,
        ⟨79323, false, false, [], [13, 1, 11]⟩,
        ⟨79547, false, false, [], [13, 1, 11]⟩,
        ⟨79322, false, false, [], [13, 1, 11]⟩,
        ⟨79322, false, false, [], [13, 1, 11]⟩,
        ⟨79319, false, false, [], [1, 11]⟩,
        ⟨79548, false, false, [], [1, 11]⟩,
        ⟨79318, false, false, [], [1, 11]⟩,
        ⟨79318, false, false, [], [1, 11]⟩,
        ⟨79314, true, false, [], [1, 11]⟩,
        ⟨8, false, false, [93451], [11]⟩,
        ⟨79315, false, false, [], [11]⟩,
        ⟨79549, false, false, [], [11]⟩,
        ⟨79315, false, false, [], [11]⟩,
        ⟨79315, false, false, [], [11]⟩,
        ⟨79311, true, false, [], [11]⟩,
        ⟨53, false, false, [93449], []⟩,
        ⟨79312, false, false, [], []⟩,
        ⟨79550, false, false, [], []⟩,
        ⟨79312, false, false, [], []⟩,
        ⟨79312, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1243. -/
def y322TCIndexRaw1243 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93447], [93447], .contexts []⟩,
    ⟨[93445], [93445], .contexts []⟩,
    ⟨[93443], [93443], .contexts []⟩,
    ⟨[93441], [93441], .contexts []⟩,
    ⟨[
      93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3
    ], [93441], .contexts [
        ⟨79551, false, false, [], [9, 1, 5, 3]⟩,
        ⟨79308, true, false, [], [9, 1, 5, 3]⟩,
        ⟨46, false, false, [93447], [1, 5, 3]⟩,
        ⟨79309, false, false, [], [1, 5, 3]⟩,
        ⟨79552, false, false, [], [1, 5, 3]⟩,
        ⟨79309, false, false, [], [1, 5, 3]⟩,
        ⟨79309, false, false, [], [1, 5, 3]⟩,
        ⟨79305, true, false, [], [1, 5, 3]⟩,
        ⟨8, false, false, [93445], [5, 3]⟩,
        ⟨79306, false, false, [], [5, 3]⟩,
        ⟨79553, false, false, [], [5, 3]⟩,
        ⟨79306, false, false, [], [5, 3]⟩,
        ⟨79306, false, false, [], [5, 3]⟩,
        ⟨79302, true, false, [], [5, 3]⟩,
        ⟨28, false, false, [93443], [3]⟩,
        ⟨79303, false, false, [], [3]⟩,
        ⟨79554, false, false, [], [3]⟩,
        ⟨79303, false, false, [], [3]⟩,
        ⟨79303, false, false, [], [3]⟩,
        ⟨79299, true, false, [], [3]⟩,
        ⟨20, false, false, [93441], []⟩,
        ⟨79300, false, false, [], []⟩,
        ⟨79555, false, false, [], []⟩,
        ⟨79300, false, false, [], []⟩,
        ⟨79300, false, false, [], []⟩
      ]⟩,
    ⟨[93439], [93439], .contexts []⟩,
    ⟨[93435], [93435], .contexts []⟩,
    ⟨[93433], [93433], .contexts []⟩,
    ⟨[
      93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [93433], .contexts [
        ⟨79556, false, false, [], [1, 15, 13, 1]⟩,
        ⟨79296, true, false, [], [1, 15, 13, 1]⟩,
        ⟨8, false, false, [93439], [15, 13, 1]⟩,
        ⟨79297, false, false, [], [15, 13, 1]⟩,
        ⟨79557, false, false, [], [15, 13, 1]⟩,
        ⟨79297, false, false, [], [15, 13, 1]⟩,
        ⟨79297, false, false, [], [15, 13, 1]⟩,
        ⟨79293, true, false, [], [15, 13, 1]⟩,
        ⟨1, false, false, [93437], [13, 1]⟩,
        ⟨79294, false, false, [], [13, 1]⟩,
        ⟨79294, false, false, [], [13, 1]⟩,
        ⟨79294, false, false, [], [13, 1]⟩,
        ⟨79290, true, false, [], [13, 1]⟩,
        ⟨59, false, false, [93435], [1]⟩,
        ⟨79291, false, false, [], [1]⟩,
        ⟨79558, false, false, [], [1]⟩,
        ⟨79291, false, false, [], [1]⟩,
        ⟨79291, false, false, [], [1]⟩,
        ⟨79288, false, false, [], []⟩,
        ⟨79559, false, false, [], []⟩,
        ⟨79287, false, false, [], []⟩,
        ⟨79287, false, false, [], []⟩
      ]⟩,
    ⟨[93431], [93431], .contexts []⟩,
    ⟨[
      93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5
    ], [30109, 93429], .contexts [
        ⟨79560, false, false, [], [11, 9, 1, 5]⟩,
        ⟨79283, true, false, [], [11, 9, 1, 5]⟩,
        ⟨53, false, false, [93431], [9, 1, 5]⟩,
        ⟨79284, false, false, [], [9, 1, 5]⟩,
        ⟨79561, false, false, [], [9, 1, 5]⟩,
        ⟨79284, false, false, [], [9, 1, 5]⟩,
        ⟨79284, false, false, [], [9, 1, 5]⟩,
        ⟨79281, true, false, [], [9, 1, 5]⟩,
        ⟨46, false, false, [92203], [1, 5]⟩,
        ⟨70668, false, false, [], [1, 5]⟩,
        ⟨70826, false, false, [], [1, 5]⟩,
        ⟨70668, false, false, [], [1, 5]⟩,
        ⟨70668, false, false, [], [1, 5]⟩,
        ⟨70667, false, false, [], [5]⟩,
        ⟨70825, false, false, [], [5]⟩,
        ⟨70671, false, false, [], [5]⟩,
        ⟨70671, false, false, [], [5]⟩,
        ⟨79273, false, false, [], []⟩,
        ⟨79274, false, false, [], []⟩,
        ⟨79275, false, false, [], []⟩,
        ⟨79275, false, false, [], []⟩
      ]⟩,
    ⟨[30109, 93425], [30109, 93425], .contexts []⟩,
    ⟨[30109, 93421], [30109, 93421], .contexts []⟩,
    ⟨[30109, 93421], [30109, 93421], .contexts []⟩,
    ⟨[
      93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13
    ], [30109, 93421], .contexts [
        ⟨79562, false, false, [], [3, 1, 15, 13]⟩,
        ⟨79265, true, false, [30109], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [30109, 93427], [1, 15, 13]⟩,
        ⟨79263, false, false, [30109], [15, 13]⟩,
        ⟨79563, false, false, [], [15, 13]⟩,
        ⟨79256, false, false, [30109], [13]⟩,
        ⟨79242, false, false, [30109], []⟩,
        ⟨79564, false, false, [], []⟩,
        ⟨79565, false, false, [], []⟩
      ]⟩,
    ⟨[30117], [30109, 13035], .source 15123⟩,
    ⟨[30119], [30117, 2909], .source 15124⟩,
    ⟨[
      93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [30119, 93415], .contexts [
        ⟨79566, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨79216, false, false, [30109], [11, 9, 1, 5]⟩,
        ⟨79567, true, false, [], [93421, 11, 9, 1, 5]⟩,
        ⟨79209, false, false, [30117], [9, 1, 5]⟩,
        ⟨79184, false, false, [30117], [1, 5]⟩,
        ⟨79157, false, false, [30117], [5]⟩,
        ⟨79140, false, false, [30117], []⟩,
        ⟨79568, true, false, [], [93415]⟩
      ]⟩,
    ⟨[30121], [30119, 1369], .source 15125⟩,
    ⟨[30123], [30121, 18113], .source 15126⟩,
    ⟨[30125], [30123, 1383], .source 15127⟩,
    ⟨[
      93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1
    ], [30125, 85339], .contexts [
        ⟨79569, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨79131, false, false, [30119], [1, 15, 13, 1]⟩,
        ⟨31488, false, false, [30119], [15, 13, 1]⟩,
        ⟨79570, true, false, [], [85331, 15, 13, 1]⟩,
        ⟨31618, false, false, [30121], [13, 1]⟩,
        ⟨31616, false, false, [30121], [1]⟩,
        ⟨79571, true, false, [], [85343, 1]⟩,
        ⟨31599, false, false, [30123], []⟩,
        ⟨79572, true, false, [], [85339]⟩
      ]⟩,
    ⟨[30127], [30125, 1369], .source 15128⟩,
    ⟨[30129], [30127, 13035], .source 15129⟩,
    ⟨[30131], [30129, 1369], .source 15130⟩,
    ⟨[30133], [30131, 17041], .source 15131⟩,
    ⟨[
      93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [30133, 80259], .contexts [
        ⟨79573, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨31554, false, false, [30125], [9, 1, 5, 3]⟩,
        ⟨79574, true, false, [], [85339, 9, 1, 5, 3]⟩,
        ⟨31552, false, false, [30127], [1, 5, 3]⟩,
        ⟨79575, true, false, [], [85339, 1, 5, 3]⟩,
        ⟨31600, false, false, [30129], [5, 3]⟩,
        ⟨79576, true, false, [], [85343, 5, 3]⟩,
        ⟨31589, false, false, [30131], [3]⟩,
        ⟨31450, false, false, [30131], []⟩,
        ⟨79577, true, false, [], [80259]⟩
      ]⟩,
    ⟨[30135], [30133, 15151], .source 15132⟩,
    ⟨[30137], [30135, 16159], .source 15133⟩,
    ⟨[30139], [30137, 16187], .source 15134⟩,
    ⟨[30141], [30139, 16007], .source 15135⟩,
    ⟨[
      93547, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11
    ], [30141, 83185], .contexts [
        ⟨79578, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨14850, false, false, [30133], [15, 13, 1, 11]⟩,
        ⟨79579, true, false, [], [80259, 15, 13, 1, 11]⟩,
        ⟨21640, false, false, [30135], [13, 1, 11]⟩,
        ⟨21638, false, false, [30135], [1, 11]⟩,
        ⟨79580, true, false, [], [83355, 1, 11]⟩,
        ⟨20844, false, false, [30137], [11]⟩,
        ⟨79581, true, false, [], [83185, 11]⟩,
        ⟨19683, false, false, [30139], []⟩,
        ⟨79582, true, false, [], [83185]⟩
      ]⟩,
    ⟨[30143], [30141, 15977], .source 15136⟩,
    ⟨[30145], [30143, 15997], .source 15137⟩,
    ⟨[93549, 3], [93549, 3], .contexts []⟩,
    ⟨[30145], [30145], .contexts [
        ⟨13, false, false, [], [30145]⟩
      ]⟩,
    ⟨[93549, 3], [30145, 83177], .contexts [
        ⟨79586, false, false, [], []⟩,
        ⟨79492, true, false, [], [3]⟩,
        ⟨79492, true, false, [], [3]⟩,
        ⟨79491, true, false, [], [3]⟩,
        ⟨79488, true, false, [], [3]⟩,
        ⟨1908, false, false, [93547], []⟩,
        ⟨1909, false, false, [93547], []⟩,
        ⟨79583, false, false, [], [9, 1, 5]⟩,
        ⟨19660, false, false, [30141], [1, 5]⟩,
        ⟨19500, false, false, [30141], [5]⟩,
        ⟨79584, true, false, [], [83169, 5]⟩,
        ⟨19586, false, false, [30143], []⟩,
        ⟨79585, true, false, [], [83177]⟩,
        ⟨19591, false, false, [30145], []⟩,
        ⟨79587, true, false, [], [83177]⟩
      ]⟩,
    ⟨[30147], [30144], .source 15138⟩,
    ⟨[93549, 1], [93547], .contexts [
        ⟨79490, false, false, [], []⟩
      ]⟩,
    ⟨[30145, 83177], [30145, 83177], .contexts []⟩,
    ⟨[30145, 83177], [30145, 83177], .contexts []⟩,
    ⟨[93549, 3], [30145, 83177], .contexts [
        ⟨79586, false, false, [], []⟩,
        ⟨79588, false, false, [], []⟩,
        ⟨79591, false, false, [], []⟩,
        ⟨79592, false, false, [], []⟩,
        ⟨79592, false, false, [], []⟩
      ]⟩,
    ⟨[30145, 87579], [30145, 87579], .contexts []⟩,
    ⟨[30145, 87579], [30145, 87579], .contexts []⟩,
    ⟨[93547, 3], [93547, 3], .contexts []⟩,
    ⟨[93547, 3], [30145, 87579], .contexts [
        ⟨79596, false, false, [], []⟩,
        ⟨79489, true, false, [], [3]⟩,
        ⟨79489, true, false, [], [3]⟩,
        ⟨79590, true, false, [], [3]⟩,
        ⟨1098, false, false, [93549], []⟩,
        ⟨1100, false, false, [93549], []⟩,
        ⟨79593, false, false, [], [1, 3, 1]⟩,
        ⟨19642, false, false, [30145], [3, 1]⟩,
        ⟨44742, false, false, [30145], [1]⟩,
        ⟨44767, false, false, [30145], []⟩,
        ⟨79594, false, false, [], []⟩,
        ⟨79595, false, false, [], []⟩,
        ⟨44777, false, false, [30145], []⟩,
        ⟨79587, true, false, [], [87579]⟩
      ]⟩,
    ⟨[87579, 3], [30147, 93547], .contexts [
        ⟨79597, true, false, [30144], [3]⟩,
        ⟨20, false, false, [30144, 93547], []⟩,
        ⟨79589, true, false, [], [93547]⟩
      ]⟩,
    ⟨[30149], [30145, 29775], .source 15139⟩,
    ⟨[93549], [93549], .contexts []⟩,
    ⟨[93549], [93549], .contexts []⟩,
    ⟨[30151], [30148], .source 15140⟩,
    ⟨[30148], [30148], .contexts []⟩,
    ⟨[93281, 7], [30151, 93549], .contexts [
        ⟨79599, false, false, [30148], [93281, 7]⟩,
        ⟨78196, true, false, [30148, 30145], [7]⟩,
        ⟨19577, true, false, [30148, 30145], [3, 7]⟩,
        ⟨79593, true, false, [30148], [7, 3, 7]⟩,
        ⟨18135, false, false, [30148, 93549], []⟩,
        ⟨79600, false, false, [30148], []⟩,
        ⟨79601, false, false, [30148], []⟩,
        ⟨79603, true, false, [], [93549]⟩,
        ⟨79603, true, false, [], [93549]⟩,
        ⟨79602, true, false, [], [93549]⟩
      ]⟩,
    ⟨[93549, 7], [30149, 93281], .contexts [
        ⟨79604, true, false, [30150], [7]⟩,
        ⟨38, false, false, [30150, 93281], []⟩,
        ⟨79602, false, true, [], [93281]⟩
      ]⟩,
    ⟨[30153], [30145, 15995], .source 15141⟩,
    ⟨[30155], [30153, 16221], .source 15142⟩,
    ⟨[30157], [30154], .source 15143⟩,
    ⟨[30154], [30154], .contexts []⟩,
    ⟨[91257, 9], [30157, 93549], .contexts [
        ⟨79607, false, false, [30154], [91257, 9]⟩,
        ⟨65147, true, false, [30154, 30153], [9]⟩,
        ⟨79606, false, false, [30154], [83195, 3, 9]⟩,
        ⟨19807, true, false, [30154, 30145], [3, 9]⟩,
        ⟨79593, true, false, [30154], [9, 3, 9]⟩,
        ⟨1612, false, false, [30154, 93549], []⟩,
        ⟨79600, false, false, [30154], []⟩,
        ⟨79601, false, false, [30154], []⟩,
        ⟨79609, true, false, [], [93549]⟩,
        ⟨79609, true, false, [], [93549]⟩,
        ⟨79608, true, false, [], [93549]⟩
      ]⟩,
    ⟨[93549, 9], [30155, 91257], .contexts [
        ⟨79610, true, false, [30156], [9]⟩,
        ⟨46, false, false, [30156, 91257], []⟩,
        ⟨79608, false, true, [], [91257]⟩
      ]⟩,
    ⟨[30159], [30145, 16373], .source 15144⟩,
    ⟨[30161], [30159, 24207], .source 15145⟩,
    ⟨[30163], [30160], .source 15146⟩,
    ⟨[30160], [30160], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1244. -/
def y322TCIndexRaw1244 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89709, 11], [30163, 93549], .contexts [
        ⟨79613, false, false, [30160], [89709, 11]⟩,
        ⟨57036, true, false, [30160, 30159], [11]⟩,
        ⟨79612, false, false, [30160], [83501, 3, 11]⟩,
        ⟨21661, true, false, [30160, 30145], [3, 11]⟩,
        ⟨79593, true, false, [30160], [11, 3, 11]⟩,
        ⟨1693, false, false, [30160, 93549], []⟩,
        ⟨79600, false, false, [30160], []⟩,
        ⟨79601, false, false, [30160], []⟩,
        ⟨79615, true, false, [], [93549]⟩,
        ⟨79615, true, false, [], [93549]⟩,
        ⟨79614, true, false, [], [93549]⟩
      ]⟩,
    ⟨[93549, 11], [30161, 89709], .contexts [
        ⟨79616, true, false, [30162], [11]⟩,
        ⟨53, false, false, [30162, 89709], []⟩,
        ⟨79614, false, true, [], [89709]⟩
      ]⟩,
    ⟨[30165], [30145, 15991], .source 15147⟩,
    ⟨[30167], [30165, 17275], .source 15148⟩,
    ⟨[84489, 13], [84489, 13], .contexts []⟩,
    ⟨[30169], [30166], .source 15149⟩,
    ⟨[30166], [30166], .contexts []⟩,
    ⟨[84489, 13], [30169, 93549], .contexts [
        ⟨79620, false, false, [], []⟩,
        ⟨79619, false, false, [30166], [84489, 13]⟩,
        ⟨27092, true, false, [30166, 30165], [13]⟩,
        ⟨79618, false, false, [30166], [83167, 3, 13]⟩,
        ⟨19588, true, false, [30166, 30145], [3, 13]⟩,
        ⟨79593, true, false, [30166], [13, 3, 13]⟩,
        ⟨1930, false, false, [30166, 93549], []⟩,
        ⟨79600, false, false, [30166], []⟩,
        ⟨79601, false, false, [30166], []⟩,
        ⟨79622, true, false, [], [93549]⟩,
        ⟨79622, true, false, [], [93549]⟩,
        ⟨79621, true, false, [], [93549]⟩
      ]⟩,
    ⟨[93549, 13], [30167, 84489], .contexts [
        ⟨79623, true, false, [30168], [13]⟩,
        ⟨59, false, false, [30168, 84489], []⟩,
        ⟨79621, false, true, [], [84489]⟩
      ]⟩,
    ⟨[93547, 3], [30145, 87579], .contexts [
        ⟨79596, false, false, [], []⟩,
        ⟨79597, false, false, [], []⟩,
        ⟨79594, false, false, [], []⟩,
        ⟨79595, false, false, [], []⟩,
        ⟨79595, false, false, [], []⟩
      ]⟩,
    ⟨[30177], [30145, 21285], .source 15153⟩,
    ⟨[30179], [29781, 29827], .source 15154⟩,
    ⟨[30181], [30177, 30179], .source 15155⟩,
    ⟨[93547], [93547], .contexts []⟩,
    ⟨[93547], [93547], .contexts []⟩,
    ⟨[30183], [30180], .source 15156⟩,
    ⟨[30180], [30180], .contexts []⟩,
    ⟨[93277, 7], [30183, 93547], .contexts [
        ⟨79628, false, false, [30180], [93277, 7]⟩,
        ⟨79627, false, false, [30180, 30177], [93277, 7]⟩,
        ⟨78257, true, false, [30180, 30177, 29781], [7]⟩,
        ⟨78203, true, false, [30180, 30177], [7]⟩,
        ⟨79626, false, false, [30180], [84713, 3, 7]⟩,
        ⟨44780, true, false, [30180, 30145], [3, 7]⟩,
        ⟨79625, true, false, [30180], [7, 3, 7]⟩,
        ⟨18135, false, false, [30180, 93547], []⟩,
        ⟨79629, false, false, [30180], []⟩,
        ⟨79630, false, false, [30180], []⟩,
        ⟨79632, true, false, [], [93547]⟩,
        ⟨79632, true, false, [], [93547]⟩,
        ⟨79631, true, false, [], [93547]⟩
      ]⟩,
    ⟨[30185], [30145, 25871], .source 15157⟩,
    ⟨[89705, 11], [89705, 11], .contexts []⟩,
    ⟨[30187], [30184], .source 15158⟩,
    ⟨[30184], [30184], .contexts []⟩,
    ⟨[89705, 11], [30187, 93547], .contexts [
        ⟨79635, false, false, [], []⟩,
        ⟨79634, false, false, [30184], [89705, 11]⟩,
        ⟨64469, true, false, [30184, 30145], [11]⟩,
        ⟨64480, true, false, [30184, 30145], [3, 11]⟩,
        ⟨79625, true, false, [30184], [11, 3, 11]⟩,
        ⟨1693, false, false, [30184, 93547], []⟩,
        ⟨79629, false, false, [30184], []⟩,
        ⟨79630, false, false, [30184], []⟩,
        ⟨79637, true, false, [], [93547]⟩,
        ⟨79637, true, false, [], [93547]⟩,
        ⟨79636, true, false, [], [93547]⟩
      ]⟩,
    ⟨[30189], [30145, 727], .source 15159⟩,
    ⟨[30191], [30189, 30147], .source 15160⟩,
    ⟨[30191, 93545], [30191, 93545], .contexts []⟩,
    ⟨[93547], [30191, 93545], .contexts [
        ⟨79630, false, false, [], []⟩,
        ⟨150, true, false, [93547], []⟩,
        ⟨79625, false, false, [], [15, 3, 15]⟩,
        ⟨44786, false, false, [30145], [3, 15]⟩,
        ⟨79639, true, false, [], [87579, 3, 15]⟩,
        ⟨79598, false, false, [30189], [15]⟩,
        ⟨79640, true, false, [], [93547, 15]⟩,
        ⟨79486, false, false, [30191], []⟩,
        ⟨79641, false, false, [], []⟩
      ]⟩,
    ⟨[30193], [30190], .source 15161⟩,
    ⟨[30190], [30190], .contexts []⟩,
    ⟨[30197], [30193, 30181], .source 15163⟩,
    ⟨[30199], [30193, 30185], .source 15164⟩,
    ⟨[30169, 93549], [30169, 93549], .contexts []⟩,
    ⟨[93547], [30191, 93545], .contexts [
        ⟨79642, false, false, [], []⟩
      ]⟩,
    ⟨[93547], [30191, 93545], .contexts [
        ⟨79648, false, false, [], []⟩,
        ⟨79641, false, false, [], []⟩
      ]⟩,
    ⟨[30201], [30169, 30191], .source 15165⟩,
    ⟨[30201, 93541], [30201, 93541], .contexts []⟩,
    ⟨[30201, 93541, 13], [84491], .contexts [
        ⟨79651, true, false, [], [13]⟩,
        ⟨79479, true, false, [30201], [13]⟩,
        ⟨79483, true, false, [30201], [1, 13]⟩,
        ⟨79650, false, false, [], [93545, 13, 1, 13]⟩,
        ⟨79649, true, false, [30169], [13, 1, 13]⟩,
        ⟨79490, true, false, [30169], [13, 1, 13]⟩,
        ⟨79647, true, false, [], [1, 13, 1, 13]⟩,
        ⟨79647, true, false, [], [1, 13, 1, 13]⟩,
        ⟨79623, true, false, [], [1, 13, 1, 13]⟩,
        ⟨79620, true, false, [], [1, 13, 1, 13]⟩,
        ⟨2012, false, false, [84489], []⟩,
        ⟨44117, false, false, [], []⟩,
        ⟨27105, false, false, [], []⟩
      ]⟩,
    ⟨[30203], [30200], .source 15166⟩,
    ⟨[30200], [30200], .contexts []⟩,
    ⟨[30205], [24249, 30201], .source 15167⟩,
    ⟨[30207], [30204], .source 15168⟩,
    ⟨[93541], [30207, 89699], .contexts [
        ⟨79655, false, false, [30204], [93541]⟩,
        ⟨57113, false, false, [30204], [30201, 93541]⟩,
        ⟨79651, true, false, [30204, 24246], []⟩,
        ⟨79653, true, true, [30204, 24246], [93541]⟩,
        ⟨59, true, false, [30204, 24246, 30202, 93541], []⟩,
        ⟨79652, false, false, [30204, 24246, 30202, 30200], [13]⟩,
        ⟨27113, false, false, [30204, 24246, 30202, 30200], [13]⟩,
        ⟨79654, true, false, [30204, 24246, 30202], [84491, 13]⟩,
        ⟨79654, true, false, [30204, 24246, 30202], [84491, 13]⟩,
        ⟨79653, true, false, [30204, 24246, 30202], [84491, 13]⟩,
        ⟨57153, false, false, [30204, 24246], []⟩,
        ⟨79656, true, false, [], [89699]⟩
      ]⟩,
    ⟨[30209], [30207, 24243], .source 15169⟩,
    ⟨[30211], [30208], .source 15170⟩,
    ⟨[30211], [30208], .contexts [
        ⟨79659, false, false, [], []⟩
      ]⟩,
    ⟨[30211], [30208], .contexts [
        ⟨79660, false, false, [], []⟩,
        ⟨13, false, false, [30208], []⟩
      ]⟩,
    ⟨[30209], [30210], .contexts [
        ⟨79659, true, true, [], []⟩
      ]⟩,
    ⟨[93543], [30209, 87411], .contexts [
        ⟨79661, false, false, [30210], [93543]⟩,
        ⟨79494, true, false, [30210, 30208], []⟩,
        ⟨79477, true, false, [30210, 30208], []⟩,
        ⟨79657, false, false, [30210, 30208], [1]⟩,
        ⟨57106, false, false, [30210, 30208, 30207], []⟩,
        ⟨79658, true, false, [30210, 30208], [87411]⟩,
        ⟨79662, true, false, [], [87411]⟩
      ]⟩,
    ⟨[30208], [30208], .contexts []⟩,
    ⟨[30211], [30208], .contexts [
        ⟨79660, false, false, [], []⟩,
        ⟨79664, false, false, [], []⟩,
        ⟨79664, false, false, [], []⟩
      ]⟩,
    ⟨[89701], [24243, 87415], .contexts [
        ⟨57097, false, false, [], []⟩,
        ⟨57093, false, false, [], []⟩
      ]⟩,
    ⟨[93539], [30209, 87415], .contexts [
        ⟨79661, false, false, [30210], [93539]⟩,
        ⟨79495, true, false, [30210, 30208], []⟩,
        ⟨79475, true, false, [30210, 30208], []⟩,
        ⟨79657, false, false, [30210, 30208], [11]⟩,
        ⟨56953, false, false, [30210, 30208, 30207], []⟩,
        ⟨79666, false, false, [30210, 30208, 30207], []⟩,
        ⟨79658, true, false, [30210, 30208], [87415]⟩,
        ⟨79662, true, false, [], [87415]⟩
      ]⟩,
    ⟨[87415, 9], [30211, 93537], .contexts [
        ⟨79667, true, false, [30208], [9]⟩,
        ⟨79472, false, false, [30208], []⟩,
        ⟨79496, false, false, [30208], []⟩,
        ⟨79665, true, false, [], [93537]⟩
      ]⟩,
    ⟨[30187, 93547], [30187, 30191, 93545], .contexts [
        ⟨79649, false, false, [30187], []⟩
      ]⟩,
    ⟨[30213], [30187, 30191], .source 15171⟩,
    ⟨[26509, 91735], [26509, 91735], .contexts []⟩,
    ⟨[26509, 91735], [26509, 91735], .contexts []⟩,
    ⟨[30215], [30212], .source 15172⟩,
    ⟨[30217], [30215, 26509], .source 15173⟩,
    ⟨[93545, 5], [30217, 91733], .contexts [
        ⟨79670, false, false, [30212], [93545, 5]⟩,
        ⟨79669, true, false, [30212], [5]⟩,
        ⟨79638, true, false, [30212], [5]⟩,
        ⟨79635, true, false, [30212], [5]⟩,
        ⟨642, false, false, [30212, 89705], []⟩,
        ⟨643, false, false, [30212, 89705], []⟩,
        ⟨67290, false, false, [30212], [11]⟩,
        ⟨67293, false, false, [30212], [11]⟩,
        ⟨79671, false, false, [30212], [11]⟩,
        ⟨79672, false, false, [30212], [11]⟩,
        ⟨79672, false, false, [30212], [11]⟩,
        ⟨67177, false, false, [30212, 26509], []⟩,
        ⟨67317, false, false, [30212, 26509], []⟩,
        ⟨79673, true, false, [], [26509, 91733]⟩,
        ⟨79674, true, false, [], [91733]⟩
      ]⟩,
    ⟨[30219], [30216], .source 15174⟩,
    ⟨[91733, 5], [30219, 93545], .contexts [
        ⟨79675, true, false, [30216], [5]⟩,
        ⟨28, false, false, [30216, 93545], []⟩,
        ⟨79676, true, false, [], [93545]⟩
      ]⟩,
    ⟨[30221], [24249, 22267], .source 15175⟩,
    ⟨[89701], [24243, 87415], .contexts [
        ⟨79666, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1245. -/
def y322TCIndexRaw1245 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[30223], [24243, 30211], .source 15176⟩,
    ⟨[93537], [93537], .contexts []⟩,
    ⟨[30225], [30220], .source 15177⟩,
    ⟨[30227], [30225, 30223], .source 15178⟩,
    ⟨[85625, 11], [30227, 93537], .contexts [
        ⟨79678, false, false, [30220], [85625, 11]⟩,
        ⟨48340, true, false, [30220, 24249], [11]⟩,
        ⟨57193, true, false, [30220], [9, 11]⟩,
        ⟨57193, true, false, [30220], [9, 11]⟩,
        ⟨57192, true, false, [30220], [9, 11]⟩,
        ⟨57196, true, false, [30220], [9, 11]⟩,
        ⟨57159, true, false, [30220], [11, 9, 11]⟩,
        ⟨536, false, false, [30220, 89699], []⟩,
        ⟨537, false, false, [30220, 89699], []⟩,
        ⟨56953, false, false, [30220], [9]⟩,
        ⟨79679, false, false, [30220], [9]⟩,
        ⟨57093, false, false, [30220], [9]⟩,
        ⟨57093, false, false, [30220], [9]⟩,
        ⟨79668, false, false, [30220, 24243], []⟩,
        ⟨79680, true, false, [30220], [93537]⟩,
        ⟨79681, false, false, [30220, 30223], []⟩,
        ⟨79682, true, false, [], [30223, 93537]⟩,
        ⟨79683, true, false, [], [93537]⟩
      ]⟩,
    ⟨[30229], [30226], .source 15179⟩,
    ⟨[30211, 93537], [30211, 93537], .contexts []⟩,
    ⟨[30211, 93537], [30211, 93537], .contexts []⟩,
    ⟨[87415, 9], [30211, 93537], .contexts [
        ⟨79668, false, false, [], []⟩,
        ⟨79686, false, false, [], []⟩,
        ⟨79687, false, false, [], []⟩,
        ⟨79687, false, false, [], []⟩
      ]⟩,
    ⟨[87415, 8], [87415, 9], .contexts [
        ⟨47, false, false, [87415], []⟩
      ]⟩,
    ⟨[88345, 13], [88345, 13], .contexts []⟩,
    ⟨[88345, 13], [30211, 93537], .contexts [
        ⟨79690, false, false, [], []⟩,
        ⟨50001, true, false, [], [13]⟩,
        ⟨50001, true, false, [], [13]⟩,
        ⟨50000, true, false, [], [13]⟩,
        ⟨49999, true, false, [], [13]⟩,
        ⟨57107, true, false, [], [9, 13]⟩,
        ⟨942, false, false, [87415], []⟩,
        ⟨79689, false, false, [], []⟩,
        ⟨79688, false, false, [], []⟩,
        ⟨79681, false, false, [30211], []⟩,
        ⟨13, true, false, [], [30211, 93537]⟩
      ]⟩,
    ⟨[30231], [20427, 30211], .source 15180⟩,
    ⟨[30233], [30230], .source 15181⟩,
    ⟨[30235], [30233, 30211], .source 15182⟩,
    ⟨[93537, 3], [30235, 93537], .contexts [
        ⟨79692, false, false, [30230], [93537, 3]⟩,
        ⟨79668, true, false, [30230, 20427], [3]⟩,
        ⟨57116, true, false, [30230], [9, 3]⟩,
        ⟨573, false, false, [30230, 87415], []⟩,
        ⟨79689, false, false, [30230], []⟩,
        ⟨79688, false, false, [30230], []⟩,
        ⟨79681, false, false, [30230, 30211], []⟩,
        ⟨79693, true, false, [], [30211, 93537]⟩,
        ⟨79694, true, false, [], [93537]⟩
      ]⟩,
    ⟨[83893, 5], [83893, 5], .contexts []⟩,
    ⟨[30237], [22695, 30211], .source 15183⟩,
    ⟨[83893, 5], [30237, 93537], .contexts [
        ⟨79696, false, false, [], []⟩,
        ⟨50014, false, false, [22692], [83893, 5]⟩,
        ⟨40468, true, false, [22692, 20421], [5]⟩,
        ⟨42874, true, false, [22692], [9, 5]⟩,
        ⟨960, false, false, [22692, 87415], []⟩,
        ⟨79689, false, false, [22692], []⟩,
        ⟨79688, false, false, [22692], []⟩,
        ⟨79681, false, false, [22692, 30211], []⟩,
        ⟨50016, true, false, [], [30211, 93537]⟩,
        ⟨79697, true, false, [], [93537]⟩
      ]⟩,
    ⟨[30239], [30236], .source 15184⟩,
    ⟨[30241], [23899, 29841], .source 15185⟩,
    ⟨[93269, 7], [93269, 7], .contexts []⟩,
    ⟨[30243], [30240], .source 15186⟩,
    ⟨[30245], [30243, 30211], .source 15187⟩,
    ⟨[93269, 7], [30245, 93537], .contexts [
        ⟨79701, false, false, [], []⟩,
        ⟨79700, false, false, [30240], [93269, 7]⟩,
        ⟨78267, true, false, [30240, 23899], [7]⟩,
        ⟨57130, true, false, [30240], [9, 7]⟩,
        ⟨579, false, false, [30240, 87415], []⟩,
        ⟨79689, false, false, [30240], []⟩,
        ⟨79688, false, false, [30240], []⟩,
        ⟨79681, false, false, [30240, 30211], []⟩,
        ⟨79702, true, false, [], [30211, 93537]⟩,
        ⟨79703, true, false, [], [93537]⟩
      ]⟩,
    ⟨[30247], [30244], .source 15188⟩,
    ⟨[22689, 85619], [22689, 85619], .contexts []⟩,
    ⟨[22689, 85619], [22689, 85619], .contexts []⟩,
    ⟨[30249], [22689, 29243], .source 15189⟩,
    ⟨[93535, 13], [93535, 13], .contexts []⟩,
    ⟨[30251], [30209, 30249], .source 15190⟩,
    ⟨[93535, 13], [30251, 92949], .contexts [
        ⟨79709, false, false, [], []⟩,
        ⟨79468, true, false, [], [13]⟩,
        ⟨79687, true, false, [30210], [1, 13]⟩,
        ⟨79687, true, false, [30210], [1, 13]⟩,
        ⟨79686, true, false, [30210], [1, 13]⟩,
        ⟨79691, true, false, [30210], [1, 13]⟩,
        ⟨79690, true, false, [30210], [1, 13]⟩,
        ⟨1968, false, false, [30210, 88345], []⟩,
        ⟨248, false, false, [30210, 88345], []⟩,
        ⟨50008, false, false, [30210], [13, 1]⟩,
        ⟨50010, false, false, [30210], [13, 1]⟩,
        ⟨79706, false, false, [30210], [13, 1]⟩,
        ⟨79707, false, false, [30210], [13, 1]⟩,
        ⟨79707, false, false, [30210], [13, 1]⟩,
        ⟨76166, false, false, [30210, 22689], [1]⟩,
        ⟨79708, true, false, [30210], [92951, 1]⟩,
        ⟨75962, false, false, [30210, 30249], []⟩,
        ⟨76153, false, false, [30210, 30249], []⟩,
        ⟨79662, true, false, [], [30249, 92949]⟩,
        ⟨79710, true, false, [], [92949]⟩
      ]⟩,
    ⟨[30253], [30250], .source 15191⟩,
    ⟨[92949, 13], [30253, 93535], .contexts [
        ⟨79711, true, false, [30250], [13]⟩,
        ⟨59, false, false, [30250, 93535], []⟩,
        ⟨79712, true, false, [], [93535]⟩
      ]⟩,
    ⟨[30237, 93537], [30237, 93537], .contexts []⟩,
    ⟨[30237, 93535], [30237, 93535], .contexts []⟩,
    ⟨[30237, 93533], [30237, 93533], .contexts []⟩,
    ⟨[30236], [30236], .contexts []⟩,
    ⟨[93533, 1], [30239, 83893], .contexts [
        ⟨79716, true, false, [30236], [1]⟩,
        ⟨79464, true, false, [], [1]⟩,
        ⟨79715, true, false, [30236], [5, 1]⟩,
        ⟨79468, true, false, [], [5, 1]⟩,
        ⟨79714, true, false, [30236], [1, 5, 1]⟩,
        ⟨79714, true, false, [30236], [1, 5, 1]⟩,
        ⟨79698, true, false, [30236], [1, 5, 1]⟩,
        ⟨79696, true, false, [30236], [1, 5, 1]⟩,
        ⟨874, false, false, [30236, 83893], []⟩,
        ⟨40466, false, false, [30236], []⟩,
        ⟨79717, true, false, [], [83893]⟩,
        ⟨79717, true, false, [], [83893]⟩,
        ⟨79699, true, false, [], [83893]⟩
      ]⟩,
    ⟨[30237], [30238], .contexts [
        ⟨79699, true, true, [], []⟩
      ]⟩,
    ⟨[93533], [30239, 83891], .contexts [
        ⟨79716, true, false, [30236], []⟩,
        ⟨79719, false, false, [30236], [93533]⟩,
        ⟨8, true, false, [30236, 30238, 93533], []⟩,
        ⟨79718, false, false, [30236, 30238], [1]⟩,
        ⟨23413, false, false, [30236], []⟩,
        ⟨23414, false, false, [30236], []⟩,
        ⟨23342, false, false, [30236], []⟩,
        ⟨23342, false, false, [30236], []⟩,
        ⟨79699, true, false, [], [83891]⟩
      ]⟩,
    ⟨[30238], [30238], .contexts []⟩,
    ⟨[83891, 5], [30237, 93535], .contexts [
        ⟨79720, true, false, [30238], [5]⟩,
        ⟨79462, false, false, [30238], []⟩,
        ⟨79498, false, false, [30238], []⟩,
        ⟨79721, true, false, [], [93535]⟩,
        ⟨79721, true, false, [], [93535]⟩,
        ⟨79719, true, false, [], [93535]⟩
      ]⟩,
    ⟨[93533], [30239, 83891], .contexts [
        ⟨79720, false, false, [], []⟩
      ]⟩,
    ⟨[93533], [30239, 83891], .contexts [
        ⟨79723, false, false, [], []⟩
      ]⟩,
    ⟨[30255], [26405, 27317], .source 15192⟩,
    ⟨[30257], [30239, 30255], .source 15193⟩,
    ⟨[30259], [30256], .source 15194⟩,
    ⟨[30259], [30256], .contexts [
        ⟨79727, false, false, [], []⟩
      ]⟩,
    ⟨[30259], [30256], .contexts [
        ⟨79728, false, false, [], []⟩,
        ⟨13, false, false, [30256], []⟩
      ]⟩,
    ⟨[30257], [30258], .contexts [
        ⟨79727, true, true, [], []⟩
      ]⟩,
    ⟨[84195], [30259, 93529], .contexts [
        ⟨25126, true, false, [], []⟩,
        ⟨79730, false, false, [30256], [84193, 1]⟩,
        ⟨79726, false, false, [30256, 30258, 30256], [84193, 1]⟩,
        ⟨79725, false, false, [30256, 30258, 30256, 30239], [84193, 1]⟩,
        ⟨70111, true, false, [30256, 30258, 30256, 30239, 26405], [1]⟩,
        ⟨66824, true, false, [30256, 30258, 30256, 30239], [1]⟩,
        ⟨79724, true, false, [30256, 30258, 30256], [3, 1]⟩,
        ⟨79460, false, false, [30256, 30258, 30256], [1]⟩,
        ⟨79499, false, false, [30256, 30258, 30256], [1]⟩,
        ⟨79729, true, false, [30256, 30258], [93531, 1]⟩,
        ⟨79457, false, false, [30256], []⟩,
        ⟨79500, false, false, [30256], []⟩,
        ⟨79729, true, false, [], [93529]⟩
      ]⟩,
    ⟨[30256], [30256], .contexts []⟩,
    ⟨[84195, 15], [30259, 93527], .contexts [
        ⟨79730, false, false, [30256], [84195, 15]⟩,
        ⟨79731, false, false, [30256, 30258], [15]⟩,
        ⟨79454, false, false, [30256], []⟩,
        ⟨79501, false, false, [30256], []⟩,
        ⟨79732, true, false, [], [93527]⟩,
        ⟨79732, true, false, [], [93527]⟩,
        ⟨79728, true, false, [], [93527]⟩
      ]⟩,
    ⟨[30245, 93537], [30245, 93537], .contexts []⟩,
    ⟨[30245, 93537], [30245, 93537], .contexts []⟩,
    ⟨[30245, 93535], [30245, 93535], .contexts []⟩,
    ⟨[30244], [30244], .contexts []⟩,
    ⟨[93535, 7], [30247, 93267], .contexts [
        ⟨79736, true, false, [30244], [7]⟩,
        ⟨79468, true, false, [], [7]⟩,
        ⟨79735, true, false, [30244], [1, 7]⟩,
        ⟨79735, true, false, [30244], [1, 7]⟩,
        ⟨79734, true, false, [30244], [1, 7]⟩,
        ⟨79704, true, false, [30244], [1, 7]⟩,
        ⟨79701, true, false, [30244], [1, 7]⟩,
        ⟨502, false, false, [30244, 93269], []⟩,
        ⟨9, false, false, [30244, 93269], []⟩,
        ⟨78103, false, false, [30244], []⟩,
        ⟨78104, false, false, [30244], []⟩,
        ⟨78075, false, false, [30244], []⟩,
        ⟨78075, false, false, [30244], []⟩,
        ⟨78291, false, false, [30244], []⟩,
        ⟨79737, true, false, [], [93267]⟩,
        ⟨79737, true, false, [], [93267]⟩,
        ⟨79705, true, false, [], [93267]⟩
      ]⟩,
    ⟨[93267, 7], [30245, 93535], .contexts [
        ⟨79738, true, false, [30246], [7]⟩,
        ⟨38, false, false, [30246, 93535], []⟩,
        ⟨79705, false, true, [], [93535]⟩
      ]⟩,
    ⟨[30251, 92949], [30251, 92949], .contexts []⟩,
    ⟨[30251, 92949], [30251, 92949], .contexts []⟩,
    ⟨[30261], [30251, 29237], .source 15195⟩,
    ⟨[30263], [30261, 24403], .source 15196⟩]

/-- Exact literal claimed equations and contextual derivations, block 1246. -/
def y322TCIndexRaw1246 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93535], [93535], .contexts []⟩,
    ⟨[30265], [30262], .source 15197⟩,
    ⟨[30262], [30262], .contexts []⟩,
    ⟨[88959, 9], [30265, 93535], .contexts [
        ⟨79743, false, false, [30262], [88959, 9]⟩,
        ⟨57835, true, false, [30262, 30261], [9]⟩,
        ⟨79742, false, false, [30262], [89833, 13, 9]⟩,
        ⟨76158, true, false, [30262, 30251], [13, 9]⟩,
        ⟨79741, true, false, [30262], [9, 13, 9]⟩,
        ⟨79741, true, false, [30262], [9, 13, 9]⟩,
        ⟨79740, true, false, [30262], [9, 13, 9]⟩,
        ⟨79711, true, false, [30262], [9, 13, 9]⟩,
        ⟨79709, true, false, [30262], [9, 13, 9]⟩,
        ⟨5366, false, false, [30262, 93535], []⟩,
        ⟨79744, false, false, [30262], []⟩,
        ⟨79746, true, false, [], [93535]⟩,
        ⟨79746, true, false, [], [93535]⟩,
        ⟨79745, true, false, [], [93535]⟩
      ]⟩,
    ⟨[93535, 9], [30263, 88959], .contexts [
        ⟨79747, true, false, [30264], [9]⟩,
        ⟨46, false, false, [30264, 88959], []⟩,
        ⟨79745, false, true, [], [88959]⟩
      ]⟩,
    ⟨[84195, 15], [30259, 93527], .contexts [
        ⟨79733, false, false, [], []⟩
      ]⟩,
    ⟨[30259, 93527], [30259, 93527], .contexts []⟩,
    ⟨[30259, 93527], [30259, 93527], .contexts []⟩,
    ⟨[91603], [91603], .contexts []⟩,
    ⟨[30267], [30257, 27315], .source 15198⟩,
    ⟨[93527, 1], [30267, 91603], .contexts [
        ⟨79751, true, false, [30258], [1]⟩,
        ⟨79751, true, false, [30258], [1]⟩,
        ⟨79750, true, false, [30258], [1]⟩,
        ⟨79749, true, false, [30258], [1]⟩,
        ⟨25131, true, false, [30258], [15, 1]⟩,
        ⟨25131, true, false, [30258], [15, 1]⟩,
        ⟨25198, true, false, [30258], [15, 1]⟩,
        ⟨25126, true, false, [30258], [15, 1]⟩,
        ⟨3040, false, false, [30258, 84193], []⟩,
        ⟨10, false, false, [30258, 84193], []⟩,
        ⟨70206, false, false, [30258], []⟩,
        ⟨79752, false, false, [30258, 27315], []⟩,
        ⟨79730, true, false, [], [27315, 91603]⟩,
        ⟨79753, true, false, [], [91603]⟩
      ]⟩,
    ⟨[30269], [30266], .source 15199⟩,
    ⟨[91603, 1], [30269, 93527], .contexts [
        ⟨79754, true, false, [30266], [1]⟩,
        ⟨8, false, false, [30266, 93527], []⟩,
        ⟨79755, true, false, [], [93527]⟩
      ]⟩,
    ⟨[84195, 13], [84197], .contexts [
        ⟨25130, false, false, [], []⟩,
        ⟨25196, false, false, [], []⟩,
        ⟨25135, false, false, [], []⟩,
        ⟨25135, false, false, [], []⟩
      ]⟩,
    ⟨[30271], [16951, 30259], .source 15200⟩,
    ⟨[30271, 93525], [30271, 93525], .contexts []⟩,
    ⟨[30271, 93525, 15], [84195], .contexts [
        ⟨79759, true, false, [], [15]⟩,
        ⟨79451, true, false, [30271], [15]⟩,
        ⟨79758, false, false, [], [93527, 13, 15]⟩,
        ⟨79733, true, false, [16951], [13, 15]⟩,
        ⟨44549, true, false, [], [15, 13, 15]⟩,
        ⟨44548, true, false, [], [15, 13, 15]⟩,
        ⟨44547, true, false, [], [15, 13, 15]⟩,
        ⟨44546, true, false, [], [15, 13, 15]⟩,
        ⟨25468, true, false, [], [13, 15, 13, 15]⟩,
        ⟨25468, true, false, [], [13, 15, 13, 15]⟩,
        ⟨44545, true, false, [], [13, 15, 13, 15]⟩,
        ⟨25134, true, false, [], [13, 15, 13, 15]⟩,
        ⟨79757, true, false, [], [15, 13, 15, 13, 15]⟩,
        ⟨5843, false, false, [84195], []⟩
      ]⟩,
    ⟨[93525, 15], [93525, 15], .contexts []⟩,
    ⟨[84195], [84195], .contexts []⟩,
    ⟨[30273], [30270], .source 15201⟩,
    ⟨[30270], [30270], .contexts []⟩,
    ⟨[93525, 15], [30273, 84195], .contexts [
        ⟨79761, false, false, [], []⟩,
        ⟨79760, false, false, [30270], []⟩,
        ⟨79762, false, false, [30270], []⟩,
        ⟨79764, true, false, [], [84195]⟩,
        ⟨79764, true, false, [], [84195]⟩,
        ⟨79763, true, false, [], [84195]⟩
      ]⟩,
    ⟨[84195, 15], [30259, 93527], .contexts [
        ⟨79749, false, false, [], []⟩
      ]⟩,
    ⟨[30275], [30257, 30271], .source 15202⟩,
    ⟨[93527], [30275, 93525], .contexts [
        ⟨79751, true, false, [30258], []⟩,
        ⟨79751, true, false, [30258], []⟩,
        ⟨79750, true, false, [30258], []⟩,
        ⟨79766, true, false, [30258], []⟩,
        ⟨79765, true, false, [30258, 30272], [15]⟩,
        ⟨1, false, false, [30258, 30272, 93525], []⟩,
        ⟨79763, false, true, [30258], [93525]⟩,
        ⟨79759, false, false, [30258], []⟩,
        ⟨79730, true, false, [], [30271, 93525]⟩,
        ⟨79767, true, false, [], [93525]⟩
      ]⟩,
    ⟨[30275, 93525], [30275, 93525], .contexts []⟩,
    ⟨[93527], [30275, 93525], .contexts [
        ⟨79768, false, false, [], []⟩,
        ⟨79769, false, false, [], []⟩
      ]⟩,
    ⟨[30277], [30274], .source 15203⟩,
    ⟨[30279], [30277, 30267], .source 15204⟩,
    ⟨[93523], [30279, 91603], .contexts [
        ⟨79447, true, false, [], []⟩,
        ⟨79770, true, false, [30274], [1]⟩,
        ⟨79754, false, false, [30274], []⟩,
        ⟨79771, true, false, [], [30267, 91603]⟩,
        ⟨79772, true, false, [], [91603]⟩
      ]⟩,
    ⟨[30281], [30278], .source 15205⟩,
    ⟨[30278], [30278], .contexts []⟩,
    ⟨[91603, 11], [30281, 93521], .contexts [
        ⟨79773, true, false, [30278], [11]⟩,
        ⟨79444, false, false, [30278], []⟩,
        ⟨79503, false, false, [30278], []⟩,
        ⟨79775, true, false, [], [93521]⟩,
        ⟨79775, true, false, [], [93521]⟩,
        ⟨79774, true, false, [], [93521]⟩
      ]⟩,
    ⟨[27323, 84195], [27323, 84195], .contexts []⟩,
    ⟨[27323, 84195], [27323, 84195], .contexts []⟩,
    ⟨[84195, 9], [27323, 84195], .contexts [
        ⟨70101, false, false, [], []⟩,
        ⟨79777, false, false, [], []⟩,
        ⟨79778, false, false, [], []⟩,
        ⟨79778, false, false, [], []⟩
      ]⟩,
    ⟨[30283], [30259, 30275], .source 15206⟩,
    ⟨[30285], [27323, 30283], .source 15207⟩,
    ⟨[84195, 15], [30283, 93525], .contexts [
        ⟨79766, false, false, [], []⟩,
        ⟨79770, false, false, [30259], []⟩,
        ⟨79780, true, false, [], [93525]⟩
      ]⟩,
    ⟨[84195, 14], [84195, 15], .contexts [
        ⟨10, false, false, [84195], []⟩
      ]⟩,
    ⟨[93525, 9], [93525, 9], .contexts []⟩,
    ⟨[93525], [93525], .contexts []⟩,
    ⟨[30287], [30284], .source 15208⟩,
    ⟨[30289], [30287, 30283], .source 15209⟩,
    ⟨[84195, 7], [27325, 85925], .contexts [
        ⟨70104, false, false, [], []⟩
      ]⟩,
    ⟨[27325, 85925], [27325, 85925], .contexts []⟩,
    ⟨[84195, 7], [27325, 85925], .contexts [
        ⟨79788, false, false, [], []⟩,
        ⟨79789, false, false, [], []⟩,
        ⟨79789, false, false, [], []⟩
      ]⟩,
    ⟨[30291], [27324], .source 15210⟩,
    ⟨[30293], [30291, 30283], .source 15211⟩,
    ⟨[30295], [30292], .source 15212⟩,
    ⟨[93525, 7], [30295, 85923], .contexts [
        ⟨79792, false, false, [30292], [93525, 7]⟩,
        ⟨79791, false, false, [30292], [30283, 93525, 7]⟩,
        ⟨79785, true, false, [30292, 27324, 30283], [7]⟩,
        ⟨79782, true, false, [30292, 27324], [7]⟩,
        ⟨79783, true, false, [30292, 27324], [7]⟩,
        ⟨18155, true, false, [30292, 27324, 84195], [7]⟩,
        ⟨79790, false, false, [30292, 27324], [15, 7, 7]⟩,
        ⟨34212, false, false, [30292], [7, 7]⟩,
        ⟨38, false, false, [30292, 85923], []⟩,
        ⟨79793, true, false, [], [85923]⟩
      ]⟩,
    ⟨[93525, 13], [30275, 93525], .contexts [
        ⟨79449, false, false, [], []⟩,
        ⟨79770, false, false, [], []⟩,
        ⟨79769, false, false, [], []⟩,
        ⟨79769, false, false, [], []⟩
      ]⟩,
    ⟨[30297], [30275, 30295], .source 15213⟩,
    ⟨[30297, 85921], [30297, 85921], .contexts []⟩,
    ⟨[85921, 7], [85921, 7], .contexts []⟩,
    ⟨[30299], [30296], .source 15214⟩,
    ⟨[30296], [30296], .contexts []⟩,
    ⟨[85921, 7], [30299, 93525], .contexts [
        ⟨79798, false, false, [], []⟩,
        ⟨79797, true, false, [30296], [7]⟩,
        ⟨34208, true, false, [], [7]⟩,
        ⟨79796, false, false, [30296], [85923, 13, 7]⟩,
        ⟨79794, true, false, [30296, 30275], [13, 7]⟩,
        ⟨79795, true, false, [30296], [7, 13, 7]⟩,
        ⟨21371, false, false, [30296, 93525], []⟩,
        ⟨79785, false, false, [30296], []⟩,
        ⟨79800, true, false, [], [93525]⟩,
        ⟨79800, true, false, [], [93525]⟩,
        ⟨79799, true, false, [], [93525]⟩
      ]⟩,
    ⟨[30297], [30298], .contexts [
        ⟨79799, true, true, [], []⟩
      ]⟩,
    ⟨[30295, 85923], [30295, 85923], .contexts []⟩,
    ⟨[30301], [30293, 30297], .source 15215⟩,
    ⟨[85923], [30301, 85921], .contexts [
        ⟨79803, true, false, [30294], []⟩,
        ⟨79803, true, false, [30294], []⟩,
        ⟨79794, true, false, [30294], []⟩,
        ⟨79801, true, false, [30294, 30298], [7]⟩,
        ⟨38, false, false, [30294, 30298, 85921], []⟩,
        ⟨79802, true, false, [30294], [85921]⟩,
        ⟨79797, false, false, [30294], []⟩,
        ⟨79793, false, true, [], [30297, 85921]⟩,
        ⟨79804, true, false, [], [85921]⟩
      ]⟩,
    ⟨[30303], [30300], .source 15216⟩,
    ⟨[30303], [30300], .contexts [
        ⟨79806, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1247. -/
def y322TCIndexRaw1247 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[30300], [30300], .contexts []⟩,
    ⟨[85921, 15], [30303, 85925], .contexts [
        ⟨79805, true, false, [30300], [15]⟩,
        ⟨34210, false, false, [30300], []⟩,
        ⟨34332, false, false, [30300], []⟩,
        ⟨79808, true, false, [], [85925]⟩,
        ⟨79808, true, false, [], [85925]⟩,
        ⟨79807, true, false, [], [85925]⟩
      ]⟩,
    ⟨[85923], [30301, 85921], .contexts [
        ⟨79805, false, false, [], []⟩
      ]⟩,
    ⟨[30301, 85921], [30301, 85921], .contexts []⟩,
    ⟨[85923], [30301, 85921], .contexts [
        ⟨79810, false, false, [], []⟩,
        ⟨79811, false, false, [], []⟩
      ]⟩,
    ⟨[30281, 93521], [30281, 93521], .contexts []⟩,
    ⟨[91603, 11], [30281, 93521], .contexts [
        ⟨79776, false, false, [], []⟩,
        ⟨79813, false, false, [], []⟩,
        ⟨79813, false, false, [], []⟩
      ]⟩,
    ⟨[91603, 10], [91603, 11], .contexts [
        ⟨54, false, false, [91603], []⟩
      ]⟩,
    ⟨[91597, 13], [91597, 13], .contexts []⟩,
    ⟨[93521], [93521], .contexts []⟩,
    ⟨[30305], [29299, 30281], .source 15217⟩,
    ⟨[91597, 13], [30305, 93521], .contexts [
        ⟨79816, false, false, [], []⟩,
        ⟨76340, true, false, [29300], [13]⟩,
        ⟨76339, true, false, [29300], [13]⟩,
        ⟨76338, true, false, [29300], [13]⟩,
        ⟨76337, true, false, [29300], [13]⟩,
        ⟨76333, true, false, [29300], [11, 13]⟩,
        ⟨76333, true, false, [29300], [11, 13]⟩,
        ⟨76335, true, false, [29300], [11, 13]⟩,
        ⟨66635, true, false, [29300], [11, 13]⟩,
        ⟨931, false, false, [29300, 91603], []⟩,
        ⟨79815, false, false, [29300], []⟩,
        ⟨79814, false, false, [29300], []⟩,
        ⟨79817, false, false, [29300, 30281], []⟩,
        ⟨76377, true, false, [], [30281, 93521]⟩,
        ⟨79818, true, false, [], [93521]⟩
      ]⟩,
    ⟨[30307], [30304], .source 15218⟩,
    ⟨[91605], [27317, 84193], .contexts [
        ⟨70111, false, false, [], []⟩
      ]⟩,
    ⟨[84191, 15], [84191, 15], .contexts []⟩,
    ⟨[30309], [27315, 30281], .source 15219⟩,
    ⟨[84191, 15], [30309, 93521], .contexts [
        ⟨79822, false, false, [], []⟩,
        ⟨25124, true, false, [], [15]⟩,
        ⟨70105, true, false, [27316], [11, 15]⟩,
        ⟨70105, true, false, [27316], [11, 15]⟩,
        ⟨79821, true, false, [27316], [11, 15]⟩,
        ⟨66595, true, false, [27316], [11, 15]⟩,
        ⟨2046, false, false, [27316, 91603], []⟩,
        ⟨79815, false, false, [27316], []⟩,
        ⟨79814, false, false, [27316], []⟩,
        ⟨79817, false, false, [27316, 30281], []⟩,
        ⟨70092, true, false, [], [30281, 93521]⟩,
        ⟨79823, true, false, [], [93521]⟩
      ]⟩,
    ⟨[30311], [30308], .source 15220⟩,
    ⟨[30269, 93527], [30269, 30275, 93525], .contexts [
        ⟨79770, false, false, [30269], []⟩
      ]⟩,
    ⟨[30313], [30269, 30275], .source 15221⟩,
    ⟨[30315], [30295, 30301], .source 15222⟩,
    ⟨[30317], [30313, 30315], .source 15223⟩,
    ⟨[30317, 85919], [30317, 85919], .contexts []⟩,
    ⟨[30317, 85919], [30317, 85919], .contexts []⟩,
    ⟨[85919, 7], [85919, 7], .contexts []⟩,
    ⟨[30319], [30316], .source 15224⟩,
    ⟨[30316], [30316], .contexts []⟩,
    ⟨[85919, 7], [30319, 91603], .contexts [
        ⟨79832, false, false, [], []⟩,
        ⟨79831, true, false, [30316], [7]⟩,
        ⟨79830, true, false, [30316], [7]⟩,
        ⟨34204, true, false, [], [7]⟩,
        ⟨79829, false, false, [30316], [85921, 1, 7]⟩,
        ⟨79828, false, false, [30316, 30313], [85921, 1, 7]⟩,
        ⟨79812, true, false, [30316, 30313, 30295], [1, 7]⟩,
        ⟨79794, true, false, [30316, 30313], [1, 7]⟩,
        ⟨79827, false, false, [30316], [93525, 7, 1, 7]⟩,
        ⟨79826, true, false, [30316], [7, 1, 7]⟩,
        ⟨79756, true, false, [30316], [7, 1, 7]⟩,
        ⟨4091, false, false, [30316, 91603], []⟩,
        ⟨79752, false, false, [30316], []⟩,
        ⟨79834, true, false, [], [91603]⟩,
        ⟨79834, true, false, [], [91603]⟩,
        ⟨79833, true, false, [], [91603]⟩
      ]⟩,
    ⟨[91603, 7], [30317, 85919], .contexts [
        ⟨79835, true, false, [30318], [7]⟩,
        ⟨38, false, false, [30318, 85919], []⟩,
        ⟨79833, false, true, [], [85919]⟩
      ]⟩,
    ⟨[93521, 7], [93521, 7], .contexts []⟩,
    ⟨[85917], [85917], .contexts []⟩,
    ⟨[30279], [30279], .contexts []⟩,
    ⟨[30321], [30279, 30317], .source 15225⟩,
    ⟨[93521, 7], [30321, 85917], .contexts [
        ⟨79837, false, false, [], []⟩,
        ⟨79814, true, false, [30280], [7]⟩,
        ⟨647, false, false, [30280, 91603], []⟩,
        ⟨648, false, false, [30280, 91603], []⟩,
        ⟨79836, false, false, [30280], [11]⟩,
        ⟨79830, false, false, [30280], [11]⟩,
        ⟨79831, false, false, [30280], [11]⟩,
        ⟨79831, false, false, [30280], [11]⟩,
        ⟨34200, false, false, [30280, 30317], []⟩,
        ⟨79838, false, false, [30280, 30317], []⟩,
        ⟨79774, false, true, [], [30317, 85917]⟩,
        ⟨79839, true, false, [], [30317, 85917]⟩,
        ⟨79840, true, false, [], [85917]⟩
      ]⟩,
    ⟨[30323], [30320], .source 15226⟩,
    ⟨[85917, 7], [30323, 93521], .contexts [
        ⟨79841, true, false, [30320], [7]⟩,
        ⟨38, false, false, [30320, 93521], []⟩,
        ⟨79842, true, false, [], [93521]⟩
      ]⟩,
    ⟨[30303, 85925], [30303, 85925], .contexts []⟩,
    ⟨[30303, 85927], [30303, 85927], .contexts []⟩,
    ⟨[30303, 85927], [30303, 85927], .contexts []⟩,
    ⟨[85919, 15], [85919, 15], .contexts []⟩,
    ⟨[85919, 15], [30303, 85927], .contexts [
        ⟨79847, false, false, [], []⟩,
        ⟨34203, true, false, [], [15]⟩,
        ⟨34203, true, false, [], [15]⟩,
        ⟨34339, true, false, [], [15]⟩,
        ⟨34338, true, false, [], [15]⟩,
        ⟨121, false, false, [85921], []⟩,
        ⟨122, false, false, [85921], []⟩,
        ⟨79809, false, false, [], [1]⟩,
        ⟨79844, false, false, [], [1]⟩,
        ⟨79844, false, false, [], [1]⟩,
        ⟨34214, false, false, [30303], []⟩,
        ⟨79845, false, false, [], []⟩,
        ⟨79846, false, false, [], []⟩,
        ⟨35924, false, false, [30303], []⟩,
        ⟨13, true, false, [], [30303, 85927]⟩
      ]⟩,
    ⟨[85927, 15], [30301, 85919], .contexts [
        ⟨79848, true, false, [30302], [15]⟩,
        ⟨1, false, false, [30302, 85919], []⟩,
        ⟨79806, false, true, [], [85919]⟩
      ]⟩,
    ⟨[30305, 93521], [30305, 93521], .contexts []⟩,
    ⟨[30305, 93519], [30305, 93519], .contexts []⟩,
    ⟨[30305, 93519], [30305, 93519], .contexts []⟩,
    ⟨[91597, 8], [91597, 9], .contexts [
        ⟨47, false, false, [91597], []⟩
      ]⟩,
    ⟨[91595], [91595], .contexts []⟩,
    ⟨[30307], [30304], .contexts [
        ⟨79820, false, false, [], []⟩
      ]⟩,
    ⟨[30304], [30304], .contexts []⟩,
    ⟨[93519, 13], [30307, 91595], .contexts [
        ⟨79852, true, false, [30304], [13]⟩,
        ⟨79851, true, false, [30304], [13]⟩,
        ⟨79440, true, false, [], [13]⟩,
        ⟨79850, true, false, [30304], [9, 13]⟩,
        ⟨79850, true, false, [30304], [9, 13]⟩,
        ⟨79819, true, false, [30304], [9, 13]⟩,
        ⟨79816, true, false, [30304], [9, 13]⟩,
        ⟨942, false, false, [30304, 91597], []⟩,
        ⟨79853, false, false, [30304], []⟩,
        ⟨76375, false, false, [30304], []⟩,
        ⟨79854, false, false, [30304], []⟩,
        ⟨79856, true, false, [], [91595]⟩,
        ⟨79856, true, false, [], [91595]⟩,
        ⟨79855, true, false, [], [91595]⟩
      ]⟩,
    ⟨[91595, 13], [30305, 93519], .contexts [
        ⟨79857, true, false, [30306], [13]⟩,
        ⟨59, false, false, [30306, 93519], []⟩,
        ⟨79820, false, true, [], [93519]⟩
      ]⟩,
    ⟨[30309, 93521], [30309, 93521], .contexts []⟩,
    ⟨[93519, 15], [93519, 15], .contexts []⟩,
    ⟨[30311], [30308], .contexts [
        ⟨79825, false, false, [], []⟩
      ]⟩,
    ⟨[30308], [30308], .contexts []⟩,
    ⟨[30311], [30308], .contexts [
        ⟨79861, false, false, [], []⟩,
        ⟨79862, false, false, [], []⟩,
        ⟨79862, false, false, [], []⟩
      ]⟩,
    ⟨[93519, 15], [30311, 84189], .contexts [
        ⟨79860, false, false, [], []⟩,
        ⟨79440, true, false, [], [15]⟩,
        ⟨79859, true, false, [30308], [9, 15]⟩,
        ⟨79859, true, false, [30308], [9, 15]⟩,
        ⟨79824, true, false, [30308], [9, 15]⟩,
        ⟨79822, true, false, [30308], [9, 15]⟩,
        ⟨1671, false, false, [30308, 84191], []⟩,
        ⟨70238, false, false, [30308], []⟩,
        ⟨70237, false, false, [30308], []⟩,
        ⟨70239, false, false, [30308], []⟩,
        ⟨79863, true, false, [], [84189]⟩
      ]⟩,
    ⟨[30309], [30310], .contexts [
        ⟨79825, true, true, [], []⟩
      ]⟩,
    ⟨[30321, 85917], [30321, 85917], .contexts []⟩,
    ⟨[93521, 7], [30321, 85917], .contexts [
        ⟨79837, false, false, [], []⟩,
        ⟨79841, false, false, [], []⟩,
        ⟨79866, false, false, [], []⟩,
        ⟨79866, false, false, [], []⟩
      ]⟩,
    ⟨[93521, 9], [93519], .contexts [
        ⟨79504, false, false, [], []⟩,
        ⟨79505, false, false, [], []⟩,
        ⟨79439, false, false, [], []⟩,
        ⟨79439, false, false, [], []⟩
      ]⟩,
    ⟨[93521, 8], [93521, 9], .contexts [
        ⟨47, false, false, [93521], []⟩
      ]⟩,
    ⟨[85915, 7], [85915, 7], .contexts []⟩,
    ⟨[93519], [93519], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1248. -/
def y322TCIndexRaw1248 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[30320], [30320], .contexts []⟩,
    ⟨[85915, 7], [30323, 93519], .contexts [
        ⟨79870, false, false, [], []⟩,
        ⟨34196, true, false, [], [7]⟩,
        ⟨79867, true, false, [30320], [9, 7]⟩,
        ⟨579, false, false, [30320, 93521], []⟩,
        ⟨79869, false, false, [30320], []⟩,
        ⟨79868, false, false, [30320], []⟩,
        ⟨79871, false, false, [30320], []⟩,
        ⟨79872, true, false, [], [93519]⟩,
        ⟨79872, true, false, [], [93519]⟩,
        ⟨79842, true, false, [], [93519]⟩
      ]⟩,
    ⟨[30321], [30322], .contexts [
        ⟨79842, true, true, [], []⟩
      ]⟩,
    ⟨[93519, 7], [30321, 85915], .contexts [
        ⟨79873, true, false, [30322], [7]⟩,
        ⟨38, false, false, [30322, 85915], []⟩,
        ⟨79874, true, false, [], [85915]⟩
      ]⟩,
    ⟨[85919, 15], [30303, 85927], .contexts [
        ⟨79847, false, false, [], []⟩,
        ⟨79848, false, false, [], []⟩,
        ⟨79845, false, false, [], []⟩,
        ⟨79846, false, false, [], []⟩,
        ⟨79846, false, false, [], []⟩
      ]⟩,
    ⟨[30325], [18943, 22451], .source 15227⟩,
    ⟨[30327], [30303, 30325], .source 15228⟩,
    ⟨[30327, 86201], [30327, 86201], .contexts []⟩,
    ⟨[30327, 86201], [30327, 86201], .contexts []⟩,
    ⟨[30329], [30326], .source 15229⟩,
    ⟨[30329], [30326], .contexts [
        ⟨79881, false, false, [], []⟩
      ]⟩,
    ⟨[30326], [30326], .contexts []⟩,
    ⟨[86201, 9], [30329, 85919], .contexts [
        ⟨79880, true, false, [30326], [9]⟩,
        ⟨79879, true, false, [30326], [9]⟩,
        ⟨35661, true, false, [], [9]⟩,
        ⟨79878, false, false, [30326], [86203, 15, 9]⟩,
        ⟨79877, false, false, [30326, 30303], [86203, 15, 9]⟩,
        ⟨49026, true, false, [30326, 30303, 18943], [15, 9]⟩,
        ⟨35926, true, false, [30326, 30303], [15, 9]⟩,
        ⟨79876, true, false, [30326], [9, 15, 9]⟩,
        ⟨2656, false, false, [30326, 85919], []⟩,
        ⟨79883, true, false, [], [85919]⟩,
        ⟨79883, true, false, [], [85919]⟩,
        ⟨79882, true, false, [], [85919]⟩
      ]⟩,
    ⟨[85919, 9], [30327, 86201], .contexts [
        ⟨79884, true, false, [30328], [9]⟩,
        ⟨46, false, false, [30328, 86201], []⟩,
        ⟨79881, false, true, [], [86201]⟩
      ]⟩,
    ⟨[30311, 84189], [30311, 84189], .contexts []⟩,
    ⟨[30311, 84189], [30311, 84189], .contexts []⟩,
    ⟨[30311, 84187], [30311, 84187], .contexts []⟩,
    ⟨[93519, 1], [93517], .contexts [
        ⟨79506, false, false, [], []⟩,
        ⟨79507, false, false, [], []⟩,
        ⟨79435, false, false, [], []⟩,
        ⟨79435, false, false, [], []⟩
      ]⟩,
    ⟨[84187, 15], [84187, 15], .contexts []⟩,
    ⟨[30309], [30309], .contexts []⟩,
    ⟨[30309], [30310], .contexts [
        ⟨79865, false, false, [], []⟩
      ]⟩,
    ⟨[30310], [30310], .contexts []⟩,
    ⟨[30309], [30310], .contexts [
        ⟨79891, false, false, [], []⟩,
        ⟨79892, false, false, [], []⟩,
        ⟨79893, false, false, [], []⟩,
        ⟨79893, false, false, [], []⟩
      ]⟩,
    ⟨[84187, 15], [30309, 93517], .contexts [
        ⟨79890, false, false, [], []⟩,
        ⟨79888, true, false, [30310], [15]⟩,
        ⟨25116, true, false, [], [15]⟩,
        ⟨79887, true, false, [30310], [1, 15]⟩,
        ⟨79887, true, false, [30310], [1, 15]⟩,
        ⟨79886, true, false, [30310], [1, 15]⟩,
        ⟨79864, true, false, [30310], [1, 15]⟩,
        ⟨79860, true, false, [30310], [1, 15]⟩,
        ⟨1666, false, false, [30310, 93519], []⟩,
        ⟨9, false, false, [30310, 93519], []⟩,
        ⟨79889, false, false, [30310], []⟩,
        ⟨79894, true, false, [], [93517]⟩
      ]⟩,
    ⟨[30323, 93519], [30323, 93519], .contexts []⟩,
    ⟨[30323, 93519], [30323, 93519], .contexts []⟩,
    ⟨[30323, 93517], [30323, 93517], .contexts []⟩,
    ⟨[30323, 93517], [30323, 93517], .contexts []⟩,
    ⟨[93517, 7], [93517, 7], .contexts []⟩,
    ⟨[85913], [85913], .contexts []⟩,
    ⟨[30322], [30322], .contexts []⟩,
    ⟨[93517, 7], [30321, 85913], .contexts [
        ⟨79900, false, false, [], []⟩,
        ⟨79899, true, false, [30322], [7]⟩,
        ⟨79898, true, false, [30322], [7]⟩,
        ⟨79436, true, false, [], [7]⟩,
        ⟨79897, true, false, [30322], [1, 7]⟩,
        ⟨79897, true, false, [30322], [1, 7]⟩,
        ⟨79896, true, false, [30322], [1, 7]⟩,
        ⟨79873, true, false, [30322], [1, 7]⟩,
        ⟨79870, true, false, [30322], [1, 7]⟩,
        ⟨502, false, false, [30322, 85915], []⟩,
        ⟨9, false, false, [30322, 85915], []⟩,
        ⟨34343, false, false, [30322], []⟩,
        ⟨34344, false, false, [30322], []⟩,
        ⟨34191, false, false, [30322], []⟩,
        ⟨34191, false, false, [30322], []⟩,
        ⟨79901, false, false, [30322], []⟩,
        ⟨79902, true, false, [], [85913]⟩,
        ⟨79902, true, false, [], [85913]⟩,
        ⟨79874, true, false, [], [85913]⟩
      ]⟩,
    ⟨[85913, 7], [30323, 93517], .contexts [
        ⟨79903, true, false, [30320], [7]⟩,
        ⟨38, false, false, [30320, 93517], []⟩,
        ⟨79842, true, false, [], [93517]⟩
      ]⟩,
    ⟨[30309, 93517], [30309, 93517], .contexts []⟩,
    ⟨[84187, 15], [30309, 93517], .contexts [
        ⟨79890, false, false, [], []⟩,
        ⟨79895, false, false, [], []⟩,
        ⟨79905, false, false, [], []⟩,
        ⟨79905, false, false, [], []⟩
      ]⟩,
    ⟨[84187, 5], [84185], .contexts [
        ⟨25208, false, false, [], []⟩,
        ⟨25209, false, false, [], []⟩,
        ⟨25111, false, false, [], []⟩,
        ⟨25111, false, false, [], []⟩
      ]⟩,
    ⟨[93515, 15], [93515, 15], .contexts []⟩,
    ⟨[93515, 15], [30311, 84185], .contexts [
        ⟨79908, false, false, [], []⟩,
        ⟨79432, true, false, [], [15]⟩,
        ⟨79906, true, false, [30308], [5, 15]⟩,
        ⟨2072, false, false, [30308, 84187], []⟩,
        ⟨29, false, false, [30308, 84187], []⟩,
        ⟨79907, false, false, [30308], []⟩,
        ⟨79863, true, false, [], [84185]⟩
      ]⟩,
    ⟨[30311, 84185], [30311, 84185], .contexts []⟩,
    ⟨[30311, 84183], [30311, 84183], .contexts []⟩,
    ⟨[84183, 15], [84183, 15], .contexts []⟩,
    ⟨[84183, 15], [30309, 93513], .contexts [
        ⟨79912, false, false, [], []⟩,
        ⟨79911, true, false, [30310], [15]⟩,
        ⟨25109, true, false, [], [15]⟩,
        ⟨79910, true, false, [30310], [3, 15]⟩,
        ⟨79910, true, false, [30310], [3, 15]⟩,
        ⟨79909, true, false, [30310], [3, 15]⟩,
        ⟨79908, true, false, [30310], [3, 15]⟩,
        ⟨1141, false, false, [30310, 93515], []⟩,
        ⟨21, false, false, [30310, 93515], []⟩,
        ⟨79511, false, false, [30310], []⟩,
        ⟨79512, false, false, [30310], []⟩,
        ⟨79427, false, false, [30310], []⟩,
        ⟨79427, false, false, [30310], []⟩,
        ⟨79894, true, false, [], [93513]⟩
      ]⟩,
    ⟨[84183, 15], [30309, 93513], .contexts [
        ⟨79912, false, false, [], []⟩,
        ⟨79913, false, false, [], []⟩
      ]⟩,
    ⟨[30309, 93513], [30309, 93513], .contexts []⟩,
    ⟨[30309, 93509], [30309, 93509], .contexts []⟩,
    ⟨[84183], [84183], .contexts []⟩,
    ⟨[30310, 93509, 1, 1], [84183, 1], .contexts [
        ⟨79916, true, false, [30310, 30308], [1, 1]⟩,
        ⟨79420, true, false, [30310], [1, 1]⟩,
        ⟨79424, true, false, [30310], [15, 1, 1]⟩,
        ⟨79915, true, false, [30310, 30308], [1, 15, 1, 1]⟩,
        ⟨79915, true, false, [30310, 30308], [1, 15, 1, 1]⟩,
        ⟨79914, true, false, [30310, 30308], [1, 15, 1, 1]⟩,
        ⟨504, false, false, [30310, 30308, 84183], [1]⟩,
        ⟨79917, false, false, [30310, 30308], [1]⟩,
        ⟨79863, true, false, [30310], [84183, 1]⟩
      ]⟩,
    ⟨[84183, 1], [84181], .contexts [
        ⟨25212, false, false, [], []⟩,
        ⟨25213, false, false, [], []⟩,
        ⟨25104, false, false, [], []⟩,
        ⟨25104, false, false, [], []⟩
      ]⟩,
    ⟨[93509], [30311, 84181], .contexts [
        ⟨79891, false, false, [30308], [93509]⟩,
        ⟨79916, true, false, [30308], []⟩,
        ⟨79865, false, false, [30308], [93509]⟩,
        ⟨8, true, false, [30308, 30310, 93509], []⟩,
        ⟨79918, false, false, [30308], []⟩,
        ⟨79919, false, false, [30308], []⟩,
        ⟨79825, true, false, [], [84181]⟩
      ]⟩,
    ⟨[30309], [30310], .contexts [
        ⟨79892, false, false, [], []⟩,
        ⟨79893, false, false, [], []⟩,
        ⟨79893, false, false, [], []⟩
      ]⟩,
    ⟨[84181, 13], [30309, 93507], .contexts [
        ⟨79920, true, false, [30310], [13]⟩,
        ⟨79416, false, false, [30310], []⟩,
        ⟨79514, false, false, [30310], []⟩,
        ⟨79921, true, false, [], [93507]⟩
      ]⟩,
    ⟨[84179, 1], [30309, 93513], .contexts [
        ⟨79825, false, false, [30310], [84179, 1]⟩,
        ⟨25101, true, false, [30310, 30308], [1]⟩,
        ⟨79920, true, false, [30310, 30308, 30310], [15, 1]⟩,
        ⟨79418, false, false, [30310, 30308, 30310], [1]⟩,
        ⟨79513, false, false, [30310, 30308, 30310], [1]⟩,
        ⟨13, true, false, [30310, 30308, 30310], [93511, 1]⟩,
        ⟨79892, true, false, [30310, 30308], [93511, 1]⟩,
        ⟨79422, false, false, [30310], []⟩,
        ⟨79512, false, false, [30310], []⟩,
        ⟨79921, true, false, [], [93513]⟩
      ]⟩,
    ⟨[93551], [82779, 3], .source 46840⟩,
    ⟨[82779, 3], [93551], .contexts [
        ⟨79924, true, false, [], []⟩
      ]⟩,
    ⟨[93551, 3], [82779], .contexts [
        ⟨79925, true, false, [], [3]⟩,
        ⟨20, false, false, [82779], []⟩,
        ⟨16524, false, false, [], []⟩
      ]⟩,
    ⟨[93551], [93551], .contexts []⟩,
    ⟨[93551], [93551], .contexts []⟩,
    ⟨[82779, 3], [93551], .contexts [
        ⟨79925, false, false, [], []⟩,
        ⟨79927, false, false, [], []⟩,
        ⟨79928, false, false, [], []⟩,
        ⟨79928, false, false, [], []⟩
      ]⟩,
    ⟨[30331], [1467, 553], .source 15230⟩,
    ⟨[30333], [30331, 1469], .source 15231⟩,
    ⟨[30333, 93551], [30333, 93551], .contexts []⟩,
    ⟨[30333, 93551], [30333, 93551], .contexts []⟩,
    ⟨[93551, 5], [93551, 5], .contexts []⟩,
    ⟨[93551], [93551], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1249. -/
def y322TCIndexRaw1249 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93551, 5], [30333, 93551], .contexts [
        ⟨79934, false, false, [], []⟩,
        ⟨79929, true, false, [], [5]⟩,
        ⟨871, false, false, [82779], []⟩,
        ⟨873, false, false, [82779], []⟩,
        ⟨16532, false, false, [], [3, 5, 3]⟩,
        ⟨16534, false, false, [], [3, 5, 3]⟩,
        ⟨16530, false, false, [], [3, 5, 3]⟩,
        ⟨16531, false, false, [], [3, 5, 3]⟩,
        ⟨16531, false, false, [], [3, 5, 3]⟩,
        ⟨16445, false, false, [1467], [5, 3]⟩,
        ⟨79930, true, false, [], [82773, 5, 3]⟩,
        ⟨16535, false, false, [30331], [3]⟩,
        ⟨79931, true, false, [], [82779, 3]⟩,
        ⟨79925, false, false, [30333], []⟩,
        ⟨79932, false, false, [], []⟩,
        ⟨79933, false, false, [], []⟩,
        ⟨79935, false, false, [30333], []⟩
      ]⟩,
    ⟨[30333], [30333], .contexts [
        ⟨13, false, false, [], [30333]⟩
      ]⟩,
    ⟨[93551, 5], [30333, 93551], .contexts [
        ⟨79936, false, false, [], []⟩,
        ⟨79937, true, false, [], [93551]⟩
      ]⟩,
    ⟨[16495, 83671], [16495, 83671], .contexts []⟩,
    ⟨[16495, 83671], [16495, 83671], .contexts []⟩,
    ⟨[93551, 7], [93551, 7], .contexts []⟩,
    ⟨[16495], [16495], .contexts [
        ⟨13, false, false, [], [16495]⟩
      ]⟩,
    ⟨[93551, 7], [16495, 83671], .contexts [
        ⟨79941, false, false, [], []⟩,
        ⟨79929, true, false, [], [7]⟩,
        ⟨140, false, false, [82779], []⟩,
        ⟨141, false, false, [82779], []⟩,
        ⟨16522, false, false, [], [3]⟩,
        ⟨16496, false, false, [], [3]⟩,
        ⟨16497, false, false, [], [3]⟩,
        ⟨16497, false, false, [], [3]⟩,
        ⟨22553, false, false, [], []⟩,
        ⟨79939, false, false, [], []⟩,
        ⟨79940, false, false, [], []⟩,
        ⟨79940, false, false, [], []⟩,
        ⟨22558, false, false, [16495], []⟩,
        ⟨79942, true, false, [], [83671]⟩
      ]⟩,
    ⟨[16493], [16494], .contexts [
        ⟨22552, true, true, [], []⟩
      ]⟩,
    ⟨[1063, 93551], [1063, 93551], .contexts []⟩,
    ⟨[1063, 93551], [1063, 93551], .contexts []⟩,
    ⟨[93551, 9], [1063, 93551], .contexts [
        ⟨79929, true, false, [], [9]⟩,
        ⟨669, false, false, [82779], []⟩,
        ⟨670, false, false, [82779], []⟩,
        ⟨16538, false, false, [], [3]⟩,
        ⟨16539, false, false, [], [3]⟩,
        ⟨16536, false, false, [], [3]⟩,
        ⟨16537, false, false, [], [3]⟩,
        ⟨16537, false, false, [], [3]⟩,
        ⟨79925, false, false, [1063], []⟩,
        ⟨79945, false, false, [], []⟩,
        ⟨79946, false, false, [], []⟩,
        ⟨79935, false, false, [1063], []⟩,
        ⟨3424, true, false, [], [93551]⟩
      ]⟩,
    ⟨[30335], [15205, 24031], .source 15232⟩,
    ⟨[93551, 13], [30335, 89439], .contexts [
        ⟨79929, true, false, [], [13]⟩,
        ⟨147, false, false, [82779], []⟩,
        ⟨148, false, false, [82779], []⟩,
        ⟨16547, false, false, [], [3]⟩,
        ⟨16550, false, false, [], [3]⟩,
        ⟨16544, false, false, [], [3]⟩,
        ⟨16546, false, false, [], [3]⟩,
        ⟨16546, false, false, [], [3]⟩,
        ⟨55926, false, false, [15205], []⟩,
        ⟨79948, true, false, [], [89439]⟩,
        ⟨55933, false, false, [30335], []⟩,
        ⟨13, true, false, [], [30335, 89439]⟩
      ]⟩,
    ⟨[30337], [30334], .source 15233⟩,
    ⟨[16861, 85325], [16861, 85325], .contexts []⟩,
    ⟨[16861, 85325], [16861, 85325], .contexts []⟩,
    ⟨[30339], [16861, 15097], .source 15234⟩,
    ⟨[93551, 15], [93551, 15], .contexts []⟩,
    ⟨[30339], [30339], .contexts [
        ⟨13, false, false, [], [30339]⟩
      ]⟩,
    ⟨[93551, 15], [30339, 86335], .contexts [
        ⟨79954, false, false, [], []⟩,
        ⟨79929, true, false, [], [15]⟩,
        ⟨151, false, false, [82779], []⟩,
        ⟨152, false, false, [82779], []⟩,
        ⟨31372, false, false, [], [3]⟩,
        ⟨79951, false, false, [], [3]⟩,
        ⟨79952, false, false, [], [3]⟩,
        ⟨79952, false, false, [], [3]⟩,
        ⟨36559, false, false, [16861], []⟩,
        ⟨79953, true, false, [], [86335]⟩,
        ⟨36563, false, false, [30339], []⟩,
        ⟨79955, true, false, [], [86335]⟩
      ]⟩,
    ⟨[30341], [30338], .source 15235⟩,
    ⟨[93553], [93551, 1], .source 46841⟩,
    ⟨[93551, 1], [93553], .contexts [
        ⟨79958, true, false, [], []⟩
      ]⟩,
    ⟨[93553, 1], [93551], .contexts [
        ⟨79959, true, false, [], [1]⟩,
        ⟨8, false, false, [93551], []⟩,
        ⟨79928, false, false, [], []⟩
      ]⟩,
    ⟨[93553], [93553], .contexts []⟩,
    ⟨[93553], [93553], .contexts []⟩,
    ⟨[93551, 1], [93553], .contexts [
        ⟨79959, false, false, [], []⟩,
        ⟨79961, false, false, [], []⟩,
        ⟨79962, false, false, [], []⟩,
        ⟨79962, false, false, [], []⟩
      ]⟩,
    ⟨[323, 93553], [323, 93553], .contexts []⟩,
    ⟨[323, 93553], [323, 93553], .contexts []⟩,
    ⟨[93553, 3], [93553, 3], .contexts []⟩,
    ⟨[93553], [93553], .contexts []⟩,
    ⟨[93553, 3], [323, 93553], .contexts [
        ⟨79966, false, false, [], []⟩,
        ⟨79963, true, false, [], [3]⟩,
        ⟨1098, false, false, [93551], []⟩,
        ⟨1100, false, false, [93551], []⟩,
        ⟨79926, false, false, [], [1, 3, 1]⟩,
        ⟨16523, false, false, [], [1, 3, 1]⟩,
        ⟨16524, false, false, [], [1, 3, 1]⟩,
        ⟨16524, false, false, [], [1, 3, 1]⟩,
        ⟨16529, false, false, [], [3, 1]⟩,
        ⟨16526, false, false, [], [3, 1]⟩,
        ⟨16527, false, false, [], [3, 1]⟩,
        ⟨16527, false, false, [], [3, 1]⟩,
        ⟨79925, false, false, [323], [1]⟩,
        ⟨79959, false, false, [323], []⟩,
        ⟨79964, false, false, [], []⟩,
        ⟨79965, false, false, [], []⟩,
        ⟨79967, false, false, [323], []⟩
      ]⟩,
    ⟨[93553, 3], [323, 93553], .contexts [
        ⟨79968, false, false, [], []⟩,
        ⟨3220, true, false, [], [93553]⟩
      ]⟩,
    ⟨[30333, 93553], [30333, 93553], .contexts []⟩,
    ⟨[30333, 93553], [30333, 93553], .contexts []⟩,
    ⟨[93553, 5], [93553, 5], .contexts []⟩,
    ⟨[93553, 5], [30333, 93553], .contexts [
        ⟨79972, false, false, [], []⟩,
        ⟨79963, true, false, [], [5]⟩,
        ⟨98, false, false, [93551], []⟩,
        ⟨99, false, false, [93551], []⟩,
        ⟨79934, false, false, [], [1]⟩,
        ⟨79938, false, false, [], [1]⟩,
        ⟨79932, false, false, [], [1]⟩,
        ⟨79933, false, false, [], [1]⟩,
        ⟨79933, false, false, [], [1]⟩,
        ⟨79959, false, false, [30333], []⟩,
        ⟨79970, false, false, [], []⟩,
        ⟨79971, false, false, [], []⟩,
        ⟨79967, false, false, [30333], []⟩,
        ⟨79937, true, false, [], [93553]⟩
      ]⟩,
    ⟨[16495, 83673], [16495, 83673], .contexts []⟩,
    ⟨[16495, 83673], [16495, 83673], .contexts []⟩,
    ⟨[93553, 7], [93553, 7], .contexts []⟩,
    ⟨[93553, 7], [16495, 83673], .contexts [
        ⟨79976, false, false, [], []⟩,
        ⟨79963, true, false, [], [7]⟩,
        ⟨104, false, false, [93551], []⟩,
        ⟨105, false, false, [93551], []⟩,
        ⟨79941, false, false, [], [1]⟩,
        ⟨79943, false, false, [], [1]⟩,
        ⟨79939, false, false, [], [1]⟩,
        ⟨79940, false, false, [], [1]⟩,
        ⟨79940, false, false, [], [1]⟩,
        ⟨22561, false, false, [16495], []⟩,
        ⟨79974, false, false, [], []⟩,
        ⟨79975, false, false, [], []⟩,
        ⟨22575, false, false, [16495], []⟩,
        ⟨79942, true, false, [], [83673]⟩
      ]⟩,
    ⟨[30339, 86335], [30339, 86335], .contexts []⟩,
    ⟨[30339, 86335], [30339, 86335], .contexts []⟩,
    ⟨[30339, 86337], [30339, 86337], .contexts []⟩,
    ⟨[30339, 86337], [30339, 86337], .contexts []⟩,
    ⟨[93553, 15], [93553, 15], .contexts []⟩,
    ⟨[93553, 15], [30339, 86337], .contexts [
        ⟨79982, false, false, [], []⟩,
        ⟨79963, true, false, [], [15]⟩,
        ⟨121, false, false, [93551], []⟩,
        ⟨122, false, false, [93551], []⟩,
        ⟨79954, false, false, [], [1]⟩,
        ⟨79956, false, false, [], [1]⟩,
        ⟨79978, false, false, [], [1]⟩,
        ⟨79979, false, false, [], [1]⟩,
        ⟨79979, false, false, [], [1]⟩,
        ⟨36574, false, false, [30339], []⟩,
        ⟨79980, false, false, [], []⟩,
        ⟨79981, false, false, [], []⟩,
        ⟨36585, false, false, [30339], []⟩,
        ⟨79955, true, false, [], [86337]⟩
      ]⟩,
    ⟨[86337, 15], [30341, 93553], .contexts [
        ⟨79983, true, false, [30338], [15]⟩,
        ⟨1, false, false, [30338, 93553], []⟩,
        ⟨79957, true, false, [], [93553]⟩
      ]⟩,
    ⟨[93553, 7], [16495, 83673], .contexts [
        ⟨79976, false, false, [], []⟩,
        ⟨79977, false, false, [], []⟩,
        ⟨79974, false, false, [], []⟩,
        ⟨79975, false, false, [], []⟩,
        ⟨79975, false, false, [], []⟩
      ]⟩,
    ⟨[30343], [16495, 23731], .source 15236⟩,
    ⟨[89197, 13], [89197, 13], .contexts []⟩,
    ⟨[30345], [30342], .source 15237⟩,
    ⟨[30342], [30342], .contexts []⟩,
    ⟨[89197, 13], [30345, 93553], .contexts [
        ⟨79987, false, false, [], []⟩,
        ⟨79986, false, false, [30342], [89197, 13]⟩,
        ⟨54726, true, false, [30342, 16495], [13]⟩,
        ⟨22579, true, false, [30342, 16495], [7, 13]⟩,
        ⟨79985, true, false, [30342], [13, 7, 13]⟩,
        ⟨15654, false, false, [30342, 93553], []⟩,
        ⟨79967, false, false, [30342], []⟩,
        ⟨79989, true, false, [], [93553]⟩,
        ⟨79989, true, false, [], [93553]⟩,
        ⟨79988, true, false, [], [93553]⟩
      ]⟩,
    ⟨[93553, 13], [30343, 89197], .contexts [
        ⟨79990, true, false, [30344], [13]⟩,
        ⟨59, false, false, [30344, 89197], []⟩,
        ⟨79988, false, true, [], [89197]⟩
      ]⟩,
    ⟨[93555], [93553, 9], .source 46842⟩,
    ⟨[93553, 9], [93555], .contexts [
        ⟨79992, true, false, [], []⟩
      ]⟩,
    ⟨[93555, 9], [93553], .contexts [
        ⟨79993, true, false, [], [9]⟩,
        ⟨46, false, false, [93553], []⟩,
        ⟨79962, false, false, [], []⟩
      ]⟩,
    ⟨[93555], [93555], .contexts []⟩,
    ⟨[93555], [93555], .contexts []⟩,
    ⟨[93553, 9], [93555], .contexts [
        ⟨79993, false, false, [], []⟩,
        ⟨79995, false, false, [], []⟩,
        ⟨79996, false, false, [], []⟩,
        ⟨79996, false, false, [], []⟩
      ]⟩,
    ⟨[1063, 93555], [1063, 93555], .contexts []⟩,
    ⟨[93555], [93555], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1250. -/
def y322TCIndexRaw1250 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93555, 1], [1063, 93555], .contexts [
        ⟨79997, true, false, [], [1]⟩,
        ⟨691, false, false, [93553], []⟩,
        ⟨694, false, false, [93553], []⟩,
        ⟨79960, false, false, [], [9, 1, 9]⟩,
        ⟨79927, false, false, [], [9, 1, 9]⟩,
        ⟨79928, false, false, [], [9, 1, 9]⟩,
        ⟨79928, false, false, [], [9, 1, 9]⟩,
        ⟨79947, false, false, [], [1, 9]⟩,
        ⟨79945, false, false, [], [1, 9]⟩,
        ⟨79946, false, false, [], [1, 9]⟩,
        ⟨79946, false, false, [], [1, 9]⟩,
        ⟨79959, false, false, [1063], [9]⟩,
        ⟨79993, false, false, [1063], []⟩,
        ⟨79998, false, false, [], []⟩,
        ⟨79999, false, false, [1063], []⟩
      ]⟩,
    ⟨[93555, 1], [1063, 93555], .contexts [
        ⟨80000, false, false, [], []⟩,
        ⟨3424, true, false, [], [93555]⟩
      ]⟩,
    ⟨[323, 93555], [323, 93555], .contexts []⟩,
    ⟨[30333, 93555], [30333, 93555], .contexts []⟩,
    ⟨[16495, 86111], [16495, 86111], .contexts []⟩,
    ⟨[16495, 86111], [16495, 86111], .contexts []⟩,
    ⟨[93555, 7], [93555, 7], .contexts []⟩,
    ⟨[93555, 7], [16495, 86111], .contexts [
        ⟨80006, false, false, [], []⟩,
        ⟨79997, true, false, [], [7]⟩,
        ⟨1084, false, false, [93553], []⟩,
        ⟨1085, false, false, [93553], []⟩,
        ⟨79985, false, false, [], [9]⟩,
        ⟨35402, false, false, [16495], []⟩,
        ⟨80004, false, false, [], []⟩,
        ⟨80005, false, false, [], []⟩,
        ⟨35408, false, false, [16495], []⟩,
        ⟨79942, true, false, [], [86111]⟩
      ]⟩,
    ⟨[86111, 7], [16493, 93555], .contexts [
        ⟨80007, true, false, [16494], [7]⟩,
        ⟨38, false, false, [16494, 93555], []⟩,
        ⟨79944, true, false, [], [93555]⟩
      ]⟩,
    ⟨[30343, 89197], [30343, 89197], .contexts []⟩,
    ⟨[30343, 89197], [30343, 89197], .contexts []⟩,
    ⟨[30343, 89195], [30343, 89195], .contexts []⟩,
    ⟨[93555, 13], [30343, 89195], .contexts [
        ⟨79997, true, false, [], [13]⟩,
        ⟨201, false, false, [93553], []⟩,
        ⟨202, false, false, [93553], []⟩,
        ⟨79991, false, false, [], [9]⟩,
        ⟨80009, false, false, [], [9]⟩,
        ⟨80010, false, false, [], [9]⟩,
        ⟨80010, false, false, [], [9]⟩,
        ⟨54507, false, false, [30343], []⟩,
        ⟨80011, false, false, [], []⟩,
        ⟨54737, false, false, [30343], []⟩,
        ⟨13, true, false, [], [30343, 89195]⟩
      ]⟩,
    ⟨[89195, 13], [30345, 93555], .contexts [
        ⟨80012, true, false, [30342], [13]⟩,
        ⟨59, false, false, [30342, 93555], []⟩,
        ⟨79988, true, false, [], [93555]⟩
      ]⟩,
    ⟨[30339, 86695], [30339, 86695], .contexts []⟩,
    ⟨[93555, 15], [30339, 86695], .contexts [
        ⟨79997, true, false, [], [15]⟩,
        ⟨205, false, false, [93553], []⟩,
        ⟨206, false, false, [93553], []⟩,
        ⟨79982, false, false, [], [9]⟩,
        ⟨79983, false, false, [], [9]⟩,
        ⟨79980, false, false, [], [9]⟩,
        ⟨79981, false, false, [], [9]⟩,
        ⟨79981, false, false, [], [9]⟩,
        ⟨38541, false, false, [30339], []⟩,
        ⟨80014, false, false, [], []⟩,
        ⟨38549, false, false, [30339], []⟩,
        ⟨79955, true, false, [], [86695]⟩
      ]⟩,
    ⟨[30347], [16495, 759], .source 15238⟩,
    ⟨[30349], [30347, 16493], .source 15239⟩,
    ⟨[30351], [30348], .source 15240⟩,
    ⟨[30348], [30348], .contexts []⟩,
    ⟨[93555, 11], [30351, 93555], .contexts [
        ⟨80017, false, false, [30348], [93555, 11]⟩,
        ⟨80008, true, false, [30348, 30347], [11]⟩,
        ⟨80016, false, false, [30348], [86111, 7, 11]⟩,
        ⟨35421, true, false, [30348, 16495], [7, 11]⟩,
        ⟨80005, true, false, [30348], [11, 7, 11]⟩,
        ⟨80005, true, false, [30348], [11, 7, 11]⟩,
        ⟨80004, true, false, [30348], [11, 7, 11]⟩,
        ⟨80007, true, false, [30348], [11, 7, 11]⟩,
        ⟨80006, true, false, [30348], [11, 7, 11]⟩,
        ⟨2806, false, false, [30348, 93555], []⟩,
        ⟨79999, false, false, [30348], []⟩,
        ⟨80019, true, false, [], [93555]⟩,
        ⟨80019, true, false, [], [93555]⟩,
        ⟨80018, true, false, [], [93555]⟩
      ]⟩,
    ⟨[93557], [89195, 15], .source 46843⟩,
    ⟨[89195, 15], [93557], .contexts [
        ⟨80021, true, false, [], []⟩
      ]⟩,
    ⟨[93557, 15], [89195], .contexts [
        ⟨80022, true, false, [], [15]⟩,
        ⟨1, false, false, [89195], []⟩,
        ⟨54506, false, false, [], []⟩
      ]⟩,
    ⟨[89195, 15], [93557], .contexts [
        ⟨80022, false, false, [], []⟩
      ]⟩,
    ⟨[93557], [93557], .contexts []⟩,
    ⟨[93557], [93557], .contexts []⟩,
    ⟨[89195, 15], [93557], .contexts [
        ⟨80024, false, false, [], []⟩,
        ⟨80025, false, false, [], []⟩,
        ⟨80026, false, false, [], []⟩,
        ⟨80026, false, false, [], []⟩
      ]⟩,
    ⟨[23729, 86113], [23729, 86113], .contexts []⟩,
    ⟨[23729, 86113], [23729, 86113], .contexts []⟩,
    ⟨[30353], [23729, 20859], .source 15241⟩,
    ⟨[93557, 7], [93557, 7], .contexts []⟩,
    ⟨[30353], [30353], .contexts [
        ⟨13, false, false, [], [30353]⟩
      ]⟩,
    ⟨[93557, 7], [30353, 84241], .contexts [
        ⟨80031, false, false, [], []⟩,
        ⟨80027, true, false, [], [7]⟩,
        ⟨37, false, false, [89195], []⟩,
        ⟨40, false, false, [89195], []⟩,
        ⟨54753, false, false, [], [15]⟩,
        ⟨54755, false, false, [], [15]⟩,
        ⟨80028, false, false, [], [15]⟩,
        ⟨80029, false, false, [], [15]⟩,
        ⟨80029, false, false, [], [15]⟩,
        ⟨35442, false, false, [23729], []⟩,
        ⟨42863, false, false, [23729], []⟩,
        ⟨80030, true, false, [], [84241]⟩,
        ⟨25712, false, false, [30353], []⟩,
        ⟨80032, true, false, [], [84241]⟩
      ]⟩,
    ⟨[30355], [30352], .source 15242⟩,
    ⟨[30345, 93555], [30345, 93555], .contexts []⟩,
    ⟨[30345, 93555], [30345, 93555], .contexts []⟩,
    ⟨[30357], [30345, 30339], .source 15243⟩,
    ⟨[30359], [30357, 21605], .source 15244⟩,
    ⟨[93557, 13], [30359, 86701], .contexts [
        ⟨80027, true, false, [], [13]⟩,
        ⟨259, false, false, [89195], []⟩,
        ⟨262, false, false, [89195], []⟩,
        ⟨80013, false, false, [], [15, 13, 15]⟩,
        ⟨80035, false, false, [], [15, 13, 15]⟩,
        ⟨80036, false, false, [], [15, 13, 15]⟩,
        ⟨80036, false, false, [], [15, 13, 15]⟩,
        ⟨80015, false, false, [30345], [13, 15]⟩,
        ⟨80037, true, false, [], [86695, 13, 15]⟩,
        ⟨45611, false, false, [30357], [15]⟩,
        ⟨80038, true, false, [], [86699, 15]⟩,
        ⟨38592, false, false, [30359], []⟩,
        ⟨38601, false, false, [30359], []⟩
      ]⟩,
    ⟨[30361], [30358], .source 15245⟩,
    ⟨[93559], [93557, 1], .source 46844⟩,
    ⟨[93557, 1], [93559], .contexts [
        ⟨80041, true, false, [], []⟩
      ]⟩,
    ⟨[93559, 1], [93557], .contexts [
        ⟨80042, true, false, [], [1]⟩,
        ⟨8, false, false, [93557], []⟩,
        ⟨80026, false, false, [], []⟩
      ]⟩,
    ⟨[93559], [93559], .contexts []⟩,
    ⟨[93557, 1], [93559], .contexts [
        ⟨80042, false, false, [], []⟩,
        ⟨80044, false, false, [], []⟩,
        ⟨80044, false, false, [], []⟩
      ]⟩,
    ⟨[30353, 84241], [30353, 84241], .contexts []⟩,
    ⟨[30353, 84243], [30353, 84243], .contexts []⟩,
    ⟨[30353, 84243], [30353, 84243], .contexts []⟩,
    ⟨[93559, 7], [93559, 7], .contexts []⟩,
    ⟨[93559, 7], [30353, 84243], .contexts [
        ⟨80049, false, false, [], []⟩,
        ⟨80045, true, false, [], [7]⟩,
        ⟨104, false, false, [93557], []⟩,
        ⟨105, false, false, [93557], []⟩,
        ⟨80031, false, false, [], [1]⟩,
        ⟨80033, false, false, [], [1]⟩,
        ⟨80046, false, false, [], [1]⟩,
        ⟨80046, false, false, [], [1]⟩,
        ⟨25714, false, false, [30353], []⟩,
        ⟨80047, false, false, [], []⟩,
        ⟨80048, false, false, [], []⟩,
        ⟨27829, false, false, [30353], []⟩,
        ⟨80032, true, false, [], [84243]⟩
      ]⟩,
    ⟨[93559, 15], [23715, 89191], .contexts [
        ⟨80045, true, false, [], [15]⟩,
        ⟨121, false, false, [93557], []⟩,
        ⟨122, false, false, [93557], []⟩,
        ⟨80023, false, false, [], [1]⟩,
        ⟨54536, false, false, [], [1]⟩,
        ⟨54506, false, false, [], [1]⟩,
        ⟨54506, false, false, [], [1]⟩,
        ⟨54538, false, false, [], []⟩,
        ⟨54775, false, false, [], []⟩,
        ⟨54760, false, false, [], []⟩,
        ⟨54760, false, false, [], []⟩,
        ⟨54777, false, false, [23715], []⟩,
        ⟨54765, true, false, [], [89191]⟩,
        ⟨54764, true, false, [], [89191]⟩,
        ⟨13, true, false, [], [23715, 89191]⟩
      ]⟩,
    ⟨[30363], [30353, 20857], .source 15246⟩,
    ⟨[30365], [30363, 28379], .source 15247⟩,
    ⟨[30367], [30364], .source 15248⟩,
    ⟨[30364], [30364], .contexts []⟩,
    ⟨[89185, 3], [30367, 93559], .contexts [
        ⟨80053, false, false, [30364], [89185, 3]⟩,
        ⟨73742, true, false, [30364, 30363], [3]⟩,
        ⟨80052, false, false, [30364], [86119, 7, 3]⟩,
        ⟨42865, true, false, [30364, 30353], [7, 3]⟩,
        ⟨80048, true, false, [30364], [3, 7, 3]⟩,
        ⟨80048, true, false, [30364], [3, 7, 3]⟩,
        ⟨80047, true, false, [30364], [3, 7, 3]⟩,
        ⟨80050, true, false, [30364], [3, 7, 3]⟩,
        ⟨80049, true, false, [30364], [3, 7, 3]⟩,
        ⟨40656, false, false, [30364, 93559], []⟩,
        ⟨80055, true, false, [], [93559]⟩,
        ⟨80055, true, false, [], [93559]⟩,
        ⟨80054, true, false, [], [93559]⟩
      ]⟩,
    ⟨[93561], [89185, 5], .source 46845⟩,
    ⟨[89185, 5], [93561], .contexts [
        ⟨80057, true, false, [], []⟩
      ]⟩,
    ⟨[93561], [93561], .contexts []⟩,
    ⟨[93561], [93561], .contexts []⟩,
    ⟨[23741, 93561], [23741, 93561], .contexts []⟩,
    ⟨[23741, 93561], [23741, 93561], .contexts []⟩,
    ⟨[93563], [93561, 9], .source 46846⟩]

/-- Exact literal claimed equations and contextual derivations, block 1251. -/
def y322TCIndexRaw1251 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93561, 9], [93563], .contexts [
        ⟨80063, true, false, [], []⟩
      ]⟩,
    ⟨[93563], [93563], .contexts []⟩,
    ⟨[93563], [93563], .contexts []⟩,
    ⟨[93565], [93563, 11], .source 46847⟩,
    ⟨[93563, 11], [93565], .contexts [
        ⟨80067, true, false, [], []⟩
      ]⟩,
    ⟨[93565], [93565], .contexts []⟩,
    ⟨[93565], [93565], .contexts []⟩,
    ⟨[93567], [93565, 1], .source 46848⟩,
    ⟨[93565, 1], [93567], .contexts [
        ⟨80071, true, false, [], []⟩
      ]⟩,
    ⟨[93567], [93567], .contexts []⟩,
    ⟨[93567], [93567], .contexts []⟩,
    ⟨[93569], [93567, 13], .source 46849⟩,
    ⟨[93567, 13], [93569], .contexts [
        ⟨80075, true, false, [], []⟩
      ]⟩,
    ⟨[93569], [93569], .contexts []⟩,
    ⟨[93569], [93569], .contexts []⟩,
    ⟨[93571], [93569, 15], .source 46850⟩,
    ⟨[93569, 15], [93571], .contexts [
        ⟨80079, true, false, [], []⟩
      ]⟩,
    ⟨[93571], [93571], .contexts []⟩,
    ⟨[93571], [93571], .contexts []⟩,
    ⟨[93573], [93571, 1], .source 46851⟩,
    ⟨[93571, 1], [93573], .contexts [
        ⟨80083, true, false, [], []⟩
      ]⟩,
    ⟨[93573], [93573], .contexts []⟩,
    ⟨[93573], [93573], .contexts []⟩,
    ⟨[93575], [93573, 3], .source 46852⟩,
    ⟨[93573, 3], [93575], .contexts [
        ⟨80087, true, false, [], []⟩
      ]⟩,
    ⟨[93575], [93575], .contexts []⟩,
    ⟨[93575], [93575], .contexts []⟩,
    ⟨[93577], [93575, 5], .source 46853⟩,
    ⟨[93575, 5], [93577], .contexts [
        ⟨80091, true, false, [], []⟩
      ]⟩,
    ⟨[93577, 5], [93575], .contexts [
        ⟨80092, true, false, [], [5]⟩,
        ⟨28, false, false, [93575], []⟩,
        ⟨80090, false, false, [], []⟩
      ]⟩,
    ⟨[93579], [93577, 1], .source 46854⟩,
    ⟨[93577, 1], [93579], .contexts [
        ⟨80094, true, false, [], []⟩
      ]⟩,
    ⟨[93577], [93577], .contexts []⟩,
    ⟨[93581], [93579, 9], .source 46855⟩,
    ⟨[93579, 9], [93581], .contexts [
        ⟨80097, true, false, [], []⟩
      ]⟩,
    ⟨[93579], [93579], .contexts []⟩,
    ⟨[93581, 9], [93579], .contexts [
        ⟨80098, true, false, [], [9]⟩,
        ⟨46, false, false, [93579], []⟩,
        ⟨80099, false, false, [], []⟩
      ]⟩,
    ⟨[93583], [93581, 11], .source 46856⟩,
    ⟨[93581, 11], [93583], .contexts [
        ⟨80101, true, false, [], []⟩
      ]⟩,
    ⟨[93581], [93581], .contexts []⟩,
    ⟨[93583, 11], [93581], .contexts [
        ⟨80102, true, false, [], [11]⟩,
        ⟨53, false, false, [93581], []⟩,
        ⟨80103, false, false, [], []⟩
      ]⟩,
    ⟨[93585], [93583, 1], .source 46857⟩,
    ⟨[93583], [93583], .contexts []⟩,
    ⟨[93585, 1], [93583], .contexts [
        ⟨80105, false, false, [], [1]⟩,
        ⟨8, false, false, [93583], []⟩,
        ⟨80106, false, false, [], []⟩
      ]⟩,
    ⟨[93587], [93585, 13], .source 46858⟩,
    ⟨[93585], [93585], .contexts []⟩,
    ⟨[93587, 13], [93585], .contexts [
        ⟨80108, false, false, [], [13]⟩,
        ⟨59, false, false, [93585], []⟩,
        ⟨80109, false, false, [], []⟩
      ]⟩,
    ⟨[93589], [93587, 15], .source 46859⟩,
    ⟨[93587], [93587], .contexts []⟩,
    ⟨[93589, 15], [93587], .contexts [
        ⟨80111, false, false, [], [15]⟩,
        ⟨1, false, false, [93587], []⟩,
        ⟨80112, false, false, [], []⟩
      ]⟩,
    ⟨[93591], [93589, 1], .source 46860⟩,
    ⟨[93589], [93589], .contexts []⟩,
    ⟨[93591, 1], [93589], .contexts [
        ⟨80114, false, false, [], [1]⟩,
        ⟨8, false, false, [93589], []⟩,
        ⟨80115, false, false, [], []⟩
      ]⟩,
    ⟨[93593], [93591, 3], .source 46861⟩,
    ⟨[93591], [93591], .contexts []⟩,
    ⟨[93593, 3], [93591], .contexts [
        ⟨80117, false, false, [], [3]⟩,
        ⟨20, false, false, [93591], []⟩,
        ⟨80118, false, false, [], []⟩
      ]⟩,
    ⟨[93595], [93593, 5], .source 46862⟩,
    ⟨[93593], [93593], .contexts []⟩,
    ⟨[93595, 5], [93593], .contexts [
        ⟨80120, false, false, [], [5]⟩,
        ⟨28, false, false, [93593], []⟩,
        ⟨80121, false, false, [], []⟩
      ]⟩,
    ⟨[93597], [93595, 1], .source 46863⟩,
    ⟨[93595], [93595], .contexts []⟩,
    ⟨[93597, 1], [93595], .contexts [
        ⟨80123, false, false, [], [1]⟩,
        ⟨8, false, false, [93595], []⟩,
        ⟨80124, false, false, [], []⟩
      ]⟩,
    ⟨[93599], [93597, 9], .source 46864⟩,
    ⟨[93597], [93597], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1252. -/
def y322TCIndexRaw1252 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93599, 9], [93597], .contexts [
        ⟨80126, false, false, [], [9]⟩,
        ⟨46, false, false, [93597], []⟩,
        ⟨80127, false, false, [], []⟩
      ]⟩,
    ⟨[93601], [93599, 11], .source 46865⟩,
    ⟨[93599], [93599], .contexts []⟩,
    ⟨[93601, 11], [93599], .contexts [
        ⟨80129, false, false, [], [11]⟩,
        ⟨53, false, false, [93599], []⟩,
        ⟨80130, false, false, [], []⟩
      ]⟩,
    ⟨[93603], [93601, 1], .source 46866⟩,
    ⟨[93601], [93601], .contexts []⟩,
    ⟨[93603, 1], [93601], .contexts [
        ⟨80132, false, false, [], [1]⟩,
        ⟨8, false, false, [93601], []⟩,
        ⟨80133, false, false, [], []⟩
      ]⟩,
    ⟨[93605], [93603, 13], .source 46867⟩,
    ⟨[93603], [93603], .contexts []⟩,
    ⟨[93605, 13], [93603], .contexts [
        ⟨80135, false, false, [], [13]⟩,
        ⟨59, false, false, [93603], []⟩,
        ⟨80136, false, false, [], []⟩
      ]⟩,
    ⟨[93607], [93605, 15], .source 46868⟩,
    ⟨[93605], [93605], .contexts []⟩,
    ⟨[93607, 15], [93605], .contexts [
        ⟨80138, false, false, [], [15]⟩,
        ⟨1, false, false, [93605], []⟩,
        ⟨80139, false, false, [], []⟩
      ]⟩,
    ⟨[93609], [93607, 1], .source 46869⟩,
    ⟨[93607], [93607], .contexts []⟩,
    ⟨[93609, 1], [93607], .contexts [
        ⟨80141, false, false, [], [1]⟩,
        ⟨8, false, false, [93607], []⟩,
        ⟨80142, false, false, [], []⟩
      ]⟩,
    ⟨[93611], [93609, 3], .source 46870⟩,
    ⟨[93609], [93609], .contexts []⟩,
    ⟨[93611, 3], [93609], .contexts [
        ⟨80144, false, false, [], [3]⟩,
        ⟨20, false, false, [93609], []⟩,
        ⟨80145, false, false, [], []⟩
      ]⟩,
    ⟨[93613], [93611, 5], .source 46871⟩,
    ⟨[93611], [93611], .contexts []⟩,
    ⟨[93613, 5], [93611], .contexts [
        ⟨80147, false, false, [], [5]⟩,
        ⟨28, false, false, [93611], []⟩,
        ⟨80148, false, false, [], []⟩
      ]⟩,
    ⟨[93615], [93613, 1], .source 46872⟩,
    ⟨[93613], [93613], .contexts []⟩,
    ⟨[93615, 1], [93613], .contexts [
        ⟨80150, false, false, [], [1]⟩,
        ⟨8, false, false, [93613], []⟩,
        ⟨80151, false, false, [], []⟩
      ]⟩,
    ⟨[93617], [93615, 9], .source 46873⟩,
    ⟨[93615], [93615], .contexts []⟩,
    ⟨[93617, 9], [93615], .contexts [
        ⟨80153, false, false, [], [9]⟩,
        ⟨46, false, false, [93615], []⟩,
        ⟨80154, false, false, [], []⟩
      ]⟩,
    ⟨[93619], [93617, 11], .source 46874⟩,
    ⟨[93617], [93617], .contexts []⟩,
    ⟨[93619, 11], [93617], .contexts [
        ⟨80156, false, false, [], [11]⟩,
        ⟨53, false, false, [93617], []⟩,
        ⟨80157, false, false, [], []⟩
      ]⟩,
    ⟨[93621], [93619, 1], .source 46875⟩,
    ⟨[93619], [93619], .contexts []⟩,
    ⟨[93621, 1], [93619], .contexts [
        ⟨80159, false, false, [], [1]⟩,
        ⟨8, false, false, [93619], []⟩,
        ⟨80160, false, false, [], []⟩
      ]⟩,
    ⟨[93623], [93621, 13], .source 46876⟩,
    ⟨[93621], [93621], .contexts []⟩,
    ⟨[93623, 13], [93621], .contexts [
        ⟨80162, false, false, [], [13]⟩,
        ⟨59, false, false, [93621], []⟩,
        ⟨80163, false, false, [], []⟩
      ]⟩,
    ⟨[93625], [93623, 15], .source 46877⟩,
    ⟨[93623], [93623], .contexts []⟩,
    ⟨[93625, 15], [93623], .contexts [
        ⟨80165, false, false, [], [15]⟩,
        ⟨1, false, false, [93623], []⟩,
        ⟨80166, false, false, [], []⟩
      ]⟩,
    ⟨[93627], [93625, 1], .source 46878⟩,
    ⟨[93625, 1], [93627], .contexts [
        ⟨80168, true, false, [], []⟩
      ]⟩,
    ⟨[93625], [93625], .contexts []⟩,
    ⟨[93627, 1], [93625], .contexts [
        ⟨80169, true, false, [], [1]⟩,
        ⟨8, false, false, [93625], []⟩,
        ⟨80170, false, false, [], []⟩
      ]⟩,
    ⟨[93629], [93627, 3], .source 46879⟩,
    ⟨[93627, 3], [93629], .contexts [
        ⟨80172, true, false, [], []⟩
      ]⟩,
    ⟨[93627], [93627], .contexts []⟩,
    ⟨[93629, 3], [93627], .contexts [
        ⟨80173, true, false, [], [3]⟩,
        ⟨20, false, false, [93627], []⟩,
        ⟨80174, false, false, [], []⟩
      ]⟩,
    ⟨[93631], [93629, 5], .source 46880⟩,
    ⟨[93629, 5], [93631], .contexts [
        ⟨80176, true, false, [], []⟩
      ]⟩,
    ⟨[93629], [93629], .contexts []⟩,
    ⟨[93631, 5], [93629], .contexts [
        ⟨80177, true, false, [], [5]⟩,
        ⟨28, false, false, [93629], []⟩,
        ⟨80178, false, false, [], []⟩
      ]⟩,
    ⟨[93633], [93631, 1], .source 46881⟩,
    ⟨[93631, 1], [93633], .contexts [
        ⟨80180, true, false, [], []⟩
      ]⟩,
    ⟨[93631], [93631], .contexts []⟩,
    ⟨[93633, 1], [93631], .contexts [
        ⟨80181, true, false, [], [1]⟩,
        ⟨8, false, false, [93631], []⟩,
        ⟨80182, false, false, [], []⟩
      ]⟩,
    ⟨[93635], [93633, 9], .source 46882⟩,
    ⟨[93633, 9], [93635], .contexts [
        ⟨80184, true, false, [], []⟩
      ]⟩,
    ⟨[93633], [93633], .contexts []⟩,
    ⟨[93635, 9], [93633], .contexts [
        ⟨80185, true, false, [], [9]⟩,
        ⟨46, false, false, [93633], []⟩,
        ⟨80186, false, false, [], []⟩
      ]⟩,
    ⟨[93637], [93635, 11], .source 46883⟩,
    ⟨[93635, 11], [93637], .contexts [
        ⟨80188, true, false, [], []⟩
      ]⟩,
    ⟨[93635], [93635], .contexts []⟩,
    ⟨[93637, 11], [93635], .contexts [
        ⟨80189, true, false, [], [11]⟩,
        ⟨53, false, false, [93635], []⟩,
        ⟨80190, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1253. -/
def y322TCIndexRaw1253 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93639], [93637, 1], .source 46884⟩,
    ⟨[93637, 1], [93639], .contexts [
        ⟨80192, true, false, [], []⟩
      ]⟩,
    ⟨[93637], [93637], .contexts []⟩,
    ⟨[93639, 1], [93637], .contexts [
        ⟨80193, true, false, [], [1]⟩,
        ⟨8, false, false, [93637], []⟩,
        ⟨80194, false, false, [], []⟩
      ]⟩,
    ⟨[93641], [93639, 13], .source 46885⟩,
    ⟨[93639, 13], [93641], .contexts [
        ⟨80196, true, false, [], []⟩
      ]⟩,
    ⟨[93639], [93639], .contexts []⟩,
    ⟨[93641, 13], [93639], .contexts [
        ⟨80197, true, false, [], [13]⟩,
        ⟨59, false, false, [93639], []⟩,
        ⟨80198, false, false, [], []⟩
      ]⟩,
    ⟨[93643], [93641, 15], .source 46886⟩,
    ⟨[93641, 15], [93643], .contexts [
        ⟨80200, true, false, [], []⟩
      ]⟩,
    ⟨[93641], [93641], .contexts []⟩,
    ⟨[93643, 15], [93641], .contexts [
        ⟨80201, true, false, [], [15]⟩,
        ⟨1, false, false, [93641], []⟩,
        ⟨80202, false, false, [], []⟩
      ]⟩,
    ⟨[93645], [93643, 1], .source 46887⟩,
    ⟨[93643, 1], [93645], .contexts [
        ⟨80204, true, false, [], []⟩
      ]⟩,
    ⟨[93643], [93643], .contexts []⟩,
    ⟨[93645, 1], [93643], .contexts [
        ⟨80205, true, false, [], [1]⟩,
        ⟨8, false, false, [93643], []⟩,
        ⟨80206, false, false, [], []⟩
      ]⟩,
    ⟨[93647], [93645, 3], .source 46888⟩,
    ⟨[93645, 3], [93647], .contexts [
        ⟨80208, true, false, [], []⟩
      ]⟩,
    ⟨[93645], [93645], .contexts []⟩,
    ⟨[93647, 3], [93645], .contexts [
        ⟨80209, true, false, [], [3]⟩,
        ⟨20, false, false, [93645], []⟩,
        ⟨80210, false, false, [], []⟩
      ]⟩,
    ⟨[93649], [93647, 5], .source 46889⟩,
    ⟨[93647, 5], [93649], .contexts [
        ⟨80212, true, false, [], []⟩
      ]⟩,
    ⟨[93647], [93647], .contexts []⟩,
    ⟨[93649, 5], [93647], .contexts [
        ⟨80213, true, false, [], [5]⟩,
        ⟨28, false, false, [93647], []⟩,
        ⟨80214, false, false, [], []⟩
      ]⟩,
    ⟨[93651], [93649, 1], .source 46890⟩,
    ⟨[93649, 1], [93651], .contexts [
        ⟨80216, true, false, [], []⟩
      ]⟩,
    ⟨[93649], [93649], .contexts []⟩,
    ⟨[93651, 1], [93649], .contexts [
        ⟨80217, true, false, [], [1]⟩,
        ⟨8, false, false, [93649], []⟩,
        ⟨80218, false, false, [], []⟩
      ]⟩,
    ⟨[93653], [93651, 9], .source 46891⟩,
    ⟨[93651, 9], [93653], .contexts [
        ⟨80220, true, false, [], []⟩
      ]⟩,
    ⟨[93651], [93651], .contexts []⟩,
    ⟨[93653, 9], [93651], .contexts [
        ⟨80221, true, false, [], [9]⟩,
        ⟨46, false, false, [93651], []⟩,
        ⟨80222, false, false, [], []⟩
      ]⟩,
    ⟨[93655], [93653, 11], .source 46892⟩,
    ⟨[93653], [93653], .contexts []⟩,
    ⟨[93657], [93655, 1], .source 46893⟩,
    ⟨[93655, 1], [93657], .contexts [
        ⟨80226, true, false, [], []⟩
      ]⟩,
    ⟨[93655], [93655], .contexts []⟩,
    ⟨[93657, 1], [93655], .contexts [
        ⟨80227, true, false, [], [1]⟩,
        ⟨8, false, false, [93655], []⟩,
        ⟨80228, false, false, [], []⟩
      ]⟩,
    ⟨[93659], [93657, 13], .source 46894⟩,
    ⟨[93657, 13], [93659], .contexts [
        ⟨80230, true, false, [], []⟩
      ]⟩,
    ⟨[93657], [93657], .contexts []⟩,
    ⟨[93659, 13], [93657], .contexts [
        ⟨80231, true, false, [], [13]⟩,
        ⟨59, false, false, [93657], []⟩,
        ⟨80232, false, false, [], []⟩
      ]⟩,
    ⟨[93661], [93659, 15], .source 46895⟩,
    ⟨[93659, 15], [93661], .contexts [
        ⟨80234, true, false, [], []⟩
      ]⟩,
    ⟨[93659], [93659], .contexts []⟩,
    ⟨[93661, 15], [93659], .contexts [
        ⟨80235, true, false, [], [15]⟩,
        ⟨1, false, false, [93659], []⟩,
        ⟨80236, false, false, [], []⟩
      ]⟩,
    ⟨[93663], [93661, 1], .source 46896⟩,
    ⟨[93661], [93661], .contexts []⟩,
    ⟨[93663, 1], [93661], .contexts [
        ⟨80238, false, false, [], [1]⟩,
        ⟨8, false, false, [93661], []⟩,
        ⟨80239, false, false, [], []⟩
      ]⟩,
    ⟨[93665], [93663, 3], .source 46897⟩,
    ⟨[93663, 3], [93665], .contexts [
        ⟨80241, true, false, [], []⟩
      ]⟩,
    ⟨[93663], [93663], .contexts []⟩,
    ⟨[93665, 3], [93663], .contexts [
        ⟨80242, true, false, [], [3]⟩,
        ⟨20, false, false, [93663], []⟩,
        ⟨80243, false, false, [], []⟩
      ]⟩,
    ⟨[93667], [93665, 5], .source 46898⟩,
    ⟨[93665, 5], [93667], .contexts [
        ⟨80245, true, false, [], []⟩
      ]⟩,
    ⟨[93665], [93665], .contexts []⟩,
    ⟨[93667, 5], [93665], .contexts [
        ⟨80246, true, false, [], [5]⟩,
        ⟨28, false, false, [93665], []⟩,
        ⟨80247, false, false, [], []⟩
      ]⟩,
    ⟨[93669], [93667, 1], .source 46899⟩,
    ⟨[93667], [93667], .contexts []⟩,
    ⟨[93669, 1], [93667], .contexts [
        ⟨80249, false, false, [], [1]⟩,
        ⟨8, false, false, [93667], []⟩,
        ⟨80250, false, false, [], []⟩
      ]⟩,
    ⟨[93671], [93669, 9], .source 46900⟩,
    ⟨[93669, 9], [93671], .contexts [
        ⟨80252, true, false, [], []⟩
      ]⟩,
    ⟨[93669], [93669], .contexts []⟩,
    ⟨[93671, 9], [93669], .contexts [
        ⟨80253, true, false, [], [9]⟩,
        ⟨46, false, false, [93669], []⟩,
        ⟨80254, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1254. -/
def y322TCIndexRaw1254 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93673], [93671, 11], .source 46901⟩,
    ⟨[93671, 11], [93673], .contexts [
        ⟨80256, true, false, [], []⟩
      ]⟩,
    ⟨[93671], [93671], .contexts []⟩,
    ⟨[93673, 11], [93671], .contexts [
        ⟨80257, true, false, [], [11]⟩,
        ⟨53, false, false, [93671], []⟩,
        ⟨80258, false, false, [], []⟩
      ]⟩,
    ⟨[93675], [93673, 1], .source 46902⟩,
    ⟨[93673, 1], [93675], .contexts [
        ⟨80260, true, false, [], []⟩
      ]⟩,
    ⟨[93673], [93673], .contexts []⟩,
    ⟨[93673, 1], [93675], .contexts [
        ⟨80261, false, false, [], []⟩
      ]⟩,
    ⟨[93675], [93675], .contexts []⟩,
    ⟨[93671], [93671], .contexts []⟩,
    ⟨[93673, 11], [93671], .contexts [
        ⟨80259, false, false, [], []⟩,
        ⟨80265, false, false, [], []⟩,
        ⟨80258, false, false, [], []⟩,
        ⟨80258, false, false, [], []⟩
      ]⟩,
    ⟨[93671, 9], [93669], .contexts [
        ⟨80255, false, false, [], []⟩
      ]⟩,
    ⟨[93669], [93669], .contexts []⟩,
    ⟨[93669, 1], [93667], .contexts [
        ⟨80251, false, false, [], []⟩
      ]⟩,
    ⟨[93667], [93667], .contexts []⟩,
    ⟨[93667, 5], [93665], .contexts [
        ⟨80248, false, false, [], []⟩
      ]⟩,
    ⟨[93665], [93665], .contexts []⟩,
    ⟨[93665, 3], [93663], .contexts [
        ⟨80244, false, false, [], []⟩
      ]⟩,
    ⟨[93663], [93663], .contexts []⟩,
    ⟨[93661], [93661], .contexts []⟩,
    ⟨[93673, 11, 9, 1, 5, 3, 1], [93661], .contexts [
        ⟨80266, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨80267, false, false, [], [1, 5, 3, 1]⟩,
        ⟨80268, false, false, [], [1, 5, 3, 1]⟩,
        ⟨80254, false, false, [], [1, 5, 3, 1]⟩,
        ⟨80254, false, false, [], [1, 5, 3, 1]⟩,
        ⟨80269, false, false, [], [5, 3, 1]⟩,
        ⟨80270, false, false, [], [5, 3, 1]⟩,
        ⟨80250, false, false, [], [5, 3, 1]⟩,
        ⟨80250, false, false, [], [5, 3, 1]⟩,
        ⟨80271, false, false, [], [3, 1]⟩,
        ⟨80272, false, false, [], [3, 1]⟩,
        ⟨80247, false, false, [], [3, 1]⟩,
        ⟨80247, false, false, [], [3, 1]⟩,
        ⟨80273, false, false, [], [1]⟩,
        ⟨80274, false, false, [], [1]⟩,
        ⟨80243, false, false, [], [1]⟩,
        ⟨80243, false, false, [], [1]⟩,
        ⟨80240, false, false, [], []⟩,
        ⟨80275, false, false, [], []⟩,
        ⟨80239, false, false, [], []⟩,
        ⟨80239, false, false, [], []⟩
      ]⟩,
    ⟨[93659], [93659], .contexts []⟩,
    ⟨[93657], [93657], .contexts []⟩,
    ⟨[93657, 1], [93655], .contexts [
        ⟨80229, false, false, [], []⟩
      ]⟩,
    ⟨[93655], [93655], .contexts []⟩,
    ⟨[93655, 11], [93653], .contexts [
        ⟨80224, false, false, [], [11]⟩,
        ⟨53, false, false, [93653], []⟩,
        ⟨80225, false, false, [], []⟩
      ]⟩,
    ⟨[93653], [93653], .contexts []⟩,
    ⟨[93651], [93651], .contexts []⟩,
    ⟨[93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9], [93651], .contexts [
        ⟨80276, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨80237, false, false, [], [13, 1, 11, 9]⟩,
        ⟨80277, false, false, [], [13, 1, 11, 9]⟩,
        ⟨80236, false, false, [], [13, 1, 11, 9]⟩,
        ⟨80236, false, false, [], [13, 1, 11, 9]⟩,
        ⟨80233, false, false, [], [1, 11, 9]⟩,
        ⟨80278, false, false, [], [1, 11, 9]⟩,
        ⟨80232, false, false, [], [1, 11, 9]⟩,
        ⟨80232, false, false, [], [1, 11, 9]⟩,
        ⟨80279, false, false, [], [11, 9]⟩,
        ⟨80280, false, false, [], [11, 9]⟩,
        ⟨80228, false, false, [], [11, 9]⟩,
        ⟨80228, false, false, [], [11, 9]⟩,
        ⟨80281, false, false, [], [9]⟩,
        ⟨80282, false, false, [], [9]⟩,
        ⟨80225, false, false, [], [9]⟩,
        ⟨80225, false, false, [], [9]⟩,
        ⟨80223, false, false, [], []⟩,
        ⟨80283, false, false, [], []⟩,
        ⟨80222, false, false, [], []⟩,
        ⟨80222, false, false, [], []⟩
      ]⟩,
    ⟨[93651, 1], [93649], .contexts [
        ⟨80219, false, false, [], []⟩
      ]⟩,
    ⟨[93649], [93649], .contexts []⟩,
    ⟨[93649, 5], [93647], .contexts [
        ⟨80215, false, false, [], []⟩
      ]⟩,
    ⟨[93647], [93647], .contexts []⟩,
    ⟨[93647, 3], [93645], .contexts [
        ⟨80211, false, false, [], []⟩
      ]⟩,
    ⟨[93645], [93645], .contexts []⟩,
    ⟨[93643], [93643], .contexts []⟩,
    ⟨[
      93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15
    ], [93641], .contexts [
        ⟨80284, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨80285, false, false, [], [5, 3, 1, 15]⟩,
        ⟨80286, false, false, [], [5, 3, 1, 15]⟩,
        ⟨80218, false, false, [], [5, 3, 1, 15]⟩,
        ⟨80218, false, false, [], [5, 3, 1, 15]⟩,
        ⟨80287, false, false, [], [3, 1, 15]⟩,
        ⟨80288, false, false, [], [3, 1, 15]⟩,
        ⟨80214, false, false, [], [3, 1, 15]⟩,
        ⟨80214, false, false, [], [3, 1, 15]⟩,
        ⟨80289, false, false, [], [1, 15]⟩,
        ⟨80290, false, false, [], [1, 15]⟩,
        ⟨80210, false, false, [], [1, 15]⟩,
        ⟨80210, false, false, [], [1, 15]⟩,
        ⟨80207, false, false, [], [15]⟩,
        ⟨80291, false, false, [], [15]⟩,
        ⟨80206, false, false, [], [15]⟩,
        ⟨80206, false, false, [], [15]⟩,
        ⟨80203, false, false, [], []⟩,
        ⟨80202, false, false, [], []⟩,
        ⟨80202, false, false, [], []⟩
      ]⟩,
    ⟨[93639], [93639], .contexts []⟩,
    ⟨[93635], [93635], .contexts []⟩,
    ⟨[93631], [93631], .contexts []⟩,
    ⟨[
      93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [93631], .contexts [
        ⟨80292, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨80199, false, false, [], [1, 11, 9, 1]⟩,
        ⟨80293, false, false, [], [1, 11, 9, 1]⟩,
        ⟨80198, false, false, [], [1, 11, 9, 1]⟩,
        ⟨80198, false, false, [], [1, 11, 9, 1]⟩,
        ⟨80195, false, false, [], [11, 9, 1]⟩,
        ⟨80194, false, false, [], [11, 9, 1]⟩,
        ⟨80194, false, false, [], [11, 9, 1]⟩,
        ⟨80191, false, false, [], [9, 1]⟩,
        ⟨80294, false, false, [], [9, 1]⟩,
        ⟨80190, false, false, [], [9, 1]⟩,
        ⟨80190, false, false, [], [9, 1]⟩,
        ⟨80187, false, false, [], [1]⟩,
        ⟨80186, false, false, [], [1]⟩,
        ⟨80186, false, false, [], [1]⟩,
        ⟨80183, false, false, [], []⟩,
        ⟨80295, false, false, [], []⟩,
        ⟨80182, false, false, [], []⟩,
        ⟨80182, false, false, [], []⟩
      ]⟩,
    ⟨[93631, 5], [93629], .contexts [
        ⟨80179, false, false, [], []⟩
      ]⟩,
    ⟨[93629], [93629], .contexts []⟩,
    ⟨[93629, 3], [93627], .contexts [
        ⟨80175, false, false, [], []⟩
      ]⟩,
    ⟨[93627], [93627], .contexts []⟩,
    ⟨[93625], [93625], .contexts []⟩,
    ⟨[93621], [93621], .contexts []⟩,
    ⟨[
      93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13
    ], [93621], .contexts [
        ⟨80296, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨80297, false, false, [], [3, 1, 15, 13]⟩,
        ⟨80298, false, false, [], [3, 1, 15, 13]⟩,
        ⟨80178, false, false, [], [3, 1, 15, 13]⟩,
        ⟨80178, false, false, [], [3, 1, 15, 13]⟩,
        ⟨80299, false, false, [], [1, 15, 13]⟩,
        ⟨80300, false, false, [], [1, 15, 13]⟩,
        ⟨80174, false, false, [], [1, 15, 13]⟩,
        ⟨80174, false, false, [], [1, 15, 13]⟩,
        ⟨80171, false, false, [], [15, 13]⟩,
        ⟨80301, false, false, [], [15, 13]⟩,
        ⟨80170, false, false, [], [15, 13]⟩,
        ⟨80170, false, false, [], [15, 13]⟩,
        ⟨80167, false, false, [], [13]⟩,
        ⟨80166, false, false, [], [13]⟩,
        ⟨80166, false, false, [], [13]⟩,
        ⟨80164, false, false, [], []⟩,
        ⟨80302, false, false, [], []⟩,
        ⟨80163, false, false, [], []⟩,
        ⟨80163, false, false, [], []⟩
      ]⟩,
    ⟨[93619], [93619], .contexts []⟩,
    ⟨[93617], [93617], .contexts []⟩,
    ⟨[93615], [93615], .contexts []⟩,
    ⟨[93613], [93613], .contexts []⟩,
    ⟨[93611], [93611], .contexts []⟩,
    ⟨[
      93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5
    ], [93611], .contexts [
        ⟨80303, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨80161, false, false, [], [11, 9, 1, 5]⟩,
        ⟨80304, false, false, [], [11, 9, 1, 5]⟩,
        ⟨80160, false, false, [], [11, 9, 1, 5]⟩,
        ⟨80160, false, false, [], [11, 9, 1, 5]⟩,
        ⟨80158, false, false, [], [9, 1, 5]⟩,
        ⟨80305, false, false, [], [9, 1, 5]⟩,
        ⟨80157, false, false, [], [9, 1, 5]⟩,
        ⟨80157, false, false, [], [9, 1, 5]⟩,
        ⟨80155, false, false, [], [1, 5]⟩,
        ⟨80306, false, false, [], [1, 5]⟩,
        ⟨80154, false, false, [], [1, 5]⟩,
        ⟨80154, false, false, [], [1, 5]⟩,
        ⟨80152, false, false, [], [5]⟩,
        ⟨80307, false, false, [], [5]⟩,
        ⟨80151, false, false, [], [5]⟩,
        ⟨80151, false, false, [], [5]⟩,
        ⟨80149, false, false, [], []⟩,
        ⟨80308, false, false, [], []⟩,
        ⟨80148, false, false, [], []⟩,
        ⟨80148, false, false, [], []⟩
      ]⟩,
    ⟨[93609], [93609], .contexts []⟩,
    ⟨[93607], [93607], .contexts []⟩,
    ⟨[93605], [93605], .contexts []⟩,
    ⟨[93603], [93603], .contexts []⟩,
    ⟨[93601], [93601], .contexts []⟩,
    ⟨[
      93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1
    ], [93601], .contexts [
        ⟨80309, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨80146, false, false, [], [1, 15, 13, 1]⟩,
        ⟨80310, false, false, [], [1, 15, 13, 1]⟩,
        ⟨80145, false, false, [], [1, 15, 13, 1]⟩,
        ⟨80145, false, false, [], [1, 15, 13, 1]⟩,
        ⟨80143, false, false, [], [15, 13, 1]⟩,
        ⟨80311, false, false, [], [15, 13, 1]⟩,
        ⟨80142, false, false, [], [15, 13, 1]⟩,
        ⟨80142, false, false, [], [15, 13, 1]⟩,
        ⟨80140, false, false, [], [13, 1]⟩,
        ⟨80312, false, false, [], [13, 1]⟩,
        ⟨80139, false, false, [], [13, 1]⟩,
        ⟨80139, false, false, [], [13, 1]⟩,
        ⟨80137, false, false, [], [1]⟩,
        ⟨80313, false, false, [], [1]⟩,
        ⟨80136, false, false, [], [1]⟩,
        ⟨80136, false, false, [], [1]⟩,
        ⟨80134, false, false, [], []⟩,
        ⟨80314, false, false, [], []⟩,
        ⟨80133, false, false, [], []⟩,
        ⟨80133, false, false, [], []⟩
      ]⟩,
    ⟨[93599], [93599], .contexts []⟩,
    ⟨[93597], [93597], .contexts []⟩,
    ⟨[93595], [93595], .contexts []⟩,
    ⟨[93593], [93593], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1255. -/
def y322TCIndexRaw1255 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93591], [93591], .contexts []⟩,
    ⟨[
      93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3
    ], [93591], .contexts [
        ⟨80315, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨80131, false, false, [], [9, 1, 5, 3]⟩,
        ⟨80316, false, false, [], [9, 1, 5, 3]⟩,
        ⟨80130, false, false, [], [9, 1, 5, 3]⟩,
        ⟨80130, false, false, [], [9, 1, 5, 3]⟩,
        ⟨80128, false, false, [], [1, 5, 3]⟩,
        ⟨80317, false, false, [], [1, 5, 3]⟩,
        ⟨80127, false, false, [], [1, 5, 3]⟩,
        ⟨80127, false, false, [], [1, 5, 3]⟩,
        ⟨80125, false, false, [], [5, 3]⟩,
        ⟨80318, false, false, [], [5, 3]⟩,
        ⟨80124, false, false, [], [5, 3]⟩,
        ⟨80124, false, false, [], [5, 3]⟩,
        ⟨80122, false, false, [], [3]⟩,
        ⟨80319, false, false, [], [3]⟩,
        ⟨80121, false, false, [], [3]⟩,
        ⟨80121, false, false, [], [3]⟩,
        ⟨80119, false, false, [], []⟩,
        ⟨80320, false, false, [], []⟩,
        ⟨80118, false, false, [], []⟩,
        ⟨80118, false, false, [], []⟩
      ]⟩,
    ⟨[93589], [93589], .contexts []⟩,
    ⟨[93587], [93587], .contexts []⟩,
    ⟨[93585], [93585], .contexts []⟩,
    ⟨[93583], [93583], .contexts []⟩,
    ⟨[93581], [93581], .contexts []⟩,
    ⟨[
      93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [93581], .contexts [
        ⟨80321, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨80116, false, false, [], [15, 13, 1, 11]⟩,
        ⟨80322, false, false, [], [15, 13, 1, 11]⟩,
        ⟨80115, false, false, [], [15, 13, 1, 11]⟩,
        ⟨80115, false, false, [], [15, 13, 1, 11]⟩,
        ⟨80113, false, false, [], [13, 1, 11]⟩,
        ⟨80323, false, false, [], [13, 1, 11]⟩,
        ⟨80112, false, false, [], [13, 1, 11]⟩,
        ⟨80112, false, false, [], [13, 1, 11]⟩,
        ⟨80110, false, false, [], [1, 11]⟩,
        ⟨80324, false, false, [], [1, 11]⟩,
        ⟨80109, false, false, [], [1, 11]⟩,
        ⟨80109, false, false, [], [1, 11]⟩,
        ⟨80107, false, false, [], [11]⟩,
        ⟨80325, false, false, [], [11]⟩,
        ⟨80106, false, false, [], [11]⟩,
        ⟨80106, false, false, [], [11]⟩,
        ⟨80104, false, false, [], []⟩,
        ⟨80326, false, false, [], []⟩,
        ⟨80103, false, false, [], []⟩,
        ⟨80103, false, false, [], []⟩
      ]⟩,
    ⟨[93579], [93579], .contexts []⟩,
    ⟨[93577], [93577], .contexts []⟩,
    ⟨[
      93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1
    ], [93571], .contexts [
        ⟨80327, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨80100, false, false, [], [1, 5, 3, 1]⟩,
        ⟨80328, false, false, [], [1, 5, 3, 1]⟩,
        ⟨80099, false, false, [], [1, 5, 3, 1]⟩,
        ⟨80099, false, false, [], [1, 5, 3, 1]⟩,
        ⟨80095, true, false, [], [1, 5, 3, 1]⟩,
        ⟨8, false, false, [93577], [5, 3, 1]⟩,
        ⟨80096, false, false, [], [5, 3, 1]⟩,
        ⟨80329, false, false, [], [5, 3, 1]⟩,
        ⟨80096, false, false, [], [5, 3, 1]⟩,
        ⟨80096, false, false, [], [5, 3, 1]⟩,
        ⟨80093, false, false, [], [3, 1]⟩,
        ⟨80089, false, false, [], [3, 1]⟩,
        ⟨80090, false, false, [], [3, 1]⟩,
        ⟨80090, false, false, [], [3, 1]⟩,
        ⟨80088, true, false, [], [3, 1]⟩,
        ⟨20, false, false, [93573], [1]⟩,
        ⟨80086, false, false, [], [1]⟩,
        ⟨80085, false, false, [], [1]⟩,
        ⟨80086, false, false, [], [1]⟩,
        ⟨80086, false, false, [], [1]⟩,
        ⟨80084, true, false, [], [1]⟩,
        ⟨8, false, false, [93571], []⟩,
        ⟨80082, false, false, [], []⟩,
        ⟨80081, false, false, [], []⟩,
        ⟨80082, false, false, [], []⟩,
        ⟨80082, false, false, [], []⟩
      ]⟩,
    ⟨[
      93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11
    ], [93563], .contexts [
        ⟨80330, false, false, [], [15, 13, 1, 11]⟩,
        ⟨80080, true, false, [], [15, 13, 1, 11]⟩,
        ⟨1, false, false, [93569], [13, 1, 11]⟩,
        ⟨80078, false, false, [], [13, 1, 11]⟩,
        ⟨80077, false, false, [], [13, 1, 11]⟩,
        ⟨80078, false, false, [], [13, 1, 11]⟩,
        ⟨80078, false, false, [], [13, 1, 11]⟩,
        ⟨80076, true, false, [], [13, 1, 11]⟩,
        ⟨59, false, false, [93567], [1, 11]⟩,
        ⟨80074, false, false, [], [1, 11]⟩,
        ⟨80073, false, false, [], [1, 11]⟩,
        ⟨80074, false, false, [], [1, 11]⟩,
        ⟨80074, false, false, [], [1, 11]⟩,
        ⟨80072, true, false, [], [1, 11]⟩,
        ⟨8, false, false, [93565], [11]⟩,
        ⟨80070, false, false, [], [11]⟩,
        ⟨80069, false, false, [], [11]⟩,
        ⟨80070, false, false, [], [11]⟩,
        ⟨80070, false, false, [], [11]⟩,
        ⟨80068, true, false, [], [11]⟩,
        ⟨53, false, false, [93563], []⟩,
        ⟨80066, false, false, [], []⟩,
        ⟨80065, false, false, [], []⟩,
        ⟨80066, false, false, [], []⟩,
        ⟨80066, false, false, [], []⟩
      ]⟩,
    ⟨[
      93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [23741, 89185], .contexts [
        ⟨80331, false, false, [], [9, 1, 5]⟩,
        ⟨80064, true, false, [], [9, 1, 5]⟩,
        ⟨46, false, false, [93561], [1, 5]⟩,
        ⟨80060, false, false, [], [1, 5]⟩,
        ⟨80059, false, false, [], [1, 5]⟩,
        ⟨80060, false, false, [], [1, 5]⟩,
        ⟨80060, false, false, [], [1, 5]⟩,
        ⟨80060, true, false, [], [1, 5]⟩,
        ⟨80060, true, false, [], [1, 5]⟩,
        ⟨80059, true, false, [], [1, 5]⟩,
        ⟨80058, true, false, [], [1, 5]⟩,
        ⟨161, false, false, [89185], [5]⟩,
        ⟨162, false, false, [89185], [5]⟩,
        ⟨54807, false, false, [], [5, 5]⟩,
        ⟨54810, false, false, [], [5, 5]⟩,
        ⟨54804, false, false, [], [5, 5]⟩,
        ⟨54806, false, false, [], [5, 5]⟩,
        ⟨54806, false, false, [], [5, 5]⟩,
        ⟨80058, false, false, [23741], [5]⟩,
        ⟨80061, false, false, [], [5]⟩,
        ⟨80062, false, false, [], [5]⟩,
        ⟨54809, true, false, [], [93561, 5]⟩,
        ⟨80061, false, false, [], [5]⟩,
        ⟨80062, false, false, [], [5]⟩,
        ⟨80062, false, false, [], [5]⟩,
        ⟨80058, true, false, [23741], [5]⟩,
        ⟨28, false, false, [23741, 89185], []⟩,
        ⟨54488, false, false, [23741], []⟩,
        ⟨54804, false, false, [], []⟩,
        ⟨54805, false, false, [], []⟩
      ]⟩,
    ⟨[30377], [23741, 30367], .source 15253⟩,
    ⟨[30379], [30377, 30345], .source 15254⟩,
    ⟨[
      93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1
    ], [30379, 1063, 93555], .contexts [
        ⟨80332, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨54806, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨80056, false, false, [23741], [1, 15, 13, 1]⟩,
        ⟨80333, true, false, [], [93559, 1, 15, 13, 1]⟩,
        ⟨80043, false, false, [30377], [15, 13, 1]⟩,
        ⟨80023, false, false, [30377], [13, 1]⟩,
        ⟨80013, false, false, [30377], [1]⟩,
        ⟨80334, true, false, [], [93555, 1]⟩,
        ⟨80001, false, false, [30379], []⟩
      ]⟩,
    ⟨[30381], [30379, 1063], .source 15255⟩,
    ⟨[30383], [30381, 30351], .source 15256⟩,
    ⟨[30385], [30383, 30333], .source 15257⟩,
    ⟨[
      93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [30385, 82779], .contexts [
        ⟨80335, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨80336, true, false, [], [93555, 11, 9, 1, 5, 3]⟩,
        ⟨80020, false, false, [30381], [9, 1, 5, 3]⟩,
        ⟨80337, true, false, [], [93555, 9, 1, 5, 3]⟩,
        ⟨79994, false, false, [30383], [1, 5, 3]⟩,
        ⟨79960, false, false, [30383], [5, 3]⟩,
        ⟨79938, false, false, [30383], [3]⟩,
        ⟨80338, true, false, [], [93551, 3]⟩,
        ⟨79926, false, false, [30385], []⟩
      ]⟩,
    ⟨[30387], [30385, 323], .source 15258⟩,
    ⟨[30389], [30387, 16861], .source 15259⟩,
    ⟨[30391], [30389, 16855], .source 15260⟩,
    ⟨[
      93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11
    ], [30391, 15175, 80983], .contexts [
        ⟨80339, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨16529, false, false, [30385], [15, 13, 1, 11]⟩,
        ⟨80340, true, false, [], [82779, 15, 13, 1, 11]⟩,
        ⟨31372, false, false, [30387], [13, 1, 11]⟩,
        ⟨80341, true, false, [], [85325, 13, 1, 11]⟩,
        ⟨31366, false, false, [30389], [1, 11]⟩,
        ⟨80342, true, false, [], [79891, 1, 11]⟩,
        ⟨7507, false, false, [30391], [11]⟩,
        ⟨14902, false, false, [30391], []⟩
      ]⟩,
    ⟨[30393], [30391, 15175], .source 15261⟩,
    ⟨[30395], [30393, 4217], .source 15262⟩,
    ⟨[30397], [30395, 3155], .source 15263⟩,
    ⟨[30399], [3153, 9213], .source 15264⟩,
    ⟨[30401], [30397, 30399], .source 15265⟩,
    ⟨[30403], [30401, 2375], .source 15266⟩,
    ⟨[
      93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1
    ], [30403, 80429, 1], .contexts [
        ⟨80343, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨80344, true, false, [], [80983, 9, 1, 5, 3, 1]⟩,
        ⟨8417, false, false, [30393], [1, 5, 3, 1]⟩,
        ⟨80345, true, false, [], [80983, 1, 5, 3, 1]⟩,
        ⟨8409, false, false, [30395], [5, 3, 1]⟩,
        ⟨80346, true, false, [], [80793, 5, 3, 1]⟩,
        ⟨8242, false, false, [30397], [3, 1]⟩,
        ⟨12056, false, false, [30397, 3153], [3, 1]⟩,
        ⟨80347, true, false, [30397], [80429, 3, 1]⟩,
        ⟨80348, true, false, [], [80429, 3, 1]⟩,
        ⟨7886, false, false, [30401], [1]⟩,
        ⟨80349, true, false, [], [80429, 1]⟩
      ]⟩,
    ⟨[30405], [30403, 8433], .source 15267⟩,
    ⟨[30407], [30405, 8411], .source 15268⟩,
    ⟨[30409], [30407, 15553], .source 15269⟩,
    ⟨[
      93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [30409, 82785], .contexts [
        ⟨80350, false, false, [], [15, 13, 1, 11]⟩,
        ⟨7883, false, false, [30403], [15, 13, 1, 11]⟩,
        ⟨11541, false, false, [30403], [13, 1, 11]⟩,
        ⟨80351, true, false, [], [80991, 13, 1, 11]⟩,
        ⟨11511, false, false, [30405], [1, 11]⟩,
        ⟨80352, true, false, [], [81373, 1, 11]⟩,
        ⟨17046, false, false, [30407], [11]⟩,
        ⟨80353, true, false, [], [82819, 11]⟩,
        ⟨17059, false, false, [30409], []⟩
      ]⟩,
    ⟨[30411], [30409, 15979], .source 15270⟩,
    ⟨[30413], [30411, 15999], .source 15271⟩,
    ⟨[
      93673, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1
    ], [30413, 87579], .contexts [
        ⟨80354, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨19480, false, false, [30409], [1, 5, 3, 1]⟩,
        ⟨19502, false, false, [30409], [5, 3, 1]⟩,
        ⟨80355, true, false, [], [83171, 5, 3, 1]⟩,
        ⟨19648, false, false, [30411], [3, 1]⟩,
        ⟨80356, true, false, [], [83183, 3, 1]⟩,
        ⟨44742, false, false, [30413], [1]⟩,
        ⟨44767, false, false, [30413], []⟩
      ]⟩,
    ⟨[30415], [30413, 727], .source 15272⟩,
    ⟨[93675, 13], [93675, 13], .contexts []⟩,
    ⟨[93675, 13], [30415, 87579], .contexts [
        ⟨80359, false, false, [], []⟩,
        ⟨80264, true, false, [], [13]⟩,
        ⟨80264, true, false, [], [13]⟩,
        ⟨80263, true, false, [], [13]⟩,
        ⟨5361, false, false, [93673], []⟩,
        ⟨5362, false, false, [93673], []⟩,
        ⟨80357, false, false, [], [15]⟩,
        ⟨44786, false, false, [30413], []⟩,
        ⟨80358, true, false, [], [87579]⟩,
        ⟨44777, false, false, [30415], []⟩,
        ⟨13, true, false, [], [30415, 87579]⟩
      ]⟩,
    ⟨[30417], [30414], .source 15273⟩,
    ⟨[87579, 13], [30417, 93675], .contexts [
        ⟨80360, true, false, [30414], [13]⟩,
        ⟨59, false, false, [30414, 93675], []⟩,
        ⟨80361, true, false, [], [93675]⟩
      ]⟩,
    ⟨[93673], [93673], .contexts []⟩,
    ⟨[30415, 87579], [30415, 87579], .contexts []⟩,
    ⟨[30419], [30415, 2797], .source 15274⟩,
    ⟨[30419, 87579], [30419, 87579], .contexts []⟩,
    ⟨[30419, 87579], [30419, 87579], .contexts []⟩,
    ⟨[93673, 13], [93673, 13], .contexts []⟩,
    ⟨[93673, 13], [30419, 87579], .contexts [
        ⟨80368, false, false, [], []⟩,
        ⟨80262, true, false, [], [13]⟩,
        ⟨80262, true, false, [], [13]⟩,
        ⟨80363, true, false, [], [13]⟩,
        ⟨80262, true, false, [], [13]⟩,
        ⟨8, true, false, [93673], [13]⟩,
        ⟨80261, false, false, [], [1, 13]⟩,
        ⟨115, false, false, [93675], []⟩,
        ⟨118, false, false, [93675], []⟩,
        ⟨80359, false, false, [], [1, 13, 1]⟩,
        ⟨80360, false, false, [], [1, 13, 1]⟩,
        ⟨80364, false, false, [], [1, 13, 1]⟩,
        ⟨80364, false, false, [], [1, 13, 1]⟩,
        ⟨44768, false, false, [30415], [13, 1]⟩,
        ⟨44761, false, false, [30415], [1]⟩,
        ⟨80365, true, false, [], [87577, 1]⟩,
        ⟨44767, false, false, [30419], []⟩,
        ⟨80366, false, false, [], []⟩,
        ⟨80367, false, false, [], []⟩,
        ⟨44777, false, false, [30419], []⟩
      ]⟩,
    ⟨[93673, 13], [30419, 87579], .contexts [
        ⟨80369, false, false, [], []⟩,
        ⟨13, true, false, [], [30419, 87579]⟩
      ]⟩,
    ⟨[30421], [30418], .source 15275⟩,
    ⟨[30417, 93675], [30417, 93675], .contexts []⟩,
    ⟨[30423], [30415, 30421], .source 15276⟩,
    ⟨[93673, 13], [30419, 87579], .contexts [
        ⟨80368, false, false, [], []⟩,
        ⟨80370, false, false, [], []⟩,
        ⟨80366, false, false, [], []⟩,
        ⟨80367, false, false, [], []⟩,
        ⟨80367, false, false, [], []⟩
      ]⟩,
    ⟨[30425], [30147, 30191], .source 15277⟩,
    ⟨[30427], [30419, 30425], .source 15278⟩,
    ⟨[93543], [30209, 87411], .contexts [
        ⟨79663, false, false, [], []⟩
      ]⟩,
    ⟨[30429], [30427, 30209], .source 15279⟩,
    ⟨[93673], [93673], .contexts []⟩,
    ⟨[93673], [93673], .contexts []⟩,
    ⟨[30431], [30428], .source 15280⟩,
    ⟨[30428], [30428], .contexts []⟩,
    ⟨[87411, 3], [30431, 93673], .contexts [
        ⟨80378, false, false, [30428], [87411, 3]⟩,
        ⟨80377, true, false, [30428, 30427], [3]⟩,
        ⟨79483, true, false, [30428, 30427], [3]⟩,
        ⟨80376, false, false, [30428], [93545, 13, 3]⟩,
        ⟨80375, false, false, [30428, 30419], [93545, 13, 3]⟩,
        ⟨79649, true, false, [30428, 30419, 30147], [13, 3]⟩,
        ⟨79598, true, false, [30428, 30419], [13, 3]⟩,
        ⟨80374, true, false, [30428], [3, 13, 3]⟩,
        ⟨4550, false, false, [30428, 93673], []⟩,
        ⟨80379, false, false, [30428], []⟩,
        ⟨80380, false, false, [30428], []⟩,
        ⟨80382, true, false, [], [93673]⟩,
        ⟨80382, true, false, [], [93673]⟩,
        ⟨80381, true, false, [], [93673]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1256. -/
def y322TCIndexRaw1256 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93673, 3], [30429, 87411], .contexts [
        ⟨80383, true, false, [30430], [3]⟩,
        ⟨20, false, false, [30430, 87411], []⟩,
        ⟨80381, false, true, [], [87411]⟩
      ]⟩,
    ⟨[30433], [30419, 21283], .source 15281⟩,
    ⟨[93675], [30423, 93673], .contexts [
        ⟨80372, true, false, [30416], []⟩,
        ⟨80372, true, false, [30416], []⟩,
        ⟨80362, true, false, [30416], []⟩,
        ⟨80370, true, false, [30416, 30418], [13]⟩,
        ⟨59, false, false, [30416, 30418, 93673], []⟩,
        ⟨80371, true, false, [30416], [93673]⟩,
        ⟨80361, false, true, [], [30421, 93673]⟩,
        ⟨80373, true, false, [], [93673]⟩
      ]⟩,
    ⟨[30423, 93673], [30423, 93673], .contexts []⟩,
    ⟨[93675], [30423, 93673], .contexts [
        ⟨80386, false, false, [], []⟩,
        ⟨80387, false, false, [], []⟩
      ]⟩,
    ⟨[30435], [30417, 30423], .source 15282⟩,
    ⟨[30437], [30433, 30435], .source 15283⟩,
    ⟨[93673, 5], [93673, 5], .contexts []⟩,
    ⟨[30439], [30436], .source 15284⟩,
    ⟨[30436], [30436], .contexts []⟩,
    ⟨[30439], [30436], .contexts [
        ⟨80392, false, false, [], []⟩,
        ⟨80393, false, false, [], []⟩,
        ⟨80393, false, false, [], []⟩
      ]⟩,
    ⟨[93673, 5], [30439, 93673], .contexts [
        ⟨80391, false, false, [], []⟩,
        ⟨80390, false, false, [30436], [93673, 5]⟩,
        ⟨80389, false, false, [30436, 30433], [93673, 5]⟩,
        ⟨80388, true, false, [30436, 30433, 30417], [5]⟩,
        ⟨80362, true, false, [30436, 30433], [5]⟩,
        ⟨80385, false, false, [30436], [87579, 13, 5]⟩,
        ⟨44778, true, false, [30436, 30419], [13, 5]⟩,
        ⟨80374, true, false, [30436], [5, 13, 5]⟩,
        ⟨1116, false, false, [30436, 93673], []⟩,
        ⟨80379, false, false, [30436], []⟩,
        ⟨80380, false, false, [30436], []⟩,
        ⟨80394, true, false, [], [93673]⟩
      ]⟩,
    ⟨[30441], [30419, 21285], .source 15285⟩,
    ⟨[30443], [30441, 17543], .source 15286⟩,
    ⟨[84709, 7], [84709, 7], .contexts []⟩,
    ⟨[30445], [30442], .source 15287⟩,
    ⟨[30442], [30442], .contexts []⟩,
    ⟨[30445], [30442], .contexts [
        ⟨80399, false, false, [], []⟩,
        ⟨80400, false, false, [], []⟩,
        ⟨80400, false, false, [], []⟩
      ]⟩,
    ⟨[84709, 7], [30445, 93673], .contexts [
        ⟨80398, false, false, [], []⟩,
        ⟨80397, false, false, [30442], [84709, 7]⟩,
        ⟨28327, true, false, [30442, 30441], [7]⟩,
        ⟨28147, true, false, [30442, 30441], [7]⟩,
        ⟨80396, false, false, [30442], [84713, 13, 7]⟩,
        ⟨44780, true, false, [30442, 30419], [13, 7]⟩,
        ⟨80374, true, false, [30442], [7, 13, 7]⟩,
        ⟨21371, false, false, [30442, 93673], []⟩,
        ⟨80379, false, false, [30442], []⟩,
        ⟨80380, false, false, [30442], []⟩,
        ⟨80401, true, false, [], [93673]⟩
      ]⟩,
    ⟨[30443], [30444], .contexts [
        ⟨80399, true, true, [], []⟩
      ]⟩,
    ⟨[93673, 7], [30443, 84709], .contexts [
        ⟨80402, true, false, [30444], [7]⟩,
        ⟨38, false, false, [30444, 84709], []⟩,
        ⟨80403, true, false, [], [84709]⟩
      ]⟩,
    ⟨[30419, 91121], [30419, 91121], .contexts []⟩,
    ⟨[30419, 91121], [30419, 91121], .contexts []⟩,
    ⟨[91121, 13], [91121, 13], .contexts []⟩,
    ⟨[93671], [93671], .contexts []⟩,
    ⟨[30418], [30418], .contexts []⟩,
    ⟨[30421], [30418], .contexts [
        ⟨80371, false, false, [], []⟩,
        ⟨80409, false, false, [], []⟩,
        ⟨80409, false, false, [], []⟩
      ]⟩,
    ⟨[91121, 13], [30421, 93671], .contexts [
        ⟨80407, false, false, [], []⟩,
        ⟨80406, true, false, [30418], [13]⟩,
        ⟨80405, true, false, [30418], [13]⟩,
        ⟨64480, true, false, [], [13]⟩,
        ⟨80374, true, false, [30418], [11, 13]⟩,
        ⟨931, false, false, [30418, 93673], []⟩,
        ⟨54, false, false, [30418, 93673], []⟩,
        ⟨80266, false, false, [30418], []⟩,
        ⟨80408, false, false, [30418], []⟩,
        ⟨80410, true, false, [], [93671]⟩
      ]⟩,
    ⟨[30419], [30420], .contexts [
        ⟨80371, true, true, [], []⟩
      ]⟩,
    ⟨[93671, 13], [30419, 91121], .contexts [
        ⟨80411, true, false, [30420], [13]⟩,
        ⟨59, false, false, [30420, 91121], []⟩,
        ⟨80412, true, false, [], [91121]⟩
      ]⟩,
    ⟨[93673, 1], [30423, 93673], .contexts [
        ⟨80263, false, false, [], []⟩,
        ⟨80388, false, false, [], []⟩,
        ⟨80387, false, false, [], []⟩,
        ⟨80387, false, false, [], []⟩
      ]⟩,
    ⟨[30423, 93671], [30423, 93671], .contexts []⟩,
    ⟨[30423, 93671], [30423, 93671], .contexts []⟩,
    ⟨[93671, 1], [93671, 1], .contexts []⟩,
    ⟨[30423], [30423], .contexts [
        ⟨13, false, false, [], [30423]⟩
      ]⟩,
    ⟨[93671, 1], [30423, 93671], .contexts [
        ⟨80417, false, false, [], []⟩,
        ⟨80266, true, false, [], [1]⟩,
        ⟨562, false, false, [93673], []⟩,
        ⟨563, false, false, [93673], []⟩,
        ⟨80414, false, false, [], [11]⟩,
        ⟨80259, false, false, [30423], []⟩,
        ⟨80415, false, false, [], []⟩,
        ⟨80416, false, false, [], []⟩,
        ⟨80408, false, false, [30423], []⟩,
        ⟨80418, true, false, [], [93671]⟩
      ]⟩,
    ⟨[30429, 87411], [30429, 87411], .contexts []⟩,
    ⟨[30429, 87411], [30429, 87411], .contexts []⟩,
    ⟨[93673, 3], [30429, 87411], .contexts [
        ⟨80384, false, false, [], []⟩,
        ⟨80420, false, false, [], []⟩,
        ⟨80421, false, false, [], []⟩,
        ⟨80421, false, false, [], []⟩
      ]⟩,
    ⟨[30429, 87413], [30429, 87413], .contexts []⟩,
    ⟨[30429, 87413], [30429, 87413], .contexts []⟩,
    ⟨[93671, 3], [93671, 3], .contexts []⟩,
    ⟨[93671, 3], [30429, 87413], .contexts [
        ⟨80425, false, false, [], []⟩,
        ⟨80266, true, false, [], [3]⟩,
        ⟨215, false, false, [93673], []⟩,
        ⟨216, false, false, [93673], []⟩,
        ⟨80422, false, false, [], [11]⟩,
        ⟨41561, false, false, [30429], []⟩,
        ⟨80423, false, false, [], []⟩,
        ⟨80424, false, false, [], []⟩,
        ⟨42877, false, false, [30429], []⟩,
        ⟨13, true, false, [], [30429, 87413]⟩
      ]⟩,
    ⟨[87413, 3], [30431, 93671], .contexts [
        ⟨80426, true, false, [30428], [3]⟩,
        ⟨20, false, false, [30428, 93671], []⟩,
        ⟨80381, true, false, [], [93671]⟩
      ]⟩,
    ⟨[30439, 93673], [30439, 93673], .contexts []⟩,
    ⟨[30439, 93673], [30439, 93673], .contexts []⟩,
    ⟨[93673, 5], [30439, 93673], .contexts [
        ⟨80391, false, false, [], []⟩,
        ⟨80395, false, false, [], []⟩,
        ⟨80428, false, false, [], []⟩,
        ⟨80429, false, false, [], []⟩,
        ⟨80429, false, false, [], []⟩
      ]⟩,
    ⟨[30439, 93671], [30439, 93671], .contexts []⟩,
    ⟨[30439, 93671], [30439, 93671], .contexts []⟩,
    ⟨[93671, 5], [93671, 5], .contexts []⟩,
    ⟨[30439], [30439], .contexts [
        ⟨13, false, false, [], [30439]⟩
      ]⟩,
    ⟨[93671, 5], [30439, 93671], .contexts [
        ⟨80433, false, false, [], []⟩,
        ⟨80266, true, false, [], [5]⟩,
        ⟨642, false, false, [93673], []⟩,
        ⟨643, false, false, [93673], []⟩,
        ⟨80430, false, false, [], [11]⟩,
        ⟨80259, false, false, [30439], []⟩,
        ⟨80431, false, false, [], []⟩,
        ⟨80432, false, false, [], []⟩,
        ⟨80408, false, false, [30439], []⟩,
        ⟨80434, true, false, [], [93671]⟩
      ]⟩,
    ⟨[30443, 84709], [30443, 84709], .contexts []⟩,
    ⟨[30443, 84709], [30443, 84709], .contexts []⟩,
    ⟨[30443, 84707], [30443, 84707], .contexts []⟩,
    ⟨[30443, 84707], [30443, 84707], .contexts []⟩,
    ⟨[93671, 7], [93671, 7], .contexts []⟩,
    ⟨[93671, 7], [30443, 84707], .contexts [
        ⟨80440, false, false, [], []⟩,
        ⟨80266, true, false, [], [7]⟩,
        ⟨647, false, false, [93673], []⟩,
        ⟨648, false, false, [93673], []⟩,
        ⟨80404, false, false, [], [11]⟩,
        ⟨80436, false, false, [], [11]⟩,
        ⟨80437, false, false, [], [11]⟩,
        ⟨80437, false, false, [], [11]⟩,
        ⟨28140, false, false, [30443], []⟩,
        ⟨80438, false, false, [], []⟩,
        ⟨80439, false, false, [], []⟩,
        ⟨28333, false, false, [30443], []⟩,
        ⟨13, true, false, [], [30443, 84707]⟩
      ]⟩,
    ⟨[30421, 93671], [30421, 93671], .contexts []⟩,
    ⟨[30421, 93671], [30421, 93671], .contexts []⟩,
    ⟨[30421, 93669], [30421, 93669], .contexts []⟩,
    ⟨[93669, 13], [93669, 13], .contexts []⟩,
    ⟨[30420], [30420], .contexts []⟩,
    ⟨[93669, 13], [30419, 91123], .contexts [
        ⟨80445, false, false, [], []⟩,
        ⟨80444, true, false, [30420], [13]⟩,
        ⟨80255, true, false, [], [13]⟩,
        ⟨80443, true, false, [30420], [9, 13]⟩,
        ⟨80443, true, false, [30420], [9, 13]⟩,
        ⟨80442, true, false, [30420], [9, 13]⟩,
        ⟨80411, true, false, [30420], [9, 13]⟩,
        ⟨80407, true, false, [30420], [9, 13]⟩,
        ⟨942, false, false, [30420, 91121], []⟩,
        ⟨47, false, false, [30420, 91121], []⟩,
        ⟨64490, false, false, [30420], []⟩,
        ⟨64498, false, false, [30420], []⟩,
        ⟨80446, true, false, [], [91123]⟩,
        ⟨80446, true, false, [], [91123]⟩,
        ⟨80412, true, false, [], [91123]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1257. -/
def y322TCIndexRaw1257 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[91123, 13], [30421, 93669], .contexts [
        ⟨80447, true, false, [30418], [13]⟩,
        ⟨59, false, false, [30418, 93669], []⟩,
        ⟨80371, true, false, [], [93669]⟩
      ]⟩,
    ⟨[93671, 1], [30423, 93671], .contexts [
        ⟨80417, false, false, [], []⟩,
        ⟨80419, false, false, [], []⟩,
        ⟨80415, false, false, [], []⟩,
        ⟨80416, false, false, [], []⟩,
        ⟨80416, false, false, [], []⟩
      ]⟩,
    ⟨[93671, 9], [93669], .contexts [
        ⟨80267, false, false, [], []⟩,
        ⟨80268, false, false, [], []⟩,
        ⟨80254, false, false, [], []⟩,
        ⟨80254, false, false, [], []⟩
      ]⟩,
    ⟨[93667, 9], [93667, 9], .contexts []⟩,
    ⟨[93667], [93667], .contexts []⟩,
    ⟨[30447], [30422], .source 15288⟩,
    ⟨[30422], [30422], .contexts []⟩,
    ⟨[93671, 5], [30439, 93671], .contexts [
        ⟨80433, false, false, [], []⟩,
        ⟨80435, false, false, [], []⟩,
        ⟨80431, false, false, [], []⟩,
        ⟨80432, false, false, [], []⟩,
        ⟨80432, false, false, [], []⟩
      ]⟩,
    ⟨[30439, 93669], [30439, 93669], .contexts []⟩,
    ⟨[93671, 8], [93671, 9], .contexts [
        ⟨47, false, false, [93671], []⟩
      ]⟩,
    ⟨[93669, 5], [93669, 5], .contexts []⟩,
    ⟨[93669], [93669], .contexts []⟩,
    ⟨[30437], [30438], .contexts [
        ⟨80392, true, true, [], []⟩
      ]⟩,
    ⟨[30437], [30437], .contexts []⟩,
    ⟨[30438], [30438], .contexts []⟩,
    ⟨[93669, 5], [30437, 93669], .contexts [
        ⟨80458, false, false, [], []⟩,
        ⟨80456, true, false, [30438], [5]⟩,
        ⟨80255, true, false, [], [5]⟩,
        ⟨80455, true, false, [30438], [9, 5]⟩,
        ⟨960, false, false, [30438, 93671], []⟩,
        ⟨80457, false, false, [30438], []⟩,
        ⟨80450, false, false, [30438], []⟩,
        ⟨80459, false, false, [30438], []⟩,
        ⟨80462, true, false, [], [93669]⟩,
        ⟨80462, true, false, [], [93669]⟩,
        ⟨80460, true, false, [], [93669]⟩,
        ⟨80461, true, false, [], [93669]⟩
      ]⟩,
    ⟨[93671, 7], [30443, 84707], .contexts [
        ⟨80440, false, false, [], []⟩,
        ⟨80441, false, false, [], []⟩,
        ⟨80438, false, false, [], []⟩,
        ⟨80439, false, false, [], []⟩,
        ⟨80439, false, false, [], []⟩
      ]⟩,
    ⟨[30443, 84705], [30443, 84705], .contexts []⟩,
    ⟨[84705, 7], [84705, 7], .contexts []⟩,
    ⟨[84705, 7], [30445, 93669], .contexts [
        ⟨80466, false, false, [], []⟩,
        ⟨80465, true, false, [30442], [7]⟩,
        ⟨28136, true, false, [], [7]⟩,
        ⟨80464, true, false, [30442], [9, 7]⟩,
        ⟨579, false, false, [30442, 93671], []⟩,
        ⟨80457, false, false, [30442], []⟩,
        ⟨80450, false, false, [30442], []⟩,
        ⟨80459, false, false, [30442], []⟩,
        ⟨80401, true, false, [], [93669]⟩
      ]⟩,
    ⟨[30419, 91123], [30419, 91123], .contexts []⟩,
    ⟨[30419, 91123], [30419, 91123], .contexts []⟩,
    ⟨[93669, 13], [30419, 91123], .contexts [
        ⟨80445, false, false, [], []⟩,
        ⟨80447, false, false, [], []⟩,
        ⟨80468, false, false, [], []⟩,
        ⟨80469, false, false, [], []⟩,
        ⟨80469, false, false, [], []⟩
      ]⟩,
    ⟨[30449], [30419, 16023], .source 15289⟩,
    ⟨[30451], [30449, 30421], .source 15290⟩,
    ⟨[93669, 1], [93667], .contexts [
        ⟨80269, false, false, [], []⟩,
        ⟨80270, false, false, [], []⟩,
        ⟨80250, false, false, [], []⟩,
        ⟨80250, false, false, [], []⟩
      ]⟩,
    ⟨[30453], [30450], .source 15291⟩,
    ⟨[30450], [30450], .contexts []⟩,
    ⟨[93667, 13], [30453, 93667], .contexts [
        ⟨80251, true, false, [], [13]⟩,
        ⟨80472, false, false, [30450], [93669, 1, 13]⟩,
        ⟨80448, true, false, [30450, 30449], [1, 13]⟩,
        ⟨80471, false, false, [30450], [91123, 13, 1, 13]⟩,
        ⟨64500, true, false, [30450, 30419], [13, 1, 13]⟩,
        ⟨80470, true, false, [30450], [1, 13, 1, 13]⟩,
        ⟨2012, false, false, [30450, 93669], []⟩,
        ⟨9, false, false, [30450, 93669], []⟩,
        ⟨80473, false, false, [30450], []⟩,
        ⟨80452, false, false, [30450], []⟩,
        ⟨80475, true, false, [], [93667]⟩,
        ⟨80475, true, false, [], [93667]⟩,
        ⟨80474, true, false, [], [93667]⟩
      ]⟩,
    ⟨[93669], [93669], .contexts []⟩,
    ⟨[91127, 11], [30421, 93669], .contexts [
        ⟨64544, true, false, [], [11]⟩,
        ⟨64510, true, false, [], [13, 11]⟩,
        ⟨80470, true, false, [30418], [11, 13, 11]⟩,
        ⟨4838, false, false, [30418, 93669], []⟩,
        ⟨80477, false, false, [30418], []⟩,
        ⟨80459, false, false, [30418], []⟩,
        ⟨80410, true, false, [], [93669]⟩
      ]⟩,
    ⟨[93669, 11], [30419, 91127], .contexts [
        ⟨80478, true, false, [30420], [11]⟩,
        ⟨53, false, false, [30420, 91127], []⟩,
        ⟨80412, true, false, [], [91127]⟩
      ]⟩,
    ⟨[30447, 93667], [30447, 93667], .contexts []⟩,
    ⟨[93667, 9], [30447, 93667], .contexts [
        ⟨80451, false, false, [], []⟩,
        ⟨80451, false, false, [], []⟩,
        ⟨80251, true, false, [], [9]⟩,
        ⟨80255, true, false, [], [1, 9]⟩,
        ⟨80449, true, false, [30422], [9, 1, 9]⟩,
        ⟨582, false, false, [30422, 93671], []⟩,
        ⟨453, false, false, [30422, 93671], []⟩,
        ⟨80450, false, false, [30422], [1]⟩,
        ⟨80269, false, false, [30422], []⟩,
        ⟨80270, false, false, [30422], []⟩,
        ⟨80250, false, false, [30422], []⟩,
        ⟨80250, false, false, [30422], []⟩,
        ⟨80452, false, false, [30422], []⟩,
        ⟨80454, true, false, [], [93667]⟩,
        ⟨80454, true, false, [], [93667]⟩,
        ⟨80453, true, false, [], [93667]⟩,
        ⟨80480, false, false, [], []⟩,
        ⟨80480, false, false, [], []⟩
      ]⟩,
    ⟨[93665], [93665], .contexts []⟩,
    ⟨[30446], [30446], .contexts []⟩,
    ⟨[93665, 9], [30423, 93665], .contexts [
        ⟨80248, true, false, [], [9]⟩,
        ⟨80481, true, false, [30446], [5, 9]⟩,
        ⟨598, false, false, [30446, 93667], []⟩,
        ⟨29, false, false, [30446, 93667], []⟩,
        ⟨80271, false, false, [30446], []⟩,
        ⟨80272, false, false, [30446], []⟩,
        ⟨80247, false, false, [30446], []⟩,
        ⟨80247, false, false, [30446], []⟩,
        ⟨80482, false, false, [30446], []⟩,
        ⟨80483, true, false, [], [93665]⟩,
        ⟨80483, true, false, [], [93665]⟩,
        ⟨80453, false, true, [], [93665]⟩
      ]⟩,
    ⟨[30437, 93669], [30437, 93669], .contexts []⟩,
    ⟨[30437, 93669], [30437, 93669], .contexts []⟩,
    ⟨[30437, 93665], [30437, 93665], .contexts []⟩,
    ⟨[30437, 93665], [30437, 93665], .contexts []⟩,
    ⟨[93665, 1], [30439, 93669], .contexts [
        ⟨80488, true, false, [30436], [1]⟩,
        ⟨80487, true, false, [30436], [1]⟩,
        ⟨80248, true, false, [], [1]⟩,
        ⟨80251, true, false, [], [5, 1]⟩,
        ⟨80486, true, false, [30436], [1, 5, 1]⟩,
        ⟨80486, true, false, [30436], [1, 5, 1]⟩,
        ⟨80485, true, false, [30436], [1, 5, 1]⟩,
        ⟨80463, true, false, [30436], [1, 5, 1]⟩,
        ⟨80458, true, false, [30436], [1, 5, 1]⟩,
        ⟨874, false, false, [30436, 93669], []⟩,
        ⟨80477, false, false, [30436], []⟩,
        ⟨80459, false, false, [30436], []⟩,
        ⟨80394, true, false, [], [93669]⟩
      ]⟩,
    ⟨[93667], [30437, 93665], .contexts [
        ⟨80473, true, false, [], []⟩,
        ⟨80489, true, false, [30438], [1]⟩,
        ⟨8, false, false, [30438, 93665], []⟩,
        ⟨80460, true, false, [], [93665]⟩,
        ⟨80487, false, false, [], []⟩,
        ⟨80461, true, false, [], [93665]⟩
      ]⟩,
    ⟨[93667], [30437, 93665], .contexts [
        ⟨80490, false, false, [], []⟩
      ]⟩,
    ⟨[93667], [30437, 93665], .contexts [
        ⟨80491, false, false, [], []⟩,
        ⟨80488, false, false, [], []⟩
      ]⟩,
    ⟨[30455], [30439, 30453], .source 15292⟩,
    ⟨[30457], [30455, 30437], .source 15293⟩,
    ⟨[93665, 13], [30457, 93665], .contexts [
        ⟨80490, true, false, [30436], [13]⟩,
        ⟨80476, false, false, [30436], []⟩,
        ⟨80492, false, false, [30436, 30453], []⟩,
        ⟨80392, true, false, [], [30453, 30437, 93665]⟩,
        ⟨80493, true, false, [], [30437, 93665]⟩,
        ⟨80494, true, false, [], [93665]⟩
      ]⟩,
    ⟨[30445, 93669], [30445, 93669], .contexts []⟩,
    ⟨[30445, 93669], [30445, 93669], .contexts []⟩,
    ⟨[30459], [30445, 30437], .source 15294⟩,
    ⟨[84705, 1], [84703], .contexts [
        ⟨28166, false, false, [], []⟩,
        ⟨28167, false, false, [], []⟩,
        ⟨28131, false, false, [], []⟩,
        ⟨28131, false, false, [], []⟩
      ]⟩,
    ⟨[93665, 7], [93665, 7], .contexts []⟩,
    ⟨[30461], [30458], .source 15295⟩,
    ⟨[30458], [30458], .contexts []⟩,
    ⟨[93665, 7], [30461, 84703], .contexts [
        ⟨80500, false, false, [], []⟩,
        ⟨80498, false, false, [30458], [93665, 7]⟩,
        ⟨80492, true, false, [30458, 30445], [7]⟩,
        ⟨80251, true, false, [30458, 30445], [7]⟩,
        ⟨80497, true, false, [30458], [1, 7]⟩,
        ⟨80497, true, false, [30458], [1, 7]⟩,
        ⟨80496, true, false, [30458], [1, 7]⟩,
        ⟨80467, true, false, [30458], [1, 7]⟩,
        ⟨80466, true, false, [30458], [1, 7]⟩,
        ⟨502, false, false, [30458, 84705], []⟩,
        ⟨9, false, false, [30458, 84705], []⟩,
        ⟨80499, false, false, [30458], []⟩,
        ⟨28338, false, false, [30458], []⟩,
        ⟨80502, true, false, [], [84703]⟩,
        ⟨80502, true, false, [], [84703]⟩,
        ⟨80501, true, false, [], [84703]⟩
      ]⟩,
    ⟨[84703, 7], [30459, 93665], .contexts [
        ⟨80503, true, false, [30460], [7]⟩,
        ⟨38, false, false, [30460, 93665], []⟩,
        ⟨80501, false, true, [], [93665]⟩
      ]⟩,
    ⟨[30461, 84703], [30461, 84703], .contexts []⟩,
    ⟨[30461, 84703], [30461, 84703], .contexts []⟩,
    ⟨[93665, 7], [30461, 84703], .contexts [
        ⟨80500, false, false, [], []⟩,
        ⟨80503, false, false, [], []⟩,
        ⟨80505, false, false, [], []⟩,
        ⟨80506, false, false, [], []⟩,
        ⟨80506, false, false, [], []⟩
      ]⟩,
    ⟨[30465], [30461, 24751], .source 15297⟩,
    ⟨[30467], [30464], .source 15298⟩,
    ⟨[30469], [23463, 30467], .source 15299⟩,
    ⟨[30471], [30468], .source 15300⟩]

/-- Exact literal claimed equations and contextual derivations, block 1258. -/
def y322TCIndexRaw1258 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93663], [30471, 88955], .contexts [
        ⟨80510, false, false, [30468], [93663]⟩,
        ⟨53549, false, false, [30468], [30467, 93663]⟩,
        ⟨80509, false, false, [30468, 23464], [93663]⟩,
        ⟨38, true, false, [30468, 23464, 30464, 93663], []⟩,
        ⟨80243, true, false, [30468, 23464, 30464], [7, 7]⟩,
        ⟨80243, true, false, [30468, 23464, 30464], [7, 7]⟩,
        ⟨80274, true, false, [30468, 23464, 30464], [7, 7]⟩,
        ⟨80273, true, false, [30468, 23464, 30464], [7, 7]⟩,
        ⟨140, false, false, [30468, 23464, 30464, 93665], [7]⟩,
        ⟨141, false, false, [30468, 23464, 30464, 93665], [7]⟩,
        ⟨80507, false, false, [30468, 23464, 30464], [3, 7]⟩,
        ⟨59638, false, false, [30468, 23464, 30464, 30461], [7]⟩,
        ⟨80508, true, false, [30468, 23464, 30464], [87783, 7]⟩,
        ⟨59636, false, false, [30468, 23464], [7]⟩,
        ⟨13, true, false, [30468, 23464, 30464], [30465, 87783, 7]⟩,
        ⟨53562, false, false, [30468, 23464], []⟩,
        ⟨80511, true, false, [], [88955]⟩
      ]⟩,
    ⟨[30469], [30470], .contexts [
        ⟨80511, true, true, [], []⟩
      ]⟩,
    ⟨[30469], [30470], .contexts [
        ⟨80513, false, false, [], []⟩
      ]⟩,
    ⟨[30470], [30470], .contexts []⟩,
    ⟨[30469], [30470], .contexts [
        ⟨80514, false, false, [], []⟩,
        ⟨80515, false, false, [], []⟩,
        ⟨80515, false, false, [], []⟩
      ]⟩,
    ⟨[93663], [30471, 88955], .contexts [
        ⟨80512, false, false, [], []⟩
      ]⟩,
    ⟨[93663], [30471, 88955], .contexts [
        ⟨80517, false, false, [], []⟩
      ]⟩,
    ⟨[30471, 88957], [30471, 88957], .contexts []⟩,
    ⟨[93661], [30471, 88957], .contexts [
        ⟨80514, false, false, [30468], [93661]⟩,
        ⟨13, false, false, [30468, 30470], [93661]⟩,
        ⟨80275, true, false, [30468, 30470], []⟩,
        ⟨80240, true, false, [30468, 30470], []⟩,
        ⟨80518, false, false, [30468, 30470], [1]⟩,
        ⟨53238, false, false, [30468], []⟩,
        ⟨80519, false, false, [30468, 30470], []⟩,
        ⟨80511, true, false, [], [88957]⟩
      ]⟩,
    ⟨[88957, 15], [30469, 93659], .contexts [
        ⟨80520, true, false, [30470], [15]⟩,
        ⟨80237, false, false, [30470], []⟩,
        ⟨80277, false, false, [30470], []⟩,
        ⟨80516, true, false, [], [93659]⟩
      ]⟩,
    ⟨[30473], [30437, 30461], .source 15301⟩,
    ⟨[84701, 7], [84701, 7], .contexts []⟩,
    ⟨[30475], [30472], .source 15302⟩,
    ⟨[30477], [30475, 30461], .source 15303⟩,
    ⟨[84701, 7], [30477, 84701], .contexts [
        ⟨80523, false, false, [], []⟩,
        ⟨28128, true, false, [], [7]⟩,
        ⟨80522, false, false, [30472], [84703, 5, 7]⟩,
        ⟨80503, true, false, [30472, 30437], [5, 7]⟩,
        ⟨80488, true, false, [30472], [7, 5, 7]⟩,
        ⟨80488, true, false, [30472], [7, 5, 7]⟩,
        ⟨80492, true, false, [30472], [7, 5, 7]⟩,
        ⟨80246, true, false, [30472], [7, 5, 7]⟩,
        ⟨48805, false, false, [30472, 93665], []⟩,
        ⟨3273, false, false, [30472, 93665], []⟩,
        ⟨80507, false, false, [30472], [5]⟩,
        ⟨28128, false, false, [30472, 30461], []⟩,
        ⟨28346, false, false, [30472, 30461], []⟩,
        ⟨80524, true, false, [], [30461, 84701]⟩,
        ⟨80525, true, false, [], [84701]⟩
      ]⟩,
    ⟨[88957, 15], [30469, 93659], .contexts [
        ⟨80521, false, false, [], []⟩
      ]⟩,
    ⟨[30469, 93659], [30469, 93659], .contexts []⟩,
    ⟨[30469, 93659], [30469, 93659], .contexts []⟩,
    ⟨[88953, 1], [88953, 1], .contexts []⟩,
    ⟨[93659], [93659], .contexts []⟩,
    ⟨[88953, 1], [30469, 93659], .contexts [
        ⟨80530, false, false, [], []⟩,
        ⟨59673, true, false, [], [1]⟩,
        ⟨7, false, false, [88955], []⟩,
        ⟨11, false, false, [88955], []⟩,
        ⟨53238, false, false, [], [15]⟩,
        ⟨53280, false, false, [], [15]⟩,
        ⟨53243, false, false, [], [15]⟩,
        ⟨53243, false, false, [], [15]⟩,
        ⟨80527, false, false, [], []⟩,
        ⟨80528, false, false, [], []⟩,
        ⟨80529, false, false, [], []⟩,
        ⟨80529, false, false, [], []⟩,
        ⟨80531, false, false, [30469], []⟩,
        ⟨13, true, false, [], [30469, 93659]⟩
      ]⟩,
    ⟨[30479], [24405, 25343], .source 15304⟩,
    ⟨[30469, 93659, 13], [30469, 93657], .contexts [
        ⟨80233, false, false, [30469], []⟩
      ]⟩,
    ⟨[30469, 93657], [30469, 93657], .contexts []⟩,
    ⟨[30469, 93657], [30469, 93657], .contexts []⟩,
    ⟨[30469, 93657], [30469, 93657], .contexts []⟩,
    ⟨[89825, 15], [89825, 15], .contexts []⟩,
    ⟨[93657], [93657], .contexts []⟩,
    ⟨[30481], [30478], .source 15305⟩,
    ⟨[30483], [30481, 30469], .source 15306⟩,
    ⟨[89825, 15], [30483, 93657], .contexts [
        ⟨80538, false, false, [], []⟩,
        ⟨57676, true, false, [], [15]⟩,
        ⟨57680, true, false, [], [13, 15]⟩,
        ⟨80533, false, false, [30478], [89829, 15, 13, 15]⟩,
        ⟨61884, true, false, [30478, 24405], [15, 13, 15]⟩,
        ⟨57844, true, false, [30478], [15, 13, 15]⟩,
        ⟨57842, true, false, [30478], [15, 13, 15]⟩,
        ⟨2022, false, false, [30478, 88957], []⟩,
        ⟨89, false, false, [30478, 88957], []⟩,
        ⟨80527, false, false, [30478], [13]⟩,
        ⟨80528, false, false, [30478], [13]⟩,
        ⟨80529, false, false, [30478], [13]⟩,
        ⟨80529, false, false, [30478], [13]⟩,
        ⟨80534, false, false, [30478], []⟩,
        ⟨80535, false, false, [30478], []⟩,
        ⟨80536, false, false, [30478], []⟩,
        ⟨80537, false, false, [30478], []⟩,
        ⟨80539, false, false, [30478, 30469], []⟩,
        ⟨80540, true, false, [], [30469, 93657]⟩,
        ⟨80541, true, false, [], [93657]⟩
      ]⟩,
    ⟨[30485], [30482], .source 15307⟩,
    ⟨[93657, 15], [30485, 89825], .contexts [
        ⟨80542, true, false, [30482], [15]⟩,
        ⟨1, false, false, [30482, 89825], []⟩,
        ⟨80543, true, false, [], [89825]⟩
      ]⟩,
    ⟨[30477, 84701], [30477, 84701], .contexts []⟩,
    ⟨[30477, 84701], [30477, 84701], .contexts []⟩,
    ⟨[84701, 7], [30477, 84701], .contexts [
        ⟨80523, false, false, [], []⟩,
        ⟨80526, false, false, [], []⟩,
        ⟨80545, false, false, [], []⟩,
        ⟨80546, false, false, [], []⟩,
        ⟨80546, false, false, [], []⟩
      ]⟩,
    ⟨[84699, 7], [84699, 7], .contexts []⟩,
    ⟨[30487], [30476], .source 15308⟩,
    ⟨[30476], [30476], .contexts []⟩,
    ⟨[30487], [30476], .contexts [
        ⟨80549, false, false, [], []⟩,
        ⟨80550, false, false, [], []⟩,
        ⟨80550, false, false, [], []⟩
      ]⟩,
    ⟨[84699, 7], [30487, 84699], .contexts [
        ⟨80548, false, false, [], []⟩,
        ⟨28124, true, false, [], [7]⟩,
        ⟨80547, true, false, [30476], [3, 7]⟩,
        ⟨14911, false, false, [30476, 84701], []⟩,
        ⟨28352, false, false, [30476], []⟩,
        ⟨28351, false, false, [30476], []⟩,
        ⟨28353, false, false, [30476], []⟩,
        ⟨80551, true, false, [], [84699]⟩
      ]⟩,
    ⟨[93655, 13], [93655, 13], .contexts []⟩,
    ⟨[30468], [30468], .contexts []⟩,
    ⟨[30471], [30468], .contexts [
        ⟨80511, false, false, [], []⟩,
        ⟨80554, false, false, [], []⟩,
        ⟨80554, false, false, [], []⟩
      ]⟩,
    ⟨[93655, 13], [30471, 88949], .contexts [
        ⟨80553, false, false, [], []⟩,
        ⟨80229, true, false, [], [13]⟩,
        ⟨80537, true, false, [30468], [1, 13]⟩,
        ⟨80536, true, false, [30468], [1, 13]⟩,
        ⟨80535, true, false, [30468], [1, 13]⟩,
        ⟨80534, true, false, [30468], [1, 13]⟩,
        ⟨80529, true, false, [30468], [13, 1, 13]⟩,
        ⟨80529, true, false, [30468], [13, 1, 13]⟩,
        ⟨80528, true, false, [30468], [13, 1, 13]⟩,
        ⟨80532, true, false, [30468], [13, 1, 13]⟩,
        ⟨80530, true, false, [30468], [13, 1, 13]⟩,
        ⟨919, false, false, [30468, 88953], []⟩,
        ⟨116, false, false, [30468, 88953], []⟩,
        ⟨53587, false, false, [30468], [1]⟩,
        ⟨53288, false, false, [30468], []⟩,
        ⟨53289, false, false, [30468], []⟩,
        ⟨53227, false, false, [30468], []⟩,
        ⟨53227, false, false, [30468], []⟩,
        ⟨62006, false, false, [30468], []⟩,
        ⟨80555, true, false, [], [88949]⟩
      ]⟩,
    ⟨[88949, 13], [30469, 93655], .contexts [
        ⟨80556, true, false, [30470], [13]⟩,
        ⟨59, false, false, [30470, 93655], []⟩,
        ⟨80513, true, false, [], [93655]⟩
      ]⟩,
    ⟨[30483, 93657], [30483, 93657], .contexts []⟩,
    ⟨[89825, 15], [30483, 93657], .contexts [
        ⟨80538, false, false, [], []⟩,
        ⟨80542, false, false, [], []⟩,
        ⟨80558, false, false, [], []⟩,
        ⟨80558, false, false, [], []⟩
      ]⟩,
    ⟨[93655, 15], [93655, 15], .contexts []⟩,
    ⟨[30482], [30482], .contexts []⟩,
    ⟨[30485], [30482], .contexts [
        ⟨80543, false, false, [], []⟩,
        ⟨80561, false, false, [], []⟩,
        ⟨80561, false, false, [], []⟩
      ]⟩,
    ⟨[93655, 15], [30485, 89823], .contexts [
        ⟨80560, false, false, [], []⟩,
        ⟨80229, true, false, [], [15]⟩,
        ⟨80559, true, false, [30482], [1, 15]⟩,
        ⟨1666, false, false, [30482, 89825], []⟩,
        ⟨9, false, false, [30482, 89825], []⟩,
        ⟨57707, false, false, [30482], []⟩,
        ⟨57708, false, false, [30482], []⟩,
        ⟨57671, false, false, [30482], []⟩,
        ⟨57671, false, false, [30482], []⟩,
        ⟨61962, false, false, [30482], []⟩,
        ⟨80562, true, false, [], [89823]⟩
      ]⟩,
    ⟨[30483], [30484], .contexts [
        ⟨80543, true, true, [], []⟩
      ]⟩,
    ⟨[89823, 15], [30483, 93655], .contexts [
        ⟨80563, true, false, [30484], [15]⟩,
        ⟨1, false, false, [30484, 93655], []⟩,
        ⟨80564, true, false, [], [93655]⟩
      ]⟩,
    ⟨[30487, 84699], [30487, 84699], .contexts []⟩,
    ⟨[30487, 84699], [30487, 84699], .contexts []⟩,
    ⟨[84697, 7], [84697, 7], .contexts []⟩,
    ⟨[30486], [30486], .contexts []⟩,
    ⟨[30477], [30486], .contexts [
        ⟨80549, true, true, [], []⟩,
        ⟨80569, false, false, [], []⟩,
        ⟨80569, false, false, [], []⟩
      ]⟩,
    ⟨[84697, 7], [30477, 84697], .contexts [
        ⟨80568, false, false, [], []⟩,
        ⟨28120, true, false, [], [7]⟩,
        ⟨80567, true, false, [30486], [1, 7]⟩,
        ⟨80567, true, false, [30486], [1, 7]⟩,
        ⟨80566, true, false, [30486], [1, 7]⟩,
        ⟨80552, true, false, [30486], [1, 7]⟩,
        ⟨80548, true, false, [30486], [1, 7]⟩,
        ⟨502, false, false, [30486, 84699], []⟩,
        ⟨9, false, false, [30486, 84699], []⟩,
        ⟨28172, false, false, [30486], []⟩,
        ⟨28173, false, false, [30486], []⟩,
        ⟨28119, false, false, [30486], []⟩,
        ⟨28119, false, false, [30486], []⟩,
        ⟨80570, true, false, [], [84697]⟩
      ]⟩,
    ⟨[30471, 88949], [30471, 88949], .contexts []⟩,
    ⟨[30471, 88949], [30471, 88949], .contexts []⟩,
    ⟨[93655, 13], [30471, 88949], .contexts [
        ⟨80553, false, false, [], []⟩,
        ⟨80556, false, false, [], []⟩,
        ⟨80572, false, false, [], []⟩,
        ⟨80573, false, false, [], []⟩,
        ⟨80573, false, false, [], []⟩
      ]⟩,
    ⟨[30471, 88947], [30471, 88947], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1259. -/
def y322TCIndexRaw1259 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93655, 11], [93653], .contexts [
        ⟨80281, false, false, [], []⟩,
        ⟨80282, false, false, [], []⟩,
        ⟨80225, false, false, [], []⟩,
        ⟨80225, false, false, [], []⟩
      ]⟩,
    ⟨[93655, 10], [93655, 11], .contexts [
        ⟨54, false, false, [93655], []⟩
      ]⟩,
    ⟨[88947, 13], [88947, 13], .contexts []⟩,
    ⟨[93653], [93653], .contexts []⟩,
    ⟨[88947, 13], [30469, 93653], .contexts [
        ⟨80578, false, false, [], []⟩,
        ⟨80575, true, false, [30470], [13]⟩,
        ⟨53224, true, false, [], [13]⟩,
        ⟨80574, true, false, [30470], [11, 13]⟩,
        ⟨931, false, false, [30470, 93655], []⟩,
        ⟨80577, false, false, [30470], []⟩,
        ⟨80576, false, false, [30470], []⟩,
        ⟨80579, false, false, [30470], []⟩,
        ⟨80515, true, false, [], [93653]⟩,
        ⟨80515, true, false, [], [93653]⟩,
        ⟨80514, true, false, [], [93653]⟩
      ]⟩,
    ⟨[30485, 89823], [30485, 89823], .contexts []⟩,
    ⟨[30485, 89823], [30485, 89823], .contexts []⟩,
    ⟨[30485, 89821], [30485, 89821], .contexts []⟩,
    ⟨[89821, 15], [89821, 15], .contexts []⟩,
    ⟨[30483], [30483], .contexts []⟩,
    ⟨[30483], [30484], .contexts [
        ⟨80564, false, false, [], []⟩
      ]⟩,
    ⟨[30484], [30484], .contexts []⟩,
    ⟨[30483], [30484], .contexts [
        ⟨80585, false, false, [], []⟩,
        ⟨80586, false, false, [], []⟩,
        ⟨80587, false, false, [], []⟩,
        ⟨80587, false, false, [], []⟩
      ]⟩,
    ⟨[89821, 15], [30483, 93653], .contexts [
        ⟨80584, false, false, [], []⟩,
        ⟨80583, true, false, [30484], [15]⟩,
        ⟨57668, true, false, [], [15]⟩,
        ⟨80582, true, false, [30484], [11, 15]⟩,
        ⟨80582, true, false, [30484], [11, 15]⟩,
        ⟨80581, true, false, [30484], [11, 15]⟩,
        ⟨80563, true, false, [30484], [11, 15]⟩,
        ⟨80560, true, false, [30484], [11, 15]⟩,
        ⟨2046, false, false, [30484, 93655], []⟩,
        ⟨80577, false, false, [30484], []⟩,
        ⟨80576, false, false, [30484], []⟩,
        ⟨80579, false, false, [30484], []⟩,
        ⟨80588, true, false, [], [93653]⟩
      ]⟩,
    ⟨[30477, 84697], [30477, 84697], .contexts []⟩,
    ⟨[30477, 84697], [30477, 84697], .contexts []⟩,
    ⟨[84695, 7], [84695, 7], .contexts []⟩,
    ⟨[30469, 93653], [30469, 93653], .contexts []⟩,
    ⟨[93651, 13], [93651, 13], .contexts []⟩,
    ⟨[93651, 13], [30471, 88945], .contexts [
        ⟨80594, false, false, [], []⟩,
        ⟨80223, true, false, [], [13]⟩,
        ⟨80593, true, false, [30468], [9, 13]⟩,
        ⟨80593, true, false, [30468], [9, 13]⟩,
        ⟨80580, true, false, [30468], [9, 13]⟩,
        ⟨80578, true, false, [30468], [9, 13]⟩,
        ⟨942, false, false, [30468, 88947], []⟩,
        ⟨62045, false, false, [30468], []⟩,
        ⟨62044, false, false, [30468], []⟩,
        ⟨62047, false, false, [30468], []⟩,
        ⟨80555, true, false, [], [88945]⟩
      ]⟩,
    ⟨[88945, 13], [30469, 93651], .contexts [
        ⟨80595, true, false, [30470], [13]⟩,
        ⟨59, false, false, [30470, 93651], []⟩,
        ⟨80513, true, false, [], [93651]⟩
      ]⟩,
    ⟨[30483, 93653], [30483, 93653], .contexts []⟩,
    ⟨[30483, 93651], [30483, 93651], .contexts []⟩,
    ⟨[93651, 15], [93651, 15], .contexts []⟩,
    ⟨[93651, 15], [30485, 89819], .contexts [
        ⟨80599, false, false, [], []⟩,
        ⟨80598, true, false, [30482], [15]⟩,
        ⟨80223, true, false, [], [15]⟩,
        ⟨80597, true, false, [30482], [9, 15]⟩,
        ⟨80597, true, false, [30482], [9, 15]⟩,
        ⟨80589, true, false, [30482], [9, 15]⟩,
        ⟨80584, true, false, [30482], [9, 15]⟩,
        ⟨1671, false, false, [30482, 89821], []⟩,
        ⟨62027, false, false, [30482], []⟩,
        ⟨62026, false, false, [30482], []⟩,
        ⟨62028, false, false, [30482], []⟩,
        ⟨80562, true, false, [], [89819]⟩
      ]⟩,
    ⟨[89819, 15], [30483, 93651], .contexts [
        ⟨80600, true, false, [30484], [15]⟩,
        ⟨1, false, false, [30484, 93651], []⟩,
        ⟨80564, true, false, [], [93651]⟩
      ]⟩,
    ⟨[30487, 84695], [30487, 84695], .contexts []⟩,
    ⟨[84695, 7], [30487, 84695], .contexts [
        ⟨80592, false, false, [], []⟩,
        ⟨80592, false, false, [], []⟩,
        ⟨28116, true, false, [], [7]⟩,
        ⟨80591, true, false, [30476], [15, 7]⟩,
        ⟨80591, true, false, [30476], [15, 7]⟩,
        ⟨80590, true, false, [30476], [15, 7]⟩,
        ⟨80571, true, false, [30476], [15, 7]⟩,
        ⟨80568, true, false, [30476], [15, 7]⟩,
        ⟨18155, false, false, [30476, 84697], []⟩,
        ⟨10, false, false, [30476, 84697], []⟩,
        ⟨28174, false, false, [30476], []⟩,
        ⟨28175, false, false, [30476], []⟩,
        ⟨28115, false, false, [30476], []⟩,
        ⟨28115, false, false, [30476], []⟩,
        ⟨80551, true, false, [], [84695]⟩,
        ⟨80602, false, false, [], []⟩,
        ⟨80602, false, false, [], []⟩
      ]⟩,
    ⟨[84693, 7], [84693, 7], .contexts []⟩,
    ⟨[84693, 7], [30477, 84693], .contexts [
        ⟨80604, false, false, [], []⟩,
        ⟨28113, true, false, [], [7]⟩,
        ⟨80603, true, false, [30486], [13, 7]⟩,
        ⟨518, false, false, [30486, 84695], []⟩,
        ⟨64, false, false, [30486, 84695], []⟩,
        ⟨28177, false, false, [30486], []⟩,
        ⟨28178, false, false, [30486], []⟩,
        ⟨28112, false, false, [30486], []⟩,
        ⟨28112, false, false, [30486], []⟩,
        ⟨80570, true, false, [], [84693]⟩
      ]⟩,
    ⟨[30485, 89819], [30485, 89819], .contexts []⟩,
    ⟨[89817, 15], [89817, 15], .contexts []⟩,
    ⟨[93649], [93649], .contexts []⟩,
    ⟨[89817, 15], [30483, 93649], .contexts [
        ⟨80607, false, false, [], []⟩,
        ⟨57660, true, false, [], [15]⟩,
        ⟨80606, true, false, [30484], [1, 15]⟩,
        ⟨80606, true, false, [30484], [1, 15]⟩,
        ⟨80600, true, false, [30484], [1, 15]⟩,
        ⟨80599, true, false, [30484], [1, 15]⟩,
        ⟨1666, false, false, [30484, 93651], []⟩,
        ⟨9, false, false, [30484, 93651], []⟩,
        ⟨80285, false, false, [30484], []⟩,
        ⟨80286, false, false, [30484], []⟩,
        ⟨80218, false, false, [30484], []⟩,
        ⟨80218, false, false, [30484], []⟩,
        ⟨80608, false, false, [30484], []⟩,
        ⟨80588, true, false, [], [93649]⟩
      ]⟩,
    ⟨[93649, 15], [30485, 89817], .contexts [
        ⟨80609, true, false, [30482], [15]⟩,
        ⟨1, false, false, [30482, 89817], []⟩,
        ⟨80543, true, false, [], [89817]⟩
      ]⟩,
    ⟨[30477, 84693], [30477, 84693], .contexts []⟩,
    ⟨[30477, 84693], [30477, 84693], .contexts []⟩,
    ⟨[84691, 7], [84691, 7], .contexts []⟩,
    ⟨[84691], [84691], .contexts []⟩,
    ⟨[84691, 7], [30487, 84691], .contexts [
        ⟨80613, false, false, [], []⟩,
        ⟨28109, true, false, [], [7]⟩,
        ⟨80612, true, false, [30476], [1, 7]⟩,
        ⟨80612, true, false, [30476], [1, 7]⟩,
        ⟨80611, true, false, [30476], [1, 7]⟩,
        ⟨80605, true, false, [30476], [1, 7]⟩,
        ⟨80604, true, false, [30476], [1, 7]⟩,
        ⟨502, false, false, [30476, 84693], []⟩,
        ⟨9, false, false, [30476, 84693], []⟩,
        ⟨28179, false, false, [30476], []⟩,
        ⟨28180, false, false, [30476], []⟩,
        ⟨28108, false, false, [30476], []⟩,
        ⟨28108, false, false, [30476], []⟩,
        ⟨80614, false, false, [30476], []⟩,
        ⟨80551, true, false, [], [84691]⟩
      ]⟩,
    ⟨[30483, 93649], [30483, 93649], .contexts []⟩,
    ⟨[30483, 93649], [30483, 93649], .contexts []⟩,
    ⟨[93647, 15], [93647, 15], .contexts []⟩,
    ⟨[89815], [89815], .contexts []⟩,
    ⟨[93647, 15], [30485, 89815], .contexts [
        ⟨80618, false, false, [], []⟩,
        ⟨80215, true, false, [], [15]⟩,
        ⟨80617, true, false, [30482], [5, 15]⟩,
        ⟨80617, true, false, [30482], [5, 15]⟩,
        ⟨80616, true, false, [30482], [5, 15]⟩,
        ⟨80609, true, false, [30482], [5, 15]⟩,
        ⟨80607, true, false, [30482], [5, 15]⟩,
        ⟨2072, false, false, [30482, 89817], []⟩,
        ⟨29, false, false, [30482, 89817], []⟩,
        ⟨57716, false, false, [30482], []⟩,
        ⟨57717, false, false, [30482], []⟩,
        ⟨57656, false, false, [30482], []⟩,
        ⟨57656, false, false, [30482], []⟩,
        ⟨80619, false, false, [30482], []⟩,
        ⟨80562, true, false, [], [89815]⟩
      ]⟩,
    ⟨[30487, 84691], [30487, 84691], .contexts []⟩,
    ⟨[30487, 84691], [30487, 84691], .contexts []⟩,
    ⟨[84689, 7], [84689, 7], .contexts []⟩,
    ⟨[30485, 89815], [30485, 89815], .contexts []⟩,
    ⟨[30485, 89815], [30485, 89815], .contexts []⟩,
    ⟨[30485, 89813], [30485, 89813], .contexts []⟩,
    ⟨[89813, 15], [89813, 15], .contexts []⟩,
    ⟨[93645], [93645], .contexts []⟩,
    ⟨[89813, 15], [30483, 93645], .contexts [
        ⟨80627, false, false, [], []⟩,
        ⟨80626, true, false, [30484], [15]⟩,
        ⟨57653, true, false, [], [15]⟩,
        ⟨80625, true, false, [30484], [3, 15]⟩,
        ⟨80625, true, false, [30484], [3, 15]⟩,
        ⟨80624, true, false, [30484], [3, 15]⟩,
        ⟨80620, true, false, [30484], [3, 15]⟩,
        ⟨80618, true, false, [30484], [3, 15]⟩,
        ⟨1141, false, false, [30484, 93647], []⟩,
        ⟨21, false, false, [30484, 93647], []⟩,
        ⟨80289, false, false, [30484], []⟩,
        ⟨80290, false, false, [30484], []⟩,
        ⟨80210, false, false, [30484], []⟩,
        ⟨80210, false, false, [30484], []⟩,
        ⟨80628, false, false, [30484], []⟩,
        ⟨80588, true, false, [], [93645]⟩
      ]⟩,
    ⟨[93645, 15], [30485, 89813], .contexts [
        ⟨80629, true, false, [30482], [15]⟩,
        ⟨1, false, false, [30482, 89813], []⟩,
        ⟨80543, true, false, [], [89813]⟩
      ]⟩,
    ⟨[30477, 84689], [30477, 84689], .contexts []⟩,
    ⟨[84689, 7], [30477, 84689], .contexts [
        ⟨80623, false, false, [], []⟩,
        ⟨80623, false, false, [], []⟩,
        ⟨28105, true, false, [], [7]⟩,
        ⟨80622, true, false, [30486], [11, 7]⟩,
        ⟨80622, true, false, [30486], [11, 7]⟩,
        ⟨80621, true, false, [30486], [11, 7]⟩,
        ⟨80615, true, false, [30486], [11, 7]⟩,
        ⟨80613, true, false, [30486], [11, 7]⟩,
        ⟨555, false, false, [30486, 84691], []⟩,
        ⟨54, false, false, [30486, 84691], []⟩,
        ⟨28181, false, false, [30486], []⟩,
        ⟨28182, false, false, [30486], []⟩,
        ⟨28104, false, false, [30486], []⟩,
        ⟨28104, false, false, [30486], []⟩,
        ⟨80570, true, false, [], [84689]⟩,
        ⟨80631, false, false, [], []⟩,
        ⟨80631, false, false, [], []⟩
      ]⟩,
    ⟨[84687, 7], [84687, 7], .contexts []⟩,
    ⟨[84687, 7], [30487, 84687], .contexts [
        ⟨80633, false, false, [], []⟩,
        ⟨28101, true, false, [], [7]⟩,
        ⟨80632, true, false, [30476], [9, 7]⟩,
        ⟨579, false, false, [30476, 84689], []⟩,
        ⟨47, false, false, [30476, 84689], []⟩,
        ⟨28183, false, false, [30476], []⟩,
        ⟨28184, false, false, [30476], []⟩,
        ⟨28100, false, false, [30476], []⟩,
        ⟨28100, false, false, [30476], []⟩,
        ⟨80551, true, false, [], [84687]⟩
      ]⟩,
    ⟨[89813, 15], [30483, 93645], .contexts [
        ⟨80627, false, false, [], []⟩,
        ⟨80629, false, false, [], []⟩
      ]⟩,
    ⟨[30483, 93645], [30483, 93645], .contexts []⟩,
    ⟨[30483, 93641], [30483, 93641], .contexts []⟩,
    ⟨[89813], [89813], .contexts []⟩,
    ⟨[30484, 93641, 1, 1], [89813, 1], .contexts [
        ⟨80637, true, false, [30484, 30482], [1, 1]⟩,
        ⟨80203, true, false, [30484], [1, 1]⟩,
        ⟨80207, true, false, [30484], [15, 1, 1]⟩,
        ⟨80636, true, false, [30484, 30482], [1, 15, 1, 1]⟩,
        ⟨80636, true, false, [30484, 30482], [1, 15, 1, 1]⟩,
        ⟨80635, true, false, [30484, 30482], [1, 15, 1, 1]⟩,
        ⟨504, false, false, [30484, 30482, 89813], [1]⟩,
        ⟨80638, false, false, [30484, 30482], [1]⟩,
        ⟨80562, true, false, [30484], [89813, 1]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1260. -/
def y322TCIndexRaw1260 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93641], [30485, 89811], .contexts [
        ⟨80585, false, false, [30482], [93641]⟩,
        ⟨80637, true, false, [30482], []⟩,
        ⟨80564, false, false, [30482], [93641]⟩,
        ⟨8, true, false, [30482, 30484, 93641], []⟩,
        ⟨80639, false, false, [30482], []⟩,
        ⟨57720, false, false, [30482], []⟩,
        ⟨57721, false, false, [30482], []⟩,
        ⟨57648, false, false, [30482], []⟩,
        ⟨57648, false, false, [30482], []⟩,
        ⟨80543, true, false, [], [89811]⟩
      ]⟩,
    ⟨[30483], [30484], .contexts [
        ⟨80586, false, false, [], []⟩,
        ⟨80587, false, false, [], []⟩,
        ⟨80587, false, false, [], []⟩
      ]⟩,
    ⟨[89811, 13], [30483, 93639], .contexts [
        ⟨80640, true, false, [30484], [13]⟩,
        ⟨80199, false, false, [30484], []⟩,
        ⟨80293, false, false, [30484], []⟩,
        ⟨80641, true, false, [], [93639]⟩
      ]⟩,
    ⟨[93641], [30485, 89811], .contexts [
        ⟨80640, false, false, [], []⟩
      ]⟩,
    ⟨[30485, 89809], [30485, 89809], .contexts []⟩,
    ⟨[93643], [30485, 89809], .contexts [
        ⟨80586, false, false, [30482], [93643]⟩,
        ⟨13, false, false, [30482, 30484], [93643]⟩,
        ⟨80291, true, false, [30482, 30484], []⟩,
        ⟨80201, true, false, [30482, 30484], []⟩,
        ⟨80643, false, false, [30482, 30484], [15]⟩,
        ⟨57645, false, false, [30482], []⟩,
        ⟨80644, false, false, [30482, 30484], []⟩,
        ⟨80543, true, false, [], [89809]⟩
      ]⟩,
    ⟨[89809, 1], [30483, 93645], .contexts [
        ⟨80645, true, false, [30484], [1]⟩,
        ⟨80205, false, false, [30484], []⟩,
        ⟨80290, false, false, [30484], []⟩,
        ⟨80641, true, false, [], [93645]⟩
      ]⟩,
    ⟨[30487, 84687], [30487, 84687], .contexts []⟩,
    ⟨[30487, 84687], [30487, 84687], .contexts []⟩,
    ⟨[84685], [84685], .contexts []⟩,
    ⟨[93677], [84363, 3], .source 46903⟩,
    ⟨[84363, 3], [93677], .contexts [
        ⟨80650, true, false, [], []⟩
      ]⟩,
    ⟨[93677, 3], [84363], .contexts [
        ⟨80651, true, false, [], [3]⟩,
        ⟨20, false, false, [84363], []⟩,
        ⟨26306, false, false, [], []⟩
      ]⟩,
    ⟨[93677], [93677], .contexts []⟩,
    ⟨[93677], [93677], .contexts []⟩,
    ⟨[84363, 3], [93677], .contexts [
        ⟨80651, false, false, [], []⟩,
        ⟨80653, false, false, [], []⟩,
        ⟨80654, false, false, [], []⟩,
        ⟨80654, false, false, [], []⟩
      ]⟩,
    ⟨[17069, 83185], [17069, 83185], .contexts []⟩,
    ⟨[17069, 83185], [17069, 83185], .contexts []⟩,
    ⟨[30489], [17069, 10729], .source 15309⟩,
    ⟨[30491], [30489, 17071], .source 15310⟩,
    ⟨[30491, 93677], [30491, 93677], .contexts []⟩,
    ⟨[30491, 93677], [30491, 93677], .contexts []⟩,
    ⟨[93677, 5], [93677, 5], .contexts []⟩,
    ⟨[93677], [93677], .contexts []⟩,
    ⟨[93677, 5], [30491, 93677], .contexts [
        ⟨80662, false, false, [], []⟩,
        ⟨80655, true, false, [], [5]⟩,
        ⟨871, false, false, [84363], []⟩,
        ⟨873, false, false, [84363], []⟩,
        ⟨26315, false, false, [], [3, 5, 3]⟩,
        ⟨26317, false, false, [], [3, 5, 3]⟩,
        ⟨80656, false, false, [], [3, 5, 3]⟩,
        ⟨80657, false, false, [], [3, 5, 3]⟩,
        ⟨80657, false, false, [], [3, 5, 3]⟩,
        ⟨19667, false, false, [17069], [5, 3]⟩,
        ⟨80658, true, false, [], [83185, 5, 3]⟩,
        ⟨26319, false, false, [30489], [3]⟩,
        ⟨80659, true, false, [], [84363, 3]⟩,
        ⟨80651, false, false, [30491], []⟩,
        ⟨80660, false, false, [], []⟩,
        ⟨80661, false, false, [], []⟩,
        ⟨80663, false, false, [30491], []⟩
      ]⟩,
    ⟨[30491], [30491], .contexts [
        ⟨13, false, false, [], [30491]⟩
      ]⟩,
    ⟨[93677, 7], [93677, 7], .contexts []⟩,
    ⟨[93677, 7], [87715], .contexts [
        ⟨80666, false, false, [], []⟩,
        ⟨80655, true, false, [], [7]⟩,
        ⟨140, false, false, [84363], []⟩,
        ⟨141, false, false, [84363], []⟩,
        ⟨26304, false, false, [], [3]⟩,
        ⟨26276, false, false, [], [3]⟩,
        ⟨26277, false, false, [], [3]⟩,
        ⟨26277, false, false, [], [3]⟩,
        ⟨45822, false, false, [], []⟩,
        ⟨45823, false, false, [], []⟩,
        ⟨45824, false, false, [], []⟩,
        ⟨45824, false, false, [], []⟩,
        ⟨45831, false, false, [], []⟩,
        ⟨672, true, false, [], [87715]⟩
      ]⟩,
    ⟨[93677, 9], [87577], .contexts [
        ⟨80655, true, false, [], [9]⟩,
        ⟨669, false, false, [84363], []⟩,
        ⟨670, false, false, [84363], []⟩,
        ⟨26321, false, false, [], [3]⟩,
        ⟨26322, false, false, [], [3]⟩,
        ⟨19638, false, false, [], [3]⟩,
        ⟨19639, false, false, [], [3]⟩,
        ⟨19639, false, false, [], [3]⟩,
        ⟨44744, false, false, [], []⟩,
        ⟨44745, false, false, [], []⟩,
        ⟨44746, false, false, [], []⟩,
        ⟨44746, false, false, [], []⟩,
        ⟨64452, false, false, [], []⟩,
        ⟨64453, false, false, [], []⟩
      ]⟩,
    ⟨[16023, 93677], [16023, 93677], .contexts []⟩,
    ⟨[16023, 93677], [16023, 93677], .contexts []⟩,
    ⟨[93677, 11], [93677, 11], .contexts []⟩,
    ⟨[727, 93677], [727, 93677], .contexts []⟩,
    ⟨[727, 93677], [727, 93677], .contexts []⟩,
    ⟨[93677, 15], [93677, 15], .contexts []⟩,
    ⟨[93679], [93677, 1], .source 46904⟩,
    ⟨[93677, 1], [93679], .contexts [
        ⟨80675, true, false, [], []⟩
      ]⟩,
    ⟨[93679, 1], [93677], .contexts [
        ⟨80676, true, false, [], [1]⟩,
        ⟨8, false, false, [93677], []⟩,
        ⟨80654, false, false, [], []⟩
      ]⟩,
    ⟨[93679], [93679], .contexts []⟩,
    ⟨[93679], [93679], .contexts []⟩,
    ⟨[93677, 1], [93679], .contexts [
        ⟨80676, false, false, [], []⟩,
        ⟨80678, false, false, [], []⟩,
        ⟨80679, false, false, [], []⟩,
        ⟨80679, false, false, [], []⟩
      ]⟩,
    ⟨[30493], [11247, 26991], .source 15311⟩,
    ⟨[30495], [30493, 27011], .source 15312⟩,
    ⟨[93679, 3], [93679, 3], .contexts []⟩,
    ⟨[93679, 3], [30495, 92039], .contexts [
        ⟨80683, false, false, [], []⟩,
        ⟨80680, true, false, [], [3]⟩,
        ⟨1098, false, false, [93677], []⟩,
        ⟨1100, false, false, [93677], []⟩,
        ⟨80652, false, false, [], [1, 3, 1]⟩,
        ⟨26305, false, false, [], [1, 3, 1]⟩,
        ⟨26306, false, false, [], [1, 3, 1]⟩,
        ⟨26306, false, false, [], [1, 3, 1]⟩,
        ⟨26311, false, false, [], [3, 1]⟩,
        ⟨26309, false, false, [], [3, 1]⟩,
        ⟨26310, false, false, [], [3, 1]⟩,
        ⟨26310, false, false, [], [3, 1]⟩,
        ⟨69089, false, false, [11247], [1]⟩,
        ⟨80681, true, false, [], [92043, 1]⟩,
        ⟨68990, false, false, [30493], []⟩,
        ⟨69139, false, false, [30493], []⟩,
        ⟨80682, true, false, [], [92039]⟩,
        ⟨77546, false, false, [30495], []⟩
      ]⟩,
    ⟨[93679, 3], [30495, 92039], .contexts [
        ⟨80684, false, false, [], []⟩,
        ⟨13, true, false, [], [30495, 92039]⟩
      ]⟩,
    ⟨[30497], [30494], .source 15313⟩,
    ⟨[93677, 5], [30491, 93677], .contexts [
        ⟨80664, false, false, [], []⟩,
        ⟨80665, true, false, [], [93677]⟩
      ]⟩,
    ⟨[30491, 93679], [30491, 93679], .contexts []⟩,
    ⟨[30491, 93679], [30491, 93679], .contexts []⟩,
    ⟨[93679, 5], [93679, 5], .contexts []⟩,
    ⟨[93679], [93679], .contexts []⟩,
    ⟨[93679, 5], [30491, 93679], .contexts [
        ⟨80690, false, false, [], []⟩,
        ⟨80680, true, false, [], [5]⟩,
        ⟨98, false, false, [93677], []⟩,
        ⟨99, false, false, [93677], []⟩,
        ⟨80662, false, false, [], [1]⟩,
        ⟨80687, false, false, [], [1]⟩,
        ⟨80660, false, false, [], [1]⟩,
        ⟨80661, false, false, [], [1]⟩,
        ⟨80661, false, false, [], [1]⟩,
        ⟨80676, false, false, [30491], []⟩,
        ⟨80688, false, false, [], []⟩,
        ⟨80689, false, false, [], []⟩,
        ⟨80691, false, false, [30491], []⟩,
        ⟨80665, true, false, [], [93679]⟩
      ]⟩,
    ⟨[93679, 7], [25829, 91113], .contexts [
        ⟨80680, true, false, [], [7]⟩,
        ⟨104, false, false, [93677], []⟩,
        ⟨105, false, false, [93677], []⟩,
        ⟨80666, false, false, [], [1]⟩,
        ⟨80667, false, false, [], [1]⟩,
        ⟨45823, false, false, [], [1]⟩,
        ⟨45824, false, false, [], [1]⟩,
        ⟨45824, false, false, [], [1]⟩,
        ⟨64334, false, false, [], []⟩,
        ⟨64352, false, false, [25811], []⟩,
        ⟨64353, true, false, [], [91113]⟩,
        ⟨64344, false, false, [25829], []⟩,
        ⟨13, true, false, [], [25829, 91113]⟩
      ]⟩,
    ⟨[30499], [25828], .source 15314⟩,
    ⟨[93677, 11, 1], [16023, 93679], .contexts [
        ⟨80671, false, false, [], [1]⟩,
        ⟨80671, false, false, [], [1]⟩,
        ⟨80655, true, false, [], [11, 1]⟩,
        ⟨144, false, false, [84363], [1]⟩,
        ⟨145, false, false, [84363], [1]⟩,
        ⟨26326, false, false, [], [3, 1]⟩,
        ⟨26328, false, false, [], [3, 1]⟩,
        ⟨26324, false, false, [], [3, 1]⟩,
        ⟨26325, false, false, [], [3, 1]⟩,
        ⟨26325, false, false, [], [3, 1]⟩,
        ⟨80651, false, false, [16023], [1]⟩,
        ⟨80669, false, false, [], [1]⟩,
        ⟨80670, false, false, [], [1]⟩,
        ⟨80663, false, false, [16023], [1]⟩,
        ⟨19784, true, false, [], [93677, 1]⟩,
        ⟨80669, false, false, [], [1]⟩,
        ⟨80670, false, false, [], [1]⟩,
        ⟨80670, false, false, [], [1]⟩,
        ⟨80676, false, false, [16023], []⟩
      ]⟩,
    ⟨[727, 93679], [727, 93679], .contexts []⟩,
    ⟨[93677, 15, 1], [727, 93679], .contexts [
        ⟨80674, false, false, [], [1]⟩,
        ⟨80674, false, false, [], [1]⟩,
        ⟨80655, true, false, [], [15, 1]⟩,
        ⟨151, false, false, [84363], [1]⟩,
        ⟨152, false, false, [84363], [1]⟩,
        ⟨26337, false, false, [], [3, 1]⟩,
        ⟨26338, false, false, [], [3, 1]⟩,
        ⟨26335, false, false, [], [3, 1]⟩,
        ⟨26336, false, false, [], [3, 1]⟩,
        ⟨26336, false, false, [], [3, 1]⟩,
        ⟨80651, false, false, [727], [1]⟩,
        ⟨80672, false, false, [], [1]⟩,
        ⟨80673, false, false, [], [1]⟩,
        ⟨80663, false, false, [727], [1]⟩,
        ⟨19522, true, false, [], [93677, 1]⟩,
        ⟨80672, false, false, [], [1]⟩,
        ⟨80673, false, false, [], [1]⟩,
        ⟨80673, false, false, [], [1]⟩,
        ⟨80676, false, false, [727], []⟩,
        ⟨80696, false, false, [], []⟩
      ]⟩,
    ⟨[727, 93679], [727, 93679], .contexts []⟩,
    ⟨[93679, 15], [93679, 15], .contexts []⟩,
    ⟨[93679, 15], [727, 93679], .contexts [
        ⟨80699, false, false, [], []⟩,
        ⟨80680, true, false, [], [15]⟩,
        ⟨121, false, false, [93677], []⟩,
        ⟨122, false, false, [93677], []⟩,
        ⟨80697, false, false, [], []⟩,
        ⟨80698, false, false, [], []⟩,
        ⟨80691, false, false, [727], []⟩,
        ⟨19522, true, false, [], [93679]⟩
      ]⟩,
    ⟨[93681], [93679, 9], .source 46905⟩,
    ⟨[93679, 9], [93681], .contexts [
        ⟨80701, true, false, [], []⟩
      ]⟩,
    ⟨[93681, 9], [93679], .contexts [
        ⟨80702, true, false, [], [9]⟩,
        ⟨46, false, false, [93679], []⟩,
        ⟨80679, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1261. -/
def y322TCIndexRaw1261 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93681], [93681], .contexts []⟩,
    ⟨[93681], [93681], .contexts []⟩,
    ⟨[93679, 9], [93681], .contexts [
        ⟨80702, false, false, [], []⟩,
        ⟨80704, false, false, [], []⟩,
        ⟨80705, false, false, [], []⟩,
        ⟨80705, false, false, [], []⟩
      ]⟩,
    ⟨[93679, 1], [93677], .contexts [
        ⟨80677, false, false, [], []⟩
      ]⟩,
    ⟨[93681, 1], [93681, 1], .contexts []⟩,
    ⟨[93681, 1], [87581], .contexts [
        ⟨80708, false, false, [], []⟩,
        ⟨80706, true, false, [], [1]⟩,
        ⟨691, false, false, [93679], []⟩,
        ⟨694, false, false, [93679], []⟩,
        ⟨80707, false, false, [], [9, 1, 9]⟩,
        ⟨80653, false, false, [], [9, 1, 9]⟩,
        ⟨80654, false, false, [], [9, 1, 9]⟩,
        ⟨80654, false, false, [], [9, 1, 9]⟩,
        ⟨80668, false, false, [], [1, 9]⟩,
        ⟨44745, false, false, [], [1, 9]⟩,
        ⟨44746, false, false, [], [1, 9]⟩,
        ⟨44746, false, false, [], [1, 9]⟩,
        ⟨44769, false, false, [], [9]⟩,
        ⟨44770, false, false, [], [9]⟩,
        ⟨44771, false, false, [], [9]⟩,
        ⟨44771, false, false, [], [9]⟩,
        ⟨44790, false, false, [], []⟩,
        ⟨44791, false, false, [], []⟩,
        ⟨44792, false, false, [], []⟩,
        ⟨44792, false, false, [], []⟩,
        ⟨44797, false, false, [], []⟩
      ]⟩,
    ⟨[93681, 1], [87581], .contexts [
        ⟨80709, false, false, [], []⟩,
        ⟨672, true, false, [], [87581]⟩
      ]⟩,
    ⟨[30495, 92039], [30495, 92039], .contexts []⟩,
    ⟨[30495, 92039], [30495, 92039], .contexts []⟩,
    ⟨[30501], [30495, 29621], .source 15315⟩,
    ⟨[91721], [91721], .contexts []⟩,
    ⟨[30503], [30500], .source 15316⟩,
    ⟨[91721, 3], [30503, 93681], .contexts [
        ⟨13, false, false, [30500], [30501, 91721, 3]⟩,
        ⟨80714, true, false, [], [3]⟩,
        ⟨80713, false, false, [30500], [91721, 3]⟩,
        ⟨77551, true, false, [30500, 30495], [3]⟩,
        ⟨80712, true, false, [30500], [9, 3]⟩,
        ⟨80712, true, false, [30500], [9, 3]⟩,
        ⟨80711, true, false, [30500], [9, 3]⟩,
        ⟨80685, true, false, [30500], [9, 3]⟩,
        ⟨80683, true, false, [30500], [9, 3]⟩,
        ⟨197, true, false, [30500, 93679], [3]⟩,
        ⟨196, true, false, [30500, 93679], [3]⟩,
        ⟨80706, false, false, [30500], [3, 3]⟩,
        ⟨20, false, false, [30500, 93681], []⟩,
        ⟨80715, true, false, [], [93681]⟩
      ]⟩,
    ⟨[93681], [93681], .contexts []⟩,
    ⟨[87585, 11], [93681], .contexts [
        ⟨44824, true, false, [], [11]⟩,
        ⟨44824, true, false, [], [11]⟩,
        ⟨44823, true, false, [], [11]⟩,
        ⟨44822, true, false, [], [11]⟩,
        ⟨44808, true, false, [], [1, 11]⟩,
        ⟨44808, true, false, [], [1, 11]⟩,
        ⟨44807, true, false, [], [1, 11]⟩,
        ⟨44806, true, false, [], [1, 11]⟩,
        ⟨44792, true, false, [], [11, 1, 11]⟩,
        ⟨44792, true, false, [], [11, 1, 11]⟩,
        ⟨44791, true, false, [], [11, 1, 11]⟩,
        ⟨80710, true, false, [], [11, 1, 11]⟩,
        ⟨80708, true, false, [], [11, 1, 11]⟩,
        ⟨994, false, false, [93681], []⟩,
        ⟨80717, false, false, [], []⟩,
        ⟨672, true, false, [], [93681]⟩
      ]⟩,
    ⟨[93681, 11], [87585], .contexts [
        ⟨80718, true, false, [], [11]⟩,
        ⟨53, false, false, [87585], []⟩,
        ⟨44824, false, false, [], []⟩
      ]⟩,
    ⟨[93683], [87583, 13], .source 46906⟩,
    ⟨[87583, 13], [93683], .contexts [
        ⟨80720, true, false, [], []⟩
      ]⟩,
    ⟨[93683, 13], [87583], .contexts [
        ⟨80721, true, false, [], [13]⟩,
        ⟨59, false, false, [87583], []⟩,
        ⟨44808, false, false, [], []⟩
      ]⟩,
    ⟨[93683], [93683], .contexts []⟩,
    ⟨[93683], [93683], .contexts []⟩,
    ⟨[87583, 13], [93683], .contexts [
        ⟨80721, false, false, [], []⟩,
        ⟨80723, false, false, [], []⟩,
        ⟨80724, false, false, [], []⟩,
        ⟨80724, false, false, [], []⟩
      ]⟩,
    ⟨[21283, 93683], [21283, 93683], .contexts []⟩,
    ⟨[21283, 93683], [21283, 93683], .contexts []⟩,
    ⟨[93683, 5], [93683, 5], .contexts []⟩,
    ⟨[93683], [93683], .contexts []⟩,
    ⟨[93683, 9], [93683, 9], .contexts []⟩,
    ⟨[93683, 9], [91127], .contexts [
        ⟨80730, false, false, [], []⟩,
        ⟨80725, true, false, [], [9]⟩,
        ⟨77, false, false, [87583], []⟩,
        ⟨78, false, false, [87583], []⟩,
        ⟨64527, false, false, [], [13]⟩,
        ⟨64512, false, false, [], [13]⟩,
        ⟨64513, false, false, [], [13]⟩,
        ⟨64513, false, false, [], [13]⟩,
        ⟨64546, false, false, [], []⟩,
        ⟨64547, false, false, [], []⟩,
        ⟨64548, false, false, [], []⟩,
        ⟨64548, false, false, [], []⟩,
        ⟨64552, false, false, [], []⟩,
        ⟨672, true, false, [], [91127]⟩
      ]⟩,
    ⟨[93685], [93683, 15], .source 46907⟩,
    ⟨[93683, 15], [93685], .contexts [
        ⟨80732, true, false, [], []⟩
      ]⟩,
    ⟨[93685], [93685], .contexts []⟩,
    ⟨[93685], [93685], .contexts []⟩,
    ⟨[93683, 15], [93685], .contexts [
        ⟨80733, false, false, [], []⟩,
        ⟨80734, false, false, [], []⟩,
        ⟨80735, false, false, [], []⟩,
        ⟨80735, false, false, [], []⟩
      ]⟩,
    ⟨[21283, 93685], [21283, 93685], .contexts []⟩,
    ⟨[21283, 93685], [21283, 93685], .contexts []⟩,
    ⟨[93685, 5], [93685, 5], .contexts []⟩,
    ⟨[93685, 5], [21283, 93685], .contexts [
        ⟨80739, false, false, [], []⟩,
        ⟨80736, true, false, [], [5]⟩,
        ⟨27, false, false, [93683], []⟩,
        ⟨30, false, false, [93683], []⟩,
        ⟨80728, false, false, [], [15]⟩,
        ⟨80728, false, false, [], [15]⟩,
        ⟨80725, true, false, [], [5, 15]⟩,
        ⟨68, false, false, [87583], [15]⟩,
        ⟨69, false, false, [87583], [15]⟩,
        ⟨44826, false, false, [], [13, 15]⟩,
        ⟨80721, false, false, [21283], [15]⟩,
        ⟨80726, false, false, [], [15]⟩,
        ⟨80727, false, false, [], [15]⟩,
        ⟨80729, false, false, [21283], [15]⟩,
        ⟨44755, true, false, [], [93683, 15]⟩,
        ⟨80726, false, false, [], [15]⟩,
        ⟨80727, false, false, [], [15]⟩,
        ⟨80727, false, false, [], [15]⟩,
        ⟨80733, false, false, [21283], []⟩,
        ⟨80737, false, false, [], []⟩,
        ⟨80738, false, false, [], []⟩
      ]⟩,
    ⟨[93685], [93685], .contexts []⟩,
    ⟨[93685, 9], [91129], .contexts [
        ⟨80736, true, false, [], [9]⟩,
        ⟨45, false, false, [93683], []⟩,
        ⟨48, false, false, [93683], []⟩,
        ⟨80730, false, false, [], [15]⟩,
        ⟨80731, false, false, [], [15]⟩,
        ⟨64547, false, false, [], [15]⟩,
        ⟨64548, false, false, [], [15]⟩,
        ⟨64548, false, false, [], [15]⟩,
        ⟨64556, false, false, [], []⟩,
        ⟨64557, false, false, [], []⟩,
        ⟨64558, false, false, [], []⟩,
        ⟨64558, false, false, [], []⟩,
        ⟨64564, false, false, [], []⟩,
        ⟨672, true, false, [], [91129]⟩
      ]⟩,
    ⟨[93687], [93685, 1], .source 46908⟩,
    ⟨[93685, 1], [93687], .contexts [
        ⟨80743, true, false, [], []⟩
      ]⟩,
    ⟨[93687], [93687], .contexts []⟩,
    ⟨[93687], [93687], .contexts []⟩,
    ⟨[93685, 1], [93687], .contexts [
        ⟨80744, false, false, [], []⟩,
        ⟨80745, false, false, [], []⟩,
        ⟨80746, false, false, [], []⟩,
        ⟨80746, false, false, [], []⟩
      ]⟩,
    ⟨[21283, 93687], [21283, 93687], .contexts []⟩,
    ⟨[21283, 93687], [21283, 93687], .contexts []⟩,
    ⟨[93689], [93687, 3], .source 46909⟩,
    ⟨[93687, 3], [93689], .contexts [
        ⟨80750, true, false, [], []⟩
      ]⟩,
    ⟨[93691], [93689, 5], .source 46910⟩,
    ⟨[93689, 5], [93691], .contexts [
        ⟨80752, true, false, [], []⟩
      ]⟩,
    ⟨[93689], [93689], .contexts []⟩,
    ⟨[93691], [93691], .contexts []⟩,
    ⟨[93691], [93691], .contexts []⟩,
    ⟨[93689, 3], [93687], .contexts [
        ⟨80751, true, false, [], [3]⟩,
        ⟨20, false, false, [93687], []⟩,
        ⟨80746, false, false, [], []⟩
      ]⟩,
    ⟨[93689, 3, 5, 3], [21283, 93687, 3], .contexts [
        ⟨80757, false, false, [], [5, 3]⟩,
        ⟨80745, false, false, [], [5, 3]⟩,
        ⟨80746, false, false, [], [5, 3]⟩,
        ⟨80746, false, false, [], [5, 3]⟩,
        ⟨80747, true, false, [], [5, 3]⟩,
        ⟨98, false, false, [93685], [3]⟩,
        ⟨99, false, false, [93685], [3]⟩,
        ⟨80739, false, false, [], [1, 3]⟩,
        ⟨80740, false, false, [], [1, 3]⟩,
        ⟨80741, false, false, [21283], [1, 3]⟩,
        ⟨44755, true, false, [], [93685, 1, 3]⟩,
        ⟨80737, false, false, [], [1, 3]⟩,
        ⟨80738, false, false, [], [1, 3]⟩,
        ⟨80738, false, false, [], [1, 3]⟩,
        ⟨80744, false, false, [21283], [3]⟩,
        ⟨80748, false, false, [], [3]⟩,
        ⟨80749, false, false, [], [3]⟩,
        ⟨44755, true, false, [], [93687, 3]⟩,
        ⟨80748, false, false, [], [3]⟩,
        ⟨80749, false, false, [], [3]⟩,
        ⟨80749, false, false, [], [3]⟩
      ]⟩,
    ⟨[93693], [93691, 1], .source 46911⟩,
    ⟨[93691, 1], [93693], .contexts [
        ⟨80759, true, false, [], []⟩
      ]⟩,
    ⟨[93693, 1], [93691], .contexts [
        ⟨80760, true, false, [], [1]⟩,
        ⟨8, false, false, [93691], []⟩,
        ⟨80756, false, false, [], []⟩
      ]⟩,
    ⟨[93695], [93693, 9], .source 46912⟩,
    ⟨[93693, 9], [93695], .contexts [
        ⟨80762, true, false, [], []⟩
      ]⟩,
    ⟨[93693], [93693], .contexts []⟩,
    ⟨[93695, 9], [93693], .contexts [
        ⟨80763, true, false, [], [9]⟩,
        ⟨46, false, false, [93693], []⟩,
        ⟨80764, false, false, [], []⟩
      ]⟩,
    ⟨[93697], [93695, 11], .source 46913⟩,
    ⟨[93695, 11], [93697], .contexts [
        ⟨80766, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1262. -/
def y322TCIndexRaw1262 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93695], [93695], .contexts []⟩,
    ⟨[93699], [93697, 1], .source 46914⟩,
    ⟨[93697, 1], [93699], .contexts [
        ⟨80769, true, false, [], []⟩
      ]⟩,
    ⟨[93697], [93697], .contexts []⟩,
    ⟨[93701], [93699, 13], .source 46915⟩,
    ⟨[93699, 13], [93701], .contexts [
        ⟨80772, true, false, [], []⟩
      ]⟩,
    ⟨[93699], [93699], .contexts []⟩,
    ⟨[93701, 13], [93699], .contexts [
        ⟨80773, true, false, [], [13]⟩,
        ⟨59, false, false, [93699], []⟩,
        ⟨80774, false, false, [], []⟩
      ]⟩,
    ⟨[93703], [93701, 15], .source 46916⟩,
    ⟨[93701, 15], [93703], .contexts [
        ⟨80776, true, false, [], []⟩
      ]⟩,
    ⟨[93701], [93701], .contexts []⟩,
    ⟨[93703, 15], [93701], .contexts [
        ⟨80777, true, false, [], [15]⟩,
        ⟨1, false, false, [93701], []⟩,
        ⟨80778, false, false, [], []⟩
      ]⟩,
    ⟨[93705], [93703, 1], .source 46917⟩,
    ⟨[93703, 1], [93705], .contexts [
        ⟨80780, true, false, [], []⟩
      ]⟩,
    ⟨[93703], [93703], .contexts []⟩,
    ⟨[93705, 1], [93703], .contexts [
        ⟨80781, true, false, [], [1]⟩,
        ⟨8, false, false, [93703], []⟩,
        ⟨80782, false, false, [], []⟩
      ]⟩,
    ⟨[93707], [93705, 3], .source 46918⟩,
    ⟨[93705, 3], [93707], .contexts [
        ⟨80784, true, false, [], []⟩
      ]⟩,
    ⟨[93705], [93705], .contexts []⟩,
    ⟨[93709], [93707, 5], .source 46919⟩,
    ⟨[93707, 5], [93709], .contexts [
        ⟨80787, true, false, [], []⟩
      ]⟩,
    ⟨[93707], [93707], .contexts []⟩,
    ⟨[93711], [93709, 1], .source 46920⟩,
    ⟨[93709, 1], [93711], .contexts [
        ⟨80790, true, false, [], []⟩
      ]⟩,
    ⟨[93709], [93709], .contexts []⟩,
    ⟨[93713], [93711, 9], .source 46921⟩,
    ⟨[93711, 9], [93713], .contexts [
        ⟨80793, true, false, [], []⟩
      ]⟩,
    ⟨[93711], [93711], .contexts []⟩,
    ⟨[93715], [93713, 11], .source 46922⟩,
    ⟨[93713, 11], [93715], .contexts [
        ⟨80796, true, false, [], []⟩
      ]⟩,
    ⟨[93713], [93713], .contexts []⟩,
    ⟨[93717], [93715, 1], .source 46923⟩,
    ⟨[93715, 1], [93717], .contexts [
        ⟨80799, true, false, [], []⟩
      ]⟩,
    ⟨[93715], [93715], .contexts []⟩,
    ⟨[93719], [93717, 13], .source 46924⟩,
    ⟨[93717, 13], [93719], .contexts [
        ⟨80802, true, false, [], []⟩
      ]⟩,
    ⟨[93717], [93717], .contexts []⟩,
    ⟨[93721], [93719, 15], .source 46925⟩,
    ⟨[93719, 15], [93721], .contexts [
        ⟨80805, true, false, [], []⟩
      ]⟩,
    ⟨[93719], [93719], .contexts []⟩,
    ⟨[93723], [93721, 1], .source 46926⟩,
    ⟨[93721, 1], [93723], .contexts [
        ⟨80808, true, false, [], []⟩
      ]⟩,
    ⟨[93721], [93721], .contexts []⟩,
    ⟨[93725], [93723, 3], .source 46927⟩,
    ⟨[93723, 3], [93725], .contexts [
        ⟨80811, true, false, [], []⟩
      ]⟩,
    ⟨[93723], [93723], .contexts []⟩,
    ⟨[93727], [93725, 5], .source 46928⟩,
    ⟨[93725, 5], [93727], .contexts [
        ⟨80814, true, false, [], []⟩
      ]⟩,
    ⟨[93725], [93725], .contexts []⟩,
    ⟨[93727, 5], [93725], .contexts [
        ⟨80815, true, false, [], [5]⟩,
        ⟨28, false, false, [93725], []⟩,
        ⟨80816, false, false, [], []⟩
      ]⟩,
    ⟨[93729], [93727, 1], .source 46929⟩,
    ⟨[93727, 1], [93729], .contexts [
        ⟨80818, true, false, [], []⟩
      ]⟩,
    ⟨[93727], [93727], .contexts []⟩,
    ⟨[93731], [93729, 9], .source 46930⟩,
    ⟨[93729, 9], [93731], .contexts [
        ⟨80821, true, false, [], []⟩
      ]⟩,
    ⟨[93729], [93729], .contexts []⟩,
    ⟨[93731, 9], [93729], .contexts [
        ⟨80822, true, false, [], [9]⟩,
        ⟨46, false, false, [93729], []⟩,
        ⟨80823, false, false, [], []⟩
      ]⟩,
    ⟨[93733], [93731, 11], .source 46931⟩,
    ⟨[93731, 11], [93733], .contexts [
        ⟨80825, true, false, [], []⟩
      ]⟩,
    ⟨[93731], [93731], .contexts []⟩,
    ⟨[93735], [93733, 1], .source 46932⟩,
    ⟨[93733], [93733], .contexts []⟩,
    ⟨[93735, 1], [93733], .contexts [
        ⟨80828, false, false, [], [1]⟩,
        ⟨8, false, false, [93733], []⟩,
        ⟨80829, false, false, [], []⟩
      ]⟩,
    ⟨[93737], [93735, 13], .source 46933⟩]

/-- Exact literal claimed equations and contextual derivations, block 1263. -/
def y322TCIndexRaw1263 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93735, 13], [93737], .contexts [
        ⟨80831, true, false, [], []⟩
      ]⟩,
    ⟨[93735], [93735], .contexts []⟩,
    ⟨[93737, 13], [93735], .contexts [
        ⟨80832, true, false, [], [13]⟩,
        ⟨59, false, false, [93735], []⟩,
        ⟨80833, false, false, [], []⟩
      ]⟩,
    ⟨[93739], [93737, 15], .source 46934⟩,
    ⟨[93737], [93737], .contexts []⟩,
    ⟨[93739, 15], [93737], .contexts [
        ⟨80835, false, false, [], [15]⟩,
        ⟨1, false, false, [93737], []⟩,
        ⟨80836, false, false, [], []⟩
      ]⟩,
    ⟨[93741], [93739, 1], .source 46935⟩,
    ⟨[93739], [93739], .contexts []⟩,
    ⟨[93741, 1], [93739], .contexts [
        ⟨80838, false, false, [], [1]⟩,
        ⟨8, false, false, [93739], []⟩,
        ⟨80839, false, false, [], []⟩
      ]⟩,
    ⟨[93743], [93741, 3], .source 46936⟩,
    ⟨[93741], [93741], .contexts []⟩,
    ⟨[93743, 3], [93741], .contexts [
        ⟨80841, false, false, [], [3]⟩,
        ⟨20, false, false, [93741], []⟩,
        ⟨80842, false, false, [], []⟩
      ]⟩,
    ⟨[93745], [93743, 5], .source 46937⟩,
    ⟨[93743], [93743], .contexts []⟩,
    ⟨[93745, 5], [93743], .contexts [
        ⟨80844, false, false, [], [5]⟩,
        ⟨28, false, false, [93743], []⟩,
        ⟨80845, false, false, [], []⟩
      ]⟩,
    ⟨[93747], [93745, 1], .source 46938⟩,
    ⟨[93745], [93745], .contexts []⟩,
    ⟨[93747, 1], [93745], .contexts [
        ⟨80847, false, false, [], [1]⟩,
        ⟨8, false, false, [93745], []⟩,
        ⟨80848, false, false, [], []⟩
      ]⟩,
    ⟨[93749], [93747, 9], .source 46939⟩,
    ⟨[93747], [93747], .contexts []⟩,
    ⟨[93749, 9], [93747], .contexts [
        ⟨80850, false, false, [], [9]⟩,
        ⟨46, false, false, [93747], []⟩,
        ⟨80851, false, false, [], []⟩
      ]⟩,
    ⟨[93751], [93749, 11], .source 46940⟩,
    ⟨[93749], [93749], .contexts []⟩,
    ⟨[93751, 11], [93749], .contexts [
        ⟨80853, false, false, [], [11]⟩,
        ⟨53, false, false, [93749], []⟩,
        ⟨80854, false, false, [], []⟩
      ]⟩,
    ⟨[93753], [93751, 1], .source 46941⟩,
    ⟨[93751], [93751], .contexts []⟩,
    ⟨[93753, 1], [93751], .contexts [
        ⟨80856, false, false, [], [1]⟩,
        ⟨8, false, false, [93751], []⟩,
        ⟨80857, false, false, [], []⟩
      ]⟩,
    ⟨[93755], [93753, 13], .source 46942⟩,
    ⟨[93753], [93753], .contexts []⟩,
    ⟨[93755, 13], [93753], .contexts [
        ⟨80859, false, false, [], [13]⟩,
        ⟨59, false, false, [93753], []⟩,
        ⟨80860, false, false, [], []⟩
      ]⟩,
    ⟨[93757], [93755, 15], .source 46943⟩,
    ⟨[93755], [93755], .contexts []⟩,
    ⟨[93757, 15], [93755], .contexts [
        ⟨80862, false, false, [], [15]⟩,
        ⟨1, false, false, [93755], []⟩,
        ⟨80863, false, false, [], []⟩
      ]⟩,
    ⟨[93759], [93757, 1], .source 46944⟩,
    ⟨[93757], [93757], .contexts []⟩,
    ⟨[93759, 1], [93757], .contexts [
        ⟨80865, false, false, [], [1]⟩,
        ⟨8, false, false, [93757], []⟩,
        ⟨80866, false, false, [], []⟩
      ]⟩,
    ⟨[93761], [93759, 3], .source 46945⟩,
    ⟨[93759], [93759], .contexts []⟩,
    ⟨[93761, 3], [93759], .contexts [
        ⟨80868, false, false, [], [3]⟩,
        ⟨20, false, false, [93759], []⟩,
        ⟨80869, false, false, [], []⟩
      ]⟩,
    ⟨[93763], [93761, 5], .source 46946⟩,
    ⟨[93761, 5], [93763], .contexts [
        ⟨80871, true, false, [], []⟩
      ]⟩,
    ⟨[93761], [93761], .contexts []⟩,
    ⟨[93763, 5], [93761], .contexts [
        ⟨80872, true, false, [], [5]⟩,
        ⟨28, false, false, [93761], []⟩,
        ⟨80873, false, false, [], []⟩
      ]⟩,
    ⟨[93765], [93763, 1], .source 46947⟩,
    ⟨[93763, 1], [93765], .contexts [
        ⟨80875, true, false, [], []⟩
      ]⟩,
    ⟨[93763], [93763], .contexts []⟩,
    ⟨[93765, 1], [93763], .contexts [
        ⟨80876, true, false, [], [1]⟩,
        ⟨8, false, false, [93763], []⟩,
        ⟨80877, false, false, [], []⟩
      ]⟩,
    ⟨[93767], [93765, 9], .source 46948⟩,
    ⟨[93765, 9], [93767], .contexts [
        ⟨80879, true, false, [], []⟩
      ]⟩,
    ⟨[93765], [93765], .contexts []⟩,
    ⟨[93767, 9], [93765], .contexts [
        ⟨80880, true, false, [], [9]⟩,
        ⟨46, false, false, [93765], []⟩,
        ⟨80881, false, false, [], []⟩
      ]⟩,
    ⟨[93769], [93767, 11], .source 46949⟩,
    ⟨[93767, 11], [93769], .contexts [
        ⟨80883, true, false, [], []⟩
      ]⟩,
    ⟨[93767], [93767], .contexts []⟩,
    ⟨[93769, 11], [93767], .contexts [
        ⟨80884, true, false, [], [11]⟩,
        ⟨53, false, false, [93767], []⟩,
        ⟨80885, false, false, [], []⟩
      ]⟩,
    ⟨[93771], [93769, 1], .source 46950⟩,
    ⟨[93769], [93769], .contexts []⟩,
    ⟨[93771, 1], [93769], .contexts [
        ⟨80887, false, false, [], [1]⟩,
        ⟨8, false, false, [93769], []⟩,
        ⟨80888, false, false, [], []⟩
      ]⟩,
    ⟨[93773], [93771, 13], .source 46951⟩,
    ⟨[93771, 13], [93773], .contexts [
        ⟨80890, true, false, [], []⟩
      ]⟩,
    ⟨[93771], [93771], .contexts []⟩,
    ⟨[93773, 13], [93771], .contexts [
        ⟨80891, true, false, [], [13]⟩,
        ⟨59, false, false, [93771], []⟩,
        ⟨80892, false, false, [], []⟩
      ]⟩,
    ⟨[93775], [93773, 15], .source 46952⟩,
    ⟨[93773, 15], [93775], .contexts [
        ⟨80894, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1264. -/
def y322TCIndexRaw1264 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93773], [93773], .contexts []⟩,
    ⟨[93775, 15], [93773], .contexts [
        ⟨80895, true, false, [], [15]⟩,
        ⟨1, false, false, [93773], []⟩,
        ⟨80896, false, false, [], []⟩
      ]⟩,
    ⟨[93777], [93775, 1], .source 46953⟩,
    ⟨[93775, 1], [93777], .contexts [
        ⟨80898, true, false, [], []⟩
      ]⟩,
    ⟨[93775], [93775], .contexts []⟩,
    ⟨[93777, 1], [93775], .contexts [
        ⟨80899, true, false, [], [1]⟩,
        ⟨8, false, false, [93775], []⟩,
        ⟨80900, false, false, [], []⟩
      ]⟩,
    ⟨[93779], [93777, 3], .source 46954⟩,
    ⟨[93777, 3], [93779], .contexts [
        ⟨80902, true, false, [], []⟩
      ]⟩,
    ⟨[93777], [93777], .contexts []⟩,
    ⟨[93779, 3], [93777], .contexts [
        ⟨80903, true, false, [], [3]⟩,
        ⟨20, false, false, [93777], []⟩,
        ⟨80904, false, false, [], []⟩
      ]⟩,
    ⟨[93781], [93779, 5], .source 46955⟩,
    ⟨[93779, 5], [93781], .contexts [
        ⟨80906, true, false, [], []⟩
      ]⟩,
    ⟨[93779], [93779], .contexts []⟩,
    ⟨[93781, 5], [93779], .contexts [
        ⟨80907, true, false, [], [5]⟩,
        ⟨28, false, false, [93779], []⟩,
        ⟨80908, false, false, [], []⟩
      ]⟩,
    ⟨[93783], [93781, 1], .source 46956⟩,
    ⟨[93781], [93781], .contexts []⟩,
    ⟨[93785], [93783, 9], .source 46957⟩,
    ⟨[93783, 9], [93785], .contexts [
        ⟨80912, true, false, [], []⟩
      ]⟩,
    ⟨[93783], [93783], .contexts []⟩,
    ⟨[93785, 9], [93783], .contexts [
        ⟨80913, true, false, [], [9]⟩,
        ⟨46, false, false, [93783], []⟩,
        ⟨80914, false, false, [], []⟩
      ]⟩,
    ⟨[93787], [93785, 11], .source 46958⟩,
    ⟨[93785, 11], [93787], .contexts [
        ⟨80916, true, false, [], []⟩
      ]⟩,
    ⟨[93785], [93785], .contexts []⟩,
    ⟨[93787, 11], [93785], .contexts [
        ⟨80917, true, false, [], [11]⟩,
        ⟨53, false, false, [93785], []⟩,
        ⟨80918, false, false, [], []⟩
      ]⟩,
    ⟨[93789], [93787, 1], .source 46959⟩,
    ⟨[93787], [93787], .contexts []⟩,
    ⟨[93789, 1], [93787], .contexts [
        ⟨80920, false, false, [], [1]⟩,
        ⟨8, false, false, [93787], []⟩,
        ⟨80921, false, false, [], []⟩
      ]⟩,
    ⟨[93791], [93789, 13], .source 46960⟩,
    ⟨[93789, 13], [93791], .contexts [
        ⟨80923, true, false, [], []⟩
      ]⟩,
    ⟨[93789], [93789], .contexts []⟩,
    ⟨[93791, 13], [93789], .contexts [
        ⟨80924, true, false, [], [13]⟩,
        ⟨59, false, false, [93789], []⟩,
        ⟨80925, false, false, [], []⟩
      ]⟩,
    ⟨[93793], [93791, 15], .source 46961⟩,
    ⟨[93791, 15], [93793], .contexts [
        ⟨80927, true, false, [], []⟩
      ]⟩,
    ⟨[93791], [93791], .contexts []⟩,
    ⟨[93793, 15], [93791], .contexts [
        ⟨80928, true, false, [], [15]⟩,
        ⟨1, false, false, [93791], []⟩,
        ⟨80929, false, false, [], []⟩
      ]⟩,
    ⟨[93795], [93793, 1], .source 46962⟩,
    ⟨[93793, 1], [93795], .contexts [
        ⟨80931, true, false, [], []⟩
      ]⟩,
    ⟨[93793], [93793], .contexts []⟩,
    ⟨[93795, 1], [93793], .contexts [
        ⟨80932, true, false, [], [1]⟩,
        ⟨8, false, false, [93793], []⟩,
        ⟨80933, false, false, [], []⟩
      ]⟩,
    ⟨[93797], [93795, 3], .source 46963⟩,
    ⟨[93795, 3], [93797], .contexts [
        ⟨80935, true, false, [], []⟩
      ]⟩,
    ⟨[93795], [93795], .contexts []⟩,
    ⟨[93797, 3], [93795], .contexts [
        ⟨80936, true, false, [], [3]⟩,
        ⟨20, false, false, [93795], []⟩,
        ⟨80937, false, false, [], []⟩
      ]⟩,
    ⟨[93799], [93797, 5], .source 46964⟩,
    ⟨[93797, 5], [93799], .contexts [
        ⟨80939, true, false, [], []⟩
      ]⟩,
    ⟨[93797], [93797], .contexts []⟩,
    ⟨[93799, 5], [93797], .contexts [
        ⟨80940, true, false, [], [5]⟩,
        ⟨28, false, false, [93797], []⟩,
        ⟨80941, false, false, [], []⟩
      ]⟩,
    ⟨[93801], [93799, 1], .source 46965⟩,
    ⟨[93799, 1], [93801], .contexts [
        ⟨80943, true, false, [], []⟩
      ]⟩,
    ⟨[93799], [93799], .contexts []⟩,
    ⟨[93801, 1], [93799], .contexts [
        ⟨80944, true, false, [], [1]⟩,
        ⟨8, false, false, [93799], []⟩,
        ⟨80945, false, false, [], []⟩
      ]⟩,
    ⟨[93803], [93801, 9], .source 46966⟩,
    ⟨[93801, 9], [93803], .contexts [
        ⟨80947, true, false, [], []⟩
      ]⟩,
    ⟨[93801], [93801], .contexts []⟩,
    ⟨[93803, 9], [93801], .contexts [
        ⟨80948, true, false, [], [9]⟩,
        ⟨46, false, false, [93801], []⟩,
        ⟨80949, false, false, [], []⟩
      ]⟩,
    ⟨[93805], [93803, 11], .source 46967⟩,
    ⟨[93803], [93803], .contexts []⟩,
    ⟨[93805, 11], [93803], .contexts [
        ⟨80951, false, false, [], [11]⟩,
        ⟨53, false, false, [93803], []⟩,
        ⟨80952, false, false, [], []⟩
      ]⟩,
    ⟨[93807], [93805, 1], .source 46968⟩,
    ⟨[93805], [93805], .contexts []⟩,
    ⟨[93807, 1], [93805], .contexts [
        ⟨80954, false, false, [], [1]⟩,
        ⟨8, false, false, [93805], []⟩,
        ⟨80955, false, false, [], []⟩
      ]⟩,
    ⟨[93809], [93807, 13], .source 46969⟩,
    ⟨[93807, 13], [93809], .contexts [
        ⟨80957, true, false, [], []⟩
      ]⟩,
    ⟨[93809, 13], [93807], .contexts [
        ⟨80958, true, false, [], [13]⟩,
        ⟨59, false, false, [93807], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1265. -/
def y322TCIndexRaw1265 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93809], [93809], .contexts []⟩,
    ⟨[93809], [93809], .contexts []⟩,
    ⟨[93805], [93805], .contexts []⟩,
    ⟨[93803], [93803], .contexts []⟩,
    ⟨[93801], [93801], .contexts []⟩,
    ⟨[93801, 1], [93799], .contexts [
        ⟨80946, false, false, [], []⟩
      ]⟩,
    ⟨[93799], [93799], .contexts []⟩,
    ⟨[93807, 1, 11, 9, 1, 5], [93797], .contexts [
        ⟨80956, false, false, [], [11, 9, 1, 5]⟩,
        ⟨80962, false, false, [], [11, 9, 1, 5]⟩,
        ⟨80955, false, false, [], [11, 9, 1, 5]⟩,
        ⟨80955, false, false, [], [11, 9, 1, 5]⟩,
        ⟨80953, false, false, [], [9, 1, 5]⟩,
        ⟨80963, false, false, [], [9, 1, 5]⟩,
        ⟨80952, false, false, [], [9, 1, 5]⟩,
        ⟨80952, false, false, [], [9, 1, 5]⟩,
        ⟨80950, false, false, [], [1, 5]⟩,
        ⟨80964, false, false, [], [1, 5]⟩,
        ⟨80949, false, false, [], [1, 5]⟩,
        ⟨80949, false, false, [], [1, 5]⟩,
        ⟨80965, false, false, [], [5]⟩,
        ⟨80966, false, false, [], [5]⟩,
        ⟨80945, false, false, [], [5]⟩,
        ⟨80945, false, false, [], [5]⟩,
        ⟨80942, false, false, [], []⟩,
        ⟨80941, false, false, [], []⟩,
        ⟨80941, false, false, [], []⟩
      ]⟩,
    ⟨[93797, 3], [93795], .contexts [
        ⟨80938, false, false, [], []⟩
      ]⟩,
    ⟨[93795], [93795], .contexts []⟩,
    ⟨[93791], [93791], .contexts []⟩,
    ⟨[93787], [93787], .contexts []⟩,
    ⟨[93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1], [93787], .contexts [
        ⟨80967, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨80968, false, false, [], [1, 15, 13, 1]⟩,
        ⟨80969, false, false, [], [1, 15, 13, 1]⟩,
        ⟨80937, false, false, [], [1, 15, 13, 1]⟩,
        ⟨80937, false, false, [], [1, 15, 13, 1]⟩,
        ⟨80934, false, false, [], [15, 13, 1]⟩,
        ⟨80933, false, false, [], [15, 13, 1]⟩,
        ⟨80933, false, false, [], [15, 13, 1]⟩,
        ⟨80930, false, false, [], [13, 1]⟩,
        ⟨80970, false, false, [], [13, 1]⟩,
        ⟨80929, false, false, [], [13, 1]⟩,
        ⟨80929, false, false, [], [13, 1]⟩,
        ⟨80926, false, false, [], [1]⟩,
        ⟨80925, false, false, [], [1]⟩,
        ⟨80925, false, false, [], [1]⟩,
        ⟨80922, false, false, [], []⟩,
        ⟨80971, false, false, [], []⟩,
        ⟨80921, false, false, [], []⟩,
        ⟨80921, false, false, [], []⟩
      ]⟩,
    ⟨[93785], [93785], .contexts []⟩,
    ⟨[93785, 9], [93783], .contexts [
        ⟨80915, false, false, [], []⟩
      ]⟩,
    ⟨[93783], [93783], .contexts []⟩,
    ⟨[93783, 1], [93781], .contexts [
        ⟨80910, false, false, [], [1]⟩,
        ⟨8, false, false, [93781], []⟩,
        ⟨80911, false, false, [], []⟩
      ]⟩,
    ⟨[93781], [93781], .contexts []⟩,
    ⟨[93781, 5], [93779], .contexts [
        ⟨80909, false, false, [], []⟩
      ]⟩,
    ⟨[93779], [93779], .contexts []⟩,
    ⟨[93779, 3], [93777], .contexts [
        ⟨80905, false, false, [], []⟩
      ]⟩,
    ⟨[93777], [93777], .contexts []⟩,
    ⟨[
      93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3
    ], [93777], .contexts [
        ⟨80972, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨80919, false, false, [], [9, 1, 5, 3]⟩,
        ⟨80973, false, false, [], [9, 1, 5, 3]⟩,
        ⟨80918, false, false, [], [9, 1, 5, 3]⟩,
        ⟨80918, false, false, [], [9, 1, 5, 3]⟩,
        ⟨80974, false, false, [], [1, 5, 3]⟩,
        ⟨80975, false, false, [], [1, 5, 3]⟩,
        ⟨80914, false, false, [], [1, 5, 3]⟩,
        ⟨80914, false, false, [], [1, 5, 3]⟩,
        ⟨80976, false, false, [], [5, 3]⟩,
        ⟨80977, false, false, [], [5, 3]⟩,
        ⟨80911, false, false, [], [5, 3]⟩,
        ⟨80911, false, false, [], [5, 3]⟩,
        ⟨80978, false, false, [], [3]⟩,
        ⟨80979, false, false, [], [3]⟩,
        ⟨80908, false, false, [], [3]⟩,
        ⟨80908, false, false, [], [3]⟩,
        ⟨80980, false, false, [], []⟩,
        ⟨80981, false, false, [], []⟩,
        ⟨80904, false, false, [], []⟩,
        ⟨80904, false, false, [], []⟩
      ]⟩,
    ⟨[93775], [93775], .contexts []⟩,
    ⟨[93771], [93771], .contexts []⟩,
    ⟨[93769], [93769], .contexts []⟩,
    ⟨[93767], [93767], .contexts []⟩,
    ⟨[
      93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [93767], .contexts [
        ⟨80982, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨80901, false, false, [], [15, 13, 1, 11]⟩,
        ⟨80983, false, false, [], [15, 13, 1, 11]⟩,
        ⟨80900, false, false, [], [15, 13, 1, 11]⟩,
        ⟨80900, false, false, [], [15, 13, 1, 11]⟩,
        ⟨80897, false, false, [], [13, 1, 11]⟩,
        ⟨80896, false, false, [], [13, 1, 11]⟩,
        ⟨80896, false, false, [], [13, 1, 11]⟩,
        ⟨80893, false, false, [], [1, 11]⟩,
        ⟨80984, false, false, [], [1, 11]⟩,
        ⟨80892, false, false, [], [1, 11]⟩,
        ⟨80892, false, false, [], [1, 11]⟩,
        ⟨80889, false, false, [], [11]⟩,
        ⟨80985, false, false, [], [11]⟩,
        ⟨80888, false, false, [], [11]⟩,
        ⟨80888, false, false, [], [11]⟩,
        ⟨80886, false, false, [], []⟩,
        ⟨80986, false, false, [], []⟩,
        ⟨80885, false, false, [], []⟩,
        ⟨80885, false, false, [], []⟩
      ]⟩,
    ⟨[93765], [93765], .contexts []⟩,
    ⟨[93765, 1], [93763], .contexts [
        ⟨80878, false, false, [], []⟩
      ]⟩,
    ⟨[93763], [93763], .contexts []⟩,
    ⟨[93759], [93759], .contexts []⟩,
    ⟨[93757], [93757], .contexts []⟩,
    ⟨[
      93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1
    ], [93757], .contexts [
        ⟨80987, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨80882, false, false, [], [1, 5, 3, 1]⟩,
        ⟨80988, false, false, [], [1, 5, 3, 1]⟩,
        ⟨80881, false, false, [], [1, 5, 3, 1]⟩,
        ⟨80881, false, false, [], [1, 5, 3, 1]⟩,
        ⟨80989, false, false, [], [5, 3, 1]⟩,
        ⟨80990, false, false, [], [5, 3, 1]⟩,
        ⟨80877, false, false, [], [5, 3, 1]⟩,
        ⟨80877, false, false, [], [5, 3, 1]⟩,
        ⟨80874, false, false, [], [3, 1]⟩,
        ⟨80873, false, false, [], [3, 1]⟩,
        ⟨80873, false, false, [], [3, 1]⟩,
        ⟨80870, false, false, [], [1]⟩,
        ⟨80991, false, false, [], [1]⟩,
        ⟨80869, false, false, [], [1]⟩,
        ⟨80869, false, false, [], [1]⟩,
        ⟨80867, false, false, [], []⟩,
        ⟨80992, false, false, [], []⟩,
        ⟨80866, false, false, [], []⟩,
        ⟨80866, false, false, [], []⟩
      ]⟩,
    ⟨[93755], [93755], .contexts []⟩,
    ⟨[93753], [93753], .contexts []⟩,
    ⟨[93751], [93751], .contexts []⟩,
    ⟨[93749], [93749], .contexts []⟩,
    ⟨[93747], [93747], .contexts []⟩,
    ⟨[
      93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9
    ], [93747], .contexts [
        ⟨80993, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨80864, false, false, [], [13, 1, 11, 9]⟩,
        ⟨80994, false, false, [], [13, 1, 11, 9]⟩,
        ⟨80863, false, false, [], [13, 1, 11, 9]⟩,
        ⟨80863, false, false, [], [13, 1, 11, 9]⟩,
        ⟨80861, false, false, [], [1, 11, 9]⟩,
        ⟨80995, false, false, [], [1, 11, 9]⟩,
        ⟨80860, false, false, [], [1, 11, 9]⟩,
        ⟨80860, false, false, [], [1, 11, 9]⟩,
        ⟨80858, false, false, [], [11, 9]⟩,
        ⟨80996, false, false, [], [11, 9]⟩,
        ⟨80857, false, false, [], [11, 9]⟩,
        ⟨80857, false, false, [], [11, 9]⟩,
        ⟨80855, false, false, [], [9]⟩,
        ⟨80997, false, false, [], [9]⟩,
        ⟨80854, false, false, [], [9]⟩,
        ⟨80854, false, false, [], [9]⟩,
        ⟨80852, false, false, [], []⟩,
        ⟨80998, false, false, [], []⟩,
        ⟨80851, false, false, [], []⟩,
        ⟨80851, false, false, [], []⟩
      ]⟩,
    ⟨[93745], [93745], .contexts []⟩,
    ⟨[93743], [93743], .contexts []⟩,
    ⟨[93741], [93741], .contexts []⟩,
    ⟨[93739], [93739], .contexts []⟩,
    ⟨[93737], [93737], .contexts []⟩,
    ⟨[
      93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [93737], .contexts [
        ⟨80999, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨80849, false, false, [], [5, 3, 1, 15]⟩,
        ⟨81000, false, false, [], [5, 3, 1, 15]⟩,
        ⟨80848, false, false, [], [5, 3, 1, 15]⟩,
        ⟨80848, false, false, [], [5, 3, 1, 15]⟩,
        ⟨80846, false, false, [], [3, 1, 15]⟩,
        ⟨81001, false, false, [], [3, 1, 15]⟩,
        ⟨80845, false, false, [], [3, 1, 15]⟩,
        ⟨80845, false, false, [], [3, 1, 15]⟩,
        ⟨80843, false, false, [], [1, 15]⟩,
        ⟨81002, false, false, [], [1, 15]⟩,
        ⟨80842, false, false, [], [1, 15]⟩,
        ⟨80842, false, false, [], [1, 15]⟩,
        ⟨80840, false, false, [], [15]⟩,
        ⟨81003, false, false, [], [15]⟩,
        ⟨80839, false, false, [], [15]⟩,
        ⟨80839, false, false, [], [15]⟩,
        ⟨80837, false, false, [], []⟩,
        ⟨81004, false, false, [], []⟩,
        ⟨80836, false, false, [], []⟩,
        ⟨80836, false, false, [], []⟩
      ]⟩,
    ⟨[93733], [93733], .contexts []⟩,
    ⟨[93731], [93731], .contexts []⟩,
    ⟨[93729], [93729], .contexts []⟩,
    ⟨[93727], [93727], .contexts []⟩,
    ⟨[
      93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1
    ], [93727], .contexts [
        ⟨81005, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨80834, false, false, [], [1, 11, 9, 1]⟩,
        ⟨80833, false, false, [], [1, 11, 9, 1]⟩,
        ⟨80833, false, false, [], [1, 11, 9, 1]⟩,
        ⟨80830, false, false, [], [11, 9, 1]⟩,
        ⟨81006, false, false, [], [11, 9, 1]⟩,
        ⟨80829, false, false, [], [11, 9, 1]⟩,
        ⟨80829, false, false, [], [11, 9, 1]⟩,
        ⟨80826, true, false, [], [11, 9, 1]⟩,
        ⟨53, false, false, [93731], [9, 1]⟩,
        ⟨80827, false, false, [], [9, 1]⟩,
        ⟨81007, false, false, [], [9, 1]⟩,
        ⟨80827, false, false, [], [9, 1]⟩,
        ⟨80827, false, false, [], [9, 1]⟩,
        ⟨80824, false, false, [], [1]⟩,
        ⟨81008, false, false, [], [1]⟩,
        ⟨80823, false, false, [], [1]⟩,
        ⟨80823, false, false, [], [1]⟩,
        ⟨80819, true, false, [], [1]⟩,
        ⟨8, false, false, [93727], []⟩,
        ⟨80820, false, false, [], []⟩,
        ⟨81009, false, false, [], []⟩,
        ⟨80820, false, false, [], []⟩,
        ⟨80820, false, false, [], []⟩
      ]⟩,
    ⟨[93725], [93725], .contexts []⟩,
    ⟨[93723], [93723], .contexts []⟩,
    ⟨[93721], [93721], .contexts []⟩,
    ⟨[93719], [93719], .contexts []⟩,
    ⟨[93717], [93717], .contexts []⟩,
    ⟨[
      93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [93717], .contexts [
        ⟨81010, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨80817, false, false, [], [3, 1, 15, 13]⟩,
        ⟨81011, false, false, [], [3, 1, 15, 13]⟩,
        ⟨80816, false, false, [], [3, 1, 15, 13]⟩,
        ⟨80816, false, false, [], [3, 1, 15, 13]⟩,
        ⟨80812, true, false, [], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [93723], [1, 15, 13]⟩,
        ⟨80813, false, false, [], [1, 15, 13]⟩,
        ⟨81012, false, false, [], [1, 15, 13]⟩,
        ⟨80813, false, false, [], [1, 15, 13]⟩,
        ⟨80813, false, false, [], [1, 15, 13]⟩,
        ⟨80809, true, false, [], [1, 15, 13]⟩,
        ⟨8, false, false, [93721], [15, 13]⟩,
        ⟨80810, false, false, [], [15, 13]⟩,
        ⟨81013, false, false, [], [15, 13]⟩,
        ⟨80810, false, false, [], [15, 13]⟩,
        ⟨80810, false, false, [], [15, 13]⟩,
        ⟨80806, true, false, [], [15, 13]⟩,
        ⟨1, false, false, [93719], [13]⟩,
        ⟨80807, false, false, [], [13]⟩,
        ⟨81014, false, false, [], [13]⟩,
        ⟨80807, false, false, [], [13]⟩,
        ⟨80807, false, false, [], [13]⟩,
        ⟨80803, true, false, [], [13]⟩,
        ⟨59, false, false, [93717], []⟩,
        ⟨80804, false, false, [], []⟩,
        ⟨81015, false, false, [], []⟩,
        ⟨80804, false, false, [], []⟩,
        ⟨80804, false, false, [], []⟩
      ]⟩,
    ⟨[93715], [93715], .contexts []⟩,
    ⟨[93713], [93713], .contexts []⟩,
    ⟨[93711], [93711], .contexts []⟩,
    ⟨[93709], [93709], .contexts []⟩,
    ⟨[
      93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1
    ], [93709], .contexts [
        ⟨81016, false, false, [], [1, 11, 9, 1]⟩,
        ⟨80800, true, false, [], [1, 11, 9, 1]⟩,
        ⟨8, false, false, [93715], [11, 9, 1]⟩,
        ⟨80801, false, false, [], [11, 9, 1]⟩,
        ⟨81017, false, false, [], [11, 9, 1]⟩,
        ⟨80801, false, false, [], [11, 9, 1]⟩,
        ⟨80801, false, false, [], [11, 9, 1]⟩,
        ⟨80797, true, false, [], [11, 9, 1]⟩,
        ⟨53, false, false, [93713], [9, 1]⟩,
        ⟨80798, false, false, [], [9, 1]⟩,
        ⟨81018, false, false, [], [9, 1]⟩,
        ⟨80798, false, false, [], [9, 1]⟩,
        ⟨80798, false, false, [], [9, 1]⟩,
        ⟨80794, true, false, [], [9, 1]⟩,
        ⟨46, false, false, [93711], [1]⟩,
        ⟨80795, false, false, [], [1]⟩,
        ⟨81019, false, false, [], [1]⟩,
        ⟨80795, false, false, [], [1]⟩,
        ⟨80795, false, false, [], [1]⟩,
        ⟨80791, true, false, [], [1]⟩,
        ⟨8, false, false, [93709], []⟩,
        ⟨80792, false, false, [], []⟩,
        ⟨81020, false, false, [], []⟩,
        ⟨80792, false, false, [], []⟩,
        ⟨80792, false, false, [], []⟩
      ]⟩,
    ⟨[93707], [93707], .contexts []⟩,
    ⟨[93703], [93703], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1266. -/
def y322TCIndexRaw1266 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93701], [93701], .contexts []⟩,
    ⟨[
      93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15
    ], [93701], .contexts [
        ⟨81021, false, false, [], [5, 3, 1, 15]⟩,
        ⟨80788, true, false, [], [5, 3, 1, 15]⟩,
        ⟨28, false, false, [93707], [3, 1, 15]⟩,
        ⟨80789, false, false, [], [3, 1, 15]⟩,
        ⟨81022, false, false, [], [3, 1, 15]⟩,
        ⟨80789, false, false, [], [3, 1, 15]⟩,
        ⟨80789, false, false, [], [3, 1, 15]⟩,
        ⟨80785, true, false, [], [3, 1, 15]⟩,
        ⟨20, false, false, [93705], [1, 15]⟩,
        ⟨80786, false, false, [], [1, 15]⟩,
        ⟨80786, false, false, [], [1, 15]⟩,
        ⟨80786, false, false, [], [1, 15]⟩,
        ⟨80783, false, false, [], [15]⟩,
        ⟨81023, false, false, [], [15]⟩,
        ⟨80782, false, false, [], [15]⟩,
        ⟨80782, false, false, [], [15]⟩,
        ⟨80779, false, false, [], []⟩,
        ⟨81024, false, false, [], []⟩,
        ⟨80778, false, false, [], []⟩,
        ⟨80778, false, false, [], []⟩
      ]⟩,
    ⟨[93699], [93699], .contexts []⟩,
    ⟨[93697], [93697], .contexts []⟩,
    ⟨[93695], [93695], .contexts []⟩,
    ⟨[
      93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [93691], .contexts [
        ⟨81025, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨80775, false, false, [], [1, 11, 9, 1]⟩,
        ⟨81026, false, false, [], [1, 11, 9, 1]⟩,
        ⟨80774, false, false, [], [1, 11, 9, 1]⟩,
        ⟨80774, false, false, [], [1, 11, 9, 1]⟩,
        ⟨80770, true, false, [], [1, 11, 9, 1]⟩,
        ⟨8, false, false, [93697], [11, 9, 1]⟩,
        ⟨80771, false, false, [], [11, 9, 1]⟩,
        ⟨81027, false, false, [], [11, 9, 1]⟩,
        ⟨80771, false, false, [], [11, 9, 1]⟩,
        ⟨80771, false, false, [], [11, 9, 1]⟩,
        ⟨80767, true, false, [], [11, 9, 1]⟩,
        ⟨53, false, false, [93695], [9, 1]⟩,
        ⟨80768, false, false, [], [9, 1]⟩,
        ⟨81028, false, false, [], [9, 1]⟩,
        ⟨80768, false, false, [], [9, 1]⟩,
        ⟨80768, false, false, [], [9, 1]⟩,
        ⟨80765, false, false, [], [1]⟩,
        ⟨80764, false, false, [], [1]⟩,
        ⟨80764, false, false, [], [1]⟩,
        ⟨80761, false, false, [], []⟩,
        ⟨80755, false, false, [], []⟩,
        ⟨80756, false, false, [], []⟩,
        ⟨80756, false, false, [], []⟩
      ]⟩,
    ⟨[93689], [93689], .contexts []⟩,
    ⟨[
      93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15
    ], [93683], .contexts [
        ⟨81029, false, false, [], [5, 3, 1, 15]⟩,
        ⟨80753, true, false, [], [5, 3, 1, 15]⟩,
        ⟨28, false, false, [93689], [3, 1, 15]⟩,
        ⟨80754, false, false, [], [3, 1, 15]⟩,
        ⟨81030, false, false, [], [3, 1, 15]⟩,
        ⟨80754, false, false, [], [3, 1, 15]⟩,
        ⟨80754, false, false, [], [3, 1, 15]⟩,
        ⟨80757, false, false, [], [1, 15]⟩,
        ⟨80745, false, false, [], [1, 15]⟩,
        ⟨80746, false, false, [], [1, 15]⟩,
        ⟨80746, false, false, [], [1, 15]⟩,
        ⟨80744, true, false, [], [1, 15]⟩,
        ⟨8, false, false, [93685], [15]⟩,
        ⟨80735, false, false, [], [15]⟩,
        ⟨80734, false, false, [], [15]⟩,
        ⟨80735, false, false, [], [15]⟩,
        ⟨80735, false, false, [], [15]⟩,
        ⟨80733, true, false, [], [15]⟩,
        ⟨1, false, false, [93683], []⟩,
        ⟨80724, false, false, [], []⟩,
        ⟨80723, false, false, [], []⟩,
        ⟨80724, false, false, [], []⟩,
        ⟨80724, false, false, [], []⟩
      ]⟩,
    ⟨[
      93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1
    ], [93677], .contexts [
        ⟨81031, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨80722, false, false, [], [1, 11, 9, 1]⟩,
        ⟨44807, false, false, [], [1, 11, 9, 1]⟩,
        ⟨44808, false, false, [], [1, 11, 9, 1]⟩,
        ⟨44808, false, false, [], [1, 11, 9, 1]⟩,
        ⟨44822, false, false, [], [11, 9, 1]⟩,
        ⟨44823, false, false, [], [11, 9, 1]⟩,
        ⟨44824, false, false, [], [11, 9, 1]⟩,
        ⟨44824, false, false, [], [11, 9, 1]⟩,
        ⟨80718, false, false, [], [9, 1]⟩,
        ⟨80704, false, false, [], [9, 1]⟩,
        ⟨80705, false, false, [], [9, 1]⟩,
        ⟨80705, false, false, [], [9, 1]⟩,
        ⟨80703, false, false, [], [1]⟩,
        ⟨80678, false, false, [], [1]⟩,
        ⟨80679, false, false, [], [1]⟩,
        ⟨80679, false, false, [], [1]⟩,
        ⟨80707, false, false, [], []⟩,
        ⟨80653, false, false, [], []⟩,
        ⟨80654, false, false, [], []⟩,
        ⟨80654, false, false, [], []⟩
      ]⟩,
    ⟨[30505], [30491, 11247], .source 15317⟩,
    ⟨[30507], [30505, 3035], .source 15318⟩,
    ⟨[30509], [30507, 17059], .source 15319⟩,
    ⟨[
      93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13
    ], [30509, 84353], .contexts [
        ⟨81032, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨80687, false, false, [], [3, 1, 15, 13]⟩,
        ⟨80660, false, false, [], [3, 1, 15, 13]⟩,
        ⟨80661, false, false, [], [3, 1, 15, 13]⟩,
        ⟨80661, false, false, [], [3, 1, 15, 13]⟩,
        ⟨80652, false, false, [30491], [1, 15, 13]⟩,
        ⟨26311, false, false, [30491], [15, 13]⟩,
        ⟨81033, true, false, [], [84359, 15, 13]⟩,
        ⟨26272, false, false, [30505], [13]⟩,
        ⟨81034, true, false, [], [84359, 13]⟩,
        ⟨26269, false, false, [30507], []⟩,
        ⟨81035, true, false, [], [84353]⟩
      ]⟩,
    ⟨[30511], [30509, 4395], .source 15320⟩,
    ⟨[30513], [30511, 15133], .source 15321⟩,
    ⟨[30515], [30513, 16177], .source 15322⟩,
    ⟨[30517], [30515, 9191], .source 15323⟩,
    ⟨[
      93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5
    ], [30517, 79697], .contexts [
        ⟨81036, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨26177, false, false, [30509], [11, 9, 1, 5]⟩,
        ⟨81037, true, false, [], [84353, 11, 9, 1, 5]⟩,
        ⟨26190, false, false, [30511], [9, 1, 5]⟩,
        ⟨81038, true, false, [], [84353, 9, 1, 5]⟩,
        ⟨26186, false, false, [30513], [1, 5]⟩,
        ⟨81039, true, false, [], [82311, 1, 5]⟩,
        ⟨10113, false, false, [30515], [5]⟩,
        ⟨12009, false, false, [30515], [5]⟩,
        ⟨81040, true, false, [], [79699, 5]⟩,
        ⟨7066, false, false, [30517], []⟩
      ]⟩,
    ⟨[30519], [30517, 2373], .source 15324⟩,
    ⟨[30521], [30519, 9193], .source 15325⟩,
    ⟨[30523], [30521, 12843], .source 15326⟩,
    ⟨[30525], [30523, 2021], .source 15327⟩,
    ⟨[
      93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [30525, 79889], .contexts [
        ⟨81041, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨7056, false, false, [30517], [1, 15, 13, 1]⟩,
        ⟨81042, true, false, [], [79697, 1, 15, 13, 1]⟩,
        ⟨12018, false, false, [30519], [15, 13, 1]⟩,
        ⟨81043, true, false, [], [80263, 15, 13, 1]⟩,
        ⟨7787, false, false, [30521], [13, 1]⟩,
        ⟨13788, false, false, [30521], [13, 1]⟩,
        ⟨81044, true, false, [], [79911, 13, 1]⟩,
        ⟨7496, false, false, [30523], [1]⟩,
        ⟨81045, true, false, [], [79911, 1]⟩,
        ⟨7491, false, false, [30525], []⟩
      ]⟩,
    ⟨[30527], [30525, 9193], .source 15328⟩,
    ⟨[30529], [30527, 9215], .source 15329⟩,
    ⟨[30531], [30529, 4217], .source 15330⟩,
    ⟨[
      93807, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3
    ], [30531, 87465], .contexts [
        ⟨81046, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨12036, false, false, [30525], [9, 1, 5, 3]⟩,
        ⟨81047, true, false, [], [80429, 9, 1, 5, 3]⟩,
        ⟨12059, false, false, [30527], [1, 5, 3]⟩,
        ⟨81048, true, false, [], [80801, 1, 5, 3]⟩,
        ⟨8258, false, false, [30529], [5, 3]⟩,
        ⟨81049, true, false, [], [80801, 5, 3]⟩,
        ⟨24090, false, false, [30531], [3]⟩,
        ⟨43707, false, false, [30531], []⟩
      ]⟩,
    ⟨[30531, 87467], [30531, 87467], .contexts []⟩,
    ⟨[30531, 87467], [30531, 87467], .contexts []⟩,
    ⟨[93809, 15], [93809, 15], .contexts []⟩,
    ⟨[93809, 15], [30531, 87467], .contexts [
        ⟨81053, false, false, [], []⟩,
        ⟨80961, true, false, [], [15]⟩,
        ⟨80961, true, false, [], [15]⟩,
        ⟨80960, true, false, [], [15]⟩,
        ⟨80958, true, false, [], [15]⟩,
        ⟨2277, false, false, [93807], []⟩,
        ⟨2278, false, false, [93807], []⟩,
        ⟨81050, false, false, [], [1]⟩,
        ⟨43728, false, false, [30531], []⟩,
        ⟨81051, false, false, [], []⟩,
        ⟨81052, false, false, [], []⟩,
        ⟨43736, false, false, [30531], []⟩,
        ⟨13, true, false, [], [30531, 87467]⟩
      ]⟩,
    ⟨[30533], [30530], .source 15331⟩,
    ⟨[87467, 15], [30533, 93809], .contexts [
        ⟨81054, true, false, [30530], [15]⟩,
        ⟨1, false, false, [30530, 93809], []⟩,
        ⟨81055, true, false, [], [93809]⟩
      ]⟩,
    ⟨[93809, 15], [30531, 87467], .contexts [
        ⟨81053, false, false, [], []⟩,
        ⟨81054, false, false, [], []⟩,
        ⟨81051, false, false, [], []⟩,
        ⟨81052, false, false, [], []⟩,
        ⟨81052, false, false, [], []⟩
      ]⟩,
    ⟨[30539], [30531, 4217], .source 15334⟩,
    ⟨[30541], [30539, 30533], .source 15335⟩,
    ⟨[93809], [93809], .contexts []⟩,
    ⟨[93809], [93809], .contexts []⟩,
    ⟨[30543], [30540], .source 15336⟩,
    ⟨[30540], [30540], .contexts []⟩,
    ⟨[30545], [30531, 2375], .source 15337⟩,
    ⟨[30547], [30545, 30533], .source 15338⟩,
    ⟨[30549], [30546], .source 15339⟩,
    ⟨[30546], [30546], .contexts []⟩,
    ⟨[30551], [30531, 27229], .source 15340⟩,
    ⟨[30553], [30551, 27231], .source 15341⟩,
    ⟨[83227, 7], [83227, 7], .contexts []⟩,
    ⟨[30555], [30552], .source 15342⟩,
    ⟨[30552], [30552], .contexts []⟩,
    ⟨[83227, 7], [30555, 93809], .contexts [
        ⟨81070, false, false, [], []⟩,
        ⟨81069, false, false, [30552], [83227, 7]⟩,
        ⟨69974, true, false, [30552, 30551], [7]⟩,
        ⟨69860, true, false, [30552, 30551], [7]⟩,
        ⟨81068, false, false, [30552], [92173, 15, 7]⟩,
        ⟨70022, true, false, [30552, 30531], [15, 7]⟩,
        ⟨81057, true, false, [30552], [7, 15, 7]⟩,
        ⟨2651, false, false, [30552, 93809], []⟩,
        ⟨81060, false, false, [30552], []⟩,
        ⟨81061, false, false, [30552], []⟩,
        ⟨81072, true, false, [], [93809]⟩,
        ⟨81072, true, false, [], [93809]⟩,
        ⟨81071, true, false, [], [93809]⟩
      ]⟩,
    ⟨[30553], [30554], .contexts [
        ⟨81071, true, true, [], []⟩
      ]⟩,
    ⟨[30557], [30531, 15113], .source 15343⟩,
    ⟨[30559], [30557, 30533], .source 15344⟩,
    ⟨[30561], [30558], .source 15345⟩,
    ⟨[30558], [30558], .contexts []⟩,
    ⟨[30555, 93809], [30555, 93809], .contexts []⟩,
    ⟨[30555, 93809], [30555, 93809], .contexts []⟩,
    ⟨[16135, 89213], [16135, 89213], .contexts []⟩,
    ⟨[16135, 89213], [16135, 89213], .contexts []⟩,
    ⟨[30565], [30553, 16135], .source 15347⟩,
    ⟨[30569], [30564], .source 15349⟩,
    ⟨[25063, 90469], [30569, 93807], .contexts [
        ⟨60991, false, false, [], [90469]⟩,
        ⟨60962, true, false, [25045], []⟩,
        ⟨60951, true, false, [], []⟩,
        ⟨81083, false, false, [30564], [89213, 7]⟩,
        ⟨81074, false, false, [30564], [16135, 89213, 7]⟩,
        ⟨54897, true, false, [30564, 30554, 16135], [7]⟩,
        ⟨81082, true, false, [30564, 30554], [7]⟩,
        ⟨81082, true, false, [30564, 30554], [7]⟩,
        ⟨81081, true, false, [30564, 30554], [7]⟩,
        ⟨54904, true, false, [30564, 30554], [7]⟩,
        ⟨64, true, false, [30564, 30554, 83227], [7]⟩,
        ⟨518, true, false, [30564, 30554, 83227], [7]⟩,
        ⟨81070, false, false, [30564, 30554], [13, 7, 7]⟩,
        ⟨81073, false, false, [30564, 30554], [13, 7, 7]⟩,
        ⟨81079, false, false, [30564, 30554], [13, 7, 7]⟩,
        ⟨81080, false, false, [30564, 30554], [13, 7, 7]⟩,
        ⟨81080, false, false, [30564, 30554], [13, 7, 7]⟩,
        ⟨80959, false, false, [30564], [7, 7]⟩,
        ⟨38, false, false, [30564, 93807], []⟩,
        ⟨81084, true, false, [], [93807]⟩
      ]⟩,
    ⟨[30567], [25062], .source 15348⟩,
    ⟨[30571], [30567, 30569], .source 15350⟩]

/-- Exact literal claimed equations and contextual derivations, block 1267. -/
def y322TCIndexRaw1267 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[30573], [30570], .source 15351⟩,
    ⟨[93807], [30573, 90469], .contexts [
        ⟨81087, false, false, [30570], [93807]⟩,
        ⟨81086, false, false, [30570], [30569, 93807]⟩,
        ⟨81085, true, false, [30570, 25062], []⟩,
        ⟨81088, true, false, [], [90469]⟩
      ]⟩,
    ⟨[30572], [30572], .contexts []⟩,
    ⟨[93807], [30573, 90469], .contexts [
        ⟨81089, false, false, [], []⟩
      ]⟩,
    ⟨[30575], [30573, 25033], .source 15352⟩,
    ⟨[30577], [30574], .source 15353⟩,
    ⟨[30579], [30575, 25035], .source 15354⟩,
    ⟨[30579, 90473], [93803], .contexts [
        ⟨81094, false, false, [], [90473]⟩,
        ⟨60934, true, false, [30575], []⟩,
        ⟨81093, true, true, [], [90473, 11]⟩,
        ⟨81092, false, false, [30576, 30574], [90473, 11]⟩,
        ⟨60957, true, false, [30576, 30574, 30573], [11]⟩,
        ⟨81091, true, false, [30576, 30574], [1, 11]⟩,
        ⟨80956, false, false, [30576, 30574], [11]⟩,
        ⟨80962, false, false, [30576, 30574], [11]⟩,
        ⟨13, true, false, [30576, 30574], [93805, 11]⟩,
        ⟨81093, true, false, [30576], [93805, 11]⟩,
        ⟨80953, false, false, [], []⟩,
        ⟨80963, false, false, [], []⟩
      ]⟩,
    ⟨[30581], [30578], .source 15355⟩,
    ⟨[30581], [30578], .contexts [
        ⟨81096, false, false, [], []⟩
      ]⟩,
    ⟨[93803], [30579, 90473], .contexts [
        ⟨81097, false, false, [30580], [93803]⟩,
        ⟨13, false, false, [30580, 30578], [93803]⟩,
        ⟨81095, true, false, [30580, 30578], []⟩,
        ⟨81096, false, true, [], [90473]⟩
      ]⟩,
    ⟨[30578], [30578], .contexts []⟩,
    ⟨[90473, 9], [30581, 93801], .contexts [
        ⟨81098, true, false, [30578], [9]⟩,
        ⟨80950, false, false, [30578], []⟩,
        ⟨80964, false, false, [30578], []⟩,
        ⟨81099, true, false, [], [93801]⟩,
        ⟨81099, true, false, [], [93801]⟩,
        ⟨81097, true, false, [], [93801]⟩
      ]⟩,
    ⟨[30583], [25039, 30581], .source 15356⟩,
    ⟨[30581, 93801], [30581, 93801], .contexts []⟩,
    ⟨[90473, 9], [30581, 93801], .contexts [
        ⟨81100, false, false, [], []⟩,
        ⟨81102, false, false, [], []⟩,
        ⟨81102, false, false, [], []⟩
      ]⟩,
    ⟨[90473, 8], [90473, 9], .contexts [
        ⟨47, false, false, [90473], []⟩
      ]⟩,
    ⟨[93801, 15], [93801, 15], .contexts []⟩,
    ⟨[93801], [93801], .contexts []⟩,
    ⟨[30585], [30582], .source 15357⟩,
    ⟨[30587], [30585, 30581], .source 15358⟩,
    ⟨[93801, 15], [30587, 93801], .contexts [
        ⟨81105, false, false, [], []⟩,
        ⟨81101, false, false, [30582], [93801, 15]⟩,
        ⟨81100, true, false, [30582, 25039], [15]⟩,
        ⟨60937, true, false, [30582], [9, 15]⟩,
        ⟨1671, false, false, [30582, 90473], []⟩,
        ⟨81104, false, false, [30582], []⟩,
        ⟨81103, false, false, [30582], []⟩,
        ⟨81106, false, false, [30582, 30581], []⟩,
        ⟨81107, true, false, [], [30581, 93801]⟩,
        ⟨81108, true, false, [], [93801]⟩
      ]⟩,
    ⟨[30589], [25033, 30581], .source 15359⟩,
    ⟨[90463, 9], [90463, 9], .contexts []⟩,
    ⟨[93799], [93799], .contexts []⟩,
    ⟨[30591], [25073, 30589], .source 15360⟩,
    ⟨[90463, 9], [30591, 93799], .contexts [
        ⟨81111, false, false, [], []⟩,
        ⟨61030, true, false, [25058], [9]⟩,
        ⟨61030, true, false, [25058], [9]⟩,
        ⟨77839, true, false, [25058], [9]⟩,
        ⟨60723, true, false, [25058], [9]⟩,
        ⟨60970, true, false, [25058], [1, 9]⟩,
        ⟨1964, false, false, [25058, 90469], []⟩,
        ⟨693, false, false, [25058, 90469], []⟩,
        ⟨60956, false, false, [25058], [9, 1]⟩,
        ⟨78152, false, false, [25058], [9, 1]⟩,
        ⟨60931, false, false, [25058], [9, 1]⟩,
        ⟨60932, false, false, [25058], [9, 1]⟩,
        ⟨60932, false, false, [25058], [9, 1]⟩,
        ⟨81100, false, false, [25058, 25033], [1]⟩,
        ⟨81110, true, false, [25058], [93801, 1]⟩,
        ⟨80946, false, false, [25058, 30589], []⟩,
        ⟨81112, false, false, [25058, 30589], []⟩,
        ⟨61033, true, false, [], [30589, 93799]⟩,
        ⟨81113, true, false, [], [93799]⟩
      ]⟩,
    ⟨[30593], [30590], .source 15361⟩,
    ⟨[30595], [25043, 27241], .source 15362⟩,
    ⟨[30597], [30594], .source 15363⟩,
    ⟨[30599], [30597, 30581], .source 15364⟩,
    ⟨[92163, 7], [30599, 93801], .contexts [
        ⟨81116, false, false, [30594], [92163, 7]⟩,
        ⟨69991, true, false, [30594, 25043], [7]⟩,
        ⟨60920, true, false, [30594], [9, 7]⟩,
        ⟨60920, true, false, [30594], [9, 7]⟩,
        ⟨60919, true, false, [30594], [9, 7]⟩,
        ⟨60927, true, false, [30594], [9, 7]⟩,
        ⟨579, false, false, [30594, 90473], []⟩,
        ⟨81104, false, false, [30594], []⟩,
        ⟨81103, false, false, [30594], []⟩,
        ⟨81106, false, false, [30594, 30581], []⟩,
        ⟨81117, true, false, [], [30581, 93801]⟩,
        ⟨81118, true, false, [], [93801]⟩
      ]⟩,
    ⟨[30601], [30598], .source 15365⟩,
    ⟨[30603], [25007, 30581], .source 15366⟩,
    ⟨[30605], [30602], .source 15367⟩,
    ⟨[30607], [30605, 30581], .source 15368⟩,
    ⟨[91245, 3], [91245, 3], .contexts []⟩,
    ⟨[30609], [29722], .source 15369⟩,
    ⟨[30611], [30609, 30581], .source 15370⟩,
    ⟨[91245, 3], [30611, 93801], .contexts [
        ⟨81124, false, false, [], []⟩,
        ⟨64773, true, false, [], [3]⟩,
        ⟨78154, false, false, [29722], [91247, 9, 3]⟩,
        ⟨64963, true, false, [29722, 25939], [9, 3]⟩,
        ⟨64939, true, false, [29722], [9, 3]⟩,
        ⟨573, false, false, [29722, 90473], []⟩,
        ⟨81104, false, false, [29722], []⟩,
        ⟨81103, false, false, [29722], []⟩,
        ⟨81106, false, false, [29722, 30581], []⟩,
        ⟨81125, true, false, [], [30581, 93801]⟩,
        ⟨81126, true, false, [], [93801]⟩
      ]⟩,
    ⟨[30613], [30610], .source 15371⟩,
    ⟨[30587, 93801], [30587, 93801], .contexts []⟩,
    ⟨[30615], [30586], .source 15372⟩,
    ⟨[30586], [30586], .contexts []⟩,
    ⟨[90463, 9], [30591, 93799], .contexts [
        ⟨81111, false, false, [], []⟩,
        ⟨81114, false, false, [], []⟩
      ]⟩,
    ⟨[30591, 93799], [30591, 93799], .contexts []⟩,
    ⟨[90463, 9], [30591, 93799], .contexts [
        ⟨81132, false, false, [], []⟩,
        ⟨81133, false, false, [], []⟩,
        ⟨81133, false, false, [], []⟩
      ]⟩,
    ⟨[93797, 9], [93797, 9], .contexts []⟩,
    ⟨[30617], [30593, 25059], .source 15373⟩,
    ⟨[93797, 9], [30617, 90463], .contexts [
        ⟨81135, false, false, [], []⟩,
        ⟨80942, true, false, [], [9]⟩,
        ⟨81134, true, false, [30590], [5, 9]⟩,
        ⟨598, false, false, [30590, 90463], []⟩,
        ⟨29, false, false, [30590, 90463], []⟩,
        ⟨60681, false, false, [30590], []⟩,
        ⟨77839, false, false, [30590], []⟩,
        ⟨61030, false, false, [30590], []⟩,
        ⟨61030, false, false, [30590], []⟩,
        ⟨61056, false, false, [30590, 25059], []⟩,
        ⟨81115, true, false, [], [25059, 90463]⟩,
        ⟨81136, true, false, [], [90463]⟩
      ]⟩,
    ⟨[30619], [30616], .source 15374⟩,
    ⟨[30621], [30593, 30619], .source 15375⟩,
    ⟨[93799], [30621, 93797], .contexts [
        ⟨81134, true, false, [30590], []⟩,
        ⟨81137, true, false, [30590, 30616], [9]⟩,
        ⟨46, false, false, [30590, 30616, 93797], []⟩,
        ⟨81138, true, false, [30590], [93797]⟩,
        ⟨81115, true, false, [], [30619, 93797]⟩,
        ⟨81139, true, false, [], [93797]⟩
      ]⟩,
    ⟨[30623], [30620], .source 15376⟩,
    ⟨[30620], [30620], .contexts []⟩,
    ⟨[93799], [30621, 93797], .contexts [
        ⟨81140, false, false, [], []⟩
      ]⟩,
    ⟨[93799], [30621, 93797], .contexts [
        ⟨81143, false, false, [], []⟩
      ]⟩,
    ⟨[30625], [30623, 30615], .source 15377⟩,
    ⟨[30627], [30625, 30621], .source 15378⟩,
    ⟨[93797, 15], [30627, 93797], .contexts [
        ⟨81140, true, false, [30620], [15]⟩,
        ⟨80946, true, false, [30620], [15]⟩,
        ⟨81129, true, false, [30620, 30586], [1, 15]⟩,
        ⟨81129, true, false, [30620, 30586], [1, 15]⟩,
        ⟨81109, true, false, [30620, 30586], [1, 15]⟩,
        ⟨81105, true, false, [30620, 30586], [1, 15]⟩,
        ⟨1666, false, false, [30620, 30586, 93801], []⟩,
        ⟨9, false, false, [30620, 30586, 93801], []⟩,
        ⟨80965, false, false, [30620, 30586], []⟩,
        ⟨80966, false, false, [30620, 30586], []⟩,
        ⟨80945, false, false, [30620, 30586], []⟩,
        ⟨80945, false, false, [30620, 30586], []⟩,
        ⟨81112, false, false, [30620, 30586], []⟩,
        ⟨81131, true, false, [30620], [93799]⟩,
        ⟨81131, true, false, [30620], [93799]⟩,
        ⟨81130, true, false, [30620], [93799]⟩,
        ⟨81144, false, false, [30620, 30615], []⟩,
        ⟨81141, true, false, [], [30615, 30621, 93797]⟩,
        ⟨81145, true, false, [], [30621, 93797]⟩,
        ⟨81146, true, false, [], [93797]⟩
      ]⟩,
    ⟨[30629], [30591, 30621], .source 15379⟩,
    ⟨[30631], [25079, 24505], .source 15380⟩,
    ⟨[93797, 7], [93797, 7], .contexts []⟩,
    ⟨[30633], [30628], .source 15381⟩]

/-- Exact literal claimed equations and contextual derivations, block 1268. -/
def y322TCIndexRaw1268 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[30635], [30633, 30631], .source 15382⟩,
    ⟨[93797, 7], [30635, 84203], .contexts [
        ⟨81150, false, false, [], []⟩,
        ⟨81148, false, false, [30628], [93797, 7]⟩,
        ⟨81144, true, false, [30628, 30591], [7]⟩,
        ⟨81132, true, false, [30628], [7]⟩,
        ⟨1084, false, false, [30628, 90463], []⟩,
        ⟨1085, false, false, [30628, 90463], []⟩,
        ⟨61052, false, false, [30628], [9]⟩,
        ⟨58433, false, false, [30628, 25079], []⟩,
        ⟨81149, true, false, [30628], [84203]⟩,
        ⟨25456, false, false, [30628, 30631], []⟩,
        ⟨81151, true, false, [], [30631, 84203]⟩,
        ⟨81152, true, false, [], [84203]⟩
      ]⟩,
    ⟨[30637], [30634], .source 15383⟩,
    ⟨[30617, 90463], [30617, 90463], .contexts []⟩,
    ⟨[30617, 90463], [30617, 90463], .contexts []⟩,
    ⟨[30639], [30617, 25101], .source 15384⟩,
    ⟨[93797, 3], [93795], .contexts [
        ⟨80968, false, false, [], []⟩,
        ⟨80969, false, false, [], []⟩,
        ⟨80937, false, false, [], []⟩,
        ⟨80937, false, false, [], []⟩
      ]⟩,
    ⟨[93797, 2], [93797, 3], .contexts [
        ⟨21, false, false, [93797], []⟩
      ]⟩,
    ⟨[90457, 9], [90457, 9], .contexts []⟩,
    ⟨[93795], [93795], .contexts []⟩,
    ⟨[30641], [30638], .source 15385⟩,
    ⟨[30638], [30638], .contexts []⟩,
    ⟨[90457, 9], [30641, 93795], .contexts [
        ⟨81160, false, false, [], []⟩,
        ⟨81157, false, false, [30638], [90457, 9]⟩,
        ⟨61080, true, false, [30638, 30617], [9]⟩,
        ⟨60679, true, false, [30638, 30617], [9]⟩,
        ⟨81156, true, false, [30638], [3, 9]⟩,
        ⟨81156, true, false, [30638], [3, 9]⟩,
        ⟨81155, true, false, [30638], [3, 9]⟩,
        ⟨81137, true, false, [30638], [3, 9]⟩,
        ⟨81135, true, false, [30638], [3, 9]⟩,
        ⟨479, false, false, [30638, 93797], []⟩,
        ⟨81159, false, false, [30638], []⟩,
        ⟨81158, false, false, [30638], []⟩,
        ⟨81161, false, false, [30638], []⟩,
        ⟨81163, true, false, [], [93795]⟩,
        ⟨81163, true, false, [], [93795]⟩,
        ⟨81162, true, false, [], [93795]⟩
      ]⟩,
    ⟨[30639], [30640], .contexts [
        ⟨81162, true, true, [], []⟩
      ]⟩,
    ⟨[93795, 9], [30639, 90457], .contexts [
        ⟨81164, true, false, [30640], [9]⟩,
        ⟨46, false, false, [30640, 90457], []⟩,
        ⟨81165, true, false, [], [90457]⟩
      ]⟩,
    ⟨[30611, 93801], [30611, 93801], .contexts []⟩,
    ⟨[91245, 3], [30611, 93801], .contexts [
        ⟨81124, false, false, [], []⟩,
        ⟨81127, false, false, [], []⟩,
        ⟨81167, false, false, [], []⟩,
        ⟨81167, false, false, [], []⟩
      ]⟩,
    ⟨[30643], [30611, 30621], .source 15386⟩,
    ⟨[93793, 3], [93793, 3], .contexts []⟩,
    ⟨[30645], [30642], .source 15387⟩,
    ⟨[30642], [30642], .contexts []⟩,
    ⟨[93793, 3], [30645, 91243], .contexts [
        ⟨81170, false, false, [], []⟩,
        ⟨80934, true, false, [], [3]⟩,
        ⟨80938, true, false, [], [1, 3]⟩,
        ⟨81169, false, false, [30642], [93797, 3, 1, 3]⟩,
        ⟨81144, true, false, [30642, 30611], [3, 1, 3]⟩,
        ⟨80946, true, false, [30642, 30611], [3, 1, 3]⟩,
        ⟨81168, true, false, [30642], [1, 3, 1, 3]⟩,
        ⟨1178, false, false, [30642, 91245], []⟩,
        ⟨64999, false, false, [30642], []⟩,
        ⟨64998, false, false, [30642], []⟩,
        ⟨64983, false, false, [30642], []⟩,
        ⟨81172, true, false, [], [91243]⟩,
        ⟨81172, true, false, [], [91243]⟩,
        ⟨81171, true, false, [], [91243]⟩
      ]⟩,
    ⟨[91243, 3], [30643, 93793], .contexts [
        ⟨81173, true, false, [30644], [3]⟩,
        ⟨20, false, false, [30644, 93793], []⟩,
        ⟨81171, false, true, [], [93793]⟩
      ]⟩,
    ⟨[25983, 82887], [25983, 82887], .contexts []⟩,
    ⟨[25983, 82887], [25983, 82887], .contexts []⟩,
    ⟨[30647], [25983, 25399], .source 15388⟩,
    ⟨[30649], [30613, 30647], .source 15389⟩,
    ⟨[93801, 11], [30649, 90623], .contexts [
        ⟨81168, true, false, [30610], [11]⟩,
        ⟨144, false, false, [30610, 91245], []⟩,
        ⟨145, false, false, [30610, 91245], []⟩,
        ⟨65024, false, false, [30610], [3]⟩,
        ⟨65026, false, false, [30610], [3]⟩,
        ⟨81175, false, false, [30610], [3]⟩,
        ⟨81176, false, false, [30610], [3]⟩,
        ⟨81176, false, false, [30610], [3]⟩,
        ⟨62238, false, false, [30610, 25983], []⟩,
        ⟨81177, true, false, [30610], [90623]⟩,
        ⟨62242, false, false, [30610, 30647], []⟩,
        ⟨81128, true, false, [], [30647, 90623]⟩,
        ⟨81178, true, false, [], [90623]⟩
      ]⟩,
    ⟨[30651], [30648], .source 15390⟩,
    ⟨[30627, 93797], [30627, 93797], .contexts []⟩,
    ⟨[30653], [30626], .source 15391⟩,
    ⟨[30626], [30626], .contexts []⟩,
    ⟨[30635, 84203], [30635, 84203], .contexts []⟩,
    ⟨[30635, 84203], [30635, 84203], .contexts []⟩,
    ⟨[30635, 84201], [30635, 84201], .contexts []⟩,
    ⟨[30635, 84201], [30635, 84201], .contexts []⟩,
    ⟨[93795, 7], [93795, 7], .contexts []⟩,
    ⟨[93795, 7], [30635, 84201], .contexts [
        ⟨81188, false, false, [], []⟩,
        ⟨81158, true, false, [], [7]⟩,
        ⟨140, false, false, [93797], []⟩,
        ⟨141, false, false, [93797], []⟩,
        ⟨81150, false, false, [], [3]⟩,
        ⟨81153, false, false, [], [3]⟩,
        ⟨81184, false, false, [], [3]⟩,
        ⟨81185, false, false, [], [3]⟩,
        ⟨81185, false, false, [], [3]⟩,
        ⟨25143, false, false, [30635], []⟩,
        ⟨81186, false, false, [], []⟩,
        ⟨81187, false, false, [], []⟩,
        ⟨25463, false, false, [30635], []⟩,
        ⟨13, true, false, [], [30635, 84201]⟩
      ]⟩,
    ⟨[30623, 93801], [30623, 93801], .contexts []⟩,
    ⟨[30655], [30623, 30649], .source 15392⟩,
    ⟨[30655, 90625], [30655, 90625], .contexts []⟩,
    ⟨[30655, 90625, 11], [93797, 1, 11, 1, 11], .contexts [
        ⟨81192, true, false, [], [11]⟩,
        ⟨62255, true, false, [30655], [11]⟩,
        ⟨81191, false, false, [], [90623, 1, 11]⟩,
        ⟨81179, true, false, [30623], [1, 11]⟩,
        ⟨81190, true, false, [], [11, 1, 11]⟩,
        ⟨81190, true, false, [], [11, 1, 11]⟩,
        ⟨81141, false, false, [], [93801, 11, 1, 11]⟩,
        ⟨81142, false, false, [], [93801, 11, 1, 11]⟩,
        ⟨81142, false, false, [], [93801, 11, 1, 11]⟩,
        ⟨80964, true, false, [30620], [11, 1, 11]⟩,
        ⟨80944, true, false, [30620], [11, 1, 11]⟩,
        ⟨81140, false, false, [30620], [1, 11, 1, 11]⟩
      ]⟩,
    ⟨[90625, 11], [90625, 11], .contexts []⟩,
    ⟨[30657], [30654], .source 15393⟩,
    ⟨[30654], [30654], .contexts []⟩,
    ⟨[90625, 11], [30657, 93797], .contexts [
        ⟨81194, false, false, [], []⟩,
        ⟨81193, false, false, [30654], []⟩,
        ⟨994, false, false, [30654, 93797], []⟩,
        ⟨81196, true, false, [], [93797]⟩,
        ⟨81196, true, false, [], [93797]⟩,
        ⟨81195, true, false, [], [93797]⟩
      ]⟩,
    ⟨[30655], [30656], .contexts [
        ⟨81195, true, true, [], []⟩
      ]⟩,
    ⟨[30641, 93795], [30641, 93795], .contexts []⟩,
    ⟨[30659], [25103, 30641], .source 15394⟩,
    ⟨[93793], [93793], .contexts []⟩,
    ⟨[30661], [30639, 30659], .source 15395⟩,
    ⟨[30645, 91243], [30645, 91243], .contexts []⟩,
    ⟨[30645, 91243], [30645, 91243], .contexts []⟩,
    ⟨[93793, 3], [30645, 91243], .contexts [
        ⟨81170, false, false, [], []⟩,
        ⟨81173, false, false, [], []⟩,
        ⟨81203, false, false, [], []⟩,
        ⟨81204, false, false, [], []⟩,
        ⟨81204, false, false, [], []⟩
      ]⟩,
    ⟨[30663], [30645, 25977], .source 15396⟩,
    ⟨[30665], [30663, 27307], .source 15397⟩,
    ⟨[93793], [93793], .contexts []⟩,
    ⟨[84197, 7], [84197, 7], .contexts []⟩,
    ⟨[30667], [30664], .source 15398⟩,
    ⟨[30664], [30664], .contexts []⟩,
    ⟨[84197, 7], [30667, 93793], .contexts [
        ⟨81209, false, false, [], []⟩,
        ⟨81207, false, false, [30664], [84197, 7]⟩,
        ⟨70081, true, false, [30664, 30663], [7]⟩,
        ⟨63077, true, false, [30664, 30663], [7]⟩,
        ⟨81206, false, false, [30664], [90859, 3, 7]⟩,
        ⟨65020, true, false, [30664, 30645], [3, 7]⟩,
        ⟨81205, true, false, [30664], [7, 3, 7]⟩,
        ⟨18135, false, false, [30664, 93793], []⟩,
        ⟨81208, false, false, [30664], []⟩,
        ⟨81201, false, false, [30664], []⟩,
        ⟨81211, true, false, [], [93793]⟩,
        ⟨81211, true, false, [], [93793]⟩,
        ⟨81210, true, false, [], [93793]⟩
      ]⟩,
    ⟨[30669], [30645, 25995], .source 15399⟩,
    ⟨[30669, 82893], [30669, 82893], .contexts []⟩,
    ⟨[82893, 11], [82893, 11], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1269. -/
def y322TCIndexRaw1269 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[30671], [30668], .source 15400⟩,
    ⟨[30668], [30668], .contexts []⟩,
    ⟨[82893, 11], [30671, 93793], .contexts [
        ⟨81215, false, false, [], []⟩,
        ⟨81214, true, false, [30668], [11]⟩,
        ⟨17830, true, false, [], [11]⟩,
        ⟨81213, false, false, [30668], [82891, 3, 11]⟩,
        ⟨65054, true, false, [30668, 30645], [3, 11]⟩,
        ⟨81205, true, false, [30668], [11, 3, 11]⟩,
        ⟨1693, false, false, [30668, 93793], []⟩,
        ⟨81208, false, false, [30668], []⟩,
        ⟨81201, false, false, [30668], []⟩,
        ⟨81217, true, false, [], [93793]⟩,
        ⟨81217, true, false, [], [93793]⟩,
        ⟨81216, true, false, [], [93793]⟩
      ]⟩,
    ⟨[30673], [30645, 25965], .source 15401⟩,
    ⟨[30675], [30673, 30643], .source 15402⟩,
    ⟨[30675, 93791], [30675, 93791], .contexts []⟩,
    ⟨[30675], [30675], .contexts []⟩,
    ⟨[93793], [30675, 93791], .contexts [
        ⟨81201, false, false, [], []⟩,
        ⟨150, true, false, [93793], []⟩,
        ⟨81205, false, false, [], [15, 3, 15]⟩,
        ⟨65005, false, false, [30645], [3, 15]⟩,
        ⟨81219, true, false, [], [91243, 3, 15]⟩,
        ⟨81174, false, false, [30673], [15]⟩,
        ⟨81220, true, false, [], [93793, 15]⟩,
        ⟨80930, false, false, [30675], []⟩,
        ⟨81221, false, false, [], []⟩,
        ⟨81222, true, false, [], [93791]⟩
      ]⟩,
    ⟨[30677], [30674], .source 15403⟩,
    ⟨[30674], [30674], .contexts []⟩,
    ⟨[30679], [30677, 30645], .source 15404⟩,
    ⟨[93791, 3], [30679, 91243], .contexts [
        ⟨81223, true, false, [30674], [3]⟩,
        ⟨81173, false, false, [30674], []⟩,
        ⟨81203, false, false, [30674], []⟩,
        ⟨81224, true, false, [], [30645, 91243]⟩,
        ⟨81226, true, false, [], [91243]⟩
      ]⟩,
    ⟨[93793], [30675, 93791], .contexts [
        ⟨81223, false, false, [], []⟩
      ]⟩,
    ⟨[93793], [30675, 93791], .contexts [
        ⟨81228, false, false, [], []⟩,
        ⟨81221, false, false, [], []⟩
      ]⟩,
    ⟨[30681], [30677, 30661], .source 15405⟩,
    ⟨[30683], [30681, 30675], .source 15406⟩,
    ⟨[30685], [30677, 30665], .source 15407⟩,
    ⟨[30687], [30677, 30669], .source 15408⟩,
    ⟨[30689], [30635, 21177], .source 15409⟩,
    ⟨[30691], [30689, 27337], .source 15410⟩,
    ⟨[88687, 13], [88687, 13], .contexts []⟩,
    ⟨[30693], [30690], .source 15411⟩,
    ⟨[30690], [30690], .contexts []⟩,
    ⟨[88687, 13], [30693, 93795], .contexts [
        ⟨81236, false, false, [], []⟩,
        ⟨81235, false, false, [30690], [88687, 13]⟩,
        ⟨70132, true, false, [30690, 30689], [13]⟩,
        ⟨81234, false, false, [30690], [85467, 7, 13]⟩,
        ⟨44519, true, false, [30690, 30635], [7, 13]⟩,
        ⟨81187, true, false, [30690], [13, 7, 13]⟩,
        ⟨81187, true, false, [30690], [13, 7, 13]⟩,
        ⟨81186, true, false, [30690], [13, 7, 13]⟩,
        ⟨81189, true, false, [30690], [13, 7, 13]⟩,
        ⟨81188, true, false, [30690], [13, 7, 13]⟩,
        ⟨15654, false, false, [30690, 93795], []⟩,
        ⟨81161, false, false, [30690], []⟩,
        ⟨81238, true, false, [], [93795]⟩,
        ⟨81238, true, false, [], [93795]⟩,
        ⟨81237, true, false, [], [93795]⟩
      ]⟩,
    ⟨[30657, 93797], [30657, 93797], .contexts []⟩,
    ⟨[30656], [30656], .contexts []⟩,
    ⟨[93795, 11], [30655, 90627], .contexts [
        ⟨80938, true, false, [], [11]⟩,
        ⟨81240, true, false, [30656], [3, 11]⟩,
        ⟨81240, true, false, [30656], [3, 11]⟩,
        ⟨81197, true, false, [30656], [3, 11]⟩,
        ⟨81194, true, false, [30656], [3, 11]⟩,
        ⟨603, false, false, [30656, 90625], []⟩,
        ⟨21, false, false, [30656, 90625], []⟩,
        ⟨62273, false, false, [30656], []⟩,
        ⟨62282, false, false, [30656], []⟩,
        ⟨81241, true, false, [], [90627]⟩,
        ⟨81241, true, false, [], [90627]⟩,
        ⟨81198, true, false, [], [90627]⟩
      ]⟩,
    ⟨[30697], [30667, 30675], .source 15413⟩,
    ⟨[30697, 93789], [30697, 93789], .contexts []⟩,
    ⟨[30699], [30696], .source 15414⟩,
    ⟨[30696], [30696], .contexts []⟩,
    ⟨[27325, 85925], [30697, 93789], .contexts [
        ⟨79790, true, false, [], []⟩,
        ⟨81245, false, false, [30698], [84195, 7]⟩,
        ⟨81246, false, false, [30698], [84195, 7]⟩,
        ⟨81246, false, false, [30698], [84195, 7]⟩,
        ⟨79762, true, false, [30698, 30696], [7]⟩,
        ⟨25131, true, false, [30698, 30696], [7]⟩,
        ⟨25131, true, false, [30698, 30696], [7]⟩,
        ⟨25198, true, false, [30698, 30696], [7]⟩,
        ⟨25197, true, false, [30698, 30696], [7]⟩,
        ⟨64, true, false, [30698, 30696, 84197], [7]⟩,
        ⟨518, true, false, [30698, 30696, 84197], [7]⟩,
        ⟨81209, false, false, [30698, 30696], [13, 7, 7]⟩,
        ⟨81212, false, false, [30698, 30696], [13, 7, 7]⟩,
        ⟨81229, false, false, [30698, 30696, 30667], [13, 7, 7]⟩,
        ⟨81243, true, false, [30698, 30696], [93791, 13, 7, 7]⟩,
        ⟨80926, false, false, [30698], [7, 7]⟩,
        ⟨81244, false, false, [30698, 30696], [7, 7]⟩,
        ⟨38, false, false, [30698, 93789], []⟩,
        ⟨81245, false, true, [], [93789]⟩
      ]⟩,
    ⟨[30701], [30291, 30697], .source 15415⟩,
    ⟨[30703], [30700], .source 15416⟩,
    ⟨[93789], [30703, 85925], .contexts [
        ⟨81248, false, false, [30700], [93789]⟩,
        ⟨79791, false, false, [30700], [30697, 93789]⟩,
        ⟨81244, true, false, [30700, 27324], []⟩,
        ⟨81247, true, false, [30700, 27324], []⟩,
        ⟨81249, true, false, [], [85925]⟩
      ]⟩,
    ⟨[30701], [30702], .contexts [
        ⟨81249, true, true, [], []⟩
      ]⟩,
    ⟨[30702], [30702], .contexts []⟩,
    ⟨[30701], [30702], .contexts [
        ⟨81251, false, false, [], []⟩,
        ⟨81252, false, false, [], []⟩,
        ⟨81252, false, false, [], []⟩
      ]⟩,
    ⟨[85925, 13], [30701, 93791], .contexts [
        ⟨81250, true, false, [30702], [13]⟩,
        ⟨80924, false, false, [30702], []⟩,
        ⟨80970, false, false, [30702], []⟩,
        ⟨81253, true, false, [], [93791]⟩
      ]⟩,
    ⟨[93789], [30703, 85925], .contexts [
        ⟨81250, false, false, [], []⟩
      ]⟩,
    ⟨[93787], [30703, 85927], .contexts [
        ⟨81251, false, false, [30700], [93787]⟩,
        ⟨13, false, false, [30700, 30702], [93787]⟩,
        ⟨80971, true, false, [30700, 30702], []⟩,
        ⟨80922, true, false, [30700, 30702], []⟩,
        ⟨81255, false, false, [30700, 30702], [1]⟩,
        ⟨34214, false, false, [30700], []⟩,
        ⟨81249, true, false, [], [85927]⟩
      ]⟩,
    ⟨[85927, 11], [30701, 93785], .contexts [
        ⟨81256, true, false, [30702], [11]⟩,
        ⟨80919, false, false, [30702], []⟩,
        ⟨80973, false, false, [30702], []⟩,
        ⟨81253, true, false, [], [93785]⟩
      ]⟩,
    ⟨[30705], [30671, 30675], .source 15417⟩,
    ⟨[30707], [30705, 30703], .source 15418⟩,
    ⟨[85925, 11], [85925, 11], .contexts []⟩,
    ⟨[30709], [30706], .source 15419⟩,
    ⟨[30711], [30709, 25541], .source 15420⟩,
    ⟨[85925, 11], [30711, 83019], .contexts [
        ⟨81260, false, false, [], []⟩,
        ⟨81259, false, false, [30706], [85925, 11]⟩,
        ⟨81255, true, false, [30706, 30705], [11]⟩,
        ⟨80926, true, false, [30706, 30705], [11]⟩,
        ⟨81258, false, false, [30706], [93791, 13, 11]⟩,
        ⟨81229, true, false, [30706, 30671], [13, 11]⟩,
        ⟨81218, true, false, [30706], [13, 11]⟩,
        ⟨81215, true, false, [30706], [13, 11]⟩,
        ⟨619, false, false, [30706, 82893], []⟩,
        ⟨64, false, false, [30706, 82893], []⟩,
        ⟨62882, false, false, [30706], []⟩,
        ⟨62849, false, false, [30706, 25541], []⟩,
        ⟨81261, true, false, [], [25541, 83019]⟩,
        ⟨81262, true, false, [], [83019]⟩
      ]⟩,
    ⟨[30713], [30710], .source 15421⟩,
    ⟨[83019, 11], [30713, 85925], .contexts [
        ⟨81263, true, false, [30710], [11]⟩,
        ⟨53, false, false, [30710, 85925], []⟩,
        ⟨81264, true, false, [], [85925]⟩
      ]⟩,
    ⟨[30693, 93795], [30693, 93795], .contexts []⟩,
    ⟨[30715], [30693, 30639], .source 15422⟩,
    ⟨[30717], [30715, 25109], .source 15423⟩,
    ⟨[89421, 9], [89421, 9], .contexts []⟩,
    ⟨[88687], [88687], .contexts []⟩,
    ⟨[30719], [30716], .source 15424⟩,
    ⟨[30716], [30716], .contexts []⟩,
    ⟨[89421, 9], [30719, 88687], .contexts [
        ⟨81269, false, false, [], []⟩,
        ⟨81268, false, false, [30716], [89421, 9]⟩,
        ⟨61103, true, false, [30716, 30715], [9]⟩,
        ⟨60668, true, false, [30716, 30715], [9]⟩,
        ⟨81267, false, false, [30716], [90457, 13, 9]⟩,
        ⟨81166, true, false, [30716, 30693], [13, 9]⟩,
        ⟨81266, true, false, [30716], [9, 13, 9]⟩,
        ⟨81266, true, false, [30716], [9, 13, 9]⟩,
        ⟨81239, true, false, [30716], [9, 13, 9]⟩,
        ⟨81236, true, false, [30716], [9, 13, 9]⟩,
        ⟨5366, false, false, [30716, 88687], []⟩,
        ⟨81270, false, false, [30716], []⟩,
        ⟨81272, true, false, [], [88687]⟩,
        ⟨81272, true, false, [], [88687]⟩,
        ⟨81271, true, false, [], [88687]⟩
      ]⟩,
    ⟨[88687, 9], [30717, 89421], .contexts [
        ⟨81273, true, false, [30718], [9]⟩,
        ⟨46, false, false, [30718, 89421], []⟩,
        ⟨81271, false, true, [], [89421]⟩
      ]⟩,
    ⟨[85927, 11], [30701, 93785], .contexts [
        ⟨81257, false, false, [], []⟩
      ]⟩,
    ⟨[30701, 93785], [30701, 93785], .contexts []⟩,
    ⟨[30701, 93785], [30701, 93785], .contexts []⟩,
    ⟨[30711, 83019], [30711, 83019], .contexts []⟩,
    ⟨[30711, 83019], [30711, 83019], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1270. -/
def y322TCIndexRaw1270 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85925, 11], [30711, 83019], .contexts [
        ⟨81260, false, false, [], []⟩,
        ⟨81263, false, false, [], []⟩,
        ⟨81278, false, false, [], []⟩,
        ⟨81279, false, false, [], []⟩,
        ⟨81279, false, false, [], []⟩
      ]⟩,
    ⟨[85925, 10], [85925, 11], .contexts [
        ⟨54, false, false, [85925], []⟩
      ]⟩,
    ⟨[93785, 1], [93785, 1], .contexts []⟩,
    ⟨[30703], [30700], .contexts [
        ⟨81249, false, false, [], []⟩
      ]⟩,
    ⟨[30721], [30703, 30711], .source 15425⟩,
    ⟨[93785, 1], [30721, 83019], .contexts [
        ⟨81282, false, false, [], []⟩,
        ⟨81277, true, false, [30700], [1]⟩,
        ⟨81277, true, false, [30700], [1]⟩,
        ⟨81276, true, false, [30700], [1]⟩,
        ⟨81275, true, false, [30700], [1]⟩,
        ⟨34219, true, false, [30700], [11, 1]⟩,
        ⟨34219, true, false, [30700], [11, 1]⟩,
        ⟨34330, true, false, [30700], [11, 1]⟩,
        ⟨34214, true, false, [30700], [11, 1]⟩,
        ⟨4506, false, false, [30700, 85925], []⟩,
        ⟨81281, false, false, [30700], []⟩,
        ⟨81280, false, false, [30700], []⟩,
        ⟨62849, false, false, [30700, 30711], []⟩,
        ⟨81283, true, false, [], [30711, 83019]⟩,
        ⟨81284, true, false, [], [83019]⟩
      ]⟩,
    ⟨[30723], [30720], .source 15426⟩,
    ⟨[83019, 1], [30723, 93785], .contexts [
        ⟨81285, true, false, [30720], [1]⟩,
        ⟨8, false, false, [30720, 93785], []⟩,
        ⟨81286, true, false, [], [93785]⟩
      ]⟩,
    ⟨[26419, 91605], [26419, 27317, 84193], .contexts [
        ⟨70111, false, false, [26419], []⟩
      ]⟩,
    ⟨[30725], [26419, 27317], .source 15427⟩,
    ⟨[85927, 11], [30701, 93785], .contexts [
        ⟨81275, false, false, [], []⟩,
        ⟨81276, false, false, [], []⟩,
        ⟨81277, false, false, [], []⟩,
        ⟨81277, false, false, [], []⟩
      ]⟩,
    ⟨[85927, 10], [85927, 11], .contexts [
        ⟨54, false, false, [85927], []⟩
      ]⟩,
    ⟨[84191, 7], [84191, 7], .contexts []⟩,
    ⟨[93785], [93785], .contexts []⟩,
    ⟨[30727], [30724], .source 15428⟩,
    ⟨[30729], [30727, 30701], .source 15429⟩,
    ⟨[84191, 7], [30729, 93785], .contexts [
        ⟨81292, false, false, [], []⟩,
        ⟨25124, true, false, [], [7]⟩,
        ⟨81289, false, false, [30724], [84193, 11, 7]⟩,
        ⟨81288, true, false, [30724], [11, 7]⟩,
        ⟨66851, true, false, [30724], [11, 7]⟩,
        ⟨555, false, false, [30724, 85927], []⟩,
        ⟨81291, false, false, [30724], []⟩,
        ⟨81290, false, false, [30724], []⟩,
        ⟨81293, false, false, [30724, 30701], []⟩,
        ⟨81294, true, false, [], [30701, 93785]⟩,
        ⟨81295, true, false, [], [93785]⟩
      ]⟩,
    ⟨[30731], [30728], .source 15430⟩,
    ⟨[93785, 7], [30731, 84191], .contexts [
        ⟨81296, true, false, [30728], [7]⟩,
        ⟨38, false, false, [30728, 84191], []⟩,
        ⟨81297, true, false, [], [84191]⟩
      ]⟩,
    ⟨[30301, 85919], [30301, 85919], .contexts []⟩,
    ⟨[30301, 85919], [30301, 85919], .contexts []⟩,
    ⟨[85927, 15], [30301, 85919], .contexts [
        ⟨79849, false, false, [], []⟩,
        ⟨81299, false, false, [], []⟩,
        ⟨81300, false, false, [], []⟩,
        ⟨81300, false, false, [], []⟩
      ]⟩,
    ⟨[85917, 15], [85917, 15], .contexts []⟩,
    ⟨[30303], [30300], .contexts [
        ⟨79807, false, false, [], []⟩
      ]⟩,
    ⟨[30733], [30303, 30701], .source 15431⟩,
    ⟨[85917, 15], [30733, 93785], .contexts [
        ⟨81302, false, false, [], []⟩,
        ⟨34200, true, false, [], [15]⟩,
        ⟨81301, true, false, [30300], [11, 15]⟩,
        ⟨2046, false, false, [30300, 85927], []⟩,
        ⟨81291, false, false, [30300], []⟩,
        ⟨81290, false, false, [30300], []⟩,
        ⟨81293, false, false, [30300, 30701], []⟩,
        ⟨81303, true, false, [], [30701, 93785]⟩,
        ⟨81304, true, false, [], [93785]⟩
      ]⟩,
    ⟨[30735], [30732], .source 15432⟩,
    ⟨[93785, 15], [30735, 85917], .contexts [
        ⟨81305, true, false, [30732], [15]⟩,
        ⟨1, false, false, [30732, 85917], []⟩,
        ⟨81306, true, false, [], [85917]⟩
      ]⟩,
    ⟨[30719, 88687], [30719, 88687], .contexts []⟩,
    ⟨[30719, 88687], [30719, 88687], .contexts []⟩,
    ⟨[89421, 9], [30719, 88687], .contexts [
        ⟨81269, false, false, [], []⟩,
        ⟨81273, false, false, [], []⟩,
        ⟨81308, false, false, [], []⟩,
        ⟨81309, false, false, [], []⟩,
        ⟨81309, false, false, [], []⟩
      ]⟩,
    ⟨[30737], [30719, 26177], .source 15433⟩,
    ⟨[30737, 91345], [30737, 91345], .contexts []⟩,
    ⟨[91345, 9], [91345, 9], .contexts []⟩,
    ⟨[30739], [30736], .source 15434⟩,
    ⟨[30736], [30736], .contexts []⟩,
    ⟨[91345, 9], [30739, 89419], .contexts [
        ⟨81313, false, false, [], []⟩,
        ⟨81312, true, false, [30736], [9]⟩,
        ⟨65455, true, false, [], [9]⟩,
        ⟨81311, false, false, [30736], [91347, 1, 9]⟩,
        ⟨65745, true, false, [30736, 30719], [1, 9]⟩,
        ⟨52062, true, false, [30736, 30719], [9, 1, 9]⟩,
        ⟨81310, true, false, [30736], [1, 9, 1, 9]⟩,
        ⟨495, false, false, [30736, 89421], []⟩,
        ⟨9, false, false, [30736, 89421], []⟩,
        ⟨55821, false, false, [30736], []⟩,
        ⟨55822, false, false, [30736], []⟩,
        ⟨55771, false, false, [30736], []⟩,
        ⟨55771, false, false, [30736], []⟩,
        ⟨61115, false, false, [30736], []⟩,
        ⟨81315, true, false, [], [89419]⟩,
        ⟨81315, true, false, [], [89419]⟩,
        ⟨81314, true, false, [], [89419]⟩
      ]⟩,
    ⟨[89419, 9], [30737, 91345], .contexts [
        ⟨81316, true, false, [30738], [9]⟩,
        ⟨46, false, false, [30738, 91345], []⟩,
        ⟨81314, false, true, [], [91345]⟩
      ]⟩,
    ⟨[30741], [30719, 29307], .source 15435⟩,
    ⟨[89421, 15], [29679, 91813], .contexts [
        ⟨77649, false, false, [], []⟩,
        ⟨77680, false, false, [], []⟩,
        ⟨77682, false, false, [], []⟩,
        ⟨77683, false, false, [], []⟩
      ]⟩,
    ⟨[89421, 14], [89421, 15], .contexts [
        ⟨10, false, false, [89421], []⟩
      ]⟩,
    ⟨[91813], [91813], .contexts []⟩,
    ⟨[30743], [30740], .source 15436⟩,
    ⟨[30745], [30743, 29679], .source 15437⟩,
    ⟨[88683, 9], [30745, 91813], .contexts [
        ⟨81318, false, false, [30740], [88683, 9]⟩,
        ⟨76310, true, false, [30740, 30719], [9]⟩,
        ⟨52060, true, false, [30740, 30719], [9]⟩,
        ⟨81310, true, false, [30740], [15, 9]⟩,
        ⟨935, false, false, [30740, 89421], []⟩,
        ⟨81320, false, false, [30740], []⟩,
        ⟨81319, false, false, [30740], []⟩,
        ⟨81321, false, false, [30740, 29679], []⟩,
        ⟨81322, true, false, [], [29679, 91813]⟩,
        ⟨81323, true, false, [], [91813]⟩
      ]⟩,
    ⟨[30747], [30744], .source 15438⟩,
    ⟨[30721, 83019], [30721, 83019], .contexts []⟩,
    ⟨[30721, 83019], [30721, 83019], .contexts []⟩,
    ⟨[93785, 1], [30721, 83019], .contexts [
        ⟨81282, false, false, [], []⟩,
        ⟨81285, false, false, [], []⟩,
        ⟨81326, false, false, [], []⟩,
        ⟨81327, false, false, [], []⟩,
        ⟨81327, false, false, [], []⟩
      ]⟩,
    ⟨[30721, 83023], [30721, 83023], .contexts []⟩,
    ⟨[83023, 5], [83023, 5], .contexts []⟩,
    ⟨[30723], [30720], .contexts [
        ⟨81286, false, false, [], []⟩
      ]⟩,
    ⟨[30720], [30720], .contexts []⟩,
    ⟨[30723], [30720], .contexts [
        ⟨81331, false, false, [], []⟩,
        ⟨81332, false, false, [], []⟩,
        ⟨81332, false, false, [], []⟩
      ]⟩,
    ⟨[83023, 5], [30723, 93785], .contexts [
        ⟨81330, false, false, [], []⟩,
        ⟨81329, true, false, [30720], [5]⟩,
        ⟨18429, true, false, [], [5]⟩,
        ⟨18425, true, false, [], [1, 5]⟩,
        ⟨81328, true, false, [30720], [5, 1, 5]⟩,
        ⟨1152, false, false, [30720, 93785], []⟩,
        ⟨81293, false, false, [30720], []⟩,
        ⟨81333, true, false, [], [93785]⟩
      ]⟩,
    ⟨[30721], [30722], .contexts [
        ⟨81286, true, true, [], []⟩
      ]⟩,
    ⟨[93785, 5], [30721, 83023], .contexts [
        ⟨81334, true, false, [30722], [5]⟩,
        ⟨28, false, false, [30722, 83023], []⟩,
        ⟨81335, true, false, [], [83023]⟩
      ]⟩,
    ⟨[30729, 93785], [30729, 93785], .contexts []⟩,
    ⟨[30729, 93785], [30729, 93785], .contexts []⟩,
    ⟨[93783, 7], [93783, 7], .contexts []⟩,
    ⟨[30728], [30728], .contexts []⟩,
    ⟨[93783, 7], [30731, 84189], .contexts [
        ⟨81339, false, false, [], []⟩,
        ⟨80915, true, false, [], [7]⟩,
        ⟨81338, true, false, [30728], [9, 7]⟩,
        ⟨81338, true, false, [30728], [9, 7]⟩,
        ⟨81337, true, false, [30728], [9, 7]⟩,
        ⟨81296, true, false, [30728], [9, 7]⟩,
        ⟨81292, true, false, [30728], [9, 7]⟩,
        ⟨579, false, false, [30728, 84191], []⟩,
        ⟨70238, false, false, [30728], []⟩,
        ⟨70237, false, false, [30728], []⟩,
        ⟨70239, false, false, [30728], []⟩,
        ⟨81340, true, false, [], [84189]⟩,
        ⟨81340, true, false, [], [84189]⟩,
        ⟨81297, true, false, [], [84189]⟩
      ]⟩,
    ⟨[30729], [30730], .contexts [
        ⟨81297, true, true, [], []⟩
      ]⟩,
    ⟨[84189, 7], [30729, 93783], .contexts [
        ⟨81341, true, false, [30730], [7]⟩,
        ⟨38, false, false, [30730, 93783], []⟩,
        ⟨81342, true, false, [], [93783]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1271. -/
def y322TCIndexRaw1271 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[30733, 93785], [30733, 93785], .contexts []⟩,
    ⟨[30733, 93785], [30733, 93785], .contexts []⟩,
    ⟨[85917, 15], [30733, 93785], .contexts [
        ⟨81302, false, false, [], []⟩,
        ⟨81305, false, false, [], []⟩,
        ⟨81344, false, false, [], []⟩,
        ⟨81345, false, false, [], []⟩,
        ⟨81345, false, false, [], []⟩
      ]⟩,
    ⟨[93783, 15], [93783, 15], .contexts []⟩,
    ⟨[85915], [85915], .contexts []⟩,
    ⟨[30735], [30735], .contexts []⟩,
    ⟨[30735], [30732], .contexts [
        ⟨81349, false, false, [], []⟩,
        ⟨81306, false, false, [], []⟩
      ]⟩,
    ⟨[30732], [30732], .contexts []⟩,
    ⟨[30735], [30732], .contexts [
        ⟨81350, false, false, [], []⟩,
        ⟨81351, false, false, [], []⟩,
        ⟨81351, false, false, [], []⟩
      ]⟩,
    ⟨[93783, 15], [30735, 85915], .contexts [
        ⟨81347, false, false, [], []⟩,
        ⟨80915, true, false, [], [15]⟩,
        ⟨81346, true, false, [30732], [9, 15]⟩,
        ⟨1671, false, false, [30732, 85917], []⟩,
        ⟨47, false, false, [30732, 85917], []⟩,
        ⟨34341, false, false, [30732], []⟩,
        ⟨34342, false, false, [30732], []⟩,
        ⟨34195, false, false, [30732], []⟩,
        ⟨34195, false, false, [30732], []⟩,
        ⟨81348, false, false, [30732], []⟩,
        ⟨81352, true, false, [], [85915]⟩
      ]⟩,
    ⟨[30733], [30734], .contexts [
        ⟨81306, true, true, [], []⟩
      ]⟩,
    ⟨[30739, 89419], [30739, 89419], .contexts []⟩,
    ⟨[30749], [30739, 25111], .source 15439⟩,
    ⟨[90449, 11], [90449, 11], .contexts []⟩,
    ⟨[30751], [30748], .source 15440⟩,
    ⟨[30751], [30751], .contexts []⟩,
    ⟨[30751], [30748], .contexts [
        ⟨81358, false, false, [], []⟩
      ]⟩,
    ⟨[30748], [30748], .contexts []⟩,
    ⟨[30751], [30748], .contexts [
        ⟨81359, false, false, [], []⟩,
        ⟨81360, false, false, [], []⟩,
        ⟨81361, false, false, [], []⟩,
        ⟨81361, false, false, [], []⟩
      ]⟩,
    ⟨[90449, 11], [30751, 91341], .contexts [
        ⟨81357, false, false, [], []⟩,
        ⟨60657, true, false, [], [11]⟩,
        ⟨81356, false, false, [30748], [90451, 9, 11]⟩,
        ⟨61109, true, false, [30748, 30739], [9, 11]⟩,
        ⟨81355, true, false, [30748], [11, 9, 11]⟩,
        ⟨81355, true, false, [30748], [11, 9, 11]⟩,
        ⟨81316, true, false, [30748], [11, 9, 11]⟩,
        ⟨81313, true, false, [30748], [11, 9, 11]⟩,
        ⟨536, false, false, [30748, 91345], []⟩,
        ⟨537, false, false, [30748, 91345], []⟩,
        ⟨65510, false, false, [30748], [9]⟩,
        ⟨65511, false, false, [30748], [9]⟩,
        ⟨65450, false, false, [30748], [9]⟩,
        ⟨65450, false, false, [30748], [9]⟩,
        ⟨65513, false, false, [30748], []⟩,
        ⟨65514, false, false, [30748], []⟩,
        ⟨65446, false, false, [30748], []⟩,
        ⟨65446, false, false, [30748], []⟩,
        ⟨81362, true, false, [], [91341]⟩
      ]⟩,
    ⟨[30749], [30750], .contexts [
        ⟨81358, true, true, [], []⟩
      ]⟩,
    ⟨[30723, 93785], [30723, 93785], .contexts []⟩,
    ⟨[30723, 93785], [30723, 93785], .contexts []⟩,
    ⟨[93783, 5], [93783, 5], .contexts []⟩,
    ⟨[83025], [83025], .contexts []⟩,
    ⟨[30722], [30722], .contexts []⟩,
    ⟨[30721], [30722], .contexts [
        ⟨81335, false, false, [], []⟩,
        ⟨81369, false, false, [], []⟩,
        ⟨81369, false, false, [], []⟩
      ]⟩,
    ⟨[93783, 5], [30721, 83025], .contexts [
        ⟨81367, false, false, [], []⟩,
        ⟨80915, true, false, [], [5]⟩,
        ⟨81366, true, false, [30722], [9, 5]⟩,
        ⟨81366, true, false, [30722], [9, 5]⟩,
        ⟨81365, true, false, [30722], [9, 5]⟩,
        ⟨81334, true, false, [30722], [9, 5]⟩,
        ⟨81330, true, false, [30722], [9, 5]⟩,
        ⟨960, false, false, [30722, 83023], []⟩,
        ⟨47, false, false, [30722, 83023], []⟩,
        ⟨18433, false, false, [30722], []⟩,
        ⟨18656, false, false, [30722], []⟩,
        ⟨18438, false, false, [30722], []⟩,
        ⟨18438, false, false, [30722], []⟩,
        ⟨81368, false, false, [30722], []⟩,
        ⟨81370, true, false, [], [83025]⟩
      ]⟩,
    ⟨[83025, 5], [30723, 93783], .contexts [
        ⟨81371, true, false, [30720], [5]⟩,
        ⟨28, false, false, [30720, 93783], []⟩,
        ⟨81286, true, false, [], [93783]⟩
      ]⟩,
    ⟨[30731, 84189], [30731, 84189], .contexts []⟩,
    ⟨[30731, 84189], [30731, 84189], .contexts []⟩,
    ⟨[30731, 84187], [30731, 84187], .contexts []⟩,
    ⟨[93783, 1], [93781], .contexts [
        ⟨80976, false, false, [], []⟩,
        ⟨80977, false, false, [], []⟩,
        ⟨80911, false, false, [], []⟩,
        ⟨80911, false, false, [], []⟩
      ]⟩,
    ⟨[93783, 0], [93783, 1], .contexts [
        ⟨9, false, false, [93783], []⟩
      ]⟩,
    ⟨[84187, 7], [84187, 7], .contexts []⟩,
    ⟨[93781], [93781], .contexts []⟩,
    ⟨[30730], [30730], .contexts []⟩,
    ⟨[84187, 7], [30729, 93781], .contexts [
        ⟨81378, false, false, [], []⟩,
        ⟨81375, true, false, [30730], [7]⟩,
        ⟨25116, true, false, [], [7]⟩,
        ⟨81374, true, false, [30730], [1, 7]⟩,
        ⟨81374, true, false, [30730], [1, 7]⟩,
        ⟨81373, true, false, [30730], [1, 7]⟩,
        ⟨81341, true, false, [30730], [1, 7]⟩,
        ⟨81339, true, false, [30730], [1, 7]⟩,
        ⟨502, false, false, [30730, 93783], []⟩,
        ⟨81377, false, false, [30730], []⟩,
        ⟨81376, false, false, [30730], []⟩,
        ⟨81379, false, false, [30730], []⟩,
        ⟨81380, true, false, [], [93781]⟩,
        ⟨81380, true, false, [], [93781]⟩,
        ⟨81342, true, false, [], [93781]⟩
      ]⟩,
    ⟨[30735, 85915], [30735, 85915], .contexts []⟩,
    ⟨[30735, 85915], [30735, 85915], .contexts []⟩,
    ⟨[85913, 15], [85913, 15], .contexts []⟩,
    ⟨[30733], [30733], .contexts []⟩,
    ⟨[30733], [30734], .contexts [
        ⟨81354, false, false, [], []⟩
      ]⟩,
    ⟨[30734], [30734], .contexts []⟩,
    ⟨[30733], [30734], .contexts [
        ⟨81385, false, false, [], []⟩,
        ⟨81386, false, false, [], []⟩,
        ⟨81387, false, false, [], []⟩,
        ⟨81387, false, false, [], []⟩
      ]⟩,
    ⟨[85913, 15], [30733, 93781], .contexts [
        ⟨81384, false, false, [], []⟩,
        ⟨34192, true, false, [], [15]⟩,
        ⟨81383, true, false, [30734], [1, 15]⟩,
        ⟨81383, true, false, [30734], [1, 15]⟩,
        ⟨81382, true, false, [30734], [1, 15]⟩,
        ⟨81353, true, false, [30734], [1, 15]⟩,
        ⟨81347, true, false, [30734], [1, 15]⟩,
        ⟨1666, false, false, [30734, 93783], []⟩,
        ⟨81377, false, false, [30734], []⟩,
        ⟨81376, false, false, [30734], []⟩,
        ⟨81379, false, false, [30734], []⟩,
        ⟨81388, true, false, [], [93781]⟩
      ]⟩,
    ⟨[30751, 91341], [30751, 91341], .contexts []⟩,
    ⟨[91339, 11], [91339, 11], .contexts []⟩,
    ⟨[30749], [30749], .contexts []⟩,
    ⟨[30750], [30750], .contexts []⟩,
    ⟨[30749], [30750], .contexts [
        ⟨81392, false, false, [], []⟩,
        ⟨81364, false, false, [], []⟩,
        ⟨81393, false, false, [], []⟩,
        ⟨81393, false, false, [], []⟩
      ]⟩,
    ⟨[91339, 11], [30749, 90447], .contexts [
        ⟨81391, false, false, [], []⟩,
        ⟨65444, true, false, [], [11]⟩,
        ⟨81390, true, false, [30750], [1, 11]⟩,
        ⟨81390, true, false, [30750], [1, 11]⟩,
        ⟨81363, true, false, [30750], [1, 11]⟩,
        ⟨81357, true, false, [30750], [1, 11]⟩,
        ⟨567, false, false, [30750, 90449], []⟩,
        ⟨9, false, false, [30750, 90449], []⟩,
        ⟨60735, false, false, [30750], []⟩,
        ⟨60736, false, false, [30750], []⟩,
        ⟨60652, false, false, [30750], []⟩,
        ⟨60652, false, false, [30750], []⟩,
        ⟨81394, true, false, [], [90447]⟩
      ]⟩,
    ⟨[30721, 83025], [30721, 83025], .contexts []⟩,
    ⟨[30721, 83025], [30721, 83025], .contexts []⟩,
    ⟨[83025, 1], [83025, 1], .contexts []⟩,
    ⟨[83025, 1], [30723, 93779], .contexts [
        ⟨81398, false, false, [], []⟩,
        ⟨81397, true, false, [30720], [1]⟩,
        ⟨81397, true, false, [30720], [1]⟩,
        ⟨81396, true, false, [30720], [1]⟩,
        ⟨81371, true, false, [30720], [1]⟩,
        ⟨81367, true, false, [30720], [1]⟩,
        ⟨161, false, false, [30720, 93783], []⟩,
        ⟨162, false, false, [30720, 93783], []⟩,
        ⟨81376, false, false, [30720], [5]⟩,
        ⟨80978, false, false, [30720], []⟩,
        ⟨80979, false, false, [30720], []⟩,
        ⟨80908, false, false, [30720], []⟩,
        ⟨80908, false, false, [30720], []⟩,
        ⟨81333, true, false, [], [93779]⟩
      ]⟩,
    ⟨[93779, 1], [30721, 83025], .contexts [
        ⟨81399, true, false, [30722], [1]⟩,
        ⟨8, false, false, [30722, 83025], []⟩,
        ⟨81335, true, false, [], [83025]⟩
      ]⟩,
    ⟨[30733, 93781], [30733, 93781], .contexts []⟩,
    ⟨[30733, 93779], [30733, 93779], .contexts []⟩,
    ⟨[93779, 15], [93779, 15], .contexts []⟩,
    ⟨[85911], [85911], .contexts []⟩,
    ⟨[93779, 15], [30735, 85911], .contexts [
        ⟨81403, false, false, [], []⟩,
        ⟨81402, true, false, [30732], [15]⟩,
        ⟨80909, true, false, [], [15]⟩,
        ⟨81401, true, false, [30732], [5, 15]⟩,
        ⟨81401, true, false, [30732], [5, 15]⟩,
        ⟨81389, true, false, [30732], [5, 15]⟩,
        ⟨81384, true, false, [30732], [5, 15]⟩,
        ⟨2072, false, false, [30732, 85913], []⟩,
        ⟨29, false, false, [30732, 85913], []⟩,
        ⟨34346, false, false, [30732], []⟩,
        ⟨34347, false, false, [30732], []⟩,
        ⟨34187, false, false, [30732], []⟩,
        ⟨34187, false, false, [30732], []⟩,
        ⟨81404, false, false, [30732], []⟩,
        ⟨81352, true, false, [], [85911]⟩
      ]⟩,
    ⟨[91339, 11], [30749, 90447], .contexts [
        ⟨81391, false, false, [], []⟩,
        ⟨81395, false, false, [], []⟩
      ]⟩,
    ⟨[30749, 90447], [30749, 90447], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1272. -/
def y322TCIndexRaw1272 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[30749, 90445], [30749, 90445], .contexts []⟩,
    ⟨[90445, 11], [90445, 11], .contexts []⟩,
    ⟨[90445, 11], [30751, 91337], .contexts [
        ⟨81409, false, false, [], []⟩,
        ⟨81408, true, false, [30748], [11]⟩,
        ⟨60650, true, false, [], [11]⟩,
        ⟨81407, true, false, [30748], [5, 11]⟩,
        ⟨81407, true, false, [30748], [5, 11]⟩,
        ⟨81406, true, false, [30748], [5, 11]⟩,
        ⟨588, false, false, [30748, 91339], []⟩,
        ⟨29, false, false, [30748, 91339], []⟩,
        ⟨65516, false, false, [30748], []⟩,
        ⟨65517, false, false, [30748], []⟩,
        ⟨65439, false, false, [30748], []⟩,
        ⟨65439, false, false, [30748], []⟩,
        ⟨81362, true, false, [], [91337]⟩
      ]⟩,
    ⟨[30723, 93779], [30723, 93779], .contexts []⟩,
    ⟨[30723, 93779], [30723, 93779], .contexts []⟩,
    ⟨[83025, 1], [30723, 93779], .contexts [
        ⟨81398, false, false, [], []⟩,
        ⟨81399, false, false, [], []⟩,
        ⟨81411, false, false, [], []⟩,
        ⟨81412, false, false, [], []⟩,
        ⟨81412, false, false, [], []⟩
      ]⟩,
    ⟨[93779, 11], [93779, 11], .contexts []⟩,
    ⟨[83029], [83029], .contexts []⟩,
    ⟨[93779, 11], [30721, 83029], .contexts [
        ⟨81414, false, false, [], []⟩,
        ⟨81413, true, false, [30722], [11]⟩,
        ⟨110, false, false, [30722, 83025], []⟩,
        ⟨111, false, false, [30722, 83025], []⟩,
        ⟨18437, false, false, [30722], [1]⟩,
        ⟨18655, false, false, [30722], [1]⟩,
        ⟨18441, false, false, [30722], [1]⟩,
        ⟨18441, false, false, [30722], [1]⟩,
        ⟨18440, false, false, [30722], []⟩,
        ⟨18654, false, false, [30722], []⟩,
        ⟨18444, false, false, [30722], []⟩,
        ⟨18444, false, false, [30722], []⟩,
        ⟨81415, false, false, [30722], []⟩,
        ⟨81370, true, false, [], [83029]⟩
      ]⟩,
    ⟨[83029, 11], [30723, 93779], .contexts [
        ⟨81416, true, false, [30720], [11]⟩,
        ⟨53, false, false, [30720, 93779], []⟩,
        ⟨81286, true, false, [], [93779]⟩
      ]⟩,
    ⟨[30735, 85911], [30735, 85911], .contexts []⟩,
    ⟨[93779, 15], [30735, 85911], .contexts [
        ⟨81403, false, false, [], []⟩,
        ⟨81405, false, false, [], []⟩,
        ⟨81418, false, false, [], []⟩,
        ⟨81418, false, false, [], []⟩
      ]⟩,
    ⟨[85909, 15], [85909, 15], .contexts []⟩,
    ⟨[93777], [93777], .contexts []⟩,
    ⟨[85909, 15], [30733, 93777], .contexts [
        ⟨81420, false, false, [], []⟩,
        ⟨34184, true, false, [], [15]⟩,
        ⟨81419, true, false, [30734], [3, 15]⟩,
        ⟨1141, false, false, [30734, 93779], []⟩,
        ⟨21, false, false, [30734, 93779], []⟩,
        ⟨80980, false, false, [30734], []⟩,
        ⟨80981, false, false, [30734], []⟩,
        ⟨80904, false, false, [30734], []⟩,
        ⟨80904, false, false, [30734], []⟩,
        ⟨81421, false, false, [30734], []⟩,
        ⟨81388, true, false, [], [93777]⟩
      ]⟩,
    ⟨[90445, 11], [30751, 91337], .contexts [
        ⟨81409, false, false, [], []⟩,
        ⟨81410, false, false, [], []⟩
      ]⟩,
    ⟨[30751, 91337], [30751, 91337], .contexts []⟩,
    ⟨[91335, 11], [91335, 11], .contexts []⟩,
    ⟨[91335, 11], [30749, 90443], .contexts [
        ⟨81425, false, false, [], []⟩,
        ⟨65437, true, false, [], [11]⟩,
        ⟨81424, true, false, [30750], [3, 11]⟩,
        ⟨81424, true, false, [30750], [3, 11]⟩,
        ⟨81423, true, false, [30750], [3, 11]⟩,
        ⟨603, false, false, [30750, 90445], []⟩,
        ⟨21, false, false, [30750, 90445], []⟩,
        ⟨60739, false, false, [30750], []⟩,
        ⟨60740, false, false, [30750], []⟩,
        ⟨60645, false, false, [30750], []⟩,
        ⟨60645, false, false, [30750], []⟩,
        ⟨77789, false, false, [30750], []⟩,
        ⟨81394, true, false, [], [90443]⟩
      ]⟩,
    ⟨[30733, 93777], [30733, 93777], .contexts []⟩,
    ⟨[30733, 93777], [30733, 93777], .contexts []⟩,
    ⟨[85909, 15], [30733, 93777], .contexts [
        ⟨81420, false, false, [], []⟩,
        ⟨81422, false, false, [], []⟩,
        ⟨81427, false, false, [], []⟩,
        ⟨81428, false, false, [], []⟩,
        ⟨81428, false, false, [], []⟩
      ]⟩,
    ⟨[30733, 93773], [30733, 93773], .contexts []⟩,
    ⟨[85909], [85909], .contexts []⟩,
    ⟨[85909, 1], [85907], .contexts [
        ⟨34349, false, false, [], []⟩,
        ⟨34350, false, false, [], []⟩,
        ⟨34179, false, false, [], []⟩,
        ⟨34179, false, false, [], []⟩
      ]⟩,
    ⟨[85907], [30733, 93773], .contexts [
        ⟨81432, true, false, [], []⟩,
        ⟨81352, false, false, [30734], [85909, 1]⟩,
        ⟨81431, true, false, [30734, 30732], [1]⟩,
        ⟨504, true, false, [30734, 30732, 85909], [1]⟩,
        ⟨81429, false, false, [30734, 30732], [1, 15, 1, 1]⟩,
        ⟨80901, false, false, [30734], [15, 1, 1]⟩,
        ⟨80897, false, false, [30734], [1, 1]⟩,
        ⟨81430, false, false, [30734, 30732], [1, 1]⟩,
        ⟨8, false, false, [30734, 93773], []⟩,
        ⟨81354, true, false, [], [93773]⟩
      ]⟩,
    ⟨[93773], [30735, 85907], .contexts [
        ⟨81385, false, false, [30732], [93773]⟩,
        ⟨81430, true, false, [30732], []⟩,
        ⟨81433, true, false, [30732], []⟩,
        ⟨81306, true, false, [], [85907]⟩
      ]⟩,
    ⟨[30733], [30734], .contexts [
        ⟨81386, false, false, [], []⟩,
        ⟨81387, false, false, [], []⟩,
        ⟨81387, false, false, [], []⟩
      ]⟩,
    ⟨[85907, 13], [30733, 93771], .contexts [
        ⟨81434, true, false, [30734], [13]⟩,
        ⟨80893, false, false, [30734], []⟩,
        ⟨80984, false, false, [30734], []⟩,
        ⟨81435, true, false, [], [93771]⟩
      ]⟩,
    ⟨[93773], [30735, 85907], .contexts [
        ⟨81434, false, false, [], []⟩
      ]⟩,
    ⟨[30735, 85905], [30735, 85905], .contexts []⟩,
    ⟨[93775], [30735, 85905], .contexts [
        ⟨81386, false, false, [30732], [93775]⟩,
        ⟨13, false, false, [30732, 30734], [93775]⟩,
        ⟨80983, true, false, [30732, 30734], []⟩,
        ⟨80895, true, false, [30732, 30734], []⟩,
        ⟨81437, false, false, [30732, 30734], [15]⟩,
        ⟨34176, false, false, [30732], []⟩,
        ⟨81438, false, false, [30732, 30734], []⟩,
        ⟨81306, true, false, [], [85905]⟩
      ]⟩,
    ⟨[30749, 90443], [30749, 90443], .contexts []⟩,
    ⟨[30749, 90443], [30749, 90443], .contexts []⟩,
    ⟨[30749, 90441], [30749, 90441], .contexts []⟩,
    ⟨[90441, 11], [90441, 11], .contexts []⟩,
    ⟨[90441, 11], [30751, 91333], .contexts [
        ⟨81443, false, false, [], []⟩,
        ⟨81442, true, false, [30748], [11]⟩,
        ⟨60642, true, false, [], [11]⟩,
        ⟨81441, true, false, [30748], [1, 11]⟩,
        ⟨81441, true, false, [30748], [1, 11]⟩,
        ⟨81440, true, false, [30748], [1, 11]⟩,
        ⟨81426, true, false, [30748], [1, 11]⟩,
        ⟨81425, true, false, [30748], [1, 11]⟩,
        ⟨567, false, false, [30748, 91335], []⟩,
        ⟨9, false, false, [30748, 91335], []⟩,
        ⟨65519, false, false, [30748], []⟩,
        ⟨65520, false, false, [30748], []⟩,
        ⟨65433, false, false, [30748], []⟩,
        ⟨65433, false, false, [30748], []⟩,
        ⟨81362, true, false, [], [91333]⟩
      ]⟩,
    ⟨[30751, 91333], [30751, 91333], .contexts []⟩,
    ⟨[90441, 15], [90439], .contexts [
        ⟨60744, false, false, [], []⟩
      ]⟩,
    ⟨[91331, 11], [91331, 11], .contexts []⟩,
    ⟨[91331, 11], [30749, 90439], .contexts [
        ⟨81447, false, false, [], []⟩,
        ⟨65431, true, false, [], [11]⟩,
        ⟨81445, true, false, [30750], [15, 11]⟩,
        ⟨81445, true, false, [30750], [15, 11]⟩,
        ⟨81444, true, false, [30750], [15, 11]⟩,
        ⟨81443, true, false, [30750], [15, 11]⟩,
        ⟨615, false, false, [30750, 90441], []⟩,
        ⟨10, false, false, [30750, 90441], []⟩,
        ⟨81446, false, false, [30750], []⟩,
        ⟨60745, false, false, [30750], []⟩,
        ⟨60637, false, false, [30750], []⟩,
        ⟨60637, false, false, [30750], []⟩,
        ⟨81394, true, false, [], [90439]⟩
      ]⟩,
    ⟨[30749, 90439], [30749, 90439], .contexts []⟩,
    ⟨[30749, 90439], [30749, 90439], .contexts []⟩,
    ⟨[90437, 11], [90437, 11], .contexts []⟩,
    ⟨[90437, 11], [30751, 91329], .contexts [
        ⟨81451, false, false, [], []⟩,
        ⟨60634, true, false, [], [11]⟩,
        ⟨81450, true, false, [30748], [13, 11]⟩,
        ⟨81450, true, false, [30748], [13, 11]⟩,
        ⟨81449, true, false, [30748], [13, 11]⟩,
        ⟨81448, true, false, [30748], [13, 11]⟩,
        ⟨81447, true, false, [30748], [13, 11]⟩,
        ⟨619, false, false, [30748, 91331], []⟩,
        ⟨64, false, false, [30748, 91331], []⟩,
        ⟨65523, false, false, [30748], []⟩,
        ⟨65524, false, false, [30748], []⟩,
        ⟨65428, false, false, [30748], []⟩,
        ⟨65428, false, false, [30748], []⟩,
        ⟨81362, true, false, [], [91329]⟩
      ]⟩,
    ⟨[30751, 91329], [30751, 91329], .contexts []⟩,
    ⟨[30751, 91329], [30751, 91329], .contexts []⟩,
    ⟨[30751, 91325], [30751, 91325], .contexts []⟩,
    ⟨[91325, 1], [30749, 90437], .contexts [
        ⟨81455, true, false, [30750], [1]⟩,
        ⟨65423, true, false, [], [1]⟩,
        ⟨65426, true, false, [], [11, 1]⟩,
        ⟨81454, true, false, [30750], [1, 11, 1]⟩,
        ⟨81454, true, false, [30750], [1, 11, 1]⟩,
        ⟨81453, true, false, [30750], [1, 11, 1]⟩,
        ⟨81452, true, false, [30750], [1, 11, 1]⟩,
        ⟨81451, true, false, [30750], [1, 11, 1]⟩,
        ⟨628, false, false, [30750, 90437], []⟩,
        ⟨81394, true, false, [], [90437]⟩
      ]⟩,
    ⟨[30751], [30751], .contexts []⟩,
    ⟨[30751], [30751], .contexts []⟩,
    ⟨[91325], [30749, 90435], .contexts [
        ⟨81359, false, false, [30750], [91325]⟩,
        ⟨81457, false, false, [30750], [91325]⟩,
        ⟨81458, false, false, [30750], [91325]⟩,
        ⟨81455, true, false, [30750], []⟩,
        ⟨81358, false, false, [30750], [91325]⟩,
        ⟨8, true, false, [30750, 30748, 91325], []⟩,
        ⟨81456, false, false, [30750, 30748], [1]⟩,
        ⟨60747, false, false, [30750], []⟩,
        ⟨60748, false, false, [30750], []⟩,
        ⟨60631, false, false, [30750], []⟩,
        ⟨60631, false, false, [30750], []⟩,
        ⟨81364, true, false, [], [90435]⟩
      ]⟩,
    ⟨[30749, 90433], [30749, 90433], .contexts []⟩,
    ⟨[93811], [92177, 9], .source 46970⟩,
    ⟨[92177, 9], [93811], .contexts [
        ⟨81461, true, false, [], []⟩
      ]⟩,
    ⟨[92177, 9], [93811], .contexts [
        ⟨81462, false, false, [], []⟩
      ]⟩,
    ⟨[93811], [93811], .contexts []⟩,
    ⟨[93811], [93811], .contexts []⟩,
    ⟨[92177, 9], [93811], .contexts [
        ⟨81463, false, false, [], []⟩,
        ⟨81464, false, false, [], []⟩,
        ⟨81465, false, false, [], []⟩,
        ⟨81465, false, false, [], []⟩
      ]⟩,
    ⟨[93811, 5], [93811, 5], .contexts []⟩,
    ⟨[93811, 5], [92189], .contexts [
        ⟨81467, false, false, [], []⟩,
        ⟨81466, true, false, [], [5]⟩,
        ⟨1079, false, false, [92177], []⟩,
        ⟨1080, false, false, [92177], []⟩,
        ⟨70524, false, false, [], [9]⟩,
        ⟨70509, false, false, [], [9]⟩,
        ⟨70510, false, false, [], [9]⟩,
        ⟨70510, false, false, [], [9]⟩,
        ⟨70572, false, false, [], []⟩,
        ⟨70573, false, false, [], []⟩,
        ⟨70574, false, false, [], []⟩,
        ⟨70574, false, false, [], []⟩,
        ⟨70579, false, false, [], []⟩,
        ⟨672, true, false, [], [92189]⟩
      ]⟩,
    ⟨[92189, 5], [93811], .contexts [
        ⟨81468, true, false, [], [5]⟩,
        ⟨28, false, false, [93811], []⟩,
        ⟨81465, false, false, [], []⟩
      ]⟩,
    ⟨[93811, 7], [93811, 7], .contexts []⟩,
    ⟨[93811, 7], [84103], .contexts [
        ⟨81470, false, false, [], []⟩,
        ⟨81466, true, false, [], [7]⟩,
        ⟨1084, false, false, [92177], []⟩,
        ⟨1085, false, false, [92177], []⟩,
        ⟨70385, false, false, [], [9]⟩,
        ⟨24833, false, false, [], []⟩,
        ⟨24834, false, false, [], []⟩,
        ⟨24835, false, false, [], []⟩,
        ⟨24835, false, false, [], []⟩,
        ⟨24850, false, false, [], []⟩,
        ⟨672, true, false, [], [84103]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1273. -/
def y322TCIndexRaw1273 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[27423, 85707], [27423, 85707], .contexts []⟩,
    ⟨[85707], [85707], .contexts []⟩,
    ⟨[93811, 13], [27423, 85707], .contexts [
        ⟨81466, true, false, [], [13]⟩,
        ⟨201, false, false, [92177], []⟩,
        ⟨202, false, false, [92177], []⟩,
        ⟨70415, false, false, [], [9]⟩,
        ⟨33062, false, false, [27423], []⟩,
        ⟨81472, false, false, [], []⟩,
        ⟨81473, false, false, [27423], []⟩,
        ⟨13, true, false, [], [27423, 85707]⟩
      ]⟩,
    ⟨[93813], [93811, 11], .source 46971⟩,
    ⟨[93811, 11], [93813], .contexts [
        ⟨81475, true, false, [], []⟩
      ]⟩,
    ⟨[93813, 11], [93811], .contexts [
        ⟨81476, true, false, [], [11]⟩,
        ⟨53, false, false, [93811], []⟩,
        ⟨81465, false, false, [], []⟩
      ]⟩,
    ⟨[93811, 11], [93813], .contexts [
        ⟨81476, false, false, [], []⟩
      ]⟩,
    ⟨[93813], [93813], .contexts []⟩,
    ⟨[93813], [93813], .contexts []⟩,
    ⟨[93811, 11], [93813], .contexts [
        ⟨81478, false, false, [], []⟩,
        ⟨81479, false, false, [], []⟩,
        ⟨81480, false, false, [], []⟩,
        ⟨81480, false, false, [], []⟩
      ]⟩,
    ⟨[93813, 5], [93813, 5], .contexts []⟩,
    ⟨[93813, 5], [92191], .contexts [
        ⟨81482, false, false, [], []⟩,
        ⟨81481, true, false, [], [5]⟩,
        ⟨642, false, false, [93811], []⟩,
        ⟨643, false, false, [93811], []⟩,
        ⟨81467, false, false, [], [11]⟩,
        ⟨81468, false, false, [], [11]⟩,
        ⟨70573, false, false, [], [11]⟩,
        ⟨70574, false, false, [], [11]⟩,
        ⟨70574, false, false, [], [11]⟩,
        ⟨70592, false, false, [], []⟩,
        ⟨70593, false, false, [], []⟩,
        ⟨70594, false, false, [], []⟩,
        ⟨70594, false, false, [], []⟩,
        ⟨70600, false, false, [], []⟩,
        ⟨672, true, false, [], [92191]⟩
      ]⟩,
    ⟨[93813, 7], [93813, 7], .contexts []⟩,
    ⟨[93813, 7], [84105], .contexts [
        ⟨81484, false, false, [], []⟩,
        ⟨81481, true, false, [], [7]⟩,
        ⟨647, false, false, [93811], []⟩,
        ⟨648, false, false, [93811], []⟩,
        ⟨81470, false, false, [], [11]⟩,
        ⟨81471, false, false, [], [11]⟩,
        ⟨24834, false, false, [], [11]⟩,
        ⟨24835, false, false, [], [11]⟩,
        ⟨24835, false, false, [], [11]⟩,
        ⟨24855, false, false, [], []⟩,
        ⟨24856, false, false, [], []⟩,
        ⟨24857, false, false, [], []⟩,
        ⟨24857, false, false, [], []⟩,
        ⟨24871, false, false, [], []⟩,
        ⟨672, true, false, [], [84105]⟩
      ]⟩,
    ⟨[84105, 7], [93813], .contexts [
        ⟨81485, true, false, [], [7]⟩,
        ⟨38, false, false, [93813], []⟩,
        ⟨81480, false, false, [], []⟩
      ]⟩,
    ⟨[93815], [93813, 1], .source 46972⟩,
    ⟨[93813, 1], [93815], .contexts [
        ⟨81487, true, false, [], []⟩
      ]⟩,
    ⟨[93815, 1], [93813], .contexts [
        ⟨81488, true, false, [], [1]⟩,
        ⟨8, false, false, [93813], []⟩,
        ⟨81480, false, false, [], []⟩
      ]⟩,
    ⟨[93815], [93815], .contexts []⟩,
    ⟨[93815], [93815], .contexts []⟩,
    ⟨[93813, 1], [93815], .contexts [
        ⟨81488, false, false, [], []⟩,
        ⟨81490, false, false, [], []⟩,
        ⟨81491, false, false, [], []⟩,
        ⟨81491, false, false, [], []⟩
      ]⟩,
    ⟨[93815, 5], [93815, 5], .contexts []⟩,
    ⟨[93815, 5], [92193], .contexts [
        ⟨81493, false, false, [], []⟩,
        ⟨81492, true, false, [], [5]⟩,
        ⟨98, false, false, [93813], []⟩,
        ⟨99, false, false, [93813], []⟩,
        ⟨81482, false, false, [], [1]⟩,
        ⟨81483, false, false, [], [1]⟩,
        ⟨70593, false, false, [], [1]⟩,
        ⟨70594, false, false, [], [1]⟩,
        ⟨70594, false, false, [], [1]⟩,
        ⟨70612, false, false, [], []⟩,
        ⟨70613, false, false, [], []⟩,
        ⟨70614, false, false, [], []⟩,
        ⟨70614, false, false, [], []⟩,
        ⟨70619, false, false, [], []⟩,
        ⟨672, true, false, [], [92193]⟩
      ]⟩,
    ⟨[92193, 5], [93815], .contexts [
        ⟨81494, true, false, [], [5]⟩,
        ⟨28, false, false, [93815], []⟩,
        ⟨81491, false, false, [], []⟩
      ]⟩,
    ⟨[93815, 7], [93815, 7], .contexts []⟩,
    ⟨[93815, 7], [84107], .contexts [
        ⟨81496, false, false, [], []⟩,
        ⟨81492, true, false, [], [7]⟩,
        ⟨104, false, false, [93813], []⟩,
        ⟨105, false, false, [93813], []⟩,
        ⟨81484, false, false, [], [1]⟩,
        ⟨81485, false, false, [], [1]⟩,
        ⟨24856, false, false, [], [1]⟩,
        ⟨24857, false, false, [], [1]⟩,
        ⟨24857, false, false, [], [1]⟩,
        ⟨24876, false, false, [], []⟩,
        ⟨24877, false, false, [], []⟩,
        ⟨24878, false, false, [], []⟩,
        ⟨24878, false, false, [], []⟩,
        ⟨24887, false, false, [], []⟩,
        ⟨672, true, false, [], [84107]⟩
      ]⟩,
    ⟨[84107, 7], [93815], .contexts [
        ⟨81497, true, false, [], [7]⟩,
        ⟨38, false, false, [93815], []⟩,
        ⟨81491, false, false, [], []⟩
      ]⟩,
    ⟨[93815, 5], [92193], .contexts [
        ⟨81493, false, false, [], []⟩,
        ⟨81494, false, false, [], []⟩,
        ⟨70613, false, false, [], []⟩,
        ⟨70614, false, false, [], []⟩,
        ⟨70614, false, false, [], []⟩
      ]⟩,
    ⟨[93815], [93815], .contexts []⟩,
    ⟨[30113, 93815, 3], [93815], .contexts [
        ⟨81495, true, false, [30113], [3]⟩,
        ⟨79277, false, false, [], [92193, 5, 3]⟩,
        ⟨79223, true, false, [30111], [5, 3]⟩,
        ⟨79276, false, false, [], [93421, 3, 5, 3]⟩,
        ⟨79229, true, false, [30109], [3, 5, 3]⟩,
        ⟨79565, true, false, [], [5, 3, 5, 3]⟩,
        ⟨79565, true, false, [], [5, 3, 5, 3]⟩,
        ⟨79564, true, false, [], [5, 3, 5, 3]⟩,
        ⟨79225, true, false, [], [5, 3, 5, 3]⟩,
        ⟨81499, true, false, [], [3, 5, 3, 5, 3]⟩,
        ⟨7129, false, false, [93815], []⟩,
        ⟨81500, false, false, [], []⟩
      ]⟩,
    ⟨[93815, 3], [93815, 3], .contexts []⟩,
    ⟨[93815], [93815], .contexts []⟩,
    ⟨[93815, 3], [30115, 93815], .contexts [
        ⟨81502, false, false, [], []⟩,
        ⟨81501, false, false, [30112], []⟩,
        ⟨81503, false, false, [30112], []⟩,
        ⟨79279, true, false, [], [93815]⟩,
        ⟨79279, true, false, [], [93815]⟩,
        ⟨79278, true, false, [], [93815]⟩
      ]⟩,
    ⟨[93815, 9], [93815, 9], .contexts []⟩,
    ⟨[27478], [27478], .contexts []⟩,
    ⟨[93815, 9], [27477, 93815], .contexts [
        ⟨81505, false, false, [], []⟩,
        ⟨81495, true, false, [], [9]⟩,
        ⟨70643, true, false, [27478], [5, 9]⟩,
        ⟨70643, true, false, [27478], [5, 9]⟩,
        ⟨70642, true, false, [27478], [5, 9]⟩,
        ⟨70641, true, false, [27478], [5, 9]⟩,
        ⟨81499, true, false, [27478], [9, 5, 9]⟩,
        ⟨882, false, false, [27478, 93815], []⟩,
        ⟨81500, false, false, [27478], []⟩,
        ⟨81503, false, false, [27478], []⟩,
        ⟨81506, true, false, [], [93815]⟩,
        ⟨81506, true, false, [], [93815]⟩,
        ⟨70630, false, true, [], [93815]⟩
      ]⟩,
    ⟨[93817], [93815, 13], .source 46973⟩,
    ⟨[93815, 13], [93817], .contexts [
        ⟨81508, true, false, [], []⟩
      ]⟩,
    ⟨[93817, 13], [93815], .contexts [
        ⟨81509, true, false, [], [13]⟩,
        ⟨59, false, false, [93815], []⟩,
        ⟨81491, false, false, [], []⟩
      ]⟩,
    ⟨[93817], [93817], .contexts []⟩,
    ⟨[93817], [93817], .contexts []⟩,
    ⟨[93815, 13], [93817], .contexts [
        ⟨81509, false, false, [], []⟩,
        ⟨81511, false, false, [], []⟩,
        ⟨81512, false, false, [], []⟩,
        ⟨81512, false, false, [], []⟩
      ]⟩,
    ⟨[30115, 93815], [30115, 93815], .contexts []⟩,
    ⟨[30115, 93815], [30115, 93815], .contexts []⟩,
    ⟨[30115, 93817], [30115, 93817], .contexts []⟩,
    ⟨[30115, 93817], [30115, 93817], .contexts []⟩,
    ⟨[30115, 93817], [30115, 93817], .contexts []⟩,
    ⟨[93817, 3], [93817, 3], .contexts []⟩,
    ⟨[93817], [93817], .contexts []⟩,
    ⟨[30115], [30115], .contexts [
        ⟨13, false, false, [], [30115]⟩
      ]⟩,
    ⟨[93817, 3], [30115, 93817], .contexts [
        ⟨81519, false, false, [], []⟩,
        ⟨81513, true, false, [], [3]⟩,
        ⟨63, false, false, [93815], []⟩,
        ⟨65, false, false, [93815], []⟩,
        ⟨81502, false, false, [], [13]⟩,
        ⟨81504, false, false, [], [13]⟩,
        ⟨81514, false, false, [], [13]⟩,
        ⟨81515, false, false, [], [13]⟩,
        ⟨81515, false, false, [], [13]⟩,
        ⟨81509, false, false, [30115], []⟩,
        ⟨81516, false, false, [], []⟩,
        ⟨81517, false, false, [], []⟩,
        ⟨81518, false, false, [], []⟩,
        ⟨81520, false, false, [30115], []⟩,
        ⟨81521, true, false, [], [93817]⟩
      ]⟩,
    ⟨[93817, 5], [93817, 5], .contexts []⟩,
    ⟨[93817, 5], [92195], .contexts [
        ⟨81523, false, false, [], []⟩,
        ⟨81513, true, false, [], [5]⟩,
        ⟨68, false, false, [93815], []⟩,
        ⟨69, false, false, [93815], []⟩,
        ⟨81499, false, false, [], [13]⟩,
        ⟨70636, false, false, [], []⟩,
        ⟨70637, false, false, [], []⟩,
        ⟨70638, false, false, [], []⟩,
        ⟨70638, false, false, [], []⟩,
        ⟨70640, false, false, [], []⟩,
        ⟨672, true, false, [], [92195]⟩
      ]⟩,
    ⟨[92195, 5], [93817], .contexts [
        ⟨81524, true, false, [], [5]⟩,
        ⟨28, false, false, [93817], []⟩,
        ⟨81512, false, false, [], []⟩
      ]⟩,
    ⟨[93817, 7], [93817, 7], .contexts []⟩,
    ⟨[84109], [84109], .contexts [
        ⟨24906, false, false, [], []⟩
      ]⟩,
    ⟨[84109], [84109], .contexts [
        ⟨672, true, false, [], [84109]⟩
      ]⟩,
    ⟨[93817, 7], [84109], .contexts [
        ⟨81526, false, false, [], []⟩,
        ⟨81513, true, false, [], [7]⟩,
        ⟨73, false, false, [93815], []⟩,
        ⟨74, false, false, [93815], []⟩,
        ⟨81496, false, false, [], [13]⟩,
        ⟨81497, false, false, [], [13]⟩,
        ⟨24877, false, false, [], [13]⟩,
        ⟨24878, false, false, [], [13]⟩,
        ⟨24878, false, false, [], [13]⟩,
        ⟨24898, false, false, [], []⟩,
        ⟨24899, false, false, [], []⟩,
        ⟨24900, false, false, [], []⟩,
        ⟨24900, false, false, [], []⟩,
        ⟨81527, false, false, [], []⟩,
        ⟨81528, false, false, [], []⟩
      ]⟩,
    ⟨[27477, 93815], [27477, 93815], .contexts []⟩,
    ⟨[27477, 93815], [27477, 93815], .contexts []⟩,
    ⟨[93817, 7], [84109], .contexts [
        ⟨81526, false, false, [], []⟩,
        ⟨81529, false, false, [], []⟩,
        ⟨24899, false, false, [], []⟩,
        ⟨24900, false, false, [], []⟩,
        ⟨24900, false, false, [], []⟩
      ]⟩,
    ⟨[28257, 90735], [28257, 90735], .contexts []⟩,
    ⟨[28257, 90735], [28257, 90735], .contexts []⟩,
    ⟨[30753], [28257, 27041], .source 15441⟩]

/-- Exact literal claimed equations and contextual derivations, block 1274. -/
def y322TCIndexRaw1274 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[30755], [30752], .source 15442⟩,
    ⟨[30752], [30752], .contexts []⟩,
    ⟨[92031, 11], [30755, 93817], .contexts [
        ⟨81535, false, false, [30752], [92031, 11]⟩,
        ⟨69177, true, false, [30752, 28257], [11]⟩,
        ⟨81534, true, false, [30752], [7, 11]⟩,
        ⟨81534, true, false, [30752], [7, 11]⟩,
        ⟨81533, true, false, [30752], [7, 11]⟩,
        ⟨73266, true, false, [30752], [7, 11]⟩,
        ⟨81532, true, false, [30752], [11, 7, 11]⟩,
        ⟨2806, false, false, [30752, 93817], []⟩,
        ⟨81520, false, false, [30752], []⟩,
        ⟨81537, true, false, [], [93817]⟩,
        ⟨81537, true, false, [], [93817]⟩,
        ⟨81536, true, false, [], [93817]⟩
      ]⟩,
    ⟨[93817, 11], [30753, 92031], .contexts [
        ⟨81538, true, false, [30754], [11]⟩,
        ⟨53, false, false, [30754, 92031], []⟩,
        ⟨81536, false, true, [], [92031]⟩
      ]⟩,
    ⟨[93819], [93817, 15], .source 46974⟩,
    ⟨[93817, 15], [93819], .contexts [
        ⟨81540, true, false, [], []⟩
      ]⟩,
    ⟨[93819, 15], [93817], .contexts [
        ⟨81541, true, false, [], [15]⟩,
        ⟨1, false, false, [93817], []⟩,
        ⟨81512, false, false, [], []⟩
      ]⟩,
    ⟨[93819], [93819], .contexts []⟩,
    ⟨[93819], [93819], .contexts []⟩,
    ⟨[93817, 15], [93819], .contexts [
        ⟨81541, false, false, [], []⟩,
        ⟨81543, false, false, [], []⟩,
        ⟨81544, false, false, [], []⟩,
        ⟨81544, false, false, [], []⟩
      ]⟩,
    ⟨[30115, 93819], [30115, 93819], .contexts []⟩,
    ⟨[30115, 93819], [30115, 93819], .contexts []⟩,
    ⟨[30115, 93819], [30115, 93819], .contexts []⟩,
    ⟨[93819, 5], [93819, 5], .contexts []⟩,
    ⟨[93819, 5], [92197], .contexts [
        ⟨81549, false, false, [], []⟩,
        ⟨81545, true, false, [], [5]⟩,
        ⟨27, false, false, [93817], []⟩,
        ⟨30, false, false, [93817], []⟩,
        ⟨81523, false, false, [], [15]⟩,
        ⟨81524, false, false, [], [15]⟩,
        ⟨70637, false, false, [], [15]⟩,
        ⟨70638, false, false, [], [15]⟩,
        ⟨70638, false, false, [], [15]⟩,
        ⟨70647, false, false, [], []⟩,
        ⟨70648, false, false, [], []⟩,
        ⟨70649, false, false, [], []⟩,
        ⟨70649, false, false, [], []⟩,
        ⟨70650, false, false, [], []⟩,
        ⟨672, true, false, [], [92197]⟩
      ]⟩,
    ⟨[93819, 7], [93819, 7], .contexts []⟩,
    ⟨[93819, 7], [84111], .contexts [
        ⟨81551, false, false, [], []⟩,
        ⟨81545, true, false, [], [7]⟩,
        ⟨37, false, false, [93817], []⟩,
        ⟨40, false, false, [93817], []⟩,
        ⟨81532, false, false, [], [15]⟩,
        ⟨24915, false, false, [], []⟩,
        ⟨24916, false, false, [], []⟩,
        ⟨24917, false, false, [], []⟩,
        ⟨24917, false, false, [], []⟩,
        ⟨24922, false, false, [], []⟩,
        ⟨672, true, false, [], [84111]⟩
      ]⟩,
    ⟨[93821], [93819, 1], .source 46975⟩,
    ⟨[93819, 1], [93821], .contexts [
        ⟨81553, true, false, [], []⟩
      ]⟩,
    ⟨[93821, 1], [93819], .contexts [
        ⟨81554, true, false, [], [1]⟩,
        ⟨8, false, false, [93819], []⟩,
        ⟨81544, false, false, [], []⟩
      ]⟩,
    ⟨[93821], [93821], .contexts []⟩,
    ⟨[93821], [93821], .contexts []⟩,
    ⟨[93819, 1], [93821], .contexts [
        ⟨81554, false, false, [], []⟩,
        ⟨81556, false, false, [], []⟩,
        ⟨81557, false, false, [], []⟩,
        ⟨81557, false, false, [], []⟩
      ]⟩,
    ⟨[93821, 5], [92199], .contexts [
        ⟨81558, true, false, [], [5]⟩,
        ⟨98, false, false, [93819], []⟩,
        ⟨99, false, false, [93819], []⟩,
        ⟨81549, false, false, [], [1]⟩,
        ⟨81550, false, false, [], [1]⟩,
        ⟨70648, false, false, [], [1]⟩,
        ⟨70649, false, false, [], [1]⟩,
        ⟨70649, false, false, [], [1]⟩,
        ⟨70655, false, false, [], []⟩,
        ⟨70656, false, false, [], []⟩,
        ⟨70657, false, false, [], []⟩,
        ⟨70657, false, false, [], []⟩,
        ⟨70658, false, false, [], []⟩,
        ⟨672, true, false, [], [92199]⟩
      ]⟩,
    ⟨[93821, 7], [93821, 7], .contexts []⟩,
    ⟨[93821, 7], [84113], .contexts [
        ⟨81560, false, false, [], []⟩,
        ⟨81558, true, false, [], [7]⟩,
        ⟨104, false, false, [93819], []⟩,
        ⟨105, false, false, [93819], []⟩,
        ⟨81551, false, false, [], [1]⟩,
        ⟨81552, false, false, [], [1]⟩,
        ⟨24916, false, false, [], [1]⟩,
        ⟨24917, false, false, [], [1]⟩,
        ⟨24917, false, false, [], [1]⟩,
        ⟨24931, false, false, [], []⟩,
        ⟨24932, false, false, [], []⟩,
        ⟨24933, false, false, [], []⟩,
        ⟨24933, false, false, [], []⟩,
        ⟨24937, false, false, [], []⟩,
        ⟨672, true, false, [], [84113]⟩
      ]⟩,
    ⟨[84113, 7], [93821], .contexts [
        ⟨81561, true, false, [], [7]⟩,
        ⟨38, false, false, [93821], []⟩,
        ⟨81557, false, false, [], []⟩
      ]⟩,
    ⟨[93823], [93821, 3], .source 46976⟩,
    ⟨[93821, 3], [93823], .contexts [
        ⟨81563, true, false, [], []⟩
      ]⟩,
    ⟨[93823, 3], [93821], .contexts [
        ⟨81564, true, false, [], [3]⟩,
        ⟨20, false, false, [93821], []⟩,
        ⟨81557, false, false, [], []⟩
      ]⟩,
    ⟨[93823], [93823], .contexts []⟩,
    ⟨[93821, 3], [93823], .contexts [
        ⟨81564, false, false, [], []⟩,
        ⟨81566, false, false, [], []⟩,
        ⟨81566, false, false, [], []⟩
      ]⟩,
    ⟨[30115, 93821], [30115, 93821], .contexts []⟩,
    ⟨[30115, 93821], [30115, 93821], .contexts []⟩,
    ⟨[93821, 1, 3, 1], [30115, 93821], .contexts [
        ⟨81555, false, false, [], [3, 1]⟩,
        ⟨81543, false, false, [], [3, 1]⟩,
        ⟨81544, false, false, [], [3, 1]⟩,
        ⟨81544, false, false, [], [3, 1]⟩,
        ⟨81545, true, false, [], [3, 1]⟩,
        ⟨19, false, false, [93817], [1]⟩,
        ⟨22, false, false, [93817], [1]⟩,
        ⟨81519, false, false, [], [15, 1]⟩,
        ⟨81522, false, false, [], [15, 1]⟩,
        ⟨81516, false, false, [], [15, 1]⟩,
        ⟨81518, false, false, [], [15, 1]⟩,
        ⟨81518, false, false, [], [15, 1]⟩,
        ⟨81541, false, false, [30115], [1]⟩,
        ⟨81546, false, false, [], [1]⟩,
        ⟨81547, false, false, [], [1]⟩,
        ⟨81548, false, false, [], [1]⟩,
        ⟨81521, true, false, [], [93819, 1]⟩,
        ⟨81546, false, false, [], [1]⟩,
        ⟨81548, false, false, [], [1]⟩,
        ⟨81548, false, false, [], [1]⟩,
        ⟨81554, false, false, [30115], []⟩,
        ⟨81568, false, false, [], []⟩,
        ⟨81569, false, false, [], []⟩
      ]⟩,
    ⟨[30115, 93821], [30115, 93821], .contexts []⟩,
    ⟨[30115, 93823], [30115, 93823], .contexts []⟩,
    ⟨[30115, 93823], [30115, 93823], .contexts []⟩,
    ⟨[30115, 93823], [30115, 93823], .contexts []⟩,
    ⟨[93823, 1], [93823, 1], .contexts []⟩,
    ⟨[93823, 7], [84115], .contexts [
        ⟨81567, true, false, [], [7]⟩,
        ⟨140, false, false, [93821], []⟩,
        ⟨141, false, false, [93821], []⟩,
        ⟨81560, false, false, [], [3]⟩,
        ⟨81561, false, false, [], [3]⟩,
        ⟨24932, false, false, [], [3]⟩,
        ⟨24933, false, false, [], [3]⟩,
        ⟨24933, false, false, [], [3]⟩,
        ⟨24942, false, false, [], []⟩,
        ⟨24943, false, false, [], []⟩,
        ⟨24944, false, false, [], []⟩,
        ⟨24944, false, false, [], []⟩,
        ⟨24954, false, false, [], []⟩,
        ⟨672, true, false, [], [84115]⟩
      ]⟩,
    ⟨[93825], [93823, 5], .source 46977⟩,
    ⟨[93823, 5], [93825], .contexts [
        ⟨81577, true, false, [], []⟩
      ]⟩,
    ⟨[93825, 5], [93823], .contexts [
        ⟨81578, true, false, [], [5]⟩,
        ⟨28, false, false, [93823], []⟩,
        ⟨81566, false, false, [], []⟩
      ]⟩,
    ⟨[93825], [93825], .contexts []⟩,
    ⟨[93825], [93825], .contexts []⟩,
    ⟨[93823, 5], [93825], .contexts [
        ⟨81578, false, false, [], []⟩,
        ⟨81580, false, false, [], []⟩,
        ⟨81581, false, false, [], []⟩,
        ⟨81581, false, false, [], []⟩
      ]⟩,
    ⟨[30115, 93825], [30115, 93825], .contexts []⟩,
    ⟨[30115, 93825], [30115, 93825], .contexts []⟩,
    ⟨[93825, 1], [30115, 93825], .contexts [
        ⟨81582, true, false, [], [1]⟩,
        ⟨161, false, false, [93823], []⟩,
        ⟨162, false, false, [93823], []⟩,
        ⟨81575, false, false, [], [5]⟩,
        ⟨81575, false, false, [], [5]⟩,
        ⟨81567, true, false, [], [1, 5]⟩,
        ⟨130, false, false, [93821], [5]⟩,
        ⟨133, false, false, [93821], [5]⟩,
        ⟨81570, false, false, [], [3, 5]⟩,
        ⟨81571, false, false, [], [3, 5]⟩,
        ⟨81564, false, false, [30115], [5]⟩,
        ⟨81572, false, false, [], [5]⟩,
        ⟨81573, false, false, [], [5]⟩,
        ⟨81574, false, false, [], [5]⟩,
        ⟨81521, true, false, [], [93823, 5]⟩,
        ⟨81572, false, false, [], [5]⟩,
        ⟨81574, false, false, [], [5]⟩,
        ⟨81574, false, false, [], [5]⟩,
        ⟨81578, false, false, [30115], []⟩,
        ⟨81583, false, false, [], []⟩,
        ⟨81584, false, false, [], []⟩
      ]⟩,
    ⟨[93825], [93825], .contexts []⟩,
    ⟨[93825, 1], [30115, 93825], .contexts [
        ⟨81585, false, false, [], []⟩,
        ⟨81586, false, false, [30115], []⟩,
        ⟨81521, true, false, [], [93825]⟩
      ]⟩,
    ⟨[93825, 3], [93825, 3], .contexts []⟩,
    ⟨[92203], [92203], .contexts []⟩,
    ⟨[93825, 3], [92203], .contexts [
        ⟨81588, false, false, [], []⟩,
        ⟨81582, true, false, [], [3]⟩,
        ⟨166, false, false, [93823], []⟩,
        ⟨169, false, false, [93823], []⟩,
        ⟨81565, false, false, [], [5, 3, 5]⟩,
        ⟨81556, false, false, [], [5, 3, 5]⟩,
        ⟨81557, false, false, [], [5, 3, 5]⟩,
        ⟨81557, false, false, [], [5, 3, 5]⟩,
        ⟨81559, false, false, [], [3, 5]⟩,
        ⟨70656, false, false, [], [3, 5]⟩,
        ⟨70657, false, false, [], [3, 5]⟩,
        ⟨70657, false, false, [], [3, 5]⟩,
        ⟨70660, false, false, [], [5]⟩,
        ⟨70661, false, false, [], [5]⟩,
        ⟨70662, false, false, [], [5]⟩,
        ⟨70662, false, false, [], [5]⟩,
        ⟨70665, false, false, [], []⟩,
        ⟨70826, false, false, [], []⟩,
        ⟨70668, false, false, [], []⟩,
        ⟨70668, false, false, [], []⟩,
        ⟨81589, false, false, [], []⟩
      ]⟩,
    ⟨[93825, 3], [92203], .contexts [
        ⟨81590, false, false, [], []⟩,
        ⟨672, true, false, [], [92203]⟩
      ]⟩,
    ⟨[93827], [93825, 9], .source 46978⟩,
    ⟨[93825, 9], [93827], .contexts [
        ⟨81592, true, false, [], []⟩
      ]⟩,
    ⟨[93827], [93827], .contexts []⟩,
    ⟨[93827], [93827], .contexts []⟩,
    ⟨[93827, 3], [93827, 3], .contexts []⟩,
    ⟨[93829], [93827, 11], .source 46979⟩,
    ⟨[93827, 11], [93829], .contexts [
        ⟨81597, true, false, [], []⟩
      ]⟩,
    ⟨[93829], [93829], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1275. -/
def y322TCIndexRaw1275 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93829], [93829], .contexts []⟩,
    ⟨[93827, 3, 11], [93433], .contexts [
        ⟨81596, false, false, [], [11]⟩,
        ⟨81596, false, false, [], [11]⟩,
        ⟨81595, true, false, [], [3, 11]⟩,
        ⟨81595, true, false, [], [3, 11]⟩,
        ⟨81594, true, false, [], [3, 11]⟩,
        ⟨81593, true, false, [], [3, 11]⟩,
        ⟨196, false, false, [93825], [11]⟩,
        ⟨197, false, false, [93825], [11]⟩,
        ⟨81588, false, false, [], [9, 11]⟩,
        ⟨81591, false, false, [], [9, 11]⟩,
        ⟨70826, false, false, [], [9, 11]⟩,
        ⟨70668, false, false, [], [9, 11]⟩,
        ⟨70668, false, false, [], [9, 11]⟩,
        ⟨79281, false, false, [], [11]⟩,
        ⟨79561, false, false, [], [11]⟩,
        ⟨79284, false, false, [], [11]⟩,
        ⟨79284, false, false, [], [11]⟩,
        ⟨672, true, false, [], [93431, 11]⟩,
        ⟨79561, false, false, [], [11]⟩,
        ⟨79284, false, false, [], [11]⟩,
        ⟨79284, false, false, [], [11]⟩,
        ⟨79283, false, false, [], []⟩,
        ⟨79559, false, false, [], []⟩,
        ⟨79287, false, false, [], []⟩
      ]⟩,
    ⟨[93831], [93829, 1], .source 46980⟩,
    ⟨[93829, 1], [93831], .contexts [
        ⟨81602, true, false, [], []⟩
      ]⟩,
    ⟨[93831, 1], [93829], .contexts [
        ⟨81603, true, false, [], [1]⟩,
        ⟨8, false, false, [93829], []⟩,
        ⟨81600, false, false, [], []⟩
      ]⟩,
    ⟨[93833], [93831, 13], .source 46981⟩,
    ⟨[93831, 13], [93833], .contexts [
        ⟨81605, true, false, [], []⟩
      ]⟩,
    ⟨[93831], [93831], .contexts []⟩,
    ⟨[93833, 13], [93831], .contexts [
        ⟨81606, true, false, [], [13]⟩,
        ⟨59, false, false, [93831], []⟩,
        ⟨81607, false, false, [], []⟩
      ]⟩,
    ⟨[93835], [93833, 15], .source 46982⟩,
    ⟨[93833, 15], [93835], .contexts [
        ⟨81609, true, false, [], []⟩
      ]⟩,
    ⟨[93833], [93833], .contexts []⟩,
    ⟨[93837], [93835, 1], .source 46983⟩,
    ⟨[93835, 1], [93837], .contexts [
        ⟨81612, true, false, [], []⟩
      ]⟩,
    ⟨[93835], [93835], .contexts []⟩,
    ⟨[93839], [93837, 3], .source 46984⟩,
    ⟨[93837, 3], [93839], .contexts [
        ⟨81615, true, false, [], []⟩
      ]⟩,
    ⟨[93837], [93837], .contexts []⟩,
    ⟨[93841], [93839, 5], .source 46985⟩,
    ⟨[93839, 5], [93841], .contexts [
        ⟨81618, true, false, [], []⟩
      ]⟩,
    ⟨[93839], [93839], .contexts []⟩,
    ⟨[93843], [93841, 1], .source 46986⟩,
    ⟨[93841, 1], [93843], .contexts [
        ⟨81621, true, false, [], []⟩
      ]⟩,
    ⟨[93841], [93841], .contexts []⟩,
    ⟨[93845], [93843, 9], .source 46987⟩,
    ⟨[93843, 9], [93845], .contexts [
        ⟨81624, true, false, [], []⟩
      ]⟩,
    ⟨[93843], [93843], .contexts []⟩,
    ⟨[93845, 9], [93843], .contexts [
        ⟨81625, true, false, [], [9]⟩,
        ⟨46, false, false, [93843], []⟩,
        ⟨81626, false, false, [], []⟩
      ]⟩,
    ⟨[93847], [93845, 11], .source 46988⟩,
    ⟨[93845, 11], [93847], .contexts [
        ⟨81628, true, false, [], []⟩
      ]⟩,
    ⟨[93845], [93845], .contexts []⟩,
    ⟨[93849], [93847, 1], .source 46989⟩,
    ⟨[93847, 1], [93849], .contexts [
        ⟨81631, true, false, [], []⟩
      ]⟩,
    ⟨[93847], [93847], .contexts []⟩,
    ⟨[93849, 1], [93847], .contexts [
        ⟨81632, true, false, [], [1]⟩,
        ⟨8, false, false, [93847], []⟩,
        ⟨81633, false, false, [], []⟩
      ]⟩,
    ⟨[93851], [93849, 13], .source 46990⟩,
    ⟨[93849, 13], [93851], .contexts [
        ⟨81635, true, false, [], []⟩
      ]⟩,
    ⟨[93849], [93849], .contexts []⟩,
    ⟨[93853], [93851, 15], .source 46991⟩,
    ⟨[93851, 15], [93853], .contexts [
        ⟨81638, true, false, [], []⟩
      ]⟩,
    ⟨[93851], [93851], .contexts []⟩,
    ⟨[93855], [93853, 1], .source 46992⟩,
    ⟨[93853, 1], [93855], .contexts [
        ⟨81641, true, false, [], []⟩
      ]⟩,
    ⟨[93853], [93853], .contexts []⟩,
    ⟨[93857], [93855, 3], .source 46993⟩,
    ⟨[93855, 3], [93857], .contexts [
        ⟨81644, true, false, [], []⟩
      ]⟩,
    ⟨[93855], [93855], .contexts []⟩,
    ⟨[93859], [93857, 5], .source 46994⟩,
    ⟨[93857, 5], [93859], .contexts [
        ⟨81647, true, false, [], []⟩
      ]⟩,
    ⟨[93857], [93857], .contexts []⟩,
    ⟨[93859, 5], [93857], .contexts [
        ⟨81648, true, false, [], [5]⟩,
        ⟨28, false, false, [93857], []⟩,
        ⟨81649, false, false, [], []⟩
      ]⟩,
    ⟨[93861], [93859, 1], .source 46995⟩,
    ⟨[93859, 1], [93861], .contexts [
        ⟨81651, true, false, [], []⟩
      ]⟩,
    ⟨[93859], [93859], .contexts []⟩,
    ⟨[93861, 1], [93859], .contexts [
        ⟨81652, true, false, [], [1]⟩,
        ⟨8, false, false, [93859], []⟩,
        ⟨81653, false, false, [], []⟩
      ]⟩,
    ⟨[93863], [93861, 9], .source 46996⟩,
    ⟨[93861, 9], [93863], .contexts [
        ⟨81655, true, false, [], []⟩
      ]⟩,
    ⟨[93861], [93861], .contexts []⟩,
    ⟨[93865], [93863, 11], .source 46997⟩,
    ⟨[93863, 11], [93865], .contexts [
        ⟨81658, true, false, [], []⟩
      ]⟩,
    ⟨[93863], [93863], .contexts []⟩,
    ⟨[93865, 11], [93863], .contexts [
        ⟨81659, true, false, [], [11]⟩,
        ⟨53, false, false, [93863], []⟩,
        ⟨81660, false, false, [], []⟩
      ]⟩,
    ⟨[93867], [93865, 1], .source 46998⟩,
    ⟨[93865, 1], [93867], .contexts [
        ⟨81662, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1276. -/
def y322TCIndexRaw1276 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93865], [93865], .contexts []⟩,
    ⟨[93867, 1], [93865], .contexts [
        ⟨81663, true, false, [], [1]⟩,
        ⟨8, false, false, [93865], []⟩,
        ⟨81664, false, false, [], []⟩
      ]⟩,
    ⟨[93869], [93867, 13], .source 46999⟩,
    ⟨[93867, 13], [93869], .contexts [
        ⟨81666, true, false, [], []⟩
      ]⟩,
    ⟨[93867], [93867], .contexts []⟩,
    ⟨[93869, 13], [93867], .contexts [
        ⟨81667, true, false, [], [13]⟩,
        ⟨59, false, false, [93867], []⟩,
        ⟨81668, false, false, [], []⟩
      ]⟩,
    ⟨[93871], [93869, 15], .source 47000⟩,
    ⟨[93869], [93869], .contexts []⟩,
    ⟨[93871, 15], [93869], .contexts [
        ⟨81670, false, false, [], [15]⟩,
        ⟨1, false, false, [93869], []⟩,
        ⟨81671, false, false, [], []⟩
      ]⟩,
    ⟨[93873], [93871, 1], .source 47001⟩,
    ⟨[93871, 1], [93873], .contexts [
        ⟨81673, true, false, [], []⟩
      ]⟩,
    ⟨[93871], [93871], .contexts []⟩,
    ⟨[93873, 1], [93871], .contexts [
        ⟨81674, true, false, [], [1]⟩,
        ⟨8, false, false, [93871], []⟩,
        ⟨81675, false, false, [], []⟩
      ]⟩,
    ⟨[93875], [93873, 3], .source 47002⟩,
    ⟨[93873], [93873], .contexts []⟩,
    ⟨[93875, 3], [93873], .contexts [
        ⟨81677, false, false, [], [3]⟩,
        ⟨20, false, false, [93873], []⟩,
        ⟨81678, false, false, [], []⟩
      ]⟩,
    ⟨[93877], [93875, 5], .source 47003⟩,
    ⟨[93875], [93875], .contexts []⟩,
    ⟨[93877, 5], [93875], .contexts [
        ⟨81680, false, false, [], [5]⟩,
        ⟨28, false, false, [93875], []⟩,
        ⟨81681, false, false, [], []⟩
      ]⟩,
    ⟨[93879], [93877, 1], .source 47004⟩,
    ⟨[93877], [93877], .contexts []⟩,
    ⟨[93879, 1], [93877], .contexts [
        ⟨81683, false, false, [], [1]⟩,
        ⟨8, false, false, [93877], []⟩,
        ⟨81684, false, false, [], []⟩
      ]⟩,
    ⟨[93881], [93879, 9], .source 47005⟩,
    ⟨[93879], [93879], .contexts []⟩,
    ⟨[93881, 9], [93879], .contexts [
        ⟨81686, false, false, [], [9]⟩,
        ⟨46, false, false, [93879], []⟩,
        ⟨81687, false, false, [], []⟩
      ]⟩,
    ⟨[93883], [93881, 11], .source 47006⟩,
    ⟨[93881], [93881], .contexts []⟩,
    ⟨[93883, 11], [93881], .contexts [
        ⟨81689, false, false, [], [11]⟩,
        ⟨53, false, false, [93881], []⟩,
        ⟨81690, false, false, [], []⟩
      ]⟩,
    ⟨[93885], [93883, 1], .source 47007⟩,
    ⟨[93883], [93883], .contexts []⟩,
    ⟨[93885, 1], [93883], .contexts [
        ⟨81692, false, false, [], [1]⟩,
        ⟨8, false, false, [93883], []⟩,
        ⟨81693, false, false, [], []⟩
      ]⟩,
    ⟨[93887], [93885, 13], .source 47008⟩,
    ⟨[93885], [93885], .contexts []⟩,
    ⟨[93887, 13], [93885], .contexts [
        ⟨81695, false, false, [], [13]⟩,
        ⟨59, false, false, [93885], []⟩,
        ⟨81696, false, false, [], []⟩
      ]⟩,
    ⟨[93889], [93887, 15], .source 47009⟩,
    ⟨[93887, 15], [93889], .contexts [
        ⟨81698, true, false, [], []⟩
      ]⟩,
    ⟨[93887], [93887], .contexts []⟩,
    ⟨[93889, 15], [93887], .contexts [
        ⟨81699, true, false, [], [15]⟩,
        ⟨1, false, false, [93887], []⟩,
        ⟨81700, false, false, [], []⟩
      ]⟩,
    ⟨[93891], [93889, 1], .source 47010⟩,
    ⟨[93889, 1], [93891], .contexts [
        ⟨81702, true, false, [], []⟩
      ]⟩,
    ⟨[93889], [93889], .contexts []⟩,
    ⟨[93891, 1], [93889], .contexts [
        ⟨81703, true, false, [], [1]⟩,
        ⟨8, false, false, [93889], []⟩,
        ⟨81704, false, false, [], []⟩
      ]⟩,
    ⟨[93893], [93891, 3], .source 47011⟩,
    ⟨[93891], [93891], .contexts []⟩,
    ⟨[93893, 3], [93891], .contexts [
        ⟨81706, false, false, [], [3]⟩,
        ⟨20, false, false, [93891], []⟩,
        ⟨81707, false, false, [], []⟩
      ]⟩,
    ⟨[93895], [93893, 5], .source 47012⟩,
    ⟨[93893], [93893], .contexts []⟩,
    ⟨[93895, 5], [93893], .contexts [
        ⟨81709, false, false, [], [5]⟩,
        ⟨28, false, false, [93893], []⟩,
        ⟨81710, false, false, [], []⟩
      ]⟩,
    ⟨[93897], [93895, 1], .source 47013⟩,
    ⟨[93895], [93895], .contexts []⟩,
    ⟨[93897, 1], [93895], .contexts [
        ⟨81712, false, false, [], [1]⟩,
        ⟨8, false, false, [93895], []⟩,
        ⟨81713, false, false, [], []⟩
      ]⟩,
    ⟨[93899], [93897, 9], .source 47014⟩,
    ⟨[93897, 9], [93899], .contexts [
        ⟨81715, true, false, [], []⟩
      ]⟩,
    ⟨[93897], [93897], .contexts []⟩,
    ⟨[93899, 9], [93897], .contexts [
        ⟨81716, true, false, [], [9]⟩,
        ⟨46, false, false, [93897], []⟩,
        ⟨81717, false, false, [], []⟩
      ]⟩,
    ⟨[93901], [93899, 11], .source 47015⟩,
    ⟨[93899, 11], [93901], .contexts [
        ⟨81719, true, false, [], []⟩
      ]⟩,
    ⟨[93899], [93899], .contexts []⟩,
    ⟨[93901, 11], [93899], .contexts [
        ⟨81720, true, false, [], [11]⟩,
        ⟨53, false, false, [93899], []⟩,
        ⟨81721, false, false, [], []⟩
      ]⟩,
    ⟨[93903], [93901, 1], .source 47016⟩,
    ⟨[93901, 1], [93903], .contexts [
        ⟨81723, true, false, [], []⟩
      ]⟩,
    ⟨[93901], [93901], .contexts []⟩,
    ⟨[93903, 1], [93901], .contexts [
        ⟨81724, true, false, [], [1]⟩,
        ⟨8, false, false, [93901], []⟩,
        ⟨81725, false, false, [], []⟩
      ]⟩,
    ⟨[93905], [93903, 13], .source 47017⟩]

/-- Exact literal claimed equations and contextual derivations, block 1277. -/
def y322TCIndexRaw1277 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93903, 13], [93905], .contexts [
        ⟨81727, true, false, [], []⟩
      ]⟩,
    ⟨[93903], [93903], .contexts []⟩,
    ⟨[93905, 13], [93903], .contexts [
        ⟨81728, true, false, [], [13]⟩,
        ⟨59, false, false, [93903], []⟩,
        ⟨81729, false, false, [], []⟩
      ]⟩,
    ⟨[93907], [93905, 15], .source 47018⟩,
    ⟨[93905], [93905], .contexts []⟩,
    ⟨[93907, 15], [93905], .contexts [
        ⟨81731, false, false, [], [15]⟩,
        ⟨1, false, false, [93905], []⟩,
        ⟨81732, false, false, [], []⟩
      ]⟩,
    ⟨[93909], [93907, 1], .source 47019⟩,
    ⟨[93907], [93907], .contexts []⟩,
    ⟨[93909, 1], [93907], .contexts [
        ⟨81734, false, false, [], [1]⟩,
        ⟨8, false, false, [93907], []⟩,
        ⟨81735, false, false, [], []⟩
      ]⟩,
    ⟨[93911], [93909, 3], .source 47020⟩,
    ⟨[93909], [93909], .contexts []⟩,
    ⟨[93911, 3], [93909], .contexts [
        ⟨81737, false, false, [], [3]⟩,
        ⟨20, false, false, [93909], []⟩,
        ⟨81738, false, false, [], []⟩
      ]⟩,
    ⟨[93913], [93911, 5], .source 47021⟩,
    ⟨[93911], [93911], .contexts []⟩,
    ⟨[93913, 5], [93911], .contexts [
        ⟨81740, false, false, [], [5]⟩,
        ⟨28, false, false, [93911], []⟩,
        ⟨81741, false, false, [], []⟩
      ]⟩,
    ⟨[93915], [93913, 1], .source 47022⟩,
    ⟨[93913, 1], [93915], .contexts [
        ⟨81743, true, false, [], []⟩
      ]⟩,
    ⟨[93913], [93913], .contexts []⟩,
    ⟨[93915, 1], [93913], .contexts [
        ⟨81744, true, false, [], [1]⟩,
        ⟨8, false, false, [93913], []⟩,
        ⟨81745, false, false, [], []⟩
      ]⟩,
    ⟨[93917], [93915, 9], .source 47023⟩,
    ⟨[93915, 9], [93917], .contexts [
        ⟨81747, true, false, [], []⟩
      ]⟩,
    ⟨[93915], [93915], .contexts []⟩,
    ⟨[93917, 9], [93915], .contexts [
        ⟨81748, true, false, [], [9]⟩,
        ⟨46, false, false, [93915], []⟩,
        ⟨81749, false, false, [], []⟩
      ]⟩,
    ⟨[93919], [93917, 11], .source 47024⟩,
    ⟨[93917, 11], [93919], .contexts [
        ⟨81751, true, false, [], []⟩
      ]⟩,
    ⟨[93917], [93917], .contexts []⟩,
    ⟨[93919, 11], [93917], .contexts [
        ⟨81752, true, false, [], [11]⟩,
        ⟨53, false, false, [93917], []⟩,
        ⟨81753, false, false, [], []⟩
      ]⟩,
    ⟨[93921], [93919, 1], .source 47025⟩,
    ⟨[93919, 1], [93921], .contexts [
        ⟨81755, true, false, [], []⟩
      ]⟩,
    ⟨[93919], [93919], .contexts []⟩,
    ⟨[93921, 1], [93919], .contexts [
        ⟨81756, true, false, [], [1]⟩,
        ⟨8, false, false, [93919], []⟩,
        ⟨81757, false, false, [], []⟩
      ]⟩,
    ⟨[93923], [93921, 13], .source 47026⟩,
    ⟨[93921, 13], [93923], .contexts [
        ⟨81759, true, false, [], []⟩
      ]⟩,
    ⟨[93921], [93921], .contexts []⟩,
    ⟨[93923, 13], [93921], .contexts [
        ⟨81760, true, false, [], [13]⟩,
        ⟨59, false, false, [93921], []⟩,
        ⟨81761, false, false, [], []⟩
      ]⟩,
    ⟨[93923], [93923], .contexts []⟩,
    ⟨[93919], [93919], .contexts []⟩,
    ⟨[93921, 1], [93919], .contexts [
        ⟨81758, false, false, [], []⟩,
        ⟨81764, false, false, [], []⟩,
        ⟨81757, false, false, [], []⟩,
        ⟨81757, false, false, [], []⟩
      ]⟩,
    ⟨[93919, 11], [93917], .contexts [
        ⟨81754, false, false, [], []⟩
      ]⟩,
    ⟨[93917], [93917], .contexts []⟩,
    ⟨[93917, 9], [93915], .contexts [
        ⟨81750, false, false, [], []⟩
      ]⟩,
    ⟨[93915], [93915], .contexts []⟩,
    ⟨[93915, 1], [93913], .contexts [
        ⟨81746, false, false, [], []⟩
      ]⟩,
    ⟨[93913], [93913], .contexts []⟩,
    ⟨[93913, 5], [93911], .contexts [
        ⟨81742, false, false, [], []⟩
      ]⟩,
    ⟨[93911], [93911], .contexts []⟩,
    ⟨[93909], [93909], .contexts []⟩,
    ⟨[93921, 1, 11, 9, 1, 5, 3], [93909], .contexts [
        ⟨81765, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨81766, false, false, [], [9, 1, 5, 3]⟩,
        ⟨81767, false, false, [], [9, 1, 5, 3]⟩,
        ⟨81753, false, false, [], [9, 1, 5, 3]⟩,
        ⟨81753, false, false, [], [9, 1, 5, 3]⟩,
        ⟨81768, false, false, [], [1, 5, 3]⟩,
        ⟨81769, false, false, [], [1, 5, 3]⟩,
        ⟨81749, false, false, [], [1, 5, 3]⟩,
        ⟨81749, false, false, [], [1, 5, 3]⟩,
        ⟨81770, false, false, [], [5, 3]⟩,
        ⟨81771, false, false, [], [5, 3]⟩,
        ⟨81745, false, false, [], [5, 3]⟩,
        ⟨81745, false, false, [], [5, 3]⟩,
        ⟨81772, false, false, [], [3]⟩,
        ⟨81773, false, false, [], [3]⟩,
        ⟨81741, false, false, [], [3]⟩,
        ⟨81741, false, false, [], [3]⟩,
        ⟨81739, false, false, [], []⟩,
        ⟨81774, false, false, [], []⟩,
        ⟨81738, false, false, [], []⟩,
        ⟨81738, false, false, [], []⟩
      ]⟩,
    ⟨[93909, 1], [93907], .contexts [
        ⟨81736, false, false, [], []⟩
      ]⟩,
    ⟨[93907], [93907], .contexts []⟩,
    ⟨[93905], [93905], .contexts []⟩,
    ⟨[93903], [93903], .contexts []⟩,
    ⟨[93901], [93901], .contexts []⟩,
    ⟨[93901, 11], [93899], .contexts [
        ⟨81722, false, false, [], []⟩
      ]⟩,
    ⟨[93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11], [93899], .contexts [
        ⟨81775, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨81776, false, false, [], [15, 13, 1, 11]⟩,
        ⟨81777, false, false, [], [15, 13, 1, 11]⟩,
        ⟨81735, false, false, [], [15, 13, 1, 11]⟩,
        ⟨81735, false, false, [], [15, 13, 1, 11]⟩,
        ⟨81733, false, false, [], [13, 1, 11]⟩,
        ⟨81778, false, false, [], [13, 1, 11]⟩,
        ⟨81732, false, false, [], [13, 1, 11]⟩,
        ⟨81732, false, false, [], [13, 1, 11]⟩,
        ⟨81730, false, false, [], [1, 11]⟩,
        ⟨81779, false, false, [], [1, 11]⟩,
        ⟨81729, false, false, [], [1, 11]⟩,
        ⟨81729, false, false, [], [1, 11]⟩,
        ⟨81726, false, false, [], [11]⟩,
        ⟨81780, false, false, [], [11]⟩,
        ⟨81725, false, false, [], [11]⟩,
        ⟨81725, false, false, [], [11]⟩,
        ⟨81781, false, false, [], []⟩,
        ⟨81721, false, false, [], []⟩,
        ⟨81721, false, false, [], []⟩
      ]⟩,
    ⟨[93897], [93897], .contexts []⟩,
    ⟨[93897, 1], [93895], .contexts [
        ⟨81714, false, false, [], []⟩
      ]⟩,
    ⟨[93895], [93895], .contexts []⟩,
    ⟨[93893], [93893], .contexts []⟩,
    ⟨[93891], [93891], .contexts []⟩,
    ⟨[93889], [93889], .contexts []⟩,
    ⟨[
      93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1
    ], [93889], .contexts [
        ⟨81782, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨81718, false, false, [], [1, 5, 3, 1]⟩,
        ⟨81783, false, false, [], [1, 5, 3, 1]⟩,
        ⟨81717, false, false, [], [1, 5, 3, 1]⟩,
        ⟨81717, false, false, [], [1, 5, 3, 1]⟩,
        ⟨81784, false, false, [], [5, 3, 1]⟩,
        ⟨81785, false, false, [], [5, 3, 1]⟩,
        ⟨81713, false, false, [], [5, 3, 1]⟩,
        ⟨81713, false, false, [], [5, 3, 1]⟩,
        ⟨81711, false, false, [], [3, 1]⟩,
        ⟨81786, false, false, [], [3, 1]⟩,
        ⟨81710, false, false, [], [3, 1]⟩,
        ⟨81710, false, false, [], [3, 1]⟩,
        ⟨81708, false, false, [], [1]⟩,
        ⟨81787, false, false, [], [1]⟩,
        ⟨81707, false, false, [], [1]⟩,
        ⟨81707, false, false, [], [1]⟩,
        ⟨81705, false, false, [], []⟩,
        ⟨81788, false, false, [], []⟩,
        ⟨81704, false, false, [], []⟩,
        ⟨81704, false, false, [], []⟩
      ]⟩,
    ⟨[93889, 15], [93887], .contexts [
        ⟨81701, false, false, [], []⟩
      ]⟩,
    ⟨[93885], [93885], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1278. -/
def y322TCIndexRaw1278 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93883], [93883], .contexts []⟩,
    ⟨[93881], [93881], .contexts []⟩,
    ⟨[93879], [93879], .contexts []⟩,
    ⟨[
      93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [93879], .contexts [
        ⟨81789, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨81790, false, false, [], [13, 1, 11, 9]⟩,
        ⟨81700, false, false, [], [13, 1, 11, 9]⟩,
        ⟨81700, false, false, [], [13, 1, 11, 9]⟩,
        ⟨81697, false, false, [], [1, 11, 9]⟩,
        ⟨81791, false, false, [], [1, 11, 9]⟩,
        ⟨81696, false, false, [], [1, 11, 9]⟩,
        ⟨81696, false, false, [], [1, 11, 9]⟩,
        ⟨81694, false, false, [], [11, 9]⟩,
        ⟨81792, false, false, [], [11, 9]⟩,
        ⟨81693, false, false, [], [11, 9]⟩,
        ⟨81693, false, false, [], [11, 9]⟩,
        ⟨81691, false, false, [], [9]⟩,
        ⟨81793, false, false, [], [9]⟩,
        ⟨81690, false, false, [], [9]⟩,
        ⟨81690, false, false, [], [9]⟩,
        ⟨81688, false, false, [], []⟩,
        ⟨81794, false, false, [], []⟩,
        ⟨81687, false, false, [], []⟩,
        ⟨81687, false, false, [], []⟩
      ]⟩,
    ⟨[93877], [93877], .contexts []⟩,
    ⟨[93875], [93875], .contexts []⟩,
    ⟨[93873], [93873], .contexts []⟩,
    ⟨[93871], [93871], .contexts []⟩,
    ⟨[93871, 15], [93869], .contexts [
        ⟨81672, false, false, [], []⟩
      ]⟩,
    ⟨[
      93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15
    ], [93869], .contexts [
        ⟨81795, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨81685, false, false, [], [5, 3, 1, 15]⟩,
        ⟨81796, false, false, [], [5, 3, 1, 15]⟩,
        ⟨81684, false, false, [], [5, 3, 1, 15]⟩,
        ⟨81684, false, false, [], [5, 3, 1, 15]⟩,
        ⟨81682, false, false, [], [3, 1, 15]⟩,
        ⟨81797, false, false, [], [3, 1, 15]⟩,
        ⟨81681, false, false, [], [3, 1, 15]⟩,
        ⟨81681, false, false, [], [3, 1, 15]⟩,
        ⟨81679, false, false, [], [1, 15]⟩,
        ⟨81798, false, false, [], [1, 15]⟩,
        ⟨81678, false, false, [], [1, 15]⟩,
        ⟨81678, false, false, [], [1, 15]⟩,
        ⟨81676, false, false, [], [15]⟩,
        ⟨81799, false, false, [], [15]⟩,
        ⟨81675, false, false, [], [15]⟩,
        ⟨81675, false, false, [], [15]⟩,
        ⟨81800, false, false, [], []⟩,
        ⟨81671, false, false, [], []⟩,
        ⟨81671, false, false, [], []⟩
      ]⟩,
    ⟨[93867], [93867], .contexts []⟩,
    ⟨[93865], [93865], .contexts []⟩,
    ⟨[93861], [93861], .contexts []⟩,
    ⟨[93861, 1], [93859], .contexts [
        ⟨81654, false, false, [], []⟩
      ]⟩,
    ⟨[93859], [93859], .contexts []⟩,
    ⟨[
      93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1
    ], [93859], .contexts [
        ⟨81801, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨81669, false, false, [], [1, 11, 9, 1]⟩,
        ⟨81802, false, false, [], [1, 11, 9, 1]⟩,
        ⟨81668, false, false, [], [1, 11, 9, 1]⟩,
        ⟨81668, false, false, [], [1, 11, 9, 1]⟩,
        ⟨81665, false, false, [], [11, 9, 1]⟩,
        ⟨81803, false, false, [], [11, 9, 1]⟩,
        ⟨81664, false, false, [], [11, 9, 1]⟩,
        ⟨81664, false, false, [], [11, 9, 1]⟩,
        ⟨81661, false, false, [], [9, 1]⟩,
        ⟨81660, false, false, [], [9, 1]⟩,
        ⟨81660, false, false, [], [9, 1]⟩,
        ⟨81656, true, false, [], [9, 1]⟩,
        ⟨46, false, false, [93861], [1]⟩,
        ⟨81657, false, false, [], [1]⟩,
        ⟨81804, false, false, [], [1]⟩,
        ⟨81657, false, false, [], [1]⟩,
        ⟨81657, false, false, [], [1]⟩,
        ⟨81805, false, false, [], []⟩,
        ⟨81806, false, false, [], []⟩,
        ⟨81653, false, false, [], []⟩,
        ⟨81653, false, false, [], []⟩
      ]⟩,
    ⟨[93857], [93857], .contexts []⟩,
    ⟨[93855], [93855], .contexts []⟩,
    ⟨[93853], [93853], .contexts []⟩,
    ⟨[93851], [93851], .contexts []⟩,
    ⟨[93849], [93849], .contexts []⟩,
    ⟨[
      93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13
    ], [93849], .contexts [
        ⟨81807, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨81650, false, false, [], [3, 1, 15, 13]⟩,
        ⟨81808, false, false, [], [3, 1, 15, 13]⟩,
        ⟨81649, false, false, [], [3, 1, 15, 13]⟩,
        ⟨81649, false, false, [], [3, 1, 15, 13]⟩,
        ⟨81645, true, false, [], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [93855], [1, 15, 13]⟩,
        ⟨81646, false, false, [], [1, 15, 13]⟩,
        ⟨81809, false, false, [], [1, 15, 13]⟩,
        ⟨81646, false, false, [], [1, 15, 13]⟩,
        ⟨81646, false, false, [], [1, 15, 13]⟩,
        ⟨81642, true, false, [], [1, 15, 13]⟩,
        ⟨8, false, false, [93853], [15, 13]⟩,
        ⟨81643, false, false, [], [15, 13]⟩,
        ⟨81810, false, false, [], [15, 13]⟩,
        ⟨81643, false, false, [], [15, 13]⟩,
        ⟨81643, false, false, [], [15, 13]⟩,
        ⟨81639, true, false, [], [15, 13]⟩,
        ⟨1, false, false, [93851], [13]⟩,
        ⟨81640, false, false, [], [13]⟩,
        ⟨81811, false, false, [], [13]⟩,
        ⟨81640, false, false, [], [13]⟩,
        ⟨81640, false, false, [], [13]⟩,
        ⟨81636, true, false, [], [13]⟩,
        ⟨59, false, false, [93849], []⟩,
        ⟨81637, false, false, [], []⟩,
        ⟨81812, false, false, [], []⟩,
        ⟨81637, false, false, [], []⟩,
        ⟨81637, false, false, [], []⟩
      ]⟩,
    ⟨[93845], [93845], .contexts []⟩,
    ⟨[93843], [93843], .contexts []⟩,
    ⟨[93841], [93841], .contexts []⟩,
    ⟨[93839], [93839], .contexts []⟩,
    ⟨[
      93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5
    ], [93839], .contexts [
        ⟨81813, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨81634, false, false, [], [11, 9, 1, 5]⟩,
        ⟨81633, false, false, [], [11, 9, 1, 5]⟩,
        ⟨81633, false, false, [], [11, 9, 1, 5]⟩,
        ⟨81629, true, false, [], [11, 9, 1, 5]⟩,
        ⟨53, false, false, [93845], [9, 1, 5]⟩,
        ⟨81630, false, false, [], [9, 1, 5]⟩,
        ⟨81814, false, false, [], [9, 1, 5]⟩,
        ⟨81630, false, false, [], [9, 1, 5]⟩,
        ⟨81630, false, false, [], [9, 1, 5]⟩,
        ⟨81627, false, false, [], [1, 5]⟩,
        ⟨81815, false, false, [], [1, 5]⟩,
        ⟨81626, false, false, [], [1, 5]⟩,
        ⟨81626, false, false, [], [1, 5]⟩,
        ⟨81622, true, false, [], [1, 5]⟩,
        ⟨8, false, false, [93841], [5]⟩,
        ⟨81623, false, false, [], [5]⟩,
        ⟨81816, false, false, [], [5]⟩,
        ⟨81623, false, false, [], [5]⟩,
        ⟨81623, false, false, [], [5]⟩,
        ⟨81619, true, false, [], [5]⟩,
        ⟨28, false, false, [93839], []⟩,
        ⟨81620, false, false, [], []⟩,
        ⟨81817, false, false, [], []⟩,
        ⟨81620, false, false, [], []⟩,
        ⟨81620, false, false, [], []⟩
      ]⟩,
    ⟨[93837], [93837], .contexts []⟩,
    ⟨[93835], [93835], .contexts []⟩,
    ⟨[93833], [93833], .contexts []⟩,
    ⟨[93831], [93831], .contexts []⟩,
    ⟨[
      93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [93831], .contexts [
        ⟨81818, false, false, [], [3, 1, 15, 13]⟩,
        ⟨81616, true, false, [], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [93837], [1, 15, 13]⟩,
        ⟨81617, false, false, [], [1, 15, 13]⟩,
        ⟨81819, false, false, [], [1, 15, 13]⟩,
        ⟨81617, false, false, [], [1, 15, 13]⟩,
        ⟨81617, false, false, [], [1, 15, 13]⟩,
        ⟨81613, true, false, [], [1, 15, 13]⟩,
        ⟨8, false, false, [93835], [15, 13]⟩,
        ⟨81614, false, false, [], [15, 13]⟩,
        ⟨81820, false, false, [], [15, 13]⟩,
        ⟨81614, false, false, [], [15, 13]⟩,
        ⟨81614, false, false, [], [15, 13]⟩,
        ⟨81610, true, false, [], [15, 13]⟩,
        ⟨1, false, false, [93833], [13]⟩,
        ⟨81611, false, false, [], [13]⟩,
        ⟨81821, false, false, [], [13]⟩,
        ⟨81611, false, false, [], [13]⟩,
        ⟨81611, false, false, [], [13]⟩,
        ⟨81608, false, false, [], []⟩,
        ⟨81822, false, false, [], []⟩,
        ⟨81607, false, false, [], []⟩,
        ⟨81607, false, false, [], []⟩
      ]⟩,
    ⟨[
      93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5
    ], [30115, 93823], .contexts [
        ⟨81823, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨81604, false, false, [], [11, 9, 1, 5]⟩,
        ⟨81599, false, false, [], [11, 9, 1, 5]⟩,
        ⟨81600, false, false, [], [11, 9, 1, 5]⟩,
        ⟨81600, false, false, [], [11, 9, 1, 5]⟩,
        ⟨81598, true, false, [], [11, 9, 1, 5]⟩,
        ⟨53, false, false, [93827], [9, 1, 5]⟩,
        ⟨81595, false, false, [], [9, 1, 5]⟩,
        ⟨81594, false, false, [], [9, 1, 5]⟩,
        ⟨81595, false, false, [], [9, 1, 5]⟩,
        ⟨81595, false, false, [], [9, 1, 5]⟩,
        ⟨81593, true, false, [], [9, 1, 5]⟩,
        ⟨46, false, false, [93825], [1, 5]⟩,
        ⟨81581, false, false, [], [1, 5]⟩,
        ⟨81580, false, false, [], [1, 5]⟩,
        ⟨81581, false, false, [], [1, 5]⟩,
        ⟨81581, false, false, [], [1, 5]⟩,
        ⟨81587, false, false, [], [5]⟩,
        ⟨81583, false, false, [], [5]⟩,
        ⟨81584, false, false, [], [5]⟩,
        ⟨81584, false, false, [], [5]⟩,
        ⟨81579, false, false, [30115], []⟩,
        ⟨81572, false, false, [], []⟩,
        ⟨81573, false, false, [], []⟩,
        ⟨81574, false, false, [], []⟩
      ]⟩,
    ⟨[
      93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1
    ], [30115, 93813], .contexts [
        ⟨81824, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨81565, false, false, [30115], [1, 15, 13, 1]⟩,
        ⟨81568, false, false, [], [1, 15, 13, 1]⟩,
        ⟨81569, false, false, [], [1, 15, 13, 1]⟩,
        ⟨81571, false, false, [], [1, 15, 13, 1]⟩,
        ⟨81555, false, false, [30115], [15, 13, 1]⟩,
        ⟨81546, false, false, [], [15, 13, 1]⟩,
        ⟨81547, false, false, [], [15, 13, 1]⟩,
        ⟨81548, false, false, [], [15, 13, 1]⟩,
        ⟨81542, false, false, [30115], [13, 1]⟩,
        ⟨81516, false, false, [], [13, 1]⟩,
        ⟨81517, false, false, [], [13, 1]⟩,
        ⟨81518, false, false, [], [13, 1]⟩,
        ⟨81510, false, false, [30115], [1]⟩,
        ⟨81514, false, false, [], [1]⟩,
        ⟨81515, false, false, [], [1]⟩,
        ⟨81489, false, false, [30115], []⟩
      ]⟩,
    ⟨[30757], [30115, 27451], .source 15443⟩,
    ⟨[
      93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3
    ], [30757, 85327], .contexts [
        ⟨81825, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨81477, false, false, [30115], [9, 1, 5, 3]⟩,
        ⟨81462, true, false, [30115], [9, 1, 5, 3]⟩,
        ⟨46, false, false, [30115, 92177], [1, 5, 3]⟩,
        ⟨70381, false, false, [30115], [1, 5, 3]⟩,
        ⟨70378, false, false, [30115], [5, 3]⟩,
        ⟨70479, false, false, [30115], [3]⟩,
        ⟨70489, false, false, [30115], []⟩,
        ⟨81826, true, false, [], [85327]⟩
      ]⟩,
    ⟨[30759], [30757, 14671], .source 15444⟩,
    ⟨[30761], [30759, 16355], .source 15445⟩,
    ⟨[30763], [30761, 2021], .source 15446⟩,
    ⟨[
      93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1
    ], [30763, 2373, 86569], .contexts [
        ⟨81827, false, false, [], [1, 15, 13, 1]⟩,
        ⟨31381, false, false, [30757], [15, 13, 1]⟩,
        ⟨81828, true, false, [], [85327, 15, 13, 1]⟩,
        ⟨37885, false, false, [30759], [13, 1]⟩,
        ⟨81829, true, false, [], [86569, 13, 1]⟩,
        ⟨37853, true, false, [30761], [13, 1]⟩,
        ⟨179, false, false, [30761, 80253], [1]⟩,
        ⟨180, false, false, [30761, 80253], [1]⟩,
        ⟨7754, false, false, [30761], [5, 1]⟩,
        ⟨7756, false, false, [30761], [5, 1]⟩,
        ⟨7752, false, false, [30761], [5, 1]⟩,
        ⟨7753, false, false, [30761], [5, 1]⟩,
        ⟨7753, false, false, [30761], [5, 1]⟩,
        ⟨37851, false, false, [30761, 2021], [1]⟩,
        ⟨37857, false, false, [30761, 2021], [1]⟩,
        ⟨5692, true, false, [30761], [86569, 1]⟩,
        ⟨81830, true, false, [], [86569, 1]⟩,
        ⟨37858, false, false, [30763], []⟩
      ]⟩,
    ⟨[30765], [30763, 2373], .source 15447⟩,
    ⟨[30767], [30765, 15127], .source 15448⟩,
    ⟨[30769], [30767, 4217], .source 15449⟩,
    ⟨[30771], [30769, 2375], .source 15450⟩,
    ⟨[
      93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [30771, 8431, 80261], .contexts [
        ⟨81831, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨81832, true, false, [], [86569, 11, 9, 1, 5, 3]⟩,
        ⟨37880, false, false, [30765], [9, 1, 5, 3]⟩,
        ⟨81833, true, false, [], [83951, 9, 1, 5, 3]⟩,
        ⟨24080, false, false, [30767], [1, 5, 3]⟩,
        ⟨81834, true, false, [], [83951, 1, 5, 3]⟩,
        ⟨24073, false, false, [30769], [5, 3]⟩,
        ⟨81835, true, false, [], [83951, 5, 3]⟩,
        ⟨24065, false, false, [30771], [3]⟩,
        ⟨8349, false, false, [30771], []⟩,
        ⟨11536, false, false, [30771], []⟩
      ]⟩,
    ⟨[30773], [30771, 8431], .source 15451⟩,
    ⟨[30775], [30773, 9215], .source 15452⟩,
    ⟨[30777], [30775, 8411], .source 15453⟩,
    ⟨[30779], [30777, 14713], .source 15454⟩,
    ⟨[
      93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11
    ], [30779, 79367], .contexts [
        ⟨81836, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨81837, true, false, [], [80261, 1, 15, 13, 1, 11]⟩,
        ⟨7884, false, false, [30773], [15, 13, 1, 11]⟩,
        ⟨12061, false, false, [30773], [13, 1, 11]⟩,
        ⟨81838, true, false, [], [80805, 13, 1, 11]⟩,
        ⟨11516, false, false, [30775], [1, 11]⟩,
        ⟨81839, true, false, [], [81405, 1, 11]⟩,
        ⟨14550, false, false, [30777], [11]⟩,
        ⟨81840, true, false, [], [79191, 11]⟩,
        ⟨6782, false, false, [30779], []⟩
      ]⟩,
    ⟨[30781], [30779, 2009], .source 15455⟩,
    ⟨[30783], [30781, 15971], .source 15456⟩,
    ⟨[30785], [30783, 17275], .source 15457⟩,
    ⟨[
      93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1
    ], [30785, 84489, 1], .contexts [
        ⟨81841, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨16584, false, false, [30779], [1, 5, 3, 1]⟩,
        ⟨16592, false, false, [30779], [5, 3, 1]⟩,
        ⟨81842, true, false, [], [82783, 5, 3, 1]⟩,
        ⟨19455, false, false, [30781], [3, 1]⟩,
        ⟨81843, true, false, [], [83167, 3, 1]⟩,
        ⟨27092, false, false, [30783], [1]⟩,
        ⟨81844, true, false, [], [84489, 1]⟩
      ]⟩,
    ⟨[30787], [30785, 17269], .source 15458⟩,
    ⟨[30789], [30787, 23305], .source 15459⟩,
    ⟨[30791], [30789, 23287], .source 15460⟩,
    ⟨[
      93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [30791, 88831], .contexts [
        ⟨81845, false, false, [], [15, 13, 1, 11]⟩,
        ⟨27100, false, false, [30785], [15, 13, 1, 11]⟩,
        ⟨27120, false, false, [30785], [13, 1, 11]⟩,
        ⟨81846, true, false, [], [83577, 13, 1, 11]⟩,
        ⟨52662, false, false, [30787], [1, 11]⟩,
        ⟨81847, true, false, [], [88829, 1, 11]⟩,
        ⟨52664, false, false, [30789], [11]⟩,
        ⟨81848, true, false, [], [88829, 11]⟩,
        ⟨52546, false, false, [30791], []⟩
      ]⟩,
    ⟨[30793], [30791, 28817], .source 15461⟩,
    ⟨[30795], [30793, 28679], .source 15462⟩,
    ⟨[30797], [30795, 24605], .source 15463⟩,
    ⟨[30799], [30797, 22631], .source 15464⟩,
    ⟨[30799, 86785], [30799, 86785], .contexts []⟩,
    ⟨[30799, 86785], [30799, 86785], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1279. -/
def y322TCIndexRaw1279 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[
      93921, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1
    ], [30799, 86785], .contexts [
        ⟨81849, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨74855, false, false, [30791], [1, 5, 3, 1]⟩,
        ⟨81850, true, false, [], [92783, 1, 5, 3, 1]⟩,
        ⟨74168, false, false, [30793], [5, 3, 1]⟩,
        ⟨75072, false, false, [30793], [5, 3, 1]⟩,
        ⟨81851, true, false, [], [90091, 5, 3, 1]⟩,
        ⟨59043, false, false, [30795], [3, 1]⟩,
        ⟨81852, true, false, [], [86783, 3, 1]⟩,
        ⟨49821, false, false, [30797], [1]⟩,
        ⟨81853, true, false, [], [86783, 1]⟩,
        ⟨38749, false, false, [30799], []⟩,
        ⟨81854, false, false, [], []⟩,
        ⟨81855, false, false, [], []⟩
      ]⟩,
    ⟨[93923, 15], [93923, 15], .contexts []⟩,
    ⟨[93923, 15], [30799, 86785], .contexts [
        ⟨81857, false, false, [], []⟩,
        ⟨81763, true, false, [], [15]⟩,
        ⟨81763, true, false, [], [15]⟩,
        ⟨81760, true, false, [], [15]⟩,
        ⟨2277, false, false, [93921], []⟩,
        ⟨2278, false, false, [93921], []⟩,
        ⟨81856, false, false, [], []⟩,
        ⟨61240, false, false, [30799], []⟩,
        ⟨13, true, false, [], [30799, 86785]⟩
      ]⟩,
    ⟨[30801], [30798], .source 15465⟩,
    ⟨[86785, 15], [30801, 93923], .contexts [
        ⟨81858, true, false, [30798], [15]⟩,
        ⟨1, false, false, [30798, 93923], []⟩,
        ⟨81859, true, false, [], [93923]⟩
      ]⟩,
    ⟨[93921], [93921], .contexts []⟩,
    ⟨[93923, 15], [30799, 86785], .contexts [
        ⟨81857, false, false, [], []⟩,
        ⟨81858, false, false, [], []⟩,
        ⟨81854, false, false, [], []⟩,
        ⟨81855, false, false, [], []⟩,
        ⟨81855, false, false, [], []⟩
      ]⟩,
    ⟨[30803], [30799, 19493], .source 15466⟩,
    ⟨[30803, 83893], [30803, 83893], .contexts []⟩,
    ⟨[30803, 83893], [30803, 83893], .contexts []⟩,
    ⟨[93921, 15], [93921, 15], .contexts []⟩,
    ⟨[30803], [30803], .contexts []⟩,
    ⟨[30803], [30803], .contexts []⟩,
    ⟨[93921, 15], [30803, 83893], .contexts [
        ⟨81866, false, false, [], []⟩,
        ⟨81761, true, false, [], [15]⟩,
        ⟨81761, true, false, [], [15]⟩,
        ⟨81861, true, false, [], [15]⟩,
        ⟨81762, true, false, [], [15]⟩,
        ⟨88, false, false, [93923], []⟩,
        ⟨91, false, false, [93923], []⟩,
        ⟨81862, false, false, [], [13, 15, 13]⟩,
        ⟨38753, false, false, [30799], [15, 13]⟩,
        ⟨39026, false, false, [30799], [15, 13]⟩,
        ⟨81863, true, false, [], [83897, 15, 13]⟩,
        ⟨23351, false, false, [30803], [13]⟩,
        ⟨23347, false, false, [30803], []⟩,
        ⟨81864, false, false, [], []⟩,
        ⟨81865, false, false, [], []⟩,
        ⟨40466, false, false, [30803], []⟩,
        ⟨81868, true, false, [], [83893]⟩,
        ⟨81867, true, false, [], [83893]⟩,
        ⟨13, true, false, [], [30803, 83893]⟩
      ]⟩,
    ⟨[30805], [30802], .source 15467⟩,
    ⟨[83893, 15], [30805, 93921], .contexts [
        ⟨81869, true, false, [30802], [15]⟩,
        ⟨1, false, false, [30802, 93921], []⟩,
        ⟨81870, true, false, [], [93921]⟩
      ]⟩,
    ⟨[30807], [30799, 22623], .source 15468⟩,
    ⟨[93923], [93923], .contexts []⟩,
    ⟨[88325, 1], [88325, 1], .contexts []⟩,
    ⟨[93923], [93923], .contexts []⟩,
    ⟨[30809], [30806], .source 15469⟩,
    ⟨[30809], [30806], .contexts [
        ⟨81876, false, false, [], []⟩
      ]⟩,
    ⟨[30806], [30806], .contexts []⟩,
    ⟨[30809], [30806], .contexts [
        ⟨81877, false, false, [], []⟩,
        ⟨81878, false, false, [], []⟩,
        ⟨81878, false, false, [], []⟩
      ]⟩,
    ⟨[88325, 1], [30809, 93923], .contexts [
        ⟨81874, false, false, [], []⟩,
        ⟨81872, false, false, [30806], [88325, 1]⟩,
        ⟨49817, true, false, [30806, 30799], [1]⟩,
        ⟨38751, true, false, [30806, 30799], [15, 1]⟩,
        ⟨81862, true, false, [30806], [1, 15, 1]⟩,
        ⟨504, false, false, [30806, 93923], []⟩,
        ⟨81873, false, false, [30806], []⟩,
        ⟨81875, false, false, [30806], []⟩,
        ⟨81879, true, false, [], [93923]⟩
      ]⟩,
    ⟨[30807], [30808], .contexts [
        ⟨81876, true, true, [], []⟩
      ]⟩,
    ⟨[30811], [30799, 22627], .source 15470⟩,
    ⟨[30813], [30811, 20905], .source 15471⟩,
    ⟨[83685, 7], [83685, 7], .contexts []⟩,
    ⟨[30815], [30812], .source 15472⟩,
    ⟨[30812], [30812], .contexts []⟩,
    ⟨[83685, 7], [30815, 93923], .contexts [
        ⟨81884, false, false, [], []⟩,
        ⟨81883, false, false, [30812], [83685, 7]⟩,
        ⟨43035, true, false, [30812, 30811], [7]⟩,
        ⟨81882, false, false, [30812], [83461, 15, 7]⟩,
        ⟨49813, true, false, [30812, 30799], [15, 7]⟩,
        ⟨81862, true, false, [30812], [7, 15, 7]⟩,
        ⟨2651, false, false, [30812, 93923], []⟩,
        ⟨81873, false, false, [30812], []⟩,
        ⟨81875, false, false, [30812], []⟩,
        ⟨81886, true, false, [], [93923]⟩,
        ⟨81886, true, false, [], [93923]⟩,
        ⟨81885, true, false, [], [93923]⟩
      ]⟩,
    ⟨[30813], [30814], .contexts [
        ⟨81885, true, true, [], []⟩
      ]⟩,
    ⟨[30803, 90487], [30803, 90487], .contexts []⟩,
    ⟨[30805], [30802], .contexts [
        ⟨81870, false, false, [], []⟩
      ]⟩,
    ⟨[30802], [30802], .contexts []⟩,
    ⟨[30805], [30802], .contexts [
        ⟨81890, false, false, [], []⟩,
        ⟨81891, false, false, [], []⟩,
        ⟨81891, false, false, [], []⟩
      ]⟩,
    ⟨[90487, 11], [30805, 93923], .contexts [
        ⟨81889, true, false, [30802], [11]⟩,
        ⟨61254, true, false, [], [11]⟩,
        ⟨81863, false, false, [30802], [90485, 15, 11]⟩,
        ⟨61243, true, false, [30802, 30799], [15, 11]⟩,
        ⟨81862, true, false, [30802], [11, 15, 11]⟩,
        ⟨2289, false, false, [30802, 93923], []⟩,
        ⟨81873, false, false, [30802], []⟩,
        ⟨81875, false, false, [30802], []⟩,
        ⟨81892, true, false, [], [93923]⟩
      ]⟩,
    ⟨[30803], [30804], .contexts [
        ⟨81870, true, true, [], []⟩
      ]⟩,
    ⟨[30803, 83891], [30803, 83891], .contexts []⟩,
    ⟨[83891, 15], [83891, 15], .contexts []⟩,
    ⟨[83891, 15], [30805, 93919], .contexts [
        ⟨81896, false, false, [], []⟩,
        ⟨81895, true, false, [30802], [15]⟩,
        ⟨23343, true, false, [], [15]⟩,
        ⟨81865, true, false, [30802], [1, 15]⟩,
        ⟨81865, true, false, [30802], [1, 15]⟩,
        ⟨81864, true, false, [30802], [1, 15]⟩,
        ⟨81869, true, false, [30802], [1, 15]⟩,
        ⟨81866, true, false, [30802], [1, 15]⟩,
        ⟨1666, false, false, [30802, 93921], []⟩,
        ⟨9, false, false, [30802, 93921], []⟩,
        ⟨81765, false, false, [30802], []⟩,
        ⟨81892, true, false, [], [93919]⟩
      ]⟩,
    ⟨[30809, 93923], [30809, 93923], .contexts []⟩,
    ⟨[93919, 13], [93919, 13], .contexts []⟩,
    ⟨[30807], [30808], .contexts [
        ⟨81881, false, false, [], []⟩
      ]⟩,
    ⟨[30808], [30808], .contexts []⟩,
    ⟨[30807], [30808], .contexts [
        ⟨81900, false, false, [], []⟩,
        ⟨81901, false, false, [], []⟩,
        ⟨81901, false, false, [], []⟩
      ]⟩,
    ⟨[93919, 13], [30807, 88321], .contexts [
        ⟨81899, false, false, [], []⟩,
        ⟨81758, true, false, [], [13]⟩,
        ⟨81762, true, false, [], [1, 13]⟩,
        ⟨81898, true, false, [30808], [13, 1, 13]⟩,
        ⟨81898, true, false, [30808], [13, 1, 13]⟩,
        ⟨81880, true, false, [30808], [13, 1, 13]⟩,
        ⟨81874, true, false, [30808], [13, 1, 13]⟩,
        ⟨919, false, false, [30808, 88325], []⟩,
        ⟨116, false, false, [30808, 88325], []⟩,
        ⟨49890, false, false, [30808], [1]⟩,
        ⟨49602, false, false, [30808], []⟩,
        ⟨49603, false, false, [30808], []⟩,
        ⟨49555, false, false, [30808], []⟩,
        ⟨49555, false, false, [30808], []⟩,
        ⟨81902, true, false, [], [88321]⟩
      ]⟩,
    ⟨[30815, 93923], [30815, 93923], .contexts []⟩,
    ⟨[26819, 86621], [26819, 86621], .contexts []⟩,
    ⟨[86621], [86621], .contexts []⟩,
    ⟨[30817], [30813, 26819], .source 15473⟩,
    ⟨[93921, 7], [30817, 86621], .contexts [
        ⟨81762, true, false, [], [7]⟩,
        ⟨81904, true, false, [30814], [13, 7]⟩,
        ⟨81904, true, false, [30814], [13, 7]⟩,
        ⟨81887, true, false, [30814], [13, 7]⟩,
        ⟨81884, true, false, [30814], [13, 7]⟩,
        ⟨518, false, false, [30814, 83685], []⟩,
        ⟨64, false, false, [30814, 83685], []⟩,
        ⟨68384, false, false, [30814], []⟩,
        ⟨81905, false, false, [30814], []⟩,
        ⟨81905, false, false, [30814], []⟩,
        ⟨81906, false, false, [30814, 26819], []⟩,
        ⟨81888, true, false, [], [26819, 86621]⟩,
        ⟨81907, true, false, [], [86621]⟩
      ]⟩,
    ⟨[30819], [30816], .source 15474⟩,
    ⟨[30805, 93919], [30805, 93919], .contexts []⟩,
    ⟨[83891, 15], [30805, 93919], .contexts [
        ⟨81896, false, false, [], []⟩,
        ⟨81897, false, false, [], []⟩,
        ⟨81910, false, false, [], []⟩,
        ⟨81910, false, false, [], []⟩
      ]⟩,
    ⟨[30821], [30255, 27315], .source 15475⟩,
    ⟨[93919, 3], [93919, 3], .contexts []⟩,
    ⟨[30803], [30803], .contexts []⟩,
    ⟨[30803], [30804], .contexts [
        ⟨81914, false, false, [], []⟩,
        ⟨81894, false, false, [], []⟩
      ]⟩,
    ⟨[30823], [30803, 30821], .source 15476⟩,
    ⟨[93919, 3], [30823, 91603], .contexts [
        ⟨81913, false, false, [], []⟩,
        ⟨81911, true, false, [30804], [3]⟩,
        ⟨19, false, false, [30804, 83891], []⟩,
        ⟨22, false, false, [30804, 83891], []⟩,
        ⟨66824, false, false, [30804], [15]⟩,
        ⟨70111, false, false, [30804, 26405], [15]⟩,
        ⟨79725, true, false, [30804], [84193, 15]⟩,
        ⟨70107, false, false, [30804, 30255], []⟩,
        ⟨81912, true, false, [30804], [91603]⟩,
        ⟨79752, false, false, [30804, 30821], []⟩,
        ⟨81915, true, false, [], [30821, 91603]⟩,
        ⟨81916, true, false, [], [91603]⟩
      ]⟩,
    ⟨[30825], [30822], .source 15477⟩,
    ⟨[91603, 3], [30825, 93919], .contexts [
        ⟨81917, true, false, [30822], [3]⟩,
        ⟨20, false, false, [30822, 93919], []⟩,
        ⟨81918, true, false, [], [93919]⟩
      ]⟩]

/-- Literal contextual derivation data in chronological chunk 19. -/
def y322TCIndexRawChunk19 (i : Fin 4096) : Y322RawContextCertificate :=
  if i.val < 2048 then
    if i.val < 1024 then
      if i.val < 512 then
        if i.val < 256 then
          if i.val < 128 then
            if i.val < 64 then
              y322TCIndexRaw1216 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1217 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 192 then
              y322TCIndexRaw1218 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1219 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 384 then
            if i.val < 320 then
              y322TCIndexRaw1220 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1221 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 448 then
              y322TCIndexRaw1222 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1223 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 768 then
          if i.val < 640 then
            if i.val < 576 then
              y322TCIndexRaw1224 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1225 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 704 then
              y322TCIndexRaw1226 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1227 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 896 then
            if i.val < 832 then
              y322TCIndexRaw1228 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1229 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 960 then
              y322TCIndexRaw1230 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1231 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 1536 then
        if i.val < 1280 then
          if i.val < 1152 then
            if i.val < 1088 then
              y322TCIndexRaw1232 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1233 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1216 then
              y322TCIndexRaw1234 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1235 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1408 then
            if i.val < 1344 then
              y322TCIndexRaw1236 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1237 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1472 then
              y322TCIndexRaw1238 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1239 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 1792 then
          if i.val < 1664 then
            if i.val < 1600 then
              y322TCIndexRaw1240 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1241 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1728 then
              y322TCIndexRaw1242 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1243 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1920 then
            if i.val < 1856 then
              y322TCIndexRaw1244 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1245 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1984 then
              y322TCIndexRaw1246 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1247 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  else
    if i.val < 3072 then
      if i.val < 2560 then
        if i.val < 2304 then
          if i.val < 2176 then
            if i.val < 2112 then
              y322TCIndexRaw1248 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1249 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2240 then
              y322TCIndexRaw1250 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1251 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2432 then
            if i.val < 2368 then
              y322TCIndexRaw1252 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1253 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2496 then
              y322TCIndexRaw1254 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1255 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 2816 then
          if i.val < 2688 then
            if i.val < 2624 then
              y322TCIndexRaw1256 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1257 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2752 then
              y322TCIndexRaw1258 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1259 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2944 then
            if i.val < 2880 then
              y322TCIndexRaw1260 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1261 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3008 then
              y322TCIndexRaw1262 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1263 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 3584 then
        if i.val < 3328 then
          if i.val < 3200 then
            if i.val < 3136 then
              y322TCIndexRaw1264 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1265 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3264 then
              y322TCIndexRaw1266 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1267 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3456 then
            if i.val < 3392 then
              y322TCIndexRaw1268 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1269 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3520 then
              y322TCIndexRaw1270 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1271 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 3840 then
          if i.val < 3712 then
            if i.val < 3648 then
              y322TCIndexRaw1272 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1273 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3776 then
              y322TCIndexRaw1274 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1275 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3968 then
            if i.val < 3904 then
              y322TCIndexRaw1276 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1277 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 4032 then
              y322TCIndexRaw1278 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1279 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
