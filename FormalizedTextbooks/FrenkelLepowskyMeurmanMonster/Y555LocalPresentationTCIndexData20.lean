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

/-- Exact literal claimed equations and contextual derivations, block 1280. -/
def y322TCIndexRaw1280 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[30805, 93917], [30805, 93917], .contexts []⟩,
    ⟨[30805, 93917], [30805, 93917], .contexts []⟩,
    ⟨[93917, 15], [93917, 15], .contexts []⟩,
    ⟨[30804], [30804], .contexts []⟩,
    ⟨[30803], [30804], .contexts [
        ⟨81915, false, false, [], []⟩,
        ⟨81923, false, false, [], []⟩,
        ⟨81923, false, false, [], []⟩
      ]⟩,
    ⟨[93917, 15], [30803, 83889], .contexts [
        ⟨81922, false, false, [], []⟩,
        ⟨81921, true, false, [30804], [15]⟩,
        ⟨81920, true, false, [30804], [15]⟩,
        ⟨81754, true, false, [], [15]⟩,
        ⟨81911, true, false, [30804], [11, 15]⟩,
        ⟨2046, false, false, [30804, 83891], []⟩,
        ⟨54182, false, false, [30804], []⟩,
        ⟨54181, false, false, [30804], []⟩,
        ⟨54184, false, false, [30804], []⟩,
        ⟨81924, true, false, [], [83889]⟩
      ]⟩,
    ⟨[83889, 15], [30805, 93917], .contexts [
        ⟨81925, true, false, [30802], [15]⟩,
        ⟨1, false, false, [30802, 93917], []⟩,
        ⟨81870, true, false, [], [93917]⟩
      ]⟩,
    ⟨[30807, 88321], [30807, 88321], .contexts []⟩,
    ⟨[30807, 88321], [30807, 88321], .contexts []⟩,
    ⟨[93919, 13], [30807, 88321], .contexts [
        ⟨81899, false, false, [], []⟩,
        ⟨81903, false, false, [], []⟩,
        ⟨81927, false, false, [], []⟩,
        ⟨81928, false, false, [], []⟩,
        ⟨81928, false, false, [], []⟩
      ]⟩,
    ⟨[30823, 91603], [30823, 91603], .contexts []⟩,
    ⟨[93919, 3], [30823, 91603], .contexts [
        ⟨81913, false, false, [], []⟩,
        ⟨81917, false, false, [], []⟩,
        ⟨81930, false, false, [], []⟩,
        ⟨81930, false, false, [], []⟩
      ]⟩,
    ⟨[30827], [30823, 29301], .source 15478⟩,
    ⟨[88321, 3], [88321, 3], .contexts []⟩,
    ⟨[30829], [30809, 30827], .source 15479⟩,
    ⟨[88321, 3], [30829, 91599], .contexts [
        ⟨81933, false, false, [], []⟩,
        ⟨81929, true, false, [30806], [3]⟩,
        ⟨63, false, false, [30806, 93919], []⟩,
        ⟨65, false, false, [30806, 93919], []⟩,
        ⟨81931, false, false, [30806], [13]⟩,
        ⟨66593, false, false, [30806, 30823], []⟩,
        ⟨76334, false, false, [30806, 30823], []⟩,
        ⟨81932, true, false, [30806], [91599]⟩,
        ⟨81877, true, false, [], [30827, 91599]⟩,
        ⟨81934, true, false, [], [91599]⟩
      ]⟩,
    ⟨[30831], [30828], .source 15480⟩,
    ⟨[91599, 3], [30831, 88321], .contexts [
        ⟨81935, true, false, [30828], [3]⟩,
        ⟨20, false, false, [30828, 88321], []⟩,
        ⟨81936, true, false, [], [88321]⟩
      ]⟩,
    ⟨[30807, 88319], [30807, 88319], .contexts []⟩,
    ⟨[93919, 11], [93917], .contexts [
        ⟨81766, false, false, [], []⟩,
        ⟨81767, false, false, [], []⟩,
        ⟨81753, false, false, [], []⟩,
        ⟨81753, false, false, [], []⟩
      ]⟩,
    ⟨[93919, 10], [93919, 11], .contexts [
        ⟨54, false, false, [93919], []⟩
      ]⟩,
    ⟨[88319, 13], [88319, 13], .contexts []⟩,
    ⟨[93917], [93917], .contexts []⟩,
    ⟨[88319, 13], [30809, 93917], .contexts [
        ⟨81941, false, false, [], []⟩,
        ⟨81938, true, false, [30806], [13]⟩,
        ⟨49553, true, false, [], [13]⟩,
        ⟨81929, true, false, [30806], [11, 13]⟩,
        ⟨931, false, false, [30806, 93919], []⟩,
        ⟨81940, false, false, [30806], []⟩,
        ⟨81939, false, false, [30806], []⟩,
        ⟨81942, false, false, [30806], []⟩,
        ⟨81879, true, false, [], [93917]⟩
      ]⟩,
    ⟨[93917, 13], [30807, 88319], .contexts [
        ⟨81943, true, false, [30808], [13]⟩,
        ⟨59, false, false, [30808, 88319], []⟩,
        ⟨81881, true, false, [], [88319]⟩
      ]⟩,
    ⟨[30833], [30823, 30281], .source 15481⟩,
    ⟨[93521, 3], [93521, 3], .contexts []⟩,
    ⟨[30835], [30832], .source 15482⟩,
    ⟨[30832], [30832], .contexts []⟩,
    ⟨[93521, 3], [30835, 93917], .contexts [
        ⟨81946, false, false, [], []⟩,
        ⟨81945, false, false, [30832], [93521, 3]⟩,
        ⟨79776, true, false, [30832, 30823], [3]⟩,
        ⟨81931, true, false, [30832], [11, 3]⟩,
        ⟨545, false, false, [30832, 93919], []⟩,
        ⟨81940, false, false, [30832], []⟩,
        ⟨81939, false, false, [30832], []⟩,
        ⟨81942, false, false, [30832], []⟩,
        ⟨81948, true, false, [], [93917]⟩,
        ⟨81948, true, false, [], [93917]⟩,
        ⟨81947, true, false, [], [93917]⟩
      ]⟩,
    ⟨[30833], [30834], .contexts [
        ⟨81947, true, true, [], []⟩
      ]⟩,
    ⟨[30803, 83889], [30803, 83889], .contexts []⟩,
    ⟨[30803, 83887], [30803, 83887], .contexts []⟩,
    ⟨[83887, 15], [83887, 15], .contexts []⟩,
    ⟨[93915], [93915], .contexts []⟩,
    ⟨[83887, 15], [30805, 93915], .contexts [
        ⟨81953, false, false, [], []⟩,
        ⟨81952, true, false, [30802], [15]⟩,
        ⟨23335, true, false, [], [15]⟩,
        ⟨81951, true, false, [30802], [9, 15]⟩,
        ⟨81951, true, false, [30802], [9, 15]⟩,
        ⟨81925, true, false, [30802], [9, 15]⟩,
        ⟨81922, true, false, [30802], [9, 15]⟩,
        ⟨1671, false, false, [30802, 93917], []⟩,
        ⟨47, false, false, [30802, 93917], []⟩,
        ⟨81768, false, false, [30802], []⟩,
        ⟨81769, false, false, [30802], []⟩,
        ⟨81749, false, false, [30802], []⟩,
        ⟨81749, false, false, [30802], []⟩,
        ⟨81954, false, false, [30802], []⟩,
        ⟨81892, true, false, [], [93915]⟩
      ]⟩,
    ⟨[30829, 91599], [30829, 91599], .contexts []⟩,
    ⟨[30829, 91599], [30829, 91599], .contexts []⟩,
    ⟨[30829, 91597], [30829, 91597], .contexts []⟩,
    ⟨[91597, 3], [91597, 3], .contexts []⟩,
    ⟨[30828], [30828], .contexts []⟩,
    ⟨[91597, 3], [30831, 88319], .contexts [
        ⟨81959, false, false, [], []⟩,
        ⟨81958, true, false, [30828], [3]⟩,
        ⟨66585, true, false, [], [3]⟩,
        ⟨81957, true, false, [30828], [11, 3]⟩,
        ⟨81957, true, false, [30828], [11, 3]⟩,
        ⟨81956, true, false, [30828], [11, 3]⟩,
        ⟨81935, true, false, [30828], [11, 3]⟩,
        ⟨81933, true, false, [30828], [11, 3]⟩,
        ⟨545, false, false, [30828, 88321], []⟩,
        ⟨49917, false, false, [30828], []⟩,
        ⟨49916, false, false, [30828], []⟩,
        ⟨49919, false, false, [30828], []⟩,
        ⟨81960, true, false, [], [88319]⟩,
        ⟨81960, true, false, [], [88319]⟩,
        ⟨81936, true, false, [], [88319]⟩
      ]⟩,
    ⟨[30829], [30830], .contexts [
        ⟨81936, true, true, [], []⟩
      ]⟩,
    ⟨[88319, 3], [30829, 91597], .contexts [
        ⟨81961, true, false, [30830], [3]⟩,
        ⟨20, false, false, [30830, 91597], []⟩,
        ⟨81962, true, false, [], [91597]⟩
      ]⟩,
    ⟨[30809, 93917], [30809, 93917], .contexts []⟩,
    ⟨[88319, 13], [30809, 93917], .contexts [
        ⟨81941, false, false, [], []⟩,
        ⟨81943, false, false, [], []⟩,
        ⟨81964, false, false, [], []⟩,
        ⟨81964, false, false, [], []⟩
      ]⟩,
    ⟨[30837], [22659, 26855], .source 15483⟩,
    ⟨[86625], [86625], .contexts []⟩,
    ⟨[30839], [30807, 30837], .source 15484⟩,
    ⟨[93917, 7], [30839, 86625], .contexts [
        ⟨81965, true, false, [30808], [7]⟩,
        ⟨73, false, false, [30808, 88319], []⟩,
        ⟨74, false, false, [30808, 88319], []⟩,
        ⟨49921, false, false, [30808], [13]⟩,
        ⟨49914, false, false, [30808], [13]⟩,
        ⟨49915, false, false, [30808], [13]⟩,
        ⟨49915, false, false, [30808], [13]⟩,
        ⟨68466, false, false, [30808, 22659], []⟩,
        ⟨81966, true, false, [30808], [86625]⟩,
        ⟨81967, false, false, [30808, 30837], []⟩,
        ⟨81900, true, false, [], [30837, 86625]⟩,
        ⟨81968, true, false, [], [86625]⟩
      ]⟩,
    ⟨[30841], [30838], .source 15485⟩,
    ⟨[30809, 93915], [30809, 93915], .contexts []⟩,
    ⟨[30809, 93915], [30809, 93915], .contexts []⟩,
    ⟨[88317], [88317], .contexts []⟩,
    ⟨[93915, 13], [30807, 88317], .contexts [
        ⟨81972, true, false, [30808], [13]⟩,
        ⟨81971, true, false, [30808], [13]⟩,
        ⟨81750, true, false, [], [13]⟩,
        ⟨81965, true, false, [30808], [9, 13]⟩,
        ⟨942, false, false, [30808, 88319], []⟩,
        ⟨47, false, false, [30808, 88319], []⟩,
        ⟨49606, false, false, [30808], []⟩,
        ⟨49607, false, false, [30808], []⟩,
        ⟨49548, false, false, [30808], []⟩,
        ⟨49548, false, false, [30808], []⟩,
        ⟨81973, false, false, [30808], []⟩,
        ⟨81902, true, false, [], [88317]⟩
      ]⟩,
    ⟨[30835, 93917], [30835, 93917], .contexts []⟩,
    ⟨[30835, 93917], [30835, 93917], .contexts []⟩,
    ⟨[93521, 3], [30835, 93917], .contexts [
        ⟨81946, false, false, [], []⟩,
        ⟨81949, false, false, [], []⟩,
        ⟨81975, false, false, [], []⟩,
        ⟨81976, false, false, [], []⟩,
        ⟨81976, false, false, [], []⟩
      ]⟩,
    ⟨[30843], [30835, 30839], .source 15486⟩,
    ⟨[30845], [30842], .source 15487⟩,
    ⟨[30847], [30845, 30321], .source 15488⟩,
    ⟨[86625, 3], [30847, 85917], .contexts [
        ⟨81978, false, false, [30842], [86625, 3]⟩,
        ⟨81969, true, false, [30842, 30835], [3]⟩,
        ⟨81977, true, false, [30842], [7, 3]⟩,
        ⟨14556, false, false, [30842, 93521], []⟩,
        ⟨39, false, false, [30842, 93521], []⟩,
        ⟨79867, false, false, [30842], []⟩,
        ⟨79838, false, false, [30842, 30321], []⟩,
        ⟨81979, true, false, [], [30321, 85917]⟩,
        ⟨81980, true, false, [], [85917]⟩
      ]⟩,
    ⟨[30849], [30846], .source 15489⟩,
    ⟨[85917, 3], [30849, 86625], .contexts [
        ⟨81981, true, false, [30846], [3]⟩,
        ⟨20, false, false, [30846, 86625], []⟩,
        ⟨81982, true, false, [], [86625]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1281. -/
def y322TCIndexRaw1281 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[30834], [30834], .contexts []⟩,
    ⟨[93915, 3], [30833, 93519], .contexts [
        ⟨81750, true, false, [], [3]⟩,
        ⟨81977, true, false, [30834], [9, 3]⟩,
        ⟨573, false, false, [30834, 93521], []⟩,
        ⟨79869, false, false, [30834], []⟩,
        ⟨79868, false, false, [30834], []⟩,
        ⟨79871, false, false, [30834], []⟩,
        ⟨81984, true, false, [], [93519]⟩,
        ⟨81984, true, false, [], [93519]⟩,
        ⟨81950, true, false, [], [93519]⟩
      ]⟩,
    ⟨[93519, 3], [30835, 93915], .contexts [
        ⟨81985, true, false, [30832], [3]⟩,
        ⟨20, false, false, [30832, 93915], []⟩,
        ⟨81947, true, false, [], [93915]⟩
      ]⟩,
    ⟨[30805, 93915], [30805, 93915], .contexts []⟩,
    ⟨[93913, 15], [93913, 15], .contexts []⟩,
    ⟨[83885], [83885], .contexts []⟩,
    ⟨[93913, 15], [30803, 83885], .contexts [
        ⟨81988, false, false, [], []⟩,
        ⟨81746, true, false, [], [15]⟩,
        ⟨81987, true, false, [30804], [1, 15]⟩,
        ⟨81987, true, false, [30804], [1, 15]⟩,
        ⟨81955, true, false, [30804], [1, 15]⟩,
        ⟨81953, true, false, [30804], [1, 15]⟩,
        ⟨1666, false, false, [30804, 83887], []⟩,
        ⟨9, false, false, [30804, 83887], []⟩,
        ⟨23419, false, false, [30804], []⟩,
        ⟨23420, false, false, [30804], []⟩,
        ⟨23330, false, false, [30804], []⟩,
        ⟨23330, false, false, [30804], []⟩,
        ⟨81989, false, false, [30804], []⟩,
        ⟨81924, true, false, [], [83885]⟩
      ]⟩,
    ⟨[83885, 15], [30805, 93913], .contexts [
        ⟨81990, true, false, [30802], [15]⟩,
        ⟨1, false, false, [30802, 93913], []⟩,
        ⟨81870, true, false, [], [93913]⟩
      ]⟩,
    ⟨[30831, 88319], [30831, 88319], .contexts []⟩,
    ⟨[30831, 88317], [30831, 88317], .contexts []⟩,
    ⟨[30831, 88317], [30831, 88317], .contexts []⟩,
    ⟨[30830], [30830], .contexts []⟩,
    ⟨[88317, 3], [30829, 91595], .contexts [
        ⟨81994, true, false, [30830], [3]⟩,
        ⟨81993, true, false, [30830], [3]⟩,
        ⟨49549, true, false, [], [3]⟩,
        ⟨81992, true, false, [30830], [9, 3]⟩,
        ⟨81992, true, false, [30830], [9, 3]⟩,
        ⟨81961, true, false, [30830], [9, 3]⟩,
        ⟨81959, true, false, [30830], [9, 3]⟩,
        ⟨573, false, false, [30830, 91597], []⟩,
        ⟨79853, false, false, [30830], []⟩,
        ⟨76375, false, false, [30830], []⟩,
        ⟨79854, false, false, [30830], []⟩,
        ⟨81995, true, false, [], [91595]⟩,
        ⟨81995, true, false, [], [91595]⟩,
        ⟨81962, true, false, [], [91595]⟩
      ]⟩,
    ⟨[91595, 3], [30831, 88317], .contexts [
        ⟨81996, true, false, [30828], [3]⟩,
        ⟨20, false, false, [30828, 88317], []⟩,
        ⟨81936, true, false, [], [88317]⟩
      ]⟩,
    ⟨[30803, 83885], [30803, 83885], .contexts []⟩,
    ⟨[30803, 83885], [30803, 83885], .contexts []⟩,
    ⟨[30803, 83883], [30803, 83883], .contexts []⟩,
    ⟨[93913, 5], [93911], .contexts [
        ⟨81772, false, false, [], []⟩,
        ⟨81773, false, false, [], []⟩,
        ⟨81741, false, false, [], []⟩,
        ⟨81741, false, false, [], []⟩
      ]⟩,
    ⟨[83883, 15], [83883, 15], .contexts []⟩,
    ⟨[83883, 15], [30805, 93911], .contexts [
        ⟨82002, false, false, [], []⟩,
        ⟨82000, true, false, [30802], [15]⟩,
        ⟨23327, true, false, [], [15]⟩,
        ⟨81999, true, false, [30802], [5, 15]⟩,
        ⟨81999, true, false, [30802], [5, 15]⟩,
        ⟨81998, true, false, [30802], [5, 15]⟩,
        ⟨81990, true, false, [30802], [5, 15]⟩,
        ⟨81988, true, false, [30802], [5, 15]⟩,
        ⟨2072, false, false, [30802, 93913], []⟩,
        ⟨29, false, false, [30802, 93913], []⟩,
        ⟨82001, false, false, [30802], []⟩,
        ⟨81892, true, false, [], [93911]⟩
      ]⟩,
    ⟨[30805, 93911], [30805, 93911], .contexts []⟩,
    ⟨[83883, 3], [83881], .contexts [
        ⟨23424, false, false, [], []⟩,
        ⟨23425, false, false, [], []⟩,
        ⟨23322, false, false, [], []⟩,
        ⟨23322, false, false, [], []⟩
      ]⟩,
    ⟨[83883, 2], [83883, 3], .contexts [
        ⟨21, false, false, [83883], []⟩
      ]⟩,
    ⟨[93909, 15], [93909, 15], .contexts []⟩,
    ⟨[83881], [83881], .contexts []⟩,
    ⟨[93909, 15], [30803, 83881], .contexts [
        ⟨82007, false, false, [], []⟩,
        ⟨81739, true, false, [], [15]⟩,
        ⟨82004, true, false, [30804], [3, 15]⟩,
        ⟨82004, true, false, [30804], [3, 15]⟩,
        ⟨82003, true, false, [30804], [3, 15]⟩,
        ⟨82002, true, false, [30804], [3, 15]⟩,
        ⟨1141, false, false, [30804, 83883], []⟩,
        ⟨82006, false, false, [30804], []⟩,
        ⟨82005, false, false, [30804], []⟩,
        ⟨82008, false, false, [30804], []⟩,
        ⟨81924, true, false, [], [83881]⟩
      ]⟩,
    ⟨[83881, 15], [30805, 93909], .contexts [
        ⟨82009, true, false, [30802], [15]⟩,
        ⟨1, false, false, [30802, 93909], []⟩,
        ⟨81870, true, false, [], [93909]⟩
      ]⟩,
    ⟨[30803, 83881], [30803, 83881], .contexts []⟩,
    ⟨[30803, 83881], [30803, 83881], .contexts []⟩,
    ⟨[30803, 83879], [30803, 83879], .contexts []⟩,
    ⟨[30803, 83879], [30803, 83879], .contexts []⟩,
    ⟨[30803, 83879], [30803, 83879], .contexts []⟩,
    ⟨[30803, 83877], [30803, 83877], .contexts []⟩,
    ⟨[30803, 83877], [30803, 83877], .contexts []⟩,
    ⟨[83877, 1], [83877, 1], .contexts []⟩,
    ⟨[93909], [93909], .contexts []⟩,
    ⟨[83877, 1], [30805, 93909], .contexts [
        ⟨82018, false, false, [], []⟩,
        ⟨82017, true, false, [30802], [1]⟩,
        ⟨82016, true, false, [30802], [1]⟩,
        ⟨23315, true, false, [], [1]⟩,
        ⟨82015, true, false, [30802], [15, 1]⟩,
        ⟨82014, true, false, [30802], [15, 1]⟩,
        ⟨82013, true, false, [30802], [15, 1]⟩,
        ⟨23319, true, false, [], [15, 1]⟩,
        ⟨82012, true, false, [30802], [1, 15, 1]⟩,
        ⟨82012, true, false, [30802], [1, 15, 1]⟩,
        ⟨82011, true, false, [30802], [1, 15, 1]⟩,
        ⟨82009, true, false, [30802], [1, 15, 1]⟩,
        ⟨82007, true, false, [30802], [1, 15, 1]⟩,
        ⟨504, false, false, [30802, 93909], []⟩,
        ⟨82019, false, false, [30802], []⟩,
        ⟨81892, true, false, [], [93909]⟩
      ]⟩,
    ⟨[93907], [30803, 83877], .contexts [
        ⟨81735, true, false, [], []⟩,
        ⟨81735, true, false, [], []⟩,
        ⟨81777, true, false, [], []⟩,
        ⟨81776, true, false, [], []⟩,
        ⟨82020, true, false, [30804], [1]⟩,
        ⟨8, false, false, [30804, 83877], []⟩,
        ⟨81894, true, false, [], [83877]⟩,
        ⟨82016, false, false, [], []⟩,
        ⟨81868, true, false, [], [83877]⟩,
        ⟨81867, true, false, [], [83877]⟩,
        ⟨81914, true, false, [], [83877]⟩,
        ⟨82017, false, false, [], []⟩
      ]⟩,
    ⟨[93905], [30803, 83879], .contexts [
        ⟨81890, false, false, [30804], [93905]⟩,
        ⟨13, false, false, [30804, 30802], [93905]⟩,
        ⟨81778, true, false, [30804, 30802], []⟩,
        ⟨81733, true, false, [30804, 30802], []⟩,
        ⟨82021, false, false, [30804, 30802], [15]⟩,
        ⟨23313, false, false, [30804], []⟩,
        ⟨82013, false, false, [30804, 30802], []⟩,
        ⟨82014, false, false, [30804, 30802], []⟩,
        ⟨82015, false, false, [30804, 30802], []⟩,
        ⟨81894, true, false, [], [83879]⟩
      ]⟩,
    ⟨[83879, 13], [30805, 93903], .contexts [
        ⟨82022, true, false, [30802], [13]⟩,
        ⟨81730, false, false, [30802], []⟩,
        ⟨81779, false, false, [30802], []⟩,
        ⟨81891, true, false, [], [93903]⟩,
        ⟨81891, true, false, [], [93903]⟩,
        ⟨81890, true, false, [], [93903]⟩
      ]⟩,
    ⟨[93925], [81365, 3], .source 47027⟩,
    ⟨[81365, 3], [93925], .contexts [
        ⟨82024, true, false, [], []⟩
      ]⟩,
    ⟨[93925, 3], [81365], .contexts [
        ⟨82025, true, false, [], [3]⟩,
        ⟨20, false, false, [81365], []⟩,
        ⟨8926, false, false, [], []⟩
      ]⟩,
    ⟨[93925], [93925], .contexts []⟩,
    ⟨[81365, 3], [93925], .contexts [
        ⟨82025, false, false, [], []⟩,
        ⟨82027, false, false, [], []⟩,
        ⟨82027, false, false, [], []⟩
      ]⟩,
    ⟨[93925, 7], [86433], .contexts [
        ⟨82028, true, false, [], [7]⟩,
        ⟨140, false, false, [81365], []⟩,
        ⟨141, false, false, [81365], []⟩,
        ⟨19936, false, false, [], [3]⟩,
        ⟨8914, false, false, [], [3]⟩,
        ⟨8915, false, false, [], [3]⟩,
        ⟨8915, false, false, [], [3]⟩,
        ⟨37021, false, false, [], []⟩,
        ⟨37022, false, false, [], []⟩,
        ⟨37023, false, false, [], []⟩,
        ⟨37023, false, false, [], []⟩,
        ⟨46505, false, false, [], []⟩,
        ⟨46506, false, false, [], []⟩
      ]⟩,
    ⟨[4217, 93925], [4217, 93925], .contexts []⟩,
    ⟨[4217, 93925], [4217, 93925], .contexts []⟩,
    ⟨[93925, 9], [93925, 9], .contexts []⟩,
    ⟨[93925], [93925], .contexts []⟩,
    ⟨[8967, 82311], [8967, 82311], .contexts []⟩,
    ⟨[8967, 82311], [8967, 82311], .contexts []⟩,
    ⟨[8967, 92175], [8967, 92175], .contexts []⟩,
    ⟨[8967, 92175], [8967, 92175], .contexts []⟩,
    ⟨[93925, 11], [93925, 11], .contexts []⟩,
    ⟨[8967], [8967], .contexts []⟩,
    ⟨[8967], [8967], .contexts []⟩,
    ⟨[8967], [8967], .contexts [
        ⟨13, false, false, [], [8967]⟩,
        ⟨82039, false, false, [], []⟩,
        ⟨82040, false, false, [], []⟩
      ]⟩,
    ⟨[93925, 11], [8967, 92175], .contexts [
        ⟨82038, false, false, [], []⟩,
        ⟨82028, true, false, [], [11]⟩,
        ⟨144, false, false, [81365], []⟩,
        ⟨145, false, false, [81365], []⟩,
        ⟨11818, false, false, [], [3]⟩,
        ⟨82034, false, false, [], [3]⟩,
        ⟨82035, false, false, [], [3]⟩,
        ⟨82035, false, false, [], [3]⟩,
        ⟨70344, false, false, [8967], []⟩,
        ⟨82036, false, false, [], []⟩,
        ⟨82037, false, false, [], []⟩,
        ⟨75675, false, false, [8967], []⟩,
        ⟨82041, true, false, [], [92175]⟩
      ]⟩,
    ⟨[93925, 13], [18365, 85719], .contexts [
        ⟨82028, true, false, [], [13]⟩,
        ⟨147, false, false, [81365], []⟩,
        ⟨148, false, false, [81365], []⟩,
        ⟨19902, false, false, [], [3]⟩,
        ⟨19880, false, false, [], [3]⟩,
        ⟨19881, false, false, [], [3]⟩,
        ⟨19881, false, false, [], [3]⟩,
        ⟨46492, false, false, [], []⟩,
        ⟨46493, false, false, [], []⟩,
        ⟨46494, false, false, [], []⟩,
        ⟨46494, false, false, [], []⟩,
        ⟨46496, false, false, [], []⟩,
        ⟨46497, false, false, [], []⟩
      ]⟩,
    ⟨[93925, 15], [93925, 15], .contexts []⟩,
    ⟨[93925, 15], [8439, 89105], .contexts [
        ⟨82044, false, false, [], []⟩,
        ⟨82028, true, false, [], [15]⟩,
        ⟨151, false, false, [81365], []⟩,
        ⟨152, false, false, [81365], []⟩,
        ⟨8937, false, false, [], [3]⟩,
        ⟨8938, false, false, [], [3]⟩,
        ⟨54226, false, false, [], [3]⟩,
        ⟨11551, false, false, [], [3]⟩,
        ⟨11551, false, false, [], [3]⟩,
        ⟨54227, false, false, [], []⟩,
        ⟨54228, false, false, [], []⟩,
        ⟨54229, false, false, [], []⟩,
        ⟨54230, false, false, [], []⟩,
        ⟨54232, false, false, [], []⟩,
        ⟨54233, false, false, [], []⟩
      ]⟩,
    ⟨[93927], [93925, 5], .source 47028⟩,
    ⟨[93925, 5], [93927], .contexts [
        ⟨82046, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1282. -/
def y322TCIndexRaw1282 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93927], [93927], .contexts []⟩,
    ⟨[93927], [93927], .contexts []⟩,
    ⟨[93925, 5], [93927], .contexts [
        ⟨82047, false, false, [], []⟩,
        ⟨82048, false, false, [], []⟩,
        ⟨82049, false, false, [], []⟩,
        ⟨82049, false, false, [], []⟩
      ]⟩,
    ⟨[93927, 3], [93927, 3], .contexts []⟩,
    ⟨[93927, 3], [83949], .contexts [
        ⟨82051, false, false, [], []⟩,
        ⟨82050, true, false, [], [3]⟩,
        ⟨166, false, false, [93925], []⟩,
        ⟨169, false, false, [93925], []⟩,
        ⟨82026, false, false, [], [5, 3, 5]⟩,
        ⟨8925, false, false, [], [5, 3, 5]⟩,
        ⟨8926, false, false, [], [5, 3, 5]⟩,
        ⟨8926, false, false, [], [5, 3, 5]⟩,
        ⟨8929, false, false, [], [3, 5]⟩,
        ⟨11525, false, false, [], [3, 5]⟩,
        ⟨11504, false, false, [], [3, 5]⟩,
        ⟨11504, false, false, [], [3, 5]⟩,
        ⟨11508, false, false, [8409], [5]⟩,
        ⟨17142, true, false, [], [81357, 5]⟩,
        ⟨24040, false, false, [], []⟩,
        ⟨24041, false, false, [], []⟩,
        ⟨24042, false, false, [], []⟩,
        ⟨24042, false, false, [], []⟩,
        ⟨24048, false, false, [], []⟩
      ]⟩,
    ⟨[93927, 3], [83949], .contexts [
        ⟨82052, false, false, [], []⟩,
        ⟨672, true, false, [], [83949]⟩
      ]⟩,
    ⟨[83949, 3], [93927], .contexts [
        ⟨82053, true, false, [], [3]⟩,
        ⟨20, false, false, [93927], []⟩,
        ⟨82049, false, false, [], []⟩
      ]⟩,
    ⟨[93927], [93927], .contexts []⟩,
    ⟨[4217, 93927], [4217, 93927], .contexts []⟩,
    ⟨[93925, 9, 5], [4217, 93927], .contexts [
        ⟨82032, false, false, [], [5]⟩,
        ⟨82032, false, false, [], [5]⟩,
        ⟨82028, true, false, [], [9, 5]⟩,
        ⟨669, false, false, [81365], [5]⟩,
        ⟨670, false, false, [81365], [5]⟩,
        ⟨8933, false, false, [], [3, 5]⟩,
        ⟨8935, false, false, [], [3, 5]⟩,
        ⟨8931, false, false, [], [3, 5]⟩,
        ⟨8932, false, false, [], [3, 5]⟩,
        ⟨8932, false, false, [], [3, 5]⟩,
        ⟨82025, false, false, [4217], [5]⟩,
        ⟨82030, false, false, [], [5]⟩,
        ⟨82031, false, false, [], [5]⟩,
        ⟨82033, false, false, [4217], [5]⟩,
        ⟨7911, true, false, [], [93925, 5]⟩,
        ⟨82030, false, false, [], [5]⟩,
        ⟨82031, false, false, [], [5]⟩,
        ⟨82031, false, false, [], [5]⟩,
        ⟨82047, false, false, [4217], []⟩,
        ⟨82056, false, false, [], []⟩
      ]⟩,
    ⟨[4217, 93927], [4217, 93927], .contexts []⟩,
    ⟨[8967, 92185], [8967, 92185], .contexts []⟩,
    ⟨[8967, 92185], [8967, 92185], .contexts []⟩,
    ⟨[93927, 11], [93927, 11], .contexts []⟩,
    ⟨[93927, 11], [8967, 92185], .contexts [
        ⟨82061, false, false, [], []⟩,
        ⟨82050, true, false, [], [11]⟩,
        ⟨174, false, false, [93925], []⟩,
        ⟨175, false, false, [93925], []⟩,
        ⟨82038, false, false, [], [5]⟩,
        ⟨82042, false, false, [], [5]⟩,
        ⟨82036, false, false, [], [5]⟩,
        ⟨82037, false, false, [], [5]⟩,
        ⟨82037, false, false, [], [5]⟩,
        ⟨70479, false, false, [8967], []⟩,
        ⟨82059, false, false, [], []⟩,
        ⟨82060, false, false, [], []⟩,
        ⟨70495, false, false, [8967], []⟩,
        ⟨82041, true, false, [], [92185]⟩
      ]⟩,
    ⟨[93927, 15], [93927, 15], .contexts []⟩,
    ⟨[93927, 15], [8439, 89107], .contexts [
        ⟨82063, false, false, [], []⟩,
        ⟨82050, true, false, [], [15]⟩,
        ⟨184, false, false, [93925], []⟩,
        ⟨185, false, false, [93925], []⟩,
        ⟨82044, false, false, [], [5]⟩,
        ⟨82045, false, false, [], [5]⟩,
        ⟨54228, false, false, [], [5]⟩,
        ⟨54230, false, false, [], [5]⟩,
        ⟨54230, false, false, [], [5]⟩,
        ⟨54263, false, false, [], []⟩,
        ⟨54264, false, false, [], []⟩,
        ⟨54265, false, false, [], []⟩,
        ⟨54266, false, false, [], []⟩,
        ⟨54267, false, false, [], []⟩,
        ⟨54268, false, false, [], []⟩
      ]⟩,
    ⟨[93929], [93927, 1], .source 47029⟩,
    ⟨[93927, 1], [93929], .contexts [
        ⟨82065, true, false, [], []⟩
      ]⟩,
    ⟨[93929, 1], [93927], .contexts [
        ⟨82066, true, false, [], [1]⟩,
        ⟨8, false, false, [93927], []⟩,
        ⟨82049, false, false, [], []⟩
      ]⟩,
    ⟨[93929], [93929], .contexts []⟩,
    ⟨[93929], [93929], .contexts []⟩,
    ⟨[93927, 1], [93929], .contexts [
        ⟨82066, false, false, [], []⟩,
        ⟨82068, false, false, [], []⟩,
        ⟨82069, false, false, [], []⟩,
        ⟨82069, false, false, [], []⟩
      ]⟩,
    ⟨[14153, 93929], [14153, 93929], .contexts []⟩,
    ⟨[14153, 93929], [14153, 93929], .contexts []⟩,
    ⟨[93929, 3], [93929, 3], .contexts []⟩,
    ⟨[93929], [93929], .contexts []⟩,
    ⟨[93929, 3], [14153, 93929], .contexts [
        ⟨82073, false, false, [], []⟩,
        ⟨82070, true, false, [], [3]⟩,
        ⟨1098, false, false, [93927], []⟩,
        ⟨1100, false, false, [93927], []⟩,
        ⟨82051, false, false, [], [1, 3, 1]⟩,
        ⟨82053, false, false, [], [1, 3, 1]⟩,
        ⟨24041, false, false, [], [1, 3, 1]⟩,
        ⟨24042, false, false, [], [1, 3, 1]⟩,
        ⟨24042, false, false, [], [1, 3, 1]⟩,
        ⟨24050, false, false, [], [3, 1]⟩,
        ⟨24046, false, false, [], [3, 1]⟩,
        ⟨24047, false, false, [], [3, 1]⟩,
        ⟨24047, false, false, [], [3, 1]⟩,
        ⟨82054, false, false, [14153], [1]⟩,
        ⟨82066, false, false, [14153], []⟩,
        ⟨82071, false, false, [], []⟩,
        ⟨82072, false, false, [], []⟩,
        ⟨82074, false, false, [14153], []⟩
      ]⟩,
    ⟨[8967, 92187], [8967, 92187], .contexts []⟩,
    ⟨[8967, 92187], [8967, 92187], .contexts []⟩,
    ⟨[93929, 11], [93929, 11], .contexts []⟩,
    ⟨[93929, 11], [8967, 92187], .contexts [
        ⟨82078, false, false, [], []⟩,
        ⟨82070, true, false, [], [11]⟩,
        ⟨110, false, false, [93927], []⟩,
        ⟨111, false, false, [93927], []⟩,
        ⟨82061, false, false, [], [1]⟩,
        ⟨82062, false, false, [], [1]⟩,
        ⟨82059, false, false, [], [1]⟩,
        ⟨82060, false, false, [], [1]⟩,
        ⟨82060, false, false, [], [1]⟩,
        ⟨70507, false, false, [8967], []⟩,
        ⟨82076, false, false, [], []⟩,
        ⟨82077, false, false, [], []⟩,
        ⟨70517, false, false, [8967], []⟩,
        ⟨82041, true, false, [], [92187]⟩
      ]⟩,
    ⟨[8439, 89109], [8439, 89109], .contexts []⟩,
    ⟨[8439, 89109], [8439, 89109], .contexts []⟩,
    ⟨[93929, 15], [93929, 15], .contexts []⟩,
    ⟨[93929, 15], [8439, 89109], .contexts [
        ⟨82082, false, false, [], []⟩,
        ⟨82070, true, false, [], [15]⟩,
        ⟨121, false, false, [93927], []⟩,
        ⟨122, false, false, [93927], []⟩,
        ⟨82063, false, false, [], [1]⟩,
        ⟨82064, false, false, [], [1]⟩,
        ⟨54264, false, false, [], [1]⟩,
        ⟨54266, false, false, [], [1]⟩,
        ⟨54266, false, false, [], [1]⟩,
        ⟨54271, false, false, [8439], []⟩,
        ⟨82080, false, false, [], []⟩,
        ⟨82081, false, false, [], []⟩,
        ⟨54280, false, false, [8439], []⟩,
        ⟨24084, true, false, [], [89109]⟩
      ]⟩,
    ⟨[93929, 11], [8967, 92187], .contexts [
        ⟨82079, false, false, [], []⟩
      ]⟩,
    ⟨[30851], [8967, 27459], .source 15490⟩,
    ⟨[30851, 91827], [30851, 91827], .contexts []⟩,
    ⟨[30851, 91827], [30851, 91827], .contexts []⟩,
    ⟨[30853], [30850], .source 15491⟩,
    ⟨[30850], [30850], .contexts []⟩,
    ⟨[91827, 13], [30853, 93929], .contexts [
        ⟨82087, true, false, [30850], [13]⟩,
        ⟨82086, true, false, [30850], [13]⟩,
        ⟨67635, true, false, [], [13]⟩,
        ⟨82085, false, false, [30850], [91829, 11, 13]⟩,
        ⟨70533, true, false, [30850, 8967], [11, 13]⟩,
        ⟨82077, true, false, [30850], [13, 11, 13]⟩,
        ⟨82077, true, false, [30850], [13, 11, 13]⟩,
        ⟨82076, true, false, [30850], [13, 11, 13]⟩,
        ⟨82084, true, false, [30850], [13, 11, 13]⟩,
        ⟨82078, true, false, [30850], [13, 11, 13]⟩,
        ⟨1109, false, false, [30850, 93929], []⟩,
        ⟨82074, false, false, [30850], []⟩,
        ⟨82089, true, false, [], [93929]⟩,
        ⟨82089, true, false, [], [93929]⟩,
        ⟨82088, true, false, [], [93929]⟩
      ]⟩,
    ⟨[93931], [93929, 9], .source 47030⟩,
    ⟨[93929, 9], [93931], .contexts [
        ⟨82091, true, false, [], []⟩
      ]⟩,
    ⟨[93931, 9], [93929], .contexts [
        ⟨82092, true, false, [], [9]⟩,
        ⟨46, false, false, [93929], []⟩,
        ⟨82069, false, false, [], []⟩
      ]⟩,
    ⟨[93931], [93931], .contexts []⟩,
    ⟨[93931], [93931], .contexts []⟩,
    ⟨[93929, 9], [93931], .contexts [
        ⟨82092, false, false, [], []⟩,
        ⟨82094, false, false, [], []⟩,
        ⟨82095, false, false, [], []⟩,
        ⟨82095, false, false, [], []⟩
      ]⟩,
    ⟨[4217, 93931], [4217, 93931], .contexts []⟩,
    ⟨[4217, 93931], [4217, 93931], .contexts []⟩,
    ⟨[93929, 1, 9, 1, 9], [4217, 93931], .contexts [
        ⟨82067, false, false, [], [9, 1, 9]⟩,
        ⟨82048, false, false, [], [9, 1, 9]⟩,
        ⟨82049, false, false, [], [9, 1, 9]⟩,
        ⟨82049, false, false, [], [9, 1, 9]⟩,
        ⟨82050, true, false, [], [9, 1, 9]⟩,
        ⟨1265, false, false, [93925], [1, 9]⟩,
        ⟨1266, false, false, [93925], [1, 9]⟩,
        ⟨82057, false, false, [], [1, 9]⟩,
        ⟨82058, false, false, [], [1, 9]⟩,
        ⟨82055, false, false, [4217], [1, 9]⟩,
        ⟨7911, true, false, [], [93927, 1, 9]⟩,
        ⟨82056, false, false, [], [1, 9]⟩,
        ⟨82058, false, false, [], [1, 9]⟩,
        ⟨82058, false, false, [], [1, 9]⟩,
        ⟨82066, false, false, [4217], [9]⟩,
        ⟨82092, false, false, [4217], []⟩,
        ⟨82097, false, false, [], []⟩,
        ⟨82098, false, false, [], []⟩
      ]⟩,
    ⟨[93931, 1], [93931, 1], .contexts []⟩,
    ⟨[93931], [93931], .contexts []⟩,
    ⟨[14153, 93931], [14153, 93931], .contexts []⟩,
    ⟨[14153, 93931], [14153, 93931], .contexts []⟩,
    ⟨[93931, 3], [93931, 3], .contexts []⟩,
    ⟨[30851, 91825], [30851, 91825], .contexts []⟩,
    ⟨[30851, 91825], [30851, 91825], .contexts []⟩,
    ⟨[30851, 91825], [30851, 91825], .contexts [
        ⟨67767, false, false, [30851], []⟩
      ]⟩,
    ⟨[30851, 91825], [30851, 91825], .contexts [
        ⟨13, true, false, [], [30851, 91825]⟩
      ]⟩,
    ⟨[93931, 13], [30851, 91825], .contexts [
        ⟨82096, true, false, [], [13]⟩,
        ⟨201, false, false, [93929], []⟩,
        ⟨202, false, false, [93929], []⟩,
        ⟨82090, true, false, [30852], [13, 9]⟩,
        ⟨59, false, false, [30852, 91827], [9]⟩,
        ⟨82088, false, true, [], [91827, 9]⟩,
        ⟨82086, false, false, [], [9]⟩,
        ⟨82087, false, false, [], [9]⟩,
        ⟨82087, false, false, [], [9]⟩,
        ⟨67631, false, false, [30851], []⟩,
        ⟨82105, false, false, [], []⟩,
        ⟨82106, false, false, [], []⟩,
        ⟨82107, false, false, [], []⟩,
        ⟨82108, false, false, [], []⟩
      ]⟩,
    ⟨[8439, 89111], [8439, 89111], .contexts []⟩,
    ⟨[8439, 89111], [8439, 89111], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1283. -/
def y322TCIndexRaw1283 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93931, 15], [93931, 15], .contexts []⟩,
    ⟨[93931, 15], [8439, 89111], .contexts [
        ⟨82112, false, false, [], []⟩,
        ⟨82096, true, false, [], [15]⟩,
        ⟨205, false, false, [93929], []⟩,
        ⟨206, false, false, [93929], []⟩,
        ⟨82082, false, false, [], [9]⟩,
        ⟨82083, false, false, [], [9]⟩,
        ⟨82080, false, false, [], [9]⟩,
        ⟨82081, false, false, [], [9]⟩,
        ⟨82081, false, false, [], [9]⟩,
        ⟨54291, false, false, [8439], []⟩,
        ⟨82110, false, false, [], []⟩,
        ⟨82111, false, false, [], []⟩,
        ⟨54299, false, false, [8439], []⟩,
        ⟨24084, true, false, [], [89111]⟩
      ]⟩,
    ⟨[89111, 15], [8441, 93931], .contexts [
        ⟨82113, true, false, [8438], [15]⟩,
        ⟨1, false, false, [8438, 93931], []⟩,
        ⟨11545, true, false, [], [93931]⟩
      ]⟩,
    ⟨[93933], [93931, 11], .source 47031⟩,
    ⟨[93931, 11], [93933], .contexts [
        ⟨82115, true, false, [], []⟩
      ]⟩,
    ⟨[93933, 11], [93931], .contexts [
        ⟨82116, true, false, [], [11]⟩,
        ⟨53, false, false, [93931], []⟩,
        ⟨82095, false, false, [], []⟩
      ]⟩,
    ⟨[93933], [93933], .contexts []⟩,
    ⟨[93933], [93933], .contexts []⟩,
    ⟨[93931, 11], [93933], .contexts [
        ⟨82116, false, false, [], []⟩,
        ⟨82118, false, false, [], []⟩,
        ⟨82119, false, false, [], []⟩,
        ⟨82119, false, false, [], []⟩
      ]⟩,
    ⟨[93933], [93933], .contexts []⟩,
    ⟨[93933, 1], [4217, 93933], .contexts [
        ⟨82120, true, false, [], [1]⟩,
        ⟨562, false, false, [93931], []⟩,
        ⟨563, false, false, [93931], []⟩,
        ⟨82100, false, false, [], [11]⟩,
        ⟨82100, false, false, [], [11]⟩,
        ⟨82096, true, false, [], [1, 11]⟩,
        ⟨691, false, false, [93929], [11]⟩,
        ⟨694, false, false, [93929], [11]⟩,
        ⟨82099, false, false, [], [11]⟩,
        ⟨82101, false, false, [4217], [11]⟩,
        ⟨7911, true, false, [], [93931, 11]⟩,
        ⟨82097, false, false, [], [11]⟩,
        ⟨82098, false, false, [], [11]⟩,
        ⟨82098, false, false, [], [11]⟩,
        ⟨82116, false, false, [4217], []⟩,
        ⟨82121, false, false, [4217], []⟩
      ]⟩,
    ⟨[93933, 1], [4217, 93933], .contexts [
        ⟨82122, false, false, [], []⟩,
        ⟨7911, true, false, [], [93933]⟩
      ]⟩,
    ⟨[93931, 3, 11], [14153, 93933], .contexts [
        ⟨82104, false, false, [], [11]⟩,
        ⟨82104, false, false, [], [11]⟩,
        ⟨82096, true, false, [], [3, 11]⟩,
        ⟨196, false, false, [93929], [11]⟩,
        ⟨197, false, false, [93929], [11]⟩,
        ⟨82073, false, false, [], [9, 11]⟩,
        ⟨82075, false, false, [], [9, 11]⟩,
        ⟨24049, true, false, [], [93929, 9, 11]⟩,
        ⟨82071, false, false, [], [9, 11]⟩,
        ⟨82072, false, false, [], [9, 11]⟩,
        ⟨82072, false, false, [], [9, 11]⟩,
        ⟨82092, false, false, [14153], [11]⟩,
        ⟨82102, false, false, [], [11]⟩,
        ⟨82103, false, false, [], [11]⟩,
        ⟨82101, false, false, [14153], [11]⟩,
        ⟨24049, true, false, [], [93931, 11]⟩,
        ⟨82102, false, false, [], [11]⟩,
        ⟨82103, false, false, [], [11]⟩,
        ⟨82103, false, false, [], [11]⟩,
        ⟨82116, false, false, [14153], []⟩
      ]⟩,
    ⟨[14153, 93933], [14153, 93933], .contexts []⟩,
    ⟨[14153, 93933], [14153, 93933], .contexts []⟩,
    ⟨[14153, 93933], [14153, 93933], .contexts []⟩,
    ⟨[93933, 3], [93933, 3], .contexts []⟩,
    ⟨[8967, 92191], [8967, 92191], .contexts []⟩,
    ⟨[8967, 92191], [8967, 92191], .contexts []⟩,
    ⟨[93933, 9], [93933, 9], .contexts []⟩,
    ⟨[93933, 9], [8967, 92191], .contexts [
        ⟨82131, false, false, [], []⟩,
        ⟨82120, true, false, [], [9]⟩,
        ⟨221, false, false, [93931], []⟩,
        ⟨224, false, false, [93931], []⟩,
        ⟨82093, false, false, [], [11, 9, 11]⟩,
        ⟨82068, false, false, [], [11, 9, 11]⟩,
        ⟨82069, false, false, [], [11, 9, 11]⟩,
        ⟨82069, false, false, [], [11, 9, 11]⟩,
        ⟨82084, false, false, [], [9, 11]⟩,
        ⟨82076, false, false, [], [9, 11]⟩,
        ⟨82077, false, false, [], [9, 11]⟩,
        ⟨82077, false, false, [], [9, 11]⟩,
        ⟨70570, false, false, [8967], [11]⟩,
        ⟨70591, false, false, [8967], []⟩,
        ⟨82129, false, false, [], []⟩,
        ⟨82130, false, false, [], []⟩,
        ⟨70600, false, false, [8967], []⟩
      ]⟩,
    ⟨[93933, 9], [8967, 92191], .contexts [
        ⟨82132, false, false, [], []⟩,
        ⟨82041, true, false, [], [92191]⟩
      ]⟩,
    ⟨[92191, 9], [8965, 93933], .contexts [
        ⟨82133, true, false, [8966], [9]⟩,
        ⟨46, false, false, [8966, 93933], []⟩,
        ⟨11815, true, false, [], [93933]⟩
      ]⟩,
    ⟨[8439, 89113], [8439, 89113], .contexts []⟩,
    ⟨[8439, 89113], [8439, 89113], .contexts []⟩,
    ⟨[93933, 15], [8439, 89113], .contexts [
        ⟨82120, true, false, [], [15]⟩,
        ⟨231, false, false, [93931], []⟩,
        ⟨232, false, false, [93931], []⟩,
        ⟨82112, false, false, [], [11]⟩,
        ⟨82113, false, false, [], [11]⟩,
        ⟨82110, false, false, [], [11]⟩,
        ⟨82111, false, false, [], [11]⟩,
        ⟨82111, false, false, [], [11]⟩,
        ⟨54312, false, false, [8439], []⟩,
        ⟨82135, false, false, [], []⟩,
        ⟨82136, false, false, [], []⟩,
        ⟨54320, false, false, [8439], []⟩,
        ⟨24084, true, false, [], [89113]⟩
      ]⟩,
    ⟨[93935], [93933, 13], .source 47032⟩,
    ⟨[93933, 13], [93935], .contexts [
        ⟨82138, true, false, [], []⟩
      ]⟩,
    ⟨[93935, 13], [93933], .contexts [
        ⟨82139, true, false, [], [13]⟩,
        ⟨59, false, false, [93933], []⟩,
        ⟨82119, false, false, [], []⟩
      ]⟩,
    ⟨[93935], [93935], .contexts []⟩,
    ⟨[93933, 13], [93935], .contexts [
        ⟨82139, false, false, [], []⟩,
        ⟨82141, false, false, [], []⟩,
        ⟨82141, false, false, [], []⟩
      ]⟩,
    ⟨[14153, 93935], [14153, 93935], .contexts []⟩,
    ⟨[14153, 93935], [14153, 93935], .contexts []⟩,
    ⟨[14153, 93935], [14153, 93935], .contexts []⟩,
    ⟨[93935, 3], [93935, 3], .contexts []⟩,
    ⟨[93935, 3], [14153, 93935], .contexts [
        ⟨82146, false, false, [], []⟩,
        ⟨82142, true, false, [], [3]⟩,
        ⟨63, false, false, [93933], []⟩,
        ⟨65, false, false, [93933], []⟩,
        ⟨82128, false, false, [], [13]⟩,
        ⟨82128, false, false, [], [13]⟩,
        ⟨82120, true, false, [], [3, 13]⟩,
        ⟨215, false, false, [93931], [13]⟩,
        ⟨216, false, false, [93931], [13]⟩,
        ⟨82124, false, false, [], [13]⟩,
        ⟨82125, false, false, [], [13]⟩,
        ⟨82126, false, false, [], [13]⟩,
        ⟨82127, false, false, [], [13]⟩,
        ⟨82121, false, false, [14153], [13]⟩,
        ⟨24049, true, false, [], [93933, 13]⟩,
        ⟨82125, false, false, [], [13]⟩,
        ⟨82127, false, false, [], [13]⟩,
        ⟨82127, false, false, [], [13]⟩,
        ⟨82139, false, false, [14153], []⟩,
        ⟨82143, false, false, [], []⟩,
        ⟨82144, false, false, [], []⟩,
        ⟨82145, false, false, [], []⟩
      ]⟩,
    ⟨[8967, 92835], [8967, 92835], .contexts []⟩,
    ⟨[8967, 92835], [8967, 92835], .contexts []⟩,
    ⟨[93935, 9], [93935, 9], .contexts []⟩,
    ⟨[93935, 9], [8967, 92835], .contexts [
        ⟨82150, false, false, [], []⟩,
        ⟨82142, true, false, [], [9]⟩,
        ⟨77, false, false, [93933], []⟩,
        ⟨78, false, false, [93933], []⟩,
        ⟨82131, false, false, [], [13]⟩,
        ⟨82133, false, false, [], [13]⟩,
        ⟨82129, false, false, [], [13]⟩,
        ⟨82130, false, false, [], [13]⟩,
        ⟨82130, false, false, [], [13]⟩,
        ⟨75734, false, false, [8967], []⟩,
        ⟨82148, false, false, [], []⟩,
        ⟨82149, false, false, [], []⟩,
        ⟨75742, false, false, [8967], []⟩,
        ⟨82041, true, false, [], [92835]⟩
      ]⟩,
    ⟨[93935, 11], [30851, 91825], .contexts [
        ⟨82142, true, false, [], [11]⟩,
        ⟨82, false, false, [93933], []⟩,
        ⟨83, false, false, [93933], []⟩,
        ⟨82117, false, false, [], [13]⟩,
        ⟨82094, false, false, [], [13]⟩,
        ⟨82095, false, false, [], [13]⟩,
        ⟨82095, false, false, [], [13]⟩,
        ⟨82109, false, false, [], []⟩,
        ⟨82105, false, false, [], []⟩,
        ⟨82106, false, false, [], []⟩,
        ⟨82106, false, false, [], []⟩,
        ⟨82107, false, false, [], []⟩,
        ⟨82108, false, false, [], []⟩
      ]⟩,
    ⟨[91825, 11], [30853, 93935], .contexts [
        ⟨82152, true, false, [30850], [11]⟩,
        ⟨53, false, false, [30850, 93935], []⟩,
        ⟨82088, true, false, [], [93935]⟩
      ]⟩,
    ⟨[93937], [93935, 15], .source 47033⟩,
    ⟨[93935, 15], [93937], .contexts [
        ⟨82154, true, false, [], []⟩
      ]⟩,
    ⟨[93937], [93937], .contexts []⟩,
    ⟨[93937], [93937], .contexts []⟩,
    ⟨[93935, 15], [93937], .contexts [
        ⟨82155, false, false, [], []⟩,
        ⟨82156, false, false, [], []⟩,
        ⟨82157, false, false, [], []⟩,
        ⟨82157, false, false, [], []⟩
      ]⟩,
    ⟨[14153, 93937], [14153, 93937], .contexts []⟩,
    ⟨[14153, 93937], [14153, 93937], .contexts []⟩,
    ⟨[14153, 93937], [14153, 93937], .contexts []⟩,
    ⟨[93937], [93937], .contexts []⟩,
    ⟨[8967, 92837], [8967, 92837], .contexts []⟩,
    ⟨[8967, 92837], [8967, 92837], .contexts []⟩,
    ⟨[93937, 9], [93937, 9], .contexts []⟩,
    ⟨[8439, 89117], [8439, 89117], .contexts []⟩,
    ⟨[93937, 13], [8439, 89117], .contexts [
        ⟨82158, true, false, [], [13]⟩,
        ⟨259, false, false, [93935], []⟩,
        ⟨262, false, false, [93935], []⟩,
        ⟨82140, false, false, [], [15, 13, 15]⟩,
        ⟨82118, false, false, [], [15, 13, 15]⟩,
        ⟨82119, false, false, [], [15, 13, 15]⟩,
        ⟨82119, false, false, [], [15, 13, 15]⟩,
        ⟨82137, false, false, [], [13, 15]⟩,
        ⟨82135, false, false, [], [13, 15]⟩,
        ⟨82136, false, false, [], [13, 15]⟩,
        ⟨82136, false, false, [], [13, 15]⟩,
        ⟨54338, false, false, [8439], [15]⟩,
        ⟨54347, false, false, [8439], []⟩,
        ⟨82166, false, false, [], []⟩,
        ⟨54355, false, false, [8439], []⟩
      ]⟩,
    ⟨[93937, 13], [8439, 89117], .contexts [
        ⟨82167, false, false, [], []⟩,
        ⟨24084, true, false, [], [89117]⟩
      ]⟩,
    ⟨[93939], [93937, 1], .source 47034⟩,
    ⟨[93937, 1], [93939], .contexts [
        ⟨82169, true, false, [], []⟩
      ]⟩,
    ⟨[93939, 1], [93937], .contexts [
        ⟨82170, true, false, [], [1]⟩,
        ⟨8, false, false, [93937], []⟩,
        ⟨82157, false, false, [], []⟩
      ]⟩,
    ⟨[93939], [93939], .contexts []⟩,
    ⟨[93939], [93939], .contexts []⟩,
    ⟨[93941], [93939, 3], .source 47035⟩,
    ⟨[93939, 3], [93941], .contexts [
        ⟨82174, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1284. -/
def y322TCIndexRaw1284 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93941, 3], [93939], .contexts [
        ⟨82175, true, false, [], [3]⟩,
        ⟨20, false, false, [93939], []⟩,
        ⟨82173, false, false, [], []⟩
      ]⟩,
    ⟨[93941], [93941], .contexts []⟩,
    ⟨[93941], [93941], .contexts []⟩,
    ⟨[93939, 1], [93937], .contexts [
        ⟨82171, false, false, [], []⟩
      ]⟩,
    ⟨[93939, 1, 3, 1], [14153, 93939], .contexts [
        ⟨82179, false, false, [], [3, 1]⟩,
        ⟨82156, false, false, [], [3, 1]⟩,
        ⟨82157, false, false, [], [3, 1]⟩,
        ⟨82157, false, false, [], [3, 1]⟩,
        ⟨82158, true, false, [], [3, 1]⟩,
        ⟨19, false, false, [93935], [1]⟩,
        ⟨22, false, false, [93935], [1]⟩,
        ⟨82146, false, false, [], [15, 1]⟩,
        ⟨82147, false, false, [], [15, 1]⟩,
        ⟨24049, true, false, [], [93935, 15, 1]⟩,
        ⟨82143, false, false, [], [15, 1]⟩,
        ⟨82145, false, false, [], [15, 1]⟩,
        ⟨82145, false, false, [], [15, 1]⟩,
        ⟨82155, false, false, [14153], [1]⟩,
        ⟨82159, false, false, [], [1]⟩,
        ⟨82160, false, false, [], [1]⟩,
        ⟨82161, false, false, [], [1]⟩,
        ⟨82162, false, false, [14153], [1]⟩,
        ⟨24049, true, false, [], [93937, 1]⟩,
        ⟨82159, false, false, [], [1]⟩,
        ⟨82161, false, false, [], [1]⟩,
        ⟨82161, false, false, [], [1]⟩,
        ⟨82170, false, false, [14153], []⟩
      ]⟩,
    ⟨[14153, 93939], [14153, 93939], .contexts []⟩,
    ⟨[14153, 93939], [14153, 93939], .contexts []⟩,
    ⟨[14153, 93939], [14153, 93939], .contexts []⟩,
    ⟨[14153, 93941], [14153, 93941], .contexts []⟩,
    ⟨[14153, 93941], [14153, 93941], .contexts []⟩,
    ⟨[14153, 93941], [14153, 93941], .contexts []⟩,
    ⟨[93941, 1], [93941, 1], .contexts []⟩,
    ⟨[93941], [93941], .contexts []⟩,
    ⟨[93943], [93941, 5], .source 47036⟩,
    ⟨[93941, 5], [93943], .contexts [
        ⟨82189, true, false, [], []⟩
      ]⟩,
    ⟨[93943, 5], [93941], .contexts [
        ⟨82190, true, false, [], [5]⟩,
        ⟨28, false, false, [93941], []⟩,
        ⟨82178, false, false, [], []⟩
      ]⟩,
    ⟨[93943], [93943], .contexts []⟩,
    ⟨[93943], [93943], .contexts []⟩,
    ⟨[14153, 93943], [14153, 93943], .contexts []⟩,
    ⟨[14153, 93943], [14153, 93943], .contexts []⟩,
    ⟨[93941, 1, 5], [14153, 93943], .contexts [
        ⟨82187, false, false, [], [5]⟩,
        ⟨82187, false, false, [], [5]⟩,
        ⟨82178, true, false, [], [1, 5]⟩,
        ⟨82178, true, false, [], [1, 5]⟩,
        ⟨82177, true, false, [], [1, 5]⟩,
        ⟨82175, true, false, [], [1, 5]⟩,
        ⟨130, false, false, [93939], [5]⟩,
        ⟨133, false, false, [93939], [5]⟩,
        ⟨82180, false, false, [], [3, 5]⟩,
        ⟨82181, false, false, [], [3, 5]⟩,
        ⟨82182, false, false, [], [3, 5]⟩,
        ⟨82183, false, false, [], [3, 5]⟩,
        ⟨82175, false, false, [14153], [5]⟩,
        ⟨82184, false, false, [], [5]⟩,
        ⟨82185, false, false, [], [5]⟩,
        ⟨82186, false, false, [], [5]⟩,
        ⟨82188, false, false, [14153], [5]⟩,
        ⟨24049, true, false, [], [93941, 5]⟩,
        ⟨82184, false, false, [], [5]⟩,
        ⟨82186, false, false, [], [5]⟩,
        ⟨82186, false, false, [], [5]⟩,
        ⟨82190, false, false, [14153], []⟩,
        ⟨82194, false, false, [], []⟩,
        ⟨82195, false, false, [], []⟩
      ]⟩,
    ⟨[93943], [93943], .contexts []⟩,
    ⟨[93943, 1], [14153, 93943], .contexts [
        ⟨82193, true, false, [], [1]⟩,
        ⟨82193, true, false, [], [1]⟩,
        ⟨82192, true, false, [], [1]⟩,
        ⟨82190, true, false, [], [1]⟩,
        ⟨161, false, false, [93941], []⟩,
        ⟨162, false, false, [93941], []⟩,
        ⟨82196, false, false, [], []⟩,
        ⟨82197, false, false, [14153], []⟩,
        ⟨24049, true, false, [], [93943]⟩
      ]⟩,
    ⟨[93945], [93943, 9], .source 47037⟩,
    ⟨[93943, 9], [93945], .contexts [
        ⟨82199, true, false, [], []⟩
      ]⟩,
    ⟨[93945, 9], [93943], .contexts [
        ⟨82200, true, false, [], [9]⟩,
        ⟨46, false, false, [93943], []⟩,
        ⟨82193, false, false, [], []⟩
      ]⟩,
    ⟨[93947], [93945, 11], .source 47038⟩,
    ⟨[93945, 11], [93947], .contexts [
        ⟨82202, true, false, [], []⟩
      ]⟩,
    ⟨[93945], [93945], .contexts []⟩,
    ⟨[93949], [93947, 1], .source 47039⟩,
    ⟨[93947, 1], [93949], .contexts [
        ⟨82205, true, false, [], []⟩
      ]⟩,
    ⟨[93947], [93947], .contexts []⟩,
    ⟨[93951], [93949, 13], .source 47040⟩,
    ⟨[93949, 13], [93951], .contexts [
        ⟨82208, true, false, [], []⟩
      ]⟩,
    ⟨[93949], [93949], .contexts []⟩,
    ⟨[93953], [93951, 15], .source 47041⟩,
    ⟨[93951, 15], [93953], .contexts [
        ⟨82211, true, false, [], []⟩
      ]⟩,
    ⟨[93951], [93951], .contexts []⟩,
    ⟨[93953, 15], [93951], .contexts [
        ⟨82212, true, false, [], [15]⟩,
        ⟨1, false, false, [93951], []⟩,
        ⟨82213, false, false, [], []⟩
      ]⟩,
    ⟨[93955], [93953, 1], .source 47042⟩,
    ⟨[93953, 1], [93955], .contexts [
        ⟨82215, true, false, [], []⟩
      ]⟩,
    ⟨[93953], [93953], .contexts []⟩,
    ⟨[93955, 1], [93953], .contexts [
        ⟨82216, true, false, [], [1]⟩,
        ⟨8, false, false, [93953], []⟩,
        ⟨82217, false, false, [], []⟩
      ]⟩,
    ⟨[93957], [93955, 3], .source 47043⟩,
    ⟨[93955, 3], [93957], .contexts [
        ⟨82219, true, false, [], []⟩
      ]⟩,
    ⟨[93955], [93955], .contexts []⟩,
    ⟨[93959], [93957, 5], .source 47044⟩,
    ⟨[93957, 5], [93959], .contexts [
        ⟨82222, true, false, [], []⟩
      ]⟩,
    ⟨[93957], [93957], .contexts []⟩,
    ⟨[93961], [93959, 1], .source 47045⟩,
    ⟨[93959, 1], [93961], .contexts [
        ⟨82225, true, false, [], []⟩
      ]⟩,
    ⟨[93959], [93959], .contexts []⟩,
    ⟨[93963], [93961, 9], .source 47046⟩,
    ⟨[93961, 9], [93963], .contexts [
        ⟨82228, true, false, [], []⟩
      ]⟩,
    ⟨[93961], [93961], .contexts []⟩,
    ⟨[93965], [93963, 11], .source 47047⟩,
    ⟨[93963, 11], [93965], .contexts [
        ⟨82231, true, false, [], []⟩
      ]⟩,
    ⟨[93963], [93963], .contexts []⟩,
    ⟨[93965, 11], [93963], .contexts [
        ⟨82232, true, false, [], [11]⟩,
        ⟨53, false, false, [93963], []⟩,
        ⟨82233, false, false, [], []⟩
      ]⟩,
    ⟨[93967], [93965, 1], .source 47048⟩,
    ⟨[93965, 1], [93967], .contexts [
        ⟨82235, true, false, [], []⟩
      ]⟩,
    ⟨[93965], [93965], .contexts []⟩,
    ⟨[93967, 1], [93965], .contexts [
        ⟨82236, true, false, [], [1]⟩,
        ⟨8, false, false, [93965], []⟩,
        ⟨82237, false, false, [], []⟩
      ]⟩,
    ⟨[93969], [93967, 13], .source 47049⟩]

/-- Exact literal claimed equations and contextual derivations, block 1285. -/
def y322TCIndexRaw1285 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93967, 13], [93969], .contexts [
        ⟨82239, true, false, [], []⟩
      ]⟩,
    ⟨[93967], [93967], .contexts []⟩,
    ⟨[93971], [93969, 15], .source 47050⟩,
    ⟨[93969, 15], [93971], .contexts [
        ⟨82242, true, false, [], []⟩
      ]⟩,
    ⟨[93969], [93969], .contexts []⟩,
    ⟨[93973], [93971, 1], .source 47051⟩,
    ⟨[93971, 1], [93973], .contexts [
        ⟨82245, true, false, [], []⟩
      ]⟩,
    ⟨[93971], [93971], .contexts []⟩,
    ⟨[93975], [93973, 3], .source 47052⟩,
    ⟨[93973, 3], [93975], .contexts [
        ⟨82248, true, false, [], []⟩
      ]⟩,
    ⟨[93973], [93973], .contexts []⟩,
    ⟨[93977], [93975, 5], .source 47053⟩,
    ⟨[93975, 5], [93977], .contexts [
        ⟨82251, true, false, [], []⟩
      ]⟩,
    ⟨[93975], [93975], .contexts []⟩,
    ⟨[93977, 5], [93975], .contexts [
        ⟨82252, true, false, [], [5]⟩,
        ⟨28, false, false, [93975], []⟩,
        ⟨82253, false, false, [], []⟩
      ]⟩,
    ⟨[93979], [93977, 1], .source 47054⟩,
    ⟨[93977, 1], [93979], .contexts [
        ⟨82255, true, false, [], []⟩
      ]⟩,
    ⟨[93977], [93977], .contexts []⟩,
    ⟨[93981], [93979, 9], .source 47055⟩,
    ⟨[93979, 9], [93981], .contexts [
        ⟨82258, true, false, [], []⟩
      ]⟩,
    ⟨[93979], [93979], .contexts []⟩,
    ⟨[93983], [93981, 11], .source 47056⟩,
    ⟨[93981, 11], [93983], .contexts [
        ⟨82261, true, false, [], []⟩
      ]⟩,
    ⟨[93981], [93981], .contexts []⟩,
    ⟨[93985], [93983, 1], .source 47057⟩,
    ⟨[93983, 1], [93985], .contexts [
        ⟨82264, true, false, [], []⟩
      ]⟩,
    ⟨[93983], [93983], .contexts []⟩,
    ⟨[93987], [93985, 13], .source 47058⟩,
    ⟨[93985, 13], [93987], .contexts [
        ⟨82267, true, false, [], []⟩
      ]⟩,
    ⟨[93985], [93985], .contexts []⟩,
    ⟨[93989], [93987, 15], .source 47059⟩,
    ⟨[93987, 15], [93989], .contexts [
        ⟨82270, true, false, [], []⟩
      ]⟩,
    ⟨[93987], [93987], .contexts []⟩,
    ⟨[93991], [93989, 1], .source 47060⟩,
    ⟨[93989, 1], [93991], .contexts [
        ⟨82273, true, false, [], []⟩
      ]⟩,
    ⟨[93989], [93989], .contexts []⟩,
    ⟨[93993], [93991, 3], .source 47061⟩,
    ⟨[93991, 3], [93993], .contexts [
        ⟨82276, true, false, [], []⟩
      ]⟩,
    ⟨[93991], [93991], .contexts []⟩,
    ⟨[93995], [93993, 5], .source 47062⟩,
    ⟨[93993, 5], [93995], .contexts [
        ⟨82279, true, false, [], []⟩
      ]⟩,
    ⟨[93993], [93993], .contexts []⟩,
    ⟨[93997], [93995, 1], .source 47063⟩,
    ⟨[93995, 1], [93997], .contexts [
        ⟨82282, true, false, [], []⟩
      ]⟩,
    ⟨[93995], [93995], .contexts []⟩,
    ⟨[93999], [93997, 9], .source 47064⟩,
    ⟨[93997, 9], [93999], .contexts [
        ⟨82285, true, false, [], []⟩
      ]⟩,
    ⟨[93997], [93997], .contexts []⟩,
    ⟨[94001], [93999, 11], .source 47065⟩,
    ⟨[93999, 11], [94001], .contexts [
        ⟨82288, true, false, [], []⟩
      ]⟩,
    ⟨[93999], [93999], .contexts []⟩,
    ⟨[94003], [94001, 1], .source 47066⟩,
    ⟨[94001, 1], [94003], .contexts [
        ⟨82291, true, false, [], []⟩
      ]⟩,
    ⟨[94001], [94001], .contexts []⟩,
    ⟨[94003, 1], [94001], .contexts [
        ⟨82292, true, false, [], [1]⟩,
        ⟨8, false, false, [94001], []⟩,
        ⟨82293, false, false, [], []⟩
      ]⟩,
    ⟨[94005], [94003, 13], .source 47067⟩,
    ⟨[94003, 13], [94005], .contexts [
        ⟨82295, true, false, [], []⟩
      ]⟩,
    ⟨[94003], [94003], .contexts []⟩,
    ⟨[94005, 13], [94003], .contexts [
        ⟨82296, true, false, [], [13]⟩,
        ⟨59, false, false, [94003], []⟩,
        ⟨82297, false, false, [], []⟩
      ]⟩,
    ⟨[94007], [94005, 15], .source 47068⟩,
    ⟨[94005, 15], [94007], .contexts [
        ⟨82299, true, false, [], []⟩
      ]⟩,
    ⟨[94005], [94005], .contexts []⟩,
    ⟨[94007, 15], [94005], .contexts [
        ⟨82300, true, false, [], [15]⟩,
        ⟨1, false, false, [94005], []⟩,
        ⟨82301, false, false, [], []⟩
      ]⟩,
    ⟨[94009], [94007, 1], .source 47069⟩]

/-- Exact literal claimed equations and contextual derivations, block 1286. -/
def y322TCIndexRaw1286 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94007], [94007], .contexts []⟩,
    ⟨[94009, 1], [94007], .contexts [
        ⟨82303, false, false, [], [1]⟩,
        ⟨8, false, false, [94007], []⟩,
        ⟨82304, false, false, [], []⟩
      ]⟩,
    ⟨[94011], [94009, 3], .source 47070⟩,
    ⟨[94009], [94009], .contexts []⟩,
    ⟨[94011, 3], [94009], .contexts [
        ⟨82306, false, false, [], [3]⟩,
        ⟨20, false, false, [94009], []⟩,
        ⟨82307, false, false, [], []⟩
      ]⟩,
    ⟨[94013], [94011, 5], .source 47071⟩,
    ⟨[94011], [94011], .contexts []⟩,
    ⟨[94013, 5], [94011], .contexts [
        ⟨82309, false, false, [], [5]⟩,
        ⟨28, false, false, [94011], []⟩,
        ⟨82310, false, false, [], []⟩
      ]⟩,
    ⟨[94015], [94013, 1], .source 47072⟩,
    ⟨[94013, 1], [94015], .contexts [
        ⟨82312, true, false, [], []⟩
      ]⟩,
    ⟨[94013], [94013], .contexts []⟩,
    ⟨[94015, 1], [94013], .contexts [
        ⟨82313, true, false, [], [1]⟩,
        ⟨8, false, false, [94013], []⟩,
        ⟨82314, false, false, [], []⟩
      ]⟩,
    ⟨[94017], [94015, 9], .source 47073⟩,
    ⟨[94015, 9], [94017], .contexts [
        ⟨82316, true, false, [], []⟩
      ]⟩,
    ⟨[94015], [94015], .contexts []⟩,
    ⟨[94017, 9], [94015], .contexts [
        ⟨82317, true, false, [], [9]⟩,
        ⟨46, false, false, [94015], []⟩,
        ⟨82318, false, false, [], []⟩
      ]⟩,
    ⟨[94019], [94017, 11], .source 47074⟩,
    ⟨[94017], [94017], .contexts []⟩,
    ⟨[94019, 11], [94017], .contexts [
        ⟨82320, false, false, [], [11]⟩,
        ⟨53, false, false, [94017], []⟩,
        ⟨82321, false, false, [], []⟩
      ]⟩,
    ⟨[94021], [94019, 1], .source 47075⟩,
    ⟨[94019], [94019], .contexts []⟩,
    ⟨[94021, 1], [94019], .contexts [
        ⟨82323, false, false, [], [1]⟩,
        ⟨8, false, false, [94019], []⟩,
        ⟨82324, false, false, [], []⟩
      ]⟩,
    ⟨[94023], [94021, 13], .source 47076⟩,
    ⟨[94021], [94021], .contexts []⟩,
    ⟨[94023, 13], [94021], .contexts [
        ⟨82326, false, false, [], [13]⟩,
        ⟨59, false, false, [94021], []⟩,
        ⟨82327, false, false, [], []⟩
      ]⟩,
    ⟨[94025], [94023, 15], .source 47077⟩,
    ⟨[94023, 15], [94025], .contexts [
        ⟨82329, true, false, [], []⟩
      ]⟩,
    ⟨[94023], [94023], .contexts []⟩,
    ⟨[94025, 15], [94023], .contexts [
        ⟨82330, true, false, [], [15]⟩,
        ⟨1, false, false, [94023], []⟩,
        ⟨82331, false, false, [], []⟩
      ]⟩,
    ⟨[94027], [94025, 1], .source 47078⟩,
    ⟨[94025], [94025], .contexts []⟩,
    ⟨[94027, 1], [94025], .contexts [
        ⟨82333, false, false, [], [1]⟩,
        ⟨8, false, false, [94025], []⟩,
        ⟨82334, false, false, [], []⟩
      ]⟩,
    ⟨[94029], [94027, 3], .source 47079⟩,
    ⟨[94027, 3], [94029], .contexts [
        ⟨82336, true, false, [], []⟩
      ]⟩,
    ⟨[94027], [94027], .contexts []⟩,
    ⟨[94029, 3], [94027], .contexts [
        ⟨82337, true, false, [], [3]⟩,
        ⟨20, false, false, [94027], []⟩,
        ⟨82338, false, false, [], []⟩
      ]⟩,
    ⟨[94031], [94029, 5], .source 47080⟩,
    ⟨[94029, 5], [94031], .contexts [
        ⟨82340, true, false, [], []⟩
      ]⟩,
    ⟨[94029], [94029], .contexts []⟩,
    ⟨[94031, 5], [94029], .contexts [
        ⟨82341, true, false, [], [5]⟩,
        ⟨28, false, false, [94029], []⟩,
        ⟨82342, false, false, [], []⟩
      ]⟩,
    ⟨[94033], [94031, 1], .source 47081⟩,
    ⟨[94031, 1], [94033], .contexts [
        ⟨82344, true, false, [], []⟩
      ]⟩,
    ⟨[94031], [94031], .contexts []⟩,
    ⟨[94033, 1], [94031], .contexts [
        ⟨82345, true, false, [], [1]⟩,
        ⟨8, false, false, [94031], []⟩,
        ⟨82346, false, false, [], []⟩
      ]⟩,
    ⟨[94035], [94033, 9], .source 47082⟩,
    ⟨[94033, 9], [94035], .contexts [
        ⟨82348, true, false, [], []⟩
      ]⟩,
    ⟨[94033], [94033], .contexts []⟩,
    ⟨[94035, 9], [94033], .contexts [
        ⟨82349, true, false, [], [9]⟩,
        ⟨46, false, false, [94033], []⟩,
        ⟨82350, false, false, [], []⟩
      ]⟩,
    ⟨[94037], [94035, 11], .source 47083⟩,
    ⟨[94035, 11], [94037], .contexts [
        ⟨82352, true, false, [], []⟩
      ]⟩,
    ⟨[94035], [94035], .contexts []⟩,
    ⟨[94037, 11], [94035], .contexts [
        ⟨82353, true, false, [], [11]⟩,
        ⟨53, false, false, [94035], []⟩,
        ⟨82354, false, false, [], []⟩
      ]⟩,
    ⟨[94039], [94037, 1], .source 47084⟩,
    ⟨[94037, 1], [94039], .contexts [
        ⟨82356, true, false, [], []⟩
      ]⟩,
    ⟨[94037], [94037], .contexts []⟩,
    ⟨[94039, 1], [94037], .contexts [
        ⟨82357, true, false, [], [1]⟩,
        ⟨8, false, false, [94037], []⟩,
        ⟨82358, false, false, [], []⟩
      ]⟩,
    ⟨[94041], [94039, 13], .source 47085⟩,
    ⟨[94039, 13], [94041], .contexts [
        ⟨82360, true, false, [], []⟩
      ]⟩,
    ⟨[94039], [94039], .contexts []⟩,
    ⟨[94041, 13], [94039], .contexts [
        ⟨82361, true, false, [], [13]⟩,
        ⟨59, false, false, [94039], []⟩,
        ⟨82362, false, false, [], []⟩
      ]⟩,
    ⟨[94043], [94041, 15], .source 47086⟩,
    ⟨[94041], [94041], .contexts []⟩,
    ⟨[94043, 15], [94041], .contexts [
        ⟨82364, false, false, [], [15]⟩,
        ⟨1, false, false, [94041], []⟩,
        ⟨82365, false, false, [], []⟩
      ]⟩,
    ⟨[94045], [94043, 1], .source 47087⟩]

/-- Exact literal claimed equations and contextual derivations, block 1287. -/
def y322TCIndexRaw1287 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94043], [94043], .contexts []⟩,
    ⟨[94045, 1], [94043], .contexts [
        ⟨82367, false, false, [], [1]⟩,
        ⟨8, false, false, [94043], []⟩,
        ⟨82368, false, false, [], []⟩
      ]⟩,
    ⟨[94047], [94045, 3], .source 47088⟩,
    ⟨[94045], [94045], .contexts []⟩,
    ⟨[94047, 3], [94045], .contexts [
        ⟨82370, false, false, [], [3]⟩,
        ⟨20, false, false, [94045], []⟩,
        ⟨82371, false, false, [], []⟩
      ]⟩,
    ⟨[94049], [94047, 5], .source 47089⟩,
    ⟨[94047, 5], [94049], .contexts [
        ⟨82373, true, false, [], []⟩
      ]⟩,
    ⟨[94047], [94047], .contexts []⟩,
    ⟨[94049, 5], [94047], .contexts [
        ⟨82374, true, false, [], [5]⟩,
        ⟨28, false, false, [94047], []⟩,
        ⟨82375, false, false, [], []⟩
      ]⟩,
    ⟨[94051], [94049, 1], .source 47090⟩,
    ⟨[94049], [94049], .contexts []⟩,
    ⟨[94051, 1], [94049], .contexts [
        ⟨82377, false, false, [], [1]⟩,
        ⟨8, false, false, [94049], []⟩,
        ⟨82378, false, false, [], []⟩
      ]⟩,
    ⟨[94053], [94051, 9], .source 47091⟩,
    ⟨[94051, 9], [94053], .contexts [
        ⟨82380, true, false, [], []⟩
      ]⟩,
    ⟨[94051], [94051], .contexts []⟩,
    ⟨[94053, 9], [94051], .contexts [
        ⟨82381, true, false, [], [9]⟩,
        ⟨46, false, false, [94051], []⟩,
        ⟨82382, false, false, [], []⟩
      ]⟩,
    ⟨[94055], [94053, 11], .source 47092⟩,
    ⟨[94053], [94053], .contexts []⟩,
    ⟨[94055, 11], [94053], .contexts [
        ⟨82384, false, false, [], [11]⟩,
        ⟨53, false, false, [94053], []⟩,
        ⟨82385, false, false, [], []⟩
      ]⟩,
    ⟨[94057], [94055, 1], .source 47093⟩,
    ⟨[94055, 1], [94057], .contexts [
        ⟨82387, true, false, [], []⟩
      ]⟩,
    ⟨[94055], [94055], .contexts []⟩,
    ⟨[94057], [94057], .contexts []⟩,
    ⟨[94055, 11], [94053], .contexts [
        ⟨82386, false, false, [], []⟩,
        ⟨82385, false, false, [], []⟩,
        ⟨82385, false, false, [], []⟩
      ]⟩,
    ⟨[94051], [94051], .contexts []⟩,
    ⟨[94051, 1], [94049], .contexts [
        ⟨82379, false, false, [], []⟩
      ]⟩,
    ⟨[94049], [94049], .contexts []⟩,
    ⟨[94049, 5], [94047], .contexts [
        ⟨82376, false, false, [], []⟩
      ]⟩,
    ⟨[94047], [94047], .contexts []⟩,
    ⟨[94047, 3], [94045], .contexts [
        ⟨82372, false, false, [], []⟩
      ]⟩,
    ⟨[94045], [94045], .contexts []⟩,
    ⟨[94045, 1], [94043], .contexts [
        ⟨82369, false, false, [], []⟩
      ]⟩,
    ⟨[94043], [94043], .contexts []⟩,
    ⟨[94055, 11, 9, 1, 5, 3, 1], [94043], .contexts [
        ⟨82391, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨82383, false, false, [], [1, 5, 3, 1]⟩,
        ⟨82392, false, false, [], [1, 5, 3, 1]⟩,
        ⟨82382, false, false, [], [1, 5, 3, 1]⟩,
        ⟨82382, false, false, [], [1, 5, 3, 1]⟩,
        ⟨82393, false, false, [], [5, 3, 1]⟩,
        ⟨82394, false, false, [], [5, 3, 1]⟩,
        ⟨82378, false, false, [], [5, 3, 1]⟩,
        ⟨82378, false, false, [], [5, 3, 1]⟩,
        ⟨82395, false, false, [], [3, 1]⟩,
        ⟨82396, false, false, [], [3, 1]⟩,
        ⟨82375, false, false, [], [3, 1]⟩,
        ⟨82375, false, false, [], [3, 1]⟩,
        ⟨82397, false, false, [], [1]⟩,
        ⟨82398, false, false, [], [1]⟩,
        ⟨82371, false, false, [], [1]⟩,
        ⟨82371, false, false, [], [1]⟩,
        ⟨82399, false, false, [], []⟩,
        ⟨82400, false, false, [], []⟩,
        ⟨82368, false, false, [], []⟩,
        ⟨82368, false, false, [], []⟩
      ]⟩,
    ⟨[94043, 15], [94041], .contexts [
        ⟨82366, false, false, [], []⟩
      ]⟩,
    ⟨[94041], [94041], .contexts []⟩,
    ⟨[94041, 13], [94039], .contexts [
        ⟨82363, false, false, [], []⟩
      ]⟩,
    ⟨[94039], [94039], .contexts []⟩,
    ⟨[94039, 1], [94037], .contexts [
        ⟨82359, false, false, [], []⟩
      ]⟩,
    ⟨[94037], [94037], .contexts []⟩,
    ⟨[94037, 11], [94035], .contexts [
        ⟨82355, false, false, [], []⟩
      ]⟩,
    ⟨[94035], [94035], .contexts []⟩,
    ⟨[94035, 9], [94033], .contexts [
        ⟨82351, false, false, [], []⟩
      ]⟩,
    ⟨[94033], [94033], .contexts []⟩,
    ⟨[94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9], [94033], .contexts [
        ⟨82401, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨82402, false, false, [], [13, 1, 11, 9]⟩,
        ⟨82403, false, false, [], [13, 1, 11, 9]⟩,
        ⟨82365, false, false, [], [13, 1, 11, 9]⟩,
        ⟨82365, false, false, [], [13, 1, 11, 9]⟩,
        ⟨82404, false, false, [], [1, 11, 9]⟩,
        ⟨82405, false, false, [], [1, 11, 9]⟩,
        ⟨82362, false, false, [], [1, 11, 9]⟩,
        ⟨82362, false, false, [], [1, 11, 9]⟩,
        ⟨82406, false, false, [], [11, 9]⟩,
        ⟨82407, false, false, [], [11, 9]⟩,
        ⟨82358, false, false, [], [11, 9]⟩,
        ⟨82358, false, false, [], [11, 9]⟩,
        ⟨82408, false, false, [], [9]⟩,
        ⟨82409, false, false, [], [9]⟩,
        ⟨82354, false, false, [], [9]⟩,
        ⟨82354, false, false, [], [9]⟩,
        ⟨82410, false, false, [], []⟩,
        ⟨82411, false, false, [], []⟩,
        ⟨82350, false, false, [], []⟩,
        ⟨82350, false, false, [], []⟩
      ]⟩,
    ⟨[94033, 1], [94031], .contexts [
        ⟨82347, false, false, [], []⟩
      ]⟩,
    ⟨[94031], [94031], .contexts []⟩,
    ⟨[94031, 5], [94029], .contexts [
        ⟨82343, false, false, [], []⟩
      ]⟩,
    ⟨[94029], [94029], .contexts []⟩,
    ⟨[94029, 3], [94027], .contexts [
        ⟨82339, false, false, [], []⟩
      ]⟩,
    ⟨[94027], [94027], .contexts []⟩,
    ⟨[94025], [94025], .contexts []⟩,
    ⟨[
      94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15
    ], [94023], .contexts [
        ⟨82412, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨82413, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82414, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82346, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82346, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82415, false, false, [], [3, 1, 15]⟩,
        ⟨82416, false, false, [], [3, 1, 15]⟩,
        ⟨82342, false, false, [], [3, 1, 15]⟩,
        ⟨82342, false, false, [], [3, 1, 15]⟩,
        ⟨82417, false, false, [], [1, 15]⟩,
        ⟨82418, false, false, [], [1, 15]⟩,
        ⟨82338, false, false, [], [1, 15]⟩,
        ⟨82338, false, false, [], [1, 15]⟩,
        ⟨82335, false, false, [], [15]⟩,
        ⟨82419, false, false, [], [15]⟩,
        ⟨82334, false, false, [], [15]⟩,
        ⟨82334, false, false, [], [15]⟩,
        ⟨82332, false, false, [], []⟩,
        ⟨82331, false, false, [], []⟩,
        ⟨82331, false, false, [], []⟩
      ]⟩,
    ⟨[94021], [94021], .contexts []⟩,
    ⟨[94021, 1], [94019], .contexts [
        ⟨82325, false, false, [], []⟩
      ]⟩,
    ⟨[94019], [94019], .contexts []⟩,
    ⟨[94015], [94015], .contexts []⟩,
    ⟨[
      94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [94013], .contexts [
        ⟨82420, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨82328, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82421, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82327, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82327, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82422, false, false, [], [11, 9, 1]⟩,
        ⟨82423, false, false, [], [11, 9, 1]⟩,
        ⟨82324, false, false, [], [11, 9, 1]⟩,
        ⟨82324, false, false, [], [11, 9, 1]⟩,
        ⟨82322, false, false, [], [9, 1]⟩,
        ⟨82321, false, false, [], [9, 1]⟩,
        ⟨82321, false, false, [], [9, 1]⟩,
        ⟨82319, false, false, [], [1]⟩,
        ⟨82424, false, false, [], [1]⟩,
        ⟨82318, false, false, [], [1]⟩,
        ⟨82318, false, false, [], [1]⟩,
        ⟨82315, false, false, [], []⟩,
        ⟨82314, false, false, [], []⟩,
        ⟨82314, false, false, [], []⟩
      ]⟩,
    ⟨[94011], [94011], .contexts []⟩,
    ⟨[94009], [94009], .contexts []⟩,
    ⟨[94007], [94007], .contexts []⟩,
    ⟨[94005], [94005], .contexts []⟩,
    ⟨[94003], [94003], .contexts []⟩,
    ⟨[
      94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13
    ], [94003], .contexts [
        ⟨82425, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨82311, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82426, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82310, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82310, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82308, false, false, [], [1, 15, 13]⟩,
        ⟨82427, false, false, [], [1, 15, 13]⟩,
        ⟨82307, false, false, [], [1, 15, 13]⟩,
        ⟨82307, false, false, [], [1, 15, 13]⟩,
        ⟨82305, false, false, [], [15, 13]⟩,
        ⟨82428, false, false, [], [15, 13]⟩,
        ⟨82304, false, false, [], [15, 13]⟩,
        ⟨82304, false, false, [], [15, 13]⟩,
        ⟨82302, false, false, [], [13]⟩,
        ⟨82429, false, false, [], [13]⟩,
        ⟨82301, false, false, [], [13]⟩,
        ⟨82301, false, false, [], [13]⟩,
        ⟨82298, false, false, [], []⟩,
        ⟨82430, false, false, [], []⟩,
        ⟨82297, false, false, [], []⟩,
        ⟨82297, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1288. -/
def y322TCIndexRaw1288 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94001], [94001], .contexts []⟩,
    ⟨[93999], [93999], .contexts []⟩,
    ⟨[93997], [93997], .contexts []⟩,
    ⟨[93995], [93995], .contexts []⟩,
    ⟨[93993], [93993], .contexts []⟩,
    ⟨[
      94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5
    ], [93993], .contexts [
        ⟨82431, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨82294, false, false, [], [11, 9, 1, 5]⟩,
        ⟨82432, false, false, [], [11, 9, 1, 5]⟩,
        ⟨82293, false, false, [], [11, 9, 1, 5]⟩,
        ⟨82293, false, false, [], [11, 9, 1, 5]⟩,
        ⟨82289, true, false, [], [11, 9, 1, 5]⟩,
        ⟨53, false, false, [93999], [9, 1, 5]⟩,
        ⟨82290, false, false, [], [9, 1, 5]⟩,
        ⟨82433, false, false, [], [9, 1, 5]⟩,
        ⟨82290, false, false, [], [9, 1, 5]⟩,
        ⟨82290, false, false, [], [9, 1, 5]⟩,
        ⟨82286, true, false, [], [9, 1, 5]⟩,
        ⟨46, false, false, [93997], [1, 5]⟩,
        ⟨82287, false, false, [], [1, 5]⟩,
        ⟨82434, false, false, [], [1, 5]⟩,
        ⟨82287, false, false, [], [1, 5]⟩,
        ⟨82287, false, false, [], [1, 5]⟩,
        ⟨82283, true, false, [], [1, 5]⟩,
        ⟨8, false, false, [93995], [5]⟩,
        ⟨82284, false, false, [], [5]⟩,
        ⟨82435, false, false, [], [5]⟩,
        ⟨82284, false, false, [], [5]⟩,
        ⟨82284, false, false, [], [5]⟩,
        ⟨82280, true, false, [], [5]⟩,
        ⟨28, false, false, [93993], []⟩,
        ⟨82281, false, false, [], []⟩,
        ⟨82436, false, false, [], []⟩,
        ⟨82281, false, false, [], []⟩,
        ⟨82281, false, false, [], []⟩
      ]⟩,
    ⟨[93991], [93991], .contexts []⟩,
    ⟨[93989], [93989], .contexts []⟩,
    ⟨[93987], [93987], .contexts []⟩,
    ⟨[93985], [93985], .contexts []⟩,
    ⟨[
      94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [93985], .contexts [
        ⟨82437, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82277, true, false, [], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [93991], [1, 15, 13]⟩,
        ⟨82278, false, false, [], [1, 15, 13]⟩,
        ⟨82438, false, false, [], [1, 15, 13]⟩,
        ⟨82278, false, false, [], [1, 15, 13]⟩,
        ⟨82278, false, false, [], [1, 15, 13]⟩,
        ⟨82274, true, false, [], [1, 15, 13]⟩,
        ⟨8, false, false, [93989], [15, 13]⟩,
        ⟨82275, false, false, [], [15, 13]⟩,
        ⟨82439, false, false, [], [15, 13]⟩,
        ⟨82275, false, false, [], [15, 13]⟩,
        ⟨82275, false, false, [], [15, 13]⟩,
        ⟨82271, true, false, [], [15, 13]⟩,
        ⟨1, false, false, [93987], [13]⟩,
        ⟨82272, false, false, [], [13]⟩,
        ⟨82440, false, false, [], [13]⟩,
        ⟨82272, false, false, [], [13]⟩,
        ⟨82272, false, false, [], [13]⟩,
        ⟨82268, true, false, [], [13]⟩,
        ⟨59, false, false, [93985], []⟩,
        ⟨82269, false, false, [], []⟩,
        ⟨82441, false, false, [], []⟩,
        ⟨82269, false, false, [], []⟩,
        ⟨82269, false, false, [], []⟩
      ]⟩,
    ⟨[93983], [93983], .contexts []⟩,
    ⟨[93981], [93981], .contexts []⟩,
    ⟨[93979], [93979], .contexts []⟩,
    ⟨[93977], [93977], .contexts []⟩,
    ⟨[
      94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1
    ], [93977], .contexts [
        ⟨82442, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82265, true, false, [], [1, 11, 9, 1]⟩,
        ⟨8, false, false, [93983], [11, 9, 1]⟩,
        ⟨82266, false, false, [], [11, 9, 1]⟩,
        ⟨82443, false, false, [], [11, 9, 1]⟩,
        ⟨82266, false, false, [], [11, 9, 1]⟩,
        ⟨82266, false, false, [], [11, 9, 1]⟩,
        ⟨82262, true, false, [], [11, 9, 1]⟩,
        ⟨53, false, false, [93981], [9, 1]⟩,
        ⟨82263, false, false, [], [9, 1]⟩,
        ⟨82444, false, false, [], [9, 1]⟩,
        ⟨82263, false, false, [], [9, 1]⟩,
        ⟨82263, false, false, [], [9, 1]⟩,
        ⟨82259, true, false, [], [9, 1]⟩,
        ⟨46, false, false, [93979], [1]⟩,
        ⟨82260, false, false, [], [1]⟩,
        ⟨82445, false, false, [], [1]⟩,
        ⟨82260, false, false, [], [1]⟩,
        ⟨82260, false, false, [], [1]⟩,
        ⟨82256, true, false, [], [1]⟩,
        ⟨8, false, false, [93977], []⟩,
        ⟨82257, false, false, [], []⟩,
        ⟨82446, false, false, [], []⟩,
        ⟨82257, false, false, [], []⟩,
        ⟨82257, false, false, [], []⟩
      ]⟩,
    ⟨[93975], [93975], .contexts []⟩,
    ⟨[93973], [93973], .contexts []⟩,
    ⟨[93971], [93971], .contexts []⟩,
    ⟨[93969], [93969], .contexts []⟩,
    ⟨[93967], [93967], .contexts []⟩,
    ⟨[
      94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [93967], .contexts [
        ⟨82447, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨82254, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82448, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82253, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82253, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82249, true, false, [], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [93973], [1, 15, 13]⟩,
        ⟨82250, false, false, [], [1, 15, 13]⟩,
        ⟨82449, false, false, [], [1, 15, 13]⟩,
        ⟨82250, false, false, [], [1, 15, 13]⟩,
        ⟨82250, false, false, [], [1, 15, 13]⟩,
        ⟨82246, true, false, [], [1, 15, 13]⟩,
        ⟨8, false, false, [93971], [15, 13]⟩,
        ⟨82247, false, false, [], [15, 13]⟩,
        ⟨82450, false, false, [], [15, 13]⟩,
        ⟨82247, false, false, [], [15, 13]⟩,
        ⟨82247, false, false, [], [15, 13]⟩,
        ⟨82243, true, false, [], [15, 13]⟩,
        ⟨1, false, false, [93969], [13]⟩,
        ⟨82244, false, false, [], [13]⟩,
        ⟨82451, false, false, [], [13]⟩,
        ⟨82244, false, false, [], [13]⟩,
        ⟨82244, false, false, [], [13]⟩,
        ⟨82240, true, false, [], [13]⟩,
        ⟨59, false, false, [93967], []⟩,
        ⟨82241, false, false, [], []⟩,
        ⟨82452, false, false, [], []⟩,
        ⟨82241, false, false, [], []⟩,
        ⟨82241, false, false, [], []⟩
      ]⟩,
    ⟨[93965], [93965], .contexts []⟩,
    ⟨[93963], [93963], .contexts []⟩,
    ⟨[93961], [93961], .contexts []⟩,
    ⟨[93959], [93959], .contexts []⟩,
    ⟨[93957], [93957], .contexts []⟩,
    ⟨[
      94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5
    ], [93957], .contexts [
        ⟨82453, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨82238, false, false, [], [11, 9, 1, 5]⟩,
        ⟨82454, false, false, [], [11, 9, 1, 5]⟩,
        ⟨82237, false, false, [], [11, 9, 1, 5]⟩,
        ⟨82237, false, false, [], [11, 9, 1, 5]⟩,
        ⟨82234, false, false, [], [9, 1, 5]⟩,
        ⟨82455, false, false, [], [9, 1, 5]⟩,
        ⟨82233, false, false, [], [9, 1, 5]⟩,
        ⟨82233, false, false, [], [9, 1, 5]⟩,
        ⟨82229, true, false, [], [9, 1, 5]⟩,
        ⟨46, false, false, [93961], [1, 5]⟩,
        ⟨82230, false, false, [], [1, 5]⟩,
        ⟨82456, false, false, [], [1, 5]⟩,
        ⟨82230, false, false, [], [1, 5]⟩,
        ⟨82230, false, false, [], [1, 5]⟩,
        ⟨82226, true, false, [], [1, 5]⟩,
        ⟨8, false, false, [93959], [5]⟩,
        ⟨82227, false, false, [], [5]⟩,
        ⟨82457, false, false, [], [5]⟩,
        ⟨82227, false, false, [], [5]⟩,
        ⟨82227, false, false, [], [5]⟩,
        ⟨82223, true, false, [], [5]⟩,
        ⟨28, false, false, [93957], []⟩,
        ⟨82224, false, false, [], []⟩,
        ⟨82458, false, false, [], []⟩,
        ⟨82224, false, false, [], []⟩,
        ⟨82224, false, false, [], []⟩
      ]⟩,
    ⟨[93955], [93955], .contexts []⟩,
    ⟨[93953], [93953], .contexts []⟩,
    ⟨[93953, 15], [93951], .contexts [
        ⟨82214, false, false, [], []⟩
      ]⟩,
    ⟨[93951], [93951], .contexts []⟩,
    ⟨[93949], [93949], .contexts []⟩,
    ⟨[
      94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13
    ], [93949], .contexts [
        ⟨82459, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82220, true, false, [], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [93955], [1, 15, 13]⟩,
        ⟨82221, false, false, [], [1, 15, 13]⟩,
        ⟨82460, false, false, [], [1, 15, 13]⟩,
        ⟨82221, false, false, [], [1, 15, 13]⟩,
        ⟨82221, false, false, [], [1, 15, 13]⟩,
        ⟨82218, false, false, [], [15, 13]⟩,
        ⟨82461, false, false, [], [15, 13]⟩,
        ⟨82217, false, false, [], [15, 13]⟩,
        ⟨82217, false, false, [], [15, 13]⟩,
        ⟨82462, false, false, [], [13]⟩,
        ⟨82463, false, false, [], [13]⟩,
        ⟨82213, false, false, [], [13]⟩,
        ⟨82213, false, false, [], [13]⟩,
        ⟨82209, true, false, [], [13]⟩,
        ⟨59, false, false, [93949], []⟩,
        ⟨82210, false, false, [], []⟩,
        ⟨82464, false, false, [], []⟩,
        ⟨82210, false, false, [], []⟩,
        ⟨82210, false, false, [], []⟩
      ]⟩,
    ⟨[93947], [93947], .contexts []⟩,
    ⟨[
      94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [14153, 93943], .contexts [
        ⟨82465, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82206, true, false, [], [1, 11, 9, 1]⟩,
        ⟨8, false, false, [93947], [11, 9, 1]⟩,
        ⟨82207, false, false, [], [11, 9, 1]⟩,
        ⟨82466, false, false, [], [11, 9, 1]⟩,
        ⟨82207, false, false, [], [11, 9, 1]⟩,
        ⟨82207, false, false, [], [11, 9, 1]⟩,
        ⟨82203, true, false, [], [11, 9, 1]⟩,
        ⟨53, false, false, [93945], [9, 1]⟩,
        ⟨82204, false, false, [], [9, 1]⟩,
        ⟨82204, false, false, [], [9, 1]⟩,
        ⟨82204, false, false, [], [9, 1]⟩,
        ⟨82201, false, false, [], [1]⟩,
        ⟨82192, false, false, [], [1]⟩,
        ⟨82193, false, false, [], [1]⟩,
        ⟨82193, false, false, [], [1]⟩,
        ⟨82198, false, false, [], []⟩,
        ⟨82194, false, false, [], []⟩,
        ⟨82195, false, false, [], []⟩,
        ⟨82195, false, false, [], []⟩
      ]⟩,
    ⟨[
      94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13
    ], [14153, 93933], .contexts [
        ⟨82467, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨82191, false, false, [14153], [3, 1, 15, 13]⟩,
        ⟨82184, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82185, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82186, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82176, false, false, [14153], [1, 15, 13]⟩,
        ⟨82181, false, false, [], [1, 15, 13]⟩,
        ⟨82182, false, false, [], [1, 15, 13]⟩,
        ⟨82183, false, false, [], [1, 15, 13]⟩,
        ⟨82171, false, false, [14153], [15, 13]⟩,
        ⟨82159, false, false, [], [15, 13]⟩,
        ⟨82160, false, false, [], [15, 13]⟩,
        ⟨82161, false, false, [], [15, 13]⟩,
        ⟨82155, true, false, [14153], [15, 13]⟩,
        ⟨1, false, false, [14153, 93935], [13]⟩,
        ⟨82141, false, false, [14153], [13]⟩,
        ⟨82143, false, false, [], [13]⟩,
        ⟨82144, false, false, [], [13]⟩,
        ⟨82145, false, false, [], [13]⟩,
        ⟨82140, false, false, [14153], []⟩,
        ⟨82125, false, false, [], []⟩,
        ⟨82126, false, false, [], []⟩,
        ⟨82127, false, false, [], []⟩
      ]⟩,
    ⟨[30855], [14153, 4217], .source 15492⟩,
    ⟨[
      94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5
    ], [30855, 93925], .contexts [
        ⟨82468, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨82123, false, false, [14153], [11, 9, 1, 5]⟩,
        ⟨82469, true, false, [], [93933, 11, 9, 1, 5]⟩,
        ⟨82117, false, false, [30855], [9, 1, 5]⟩,
        ⟨82093, false, false, [30855], [1, 5]⟩,
        ⟨82067, false, false, [30855], [5]⟩,
        ⟨82047, true, false, [30855], [5]⟩,
        ⟨28, false, false, [30855, 93925], []⟩,
        ⟨82027, false, false, [30855], []⟩
      ]⟩,
    ⟨[30857], [30855, 15163], .source 15493⟩,
    ⟨[30859], [30857, 15159], .source 15494⟩,
    ⟨[30861], [30859, 15099], .source 15495⟩,
    ⟨[
      94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1
    ], [30861, 82849], .contexts [
        ⟨82470, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨82026, false, false, [30855], [1, 15, 13, 1]⟩,
        ⟨9016, false, false, [30855], [15, 13, 1]⟩,
        ⟨14881, false, false, [30855], [13, 1]⟩,
        ⟨82471, true, false, [], [80793, 13, 1]⟩,
        ⟨17470, false, false, [30857], [1]⟩,
        ⟨82472, true, false, [], [82849, 1]⟩,
        ⟨17455, false, false, [30859], []⟩,
        ⟨82473, true, false, [], [82849]⟩
      ]⟩,
    ⟨[30863], [30861, 16853], .source 15496⟩,
    ⟨[30865], [30863, 15099], .source 15497⟩,
    ⟨[30867], [30865, 18101], .source 15498⟩,
    ⟨[30869], [30867, 2375], .source 15499⟩,
    ⟨[
      94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3
    ], [30869, 80431], .contexts [
        ⟨82474, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨31362, false, false, [30861], [9, 1, 5, 3]⟩,
        ⟨31360, false, false, [30861], [1, 5, 3]⟩,
        ⟨82475, true, false, [], [85325, 1, 5, 3]⟩,
        ⟨31349, false, false, [30863], [5, 3]⟩,
        ⟨82476, true, false, [], [85325, 5, 3]⟩,
        ⟨31356, false, false, [30865], [3]⟩,
        ⟨82477, true, false, [], [80431, 3]⟩,
        ⟨7898, false, false, [30867], []⟩,
        ⟨82478, true, false, [], [80431]⟩
      ]⟩,
    ⟨[30871], [30869, 2019], .source 15500⟩,
    ⟨[30873], [30871, 15423], .source 15501⟩,
    ⟨[30875], [30873, 275], .source 15502⟩,
    ⟨[30877], [30875, 15221], .source 15503⟩,
    ⟨[30879], [30877, 15247], .source 15504⟩,
    ⟨[
      94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [30879, 82671], .contexts [
        ⟨82479, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨7896, false, false, [30869], [15, 13, 1, 11]⟩,
        ⟨82480, true, false, [], [80431, 15, 13, 1, 11]⟩,
        ⟨16459, false, false, [30871], [13, 1, 11]⟩,
        ⟨82481, true, false, [], [82773, 13, 1, 11]⟩,
        ⟨16463, false, false, [30873], [1, 11]⟩,
        ⟨82482, true, false, [], [82649, 1, 11]⟩,
        ⟨15043, false, false, [30875], [11]⟩,
        ⟨82483, true, false, [], [82659, 11]⟩,
        ⟨15209, false, false, [30877], []⟩,
        ⟨82484, true, false, [], [82671]⟩
      ]⟩,
    ⟨[30881], [30879, 15211], .source 15505⟩,
    ⟨[
      94055, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1
    ], [30881, 87035], .contexts [
        ⟨82485, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨15178, false, false, [30879], [1, 5, 3, 1]⟩,
        ⟨15006, false, false, [30879], [5, 3, 1]⟩,
        ⟨82486, true, false, [], [78843, 5, 3, 1]⟩,
        ⟨15289, false, false, [30881], [3, 1]⟩,
        ⟨39031, false, false, [30881], [1]⟩,
        ⟨40036, false, false, [30881], []⟩
      ]⟩,
    ⟨[30881, 82879], [30881, 82879], .contexts []⟩,
    ⟨[30881, 82879], [30881, 82879], .contexts []⟩,
    ⟨[94057, 13], [94057, 13], .contexts []⟩,
    ⟨[94057, 13], [30881, 82879], .contexts [
        ⟨82490, false, false, [], []⟩,
        ⟨82390, true, false, [], [13]⟩,
        ⟨82390, true, false, [], [13]⟩,
        ⟨82388, true, false, [], [13]⟩,
        ⟨5361, false, false, [94055], []⟩,
        ⟨5362, false, false, [94055], []⟩,
        ⟨82487, false, false, [], [15]⟩,
        ⟨40045, false, false, [30881], []⟩,
        ⟨82488, false, false, [], []⟩,
        ⟨82489, false, false, [], []⟩,
        ⟨21093, false, false, [30881], []⟩,
        ⟨13, true, false, [], [30881, 82879]⟩
      ]⟩,
    ⟨[30883], [30880], .source 15506⟩,
    ⟨[82879, 13], [30883, 94057], .contexts [
        ⟨82491, true, false, [30880], [13]⟩,
        ⟨59, false, false, [30880, 94057], []⟩,
        ⟨82492, true, false, [], [94057]⟩
      ]⟩,
    ⟨[30885], [30881, 1075], .source 15507⟩,
    ⟨[30885, 82879], [30885, 82879], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1289. -/
def y322TCIndexRaw1289 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[30885, 82879], [30885, 82879], .contexts []⟩,
    ⟨[94055, 13], [94055, 13], .contexts []⟩,
    ⟨[94055, 13], [30885, 82879], .contexts [
        ⟨82497, false, false, [], []⟩,
        ⟨82389, true, false, [], [13]⟩,
        ⟨82389, true, false, [], [13]⟩,
        ⟨82389, true, false, [], [13]⟩,
        ⟨8, true, false, [94055], [13]⟩,
        ⟨82388, false, false, [], [1, 13]⟩,
        ⟨115, false, false, [94057], []⟩,
        ⟨118, false, false, [94057], []⟩,
        ⟨82490, false, false, [], [1, 13, 1]⟩,
        ⟨82491, false, false, [], [1, 13, 1]⟩,
        ⟨82488, false, false, [], [1, 13, 1]⟩,
        ⟨82489, false, false, [], [1, 13, 1]⟩,
        ⟨82489, false, false, [], [1, 13, 1]⟩,
        ⟨17805, false, false, [30881], [13, 1]⟩,
        ⟨17802, false, false, [30881], [1]⟩,
        ⟨82494, true, false, [], [82877, 1]⟩,
        ⟨17804, false, false, [30885], []⟩,
        ⟨82495, false, false, [], []⟩,
        ⟨82496, false, false, [], []⟩,
        ⟨21093, false, false, [30885], []⟩
      ]⟩,
    ⟨[94055, 13], [30885, 82879], .contexts [
        ⟨82498, false, false, [], []⟩,
        ⟨13, true, false, [], [30885, 82879]⟩
      ]⟩,
    ⟨[30887], [30884], .source 15508⟩,
    ⟨[30883, 94057], [30883, 94057], .contexts []⟩,
    ⟨[30889], [30881, 30887], .source 15509⟩,
    ⟨[94055, 13], [30885, 82879], .contexts [
        ⟨82497, false, false, [], []⟩,
        ⟨82499, false, false, [], []⟩,
        ⟨82495, false, false, [], []⟩,
        ⟨82496, false, false, [], []⟩,
        ⟨82496, false, false, [], []⟩
      ]⟩,
    ⟨[30891], [30885, 16221], .source 15510⟩,
    ⟨[30893], [30891, 26695], .source 15511⟩,
    ⟨[94055], [94055], .contexts []⟩,
    ⟨[94055], [94055], .contexts []⟩,
    ⟨[30895], [30892], .source 15512⟩,
    ⟨[30892], [30892], .contexts []⟩,
    ⟨[91935, 3], [30895, 94055], .contexts [
        ⟨82505, false, false, [30892], [91935, 3]⟩,
        ⟨68218, true, false, [30892, 30891], [3]⟩,
        ⟨82504, false, false, [30892], [83377, 13, 3]⟩,
        ⟨21095, true, false, [30892, 30885], [13, 3]⟩,
        ⟨82503, true, false, [30892], [3, 13, 3]⟩,
        ⟨4550, false, false, [30892, 94055], []⟩,
        ⟨82506, false, false, [30892], []⟩,
        ⟨82507, false, false, [30892], []⟩,
        ⟨82509, true, false, [], [94055]⟩,
        ⟨82509, true, false, [], [94055]⟩,
        ⟨82508, true, false, [], [94055]⟩
      ]⟩,
    ⟨[30897], [30885, 21099], .source 15513⟩,
    ⟨[30899], [30896], .source 15514⟩,
    ⟨[30896], [30896], .contexts []⟩,
    ⟨[83775, 5], [30899, 94055], .contexts [
        ⟨82511, false, false, [30896], [83775, 5]⟩,
        ⟨44210, true, false, [30896, 30885], [5]⟩,
        ⟨44191, true, false, [30896, 30885], [13, 5]⟩,
        ⟨82503, true, false, [30896], [5, 13, 5]⟩,
        ⟨1116, false, false, [30896, 94055], []⟩,
        ⟨82506, false, false, [30896], []⟩,
        ⟨82507, false, false, [30896], []⟩,
        ⟨82513, true, false, [], [94055]⟩,
        ⟨82513, true, false, [], [94055]⟩,
        ⟨82512, true, false, [], [94055]⟩
      ]⟩,
    ⟨[94055, 5], [30897, 83775], .contexts [
        ⟨82514, true, false, [30898], [5]⟩,
        ⟨28, false, false, [30898, 83775], []⟩,
        ⟨82512, false, true, [], [83775]⟩
      ]⟩,
    ⟨[30901], [30885, 22199], .source 15515⟩,
    ⟨[30903], [30901, 22431], .source 15516⟩,
    ⟨[30905], [30902], .source 15517⟩,
    ⟨[30902], [30902], .contexts []⟩,
    ⟨[88021, 7], [30905, 94055], .contexts [
        ⟨82517, false, false, [30902], [88021, 7]⟩,
        ⟨48929, true, false, [30902, 30901], [7]⟩,
        ⟨47733, true, false, [30902, 30901], [7]⟩,
        ⟨82516, false, false, [30902], [88025, 13, 7]⟩,
        ⟨48147, true, false, [30902, 30885], [13, 7]⟩,
        ⟨82503, true, false, [30902], [7, 13, 7]⟩,
        ⟨21371, false, false, [30902, 94055], []⟩,
        ⟨82506, false, false, [30902], []⟩,
        ⟨82507, false, false, [30902], []⟩,
        ⟨82519, true, false, [], [94055]⟩,
        ⟨82519, true, false, [], [94055]⟩,
        ⟨82518, true, false, [], [94055]⟩
      ]⟩,
    ⟨[30907], [30885, 20639], .source 15518⟩,
    ⟨[30909], [30907, 27059], .source 15519⟩,
    ⟨[30911], [30908], .source 15520⟩,
    ⟨[30911], [30908], .contexts [
        ⟨82523, false, false, [], []⟩
      ]⟩,
    ⟨[30908], [30908], .contexts []⟩,
    ⟨[85871, 11], [30911, 94055], .contexts [
        ⟨82522, false, false, [30908], [85871, 11]⟩,
        ⟨69229, true, false, [30908, 30907], [11]⟩,
        ⟨82521, false, false, [30908], [85251, 13, 11]⟩,
        ⟨42643, true, false, [30908, 30885], [13, 11]⟩,
        ⟨36054, true, false, [30908, 30885], [13, 11]⟩,
        ⟨82503, true, false, [30908], [11, 13, 11]⟩,
        ⟨4838, false, false, [30908, 94055], []⟩,
        ⟨82506, false, false, [30908], []⟩,
        ⟨82507, false, false, [30908], []⟩,
        ⟨82525, true, false, [], [94055]⟩,
        ⟨82525, true, false, [], [94055]⟩,
        ⟨82524, true, false, [], [94055]⟩
      ]⟩,
    ⟨[94053], [30909, 85871], .contexts [
        ⟨82391, true, false, [], []⟩,
        ⟨82526, true, false, [30910], [11]⟩,
        ⟨53, false, false, [30910, 85871], []⟩,
        ⟨82523, false, true, [], [85871]⟩
      ]⟩,
    ⟨[85871, 9], [30911, 94051], .contexts [
        ⟨82527, true, false, [30908], [9]⟩,
        ⟨82383, false, false, [30908], []⟩,
        ⟨82392, false, false, [30908], []⟩,
        ⟨82525, true, false, [], [94051]⟩,
        ⟨82525, true, false, [], [94051]⟩,
        ⟨82524, true, false, [], [94051]⟩
      ]⟩,
    ⟨[85873], [21979, 85871], .contexts [
        ⟨47289, false, false, [], []⟩
      ]⟩,
    ⟨[21979, 85871], [21979, 85871], .contexts []⟩,
    ⟨[85873], [21979, 85871], .contexts [
        ⟨82529, false, false, [], []⟩,
        ⟨82530, false, false, [], []⟩
      ]⟩,
    ⟨[30913], [21979, 30911], .source 15521⟩,
    ⟨[30911, 94051], [30911, 94051], .contexts []⟩,
    ⟨[85871, 9], [30911, 94051], .contexts [
        ⟨82528, false, false, [], []⟩,
        ⟨82533, false, false, [], []⟩,
        ⟨82533, false, false, [], []⟩
      ]⟩,
    ⟨[94049, 9], [94049, 9], .contexts []⟩,
    ⟨[94049], [94049], .contexts []⟩,
    ⟨[30915], [30912], .source 15522⟩,
    ⟨[30917], [30915, 30911], .source 15523⟩,
    ⟨[94049, 9], [30917, 94049], .contexts [
        ⟨82535, false, false, [], []⟩,
        ⟨82379, true, false, [], [9]⟩,
        ⟨82532, false, false, [30912], [94051, 1, 9]⟩,
        ⟨82528, true, false, [30912, 21979], [1, 9]⟩,
        ⟨82530, true, false, [30912], [9, 1, 9]⟩,
        ⟨82530, true, false, [30912], [9, 1, 9]⟩,
        ⟨82531, true, false, [30912], [9, 1, 9]⟩,
        ⟨34108, true, false, [30912], [9, 1, 9]⟩,
        ⟨582, false, false, [30912, 85871], []⟩,
        ⟨453, false, false, [30912, 85871], []⟩,
        ⟨82534, false, false, [30912], [1]⟩,
        ⟨82379, false, false, [30912, 30911], []⟩,
        ⟨82536, false, false, [30912, 30911], []⟩,
        ⟨82537, true, false, [], [30911, 94049]⟩,
        ⟨82538, true, false, [], [94049]⟩
      ]⟩,
    ⟨[30919], [21977, 29221], .source 15524⟩,
    ⟨[85871, 8], [85871, 9], .contexts [
        ⟨47, false, false, [85871], []⟩
      ]⟩,
    ⟨[92951, 3], [92951, 3], .contexts []⟩,
    ⟨[94051], [94051], .contexts []⟩,
    ⟨[30921], [30918], .source 15525⟩,
    ⟨[30923], [30921, 30911], .source 15526⟩,
    ⟨[92951, 3], [30923, 94051], .contexts [
        ⟨82542, false, false, [], []⟩,
        ⟨82540, false, false, [30918], [92951, 3]⟩,
        ⟨76135, true, false, [30918, 21977], [3]⟩,
        ⟨69240, true, false, [30918], [9, 3]⟩,
        ⟨573, false, false, [30918, 85871], []⟩,
        ⟨82541, false, false, [30918], []⟩,
        ⟨82534, false, false, [30918], []⟩,
        ⟨82543, false, false, [30918, 30911], []⟩,
        ⟨82544, true, false, [], [30911, 94051]⟩,
        ⟨82545, true, false, [], [94051]⟩
      ]⟩,
    ⟨[30925], [30922], .source 15527⟩,
    ⟨[30927], [27061, 20637], .source 15528⟩,
    ⟨[86231, 13], [86231, 13], .contexts []⟩,
    ⟨[30929], [30926], .source 15529⟩,
    ⟨[30931], [30929, 30911], .source 15530⟩,
    ⟨[86231, 13], [30931, 94051], .contexts [
        ⟨82549, false, false, [], []⟩,
        ⟨82548, false, false, [30926], [86231, 13]⟩,
        ⟨42641, true, false, [30926, 27061], [13]⟩,
        ⟨69232, true, false, [30926], [9, 13]⟩,
        ⟨942, false, false, [30926, 85871], []⟩,
        ⟨82541, false, false, [30926], []⟩,
        ⟨82534, false, false, [30926], []⟩,
        ⟨82543, false, false, [30926, 30911], []⟩,
        ⟨82550, true, false, [], [30911, 94051]⟩,
        ⟨82551, true, false, [], [94051]⟩
      ]⟩,
    ⟨[30933], [30930], .source 15531⟩,
    ⟨[27115, 88019], [27115, 88019], .contexts []⟩,
    ⟨[27115, 88019], [27115, 88019], .contexts []⟩,
    ⟨[88017, 7], [88017, 7], .contexts []⟩,
    ⟨[30935], [27117, 30911], .source 15532⟩,
    ⟨[88017, 7], [30935, 94051], .contexts [
        ⟨82556, false, false, [], []⟩,
        ⟨47721, true, false, [], [7]⟩,
        ⟨82555, true, false, [27114], [9, 7]⟩,
        ⟨82555, true, false, [27114], [9, 7]⟩,
        ⟨82554, true, false, [27114], [9, 7]⟩,
        ⟨69310, true, false, [27114], [9, 7]⟩,
        ⟨579, false, false, [27114, 85871], []⟩,
        ⟨82541, false, false, [27114], []⟩,
        ⟨82534, false, false, [27114], []⟩,
        ⟨82543, false, false, [27114, 30911], []⟩,
        ⟨69307, true, false, [], [30911, 94051]⟩,
        ⟨82557, true, false, [], [94051]⟩
      ]⟩,
    ⟨[30937], [30934], .source 15533⟩]

/-- Exact literal claimed equations and contextual derivations, block 1290. -/
def y322TCIndexRaw1290 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[30917, 94049], [30917, 94049], .contexts []⟩,
    ⟨[94049, 5], [94047], .contexts [
        ⟨82395, false, false, [], []⟩,
        ⟨82396, false, false, [], []⟩,
        ⟨82375, false, false, [], []⟩,
        ⟨82375, false, false, [], []⟩
      ]⟩,
    ⟨[94049, 4], [94049, 5], .contexts [
        ⟨29, false, false, [94049], []⟩
      ]⟩,
    ⟨[94047, 9], [94047, 9], .contexts []⟩,
    ⟨[94047], [94047], .contexts []⟩,
    ⟨[30939], [30916], .source 15534⟩,
    ⟨[30916], [30916], .contexts []⟩,
    ⟨[94047, 9], [30939, 94047], .contexts [
        ⟨82563, false, false, [], []⟩,
        ⟨82376, true, false, [], [9]⟩,
        ⟨82560, true, false, [30916], [5, 9]⟩,
        ⟨82560, true, false, [30916], [5, 9]⟩,
        ⟨82539, true, false, [30916], [5, 9]⟩,
        ⟨82535, true, false, [30916], [5, 9]⟩,
        ⟨598, false, false, [30916, 94049], []⟩,
        ⟨82562, false, false, [30916], []⟩,
        ⟨82561, false, false, [30916], []⟩,
        ⟨82564, false, false, [30916], []⟩,
        ⟨82566, true, false, [], [94047]⟩,
        ⟨82566, true, false, [], [94047]⟩,
        ⟨82565, true, false, [], [94047]⟩
      ]⟩,
    ⟨[30923, 94051], [30923, 94051], .contexts []⟩,
    ⟨[29245, 88347], [29245, 88347], .contexts []⟩,
    ⟨[29245, 88347], [29245, 88347], .contexts []⟩,
    ⟨[92951, 11], [29245, 88347], .contexts [
        ⟨76208, false, false, [], []⟩,
        ⟨76210, false, false, [], []⟩,
        ⟨82569, false, false, [], []⟩,
        ⟨82570, false, false, [], []⟩,
        ⟨82570, false, false, [], []⟩
      ]⟩,
    ⟨[30941], [18975, 28669], .source 15535⟩,
    ⟨[30943], [29245, 30941], .source 15536⟩,
    ⟨[94051, 11], [94051, 11], .contexts []⟩,
    ⟨[84743], [84743], .contexts []⟩,
    ⟨[30945], [30925, 30943], .source 15537⟩,
    ⟨[94051, 11], [30945, 84743], .contexts [
        ⟨82574, false, false, [], []⟩,
        ⟨82568, true, false, [30922], [11]⟩,
        ⟨82568, true, false, [30922], [11]⟩,
        ⟨82546, true, false, [30922], [11]⟩,
        ⟨82542, true, false, [30922], [11]⟩,
        ⟨144, false, false, [30922, 92951], []⟩,
        ⟨145, false, false, [30922, 92951], []⟩,
        ⟨82571, false, false, [30922], [3]⟩,
        ⟨50042, false, false, [30922, 29245], []⟩,
        ⟨74677, false, false, [30922, 29245, 18975], []⟩,
        ⟨82572, true, false, [30922, 29245], [84743]⟩,
        ⟨82573, true, false, [30922], [84743]⟩,
        ⟨82575, false, false, [30922, 30943], []⟩,
        ⟨82547, true, false, [], [30943, 84743]⟩,
        ⟨82576, true, false, [], [84743]⟩
      ]⟩,
    ⟨[30947], [30944], .source 15538⟩,
    ⟨[84743, 11], [30947, 94051], .contexts [
        ⟨82577, true, false, [30944], [11]⟩,
        ⟨53, false, false, [30944, 94051], []⟩,
        ⟨82578, true, false, [], [94051]⟩
      ]⟩,
    ⟨[30931, 94051], [30931, 94051], .contexts []⟩,
    ⟨[86231, 13], [30931, 94051], .contexts [
        ⟨82549, false, false, [], []⟩,
        ⟨82552, false, false, [], []⟩,
        ⟨82580, false, false, [], []⟩,
        ⟨82580, false, false, [], []⟩
      ]⟩,
    ⟨[30949], [2243, 30931], .source 15539⟩,
    ⟨[94049, 13], [94049, 13], .contexts []⟩,
    ⟨[30951], [30933, 30949], .source 15540⟩,
    ⟨[94049, 13], [30951, 94049], .contexts [
        ⟨82583, false, false, [], []⟩,
        ⟨82379, true, false, [], [13]⟩,
        ⟨82581, true, false, [30930], [1, 13]⟩,
        ⟨1968, false, false, [30930, 86231], []⟩,
        ⟨248, false, false, [30930, 86231], []⟩,
        ⟨36083, false, false, [30930], [13, 1]⟩,
        ⟨82552, false, false, [30930, 2243], [1]⟩,
        ⟨82582, true, false, [30930], [94051, 1]⟩,
        ⟨82379, false, false, [30930, 30949], []⟩,
        ⟨82536, false, false, [30930, 30949], []⟩,
        ⟨82553, true, false, [], [30949, 94049]⟩,
        ⟨82584, true, false, [], [94049]⟩
      ]⟩,
    ⟨[88017, 7], [30935, 94051], .contexts [
        ⟨82556, false, false, [], []⟩,
        ⟨82558, false, false, [], []⟩
      ]⟩,
    ⟨[30935, 94051], [30935, 94051], .contexts []⟩,
    ⟨[88017, 1], [22209, 88013], .contexts [
        ⟨48199, false, false, [], []⟩,
        ⟨49066, false, false, [], []⟩,
        ⟨48196, false, false, [], []⟩,
        ⟨48196, false, false, [], []⟩
      ]⟩,
    ⟨[94049, 7], [94049, 7], .contexts []⟩,
    ⟨[30953], [30937, 22209], .source 15541⟩,
    ⟨[94049, 7], [30953, 88013], .contexts [
        ⟨82589, false, false, [], []⟩,
        ⟨82379, true, false, [], [7]⟩,
        ⟨82587, true, false, [30934], [1, 7]⟩,
        ⟨82587, true, false, [30934], [1, 7]⟩,
        ⟨82586, true, false, [30934], [1, 7]⟩,
        ⟨502, false, false, [30934, 88017], []⟩,
        ⟨9, false, false, [30934, 88017], []⟩,
        ⟨82588, false, false, [30934], []⟩,
        ⟨49068, false, false, [30934, 22209], []⟩,
        ⟨82559, true, false, [], [22209, 88013]⟩,
        ⟨82590, true, false, [], [88013]⟩
      ]⟩,
    ⟨[30955], [30952], .source 15542⟩,
    ⟨[88013, 7], [30955, 94049], .contexts [
        ⟨82591, true, false, [30952], [7]⟩,
        ⟨38, false, false, [30952, 94049], []⟩,
        ⟨82592, true, false, [], [94049]⟩
      ]⟩,
    ⟨[30939, 94047], [30939, 94047], .contexts []⟩,
    ⟨[30939, 94047], [30939, 94047], .contexts []⟩,
    ⟨[94047, 9], [30939, 94047], .contexts [
        ⟨82563, false, false, [], []⟩,
        ⟨82567, false, false, [], []⟩,
        ⟨82594, false, false, [], []⟩,
        ⟨82595, false, false, [], []⟩,
        ⟨82595, false, false, [], []⟩
      ]⟩,
    ⟨[94047, 3], [94045], .contexts [
        ⟨82397, false, false, [], []⟩,
        ⟨82398, false, false, [], []⟩,
        ⟨82371, false, false, [], []⟩,
        ⟨82371, false, false, [], []⟩
      ]⟩,
    ⟨[94047, 2], [94047, 3], .contexts [
        ⟨21, false, false, [94047], []⟩
      ]⟩,
    ⟨[94045], [94045], .contexts []⟩,
    ⟨[30938], [30938], .contexts []⟩,
    ⟨[30945, 84743], [30945, 84743], .contexts []⟩,
    ⟨[30945, 84743], [30945, 84743], .contexts []⟩,
    ⟨[30945, 84745], [30945, 84745], .contexts []⟩,
    ⟨[84745, 11], [84745, 11], .contexts []⟩,
    ⟨[30944], [30944], .contexts []⟩,
    ⟨[84745, 11], [30947, 94049], .contexts [
        ⟨82604, false, false, [], []⟩,
        ⟨82603, true, false, [30944], [11]⟩,
        ⟨28515, true, false, [], [11]⟩,
        ⟨82602, true, false, [30944], [1, 11]⟩,
        ⟨82602, true, false, [30944], [1, 11]⟩,
        ⟨82601, true, false, [30944], [1, 11]⟩,
        ⟨82577, true, false, [30944], [1, 11]⟩,
        ⟨82574, true, false, [30944], [1, 11]⟩,
        ⟨567, false, false, [30944, 94051], []⟩,
        ⟨9, false, false, [30944, 94051], []⟩,
        ⟨82393, false, false, [30944], []⟩,
        ⟨82394, false, false, [30944], []⟩,
        ⟨82378, false, false, [30944], []⟩,
        ⟨82378, false, false, [30944], []⟩,
        ⟨82536, false, false, [30944], []⟩,
        ⟨82605, true, false, [], [94049]⟩,
        ⟨82605, true, false, [], [94049]⟩,
        ⟨82578, true, false, [], [94049]⟩
      ]⟩,
    ⟨[30951, 94049], [30951, 94049], .contexts []⟩,
    ⟨[94049, 13], [30951, 94049], .contexts [
        ⟨82583, false, false, [], []⟩,
        ⟨82585, false, false, [], []⟩,
        ⟨82607, false, false, [], []⟩,
        ⟨82607, false, false, [], []⟩
      ]⟩,
    ⟨[30957], [30950], .source 15543⟩,
    ⟨[30950], [30950], .contexts []⟩,
    ⟨[30959], [30951, 30953], .source 15544⟩,
    ⟨[30953, 88013], [30953, 88013], .contexts []⟩,
    ⟨[30953, 88013], [30953, 88013], .contexts []⟩,
    ⟨[94049, 7], [30953, 88013], .contexts [
        ⟨82589, false, false, [], []⟩,
        ⟨82591, false, false, [], []⟩,
        ⟨82612, false, false, [], []⟩,
        ⟨82613, false, false, [], []⟩,
        ⟨82613, false, false, [], []⟩
      ]⟩,
    ⟨[88013, 13], [88013, 13], .contexts []⟩,
    ⟨[30961], [30958], .source 15545⟩,
    ⟨[30963], [30961, 30953], .source 15546⟩,
    ⟨[88013, 13], [30963, 88013], .contexts [
        ⟨82615, false, false, [], []⟩,
        ⟨82611, false, false, [30958], [88013, 13]⟩,
        ⟨82591, true, false, [30958, 30951], [13]⟩,
        ⟨82608, true, false, [30958], [7, 13]⟩,
        ⟨14716, false, false, [30958, 94049], []⟩,
        ⟨39, false, false, [30958, 94049], []⟩,
        ⟨82614, false, false, [30958], []⟩,
        ⟨49068, false, false, [30958, 30953], []⟩,
        ⟨82616, true, false, [], [30953, 88013]⟩,
        ⟨82617, true, false, [], [88013]⟩
      ]⟩,
    ⟨[30965], [30953, 22209], .source 15547⟩,
    ⟨[30967], [30965, 30955], .source 15548⟩,
    ⟨[94047, 7], [94047, 7], .contexts []⟩,
    ⟨[30969], [30966], .source 15549⟩,
    ⟨[30966], [30966], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1291. -/
def y322TCIndexRaw1291 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[30969], [30966], .contexts [
        ⟨82622, false, false, [], []⟩,
        ⟨82623, false, false, [], []⟩,
        ⟨82623, false, false, [], []⟩
      ]⟩,
    ⟨[94047, 7], [30969, 94047], .contexts [
        ⟨82621, false, false, [], []⟩,
        ⟨82376, true, false, [], [7]⟩,
        ⟨82620, false, false, [30966], [94049, 5, 7]⟩,
        ⟨82593, true, false, [30966, 30965], [5, 7]⟩,
        ⟨82619, false, false, [30966], [88013, 7, 5, 7]⟩,
        ⟨49064, true, false, [30966, 30953], [7, 5, 7]⟩,
        ⟨47712, true, false, [30966, 30953], [7, 5, 7]⟩,
        ⟨82614, true, false, [30966], [5, 7, 5, 7]⟩,
        ⟨18796, false, false, [30966, 94049], []⟩,
        ⟨82562, false, false, [30966], []⟩,
        ⟨82561, false, false, [30966], []⟩,
        ⟨82564, false, false, [30966], []⟩,
        ⟨82624, true, false, [], [94047]⟩
      ]⟩,
    ⟨[30963, 88013], [30963, 88013], .contexts []⟩,
    ⟨[30963, 88013], [30963, 88013], .contexts []⟩,
    ⟨[30971], [30962], .source 15550⟩,
    ⟨[30962], [30962], .contexts []⟩,
    ⟨[30969, 94047], [30969, 94047], .contexts []⟩,
    ⟨[30969, 94047], [30969, 94047], .contexts []⟩,
    ⟨[94047, 7], [30969, 94047], .contexts [
        ⟨82621, false, false, [], []⟩,
        ⟨82625, false, false, [], []⟩,
        ⟨82630, false, false, [], []⟩,
        ⟨82631, false, false, [], []⟩,
        ⟨82631, false, false, [], []⟩
      ]⟩,
    ⟨[94045, 7], [94045, 7], .contexts []⟩,
    ⟨[30968], [30968], .contexts []⟩,
    ⟨[30967], [30968], .contexts [
        ⟨82622, true, true, [], []⟩,
        ⟨82634, false, false, [], []⟩,
        ⟨82634, false, false, [], []⟩
      ]⟩,
    ⟨[30967, 94045], [30967, 94045], .contexts []⟩,
    ⟨[94045, 7, 1], [30967, 94043], .contexts [
        ⟨82633, false, false, [], [1]⟩,
        ⟨82633, false, false, [], [1]⟩,
        ⟨82372, true, false, [], [7, 1]⟩,
        ⟨82632, true, false, [30968], [3, 7, 1]⟩,
        ⟨14911, false, false, [30968, 94047], [1]⟩,
        ⟨82598, false, false, [30968], [1]⟩,
        ⟨82597, false, false, [30968], [1]⟩,
        ⟨82599, false, false, [30968], [1]⟩,
        ⟨82635, true, false, [], [94045, 1]⟩,
        ⟨82636, false, false, [], [1]⟩,
        ⟨82636, false, false, [], [1]⟩,
        ⟨82369, false, false, [30967], []⟩
      ]⟩,
    ⟨[94043, 7], [94043, 7], .contexts []⟩,
    ⟨[30969, 94043], [30969, 94043], .contexts []⟩,
    ⟨[30969, 94041, 7], [94043, 15], .contexts [
        ⟨82366, true, false, [30969], [7]⟩,
        ⟨82639, true, false, [], [15, 7]⟩,
        ⟨82639, true, false, [], [15, 7]⟩,
        ⟨82624, false, false, [], [94043, 15, 7]⟩,
        ⟨82368, true, false, [30966], [15, 7]⟩,
        ⟨82368, true, false, [30966], [15, 7]⟩,
        ⟨82400, true, false, [30966], [15, 7]⟩,
        ⟨82399, true, false, [30966], [15, 7]⟩,
        ⟨9, true, false, [30966, 94045], [15, 7]⟩,
        ⟨502, true, false, [30966, 94045], [15, 7]⟩,
        ⟨82637, false, false, [30966], [7, 15, 7]⟩,
        ⟨82638, true, false, [], [15, 7]⟩,
        ⟨82638, true, false, [], [15, 7]⟩,
        ⟨18155, false, false, [94043], []⟩,
        ⟨10, false, false, [94043], []⟩
      ]⟩,
    ⟨[94041, 7], [94041, 7], .contexts []⟩,
    ⟨[30967, 94041], [30967, 94041], .contexts []⟩,
    ⟨[30967, 94039, 7], [94041, 13], .contexts [
        ⟨82363, true, false, [30967], [7]⟩,
        ⟨82642, true, false, [], [13, 7]⟩,
        ⟨82642, true, false, [], [13, 7]⟩,
        ⟨82635, false, false, [], [94041, 13, 7]⟩,
        ⟨82365, true, false, [30968], [13, 7]⟩,
        ⟨82365, true, false, [30968], [13, 7]⟩,
        ⟨82403, true, false, [30968], [13, 7]⟩,
        ⟨82402, true, false, [30968], [13, 7]⟩,
        ⟨82640, true, false, [30968], [13, 7]⟩,
        ⟨82641, true, false, [], [13, 7]⟩,
        ⟨82641, true, false, [], [13, 7]⟩,
        ⟨518, false, false, [94041], []⟩,
        ⟨64, false, false, [94041], []⟩
      ]⟩,
    ⟨[94039, 7], [94039, 7], .contexts []⟩,
    ⟨[94039], [94039], .contexts []⟩,
    ⟨[94039, 7], [30969, 94039], .contexts [
        ⟨82644, false, false, [], []⟩,
        ⟨82643, false, false, [30966], []⟩,
        ⟨82404, false, false, [30966], []⟩,
        ⟨82405, false, false, [30966], []⟩,
        ⟨82362, false, false, [30966], []⟩,
        ⟨82362, false, false, [30966], []⟩,
        ⟨82645, false, false, [30966], []⟩,
        ⟨82624, true, false, [], [94039]⟩
      ]⟩,
    ⟨[30969, 94039], [30969, 94039], .contexts []⟩,
    ⟨[30969, 94039], [30969, 94039], .contexts []⟩,
    ⟨[94037, 7], [94037, 7], .contexts []⟩,
    ⟨[94037], [94037], .contexts []⟩,
    ⟨[94037, 7], [30967, 94037], .contexts [
        ⟨82649, false, false, [], []⟩,
        ⟨82359, true, false, [], [7]⟩,
        ⟨82648, true, false, [30968], [1, 7]⟩,
        ⟨82648, true, false, [30968], [1, 7]⟩,
        ⟨82647, true, false, [30968], [1, 7]⟩,
        ⟨82646, true, false, [30968], [1, 7]⟩,
        ⟨82644, true, false, [30968], [1, 7]⟩,
        ⟨502, false, false, [30968, 94039], []⟩,
        ⟨9, false, false, [30968, 94039], []⟩,
        ⟨82406, false, false, [30968], []⟩,
        ⟨82407, false, false, [30968], []⟩,
        ⟨82358, false, false, [30968], []⟩,
        ⟨82358, false, false, [30968], []⟩,
        ⟨82650, false, false, [30968], []⟩,
        ⟨82635, true, false, [], [94037]⟩
      ]⟩,
    ⟨[30967, 94037], [30967, 94037], .contexts []⟩,
    ⟨[30967, 94037], [30967, 94037], .contexts []⟩,
    ⟨[94037, 7], [30967, 94037], .contexts [
        ⟨82649, false, false, [], []⟩,
        ⟨82651, false, false, [], []⟩,
        ⟨82652, false, false, [], []⟩,
        ⟨82653, false, false, [], []⟩,
        ⟨82653, false, false, [], []⟩
      ]⟩,
    ⟨[94037, 11], [94035], .contexts [
        ⟨82408, false, false, [], []⟩,
        ⟨82409, false, false, [], []⟩,
        ⟨82354, false, false, [], []⟩,
        ⟨82354, false, false, [], []⟩
      ]⟩,
    ⟨[94037, 10], [94037, 11], .contexts [
        ⟨54, false, false, [94037], []⟩
      ]⟩,
    ⟨[94035], [94035], .contexts []⟩,
    ⟨[94033, 1], [94031], .contexts [
        ⟨82413, false, false, [], []⟩,
        ⟨82414, false, false, [], []⟩,
        ⟨82346, false, false, [], []⟩,
        ⟨82346, false, false, [], []⟩
      ]⟩,
    ⟨[94033, 0], [94033, 1], .contexts [
        ⟨9, false, false, [94033], []⟩
      ]⟩,
    ⟨[94031], [94031], .contexts []⟩,
    ⟨[94059], [84343, 9], .source 47094⟩,
    ⟨[84343, 9], [94059], .contexts [
        ⟨82661, true, false, [], []⟩
      ]⟩,
    ⟨[94059, 9], [84343], .contexts [
        ⟨82662, true, false, [], [9]⟩,
        ⟨46, false, false, [84343], []⟩,
        ⟨25910, false, false, [], []⟩
      ]⟩,
    ⟨[94059], [94059], .contexts []⟩,
    ⟨[84343, 9], [94059], .contexts [
        ⟨82662, false, false, [], []⟩,
        ⟨82664, false, false, [], []⟩,
        ⟨82664, false, false, [], []⟩
      ]⟩,
    ⟨[17033, 84345], [17033, 84345], .contexts []⟩,
    ⟨[17033, 84345], [17033, 84345], .contexts []⟩,
    ⟨[17033, 94059], [17033, 94059], .contexts []⟩,
    ⟨[17033, 94059], [17033, 94059], .contexts []⟩,
    ⟨[94059, 1], [94059, 1], .contexts []⟩,
    ⟨[94059], [94059], .contexts []⟩,
    ⟨[17033], [17033], .contexts [
        ⟨13, false, false, [], [17033]⟩
      ]⟩,
    ⟨[18079, 85321], [18079, 85321], .contexts []⟩,
    ⟨[18079, 85321], [18079, 85321], .contexts []⟩,
    ⟨[30981], [18079, 20523], .source 15555⟩,
    ⟨[94059, 3], [30981, 83623], .contexts [
        ⟨82665, true, false, [], [3]⟩,
        ⟨196, false, false, [84343], []⟩,
        ⟨197, false, false, [84343], []⟩,
        ⟨31205, false, false, [], [9]⟩,
        ⟨82673, false, false, [], [9]⟩,
        ⟨82674, false, false, [], [9]⟩,
        ⟨82674, false, false, [], [9]⟩,
        ⟨42148, false, false, [18079], []⟩,
        ⟨82675, true, false, [], [83623]⟩,
        ⟨42020, false, false, [30981], []⟩,
        ⟨13, true, false, [], [30981, 83623]⟩
      ]⟩,
    ⟨[30983], [30980], .source 15556⟩,
    ⟨[83623, 3], [30983, 94059], .contexts [
        ⟨82676, true, false, [30980], [3]⟩,
        ⟨20, false, false, [30980, 94059], []⟩,
        ⟨82677, true, false, [], [94059]⟩
      ]⟩,
    ⟨[17025, 94059], [17025, 94059], .contexts []⟩,
    ⟨[17025, 94059], [17025, 94059], .contexts []⟩,
    ⟨[94059, 5], [94059, 5], .contexts []⟩,
    ⟨[17025], [17025], .contexts [
        ⟨13, false, false, [], [17025]⟩
      ]⟩,
    ⟨[94059, 15], [94059, 15], .contexts []⟩,
    ⟨[94059, 15], [86435], .contexts [
        ⟨82683, false, false, [], []⟩,
        ⟨82665, true, false, [], [15]⟩,
        ⟨205, false, false, [84343], []⟩,
        ⟨206, false, false, [84343], []⟩,
        ⟨25916, false, false, [], [9]⟩,
        ⟨37050, false, false, [], []⟩,
        ⟨37051, false, false, [], []⟩,
        ⟨37052, false, false, [], []⟩,
        ⟨37052, false, false, [], []⟩,
        ⟨37062, false, false, [], []⟩,
        ⟨672, true, false, [], [86435]⟩
      ]⟩,
    ⟨[86435, 15], [94059], .contexts [
        ⟨82684, true, false, [], [15]⟩,
        ⟨1, false, false, [94059], []⟩,
        ⟨82664, false, false, [], []⟩
      ]⟩,
    ⟨[94061], [94059, 11], .source 47095⟩,
    ⟨[94059, 11], [94061], .contexts [
        ⟨82686, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1292. -/
def y322TCIndexRaw1292 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94061, 11], [94059], .contexts [
        ⟨82687, true, false, [], [11]⟩,
        ⟨53, false, false, [94059], []⟩,
        ⟨82664, false, false, [], []⟩
      ]⟩,
    ⟨[94061], [94061], .contexts []⟩,
    ⟨[94061], [94061], .contexts []⟩,
    ⟨[94059, 11], [94061], .contexts [
        ⟨82687, false, false, [], []⟩,
        ⟨82689, false, false, [], []⟩,
        ⟨82690, false, false, [], []⟩,
        ⟨82690, false, false, [], []⟩
      ]⟩,
    ⟨[94059, 1], [17033, 94059], .contexts [
        ⟨82670, false, false, [], []⟩,
        ⟨82670, false, false, [], []⟩,
        ⟨82665, true, false, [], [1]⟩,
        ⟨691, false, false, [84343], []⟩,
        ⟨694, false, false, [84343], []⟩,
        ⟨25914, false, false, [], [9, 1, 9]⟩,
        ⟨26043, false, false, [], [1, 9]⟩,
        ⟨82666, false, false, [], [1, 9]⟩,
        ⟨82667, false, false, [], [1, 9]⟩,
        ⟨82667, false, false, [], [1, 9]⟩,
        ⟨25911, false, false, [17033], [9]⟩,
        ⟨82662, false, false, [17033], []⟩,
        ⟨82668, false, false, [], []⟩,
        ⟨82669, false, false, [], []⟩,
        ⟨82671, false, false, [17033], []⟩,
        ⟨82672, true, false, [], [94059]⟩,
        ⟨82668, false, false, [], []⟩,
        ⟨82669, false, false, [], []⟩
      ]⟩,
    ⟨[94059, 1], [17033, 94059], .contexts [
        ⟨82692, false, false, [], []⟩,
        ⟨82669, false, false, [], []⟩
      ]⟩,
    ⟨[17033, 94061], [17033, 94061], .contexts []⟩,
    ⟨[94061], [94061], .contexts []⟩,
    ⟨[94061, 1], [17033, 94061], .contexts [
        ⟨82691, true, false, [], [1]⟩,
        ⟨562, false, false, [94059], []⟩,
        ⟨563, false, false, [94059], []⟩,
        ⟨82693, false, false, [], [11]⟩,
        ⟨82687, false, false, [17033], []⟩,
        ⟨82694, false, false, [], []⟩,
        ⟨82695, false, false, [17033], []⟩,
        ⟨82672, true, false, [], [94061]⟩
      ]⟩,
    ⟨[17025, 94061], [17025, 94061], .contexts []⟩,
    ⟨[17025, 94061], [17025, 94061], .contexts []⟩,
    ⟨[94061, 5], [94061, 5], .contexts []⟩,
    ⟨[94061, 5], [17025, 94061], .contexts [
        ⟨82699, false, false, [], []⟩,
        ⟨82691, true, false, [], [5]⟩,
        ⟨642, false, false, [94059], []⟩,
        ⟨643, false, false, [94059], []⟩,
        ⟨82681, false, false, [], [11]⟩,
        ⟨82681, false, false, [], [11]⟩,
        ⟨82665, true, false, [], [5, 11]⟩,
        ⟨1079, false, false, [84343], [11]⟩,
        ⟨1080, false, false, [84343], [11]⟩,
        ⟨26058, false, false, [], [9, 11]⟩,
        ⟨82662, false, false, [17025], [11]⟩,
        ⟨82679, false, false, [], [11]⟩,
        ⟨82680, false, false, [], [11]⟩,
        ⟨82671, false, false, [17025], [11]⟩,
        ⟨82682, true, false, [], [94059, 11]⟩,
        ⟨82679, false, false, [], [11]⟩,
        ⟨82680, false, false, [], [11]⟩,
        ⟨82680, false, false, [], [11]⟩,
        ⟨82687, false, false, [17025], []⟩,
        ⟨82697, false, false, [], []⟩,
        ⟨82698, false, false, [], []⟩
      ]⟩,
    ⟨[94061, 5], [17025, 94061], .contexts [
        ⟨82700, false, false, [], []⟩,
        ⟨82695, false, false, [17025], []⟩,
        ⟨82682, true, false, [], [94061]⟩
      ]⟩,
    ⟨[23359, 88839], [23359, 88839], .contexts []⟩,
    ⟨[23359, 88839], [23359, 88839], .contexts []⟩,
    ⟨[23359, 88843], [23359, 88843], .contexts []⟩,
    ⟨[94061, 9], [23359, 88843], .contexts [
        ⟨82691, true, false, [], [9]⟩,
        ⟨221, false, false, [94059], []⟩,
        ⟨224, false, false, [94059], []⟩,
        ⟨82663, false, false, [], [11, 9, 11]⟩,
        ⟨26050, false, false, [], [11, 9, 11]⟩,
        ⟨25910, false, false, [], [11, 9, 11]⟩,
        ⟨25910, false, false, [], [11, 9, 11]⟩,
        ⟨52933, false, false, [], [9, 11]⟩,
        ⟨82702, false, false, [], [9, 11]⟩,
        ⟨82703, false, false, [], [9, 11]⟩,
        ⟨82703, false, false, [], [9, 11]⟩,
        ⟨52941, false, false, [23359], [11]⟩,
        ⟨52958, false, false, [23359], []⟩,
        ⟨82704, false, false, [], []⟩,
        ⟨52966, false, false, [23359], []⟩
      ]⟩,
    ⟨[94061, 9], [23359, 88843], .contexts [
        ⟨82705, false, false, [], []⟩,
        ⟨13, true, false, [], [23359, 88843]⟩
      ]⟩,
    ⟨[88843, 9], [23357, 94061], .contexts [
        ⟨82706, true, false, [23358], [9]⟩,
        ⟨46, false, false, [23358, 94061], []⟩,
        ⟨52904, false, true, [], [94061]⟩
      ]⟩,
    ⟨[94061, 15], [86437], .contexts [
        ⟨82691, true, false, [], [15]⟩,
        ⟨231, false, false, [94059], []⟩,
        ⟨232, false, false, [94059], []⟩,
        ⟨82683, false, false, [], [11]⟩,
        ⟨82684, false, false, [], [11]⟩,
        ⟨37051, false, false, [], [11]⟩,
        ⟨37052, false, false, [], [11]⟩,
        ⟨37052, false, false, [], [11]⟩,
        ⟨37074, false, false, [], []⟩,
        ⟨37075, false, false, [], []⟩,
        ⟨37076, false, false, [], []⟩,
        ⟨37076, false, false, [], []⟩,
        ⟨37081, false, false, [], []⟩,
        ⟨672, true, false, [], [86437]⟩
      ]⟩,
    ⟨[94063], [94061, 13], .source 47096⟩,
    ⟨[94061, 13], [94063], .contexts [
        ⟨82709, true, false, [], []⟩
      ]⟩,
    ⟨[94063, 13], [94061], .contexts [
        ⟨82710, true, false, [], [13]⟩,
        ⟨59, false, false, [94061], []⟩,
        ⟨82690, false, false, [], []⟩
      ]⟩,
    ⟨[94063], [94063], .contexts []⟩,
    ⟨[94063], [94063], .contexts []⟩,
    ⟨[17025, 94063], [17025, 94063], .contexts []⟩,
    ⟨[17025, 94063], [17025, 94063], .contexts []⟩,
    ⟨[94063, 5], [94063, 5], .contexts []⟩,
    ⟨[94063], [94063], .contexts []⟩,
    ⟨[94063, 5], [17025, 94063], .contexts [
        ⟨82716, false, false, [], []⟩,
        ⟨82713, true, false, [], [5]⟩,
        ⟨82713, true, false, [], [5]⟩,
        ⟨82712, true, false, [], [5]⟩,
        ⟨82710, true, false, [], [5]⟩,
        ⟨68, false, false, [94061], []⟩,
        ⟨69, false, false, [94061], []⟩,
        ⟨82699, false, false, [], [13]⟩,
        ⟨82701, false, false, [], [13]⟩,
        ⟨82697, false, false, [], [13]⟩,
        ⟨82698, false, false, [], [13]⟩,
        ⟨82698, false, false, [], [13]⟩,
        ⟨82710, false, false, [17025], []⟩,
        ⟨82714, false, false, [], []⟩,
        ⟨82715, false, false, [], []⟩,
        ⟨82717, false, false, [17025], []⟩,
        ⟨82682, true, false, [], [94063]⟩
      ]⟩,
    ⟨[94065], [94063, 15], .source 47097⟩,
    ⟨[94063, 15], [94065], .contexts [
        ⟨82719, true, false, [], []⟩
      ]⟩,
    ⟨[94065], [94065], .contexts []⟩,
    ⟨[94065], [94065], .contexts []⟩,
    ⟨[94063, 15], [94065], .contexts [
        ⟨82720, false, false, [], []⟩,
        ⟨82721, false, false, [], []⟩,
        ⟨82722, false, false, [], []⟩,
        ⟨82722, false, false, [], []⟩
      ]⟩,
    ⟨[17025, 94065], [17025, 94065], .contexts []⟩,
    ⟨[17025, 94065], [17025, 94065], .contexts []⟩,
    ⟨[94065, 5], [94065, 5], .contexts []⟩,
    ⟨[94065], [94065], .contexts []⟩,
    ⟨[94065, 13], [94065, 13], .contexts []⟩,
    ⟨[94065, 13], [86441], .contexts [
        ⟨82728, false, false, [], []⟩,
        ⟨82723, true, false, [], [13]⟩,
        ⟨259, false, false, [94063], []⟩,
        ⟨262, false, false, [94063], []⟩,
        ⟨82711, false, false, [], [15, 13, 15]⟩,
        ⟨82689, false, false, [], [15, 13, 15]⟩,
        ⟨82690, false, false, [], [15, 13, 15]⟩,
        ⟨82690, false, false, [], [15, 13, 15]⟩,
        ⟨82708, false, false, [], [13, 15]⟩,
        ⟨37075, false, false, [], [13, 15]⟩,
        ⟨37076, false, false, [], [13, 15]⟩,
        ⟨37076, false, false, [], [13, 15]⟩,
        ⟨37115, false, false, [], [15]⟩,
        ⟨37116, false, false, [], [15]⟩,
        ⟨37117, false, false, [], [15]⟩,
        ⟨37117, false, false, [], [15]⟩,
        ⟨37127, false, false, [], []⟩,
        ⟨37128, false, false, [], []⟩,
        ⟨37129, false, false, [], []⟩,
        ⟨37129, false, false, [], []⟩,
        ⟨37133, false, false, [], []⟩
      ]⟩,
    ⟨[94065, 13], [86441], .contexts [
        ⟨82729, false, false, [], []⟩,
        ⟨672, true, false, [], [86441]⟩
      ]⟩,
    ⟨[86441, 13], [94065], .contexts [
        ⟨82730, true, false, [], [13]⟩,
        ⟨59, false, false, [94065], []⟩,
        ⟨82722, false, false, [], []⟩
      ]⟩,
    ⟨[94065, 13], [86441], .contexts [
        ⟨82728, false, false, [], []⟩,
        ⟨82730, false, false, [], []⟩,
        ⟨37128, false, false, [], []⟩,
        ⟨37129, false, false, [], []⟩,
        ⟨37129, false, false, [], []⟩
      ]⟩,
    ⟨[30985], [20861, 29475], .source 15557⟩,
    ⟨[89319, 3], [89319, 3], .contexts []⟩,
    ⟨[30987], [30984], .source 15558⟩,
    ⟨[30984], [30984], .contexts []⟩,
    ⟨[89319, 3], [30987, 94065], .contexts [
        ⟨82734, false, false, [], []⟩,
        ⟨82733, false, false, [30984], [89319, 3]⟩,
        ⟨76989, true, false, [30984, 20861], [3]⟩,
        ⟨43438, true, false, [30984], [13, 3]⟩,
        ⟨43438, true, false, [30984], [13, 3]⟩,
        ⟨43437, true, false, [30984], [13, 3]⟩,
        ⟨43436, true, false, [30984], [13, 3]⟩,
        ⟨82732, true, false, [30984], [3, 13, 3]⟩,
        ⟨4550, false, false, [30984, 94065], []⟩,
        ⟨82727, false, false, [30984], []⟩,
        ⟨82736, true, false, [], [94065]⟩,
        ⟨82736, true, false, [], [94065]⟩,
        ⟨82735, true, false, [], [94065]⟩
      ]⟩,
    ⟨[94065, 3], [30985, 89319], .contexts [
        ⟨82737, true, false, [30986], [3]⟩,
        ⟨20, false, false, [30986, 89319], []⟩,
        ⟨82735, false, true, [], [89319]⟩
      ]⟩,
    ⟨[94067], [94065, 1], .source 47098⟩,
    ⟨[94065, 1], [94067], .contexts [
        ⟨82739, true, false, [], []⟩
      ]⟩,
    ⟨[94067, 1], [94065], .contexts [
        ⟨82740, true, false, [], [1]⟩,
        ⟨8, false, false, [94065], []⟩,
        ⟨82722, false, false, [], []⟩
      ]⟩,
    ⟨[94065, 1], [94067], .contexts [
        ⟨82740, false, false, [], []⟩
      ]⟩,
    ⟨[94067], [94067], .contexts []⟩,
    ⟨[94067], [94067], .contexts []⟩,
    ⟨[94065, 1], [94067], .contexts [
        ⟨82742, false, false, [], []⟩,
        ⟨82743, false, false, [], []⟩,
        ⟨82744, false, false, [], []⟩,
        ⟨82744, false, false, [], []⟩
      ]⟩,
    ⟨[30985, 89319], [30985, 89319], .contexts []⟩,
    ⟨[30985, 89319], [30985, 89319], .contexts []⟩,
    ⟨[94065, 3], [30985, 89319], .contexts [
        ⟨82738, false, false, [], []⟩,
        ⟨82746, false, false, [], []⟩,
        ⟨82747, false, false, [], []⟩,
        ⟨82747, false, false, [], []⟩
      ]⟩,
    ⟨[30989], [30985, 20357], .source 15559⟩,
    ⟨[30991], [30989, 30987], .source 15560⟩,
    ⟨[30991, 94067], [30991, 94067], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1293. -/
def y322TCIndexRaw1293 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94067], [94067], .contexts []⟩,
    ⟨[94067, 3], [30991, 94067], .contexts [
        ⟨82745, true, false, [], [3]⟩,
        ⟨1098, false, false, [94065], []⟩,
        ⟨1100, false, false, [94065], []⟩,
        ⟨82748, false, false, [], [1, 3, 1]⟩,
        ⟨55587, false, false, [30985], [3, 1]⟩,
        ⟨82749, true, false, [], [89319, 3, 1]⟩,
        ⟨82737, false, false, [30989], [1]⟩,
        ⟨82750, true, false, [], [94065, 1]⟩,
        ⟨82740, false, false, [30991], []⟩,
        ⟨82751, false, false, [], []⟩,
        ⟨82752, false, false, [30991], []⟩,
        ⟨13, true, false, [], [30991, 94067]⟩
      ]⟩,
    ⟨[94065, 5], [17025, 94065], .contexts [
        ⟨82726, false, false, [], []⟩,
        ⟨82723, true, false, [], [5]⟩,
        ⟨27, false, false, [94063], []⟩,
        ⟨30, false, false, [94063], []⟩,
        ⟨82716, false, false, [], [15]⟩,
        ⟨82718, false, false, [], [15]⟩,
        ⟨82714, false, false, [], [15]⟩,
        ⟨82715, false, false, [], [15]⟩,
        ⟨82715, false, false, [], [15]⟩,
        ⟨82720, false, false, [17025], []⟩,
        ⟨82724, false, false, [], []⟩,
        ⟨82725, false, false, [], []⟩,
        ⟨82727, false, false, [17025], []⟩,
        ⟨82682, true, false, [], [94065]⟩
      ]⟩,
    ⟨[94065, 5], [17025, 94065], .contexts [
        ⟨82726, false, false, [], []⟩,
        ⟨82754, false, false, [], []⟩,
        ⟨82724, false, false, [], []⟩,
        ⟨82725, false, false, [], []⟩,
        ⟨82725, false, false, [], []⟩
      ]⟩,
    ⟨[17025, 94067], [17025, 94067], .contexts []⟩,
    ⟨[17025, 94067], [17025, 94067], .contexts []⟩,
    ⟨[94067, 5], [94067, 5], .contexts []⟩,
    ⟨[94067, 5], [17025, 94067], .contexts [
        ⟨82758, false, false, [], []⟩,
        ⟨82745, true, false, [], [5]⟩,
        ⟨98, false, false, [94065], []⟩,
        ⟨99, false, false, [94065], []⟩,
        ⟨82755, false, false, [], [1]⟩,
        ⟨82740, false, false, [17025], []⟩,
        ⟨82756, false, false, [], []⟩,
        ⟨82757, false, false, [], []⟩,
        ⟨82752, false, false, [17025], []⟩,
        ⟨82682, true, false, [], [94067]⟩
      ]⟩,
    ⟨[94069], [94065, 9], .source 47099⟩,
    ⟨[94065, 9], [94069], .contexts [
        ⟨82760, true, false, [], []⟩
      ]⟩,
    ⟨[94069, 9], [94065], .contexts [
        ⟨82761, true, false, [], [9]⟩,
        ⟨46, false, false, [94065], []⟩,
        ⟨82722, false, false, [], []⟩
      ]⟩,
    ⟨[94065, 9], [94069], .contexts [
        ⟨82761, false, false, [], []⟩
      ]⟩,
    ⟨[94069], [94069], .contexts []⟩,
    ⟨[94069], [94069], .contexts []⟩,
    ⟨[94065, 9], [94069], .contexts [
        ⟨82763, false, false, [], []⟩,
        ⟨82764, false, false, [], []⟩,
        ⟨82765, false, false, [], []⟩,
        ⟨82765, false, false, [], []⟩
      ]⟩,
    ⟨[30985, 89321], [30985, 89321], .contexts []⟩,
    ⟨[30985, 89321], [30985, 89321], .contexts []⟩,
    ⟨[94069, 3], [94069, 3], .contexts []⟩,
    ⟨[30985], [30985], .contexts [
        ⟨13, false, false, [], [30985]⟩
      ]⟩,
    ⟨[94069, 3], [30985, 89321], .contexts [
        ⟨82769, false, false, [], []⟩,
        ⟨82766, true, false, [], [3]⟩,
        ⟨196, false, false, [94065], []⟩,
        ⟨197, false, false, [94065], []⟩,
        ⟨82748, false, false, [], [9]⟩,
        ⟨55589, false, false, [30985], []⟩,
        ⟨82767, false, false, [], []⟩,
        ⟨82768, false, false, [], []⟩,
        ⟨82770, true, false, [], [89321]⟩
      ]⟩,
    ⟨[89321, 3], [30987, 94069], .contexts [
        ⟨82771, true, false, [30984], [3]⟩,
        ⟨20, false, false, [30984, 94069], []⟩,
        ⟨82735, true, false, [], [94069]⟩
      ]⟩,
    ⟨[86441, 9], [18219, 92581], .contexts [
        ⟨73313, false, false, [], []⟩
      ]⟩,
    ⟨[18219, 92581], [18219, 92581], .contexts []⟩,
    ⟨[18219, 92581], [18219, 92581], .contexts []⟩,
    ⟨[94069, 13], [18219, 92581], .contexts [
        ⟨82766, true, false, [], [13]⟩,
        ⟨201, false, false, [94065], []⟩,
        ⟨202, false, false, [94065], []⟩,
        ⟨82732, false, false, [], [9]⟩,
        ⟨82773, false, false, [], []⟩,
        ⟨82774, false, false, [], []⟩,
        ⟨82775, false, false, [], []⟩,
        ⟨82775, false, false, [], []⟩,
        ⟨73312, false, false, [18219], []⟩,
        ⟨37094, true, false, [], [92581]⟩
      ]⟩,
    ⟨[94071], [94069, 11], .source 47100⟩,
    ⟨[94069, 11], [94071], .contexts [
        ⟨82777, true, false, [], []⟩
      ]⟩,
    ⟨[94071], [94071], .contexts []⟩,
    ⟨[94071], [94071], .contexts []⟩,
    ⟨[30985, 89323], [30985, 89323], .contexts []⟩,
    ⟨[89323], [89323], .contexts []⟩,
    ⟨[94071, 3], [30985, 89323], .contexts [
        ⟨82780, true, false, [], [3]⟩,
        ⟨82780, true, false, [], [3]⟩,
        ⟨82779, true, false, [], [3]⟩,
        ⟨82778, true, false, [], [3]⟩,
        ⟨215, false, false, [94069], []⟩,
        ⟨216, false, false, [94069], []⟩,
        ⟨82769, false, false, [], [11]⟩,
        ⟨82771, false, false, [], [11]⟩,
        ⟨82767, false, false, [], [11]⟩,
        ⟨82768, false, false, [], [11]⟩,
        ⟨82768, false, false, [], [11]⟩,
        ⟨55592, false, false, [30985], []⟩,
        ⟨82781, false, false, [], []⟩,
        ⟨82782, false, false, [30985], []⟩,
        ⟨82770, true, false, [], [89323]⟩
      ]⟩,
    ⟨[94073], [94071, 1], .source 47101⟩,
    ⟨[94071, 1], [94073], .contexts [
        ⟨82784, true, false, [], []⟩
      ]⟩,
    ⟨[94073], [94073], .contexts []⟩,
    ⟨[94073], [94073], .contexts []⟩,
    ⟨[94075], [94073, 13], .source 47102⟩,
    ⟨[94073, 13], [94075], .contexts [
        ⟨82788, true, false, [], []⟩
      ]⟩,
    ⟨[94075], [94075], .contexts []⟩,
    ⟨[94075], [94075], .contexts []⟩,
    ⟨[94077], [94075, 15], .source 47103⟩,
    ⟨[94075, 15], [94077], .contexts [
        ⟨82792, true, false, [], []⟩
      ]⟩,
    ⟨[94077], [94077], .contexts []⟩,
    ⟨[94077], [94077], .contexts []⟩,
    ⟨[94079], [94077, 1], .source 47104⟩,
    ⟨[94077, 1], [94079], .contexts [
        ⟨82796, true, false, [], []⟩
      ]⟩,
    ⟨[94079], [94079], .contexts []⟩,
    ⟨[94079], [94079], .contexts []⟩,
    ⟨[94081], [94079, 3], .source 47105⟩,
    ⟨[94079, 3], [94081], .contexts [
        ⟨82800, true, false, [], []⟩
      ]⟩,
    ⟨[94083], [94081, 5], .source 47106⟩,
    ⟨[94081, 5], [94083], .contexts [
        ⟨82802, true, false, [], []⟩
      ]⟩,
    ⟨[94081], [94081], .contexts []⟩,
    ⟨[94083], [94083], .contexts []⟩,
    ⟨[94083], [94083], .contexts []⟩,
    ⟨[94085], [94083, 1], .source 47107⟩,
    ⟨[94083, 1], [94085], .contexts [
        ⟨82807, true, false, [], []⟩
      ]⟩,
    ⟨[94085, 1], [94083], .contexts [
        ⟨82808, true, false, [], [1]⟩,
        ⟨8, false, false, [94083], []⟩,
        ⟨82806, false, false, [], []⟩
      ]⟩,
    ⟨[94087], [94085, 9], .source 47108⟩,
    ⟨[94085, 9], [94087], .contexts [
        ⟨82810, true, false, [], []⟩
      ]⟩,
    ⟨[94085], [94085], .contexts []⟩,
    ⟨[94089], [94087, 11], .source 47109⟩,
    ⟨[94087, 11], [94089], .contexts [
        ⟨82813, true, false, [], []⟩
      ]⟩,
    ⟨[94087], [94087], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1294. -/
def y322TCIndexRaw1294 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94089, 11], [94087], .contexts [
        ⟨82814, true, false, [], [11]⟩,
        ⟨53, false, false, [94087], []⟩,
        ⟨82815, false, false, [], []⟩
      ]⟩,
    ⟨[94091], [94089, 1], .source 47110⟩,
    ⟨[94089, 1], [94091], .contexts [
        ⟨82817, true, false, [], []⟩
      ]⟩,
    ⟨[94089], [94089], .contexts []⟩,
    ⟨[94093], [94091, 13], .source 47111⟩,
    ⟨[94091, 13], [94093], .contexts [
        ⟨82820, true, false, [], []⟩
      ]⟩,
    ⟨[94091], [94091], .contexts []⟩,
    ⟨[94095], [94093, 15], .source 47112⟩,
    ⟨[94093, 15], [94095], .contexts [
        ⟨82823, true, false, [], []⟩
      ]⟩,
    ⟨[94093], [94093], .contexts []⟩,
    ⟨[94095, 15], [94093], .contexts [
        ⟨82824, true, false, [], [15]⟩,
        ⟨1, false, false, [94093], []⟩,
        ⟨82825, false, false, [], []⟩
      ]⟩,
    ⟨[94097], [94095, 1], .source 47113⟩,
    ⟨[94095, 1], [94097], .contexts [
        ⟨82827, true, false, [], []⟩
      ]⟩,
    ⟨[94095], [94095], .contexts []⟩,
    ⟨[94099], [94097, 3], .source 47114⟩,
    ⟨[94097, 3], [94099], .contexts [
        ⟨82830, true, false, [], []⟩
      ]⟩,
    ⟨[94097], [94097], .contexts []⟩,
    ⟨[94101], [94099, 5], .source 47115⟩,
    ⟨[94099, 5], [94101], .contexts [
        ⟨82833, true, false, [], []⟩
      ]⟩,
    ⟨[94099], [94099], .contexts []⟩,
    ⟨[94103], [94101, 1], .source 47116⟩,
    ⟨[94101, 1], [94103], .contexts [
        ⟨82836, true, false, [], []⟩
      ]⟩,
    ⟨[94101], [94101], .contexts []⟩,
    ⟨[94105], [94103, 9], .source 47117⟩,
    ⟨[94103, 9], [94105], .contexts [
        ⟨82839, true, false, [], []⟩
      ]⟩,
    ⟨[94103], [94103], .contexts []⟩,
    ⟨[94107], [94105, 11], .source 47118⟩,
    ⟨[94105, 11], [94107], .contexts [
        ⟨82842, true, false, [], []⟩
      ]⟩,
    ⟨[94105], [94105], .contexts []⟩,
    ⟨[94109], [94107, 1], .source 47119⟩,
    ⟨[94107, 1], [94109], .contexts [
        ⟨82845, true, false, [], []⟩
      ]⟩,
    ⟨[94107], [94107], .contexts []⟩,
    ⟨[94111], [94109, 13], .source 47120⟩,
    ⟨[94109, 13], [94111], .contexts [
        ⟨82848, true, false, [], []⟩
      ]⟩,
    ⟨[94109], [94109], .contexts []⟩,
    ⟨[94111, 13], [94109], .contexts [
        ⟨82849, true, false, [], [13]⟩,
        ⟨59, false, false, [94109], []⟩,
        ⟨82850, false, false, [], []⟩
      ]⟩,
    ⟨[94113], [94111, 15], .source 47121⟩,
    ⟨[94111, 15], [94113], .contexts [
        ⟨82852, true, false, [], []⟩
      ]⟩,
    ⟨[94111], [94111], .contexts []⟩,
    ⟨[94115], [94113, 1], .source 47122⟩,
    ⟨[94113, 1], [94115], .contexts [
        ⟨82855, true, false, [], []⟩
      ]⟩,
    ⟨[94113], [94113], .contexts []⟩,
    ⟨[94117], [94115, 3], .source 47123⟩,
    ⟨[94115, 3], [94117], .contexts [
        ⟨82858, true, false, [], []⟩
      ]⟩,
    ⟨[94115], [94115], .contexts []⟩,
    ⟨[94119], [94117, 5], .source 47124⟩,
    ⟨[94117, 5], [94119], .contexts [
        ⟨82861, true, false, [], []⟩
      ]⟩,
    ⟨[94117], [94117], .contexts []⟩,
    ⟨[94121], [94119, 1], .source 47125⟩,
    ⟨[94119, 1], [94121], .contexts [
        ⟨82864, true, false, [], []⟩
      ]⟩,
    ⟨[94119], [94119], .contexts []⟩,
    ⟨[94123], [94121, 9], .source 47126⟩,
    ⟨[94121, 9], [94123], .contexts [
        ⟨82867, true, false, [], []⟩
      ]⟩,
    ⟨[94121], [94121], .contexts []⟩,
    ⟨[94125], [94123, 11], .source 47127⟩,
    ⟨[94123, 11], [94125], .contexts [
        ⟨82870, true, false, [], []⟩
      ]⟩,
    ⟨[94123], [94123], .contexts []⟩,
    ⟨[94127], [94125, 1], .source 47128⟩,
    ⟨[94125, 1], [94127], .contexts [
        ⟨82873, true, false, [], []⟩
      ]⟩,
    ⟨[94125], [94125], .contexts []⟩,
    ⟨[94127, 1], [94125], .contexts [
        ⟨82874, true, false, [], [1]⟩,
        ⟨8, false, false, [94125], []⟩,
        ⟨82875, false, false, [], []⟩
      ]⟩,
    ⟨[94129], [94127, 13], .source 47129⟩,
    ⟨[94127, 13], [94129], .contexts [
        ⟨82877, true, false, [], []⟩
      ]⟩,
    ⟨[94127], [94127], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1295. -/
def y322TCIndexRaw1295 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94129, 13], [94127], .contexts [
        ⟨82878, true, false, [], [13]⟩,
        ⟨59, false, false, [94127], []⟩,
        ⟨82879, false, false, [], []⟩
      ]⟩,
    ⟨[94131], [94129, 15], .source 47130⟩,
    ⟨[94129, 15], [94131], .contexts [
        ⟨82881, true, false, [], []⟩
      ]⟩,
    ⟨[94129], [94129], .contexts []⟩,
    ⟨[94133], [94131, 1], .source 47131⟩,
    ⟨[94131, 1], [94133], .contexts [
        ⟨82884, true, false, [], []⟩
      ]⟩,
    ⟨[94131], [94131], .contexts []⟩,
    ⟨[94135], [94133, 3], .source 47132⟩,
    ⟨[94133, 3], [94135], .contexts [
        ⟨82887, true, false, [], []⟩
      ]⟩,
    ⟨[94133], [94133], .contexts []⟩,
    ⟨[94137], [94135, 5], .source 47133⟩,
    ⟨[94135, 5], [94137], .contexts [
        ⟨82890, true, false, [], []⟩
      ]⟩,
    ⟨[94135], [94135], .contexts []⟩,
    ⟨[94139], [94137, 1], .source 47134⟩,
    ⟨[94137, 1], [94139], .contexts [
        ⟨82893, true, false, [], []⟩
      ]⟩,
    ⟨[94137], [94137], .contexts []⟩,
    ⟨[94141], [94139, 9], .source 47135⟩,
    ⟨[94139, 9], [94141], .contexts [
        ⟨82896, true, false, [], []⟩
      ]⟩,
    ⟨[94139], [94139], .contexts []⟩,
    ⟨[94143], [94141, 11], .source 47136⟩,
    ⟨[94141, 11], [94143], .contexts [
        ⟨82899, true, false, [], []⟩
      ]⟩,
    ⟨[94141], [94141], .contexts []⟩,
    ⟨[94145], [94143, 1], .source 47137⟩,
    ⟨[94143, 1], [94145], .contexts [
        ⟨82902, true, false, [], []⟩
      ]⟩,
    ⟨[94143], [94143], .contexts []⟩,
    ⟨[94147], [94145, 13], .source 47138⟩,
    ⟨[94145, 13], [94147], .contexts [
        ⟨82905, true, false, [], []⟩
      ]⟩,
    ⟨[94145], [94145], .contexts []⟩,
    ⟨[94149], [94147, 15], .source 47139⟩,
    ⟨[94147], [94147], .contexts []⟩,
    ⟨[94149, 15], [94147], .contexts [
        ⟨82908, false, false, [], [15]⟩,
        ⟨1, false, false, [94147], []⟩,
        ⟨82909, false, false, [], []⟩
      ]⟩,
    ⟨[94151], [94149, 1], .source 47140⟩,
    ⟨[94149], [94149], .contexts []⟩,
    ⟨[94151, 1], [94149], .contexts [
        ⟨82911, false, false, [], [1]⟩,
        ⟨8, false, false, [94149], []⟩,
        ⟨82912, false, false, [], []⟩
      ]⟩,
    ⟨[94153], [94151, 3], .source 47141⟩,
    ⟨[94151, 3], [94153], .contexts [
        ⟨82914, true, false, [], []⟩
      ]⟩,
    ⟨[94151], [94151], .contexts []⟩,
    ⟨[94153, 3], [94151], .contexts [
        ⟨82915, true, false, [], [3]⟩,
        ⟨20, false, false, [94151], []⟩,
        ⟨82916, false, false, [], []⟩
      ]⟩,
    ⟨[94155], [94153, 5], .source 47142⟩,
    ⟨[94153, 5], [94155], .contexts [
        ⟨82918, true, false, [], []⟩
      ]⟩,
    ⟨[94153], [94153], .contexts []⟩,
    ⟨[94155, 5], [94153], .contexts [
        ⟨82919, true, false, [], [5]⟩,
        ⟨28, false, false, [94153], []⟩,
        ⟨82920, false, false, [], []⟩
      ]⟩,
    ⟨[94157], [94155, 1], .source 47143⟩,
    ⟨[94155, 1], [94157], .contexts [
        ⟨82922, true, false, [], []⟩
      ]⟩,
    ⟨[94155], [94155], .contexts []⟩,
    ⟨[94157, 1], [94155], .contexts [
        ⟨82923, true, false, [], [1]⟩,
        ⟨8, false, false, [94155], []⟩,
        ⟨82924, false, false, [], []⟩
      ]⟩,
    ⟨[94159], [94157, 9], .source 47144⟩,
    ⟨[94157, 9], [94159], .contexts [
        ⟨82926, true, false, [], []⟩
      ]⟩,
    ⟨[94157], [94157], .contexts []⟩,
    ⟨[94159, 9], [94157], .contexts [
        ⟨82927, true, false, [], [9]⟩,
        ⟨46, false, false, [94157], []⟩,
        ⟨82928, false, false, [], []⟩
      ]⟩,
    ⟨[94161], [94159, 11], .source 47145⟩,
    ⟨[94159, 11], [94161], .contexts [
        ⟨82930, true, false, [], []⟩
      ]⟩,
    ⟨[94159], [94159], .contexts []⟩,
    ⟨[94161, 11], [94159], .contexts [
        ⟨82931, true, false, [], [11]⟩,
        ⟨53, false, false, [94159], []⟩,
        ⟨82932, false, false, [], []⟩
      ]⟩,
    ⟨[94163], [94161, 1], .source 47146⟩,
    ⟨[94161, 1], [94163], .contexts [
        ⟨82934, true, false, [], []⟩
      ]⟩,
    ⟨[94161], [94161], .contexts []⟩,
    ⟨[94163, 1], [94161], .contexts [
        ⟨82935, true, false, [], [1]⟩,
        ⟨8, false, false, [94161], []⟩,
        ⟨82936, false, false, [], []⟩
      ]⟩,
    ⟨[94165], [94163, 13], .source 47147⟩,
    ⟨[94163, 13], [94165], .contexts [
        ⟨82938, true, false, [], []⟩
      ]⟩,
    ⟨[94163], [94163], .contexts []⟩,
    ⟨[94165, 13], [94163], .contexts [
        ⟨82939, true, false, [], [13]⟩,
        ⟨59, false, false, [94163], []⟩,
        ⟨82940, false, false, [], []⟩
      ]⟩,
    ⟨[94167], [94165, 15], .source 47148⟩,
    ⟨[94165], [94165], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1296. -/
def y322TCIndexRaw1296 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94167, 15], [94165], .contexts [
        ⟨82942, false, false, [], [15]⟩,
        ⟨1, false, false, [94165], []⟩,
        ⟨82943, false, false, [], []⟩
      ]⟩,
    ⟨[94169], [94167, 1], .source 47149⟩,
    ⟨[94167, 1], [94169], .contexts [
        ⟨82945, true, false, [], []⟩
      ]⟩,
    ⟨[94167], [94167], .contexts []⟩,
    ⟨[94169, 1], [94167], .contexts [
        ⟨82946, true, false, [], [1]⟩,
        ⟨8, false, false, [94167], []⟩,
        ⟨82947, false, false, [], []⟩
      ]⟩,
    ⟨[94171], [94169, 3], .source 47150⟩,
    ⟨[94169, 3], [94171], .contexts [
        ⟨82949, true, false, [], []⟩
      ]⟩,
    ⟨[94169], [94169], .contexts []⟩,
    ⟨[94171, 3], [94169], .contexts [
        ⟨82950, true, false, [], [3]⟩,
        ⟨20, false, false, [94169], []⟩,
        ⟨82951, false, false, [], []⟩
      ]⟩,
    ⟨[94173], [94171, 5], .source 47151⟩,
    ⟨[94171], [94171], .contexts []⟩,
    ⟨[94173, 5], [94171], .contexts [
        ⟨82953, false, false, [], [5]⟩,
        ⟨28, false, false, [94171], []⟩,
        ⟨82954, false, false, [], []⟩
      ]⟩,
    ⟨[94175], [94173, 1], .source 47152⟩,
    ⟨[94173], [94173], .contexts []⟩,
    ⟨[94175, 1], [94173], .contexts [
        ⟨82956, false, false, [], [1]⟩,
        ⟨8, false, false, [94173], []⟩,
        ⟨82957, false, false, [], []⟩
      ]⟩,
    ⟨[94177], [94175, 9], .source 47153⟩,
    ⟨[94175], [94175], .contexts []⟩,
    ⟨[94177, 9], [94175], .contexts [
        ⟨82959, false, false, [], [9]⟩,
        ⟨46, false, false, [94175], []⟩,
        ⟨82960, false, false, [], []⟩
      ]⟩,
    ⟨[94179], [94177, 11], .source 47154⟩,
    ⟨[94177, 11], [94179], .contexts [
        ⟨82962, true, false, [], []⟩
      ]⟩,
    ⟨[94177], [94177], .contexts []⟩,
    ⟨[94179, 11], [94177], .contexts [
        ⟨82963, true, false, [], [11]⟩,
        ⟨53, false, false, [94177], []⟩,
        ⟨82964, false, false, [], []⟩
      ]⟩,
    ⟨[94179], [94179], .contexts []⟩,
    ⟨[94177, 9], [94175], .contexts [
        ⟨82961, false, false, [], []⟩,
        ⟨82960, false, false, [], []⟩,
        ⟨82960, false, false, [], []⟩
      ]⟩,
    ⟨[94175, 1], [94173], .contexts [
        ⟨82958, false, false, [], []⟩
      ]⟩,
    ⟨[94173], [94173], .contexts []⟩,
    ⟨[94171, 3], [94169], .contexts [
        ⟨82952, false, false, [], []⟩
      ]⟩,
    ⟨[94169], [94169], .contexts []⟩,
    ⟨[94169, 1], [94167], .contexts [
        ⟨82948, false, false, [], []⟩
      ]⟩,
    ⟨[94167], [94167], .contexts []⟩,
    ⟨[94167, 15], [94165], .contexts [
        ⟨82944, false, false, [], []⟩
      ]⟩,
    ⟨[94165], [94165], .contexts []⟩,
    ⟨[94177, 9, 1, 5, 3, 1, 15], [94165], .contexts [
        ⟨82967, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨82968, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82969, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82957, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82957, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82955, false, false, [], [3, 1, 15]⟩,
        ⟨82954, false, false, [], [3, 1, 15]⟩,
        ⟨82954, false, false, [], [3, 1, 15]⟩,
        ⟨82970, false, false, [], [1, 15]⟩,
        ⟨82971, false, false, [], [1, 15]⟩,
        ⟨82951, false, false, [], [1, 15]⟩,
        ⟨82951, false, false, [], [1, 15]⟩,
        ⟨82972, false, false, [], [15]⟩,
        ⟨82973, false, false, [], [15]⟩,
        ⟨82947, false, false, [], [15]⟩,
        ⟨82947, false, false, [], [15]⟩,
        ⟨82974, false, false, [], []⟩,
        ⟨82975, false, false, [], []⟩,
        ⟨82943, false, false, [], []⟩,
        ⟨82943, false, false, [], []⟩
      ]⟩,
    ⟨[94165, 13], [94163], .contexts [
        ⟨82941, false, false, [], []⟩
      ]⟩,
    ⟨[94163], [94163], .contexts []⟩,
    ⟨[94163, 1], [94161], .contexts [
        ⟨82937, false, false, [], []⟩
      ]⟩,
    ⟨[94161], [94161], .contexts []⟩,
    ⟨[94161, 11], [94159], .contexts [
        ⟨82933, false, false, [], []⟩
      ]⟩,
    ⟨[94159], [94159], .contexts []⟩,
    ⟨[94159, 9], [94157], .contexts [
        ⟨82929, false, false, [], []⟩
      ]⟩,
    ⟨[94157], [94157], .contexts []⟩,
    ⟨[94157, 1], [94155], .contexts [
        ⟨82925, false, false, [], []⟩
      ]⟩,
    ⟨[94155], [94155], .contexts []⟩,
    ⟨[94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1], [94155], .contexts [
        ⟨82976, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨82977, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82978, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82940, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82940, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82979, false, false, [], [11, 9, 1]⟩,
        ⟨82980, false, false, [], [11, 9, 1]⟩,
        ⟨82936, false, false, [], [11, 9, 1]⟩,
        ⟨82936, false, false, [], [11, 9, 1]⟩,
        ⟨82981, false, false, [], [9, 1]⟩,
        ⟨82982, false, false, [], [9, 1]⟩,
        ⟨82932, false, false, [], [9, 1]⟩,
        ⟨82932, false, false, [], [9, 1]⟩,
        ⟨82983, false, false, [], [1]⟩,
        ⟨82984, false, false, [], [1]⟩,
        ⟨82928, false, false, [], [1]⟩,
        ⟨82928, false, false, [], [1]⟩,
        ⟨82985, false, false, [], []⟩,
        ⟨82986, false, false, [], []⟩,
        ⟨82924, false, false, [], []⟩,
        ⟨82924, false, false, [], []⟩
      ]⟩,
    ⟨[94155, 5], [94153], .contexts [
        ⟨82921, false, false, [], []⟩
      ]⟩,
    ⟨[94153], [94153], .contexts []⟩,
    ⟨[94153, 3], [94151], .contexts [
        ⟨82917, false, false, [], []⟩
      ]⟩,
    ⟨[94151], [94151], .contexts []⟩,
    ⟨[94147], [94147], .contexts []⟩,
    ⟨[94145], [94145], .contexts []⟩,
    ⟨[
      94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13
    ], [94145], .contexts [
        ⟨82987, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨82988, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82989, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82920, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82920, false, false, [], [3, 1, 15, 13]⟩,
        ⟨82990, false, false, [], [1, 15, 13]⟩,
        ⟨82991, false, false, [], [1, 15, 13]⟩,
        ⟨82916, false, false, [], [1, 15, 13]⟩,
        ⟨82916, false, false, [], [1, 15, 13]⟩,
        ⟨82913, false, false, [], [15, 13]⟩,
        ⟨82912, false, false, [], [15, 13]⟩,
        ⟨82912, false, false, [], [15, 13]⟩,
        ⟨82910, false, false, [], [13]⟩,
        ⟨82992, false, false, [], [13]⟩,
        ⟨82909, false, false, [], [13]⟩,
        ⟨82909, false, false, [], [13]⟩,
        ⟨82906, true, false, [], [13]⟩,
        ⟨59, false, false, [94145], []⟩,
        ⟨82907, false, false, [], []⟩,
        ⟨82993, false, false, [], []⟩,
        ⟨82907, false, false, [], []⟩,
        ⟨82907, false, false, [], []⟩
      ]⟩,
    ⟨[94143], [94143], .contexts []⟩,
    ⟨[94141], [94141], .contexts []⟩,
    ⟨[94139], [94139], .contexts []⟩,
    ⟨[94137], [94137], .contexts []⟩,
    ⟨[
      94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [94137], .contexts [
        ⟨82994, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82903, true, false, [], [1, 11, 9, 1]⟩,
        ⟨8, false, false, [94143], [11, 9, 1]⟩,
        ⟨82904, false, false, [], [11, 9, 1]⟩,
        ⟨82995, false, false, [], [11, 9, 1]⟩,
        ⟨82904, false, false, [], [11, 9, 1]⟩,
        ⟨82904, false, false, [], [11, 9, 1]⟩,
        ⟨82900, true, false, [], [11, 9, 1]⟩,
        ⟨53, false, false, [94141], [9, 1]⟩,
        ⟨82901, false, false, [], [9, 1]⟩,
        ⟨82996, false, false, [], [9, 1]⟩,
        ⟨82901, false, false, [], [9, 1]⟩,
        ⟨82901, false, false, [], [9, 1]⟩,
        ⟨82897, true, false, [], [9, 1]⟩,
        ⟨46, false, false, [94139], [1]⟩,
        ⟨82898, false, false, [], [1]⟩,
        ⟨82997, false, false, [], [1]⟩,
        ⟨82898, false, false, [], [1]⟩,
        ⟨82898, false, false, [], [1]⟩,
        ⟨82894, true, false, [], [1]⟩,
        ⟨8, false, false, [94137], []⟩,
        ⟨82895, false, false, [], []⟩,
        ⟨82998, false, false, [], []⟩,
        ⟨82895, false, false, [], []⟩,
        ⟨82895, false, false, [], []⟩
      ]⟩,
    ⟨[94135], [94135], .contexts []⟩,
    ⟨[94133], [94133], .contexts []⟩,
    ⟨[94131], [94131], .contexts []⟩,
    ⟨[94129], [94129], .contexts []⟩,
    ⟨[
      94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15
    ], [94129], .contexts [
        ⟨82999, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82891, true, false, [], [5, 3, 1, 15]⟩,
        ⟨28, false, false, [94135], [3, 1, 15]⟩,
        ⟨82892, false, false, [], [3, 1, 15]⟩,
        ⟨83000, false, false, [], [3, 1, 15]⟩,
        ⟨82892, false, false, [], [3, 1, 15]⟩,
        ⟨82892, false, false, [], [3, 1, 15]⟩,
        ⟨82888, true, false, [], [3, 1, 15]⟩,
        ⟨20, false, false, [94133], [1, 15]⟩,
        ⟨82889, false, false, [], [1, 15]⟩,
        ⟨83001, false, false, [], [1, 15]⟩,
        ⟨82889, false, false, [], [1, 15]⟩,
        ⟨82889, false, false, [], [1, 15]⟩,
        ⟨82885, true, false, [], [1, 15]⟩,
        ⟨8, false, false, [94131], [15]⟩,
        ⟨82886, false, false, [], [15]⟩,
        ⟨83002, false, false, [], [15]⟩,
        ⟨82886, false, false, [], [15]⟩,
        ⟨82886, false, false, [], [15]⟩,
        ⟨82882, true, false, [], [15]⟩,
        ⟨1, false, false, [94129], []⟩,
        ⟨82883, false, false, [], []⟩,
        ⟨83003, false, false, [], []⟩,
        ⟨82883, false, false, [], []⟩,
        ⟨82883, false, false, [], []⟩
      ]⟩,
    ⟨[94127], [94127], .contexts []⟩,
    ⟨[94125], [94125], .contexts []⟩,
    ⟨[94123], [94123], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1297. -/
def y322TCIndexRaw1297 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94121], [94121], .contexts []⟩,
    ⟨[94119], [94119], .contexts []⟩,
    ⟨[
      94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1
    ], [94119], .contexts [
        ⟨83004, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨82880, false, false, [], [1, 11, 9, 1]⟩,
        ⟨83005, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82879, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82879, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82876, false, false, [], [11, 9, 1]⟩,
        ⟨83006, false, false, [], [11, 9, 1]⟩,
        ⟨82875, false, false, [], [11, 9, 1]⟩,
        ⟨82875, false, false, [], [11, 9, 1]⟩,
        ⟨82871, true, false, [], [11, 9, 1]⟩,
        ⟨53, false, false, [94123], [9, 1]⟩,
        ⟨82872, false, false, [], [9, 1]⟩,
        ⟨83007, false, false, [], [9, 1]⟩,
        ⟨82872, false, false, [], [9, 1]⟩,
        ⟨82872, false, false, [], [9, 1]⟩,
        ⟨82868, true, false, [], [9, 1]⟩,
        ⟨46, false, false, [94121], [1]⟩,
        ⟨82869, false, false, [], [1]⟩,
        ⟨83008, false, false, [], [1]⟩,
        ⟨82869, false, false, [], [1]⟩,
        ⟨82869, false, false, [], [1]⟩,
        ⟨82865, true, false, [], [1]⟩,
        ⟨8, false, false, [94119], []⟩,
        ⟨82866, false, false, [], []⟩,
        ⟨83009, false, false, [], []⟩,
        ⟨82866, false, false, [], []⟩,
        ⟨82866, false, false, [], []⟩
      ]⟩,
    ⟨[94117], [94117], .contexts []⟩,
    ⟨[94115], [94115], .contexts []⟩,
    ⟨[94111], [94111], .contexts []⟩,
    ⟨[
      94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [94111], .contexts [
        ⟨83010, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82862, true, false, [], [5, 3, 1, 15]⟩,
        ⟨28, false, false, [94117], [3, 1, 15]⟩,
        ⟨82863, false, false, [], [3, 1, 15]⟩,
        ⟨83011, false, false, [], [3, 1, 15]⟩,
        ⟨82863, false, false, [], [3, 1, 15]⟩,
        ⟨82863, false, false, [], [3, 1, 15]⟩,
        ⟨82859, true, false, [], [3, 1, 15]⟩,
        ⟨20, false, false, [94115], [1, 15]⟩,
        ⟨82860, false, false, [], [1, 15]⟩,
        ⟨83012, false, false, [], [1, 15]⟩,
        ⟨82860, false, false, [], [1, 15]⟩,
        ⟨82860, false, false, [], [1, 15]⟩,
        ⟨82856, true, false, [], [1, 15]⟩,
        ⟨8, false, false, [94113], [15]⟩,
        ⟨82857, false, false, [], [15]⟩,
        ⟨82857, false, false, [], [15]⟩,
        ⟨82857, false, false, [], [15]⟩,
        ⟨82853, true, false, [], [15]⟩,
        ⟨1, false, false, [94111], []⟩,
        ⟨82854, false, false, [], []⟩,
        ⟨83013, false, false, [], []⟩,
        ⟨82854, false, false, [], []⟩,
        ⟨82854, false, false, [], []⟩
      ]⟩,
    ⟨[94111, 13], [94109], .contexts [
        ⟨82851, false, false, [], []⟩
      ]⟩,
    ⟨[94109], [94109], .contexts []⟩,
    ⟨[94107], [94107], .contexts []⟩,
    ⟨[94103], [94103], .contexts []⟩,
    ⟨[
      94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1
    ], [94101], .contexts [
        ⟨83014, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨83015, false, false, [], [1, 11, 9, 1]⟩,
        ⟨83016, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82850, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82850, false, false, [], [1, 11, 9, 1]⟩,
        ⟨82846, true, false, [], [1, 11, 9, 1]⟩,
        ⟨8, false, false, [94107], [11, 9, 1]⟩,
        ⟨82847, false, false, [], [11, 9, 1]⟩,
        ⟨83017, false, false, [], [11, 9, 1]⟩,
        ⟨82847, false, false, [], [11, 9, 1]⟩,
        ⟨82847, false, false, [], [11, 9, 1]⟩,
        ⟨82843, true, false, [], [11, 9, 1]⟩,
        ⟨53, false, false, [94105], [9, 1]⟩,
        ⟨82844, false, false, [], [9, 1]⟩,
        ⟨82844, false, false, [], [9, 1]⟩,
        ⟨82844, false, false, [], [9, 1]⟩,
        ⟨82840, true, false, [], [9, 1]⟩,
        ⟨46, false, false, [94103], [1]⟩,
        ⟨82841, false, false, [], [1]⟩,
        ⟨83018, false, false, [], [1]⟩,
        ⟨82841, false, false, [], [1]⟩,
        ⟨82841, false, false, [], [1]⟩,
        ⟨82837, true, false, [], [1]⟩,
        ⟨8, false, false, [94101], []⟩,
        ⟨82838, false, false, [], []⟩,
        ⟨82838, false, false, [], []⟩,
        ⟨82838, false, false, [], []⟩
      ]⟩,
    ⟨[94099], [94099], .contexts []⟩,
    ⟨[94095], [94095], .contexts []⟩,
    ⟨[94095, 15], [94093], .contexts [
        ⟨82826, false, false, [], []⟩
      ]⟩,
    ⟨[94093], [94093], .contexts []⟩,
    ⟨[
      94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15
    ], [94093], .contexts [
        ⟨83019, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82834, true, false, [], [5, 3, 1, 15]⟩,
        ⟨28, false, false, [94099], [3, 1, 15]⟩,
        ⟨82835, false, false, [], [3, 1, 15]⟩,
        ⟨83020, false, false, [], [3, 1, 15]⟩,
        ⟨82835, false, false, [], [3, 1, 15]⟩,
        ⟨82835, false, false, [], [3, 1, 15]⟩,
        ⟨82831, true, false, [], [3, 1, 15]⟩,
        ⟨20, false, false, [94097], [1, 15]⟩,
        ⟨82832, false, false, [], [1, 15]⟩,
        ⟨82832, false, false, [], [1, 15]⟩,
        ⟨82832, false, false, [], [1, 15]⟩,
        ⟨82828, true, false, [], [1, 15]⟩,
        ⟨8, false, false, [94095], [15]⟩,
        ⟨82829, false, false, [], [15]⟩,
        ⟨83021, false, false, [], [15]⟩,
        ⟨82829, false, false, [], [15]⟩,
        ⟨82829, false, false, [], [15]⟩,
        ⟨83022, false, false, [], []⟩,
        ⟨83023, false, false, [], []⟩,
        ⟨82825, false, false, [], []⟩,
        ⟨82825, false, false, [], []⟩
      ]⟩,
    ⟨[94091], [94091], .contexts []⟩,
    ⟨[94089], [94089], .contexts []⟩,
    ⟨[94087], [94087], .contexts []⟩,
    ⟨[94085], [94085], .contexts []⟩,
    ⟨[
      94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [94085], .contexts [
        ⟨83024, false, false, [], [13, 1, 11, 9]⟩,
        ⟨82821, true, false, [], [13, 1, 11, 9]⟩,
        ⟨59, false, false, [94091], [1, 11, 9]⟩,
        ⟨82822, false, false, [], [1, 11, 9]⟩,
        ⟨83025, false, false, [], [1, 11, 9]⟩,
        ⟨82822, false, false, [], [1, 11, 9]⟩,
        ⟨82822, false, false, [], [1, 11, 9]⟩,
        ⟨82818, true, false, [], [1, 11, 9]⟩,
        ⟨8, false, false, [94089], [11, 9]⟩,
        ⟨82819, false, false, [], [11, 9]⟩,
        ⟨83026, false, false, [], [11, 9]⟩,
        ⟨82819, false, false, [], [11, 9]⟩,
        ⟨82819, false, false, [], [11, 9]⟩,
        ⟨82816, false, false, [], [9]⟩,
        ⟨83027, false, false, [], [9]⟩,
        ⟨82815, false, false, [], [9]⟩,
        ⟨82815, false, false, [], [9]⟩,
        ⟨82811, true, false, [], [9]⟩,
        ⟨46, false, false, [94085], []⟩,
        ⟨82812, false, false, [], []⟩,
        ⟨83028, false, false, [], []⟩,
        ⟨82812, false, false, [], []⟩,
        ⟨82812, false, false, [], []⟩
      ]⟩,
    ⟨[94081], [94081], .contexts []⟩,
    ⟨[
      94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15
    ], [94075], .contexts [
        ⟨83029, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨82809, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82805, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82806, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82806, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82803, true, false, [], [5, 3, 1, 15]⟩,
        ⟨28, false, false, [94081], [3, 1, 15]⟩,
        ⟨82804, false, false, [], [3, 1, 15]⟩,
        ⟨83030, false, false, [], [3, 1, 15]⟩,
        ⟨82804, false, false, [], [3, 1, 15]⟩,
        ⟨82804, false, false, [], [3, 1, 15]⟩,
        ⟨82801, true, false, [], [3, 1, 15]⟩,
        ⟨20, false, false, [94079], [1, 15]⟩,
        ⟨82799, false, false, [], [1, 15]⟩,
        ⟨82798, false, false, [], [1, 15]⟩,
        ⟨82799, false, false, [], [1, 15]⟩,
        ⟨82799, false, false, [], [1, 15]⟩,
        ⟨82797, true, false, [], [1, 15]⟩,
        ⟨8, false, false, [94077], [15]⟩,
        ⟨82795, false, false, [], [15]⟩,
        ⟨82794, false, false, [], [15]⟩,
        ⟨82795, false, false, [], [15]⟩,
        ⟨82795, false, false, [], [15]⟩,
        ⟨82793, true, false, [], [15]⟩,
        ⟨1, false, false, [94075], []⟩,
        ⟨82791, false, false, [], []⟩,
        ⟨82790, false, false, [], []⟩,
        ⟨82791, false, false, [], []⟩,
        ⟨82791, false, false, [], []⟩
      ]⟩,
    ⟨[
      94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9
    ], [94065], .contexts [
        ⟨83031, false, false, [], [13, 1, 11, 9]⟩,
        ⟨82789, true, false, [], [13, 1, 11, 9]⟩,
        ⟨59, false, false, [94073], [1, 11, 9]⟩,
        ⟨82787, false, false, [], [1, 11, 9]⟩,
        ⟨82786, false, false, [], [1, 11, 9]⟩,
        ⟨82787, false, false, [], [1, 11, 9]⟩,
        ⟨82787, false, false, [], [1, 11, 9]⟩,
        ⟨82785, true, false, [], [1, 11, 9]⟩,
        ⟨8, false, false, [94071], [11, 9]⟩,
        ⟨82780, false, false, [], [11, 9]⟩,
        ⟨82779, false, false, [], [11, 9]⟩,
        ⟨82780, false, false, [], [11, 9]⟩,
        ⟨82780, false, false, [], [11, 9]⟩,
        ⟨82778, true, false, [], [11, 9]⟩,
        ⟨53, false, false, [94069], [9]⟩,
        ⟨82765, false, false, [], [9]⟩,
        ⟨82764, false, false, [], [9]⟩,
        ⟨82765, false, false, [], [9]⟩,
        ⟨82765, false, false, [], [9]⟩,
        ⟨82762, false, false, [], []⟩,
        ⟨82721, false, false, [], []⟩,
        ⟨82722, false, false, [], []⟩,
        ⟨82722, false, false, [], []⟩
      ]⟩,
    ⟨[94067, 5], [17025, 94067], .contexts [
        ⟨82759, false, false, [], []⟩
      ]⟩,
    ⟨[30993], [17025, 30991], .source 15561⟩,
    ⟨[
      94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15
    ], [30993, 94063], .contexts [
        ⟨83032, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨82742, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82743, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82744, false, false, [], [5, 3, 1, 15]⟩,
        ⟨82744, false, false, [], [5, 3, 1, 15]⟩,
        ⟨83033, false, false, [], [3, 1, 15]⟩,
        ⟨82756, false, false, [], [3, 1, 15]⟩,
        ⟨82757, false, false, [], [3, 1, 15]⟩,
        ⟨82757, false, false, [], [3, 1, 15]⟩,
        ⟨82753, false, false, [17025], [1, 15]⟩,
        ⟨83034, true, false, [], [94067, 1, 15]⟩,
        ⟨82741, false, false, [30993], [15]⟩,
        ⟨82720, true, false, [30993], [15]⟩,
        ⟨1, false, false, [30993, 94063], []⟩,
        ⟨82713, false, false, [30993], []⟩
      ]⟩,
    ⟨[30995], [30993, 17033], .source 15562⟩,
    ⟨[
      94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1
    ], [30995, 84345], .contexts [
        ⟨83035, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨82711, false, false, [30993], [1, 11, 9, 1]⟩,
        ⟨82696, false, false, [30993], [11, 9, 1]⟩,
        ⟨83036, true, false, [], [94061, 11, 9, 1]⟩,
        ⟨82688, false, false, [30995], [9, 1]⟩,
        ⟨82663, false, false, [30995], [1]⟩,
        ⟨25909, false, false, [30995], []⟩
      ]⟩,
    ⟨[30997], [30995, 17027], .source 15563⟩,
    ⟨[30999], [30997, 17015], .source 15564⟩,
    ⟨[31001], [30999, 3155], .source 15565⟩,
    ⟨[31003], [31001, 15155], .source 15566⟩,
    ⟨[31005], [31003, 8973], .source 15567⟩,
    ⟨[
      94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [31005, 82821], .contexts [
        ⟨83037, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨26038, false, false, [30995], [3, 1, 15, 13]⟩,
        ⟨83038, true, false, [], [84345, 3, 1, 15, 13]⟩,
        ⟨26020, false, false, [30997], [1, 15, 13]⟩,
        ⟨83039, true, false, [], [80981, 1, 15, 13]⟩,
        ⟨8391, false, false, [30999], [15, 13]⟩,
        ⟨83040, true, false, [], [80791, 15, 13]⟩,
        ⟨14859, false, false, [31001], [13]⟩,
        ⟨83041, true, false, [], [81391, 13]⟩,
        ⟨17082, false, false, [31003], []⟩,
        ⟨83042, true, false, [], [82821]⟩
      ]⟩,
    ⟨[31007], [31005, 2007], .source 15568⟩,
    ⟨[
      94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5
    ], [31007, 79377], .contexts [
        ⟨83043, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨17076, false, false, [31005], [11, 9, 1, 5]⟩,
        ⟨6808, false, false, [31005], [9, 1, 5]⟩,
        ⟨19435, false, false, [31005], [1, 5]⟩,
        ⟨19431, false, false, [31005], [5]⟩,
        ⟨83044, true, false, [], [83165, 5]⟩,
        ⟨19423, false, false, [31007], []⟩
      ]⟩,
    ⟨[31009], [31007, 14721], .source 15569⟩,
    ⟨[31011], [31009, 14715], .source 15570⟩,
    ⟨[31013], [31011, 15431], .source 15571⟩,
    ⟨[31015], [31013, 277], .source 15572⟩,
    ⟨[
      94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [31015, 82767], .contexts [
        ⟨83045, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨14559, false, false, [31007], [1, 15, 13, 1]⟩,
        ⟨83046, true, false, [], [79191, 1, 15, 13, 1]⟩,
        ⟨14552, false, false, [31009], [15, 13, 1]⟩,
        ⟨83047, true, false, [], [81405, 15, 13, 1]⟩,
        ⟨16486, false, false, [31011], [13, 1]⟩,
        ⟨83048, true, false, [], [82775, 13, 1]⟩,
        ⟨16466, false, false, [31013], [1]⟩,
        ⟨16386, false, false, [31013], []⟩,
        ⟨83049, true, false, [], [82767]⟩
      ]⟩,
    ⟨[31017], [31015, 243], .source 15573⟩,
    ⟨[31019], [31017, 277], .source 15574⟩,
    ⟨[31021], [31019, 1469], .source 15575⟩,
    ⟨[
      94177, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3
    ], [31021, 93551], .contexts [
        ⟨83050, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨16435, false, false, [31015], [9, 1, 5, 3]⟩,
        ⟨16452, false, false, [31015], [1, 5, 3]⟩,
        ⟨83051, true, false, [], [82773, 1, 5, 3]⟩,
        ⟨16442, false, false, [31017], [5, 3]⟩,
        ⟨83052, true, false, [], [82773, 5, 3]⟩,
        ⟨16535, false, false, [31019], [3]⟩,
        ⟨83053, true, false, [], [82779, 3]⟩,
        ⟨79925, false, false, [31021], []⟩
      ]⟩,
    ⟨[31023], [31021, 30339], .source 15576⟩,
    ⟨[31023, 86339], [31023, 86339], .contexts []⟩,
    ⟨[31023, 86339], [31023, 86339], .contexts []⟩,
    ⟨[94179, 1], [94179, 1], .contexts []⟩,
    ⟨[94179, 1], [31023, 86339], .contexts [
        ⟨83058, false, false, [], []⟩,
        ⟨82966, true, false, [], [1]⟩,
        ⟨82966, true, false, [], [1]⟩,
        ⟨82963, true, false, [], [1]⟩,
        ⟨3787, false, false, [94177], []⟩,
        ⟨3788, false, false, [94177], []⟩,
        ⟨83054, false, false, [], [1, 15, 13]⟩,
        ⟨79959, false, false, [31021], [15, 13]⟩,
        ⟨79983, false, false, [31021], [13]⟩,
        ⟨83055, true, false, [], [86337, 13]⟩,
        ⟨36599, false, false, [31023], []⟩,
        ⟨83056, false, false, [], []⟩,
        ⟨83057, false, false, [], []⟩,
        ⟨36610, false, false, [31023], []⟩,
        ⟨13, true, false, [], [31023, 86339]⟩
      ]⟩,
    ⟨[31025], [31022], .source 15577⟩,
    ⟨[86339, 1], [31025, 94179], .contexts [
        ⟨83059, true, false, [31022], [1]⟩,
        ⟨8, false, false, [31022, 94179], []⟩,
        ⟨83060, true, false, [], [94179]⟩
      ]⟩,
    ⟨[94179, 1], [31023, 86339], .contexts [
        ⟨83058, false, false, [], []⟩,
        ⟨83059, false, false, [], []⟩,
        ⟨83056, false, false, [], []⟩,
        ⟨83057, false, false, [], []⟩,
        ⟨83057, false, false, [], []⟩
      ]⟩,
    ⟨[31027], [31023, 1739], .source 15578⟩,
    ⟨[31029], [31027, 31025], .source 15579⟩,
    ⟨[94179], [94179], .contexts []⟩,
    ⟨[94179, 5], [94179, 5], .contexts []⟩,
    ⟨[94179], [94179], .contexts []⟩,
    ⟨[31031], [31028], .source 15580⟩,
    ⟨[31031], [31031], .contexts []⟩,
    ⟨[31028], [31028], .contexts []⟩,
    ⟨[31031], [31028], .contexts [
        ⟨83069, false, false, [], []⟩,
        ⟨83068, false, false, [], []⟩,
        ⟨83070, false, false, [], []⟩,
        ⟨83070, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1298. -/
def y322TCIndexRaw1298 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[31033], [31023, 18137], .source 15581⟩,
    ⟨[31035], [31033, 24823], .source 15582⟩,
    ⟨[90353, 7], [90353, 7], .contexts []⟩,
    ⟨[31037], [31034], .source 15583⟩,
    ⟨[31034], [31034], .contexts []⟩,
    ⟨[90353, 7], [31037, 94179], .contexts [
        ⟨83074, false, false, [], []⟩,
        ⟨83073, false, false, [31034], [90353, 7]⟩,
        ⟨60104, true, false, [31034, 31033], [7]⟩,
        ⟨83072, false, false, [31034], [85357, 1, 7]⟩,
        ⟨36620, true, false, [31034, 31023], [1, 7]⟩,
        ⟨83062, true, false, [31034], [7, 1, 7]⟩,
        ⟨4091, false, false, [31034, 94179], []⟩,
        ⟨83065, false, false, [31034], []⟩,
        ⟨83067, false, false, [31034], []⟩,
        ⟨83076, true, false, [], [94179]⟩,
        ⟨83076, true, false, [], [94179]⟩,
        ⟨83075, true, false, [], [94179]⟩
      ]⟩,
    ⟨[31035], [31036], .contexts [
        ⟨83075, true, true, [], []⟩
      ]⟩,
    ⟨[31039], [31023, 27449], .source 15584⟩,
    ⟨[31039, 92823, 13], [94179], .contexts [
        ⟨75626, true, false, [31039], [13]⟩,
        ⟨83079, false, false, [], [92183, 1, 13]⟩,
        ⟨70477, true, false, [31023], [1, 13]⟩,
        ⟨36575, true, false, [31023], [13, 1, 13]⟩,
        ⟨36600, true, false, [31023], [1, 13, 1, 13]⟩,
        ⟨83062, true, false, [], [13, 1, 13, 1, 13]⟩,
        ⟨521, false, false, [94179], []⟩,
        ⟨83065, false, false, [], []⟩
      ]⟩,
    ⟨[31041], [31038], .source 15585⟩,
    ⟨[31038], [31038], .contexts []⟩,
    ⟨[31022], [31022], .contexts []⟩,
    ⟨[31031, 94179], [31031, 94179], .contexts []⟩,
    ⟨[94179, 5], [31031, 94179], .contexts [
        ⟨83066, false, false, [], []⟩,
        ⟨83066, false, false, [], []⟩,
        ⟨83064, false, false, [31028], [94179, 5]⟩,
        ⟨83061, true, false, [31028, 31027], [5]⟩,
        ⟨83063, false, false, [31028], [86339, 1, 5]⟩,
        ⟨36616, true, false, [31028, 31023], [1, 5]⟩,
        ⟨83062, true, false, [31028], [5, 1, 5]⟩,
        ⟨1152, false, false, [31028, 94179], []⟩,
        ⟨83065, false, false, [31028], []⟩,
        ⟨83067, false, false, [31028], []⟩,
        ⟨83071, true, false, [], [94179]⟩,
        ⟨83084, false, false, [], []⟩,
        ⟨83084, false, false, [], []⟩
      ]⟩,
    ⟨[94177, 5], [94177, 5], .contexts []⟩,
    ⟨[94177], [94177], .contexts []⟩,
    ⟨[31030], [31030], .contexts []⟩,
    ⟨[31029], [31030], .contexts [
        ⟨83068, true, true, [], []⟩,
        ⟨83088, false, false, [], []⟩,
        ⟨83088, false, false, [], []⟩
      ]⟩,
    ⟨[31037, 94179], [31037, 94179], .contexts []⟩,
    ⟨[94177, 7], [94177, 7], .contexts []⟩,
    ⟨[31043], [31035, 24825], .source 15586⟩,
    ⟨[94177, 7], [31043, 87025], .contexts [
        ⟨83091, false, false, [], []⟩,
        ⟨82965, true, false, [], [7]⟩,
        ⟨83090, true, false, [31036], [11, 7]⟩,
        ⟨83090, true, false, [31036], [11, 7]⟩,
        ⟨83077, true, false, [31036], [11, 7]⟩,
        ⟨83074, true, false, [31036], [11, 7]⟩,
        ⟨555, false, false, [31036, 90353], []⟩,
        ⟨54, false, false, [31036, 90353], []⟩,
        ⟨60117, false, false, [31036], []⟩,
        ⟨39917, false, false, [31036, 24825], []⟩,
        ⟨83078, true, false, [], [24825, 87025]⟩,
        ⟨83092, true, false, [], [87025]⟩
      ]⟩,
    ⟨[31045], [31042], .source 15587⟩,
    ⟨[31029, 94177], [31029, 94177], .contexts []⟩,
    ⟨[94177, 5, 9], [31029, 94175], .contexts [
        ⟨83086, false, false, [], [9]⟩,
        ⟨83086, false, false, [], [9]⟩,
        ⟨82965, true, false, [], [5, 9]⟩,
        ⟨83085, true, false, [31030], [11, 5, 9]⟩,
        ⟨940, false, false, [31030, 94179], [9]⟩,
        ⟨54, false, false, [31030, 94179], [9]⟩,
        ⟨82965, false, false, [31030], [9]⟩,
        ⟨82964, false, false, [31030], [9]⟩,
        ⟨82964, false, false, [31030], [9]⟩,
        ⟨83087, false, false, [31030], [9]⟩,
        ⟨83089, true, false, [], [94177, 9]⟩,
        ⟨83095, false, false, [], [9]⟩,
        ⟨83095, false, false, [], [9]⟩,
        ⟨82961, false, false, [31029], []⟩
      ]⟩,
    ⟨[94177, 8], [94177, 9], .contexts [
        ⟨47, false, false, [94177], []⟩
      ]⟩,
    ⟨[94175, 5], [94175, 5], .contexts []⟩,
    ⟨[94175], [94175], .contexts []⟩,
    ⟨[31043, 87025], [31043, 87025], .contexts []⟩,
    ⟨[31043, 87025], [31043, 87025], .contexts []⟩,
    ⟨[31047], [31043, 24847], .source 15588⟩,
    ⟨[90347, 7], [90347, 7], .contexts []⟩,
    ⟨[31049], [31046], .source 15589⟩,
    ⟨[31046], [31046], .contexts []⟩,
    ⟨[90347, 7], [31049, 94175], .contexts [
        ⟨83103, false, false, [], []⟩,
        ⟨83102, false, false, [31046], [90347, 7]⟩,
        ⟨60147, false, false, [31046, 31043], [90347, 7]⟩,
        ⟨60145, true, false, [31046, 31043, 24827], [7]⟩,
        ⟨60113, true, false, [31046, 31043], [7]⟩,
        ⟨83101, true, false, [31046], [9, 7]⟩,
        ⟨83101, true, false, [31046], [9, 7]⟩,
        ⟨83100, true, false, [31046], [9, 7]⟩,
        ⟨83093, true, false, [31046], [9, 7]⟩,
        ⟨83091, true, false, [31046], [9, 7]⟩,
        ⟨579, false, false, [31046, 94177], []⟩,
        ⟨83097, false, false, [31046], []⟩,
        ⟨82967, false, false, [31046], []⟩,
        ⟨83099, false, false, [31046], []⟩,
        ⟨83105, true, false, [], [94175]⟩,
        ⟨83105, true, false, [], [94175]⟩,
        ⟨83104, true, false, [], [94175]⟩
      ]⟩,
    ⟨[31031, 94175], [31031, 94175], .contexts []⟩,
    ⟨[31031, 94171], [31031, 94171], .contexts []⟩,
    ⟨[31031, 94171], [31031, 94171], .contexts []⟩,
    ⟨[94175, 5, 1, 5], [31031, 94171], .contexts [
        ⟨83098, false, false, [], [1, 5]⟩,
        ⟨83098, false, false, [], [1, 5]⟩,
        ⟨83096, true, false, [31028], [5, 1, 5]⟩,
        ⟨960, false, false, [31028, 94177], [1, 5]⟩,
        ⟨83097, false, false, [31028], [1, 5]⟩,
        ⟨82967, false, false, [31028], [1, 5]⟩,
        ⟨83099, false, false, [31028], [1, 5]⟩,
        ⟨83071, true, false, [], [94175, 1, 5]⟩,
        ⟨83107, false, false, [], [1, 5]⟩,
        ⟨83107, false, false, [], [1, 5]⟩,
        ⟨82958, false, false, [31031], [5]⟩,
        ⟨82955, false, false, [31031], []⟩,
        ⟨83108, false, false, [], []⟩,
        ⟨83109, false, false, [], []⟩
      ]⟩,
    ⟨[94171, 1], [94171, 1], .contexts []⟩,
    ⟨[94171, 1], [31029, 94175], .contexts [
        ⟨83111, false, false, [], []⟩,
        ⟨83110, true, false, [31030], [1]⟩,
        ⟨874, false, false, [31030, 94175], []⟩,
        ⟨83099, false, false, [31030], []⟩,
        ⟨83089, true, false, [], [94175]⟩
      ]⟩,
    ⟨[31049, 94175], [31049, 94175], .contexts []⟩,
    ⟨[90347, 7], [31049, 94175], .contexts [
        ⟨83103, false, false, [], []⟩,
        ⟨83106, false, false, [], []⟩,
        ⟨83113, false, false, [], []⟩,
        ⟨83113, false, false, [], []⟩
      ]⟩,
    ⟨[31051], [31049, 31031], .source 15590⟩,
    ⟨[94171, 7], [31050, 24843, 90347], .contexts [
        ⟨83115, false, false, [31050], [94171, 7]⟩,
        ⟨83109, true, false, [31050, 31049], [7]⟩,
        ⟨83069, false, false, [31050, 31049], [94171, 7]⟩,
        ⟨83108, true, false, [31050, 31049], [7]⟩,
        ⟨83068, false, false, [31050, 31049], [94171, 7]⟩,
        ⟨8, true, false, [31050, 31049, 31028, 94171], [7]⟩,
        ⟨83112, false, false, [31050, 31049, 31028], [1, 7]⟩,
        ⟨82968, false, false, [31050, 31049], [7]⟩,
        ⟨82969, false, false, [31050, 31049], [7]⟩,
        ⟨82957, false, false, [31050, 31049], [7]⟩,
        ⟨82957, false, false, [31050, 31049], [7]⟩,
        ⟨82958, true, false, [31050, 31049], [7]⟩,
        ⟨83114, true, false, [31050], [1, 7]⟩,
        ⟨502, false, false, [31050, 90347], []⟩,
        ⟨9, false, false, [31050, 90347], []⟩,
        ⟨60162, false, false, [31050], []⟩
      ]⟩,
    ⟨[31053], [31050], .source 15591⟩,
    ⟨[31055], [31053, 24843], .source 15592⟩,
    ⟨[94171, 7], [31055, 90347], .contexts [
        ⟨83116, false, false, [], []⟩,
        ⟨60149, false, false, [31050, 24843], []⟩,
        ⟨83117, true, false, [], [24843, 90347]⟩,
        ⟨83118, true, false, [], [90347]⟩
      ]⟩,
    ⟨[31057], [31054], .source 15593⟩,
    ⟨[31059], [31047, 31057], .source 15594⟩,
    ⟨[94175], [31059, 94171], .contexts [
        ⟨83114, true, false, [31048], []⟩,
        ⟨83119, true, false, [31048, 31054], [7]⟩,
        ⟨38, false, false, [31048, 31054, 94171], []⟩,
        ⟨83120, true, false, [31048], [94171]⟩,
        ⟨83104, false, true, [], [31057, 94171]⟩,
        ⟨83121, true, false, [], [94171]⟩
      ]⟩,
    ⟨[94175], [31059, 94171], .contexts [
        ⟨83122, false, false, [], []⟩
      ]⟩,
    ⟨[31063], [31029, 31059], .source 15596⟩,
    ⟨[94167, 3], [94167, 3], .contexts []⟩,
    ⟨[94167], [94167], .contexts []⟩,
    ⟨[31065], [31062], .source 15597⟩,
    ⟨[31062], [31062], .contexts []⟩,
    ⟨[31065], [31062], .contexts [
        ⟨83127, false, false, [], []⟩,
        ⟨83128, false, false, [], []⟩,
        ⟨83128, false, false, [], []⟩
      ]⟩,
    ⟨[94167, 3], [31065, 94167], .contexts [
        ⟨83125, false, false, [], []⟩,
        ⟨82948, true, false, [], [3]⟩,
        ⟨82952, true, false, [], [1, 3]⟩,
        ⟨83124, false, false, [31062], [94171, 3, 1, 3]⟩,
        ⟨83123, true, false, [31062, 31029], [3, 1, 3]⟩,
        ⟨83112, true, false, [31062], [3, 1, 3]⟩,
        ⟨83111, true, false, [31062], [3, 1, 3]⟩,
        ⟨484, false, false, [31062, 94171], []⟩,
        ⟨485, false, false, [31062, 94171], []⟩,
        ⟨82970, false, false, [31062], [1]⟩,
        ⟨82971, false, false, [31062], [1]⟩,
        ⟨82951, false, false, [31062], [1]⟩,
        ⟨82951, false, false, [31062], [1]⟩,
        ⟨82972, false, false, [31062], []⟩,
        ⟨82973, false, false, [31062], []⟩,
        ⟨82947, false, false, [31062], []⟩,
        ⟨82947, false, false, [31062], []⟩,
        ⟨83126, false, false, [31062], []⟩,
        ⟨83129, true, false, [], [94167]⟩
      ]⟩,
    ⟨[31065, 94167], [31065, 94167], .contexts []⟩,
    ⟨[31065, 94167], [31065, 94167], .contexts []⟩,
    ⟨[94167, 3], [31065, 94167], .contexts [
        ⟨83125, false, false, [], []⟩,
        ⟨83130, false, false, [], []⟩,
        ⟨83131, false, false, [], []⟩,
        ⟨83132, false, false, [], []⟩,
        ⟨83132, false, false, [], []⟩
      ]⟩,
    ⟨[94167, 15], [94165], .contexts [
        ⟨82974, false, false, [], []⟩,
        ⟨82975, false, false, [], []⟩,
        ⟨82943, false, false, [], []⟩,
        ⟨82943, false, false, [], []⟩
      ]⟩,
    ⟨[94167, 14], [94167, 15], .contexts [
        ⟨10, false, false, [94167], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1299. -/
def y322TCIndexRaw1299 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94165, 3], [94165, 3], .contexts []⟩,
    ⟨[94165], [94165], .contexts []⟩,
    ⟨[31064], [31064], .contexts []⟩,
    ⟨[31063, 94165], [31063, 94165], .contexts []⟩,
    ⟨[94165, 3, 13], [31063, 94163], .contexts [
        ⟨83136, false, false, [], [13]⟩,
        ⟨83136, false, false, [], [13]⟩,
        ⟨82944, true, false, [], [3, 13]⟩,
        ⟨83133, true, false, [31064], [15, 3, 13]⟩,
        ⟨499, false, false, [31064, 94167], [13]⟩,
        ⟨83135, false, false, [31064], [13]⟩,
        ⟨83134, false, false, [31064], [13]⟩,
        ⟨83137, false, false, [31064], [13]⟩,
        ⟨83138, true, false, [], [94165, 13]⟩,
        ⟨83138, true, false, [], [94165, 13]⟩,
        ⟨83127, false, true, [], [94165, 13]⟩,
        ⟨83139, false, false, [], [13]⟩,
        ⟨83139, false, false, [], [13]⟩,
        ⟨82941, false, false, [31063], []⟩
      ]⟩,
    ⟨[94165, 13], [94163], .contexts [
        ⟨82977, false, false, [], []⟩,
        ⟨82978, false, false, [], []⟩,
        ⟨82940, false, false, [], []⟩,
        ⟨82940, false, false, [], []⟩
      ]⟩,
    ⟨[94165, 12], [94165, 13], .contexts [
        ⟨64, false, false, [94165], []⟩
      ]⟩,
    ⟨[94163], [94163], .contexts []⟩,
    ⟨[94181], [89105, 1], .source 47155⟩,
    ⟨[89105, 1], [94181], .contexts [
        ⟨83144, true, false, [], []⟩
      ]⟩,
    ⟨[94181], [94181], .contexts []⟩,
    ⟨[89105, 1], [94181], .contexts [
        ⟨83145, false, false, [], []⟩,
        ⟨83146, false, false, [], []⟩,
        ⟨83146, false, false, [], []⟩
      ]⟩,
    ⟨[94181, 5], [94181, 5], .contexts []⟩,
    ⟨[94181, 5], [89109], .contexts [
        ⟨83148, false, false, [], []⟩,
        ⟨83147, true, false, [], [5]⟩,
        ⟨98, false, false, [89105], []⟩,
        ⟨99, false, false, [89105], []⟩,
        ⟨54240, false, false, [], [1]⟩,
        ⟨54273, false, false, [], []⟩,
        ⟨54274, false, false, [], []⟩,
        ⟨54275, false, false, [], []⟩,
        ⟨54275, false, false, [], []⟩,
        ⟨54280, false, false, [], []⟩,
        ⟨672, true, false, [], [89109]⟩
      ]⟩,
    ⟨[89109, 5], [94181], .contexts [
        ⟨83149, true, false, [], [5]⟩,
        ⟨28, false, false, [94181], []⟩,
        ⟨83146, false, false, [], []⟩
      ]⟩,
    ⟨[17017, 84343], [17017, 84343], .contexts []⟩,
    ⟨[17017, 84343], [17017, 84343], .contexts []⟩,
    ⟨[94181, 7], [94181, 7], .contexts []⟩,
    ⟨[94181, 7], [17017, 84343], .contexts [
        ⟨83153, false, false, [], []⟩,
        ⟨83147, true, false, [], [7]⟩,
        ⟨104, false, false, [89105], []⟩,
        ⟨105, false, false, [89105], []⟩,
        ⟨54246, false, false, [], [1]⟩,
        ⟨25911, false, false, [17017], []⟩,
        ⟨83151, false, false, [], []⟩,
        ⟨83152, false, false, [], []⟩,
        ⟨26052, false, false, [17017], []⟩,
        ⟨54208, true, false, [], [84343]⟩
      ]⟩,
    ⟨[15177, 92821], [15177, 92821], .contexts []⟩,
    ⟨[15177, 92821], [15177, 92821], .contexts []⟩,
    ⟨[94181, 11], [94181, 11], .contexts []⟩,
    ⟨[92821], [92821], .contexts []⟩,
    ⟨[94181, 11], [15177, 92821], .contexts [
        ⟨83157, false, false, [], []⟩,
        ⟨83147, true, false, [], [11]⟩,
        ⟨110, false, false, [89105], []⟩,
        ⟨111, false, false, [89105], []⟩,
        ⟨54258, false, false, [], [1]⟩,
        ⟨75600, false, false, [15177], []⟩,
        ⟨83155, false, false, [], []⟩,
        ⟨83156, false, false, [], []⟩,
        ⟨83158, false, false, [15177], []⟩,
        ⟨54222, true, false, [], [92821]⟩
      ]⟩,
    ⟨[92821, 11], [15175, 94181], .contexts [
        ⟨83159, true, false, [15176], [11]⟩,
        ⟨53, false, false, [15176, 94181], []⟩,
        ⟨54224, true, false, [], [94181]⟩
      ]⟩,
    ⟨[94183], [94181, 3], .source 47156⟩,
    ⟨[94181, 3], [94183], .contexts [
        ⟨83161, true, false, [], []⟩
      ]⟩,
    ⟨[94183, 3], [94181], .contexts [
        ⟨83162, true, false, [], [3]⟩,
        ⟨20, false, false, [94181], []⟩,
        ⟨83146, false, false, [], []⟩
      ]⟩,
    ⟨[94183], [94183], .contexts []⟩,
    ⟨[94183], [94183], .contexts []⟩,
    ⟨[94181, 3], [94183], .contexts [
        ⟨83162, false, false, [], []⟩,
        ⟨83164, false, false, [], []⟩,
        ⟨83165, false, false, [], []⟩,
        ⟨83165, false, false, [], []⟩
      ]⟩,
    ⟨[31067], [3155, 12835], .source 15598⟩,
    ⟨[94181, 1, 3, 1, 3], [31067, 92825], .contexts [
        ⟨83145, true, false, [], [1, 3, 1, 3]⟩,
        ⟨8, false, false, [89105], [3, 1, 3]⟩,
        ⟨54203, false, false, [], [3, 1, 3]⟩,
        ⟨54202, false, false, [], [3, 1, 3]⟩,
        ⟨54203, false, false, [], [3, 1, 3]⟩,
        ⟨54203, false, false, [], [3, 1, 3]⟩,
        ⟨54241, false, false, [], [1, 3]⟩,
        ⟨8403, false, false, [], [1, 3]⟩,
        ⟨8404, false, false, [], [1, 3]⟩,
        ⟨8404, false, false, [], [1, 3]⟩,
        ⟨8409, false, false, [], [3]⟩,
        ⟨8406, false, false, [], [3]⟩,
        ⟨8407, false, false, [], [3]⟩,
        ⟨8407, false, false, [], [3]⟩,
        ⟨75644, false, false, [3155], []⟩,
        ⟨83167, true, false, [], [92825]⟩
      ]⟩,
    ⟨[94183, 1], [94183, 1], .contexts []⟩,
    ⟨[31067], [31067], .contexts [
        ⟨13, false, false, [], [31067]⟩
      ]⟩,
    ⟨[94183, 1], [31067, 92825], .contexts [
        ⟨83169, false, false, [], []⟩,
        ⟨83166, true, false, [], [1]⟩,
        ⟨130, false, false, [94181], []⟩,
        ⟨133, false, false, [94181], []⟩,
        ⟨83168, false, false, [], []⟩,
        ⟨75646, false, false, [31067], []⟩,
        ⟨83170, true, false, [], [92825]⟩
      ]⟩,
    ⟨[31069], [31066], .source 15599⟩,
    ⟨[2375, 94183], [2375, 94183], .contexts []⟩,
    ⟨[94183], [94183], .contexts []⟩,
    ⟨[94183, 5], [2375, 94183], .contexts [
        ⟨83166, true, false, [], [5]⟩,
        ⟨871, false, false, [94181], []⟩,
        ⟨873, false, false, [94181], []⟩,
        ⟨83148, false, false, [], [3, 5, 3]⟩,
        ⟨83149, false, false, [], [3, 5, 3]⟩,
        ⟨54274, false, false, [], [3, 5, 3]⟩,
        ⟨54275, false, false, [], [3, 5, 3]⟩,
        ⟨54275, false, false, [], [3, 5, 3]⟩,
        ⟨54302, false, false, [], [5, 3]⟩,
        ⟨54277, false, false, [], [5, 3]⟩,
        ⟨54278, false, false, [], [5, 3]⟩,
        ⟨54278, false, false, [], [5, 3]⟩,
        ⟨83150, false, false, [2375], [3]⟩,
        ⟨83162, false, false, [2375], []⟩,
        ⟨83173, false, false, [], []⟩,
        ⟨83174, false, false, [2375], []⟩
      ]⟩,
    ⟨[31071], [17017, 18079], .source 15600⟩,
    ⟨[94183, 7], [94183, 7], .contexts []⟩,
    ⟨[94183, 7], [31071, 85321], .contexts [
        ⟨83177, false, false, [], []⟩,
        ⟨83166, true, false, [], [7]⟩,
        ⟨140, false, false, [94181], []⟩,
        ⟨141, false, false, [94181], []⟩,
        ⟨83153, false, false, [], [3]⟩,
        ⟨83154, false, false, [], [3]⟩,
        ⟨83151, false, false, [], [3]⟩,
        ⟨83152, false, false, [], [3]⟩,
        ⟨83152, false, false, [], [3]⟩,
        ⟨31205, false, false, [17017], []⟩,
        ⟨83176, true, false, [], [85321]⟩,
        ⟨42144, false, false, [31071], []⟩,
        ⟨13, true, false, [], [31071, 85321]⟩
      ]⟩,
    ⟨[31073], [31070], .source 15601⟩,
    ⟨[94183, 11], [15177, 92823], .contexts [
        ⟨83166, true, false, [], [11]⟩,
        ⟨144, false, false, [94181], []⟩,
        ⟨145, false, false, [94181], []⟩,
        ⟨83157, false, false, [], [3]⟩,
        ⟨83159, false, false, [], [3]⟩,
        ⟨83155, false, false, [], [3]⟩,
        ⟨83156, false, false, [], [3]⟩,
        ⟨83156, false, false, [], [3]⟩,
        ⟨75619, false, false, [15177], []⟩,
        ⟨54222, true, false, [], [92823]⟩
      ]⟩,
    ⟨[31067, 92825], [31067, 92825], .contexts []⟩,
    ⟨[31067, 92825], [31067, 92825], .contexts []⟩,
    ⟨[94183, 1], [31067, 92825], .contexts [
        ⟨83169, false, false, [], []⟩,
        ⟨83171, false, false, [], []⟩,
        ⟨83181, false, false, [], []⟩,
        ⟨83182, false, false, [], []⟩,
        ⟨83182, false, false, [], []⟩
      ]⟩,
    ⟨[31067, 93283], [31067, 93283], .contexts []⟩,
    ⟨[31067, 93283], [31067, 93283], .contexts []⟩,
    ⟨[94183], [94183], .contexts []⟩,
    ⟨[93283, 15], [93283, 15], .contexts []⟩,
    ⟨[31069], [31066], .contexts [
        ⟨83172, false, false, [], []⟩
      ]⟩,
    ⟨[31066], [31066], .contexts []⟩,
    ⟨[93283, 15], [31069, 94183], .contexts [
        ⟨83187, false, false, [], []⟩,
        ⟨83185, true, false, [31066], [15]⟩,
        ⟨83184, true, false, [31066], [15]⟩,
        ⟨78459, true, false, [], [15]⟩,
        ⟨75656, true, false, [], [1, 15]⟩,
        ⟨83183, true, false, [31066], [15, 1, 15]⟩,
        ⟨2185, false, false, [31066, 94183], []⟩,
        ⟨83186, false, false, [31066], []⟩,
        ⟨83174, false, false, [31066], []⟩,
        ⟨83189, true, false, [], [94183]⟩,
        ⟨83189, true, false, [], [94183]⟩,
        ⟨83188, true, false, [], [94183]⟩
      ]⟩,
    ⟨[94183, 15], [31067, 93283], .contexts [
        ⟨83190, true, false, [31068], [15]⟩,
        ⟨1, false, false, [31068, 93283], []⟩,
        ⟨83172, false, true, [], [93283]⟩
      ]⟩,
    ⟨[31071, 85321], [31071, 85321], .contexts []⟩,
    ⟨[31071, 85321], [31071, 85321], .contexts []⟩,
    ⟨[94183, 7], [31071, 85321], .contexts [
        ⟨83177, false, false, [], []⟩,
        ⟨83178, false, false, [], []⟩,
        ⟨83192, false, false, [], []⟩,
        ⟨83193, false, false, [], []⟩,
        ⟨83193, false, false, [], []⟩
      ]⟩,
    ⟨[31075], [31071, 19647], .source 15602⟩,
    ⟨[31077], [31075, 31045], .source 15603⟩,
    ⟨[31079], [31076], .source 15604⟩,
    ⟨[31076], [31076], .contexts []⟩,
    ⟨[94183, 13], [31077, 94177], .contexts [
        ⟨83197, false, false, [31078], [94183, 13]⟩,
        ⟨83198, false, false, [31078], [94183, 13]⟩,
        ⟨83198, false, false, [31078], [94183, 13]⟩,
        ⟨83174, true, false, [31078, 31076], [13]⟩,
        ⟨83186, true, false, [31078, 31076], [13]⟩,
        ⟨15654, true, false, [31078, 31076, 94183], [13]⟩,
        ⟨83194, false, false, [31078, 31076], [13, 7, 13, 13]⟩,
        ⟨39897, false, false, [31078, 31076, 31071], [7, 13, 13]⟩,
        ⟨83195, true, false, [31078, 31076], [87025, 7, 13, 13]⟩,
        ⟨83093, true, false, [31078, 31076, 31075, 31042], [7, 13, 13]⟩,
        ⟨38, false, false, [31078, 31076, 31075, 31042, 94177], [13, 13]⟩,
        ⟨83094, true, false, [31078, 31076, 31075], [94177, 13, 13]⟩,
        ⟨83196, true, false, [31078, 31076], [94177, 13, 13]⟩,
        ⟨59, false, false, [31078, 94177], []⟩,
        ⟨83197, false, true, [], [94177]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1300. -/
def y322TCIndexRaw1300 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94185], [92179, 9], .source 47157⟩,
    ⟨[92179, 9], [94185], .contexts [
        ⟨83200, true, false, [], []⟩
      ]⟩,
    ⟨[94185, 9], [92179], .contexts [
        ⟨83201, true, false, [], [9]⟩,
        ⟨46, false, false, [92179], []⟩,
        ⟨70396, false, false, [], []⟩
      ]⟩,
    ⟨[94185], [94185], .contexts []⟩,
    ⟨[94185], [94185], .contexts []⟩,
    ⟨[92179, 9], [94185], .contexts [
        ⟨83201, false, false, [], []⟩,
        ⟨83203, false, false, [], []⟩,
        ⟨83204, false, false, [], []⟩,
        ⟨83204, false, false, [], []⟩
      ]⟩,
    ⟨[31081], [9191, 2009], .source 15605⟩,
    ⟨[31083], [31081, 9189], .source 15606⟩,
    ⟨[31083, 94185], [31083, 94185], .contexts []⟩,
    ⟨[31083, 94185], [31083, 94185], .contexts []⟩,
    ⟨[31083, 94185], [31083, 94185], .contexts []⟩,
    ⟨[94185, 1], [94185, 1], .contexts []⟩,
    ⟨[94185, 1], [31083, 94185], .contexts [
        ⟨83211, false, false, [], []⟩,
        ⟨83205, true, false, [], [1]⟩,
        ⟨691, false, false, [92179], []⟩,
        ⟨694, false, false, [92179], []⟩,
        ⟨70403, false, false, [], [9, 1, 9]⟩,
        ⟨70408, false, false, [], [9, 1, 9]⟩,
        ⟨70401, false, false, [], [9, 1, 9]⟩,
        ⟨70402, false, false, [], [9, 1, 9]⟩,
        ⟨70402, false, false, [], [9, 1, 9]⟩,
        ⟨67795, false, false, [9191], [1, 9]⟩,
        ⟨83206, true, false, [], [91833, 1, 9]⟩,
        ⟨70409, false, false, [31081], [9]⟩,
        ⟨83207, true, false, [], [92179, 9]⟩,
        ⟨83201, false, false, [31083], []⟩,
        ⟨83208, false, false, [], []⟩,
        ⟨83209, false, false, [], []⟩,
        ⟨83210, false, false, [], []⟩
      ]⟩,
    ⟨[31083], [31083], .contexts [
        ⟨13, false, false, [], [31083]⟩
      ]⟩,
    ⟨[94185, 3], [94185, 3], .contexts []⟩,
    ⟨[94185, 3], [93811], .contexts [
        ⟨83214, false, false, [], []⟩,
        ⟨83205, true, false, [], [3]⟩,
        ⟨196, false, false, [92179], []⟩,
        ⟨197, false, false, [92179], []⟩,
        ⟨70394, true, false, [], [3, 9]⟩,
        ⟨20, false, false, [92177], [9]⟩,
        ⟨70381, false, false, [], [9]⟩,
        ⟨70380, false, false, [], [9]⟩,
        ⟨70381, false, false, [], [9]⟩,
        ⟨70381, false, false, [], [9]⟩,
        ⟨81463, false, false, [], []⟩,
        ⟨81464, false, false, [], []⟩,
        ⟨81465, false, false, [], []⟩,
        ⟨81465, false, false, [], []⟩,
        ⟨672, true, false, [], [93811]⟩
      ]⟩,
    ⟨[94185, 7], [94185, 7], .contexts []⟩,
    ⟨[94185, 7], [16867, 83801], .contexts [
        ⟨83216, false, false, [], []⟩,
        ⟨83205, true, false, [], [7]⟩,
        ⟨1084, false, false, [92179], []⟩,
        ⟨1085, false, false, [92179], []⟩,
        ⟨70410, false, false, [], [9]⟩,
        ⟨70411, false, false, [], [9]⟩,
        ⟨24813, false, false, [], [9]⟩,
        ⟨24814, false, false, [], [9]⟩,
        ⟨24814, false, false, [], [9]⟩,
        ⟨24838, false, false, [], []⟩,
        ⟨24839, false, false, [], []⟩,
        ⟨24840, false, false, [], []⟩,
        ⟨24841, false, false, [], []⟩,
        ⟨24843, false, false, [], []⟩,
        ⟨24844, false, false, [], []⟩
      ]⟩,
    ⟨[27427, 86319], [27427, 86319], .contexts []⟩,
    ⟨[27427, 86319], [27427, 86319], .contexts []⟩,
    ⟨[27427, 86317], [27427, 86317], .contexts []⟩,
    ⟨[27427, 86317], [27427, 86317], .contexts []⟩,
    ⟨[27427, 86317], [27427, 86317], .contexts [
        ⟨36493, false, false, [27427], []⟩
      ]⟩,
    ⟨[27427, 86317], [27427, 86317], .contexts [
        ⟨70418, true, false, [], [86317]⟩
      ]⟩,
    ⟨[94185, 13], [27427, 86317], .contexts [
        ⟨83205, true, false, [], [13]⟩,
        ⟨201, false, false, [92179], []⟩,
        ⟨202, false, false, [92179], []⟩,
        ⟨70417, false, false, [], [9]⟩,
        ⟨70419, false, false, [], [9]⟩,
        ⟨83218, false, false, [], [9]⟩,
        ⟨83219, false, false, [], [9]⟩,
        ⟨83219, false, false, [], [9]⟩,
        ⟨36319, false, false, [27427], []⟩,
        ⟨83220, false, false, [], []⟩,
        ⟨83221, false, false, [], []⟩,
        ⟨83222, false, false, [], []⟩,
        ⟨83223, false, false, [], []⟩
      ]⟩,
    ⟨[15173, 92823], [15173, 92823], .contexts []⟩,
    ⟨[15173, 92963], [15173, 92963], .contexts []⟩,
    ⟨[15173, 92963], [15173, 92963], .contexts []⟩,
    ⟨[94185, 15], [94185, 15], .contexts []⟩,
    ⟨[94187], [94185, 11], .source 47158⟩,
    ⟨[94185, 11], [94187], .contexts [
        ⟨83229, true, false, [], []⟩
      ]⟩,
    ⟨[94187, 11], [94185], .contexts [
        ⟨83230, true, false, [], [11]⟩,
        ⟨53, false, false, [94185], []⟩,
        ⟨83204, false, false, [], []⟩
      ]⟩,
    ⟨[94187], [94187], .contexts []⟩,
    ⟨[94187], [94187], .contexts []⟩,
    ⟨[94185, 11], [94187], .contexts [
        ⟨83230, false, false, [], []⟩,
        ⟨83232, false, false, [], []⟩,
        ⟨83233, false, false, [], []⟩,
        ⟨83233, false, false, [], []⟩
      ]⟩,
    ⟨[31083, 94187], [31083, 94187], .contexts []⟩,
    ⟨[31083, 94187], [31083, 94187], .contexts []⟩,
    ⟨[93813], [93813], .contexts []⟩,
    ⟨[94187, 3], [93813], .contexts [
        ⟨83234, true, false, [], [3]⟩,
        ⟨215, false, false, [94185], []⟩,
        ⟨216, false, false, [94185], []⟩,
        ⟨83214, false, false, [], [11]⟩,
        ⟨83215, false, false, [], [11]⟩,
        ⟨81464, false, false, [], [11]⟩,
        ⟨81465, false, false, [], [11]⟩,
        ⟨81465, false, false, [], [11]⟩,
        ⟨81478, false, false, [], []⟩,
        ⟨81479, false, false, [], []⟩,
        ⟨81480, false, false, [], []⟩,
        ⟨81480, false, false, [], []⟩,
        ⟨83237, false, false, [], []⟩,
        ⟨672, true, false, [], [93813]⟩
      ]⟩,
    ⟨[93813, 3], [94187], .contexts [
        ⟨83238, true, false, [], [3]⟩,
        ⟨20, false, false, [94187], []⟩,
        ⟨83233, false, false, [], []⟩
      ]⟩,
    ⟨[94187, 7], [94187, 7], .contexts []⟩,
    ⟨[94187, 7], [16867, 83803], .contexts [
        ⟨83240, false, false, [], []⟩,
        ⟨83234, true, false, [], [7]⟩,
        ⟨647, false, false, [94185], []⟩,
        ⟨648, false, false, [94185], []⟩,
        ⟨83216, false, false, [], [11]⟩,
        ⟨83217, false, false, [], [11]⟩,
        ⟨24839, false, false, [], [11]⟩,
        ⟨24841, false, false, [], [11]⟩,
        ⟨24841, false, false, [], [11]⟩,
        ⟨24859, false, false, [], []⟩,
        ⟨24860, false, false, [], []⟩,
        ⟨24861, false, false, [], []⟩,
        ⟨24862, false, false, [], []⟩,
        ⟨24864, false, false, [], []⟩,
        ⟨24865, false, false, [], []⟩
      ]⟩,
    ⟨[9191, 93283], [9191, 93283], .contexts []⟩,
    ⟨[94187, 9], [9191, 93287], .contexts [
        ⟨83234, true, false, [], [9]⟩,
        ⟨221, false, false, [94185], []⟩,
        ⟨224, false, false, [94185], []⟩,
        ⟨83202, false, false, [], [11, 9, 11]⟩,
        ⟨70395, false, false, [], [11, 9, 11]⟩,
        ⟨70396, false, false, [], [11, 9, 11]⟩,
        ⟨70396, false, false, [], [11, 9, 11]⟩,
        ⟨78475, false, false, [], [9, 11]⟩,
        ⟨83242, false, false, [], [9, 11]⟩,
        ⟨83242, false, false, [], [9, 11]⟩,
        ⟨78486, false, false, [9191], [11]⟩,
        ⟨78508, false, false, [9191], []⟩,
        ⟨78516, false, false, [9191], []⟩
      ]⟩,
    ⟨[93287, 9], [9189, 94187], .contexts [
        ⟨70407, false, false, [9190], [93287, 9]⟩,
        ⟨83243, true, false, [9190], [9]⟩,
        ⟨46, false, false, [9190, 94187], []⟩,
        ⟨11994, true, false, [], [94187]⟩
      ]⟩,
    ⟨[94185, 15], [15173, 92963], .contexts [
        ⟨83228, false, false, [], []⟩,
        ⟨83228, false, false, [], []⟩,
        ⟨83205, true, false, [], [15]⟩,
        ⟨205, false, false, [92179], []⟩,
        ⟨206, false, false, [92179], []⟩,
        ⟨75634, true, false, [15170], [15, 9]⟩,
        ⟨1, false, false, [15170, 92823], [9]⟩,
        ⟨14897, true, false, [], [92823, 9]⟩,
        ⟨83225, false, false, [], [9]⟩,
        ⟨83225, false, false, [], [9]⟩,
        ⟨76434, false, false, [15173], []⟩,
        ⟨83226, false, false, [], []⟩,
        ⟨83227, false, false, [], []⟩,
        ⟨76447, false, false, [15173], []⟩,
        ⟨70372, true, false, [], [92963]⟩,
        ⟨83226, false, false, [], []⟩,
        ⟨83227, false, false, [], []⟩
      ]⟩,
    ⟨[15173, 92965], [15173, 92965], .contexts []⟩,
    ⟨[15173, 92965], [15173, 92965], .contexts []⟩,
    ⟨[94189], [94187, 13], .source 47159⟩,
    ⟨[94187, 13], [94189], .contexts [
        ⟨83248, true, false, [], []⟩
      ]⟩,
    ⟨[94189], [94189], .contexts []⟩,
    ⟨[94189], [94189], .contexts []⟩,
    ⟨[94187, 13], [94189], .contexts [
        ⟨83249, false, false, [], []⟩,
        ⟨83250, false, false, [], []⟩,
        ⟨83251, false, false, [], []⟩,
        ⟨83251, false, false, [], []⟩
      ]⟩,
    ⟨[94189, 7], [94189, 7], .contexts []⟩,
    ⟨[94189, 7], [16867, 83805], .contexts [
        ⟨83253, false, false, [], []⟩,
        ⟨83252, true, false, [], [7]⟩,
        ⟨73, false, false, [94187], []⟩,
        ⟨74, false, false, [94187], []⟩,
        ⟨83240, false, false, [], [13]⟩,
        ⟨83241, false, false, [], [13]⟩,
        ⟨24860, false, false, [], [13]⟩,
        ⟨24862, false, false, [], [13]⟩,
        ⟨24862, false, false, [], [13]⟩,
        ⟨73273, false, false, [], []⟩,
        ⟨73274, false, false, [], []⟩,
        ⟨73275, false, false, [], []⟩,
        ⟨73276, false, false, [], []⟩,
        ⟨73278, false, false, [], []⟩,
        ⟨73279, false, false, [], []⟩
      ]⟩,
    ⟨[94191], [94189, 15], .source 47160⟩,
    ⟨[94189, 15], [94191], .contexts [
        ⟨83255, true, false, [], []⟩
      ]⟩,
    ⟨[94191], [94191], .contexts []⟩,
    ⟨[94191], [94191], .contexts []⟩,
    ⟨[94189, 15], [94191], .contexts [
        ⟨83256, false, false, [], []⟩,
        ⟨83257, false, false, [], []⟩,
        ⟨83258, false, false, [], []⟩,
        ⟨83258, false, false, [], []⟩
      ]⟩,
    ⟨[94191, 7], [94191, 7], .contexts []⟩,
    ⟨[94191, 7], [16867, 83807], .contexts [
        ⟨83260, false, false, [], []⟩,
        ⟨83259, true, false, [], [7]⟩,
        ⟨37, false, false, [94189], []⟩,
        ⟨40, false, false, [94189], []⟩,
        ⟨83253, false, false, [], [15]⟩,
        ⟨83254, false, false, [], [15]⟩,
        ⟨73274, false, false, [], [15]⟩,
        ⟨73276, false, false, [], [15]⟩,
        ⟨73276, false, false, [], [15]⟩,
        ⟨73302, false, false, [], []⟩,
        ⟨73303, false, false, [], []⟩,
        ⟨73304, false, false, [], []⟩,
        ⟨73305, false, false, [], []⟩,
        ⟨73306, false, false, [], []⟩,
        ⟨73307, false, false, [], []⟩
      ]⟩,
    ⟨[94189, 13], [94187], .contexts [
        ⟨83249, true, false, [], [13]⟩,
        ⟨59, false, false, [94187], []⟩,
        ⟨83233, false, false, [], []⟩
      ]⟩,
    ⟨[15173, 92969], [15173, 92969], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1301. -/
def y322TCIndexRaw1301 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94189, 13, 15, 13, 15], [15173, 92969], .contexts [
        ⟨83262, false, false, [], [15, 13, 15]⟩,
        ⟨83232, false, false, [], [15, 13, 15]⟩,
        ⟨83233, false, false, [], [15, 13, 15]⟩,
        ⟨83233, false, false, [], [15, 13, 15]⟩,
        ⟨83234, true, false, [], [15, 13, 15]⟩,
        ⟨231, false, false, [94185], [13, 15]⟩,
        ⟨232, false, false, [94185], [13, 15]⟩,
        ⟨83245, false, false, [], [11, 13, 15]⟩,
        ⟨83227, false, false, [], [11, 13, 15]⟩,
        ⟨76453, false, false, [15173], [13, 15]⟩,
        ⟨83246, false, false, [], [13, 15]⟩,
        ⟨83247, false, false, [], [13, 15]⟩,
        ⟨76461, false, false, [15173], [13, 15]⟩,
        ⟨70372, true, false, [], [92965, 13, 15]⟩,
        ⟨83246, false, false, [], [13, 15]⟩,
        ⟨83247, false, false, [], [13, 15]⟩,
        ⟨83247, false, false, [], [13, 15]⟩,
        ⟨76468, false, false, [15173], [15]⟩,
        ⟨76482, false, false, [15173], []⟩,
        ⟨83263, false, false, [], []⟩
      ]⟩,
    ⟨[94191, 13], [15173, 92969], .contexts [
        ⟨83259, true, false, [], [13]⟩,
        ⟨259, false, false, [94189], []⟩,
        ⟨262, false, false, [94189], []⟩,
        ⟨83264, false, false, [], []⟩,
        ⟨76486, false, false, [15173], []⟩,
        ⟨70372, true, false, [], [92969]⟩
      ]⟩,
    ⟨[94191, 7], [16867, 83807], .contexts [
        ⟨83260, false, false, [], []⟩,
        ⟨83261, false, false, [], []⟩,
        ⟨73303, false, false, [], []⟩,
        ⟨73305, false, false, [], []⟩,
        ⟨73305, false, false, [], []⟩
      ]⟩,
    ⟨[31085], [16867, 20945], .source 15607⟩,
    ⟨[31087], [31085, 29711], .source 15608⟩,
    ⟨[31089], [31086], .source 15609⟩,
    ⟨[31086], [31086], .contexts []⟩,
    ⟨[93191, 9], [31089, 94191], .contexts [
        ⟨83268, false, false, [31086], [93191, 9]⟩,
        ⟨77910, true, false, [31086, 31085], [9]⟩,
        ⟨83267, false, false, [31086], [83237, 7, 9]⟩,
        ⟨43430, true, false, [31086, 16867], [7, 9]⟩,
        ⟨83266, true, false, [31086], [9, 7, 9]⟩,
        ⟨50640, false, false, [31086, 94191], []⟩,
        ⟨83270, true, false, [], [94191]⟩,
        ⟨83270, true, false, [], [94191]⟩,
        ⟨83269, true, false, [], [94191]⟩
      ]⟩,
    ⟨[94191, 9], [31087, 93191], .contexts [
        ⟨83271, true, false, [31088], [9]⟩,
        ⟨46, false, false, [31088, 93191], []⟩,
        ⟨83269, false, true, [], [93191]⟩
      ]⟩,
    ⟨[94193], [94191, 1], .source 47161⟩,
    ⟨[94191, 1], [94193], .contexts [
        ⟨83273, true, false, [], []⟩
      ]⟩,
    ⟨[94193], [94193], .contexts []⟩,
    ⟨[94193], [94193], .contexts []⟩,
    ⟨[94193, 7], [94193, 7], .contexts []⟩,
    ⟨[94193, 7], [16867, 83809], .contexts [
        ⟨83277, false, false, [], []⟩,
        ⟨83276, true, false, [], [7]⟩,
        ⟨83276, true, false, [], [7]⟩,
        ⟨83275, true, false, [], [7]⟩,
        ⟨83274, true, false, [], [7]⟩,
        ⟨104, false, false, [94191], []⟩,
        ⟨105, false, false, [94191], []⟩,
        ⟨83266, false, false, [], [1]⟩,
        ⟨73328, false, false, [], []⟩,
        ⟨73329, false, false, [], []⟩,
        ⟨73330, false, false, [], []⟩,
        ⟨73331, false, false, [], []⟩,
        ⟨72132, false, false, [16867], []⟩,
        ⟨24818, true, false, [], [83809]⟩
      ]⟩,
    ⟨[94195], [94193, 3], .source 47162⟩,
    ⟨[94193, 3], [94195], .contexts [
        ⟨83279, true, false, [], []⟩
      ]⟩,
    ⟨[94195], [94195], .contexts []⟩,
    ⟨[94195], [94195], .contexts []⟩,
    ⟨[94197], [94195, 5], .source 47163⟩,
    ⟨[94195, 5], [94197], .contexts [
        ⟨83283, true, false, [], []⟩
      ]⟩,
    ⟨[94197], [94197], .contexts []⟩,
    ⟨[94197], [94197], .contexts []⟩,
    ⟨[94199], [94197, 1], .source 47164⟩,
    ⟨[94197, 1], [94199], .contexts [
        ⟨83287, true, false, [], []⟩
      ]⟩,
    ⟨[94201], [94199, 9], .source 47165⟩,
    ⟨[94199, 9], [94201], .contexts [
        ⟨83289, true, false, [], []⟩
      ]⟩,
    ⟨[94199], [94199], .contexts []⟩,
    ⟨[94203], [94201, 11], .source 47166⟩,
    ⟨[94201, 11], [94203], .contexts [
        ⟨83292, true, false, [], []⟩
      ]⟩,
    ⟨[94201], [94201], .contexts []⟩,
    ⟨[94205], [94203, 1], .source 47167⟩,
    ⟨[94203, 1], [94205], .contexts [
        ⟨83295, true, false, [], []⟩
      ]⟩,
    ⟨[94203], [94203], .contexts []⟩,
    ⟨[94205, 1], [94203], .contexts [
        ⟨83296, true, false, [], [1]⟩,
        ⟨8, false, false, [94203], []⟩,
        ⟨83297, false, false, [], []⟩
      ]⟩,
    ⟨[94207], [94205, 13], .source 47168⟩,
    ⟨[94205, 13], [94207], .contexts [
        ⟨83299, true, false, [], []⟩
      ]⟩,
    ⟨[94205], [94205], .contexts []⟩,
    ⟨[94209], [94207, 15], .source 47169⟩,
    ⟨[94207, 15], [94209], .contexts [
        ⟨83302, true, false, [], []⟩
      ]⟩,
    ⟨[94207], [94207], .contexts []⟩,
    ⟨[94209, 15], [94207], .contexts [
        ⟨83303, true, false, [], [15]⟩,
        ⟨1, false, false, [94207], []⟩,
        ⟨83304, false, false, [], []⟩
      ]⟩,
    ⟨[94211], [94209, 1], .source 47170⟩,
    ⟨[94209, 1], [94211], .contexts [
        ⟨83306, true, false, [], []⟩
      ]⟩,
    ⟨[94209], [94209], .contexts []⟩,
    ⟨[94211, 1], [94209], .contexts [
        ⟨83307, true, false, [], [1]⟩,
        ⟨8, false, false, [94209], []⟩,
        ⟨83308, false, false, [], []⟩
      ]⟩,
    ⟨[94213], [94211, 3], .source 47171⟩,
    ⟨[94211, 3], [94213], .contexts [
        ⟨83310, true, false, [], []⟩
      ]⟩,
    ⟨[94211], [94211], .contexts []⟩,
    ⟨[94215], [94213, 5], .source 47172⟩,
    ⟨[94213, 5], [94215], .contexts [
        ⟨83313, true, false, [], []⟩
      ]⟩,
    ⟨[94213], [94213], .contexts []⟩,
    ⟨[94215, 5], [94213], .contexts [
        ⟨83314, true, false, [], [5]⟩,
        ⟨28, false, false, [94213], []⟩,
        ⟨83315, false, false, [], []⟩
      ]⟩,
    ⟨[94217], [94215, 1], .source 47173⟩,
    ⟨[94215, 1], [94217], .contexts [
        ⟨83317, true, false, [], []⟩
      ]⟩,
    ⟨[94215], [94215], .contexts []⟩,
    ⟨[94219], [94217, 9], .source 47174⟩,
    ⟨[94217, 9], [94219], .contexts [
        ⟨83320, true, false, [], []⟩
      ]⟩,
    ⟨[94217], [94217], .contexts []⟩,
    ⟨[94221], [94219, 11], .source 47175⟩,
    ⟨[94219, 11], [94221], .contexts [
        ⟨83323, true, false, [], []⟩
      ]⟩,
    ⟨[94219], [94219], .contexts []⟩,
    ⟨[94221, 11], [94219], .contexts [
        ⟨83324, true, false, [], [11]⟩,
        ⟨53, false, false, [94219], []⟩,
        ⟨83325, false, false, [], []⟩
      ]⟩,
    ⟨[94223], [94221, 1], .source 47176⟩]

/-- Exact literal claimed equations and contextual derivations, block 1302. -/
def y322TCIndexRaw1302 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94221, 1], [94223], .contexts [
        ⟨83327, true, false, [], []⟩
      ]⟩,
    ⟨[94221], [94221], .contexts []⟩,
    ⟨[94225], [94223, 13], .source 47177⟩,
    ⟨[94223, 13], [94225], .contexts [
        ⟨83330, true, false, [], []⟩
      ]⟩,
    ⟨[94223], [94223], .contexts []⟩,
    ⟨[94227], [94225, 15], .source 47178⟩,
    ⟨[94225, 15], [94227], .contexts [
        ⟨83333, true, false, [], []⟩
      ]⟩,
    ⟨[94225], [94225], .contexts []⟩,
    ⟨[94227, 15], [94225], .contexts [
        ⟨83334, true, false, [], [15]⟩,
        ⟨1, false, false, [94225], []⟩,
        ⟨83335, false, false, [], []⟩
      ]⟩,
    ⟨[94229], [94227, 1], .source 47179⟩,
    ⟨[94227, 1], [94229], .contexts [
        ⟨83337, true, false, [], []⟩
      ]⟩,
    ⟨[94227], [94227], .contexts []⟩,
    ⟨[94231], [94229, 3], .source 47180⟩,
    ⟨[94229, 3], [94231], .contexts [
        ⟨83340, true, false, [], []⟩
      ]⟩,
    ⟨[94229], [94229], .contexts []⟩,
    ⟨[94233], [94231, 5], .source 47181⟩,
    ⟨[94231, 5], [94233], .contexts [
        ⟨83343, true, false, [], []⟩
      ]⟩,
    ⟨[94231], [94231], .contexts []⟩,
    ⟨[94235], [94233, 1], .source 47182⟩,
    ⟨[94233, 1], [94235], .contexts [
        ⟨83346, true, false, [], []⟩
      ]⟩,
    ⟨[94233], [94233], .contexts []⟩,
    ⟨[94235, 1], [94233], .contexts [
        ⟨83347, true, false, [], [1]⟩,
        ⟨8, false, false, [94233], []⟩,
        ⟨83348, false, false, [], []⟩
      ]⟩,
    ⟨[94237], [94235, 9], .source 47183⟩,
    ⟨[94235, 9], [94237], .contexts [
        ⟨83350, true, false, [], []⟩
      ]⟩,
    ⟨[94235], [94235], .contexts []⟩,
    ⟨[94237, 9], [94235], .contexts [
        ⟨83351, true, false, [], [9]⟩,
        ⟨46, false, false, [94235], []⟩,
        ⟨83352, false, false, [], []⟩
      ]⟩,
    ⟨[94239], [94237, 11], .source 47184⟩,
    ⟨[94237, 11], [94239], .contexts [
        ⟨83354, true, false, [], []⟩
      ]⟩,
    ⟨[94237], [94237], .contexts []⟩,
    ⟨[94239, 11], [94237], .contexts [
        ⟨83355, true, false, [], [11]⟩,
        ⟨53, false, false, [94237], []⟩,
        ⟨83356, false, false, [], []⟩
      ]⟩,
    ⟨[94241], [94239, 1], .source 47185⟩,
    ⟨[94239], [94239], .contexts []⟩,
    ⟨[94241, 1], [94239], .contexts [
        ⟨83358, false, false, [], [1]⟩,
        ⟨8, false, false, [94239], []⟩,
        ⟨83359, false, false, [], []⟩
      ]⟩,
    ⟨[94243], [94241, 13], .source 47186⟩,
    ⟨[94241], [94241], .contexts []⟩,
    ⟨[94243, 13], [94241], .contexts [
        ⟨83361, false, false, [], [13]⟩,
        ⟨59, false, false, [94241], []⟩,
        ⟨83362, false, false, [], []⟩
      ]⟩,
    ⟨[94245], [94243, 15], .source 47187⟩,
    ⟨[94243], [94243], .contexts []⟩,
    ⟨[94245, 15], [94243], .contexts [
        ⟨83364, false, false, [], [15]⟩,
        ⟨1, false, false, [94243], []⟩,
        ⟨83365, false, false, [], []⟩
      ]⟩,
    ⟨[94247], [94245, 1], .source 47188⟩,
    ⟨[94245], [94245], .contexts []⟩,
    ⟨[94247, 1], [94245], .contexts [
        ⟨83367, false, false, [], [1]⟩,
        ⟨8, false, false, [94245], []⟩,
        ⟨83368, false, false, [], []⟩
      ]⟩,
    ⟨[94249], [94247, 3], .source 47189⟩,
    ⟨[94247], [94247], .contexts []⟩,
    ⟨[94249, 3], [94247], .contexts [
        ⟨83370, false, false, [], [3]⟩,
        ⟨20, false, false, [94247], []⟩,
        ⟨83371, false, false, [], []⟩
      ]⟩,
    ⟨[94251], [94249, 5], .source 47190⟩,
    ⟨[94249, 5], [94251], .contexts [
        ⟨83373, true, false, [], []⟩
      ]⟩,
    ⟨[94249], [94249], .contexts []⟩,
    ⟨[94251, 5], [94249], .contexts [
        ⟨83374, true, false, [], [5]⟩,
        ⟨28, false, false, [94249], []⟩,
        ⟨83375, false, false, [], []⟩
      ]⟩,
    ⟨[94253], [94251, 1], .source 47191⟩,
    ⟨[94251], [94251], .contexts []⟩,
    ⟨[94253, 1], [94251], .contexts [
        ⟨83377, false, false, [], [1]⟩,
        ⟨8, false, false, [94251], []⟩,
        ⟨83378, false, false, [], []⟩
      ]⟩,
    ⟨[94255], [94253, 9], .source 47192⟩,
    ⟨[94253], [94253], .contexts []⟩,
    ⟨[94255, 9], [94253], .contexts [
        ⟨83380, false, false, [], [9]⟩,
        ⟨46, false, false, [94253], []⟩,
        ⟨83381, false, false, [], []⟩
      ]⟩,
    ⟨[94257], [94255, 11], .source 47193⟩,
    ⟨[94255], [94255], .contexts []⟩,
    ⟨[94257, 11], [94255], .contexts [
        ⟨83383, false, false, [], [11]⟩,
        ⟨53, false, false, [94255], []⟩,
        ⟨83384, false, false, [], []⟩
      ]⟩,
    ⟨[94259], [94257, 1], .source 47194⟩,
    ⟨[94257], [94257], .contexts []⟩,
    ⟨[94259, 1], [94257], .contexts [
        ⟨83386, false, false, [], [1]⟩,
        ⟨8, false, false, [94257], []⟩,
        ⟨83387, false, false, [], []⟩
      ]⟩,
    ⟨[94261], [94259, 13], .source 47195⟩,
    ⟨[94259], [94259], .contexts []⟩,
    ⟨[94261, 13], [94259], .contexts [
        ⟨83389, false, false, [], [13]⟩,
        ⟨59, false, false, [94259], []⟩,
        ⟨83390, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1303. -/
def y322TCIndexRaw1303 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94263], [94261, 15], .source 47196⟩,
    ⟨[94261], [94261], .contexts []⟩,
    ⟨[94263, 15], [94261], .contexts [
        ⟨83392, false, false, [], [15]⟩,
        ⟨1, false, false, [94261], []⟩,
        ⟨83393, false, false, [], []⟩
      ]⟩,
    ⟨[94265], [94263, 1], .source 47197⟩,
    ⟨[94263], [94263], .contexts []⟩,
    ⟨[94265, 1], [94263], .contexts [
        ⟨83395, false, false, [], [1]⟩,
        ⟨8, false, false, [94263], []⟩,
        ⟨83396, false, false, [], []⟩
      ]⟩,
    ⟨[94267], [94265, 3], .source 47198⟩,
    ⟨[94265, 3], [94267], .contexts [
        ⟨83398, true, false, [], []⟩
      ]⟩,
    ⟨[94265], [94265], .contexts []⟩,
    ⟨[94267, 3], [94265], .contexts [
        ⟨83399, true, false, [], [3]⟩,
        ⟨20, false, false, [94265], []⟩,
        ⟨83400, false, false, [], []⟩
      ]⟩,
    ⟨[94269], [94267, 5], .source 47199⟩,
    ⟨[94267, 5], [94269], .contexts [
        ⟨83402, true, false, [], []⟩
      ]⟩,
    ⟨[94267], [94267], .contexts []⟩,
    ⟨[94269, 5], [94267], .contexts [
        ⟨83403, true, false, [], [5]⟩,
        ⟨28, false, false, [94267], []⟩,
        ⟨83404, false, false, [], []⟩
      ]⟩,
    ⟨[94271], [94269, 1], .source 47200⟩,
    ⟨[94269], [94269], .contexts []⟩,
    ⟨[94271, 1], [94269], .contexts [
        ⟨83406, false, false, [], [1]⟩,
        ⟨8, false, false, [94269], []⟩,
        ⟨83407, false, false, [], []⟩
      ]⟩,
    ⟨[94273], [94271, 9], .source 47201⟩,
    ⟨[94271], [94271], .contexts []⟩,
    ⟨[94273, 9], [94271], .contexts [
        ⟨83409, false, false, [], [9]⟩,
        ⟨46, false, false, [94271], []⟩,
        ⟨83410, false, false, [], []⟩
      ]⟩,
    ⟨[94275], [94273, 11], .source 47202⟩,
    ⟨[94273], [94273], .contexts []⟩,
    ⟨[94275, 11], [94273], .contexts [
        ⟨83412, false, false, [], [11]⟩,
        ⟨53, false, false, [94273], []⟩,
        ⟨83413, false, false, [], []⟩
      ]⟩,
    ⟨[94277], [94275, 1], .source 47203⟩,
    ⟨[94275, 1], [94277], .contexts [
        ⟨83415, true, false, [], []⟩
      ]⟩,
    ⟨[94275], [94275], .contexts []⟩,
    ⟨[94277, 1], [94275], .contexts [
        ⟨83416, true, false, [], [1]⟩,
        ⟨8, false, false, [94275], []⟩,
        ⟨83417, false, false, [], []⟩
      ]⟩,
    ⟨[94279], [94277, 13], .source 47204⟩,
    ⟨[94277], [94277], .contexts []⟩,
    ⟨[94279, 13], [94277], .contexts [
        ⟨83419, false, false, [], [13]⟩,
        ⟨59, false, false, [94277], []⟩,
        ⟨83420, false, false, [], []⟩
      ]⟩,
    ⟨[94281], [94279, 15], .source 47205⟩,
    ⟨[94279, 15], [94281], .contexts [
        ⟨83422, true, false, [], []⟩
      ]⟩,
    ⟨[94279], [94279], .contexts []⟩,
    ⟨[94281, 15], [94279], .contexts [
        ⟨83423, true, false, [], [15]⟩,
        ⟨1, false, false, [94279], []⟩,
        ⟨83424, false, false, [], []⟩
      ]⟩,
    ⟨[94283], [94281, 1], .source 47206⟩,
    ⟨[94281], [94281], .contexts []⟩,
    ⟨[94283, 1], [94281], .contexts [
        ⟨83426, false, false, [], [1]⟩,
        ⟨8, false, false, [94281], []⟩,
        ⟨83427, false, false, [], []⟩
      ]⟩,
    ⟨[94285], [94283, 3], .source 47207⟩,
    ⟨[94283, 3], [94285], .contexts [
        ⟨83429, true, false, [], []⟩
      ]⟩,
    ⟨[94283], [94283], .contexts []⟩,
    ⟨[94285, 3], [94283], .contexts [
        ⟨83430, true, false, [], [3]⟩,
        ⟨20, false, false, [94283], []⟩,
        ⟨83431, false, false, [], []⟩
      ]⟩,
    ⟨[94287], [94285, 5], .source 47208⟩,
    ⟨[94285, 5], [94287], .contexts [
        ⟨83433, true, false, [], []⟩
      ]⟩,
    ⟨[94285], [94285], .contexts []⟩,
    ⟨[94287, 5], [94285], .contexts [
        ⟨83434, true, false, [], [5]⟩,
        ⟨28, false, false, [94285], []⟩,
        ⟨83435, false, false, [], []⟩
      ]⟩,
    ⟨[94289], [94287, 1], .source 47209⟩,
    ⟨[94287, 1], [94289], .contexts [
        ⟨83437, true, false, [], []⟩
      ]⟩,
    ⟨[94287], [94287], .contexts []⟩,
    ⟨[94289, 1], [94287], .contexts [
        ⟨83438, true, false, [], [1]⟩,
        ⟨8, false, false, [94287], []⟩,
        ⟨83439, false, false, [], []⟩
      ]⟩,
    ⟨[94291], [94289, 9], .source 47210⟩,
    ⟨[94289], [94289], .contexts []⟩,
    ⟨[94291, 9], [94289], .contexts [
        ⟨83441, false, false, [], [9]⟩,
        ⟨46, false, false, [94289], []⟩,
        ⟨83442, false, false, [], []⟩
      ]⟩,
    ⟨[94293], [94291, 11], .source 47211⟩,
    ⟨[94291, 11], [94293], .contexts [
        ⟨83444, true, false, [], []⟩
      ]⟩,
    ⟨[94291], [94291], .contexts []⟩,
    ⟨[94293, 11], [94291], .contexts [
        ⟨83445, true, false, [], [11]⟩,
        ⟨53, false, false, [94291], []⟩,
        ⟨83446, false, false, [], []⟩
      ]⟩,
    ⟨[94295], [94293, 1], .source 47212⟩,
    ⟨[94293], [94293], .contexts []⟩,
    ⟨[94295, 1], [94293], .contexts [
        ⟨83448, false, false, [], [1]⟩,
        ⟨8, false, false, [94293], []⟩,
        ⟨83449, false, false, [], []⟩
      ]⟩,
    ⟨[94297], [94295, 13], .source 47213⟩,
    ⟨[94295, 13], [94297], .contexts [
        ⟨83451, true, false, [], []⟩
      ]⟩,
    ⟨[94295], [94295], .contexts []⟩,
    ⟨[94297, 13], [94295], .contexts [
        ⟨83452, true, false, [], [13]⟩,
        ⟨59, false, false, [94295], []⟩,
        ⟨83453, false, false, [], []⟩
      ]⟩,
    ⟨[94299], [94297, 15], .source 47214⟩]

/-- Exact literal claimed equations and contextual derivations, block 1304. -/
def y322TCIndexRaw1304 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94297, 15], [94299], .contexts [
        ⟨83455, true, false, [], []⟩
      ]⟩,
    ⟨[94297], [94297], .contexts []⟩,
    ⟨[94299, 15], [94297], .contexts [
        ⟨83456, true, false, [], [15]⟩,
        ⟨1, false, false, [94297], []⟩,
        ⟨83457, false, false, [], []⟩
      ]⟩,
    ⟨[94301], [94299, 1], .source 47215⟩,
    ⟨[94299], [94299], .contexts []⟩,
    ⟨[94301, 1], [94299], .contexts [
        ⟨83459, false, false, [], [1]⟩,
        ⟨8, false, false, [94299], []⟩,
        ⟨83460, false, false, [], []⟩
      ]⟩,
    ⟨[94303], [94301, 3], .source 47216⟩,
    ⟨[94301], [94301], .contexts []⟩,
    ⟨[94303, 3], [94301], .contexts [
        ⟨83462, false, false, [], [3]⟩,
        ⟨20, false, false, [94301], []⟩,
        ⟨83463, false, false, [], []⟩
      ]⟩,
    ⟨[94305], [94303, 5], .source 47217⟩,
    ⟨[94303], [94303], .contexts []⟩,
    ⟨[94305, 5], [94303], .contexts [
        ⟨83465, false, false, [], [5]⟩,
        ⟨28, false, false, [94303], []⟩,
        ⟨83466, false, false, [], []⟩
      ]⟩,
    ⟨[94307], [94305, 1], .source 47218⟩,
    ⟨[94305], [94305], .contexts []⟩,
    ⟨[94307, 1], [94305], .contexts [
        ⟨83468, false, false, [], [1]⟩,
        ⟨8, false, false, [94305], []⟩,
        ⟨83469, false, false, [], []⟩
      ]⟩,
    ⟨[94309], [94307, 9], .source 47219⟩,
    ⟨[94307, 9], [94309], .contexts [
        ⟨83471, true, false, [], []⟩
      ]⟩,
    ⟨[94309, 9], [94307], .contexts [
        ⟨83472, true, false, [], [9]⟩,
        ⟨46, false, false, [94307], []⟩
      ]⟩,
    ⟨[94309], [94309], .contexts []⟩,
    ⟨[94309], [94309], .contexts []⟩,
    ⟨[94305], [94305], .contexts []⟩,
    ⟨[94303], [94303], .contexts []⟩,
    ⟨[94301], [94301], .contexts []⟩,
    ⟨[94299], [94299], .contexts []⟩,
    ⟨[94297], [94297], .contexts []⟩,
    ⟨[94307, 1, 5, 3, 1, 15], [94297], .contexts [
        ⟨83470, false, false, [], [5, 3, 1, 15]⟩,
        ⟨83476, false, false, [], [5, 3, 1, 15]⟩,
        ⟨83469, false, false, [], [5, 3, 1, 15]⟩,
        ⟨83469, false, false, [], [5, 3, 1, 15]⟩,
        ⟨83467, false, false, [], [3, 1, 15]⟩,
        ⟨83477, false, false, [], [3, 1, 15]⟩,
        ⟨83466, false, false, [], [3, 1, 15]⟩,
        ⟨83466, false, false, [], [3, 1, 15]⟩,
        ⟨83464, false, false, [], [1, 15]⟩,
        ⟨83478, false, false, [], [1, 15]⟩,
        ⟨83463, false, false, [], [1, 15]⟩,
        ⟨83463, false, false, [], [1, 15]⟩,
        ⟨83461, false, false, [], [15]⟩,
        ⟨83479, false, false, [], [15]⟩,
        ⟨83460, false, false, [], [15]⟩,
        ⟨83460, false, false, [], [15]⟩,
        ⟨83458, false, false, [], []⟩,
        ⟨83480, false, false, [], []⟩,
        ⟨83457, false, false, [], []⟩,
        ⟨83457, false, false, [], []⟩
      ]⟩,
    ⟨[94295], [94295], .contexts []⟩,
    ⟨[94295, 1], [94293], .contexts [
        ⟨83450, false, false, [], []⟩
      ]⟩,
    ⟨[94293], [94293], .contexts []⟩,
    ⟨[94293, 11], [94291], .contexts [
        ⟨83447, false, false, [], []⟩
      ]⟩,
    ⟨[94291], [94291], .contexts []⟩,
    ⟨[94291, 9], [94289], .contexts [
        ⟨83443, false, false, [], []⟩
      ]⟩,
    ⟨[94289], [94289], .contexts []⟩,
    ⟨[94289, 1], [94287], .contexts [
        ⟨83440, false, false, [], []⟩
      ]⟩,
    ⟨[94287], [94287], .contexts []⟩,
    ⟨[94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1], [94287], .contexts [
        ⟨83481, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨83454, false, false, [], [1, 11, 9, 1]⟩,
        ⟨83482, false, false, [], [1, 11, 9, 1]⟩,
        ⟨83453, false, false, [], [1, 11, 9, 1]⟩,
        ⟨83453, false, false, [], [1, 11, 9, 1]⟩,
        ⟨83483, false, false, [], [11, 9, 1]⟩,
        ⟨83484, false, false, [], [11, 9, 1]⟩,
        ⟨83449, false, false, [], [11, 9, 1]⟩,
        ⟨83449, false, false, [], [11, 9, 1]⟩,
        ⟨83485, false, false, [], [9, 1]⟩,
        ⟨83486, false, false, [], [9, 1]⟩,
        ⟨83446, false, false, [], [9, 1]⟩,
        ⟨83446, false, false, [], [9, 1]⟩,
        ⟨83487, false, false, [], [1]⟩,
        ⟨83488, false, false, [], [1]⟩,
        ⟨83442, false, false, [], [1]⟩,
        ⟨83442, false, false, [], [1]⟩,
        ⟨83489, false, false, [], []⟩,
        ⟨83490, false, false, [], []⟩,
        ⟨83439, false, false, [], []⟩,
        ⟨83439, false, false, [], []⟩
      ]⟩,
    ⟨[94285], [94285], .contexts []⟩,
    ⟨[94285, 3], [94283], .contexts [
        ⟨83432, false, false, [], []⟩
      ]⟩,
    ⟨[94283], [94283], .contexts []⟩,
    ⟨[94281], [94281], .contexts []⟩,
    ⟨[94277], [94277], .contexts []⟩,
    ⟨[
      94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13
    ], [94277], .contexts [
        ⟨83491, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨83436, false, false, [], [3, 1, 15, 13]⟩,
        ⟨83492, false, false, [], [3, 1, 15, 13]⟩,
        ⟨83435, false, false, [], [3, 1, 15, 13]⟩,
        ⟨83435, false, false, [], [3, 1, 15, 13]⟩,
        ⟨83493, false, false, [], [1, 15, 13]⟩,
        ⟨83494, false, false, [], [1, 15, 13]⟩,
        ⟨83431, false, false, [], [1, 15, 13]⟩,
        ⟨83431, false, false, [], [1, 15, 13]⟩,
        ⟨83428, false, false, [], [15, 13]⟩,
        ⟨83495, false, false, [], [15, 13]⟩,
        ⟨83427, false, false, [], [15, 13]⟩,
        ⟨83427, false, false, [], [15, 13]⟩,
        ⟨83425, false, false, [], [13]⟩,
        ⟨83424, false, false, [], [13]⟩,
        ⟨83424, false, false, [], [13]⟩,
        ⟨83421, false, false, [], []⟩,
        ⟨83496, false, false, [], []⟩,
        ⟨83420, false, false, [], []⟩,
        ⟨83420, false, false, [], []⟩
      ]⟩,
    ⟨[94275], [94275], .contexts []⟩,
    ⟨[94275, 11], [94273], .contexts [
        ⟨83414, false, false, [], []⟩
      ]⟩,
    ⟨[94273], [94273], .contexts []⟩,
    ⟨[94271], [94271], .contexts []⟩,
    ⟨[94269], [94269], .contexts []⟩,
    ⟨[94267], [94267], .contexts []⟩,
    ⟨[
      94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [94267], .contexts [
        ⟨83497, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨83418, false, false, [], [11, 9, 1, 5]⟩,
        ⟨83498, false, false, [], [11, 9, 1, 5]⟩,
        ⟨83417, false, false, [], [11, 9, 1, 5]⟩,
        ⟨83417, false, false, [], [11, 9, 1, 5]⟩,
        ⟨83499, false, false, [], [9, 1, 5]⟩,
        ⟨83500, false, false, [], [9, 1, 5]⟩,
        ⟨83413, false, false, [], [9, 1, 5]⟩,
        ⟨83413, false, false, [], [9, 1, 5]⟩,
        ⟨83411, false, false, [], [1, 5]⟩,
        ⟨83501, false, false, [], [1, 5]⟩,
        ⟨83410, false, false, [], [1, 5]⟩,
        ⟨83410, false, false, [], [1, 5]⟩,
        ⟨83408, false, false, [], [5]⟩,
        ⟨83502, false, false, [], [5]⟩,
        ⟨83407, false, false, [], [5]⟩,
        ⟨83407, false, false, [], [5]⟩,
        ⟨83405, false, false, [], []⟩,
        ⟨83503, false, false, [], []⟩,
        ⟨83404, false, false, [], []⟩,
        ⟨83404, false, false, [], []⟩
      ]⟩,
    ⟨[94263], [94263], .contexts []⟩,
    ⟨[94261], [94261], .contexts []⟩,
    ⟨[94259], [94259], .contexts []⟩,
    ⟨[94257], [94257], .contexts []⟩,
    ⟨[
      94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1
    ], [94257], .contexts [
        ⟨83504, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨83401, false, false, [], [1, 15, 13, 1]⟩,
        ⟨83400, false, false, [], [1, 15, 13, 1]⟩,
        ⟨83400, false, false, [], [1, 15, 13, 1]⟩,
        ⟨83397, false, false, [], [15, 13, 1]⟩,
        ⟨83505, false, false, [], [15, 13, 1]⟩,
        ⟨83396, false, false, [], [15, 13, 1]⟩,
        ⟨83396, false, false, [], [15, 13, 1]⟩,
        ⟨83394, false, false, [], [13, 1]⟩,
        ⟨83506, false, false, [], [13, 1]⟩,
        ⟨83393, false, false, [], [13, 1]⟩,
        ⟨83393, false, false, [], [13, 1]⟩,
        ⟨83391, false, false, [], [1]⟩,
        ⟨83507, false, false, [], [1]⟩,
        ⟨83390, false, false, [], [1]⟩,
        ⟨83390, false, false, [], [1]⟩,
        ⟨83388, false, false, [], []⟩,
        ⟨83508, false, false, [], []⟩,
        ⟨83387, false, false, [], []⟩,
        ⟨83387, false, false, [], []⟩
      ]⟩,
    ⟨[94255], [94255], .contexts []⟩,
    ⟨[94253], [94253], .contexts []⟩,
    ⟨[94251], [94251], .contexts []⟩,
    ⟨[94249], [94249], .contexts []⟩,
    ⟨[94247], [94247], .contexts []⟩,
    ⟨[
      94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3
    ], [94247], .contexts [
        ⟨83509, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨83385, false, false, [], [9, 1, 5, 3]⟩,
        ⟨83510, false, false, [], [9, 1, 5, 3]⟩,
        ⟨83384, false, false, [], [9, 1, 5, 3]⟩,
        ⟨83384, false, false, [], [9, 1, 5, 3]⟩,
        ⟨83382, false, false, [], [1, 5, 3]⟩,
        ⟨83511, false, false, [], [1, 5, 3]⟩,
        ⟨83381, false, false, [], [1, 5, 3]⟩,
        ⟨83381, false, false, [], [1, 5, 3]⟩,
        ⟨83379, false, false, [], [5, 3]⟩,
        ⟨83512, false, false, [], [5, 3]⟩,
        ⟨83378, false, false, [], [5, 3]⟩,
        ⟨83378, false, false, [], [5, 3]⟩,
        ⟨83376, false, false, [], [3]⟩,
        ⟨83513, false, false, [], [3]⟩,
        ⟨83375, false, false, [], [3]⟩,
        ⟨83375, false, false, [], [3]⟩,
        ⟨83372, false, false, [], []⟩,
        ⟨83514, false, false, [], []⟩,
        ⟨83371, false, false, [], []⟩,
        ⟨83371, false, false, [], []⟩
      ]⟩,
    ⟨[94245], [94245], .contexts []⟩,
    ⟨[94243], [94243], .contexts []⟩,
    ⟨[94241], [94241], .contexts []⟩,
    ⟨[94239], [94239], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1305. -/
def y322TCIndexRaw1305 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94237], [94237], .contexts []⟩,
    ⟨[
      94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [94237], .contexts [
        ⟨83515, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨83369, false, false, [], [15, 13, 1, 11]⟩,
        ⟨83516, false, false, [], [15, 13, 1, 11]⟩,
        ⟨83368, false, false, [], [15, 13, 1, 11]⟩,
        ⟨83368, false, false, [], [15, 13, 1, 11]⟩,
        ⟨83366, false, false, [], [13, 1, 11]⟩,
        ⟨83517, false, false, [], [13, 1, 11]⟩,
        ⟨83365, false, false, [], [13, 1, 11]⟩,
        ⟨83365, false, false, [], [13, 1, 11]⟩,
        ⟨83363, false, false, [], [1, 11]⟩,
        ⟨83518, false, false, [], [1, 11]⟩,
        ⟨83362, false, false, [], [1, 11]⟩,
        ⟨83362, false, false, [], [1, 11]⟩,
        ⟨83360, false, false, [], [11]⟩,
        ⟨83519, false, false, [], [11]⟩,
        ⟨83359, false, false, [], [11]⟩,
        ⟨83359, false, false, [], [11]⟩,
        ⟨83357, false, false, [], []⟩,
        ⟨83520, false, false, [], []⟩,
        ⟨83356, false, false, [], []⟩,
        ⟨83356, false, false, [], []⟩
      ]⟩,
    ⟨[94235], [94235], .contexts []⟩,
    ⟨[94233], [94233], .contexts []⟩,
    ⟨[94231], [94231], .contexts []⟩,
    ⟨[94229], [94229], .contexts []⟩,
    ⟨[94227], [94227], .contexts []⟩,
    ⟨[
      94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1
    ], [94227], .contexts [
        ⟨83521, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨83353, false, false, [], [1, 5, 3, 1]⟩,
        ⟨83522, false, false, [], [1, 5, 3, 1]⟩,
        ⟨83352, false, false, [], [1, 5, 3, 1]⟩,
        ⟨83352, false, false, [], [1, 5, 3, 1]⟩,
        ⟨83349, false, false, [], [5, 3, 1]⟩,
        ⟨83523, false, false, [], [5, 3, 1]⟩,
        ⟨83348, false, false, [], [5, 3, 1]⟩,
        ⟨83348, false, false, [], [5, 3, 1]⟩,
        ⟨83344, true, false, [], [5, 3, 1]⟩,
        ⟨28, false, false, [94231], [3, 1]⟩,
        ⟨83345, false, false, [], [3, 1]⟩,
        ⟨83524, false, false, [], [3, 1]⟩,
        ⟨83345, false, false, [], [3, 1]⟩,
        ⟨83345, false, false, [], [3, 1]⟩,
        ⟨83341, true, false, [], [3, 1]⟩,
        ⟨20, false, false, [94229], [1]⟩,
        ⟨83342, false, false, [], [1]⟩,
        ⟨83525, false, false, [], [1]⟩,
        ⟨83342, false, false, [], [1]⟩,
        ⟨83342, false, false, [], [1]⟩,
        ⟨83338, true, false, [], [1]⟩,
        ⟨8, false, false, [94227], []⟩,
        ⟨83339, false, false, [], []⟩,
        ⟨83526, false, false, [], []⟩,
        ⟨83339, false, false, [], []⟩,
        ⟨83339, false, false, [], []⟩
      ]⟩,
    ⟨[94225], [94225], .contexts []⟩,
    ⟨[94221], [94221], .contexts []⟩,
    ⟨[94219], [94219], .contexts []⟩,
    ⟨[94217], [94217], .contexts []⟩,
    ⟨[
      94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [94217], .contexts [
        ⟨83527, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨83336, false, false, [], [13, 1, 11, 9]⟩,
        ⟨83528, false, false, [], [13, 1, 11, 9]⟩,
        ⟨83335, false, false, [], [13, 1, 11, 9]⟩,
        ⟨83335, false, false, [], [13, 1, 11, 9]⟩,
        ⟨83331, true, false, [], [13, 1, 11, 9]⟩,
        ⟨59, false, false, [94223], [1, 11, 9]⟩,
        ⟨83332, false, false, [], [1, 11, 9]⟩,
        ⟨83332, false, false, [], [1, 11, 9]⟩,
        ⟨83332, false, false, [], [1, 11, 9]⟩,
        ⟨83328, true, false, [], [1, 11, 9]⟩,
        ⟨8, false, false, [94221], [11, 9]⟩,
        ⟨83329, false, false, [], [11, 9]⟩,
        ⟨83529, false, false, [], [11, 9]⟩,
        ⟨83329, false, false, [], [11, 9]⟩,
        ⟨83329, false, false, [], [11, 9]⟩,
        ⟨83326, false, false, [], [9]⟩,
        ⟨83530, false, false, [], [9]⟩,
        ⟨83325, false, false, [], [9]⟩,
        ⟨83325, false, false, [], [9]⟩,
        ⟨83321, true, false, [], [9]⟩,
        ⟨46, false, false, [94217], []⟩,
        ⟨83322, false, false, [], []⟩,
        ⟨83531, false, false, [], []⟩,
        ⟨83322, false, false, [], []⟩,
        ⟨83322, false, false, [], []⟩
      ]⟩,
    ⟨[94215], [94215], .contexts []⟩,
    ⟨[94213], [94213], .contexts []⟩,
    ⟨[94209], [94209], .contexts []⟩,
    ⟨[
      94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1
    ], [94209], .contexts [
        ⟨83532, false, false, [], [1, 5, 3, 1]⟩,
        ⟨83318, true, false, [], [1, 5, 3, 1]⟩,
        ⟨8, false, false, [94215], [5, 3, 1]⟩,
        ⟨83319, false, false, [], [5, 3, 1]⟩,
        ⟨83533, false, false, [], [5, 3, 1]⟩,
        ⟨83319, false, false, [], [5, 3, 1]⟩,
        ⟨83319, false, false, [], [5, 3, 1]⟩,
        ⟨83316, false, false, [], [3, 1]⟩,
        ⟨83534, false, false, [], [3, 1]⟩,
        ⟨83315, false, false, [], [3, 1]⟩,
        ⟨83315, false, false, [], [3, 1]⟩,
        ⟨83311, true, false, [], [3, 1]⟩,
        ⟨20, false, false, [94211], [1]⟩,
        ⟨83312, false, false, [], [1]⟩,
        ⟨83312, false, false, [], [1]⟩,
        ⟨83312, false, false, [], [1]⟩,
        ⟨83309, false, false, [], []⟩,
        ⟨83535, false, false, [], []⟩,
        ⟨83308, false, false, [], []⟩,
        ⟨83308, false, false, [], []⟩
      ]⟩,
    ⟨[94207], [94207], .contexts []⟩,
    ⟨[94205], [94205], .contexts []⟩,
    ⟨[94203], [94203], .contexts []⟩,
    ⟨[94201], [94201], .contexts []⟩,
    ⟨[94199], [94199], .contexts []⟩,
    ⟨[
      94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9
    ], [94199], .contexts [
        ⟨83536, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨83305, false, false, [], [13, 1, 11, 9]⟩,
        ⟨83537, false, false, [], [13, 1, 11, 9]⟩,
        ⟨83304, false, false, [], [13, 1, 11, 9]⟩,
        ⟨83304, false, false, [], [13, 1, 11, 9]⟩,
        ⟨83300, true, false, [], [13, 1, 11, 9]⟩,
        ⟨59, false, false, [94205], [1, 11, 9]⟩,
        ⟨83301, false, false, [], [1, 11, 9]⟩,
        ⟨83538, false, false, [], [1, 11, 9]⟩,
        ⟨83301, false, false, [], [1, 11, 9]⟩,
        ⟨83301, false, false, [], [1, 11, 9]⟩,
        ⟨83298, false, false, [], [11, 9]⟩,
        ⟨83539, false, false, [], [11, 9]⟩,
        ⟨83297, false, false, [], [11, 9]⟩,
        ⟨83297, false, false, [], [11, 9]⟩,
        ⟨83293, true, false, [], [11, 9]⟩,
        ⟨53, false, false, [94201], [9]⟩,
        ⟨83294, false, false, [], [9]⟩,
        ⟨83540, false, false, [], [9]⟩,
        ⟨83294, false, false, [], [9]⟩,
        ⟨83294, false, false, [], [9]⟩,
        ⟨83290, true, false, [], [9]⟩,
        ⟨46, false, false, [94199], []⟩,
        ⟨83291, false, false, [], []⟩,
        ⟨83541, false, false, [], []⟩,
        ⟨83291, false, false, [], []⟩,
        ⟨83291, false, false, [], []⟩
      ]⟩,
    ⟨[
      94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [94191], .contexts [
        ⟨83542, false, false, [], [1, 5, 3, 1]⟩,
        ⟨83288, true, false, [], [1, 5, 3, 1]⟩,
        ⟨8, false, false, [94197], [5, 3, 1]⟩,
        ⟨83286, false, false, [], [5, 3, 1]⟩,
        ⟨83285, false, false, [], [5, 3, 1]⟩,
        ⟨83286, false, false, [], [5, 3, 1]⟩,
        ⟨83286, false, false, [], [5, 3, 1]⟩,
        ⟨83284, true, false, [], [5, 3, 1]⟩,
        ⟨28, false, false, [94195], [3, 1]⟩,
        ⟨83282, false, false, [], [3, 1]⟩,
        ⟨83281, false, false, [], [3, 1]⟩,
        ⟨83282, false, false, [], [3, 1]⟩,
        ⟨83282, false, false, [], [3, 1]⟩,
        ⟨83280, true, false, [], [3, 1]⟩,
        ⟨20, false, false, [94193], [1]⟩,
        ⟨83276, false, false, [], [1]⟩,
        ⟨83275, false, false, [], [1]⟩,
        ⟨83276, false, false, [], [1]⟩,
        ⟨83276, false, false, [], [1]⟩,
        ⟨83274, true, false, [], [1]⟩,
        ⟨8, false, false, [94191], []⟩,
        ⟨83258, false, false, [], []⟩,
        ⟨83257, false, false, [], []⟩,
        ⟨83258, false, false, [], []⟩,
        ⟨83258, false, false, [], []⟩
      ]⟩,
    ⟨[
      94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11
    ], [31083, 94185], .contexts [
        ⟨83543, false, false, [], [15, 13, 1, 11]⟩,
        ⟨83256, true, false, [], [15, 13, 1, 11]⟩,
        ⟨1, false, false, [94189], [13, 1, 11]⟩,
        ⟨83251, false, false, [], [13, 1, 11]⟩,
        ⟨83250, false, false, [], [13, 1, 11]⟩,
        ⟨83251, false, false, [], [13, 1, 11]⟩,
        ⟨83251, false, false, [], [13, 1, 11]⟩,
        ⟨83262, false, false, [], [1, 11]⟩,
        ⟨83232, false, false, [], [1, 11]⟩,
        ⟨83233, false, false, [], [1, 11]⟩,
        ⟨83233, false, false, [], [1, 11]⟩,
        ⟨83234, true, false, [], [1, 11]⟩,
        ⟨562, false, false, [94185], [11]⟩,
        ⟨563, false, false, [94185], [11]⟩,
        ⟨83211, false, false, [], [11, 11]⟩,
        ⟨83212, false, false, [], [11, 11]⟩,
        ⟨83213, true, false, [], [94185, 11, 11]⟩,
        ⟨83208, false, false, [], [11, 11]⟩,
        ⟨83210, false, false, [], [11, 11]⟩,
        ⟨83210, false, false, [], [11, 11]⟩,
        ⟨83230, false, false, [31083], [11]⟩,
        ⟨83235, false, false, [], [11]⟩,
        ⟨83236, false, false, [], [11]⟩,
        ⟨83213, true, false, [], [94187, 11]⟩,
        ⟨83235, false, false, [], [11]⟩,
        ⟨83236, false, false, [], [11]⟩,
        ⟨83236, false, false, [], [11]⟩,
        ⟨83231, false, false, [31083], []⟩
      ]⟩,
    ⟨[31091], [31083, 9191], .source 15610⟩,
    ⟨[31093], [31091, 2373], .source 15611⟩,
    ⟨[
      94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1
    ], [31093, 9189, 82311], .contexts [
        ⟨83544, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨83208, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨83209, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨83210, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨83202, false, false, [31083], [1, 5, 3, 1]⟩,
        ⟨70408, false, false, [31083], [5, 3, 1]⟩,
        ⟨83545, true, false, [], [91833, 5, 3, 1]⟩,
        ⟨67787, false, false, [31091], [3, 1]⟩,
        ⟨83546, true, false, [], [91833, 3, 1]⟩,
        ⟨67781, false, false, [31093], [1]⟩,
        ⟨12007, false, false, [31093], []⟩
      ]⟩,
    ⟨[31095], [31093, 9189], .source 15612⟩,
    ⟨[31097], [31095, 15173], .source 15613⟩,
    ⟨[31099], [31097, 2021], .source 15614⟩,
    ⟨[31101], [31099, 12833], .source 15615⟩,
    ⟨[
      94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9
    ], [31101, 80793, 9], .contexts [
        ⟨83547, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨83548, true, false, [], [82311, 15, 13, 1, 11, 9]⟩,
        ⟨14898, false, false, [31095], [13, 1, 11, 9]⟩,
        ⟨83549, true, false, [], [79913, 13, 1, 11, 9]⟩,
        ⟨7512, false, false, [31097], [1, 11, 9]⟩,
        ⟨83550, true, false, [], [79913, 1, 11, 9]⟩,
        ⟨7506, false, false, [31099], [11, 9]⟩,
        ⟨13762, false, false, [31099], [9]⟩,
        ⟨83551, true, false, [], [80793, 9]⟩
      ]⟩,
    ⟨[31103], [31101, 15159], .source 15616⟩,
    ⟨[31105], [31103, 4217], .source 15617⟩,
    ⟨[31107], [31105, 2375], .source 15618⟩,
    ⟨[31109], [31107, 4217], .source 15619⟩,
    ⟨[
      94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1
    ], [31109, 80801], .contexts [
        ⟨83552, false, false, [], [1, 5, 3, 1]⟩,
        ⟨24102, false, false, [31101], [1, 5, 3, 1]⟩,
        ⟨83553, true, false, [], [83953, 1, 5, 3, 1]⟩,
        ⟨24099, false, false, [31103], [5, 3, 1]⟩,
        ⟨83554, true, false, [], [83953, 5, 3, 1]⟩,
        ⟨24091, false, false, [31105], [3, 1]⟩,
        ⟨8262, false, false, [31105], [1]⟩,
        ⟨83555, true, false, [], [80801, 1]⟩,
        ⟨8258, false, false, [31107], []⟩,
        ⟨83556, true, false, [], [80801]⟩
      ]⟩,
    ⟨[31111], [31109, 15107], .source 15620⟩,
    ⟨[31113], [31111, 14713], .source 15621⟩,
    ⟨[31115], [31113, 2215], .source 15622⟩,
    ⟨[
      94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [31115, 78735], .contexts [
        ⟨83557, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨14786, false, false, [31109], [13, 1, 11, 9]⟩,
        ⟨83558, true, false, [], [81401, 13, 1, 11, 9]⟩,
        ⟨17144, false, false, [31111], [1, 11, 9]⟩,
        ⟨17120, false, false, [31111], [11, 9]⟩,
        ⟨83559, true, false, [], [78839, 11, 9]⟩,
        ⟨5189, false, false, [31113], [9]⟩,
        ⟨83560, true, false, [], [78839, 9]⟩,
        ⟨5170, false, false, [31115], []⟩
      ]⟩,
    ⟨[31117], [31115, 16221], .source 15623⟩,
    ⟨[31119], [31117, 26695], .source 15624⟩,
    ⟨[
      94307, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15
    ], [31119, 91939], .contexts [
        ⟨83561, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨5074, false, false, [31115], [5, 3, 1, 15]⟩,
        ⟨5530, false, false, [31115], [3, 1, 15]⟩,
        ⟨21081, false, false, [31115], [1, 15]⟩,
        ⟨83562, true, false, [], [83375, 1, 15]⟩,
        ⟨21083, false, false, [31117], [15]⟩,
        ⟨68219, false, false, [31117], []⟩,
        ⟨83563, true, false, [], [91939]⟩
      ]⟩,
    ⟨[31121], [31119, 26743], .source 15625⟩,
    ⟨[31123], [31121, 20893], .source 15626⟩,
    ⟨[94309, 11], [94309, 11], .contexts []⟩,
    ⟨[94309, 11], [31123, 86683], .contexts [
        ⟨83567, false, false, [], []⟩,
        ⟨83475, true, false, [], [11]⟩,
        ⟨83475, true, false, [], [11]⟩,
        ⟨83474, true, false, [], [11]⟩,
        ⟨83472, true, false, [], [11]⟩,
        ⟨3611, false, false, [94307], []⟩,
        ⟨3612, false, false, [94307], []⟩,
        ⟨83564, false, false, [], [13, 1]⟩,
        ⟨68280, false, false, [31119], [1]⟩,
        ⟨83565, true, false, [], [86683, 1]⟩,
        ⟨38366, false, false, [31121], []⟩,
        ⟨43017, false, false, [31121], []⟩,
        ⟨83566, true, false, [], [86683]⟩,
        ⟨63884, false, false, [31123], []⟩,
        ⟨13, true, false, [], [31123, 86683]⟩
      ]⟩,
    ⟨[31125], [31122], .source 15627⟩,
    ⟨[31123, 86683], [31123, 86683], .contexts []⟩,
    ⟨[31123, 86683], [31123, 86683], .contexts []⟩,
    ⟨[94309, 11], [31123, 86683], .contexts [
        ⟨83567, false, false, [], []⟩,
        ⟨83568, false, false, [], []⟩,
        ⟨83570, false, false, [], []⟩,
        ⟨83571, false, false, [], []⟩,
        ⟨83571, false, false, [], []⟩
      ]⟩,
    ⟨[94309], [94309], .contexts []⟩,
    ⟨[94309], [94309], .contexts []⟩,
    ⟨[31133], [31123, 20895], .source 15631⟩,
    ⟨[31135], [31133, 21901], .source 15632⟩,
    ⟨[87935, 3], [87935, 3], .contexts []⟩,
    ⟨[31137], [31134], .source 15633⟩,
    ⟨[31134], [31134], .contexts []⟩,
    ⟨[87935, 3], [31137, 94309], .contexts [
        ⟨83577, false, false, [], []⟩,
        ⟨83576, false, false, [31134], [87935, 3]⟩,
        ⟨47051, true, false, [31134, 31133], [3]⟩,
        ⟨83575, false, false, [31134], [86687, 11, 3]⟩,
        ⟨43013, true, false, [31134, 31123], [11, 3]⟩,
        ⟨83572, true, false, [31134], [3, 11, 3]⟩,
        ⟨3623, false, false, [31134, 94309], []⟩,
        ⟨83573, false, false, [31134], []⟩,
        ⟨83574, false, false, [31134], []⟩,
        ⟨83579, true, false, [], [94309]⟩,
        ⟨83579, true, false, [], [94309]⟩,
        ⟨83578, true, false, [], [94309]⟩
      ]⟩,
    ⟨[31139], [31123, 25739], .source 15634⟩,
    ⟨[31139, 90999], [31139, 90999], .contexts []⟩,
    ⟨[90999, 5], [90999, 5], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1306. -/
def y322TCIndexRaw1306 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[31141], [31138], .source 15635⟩,
    ⟨[31138], [31138], .contexts []⟩,
    ⟨[90999, 5], [31141, 94309], .contexts [
        ⟨83583, false, false, [], []⟩,
        ⟨83582, true, false, [31138], [5]⟩,
        ⟨63722, true, false, [], [5]⟩,
        ⟨83581, false, false, [31138], [91001, 11, 5]⟩,
        ⟨63890, true, false, [31138, 31123], [11, 5]⟩,
        ⟨83572, true, false, [31138], [5, 11, 5]⟩,
        ⟨681, false, false, [31138, 94309], []⟩,
        ⟨83573, false, false, [31138], []⟩,
        ⟨83574, false, false, [31138], []⟩,
        ⟨83585, true, false, [], [94309]⟩,
        ⟨83585, true, false, [], [94309]⟩,
        ⟨83584, true, false, [], [94309]⟩
      ]⟩,
    ⟨[31143], [31123, 22641], .source 15636⟩,
    ⟨[31143, 86421], [31143, 86421], .contexts []⟩,
    ⟨[31145], [31142], .source 15637⟩,
    ⟨[31142], [31142], .contexts []⟩,
    ⟨[86421, 7], [31145, 94309], .contexts [
        ⟨83588, true, false, [31142], [7]⟩,
        ⟨36822, true, false, [], [7]⟩,
        ⟨83587, false, false, [31142], [86423, 11, 7]⟩,
        ⟨49835, true, false, [31142, 31123], [11, 7]⟩,
        ⟨83572, true, false, [31142], [7, 11, 7]⟩,
        ⟨14923, false, false, [31142, 94309], []⟩,
        ⟨83573, false, false, [31142], []⟩,
        ⟨83574, false, false, [31142], []⟩,
        ⟨83590, true, false, [], [94309]⟩,
        ⟨83590, true, false, [], [94309]⟩,
        ⟨83589, true, false, [], [94309]⟩
      ]⟩,
    ⟨[94309, 7], [31143, 86421], .contexts [
        ⟨83591, true, false, [31144], [7]⟩,
        ⟨38, false, false, [31144, 86421], []⟩,
        ⟨83589, false, true, [], [86421]⟩
      ]⟩,
    ⟨[31147], [31123, 26745], .source 15638⟩,
    ⟨[31149], [31147, 26715], .source 15639⟩,
    ⟨[88201, 13], [88201, 13], .contexts []⟩,
    ⟨[31151], [31148], .source 15640⟩,
    ⟨[31148], [31148], .contexts []⟩,
    ⟨[88201, 13], [31151, 94309], .contexts [
        ⟨83595, false, false, [], []⟩,
        ⟨83594, false, false, [31148], [88201, 13]⟩,
        ⟨68247, true, true, [31148, 31147], [88201, 13]⟩,
        ⟨53, true, false, [31148, 31147, 26716, 88201], [13]⟩,
        ⟨68249, false, false, [31148, 31147, 26716], [11, 13]⟩,
        ⟨83593, false, false, [31148], [91939, 11, 13]⟩,
        ⟨68282, true, false, [31148, 31123], [11, 13]⟩,
        ⟨83572, true, false, [31148], [13, 11, 13]⟩,
        ⟨1109, false, false, [31148, 94309], []⟩,
        ⟨83573, false, false, [31148], []⟩,
        ⟨83574, false, false, [31148], []⟩,
        ⟨83597, true, false, [], [94309]⟩,
        ⟨83597, true, false, [], [94309]⟩,
        ⟨83596, true, false, [], [94309]⟩
      ]⟩,
    ⟨[31137, 94309], [31137, 94309], .contexts []⟩,
    ⟨[31153], [31135, 21895], .source 15641⟩,
    ⟨[31155], [31152], .source 15642⟩,
    ⟨[84575], [31155, 94307], .contexts [
        ⟨70980, true, false, [], []⟩,
        ⟨83600, false, false, [31152], [84577, 3]⟩,
        ⟨83578, true, true, [31152], [21895, 84577, 3]⟩,
        ⟨69435, true, false, [31152, 31136, 21895], [3]⟩,
        ⟨47040, true, false, [31152, 31136], [3]⟩,
        ⟨47040, true, false, [31152, 31136], [3]⟩,
        ⟨47039, true, false, [31152, 31136], [3]⟩,
        ⟨47046, true, false, [31152, 31136], [3]⟩,
        ⟨47, true, false, [31152, 31136, 87935], [3]⟩,
        ⟨573, true, false, [31152, 31136, 87935], [3]⟩,
        ⟨83577, false, false, [31152, 31136], [9, 3, 3]⟩,
        ⟨83580, false, false, [31152, 31136], [9, 3, 3]⟩,
        ⟨83599, false, false, [31152, 31136], [9, 3, 3]⟩,
        ⟨83599, false, false, [31152, 31136], [9, 3, 3]⟩,
        ⟨83473, false, false, [31152], [3, 3]⟩,
        ⟨20, false, false, [31152, 94307], []⟩,
        ⟨83601, true, false, [], [94307]⟩
      ]⟩,
    ⟨[31153], [31154], .contexts [
        ⟨83601, true, true, [], []⟩
      ]⟩,
    ⟨[94307], [31153, 84575], .contexts [
        ⟨83602, true, false, [31154], []⟩,
        ⟨83603, true, false, [], [84575]⟩
      ]⟩,
    ⟨[31155], [31152], .contexts [
        ⟨83601, false, false, [], []⟩
      ]⟩,
    ⟨[31152], [31152], .contexts []⟩,
    ⟨[94307], [31153, 84575], .contexts [
        ⟨83604, false, false, [], []⟩
      ]⟩,
    ⟨[31153, 84573], [31153, 84573], .contexts []⟩,
    ⟨[31157], [31153, 27755], .source 15643⟩,
    ⟨[31159], [31156], .source 15644⟩,
    ⟨[90995], [31159, 94303], .contexts [
        ⟨83609, false, false, [31156], [90995]⟩,
        ⟨71728, true, false, [31156, 31153], []⟩,
        ⟨83608, true, false, [31156], [5]⟩,
        ⟨83603, false, false, [31156], [84573, 5]⟩,
        ⟨83608, true, false, [31156, 31154, 31152], [5]⟩,
        ⟨27310, true, false, [31156, 31154], [5]⟩,
        ⟨83607, true, false, [31156, 31154, 31152], [1, 5]⟩,
        ⟨83470, false, false, [31156, 31154, 31152], [5]⟩,
        ⟨83476, false, false, [31156, 31154, 31152], [5]⟩,
        ⟨13, true, false, [31156, 31154, 31152], [94305, 5]⟩,
        ⟨83605, true, false, [31156, 31154], [94305, 5]⟩,
        ⟨83467, false, false, [31156], []⟩,
        ⟨83477, false, false, [31156], []⟩,
        ⟨13, true, false, [31156], [94303]⟩,
        ⟨83610, true, false, [], [94303]⟩
      ]⟩,
    ⟨[31161], [31157, 25757], .source 15645⟩,
    ⟨[31163], [31160], .source 15646⟩,
    ⟨[31163], [31160], .contexts [
        ⟨83613, false, false, [], []⟩
      ]⟩,
    ⟨[31163], [31160], .contexts [
        ⟨83614, false, false, [], []⟩,
        ⟨13, false, false, [31160], []⟩
      ]⟩,
    ⟨[31161], [31162], .contexts [
        ⟨83613, true, true, [], []⟩
      ]⟩,
    ⟨[94301, 1], [31161, 90997], .contexts [
        ⟨83615, false, false, [31162], [94301, 1]⟩,
        ⟨83478, true, false, [31162, 31160], [1]⟩,
        ⟨83464, true, false, [31162, 31160], [1]⟩,
        ⟨83611, true, false, [31162, 31160, 31158], [3, 1]⟩,
        ⟨83610, false, true, [31162, 31160], [90995, 3, 1]⟩,
        ⟨63930, false, false, [31162, 31160, 31157], [1]⟩,
        ⟨83612, true, false, [31162, 31160], [90995, 1]⟩,
        ⟨83616, true, false, [], [90995, 1]⟩,
        ⟨63712, false, false, [31161], []⟩
      ]⟩,
    ⟨[31161, 90997], [31161, 90997], .contexts []⟩,
    ⟨[94299], [31161, 90997], .contexts [
        ⟨83615, false, false, [31162], [94299]⟩,
        ⟨83479, true, false, [31162, 31160], []⟩,
        ⟨83461, true, false, [31162, 31160], []⟩,
        ⟨83617, false, false, [31162, 31160], []⟩,
        ⟨83618, false, false, [31162, 31160], []⟩,
        ⟨83616, true, false, [], [90997]⟩
      ]⟩,
    ⟨[31160], [31160], .contexts []⟩,
    ⟨[90997, 15], [31163, 94297], .contexts [
        ⟨83619, true, false, [31160], [15]⟩,
        ⟨83458, false, false, [31160], []⟩,
        ⟨83480, false, false, [31160], []⟩,
        ⟨83620, true, false, [], [94297]⟩,
        ⟨83620, true, false, [], [94297]⟩,
        ⟨83614, true, false, [], [94297]⟩
      ]⟩,
    ⟨[31165], [27755, 31163], .source 15647⟩,
    ⟨[31167], [31164], .source 15648⟩,
    ⟨[31169], [31167, 28613], .source 15649⟩,
    ⟨[26097, 91367], [26097, 91367], .contexts []⟩,
    ⟨[26097, 91367], [26097, 91367], .contexts []⟩,
    ⟨[31163, 94297], [31163, 94297], .contexts []⟩,
    ⟨[90997, 15], [31163, 94297], .contexts [
        ⟨83621, false, false, [], []⟩,
        ⟨83627, false, false, [], []⟩,
        ⟨83627, false, false, [], []⟩
      ]⟩,
    ⟨[90997, 14], [90997, 15], .contexts [
        ⟨10, false, false, [90997], []⟩
      ]⟩,
    ⟨[91367, 9], [91367, 9], .contexts []⟩,
    ⟨[94297], [94297], .contexts []⟩,
    ⟨[31173], [26095, 31163], .source 15651⟩,
    ⟨[91367, 9], [31173, 94297], .contexts [
        ⟨83630, false, false, [], []⟩,
        ⟨83626, true, false, [26096], [9]⟩,
        ⟨83626, true, false, [26096], [9]⟩,
        ⟨83625, true, false, [26096], [9]⟩,
        ⟨65595, true, false, [26096], [9]⟩,
        ⟨63721, true, false, [26096], [15, 9]⟩,
        ⟨63721, true, false, [26096], [15, 9]⟩,
        ⟨63728, true, false, [26096], [15, 9]⟩,
        ⟨63716, true, false, [26096], [15, 9]⟩,
        ⟨935, false, false, [26096, 90997], []⟩,
        ⟨83629, false, false, [26096], []⟩,
        ⟨83628, false, false, [26096], []⟩,
        ⟨83631, false, false, [26096, 31163], []⟩,
        ⟨65594, false, true, [], [31163, 94297]⟩,
        ⟨83632, true, false, [], [94297]⟩
      ]⟩,
    ⟨[31175], [31172], .source 15652⟩,
    ⟨[31177], [25751, 23601], .source 15653⟩,
    ⟨[89085, 15], [89085, 15], .contexts []⟩,
    ⟨[94295], [94295], .contexts []⟩,
    ⟨[31179], [31176], .source 15654⟩,
    ⟨[31181], [31179, 31163], .source 15655⟩,
    ⟨[89085, 15], [31181, 94295], .contexts [
        ⟨83636, false, false, [], []⟩,
        ⟨83635, false, false, [31176], [89085, 15]⟩,
        ⟨54157, true, false, [31176, 25751], [15]⟩,
        ⟨63911, false, false, [31176], [86791, 13, 15]⟩,
        ⟨39011, true, false, [31176, 25745], [13, 15]⟩,
        ⟨63910, true, false, [31176], [15, 13, 15]⟩,
        ⟨2022, false, false, [31176, 90997], []⟩,
        ⟨89, false, false, [31176, 90997], []⟩,
        ⟨83628, false, false, [31176], [13]⟩,
        ⟨83454, false, false, [31176, 31163], []⟩,
        ⟨83637, false, false, [31176, 31163], []⟩,
        ⟨83638, true, false, [], [31163, 94295]⟩,
        ⟨83639, true, false, [], [94295]⟩
      ]⟩,
    ⟨[31183], [31180], .source 15656⟩,
    ⟨[90997, 7], [27841, 89289], .contexts [
        ⟨71833, false, false, [], []⟩,
        ⟨71827, false, false, [], []⟩,
        ⟨71828, false, false, [], []⟩,
        ⟨71828, false, false, [], []⟩
      ]⟩,
    ⟨[89287, 7], [89287, 7], .contexts []⟩,
    ⟨[31185], [27843, 31163], .source 15657⟩,
    ⟨[89287, 7], [31185, 94297], .contexts [
        ⟨83643, false, false, [], []⟩,
        ⟨55091, true, false, [], [7]⟩,
        ⟨83642, true, false, [27840], [15, 7]⟩,
        ⟨18155, false, false, [27840, 90997], []⟩,
        ⟨83629, false, false, [27840], []⟩,
        ⟨83628, false, false, [27840], []⟩,
        ⟨83631, false, false, [27840, 31163], []⟩,
        ⟨71830, true, false, [], [31163, 94297]⟩,
        ⟨83644, true, false, [], [94297]⟩
      ]⟩,
    ⟨[31187], [31184], .source 15658⟩,
    ⟨[31173, 94297], [31173, 94297], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1307. -/
def y322TCIndexRaw1307 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[91365], [91365], .contexts []⟩,
    ⟨[31172], [31172], .contexts []⟩,
    ⟨[94295, 9], [31175, 91365], .contexts [
        ⟨83454, true, false, [], [9]⟩,
        ⟨83647, true, false, [31172], [13, 9]⟩,
        ⟨83647, true, false, [31172], [13, 9]⟩,
        ⟨83633, true, false, [31172], [13, 9]⟩,
        ⟨83630, true, false, [31172], [13, 9]⟩,
        ⟨511, false, false, [31172, 91367], []⟩,
        ⟨64, false, false, [31172, 91367], []⟩,
        ⟨65597, false, false, [31172], []⟩,
        ⟨83648, false, false, [31172], []⟩,
        ⟨83649, true, false, [], [91365]⟩,
        ⟨83649, true, false, [], [91365]⟩,
        ⟨83634, true, false, [], [91365]⟩
      ]⟩,
    ⟨[91365, 9], [31173, 94295], .contexts [
        ⟨83650, true, false, [31174], [9]⟩,
        ⟨46, false, false, [31174, 94295], []⟩,
        ⟨83634, false, true, [], [94295]⟩
      ]⟩,
    ⟨[31181, 94295], [31181, 94295], .contexts []⟩,
    ⟨[94293, 15], [94293, 15], .contexts []⟩,
    ⟨[31183], [31183], .contexts []⟩,
    ⟨[31183], [31180], .contexts [
        ⟨83654, false, false, [], []⟩,
        ⟨83641, false, false, [], []⟩
      ]⟩,
    ⟨[31180], [31180], .contexts []⟩,
    ⟨[31183], [31180], .contexts [
        ⟨83655, false, false, [], []⟩,
        ⟨83656, false, false, [], []⟩,
        ⟨83656, false, false, [], []⟩
      ]⟩,
    ⟨[94293, 15], [31183, 89083], .contexts [
        ⟨83653, false, false, [], []⟩,
        ⟨83450, true, false, [], [15]⟩,
        ⟨83652, true, false, [31180], [1, 15]⟩,
        ⟨83652, true, false, [31180], [1, 15]⟩,
        ⟨83640, true, false, [31180], [1, 15]⟩,
        ⟨83636, true, false, [31180], [1, 15]⟩,
        ⟨1666, false, false, [31180, 89085], []⟩,
        ⟨9, false, false, [31180, 89085], []⟩,
        ⟨76183, false, false, [31180], []⟩,
        ⟨54168, false, false, [31180], []⟩,
        ⟨83657, true, false, [], [89083]⟩
      ]⟩,
    ⟨[31181], [31182], .contexts [
        ⟨83641, true, true, [], []⟩
      ]⟩,
    ⟨[89083, 15], [31181, 94293], .contexts [
        ⟨83658, true, false, [31182], [15]⟩,
        ⟨1, false, false, [31182, 94293], []⟩,
        ⟨83659, true, false, [], [94293]⟩
      ]⟩,
    ⟨[31185, 94297], [31185, 94297], .contexts []⟩,
    ⟨[89287, 13], [89285], .contexts [
        ⟨55143, false, false, [], []⟩,
        ⟨55144, false, false, [], []⟩,
        ⟨55086, false, false, [], []⟩,
        ⟨55086, false, false, [], []⟩
      ]⟩,
    ⟨[89287, 12], [89287, 13], .contexts [
        ⟨64, false, false, [89287], []⟩
      ]⟩,
    ⟨[94295, 7], [94295, 7], .contexts []⟩,
    ⟨[89285], [89285], .contexts []⟩,
    ⟨[31184], [31184], .contexts []⟩,
    ⟨[31187], [31184], .contexts [
        ⟨83646, false, false, [], []⟩,
        ⟨83666, false, false, [], []⟩,
        ⟨83666, false, false, [], []⟩
      ]⟩,
    ⟨[94295, 7], [31187, 89285], .contexts [
        ⟨83664, false, false, [], []⟩,
        ⟨83454, true, false, [], [7]⟩,
        ⟨83661, true, false, [31184], [13, 7]⟩,
        ⟨83661, true, false, [31184], [13, 7]⟩,
        ⟨83645, true, false, [31184], [13, 7]⟩,
        ⟨83643, true, false, [31184], [13, 7]⟩,
        ⟨518, false, false, [31184, 89287], []⟩,
        ⟨83663, false, false, [31184], []⟩,
        ⟨83662, false, false, [31184], []⟩,
        ⟨83665, false, false, [31184], []⟩,
        ⟨83667, true, false, [], [89285]⟩
      ]⟩,
    ⟨[31185], [31186], .contexts [
        ⟨83646, true, true, [], []⟩
      ]⟩,
    ⟨[31183, 89083], [31183, 89083], .contexts []⟩,
    ⟨[94293, 15], [31183, 89083], .contexts [
        ⟨83653, false, false, [], []⟩,
        ⟨83658, false, false, [], []⟩,
        ⟨83670, false, false, [], []⟩,
        ⟨83670, false, false, [], []⟩
      ]⟩,
    ⟨[31189], [31183, 29255], .source 15659⟩,
    ⟨[31189, 85463], [31189, 85463], .contexts []⟩,
    ⟨[94293], [94293], .contexts []⟩,
    ⟨[85463, 3], [85463, 3], .contexts []⟩,
    ⟨[94293], [94293], .contexts []⟩,
    ⟨[31191], [31188], .source 15660⟩,
    ⟨[31188], [31188], .contexts []⟩,
    ⟨[85463, 3], [31191, 94293], .contexts [
        ⟨83675, false, false, [], []⟩,
        ⟨83673, true, false, [31188], [3]⟩,
        ⟨32010, true, false, [], [3]⟩,
        ⟨83672, false, false, [31188], [85465, 15, 3]⟩,
        ⟨76190, false, false, [31188, 31183], [85465, 15, 3]⟩,
        ⟨70130, true, false, [31188, 31183, 26437], [15, 3]⟩,
        ⟨66872, true, false, [31188, 31183], [15, 3]⟩,
        ⟨83671, true, false, [31188], [3, 15, 3]⟩,
        ⟨903, false, false, [31188, 94293], []⟩,
        ⟨83674, false, false, [31188], []⟩,
        ⟨83676, false, false, [31188], []⟩,
        ⟨83678, true, false, [], [94293]⟩,
        ⟨83678, true, false, [], [94293]⟩,
        ⟨83677, true, false, [], [94293]⟩
      ]⟩,
    ⟨[31189], [31190], .contexts [
        ⟨83677, true, true, [], []⟩
      ]⟩,
    ⟨[31193], [31183, 24399], .source 15661⟩,
    ⟨[31195], [31193, 26829], .source 15662⟩,
    ⟨[31197], [31194], .source 15663⟩,
    ⟨[31194], [31194], .contexts []⟩,
    ⟨[86669, 9], [31197, 94293], .contexts [
        ⟨83682, false, false, [31194], [86669, 9]⟩,
        ⟨68430, true, false, [31194, 31193], [9]⟩,
        ⟨83681, false, false, [31194], [89835, 15, 9]⟩,
        ⟨57811, true, false, [31194, 31183], [15, 9]⟩,
        ⟨83671, true, false, [31194], [9, 15, 9]⟩,
        ⟨2656, false, false, [31194, 94293], []⟩,
        ⟨83674, false, false, [31194], []⟩,
        ⟨83676, false, false, [31194], []⟩,
        ⟨83684, true, false, [], [94293]⟩,
        ⟨83684, true, false, [], [94293]⟩,
        ⟨83683, true, false, [], [94293]⟩
      ]⟩,
    ⟨[89081, 15], [89081, 15], .contexts []⟩,
    ⟨[94291], [94291], .contexts []⟩,
    ⟨[31181], [31181], .contexts []⟩,
    ⟨[31181], [31182], .contexts [
        ⟨83659, false, false, [], []⟩
      ]⟩,
    ⟨[31182], [31182], .contexts []⟩,
    ⟨[31181], [31182], .contexts [
        ⟨83688, false, false, [], []⟩,
        ⟨83689, false, false, [], []⟩,
        ⟨83690, false, false, [], []⟩,
        ⟨83690, false, false, [], []⟩
      ]⟩,
    ⟨[89081, 15], [31181, 94291], .contexts [
        ⟨83686, false, false, [], []⟩,
        ⟨53905, true, false, [], [15]⟩,
        ⟨83671, true, false, [31182], [11, 15]⟩,
        ⟨2046, false, false, [31182, 94293], []⟩,
        ⟨54, false, false, [31182, 94293], []⟩,
        ⟨83485, false, false, [31182], []⟩,
        ⟨83486, false, false, [31182], []⟩,
        ⟨83446, false, false, [31182], []⟩,
        ⟨83446, false, false, [31182], []⟩,
        ⟨83687, false, false, [31182], []⟩,
        ⟨83691, true, false, [], [94291]⟩
      ]⟩,
    ⟨[94291, 15], [31183, 89081], .contexts [
        ⟨83692, true, false, [31180], [15]⟩,
        ⟨1, false, false, [31180, 89081], []⟩,
        ⟨83641, true, false, [], [89081]⟩
      ]⟩,
    ⟨[31187, 89285], [31187, 89285], .contexts []⟩,
    ⟨[31187, 89285], [31187, 89285], .contexts []⟩,
    ⟨[31187, 89283], [31187, 89283], .contexts []⟩,
    ⟨[89283, 7], [89283, 7], .contexts []⟩,
    ⟨[31186], [31186], .contexts []⟩,
    ⟨[31185], [31186], .contexts [
        ⟨83669, false, false, [], []⟩,
        ⟨83698, false, false, [], []⟩,
        ⟨83698, false, false, [], []⟩
      ]⟩,
    ⟨[89283, 7], [31185, 94293], .contexts [
        ⟨83697, false, false, [], []⟩,
        ⟨83696, true, false, [31186], [7]⟩,
        ⟨55083, true, false, [], [7]⟩,
        ⟨83695, true, false, [31186], [1, 7]⟩,
        ⟨83695, true, false, [31186], [1, 7]⟩,
        ⟨83694, true, false, [31186], [1, 7]⟩,
        ⟨83668, true, false, [31186], [1, 7]⟩,
        ⟨83664, true, false, [31186], [1, 7]⟩,
        ⟨502, false, false, [31186, 94295], []⟩,
        ⟨9, false, false, [31186, 94295], []⟩,
        ⟨83483, false, false, [31186], []⟩,
        ⟨83484, false, false, [31186], []⟩,
        ⟨83449, false, false, [31186], []⟩,
        ⟨83449, false, false, [31186], []⟩,
        ⟨83676, false, false, [31186], []⟩,
        ⟨83699, true, false, [], [94293]⟩
      ]⟩,
    ⟨[94293, 7], [31187, 89283], .contexts [
        ⟨83700, true, false, [31184], [7]⟩,
        ⟨38, false, false, [31184, 89283], []⟩,
        ⟨83646, true, false, [], [89283]⟩
      ]⟩,
    ⟨[85463, 3], [31191, 94293], .contexts [
        ⟨83675, false, false, [], []⟩,
        ⟨83679, false, false, [], []⟩
      ]⟩,
    ⟨[31191, 94293], [31191, 94293], .contexts []⟩,
    ⟨[85463, 3], [31191, 94293], .contexts [
        ⟨83702, false, false, [], []⟩,
        ⟨83703, false, false, [], []⟩,
        ⟨83703, false, false, [], []⟩
      ]⟩,
    ⟨[31199], [31191, 31187], .source 15664⟩,
    ⟨[89283, 3], [89283, 3], .contexts []⟩,
    ⟨[88681], [88681], .contexts []⟩,
    ⟨[31201], [31198], .source 15665⟩,
    ⟨[31203], [31201, 29321], .source 15666⟩,
    ⟨[89283, 3], [31203, 88681], .contexts [
        ⟨83706, false, false, [], []⟩,
        ⟨83705, false, false, [31198], [89283, 3]⟩,
        ⟨83701, true, false, [31198, 31191], [3]⟩,
        ⟨83704, true, false, [31198], [7, 3]⟩,
        ⟨14556, false, false, [31198, 85463], []⟩,
        ⟨39, false, false, [31198, 85463], []⟩,
        ⟨76320, false, false, [31198], []⟩,
        ⟨83707, false, false, [31198, 29321], []⟩,
        ⟨83708, true, false, [], [29321, 88681]⟩,
        ⟨83709, true, false, [], [88681]⟩
      ]⟩,
    ⟨[31205], [31202], .source 15667⟩]

/-- Exact literal claimed equations and contextual derivations, block 1308. -/
def y322TCIndexRaw1308 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88681, 3], [31205, 89283], .contexts [
        ⟨83710, true, false, [31202], [3]⟩,
        ⟨20, false, false, [31202, 89283], []⟩,
        ⟨83711, true, false, [], [89283]⟩
      ]⟩,
    ⟨[94291, 3], [94291, 3], .contexts []⟩,
    ⟨[31207], [31189, 29279], .source 15668⟩,
    ⟨[94291, 3], [31207, 92935], .contexts [
        ⟨83713, false, false, [], []⟩,
        ⟨83447, true, false, [], [3]⟩,
        ⟨83704, true, false, [31190], [11, 3]⟩,
        ⟨545, false, false, [31190, 85463], []⟩,
        ⟨76296, false, false, [31190], []⟩,
        ⟨76295, false, false, [31190], []⟩,
        ⟨76298, false, false, [31190, 29279], []⟩,
        ⟨83680, true, false, [], [29279, 92935]⟩,
        ⟨83714, true, false, [], [92935]⟩
      ]⟩,
    ⟨[31209], [31206], .source 15669⟩,
    ⟨[92935, 3], [31209, 94291], .contexts [
        ⟨83715, true, false, [31206], [3]⟩,
        ⟨20, false, false, [31206, 94291], []⟩,
        ⟨83716, true, false, [], [94291]⟩
      ]⟩,
    ⟨[31181, 94291], [31181, 94291], .contexts []⟩,
    ⟨[31181, 94289], [31181, 94289], .contexts []⟩,
    ⟨[94289, 15], [94289, 15], .contexts []⟩,
    ⟨[94289, 15], [31183, 89079], .contexts [
        ⟨83720, false, false, [], []⟩,
        ⟨83719, true, false, [31180], [15]⟩,
        ⟨83443, true, false, [], [15]⟩,
        ⟨83718, true, false, [31180], [9, 15]⟩,
        ⟨83718, true, false, [31180], [9, 15]⟩,
        ⟨83692, true, false, [31180], [9, 15]⟩,
        ⟨83686, true, false, [31180], [9, 15]⟩,
        ⟨1671, false, false, [31180, 89081], []⟩,
        ⟨54194, false, false, [31180], []⟩,
        ⟨54193, false, false, [31180], []⟩,
        ⟨54195, false, false, [31180], []⟩,
        ⟨83657, true, false, [], [89079]⟩
      ]⟩,
    ⟨[89283, 7], [31185, 94293], .contexts [
        ⟨83697, false, false, [], []⟩,
        ⟨83700, false, false, [], []⟩
      ]⟩,
    ⟨[31185, 94293], [31185, 94293], .contexts []⟩,
    ⟨[89283, 7], [31185, 94293], .contexts [
        ⟨83722, false, false, [], []⟩,
        ⟨83723, false, false, [], []⟩,
        ⟨83723, false, false, [], []⟩
      ]⟩,
    ⟨[31185, 94291], [31185, 94291], .contexts []⟩,
    ⟨[89283, 11], [89281], .contexts [
        ⟨55148, false, false, [], []⟩
      ]⟩,
    ⟨[89283, 11], [89281], .contexts [
        ⟨83726, false, false, [], []⟩,
        ⟨55149, false, false, [], []⟩,
        ⟨55078, false, false, [], []⟩,
        ⟨55078, false, false, [], []⟩
      ]⟩,
    ⟨[89283, 10], [89283, 11], .contexts [
        ⟨54, false, false, [89283], []⟩
      ]⟩,
    ⟨[94291, 7], [94291, 7], .contexts []⟩,
    ⟨[89281], [89281], .contexts []⟩,
    ⟨[94291, 7], [31187, 89281], .contexts [
        ⟨83729, false, false, [], []⟩,
        ⟨83725, true, false, [31184], [7]⟩,
        ⟨83447, true, false, [], [7]⟩,
        ⟨83724, true, false, [31184], [11, 7]⟩,
        ⟨555, false, false, [31184, 89283], []⟩,
        ⟨83728, false, false, [31184], []⟩,
        ⟨83727, false, false, [31184], []⟩,
        ⟨83730, false, false, [31184], []⟩,
        ⟨83667, true, false, [], [89281]⟩
      ]⟩,
    ⟨[31211], [31185, 31183], .source 15670⟩,
    ⟨[31213], [31211, 23959], .source 15671⟩,
    ⟨[89283], [89283], .contexts []⟩,
    ⟨[31215], [31212], .source 15672⟩,
    ⟨[31212], [31212], .contexts []⟩,
    ⟨[88691, 15], [31215, 89283], .contexts [
        ⟨83733, false, false, [31212], [88691, 15]⟩,
        ⟨55445, true, false, [31212, 31211], [15]⟩,
        ⟨83732, false, false, [31212], [89083, 7, 15]⟩,
        ⟨83658, true, false, [31212, 31185], [7, 15]⟩,
        ⟨83724, true, false, [31212], [15, 7, 15]⟩,
        ⟨3386, false, false, [31212, 89283], []⟩,
        ⟨83734, false, false, [31212], []⟩,
        ⟨83736, true, false, [], [89283]⟩,
        ⟨83736, true, false, [], [89283]⟩,
        ⟨83735, true, false, [], [89283]⟩
      ]⟩,
    ⟨[31203, 88681], [31203, 88681], .contexts []⟩,
    ⟨[31203, 88681], [31203, 88681], .contexts []⟩,
    ⟨[31203, 88679], [31203, 88679], .contexts []⟩,
    ⟨[31203, 88679], [31203, 88679], .contexts []⟩,
    ⟨[88679, 3], [88679, 3], .contexts []⟩,
    ⟨[31202], [31202], .contexts []⟩,
    ⟨[88679, 3], [31205, 89281], .contexts [
        ⟨83742, false, false, [], []⟩,
        ⟨83741, true, false, [31202], [3]⟩,
        ⟨83740, true, false, [31202], [3]⟩,
        ⟨52048, true, false, [], [3]⟩,
        ⟨83739, true, false, [31202], [11, 3]⟩,
        ⟨83739, true, false, [31202], [11, 3]⟩,
        ⟨83738, true, false, [31202], [11, 3]⟩,
        ⟨83710, true, false, [31202], [11, 3]⟩,
        ⟨83706, true, false, [31202], [11, 3]⟩,
        ⟨545, false, false, [31202, 89283], []⟩,
        ⟨83728, false, false, [31202], []⟩,
        ⟨83727, false, false, [31202], []⟩,
        ⟨83730, false, false, [31202], []⟩,
        ⟨83743, true, false, [], [89281]⟩,
        ⟨83743, true, false, [], [89281]⟩,
        ⟨83711, true, false, [], [89281]⟩
      ]⟩,
    ⟨[31203], [31204], .contexts [
        ⟨83711, true, true, [], []⟩
      ]⟩,
    ⟨[89281, 3], [31203, 88679], .contexts [
        ⟨83744, true, false, [31204], [3]⟩,
        ⟨20, false, false, [31204, 88679], []⟩,
        ⟨83745, true, false, [], [88679]⟩
      ]⟩,
    ⟨[31207, 92935], [31207, 92935], .contexts []⟩,
    ⟨[31207, 92935], [31207, 92935], .contexts []⟩,
    ⟨[31207, 92933], [31207, 92933], .contexts []⟩,
    ⟨[94291, 9], [94289], .contexts [
        ⟨83487, false, false, [], []⟩,
        ⟨83488, false, false, [], []⟩,
        ⟨83442, false, false, [], []⟩,
        ⟨83442, false, false, [], []⟩
      ]⟩,
    ⟨[94291, 8], [94291, 9], .contexts [
        ⟨47, false, false, [94291], []⟩
      ]⟩,
    ⟨[94289], [94289], .contexts []⟩,
    ⟨[31206], [31206], .contexts []⟩,
    ⟨[31183, 89079], [31183, 89079], .contexts []⟩,
    ⟨[89077, 15], [89077, 15], .contexts []⟩,
    ⟨[89077, 15], [31181, 94287], .contexts [
        ⟨83755, false, false, [], []⟩,
        ⟨53897, true, false, [], [15]⟩,
        ⟨83754, true, false, [31182], [1, 15]⟩,
        ⟨83754, true, false, [31182], [1, 15]⟩,
        ⟨83721, true, false, [31182], [1, 15]⟩,
        ⟨83720, true, false, [31182], [1, 15]⟩,
        ⟨1666, false, false, [31182, 94289], []⟩,
        ⟨9, false, false, [31182, 94289], []⟩,
        ⟨83489, false, false, [31182], []⟩,
        ⟨83490, false, false, [31182], []⟩,
        ⟨83439, false, false, [31182], []⟩,
        ⟨83439, false, false, [31182], []⟩,
        ⟨83691, true, false, [], [94287]⟩
      ]⟩,
    ⟨[31187, 89281], [31187, 89281], .contexts []⟩,
    ⟨[31187, 89279], [31187, 89279], .contexts []⟩,
    ⟨[89279, 7], [89279, 7], .contexts []⟩,
    ⟨[89279, 7], [31185, 94289], .contexts [
        ⟨83759, false, false, [], []⟩,
        ⟨83758, true, false, [31186], [7]⟩,
        ⟨55075, true, false, [], [7]⟩,
        ⟨83757, true, false, [31186], [9, 7]⟩,
        ⟨83757, true, false, [31186], [9, 7]⟩,
        ⟨83731, true, false, [31186], [9, 7]⟩,
        ⟨83729, true, false, [31186], [9, 7]⟩,
        ⟨579, false, false, [31186, 94291], []⟩,
        ⟨83751, false, false, [31186], []⟩,
        ⟨83750, false, false, [31186], []⟩,
        ⟨83752, false, false, [31186], []⟩,
        ⟨83699, true, false, [], [94289]⟩
      ]⟩,
    ⟨[31205, 89281], [31205, 89281], .contexts []⟩,
    ⟨[31205, 89279], [31205, 89279], .contexts []⟩,
    ⟨[31203], [31204], .contexts [
        ⟨83745, false, false, [], []⟩
      ]⟩,
    ⟨[31204], [31204], .contexts []⟩,
    ⟨[89279, 3], [31203, 88677], .contexts [
        ⟨83762, true, false, [31204], [3]⟩,
        ⟨55075, true, false, [], [3]⟩,
        ⟨83761, true, false, [31204], [9, 3]⟩,
        ⟨83761, true, false, [31204], [9, 3]⟩,
        ⟨83744, true, false, [31204], [9, 3]⟩,
        ⟨83742, true, false, [31204], [9, 3]⟩,
        ⟨573, false, false, [31204, 88679], []⟩,
        ⟨47, false, false, [31204, 88679], []⟩,
        ⟨52116, false, false, [31204], []⟩,
        ⟨52117, false, false, [31204], []⟩,
        ⟨52043, false, false, [31204], []⟩,
        ⟨52043, false, false, [31204], []⟩,
        ⟨83764, true, false, [], [88677]⟩,
        ⟨83764, true, false, [], [88677]⟩,
        ⟨83763, true, false, [], [88677]⟩
      ]⟩,
    ⟨[31181, 94287], [31181, 94287], .contexts []⟩,
    ⟨[31181, 94287], [31181, 94287], .contexts []⟩,
    ⟨[31181, 94285], [31181, 94285], .contexts []⟩,
    ⟨[31181, 94285], [31181, 94285], .contexts []⟩,
    ⟨[89077, 5], [89075], .contexts [
        ⟨53955, false, false, [], []⟩,
        ⟨53956, false, false, [], []⟩,
        ⟨53892, false, false, [], []⟩,
        ⟨53892, false, false, [], []⟩
      ]⟩,
    ⟨[94285, 15], [94285, 15], .contexts []⟩,
    ⟨[89075], [89075], .contexts []⟩,
    ⟨[94285, 15], [31183, 89075], .contexts [
        ⟨83771, false, false, [], []⟩,
        ⟨83769, true, false, [31180], [15]⟩,
        ⟨83768, true, false, [31180], [15]⟩,
        ⟨83436, true, false, [], [15]⟩,
        ⟨83767, true, false, [31180], [5, 15]⟩,
        ⟨83767, true, false, [31180], [5, 15]⟩,
        ⟨83766, true, false, [31180], [5, 15]⟩,
        ⟨83756, true, false, [31180], [5, 15]⟩,
        ⟨83755, true, false, [31180], [5, 15]⟩,
        ⟨2072, false, false, [31180, 89077], []⟩,
        ⟨29, false, false, [31180, 89077], []⟩,
        ⟨83770, false, false, [31180], []⟩,
        ⟨83772, false, false, [31180], []⟩,
        ⟨83657, true, false, [], [89075]⟩
      ]⟩,
    ⟨[31185, 94289], [31185, 94289], .contexts []⟩,
    ⟨[89277], [89277], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1309. -/
def y322TCIndexRaw1309 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94287, 7], [31187, 89277], .contexts [
        ⟨83440, true, false, [], [7]⟩,
        ⟨83774, true, false, [31184], [1, 7]⟩,
        ⟨83774, true, false, [31184], [1, 7]⟩,
        ⟨83760, true, false, [31184], [1, 7]⟩,
        ⟨83759, true, false, [31184], [1, 7]⟩,
        ⟨502, false, false, [31184, 89279], []⟩,
        ⟨9, false, false, [31184, 89279], []⟩,
        ⟨55152, false, false, [31184], []⟩,
        ⟨55153, false, false, [31184], []⟩,
        ⟨55070, false, false, [31184], []⟩,
        ⟨55070, false, false, [31184], []⟩,
        ⟨83775, false, false, [31184], []⟩,
        ⟨83667, true, false, [], [89277]⟩
      ]⟩,
    ⟨[31183, 89075], [31183, 89075], .contexts []⟩,
    ⟨[31183, 89075], [31183, 89075], .contexts []⟩,
    ⟨[89073, 15], [89073, 15], .contexts []⟩,
    ⟨[89073, 15], [31181, 94283], .contexts [
        ⟨83779, false, false, [], []⟩,
        ⟨53889, true, false, [], [15]⟩,
        ⟨83778, true, false, [31182], [3, 15]⟩,
        ⟨83778, true, false, [31182], [3, 15]⟩,
        ⟨83777, true, false, [31182], [3, 15]⟩,
        ⟨83773, true, false, [31182], [3, 15]⟩,
        ⟨83771, true, false, [31182], [3, 15]⟩,
        ⟨1141, false, false, [31182, 94285], []⟩,
        ⟨21, false, false, [31182, 94285], []⟩,
        ⟨83493, false, false, [31182], []⟩,
        ⟨83494, false, false, [31182], []⟩,
        ⟨83431, false, false, [31182], []⟩,
        ⟨83431, false, false, [31182], []⟩,
        ⟨83691, true, false, [], [94283]⟩
      ]⟩,
    ⟨[31181, 94283], [31181, 94283], .contexts []⟩,
    ⟨[31181, 94279], [31181, 94279], .contexts []⟩,
    ⟨[94279, 1], [31183, 89073], .contexts [
        ⟨83782, true, false, [31180], [1]⟩,
        ⟨83425, true, false, [], [1]⟩,
        ⟨83428, true, false, [], [15, 1]⟩,
        ⟨83781, true, false, [31180], [1, 15, 1]⟩,
        ⟨83781, true, false, [31180], [1, 15, 1]⟩,
        ⟨83780, true, false, [31180], [1, 15, 1]⟩,
        ⟨83779, true, false, [31180], [1, 15, 1]⟩,
        ⟨504, false, false, [31180, 89073], []⟩,
        ⟨83657, true, false, [], [89073]⟩
      ]⟩,
    ⟨[31181], [31181], .contexts []⟩,
    ⟨[31181], [31181], .contexts []⟩,
    ⟨[94279], [31183, 89071], .contexts [
        ⟨83688, false, false, [31180], [94279]⟩,
        ⟨83784, false, false, [31180], [94279]⟩,
        ⟨83785, false, false, [31180], [94279]⟩,
        ⟨83782, true, false, [31180], []⟩,
        ⟨83659, false, false, [31180], [94279]⟩,
        ⟨8, true, false, [31180, 31182, 94279], []⟩,
        ⟨83783, false, false, [31180, 31182], [1]⟩,
        ⟨53957, false, false, [31180], []⟩,
        ⟨53958, false, false, [31180], []⟩,
        ⟨53885, false, false, [31180], []⟩,
        ⟨53885, false, false, [31180], []⟩,
        ⟨83641, true, false, [], [89071]⟩
      ]⟩,
    ⟨[89071, 13], [31181, 94277], .contexts [
        ⟨83786, true, false, [31182], [13]⟩,
        ⟨83421, false, false, [31182], []⟩,
        ⟨83496, false, false, [31182], []⟩,
        ⟨83690, true, false, [], [94277]⟩,
        ⟨83690, true, false, [], [94277]⟩,
        ⟨83689, true, false, [], [94277]⟩
      ]⟩,
    ⟨[31183, 89069], [31183, 89069], .contexts []⟩,
    ⟨[94311], [82717, 3], .source 47220⟩,
    ⟨[82717, 3], [94311], .contexts [
        ⟨83789, true, false, [], []⟩
      ]⟩,
    ⟨[94311, 3], [82717], .contexts [
        ⟨83790, true, false, [], [3]⟩,
        ⟨20, false, false, [82717], []⟩,
        ⟨15735, false, false, [], []⟩
      ]⟩,
    ⟨[94311], [94311], .contexts []⟩,
    ⟨[94311], [94311], .contexts []⟩,
    ⟨[82717, 3], [94311], .contexts [
        ⟨83790, false, false, [], []⟩,
        ⟨83792, false, false, [], []⟩,
        ⟨83793, false, false, [], []⟩,
        ⟨83793, false, false, [], []⟩
      ]⟩,
    ⟨[15399, 94311], [15399, 94311], .contexts []⟩,
    ⟨[94311], [94311], .contexts []⟩,
    ⟨[94311, 1], [15399, 94311], .contexts [
        ⟨83794, true, false, [], [1]⟩,
        ⟨130, false, false, [82717], []⟩,
        ⟨133, false, false, [82717], []⟩,
        ⟨16242, false, false, [], [3, 1, 3]⟩,
        ⟨16236, false, false, [], [3, 1, 3]⟩,
        ⟨16237, false, false, [], [3, 1, 3]⟩,
        ⟨16237, false, false, [], [3, 1, 3]⟩,
        ⟨16276, false, false, [], [1, 3]⟩,
        ⟨16277, false, false, [], [1, 3]⟩,
        ⟨16278, false, false, [], [1, 3]⟩,
        ⟨16278, false, false, [], [1, 3]⟩,
        ⟨16241, false, false, [15399], [3]⟩,
        ⟨83790, false, false, [15399], []⟩,
        ⟨83795, false, false, [], []⟩,
        ⟨83796, false, false, [15399], []⟩
      ]⟩,
    ⟨[94311, 1], [15399, 94311], .contexts [
        ⟨83797, false, false, [], []⟩,
        ⟨16281, true, false, [], [94311]⟩
      ]⟩,
    ⟨[553, 94311], [553, 94311], .contexts []⟩,
    ⟨[94311, 5], [553, 94311], .contexts [
        ⟨83794, true, false, [], [5]⟩,
        ⟨871, false, false, [82717], []⟩,
        ⟨873, false, false, [82717], []⟩,
        ⟨15733, false, false, [], [3, 5, 3]⟩,
        ⟨15710, false, false, [], [3, 5, 3]⟩,
        ⟨15711, false, false, [], [3, 5, 3]⟩,
        ⟨15711, false, false, [], [3, 5, 3]⟩,
        ⟨16387, false, false, [], [5, 3]⟩,
        ⟨15713, false, false, [], [5, 3]⟩,
        ⟨15714, false, false, [], [5, 3]⟩,
        ⟨15714, false, false, [], [5, 3]⟩,
        ⟨15732, false, false, [553], [3]⟩,
        ⟨83790, false, false, [553], []⟩,
        ⟨83799, false, false, [], []⟩,
        ⟨83796, false, false, [553], []⟩
      ]⟩,
    ⟨[94311, 5], [553, 94311], .contexts [
        ⟨83800, false, false, [], []⟩,
        ⟨15717, true, false, [], [94311]⟩
      ]⟩,
    ⟨[551, 83667], [551, 83667], .contexts []⟩,
    ⟨[551, 83667], [551, 83667], .contexts []⟩,
    ⟨[94311, 7], [94311, 7], .contexts []⟩,
    ⟨[551], [551], .contexts [
        ⟨13, false, false, [], [551]⟩
      ]⟩,
    ⟨[94311, 7], [551, 83667], .contexts [
        ⟨83804, false, false, [], []⟩,
        ⟨83794, true, false, [], [7]⟩,
        ⟨140, false, false, [82717], []⟩,
        ⟨141, false, false, [82717], []⟩,
        ⟨15755, false, false, [], [3]⟩,
        ⟨22523, false, false, [], []⟩,
        ⟨83802, false, false, [], []⟩,
        ⟨83803, false, false, [], []⟩,
        ⟨83803, false, false, [], []⟩,
        ⟨22518, false, false, [551], []⟩,
        ⟨83805, true, false, [], [83667]⟩
      ]⟩,
    ⟨[545], [550], .contexts [
        ⟨1716, true, true, [], []⟩
      ]⟩,
    ⟨[243, 94311], [243, 94311], .contexts []⟩,
    ⟨[31217], [15343, 24997], .source 15673⟩,
    ⟨[94311, 13], [94311, 13], .contexts []⟩,
    ⟨[94311, 13], [31217, 90479], .contexts [
        ⟨83810, false, false, [], []⟩,
        ⟨83794, true, false, [], [13]⟩,
        ⟨147, false, false, [82717], []⟩,
        ⟨148, false, false, [82717], []⟩,
        ⟨15763, false, false, [], [3]⟩,
        ⟨60818, false, false, [15343], []⟩,
        ⟨83809, true, false, [], [90479]⟩,
        ⟨60834, false, false, [31217], []⟩,
        ⟨13, true, false, [], [31217, 90479]⟩
      ]⟩,
    ⟨[31219], [31216], .source 15674⟩,
    ⟨[15359, 82731], [15359, 82731], .contexts []⟩,
    ⟨[15359, 82731], [15359, 82731], .contexts []⟩,
    ⟨[15359, 86331], [15359, 86331], .contexts []⟩,
    ⟨[15359, 86331], [15359, 86331], .contexts []⟩,
    ⟨[94311, 15], [94311, 15], .contexts []⟩,
    ⟨[15359], [15359], .contexts [
        ⟨13, false, false, [], [15359]⟩
      ]⟩,
    ⟨[94311, 15], [15359, 86331], .contexts [
        ⟨83817, false, false, [], []⟩,
        ⟨83794, true, false, [], [15]⟩,
        ⟨151, false, false, [82717], []⟩,
        ⟨152, false, false, [82717], []⟩,
        ⟨15920, false, false, [], [3]⟩,
        ⟨83813, false, false, [], [3]⟩,
        ⟨83814, false, false, [], [3]⟩,
        ⟨83814, false, false, [], [3]⟩,
        ⟨36504, false, false, [15359], []⟩,
        ⟨83815, false, false, [], []⟩,
        ⟨83816, false, false, [], []⟩,
        ⟨36514, false, false, [15359], []⟩,
        ⟨83818, true, false, [], [86331]⟩
      ]⟩,
    ⟨[8695], [15358], .contexts [
        ⟨15899, true, true, [], []⟩
      ]⟩,
    ⟨[86331, 15], [8695, 94311], .contexts [
        ⟨83819, true, false, [15358], [15]⟩,
        ⟨1, false, false, [15358, 94311], []⟩,
        ⟨83820, true, false, [], [94311]⟩
      ]⟩,
    ⟨[94313], [94311, 9], .source 47221⟩,
    ⟨[94311, 9], [94313], .contexts [
        ⟨83822, true, false, [], []⟩
      ]⟩,
    ⟨[94313, 9], [94311], .contexts [
        ⟨83823, true, false, [], [9]⟩,
        ⟨46, false, false, [94311], []⟩,
        ⟨83793, false, false, [], []⟩
      ]⟩,
    ⟨[94313], [94313], .contexts []⟩,
    ⟨[94311, 9], [94313], .contexts [
        ⟨83823, false, false, [], []⟩,
        ⟨83825, false, false, [], []⟩,
        ⟨83825, false, false, [], []⟩
      ]⟩,
    ⟨[295, 82771], [295, 82771], .contexts []⟩,
    ⟨[295, 82771], [295, 82771], .contexts []⟩,
    ⟨[94313, 3], [94313, 3], .contexts []⟩,
    ⟨[94313, 3], [295, 82771], .contexts [
        ⟨83829, false, false, [], []⟩,
        ⟨83826, true, false, [], [3]⟩,
        ⟨196, false, false, [94311], []⟩,
        ⟨197, false, false, [94311], []⟩,
        ⟨83791, false, false, [], [9]⟩,
        ⟨15734, false, false, [], [9]⟩,
        ⟨15735, false, false, [], [9]⟩,
        ⟨15735, false, false, [], [9]⟩,
        ⟨16433, false, false, [], []⟩,
        ⟨83827, false, false, [], []⟩,
        ⟨83828, false, false, [], []⟩,
        ⟨83828, false, false, [], []⟩,
        ⟨16424, false, false, [295], []⟩,
        ⟨3765, true, false, [], [82771]⟩
      ]⟩,
    ⟨[551, 83669], [551, 83669], .contexts []⟩,
    ⟨[94313, 7], [551, 83669], .contexts [
        ⟨83826, true, false, [], [7]⟩,
        ⟨1084, false, false, [94311], []⟩,
        ⟨1085, false, false, [94311], []⟩,
        ⟨83804, false, false, [], [9]⟩,
        ⟨83806, false, false, [], [9]⟩,
        ⟨83802, false, false, [], [9]⟩,
        ⟨83803, false, false, [], [9]⟩,
        ⟨83803, false, false, [], [9]⟩,
        ⟨22529, false, false, [551], []⟩,
        ⟨83831, false, false, [], []⟩,
        ⟨31715, false, false, [551], []⟩,
        ⟨83805, true, false, [], [83669]⟩
      ]⟩,
    ⟨[31217, 90479], [31217, 90479], .contexts []⟩,
    ⟨[31217, 90479], [31217, 90479], .contexts []⟩,
    ⟨[31221], [31217, 25013], .source 15675⟩,
    ⟨[31223], [31220], .source 15676⟩,
    ⟨[15359, 86333], [15359, 86333], .contexts []⟩,
    ⟨[94313, 15], [15359, 86333], .contexts [
        ⟨83826, true, false, [], [15]⟩,
        ⟨205, false, false, [94311], []⟩,
        ⟨206, false, false, [94311], []⟩,
        ⟨83817, false, false, [], [9]⟩,
        ⟨83819, false, false, [], [9]⟩,
        ⟨83815, false, false, [], [9]⟩,
        ⟨83816, false, false, [], [9]⟩,
        ⟨83816, false, false, [], [9]⟩,
        ⟨36531, false, false, [15359], []⟩,
        ⟨83837, false, false, [], []⟩,
        ⟨36543, false, false, [15359], []⟩,
        ⟨83818, true, false, [], [86333]⟩
      ]⟩,
    ⟨[31225], [295, 15351], .source 15677⟩]

/-- Exact literal claimed equations and contextual derivations, block 1310. -/
def y322TCIndexRaw1310 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[31225, 93551], [31225, 93551], .contexts []⟩,
    ⟨[31227], [31224], .source 15678⟩,
    ⟨[31224], [31224], .contexts []⟩,
    ⟨[93551, 11], [31227, 94313], .contexts [
        ⟨83840, true, false, [31224], [11]⟩,
        ⟨79925, true, false, [], [11]⟩,
        ⟨83839, false, false, [31224], [82779, 3, 11]⟩,
        ⟨16542, true, false, [31224, 295], [3, 11]⟩,
        ⟨83828, true, false, [31224], [11, 3, 11]⟩,
        ⟨83828, true, false, [31224], [11, 3, 11]⟩,
        ⟨83827, true, false, [31224], [11, 3, 11]⟩,
        ⟨83830, true, false, [31224], [11, 3, 11]⟩,
        ⟨83829, true, false, [31224], [11, 3, 11]⟩,
        ⟨1693, false, false, [31224, 94313], []⟩,
        ⟨83842, true, false, [], [94313]⟩,
        ⟨83842, true, false, [], [94313]⟩,
        ⟨83841, true, false, [], [94313]⟩
      ]⟩,
    ⟨[94315], [89197, 15], .source 47222⟩,
    ⟨[89197, 15], [94315], .contexts [
        ⟨83844, true, false, [], []⟩
      ]⟩,
    ⟨[94315, 15], [89197], .contexts [
        ⟨83845, true, false, [], [15]⟩,
        ⟨1, false, false, [89197], []⟩,
        ⟨54510, false, false, [], []⟩
      ]⟩,
    ⟨[94315], [94315], .contexts []⟩,
    ⟨[94315], [94315], .contexts []⟩,
    ⟨[89197, 15], [94315], .contexts [
        ⟨83845, false, false, [], []⟩,
        ⟨83847, false, false, [], []⟩,
        ⟨83848, false, false, [], []⟩,
        ⟨83848, false, false, [], []⟩
      ]⟩,
    ⟨[23719, 94315], [23719, 94315], .contexts []⟩,
    ⟨[23719, 94315], [23719, 94315], .contexts []⟩,
    ⟨[23719, 94315], [23719, 94315], .contexts []⟩,
    ⟨[94315], [94315], .contexts []⟩,
    ⟨[23719], [23719], .contexts [
        ⟨13, false, false, [], [23719]⟩
      ]⟩,
    ⟨[23705, 94315], [23705, 94315], .contexts []⟩,
    ⟨[23705, 94315], [23705, 94315], .contexts []⟩,
    ⟨[94315, 5], [94315, 5], .contexts []⟩,
    ⟨[23705], [23705], .contexts [
        ⟨13, false, false, [], [23705]⟩
      ]⟩,
    ⟨[23729, 83675], [23729, 83675], .contexts []⟩,
    ⟨[23729, 83675], [23729, 83675], .contexts []⟩,
    ⟨[23729, 83677], [23729, 83677], .contexts []⟩,
    ⟨[23729, 83677], [23729, 83677], .contexts []⟩,
    ⟨[94315, 7], [94315, 7], .contexts []⟩,
    ⟨[23729], [23729], .contexts [
        ⟨13, false, false, [], [23729]⟩
      ]⟩,
    ⟨[94315, 7], [23729, 83677], .contexts [
        ⟨83863, false, false, [], []⟩,
        ⟨83849, true, false, [], [7]⟩,
        ⟨37, false, false, [89197], []⟩,
        ⟨40, false, false, [89197], []⟩,
        ⟨54728, false, false, [], [15]⟩,
        ⟨83859, false, false, [], [15]⟩,
        ⟨83860, false, false, [], [15]⟩,
        ⟨83860, false, false, [], [15]⟩,
        ⟨22592, false, false, [23729], []⟩,
        ⟨83861, false, false, [], []⟩,
        ⟨83862, false, false, [], []⟩,
        ⟨22600, false, false, [23729], []⟩,
        ⟨83864, true, false, [], [83677]⟩
      ]⟩,
    ⟨[30345, 93553], [30345, 93553], .contexts []⟩,
    ⟨[30345, 93553], [30345, 93553], .contexts []⟩,
    ⟨[30357, 86341], [30357, 86341], .contexts []⟩,
    ⟨[30357, 86341], [30357, 86341], .contexts []⟩,
    ⟨[94315, 13], [94315, 13], .contexts []⟩,
    ⟨[94315, 13], [30357, 86341], .contexts [
        ⟨83870, false, false, [], []⟩,
        ⟨83849, true, false, [], [13]⟩,
        ⟨259, false, false, [89197], []⟩,
        ⟨262, false, false, [89197], []⟩,
        ⟨79987, false, false, [], [15, 13, 15]⟩,
        ⟨79990, false, false, [], [15, 13, 15]⟩,
        ⟨83866, false, false, [], [15, 13, 15]⟩,
        ⟨83867, false, false, [], [15, 13, 15]⟩,
        ⟨83867, false, false, [], [15, 13, 15]⟩,
        ⟨79983, false, false, [30345], [13, 15]⟩,
        ⟨80037, true, false, [], [86337, 13, 15]⟩,
        ⟨36599, false, false, [30357], [15]⟩,
        ⟨36622, false, false, [30357], []⟩,
        ⟨83868, false, false, [], []⟩,
        ⟨83869, false, false, [], []⟩,
        ⟨36630, false, false, [30357], []⟩
      ]⟩,
    ⟨[94315, 13], [30357, 86341], .contexts [
        ⟨83871, false, false, [], []⟩,
        ⟨13, true, false, [], [30357, 86341]⟩
      ]⟩,
    ⟨[31229], [30356], .source 15679⟩,
    ⟨[94317], [94315, 1], .source 47223⟩,
    ⟨[94315, 1], [94317], .contexts [
        ⟨83874, true, false, [], []⟩
      ]⟩,
    ⟨[94317, 1], [94315], .contexts [
        ⟨83875, true, false, [], [1]⟩,
        ⟨8, false, false, [94315], []⟩,
        ⟨83848, false, false, [], []⟩
      ]⟩,
    ⟨[94317], [94317], .contexts []⟩,
    ⟨[94317], [94317], .contexts []⟩,
    ⟨[94315, 1], [94317], .contexts [
        ⟨83875, false, false, [], []⟩,
        ⟨83877, false, false, [], []⟩,
        ⟨83878, false, false, [], []⟩,
        ⟨83878, false, false, [], []⟩
      ]⟩,
    ⟨[23705, 94317], [23705, 94317], .contexts []⟩,
    ⟨[23705, 94317], [23705, 94317], .contexts []⟩,
    ⟨[94317, 5], [23705, 94317], .contexts [
        ⟨83879, true, false, [], [5]⟩,
        ⟨98, false, false, [94315], []⟩,
        ⟨99, false, false, [94315], []⟩,
        ⟨83857, false, false, [], [1]⟩,
        ⟨83857, false, false, [], [1]⟩,
        ⟨83849, true, false, [], [5, 1]⟩,
        ⟨27, false, false, [89197], [1]⟩,
        ⟨30, false, false, [89197], [1]⟩,
        ⟨54731, false, false, [], [15, 1]⟩,
        ⟨83845, false, false, [23705], [1]⟩,
        ⟨83855, false, false, [], [1]⟩,
        ⟨83856, false, false, [], [1]⟩,
        ⟨83853, false, false, [23705], [1]⟩,
        ⟨83858, true, false, [], [94315, 1]⟩,
        ⟨83855, false, false, [], [1]⟩,
        ⟨83856, false, false, [], [1]⟩,
        ⟨83856, false, false, [], [1]⟩,
        ⟨83875, false, false, [23705], []⟩,
        ⟨83880, false, false, [], []⟩,
        ⟨83881, false, false, [], []⟩
      ]⟩,
    ⟨[23729, 83679], [23729, 83679], .contexts []⟩,
    ⟨[23729, 83679], [23729, 83679], .contexts []⟩,
    ⟨[94317, 7], [94317, 7], .contexts []⟩,
    ⟨[94317, 7], [23729, 83679], .contexts [
        ⟨83885, false, false, [], []⟩,
        ⟨83879, true, false, [], [7]⟩,
        ⟨104, false, false, [94315], []⟩,
        ⟨105, false, false, [94315], []⟩,
        ⟨83863, false, false, [], [1]⟩,
        ⟨83865, false, false, [], [1]⟩,
        ⟨83861, false, false, [], [1]⟩,
        ⟨83862, false, false, [], [1]⟩,
        ⟨83862, false, false, [], [1]⟩,
        ⟨22603, false, false, [23729], []⟩,
        ⟨83883, false, false, [], []⟩,
        ⟨83884, false, false, [], []⟩,
        ⟨34001, false, false, [23729], []⟩,
        ⟨83864, true, false, [], [83679]⟩
      ]⟩,
    ⟨[31231], [30357, 28159], .source 15680⟩,
    ⟨[31231, 92507], [31231, 92507], .contexts []⟩,
    ⟨[31231, 92507], [31231, 92507], .contexts []⟩,
    ⟨[94317, 13], [94317, 13], .contexts []⟩,
    ⟨[94317, 13], [31231, 92507], .contexts [
        ⟨83890, false, false, [], []⟩,
        ⟨83879, true, false, [], [13]⟩,
        ⟨115, false, false, [94315], []⟩,
        ⟨118, false, false, [94315], []⟩,
        ⟨83870, false, false, [], [1, 13, 1]⟩,
        ⟨83872, false, false, [], [1, 13, 1]⟩,
        ⟨83868, false, false, [], [1, 13, 1]⟩,
        ⟨83869, false, false, [], [1, 13, 1]⟩,
        ⟨83869, false, false, [], [1, 13, 1]⟩,
        ⟨36642, false, false, [30357], [13, 1]⟩,
        ⟨72917, false, false, [30357], [1]⟩,
        ⟨83887, true, false, [], [92509, 1]⟩,
        ⟨72840, false, false, [31231], []⟩,
        ⟨83888, false, false, [], []⟩,
        ⟨83889, false, false, [], []⟩,
        ⟨72835, false, false, [31231], []⟩
      ]⟩,
    ⟨[94317, 13], [31231, 92507], .contexts [
        ⟨83891, false, false, [], []⟩,
        ⟨13, true, false, [], [31231, 92507]⟩
      ]⟩,
    ⟨[31233], [31230], .source 15681⟩,
    ⟨[94319], [94317, 3], .source 47224⟩,
    ⟨[94317, 3], [94319], .contexts [
        ⟨83894, true, false, [], []⟩
      ]⟩,
    ⟨[94319, 3], [94317], .contexts [
        ⟨83895, true, false, [], [3]⟩,
        ⟨20, false, false, [94317], []⟩,
        ⟨83878, false, false, [], []⟩
      ]⟩,
    ⟨[94319], [94319], .contexts []⟩,
    ⟨[94319], [94319], .contexts []⟩,
    ⟨[94317, 3], [94319], .contexts [
        ⟨83895, false, false, [], []⟩,
        ⟨83897, false, false, [], []⟩,
        ⟨83898, false, false, [], []⟩,
        ⟨83898, false, false, [], []⟩
      ]⟩,
    ⟨[23719, 94317], [23719, 94317], .contexts []⟩,
    ⟨[23719, 94317], [23719, 94317], .contexts []⟩,
    ⟨[23719, 94317], [23719, 94317], .contexts []⟩,
    ⟨[23719, 94319], [23719, 94319], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1311. -/
def y322TCIndexRaw1311 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[23719, 94319], [23719, 94319], .contexts []⟩,
    ⟨[94317, 1, 3, 1, 3], [23719, 94319], .contexts [
        ⟨83876, false, false, [], [3, 1, 3]⟩,
        ⟨83847, false, false, [], [3, 1, 3]⟩,
        ⟨83848, false, false, [], [3, 1, 3]⟩,
        ⟨83848, false, false, [], [3, 1, 3]⟩,
        ⟨83849, true, false, [], [3, 1, 3]⟩,
        ⟨19, false, false, [89197], [1, 3]⟩,
        ⟨22, false, false, [89197], [1, 3]⟩,
        ⟨54768, false, false, [], [15, 1, 3]⟩,
        ⟨83845, false, false, [23719], [1, 3]⟩,
        ⟨83850, false, false, [], [1, 3]⟩,
        ⟨83851, false, false, [], [1, 3]⟩,
        ⟨83852, false, false, [], [1, 3]⟩,
        ⟨83853, false, false, [23719], [1, 3]⟩,
        ⟨83854, true, false, [], [94315, 1, 3]⟩,
        ⟨83850, false, false, [], [1, 3]⟩,
        ⟨83852, false, false, [], [1, 3]⟩,
        ⟨83852, false, false, [], [1, 3]⟩,
        ⟨83875, false, false, [23719], [3]⟩,
        ⟨83900, false, false, [], [3]⟩,
        ⟨83901, false, false, [], [3]⟩,
        ⟨83902, false, false, [], [3]⟩,
        ⟨83895, false, false, [23719], []⟩,
        ⟨83903, false, false, [], []⟩,
        ⟨83904, false, false, [], []⟩
      ]⟩,
    ⟨[23719, 94319], [23719, 94319], .contexts []⟩,
    ⟨[94319, 1], [94319, 1], .contexts []⟩,
    ⟨[23729, 83681], [23729, 83681], .contexts []⟩,
    ⟨[94319, 7], [23729, 83681], .contexts [
        ⟨83899, true, false, [], [7]⟩,
        ⟨140, false, false, [94317], []⟩,
        ⟨141, false, false, [94317], []⟩,
        ⟨83885, false, false, [], [3]⟩,
        ⟨83886, false, false, [], [3]⟩,
        ⟨83883, false, false, [], [3]⟩,
        ⟨83884, false, false, [], [3]⟩,
        ⟨83884, false, false, [], [3]⟩,
        ⟨22606, false, false, [23729], []⟩,
        ⟨83908, false, false, [], []⟩,
        ⟨22617, false, false, [23729], []⟩,
        ⟨83864, true, false, [], [83681]⟩
      ]⟩,
    ⟨[83681, 7], [23731, 94319], .contexts [
        ⟨83909, true, false, [23728], [7]⟩,
        ⟨38, false, false, [23728, 94319], []⟩,
        ⟨54724, true, false, [], [94319]⟩
      ]⟩,
    ⟨[31235], [31231, 24059], .source 15682⟩,
    ⟨[31235], [31235], .contexts []⟩,
    ⟨[31235], [31235], .contexts []⟩,
    ⟨[94319, 13], [31235, 85505], .contexts [
        ⟨83899, true, false, [], [13]⟩,
        ⟨147, false, false, [94317], []⟩,
        ⟨148, false, false, [94317], []⟩,
        ⟨83890, false, false, [], [3]⟩,
        ⟨83892, false, false, [], [3]⟩,
        ⟨83888, false, false, [], [3]⟩,
        ⟨83889, false, false, [], [3]⟩,
        ⟨83889, false, false, [], [3]⟩,
        ⟨72830, false, false, [31231], []⟩,
        ⟨83911, true, false, [], [85505]⟩,
        ⟨48378, false, false, [31235], []⟩,
        ⟨83913, true, false, [], [85505]⟩,
        ⟨83912, true, false, [], [85505]⟩,
        ⟨13, true, false, [], [31235, 85505]⟩
      ]⟩,
    ⟨[31237], [31234], .source 15683⟩,
    ⟨[85505, 13], [31237, 94319], .contexts [
        ⟨83914, true, false, [31234], [13]⟩,
        ⟨59, false, false, [31234, 94319], []⟩,
        ⟨83915, true, false, [], [94319]⟩
      ]⟩,
    ⟨[94321], [94319, 5], .source 47225⟩,
    ⟨[94319, 5], [94321], .contexts [
        ⟨83917, true, false, [], []⟩
      ]⟩,
    ⟨[94321, 5], [94319], .contexts [
        ⟨83918, true, false, [], [5]⟩,
        ⟨28, false, false, [94319], []⟩,
        ⟨83898, false, false, [], []⟩
      ]⟩,
    ⟨[94321], [94321], .contexts []⟩,
    ⟨[94321], [94321], .contexts []⟩,
    ⟨[94319, 5], [94321], .contexts [
        ⟨83918, false, false, [], []⟩,
        ⟨83920, false, false, [], []⟩,
        ⟨83921, false, false, [], []⟩,
        ⟨83921, false, false, [], []⟩
      ]⟩,
    ⟨[23719, 94321], [23719, 94321], .contexts []⟩,
    ⟨[23719, 94321], [23719, 94321], .contexts []⟩,
    ⟨[94321], [94321], .contexts []⟩,
    ⟨[94321, 1], [23719, 94321], .contexts [
        ⟨83922, true, false, [], [1]⟩,
        ⟨161, false, false, [94319], []⟩,
        ⟨162, false, false, [94319], []⟩,
        ⟨83907, false, false, [], [5]⟩,
        ⟨83907, false, false, [], [5]⟩,
        ⟨83899, true, false, [], [1, 5]⟩,
        ⟨130, false, false, [94317], [5]⟩,
        ⟨133, false, false, [94317], [5]⟩,
        ⟨83905, false, false, [], [5]⟩,
        ⟨83906, false, false, [], [5]⟩,
        ⟨83854, true, false, [], [94319, 5]⟩,
        ⟨83903, false, false, [], [5]⟩,
        ⟨83906, false, false, [], [5]⟩,
        ⟨83906, false, false, [], [5]⟩,
        ⟨83918, false, false, [23719], []⟩,
        ⟨83923, false, false, [], []⟩,
        ⟨83924, false, false, [], []⟩,
        ⟨83925, false, false, [23719], []⟩
      ]⟩,
    ⟨[94321, 1], [23719, 94321], .contexts [
        ⟨83926, false, false, [], []⟩,
        ⟨83854, true, false, [], [94321]⟩
      ]⟩,
    ⟨[23705, 94321], [23705, 94321], .contexts []⟩,
    ⟨[23705, 94321], [23705, 94321], .contexts []⟩,
    ⟨[94321, 3], [94321, 3], .contexts []⟩,
    ⟨[94321, 3], [23705, 94321], .contexts [
        ⟨83930, false, false, [], []⟩,
        ⟨83922, true, false, [], [3]⟩,
        ⟨166, false, false, [94319], []⟩,
        ⟨169, false, false, [94319], []⟩,
        ⟨83896, false, false, [], [5, 3, 5]⟩,
        ⟨83877, false, false, [], [5, 3, 5]⟩,
        ⟨83878, false, false, [], [5, 3, 5]⟩,
        ⟨83878, false, false, [], [5, 3, 5]⟩,
        ⟨83882, false, false, [], [3, 5]⟩,
        ⟨83858, true, false, [], [94317, 3, 5]⟩,
        ⟨83880, false, false, [], [3, 5]⟩,
        ⟨83881, false, false, [], [3, 5]⟩,
        ⟨83881, false, false, [], [3, 5]⟩,
        ⟨83895, false, false, [23705], [5]⟩,
        ⟨83918, false, false, [23705], []⟩,
        ⟨83928, false, false, [], []⟩,
        ⟨83929, false, false, [], []⟩,
        ⟨83925, false, false, [23705], []⟩
      ]⟩,
    ⟨[94321, 3], [23705, 94321], .contexts [
        ⟨83931, false, false, [], []⟩,
        ⟨83858, true, false, [], [94321]⟩
      ]⟩,
    ⟨[94323], [94321, 9], .source 47226⟩,
    ⟨[94321, 9], [94323], .contexts [
        ⟨83933, true, false, [], []⟩
      ]⟩,
    ⟨[94323, 9], [94321], .contexts [
        ⟨83934, true, false, [], [9]⟩,
        ⟨46, false, false, [94321], []⟩,
        ⟨83921, false, false, [], []⟩
      ]⟩,
    ⟨[94323], [94323], .contexts []⟩,
    ⟨[94323], [94323], .contexts []⟩,
    ⟨[23705, 94323], [23705, 94323], .contexts []⟩,
    ⟨[94323], [94323], .contexts []⟩,
    ⟨[94323, 3], [23705, 94323], .contexts [
        ⟨83937, true, false, [], [3]⟩,
        ⟨83937, true, false, [], [3]⟩,
        ⟨83936, true, false, [], [3]⟩,
        ⟨83934, true, false, [], [3]⟩,
        ⟨196, false, false, [94321], []⟩,
        ⟨197, false, false, [94321], []⟩,
        ⟨83930, false, false, [], [9]⟩,
        ⟨83932, false, false, [], [9]⟩,
        ⟨83928, false, false, [], [9]⟩,
        ⟨83929, false, false, [], [9]⟩,
        ⟨83929, false, false, [], [9]⟩,
        ⟨83934, false, false, [23705], []⟩,
        ⟨83938, false, false, [], []⟩,
        ⟨83939, false, false, [23705], []⟩,
        ⟨83858, true, false, [], [94323]⟩
      ]⟩,
    ⟨[94325], [94323, 11], .source 47227⟩,
    ⟨[94323, 11], [94325], .contexts [
        ⟨83941, true, false, [], []⟩
      ]⟩,
    ⟨[94325], [94325], .contexts []⟩,
    ⟨[94327], [94325, 1], .source 47228⟩,
    ⟨[94325, 1], [94327], .contexts [
        ⟨83944, true, false, [], []⟩
      ]⟩,
    ⟨[94329], [94327, 13], .source 47229⟩,
    ⟨[94327, 13], [94329], .contexts [
        ⟨83946, true, false, [], []⟩
      ]⟩,
    ⟨[94327], [94327], .contexts []⟩,
    ⟨[94329, 13], [94327], .contexts [
        ⟨83947, true, false, [], [13]⟩,
        ⟨59, false, false, [94327], []⟩,
        ⟨83948, false, false, [], []⟩
      ]⟩,
    ⟨[94331], [94329, 15], .source 47230⟩,
    ⟨[94329, 15], [94331], .contexts [
        ⟨83950, true, false, [], []⟩
      ]⟩,
    ⟨[94329], [94329], .contexts []⟩,
    ⟨[94331, 15], [94329], .contexts [
        ⟨83951, true, false, [], [15]⟩,
        ⟨1, false, false, [94329], []⟩,
        ⟨83952, false, false, [], []⟩
      ]⟩,
    ⟨[94333], [94331, 1], .source 47231⟩,
    ⟨[94331, 1], [94333], .contexts [
        ⟨83954, true, false, [], []⟩
      ]⟩,
    ⟨[94331], [94331], .contexts []⟩,
    ⟨[94333, 1], [94331], .contexts [
        ⟨83955, true, false, [], [1]⟩,
        ⟨8, false, false, [94331], []⟩,
        ⟨83956, false, false, [], []⟩
      ]⟩,
    ⟨[94335], [94333, 3], .source 47232⟩,
    ⟨[94333, 3], [94335], .contexts [
        ⟨83958, true, false, [], []⟩
      ]⟩,
    ⟨[94333], [94333], .contexts []⟩,
    ⟨[94335, 3], [94333], .contexts [
        ⟨83959, true, false, [], [3]⟩,
        ⟨20, false, false, [94333], []⟩,
        ⟨83960, false, false, [], []⟩
      ]⟩,
    ⟨[94337], [94335, 5], .source 47233⟩,
    ⟨[94335, 5], [94337], .contexts [
        ⟨83962, true, false, [], []⟩
      ]⟩,
    ⟨[94335], [94335], .contexts []⟩,
    ⟨[94339], [94337, 1], .source 47234⟩,
    ⟨[94337, 1], [94339], .contexts [
        ⟨83965, true, false, [], []⟩
      ]⟩,
    ⟨[94337], [94337], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1312. -/
def y322TCIndexRaw1312 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94341], [94339, 9], .source 47235⟩,
    ⟨[94339, 9], [94341], .contexts [
        ⟨83968, true, false, [], []⟩
      ]⟩,
    ⟨[94339], [94339], .contexts []⟩,
    ⟨[94341, 9], [94339], .contexts [
        ⟨83969, true, false, [], [9]⟩,
        ⟨46, false, false, [94339], []⟩,
        ⟨83970, false, false, [], []⟩
      ]⟩,
    ⟨[94343], [94341, 11], .source 47236⟩,
    ⟨[94341, 11], [94343], .contexts [
        ⟨83972, true, false, [], []⟩
      ]⟩,
    ⟨[94341], [94341], .contexts []⟩,
    ⟨[94345], [94343, 1], .source 47237⟩,
    ⟨[94343, 1], [94345], .contexts [
        ⟨83975, true, false, [], []⟩
      ]⟩,
    ⟨[94343], [94343], .contexts []⟩,
    ⟨[94347], [94345, 13], .source 47238⟩,
    ⟨[94345, 13], [94347], .contexts [
        ⟨83978, true, false, [], []⟩
      ]⟩,
    ⟨[94345], [94345], .contexts []⟩,
    ⟨[94349], [94347, 15], .source 47239⟩,
    ⟨[94347, 15], [94349], .contexts [
        ⟨83981, true, false, [], []⟩
      ]⟩,
    ⟨[94347], [94347], .contexts []⟩,
    ⟨[94351], [94349, 1], .source 47240⟩,
    ⟨[94349, 1], [94351], .contexts [
        ⟨83984, true, false, [], []⟩
      ]⟩,
    ⟨[94349], [94349], .contexts []⟩,
    ⟨[94353], [94351, 3], .source 47241⟩,
    ⟨[94351, 3], [94353], .contexts [
        ⟨83987, true, false, [], []⟩
      ]⟩,
    ⟨[94351], [94351], .contexts []⟩,
    ⟨[94355], [94353, 5], .source 47242⟩,
    ⟨[94353, 5], [94355], .contexts [
        ⟨83990, true, false, [], []⟩
      ]⟩,
    ⟨[94353], [94353], .contexts []⟩,
    ⟨[94357], [94355, 1], .source 47243⟩,
    ⟨[94355, 1], [94357], .contexts [
        ⟨83993, true, false, [], []⟩
      ]⟩,
    ⟨[94355], [94355], .contexts []⟩,
    ⟨[94357, 1], [94355], .contexts [
        ⟨83994, true, false, [], [1]⟩,
        ⟨8, false, false, [94355], []⟩,
        ⟨83995, false, false, [], []⟩
      ]⟩,
    ⟨[94359], [94357, 9], .source 47244⟩,
    ⟨[94357, 9], [94359], .contexts [
        ⟨83997, true, false, [], []⟩
      ]⟩,
    ⟨[94357], [94357], .contexts []⟩,
    ⟨[94359, 9], [94357], .contexts [
        ⟨83998, true, false, [], [9]⟩,
        ⟨46, false, false, [94357], []⟩,
        ⟨83999, false, false, [], []⟩
      ]⟩,
    ⟨[94361], [94359, 11], .source 47245⟩,
    ⟨[94359, 11], [94361], .contexts [
        ⟨84001, true, false, [], []⟩
      ]⟩,
    ⟨[94359], [94359], .contexts []⟩,
    ⟨[94361, 11], [94359], .contexts [
        ⟨84002, true, false, [], [11]⟩,
        ⟨53, false, false, [94359], []⟩,
        ⟨84003, false, false, [], []⟩
      ]⟩,
    ⟨[94363], [94361, 1], .source 47246⟩,
    ⟨[94361, 1], [94363], .contexts [
        ⟨84005, true, false, [], []⟩
      ]⟩,
    ⟨[94361], [94361], .contexts []⟩,
    ⟨[94365], [94363, 13], .source 47247⟩,
    ⟨[94363, 13], [94365], .contexts [
        ⟨84008, true, false, [], []⟩
      ]⟩,
    ⟨[94363], [94363], .contexts []⟩,
    ⟨[94365, 13], [94363], .contexts [
        ⟨84009, true, false, [], [13]⟩,
        ⟨59, false, false, [94363], []⟩,
        ⟨84010, false, false, [], []⟩
      ]⟩,
    ⟨[94367], [94365, 15], .source 47248⟩,
    ⟨[94365, 15], [94367], .contexts [
        ⟨84012, true, false, [], []⟩
      ]⟩,
    ⟨[94365], [94365], .contexts []⟩,
    ⟨[94369], [94367, 1], .source 47249⟩,
    ⟨[94367, 1], [94369], .contexts [
        ⟨84015, true, false, [], []⟩
      ]⟩,
    ⟨[94367], [94367], .contexts []⟩,
    ⟨[94371], [94369, 3], .source 47250⟩,
    ⟨[94369, 3], [94371], .contexts [
        ⟨84018, true, false, [], []⟩
      ]⟩,
    ⟨[94369], [94369], .contexts []⟩,
    ⟨[94373], [94371, 5], .source 47251⟩,
    ⟨[94371, 5], [94373], .contexts [
        ⟨84021, true, false, [], []⟩
      ]⟩,
    ⟨[94371], [94371], .contexts []⟩,
    ⟨[94375], [94373, 1], .source 47252⟩,
    ⟨[94373, 1], [94375], .contexts [
        ⟨84024, true, false, [], []⟩
      ]⟩,
    ⟨[94373], [94373], .contexts []⟩,
    ⟨[94377], [94375, 9], .source 47253⟩,
    ⟨[94375, 9], [94377], .contexts [
        ⟨84027, true, false, [], []⟩
      ]⟩,
    ⟨[94375], [94375], .contexts []⟩,
    ⟨[94379], [94377, 11], .source 47254⟩,
    ⟨[94377, 11], [94379], .contexts [
        ⟨84030, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1313. -/
def y322TCIndexRaw1313 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94377], [94377], .contexts []⟩,
    ⟨[94381], [94379, 1], .source 47255⟩,
    ⟨[94379, 1], [94381], .contexts [
        ⟨84033, true, false, [], []⟩
      ]⟩,
    ⟨[94379], [94379], .contexts []⟩,
    ⟨[94381, 1], [94379], .contexts [
        ⟨84034, true, false, [], [1]⟩,
        ⟨8, false, false, [94379], []⟩,
        ⟨84035, false, false, [], []⟩
      ]⟩,
    ⟨[94383], [94381, 13], .source 47256⟩,
    ⟨[94381, 13], [94383], .contexts [
        ⟨84037, true, false, [], []⟩
      ]⟩,
    ⟨[94381], [94381], .contexts []⟩,
    ⟨[94385], [94383, 15], .source 47257⟩,
    ⟨[94383, 15], [94385], .contexts [
        ⟨84040, true, false, [], []⟩
      ]⟩,
    ⟨[94383], [94383], .contexts []⟩,
    ⟨[94387], [94385, 1], .source 47258⟩,
    ⟨[94385, 1], [94387], .contexts [
        ⟨84043, true, false, [], []⟩
      ]⟩,
    ⟨[94385], [94385], .contexts []⟩,
    ⟨[94389], [94387, 3], .source 47259⟩,
    ⟨[94387, 3], [94389], .contexts [
        ⟨84046, true, false, [], []⟩
      ]⟩,
    ⟨[94387], [94387], .contexts []⟩,
    ⟨[94389, 3], [94387], .contexts [
        ⟨84047, true, false, [], [3]⟩,
        ⟨20, false, false, [94387], []⟩,
        ⟨84048, false, false, [], []⟩
      ]⟩,
    ⟨[94391], [94389, 5], .source 47260⟩,
    ⟨[94389, 5], [94391], .contexts [
        ⟨84050, true, false, [], []⟩
      ]⟩,
    ⟨[94389], [94389], .contexts []⟩,
    ⟨[94393], [94391, 1], .source 47261⟩,
    ⟨[94391, 1], [94393], .contexts [
        ⟨84053, true, false, [], []⟩
      ]⟩,
    ⟨[94391], [94391], .contexts []⟩,
    ⟨[94395], [94393, 9], .source 47262⟩,
    ⟨[94393, 9], [94395], .contexts [
        ⟨84056, true, false, [], []⟩
      ]⟩,
    ⟨[94393], [94393], .contexts []⟩,
    ⟨[94397], [94395, 11], .source 47263⟩,
    ⟨[94395], [94395], .contexts []⟩,
    ⟨[94397, 11], [94395], .contexts [
        ⟨84059, false, false, [], [11]⟩,
        ⟨53, false, false, [94395], []⟩,
        ⟨84060, false, false, [], []⟩
      ]⟩,
    ⟨[94399], [94397, 1], .source 47264⟩,
    ⟨[94397], [94397], .contexts []⟩,
    ⟨[94399, 1], [94397], .contexts [
        ⟨84062, false, false, [], [1]⟩,
        ⟨8, false, false, [94397], []⟩,
        ⟨84063, false, false, [], []⟩
      ]⟩,
    ⟨[94401], [94399, 13], .source 47265⟩,
    ⟨[94399, 13], [94401], .contexts [
        ⟨84065, true, false, [], []⟩
      ]⟩,
    ⟨[94399], [94399], .contexts []⟩,
    ⟨[94401, 13], [94399], .contexts [
        ⟨84066, true, false, [], [13]⟩,
        ⟨59, false, false, [94399], []⟩,
        ⟨84067, false, false, [], []⟩
      ]⟩,
    ⟨[94403], [94401, 15], .source 47266⟩,
    ⟨[94401, 15], [94403], .contexts [
        ⟨84069, true, false, [], []⟩
      ]⟩,
    ⟨[94401], [94401], .contexts []⟩,
    ⟨[94403, 15], [94401], .contexts [
        ⟨84070, true, false, [], [15]⟩,
        ⟨1, false, false, [94401], []⟩,
        ⟨84071, false, false, [], []⟩
      ]⟩,
    ⟨[94405], [94403, 1], .source 47267⟩,
    ⟨[94403, 1], [94405], .contexts [
        ⟨84073, true, false, [], []⟩
      ]⟩,
    ⟨[94403], [94403], .contexts []⟩,
    ⟨[94405, 1], [94403], .contexts [
        ⟨84074, true, false, [], [1]⟩,
        ⟨8, false, false, [94403], []⟩,
        ⟨84075, false, false, [], []⟩
      ]⟩,
    ⟨[94407], [94405, 3], .source 47268⟩,
    ⟨[94405, 3], [94407], .contexts [
        ⟨84077, true, false, [], []⟩
      ]⟩,
    ⟨[94405], [94405], .contexts []⟩,
    ⟨[94407, 3], [94405], .contexts [
        ⟨84078, true, false, [], [3]⟩,
        ⟨20, false, false, [94405], []⟩,
        ⟨84079, false, false, [], []⟩
      ]⟩,
    ⟨[94409], [94407, 5], .source 47269⟩,
    ⟨[94407, 5], [94409], .contexts [
        ⟨84081, true, false, [], []⟩
      ]⟩,
    ⟨[94407], [94407], .contexts []⟩,
    ⟨[94409, 5], [94407], .contexts [
        ⟨84082, true, false, [], [5]⟩,
        ⟨28, false, false, [94407], []⟩,
        ⟨84083, false, false, [], []⟩
      ]⟩,
    ⟨[94411], [94409, 1], .source 47270⟩,
    ⟨[94409, 1], [94411], .contexts [
        ⟨84085, true, false, [], []⟩
      ]⟩,
    ⟨[94409], [94409], .contexts []⟩,
    ⟨[94411, 1], [94409], .contexts [
        ⟨84086, true, false, [], [1]⟩,
        ⟨8, false, false, [94409], []⟩,
        ⟨84087, false, false, [], []⟩
      ]⟩,
    ⟨[94413], [94411, 9], .source 47271⟩,
    ⟨[94411, 9], [94413], .contexts [
        ⟨84089, true, false, [], []⟩
      ]⟩,
    ⟨[94411], [94411], .contexts []⟩,
    ⟨[94413, 9], [94411], .contexts [
        ⟨84090, true, false, [], [9]⟩,
        ⟨46, false, false, [94411], []⟩,
        ⟨84091, false, false, [], []⟩
      ]⟩,
    ⟨[94415], [94413, 11], .source 47272⟩,
    ⟨[94413, 11], [94415], .contexts [
        ⟨84093, true, false, [], []⟩
      ]⟩,
    ⟨[94413], [94413], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1314. -/
def y322TCIndexRaw1314 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94415, 11], [94413], .contexts [
        ⟨84094, true, false, [], [11]⟩,
        ⟨53, false, false, [94413], []⟩,
        ⟨84095, false, false, [], []⟩
      ]⟩,
    ⟨[94417], [94415, 1], .source 47273⟩,
    ⟨[94415, 1], [94417], .contexts [
        ⟨84097, true, false, [], []⟩
      ]⟩,
    ⟨[94415], [94415], .contexts []⟩,
    ⟨[94417, 1], [94415], .contexts [
        ⟨84098, true, false, [], [1]⟩,
        ⟨8, false, false, [94415], []⟩,
        ⟨84099, false, false, [], []⟩
      ]⟩,
    ⟨[94419], [94417, 13], .source 47274⟩,
    ⟨[94417, 13], [94419], .contexts [
        ⟨84101, true, false, [], []⟩
      ]⟩,
    ⟨[94417], [94417], .contexts []⟩,
    ⟨[94419, 13], [94417], .contexts [
        ⟨84102, true, false, [], [13]⟩,
        ⟨59, false, false, [94417], []⟩,
        ⟨84103, false, false, [], []⟩
      ]⟩,
    ⟨[94421], [94419, 15], .source 47275⟩,
    ⟨[94419, 15], [94421], .contexts [
        ⟨84105, true, false, [], []⟩
      ]⟩,
    ⟨[94419], [94419], .contexts []⟩,
    ⟨[94421, 15], [94419], .contexts [
        ⟨84106, true, false, [], [15]⟩,
        ⟨1, false, false, [94419], []⟩,
        ⟨84107, false, false, [], []⟩
      ]⟩,
    ⟨[94423], [94421, 1], .source 47276⟩,
    ⟨[94421, 1], [94423], .contexts [
        ⟨84109, true, false, [], []⟩
      ]⟩,
    ⟨[94421], [94421], .contexts []⟩,
    ⟨[94423, 1], [94421], .contexts [
        ⟨84110, true, false, [], [1]⟩,
        ⟨8, false, false, [94421], []⟩,
        ⟨84111, false, false, [], []⟩
      ]⟩,
    ⟨[94425], [94423, 3], .source 47277⟩,
    ⟨[94423], [94423], .contexts []⟩,
    ⟨[94425, 3], [94423], .contexts [
        ⟨84113, false, false, [], [3]⟩,
        ⟨20, false, false, [94423], []⟩,
        ⟨84114, false, false, [], []⟩
      ]⟩,
    ⟨[94427], [94425, 5], .source 47278⟩,
    ⟨[94425], [94425], .contexts []⟩,
    ⟨[94427, 5], [94425], .contexts [
        ⟨84116, false, false, [], [5]⟩,
        ⟨28, false, false, [94425], []⟩,
        ⟨84117, false, false, [], []⟩
      ]⟩,
    ⟨[94429], [94427, 1], .source 47279⟩,
    ⟨[94427, 1], [94429], .contexts [
        ⟨84119, true, false, [], []⟩
      ]⟩,
    ⟨[94427], [94427], .contexts []⟩,
    ⟨[94429, 1], [94427], .contexts [
        ⟨84120, true, false, [], [1]⟩,
        ⟨8, false, false, [94427], []⟩,
        ⟨84121, false, false, [], []⟩
      ]⟩,
    ⟨[94429], [94429], .contexts []⟩,
    ⟨[94429], [94429], .contexts []⟩,
    ⟨[94425], [94425], .contexts []⟩,
    ⟨[94423], [94423], .contexts []⟩,
    ⟨[94421], [94421], .contexts []⟩,
    ⟨[94421, 15], [94419], .contexts [
        ⟨84108, false, false, [], []⟩
      ]⟩,
    ⟨[94419], [94419], .contexts []⟩,
    ⟨[94419, 13], [94417], .contexts [
        ⟨84104, false, false, [], []⟩
      ]⟩,
    ⟨[94417], [94417], .contexts []⟩,
    ⟨[94427, 5, 3, 1, 15, 13], [94417], .contexts [
        ⟨84118, false, false, [], [3, 1, 15, 13]⟩,
        ⟨84125, false, false, [], [3, 1, 15, 13]⟩,
        ⟨84117, false, false, [], [3, 1, 15, 13]⟩,
        ⟨84117, false, false, [], [3, 1, 15, 13]⟩,
        ⟨84115, false, false, [], [1, 15, 13]⟩,
        ⟨84126, false, false, [], [1, 15, 13]⟩,
        ⟨84114, false, false, [], [1, 15, 13]⟩,
        ⟨84114, false, false, [], [1, 15, 13]⟩,
        ⟨84112, false, false, [], [15, 13]⟩,
        ⟨84127, false, false, [], [15, 13]⟩,
        ⟨84111, false, false, [], [15, 13]⟩,
        ⟨84111, false, false, [], [15, 13]⟩,
        ⟨84128, false, false, [], [13]⟩,
        ⟨84129, false, false, [], [13]⟩,
        ⟨84107, false, false, [], [13]⟩,
        ⟨84107, false, false, [], [13]⟩,
        ⟨84130, false, false, [], []⟩,
        ⟨84131, false, false, [], []⟩,
        ⟨84103, false, false, [], []⟩,
        ⟨84103, false, false, [], []⟩
      ]⟩,
    ⟨[94417, 1], [94415], .contexts [
        ⟨84100, false, false, [], []⟩
      ]⟩,
    ⟨[94415], [94415], .contexts []⟩,
    ⟨[94415, 11], [94413], .contexts [
        ⟨84096, false, false, [], []⟩
      ]⟩,
    ⟨[94413], [94413], .contexts []⟩,
    ⟨[94413, 9], [94411], .contexts [
        ⟨84092, false, false, [], []⟩
      ]⟩,
    ⟨[94411], [94411], .contexts []⟩,
    ⟨[94411, 1], [94409], .contexts [
        ⟨84088, false, false, [], []⟩
      ]⟩,
    ⟨[94409], [94409], .contexts []⟩,
    ⟨[94409, 5], [94407], .contexts [
        ⟨84084, false, false, [], []⟩
      ]⟩,
    ⟨[94407], [94407], .contexts []⟩,
    ⟨[94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5], [94407], .contexts [
        ⟨84132, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨84133, false, false, [], [11, 9, 1, 5]⟩,
        ⟨84134, false, false, [], [11, 9, 1, 5]⟩,
        ⟨84099, false, false, [], [11, 9, 1, 5]⟩,
        ⟨84099, false, false, [], [11, 9, 1, 5]⟩,
        ⟨84135, false, false, [], [9, 1, 5]⟩,
        ⟨84136, false, false, [], [9, 1, 5]⟩,
        ⟨84095, false, false, [], [9, 1, 5]⟩,
        ⟨84095, false, false, [], [9, 1, 5]⟩,
        ⟨84137, false, false, [], [1, 5]⟩,
        ⟨84138, false, false, [], [1, 5]⟩,
        ⟨84091, false, false, [], [1, 5]⟩,
        ⟨84091, false, false, [], [1, 5]⟩,
        ⟨84139, false, false, [], [5]⟩,
        ⟨84140, false, false, [], [5]⟩,
        ⟨84087, false, false, [], [5]⟩,
        ⟨84087, false, false, [], [5]⟩,
        ⟨84141, false, false, [], []⟩,
        ⟨84142, false, false, [], []⟩,
        ⟨84083, false, false, [], []⟩,
        ⟨84083, false, false, [], []⟩
      ]⟩,
    ⟨[94407, 3], [94405], .contexts [
        ⟨84080, false, false, [], []⟩
      ]⟩,
    ⟨[94405], [94405], .contexts []⟩,
    ⟨[94405, 1], [94403], .contexts [
        ⟨84076, false, false, [], []⟩
      ]⟩,
    ⟨[94403], [94403], .contexts []⟩,
    ⟨[94403, 15], [94401], .contexts [
        ⟨84072, false, false, [], []⟩
      ]⟩,
    ⟨[94401], [94401], .contexts []⟩,
    ⟨[94401, 13], [94399], .contexts [
        ⟨84068, false, false, [], []⟩
      ]⟩,
    ⟨[94399], [94399], .contexts []⟩,
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1
    ], [94397], .contexts [
        ⟨84143, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨84144, false, false, [], [1, 15, 13, 1]⟩,
        ⟨84145, false, false, [], [1, 15, 13, 1]⟩,
        ⟨84079, false, false, [], [1, 15, 13, 1]⟩,
        ⟨84079, false, false, [], [1, 15, 13, 1]⟩,
        ⟨84146, false, false, [], [15, 13, 1]⟩,
        ⟨84147, false, false, [], [15, 13, 1]⟩,
        ⟨84075, false, false, [], [15, 13, 1]⟩,
        ⟨84075, false, false, [], [15, 13, 1]⟩,
        ⟨84148, false, false, [], [13, 1]⟩,
        ⟨84149, false, false, [], [13, 1]⟩,
        ⟨84071, false, false, [], [13, 1]⟩,
        ⟨84071, false, false, [], [13, 1]⟩,
        ⟨84150, false, false, [], [1]⟩,
        ⟨84151, false, false, [], [1]⟩,
        ⟨84067, false, false, [], [1]⟩,
        ⟨84067, false, false, [], [1]⟩,
        ⟨84064, false, false, [], []⟩,
        ⟨84063, false, false, [], []⟩,
        ⟨84063, false, false, [], []⟩
      ]⟩,
    ⟨[94395], [94395], .contexts []⟩,
    ⟨[94393], [94393], .contexts []⟩,
    ⟨[94389], [94389], .contexts []⟩,
    ⟨[94387], [94387], .contexts []⟩,
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [94387], .contexts [
        ⟨84152, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨84061, false, false, [], [9, 1, 5, 3]⟩,
        ⟨84153, false, false, [], [9, 1, 5, 3]⟩,
        ⟨84060, false, false, [], [9, 1, 5, 3]⟩,
        ⟨84060, false, false, [], [9, 1, 5, 3]⟩,
        ⟨84057, true, false, [], [9, 1, 5, 3]⟩,
        ⟨46, false, false, [94393], [1, 5, 3]⟩,
        ⟨84058, false, false, [], [1, 5, 3]⟩,
        ⟨84154, false, false, [], [1, 5, 3]⟩,
        ⟨84058, false, false, [], [1, 5, 3]⟩,
        ⟨84058, false, false, [], [1, 5, 3]⟩,
        ⟨84054, true, false, [], [1, 5, 3]⟩,
        ⟨8, false, false, [94391], [5, 3]⟩,
        ⟨84055, false, false, [], [5, 3]⟩,
        ⟨84055, false, false, [], [5, 3]⟩,
        ⟨84055, false, false, [], [5, 3]⟩,
        ⟨84051, true, false, [], [5, 3]⟩,
        ⟨28, false, false, [94389], [3]⟩,
        ⟨84052, false, false, [], [3]⟩,
        ⟨84155, false, false, [], [3]⟩,
        ⟨84052, false, false, [], [3]⟩,
        ⟨84052, false, false, [], [3]⟩,
        ⟨84049, false, false, [], []⟩,
        ⟨84156, false, false, [], []⟩,
        ⟨84048, false, false, [], []⟩,
        ⟨84048, false, false, [], []⟩
      ]⟩,
    ⟨[94385], [94385], .contexts []⟩,
    ⟨[94381], [94381], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1315. -/
def y322TCIndexRaw1315 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94379], [94379], .contexts []⟩,
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1
    ], [94379], .contexts [
        ⟨84157, false, false, [], [1, 15, 13, 1]⟩,
        ⟨84044, true, false, [], [1, 15, 13, 1]⟩,
        ⟨8, false, false, [94385], [15, 13, 1]⟩,
        ⟨84045, false, false, [], [15, 13, 1]⟩,
        ⟨84158, false, false, [], [15, 13, 1]⟩,
        ⟨84045, false, false, [], [15, 13, 1]⟩,
        ⟨84045, false, false, [], [15, 13, 1]⟩,
        ⟨84041, true, false, [], [15, 13, 1]⟩,
        ⟨1, false, false, [94383], [13, 1]⟩,
        ⟨84042, false, false, [], [13, 1]⟩,
        ⟨84042, false, false, [], [13, 1]⟩,
        ⟨84042, false, false, [], [13, 1]⟩,
        ⟨84038, true, false, [], [13, 1]⟩,
        ⟨59, false, false, [94381], [1]⟩,
        ⟨84039, false, false, [], [1]⟩,
        ⟨84159, false, false, [], [1]⟩,
        ⟨84039, false, false, [], [1]⟩,
        ⟨84039, false, false, [], [1]⟩,
        ⟨84036, false, false, [], []⟩,
        ⟨84160, false, false, [], []⟩,
        ⟨84035, false, false, [], []⟩,
        ⟨84035, false, false, [], []⟩
      ]⟩,
    ⟨[94377], [94377], .contexts []⟩,
    ⟨[94375], [94375], .contexts []⟩,
    ⟨[94373], [94373], .contexts []⟩,
    ⟨[94371], [94371], .contexts []⟩,
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5
    ], [94371], .contexts [
        ⟨84161, false, false, [], [11, 9, 1, 5]⟩,
        ⟨84031, true, false, [], [11, 9, 1, 5]⟩,
        ⟨53, false, false, [94377], [9, 1, 5]⟩,
        ⟨84032, false, false, [], [9, 1, 5]⟩,
        ⟨84162, false, false, [], [9, 1, 5]⟩,
        ⟨84032, false, false, [], [9, 1, 5]⟩,
        ⟨84032, false, false, [], [9, 1, 5]⟩,
        ⟨84028, true, false, [], [9, 1, 5]⟩,
        ⟨46, false, false, [94375], [1, 5]⟩,
        ⟨84029, false, false, [], [1, 5]⟩,
        ⟨84163, false, false, [], [1, 5]⟩,
        ⟨84029, false, false, [], [1, 5]⟩,
        ⟨84029, false, false, [], [1, 5]⟩,
        ⟨84025, true, false, [], [1, 5]⟩,
        ⟨8, false, false, [94373], [5]⟩,
        ⟨84026, false, false, [], [5]⟩,
        ⟨84164, false, false, [], [5]⟩,
        ⟨84026, false, false, [], [5]⟩,
        ⟨84026, false, false, [], [5]⟩,
        ⟨84022, true, false, [], [5]⟩,
        ⟨28, false, false, [94371], []⟩,
        ⟨84023, false, false, [], []⟩,
        ⟨84165, false, false, [], []⟩,
        ⟨84023, false, false, [], []⟩,
        ⟨84023, false, false, [], []⟩
      ]⟩,
    ⟨[94369], [94369], .contexts []⟩,
    ⟨[94367], [94367], .contexts []⟩,
    ⟨[94365], [94365], .contexts []⟩,
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [94363], .contexts [
        ⟨84166, false, false, [], [3, 1, 15, 13]⟩,
        ⟨84019, true, false, [], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [94369], [1, 15, 13]⟩,
        ⟨84020, false, false, [], [1, 15, 13]⟩,
        ⟨84167, false, false, [], [1, 15, 13]⟩,
        ⟨84020, false, false, [], [1, 15, 13]⟩,
        ⟨84020, false, false, [], [1, 15, 13]⟩,
        ⟨84016, true, false, [], [1, 15, 13]⟩,
        ⟨8, false, false, [94367], [15, 13]⟩,
        ⟨84017, false, false, [], [15, 13]⟩,
        ⟨84168, false, false, [], [15, 13]⟩,
        ⟨84017, false, false, [], [15, 13]⟩,
        ⟨84017, false, false, [], [15, 13]⟩,
        ⟨84013, true, false, [], [15, 13]⟩,
        ⟨1, false, false, [94365], [13]⟩,
        ⟨84014, false, false, [], [13]⟩,
        ⟨84169, false, false, [], [13]⟩,
        ⟨84014, false, false, [], [13]⟩,
        ⟨84014, false, false, [], [13]⟩,
        ⟨84011, false, false, [], []⟩,
        ⟨84010, false, false, [], []⟩,
        ⟨84010, false, false, [], []⟩
      ]⟩,
    ⟨[94361], [94361], .contexts []⟩,
    ⟨[94361, 11], [94359], .contexts [
        ⟨84004, false, false, [], []⟩
      ]⟩,
    ⟨[94359], [94359], .contexts []⟩,
    ⟨[94357], [94357], .contexts []⟩,
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1
    ], [94355], .contexts [
        ⟨84170, false, false, [], [1, 11, 9, 1]⟩,
        ⟨84006, true, false, [], [1, 11, 9, 1]⟩,
        ⟨8, false, false, [94361], [11, 9, 1]⟩,
        ⟨84007, false, false, [], [11, 9, 1]⟩,
        ⟨84171, false, false, [], [11, 9, 1]⟩,
        ⟨84007, false, false, [], [11, 9, 1]⟩,
        ⟨84007, false, false, [], [11, 9, 1]⟩,
        ⟨84172, false, false, [], [9, 1]⟩,
        ⟨84173, false, false, [], [9, 1]⟩,
        ⟨84003, false, false, [], [9, 1]⟩,
        ⟨84003, false, false, [], [9, 1]⟩,
        ⟨84000, false, false, [], [1]⟩,
        ⟨84174, false, false, [], [1]⟩,
        ⟨83999, false, false, [], [1]⟩,
        ⟨83999, false, false, [], [1]⟩,
        ⟨83996, false, false, [], []⟩,
        ⟨83995, false, false, [], []⟩,
        ⟨83995, false, false, [], []⟩
      ]⟩,
    ⟨[94353], [94353], .contexts []⟩,
    ⟨[94353, 3], [94351], .contexts [
        ⟨83988, true, false, [], [3]⟩,
        ⟨20, false, false, [94351], []⟩,
        ⟨83989, false, false, [], []⟩
      ]⟩,
    ⟨[94351], [94351], .contexts []⟩,
    ⟨[94349], [94349], .contexts []⟩,
    ⟨[94347], [94347], .contexts []⟩,
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15
    ], [94347], .contexts [
        ⟨84175, false, false, [], [5, 3, 1, 15]⟩,
        ⟨83991, true, false, [], [5, 3, 1, 15]⟩,
        ⟨28, false, false, [94353], [3, 1, 15]⟩,
        ⟨83992, false, false, [], [3, 1, 15]⟩,
        ⟨84176, false, false, [], [3, 1, 15]⟩,
        ⟨83992, false, false, [], [3, 1, 15]⟩,
        ⟨83992, false, false, [], [3, 1, 15]⟩,
        ⟨84177, false, false, [], [1, 15]⟩,
        ⟨84178, false, false, [], [1, 15]⟩,
        ⟨83989, false, false, [], [1, 15]⟩,
        ⟨83989, false, false, [], [1, 15]⟩,
        ⟨83985, true, false, [], [1, 15]⟩,
        ⟨8, false, false, [94349], [15]⟩,
        ⟨83986, false, false, [], [15]⟩,
        ⟨84179, false, false, [], [15]⟩,
        ⟨83986, false, false, [], [15]⟩,
        ⟨83986, false, false, [], [15]⟩,
        ⟨83982, true, false, [], [15]⟩,
        ⟨1, false, false, [94347], []⟩,
        ⟨83983, false, false, [], []⟩,
        ⟨84180, false, false, [], []⟩,
        ⟨83983, false, false, [], []⟩,
        ⟨83983, false, false, [], []⟩
      ]⟩,
    ⟨[94345], [94345], .contexts []⟩,
    ⟨[94343], [94343], .contexts []⟩,
    ⟨[94341], [94341], .contexts []⟩,
    ⟨[94339], [94339], .contexts []⟩,
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [94339], .contexts [
        ⟨84181, false, false, [], [13, 1, 11, 9]⟩,
        ⟨83979, true, false, [], [13, 1, 11, 9]⟩,
        ⟨59, false, false, [94345], [1, 11, 9]⟩,
        ⟨83980, false, false, [], [1, 11, 9]⟩,
        ⟨84182, false, false, [], [1, 11, 9]⟩,
        ⟨83980, false, false, [], [1, 11, 9]⟩,
        ⟨83980, false, false, [], [1, 11, 9]⟩,
        ⟨83976, true, false, [], [1, 11, 9]⟩,
        ⟨8, false, false, [94343], [11, 9]⟩,
        ⟨83977, false, false, [], [11, 9]⟩,
        ⟨84183, false, false, [], [11, 9]⟩,
        ⟨83977, false, false, [], [11, 9]⟩,
        ⟨83977, false, false, [], [11, 9]⟩,
        ⟨83973, true, false, [], [11, 9]⟩,
        ⟨53, false, false, [94341], [9]⟩,
        ⟨83974, false, false, [], [9]⟩,
        ⟨84184, false, false, [], [9]⟩,
        ⟨83974, false, false, [], [9]⟩,
        ⟨83974, false, false, [], [9]⟩,
        ⟨83971, false, false, [], []⟩,
        ⟨84185, false, false, [], []⟩,
        ⟨83970, false, false, [], []⟩,
        ⟨83970, false, false, [], []⟩
      ]⟩,
    ⟨[94337], [94337], .contexts []⟩,
    ⟨[94335], [94335], .contexts []⟩,
    ⟨[94333], [94333], .contexts []⟩,
    ⟨[94331], [94331], .contexts []⟩,
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1
    ], [94331], .contexts [
        ⟨84186, false, false, [], [1, 5, 3, 1]⟩,
        ⟨83966, true, false, [], [1, 5, 3, 1]⟩,
        ⟨8, false, false, [94337], [5, 3, 1]⟩,
        ⟨83967, false, false, [], [5, 3, 1]⟩,
        ⟨84187, false, false, [], [5, 3, 1]⟩,
        ⟨83967, false, false, [], [5, 3, 1]⟩,
        ⟨83967, false, false, [], [5, 3, 1]⟩,
        ⟨83963, true, false, [], [5, 3, 1]⟩,
        ⟨28, false, false, [94335], [3, 1]⟩,
        ⟨83964, false, false, [], [3, 1]⟩,
        ⟨84188, false, false, [], [3, 1]⟩,
        ⟨83964, false, false, [], [3, 1]⟩,
        ⟨83964, false, false, [], [3, 1]⟩,
        ⟨83961, false, false, [], [1]⟩,
        ⟨84189, false, false, [], [1]⟩,
        ⟨83960, false, false, [], [1]⟩,
        ⟨83960, false, false, [], [1]⟩,
        ⟨83957, false, false, [], []⟩,
        ⟨84190, false, false, [], []⟩,
        ⟨83956, false, false, [], []⟩,
        ⟨83956, false, false, [], []⟩
      ]⟩,
    ⟨[94329], [94329], .contexts []⟩,
    ⟨[94327], [94327], .contexts []⟩,
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9
    ], [94321], .contexts [
        ⟨84191, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨83953, false, false, [], [13, 1, 11, 9]⟩,
        ⟨84192, false, false, [], [13, 1, 11, 9]⟩,
        ⟨83952, false, false, [], [13, 1, 11, 9]⟩,
        ⟨83952, false, false, [], [13, 1, 11, 9]⟩,
        ⟨83949, false, false, [], [1, 11, 9]⟩,
        ⟨84193, false, false, [], [1, 11, 9]⟩,
        ⟨83948, false, false, [], [1, 11, 9]⟩,
        ⟨83948, false, false, [], [1, 11, 9]⟩,
        ⟨83945, true, false, [], [1, 11, 9]⟩,
        ⟨8, false, false, [94325], [11, 9]⟩,
        ⟨83943, false, false, [], [11, 9]⟩,
        ⟨83943, false, false, [], [11, 9]⟩,
        ⟨83943, false, false, [], [11, 9]⟩,
        ⟨83942, true, false, [], [11, 9]⟩,
        ⟨53, false, false, [94323], [9]⟩,
        ⟨83937, false, false, [], [9]⟩,
        ⟨83936, false, false, [], [9]⟩,
        ⟨83937, false, false, [], [9]⟩,
        ⟨83937, false, false, [], [9]⟩,
        ⟨83935, false, false, [], []⟩,
        ⟨83920, false, false, [], []⟩,
        ⟨83921, false, false, [], []⟩,
        ⟨83921, false, false, [], []⟩
      ]⟩,
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [23719, 89197], .contexts [
        ⟨84194, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨83927, false, false, [], [5, 3, 1, 15]⟩,
        ⟨83923, false, false, [], [5, 3, 1, 15]⟩,
        ⟨83924, false, false, [], [5, 3, 1, 15]⟩,
        ⟨83924, false, false, [], [5, 3, 1, 15]⟩,
        ⟨83919, false, false, [23719], [3, 1, 15]⟩,
        ⟨83903, false, false, [], [3, 1, 15]⟩,
        ⟨83904, false, false, [], [3, 1, 15]⟩,
        ⟨83906, false, false, [], [3, 1, 15]⟩,
        ⟨83896, false, false, [23719], [1, 15]⟩,
        ⟨83900, false, false, [], [1, 15]⟩,
        ⟨83901, false, false, [], [1, 15]⟩,
        ⟨83902, false, false, [], [1, 15]⟩,
        ⟨83876, false, false, [23719], [15]⟩,
        ⟨83850, false, false, [], [15]⟩,
        ⟨83851, false, false, [], [15]⟩,
        ⟨83852, false, false, [], [15]⟩,
        ⟨83846, false, false, [23719], []⟩,
        ⟨54766, false, false, [], []⟩,
        ⟨54767, false, false, [], []⟩
      ]⟩,
    ⟨[31239], [23719, 30345], .source 15684⟩,
    ⟨[31241], [31239, 31227], .source 15685⟩,
    ⟨[31243], [31241, 15399], .source 15686⟩,
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1
    ], [31243, 94311], .contexts [
        ⟨84195, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨79990, false, false, [23719], [1, 11, 9, 1]⟩,
        ⟨84196, true, false, [], [93553, 1, 11, 9, 1]⟩,
        ⟨79960, false, false, [31239], [11, 9, 1]⟩,
        ⟨83843, false, false, [31239], [9, 1]⟩,
        ⟨84197, true, false, [], [94313, 9, 1]⟩,
        ⟨83824, false, false, [31241], [1]⟩,
        ⟨83798, false, false, [31241], []⟩,
        ⟨84198, true, false, [], [94311]⟩
      ]⟩,
    ⟨[31245], [31243, 553], .source 15687⟩,
    ⟨[31247], [31245, 13163], .source 15688⟩,
    ⟨[31249], [31247, 8681], .source 15689⟩,
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [31249, 82743], .contexts [
        ⟨84199, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨83801, false, false, [31243], [3, 1, 15, 13]⟩,
        ⟨84200, true, false, [], [94311, 3, 1, 15, 13]⟩,
        ⟨83791, false, false, [31245], [1, 15, 13]⟩,
        ⟨16242, false, false, [31245], [15, 13]⟩,
        ⟨16259, false, false, [31245], [13]⟩,
        ⟨84201, true, false, [], [82743, 13]⟩,
        ⟨16076, false, false, [31247], []⟩,
        ⟨84202, true, false, [], [82743]⟩
      ]⟩,
    ⟨[31251], [31249, 8673], .source 15690⟩,
    ⟨[31253], [31251, 8673], .source 15691⟩,
    ⟨[31255], [31253, 15095], .source 15692⟩,
    ⟨[31257], [31255, 15099], .source 15693⟩,
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5
    ], [31257, 80803], .contexts [
        ⟨84203, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨16062, false, false, [31249], [11, 9, 1, 5]⟩,
        ⟨84204, true, false, [], [82731, 11, 9, 1, 5]⟩,
        ⟨15915, false, false, [31251], [9, 1, 5]⟩,
        ⟨84205, true, false, [], [82731, 9, 1, 5]⟩,
        ⟨17464, false, false, [31253], [1, 5]⟩,
        ⟨84206, true, false, [], [82849, 1, 5]⟩,
        ⟨17455, false, false, [31255], [5]⟩,
        ⟨84207, true, false, [], [82849, 5]⟩,
        ⟨17444, false, false, [31257], []⟩
      ]⟩,
    ⟨[31259], [31257, 2375], .source 15694⟩,
    ⟨[31261], [31259, 15099], .source 15695⟩,
    ⟨[31263], [31261, 15415], .source 15696⟩,
    ⟨[31265], [31263, 15433], .source 15697⟩,
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1
    ], [31265, 82671], .contexts [
        ⟨84208, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨8273, false, false, [31257], [1, 15, 13, 1]⟩,
        ⟨84209, true, false, [], [80803, 1, 15, 13, 1]⟩,
        ⟨14776, false, false, [31259], [15, 13, 1]⟩,
        ⟨84210, true, false, [], [80803, 15, 13, 1]⟩,
        ⟨16401, false, false, [31261], [13, 1]⟩,
        ⟨84211, true, false, [], [82767, 13, 1]⟩,
        ⟨16465, false, false, [31263], [1]⟩,
        ⟨16493, false, false, [31263], []⟩,
        ⟨84212, true, false, [], [82671]⟩
      ]⟩,
    ⟨[31267], [31265, 15245], .source 15698⟩,
    ⟨[31269], [31267, 15517], .source 15699⟩,
    ⟨[31271], [31269, 15625], .source 15700⟩,
    ⟨[31273], [31271, 17151], .source 15701⟩,
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [31273, 83575], .contexts [
        ⟨84213, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨15210, false, false, [31265], [9, 1, 5, 3]⟩,
        ⟨84214, true, false, [], [82659, 9, 1, 5, 3]⟩,
        ⟨16875, false, false, [31267], [1, 5, 3]⟩,
        ⟨16883, false, false, [31267], [5, 3]⟩,
        ⟨84215, true, false, [], [82809, 5, 3]⟩,
        ⟨17401, false, false, [31269], [3]⟩,
        ⟨84216, true, false, [], [82845, 3]⟩,
        ⟨26510, false, false, [31271], []⟩,
        ⟨84217, true, false, [], [83575]⟩
      ]⟩,
    ⟨[31275], [31273, 17271], .source 15702⟩,
    ⟨[31277], [31275, 24247], .source 15703⟩,
    ⟨[31279], [31277, 24243], .source 15704⟩,
    ⟨[31279, 87413], [31279, 87413], .contexts []⟩,
    ⟨[31279, 87413], [31279, 87413], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1316. -/
def y322TCIndexRaw1316 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[
      94427, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11
    ], [31279, 87413], .contexts [
        ⟨84218, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨22085, false, false, [31273], [15, 13, 1, 11]⟩,
        ⟨27121, false, false, [31273], [13, 1, 11]⟩,
        ⟨84219, true, false, [], [84491, 13, 1, 11]⟩,
        ⟨57112, false, false, [31275], [1, 11]⟩,
        ⟨84220, true, false, [], [89699, 1, 11]⟩,
        ⟨57106, false, false, [31277], [11]⟩,
        ⟨84221, true, false, [], [87411, 11]⟩,
        ⟨41561, false, false, [31279], []⟩,
        ⟨84222, false, false, [], []⟩,
        ⟨84223, false, false, [], []⟩
      ]⟩,
    ⟨[94429, 9], [94429, 9], .contexts []⟩,
    ⟨[94429, 9], [31279, 87413], .contexts [
        ⟨84225, false, false, [], []⟩,
        ⟨84124, true, false, [], [9]⟩,
        ⟨84124, true, false, [], [9]⟩,
        ⟨84123, true, false, [], [9]⟩,
        ⟨84120, true, false, [], [9]⟩,
        ⟨447, false, false, [94427], []⟩,
        ⟨449, false, false, [94427], []⟩,
        ⟨84224, false, false, [], []⟩,
        ⟨42877, false, false, [31279], []⟩,
        ⟨13, true, false, [], [31279, 87413]⟩
      ]⟩,
    ⟨[31281], [31278], .source 15705⟩,
    ⟨[94429, 9], [31279, 87413], .contexts [
        ⟨84225, false, false, [], []⟩,
        ⟨84226, false, false, [], []⟩,
        ⟨84222, false, false, [], []⟩,
        ⟨84223, false, false, [], []⟩,
        ⟨84223, false, false, [], []⟩
      ]⟩,
    ⟨[31283], [31279, 30211], .source 15706⟩,
    ⟨[31285], [31282], .source 15707⟩,
    ⟨[93535, 9], [31285, 94427], .contexts [
        ⟨13, false, false, [31282], [31283, 93535, 9]⟩,
        ⟨79744, true, false, [], [9]⟩,
        ⟨79468, true, false, [], [9]⟩,
        ⟨84229, false, false, [31282], [93537, 1, 9]⟩,
        ⟨79668, true, false, [31282, 31279], [1, 9]⟩,
        ⟨41565, true, false, [31282, 31279], [9, 1, 9]⟩,
        ⟨84228, true, false, [31282], [1, 9, 1, 9]⟩,
        ⟨455, true, false, [31282, 94429], [9]⟩,
        ⟨452, true, false, [31282, 94429], [9]⟩,
        ⟨84122, false, false, [31282], [9, 9]⟩,
        ⟨84121, false, false, [31282], [9, 9]⟩,
        ⟨84121, false, false, [31282], [9, 9]⟩,
        ⟨46, false, false, [31282, 94427], []⟩,
        ⟨84230, true, false, [], [94427]⟩
      ]⟩,
    ⟨[30263, 88959], [30263, 88959], .contexts []⟩,
    ⟨[31287], [30265, 31285], .source 15708⟩,
    ⟨[31289], [31286], .source 15709⟩,
    ⟨[94427], [31289, 88959], .contexts [
        ⟨84233, false, false, [31286], [94427]⟩,
        ⟨79745, false, false, [31286], [31285, 94427]⟩,
        ⟨84231, true, false, [31286, 30262], []⟩,
        ⟨79748, false, false, [31286, 30262], []⟩,
        ⟨84232, false, false, [31286, 30262], []⟩,
        ⟨84232, false, false, [31286, 30262], []⟩,
        ⟨84234, true, false, [], [88959]⟩
      ]⟩,
    ⟨[31287], [31288], .contexts [
        ⟨84234, true, true, [], []⟩
      ]⟩,
    ⟨[31288], [31288], .contexts []⟩,
    ⟨[31287], [31288], .contexts [
        ⟨84236, false, false, [], []⟩,
        ⟨84237, false, false, [], []⟩,
        ⟨84237, false, false, [], []⟩
      ]⟩,
    ⟨[94427], [31289, 88959], .contexts [
        ⟨84235, false, false, [], []⟩
      ]⟩,
    ⟨[88961, 3], [31287, 94423], .contexts [
        ⟨84234, false, false, [31288], [88961, 3]⟩,
        ⟨53246, true, false, [31288, 31286], [3]⟩,
        ⟨84239, true, false, [31288, 31286, 31288], [5, 3]⟩,
        ⟨84118, false, false, [31288, 31286, 31288], [3]⟩,
        ⟨84125, false, false, [31288, 31286, 31288], [3]⟩,
        ⟨13, true, false, [31288, 31286, 31288], [94425, 3]⟩,
        ⟨84236, true, false, [31288, 31286], [94425, 3]⟩,
        ⟨84115, false, false, [31288], []⟩,
        ⟨84126, false, false, [31288], []⟩,
        ⟨84238, true, false, [], [94423]⟩
      ]⟩,
    ⟨[31291], [31279, 30431], .source 15710⟩,
    ⟨[31291, 93669], [31291, 93669], .contexts []⟩,
    ⟨[31291, 93669], [31291, 93669], .contexts []⟩,
    ⟨[94429], [94429], .contexts []⟩,
    ⟨[94429], [94429], .contexts []⟩,
    ⟨[31293], [31290], .source 15711⟩,
    ⟨[31290], [31290], .contexts []⟩,
    ⟨[93669, 3], [31293, 94429], .contexts [
        ⟨84243, true, false, [31290], [3]⟩,
        ⟨84242, true, false, [31290], [3]⟩,
        ⟨80255, true, false, [], [3]⟩,
        ⟨84241, false, false, [31290], [93671, 9, 3]⟩,
        ⟨80427, true, false, [31290, 31279], [9, 3]⟩,
        ⟨84228, true, false, [31290], [3, 9, 3]⟩,
        ⟨1439, false, false, [31290, 94429], []⟩,
        ⟨84244, false, false, [31290], []⟩,
        ⟨84245, false, false, [31290], []⟩,
        ⟨84247, true, false, [], [94429]⟩,
        ⟨84247, true, false, [], [94429]⟩,
        ⟨84246, true, false, [], [94429]⟩
      ]⟩,
    ⟨[94429, 3], [31291, 93669], .contexts [
        ⟨84248, true, false, [31292], [3]⟩,
        ⟨20, false, false, [31292, 93669], []⟩,
        ⟨84246, false, true, [], [93669]⟩
      ]⟩,
    ⟨[31295], [31279, 20421], .source 15712⟩,
    ⟨[31297], [31295, 23397], .source 15713⟩,
    ⟨[88963, 5], [88963, 5], .contexts []⟩,
    ⟨[31299], [31296], .source 15714⟩,
    ⟨[31296], [31296], .contexts []⟩,
    ⟨[88963, 5], [31299, 94429], .contexts [
        ⟨84252, false, false, [], []⟩,
        ⟨84251, false, false, [31296], [88963, 5]⟩,
        ⟨53394, true, false, [31296, 31295], [5]⟩,
        ⟨84250, false, false, [31296], [83321, 9, 5]⟩,
        ⟨42879, true, false, [31296, 31279], [9, 5]⟩,
        ⟨84228, true, false, [31296], [5, 9, 5]⟩,
        ⟨497, false, false, [31296, 94429], []⟩,
        ⟨84244, false, false, [31296], []⟩,
        ⟨84245, false, false, [31296], []⟩,
        ⟨84254, true, false, [], [94429]⟩,
        ⟨84254, true, false, [], [94429]⟩,
        ⟨84253, true, false, [], [94429]⟩
      ]⟩,
    ⟨[31297], [31298], .contexts [
        ⟨84253, true, true, [], []⟩
      ]⟩,
    ⟨[94429, 5], [31297, 88963], .contexts [
        ⟨84255, true, false, [31298], [5]⟩,
        ⟨28, false, false, [31298, 88963], []⟩,
        ⟨84256, true, false, [], [88963]⟩
      ]⟩,
    ⟨[31301], [31279, 22389], .source 15715⟩,
    ⟨[31301, 84473], [31301, 84473], .contexts []⟩,
    ⟨[31303], [31300], .source 15716⟩,
    ⟨[31300], [31300], .contexts []⟩,
    ⟨[84473, 7], [31303, 94429], .contexts [
        ⟨84259, true, false, [31300], [7]⟩,
        ⟨26899, true, false, [], [7]⟩,
        ⟨84258, false, false, [31300], [84475, 9, 7]⟩,
        ⟨48840, true, false, [31300, 31279], [9, 7]⟩,
        ⟨84228, true, false, [31300], [7, 9, 7]⟩,
        ⟨469, false, false, [31300, 94429], []⟩,
        ⟨84244, false, false, [31300], []⟩,
        ⟨84245, false, false, [31300], []⟩,
        ⟨84261, true, false, [], [94429]⟩,
        ⟨84261, true, false, [], [94429]⟩,
        ⟨84260, true, false, [], [94429]⟩
      ]⟩,
    ⟨[23423, 88963], [23423, 88963], .contexts []⟩,
    ⟨[23423, 88963], [23423, 88963], .contexts []⟩,
    ⟨[31305], [23423, 31287], .source 15717⟩,
    ⟨[31305, 94421], [31305, 94421], .contexts []⟩,
    ⟨[31305, 94421, 3], [88961], .contexts [
        ⟨84266, true, false, [], [3]⟩,
        ⟨84112, true, false, [31305], [3]⟩,
        ⟨84265, false, false, [], [94423, 1, 3]⟩,
        ⟨84240, true, false, [23423], [1, 3]⟩,
        ⟨53252, true, false, [23423], [3, 1, 3]⟩,
        ⟨84264, true, false, [], [1, 3, 1, 3]⟩,
        ⟨84264, true, false, [], [1, 3, 1, 3]⟩,
        ⟨84263, true, false, [], [1, 3, 1, 3]⟩,
        ⟨53437, true, false, [], [1, 3, 1, 3]⟩,
        ⟨69366, true, false, [], [3, 1, 3, 1, 3]⟩,
        ⟨4083, false, false, [88961], []⟩
      ]⟩,
    ⟨[31307], [31304], .source 15718⟩,
    ⟨[31304], [31304], .contexts []⟩,
    ⟨[94421, 3], [31307, 88961], .contexts [
        ⟨84267, false, false, [31304], []⟩,
        ⟨53421, false, false, [31304], []⟩,
        ⟨84269, true, false, [], [88961]⟩,
        ⟨84269, true, false, [], [88961]⟩,
        ⟨84268, true, false, [], [88961]⟩
      ]⟩,
    ⟨[88961, 3], [31287, 94423], .contexts [
        ⟨84240, false, false, [], []⟩
      ]⟩,
    ⟨[31287, 94423], [31287, 94423], .contexts []⟩,
    ⟨[31309], [31289, 31305], .source 15719⟩,
    ⟨[31311], [23413, 30255], .source 15720⟩,
    ⟨[94423], [31309, 94421], .contexts [
        ⟨84272, true, false, [31286], []⟩,
        ⟨84272, true, false, [31286], []⟩,
        ⟨84271, true, false, [31286], []⟩,
        ⟨84270, true, false, [31286, 31306], [3]⟩,
        ⟨20, false, false, [31286, 31306, 94421], []⟩,
        ⟨84268, false, true, [31286], [94421]⟩,
        ⟨84266, false, false, [31286], []⟩,
        ⟨84234, true, false, [], [31305, 94421]⟩,
        ⟨84273, true, false, [], [94421]⟩
      ]⟩,
    ⟨[31309, 94421], [31309, 94421], .contexts []⟩,
    ⟨[94423], [31309, 94421], .contexts [
        ⟨84275, false, false, [], []⟩,
        ⟨84276, false, false, [], []⟩
      ]⟩,
    ⟨[31313], [31287, 31309], .source 15721⟩,
    ⟨[88961, 3], [31313, 94421], .contexts [
        ⟨84271, false, false, [], []⟩,
        ⟨84277, false, false, [31287], []⟩,
        ⟨84278, true, false, [], [94421]⟩
      ]⟩,
    ⟨[88961, 2], [88961, 3], .contexts [
        ⟨21, false, false, [88961], []⟩
      ]⟩,
    ⟨[94421], [94421], .contexts []⟩,
    ⟨[31315], [31310], .source 15722⟩,
    ⟨[31317], [31315, 31313], .source 15723⟩,
    ⟨[84193, 9], [31317, 94421], .contexts [
        ⟨84274, false, false, [31310], [84193, 9]⟩,
        ⟨79725, false, false, [31310, 23413], [84193, 9]⟩,
        ⟨70111, true, false, [31310, 23413, 26405], [9]⟩,
        ⟨66824, true, false, [31310, 23413], [9]⟩,
        ⟨53477, true, false, [31310], [3, 9]⟩,
        ⟨479, false, false, [31310, 88961], []⟩,
        ⟨84280, false, false, [31310], []⟩,
        ⟨84279, false, false, [31310], []⟩,
        ⟨84281, false, false, [31310, 31313], []⟩,
        ⟨84282, true, false, [], [31313, 94421]⟩,
        ⟨84283, true, false, [], [94421]⟩
      ]⟩,
    ⟨[31319], [31316], .source 15724⟩,
    ⟨[94421, 9], [31319, 84193], .contexts [
        ⟨84284, true, false, [31316], [9]⟩,
        ⟨46, false, false, [31316, 84193], []⟩,
        ⟨84285, true, false, [], [84193]⟩
      ]⟩,
    ⟨[31321], [23431, 22451], .source 15725⟩]

/-- Exact literal claimed equations and contextual derivations, block 1317. -/
def y322TCIndexRaw1317 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[31323], [31320], .source 15726⟩,
    ⟨[31325], [31323, 31313], .source 15727⟩,
    ⟨[86203, 7], [31325, 94421], .contexts [
        ⟨84287, false, false, [31320], [86203, 7]⟩,
        ⟨49026, true, false, [31320, 23431], [7]⟩,
        ⟨35668, true, false, [31320, 23431], [7]⟩,
        ⟨53463, true, false, [31320], [3, 7]⟩,
        ⟨14911, false, false, [31320, 88961], []⟩,
        ⟨84280, false, false, [31320], []⟩,
        ⟨84279, false, false, [31320], []⟩,
        ⟨84281, false, false, [31320, 31313], []⟩,
        ⟨84288, true, false, [], [31313, 94421]⟩,
        ⟨84289, true, false, [], [94421]⟩
      ]⟩,
    ⟨[31327], [31324], .source 15728⟩,
    ⟨[94421, 7], [31327, 86203], .contexts [
        ⟨84290, true, false, [31324], [7]⟩,
        ⟨38, false, false, [31324, 86203], []⟩,
        ⟨84291, true, false, [], [86203]⟩
      ]⟩,
    ⟨[31329], [24405, 27121], .source 15729⟩,
    ⟨[86659, 13], [86659, 13], .contexts []⟩,
    ⟨[31331], [31328], .source 15730⟩,
    ⟨[31333], [31331, 31313], .source 15731⟩,
    ⟨[86659, 13], [31333, 94421], .contexts [
        ⟨84294, false, false, [], []⟩,
        ⟨84293, false, false, [31328], [86659, 13]⟩,
        ⟨69332, false, false, [31328, 24405], [86659, 13]⟩,
        ⟨69329, true, false, [31328, 24405, 26779], [13]⟩,
        ⟨68396, true, false, [31328, 24405], [13]⟩,
        ⟨57832, true, false, [31328], [3, 13]⟩,
        ⟨1132, false, false, [31328, 88961], []⟩,
        ⟨84280, false, false, [31328], []⟩,
        ⟨84279, false, false, [31328], []⟩,
        ⟨84281, false, false, [31328, 31313], []⟩,
        ⟨84295, true, false, [], [31313, 94421]⟩,
        ⟨84296, true, false, [], [94421]⟩
      ]⟩,
    ⟨[31335], [31332], .source 15732⟩,
    ⟨[31299, 94429], [31299, 94429], .contexts []⟩,
    ⟨[31299, 94429], [31299, 94429], .contexts []⟩,
    ⟨[27135, 88479], [27135, 88479], .contexts []⟩,
    ⟨[27135, 88479], [27135, 88479], .contexts []⟩,
    ⟨[31337], [27135, 26921], .source 15733⟩,
    ⟨[94429, 11], [94429, 11], .contexts []⟩,
    ⟨[91949], [91949], .contexts []⟩,
    ⟨[31339], [31297, 31337], .source 15734⟩,
    ⟨[94429, 11], [31339, 91949], .contexts [
        ⟨84304, false, false, [], []⟩,
        ⟨84300, true, false, [31298], [11]⟩,
        ⟨84300, true, false, [31298], [11]⟩,
        ⟨84299, true, false, [31298], [11]⟩,
        ⟨84255, true, false, [31298], [11]⟩,
        ⟨84252, true, false, [31298], [11]⟩,
        ⟨174, false, false, [31298, 88963], []⟩,
        ⟨175, false, false, [31298, 88963], []⟩,
        ⟨69370, false, false, [31298], [5]⟩,
        ⟨84301, false, false, [31298], [5]⟩,
        ⟨84302, false, false, [31298], [5]⟩,
        ⟨84302, false, false, [31298], [5]⟩,
        ⟨68795, false, false, [31298, 27135], []⟩,
        ⟨84303, true, false, [31298], [91949]⟩,
        ⟨84305, false, false, [31298, 31337], []⟩,
        ⟨84256, true, false, [], [31337, 91949]⟩,
        ⟨84306, true, false, [], [91949]⟩
      ]⟩,
    ⟨[31341], [31338], .source 15735⟩,
    ⟨[91949, 11], [31341, 94429], .contexts [
        ⟨84307, true, false, [31338], [11]⟩,
        ⟨53, false, false, [31338, 94429], []⟩,
        ⟨84308, true, false, [], [94429]⟩
      ]⟩,
    ⟨[94421, 15], [94419], .contexts [
        ⟨84128, false, false, [], []⟩,
        ⟨84129, false, false, [], []⟩,
        ⟨84107, false, false, [], []⟩,
        ⟨84107, false, false, [], []⟩
      ]⟩,
    ⟨[31309, 94419], [31309, 94419], .contexts []⟩,
    ⟨[31309, 94419], [31309, 94419], .contexts []⟩,
    ⟨[94419, 1], [94419, 1], .contexts []⟩,
    ⟨[94419, 1], [31309, 94419], .contexts [
        ⟨84313, false, false, [], []⟩,
        ⟨84310, true, false, [], [1]⟩,
        ⟨7, false, false, [94421], []⟩,
        ⟨11, false, false, [94421], []⟩,
        ⟨84110, false, false, [], [15]⟩,
        ⟨84277, false, false, [], [15]⟩,
        ⟨84276, false, false, [], [15]⟩,
        ⟨84276, false, false, [], [15]⟩,
        ⟨84108, false, false, [31309], []⟩,
        ⟨84311, false, false, [], []⟩,
        ⟨84312, false, false, [], []⟩,
        ⟨13, true, false, [], [31309, 94419]⟩
      ]⟩,
    ⟨[31327, 86203], [31327, 86203], .contexts []⟩,
    ⟨[31327, 86203], [31327, 86203], .contexts []⟩,
    ⟨[31327, 86201], [31327, 86201], .contexts []⟩,
    ⟨[31327, 86201], [31327, 86201], .contexts []⟩,
    ⟨[94419, 7], [94419, 7], .contexts []⟩,
    ⟨[94419, 7], [31327, 86201], .contexts [
        ⟨84319, false, false, [], []⟩,
        ⟨84310, true, false, [], [7]⟩,
        ⟨37, false, false, [94421], []⟩,
        ⟨40, false, false, [94421], []⟩,
        ⟨84292, false, false, [], [15]⟩,
        ⟨84315, false, false, [], [15]⟩,
        ⟨84316, false, false, [], [15]⟩,
        ⟨84316, false, false, [], [15]⟩,
        ⟨35661, false, false, [31327], []⟩,
        ⟨84317, false, false, [], []⟩,
        ⟨84318, false, false, [], []⟩,
        ⟨49032, false, false, [31327], []⟩,
        ⟨13, true, false, [], [31327, 86201]⟩
      ]⟩,
    ⟨[31325], [31326], .contexts [
        ⟨84291, true, true, [], []⟩
      ]⟩,
    ⟨[31319, 84193], [31319, 84193], .contexts []⟩,
    ⟨[31319, 84193], [31319, 84193], .contexts []⟩,
    ⟨[31343], [31319, 27315], .source 15736⟩,
    ⟨[94419, 9], [94419, 9], .contexts []⟩,
    ⟨[94419, 9], [31343, 91603], .contexts [
        ⟨84325, false, false, [], []⟩,
        ⟨84310, true, false, [], [9]⟩,
        ⟨45, false, false, [94421], []⟩,
        ⟨48, false, false, [94421], []⟩,
        ⟨84286, false, false, [], [15]⟩,
        ⟨84322, false, false, [], [15]⟩,
        ⟨84323, false, false, [], [15]⟩,
        ⟨84323, false, false, [], [15]⟩,
        ⟨70107, false, false, [31319], []⟩,
        ⟨84324, true, false, [], [91603]⟩,
        ⟨79752, false, false, [31343], []⟩,
        ⟨13, true, false, [], [31343, 91603]⟩
      ]⟩,
    ⟨[31345], [31342], .source 15737⟩,
    ⟨[31339, 91949], [31339, 91949], .contexts []⟩,
    ⟨[31347], [31291, 30419], .source 15738⟩,
    ⟨[91949, 3], [91949, 3], .contexts []⟩,
    ⟨[31349], [31341, 31347], .source 15739⟩,
    ⟨[91949, 3], [31349, 91127], .contexts [
        ⟨84330, false, false, [], []⟩,
        ⟨84328, true, false, [31338], [3]⟩,
        ⟨84328, true, false, [31338], [3]⟩,
        ⟨84307, true, false, [31338], [3]⟩,
        ⟨84304, true, false, [31338], [3]⟩,
        ⟨215, false, false, [31338, 94429], []⟩,
        ⟨216, false, false, [31338, 94429], []⟩,
        ⟨84249, false, false, [31338], [11]⟩,
        ⟨84242, false, false, [31338], [11]⟩,
        ⟨84243, false, false, [31338], [11]⟩,
        ⟨84243, false, false, [31338], [11]⟩,
        ⟨80479, false, false, [31338, 31291], []⟩,
        ⟨84329, true, false, [31338], [91127]⟩,
        ⟨64552, false, false, [31338, 31347], []⟩,
        ⟨84308, true, false, [], [31347, 91127]⟩,
        ⟨84331, true, false, [], [91127]⟩
      ]⟩,
    ⟨[31351], [31348], .source 15740⟩,
    ⟨[94419, 13], [94417], .contexts [
        ⟨84130, false, false, [], []⟩,
        ⟨84131, false, false, [], []⟩,
        ⟨84103, false, false, [], []⟩,
        ⟨84103, false, false, [], []⟩
      ]⟩,
    ⟨[94415, 13], [94415, 13], .contexts []⟩,
    ⟨[94415], [94415], .contexts []⟩,
    ⟨[31353], [31308], .source 15741⟩,
    ⟨[31308], [31308], .contexts []⟩,
    ⟨[31353], [31308], .contexts [
        ⟨84337, false, false, [], []⟩,
        ⟨84338, false, false, [], []⟩,
        ⟨84338, false, false, [], []⟩
      ]⟩,
    ⟨[94415, 13], [31353, 94415], .contexts [
        ⟨84335, false, false, [], []⟩,
        ⟨84100, true, false, [], [13]⟩,
        ⟨84104, true, false, [], [1, 13]⟩,
        ⟨84312, true, false, [31308], [13, 1, 13]⟩,
        ⟨84312, true, false, [31308], [13, 1, 13]⟩,
        ⟨84311, true, false, [31308], [13, 1, 13]⟩,
        ⟨84314, true, false, [31308], [13, 1, 13]⟩,
        ⟨84313, true, false, [31308], [13, 1, 13]⟩,
        ⟨919, false, false, [31308, 94419], []⟩,
        ⟨116, false, false, [31308, 94419], []⟩,
        ⟨84334, false, false, [31308], [1]⟩,
        ⟨84133, false, false, [31308], []⟩,
        ⟨84134, false, false, [31308], []⟩,
        ⟨84099, false, false, [31308], []⟩,
        ⟨84099, false, false, [31308], []⟩,
        ⟨84336, false, false, [31308], []⟩,
        ⟨84339, true, false, [], [94415]⟩
      ]⟩,
    ⟨[31327, 86199], [31327, 86199], .contexts []⟩,
    ⟨[94419, 12], [94419, 13], .contexts [
        ⟨64, false, false, [94419], []⟩
      ]⟩,
    ⟨[86199, 7], [86199, 7], .contexts []⟩,
    ⟨[94417], [94417], .contexts []⟩,
    ⟨[31325], [31326], .contexts [
        ⟨84321, false, false, [], []⟩
      ]⟩,
    ⟨[31326], [31326], .contexts []⟩,
    ⟨[31325], [31326], .contexts [
        ⟨84345, false, false, [], []⟩,
        ⟨84346, false, false, [], []⟩,
        ⟨84346, false, false, [], []⟩
      ]⟩,
    ⟨[86199, 7], [31325, 94417], .contexts [
        ⟨84343, false, false, [], []⟩,
        ⟨84341, true, false, [31326], [7]⟩,
        ⟨35657, true, false, [], [7]⟩,
        ⟨84318, true, false, [31326], [13, 7]⟩,
        ⟨84318, true, false, [31326], [13, 7]⟩,
        ⟨84317, true, false, [31326], [13, 7]⟩,
        ⟨84320, true, false, [31326], [13, 7]⟩,
        ⟨84319, true, false, [31326], [13, 7]⟩,
        ⟨518, false, false, [31326, 94419], []⟩,
        ⟨84342, false, false, [31326], []⟩,
        ⟨84334, false, false, [31326], []⟩,
        ⟨84344, false, false, [31326], []⟩,
        ⟨84347, true, false, [], [94417]⟩
      ]⟩,
    ⟨[31343, 91603], [31343, 91603], .contexts []⟩,
    ⟨[31355], [31343, 29301], .source 15742⟩,
    ⟨[91599, 9], [91599, 9], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1318. -/
def y322TCIndexRaw1318 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[31357], [31354], .source 15743⟩,
    ⟨[31354], [31354], .contexts []⟩,
    ⟨[91599, 9], [31357, 94417], .contexts [
        ⟨84351, false, false, [], []⟩,
        ⟨84350, false, false, [31354], [91599, 9]⟩,
        ⟨76334, true, false, [31354, 31343], [9]⟩,
        ⟨66593, true, false, [31354, 31343], [9]⟩,
        ⟨84349, true, false, [31354], [13, 9]⟩,
        ⟨84349, true, false, [31354], [13, 9]⟩,
        ⟨84326, true, false, [31354], [13, 9]⟩,
        ⟨84325, true, false, [31354], [13, 9]⟩,
        ⟨511, false, false, [31354, 94419], []⟩,
        ⟨84342, false, false, [31354], []⟩,
        ⟨84334, false, false, [31354], []⟩,
        ⟨84344, false, false, [31354], []⟩,
        ⟨84353, true, false, [], [94417]⟩,
        ⟨84353, true, false, [], [94417]⟩,
        ⟨84352, true, false, [], [94417]⟩
      ]⟩,
    ⟨[31355], [31356], .contexts [
        ⟨84352, true, true, [], []⟩
      ]⟩,
    ⟨[31349, 91127], [31349, 91127], .contexts []⟩,
    ⟨[31349, 91127], [31349, 91127], .contexts []⟩,
    ⟨[91949, 3], [31349, 91127], .contexts [
        ⟨84330, false, false, [], []⟩,
        ⟨84332, false, false, [], []⟩,
        ⟨84356, false, false, [], []⟩,
        ⟨84357, false, false, [], []⟩,
        ⟨84357, false, false, [], []⟩
      ]⟩,
    ⟨[31349, 91125], [31349, 91125], .contexts []⟩,
    ⟨[31351], [31348], .contexts [
        ⟨84333, false, false, [], []⟩
      ]⟩,
    ⟨[31348], [31348], .contexts []⟩,
    ⟨[91125, 3], [31351, 91947], .contexts [
        ⟨84359, true, false, [31348], [3]⟩,
        ⟨64545, true, false, [], [3]⟩,
        ⟨84358, true, false, [31348], [13, 3]⟩,
        ⟨514, false, false, [31348, 91949], []⟩,
        ⟨64, false, false, [31348, 91949], []⟩,
        ⟨68808, false, false, [31348], []⟩,
        ⟨68784, false, false, [31348], []⟩,
        ⟨84361, true, false, [], [91947]⟩,
        ⟨84361, true, false, [], [91947]⟩,
        ⟨84360, true, false, [], [91947]⟩
      ]⟩,
    ⟨[91947, 3], [31349, 91125], .contexts [
        ⟨84362, true, false, [31350], [3]⟩,
        ⟨20, false, false, [31350, 91125], []⟩,
        ⟨84333, false, true, [], [91125]⟩
      ]⟩,
    ⟨[91951], [27151, 85895], .contexts [
        ⟨69407, false, false, [], []⟩
      ]⟩,
    ⟨[91949, 15], [27151, 85895], .contexts [
        ⟨68799, false, false, [], []⟩,
        ⟨84364, false, false, [], []⟩,
        ⟨69406, false, false, [], []⟩,
        ⟨69406, false, false, [], []⟩
      ]⟩,
    ⟨[91949, 14], [91949, 15], .contexts [
        ⟨10, false, false, [91949], []⟩
      ]⟩,
    ⟨[91129, 3], [91129, 3], .contexts []⟩,
    ⟨[85895], [85895], .contexts []⟩,
    ⟨[31359], [31351, 27151], .source 15744⟩,
    ⟨[91129, 3], [31359, 85895], .contexts [
        ⟨84367, false, false, [], []⟩,
        ⟨64554, true, false, [], [3]⟩,
        ⟨84358, true, false, [31348], [15, 3]⟩,
        ⟨499, false, false, [31348, 91949], []⟩,
        ⟨84366, false, false, [31348], []⟩,
        ⟨84365, false, false, [31348], []⟩,
        ⟨84368, false, false, [31348, 27151], []⟩,
        ⟨84360, true, false, [], [27151, 85895]⟩,
        ⟨84369, true, false, [], [85895]⟩
      ]⟩,
    ⟨[31361], [31358], .source 15745⟩,
    ⟨[85895, 3], [31361, 91129], .contexts [
        ⟨84370, true, false, [31358], [3]⟩,
        ⟨20, false, false, [31358, 91129], []⟩,
        ⟨84371, true, false, [], [91129]⟩
      ]⟩,
    ⟨[31353, 94415], [31353, 94415], .contexts []⟩,
    ⟨[94415, 11], [94413], .contexts [
        ⟨84135, false, false, [], []⟩,
        ⟨84136, false, false, [], []⟩,
        ⟨84095, false, false, [], []⟩,
        ⟨84095, false, false, [], []⟩
      ]⟩,
    ⟨[94415, 10], [94415, 11], .contexts [
        ⟨54, false, false, [94415], []⟩
      ]⟩,
    ⟨[94413, 13], [94413, 13], .contexts []⟩,
    ⟨[94413], [94413], .contexts []⟩,
    ⟨[31352], [31352], .contexts []⟩,
    ⟨[94413, 13], [31309, 94413], .contexts [
        ⟨84376, false, false, [], []⟩,
        ⟨84096, true, false, [], [13]⟩,
        ⟨84373, true, false, [31352], [11, 13]⟩,
        ⟨84373, true, false, [31352], [11, 13]⟩,
        ⟨84340, true, false, [31352], [11, 13]⟩,
        ⟨84335, true, false, [31352], [11, 13]⟩,
        ⟨931, false, false, [31352, 94415], []⟩,
        ⟨84375, false, false, [31352], []⟩,
        ⟨84374, false, false, [31352], []⟩,
        ⟨84377, false, false, [31352], []⟩,
        ⟨84378, true, false, [], [94413]⟩,
        ⟨84378, true, false, [], [94413]⟩,
        ⟨84337, false, true, [], [94413]⟩
      ]⟩,
    ⟨[31325, 94417], [31325, 94417], .contexts []⟩,
    ⟨[86199, 1], [86197], .contexts [
        ⟨35722, false, false, [], []⟩,
        ⟨35723, false, false, [], []⟩,
        ⟨35652, false, false, [], []⟩,
        ⟨35652, false, false, [], []⟩
      ]⟩,
    ⟨[86199, 0], [86199, 1], .contexts [
        ⟨9, false, false, [86199], []⟩
      ]⟩,
    ⟨[94415, 7], [94415, 7], .contexts []⟩,
    ⟨[31324], [31324], .contexts []⟩,
    ⟨[31327], [31324], .contexts [
        ⟨84291, false, false, [], []⟩,
        ⟨84384, false, false, [], []⟩,
        ⟨84384, false, false, [], []⟩
      ]⟩,
    ⟨[94415, 7], [31327, 86197], .contexts [
        ⟨84383, false, false, [], []⟩,
        ⟨84100, true, false, [], [7]⟩,
        ⟨84380, true, false, [31324], [1, 7]⟩,
        ⟨84380, true, false, [31324], [1, 7]⟩,
        ⟨84348, true, false, [31324], [1, 7]⟩,
        ⟨84343, true, false, [31324], [1, 7]⟩,
        ⟨502, false, false, [31324, 86199], []⟩,
        ⟨84382, false, false, [31324], []⟩,
        ⟨84381, false, false, [31324], []⟩,
        ⟨49080, false, false, [31324], []⟩,
        ⟨84385, true, false, [], [86197]⟩
      ]⟩,
    ⟨[91599, 9], [31357, 94417], .contexts [
        ⟨84354, false, false, [], []⟩
      ]⟩,
    ⟨[91599, 9], [31357, 94417], .contexts [
        ⟨84351, false, false, [], []⟩,
        ⟨84387, false, false, [], []⟩
      ]⟩,
    ⟨[31357, 94417], [31357, 94417], .contexts []⟩,
    ⟨[31357, 94417], [31357, 94417], .contexts []⟩,
    ⟨[31363], [29301, 31357], .source 15746⟩,
    ⟨[94415, 9], [94415, 9], .contexts []⟩,
    ⟨[31355], [31356], .contexts [
        ⟨84355, false, false, [], []⟩
      ]⟩,
    ⟨[31365], [31355, 31363], .source 15747⟩,
    ⟨[94415, 9], [31365, 94415], .contexts [
        ⟨84392, false, false, [], []⟩,
        ⟨84100, true, false, [], [9]⟩,
        ⟨84390, true, false, [31356], [1, 9]⟩,
        ⟨84390, true, false, [31356], [1, 9]⟩,
        ⟨84389, true, false, [31356], [1, 9]⟩,
        ⟨84388, true, false, [31356], [1, 9]⟩,
        ⟨1964, false, false, [31356, 91599], []⟩,
        ⟨693, false, false, [31356, 91599], []⟩,
        ⟨76336, false, false, [31356], [9, 1]⟩,
        ⟨84354, false, false, [31356, 29301], [1]⟩,
        ⟨84391, true, false, [31356], [94417, 1]⟩,
        ⟨84100, false, false, [31356, 31363], []⟩,
        ⟨84336, false, false, [31356, 31363], []⟩,
        ⟨84393, true, false, [], [31363, 94415]⟩,
        ⟨84394, true, false, [], [94415]⟩
      ]⟩,
    ⟨[31359, 85895], [31359, 85895], .contexts []⟩,
    ⟨[31359, 85895], [31359, 85895], .contexts []⟩,
    ⟨[31367], [31359, 27149], .source 15748⟩,
    ⟨[91955, 1], [91955, 1], .contexts []⟩,
    ⟨[91133], [91133], .contexts []⟩,
    ⟨[31369], [31366], .source 15749⟩,
    ⟨[31369], [31369], .contexts []⟩,
    ⟨[31369], [31366], .contexts [
        ⟨84402, false, false, [], []⟩,
        ⟨84401, false, false, [], []⟩
      ]⟩,
    ⟨[31366], [31366], .contexts []⟩,
    ⟨[91955, 1], [31369, 91133], .contexts [
        ⟨84399, false, false, [], []⟩,
        ⟨84398, false, false, [31366], [91955, 1]⟩,
        ⟨69415, true, false, [31366, 31359], [1]⟩,
        ⟨34154, true, false, [31366, 31359], [3, 1]⟩,
        ⟨84397, true, false, [31366], [1, 3, 1]⟩,
        ⟨84397, true, false, [31366], [1, 3, 1]⟩,
        ⟨84396, true, false, [31366], [1, 3, 1]⟩,
        ⟨84370, true, false, [31366], [1, 3, 1]⟩,
        ⟨84367, true, false, [31366], [1, 3, 1]⟩,
        ⟨1738, false, false, [31366, 91129], []⟩,
        ⟨131, false, false, [31366, 91129], []⟩,
        ⟨64573, false, false, [31366], [3]⟩,
        ⟨64579, false, false, [31366], []⟩,
        ⟨64858, false, false, [31366], []⟩,
        ⟨64583, false, false, [31366], []⟩,
        ⟨64583, false, false, [31366], []⟩,
        ⟨84400, false, false, [31366], []⟩,
        ⟨84404, true, false, [], [91133]⟩,
        ⟨84404, true, false, [], [91133]⟩,
        ⟨84403, true, false, [], [91133]⟩
      ]⟩,
    ⟨[31367], [31368], .contexts [
        ⟨84401, true, true, [], []⟩
      ]⟩,
    ⟨[31309, 94413], [31309, 94413], .contexts []⟩,
    ⟨[94411], [94411], .contexts []⟩,
    ⟨[31327, 86197], [31327, 86197], .contexts []⟩,
    ⟨[31327, 86197], [31327, 86197], .contexts []⟩,
    ⟨[94415, 7], [31327, 86197], .contexts [
        ⟨84383, false, false, [], []⟩,
        ⟨84386, false, false, [], []⟩,
        ⟨84409, false, false, [], []⟩,
        ⟨84410, false, false, [], []⟩,
        ⟨84410, false, false, [], []⟩
      ]⟩,
    ⟨[31365, 94415], [31365, 94415], .contexts []⟩,
    ⟨[94415, 9], [31365, 94415], .contexts [
        ⟨84392, false, false, [], []⟩,
        ⟨84395, false, false, [], []⟩,
        ⟨84412, false, false, [], []⟩,
        ⟨84412, false, false, [], []⟩
      ]⟩,
    ⟨[31371], [31365, 31327], .source 15750⟩,
    ⟨[86197, 9], [86197, 9], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1319. -/
def y322TCIndexRaw1319 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[31373], [31325, 31371], .source 15751⟩,
    ⟨[86197, 9], [31373, 86197], .contexts [
        ⟨84415, false, false, [], []⟩,
        ⟨84411, true, false, [31326], [9]⟩,
        ⟨1534, false, false, [31326, 94415], []⟩,
        ⟨1535, false, false, [31326, 94415], []⟩,
        ⟨84413, false, false, [31326], [7]⟩,
        ⟨84386, false, false, [31326, 31365], []⟩,
        ⟨84414, true, false, [31326], [86197]⟩,
        ⟨49080, false, false, [31326, 31371], []⟩,
        ⟨84345, true, false, [], [31371, 86197]⟩,
        ⟨84416, true, false, [], [86197]⟩
      ]⟩,
    ⟨[31327, 86195], [31327, 86195], .contexts []⟩,
    ⟨[86195, 7], [86195, 7], .contexts []⟩,
    ⟨[86195, 7], [31325, 94413], .contexts [
        ⟨84419, false, false, [], []⟩,
        ⟨84418, true, false, [31326], [7]⟩,
        ⟨35649, true, false, [], [7]⟩,
        ⟨84411, true, false, [31326], [11, 7]⟩,
        ⟨555, false, false, [31326, 94415], []⟩,
        ⟨84375, false, false, [31326], []⟩,
        ⟨84374, false, false, [31326], []⟩,
        ⟨84377, false, false, [31326], []⟩,
        ⟨84347, true, false, [], [94413]⟩
      ]⟩,
    ⟨[94411, 11], [94411, 11], .contexts []⟩,
    ⟨[31375], [31364], .source 15752⟩,
    ⟨[31364], [31364], .contexts []⟩,
    ⟨[31375], [31364], .contexts [
        ⟨84422, false, false, [], []⟩,
        ⟨84423, false, false, [], []⟩,
        ⟨84423, false, false, [], []⟩
      ]⟩,
    ⟨[94411, 11], [31375, 94411], .contexts [
        ⟨84421, false, false, [], []⟩,
        ⟨84092, true, false, [], [11]⟩,
        ⟨84096, true, false, [], [9, 11]⟩,
        ⟨84413, true, false, [31364], [11, 9, 11]⟩,
        ⟨536, false, false, [31364, 94415], []⟩,
        ⟨537, false, false, [31364, 94415], []⟩,
        ⟨84374, false, false, [31364], [9]⟩,
        ⟨84137, false, false, [31364], []⟩,
        ⟨84138, false, false, [31364], []⟩,
        ⟨84091, false, false, [31364], []⟩,
        ⟨84091, false, false, [31364], []⟩,
        ⟨84408, false, false, [31364], []⟩,
        ⟨84424, true, false, [], [94411]⟩
      ]⟩,
    ⟨[31369, 91133], [31369, 91133], .contexts []⟩,
    ⟨[31369, 91133], [31369, 91133], .contexts []⟩,
    ⟨[31369, 91135], [31369, 91135], .contexts []⟩,
    ⟨[31369, 91135], [31369, 91135], .contexts []⟩,
    ⟨[31369, 91135], [31369, 91135], .contexts []⟩,
    ⟨[31369, 91137], [31369, 91137], .contexts []⟩,
    ⟨[31369, 91137], [31369, 91137], .contexts []⟩,
    ⟨[91955], [91955], .contexts []⟩,
    ⟨[31367], [31368], .contexts [
        ⟨84406, false, false, [], []⟩
      ]⟩,
    ⟨[31368], [31368], .contexts []⟩,
    ⟨[91137, 5], [31367, 91955], .contexts [
        ⟨84432, true, false, [31368], [5]⟩,
        ⟨84431, true, false, [31368], [5]⟩,
        ⟨64589, true, false, [], [5]⟩,
        ⟨84430, true, false, [31368], [1, 5]⟩,
        ⟨84429, true, false, [31368], [1, 5]⟩,
        ⟨84428, true, false, [31368], [1, 5]⟩,
        ⟨64582, true, false, [], [1, 5]⟩,
        ⟨84427, true, false, [31368], [5, 1, 5]⟩,
        ⟨84427, true, false, [31368], [5, 1, 5]⟩,
        ⟨84426, true, false, [31368], [5, 1, 5]⟩,
        ⟨84405, true, false, [31368], [5, 1, 5]⟩,
        ⟨84399, true, false, [31368], [5, 1, 5]⟩,
        ⟨1152, false, false, [31368, 91955], []⟩,
        ⟨84433, false, false, [31368], []⟩,
        ⟨84435, true, false, [], [91955]⟩,
        ⟨84435, true, false, [], [91955]⟩,
        ⟨84434, true, false, [], [91955]⟩
      ]⟩,
    ⟨[91957], [31369, 91137], .contexts [
        ⟨68825, true, false, [], []⟩,
        ⟨84436, true, false, [31366], [5]⟩,
        ⟨28, false, false, [31366, 91137], []⟩,
        ⟨84401, true, false, [], [91137]⟩,
        ⟨84431, false, false, [], []⟩,
        ⟨84402, true, false, [], [91137]⟩
      ]⟩,
    ⟨[31377], [31367, 26919], .source 15753⟩,
    ⟨[91137, 3], [31377, 88487], .contexts [
        ⟨84437, true, false, [31368], [3]⟩,
        ⟨68831, false, false, [31368], []⟩,
        ⟨68827, false, false, [31368], []⟩,
        ⟨84406, true, false, [], [26919, 88487]⟩,
        ⟨84438, true, false, [], [88487]⟩
      ]⟩,
    ⟨[91957], [31369, 91137], .contexts [
        ⟨84437, false, false, [], []⟩
      ]⟩,
    ⟨[91957], [31369, 91137], .contexts [
        ⟨84440, false, false, [], []⟩,
        ⟨84432, false, false, [], []⟩
      ]⟩,
    ⟨[91959], [31369, 91135], .contexts [
        ⟨84434, false, false, [31366], [91959]⟩,
        ⟨13, false, false, [31366, 31368], [91959]⟩,
        ⟨68835, true, false, [31366, 31368], []⟩,
        ⟨68834, true, false, [31366, 31368], []⟩,
        ⟨84441, false, false, [31366, 31368], [1]⟩,
        ⟨64590, false, false, [31366], []⟩,
        ⟨84428, false, false, [31366, 31368], []⟩,
        ⟨84429, false, false, [31366, 31368], []⟩,
        ⟨84430, false, false, [31366, 31368], []⟩,
        ⟨84401, true, false, [], [91135]⟩
      ]⟩,
    ⟨[91135, 9], [31367, 91961], .contexts [
        ⟨84442, true, false, [31368], [9]⟩,
        ⟨68845, false, false, [31368], []⟩,
        ⟨68847, false, false, [31368], []⟩,
        ⟨84435, true, false, [], [91961]⟩,
        ⟨84435, true, false, [], [91961]⟩,
        ⟨84434, true, false, [], [91961]⟩
      ]⟩,
    ⟨[31373, 86197], [31373, 86197], .contexts []⟩,
    ⟨[31373, 86197], [31373, 86197], .contexts []⟩,
    ⟨[86193, 11], [86193, 11], .contexts []⟩,
    ⟨[31379], [31372], .source 15754⟩,
    ⟨[31379], [31379], .contexts []⟩,
    ⟨[31372], [31372], .contexts []⟩,
    ⟨[31379], [31372], .contexts [
        ⟨84448, false, false, [], []⟩,
        ⟨84447, false, false, [], []⟩,
        ⟨84449, false, false, [], []⟩,
        ⟨84449, false, false, [], []⟩
      ]⟩,
    ⟨[86193, 11], [31379, 86193], .contexts [
        ⟨84446, false, false, [], []⟩,
        ⟨35645, true, false, [], [11]⟩,
        ⟨35649, true, false, [], [9, 11]⟩,
        ⟨84445, true, false, [31372], [11, 9, 11]⟩,
        ⟨84445, true, false, [31372], [11, 9, 11]⟩,
        ⟨84444, true, false, [31372], [11, 9, 11]⟩,
        ⟨84417, true, false, [31372], [11, 9, 11]⟩,
        ⟨84415, true, false, [31372], [11, 9, 11]⟩,
        ⟨536, false, false, [31372, 86197], []⟩,
        ⟨537, false, false, [31372, 86197], []⟩,
        ⟨49122, false, false, [31372], [9]⟩,
        ⟨35726, false, false, [31372], []⟩,
        ⟨35727, false, false, [31372], []⟩,
        ⟨35644, false, false, [31372], []⟩,
        ⟨35644, false, false, [31372], []⟩,
        ⟨49146, false, false, [31372], []⟩,
        ⟨84450, true, false, [], [86193]⟩
      ]⟩,
    ⟨[31325, 94413], [31325, 94413], .contexts []⟩,
    ⟨[31325, 94411], [31325, 94411], .contexts []⟩,
    ⟨[31325, 94411], [31325, 94411], .contexts []⟩,
    ⟨[94411, 7], [94411, 7], .contexts []⟩,
    ⟨[94411, 7], [31327, 86193], .contexts [
        ⟨84455, false, false, [], []⟩,
        ⟨84454, true, false, [31324], [7]⟩,
        ⟨84453, true, false, [31324], [7]⟩,
        ⟨84092, true, false, [], [7]⟩,
        ⟨84452, true, false, [31324], [9, 7]⟩,
        ⟨84452, true, false, [31324], [9, 7]⟩,
        ⟨84420, true, false, [31324], [9, 7]⟩,
        ⟨84419, true, false, [31324], [9, 7]⟩,
        ⟨579, false, false, [31324, 86195], []⟩,
        ⟨49145, false, false, [31324], []⟩,
        ⟨49144, false, false, [31324], []⟩,
        ⟨49146, false, false, [31324], []⟩,
        ⟨84385, true, false, [], [86193]⟩
      ]⟩,
    ⟨[86193, 7], [31325, 94411], .contexts [
        ⟨84456, true, false, [31326], [7]⟩,
        ⟨38, false, false, [31326, 94411], []⟩,
        ⟨84321, true, false, [], [94411]⟩
      ]⟩,
    ⟨[31375, 94411], [31375, 94411], .contexts []⟩,
    ⟨[31375, 94411], [31375, 94411], .contexts []⟩,
    ⟨[94411, 1], [94409], .contexts [
        ⟨84139, false, false, [], []⟩,
        ⟨84140, false, false, [], []⟩,
        ⟨84087, false, false, [], []⟩,
        ⟨84087, false, false, [], []⟩
      ]⟩,
    ⟨[94411, 0], [94411, 1], .contexts [
        ⟨9, false, false, [94411], []⟩
      ]⟩,
    ⟨[94409, 11], [94409, 11], .contexts []⟩,
    ⟨[94409], [94409], .contexts []⟩,
    ⟨[31374], [31374], .contexts []⟩,
    ⟨[31365], [31374], .contexts [
        ⟨84422, true, true, [], []⟩,
        ⟨84464, false, false, [], []⟩,
        ⟨84464, false, false, [], []⟩
      ]⟩,
    ⟨[94409, 11], [31365, 94409], .contexts [
        ⟨84462, false, false, [], []⟩,
        ⟨84088, true, false, [], [11]⟩,
        ⟨84459, true, false, [31374], [1, 11]⟩,
        ⟨84459, true, false, [31374], [1, 11]⟩,
        ⟨84458, true, false, [31374], [1, 11]⟩,
        ⟨84425, true, false, [31374], [1, 11]⟩,
        ⟨84421, true, false, [31374], [1, 11]⟩,
        ⟨567, false, false, [31374, 94411], []⟩,
        ⟨84461, false, false, [31374], []⟩,
        ⟨84460, false, false, [31374], []⟩,
        ⟨84463, false, false, [31374], []⟩,
        ⟨84465, true, false, [], [94409]⟩
      ]⟩,
    ⟨[91137, 9], [91139], .contexts [
        ⟨64592, false, false, [], []⟩,
        ⟨64853, false, false, [], []⟩,
        ⟨64597, false, false, [], []⟩,
        ⟨64597, false, false, [], []⟩
      ]⟩,
    ⟨[31377, 88487], [31377, 88487], .contexts []⟩,
    ⟨[31377, 88487], [31377, 88487], .contexts []⟩,
    ⟨[31377, 88489], [31377, 88489], .contexts []⟩,
    ⟨[31377, 88489], [31377, 88489], .contexts []⟩,
    ⟨[91139, 3], [91139, 3], .contexts []⟩,
    ⟨[31381], [31376], .source 15755⟩,
    ⟨[31379, 86193], [31379, 86193], .contexts []⟩,
    ⟨[31379, 86193], [31379, 86193], .contexts []⟩,
    ⟨[86191, 11], [86191, 11], .contexts []⟩,
    ⟨[86191], [86191], .contexts []⟩,
    ⟨[31378], [31378], .contexts []⟩,
    ⟨[31373], [31378], .contexts [
        ⟨84447, true, true, [], []⟩,
        ⟨84478, false, false, [], []⟩,
        ⟨84478, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1320. -/
def y322TCIndexRaw1320 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86191, 11], [31373, 86191], .contexts [
        ⟨84476, false, false, [], []⟩,
        ⟨35641, true, false, [], [11]⟩,
        ⟨84475, true, false, [31378], [1, 11]⟩,
        ⟨84475, true, false, [31378], [1, 11]⟩,
        ⟨84474, true, false, [31378], [1, 11]⟩,
        ⟨84451, true, false, [31378], [1, 11]⟩,
        ⟨84446, true, false, [31378], [1, 11]⟩,
        ⟨567, false, false, [31378, 86193], []⟩,
        ⟨9, false, false, [31378, 86193], []⟩,
        ⟨35728, false, false, [31378], []⟩,
        ⟨35729, false, false, [31378], []⟩,
        ⟨35640, false, false, [31378], []⟩,
        ⟨35640, false, false, [31378], []⟩,
        ⟨84477, false, false, [31378], []⟩,
        ⟨84479, true, false, [], [86191]⟩
      ]⟩,
    ⟨[31327, 86193], [31327, 86193], .contexts []⟩,
    ⟨[31327, 86193], [31327, 86193], .contexts []⟩,
    ⟨[94411, 7], [31327, 86193], .contexts [
        ⟨84455, false, false, [], []⟩,
        ⟨84456, false, false, [], []⟩,
        ⟨84481, false, false, [], []⟩,
        ⟨84482, false, false, [], []⟩,
        ⟨84482, false, false, [], []⟩
      ]⟩,
    ⟨[31327, 86191], [31327, 86191], .contexts []⟩,
    ⟨[31327, 86191], [31327, 86191], .contexts []⟩,
    ⟨[86191, 7], [31325, 94409], .contexts [
        ⟨84485, true, false, [31326], [7]⟩,
        ⟨84484, true, false, [31326], [7]⟩,
        ⟨35641, true, false, [], [7]⟩,
        ⟨84483, true, false, [31326], [1, 7]⟩,
        ⟨502, false, false, [31326, 94411], []⟩,
        ⟨84461, false, false, [31326], []⟩,
        ⟨84460, false, false, [31326], []⟩,
        ⟨84463, false, false, [31326], []⟩,
        ⟨84347, true, false, [], [94409]⟩
      ]⟩,
    ⟨[94409, 7], [31327, 86191], .contexts [
        ⟨84486, true, false, [31324], [7]⟩,
        ⟨38, false, false, [31324, 86191], []⟩,
        ⟨84291, true, false, [], [86191]⟩
      ]⟩,
    ⟨[31365, 94409], [31365, 94409], .contexts []⟩,
    ⟨[31365, 94409], [31365, 94409], .contexts []⟩,
    ⟨[94409, 11], [31365, 94409], .contexts [
        ⟨84462, false, false, [], []⟩,
        ⟨84466, false, false, [], []⟩,
        ⟨84488, false, false, [], []⟩,
        ⟨84489, false, false, [], []⟩,
        ⟨84489, false, false, [], []⟩
      ]⟩,
    ⟨[94407, 11], [94407, 11], .contexts []⟩,
    ⟨[94407, 11], [31375, 94407], .contexts [
        ⟨84491, false, false, [], []⟩,
        ⟨84084, true, false, [], [11]⟩,
        ⟨84490, true, false, [31364], [5, 11]⟩,
        ⟨588, false, false, [31364, 94409], []⟩,
        ⟨29, false, false, [31364, 94409], []⟩,
        ⟨84141, false, false, [31364], []⟩,
        ⟨84142, false, false, [31364], []⟩,
        ⟨84083, false, false, [31364], []⟩,
        ⟨84083, false, false, [31364], []⟩,
        ⟨84424, true, false, [], [94407]⟩
      ]⟩,
    ⟨[31377, 88491], [31377, 88491], .contexts []⟩,
    ⟨[91139, 3, 11], [31377, 88491], .contexts [
        ⟨84472, false, false, [], [11]⟩,
        ⟨84472, false, false, [], [11]⟩,
        ⟨84467, true, false, [], [3, 11]⟩,
        ⟨196, false, false, [91137], [11]⟩,
        ⟨197, false, false, [91137], [11]⟩,
        ⟨84439, false, false, [], [9, 11]⟩,
        ⟨84468, false, false, [], [9, 11]⟩,
        ⟨84469, false, false, [], [9, 11]⟩,
        ⟨84469, false, false, [], [9, 11]⟩,
        ⟨50849, false, false, [31377], [11]⟩,
        ⟨84470, false, false, [], [11]⟩,
        ⟨84471, false, false, [], [11]⟩,
        ⟨13, true, false, [], [31377, 88489, 11]⟩,
        ⟨84470, false, false, [], [11]⟩,
        ⟨84471, false, false, [], [11]⟩,
        ⟨84471, false, false, [], [11]⟩,
        ⟨50852, false, false, [31377], []⟩,
        ⟨84493, false, false, [], []⟩
      ]⟩,
    ⟨[91139, 11], [91141], .contexts [
        ⟨64596, false, false, [], []⟩,
        ⟨64852, false, false, [], []⟩,
        ⟨64601, false, false, [], []⟩,
        ⟨64601, false, false, [], []⟩
      ]⟩,
    ⟨[31376], [31376], .contexts []⟩,
    ⟨[31373, 86191], [31373, 86191], .contexts []⟩,
    ⟨[31373, 86191], [31373, 86191], .contexts []⟩,
    ⟨[86189, 11], [86189, 11], .contexts []⟩,
    ⟨[86189], [86189], .contexts []⟩,
    ⟨[86189, 11], [31379, 86189], .contexts [
        ⟨84499, false, false, [], []⟩,
        ⟨35637, true, false, [], [11]⟩,
        ⟨84498, true, false, [31372], [5, 11]⟩,
        ⟨84498, true, false, [31372], [5, 11]⟩,
        ⟨84497, true, false, [31372], [5, 11]⟩,
        ⟨84480, true, false, [31372], [5, 11]⟩,
        ⟨84476, true, false, [31372], [5, 11]⟩,
        ⟨588, false, false, [31372, 86191], []⟩,
        ⟨29, false, false, [31372, 86191], []⟩,
        ⟨35730, false, false, [31372], []⟩,
        ⟨35731, false, false, [31372], []⟩,
        ⟨35636, false, false, [31372], []⟩,
        ⟨35636, false, false, [31372], []⟩,
        ⟨84500, false, false, [31372], []⟩,
        ⟨84450, true, false, [], [86189]⟩
      ]⟩,
    ⟨[31375, 94407], [31375, 94407], .contexts []⟩,
    ⟨[94407, 3], [94405], .contexts [
        ⟨84144, false, false, [], []⟩,
        ⟨84145, false, false, [], []⟩,
        ⟨84079, false, false, [], []⟩,
        ⟨84079, false, false, [], []⟩
      ]⟩,
    ⟨[94407, 2], [94407, 3], .contexts [
        ⟨21, false, false, [94407], []⟩
      ]⟩,
    ⟨[94405, 11], [94405, 11], .contexts []⟩,
    ⟨[94405], [94405], .contexts []⟩,
    ⟨[94405, 11], [31365, 94405], .contexts [
        ⟨84505, false, false, [], []⟩,
        ⟨84080, true, false, [], [11]⟩,
        ⟨84502, true, false, [31374], [3, 11]⟩,
        ⟨84502, true, false, [31374], [3, 11]⟩,
        ⟨84492, true, false, [31374], [3, 11]⟩,
        ⟨84491, true, false, [31374], [3, 11]⟩,
        ⟨603, false, false, [31374, 94407], []⟩,
        ⟨84504, false, false, [31374], []⟩,
        ⟨84503, false, false, [31374], []⟩,
        ⟨84506, false, false, [31374], []⟩,
        ⟨84465, true, false, [], [94405]⟩
      ]⟩,
    ⟨[31379, 86189], [31379, 86189], .contexts []⟩,
    ⟨[31379, 86189], [31379, 86189], .contexts []⟩,
    ⟨[86187, 11], [86187, 11], .contexts []⟩,
    ⟨[86187, 11], [31373, 86187], .contexts [
        ⟨84510, false, false, [], []⟩,
        ⟨35633, true, false, [], [11]⟩,
        ⟨84509, true, false, [31378], [3, 11]⟩,
        ⟨84509, true, false, [31378], [3, 11]⟩,
        ⟨84508, true, false, [31378], [3, 11]⟩,
        ⟨84501, true, false, [31378], [3, 11]⟩,
        ⟨84499, true, false, [31378], [3, 11]⟩,
        ⟨603, false, false, [31378, 86189], []⟩,
        ⟨21, false, false, [31378, 86189], []⟩,
        ⟨35733, false, false, [31378], []⟩,
        ⟨35734, false, false, [31378], []⟩,
        ⟨35632, false, false, [31378], []⟩,
        ⟨35632, false, false, [31378], []⟩,
        ⟨84479, true, false, [], [86187]⟩
      ]⟩,
    ⟨[31365, 94405], [31365, 94405], .contexts []⟩,
    ⟨[94403, 11], [94403, 11], .contexts []⟩,
    ⟨[94403, 11], [31375, 94403], .contexts [
        ⟨84513, false, false, [], []⟩,
        ⟨84076, true, false, [], [11]⟩,
        ⟨84512, true, false, [31364], [1, 11]⟩,
        ⟨84512, true, false, [31364], [1, 11]⟩,
        ⟨84507, true, false, [31364], [1, 11]⟩,
        ⟨84505, true, false, [31364], [1, 11]⟩,
        ⟨567, false, false, [31364, 94405], []⟩,
        ⟨9, false, false, [31364, 94405], []⟩,
        ⟨84146, false, false, [31364], []⟩,
        ⟨84147, false, false, [31364], []⟩,
        ⟨84075, false, false, [31364], []⟩,
        ⟨84075, false, false, [31364], []⟩,
        ⟨84424, true, false, [], [94403]⟩
      ]⟩,
    ⟨[31373, 86187], [31373, 86187], .contexts []⟩,
    ⟨[31373, 86187], [31373, 86187], .contexts []⟩,
    ⟨[86185, 11], [86185, 11], .contexts []⟩,
    ⟨[86185], [86185], .contexts []⟩,
    ⟨[86185, 11], [31379, 86185], .contexts [
        ⟨84517, false, false, [], []⟩,
        ⟨35629, true, false, [], [11]⟩,
        ⟨84516, true, false, [31372], [1, 11]⟩,
        ⟨84516, true, false, [31372], [1, 11]⟩,
        ⟨84515, true, false, [31372], [1, 11]⟩,
        ⟨84511, true, false, [31372], [1, 11]⟩,
        ⟨84510, true, false, [31372], [1, 11]⟩,
        ⟨567, false, false, [31372, 86187], []⟩,
        ⟨9, false, false, [31372, 86187], []⟩,
        ⟨35735, false, false, [31372], []⟩,
        ⟨35736, false, false, [31372], []⟩,
        ⟨35628, false, false, [31372], []⟩,
        ⟨35628, false, false, [31372], []⟩,
        ⟨84518, false, false, [31372], []⟩,
        ⟨84450, true, false, [], [86185]⟩
      ]⟩,
    ⟨[31375, 94403], [31375, 94403], .contexts []⟩,
    ⟨[94403, 11], [31375, 94403], .contexts [
        ⟨84513, false, false, [], []⟩,
        ⟨84514, false, false, [], []⟩,
        ⟨84520, false, false, [], []⟩,
        ⟨84520, false, false, [], []⟩
      ]⟩,
    ⟨[94401, 11], [94401, 11], .contexts []⟩,
    ⟨[94401], [94401], .contexts []⟩,
    ⟨[94401, 11], [31365, 94401], .contexts [
        ⟨84522, false, false, [], []⟩,
        ⟨84072, true, false, [], [11]⟩,
        ⟨84521, true, false, [31374], [15, 11]⟩,
        ⟨615, false, false, [31374, 94403], []⟩,
        ⟨10, false, false, [31374, 94403], []⟩,
        ⟨84148, false, false, [31374], []⟩,
        ⟨84149, false, false, [31374], []⟩,
        ⟨84071, false, false, [31374], []⟩,
        ⟨84071, false, false, [31374], []⟩,
        ⟨84523, false, false, [31374], []⟩,
        ⟨84465, true, false, [], [94401]⟩
      ]⟩,
    ⟨[31379, 86185], [31379, 86185], .contexts []⟩,
    ⟨[31379, 86185], [31379, 86185], .contexts []⟩,
    ⟨[86183, 11], [86183, 11], .contexts []⟩,
    ⟨[86183], [86183], .contexts []⟩,
    ⟨[31365, 94401], [31365, 94401], .contexts []⟩,
    ⟨[31365, 94401], [31365, 94401], .contexts []⟩,
    ⟨[31365, 94399], [31365, 94399], .contexts []⟩,
    ⟨[94399, 11], [94399, 11], .contexts []⟩,
    ⟨[94399], [94399], .contexts []⟩,
    ⟨[31373, 86183], [31373, 86183], .contexts []⟩,
    ⟨[86183, 11], [31373, 86183], .contexts [
        ⟨84527, false, false, [], []⟩,
        ⟨84527, false, false, [], []⟩,
        ⟨35625, true, false, [], [11]⟩,
        ⟨84526, true, false, [31378], [15, 11]⟩,
        ⟨84526, true, false, [31378], [15, 11]⟩,
        ⟨84525, true, false, [31378], [15, 11]⟩,
        ⟨84519, true, false, [31378], [15, 11]⟩,
        ⟨84517, true, false, [31378], [15, 11]⟩,
        ⟨615, false, false, [31378, 86185], []⟩,
        ⟨10, false, false, [31378, 86185], []⟩,
        ⟨35737, false, false, [31378], []⟩,
        ⟨35738, false, false, [31378], []⟩,
        ⟨35624, false, false, [31378], []⟩,
        ⟨35624, false, false, [31378], []⟩,
        ⟨84528, false, false, [31378], []⟩,
        ⟨84479, true, false, [], [86183]⟩,
        ⟨84534, false, false, [], []⟩,
        ⟨84534, false, false, [], []⟩
      ]⟩,
    ⟨[31373, 86181], [31373, 86181], .contexts []⟩,
    ⟨[86181, 11], [86181, 11], .contexts []⟩,
    ⟨[86181], [86181], .contexts []⟩,
    ⟨[86181, 11], [31379, 86181], .contexts [
        ⟨84537, false, false, [], []⟩,
        ⟨84536, true, false, [31372], [11]⟩,
        ⟨35621, true, false, [], [11]⟩,
        ⟨84535, true, false, [31372], [13, 11]⟩,
        ⟨619, false, false, [31372, 86183], []⟩,
        ⟨64, false, false, [31372, 86183], []⟩,
        ⟨35739, false, false, [31372], []⟩,
        ⟨35740, false, false, [31372], []⟩,
        ⟨35620, false, false, [31372], []⟩,
        ⟨35620, false, false, [31372], []⟩,
        ⟨84538, false, false, [31372], []⟩,
        ⟨84450, true, false, [], [86181]⟩
      ]⟩,
    ⟨[31375, 94399], [31375, 94399], .contexts []⟩,
    ⟨[94399, 11], [31375, 94399], .contexts [
        ⟨84532, false, false, [], []⟩,
        ⟨84532, false, false, [], []⟩,
        ⟨84531, true, false, [31364], [11]⟩,
        ⟨84068, true, false, [], [11]⟩,
        ⟨84530, true, false, [31364], [13, 11]⟩,
        ⟨84530, true, false, [31364], [13, 11]⟩,
        ⟨84529, true, false, [31364], [13, 11]⟩,
        ⟨84524, true, false, [31364], [13, 11]⟩,
        ⟨84522, true, false, [31364], [13, 11]⟩,
        ⟨619, false, false, [31364, 94401], []⟩,
        ⟨64, false, false, [31364, 94401], []⟩,
        ⟨84150, false, false, [31364], []⟩,
        ⟨84151, false, false, [31364], []⟩,
        ⟨84067, false, false, [31364], []⟩,
        ⟨84067, false, false, [31364], []⟩,
        ⟨84533, false, false, [31364], []⟩,
        ⟨84424, true, false, [], [94399]⟩,
        ⟨84540, false, false, [], []⟩,
        ⟨84540, false, false, [], []⟩
      ]⟩,
    ⟨[31379, 86181], [31379, 86181], .contexts []⟩,
    ⟨[31379, 86181], [31379, 86181], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1321. -/
def y322TCIndexRaw1321 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[31379, 86177], [31379, 86177], .contexts []⟩,
    ⟨[31379, 86177], [31379, 86177], .contexts []⟩,
    ⟨[86177, 1], [31373, 86181], .contexts [
        ⟨84545, true, false, [31378], [1]⟩,
        ⟨84544, true, false, [31378], [1]⟩,
        ⟨35614, true, false, [], [1]⟩,
        ⟨35617, true, false, [], [11, 1]⟩,
        ⟨84543, true, false, [31378], [1, 11, 1]⟩,
        ⟨84543, true, false, [31378], [1, 11, 1]⟩,
        ⟨84542, true, false, [31378], [1, 11, 1]⟩,
        ⟨84539, true, false, [31378], [1, 11, 1]⟩,
        ⟨84537, true, false, [31378], [1, 11, 1]⟩,
        ⟨628, false, false, [31378, 86181], []⟩,
        ⟨84538, false, false, [31378], []⟩,
        ⟨84479, true, false, [], [86181]⟩
      ]⟩,
    ⟨[94431], [90219, 9], .source 47280⟩,
    ⟨[90219, 9], [94431], .contexts [
        ⟨84547, true, false, [], []⟩
      ]⟩,
    ⟨[94431, 9], [90219], .contexts [
        ⟨84548, true, false, [], [9]⟩,
        ⟨46, false, false, [90219], []⟩,
        ⟨59410, false, false, [], []⟩
      ]⟩,
    ⟨[94431], [94431], .contexts []⟩,
    ⟨[94431], [94431], .contexts []⟩,
    ⟨[90219, 9], [94431], .contexts [
        ⟨84548, false, false, [], []⟩,
        ⟨84550, false, false, [], []⟩,
        ⟨84551, false, false, [], []⟩,
        ⟨84551, false, false, [], []⟩
      ]⟩,
    ⟨[31383], [24695, 16023], .source 15756⟩,
    ⟨[31385], [31383, 24717], .source 15757⟩,
    ⟨[31385, 94431], [31385, 94431], .contexts []⟩,
    ⟨[31385, 94431], [31385, 94431], .contexts []⟩,
    ⟨[31385, 94431], [31385, 94431], .contexts []⟩,
    ⟨[94431, 1], [94431, 1], .contexts []⟩,
    ⟨[94431], [94431], .contexts []⟩,
    ⟨[31385], [31385], .contexts [
        ⟨13, false, false, [], [31385]⟩
      ]⟩,
    ⟨[94431, 1], [31385, 94431], .contexts [
        ⟨84558, false, false, [], []⟩,
        ⟨84552, true, false, [], [1]⟩,
        ⟨691, false, false, [90219], []⟩,
        ⟨694, false, false, [90219], []⟩,
        ⟨59537, false, false, [], [9, 1, 9]⟩,
        ⟨41340, false, false, [24695], [1, 9]⟩,
        ⟨84553, true, false, [], [87335, 1, 9]⟩,
        ⟨59522, false, false, [31383], [9]⟩,
        ⟨59563, false, false, [31383, 24693], [9]⟩,
        ⟨59564, true, false, [31383], [90219, 9]⟩,
        ⟨84554, true, false, [], [90219, 9]⟩,
        ⟨84548, false, false, [31385], []⟩,
        ⟨84555, false, false, [], []⟩,
        ⟨84556, false, false, [], []⟩,
        ⟨84557, false, false, [], []⟩,
        ⟨84559, false, false, [31385], []⟩,
        ⟨84560, true, false, [], [94431]⟩
      ]⟩,
    ⟨[31387], [24705, 26533], .source 15758⟩,
    ⟨[94431, 3], [31387, 91729], .contexts [
        ⟨84552, true, false, [], [3]⟩,
        ⟨196, false, false, [90219], []⟩,
        ⟨197, false, false, [90219], []⟩,
        ⟨59578, false, false, [], [9]⟩,
        ⟨67377, false, false, [24705], []⟩,
        ⟨84562, true, false, [], [91729]⟩,
        ⟨67356, false, false, [31387], []⟩,
        ⟨13, true, false, [], [31387, 91729]⟩
      ]⟩,
    ⟨[31389], [31386], .source 15759⟩,
    ⟨[91729, 3], [31389, 94431], .contexts [
        ⟨84563, true, false, [31386], [3]⟩,
        ⟨20, false, false, [31386, 94431], []⟩,
        ⟨84564, true, false, [], [94431]⟩
      ]⟩,
    ⟨[24695, 87341], [24695, 87341], .contexts []⟩,
    ⟨[24695, 87341], [24695, 87341], .contexts []⟩,
    ⟨[94431, 5], [94431, 5], .contexts []⟩,
    ⟨[94431, 5], [24695, 87341], .contexts [
        ⟨84568, false, false, [], []⟩,
        ⟨84552, true, false, [], [5]⟩,
        ⟨1079, false, false, [90219], []⟩,
        ⟨1080, false, false, [90219], []⟩,
        ⟨59552, false, false, [], [9]⟩,
        ⟨59548, false, false, [], [9]⟩,
        ⟨59549, false, false, [], [9]⟩,
        ⟨59549, false, false, [], [9]⟩,
        ⟨41402, false, false, [24695], []⟩,
        ⟨84566, false, false, [], []⟩,
        ⟨84567, false, false, [], []⟩,
        ⟨41412, false, false, [24695], []⟩,
        ⟨59528, true, false, [], [87341]⟩
      ]⟩,
    ⟨[87341, 5], [24697, 94431], .contexts [
        ⟨84569, true, false, [24694], [5]⟩,
        ⟨28, false, false, [24694, 94431], []⟩,
        ⟨59530, true, false, [], [94431]⟩
      ]⟩,
    ⟨[25875, 91121], [25875, 91121], .contexts []⟩,
    ⟨[25875, 91121], [25875, 91121], .contexts []⟩,
    ⟨[25875, 91123], [25875, 91123], .contexts []⟩,
    ⟨[25875, 91123], [25875, 91123], .contexts []⟩,
    ⟨[94431, 7], [94431, 7], .contexts []⟩,
    ⟨[25875], [25875], .contexts [
        ⟨13, false, false, [], [25875]⟩
      ]⟩,
    ⟨[94431, 7], [25875, 91123], .contexts [
        ⟨84575, false, false, [], []⟩,
        ⟨84552, true, false, [], [7]⟩,
        ⟨1084, false, false, [90219], []⟩,
        ⟨1085, false, false, [90219], []⟩,
        ⟨64478, false, false, [], [9]⟩,
        ⟨84571, false, false, [], [9]⟩,
        ⟨84572, false, false, [], [9]⟩,
        ⟨84572, false, false, [], [9]⟩,
        ⟨64486, false, false, [25875], []⟩,
        ⟨84573, false, false, [], []⟩,
        ⟨84574, false, false, [], []⟩,
        ⟨64498, false, false, [25875], []⟩,
        ⟨84576, true, false, [], [91123]⟩
      ]⟩,
    ⟨[24717], [25874], .contexts [
        ⟨64477, true, true, [], []⟩
      ]⟩,
    ⟨[24737, 84707], [24737, 84707], .contexts []⟩,
    ⟨[24737, 84705], [24737, 84705], .contexts []⟩,
    ⟨[24737, 84705], [24737, 84705], .contexts []⟩,
    ⟨[24737, 84705], [24737, 84705], .contexts [
        ⟨59616, false, false, [24737], []⟩
      ]⟩,
    ⟨[24737, 84705], [24737, 84705], .contexts [
        ⟨13, true, false, [], [24737, 84705]⟩
      ]⟩,
    ⟨[94431, 13], [24737, 84705], .contexts [
        ⟨84552, true, false, [], [13]⟩,
        ⟨201, false, false, [90219], []⟩,
        ⟨202, false, false, [90219], []⟩,
        ⟨59413, false, false, [], [9]⟩,
        ⟨59574, false, false, [], [9]⟩,
        ⟨59602, false, false, [], [9]⟩,
        ⟨59603, true, false, [], [84707, 9]⟩,
        ⟨84579, false, false, [], [9]⟩,
        ⟨84579, false, false, [], [9]⟩,
        ⟨28136, false, false, [24737], []⟩,
        ⟨84580, false, false, [], []⟩,
        ⟨84581, false, false, [], []⟩,
        ⟨84582, false, false, [], []⟩,
        ⟨84583, false, false, [], []⟩
      ]⟩,
    ⟨[31391], [24736], .source 15760⟩,
    ⟨[84705, 13], [31391, 94431], .contexts [
        ⟨84584, true, false, [24736], [13]⟩,
        ⟨59, false, false, [24736, 94431], []⟩,
        ⟨84585, true, false, [], [94431]⟩
      ]⟩,
    ⟨[94433], [94431, 11], .source 47281⟩,
    ⟨[94431, 11], [94433], .contexts [
        ⟨84587, true, false, [], []⟩
      ]⟩,
    ⟨[94433, 11], [94431], .contexts [
        ⟨84588, true, false, [], [11]⟩,
        ⟨53, false, false, [94431], []⟩,
        ⟨84551, false, false, [], []⟩
      ]⟩,
    ⟨[94433], [94433], .contexts []⟩,
    ⟨[94433], [94433], .contexts []⟩,
    ⟨[94431, 11], [94433], .contexts [
        ⟨84588, false, false, [], []⟩,
        ⟨84590, false, false, [], []⟩,
        ⟨84591, false, false, [], []⟩,
        ⟨84591, false, false, [], []⟩
      ]⟩,
    ⟨[31385, 94433], [31385, 94433], .contexts []⟩,
    ⟨[31385, 94433], [31385, 94433], .contexts []⟩,
    ⟨[94433], [94433], .contexts []⟩,
    ⟨[94433, 1], [31385, 94433], .contexts [
        ⟨84592, true, false, [], [1]⟩,
        ⟨562, false, false, [94431], []⟩,
        ⟨563, false, false, [94431], []⟩,
        ⟨84558, false, false, [], [11]⟩,
        ⟨84561, false, false, [], [11]⟩,
        ⟨84555, false, false, [], [11]⟩,
        ⟨84557, false, false, [], [11]⟩,
        ⟨84557, false, false, [], [11]⟩,
        ⟨84588, false, false, [31385], []⟩,
        ⟨84593, false, false, [], []⟩,
        ⟨84594, false, false, [], []⟩,
        ⟨84595, false, false, [31385], []⟩,
        ⟨84560, true, false, [], [94433]⟩
      ]⟩,
    ⟨[24695, 87343], [24695, 87343], .contexts []⟩,
    ⟨[24695, 87343], [24695, 87343], .contexts []⟩,
    ⟨[94433, 5], [94433, 5], .contexts []⟩,
    ⟨[94433, 5], [24695, 87343], .contexts [
        ⟨84599, false, false, [], []⟩,
        ⟨84592, true, false, [], [5]⟩,
        ⟨642, false, false, [94431], []⟩,
        ⟨643, false, false, [94431], []⟩,
        ⟨84568, false, false, [], [11]⟩,
        ⟨84569, false, false, [], [11]⟩,
        ⟨84566, false, false, [], [11]⟩,
        ⟨84567, false, false, [], [11]⟩,
        ⟨84567, false, false, [], [11]⟩,
        ⟨41422, false, false, [24695], []⟩,
        ⟨84597, false, false, [], []⟩,
        ⟨84598, false, false, [], []⟩,
        ⟨41430, false, false, [24695], []⟩,
        ⟨59528, true, false, [], [87343]⟩
      ]⟩,
    ⟨[87343, 5], [24697, 94433], .contexts [
        ⟨84600, true, false, [24694], [5]⟩,
        ⟨28, false, false, [24694, 94433], []⟩,
        ⟨59530, true, false, [], [94433]⟩
      ]⟩,
    ⟨[25875, 91125], [25875, 91125], .contexts []⟩,
    ⟨[25875, 91125], [25875, 91125], .contexts []⟩,
    ⟨[94433, 7], [94433, 7], .contexts []⟩,
    ⟨[94433, 7], [25875, 91125], .contexts [
        ⟨84604, false, false, [], []⟩,
        ⟨84592, true, false, [], [7]⟩,
        ⟨647, false, false, [94431], []⟩,
        ⟨648, false, false, [94431], []⟩,
        ⟨84575, false, false, [], [11]⟩,
        ⟨84577, false, false, [], [11]⟩,
        ⟨84573, false, false, [], [11]⟩,
        ⟨84574, false, false, [], [11]⟩,
        ⟨84574, false, false, [], [11]⟩,
        ⟨64510, false, false, [25875], []⟩,
        ⟨84602, false, false, [], []⟩,
        ⟨84603, false, false, [], []⟩,
        ⟨64518, false, false, [25875], []⟩,
        ⟨84576, true, false, [], [91125]⟩
      ]⟩,
    ⟨[94435], [94433, 13], .source 47282⟩,
    ⟨[94433, 13], [94435], .contexts [
        ⟨84606, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1322. -/
def y322TCIndexRaw1322 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94435, 13], [94433], .contexts [
        ⟨84607, true, false, [], [13]⟩,
        ⟨59, false, false, [94433], []⟩,
        ⟨84591, false, false, [], []⟩
      ]⟩,
    ⟨[94435], [94435], .contexts []⟩,
    ⟨[94435], [94435], .contexts []⟩,
    ⟨[94433, 13], [94435], .contexts [
        ⟨84607, false, false, [], []⟩,
        ⟨84609, false, false, [], []⟩,
        ⟨84610, false, false, [], []⟩,
        ⟨84610, false, false, [], []⟩
      ]⟩,
    ⟨[24695, 87345], [24695, 87345], .contexts []⟩,
    ⟨[24695, 87345], [24695, 87345], .contexts []⟩,
    ⟨[94435, 5], [94435, 5], .contexts []⟩,
    ⟨[94435, 5], [24695, 87345], .contexts [
        ⟨84614, false, false, [], []⟩,
        ⟨84611, true, false, [], [5]⟩,
        ⟨68, false, false, [94433], []⟩,
        ⟨69, false, false, [94433], []⟩,
        ⟨84599, false, false, [], [13]⟩,
        ⟨84600, false, false, [], [13]⟩,
        ⟨84597, false, false, [], [13]⟩,
        ⟨84598, false, false, [], [13]⟩,
        ⟨84598, false, false, [], [13]⟩,
        ⟨41440, false, false, [24695], []⟩,
        ⟨84612, false, false, [], []⟩,
        ⟨84613, false, false, [], []⟩,
        ⟨41448, false, false, [24695], []⟩,
        ⟨59528, true, false, [], [87345]⟩
      ]⟩,
    ⟨[25875, 91127], [25875, 91127], .contexts []⟩,
    ⟨[25875, 91127], [25875, 91127], .contexts []⟩,
    ⟨[94435, 7], [94435, 7], .contexts []⟩,
    ⟨[94435, 7], [25875, 91127], .contexts [
        ⟨84618, false, false, [], []⟩,
        ⟨84611, true, false, [], [7]⟩,
        ⟨73, false, false, [94433], []⟩,
        ⟨74, false, false, [94433], []⟩,
        ⟨84604, false, false, [], [13]⟩,
        ⟨84605, false, false, [], [13]⟩,
        ⟨84602, false, false, [], [13]⟩,
        ⟨84603, false, false, [], [13]⟩,
        ⟨84603, false, false, [], [13]⟩,
        ⟨64544, false, false, [25875], []⟩,
        ⟨84616, false, false, [], []⟩,
        ⟨84617, false, false, [], []⟩,
        ⟨64552, false, false, [25875], []⟩,
        ⟨84576, true, false, [], [91127]⟩
      ]⟩,
    ⟨[94435, 11], [24737, 84705], .contexts [
        ⟨84611, true, false, [], [11]⟩,
        ⟨82, false, false, [94433], []⟩,
        ⟨83, false, false, [94433], []⟩,
        ⟨84589, false, false, [], [13]⟩,
        ⟨84550, false, false, [], [13]⟩,
        ⟨84551, false, false, [], [13]⟩,
        ⟨84551, false, false, [], [13]⟩,
        ⟨84584, false, false, [], []⟩,
        ⟨84580, false, false, [], []⟩,
        ⟨84581, false, false, [], []⟩,
        ⟨84581, false, false, [], []⟩,
        ⟨84582, false, false, [], []⟩,
        ⟨84583, false, false, [], []⟩
      ]⟩,
    ⟨[84705, 11], [31391, 94435], .contexts [
        ⟨84620, true, false, [24736], [11]⟩,
        ⟨53, false, false, [24736, 94435], []⟩,
        ⟨84585, true, false, [], [94435]⟩
      ]⟩,
    ⟨[94437], [94435, 15], .source 47283⟩,
    ⟨[94435, 15], [94437], .contexts [
        ⟨84622, true, false, [], []⟩
      ]⟩,
    ⟨[94437, 15], [94435], .contexts [
        ⟨84623, true, false, [], [15]⟩,
        ⟨1, false, false, [94435], []⟩,
        ⟨84610, false, false, [], []⟩
      ]⟩,
    ⟨[94437], [94437], .contexts []⟩,
    ⟨[94437], [94437], .contexts []⟩,
    ⟨[94435, 15], [94437], .contexts [
        ⟨84623, false, false, [], []⟩,
        ⟨84625, false, false, [], []⟩,
        ⟨84626, false, false, [], []⟩,
        ⟨84626, false, false, [], []⟩
      ]⟩,
    ⟨[24695, 87347], [24695, 87347], .contexts []⟩,
    ⟨[24695, 87347], [24695, 87347], .contexts []⟩,
    ⟨[94437, 5], [94437, 5], .contexts []⟩,
    ⟨[94437, 5], [24695, 87347], .contexts [
        ⟨84630, false, false, [], []⟩,
        ⟨84627, true, false, [], [5]⟩,
        ⟨27, false, false, [94435], []⟩,
        ⟨30, false, false, [94435], []⟩,
        ⟨84614, false, false, [], [15]⟩,
        ⟨84615, false, false, [], [15]⟩,
        ⟨84612, false, false, [], [15]⟩,
        ⟨84613, false, false, [], [15]⟩,
        ⟨84613, false, false, [], [15]⟩,
        ⟨41450, false, false, [24695], []⟩,
        ⟨84628, false, false, [], []⟩,
        ⟨84629, false, false, [], []⟩,
        ⟨41459, false, false, [24695], []⟩,
        ⟨59528, true, false, [], [87347]⟩
      ]⟩,
    ⟨[87347, 5], [24697, 94437], .contexts [
        ⟨84631, true, false, [24694], [5]⟩,
        ⟨28, false, false, [24694, 94437], []⟩,
        ⟨59530, true, false, [], [94437]⟩
      ]⟩,
    ⟨[25875, 91129], [25875, 91129], .contexts []⟩,
    ⟨[25875, 91129], [25875, 91129], .contexts []⟩,
    ⟨[94437, 7], [94437, 7], .contexts []⟩,
    ⟨[94437, 7], [25875, 91129], .contexts [
        ⟨84635, false, false, [], []⟩,
        ⟨84627, true, false, [], [7]⟩,
        ⟨37, false, false, [94435], []⟩,
        ⟨40, false, false, [94435], []⟩,
        ⟨84618, false, false, [], [15]⟩,
        ⟨84619, false, false, [], [15]⟩,
        ⟨84616, false, false, [], [15]⟩,
        ⟨84617, false, false, [], [15]⟩,
        ⟨84617, false, false, [], [15]⟩,
        ⟨64554, false, false, [25875], []⟩,
        ⟨84633, false, false, [], []⟩,
        ⟨84634, false, false, [], []⟩,
        ⟨64564, false, false, [25875], []⟩,
        ⟨84576, true, false, [], [91129]⟩
      ]⟩,
    ⟨[94437], [94437], .contexts []⟩,
    ⟨[94439], [94437, 1], .source 47284⟩,
    ⟨[94437, 1], [94439], .contexts [
        ⟨84638, true, false, [], []⟩
      ]⟩,
    ⟨[94439, 1], [94437], .contexts [
        ⟨84639, true, false, [], [1]⟩,
        ⟨8, false, false, [94437], []⟩,
        ⟨84626, false, false, [], []⟩
      ]⟩,
    ⟨[94439], [94439], .contexts []⟩,
    ⟨[94439], [94439], .contexts []⟩,
    ⟨[94437, 1], [94439], .contexts [
        ⟨84639, false, false, [], []⟩,
        ⟨84641, false, false, [], []⟩,
        ⟨84642, false, false, [], []⟩,
        ⟨84642, false, false, [], []⟩
      ]⟩,
    ⟨[24695, 87349], [24695, 87349], .contexts []⟩,
    ⟨[24695, 87349], [24695, 87349], .contexts []⟩,
    ⟨[94439, 5], [24695, 87349], .contexts [
        ⟨84643, true, false, [], [5]⟩,
        ⟨98, false, false, [94437], []⟩,
        ⟨99, false, false, [94437], []⟩,
        ⟨84630, false, false, [], [1]⟩,
        ⟨84631, false, false, [], [1]⟩,
        ⟨84628, false, false, [], [1]⟩,
        ⟨84629, false, false, [], [1]⟩,
        ⟨84629, false, false, [], [1]⟩,
        ⟨41464, false, false, [24695], []⟩,
        ⟨84644, false, false, [], []⟩,
        ⟨84645, false, false, [], []⟩,
        ⟨41469, false, false, [24695], []⟩,
        ⟨59528, true, false, [], [87349]⟩
      ]⟩,
    ⟨[25875, 91131], [25875, 91131], .contexts []⟩,
    ⟨[25875, 91131], [25875, 91131], .contexts []⟩,
    ⟨[94439, 7], [94439, 7], .contexts []⟩,
    ⟨[94439, 7], [25875, 91131], .contexts [
        ⟨84649, false, false, [], []⟩,
        ⟨84643, true, false, [], [7]⟩,
        ⟨104, false, false, [94437], []⟩,
        ⟨105, false, false, [94437], []⟩,
        ⟨84635, false, false, [], [1]⟩,
        ⟨84636, false, false, [], [1]⟩,
        ⟨84633, false, false, [], [1]⟩,
        ⟨84634, false, false, [], [1]⟩,
        ⟨84634, false, false, [], [1]⟩,
        ⟨64569, false, false, [25875], []⟩,
        ⟨84647, false, false, [], []⟩,
        ⟨84648, false, false, [], []⟩,
        ⟨64576, false, false, [25875], []⟩,
        ⟨84576, true, false, [], [91131]⟩
      ]⟩,
    ⟨[94441], [94439, 3], .source 47285⟩,
    ⟨[94439, 3], [94441], .contexts [
        ⟨84651, true, false, [], []⟩
      ]⟩,
    ⟨[94441, 3], [94439], .contexts [
        ⟨84652, true, false, [], [3]⟩,
        ⟨20, false, false, [94439], []⟩,
        ⟨84642, false, false, [], []⟩
      ]⟩,
    ⟨[94441], [94441], .contexts []⟩,
    ⟨[94441], [94441], .contexts []⟩,
    ⟨[25875, 91133], [25875, 91133], .contexts []⟩,
    ⟨[94441, 7], [25875, 91133], .contexts [
        ⟨84655, true, false, [], [7]⟩,
        ⟨84655, true, false, [], [7]⟩,
        ⟨84654, true, false, [], [7]⟩,
        ⟨84652, true, false, [], [7]⟩,
        ⟨140, false, false, [94439], []⟩,
        ⟨141, false, false, [94439], []⟩,
        ⟨84649, false, false, [], [3]⟩,
        ⟨84650, false, false, [], [3]⟩,
        ⟨84647, false, false, [], [3]⟩,
        ⟨84648, false, false, [], [3]⟩,
        ⟨84648, false, false, [], [3]⟩,
        ⟨64579, false, false, [25875], []⟩,
        ⟨84656, false, false, [], []⟩,
        ⟨84400, false, false, [25875], []⟩,
        ⟨84576, true, false, [], [91133]⟩
      ]⟩,
    ⟨[94443], [94441, 5], .source 47286⟩,
    ⟨[94441, 5], [94443], .contexts [
        ⟨84658, true, false, [], []⟩
      ]⟩,
    ⟨[94443, 5], [94441], .contexts [
        ⟨84659, true, false, [], [5]⟩,
        ⟨28, false, false, [94441], []⟩,
        ⟨84655, false, false, [], []⟩
      ]⟩,
    ⟨[94443], [94443], .contexts []⟩,
    ⟨[94443], [94443], .contexts []⟩,
    ⟨[94441, 3], [94439], .contexts [
        ⟨84653, false, false, [], []⟩
      ]⟩,
    ⟨[24695, 87353], [24695, 87353], .contexts []⟩,
    ⟨[94443, 3], [24695, 87353], .contexts [
        ⟨84662, true, false, [], [3]⟩,
        ⟨84662, true, false, [], [3]⟩,
        ⟨84661, true, false, [], [3]⟩,
        ⟨84659, true, false, [], [3]⟩,
        ⟨166, false, false, [94441], []⟩,
        ⟨169, false, false, [94441], []⟩,
        ⟨84663, false, false, [], [5, 3, 5]⟩,
        ⟨84641, false, false, [], [5, 3, 5]⟩,
        ⟨84642, false, false, [], [5, 3, 5]⟩,
        ⟨84642, false, false, [], [5, 3, 5]⟩,
        ⟨84646, false, false, [], [3, 5]⟩,
        ⟨84644, false, false, [], [3, 5]⟩,
        ⟨84645, false, false, [], [3, 5]⟩,
        ⟨84645, false, false, [], [3, 5]⟩,
        ⟨41471, false, false, [24695], [5]⟩,
        ⟨41477, false, false, [24695], []⟩,
        ⟨84664, false, false, [], []⟩
      ]⟩,
    ⟨[94445], [94443, 1], .source 47287⟩,
    ⟨[94443, 1], [94445], .contexts [
        ⟨84666, true, false, [], []⟩
      ]⟩,
    ⟨[94445, 1], [94443], .contexts [
        ⟨84667, true, false, [], [1]⟩,
        ⟨8, false, false, [94443], []⟩,
        ⟨84662, false, false, [], []⟩
      ]⟩,
    ⟨[94447], [94445, 9], .source 47288⟩,
    ⟨[94445, 9], [94447], .contexts [
        ⟨84669, true, false, [], []⟩
      ]⟩,
    ⟨[94445], [94445], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1323. -/
def y322TCIndexRaw1323 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94449], [94447, 11], .source 47289⟩,
    ⟨[94447, 11], [94449], .contexts [
        ⟨84672, true, false, [], []⟩
      ]⟩,
    ⟨[94447], [94447], .contexts []⟩,
    ⟨[94451], [94449, 1], .source 47290⟩,
    ⟨[94449, 1], [94451], .contexts [
        ⟨84675, true, false, [], []⟩
      ]⟩,
    ⟨[94449], [94449], .contexts []⟩,
    ⟨[94451, 1], [94449], .contexts [
        ⟨84676, true, false, [], [1]⟩,
        ⟨8, false, false, [94449], []⟩,
        ⟨84677, false, false, [], []⟩
      ]⟩,
    ⟨[94453], [94451, 13], .source 47291⟩,
    ⟨[94451, 13], [94453], .contexts [
        ⟨84679, true, false, [], []⟩
      ]⟩,
    ⟨[94451], [94451], .contexts []⟩,
    ⟨[94455], [94453, 15], .source 47292⟩,
    ⟨[94453, 15], [94455], .contexts [
        ⟨84682, true, false, [], []⟩
      ]⟩,
    ⟨[94453], [94453], .contexts []⟩,
    ⟨[94457], [94455, 1], .source 47293⟩,
    ⟨[94455, 1], [94457], .contexts [
        ⟨84685, true, false, [], []⟩
      ]⟩,
    ⟨[94455], [94455], .contexts []⟩,
    ⟨[94459], [94457, 3], .source 47294⟩,
    ⟨[94457, 3], [94459], .contexts [
        ⟨84688, true, false, [], []⟩
      ]⟩,
    ⟨[94457], [94457], .contexts []⟩,
    ⟨[94461], [94459, 5], .source 47295⟩,
    ⟨[94459, 5], [94461], .contexts [
        ⟨84691, true, false, [], []⟩
      ]⟩,
    ⟨[94459], [94459], .contexts []⟩,
    ⟨[94463], [94461, 1], .source 47296⟩,
    ⟨[94461, 1], [94463], .contexts [
        ⟨84694, true, false, [], []⟩
      ]⟩,
    ⟨[94461], [94461], .contexts []⟩,
    ⟨[94465], [94463, 9], .source 47297⟩,
    ⟨[94463, 9], [94465], .contexts [
        ⟨84697, true, false, [], []⟩
      ]⟩,
    ⟨[94463], [94463], .contexts []⟩,
    ⟨[94465, 9], [94463], .contexts [
        ⟨84698, true, false, [], [9]⟩,
        ⟨46, false, false, [94463], []⟩,
        ⟨84699, false, false, [], []⟩
      ]⟩,
    ⟨[94467], [94465, 11], .source 47298⟩,
    ⟨[94465, 11], [94467], .contexts [
        ⟨84701, true, false, [], []⟩
      ]⟩,
    ⟨[94465], [94465], .contexts []⟩,
    ⟨[94469], [94467, 1], .source 47299⟩,
    ⟨[94467, 1], [94469], .contexts [
        ⟨84704, true, false, [], []⟩
      ]⟩,
    ⟨[94467], [94467], .contexts []⟩,
    ⟨[94471], [94469, 13], .source 47300⟩,
    ⟨[94469, 13], [94471], .contexts [
        ⟨84707, true, false, [], []⟩
      ]⟩,
    ⟨[94469], [94469], .contexts []⟩,
    ⟨[94473], [94471, 15], .source 47301⟩,
    ⟨[94471, 15], [94473], .contexts [
        ⟨84710, true, false, [], []⟩
      ]⟩,
    ⟨[94471], [94471], .contexts []⟩,
    ⟨[94473, 15], [94471], .contexts [
        ⟨84711, true, false, [], [15]⟩,
        ⟨1, false, false, [94471], []⟩,
        ⟨84712, false, false, [], []⟩
      ]⟩,
    ⟨[94475], [94473, 1], .source 47302⟩,
    ⟨[94473, 1], [94475], .contexts [
        ⟨84714, true, false, [], []⟩
      ]⟩,
    ⟨[94473], [94473], .contexts []⟩,
    ⟨[94477], [94475, 3], .source 47303⟩,
    ⟨[94475, 3], [94477], .contexts [
        ⟨84717, true, false, [], []⟩
      ]⟩,
    ⟨[94475], [94475], .contexts []⟩,
    ⟨[94479], [94477, 5], .source 47304⟩,
    ⟨[94477, 5], [94479], .contexts [
        ⟨84720, true, false, [], []⟩
      ]⟩,
    ⟨[94477], [94477], .contexts []⟩,
    ⟨[94479, 5], [94477], .contexts [
        ⟨84721, true, false, [], [5]⟩,
        ⟨28, false, false, [94477], []⟩,
        ⟨84722, false, false, [], []⟩
      ]⟩,
    ⟨[94481], [94479, 1], .source 47305⟩,
    ⟨[94479, 1], [94481], .contexts [
        ⟨84724, true, false, [], []⟩
      ]⟩,
    ⟨[94479], [94479], .contexts []⟩,
    ⟨[94481, 1], [94479], .contexts [
        ⟨84725, true, false, [], [1]⟩,
        ⟨8, false, false, [94479], []⟩,
        ⟨84726, false, false, [], []⟩
      ]⟩,
    ⟨[94483], [94481, 9], .source 47306⟩,
    ⟨[94481, 9], [94483], .contexts [
        ⟨84728, true, false, [], []⟩
      ]⟩,
    ⟨[94481], [94481], .contexts []⟩,
    ⟨[94485], [94483, 11], .source 47307⟩,
    ⟨[94483, 11], [94485], .contexts [
        ⟨84731, true, false, [], []⟩
      ]⟩,
    ⟨[94483], [94483], .contexts []⟩,
    ⟨[94487], [94485, 1], .source 47308⟩,
    ⟨[94485, 1], [94487], .contexts [
        ⟨84734, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1324. -/
def y322TCIndexRaw1324 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94485], [94485], .contexts []⟩,
    ⟨[94489], [94487, 13], .source 47309⟩,
    ⟨[94487, 13], [94489], .contexts [
        ⟨84737, true, false, [], []⟩
      ]⟩,
    ⟨[94487], [94487], .contexts []⟩,
    ⟨[94489, 13], [94487], .contexts [
        ⟨84738, true, false, [], [13]⟩,
        ⟨59, false, false, [94487], []⟩,
        ⟨84739, false, false, [], []⟩
      ]⟩,
    ⟨[94491], [94489, 15], .source 47310⟩,
    ⟨[94489, 15], [94491], .contexts [
        ⟨84741, true, false, [], []⟩
      ]⟩,
    ⟨[94489], [94489], .contexts []⟩,
    ⟨[94491, 15], [94489], .contexts [
        ⟨84742, true, false, [], [15]⟩,
        ⟨1, false, false, [94489], []⟩,
        ⟨84743, false, false, [], []⟩
      ]⟩,
    ⟨[94493], [94491, 1], .source 47311⟩,
    ⟨[94491, 1], [94493], .contexts [
        ⟨84745, true, false, [], []⟩
      ]⟩,
    ⟨[94491], [94491], .contexts []⟩,
    ⟨[94493, 1], [94491], .contexts [
        ⟨84746, true, false, [], [1]⟩,
        ⟨8, false, false, [94491], []⟩,
        ⟨84747, false, false, [], []⟩
      ]⟩,
    ⟨[94495], [94493, 3], .source 47312⟩,
    ⟨[94493, 3], [94495], .contexts [
        ⟨84749, true, false, [], []⟩
      ]⟩,
    ⟨[94493], [94493], .contexts []⟩,
    ⟨[94495, 3], [94493], .contexts [
        ⟨84750, true, false, [], [3]⟩,
        ⟨20, false, false, [94493], []⟩,
        ⟨84751, false, false, [], []⟩
      ]⟩,
    ⟨[94497], [94495, 5], .source 47313⟩,
    ⟨[94495], [94495], .contexts []⟩,
    ⟨[94497, 5], [94495], .contexts [
        ⟨84753, false, false, [], [5]⟩,
        ⟨28, false, false, [94495], []⟩,
        ⟨84754, false, false, [], []⟩
      ]⟩,
    ⟨[94499], [94497, 1], .source 47314⟩,
    ⟨[94497], [94497], .contexts []⟩,
    ⟨[94499, 1], [94497], .contexts [
        ⟨84756, false, false, [], [1]⟩,
        ⟨8, false, false, [94497], []⟩,
        ⟨84757, false, false, [], []⟩
      ]⟩,
    ⟨[94501], [94499, 9], .source 47315⟩,
    ⟨[94499], [94499], .contexts []⟩,
    ⟨[94501, 9], [94499], .contexts [
        ⟨84759, false, false, [], [9]⟩,
        ⟨46, false, false, [94499], []⟩,
        ⟨84760, false, false, [], []⟩
      ]⟩,
    ⟨[94503], [94501, 11], .source 47316⟩,
    ⟨[94501], [94501], .contexts []⟩,
    ⟨[94503, 11], [94501], .contexts [
        ⟨84762, false, false, [], [11]⟩,
        ⟨53, false, false, [94501], []⟩,
        ⟨84763, false, false, [], []⟩
      ]⟩,
    ⟨[94505], [94503, 1], .source 47317⟩,
    ⟨[94503], [94503], .contexts []⟩,
    ⟨[94505, 1], [94503], .contexts [
        ⟨84765, false, false, [], [1]⟩,
        ⟨8, false, false, [94503], []⟩,
        ⟨84766, false, false, [], []⟩
      ]⟩,
    ⟨[94507], [94505, 13], .source 47318⟩,
    ⟨[94505, 13], [94507], .contexts [
        ⟨84768, true, false, [], []⟩
      ]⟩,
    ⟨[94505], [94505], .contexts []⟩,
    ⟨[94507, 13], [94505], .contexts [
        ⟨84769, true, false, [], [13]⟩,
        ⟨59, false, false, [94505], []⟩,
        ⟨84770, false, false, [], []⟩
      ]⟩,
    ⟨[94509], [94507, 15], .source 47319⟩,
    ⟨[94507], [94507], .contexts []⟩,
    ⟨[94509, 15], [94507], .contexts [
        ⟨84772, false, false, [], [15]⟩,
        ⟨1, false, false, [94507], []⟩,
        ⟨84773, false, false, [], []⟩
      ]⟩,
    ⟨[94511], [94509, 1], .source 47320⟩,
    ⟨[94509, 1], [94511], .contexts [
        ⟨84775, true, false, [], []⟩
      ]⟩,
    ⟨[94509], [94509], .contexts []⟩,
    ⟨[94511, 1], [94509], .contexts [
        ⟨84776, true, false, [], [1]⟩,
        ⟨8, false, false, [94509], []⟩,
        ⟨84777, false, false, [], []⟩
      ]⟩,
    ⟨[94513], [94511, 3], .source 47321⟩,
    ⟨[94511, 3], [94513], .contexts [
        ⟨84779, true, false, [], []⟩
      ]⟩,
    ⟨[94511], [94511], .contexts []⟩,
    ⟨[94513, 3], [94511], .contexts [
        ⟨84780, true, false, [], [3]⟩,
        ⟨20, false, false, [94511], []⟩,
        ⟨84781, false, false, [], []⟩
      ]⟩,
    ⟨[94515], [94513, 5], .source 47322⟩,
    ⟨[94513], [94513], .contexts []⟩,
    ⟨[94515, 5], [94513], .contexts [
        ⟨84783, false, false, [], [5]⟩,
        ⟨28, false, false, [94513], []⟩,
        ⟨84784, false, false, [], []⟩
      ]⟩,
    ⟨[94517], [94515, 1], .source 47323⟩,
    ⟨[94515], [94515], .contexts []⟩,
    ⟨[94517, 1], [94515], .contexts [
        ⟨84786, false, false, [], [1]⟩,
        ⟨8, false, false, [94515], []⟩,
        ⟨84787, false, false, [], []⟩
      ]⟩,
    ⟨[94519], [94517, 9], .source 47324⟩,
    ⟨[94517], [94517], .contexts []⟩,
    ⟨[94519, 9], [94517], .contexts [
        ⟨84789, false, false, [], [9]⟩,
        ⟨46, false, false, [94517], []⟩,
        ⟨84790, false, false, [], []⟩
      ]⟩,
    ⟨[94521], [94519, 11], .source 47325⟩,
    ⟨[94519], [94519], .contexts []⟩,
    ⟨[94521, 11], [94519], .contexts [
        ⟨84792, false, false, [], [11]⟩,
        ⟨53, false, false, [94519], []⟩,
        ⟨84793, false, false, [], []⟩
      ]⟩,
    ⟨[94523], [94521, 1], .source 47326⟩,
    ⟨[94521], [94521], .contexts []⟩,
    ⟨[94523, 1], [94521], .contexts [
        ⟨84795, false, false, [], [1]⟩,
        ⟨8, false, false, [94521], []⟩,
        ⟨84796, false, false, [], []⟩
      ]⟩,
    ⟨[94525], [94523, 13], .source 47327⟩,
    ⟨[94523], [94523], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1325. -/
def y322TCIndexRaw1325 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94525, 13], [94523], .contexts [
        ⟨84798, false, false, [], [13]⟩,
        ⟨59, false, false, [94523], []⟩,
        ⟨84799, false, false, [], []⟩
      ]⟩,
    ⟨[94527], [94525, 15], .source 47328⟩,
    ⟨[94525], [94525], .contexts []⟩,
    ⟨[94527, 15], [94525], .contexts [
        ⟨84801, false, false, [], [15]⟩,
        ⟨1, false, false, [94525], []⟩,
        ⟨84802, false, false, [], []⟩
      ]⟩,
    ⟨[94529], [94527, 1], .source 47329⟩,
    ⟨[94527], [94527], .contexts []⟩,
    ⟨[94529, 1], [94527], .contexts [
        ⟨84804, false, false, [], [1]⟩,
        ⟨8, false, false, [94527], []⟩,
        ⟨84805, false, false, [], []⟩
      ]⟩,
    ⟨[94531], [94529, 3], .source 47330⟩,
    ⟨[94529, 3], [94531], .contexts [
        ⟨84807, true, false, [], []⟩
      ]⟩,
    ⟨[94529], [94529], .contexts []⟩,
    ⟨[94531, 3], [94529], .contexts [
        ⟨84808, true, false, [], [3]⟩,
        ⟨20, false, false, [94529], []⟩,
        ⟨84809, false, false, [], []⟩
      ]⟩,
    ⟨[94533], [94531, 5], .source 47331⟩,
    ⟨[94531, 5], [94533], .contexts [
        ⟨84811, true, false, [], []⟩
      ]⟩,
    ⟨[94531], [94531], .contexts []⟩,
    ⟨[94533, 5], [94531], .contexts [
        ⟨84812, true, false, [], [5]⟩,
        ⟨28, false, false, [94531], []⟩,
        ⟨84813, false, false, [], []⟩
      ]⟩,
    ⟨[94535], [94533, 1], .source 47332⟩,
    ⟨[94533], [94533], .contexts []⟩,
    ⟨[94535, 1], [94533], .contexts [
        ⟨84815, false, false, [], [1]⟩,
        ⟨8, false, false, [94533], []⟩,
        ⟨84816, false, false, [], []⟩
      ]⟩,
    ⟨[94537], [94535, 9], .source 47333⟩,
    ⟨[94535], [94535], .contexts []⟩,
    ⟨[94537, 9], [94535], .contexts [
        ⟨84818, false, false, [], [9]⟩,
        ⟨46, false, false, [94535], []⟩,
        ⟨84819, false, false, [], []⟩
      ]⟩,
    ⟨[94539], [94537, 11], .source 47334⟩,
    ⟨[94537], [94537], .contexts []⟩,
    ⟨[94539, 11], [94537], .contexts [
        ⟨84821, false, false, [], [11]⟩,
        ⟨53, false, false, [94537], []⟩,
        ⟨84822, false, false, [], []⟩
      ]⟩,
    ⟨[94541], [94539, 1], .source 47335⟩,
    ⟨[94539, 1], [94541], .contexts [
        ⟨84824, true, false, [], []⟩
      ]⟩,
    ⟨[94539], [94539], .contexts []⟩,
    ⟨[94541, 1], [94539], .contexts [
        ⟨84825, true, false, [], [1]⟩,
        ⟨8, false, false, [94539], []⟩,
        ⟨84826, false, false, [], []⟩
      ]⟩,
    ⟨[94543], [94541, 13], .source 47336⟩,
    ⟨[94541, 13], [94543], .contexts [
        ⟨84828, true, false, [], []⟩
      ]⟩,
    ⟨[94541], [94541], .contexts []⟩,
    ⟨[94543, 13], [94541], .contexts [
        ⟨84829, true, false, [], [13]⟩,
        ⟨59, false, false, [94541], []⟩,
        ⟨84830, false, false, [], []⟩
      ]⟩,
    ⟨[94545], [94543, 15], .source 47337⟩,
    ⟨[94543, 15], [94545], .contexts [
        ⟨84832, true, false, [], []⟩
      ]⟩,
    ⟨[94543], [94543], .contexts []⟩,
    ⟨[94545, 15], [94543], .contexts [
        ⟨84833, true, false, [], [15]⟩,
        ⟨1, false, false, [94543], []⟩,
        ⟨84834, false, false, [], []⟩
      ]⟩,
    ⟨[94547], [94545, 1], .source 47338⟩,
    ⟨[94545], [94545], .contexts []⟩,
    ⟨[94547, 1], [94545], .contexts [
        ⟨84836, false, false, [], [1]⟩,
        ⟨8, false, false, [94545], []⟩,
        ⟨84837, false, false, [], []⟩
      ]⟩,
    ⟨[94549], [94547, 3], .source 47339⟩,
    ⟨[94547, 3], [94549], .contexts [
        ⟨84839, true, false, [], []⟩
      ]⟩,
    ⟨[94547], [94547], .contexts []⟩,
    ⟨[94549, 3], [94547], .contexts [
        ⟨84840, true, false, [], [3]⟩,
        ⟨20, false, false, [94547], []⟩,
        ⟨84841, false, false, [], []⟩
      ]⟩,
    ⟨[94551], [94549, 5], .source 47340⟩,
    ⟨[94549, 5], [94551], .contexts [
        ⟨84843, true, false, [], []⟩
      ]⟩,
    ⟨[94549], [94549], .contexts []⟩,
    ⟨[94551, 5], [94549], .contexts [
        ⟨84844, true, false, [], [5]⟩,
        ⟨28, false, false, [94549], []⟩,
        ⟨84845, false, false, [], []⟩
      ]⟩,
    ⟨[94553], [94551, 1], .source 47341⟩,
    ⟨[94551, 1], [94553], .contexts [
        ⟨84847, true, false, [], []⟩
      ]⟩,
    ⟨[94551], [94551], .contexts []⟩,
    ⟨[94553, 1], [94551], .contexts [
        ⟨84848, true, false, [], [1]⟩,
        ⟨8, false, false, [94551], []⟩,
        ⟨84849, false, false, [], []⟩
      ]⟩,
    ⟨[94555], [94553, 9], .source 47342⟩,
    ⟨[94553], [94553], .contexts []⟩,
    ⟨[94555, 9], [94553], .contexts [
        ⟨84851, false, false, [], [9]⟩,
        ⟨46, false, false, [94553], []⟩,
        ⟨84852, false, false, [], []⟩
      ]⟩,
    ⟨[94557], [94555, 11], .source 47343⟩,
    ⟨[94555, 11], [94557], .contexts [
        ⟨84854, true, false, [], []⟩
      ]⟩,
    ⟨[94555], [94555], .contexts []⟩,
    ⟨[94557, 11], [94555], .contexts [
        ⟨84855, true, false, [], [11]⟩,
        ⟨53, false, false, [94555], []⟩,
        ⟨84856, false, false, [], []⟩
      ]⟩,
    ⟨[94557], [94557], .contexts []⟩,
    ⟨[94557], [94557], .contexts []⟩,
    ⟨[94553], [94553], .contexts []⟩,
    ⟨[94549], [94549], .contexts []⟩,
    ⟨[94549, 3], [94547], .contexts [
        ⟨84842, false, false, [], []⟩
      ]⟩,
    ⟨[94547], [94547], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1326. -/
def y322TCIndexRaw1326 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94545], [94545], .contexts []⟩,
    ⟨[94555, 9, 1, 5, 3, 1], [94545], .contexts [
        ⟨84853, false, false, [], [1, 5, 3, 1]⟩,
        ⟨84860, false, false, [], [1, 5, 3, 1]⟩,
        ⟨84852, false, false, [], [1, 5, 3, 1]⟩,
        ⟨84852, false, false, [], [1, 5, 3, 1]⟩,
        ⟨84850, false, false, [], [5, 3, 1]⟩,
        ⟨84849, false, false, [], [5, 3, 1]⟩,
        ⟨84849, false, false, [], [5, 3, 1]⟩,
        ⟨84846, false, false, [], [3, 1]⟩,
        ⟨84861, false, false, [], [3, 1]⟩,
        ⟨84845, false, false, [], [3, 1]⟩,
        ⟨84845, false, false, [], [3, 1]⟩,
        ⟨84862, false, false, [], [1]⟩,
        ⟨84863, false, false, [], [1]⟩,
        ⟨84841, false, false, [], [1]⟩,
        ⟨84841, false, false, [], [1]⟩,
        ⟨84838, false, false, [], []⟩,
        ⟨84864, false, false, [], []⟩,
        ⟨84837, false, false, [], []⟩,
        ⟨84837, false, false, [], []⟩
      ]⟩,
    ⟨[94543], [94543], .contexts []⟩,
    ⟨[94543, 13], [94541], .contexts [
        ⟨84831, false, false, [], []⟩
      ]⟩,
    ⟨[94541], [94541], .contexts []⟩,
    ⟨[94539, 11], [94537], .contexts [
        ⟨84823, false, false, [], []⟩
      ]⟩,
    ⟨[94537], [94537], .contexts []⟩,
    ⟨[94535], [94535], .contexts []⟩,
    ⟨[94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9], [94535], .contexts [
        ⟨84865, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨84835, false, false, [], [13, 1, 11, 9]⟩,
        ⟨84866, false, false, [], [13, 1, 11, 9]⟩,
        ⟨84834, false, false, [], [13, 1, 11, 9]⟩,
        ⟨84834, false, false, [], [13, 1, 11, 9]⟩,
        ⟨84867, false, false, [], [1, 11, 9]⟩,
        ⟨84868, false, false, [], [1, 11, 9]⟩,
        ⟨84830, false, false, [], [1, 11, 9]⟩,
        ⟨84830, false, false, [], [1, 11, 9]⟩,
        ⟨84827, false, false, [], [11, 9]⟩,
        ⟨84826, false, false, [], [11, 9]⟩,
        ⟨84826, false, false, [], [11, 9]⟩,
        ⟨84869, false, false, [], [9]⟩,
        ⟨84870, false, false, [], [9]⟩,
        ⟨84822, false, false, [], [9]⟩,
        ⟨84822, false, false, [], [9]⟩,
        ⟨84820, false, false, [], []⟩,
        ⟨84871, false, false, [], []⟩,
        ⟨84819, false, false, [], []⟩,
        ⟨84819, false, false, [], []⟩
      ]⟩,
    ⟨[94533], [94533], .contexts []⟩,
    ⟨[94533, 5], [94531], .contexts [
        ⟨84814, false, false, [], []⟩
      ]⟩,
    ⟨[94529], [94529], .contexts []⟩,
    ⟨[94529, 1], [94527], .contexts [
        ⟨84806, false, false, [], []⟩
      ]⟩,
    ⟨[94527], [94527], .contexts []⟩,
    ⟨[94525], [94525], .contexts []⟩,
    ⟨[
      94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15
    ], [94525], .contexts [
        ⟨84872, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨84817, false, false, [], [5, 3, 1, 15]⟩,
        ⟨84873, false, false, [], [5, 3, 1, 15]⟩,
        ⟨84816, false, false, [], [5, 3, 1, 15]⟩,
        ⟨84816, false, false, [], [5, 3, 1, 15]⟩,
        ⟨84874, false, false, [], [3, 1, 15]⟩,
        ⟨84813, false, false, [], [3, 1, 15]⟩,
        ⟨84813, false, false, [], [3, 1, 15]⟩,
        ⟨84810, false, false, [], [1, 15]⟩,
        ⟨84875, false, false, [], [1, 15]⟩,
        ⟨84809, false, false, [], [1, 15]⟩,
        ⟨84809, false, false, [], [1, 15]⟩,
        ⟨84876, false, false, [], [15]⟩,
        ⟨84877, false, false, [], [15]⟩,
        ⟨84805, false, false, [], [15]⟩,
        ⟨84805, false, false, [], [15]⟩,
        ⟨84803, false, false, [], []⟩,
        ⟨84878, false, false, [], []⟩,
        ⟨84802, false, false, [], []⟩,
        ⟨84802, false, false, [], []⟩
      ]⟩,
    ⟨[94523], [94523], .contexts []⟩,
    ⟨[94521], [94521], .contexts []⟩,
    ⟨[94519], [94519], .contexts []⟩,
    ⟨[94517], [94517], .contexts []⟩,
    ⟨[94515], [94515], .contexts []⟩,
    ⟨[
      94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [94515], .contexts [
        ⟨84879, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨84800, false, false, [], [1, 11, 9, 1]⟩,
        ⟨84880, false, false, [], [1, 11, 9, 1]⟩,
        ⟨84799, false, false, [], [1, 11, 9, 1]⟩,
        ⟨84799, false, false, [], [1, 11, 9, 1]⟩,
        ⟨84797, false, false, [], [11, 9, 1]⟩,
        ⟨84881, false, false, [], [11, 9, 1]⟩,
        ⟨84796, false, false, [], [11, 9, 1]⟩,
        ⟨84796, false, false, [], [11, 9, 1]⟩,
        ⟨84794, false, false, [], [9, 1]⟩,
        ⟨84882, false, false, [], [9, 1]⟩,
        ⟨84793, false, false, [], [9, 1]⟩,
        ⟨84793, false, false, [], [9, 1]⟩,
        ⟨84791, false, false, [], [1]⟩,
        ⟨84883, false, false, [], [1]⟩,
        ⟨84790, false, false, [], [1]⟩,
        ⟨84790, false, false, [], [1]⟩,
        ⟨84788, false, false, [], []⟩,
        ⟨84884, false, false, [], []⟩,
        ⟨84787, false, false, [], []⟩,
        ⟨84787, false, false, [], []⟩
      ]⟩,
    ⟨[94513], [94513], .contexts []⟩,
    ⟨[94511], [94511], .contexts []⟩,
    ⟨[94507], [94507], .contexts []⟩,
    ⟨[94505], [94505], .contexts []⟩,
    ⟨[
      94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13
    ], [94505], .contexts [
        ⟨84885, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨84785, false, false, [], [3, 1, 15, 13]⟩,
        ⟨84886, false, false, [], [3, 1, 15, 13]⟩,
        ⟨84784, false, false, [], [3, 1, 15, 13]⟩,
        ⟨84784, false, false, [], [3, 1, 15, 13]⟩,
        ⟨84782, false, false, [], [1, 15, 13]⟩,
        ⟨84887, false, false, [], [1, 15, 13]⟩,
        ⟨84781, false, false, [], [1, 15, 13]⟩,
        ⟨84781, false, false, [], [1, 15, 13]⟩,
        ⟨84778, false, false, [], [15, 13]⟩,
        ⟨84777, false, false, [], [15, 13]⟩,
        ⟨84777, false, false, [], [15, 13]⟩,
        ⟨84774, false, false, [], [13]⟩,
        ⟨84888, false, false, [], [13]⟩,
        ⟨84773, false, false, [], [13]⟩,
        ⟨84773, false, false, [], [13]⟩,
        ⟨84771, false, false, [], []⟩,
        ⟨84889, false, false, [], []⟩,
        ⟨84770, false, false, [], []⟩,
        ⟨84770, false, false, [], []⟩
      ]⟩,
    ⟨[94503], [94503], .contexts []⟩,
    ⟨[94501], [94501], .contexts []⟩,
    ⟨[94499], [94499], .contexts []⟩,
    ⟨[94497], [94497], .contexts []⟩,
    ⟨[94495], [94495], .contexts []⟩,
    ⟨[
      94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5
    ], [94495], .contexts [
        ⟨84890, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨84767, false, false, [], [11, 9, 1, 5]⟩,
        ⟨84891, false, false, [], [11, 9, 1, 5]⟩,
        ⟨84766, false, false, [], [11, 9, 1, 5]⟩,
        ⟨84766, false, false, [], [11, 9, 1, 5]⟩,
        ⟨84764, false, false, [], [9, 1, 5]⟩,
        ⟨84892, false, false, [], [9, 1, 5]⟩,
        ⟨84763, false, false, [], [9, 1, 5]⟩,
        ⟨84763, false, false, [], [9, 1, 5]⟩,
        ⟨84761, false, false, [], [1, 5]⟩,
        ⟨84893, false, false, [], [1, 5]⟩,
        ⟨84760, false, false, [], [1, 5]⟩,
        ⟨84760, false, false, [], [1, 5]⟩,
        ⟨84758, false, false, [], [5]⟩,
        ⟨84894, false, false, [], [5]⟩,
        ⟨84757, false, false, [], [5]⟩,
        ⟨84757, false, false, [], [5]⟩,
        ⟨84755, false, false, [], []⟩,
        ⟨84895, false, false, [], []⟩,
        ⟨84754, false, false, [], []⟩,
        ⟨84754, false, false, [], []⟩
      ]⟩,
    ⟨[94493], [94493], .contexts []⟩,
    ⟨[94491], [94491], .contexts []⟩,
    ⟨[94491, 15], [94489], .contexts [
        ⟨84744, false, false, [], []⟩
      ]⟩,
    ⟨[94489], [94489], .contexts []⟩,
    ⟨[94487], [94487], .contexts []⟩,
    ⟨[94485], [94485], .contexts []⟩,
    ⟨[
      94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [94485], .contexts [
        ⟨84896, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨84752, false, false, [], [1, 15, 13, 1]⟩,
        ⟨84897, false, false, [], [1, 15, 13, 1]⟩,
        ⟨84751, false, false, [], [1, 15, 13, 1]⟩,
        ⟨84751, false, false, [], [1, 15, 13, 1]⟩,
        ⟨84748, false, false, [], [15, 13, 1]⟩,
        ⟨84898, false, false, [], [15, 13, 1]⟩,
        ⟨84747, false, false, [], [15, 13, 1]⟩,
        ⟨84747, false, false, [], [15, 13, 1]⟩,
        ⟨84899, false, false, [], [13, 1]⟩,
        ⟨84900, false, false, [], [13, 1]⟩,
        ⟨84743, false, false, [], [13, 1]⟩,
        ⟨84743, false, false, [], [13, 1]⟩,
        ⟨84740, false, false, [], [1]⟩,
        ⟨84901, false, false, [], [1]⟩,
        ⟨84739, false, false, [], [1]⟩,
        ⟨84739, false, false, [], [1]⟩,
        ⟨84735, true, false, [], [1]⟩,
        ⟨8, false, false, [94485], []⟩,
        ⟨84736, false, false, [], []⟩,
        ⟨84902, false, false, [], []⟩,
        ⟨84736, false, false, [], []⟩,
        ⟨84736, false, false, [], []⟩
      ]⟩,
    ⟨[94481], [94481], .contexts []⟩,
    ⟨[94479], [94479], .contexts []⟩,
    ⟨[94479, 5], [94477], .contexts [
        ⟨84723, false, false, [], []⟩
      ]⟩,
    ⟨[94477], [94477], .contexts []⟩,
    ⟨[
      94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5
    ], [94477], .contexts [
        ⟨84903, false, false, [], [11, 9, 1, 5]⟩,
        ⟨84732, true, false, [], [11, 9, 1, 5]⟩,
        ⟨53, false, false, [94483], [9, 1, 5]⟩,
        ⟨84733, false, false, [], [9, 1, 5]⟩,
        ⟨84733, false, false, [], [9, 1, 5]⟩,
        ⟨84733, false, false, [], [9, 1, 5]⟩,
        ⟨84729, true, false, [], [9, 1, 5]⟩,
        ⟨46, false, false, [94481], [1, 5]⟩,
        ⟨84730, false, false, [], [1, 5]⟩,
        ⟨84904, false, false, [], [1, 5]⟩,
        ⟨84730, false, false, [], [1, 5]⟩,
        ⟨84730, false, false, [], [1, 5]⟩,
        ⟨84727, false, false, [], [5]⟩,
        ⟨84905, false, false, [], [5]⟩,
        ⟨84726, false, false, [], [5]⟩,
        ⟨84726, false, false, [], [5]⟩,
        ⟨84906, false, false, [], []⟩,
        ⟨84907, false, false, [], []⟩,
        ⟨84722, false, false, [], []⟩,
        ⟨84722, false, false, [], []⟩
      ]⟩,
    ⟨[94475], [94475], .contexts []⟩,
    ⟨[94473], [94473], .contexts []⟩,
    ⟨[94471], [94471], .contexts []⟩,
    ⟨[94469], [94469], .contexts []⟩,
    ⟨[
      94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13
    ], [94469], .contexts [
        ⟨84908, false, false, [], [3, 1, 15, 13]⟩,
        ⟨84718, true, false, [], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [94475], [1, 15, 13]⟩,
        ⟨84719, false, false, [], [1, 15, 13]⟩,
        ⟨84909, false, false, [], [1, 15, 13]⟩,
        ⟨84719, false, false, [], [1, 15, 13]⟩,
        ⟨84719, false, false, [], [1, 15, 13]⟩,
        ⟨84715, true, false, [], [1, 15, 13]⟩,
        ⟨8, false, false, [94473], [15, 13]⟩,
        ⟨84716, false, false, [], [15, 13]⟩,
        ⟨84910, false, false, [], [15, 13]⟩,
        ⟨84716, false, false, [], [15, 13]⟩,
        ⟨84716, false, false, [], [15, 13]⟩,
        ⟨84713, false, false, [], [13]⟩,
        ⟨84911, false, false, [], [13]⟩,
        ⟨84712, false, false, [], [13]⟩,
        ⟨84712, false, false, [], [13]⟩,
        ⟨84708, true, false, [], [13]⟩,
        ⟨59, false, false, [94469], []⟩,
        ⟨84709, false, false, [], []⟩,
        ⟨84912, false, false, [], []⟩,
        ⟨84709, false, false, [], []⟩,
        ⟨84709, false, false, [], []⟩
      ]⟩,
    ⟨[94465], [94465], .contexts []⟩,
    ⟨[94465, 9], [94463], .contexts [
        ⟨84700, false, false, [], []⟩
      ]⟩,
    ⟨[94463], [94463], .contexts []⟩,
    ⟨[94461], [94461], .contexts []⟩,
    ⟨[
      94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [94461], .contexts [
        ⟨84913, false, false, [], [1, 11, 9, 1]⟩,
        ⟨84705, true, false, [], [1, 11, 9, 1]⟩,
        ⟨8, false, false, [94467], [11, 9, 1]⟩,
        ⟨84706, false, false, [], [11, 9, 1]⟩,
        ⟨84706, false, false, [], [11, 9, 1]⟩,
        ⟨84706, false, false, [], [11, 9, 1]⟩,
        ⟨84702, true, false, [], [11, 9, 1]⟩,
        ⟨53, false, false, [94465], [9, 1]⟩,
        ⟨84703, false, false, [], [9, 1]⟩,
        ⟨84914, false, false, [], [9, 1]⟩,
        ⟨84703, false, false, [], [9, 1]⟩,
        ⟨84703, false, false, [], [9, 1]⟩,
        ⟨84915, false, false, [], [1]⟩,
        ⟨84916, false, false, [], [1]⟩,
        ⟨84699, false, false, [], [1]⟩,
        ⟨84699, false, false, [], [1]⟩,
        ⟨84695, true, false, [], [1]⟩,
        ⟨8, false, false, [94461], []⟩,
        ⟨84696, false, false, [], []⟩,
        ⟨84917, false, false, [], []⟩,
        ⟨84696, false, false, [], []⟩,
        ⟨84696, false, false, [], []⟩
      ]⟩,
    ⟨[94459], [94459], .contexts []⟩,
    ⟨[94457], [94457], .contexts []⟩,
    ⟨[94455], [94455], .contexts []⟩,
    ⟨[
      94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15
    ], [94453], .contexts [
        ⟨84918, false, false, [], [5, 3, 1, 15]⟩,
        ⟨84692, true, false, [], [5, 3, 1, 15]⟩,
        ⟨28, false, false, [94459], [3, 1, 15]⟩,
        ⟨84693, false, false, [], [3, 1, 15]⟩,
        ⟨84919, false, false, [], [3, 1, 15]⟩,
        ⟨84693, false, false, [], [3, 1, 15]⟩,
        ⟨84693, false, false, [], [3, 1, 15]⟩,
        ⟨84689, true, false, [], [3, 1, 15]⟩,
        ⟨20, false, false, [94457], [1, 15]⟩,
        ⟨84690, false, false, [], [1, 15]⟩,
        ⟨84920, false, false, [], [1, 15]⟩,
        ⟨84690, false, false, [], [1, 15]⟩,
        ⟨84690, false, false, [], [1, 15]⟩,
        ⟨84686, true, false, [], [1, 15]⟩,
        ⟨8, false, false, [94455], [15]⟩,
        ⟨84687, false, false, [], [15]⟩,
        ⟨84921, false, false, [], [15]⟩,
        ⟨84687, false, false, [], [15]⟩,
        ⟨84687, false, false, [], [15]⟩,
        ⟨84683, true, false, [], [15]⟩,
        ⟨1, false, false, [94453], []⟩,
        ⟨84684, false, false, [], []⟩,
        ⟨84684, false, false, [], []⟩,
        ⟨84684, false, false, [], []⟩
      ]⟩,
    ⟨[94451], [94451], .contexts []⟩,
    ⟨[94449], [94449], .contexts []⟩,
    ⟨[94447], [94447], .contexts []⟩,
    ⟨[94445], [94445], .contexts []⟩,
    ⟨[
      94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9
    ], [94445], .contexts [
        ⟨84922, false, false, [], [13, 1, 11, 9]⟩,
        ⟨84680, true, false, [], [13, 1, 11, 9]⟩,
        ⟨59, false, false, [94451], [1, 11, 9]⟩,
        ⟨84681, false, false, [], [1, 11, 9]⟩,
        ⟨84923, false, false, [], [1, 11, 9]⟩,
        ⟨84681, false, false, [], [1, 11, 9]⟩,
        ⟨84681, false, false, [], [1, 11, 9]⟩,
        ⟨84678, false, false, [], [11, 9]⟩,
        ⟨84924, false, false, [], [11, 9]⟩,
        ⟨84677, false, false, [], [11, 9]⟩,
        ⟨84677, false, false, [], [11, 9]⟩,
        ⟨84673, true, false, [], [11, 9]⟩,
        ⟨53, false, false, [94447], [9]⟩,
        ⟨84674, false, false, [], [9]⟩,
        ⟨84925, false, false, [], [9]⟩,
        ⟨84674, false, false, [], [9]⟩,
        ⟨84674, false, false, [], [9]⟩,
        ⟨84670, true, false, [], [9]⟩,
        ⟨46, false, false, [94445], []⟩,
        ⟨84671, false, false, [], []⟩,
        ⟨84926, false, false, [], []⟩,
        ⟨84671, false, false, [], []⟩,
        ⟨84671, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1327. -/
def y322TCIndexRaw1327 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[
      94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15
    ], [94435], .contexts [
        ⟨84927, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨84668, false, false, [], [5, 3, 1, 15]⟩,
        ⟨84661, false, false, [], [5, 3, 1, 15]⟩,
        ⟨84662, false, false, [], [5, 3, 1, 15]⟩,
        ⟨84662, false, false, [], [5, 3, 1, 15]⟩,
        ⟨84660, false, false, [], [3, 1, 15]⟩,
        ⟨84654, false, false, [], [3, 1, 15]⟩,
        ⟨84655, false, false, [], [3, 1, 15]⟩,
        ⟨84655, false, false, [], [3, 1, 15]⟩,
        ⟨84663, false, false, [], [1, 15]⟩,
        ⟨84641, false, false, [], [1, 15]⟩,
        ⟨84642, false, false, [], [1, 15]⟩,
        ⟨84642, false, false, [], [1, 15]⟩,
        ⟨84640, false, false, [], [15]⟩,
        ⟨84625, false, false, [], [15]⟩,
        ⟨84626, false, false, [], [15]⟩,
        ⟨84626, false, false, [], [15]⟩,
        ⟨84624, false, false, [], []⟩,
        ⟨84609, false, false, [], []⟩,
        ⟨84610, false, false, [], []⟩,
        ⟨84610, false, false, [], []⟩
      ]⟩,
    ⟨[31393], [31385, 24695], .source 15761⟩,
    ⟨[
      94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1
    ], [31393, 87335], .contexts [
        ⟨84928, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨84608, false, false, [], [1, 11, 9, 1]⟩,
        ⟨84590, false, false, [], [1, 11, 9, 1]⟩,
        ⟨84591, false, false, [], [1, 11, 9, 1]⟩,
        ⟨84591, false, false, [], [1, 11, 9, 1]⟩,
        ⟨84596, false, false, [], [11, 9, 1]⟩,
        ⟨84593, false, false, [], [11, 9, 1]⟩,
        ⟨84594, false, false, [], [11, 9, 1]⟩,
        ⟨84594, false, false, [], [11, 9, 1]⟩,
        ⟨84589, false, false, [31385], [9, 1]⟩,
        ⟨84555, false, false, [], [9, 1]⟩,
        ⟨84556, false, false, [], [9, 1]⟩,
        ⟨84557, false, false, [], [9, 1]⟩,
        ⟨84549, false, false, [31385], [1]⟩,
        ⟨59529, false, false, [31385], []⟩,
        ⟨84929, true, false, [], [87335]⟩
      ]⟩,
    ⟨[31395], [31393, 16707], .source 15762⟩,
    ⟨[31397], [31395, 1021], .source 15763⟩,
    ⟨[31399], [31397, 12937], .source 15764⟩,
    ⟨[31401], [31399, 16353], .source 15765⟩,
    ⟨[
      94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [31401, 85327], .contexts [
        ⟨84930, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨41357, false, false, [31393], [3, 1, 15, 13]⟩,
        ⟨41367, false, false, [31393], [1, 15, 13]⟩,
        ⟨84931, true, false, [], [83941, 1, 15, 13]⟩,
        ⟨23948, false, false, [31395], [15, 13]⟩,
        ⟨84932, true, false, [], [83937, 15, 13]⟩,
        ⟨23903, false, false, [31397], [13]⟩,
        ⟨84933, true, false, [], [83937, 13]⟩,
        ⟨31390, false, false, [31399], []⟩,
        ⟨84934, true, false, [], [85327]⟩
      ]⟩,
    ⟨[31403], [31401, 14671], .source 15766⟩,
    ⟨[31405], [31403, 16349], .source 15767⟩,
    ⟨[31407], [31405, 4217], .source 15768⟩,
    ⟨[31409], [31407, 14153], .source 15769⟩,
    ⟨[
      94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5
    ], [31409, 81357], .contexts [
        ⟨84935, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨31381, false, false, [31401], [11, 9, 1, 5]⟩,
        ⟨84936, true, false, [], [85327, 11, 9, 1, 5]⟩,
        ⟨31387, false, false, [31403], [9, 1, 5]⟩,
        ⟨84937, true, false, [], [83949, 9, 1, 5]⟩,
        ⟨24057, false, false, [31405], [1, 5]⟩,
        ⟨84938, true, false, [], [83949, 1, 5]⟩,
        ⟨24050, false, false, [31407], [5]⟩,
        ⟨84939, true, false, [], [83949, 5]⟩,
        ⟨24039, false, false, [31409], []⟩
      ]⟩,
    ⟨[31411], [31409, 8409], .source 15770⟩,
    ⟨[31413], [31411, 9213], .source 15771⟩,
    ⟨[31415], [31413, 9215], .source 15772⟩,
    ⟨[31417], [31415, 15099], .source 15773⟩,
    ⟨[
      94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [31417, 80803], .contexts [
        ⟨84940, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨8878, false, false, [31409], [1, 15, 13, 1]⟩,
        ⟨11505, false, false, [31409], [1, 15, 13, 1]⟩,
        ⟨84941, true, false, [], [80991, 1, 15, 13, 1]⟩,
        ⟨8446, false, false, [31411], [15, 13, 1]⟩,
        ⟨8278, false, false, [31411], [13, 1]⟩,
        ⟨12056, false, false, [31411], [13, 1]⟩,
        ⟨84942, true, false, [], [80429, 13, 1]⟩,
        ⟨12060, false, false, [31413], [1]⟩,
        ⟨84943, true, false, [], [80803, 1]⟩,
        ⟨14776, false, false, [31415], []⟩,
        ⟨84944, true, false, [], [80803]⟩
      ]⟩,
    ⟨[31419], [31417, 9213], .source 15774⟩,
    ⟨[31421], [31419, 9213], .source 15775⟩,
    ⟨[31423], [31421, 2019], .source 15776⟩,
    ⟨[31425], [31423, 18103], .source 15777⟩,
    ⟨[31427], [31425, 15097], .source 15778⟩,
    ⟨[
      94555, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3
    ], [31427, 86335], .contexts [
        ⟨84945, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨8276, false, false, [31417], [9, 1, 5, 3]⟩,
        ⟨12048, false, false, [31417], [9, 1, 5, 3]⟩,
        ⟨84946, true, false, [], [80431, 9, 1, 5, 3]⟩,
        ⟨8117, false, false, [31419], [1, 5, 3]⟩,
        ⟨12048, false, false, [31419], [1, 5, 3]⟩,
        ⟨84947, true, false, [], [80431, 1, 5, 3]⟩,
        ⟨7896, false, false, [31421], [5, 3]⟩,
        ⟨84948, true, false, [], [80431, 5, 3]⟩,
        ⟨31358, false, false, [31423], [3]⟩,
        ⟨84949, true, false, [], [85325, 3]⟩,
        ⟨36559, false, false, [31425], []⟩,
        ⟨84950, true, false, [], [86335]⟩
      ]⟩,
    ⟨[31429], [31427, 30341], .source 15779⟩,
    ⟨[31431], [31429, 30343], .source 15780⟩,
    ⟨[94557, 1], [94557, 1], .contexts []⟩,
    ⟨[31431], [31431], .contexts [
        ⟨13, false, false, [], [31431]⟩
      ]⟩,
    ⟨[94557, 1], [31431, 89197], .contexts [
        ⟨84954, false, false, [], []⟩,
        ⟨84859, true, false, [], [1]⟩,
        ⟨84859, true, false, [], [1]⟩,
        ⟨84858, true, false, [], [1]⟩,
        ⟨84855, true, false, [], [1]⟩,
        ⟨3787, false, false, [94555], []⟩,
        ⟨3788, false, false, [94555], []⟩,
        ⟨84951, false, false, [], [1, 15, 13]⟩,
        ⟨36574, false, false, [31427], [15, 13]⟩,
        ⟨79984, false, false, [31427], [13]⟩,
        ⟨84952, true, false, [], [93553, 13]⟩,
        ⟨79991, false, false, [31429], []⟩,
        ⟨84953, true, false, [], [89197]⟩,
        ⟨54701, false, false, [31431], []⟩,
        ⟨84955, true, false, [], [89197]⟩
      ]⟩,
    ⟨[31433], [31430], .source 15781⟩,
    ⟨[89197, 1], [31433, 94557], .contexts [
        ⟨84956, true, false, [31430], [1]⟩,
        ⟨8, false, false, [31430, 94557], []⟩,
        ⟨84957, true, false, [], [94557]⟩
      ]⟩,
    ⟨[94557, 11], [94555], .contexts [
        ⟨84857, false, false, [], []⟩
      ]⟩,
    ⟨[31431, 89197], [31431, 89197], .contexts []⟩,
    ⟨[31431, 89197], [31431, 89197], .contexts []⟩,
    ⟨[94557, 1], [31431, 89197], .contexts [
        ⟨84954, false, false, [], []⟩,
        ⟨84956, false, false, [], []⟩,
        ⟨84960, false, false, [], []⟩,
        ⟨84961, false, false, [], []⟩,
        ⟨84961, false, false, [], []⟩
      ]⟩,
    ⟨[31433], [31433], .contexts []⟩,
    ⟨[31431], [31432], .contexts [
        ⟨84957, true, true, [], []⟩
      ]⟩,
    ⟨[94555], [31431, 89201], .contexts [
        ⟨84963, false, false, [31432], [94555]⟩,
        ⟨84957, false, false, [31432], [94555]⟩,
        ⟨8, true, false, [31432, 31430, 94555], []⟩,
        ⟨84856, true, false, [31432, 31430], [1, 1]⟩,
        ⟨84856, true, false, [31432, 31430], [1, 1]⟩,
        ⟨84959, true, false, [31432, 31430], [1, 1]⟩,
        ⟨562, false, false, [31432, 31430, 94557], [1]⟩,
        ⟨563, false, false, [31432, 31430, 94557], [1]⟩,
        ⟨84962, false, false, [31432, 31430], [11, 1]⟩,
        ⟨54509, false, false, [31432], [1]⟩,
        ⟨54685, false, false, [31432], [1]⟩,
        ⟨84955, true, false, [31432, 31430], [89199, 1]⟩,
        ⟨54513, false, false, [31432], []⟩,
        ⟨54530, false, false, [31432], []⟩,
        ⟨54518, false, false, [31432], []⟩,
        ⟨54518, false, false, [31432], []⟩,
        ⟨84964, true, false, [], [89201]⟩
      ]⟩,
    ⟨[31433], [31430], .contexts [
        ⟨84957, false, false, [], []⟩
      ]⟩,
    ⟨[31430], [31430], .contexts []⟩,
    ⟨[31433], [31430], .contexts [
        ⟨84966, false, false, [], []⟩,
        ⟨84967, false, false, [], []⟩,
        ⟨84967, false, false, [], []⟩
      ]⟩,
    ⟨[89201, 9], [31433, 94553], .contexts [
        ⟨84965, true, false, [31430], [9]⟩,
        ⟨84853, false, false, [31430], []⟩,
        ⟨84860, false, false, [31430], []⟩,
        ⟨84968, true, false, [], [94553]⟩
      ]⟩,
    ⟨[89201, 11], [31433, 94557], .contexts [
        ⟨84965, true, false, [31430], [11]⟩,
        ⟨84855, false, false, [31430], []⟩,
        ⟨84858, false, false, [31430], []⟩,
        ⟨84968, true, false, [], [94557]⟩
      ]⟩,
    ⟨[94555], [31431, 89201], .contexts [
        ⟨84965, false, false, [], []⟩
      ]⟩,
    ⟨[31431, 89201], [31431, 89201], .contexts []⟩,
    ⟨[94557, 11], [31431, 89201], .contexts [
        ⟨84959, false, false, [], []⟩,
        ⟨84971, false, false, [], []⟩,
        ⟨84972, false, false, [], []⟩,
        ⟨84972, false, false, [], []⟩,
        ⟨84972, false, false, [], []⟩
      ]⟩,
    ⟨[31435], [31431, 23705], .source 15782⟩,
    ⟨[31437], [31435, 31433], .source 15783⟩,
    ⟨[94557], [94557], .contexts []⟩,
    ⟨[94557], [94557], .contexts []⟩,
    ⟨[31439], [31436], .source 15784⟩,
    ⟨[31436], [31436], .contexts []⟩,
    ⟨[31441], [31431, 23713], .source 15785⟩,
    ⟨[31441, 87109], [31441, 87109], .contexts []⟩,
    ⟨[31443], [31440], .source 15786⟩,
    ⟨[31440], [31440], .contexts []⟩,
    ⟨[87109, 7], [31443, 94557], .contexts [
        ⟨84981, true, false, [31440], [7]⟩,
        ⟨40191, true, false, [], [7]⟩,
        ⟨84980, false, false, [31440], [87111, 11, 7]⟩,
        ⟨54680, true, false, [31440, 31431], [11, 7]⟩,
        ⟨84973, true, false, [31440], [7, 11, 7]⟩,
        ⟨14923, false, false, [31440, 94557], []⟩,
        ⟨84976, false, false, [31440], []⟩,
        ⟨84977, false, false, [31440], []⟩,
        ⟨84983, true, false, [], [94557]⟩,
        ⟨84983, true, false, [], [94557]⟩,
        ⟨84982, true, false, [], [94557]⟩
      ]⟩,
    ⟨[89203], [23687, 86327], .contexts [
        ⟨54648, false, false, [], []⟩,
        ⟨54647, false, false, [], []⟩
      ]⟩,
    ⟨[31445], [31431, 23687], .source 15787⟩,
    ⟨[31447], [31445, 24053], .source 15788⟩,
    ⟨[31449], [31446], .source 15789⟩,
    ⟨[31446], [31446], .contexts []⟩,
    ⟨[89437, 13], [31449, 94557], .contexts [
        ⟨84987, false, false, [31446], [89437, 13]⟩,
        ⟨55978, true, false, [31446, 31445], [13]⟩,
        ⟨84986, false, false, [31446], [86327, 11, 13]⟩,
        ⟨84985, true, false, [31446, 31431], [11, 13]⟩,
        ⟨54517, true, false, [31446, 31431], [11, 13]⟩,
        ⟨84973, true, false, [31446], [13, 11, 13]⟩,
        ⟨1109, false, false, [31446, 94557], []⟩,
        ⟨84976, false, false, [31446], []⟩,
        ⟨84977, false, false, [31446], []⟩,
        ⟨84989, true, false, [], [94557]⟩,
        ⟨84989, true, false, [], [94557]⟩,
        ⟨84988, true, false, [], [94557]⟩
      ]⟩,
    ⟨[94317, 15], [31433, 94557], .contexts [
        ⟨83875, true, false, [], [15]⟩,
        ⟨83845, true, false, [], [1, 15]⟩,
        ⟨84962, true, false, [31430], [15, 1, 15]⟩,
        ⟨2185, false, false, [31430, 94557], []⟩,
        ⟨84976, false, false, [31430], []⟩,
        ⟨84977, false, false, [31430], []⟩,
        ⟨84967, true, false, [], [94557]⟩,
        ⟨84967, true, false, [], [94557]⟩,
        ⟨84966, true, false, [], [94557]⟩,
        ⟨84963, true, false, [], [94557]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1328. -/
def y322TCIndexRaw1328 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94557, 15], [31431, 94317], .contexts [
        ⟨84991, true, false, [31432], [15]⟩,
        ⟨1, false, false, [31432, 94317], []⟩,
        ⟨84964, true, false, [], [94317]⟩
      ]⟩,
    ⟨[31451], [23727, 31433], .source 15790⟩,
    ⟨[31451, 94551], [31451, 94551], .contexts []⟩,
    ⟨[89201], [89201], .contexts []⟩,
    ⟨[31451, 94551, 9], [89201], .contexts [
        ⟨84994, true, false, [], [9]⟩,
        ⟨84850, true, false, [31451], [9]⟩,
        ⟨84993, false, false, [], [94553, 1, 9]⟩,
        ⟨84969, true, false, [23727], [1, 9]⟩,
        ⟨54513, true, false, [23727], [9, 1, 9]⟩,
        ⟨54745, true, false, [], [1, 9, 1, 9]⟩,
        ⟨54745, true, false, [], [1, 9, 1, 9]⟩,
        ⟨54744, true, false, [], [1, 9, 1, 9]⟩,
        ⟨54743, true, false, [], [1, 9, 1, 9]⟩,
        ⟨54683, true, false, [], [9, 1, 9, 1, 9]⟩,
        ⟨4283, false, false, [89201], []⟩,
        ⟨84995, false, false, [], []⟩
      ]⟩,
    ⟨[31453], [31450], .source 15791⟩,
    ⟨[31450], [31450], .contexts []⟩,
    ⟨[89201, 9], [31433, 94553], .contexts [
        ⟨84969, false, false, [], []⟩
      ]⟩,
    ⟨[31433, 94553], [31433, 94553], .contexts []⟩,
    ⟨[31455], [31431, 31451], .source 15792⟩,
    ⟨[94553], [31455, 94551], .contexts [
        ⟨85000, true, false, [31432], []⟩,
        ⟨85000, true, false, [31432], []⟩,
        ⟨84999, true, false, [31432], []⟩,
        ⟨84997, false, false, [31432, 31452], [89201, 9]⟩,
        ⟨84998, false, false, [31432, 31452], [89201, 9]⟩,
        ⟨84998, false, false, [31432, 31452], [89201, 9]⟩,
        ⟨54668, true, false, [31432, 31452, 31450], [9]⟩,
        ⟨84996, true, false, [31432, 31452, 31450], [9]⟩,
        ⟨46, false, false, [31432, 31452, 94551], []⟩,
        ⟨84997, false, true, [31432], [94551]⟩,
        ⟨84994, false, false, [31432], []⟩,
        ⟨84964, true, false, [], [31451, 94551]⟩,
        ⟨85001, true, false, [], [94551]⟩
      ]⟩,
    ⟨[31457], [31433, 31455], .source 15793⟩,
    ⟨[31459], [23705, 31457], .source 15794⟩,
    ⟨[31459, 94549], [31459, 94549], .contexts []⟩,
    ⟨[31461], [31458], .source 15795⟩,
    ⟨[31458], [31458], .contexts []⟩,
    ⟨[94549, 9], [31461, 89201], .contexts [
        ⟨85005, true, false, [31458], [9]⟩,
        ⟨84846, true, false, [], [9]⟩,
        ⟨85004, false, false, [31458], [94551, 5, 9]⟩,
        ⟨85003, false, false, [31458, 23705], [94551, 5, 9]⟩,
        ⟨85002, true, false, [31458, 23705, 31433], [5, 9]⟩,
        ⟨84969, true, false, [31458, 23705], [5, 9]⟩,
        ⟨54682, true, false, [31458], [9, 5, 9]⟩,
        ⟨882, false, false, [31458, 89201], []⟩,
        ⟨84995, false, false, [31458], []⟩,
        ⟨54668, false, false, [31458], []⟩,
        ⟨85007, true, false, [], [89201]⟩,
        ⟨85007, true, false, [], [89201]⟩,
        ⟨85006, true, false, [], [89201]⟩
      ]⟩,
    ⟨[31463], [31456], .source 15796⟩,
    ⟨[31465], [31463, 31459], .source 15797⟩,
    ⟨[94551], [31465, 94549], .contexts [
        ⟨85003, false, false, [31456], [94551]⟩,
        ⟨85002, true, false, [31456, 31433], []⟩,
        ⟨84999, true, false, [31456], []⟩,
        ⟨85008, true, false, [31456, 31460], [9]⟩,
        ⟨46, false, false, [31456, 31460, 94549], []⟩,
        ⟨85006, false, true, [31456], [94549]⟩,
        ⟨85005, false, false, [31456], []⟩,
        ⟨85009, true, false, [], [31459, 94549]⟩,
        ⟨85010, true, false, [], [94549]⟩
      ]⟩,
    ⟨[31467], [31455, 31465], .source 15798⟩,
    ⟨[94553], [31467, 94549], .contexts [
        ⟨85002, false, false, [], []⟩,
        ⟨85011, false, false, [31455], []⟩,
        ⟨85012, true, false, [], [94549]⟩
      ]⟩,
    ⟨[31469], [31464], .source 15799⟩,
    ⟨[31471], [31469, 31467], .source 15800⟩,
    ⟨[94549, 1], [31471, 94549], .contexts [
        ⟨85011, true, false, [31464], [1]⟩,
        ⟨84848, false, false, [31464], []⟩,
        ⟨85013, false, false, [31464], []⟩,
        ⟨85014, true, false, [], [31467, 94549]⟩,
        ⟨85015, true, false, [], [94549]⟩
      ]⟩,
    ⟨[23713, 87111], [23713, 87111], .contexts []⟩,
    ⟨[23713, 87111], [23713, 87111], .contexts []⟩,
    ⟨[31473], [27721, 27727], .source 15801⟩,
    ⟨[31475], [23713, 31473], .source 15802⟩,
    ⟨[31433, 94553], [31433, 31467, 94549], .contexts [
        ⟨85013, false, false, [31433], []⟩
      ]⟩,
    ⟨[31477], [31433, 31467], .source 15803⟩,
    ⟨[94549], [94549], .contexts []⟩,
    ⟨[31479], [31474], .source 15804⟩,
    ⟨[31481], [31479, 31477], .source 15805⟩,
    ⟨[92385, 7], [31481, 94549], .contexts [
        ⟨85020, false, false, [31474], [92385, 7]⟩,
        ⟨85019, false, false, [31474, 23713], [92385, 7]⟩,
        ⟨71642, true, false, [31474, 23713, 27721], [7]⟩,
        ⟨71605, true, false, [31474, 23713], [7]⟩,
        ⟨85018, true, false, [31474], [9, 7]⟩,
        ⟨85018, true, false, [31474], [9, 7]⟩,
        ⟨85017, true, false, [31474], [9, 7]⟩,
        ⟨54680, true, false, [31474], [9, 7]⟩,
        ⟨579, false, false, [31474, 89201], []⟩,
        ⟨47, false, false, [31474, 89201], []⟩,
        ⟨84999, false, false, [31474], []⟩,
        ⟨85021, false, false, [31474], []⟩,
        ⟨85022, true, false, [31474], [94549]⟩,
        ⟨85023, false, false, [31474, 31477], []⟩,
        ⟨85024, true, false, [], [31477, 94549]⟩,
        ⟨85025, true, false, [], [94549]⟩
      ]⟩,
    ⟨[31483], [31480], .source 15806⟩,
    ⟨[94549, 7], [31483, 92385], .contexts [
        ⟨85026, true, false, [31480], [7]⟩,
        ⟨38, false, false, [31480, 92385], []⟩,
        ⟨85027, true, false, [], [92385]⟩
      ]⟩,
    ⟨[31471, 94549], [31471, 94549], .contexts []⟩,
    ⟨[31471, 94549], [31471, 94549], .contexts []⟩,
    ⟨[94549, 3], [94547], .contexts [
        ⟨84862, false, false, [], []⟩
      ]⟩,
    ⟨[31483, 92385], [31483, 92385], .contexts []⟩,
    ⟨[31483, 92385], [31483, 92385], .contexts []⟩,
    ⟨[94549, 7], [31483, 92385], .contexts [
        ⟨85028, false, false, [], []⟩,
        ⟨85032, false, false, [], []⟩,
        ⟨85033, false, false, [], []⟩,
        ⟨85033, false, false, [], []⟩
      ]⟩,
    ⟨[31487], [31483, 27729], .source 15808⟩,
    ⟨[31489], [31486], .source 15809⟩,
    ⟨[31491], [27843, 31489], .source 15810⟩,
    ⟨[31493], [31490], .source 15811⟩,
    ⟨[94547], [31493, 89289], .contexts [
        ⟨85037, false, false, [31490], [94547]⟩,
        ⟨71829, false, false, [31490], [31489, 94547]⟩,
        ⟨85036, false, false, [31490, 27840], [94547]⟩,
        ⟨38, true, false, [31490, 27840, 31486, 94547], []⟩,
        ⟨84841, true, false, [31490, 27840, 31486], [7, 7]⟩,
        ⟨84841, true, false, [31490, 27840, 31486], [7, 7]⟩,
        ⟨84863, true, false, [31490, 27840, 31486], [7, 7]⟩,
        ⟨85031, true, false, [31490, 27840, 31486], [7, 7]⟩,
        ⟨140, false, false, [31490, 27840, 31486, 94549], [7]⟩,
        ⟨141, false, false, [31490, 27840, 31486, 94549], [7]⟩,
        ⟨85034, false, false, [31490, 27840, 31486], [3, 7]⟩,
        ⟨71623, false, false, [31490, 27840, 31486, 31483], [7]⟩,
        ⟨85035, true, false, [31490, 27840, 31486], [90997, 7]⟩,
        ⟨71685, false, false, [31490, 27840], [7]⟩,
        ⟨13, true, false, [31490, 27840, 31486], [31487, 90997, 7]⟩,
        ⟨83642, false, false, [31490, 27840], []⟩,
        ⟨85038, true, false, [], [89289]⟩
      ]⟩,
    ⟨[31491], [31492], .contexts [
        ⟨85038, true, true, [], []⟩
      ]⟩,
    ⟨[31491], [31492], .contexts [
        ⟨85040, false, false, [], []⟩
      ]⟩,
    ⟨[31492], [31492], .contexts []⟩,
    ⟨[31491], [31492], .contexts [
        ⟨85041, false, false, [], []⟩,
        ⟨85042, false, false, [], []⟩,
        ⟨85042, false, false, [], []⟩
      ]⟩,
    ⟨[94547], [31493, 89289], .contexts [
        ⟨85039, false, false, [], []⟩
      ]⟩,
    ⟨[94547], [31493, 89289], .contexts [
        ⟨85044, false, false, [], []⟩
      ]⟩,
    ⟨[31493, 89291], [31493, 89291], .contexts []⟩,
    ⟨[94545], [31493, 89291], .contexts [
        ⟨85041, false, false, [31490], [94545]⟩,
        ⟨13, false, false, [31490, 31492], [94545]⟩,
        ⟨84864, true, false, [31490, 31492], []⟩,
        ⟨84838, true, false, [31490, 31492], []⟩,
        ⟨85045, false, false, [31490, 31492], [1]⟩,
        ⟨55093, false, false, [31490], []⟩,
        ⟨85046, false, false, [31490, 31492], []⟩,
        ⟨85038, true, false, [], [89291]⟩
      ]⟩,
    ⟨[89291, 15], [31491, 94543], .contexts [
        ⟨85047, true, false, [31492], [15]⟩,
        ⟨84835, false, false, [31492], []⟩,
        ⟨84866, false, false, [31492], []⟩,
        ⟨85043, true, false, [], [94543]⟩
      ]⟩,
    ⟨[31495], [27829, 31491], .source 15812⟩,
    ⟨[89291, 15], [31491, 94543], .contexts [
        ⟨85048, false, false, [], []⟩
      ]⟩,
    ⟨[31491, 94543], [31491, 94543], .contexts []⟩,
    ⟨[31491, 94543], [31491, 94543], .contexts []⟩,
    ⟨[89291, 15], [31491, 94543], .contexts [
        ⟨85050, false, false, [], []⟩,
        ⟨85051, false, false, [], []⟩,
        ⟨85052, false, false, [], []⟩,
        ⟨85052, false, false, [], []⟩
      ]⟩,
    ⟨[89291, 14], [89291, 15], .contexts [
        ⟨10, false, false, [89291], []⟩
      ]⟩,
    ⟨[94543, 3], [94543, 3], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1329. -/
def y322TCIndexRaw1329 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94543], [94543], .contexts []⟩,
    ⟨[31497], [31494], .source 15813⟩,
    ⟨[31499], [31497, 31491], .source 15814⟩,
    ⟨[94543, 3], [31499, 94543], .contexts [
        ⟨85055, false, false, [], []⟩,
        ⟨85049, false, false, [31494], [94543, 3]⟩,
        ⟨85048, true, false, [31494, 27829], [3]⟩,
        ⟨71809, true, false, [31494], [15, 3]⟩,
        ⟨71809, true, false, [31494], [15, 3]⟩,
        ⟨71814, true, false, [31494], [15, 3]⟩,
        ⟨55097, true, false, [31494], [15, 3]⟩,
        ⟨499, false, false, [31494, 89291], []⟩,
        ⟨85054, false, false, [31494], []⟩,
        ⟨85053, false, false, [31494], []⟩,
        ⟨85056, false, false, [31494, 31491], []⟩,
        ⟨85057, true, false, [], [31491, 94543]⟩,
        ⟨85058, true, false, [], [94543]⟩
      ]⟩,
    ⟨[89289, 1], [89291], .contexts [
        ⟨55093, false, false, [], []⟩,
        ⟨55138, false, false, [], []⟩,
        ⟨55098, false, false, [], []⟩,
        ⟨55098, false, false, [], []⟩
      ]⟩,
    ⟨[89287, 1], [89287, 1], .contexts []⟩,
    ⟨[89287, 1], [31491, 94543], .contexts [
        ⟨85061, false, false, [], []⟩,
        ⟨55090, true, false, [], [1]⟩,
        ⟨55090, true, false, [], [1]⟩,
        ⟨55142, true, false, [], [1]⟩,
        ⟨55141, true, false, [], [1]⟩,
        ⟨7, false, false, [89289], []⟩,
        ⟨11, false, false, [89289], []⟩,
        ⟨85060, false, false, [], [15]⟩,
        ⟨85050, false, false, [], []⟩,
        ⟨85051, false, false, [], []⟩,
        ⟨85052, false, false, [], []⟩,
        ⟨85052, false, false, [], []⟩,
        ⟨85056, false, false, [31491], []⟩,
        ⟨13, true, false, [], [31491, 94543]⟩
      ]⟩,
    ⟨[23935, 89291], [23935, 89291], .contexts []⟩,
    ⟨[31501], [23935, 31491], .source 15815⟩,
    ⟨[94543, 9], [94543, 9], .contexts []⟩,
    ⟨[31503], [31500], .source 15816⟩,
    ⟨[31505], [31503, 31491], .source 15817⟩,
    ⟨[94543, 9], [31505, 94543], .contexts [
        ⟨85065, false, false, [], []⟩,
        ⟨85064, false, false, [31500], [94543, 9]⟩,
        ⟨85048, true, false, [31500, 23935], [9]⟩,
        ⟨85063, true, false, [31500], [15, 9]⟩,
        ⟨85063, true, false, [31500], [15, 9]⟩,
        ⟨55468, true, false, [31500], [15, 9]⟩,
        ⟨55465, true, false, [31500], [15, 9]⟩,
        ⟨935, false, false, [31500, 89291], []⟩,
        ⟨85054, false, false, [31500], []⟩,
        ⟨85053, false, false, [31500], []⟩,
        ⟨85056, false, false, [31500, 31491], []⟩,
        ⟨85066, true, false, [], [31491, 94543]⟩,
        ⟨85067, true, false, [], [94543]⟩
      ]⟩,
    ⟨[27837, 83459], [27837, 83459], .contexts []⟩,
    ⟨[27837, 83459], [27837, 83459], .contexts []⟩,
    ⟨[31491, 94543, 13], [31491, 94541], .contexts [
        ⟨84831, false, false, [31491], []⟩
      ]⟩,
    ⟨[31491, 94541], [31491, 94541], .contexts []⟩,
    ⟨[31491, 94541], [31491, 94541], .contexts []⟩,
    ⟨[31491, 94541], [31491, 94541], .contexts []⟩,
    ⟨[83455, 15], [83455, 15], .contexts []⟩,
    ⟨[94541], [94541], .contexts []⟩,
    ⟨[31507], [27839, 31491], .source 15818⟩,
    ⟨[83455, 15], [31507, 94541], .contexts [
        ⟨85075, false, false, [], []⟩,
        ⟨21245, true, false, [], [15]⟩,
        ⟨21249, true, false, [], [13, 15]⟩,
        ⟨85070, true, false, [27836], [15, 13, 15]⟩,
        ⟨85070, true, false, [27836], [15, 13, 15]⟩,
        ⟨85069, true, false, [27836], [15, 13, 15]⟩,
        ⟨71825, true, false, [27836], [15, 13, 15]⟩,
        ⟨2022, false, false, [27836, 89291], []⟩,
        ⟨89, false, false, [27836, 89291], []⟩,
        ⟨85053, false, false, [27836], [13]⟩,
        ⟨85071, false, false, [27836], []⟩,
        ⟨85072, false, false, [27836], []⟩,
        ⟨85073, false, false, [27836], []⟩,
        ⟨85074, false, false, [27836], []⟩,
        ⟨85076, false, false, [27836, 31491], []⟩,
        ⟨71822, true, false, [], [31491, 94541]⟩,
        ⟨85077, true, false, [], [94541]⟩
      ]⟩,
    ⟨[31509], [31506], .source 15819⟩,
    ⟨[31499, 94543], [31499, 94543], .contexts []⟩,
    ⟨[94543, 13], [94541], .contexts [
        ⟨84867, false, false, [], []⟩,
        ⟨84868, false, false, [], []⟩,
        ⟨84830, false, false, [], []⟩,
        ⟨84830, false, false, [], []⟩
      ]⟩,
    ⟨[94543, 12], [94543, 13], .contexts [
        ⟨64, false, false, [94543], []⟩
      ]⟩,
    ⟨[31511], [31498], .source 15820⟩,
    ⟨[31498], [31498], .contexts []⟩,
    ⟨[31491, 94539], [31491, 94539], .contexts []⟩,
    ⟨[31491, 94539], [31491, 94539], .contexts []⟩,
    ⟨[94539, 13], [94539, 13], .contexts []⟩,
    ⟨[31490], [31490], .contexts []⟩,
    ⟨[94539, 13], [31493, 89283], .contexts [
        ⟨85087, false, false, [], []⟩,
        ⟨85086, true, false, [31490], [13]⟩,
        ⟨85085, true, false, [31490], [13]⟩,
        ⟨84827, true, false, [], [13]⟩,
        ⟨85074, true, false, [31490], [1, 13]⟩,
        ⟨85073, true, false, [31490], [1, 13]⟩,
        ⟨85072, true, false, [31490], [1, 13]⟩,
        ⟨85071, true, false, [31490], [1, 13]⟩,
        ⟨85052, true, false, [31490], [13, 1, 13]⟩,
        ⟨85052, true, false, [31490], [13, 1, 13]⟩,
        ⟨85051, true, false, [31490], [13, 1, 13]⟩,
        ⟨85062, true, false, [31490], [13, 1, 13]⟩,
        ⟨85061, true, false, [31490], [13, 1, 13]⟩,
        ⟨919, false, false, [31490, 89287], []⟩,
        ⟨116, false, false, [31490, 89287], []⟩,
        ⟨83662, false, false, [31490], [1]⟩,
        ⟨55145, false, false, [31490], []⟩,
        ⟨55146, false, false, [31490], []⟩,
        ⟨55082, false, false, [31490], []⟩,
        ⟨55082, false, false, [31490], []⟩,
        ⟨83734, false, false, [31490], []⟩,
        ⟨85088, true, false, [], [89283]⟩,
        ⟨85088, true, false, [], [89283]⟩,
        ⟨85038, true, false, [], [89283]⟩
      ]⟩,
    ⟨[89283, 13], [31491, 94539], .contexts [
        ⟨85089, true, false, [31492], [13]⟩,
        ⟨59, false, false, [31492, 94539], []⟩,
        ⟨85040, true, false, [], [94539]⟩
      ]⟩,
    ⟨[31505, 94543], [31505, 94543], .contexts []⟩,
    ⟨[31513], [31504], .source 15821⟩,
    ⟨[31504], [31504], .contexts []⟩,
    ⟨[94541, 9], [31513, 94541], .contexts [
        ⟨84831, true, false, [], [9]⟩,
        ⟨85091, true, false, [31504], [13, 9]⟩,
        ⟨85091, true, false, [31504], [13, 9]⟩,
        ⟨85068, true, false, [31504], [13, 9]⟩,
        ⟨85065, true, false, [31504], [13, 9]⟩,
        ⟨511, false, false, [31504, 94543], []⟩,
        ⟨85082, false, false, [31504], []⟩,
        ⟨85081, false, false, [31504], []⟩,
        ⟨85076, false, false, [31504], []⟩,
        ⟨85093, true, false, [], [94541]⟩,
        ⟨85093, true, false, [], [94541]⟩,
        ⟨85092, true, false, [], [94541]⟩
      ]⟩,
    ⟨[31507, 94541], [31507, 94541], .contexts []⟩,
    ⟨[83455, 15], [31507, 94541], .contexts [
        ⟨85075, false, false, [], []⟩,
        ⟨85078, false, false, [], []⟩,
        ⟨85095, false, false, [], []⟩,
        ⟨85095, false, false, [], []⟩
      ]⟩,
    ⟨[94539, 15], [94539, 15], .contexts []⟩,
    ⟨[31509], [31506], .contexts [
        ⟨85079, false, false, [], []⟩
      ]⟩,
    ⟨[31506], [31506], .contexts []⟩,
    ⟨[94539, 15], [31509, 83453], .contexts [
        ⟨85097, false, false, [], []⟩,
        ⟨84827, true, false, [], [15]⟩,
        ⟨85096, true, false, [31506], [1, 15]⟩,
        ⟨1666, false, false, [31506, 83455], []⟩,
        ⟨49905, false, false, [31506], []⟩,
        ⟨43544, false, false, [31506], []⟩,
        ⟨49907, false, false, [31506], []⟩,
        ⟨85099, true, false, [], [83453]⟩,
        ⟨85099, true, false, [], [83453]⟩,
        ⟨85098, true, false, [], [83453]⟩
      ]⟩,
    ⟨[83453, 15], [31507, 94539], .contexts [
        ⟨85100, true, false, [31508], [15]⟩,
        ⟨1, false, false, [31508, 94539], []⟩,
        ⟨85079, false, true, [], [94539]⟩
      ]⟩,
    ⟨[31515], [31509, 20905], .source 15822⟩,
    ⟨[94541, 11], [31515, 83693], .contexts [
        ⟨85096, true, false, [31506], [11]⟩,
        ⟨52, false, false, [31506, 83455], []⟩,
        ⟨55, false, false, [31506, 83455], []⟩,
        ⟨43543, false, false, [31506], [15]⟩,
        ⟨22646, false, false, [31506, 20905], []⟩,
        ⟨43478, false, false, [31506, 20905], []⟩,
        ⟨85098, true, false, [], [20905, 83693]⟩,
        ⟨85102, true, false, [], [83693]⟩
      ]⟩,
    ⟨[31517], [31514], .source 15823⟩,
    ⟨[31493, 89283], [31493, 89283], .contexts []⟩,
    ⟨[31493, 89281], [31493, 89281], .contexts []⟩,
    ⟨[94539, 11], [94537], .contexts [
        ⟨84869, false, false, [], []⟩,
        ⟨84870, false, false, [], []⟩,
        ⟨84822, false, false, [], []⟩,
        ⟨84822, false, false, [], []⟩
      ]⟩,
    ⟨[89281, 13], [89281, 13], .contexts []⟩,
    ⟨[89281, 13], [31491, 94537], .contexts [
        ⟨85108, false, false, [], []⟩,
        ⟨85106, true, false, [31492], [13]⟩,
        ⟨55079, true, false, [], [13]⟩,
        ⟨85105, true, false, [31492], [11, 13]⟩,
        ⟨85105, true, false, [31492], [11, 13]⟩,
        ⟨85089, true, false, [31492], [11, 13]⟩,
        ⟨85087, true, false, [31492], [11, 13]⟩,
        ⟨931, false, false, [31492, 94539], []⟩,
        ⟨54, false, false, [31492, 94539], []⟩,
        ⟨85107, false, false, [31492], []⟩,
        ⟨85042, true, false, [], [94537]⟩,
        ⟨85042, true, false, [], [94537]⟩,
        ⟨85041, true, false, [], [94537]⟩
      ]⟩,
    ⟨[31509, 83453], [31509, 83453], .contexts []⟩,
    ⟨[31509, 83453], [31509, 83453], .contexts []⟩,
    ⟨[83695, 11], [83695, 11], .contexts []⟩,
    ⟨[31517], [31514], .contexts [
        ⟨85104, false, false, [], []⟩
      ]⟩,
    ⟨[31514], [31514], .contexts []⟩,
    ⟨[83695, 11], [31517, 94539], .contexts [
        ⟨85112, false, false, [], []⟩,
        ⟨85102, false, false, [31514], [83695, 11]⟩,
        ⟨43612, true, false, [31514, 31509], [11]⟩,
        ⟨21237, true, false, [31514, 31509], [15, 11]⟩,
        ⟨85111, true, false, [31514], [11, 15, 11]⟩,
        ⟨85111, true, false, [31514], [11, 15, 11]⟩,
        ⟨85110, true, false, [31514], [11, 15, 11]⟩,
        ⟨85100, true, false, [31514], [11, 15, 11]⟩,
        ⟨85097, true, false, [31514], [11, 15, 11]⟩,
        ⟨2289, false, false, [31514, 94539], []⟩,
        ⟨85114, true, false, [], [94539]⟩,
        ⟨85114, true, false, [], [94539]⟩,
        ⟨85113, true, false, [], [94539]⟩
      ]⟩,
    ⟨[94537], [31515, 83695], .contexts [
        ⟨85107, true, false, [], []⟩,
        ⟨85115, true, false, [31516], [11]⟩,
        ⟨53, false, false, [31516, 83695], []⟩,
        ⟨85104, false, true, [], [83695]⟩
      ]⟩,
    ⟨[83695, 9], [31517, 94535], .contexts [
        ⟨85116, true, false, [31514], [9]⟩,
        ⟨84820, false, false, [31514], []⟩,
        ⟨84871, false, false, [31514], []⟩,
        ⟨85114, true, false, [], [94535]⟩,
        ⟨85114, true, false, [], [94535]⟩,
        ⟨85113, true, false, [], [94535]⟩
      ]⟩,
    ⟨[31519], [31517, 31493], .source 15824⟩,
    ⟨[94537], [31515, 83695], .contexts [
        ⟨85116, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1330. -/
def y322TCIndexRaw1330 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[31491, 94537], [31491, 31515, 83695], .contexts [
        ⟨85119, false, false, [31491], []⟩
      ]⟩,
    ⟨[31521], [31491, 31515], .source 15825⟩,
    ⟨[89281, 13], [31521, 83695], .contexts [
        ⟨85108, false, false, [], []⟩,
        ⟨85109, false, false, [], []⟩,
        ⟨85120, false, false, [], []⟩,
        ⟨85121, true, false, [], [83695]⟩
      ]⟩,
    ⟨[83697, 13], [83697, 13], .contexts []⟩,
    ⟨[31523], [31520], .source 15826⟩,
    ⟨[31525], [31523, 31203], .source 15827⟩,
    ⟨[83697, 13], [31525, 88679], .contexts [
        ⟨85123, false, false, [], []⟩,
        ⟨22654, true, false, [], [13]⟩,
        ⟨85122, true, false, [31520], [3, 13]⟩,
        ⟨1132, false, false, [31520, 89281], []⟩,
        ⟨21, false, false, [31520, 89281], []⟩,
        ⟨83746, false, false, [31520], []⟩,
        ⟨83740, false, false, [31520], []⟩,
        ⟨83741, false, false, [31520], []⟩,
        ⟨83741, false, false, [31520], []⟩,
        ⟨76322, false, false, [31520, 31203], []⟩,
        ⟨85124, true, false, [], [31203, 88679]⟩,
        ⟨85125, true, false, [], [88679]⟩
      ]⟩,
    ⟨[31527], [31524], .source 15828⟩,
    ⟨[31529], [31521, 31517], .source 15829⟩,
    ⟨[89279], [89279], .contexts []⟩,
    ⟨[31531], [31528], .source 15830⟩,
    ⟨[31531], [31528], .contexts [
        ⟨85130, false, false, [], []⟩
      ]⟩,
    ⟨[31528], [31528], .contexts []⟩,
    ⟨[94535, 13], [31531, 89279], .contexts [
        ⟨85128, false, false, [31528], [94535, 13]⟩,
        ⟨85117, true, false, [31528, 31521], [13]⟩,
        ⟨85122, true, false, [31528], [9, 13]⟩,
        ⟨942, false, false, [31528, 89281], []⟩,
        ⟨47, false, false, [31528, 89281], []⟩,
        ⟨55150, false, false, [31528], []⟩,
        ⟨55151, false, false, [31528], []⟩,
        ⟨55074, false, false, [31528], []⟩,
        ⟨55074, false, false, [31528], []⟩,
        ⟨85129, false, false, [31528], []⟩,
        ⟨85132, true, false, [], [89279]⟩,
        ⟨85132, true, false, [], [89279]⟩,
        ⟨85131, true, false, [], [89279]⟩
      ]⟩,
    ⟨[89279, 13], [31529, 94535], .contexts [
        ⟨85133, true, false, [31530], [13]⟩,
        ⟨59, false, false, [31530, 94535], []⟩,
        ⟨85130, false, true, [], [94535]⟩
      ]⟩,
    ⟨[83695, 9], [31517, 94535], .contexts [
        ⟨85117, false, false, [], []⟩
      ]⟩,
    ⟨[31517, 94535], [31517, 94535], .contexts []⟩,
    ⟨[83695, 9], [31517, 94535], .contexts [
        ⟨85135, false, false, [], []⟩,
        ⟨85136, false, false, [], []⟩,
        ⟨85136, false, false, [], []⟩
      ]⟩,
    ⟨[83695, 8], [83695, 9], .contexts [
        ⟨47, false, false, [83695], []⟩
      ]⟩,
    ⟨[83449, 15], [83449, 15], .contexts []⟩,
    ⟨[94535], [94535], .contexts []⟩,
    ⟨[31533], [20905, 31517], .source 15831⟩,
    ⟨[83449, 15], [31533, 94535], .contexts [
        ⟨85139, false, false, [], []⟩,
        ⟨21233, true, false, [], [15]⟩,
        ⟨43609, true, false, [20902], [9, 15]⟩,
        ⟨43609, true, false, [20902], [9, 15]⟩,
        ⟨43608, true, false, [20902], [9, 15]⟩,
        ⟨43613, true, false, [20902], [9, 15]⟩,
        ⟨1671, false, false, [20902, 83695], []⟩,
        ⟨85138, false, false, [20902], []⟩,
        ⟨85137, false, false, [20902], []⟩,
        ⟨85140, false, false, [20902, 31517], []⟩,
        ⟨43226, true, false, [], [31517, 94535]⟩,
        ⟨85141, true, false, [], [94535]⟩
      ]⟩,
    ⟨[31535], [31532], .source 15832⟩,
    ⟨[86639, 5], [86639, 5], .contexts []⟩,
    ⟨[31537], [26863, 31517], .source 15833⟩,
    ⟨[86639, 5], [31537, 94535], .contexts [
        ⟨85144, false, false, [], []⟩,
        ⟨38276, true, false, [], [5]⟩,
        ⟨68514, true, false, [26864], [9, 5]⟩,
        ⟨68514, true, false, [26864], [9, 5]⟩,
        ⟨68513, true, false, [26864], [9, 5]⟩,
        ⟨68518, true, false, [26864], [9, 5]⟩,
        ⟨960, false, false, [26864, 83695], []⟩,
        ⟨85138, false, false, [26864], []⟩,
        ⟨85137, false, false, [26864], []⟩,
        ⟨85140, false, false, [26864, 31517], []⟩,
        ⟨68515, true, false, [], [31517, 94535]⟩,
        ⟨85145, true, false, [], [94535]⟩
      ]⟩,
    ⟨[31539], [31536], .source 15834⟩,
    ⟨[83697, 13], [31525, 88679], .contexts [
        ⟨85123, false, false, [], []⟩,
        ⟨85126, false, false, [], []⟩
      ]⟩,
    ⟨[31525, 88679], [31525, 88679], .contexts []⟩,
    ⟨[31541], [31525, 29327], .source 15835⟩,
    ⟨[31543], [31541, 29313], .source 15836⟩,
    ⟨[31545], [31542], .source 15837⟩,
    ⟨[31545], [31542], .contexts [
        ⟨85152, false, false, [], []⟩
      ]⟩,
    ⟨[31542], [31542], .contexts []⟩,
    ⟨[85457, 7], [31545, 83697], .contexts [
        ⟨85151, false, false, [31542], [85457, 7]⟩,
        ⟨76302, true, false, [31542, 31541], [7]⟩,
        ⟨85150, false, false, [31542], [92935, 13, 7]⟩,
        ⟨76326, true, false, [31542, 31525], [13, 7]⟩,
        ⟨85149, true, false, [31542], [7, 13, 7]⟩,
        ⟨85149, true, false, [31542], [7, 13, 7]⟩,
        ⟨85148, true, false, [31542], [7, 13, 7]⟩,
        ⟨21371, false, false, [31542, 83697], []⟩,
        ⟨43617, false, false, [31542], []⟩,
        ⟨43555, false, false, [31542], []⟩,
        ⟨85154, true, false, [], [83697]⟩,
        ⟨85154, true, false, [], [83697]⟩,
        ⟨85153, true, false, [], [83697]⟩
      ]⟩,
    ⟨[83697, 7], [31543, 85457], .contexts [
        ⟨85155, true, false, [31544], [7]⟩,
        ⟨38, false, false, [31544, 85457], []⟩,
        ⟨85152, false, true, [], [85457]⟩
      ]⟩,
    ⟨[83449, 15], [31533, 94535], .contexts [
        ⟨85139, false, false, [], []⟩,
        ⟨85142, false, false, [], []⟩
      ]⟩,
    ⟨[31533, 94535], [31533, 94535], .contexts []⟩,
    ⟨[83449, 1], [83447], .contexts [
        ⟨21229, false, false, [], []⟩,
        ⟨21322, false, false, [], []⟩,
        ⟨21228, false, false, [], []⟩,
        ⟨21228, false, false, [], []⟩
      ]⟩,
    ⟨[94533, 15], [94533, 15], .contexts []⟩,
    ⟨[83447], [83447], .contexts []⟩,
    ⟨[31532], [31532], .contexts []⟩,
    ⟨[94533, 15], [31535, 83447], .contexts [
        ⟨85160, false, false, [], []⟩,
        ⟨84817, true, false, [], [15]⟩,
        ⟨85158, true, false, [31532], [1, 15]⟩,
        ⟨85158, true, false, [31532], [1, 15]⟩,
        ⟨85157, true, false, [31532], [1, 15]⟩,
        ⟨1666, false, false, [31532, 83449], []⟩,
        ⟨9, false, false, [31532, 83449], []⟩,
        ⟨85159, false, false, [31532], []⟩,
        ⟨85161, false, false, [31532], []⟩,
        ⟨85162, true, false, [], [83447]⟩,
        ⟨85162, true, false, [], [83447]⟩,
        ⟨85143, true, false, [], [83447]⟩
      ]⟩,
    ⟨[31533], [31534], .contexts [
        ⟨85143, true, true, [], []⟩
      ]⟩,
    ⟨[31537, 94535], [31537, 94535], .contexts []⟩,
    ⟨[31537, 94531], [31537, 94531], .contexts []⟩,
    ⟨[86639], [86639], .contexts []⟩,
    ⟨[31536], [31536], .contexts []⟩,
    ⟨[94531, 1], [31539, 86639], .contexts [
        ⟨85166, true, false, [31536], [1]⟩,
        ⟨84814, true, false, [], [1]⟩,
        ⟨84817, true, false, [], [5, 1]⟩,
        ⟨85165, true, false, [31536], [1, 5, 1]⟩,
        ⟨85165, true, false, [31536], [1, 5, 1]⟩,
        ⟨85146, true, false, [31536], [1, 5, 1]⟩,
        ⟨85144, true, false, [31536], [1, 5, 1]⟩,
        ⟨874, false, false, [31536, 86639], []⟩,
        ⟨85167, false, false, [31536], []⟩,
        ⟨85168, true, false, [], [86639]⟩,
        ⟨85168, true, false, [], [86639]⟩,
        ⟨85147, true, false, [], [86639]⟩
      ]⟩,
    ⟨[31547], [26915, 31537], .source 15838⟩,
    ⟨[31549], [31546], .source 15839⟩,
    ⟨[94531], [31549, 90833], .contexts [
        ⟨85170, false, false, [31546], [94531]⟩,
        ⟨68583, false, false, [31546], [31537, 94531]⟩,
        ⟨85166, true, false, [31546, 26898], []⟩,
        ⟨85147, true, true, [31546, 26898], [94531]⟩,
        ⟨8, true, false, [31546, 26898, 31538, 94531], []⟩,
        ⟨85169, false, false, [31546, 26898, 31538], [1]⟩,
        ⟨68684, false, false, [31546, 26898], []⟩,
        ⟨68673, false, false, [31546, 26898], []⟩,
        ⟨68674, false, false, [31546, 26898], []⟩,
        ⟨68674, false, false, [31546, 26898], []⟩,
        ⟨85171, true, false, [], [90833]⟩
      ]⟩,
    ⟨[31548], [31548], .contexts []⟩,
    ⟨[31547], [31548], .contexts [
        ⟨85171, true, true, [], []⟩,
        ⟨85173, false, false, [], []⟩,
        ⟨85173, false, false, [], []⟩
      ]⟩,
    ⟨[90833, 3], [31547, 94529], .contexts [
        ⟨85172, true, false, [31548], [3]⟩,
        ⟨84810, false, false, [31548], []⟩,
        ⟨84875, false, false, [31548], []⟩,
        ⟨85174, true, false, [], [94529]⟩
      ]⟩,
    ⟨[31535, 83447], [31535, 83447], .contexts []⟩,
    ⟨[31535, 83447], [31535, 83447], .contexts []⟩,
    ⟨[31549, 90833], [31549, 90833], .contexts []⟩,
    ⟨[94531], [31549, 90833], .contexts [
        ⟨85172, false, false, [], []⟩,
        ⟨85178, false, false, [], []⟩
      ]⟩,
    ⟨[94533, 5], [31549, 90833], .contexts [
        ⟨84874, false, false, [], []⟩,
        ⟨85179, false, false, [], []⟩,
        ⟨85178, false, false, [], []⟩,
        ⟨85178, false, false, [], []⟩
      ]⟩,
    ⟨[31551], [31533, 31549], .source 15840⟩,
    ⟨[83445, 15], [31551, 90833], .contexts [
        ⟨21225, true, false, [], [15]⟩,
        ⟨85177, true, false, [31534], [5, 15]⟩,
        ⟨85177, true, false, [31534], [5, 15]⟩,
        ⟨85176, true, false, [31534], [5, 15]⟩,
        ⟨85163, true, false, [31534], [5, 15]⟩,
        ⟨85160, true, false, [31534], [5, 15]⟩,
        ⟨2072, false, false, [31534, 94533], []⟩,
        ⟨29, false, false, [31534, 94533], []⟩,
        ⟨85180, false, false, [31534], []⟩,
        ⟨68665, false, false, [31534, 31549], []⟩,
        ⟨85164, true, false, [], [31549, 90833]⟩,
        ⟨85181, true, false, [], [90833]⟩
      ]⟩,
    ⟨[31553], [31550], .source 15841⟩]

/-- Exact literal claimed equations and contextual derivations, block 1331. -/
def y322TCIndexRaw1331 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90833, 15], [31553, 83445], .contexts [
        ⟨85182, true, false, [31550], [15]⟩,
        ⟨1, false, false, [31550, 83445], []⟩,
        ⟨85183, true, false, [], [83445]⟩
      ]⟩,
    ⟨[31547, 94529], [31547, 94529], .contexts []⟩,
    ⟨[31547, 94529], [31547, 94529], .contexts []⟩,
    ⟨[90833, 3], [31547, 94529], .contexts [
        ⟨85175, false, false, [], []⟩,
        ⟨85185, false, false, [], []⟩,
        ⟨85186, false, false, [], []⟩,
        ⟨85186, false, false, [], []⟩
      ]⟩,
    ⟨[31553, 83445], [31553, 83445], .contexts []⟩,
    ⟨[31553, 83445], [31553, 83445], .contexts []⟩,
    ⟨[90833, 15], [31553, 83445], .contexts [
        ⟨85184, false, false, [], []⟩,
        ⟨85188, false, false, [], []⟩,
        ⟨85189, false, false, [], []⟩,
        ⟨85189, false, false, [], []⟩
      ]⟩,
    ⟨[94529, 15], [94529, 15], .contexts []⟩,
    ⟨[83443], [83443], .contexts []⟩,
    ⟨[31555], [31549, 31553], .source 15842⟩,
    ⟨[94529, 15], [31555, 83443], .contexts [
        ⟨85191, false, false, [], []⟩,
        ⟨85187, true, false, [31546], [15]⟩,
        ⟨151, false, false, [31546, 90833], []⟩,
        ⟨152, false, false, [31546, 90833], []⟩,
        ⟨85190, false, false, [31546], [3]⟩,
        ⟨21221, false, false, [31546, 31553], []⟩,
        ⟨85192, false, false, [31546, 31553], []⟩,
        ⟨85171, true, false, [], [31553, 83443]⟩,
        ⟨85193, true, false, [], [83443]⟩
      ]⟩,
    ⟨[31557], [31554], .source 15843⟩,
    ⟨[83443, 15], [31557, 94529], .contexts [
        ⟨85194, true, false, [31554], [15]⟩,
        ⟨1, false, false, [31554, 94529], []⟩,
        ⟨85195, true, false, [], [94529]⟩
      ]⟩,
    ⟨[31555, 83443], [31555, 83443], .contexts []⟩,
    ⟨[31555, 83443], [31555, 83443], .contexts []⟩,
    ⟨[31555, 83441], [31555, 83441], .contexts []⟩,
    ⟨[31555, 83441], [31555, 83441], .contexts []⟩,
    ⟨[31555, 83441], [31555, 83441], .contexts []⟩,
    ⟨[31555, 83439], [31555, 83439], .contexts []⟩,
    ⟨[31555, 83439], [31555, 83439], .contexts []⟩,
    ⟨[83439, 1], [83439, 1], .contexts []⟩,
    ⟨[94529], [94529], .contexts []⟩,
    ⟨[31557], [31554], .contexts [
        ⟨85195, false, false, [], []⟩
      ]⟩,
    ⟨[31554], [31554], .contexts []⟩,
    ⟨[83439, 1], [31557, 94529], .contexts [
        ⟨85204, false, false, [], []⟩,
        ⟨85203, true, false, [31554], [1]⟩,
        ⟨85202, true, false, [31554], [1]⟩,
        ⟨21213, true, false, [], [1]⟩,
        ⟨85201, true, false, [31554], [15, 1]⟩,
        ⟨85200, true, false, [31554], [15, 1]⟩,
        ⟨85199, true, false, [31554], [15, 1]⟩,
        ⟨21217, true, false, [], [15, 1]⟩,
        ⟨85198, true, false, [31554], [1, 15, 1]⟩,
        ⟨85198, true, false, [31554], [1, 15, 1]⟩,
        ⟨85197, true, false, [31554], [1, 15, 1]⟩,
        ⟨85194, true, false, [31554], [1, 15, 1]⟩,
        ⟨85191, true, false, [31554], [1, 15, 1]⟩,
        ⟨504, false, false, [31554, 94529], []⟩,
        ⟨85205, false, false, [31554], []⟩,
        ⟨85207, true, false, [], [94529]⟩,
        ⟨85207, true, false, [], [94529]⟩,
        ⟨85206, true, false, [], [94529]⟩
      ]⟩,
    ⟨[31555], [31556], .contexts [
        ⟨85195, true, true, [], []⟩
      ]⟩,
    ⟨[31555], [31555], .contexts []⟩,
    ⟨[94527], [31555, 83439], .contexts [
        ⟨84805, true, false, [], []⟩,
        ⟨84805, true, false, [], []⟩,
        ⟨84877, true, false, [], []⟩,
        ⟨84876, true, false, [], []⟩,
        ⟨85208, true, false, [31556], [1]⟩,
        ⟨8, false, false, [31556, 83439], []⟩,
        ⟨85209, true, false, [], [83439]⟩,
        ⟨85202, false, false, [], []⟩,
        ⟨85210, true, false, [], [83439]⟩,
        ⟨85203, false, false, [], []⟩
      ]⟩,
    ⟨[83441, 13], [31557, 94523], .contexts [
        ⟨85209, false, false, [31554], [83441, 13]⟩,
        ⟨85201, true, false, [31554, 31556, 31554], [13]⟩,
        ⟨85200, true, false, [31554, 31556, 31554], [13]⟩,
        ⟨85199, true, false, [31554, 31556, 31554], [13]⟩,
        ⟨21211, true, false, [31554, 31556], [13]⟩,
        ⟨85211, true, false, [31554, 31556, 31554], [15, 13]⟩,
        ⟨84803, false, false, [31554, 31556, 31554], [13]⟩,
        ⟨84878, false, false, [31554, 31556, 31554], [13]⟩,
        ⟨13, true, false, [31554, 31556, 31554], [94525, 13]⟩,
        ⟨85206, true, false, [31554, 31556], [94525, 13]⟩,
        ⟨84800, false, false, [31554], []⟩,
        ⟨84880, false, false, [31554], []⟩,
        ⟨85207, true, false, [], [94523]⟩,
        ⟨85207, true, false, [], [94523]⟩,
        ⟨85206, true, false, [], [94523]⟩
      ]⟩,
    ⟨[94559], [83619, 15], .source 47344⟩,
    ⟨[83619, 15], [94559], .contexts [
        ⟨85213, true, false, [], []⟩
      ]⟩,
    ⟨[94559, 15], [83619], .contexts [
        ⟨85214, true, false, [], [15]⟩,
        ⟨1, false, false, [83619], []⟩,
        ⟨22166, false, false, [], []⟩
      ]⟩,
    ⟨[94559], [94559], .contexts []⟩,
    ⟨[94559], [94559], .contexts []⟩,
    ⟨[83619, 15], [94559], .contexts [
        ⟨85214, false, false, [], []⟩,
        ⟨85216, false, false, [], []⟩,
        ⟨85217, false, false, [], []⟩,
        ⟨85217, false, false, [], []⟩
      ]⟩,
    ⟨[31559], [20525, 24905], .source 15844⟩,
    ⟨[94559, 5], [94559, 5], .contexts []⟩,
    ⟨[31559], [31559], .contexts [
        ⟨13, false, false, [], [31559]⟩
      ]⟩,
    ⟨[94559, 5], [31559, 90337], .contexts [
        ⟨85220, false, false, [], []⟩,
        ⟨85218, true, false, [], [5]⟩,
        ⟨27, false, false, [83619], []⟩,
        ⟨30, false, false, [83619], []⟩,
        ⟨42370, false, false, [], [15]⟩,
        ⟨42362, false, false, [], [15]⟩,
        ⟨42363, false, false, [], [15]⟩,
        ⟨42363, false, false, [], [15]⟩,
        ⟨60230, false, false, [20525], []⟩,
        ⟨85219, true, false, [], [90337]⟩,
        ⟨60226, false, false, [31559], []⟩,
        ⟨85221, true, false, [], [90337]⟩
      ]⟩,
    ⟨[31561], [31558], .source 15845⟩,
    ⟨[90337, 5], [31561, 94559], .contexts [
        ⟨85222, true, false, [31558], [5]⟩,
        ⟨28, false, false, [31558, 94559], []⟩,
        ⟨85223, true, false, [], [94559]⟩
      ]⟩,
    ⟨[20717, 83235, 15], [20717, 83237], .contexts [
        ⟨20189, false, false, [20717], []⟩
      ]⟩,
    ⟨[20717, 83237], [20717, 83237], .contexts []⟩,
    ⟨[20717, 83237], [20717, 83237], .contexts []⟩,
    ⟨[20717, 83237], [20717, 83237], .contexts []⟩,
    ⟨[94559, 11], [94559, 11], .contexts []⟩,
    ⟨[20717], [20717], .contexts []⟩,
    ⟨[20717], [20717], .contexts []⟩,
    ⟨[20717], [20717], .contexts [
        ⟨13, false, false, [], [20717]⟩,
        ⟨85230, false, false, [], []⟩,
        ⟨85231, false, false, [], []⟩
      ]⟩,
    ⟨[94559, 11], [20717, 83237], .contexts [
        ⟨85229, false, false, [], []⟩,
        ⟨85218, true, false, [], [11]⟩,
        ⟨52, false, false, [83619], []⟩,
        ⟨55, false, false, [83619], []⟩,
        ⟨43307, false, false, [], [15]⟩,
        ⟨85225, false, false, [], []⟩,
        ⟨85226, false, false, [], []⟩,
        ⟨85227, false, false, [], []⟩,
        ⟨85228, false, false, [], []⟩,
        ⟨43317, false, false, [20717], []⟩,
        ⟨85232, true, false, [], [83237]⟩
      ]⟩,
    ⟨[94561], [94559, 1], .source 47345⟩,
    ⟨[94559, 1], [94561], .contexts [
        ⟨85234, true, false, [], []⟩
      ]⟩,
    ⟨[94561, 1], [94559], .contexts [
        ⟨85235, true, false, [], [1]⟩,
        ⟨8, false, false, [94559], []⟩,
        ⟨85217, false, false, [], []⟩
      ]⟩,
    ⟨[94561], [94561], .contexts []⟩,
    ⟨[94561], [94561], .contexts []⟩,
    ⟨[94559, 1], [94561], .contexts [
        ⟨85235, false, false, [], []⟩,
        ⟨85237, false, false, [], []⟩,
        ⟨85238, false, false, [], []⟩,
        ⟨85238, false, false, [], []⟩
      ]⟩,
    ⟨[31559, 90337], [31559, 90337], .contexts []⟩,
    ⟨[31559, 90337], [31559, 90337], .contexts []⟩,
    ⟨[31559, 90335], [31559, 90335], .contexts []⟩,
    ⟨[31559, 90335], [31559, 90335], .contexts []⟩,
    ⟨[94561, 5], [94561, 5], .contexts []⟩,
    ⟨[94561, 5], [31559, 90335], .contexts [
        ⟨85244, false, false, [], []⟩,
        ⟨85239, true, false, [], [5]⟩,
        ⟨98, false, false, [94559], []⟩,
        ⟨99, false, false, [94559], []⟩,
        ⟨85220, false, false, [], [1]⟩,
        ⟨85222, false, false, [], [1]⟩,
        ⟨85240, false, false, [], [1]⟩,
        ⟨85241, false, false, [], [1]⟩,
        ⟨85241, false, false, [], [1]⟩,
        ⟨59964, false, false, [31559], []⟩,
        ⟨85242, false, false, [], []⟩,
        ⟨85243, false, false, [], []⟩,
        ⟨60258, false, false, [31559], []⟩,
        ⟨85221, true, false, [], [90335]⟩
      ]⟩,
    ⟨[90335, 5], [31561, 94561], .contexts [
        ⟨85245, true, false, [31558], [5]⟩,
        ⟨28, false, false, [31558, 94561], []⟩,
        ⟨85223, true, false, [], [94561]⟩
      ]⟩,
    ⟨[20717, 83239], [20717, 83239], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1332. -/
def y322TCIndexRaw1332 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[20717, 83239], [20717, 83239], .contexts []⟩,
    ⟨[94561, 11], [94561, 11], .contexts []⟩,
    ⟨[94561, 11], [20717, 83239], .contexts [
        ⟨85249, false, false, [], []⟩,
        ⟨85239, true, false, [], [11]⟩,
        ⟨110, false, false, [94559], []⟩,
        ⟨111, false, false, [94559], []⟩,
        ⟨85229, false, false, [], [1]⟩,
        ⟨85233, false, false, [], [1]⟩,
        ⟨85226, false, false, [], [1]⟩,
        ⟨85228, false, false, [], [1]⟩,
        ⟨85228, false, false, [], [1]⟩,
        ⟨20193, false, false, [20717], []⟩,
        ⟨85247, false, false, [], []⟩,
        ⟨85248, false, false, [], []⟩,
        ⟨43434, false, false, [20717], []⟩,
        ⟨85232, true, false, [], [83239]⟩
      ]⟩,
    ⟨[83239, 11], [20719, 94561], .contexts [
        ⟨85250, true, false, [20716], [11]⟩,
        ⟨53, false, false, [20716, 94561], []⟩,
        ⟨42559, true, false, [], [94561]⟩
      ]⟩,
    ⟨[94559, 15], [83619], .contexts [
        ⟨85215, false, false, [], []⟩
      ]⟩,
    ⟨[94561, 15], [83617], .contexts [
        ⟨85239, true, false, [], [15]⟩,
        ⟨121, false, false, [94559], []⟩,
        ⟨122, false, false, [94559], []⟩,
        ⟨85252, false, false, [], [1]⟩,
        ⟨22263, false, false, [], [1]⟩,
        ⟨22166, false, false, [], [1]⟩,
        ⟨22166, false, false, [], [1]⟩,
        ⟨22264, false, false, [], []⟩,
        ⟨22265, false, false, [], []⟩,
        ⟨22162, false, false, [], []⟩,
        ⟨22162, false, false, [], []⟩,
        ⟨42915, false, false, [], []⟩,
        ⟨672, true, false, [], [83617]⟩
      ]⟩,
    ⟨[83617, 15], [94561], .contexts [
        ⟨85253, true, false, [], [15]⟩,
        ⟨1, false, false, [94561], []⟩,
        ⟨85238, false, false, [], []⟩
      ]⟩,
    ⟨[31563], [31559, 24877], .source 15846⟩,
    ⟨[31565], [31563, 31561], .source 15847⟩,
    ⟨[94561, 13], [94561, 13], .contexts []⟩,
    ⟨[94561], [94561], .contexts []⟩,
    ⟨[31567], [31564], .source 15848⟩,
    ⟨[31564], [31564], .contexts []⟩,
    ⟨[94561, 13], [31567, 94561], .contexts [
        ⟨85257, false, false, [], []⟩,
        ⟨85256, false, false, [31564], [94561, 13]⟩,
        ⟨85246, true, false, [31564, 31563], [13]⟩,
        ⟨85255, false, false, [31564], [90335, 5, 13]⟩,
        ⟨60261, true, false, [31564, 31559], [5, 13]⟩,
        ⟨85243, true, false, [31564], [13, 5, 13]⟩,
        ⟨85243, true, false, [31564], [13, 5, 13]⟩,
        ⟨85242, true, false, [31564], [13, 5, 13]⟩,
        ⟨85245, true, false, [31564], [13, 5, 13]⟩,
        ⟨85244, true, false, [31564], [13, 5, 13]⟩,
        ⟨4632, false, false, [31564, 94561], []⟩,
        ⟨85258, false, false, [31564], []⟩,
        ⟨85260, true, false, [], [94561]⟩,
        ⟨85260, true, false, [], [94561]⟩,
        ⟨85259, true, false, [], [94561]⟩
      ]⟩,
    ⟨[94563], [94561, 3], .source 47346⟩,
    ⟨[94561, 3], [94563], .contexts [
        ⟨85262, true, false, [], []⟩
      ]⟩,
    ⟨[94563, 3], [94561], .contexts [
        ⟨85263, true, false, [], [3]⟩,
        ⟨20, false, false, [94561], []⟩,
        ⟨85238, false, false, [], []⟩
      ]⟩,
    ⟨[94561, 3], [94563], .contexts [
        ⟨85263, false, false, [], []⟩
      ]⟩,
    ⟨[94563], [94563], .contexts []⟩,
    ⟨[94563], [94563], .contexts []⟩,
    ⟨[94561, 3], [94563], .contexts [
        ⟨85265, false, false, [], []⟩,
        ⟨85266, false, false, [], []⟩,
        ⟨85267, false, false, [], []⟩,
        ⟨85267, false, false, [], []⟩
      ]⟩,
    ⟨[20717, 83241], [20717, 83241], .contexts []⟩,
    ⟨[20717, 83241], [20717, 83241], .contexts []⟩,
    ⟨[94563, 11], [94563, 11], .contexts []⟩,
    ⟨[94563, 11], [20717, 83241], .contexts [
        ⟨85271, false, false, [], []⟩,
        ⟨85268, true, false, [], [11]⟩,
        ⟨144, false, false, [94561], []⟩,
        ⟨145, false, false, [94561], []⟩,
        ⟨85249, false, false, [], [3]⟩,
        ⟨85250, false, false, [], [3]⟩,
        ⟨85247, false, false, [], [3]⟩,
        ⟨85248, false, false, [], [3]⟩,
        ⟨85248, false, false, [], [3]⟩,
        ⟨20197, false, false, [20717], []⟩,
        ⟨85269, false, false, [], []⟩,
        ⟨85270, false, false, [], []⟩,
        ⟨43512, false, false, [20717], []⟩,
        ⟨85232, true, false, [], [83241]⟩
      ]⟩,
    ⟨[83241, 11], [20719, 94563], .contexts [
        ⟨85272, true, false, [20716], [11]⟩,
        ⟨53, false, false, [20716, 94563], []⟩,
        ⟨42559, true, false, [], [94563]⟩
      ]⟩,
    ⟨[31567, 94561], [31567, 94561], .contexts []⟩,
    ⟨[31567, 94561], [31567, 94561], .contexts []⟩,
    ⟨[31567, 94563], [31567, 94563], .contexts []⟩,
    ⟨[31567, 94563], [31567, 94563], .contexts []⟩,
    ⟨[94563, 13], [94563, 13], .contexts []⟩,
    ⟨[94563], [94563], .contexts []⟩,
    ⟨[31567], [31567], .contexts [
        ⟨13, false, false, [], [31567]⟩
      ]⟩,
    ⟨[94565], [94563, 5], .source 47347⟩,
    ⟨[94563, 5], [94565], .contexts [
        ⟨85281, true, false, [], []⟩
      ]⟩,
    ⟨[94565, 5], [94563], .contexts [
        ⟨85282, true, false, [], [5]⟩,
        ⟨28, false, false, [94563], []⟩,
        ⟨85267, false, false, [], []⟩
      ]⟩,
    ⟨[94565], [94565], .contexts []⟩,
    ⟨[94565], [94565], .contexts []⟩,
    ⟨[94563, 5], [94565], .contexts [
        ⟨85282, false, false, [], []⟩,
        ⟨85284, false, false, [], []⟩,
        ⟨85285, false, false, [], []⟩,
        ⟨85285, false, false, [], []⟩
      ]⟩,
    ⟨[94563, 11], [20717, 83241], .contexts [
        ⟨85271, false, false, [], []⟩,
        ⟨85272, false, false, [], []⟩,
        ⟨85269, false, false, [], []⟩,
        ⟨85270, false, false, [], []⟩,
        ⟨85270, false, false, [], []⟩
      ]⟩,
    ⟨[20717, 83243], [20717, 83243], .contexts []⟩,
    ⟨[20717, 83243], [20717, 83243], .contexts []⟩,
    ⟨[94565, 11], [94565, 11], .contexts []⟩,
    ⟨[94565, 11], [20717, 83243], .contexts [
        ⟨85290, false, false, [], []⟩,
        ⟨85286, true, false, [], [11]⟩,
        ⟨174, false, false, [94563], []⟩,
        ⟨175, false, false, [94563], []⟩,
        ⟨85287, false, false, [], [5]⟩,
        ⟨20201, false, false, [20717], []⟩,
        ⟨85288, false, false, [], []⟩,
        ⟨85289, false, false, [], []⟩,
        ⟨60360, false, false, [20717], []⟩,
        ⟨85232, true, false, [], [83243]⟩
      ]⟩,
    ⟨[83243, 11], [20719, 94565], .contexts [
        ⟨85291, true, false, [20716], [11]⟩,
        ⟨53, false, false, [20716, 94565], []⟩,
        ⟨42559, true, false, [], [94565]⟩
      ]⟩,
    ⟨[94563, 13, 5], [31567, 94565], .contexts [
        ⟨85278, false, false, [], [5]⟩,
        ⟨85278, false, false, [], [5]⟩,
        ⟨85268, true, false, [], [13, 5]⟩,
        ⟨147, false, false, [94561], [5]⟩,
        ⟨148, false, false, [94561], [5]⟩,
        ⟨85257, false, false, [], [3, 5]⟩,
        ⟨85261, false, false, [], [3, 5]⟩,
        ⟨85274, false, false, [], [3, 5]⟩,
        ⟨85275, false, false, [], [3, 5]⟩,
        ⟨85275, false, false, [], [3, 5]⟩,
        ⟨85263, false, false, [31567], [5]⟩,
        ⟨85276, false, false, [], [5]⟩,
        ⟨85277, false, false, [], [5]⟩,
        ⟨85279, false, false, [31567], [5]⟩,
        ⟨85280, true, false, [], [94563, 5]⟩,
        ⟨85276, false, false, [], [5]⟩,
        ⟨85277, false, false, [], [5]⟩,
        ⟨85277, false, false, [], [5]⟩,
        ⟨85282, false, false, [31567], []⟩
      ]⟩,
    ⟨[94565], [94565], .contexts []⟩,
    ⟨[94567], [94565, 1], .source 47348⟩,
    ⟨[94565, 1], [94567], .contexts [
        ⟨85295, true, false, [], []⟩
      ]⟩,
    ⟨[94567, 1], [94565], .contexts [
        ⟨85296, true, false, [], [1]⟩,
        ⟨8, false, false, [94565], []⟩,
        ⟨85285, false, false, [], []⟩
      ]⟩,
    ⟨[94565, 1], [94567], .contexts [
        ⟨85296, false, false, [], []⟩
      ]⟩,
    ⟨[94567], [94567], .contexts []⟩,
    ⟨[94567], [94567], .contexts []⟩,
    ⟨[20717, 83245], [20717, 83245], .contexts []⟩,
    ⟨[20717, 83245], [20717, 83245], .contexts []⟩,
    ⟨[94567, 11], [94567, 11], .contexts []⟩,
    ⟨[83245], [83245], .contexts []⟩,
    ⟨[94567, 11], [20717, 83245], .contexts [
        ⟨85303, false, false, [], []⟩,
        ⟨85300, true, false, [], [11]⟩,
        ⟨85300, true, false, [], [11]⟩,
        ⟨85299, true, false, [], [11]⟩,
        ⟨85298, true, false, [], [11]⟩,
        ⟨110, false, false, [94565], []⟩,
        ⟨111, false, false, [94565], []⟩,
        ⟨85290, false, false, [], [1]⟩,
        ⟨85291, false, false, [], [1]⟩,
        ⟨85288, false, false, [], [1]⟩,
        ⟨85289, false, false, [], [1]⟩,
        ⟨85289, false, false, [], [1]⟩,
        ⟨20205, false, false, [20717], []⟩,
        ⟨85301, false, false, [], []⟩,
        ⟨85302, false, false, [], []⟩,
        ⟨85304, false, false, [20717], []⟩,
        ⟨85232, true, false, [], [83245]⟩
      ]⟩,
    ⟨[83245, 11], [20719, 94567], .contexts [
        ⟨85305, true, false, [20716], [11]⟩,
        ⟨53, false, false, [20716, 94567], []⟩,
        ⟨42559, true, false, [], [94567]⟩
      ]⟩,
    ⟨[94567, 11], [20717, 83245], .contexts [
        ⟨85305, false, false, [], []⟩
      ]⟩,
    ⟨[31569], [20717, 20997], .source 15849⟩,
    ⟨[31571], [31569, 20719], .source 15850⟩,
    ⟨[94567, 3], [94567, 3], .contexts []⟩,
    ⟨[31573], [31570], .source 15851⟩]

/-- Exact literal claimed equations and contextual derivations, block 1333. -/
def y322TCIndexRaw1333 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[31570], [31570], .contexts []⟩,
    ⟨[94567, 3], [31573, 94567], .contexts [
        ⟨85310, false, false, [], []⟩,
        ⟨85309, false, false, [31570], [94567, 3]⟩,
        ⟨85306, true, false, [31570, 31569], [3]⟩,
        ⟨85308, false, false, [31570], [83245, 11, 3]⟩,
        ⟨43525, true, false, [31570, 20717], [11, 3]⟩,
        ⟨85302, true, false, [31570], [3, 11, 3]⟩,
        ⟨85302, true, false, [31570], [3, 11, 3]⟩,
        ⟨85301, true, false, [31570], [3, 11, 3]⟩,
        ⟨85307, true, false, [31570], [3, 11, 3]⟩,
        ⟨85303, true, false, [31570], [3, 11, 3]⟩,
        ⟨3623, false, false, [31570, 94567], []⟩,
        ⟨85312, true, false, [], [94567]⟩,
        ⟨85312, true, false, [], [94567]⟩,
        ⟨85311, true, false, [], [94567]⟩
      ]⟩,
    ⟨[94569], [94567, 9], .source 47349⟩,
    ⟨[94567, 9], [94569], .contexts [
        ⟨85314, true, false, [], []⟩
      ]⟩,
    ⟨[94569, 9], [94567], .contexts [
        ⟨85315, true, false, [], [9]⟩,
        ⟨46, false, false, [94567], []⟩,
        ⟨85300, false, false, [], []⟩
      ]⟩,
    ⟨[94569], [94569], .contexts []⟩,
    ⟨[94569], [94569], .contexts []⟩,
    ⟨[94567, 9], [94569], .contexts [
        ⟨85315, false, false, [], []⟩,
        ⟨85317, false, false, [], []⟩,
        ⟨85318, false, false, [], []⟩,
        ⟨85318, false, false, [], []⟩
      ]⟩,
    ⟨[31573, 94567], [31573, 94567], .contexts []⟩,
    ⟨[31573, 94569], [31573, 94569], .contexts []⟩,
    ⟨[31573, 94569], [31573, 94569], .contexts []⟩,
    ⟨[94569, 3], [94569, 3], .contexts []⟩,
    ⟨[94569], [94569], .contexts []⟩,
    ⟨[31573], [31573], .contexts [
        ⟨13, false, false, [], [31573]⟩
      ]⟩,
    ⟨[94569, 3], [31573, 94569], .contexts [
        ⟨85323, false, false, [], []⟩,
        ⟨85319, true, false, [], [3]⟩,
        ⟨196, false, false, [94567], []⟩,
        ⟨197, false, false, [94567], []⟩,
        ⟨85310, false, false, [], [9]⟩,
        ⟨85313, false, false, [], [9]⟩,
        ⟨85320, false, false, [], [9]⟩,
        ⟨85320, false, false, [], [9]⟩,
        ⟨85315, false, false, [31573], []⟩,
        ⟨85321, false, false, [], []⟩,
        ⟨85322, false, false, [], []⟩,
        ⟨85324, false, false, [31573], []⟩,
        ⟨85325, true, false, [], [94569]⟩
      ]⟩,
    ⟨[94571], [94569, 11], .source 47350⟩,
    ⟨[94569, 11], [94571], .contexts [
        ⟨85327, true, false, [], []⟩
      ]⟩,
    ⟨[94571, 11], [94569], .contexts [
        ⟨85328, true, false, [], [11]⟩,
        ⟨53, false, false, [94569], []⟩,
        ⟨85318, false, false, [], []⟩
      ]⟩,
    ⟨[94571], [94571], .contexts []⟩,
    ⟨[94571], [94571], .contexts []⟩,
    ⟨[94569, 11], [94571], .contexts [
        ⟨85328, false, false, [], []⟩,
        ⟨85330, false, false, [], []⟩,
        ⟨85331, false, false, [], []⟩,
        ⟨85331, false, false, [], []⟩
      ]⟩,
    ⟨[31573, 94571], [31573, 94571], .contexts []⟩,
    ⟨[31573, 94571], [31573, 94571], .contexts []⟩,
    ⟨[94571, 3], [94571, 3], .contexts []⟩,
    ⟨[94571], [94571], .contexts []⟩,
    ⟨[94569, 9], [94567], .contexts [
        ⟨85316, false, false, [], []⟩
      ]⟩,
    ⟨[20717, 83249], [20717, 83249], .contexts []⟩,
    ⟨[20717, 83249], [20717, 83249], .contexts []⟩,
    ⟨[94571, 9], [94571, 9], .contexts []⟩,
    ⟨[94571, 9], [20717, 83249], .contexts [
        ⟨85340, false, false, [], []⟩,
        ⟨85332, true, false, [], [9]⟩,
        ⟨221, false, false, [94569], []⟩,
        ⟨224, false, false, [94569], []⟩,
        ⟨85337, false, false, [], [11, 9, 11]⟩,
        ⟨85299, false, false, [], [11, 9, 11]⟩,
        ⟨85300, false, false, [], [11, 9, 11]⟩,
        ⟨85300, false, false, [], [11, 9, 11]⟩,
        ⟨85307, false, false, [], [9, 11]⟩,
        ⟨85301, false, false, [], [9, 11]⟩,
        ⟨85302, false, false, [], [9, 11]⟩,
        ⟨85302, false, false, [], [9, 11]⟩,
        ⟨20209, false, false, [20717], [11]⟩,
        ⟨20213, false, false, [20717], []⟩,
        ⟨85338, false, false, [], []⟩,
        ⟨85339, false, false, [], []⟩,
        ⟨43643, false, false, [20717], []⟩
      ]⟩,
    ⟨[94571, 9], [20717, 83249], .contexts [
        ⟨85341, false, false, [], []⟩,
        ⟨85232, true, false, [], [83249]⟩
      ]⟩,
    ⟨[83249, 9], [20719, 94571], .contexts [
        ⟨85342, true, false, [20716], [9]⟩,
        ⟨46, false, false, [20716, 94571], []⟩,
        ⟨42559, true, false, [], [94571]⟩
      ]⟩,
    ⟨[94573], [94571, 1], .source 47351⟩,
    ⟨[94571, 1], [94573], .contexts [
        ⟨85344, true, false, [], []⟩
      ]⟩,
    ⟨[94575], [94573, 13], .source 47352⟩,
    ⟨[94573, 13], [94575], .contexts [
        ⟨85346, true, false, [], []⟩
      ]⟩,
    ⟨[94573], [94573], .contexts []⟩,
    ⟨[94575, 13], [94573], .contexts [
        ⟨85347, true, false, [], [13]⟩,
        ⟨59, false, false, [94573], []⟩,
        ⟨85348, false, false, [], []⟩
      ]⟩,
    ⟨[94577], [94575, 15], .source 47353⟩,
    ⟨[94575, 15], [94577], .contexts [
        ⟨85350, true, false, [], []⟩
      ]⟩,
    ⟨[94575], [94575], .contexts []⟩,
    ⟨[94579], [94577, 1], .source 47354⟩,
    ⟨[94577, 1], [94579], .contexts [
        ⟨85353, true, false, [], []⟩
      ]⟩,
    ⟨[94577], [94577], .contexts []⟩,
    ⟨[94581], [94579, 3], .source 47355⟩,
    ⟨[94579, 3], [94581], .contexts [
        ⟨85356, true, false, [], []⟩
      ]⟩,
    ⟨[94579], [94579], .contexts []⟩,
    ⟨[94581, 3], [94579], .contexts [
        ⟨85357, true, false, [], [3]⟩,
        ⟨20, false, false, [94579], []⟩,
        ⟨85358, false, false, [], []⟩
      ]⟩,
    ⟨[94583], [94581, 5], .source 47356⟩,
    ⟨[94581, 5], [94583], .contexts [
        ⟨85360, true, false, [], []⟩
      ]⟩,
    ⟨[94581], [94581], .contexts []⟩,
    ⟨[94583, 5], [94581], .contexts [
        ⟨85361, true, false, [], [5]⟩,
        ⟨28, false, false, [94581], []⟩,
        ⟨85362, false, false, [], []⟩
      ]⟩,
    ⟨[94585], [94583, 1], .source 47357⟩,
    ⟨[94583, 1], [94585], .contexts [
        ⟨85364, true, false, [], []⟩
      ]⟩,
    ⟨[94583], [94583], .contexts []⟩,
    ⟨[94585, 1], [94583], .contexts [
        ⟨85365, true, false, [], [1]⟩,
        ⟨8, false, false, [94583], []⟩,
        ⟨85366, false, false, [], []⟩
      ]⟩,
    ⟨[94587], [94585, 9], .source 47358⟩,
    ⟨[94585, 9], [94587], .contexts [
        ⟨85368, true, false, [], []⟩
      ]⟩,
    ⟨[94585], [94585], .contexts []⟩,
    ⟨[94587, 9], [94585], .contexts [
        ⟨85369, true, false, [], [9]⟩,
        ⟨46, false, false, [94585], []⟩,
        ⟨85370, false, false, [], []⟩
      ]⟩,
    ⟨[94589], [94587, 11], .source 47359⟩,
    ⟨[94587, 11], [94589], .contexts [
        ⟨85372, true, false, [], []⟩
      ]⟩,
    ⟨[94587], [94587], .contexts []⟩,
    ⟨[94589, 11], [94587], .contexts [
        ⟨85373, true, false, [], [11]⟩,
        ⟨53, false, false, [94587], []⟩,
        ⟨85374, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1334. -/
def y322TCIndexRaw1334 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94591], [94589, 1], .source 47360⟩,
    ⟨[94589, 1], [94591], .contexts [
        ⟨85376, true, false, [], []⟩
      ]⟩,
    ⟨[94589], [94589], .contexts []⟩,
    ⟨[94591, 1], [94589], .contexts [
        ⟨85377, true, false, [], [1]⟩,
        ⟨8, false, false, [94589], []⟩,
        ⟨85378, false, false, [], []⟩
      ]⟩,
    ⟨[94593], [94591, 13], .source 47361⟩,
    ⟨[94591], [94591], .contexts []⟩,
    ⟨[94593, 13], [94591], .contexts [
        ⟨85380, false, false, [], [13]⟩,
        ⟨59, false, false, [94591], []⟩,
        ⟨85381, false, false, [], []⟩
      ]⟩,
    ⟨[94595], [94593, 15], .source 47362⟩,
    ⟨[94593], [94593], .contexts []⟩,
    ⟨[94595, 15], [94593], .contexts [
        ⟨85383, false, false, [], [15]⟩,
        ⟨1, false, false, [94593], []⟩,
        ⟨85384, false, false, [], []⟩
      ]⟩,
    ⟨[94597], [94595, 1], .source 47363⟩,
    ⟨[94595], [94595], .contexts []⟩,
    ⟨[94597, 1], [94595], .contexts [
        ⟨85386, false, false, [], [1]⟩,
        ⟨8, false, false, [94595], []⟩,
        ⟨85387, false, false, [], []⟩
      ]⟩,
    ⟨[94599], [94597, 3], .source 47364⟩,
    ⟨[94597], [94597], .contexts []⟩,
    ⟨[94599, 3], [94597], .contexts [
        ⟨85389, false, false, [], [3]⟩,
        ⟨20, false, false, [94597], []⟩,
        ⟨85390, false, false, [], []⟩
      ]⟩,
    ⟨[94601], [94599, 5], .source 47365⟩,
    ⟨[94599], [94599], .contexts []⟩,
    ⟨[94601, 5], [94599], .contexts [
        ⟨85392, false, false, [], [5]⟩,
        ⟨28, false, false, [94599], []⟩,
        ⟨85393, false, false, [], []⟩
      ]⟩,
    ⟨[94603], [94601, 1], .source 47366⟩,
    ⟨[94601], [94601], .contexts []⟩,
    ⟨[94603, 1], [94601], .contexts [
        ⟨85395, false, false, [], [1]⟩,
        ⟨8, false, false, [94601], []⟩,
        ⟨85396, false, false, [], []⟩
      ]⟩,
    ⟨[94605], [94603, 9], .source 47367⟩,
    ⟨[94603], [94603], .contexts []⟩,
    ⟨[94605, 9], [94603], .contexts [
        ⟨85398, false, false, [], [9]⟩,
        ⟨46, false, false, [94603], []⟩,
        ⟨85399, false, false, [], []⟩
      ]⟩,
    ⟨[94607], [94605, 11], .source 47368⟩,
    ⟨[94605], [94605], .contexts []⟩,
    ⟨[94607, 11], [94605], .contexts [
        ⟨85401, false, false, [], [11]⟩,
        ⟨53, false, false, [94605], []⟩,
        ⟨85402, false, false, [], []⟩
      ]⟩,
    ⟨[94609], [94607, 1], .source 47369⟩,
    ⟨[94607], [94607], .contexts []⟩,
    ⟨[94609, 1], [94607], .contexts [
        ⟨85404, false, false, [], [1]⟩,
        ⟨8, false, false, [94607], []⟩,
        ⟨85405, false, false, [], []⟩
      ]⟩,
    ⟨[94611], [94609, 13], .source 47370⟩,
    ⟨[94609], [94609], .contexts []⟩,
    ⟨[94611, 13], [94609], .contexts [
        ⟨85407, false, false, [], [13]⟩,
        ⟨59, false, false, [94609], []⟩,
        ⟨85408, false, false, [], []⟩
      ]⟩,
    ⟨[94613], [94611, 15], .source 47371⟩,
    ⟨[94611], [94611], .contexts []⟩,
    ⟨[94613, 15], [94611], .contexts [
        ⟨85410, false, false, [], [15]⟩,
        ⟨1, false, false, [94611], []⟩,
        ⟨85411, false, false, [], []⟩
      ]⟩,
    ⟨[94615], [94613, 1], .source 47372⟩,
    ⟨[94613], [94613], .contexts []⟩,
    ⟨[94615, 1], [94613], .contexts [
        ⟨85413, false, false, [], [1]⟩,
        ⟨8, false, false, [94613], []⟩,
        ⟨85414, false, false, [], []⟩
      ]⟩,
    ⟨[94617], [94615, 3], .source 47373⟩,
    ⟨[94615], [94615], .contexts []⟩,
    ⟨[94617, 3], [94615], .contexts [
        ⟨85416, false, false, [], [3]⟩,
        ⟨20, false, false, [94615], []⟩,
        ⟨85417, false, false, [], []⟩
      ]⟩,
    ⟨[94619], [94617, 5], .source 47374⟩,
    ⟨[94617], [94617], .contexts []⟩,
    ⟨[94619, 5], [94617], .contexts [
        ⟨85419, false, false, [], [5]⟩,
        ⟨28, false, false, [94617], []⟩,
        ⟨85420, false, false, [], []⟩
      ]⟩,
    ⟨[94621], [94619, 1], .source 47375⟩,
    ⟨[94619], [94619], .contexts []⟩,
    ⟨[94621, 1], [94619], .contexts [
        ⟨85422, false, false, [], [1]⟩,
        ⟨8, false, false, [94619], []⟩,
        ⟨85423, false, false, [], []⟩
      ]⟩,
    ⟨[94623], [94621, 9], .source 47376⟩,
    ⟨[94621], [94621], .contexts []⟩,
    ⟨[94623, 9], [94621], .contexts [
        ⟨85425, false, false, [], [9]⟩,
        ⟨46, false, false, [94621], []⟩,
        ⟨85426, false, false, [], []⟩
      ]⟩,
    ⟨[94625], [94623, 11], .source 47377⟩,
    ⟨[94623], [94623], .contexts []⟩,
    ⟨[94625, 11], [94623], .contexts [
        ⟨85428, false, false, [], [11]⟩,
        ⟨53, false, false, [94623], []⟩,
        ⟨85429, false, false, [], []⟩
      ]⟩,
    ⟨[94627], [94625, 1], .source 47378⟩,
    ⟨[94625], [94625], .contexts []⟩,
    ⟨[94627, 1], [94625], .contexts [
        ⟨85431, false, false, [], [1]⟩,
        ⟨8, false, false, [94625], []⟩,
        ⟨85432, false, false, [], []⟩
      ]⟩,
    ⟨[94629], [94627, 13], .source 47379⟩,
    ⟨[94627], [94627], .contexts []⟩,
    ⟨[94629, 13], [94627], .contexts [
        ⟨85434, false, false, [], [13]⟩,
        ⟨59, false, false, [94627], []⟩,
        ⟨85435, false, false, [], []⟩
      ]⟩,
    ⟨[94631], [94629, 15], .source 47380⟩,
    ⟨[94629], [94629], .contexts []⟩,
    ⟨[94631, 15], [94629], .contexts [
        ⟨85437, false, false, [], [15]⟩,
        ⟨1, false, false, [94629], []⟩,
        ⟨85438, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1335. -/
def y322TCIndexRaw1335 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94633], [94631, 1], .source 47381⟩,
    ⟨[94631], [94631], .contexts []⟩,
    ⟨[94633, 1], [94631], .contexts [
        ⟨85440, false, false, [], [1]⟩,
        ⟨8, false, false, [94631], []⟩,
        ⟨85441, false, false, [], []⟩
      ]⟩,
    ⟨[94635], [94633, 3], .source 47382⟩,
    ⟨[94633], [94633], .contexts []⟩,
    ⟨[94635, 3], [94633], .contexts [
        ⟨85443, false, false, [], [3]⟩,
        ⟨20, false, false, [94633], []⟩,
        ⟨85444, false, false, [], []⟩
      ]⟩,
    ⟨[94637], [94635, 5], .source 47383⟩,
    ⟨[94635], [94635], .contexts []⟩,
    ⟨[94637, 5], [94635], .contexts [
        ⟨85446, false, false, [], [5]⟩,
        ⟨28, false, false, [94635], []⟩,
        ⟨85447, false, false, [], []⟩
      ]⟩,
    ⟨[94639], [94637, 1], .source 47384⟩,
    ⟨[94637], [94637], .contexts []⟩,
    ⟨[94639, 1], [94637], .contexts [
        ⟨85449, false, false, [], [1]⟩,
        ⟨8, false, false, [94637], []⟩,
        ⟨85450, false, false, [], []⟩
      ]⟩,
    ⟨[94641], [94639, 9], .source 47385⟩,
    ⟨[94639], [94639], .contexts []⟩,
    ⟨[94641, 9], [94639], .contexts [
        ⟨85452, false, false, [], [9]⟩,
        ⟨46, false, false, [94639], []⟩,
        ⟨85453, false, false, [], []⟩
      ]⟩,
    ⟨[94643], [94641, 11], .source 47386⟩,
    ⟨[94641], [94641], .contexts []⟩,
    ⟨[94643, 11], [94641], .contexts [
        ⟨85455, false, false, [], [11]⟩,
        ⟨53, false, false, [94641], []⟩,
        ⟨85456, false, false, [], []⟩
      ]⟩,
    ⟨[94645], [94643, 1], .source 47387⟩,
    ⟨[94643], [94643], .contexts []⟩,
    ⟨[94645, 1], [94643], .contexts [
        ⟨85458, false, false, [], [1]⟩,
        ⟨8, false, false, [94643], []⟩,
        ⟨85459, false, false, [], []⟩
      ]⟩,
    ⟨[94647], [94645, 13], .source 47388⟩,
    ⟨[94645], [94645], .contexts []⟩,
    ⟨[94647, 13], [94645], .contexts [
        ⟨85461, false, false, [], [13]⟩,
        ⟨59, false, false, [94645], []⟩,
        ⟨85462, false, false, [], []⟩
      ]⟩,
    ⟨[94649], [94647, 15], .source 47389⟩,
    ⟨[94647], [94647], .contexts []⟩,
    ⟨[94649, 15], [94647], .contexts [
        ⟨85464, false, false, [], [15]⟩,
        ⟨1, false, false, [94647], []⟩,
        ⟨85465, false, false, [], []⟩
      ]⟩,
    ⟨[94651], [94649, 1], .source 47390⟩,
    ⟨[94649], [94649], .contexts []⟩,
    ⟨[94651, 1], [94649], .contexts [
        ⟨85467, false, false, [], [1]⟩,
        ⟨8, false, false, [94649], []⟩,
        ⟨85468, false, false, [], []⟩
      ]⟩,
    ⟨[94653], [94651, 3], .source 47391⟩,
    ⟨[94651], [94651], .contexts []⟩,
    ⟨[94653, 3], [94651], .contexts [
        ⟨85470, false, false, [], [3]⟩,
        ⟨20, false, false, [94651], []⟩,
        ⟨85471, false, false, [], []⟩
      ]⟩,
    ⟨[94655], [94653, 5], .source 47392⟩,
    ⟨[94653], [94653], .contexts []⟩,
    ⟨[94655, 5], [94653], .contexts [
        ⟨85473, false, false, [], [5]⟩,
        ⟨28, false, false, [94653], []⟩,
        ⟨85474, false, false, [], []⟩
      ]⟩,
    ⟨[94657], [94655, 1], .source 47393⟩,
    ⟨[94655], [94655], .contexts []⟩,
    ⟨[94657, 1], [94655], .contexts [
        ⟨85476, false, false, [], [1]⟩,
        ⟨8, false, false, [94655], []⟩,
        ⟨85477, false, false, [], []⟩
      ]⟩,
    ⟨[94659], [94657, 9], .source 47394⟩,
    ⟨[94657], [94657], .contexts []⟩,
    ⟨[94659, 9], [94657], .contexts [
        ⟨85479, false, false, [], [9]⟩,
        ⟨46, false, false, [94657], []⟩,
        ⟨85480, false, false, [], []⟩
      ]⟩,
    ⟨[94661], [94659, 11], .source 47395⟩,
    ⟨[94659], [94659], .contexts []⟩,
    ⟨[94661, 11], [94659], .contexts [
        ⟨85482, false, false, [], [11]⟩,
        ⟨53, false, false, [94659], []⟩,
        ⟨85483, false, false, [], []⟩
      ]⟩,
    ⟨[94663], [94661, 1], .source 47396⟩,
    ⟨[94661], [94661], .contexts []⟩,
    ⟨[94663, 1], [94661], .contexts [
        ⟨85485, false, false, [], [1]⟩,
        ⟨8, false, false, [94661], []⟩,
        ⟨85486, false, false, [], []⟩
      ]⟩,
    ⟨[94665], [94663, 13], .source 47397⟩,
    ⟨[94663, 13], [94665], .contexts [
        ⟨85488, true, false, [], []⟩
      ]⟩,
    ⟨[94663], [94663], .contexts []⟩,
    ⟨[94665, 13], [94663], .contexts [
        ⟨85489, true, false, [], [13]⟩,
        ⟨59, false, false, [94663], []⟩,
        ⟨85490, false, false, [], []⟩
      ]⟩,
    ⟨[94665], [94665], .contexts []⟩,
    ⟨[94663, 1], [94661], .contexts [
        ⟨85487, false, false, [], []⟩
      ]⟩,
    ⟨[94663, 1], [94661], .contexts [
        ⟨85493, false, false, [], []⟩,
        ⟨85486, false, false, [], []⟩,
        ⟨85486, false, false, [], []⟩
      ]⟩,
    ⟨[94659, 9], [94657], .contexts [
        ⟨85481, false, false, [], []⟩
      ]⟩,
    ⟨[94657], [94657], .contexts []⟩,
    ⟨[94657, 1], [94655], .contexts [
        ⟨85478, false, false, [], []⟩
      ]⟩,
    ⟨[94655], [94655], .contexts []⟩,
    ⟨[94653, 3], [94651], .contexts [
        ⟨85472, false, false, [], []⟩
      ]⟩,
    ⟨[94651], [94651], .contexts []⟩,
    ⟨[94663, 1, 11, 9, 1, 5, 3], [94651], .contexts [
        ⟨85494, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨85484, false, false, [], [9, 1, 5, 3]⟩,
        ⟨85483, false, false, [], [9, 1, 5, 3]⟩,
        ⟨85483, false, false, [], [9, 1, 5, 3]⟩,
        ⟨85495, false, false, [], [1, 5, 3]⟩,
        ⟨85496, false, false, [], [1, 5, 3]⟩,
        ⟨85480, false, false, [], [1, 5, 3]⟩,
        ⟨85480, false, false, [], [1, 5, 3]⟩,
        ⟨85497, false, false, [], [5, 3]⟩,
        ⟨85498, false, false, [], [5, 3]⟩,
        ⟨85477, false, false, [], [5, 3]⟩,
        ⟨85477, false, false, [], [5, 3]⟩,
        ⟨85475, false, false, [], [3]⟩,
        ⟨85474, false, false, [], [3]⟩,
        ⟨85474, false, false, [], [3]⟩,
        ⟨85499, false, false, [], []⟩,
        ⟨85500, false, false, [], []⟩,
        ⟨85471, false, false, [], []⟩,
        ⟨85471, false, false, [], []⟩
      ]⟩,
    ⟨[94649, 15], [94647], .contexts [
        ⟨85466, false, false, [], []⟩
      ]⟩,
    ⟨[94647], [94647], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1336. -/
def y322TCIndexRaw1336 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94647, 13], [94645], .contexts [
        ⟨85463, false, false, [], []⟩
      ]⟩,
    ⟨[94645], [94645], .contexts []⟩,
    ⟨[94645, 1], [94643], .contexts [
        ⟨85460, false, false, [], []⟩
      ]⟩,
    ⟨[94643], [94643], .contexts []⟩,
    ⟨[94643, 11], [94641], .contexts [
        ⟨85457, false, false, [], []⟩
      ]⟩,
    ⟨[94641], [94641], .contexts []⟩,
    ⟨[94663, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11], [94641], .contexts [
        ⟨85501, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨85469, false, false, [], [15, 13, 1, 11]⟩,
        ⟨85468, false, false, [], [15, 13, 1, 11]⟩,
        ⟨85468, false, false, [], [15, 13, 1, 11]⟩,
        ⟨85502, false, false, [], [13, 1, 11]⟩,
        ⟨85503, false, false, [], [13, 1, 11]⟩,
        ⟨85465, false, false, [], [13, 1, 11]⟩,
        ⟨85465, false, false, [], [13, 1, 11]⟩,
        ⟨85504, false, false, [], [1, 11]⟩,
        ⟨85505, false, false, [], [1, 11]⟩,
        ⟨85462, false, false, [], [1, 11]⟩,
        ⟨85462, false, false, [], [1, 11]⟩,
        ⟨85506, false, false, [], [11]⟩,
        ⟨85507, false, false, [], [11]⟩,
        ⟨85459, false, false, [], [11]⟩,
        ⟨85459, false, false, [], [11]⟩,
        ⟨85508, false, false, [], []⟩,
        ⟨85509, false, false, [], []⟩,
        ⟨85456, false, false, [], []⟩,
        ⟨85456, false, false, [], []⟩
      ]⟩,
    ⟨[94641, 9], [94639], .contexts [
        ⟨85454, false, false, [], []⟩
      ]⟩,
    ⟨[94639], [94639], .contexts []⟩,
    ⟨[94639, 1], [94637], .contexts [
        ⟨85451, false, false, [], []⟩
      ]⟩,
    ⟨[94637], [94637], .contexts []⟩,
    ⟨[94637, 5], [94635], .contexts [
        ⟨85448, false, false, [], []⟩
      ]⟩,
    ⟨[94635], [94635], .contexts []⟩,
    ⟨[94635, 3], [94633], .contexts [
        ⟨85445, false, false, [], []⟩
      ]⟩,
    ⟨[94633], [94633], .contexts []⟩,
    ⟨[94633, 1], [94631], .contexts [
        ⟨85442, false, false, [], []⟩
      ]⟩,
    ⟨[94631], [94631], .contexts []⟩,
    ⟨[
      94663, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1
    ], [94631], .contexts [
        ⟨85510, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨85511, false, false, [], [1, 5, 3, 1]⟩,
        ⟨85512, false, false, [], [1, 5, 3, 1]⟩,
        ⟨85453, false, false, [], [1, 5, 3, 1]⟩,
        ⟨85453, false, false, [], [1, 5, 3, 1]⟩,
        ⟨85513, false, false, [], [5, 3, 1]⟩,
        ⟨85514, false, false, [], [5, 3, 1]⟩,
        ⟨85450, false, false, [], [5, 3, 1]⟩,
        ⟨85450, false, false, [], [5, 3, 1]⟩,
        ⟨85515, false, false, [], [3, 1]⟩,
        ⟨85516, false, false, [], [3, 1]⟩,
        ⟨85447, false, false, [], [3, 1]⟩,
        ⟨85447, false, false, [], [3, 1]⟩,
        ⟨85517, false, false, [], [1]⟩,
        ⟨85518, false, false, [], [1]⟩,
        ⟨85444, false, false, [], [1]⟩,
        ⟨85444, false, false, [], [1]⟩,
        ⟨85519, false, false, [], []⟩,
        ⟨85520, false, false, [], []⟩,
        ⟨85441, false, false, [], []⟩,
        ⟨85441, false, false, [], []⟩
      ]⟩,
    ⟨[94627], [94627], .contexts []⟩,
    ⟨[94625], [94625], .contexts []⟩,
    ⟨[94623], [94623], .contexts []⟩,
    ⟨[94621], [94621], .contexts []⟩,
    ⟨[
      94663, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [94621], .contexts [
        ⟨85521, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨85439, false, false, [], [13, 1, 11, 9]⟩,
        ⟨85438, false, false, [], [13, 1, 11, 9]⟩,
        ⟨85438, false, false, [], [13, 1, 11, 9]⟩,
        ⟨85436, false, false, [], [1, 11, 9]⟩,
        ⟨85522, false, false, [], [1, 11, 9]⟩,
        ⟨85435, false, false, [], [1, 11, 9]⟩,
        ⟨85435, false, false, [], [1, 11, 9]⟩,
        ⟨85433, false, false, [], [11, 9]⟩,
        ⟨85523, false, false, [], [11, 9]⟩,
        ⟨85432, false, false, [], [11, 9]⟩,
        ⟨85432, false, false, [], [11, 9]⟩,
        ⟨85430, false, false, [], [9]⟩,
        ⟨85524, false, false, [], [9]⟩,
        ⟨85429, false, false, [], [9]⟩,
        ⟨85429, false, false, [], [9]⟩,
        ⟨85427, false, false, [], []⟩,
        ⟨85525, false, false, [], []⟩,
        ⟨85426, false, false, [], []⟩,
        ⟨85426, false, false, [], []⟩
      ]⟩,
    ⟨[94619], [94619], .contexts []⟩,
    ⟨[94617], [94617], .contexts []⟩,
    ⟨[94615], [94615], .contexts []⟩,
    ⟨[94613], [94613], .contexts []⟩,
    ⟨[94611], [94611], .contexts []⟩,
    ⟨[
      94663, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15
    ], [94611], .contexts [
        ⟨85526, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨85424, false, false, [], [5, 3, 1, 15]⟩,
        ⟨85527, false, false, [], [5, 3, 1, 15]⟩,
        ⟨85423, false, false, [], [5, 3, 1, 15]⟩,
        ⟨85423, false, false, [], [5, 3, 1, 15]⟩,
        ⟨85421, false, false, [], [3, 1, 15]⟩,
        ⟨85528, false, false, [], [3, 1, 15]⟩,
        ⟨85420, false, false, [], [3, 1, 15]⟩,
        ⟨85420, false, false, [], [3, 1, 15]⟩,
        ⟨85418, false, false, [], [1, 15]⟩,
        ⟨85529, false, false, [], [1, 15]⟩,
        ⟨85417, false, false, [], [1, 15]⟩,
        ⟨85417, false, false, [], [1, 15]⟩,
        ⟨85415, false, false, [], [15]⟩,
        ⟨85530, false, false, [], [15]⟩,
        ⟨85414, false, false, [], [15]⟩,
        ⟨85414, false, false, [], [15]⟩,
        ⟨85412, false, false, [], []⟩,
        ⟨85531, false, false, [], []⟩,
        ⟨85411, false, false, [], []⟩,
        ⟨85411, false, false, [], []⟩
      ]⟩,
    ⟨[94609], [94609], .contexts []⟩,
    ⟨[94607], [94607], .contexts []⟩,
    ⟨[94605], [94605], .contexts []⟩,
    ⟨[94603], [94603], .contexts []⟩,
    ⟨[94601], [94601], .contexts []⟩,
    ⟨[
      94663, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1
    ], [94601], .contexts [
        ⟨85532, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨85409, false, false, [], [1, 11, 9, 1]⟩,
        ⟨85533, false, false, [], [1, 11, 9, 1]⟩,
        ⟨85408, false, false, [], [1, 11, 9, 1]⟩,
        ⟨85408, false, false, [], [1, 11, 9, 1]⟩,
        ⟨85406, false, false, [], [11, 9, 1]⟩,
        ⟨85534, false, false, [], [11, 9, 1]⟩,
        ⟨85405, false, false, [], [11, 9, 1]⟩,
        ⟨85405, false, false, [], [11, 9, 1]⟩,
        ⟨85403, false, false, [], [9, 1]⟩,
        ⟨85535, false, false, [], [9, 1]⟩,
        ⟨85402, false, false, [], [9, 1]⟩,
        ⟨85402, false, false, [], [9, 1]⟩,
        ⟨85400, false, false, [], [1]⟩,
        ⟨85536, false, false, [], [1]⟩,
        ⟨85399, false, false, [], [1]⟩,
        ⟨85399, false, false, [], [1]⟩,
        ⟨85397, false, false, [], []⟩,
        ⟨85537, false, false, [], []⟩,
        ⟨85396, false, false, [], []⟩,
        ⟨85396, false, false, [], []⟩
      ]⟩,
    ⟨[94599], [94599], .contexts []⟩,
    ⟨[94597], [94597], .contexts []⟩,
    ⟨[94595], [94595], .contexts []⟩,
    ⟨[94593], [94593], .contexts []⟩,
    ⟨[94591], [94591], .contexts []⟩,
    ⟨[
      94663, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13
    ], [94591], .contexts [
        ⟨85538, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨85394, false, false, [], [3, 1, 15, 13]⟩,
        ⟨85539, false, false, [], [3, 1, 15, 13]⟩,
        ⟨85393, false, false, [], [3, 1, 15, 13]⟩,
        ⟨85393, false, false, [], [3, 1, 15, 13]⟩,
        ⟨85391, false, false, [], [1, 15, 13]⟩,
        ⟨85540, false, false, [], [1, 15, 13]⟩,
        ⟨85390, false, false, [], [1, 15, 13]⟩,
        ⟨85390, false, false, [], [1, 15, 13]⟩,
        ⟨85388, false, false, [], [15, 13]⟩,
        ⟨85541, false, false, [], [15, 13]⟩,
        ⟨85387, false, false, [], [15, 13]⟩,
        ⟨85387, false, false, [], [15, 13]⟩,
        ⟨85385, false, false, [], [13]⟩,
        ⟨85542, false, false, [], [13]⟩,
        ⟨85384, false, false, [], [13]⟩,
        ⟨85384, false, false, [], [13]⟩,
        ⟨85382, false, false, [], []⟩,
        ⟨85543, false, false, [], []⟩,
        ⟨85381, false, false, [], []⟩,
        ⟨85381, false, false, [], []⟩
      ]⟩,
    ⟨[94589], [94589], .contexts []⟩,
    ⟨[94585], [94585], .contexts []⟩,
    ⟨[94581], [94581], .contexts []⟩,
    ⟨[
      94663, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5
    ], [94581], .contexts [
        ⟨85544, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨85379, false, false, [], [11, 9, 1, 5]⟩,
        ⟨85545, false, false, [], [11, 9, 1, 5]⟩,
        ⟨85378, false, false, [], [11, 9, 1, 5]⟩,
        ⟨85378, false, false, [], [11, 9, 1, 5]⟩,
        ⟨85375, false, false, [], [9, 1, 5]⟩,
        ⟨85374, false, false, [], [9, 1, 5]⟩,
        ⟨85374, false, false, [], [9, 1, 5]⟩,
        ⟨85371, false, false, [], [1, 5]⟩,
        ⟨85546, false, false, [], [1, 5]⟩,
        ⟨85370, false, false, [], [1, 5]⟩,
        ⟨85370, false, false, [], [1, 5]⟩,
        ⟨85367, false, false, [], [5]⟩,
        ⟨85366, false, false, [], [5]⟩,
        ⟨85366, false, false, [], [5]⟩,
        ⟨85363, false, false, [], []⟩,
        ⟨85547, false, false, [], []⟩,
        ⟨85362, false, false, [], []⟩,
        ⟨85362, false, false, [], []⟩
      ]⟩,
    ⟨[94577], [94577], .contexts []⟩,
    ⟨[94575], [94575], .contexts []⟩,
    ⟨[94573], [94573], .contexts []⟩,
    ⟨[
      94663, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [94571], .contexts [
        ⟨85548, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨85359, false, false, [], [1, 15, 13, 1]⟩,
        ⟨85358, false, false, [], [1, 15, 13, 1]⟩,
        ⟨85358, false, false, [], [1, 15, 13, 1]⟩,
        ⟨85354, true, false, [], [1, 15, 13, 1]⟩,
        ⟨8, false, false, [94577], [15, 13, 1]⟩,
        ⟨85355, false, false, [], [15, 13, 1]⟩,
        ⟨85549, false, false, [], [15, 13, 1]⟩,
        ⟨85355, false, false, [], [15, 13, 1]⟩,
        ⟨85355, false, false, [], [15, 13, 1]⟩,
        ⟨85351, true, false, [], [15, 13, 1]⟩,
        ⟨1, false, false, [94575], [13, 1]⟩,
        ⟨85352, false, false, [], [13, 1]⟩,
        ⟨85550, false, false, [], [13, 1]⟩,
        ⟨85352, false, false, [], [13, 1]⟩,
        ⟨85352, false, false, [], [13, 1]⟩,
        ⟨85349, false, false, [], [1]⟩,
        ⟨85551, false, false, [], [1]⟩,
        ⟨85348, false, false, [], [1]⟩,
        ⟨85348, false, false, [], [1]⟩,
        ⟨85345, true, false, [], [1]⟩,
        ⟨8, false, false, [94571], []⟩,
        ⟨85331, false, false, [], []⟩,
        ⟨85330, false, false, [], []⟩,
        ⟨85331, false, false, [], []⟩,
        ⟨85331, false, false, [], []⟩
      ]⟩,
    ⟨[94571, 11], [94569], .contexts [
        ⟨85329, false, false, [], []⟩
      ]⟩,
    ⟨[
      94663, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3
    ], [94561], .contexts [
        ⟨85552, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨85553, false, false, [], [9, 1, 5, 3]⟩,
        ⟨85317, false, false, [], [9, 1, 5, 3]⟩,
        ⟨85318, false, false, [], [9, 1, 5, 3]⟩,
        ⟨85318, false, false, [], [9, 1, 5, 3]⟩,
        ⟨85337, false, false, [], [1, 5, 3]⟩,
        ⟨85299, false, false, [], [1, 5, 3]⟩,
        ⟨85300, false, false, [], [1, 5, 3]⟩,
        ⟨85300, false, false, [], [1, 5, 3]⟩,
        ⟨85297, false, false, [], [5, 3]⟩,
        ⟨85284, false, false, [], [5, 3]⟩,
        ⟨85285, false, false, [], [5, 3]⟩,
        ⟨85285, false, false, [], [5, 3]⟩,
        ⟨85283, false, false, [], [3]⟩,
        ⟨85266, false, false, [], [3]⟩,
        ⟨85267, false, false, [], [3]⟩,
        ⟨85267, false, false, [], [3]⟩,
        ⟨85264, false, false, [], []⟩,
        ⟨85237, false, false, [], []⟩,
        ⟨85238, false, false, [], []⟩,
        ⟨85238, false, false, [], []⟩
      ]⟩,
    ⟨[
      94663, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [20717, 83231], .contexts [
        ⟨85554, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨85236, false, false, [], [15, 13, 1, 11]⟩,
        ⟨85216, false, false, [], [15, 13, 1, 11]⟩,
        ⟨85217, false, false, [], [15, 13, 1, 11]⟩,
        ⟨85217, false, false, [], [15, 13, 1, 11]⟩,
        ⟨85252, false, false, [], [13, 1, 11]⟩,
        ⟨22263, false, false, [], [13, 1, 11]⟩,
        ⟨22166, false, false, [], [13, 1, 11]⟩,
        ⟨22166, false, false, [], [13, 1, 11]⟩,
        ⟨22165, false, false, [], [1, 11]⟩,
        ⟨22262, false, false, [], [1, 11]⟩,
        ⟨22170, false, false, [], [1, 11]⟩,
        ⟨22170, false, false, [], [1, 11]⟩,
        ⟨42880, false, false, [], [11]⟩,
        ⟨42881, false, false, [], [11]⟩,
        ⟨42882, false, false, [], [11]⟩,
        ⟨42882, false, false, [], [11]⟩,
        ⟨42884, false, false, [], []⟩,
        ⟨42885, false, false, [], []⟩,
        ⟨42886, false, false, [], []⟩,
        ⟨42887, false, false, [], []⟩
      ]⟩,
    ⟨[31575], [20717, 15817], .source 15852⟩,
    ⟨[31577], [31575, 27903], .source 15853⟩,
    ⟨[31579], [31577, 17705], .source 15854⟩,
    ⟨[31581], [31579, 27905], .source 15855⟩,
    ⟨[
      94663, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1
    ], [31581, 90357], .contexts [
        ⟨85555, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨20180, false, false, [20717], [1, 5, 3, 1]⟩,
        ⟨85556, true, false, [], [83231, 1, 5, 3, 1]⟩,
        ⟨20182, false, false, [31575], [5, 3, 1]⟩,
        ⟨72058, false, false, [31575], [3, 1]⟩,
        ⟨85557, true, false, [], [92389, 3, 1]⟩,
        ⟨72053, false, false, [31577], [1]⟩,
        ⟨85558, true, false, [], [92389, 1]⟩,
        ⟨72071, false, false, [31579], []⟩,
        ⟨85559, true, false, [], [90357]⟩
      ]⟩,
    ⟨[31583], [31581, 24955], .source 15856⟩,
    ⟨[31585], [31583, 20357], .source 15857⟩,
    ⟨[31587], [31585, 20337], .source 15858⟩,
    ⟨[
      94663, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9
    ], [31587, 83105], .contexts [
        ⟨85560, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨60473, false, false, [31581], [13, 1, 11, 9]⟩,
        ⟨85561, true, false, [], [89311, 13, 1, 11, 9]⟩,
        ⟨55522, false, false, [31583], [1, 11, 9]⟩,
        ⟨85562, true, false, [], [89311, 1, 11, 9]⟩,
        ⟨55524, false, false, [31585], [11, 9]⟩,
        ⟨55535, false, false, [31585], [9]⟩,
        ⟨22187, false, false, [31585], []⟩,
        ⟨41873, false, false, [31585], []⟩,
        ⟨85563, true, false, [], [83105]⟩
      ]⟩,
    ⟨[31589], [31587, 18087], .source 15859⟩,
    ⟨[31591], [31589, 18071], .source 15860⟩,
    ⟨[31593], [31591, 3153], .source 15861⟩]

/-- Exact literal claimed equations and contextual derivations, block 1337. -/
def y322TCIndexRaw1337 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[31595], [31593, 8441], .source 15862⟩,
    ⟨[
      94663, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [31595, 81363], .contexts [
        ⟨85564, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨18585, false, false, [31587], [5, 3, 1, 15]⟩,
        ⟨31218, false, false, [31587], [3, 1, 15]⟩,
        ⟨85565, true, false, [], [85323, 3, 1, 15]⟩,
        ⟨31191, false, false, [31589], [1, 15]⟩,
        ⟨85566, true, false, [], [80791, 1, 15]⟩,
        ⟨8392, false, false, [31591], [15]⟩,
        ⟨85567, true, false, [], [80981, 15]⟩,
        ⟨11560, false, false, [31593], []⟩,
        ⟨85568, true, false, [], [81363]⟩
      ]⟩,
    ⟨[31597], [31595, 15553], .source 15863⟩,
    ⟨[31599], [31597, 15997], .source 15864⟩,
    ⟨[
      94663, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1
    ], [31599, 83181], .contexts [
        ⟨85569, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨19939, false, false, [31595], [1, 11, 9, 1]⟩,
        ⟨19919, false, false, [31595], [11, 9, 1]⟩,
        ⟨85570, true, false, [], [83201, 11, 9, 1]⟩,
        ⟨19868, false, false, [31597], [9, 1]⟩,
        ⟨19831, false, false, [31597], [1]⟩,
        ⟨85571, true, false, [], [83175, 1]⟩,
        ⟨19622, false, false, [31599], []⟩
      ]⟩,
    ⟨[31601], [31599, 16017], .source 15865⟩,
    ⟨[31603], [31601, 12501], .source 15866⟩,
    ⟨[31605], [31603, 12489], .source 15867⟩,
    ⟨[
      94663, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [31605, 81357], .contexts [
        ⟨85572, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨19615, false, false, [31599], [3, 1, 15, 13]⟩,
        ⟨19724, false, false, [31599], [1, 15, 13]⟩,
        ⟨85573, true, false, [], [83189, 1, 15, 13]⟩,
        ⟨20676, false, false, [31601], [15, 13]⟩,
        ⟨20699, false, false, [31601], [13]⟩,
        ⟨85574, true, false, [], [83345, 13]⟩,
        ⟨20691, false, false, [31603], []⟩,
        ⟨85575, true, false, [], [81357]⟩
      ]⟩,
    ⟨[31607], [31605, 14153], .source 15868⟩,
    ⟨[31609], [31607, 16351], .source 15869⟩,
    ⟨[31611], [31609, 7259], .source 15870⟩,
    ⟨[31613], [31611, 1383], .source 15871⟩,
    ⟨[
      94663, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5
    ], [31613, 85335], .contexts [
        ⟨85576, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨14340, false, false, [31605], [11, 9, 1, 5]⟩,
        ⟨85577, true, false, [], [81357, 11, 9, 1, 5]⟩,
        ⟨21602, false, false, [31607], [9, 1, 5]⟩,
        ⟨85578, true, false, [], [83497, 9, 1, 5]⟩,
        ⟨26134, false, false, [31609], [1, 5]⟩,
        ⟨85579, true, false, [], [84349, 1, 5]⟩,
        ⟨31399, false, false, [31611], [5]⟩,
        ⟨85580, true, false, [], [85329, 5]⟩,
        ⟨31481, false, false, [31613], []⟩
      ]⟩,
    ⟨[31613, 93417], [31613, 93417], .contexts []⟩,
    ⟨[31613, 93417], [31613, 93417], .contexts []⟩,
    ⟨[94665, 15], [94665, 15], .contexts []⟩,
    ⟨[94665, 15], [31613, 93417], .contexts [
        ⟨85584, false, false, [], []⟩,
        ⟨85492, true, false, [], [15]⟩,
        ⟨85492, true, false, [], [15]⟩,
        ⟨85489, true, false, [], [15]⟩,
        ⟨2277, false, false, [94663], []⟩,
        ⟨2278, false, false, [94663], []⟩,
        ⟨85581, false, false, [], [3, 1]⟩,
        ⟨79130, false, false, [31613], [1]⟩,
        ⟨79156, false, false, [31613], []⟩,
        ⟨85582, false, false, [], []⟩,
        ⟨85583, false, false, [], []⟩,
        ⟨79172, false, false, [31613], []⟩,
        ⟨13, true, false, [], [31613, 93417]⟩
      ]⟩,
    ⟨[31615], [31612], .source 15872⟩,
    ⟨[93417, 15], [31615, 94665], .contexts [
        ⟨85585, true, false, [31612], [15]⟩,
        ⟨1, false, false, [31612, 94665], []⟩,
        ⟨85586, true, false, [], [94665]⟩
      ]⟩,
    ⟨[94665, 15], [31613, 93417], .contexts [
        ⟨85584, false, false, [], []⟩,
        ⟨85585, false, false, [], []⟩,
        ⟨85582, false, false, [], []⟩,
        ⟨85583, false, false, [], []⟩,
        ⟨85583, false, false, [], []⟩
      ]⟩,
    ⟨[31617], [31613, 2909], .source 15873⟩,
    ⟨[31619], [31617, 31615], .source 15874⟩,
    ⟨[94665], [94665], .contexts []⟩,
    ⟨[94665, 5], [94665, 5], .contexts []⟩,
    ⟨[94665], [94665], .contexts []⟩,
    ⟨[31621], [31618], .source 15875⟩,
    ⟨[31618], [31618], .contexts []⟩,
    ⟨[31621], [31618], .contexts [
        ⟨85594, false, false, [], []⟩,
        ⟨85595, false, false, [], []⟩,
        ⟨85595, false, false, [], []⟩
      ]⟩,
    ⟨[94665, 5], [31621, 94665], .contexts [
        ⟨85592, false, false, [], []⟩,
        ⟨85590, false, false, [31618], [94665, 5]⟩,
        ⟨85587, true, false, [31618, 31617], [5]⟩,
        ⟨85589, false, false, [31618], [93417, 15, 5]⟩,
        ⟨79173, true, false, [31618, 31613], [15, 5]⟩,
        ⟨85588, true, false, [31618], [5, 15, 5]⟩,
        ⟨2284, false, false, [31618, 94665], []⟩,
        ⟨85591, false, false, [31618], []⟩,
        ⟨85593, false, false, [31618], []⟩,
        ⟨85596, true, false, [], [94665]⟩
      ]⟩,
    ⟨[31623], [31613, 2939], .source 15876⟩,
    ⟨[31625], [31623, 31615], .source 15877⟩,
    ⟨[31627], [31624], .source 15878⟩,
    ⟨[31624], [31624], .contexts []⟩,
    ⟨[31629], [31613, 1369], .source 15879⟩,
    ⟨[31631], [31629, 31615], .source 15880⟩,
    ⟨[94665, 11], [94665, 11], .contexts []⟩,
    ⟨[31633], [31630], .source 15881⟩,
    ⟨[31633], [31630], .contexts [
        ⟨85605, false, false, [], []⟩
      ]⟩,
    ⟨[31630], [31630], .contexts []⟩,
    ⟨[31633], [31630], .contexts [
        ⟨85606, false, false, [], []⟩,
        ⟨85607, false, false, [], []⟩,
        ⟨85607, false, false, [], []⟩
      ]⟩,
    ⟨[94665, 11], [31633, 94665], .contexts [
        ⟨85604, false, false, [], []⟩,
        ⟨85603, false, false, [31630], [94665, 11]⟩,
        ⟨85587, true, false, [31630, 31629], [11]⟩,
        ⟨85602, false, false, [31630], [93417, 15, 11]⟩,
        ⟨79181, true, false, [31630, 31613], [15, 11]⟩,
        ⟨85588, true, false, [31630], [11, 15, 11]⟩,
        ⟨2289, false, false, [31630, 94665], []⟩,
        ⟨85591, false, false, [31630], []⟩,
        ⟨85593, false, false, [31630], []⟩,
        ⟨85608, true, false, [], [94665]⟩
      ]⟩,
    ⟨[31621, 94665], [31621, 94665], .contexts []⟩,
    ⟨[31621, 94665], [31621, 94665], .contexts []⟩,
    ⟨[94665, 13], [94663], .contexts [
        ⟨85491, false, false, [], []⟩,
        ⟨85490, false, false, [], []⟩,
        ⟨85490, false, false, [], []⟩
      ]⟩,
    ⟨[94665, 12], [94665, 13], .contexts [
        ⟨64, false, false, [94665], []⟩
      ]⟩,
    ⟨[94663, 5], [94663, 5], .contexts []⟩,
    ⟨[94663], [94663], .contexts []⟩,
    ⟨[31620], [31620], .contexts []⟩,
    ⟨[31633, 94665], [31633, 94665], .contexts []⟩,
    ⟨[31633, 94665], [31633, 94665], .contexts []⟩,
    ⟨[94663, 11], [94663, 11], .contexts []⟩,
    ⟨[31631], [31632], .contexts [
        ⟨85605, true, true, [], []⟩
      ]⟩,
    ⟨[31631], [31631], .contexts []⟩,
    ⟨[31632], [31632], .contexts []⟩,
    ⟨[31619, 94663], [31619, 94663], .contexts []⟩,
    ⟨[94663, 5], [31619, 94663], .contexts [
        ⟨85614, false, false, [], []⟩,
        ⟨85614, false, false, [], []⟩,
        ⟨85491, true, false, [], [5]⟩,
        ⟨85611, true, false, [31620], [13, 5]⟩,
        ⟨85611, true, false, [31620], [13, 5]⟩,
        ⟨85610, true, false, [31620], [13, 5]⟩,
        ⟨85597, true, false, [31620], [13, 5]⟩,
        ⟨85592, true, false, [31620], [13, 5]⟩,
        ⟨913, false, false, [31620, 94665], []⟩,
        ⟨85613, false, false, [31620], []⟩,
        ⟨85612, false, false, [31620], []⟩,
        ⟨85615, false, false, [31620], []⟩,
        ⟨85616, true, false, [], [94663]⟩,
        ⟨85616, true, false, [], [94663]⟩,
        ⟨85594, false, true, [], [94663]⟩,
        ⟨85623, false, false, [], []⟩,
        ⟨85623, false, false, [], []⟩
      ]⟩,
    ⟨[31631, 94663], [31631, 94663], .contexts []⟩,
    ⟨[94663, 11], [31631, 94663], .contexts [
        ⟨85619, false, false, [], []⟩,
        ⟨85619, false, false, [], []⟩,
        ⟨85491, true, false, [], [11]⟩,
        ⟨85618, true, false, [31632], [13, 11]⟩,
        ⟨85618, true, false, [31632], [13, 11]⟩,
        ⟨85617, true, false, [31632], [13, 11]⟩,
        ⟨85609, true, false, [31632], [13, 11]⟩,
        ⟨85604, true, false, [31632], [13, 11]⟩,
        ⟨619, false, false, [31632, 94665], []⟩,
        ⟨85613, false, false, [31632], []⟩,
        ⟨85612, false, false, [31632], []⟩,
        ⟨85615, false, false, [31632], []⟩,
        ⟨85622, true, false, [], [94663]⟩,
        ⟨85622, true, false, [], [94663]⟩,
        ⟨85620, true, false, [], [94663]⟩,
        ⟨85621, true, false, [], [94663]⟩,
        ⟨85625, false, false, [], []⟩,
        ⟨85625, false, false, [], []⟩
      ]⟩,
    ⟨[31631, 94659], [31631, 94659], .contexts []⟩,
    ⟨[31631, 94659], [31631, 94659], .contexts []⟩,
    ⟨[94661], [31631, 94659], .contexts [
        ⟨85494, true, false, [], []⟩,
        ⟨85608, false, false, [31632], [94663, 1]⟩,
        ⟨85615, true, false, [31632, 31630], [1]⟩,
        ⟨628, true, false, [31632, 31630, 94663], [1]⟩,
        ⟨85626, false, false, [31632, 31630], [1, 11, 1, 1]⟩,
        ⟨85487, false, false, [31632], [11, 1, 1]⟩,
        ⟨85484, false, false, [31632], [1, 1]⟩,
        ⟨85627, false, false, [31632, 31630], [1, 1]⟩,
        ⟨85628, false, false, [31632, 31630], [1, 1]⟩,
        ⟨8, false, false, [31632, 94659], []⟩,
        ⟨85620, true, false, [], [94659]⟩
      ]⟩,
    ⟨[31631], [31631], .contexts [
        ⟨85621, false, false, [], []⟩
      ]⟩,
    ⟨[94661], [31631, 94659], .contexts [
        ⟨85629, false, false, [], []⟩,
        ⟨85627, false, false, [], []⟩,
        ⟨85630, true, false, [], [94659]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1338. -/
def y322TCIndexRaw1338 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94661], [31631, 94659], .contexts [
        ⟨85631, false, false, [], []⟩,
        ⟨85628, false, false, [], []⟩
      ]⟩,
    ⟨[31635], [31633, 31621], .source 15882⟩,
    ⟨[31637], [31635, 31631], .source 15883⟩,
    ⟨[31637, 94659], [31637, 94659], .contexts []⟩,
    ⟨[94659, 5, 9], [31637, 94659, 9], .contexts [
        ⟨85631, true, false, [31630], [5, 9]⟩,
        ⟨85487, true, false, [31630], [5, 9]⟩,
        ⟨85624, true, false, [31630, 31618], [1, 5, 9]⟩,
        ⟨890, false, false, [31630, 31618, 94663], [9]⟩,
        ⟨9, false, false, [31630, 31618, 94663], [9]⟩,
        ⟨85494, false, false, [31630, 31618], [9]⟩,
        ⟨85596, true, false, [31630], [94661, 9]⟩,
        ⟨85632, false, false, [31630, 31621], [9]⟩,
        ⟨85605, true, false, [], [31621, 31631, 94659, 9]⟩,
        ⟨85633, true, false, [], [31631, 94659, 9]⟩,
        ⟨85634, true, false, [], [94659, 9]⟩,
        ⟨85635, false, false, [], [9]⟩,
        ⟨85635, false, false, [], [9]⟩
      ]⟩,
    ⟨[94659, 9], [94657], .contexts [
        ⟨85495, false, false, [], []⟩,
        ⟨85496, false, false, [], []⟩,
        ⟨85480, false, false, [], []⟩,
        ⟨85480, false, false, [], []⟩
      ]⟩,
    ⟨[94659, 8], [94659, 9], .contexts [
        ⟨47, false, false, [94659], []⟩
      ]⟩,
    ⟨[94657, 5], [94657, 5], .contexts []⟩,
    ⟨[94657], [94657], .contexts []⟩,
    ⟨[31643], [31636], .source 15886⟩,
    ⟨[31643], [31643], .contexts []⟩,
    ⟨[31636], [31636], .contexts []⟩,
    ⟨[31643, 94657], [31643, 94657], .contexts []⟩,
    ⟨[94657, 5, 1], [31643, 94655], .contexts [
        ⟨85639, false, false, [], [1]⟩,
        ⟨85639, false, false, [], [1]⟩,
        ⟨85481, true, false, [], [5, 1]⟩,
        ⟨85636, true, false, [31636], [5, 1]⟩,
        ⟨960, false, false, [31636, 94659], [1]⟩,
        ⟨85638, false, false, [31636], [1]⟩,
        ⟨85637, false, false, [31636], [1]⟩,
        ⟨85640, false, false, [31636], [1]⟩,
        ⟨85643, true, false, [], [94657, 1]⟩,
        ⟨85643, true, false, [], [94657, 1]⟩,
        ⟨85641, true, false, [], [94657, 1]⟩,
        ⟨85642, true, false, [], [94657, 1]⟩,
        ⟨85644, false, false, [], [1]⟩,
        ⟨85644, false, false, [], [1]⟩,
        ⟨85478, false, false, [31643], []⟩
      ]⟩,
    ⟨[31643, 94653], [31643, 94653], .contexts []⟩,
    ⟨[31643, 94653], [31643, 94653], .contexts []⟩,
    ⟨[31642], [31642], .contexts []⟩,
    ⟨[94657, 1], [94655], .contexts [
        ⟨85497, false, false, [], []⟩
      ]⟩,
    ⟨[31643], [31643], .contexts [
        ⟨85642, false, false, [], []⟩
      ]⟩,
    ⟨[94655], [31643, 94653], .contexts [
        ⟨85477, true, false, [], []⟩,
        ⟨85477, true, false, [], []⟩,
        ⟨85498, true, false, [], []⟩,
        ⟨85649, true, false, [], []⟩,
        ⟨85641, true, true, [31636], [94657, 1]⟩,
        ⟨85648, false, false, [31636], [94657, 1]⟩,
        ⟨85648, false, false, [31636], [94657, 1]⟩,
        ⟨85640, true, false, [31636, 31642], [1]⟩,
        ⟨874, true, false, [31636, 31642, 94657], [1]⟩,
        ⟨85645, false, false, [31636, 31642], [5, 1, 1]⟩,
        ⟨85475, false, false, [31636], [1, 1]⟩,
        ⟨85646, false, false, [31636, 31642], [1, 1]⟩,
        ⟨85647, false, false, [31636, 31642], [1, 1]⟩,
        ⟨8, false, false, [31636, 94653], []⟩,
        ⟨85641, true, false, [], [94653]⟩,
        ⟨85646, false, false, [], []⟩,
        ⟨85650, true, false, [], [94653]⟩
      ]⟩,
    ⟨[94655], [31643, 94653], .contexts [
        ⟨85651, false, false, [], []⟩,
        ⟨85647, false, false, [], []⟩
      ]⟩,
    ⟨[94655], [31643, 94653], .contexts [
        ⟨85652, false, false, [], []⟩
      ]⟩,
    ⟨[94653], [94653], .contexts []⟩,
    ⟨[94653, 3], [94651], .contexts [
        ⟨85499, false, false, [], []⟩
      ]⟩,
    ⟨[94667], [94183, 9], .source 47398⟩,
    ⟨[94183, 9], [94667], .contexts [
        ⟨85656, true, false, [], []⟩
      ]⟩,
    ⟨[94667, 9], [94183], .contexts [
        ⟨85657, true, false, [], [9]⟩,
        ⟨46, false, false, [94183], []⟩,
        ⟨83165, false, false, [], []⟩
      ]⟩,
    ⟨[94667], [94667], .contexts []⟩,
    ⟨[94183, 9], [94667], .contexts [
        ⟨85657, false, false, [], []⟩,
        ⟨85659, false, false, [], []⟩,
        ⟨85659, false, false, [], []⟩
      ]⟩,
    ⟨[31655], [31067, 29127], .source 15892⟩,
    ⟨[31655, 87469], [31655, 87469], .contexts []⟩,
    ⟨[31655, 87469], [31655, 87469], .contexts []⟩,
    ⟨[94667, 1], [94667, 1], .contexts []⟩,
    ⟨[94667, 1], [31655, 87469], .contexts [
        ⟨85664, false, false, [], []⟩,
        ⟨85660, true, false, [], [1]⟩,
        ⟨691, false, false, [94183], []⟩,
        ⟨694, false, false, [94183], []⟩,
        ⟨83183, false, false, [], [9, 1, 9]⟩,
        ⟨75663, false, false, [31067], [1, 9]⟩,
        ⟨85661, true, false, [], [87465, 1, 9]⟩,
        ⟨43728, false, false, [31655], [9]⟩,
        ⟨43756, false, false, [31655], []⟩,
        ⟨85662, false, false, [], []⟩,
        ⟨85663, false, false, [], []⟩,
        ⟨43764, false, false, [31655], []⟩,
        ⟨13, true, false, [], [31655, 87469]⟩
      ]⟩,
    ⟨[31657], [31654], .source 15893⟩,
    ⟨[31659], [31071, 20523], .source 15894⟩,
    ⟨[94667, 7], [31659, 83623], .contexts [
        ⟨85660, true, false, [], [7]⟩,
        ⟨1084, false, false, [94183], []⟩,
        ⟨1085, false, false, [94183], []⟩,
        ⟨83194, false, false, [], [9]⟩,
        ⟨42148, false, false, [31071], []⟩,
        ⟨85667, true, false, [], [83623]⟩,
        ⟨42020, false, false, [31659], []⟩,
        ⟨13, true, false, [], [31659, 83623]⟩
      ]⟩,
    ⟨[31661], [31658], .source 15895⟩,
    ⟨[94183, 13], [31077, 94177], .contexts [
        ⟨83199, false, false, [], []⟩
      ]⟩,
    ⟨[31077, 94177], [31077, 94177], .contexts []⟩,
    ⟨[31663], [31077, 31059], .source 15896⟩,
    ⟨[94667, 13], [94667, 13], .contexts []⟩,
    ⟨[94667, 13], [31663, 94171], .contexts [
        ⟨85673, false, false, [], []⟩,
        ⟨85660, true, false, [], [13]⟩,
        ⟨201, false, false, [94183], []⟩,
        ⟨202, false, false, [94183], []⟩,
        ⟨85670, false, false, [], [9]⟩,
        ⟨85671, false, false, [], [9]⟩,
        ⟨85671, false, false, [], [9]⟩,
        ⟨82961, false, false, [31077], []⟩,
        ⟨83123, false, false, [31077], []⟩,
        ⟨85672, true, false, [], [94171]⟩,
        ⟨13, true, false, [], [31663, 94171]⟩
      ]⟩,
    ⟨[31665], [31662], .source 15897⟩,
    ⟨[31067, 93285], [31067, 93285], .contexts []⟩,
    ⟨[31067, 93285], [31067, 93285], .contexts []⟩,
    ⟨[94667, 15], [94667, 15], .contexts []⟩,
    ⟨[94667, 15], [31067, 93285], .contexts [
        ⟨85678, false, false, [], []⟩,
        ⟨85660, true, false, [], [15]⟩,
        ⟨205, false, false, [94183], []⟩,
        ⟨206, false, false, [94183], []⟩,
        ⟨83191, false, false, [], [9]⟩,
        ⟨83184, false, false, [], [9]⟩,
        ⟨83185, false, false, [], [9]⟩,
        ⟨83185, false, false, [], [9]⟩,
        ⟨78486, false, false, [31067], []⟩,
        ⟨85676, false, false, [], []⟩,
        ⟨85677, false, false, [], []⟩,
        ⟨78495, false, false, [31067], []⟩,
        ⟨83170, true, false, [], [93285]⟩
      ]⟩,
    ⟨[93285, 15], [31069, 94667], .contexts [
        ⟨85679, true, false, [31066], [15]⟩,
        ⟨1, false, false, [31066, 94667], []⟩,
        ⟨83172, true, false, [], [94667]⟩
      ]⟩,
    ⟨[31655, 87473], [31655, 87473], .contexts []⟩,
    ⟨[31655, 87473], [31655, 87473], .contexts []⟩,
    ⟨[87473, 11], [87473, 11], .contexts []⟩,
    ⟨[31654], [31654], .contexts []⟩,
    ⟨[87473, 11], [31657, 94667], .contexts [
        ⟨85683, false, false, [], []⟩,
        ⟨85682, true, false, [31654], [11]⟩,
        ⟨85681, true, false, [31654], [11]⟩,
        ⟨43795, true, false, [], [11]⟩,
        ⟨43776, true, false, [], [1, 11]⟩,
        ⟨85663, true, false, [31654], [11, 1, 11]⟩,
        ⟨85663, true, false, [31654], [11, 1, 11]⟩,
        ⟨85662, true, false, [31654], [11, 1, 11]⟩,
        ⟨85665, true, false, [31654], [11, 1, 11]⟩,
        ⟨85664, true, false, [31654], [11, 1, 11]⟩,
        ⟨994, false, false, [31654, 94667], []⟩,
        ⟨85684, true, false, [], [94667]⟩,
        ⟨85684, true, false, [], [94667]⟩,
        ⟨85666, true, false, [], [94667]⟩
      ]⟩,
    ⟨[31663, 94171], [31663, 94171], .contexts []⟩,
    ⟨[94667, 11], [31655, 87473], .contexts [
        ⟨85685, true, false, [31656], [11]⟩,
        ⟨53, false, false, [31656, 87473], []⟩,
        ⟨85666, false, true, [], [87473]⟩,
        ⟨85681, false, false, [], []⟩,
        ⟨85682, false, false, [], []⟩,
        ⟨85682, false, false, [], []⟩
      ]⟩,
    ⟨[31667], [31665, 31655], .source 15898⟩,
    ⟨[31669], [31666], .source 15899⟩,
    ⟨[87475, 11], [31669, 94171], .contexts [
        ⟨85688, false, false, [31666], [87475, 11]⟩,
        ⟨85675, false, false, [31666], [31655, 87475, 11]⟩,
        ⟨43818, true, false, [31666, 31662, 31655], [11]⟩,
        ⟨43805, true, false, [31666, 31662, 31655], [11]⟩,
        ⟨85687, true, false, [31666, 31662], [13, 11]⟩,
        ⟨83, true, false, [31666, 31662, 94667], [11]⟩,
        ⟨82, true, false, [31666, 31662, 94667], [11]⟩,
        ⟨85673, false, false, [31666, 31662], [11, 11]⟩,
        ⟨85674, false, false, [31666, 31662], [11, 11]⟩,
        ⟨85686, false, false, [31666, 31662], [11, 11]⟩,
        ⟨85686, false, false, [31666, 31662], [11, 11]⟩,
        ⟨53, false, false, [31666, 94171], []⟩,
        ⟨85689, true, false, [], [94171]⟩
      ]⟩,
    ⟨[93287, 15], [93287, 15], .contexts []⟩,
    ⟨[31671], [31069, 31655], .source 15900⟩,
    ⟨[93287, 15], [31671, 87473], .contexts [
        ⟨85691, false, false, [], []⟩,
        ⟨78508, true, false, [], [15]⟩,
        ⟨85677, true, false, [31066], [11, 15]⟩,
        ⟨85677, true, false, [31066], [11, 15]⟩,
        ⟨85676, true, false, [31066], [11, 15]⟩,
        ⟨85679, true, false, [31066], [11, 15]⟩,
        ⟨85678, true, false, [31066], [11, 15]⟩,
        ⟨2046, false, false, [31066, 94667], []⟩,
        ⟨54, false, false, [31066, 94667], []⟩,
        ⟨85687, false, false, [31066], []⟩,
        ⟨43802, false, false, [31066, 31655], []⟩,
        ⟨83188, true, false, [], [31655, 87473]⟩,
        ⟨85692, true, false, [], [87473]⟩
      ]⟩,
    ⟨[31673], [31670], .source 15901⟩,
    ⟨[31657, 94667], [31657, 94667], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1339. -/
def y322TCIndexRaw1339 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[31675], [31657, 15177], .source 15902⟩,
    ⟨[87473, 11, 9, 11, 9, 11], [31675, 92965], .contexts [
        ⟨85683, false, false, [], [9, 11, 9, 11]⟩,
        ⟨85685, false, false, [], [9, 11, 9, 11]⟩,
        ⟨85695, false, false, [], [9, 11, 9, 11]⟩,
        ⟨85695, false, false, [], [9, 11, 9, 11]⟩,
        ⟨85658, false, false, [31657], [11, 9, 11]⟩,
        ⟨83180, false, false, [31657], [9, 11]⟩,
        ⟨85696, true, false, [], [92823, 9, 11]⟩,
        ⟨76434, false, false, [31675], [11]⟩,
        ⟨76453, false, false, [31675], []⟩
      ]⟩,
    ⟨[92965, 9], [92965, 9], .contexts []⟩,
    ⟨[31677], [31674], .source 15903⟩,
    ⟨[31674], [31674], .contexts []⟩,
    ⟨[31677], [31674], .contexts [
        ⟨85699, false, false, [], []⟩,
        ⟨85700, false, false, [], []⟩,
        ⟨85700, false, false, [], []⟩
      ]⟩,
    ⟨[92965, 9], [31677, 87473], .contexts [
        ⟨85698, false, false, [], []⟩,
        ⟨85697, true, false, [31674], [9]⟩,
        ⟨2884, false, false, [31674, 87473], []⟩,
        ⟨43802, false, false, [31674], []⟩,
        ⟨85701, true, false, [], [87473]⟩
      ]⟩,
    ⟨[31675], [31676], .contexts [
        ⟨85699, true, true, [], []⟩
      ]⟩,
    ⟨[31671, 87473], [31671, 87473], .contexts []⟩,
    ⟨[31671, 87473], [31671, 87473], .contexts []⟩,
    ⟨[31671, 87471], [31671, 87471], .contexts []⟩,
    ⟨[87471, 15], [87471, 15], .contexts []⟩,
    ⟨[31670], [31670], .contexts []⟩,
    ⟨[87471, 15], [31673, 93289], .contexts [
        ⟨85707, false, false, [], []⟩,
        ⟨85706, true, false, [31670], [15]⟩,
        ⟨43796, true, false, [], [15]⟩,
        ⟨85705, true, false, [31670], [1, 15]⟩,
        ⟨85705, true, false, [31670], [1, 15]⟩,
        ⟨85704, true, false, [31670], [1, 15]⟩,
        ⟨85693, true, false, [31670], [1, 15]⟩,
        ⟨85691, true, false, [31670], [1, 15]⟩,
        ⟨1666, false, false, [31670, 93287], []⟩,
        ⟨9, false, false, [31670, 93287], []⟩,
        ⟨78530, false, false, [31670], []⟩,
        ⟨78534, false, false, [31670], []⟩,
        ⟨85708, true, false, [], [93289]⟩,
        ⟨85708, true, false, [], [93289]⟩,
        ⟨85694, true, false, [], [93289]⟩
      ]⟩,
    ⟨[31671], [31672], .contexts [
        ⟨85694, true, true, [], []⟩
      ]⟩,
    ⟨[93289, 15], [31671, 87471], .contexts [
        ⟨85709, true, false, [31672], [15]⟩,
        ⟨1, false, false, [31672, 87471], []⟩,
        ⟨85710, true, false, [], [87471]⟩
      ]⟩,
    ⟨[31677, 87473], [31677, 87473], .contexts []⟩,
    ⟨[87475, 9], [87475, 9], .contexts []⟩,
    ⟨[31675], [31676], .contexts [
        ⟨85703, false, false, [], []⟩
      ]⟩,
    ⟨[31676], [31676], .contexts []⟩,
    ⟨[87475, 9], [31675, 92967], .contexts [
        ⟨85713, false, false, [], []⟩,
        ⟨43805, true, false, [], [9]⟩,
        ⟨85712, true, false, [31676], [13, 9]⟩,
        ⟨85712, true, false, [31676], [13, 9]⟩,
        ⟨85702, true, false, [31676], [13, 9]⟩,
        ⟨85698, true, false, [31676], [13, 9]⟩,
        ⟨511, false, false, [31676, 92965], []⟩,
        ⟨64, false, false, [31676, 92965], []⟩,
        ⟨76471, false, false, [31676], []⟩,
        ⟨85715, true, false, [], [92967]⟩,
        ⟨85715, true, false, [], [92967]⟩,
        ⟨85714, true, false, [], [92967]⟩
      ]⟩,
    ⟨[31673, 93289], [31673, 93289], .contexts []⟩,
    ⟨[31673, 93289], [31673, 93289], .contexts []⟩,
    ⟨[31679], [21005, 31673], .source 15904⟩,
    ⟨[31681], [31671, 31679], .source 15905⟩,
    ⟨[93293, 13], [31681, 93289], .contexts [
        ⟨78576, true, false, [], [13]⟩,
        ⟨78557, true, false, [], [15, 13]⟩,
        ⟨85718, true, false, [31672], [13, 15, 13]⟩,
        ⟨85718, true, false, [31672], [13, 15, 13]⟩,
        ⟨85717, true, false, [31672], [13, 15, 13]⟩,
        ⟨85709, true, false, [31672], [13, 15, 13]⟩,
        ⟨85707, true, false, [31672], [13, 15, 13]⟩,
        ⟨6196, false, false, [31672, 87471], []⟩,
        ⟨260, false, false, [31672, 87471], []⟩,
        ⟨43792, false, false, [31672], [15]⟩,
        ⟨43810, false, false, [31672], [15]⟩,
        ⟨43789, false, false, [31672], [15]⟩,
        ⟨43791, false, false, [31672], [15]⟩,
        ⟨43791, false, false, [31672], [15]⟩,
        ⟨85709, false, false, [31672, 21005], []⟩,
        ⟨85719, true, false, [31672], [93289]⟩,
        ⟨78534, false, false, [31672, 31679], []⟩,
        ⟨85710, true, false, [], [31679, 93289]⟩,
        ⟨85720, true, false, [], [93289]⟩
      ]⟩,
    ⟨[31683], [31680], .source 15906⟩,
    ⟨[31683], [31683], .contexts []⟩,
    ⟨[31683], [31683], .contexts []⟩,
    ⟨[31683], [31683], .contexts []⟩,
    ⟨[31681], [31682], .contexts [
        ⟨85722, true, true, [], []⟩
      ]⟩,
    ⟨[93293], [31681, 93291], .contexts [
        ⟨85723, false, false, [31682], [93293]⟩,
        ⟨85724, false, false, [31682], [93293]⟩,
        ⟨85725, false, false, [31682], [93293]⟩,
        ⟨85722, false, false, [31682], [93293]⟩,
        ⟨59, true, false, [31682, 31680, 93293], []⟩,
        ⟨85721, false, false, [31682, 31680], [13]⟩,
        ⟨78562, false, false, [31682], []⟩,
        ⟨85726, true, false, [], [93291]⟩
      ]⟩,
    ⟨[31681, 93291], [31681, 93291], .contexts []⟩,
    ⟨[31683], [31680], .contexts [
        ⟨85722, false, false, [], []⟩
      ]⟩,
    ⟨[31680], [31680], .contexts []⟩,
    ⟨[93291, 1], [31683, 93295], .contexts [
        ⟨85727, true, false, [31680], [1]⟩,
        ⟨78591, false, false, [31680], []⟩,
        ⟨78593, false, false, [31680], []⟩,
        ⟨85730, true, false, [], [93295]⟩,
        ⟨85730, true, false, [], [93295]⟩,
        ⟨85729, true, false, [], [93295]⟩
      ]⟩,
    ⟨[31675, 92967], [31675, 92967], .contexts []⟩,
    ⟨[92969, 9], [92969, 9], .contexts []⟩,
    ⟨[92969, 9], [31677, 87477], .contexts [
        ⟨85733, false, false, [], []⟩,
        ⟨76482, true, false, [], [9]⟩,
        ⟨85732, true, false, [31674], [15, 9]⟩,
        ⟨85732, true, false, [31674], [15, 9]⟩,
        ⟨85716, true, false, [31674], [15, 9]⟩,
        ⟨85713, true, false, [31674], [15, 9]⟩,
        ⟨935, false, false, [31674, 87475], []⟩,
        ⟨10, false, false, [31674, 87475], []⟩,
        ⟨43826, false, false, [31674], []⟩,
        ⟨43829, false, false, [31674], []⟩,
        ⟨85701, true, false, [], [87477]⟩
      ]⟩,
    ⟨[93293], [31681, 93291], .contexts [
        ⟨85727, false, false, [], []⟩,
        ⟨85728, false, false, [], []⟩
      ]⟩,
    ⟨[93291, 1], [31683, 93295], .contexts [
        ⟨85731, false, false, [], []⟩
      ]⟩,
    ⟨[31683, 93295], [31683, 93295], .contexts []⟩,
    ⟨[31683, 93295], [31683, 93295], .contexts []⟩,
    ⟨[93295, 15], [93295, 15], .contexts []⟩,
    ⟨[31677, 87477], [31677, 87477], .contexts []⟩,
    ⟨[92969, 9], [31677, 87477], .contexts [
        ⟨85733, false, false, [], []⟩,
        ⟨85734, false, false, [], []⟩,
        ⟨85740, false, false, [], []⟩,
        ⟨85740, false, false, [], []⟩
      ]⟩,
    ⟨[31685], [24361, 29459], .source 15907⟩,
    ⟨[87477, 7], [87477, 7], .contexts []⟩,
    ⟨[31687], [31675, 31685], .source 15908⟩,
    ⟨[87477, 7], [31687, 89319], .contexts [
        ⟨85743, false, false, [], []⟩,
        ⟨85741, true, false, [31676], [7]⟩,
        ⟨1084, false, false, [31676, 92969], []⟩,
        ⟨1085, false, false, [31676, 92969], []⟩,
        ⟨76496, false, false, [31676], [9]⟩,
        ⟨77062, false, false, [31676, 24361], [9]⟩,
        ⟨85742, true, false, [31676], [89321, 9]⟩,
        ⟨55590, false, false, [31676, 31685], []⟩,
        ⟨55586, false, false, [31676, 31685], []⟩,
        ⟨85714, true, false, [], [31685, 89319]⟩,
        ⟨85744, true, false, [], [89319]⟩
      ]⟩,
    ⟨[31689], [31686], .source 15909⟩,
    ⟨[15171, 94191], [15171, 94191], .contexts []⟩,
    ⟨[31691], [15171, 31087], .source 15910⟩,
    ⟨[87477, 13], [87477, 13], .contexts []⟩,
    ⟨[31693], [31675, 31691], .source 15911⟩,
    ⟨[87477, 13], [31693, 93191], .contexts [
        ⟨85749, false, false, [], []⟩,
        ⟨85741, true, false, [31676], [13]⟩,
        ⟨201, false, false, [31676, 92969], []⟩,
        ⟨202, false, false, [31676, 92969], []⟩,
        ⟨83265, true, false, [31676, 15172], [13, 9]⟩,
        ⟨59, false, false, [31676, 15172, 94191], [9]⟩,
        ⟨70374, true, false, [31676], [94191, 9]⟩,
        ⟨85747, false, false, [31676], [9]⟩,
        ⟨85747, false, false, [31676], [9]⟩,
        ⟨83272, false, false, [31676, 15171], []⟩,
        ⟨85748, true, false, [31676], [93191]⟩,
        ⟨77902, false, false, [31676, 31691], []⟩,
        ⟨85714, true, false, [], [31691, 93191]⟩,
        ⟨85750, true, false, [], [93191]⟩
      ]⟩,
    ⟨[31695], [31692], .source 15912⟩,
    ⟨[93191, 13], [31695, 87477], .contexts [
        ⟨85751, true, false, [31692], [13]⟩,
        ⟨59, false, false, [31692, 87477], []⟩,
        ⟨85752, true, false, [], [87477]⟩
      ]⟩,
    ⟨[93295, 15, 3], [31683, 93297], .contexts [
        ⟨85739, false, false, [], [3]⟩,
        ⟨85739, false, false, [], [3]⟩,
        ⟨85722, true, false, [31681], [93295, 15, 3]⟩,
        ⟨85731, true, false, [31681], [15, 3]⟩,
        ⟨85728, true, false, [], [1, 15, 3]⟩,
        ⟨85728, true, false, [], [1, 15, 3]⟩,
        ⟨85735, true, false, [], [1, 15, 3]⟩,
        ⟨78577, true, false, [], [1, 15, 3]⟩,
        ⟨1666, false, false, [93291], [3]⟩,
        ⟨9, false, false, [93291], [3]⟩,
        ⟨85736, false, false, [], [3]⟩,
        ⟨85737, false, false, [], [3]⟩,
        ⟨85738, false, false, [], [3]⟩,
        ⟨85738, false, false, [], [3]⟩,
        ⟨78597, false, false, [31683], [3]⟩,
        ⟨85725, true, false, [], [93295, 3]⟩,
        ⟨85724, true, false, [], [93295, 3]⟩,
        ⟨13, true, false, [], [31683, 93295, 3]⟩,
        ⟨85737, false, false, [], [3]⟩,
        ⟨85738, false, false, [], [3]⟩,
        ⟨85738, false, false, [], [3]⟩,
        ⟨78600, false, false, [31683], []⟩
      ]⟩,
    ⟨[93297, 15], [93297, 15], .contexts []⟩,
    ⟨[31681], [31681], .contexts []⟩,
    ⟨[31681], [31682], .contexts [
        ⟨85756, false, false, [], []⟩,
        ⟨85726, false, false, [], []⟩
      ]⟩,
    ⟨[31682], [31682], .contexts []⟩,
    ⟨[31681], [31682], .contexts [
        ⟨85757, false, false, [], []⟩,
        ⟨85758, false, false, [], []⟩,
        ⟨85758, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1340. -/
def y322TCIndexRaw1340 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93297, 15], [31681, 93297], .contexts [
        ⟨85755, false, false, [], []⟩,
        ⟨85754, true, false, [31682], [15]⟩,
        ⟨1141, false, false, [31682, 93295], []⟩,
        ⟨21, false, false, [31682, 93295], []⟩,
        ⟨78604, false, false, [31682], []⟩,
        ⟨78613, false, false, [31682], []⟩,
        ⟨85759, true, false, [], [93297]⟩
      ]⟩,
    ⟨[31687, 89319], [31687, 89319], .contexts []⟩,
    ⟨[31687, 89319], [31687, 89319], .contexts []⟩,
    ⟨[31697], [31687, 30987], .source 15913⟩,
    ⟨[87477, 3], [87479], .contexts [
        ⟨43831, false, false, [], []⟩,
        ⟨44049, false, false, [], []⟩,
        ⟨43834, false, false, [], []⟩,
        ⟨43834, false, false, [], []⟩
      ]⟩,
    ⟨[87477, 2], [87477, 3], .contexts [
        ⟨21, false, false, [87477], []⟩
      ]⟩,
    ⟨[94065, 7], [94065, 7], .contexts []⟩,
    ⟨[87479], [87479], .contexts []⟩,
    ⟨[31699], [31696], .source 15914⟩,
    ⟨[31696], [31696], .contexts []⟩,
    ⟨[94065, 7], [31699, 87479], .contexts [
        ⟨85766, false, false, [], []⟩,
        ⟨85763, false, false, [31696], [94065, 7]⟩,
        ⟨82737, true, false, [31696, 31687], [7]⟩,
        ⟨85762, true, false, [31696], [3, 7]⟩,
        ⟨85762, true, false, [31696], [3, 7]⟩,
        ⟨85761, true, false, [31696], [3, 7]⟩,
        ⟨85745, true, false, [31696], [3, 7]⟩,
        ⟨85743, true, false, [31696], [3, 7]⟩,
        ⟨14911, false, false, [31696, 87477], []⟩,
        ⟨85765, false, false, [31696], []⟩,
        ⟨85764, false, false, [31696], []⟩,
        ⟨85767, false, false, [31696], []⟩,
        ⟨85769, true, false, [], [87479]⟩,
        ⟨85769, true, false, [], [87479]⟩,
        ⟨85768, true, false, [], [87479]⟩
      ]⟩,
    ⟨[31693, 93191], [31693, 93191], .contexts []⟩,
    ⟨[31693, 93191], [31693, 93191], .contexts []⟩,
    ⟨[31693, 93193], [31693, 93193], .contexts []⟩,
    ⟨[93193, 13], [93193, 13], .contexts []⟩,
    ⟨[31692], [31692], .contexts []⟩,
    ⟨[93193, 13], [31695, 87479], .contexts [
        ⟨85774, false, false, [], []⟩,
        ⟨85773, true, false, [31692], [13]⟩,
        ⟨77912, true, false, [], [13]⟩,
        ⟨85772, true, false, [31692], [3, 13]⟩,
        ⟨85772, true, false, [31692], [3, 13]⟩,
        ⟨85771, true, false, [31692], [3, 13]⟩,
        ⟨85751, true, false, [31692], [3, 13]⟩,
        ⟨85749, true, false, [31692], [3, 13]⟩,
        ⟨1132, false, false, [31692, 87477], []⟩,
        ⟨85765, false, false, [31692], []⟩,
        ⟨85764, false, false, [31692], []⟩,
        ⟨85767, false, false, [31692], []⟩,
        ⟨85775, true, false, [], [87479]⟩,
        ⟨85775, true, false, [], [87479]⟩,
        ⟨85752, true, false, [], [87479]⟩
      ]⟩,
    ⟨[31693], [31694], .contexts [
        ⟨85752, true, true, [], []⟩
      ]⟩,
    ⟨[31681, 93297], [31681, 93297], .contexts []⟩,
    ⟨[31681, 93297], [31681, 93297], .contexts []⟩,
    ⟨[93297, 4], [93297, 5], .contexts [
        ⟨29, false, false, [93297], []⟩
      ]⟩,
    ⟨[93299, 15], [93299, 15], .contexts []⟩,
    ⟨[31683], [31680], .contexts [
        ⟨85723, false, false, [], []⟩,
        ⟨85729, false, false, [], []⟩,
        ⟨85730, false, false, [], []⟩,
        ⟨85730, false, false, [], []⟩
      ]⟩,
    ⟨[93299, 15], [31683, 93299], .contexts [
        ⟨85781, false, false, [], []⟩,
        ⟨78616, true, false, [], [15]⟩,
        ⟨85779, true, false, [31680], [5, 15]⟩,
        ⟨85779, true, false, [31680], [5, 15]⟩,
        ⟨85778, true, false, [31680], [5, 15]⟩,
        ⟨85760, true, false, [31680], [5, 15]⟩,
        ⟨85755, true, false, [31680], [5, 15]⟩,
        ⟨2072, false, false, [31680, 93297], []⟩,
        ⟨85780, false, false, [31680], []⟩,
        ⟨78620, false, false, [31680], []⟩,
        ⟨78623, false, false, [31680], []⟩,
        ⟨85782, true, false, [], [93299]⟩
      ]⟩,
    ⟨[31699, 87479], [31699, 87479], .contexts []⟩,
    ⟨[31701], [17025, 31699], .source 15915⟩,
    ⟨[87481, 7], [87481, 7], .contexts []⟩,
    ⟨[31703], [31697, 31701], .source 15916⟩,
    ⟨[31695, 87479], [31695, 87479], .contexts []⟩,
    ⟨[31695, 87481], [31695, 87481], .contexts []⟩,
    ⟨[31694], [31694], .contexts []⟩,
    ⟨[31683, 93299], [31683, 93299], .contexts []⟩,
    ⟨[31683, 93299], [31683, 93299], .contexts []⟩,
    ⟨[93301, 15], [93301, 15], .contexts []⟩,
    ⟨[31703, 87481], [31703, 87481], .contexts []⟩,
    ⟨[87481, 7], [31703, 87481], .contexts [
        ⟨85786, false, false, [], []⟩,
        ⟨85786, false, false, [], []⟩,
        ⟨43833, true, false, [], [7]⟩,
        ⟨85784, true, false, [31698], [5, 7]⟩,
        ⟨85784, true, false, [31698], [5, 7]⟩,
        ⟨85770, true, false, [31698], [5, 7]⟩,
        ⟨85766, true, false, [31698], [5, 7]⟩,
        ⟨46414, false, false, [31698, 94065], []⟩,
        ⟨1045, false, false, [31698, 94065], []⟩,
        ⟨82755, false, false, [31698], [7, 5]⟩,
        ⟨85770, false, false, [31698, 17025], [5]⟩,
        ⟨85785, true, false, [31698], [87479, 5]⟩,
        ⟨43833, false, false, [31698, 31701], []⟩,
        ⟨85768, false, true, [], [31701, 87481]⟩,
        ⟨85787, true, false, [], [87481]⟩,
        ⟨85794, false, false, [], []⟩,
        ⟨85794, false, false, [], []⟩
      ]⟩,
    ⟨[87483], [87483], .contexts []⟩,
    ⟨[31705], [31702], .source 15917⟩,
    ⟨[31702], [31702], .contexts []⟩,
    ⟨[31681, 93301], [31681, 93301], .contexts []⟩,
    ⟨[93301, 15], [31681, 93301], .contexts [
        ⟨85793, false, false, [], []⟩,
        ⟨85793, false, false, [], []⟩,
        ⟨78628, true, false, [], [15]⟩,
        ⟨85792, true, false, [31682], [9, 15]⟩,
        ⟨85792, true, false, [31682], [9, 15]⟩,
        ⟨85791, true, false, [31682], [9, 15]⟩,
        ⟨85783, true, false, [31682], [9, 15]⟩,
        ⟨85781, true, false, [31682], [9, 15]⟩,
        ⟨1671, false, false, [31682, 93299], []⟩,
        ⟨47, false, false, [31682, 93299], []⟩,
        ⟨78628, false, false, [31682], []⟩,
        ⟨78630, false, false, [31682], []⟩,
        ⟨78631, false, false, [31682], []⟩,
        ⟨78631, false, false, [31682], []⟩,
        ⟨85759, true, false, [], [93301]⟩,
        ⟨85799, false, false, [], []⟩,
        ⟨85799, false, false, [], []⟩
      ]⟩,
    ⟨[93303, 15], [93303, 15], .contexts []⟩,
    ⟨[31683, 93303], [31683, 93303], .contexts []⟩,
    ⟨[93303, 15, 1], [31683, 93305], .contexts [
        ⟨85801, false, false, [], [1]⟩,
        ⟨85801, false, false, [], [1]⟩,
        ⟨78633, true, false, [], [15, 1]⟩,
        ⟨85800, true, false, [31680], [11, 15, 1]⟩,
        ⟨2046, false, false, [31680, 93301], [1]⟩,
        ⟨54, false, false, [31680, 93301], [1]⟩,
        ⟨78633, false, false, [31680], [1]⟩,
        ⟨78634, false, false, [31680], [1]⟩,
        ⟨78635, false, false, [31680], [1]⟩,
        ⟨78635, false, false, [31680], [1]⟩,
        ⟨85782, true, false, [], [93303, 1]⟩,
        ⟨85802, false, false, [], [1]⟩,
        ⟨85802, false, false, [], [1]⟩,
        ⟨78637, false, false, [31683], []⟩
      ]⟩,
    ⟨[93305, 15], [93305, 15], .contexts []⟩,
    ⟨[31681, 93305], [31681, 93305], .contexts []⟩,
    ⟨[93305, 15, 13, 15], [31681, 93309], .contexts [
        ⟨85804, false, false, [], [13, 15]⟩,
        ⟨85804, false, false, [], [13, 15]⟩,
        ⟨85803, true, false, [31682], [15, 13, 15]⟩,
        ⟨1666, false, false, [31682, 93303], [13, 15]⟩,
        ⟨9, false, false, [31682, 93303], [13, 15]⟩,
        ⟨78637, false, false, [31682], [13, 15]⟩,
        ⟨78885, false, false, [31682], [13, 15]⟩,
        ⟨78640, false, false, [31682], [13, 15]⟩,
        ⟨78640, false, false, [31682], [13, 15]⟩,
        ⟨85759, true, false, [], [93305, 13, 15]⟩,
        ⟨85805, false, false, [], [13, 15]⟩,
        ⟨85805, false, false, [], [13, 15]⟩,
        ⟨78639, false, false, [31681], [15]⟩,
        ⟨78643, false, false, [31681], []⟩
      ]⟩,
    ⟨[93309], [93309], .contexts []⟩,
    ⟨[94669], [93287, 3], .source 47399⟩,
    ⟨[93287, 3], [94669], .contexts [
        ⟨85808, true, false, [], []⟩
      ]⟩,
    ⟨[94669, 3], [93287], .contexts [
        ⟨85809, true, false, [], [3]⟩,
        ⟨20, false, false, [93287], []⟩,
        ⟨78511, false, false, [], []⟩
      ]⟩,
    ⟨[94669], [94669], .contexts []⟩,
    ⟨[94669], [94669], .contexts []⟩,
    ⟨[93287, 3], [94669], .contexts [
        ⟨85809, false, false, [], []⟩,
        ⟨85811, false, false, [], []⟩,
        ⟨85812, false, false, [], []⟩,
        ⟨85812, false, false, [], []⟩
      ]⟩,
    ⟨[29969, 94669], [29969, 94669], .contexts []⟩,
    ⟨[94669], [94669], .contexts []⟩,
    ⟨[31707], [29961, 20863], .source 15918⟩,
    ⟨[94669, 7], [31707, 86437], .contexts [
        ⟨85813, true, false, [], [7]⟩,
        ⟨140, false, false, [93287], []⟩,
        ⟨141, false, false, [93287], []⟩,
        ⟨78538, false, false, [], [3]⟩,
        ⟨42908, false, false, [29961], []⟩,
        ⟨85816, true, false, [], [86437]⟩,
        ⟨37081, false, false, [31707], []⟩,
        ⟨13, true, false, [], [31707, 86437]⟩
      ]⟩,
    ⟨[31709], [31706], .source 15919⟩,
    ⟨[9189, 94187], [9189, 94187], .contexts []⟩,
    ⟨[9189, 93813], [9189, 93813], .contexts []⟩,
    ⟨[9189, 93813], [9189, 93813], .contexts []⟩,
    ⟨[94669, 9], [94669, 9], .contexts []⟩,
    ⟨[94669, 9], [9189, 93813], .contexts [
        ⟨85822, false, false, [], []⟩,
        ⟨85813, true, false, [], [9]⟩,
        ⟨669, false, false, [93287], []⟩,
        ⟨670, false, false, [93287], []⟩,
        ⟨83244, false, false, [], [3]⟩,
        ⟨85819, false, false, [], [3]⟩,
        ⟨85819, false, false, [], [3]⟩,
        ⟨83238, false, false, [9189], []⟩,
        ⟨85820, false, false, [], []⟩,
        ⟨85821, false, false, [], []⟩,
        ⟨83237, false, false, [9189], []⟩,
        ⟨78474, true, false, [], [93813]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1341. -/
def y322TCIndexRaw1341 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[31711], [9189, 8965], .source 15920⟩,
    ⟨[31713], [31710], .source 15921⟩,
    ⟨[31710], [31710], .contexts []⟩,
    ⟨[93933, 5], [31713, 94669], .contexts [
        ⟨85824, false, false, [31710], [93933, 5]⟩,
        ⟨82134, true, false, [31710, 9189], [5]⟩,
        ⟨81483, true, false, [31710, 9189], [9, 5]⟩,
        ⟨85821, true, false, [31710], [5, 9, 5]⟩,
        ⟨85821, true, false, [31710], [5, 9, 5]⟩,
        ⟨85820, true, false, [31710], [5, 9, 5]⟩,
        ⟨85823, true, false, [31710], [5, 9, 5]⟩,
        ⟨85822, true, false, [31710], [5, 9, 5]⟩,
        ⟨497, false, false, [31710, 94669], []⟩,
        ⟨85815, false, false, [31710], []⟩,
        ⟨85826, true, false, [], [94669]⟩,
        ⟨85826, true, false, [], [94669]⟩,
        ⟨85825, true, false, [], [94669]⟩
      ]⟩,
    ⟨[94671], [92833, 13], .source 47400⟩,
    ⟨[92833, 13], [94671], .contexts [
        ⟨85828, true, false, [], []⟩
      ]⟩,
    ⟨[94671], [94671], .contexts []⟩,
    ⟨[94671], [94671], .contexts []⟩,
    ⟨[94671], [94671], .contexts []⟩,
    ⟨[16177, 92195], [16177, 92195], .contexts []⟩,
    ⟨[16177, 92195], [16177, 92195], .contexts []⟩,
    ⟨[94671, 11], [94671, 11], .contexts []⟩,
    ⟨[94671, 11], [16177, 92195], .contexts [
        ⟨85835, false, false, [], []⟩,
        ⟨85831, true, false, [], [11]⟩,
        ⟨85831, true, false, [], [11]⟩,
        ⟨85830, true, false, [], [11]⟩,
        ⟨85829, true, false, [], [11]⟩,
        ⟨82, false, false, [92833], []⟩,
        ⟨83, false, false, [92833], []⟩,
        ⟨75732, false, false, [], [13]⟩,
        ⟨75728, false, false, [], [13]⟩,
        ⟨75729, false, false, [], [13]⟩,
        ⟨75729, false, false, [], [13]⟩,
        ⟨70634, false, false, [16177], []⟩,
        ⟨85833, false, false, [], []⟩,
        ⟨85834, false, false, [], []⟩,
        ⟨70640, false, false, [16177], []⟩,
        ⟨20788, true, false, [], [92195]⟩
      ]⟩,
    ⟨[94671, 11], [16177, 92195], .contexts [
        ⟨85835, false, false, [], []⟩,
        ⟨85836, false, false, [], []⟩,
        ⟨85833, false, false, [], []⟩,
        ⟨85834, false, false, [], []⟩,
        ⟨85834, false, false, [], []⟩
      ]⟩,
    ⟨[31715], [16177, 30753], .source 15922⟩,
    ⟨[92031, 5], [92031, 5], .contexts []⟩,
    ⟨[31717], [31714], .source 15923⟩,
    ⟨[31717], [31714], .contexts [
        ⟨85840, false, false, [], []⟩
      ]⟩,
    ⟨[31714], [31714], .contexts []⟩,
    ⟨[31717], [31714], .contexts [
        ⟨85841, false, false, [], []⟩,
        ⟨85842, false, false, [], []⟩,
        ⟨85842, false, false, [], []⟩
      ]⟩,
    ⟨[31715], [31716], .contexts [
        ⟨85840, true, true, [], []⟩
      ]⟩,
    ⟨[31717, 94671], [31717, 94671], .contexts []⟩,
    ⟨[92031, 5], [31717, 94671], .contexts [
        ⟨85839, false, false, [], []⟩,
        ⟨85839, false, false, [], []⟩,
        ⟨85838, false, false, [31714], [92031, 5]⟩,
        ⟨81539, true, false, [31714, 16177], [5]⟩,
        ⟨81525, true, false, [31714, 16177], [11, 5]⟩,
        ⟨85837, true, false, [31714], [5, 11, 5]⟩,
        ⟨681, false, false, [31714, 94671], []⟩,
        ⟨85832, false, false, [31714], []⟩,
        ⟨85843, true, false, [], [94671]⟩,
        ⟨85845, false, false, [], []⟩,
        ⟨85845, false, false, [], []⟩
      ]⟩,
    ⟨[31716], [31716], .contexts []⟩,
    ⟨[94671, 1], [31715, 92027], .contexts [
        ⟨85846, true, false, [31716], [1]⟩,
        ⟨161, false, false, [31716, 92031], []⟩,
        ⟨162, false, false, [31716, 92031], []⟩,
        ⟨69001, false, false, [31716], [5]⟩,
        ⟨69002, false, false, [31716], [5]⟩,
        ⟨68967, false, false, [31716], [5]⟩,
        ⟨68967, false, false, [31716], [5]⟩,
        ⟨69003, false, false, [31716], []⟩,
        ⟨69004, false, false, [31716], []⟩,
        ⟨68963, false, false, [31716], []⟩,
        ⟨68963, false, false, [31716], []⟩,
        ⟨69182, false, false, [31716], []⟩,
        ⟨85847, true, false, [], [92027]⟩,
        ⟨85847, true, false, [], [92027]⟩,
        ⟨85844, true, false, [], [92027]⟩
      ]⟩,
    ⟨[94673], [94671, 15], .source 47401⟩,
    ⟨[94671, 15], [94673], .contexts [
        ⟨85849, true, false, [], []⟩
      ]⟩,
    ⟨[94673], [94673], .contexts []⟩,
    ⟨[94673], [94673], .contexts []⟩,
    ⟨[16177, 92197], [16177, 92197], .contexts []⟩,
    ⟨[16177, 92197], [16177, 92197], .contexts []⟩,
    ⟨[94673, 11], [94673, 11], .contexts []⟩,
    ⟨[94673, 11], [16177, 92197], .contexts [
        ⟨85855, false, false, [], []⟩,
        ⟨85852, true, false, [], [11]⟩,
        ⟨85852, true, false, [], [11]⟩,
        ⟨85851, true, false, [], [11]⟩,
        ⟨85850, true, false, [], [11]⟩,
        ⟨52, false, false, [94671], []⟩,
        ⟨55, false, false, [94671], []⟩,
        ⟨85837, false, false, [], [15]⟩,
        ⟨70645, false, false, [16177], []⟩,
        ⟨85853, false, false, [], []⟩,
        ⟨85854, false, false, [], []⟩,
        ⟨70650, false, false, [16177], []⟩,
        ⟨20788, true, false, [], [92197]⟩
      ]⟩,
    ⟨[94675], [94673, 1], .source 47402⟩,
    ⟨[94673, 1], [94675], .contexts [
        ⟨85857, true, false, [], []⟩
      ]⟩,
    ⟨[94675, 1], [94673], .contexts [
        ⟨85858, true, false, [], [1]⟩,
        ⟨8, false, false, [94673], []⟩,
        ⟨85852, false, false, [], []⟩
      ]⟩,
    ⟨[94675], [94675], .contexts []⟩,
    ⟨[94675], [94675], .contexts []⟩,
    ⟨[94673, 1], [94675], .contexts [
        ⟨85858, false, false, [], []⟩,
        ⟨85860, false, false, [], []⟩,
        ⟨85861, false, false, [], []⟩,
        ⟨85861, false, false, [], []⟩
      ]⟩,
    ⟨[16177, 92199], [16177, 92199], .contexts []⟩,
    ⟨[16177, 92199], [16177, 92199], .contexts []⟩,
    ⟨[94675, 11], [94675, 11], .contexts []⟩,
    ⟨[94675, 11], [16177, 92199], .contexts [
        ⟨85865, false, false, [], []⟩,
        ⟨85862, true, false, [], [11]⟩,
        ⟨110, false, false, [94673], []⟩,
        ⟨111, false, false, [94673], []⟩,
        ⟨85855, false, false, [], [1]⟩,
        ⟨85856, false, false, [], [1]⟩,
        ⟨85853, false, false, [], [1]⟩,
        ⟨85854, false, false, [], [1]⟩,
        ⟨85854, false, false, [], [1]⟩,
        ⟨70655, false, false, [16177], []⟩,
        ⟨85863, false, false, [], []⟩,
        ⟨85864, false, false, [], []⟩,
        ⟨70658, false, false, [16177], []⟩,
        ⟨20788, true, false, [], [92199]⟩
      ]⟩,
    ⟨[94673, 15], [94671], .contexts [
        ⟨85850, true, false, [], [15]⟩,
        ⟨1, false, false, [94671], []⟩,
        ⟨85831, false, false, [], []⟩
      ]⟩,
    ⟨[31715, 92027], [31715, 92027], .contexts []⟩,
    ⟨[31715, 92027], [31715, 92027], .contexts []⟩,
    ⟨[94675, 15], [94675, 15], .contexts []⟩,
    ⟨[31715], [31715], .contexts []⟩,
    ⟨[31715], [31715], .contexts []⟩,
    ⟨[31715], [31715], .contexts [
        ⟨13, false, false, [], [31715]⟩,
        ⟨85871, false, false, [], []⟩,
        ⟨85872, false, false, [], []⟩
      ]⟩,
    ⟨[94675, 15], [31715, 92027], .contexts [
        ⟨85870, false, false, [], []⟩,
        ⟨85862, true, false, [], [15]⟩,
        ⟨121, false, false, [94673], []⟩,
        ⟨122, false, false, [94673], []⟩,
        ⟨85867, false, false, [], [1]⟩,
        ⟨85830, false, false, [], [1]⟩,
        ⟨85831, false, false, [], [1]⟩,
        ⟨85831, false, false, [], [1]⟩,
        ⟨85848, false, false, [], []⟩,
        ⟨85868, false, false, [], []⟩,
        ⟨85869, false, false, [], []⟩,
        ⟨85869, false, false, [], []⟩,
        ⟨69182, false, false, [31715], []⟩,
        ⟨85873, true, false, [], [92027]⟩
      ]⟩,
    ⟨[94677], [94675, 3], .source 47403⟩,
    ⟨[94675, 3], [94677], .contexts [
        ⟨85875, true, false, [], []⟩
      ]⟩,
    ⟨[94677], [94677], .contexts []⟩,
    ⟨[94677], [94677], .contexts []⟩,
    ⟨[94675, 3], [94677], .contexts [
        ⟨85876, false, false, [], []⟩,
        ⟨85877, false, false, [], []⟩,
        ⟨85878, false, false, [], []⟩,
        ⟨85878, false, false, [], []⟩
      ]⟩,
    ⟨[16177, 92201], [16177, 92201], .contexts []⟩,
    ⟨[16177, 92201], [16177, 92201], .contexts []⟩,
    ⟨[94677, 11], [94677, 11], .contexts []⟩,
    ⟨[94677, 11], [16177, 92201], .contexts [
        ⟨85882, false, false, [], []⟩,
        ⟨85879, true, false, [], [11]⟩,
        ⟨144, false, false, [94675], []⟩,
        ⟨145, false, false, [94675], []⟩,
        ⟨85865, false, false, [], [3]⟩,
        ⟨85866, false, false, [], [3]⟩,
        ⟨85863, false, false, [], [3]⟩,
        ⟨85864, false, false, [], [3]⟩,
        ⟨85864, false, false, [], [3]⟩,
        ⟨70660, false, false, [16177], []⟩,
        ⟨85880, false, false, [], []⟩,
        ⟨85881, false, false, [], []⟩,
        ⟨70663, false, false, [16177], []⟩,
        ⟨20788, true, false, [], [92201]⟩
      ]⟩,
    ⟨[31715, 92025], [31715, 92025], .contexts []⟩,
    ⟨[31715, 92025], [31715, 92025], .contexts []⟩,
    ⟨[94677, 15], [94677, 15], .contexts []⟩,
    ⟨[94677, 15], [31715, 92025], .contexts [
        ⟨85886, false, false, [], []⟩,
        ⟨85879, true, false, [], [15]⟩,
        ⟨151, false, false, [94675], []⟩,
        ⟨152, false, false, [94675], []⟩,
        ⟨85870, false, false, [], [3]⟩,
        ⟨85874, false, false, [], [3]⟩,
        ⟨85868, false, false, [], [3]⟩,
        ⟨85869, false, false, [], [3]⟩,
        ⟨85869, false, false, [], [3]⟩,
        ⟨68960, false, false, [31715], []⟩,
        ⟨85884, false, false, [], []⟩,
        ⟨85885, false, false, [], []⟩,
        ⟨69183, false, false, [31715], []⟩,
        ⟨85873, true, false, [], [92025]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1342. -/
def y322TCIndexRaw1342 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[92025, 15], [31717, 94677], .contexts [
        ⟨85887, true, false, [31714], [15]⟩,
        ⟨1, false, false, [31714, 94677], []⟩,
        ⟨85840, true, false, [], [94677]⟩
      ]⟩,
    ⟨[31715, 92021], [31715, 92021], .contexts []⟩,
    ⟨[31715, 92021], [31715, 92021], .contexts []⟩,
    ⟨[92021, 1], [92021, 1], .contexts []⟩,
    ⟨[92021, 1], [31717, 94677], .contexts [
        ⟨85891, false, false, [], []⟩,
        ⟨85890, true, false, [31714], [1]⟩,
        ⟨85889, true, false, [31714], [1]⟩,
        ⟨68953, true, false, [], [1]⟩,
        ⟨68957, true, false, [], [15, 1]⟩,
        ⟨85885, true, false, [31714], [1, 15, 1]⟩,
        ⟨85885, true, false, [31714], [1, 15, 1]⟩,
        ⟨85884, true, false, [31714], [1, 15, 1]⟩,
        ⟨85887, true, false, [31714], [1, 15, 1]⟩,
        ⟨85886, true, false, [31714], [1, 15, 1]⟩,
        ⟨504, false, false, [31714, 94677], []⟩,
        ⟨85843, true, false, [], [94677]⟩
      ]⟩,
    ⟨[31717, 94677], [31717, 94677], .contexts []⟩,
    ⟨[31719], [31717, 16177], .source 15924⟩,
    ⟨[31721], [31719, 30109], .source 15925⟩,
    ⟨[92021], [92021], .contexts []⟩,
    ⟨[31723], [31720], .source 15926⟩,
    ⟨[31720], [31720], .contexts []⟩,
    ⟨[93429, 11], [31723, 92021], .contexts [
        ⟨85895, false, false, [31720], [93429, 11]⟩,
        ⟨79224, false, false, [31720, 31719], [93429, 11]⟩,
        ⟨8, true, false, [31720, 31719, 30106, 93429], [11]⟩,
        ⟨79271, false, false, [31720, 31719, 30106], [1, 11]⟩,
        ⟨85894, false, false, [31720], [92201, 1, 11]⟩,
        ⟨85883, true, false, [31720, 31717], [1, 11]⟩,
        ⟨85893, true, false, [31720], [11, 1, 11]⟩,
        ⟨85893, true, false, [31720], [11, 1, 11]⟩,
        ⟨85892, true, false, [31720], [11, 1, 11]⟩,
        ⟨85891, true, false, [31720], [11, 1, 11]⟩,
        ⟨994, false, false, [31720, 92021], []⟩,
        ⟨85896, false, false, [31720], []⟩,
        ⟨69185, false, false, [31720], []⟩,
        ⟨85898, true, false, [], [92021]⟩,
        ⟨85898, true, false, [], [92021]⟩,
        ⟨85897, true, false, [], [92021]⟩
      ]⟩,
    ⟨[94679], [94677, 5], .source 47404⟩,
    ⟨[94677, 5], [94679], .contexts [
        ⟨85900, true, false, [], []⟩
      ]⟩,
    ⟨[94679], [94679], .contexts []⟩,
    ⟨[94679], [94679], .contexts []⟩,
    ⟨[16177, 92203], [16177, 92203], .contexts []⟩,
    ⟨[16177, 92203], [16177, 92203], .contexts []⟩,
    ⟨[94679, 11], [94679, 11], .contexts []⟩,
    ⟨[94681], [94679, 1], .source 47405⟩,
    ⟨[94679, 1], [94681], .contexts [
        ⟨85907, true, false, [], []⟩
      ]⟩,
    ⟨[94681], [94681], .contexts []⟩,
    ⟨[94681], [94681], .contexts []⟩,
    ⟨[94679, 1], [94681], .contexts [
        ⟨85908, false, false, [], []⟩,
        ⟨85909, false, false, [], []⟩,
        ⟨85910, false, false, [], []⟩,
        ⟨85910, false, false, [], []⟩
      ]⟩,
    ⟨[94679, 5], [94677], .contexts [
        ⟨85901, true, false, [], [5]⟩,
        ⟨28, false, false, [94677], []⟩,
        ⟨85878, false, false, [], []⟩
      ]⟩,
    ⟨[94677, 1], [31715, 92021], .contexts [
        ⟨85892, true, false, [31716], [1]⟩,
        ⟨8, false, false, [31716, 92021], []⟩,
        ⟨85844, true, false, [], [92021]⟩
      ]⟩,
    ⟨[92021, 5], [31717, 94681], .contexts [
        ⟨85873, false, false, [31714], [92021, 5]⟩,
        ⟨69185, true, false, [], [5]⟩,
        ⟨85890, true, false, [31714], [5]⟩,
        ⟨85890, true, false, [31714], [5]⟩,
        ⟨85889, true, false, [31714], [5]⟩,
        ⟨85913, true, false, [31714], [5]⟩,
        ⟨85878, true, false, [31714], [1, 5]⟩,
        ⟨85878, true, false, [31714], [1, 5]⟩,
        ⟨85877, true, false, [31714], [1, 5]⟩,
        ⟨85912, true, false, [31714], [1, 5]⟩,
        ⟨99, true, false, [31714, 94679], [5]⟩,
        ⟨98, true, false, [31714, 94679], [5]⟩,
        ⟨85911, false, false, [31714], [5, 5]⟩,
        ⟨28, false, false, [31714, 94681], []⟩,
        ⟨85840, true, false, [], [94681]⟩
      ]⟩,
    ⟨[16177, 92205], [16177, 92205], .contexts []⟩,
    ⟨[94679, 11, 1], [16177, 92205], .contexts [
        ⟨85906, false, false, [], [1]⟩,
        ⟨85906, false, false, [], [1]⟩,
        ⟨85903, true, false, [], [11, 1]⟩,
        ⟨85903, true, false, [], [11, 1]⟩,
        ⟨85902, true, false, [], [11, 1]⟩,
        ⟨85901, true, false, [], [11, 1]⟩,
        ⟨174, false, false, [94677], [1]⟩,
        ⟨175, false, false, [94677], [1]⟩,
        ⟨85882, false, false, [], [5, 1]⟩,
        ⟨85883, false, false, [], [5, 1]⟩,
        ⟨85880, false, false, [], [5, 1]⟩,
        ⟨85881, false, false, [], [5, 1]⟩,
        ⟨85881, false, false, [], [5, 1]⟩,
        ⟨70665, false, false, [16177], [1]⟩,
        ⟨85904, false, false, [], [1]⟩,
        ⟨85905, false, false, [], [1]⟩,
        ⟨81589, false, false, [16177], [1]⟩,
        ⟨20788, true, false, [], [92203, 1]⟩,
        ⟨85904, false, false, [], [1]⟩,
        ⟨85905, false, false, [], [1]⟩,
        ⟨85905, false, false, [], [1]⟩,
        ⟨70667, false, false, [16177], []⟩,
        ⟨85915, false, false, [], []⟩
      ]⟩,
    ⟨[16177, 92205], [16177, 92205], .contexts []⟩,
    ⟨[94681, 11], [16177, 92205], .contexts [
        ⟨85911, true, false, [], [11]⟩,
        ⟨110, false, false, [94679], []⟩,
        ⟨111, false, false, [94679], []⟩,
        ⟨85916, false, false, [], []⟩,
        ⟨85917, false, false, [], []⟩,
        ⟨20788, true, false, [], [92205]⟩
      ]⟩,
    ⟨[94683], [94681, 9], .source 47406⟩,
    ⟨[94681, 9], [94683], .contexts [
        ⟨85919, true, false, [], []⟩
      ]⟩,
    ⟨[94683], [94683], .contexts []⟩,
    ⟨[94685], [94683, 11], .source 47407⟩,
    ⟨[94683, 11], [94685], .contexts [
        ⟨85922, true, false, [], []⟩
      ]⟩,
    ⟨[94685], [94685], .contexts []⟩,
    ⟨[94685], [94685], .contexts []⟩,
    ⟨[94683, 9], [94681], .contexts [
        ⟨85920, true, false, [], [9]⟩,
        ⟨46, false, false, [94681], []⟩,
        ⟨85910, false, false, [], []⟩
      ]⟩,
    ⟨[16177, 92209], [16177, 92209], .contexts []⟩,
    ⟨[94685, 9], [16177, 92209], .contexts [
        ⟨85925, true, false, [], [9]⟩,
        ⟨85925, true, false, [], [9]⟩,
        ⟨85924, true, false, [], [9]⟩,
        ⟨85923, true, false, [], [9]⟩,
        ⟨221, false, false, [94683], []⟩,
        ⟨224, false, false, [94683], []⟩,
        ⟨85926, false, false, [], [11, 9, 11]⟩,
        ⟨85909, false, false, [], [11, 9, 11]⟩,
        ⟨85910, false, false, [], [11, 9, 11]⟩,
        ⟨85910, false, false, [], [11, 9, 11]⟩,
        ⟨85918, false, false, [], [9, 11]⟩,
        ⟨85915, false, false, [], [9, 11]⟩,
        ⟨85917, false, false, [], [9, 11]⟩,
        ⟨85917, false, false, [], [9, 11]⟩,
        ⟨70670, false, false, [16177], [11]⟩,
        ⟨70673, false, false, [16177], []⟩,
        ⟨85927, false, false, [], []⟩
      ]⟩,
    ⟨[94687], [94685, 1], .source 47408⟩,
    ⟨[94689], [94687, 13], .source 47409⟩,
    ⟨[94687], [94687], .contexts []⟩,
    ⟨[94691], [94689, 15], .source 47410⟩,
    ⟨[94689], [94689], .contexts []⟩,
    ⟨[94693], [94691, 1], .source 47411⟩,
    ⟨[94691], [94691], .contexts []⟩,
    ⟨[94695], [94693, 3], .source 47412⟩,
    ⟨[94693], [94693], .contexts []⟩,
    ⟨[94697], [94695, 5], .source 47413⟩,
    ⟨[94695], [94695], .contexts []⟩,
    ⟨[94699], [94697, 1], .source 47414⟩,
    ⟨[94697], [94697], .contexts []⟩,
    ⟨[94701], [94699, 9], .source 47415⟩,
    ⟨[94699], [94699], .contexts []⟩,
    ⟨[94703], [94701, 11], .source 47416⟩,
    ⟨[94701], [94701], .contexts []⟩,
    ⟨[94705], [94703, 1], .source 47417⟩,
    ⟨[94703], [94703], .contexts []⟩,
    ⟨[94707], [94705, 13], .source 47418⟩,
    ⟨[94705], [94705], .contexts []⟩,
    ⟨[94709], [94707, 15], .source 47419⟩,
    ⟨[94707], [94707], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1343. -/
def y322TCIndexRaw1343 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94711], [94709, 1], .source 47420⟩,
    ⟨[94709], [94709], .contexts []⟩,
    ⟨[94713], [94711, 3], .source 47421⟩,
    ⟨[94711], [94711], .contexts []⟩,
    ⟨[94715], [94713, 5], .source 47422⟩,
    ⟨[94713], [94713], .contexts []⟩,
    ⟨[94717], [94715, 1], .source 47423⟩,
    ⟨[94715], [94715], .contexts []⟩,
    ⟨[94719], [94717, 9], .source 47424⟩,
    ⟨[94717], [94717], .contexts []⟩,
    ⟨[94721], [94719, 11], .source 47425⟩,
    ⟨[94719], [94719], .contexts []⟩,
    ⟨[94723], [94721, 1], .source 47426⟩,
    ⟨[94721], [94721], .contexts []⟩,
    ⟨[94723, 1], [94721], .contexts [
        ⟨85964, false, false, [], [1]⟩,
        ⟨8, false, false, [94721], []⟩,
        ⟨85965, false, false, [], []⟩
      ]⟩,
    ⟨[94725], [94723, 13], .source 47427⟩,
    ⟨[94723, 13], [94725], .contexts [
        ⟨85967, true, false, [], []⟩
      ]⟩,
    ⟨[94723], [94723], .contexts []⟩,
    ⟨[94725, 13], [94723], .contexts [
        ⟨85968, true, false, [], [13]⟩,
        ⟨59, false, false, [94723], []⟩,
        ⟨85969, false, false, [], []⟩
      ]⟩,
    ⟨[94727], [94725, 15], .source 47428⟩,
    ⟨[94725], [94725], .contexts []⟩,
    ⟨[94727, 15], [94725], .contexts [
        ⟨85971, false, false, [], [15]⟩,
        ⟨1, false, false, [94725], []⟩,
        ⟨85972, false, false, [], []⟩
      ]⟩,
    ⟨[94729], [94727, 1], .source 47429⟩,
    ⟨[94727], [94727], .contexts []⟩,
    ⟨[94729, 1], [94727], .contexts [
        ⟨85974, false, false, [], [1]⟩,
        ⟨8, false, false, [94727], []⟩,
        ⟨85975, false, false, [], []⟩
      ]⟩,
    ⟨[94731], [94729, 3], .source 47430⟩,
    ⟨[94729], [94729], .contexts []⟩,
    ⟨[94733], [94731, 5], .source 47431⟩,
    ⟨[94731], [94731], .contexts []⟩,
    ⟨[94733, 5], [94731], .contexts [
        ⟨85979, false, false, [], [5]⟩,
        ⟨28, false, false, [94731], []⟩,
        ⟨85980, false, false, [], []⟩
      ]⟩,
    ⟨[94735], [94733, 1], .source 47432⟩,
    ⟨[94733], [94733], .contexts []⟩,
    ⟨[94735, 1], [94733], .contexts [
        ⟨85982, false, false, [], [1]⟩,
        ⟨8, false, false, [94733], []⟩,
        ⟨85983, false, false, [], []⟩
      ]⟩,
    ⟨[94737], [94735, 9], .source 47433⟩,
    ⟨[94735], [94735], .contexts []⟩,
    ⟨[94737, 9], [94735], .contexts [
        ⟨85985, false, false, [], [9]⟩,
        ⟨46, false, false, [94735], []⟩,
        ⟨85986, false, false, [], []⟩
      ]⟩,
    ⟨[94739], [94737, 11], .source 47434⟩,
    ⟨[94737], [94737], .contexts []⟩,
    ⟨[94739, 11], [94737], .contexts [
        ⟨85988, false, false, [], [11]⟩,
        ⟨53, false, false, [94737], []⟩,
        ⟨85989, false, false, [], []⟩
      ]⟩,
    ⟨[94741], [94739, 1], .source 47435⟩,
    ⟨[94739], [94739], .contexts []⟩,
    ⟨[94741, 1], [94739], .contexts [
        ⟨85991, false, false, [], [1]⟩,
        ⟨8, false, false, [94739], []⟩,
        ⟨85992, false, false, [], []⟩
      ]⟩,
    ⟨[94743], [94741, 13], .source 47436⟩,
    ⟨[94741, 13], [94743], .contexts [
        ⟨85994, true, false, [], []⟩
      ]⟩,
    ⟨[94741], [94741], .contexts []⟩,
    ⟨[94743, 13], [94741], .contexts [
        ⟨85995, true, false, [], [13]⟩,
        ⟨59, false, false, [94741], []⟩,
        ⟨85996, false, false, [], []⟩
      ]⟩,
    ⟨[94745], [94743, 15], .source 47437⟩,
    ⟨[94743, 15], [94745], .contexts [
        ⟨85998, true, false, [], []⟩
      ]⟩,
    ⟨[94743], [94743], .contexts []⟩,
    ⟨[94745, 15], [94743], .contexts [
        ⟨85999, true, false, [], [15]⟩,
        ⟨1, false, false, [94743], []⟩,
        ⟨86000, false, false, [], []⟩
      ]⟩,
    ⟨[94747], [94745, 1], .source 47438⟩,
    ⟨[94745], [94745], .contexts []⟩,
    ⟨[94747, 1], [94745], .contexts [
        ⟨86002, false, false, [], [1]⟩,
        ⟨8, false, false, [94745], []⟩,
        ⟨86003, false, false, [], []⟩
      ]⟩,
    ⟨[94749], [94747, 3], .source 47439⟩,
    ⟨[94747, 3], [94749], .contexts [
        ⟨86005, true, false, [], []⟩
      ]⟩,
    ⟨[94747], [94747], .contexts []⟩,
    ⟨[94749, 3], [94747], .contexts [
        ⟨86006, true, false, [], [3]⟩,
        ⟨20, false, false, [94747], []⟩,
        ⟨86007, false, false, [], []⟩
      ]⟩,
    ⟨[94751], [94749, 5], .source 47440⟩,
    ⟨[94749], [94749], .contexts []⟩,
    ⟨[94751, 5], [94749], .contexts [
        ⟨86009, false, false, [], [5]⟩,
        ⟨28, false, false, [94749], []⟩,
        ⟨86010, false, false, [], []⟩
      ]⟩,
    ⟨[94753], [94751, 1], .source 47441⟩,
    ⟨[94751], [94751], .contexts []⟩,
    ⟨[94753, 1], [94751], .contexts [
        ⟨86012, false, false, [], [1]⟩,
        ⟨8, false, false, [94751], []⟩,
        ⟨86013, false, false, [], []⟩
      ]⟩,
    ⟨[94755], [94753, 9], .source 47442⟩]

/-- Literal contextual derivation data in chronological chunk 20. -/
def y322TCIndexRawChunk20 (i : Fin 4096) : Y322RawContextCertificate :=
  if i.val < 2048 then
    if i.val < 1024 then
      if i.val < 512 then
        if i.val < 256 then
          if i.val < 128 then
            if i.val < 64 then
              y322TCIndexRaw1280 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1281 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 192 then
              y322TCIndexRaw1282 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1283 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 384 then
            if i.val < 320 then
              y322TCIndexRaw1284 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1285 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 448 then
              y322TCIndexRaw1286 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1287 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 768 then
          if i.val < 640 then
            if i.val < 576 then
              y322TCIndexRaw1288 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1289 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 704 then
              y322TCIndexRaw1290 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1291 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 896 then
            if i.val < 832 then
              y322TCIndexRaw1292 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1293 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 960 then
              y322TCIndexRaw1294 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1295 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 1536 then
        if i.val < 1280 then
          if i.val < 1152 then
            if i.val < 1088 then
              y322TCIndexRaw1296 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1297 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1216 then
              y322TCIndexRaw1298 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1299 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1408 then
            if i.val < 1344 then
              y322TCIndexRaw1300 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1301 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1472 then
              y322TCIndexRaw1302 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1303 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 1792 then
          if i.val < 1664 then
            if i.val < 1600 then
              y322TCIndexRaw1304 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1305 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1728 then
              y322TCIndexRaw1306 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1307 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1920 then
            if i.val < 1856 then
              y322TCIndexRaw1308 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1309 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1984 then
              y322TCIndexRaw1310 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1311 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  else
    if i.val < 3072 then
      if i.val < 2560 then
        if i.val < 2304 then
          if i.val < 2176 then
            if i.val < 2112 then
              y322TCIndexRaw1312 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1313 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2240 then
              y322TCIndexRaw1314 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1315 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2432 then
            if i.val < 2368 then
              y322TCIndexRaw1316 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1317 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2496 then
              y322TCIndexRaw1318 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1319 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 2816 then
          if i.val < 2688 then
            if i.val < 2624 then
              y322TCIndexRaw1320 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1321 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2752 then
              y322TCIndexRaw1322 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1323 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2944 then
            if i.val < 2880 then
              y322TCIndexRaw1324 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1325 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3008 then
              y322TCIndexRaw1326 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1327 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 3584 then
        if i.val < 3328 then
          if i.val < 3200 then
            if i.val < 3136 then
              y322TCIndexRaw1328 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1329 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3264 then
              y322TCIndexRaw1330 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1331 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3456 then
            if i.val < 3392 then
              y322TCIndexRaw1332 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1333 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3520 then
              y322TCIndexRaw1334 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1335 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 3840 then
          if i.val < 3712 then
            if i.val < 3648 then
              y322TCIndexRaw1336 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1337 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3776 then
              y322TCIndexRaw1338 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1339 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3968 then
            if i.val < 3904 then
              y322TCIndexRaw1340 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1341 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 4032 then
              y322TCIndexRaw1342 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1343 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
