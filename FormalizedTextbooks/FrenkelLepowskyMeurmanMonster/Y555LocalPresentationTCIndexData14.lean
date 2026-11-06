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

/-- Exact literal claimed equations and contextual derivations, block 896. -/
def y322TCIndexRaw896 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89687, 9], [24325, 89687], .contexts [
        ⟨57293, false, false, [], []⟩,
        ⟨57296, false, false, [], []⟩,
        ⟨57343, false, false, [], []⟩,
        ⟨57343, false, false, [], []⟩
      ]⟩,
    ⟨[24347], [24325, 24341], .source 12238⟩,
    ⟨[24347, 87073], [24347, 87073], .contexts []⟩,
    ⟨[24349], [24346], .source 12239⟩,
    ⟨[24346], [24346], .contexts []⟩,
    ⟨[24341, 87071], [24341, 87071], .contexts []⟩,
    ⟨[24341, 87071], [24341, 87071], .contexts []⟩,
    ⟨[24341, 87071], [24347, 87073], .contexts [
        ⟨57350, true, false, [], []⟩,
        ⟨57350, true, false, [], []⟩,
        ⟨57349, true, false, [], []⟩,
        ⟨57334, true, false, [], []⟩,
        ⟨57329, true, false, [], []⟩,
        ⟨57347, false, false, [24348], [89687, 5]⟩,
        ⟨57348, false, false, [24348], [89687, 5]⟩,
        ⟨57348, false, false, [24348], [89687, 5]⟩,
        ⟨57288, true, false, [24348, 24346], [5]⟩,
        ⟨497, true, false, [24348, 24346, 89687], [5]⟩,
        ⟨57344, false, false, [24348, 24346], [5, 9, 5, 5]⟩,
        ⟨57334, false, false, [24348, 24346, 24325], [9, 5, 5]⟩,
        ⟨57345, true, false, [24348, 24346], [87071, 9, 5, 5]⟩,
        ⟨40125, false, false, [24348], [5, 5]⟩,
        ⟨57346, false, false, [24348, 24346], [5, 5]⟩,
        ⟨28, false, false, [24348, 87073], []⟩,
        ⟨57347, false, true, [], [87073]⟩
      ]⟩,
    ⟨[24351], [24333, 24347], .source 12240⟩,
    ⟨[24353], [24350], .source 12241⟩,
    ⟨[87073], [24353, 87071], .contexts [
        ⟨57352, false, false, [24350], [87073]⟩,
        ⟨57335, false, false, [24350], [24347, 87073]⟩,
        ⟨57346, true, false, [24350, 24340], []⟩,
        ⟨57351, true, false, [24350, 24340], []⟩,
        ⟨57353, true, false, [], [87071]⟩
      ]⟩,
    ⟨[24351], [24352], .contexts [
        ⟨57353, true, true, [], []⟩
      ]⟩,
    ⟨[24352], [24352], .contexts []⟩,
    ⟨[87071, 11], [24351, 87075], .contexts [
        ⟨57354, true, false, [24352], [11]⟩,
        ⟨40128, false, false, [24352], []⟩,
        ⟨40252, false, false, [24352], []⟩,
        ⟨57356, true, false, [], [87075]⟩,
        ⟨57356, true, false, [], [87075]⟩,
        ⟨57355, true, false, [], [87075]⟩
      ]⟩,
    ⟨[24355], [24324], .source 12242⟩,
    ⟨[24324], [24324], .contexts []⟩,
    ⟨[24343, 88003], [24343, 88003], .contexts []⟩,
    ⟨[24343, 88003], [24343, 88003], .contexts []⟩,
    ⟨[24343, 88001], [24343, 88001], .contexts []⟩,
    ⟨[88001, 13], [88001, 13], .contexts []⟩,
    ⟨[24342], [24342], .contexts []⟩,
    ⟨[88001, 13], [24345, 89681], .contexts [
        ⟨57363, false, false, [], []⟩,
        ⟨57362, true, false, [24342], [13]⟩,
        ⟨47690, true, false, [], [13]⟩,
        ⟨57361, true, false, [24342], [11, 13]⟩,
        ⟨57361, true, false, [24342], [11, 13]⟩,
        ⟨57360, true, false, [24342], [11, 13]⟩,
        ⟨57341, true, false, [24342], [11, 13]⟩,
        ⟨57338, true, false, [24342], [11, 13]⟩,
        ⟨931, false, false, [24342, 89683], []⟩,
        ⟨54, false, false, [24342, 89683], []⟩,
        ⟨56986, false, false, [24342], []⟩,
        ⟨56987, false, false, [24342], []⟩,
        ⟨56920, false, false, [24342], []⟩,
        ⟨56920, false, false, [24342], []⟩,
        ⟨57364, true, false, [], [89681]⟩,
        ⟨57364, true, false, [], [89681]⟩,
        ⟨57342, true, false, [], [89681]⟩
      ]⟩,
    ⟨[24343], [24344], .contexts [
        ⟨57342, true, true, [], []⟩
      ]⟩,
    ⟨[24351, 87075], [24351, 87075], .contexts []⟩,
    ⟨[24351, 87075], [24351, 87075], .contexts []⟩,
    ⟨[24351, 87077], [24351, 87077], .contexts []⟩,
    ⟨[87077], [87077], .contexts []⟩,
    ⟨[87069, 11], [24351, 87077], .contexts [
        ⟨40122, true, false, [], [11]⟩,
        ⟨40122, true, false, [], [11]⟩,
        ⟨40254, true, false, [], [11]⟩,
        ⟨40123, true, false, [], [11]⟩,
        ⟨110, false, false, [87071], []⟩,
        ⟨111, false, false, [87071], []⟩,
        ⟨57357, false, false, [], [1]⟩,
        ⟨57367, false, false, [], [1]⟩,
        ⟨57368, false, false, [], [1]⟩,
        ⟨57368, false, false, [], [1]⟩,
        ⟨40132, false, false, [24351], []⟩,
        ⟨57369, false, false, [], []⟩,
        ⟨57370, false, false, [24351], []⟩,
        ⟨13, true, false, [], [24351, 87077]⟩
      ]⟩,
    ⟨[87077, 11], [24353, 87069], .contexts [
        ⟨57371, true, false, [24350], [11]⟩,
        ⟨53, false, false, [24350, 87069], []⟩,
        ⟨57353, true, false, [], [87069]⟩
      ]⟩,
    ⟨[88001, 13], [24345, 89681], .contexts [
        ⟨57363, false, false, [], []⟩,
        ⟨57365, false, false, [], []⟩
      ]⟩,
    ⟨[24345, 89681], [24345, 89681], .contexts []⟩,
    ⟨[88001, 9], [87999], .contexts [
        ⟨47885, false, false, [], []⟩,
        ⟨47886, false, false, [], []⟩,
        ⟨47685, false, false, [], []⟩,
        ⟨47685, false, false, [], []⟩
      ]⟩,
    ⟨[24344], [24344], .contexts []⟩,
    ⟨[87999, 13], [24345, 89679], .contexts [
        ⟨57366, false, false, [24342], [87999, 13]⟩,
        ⟨57376, false, false, [24342], [87999, 13]⟩,
        ⟨57376, false, false, [24342], [87999, 13]⟩,
        ⟨57375, true, false, [24342, 24344], [13]⟩,
        ⟨47, true, false, [24342, 24344, 88001], [13]⟩,
        ⟨942, true, false, [24342, 24344, 88001], [13]⟩,
        ⟨57373, false, false, [24342, 24344], [9, 13, 13]⟩,
        ⟨57374, false, false, [24342, 24344], [9, 13, 13]⟩,
        ⟨57374, false, false, [24342, 24344], [9, 13, 13]⟩,
        ⟨56917, false, false, [24342], [13, 13]⟩,
        ⟨59, false, false, [24342, 89679], []⟩,
        ⟨57342, true, false, [], [89679]⟩
      ]⟩,
    ⟨[89711], [83637, 5], .source 44920⟩,
    ⟨[83637, 5], [89711], .contexts [
        ⟨57378, true, false, [], []⟩
      ]⟩,
    ⟨[89711, 5], [83637], .contexts [
        ⟨57379, true, false, [], [5]⟩,
        ⟨28, false, false, [83637], []⟩,
        ⟨22199, false, false, [], []⟩
      ]⟩,
    ⟨[89711], [89711], .contexts []⟩,
    ⟨[89711], [89711], .contexts []⟩,
    ⟨[83637, 5], [89711], .contexts [
        ⟨57379, false, false, [], []⟩,
        ⟨57381, false, false, [], []⟩,
        ⟨57382, false, false, [], []⟩,
        ⟨57382, false, false, [], []⟩
      ]⟩,
    ⟨[20331, 83791], [20331, 83791], .contexts []⟩,
    ⟨[20331, 83791], [20331, 83791], .contexts []⟩,
    ⟨[24357], [20331, 15077], .source 12243⟩,
    ⟨[24359], [24357, 3153], .source 12244⟩,
    ⟨[24359, 79893], [24359, 79893], .contexts []⟩,
    ⟨[24359, 79893], [24359, 79893], .contexts []⟩,
    ⟨[89711, 3], [89711, 3], .contexts []⟩,
    ⟨[89711, 3], [24359, 79893], .contexts [
        ⟨57390, false, false, [], []⟩,
        ⟨57383, true, false, [], [3]⟩,
        ⟨166, false, false, [83637], []⟩,
        ⟨169, false, false, [83637], []⟩,
        ⟨41849, false, false, [], [5, 3, 5]⟩,
        ⟨57384, false, false, [], [5, 3, 5]⟩,
        ⟨57385, false, false, [], [5, 3, 5]⟩,
        ⟨57385, false, false, [], [5, 3, 5]⟩,
        ⟨23062, false, false, [20331], [3, 5]⟩,
        ⟨57386, true, false, [], [79885, 3, 5]⟩,
        ⟨7320, false, false, [24357], [5]⟩,
        ⟨57387, true, false, [], [79705, 5]⟩,
        ⟨7371, false, false, [24359], []⟩,
        ⟨57388, false, false, [], []⟩,
        ⟨57389, false, false, [], []⟩,
        ⟨7373, false, false, [24359], []⟩
      ]⟩,
    ⟨[24359], [24359], .contexts [
        ⟨13, false, false, [], [24359]⟩
      ]⟩,
    ⟨[89711, 3], [24359, 79893], .contexts [
        ⟨57391, false, false, [], []⟩,
        ⟨57392, true, false, [], [79893]⟩
      ]⟩,
    ⟨[24361], [24358], .source 12245⟩,
    ⟨[79893, 3], [24361, 89711], .contexts [
        ⟨57393, true, false, [24358], [3]⟩,
        ⟨20, false, false, [24358, 89711], []⟩,
        ⟨57394, true, false, [], [89711]⟩
      ]⟩,
    ⟨[83637, 9], [20335, 83637], .contexts [
        ⟨41854, false, false, [], []⟩
      ]⟩,
    ⟨[20335, 83637], [20335, 83637], .contexts []⟩,
    ⟨[20335, 83637], [20335, 83637], .contexts []⟩,
    ⟨[20335, 89711], [20335, 89711], .contexts []⟩,
    ⟨[20335, 89711], [20335, 89711], .contexts []⟩,
    ⟨[20335, 89711], [20335, 89711], .contexts []⟩,
    ⟨[89711], [89711], .contexts []⟩,
    ⟨[20335], [20335], .contexts [
        ⟨13, false, false, [], [20335]⟩
      ]⟩,
    ⟨[89711, 9], [20335, 89711], .contexts [
        ⟨57383, true, false, [], [9]⟩,
        ⟨1265, false, false, [83637], []⟩,
        ⟨1266, false, false, [83637], []⟩,
        ⟨57396, false, false, [], [5]⟩,
        ⟨57397, false, false, [], [5]⟩,
        ⟨57398, false, false, [], [5]⟩,
        ⟨57398, false, false, [], [5]⟩,
        ⟨57379, false, false, [20335], []⟩,
        ⟨57399, false, false, [], []⟩,
        ⟨57400, false, false, [], []⟩,
        ⟨57401, false, false, [], []⟩,
        ⟨57402, false, false, [20335], []⟩,
        ⟨57403, true, false, [], [89711]⟩
      ]⟩,
    ⟨[20337, 83107], [20337, 83107], .contexts []⟩,
    ⟨[20337, 83107], [20337, 83107], .contexts []⟩,
    ⟨[89711, 11], [89711, 11], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 897. -/
def y322TCIndexRaw897 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[20519], [20519], .contexts [
        ⟨13, false, false, [], [20519]⟩
      ]⟩,
    ⟨[89711, 11], [20519, 85323], .contexts [
        ⟨57407, false, false, [], []⟩,
        ⟨57383, true, false, [], [11]⟩,
        ⟨174, false, false, [83637], []⟩,
        ⟨175, false, false, [83637], []⟩,
        ⟨41857, false, false, [], [5]⟩,
        ⟨57405, false, false, [], [5]⟩,
        ⟨57406, false, false, [], [5]⟩,
        ⟨57406, false, false, [], [5]⟩,
        ⟨31218, false, false, [20337], []⟩,
        ⟨42142, true, false, [], [85323]⟩,
        ⟨31212, false, false, [20519], []⟩,
        ⟨57408, true, false, [], [85323]⟩
      ]⟩,
    ⟨[24363], [20518], .source 12246⟩,
    ⟨[85323, 11], [24363, 89711], .contexts [
        ⟨57409, true, false, [20518], [11]⟩,
        ⟨53, false, false, [20518, 89711], []⟩,
        ⟨57410, true, false, [], [89711]⟩
      ]⟩,
    ⟨[89711, 13], [20325, 85353], .contexts [
        ⟨57383, true, false, [], [13]⟩,
        ⟨179, false, false, [83637], []⟩,
        ⟨180, false, false, [83637], []⟩,
        ⟨22198, false, false, [], [5]⟩,
        ⟨22252, false, false, [], [5]⟩,
        ⟨22203, false, false, [], [5]⟩,
        ⟨22203, false, false, [], [5]⟩,
        ⟨45394, false, false, [], []⟩,
        ⟨45395, false, false, [], []⟩,
        ⟨45396, false, false, [], []⟩,
        ⟨45396, false, false, [], []⟩,
        ⟨31739, false, false, [20325], []⟩,
        ⟨13, true, false, [], [20325, 85353]⟩
      ]⟩,
    ⟨[20331, 83795], [20331, 83795], .contexts []⟩,
    ⟨[20331, 83795], [20331, 83795], .contexts []⟩,
    ⟨[20331, 83797], [20331, 83797], .contexts []⟩,
    ⟨[20331, 83797], [20331, 83797], .contexts []⟩,
    ⟨[89711, 15], [89711, 15], .contexts []⟩,
    ⟨[20331], [20331], .contexts [
        ⟨13, false, false, [], [20331]⟩
      ]⟩,
    ⟨[89711, 15], [20331, 83797], .contexts [
        ⟨57417, false, false, [], []⟩,
        ⟨57383, true, false, [], [15]⟩,
        ⟨184, false, false, [83637], []⟩,
        ⟨185, false, false, [83637], []⟩,
        ⟨41858, false, false, [], [5]⟩,
        ⟨57413, false, false, [], [5]⟩,
        ⟨57414, false, false, [], [5]⟩,
        ⟨57414, false, false, [], [5]⟩,
        ⟨23123, false, false, [20331], []⟩,
        ⟨57415, false, false, [], []⟩,
        ⟨57416, false, false, [], []⟩,
        ⟨23140, false, false, [20331], []⟩,
        ⟨57418, true, false, [], [83797]⟩
      ]⟩,
    ⟨[24365], [20330], .source 12247⟩,
    ⟨[83797, 15], [24365, 89711], .contexts [
        ⟨57419, true, false, [20330], [15]⟩,
        ⟨1, false, false, [20330, 89711], []⟩,
        ⟨57420, true, false, [], [89711]⟩
      ]⟩,
    ⟨[89713], [89711, 1], .source 44921⟩,
    ⟨[89711, 1], [89713], .contexts [
        ⟨57422, true, false, [], []⟩
      ]⟩,
    ⟨[89713, 1], [89711], .contexts [
        ⟨57423, true, false, [], [1]⟩,
        ⟨8, false, false, [89711], []⟩,
        ⟨57382, false, false, [], []⟩
      ]⟩,
    ⟨[89713], [89713], .contexts []⟩,
    ⟨[89713], [89713], .contexts []⟩,
    ⟨[89711, 1], [89713], .contexts [
        ⟨57423, false, false, [], []⟩,
        ⟨57425, false, false, [], []⟩,
        ⟨57426, false, false, [], []⟩,
        ⟨57426, false, false, [], []⟩
      ]⟩,
    ⟨[24359, 88839], [24359, 88839], .contexts []⟩,
    ⟨[24359, 88839], [24359, 88839], .contexts []⟩,
    ⟨[89713, 3], [89713, 3], .contexts []⟩,
    ⟨[89713, 3], [24359, 88839], .contexts [
        ⟨57430, false, false, [], []⟩,
        ⟨57427, true, false, [], [3]⟩,
        ⟨1098, false, false, [89711], []⟩,
        ⟨1100, false, false, [89711], []⟩,
        ⟨57390, false, false, [], [1, 3, 1]⟩,
        ⟨57393, false, false, [], [1, 3, 1]⟩,
        ⟨57388, false, false, [], [1, 3, 1]⟩,
        ⟨57389, false, false, [], [1, 3, 1]⟩,
        ⟨57389, false, false, [], [1, 3, 1]⟩,
        ⟨7521, false, false, [24359], [3, 1]⟩,
        ⟨52885, false, false, [24359], [1]⟩,
        ⟨52916, false, false, [24359], []⟩,
        ⟨57428, false, false, [], []⟩,
        ⟨57429, false, false, [], []⟩,
        ⟨52926, false, false, [24359], []⟩
      ]⟩,
    ⟨[89713, 3], [24359, 88839], .contexts [
        ⟨57431, false, false, [], []⟩,
        ⟨57392, true, false, [], [88839]⟩
      ]⟩,
    ⟨[88839, 3], [24361, 89713], .contexts [
        ⟨57432, true, false, [24358], [3]⟩,
        ⟨20, false, false, [24358, 89713], []⟩,
        ⟨57394, true, false, [], [89713]⟩
      ]⟩,
    ⟨[89713, 5], [83635], .contexts [
        ⟨57427, true, false, [], [5]⟩,
        ⟨98, false, false, [89711], []⟩,
        ⟨99, false, false, [89711], []⟩,
        ⟨57380, false, false, [], [1]⟩,
        ⟨22253, false, false, [], [1]⟩,
        ⟨22199, false, false, [], [1]⟩,
        ⟨22199, false, false, [], [1]⟩,
        ⟨22254, false, false, [], []⟩,
        ⟨22255, false, false, [], []⟩,
        ⟨22195, false, false, [], []⟩,
        ⟨22195, false, false, [], []⟩,
        ⟨22473, false, false, [], []⟩,
        ⟨672, true, false, [], [83635]⟩
      ]⟩,
    ⟨[83635, 5], [89713], .contexts [
        ⟨57434, true, false, [], [5]⟩,
        ⟨28, false, false, [89713], []⟩,
        ⟨57426, false, false, [], []⟩
      ]⟩,
    ⟨[20519, 85323], [20519, 85323], .contexts []⟩,
    ⟨[20519, 85321], [20519, 85321], .contexts []⟩,
    ⟨[89713, 11], [20519, 85321], .contexts [
        ⟨57427, true, false, [], [11]⟩,
        ⟨110, false, false, [89711], []⟩,
        ⟨111, false, false, [89711], []⟩,
        ⟨57407, false, false, [], [1]⟩,
        ⟨57409, false, false, [], [1]⟩,
        ⟨57436, false, false, [], [1]⟩,
        ⟨57436, false, false, [], [1]⟩,
        ⟨31096, false, false, [20519], []⟩,
        ⟨57437, false, false, [], []⟩,
        ⟨42144, false, false, [20519], []⟩,
        ⟨57408, true, false, [], [85321]⟩
      ]⟩,
    ⟨[85321, 11], [24363, 89713], .contexts [
        ⟨57438, true, false, [20518], [11]⟩,
        ⟨53, false, false, [20518, 89713], []⟩,
        ⟨57410, true, false, [], [89713]⟩
      ]⟩,
    ⟨[20331, 83799], [20331, 83799], .contexts []⟩,
    ⟨[20331, 83799], [20331, 83799], .contexts []⟩,
    ⟨[89713, 15], [89713, 15], .contexts []⟩,
    ⟨[89713, 15], [20331, 83799], .contexts [
        ⟨57442, false, false, [], []⟩,
        ⟨57427, true, false, [], [15]⟩,
        ⟨121, false, false, [89711], []⟩,
        ⟨122, false, false, [89711], []⟩,
        ⟨57417, false, false, [], [1]⟩,
        ⟨57419, false, false, [], [1]⟩,
        ⟨57415, false, false, [], [1]⟩,
        ⟨57416, false, false, [], [1]⟩,
        ⟨57416, false, false, [], [1]⟩,
        ⟨23143, false, false, [20331], []⟩,
        ⟨57440, false, false, [], []⟩,
        ⟨57441, false, false, [], []⟩,
        ⟨24816, false, false, [20331], []⟩,
        ⟨57418, true, false, [], [83799]⟩
      ]⟩,
    ⟨[89715], [89713, 9], .source 44922⟩,
    ⟨[89713, 9], [89715], .contexts [
        ⟨57444, true, false, [], []⟩
      ]⟩,
    ⟨[89715, 9], [89713], .contexts [
        ⟨57445, true, false, [], [9]⟩,
        ⟨46, false, false, [89713], []⟩,
        ⟨57426, false, false, [], []⟩
      ]⟩,
    ⟨[89713, 9], [89715], .contexts [
        ⟨57445, false, false, [], []⟩
      ]⟩,
    ⟨[89715], [89715], .contexts []⟩,
    ⟨[89715], [89715], .contexts []⟩,
    ⟨[89713, 9], [89715], .contexts [
        ⟨57447, false, false, [], []⟩,
        ⟨57448, false, false, [], []⟩,
        ⟨57449, false, false, [], []⟩,
        ⟨57449, false, false, [], []⟩
      ]⟩,
    ⟨[20335, 89713], [20335, 89713], .contexts []⟩,
    ⟨[20335, 89713], [20335, 89713], .contexts []⟩,
    ⟨[20335, 89713], [20335, 89713], .contexts []⟩,
    ⟨[20335, 89715], [20335, 89715], .contexts []⟩,
    ⟨[20335, 89715], [20335, 89715], .contexts []⟩,
    ⟨[20335, 89715], [20335, 89715], .contexts []⟩,
    ⟨[89715, 1], [89715, 1], .contexts []⟩,
    ⟨[89715], [89715], .contexts []⟩,
    ⟨[89715, 1], [20335, 89715], .contexts [
        ⟨57457, false, false, [], []⟩,
        ⟨57450, true, false, [], [1]⟩,
        ⟨691, false, false, [89713], []⟩,
        ⟨694, false, false, [89713], []⟩,
        ⟨57424, false, false, [], [9, 1, 9]⟩,
        ⟨57381, false, false, [], [9, 1, 9]⟩,
        ⟨57382, false, false, [], [9, 1, 9]⟩,
        ⟨57382, false, false, [], [9, 1, 9]⟩,
        ⟨57404, false, false, [], [1, 9]⟩,
        ⟨57399, false, false, [], [1, 9]⟩,
        ⟨57401, false, false, [], [1, 9]⟩,
        ⟨57401, false, false, [], [1, 9]⟩,
        ⟨57423, false, false, [20335], [9]⟩,
        ⟨57451, false, false, [], [9]⟩,
        ⟨57452, false, false, [], [9]⟩,
        ⟨57453, false, false, [], [9]⟩,
        ⟨57445, false, false, [20335], []⟩,
        ⟨57454, false, false, [], []⟩,
        ⟨57455, false, false, [], []⟩,
        ⟨57456, false, false, [], []⟩,
        ⟨57458, false, false, [20335], []⟩
      ]⟩,
    ⟨[89715, 1], [20335, 89715], .contexts [
        ⟨57459, false, false, [], []⟩,
        ⟨57403, true, false, [], [89715]⟩
      ]⟩,
    ⟨[24359, 88841], [24359, 88841], .contexts []⟩,
    ⟨[24359, 88841], [24359, 88841], .contexts []⟩,
    ⟨[89715, 3], [89715, 3], .contexts []⟩,
    ⟨[89715, 3], [24359, 88841], .contexts [
        ⟨57463, false, false, [], []⟩,
        ⟨57450, true, false, [], [3]⟩,
        ⟨196, false, false, [89713], []⟩,
        ⟨197, false, false, [89713], []⟩,
        ⟨57430, false, false, [], [9]⟩,
        ⟨57432, false, false, [], [9]⟩,
        ⟨57428, false, false, [], [9]⟩,
        ⟨57429, false, false, [], [9]⟩,
        ⟨57429, false, false, [], [9]⟩,
        ⟨52941, false, false, [24359], []⟩,
        ⟨57461, false, false, [], []⟩,
        ⟨57462, false, false, [], []⟩,
        ⟨52949, false, false, [24359], []⟩,
        ⟨57392, true, false, [], [88841]⟩
      ]⟩,
    ⟨[88841, 3], [24361, 89715], .contexts [
        ⟨57464, true, false, [24358], [3]⟩,
        ⟨20, false, false, [24358, 89715], []⟩,
        ⟨57394, true, false, [], [89715]⟩
      ]⟩,
    ⟨[20331, 83801], [20331, 83801], .contexts []⟩,
    ⟨[20331, 83801], [20331, 83801], .contexts []⟩,
    ⟨[89715, 15], [89715, 15], .contexts []⟩,
    ⟨[89715, 15], [20331, 83801], .contexts [
        ⟨57468, false, false, [], []⟩,
        ⟨57450, true, false, [], [15]⟩,
        ⟨205, false, false, [89713], []⟩,
        ⟨206, false, false, [89713], []⟩,
        ⟨57442, false, false, [], [9]⟩,
        ⟨57443, false, false, [], [9]⟩,
        ⟨57440, false, false, [], [9]⟩,
        ⟨57441, false, false, [], [9]⟩,
        ⟨57441, false, false, [], [9]⟩,
        ⟨23146, false, false, [20331], []⟩,
        ⟨57466, false, false, [], []⟩,
        ⟨57467, false, false, [], []⟩,
        ⟨23158, false, false, [20331], []⟩,
        ⟨57418, true, false, [], [83801]⟩
      ]⟩,
    ⟨[83801, 15], [24365, 89715], .contexts [
        ⟨57469, true, false, [20330], [15]⟩,
        ⟨1, false, false, [20330, 89715], []⟩,
        ⟨57420, true, false, [], [89715]⟩
      ]⟩,
    ⟨[89717], [89715, 11], .source 44923⟩]

/-- Exact literal claimed equations and contextual derivations, block 898. -/
def y322TCIndexRaw898 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89715, 11], [89717], .contexts [
        ⟨57471, true, false, [], []⟩
      ]⟩,
    ⟨[89717, 11], [89715], .contexts [
        ⟨57472, true, false, [], [11]⟩,
        ⟨53, false, false, [89715], []⟩,
        ⟨57449, false, false, [], []⟩
      ]⟩,
    ⟨[89715, 11], [89717], .contexts [
        ⟨57472, false, false, [], []⟩
      ]⟩,
    ⟨[89717], [89717], .contexts []⟩,
    ⟨[89717], [89717], .contexts []⟩,
    ⟨[89715, 11], [89717], .contexts [
        ⟨57474, false, false, [], []⟩,
        ⟨57475, false, false, [], []⟩,
        ⟨57476, false, false, [], []⟩,
        ⟨57476, false, false, [], []⟩
      ]⟩,
    ⟨[20335, 89717], [20335, 89717], .contexts []⟩,
    ⟨[20335, 89717], [20335, 89717], .contexts []⟩,
    ⟨[89717], [89717], .contexts []⟩,
    ⟨[89717, 1], [20335, 89717], .contexts [
        ⟨57477, true, false, [], [1]⟩,
        ⟨562, false, false, [89715], []⟩,
        ⟨563, false, false, [89715], []⟩,
        ⟨57457, false, false, [], [11]⟩,
        ⟨57460, false, false, [], [11]⟩,
        ⟨57454, false, false, [], [11]⟩,
        ⟨57456, false, false, [], [11]⟩,
        ⟨57456, false, false, [], [11]⟩,
        ⟨57472, false, false, [20335], []⟩,
        ⟨57478, false, false, [], []⟩,
        ⟨57479, false, false, [], []⟩,
        ⟨57480, false, false, [20335], []⟩,
        ⟨57403, true, false, [], [89717]⟩
      ]⟩,
    ⟨[24359, 88843], [24359, 88843], .contexts []⟩,
    ⟨[89717, 3], [24359, 88843], .contexts [
        ⟨57477, true, false, [], [3]⟩,
        ⟨215, false, false, [89715], []⟩,
        ⟨216, false, false, [89715], []⟩,
        ⟨57463, false, false, [], [11]⟩,
        ⟨57464, false, false, [], [11]⟩,
        ⟨57461, false, false, [], [11]⟩,
        ⟨57462, false, false, [], [11]⟩,
        ⟨57462, false, false, [], [11]⟩,
        ⟨52958, false, false, [24359], []⟩,
        ⟨57482, false, false, [], []⟩,
        ⟨52966, false, false, [24359], []⟩,
        ⟨57392, true, false, [], [88843]⟩
      ]⟩,
    ⟨[88843, 3], [24361, 89717], .contexts [
        ⟨57483, true, false, [24358], [3]⟩,
        ⟨20, false, false, [24358, 89717], []⟩,
        ⟨57394, true, false, [], [89717]⟩
      ]⟩,
    ⟨[20331, 83803], [20331, 83803], .contexts []⟩,
    ⟨[20331, 83803], [20331, 83803], .contexts []⟩,
    ⟨[89717, 15], [20331, 83803], .contexts [
        ⟨57477, true, false, [], [15]⟩,
        ⟨231, false, false, [89715], []⟩,
        ⟨232, false, false, [89715], []⟩,
        ⟨57468, false, false, [], [11]⟩,
        ⟨57469, false, false, [], [11]⟩,
        ⟨57466, false, false, [], [11]⟩,
        ⟨57467, false, false, [], [11]⟩,
        ⟨57467, false, false, [], [11]⟩,
        ⟨23162, false, false, [20331], []⟩,
        ⟨57485, false, false, [], []⟩,
        ⟨57486, false, false, [], []⟩,
        ⟨23168, false, false, [20331], []⟩,
        ⟨57418, true, false, [], [83803]⟩
      ]⟩,
    ⟨[89719], [89717, 13], .source 44924⟩,
    ⟨[89717, 13], [89719], .contexts [
        ⟨57488, true, false, [], []⟩
      ]⟩,
    ⟨[89719, 13], [89717], .contexts [
        ⟨57489, true, false, [], [13]⟩,
        ⟨59, false, false, [89717], []⟩,
        ⟨57476, false, false, [], []⟩
      ]⟩,
    ⟨[89721], [89719, 15], .source 44925⟩,
    ⟨[89719, 15], [89721], .contexts [
        ⟨57491, true, false, [], []⟩
      ]⟩,
    ⟨[89719], [89719], .contexts []⟩,
    ⟨[89721, 15], [89719], .contexts [
        ⟨57492, true, false, [], [15]⟩,
        ⟨1, false, false, [89719], []⟩,
        ⟨57493, false, false, [], []⟩
      ]⟩,
    ⟨[89719, 15], [89721], .contexts [
        ⟨57492, false, false, [], []⟩
      ]⟩,
    ⟨[89721], [89721], .contexts []⟩,
    ⟨[89721], [89721], .contexts []⟩,
    ⟨[89719, 13], [89717], .contexts [
        ⟨57490, false, false, [], []⟩
      ]⟩,
    ⟨[20331, 83807], [20331, 83807], .contexts []⟩,
    ⟨[83807], [83807], .contexts []⟩,
    ⟨[89721, 13], [20331, 83807], .contexts [
        ⟨57497, true, false, [], [13]⟩,
        ⟨57497, true, false, [], [13]⟩,
        ⟨57496, true, false, [], [13]⟩,
        ⟨57495, true, false, [], [13]⟩,
        ⟨259, false, false, [89719], []⟩,
        ⟨262, false, false, [89719], []⟩,
        ⟨57498, false, false, [], [15, 13, 15]⟩,
        ⟨57475, false, false, [], [15, 13, 15]⟩,
        ⟨57476, false, false, [], [15, 13, 15]⟩,
        ⟨57476, false, false, [], [15, 13, 15]⟩,
        ⟨57487, false, false, [], [13, 15]⟩,
        ⟨57485, false, false, [], [13, 15]⟩,
        ⟨57486, false, false, [], [13, 15]⟩,
        ⟨57486, false, false, [], [13, 15]⟩,
        ⟨23171, false, false, [20331], [15]⟩,
        ⟨23174, false, false, [20331], []⟩,
        ⟨57499, false, false, [], []⟩,
        ⟨57500, false, false, [20331], []⟩
      ]⟩,
    ⟨[89721, 13], [20331, 83807], .contexts [
        ⟨57501, false, false, [], []⟩,
        ⟨57418, true, false, [], [83807]⟩
      ]⟩,
    ⟨[89723], [89721, 1], .source 44926⟩,
    ⟨[89721, 1], [89723], .contexts [
        ⟨57503, true, false, [], []⟩
      ]⟩,
    ⟨[89723, 1], [89721], .contexts [
        ⟨57504, true, false, [], [1]⟩,
        ⟨8, false, false, [89721], []⟩,
        ⟨57497, false, false, [], []⟩
      ]⟩,
    ⟨[89725], [89723, 3], .source 44927⟩,
    ⟨[89723, 3], [89725], .contexts [
        ⟨57506, true, false, [], []⟩
      ]⟩,
    ⟨[89723], [89723], .contexts []⟩,
    ⟨[89727], [89725, 5], .source 44928⟩,
    ⟨[89725, 5], [89727], .contexts [
        ⟨57509, true, false, [], []⟩
      ]⟩,
    ⟨[89725], [89725], .contexts []⟩,
    ⟨[89729], [89727, 1], .source 44929⟩,
    ⟨[89727, 1], [89729], .contexts [
        ⟨57512, true, false, [], []⟩
      ]⟩,
    ⟨[89727], [89727], .contexts []⟩,
    ⟨[89729, 1], [89727], .contexts [
        ⟨57513, true, false, [], [1]⟩,
        ⟨8, false, false, [89727], []⟩,
        ⟨57514, false, false, [], []⟩
      ]⟩,
    ⟨[89731], [89729, 9], .source 44930⟩,
    ⟨[89729, 9], [89731], .contexts [
        ⟨57516, true, false, [], []⟩
      ]⟩,
    ⟨[89729], [89729], .contexts []⟩,
    ⟨[89733], [89731, 11], .source 44931⟩,
    ⟨[89731, 11], [89733], .contexts [
        ⟨57519, true, false, [], []⟩
      ]⟩,
    ⟨[89731], [89731], .contexts []⟩,
    ⟨[89735], [89733, 1], .source 44932⟩,
    ⟨[89733, 1], [89735], .contexts [
        ⟨57522, true, false, [], []⟩
      ]⟩,
    ⟨[89733], [89733], .contexts []⟩,
    ⟨[89737], [89735, 13], .source 44933⟩,
    ⟨[89735, 13], [89737], .contexts [
        ⟨57525, true, false, [], []⟩
      ]⟩,
    ⟨[89735], [89735], .contexts []⟩,
    ⟨[89739], [89737, 15], .source 44934⟩,
    ⟨[89737, 15], [89739], .contexts [
        ⟨57528, true, false, [], []⟩
      ]⟩,
    ⟨[89737], [89737], .contexts []⟩,
    ⟨[89741], [89739, 1], .source 44935⟩,
    ⟨[89739, 1], [89741], .contexts [
        ⟨57531, true, false, [], []⟩
      ]⟩,
    ⟨[89739], [89739], .contexts []⟩,
    ⟨[89743], [89741, 3], .source 44936⟩,
    ⟨[89741, 3], [89743], .contexts [
        ⟨57534, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 899. -/
def y322TCIndexRaw899 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89741], [89741], .contexts []⟩,
    ⟨[89745], [89743, 5], .source 44937⟩,
    ⟨[89743, 5], [89745], .contexts [
        ⟨57537, true, false, [], []⟩
      ]⟩,
    ⟨[89743], [89743], .contexts []⟩,
    ⟨[89747], [89745, 1], .source 44938⟩,
    ⟨[89745, 1], [89747], .contexts [
        ⟨57540, true, false, [], []⟩
      ]⟩,
    ⟨[89745], [89745], .contexts []⟩,
    ⟨[89749], [89747, 9], .source 44939⟩,
    ⟨[89747, 9], [89749], .contexts [
        ⟨57543, true, false, [], []⟩
      ]⟩,
    ⟨[89747], [89747], .contexts []⟩,
    ⟨[89751], [89749, 11], .source 44940⟩,
    ⟨[89749, 11], [89751], .contexts [
        ⟨57546, true, false, [], []⟩
      ]⟩,
    ⟨[89749], [89749], .contexts []⟩,
    ⟨[89753], [89751, 1], .source 44941⟩,
    ⟨[89751, 1], [89753], .contexts [
        ⟨57549, true, false, [], []⟩
      ]⟩,
    ⟨[89751], [89751], .contexts []⟩,
    ⟨[89755], [89753, 13], .source 44942⟩,
    ⟨[89753, 13], [89755], .contexts [
        ⟨57552, true, false, [], []⟩
      ]⟩,
    ⟨[89753], [89753], .contexts []⟩,
    ⟨[89757], [89755, 15], .source 44943⟩,
    ⟨[89755, 15], [89757], .contexts [
        ⟨57555, true, false, [], []⟩
      ]⟩,
    ⟨[89755], [89755], .contexts []⟩,
    ⟨[89759], [89757, 1], .source 44944⟩,
    ⟨[89757, 1], [89759], .contexts [
        ⟨57558, true, false, [], []⟩
      ]⟩,
    ⟨[89757], [89757], .contexts []⟩,
    ⟨[89761], [89759, 3], .source 44945⟩,
    ⟨[89759, 3], [89761], .contexts [
        ⟨57561, true, false, [], []⟩
      ]⟩,
    ⟨[89759], [89759], .contexts []⟩,
    ⟨[89763], [89761, 5], .source 44946⟩,
    ⟨[89761, 5], [89763], .contexts [
        ⟨57564, true, false, [], []⟩
      ]⟩,
    ⟨[89761], [89761], .contexts []⟩,
    ⟨[89765], [89763, 1], .source 44947⟩,
    ⟨[89763, 1], [89765], .contexts [
        ⟨57567, true, false, [], []⟩
      ]⟩,
    ⟨[89763], [89763], .contexts []⟩,
    ⟨[89767], [89765, 9], .source 44948⟩,
    ⟨[89765, 9], [89767], .contexts [
        ⟨57570, true, false, [], []⟩
      ]⟩,
    ⟨[89765], [89765], .contexts []⟩,
    ⟨[89769], [89767, 11], .source 44949⟩,
    ⟨[89767, 11], [89769], .contexts [
        ⟨57573, true, false, [], []⟩
      ]⟩,
    ⟨[89767], [89767], .contexts []⟩,
    ⟨[89771], [89769, 1], .source 44950⟩,
    ⟨[89769, 1], [89771], .contexts [
        ⟨57576, true, false, [], []⟩
      ]⟩,
    ⟨[89769], [89769], .contexts []⟩,
    ⟨[89773], [89771, 13], .source 44951⟩,
    ⟨[89771, 13], [89773], .contexts [
        ⟨57579, true, false, [], []⟩
      ]⟩,
    ⟨[89771], [89771], .contexts []⟩,
    ⟨[89775], [89773, 15], .source 44952⟩,
    ⟨[89773, 15], [89775], .contexts [
        ⟨57582, true, false, [], []⟩
      ]⟩,
    ⟨[89773], [89773], .contexts []⟩,
    ⟨[89777], [89775, 1], .source 44953⟩,
    ⟨[89775, 1], [89777], .contexts [
        ⟨57585, true, false, [], []⟩
      ]⟩,
    ⟨[89775], [89775], .contexts []⟩,
    ⟨[89779], [89777, 3], .source 44954⟩,
    ⟨[89777, 3], [89779], .contexts [
        ⟨57588, true, false, [], []⟩
      ]⟩,
    ⟨[89777], [89777], .contexts []⟩,
    ⟨[89781], [89779, 5], .source 44955⟩,
    ⟨[89779, 5], [89781], .contexts [
        ⟨57591, true, false, [], []⟩
      ]⟩,
    ⟨[89779], [89779], .contexts []⟩,
    ⟨[89783], [89781, 1], .source 44956⟩,
    ⟨[89781, 1], [89783], .contexts [
        ⟨57594, true, false, [], []⟩
      ]⟩,
    ⟨[89781], [89781], .contexts []⟩,
    ⟨[89785], [89783, 9], .source 44957⟩,
    ⟨[89783, 9], [89785], .contexts [
        ⟨57597, true, false, [], []⟩
      ]⟩,
    ⟨[89783], [89783], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 900. -/
def y322TCIndexRaw900 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89787], [89785, 11], .source 44958⟩,
    ⟨[89785, 11], [89787], .contexts [
        ⟨57600, true, false, [], []⟩
      ]⟩,
    ⟨[89785], [89785], .contexts []⟩,
    ⟨[89789], [89787, 1], .source 44959⟩,
    ⟨[89787, 1], [89789], .contexts [
        ⟨57603, true, false, [], []⟩
      ]⟩,
    ⟨[89787], [89787], .contexts []⟩,
    ⟨[89791], [89789, 13], .source 44960⟩,
    ⟨[89789, 13], [89791], .contexts [
        ⟨57606, true, false, [], []⟩
      ]⟩,
    ⟨[89789], [89789], .contexts []⟩,
    ⟨[89793], [89791, 15], .source 44961⟩,
    ⟨[89791, 15], [89793], .contexts [
        ⟨57609, true, false, [], []⟩
      ]⟩,
    ⟨[89791], [89791], .contexts []⟩,
    ⟨[89793, 15], [89791], .contexts [
        ⟨57610, true, false, [], [15]⟩,
        ⟨1, false, false, [89791], []⟩,
        ⟨57611, false, false, [], []⟩
      ]⟩,
    ⟨[89795], [89793, 1], .source 44962⟩,
    ⟨[89793, 1], [89795], .contexts [
        ⟨57613, true, false, [], []⟩
      ]⟩,
    ⟨[89793], [89793], .contexts []⟩,
    ⟨[89795, 1], [89793], .contexts [
        ⟨57614, true, false, [], [1]⟩,
        ⟨8, false, false, [89793], []⟩,
        ⟨57615, false, false, [], []⟩
      ]⟩,
    ⟨[89797], [89795, 3], .source 44963⟩,
    ⟨[89795, 3], [89797], .contexts [
        ⟨57617, true, false, [], []⟩
      ]⟩,
    ⟨[89795], [89795], .contexts []⟩,
    ⟨[89799], [89797, 5], .source 44964⟩,
    ⟨[89797, 5], [89799], .contexts [
        ⟨57620, true, false, [], []⟩
      ]⟩,
    ⟨[89797], [89797], .contexts []⟩,
    ⟨[89799, 5], [89797], .contexts [
        ⟨57621, true, false, [], [5]⟩,
        ⟨28, false, false, [89797], []⟩,
        ⟨57622, false, false, [], []⟩
      ]⟩,
    ⟨[89801], [89799, 1], .source 44965⟩,
    ⟨[89799, 1], [89801], .contexts [
        ⟨57624, true, false, [], []⟩
      ]⟩,
    ⟨[89799], [89799], .contexts []⟩,
    ⟨[89803], [89801, 9], .source 44966⟩,
    ⟨[89801, 9], [89803], .contexts [
        ⟨57627, true, false, [], []⟩
      ]⟩,
    ⟨[89801], [89801], .contexts []⟩,
    ⟨[89805], [89803, 11], .source 44967⟩,
    ⟨[89803, 11], [89805], .contexts [
        ⟨57630, true, false, [], []⟩
      ]⟩,
    ⟨[89803], [89803], .contexts []⟩,
    ⟨[89805, 11], [89803], .contexts [
        ⟨57631, true, false, [], [11]⟩,
        ⟨53, false, false, [89803], []⟩,
        ⟨57632, false, false, [], []⟩
      ]⟩,
    ⟨[89807], [89805, 1], .source 44968⟩,
    ⟨[89805, 1], [89807], .contexts [
        ⟨57634, true, false, [], []⟩
      ]⟩,
    ⟨[89805], [89805], .contexts []⟩,
    ⟨[89807, 1], [89805], .contexts [
        ⟨57635, true, false, [], [1]⟩,
        ⟨8, false, false, [89805], []⟩,
        ⟨57636, false, false, [], []⟩
      ]⟩,
    ⟨[89809], [89807, 13], .source 44969⟩,
    ⟨[89807, 13], [89809], .contexts [
        ⟨57638, true, false, [], []⟩
      ]⟩,
    ⟨[89807], [89807], .contexts []⟩,
    ⟨[89809, 13], [89807], .contexts [
        ⟨57639, true, false, [], [13]⟩,
        ⟨59, false, false, [89807], []⟩,
        ⟨57640, false, false, [], []⟩
      ]⟩,
    ⟨[89811], [89809, 15], .source 44970⟩,
    ⟨[89809, 15], [89811], .contexts [
        ⟨57642, true, false, [], []⟩
      ]⟩,
    ⟨[89809], [89809], .contexts []⟩,
    ⟨[89811, 15], [89809], .contexts [
        ⟨57643, true, false, [], [15]⟩,
        ⟨1, false, false, [89809], []⟩,
        ⟨57644, false, false, [], []⟩
      ]⟩,
    ⟨[89813], [89811, 1], .source 44971⟩,
    ⟨[89811, 1], [89813], .contexts [
        ⟨57646, true, false, [], []⟩
      ]⟩,
    ⟨[89811], [89811], .contexts []⟩,
    ⟨[89813, 1], [89811], .contexts [
        ⟨57647, true, false, [], [1]⟩,
        ⟨8, false, false, [89811], []⟩,
        ⟨57648, false, false, [], []⟩
      ]⟩,
    ⟨[89815], [89813, 3], .source 44972⟩,
    ⟨[89813, 3], [89815], .contexts [
        ⟨57650, true, false, [], []⟩
      ]⟩,
    ⟨[89813], [89813], .contexts []⟩,
    ⟨[89815, 3], [89813], .contexts [
        ⟨57651, true, false, [], [3]⟩,
        ⟨20, false, false, [89813], []⟩,
        ⟨57652, false, false, [], []⟩
      ]⟩,
    ⟨[89817], [89815, 5], .source 44973⟩,
    ⟨[89815, 5], [89817], .contexts [
        ⟨57654, true, false, [], []⟩
      ]⟩,
    ⟨[89815], [89815], .contexts []⟩,
    ⟨[89817, 5], [89815], .contexts [
        ⟨57655, true, false, [], [5]⟩,
        ⟨28, false, false, [89815], []⟩,
        ⟨57656, false, false, [], []⟩
      ]⟩,
    ⟨[89819], [89817, 1], .source 44974⟩,
    ⟨[89817], [89817], .contexts []⟩,
    ⟨[89819, 1], [89817], .contexts [
        ⟨57658, false, false, [], [1]⟩,
        ⟨8, false, false, [89817], []⟩,
        ⟨57659, false, false, [], []⟩
      ]⟩,
    ⟨[89821], [89819, 9], .source 44975⟩,
    ⟨[89819, 9], [89821], .contexts [
        ⟨57661, true, false, [], []⟩
      ]⟩,
    ⟨[89819], [89819], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 901. -/
def y322TCIndexRaw901 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89821, 9], [89819], .contexts [
        ⟨57662, true, false, [], [9]⟩,
        ⟨46, false, false, [89819], []⟩,
        ⟨57663, false, false, [], []⟩
      ]⟩,
    ⟨[89823], [89821, 11], .source 44976⟩,
    ⟨[89821, 11], [89823], .contexts [
        ⟨57665, true, false, [], []⟩
      ]⟩,
    ⟨[89821], [89821], .contexts []⟩,
    ⟨[89823, 11], [89821], .contexts [
        ⟨57666, true, false, [], [11]⟩,
        ⟨53, false, false, [89821], []⟩,
        ⟨57667, false, false, [], []⟩
      ]⟩,
    ⟨[89825], [89823, 1], .source 44977⟩,
    ⟨[89823, 1], [89825], .contexts [
        ⟨57669, true, false, [], []⟩
      ]⟩,
    ⟨[89823], [89823], .contexts []⟩,
    ⟨[89825, 1], [89823], .contexts [
        ⟨57670, true, false, [], [1]⟩,
        ⟨8, false, false, [89823], []⟩,
        ⟨57671, false, false, [], []⟩
      ]⟩,
    ⟨[89827], [89825, 13], .source 44978⟩,
    ⟨[89825, 13], [89827], .contexts [
        ⟨57673, true, false, [], []⟩
      ]⟩,
    ⟨[89825], [89825], .contexts []⟩,
    ⟨[89827, 13], [89825], .contexts [
        ⟨57674, true, false, [], [13]⟩,
        ⟨59, false, false, [89825], []⟩,
        ⟨57675, false, false, [], []⟩
      ]⟩,
    ⟨[89829], [89827, 15], .source 44979⟩,
    ⟨[89827, 15], [89829], .contexts [
        ⟨57677, true, false, [], []⟩
      ]⟩,
    ⟨[89827], [89827], .contexts []⟩,
    ⟨[89829, 15], [89827], .contexts [
        ⟨57678, true, false, [], [15]⟩,
        ⟨1, false, false, [89827], []⟩,
        ⟨57679, false, false, [], []⟩
      ]⟩,
    ⟨[89831], [89829, 1], .source 44980⟩,
    ⟨[89829, 1], [89831], .contexts [
        ⟨57681, true, false, [], []⟩
      ]⟩,
    ⟨[89829], [89829], .contexts []⟩,
    ⟨[89831, 1], [89829], .contexts [
        ⟨57682, true, false, [], [1]⟩,
        ⟨8, false, false, [89829], []⟩,
        ⟨57683, false, false, [], []⟩
      ]⟩,
    ⟨[89833], [89831, 3], .source 44981⟩,
    ⟨[89831, 3], [89833], .contexts [
        ⟨57685, true, false, [], []⟩
      ]⟩,
    ⟨[89831], [89831], .contexts []⟩,
    ⟨[89833, 3], [89831], .contexts [
        ⟨57686, true, false, [], [3]⟩,
        ⟨20, false, false, [89831], []⟩,
        ⟨57687, false, false, [], []⟩
      ]⟩,
    ⟨[89835], [89833, 5], .source 44982⟩,
    ⟨[89833, 5], [89835], .contexts [
        ⟨57689, true, false, [], []⟩
      ]⟩,
    ⟨[89833], [89833], .contexts []⟩,
    ⟨[89835, 5], [89833], .contexts [
        ⟨57690, true, false, [], [5]⟩,
        ⟨28, false, false, [89833], []⟩,
        ⟨57691, false, false, [], []⟩
      ]⟩,
    ⟨[89837], [89835, 1], .source 44983⟩,
    ⟨[89835, 1], [89837], .contexts [
        ⟨57693, true, false, [], []⟩
      ]⟩,
    ⟨[89835], [89835], .contexts []⟩,
    ⟨[89837, 1], [89835], .contexts [
        ⟨57694, true, false, [], [1]⟩,
        ⟨8, false, false, [89835], []⟩,
        ⟨57695, false, false, [], []⟩
      ]⟩,
    ⟨[89837], [89837], .contexts []⟩,
    ⟨[89833], [89833], .contexts []⟩,
    ⟨[89835, 5], [89833], .contexts [
        ⟨57692, false, false, [], []⟩,
        ⟨57698, false, false, [], []⟩,
        ⟨57691, false, false, [], []⟩,
        ⟨57691, false, false, [], []⟩
      ]⟩,
    ⟨[89833, 3], [89831], .contexts [
        ⟨57688, false, false, [], []⟩
      ]⟩,
    ⟨[89831], [89831], .contexts []⟩,
    ⟨[89829], [89829], .contexts []⟩,
    ⟨[89829, 15], [89827], .contexts [
        ⟨57680, false, false, [], []⟩
      ]⟩,
    ⟨[89827], [89827], .contexts []⟩,
    ⟨[89827, 13], [89825], .contexts [
        ⟨57676, false, false, [], []⟩
      ]⟩,
    ⟨[89825], [89825], .contexts []⟩,
    ⟨[89825, 1], [89823], .contexts [
        ⟨57672, false, false, [], []⟩
      ]⟩,
    ⟨[89823], [89823], .contexts []⟩,
    ⟨[89835, 5, 3, 1, 15, 13, 1], [89823], .contexts [
        ⟨57699, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨57700, false, false, [], [1, 15, 13, 1]⟩,
        ⟨57701, false, false, [], [1, 15, 13, 1]⟩,
        ⟨57687, false, false, [], [1, 15, 13, 1]⟩,
        ⟨57687, false, false, [], [1, 15, 13, 1]⟩,
        ⟨57684, false, false, [], [15, 13, 1]⟩,
        ⟨57702, false, false, [], [15, 13, 1]⟩,
        ⟨57683, false, false, [], [15, 13, 1]⟩,
        ⟨57683, false, false, [], [15, 13, 1]⟩,
        ⟨57703, false, false, [], [13, 1]⟩,
        ⟨57704, false, false, [], [13, 1]⟩,
        ⟨57679, false, false, [], [13, 1]⟩,
        ⟨57679, false, false, [], [13, 1]⟩,
        ⟨57705, false, false, [], [1]⟩,
        ⟨57706, false, false, [], [1]⟩,
        ⟨57675, false, false, [], [1]⟩,
        ⟨57675, false, false, [], [1]⟩,
        ⟨57707, false, false, [], []⟩,
        ⟨57708, false, false, [], []⟩,
        ⟨57671, false, false, [], []⟩,
        ⟨57671, false, false, [], []⟩
      ]⟩,
    ⟨[89823, 11], [89821], .contexts [
        ⟨57668, false, false, [], []⟩
      ]⟩,
    ⟨[89821], [89821], .contexts []⟩,
    ⟨[89821, 9], [89819], .contexts [
        ⟨57664, false, false, [], []⟩
      ]⟩,
    ⟨[89819], [89819], .contexts []⟩,
    ⟨[89819, 1], [89817], .contexts [
        ⟨57660, false, false, [], []⟩
      ]⟩,
    ⟨[89817], [89817], .contexts []⟩,
    ⟨[89817, 5], [89815], .contexts [
        ⟨57657, false, false, [], []⟩
      ]⟩,
    ⟨[89815], [89815], .contexts []⟩,
    ⟨[89813], [89813], .contexts []⟩,
    ⟨[89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3], [89813], .contexts [
        ⟨57709, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨57710, false, false, [], [9, 1, 5, 3]⟩,
        ⟨57711, false, false, [], [9, 1, 5, 3]⟩,
        ⟨57667, false, false, [], [9, 1, 5, 3]⟩,
        ⟨57667, false, false, [], [9, 1, 5, 3]⟩,
        ⟨57712, false, false, [], [1, 5, 3]⟩,
        ⟨57713, false, false, [], [1, 5, 3]⟩,
        ⟨57663, false, false, [], [1, 5, 3]⟩,
        ⟨57663, false, false, [], [1, 5, 3]⟩,
        ⟨57714, false, false, [], [5, 3]⟩,
        ⟨57715, false, false, [], [5, 3]⟩,
        ⟨57659, false, false, [], [5, 3]⟩,
        ⟨57659, false, false, [], [5, 3]⟩,
        ⟨57716, false, false, [], [3]⟩,
        ⟨57717, false, false, [], [3]⟩,
        ⟨57656, false, false, [], [3]⟩,
        ⟨57656, false, false, [], [3]⟩,
        ⟨57653, false, false, [], []⟩,
        ⟨57718, false, false, [], []⟩,
        ⟨57652, false, false, [], []⟩,
        ⟨57652, false, false, [], []⟩
      ]⟩,
    ⟨[89813, 1], [89811], .contexts [
        ⟨57649, false, false, [], []⟩
      ]⟩,
    ⟨[89811], [89811], .contexts []⟩,
    ⟨[89809], [89809], .contexts []⟩,
    ⟨[89807], [89807], .contexts []⟩,
    ⟨[89805], [89805], .contexts []⟩,
    ⟨[89803], [89803], .contexts []⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11
    ], [89803], .contexts [
        ⟨57719, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨57720, false, false, [], [15, 13, 1, 11]⟩,
        ⟨57721, false, false, [], [15, 13, 1, 11]⟩,
        ⟨57648, false, false, [], [15, 13, 1, 11]⟩,
        ⟨57648, false, false, [], [15, 13, 1, 11]⟩,
        ⟨57645, false, false, [], [13, 1, 11]⟩,
        ⟨57722, false, false, [], [13, 1, 11]⟩,
        ⟨57644, false, false, [], [13, 1, 11]⟩,
        ⟨57644, false, false, [], [13, 1, 11]⟩,
        ⟨57641, false, false, [], [1, 11]⟩,
        ⟨57723, false, false, [], [1, 11]⟩,
        ⟨57640, false, false, [], [1, 11]⟩,
        ⟨57640, false, false, [], [1, 11]⟩,
        ⟨57637, false, false, [], [11]⟩,
        ⟨57724, false, false, [], [11]⟩,
        ⟨57636, false, false, [], [11]⟩,
        ⟨57636, false, false, [], [11]⟩,
        ⟨57633, false, false, [], []⟩,
        ⟨57725, false, false, [], []⟩,
        ⟨57632, false, false, [], []⟩,
        ⟨57632, false, false, [], []⟩
      ]⟩,
    ⟨[89799], [89799], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 902. -/
def y322TCIndexRaw902 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89797], [89797], .contexts []⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [89795], .contexts [
        ⟨57726, false, false, [], [9, 1, 5, 3]⟩,
        ⟨57628, true, false, [], [9, 1, 5, 3]⟩,
        ⟨46, false, false, [89801], [1, 5, 3]⟩,
        ⟨57629, false, false, [], [1, 5, 3]⟩,
        ⟨57629, false, false, [], [1, 5, 3]⟩,
        ⟨57629, false, false, [], [1, 5, 3]⟩,
        ⟨57625, true, false, [], [1, 5, 3]⟩,
        ⟨8, false, false, [89799], [5, 3]⟩,
        ⟨57626, false, false, [], [5, 3]⟩,
        ⟨57727, false, false, [], [5, 3]⟩,
        ⟨57626, false, false, [], [5, 3]⟩,
        ⟨57626, false, false, [], [5, 3]⟩,
        ⟨57623, false, false, [], [3]⟩,
        ⟨57728, false, false, [], [3]⟩,
        ⟨57622, false, false, [], [3]⟩,
        ⟨57622, false, false, [], [3]⟩,
        ⟨57618, true, false, [], [3]⟩,
        ⟨20, false, false, [89795], []⟩,
        ⟨57619, false, false, [], []⟩,
        ⟨57619, false, false, [], []⟩,
        ⟨57619, false, false, [], []⟩
      ]⟩,
    ⟨[89793], [89793], .contexts []⟩,
    ⟨[89791], [89791], .contexts []⟩,
    ⟨[89789], [89789], .contexts []⟩,
    ⟨[89787], [89787], .contexts []⟩,
    ⟨[89785], [89785], .contexts []⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11
    ], [89785], .contexts [
        ⟨57729, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨57616, false, false, [], [15, 13, 1, 11]⟩,
        ⟨57730, false, false, [], [15, 13, 1, 11]⟩,
        ⟨57615, false, false, [], [15, 13, 1, 11]⟩,
        ⟨57615, false, false, [], [15, 13, 1, 11]⟩,
        ⟨57612, false, false, [], [13, 1, 11]⟩,
        ⟨57731, false, false, [], [13, 1, 11]⟩,
        ⟨57611, false, false, [], [13, 1, 11]⟩,
        ⟨57611, false, false, [], [13, 1, 11]⟩,
        ⟨57607, true, false, [], [13, 1, 11]⟩,
        ⟨59, false, false, [89789], [1, 11]⟩,
        ⟨57608, false, false, [], [1, 11]⟩,
        ⟨57732, false, false, [], [1, 11]⟩,
        ⟨57608, false, false, [], [1, 11]⟩,
        ⟨57608, false, false, [], [1, 11]⟩,
        ⟨57604, true, false, [], [1, 11]⟩,
        ⟨8, false, false, [89787], [11]⟩,
        ⟨57605, false, false, [], [11]⟩,
        ⟨57733, false, false, [], [11]⟩,
        ⟨57605, false, false, [], [11]⟩,
        ⟨57605, false, false, [], [11]⟩,
        ⟨57601, true, false, [], [11]⟩,
        ⟨53, false, false, [89785], []⟩,
        ⟨57602, false, false, [], []⟩,
        ⟨57734, false, false, [], []⟩,
        ⟨57602, false, false, [], []⟩,
        ⟨57602, false, false, [], []⟩
      ]⟩,
    ⟨[89783], [89783], .contexts []⟩,
    ⟨[89781], [89781], .contexts []⟩,
    ⟨[89779], [89779], .contexts []⟩,
    ⟨[89777], [89777], .contexts []⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3
    ], [89777], .contexts [
        ⟨57735, false, false, [], [9, 1, 5, 3]⟩,
        ⟨57598, true, false, [], [9, 1, 5, 3]⟩,
        ⟨46, false, false, [89783], [1, 5, 3]⟩,
        ⟨57599, false, false, [], [1, 5, 3]⟩,
        ⟨57736, false, false, [], [1, 5, 3]⟩,
        ⟨57599, false, false, [], [1, 5, 3]⟩,
        ⟨57599, false, false, [], [1, 5, 3]⟩,
        ⟨57595, true, false, [], [1, 5, 3]⟩,
        ⟨8, false, false, [89781], [5, 3]⟩,
        ⟨57596, false, false, [], [5, 3]⟩,
        ⟨57737, false, false, [], [5, 3]⟩,
        ⟨57596, false, false, [], [5, 3]⟩,
        ⟨57596, false, false, [], [5, 3]⟩,
        ⟨57592, true, false, [], [5, 3]⟩,
        ⟨28, false, false, [89779], [3]⟩,
        ⟨57593, false, false, [], [3]⟩,
        ⟨57738, false, false, [], [3]⟩,
        ⟨57593, false, false, [], [3]⟩,
        ⟨57593, false, false, [], [3]⟩,
        ⟨57589, true, false, [], [3]⟩,
        ⟨20, false, false, [89777], []⟩,
        ⟨57590, false, false, [], []⟩,
        ⟨57739, false, false, [], []⟩,
        ⟨57590, false, false, [], []⟩,
        ⟨57590, false, false, [], []⟩
      ]⟩,
    ⟨[89775], [89775], .contexts []⟩,
    ⟨[89773], [89773], .contexts []⟩,
    ⟨[89771], [89771], .contexts []⟩,
    ⟨[89769], [89769], .contexts []⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [89769], .contexts [
        ⟨57740, false, false, [], [1, 15, 13, 1]⟩,
        ⟨57586, true, false, [], [1, 15, 13, 1]⟩,
        ⟨8, false, false, [89775], [15, 13, 1]⟩,
        ⟨57587, false, false, [], [15, 13, 1]⟩,
        ⟨57741, false, false, [], [15, 13, 1]⟩,
        ⟨57587, false, false, [], [15, 13, 1]⟩,
        ⟨57587, false, false, [], [15, 13, 1]⟩,
        ⟨57583, true, false, [], [15, 13, 1]⟩,
        ⟨1, false, false, [89773], [13, 1]⟩,
        ⟨57584, false, false, [], [13, 1]⟩,
        ⟨57742, false, false, [], [13, 1]⟩,
        ⟨57584, false, false, [], [13, 1]⟩,
        ⟨57584, false, false, [], [13, 1]⟩,
        ⟨57580, true, false, [], [13, 1]⟩,
        ⟨59, false, false, [89771], [1]⟩,
        ⟨57581, false, false, [], [1]⟩,
        ⟨57743, false, false, [], [1]⟩,
        ⟨57581, false, false, [], [1]⟩,
        ⟨57581, false, false, [], [1]⟩,
        ⟨57577, true, false, [], [1]⟩,
        ⟨8, false, false, [89769], []⟩,
        ⟨57578, false, false, [], []⟩,
        ⟨57744, false, false, [], []⟩,
        ⟨57578, false, false, [], []⟩,
        ⟨57578, false, false, [], []⟩
      ]⟩,
    ⟨[89767], [89767], .contexts []⟩,
    ⟨[89765], [89765], .contexts []⟩,
    ⟨[89763], [89763], .contexts []⟩,
    ⟨[89761], [89761], .contexts []⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5
    ], [89761], .contexts [
        ⟨57745, false, false, [], [11, 9, 1, 5]⟩,
        ⟨57574, true, false, [], [11, 9, 1, 5]⟩,
        ⟨53, false, false, [89767], [9, 1, 5]⟩,
        ⟨57575, false, false, [], [9, 1, 5]⟩,
        ⟨57746, false, false, [], [9, 1, 5]⟩,
        ⟨57575, false, false, [], [9, 1, 5]⟩,
        ⟨57575, false, false, [], [9, 1, 5]⟩,
        ⟨57571, true, false, [], [9, 1, 5]⟩,
        ⟨46, false, false, [89765], [1, 5]⟩,
        ⟨57572, false, false, [], [1, 5]⟩,
        ⟨57747, false, false, [], [1, 5]⟩,
        ⟨57572, false, false, [], [1, 5]⟩,
        ⟨57572, false, false, [], [1, 5]⟩,
        ⟨57568, true, false, [], [1, 5]⟩,
        ⟨8, false, false, [89763], [5]⟩,
        ⟨57569, false, false, [], [5]⟩,
        ⟨57748, false, false, [], [5]⟩,
        ⟨57569, false, false, [], [5]⟩,
        ⟨57569, false, false, [], [5]⟩,
        ⟨57565, true, false, [], [5]⟩,
        ⟨28, false, false, [89761], []⟩,
        ⟨57566, false, false, [], []⟩,
        ⟨57749, false, false, [], []⟩,
        ⟨57566, false, false, [], []⟩,
        ⟨57566, false, false, [], []⟩
      ]⟩,
    ⟨[89759], [89759], .contexts []⟩,
    ⟨[89757], [89757], .contexts []⟩,
    ⟨[89755], [89755], .contexts []⟩,
    ⟨[89753], [89753], .contexts []⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13
    ], [89753], .contexts [
        ⟨57750, false, false, [], [3, 1, 15, 13]⟩,
        ⟨57562, true, false, [], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [89759], [1, 15, 13]⟩,
        ⟨57563, false, false, [], [1, 15, 13]⟩,
        ⟨57751, false, false, [], [1, 15, 13]⟩,
        ⟨57563, false, false, [], [1, 15, 13]⟩,
        ⟨57563, false, false, [], [1, 15, 13]⟩,
        ⟨57559, true, false, [], [1, 15, 13]⟩,
        ⟨8, false, false, [89757], [15, 13]⟩,
        ⟨57560, false, false, [], [15, 13]⟩,
        ⟨57752, false, false, [], [15, 13]⟩,
        ⟨57560, false, false, [], [15, 13]⟩,
        ⟨57560, false, false, [], [15, 13]⟩,
        ⟨57556, true, false, [], [15, 13]⟩,
        ⟨1, false, false, [89755], [13]⟩,
        ⟨57557, false, false, [], [13]⟩,
        ⟨57753, false, false, [], [13]⟩,
        ⟨57557, false, false, [], [13]⟩,
        ⟨57557, false, false, [], [13]⟩,
        ⟨57553, true, false, [], [13]⟩,
        ⟨59, false, false, [89753], []⟩,
        ⟨57554, false, false, [], []⟩,
        ⟨57754, false, false, [], []⟩,
        ⟨57554, false, false, [], []⟩,
        ⟨57554, false, false, [], []⟩
      ]⟩,
    ⟨[89751], [89751], .contexts []⟩,
    ⟨[89749], [89749], .contexts []⟩,
    ⟨[89745], [89745], .contexts []⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [89745], .contexts [
        ⟨57755, false, false, [], [1, 11, 9, 1]⟩,
        ⟨57550, true, false, [], [1, 11, 9, 1]⟩,
        ⟨8, false, false, [89751], [11, 9, 1]⟩,
        ⟨57551, false, false, [], [11, 9, 1]⟩,
        ⟨57756, false, false, [], [11, 9, 1]⟩,
        ⟨57551, false, false, [], [11, 9, 1]⟩,
        ⟨57551, false, false, [], [11, 9, 1]⟩,
        ⟨57547, true, false, [], [11, 9, 1]⟩,
        ⟨53, false, false, [89749], [9, 1]⟩,
        ⟨57548, false, false, [], [9, 1]⟩,
        ⟨57757, false, false, [], [9, 1]⟩,
        ⟨57548, false, false, [], [9, 1]⟩,
        ⟨57548, false, false, [], [9, 1]⟩,
        ⟨57544, true, false, [], [9, 1]⟩,
        ⟨46, false, false, [89747], [1]⟩,
        ⟨57545, false, false, [], [1]⟩,
        ⟨57545, false, false, [], [1]⟩,
        ⟨57545, false, false, [], [1]⟩,
        ⟨57541, true, false, [], [1]⟩,
        ⟨8, false, false, [89745], []⟩,
        ⟨57542, false, false, [], []⟩,
        ⟨57758, false, false, [], []⟩,
        ⟨57542, false, false, [], []⟩,
        ⟨57542, false, false, [], []⟩
      ]⟩,
    ⟨[89743], [89743], .contexts []⟩,
    ⟨[89741], [89741], .contexts []⟩,
    ⟨[89739], [89739], .contexts []⟩,
    ⟨[89737], [89737], .contexts []⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15
    ], [89737], .contexts [
        ⟨57759, false, false, [], [5, 3, 1, 15]⟩,
        ⟨57538, true, false, [], [5, 3, 1, 15]⟩,
        ⟨28, false, false, [89743], [3, 1, 15]⟩,
        ⟨57539, false, false, [], [3, 1, 15]⟩,
        ⟨57760, false, false, [], [3, 1, 15]⟩,
        ⟨57539, false, false, [], [3, 1, 15]⟩,
        ⟨57539, false, false, [], [3, 1, 15]⟩,
        ⟨57535, true, false, [], [3, 1, 15]⟩,
        ⟨20, false, false, [89741], [1, 15]⟩,
        ⟨57536, false, false, [], [1, 15]⟩,
        ⟨57761, false, false, [], [1, 15]⟩,
        ⟨57536, false, false, [], [1, 15]⟩,
        ⟨57536, false, false, [], [1, 15]⟩,
        ⟨57532, true, false, [], [1, 15]⟩,
        ⟨8, false, false, [89739], [15]⟩,
        ⟨57533, false, false, [], [15]⟩,
        ⟨57762, false, false, [], [15]⟩,
        ⟨57533, false, false, [], [15]⟩,
        ⟨57533, false, false, [], [15]⟩,
        ⟨57529, true, false, [], [15]⟩,
        ⟨1, false, false, [89737], []⟩,
        ⟨57530, false, false, [], []⟩,
        ⟨57763, false, false, [], []⟩,
        ⟨57530, false, false, [], []⟩,
        ⟨57530, false, false, [], []⟩
      ]⟩,
    ⟨[89733], [89733], .contexts []⟩,
    ⟨[89731], [89731], .contexts []⟩,
    ⟨[89729], [89729], .contexts []⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9
    ], [89729], .contexts [
        ⟨57764, false, false, [], [13, 1, 11, 9]⟩,
        ⟨57526, true, false, [], [13, 1, 11, 9]⟩,
        ⟨59, false, false, [89735], [1, 11, 9]⟩,
        ⟨57527, false, false, [], [1, 11, 9]⟩,
        ⟨57527, false, false, [], [1, 11, 9]⟩,
        ⟨57527, false, false, [], [1, 11, 9]⟩,
        ⟨57523, true, false, [], [1, 11, 9]⟩,
        ⟨8, false, false, [89733], [11, 9]⟩,
        ⟨57524, false, false, [], [11, 9]⟩,
        ⟨57765, false, false, [], [11, 9]⟩,
        ⟨57524, false, false, [], [11, 9]⟩,
        ⟨57524, false, false, [], [11, 9]⟩,
        ⟨57520, true, false, [], [11, 9]⟩,
        ⟨53, false, false, [89731], [9]⟩,
        ⟨57521, false, false, [], [9]⟩,
        ⟨57766, false, false, [], [9]⟩,
        ⟨57521, false, false, [], [9]⟩,
        ⟨57521, false, false, [], [9]⟩,
        ⟨57517, true, false, [], [9]⟩,
        ⟨46, false, false, [89729], []⟩,
        ⟨57518, false, false, [], []⟩,
        ⟨57767, false, false, [], []⟩,
        ⟨57518, false, false, [], []⟩,
        ⟨57518, false, false, [], []⟩
      ]⟩,
    ⟨[89727], [89727], .contexts []⟩,
    ⟨[89725], [89725], .contexts []⟩,
    ⟨[89725, 3], [89723], .contexts [
        ⟨57507, true, false, [], [3]⟩,
        ⟨20, false, false, [89723], []⟩,
        ⟨57508, false, false, [], []⟩
      ]⟩,
    ⟨[89723], [89723], .contexts []⟩,
    ⟨[89719], [89719], .contexts []⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [89719], .contexts [
        ⟨57768, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨57515, false, false, [], [5, 3, 1, 15]⟩,
        ⟨57769, false, false, [], [5, 3, 1, 15]⟩,
        ⟨57514, false, false, [], [5, 3, 1, 15]⟩,
        ⟨57514, false, false, [], [5, 3, 1, 15]⟩,
        ⟨57510, true, false, [], [5, 3, 1, 15]⟩,
        ⟨28, false, false, [89725], [3, 1, 15]⟩,
        ⟨57511, false, false, [], [3, 1, 15]⟩,
        ⟨57770, false, false, [], [3, 1, 15]⟩,
        ⟨57511, false, false, [], [3, 1, 15]⟩,
        ⟨57511, false, false, [], [3, 1, 15]⟩,
        ⟨57771, false, false, [], [1, 15]⟩,
        ⟨57772, false, false, [], [1, 15]⟩,
        ⟨57508, false, false, [], [1, 15]⟩,
        ⟨57508, false, false, [], [1, 15]⟩,
        ⟨57505, false, false, [], [15]⟩,
        ⟨57496, false, false, [], [15]⟩,
        ⟨57497, false, false, [], [15]⟩,
        ⟨57497, false, false, [], [15]⟩,
        ⟨57494, false, false, [], []⟩,
        ⟨57773, false, false, [], []⟩,
        ⟨57493, false, false, [], []⟩,
        ⟨57493, false, false, [], []⟩
      ]⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1
    ], [20335, 89711], .contexts [
        ⟨57774, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨57498, false, false, [], [1, 11, 9, 1]⟩,
        ⟨57475, false, false, [], [1, 11, 9, 1]⟩,
        ⟨57476, false, false, [], [1, 11, 9, 1]⟩,
        ⟨57476, false, false, [], [1, 11, 9, 1]⟩,
        ⟨57481, false, false, [], [11, 9, 1]⟩,
        ⟨57478, false, false, [], [11, 9, 1]⟩,
        ⟨57479, false, false, [], [11, 9, 1]⟩,
        ⟨57479, false, false, [], [11, 9, 1]⟩,
        ⟨57473, false, false, [20335], [9, 1]⟩,
        ⟨57454, false, false, [], [9, 1]⟩,
        ⟨57455, false, false, [], [9, 1]⟩,
        ⟨57456, false, false, [], [9, 1]⟩,
        ⟨57446, false, false, [20335], [1]⟩,
        ⟨57451, false, false, [], [1]⟩,
        ⟨57452, false, false, [], [1]⟩,
        ⟨57453, false, false, [], [1]⟩,
        ⟨57424, false, false, [20335], []⟩,
        ⟨57399, false, false, [], []⟩,
        ⟨57400, false, false, [], []⟩,
        ⟨57401, false, false, [], []⟩
      ]⟩,
    ⟨[24367], [20335, 20331], .source 12248⟩,
    ⟨[24369], [24367, 1389], .source 12249⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [24369, 78729], .contexts [
        ⟨57775, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨57380, false, false, [20335], [3, 1, 15, 13]⟩,
        ⟨57397, false, false, [], [3, 1, 15, 13]⟩,
        ⟨57398, false, false, [], [3, 1, 15, 13]⟩,
        ⟨41849, false, false, [20335], [1, 15, 13]⟩,
        ⟨57776, true, false, [], [83791, 1, 15, 13]⟩,
        ⟨23059, false, false, [24367], [15, 13]⟩,
        ⟨57777, true, false, [], [83791, 15, 13]⟩,
        ⟨23079, false, false, [24369], [13]⟩,
        ⟨23106, false, false, [24369], []⟩
      ]⟩,
    ⟨[24371], [24369, 2243], .source 12250⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5
    ], [24371, 78731], .contexts [
        ⟨57778, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨4945, false, false, [24369], [11, 9, 1, 5]⟩,
        ⟨21814, false, false, [24369], [9, 1, 5]⟩,
        ⟨21811, false, false, [24369], [1, 5]⟩,
        ⟨57779, true, false, [], [83511, 1, 5]⟩,
        ⟨21799, false, false, [24371], [5]⟩,
        ⟨21769, false, false, [24371], []⟩
      ]⟩,
    ⟨[24373], [24371, 15065], .source 12251⟩,
    ⟨[24375], [24373, 2575], .source 12252⟩,
    ⟨[24377], [24375, 7357], .source 12253⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1
    ], [24377, 82655], .contexts [
        ⟨57780, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨14730, false, false, [24371], [1, 15, 13, 1]⟩,
        ⟨57781, true, false, [], [79179, 1, 15, 13, 1]⟩,
        ⟨6214, false, false, [24373], [15, 13, 1]⟩,
        ⟨6345, false, false, [24373], [13, 1]⟩,
        ⟨6361, false, false, [24373], [1]⟩,
        ⟨57782, true, false, [], [79201, 1]⟩,
        ⟨14985, false, false, [24375], []⟩,
        ⟨57783, true, false, [], [82655]⟩
      ]⟩,
    ⟨[24379], [24377, 1063], .source 12254⟩,
    ⟨[24381], [24379, 7355], .source 12255⟩,
    ⟨[24383], [24381, 15229], .source 12256⟩,
    ⟨[24385], [24383, 22521], .source 12257⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [24385, 88209], .contexts [
        ⟨57784, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨14975, false, false, [24377], [9, 1, 5, 3]⟩,
        ⟨4572, false, false, [24377], [1, 5, 3]⟩,
        ⟨57785, true, false, [], [78543, 1, 5, 3]⟩,
        ⟨11002, false, false, [24379], [5, 3]⟩,
        ⟨57786, true, false, [], [79381, 5, 3]⟩,
        ⟨15100, false, false, [24381], [3]⟩,
        ⟨57787, true, false, [], [82663, 3]⟩,
        ⟨49242, false, false, [24383], []⟩,
        ⟨57788, true, false, [], [88209]⟩
      ]⟩,
    ⟨[24387], [24385, 21103], .source 12258⟩,
    ⟨[24389], [24387, 18945], .source 12259⟩]

/-- Exact literal claimed equations and contextual derivations, block 903. -/
def y322TCIndexRaw903 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[24391], [24389, 18943], .source 12260⟩,
    ⟨[86215], [18941, 85939], .contexts [
        ⟨35869, false, false, [], []⟩
      ]⟩,
    ⟨[86215], [18941, 85939], .contexts [
        ⟨57793, false, false, [], []⟩,
        ⟨35857, false, false, [], []⟩
      ]⟩,
    ⟨[24393], [24391, 18941], .source 12261⟩,
    ⟨[
      89835, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11
    ], [24393, 85939], .contexts [
        ⟨57789, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨49261, false, false, [24385], [15, 13, 1, 11]⟩,
        ⟨49271, false, false, [24385], [13, 1, 11]⟩,
        ⟨57790, true, false, [], [85495, 13, 1, 11]⟩,
        ⟨35880, false, false, [24387], [1, 11]⟩,
        ⟨57791, true, false, [], [85935, 1, 11]⟩,
        ⟨35887, false, false, [24389], [11]⟩,
        ⟨57792, true, false, [], [86213, 11]⟩,
        ⟨35682, false, false, [24391], []⟩,
        ⟨57794, false, false, [24391], []⟩,
        ⟨57795, true, false, [], [85939]⟩
      ]⟩,
    ⟨[89837, 9], [89837, 9], .contexts []⟩,
    ⟨[89837, 9], [24393, 85939], .contexts [
        ⟨57797, false, false, [], []⟩,
        ⟨57697, true, false, [], [9]⟩,
        ⟨57697, true, false, [], [9]⟩,
        ⟨57694, true, false, [], [9]⟩,
        ⟨447, false, false, [89835], []⟩,
        ⟨449, false, false, [89835], []⟩,
        ⟨57796, false, false, [], []⟩,
        ⟨44432, false, false, [24393], []⟩,
        ⟨13, true, false, [], [24393, 85939]⟩
      ]⟩,
    ⟨[24395], [24392], .source 12262⟩,
    ⟨[85939, 9], [24395, 89837], .contexts [
        ⟨57798, true, false, [24392], [9]⟩,
        ⟨46, false, false, [24392, 89837], []⟩,
        ⟨57799, true, false, [], [89837]⟩
      ]⟩,
    ⟨[89835], [89835], .contexts []⟩,
    ⟨[89837, 1], [89835], .contexts [
        ⟨57696, false, false, [], []⟩,
        ⟨57801, false, false, [], []⟩,
        ⟨57695, false, false, [], []⟩,
        ⟨57695, false, false, [], []⟩
      ]⟩,
    ⟨[24393, 85939], [24393, 85939], .contexts []⟩,
    ⟨[89837, 9], [24393, 85939], .contexts [
        ⟨57797, false, false, [], []⟩,
        ⟨57798, false, false, [], []⟩,
        ⟨57803, false, false, [], []⟩,
        ⟨57803, false, false, [], []⟩
      ]⟩,
    ⟨[24397], [24393, 23615], .source 12263⟩,
    ⟨[24397, 89083], [24397, 89083], .contexts []⟩,
    ⟨[24397, 89083], [24397, 89083], .contexts []⟩,
    ⟨[89835, 9], [89835, 9], .contexts []⟩,
    ⟨[89835, 9], [24397, 89083], .contexts [
        ⟨57808, false, false, [], []⟩,
        ⟨57802, true, false, [], [9]⟩,
        ⟨452, false, false, [89837], []⟩,
        ⟨455, false, false, [89837], []⟩,
        ⟨57804, false, false, [], [1, 9, 1]⟩,
        ⟨34239, false, false, [24393], [9, 1]⟩,
        ⟨54177, false, false, [24393], [1]⟩,
        ⟨57805, true, false, [], [89085, 1]⟩,
        ⟨53909, false, false, [24397], []⟩,
        ⟨57806, false, false, [], []⟩,
        ⟨57807, false, false, [], []⟩,
        ⟨54168, false, false, [24397], []⟩,
        ⟨13, true, false, [], [24397, 89083]⟩
      ]⟩,
    ⟨[24399], [24396], .source 12264⟩,
    ⟨[89083, 9], [24399, 89835], .contexts [
        ⟨57809, true, false, [24396], [9]⟩,
        ⟨46, false, false, [24396, 89835], []⟩,
        ⟨57810, true, false, [], [89835]⟩
      ]⟩,
    ⟨[24393, 88473], [24393, 88473], .contexts []⟩,
    ⟨[89837], [89837], .contexts []⟩,
    ⟨[88473, 13], [88473, 13], .contexts []⟩,
    ⟨[89837], [89837], .contexts []⟩,
    ⟨[24392], [24392], .contexts []⟩,
    ⟨[88473, 13], [24395, 89837], .contexts [
        ⟨57814, false, false, [], []⟩,
        ⟨57812, true, false, [24392], [13]⟩,
        ⟨50743, true, false, [], [13]⟩,
        ⟨34241, true, false, [], [9, 13]⟩,
        ⟨57804, true, false, [24392], [13, 9, 13]⟩,
        ⟨475, false, false, [24392, 89837], []⟩,
        ⟨57813, false, false, [24392], []⟩,
        ⟨57815, false, false, [24392], []⟩,
        ⟨57816, true, false, [], [89837]⟩,
        ⟨57816, true, false, [], [89837]⟩,
        ⟨57799, true, false, [], [89837]⟩
      ]⟩,
    ⟨[89835, 9], [24397, 89083], .contexts [
        ⟨57808, false, false, [], []⟩,
        ⟨57809, false, false, [], []⟩,
        ⟨57806, false, false, [], []⟩,
        ⟨57807, false, false, [], []⟩,
        ⟨57807, false, false, [], []⟩
      ]⟩,
    ⟨[24401], [24397, 23609], .source 12265⟩,
    ⟨[24403], [24401, 23411], .source 12266⟩,
    ⟨[89835], [89835], .contexts []⟩,
    ⟨[88961, 13], [88961, 13], .contexts []⟩,
    ⟨[89835], [89835], .contexts []⟩,
    ⟨[24405], [24402], .source 12267⟩,
    ⟨[24402], [24402], .contexts []⟩,
    ⟨[24405], [24402], .contexts [
        ⟨57824, false, false, [], []⟩,
        ⟨57825, false, false, [], []⟩,
        ⟨57825, false, false, [], []⟩
      ]⟩,
    ⟨[88961, 13], [24405, 89835], .contexts [
        ⟨57822, false, false, [], []⟩,
        ⟨57820, false, false, [24402], [88961, 13]⟩,
        ⟨53423, true, false, [24402, 24401], [13]⟩,
        ⟨57819, false, false, [24402], [83891, 9, 13]⟩,
        ⟨54172, true, false, [24402, 24397], [9, 13]⟩,
        ⟨57818, true, false, [24402], [13, 9, 13]⟩,
        ⟨475, false, false, [24402, 89835], []⟩,
        ⟨57821, false, false, [24402], []⟩,
        ⟨57823, false, false, [24402], []⟩,
        ⟨57826, true, false, [], [89835]⟩
      ]⟩,
    ⟨[24403], [24404], .contexts [
        ⟨57824, true, true, [], []⟩
      ]⟩,
    ⟨[89835, 13], [24403, 88961], .contexts [
        ⟨57827, true, false, [24404], [13]⟩,
        ⟨59, false, false, [24404, 88961], []⟩,
        ⟨57828, true, false, [], [88961]⟩
      ]⟩,
    ⟨[24405, 89835], [24405, 89835], .contexts []⟩,
    ⟨[24405, 89835], [24405, 89835], .contexts []⟩,
    ⟨[88961, 13], [24405, 89835], .contexts [
        ⟨57822, false, false, [], []⟩,
        ⟨57827, false, false, [], []⟩,
        ⟨57830, false, false, [], []⟩,
        ⟨57831, false, false, [], []⟩,
        ⟨57831, false, false, [], []⟩
      ]⟩,
    ⟨[89833, 13], [89833, 13], .contexts []⟩,
    ⟨[24404], [24404], .contexts []⟩,
    ⟨[89833, 13], [24403, 88959], .contexts [
        ⟨57833, false, false, [], []⟩,
        ⟨57692, true, false, [], [13]⟩,
        ⟨57832, true, false, [24404], [5, 13]⟩,
        ⟨1136, false, false, [24404, 88961], []⟩,
        ⟨53467, false, false, [24404], []⟩,
        ⟨53466, false, false, [24404], []⟩,
        ⟨53469, false, false, [24404], []⟩,
        ⟨57834, true, false, [], [88959]⟩,
        ⟨57834, true, false, [], [88959]⟩,
        ⟨57828, true, false, [], [88959]⟩
      ]⟩,
    ⟨[24403, 88959], [24403, 88959], .contexts []⟩,
    ⟨[24403, 88959], [24403, 88959], .contexts []⟩,
    ⟨[24403, 88957], [24403, 88957], .contexts []⟩,
    ⟨[89833, 3], [89831], .contexts [
        ⟨57700, false, false, [], []⟩
      ]⟩,
    ⟨[89833, 3], [89831], .contexts [
        ⟨57839, false, false, [], []⟩,
        ⟨57701, false, false, [], []⟩,
        ⟨57687, false, false, [], []⟩,
        ⟨57687, false, false, [], []⟩
      ]⟩,
    ⟨[89833, 2], [89833, 3], .contexts [
        ⟨21, false, false, [89833], []⟩
      ]⟩,
    ⟨[88957, 13], [88957, 13], .contexts []⟩,
    ⟨[89831], [89831], .contexts []⟩,
    ⟨[88957, 13], [24405, 89831], .contexts [
        ⟨57842, false, false, [], []⟩,
        ⟨57838, true, false, [24402], [13]⟩,
        ⟨53244, true, false, [], [13]⟩,
        ⟨57837, true, false, [24402], [3, 13]⟩,
        ⟨57837, true, false, [24402], [3, 13]⟩,
        ⟨57836, true, false, [24402], [3, 13]⟩,
        ⟨57835, true, false, [24402], [3, 13]⟩,
        ⟨57833, true, false, [24402], [3, 13]⟩,
        ⟨1132, false, false, [24402, 89833], []⟩,
        ⟨57841, false, false, [24402], []⟩,
        ⟨57840, false, false, [24402], []⟩,
        ⟨57843, false, false, [24402], []⟩,
        ⟨57826, true, false, [], [89831]⟩
      ]⟩,
    ⟨[89839], [84717, 5], .source 44984⟩,
    ⟨[84717, 5], [89839], .contexts [
        ⟨57845, true, false, [], []⟩
      ]⟩,
    ⟨[89839, 5], [84717], .contexts [
        ⟨57846, true, false, [], [5]⟩,
        ⟨28, false, false, [84717], []⟩,
        ⟨28157, false, false, [], []⟩
      ]⟩,
    ⟨[89839], [89839], .contexts []⟩,
    ⟨[89839], [89839], .contexts []⟩,
    ⟨[84717, 5], [89839], .contexts [
        ⟨57846, false, false, [], []⟩,
        ⟨57848, false, false, [], []⟩,
        ⟨57849, false, false, [], []⟩,
        ⟨57849, false, false, [], []⟩
      ]⟩,
    ⟨[24407], [17525, 16017], .source 12268⟩,
    ⟨[24407, 83943], [24407, 83943], .contexts []⟩,
    ⟨[89839, 3], [24407, 83943], .contexts [
        ⟨57850, true, false, [], [3]⟩,
        ⟨166, false, false, [84717], []⟩,
        ⟨169, false, false, [84717], []⟩,
        ⟨28276, false, false, [], [5, 3, 5]⟩,
        ⟨19615, false, false, [17525], [3, 5]⟩,
        ⟨28264, false, false, [], [3, 5]⟩,
        ⟨28265, false, false, [], [3, 5]⟩,
        ⟨28266, false, false, [], [3, 5]⟩,
        ⟨19724, false, false, [17525], [5]⟩,
        ⟨57851, true, false, [], [83189, 5]⟩,
        ⟨23963, false, false, [24407], []⟩,
        ⟨57852, false, false, [], []⟩,
        ⟨23970, false, false, [24407], []⟩,
        ⟨13, true, false, [], [24407, 83943]⟩
      ]⟩,
    ⟨[24409], [24406], .source 12269⟩,
    ⟨[17525, 87577], [17525, 87577], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 904. -/
def y322TCIndexRaw904 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[17525, 87577], [17525, 87577], .contexts []⟩,
    ⟨[24411], [17525, 21283], .source 12270⟩,
    ⟨[24413], [24411, 17527], .source 12271⟩,
    ⟨[24413, 89839], [24413, 89839], .contexts []⟩,
    ⟨[24413, 89839], [24413, 89839], .contexts []⟩,
    ⟨[89839, 7], [89839, 7], .contexts []⟩,
    ⟨[89839], [89839], .contexts []⟩,
    ⟨[89839, 7], [24413, 89839], .contexts [
        ⟨57861, false, false, [], []⟩,
        ⟨57850, true, false, [], [7]⟩,
        ⟨3272, false, false, [84717], []⟩,
        ⟨3275, false, false, [84717], []⟩,
        ⟨44759, false, false, [], [5, 7, 5]⟩,
        ⟨57855, false, false, [], [5, 7, 5]⟩,
        ⟨57856, false, false, [], [5, 7, 5]⟩,
        ⟨57856, false, false, [], [5, 7, 5]⟩,
        ⟨44756, false, false, [17525], [7, 5]⟩,
        ⟨57857, true, false, [], [87577, 7, 5]⟩,
        ⟨44758, false, false, [24411], [5]⟩,
        ⟨57858, true, false, [], [84717, 5]⟩,
        ⟨57846, false, false, [24413], []⟩,
        ⟨57859, false, false, [], []⟩,
        ⟨57860, false, false, [], []⟩,
        ⟨57862, false, false, [24413], []⟩
      ]⟩,
    ⟨[24413], [24413], .contexts [
        ⟨13, false, false, [], [24413]⟩
      ]⟩,
    ⟨[17525, 87715], [17525, 87715], .contexts []⟩,
    ⟨[17525, 87715], [17525, 87715], .contexts []⟩,
    ⟨[17525, 87717], [17525, 87717], .contexts []⟩,
    ⟨[17525, 87717], [17525, 87717], .contexts []⟩,
    ⟨[89839, 9], [17525, 87717], .contexts [
        ⟨57850, true, false, [], [9]⟩,
        ⟨1265, false, false, [84717], []⟩,
        ⟨1266, false, false, [84717], []⟩,
        ⟨45827, false, false, [], [5]⟩,
        ⟨57865, false, false, [], [5]⟩,
        ⟨57866, false, false, [], [5]⟩,
        ⟨57866, false, false, [], [5]⟩,
        ⟨45842, false, false, [17525], []⟩,
        ⟨57867, false, false, [], []⟩,
        ⟨57868, false, false, [], []⟩,
        ⟨45850, false, false, [17525], []⟩,
        ⟨28272, true, false, [], [87717]⟩
      ]⟩,
    ⟨[17524, 89839], [17527, 89839], .contexts [
        ⟨28274, true, false, [], [89839]⟩
      ]⟩,
    ⟨[17525, 87335], [17525, 87335], .contexts []⟩,
    ⟨[17525, 87335], [17525, 87335], .contexts []⟩,
    ⟨[17525, 87337], [17525, 87337], .contexts []⟩,
    ⟨[17525, 87337], [17525, 87337], .contexts []⟩,
    ⟨[89839, 11], [89839, 11], .contexts []⟩,
    ⟨[89839, 11], [17525, 87337], .contexts [
        ⟨57875, false, false, [], []⟩,
        ⟨57850, true, false, [], [11]⟩,
        ⟨174, false, false, [84717], []⟩,
        ⟨175, false, false, [84717], []⟩,
        ⟨41348, false, false, [], [5]⟩,
        ⟨57871, false, false, [], [5]⟩,
        ⟨57872, false, false, [], [5]⟩,
        ⟨57872, false, false, [], [5]⟩,
        ⟨41357, false, false, [17525], []⟩,
        ⟨57873, false, false, [], []⟩,
        ⟨57874, false, false, [], []⟩,
        ⟨41373, false, false, [17525], []⟩,
        ⟨28272, true, false, [], [87337]⟩
      ]⟩,
    ⟨[87337, 11], [17527, 89839], .contexts [
        ⟨57876, true, false, [17524], [11]⟩,
        ⟨53, false, false, [17524, 89839], []⟩,
        ⟨57870, false, false, [], []⟩
      ]⟩,
    ⟨[17539, 89839], [17539, 89839], .contexts []⟩,
    ⟨[17539, 89839], [17539, 89839], .contexts []⟩,
    ⟨[89839, 15], [89839, 15], .contexts []⟩,
    ⟨[17539], [17539], .contexts [
        ⟨13, false, false, [], [17539]⟩,
        ⟨28301, false, false, [], []⟩,
        ⟨28302, false, false, [], []⟩
      ]⟩,
    ⟨[89841], [89839, 1], .source 44985⟩,
    ⟨[89839, 1], [89841], .contexts [
        ⟨57882, true, false, [], []⟩
      ]⟩,
    ⟨[89841, 1], [89839], .contexts [
        ⟨57883, true, false, [], [1]⟩,
        ⟨8, false, false, [89839], []⟩,
        ⟨57849, false, false, [], []⟩
      ]⟩,
    ⟨[89841], [89841], .contexts []⟩,
    ⟨[89839, 1], [89841], .contexts [
        ⟨57883, false, false, [], []⟩,
        ⟨57885, false, false, [], []⟩,
        ⟨57885, false, false, [], []⟩
      ]⟩,
    ⟨[84713, 5], [17537, 89841], .contexts [
        ⟨57881, false, false, [17538], [84713, 5]⟩,
        ⟨28315, true, false, [], [5]⟩,
        ⟨28295, true, false, [17538], [5]⟩,
        ⟨28295, true, false, [17538], [5]⟩,
        ⟨28308, true, false, [17538], [5]⟩,
        ⟨28300, true, false, [17538], [5]⟩,
        ⟨28157, true, false, [17538], [1, 5]⟩,
        ⟨28157, true, false, [17538], [1, 5]⟩,
        ⟨28156, true, false, [17538], [1, 5]⟩,
        ⟨57847, true, false, [17538], [1, 5]⟩,
        ⟨99, true, false, [17538, 89839], [5]⟩,
        ⟨98, true, false, [17538, 89839], [5]⟩,
        ⟨57886, false, false, [17538], [5, 5]⟩,
        ⟨28, false, false, [17538, 89841], []⟩,
        ⟨28297, true, false, [], [89841]⟩
      ]⟩,
    ⟨[24413, 89841], [24413, 89841], .contexts []⟩,
    ⟨[24413, 89841], [24413, 89841], .contexts []⟩,
    ⟨[89841, 7], [89841, 7], .contexts []⟩,
    ⟨[89841], [89841], .contexts []⟩,
    ⟨[17525, 87339], [17525, 87339], .contexts []⟩,
    ⟨[89841, 11], [17525, 87339], .contexts [
        ⟨57886, true, false, [], [11]⟩,
        ⟨110, false, false, [89839], []⟩,
        ⟨111, false, false, [89839], []⟩,
        ⟨57875, false, false, [], [1]⟩,
        ⟨57876, false, false, [], [1]⟩,
        ⟨57873, false, false, [], [1]⟩,
        ⟨57874, false, false, [], [1]⟩,
        ⟨57874, false, false, [], [1]⟩,
        ⟨41385, false, false, [17525], []⟩,
        ⟨57892, false, false, [], []⟩,
        ⟨41395, false, false, [17525], []⟩,
        ⟨28272, true, false, [], [87339]⟩
      ]⟩,
    ⟨[17539, 89841], [17539, 89841], .contexts []⟩,
    ⟨[17539, 89841], [17539, 89841], .contexts []⟩,
    ⟨[89841, 15], [89841, 15], .contexts []⟩,
    ⟨[89841, 15], [17539, 89841], .contexts [
        ⟨57896, false, false, [], []⟩,
        ⟨57886, true, false, [], [15]⟩,
        ⟨121, false, false, [89839], []⟩,
        ⟨122, false, false, [89839], []⟩,
        ⟨57880, false, false, [], [1]⟩,
        ⟨57880, false, false, [], [1]⟩,
        ⟨57850, true, false, [], [15, 1]⟩,
        ⟨184, false, false, [84717], [1]⟩,
        ⟨185, false, false, [84717], [1]⟩,
        ⟨28293, false, false, [], [5, 1]⟩,
        ⟨57846, false, false, [17539], [1]⟩,
        ⟨57878, false, false, [], [1]⟩,
        ⟨57879, false, false, [], [1]⟩,
        ⟨57862, false, false, [17539], [1]⟩,
        ⟨57881, true, false, [], [89839, 1]⟩,
        ⟨57878, false, false, [], [1]⟩,
        ⟨57879, false, false, [], [1]⟩,
        ⟨57879, false, false, [], [1]⟩,
        ⟨57883, false, false, [17539], []⟩,
        ⟨57894, false, false, [], []⟩,
        ⟨57895, false, false, [], []⟩
      ]⟩,
    ⟨[89843], [89841, 9], .source 44986⟩,
    ⟨[89841, 9], [89843], .contexts [
        ⟨57898, true, false, [], []⟩
      ]⟩,
    ⟨[89843, 9], [89841], .contexts [
        ⟨57899, true, false, [], [9]⟩,
        ⟨46, false, false, [89841], []⟩,
        ⟨57885, false, false, [], []⟩
      ]⟩,
    ⟨[89843], [89843], .contexts []⟩,
    ⟨[89843], [89843], .contexts []⟩,
    ⟨[89841, 9], [89843], .contexts [
        ⟨57899, false, false, [], []⟩,
        ⟨57901, false, false, [], []⟩,
        ⟨57902, false, false, [], []⟩,
        ⟨57902, false, false, [], []⟩
      ]⟩,
    ⟨[17525, 87721], [17525, 87721], .contexts []⟩,
    ⟨[17525, 87721], [17525, 87721], .contexts []⟩,
    ⟨[89843, 1], [89843, 1], .contexts []⟩,
    ⟨[89843, 1], [17525, 87721], .contexts [
        ⟨57906, false, false, [], []⟩,
        ⟨57903, true, false, [], [1]⟩,
        ⟨691, false, false, [89841], []⟩,
        ⟨694, false, false, [89841], []⟩,
        ⟨57884, false, false, [], [9, 1, 9]⟩,
        ⟨57848, false, false, [], [9, 1, 9]⟩,
        ⟨57849, false, false, [], [9, 1, 9]⟩,
        ⟨57849, false, false, [], [9, 1, 9]⟩,
        ⟨57869, false, false, [], [1, 9]⟩,
        ⟨57867, false, false, [], [1, 9]⟩,
        ⟨57868, false, false, [], [1, 9]⟩,
        ⟨57868, false, false, [], [1, 9]⟩,
        ⟨45859, false, false, [17525], [9]⟩,
        ⟨45873, false, false, [17525], []⟩,
        ⟨57904, false, false, [], []⟩,
        ⟨57905, false, false, [], []⟩,
        ⟨45882, false, false, [17525], []⟩
      ]⟩,
    ⟨[89843, 1], [17525, 87721], .contexts [
        ⟨57907, false, false, [], []⟩,
        ⟨28272, true, false, [], [87721]⟩
      ]⟩,
    ⟨[87721, 1], [17527, 89843], .contexts [
        ⟨57908, true, false, [17524], [1]⟩,
        ⟨8, false, false, [17524, 89843], []⟩,
        ⟨28274, true, false, [], [89843]⟩
      ]⟩,
    ⟨[89841, 7, 9], [24413, 89843], .contexts [
        ⟨57890, false, false, [], [9]⟩,
        ⟨57890, false, false, [], [9]⟩,
        ⟨57886, true, false, [], [7, 9]⟩,
        ⟨104, false, false, [89839], [9]⟩,
        ⟨105, false, false, [89839], [9]⟩,
        ⟨57861, false, false, [], [1, 9]⟩,
        ⟨57863, false, false, [], [1, 9]⟩,
        ⟨57864, true, false, [], [89839, 1, 9]⟩,
        ⟨57859, false, false, [], [1, 9]⟩,
        ⟨57860, false, false, [], [1, 9]⟩,
        ⟨57860, false, false, [], [1, 9]⟩,
        ⟨57883, false, false, [24413], [9]⟩,
        ⟨57888, false, false, [], [9]⟩,
        ⟨57889, false, false, [], [9]⟩,
        ⟨57891, false, false, [24413], [9]⟩,
        ⟨57864, true, false, [], [89841, 9]⟩,
        ⟨57888, false, false, [], [9]⟩,
        ⟨57889, false, false, [], [9]⟩,
        ⟨57889, false, false, [], [9]⟩,
        ⟨57899, false, false, [24413], []⟩
      ]⟩,
    ⟨[24413, 89843], [24413, 89843], .contexts []⟩,
    ⟨[89843], [89843], .contexts []⟩,
    ⟨[17539, 89843], [17539, 89843], .contexts []⟩,
    ⟨[17525, 87725], [17525, 87725], .contexts []⟩,
    ⟨[87725, 11], [87725, 11], .contexts []⟩,
    ⟨[17524], [17524], .contexts []⟩,
    ⟨[87725, 11], [17527, 89843], .contexts [
        ⟨57915, false, false, [], []⟩,
        ⟨57914, true, false, [17524], [11]⟩,
        ⟨45902, true, false, [], [11]⟩,
        ⟨45885, true, false, [], [1, 11]⟩,
        ⟨57905, true, false, [17524], [11, 1, 11]⟩,
        ⟨57905, true, false, [17524], [11, 1, 11]⟩,
        ⟨57904, true, false, [17524], [11, 1, 11]⟩,
        ⟨57908, true, false, [17524], [11, 1, 11]⟩,
        ⟨57906, true, false, [17524], [11, 1, 11]⟩,
        ⟨994, false, false, [17524, 89843], []⟩,
        ⟨57912, false, false, [17524], []⟩,
        ⟨57916, true, false, [], [89843]⟩,
        ⟨57916, true, false, [], [89843]⟩,
        ⟨28274, true, false, [], [89843]⟩
      ]⟩,
    ⟨[17527, 89843], [17527, 89843], .contexts []⟩,
    ⟨[17527, 89843], [17527, 89843], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 905. -/
def y322TCIndexRaw905 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[87725, 11, 9, 11, 9, 11], [87343], .contexts [
        ⟨57915, false, false, [], [9, 11, 9, 11]⟩,
        ⟨57917, false, false, [], [9, 11, 9, 11]⟩,
        ⟨57918, false, false, [], [9, 11, 9, 11]⟩,
        ⟨57919, false, false, [], [9, 11, 9, 11]⟩,
        ⟨57919, false, false, [], [9, 11, 9, 11]⟩,
        ⟨57900, false, false, [17527], [11, 9, 11]⟩,
        ⟨57893, false, false, [17527], [9, 11]⟩,
        ⟨28274, false, false, [], [17525, 87339, 9, 11]⟩,
        ⟨41403, false, false, [], [11]⟩,
        ⟨41404, false, false, [], [11]⟩,
        ⟨41405, false, false, [], [11]⟩,
        ⟨41405, false, false, [], [11]⟩,
        ⟨41424, false, false, [], []⟩,
        ⟨41425, false, false, [], []⟩,
        ⟨41426, false, false, [], []⟩,
        ⟨41426, false, false, [], []⟩
      ]⟩,
    ⟨[87343, 9], [87343, 9], .contexts []⟩,
    ⟨[87343, 9], [87725], .contexts [
        ⟨57921, false, false, [], []⟩,
        ⟨57920, true, false, [], [9]⟩,
        ⟨2884, false, false, [87725], []⟩,
        ⟨45910, false, false, [], []⟩,
        ⟨672, true, false, [], [87725]⟩
      ]⟩,
    ⟨[87727, 9], [87727, 9], .contexts []⟩,
    ⟨[87727, 9], [87345], .contexts [
        ⟨57923, false, false, [], []⟩,
        ⟨45917, true, false, [], [9]⟩,
        ⟨45917, true, false, [], [9]⟩,
        ⟨46117, true, false, [], [9]⟩,
        ⟨52867, true, false, [], [9]⟩,
        ⟨45905, true, false, [], [13, 9]⟩,
        ⟨45905, true, false, [], [13, 9]⟩,
        ⟨45904, true, false, [], [13, 9]⟩,
        ⟨57922, true, false, [], [13, 9]⟩,
        ⟨57921, true, false, [], [13, 9]⟩,
        ⟨511, false, false, [87343], []⟩,
        ⟨64, false, false, [87343], []⟩,
        ⟨41444, false, false, [], []⟩,
        ⟨41448, false, false, [], []⟩,
        ⟨672, true, false, [], [87345]⟩
      ]⟩,
    ⟨[87347, 9], [87729], .contexts [
        ⟨41453, true, false, [], [9]⟩,
        ⟨41453, true, false, [], [9]⟩,
        ⟨41452, true, false, [], [9]⟩,
        ⟨41451, true, false, [], [9]⟩,
        ⟨41443, true, false, [], [15, 9]⟩,
        ⟨41443, true, false, [], [15, 9]⟩,
        ⟨41442, true, false, [], [15, 9]⟩,
        ⟨57924, true, false, [], [15, 9]⟩,
        ⟨57923, true, false, [], [15, 9]⟩,
        ⟨935, false, false, [87727], []⟩,
        ⟨52871, false, false, [], []⟩,
        ⟨45921, false, false, [], []⟩,
        ⟨45924, false, false, [], []⟩,
        ⟨672, true, false, [], [87729]⟩
      ]⟩,
    ⟨[89845], [87723, 13], .source 44987⟩,
    ⟨[87723, 13], [89845], .contexts [
        ⟨57926, true, false, [], []⟩
      ]⟩,
    ⟨[89845, 13], [87723], .contexts [
        ⟨57927, true, false, [], [13]⟩,
        ⟨59, false, false, [87723], []⟩,
        ⟨45888, false, false, [], []⟩
      ]⟩,
    ⟨[89845], [89845], .contexts []⟩,
    ⟨[87723, 13], [89845], .contexts [
        ⟨57927, false, false, [], []⟩,
        ⟨57929, false, false, [], []⟩,
        ⟨57929, false, false, [], []⟩
      ]⟩,
    ⟨[23347, 87723], [23347, 87723], .contexts []⟩,
    ⟨[23347, 87723], [23347, 87723], .contexts []⟩,
    ⟨[23347, 89845], [23347, 89845], .contexts []⟩,
    ⟨[23347, 89845], [23347, 89845], .contexts []⟩,
    ⟨[23347, 89845], [23347, 89845], .contexts []⟩,
    ⟨[89845, 3], [89845, 3], .contexts []⟩,
    ⟨[89845], [89845], .contexts []⟩,
    ⟨[23347], [23347], .contexts [
        ⟨13, false, false, [], [23347]⟩
      ]⟩,
    ⟨[23355, 89845], [23355, 89845], .contexts []⟩,
    ⟨[23355, 89845], [23355, 89845], .contexts []⟩,
    ⟨[89845, 7], [89845, 7], .contexts []⟩,
    ⟨[23355], [23355], .contexts [
        ⟨13, false, false, [], [23355]⟩
      ]⟩,
    ⟨[16023, 89845], [16023, 89845], .contexts []⟩,
    ⟨[16023, 89845], [16023, 89845], .contexts []⟩,
    ⟨[89845, 9], [89845, 9], .contexts []⟩,
    ⟨[89847], [89845, 15], .source 44988⟩,
    ⟨[89845, 15], [89847], .contexts [
        ⟨57946, true, false, [], []⟩
      ]⟩,
    ⟨[89847, 15], [89845], .contexts [
        ⟨57947, true, false, [], [15]⟩,
        ⟨1, false, false, [89845], []⟩,
        ⟨57929, false, false, [], []⟩
      ]⟩,
    ⟨[89847], [89847], .contexts []⟩,
    ⟨[89847], [89847], .contexts []⟩,
    ⟨[89845, 15], [89847], .contexts [
        ⟨57947, false, false, [], []⟩,
        ⟨57949, false, false, [], []⟩,
        ⟨57950, false, false, [], []⟩,
        ⟨57950, false, false, [], []⟩
      ]⟩,
    ⟨[23347, 89847], [23347, 89847], .contexts []⟩,
    ⟨[23347, 89847], [23347, 89847], .contexts []⟩,
    ⟨[89845, 3, 15], [23347, 89847], .contexts [
        ⟨57936, false, false, [], [15]⟩,
        ⟨57936, false, false, [], [15]⟩,
        ⟨57930, true, false, [], [3, 15]⟩,
        ⟨63, false, false, [87723], [15]⟩,
        ⟨65, false, false, [87723], [15]⟩,
        ⟨52847, false, false, [], [13, 15]⟩,
        ⟨52849, false, false, [], [13, 15]⟩,
        ⟨57931, false, false, [], [13, 15]⟩,
        ⟨57932, false, false, [], [13, 15]⟩,
        ⟨57932, false, false, [], [13, 15]⟩,
        ⟨57927, false, false, [23347], [15]⟩,
        ⟨57933, false, false, [], [15]⟩,
        ⟨57934, false, false, [], [15]⟩,
        ⟨57935, false, false, [], [15]⟩,
        ⟨57937, false, false, [23347], [15]⟩,
        ⟨57938, true, false, [], [89845, 15]⟩,
        ⟨57933, false, false, [], [15]⟩,
        ⟨57935, false, false, [], [15]⟩,
        ⟨57935, false, false, [], [15]⟩,
        ⟨57947, false, false, [23347], []⟩,
        ⟨57952, false, false, [], []⟩,
        ⟨57953, false, false, [], []⟩
      ]⟩,
    ⟨[23347, 89847], [23347, 89847], .contexts []⟩,
    ⟨[89847], [89847], .contexts []⟩,
    ⟨[89847, 3], [23347, 89847], .contexts [
        ⟨57951, true, false, [], [3]⟩,
        ⟨19, false, false, [89845], []⟩,
        ⟨22, false, false, [89845], []⟩,
        ⟨57954, false, false, [], []⟩,
        ⟨57955, false, false, [], []⟩,
        ⟨57956, false, false, [23347], []⟩,
        ⟨57938, true, false, [], [89847]⟩
      ]⟩,
    ⟨[23355, 89847], [23355, 89847], .contexts []⟩,
    ⟨[23355, 89847], [23355, 89847], .contexts []⟩,
    ⟨[89847, 7], [89847, 7], .contexts []⟩,
    ⟨[89847, 7], [23355, 89847], .contexts [
        ⟨57960, false, false, [], []⟩,
        ⟨57951, true, false, [], [7]⟩,
        ⟨37, false, false, [89845], []⟩,
        ⟨40, false, false, [89845], []⟩,
        ⟨57941, false, false, [], [15]⟩,
        ⟨57941, false, false, [], [15]⟩,
        ⟨57930, true, false, [], [7, 15]⟩,
        ⟨73, false, false, [87723], [15]⟩,
        ⟨74, false, false, [87723], [15]⟩,
        ⟨52862, false, false, [], [13, 15]⟩,
        ⟨57927, false, false, [23355], [15]⟩,
        ⟨57939, false, false, [], [15]⟩,
        ⟨57940, false, false, [], [15]⟩,
        ⟨57937, false, false, [23355], [15]⟩,
        ⟨57942, true, false, [], [89845, 15]⟩,
        ⟨57939, false, false, [], [15]⟩,
        ⟨57940, false, false, [], [15]⟩,
        ⟨57940, false, false, [], [15]⟩,
        ⟨57947, false, false, [23355], []⟩,
        ⟨57958, false, false, [], []⟩,
        ⟨57959, false, false, [], []⟩
      ]⟩,
    ⟨[89847, 7], [23355, 89847], .contexts [
        ⟨57961, false, false, [], []⟩,
        ⟨57956, false, false, [23355], []⟩,
        ⟨57942, true, false, [], [89847]⟩
      ]⟩,
    ⟨[16023, 89847], [16023, 89847], .contexts []⟩,
    ⟨[89845, 9, 15], [16023, 89847], .contexts [
        ⟨57945, false, false, [], [15]⟩,
        ⟨57945, false, false, [], [15]⟩,
        ⟨57930, true, false, [], [9, 15]⟩,
        ⟨77, false, false, [87723], [15]⟩,
        ⟨78, false, false, [87723], [15]⟩,
        ⟨45893, false, false, [], [13, 15]⟩,
        ⟨45896, false, false, [], [13, 15]⟩,
        ⟨45891, false, false, [], [13, 15]⟩,
        ⟨45892, false, false, [], [13, 15]⟩,
        ⟨45892, false, false, [], [13, 15]⟩,
        ⟨57927, false, false, [16023], [15]⟩,
        ⟨57943, false, false, [], [15]⟩,
        ⟨57944, false, false, [], [15]⟩,
        ⟨57937, false, false, [16023], [15]⟩,
        ⟨19784, true, false, [], [89845, 15]⟩,
        ⟨57943, false, false, [], [15]⟩,
        ⟨57944, false, false, [], [15]⟩,
        ⟨57944, false, false, [], [15]⟩,
        ⟨57947, false, false, [16023], []⟩,
        ⟨57963, false, false, [], []⟩
      ]⟩,
    ⟨[89847, 9], [16023, 89847], .contexts [
        ⟨57951, true, false, [], [9]⟩,
        ⟨45, false, false, [89845], []⟩,
        ⟨48, false, false, [89845], []⟩,
        ⟨57964, false, false, [], []⟩,
        ⟨57956, false, false, [16023], []⟩,
        ⟨19784, true, false, [], [89847]⟩
      ]⟩,
    ⟨[727, 89847], [727, 89847], .contexts []⟩,
    ⟨[89847, 13], [727, 89847], .contexts [
        ⟨57951, true, false, [], [13]⟩,
        ⟨259, false, false, [89845], []⟩,
        ⟨262, false, false, [89845], []⟩,
        ⟨57928, false, false, [], [15, 13, 15]⟩,
        ⟨45887, false, false, [], [15, 13, 15]⟩,
        ⟨45888, false, false, [], [15, 13, 15]⟩,
        ⟨45888, false, false, [], [15, 13, 15]⟩,
        ⟨45907, false, false, [], [13, 15]⟩,
        ⟨45897, false, false, [], [13, 15]⟩,
        ⟨45898, false, false, [], [13, 15]⟩,
        ⟨45898, false, false, [], [13, 15]⟩,
        ⟨57927, false, false, [727], [15]⟩,
        ⟨57947, false, false, [727], []⟩,
        ⟨57966, false, false, [], []⟩,
        ⟨57956, false, false, [727], []⟩
      ]⟩,
    ⟨[89847, 13], [727, 89847], .contexts [
        ⟨57967, false, false, [], []⟩,
        ⟨19522, true, false, [], [89847]⟩
      ]⟩,
    ⟨[89849], [89847, 1], .source 44989⟩,
    ⟨[89847, 1], [89849], .contexts [
        ⟨57969, true, false, [], []⟩
      ]⟩,
    ⟨[89849, 1], [89847], .contexts [
        ⟨57970, true, false, [], [1]⟩,
        ⟨8, false, false, [89847], []⟩,
        ⟨57950, false, false, [], []⟩
      ]⟩,
    ⟨[89849], [89849], .contexts []⟩,
    ⟨[89849], [89849], .contexts []⟩,
    ⟨[23355, 89849], [23355, 89849], .contexts []⟩,
    ⟨[23355, 89849], [23355, 89849], .contexts []⟩,
    ⟨[89849, 7], [89849, 7], .contexts []⟩,
    ⟨[89849], [89849], .contexts []⟩,
    ⟨[89849, 7], [23355, 89849], .contexts [
        ⟨57976, false, false, [], []⟩,
        ⟨57973, true, false, [], [7]⟩,
        ⟨57973, true, false, [], [7]⟩,
        ⟨57972, true, false, [], [7]⟩,
        ⟨57970, true, false, [], [7]⟩,
        ⟨104, false, false, [89847], []⟩,
        ⟨105, false, false, [89847], []⟩,
        ⟨57960, false, false, [], [1]⟩,
        ⟨57962, false, false, [], [1]⟩,
        ⟨57958, false, false, [], [1]⟩,
        ⟨57959, false, false, [], [1]⟩,
        ⟨57959, false, false, [], [1]⟩,
        ⟨57970, false, false, [23355], []⟩,
        ⟨57974, false, false, [], []⟩,
        ⟨57975, false, false, [], []⟩,
        ⟨57977, false, false, [23355], []⟩,
        ⟨57942, true, false, [], [89849]⟩
      ]⟩,
    ⟨[89851], [89849, 3], .source 44990⟩,
    ⟨[89849, 3], [89851], .contexts [
        ⟨57979, true, false, [], []⟩
      ]⟩,
    ⟨[89851, 3], [89849], .contexts [
        ⟨57980, true, false, [], [3]⟩,
        ⟨20, false, false, [89849], []⟩,
        ⟨57973, false, false, [], []⟩
      ]⟩,
    ⟨[89851], [89851], .contexts []⟩,
    ⟨[89851], [89851], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 906. -/
def y322TCIndexRaw906 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89849, 3], [89851], .contexts [
        ⟨57980, false, false, [], []⟩,
        ⟨57982, false, false, [], []⟩,
        ⟨57983, false, false, [], []⟩,
        ⟨57983, false, false, [], []⟩
      ]⟩,
    ⟨[23347, 89849], [23347, 89849], .contexts []⟩,
    ⟨[23347, 89849], [23347, 89849], .contexts []⟩,
    ⟨[23347, 89849], [23347, 89849], .contexts []⟩,
    ⟨[23347, 89851], [23347, 89851], .contexts []⟩,
    ⟨[23347, 89851], [23347, 89851], .contexts []⟩,
    ⟨[23347, 89851], [23347, 89851], .contexts []⟩,
    ⟨[89851, 1], [89851, 1], .contexts []⟩,
    ⟨[89851], [89851], .contexts []⟩,
    ⟨[89851, 1], [23347, 89851], .contexts [
        ⟨57991, false, false, [], []⟩,
        ⟨57984, true, false, [], [1]⟩,
        ⟨130, false, false, [89849], []⟩,
        ⟨133, false, false, [89849], []⟩,
        ⟨57971, false, false, [], [3, 1, 3]⟩,
        ⟨57949, false, false, [], [3, 1, 3]⟩,
        ⟨57950, false, false, [], [3, 1, 3]⟩,
        ⟨57950, false, false, [], [3, 1, 3]⟩,
        ⟨57957, false, false, [], [1, 3]⟩,
        ⟨57952, false, false, [], [1, 3]⟩,
        ⟨57955, false, false, [], [1, 3]⟩,
        ⟨57955, false, false, [], [1, 3]⟩,
        ⟨57970, false, false, [23347], [3]⟩,
        ⟨57985, false, false, [], [3]⟩,
        ⟨57986, false, false, [], [3]⟩,
        ⟨57987, false, false, [], [3]⟩,
        ⟨57980, false, false, [23347], []⟩,
        ⟨57988, false, false, [], []⟩,
        ⟨57989, false, false, [], []⟩,
        ⟨57990, false, false, [], []⟩,
        ⟨57992, false, false, [23347], []⟩
      ]⟩,
    ⟨[89851, 1], [23347, 89851], .contexts [
        ⟨57993, false, false, [], []⟩,
        ⟨57938, true, false, [], [89851]⟩
      ]⟩,
    ⟨[89849, 7], [23355, 89849], .contexts [
        ⟨57976, false, false, [], []⟩,
        ⟨57978, false, false, [], []⟩,
        ⟨57974, false, false, [], []⟩,
        ⟨57975, false, false, [], []⟩,
        ⟨57975, false, false, [], []⟩
      ]⟩,
    ⟨[23355, 89851], [23355, 89851], .contexts []⟩,
    ⟨[89853], [89851, 5], .source 44991⟩,
    ⟨[89851, 5], [89853], .contexts [
        ⟨57997, true, false, [], []⟩
      ]⟩,
    ⟨[89853, 5], [89851], .contexts [
        ⟨57998, true, false, [], [5]⟩,
        ⟨28, false, false, [89851], []⟩,
        ⟨57983, false, false, [], []⟩
      ]⟩,
    ⟨[89853], [89853], .contexts []⟩,
    ⟨[89853], [89853], .contexts []⟩,
    ⟨[89851, 1], [23347, 89851], .contexts [
        ⟨57991, false, false, [], []⟩,
        ⟨57994, false, false, [], []⟩,
        ⟨57988, false, false, [], []⟩,
        ⟨57990, false, false, [], []⟩,
        ⟨57990, false, false, [], []⟩
      ]⟩,
    ⟨[23347, 89853], [23347, 89853], .contexts []⟩,
    ⟨[23347, 89853], [23347, 89853], .contexts []⟩,
    ⟨[89853], [89853], .contexts []⟩,
    ⟨[89853, 1], [23347, 89853], .contexts [
        ⟨58001, true, false, [], [1]⟩,
        ⟨58001, true, false, [], [1]⟩,
        ⟨58000, true, false, [], [1]⟩,
        ⟨57998, true, false, [], [1]⟩,
        ⟨161, false, false, [89851], []⟩,
        ⟨162, false, false, [89851], []⟩,
        ⟨58002, false, false, [], [5]⟩,
        ⟨57998, false, false, [23347], []⟩,
        ⟨58003, false, false, [], []⟩,
        ⟨58004, false, false, [], []⟩,
        ⟨58005, false, false, [23347], []⟩,
        ⟨57938, true, false, [], [89853]⟩
      ]⟩,
    ⟨[89855], [89853, 9], .source 44992⟩,
    ⟨[89853, 9], [89855], .contexts [
        ⟨58007, true, false, [], []⟩
      ]⟩,
    ⟨[89855, 9], [89853], .contexts [
        ⟨58008, true, false, [], [9]⟩,
        ⟨46, false, false, [89853], []⟩,
        ⟨58001, false, false, [], []⟩
      ]⟩,
    ⟨[89857], [89855, 11], .source 44993⟩,
    ⟨[89855, 11], [89857], .contexts [
        ⟨58010, true, false, [], []⟩
      ]⟩,
    ⟨[89855], [89855], .contexts []⟩,
    ⟨[89859], [89857, 1], .source 44994⟩,
    ⟨[89857, 1], [89859], .contexts [
        ⟨58013, true, false, [], []⟩
      ]⟩,
    ⟨[89857], [89857], .contexts []⟩,
    ⟨[89859, 1], [89857], .contexts [
        ⟨58014, true, false, [], [1]⟩,
        ⟨8, false, false, [89857], []⟩,
        ⟨58015, false, false, [], []⟩
      ]⟩,
    ⟨[89861], [89859, 13], .source 44995⟩,
    ⟨[89859, 13], [89861], .contexts [
        ⟨58017, true, false, [], []⟩
      ]⟩,
    ⟨[89859], [89859], .contexts []⟩,
    ⟨[89863], [89861, 15], .source 44996⟩,
    ⟨[89861, 15], [89863], .contexts [
        ⟨58020, true, false, [], []⟩
      ]⟩,
    ⟨[89861], [89861], .contexts []⟩,
    ⟨[89863, 15], [89861], .contexts [
        ⟨58021, true, false, [], [15]⟩,
        ⟨1, false, false, [89861], []⟩,
        ⟨58022, false, false, [], []⟩
      ]⟩,
    ⟨[89865], [89863, 1], .source 44997⟩,
    ⟨[89863, 1], [89865], .contexts [
        ⟨58024, true, false, [], []⟩
      ]⟩,
    ⟨[89863], [89863], .contexts []⟩,
    ⟨[89865, 1], [89863], .contexts [
        ⟨58025, true, false, [], [1]⟩,
        ⟨8, false, false, [89863], []⟩,
        ⟨58026, false, false, [], []⟩
      ]⟩,
    ⟨[89867], [89865, 3], .source 44998⟩,
    ⟨[89865, 3], [89867], .contexts [
        ⟨58028, true, false, [], []⟩
      ]⟩,
    ⟨[89865], [89865], .contexts []⟩,
    ⟨[89867, 3], [89865], .contexts [
        ⟨58029, true, false, [], [3]⟩,
        ⟨20, false, false, [89865], []⟩,
        ⟨58030, false, false, [], []⟩
      ]⟩,
    ⟨[89869], [89867, 5], .source 44999⟩,
    ⟨[89867, 5], [89869], .contexts [
        ⟨58032, true, false, [], []⟩
      ]⟩,
    ⟨[89867], [89867], .contexts []⟩,
    ⟨[89869, 5], [89867], .contexts [
        ⟨58033, true, false, [], [5]⟩,
        ⟨28, false, false, [89867], []⟩,
        ⟨58034, false, false, [], []⟩
      ]⟩,
    ⟨[89871], [89869, 1], .source 45000⟩,
    ⟨[89869, 1], [89871], .contexts [
        ⟨58036, true, false, [], []⟩
      ]⟩,
    ⟨[89869], [89869], .contexts []⟩,
    ⟨[89871, 1], [89869], .contexts [
        ⟨58037, true, false, [], [1]⟩,
        ⟨8, false, false, [89869], []⟩,
        ⟨58038, false, false, [], []⟩
      ]⟩,
    ⟨[89873], [89871, 9], .source 45001⟩,
    ⟨[89871, 9], [89873], .contexts [
        ⟨58040, true, false, [], []⟩
      ]⟩,
    ⟨[89871], [89871], .contexts []⟩,
    ⟨[89873, 9], [89871], .contexts [
        ⟨58041, true, false, [], [9]⟩,
        ⟨46, false, false, [89871], []⟩,
        ⟨58042, false, false, [], []⟩
      ]⟩,
    ⟨[89875], [89873, 11], .source 45002⟩,
    ⟨[89873, 11], [89875], .contexts [
        ⟨58044, true, false, [], []⟩
      ]⟩,
    ⟨[89873], [89873], .contexts []⟩,
    ⟨[89875, 11], [89873], .contexts [
        ⟨58045, true, false, [], [11]⟩,
        ⟨53, false, false, [89873], []⟩,
        ⟨58046, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 907. -/
def y322TCIndexRaw907 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89877], [89875, 1], .source 45003⟩,
    ⟨[89875, 1], [89877], .contexts [
        ⟨58048, true, false, [], []⟩
      ]⟩,
    ⟨[89875], [89875], .contexts []⟩,
    ⟨[89877, 1], [89875], .contexts [
        ⟨58049, true, false, [], [1]⟩,
        ⟨8, false, false, [89875], []⟩,
        ⟨58050, false, false, [], []⟩
      ]⟩,
    ⟨[89879], [89877, 13], .source 45004⟩,
    ⟨[89877], [89877], .contexts []⟩,
    ⟨[89879, 13], [89877], .contexts [
        ⟨58052, false, false, [], [13]⟩,
        ⟨59, false, false, [89877], []⟩,
        ⟨58053, false, false, [], []⟩
      ]⟩,
    ⟨[89881], [89879, 15], .source 45005⟩,
    ⟨[89879], [89879], .contexts []⟩,
    ⟨[89881, 15], [89879], .contexts [
        ⟨58055, false, false, [], [15]⟩,
        ⟨1, false, false, [89879], []⟩,
        ⟨58056, false, false, [], []⟩
      ]⟩,
    ⟨[89883], [89881, 1], .source 45006⟩,
    ⟨[89881], [89881], .contexts []⟩,
    ⟨[89883, 1], [89881], .contexts [
        ⟨58058, false, false, [], [1]⟩,
        ⟨8, false, false, [89881], []⟩,
        ⟨58059, false, false, [], []⟩
      ]⟩,
    ⟨[89885], [89883, 3], .source 45007⟩,
    ⟨[89883], [89883], .contexts []⟩,
    ⟨[89885, 3], [89883], .contexts [
        ⟨58061, false, false, [], [3]⟩,
        ⟨20, false, false, [89883], []⟩,
        ⟨58062, false, false, [], []⟩
      ]⟩,
    ⟨[89887], [89885, 5], .source 45008⟩,
    ⟨[89885], [89885], .contexts []⟩,
    ⟨[89887, 5], [89885], .contexts [
        ⟨58064, false, false, [], [5]⟩,
        ⟨28, false, false, [89885], []⟩,
        ⟨58065, false, false, [], []⟩
      ]⟩,
    ⟨[89889], [89887, 1], .source 45009⟩,
    ⟨[89887, 1], [89889], .contexts [
        ⟨58067, true, false, [], []⟩
      ]⟩,
    ⟨[89887], [89887], .contexts []⟩,
    ⟨[89889, 1], [89887], .contexts [
        ⟨58068, true, false, [], [1]⟩,
        ⟨8, false, false, [89887], []⟩,
        ⟨58069, false, false, [], []⟩
      ]⟩,
    ⟨[89891], [89889, 9], .source 45010⟩,
    ⟨[89889], [89889], .contexts []⟩,
    ⟨[89891, 9], [89889], .contexts [
        ⟨58071, false, false, [], [9]⟩,
        ⟨46, false, false, [89889], []⟩,
        ⟨58072, false, false, [], []⟩
      ]⟩,
    ⟨[89893], [89891, 11], .source 45011⟩,
    ⟨[89891], [89891], .contexts []⟩,
    ⟨[89893, 11], [89891], .contexts [
        ⟨58074, false, false, [], [11]⟩,
        ⟨53, false, false, [89891], []⟩,
        ⟨58075, false, false, [], []⟩
      ]⟩,
    ⟨[89895], [89893, 1], .source 45012⟩,
    ⟨[89893, 1], [89895], .contexts [
        ⟨58077, true, false, [], []⟩
      ]⟩,
    ⟨[89893], [89893], .contexts []⟩,
    ⟨[89895, 1], [89893], .contexts [
        ⟨58078, true, false, [], [1]⟩,
        ⟨8, false, false, [89893], []⟩,
        ⟨58079, false, false, [], []⟩
      ]⟩,
    ⟨[89897], [89895, 13], .source 45013⟩,
    ⟨[89895, 13], [89897], .contexts [
        ⟨58081, true, false, [], []⟩
      ]⟩,
    ⟨[89895], [89895], .contexts []⟩,
    ⟨[89897, 13], [89895], .contexts [
        ⟨58082, true, false, [], [13]⟩,
        ⟨59, false, false, [89895], []⟩,
        ⟨58083, false, false, [], []⟩
      ]⟩,
    ⟨[89899], [89897, 15], .source 45014⟩,
    ⟨[89897, 15], [89899], .contexts [
        ⟨58085, true, false, [], []⟩
      ]⟩,
    ⟨[89897], [89897], .contexts []⟩,
    ⟨[89899, 15], [89897], .contexts [
        ⟨58086, true, false, [], [15]⟩,
        ⟨1, false, false, [89897], []⟩,
        ⟨58087, false, false, [], []⟩
      ]⟩,
    ⟨[89901], [89899, 1], .source 45015⟩,
    ⟨[89899, 1], [89901], .contexts [
        ⟨58089, true, false, [], []⟩
      ]⟩,
    ⟨[89899], [89899], .contexts []⟩,
    ⟨[89901, 1], [89899], .contexts [
        ⟨58090, true, false, [], [1]⟩,
        ⟨8, false, false, [89899], []⟩,
        ⟨58091, false, false, [], []⟩
      ]⟩,
    ⟨[89903], [89901, 3], .source 45016⟩,
    ⟨[89901, 3], [89903], .contexts [
        ⟨58093, true, false, [], []⟩
      ]⟩,
    ⟨[89901], [89901], .contexts []⟩,
    ⟨[89903, 3], [89901], .contexts [
        ⟨58094, true, false, [], [3]⟩,
        ⟨20, false, false, [89901], []⟩,
        ⟨58095, false, false, [], []⟩
      ]⟩,
    ⟨[89905], [89903, 5], .source 45017⟩,
    ⟨[89903, 5], [89905], .contexts [
        ⟨58097, true, false, [], []⟩
      ]⟩,
    ⟨[89903], [89903], .contexts []⟩,
    ⟨[89905, 5], [89903], .contexts [
        ⟨58098, true, false, [], [5]⟩,
        ⟨28, false, false, [89903], []⟩,
        ⟨58099, false, false, [], []⟩
      ]⟩,
    ⟨[89907], [89905, 1], .source 45018⟩,
    ⟨[89905, 1], [89907], .contexts [
        ⟨58101, true, false, [], []⟩
      ]⟩,
    ⟨[89905], [89905], .contexts []⟩,
    ⟨[89907, 1], [89905], .contexts [
        ⟨58102, true, false, [], [1]⟩,
        ⟨8, false, false, [89905], []⟩,
        ⟨58103, false, false, [], []⟩
      ]⟩,
    ⟨[89909], [89907, 9], .source 45019⟩,
    ⟨[89907, 9], [89909], .contexts [
        ⟨58105, true, false, [], []⟩
      ]⟩,
    ⟨[89907], [89907], .contexts []⟩,
    ⟨[89909, 9], [89907], .contexts [
        ⟨58106, true, false, [], [9]⟩,
        ⟨46, false, false, [89907], []⟩,
        ⟨58107, false, false, [], []⟩
      ]⟩,
    ⟨[89911], [89909, 11], .source 45020⟩,
    ⟨[89909], [89909], .contexts []⟩,
    ⟨[89911, 11], [89909], .contexts [
        ⟨58109, false, false, [], [11]⟩,
        ⟨53, false, false, [89909], []⟩,
        ⟨58110, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 908. -/
def y322TCIndexRaw908 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89913], [89911, 1], .source 45021⟩,
    ⟨[89911, 1], [89913], .contexts [
        ⟨58112, true, false, [], []⟩
      ]⟩,
    ⟨[89911], [89911], .contexts []⟩,
    ⟨[89913, 1], [89911], .contexts [
        ⟨58113, true, false, [], [1]⟩,
        ⟨8, false, false, [89911], []⟩,
        ⟨58114, false, false, [], []⟩
      ]⟩,
    ⟨[89915], [89913, 13], .source 45022⟩,
    ⟨[89913], [89913], .contexts []⟩,
    ⟨[89915, 13], [89913], .contexts [
        ⟨58116, false, false, [], [13]⟩,
        ⟨59, false, false, [89913], []⟩,
        ⟨58117, false, false, [], []⟩
      ]⟩,
    ⟨[89917], [89915, 15], .source 45023⟩,
    ⟨[89915], [89915], .contexts []⟩,
    ⟨[89917, 15], [89915], .contexts [
        ⟨58119, false, false, [], [15]⟩,
        ⟨1, false, false, [89915], []⟩,
        ⟨58120, false, false, [], []⟩
      ]⟩,
    ⟨[89919], [89917, 1], .source 45024⟩,
    ⟨[89917], [89917], .contexts []⟩,
    ⟨[89919, 1], [89917], .contexts [
        ⟨58122, false, false, [], [1]⟩,
        ⟨8, false, false, [89917], []⟩,
        ⟨58123, false, false, [], []⟩
      ]⟩,
    ⟨[89921], [89919, 3], .source 45025⟩,
    ⟨[89919], [89919], .contexts []⟩,
    ⟨[89921, 3], [89919], .contexts [
        ⟨58125, false, false, [], [3]⟩,
        ⟨20, false, false, [89919], []⟩,
        ⟨58126, false, false, [], []⟩
      ]⟩,
    ⟨[89923], [89921, 5], .source 45026⟩,
    ⟨[89921], [89921], .contexts []⟩,
    ⟨[89923, 5], [89921], .contexts [
        ⟨58128, false, false, [], [5]⟩,
        ⟨28, false, false, [89921], []⟩,
        ⟨58129, false, false, [], []⟩
      ]⟩,
    ⟨[89925], [89923, 1], .source 45027⟩,
    ⟨[89923], [89923], .contexts []⟩,
    ⟨[89925, 1], [89923], .contexts [
        ⟨58131, false, false, [], [1]⟩,
        ⟨8, false, false, [89923], []⟩,
        ⟨58132, false, false, [], []⟩
      ]⟩,
    ⟨[89927], [89925, 9], .source 45028⟩,
    ⟨[89925], [89925], .contexts []⟩,
    ⟨[89927, 9], [89925], .contexts [
        ⟨58134, false, false, [], [9]⟩,
        ⟨46, false, false, [89925], []⟩,
        ⟨58135, false, false, [], []⟩
      ]⟩,
    ⟨[89929], [89927, 11], .source 45029⟩,
    ⟨[89927, 11], [89929], .contexts [
        ⟨58137, true, false, [], []⟩
      ]⟩,
    ⟨[89927], [89927], .contexts []⟩,
    ⟨[89929, 11], [89927], .contexts [
        ⟨58138, true, false, [], [11]⟩,
        ⟨53, false, false, [89927], []⟩,
        ⟨58139, false, false, [], []⟩
      ]⟩,
    ⟨[89931], [89929, 1], .source 45030⟩,
    ⟨[89929, 1], [89931], .contexts [
        ⟨58141, true, false, [], []⟩
      ]⟩,
    ⟨[89929], [89929], .contexts []⟩,
    ⟨[89931, 1], [89929], .contexts [
        ⟨58142, true, false, [], [1]⟩,
        ⟨8, false, false, [89929], []⟩,
        ⟨58143, false, false, [], []⟩
      ]⟩,
    ⟨[89933], [89931, 13], .source 45031⟩,
    ⟨[89931, 13], [89933], .contexts [
        ⟨58145, true, false, [], []⟩
      ]⟩,
    ⟨[89931], [89931], .contexts []⟩,
    ⟨[89933, 13], [89931], .contexts [
        ⟨58146, true, false, [], [13]⟩,
        ⟨59, false, false, [89931], []⟩,
        ⟨58147, false, false, [], []⟩
      ]⟩,
    ⟨[89935], [89933, 15], .source 45032⟩,
    ⟨[89933, 15], [89935], .contexts [
        ⟨58149, true, false, [], []⟩
      ]⟩,
    ⟨[89933], [89933], .contexts []⟩,
    ⟨[89935, 15], [89933], .contexts [
        ⟨58150, true, false, [], [15]⟩,
        ⟨1, false, false, [89933], []⟩,
        ⟨58151, false, false, [], []⟩
      ]⟩,
    ⟨[89937], [89935, 1], .source 45033⟩,
    ⟨[89935, 1], [89937], .contexts [
        ⟨58153, true, false, [], []⟩
      ]⟩,
    ⟨[89935], [89935], .contexts []⟩,
    ⟨[89937, 1], [89935], .contexts [
        ⟨58154, true, false, [], [1]⟩,
        ⟨8, false, false, [89935], []⟩,
        ⟨58155, false, false, [], []⟩
      ]⟩,
    ⟨[89939], [89937, 3], .source 45034⟩,
    ⟨[89937, 3], [89939], .contexts [
        ⟨58157, true, false, [], []⟩
      ]⟩,
    ⟨[89937], [89937], .contexts []⟩,
    ⟨[89939, 3], [89937], .contexts [
        ⟨58158, true, false, [], [3]⟩,
        ⟨20, false, false, [89937], []⟩,
        ⟨58159, false, false, [], []⟩
      ]⟩,
    ⟨[89941], [89939, 5], .source 45035⟩,
    ⟨[89939], [89939], .contexts []⟩,
    ⟨[89941, 5], [89939], .contexts [
        ⟨58161, false, false, [], [5]⟩,
        ⟨28, false, false, [89939], []⟩,
        ⟨58162, false, false, [], []⟩
      ]⟩,
    ⟨[89943], [89941, 1], .source 45036⟩,
    ⟨[89941, 1], [89943], .contexts [
        ⟨58164, true, false, [], []⟩
      ]⟩,
    ⟨[89941], [89941], .contexts []⟩,
    ⟨[89943, 1], [89941], .contexts [
        ⟨58165, true, false, [], [1]⟩,
        ⟨8, false, false, [89941], []⟩,
        ⟨58166, false, false, [], []⟩
      ]⟩,
    ⟨[89945], [89943, 9], .source 45037⟩,
    ⟨[89943, 9], [89945], .contexts [
        ⟨58168, true, false, [], []⟩
      ]⟩,
    ⟨[89943], [89943], .contexts []⟩,
    ⟨[89945, 9], [89943], .contexts [
        ⟨58169, true, false, [], [9]⟩,
        ⟨46, false, false, [89943], []⟩,
        ⟨58170, false, false, [], []⟩
      ]⟩,
    ⟨[89947], [89945, 11], .source 45038⟩,
    ⟨[89945, 11], [89947], .contexts [
        ⟨58172, true, false, [], []⟩
      ]⟩,
    ⟨[89945], [89945], .contexts []⟩,
    ⟨[89947, 11], [89945], .contexts [
        ⟨58173, true, false, [], [11]⟩,
        ⟨53, false, false, [89945], []⟩,
        ⟨58174, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 909. -/
def y322TCIndexRaw909 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89949], [89947, 1], .source 45039⟩,
    ⟨[89947], [89947], .contexts []⟩,
    ⟨[89949, 1], [89947], .contexts [
        ⟨58176, false, false, [], [1]⟩,
        ⟨8, false, false, [89947], []⟩,
        ⟨58177, false, false, [], []⟩
      ]⟩,
    ⟨[89951], [89949, 13], .source 45040⟩,
    ⟨[89949], [89949], .contexts []⟩,
    ⟨[89951, 13], [89949], .contexts [
        ⟨58179, false, false, [], [13]⟩,
        ⟨59, false, false, [89949], []⟩,
        ⟨58180, false, false, [], []⟩
      ]⟩,
    ⟨[89953], [89951, 15], .source 45041⟩,
    ⟨[89951], [89951], .contexts []⟩,
    ⟨[89953, 15], [89951], .contexts [
        ⟨58182, false, false, [], [15]⟩,
        ⟨1, false, false, [89951], []⟩,
        ⟨58183, false, false, [], []⟩
      ]⟩,
    ⟨[89955], [89953, 1], .source 45042⟩,
    ⟨[89953], [89953], .contexts []⟩,
    ⟨[89955, 1], [89953], .contexts [
        ⟨58185, false, false, [], [1]⟩,
        ⟨8, false, false, [89953], []⟩,
        ⟨58186, false, false, [], []⟩
      ]⟩,
    ⟨[89957], [89955, 3], .source 45043⟩,
    ⟨[89955], [89955], .contexts []⟩,
    ⟨[89957, 3], [89955], .contexts [
        ⟨58188, false, false, [], [3]⟩,
        ⟨20, false, false, [89955], []⟩,
        ⟨58189, false, false, [], []⟩
      ]⟩,
    ⟨[89959], [89957, 5], .source 45044⟩,
    ⟨[89957, 5], [89959], .contexts [
        ⟨58191, true, false, [], []⟩
      ]⟩,
    ⟨[89957], [89957], .contexts []⟩,
    ⟨[89959, 5], [89957], .contexts [
        ⟨58192, true, false, [], [5]⟩,
        ⟨28, false, false, [89957], []⟩,
        ⟨58193, false, false, [], []⟩
      ]⟩,
    ⟨[89961], [89959, 1], .source 45045⟩,
    ⟨[89959, 1], [89961], .contexts [
        ⟨58195, true, false, [], []⟩
      ]⟩,
    ⟨[89959], [89959], .contexts []⟩,
    ⟨[89961, 1], [89959], .contexts [
        ⟨58196, true, false, [], [1]⟩,
        ⟨8, false, false, [89959], []⟩,
        ⟨58197, false, false, [], []⟩
      ]⟩,
    ⟨[89963], [89961, 9], .source 45046⟩,
    ⟨[89961, 9], [89963], .contexts [
        ⟨58199, true, false, [], []⟩
      ]⟩,
    ⟨[89961], [89961], .contexts []⟩,
    ⟨[89963, 9], [89961], .contexts [
        ⟨58200, true, false, [], [9]⟩,
        ⟨46, false, false, [89961], []⟩,
        ⟨58201, false, false, [], []⟩
      ]⟩,
    ⟨[89965], [89963, 11], .source 45047⟩,
    ⟨[89963], [89963], .contexts []⟩,
    ⟨[89965, 11], [89963], .contexts [
        ⟨58203, false, false, [], [11]⟩,
        ⟨53, false, false, [89963], []⟩,
        ⟨58204, false, false, [], []⟩
      ]⟩,
    ⟨[89967], [89965, 1], .source 45048⟩,
    ⟨[89965], [89965], .contexts []⟩,
    ⟨[89967, 1], [89965], .contexts [
        ⟨58206, false, false, [], [1]⟩,
        ⟨8, false, false, [89965], []⟩,
        ⟨58207, false, false, [], []⟩
      ]⟩,
    ⟨[89969], [89967, 13], .source 45049⟩,
    ⟨[89967], [89967], .contexts []⟩,
    ⟨[89969, 13], [89967], .contexts [
        ⟨58209, false, false, [], [13]⟩,
        ⟨59, false, false, [89967], []⟩,
        ⟨58210, false, false, [], []⟩
      ]⟩,
    ⟨[89971], [89969, 15], .source 45050⟩,
    ⟨[89969, 15], [89971], .contexts [
        ⟨58212, true, false, [], []⟩
      ]⟩,
    ⟨[89969], [89969], .contexts []⟩,
    ⟨[89971, 15], [89969], .contexts [
        ⟨58213, true, false, [], [15]⟩,
        ⟨1, false, false, [89969], []⟩,
        ⟨58214, false, false, [], []⟩
      ]⟩,
    ⟨[89971], [89971], .contexts []⟩,
    ⟨[89971], [89971], .contexts []⟩,
    ⟨[89967], [89967], .contexts []⟩,
    ⟨[89965], [89965], .contexts []⟩,
    ⟨[89963], [89963], .contexts []⟩,
    ⟨[89961], [89961], .contexts []⟩,
    ⟨[89961, 1], [89959], .contexts [
        ⟨58198, false, false, [], []⟩
      ]⟩,
    ⟨[89959], [89959], .contexts []⟩,
    ⟨[89969, 13, 1, 11, 9, 1], [89959], .contexts [
        ⟨58211, false, false, [], [1, 11, 9, 1]⟩,
        ⟨58218, false, false, [], [1, 11, 9, 1]⟩,
        ⟨58210, false, false, [], [1, 11, 9, 1]⟩,
        ⟨58210, false, false, [], [1, 11, 9, 1]⟩,
        ⟨58208, false, false, [], [11, 9, 1]⟩,
        ⟨58219, false, false, [], [11, 9, 1]⟩,
        ⟨58207, false, false, [], [11, 9, 1]⟩,
        ⟨58207, false, false, [], [11, 9, 1]⟩,
        ⟨58205, false, false, [], [9, 1]⟩,
        ⟨58220, false, false, [], [9, 1]⟩,
        ⟨58204, false, false, [], [9, 1]⟩,
        ⟨58204, false, false, [], [9, 1]⟩,
        ⟨58202, false, false, [], [1]⟩,
        ⟨58221, false, false, [], [1]⟩,
        ⟨58201, false, false, [], [1]⟩,
        ⟨58201, false, false, [], [1]⟩,
        ⟨58222, false, false, [], []⟩,
        ⟨58223, false, false, [], []⟩,
        ⟨58197, false, false, [], []⟩,
        ⟨58197, false, false, [], []⟩
      ]⟩,
    ⟨[89959, 5], [89957], .contexts [
        ⟨58194, false, false, [], []⟩
      ]⟩,
    ⟨[89957], [89957], .contexts []⟩,
    ⟨[89957, 3], [89955], .contexts [
        ⟨58190, false, false, [], []⟩
      ]⟩,
    ⟨[89955], [89955], .contexts []⟩,
    ⟨[89955, 1], [89953], .contexts [
        ⟨58187, false, false, [], []⟩
      ]⟩,
    ⟨[89953], [89953], .contexts []⟩,
    ⟨[89951, 13], [89949], .contexts [
        ⟨58181, false, false, [], []⟩
      ]⟩,
    ⟨[89949], [89949], .contexts []⟩,
    ⟨[89969, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13], [89949], .contexts [
        ⟨58224, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨58225, false, false, [], [3, 1, 15, 13]⟩,
        ⟨58226, false, false, [], [3, 1, 15, 13]⟩,
        ⟨58193, false, false, [], [3, 1, 15, 13]⟩,
        ⟨58193, false, false, [], [3, 1, 15, 13]⟩,
        ⟨58227, false, false, [], [1, 15, 13]⟩,
        ⟨58228, false, false, [], [1, 15, 13]⟩,
        ⟨58189, false, false, [], [1, 15, 13]⟩,
        ⟨58189, false, false, [], [1, 15, 13]⟩,
        ⟨58229, false, false, [], [15, 13]⟩,
        ⟨58230, false, false, [], [15, 13]⟩,
        ⟨58186, false, false, [], [15, 13]⟩,
        ⟨58186, false, false, [], [15, 13]⟩,
        ⟨58184, false, false, [], [13]⟩,
        ⟨58183, false, false, [], [13]⟩,
        ⟨58183, false, false, [], [13]⟩,
        ⟨58231, false, false, [], []⟩,
        ⟨58232, false, false, [], []⟩,
        ⟨58180, false, false, [], []⟩,
        ⟨58180, false, false, [], []⟩
      ]⟩,
    ⟨[89949, 1], [89947], .contexts [
        ⟨58178, false, false, [], []⟩
      ]⟩,
    ⟨[89947], [89947], .contexts []⟩,
    ⟨[89947, 11], [89945], .contexts [
        ⟨58175, false, false, [], []⟩
      ]⟩,
    ⟨[89945], [89945], .contexts []⟩,
    ⟨[89945, 9], [89943], .contexts [
        ⟨58171, false, false, [], []⟩
      ]⟩,
    ⟨[89943], [89943], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 910. -/
def y322TCIndexRaw910 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89943, 1], [89941], .contexts [
        ⟨58167, false, false, [], []⟩
      ]⟩,
    ⟨[89941], [89941], .contexts []⟩,
    ⟨[89941, 5], [89939], .contexts [
        ⟨58163, false, false, [], []⟩
      ]⟩,
    ⟨[89939], [89939], .contexts []⟩,
    ⟨[
      89969, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5
    ], [89939], .contexts [
        ⟨58233, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨58234, false, false, [], [11, 9, 1, 5]⟩,
        ⟨58235, false, false, [], [11, 9, 1, 5]⟩,
        ⟨58177, false, false, [], [11, 9, 1, 5]⟩,
        ⟨58177, false, false, [], [11, 9, 1, 5]⟩,
        ⟨58236, false, false, [], [9, 1, 5]⟩,
        ⟨58237, false, false, [], [9, 1, 5]⟩,
        ⟨58174, false, false, [], [9, 1, 5]⟩,
        ⟨58174, false, false, [], [9, 1, 5]⟩,
        ⟨58238, false, false, [], [1, 5]⟩,
        ⟨58239, false, false, [], [1, 5]⟩,
        ⟨58170, false, false, [], [1, 5]⟩,
        ⟨58170, false, false, [], [1, 5]⟩,
        ⟨58240, false, false, [], [5]⟩,
        ⟨58241, false, false, [], [5]⟩,
        ⟨58166, false, false, [], [5]⟩,
        ⟨58166, false, false, [], [5]⟩,
        ⟨58242, false, false, [], []⟩,
        ⟨58243, false, false, [], []⟩,
        ⟨58162, false, false, [], []⟩,
        ⟨58162, false, false, [], []⟩
      ]⟩,
    ⟨[89937], [89937], .contexts []⟩,
    ⟨[89937, 1], [89935], .contexts [
        ⟨58156, false, false, [], []⟩
      ]⟩,
    ⟨[89933], [89933], .contexts []⟩,
    ⟨[89933, 13], [89931], .contexts [
        ⟨58148, false, false, [], []⟩
      ]⟩,
    ⟨[89931], [89931], .contexts []⟩,
    ⟨[89929], [89929], .contexts []⟩,
    ⟨[
      89969, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [89929], .contexts [
        ⟨58244, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨58160, false, false, [], [1, 15, 13, 1]⟩,
        ⟨58245, false, false, [], [1, 15, 13, 1]⟩,
        ⟨58159, false, false, [], [1, 15, 13, 1]⟩,
        ⟨58159, false, false, [], [1, 15, 13, 1]⟩,
        ⟨58246, false, false, [], [15, 13, 1]⟩,
        ⟨58155, false, false, [], [15, 13, 1]⟩,
        ⟨58155, false, false, [], [15, 13, 1]⟩,
        ⟨58152, false, false, [], [13, 1]⟩,
        ⟨58247, false, false, [], [13, 1]⟩,
        ⟨58151, false, false, [], [13, 1]⟩,
        ⟨58151, false, false, [], [13, 1]⟩,
        ⟨58248, false, false, [], [1]⟩,
        ⟨58249, false, false, [], [1]⟩,
        ⟨58147, false, false, [], [1]⟩,
        ⟨58147, false, false, [], [1]⟩,
        ⟨58144, false, false, [], []⟩,
        ⟨58250, false, false, [], []⟩,
        ⟨58143, false, false, [], []⟩,
        ⟨58143, false, false, [], []⟩
      ]⟩,
    ⟨[89927], [89927], .contexts []⟩,
    ⟨[89923], [89923], .contexts []⟩,
    ⟨[89921], [89921], .contexts []⟩,
    ⟨[89919], [89919], .contexts []⟩,
    ⟨[
      89969, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3
    ], [89919], .contexts [
        ⟨58251, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨58140, false, false, [], [9, 1, 5, 3]⟩,
        ⟨58252, false, false, [], [9, 1, 5, 3]⟩,
        ⟨58139, false, false, [], [9, 1, 5, 3]⟩,
        ⟨58139, false, false, [], [9, 1, 5, 3]⟩,
        ⟨58136, false, false, [], [1, 5, 3]⟩,
        ⟨58135, false, false, [], [1, 5, 3]⟩,
        ⟨58135, false, false, [], [1, 5, 3]⟩,
        ⟨58133, false, false, [], [5, 3]⟩,
        ⟨58253, false, false, [], [5, 3]⟩,
        ⟨58132, false, false, [], [5, 3]⟩,
        ⟨58132, false, false, [], [5, 3]⟩,
        ⟨58130, false, false, [], [3]⟩,
        ⟨58254, false, false, [], [3]⟩,
        ⟨58129, false, false, [], [3]⟩,
        ⟨58129, false, false, [], [3]⟩,
        ⟨58127, false, false, [], []⟩,
        ⟨58255, false, false, [], []⟩,
        ⟨58126, false, false, [], []⟩,
        ⟨58126, false, false, [], []⟩
      ]⟩,
    ⟨[89917], [89917], .contexts []⟩,
    ⟨[89915], [89915], .contexts []⟩,
    ⟨[89913], [89913], .contexts []⟩,
    ⟨[89911], [89911], .contexts []⟩,
    ⟨[
      89969, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11
    ], [89909], .contexts [
        ⟨58256, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨58124, false, false, [], [15, 13, 1, 11]⟩,
        ⟨58257, false, false, [], [15, 13, 1, 11]⟩,
        ⟨58123, false, false, [], [15, 13, 1, 11]⟩,
        ⟨58123, false, false, [], [15, 13, 1, 11]⟩,
        ⟨58121, false, false, [], [13, 1, 11]⟩,
        ⟨58258, false, false, [], [13, 1, 11]⟩,
        ⟨58120, false, false, [], [13, 1, 11]⟩,
        ⟨58120, false, false, [], [13, 1, 11]⟩,
        ⟨58118, false, false, [], [1, 11]⟩,
        ⟨58259, false, false, [], [1, 11]⟩,
        ⟨58117, false, false, [], [1, 11]⟩,
        ⟨58117, false, false, [], [1, 11]⟩,
        ⟨58115, false, false, [], [11]⟩,
        ⟨58260, false, false, [], [11]⟩,
        ⟨58114, false, false, [], [11]⟩,
        ⟨58114, false, false, [], [11]⟩,
        ⟨58111, false, false, [], []⟩,
        ⟨58110, false, false, [], []⟩,
        ⟨58110, false, false, [], []⟩
      ]⟩,
    ⟨[89907], [89907], .contexts []⟩,
    ⟨[89905], [89905], .contexts []⟩,
    ⟨[89901], [89901], .contexts []⟩,
    ⟨[89899], [89899], .contexts []⟩,
    ⟨[
      89969, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [89899], .contexts [
        ⟨58261, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨58108, false, false, [], [1, 5, 3, 1]⟩,
        ⟨58262, false, false, [], [1, 5, 3, 1]⟩,
        ⟨58107, false, false, [], [1, 5, 3, 1]⟩,
        ⟨58107, false, false, [], [1, 5, 3, 1]⟩,
        ⟨58104, false, false, [], [5, 3, 1]⟩,
        ⟨58263, false, false, [], [5, 3, 1]⟩,
        ⟨58103, false, false, [], [5, 3, 1]⟩,
        ⟨58103, false, false, [], [5, 3, 1]⟩,
        ⟨58100, false, false, [], [3, 1]⟩,
        ⟨58099, false, false, [], [3, 1]⟩,
        ⟨58099, false, false, [], [3, 1]⟩,
        ⟨58096, false, false, [], [1]⟩,
        ⟨58264, false, false, [], [1]⟩,
        ⟨58095, false, false, [], [1]⟩,
        ⟨58095, false, false, [], [1]⟩,
        ⟨58092, false, false, [], []⟩,
        ⟨58265, false, false, [], []⟩,
        ⟨58091, false, false, [], []⟩,
        ⟨58091, false, false, [], []⟩
      ]⟩,
    ⟨[89895], [89895], .contexts []⟩,
    ⟨[89893], [89893], .contexts []⟩,
    ⟨[89889], [89889], .contexts []⟩,
    ⟨[
      89969, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9
    ], [89889], .contexts [
        ⟨58266, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨58088, false, false, [], [13, 1, 11, 9]⟩,
        ⟨58087, false, false, [], [13, 1, 11, 9]⟩,
        ⟨58087, false, false, [], [13, 1, 11, 9]⟩,
        ⟨58084, false, false, [], [1, 11, 9]⟩,
        ⟨58267, false, false, [], [1, 11, 9]⟩,
        ⟨58083, false, false, [], [1, 11, 9]⟩,
        ⟨58083, false, false, [], [1, 11, 9]⟩,
        ⟨58080, false, false, [], [11, 9]⟩,
        ⟨58268, false, false, [], [11, 9]⟩,
        ⟨58079, false, false, [], [11, 9]⟩,
        ⟨58079, false, false, [], [11, 9]⟩,
        ⟨58076, false, false, [], [9]⟩,
        ⟨58075, false, false, [], [9]⟩,
        ⟨58075, false, false, [], [9]⟩,
        ⟨58073, false, false, [], []⟩,
        ⟨58269, false, false, [], []⟩,
        ⟨58072, false, false, [], []⟩,
        ⟨58072, false, false, [], []⟩
      ]⟩,
    ⟨[89887], [89887], .contexts []⟩,
    ⟨[89887, 5], [89885], .contexts [
        ⟨58066, false, false, [], []⟩
      ]⟩,
    ⟨[89885], [89885], .contexts []⟩,
    ⟨[89883], [89883], .contexts []⟩,
    ⟨[89881], [89881], .contexts []⟩,
    ⟨[89879], [89879], .contexts []⟩,
    ⟨[
      89969, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [89879], .contexts [
        ⟨58270, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨58070, false, false, [], [5, 3, 1, 15]⟩,
        ⟨58271, false, false, [], [5, 3, 1, 15]⟩,
        ⟨58069, false, false, [], [5, 3, 1, 15]⟩,
        ⟨58069, false, false, [], [5, 3, 1, 15]⟩,
        ⟨58272, false, false, [], [3, 1, 15]⟩,
        ⟨58273, false, false, [], [3, 1, 15]⟩,
        ⟨58065, false, false, [], [3, 1, 15]⟩,
        ⟨58065, false, false, [], [3, 1, 15]⟩,
        ⟨58063, false, false, [], [1, 15]⟩,
        ⟨58274, false, false, [], [1, 15]⟩,
        ⟨58062, false, false, [], [1, 15]⟩,
        ⟨58062, false, false, [], [1, 15]⟩,
        ⟨58060, false, false, [], [15]⟩,
        ⟨58275, false, false, [], [15]⟩,
        ⟨58059, false, false, [], [15]⟩,
        ⟨58059, false, false, [], [15]⟩,
        ⟨58057, false, false, [], []⟩,
        ⟨58276, false, false, [], []⟩,
        ⟨58056, false, false, [], []⟩,
        ⟨58056, false, false, [], []⟩
      ]⟩,
    ⟨[89877], [89877], .contexts []⟩,
    ⟨[89875], [89875], .contexts []⟩,
    ⟨[89875, 11], [89873], .contexts [
        ⟨58047, false, false, [], []⟩
      ]⟩,
    ⟨[89873], [89873], .contexts []⟩,
    ⟨[89873, 9], [89871], .contexts [
        ⟨58043, false, false, [], []⟩
      ]⟩,
    ⟨[89871], [89871], .contexts []⟩,
    ⟨[89871, 1], [89869], .contexts [
        ⟨58039, false, false, [], []⟩
      ]⟩,
    ⟨[89869], [89869], .contexts []⟩,
    ⟨[
      89969, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1
    ], [89869], .contexts [
        ⟨58277, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨58054, false, false, [], [1, 11, 9, 1]⟩,
        ⟨58278, false, false, [], [1, 11, 9, 1]⟩,
        ⟨58053, false, false, [], [1, 11, 9, 1]⟩,
        ⟨58053, false, false, [], [1, 11, 9, 1]⟩,
        ⟨58051, false, false, [], [11, 9, 1]⟩,
        ⟨58279, false, false, [], [11, 9, 1]⟩,
        ⟨58050, false, false, [], [11, 9, 1]⟩,
        ⟨58050, false, false, [], [11, 9, 1]⟩,
        ⟨58280, false, false, [], [9, 1]⟩,
        ⟨58281, false, false, [], [9, 1]⟩,
        ⟨58046, false, false, [], [9, 1]⟩,
        ⟨58046, false, false, [], [9, 1]⟩,
        ⟨58282, false, false, [], [1]⟩,
        ⟨58283, false, false, [], [1]⟩,
        ⟨58042, false, false, [], [1]⟩,
        ⟨58042, false, false, [], [1]⟩,
        ⟨58284, false, false, [], []⟩,
        ⟨58285, false, false, [], []⟩,
        ⟨58038, false, false, [], []⟩,
        ⟨58038, false, false, [], []⟩
      ]⟩,
    ⟨[89867], [89867], .contexts []⟩,
    ⟨[89867, 3], [89865], .contexts [
        ⟨58031, false, false, [], []⟩
      ]⟩,
    ⟨[89865], [89865], .contexts []⟩,
    ⟨[89865, 1], [89863], .contexts [
        ⟨58027, false, false, [], []⟩
      ]⟩,
    ⟨[89863], [89863], .contexts []⟩,
    ⟨[89859], [89859], .contexts []⟩,
    ⟨[
      89969, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13
    ], [89859], .contexts [
        ⟨58286, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨58035, false, false, [], [3, 1, 15, 13]⟩,
        ⟨58287, false, false, [], [3, 1, 15, 13]⟩,
        ⟨58034, false, false, [], [3, 1, 15, 13]⟩,
        ⟨58034, false, false, [], [3, 1, 15, 13]⟩,
        ⟨58288, false, false, [], [1, 15, 13]⟩,
        ⟨58289, false, false, [], [1, 15, 13]⟩,
        ⟨58030, false, false, [], [1, 15, 13]⟩,
        ⟨58030, false, false, [], [1, 15, 13]⟩,
        ⟨58290, false, false, [], [15, 13]⟩,
        ⟨58291, false, false, [], [15, 13]⟩,
        ⟨58026, false, false, [], [15, 13]⟩,
        ⟨58026, false, false, [], [15, 13]⟩,
        ⟨58023, false, false, [], [13]⟩,
        ⟨58022, false, false, [], [13]⟩,
        ⟨58022, false, false, [], [13]⟩,
        ⟨58018, true, false, [], [13]⟩,
        ⟨59, false, false, [89859], []⟩,
        ⟨58019, false, false, [], []⟩,
        ⟨58292, false, false, [], []⟩,
        ⟨58019, false, false, [], []⟩,
        ⟨58019, false, false, [], []⟩
      ]⟩,
    ⟨[89859, 1], [89857], .contexts [
        ⟨58016, false, false, [], []⟩
      ]⟩,
    ⟨[89855], [89855], .contexts []⟩,
    ⟨[89855, 9], [89853], .contexts [
        ⟨58009, false, false, [], []⟩
      ]⟩,
    ⟨[
      89969, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5
    ], [23347, 89851], .contexts [
        ⟨58293, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨58294, false, false, [], [11, 9, 1, 5]⟩,
        ⟨58015, false, false, [], [11, 9, 1, 5]⟩,
        ⟨58015, false, false, [], [11, 9, 1, 5]⟩,
        ⟨58011, true, false, [], [11, 9, 1, 5]⟩,
        ⟨53, false, false, [89855], [9, 1, 5]⟩,
        ⟨58012, false, false, [], [9, 1, 5]⟩,
        ⟨58295, false, false, [], [9, 1, 5]⟩,
        ⟨58012, false, false, [], [9, 1, 5]⟩,
        ⟨58012, false, false, [], [9, 1, 5]⟩,
        ⟨58296, false, false, [], [1, 5]⟩,
        ⟨58000, false, false, [], [1, 5]⟩,
        ⟨58001, false, false, [], [1, 5]⟩,
        ⟨58001, false, false, [], [1, 5]⟩,
        ⟨58006, false, false, [], [5]⟩,
        ⟨58003, false, false, [], [5]⟩,
        ⟨58004, false, false, [], [5]⟩,
        ⟨58004, false, false, [], [5]⟩,
        ⟨57999, false, false, [23347], []⟩,
        ⟨57988, false, false, [], []⟩,
        ⟨57989, false, false, [], []⟩,
        ⟨57990, false, false, [], []⟩
      ]⟩,
    ⟨[
      89969, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1
    ], [23347, 87725], .contexts [
        ⟨58297, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨57981, false, false, [23347], [1, 15, 13, 1]⟩,
        ⟨57985, false, false, [], [1, 15, 13, 1]⟩,
        ⟨57986, false, false, [], [1, 15, 13, 1]⟩,
        ⟨57987, false, false, [], [1, 15, 13, 1]⟩,
        ⟨57971, false, false, [23347], [15, 13, 1]⟩,
        ⟨57952, false, false, [], [15, 13, 1]⟩,
        ⟨57953, false, false, [], [15, 13, 1]⟩,
        ⟨57955, false, false, [], [15, 13, 1]⟩,
        ⟨57948, false, false, [23347], [13, 1]⟩,
        ⟨57933, false, false, [], [13, 1]⟩,
        ⟨57934, false, false, [], [13, 1]⟩,
        ⟨57935, false, false, [], [13, 1]⟩,
        ⟨57928, false, false, [23347], [1]⟩,
        ⟨57931, false, false, [], [1]⟩,
        ⟨57932, false, false, [], [1]⟩,
        ⟨45902, false, false, [23347], []⟩
      ]⟩,
    ⟨[24415], [23347, 17527], .source 12272⟩,
    ⟨[24417], [24415, 17525], .source 12273⟩,
    ⟨[
      89969, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [24417, 83181], .contexts [
        ⟨58298, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨57917, false, false, [23347], [9, 1, 5, 3]⟩,
        ⟨58299, true, false, [], [89843, 9, 1, 5, 3]⟩,
        ⟨57900, false, false, [24415], [1, 5, 3]⟩,
        ⟨57884, false, false, [24415], [5, 3]⟩,
        ⟨57847, false, false, [24415], [3]⟩,
        ⟨28273, false, false, [24415], []⟩,
        ⟨58300, true, false, [], [83181]⟩
      ]⟩,
    ⟨[24419], [24417, 729], .source 12274⟩,
    ⟨[24421], [24419, 15991], .source 12275⟩]

/-- Exact literal claimed equations and contextual derivations, block 911. -/
def y322TCIndexRaw911 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[24423], [24421, 2007], .source 12276⟩,
    ⟨[24425], [24423, 15443], .source 12277⟩,
    ⟨[
      89969, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11
    ], [24425, 82789], .contexts [
        ⟨58301, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨19621, false, false, [24417], [15, 13, 1, 11]⟩,
        ⟨19574, false, false, [24417], [13, 1, 11]⟩,
        ⟨58302, true, false, [], [83175, 13, 1, 11]⟩,
        ⟨19569, false, false, [24419], [1, 11]⟩,
        ⟨58303, true, false, [], [83165, 1, 11]⟩,
        ⟨19431, false, false, [24421], [11]⟩,
        ⟨58304, true, false, [], [83165, 11]⟩,
        ⟨19438, false, false, [24423], []⟩,
        ⟨58305, true, false, [], [82789]⟩
      ]⟩,
    ⟨[24427], [24425, 15437], .source 12278⟩,
    ⟨[24429], [24427, 15591], .source 12279⟩,
    ⟨[24431], [24429, 15597], .source 12280⟩,
    ⟨[24433], [24431, 315], .source 12281⟩,
    ⟨[
      89969, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [24433, 79017], .contexts [
        ⟨58306, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨16743, false, false, [24425], [1, 5, 3, 1]⟩,
        ⟨58307, true, false, [], [82797, 1, 5, 3, 1]⟩,
        ⟨17214, false, false, [24427], [5, 3, 1]⟩,
        ⟨58308, true, false, [], [82831, 5, 3, 1]⟩,
        ⟨17219, false, false, [24429], [3, 1]⟩,
        ⟨58309, true, false, [], [78999, 3, 1]⟩,
        ⟨5461, false, false, [24431], [1]⟩,
        ⟨58310, true, false, [], [78999, 1]⟩,
        ⟨5580, false, false, [24433], []⟩
      ]⟩,
    ⟨[24435], [24433, 2575], .source 12282⟩,
    ⟨[
      89969, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9
    ], [24435, 82683], .contexts [
        ⟨58311, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨15287, false, false, [24433], [13, 1, 11, 9]⟩,
        ⟨15284, false, false, [24433], [1, 11, 9]⟩,
        ⟨58312, true, false, [], [82677, 1, 11, 9]⟩,
        ⟨15372, false, false, [24435], [11, 9]⟩,
        ⟨15367, false, false, [24435], [9]⟩,
        ⟨15337, false, false, [24435], []⟩
      ]⟩,
    ⟨[24437], [24435, 15301], .source 12283⟩,
    ⟨[24439], [24437, 15329], .source 12284⟩,
    ⟨[24439, 88609], [24439, 88609], .contexts []⟩,
    ⟨[24439, 88609], [24439, 88609], .contexts []⟩,
    ⟨[89971, 1], [89971, 1], .contexts []⟩,
    ⟨[24439], [24439], .contexts []⟩,
    ⟨[24439], [24439], .contexts []⟩,
    ⟨[89971, 1], [24439, 88609], .contexts [
        ⟨58318, false, false, [], []⟩,
        ⟨58217, true, false, [], [1]⟩,
        ⟨58217, true, false, [], [1]⟩,
        ⟨58216, true, false, [], [1]⟩,
        ⟨58213, true, false, [], [1]⟩,
        ⟨4071, false, false, [89969], []⟩,
        ⟨4073, false, false, [89969], []⟩,
        ⟨58313, false, false, [], [1, 5, 3]⟩,
        ⟨15424, false, false, [24435], [5, 3]⟩,
        ⟨58314, true, false, [], [82689, 5, 3]⟩,
        ⟨15603, false, false, [24437], [3]⟩,
        ⟨58315, true, false, [], [82705, 3]⟩,
        ⟨51818, false, false, [24439], []⟩,
        ⟨58316, false, false, [], []⟩,
        ⟨58317, false, false, [], []⟩,
        ⟨51834, false, false, [24439], []⟩,
        ⟨58320, true, false, [], [88609]⟩,
        ⟨58319, true, false, [], [88609]⟩,
        ⟨13, true, false, [], [24439, 88609]⟩
      ]⟩,
    ⟨[24441], [24438], .source 12285⟩,
    ⟨[89971, 15], [89969], .contexts [
        ⟨58215, false, false, [], []⟩
      ]⟩,
    ⟨[24443], [24439, 23155], .source 12286⟩,
    ⟨[24445], [24442], .source 12287⟩,
    ⟨[89969], [24444, 84383], .contexts [
        ⟨58325, false, false, [24444], [89969]⟩,
        ⟨8, true, false, [24444, 24442, 89969], []⟩,
        ⟨58214, true, false, [24444, 24442], [1, 1]⟩,
        ⟨58214, true, false, [24444, 24442], [1, 1]⟩,
        ⟨58323, true, false, [24444, 24442], [1, 1]⟩,
        ⟨7, false, false, [24444, 24442, 89971], [1]⟩,
        ⟨11, false, false, [24444, 24442, 89971], [1]⟩,
        ⟨58318, false, false, [24444, 24442], [15, 1]⟩,
        ⟨58321, false, false, [24444, 24442], [15, 1]⟩,
        ⟨58316, false, false, [24444, 24442], [15, 1]⟩,
        ⟨58317, false, false, [24444, 24442], [15, 1]⟩,
        ⟨58317, false, false, [24444, 24442], [15, 1]⟩,
        ⟨51844, false, false, [24444, 24442, 24439], [1]⟩,
        ⟨58324, true, false, [24444, 24442], [84381, 1]⟩,
        ⟨26693, false, false, [24444], [1]⟩,
        ⟨13, true, false, [24444, 24442], [24443, 84381, 1]⟩,
        ⟨26703, false, false, [24444], []⟩
      ]⟩,
    ⟨[24443], [24444], .contexts [
        ⟨58325, true, true, [], []⟩
      ]⟩,
    ⟨[89969], [24443, 84383], .contexts [
        ⟨58326, false, false, [], []⟩,
        ⟨58327, true, false, [], [84383]⟩
      ]⟩,
    ⟨[24445], [24442], .contexts [
        ⟨58325, false, false, [], []⟩
      ]⟩,
    ⟨[24442], [24442], .contexts []⟩,
    ⟨[84383, 15], [24445, 89971], .contexts [
        ⟨58328, true, false, [24442], [15]⟩,
        ⟨58213, false, false, [24442], []⟩,
        ⟨58216, false, false, [24442], []⟩,
        ⟨58330, true, false, [], [89971]⟩,
        ⟨58330, true, false, [], [89971]⟩,
        ⟨58329, true, false, [], [89971]⟩
      ]⟩,
    ⟨[24443, 84383], [24443, 84383], .contexts []⟩,
    ⟨[89969], [24443, 84383], .contexts [
        ⟨58328, false, false, [], []⟩,
        ⟨58332, false, false, [], []⟩
      ]⟩,
    ⟨[24443, 84383, 13], [24443, 89211], .contexts [
        ⟨54860, false, false, [24443], []⟩
      ]⟩,
    ⟨[24443, 89211], [24443, 89211], .contexts []⟩,
    ⟨[24443, 89211], [24443, 89211], .contexts []⟩,
    ⟨[24443, 89211], [24443, 89211], .contexts []⟩,
    ⟨[24445], [24442], .contexts [
        ⟨58329, false, false, [], []⟩,
        ⟨13, false, false, [24442], []⟩
      ]⟩,
    ⟨[24443, 89213], [24443, 89213], .contexts []⟩,
    ⟨[89213], [24445, 89965], .contexts [
        ⟨58339, true, false, [24442], []⟩,
        ⟨54886, true, false, [], []⟩,
        ⟨58337, true, false, [24442], [1]⟩,
        ⟨58327, false, false, [24442], [89211, 1]⟩,
        ⟨58337, true, false, [24442, 24444, 24442], [1]⟩,
        ⟨58336, true, false, [24442, 24444, 24442], [1]⟩,
        ⟨58335, true, false, [24442, 24444, 24442], [1]⟩,
        ⟨58334, true, false, [24442, 24444, 24442], [1]⟩,
        ⟨58333, true, false, [24442, 24444, 24442], [13, 1]⟩,
        ⟨58211, false, false, [24442, 24444, 24442], [1]⟩,
        ⟨58218, false, false, [24442, 24444, 24442], [1]⟩,
        ⟨58338, true, false, [24442, 24444], [89967, 1]⟩,
        ⟨58208, false, false, [24442], []⟩,
        ⟨58219, false, false, [24442], []⟩,
        ⟨58338, true, false, [], [89965]⟩
      ]⟩,
    ⟨[24447], [24443, 245], .source 12288⟩,
    ⟨[24449], [24446], .source 12289⟩,
    ⟨[24449], [24446], .contexts [
        ⟨58342, false, false, [], []⟩
      ]⟩,
    ⟨[89963], [24447, 89213], .contexts [
        ⟨58343, false, false, [24448], [89963]⟩,
        ⟨13, false, false, [24448, 24446], [89963]⟩,
        ⟨58220, true, false, [24448, 24446], []⟩,
        ⟨58205, true, false, [24448, 24446], []⟩,
        ⟨58340, true, false, [24448, 24446, 24444], [11]⟩,
        ⟨58327, true, false, [24448, 24446], [89213, 11]⟩,
        ⟨58339, false, false, [24448, 24446], [11]⟩,
        ⟨54898, false, false, [24448, 24446, 24443], []⟩,
        ⟨58341, true, false, [24448, 24446], [89213]⟩,
        ⟨58342, false, true, [], [89213]⟩
      ]⟩,
    ⟨[24446], [24446], .contexts []⟩,
    ⟨[89213, 9], [24449, 89961], .contexts [
        ⟨58344, true, false, [24446], [9]⟩,
        ⟨58202, false, false, [24446], []⟩,
        ⟨58221, false, false, [24446], []⟩,
        ⟨58345, true, false, [], [89961]⟩,
        ⟨58345, true, false, [], [89961]⟩,
        ⟨58343, true, false, [], [89961]⟩
      ]⟩,
    ⟨[89969], [24443, 84383], .contexts [
        ⟨58333, false, false, [], []⟩
      ]⟩,
    ⟨[89971, 15], [24443, 84383], .contexts [
        ⟨58323, false, false, [], []⟩,
        ⟨58347, false, false, [], []⟩,
        ⟨58332, false, false, [], []⟩,
        ⟨58332, false, false, [], []⟩
      ]⟩,
    ⟨[24451], [24443, 17469], .source 12290⟩,
    ⟨[24453], [24451, 23603], .source 12291⟩,
    ⟨[89971], [89971], .contexts []⟩,
    ⟨[89971], [89971], .contexts []⟩,
    ⟨[24455], [24452], .source 12292⟩,
    ⟨[24452], [24452], .contexts []⟩,
    ⟨[89099, 3], [24455, 89971], .contexts [
        ⟨58350, false, false, [24452], [89099, 3]⟩,
        ⟨54161, true, false, [24452, 24451], [3]⟩,
        ⟨58349, false, false, [24452], [84615, 15, 3]⟩,
        ⟨27891, true, false, [24452, 24443], [15, 3]⟩,
        ⟨58348, true, false, [24452], [3, 15, 3]⟩,
        ⟨903, false, false, [24452, 89971], []⟩,
        ⟨58351, false, false, [24452], []⟩,
        ⟨58352, false, false, [24452], []⟩,
        ⟨58354, true, false, [], [89971]⟩,
        ⟨58354, true, false, [], [89971]⟩,
        ⟨58353, true, false, [], [89971]⟩
      ]⟩,
    ⟨[24457], [24443, 19465], .source 12293⟩,
    ⟨[24459], [24457, 19493], .source 12294⟩,
    ⟨[24461], [24458], .source 12295⟩,
    ⟨[24458], [24458], .contexts []⟩,
    ⟨[83907, 5], [24461, 89971], .contexts [
        ⟨58357, false, false, [24458], [83907, 5]⟩,
        ⟨38933, true, false, [24458, 24457], [5]⟩,
        ⟨58356, false, false, [24458], [86799, 15, 5]⟩,
        ⟨38905, true, false, [24458, 24443], [15, 5]⟩,
        ⟨58348, true, false, [24458], [5, 15, 5]⟩,
        ⟨2284, false, false, [24458, 89971], []⟩,
        ⟨58351, false, false, [24458], []⟩,
        ⟨58352, false, false, [24458], []⟩,
        ⟨58359, true, false, [], [89971]⟩,
        ⟨58359, true, false, [], [89971]⟩,
        ⟨58358, true, false, [], [89971]⟩
      ]⟩,
    ⟨[24463], [24443, 21513], .source 12296⟩,
    ⟨[24465], [24462], .source 12297⟩,
    ⟨[24462], [24462], .contexts []⟩,
    ⟨[87665, 9], [24465, 89971], .contexts [
        ⟨58361, false, false, [24462], [87665, 9]⟩,
        ⟨45442, true, false, [24462, 24443], [9]⟩,
        ⟨26710, true, false, [24462, 24443], [15, 9]⟩,
        ⟨58348, true, false, [24462], [9, 15, 9]⟩,
        ⟨2656, false, false, [24462, 89971], []⟩,
        ⟨58351, false, false, [24462], []⟩,
        ⟨58352, false, false, [24462], []⟩,
        ⟨58363, true, false, [], [89971]⟩,
        ⟨58363, true, false, [], [89971]⟩,
        ⟨58362, true, false, [], [89971]⟩
      ]⟩,
    ⟨[89971, 9], [24463, 87665], .contexts [
        ⟨58364, true, false, [24464], [9]⟩,
        ⟨46, false, false, [24464, 87665], []⟩,
        ⟨58362, false, true, [], [87665]⟩
      ]⟩,
    ⟨[24467], [24447, 24445], .source 12298⟩,
    ⟨[24469], [24466], .source 12299⟩]

/-- Exact literal claimed equations and contextual derivations, block 912. -/
def y322TCIndexRaw912 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[24466], [24466], .contexts []⟩,
    ⟨[89971, 11], [24469, 89971], .contexts [
        ⟨58366, false, false, [24466], [89971, 11]⟩,
        ⟨58331, true, false, [24466, 24447], [11]⟩,
        ⟨58341, false, false, [24466], [84383, 15, 11]⟩,
        ⟨26708, true, false, [24466, 24443], [15, 11]⟩,
        ⟨58348, true, false, [24466], [11, 15, 11]⟩,
        ⟨2289, false, false, [24466, 89971], []⟩,
        ⟨58351, false, false, [24466], []⟩,
        ⟨58352, false, false, [24466], []⟩,
        ⟨58368, true, false, [], [89971]⟩,
        ⟨58368, true, false, [], [89971]⟩,
        ⟨58367, true, false, [], [89971]⟩
      ]⟩,
    ⟨[24471], [24443, 23773], .source 12300⟩,
    ⟨[24473], [24471, 24445], .source 12301⟩,
    ⟨[24473, 89971, 13], [89971], .contexts [
        ⟨58371, false, false, [], [89971, 13]⟩,
        ⟨58331, true, false, [24471], [13]⟩,
        ⟨54861, true, false, [24471], [15, 13]⟩,
        ⟨58370, false, false, [], [89211, 13, 15, 13]⟩,
        ⟨54884, true, false, [24443], [13, 15, 13]⟩,
        ⟨58337, true, false, [], [15, 13, 15, 13]⟩,
        ⟨58336, true, false, [], [15, 13, 15, 13]⟩,
        ⟨58335, true, false, [], [15, 13, 15, 13]⟩,
        ⟨58334, true, false, [], [15, 13, 15, 13]⟩,
        ⟨58348, true, false, [], [13, 15, 13, 15, 13]⟩,
        ⟨2137, false, false, [89971], []⟩,
        ⟨58351, false, false, [], []⟩
      ]⟩,
    ⟨[24475], [24472], .source 12302⟩,
    ⟨[24472], [24472], .contexts []⟩,
    ⟨[89971, 13], [24475, 89971], .contexts [
        ⟨58372, false, false, [24472], []⟩,
        ⟨58352, false, false, [24472], []⟩,
        ⟨58374, true, false, [], [89971]⟩,
        ⟨58374, true, false, [], [89971]⟩,
        ⟨58373, true, false, [], [89971]⟩
      ]⟩,
    ⟨[24449, 89961], [24449, 89961], .contexts []⟩,
    ⟨[24449, 89961], [24449, 89961], .contexts []⟩,
    ⟨[89213, 9], [24449, 89961], .contexts [
        ⟨58346, false, false, [], []⟩,
        ⟨58376, false, false, [], []⟩,
        ⟨58377, false, false, [], []⟩,
        ⟨58377, false, false, [], []⟩
      ]⟩,
    ⟨[89213, 8], [89213, 9], .contexts [
        ⟨47, false, false, [89213], []⟩
      ]⟩,
    ⟨[83229, 13], [83229, 13], .contexts []⟩,
    ⟨[89961], [89961], .contexts []⟩,
    ⟨[24477], [16135, 24449], .source 12303⟩,
    ⟨[83229, 13], [24477, 89961], .contexts [
        ⟨58380, false, false, [], []⟩,
        ⟨20167, true, false, [], [13]⟩,
        ⟨54901, true, false, [16132], [9, 13]⟩,
        ⟨54901, true, false, [16132], [9, 13]⟩,
        ⟨54900, true, false, [16132], [9, 13]⟩,
        ⟨54903, true, false, [16132], [9, 13]⟩,
        ⟨54902, true, false, [16132], [9, 13]⟩,
        ⟨942, false, false, [16132, 89213], []⟩,
        ⟨58379, false, false, [16132], []⟩,
        ⟨58378, false, false, [16132], []⟩,
        ⟨58381, false, false, [16132, 24449], []⟩,
        ⟨20618, true, false, [], [24449, 89961]⟩,
        ⟨58382, true, false, [], [89961]⟩
      ]⟩,
    ⟨[24479], [24476], .source 12304⟩,
    ⟨[24481], [23773, 24449], .source 12305⟩,
    ⟨[89961, 15], [89961, 15], .contexts []⟩,
    ⟨[24483], [24480], .source 12306⟩,
    ⟨[24485], [24483, 24449], .source 12307⟩,
    ⟨[89961, 15], [24485, 89961], .contexts [
        ⟨58386, false, false, [], []⟩,
        ⟨58385, false, false, [24480], [89961, 15]⟩,
        ⟨58346, true, false, [24480, 23773], [15]⟩,
        ⟨54909, true, false, [24480], [9, 15]⟩,
        ⟨54909, true, false, [24480], [9, 15]⟩,
        ⟨54908, true, false, [24480], [9, 15]⟩,
        ⟨54911, true, false, [24480], [9, 15]⟩,
        ⟨54910, true, false, [24480], [9, 15]⟩,
        ⟨1671, false, false, [24480, 89213], []⟩,
        ⟨58379, false, false, [24480], []⟩,
        ⟨58378, false, false, [24480], []⟩,
        ⟨58381, false, false, [24480, 24449], []⟩,
        ⟨58387, true, false, [], [24449, 89961]⟩,
        ⟨58388, true, false, [], [89961]⟩
      ]⟩,
    ⟨[23789, 89213], [23789, 89213], .contexts []⟩,
    ⟨[23789, 89213], [23789, 89213], .contexts []⟩,
    ⟨[24487], [23789, 24449], .source 12308⟩,
    ⟨[24489], [24486], .source 12309⟩,
    ⟨[24491], [24489, 24449], .source 12310⟩,
    ⟨[24477, 89961], [24477, 89961], .contexts []⟩,
    ⟨[24477, 89961], [24477, 89961], .contexts []⟩,
    ⟨[83229, 13], [24477, 89961], .contexts [
        ⟨58380, false, false, [], []⟩,
        ⟨58383, false, false, [], []⟩,
        ⟨58395, false, false, [], []⟩,
        ⟨58396, false, false, [], []⟩,
        ⟨58396, false, false, [], []⟩
      ]⟩,
    ⟨[89959, 13], [89959, 13], .contexts []⟩,
    ⟨[24493], [24479, 20719], .source 12311⟩,
    ⟨[89959, 13], [24493, 83617], .contexts [
        ⟨58398, false, false, [], []⟩,
        ⟨58198, true, false, [], [13]⟩,
        ⟨58397, true, false, [24476], [1, 13]⟩,
        ⟨1968, false, false, [24476, 83229], []⟩,
        ⟨248, false, false, [24476, 83229], []⟩,
        ⟨42560, false, false, [24476], [13, 1]⟩,
        ⟨43139, false, false, [24476], [13, 1]⟩,
        ⟨43140, false, false, [24476], [13, 1]⟩,
        ⟨43140, false, false, [24476], [13, 1]⟩,
        ⟨43153, false, false, [24476], [1]⟩,
        ⟨43154, false, false, [24476], [1]⟩,
        ⟨43155, false, false, [24476], [1]⟩,
        ⟨43156, false, false, [24476], [1]⟩,
        ⟨22163, false, false, [24476, 20719], []⟩,
        ⟨42915, false, false, [24476, 20719], []⟩,
        ⟨58384, true, false, [], [20719, 83617]⟩,
        ⟨58399, true, false, [], [83617]⟩
      ]⟩,
    ⟨[24495], [24492], .source 12312⟩,
    ⟨[24485, 89961], [24485, 89961], .contexts []⟩,
    ⟨[24485, 89961], [24485, 89961], .contexts []⟩,
    ⟨[89961, 1], [89959], .contexts [
        ⟨58222, false, false, [], []⟩,
        ⟨58223, false, false, [], []⟩,
        ⟨58197, false, false, [], []⟩,
        ⟨58197, false, false, [], []⟩
      ]⟩,
    ⟨[89961, 0], [89961, 1], .contexts [
        ⟨9, false, false, [89961], []⟩
      ]⟩,
    ⟨[89959, 15], [89959, 15], .contexts []⟩,
    ⟨[89959], [89959], .contexts []⟩,
    ⟨[24497], [24484], .source 12313⟩,
    ⟨[24497], [24497], .contexts []⟩,
    ⟨[24484], [24484], .contexts []⟩,
    ⟨[24497], [24484], .contexts [
        ⟨58409, false, false, [], []⟩,
        ⟨58408, false, false, [], []⟩,
        ⟨58410, false, false, [], []⟩,
        ⟨58410, false, false, [], []⟩
      ]⟩,
    ⟨[89959, 15], [24497, 89959], .contexts [
        ⟨58406, false, false, [], []⟩,
        ⟨58198, true, false, [], [15]⟩,
        ⟨58403, true, false, [24484], [1, 15]⟩,
        ⟨58403, true, false, [24484], [1, 15]⟩,
        ⟨58402, true, false, [24484], [1, 15]⟩,
        ⟨58389, true, false, [24484], [1, 15]⟩,
        ⟨58386, true, false, [24484], [1, 15]⟩,
        ⟨1666, false, false, [24484, 89961], []⟩,
        ⟨58405, false, false, [24484], []⟩,
        ⟨58404, false, false, [24484], []⟩,
        ⟨58407, false, false, [24484], []⟩,
        ⟨58411, true, false, [], [89959]⟩
      ]⟩,
    ⟨[24493, 83617], [24493, 83617], .contexts []⟩,
    ⟨[24493, 83617], [24493, 83617], .contexts []⟩,
    ⟨[89959, 13], [24493, 83617], .contexts [
        ⟨58398, false, false, [], []⟩,
        ⟨58400, false, false, [], []⟩,
        ⟨58413, false, false, [], []⟩,
        ⟨58414, false, false, [], []⟩,
        ⟨58414, false, false, [], []⟩
      ]⟩,
    ⟨[24499], [24493, 20525], .source 12314⟩,
    ⟨[89959, 5], [89957], .contexts [
        ⟨58225, false, false, [], []⟩,
        ⟨58226, false, false, [], []⟩,
        ⟨58193, false, false, [], []⟩,
        ⟨58193, false, false, [], []⟩
      ]⟩,
    ⟨[89959, 4], [89959, 5], .contexts [
        ⟨29, false, false, [89959], []⟩
      ]⟩,
    ⟨[84827, 13], [84827, 13], .contexts []⟩,
    ⟨[89957], [89957], .contexts []⟩,
    ⟨[24501], [24498], .source 12315⟩,
    ⟨[24501], [24498], .contexts [
        ⟨58421, false, false, [], []⟩
      ]⟩,
    ⟨[24498], [24498], .contexts []⟩,
    ⟨[84827, 13], [24501, 89957], .contexts [
        ⟨58419, false, false, [], []⟩,
        ⟨58416, false, false, [24498], [84827, 13]⟩,
        ⟨42579, true, false, [24498, 24493], [13]⟩,
        ⟨58415, true, false, [24498], [5, 13]⟩,
        ⟨1136, false, false, [24498, 89959], []⟩,
        ⟨58418, false, false, [24498], []⟩,
        ⟨58417, false, false, [24498], []⟩,
        ⟨58420, false, false, [24498], []⟩,
        ⟨58423, true, false, [], [89957]⟩,
        ⟨58423, true, false, [], [89957]⟩,
        ⟨58422, true, false, [], [89957]⟩
      ]⟩,
    ⟨[24499], [24500], .contexts [
        ⟨58421, true, true, [], []⟩
      ]⟩,
    ⟨[89957, 13], [24499, 84827], .contexts [
        ⟨58424, true, false, [24500], [13]⟩,
        ⟨59, false, false, [24500, 84827], []⟩,
        ⟨58425, true, false, [], [84827]⟩
      ]⟩,
    ⟨[24503], [24493, 20865], .source 12316⟩,
    ⟨[24505], [24503, 21175], .source 12317⟩,
    ⟨[24507], [24504], .source 12318⟩,
    ⟨[24504], [24504], .contexts []⟩,
    ⟨[84203, 9], [24507, 89959], .contexts [
        ⟨58428, false, false, [24504], [84203, 9]⟩,
        ⟨44461, true, false, [24504, 24503], [9]⟩,
        ⟨58427, false, false, [24504], [85469, 13, 9]⟩,
        ⟨42920, true, false, [24504, 24493], [13, 9]⟩,
        ⟨58415, true, false, [24504], [9, 13, 9]⟩,
        ⟨5366, false, false, [24504, 89959], []⟩,
        ⟨58407, false, false, [24504], []⟩,
        ⟨58430, true, false, [], [89959]⟩,
        ⟨58430, true, false, [], [89959]⟩,
        ⟨58429, true, false, [], [89959]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 913. -/
def y322TCIndexRaw913 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[24505], [24506], .contexts [
        ⟨58429, true, true, [], []⟩
      ]⟩,
    ⟨[89959, 9], [24505, 84203], .contexts [
        ⟨58431, true, false, [24506], [9]⟩,
        ⟨46, false, false, [24506, 84203], []⟩,
        ⟨58432, true, false, [], [84203]⟩
      ]⟩,
    ⟨[24497, 89959], [24497, 89959], .contexts []⟩,
    ⟨[24497, 89959], [24497, 89959], .contexts []⟩,
    ⟨[89957, 15], [89957, 15], .contexts []⟩,
    ⟨[24496], [24496], .contexts []⟩,
    ⟨[24485], [24496], .contexts [
        ⟨58408, true, true, [], []⟩,
        ⟨58437, false, false, [], []⟩,
        ⟨58437, false, false, [], []⟩
      ]⟩,
    ⟨[89957, 15], [24485, 89957], .contexts [
        ⟨58436, false, false, [], []⟩,
        ⟨58194, true, false, [], [15]⟩,
        ⟨58435, true, false, [24496], [5, 15]⟩,
        ⟨58435, true, false, [24496], [5, 15]⟩,
        ⟨58434, true, false, [24496], [5, 15]⟩,
        ⟨58412, true, false, [24496], [5, 15]⟩,
        ⟨58406, true, false, [24496], [5, 15]⟩,
        ⟨2072, false, false, [24496, 89959], []⟩,
        ⟨58418, false, false, [24496], []⟩,
        ⟨58417, false, false, [24496], []⟩,
        ⟨58420, false, false, [24496], []⟩,
        ⟨58438, true, false, [], [89957]⟩
      ]⟩,
    ⟨[84827, 13], [24501, 89957], .contexts [
        ⟨58424, false, false, [], []⟩
      ]⟩,
    ⟨[24501, 89957], [24501, 89957], .contexts []⟩,
    ⟨[24501, 89957], [24501, 89957], .contexts []⟩,
    ⟨[84827, 13], [24501, 89957], .contexts [
        ⟨58419, false, false, [], []⟩,
        ⟨58440, false, false, [], []⟩,
        ⟨58441, false, false, [], []⟩,
        ⟨58442, false, false, [], []⟩,
        ⟨58442, false, false, [], []⟩
      ]⟩,
    ⟨[24509], [17729, 24501], .source 12319⟩,
    ⟨[89957, 7], [89957, 7], .contexts []⟩,
    ⟨[24499], [24500], .contexts [
        ⟨58425, false, false, [], []⟩
      ]⟩,
    ⟨[24511], [24499, 24509], .source 12320⟩,
    ⟨[89957, 7], [24511, 89957], .contexts [
        ⟨58445, false, false, [], []⟩,
        ⟨58443, true, false, [24500], [7]⟩,
        ⟨73, false, false, [24500, 84827], []⟩,
        ⟨74, false, false, [24500, 84827], []⟩,
        ⟨29165, false, false, [24500], [13]⟩,
        ⟨58424, false, false, [24500, 17729], []⟩,
        ⟨58444, true, false, [24500], [89957]⟩,
        ⟨58420, false, false, [24500, 24509], []⟩,
        ⟨58446, true, false, [], [24509, 89957]⟩,
        ⟨58447, true, false, [], [89957]⟩
      ]⟩,
    ⟨[24513], [18223, 21175], .source 12321⟩,
    ⟨[89957, 9], [89957, 9], .contexts []⟩,
    ⟨[24515], [24499, 24513], .source 12322⟩,
    ⟨[89957, 9], [24515, 84205], .contexts [
        ⟨58450, false, false, [], []⟩,
        ⟨58443, true, false, [24500], [9]⟩,
        ⟨77, false, false, [24500, 84827], []⟩,
        ⟨78, false, false, [24500, 84827], []⟩,
        ⟨32309, false, false, [24500], [13]⟩,
        ⟨44397, false, false, [24500, 18223], []⟩,
        ⟨58449, true, false, [24500], [84205]⟩,
        ⟨25439, false, false, [24500, 24513], []⟩,
        ⟨58446, true, false, [], [24513, 84205]⟩,
        ⟨58451, true, false, [], [84205]⟩
      ]⟩,
    ⟨[24517], [24514], .source 12323⟩,
    ⟨[84205, 9], [24517, 89957], .contexts [
        ⟨58452, true, false, [24514], [9]⟩,
        ⟨46, false, false, [24514, 89957], []⟩,
        ⟨58453, true, false, [], [89957]⟩
      ]⟩,
    ⟨[24485, 89957], [24485, 89957], .contexts []⟩,
    ⟨[24485, 89957], [24485, 89957], .contexts []⟩,
    ⟨[89957, 15], [24485, 89957], .contexts [
        ⟨58436, false, false, [], []⟩,
        ⟨58439, false, false, [], []⟩,
        ⟨58455, false, false, [], []⟩,
        ⟨58456, false, false, [], []⟩,
        ⟨58456, false, false, [], []⟩
      ]⟩,
    ⟨[89957, 3], [89955], .contexts [
        ⟨58227, false, false, [], []⟩
      ]⟩,
    ⟨[89957, 3], [89955], .contexts [
        ⟨58458, false, false, [], []⟩,
        ⟨58228, false, false, [], []⟩,
        ⟨58189, false, false, [], []⟩,
        ⟨58189, false, false, [], []⟩
      ]⟩,
    ⟨[89957, 2], [89957, 3], .contexts [
        ⟨21, false, false, [89957], []⟩
      ]⟩,
    ⟨[89955, 15], [89955, 15], .contexts []⟩,
    ⟨[89955], [89955], .contexts []⟩,
    ⟨[24511, 89957], [24511, 89957], .contexts []⟩,
    ⟨[24511, 89957], [24511, 89957], .contexts []⟩,
    ⟨[89955, 7], [89955, 7], .contexts []⟩,
    ⟨[24519], [24510], .source 12324⟩,
    ⟨[24510], [24510], .contexts []⟩,
    ⟨[24497, 89955], [24497, 89955], .contexts []⟩,
    ⟨[89955, 15, 1], [24497, 89953], .contexts [
        ⟨58461, false, false, [], [1]⟩,
        ⟨58461, false, false, [], [1]⟩,
        ⟨58190, true, false, [], [15, 1]⟩,
        ⟨58457, true, false, [24484], [3, 15, 1]⟩,
        ⟨1141, false, false, [24484, 89957], [1]⟩,
        ⟨58460, false, false, [24484], [1]⟩,
        ⟨58459, false, false, [24484], [1]⟩,
        ⟨58462, false, false, [24484], [1]⟩,
        ⟨58411, true, false, [], [89955, 1]⟩,
        ⟨58468, false, false, [], [1]⟩,
        ⟨58468, false, false, [], [1]⟩,
        ⟨58187, false, false, [24497], []⟩
      ]⟩,
    ⟨[24497, 89951], [24497, 89951], .contexts []⟩,
    ⟨[24497, 89951], [24497, 89951], .contexts []⟩,
    ⟨[89955, 1], [89953], .contexts [
        ⟨58229, false, false, [], []⟩
      ]⟩,
    ⟨[24497], [24497], .contexts [
        ⟨58409, false, false, [], []⟩
      ]⟩,
    ⟨[24519, 89955], [24519, 89955], .contexts []⟩,
    ⟨[89955, 7], [24519, 89955], .contexts [
        ⟨58465, false, false, [], []⟩,
        ⟨58465, false, false, [], []⟩,
        ⟨58190, true, false, [], [7]⟩,
        ⟨58464, true, false, [24510], [3, 7]⟩,
        ⟨58464, true, false, [24510], [3, 7]⟩,
        ⟨58463, true, false, [24510], [3, 7]⟩,
        ⟨58448, true, false, [24510], [3, 7]⟩,
        ⟨58445, true, false, [24510], [3, 7]⟩,
        ⟨14911, false, false, [24510, 89957], []⟩,
        ⟨58460, false, false, [24510], []⟩,
        ⟨58459, false, false, [24510], []⟩,
        ⟨58462, false, false, [24510], []⟩,
        ⟨58467, true, false, [], [89955]⟩,
        ⟨58467, true, false, [], [89955]⟩,
        ⟨58466, true, false, [], [89955]⟩,
        ⟨58474, false, false, [], []⟩,
        ⟨58474, false, false, [], []⟩
      ]⟩,
    ⟨[89953], [24497, 89951], .contexts [
        ⟨58186, true, false, [], []⟩,
        ⟨58186, true, false, [], []⟩,
        ⟨58230, true, false, [], []⟩,
        ⟨58472, true, false, [], []⟩,
        ⟨58438, false, false, [24484], [89955, 1]⟩,
        ⟨58462, true, false, [24484, 24496], [1]⟩,
        ⟨504, true, false, [24484, 24496, 89955], [1]⟩,
        ⟨58469, false, false, [24484, 24496], [15, 1, 1]⟩,
        ⟨58184, false, false, [24484], [1, 1]⟩,
        ⟨58470, false, false, [24484, 24496], [1, 1]⟩,
        ⟨58471, false, false, [24484, 24496], [1, 1]⟩,
        ⟨8, false, false, [24484, 89951], []⟩,
        ⟨58408, true, false, [], [89951]⟩,
        ⟨58470, false, false, [], []⟩,
        ⟨58473, true, false, [], [89951]⟩
      ]⟩,
    ⟨[89953], [24497, 89951], .contexts [
        ⟨58476, false, false, [], []⟩,
        ⟨58471, false, false, [], []⟩
      ]⟩,
    ⟨[24521], [24519, 24497], .source 12325⟩,
    ⟨[89953], [24497, 89951], .contexts [
        ⟨58477, false, false, [], []⟩
      ]⟩,
    ⟨[89951, 7], [89951, 7], .contexts []⟩,
    ⟨[24523], [24520], .source 12326⟩,
    ⟨[24525], [24523, 24497], .source 12327⟩,
    ⟨[24525, 89951], [24525, 89951], .contexts []⟩,
    ⟨[24525, 89949], [24525, 89949], .contexts []⟩,
    ⟨[24525, 89949], [24525, 89949], .contexts []⟩,
    ⟨[89951, 7, 13], [24525, 89949], .contexts [
        ⟨58480, false, false, [], [13]⟩,
        ⟨58480, false, false, [], [13]⟩,
        ⟨58478, false, false, [24520], [89951, 7, 13]⟩,
        ⟨58477, true, false, [24520, 24519], [7, 13]⟩,
        ⟨58187, true, false, [24520, 24519], [7, 13]⟩,
        ⟨58475, true, false, [24520], [1, 7, 13]⟩,
        ⟨502, false, false, [24520, 89955], [13]⟩,
        ⟨9, false, false, [24520, 89955], [13]⟩,
        ⟨58472, false, false, [24520], [13]⟩,
        ⟨58479, false, false, [24520], [13]⟩,
        ⟨58471, false, false, [24520], [13]⟩,
        ⟨58471, false, false, [24520], [13]⟩,
        ⟨58481, true, false, [], [24497, 89951, 13]⟩,
        ⟨58482, true, false, [], [89951, 13]⟩,
        ⟨58483, false, false, [], [13]⟩,
        ⟨58483, false, false, [], [13]⟩,
        ⟨58181, false, false, [24525], []⟩,
        ⟨58484, false, false, [], []⟩,
        ⟨58485, false, false, [], []⟩
      ]⟩,
    ⟨[89949, 7], [89949, 7], .contexts []⟩,
    ⟨[24525], [24525], .contexts [
        ⟨13, false, false, [], [24525]⟩
      ]⟩,
    ⟨[89949, 7, 1], [24525, 89947], .contexts [
        ⟨58487, false, false, [], [1]⟩,
        ⟨58487, false, false, [], [1]⟩,
        ⟨58180, true, false, [], [7, 1]⟩,
        ⟨58180, true, false, [], [7, 1]⟩,
        ⟨58232, true, false, [], [7, 1]⟩,
        ⟨58231, true, false, [], [7, 1]⟩,
        ⟨73, false, false, [89951], [1]⟩,
        ⟨74, false, false, [89951], [1]⟩,
        ⟨58486, false, false, [], [1]⟩,
        ⟨58488, true, false, [], [89949, 1]⟩,
        ⟨58484, false, false, [], [1]⟩,
        ⟨58485, false, false, [], [1]⟩,
        ⟨58485, false, false, [], [1]⟩,
        ⟨58178, false, false, [24525], []⟩
      ]⟩,
    ⟨[89947, 7], [89947, 7], .contexts []⟩,
    ⟨[24527], [24524], .source 12328⟩,
    ⟨[24524], [24524], .contexts []⟩,
    ⟨[24527], [24524], .contexts [
        ⟨58491, false, false, [], []⟩,
        ⟨58492, false, false, [], []⟩,
        ⟨58492, false, false, [], []⟩
      ]⟩,
    ⟨[24527, 89947], [24527, 89947], .contexts []⟩,
    ⟨[24527, 89945, 7], [89947, 11], .contexts [
        ⟨58175, true, false, [24527], [7]⟩,
        ⟨58494, true, false, [], [11, 7]⟩,
        ⟨58494, true, false, [], [11, 7]⟩,
        ⟨58493, false, false, [], [89947, 11, 7]⟩,
        ⟨58177, true, false, [24524], [11, 7]⟩,
        ⟨58177, true, false, [24524], [11, 7]⟩,
        ⟨58235, true, false, [24524], [11, 7]⟩,
        ⟨58234, true, false, [24524], [11, 7]⟩,
        ⟨9, true, false, [24524, 89949], [11, 7]⟩,
        ⟨502, true, false, [24524, 89949], [11, 7]⟩,
        ⟨58489, false, false, [24524], [7, 11, 7]⟩,
        ⟨58490, true, false, [], [11, 7]⟩,
        ⟨58490, true, false, [], [11, 7]⟩,
        ⟨555, false, false, [89947], []⟩,
        ⟨54, false, false, [89947], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 914. -/
def y322TCIndexRaw914 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89945, 7], [89945, 7], .contexts []⟩,
    ⟨[24526], [24526], .contexts []⟩,
    ⟨[24525], [24526], .contexts [
        ⟨58491, true, true, [], []⟩,
        ⟨58497, false, false, [], []⟩,
        ⟨58497, false, false, [], []⟩
      ]⟩,
    ⟨[89945, 7], [24525, 89945], .contexts [
        ⟨58496, false, false, [], []⟩,
        ⟨58495, false, false, [24526], []⟩,
        ⟨58236, false, false, [24526], []⟩,
        ⟨58237, false, false, [24526], []⟩,
        ⟨58174, false, false, [24526], []⟩,
        ⟨58174, false, false, [24526], []⟩,
        ⟨58498, true, false, [], [89945]⟩
      ]⟩,
    ⟨[24525, 89945], [24525, 89945], .contexts []⟩,
    ⟨[24525, 89945], [24525, 89945], .contexts []⟩,
    ⟨[89945, 9], [89943], .contexts [
        ⟨58238, false, false, [], []⟩,
        ⟨58239, false, false, [], []⟩,
        ⟨58170, false, false, [], []⟩,
        ⟨58170, false, false, [], []⟩
      ]⟩,
    ⟨[89943, 7], [89943, 7], .contexts []⟩,
    ⟨[89943], [89943], .contexts []⟩,
    ⟨[89943, 7], [24527, 89943], .contexts [
        ⟨58503, false, false, [], []⟩,
        ⟨58171, true, false, [], [7]⟩,
        ⟨58501, true, false, [24524], [9, 7]⟩,
        ⟨58501, true, false, [24524], [9, 7]⟩,
        ⟨58500, true, false, [24524], [9, 7]⟩,
        ⟨58499, true, false, [24524], [9, 7]⟩,
        ⟨58496, true, false, [24524], [9, 7]⟩,
        ⟨579, false, false, [24524, 89945], []⟩,
        ⟨47, false, false, [24524, 89945], []⟩,
        ⟨58502, false, false, [24524], []⟩,
        ⟨58504, false, false, [24524], []⟩,
        ⟨58493, true, false, [], [89943]⟩
      ]⟩,
    ⟨[24527, 89943], [24527, 89943], .contexts []⟩,
    ⟨[24527, 89943], [24527, 89943], .contexts []⟩,
    ⟨[89943, 1], [89941], .contexts [
        ⟨58240, false, false, [], []⟩,
        ⟨58241, false, false, [], []⟩,
        ⟨58166, false, false, [], []⟩,
        ⟨58166, false, false, [], []⟩
      ]⟩,
    ⟨[89943, 0], [89943, 1], .contexts [
        ⟨9, false, false, [89943], []⟩
      ]⟩,
    ⟨[89941, 7], [89941, 7], .contexts []⟩,
    ⟨[89941], [89941], .contexts []⟩,
    ⟨[89941, 7], [24525, 89941], .contexts [
        ⟨58510, false, false, [], []⟩,
        ⟨58167, true, false, [], [7]⟩,
        ⟨58507, true, false, [24526], [1, 7]⟩,
        ⟨58507, true, false, [24526], [1, 7]⟩,
        ⟨58506, true, false, [24526], [1, 7]⟩,
        ⟨58505, true, false, [24526], [1, 7]⟩,
        ⟨58503, true, false, [24526], [1, 7]⟩,
        ⟨502, false, false, [24526, 89943], []⟩,
        ⟨58509, false, false, [24526], []⟩,
        ⟨58508, false, false, [24526], []⟩,
        ⟨58511, false, false, [24526], []⟩,
        ⟨58498, true, false, [], [89941]⟩
      ]⟩,
    ⟨[89973], [88973, 9], .source 45051⟩,
    ⟨[88973, 9], [89973], .contexts [
        ⟨58513, true, false, [], []⟩
      ]⟩,
    ⟨[89973, 9], [88973], .contexts [
        ⟨58514, true, false, [], [9]⟩,
        ⟨46, false, false, [88973], []⟩,
        ⟨53271, false, false, [], []⟩
      ]⟩,
    ⟨[89973], [89973], .contexts []⟩,
    ⟨[89973], [89973], .contexts []⟩,
    ⟨[88973, 9], [89973], .contexts [
        ⟨58514, false, false, [], []⟩,
        ⟨58516, false, false, [], []⟩,
        ⟨58517, false, false, [], []⟩,
        ⟨58517, false, false, [], []⟩
      ]⟩,
    ⟨[23401, 83577], [23401, 83577], .contexts []⟩,
    ⟨[23401, 83577], [23401, 83577], .contexts []⟩,
    ⟨[23401, 83579], [23401, 83579], .contexts []⟩,
    ⟨[23401, 83579], [23401, 83579], .contexts []⟩,
    ⟨[89973, 5], [89973, 5], .contexts []⟩,
    ⟨[23401], [23401], .contexts []⟩,
    ⟨[23401], [23401], .contexts []⟩,
    ⟨[23401], [23401], .contexts [
        ⟨13, false, false, [], [23401]⟩,
        ⟨58524, false, false, [], []⟩,
        ⟨58525, false, false, [], []⟩
      ]⟩,
    ⟨[89973, 5], [23401, 83579], .contexts [
        ⟨58523, false, false, [], []⟩,
        ⟨58518, true, false, [], [5]⟩,
        ⟨1079, false, false, [88973], []⟩,
        ⟨1080, false, false, [88973], []⟩,
        ⟨53405, false, false, [], [9]⟩,
        ⟨58519, false, false, [], [9]⟩,
        ⟨58520, false, false, [], [9]⟩,
        ⟨58520, false, false, [], [9]⟩,
        ⟨22088, false, false, [23401], []⟩,
        ⟨58521, false, false, [], []⟩,
        ⟨58522, false, false, [], []⟩,
        ⟨26540, false, false, [23401], []⟩,
        ⟨58526, true, false, [], [83579]⟩
      ]⟩,
    ⟨[23427, 86419], [23427, 86419], .contexts []⟩,
    ⟨[23427, 86419], [23427, 86419], .contexts []⟩,
    ⟨[23427, 86419], [23427, 86419], .contexts [
        ⟨52720, false, false, [23427], []⟩
      ]⟩,
    ⟨[23427, 86419], [23427, 86419], .contexts [
        ⟨13, true, false, [], [23427, 86419]⟩
      ]⟩,
    ⟨[89973, 13], [23427, 86419], .contexts [
        ⟨58518, true, false, [], [13]⟩,
        ⟨201, false, false, [88973], []⟩,
        ⟨202, false, false, [88973], []⟩,
        ⟨53454, false, false, [], [9]⟩,
        ⟨36818, false, false, [23427], []⟩,
        ⟨58528, false, false, [], []⟩,
        ⟨58529, false, false, [], []⟩,
        ⟨58530, false, false, [], []⟩,
        ⟨58531, false, false, [], []⟩
      ]⟩,
    ⟨[24529], [23393, 23871], .source 12329⟩,
    ⟨[89973, 15], [89973, 15], .contexts []⟩,
    ⟨[24529], [24529], .contexts []⟩,
    ⟨[24529], [24529], .contexts []⟩,
    ⟨[89973, 15], [24529, 87059], .contexts [
        ⟨58534, false, false, [], []⟩,
        ⟨58518, true, false, [], [15]⟩,
        ⟨205, false, false, [88973], []⟩,
        ⟨206, false, false, [88973], []⟩,
        ⟨53395, false, false, [], [9]⟩,
        ⟨42714, false, false, [23393], []⟩,
        ⟨55264, false, false, [23393, 20775], []⟩,
        ⟨55265, true, false, [23393], [87059]⟩,
        ⟨58533, true, false, [], [87059]⟩,
        ⟨58536, true, false, [], [87059]⟩,
        ⟨58535, true, false, [], [87059]⟩,
        ⟨13, true, false, [], [24529, 87059]⟩
      ]⟩,
    ⟨[89975], [89973, 11], .source 45052⟩,
    ⟨[89973, 11], [89975], .contexts [
        ⟨58538, true, false, [], []⟩
      ]⟩,
    ⟨[89975, 11], [89973], .contexts [
        ⟨58539, true, false, [], [11]⟩,
        ⟨53, false, false, [89973], []⟩,
        ⟨58517, false, false, [], []⟩
      ]⟩,
    ⟨[89975], [89975], .contexts []⟩,
    ⟨[89975], [89975], .contexts []⟩,
    ⟨[89973, 11], [89975], .contexts [
        ⟨58539, false, false, [], []⟩,
        ⟨58541, false, false, [], []⟩,
        ⟨58542, false, false, [], []⟩,
        ⟨58542, false, false, [], []⟩
      ]⟩,
    ⟨[23401, 83581], [23401, 83581], .contexts []⟩,
    ⟨[23401, 83581], [23401, 83581], .contexts []⟩,
    ⟨[89975, 5], [89975, 5], .contexts []⟩,
    ⟨[89975, 5], [23401, 83581], .contexts [
        ⟨58546, false, false, [], []⟩,
        ⟨58543, true, false, [], [5]⟩,
        ⟨642, false, false, [89973], []⟩,
        ⟨643, false, false, [89973], []⟩,
        ⟨58523, false, false, [], [11]⟩,
        ⟨58527, false, false, [], [11]⟩,
        ⟨58521, false, false, [], [11]⟩,
        ⟨58522, false, false, [], [11]⟩,
        ⟨58522, false, false, [], [11]⟩,
        ⟨22091, false, false, [23401], []⟩,
        ⟨58544, false, false, [], []⟩,
        ⟨58545, false, false, [], []⟩,
        ⟨26546, false, false, [23401], []⟩,
        ⟨58526, true, false, [], [83581]⟩
      ]⟩,
    ⟨[24529, 87059], [24529, 87059], .contexts []⟩,
    ⟨[24529, 87059], [24529, 87059], .contexts []⟩,
    ⟨[24533], [24529, 23011], .source 12331⟩,
    ⟨[89975, 15], [89975, 15], .contexts []⟩,
    ⟨[24533], [24533], .contexts [
        ⟨13, false, false, [], [24533]⟩
      ]⟩,
    ⟨[89975, 15], [24533, 87207], .contexts [
        ⟨58551, false, false, [], []⟩,
        ⟨58543, true, false, [], [15]⟩,
        ⟨231, false, false, [89973], []⟩,
        ⟨232, false, false, [89973], []⟩,
        ⟨58534, false, false, [], [11]⟩,
        ⟨58537, false, false, [], [11]⟩,
        ⟨58548, false, false, [], [11]⟩,
        ⟨58549, false, false, [], [11]⟩,
        ⟨58549, false, false, [], [11]⟩,
        ⟨51417, false, false, [24529], []⟩,
        ⟨58550, true, false, [], [87207]⟩,
        ⟨51414, false, false, [24533], []⟩,
        ⟨58552, true, false, [], [87207]⟩
      ]⟩,
    ⟨[24535], [24532], .source 12332⟩,
    ⟨[89977], [89975, 1], .source 45053⟩,
    ⟨[89975, 1], [89977], .contexts [
        ⟨58555, true, false, [], []⟩
      ]⟩,
    ⟨[89977, 1], [89975], .contexts [
        ⟨58556, true, false, [], [1]⟩,
        ⟨8, false, false, [89975], []⟩,
        ⟨58542, false, false, [], []⟩
      ]⟩,
    ⟨[89977], [89977], .contexts []⟩,
    ⟨[89977], [89977], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 915. -/
def y322TCIndexRaw915 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89975, 1], [89977], .contexts [
        ⟨58556, false, false, [], []⟩,
        ⟨58558, false, false, [], []⟩,
        ⟨58559, false, false, [], []⟩,
        ⟨58559, false, false, [], []⟩
      ]⟩,
    ⟨[89975, 5], [23401, 83581], .contexts [
        ⟨58546, false, false, [], []⟩,
        ⟨58547, false, false, [], []⟩,
        ⟨58544, false, false, [], []⟩,
        ⟨58545, false, false, [], []⟩,
        ⟨58545, false, false, [], []⟩
      ]⟩,
    ⟨[23401, 83583], [23401, 83583], .contexts []⟩,
    ⟨[23401, 83583], [23401, 83583], .contexts []⟩,
    ⟨[89977, 5], [89977, 5], .contexts []⟩,
    ⟨[89977, 5], [23401, 83583], .contexts [
        ⟨58564, false, false, [], []⟩,
        ⟨58560, true, false, [], [5]⟩,
        ⟨98, false, false, [89975], []⟩,
        ⟨99, false, false, [89975], []⟩,
        ⟨58561, false, false, [], [1]⟩,
        ⟨22094, false, false, [23401], []⟩,
        ⟨58562, false, false, [], []⟩,
        ⟨58563, false, false, [], []⟩,
        ⟨27170, false, false, [23401], []⟩,
        ⟨58526, true, false, [], [83583]⟩
      ]⟩,
    ⟨[89975, 15], [24533, 87207], .contexts [
        ⟨58553, false, false, [], []⟩
      ]⟩,
    ⟨[24533, 87207], [24533, 87207], .contexts []⟩,
    ⟨[24533, 87207], [24533, 87207], .contexts []⟩,
    ⟨[24537], [24533, 23013], .source 12333⟩,
    ⟨[89977, 15], [89977, 15], .contexts []⟩,
    ⟨[89977, 15], [24537, 87055], .contexts [
        ⟨58570, false, false, [], []⟩,
        ⟨58560, true, false, [], [15]⟩,
        ⟨121, false, false, [89975], []⟩,
        ⟨122, false, false, [89975], []⟩,
        ⟨58551, false, false, [], [1]⟩,
        ⟨58566, false, false, [], [1]⟩,
        ⟨58567, false, false, [], [1]⟩,
        ⟨58568, false, false, [], [1]⟩,
        ⟨58568, false, false, [], [1]⟩,
        ⟨40639, false, false, [24533], []⟩,
        ⟨51381, false, false, [24533], []⟩,
        ⟨58569, true, false, [], [87055]⟩,
        ⟨13, true, false, [], [24537, 87055]⟩
      ]⟩,
    ⟨[24539], [24536], .source 12334⟩,
    ⟨[89977, 15], [24537, 87055], .contexts [
        ⟨58571, false, false, [], []⟩
      ]⟩,
    ⟨[24537, 87055], [24537, 87055], .contexts []⟩,
    ⟨[24537, 87055], [24537, 87055], .contexts []⟩,
    ⟨[89977, 15], [24537, 87055], .contexts [
        ⟨58570, false, false, [], []⟩,
        ⟨58573, false, false, [], []⟩,
        ⟨58574, false, false, [], []⟩,
        ⟨58575, false, false, [], []⟩,
        ⟨58575, false, false, [], []⟩
      ]⟩,
    ⟨[24541], [24537, 23019], .source 12335⟩,
    ⟨[24543], [24541, 24539], .source 12336⟩,
    ⟨[89977], [89977], .contexts []⟩,
    ⟨[89977, 3], [89977, 3], .contexts []⟩,
    ⟨[89977], [89977], .contexts []⟩,
    ⟨[24545], [24542], .source 12337⟩,
    ⟨[24542], [24542], .contexts []⟩,
    ⟨[89977, 3], [24545, 89977], .contexts [
        ⟨58580, false, false, [], []⟩,
        ⟨58578, false, false, [24542], [89977, 3]⟩,
        ⟨58572, false, false, [24542, 24541], [89977, 3]⟩,
        ⟨1, true, false, [24542, 24541, 24536, 89977], [3]⟩,
        ⟨58571, false, false, [24542, 24541, 24536], [15, 3]⟩,
        ⟨58577, false, false, [24542], [87055, 15, 3]⟩,
        ⟨51384, true, false, [24542, 24537], [15, 3]⟩,
        ⟨58576, true, false, [24542], [3, 15, 3]⟩,
        ⟨903, false, false, [24542, 89977], []⟩,
        ⟨58579, false, false, [24542], []⟩,
        ⟨58581, false, false, [24542], []⟩,
        ⟨58583, true, false, [], [89977]⟩,
        ⟨58583, true, false, [], [89977]⟩,
        ⟨58582, true, false, [], [89977]⟩
      ]⟩,
    ⟨[24547], [24537, 23007], .source 12338⟩,
    ⟨[24549], [24547, 21105], .source 12339⟩,
    ⟨[24551], [24548], .source 12340⟩,
    ⟨[24548], [24548], .contexts []⟩,
    ⟨[88217, 9], [24551, 89977], .contexts [
        ⟨58586, false, false, [24548], [88217, 9]⟩,
        ⟨44236, false, false, [24548, 24547], [88217, 9]⟩,
        ⟨1, true, false, [24548, 24547, 21102, 88217], [9]⟩,
        ⟨49318, false, false, [24548, 24547, 21102], [15, 9]⟩,
        ⟨58585, false, false, [24548], [85725, 15, 9]⟩,
        ⟨51368, true, false, [24548, 24537], [15, 9]⟩,
        ⟨40095, true, false, [24548, 24537], [15, 9]⟩,
        ⟨46, true, false, [24548, 24537, 87053], [15, 9]⟩,
        ⟨40094, false, false, [24548, 24537], [9, 15, 9]⟩,
        ⟨58576, true, false, [24548], [9, 15, 9]⟩,
        ⟨2656, false, false, [24548, 89977], []⟩,
        ⟨58579, false, false, [24548], []⟩,
        ⟨58581, false, false, [24548], []⟩,
        ⟨58588, true, false, [], [89977]⟩,
        ⟨58588, true, false, [], [89977]⟩,
        ⟨58587, true, false, [], [89977]⟩
      ]⟩,
    ⟨[89977, 9], [24549, 88217], .contexts [
        ⟨58589, true, false, [24550], [9]⟩,
        ⟨46, false, false, [24550, 88217], []⟩,
        ⟨58587, false, true, [], [88217]⟩
      ]⟩,
    ⟨[89979], [89977, 13], .source 45054⟩,
    ⟨[89977, 13], [89979], .contexts [
        ⟨58591, true, false, [], []⟩
      ]⟩,
    ⟨[89979, 13], [89977], .contexts [
        ⟨58592, true, false, [], [13]⟩,
        ⟨59, false, false, [89977], []⟩,
        ⟨58559, false, false, [], []⟩
      ]⟩,
    ⟨[89979], [89979], .contexts []⟩,
    ⟨[89979], [89979], .contexts []⟩,
    ⟨[89977, 13], [89979], .contexts [
        ⟨58592, false, false, [], []⟩,
        ⟨58594, false, false, [], []⟩,
        ⟨58595, false, false, [], []⟩,
        ⟨58595, false, false, [], []⟩
      ]⟩,
    ⟨[24545, 89977], [24545, 89977], .contexts []⟩,
    ⟨[24545, 89977], [24545, 89977], .contexts []⟩,
    ⟨[24545, 89979], [24545, 89979], .contexts []⟩,
    ⟨[24545, 89979], [24545, 89979], .contexts []⟩,
    ⟨[24545, 89979], [24545, 89979], .contexts []⟩,
    ⟨[89979, 3], [89979, 3], .contexts []⟩,
    ⟨[89979], [89979], .contexts []⟩,
    ⟨[24545], [24545], .contexts [
        ⟨13, false, false, [], [24545]⟩
      ]⟩,
    ⟨[89979, 3], [24545, 89979], .contexts [
        ⟨58602, false, false, [], []⟩,
        ⟨58596, true, false, [], [3]⟩,
        ⟨63, false, false, [89977], []⟩,
        ⟨65, false, false, [89977], []⟩,
        ⟨58580, false, false, [], [13]⟩,
        ⟨58584, false, false, [], [13]⟩,
        ⟨58597, false, false, [], [13]⟩,
        ⟨58598, false, false, [], [13]⟩,
        ⟨58598, false, false, [], [13]⟩,
        ⟨58592, false, false, [24545], []⟩,
        ⟨58599, false, false, [], []⟩,
        ⟨58600, false, false, [], []⟩,
        ⟨58601, false, false, [], []⟩,
        ⟨58603, false, false, [24545], []⟩,
        ⟨58604, true, false, [], [89979]⟩
      ]⟩,
    ⟨[23401, 83585], [23401, 83585], .contexts []⟩,
    ⟨[23401, 83585], [23401, 83585], .contexts []⟩,
    ⟨[89979, 5], [89979, 5], .contexts []⟩,
    ⟨[83585], [83585], .contexts []⟩,
    ⟨[89979, 5], [23401, 83585], .contexts [
        ⟨58608, false, false, [], []⟩,
        ⟨58596, true, false, [], [5]⟩,
        ⟨68, false, false, [89977], []⟩,
        ⟨69, false, false, [89977], []⟩,
        ⟨58564, false, false, [], [13]⟩,
        ⟨58565, false, false, [], [13]⟩,
        ⟨58562, false, false, [], [13]⟩,
        ⟨58563, false, false, [], [13]⟩,
        ⟨58563, false, false, [], [13]⟩,
        ⟨22098, false, false, [23401], []⟩,
        ⟨58606, false, false, [], []⟩,
        ⟨58607, false, false, [], []⟩,
        ⟨58609, false, false, [23401], []⟩,
        ⟨58526, true, false, [], [83585]⟩
      ]⟩,
    ⟨[24549, 88217], [24549, 88217], .contexts []⟩,
    ⟨[24549, 88217], [24549, 88217], .contexts []⟩,
    ⟨[24549, 88219], [24549, 88219], .contexts []⟩,
    ⟨[24549, 88219], [24549, 88219], .contexts []⟩,
    ⟨[89979, 9], [89979, 9], .contexts []⟩,
    ⟨[24549], [24549], .contexts [
        ⟨13, false, false, [], [24549]⟩
      ]⟩,
    ⟨[89979, 9], [24549, 88219], .contexts [
        ⟨58615, false, false, [], []⟩,
        ⟨58596, true, false, [], [9]⟩,
        ⟨77, false, false, [89977], []⟩,
        ⟨78, false, false, [89977], []⟩,
        ⟨58590, false, false, [], [13]⟩,
        ⟨58611, false, false, [], [13]⟩,
        ⟨58612, false, false, [], [13]⟩,
        ⟨58612, false, false, [], [13]⟩,
        ⟨49327, false, false, [24549], []⟩,
        ⟨58613, false, false, [], []⟩,
        ⟨58614, false, false, [], []⟩,
        ⟨49337, false, false, [24549], []⟩,
        ⟨58616, true, false, [], [88219]⟩
      ]⟩,
    ⟨[89979, 9], [24549, 88219], .contexts [
        ⟨58615, false, false, [], []⟩,
        ⟨58617, false, false, [], []⟩,
        ⟨58613, false, false, [], []⟩,
        ⟨58614, false, false, [], []⟩,
        ⟨58614, false, false, [], []⟩
      ]⟩,
    ⟨[24553], [24549, 23965], .source 12341⟩,
    ⟨[24555], [24553, 23923], .source 12342⟩,
    ⟨[24555, 87555], [24555, 87555], .contexts []⟩,
    ⟨[24555, 87555], [24555, 87555], .contexts []⟩,
    ⟨[89979, 9, 11, 9, 11, 9], [24555, 87555], .contexts [
        ⟨58618, false, false, [], [11, 9, 11, 9]⟩,
        ⟨55453, true, false, [24549, 23962], [11, 9, 11, 9]⟩,
        ⟨53, false, false, [24549, 23962, 89297], [9, 11, 9]⟩,
        ⟨55454, true, false, [24549], [89297, 9, 11, 9]⟩,
        ⟨58619, true, false, [], [89297, 9, 11, 9]⟩,
        ⟨55109, false, false, [24553], [11, 9]⟩,
        ⟨55395, false, false, [24553], [11, 9]⟩,
        ⟨55393, false, false, [24553], [11, 9]⟩,
        ⟨58620, true, false, [], [87559, 11, 9]⟩,
        ⟨43971, false, false, [24555], [9]⟩,
        ⟨43967, false, false, [24555], []⟩,
        ⟨58621, false, false, [], []⟩,
        ⟨58622, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 916. -/
def y322TCIndexRaw916 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[87555, 11], [87555, 11], .contexts []⟩,
    ⟨[24557], [24554], .source 12343⟩,
    ⟨[24554], [24554], .contexts []⟩,
    ⟨[87555, 11], [24557, 89979], .contexts [
        ⟨58624, false, false, [], []⟩,
        ⟨58623, true, false, [24554], [11]⟩,
        ⟨1453, false, false, [24554, 89979], []⟩,
        ⟨58603, false, false, [24554], []⟩,
        ⟨58626, true, false, [], [89979]⟩,
        ⟨58626, true, false, [], [89979]⟩,
        ⟨58625, true, false, [], [89979]⟩
      ]⟩,
    ⟨[24555], [24556], .contexts [
        ⟨58625, true, true, [], []⟩
      ]⟩,
    ⟨[89979, 11], [24555, 87555], .contexts [
        ⟨58627, true, false, [24556], [11]⟩,
        ⟨53, false, false, [24556, 87555], []⟩,
        ⟨58628, true, false, [], [87555]⟩
      ]⟩,
    ⟨[89981], [89979, 15], .source 45055⟩,
    ⟨[89979, 15], [89981], .contexts [
        ⟨58630, true, false, [], []⟩
      ]⟩,
    ⟨[89981, 15], [89979], .contexts [
        ⟨58631, true, false, [], [15]⟩,
        ⟨1, false, false, [89979], []⟩,
        ⟨58595, false, false, [], []⟩
      ]⟩,
    ⟨[89981], [89981], .contexts []⟩,
    ⟨[89981], [89981], .contexts []⟩,
    ⟨[89979, 15], [89981], .contexts [
        ⟨58631, false, false, [], []⟩,
        ⟨58633, false, false, [], []⟩,
        ⟨58634, false, false, [], []⟩,
        ⟨58634, false, false, [], []⟩
      ]⟩,
    ⟨[24545, 89981], [24545, 89981], .contexts []⟩,
    ⟨[24545, 89981], [24545, 89981], .contexts []⟩,
    ⟨[24545, 89981], [24545, 89981], .contexts []⟩,
    ⟨[89981, 3], [24545, 89981], .contexts [
        ⟨58635, true, false, [], [3]⟩,
        ⟨19, false, false, [89979], []⟩,
        ⟨22, false, false, [89979], []⟩,
        ⟨58602, false, false, [], [15]⟩,
        ⟨58605, false, false, [], [15]⟩,
        ⟨58599, false, false, [], [15]⟩,
        ⟨58601, false, false, [], [15]⟩,
        ⟨58601, false, false, [], [15]⟩,
        ⟨58631, false, false, [24545], []⟩,
        ⟨58636, false, false, [], []⟩,
        ⟨58637, false, false, [], []⟩,
        ⟨58638, false, false, [], []⟩,
        ⟨58604, true, false, [], [89981]⟩
      ]⟩,
    ⟨[23401, 83587], [23401, 83587], .contexts []⟩,
    ⟨[23401, 83587], [23401, 83587], .contexts []⟩,
    ⟨[89981, 5], [89981, 5], .contexts []⟩,
    ⟨[89981, 5], [23401, 83587], .contexts [
        ⟨58642, false, false, [], []⟩,
        ⟨58635, true, false, [], [5]⟩,
        ⟨27, false, false, [89979], []⟩,
        ⟨30, false, false, [89979], []⟩,
        ⟨58608, false, false, [], [15]⟩,
        ⟨58610, false, false, [], [15]⟩,
        ⟨58606, false, false, [], [15]⟩,
        ⟨58607, false, false, [], [15]⟩,
        ⟨58607, false, false, [], [15]⟩,
        ⟨22101, false, false, [23401], []⟩,
        ⟨58640, false, false, [], []⟩,
        ⟨58641, false, false, [], []⟩,
        ⟨27185, false, false, [23401], []⟩,
        ⟨58526, true, false, [], [83587]⟩
      ]⟩,
    ⟨[24549, 88221], [24549, 88221], .contexts []⟩,
    ⟨[24549, 88221], [24549, 88221], .contexts []⟩,
    ⟨[89981, 9], [24549, 88221], .contexts [
        ⟨58635, true, false, [], [9]⟩,
        ⟨45, false, false, [89979], []⟩,
        ⟨48, false, false, [89979], []⟩,
        ⟨58618, false, false, [], [15]⟩,
        ⟨49340, false, false, [24549], []⟩,
        ⟨58644, false, false, [], []⟩,
        ⟨58645, false, false, [], []⟩,
        ⟨49349, false, false, [24549], []⟩,
        ⟨58616, true, false, [], [88221]⟩
      ]⟩,
    ⟨[24559], [24537, 23011], .source 12344⟩,
    ⟨[89981, 13], [24559, 87213], .contexts [
        ⟨58635, true, false, [], [13]⟩,
        ⟨259, false, false, [89979], []⟩,
        ⟨262, false, false, [89979], []⟩,
        ⟨58593, false, false, [], [15, 13, 15]⟩,
        ⟨58558, false, false, [], [15, 13, 15]⟩,
        ⟨58559, false, false, [], [15, 13, 15]⟩,
        ⟨58559, false, false, [], [15, 13, 15]⟩,
        ⟨58573, false, false, [], [13, 15]⟩,
        ⟨58574, false, false, [], [13, 15]⟩,
        ⟨58575, false, false, [], [13, 15]⟩,
        ⟨58575, false, false, [], [13, 15]⟩,
        ⟨51385, false, false, [24537], [15]⟩,
        ⟨58647, true, false, [], [87211, 15]⟩,
        ⟨40685, false, false, [24559], []⟩,
        ⟨40693, false, false, [24559], []⟩
      ]⟩,
    ⟨[24561], [24558], .source 12345⟩,
    ⟨[87213, 13], [24561, 89981], .contexts [
        ⟨13, false, false, [24558], [24559, 87213, 13]⟩,
        ⟨58648, true, false, [24558], [13]⟩,
        ⟨59, false, false, [24558, 89981], []⟩,
        ⟨58649, true, false, [], [89981]⟩
      ]⟩,
    ⟨[89983], [89981, 1], .source 45056⟩,
    ⟨[89981, 1], [89983], .contexts [
        ⟨58651, true, false, [], []⟩
      ]⟩,
    ⟨[89983, 1], [89981], .contexts [
        ⟨58652, true, false, [], [1]⟩,
        ⟨8, false, false, [89981], []⟩,
        ⟨58634, false, false, [], []⟩
      ]⟩,
    ⟨[89981, 1], [89983], .contexts [
        ⟨58652, false, false, [], []⟩
      ]⟩,
    ⟨[89983], [89983], .contexts []⟩,
    ⟨[89983], [89983], .contexts []⟩,
    ⟨[89981, 1], [89983], .contexts [
        ⟨58654, false, false, [], []⟩,
        ⟨58655, false, false, [], []⟩,
        ⟨58656, false, false, [], []⟩,
        ⟨58656, false, false, [], []⟩
      ]⟩,
    ⟨[89981, 5], [23401, 83587], .contexts [
        ⟨58642, false, false, [], []⟩,
        ⟨58643, false, false, [], []⟩,
        ⟨58640, false, false, [], []⟩,
        ⟨58641, false, false, [], []⟩,
        ⟨58641, false, false, [], []⟩
      ]⟩,
    ⟨[23401, 83589], [23401, 83589], .contexts []⟩,
    ⟨[23401, 83589], [23401, 83589], .contexts []⟩,
    ⟨[83589], [83589], .contexts []⟩,
    ⟨[89983, 5], [23401, 83589], .contexts [
        ⟨58657, true, false, [], [5]⟩,
        ⟨98, false, false, [89981], []⟩,
        ⟨99, false, false, [89981], []⟩,
        ⟨58658, false, false, [], [1]⟩,
        ⟨22105, false, false, [23401], []⟩,
        ⟨58659, false, false, [], []⟩,
        ⟨58660, false, false, [], []⟩,
        ⟨58661, false, false, [23401], []⟩,
        ⟨58526, true, false, [], [83589]⟩
      ]⟩,
    ⟨[89985], [89983, 3], .source 45057⟩,
    ⟨[89983, 3], [89985], .contexts [
        ⟨58663, true, false, [], []⟩
      ]⟩,
    ⟨[89985, 3], [89983], .contexts [
        ⟨58664, true, false, [], [3]⟩,
        ⟨20, false, false, [89983], []⟩,
        ⟨58656, false, false, [], []⟩
      ]⟩,
    ⟨[89985], [89985], .contexts []⟩,
    ⟨[89985], [89985], .contexts []⟩,
    ⟨[24545, 89983], [24545, 89983], .contexts []⟩,
    ⟨[24545, 89983], [24545, 89983], .contexts []⟩,
    ⟨[24545, 89983], [24545, 89983], .contexts []⟩,
    ⟨[24545, 89985], [24545, 89985], .contexts []⟩,
    ⟨[24545, 89985], [24545, 89985], .contexts []⟩,
    ⟨[24545, 89985], [24545, 89985], .contexts []⟩,
    ⟨[89985, 1], [89985, 1], .contexts []⟩,
    ⟨[89985], [89985], .contexts []⟩,
    ⟨[89985, 1], [24545, 89985], .contexts [
        ⟨58674, false, false, [], []⟩,
        ⟨58667, true, false, [], [1]⟩,
        ⟨58667, true, false, [], [1]⟩,
        ⟨58666, true, false, [], [1]⟩,
        ⟨58664, true, false, [], [1]⟩,
        ⟨130, false, false, [89983], []⟩,
        ⟨133, false, false, [89983], []⟩,
        ⟨58653, false, false, [], [3, 1, 3]⟩,
        ⟨58633, false, false, [], [3, 1, 3]⟩,
        ⟨58634, false, false, [], [3, 1, 3]⟩,
        ⟨58634, false, false, [], [3, 1, 3]⟩,
        ⟨58639, false, false, [], [1, 3]⟩,
        ⟨58636, false, false, [], [1, 3]⟩,
        ⟨58638, false, false, [], [1, 3]⟩,
        ⟨58638, false, false, [], [1, 3]⟩,
        ⟨58652, false, false, [24545], [3]⟩,
        ⟨58668, false, false, [], [3]⟩,
        ⟨58669, false, false, [], [3]⟩,
        ⟨58670, false, false, [], [3]⟩,
        ⟨58664, false, false, [24545], []⟩,
        ⟨58671, false, false, [], []⟩,
        ⟨58672, false, false, [], []⟩,
        ⟨58673, false, false, [], []⟩,
        ⟨58675, false, false, [24545], []⟩
      ]⟩,
    ⟨[89985, 1], [24545, 89985], .contexts [
        ⟨58676, false, false, [], []⟩,
        ⟨58604, true, false, [], [89985]⟩
      ]⟩,
    ⟨[89987], [89985, 5], .source 45058⟩,
    ⟨[89985, 5], [89987], .contexts [
        ⟨58678, true, false, [], []⟩
      ]⟩,
    ⟨[89987, 5], [89985], .contexts [
        ⟨58679, true, false, [], [5]⟩,
        ⟨28, false, false, [89985], []⟩,
        ⟨58667, false, false, [], []⟩
      ]⟩,
    ⟨[89987], [89987], .contexts []⟩,
    ⟨[89987], [89987], .contexts []⟩,
    ⟨[89985, 5], [89987], .contexts [
        ⟨58679, false, false, [], []⟩,
        ⟨58681, false, false, [], []⟩,
        ⟨58682, false, false, [], []⟩,
        ⟨58682, false, false, [], []⟩
      ]⟩,
    ⟨[24545, 89987], [24545, 89987], .contexts []⟩,
    ⟨[24545, 89987], [24545, 89987], .contexts []⟩,
    ⟨[89987, 1], [89987, 1], .contexts []⟩,
    ⟨[89987], [89987], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 917. -/
def y322TCIndexRaw917 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89987, 1], [24545, 89987], .contexts [
        ⟨58686, false, false, [], []⟩,
        ⟨58683, true, false, [], [1]⟩,
        ⟨161, false, false, [89985], []⟩,
        ⟨162, false, false, [89985], []⟩,
        ⟨58674, false, false, [], [5]⟩,
        ⟨58677, false, false, [], [5]⟩,
        ⟨58671, false, false, [], [5]⟩,
        ⟨58673, false, false, [], [5]⟩,
        ⟨58673, false, false, [], [5]⟩,
        ⟨58679, false, false, [24545], []⟩,
        ⟨58684, false, false, [], []⟩,
        ⟨58685, false, false, [], []⟩,
        ⟨58687, false, false, [24545], []⟩,
        ⟨58604, true, false, [], [89987]⟩
      ]⟩,
    ⟨[23401, 83593], [23401, 83593], .contexts []⟩,
    ⟨[23401, 83593], [23401, 83593], .contexts []⟩,
    ⟨[89987, 3], [89987, 3], .contexts []⟩,
    ⟨[89987, 3], [23401, 83593], .contexts [
        ⟨58691, false, false, [], []⟩,
        ⟨58683, true, false, [], [3]⟩,
        ⟨166, false, false, [89985], []⟩,
        ⟨169, false, false, [89985], []⟩,
        ⟨58665, false, false, [], [5, 3, 5]⟩,
        ⟨58655, false, false, [], [5, 3, 5]⟩,
        ⟨58656, false, false, [], [5, 3, 5]⟩,
        ⟨58656, false, false, [], [5, 3, 5]⟩,
        ⟨58662, false, false, [], [3, 5]⟩,
        ⟨58659, false, false, [], [3, 5]⟩,
        ⟨58660, false, false, [], [3, 5]⟩,
        ⟨58660, false, false, [], [3, 5]⟩,
        ⟨22108, false, false, [23401], [5]⟩,
        ⟨22110, false, false, [23401], []⟩,
        ⟨58689, false, false, [], []⟩,
        ⟨58690, false, false, [], []⟩,
        ⟨43704, false, false, [23401], []⟩
      ]⟩,
    ⟨[89987, 3], [23401, 83593], .contexts [
        ⟨58692, false, false, [], []⟩,
        ⟨58526, true, false, [], [83593]⟩
      ]⟩,
    ⟨[83593, 3], [23403, 89987], .contexts [
        ⟨58693, true, false, [23400], [3]⟩,
        ⟨20, false, false, [23400, 89987], []⟩,
        ⟨53401, true, false, [], [89987]⟩
      ]⟩,
    ⟨[89987, 1], [24545, 89987], .contexts [
        ⟨58688, false, false, [], []⟩
      ]⟩,
    ⟨[24563], [24545, 23401], .source 12346⟩,
    ⟨[89987, 3], [23401, 83593], .contexts [
        ⟨58691, false, false, [], []⟩,
        ⟨58693, false, false, [], []⟩,
        ⟨58689, false, false, [], []⟩,
        ⟨58690, false, false, [], []⟩,
        ⟨58690, false, false, [], []⟩
      ]⟩,
    ⟨[83595, 3], [83595, 3], .contexts []⟩,
    ⟨[24565], [24562], .source 12347⟩,
    ⟨[24567], [24565, 23401], .source 12348⟩,
    ⟨[83595, 3], [24567, 83595], .contexts [
        ⟨58698, false, false, [], []⟩,
        ⟨22113, true, false, [], [3]⟩,
        ⟨58696, false, false, [24562], [83593, 1, 3]⟩,
        ⟨58693, true, false, [24562, 24545], [1, 3]⟩,
        ⟨58685, true, false, [24562], [3, 1, 3]⟩,
        ⟨58685, true, false, [24562], [3, 1, 3]⟩,
        ⟨58684, true, false, [24562], [3, 1, 3]⟩,
        ⟨58695, true, false, [24562], [3, 1, 3]⟩,
        ⟨58686, true, false, [24562], [3, 1, 3]⟩,
        ⟨484, false, false, [24562, 89987], []⟩,
        ⟨485, false, false, [24562, 89987], []⟩,
        ⟨58697, false, false, [24562], [1]⟩,
        ⟨22113, false, false, [24562, 23401], []⟩,
        ⟨43697, false, false, [24562, 23401], []⟩,
        ⟨58699, true, false, [], [23401, 83595]⟩,
        ⟨58700, true, false, [], [83595]⟩
      ]⟩,
    ⟨[24569], [23401, 20999], .source 12349⟩,
    ⟨[24571], [24569, 23403], .source 12350⟩,
    ⟨[89987, 7], [89987, 7], .contexts []⟩,
    ⟨[24573], [24570], .source 12351⟩,
    ⟨[24570], [24570], .contexts []⟩,
    ⟨[89987, 7], [24573, 89987], .contexts [
        ⟨58704, false, false, [], []⟩,
        ⟨58703, false, false, [24570], [89987, 7]⟩,
        ⟨58694, true, false, [24570, 24569], [7]⟩,
        ⟨58702, false, false, [24570], [83593, 3, 7]⟩,
        ⟨43705, true, false, [24570, 23401], [3, 7]⟩,
        ⟨58697, true, false, [24570], [7, 3, 7]⟩,
        ⟨18135, false, false, [24570, 89987], []⟩,
        ⟨58687, false, false, [24570], []⟩,
        ⟨58706, true, false, [], [89987]⟩,
        ⟨58706, true, false, [], [89987]⟩,
        ⟨58705, true, false, [], [89987]⟩
      ]⟩,
    ⟨[24567, 83595], [24567, 83595], .contexts []⟩,
    ⟨[24567, 83595], [24567, 83595], .contexts []⟩,
    ⟨[83595, 9], [83597], .contexts [
        ⟨22117, false, false, [], []⟩
      ]⟩,
    ⟨[83597, 3], [83597, 3], .contexts []⟩,
    ⟨[24575], [24566], .source 12352⟩,
    ⟨[24566], [24566], .contexts []⟩,
    ⟨[24575, 83597], [24575, 83597], .contexts []⟩,
    ⟨[83597, 3], [24575, 83597], .contexts [
        ⟨58711, false, false, [], []⟩,
        ⟨58711, false, false, [], []⟩,
        ⟨22117, true, false, [], [3]⟩,
        ⟨58709, true, false, [24566], [9, 3]⟩,
        ⟨58709, true, false, [24566], [9, 3]⟩,
        ⟨58708, true, false, [24566], [9, 3]⟩,
        ⟨58701, true, false, [24566], [9, 3]⟩,
        ⟨58698, true, false, [24566], [9, 3]⟩,
        ⟨573, false, false, [24566, 83595], []⟩,
        ⟨47, false, false, [24566, 83595], []⟩,
        ⟨58710, false, false, [24566], []⟩,
        ⟨22275, false, false, [24566], []⟩,
        ⟨22122, false, false, [24566], []⟩,
        ⟨22122, false, false, [24566], []⟩,
        ⟨43693, false, false, [24566], []⟩,
        ⟨58713, true, false, [], [83597]⟩,
        ⟨58713, true, false, [], [83597]⟩,
        ⟨58712, true, false, [], [83597]⟩,
        ⟨58714, false, false, [], []⟩,
        ⟨58714, false, false, [], []⟩
      ]⟩,
    ⟨[24574], [24574], .contexts []⟩,
    ⟨[83599, 3], [24567, 83599], .contexts [
        ⟨22121, true, false, [], [3]⟩,
        ⟨58715, true, false, [24574], [11, 3]⟩,
        ⟨545, false, false, [24574, 83597], []⟩,
        ⟨54, false, false, [24574, 83597], []⟩,
        ⟨22121, false, false, [24574], []⟩,
        ⟨22274, false, false, [24574], []⟩,
        ⟨22126, false, false, [24574], []⟩,
        ⟨22126, false, false, [24574], []⟩,
        ⟨43677, false, false, [24574], []⟩,
        ⟨58716, true, false, [], [83599]⟩,
        ⟨58716, true, false, [], [83599]⟩,
        ⟨58712, false, true, [], [83599]⟩
      ]⟩,
    ⟨[89989], [89987, 9], .source 45059⟩,
    ⟨[89987, 9], [89989], .contexts [
        ⟨58718, true, false, [], []⟩
      ]⟩,
    ⟨[89989, 9], [89987], .contexts [
        ⟨58719, true, false, [], [9]⟩,
        ⟨46, false, false, [89987], []⟩,
        ⟨58682, false, false, [], []⟩
      ]⟩,
    ⟨[89989], [89989], .contexts []⟩,
    ⟨[89989], [89989], .contexts []⟩,
    ⟨[24573, 89987], [24573, 89987], .contexts []⟩,
    ⟨[24573, 89987], [24573, 89987], .contexts []⟩,
    ⟨[24573, 89989], [24573, 89989], .contexts []⟩,
    ⟨[24573, 89989], [24573, 89989], .contexts []⟩,
    ⟨[89989, 7], [89989, 7], .contexts []⟩,
    ⟨[89989], [89989], .contexts []⟩,
    ⟨[24573], [24573], .contexts [
        ⟨13, false, false, [], [24573]⟩
      ]⟩,
    ⟨[89989, 7], [24573, 89989], .contexts [
        ⟨58727, false, false, [], []⟩,
        ⟨58722, true, false, [], [7]⟩,
        ⟨58722, true, false, [], [7]⟩,
        ⟨58721, true, false, [], [7]⟩,
        ⟨58719, true, false, [], [7]⟩,
        ⟨1084, false, false, [89987], []⟩,
        ⟨1085, false, false, [89987], []⟩,
        ⟨58704, false, false, [], [9]⟩,
        ⟨58707, false, false, [], [9]⟩,
        ⟨58723, false, false, [], [9]⟩,
        ⟨58724, false, false, [], [9]⟩,
        ⟨58724, false, false, [], [9]⟩,
        ⟨58719, false, false, [24573], []⟩,
        ⟨58725, false, false, [], []⟩,
        ⟨58726, false, false, [], []⟩,
        ⟨58728, false, false, [24573], []⟩,
        ⟨58729, true, false, [], [89989]⟩
      ]⟩,
    ⟨[89991], [89989, 11], .source 45060⟩,
    ⟨[89989, 11], [89991], .contexts [
        ⟨58731, true, false, [], []⟩
      ]⟩,
    ⟨[89989, 11], [89991], .contexts [
        ⟨58732, false, false, [], []⟩
      ]⟩,
    ⟨[89991], [89991], .contexts []⟩,
    ⟨[89991], [89991], .contexts []⟩,
    ⟨[89989, 7], [24573, 89989], .contexts [
        ⟨58727, false, false, [], []⟩,
        ⟨58730, false, false, [], []⟩,
        ⟨58725, false, false, [], []⟩,
        ⟨58726, false, false, [], []⟩,
        ⟨58726, false, false, [], []⟩
      ]⟩,
    ⟨[24573, 89991], [24573, 89991], .contexts []⟩,
    ⟨[24573, 89991], [24573, 89991], .contexts []⟩,
    ⟨[89991, 7], [89991, 7], .contexts []⟩,
    ⟨[89991], [89991], .contexts []⟩,
    ⟨[89993], [89991, 1], .source 45061⟩,
    ⟨[89991, 1], [89993], .contexts [
        ⟨58741, true, false, [], []⟩
      ]⟩,
    ⟨[89993, 1], [89991], .contexts [
        ⟨58742, true, false, [], [1]⟩,
        ⟨8, false, false, [89991], []⟩,
        ⟨58735, false, false, [], []⟩
      ]⟩,
    ⟨[89993], [89993], .contexts []⟩,
    ⟨[89993], [89993], .contexts []⟩,
    ⟨[24573, 89993], [24573, 89993], .contexts []⟩,
    ⟨[24573, 89993], [24573, 89993], .contexts []⟩,
    ⟨[89993, 7], [24573, 89993], .contexts [
        ⟨58745, true, false, [], [7]⟩,
        ⟨58745, true, false, [], [7]⟩,
        ⟨58744, true, false, [], [7]⟩,
        ⟨58742, true, false, [], [7]⟩,
        ⟨104, false, false, [89991], []⟩,
        ⟨105, false, false, [89991], []⟩,
        ⟨58739, false, false, [], [1]⟩,
        ⟨58739, false, false, [], [1]⟩,
        ⟨58735, true, false, [], [7, 1]⟩,
        ⟨58735, true, false, [], [7, 1]⟩,
        ⟨58734, true, false, [], [7, 1]⟩,
        ⟨58733, true, false, [], [7, 1]⟩,
        ⟨647, false, false, [89989], [1]⟩,
        ⟨648, false, false, [89989], [1]⟩,
        ⟨58736, false, false, [], [11, 1]⟩,
        ⟨58732, false, false, [24573], [1]⟩,
        ⟨58737, false, false, [], [1]⟩,
        ⟨58738, false, false, [], [1]⟩,
        ⟨58740, false, false, [24573], [1]⟩,
        ⟨58729, true, false, [], [89991, 1]⟩,
        ⟨58737, false, false, [], [1]⟩,
        ⟨58738, false, false, [], [1]⟩,
        ⟨58738, false, false, [], [1]⟩,
        ⟨58742, false, false, [24573], []⟩,
        ⟨58746, false, false, [], []⟩,
        ⟨58747, false, false, [], []⟩
      ]⟩,
    ⟨[89993, 7], [89993, 7], .contexts []⟩,
    ⟨[89993], [89993], .contexts []⟩,
    ⟨[89993, 7], [24573, 89993], .contexts [
        ⟨58749, false, false, [], []⟩,
        ⟨58748, false, false, [], []⟩,
        ⟨58750, false, false, [24573], []⟩,
        ⟨58729, true, false, [], [89993]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 918. -/
def y322TCIndexRaw918 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89995], [89993, 13], .source 45062⟩,
    ⟨[89993, 13], [89995], .contexts [
        ⟨58752, true, false, [], []⟩
      ]⟩,
    ⟨[89995, 13], [89993], .contexts [
        ⟨58753, true, false, [], [13]⟩,
        ⟨59, false, false, [89993], []⟩,
        ⟨58745, false, false, [], []⟩
      ]⟩,
    ⟨[89995], [89995], .contexts []⟩,
    ⟨[89995], [89995], .contexts []⟩,
    ⟨[89993, 13], [89995], .contexts [
        ⟨58753, false, false, [], []⟩,
        ⟨58755, false, false, [], []⟩,
        ⟨58756, false, false, [], []⟩,
        ⟨58756, false, false, [], []⟩
      ]⟩,
    ⟨[89993, 7], [24573, 89993], .contexts [
        ⟨58749, false, false, [], []⟩,
        ⟨58751, false, false, [], []⟩,
        ⟨58746, false, false, [], []⟩,
        ⟨58747, false, false, [], []⟩,
        ⟨58747, false, false, [], []⟩
      ]⟩,
    ⟨[24573, 89995], [24573, 89995], .contexts []⟩,
    ⟨[24573, 89995], [24573, 89995], .contexts []⟩,
    ⟨[89995, 7], [89995, 7], .contexts []⟩,
    ⟨[89995], [89995], .contexts []⟩,
    ⟨[89995, 7], [24573, 89995], .contexts [
        ⟨58761, false, false, [], []⟩,
        ⟨58757, true, false, [], [7]⟩,
        ⟨73, false, false, [89993], []⟩,
        ⟨74, false, false, [89993], []⟩,
        ⟨58758, false, false, [], [13]⟩,
        ⟨58753, false, false, [24573], []⟩,
        ⟨58759, false, false, [], []⟩,
        ⟨58760, false, false, [], []⟩,
        ⟨58762, false, false, [24573], []⟩,
        ⟨58729, true, false, [], [89995]⟩
      ]⟩,
    ⟨[89997], [89995, 15], .source 45063⟩,
    ⟨[89995, 15], [89997], .contexts [
        ⟨58764, true, false, [], []⟩
      ]⟩,
    ⟨[89995, 15], [89997], .contexts [
        ⟨58765, false, false, [], []⟩
      ]⟩,
    ⟨[89995, 15], [89997], .contexts [
        ⟨58766, false, false, [], []⟩
      ]⟩,
    ⟨[89997], [89997], .contexts []⟩,
    ⟨[89997], [89997], .contexts []⟩,
    ⟨[89995, 15], [89997], .contexts [
        ⟨58767, false, false, [], []⟩,
        ⟨58768, false, false, [], []⟩,
        ⟨58769, false, false, [], []⟩,
        ⟨58769, false, false, [], []⟩
      ]⟩,
    ⟨[24573, 89997], [24573, 89997], .contexts []⟩,
    ⟨[24573, 89997], [24573, 89997], .contexts []⟩,
    ⟨[89997, 7], [89997, 7], .contexts []⟩,
    ⟨[89997], [89997], .contexts []⟩,
    ⟨[89999], [89997, 1], .source 45064⟩,
    ⟨[89997, 1], [89999], .contexts [
        ⟨58775, true, false, [], []⟩
      ]⟩,
    ⟨[89999, 1], [89997], .contexts [
        ⟨58776, true, false, [], [1]⟩,
        ⟨8, false, false, [89997], []⟩,
        ⟨58769, false, false, [], []⟩
      ]⟩,
    ⟨[89999], [89999], .contexts []⟩,
    ⟨[89999], [89999], .contexts []⟩,
    ⟨[89997, 1], [89999], .contexts [
        ⟨58776, false, false, [], []⟩,
        ⟨58778, false, false, [], []⟩,
        ⟨58779, false, false, [], []⟩,
        ⟨58779, false, false, [], []⟩
      ]⟩,
    ⟨[24573, 89999], [24573, 89999], .contexts []⟩,
    ⟨[89997, 7, 1], [24573, 89999], .contexts [
        ⟨58773, false, false, [], [1]⟩,
        ⟨58773, false, false, [], [1]⟩,
        ⟨58770, true, false, [], [7, 1]⟩,
        ⟨37, false, false, [89995], [1]⟩,
        ⟨40, false, false, [89995], [1]⟩,
        ⟨58761, false, false, [], [15, 1]⟩,
        ⟨58763, false, false, [], [15, 1]⟩,
        ⟨58759, false, false, [], [15, 1]⟩,
        ⟨58760, false, false, [], [15, 1]⟩,
        ⟨58760, false, false, [], [15, 1]⟩,
        ⟨58765, false, false, [24573], [1]⟩,
        ⟨58771, false, false, [], [1]⟩,
        ⟨58772, false, false, [], [1]⟩,
        ⟨58774, false, false, [24573], [1]⟩,
        ⟨58729, true, false, [], [89997, 1]⟩,
        ⟨58771, false, false, [], [1]⟩,
        ⟨58772, false, false, [], [1]⟩,
        ⟨58772, false, false, [], [1]⟩,
        ⟨58776, false, false, [24573], []⟩,
        ⟨58781, false, false, [], []⟩
      ]⟩,
    ⟨[24573, 89999], [24573, 89999], .contexts []⟩,
    ⟨[89999, 7], [89999, 7], .contexts []⟩,
    ⟨[89999], [89999], .contexts []⟩,
    ⟨[89999, 7], [24573, 89999], .contexts [
        ⟨58784, false, false, [], []⟩,
        ⟨58780, true, false, [], [7]⟩,
        ⟨104, false, false, [89997], []⟩,
        ⟨105, false, false, [89997], []⟩,
        ⟨58782, false, false, [], []⟩,
        ⟨58783, false, false, [], []⟩,
        ⟨58785, false, false, [24573], []⟩,
        ⟨58729, true, false, [], [89999]⟩
      ]⟩,
    ⟨[90001], [89999, 3], .source 45065⟩,
    ⟨[89999, 3], [90001], .contexts [
        ⟨58787, true, false, [], []⟩
      ]⟩,
    ⟨[90001, 3], [89999], .contexts [
        ⟨58788, true, false, [], [3]⟩,
        ⟨20, false, false, [89999], []⟩,
        ⟨58779, false, false, [], []⟩
      ]⟩,
    ⟨[89999, 3], [90001], .contexts [
        ⟨58788, false, false, [], []⟩
      ]⟩,
    ⟨[90001], [90001], .contexts []⟩,
    ⟨[90001], [90001], .contexts []⟩,
    ⟨[89999, 3], [90001], .contexts [
        ⟨58790, false, false, [], []⟩,
        ⟨58791, false, false, [], []⟩,
        ⟨58792, false, false, [], []⟩,
        ⟨58792, false, false, [], []⟩
      ]⟩,
    ⟨[24573, 90001], [24573, 90001], .contexts []⟩,
    ⟨[90001], [90001], .contexts []⟩,
    ⟨[90003], [90001, 5], .source 45066⟩,
    ⟨[90001, 5], [90003], .contexts [
        ⟨58796, true, false, [], []⟩
      ]⟩,
    ⟨[90003, 5], [90001], .contexts [
        ⟨58797, true, false, [], [5]⟩,
        ⟨28, false, false, [90001], []⟩,
        ⟨58792, false, false, [], []⟩
      ]⟩,
    ⟨[90005], [90003, 1], .source 45067⟩,
    ⟨[90003, 1], [90005], .contexts [
        ⟨58799, true, false, [], []⟩
      ]⟩,
    ⟨[90003], [90003], .contexts []⟩,
    ⟨[90007], [90005, 9], .source 45068⟩,
    ⟨[90005, 9], [90007], .contexts [
        ⟨58802, true, false, [], []⟩
      ]⟩,
    ⟨[90005], [90005], .contexts []⟩,
    ⟨[90009], [90007, 11], .source 45069⟩,
    ⟨[90007, 11], [90009], .contexts [
        ⟨58805, true, false, [], []⟩
      ]⟩,
    ⟨[90007], [90007], .contexts []⟩,
    ⟨[90011], [90009, 1], .source 45070⟩,
    ⟨[90009, 1], [90011], .contexts [
        ⟨58808, true, false, [], []⟩
      ]⟩,
    ⟨[90009], [90009], .contexts []⟩,
    ⟨[90011, 1], [90009], .contexts [
        ⟨58809, true, false, [], [1]⟩,
        ⟨8, false, false, [90009], []⟩,
        ⟨58810, false, false, [], []⟩
      ]⟩,
    ⟨[90013], [90011, 13], .source 45071⟩,
    ⟨[90011, 13], [90013], .contexts [
        ⟨58812, true, false, [], []⟩
      ]⟩,
    ⟨[90011], [90011], .contexts []⟩,
    ⟨[90013, 13], [90011], .contexts [
        ⟨58813, true, false, [], [13]⟩,
        ⟨59, false, false, [90011], []⟩,
        ⟨58814, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 919. -/
def y322TCIndexRaw919 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90015], [90013, 15], .source 45072⟩,
    ⟨[90013], [90013], .contexts []⟩,
    ⟨[90015, 15], [90013], .contexts [
        ⟨58816, false, false, [], [15]⟩,
        ⟨1, false, false, [90013], []⟩,
        ⟨58817, false, false, [], []⟩
      ]⟩,
    ⟨[90017], [90015, 1], .source 45073⟩,
    ⟨[90015], [90015], .contexts []⟩,
    ⟨[90017, 1], [90015], .contexts [
        ⟨58819, false, false, [], [1]⟩,
        ⟨8, false, false, [90015], []⟩,
        ⟨58820, false, false, [], []⟩
      ]⟩,
    ⟨[90019], [90017, 3], .source 45074⟩,
    ⟨[90017], [90017], .contexts []⟩,
    ⟨[90019, 3], [90017], .contexts [
        ⟨58822, false, false, [], [3]⟩,
        ⟨20, false, false, [90017], []⟩,
        ⟨58823, false, false, [], []⟩
      ]⟩,
    ⟨[90021], [90019, 5], .source 45075⟩,
    ⟨[90019], [90019], .contexts []⟩,
    ⟨[90021, 5], [90019], .contexts [
        ⟨58825, false, false, [], [5]⟩,
        ⟨28, false, false, [90019], []⟩,
        ⟨58826, false, false, [], []⟩
      ]⟩,
    ⟨[90023], [90021, 1], .source 45076⟩,
    ⟨[90021, 1], [90023], .contexts [
        ⟨58828, true, false, [], []⟩
      ]⟩,
    ⟨[90021], [90021], .contexts []⟩,
    ⟨[90023, 1], [90021], .contexts [
        ⟨58829, true, false, [], [1]⟩,
        ⟨8, false, false, [90021], []⟩,
        ⟨58830, false, false, [], []⟩
      ]⟩,
    ⟨[90025], [90023, 9], .source 45077⟩,
    ⟨[90023, 9], [90025], .contexts [
        ⟨58832, true, false, [], []⟩
      ]⟩,
    ⟨[90023], [90023], .contexts []⟩,
    ⟨[90025, 9], [90023], .contexts [
        ⟨58833, true, false, [], [9]⟩,
        ⟨46, false, false, [90023], []⟩,
        ⟨58834, false, false, [], []⟩
      ]⟩,
    ⟨[90027], [90025, 11], .source 45078⟩,
    ⟨[90025, 11], [90027], .contexts [
        ⟨58836, true, false, [], []⟩
      ]⟩,
    ⟨[90025], [90025], .contexts []⟩,
    ⟨[90027, 11], [90025], .contexts [
        ⟨58837, true, false, [], [11]⟩,
        ⟨53, false, false, [90025], []⟩,
        ⟨58838, false, false, [], []⟩
      ]⟩,
    ⟨[90029], [90027, 1], .source 45079⟩,
    ⟨[90027, 1], [90029], .contexts [
        ⟨58840, true, false, [], []⟩
      ]⟩,
    ⟨[90027], [90027], .contexts []⟩,
    ⟨[90029, 1], [90027], .contexts [
        ⟨58841, true, false, [], [1]⟩,
        ⟨8, false, false, [90027], []⟩,
        ⟨58842, false, false, [], []⟩
      ]⟩,
    ⟨[90031], [90029, 13], .source 45080⟩,
    ⟨[90029, 13], [90031], .contexts [
        ⟨58844, true, false, [], []⟩
      ]⟩,
    ⟨[90029], [90029], .contexts []⟩,
    ⟨[90031, 13], [90029], .contexts [
        ⟨58845, true, false, [], [13]⟩,
        ⟨59, false, false, [90029], []⟩,
        ⟨58846, false, false, [], []⟩
      ]⟩,
    ⟨[90033], [90031, 15], .source 45081⟩,
    ⟨[90031, 15], [90033], .contexts [
        ⟨58848, true, false, [], []⟩
      ]⟩,
    ⟨[90031], [90031], .contexts []⟩,
    ⟨[90033, 15], [90031], .contexts [
        ⟨58849, true, false, [], [15]⟩,
        ⟨1, false, false, [90031], []⟩,
        ⟨58850, false, false, [], []⟩
      ]⟩,
    ⟨[90035], [90033, 1], .source 45082⟩,
    ⟨[90033], [90033], .contexts []⟩,
    ⟨[90035, 1], [90033], .contexts [
        ⟨58852, false, false, [], [1]⟩,
        ⟨8, false, false, [90033], []⟩,
        ⟨58853, false, false, [], []⟩
      ]⟩,
    ⟨[90037], [90035, 3], .source 45083⟩,
    ⟨[90035, 3], [90037], .contexts [
        ⟨58855, true, false, [], []⟩
      ]⟩,
    ⟨[90035], [90035], .contexts []⟩,
    ⟨[90037, 3], [90035], .contexts [
        ⟨58856, true, false, [], [3]⟩,
        ⟨20, false, false, [90035], []⟩,
        ⟨58857, false, false, [], []⟩
      ]⟩,
    ⟨[90039], [90037, 5], .source 45084⟩,
    ⟨[90037], [90037], .contexts []⟩,
    ⟨[90039, 5], [90037], .contexts [
        ⟨58859, false, false, [], [5]⟩,
        ⟨28, false, false, [90037], []⟩,
        ⟨58860, false, false, [], []⟩
      ]⟩,
    ⟨[90041], [90039, 1], .source 45085⟩,
    ⟨[90039], [90039], .contexts []⟩,
    ⟨[90041, 1], [90039], .contexts [
        ⟨58862, false, false, [], [1]⟩,
        ⟨8, false, false, [90039], []⟩,
        ⟨58863, false, false, [], []⟩
      ]⟩,
    ⟨[90043], [90041, 9], .source 45086⟩,
    ⟨[90041], [90041], .contexts []⟩,
    ⟨[90043, 9], [90041], .contexts [
        ⟨58865, false, false, [], [9]⟩,
        ⟨46, false, false, [90041], []⟩,
        ⟨58866, false, false, [], []⟩
      ]⟩,
    ⟨[90045], [90043, 11], .source 45087⟩,
    ⟨[90043], [90043], .contexts []⟩,
    ⟨[90045, 11], [90043], .contexts [
        ⟨58868, false, false, [], [11]⟩,
        ⟨53, false, false, [90043], []⟩,
        ⟨58869, false, false, [], []⟩
      ]⟩,
    ⟨[90047], [90045, 1], .source 45088⟩,
    ⟨[90045], [90045], .contexts []⟩,
    ⟨[90047, 1], [90045], .contexts [
        ⟨58871, false, false, [], [1]⟩,
        ⟨8, false, false, [90045], []⟩,
        ⟨58872, false, false, [], []⟩
      ]⟩,
    ⟨[90049], [90047, 13], .source 45089⟩,
    ⟨[90047], [90047], .contexts []⟩,
    ⟨[90049, 13], [90047], .contexts [
        ⟨58874, false, false, [], [13]⟩,
        ⟨59, false, false, [90047], []⟩,
        ⟨58875, false, false, [], []⟩
      ]⟩,
    ⟨[90051], [90049, 15], .source 45090⟩,
    ⟨[90049], [90049], .contexts []⟩,
    ⟨[90051, 15], [90049], .contexts [
        ⟨58877, false, false, [], [15]⟩,
        ⟨1, false, false, [90049], []⟩,
        ⟨58878, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 920. -/
def y322TCIndexRaw920 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90053], [90051, 1], .source 45091⟩,
    ⟨[90051], [90051], .contexts []⟩,
    ⟨[90053, 1], [90051], .contexts [
        ⟨58880, false, false, [], [1]⟩,
        ⟨8, false, false, [90051], []⟩,
        ⟨58881, false, false, [], []⟩
      ]⟩,
    ⟨[90055], [90053, 3], .source 45092⟩,
    ⟨[90053, 3], [90055], .contexts [
        ⟨58883, true, false, [], []⟩
      ]⟩,
    ⟨[90053], [90053], .contexts []⟩,
    ⟨[90055, 3], [90053], .contexts [
        ⟨58884, true, false, [], [3]⟩,
        ⟨20, false, false, [90053], []⟩,
        ⟨58885, false, false, [], []⟩
      ]⟩,
    ⟨[90057], [90055, 5], .source 45093⟩,
    ⟨[90055, 5], [90057], .contexts [
        ⟨58887, true, false, [], []⟩
      ]⟩,
    ⟨[90055], [90055], .contexts []⟩,
    ⟨[90057, 5], [90055], .contexts [
        ⟨58888, true, false, [], [5]⟩,
        ⟨28, false, false, [90055], []⟩,
        ⟨58889, false, false, [], []⟩
      ]⟩,
    ⟨[90059], [90057, 1], .source 45094⟩,
    ⟨[90057, 1], [90059], .contexts [
        ⟨58891, true, false, [], []⟩
      ]⟩,
    ⟨[90057], [90057], .contexts []⟩,
    ⟨[90059, 1], [90057], .contexts [
        ⟨58892, true, false, [], [1]⟩,
        ⟨8, false, false, [90057], []⟩,
        ⟨58893, false, false, [], []⟩
      ]⟩,
    ⟨[90061], [90059, 9], .source 45095⟩,
    ⟨[90059, 9], [90061], .contexts [
        ⟨58895, true, false, [], []⟩
      ]⟩,
    ⟨[90059], [90059], .contexts []⟩,
    ⟨[90061, 9], [90059], .contexts [
        ⟨58896, true, false, [], [9]⟩,
        ⟨46, false, false, [90059], []⟩,
        ⟨58897, false, false, [], []⟩
      ]⟩,
    ⟨[90063], [90061, 11], .source 45096⟩,
    ⟨[90061], [90061], .contexts []⟩,
    ⟨[90063, 11], [90061], .contexts [
        ⟨58899, false, false, [], [11]⟩,
        ⟨53, false, false, [90061], []⟩,
        ⟨58900, false, false, [], []⟩
      ]⟩,
    ⟨[90065], [90063, 1], .source 45097⟩,
    ⟨[90063], [90063], .contexts []⟩,
    ⟨[90065, 1], [90063], .contexts [
        ⟨58902, false, false, [], [1]⟩,
        ⟨8, false, false, [90063], []⟩,
        ⟨58903, false, false, [], []⟩
      ]⟩,
    ⟨[90067], [90065, 13], .source 45098⟩,
    ⟨[90065], [90065], .contexts []⟩,
    ⟨[90067, 13], [90065], .contexts [
        ⟨58905, false, false, [], [13]⟩,
        ⟨59, false, false, [90065], []⟩,
        ⟨58906, false, false, [], []⟩
      ]⟩,
    ⟨[90069], [90067, 15], .source 45099⟩,
    ⟨[90067, 15], [90069], .contexts [
        ⟨58908, true, false, [], []⟩
      ]⟩,
    ⟨[90067], [90067], .contexts []⟩,
    ⟨[90069, 15], [90067], .contexts [
        ⟨58909, true, false, [], [15]⟩,
        ⟨1, false, false, [90067], []⟩,
        ⟨58910, false, false, [], []⟩
      ]⟩,
    ⟨[90071], [90069, 1], .source 45100⟩,
    ⟨[90069, 1], [90071], .contexts [
        ⟨58912, true, false, [], []⟩
      ]⟩,
    ⟨[90069], [90069], .contexts []⟩,
    ⟨[90071, 1], [90069], .contexts [
        ⟨58913, true, false, [], [1]⟩,
        ⟨8, false, false, [90069], []⟩,
        ⟨58914, false, false, [], []⟩
      ]⟩,
    ⟨[90073], [90071, 3], .source 45101⟩,
    ⟨[90071, 3], [90073], .contexts [
        ⟨58916, true, false, [], []⟩
      ]⟩,
    ⟨[90071], [90071], .contexts []⟩,
    ⟨[90073, 3], [90071], .contexts [
        ⟨58917, true, false, [], [3]⟩,
        ⟨20, false, false, [90071], []⟩,
        ⟨58918, false, false, [], []⟩
      ]⟩,
    ⟨[90075], [90073, 5], .source 45102⟩,
    ⟨[90073, 5], [90075], .contexts [
        ⟨58920, true, false, [], []⟩
      ]⟩,
    ⟨[90073], [90073], .contexts []⟩,
    ⟨[90075, 5], [90073], .contexts [
        ⟨58921, true, false, [], [5]⟩,
        ⟨28, false, false, [90073], []⟩,
        ⟨58922, false, false, [], []⟩
      ]⟩,
    ⟨[90077], [90075, 1], .source 45103⟩,
    ⟨[90075], [90075], .contexts []⟩,
    ⟨[90077, 1], [90075], .contexts [
        ⟨58924, false, false, [], [1]⟩,
        ⟨8, false, false, [90075], []⟩,
        ⟨58925, false, false, [], []⟩
      ]⟩,
    ⟨[90079], [90077, 9], .source 45104⟩,
    ⟨[90077, 9], [90079], .contexts [
        ⟨58927, true, false, [], []⟩
      ]⟩,
    ⟨[90077], [90077], .contexts []⟩,
    ⟨[90079, 9], [90077], .contexts [
        ⟨58928, true, false, [], [9]⟩,
        ⟨46, false, false, [90077], []⟩,
        ⟨58929, false, false, [], []⟩
      ]⟩,
    ⟨[90081], [90079, 11], .source 45105⟩,
    ⟨[90079], [90079], .contexts []⟩,
    ⟨[90081, 11], [90079], .contexts [
        ⟨58931, false, false, [], [11]⟩,
        ⟨53, false, false, [90079], []⟩,
        ⟨58932, false, false, [], []⟩
      ]⟩,
    ⟨[90083], [90081, 1], .source 45106⟩,
    ⟨[90081, 1], [90083], .contexts [
        ⟨58934, true, false, [], []⟩
      ]⟩,
    ⟨[90081], [90081], .contexts []⟩,
    ⟨[90083, 1], [90081], .contexts [
        ⟨58935, true, false, [], [1]⟩,
        ⟨8, false, false, [90081], []⟩,
        ⟨58936, false, false, [], []⟩
      ]⟩,
    ⟨[90085], [90083, 13], .source 45107⟩,
    ⟨[90083, 13], [90085], .contexts [
        ⟨58938, true, false, [], []⟩
      ]⟩,
    ⟨[90083], [90083], .contexts []⟩,
    ⟨[90085, 13], [90083], .contexts [
        ⟨58939, true, false, [], [13]⟩,
        ⟨59, false, false, [90083], []⟩,
        ⟨58940, false, false, [], []⟩
      ]⟩,
    ⟨[90087], [90085, 15], .source 45108⟩,
    ⟨[90085, 15], [90087], .contexts [
        ⟨58942, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 921. -/
def y322TCIndexRaw921 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90085], [90085], .contexts []⟩,
    ⟨[90087, 15], [90085], .contexts [
        ⟨58943, true, false, [], [15]⟩,
        ⟨1, false, false, [90085], []⟩,
        ⟨58944, false, false, [], []⟩
      ]⟩,
    ⟨[90089], [90087, 1], .source 45109⟩,
    ⟨[90087, 1], [90089], .contexts [
        ⟨58946, true, false, [], []⟩
      ]⟩,
    ⟨[90087], [90087], .contexts []⟩,
    ⟨[90089, 1], [90087], .contexts [
        ⟨58947, true, false, [], [1]⟩,
        ⟨8, false, false, [90087], []⟩,
        ⟨58948, false, false, [], []⟩
      ]⟩,
    ⟨[90091], [90089, 3], .source 45110⟩,
    ⟨[90089, 3], [90091], .contexts [
        ⟨58950, true, false, [], []⟩
      ]⟩,
    ⟨[90089], [90089], .contexts []⟩,
    ⟨[90091, 3], [90089], .contexts [
        ⟨58951, true, false, [], [3]⟩,
        ⟨20, false, false, [90089], []⟩,
        ⟨58952, false, false, [], []⟩
      ]⟩,
    ⟨[90091], [90091], .contexts []⟩,
    ⟨[90091], [90091], .contexts []⟩,
    ⟨[90087], [90087], .contexts []⟩,
    ⟨[90089, 1], [90087], .contexts [
        ⟨58949, false, false, [], []⟩,
        ⟨58956, false, false, [], []⟩,
        ⟨58948, false, false, [], []⟩,
        ⟨58948, false, false, [], []⟩
      ]⟩,
    ⟨[90087, 15], [90085], .contexts [
        ⟨58945, false, false, [], []⟩
      ]⟩,
    ⟨[90085], [90085], .contexts []⟩,
    ⟨[90085, 13], [90083], .contexts [
        ⟨58941, false, false, [], []⟩
      ]⟩,
    ⟨[90083], [90083], .contexts []⟩,
    ⟨[90083, 1], [90081], .contexts [
        ⟨58937, false, false, [], []⟩
      ]⟩,
    ⟨[90081], [90081], .contexts []⟩,
    ⟨[90081, 11], [90079], .contexts [
        ⟨58933, false, false, [], []⟩
      ]⟩,
    ⟨[90079], [90079], .contexts []⟩,
    ⟨[90079, 9], [90077], .contexts [
        ⟨58930, false, false, [], []⟩
      ]⟩,
    ⟨[90077], [90077], .contexts []⟩,
    ⟨[90089, 1, 15, 13, 1, 11, 9], [90077], .contexts [
        ⟨58957, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨58958, false, false, [], [13, 1, 11, 9]⟩,
        ⟨58959, false, false, [], [13, 1, 11, 9]⟩,
        ⟨58944, false, false, [], [13, 1, 11, 9]⟩,
        ⟨58944, false, false, [], [13, 1, 11, 9]⟩,
        ⟨58960, false, false, [], [1, 11, 9]⟩,
        ⟨58961, false, false, [], [1, 11, 9]⟩,
        ⟨58940, false, false, [], [1, 11, 9]⟩,
        ⟨58940, false, false, [], [1, 11, 9]⟩,
        ⟨58962, false, false, [], [11, 9]⟩,
        ⟨58963, false, false, [], [11, 9]⟩,
        ⟨58936, false, false, [], [11, 9]⟩,
        ⟨58936, false, false, [], [11, 9]⟩,
        ⟨58964, false, false, [], [9]⟩,
        ⟨58965, false, false, [], [9]⟩,
        ⟨58932, false, false, [], [9]⟩,
        ⟨58932, false, false, [], [9]⟩,
        ⟨58966, false, false, [], []⟩,
        ⟨58967, false, false, [], []⟩,
        ⟨58929, false, false, [], []⟩,
        ⟨58929, false, false, [], []⟩
      ]⟩,
    ⟨[90077, 1], [90075], .contexts [
        ⟨58926, false, false, [], []⟩
      ]⟩,
    ⟨[90075], [90075], .contexts []⟩,
    ⟨[90073], [90073], .contexts []⟩,
    ⟨[90073, 3], [90071], .contexts [
        ⟨58919, false, false, [], []⟩
      ]⟩,
    ⟨[90071], [90071], .contexts []⟩,
    ⟨[90067], [90067], .contexts []⟩,
    ⟨[90089, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15], [90067], .contexts [
        ⟨58968, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨58969, false, false, [], [5, 3, 1, 15]⟩,
        ⟨58970, false, false, [], [5, 3, 1, 15]⟩,
        ⟨58925, false, false, [], [5, 3, 1, 15]⟩,
        ⟨58925, false, false, [], [5, 3, 1, 15]⟩,
        ⟨58923, false, false, [], [3, 1, 15]⟩,
        ⟨58971, false, false, [], [3, 1, 15]⟩,
        ⟨58922, false, false, [], [3, 1, 15]⟩,
        ⟨58922, false, false, [], [3, 1, 15]⟩,
        ⟨58972, false, false, [], [1, 15]⟩,
        ⟨58973, false, false, [], [1, 15]⟩,
        ⟨58918, false, false, [], [1, 15]⟩,
        ⟨58918, false, false, [], [1, 15]⟩,
        ⟨58915, false, false, [], [15]⟩,
        ⟨58914, false, false, [], [15]⟩,
        ⟨58914, false, false, [], [15]⟩,
        ⟨58911, false, false, [], []⟩,
        ⟨58974, false, false, [], []⟩,
        ⟨58910, false, false, [], []⟩,
        ⟨58910, false, false, [], []⟩
      ]⟩,
    ⟨[90063], [90063], .contexts []⟩,
    ⟨[90061], [90061], .contexts []⟩,
    ⟨[90059], [90059], .contexts []⟩,
    ⟨[90059, 1], [90057], .contexts [
        ⟨58894, false, false, [], []⟩
      ]⟩,
    ⟨[90057], [90057], .contexts []⟩,
    ⟨[
      90089, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1
    ], [90057], .contexts [
        ⟨58975, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨58907, false, false, [], [1, 11, 9, 1]⟩,
        ⟨58906, false, false, [], [1, 11, 9, 1]⟩,
        ⟨58906, false, false, [], [1, 11, 9, 1]⟩,
        ⟨58904, false, false, [], [11, 9, 1]⟩,
        ⟨58976, false, false, [], [11, 9, 1]⟩,
        ⟨58903, false, false, [], [11, 9, 1]⟩,
        ⟨58903, false, false, [], [11, 9, 1]⟩,
        ⟨58901, false, false, [], [9, 1]⟩,
        ⟨58977, false, false, [], [9, 1]⟩,
        ⟨58900, false, false, [], [9, 1]⟩,
        ⟨58900, false, false, [], [9, 1]⟩,
        ⟨58898, false, false, [], [1]⟩,
        ⟨58978, false, false, [], [1]⟩,
        ⟨58897, false, false, [], [1]⟩,
        ⟨58897, false, false, [], [1]⟩,
        ⟨58979, false, false, [], []⟩,
        ⟨58980, false, false, [], []⟩,
        ⟨58893, false, false, [], []⟩,
        ⟨58893, false, false, [], []⟩
      ]⟩,
    ⟨[90057, 5], [90055], .contexts [
        ⟨58890, false, false, [], []⟩
      ]⟩,
    ⟨[90055], [90055], .contexts []⟩,
    ⟨[90053], [90053], .contexts []⟩,
    ⟨[90049], [90049], .contexts []⟩,
    ⟨[90047], [90047], .contexts []⟩,
    ⟨[
      90089, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [90047], .contexts [
        ⟨58981, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨58982, false, false, [], [3, 1, 15, 13]⟩,
        ⟨58983, false, false, [], [3, 1, 15, 13]⟩,
        ⟨58889, false, false, [], [3, 1, 15, 13]⟩,
        ⟨58889, false, false, [], [3, 1, 15, 13]⟩,
        ⟨58886, false, false, [], [1, 15, 13]⟩,
        ⟨58984, false, false, [], [1, 15, 13]⟩,
        ⟨58885, false, false, [], [1, 15, 13]⟩,
        ⟨58885, false, false, [], [1, 15, 13]⟩,
        ⟨58882, false, false, [], [15, 13]⟩,
        ⟨58881, false, false, [], [15, 13]⟩,
        ⟨58881, false, false, [], [15, 13]⟩,
        ⟨58879, false, false, [], [13]⟩,
        ⟨58985, false, false, [], [13]⟩,
        ⟨58878, false, false, [], [13]⟩,
        ⟨58878, false, false, [], [13]⟩,
        ⟨58876, false, false, [], []⟩,
        ⟨58986, false, false, [], []⟩,
        ⟨58875, false, false, [], []⟩,
        ⟨58875, false, false, [], []⟩
      ]⟩,
    ⟨[90045], [90045], .contexts []⟩,
    ⟨[90043], [90043], .contexts []⟩,
    ⟨[90041], [90041], .contexts []⟩,
    ⟨[90039], [90039], .contexts []⟩,
    ⟨[90037], [90037], .contexts []⟩,
    ⟨[
      90089, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5
    ], [90037], .contexts [
        ⟨58987, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨58873, false, false, [], [11, 9, 1, 5]⟩,
        ⟨58988, false, false, [], [11, 9, 1, 5]⟩,
        ⟨58872, false, false, [], [11, 9, 1, 5]⟩,
        ⟨58872, false, false, [], [11, 9, 1, 5]⟩,
        ⟨58870, false, false, [], [9, 1, 5]⟩,
        ⟨58989, false, false, [], [9, 1, 5]⟩,
        ⟨58869, false, false, [], [9, 1, 5]⟩,
        ⟨58869, false, false, [], [9, 1, 5]⟩,
        ⟨58867, false, false, [], [1, 5]⟩,
        ⟨58990, false, false, [], [1, 5]⟩,
        ⟨58866, false, false, [], [1, 5]⟩,
        ⟨58866, false, false, [], [1, 5]⟩,
        ⟨58864, false, false, [], [5]⟩,
        ⟨58991, false, false, [], [5]⟩,
        ⟨58863, false, false, [], [5]⟩,
        ⟨58863, false, false, [], [5]⟩,
        ⟨58861, false, false, [], []⟩,
        ⟨58992, false, false, [], []⟩,
        ⟨58860, false, false, [], []⟩,
        ⟨58860, false, false, [], []⟩
      ]⟩,
    ⟨[90035], [90035], .contexts []⟩,
    ⟨[90031], [90031], .contexts []⟩,
    ⟨[90031, 13], [90029], .contexts [
        ⟨58847, false, false, [], []⟩
      ]⟩,
    ⟨[90029], [90029], .contexts []⟩,
    ⟨[90029, 1], [90027], .contexts [
        ⟨58843, false, false, [], []⟩
      ]⟩,
    ⟨[90027], [90027], .contexts []⟩,
    ⟨[
      90089, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1
    ], [90027], .contexts [
        ⟨58993, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨58858, false, false, [], [1, 15, 13, 1]⟩,
        ⟨58994, false, false, [], [1, 15, 13, 1]⟩,
        ⟨58857, false, false, [], [1, 15, 13, 1]⟩,
        ⟨58857, false, false, [], [1, 15, 13, 1]⟩,
        ⟨58854, false, false, [], [15, 13, 1]⟩,
        ⟨58853, false, false, [], [15, 13, 1]⟩,
        ⟨58853, false, false, [], [15, 13, 1]⟩,
        ⟨58851, false, false, [], [13, 1]⟩,
        ⟨58995, false, false, [], [13, 1]⟩,
        ⟨58850, false, false, [], [13, 1]⟩,
        ⟨58850, false, false, [], [13, 1]⟩,
        ⟨58996, false, false, [], [1]⟩,
        ⟨58997, false, false, [], [1]⟩,
        ⟨58846, false, false, [], [1]⟩,
        ⟨58846, false, false, [], [1]⟩,
        ⟨58998, false, false, [], []⟩,
        ⟨58999, false, false, [], []⟩,
        ⟨58842, false, false, [], []⟩,
        ⟨58842, false, false, [], []⟩
      ]⟩,
    ⟨[90027, 11], [90025], .contexts [
        ⟨58839, false, false, [], []⟩
      ]⟩,
    ⟨[90025], [90025], .contexts []⟩,
    ⟨[90023], [90023], .contexts []⟩,
    ⟨[90021], [90021], .contexts []⟩,
    ⟨[90017], [90017], .contexts []⟩,
    ⟨[
      90089, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3
    ], [90017], .contexts [
        ⟨59000, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨59001, false, false, [], [9, 1, 5, 3]⟩,
        ⟨59002, false, false, [], [9, 1, 5, 3]⟩,
        ⟨58838, false, false, [], [9, 1, 5, 3]⟩,
        ⟨58838, false, false, [], [9, 1, 5, 3]⟩,
        ⟨58835, false, false, [], [1, 5, 3]⟩,
        ⟨59003, false, false, [], [1, 5, 3]⟩,
        ⟨58834, false, false, [], [1, 5, 3]⟩,
        ⟨58834, false, false, [], [1, 5, 3]⟩,
        ⟨58831, false, false, [], [5, 3]⟩,
        ⟨59004, false, false, [], [5, 3]⟩,
        ⟨58830, false, false, [], [5, 3]⟩,
        ⟨58830, false, false, [], [5, 3]⟩,
        ⟨58827, false, false, [], [3]⟩,
        ⟨58826, false, false, [], [3]⟩,
        ⟨58826, false, false, [], [3]⟩,
        ⟨58824, false, false, [], []⟩,
        ⟨59005, false, false, [], []⟩,
        ⟨58823, false, false, [], []⟩,
        ⟨58823, false, false, [], []⟩
      ]⟩,
    ⟨[90015], [90015], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 922. -/
def y322TCIndexRaw922 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90013], [90013], .contexts []⟩,
    ⟨[90011], [90011], .contexts []⟩,
    ⟨[90009], [90009], .contexts []⟩,
    ⟨[90007], [90007], .contexts []⟩,
    ⟨[
      90089, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11
    ], [90007], .contexts [
        ⟨59006, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨58821, false, false, [], [15, 13, 1, 11]⟩,
        ⟨59007, false, false, [], [15, 13, 1, 11]⟩,
        ⟨58820, false, false, [], [15, 13, 1, 11]⟩,
        ⟨58820, false, false, [], [15, 13, 1, 11]⟩,
        ⟨58818, false, false, [], [13, 1, 11]⟩,
        ⟨59008, false, false, [], [13, 1, 11]⟩,
        ⟨58817, false, false, [], [13, 1, 11]⟩,
        ⟨58817, false, false, [], [13, 1, 11]⟩,
        ⟨58815, false, false, [], [1, 11]⟩,
        ⟨59009, false, false, [], [1, 11]⟩,
        ⟨58814, false, false, [], [1, 11]⟩,
        ⟨58814, false, false, [], [1, 11]⟩,
        ⟨58811, false, false, [], [11]⟩,
        ⟨59010, false, false, [], [11]⟩,
        ⟨58810, false, false, [], [11]⟩,
        ⟨58810, false, false, [], [11]⟩,
        ⟨58806, true, false, [], [11]⟩,
        ⟨53, false, false, [90007], []⟩,
        ⟨58807, false, false, [], []⟩,
        ⟨59011, false, false, [], []⟩,
        ⟨58807, false, false, [], []⟩,
        ⟨58807, false, false, [], []⟩
      ]⟩,
    ⟨[90003], [90003], .contexts []⟩,
    ⟨[90001, 3], [89999], .contexts [
        ⟨58789, false, false, [], []⟩
      ]⟩,
    ⟨[
      90089, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [89999], .contexts [
        ⟨59012, false, false, [], [9, 1, 5, 3]⟩,
        ⟨58803, true, false, [], [9, 1, 5, 3]⟩,
        ⟨46, false, false, [90005], [1, 5, 3]⟩,
        ⟨58804, false, false, [], [1, 5, 3]⟩,
        ⟨58804, false, false, [], [1, 5, 3]⟩,
        ⟨58804, false, false, [], [1, 5, 3]⟩,
        ⟨58800, true, false, [], [1, 5, 3]⟩,
        ⟨8, false, false, [90003], [5, 3]⟩,
        ⟨58801, false, false, [], [5, 3]⟩,
        ⟨59013, false, false, [], [5, 3]⟩,
        ⟨58801, false, false, [], [5, 3]⟩,
        ⟨58801, false, false, [], [5, 3]⟩,
        ⟨58798, false, false, [], [3]⟩,
        ⟨58791, false, false, [], [3]⟩,
        ⟨58792, false, false, [], [3]⟩,
        ⟨58792, false, false, [], [3]⟩,
        ⟨59014, false, false, [], []⟩,
        ⟨58778, false, false, [], []⟩,
        ⟨58779, false, false, [], []⟩,
        ⟨58779, false, false, [], []⟩
      ]⟩,
    ⟨[
      90089, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11
    ], [89989], .contexts [
        ⟨59015, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨58777, false, false, [], [15, 13, 1, 11]⟩,
        ⟨58768, false, false, [], [15, 13, 1, 11]⟩,
        ⟨58769, false, false, [], [15, 13, 1, 11]⟩,
        ⟨58769, false, false, [], [15, 13, 1, 11]⟩,
        ⟨58765, true, false, [], [15, 13, 1, 11]⟩,
        ⟨1, false, false, [89995], [13, 1, 11]⟩,
        ⟨58756, false, false, [], [13, 1, 11]⟩,
        ⟨58755, false, false, [], [13, 1, 11]⟩,
        ⟨58756, false, false, [], [13, 1, 11]⟩,
        ⟨58756, false, false, [], [13, 1, 11]⟩,
        ⟨58754, false, false, [], [1, 11]⟩,
        ⟨58744, false, false, [], [1, 11]⟩,
        ⟨58745, false, false, [], [1, 11]⟩,
        ⟨58745, false, false, [], [1, 11]⟩,
        ⟨58743, false, false, [], [11]⟩,
        ⟨58734, false, false, [], [11]⟩,
        ⟨58735, false, false, [], [11]⟩,
        ⟨58735, false, false, [], [11]⟩,
        ⟨58732, true, false, [], [11]⟩,
        ⟨53, false, false, [89989], []⟩,
        ⟨58722, false, false, [], []⟩,
        ⟨58721, false, false, [], []⟩,
        ⟨58722, false, false, [], []⟩,
        ⟨58722, false, false, [], []⟩
      ]⟩,
    ⟨[89989, 9], [89987], .contexts [
        ⟨58720, false, false, [], []⟩
      ]⟩,
    ⟨[
      90089, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1
    ], [24545, 89981], .contexts [
        ⟨59016, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨59017, false, false, [], [1, 5, 3, 1]⟩,
        ⟨58681, false, false, [], [1, 5, 3, 1]⟩,
        ⟨58682, false, false, [], [1, 5, 3, 1]⟩,
        ⟨58682, false, false, [], [1, 5, 3, 1]⟩,
        ⟨58695, false, false, [], [5, 3, 1]⟩,
        ⟨58684, false, false, [], [5, 3, 1]⟩,
        ⟨58685, false, false, [], [5, 3, 1]⟩,
        ⟨58685, false, false, [], [5, 3, 1]⟩,
        ⟨58680, false, false, [24545], [3, 1]⟩,
        ⟨58671, false, false, [], [3, 1]⟩,
        ⟨58672, false, false, [], [3, 1]⟩,
        ⟨58673, false, false, [], [3, 1]⟩,
        ⟨58665, false, false, [24545], [1]⟩,
        ⟨58668, false, false, [], [1]⟩,
        ⟨58669, false, false, [], [1]⟩,
        ⟨58670, false, false, [], [1]⟩,
        ⟨58653, false, false, [24545], []⟩,
        ⟨58636, false, false, [], []⟩,
        ⟨58637, false, false, [], []⟩,
        ⟨58638, false, false, [], []⟩
      ]⟩,
    ⟨[
      90089, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9
    ], [24545, 88973], .contexts [
        ⟨59018, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨58632, false, false, [24545], [13, 1, 11, 9]⟩,
        ⟨58599, false, false, [], [13, 1, 11, 9]⟩,
        ⟨58600, false, false, [], [13, 1, 11, 9]⟩,
        ⟨58601, false, false, [], [13, 1, 11, 9]⟩,
        ⟨58593, false, false, [24545], [1, 11, 9]⟩,
        ⟨58597, false, false, [], [1, 11, 9]⟩,
        ⟨58598, false, false, [], [1, 11, 9]⟩,
        ⟨58557, false, false, [24545], [11, 9]⟩,
        ⟨58540, false, false, [24545], [9]⟩,
        ⟨58515, false, false, [24545], []⟩
      ]⟩,
    ⟨[24577], [24545, 23383], .source 12353⟩,
    ⟨[24579], [24577, 17153], .source 12354⟩,
    ⟨[24581], [24579, 15233], .source 12355⟩,
    ⟨[
      90089, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15
    ], [24581, 83167], .contexts [
        ⟨59019, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨53364, false, false, [24545], [5, 3, 1, 15]⟩,
        ⟨59020, true, false, [], [83573, 5, 3, 1, 15]⟩,
        ⟨22081, false, false, [24577], [3, 1, 15]⟩,
        ⟨26512, false, false, [24577], [1, 15]⟩,
        ⟨59021, true, false, [], [82845, 1, 15]⟩,
        ⟨17394, false, false, [24579], [15]⟩,
        ⟨59022, true, false, [], [82845, 15]⟩,
        ⟨19462, false, false, [24581], []⟩
      ]⟩,
    ⟨[24583], [24581, 15993], .source 12356⟩,
    ⟨[24585], [24583, 16023], .source 12357⟩,
    ⟨[24587], [24585, 16379], .source 12358⟩,
    ⟨[
      90089, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [24587, 83501], .contexts [
        ⟨59023, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨19589, false, false, [24581], [1, 11, 9, 1]⟩,
        ⟨59024, true, false, [], [83177, 1, 11, 9, 1]⟩,
        ⟨19642, false, false, [24583], [11, 9, 1]⟩,
        ⟨21756, false, false, [24583], [9, 1]⟩,
        ⟨21750, false, false, [24583], [1]⟩,
        ⟨59025, true, false, [], [83507, 1]⟩,
        ⟨21734, false, false, [24585], []⟩,
        ⟨59026, true, false, [], [83501]⟩
      ]⟩,
    ⟨[24589], [24587, 1755], .source 12359⟩,
    ⟨[24591], [24589, 1075], .source 12360⟩,
    ⟨[24593], [24591, 2575], .source 12361⟩,
    ⟨[
      90089, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13
    ], [24593, 78987], .contexts [
        ⟨59027, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨21642, false, false, [24587], [3, 1, 15, 13]⟩,
        ⟨16716, false, false, [24587], [1, 15, 13]⟩,
        ⟨59028, true, false, [], [79019, 1, 15, 13]⟩,
        ⟨5595, false, false, [24589], [15, 13]⟩,
        ⟨59029, true, false, [], [79019, 15, 13]⟩,
        ⟨5600, false, false, [24591], [13]⟩,
        ⟨59030, true, false, [], [79019, 13]⟩,
        ⟨5586, false, false, [24593], []⟩
      ]⟩,
    ⟨[24595], [24593, 2241], .source 12362⟩,
    ⟨[
      90089, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [24595, 82797], .contexts [
        ⟨59031, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨5396, false, false, [24593], [11, 9, 1, 5]⟩,
        ⟨5453, false, false, [24593], [9, 1, 5]⟩,
        ⟨5467, false, false, [24593], [1, 5]⟩,
        ⟨59032, true, false, [], [78999, 1, 5]⟩,
        ⟨5580, false, false, [24595], [5]⟩,
        ⟨16728, false, false, [24595], []⟩
      ]⟩,
    ⟨[24597], [24595, 20779], .source 12363⟩,
    ⟨[24599], [24597, 23391], .source 12364⟩,
    ⟨[24601], [24599, 23427], .source 12365⟩,
    ⟨[24603], [24601, 19109], .source 12366⟩,
    ⟨[
      90089, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1
    ], [24603, 86421], .contexts [
        ⟨59033, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨27065, false, false, [24595], [1, 15, 13, 1]⟩,
        ⟨40595, false, false, [24595], [15, 13, 1]⟩,
        ⟨48769, false, false, [24595], [15, 13, 1]⟩,
        ⟨59034, true, false, [], [85263, 15, 13, 1]⟩,
        ⟨53378, false, false, [24597], [13, 1]⟩,
        ⟨59035, true, false, [], [88973, 13, 1]⟩,
        ⟨53443, false, false, [24599], [1]⟩,
        ⟨59036, true, false, [], [86421, 1]⟩,
        ⟨36999, false, false, [24601], []⟩,
        ⟨59037, true, false, [], [86421]⟩
      ]⟩,
    ⟨[24605], [24603, 19917], .source 12367⟩,
    ⟨[24605, 86783], [24605, 86783], .contexts []⟩,
    ⟨[24605, 86783], [24605, 86783], .contexts []⟩,
    ⟨[90091, 5], [90091, 5], .contexts []⟩,
    ⟨[90091, 5], [24605, 86783], .contexts [
        ⟨59042, false, false, [], []⟩,
        ⟨58955, true, false, [], [5]⟩,
        ⟨58955, true, false, [], [5]⟩,
        ⟨58954, true, false, [], [5]⟩,
        ⟨58951, true, false, [], [5]⟩,
        ⟨865, false, false, [90089], []⟩,
        ⟨866, false, false, [90089], []⟩,
        ⟨59038, false, false, [], [11, 9, 1]⟩,
        ⟨36820, false, false, [24603], [9, 1]⟩,
        ⟨40448, false, false, [24603], [1]⟩,
        ⟨59039, true, false, [], [86785, 1]⟩,
        ⟨38751, false, false, [24605], []⟩,
        ⟨59040, false, false, [], []⟩,
        ⟨59041, false, false, [], []⟩,
        ⟨40499, false, false, [24605], []⟩,
        ⟨13, true, false, [], [24605, 86783]⟩
      ]⟩,
    ⟨[24607], [24604], .source 12368⟩,
    ⟨[86783, 5], [24607, 90091], .contexts [
        ⟨59043, true, false, [24604], [5]⟩,
        ⟨28, false, false, [24604, 90091], []⟩,
        ⟨59044, true, false, [], [90091]⟩
      ]⟩,
    ⟨[90091, 3], [90089], .contexts [
        ⟨58953, false, false, [], []⟩
      ]⟩,
    ⟨[90091, 3], [90089], .contexts [
        ⟨59046, false, false, [], []⟩,
        ⟨58952, false, false, [], []⟩,
        ⟨58952, false, false, [], []⟩
      ]⟩,
    ⟨[90091, 5], [24605, 86783], .contexts [
        ⟨59042, false, false, [], []⟩,
        ⟨59043, false, false, [], []⟩,
        ⟨59040, false, false, [], []⟩,
        ⟨59041, false, false, [], []⟩,
        ⟨59041, false, false, [], []⟩
      ]⟩,
    ⟨[24609], [24605, 22631], .source 12369⟩,
    ⟨[24611], [24609, 24607], .source 12370⟩,
    ⟨[24611, 90089], [24611, 90089], .contexts []⟩,
    ⟨[24611, 90089], [24611, 90089], .contexts []⟩,
    ⟨[90089, 5], [90089, 5], .contexts []⟩,
    ⟨[90089], [90089], .contexts []⟩,
    ⟨[24611], [24611], .contexts []⟩,
    ⟨[24611], [24611], .contexts []⟩,
    ⟨[24613], [24605, 19929], .source 12371⟩,
    ⟨[24615], [24613, 24607], .source 12372⟩,
    ⟨[90091, 9], [90091, 9], .contexts []⟩,
    ⟨[90091], [90091], .contexts []⟩,
    ⟨[24617], [24614], .source 12373⟩,
    ⟨[24614], [24614], .contexts []⟩,
    ⟨[90091, 9], [24617, 90091], .contexts [
        ⟨59059, false, false, [], []⟩,
        ⟨59058, false, false, [24614], [90091, 9]⟩,
        ⟨59045, true, false, [24614, 24613], [9]⟩,
        ⟨59057, false, false, [24614], [86783, 5, 9]⟩,
        ⟨40503, true, false, [24614, 24605], [5, 9]⟩,
        ⟨59048, true, false, [24614], [9, 5, 9]⟩,
        ⟨882, false, false, [24614, 90091], []⟩,
        ⟨59060, false, false, [24614], []⟩,
        ⟨59062, true, false, [], [90091]⟩,
        ⟨59062, true, false, [], [90091]⟩,
        ⟨59061, true, false, [], [90091]⟩
      ]⟩,
    ⟨[90089, 5], [24611, 90089], .contexts [
        ⟨59053, false, false, [], []⟩,
        ⟨59053, false, false, [], []⟩,
        ⟨59047, true, false, [], [5]⟩,
        ⟨871, false, false, [90091], []⟩,
        ⟨873, false, false, [90091], []⟩,
        ⟨59048, false, false, [], [3, 5, 3]⟩,
        ⟨49821, false, false, [24605], [5, 3]⟩,
        ⟨59049, true, false, [], [86783, 5, 3]⟩,
        ⟨59045, false, false, [24609], [3]⟩,
        ⟨59050, true, false, [], [90091, 3]⟩,
        ⟨58953, false, false, [24611], []⟩,
        ⟨59051, false, false, [], []⟩,
        ⟨59052, false, false, [], []⟩,
        ⟨59054, false, false, [24611], []⟩,
        ⟨59056, true, false, [], [90089]⟩,
        ⟨59055, true, false, [], [90089]⟩,
        ⟨13, true, false, [], [24611, 90089]⟩,
        ⟨59051, false, false, [], []⟩,
        ⟨59052, false, false, [], []⟩
      ]⟩,
    ⟨[90087, 5], [90087, 5], .contexts []⟩,
    ⟨[90087], [90087], .contexts []⟩,
    ⟨[24619], [24610], .source 12374⟩,
    ⟨[24610], [24610], .contexts []⟩,
    ⟨[24619], [24610], .contexts [
        ⟨59067, false, false, [], []⟩,
        ⟨59068, false, false, [], []⟩,
        ⟨59068, false, false, [], []⟩
      ]⟩,
    ⟨[90087, 5], [24619, 90087], .contexts [
        ⟨59065, false, false, [], []⟩,
        ⟨58949, true, false, [], [5]⟩,
        ⟨59052, true, false, [24610], [1, 5]⟩,
        ⟨59064, true, false, [24610], [1, 5]⟩,
        ⟨890, false, false, [24610, 90089], []⟩,
        ⟨9, false, false, [24610, 90089], []⟩,
        ⟨58957, false, false, [24610], []⟩,
        ⟨59066, false, false, [24610], []⟩,
        ⟨59069, true, false, [], [90087]⟩
      ]⟩,
    ⟨[24617, 90091], [24617, 90091], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 923. -/
def y322TCIndexRaw923 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[24616], [24616], .contexts []⟩,
    ⟨[24619, 90087], [24619, 90087], .contexts []⟩,
    ⟨[24619, 90087], [24619, 90087], .contexts []⟩,
    ⟨[90087, 15], [90085], .contexts [
        ⟨58958, false, false, [], []⟩,
        ⟨58959, false, false, [], []⟩,
        ⟨58944, false, false, [], []⟩,
        ⟨58944, false, false, [], []⟩
      ]⟩,
    ⟨[90085, 5], [90085, 5], .contexts []⟩,
    ⟨[90085], [90085], .contexts []⟩,
    ⟨[24611], [24618], .contexts [
        ⟨59067, true, true, [], []⟩
      ]⟩,
    ⟨[24611], [24611], .contexts []⟩,
    ⟨[24618], [24618], .contexts []⟩,
    ⟨[24611], [24618], .contexts [
        ⟨59079, false, false, [], []⟩,
        ⟨59078, false, false, [], []⟩,
        ⟨59080, false, false, [], []⟩,
        ⟨59080, false, false, [], []⟩
      ]⟩,
    ⟨[90085, 5], [24611, 90085], .contexts [
        ⟨59076, false, false, [], []⟩,
        ⟨58945, true, false, [], [5]⟩,
        ⟨59074, true, false, [24618], [15, 5]⟩,
        ⟨59074, true, false, [24618], [15, 5]⟩,
        ⟨59073, true, false, [24618], [15, 5]⟩,
        ⟨59070, true, false, [24618], [15, 5]⟩,
        ⟨59065, true, false, [24618], [15, 5]⟩,
        ⟨1204, false, false, [24618, 90087], []⟩,
        ⟨10, false, false, [24618, 90087], []⟩,
        ⟨59075, false, false, [24618], []⟩,
        ⟨59077, false, false, [24618], []⟩,
        ⟨59081, true, false, [], [90085]⟩
      ]⟩,
    ⟨[24611, 90085], [24611, 90085], .contexts []⟩,
    ⟨[24611, 90085], [24611, 90085], .contexts []⟩,
    ⟨[90085, 13], [90083], .contexts [
        ⟨58960, false, false, [], []⟩,
        ⟨58961, false, false, [], []⟩,
        ⟨58940, false, false, [], []⟩,
        ⟨58940, false, false, [], []⟩
      ]⟩,
    ⟨[90085, 12], [90085, 13], .contexts [
        ⟨64, false, false, [90085], []⟩
      ]⟩,
    ⟨[90083, 5], [90083, 5], .contexts []⟩,
    ⟨[90083], [90083], .contexts []⟩,
    ⟨[90083, 5], [24619, 90083], .contexts [
        ⟨59087, false, false, [], []⟩,
        ⟨58941, true, false, [], [5]⟩,
        ⟨59084, true, false, [24610], [13, 5]⟩,
        ⟨59084, true, false, [24610], [13, 5]⟩,
        ⟨59083, true, false, [24610], [13, 5]⟩,
        ⟨59082, true, false, [24610], [13, 5]⟩,
        ⟨59076, true, false, [24610], [13, 5]⟩,
        ⟨913, false, false, [24610, 90085], []⟩,
        ⟨59086, false, false, [24610], []⟩,
        ⟨59085, false, false, [24610], []⟩,
        ⟨59088, false, false, [24610], []⟩,
        ⟨59069, true, false, [], [90083]⟩
      ]⟩,
    ⟨[24619, 90083], [24619, 90083], .contexts []⟩,
    ⟨[24619, 90083], [24619, 90083], .contexts []⟩,
    ⟨[90083, 1], [90081], .contexts [
        ⟨58962, false, false, [], []⟩,
        ⟨58963, false, false, [], []⟩,
        ⟨58936, false, false, [], []⟩,
        ⟨58936, false, false, [], []⟩
      ]⟩,
    ⟨[90083, 0], [90083, 1], .contexts [
        ⟨9, false, false, [90083], []⟩
      ]⟩,
    ⟨[90081, 5], [90081, 5], .contexts []⟩,
    ⟨[90081], [90081], .contexts []⟩,
    ⟨[90081, 5], [24611, 90081], .contexts [
        ⟨59094, false, false, [], []⟩,
        ⟨58937, true, false, [], [5]⟩,
        ⟨59091, true, false, [24618], [1, 5]⟩,
        ⟨59091, true, false, [24618], [1, 5]⟩,
        ⟨59090, true, false, [24618], [1, 5]⟩,
        ⟨59089, true, false, [24618], [1, 5]⟩,
        ⟨59087, true, false, [24618], [1, 5]⟩,
        ⟨890, false, false, [24618, 90083], []⟩,
        ⟨59093, false, false, [24618], []⟩,
        ⟨59092, false, false, [24618], []⟩,
        ⟨59095, false, false, [24618], []⟩,
        ⟨59081, true, false, [], [90081]⟩
      ]⟩,
    ⟨[24611, 90081], [24611, 90081], .contexts []⟩,
    ⟨[24611, 90081], [24611, 90081], .contexts []⟩,
    ⟨[90081, 5], [24611, 90081], .contexts [
        ⟨59094, false, false, [], []⟩,
        ⟨59096, false, false, [], []⟩,
        ⟨59097, false, false, [], []⟩,
        ⟨59098, false, false, [], []⟩,
        ⟨59098, false, false, [], []⟩
      ]⟩,
    ⟨[90081, 11], [90079], .contexts [
        ⟨58964, false, false, [], []⟩
      ]⟩,
    ⟨[90081, 11], [90079], .contexts [
        ⟨59100, false, false, [], []⟩,
        ⟨58965, false, false, [], []⟩,
        ⟨58932, false, false, [], []⟩,
        ⟨58932, false, false, [], []⟩
      ]⟩,
    ⟨[90081, 10], [90081, 11], .contexts [
        ⟨54, false, false, [90081], []⟩
      ]⟩,
    ⟨[90079, 5], [90079, 5], .contexts []⟩,
    ⟨[90079], [90079], .contexts []⟩,
    ⟨[24619, 90079], [24619, 90079], .contexts []⟩,
    ⟨[24619, 90077], [24619, 90077], .contexts []⟩,
    ⟨[24619, 90077], [24619, 90077], .contexts []⟩,
    ⟨[90079, 5, 9], [24619, 90077], .contexts [
        ⟨59103, false, false, [], [9]⟩,
        ⟨59103, false, false, [], [9]⟩,
        ⟨58933, true, false, [], [5, 9]⟩,
        ⟨59099, true, false, [24610], [11, 5, 9]⟩,
        ⟨940, false, false, [24610, 90081], [9]⟩,
        ⟨59102, false, false, [24610], [9]⟩,
        ⟨59101, false, false, [24610], [9]⟩,
        ⟨59104, false, false, [24610], [9]⟩,
        ⟨59069, true, false, [], [90079, 9]⟩,
        ⟨59105, false, false, [], [9]⟩,
        ⟨59105, false, false, [], [9]⟩,
        ⟨58930, false, false, [24619], []⟩,
        ⟨59106, false, false, [], []⟩,
        ⟨59107, false, false, [], []⟩
      ]⟩,
    ⟨[90079, 9], [90077], .contexts [
        ⟨58966, false, false, [], []⟩,
        ⟨58967, false, false, [], []⟩,
        ⟨58929, false, false, [], []⟩,
        ⟨58929, false, false, [], []⟩
      ]⟩,
    ⟨[90079, 8], [90079, 9], .contexts [
        ⟨47, false, false, [90079], []⟩
      ]⟩,
    ⟨[90077, 5], [90077, 5], .contexts []⟩,
    ⟨[90077], [90077], .contexts []⟩,
    ⟨[90077, 5], [24611, 90077], .contexts [
        ⟨59111, false, false, [], []⟩,
        ⟨59108, true, false, [24618], [5]⟩,
        ⟨960, false, false, [24618, 90079], []⟩,
        ⟨59110, false, false, [24618], []⟩,
        ⟨59109, false, false, [24618], []⟩,
        ⟨59112, false, false, [24618], []⟩,
        ⟨59081, true, false, [], [90077]⟩
      ]⟩,
    ⟨[24611, 90077], [24611, 90077], .contexts []⟩,
    ⟨[24611, 90077], [24611, 90077], .contexts []⟩,
    ⟨[24611, 90073], [24611, 90073], .contexts []⟩,
    ⟨[24611, 90073], [24611, 90073], .contexts []⟩,
    ⟨[90077], [90077], .contexts []⟩,
    ⟨[90073, 1], [90073, 1], .contexts []⟩,
    ⟨[90073, 1], [24619, 90077], .contexts [
        ⟨59119, false, false, [], []⟩,
        ⟨59117, true, false, [24610], [1]⟩,
        ⟨59116, true, false, [24610], [1]⟩,
        ⟨58923, true, false, [], [1]⟩,
        ⟨58926, true, false, [], [5, 1]⟩,
        ⟨59115, true, false, [24610], [1, 5, 1]⟩,
        ⟨59115, true, false, [24610], [1, 5, 1]⟩,
        ⟨59114, true, false, [24610], [1, 5, 1]⟩,
        ⟨59113, true, false, [24610], [1, 5, 1]⟩,
        ⟨59111, true, false, [24610], [1, 5, 1]⟩,
        ⟨874, false, false, [24610, 90077], []⟩,
        ⟨59118, false, false, [24610], []⟩,
        ⟨59112, false, false, [24610], []⟩,
        ⟨59069, true, false, [], [90077]⟩
      ]⟩,
    ⟨[90093], [86581, 13], .source 45111⟩,
    ⟨[86581, 13], [90093], .contexts [
        ⟨59121, true, false, [], []⟩
      ]⟩,
    ⟨[90093, 13], [86581], .contexts [
        ⟨59122, true, false, [], [13]⟩,
        ⟨59, false, false, [86581], []⟩,
        ⟨38125, false, false, [], []⟩
      ]⟩,
    ⟨[90093], [90093], .contexts []⟩,
    ⟨[90093], [90093], .contexts []⟩,
    ⟨[86581, 13], [90093], .contexts [
        ⟨59122, false, false, [], []⟩,
        ⟨59124, false, false, [], []⟩,
        ⟨59125, false, false, [], []⟩,
        ⟨59125, false, false, [], []⟩
      ]⟩,
    ⟨[90093, 5], [90093, 5], .contexts []⟩,
    ⟨[21583], [21583], .contexts [
        ⟨13, false, false, [], [21583]⟩
      ]⟩,
    ⟨[90093, 5], [21583, 87019], .contexts [
        ⟨59127, false, false, [], []⟩,
        ⟨59126, true, false, [], [5]⟩,
        ⟨68, false, false, [86581], []⟩,
        ⟨69, false, false, [86581], []⟩,
        ⟨38150, false, false, [], [13]⟩,
        ⟨45613, false, false, [], []⟩,
        ⟨45614, false, false, [], []⟩,
        ⟨45615, false, false, [], []⟩,
        ⟨45615, false, false, [], []⟩,
        ⟨39964, false, false, [21583], []⟩,
        ⟨59128, true, false, [], [87019]⟩
      ]⟩,
    ⟨[16423, 90093], [16423, 90093], .contexts []⟩,
    ⟨[16423, 90093], [16423, 90093], .contexts []⟩,
    ⟨[90093, 7], [90093, 7], .contexts []⟩,
    ⟨[90093], [90093], .contexts []⟩,
    ⟨[90093, 7], [16423, 90093], .contexts [
        ⟨59132, false, false, [], []⟩,
        ⟨59126, true, false, [], [7]⟩,
        ⟨73, false, false, [86581], []⟩,
        ⟨74, false, false, [86581], []⟩,
        ⟨38139, false, false, [], [13]⟩,
        ⟨38140, false, false, [], [13]⟩,
        ⟨38137, false, false, [], [13]⟩,
        ⟨38138, false, false, [], [13]⟩,
        ⟨38138, false, false, [], [13]⟩,
        ⟨59122, false, false, [16423], []⟩,
        ⟨59130, false, false, [], []⟩,
        ⟨59131, false, false, [], []⟩,
        ⟨59133, false, false, [16423], []⟩,
        ⟨21932, true, false, [], [90093]⟩
      ]⟩,
    ⟨[24621], [21487, 21485], .source 12375⟩]

/-- Exact literal claimed equations and contextual derivations, block 924. -/
def y322TCIndexRaw924 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90093, 9], [90093, 9], .contexts []⟩,
    ⟨[90093, 9], [24621, 87331], .contexts [
        ⟨59136, false, false, [], []⟩,
        ⟨59126, true, false, [], [9]⟩,
        ⟨77, false, false, [86581], []⟩,
        ⟨78, false, false, [86581], []⟩,
        ⟨45446, false, false, [], [13]⟩,
        ⟨45385, false, false, [21487], []⟩,
        ⟨59135, true, false, [], [87331]⟩,
        ⟨41118, false, false, [24621], []⟩,
        ⟨13, true, false, [], [24621, 87331]⟩
      ]⟩,
    ⟨[24623], [24620], .source 12376⟩,
    ⟨[87331, 9], [24623, 90093], .contexts [
        ⟨59137, true, false, [24620], [9]⟩,
        ⟨46, false, false, [24620, 90093], []⟩,
        ⟨59138, true, false, [], [90093]⟩
      ]⟩,
    ⟨[17387, 90093], [17387, 90093], .contexts []⟩,
    ⟨[17387, 90093], [17387, 90093], .contexts []⟩,
    ⟨[90093, 11], [90093, 11], .contexts []⟩,
    ⟨[90093, 11], [17387, 90093], .contexts [
        ⟨59142, false, false, [], []⟩,
        ⟨59126, true, false, [], [11]⟩,
        ⟨82, false, false, [86581], []⟩,
        ⟨83, false, false, [86581], []⟩,
        ⟨38162, false, false, [], [13]⟩,
        ⟨59122, false, false, [17387], []⟩,
        ⟨59140, false, false, [], []⟩,
        ⟨59141, false, false, [], []⟩,
        ⟨59133, false, false, [17387], []⟩,
        ⟨38075, true, false, [], [90093]⟩
      ]⟩,
    ⟨[21583, 87015], [21583, 87015], .contexts []⟩,
    ⟨[21583, 87015], [21583, 87015], .contexts []⟩,
    ⟨[21582], [21582], .contexts []⟩,
    ⟨[21585], [21582], .contexts [
        ⟨45627, false, false, [], []⟩,
        ⟨59146, false, false, [], []⟩,
        ⟨59146, false, false, [], []⟩
      ]⟩,
    ⟨[87015, 1], [21585, 90093], .contexts [
        ⟨59145, true, false, [21582], [1]⟩,
        ⟨59144, true, false, [21582], [1]⟩,
        ⟨39742, true, false, [], [1]⟩,
        ⟨45625, true, false, [21582], [5, 1]⟩,
        ⟨45624, true, false, [21582], [5, 1]⟩,
        ⟨45623, true, false, [21582], [5, 1]⟩,
        ⟨45622, true, false, [21582], [5, 1]⟩,
        ⟨45615, true, false, [21582], [1, 5, 1]⟩,
        ⟨45615, true, false, [21582], [1, 5, 1]⟩,
        ⟨45614, true, false, [21582], [1, 5, 1]⟩,
        ⟨59129, true, false, [21582], [1, 5, 1]⟩,
        ⟨59127, true, false, [21582], [1, 5, 1]⟩,
        ⟨874, false, false, [21582, 90093], []⟩,
        ⟨59133, false, false, [21582], []⟩,
        ⟨59147, true, false, [], [90093]⟩
      ]⟩,
    ⟨[21583], [21584], .contexts [
        ⟨45554, true, true, [], []⟩
      ]⟩,
    ⟨[90093, 1], [21583, 87015], .contexts [
        ⟨59148, true, false, [21584], [1]⟩,
        ⟨8, false, false, [21584, 87015], []⟩,
        ⟨59149, true, false, [], [87015]⟩
      ]⟩,
    ⟨[90093, 1], [21583, 87015], .contexts [
        ⟨59150, false, false, [], []⟩
      ]⟩,
    ⟨[24621, 87331], [24621, 87331], .contexts []⟩,
    ⟨[24621, 87331], [24621, 87331], .contexts []⟩,
    ⟨[24631], [24621, 19971], .source 12380⟩,
    ⟨[24631, 84949, 9], [21583, 87015], .contexts [
        ⟨29324, true, false, [24631], [9]⟩,
        ⟨29328, true, false, [24631], [1, 9]⟩,
        ⟨59154, false, false, [], [84953, 9, 1, 9]⟩,
        ⟨41091, true, false, [24621], [9, 1, 9]⟩,
        ⟨59153, true, false, [], [1, 9, 1, 9]⟩,
        ⟨59153, true, false, [], [1, 9, 1, 9]⟩,
        ⟨59152, true, false, [], [1, 9, 1, 9]⟩,
        ⟨59137, true, false, [], [1, 9, 1, 9]⟩,
        ⟨59136, true, false, [], [1, 9, 1, 9]⟩,
        ⟨495, false, false, [90093], []⟩,
        ⟨9, false, false, [90093], []⟩,
        ⟨59151, false, false, [], []⟩,
        ⟨59144, false, false, [], []⟩,
        ⟨59145, false, false, [], []⟩,
        ⟨59145, false, false, [], []⟩
      ]⟩,
    ⟨[84949, 9], [84949, 9], .contexts []⟩,
    ⟨[24633], [24630], .source 12381⟩,
    ⟨[24635], [24633, 21583], .source 12382⟩,
    ⟨[84949, 9], [24635, 87015], .contexts [
        ⟨59156, false, false, [], []⟩,
        ⟨59155, false, false, [24630], []⟩,
        ⟨39976, false, false, [24630, 21583], []⟩,
        ⟨59157, true, false, [], [21583, 87015]⟩,
        ⟨59158, true, false, [], [87015]⟩
      ]⟩,
    ⟨[24637], [24634], .source 12383⟩,
    ⟨[24635, 87015], [24635, 87015], .contexts []⟩,
    ⟨[24635, 87015], [24635, 87015], .contexts []⟩,
    ⟨[24634], [24634], .contexts []⟩,
    ⟨[90095], [90093, 15], .source 45112⟩,
    ⟨[90093, 15], [90095], .contexts [
        ⟨59164, true, false, [], []⟩
      ]⟩,
    ⟨[90095, 15], [90093], .contexts [
        ⟨59165, true, false, [], [15]⟩,
        ⟨1, false, false, [90093], []⟩,
        ⟨59125, false, false, [], []⟩
      ]⟩,
    ⟨[90095], [90095], .contexts []⟩,
    ⟨[90095], [90095], .contexts []⟩,
    ⟨[90093, 15], [90095], .contexts [
        ⟨59165, false, false, [], []⟩,
        ⟨59167, false, false, [], []⟩,
        ⟨59168, false, false, [], []⟩,
        ⟨59168, false, false, [], []⟩
      ]⟩,
    ⟨[16423, 90095], [16423, 90095], .contexts []⟩,
    ⟨[16423, 90095], [16423, 90095], .contexts []⟩,
    ⟨[90095, 7], [90095, 7], .contexts []⟩,
    ⟨[90095], [90095], .contexts []⟩,
    ⟨[90095, 7], [16423, 90095], .contexts [
        ⟨59172, false, false, [], []⟩,
        ⟨59169, true, false, [], [7]⟩,
        ⟨37, false, false, [90093], []⟩,
        ⟨40, false, false, [90093], []⟩,
        ⟨59132, false, false, [], [15]⟩,
        ⟨59134, false, false, [], [15]⟩,
        ⟨59130, false, false, [], [15]⟩,
        ⟨59131, false, false, [], [15]⟩,
        ⟨59131, false, false, [], [15]⟩,
        ⟨59165, false, false, [16423], []⟩,
        ⟨59170, false, false, [], []⟩,
        ⟨59171, false, false, [], []⟩,
        ⟨59173, false, false, [16423], []⟩,
        ⟨21932, true, false, [], [90095]⟩
      ]⟩,
    ⟨[17387, 90095], [17387, 90095], .contexts []⟩,
    ⟨[17387, 90095], [17387, 90095], .contexts []⟩,
    ⟨[90095, 11], [90095, 11], .contexts []⟩,
    ⟨[90095, 11], [17387, 90095], .contexts [
        ⟨59177, false, false, [], []⟩,
        ⟨59169, true, false, [], [11]⟩,
        ⟨52, false, false, [90093], []⟩,
        ⟨55, false, false, [90093], []⟩,
        ⟨59142, false, false, [], [15]⟩,
        ⟨59143, false, false, [], [15]⟩,
        ⟨59140, false, false, [], [15]⟩,
        ⟨59141, false, false, [], [15]⟩,
        ⟨59141, false, false, [], [15]⟩,
        ⟨59165, false, false, [17387], []⟩,
        ⟨59175, false, false, [], []⟩,
        ⟨59176, false, false, [], []⟩,
        ⟨59173, false, false, [17387], []⟩,
        ⟨38075, true, false, [], [90095]⟩
      ]⟩,
    ⟨[90097], [90095, 1], .source 45113⟩,
    ⟨[90095, 1], [90097], .contexts [
        ⟨59179, true, false, [], []⟩
      ]⟩,
    ⟨[90097, 1], [90095], .contexts [
        ⟨59180, true, false, [], [1]⟩,
        ⟨8, false, false, [90095], []⟩,
        ⟨59168, false, false, [], []⟩
      ]⟩,
    ⟨[90097], [90097], .contexts []⟩,
    ⟨[90097], [90097], .contexts []⟩,
    ⟨[90095, 1], [90097], .contexts [
        ⟨59180, false, false, [], []⟩,
        ⟨59182, false, false, [], []⟩,
        ⟨59183, false, false, [], []⟩,
        ⟨59183, false, false, [], []⟩
      ]⟩,
    ⟨[16423, 90097], [16423, 90097], .contexts []⟩,
    ⟨[90097], [90097], .contexts []⟩,
    ⟨[17387, 90097], [17387, 90097], .contexts []⟩,
    ⟨[90095, 15], [90093], .contexts [
        ⟨59166, false, false, [], []⟩
      ]⟩,
    ⟨[90097, 15], [90097, 15], .contexts []⟩,
    ⟨[90097, 15], [21583, 87015], .contexts [
        ⟨59189, false, false, [], []⟩,
        ⟨59184, true, false, [], [15]⟩,
        ⟨121, false, false, [90095], []⟩,
        ⟨122, false, false, [90095], []⟩,
        ⟨59188, false, false, [], [1]⟩,
        ⟨59124, false, false, [], [1]⟩,
        ⟨59125, false, false, [], [1]⟩,
        ⟨59125, false, false, [], [1]⟩,
        ⟨59151, false, false, [], []⟩,
        ⟨59144, false, false, [], []⟩,
        ⟨59145, false, false, [], []⟩,
        ⟨59145, false, false, [], []⟩,
        ⟨39976, false, false, [21583], []⟩,
        ⟨59128, true, false, [], [87015]⟩
      ]⟩,
    ⟨[90099], [90097, 3], .source 45114⟩,
    ⟨[90097, 3], [90099], .contexts [
        ⟨59191, true, false, [], []⟩
      ]⟩,
    ⟨[90097, 3], [90099], .contexts [
        ⟨59192, false, false, [], []⟩
      ]⟩,
    ⟨[90099], [90099], .contexts []⟩,
    ⟨[90099], [90099], .contexts []⟩,
    ⟨[21583, 87013], [21583, 87013], .contexts []⟩,
    ⟨[21583, 87013], [21583, 87013], .contexts []⟩,
    ⟨[90099, 15], [90099, 15], .contexts []⟩,
    ⟨[90099, 15, 1], [21583, 87011], .contexts [
        ⟨59198, false, false, [], [1]⟩,
        ⟨59198, false, false, [], [1]⟩,
        ⟨59195, true, false, [], [15, 1]⟩,
        ⟨59195, true, false, [], [15, 1]⟩,
        ⟨59194, true, false, [], [15, 1]⟩,
        ⟨59193, true, false, [], [15, 1]⟩,
        ⟨151, false, false, [90097], [1]⟩,
        ⟨152, false, false, [90097], [1]⟩,
        ⟨59189, false, false, [], [3, 1]⟩,
        ⟨59190, false, false, [], [3, 1]⟩,
        ⟨59144, false, false, [], [3, 1]⟩,
        ⟨59145, false, false, [], [3, 1]⟩,
        ⟨59145, false, false, [], [3, 1]⟩,
        ⟨39738, false, false, [21583], [1]⟩,
        ⟨59196, false, false, [], [1]⟩,
        ⟨59197, false, false, [], [1]⟩,
        ⟨39980, false, false, [21583], [1]⟩,
        ⟨59128, true, false, [], [87013, 1]⟩,
        ⟨59196, false, false, [], [1]⟩,
        ⟨59197, false, false, [], [1]⟩,
        ⟨59197, false, false, [], [1]⟩,
        ⟨39735, false, false, [21583], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 925. -/
def y322TCIndexRaw925 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[21583, 87009], [21583, 87009], .contexts []⟩,
    ⟨[21583, 87009], [21583, 87009], .contexts []⟩,
    ⟨[90101], [90099, 5], .source 45115⟩,
    ⟨[90101, 5], [90099], .contexts [
        ⟨59202, false, false, [], [5]⟩,
        ⟨28, false, false, [90099], []⟩,
        ⟨59195, false, false, [], []⟩
      ]⟩,
    ⟨[90101], [90101], .contexts []⟩,
    ⟨[90101], [90101], .contexts []⟩,
    ⟨[90103], [90101, 1], .source 45116⟩,
    ⟨[90101, 1], [90103], .contexts [
        ⟨59206, true, false, [], []⟩
      ]⟩,
    ⟨[90103, 1], [90101], .contexts [
        ⟨59207, true, false, [], [1]⟩,
        ⟨8, false, false, [90101], []⟩,
        ⟨59205, false, false, [], []⟩
      ]⟩,
    ⟨[90103], [90103], .contexts []⟩,
    ⟨[90103], [90103], .contexts []⟩,
    ⟨[90101, 5], [90099], .contexts [
        ⟨59203, false, false, [], []⟩
      ]⟩,
    ⟨[90101, 5, 1], [21583, 87009], .contexts [
        ⟨59211, false, false, [], [1]⟩,
        ⟨59194, false, false, [], [1]⟩,
        ⟨59195, false, false, [], [1]⟩,
        ⟨59195, false, false, [], [1]⟩,
        ⟨59147, false, false, [21584], [90099, 1]⟩,
        ⟨504, true, false, [21584, 21582, 90099], [1]⟩,
        ⟨59199, false, false, [21584, 21582], [15, 1, 1]⟩,
        ⟨39732, false, false, [21584], [1, 1]⟩,
        ⟨59200, false, false, [21584, 21582], [1, 1]⟩,
        ⟨59201, false, false, [21584, 21582], [1, 1]⟩,
        ⟨8, false, false, [21584, 87009], []⟩,
        ⟨59149, true, false, [], [87009]⟩,
        ⟨59200, false, false, [], []⟩,
        ⟨59201, false, false, [], []⟩
      ]⟩,
    ⟨[90105], [90103, 9], .source 45117⟩,
    ⟨[90103, 9], [90105], .contexts [
        ⟨59213, true, false, [], []⟩
      ]⟩,
    ⟨[90107], [90105, 11], .source 45118⟩,
    ⟨[90105, 11], [90107], .contexts [
        ⟨59215, true, false, [], []⟩
      ]⟩,
    ⟨[90105], [90105], .contexts []⟩,
    ⟨[90107], [90107], .contexts []⟩,
    ⟨[90107], [90107], .contexts []⟩,
    ⟨[90109], [90107, 1], .source 45119⟩,
    ⟨[90107, 1], [90109], .contexts [
        ⟨59220, true, false, [], []⟩
      ]⟩,
    ⟨[90111], [90109, 13], .source 45120⟩,
    ⟨[90109, 13], [90111], .contexts [
        ⟨59222, true, false, [], []⟩
      ]⟩,
    ⟨[90109], [90109], .contexts []⟩,
    ⟨[90113], [90111, 15], .source 45121⟩,
    ⟨[90111, 15], [90113], .contexts [
        ⟨59225, true, false, [], []⟩
      ]⟩,
    ⟨[90111], [90111], .contexts []⟩,
    ⟨[90115], [90113, 1], .source 45122⟩,
    ⟨[90113, 1], [90115], .contexts [
        ⟨59228, true, false, [], []⟩
      ]⟩,
    ⟨[90113], [90113], .contexts []⟩,
    ⟨[90117], [90115, 3], .source 45123⟩,
    ⟨[90115, 3], [90117], .contexts [
        ⟨59231, true, false, [], []⟩
      ]⟩,
    ⟨[90115], [90115], .contexts []⟩,
    ⟨[90119], [90117, 5], .source 45124⟩,
    ⟨[90117, 5], [90119], .contexts [
        ⟨59234, true, false, [], []⟩
      ]⟩,
    ⟨[90117], [90117], .contexts []⟩,
    ⟨[90121], [90119, 1], .source 45125⟩,
    ⟨[90119, 1], [90121], .contexts [
        ⟨59237, true, false, [], []⟩
      ]⟩,
    ⟨[90119], [90119], .contexts []⟩,
    ⟨[90123], [90121, 9], .source 45126⟩,
    ⟨[90121, 9], [90123], .contexts [
        ⟨59240, true, false, [], []⟩
      ]⟩,
    ⟨[90121], [90121], .contexts []⟩,
    ⟨[90125], [90123, 11], .source 45127⟩,
    ⟨[90123, 11], [90125], .contexts [
        ⟨59243, true, false, [], []⟩
      ]⟩,
    ⟨[90123], [90123], .contexts []⟩,
    ⟨[90127], [90125, 1], .source 45128⟩,
    ⟨[90125, 1], [90127], .contexts [
        ⟨59246, true, false, [], []⟩
      ]⟩,
    ⟨[90125], [90125], .contexts []⟩,
    ⟨[90129], [90127, 13], .source 45129⟩,
    ⟨[90127, 13], [90129], .contexts [
        ⟨59249, true, false, [], []⟩
      ]⟩,
    ⟨[90127], [90127], .contexts []⟩,
    ⟨[90131], [90129, 15], .source 45130⟩,
    ⟨[90129, 15], [90131], .contexts [
        ⟨59252, true, false, [], []⟩
      ]⟩,
    ⟨[90129], [90129], .contexts []⟩,
    ⟨[90133], [90131, 1], .source 45131⟩,
    ⟨[90131, 1], [90133], .contexts [
        ⟨59255, true, false, [], []⟩
      ]⟩,
    ⟨[90131], [90131], .contexts []⟩,
    ⟨[90135], [90133, 3], .source 45132⟩,
    ⟨[90133, 3], [90135], .contexts [
        ⟨59258, true, false, [], []⟩
      ]⟩,
    ⟨[90133], [90133], .contexts []⟩,
    ⟨[90137], [90135, 5], .source 45133⟩,
    ⟨[90135, 5], [90137], .contexts [
        ⟨59261, true, false, [], []⟩
      ]⟩,
    ⟨[90135], [90135], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 926. -/
def y322TCIndexRaw926 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90139], [90137, 1], .source 45134⟩,
    ⟨[90137, 1], [90139], .contexts [
        ⟨59264, true, false, [], []⟩
      ]⟩,
    ⟨[90137], [90137], .contexts []⟩,
    ⟨[90141], [90139, 9], .source 45135⟩,
    ⟨[90139, 9], [90141], .contexts [
        ⟨59267, true, false, [], []⟩
      ]⟩,
    ⟨[90139], [90139], .contexts []⟩,
    ⟨[90143], [90141, 11], .source 45136⟩,
    ⟨[90141, 11], [90143], .contexts [
        ⟨59270, true, false, [], []⟩
      ]⟩,
    ⟨[90141], [90141], .contexts []⟩,
    ⟨[90143, 11], [90141], .contexts [
        ⟨59271, true, false, [], [11]⟩,
        ⟨53, false, false, [90141], []⟩,
        ⟨59272, false, false, [], []⟩
      ]⟩,
    ⟨[90145], [90143, 1], .source 45137⟩,
    ⟨[90143, 1], [90145], .contexts [
        ⟨59274, true, false, [], []⟩
      ]⟩,
    ⟨[90143], [90143], .contexts []⟩,
    ⟨[90145, 1], [90143], .contexts [
        ⟨59275, true, false, [], [1]⟩,
        ⟨8, false, false, [90143], []⟩,
        ⟨59276, false, false, [], []⟩
      ]⟩,
    ⟨[90147], [90145, 13], .source 45138⟩,
    ⟨[90145, 13], [90147], .contexts [
        ⟨59278, true, false, [], []⟩
      ]⟩,
    ⟨[90145], [90145], .contexts []⟩,
    ⟨[90149], [90147, 15], .source 45139⟩,
    ⟨[90147, 15], [90149], .contexts [
        ⟨59281, true, false, [], []⟩
      ]⟩,
    ⟨[90147], [90147], .contexts []⟩,
    ⟨[90151], [90149, 1], .source 45140⟩,
    ⟨[90149, 1], [90151], .contexts [
        ⟨59284, true, false, [], []⟩
      ]⟩,
    ⟨[90149], [90149], .contexts []⟩,
    ⟨[90153], [90151, 3], .source 45141⟩,
    ⟨[90151, 3], [90153], .contexts [
        ⟨59287, true, false, [], []⟩
      ]⟩,
    ⟨[90151], [90151], .contexts []⟩,
    ⟨[90155], [90153, 5], .source 45142⟩,
    ⟨[90153, 5], [90155], .contexts [
        ⟨59290, true, false, [], []⟩
      ]⟩,
    ⟨[90153], [90153], .contexts []⟩,
    ⟨[90155, 5], [90153], .contexts [
        ⟨59291, true, false, [], [5]⟩,
        ⟨28, false, false, [90153], []⟩,
        ⟨59292, false, false, [], []⟩
      ]⟩,
    ⟨[90157], [90155, 1], .source 45143⟩,
    ⟨[90155, 1], [90157], .contexts [
        ⟨59294, true, false, [], []⟩
      ]⟩,
    ⟨[90155], [90155], .contexts []⟩,
    ⟨[90157, 1], [90155], .contexts [
        ⟨59295, true, false, [], [1]⟩,
        ⟨8, false, false, [90155], []⟩,
        ⟨59296, false, false, [], []⟩
      ]⟩,
    ⟨[90159], [90157, 9], .source 45144⟩,
    ⟨[90157, 9], [90159], .contexts [
        ⟨59298, true, false, [], []⟩
      ]⟩,
    ⟨[90157], [90157], .contexts []⟩,
    ⟨[90161], [90159, 11], .source 45145⟩,
    ⟨[90159, 11], [90161], .contexts [
        ⟨59301, true, false, [], []⟩
      ]⟩,
    ⟨[90159], [90159], .contexts []⟩,
    ⟨[90163], [90161, 1], .source 45146⟩,
    ⟨[90161, 1], [90163], .contexts [
        ⟨59304, true, false, [], []⟩
      ]⟩,
    ⟨[90161], [90161], .contexts []⟩,
    ⟨[90165], [90163, 13], .source 45147⟩,
    ⟨[90163, 13], [90165], .contexts [
        ⟨59307, true, false, [], []⟩
      ]⟩,
    ⟨[90163], [90163], .contexts []⟩,
    ⟨[90167], [90165, 15], .source 45148⟩,
    ⟨[90165, 15], [90167], .contexts [
        ⟨59310, true, false, [], []⟩
      ]⟩,
    ⟨[90165], [90165], .contexts []⟩,
    ⟨[90167, 15], [90165], .contexts [
        ⟨59311, true, false, [], [15]⟩,
        ⟨1, false, false, [90165], []⟩,
        ⟨59312, false, false, [], []⟩
      ]⟩,
    ⟨[90169], [90167, 1], .source 45149⟩,
    ⟨[90167, 1], [90169], .contexts [
        ⟨59314, true, false, [], []⟩
      ]⟩,
    ⟨[90167], [90167], .contexts []⟩,
    ⟨[90169, 1], [90167], .contexts [
        ⟨59315, true, false, [], [1]⟩,
        ⟨8, false, false, [90167], []⟩,
        ⟨59316, false, false, [], []⟩
      ]⟩,
    ⟨[90171], [90169, 3], .source 45150⟩,
    ⟨[90169, 3], [90171], .contexts [
        ⟨59318, true, false, [], []⟩
      ]⟩,
    ⟨[90169], [90169], .contexts []⟩,
    ⟨[90171, 3], [90169], .contexts [
        ⟨59319, true, false, [], [3]⟩,
        ⟨20, false, false, [90169], []⟩,
        ⟨59320, false, false, [], []⟩
      ]⟩,
    ⟨[90173], [90171, 5], .source 45151⟩,
    ⟨[90171, 5], [90173], .contexts [
        ⟨59322, true, false, [], []⟩
      ]⟩,
    ⟨[90171], [90171], .contexts []⟩,
    ⟨[90175], [90173, 1], .source 45152⟩,
    ⟨[90173, 1], [90175], .contexts [
        ⟨59325, true, false, [], []⟩
      ]⟩,
    ⟨[90173], [90173], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 927. -/
def y322TCIndexRaw927 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90177], [90175, 9], .source 45153⟩,
    ⟨[90175, 9], [90177], .contexts [
        ⟨59328, true, false, [], []⟩
      ]⟩,
    ⟨[90175], [90175], .contexts []⟩,
    ⟨[90179], [90177, 11], .source 45154⟩,
    ⟨[90177, 11], [90179], .contexts [
        ⟨59331, true, false, [], []⟩
      ]⟩,
    ⟨[90177], [90177], .contexts []⟩,
    ⟨[90179, 11], [90177], .contexts [
        ⟨59332, true, false, [], [11]⟩,
        ⟨53, false, false, [90177], []⟩,
        ⟨59333, false, false, [], []⟩
      ]⟩,
    ⟨[90181], [90179, 1], .source 45155⟩,
    ⟨[90179, 1], [90181], .contexts [
        ⟨59335, true, false, [], []⟩
      ]⟩,
    ⟨[90179], [90179], .contexts []⟩,
    ⟨[90181, 1], [90179], .contexts [
        ⟨59336, true, false, [], [1]⟩,
        ⟨8, false, false, [90179], []⟩,
        ⟨59337, false, false, [], []⟩
      ]⟩,
    ⟨[90183], [90181, 13], .source 45156⟩,
    ⟨[90181, 13], [90183], .contexts [
        ⟨59339, true, false, [], []⟩
      ]⟩,
    ⟨[90181], [90181], .contexts []⟩,
    ⟨[90183, 13], [90181], .contexts [
        ⟨59340, true, false, [], [13]⟩,
        ⟨59, false, false, [90181], []⟩,
        ⟨59341, false, false, [], []⟩
      ]⟩,
    ⟨[90185], [90183, 15], .source 45157⟩,
    ⟨[90183, 15], [90185], .contexts [
        ⟨59343, true, false, [], []⟩
      ]⟩,
    ⟨[90183], [90183], .contexts []⟩,
    ⟨[90185, 15], [90183], .contexts [
        ⟨59344, true, false, [], [15]⟩,
        ⟨1, false, false, [90183], []⟩,
        ⟨59345, false, false, [], []⟩
      ]⟩,
    ⟨[90187], [90185, 1], .source 45158⟩,
    ⟨[90185], [90185], .contexts []⟩,
    ⟨[90187, 1], [90185], .contexts [
        ⟨59347, false, false, [], [1]⟩,
        ⟨8, false, false, [90185], []⟩,
        ⟨59348, false, false, [], []⟩
      ]⟩,
    ⟨[90189], [90187, 3], .source 45159⟩,
    ⟨[90187, 3], [90189], .contexts [
        ⟨59350, true, false, [], []⟩
      ]⟩,
    ⟨[90187], [90187], .contexts []⟩,
    ⟨[90189, 3], [90187], .contexts [
        ⟨59351, true, false, [], [3]⟩,
        ⟨20, false, false, [90187], []⟩,
        ⟨59352, false, false, [], []⟩
      ]⟩,
    ⟨[90191], [90189, 5], .source 45160⟩,
    ⟨[90189, 5], [90191], .contexts [
        ⟨59354, true, false, [], []⟩
      ]⟩,
    ⟨[90189], [90189], .contexts []⟩,
    ⟨[90191, 5], [90189], .contexts [
        ⟨59355, true, false, [], [5]⟩,
        ⟨28, false, false, [90189], []⟩,
        ⟨59356, false, false, [], []⟩
      ]⟩,
    ⟨[90193], [90191, 1], .source 45161⟩,
    ⟨[90191, 1], [90193], .contexts [
        ⟨59358, true, false, [], []⟩
      ]⟩,
    ⟨[90191], [90191], .contexts []⟩,
    ⟨[90193, 1], [90191], .contexts [
        ⟨59359, true, false, [], [1]⟩,
        ⟨8, false, false, [90191], []⟩,
        ⟨59360, false, false, [], []⟩
      ]⟩,
    ⟨[90195], [90193, 9], .source 45162⟩,
    ⟨[90193, 9], [90195], .contexts [
        ⟨59362, true, false, [], []⟩
      ]⟩,
    ⟨[90193], [90193], .contexts []⟩,
    ⟨[90195, 9], [90193], .contexts [
        ⟨59363, true, false, [], [9]⟩,
        ⟨46, false, false, [90193], []⟩,
        ⟨59364, false, false, [], []⟩
      ]⟩,
    ⟨[90197], [90195, 11], .source 45163⟩,
    ⟨[90195], [90195], .contexts []⟩,
    ⟨[90197, 11], [90195], .contexts [
        ⟨59366, false, false, [], [11]⟩,
        ⟨53, false, false, [90195], []⟩,
        ⟨59367, false, false, [], []⟩
      ]⟩,
    ⟨[90199], [90197, 1], .source 45164⟩,
    ⟨[90197], [90197], .contexts []⟩,
    ⟨[90199, 1], [90197], .contexts [
        ⟨59369, false, false, [], [1]⟩,
        ⟨8, false, false, [90197], []⟩,
        ⟨59370, false, false, [], []⟩
      ]⟩,
    ⟨[90201], [90199, 13], .source 45165⟩,
    ⟨[90199], [90199], .contexts []⟩,
    ⟨[90201, 13], [90199], .contexts [
        ⟨59372, false, false, [], [13]⟩,
        ⟨59, false, false, [90199], []⟩,
        ⟨59373, false, false, [], []⟩
      ]⟩,
    ⟨[90203], [90201, 15], .source 45166⟩,
    ⟨[90201], [90201], .contexts []⟩,
    ⟨[90203, 15], [90201], .contexts [
        ⟨59375, false, false, [], [15]⟩,
        ⟨1, false, false, [90201], []⟩,
        ⟨59376, false, false, [], []⟩
      ]⟩,
    ⟨[90205], [90203, 1], .source 45167⟩,
    ⟨[90203, 1], [90205], .contexts [
        ⟨59378, true, false, [], []⟩
      ]⟩,
    ⟨[90203], [90203], .contexts []⟩,
    ⟨[90205, 1], [90203], .contexts [
        ⟨59379, true, false, [], [1]⟩,
        ⟨8, false, false, [90203], []⟩,
        ⟨59380, false, false, [], []⟩
      ]⟩,
    ⟨[90207], [90205, 3], .source 45168⟩,
    ⟨[90205, 3], [90207], .contexts [
        ⟨59382, true, false, [], []⟩
      ]⟩,
    ⟨[90205], [90205], .contexts []⟩,
    ⟨[90207, 3], [90205], .contexts [
        ⟨59383, true, false, [], [3]⟩,
        ⟨20, false, false, [90205], []⟩,
        ⟨59384, false, false, [], []⟩
      ]⟩,
    ⟨[90209], [90207, 5], .source 45169⟩,
    ⟨[90207, 5], [90209], .contexts [
        ⟨59386, true, false, [], []⟩
      ]⟩,
    ⟨[90207], [90207], .contexts []⟩,
    ⟨[90209, 5], [90207], .contexts [
        ⟨59387, true, false, [], [5]⟩,
        ⟨28, false, false, [90207], []⟩,
        ⟨59388, false, false, [], []⟩
      ]⟩,
    ⟨[90211], [90209, 1], .source 45170⟩,
    ⟨[90209, 1], [90211], .contexts [
        ⟨59390, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 928. -/
def y322TCIndexRaw928 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90209], [90209], .contexts []⟩,
    ⟨[90211, 1], [90209], .contexts [
        ⟨59391, true, false, [], [1]⟩,
        ⟨8, false, false, [90209], []⟩,
        ⟨59392, false, false, [], []⟩
      ]⟩,
    ⟨[90213], [90211, 9], .source 45171⟩,
    ⟨[90211, 9], [90213], .contexts [
        ⟨59394, true, false, [], []⟩
      ]⟩,
    ⟨[90211], [90211], .contexts []⟩,
    ⟨[90213, 9], [90211], .contexts [
        ⟨59395, true, false, [], [9]⟩,
        ⟨46, false, false, [90211], []⟩,
        ⟨59396, false, false, [], []⟩
      ]⟩,
    ⟨[90215], [90213, 11], .source 45172⟩,
    ⟨[90213, 11], [90215], .contexts [
        ⟨59398, true, false, [], []⟩
      ]⟩,
    ⟨[90213], [90213], .contexts []⟩,
    ⟨[90215, 11], [90213], .contexts [
        ⟨59399, true, false, [], [11]⟩,
        ⟨53, false, false, [90213], []⟩,
        ⟨59400, false, false, [], []⟩
      ]⟩,
    ⟨[90217], [90215, 1], .source 45173⟩,
    ⟨[90215], [90215], .contexts []⟩,
    ⟨[90217, 1], [90215], .contexts [
        ⟨59402, false, false, [], [1]⟩,
        ⟨8, false, false, [90215], []⟩,
        ⟨59403, false, false, [], []⟩
      ]⟩,
    ⟨[90219], [90217, 13], .source 45174⟩,
    ⟨[90217], [90217], .contexts []⟩,
    ⟨[90219, 13], [90217], .contexts [
        ⟨59405, false, false, [], [13]⟩,
        ⟨59, false, false, [90217], []⟩,
        ⟨59406, false, false, [], []⟩
      ]⟩,
    ⟨[90221], [90219, 15], .source 45175⟩,
    ⟨[90219, 15], [90221], .contexts [
        ⟨59408, true, false, [], []⟩
      ]⟩,
    ⟨[90219], [90219], .contexts []⟩,
    ⟨[90219, 15], [90221], .contexts [
        ⟨59409, false, false, [], []⟩
      ]⟩,
    ⟨[90221], [90221], .contexts []⟩,
    ⟨[90219, 13], [90217], .contexts [
        ⟨59407, false, false, [], []⟩
      ]⟩,
    ⟨[90219, 13], [90217], .contexts [
        ⟨59413, false, false, [], []⟩,
        ⟨59406, false, false, [], []⟩,
        ⟨59406, false, false, [], []⟩
      ]⟩,
    ⟨[90215], [90215], .contexts []⟩,
    ⟨[90211], [90211], .contexts []⟩,
    ⟨[90211, 1], [90209], .contexts [
        ⟨59393, false, false, [], []⟩
      ]⟩,
    ⟨[90209], [90209], .contexts []⟩,
    ⟨[90209, 5], [90207], .contexts [
        ⟨59389, false, false, [], []⟩
      ]⟩,
    ⟨[90207], [90207], .contexts []⟩,
    ⟨[90219, 13, 1, 11, 9, 1, 5], [90207], .contexts [
        ⟨59414, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨59404, false, false, [], [11, 9, 1, 5]⟩,
        ⟨59415, false, false, [], [11, 9, 1, 5]⟩,
        ⟨59403, false, false, [], [11, 9, 1, 5]⟩,
        ⟨59403, false, false, [], [11, 9, 1, 5]⟩,
        ⟨59401, false, false, [], [9, 1, 5]⟩,
        ⟨59400, false, false, [], [9, 1, 5]⟩,
        ⟨59400, false, false, [], [9, 1, 5]⟩,
        ⟨59397, false, false, [], [1, 5]⟩,
        ⟨59416, false, false, [], [1, 5]⟩,
        ⟨59396, false, false, [], [1, 5]⟩,
        ⟨59396, false, false, [], [1, 5]⟩,
        ⟨59417, false, false, [], [5]⟩,
        ⟨59418, false, false, [], [5]⟩,
        ⟨59392, false, false, [], [5]⟩,
        ⟨59392, false, false, [], [5]⟩,
        ⟨59419, false, false, [], []⟩,
        ⟨59420, false, false, [], []⟩,
        ⟨59388, false, false, [], []⟩,
        ⟨59388, false, false, [], []⟩
      ]⟩,
    ⟨[90207, 3], [90205], .contexts [
        ⟨59385, false, false, [], []⟩
      ]⟩,
    ⟨[90205], [90205], .contexts []⟩,
    ⟨[90205, 1], [90203], .contexts [
        ⟨59381, false, false, [], []⟩
      ]⟩,
    ⟨[90203], [90203], .contexts []⟩,
    ⟨[90203, 15], [90201], .contexts [
        ⟨59377, false, false, [], []⟩
      ]⟩,
    ⟨[90201], [90201], .contexts []⟩,
    ⟨[90201, 13], [90199], .contexts [
        ⟨59374, false, false, [], []⟩
      ]⟩,
    ⟨[90199], [90199], .contexts []⟩,
    ⟨[90199, 1], [90197], .contexts [
        ⟨59371, false, false, [], []⟩
      ]⟩,
    ⟨[90197], [90197], .contexts []⟩,
    ⟨[90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1], [90197], .contexts [
        ⟨59421, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨59422, false, false, [], [1, 15, 13, 1]⟩,
        ⟨59423, false, false, [], [1, 15, 13, 1]⟩,
        ⟨59384, false, false, [], [1, 15, 13, 1]⟩,
        ⟨59384, false, false, [], [1, 15, 13, 1]⟩,
        ⟨59424, false, false, [], [15, 13, 1]⟩,
        ⟨59425, false, false, [], [15, 13, 1]⟩,
        ⟨59380, false, false, [], [15, 13, 1]⟩,
        ⟨59380, false, false, [], [15, 13, 1]⟩,
        ⟨59426, false, false, [], [13, 1]⟩,
        ⟨59427, false, false, [], [13, 1]⟩,
        ⟨59376, false, false, [], [13, 1]⟩,
        ⟨59376, false, false, [], [13, 1]⟩,
        ⟨59428, false, false, [], [1]⟩,
        ⟨59429, false, false, [], [1]⟩,
        ⟨59373, false, false, [], [1]⟩,
        ⟨59373, false, false, [], [1]⟩,
        ⟨59430, false, false, [], []⟩,
        ⟨59431, false, false, [], []⟩,
        ⟨59370, false, false, [], []⟩,
        ⟨59370, false, false, [], []⟩
      ]⟩,
    ⟨[90197, 11], [90195], .contexts [
        ⟨59368, false, false, [], []⟩
      ]⟩,
    ⟨[90195], [90195], .contexts []⟩,
    ⟨[90195, 9], [90193], .contexts [
        ⟨59365, false, false, [], []⟩
      ]⟩,
    ⟨[90193], [90193], .contexts []⟩,
    ⟨[90193, 1], [90191], .contexts [
        ⟨59361, false, false, [], []⟩
      ]⟩,
    ⟨[90191], [90191], .contexts []⟩,
    ⟨[90191, 5], [90189], .contexts [
        ⟨59357, false, false, [], []⟩
      ]⟩,
    ⟨[90189], [90189], .contexts []⟩,
    ⟨[90189, 3], [90187], .contexts [
        ⟨59353, false, false, [], []⟩
      ]⟩,
    ⟨[90187], [90187], .contexts []⟩,
    ⟨[
      90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3
    ], [90187], .contexts [
        ⟨59432, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨59433, false, false, [], [9, 1, 5, 3]⟩,
        ⟨59434, false, false, [], [9, 1, 5, 3]⟩,
        ⟨59367, false, false, [], [9, 1, 5, 3]⟩,
        ⟨59367, false, false, [], [9, 1, 5, 3]⟩,
        ⟨59435, false, false, [], [1, 5, 3]⟩,
        ⟨59436, false, false, [], [1, 5, 3]⟩,
        ⟨59364, false, false, [], [1, 5, 3]⟩,
        ⟨59364, false, false, [], [1, 5, 3]⟩,
        ⟨59437, false, false, [], [5, 3]⟩,
        ⟨59438, false, false, [], [5, 3]⟩,
        ⟨59360, false, false, [], [5, 3]⟩,
        ⟨59360, false, false, [], [5, 3]⟩,
        ⟨59439, false, false, [], [3]⟩,
        ⟨59440, false, false, [], [3]⟩,
        ⟨59356, false, false, [], [3]⟩,
        ⟨59356, false, false, [], [3]⟩,
        ⟨59441, false, false, [], []⟩,
        ⟨59442, false, false, [], []⟩,
        ⟨59352, false, false, [], []⟩,
        ⟨59352, false, false, [], []⟩
      ]⟩,
    ⟨[90187, 1], [90185], .contexts [
        ⟨59349, false, false, [], []⟩
      ]⟩,
    ⟨[90185], [90185], .contexts []⟩,
    ⟨[90183], [90183], .contexts []⟩,
    ⟨[90181], [90181], .contexts []⟩,
    ⟨[90181, 1], [90179], .contexts [
        ⟨59338, false, false, [], []⟩
      ]⟩,
    ⟨[90179], [90179], .contexts []⟩,
    ⟨[90177], [90177], .contexts []⟩,
    ⟨[
      90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [90177], .contexts [
        ⟨59443, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨59444, false, false, [], [15, 13, 1, 11]⟩,
        ⟨59445, false, false, [], [15, 13, 1, 11]⟩,
        ⟨59348, false, false, [], [15, 13, 1, 11]⟩,
        ⟨59348, false, false, [], [15, 13, 1, 11]⟩,
        ⟨59346, false, false, [], [13, 1, 11]⟩,
        ⟨59446, false, false, [], [13, 1, 11]⟩,
        ⟨59345, false, false, [], [13, 1, 11]⟩,
        ⟨59345, false, false, [], [13, 1, 11]⟩,
        ⟨59342, false, false, [], [1, 11]⟩,
        ⟨59447, false, false, [], [1, 11]⟩,
        ⟨59341, false, false, [], [1, 11]⟩,
        ⟨59341, false, false, [], [1, 11]⟩,
        ⟨59448, false, false, [], [11]⟩,
        ⟨59449, false, false, [], [11]⟩,
        ⟨59337, false, false, [], [11]⟩,
        ⟨59337, false, false, [], [11]⟩,
        ⟨59334, false, false, [], []⟩,
        ⟨59450, false, false, [], []⟩,
        ⟨59333, false, false, [], []⟩,
        ⟨59333, false, false, [], []⟩
      ]⟩,
    ⟨[90175], [90175], .contexts []⟩,
    ⟨[90173], [90173], .contexts []⟩,
    ⟨[90171], [90171], .contexts []⟩,
    ⟨[90169], [90169], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 929. -/
def y322TCIndexRaw929 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[
      90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3
    ], [90169], .contexts [
        ⟨59451, false, false, [], [9, 1, 5, 3]⟩,
        ⟨59329, true, false, [], [9, 1, 5, 3]⟩,
        ⟨46, false, false, [90175], [1, 5, 3]⟩,
        ⟨59330, false, false, [], [1, 5, 3]⟩,
        ⟨59452, false, false, [], [1, 5, 3]⟩,
        ⟨59330, false, false, [], [1, 5, 3]⟩,
        ⟨59330, false, false, [], [1, 5, 3]⟩,
        ⟨59326, true, false, [], [1, 5, 3]⟩,
        ⟨8, false, false, [90173], [5, 3]⟩,
        ⟨59327, false, false, [], [5, 3]⟩,
        ⟨59453, false, false, [], [5, 3]⟩,
        ⟨59327, false, false, [], [5, 3]⟩,
        ⟨59327, false, false, [], [5, 3]⟩,
        ⟨59323, true, false, [], [5, 3]⟩,
        ⟨28, false, false, [90171], [3]⟩,
        ⟨59324, false, false, [], [3]⟩,
        ⟨59454, false, false, [], [3]⟩,
        ⟨59324, false, false, [], [3]⟩,
        ⟨59324, false, false, [], [3]⟩,
        ⟨59321, false, false, [], []⟩,
        ⟨59455, false, false, [], []⟩,
        ⟨59320, false, false, [], []⟩,
        ⟨59320, false, false, [], []⟩
      ]⟩,
    ⟨[90169, 1], [90167], .contexts [
        ⟨59317, false, false, [], []⟩
      ]⟩,
    ⟨[90167], [90167], .contexts []⟩,
    ⟨[90167, 15], [90165], .contexts [
        ⟨59313, false, false, [], []⟩
      ]⟩,
    ⟨[90165], [90165], .contexts []⟩,
    ⟨[90163], [90163], .contexts []⟩,
    ⟨[90161], [90161], .contexts []⟩,
    ⟨[
      90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11
    ], [90159], .contexts [
        ⟨59456, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨59457, false, false, [], [15, 13, 1, 11]⟩,
        ⟨59458, false, false, [], [15, 13, 1, 11]⟩,
        ⟨59316, false, false, [], [15, 13, 1, 11]⟩,
        ⟨59316, false, false, [], [15, 13, 1, 11]⟩,
        ⟨59459, false, false, [], [13, 1, 11]⟩,
        ⟨59460, false, false, [], [13, 1, 11]⟩,
        ⟨59312, false, false, [], [13, 1, 11]⟩,
        ⟨59312, false, false, [], [13, 1, 11]⟩,
        ⟨59308, true, false, [], [13, 1, 11]⟩,
        ⟨59, false, false, [90163], [1, 11]⟩,
        ⟨59309, false, false, [], [1, 11]⟩,
        ⟨59461, false, false, [], [1, 11]⟩,
        ⟨59309, false, false, [], [1, 11]⟩,
        ⟨59309, false, false, [], [1, 11]⟩,
        ⟨59305, true, false, [], [1, 11]⟩,
        ⟨8, false, false, [90161], [11]⟩,
        ⟨59306, false, false, [], [11]⟩,
        ⟨59462, false, false, [], [11]⟩,
        ⟨59306, false, false, [], [11]⟩,
        ⟨59306, false, false, [], [11]⟩,
        ⟨59302, true, false, [], [11]⟩,
        ⟨53, false, false, [90159], []⟩,
        ⟨59303, false, false, [], []⟩,
        ⟨59303, false, false, [], []⟩,
        ⟨59303, false, false, [], []⟩
      ]⟩,
    ⟨[90155], [90155], .contexts []⟩,
    ⟨[90153], [90153], .contexts []⟩,
    ⟨[90151], [90151], .contexts []⟩,
    ⟨[
      90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [90151], .contexts [
        ⟨59463, false, false, [], [9, 1, 5, 3]⟩,
        ⟨59299, true, false, [], [9, 1, 5, 3]⟩,
        ⟨46, false, false, [90157], [1, 5, 3]⟩,
        ⟨59300, false, false, [], [1, 5, 3]⟩,
        ⟨59300, false, false, [], [1, 5, 3]⟩,
        ⟨59300, false, false, [], [1, 5, 3]⟩,
        ⟨59297, false, false, [], [5, 3]⟩,
        ⟨59464, false, false, [], [5, 3]⟩,
        ⟨59296, false, false, [], [5, 3]⟩,
        ⟨59296, false, false, [], [5, 3]⟩,
        ⟨59293, false, false, [], [3]⟩,
        ⟨59465, false, false, [], [3]⟩,
        ⟨59292, false, false, [], [3]⟩,
        ⟨59292, false, false, [], [3]⟩,
        ⟨59288, true, false, [], [3]⟩,
        ⟨20, false, false, [90151], []⟩,
        ⟨59289, false, false, [], []⟩,
        ⟨59466, false, false, [], []⟩,
        ⟨59289, false, false, [], []⟩,
        ⟨59289, false, false, [], []⟩
      ]⟩,
    ⟨[90149], [90149], .contexts []⟩,
    ⟨[90147], [90147], .contexts []⟩,
    ⟨[90143], [90143], .contexts []⟩,
    ⟨[
      90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1
    ], [90143], .contexts [
        ⟨59467, false, false, [], [1, 15, 13, 1]⟩,
        ⟨59285, true, false, [], [1, 15, 13, 1]⟩,
        ⟨8, false, false, [90149], [15, 13, 1]⟩,
        ⟨59286, false, false, [], [15, 13, 1]⟩,
        ⟨59468, false, false, [], [15, 13, 1]⟩,
        ⟨59286, false, false, [], [15, 13, 1]⟩,
        ⟨59286, false, false, [], [15, 13, 1]⟩,
        ⟨59282, true, false, [], [15, 13, 1]⟩,
        ⟨1, false, false, [90147], [13, 1]⟩,
        ⟨59283, false, false, [], [13, 1]⟩,
        ⟨59469, false, false, [], [13, 1]⟩,
        ⟨59283, false, false, [], [13, 1]⟩,
        ⟨59283, false, false, [], [13, 1]⟩,
        ⟨59279, true, false, [], [13, 1]⟩,
        ⟨59, false, false, [90145], [1]⟩,
        ⟨59280, false, false, [], [1]⟩,
        ⟨59280, false, false, [], [1]⟩,
        ⟨59280, false, false, [], [1]⟩,
        ⟨59277, false, false, [], []⟩,
        ⟨59470, false, false, [], []⟩,
        ⟨59276, false, false, [], []⟩,
        ⟨59276, false, false, [], []⟩
      ]⟩,
    ⟨[90141], [90141], .contexts []⟩,
    ⟨[90139], [90139], .contexts []⟩,
    ⟨[90137], [90137], .contexts []⟩,
    ⟨[90135], [90135], .contexts []⟩,
    ⟨[90133], [90133], .contexts []⟩,
    ⟨[
      90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3
    ], [90133], .contexts [
        ⟨59471, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨59273, false, false, [], [9, 1, 5, 3]⟩,
        ⟨59472, false, false, [], [9, 1, 5, 3]⟩,
        ⟨59272, false, false, [], [9, 1, 5, 3]⟩,
        ⟨59272, false, false, [], [9, 1, 5, 3]⟩,
        ⟨59268, true, false, [], [9, 1, 5, 3]⟩,
        ⟨46, false, false, [90139], [1, 5, 3]⟩,
        ⟨59269, false, false, [], [1, 5, 3]⟩,
        ⟨59473, false, false, [], [1, 5, 3]⟩,
        ⟨59269, false, false, [], [1, 5, 3]⟩,
        ⟨59269, false, false, [], [1, 5, 3]⟩,
        ⟨59265, true, false, [], [1, 5, 3]⟩,
        ⟨8, false, false, [90137], [5, 3]⟩,
        ⟨59266, false, false, [], [5, 3]⟩,
        ⟨59474, false, false, [], [5, 3]⟩,
        ⟨59266, false, false, [], [5, 3]⟩,
        ⟨59266, false, false, [], [5, 3]⟩,
        ⟨59262, true, false, [], [5, 3]⟩,
        ⟨28, false, false, [90135], [3]⟩,
        ⟨59263, false, false, [], [3]⟩,
        ⟨59475, false, false, [], [3]⟩,
        ⟨59263, false, false, [], [3]⟩,
        ⟨59263, false, false, [], [3]⟩,
        ⟨59259, true, false, [], [3]⟩,
        ⟨20, false, false, [90133], []⟩,
        ⟨59260, false, false, [], []⟩,
        ⟨59476, false, false, [], []⟩,
        ⟨59260, false, false, [], []⟩,
        ⟨59260, false, false, [], []⟩
      ]⟩,
    ⟨[90131], [90131], .contexts []⟩,
    ⟨[90129], [90129], .contexts []⟩,
    ⟨[90127], [90127], .contexts []⟩,
    ⟨[90125], [90125], .contexts []⟩,
    ⟨[
      90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [90125], .contexts [
        ⟨59477, false, false, [], [1, 15, 13, 1]⟩,
        ⟨59256, true, false, [], [1, 15, 13, 1]⟩,
        ⟨8, false, false, [90131], [15, 13, 1]⟩,
        ⟨59257, false, false, [], [15, 13, 1]⟩,
        ⟨59478, false, false, [], [15, 13, 1]⟩,
        ⟨59257, false, false, [], [15, 13, 1]⟩,
        ⟨59257, false, false, [], [15, 13, 1]⟩,
        ⟨59253, true, false, [], [15, 13, 1]⟩,
        ⟨1, false, false, [90129], [13, 1]⟩,
        ⟨59254, false, false, [], [13, 1]⟩,
        ⟨59479, false, false, [], [13, 1]⟩,
        ⟨59254, false, false, [], [13, 1]⟩,
        ⟨59254, false, false, [], [13, 1]⟩,
        ⟨59250, true, false, [], [13, 1]⟩,
        ⟨59, false, false, [90127], [1]⟩,
        ⟨59251, false, false, [], [1]⟩,
        ⟨59480, false, false, [], [1]⟩,
        ⟨59251, false, false, [], [1]⟩,
        ⟨59251, false, false, [], [1]⟩,
        ⟨59247, true, false, [], [1]⟩,
        ⟨8, false, false, [90125], []⟩,
        ⟨59248, false, false, [], []⟩,
        ⟨59481, false, false, [], []⟩,
        ⟨59248, false, false, [], []⟩,
        ⟨59248, false, false, [], []⟩
      ]⟩,
    ⟨[90123], [90123], .contexts []⟩,
    ⟨[90121], [90121], .contexts []⟩,
    ⟨[90119], [90119], .contexts []⟩,
    ⟨[90117], [90117], .contexts []⟩,
    ⟨[
      90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5
    ], [90117], .contexts [
        ⟨59482, false, false, [], [11, 9, 1, 5]⟩,
        ⟨59244, true, false, [], [11, 9, 1, 5]⟩,
        ⟨53, false, false, [90123], [9, 1, 5]⟩,
        ⟨59245, false, false, [], [9, 1, 5]⟩,
        ⟨59483, false, false, [], [9, 1, 5]⟩,
        ⟨59245, false, false, [], [9, 1, 5]⟩,
        ⟨59245, false, false, [], [9, 1, 5]⟩,
        ⟨59241, true, false, [], [9, 1, 5]⟩,
        ⟨46, false, false, [90121], [1, 5]⟩,
        ⟨59242, false, false, [], [1, 5]⟩,
        ⟨59484, false, false, [], [1, 5]⟩,
        ⟨59242, false, false, [], [1, 5]⟩,
        ⟨59242, false, false, [], [1, 5]⟩,
        ⟨59238, true, false, [], [1, 5]⟩,
        ⟨8, false, false, [90119], [5]⟩,
        ⟨59239, false, false, [], [5]⟩,
        ⟨59485, false, false, [], [5]⟩,
        ⟨59239, false, false, [], [5]⟩,
        ⟨59239, false, false, [], [5]⟩,
        ⟨59235, true, false, [], [5]⟩,
        ⟨28, false, false, [90117], []⟩,
        ⟨59236, false, false, [], []⟩,
        ⟨59486, false, false, [], []⟩,
        ⟨59236, false, false, [], []⟩,
        ⟨59236, false, false, [], []⟩
      ]⟩,
    ⟨[90115], [90115], .contexts []⟩,
    ⟨[90113], [90113], .contexts []⟩,
    ⟨[90111], [90111], .contexts []⟩,
    ⟨[90109], [90109], .contexts []⟩,
    ⟨[
      90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13
    ], [90109], .contexts [
        ⟨59487, false, false, [], [3, 1, 15, 13]⟩,
        ⟨59232, true, false, [], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [90115], [1, 15, 13]⟩,
        ⟨59233, false, false, [], [1, 15, 13]⟩,
        ⟨59488, false, false, [], [1, 15, 13]⟩,
        ⟨59233, false, false, [], [1, 15, 13]⟩,
        ⟨59233, false, false, [], [1, 15, 13]⟩,
        ⟨59229, true, false, [], [1, 15, 13]⟩,
        ⟨8, false, false, [90113], [15, 13]⟩,
        ⟨59230, false, false, [], [15, 13]⟩,
        ⟨59489, false, false, [], [15, 13]⟩,
        ⟨59230, false, false, [], [15, 13]⟩,
        ⟨59230, false, false, [], [15, 13]⟩,
        ⟨59226, true, false, [], [15, 13]⟩,
        ⟨1, false, false, [90111], [13]⟩,
        ⟨59227, false, false, [], [13]⟩,
        ⟨59490, false, false, [], [13]⟩,
        ⟨59227, false, false, [], [13]⟩,
        ⟨59227, false, false, [], [13]⟩,
        ⟨59223, true, false, [], [13]⟩,
        ⟨59, false, false, [90109], []⟩,
        ⟨59224, false, false, [], []⟩,
        ⟨59491, false, false, [], []⟩,
        ⟨59224, false, false, [], []⟩,
        ⟨59224, false, false, [], []⟩
      ]⟩,
    ⟨[90105], [90105], .contexts []⟩,
    ⟨[
      90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [90101], .contexts [
        ⟨59492, false, false, [], [1, 11, 9, 1]⟩,
        ⟨59221, true, false, [], [1, 11, 9, 1]⟩,
        ⟨8, false, false, [90107], [11, 9, 1]⟩,
        ⟨59219, false, false, [], [11, 9, 1]⟩,
        ⟨59218, false, false, [], [11, 9, 1]⟩,
        ⟨59219, false, false, [], [11, 9, 1]⟩,
        ⟨59219, false, false, [], [11, 9, 1]⟩,
        ⟨59216, true, false, [], [11, 9, 1]⟩,
        ⟨53, false, false, [90105], [9, 1]⟩,
        ⟨59217, false, false, [], [9, 1]⟩,
        ⟨59493, false, false, [], [9, 1]⟩,
        ⟨59217, false, false, [], [9, 1]⟩,
        ⟨59217, false, false, [], [9, 1]⟩,
        ⟨59214, true, false, [], [9, 1]⟩,
        ⟨46, false, false, [90103], [1]⟩,
        ⟨59210, false, false, [], [1]⟩,
        ⟨59209, false, false, [], [1]⟩,
        ⟨59210, false, false, [], [1]⟩,
        ⟨59210, false, false, [], [1]⟩,
        ⟨59208, false, false, [], []⟩,
        ⟨59204, false, false, [], []⟩,
        ⟨59205, false, false, [], []⟩,
        ⟨59205, false, false, [], []⟩
      ]⟩,
    ⟨[
      90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13
    ], [86581], .contexts [
        ⟨59494, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨59211, false, false, [], [3, 1, 15, 13]⟩,
        ⟨59194, false, false, [], [3, 1, 15, 13]⟩,
        ⟨59195, false, false, [], [3, 1, 15, 13]⟩,
        ⟨59195, false, false, [], [3, 1, 15, 13]⟩,
        ⟨59192, true, false, [], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [90097], [1, 15, 13]⟩,
        ⟨59183, false, false, [], [1, 15, 13]⟩,
        ⟨59182, false, false, [], [1, 15, 13]⟩,
        ⟨59183, false, false, [], [1, 15, 13]⟩,
        ⟨59183, false, false, [], [1, 15, 13]⟩,
        ⟨59181, false, false, [], [15, 13]⟩,
        ⟨59167, false, false, [], [15, 13]⟩,
        ⟨59168, false, false, [], [15, 13]⟩,
        ⟨59168, false, false, [], [15, 13]⟩,
        ⟨59188, false, false, [], [13]⟩,
        ⟨59124, false, false, [], [13]⟩,
        ⟨59125, false, false, [], [13]⟩,
        ⟨59125, false, false, [], [13]⟩,
        ⟨59123, false, false, [], []⟩,
        ⟨38124, false, false, [], []⟩,
        ⟨38125, false, false, [], []⟩,
        ⟨38125, false, false, [], []⟩
      ]⟩,
    ⟨[24661], [16429, 17387], .source 12395⟩,
    ⟨[24663], [24661, 21487], .source 12396⟩,
    ⟨[24665], [24663, 21443], .source 12397⟩,
    ⟨[24667], [24665, 20325], .source 12398⟩,
    ⟨[
      90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [24667, 85353], .contexts [
        ⟨59495, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨38151, false, false, [], [11, 9, 1, 5]⟩,
        ⟨38130, false, false, [], [11, 9, 1, 5]⟩,
        ⟨38132, false, false, [], [11, 9, 1, 5]⟩,
        ⟨38132, false, false, [], [11, 9, 1, 5]⟩,
        ⟨38144, false, false, [16429], [9, 1, 5]⟩,
        ⟨59496, true, false, [], [86581, 9, 1, 5]⟩,
        ⟨45391, false, false, [24661], [1, 5]⟩,
        ⟨59497, true, false, [], [87681, 1, 5]⟩,
        ⟨45041, false, false, [24663], [5]⟩,
        ⟨45338, false, false, [24663], [5]⟩,
        ⟨59498, true, false, [], [83639, 5]⟩,
        ⟨41839, false, false, [24665], []⟩,
        ⟨59499, true, false, [], [85353]⟩
      ]⟩,
    ⟨[24669], [24667, 18139], .source 12399⟩,
    ⟨[24671], [24669, 15099], .source 12400⟩,
    ⟨[24673], [24671, 16859], .source 12401⟩,
    ⟨[24675], [24673, 15205], .source 12402⟩,
    ⟨[24677], [24675, 15221], .source 12403⟩,
    ⟨[
      90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1
    ], [24677, 82663], .contexts [
        ⟨59500, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨31736, false, false, [24667], [1, 15, 13, 1]⟩,
        ⟨59501, true, false, [], [84097, 1, 15, 13, 1]⟩,
        ⟨24760, false, false, [24669], [15, 13, 1]⟩,
        ⟨59502, true, false, [], [84097, 15, 13, 1]⟩,
        ⟨24787, false, false, [24671], [13, 1]⟩,
        ⟨59503, true, false, [], [82777, 13, 1]⟩,
        ⟨16518, false, false, [24673], [1]⟩,
        ⟨59504, true, false, [], [82653, 1]⟩,
        ⟨15094, false, false, [24675], []⟩,
        ⟨59505, true, false, [], [82663]⟩
      ]⟩,
    ⟨[24679], [24677, 15227], .source 12404⟩,
    ⟨[24681], [24679, 15269], .source 12405⟩,
    ⟨[24683], [24681, 15277], .source 12406⟩,
    ⟨[24685], [24683, 315], .source 12407⟩,
    ⟨[
      90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3
    ], [24685, 79001], .contexts [
        ⟨59506, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨16985, false, false, [24677], [9, 1, 5, 3]⟩,
        ⟨59507, true, false, [], [82815, 9, 1, 5, 3]⟩,
        ⟨16975, false, false, [24679], [1, 5, 3]⟩,
        ⟨15321, false, false, [24679], [5, 3]⟩,
        ⟨59508, true, false, [], [82681, 5, 3]⟩,
        ⟨15331, false, false, [24681], [3]⟩,
        ⟨59509, true, false, [], [79001, 3]⟩,
        ⟨5482, false, false, [24683], []⟩,
        ⟨59510, true, false, [], [79001]⟩
      ]⟩,
    ⟨[24687], [24685, 1075], .source 12408⟩,
    ⟨[
      90219, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11
    ], [24687, 82827], .contexts [
        ⟨59511, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨5608, false, false, [24685], [15, 13, 1, 11]⟩,
        ⟨5602, false, false, [24685], [13, 1, 11]⟩,
        ⟨5585, false, false, [24685], [1, 11]⟩,
        ⟨5595, false, false, [24685], [11]⟩,
        ⟨59512, true, false, [], [79019, 11]⟩,
        ⟨17170, false, false, [24687], []⟩
      ]⟩,
    ⟨[24689], [24687, 15439], .source 12409⟩,
    ⟨[24691], [24689, 15989], .source 12410⟩,
    ⟨[24691, 87335], [24691, 87335], .contexts []⟩,
    ⟨[24691, 87335], [24691, 87335], .contexts []⟩,
    ⟨[90221, 1], [90221, 1], .contexts []⟩,
    ⟨[90221, 1], [24691, 87335], .contexts [
        ⟨59518, false, false, [], []⟩,
        ⟨59412, true, false, [], [1]⟩,
        ⟨59412, true, false, [], [1]⟩,
        ⟨59411, true, false, [], [1]⟩,
        ⟨4071, false, false, [90219], []⟩,
        ⟨4073, false, false, [90219], []⟩,
        ⟨59513, false, false, [], [9, 1, 5, 3]⟩,
        ⟨17167, false, false, [24687], [1, 5, 3]⟩,
        ⟨59514, true, false, [], [82791, 1, 5, 3]⟩,
        ⟨19774, false, false, [24689], [5, 3]⟩,
        ⟨59515, true, false, [], [83193, 5, 3]⟩,
        ⟨21695, false, false, [24691], [3]⟩,
        ⟨41329, false, false, [24691], []⟩,
        ⟨59516, false, false, [], []⟩,
        ⟨59517, false, false, [], []⟩,
        ⟨41339, false, false, [24691], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 930. -/
def y322TCIndexRaw930 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90221, 1], [24691, 87335], .contexts [
        ⟨59519, false, false, [], []⟩,
        ⟨13, true, false, [], [24691, 87335]⟩
      ]⟩,
    ⟨[24693], [24690], .source 12411⟩,
    ⟨[87335, 1], [24693, 90221], .contexts [
        ⟨59520, true, false, [24690], [1]⟩,
        ⟨8, false, false, [24690, 90221], []⟩,
        ⟨59521, true, false, [], [90221]⟩
      ]⟩,
    ⟨[90219], [90219], .contexts []⟩,
    ⟨[24695], [24691, 727], .source 12412⟩,
    ⟨[90219, 1], [90219, 1], .contexts []⟩,
    ⟨[24695], [24695], .contexts []⟩,
    ⟨[24695], [24695], .contexts []⟩,
    ⟨[24695], [24695], .contexts [
        ⟨13, false, false, [], [24695]⟩,
        ⟨59526, false, false, [], []⟩,
        ⟨59527, false, false, [], []⟩
      ]⟩,
    ⟨[90219, 1], [24695, 87335], .contexts [
        ⟨59525, false, false, [], []⟩,
        ⟨59410, true, false, [], [1]⟩,
        ⟨59410, true, false, [], [1]⟩,
        ⟨59523, true, false, [], [1]⟩,
        ⟨59410, true, false, [], [1]⟩,
        ⟨1, true, false, [90219], [1]⟩,
        ⟨59409, false, false, [], [15, 1]⟩,
        ⟨7, false, false, [90221], []⟩,
        ⟨11, false, false, [90221], []⟩,
        ⟨59518, false, false, [], [15]⟩,
        ⟨59520, false, false, [], [15]⟩,
        ⟨59516, false, false, [], [15]⟩,
        ⟨59517, false, false, [], [15]⟩,
        ⟨59517, false, false, [], [15]⟩,
        ⟨41356, false, false, [24691], []⟩,
        ⟨59524, true, false, [], [87335]⟩,
        ⟨41339, false, false, [24695], []⟩,
        ⟨59528, true, false, [], [87335]⟩
      ]⟩,
    ⟨[24697], [24694], .source 12413⟩,
    ⟨[87335, 1], [24693, 90221], .contexts [
        ⟨59522, false, false, [], []⟩
      ]⟩,
    ⟨[24693, 90221], [24693, 90221], .contexts []⟩,
    ⟨[24697, 90219], [24697, 90219], .contexts []⟩,
    ⟨[24699], [24691, 24697], .source 12414⟩,
    ⟨[24695, 87335], [24695, 87335], .contexts []⟩,
    ⟨[24695, 87335], [24695, 87335], .contexts []⟩,
    ⟨[90219, 1], [24695, 87335], .contexts [
        ⟨59525, false, false, [], []⟩,
        ⟨59529, false, false, [], []⟩,
        ⟨59535, false, false, [], []⟩,
        ⟨59536, false, false, [], []⟩,
        ⟨59536, false, false, [], []⟩
      ]⟩,
    ⟨[24701], [24695, 16379], .source 12415⟩,
    ⟨[24703], [24701, 23217], .source 12416⟩,
    ⟨[24705], [24703, 23223], .source 12417⟩,
    ⟨[90219], [90219], .contexts []⟩,
    ⟨[24705, 88703, 3], [90219], .contexts [
        ⟨59540, false, false, [], [88703, 3]⟩,
        ⟨55283, true, false, [24703], [3]⟩,
        ⟨52098, true, false, [24703], [3]⟩,
        ⟨59539, false, false, [], [88707, 1, 3]⟩,
        ⟨52192, true, false, [24701], [1, 3]⟩,
        ⟨59538, false, false, [], [83503, 3, 1, 3]⟩,
        ⟨21703, true, false, [24695], [3, 1, 3]⟩,
        ⟨41330, true, false, [24695], [1, 3, 1, 3]⟩,
        ⟨59537, true, false, [], [3, 1, 3, 1, 3]⟩,
        ⟨4083, false, false, [90219], []⟩,
        ⟨59541, false, false, [], []⟩
      ]⟩,
    ⟨[90219], [90219], .contexts []⟩,
    ⟨[24707], [24704], .source 12418⟩,
    ⟨[24704], [24704], .contexts []⟩,
    ⟨[88703, 3], [24707, 90219], .contexts [
        ⟨59542, false, false, [24704], []⟩,
        ⟨59543, false, false, [24704], []⟩,
        ⟨59545, true, false, [], [90219]⟩,
        ⟨59545, true, false, [], [90219]⟩,
        ⟨59544, true, false, [], [90219]⟩
      ]⟩,
    ⟨[90219, 3], [24705, 88703], .contexts [
        ⟨59546, true, false, [24706], [3]⟩,
        ⟨20, false, false, [24706, 88703], []⟩,
        ⟨59544, false, true, [], [88703]⟩
      ]⟩,
    ⟨[24695, 87339], [24695, 87339], .contexts []⟩,
    ⟨[24695, 87339], [24695, 87339], .contexts []⟩,
    ⟨[24694], [24694], .contexts []⟩,
    ⟨[87339, 5], [24697, 90219], .contexts [
        ⟨59549, true, false, [24694], [5]⟩,
        ⟨59548, true, false, [24694], [5]⟩,
        ⟨41385, true, false, [], [5]⟩,
        ⟨41357, true, false, [], [1, 5]⟩,
        ⟨59537, true, false, [24694], [5, 1, 5]⟩,
        ⟨1152, false, false, [24694, 90219], []⟩,
        ⟨59541, false, false, [24694], []⟩,
        ⟨59543, false, false, [24694], []⟩,
        ⟨59550, true, false, [], [90219]⟩,
        ⟨59550, true, false, [], [90219]⟩,
        ⟨59530, true, false, [], [90219]⟩
      ]⟩,
    ⟨[90219, 5], [24695, 87339], .contexts [
        ⟨59551, true, false, [24696], [5]⟩,
        ⟨28, false, false, [24696, 87339], []⟩,
        ⟨59530, false, true, [], [87339]⟩
      ]⟩,
    ⟨[24709], [24695, 17527], .source 12419⟩,
    ⟨[24711], [24709, 17539], .source 12420⟩,
    ⟨[84713, 11], [84713, 11], .contexts []⟩,
    ⟨[24713], [24710], .source 12421⟩,
    ⟨[24710], [24710], .contexts []⟩,
    ⟨[84713, 11], [24713, 90219], .contexts [
        ⟨59555, false, false, [], []⟩,
        ⟨59554, false, false, [24710], [84713, 11]⟩,
        ⟨28308, true, false, [24710, 24709], [11]⟩,
        ⟨28155, true, false, [24710, 24709], [11]⟩,
        ⟨59553, false, false, [24710], [84717, 1, 11]⟩,
        ⟨41346, true, false, [24710, 24695], [1, 11]⟩,
        ⟨59537, true, false, [24710], [11, 1, 11]⟩,
        ⟨994, false, false, [24710, 90219], []⟩,
        ⟨59541, false, false, [24710], []⟩,
        ⟨59543, false, false, [24710], []⟩,
        ⟨59557, true, false, [], [90219]⟩,
        ⟨59557, true, false, [], [90219]⟩,
        ⟨59556, true, false, [], [90219]⟩
      ]⟩,
    ⟨[90219, 11], [24711, 84713], .contexts [
        ⟨59558, true, false, [24712], [11]⟩,
        ⟨53, false, false, [24712, 84713], []⟩,
        ⟨59556, false, true, [], [84713]⟩
      ]⟩,
    ⟨[24715], [24695, 2797], .source 12422⟩,
    ⟨[90221], [24699, 90219], .contexts [
        ⟨59532, true, false, [24692], []⟩,
        ⟨59532, true, false, [24692], []⟩,
        ⟨59531, true, false, [24692], []⟩,
        ⟨59529, true, false, [24692, 24694], [1]⟩,
        ⟨8, false, false, [24692, 24694, 90219], []⟩,
        ⟨59530, true, false, [24692], [90219]⟩,
        ⟨59533, false, false, [24692], []⟩,
        ⟨59521, false, true, [], [24697, 90219]⟩,
        ⟨59534, true, false, [], [90219]⟩
      ]⟩,
    ⟨[24699, 90219], [24699, 90219], .contexts []⟩,
    ⟨[90221], [24699, 90219], .contexts [
        ⟨59561, false, false, [], []⟩,
        ⟨59562, false, false, [], []⟩
      ]⟩,
    ⟨[24717], [24693, 24699], .source 12423⟩,
    ⟨[24719], [24715, 24717], .source 12424⟩,
    ⟨[24719, 90215], [24719, 90215], .contexts []⟩,
    ⟨[24719, 90215], [24719, 90215], .contexts []⟩,
    ⟨[24719, 90215, 13], [90219], .contexts [
        ⟨59567, true, false, [], [13]⟩,
        ⟨59566, true, false, [], [13]⟩,
        ⟨59404, true, false, [24719], [13]⟩,
        ⟨59407, true, false, [24719], [1, 13]⟩,
        ⟨59565, false, false, [], [90219, 13, 1, 13]⟩,
        ⟨59564, false, false, [24715], [90219, 13, 1, 13]⟩,
        ⟨59563, true, false, [24715, 24693], [13, 1, 13]⟩,
        ⟨59522, true, false, [24715], [13, 1, 13]⟩,
        ⟨59560, false, false, [], [87335, 1, 13, 1, 13]⟩,
        ⟨41352, true, false, [24695], [1, 13, 1, 13]⟩,
        ⟨59537, true, false, [], [13, 1, 13, 1, 13]⟩,
        ⟨521, false, false, [90219], []⟩,
        ⟨59541, false, false, [], []⟩
      ]⟩,
    ⟨[24721], [24718], .source 12425⟩,
    ⟨[24721], [24718], .contexts [
        ⟨59569, false, false, [], []⟩
      ]⟩,
    ⟨[24718], [24718], .contexts []⟩,
    ⟨[90215, 13], [24721, 90219], .contexts [
        ⟨59568, false, false, [24718], []⟩,
        ⟨59543, false, false, [24718], []⟩,
        ⟨59571, true, false, [], [90219]⟩,
        ⟨59571, true, false, [], [90219]⟩,
        ⟨59570, true, false, [], [90219]⟩
      ]⟩,
    ⟨[90217], [24719, 90215], .contexts [
        ⟨59414, true, false, [], []⟩,
        ⟨59572, true, false, [24720], [13]⟩,
        ⟨59, false, false, [24720, 90215], []⟩,
        ⟨59569, false, true, [], [90215]⟩,
        ⟨59566, false, false, [], []⟩
      ]⟩,
    ⟨[90217], [24719, 90215], .contexts [
        ⟨59573, false, false, [], []⟩,
        ⟨59567, false, false, [], []⟩
      ]⟩,
    ⟨[90219, 13], [24719, 90215], .contexts [
        ⟨59413, false, false, [], []⟩,
        ⟨59574, false, false, [], []⟩,
        ⟨59567, false, false, [], []⟩,
        ⟨59567, false, false, [], []⟩
      ]⟩,
    ⟨[24705, 88703], [24705, 88703], .contexts []⟩,
    ⟨[24705, 88703], [24705, 88703], .contexts []⟩,
    ⟨[90219, 3], [24705, 88703], .contexts [
        ⟨59547, false, false, [], []⟩,
        ⟨59576, false, false, [], []⟩,
        ⟨59577, false, false, [], []⟩,
        ⟨59577, false, false, [], []⟩
      ]⟩,
    ⟨[88701], [23913, 84475], .contexts [
        ⟨55374, false, false, [], []⟩
      ]⟩,
    ⟨[23913, 84475], [23913, 84475], .contexts []⟩,
    ⟨[88701], [23913, 84475], .contexts [
        ⟨59579, false, false, [], []⟩,
        ⟨59580, false, false, [], []⟩
      ]⟩,
    ⟨[24723], [24705, 23913], .source 12426⟩,
    ⟨[24725], [24721, 24723], .source 12427⟩]

/-- Exact literal claimed equations and contextual derivations, block 931. -/
def y322TCIndexRaw931 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90215, 3], [24725, 84475], .contexts [
        ⟨59575, true, false, [24718], [3]⟩,
        ⟨63, false, false, [24718, 90219], []⟩,
        ⟨65, false, false, [24718, 90219], []⟩,
        ⟨59578, false, false, [24718], [13]⟩,
        ⟨52090, false, false, [24718, 24705], []⟩,
        ⟨59581, false, false, [24718, 24705], []⟩,
        ⟨59582, true, false, [24718], [84475]⟩,
        ⟨46340, false, false, [24718, 24723], []⟩,
        ⟨59570, true, false, [], [24723, 84475]⟩,
        ⟨59583, true, false, [], [84475]⟩
      ]⟩,
    ⟨[24727], [24724], .source 12428⟩,
    ⟨[84475, 3], [24727, 90215], .contexts [
        ⟨59584, true, false, [24724], [3]⟩,
        ⟨20, false, false, [24724, 90215], []⟩,
        ⟨59585, true, false, [], [90215]⟩
      ]⟩,
    ⟨[24711, 84713], [24711, 84713], .contexts []⟩,
    ⟨[24711, 84713], [24711, 84713], .contexts []⟩,
    ⟨[24729], [24721, 24711], .source 12429⟩,
    ⟨[24731], [24728], .source 12430⟩,
    ⟨[84713, 13], [17543, 84709], .contexts [
        ⟨28321, false, false, [], []⟩,
        ⟨28328, false, false, [], []⟩,
        ⟨28311, false, false, [], []⟩,
        ⟨28311, false, false, [], []⟩
      ]⟩,
    ⟨[24733], [17545, 24731], .source 12431⟩,
    ⟨[24735], [24732], .source 12432⟩,
    ⟨[90213], [24735, 84709], .contexts [
        ⟨59592, false, false, [24732], [90213]⟩,
        ⟨28316, false, false, [24732], [24731, 90213]⟩,
        ⟨59590, false, false, [24732, 17542], [90213]⟩,
        ⟨59, true, false, [24732, 17542, 24728, 90213], []⟩,
        ⟨59401, true, false, [24732, 17542, 24728], [13, 13]⟩,
        ⟨59575, true, false, [24732, 17542, 24728, 24718], [11, 13, 13]⟩,
        ⟨931, false, false, [24732, 17542, 24728, 24718, 90219], [13]⟩,
        ⟨54, false, false, [24732, 17542, 24728, 24718, 90219], [13]⟩,
        ⟨59559, false, false, [24732, 17542, 24728, 24718], [13]⟩,
        ⟨59587, false, false, [24732, 17542, 24728, 24718], [13]⟩,
        ⟨59588, false, false, [24732, 17542, 24728, 24718], [13]⟩,
        ⟨59588, false, false, [24732, 17542, 24728, 24718], [13]⟩,
        ⟨28315, false, false, [24732, 17542, 24728, 24718, 24711], [13]⟩,
        ⟨59570, true, false, [24732, 17542, 24728], [24711, 84713, 13]⟩,
        ⟨59589, true, false, [24732, 17542, 24728], [84713, 13]⟩,
        ⟨59591, false, false, [24732, 17542], []⟩,
        ⟨59593, true, false, [], [84709]⟩
      ]⟩,
    ⟨[24733], [24734], .contexts [
        ⟨59593, true, true, [], []⟩
      ]⟩,
    ⟨[24733], [24734], .contexts [
        ⟨59595, false, false, [], []⟩
      ]⟩,
    ⟨[24734], [24734], .contexts []⟩,
    ⟨[84709, 9], [24733, 90211], .contexts [
        ⟨59594, true, false, [24734], [9]⟩,
        ⟨59397, false, false, [24734], []⟩,
        ⟨59416, false, false, [24734], []⟩,
        ⟨59597, true, false, [], [90211]⟩,
        ⟨59597, true, false, [], [90211]⟩,
        ⟨59596, true, false, [], [90211]⟩
      ]⟩,
    ⟨[90213], [24735, 84709], .contexts [
        ⟨59594, false, false, [], []⟩
      ]⟩,
    ⟨[24735, 84707], [24735, 84707], .contexts []⟩,
    ⟨[90215], [24735, 84707], .contexts [
        ⟨59596, false, false, [24732], [90215]⟩,
        ⟨13, false, false, [24732, 24734], [90215]⟩,
        ⟨59415, true, false, [24732, 24734], []⟩,
        ⟨59399, true, false, [24732, 24734], []⟩,
        ⟨59599, false, false, [24732, 24734], [11]⟩,
        ⟨28140, false, false, [24732], []⟩,
        ⟨59600, false, false, [24732, 24734], []⟩,
        ⟨59593, true, false, [], [84707]⟩
      ]⟩,
    ⟨[24719, 90215], [24719, 24735, 84707], .contexts [
        ⟨59601, false, false, [24719], []⟩
      ]⟩,
    ⟨[24737], [24719, 24735], .source 12433⟩,
    ⟨[24739], [24733, 24721], .source 12434⟩,
    ⟨[84707, 13], [24739, 90219], .contexts [
        ⟨59601, true, false, [24734], [13]⟩,
        ⟨59572, false, false, [24734], []⟩,
        ⟨59595, true, false, [], [24721, 90219]⟩,
        ⟨59604, true, false, [], [90219]⟩
      ]⟩,
    ⟨[24741], [24733, 24725], .source 12435⟩,
    ⟨[84707, 3], [24741, 84475], .contexts [
        ⟨59601, true, false, [24734], [3]⟩,
        ⟨59584, false, false, [24734], []⟩,
        ⟨59595, true, false, [], [24725, 84475]⟩,
        ⟨59606, true, false, [], [84475]⟩
      ]⟩,
    ⟨[24741, 84475], [24741, 84475], .contexts []⟩,
    ⟨[24741, 84475], [24741, 84475], .contexts []⟩,
    ⟨[84707, 3], [24741, 84475], .contexts [
        ⟨59607, false, false, [], []⟩,
        ⟨59608, false, false, [], []⟩,
        ⟨59609, false, false, [], []⟩,
        ⟨59609, false, false, [], []⟩
      ]⟩,
    ⟨[84709, 3], [84709, 3], .contexts []⟩,
    ⟨[84709, 3], [24741, 84477], .contexts [
        ⟨59611, false, false, [], []⟩,
        ⟨28143, true, false, [], [3]⟩,
        ⟨28143, true, false, [], [3]⟩,
        ⟨28160, true, false, [], [3]⟩,
        ⟨28138, true, false, [], [3]⟩,
        ⟨215, false, false, [84707], []⟩,
        ⟨216, false, false, [84707], []⟩,
        ⟨59610, false, false, [], [11]⟩,
        ⟨26901, false, false, [24741], []⟩,
        ⟨13, true, false, [], [24741, 84477]⟩
      ]⟩,
    ⟨[24743], [24740], .source 12436⟩,
    ⟨[24741, 84473], [24741, 84473], .contexts []⟩,
    ⟨[84473, 3], [84473, 3], .contexts []⟩,
    ⟨[84705], [84705], .contexts []⟩,
    ⟨[24740], [24740], .contexts []⟩,
    ⟨[84473, 3], [24743, 84705], .contexts [
        ⟨59615, false, false, [], []⟩,
        ⟨59614, true, false, [24740], [3]⟩,
        ⟨26899, true, false, [], [3]⟩,
        ⟨59610, true, false, [24740], [9, 3]⟩,
        ⟨573, false, false, [24740, 84707], []⟩,
        ⟨47, false, false, [24740, 84707], []⟩,
        ⟨28336, false, false, [24740], []⟩,
        ⟨59616, false, false, [24740], []⟩,
        ⟨59617, true, false, [], [84705]⟩,
        ⟨59617, true, false, [], [84705]⟩,
        ⟨59613, true, false, [], [84705]⟩
      ]⟩,
    ⟨[24741], [24742], .contexts [
        ⟨59613, true, true, [], []⟩
      ]⟩,
    ⟨[17543, 84709, 9], [17543, 24733, 90211], .contexts [
        ⟨59598, false, false, [17543], []⟩
      ]⟩,
    ⟨[17543, 24733, 90211], [17543, 24733, 90211], .contexts []⟩,
    ⟨[17543, 24733, 90211], [17543, 24733, 90211], .contexts []⟩,
    ⟨[24745], [17543, 24733], .source 12437⟩,
    ⟨[17543, 24733, 90211], [24745, 90211], .contexts [
        ⟨59623, true, false, [], [90211]⟩
      ]⟩,
    ⟨[84709, 9], [24733, 90211], .contexts [
        ⟨59598, false, false, [], []⟩
      ]⟩,
    ⟨[24733, 90211], [24733, 90211], .contexts []⟩,
    ⟨[84709, 9], [24733, 90211], .contexts [
        ⟨59625, false, false, [], []⟩,
        ⟨59626, false, false, [], []⟩,
        ⟨59626, false, false, [], []⟩
      ]⟩,
    ⟨[90209, 9], [90209, 9], .contexts []⟩,
    ⟨[90209], [90209], .contexts []⟩,
    ⟨[24747], [24744], .source 12438⟩,
    ⟨[24749], [24747, 24733], .source 12439⟩,
    ⟨[90209, 9], [24749, 90209], .contexts [
        ⟨59628, false, false, [], []⟩,
        ⟨59393, true, false, [], [9]⟩,
        ⟨59624, true, false, [24744], [1, 9]⟩,
        ⟨59622, true, false, [24744], [1, 9]⟩,
        ⟨59621, true, false, [24744], [1, 9]⟩,
        ⟨59620, true, false, [24744], [1, 9]⟩,
        ⟨28329, true, false, [24744], [9, 1, 9]⟩,
        ⟨582, false, false, [24744, 84709], []⟩,
        ⟨453, false, false, [24744, 84709], []⟩,
        ⟨59627, false, false, [24744], [1]⟩,
        ⟨59393, false, false, [24744, 24733], []⟩,
        ⟨59629, false, false, [24744, 24733], []⟩,
        ⟨59630, true, false, [], [24733, 90209]⟩,
        ⟨59631, true, false, [], [90209]⟩
      ]⟩,
    ⟨[24743, 84705], [24743, 84705], .contexts []⟩,
    ⟨[24743, 84705], [24743, 84705], .contexts []⟩,
    ⟨[84703, 3], [84703, 3], .contexts []⟩,
    ⟨[87783], [87783], .contexts []⟩,
    ⟨[24751], [24741, 21729], .source 12440⟩,
    ⟨[84703, 3], [24751, 87783], .contexts [
        ⟨59635, false, false, [], []⟩,
        ⟨28132, true, false, [], [3]⟩,
        ⟨59634, true, false, [24742], [1, 3]⟩,
        ⟨59634, true, false, [24742], [1, 3]⟩,
        ⟨59633, true, false, [24742], [1, 3]⟩,
        ⟨59618, true, false, [24742], [1, 3]⟩,
        ⟨59615, true, false, [24742], [1, 3]⟩,
        ⟨1634, false, false, [24742, 84473], []⟩,
        ⟨132, false, false, [24742, 84473], []⟩,
        ⟨46391, false, false, [24742], [3, 1]⟩,
        ⟨53504, false, false, [24742], [1]⟩,
        ⟨53505, false, false, [24742], [1]⟩,
        ⟨53506, false, false, [24742], [1]⟩,
        ⟨53506, false, false, [24742], [1]⟩,
        ⟨46024, false, false, [24742, 21729], []⟩,
        ⟨59636, false, false, [24742, 21729], []⟩,
        ⟨59619, true, false, [], [21729, 87783]⟩,
        ⟨59637, true, false, [], [87783]⟩
      ]⟩,
    ⟨[24753], [24750], .source 12441⟩,
    ⟨[87783, 3], [24753, 84703], .contexts [
        ⟨59638, true, false, [24750], [3]⟩,
        ⟨20, false, false, [24750, 84703], []⟩,
        ⟨59639, true, false, [], [84703]⟩
      ]⟩,
    ⟨[24749, 90209], [24749, 90209], .contexts []⟩,
    ⟨[24749, 90209], [24749, 90209], .contexts []⟩,
    ⟨[90207, 9], [90207, 9], .contexts []⟩,
    ⟨[90207], [90207], .contexts []⟩,
    ⟨[24755], [24748], .source 12442⟩,
    ⟨[24748], [24748], .contexts []⟩,
    ⟨[90207, 9], [24755, 90207], .contexts [
        ⟨59643, false, false, [], []⟩,
        ⟨59389, true, false, [], [9]⟩,
        ⟨59642, true, false, [24748], [5, 9]⟩,
        ⟨59642, true, false, [24748], [5, 9]⟩,
        ⟨59641, true, false, [24748], [5, 9]⟩,
        ⟨59632, true, false, [24748], [5, 9]⟩,
        ⟨59628, true, false, [24748], [5, 9]⟩,
        ⟨598, false, false, [24748, 90209], []⟩,
        ⟨29, false, false, [24748, 90209], []⟩,
        ⟨59419, false, false, [24748], []⟩,
        ⟨59420, false, false, [24748], []⟩,
        ⟨59388, false, false, [24748], []⟩,
        ⟨59388, false, false, [24748], []⟩,
        ⟨59644, false, false, [24748], []⟩,
        ⟨59646, true, false, [], [90207]⟩,
        ⟨59646, true, false, [], [90207]⟩,
        ⟨59645, true, false, [], [90207]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 932. -/
def y322TCIndexRaw932 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[24751, 87783], [24751, 87783], .contexts []⟩,
    ⟨[24751, 87783], [24751, 87783], .contexts []⟩,
    ⟨[24757], [17545, 24751], .source 12443⟩,
    ⟨[87783, 9], [87783, 9], .contexts []⟩,
    ⟨[24759], [24753, 24757], .source 12444⟩,
    ⟨[87783, 9], [24759, 87783], .contexts [
        ⟨59651, false, false, [], []⟩,
        ⟨59649, true, false, [24750], [9]⟩,
        ⟨59649, true, false, [24750], [9]⟩,
        ⟨59648, true, false, [24750], [9]⟩,
        ⟨59638, true, false, [24750], [9]⟩,
        ⟨59635, true, false, [24750], [9]⟩,
        ⟨669, false, false, [24750, 84703], []⟩,
        ⟨670, false, false, [24750, 84703], []⟩,
        ⟨28342, false, false, [24750], [3]⟩,
        ⟨59638, false, false, [24750, 17545], []⟩,
        ⟨59650, true, false, [24750], [87783]⟩,
        ⟨59636, false, false, [24750, 24757], []⟩,
        ⟨59639, true, false, [], [24757, 87783]⟩,
        ⟨59652, true, false, [], [87783]⟩
      ]⟩,
    ⟨[24755, 90207], [24755, 90207], .contexts []⟩,
    ⟨[90207, 3], [90205], .contexts [
        ⟨59422, false, false, [], []⟩,
        ⟨59423, false, false, [], []⟩,
        ⟨59384, false, false, [], []⟩,
        ⟨59384, false, false, [], []⟩
      ]⟩,
    ⟨[90207, 2], [90207, 3], .contexts [
        ⟨21, false, false, [90207], []⟩
      ]⟩,
    ⟨[90205], [90205], .contexts []⟩,
    ⟨[24754], [24754], .contexts []⟩,
    ⟨[24759, 87783], [24759, 87783], .contexts []⟩,
    ⟨[24759, 87783], [24759, 87783], .contexts []⟩,
    ⟨[87783, 9], [24759, 87783], .contexts [
        ⟨59651, false, false, [], []⟩,
        ⟨59653, false, false, [], []⟩,
        ⟨59659, false, false, [], []⟩,
        ⟨59660, false, false, [], []⟩,
        ⟨59660, false, false, [], []⟩
      ]⟩,
    ⟨[24761], [24759, 23465], .source 12445⟩,
    ⟨[88955, 9], [88955, 9], .contexts []⟩,
    ⟨[24763], [24760], .source 12446⟩,
    ⟨[24765], [24763, 23465], .source 12447⟩,
    ⟨[88955, 9], [24765, 88955], .contexts [
        ⟨59663, false, false, [], []⟩,
        ⟨59662, false, false, [24760], [88955, 9]⟩,
        ⟨53548, true, false, [24760, 24759], [9]⟩,
        ⟨59661, true, false, [24760], [7, 9]⟩,
        ⟨48293, false, false, [24760, 87783], []⟩,
        ⟨39, false, false, [24760, 87783], []⟩,
        ⟨53562, false, false, [24760], []⟩,
        ⟨53545, false, false, [24760, 23465], []⟩,
        ⟨59664, true, false, [], [23465, 88955]⟩,
        ⟨59665, true, false, [], [88955]⟩
      ]⟩,
    ⟨[87781, 9], [87781, 9], .contexts []⟩,
    ⟨[24767], [24758], .source 12448⟩,
    ⟨[24758], [24758], .contexts []⟩,
    ⟨[87781, 9], [24767, 87781], .contexts [
        ⟨59667, false, false, [], []⟩,
        ⟨46020, true, false, [], [9]⟩,
        ⟨59661, true, false, [24758], [15, 9]⟩,
        ⟨935, false, false, [24758, 87783], []⟩,
        ⟨53566, false, false, [24758], []⟩,
        ⟨53565, false, false, [24758], []⟩,
        ⟨53568, false, false, [24758], []⟩,
        ⟨59669, true, false, [], [87781]⟩,
        ⟨59669, true, false, [], [87781]⟩,
        ⟨59668, true, false, [], [87781]⟩
      ]⟩,
    ⟨[24765, 88955], [24765, 88955], .contexts []⟩,
    ⟨[24765, 88955], [24765, 88955], .contexts []⟩,
    ⟨[88955, 15], [88953], .contexts [
        ⟨53283, false, false, [], []⟩,
        ⟨53284, false, false, [], []⟩,
        ⟨53235, false, false, [], []⟩,
        ⟨53235, false, false, [], []⟩
      ]⟩,
    ⟨[88953, 9], [88953, 9], .contexts []⟩,
    ⟨[88953], [88953], .contexts []⟩,
    ⟨[24769], [24764], .source 12449⟩,
    ⟨[24764], [24764], .contexts []⟩,
    ⟨[24769], [24764], .contexts [
        ⟨59676, false, false, [], []⟩,
        ⟨59677, false, false, [], []⟩,
        ⟨59677, false, false, [], []⟩
      ]⟩,
    ⟨[88953, 9], [24769, 88953], .contexts [
        ⟨59674, false, false, [], []⟩,
        ⟨53236, true, false, [], [9]⟩,
        ⟨59672, true, false, [24764], [15, 9]⟩,
        ⟨59672, true, false, [24764], [15, 9]⟩,
        ⟨59671, true, false, [24764], [15, 9]⟩,
        ⟨59666, true, false, [24764], [15, 9]⟩,
        ⟨59663, true, false, [24764], [15, 9]⟩,
        ⟨935, false, false, [24764, 88955], []⟩,
        ⟨10, false, false, [24764, 88955], []⟩,
        ⟨59673, false, false, [24764], []⟩,
        ⟨59675, false, false, [24764], []⟩,
        ⟨59678, true, false, [], [88953]⟩
      ]⟩,
    ⟨[24767, 87781], [24767, 87781], .contexts []⟩,
    ⟨[87781, 13], [87779], .contexts [
        ⟨46079, false, false, [], []⟩,
        ⟨46080, false, false, [], []⟩,
        ⟨46015, false, false, [], []⟩,
        ⟨46015, false, false, [], []⟩
      ]⟩,
    ⟨[87781, 12], [87781, 13], .contexts [
        ⟨64, false, false, [87781], []⟩
      ]⟩,
    ⟨[87779], [87779], .contexts []⟩,
    ⟨[24766], [24766], .contexts []⟩,
    ⟨[24769, 88953], [24769, 88953], .contexts []⟩,
    ⟨[24768], [24768], .contexts []⟩,
    ⟨[88951, 9], [24765, 88951], .contexts [
        ⟨53232, true, false, [], [9]⟩,
        ⟨59685, true, false, [24768], [13, 9]⟩,
        ⟨59685, true, false, [24768], [13, 9]⟩,
        ⟨59679, true, false, [24768], [13, 9]⟩,
        ⟨59674, true, false, [24768], [13, 9]⟩,
        ⟨511, false, false, [24768, 88953], []⟩,
        ⟨53588, false, false, [24768], []⟩,
        ⟨53587, false, false, [24768], []⟩,
        ⟨53590, false, false, [24768], []⟩,
        ⟨59686, true, false, [], [88951]⟩,
        ⟨59686, true, false, [], [88951]⟩,
        ⟨59676, false, true, [], [88951]⟩
      ]⟩,
    ⟨[90223], [85341, 5], .source 45176⟩,
    ⟨[85341, 5], [90223], .contexts [
        ⟨59688, true, false, [], []⟩
      ]⟩,
    ⟨[90223, 5], [85341], .contexts [
        ⟨59689, true, false, [], [5]⟩,
        ⟨28, false, false, [85341], []⟩,
        ⟨31561, false, false, [], []⟩
      ]⟩,
    ⟨[90223], [90223], .contexts []⟩,
    ⟨[90223], [90223], .contexts []⟩,
    ⟨[85341, 5], [90223], .contexts [
        ⟨59689, false, false, [], []⟩,
        ⟨59691, false, false, [], []⟩,
        ⟨59692, false, false, [], []⟩,
        ⟨59692, false, false, [], []⟩
      ]⟩,
    ⟨[18123, 90223], [18123, 90223], .contexts []⟩,
    ⟨[18123, 90223], [18123, 90223], .contexts []⟩,
    ⟨[90223], [90223], .contexts []⟩,
    ⟨[90223, 1], [18123, 90223], .contexts [
        ⟨59693, true, false, [], [1]⟩,
        ⟨161, false, false, [85341], []⟩,
        ⟨162, false, false, [85341], []⟩,
        ⟨31567, false, false, [], [5]⟩,
        ⟨31571, false, false, [], [5]⟩,
        ⟨31565, false, false, [], [5]⟩,
        ⟨31566, false, false, [], [5]⟩,
        ⟨31566, false, false, [], [5]⟩,
        ⟨59689, false, false, [18123], []⟩,
        ⟨59694, false, false, [], []⟩,
        ⟨59695, false, false, [], []⟩,
        ⟨59696, false, false, [18123], []⟩,
        ⟨31570, true, false, [], [90223]⟩
      ]⟩,
    ⟨[13035, 90223], [13035, 90223], .contexts []⟩,
    ⟨[13035, 90223], [13035, 90223], .contexts []⟩,
    ⟨[90223, 9], [90223, 9], .contexts []⟩,
    ⟨[90223, 13], [85339], .contexts [
        ⟨59693, true, false, [], [13]⟩,
        ⟨179, false, false, [85341], []⟩,
        ⟨180, false, false, [85341], []⟩,
        ⟨31559, false, false, [], [5]⟩,
        ⟨31515, false, false, [], [5]⟩,
        ⟨31516, false, false, [], [5]⟩,
        ⟨31516, false, false, [], [5]⟩,
        ⟨31542, false, false, [], []⟩,
        ⟨31543, false, false, [], []⟩,
        ⟨31544, false, false, [], []⟩,
        ⟨31544, false, false, [], []⟩,
        ⟨31550, false, false, [], []⟩,
        ⟨672, true, false, [], [85339]⟩
      ]⟩,
    ⟨[85339, 13], [90223], .contexts [
        ⟨59701, true, false, [], [13]⟩,
        ⟨59, false, false, [90223], []⟩,
        ⟨59692, false, false, [], []⟩
      ]⟩,
    ⟨[90225], [89441, 5], .source 45177⟩,
    ⟨[89441, 5], [90225], .contexts [
        ⟨59703, true, false, [], []⟩
      ]⟩,
    ⟨[90225, 5], [89441], .contexts [
        ⟨59704, true, false, [], [5]⟩,
        ⟨28, false, false, [89441], []⟩,
        ⟨56094, false, false, [], []⟩
      ]⟩,
    ⟨[90225], [90225], .contexts []⟩,
    ⟨[90225], [90225], .contexts []⟩,
    ⟨[89441, 5], [90225], .contexts [
        ⟨59704, false, false, [], []⟩,
        ⟨59706, false, false, [], []⟩,
        ⟨59707, false, false, [], []⟩,
        ⟨59707, false, false, [], []⟩
      ]⟩,
    ⟨[24775], [16219, 16205], .source 12452⟩,
    ⟨[24777], [24775, 11451], .source 12453⟩,
    ⟨[24779], [24777, 16029], .source 12454⟩]

/-- Exact literal claimed equations and contextual derivations, block 933. -/
def y322TCIndexRaw933 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90225, 3], [24779, 83197], .contexts [
        ⟨59708, true, false, [], [3]⟩,
        ⟨166, false, false, [89441], []⟩,
        ⟨169, false, false, [89441], []⟩,
        ⟨56098, false, false, [], [5, 3, 5]⟩,
        ⟨56099, false, false, [], [5, 3, 5]⟩,
        ⟨56096, false, false, [], [5, 3, 5]⟩,
        ⟨56097, false, false, [], [5, 3, 5]⟩,
        ⟨56097, false, false, [], [5, 3, 5]⟩,
        ⟨20962, false, false, [16219], [3, 5]⟩,
        ⟨59709, true, false, [], [82803, 3, 5]⟩,
        ⟨16806, false, false, [24775], [5]⟩,
        ⟨59710, true, false, [], [79379, 5]⟩,
        ⟨19829, false, false, [24777], []⟩,
        ⟨59711, true, false, [], [83197]⟩,
        ⟨19836, false, false, [24779], []⟩
      ]⟩,
    ⟨[90225, 3], [24779, 83197], .contexts [
        ⟨59712, false, false, [], []⟩,
        ⟨13, true, false, [], [24779, 83197]⟩
      ]⟩,
    ⟨[24781], [24778], .source 12455⟩,
    ⟨[83197, 3], [24781, 90225], .contexts [
        ⟨59713, true, false, [24778], [3]⟩,
        ⟨20, false, false, [24778, 90225], []⟩,
        ⟨59714, true, false, [], [90225]⟩
      ]⟩,
    ⟨[24783], [18321, 22873], .source 12456⟩,
    ⟨[90225, 11], [90225, 11], .contexts []⟩,
    ⟨[90225, 11], [24783, 85945], .contexts [
        ⟨59717, false, false, [], []⟩,
        ⟨59708, true, false, [], [11]⟩,
        ⟨174, false, false, [89441], []⟩,
        ⟨175, false, false, [89441], []⟩,
        ⟨56103, false, false, [], [5]⟩,
        ⟨56104, false, false, [], [5]⟩,
        ⟨56101, false, false, [], [5]⟩,
        ⟨56102, false, false, [], [5]⟩,
        ⟨56102, false, false, [], [5]⟩,
        ⟨50731, false, false, [18321], []⟩,
        ⟨59716, true, false, [], [85945]⟩,
        ⟨34502, false, false, [24783], []⟩,
        ⟨13, true, false, [], [24783, 85945]⟩
      ]⟩,
    ⟨[24785], [24782], .source 12457⟩,
    ⟨[90225, 13], [83373], .contexts [
        ⟨59708, true, false, [], [13]⟩,
        ⟨179, false, false, [89441], []⟩,
        ⟨180, false, false, [89441], []⟩,
        ⟨56091, false, false, [], [5]⟩,
        ⟨21071, false, false, [], [5]⟩,
        ⟨21072, false, false, [], [5]⟩,
        ⟨21072, false, false, [], [5]⟩,
        ⟨21069, false, false, [], []⟩,
        ⟨21344, false, false, [], []⟩,
        ⟨21068, false, false, [], []⟩,
        ⟨21068, false, false, [], []⟩,
        ⟨32845, false, false, [], []⟩,
        ⟨32846, false, false, [], []⟩
      ]⟩,
    ⟨[83373, 13], [90225], .contexts [
        ⟨59720, true, false, [], [13]⟩,
        ⟨59, false, false, [90225], []⟩,
        ⟨59707, false, false, [], []⟩
      ]⟩,
    ⟨[24095, 90225], [24095, 90225], .contexts []⟩,
    ⟨[90225], [90225], .contexts []⟩,
    ⟨[24783, 85945], [24783, 85945], .contexts []⟩,
    ⟨[24783, 85945], [24783, 85945], .contexts []⟩,
    ⟨[24787], [24783, 18661], .source 12458⟩,
    ⟨[24789], [24787, 19873], .source 12459⟩,
    ⟨[24791], [24788], .source 12460⟩,
    ⟨[24788], [24788], .contexts []⟩,
    ⟨[86911, 1], [24791, 90225], .contexts [
        ⟨59727, false, false, [24788], [86911, 1]⟩,
        ⟨40377, true, false, [24788, 24787], [1]⟩,
        ⟨59726, false, false, [24788], [85941, 11, 1]⟩,
        ⟨35853, true, false, [24788, 24783], [11, 1]⟩,
        ⟨34250, true, false, [24788, 24783], [11, 1]⟩,
        ⟨59725, true, false, [24788], [1, 11, 1]⟩,
        ⟨59725, true, false, [24788], [1, 11, 1]⟩,
        ⟨59724, true, false, [24788], [1, 11, 1]⟩,
        ⟨59718, true, false, [24788], [1, 11, 1]⟩,
        ⟨59717, true, false, [24788], [1, 11, 1]⟩,
        ⟨628, false, false, [24788, 90225], []⟩,
        ⟨59723, false, false, [24788], []⟩,
        ⟨59729, true, false, [], [90225]⟩,
        ⟨59729, true, false, [], [90225]⟩,
        ⟨59728, true, false, [], [90225]⟩
      ]⟩,
    ⟨[90225, 1], [24789, 86911], .contexts [
        ⟨59730, true, false, [24790], [1]⟩,
        ⟨8, false, false, [24790, 86911], []⟩,
        ⟨59728, false, true, [], [86911]⟩
      ]⟩,
    ⟨[90227], [86909, 11], .source 45178⟩,
    ⟨[86909, 11], [90227], .contexts [
        ⟨59732, true, false, [], []⟩
      ]⟩,
    ⟨[90227, 11], [86909], .contexts [
        ⟨59733, true, false, [], [11]⟩,
        ⟨53, false, false, [86909], []⟩,
        ⟨39384, false, false, [], []⟩
      ]⟩,
    ⟨[90227], [90227], .contexts []⟩,
    ⟨[90227], [90227], .contexts []⟩,
    ⟨[86909, 11], [90227], .contexts [
        ⟨59733, false, false, [], []⟩,
        ⟨59735, false, false, [], []⟩,
        ⟨59736, false, false, [], []⟩,
        ⟨59736, false, false, [], []⟩
      ]⟩,
    ⟨[86909, 9], [86911], .contexts [
        ⟨39383, false, false, [], []⟩
      ]⟩,
    ⟨[86913], [19871, 85941], .contexts [
        ⟨40375, false, false, [], []⟩
      ]⟩,
    ⟨[19871, 85941], [19871, 85941], .contexts []⟩,
    ⟨[19871, 88475], [19871, 88475], .contexts []⟩,
    ⟨[19871, 88475], [19871, 88475], .contexts []⟩,
    ⟨[90227, 9], [90227, 9], .contexts []⟩,
    ⟨[90227, 9], [19871, 88475], .contexts [
        ⟨59743, false, false, [], []⟩,
        ⟨59737, true, false, [], [9]⟩,
        ⟨221, false, false, [86909], []⟩,
        ⟨224, false, false, [86909], []⟩,
        ⟨59738, false, false, [], [11, 9, 11]⟩,
        ⟨39411, false, false, [], [11, 9, 11]⟩,
        ⟨39388, false, false, [], [11, 9, 11]⟩,
        ⟨39388, false, false, [], [11, 9, 11]⟩,
        ⟨39387, false, false, [], [9, 11]⟩,
        ⟨59739, false, false, [], [9, 11]⟩,
        ⟨59740, false, false, [], [9, 11]⟩,
        ⟨59740, false, false, [], [9, 11]⟩,
        ⟨59740, false, false, [], [9, 11]⟩,
        ⟨50743, false, false, [19871], [11]⟩,
        ⟨50764, false, false, [19871], []⟩,
        ⟨59741, false, false, [], []⟩,
        ⟨59742, false, false, [], []⟩,
        ⟨50779, false, false, [19871], []⟩
      ]⟩,
    ⟨[90227, 9], [19871, 88475], .contexts [
        ⟨59744, false, false, [], []⟩,
        ⟨13, true, false, [], [19871, 88475]⟩
      ]⟩,
    ⟨[19923, 90227], [19923, 90227], .contexts []⟩,
    ⟨[19923, 90227], [19923, 90227], .contexts []⟩,
    ⟨[90227, 15], [90227, 15], .contexts []⟩,
    ⟨[90227], [90227], .contexts []⟩,
    ⟨[19923], [19923], .contexts [
        ⟨13, false, false, [], [19923]⟩
      ]⟩,
    ⟨[90227, 15], [19923, 90227], .contexts [
        ⟨59748, false, false, [], []⟩,
        ⟨59737, true, false, [], [15]⟩,
        ⟨231, false, false, [86909], []⟩,
        ⟨232, false, false, [86909], []⟩,
        ⟨40506, false, false, [], [11]⟩,
        ⟨59733, false, false, [19923], []⟩,
        ⟨59746, false, false, [], []⟩,
        ⟨59747, false, false, [], []⟩,
        ⟨59749, false, false, [19923], []⟩,
        ⟨59750, true, false, [], [90227]⟩
      ]⟩,
    ⟨[90229], [90227, 1], .source 45179⟩,
    ⟨[90227, 1], [90229], .contexts [
        ⟨59752, true, false, [], []⟩
      ]⟩,
    ⟨[90229, 1], [90227], .contexts [
        ⟨59753, true, false, [], [1]⟩,
        ⟨8, false, false, [90227], []⟩,
        ⟨59736, false, false, [], []⟩
      ]⟩,
    ⟨[90229], [90229], .contexts []⟩,
    ⟨[90229], [90229], .contexts []⟩,
    ⟨[90227, 1], [90229], .contexts [
        ⟨59753, false, false, [], []⟩,
        ⟨59755, false, false, [], []⟩,
        ⟨59756, false, false, [], []⟩,
        ⟨59756, false, false, [], []⟩
      ]⟩,
    ⟨[90227, 11], [86909], .contexts [
        ⟨59734, false, false, [], []⟩
      ]⟩,
    ⟨[90229, 11], [86907], .contexts [
        ⟨59757, true, false, [], [11]⟩,
        ⟨110, false, false, [90227], []⟩,
        ⟨111, false, false, [90227], []⟩,
        ⟨59758, false, false, [], [1]⟩,
        ⟨39414, false, false, [], [1]⟩,
        ⟨39384, false, false, [], [1]⟩,
        ⟨39384, false, false, [], [1]⟩,
        ⟨39415, false, false, [], []⟩,
        ⟨39416, false, false, [], []⟩,
        ⟨39380, false, false, [], []⟩,
        ⟨39380, false, false, [], []⟩,
        ⟨40508, false, false, [], []⟩,
        ⟨672, true, false, [], [86907]⟩
      ]⟩,
    ⟨[86907, 11], [90229], .contexts [
        ⟨59759, true, false, [], [11]⟩,
        ⟨53, false, false, [90229], []⟩,
        ⟨59756, false, false, [], []⟩
      ]⟩,
    ⟨[19923, 90229], [19923, 90229], .contexts []⟩,
    ⟨[19923, 90229], [19923, 90229], .contexts []⟩,
    ⟨[90229], [90229], .contexts []⟩,
    ⟨[90229, 15], [19923, 90229], .contexts [
        ⟨59757, true, false, [], [15]⟩,
        ⟨121, false, false, [90227], []⟩,
        ⟨122, false, false, [90227], []⟩,
        ⟨59748, false, false, [], [1]⟩,
        ⟨59751, false, false, [], [1]⟩,
        ⟨59746, false, false, [], [1]⟩,
        ⟨59747, false, false, [], [1]⟩,
        ⟨59747, false, false, [], [1]⟩,
        ⟨59753, false, false, [19923], []⟩,
        ⟨59761, false, false, [], []⟩,
        ⟨59762, false, false, [], []⟩,
        ⟨59763, false, false, [19923], []⟩,
        ⟨59750, true, false, [], [90229]⟩
      ]⟩,
    ⟨[90231], [90229, 13], .source 45180⟩,
    ⟨[90229, 13], [90231], .contexts [
        ⟨59765, true, false, [], []⟩
      ]⟩,
    ⟨[90231, 13], [90229], .contexts [
        ⟨59766, true, false, [], [13]⟩,
        ⟨59, false, false, [90229], []⟩,
        ⟨59756, false, false, [], []⟩
      ]⟩,
    ⟨[90233], [90231, 15], .source 45181⟩,
    ⟨[90231, 15], [90233], .contexts [
        ⟨59768, true, false, [], []⟩
      ]⟩,
    ⟨[90231], [90231], .contexts []⟩,
    ⟨[90233, 15], [90231], .contexts [
        ⟨59769, true, false, [], [15]⟩,
        ⟨1, false, false, [90231], []⟩,
        ⟨59770, false, false, [], []⟩
      ]⟩,
    ⟨[90233], [90233], .contexts []⟩,
    ⟨[90233], [90233], .contexts []⟩,
    ⟨[90231, 13], [90229], .contexts [
        ⟨59767, false, false, [], []⟩
      ]⟩,
    ⟨[19923, 90233], [19923, 90233], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 934. -/
def y322TCIndexRaw934 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[19923, 90233], [19923, 90233], .contexts []⟩,
    ⟨[90233, 13], [90233, 13], .contexts []⟩,
    ⟨[90233], [90233], .contexts []⟩,
    ⟨[90233, 13], [19923, 90233], .contexts [
        ⟨59777, false, false, [], []⟩,
        ⟨59773, true, false, [], [13]⟩,
        ⟨59773, true, false, [], [13]⟩,
        ⟨59772, true, false, [], [13]⟩,
        ⟨59769, true, false, [], [13]⟩,
        ⟨259, false, false, [90231], []⟩,
        ⟨262, false, false, [90231], []⟩,
        ⟨59774, false, false, [], [15, 13, 15]⟩,
        ⟨59755, false, false, [], [15, 13, 15]⟩,
        ⟨59756, false, false, [], [15, 13, 15]⟩,
        ⟨59756, false, false, [], [15, 13, 15]⟩,
        ⟨59764, false, false, [], [13, 15]⟩,
        ⟨59761, false, false, [], [13, 15]⟩,
        ⟨59762, false, false, [], [13, 15]⟩,
        ⟨59762, false, false, [], [13, 15]⟩,
        ⟨59766, false, false, [19923], [15]⟩,
        ⟨59769, false, false, [19923], []⟩,
        ⟨59775, false, false, [], []⟩,
        ⟨59776, false, false, [], []⟩,
        ⟨59778, false, false, [19923], []⟩
      ]⟩,
    ⟨[90233, 13], [19923, 90233], .contexts [
        ⟨59779, false, false, [], []⟩,
        ⟨59750, true, false, [], [90233]⟩
      ]⟩,
    ⟨[90235], [90233, 1], .source 45182⟩,
    ⟨[90233, 1], [90235], .contexts [
        ⟨59781, true, false, [], []⟩
      ]⟩,
    ⟨[90235, 1], [90233], .contexts [
        ⟨59782, true, false, [], [1]⟩,
        ⟨8, false, false, [90233], []⟩,
        ⟨59773, false, false, [], []⟩
      ]⟩,
    ⟨[90237], [90235, 3], .source 45183⟩,
    ⟨[90235, 3], [90237], .contexts [
        ⟨59784, true, false, [], []⟩
      ]⟩,
    ⟨[90235], [90235], .contexts []⟩,
    ⟨[90237, 3], [90235], .contexts [
        ⟨59785, true, false, [], [3]⟩,
        ⟨20, false, false, [90235], []⟩,
        ⟨59786, false, false, [], []⟩
      ]⟩,
    ⟨[90239], [90237, 5], .source 45184⟩,
    ⟨[90237, 5], [90239], .contexts [
        ⟨59788, true, false, [], []⟩
      ]⟩,
    ⟨[90237], [90237], .contexts []⟩,
    ⟨[90239, 5], [90237], .contexts [
        ⟨59789, true, false, [], [5]⟩,
        ⟨28, false, false, [90237], []⟩,
        ⟨59790, false, false, [], []⟩
      ]⟩,
    ⟨[90241], [90239, 1], .source 45185⟩,
    ⟨[90239, 1], [90241], .contexts [
        ⟨59792, true, false, [], []⟩
      ]⟩,
    ⟨[90239], [90239], .contexts []⟩,
    ⟨[90241, 1], [90239], .contexts [
        ⟨59793, true, false, [], [1]⟩,
        ⟨8, false, false, [90239], []⟩,
        ⟨59794, false, false, [], []⟩
      ]⟩,
    ⟨[90243], [90241, 9], .source 45186⟩,
    ⟨[90241, 9], [90243], .contexts [
        ⟨59796, true, false, [], []⟩
      ]⟩,
    ⟨[90241], [90241], .contexts []⟩,
    ⟨[90243, 9], [90241], .contexts [
        ⟨59797, true, false, [], [9]⟩,
        ⟨46, false, false, [90241], []⟩,
        ⟨59798, false, false, [], []⟩
      ]⟩,
    ⟨[90245], [90243, 11], .source 45187⟩,
    ⟨[90243, 11], [90245], .contexts [
        ⟨59800, true, false, [], []⟩
      ]⟩,
    ⟨[90243], [90243], .contexts []⟩,
    ⟨[90247], [90245, 1], .source 45188⟩,
    ⟨[90245, 1], [90247], .contexts [
        ⟨59803, true, false, [], []⟩
      ]⟩,
    ⟨[90245], [90245], .contexts []⟩,
    ⟨[90247, 1], [90245], .contexts [
        ⟨59804, true, false, [], [1]⟩,
        ⟨8, false, false, [90245], []⟩,
        ⟨59805, false, false, [], []⟩
      ]⟩,
    ⟨[90249], [90247, 13], .source 45189⟩,
    ⟨[90247, 13], [90249], .contexts [
        ⟨59807, true, false, [], []⟩
      ]⟩,
    ⟨[90247], [90247], .contexts []⟩,
    ⟨[90249, 13], [90247], .contexts [
        ⟨59808, true, false, [], [13]⟩,
        ⟨59, false, false, [90247], []⟩,
        ⟨59809, false, false, [], []⟩
      ]⟩,
    ⟨[90251], [90249, 15], .source 45190⟩,
    ⟨[90249, 15], [90251], .contexts [
        ⟨59811, true, false, [], []⟩
      ]⟩,
    ⟨[90249], [90249], .contexts []⟩,
    ⟨[90251, 15], [90249], .contexts [
        ⟨59812, true, false, [], [15]⟩,
        ⟨1, false, false, [90249], []⟩,
        ⟨59813, false, false, [], []⟩
      ]⟩,
    ⟨[90253], [90251, 1], .source 45191⟩,
    ⟨[90251, 1], [90253], .contexts [
        ⟨59815, true, false, [], []⟩
      ]⟩,
    ⟨[90251], [90251], .contexts []⟩,
    ⟨[90253, 1], [90251], .contexts [
        ⟨59816, true, false, [], [1]⟩,
        ⟨8, false, false, [90251], []⟩,
        ⟨59817, false, false, [], []⟩
      ]⟩,
    ⟨[90255], [90253, 3], .source 45192⟩,
    ⟨[90253, 3], [90255], .contexts [
        ⟨59819, true, false, [], []⟩
      ]⟩,
    ⟨[90253], [90253], .contexts []⟩,
    ⟨[90257], [90255, 5], .source 45193⟩,
    ⟨[90255, 5], [90257], .contexts [
        ⟨59822, true, false, [], []⟩
      ]⟩,
    ⟨[90255], [90255], .contexts []⟩,
    ⟨[90257, 5], [90255], .contexts [
        ⟨59823, true, false, [], [5]⟩,
        ⟨28, false, false, [90255], []⟩,
        ⟨59824, false, false, [], []⟩
      ]⟩,
    ⟨[90259], [90257, 1], .source 45194⟩,
    ⟨[90257, 1], [90259], .contexts [
        ⟨59826, true, false, [], []⟩
      ]⟩,
    ⟨[90257], [90257], .contexts []⟩,
    ⟨[90259, 1], [90257], .contexts [
        ⟨59827, true, false, [], [1]⟩,
        ⟨8, false, false, [90257], []⟩,
        ⟨59828, false, false, [], []⟩
      ]⟩,
    ⟨[90261], [90259, 9], .source 45195⟩,
    ⟨[90259, 9], [90261], .contexts [
        ⟨59830, true, false, [], []⟩
      ]⟩,
    ⟨[90259], [90259], .contexts []⟩,
    ⟨[90263], [90261, 11], .source 45196⟩,
    ⟨[90261, 11], [90263], .contexts [
        ⟨59833, true, false, [], []⟩
      ]⟩,
    ⟨[90261], [90261], .contexts []⟩,
    ⟨[90265], [90263, 1], .source 45197⟩,
    ⟨[90263, 1], [90265], .contexts [
        ⟨59836, true, false, [], []⟩
      ]⟩,
    ⟨[90263], [90263], .contexts []⟩,
    ⟨[90267], [90265, 13], .source 45198⟩]

/-- Exact literal claimed equations and contextual derivations, block 935. -/
def y322TCIndexRaw935 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90265, 13], [90267], .contexts [
        ⟨59839, true, false, [], []⟩
      ]⟩,
    ⟨[90265], [90265], .contexts []⟩,
    ⟨[90269], [90267, 15], .source 45199⟩,
    ⟨[90267, 15], [90269], .contexts [
        ⟨59842, true, false, [], []⟩
      ]⟩,
    ⟨[90267], [90267], .contexts []⟩,
    ⟨[90269, 15], [90267], .contexts [
        ⟨59843, true, false, [], [15]⟩,
        ⟨1, false, false, [90267], []⟩,
        ⟨59844, false, false, [], []⟩
      ]⟩,
    ⟨[90271], [90269, 1], .source 45200⟩,
    ⟨[90269, 1], [90271], .contexts [
        ⟨59846, true, false, [], []⟩
      ]⟩,
    ⟨[90269], [90269], .contexts []⟩,
    ⟨[90271, 1], [90269], .contexts [
        ⟨59847, true, false, [], [1]⟩,
        ⟨8, false, false, [90269], []⟩,
        ⟨59848, false, false, [], []⟩
      ]⟩,
    ⟨[90273], [90271, 3], .source 45201⟩,
    ⟨[90271, 3], [90273], .contexts [
        ⟨59850, true, false, [], []⟩
      ]⟩,
    ⟨[90271], [90271], .contexts []⟩,
    ⟨[90275], [90273, 5], .source 45202⟩,
    ⟨[90273, 5], [90275], .contexts [
        ⟨59853, true, false, [], []⟩
      ]⟩,
    ⟨[90273], [90273], .contexts []⟩,
    ⟨[90277], [90275, 1], .source 45203⟩,
    ⟨[90275, 1], [90277], .contexts [
        ⟨59856, true, false, [], []⟩
      ]⟩,
    ⟨[90275], [90275], .contexts []⟩,
    ⟨[90279], [90277, 9], .source 45204⟩,
    ⟨[90277, 9], [90279], .contexts [
        ⟨59859, true, false, [], []⟩
      ]⟩,
    ⟨[90277], [90277], .contexts []⟩,
    ⟨[90281], [90279, 11], .source 45205⟩,
    ⟨[90279, 11], [90281], .contexts [
        ⟨59862, true, false, [], []⟩
      ]⟩,
    ⟨[90279], [90279], .contexts []⟩,
    ⟨[90281, 11], [90279], .contexts [
        ⟨59863, true, false, [], [11]⟩,
        ⟨53, false, false, [90279], []⟩,
        ⟨59864, false, false, [], []⟩
      ]⟩,
    ⟨[90283], [90281, 1], .source 45206⟩,
    ⟨[90281, 1], [90283], .contexts [
        ⟨59866, true, false, [], []⟩
      ]⟩,
    ⟨[90281], [90281], .contexts []⟩,
    ⟨[90285], [90283, 13], .source 45207⟩,
    ⟨[90283, 13], [90285], .contexts [
        ⟨59869, true, false, [], []⟩
      ]⟩,
    ⟨[90283], [90283], .contexts []⟩,
    ⟨[90287], [90285, 15], .source 45208⟩,
    ⟨[90285, 15], [90287], .contexts [
        ⟨59872, true, false, [], []⟩
      ]⟩,
    ⟨[90285], [90285], .contexts []⟩,
    ⟨[90289], [90287, 1], .source 45209⟩,
    ⟨[90287, 1], [90289], .contexts [
        ⟨59875, true, false, [], []⟩
      ]⟩,
    ⟨[90287], [90287], .contexts []⟩,
    ⟨[90291], [90289, 3], .source 45210⟩,
    ⟨[90289, 3], [90291], .contexts [
        ⟨59878, true, false, [], []⟩
      ]⟩,
    ⟨[90289], [90289], .contexts []⟩,
    ⟨[90293], [90291, 5], .source 45211⟩,
    ⟨[90291, 5], [90293], .contexts [
        ⟨59881, true, false, [], []⟩
      ]⟩,
    ⟨[90291], [90291], .contexts []⟩,
    ⟨[90293, 5], [90291], .contexts [
        ⟨59882, true, false, [], [5]⟩,
        ⟨28, false, false, [90291], []⟩,
        ⟨59883, false, false, [], []⟩
      ]⟩,
    ⟨[90295], [90293, 1], .source 45212⟩,
    ⟨[90293, 1], [90295], .contexts [
        ⟨59885, true, false, [], []⟩
      ]⟩,
    ⟨[90293], [90293], .contexts []⟩,
    ⟨[90295, 1], [90293], .contexts [
        ⟨59886, true, false, [], [1]⟩,
        ⟨8, false, false, [90293], []⟩,
        ⟨59887, false, false, [], []⟩
      ]⟩,
    ⟨[90297], [90295, 9], .source 45213⟩,
    ⟨[90295, 9], [90297], .contexts [
        ⟨59889, true, false, [], []⟩
      ]⟩,
    ⟨[90295], [90295], .contexts []⟩,
    ⟨[90299], [90297, 11], .source 45214⟩,
    ⟨[90297, 11], [90299], .contexts [
        ⟨59892, true, false, [], []⟩
      ]⟩,
    ⟨[90297], [90297], .contexts []⟩,
    ⟨[90299, 11], [90297], .contexts [
        ⟨59893, true, false, [], [11]⟩,
        ⟨53, false, false, [90297], []⟩,
        ⟨59894, false, false, [], []⟩
      ]⟩,
    ⟨[90301], [90299, 1], .source 45215⟩,
    ⟨[90299], [90299], .contexts []⟩,
    ⟨[90301, 1], [90299], .contexts [
        ⟨59896, false, false, [], [1]⟩,
        ⟨8, false, false, [90299], []⟩,
        ⟨59897, false, false, [], []⟩
      ]⟩,
    ⟨[90303], [90301, 13], .source 45216⟩,
    ⟨[90301], [90301], .contexts []⟩,
    ⟨[90303, 13], [90301], .contexts [
        ⟨59899, false, false, [], [13]⟩,
        ⟨59, false, false, [90301], []⟩,
        ⟨59900, false, false, [], []⟩
      ]⟩,
    ⟨[90305], [90303, 15], .source 45217⟩,
    ⟨[90303], [90303], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 936. -/
def y322TCIndexRaw936 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90305, 15], [90303], .contexts [
        ⟨59902, false, false, [], [15]⟩,
        ⟨1, false, false, [90303], []⟩,
        ⟨59903, false, false, [], []⟩
      ]⟩,
    ⟨[90307], [90305, 1], .source 45218⟩,
    ⟨[90305], [90305], .contexts []⟩,
    ⟨[90307, 1], [90305], .contexts [
        ⟨59905, false, false, [], [1]⟩,
        ⟨8, false, false, [90305], []⟩,
        ⟨59906, false, false, [], []⟩
      ]⟩,
    ⟨[90309], [90307, 3], .source 45219⟩,
    ⟨[90307], [90307], .contexts []⟩,
    ⟨[90309, 3], [90307], .contexts [
        ⟨59908, false, false, [], [3]⟩,
        ⟨20, false, false, [90307], []⟩,
        ⟨59909, false, false, [], []⟩
      ]⟩,
    ⟨[90311], [90309, 5], .source 45220⟩,
    ⟨[90309, 5], [90311], .contexts [
        ⟨59911, true, false, [], []⟩
      ]⟩,
    ⟨[90309], [90309], .contexts []⟩,
    ⟨[90311, 5], [90309], .contexts [
        ⟨59912, true, false, [], [5]⟩,
        ⟨28, false, false, [90309], []⟩,
        ⟨59913, false, false, [], []⟩
      ]⟩,
    ⟨[90313], [90311, 1], .source 45221⟩,
    ⟨[90311, 1], [90313], .contexts [
        ⟨59915, true, false, [], []⟩
      ]⟩,
    ⟨[90311], [90311], .contexts []⟩,
    ⟨[90313, 1], [90311], .contexts [
        ⟨59916, true, false, [], [1]⟩,
        ⟨8, false, false, [90311], []⟩,
        ⟨59917, false, false, [], []⟩
      ]⟩,
    ⟨[90315], [90313, 9], .source 45222⟩,
    ⟨[90313], [90313], .contexts []⟩,
    ⟨[90315, 9], [90313], .contexts [
        ⟨59919, false, false, [], [9]⟩,
        ⟨46, false, false, [90313], []⟩,
        ⟨59920, false, false, [], []⟩
      ]⟩,
    ⟨[90317], [90315, 11], .source 45223⟩,
    ⟨[90315], [90315], .contexts []⟩,
    ⟨[90317, 11], [90315], .contexts [
        ⟨59922, false, false, [], [11]⟩,
        ⟨53, false, false, [90315], []⟩,
        ⟨59923, false, false, [], []⟩
      ]⟩,
    ⟨[90319], [90317, 1], .source 45224⟩,
    ⟨[90317, 1], [90319], .contexts [
        ⟨59925, true, false, [], []⟩
      ]⟩,
    ⟨[90317], [90317], .contexts []⟩,
    ⟨[90319, 1], [90317], .contexts [
        ⟨59926, true, false, [], [1]⟩,
        ⟨8, false, false, [90317], []⟩,
        ⟨59927, false, false, [], []⟩
      ]⟩,
    ⟨[90321], [90319, 13], .source 45225⟩,
    ⟨[90319, 13], [90321], .contexts [
        ⟨59929, true, false, [], []⟩
      ]⟩,
    ⟨[90319], [90319], .contexts []⟩,
    ⟨[90321, 13], [90319], .contexts [
        ⟨59930, true, false, [], [13]⟩,
        ⟨59, false, false, [90319], []⟩,
        ⟨59931, false, false, [], []⟩
      ]⟩,
    ⟨[90323], [90321, 15], .source 45226⟩,
    ⟨[90321, 15], [90323], .contexts [
        ⟨59933, true, false, [], []⟩
      ]⟩,
    ⟨[90321], [90321], .contexts []⟩,
    ⟨[90323, 15], [90321], .contexts [
        ⟨59934, true, false, [], [15]⟩,
        ⟨1, false, false, [90321], []⟩,
        ⟨59935, false, false, [], []⟩
      ]⟩,
    ⟨[90325], [90323, 1], .source 45227⟩,
    ⟨[90323, 1], [90325], .contexts [
        ⟨59937, true, false, [], []⟩
      ]⟩,
    ⟨[90323], [90323], .contexts []⟩,
    ⟨[90325, 1], [90323], .contexts [
        ⟨59938, true, false, [], [1]⟩,
        ⟨8, false, false, [90323], []⟩,
        ⟨59939, false, false, [], []⟩
      ]⟩,
    ⟨[90327], [90325, 3], .source 45228⟩,
    ⟨[90325, 3], [90327], .contexts [
        ⟨59941, true, false, [], []⟩
      ]⟩,
    ⟨[90325], [90325], .contexts []⟩,
    ⟨[90327, 3], [90325], .contexts [
        ⟨59942, true, false, [], [3]⟩,
        ⟨20, false, false, [90325], []⟩,
        ⟨59943, false, false, [], []⟩
      ]⟩,
    ⟨[90329], [90327, 5], .source 45229⟩,
    ⟨[90327, 5], [90329], .contexts [
        ⟨59945, true, false, [], []⟩
      ]⟩,
    ⟨[90327], [90327], .contexts []⟩,
    ⟨[90329, 5], [90327], .contexts [
        ⟨59946, true, false, [], [5]⟩,
        ⟨28, false, false, [90327], []⟩,
        ⟨59947, false, false, [], []⟩
      ]⟩,
    ⟨[90331], [90329, 1], .source 45230⟩,
    ⟨[90329, 1], [90331], .contexts [
        ⟨59949, true, false, [], []⟩
      ]⟩,
    ⟨[90329], [90329], .contexts []⟩,
    ⟨[90331, 1], [90329], .contexts [
        ⟨59950, true, false, [], [1]⟩,
        ⟨8, false, false, [90329], []⟩,
        ⟨59951, false, false, [], []⟩
      ]⟩,
    ⟨[90333], [90331, 9], .source 45231⟩,
    ⟨[90331, 9], [90333], .contexts [
        ⟨59953, true, false, [], []⟩
      ]⟩,
    ⟨[90331], [90331], .contexts []⟩,
    ⟨[90333, 9], [90331], .contexts [
        ⟨59954, true, false, [], [9]⟩,
        ⟨46, false, false, [90331], []⟩,
        ⟨59955, false, false, [], []⟩
      ]⟩,
    ⟨[90335], [90333, 11], .source 45232⟩,
    ⟨[90333, 11], [90335], .contexts [
        ⟨59957, true, false, [], []⟩
      ]⟩,
    ⟨[90333], [90333], .contexts []⟩,
    ⟨[90335, 11], [90333], .contexts [
        ⟨59958, true, false, [], [11]⟩,
        ⟨53, false, false, [90333], []⟩,
        ⟨59959, false, false, [], []⟩
      ]⟩,
    ⟨[90337], [90335, 1], .source 45233⟩,
    ⟨[90335, 1], [90337], .contexts [
        ⟨59961, true, false, [], []⟩
      ]⟩,
    ⟨[90335], [90335], .contexts []⟩,
    ⟨[90337, 1], [90335], .contexts [
        ⟨59962, true, false, [], [1]⟩,
        ⟨8, false, false, [90335], []⟩,
        ⟨59963, false, false, [], []⟩
      ]⟩,
    ⟨[90339], [90337, 13], .source 45234⟩,
    ⟨[90337, 13], [90339], .contexts [
        ⟨59965, true, false, [], []⟩
      ]⟩,
    ⟨[90337], [90337], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 937. -/
def y322TCIndexRaw937 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90339, 13], [90337], .contexts [
        ⟨59966, true, false, [], [13]⟩,
        ⟨59, false, false, [90337], []⟩,
        ⟨59967, false, false, [], []⟩
      ]⟩,
    ⟨[90341], [90339, 15], .source 45235⟩,
    ⟨[90339, 15], [90341], .contexts [
        ⟨59969, true, false, [], []⟩
      ]⟩,
    ⟨[90339], [90339], .contexts []⟩,
    ⟨[90341, 15], [90339], .contexts [
        ⟨59970, true, false, [], [15]⟩,
        ⟨1, false, false, [90339], []⟩,
        ⟨59971, false, false, [], []⟩
      ]⟩,
    ⟨[90343], [90341, 1], .source 45236⟩,
    ⟨[90341, 1], [90343], .contexts [
        ⟨59973, true, false, [], []⟩
      ]⟩,
    ⟨[90341], [90341], .contexts []⟩,
    ⟨[90343, 1], [90341], .contexts [
        ⟨59974, true, false, [], [1]⟩,
        ⟨8, false, false, [90341], []⟩,
        ⟨59975, false, false, [], []⟩
      ]⟩,
    ⟨[90345], [90343, 3], .source 45237⟩,
    ⟨[90343, 3], [90345], .contexts [
        ⟨59977, true, false, [], []⟩
      ]⟩,
    ⟨[90343], [90343], .contexts []⟩,
    ⟨[90345, 3], [90343], .contexts [
        ⟨59978, true, false, [], [3]⟩,
        ⟨20, false, false, [90343], []⟩,
        ⟨59979, false, false, [], []⟩
      ]⟩,
    ⟨[90347], [90345, 5], .source 45238⟩,
    ⟨[90345, 5], [90347], .contexts [
        ⟨59981, true, false, [], []⟩
      ]⟩,
    ⟨[90345], [90345], .contexts []⟩,
    ⟨[90347, 5], [90345], .contexts [
        ⟨59982, true, false, [], [5]⟩,
        ⟨28, false, false, [90345], []⟩,
        ⟨59983, false, false, [], []⟩
      ]⟩,
    ⟨[90349], [90347, 1], .source 45239⟩,
    ⟨[90347, 1], [90349], .contexts [
        ⟨59985, true, false, [], []⟩
      ]⟩,
    ⟨[90347], [90347], .contexts []⟩,
    ⟨[90349, 1], [90347], .contexts [
        ⟨59986, true, false, [], [1]⟩,
        ⟨8, false, false, [90347], []⟩,
        ⟨59987, false, false, [], []⟩
      ]⟩,
    ⟨[90351], [90349, 9], .source 45240⟩,
    ⟨[90349], [90349], .contexts []⟩,
    ⟨[90351, 9], [90349], .contexts [
        ⟨59989, false, false, [], [9]⟩,
        ⟨46, false, false, [90349], []⟩,
        ⟨59990, false, false, [], []⟩
      ]⟩,
    ⟨[90353], [90351, 11], .source 45241⟩,
    ⟨[90351, 11], [90353], .contexts [
        ⟨59992, true, false, [], []⟩
      ]⟩,
    ⟨[90351], [90351], .contexts []⟩,
    ⟨[90353, 11], [90351], .contexts [
        ⟨59993, true, false, [], [11]⟩,
        ⟨53, false, false, [90351], []⟩,
        ⟨59994, false, false, [], []⟩
      ]⟩,
    ⟨[90353], [90353], .contexts []⟩,
    ⟨[90353], [90353], .contexts []⟩,
    ⟨[90349], [90349], .contexts []⟩,
    ⟨[90347], [90347], .contexts []⟩,
    ⟨[90347, 5], [90345], .contexts [
        ⟨59984, false, false, [], []⟩
      ]⟩,
    ⟨[90345], [90345], .contexts []⟩,
    ⟨[90341], [90341], .contexts []⟩,
    ⟨[90351, 9, 1, 5, 3, 1], [90341], .contexts [
        ⟨59991, false, false, [], [1, 5, 3, 1]⟩,
        ⟨59998, false, false, [], [1, 5, 3, 1]⟩,
        ⟨59990, false, false, [], [1, 5, 3, 1]⟩,
        ⟨59990, false, false, [], [1, 5, 3, 1]⟩,
        ⟨59988, false, false, [], [5, 3, 1]⟩,
        ⟨59999, false, false, [], [5, 3, 1]⟩,
        ⟨59987, false, false, [], [5, 3, 1]⟩,
        ⟨59987, false, false, [], [5, 3, 1]⟩,
        ⟨60000, false, false, [], [3, 1]⟩,
        ⟨60001, false, false, [], [3, 1]⟩,
        ⟨59983, false, false, [], [3, 1]⟩,
        ⟨59983, false, false, [], [3, 1]⟩,
        ⟨59980, false, false, [], [1]⟩,
        ⟨59979, false, false, [], [1]⟩,
        ⟨59979, false, false, [], [1]⟩,
        ⟨59976, false, false, [], []⟩,
        ⟨60002, false, false, [], []⟩,
        ⟨59975, false, false, [], []⟩,
        ⟨59975, false, false, [], []⟩
      ]⟩,
    ⟨[90341, 15], [90339], .contexts [
        ⟨59972, false, false, [], []⟩
      ]⟩,
    ⟨[90339], [90339], .contexts []⟩,
    ⟨[90339, 13], [90337], .contexts [
        ⟨59968, false, false, [], []⟩
      ]⟩,
    ⟨[90337], [90337], .contexts []⟩,
    ⟨[90337, 1], [90335], .contexts [
        ⟨59964, false, false, [], []⟩
      ]⟩,
    ⟨[90335], [90335], .contexts []⟩,
    ⟨[90335, 11], [90333], .contexts [
        ⟨59960, false, false, [], []⟩
      ]⟩,
    ⟨[90333], [90333], .contexts []⟩,
    ⟨[90333, 9], [90331], .contexts [
        ⟨59956, false, false, [], []⟩
      ]⟩,
    ⟨[90331], [90331], .contexts []⟩,
    ⟨[90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9], [90331], .contexts [
        ⟨60003, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨60004, false, false, [], [13, 1, 11, 9]⟩,
        ⟨60005, false, false, [], [13, 1, 11, 9]⟩,
        ⟨59971, false, false, [], [13, 1, 11, 9]⟩,
        ⟨59971, false, false, [], [13, 1, 11, 9]⟩,
        ⟨60006, false, false, [], [1, 11, 9]⟩,
        ⟨60007, false, false, [], [1, 11, 9]⟩,
        ⟨59967, false, false, [], [1, 11, 9]⟩,
        ⟨59967, false, false, [], [1, 11, 9]⟩,
        ⟨60008, false, false, [], [11, 9]⟩,
        ⟨60009, false, false, [], [11, 9]⟩,
        ⟨59963, false, false, [], [11, 9]⟩,
        ⟨59963, false, false, [], [11, 9]⟩,
        ⟨60010, false, false, [], [9]⟩,
        ⟨60011, false, false, [], [9]⟩,
        ⟨59959, false, false, [], [9]⟩,
        ⟨59959, false, false, [], [9]⟩,
        ⟨60012, false, false, [], []⟩,
        ⟨60013, false, false, [], []⟩,
        ⟨59955, false, false, [], []⟩,
        ⟨59955, false, false, [], []⟩
      ]⟩,
    ⟨[90331, 1], [90329], .contexts [
        ⟨59952, false, false, [], []⟩
      ]⟩,
    ⟨[90329], [90329], .contexts []⟩,
    ⟨[90327], [90327], .contexts []⟩,
    ⟨[90327, 3], [90325], .contexts [
        ⟨59944, false, false, [], []⟩
      ]⟩,
    ⟨[90325], [90325], .contexts []⟩,
    ⟨[90323], [90323], .contexts []⟩,
    ⟨[
      90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15
    ], [90321], .contexts [
        ⟨60014, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨60015, false, false, [], [5, 3, 1, 15]⟩,
        ⟨60016, false, false, [], [5, 3, 1, 15]⟩,
        ⟨59951, false, false, [], [5, 3, 1, 15]⟩,
        ⟨59951, false, false, [], [5, 3, 1, 15]⟩,
        ⟨59948, false, false, [], [3, 1, 15]⟩,
        ⟨60017, false, false, [], [3, 1, 15]⟩,
        ⟨59947, false, false, [], [3, 1, 15]⟩,
        ⟨59947, false, false, [], [3, 1, 15]⟩,
        ⟨60018, false, false, [], [1, 15]⟩,
        ⟨60019, false, false, [], [1, 15]⟩,
        ⟨59943, false, false, [], [1, 15]⟩,
        ⟨59943, false, false, [], [1, 15]⟩,
        ⟨59940, false, false, [], [15]⟩,
        ⟨60020, false, false, [], [15]⟩,
        ⟨59939, false, false, [], [15]⟩,
        ⟨59939, false, false, [], [15]⟩,
        ⟨59936, false, false, [], []⟩,
        ⟨59935, false, false, [], []⟩,
        ⟨59935, false, false, [], []⟩
      ]⟩,
    ⟨[90319], [90319], .contexts []⟩,
    ⟨[90317, 11], [90315], .contexts [
        ⟨59924, false, false, [], []⟩
      ]⟩,
    ⟨[90315], [90315], .contexts []⟩,
    ⟨[90313], [90313], .contexts []⟩,
    ⟨[90311], [90311], .contexts []⟩,
    ⟨[
      90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [90311], .contexts [
        ⟨60021, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨59932, false, false, [], [1, 11, 9, 1]⟩,
        ⟨60022, false, false, [], [1, 11, 9, 1]⟩,
        ⟨59931, false, false, [], [1, 11, 9, 1]⟩,
        ⟨59931, false, false, [], [1, 11, 9, 1]⟩,
        ⟨59928, false, false, [], [11, 9, 1]⟩,
        ⟨59927, false, false, [], [11, 9, 1]⟩,
        ⟨59927, false, false, [], [11, 9, 1]⟩,
        ⟨60023, false, false, [], [9, 1]⟩,
        ⟨60024, false, false, [], [9, 1]⟩,
        ⟨59923, false, false, [], [9, 1]⟩,
        ⟨59923, false, false, [], [9, 1]⟩,
        ⟨59921, false, false, [], [1]⟩,
        ⟨60025, false, false, [], [1]⟩,
        ⟨59920, false, false, [], [1]⟩,
        ⟨59920, false, false, [], [1]⟩,
        ⟨59918, false, false, [], []⟩,
        ⟨60026, false, false, [], []⟩,
        ⟨59917, false, false, [], []⟩,
        ⟨59917, false, false, [], []⟩
      ]⟩,
    ⟨[90307], [90307], .contexts []⟩,
    ⟨[90305], [90305], .contexts []⟩,
    ⟨[90305, 15], [90303], .contexts [
        ⟨59904, false, false, [], []⟩
      ]⟩,
    ⟨[90303], [90303], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 938. -/
def y322TCIndexRaw938 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90301], [90301], .contexts []⟩,
    ⟨[
      90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13
    ], [90301], .contexts [
        ⟨60027, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨59914, false, false, [], [3, 1, 15, 13]⟩,
        ⟨59913, false, false, [], [3, 1, 15, 13]⟩,
        ⟨59913, false, false, [], [3, 1, 15, 13]⟩,
        ⟨59910, false, false, [], [1, 15, 13]⟩,
        ⟨60028, false, false, [], [1, 15, 13]⟩,
        ⟨59909, false, false, [], [1, 15, 13]⟩,
        ⟨59909, false, false, [], [1, 15, 13]⟩,
        ⟨59907, false, false, [], [15, 13]⟩,
        ⟨60029, false, false, [], [15, 13]⟩,
        ⟨59906, false, false, [], [15, 13]⟩,
        ⟨59906, false, false, [], [15, 13]⟩,
        ⟨60030, false, false, [], [13]⟩,
        ⟨60031, false, false, [], [13]⟩,
        ⟨59903, false, false, [], [13]⟩,
        ⟨59903, false, false, [], [13]⟩,
        ⟨59901, false, false, [], []⟩,
        ⟨60032, false, false, [], []⟩,
        ⟨59900, false, false, [], []⟩,
        ⟨59900, false, false, [], []⟩
      ]⟩,
    ⟨[90299], [90299], .contexts []⟩,
    ⟨[90297], [90297], .contexts []⟩,
    ⟨[90295], [90295], .contexts []⟩,
    ⟨[90293], [90293], .contexts []⟩,
    ⟨[90291], [90291], .contexts []⟩,
    ⟨[
      90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5
    ], [90291], .contexts [
        ⟨60033, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨59898, false, false, [], [11, 9, 1, 5]⟩,
        ⟨60034, false, false, [], [11, 9, 1, 5]⟩,
        ⟨59897, false, false, [], [11, 9, 1, 5]⟩,
        ⟨59897, false, false, [], [11, 9, 1, 5]⟩,
        ⟨59895, false, false, [], [9, 1, 5]⟩,
        ⟨60035, false, false, [], [9, 1, 5]⟩,
        ⟨59894, false, false, [], [9, 1, 5]⟩,
        ⟨59894, false, false, [], [9, 1, 5]⟩,
        ⟨59890, true, false, [], [9, 1, 5]⟩,
        ⟨46, false, false, [90295], [1, 5]⟩,
        ⟨59891, false, false, [], [1, 5]⟩,
        ⟨60036, false, false, [], [1, 5]⟩,
        ⟨59891, false, false, [], [1, 5]⟩,
        ⟨59891, false, false, [], [1, 5]⟩,
        ⟨59888, false, false, [], [5]⟩,
        ⟨60037, false, false, [], [5]⟩,
        ⟨59887, false, false, [], [5]⟩,
        ⟨59887, false, false, [], [5]⟩,
        ⟨59884, false, false, [], []⟩,
        ⟨60038, false, false, [], []⟩,
        ⟨59883, false, false, [], []⟩,
        ⟨59883, false, false, [], []⟩
      ]⟩,
    ⟨[90289], [90289], .contexts []⟩,
    ⟨[90287], [90287], .contexts []⟩,
    ⟨[90285], [90285], .contexts []⟩,
    ⟨[
      90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [90283], .contexts [
        ⟨60039, false, false, [], [3, 1, 15, 13]⟩,
        ⟨59879, true, false, [], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [90289], [1, 15, 13]⟩,
        ⟨59880, false, false, [], [1, 15, 13]⟩,
        ⟨60040, false, false, [], [1, 15, 13]⟩,
        ⟨59880, false, false, [], [1, 15, 13]⟩,
        ⟨59880, false, false, [], [1, 15, 13]⟩,
        ⟨59876, true, false, [], [1, 15, 13]⟩,
        ⟨8, false, false, [90287], [15, 13]⟩,
        ⟨59877, false, false, [], [15, 13]⟩,
        ⟨60041, false, false, [], [15, 13]⟩,
        ⟨59877, false, false, [], [15, 13]⟩,
        ⟨59877, false, false, [], [15, 13]⟩,
        ⟨59873, true, false, [], [15, 13]⟩,
        ⟨1, false, false, [90285], [13]⟩,
        ⟨59874, false, false, [], [13]⟩,
        ⟨60042, false, false, [], [13]⟩,
        ⟨59874, false, false, [], [13]⟩,
        ⟨59874, false, false, [], [13]⟩,
        ⟨59870, true, false, [], [13]⟩,
        ⟨59, false, false, [90283], []⟩,
        ⟨59871, false, false, [], []⟩,
        ⟨59871, false, false, [], []⟩,
        ⟨59871, false, false, [], []⟩
      ]⟩,
    ⟨[90281], [90281], .contexts []⟩,
    ⟨[90279], [90279], .contexts []⟩,
    ⟨[90277], [90277], .contexts []⟩,
    ⟨[90275], [90275], .contexts []⟩,
    ⟨[
      90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1
    ], [90275], .contexts [
        ⟨60043, false, false, [], [1, 11, 9, 1]⟩,
        ⟨59867, true, false, [], [1, 11, 9, 1]⟩,
        ⟨8, false, false, [90281], [11, 9, 1]⟩,
        ⟨59868, false, false, [], [11, 9, 1]⟩,
        ⟨60044, false, false, [], [11, 9, 1]⟩,
        ⟨59868, false, false, [], [11, 9, 1]⟩,
        ⟨59868, false, false, [], [11, 9, 1]⟩,
        ⟨59865, false, false, [], [9, 1]⟩,
        ⟨60045, false, false, [], [9, 1]⟩,
        ⟨59864, false, false, [], [9, 1]⟩,
        ⟨59864, false, false, [], [9, 1]⟩,
        ⟨59860, true, false, [], [9, 1]⟩,
        ⟨46, false, false, [90277], [1]⟩,
        ⟨59861, false, false, [], [1]⟩,
        ⟨60046, false, false, [], [1]⟩,
        ⟨59861, false, false, [], [1]⟩,
        ⟨59861, false, false, [], [1]⟩,
        ⟨59857, true, false, [], [1]⟩,
        ⟨8, false, false, [90275], []⟩,
        ⟨59858, false, false, [], []⟩,
        ⟨60047, false, false, [], []⟩,
        ⟨59858, false, false, [], []⟩,
        ⟨59858, false, false, [], []⟩
      ]⟩,
    ⟨[90271], [90271], .contexts []⟩,
    ⟨[90269], [90269], .contexts []⟩,
    ⟨[90269, 15], [90267], .contexts [
        ⟨59845, false, false, [], []⟩
      ]⟩,
    ⟨[90267], [90267], .contexts []⟩,
    ⟨[
      90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15
    ], [90267], .contexts [
        ⟨60048, false, false, [], [5, 3, 1, 15]⟩,
        ⟨59854, true, false, [], [5, 3, 1, 15]⟩,
        ⟨28, false, false, [90273], [3, 1, 15]⟩,
        ⟨59855, false, false, [], [3, 1, 15]⟩,
        ⟨59855, false, false, [], [3, 1, 15]⟩,
        ⟨59855, false, false, [], [3, 1, 15]⟩,
        ⟨59851, true, false, [], [3, 1, 15]⟩,
        ⟨20, false, false, [90271], [1, 15]⟩,
        ⟨59852, false, false, [], [1, 15]⟩,
        ⟨60049, false, false, [], [1, 15]⟩,
        ⟨59852, false, false, [], [1, 15]⟩,
        ⟨59852, false, false, [], [1, 15]⟩,
        ⟨59849, false, false, [], [15]⟩,
        ⟨60050, false, false, [], [15]⟩,
        ⟨59848, false, false, [], [15]⟩,
        ⟨59848, false, false, [], [15]⟩,
        ⟨60051, false, false, [], []⟩,
        ⟨60052, false, false, [], []⟩,
        ⟨59844, false, false, [], []⟩,
        ⟨59844, false, false, [], []⟩
      ]⟩,
    ⟨[90265], [90265], .contexts []⟩,
    ⟨[90263], [90263], .contexts []⟩,
    ⟨[90261], [90261], .contexts []⟩,
    ⟨[90259], [90259], .contexts []⟩,
    ⟨[
      90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [90259], .contexts [
        ⟨60053, false, false, [], [13, 1, 11, 9]⟩,
        ⟨59840, true, false, [], [13, 1, 11, 9]⟩,
        ⟨59, false, false, [90265], [1, 11, 9]⟩,
        ⟨59841, false, false, [], [1, 11, 9]⟩,
        ⟨60054, false, false, [], [1, 11, 9]⟩,
        ⟨59841, false, false, [], [1, 11, 9]⟩,
        ⟨59841, false, false, [], [1, 11, 9]⟩,
        ⟨59837, true, false, [], [1, 11, 9]⟩,
        ⟨8, false, false, [90263], [11, 9]⟩,
        ⟨59838, false, false, [], [11, 9]⟩,
        ⟨60055, false, false, [], [11, 9]⟩,
        ⟨59838, false, false, [], [11, 9]⟩,
        ⟨59838, false, false, [], [11, 9]⟩,
        ⟨59834, true, false, [], [11, 9]⟩,
        ⟨53, false, false, [90261], [9]⟩,
        ⟨59835, false, false, [], [9]⟩,
        ⟨60056, false, false, [], [9]⟩,
        ⟨59835, false, false, [], [9]⟩,
        ⟨59835, false, false, [], [9]⟩,
        ⟨59831, true, false, [], [9]⟩,
        ⟨46, false, false, [90259], []⟩,
        ⟨59832, false, false, [], []⟩,
        ⟨60057, false, false, [], []⟩,
        ⟨59832, false, false, [], []⟩,
        ⟨59832, false, false, [], []⟩
      ]⟩,
    ⟨[90257], [90257], .contexts []⟩,
    ⟨[90253], [90253], .contexts []⟩,
    ⟨[90251], [90251], .contexts []⟩,
    ⟨[90251, 15], [90249], .contexts [
        ⟨59814, false, false, [], []⟩
      ]⟩,
    ⟨[90249], [90249], .contexts []⟩,
    ⟨[
      90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15
    ], [90249], .contexts [
        ⟨60058, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨59829, false, false, [], [5, 3, 1, 15]⟩,
        ⟨60059, false, false, [], [5, 3, 1, 15]⟩,
        ⟨59828, false, false, [], [5, 3, 1, 15]⟩,
        ⟨59828, false, false, [], [5, 3, 1, 15]⟩,
        ⟨59825, false, false, [], [3, 1, 15]⟩,
        ⟨59824, false, false, [], [3, 1, 15]⟩,
        ⟨59824, false, false, [], [3, 1, 15]⟩,
        ⟨59820, true, false, [], [3, 1, 15]⟩,
        ⟨20, false, false, [90253], [1, 15]⟩,
        ⟨59821, false, false, [], [1, 15]⟩,
        ⟨60060, false, false, [], [1, 15]⟩,
        ⟨59821, false, false, [], [1, 15]⟩,
        ⟨59821, false, false, [], [1, 15]⟩,
        ⟨59818, false, false, [], [15]⟩,
        ⟨60061, false, false, [], [15]⟩,
        ⟨59817, false, false, [], [15]⟩,
        ⟨59817, false, false, [], [15]⟩,
        ⟨60062, false, false, [], []⟩,
        ⟨60063, false, false, [], []⟩,
        ⟨59813, false, false, [], []⟩,
        ⟨59813, false, false, [], []⟩
      ]⟩,
    ⟨[90247], [90247], .contexts []⟩,
    ⟨[90243], [90243], .contexts []⟩,
    ⟨[90241], [90241], .contexts []⟩,
    ⟨[90241, 1], [90239], .contexts [
        ⟨59795, false, false, [], []⟩
      ]⟩,
    ⟨[90239], [90239], .contexts []⟩,
    ⟨[
      90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [90239], .contexts [
        ⟨60064, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨59810, false, false, [], [1, 11, 9, 1]⟩,
        ⟨60065, false, false, [], [1, 11, 9, 1]⟩,
        ⟨59809, false, false, [], [1, 11, 9, 1]⟩,
        ⟨59809, false, false, [], [1, 11, 9, 1]⟩,
        ⟨59806, false, false, [], [11, 9, 1]⟩,
        ⟨59805, false, false, [], [11, 9, 1]⟩,
        ⟨59805, false, false, [], [11, 9, 1]⟩,
        ⟨59801, true, false, [], [11, 9, 1]⟩,
        ⟨53, false, false, [90243], [9, 1]⟩,
        ⟨59802, false, false, [], [9, 1]⟩,
        ⟨60066, false, false, [], [9, 1]⟩,
        ⟨59802, false, false, [], [9, 1]⟩,
        ⟨59802, false, false, [], [9, 1]⟩,
        ⟨59799, false, false, [], [1]⟩,
        ⟨60067, false, false, [], [1]⟩,
        ⟨59798, false, false, [], [1]⟩,
        ⟨59798, false, false, [], [1]⟩,
        ⟨60068, false, false, [], []⟩,
        ⟨60069, false, false, [], []⟩,
        ⟨59794, false, false, [], []⟩,
        ⟨59794, false, false, [], []⟩
      ]⟩,
    ⟨[90235], [90235], .contexts []⟩,
    ⟨[90233, 15], [90231], .contexts [
        ⟨59771, false, false, [], []⟩
      ]⟩,
    ⟨[90231], [90231], .contexts []⟩,
    ⟨[
      90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13
    ], [90229], .contexts [
        ⟨60070, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨59791, false, false, [], [3, 1, 15, 13]⟩,
        ⟨59790, false, false, [], [3, 1, 15, 13]⟩,
        ⟨59790, false, false, [], [3, 1, 15, 13]⟩,
        ⟨59787, false, false, [], [1, 15, 13]⟩,
        ⟨60071, false, false, [], [1, 15, 13]⟩,
        ⟨59786, false, false, [], [1, 15, 13]⟩,
        ⟨59786, false, false, [], [1, 15, 13]⟩,
        ⟨59783, false, false, [], [15, 13]⟩,
        ⟨59772, false, false, [], [15, 13]⟩,
        ⟨59773, false, false, [], [15, 13]⟩,
        ⟨59773, false, false, [], [15, 13]⟩,
        ⟨60072, false, false, [], [13]⟩,
        ⟨60073, false, false, [], [13]⟩,
        ⟨59770, false, false, [], [13]⟩,
        ⟨59770, false, false, [], [13]⟩,
        ⟨59774, false, false, [], []⟩,
        ⟨59755, false, false, [], []⟩,
        ⟨59756, false, false, [], []⟩,
        ⟨59756, false, false, [], []⟩
      ]⟩,
    ⟨[24791, 90225], [24791, 90225], .contexts []⟩,
    ⟨[24791, 90225], [24791, 90225], .contexts []⟩,
    ⟨[
      90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5
    ], [24791, 89441], .contexts [
        ⟨60074, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨59754, false, false, [], [11, 9, 1, 5]⟩,
        ⟨59735, false, false, [], [11, 9, 1, 5]⟩,
        ⟨59736, false, false, [], [11, 9, 1, 5]⟩,
        ⟨59736, false, false, [], [11, 9, 1, 5]⟩,
        ⟨59758, false, false, [], [9, 1, 5]⟩,
        ⟨39414, false, false, [], [9, 1, 5]⟩,
        ⟨39384, false, false, [], [9, 1, 5]⟩,
        ⟨39384, false, false, [], [9, 1, 5]⟩,
        ⟨59738, false, false, [], [1, 5]⟩,
        ⟨39411, false, false, [], [1, 5]⟩,
        ⟨39388, false, false, [], [1, 5]⟩,
        ⟨39388, false, false, [], [1, 5]⟩,
        ⟨59730, false, false, [], [5]⟩,
        ⟨60075, false, false, [], [5]⟩,
        ⟨60076, false, false, [], [5]⟩,
        ⟨60076, false, false, [], [5]⟩,
        ⟨59705, false, false, [24791], []⟩
      ]⟩,
    ⟨[24793], [24791, 16219], .source 12461⟩,
    ⟨[24795], [24793, 1075], .source 12462⟩,
    ⟨[24797], [24795, 2575], .source 12463⟩,
    ⟨[
      90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [24797, 78833], .contexts [
        ⟨60077, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨56099, false, false, [24791], [1, 15, 13, 1]⟩,
        ⟨60078, true, false, [], [83363, 1, 15, 13, 1]⟩,
        ⟨20958, false, false, [24793], [15, 13, 1]⟩,
        ⟨60079, true, false, [], [83363, 15, 13, 1]⟩,
        ⟨20972, false, false, [24795], [13, 1]⟩,
        ⟨60080, true, false, [], [83363, 13, 1]⟩,
        ⟨20969, false, false, [24797], [1]⟩,
        ⟨5540, false, false, [24797], []⟩
      ]⟩,
    ⟨[24799], [24797, 2215], .source 12464⟩,
    ⟨[24801], [24799, 15589], .source 12465⟩,
    ⟨[24803], [24801, 15479], .source 12466⟩,
    ⟨[24805], [24803, 2211], .source 12467⟩,
    ⟨[
      90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3
    ], [24805, 79015], .contexts [
        ⟨60081, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨17197, false, false, [24797], [9, 1, 5, 3]⟩,
        ⟨17194, false, false, [24797], [1, 5, 3]⟩,
        ⟨60082, true, false, [], [82829, 1, 5, 3]⟩,
        ⟨17187, false, false, [24799], [5, 3]⟩,
        ⟨60083, true, false, [], [82799, 5, 3]⟩,
        ⟨16757, false, false, [24801], [3]⟩,
        ⟨60084, true, false, [], [79185, 3]⟩,
        ⟨6257, false, false, [24803], []⟩,
        ⟨60085, true, false, [], [79015]⟩
      ]⟩,
    ⟨[24807], [24805, 7357], .source 12468⟩,
    ⟨[24809], [24807, 15305], .source 12469⟩,
    ⟨[24811], [24809, 15349], .source 12470⟩,
    ⟨[24813], [24811, 15351], .source 12471⟩,
    ⟨[
      90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [24813, 78405], .contexts [
        ⟨60086, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨6215, false, false, [24805], [15, 13, 1, 11]⟩,
        ⟨14996, false, false, [24805], [13, 1, 11]⟩,
        ⟨60087, true, false, [], [82655, 13, 1, 11]⟩,
        ⟨15794, false, false, [24807], [1, 11]⟩,
        ⟨60088, true, false, [], [82721, 1, 11]⟩,
        ⟨15783, false, false, [24809], [11]⟩,
        ⟨60089, true, false, [], [82721, 11]⟩,
        ⟨15800, false, false, [24811], []⟩,
        ⟨60090, true, false, [], [78405]⟩
      ]⟩,
    ⟨[24815], [24813, 1063], .source 12472⟩,
    ⟨[24817], [24815, 323], .source 12473⟩,
    ⟨[24819], [24817, 16495], .source 12474⟩,
    ⟨[
      90351, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1
    ], [24819, 83673], .contexts [
        ⟨60091, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨4267, false, false, [24813], [1, 5, 3, 1]⟩,
        ⟨60092, true, false, [], [78405, 1, 5, 3, 1]⟩,
        ⟨4259, false, false, [24815], [5, 3, 1]⟩,
        ⟨60093, true, false, [], [78405, 5, 3, 1]⟩,
        ⟨16494, false, false, [24817], [3, 1]⟩,
        ⟨22553, false, false, [24817], [1]⟩,
        ⟨60094, true, false, [], [83671, 1]⟩,
        ⟨22561, false, false, [24819], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 939. -/
def y322TCIndexRaw939 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[24821], [24819, 16635], .source 12475⟩,
    ⟨[24821, 85357], [24821, 85357], .contexts []⟩,
    ⟨[24821, 85357], [24821, 85357], .contexts []⟩,
    ⟨[90353, 1], [90353, 1], .contexts []⟩,
    ⟨[24821], [24821], .contexts []⟩,
    ⟨[24821], [24821], .contexts []⟩,
    ⟨[90353, 1], [24821, 85357], .contexts [
        ⟨60099, false, false, [], []⟩,
        ⟨59997, true, false, [], [1]⟩,
        ⟨59997, true, false, [], [1]⟩,
        ⟨59996, true, false, [], [1]⟩,
        ⟨59993, true, false, [], [1]⟩,
        ⟨3787, false, false, [90351], []⟩,
        ⟨3788, false, false, [90351], []⟩,
        ⟨60095, false, false, [], [15, 13]⟩,
        ⟨31768, false, false, [24819], [13]⟩,
        ⟨60096, true, false, [], [85355, 13]⟩,
        ⟨31770, false, false, [24821], []⟩,
        ⟨60097, false, false, [], []⟩,
        ⟨60098, false, false, [], []⟩,
        ⟨31779, false, false, [24821], []⟩,
        ⟨60101, true, false, [], [85357]⟩,
        ⟨60100, true, false, [], [85357]⟩,
        ⟨13, true, false, [], [24821, 85357]⟩
      ]⟩,
    ⟨[24823], [24820], .source 12476⟩,
    ⟨[85357, 1], [24823, 90353], .contexts [
        ⟨60102, true, false, [24820], [1]⟩,
        ⟨8, false, false, [24820, 90353], []⟩,
        ⟨60103, true, false, [], [90353]⟩
      ]⟩,
    ⟨[90353, 11], [90351], .contexts [
        ⟨59995, false, false, [], []⟩
      ]⟩,
    ⟨[90353, 1], [24821, 85357], .contexts [
        ⟨60099, false, false, [], []⟩,
        ⟨60102, false, false, [], []⟩,
        ⟨60097, false, false, [], []⟩,
        ⟨60098, false, false, [], []⟩,
        ⟨60098, false, false, [], []⟩
      ]⟩,
    ⟨[24825], [24821, 20513], .source 12477⟩,
    ⟨[24827], [24824], .source 12478⟩,
    ⟨[24825], [24826], .contexts [
        ⟨60108, true, true, [], []⟩
      ]⟩,
    ⟨[90351], [24825, 87025], .contexts [
        ⟨60108, false, false, [24826], [90351]⟩,
        ⟨8, true, false, [24826, 24824, 90351], []⟩,
        ⟨59994, true, false, [24826, 24824], [1, 1]⟩,
        ⟨59994, true, false, [24826, 24824], [1, 1]⟩,
        ⟨60105, true, false, [24826, 24824], [1, 1]⟩,
        ⟨562, false, false, [24826, 24824, 90353], [1]⟩,
        ⟨563, false, false, [24826, 24824, 90353], [1]⟩,
        ⟨60106, false, false, [24826, 24824], [11, 1]⟩,
        ⟨42112, false, false, [24826, 24824, 24821], [1]⟩,
        ⟨60107, true, false, [24826, 24824], [87023, 1]⟩,
        ⟨39944, false, false, [24826], [1]⟩,
        ⟨13, true, false, [24826, 24824], [24825, 87023, 1]⟩,
        ⟨39755, false, false, [24826], []⟩,
        ⟨39772, false, false, [24826], []⟩,
        ⟨39760, false, false, [24826], []⟩,
        ⟨39760, false, false, [24826], []⟩,
        ⟨60109, true, false, [], [87025]⟩
      ]⟩,
    ⟨[24824], [24824], .contexts []⟩,
    ⟨[24827], [24824], .contexts [
        ⟨60108, false, false, [], []⟩,
        ⟨60111, false, false, [], []⟩,
        ⟨60111, false, false, [], []⟩
      ]⟩,
    ⟨[87025, 9], [24827, 90349], .contexts [
        ⟨60110, true, false, [24824], [9]⟩,
        ⟨59991, false, false, [24824], []⟩,
        ⟨59998, false, false, [24824], []⟩,
        ⟨60112, true, false, [], [90349]⟩
      ]⟩,
    ⟨[87025, 11], [24827, 90353], .contexts [
        ⟨60110, true, false, [24824], [11]⟩,
        ⟨59993, false, false, [24824], []⟩,
        ⟨59996, false, false, [24824], []⟩,
        ⟨60112, true, false, [], [90353]⟩
      ]⟩,
    ⟨[24825, 87025], [24825, 87025], .contexts []⟩,
    ⟨[90351], [24825, 87025], .contexts [
        ⟨60110, false, false, [], []⟩,
        ⟨60115, false, false, [], []⟩
      ]⟩,
    ⟨[90353, 11], [24825, 87025], .contexts [
        ⟨60105, false, false, [], []⟩,
        ⟨60116, false, false, [], []⟩,
        ⟨60115, false, false, [], []⟩,
        ⟨60115, false, false, [], []⟩
      ]⟩,
    ⟨[24829], [24825, 19665], .source 12479⟩,
    ⟨[90353], [90353], .contexts []⟩,
    ⟨[90353], [90353], .contexts []⟩,
    ⟨[24831], [24828], .source 12480⟩,
    ⟨[24828], [24828], .contexts []⟩,
    ⟨[84953, 5], [24831, 90353], .contexts [
        ⟨29332, true, false, [], [5]⟩,
        ⟨60118, false, false, [24828], [84955, 11, 5]⟩,
        ⟨39922, true, false, [24828, 24825], [11, 5]⟩,
        ⟨60117, true, false, [24828], [5, 11, 5]⟩,
        ⟨681, false, false, [24828, 90353], []⟩,
        ⟨60119, false, false, [24828], []⟩,
        ⟨60120, false, false, [24828], []⟩,
        ⟨60122, true, false, [], [90353]⟩,
        ⟨60122, true, false, [], [90353]⟩,
        ⟨60121, true, false, [], [90353]⟩
      ]⟩,
    ⟨[24833], [24825, 19649], .source 12481⟩,
    ⟨[24835], [24833, 24363], .source 12482⟩,
    ⟨[24837], [24834], .source 12483⟩,
    ⟨[24834], [24834], .contexts []⟩,
    ⟨[24821, 85361], [24821, 85361], .contexts []⟩,
    ⟨[24821, 85361], [24821, 85361], .contexts []⟩,
    ⟨[24820], [24820], .contexts []⟩,
    ⟨[85361, 15], [24823, 90353], .contexts [
        ⟨60129, true, false, [24820], [15]⟩,
        ⟨60128, true, false, [24820], [15]⟩,
        ⟨31801, true, false, [], [15]⟩,
        ⟨31782, true, false, [], [1, 15]⟩,
        ⟨60106, true, false, [24820], [15, 1, 15]⟩,
        ⟨2185, false, false, [24820, 90353], []⟩,
        ⟨60119, false, false, [24820], []⟩,
        ⟨60120, false, false, [24820], []⟩,
        ⟨60130, true, false, [], [90353]⟩,
        ⟨60130, true, false, [], [90353]⟩,
        ⟨60103, true, false, [], [90353]⟩
      ]⟩,
    ⟨[90353, 15], [24821, 85361], .contexts [
        ⟨60131, true, false, [24822], [15]⟩,
        ⟨1, false, false, [24822, 85361], []⟩,
        ⟨60103, false, true, [], [85361]⟩
      ]⟩,
    ⟨[24839], [19685, 24827], .source 12484⟩,
    ⟨[24839, 90347], [24839, 90347], .contexts []⟩,
    ⟨[24839, 90347, 9], [87025], .contexts [
        ⟨60134, true, false, [], [9]⟩,
        ⟨59988, true, false, [24839], [9]⟩,
        ⟨60133, false, false, [], [90349, 1, 9]⟩,
        ⟨60113, true, false, [19685], [1, 9]⟩,
        ⟨39755, true, false, [19685], [9, 1, 9]⟩,
        ⟨39962, true, false, [], [1, 9, 1, 9]⟩,
        ⟨39962, true, false, [], [1, 9, 1, 9]⟩,
        ⟨39961, true, false, [], [1, 9, 1, 9]⟩,
        ⟨39960, true, false, [], [1, 9, 1, 9]⟩,
        ⟨41137, true, false, [], [9, 1, 9, 1, 9]⟩,
        ⟨4283, false, false, [87025], []⟩,
        ⟨41140, false, false, [], []⟩
      ]⟩,
    ⟨[24841], [24838], .source 12485⟩,
    ⟨[24838], [24838], .contexts []⟩,
    ⟨[90347, 9], [24841, 87025], .contexts [
        ⟨60135, false, false, [24838], []⟩,
        ⟨39917, false, false, [24838], []⟩,
        ⟨60137, true, false, [], [87025]⟩,
        ⟨60137, true, false, [], [87025]⟩,
        ⟨60136, true, false, [], [87025]⟩
      ]⟩,
    ⟨[87025, 9], [24827, 90349], .contexts [
        ⟨60113, false, false, [], []⟩
      ]⟩,
    ⟨[24827, 90349], [24827, 90349], .contexts []⟩,
    ⟨[24843], [24825, 24839], .source 12486⟩,
    ⟨[24845], [19649, 20523], .source 12487⟩,
    ⟨[90349], [24843, 90347], .contexts [
        ⟨60140, true, false, [24826], []⟩,
        ⟨60140, true, false, [24826], []⟩,
        ⟨60139, true, false, [24826], []⟩,
        ⟨60138, true, false, [24826, 24840], [9]⟩,
        ⟨46, false, false, [24826, 24840, 90347], []⟩,
        ⟨60136, false, true, [24826], [90347]⟩,
        ⟨60134, false, false, [24826], []⟩,
        ⟨60109, true, false, [], [24839, 90347]⟩,
        ⟨60141, true, false, [], [90347]⟩
      ]⟩,
    ⟨[24843, 90347], [24843, 90347], .contexts []⟩,
    ⟨[90349], [24843, 90347], .contexts [
        ⟨60143, false, false, [], []⟩,
        ⟨60144, false, false, [], []⟩
      ]⟩,
    ⟨[24827, 90349], [24827, 24843, 90347], .contexts [
        ⟨60145, false, false, [24827], []⟩
      ]⟩,
    ⟨[24847], [24827, 24843], .source 12488⟩,
    ⟨[87025, 9], [24847, 90347], .contexts [
        ⟨60139, false, false, [], []⟩,
        ⟨60146, false, false, [], []⟩,
        ⟨60147, true, false, [], [90347]⟩
      ]⟩,
    ⟨[90347], [90347], .contexts []⟩,
    ⟨[24849], [24844], .source 12489⟩,
    ⟨[24851], [24849, 24847], .source 12490⟩,
    ⟨[83623, 13], [24851, 90347], .contexts [
        ⟨60142, false, false, [24844], [83623, 13]⟩,
        ⟨42148, true, false, [24844, 19649], [13]⟩,
        ⟨41157, true, false, [24844], [9, 13]⟩,
        ⟨942, false, false, [24844, 87025], []⟩,
        ⟨47, false, false, [24844, 87025], []⟩,
        ⟨60148, false, false, [24844], []⟩,
        ⟨60149, false, false, [24844, 24847], []⟩,
        ⟨60150, true, false, [], [24847, 90347]⟩,
        ⟨60151, true, false, [], [90347]⟩
      ]⟩,
    ⟨[24853], [24850], .source 12491⟩,
    ⟨[90347, 13], [24853, 83623], .contexts [
        ⟨60152, true, false, [24850], [13]⟩,
        ⟨59, false, false, [24850, 83623], []⟩,
        ⟨60153, true, false, [], [83623]⟩
      ]⟩,
    ⟨[19665, 84955], [19665, 84955], .contexts []⟩,
    ⟨[84955, 9], [84955, 9], .contexts []⟩,
    ⟨[90345], [90345], .contexts []⟩,
    ⟨[24855], [19663, 24847], .source 12492⟩,
    ⟨[84955, 9], [24855, 90345], .contexts [
        ⟨60156, false, false, [], []⟩,
        ⟨60155, true, false, [19664], [9]⟩,
        ⟨60155, true, false, [19664], [9]⟩,
        ⟨39922, true, false, [19664], [9]⟩,
        ⟨1265, false, false, [19664, 87025], []⟩,
        ⟨1266, false, false, [19664, 87025], []⟩,
        ⟨60148, false, false, [19664], [5]⟩,
        ⟨59984, false, false, [19664, 24847], []⟩,
        ⟨60157, false, false, [19664, 24847], []⟩,
        ⟨39930, true, false, [], [24847, 90345]⟩,
        ⟨60158, true, false, [], [90345]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 940. -/
def y322TCIndexRaw940 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[24857], [24854], .source 12493⟩,
    ⟨[90347, 5], [90345], .contexts [
        ⟨60000, false, false, [], []⟩,
        ⟨60001, false, false, [], []⟩,
        ⟨59983, false, false, [], []⟩,
        ⟨59983, false, false, [], []⟩
      ]⟩,
    ⟨[90347, 1], [24843, 90347], .contexts [
        ⟨59986, false, false, [], []⟩,
        ⟨60145, false, false, [], []⟩,
        ⟨60144, false, false, [], []⟩,
        ⟨60144, false, false, [], []⟩
      ]⟩,
    ⟨[24853, 83623], [24853, 83623], .contexts []⟩,
    ⟨[24853, 83623], [24853, 83623], .contexts []⟩,
    ⟨[24859], [24853, 20445], .source 12494⟩,
    ⟨[90345, 13], [24859, 83631], .contexts [
        ⟨60161, true, false, [], [13]⟩,
        ⟨179, false, false, [90347], []⟩,
        ⟨180, false, false, [90347], []⟩,
        ⟨60154, false, false, [], [5]⟩,
        ⟨60163, false, false, [], [5]⟩,
        ⟨60164, false, false, [], [5]⟩,
        ⟨60164, false, false, [], [5]⟩,
        ⟨42023, false, false, [24853], []⟩,
        ⟨60165, true, false, [], [83631]⟩,
        ⟨22482, false, false, [24859], []⟩,
        ⟨13, true, false, [], [24859, 83631]⟩
      ]⟩,
    ⟨[24861], [24858], .source 12495⟩,
    ⟨[83631, 13], [24861, 90345], .contexts [
        ⟨60166, true, false, [24858], [13]⟩,
        ⟨59, false, false, [24858, 90345], []⟩,
        ⟨60167, true, false, [], [90345]⟩
      ]⟩,
    ⟨[84955, 9], [24855, 90345], .contexts [
        ⟨60156, false, false, [], []⟩,
        ⟨60159, false, false, [], []⟩
      ]⟩,
    ⟨[24855, 90345], [24855, 90345], .contexts []⟩,
    ⟨[84955, 9], [24855, 90345], .contexts [
        ⟨60169, false, false, [], []⟩,
        ⟨60170, false, false, [], []⟩,
        ⟨60170, false, false, [], []⟩
      ]⟩,
    ⟨[24863], [24857, 17801], .source 12496⟩,
    ⟨[24865], [24862], .source 12497⟩,
    ⟨[24867], [24857, 24865], .source 12498⟩,
    ⟨[90345], [24867, 90343], .contexts [
        ⟨60171, true, false, [24854], []⟩,
        ⟨60172, false, false, [24854, 24862], [84955, 9]⟩,
        ⟨60160, false, false, [24854, 24862], [17801, 84955, 9]⟩,
        ⟨29459, true, false, [24854, 24862, 24854, 17801], [9]⟩,
        ⟨29483, true, false, [24854, 24862, 24854], [9]⟩,
        ⟨21, true, false, [24854, 24862, 24854, 84955], [9]⟩,
        ⟨479, true, false, [24854, 24862, 24854, 84955], [9]⟩,
        ⟨60171, false, false, [24854, 24862, 24854], [3, 9, 9]⟩,
        ⟨59980, false, false, [24854, 24862], [9, 9]⟩,
        ⟨46, false, false, [24854, 24862, 90343], []⟩,
        ⟨60173, true, false, [24854], [90343]⟩,
        ⟨60160, true, false, [], [24865, 90343]⟩,
        ⟨60174, true, false, [], [90343]⟩
      ]⟩,
    ⟨[24869], [24866], .source 12499⟩,
    ⟨[24866], [24866], .contexts []⟩,
    ⟨[90345], [24867, 90343], .contexts [
        ⟨60175, false, false, [], []⟩
      ]⟩,
    ⟨[90345], [24867, 90343], .contexts [
        ⟨60178, false, false, [], []⟩
      ]⟩,
    ⟨[24871], [24869, 24859], .source 12500⟩,
    ⟨[24873], [24843, 24867], .source 12501⟩,
    ⟨[24875], [24869, 24873], .source 12502⟩,
    ⟨[24877], [24874], .source 12503⟩,
    ⟨[90343], [24877, 90341], .contexts [
        ⟨60182, false, false, [24874], [90343]⟩,
        ⟨60176, false, false, [24874], [24873, 90343]⟩,
        ⟨60181, false, false, [24874, 24866], [90343]⟩,
        ⟨60179, true, false, [24874, 24866, 24843], []⟩,
        ⟨13, false, false, [24874, 24866], [24843, 90345]⟩,
        ⟨60157, true, false, [24874, 24866, 24843], []⟩,
        ⟨59984, true, false, [24874, 24866, 24843], []⟩,
        ⟨60162, true, false, [24874, 24866], [5]⟩,
        ⟨162, true, false, [24874, 24866, 90347], []⟩,
        ⟨161, true, false, [24874, 24866, 90347], []⟩,
        ⟨60161, false, false, [24874, 24866], [1]⟩,
        ⟨60179, false, false, [24874, 24866], [1]⟩,
        ⟨59976, false, false, [24874], []⟩,
        ⟨60183, true, false, [], [90341]⟩
      ]⟩,
    ⟨[24867, 90343], [24867, 24877, 90341], .contexts [
        ⟨60184, false, false, [24867], []⟩
      ]⟩,
    ⟨[24879], [24867, 24877], .source 12504⟩,
    ⟨[90345], [24879, 90341], .contexts [
        ⟨60179, false, false, [], []⟩,
        ⟨60185, false, false, [], []⟩,
        ⟨60186, true, false, [], [90341]⟩
      ]⟩,
    ⟨[24875], [24876], .contexts [
        ⟨60183, true, true, [], []⟩
      ]⟩,
    ⟨[24875], [24876], .contexts [
        ⟨60188, false, false, [], []⟩
      ]⟩,
    ⟨[24876], [24876], .contexts []⟩,
    ⟨[24881], [24875, 24879], .source 12505⟩,
    ⟨[24885], [24875, 24869], .source 12507⟩,
    ⟨[90341, 5], [24885, 90347], .contexts [
        ⟨60184, true, false, [24876], [5]⟩,
        ⟨60175, true, false, [24876, 24866], [5]⟩,
        ⟨59982, false, false, [24876, 24866], []⟩,
        ⟨59999, false, false, [24876, 24866], []⟩,
        ⟨60177, true, false, [24876], [90347]⟩,
        ⟨60177, true, false, [24876], [90347]⟩,
        ⟨60176, true, false, [24876], [90347]⟩,
        ⟨60188, true, false, [], [24869, 90347]⟩,
        ⟨60192, true, false, [], [90347]⟩
      ]⟩,
    ⟨[24887], [24875, 24871], .source 12508⟩,
    ⟨[24889], [24855, 24879], .source 12509⟩,
    ⟨[84955, 9], [24889, 90341], .contexts [
        ⟨60169, false, false, [], []⟩,
        ⟨60187, false, false, [24855], []⟩,
        ⟨60195, true, false, [], [90341]⟩
      ]⟩,
    ⟨[24891], [17805, 24889], .source 12510⟩,
    ⟨[90341, 7], [90341, 7], .contexts []⟩,
    ⟨[90341], [90341], .contexts []⟩,
    ⟨[24893], [24888], .source 12511⟩,
    ⟨[24893], [24888], .contexts [
        ⟨60200, false, false, [], []⟩
      ]⟩,
    ⟨[24895], [24893, 24891], .source 12512⟩,
    ⟨[90339, 9], [90339, 9], .contexts []⟩,
    ⟨[24897], [24893, 18501], .source 12513⟩,
    ⟨[90339, 9], [24897, 85833], .contexts [
        ⟨60203, false, false, [], []⟩,
        ⟨59972, true, false, [], [9]⟩,
        ⟨60196, true, false, [24888], [15, 9]⟩,
        ⟨935, false, false, [24888, 84955], []⟩,
        ⟨33784, false, false, [24888], []⟩,
        ⟨33776, false, false, [24888], []⟩,
        ⟨33785, false, false, [24888, 18501], []⟩,
        ⟨60201, true, false, [], [18501, 85833]⟩,
        ⟨60204, true, false, [], [85833]⟩
      ]⟩,
    ⟨[24899], [24896], .source 12514⟩,
    ⟨[85833, 9], [24899, 90339], .contexts [
        ⟨60205, true, false, [24896], [9]⟩,
        ⟨46, false, false, [24896, 90339], []⟩,
        ⟨60206, true, false, [], [90339]⟩
      ]⟩,
    ⟨[24877, 90341], [24877, 90341], .contexts []⟩,
    ⟨[90341, 15], [90339], .contexts [
        ⟨60004, false, false, [], []⟩,
        ⟨60005, false, false, [], []⟩,
        ⟨59971, false, false, [], []⟩,
        ⟨59971, false, false, [], []⟩
      ]⟩,
    ⟨[90341, 14], [90341, 15], .contexts [
        ⟨10, false, false, [90341], []⟩
      ]⟩,
    ⟨[90339, 1], [90339, 1], .contexts []⟩,
    ⟨[90339], [90339], .contexts []⟩,
    ⟨[24875], [24876], .contexts [
        ⟨60189, false, false, [], []⟩,
        ⟨60190, false, false, [], []⟩,
        ⟨60190, false, false, [], []⟩
      ]⟩,
    ⟨[90339, 1], [24875, 90339], .contexts [
        ⟨60211, false, false, [], []⟩,
        ⟨59972, true, false, [], [1]⟩,
        ⟨60208, true, false, [24876], [15, 1]⟩,
        ⟨60208, true, false, [24876], [15, 1]⟩,
        ⟨60208, true, false, [24876], [15, 1]⟩,
        ⟨60184, true, false, [24876], [15, 1]⟩,
        ⟨59974, true, false, [24876], [15, 1]⟩,
        ⟨3040, false, false, [24876, 90341], []⟩,
        ⟨60210, false, false, [24876], []⟩,
        ⟨60209, false, false, [24876], []⟩,
        ⟨60212, false, false, [24876], []⟩,
        ⟨60213, true, false, [], [90339]⟩
      ]⟩,
    ⟨[24887, 83631], [24887, 83631], .contexts []⟩,
    ⟨[90341, 13], [24887, 83631], .contexts [
        ⟨60184, true, false, [24876], [13]⟩,
        ⟨60175, true, false, [24876, 24866], [13]⟩,
        ⟨60166, false, false, [24876, 24866], []⟩,
        ⟨60176, true, false, [24876], [24859, 83631]⟩,
        ⟨60180, true, false, [24876], [83631]⟩,
        ⟨60188, true, false, [], [24871, 83631]⟩,
        ⟨60194, true, false, [], [83631]⟩,
        ⟨60215, false, false, [], []⟩,
        ⟨60215, false, false, [], []⟩
      ]⟩,
    ⟨[24887, 89315], [24887, 89315], .contexts []⟩,
    ⟨[24887, 89315], [24887, 89315], .contexts []⟩,
    ⟨[24901], [24886], .source 12515⟩,
    ⟨[24901], [24886], .contexts [
        ⟨60219, false, false, [], []⟩
      ]⟩,
    ⟨[24886], [24886], .contexts []⟩,
    ⟨[90341, 11], [24887, 89315], .contexts [
        ⟨60220, false, false, [24900], [90341, 11]⟩,
        ⟨60221, false, false, [24900], [90341, 11]⟩,
        ⟨60221, false, false, [24900], [90341, 11]⟩,
        ⟨60199, true, false, [24900, 24886], [11]⟩,
        ⟨4838, true, false, [24900, 24886, 90341], [11]⟩,
        ⟨60216, false, false, [24900, 24886], [11, 13, 11, 11]⟩,
        ⟨55536, false, false, [24900], [13, 11, 11]⟩,
        ⟨55544, false, false, [24900], [11, 11]⟩,
        ⟨60217, false, false, [24900, 24886], [11, 11]⟩,
        ⟨60218, false, false, [24900, 24886], [11, 11]⟩,
        ⟨53, false, false, [24900, 89315], []⟩,
        ⟨60219, false, true, [], [89315]⟩
      ]⟩,
    ⟨[24903], [24887, 20345], .source 12516⟩]

/-- Exact literal claimed equations and contextual derivations, block 941. -/
def y322TCIndexRaw941 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[24903, 84829], [24903, 84829], .contexts []⟩,
    ⟨[84829, 15], [84829, 15], .contexts []⟩,
    ⟨[90337], [90337], .contexts []⟩,
    ⟨[24905], [24902], .source 12517⟩,
    ⟨[24902], [24902], .contexts []⟩,
    ⟨[24905], [24902], .contexts [
        ⟨60227, false, false, [], []⟩,
        ⟨60228, false, false, [], []⟩,
        ⟨60228, false, false, [], []⟩
      ]⟩,
    ⟨[84829, 15], [24905, 90337], .contexts [
        ⟨60225, false, false, [], []⟩,
        ⟨60224, true, false, [24902], [15]⟩,
        ⟨28682, true, false, [], [15]⟩,
        ⟨60223, false, false, [24902], [84831, 13, 15]⟩,
        ⟨41882, true, false, [24902, 24887], [13, 15]⟩,
        ⟨60216, true, false, [24902], [15, 13, 15]⟩,
        ⟨2022, false, false, [24902, 90341], []⟩,
        ⟨89, false, false, [24902, 90341], []⟩,
        ⟨60209, false, false, [24902], [13]⟩,
        ⟨60006, false, false, [24902], []⟩,
        ⟨60007, false, false, [24902], []⟩,
        ⟨59967, false, false, [24902], []⟩,
        ⟨59967, false, false, [24902], []⟩,
        ⟨60226, false, false, [24902], []⟩,
        ⟨60229, true, false, [], [90337]⟩
      ]⟩,
    ⟨[24903], [24904], .contexts [
        ⟨60227, true, true, [], []⟩
      ]⟩,
    ⟨[90337, 15], [24903, 84829], .contexts [
        ⟨60230, true, false, [24904], [15]⟩,
        ⟨1, false, false, [24904, 84829], []⟩,
        ⟨60231, true, false, [], [84829]⟩
      ]⟩,
    ⟨[24881, 90341], [24881, 90341], .contexts []⟩,
    ⟨[90339, 3], [90339, 3], .contexts []⟩,
    ⟨[90339, 3], [24880, 90339], .contexts [
        ⟨60234, false, false, [], []⟩,
        ⟨59972, true, false, [], [3]⟩,
        ⟨60233, true, false, [24880], [15, 3]⟩,
        ⟨60233, true, false, [24880], [15, 3]⟩,
        ⟨60191, false, false, [24880], [90341, 15, 3]⟩,
        ⟨60189, false, false, [24880], [24879, 90341, 15, 3]⟩,
        ⟨60190, false, false, [24880], [24879, 90341, 15, 3]⟩,
        ⟨60187, true, false, [24880, 24876], [15, 3]⟩,
        ⟨59978, true, false, [24880, 24876], [15, 3]⟩,
        ⟨60184, false, false, [24880, 24876], [3, 15, 3]⟩,
        ⟨499, false, false, [24880, 90341], []⟩,
        ⟨60210, false, false, [24880], []⟩,
        ⟨60209, false, false, [24880], []⟩
      ]⟩,
    ⟨[24907], [24880], .source 12518⟩,
    ⟨[24880], [24880], .contexts []⟩,
    ⟨[90339, 3], [24907, 90339], .contexts [
        ⟨60235, false, false, [], []⟩,
        ⟨60212, false, false, [24880], []⟩,
        ⟨60237, true, false, [], [90339]⟩,
        ⟨60237, true, false, [], [90339]⟩,
        ⟨60236, true, false, [], [90339]⟩
      ]⟩,
    ⟨[24895, 90341], [24895, 90341], .contexts []⟩,
    ⟨[24895, 90339], [24895, 90339], .contexts []⟩,
    ⟨[90339, 7], [24895, 90339], .contexts [
        ⟨60209, true, false, [], [7]⟩,
        ⟨37, false, false, [90341], []⟩,
        ⟨40, false, false, [90341], []⟩,
        ⟨60198, false, false, [], [15]⟩,
        ⟨60198, false, false, [], [15]⟩,
        ⟨60196, true, false, [24888], [7, 15]⟩,
        ⟨1084, false, false, [24888, 84955], [15]⟩,
        ⟨1085, false, false, [24888, 84955], [15]⟩,
        ⟨29486, false, false, [24888], [9, 15]⟩,
        ⟨60159, false, false, [24888, 17805], [15]⟩,
        ⟨60187, false, false, [24888, 17805, 24855], [15]⟩,
        ⟨60195, true, false, [24888, 17805], [90341, 15]⟩,
        ⟨60197, true, false, [24888], [90341, 15]⟩,
        ⟨60199, false, false, [24888, 24891], [15]⟩,
        ⟨60201, true, false, [], [24891, 90341, 15]⟩,
        ⟨60202, true, false, [], [90341, 15]⟩,
        ⟨60239, false, false, [], [15]⟩,
        ⟨60239, false, false, [], [15]⟩,
        ⟨59972, false, false, [24895], []⟩,
        ⟨60240, false, false, [], []⟩
      ]⟩,
    ⟨[24887, 89317], [24887, 89317], .contexts []⟩,
    ⟨[24887, 89317], [24887, 89317], .contexts []⟩,
    ⟨[90339, 11], [90339, 11], .contexts []⟩,
    ⟨[24887], [24887], .contexts []⟩,
    ⟨[24887], [24887], .contexts []⟩,
    ⟨[90339, 11], [24887, 89317], .contexts [
        ⟨60244, false, false, [], []⟩,
        ⟨60209, true, false, [], [11]⟩,
        ⟨52, false, false, [90341], []⟩,
        ⟨55, false, false, [90341], []⟩,
        ⟨60222, false, false, [], [15]⟩,
        ⟨60217, false, false, [], [15]⟩,
        ⟨60218, false, false, [], [15]⟩,
        ⟨60218, false, false, [], [15]⟩,
        ⟨55563, false, false, [24887], []⟩,
        ⟨60242, false, false, [], []⟩,
        ⟨60243, false, false, [], []⟩,
        ⟨55572, false, false, [24887], []⟩,
        ⟨60246, true, false, [], [89317]⟩,
        ⟨60245, true, false, [], [89317]⟩,
        ⟨13, true, false, [], [24887, 89317]⟩
      ]⟩,
    ⟨[89317, 11], [24901, 90339], .contexts [
        ⟨60247, true, false, [24886], [11]⟩,
        ⟨53, false, false, [24886, 90339], []⟩,
        ⟨60219, true, false, [], [90339]⟩
      ]⟩,
    ⟨[24897, 85833], [24897, 85833], .contexts []⟩,
    ⟨[24897, 85833], [24897, 85833], .contexts []⟩,
    ⟨[24897, 85831], [24897, 85831], .contexts []⟩,
    ⟨[90339, 13], [90337], .contexts [
        ⟨60006, false, false, [], []⟩,
        ⟨60007, false, false, [], []⟩,
        ⟨59967, false, false, [], []⟩,
        ⟨59967, false, false, [], []⟩
      ]⟩,
    ⟨[24896], [24896], .contexts []⟩,
    ⟨[85831, 9], [24899, 90337], .contexts [
        ⟨60251, true, false, [24896], [9]⟩,
        ⟨33545, true, false, [], [9]⟩,
        ⟨60250, true, false, [24896], [13, 9]⟩,
        ⟨60250, true, false, [24896], [13, 9]⟩,
        ⟨60249, true, false, [24896], [13, 9]⟩,
        ⟨60205, true, false, [24896], [13, 9]⟩,
        ⟨60203, true, false, [24896], [13, 9]⟩,
        ⟨511, false, false, [24896, 90339], []⟩,
        ⟨64, false, false, [24896, 90339], []⟩,
        ⟨60252, false, false, [24896], []⟩,
        ⟨60226, false, false, [24896], []⟩,
        ⟨60253, true, false, [], [90337]⟩,
        ⟨60253, true, false, [], [90337]⟩,
        ⟨60206, true, false, [], [90337]⟩
      ]⟩,
    ⟨[24875, 90339], [24875, 90339], .contexts []⟩,
    ⟨[24875, 90339], [24875, 90339], .contexts []⟩,
    ⟨[90335, 13], [90335, 13], .contexts []⟩,
    ⟨[90335], [90335], .contexts []⟩,
    ⟨[24874], [24874], .contexts []⟩,
    ⟨[24877], [24874], .contexts [
        ⟨60183, false, false, [], []⟩,
        ⟨60259, false, false, [], []⟩,
        ⟨60259, false, false, [], []⟩
      ]⟩,
    ⟨[90335, 13], [24877, 90335], .contexts [
        ⟨60257, false, false, [], []⟩,
        ⟨59964, true, false, [], [13]⟩,
        ⟨59968, true, false, [], [1, 13]⟩,
        ⟨60256, true, false, [24874], [13, 1, 13]⟩,
        ⟨60256, true, false, [24874], [13, 1, 13]⟩,
        ⟨60255, true, false, [24874], [13, 1, 13]⟩,
        ⟨60214, true, false, [24874], [13, 1, 13]⟩,
        ⟨60211, true, false, [24874], [13, 1, 13]⟩,
        ⟨919, false, false, [24874, 90339], []⟩,
        ⟨116, false, false, [24874, 90339], []⟩,
        ⟨60252, false, false, [24874], [1]⟩,
        ⟨60008, false, false, [24874], []⟩,
        ⟨60009, false, false, [24874], []⟩,
        ⟨59963, false, false, [24874], []⟩,
        ⟨59963, false, false, [24874], []⟩,
        ⟨60258, false, false, [24874], []⟩,
        ⟨60260, true, false, [], [90335]⟩
      ]⟩,
    ⟨[24905, 90337], [24905, 90337], .contexts []⟩,
    ⟨[24905, 90337], [24905, 90337], .contexts []⟩,
    ⟨[84829, 15], [24905, 90337], .contexts [
        ⟨60225, false, false, [], []⟩,
        ⟨60230, false, false, [], []⟩,
        ⟨60262, false, false, [], []⟩,
        ⟨60263, false, false, [], []⟩,
        ⟨60263, false, false, [], []⟩
      ]⟩,
    ⟨[24905, 90335], [24905, 90335], .contexts []⟩,
    ⟨[90335, 15], [90335, 15], .contexts []⟩,
    ⟨[24903], [24904], .contexts [
        ⟨60231, false, false, [], []⟩
      ]⟩,
    ⟨[24904], [24904], .contexts []⟩,
    ⟨[24903], [24904], .contexts [
        ⟨60267, false, false, [], []⟩,
        ⟨60268, false, false, [], []⟩,
        ⟨60268, false, false, [], []⟩
      ]⟩,
    ⟨[90335, 15], [24903, 84827], .contexts [
        ⟨60266, false, false, [], []⟩,
        ⟨60265, true, false, [24904], [15]⟩,
        ⟨59964, true, false, [], [15]⟩,
        ⟨60264, true, false, [24904], [1, 15]⟩,
        ⟨1666, false, false, [24904, 84829], []⟩,
        ⟨29159, false, false, [24904], []⟩,
        ⟨29158, false, false, [24904], []⟩,
        ⟨29161, false, false, [24904], []⟩,
        ⟨60269, true, false, [], [84827]⟩
      ]⟩,
    ⟨[84827, 15], [24905, 90335], .contexts [
        ⟨60270, true, false, [24902], [15]⟩,
        ⟨1, false, false, [24902, 90335], []⟩,
        ⟨60227, true, false, [], [90335]⟩
      ]⟩,
    ⟨[17731, 84829], [17731, 84829], .contexts []⟩,
    ⟨[17731, 84829], [17731, 84829], .contexts []⟩,
    ⟨[24909], [17731, 24905], .source 12519⟩,
    ⟨[24911], [24903, 24909], .source 12520⟩,
    ⟨[24913], [17715, 24905], .source 12521⟩,
    ⟨[24915], [24903, 24913], .source 12522⟩,
    ⟨[24877, 90335], [24877, 90335], .contexts []⟩,
    ⟨[24877, 90335], [24877, 90335], .contexts []⟩,
    ⟨[90335, 11], [90333], .contexts [
        ⟨60010, false, false, [], []⟩,
        ⟨60011, false, false, [], []⟩,
        ⟨59959, false, false, [], []⟩,
        ⟨59959, false, false, [], []⟩
      ]⟩,
    ⟨[90335, 10], [90335, 11], .contexts [
        ⟨54, false, false, [90335], []⟩
      ]⟩,
    ⟨[90333, 13], [90333, 13], .contexts []⟩,
    ⟨[90333], [90333], .contexts []⟩,
    ⟨[90333, 13], [24875, 90333], .contexts [
        ⟨60282, false, false, [], []⟩,
        ⟨59960, true, false, [], [13]⟩,
        ⟨60279, true, false, [24876], [11, 13]⟩,
        ⟨60279, true, false, [24876], [11, 13]⟩,
        ⟨60278, true, false, [24876], [11, 13]⟩,
        ⟨60261, true, false, [24876], [11, 13]⟩,
        ⟨60257, true, false, [24876], [11, 13]⟩,
        ⟨931, false, false, [24876, 90335], []⟩,
        ⟨60281, false, false, [24876], []⟩,
        ⟨60280, false, false, [24876], []⟩,
        ⟨60283, false, false, [24876], []⟩,
        ⟨60213, true, false, [], [90333]⟩
      ]⟩,
    ⟨[24903, 84827], [24903, 84827], .contexts []⟩,
    ⟨[24903, 84827], [24903, 84827], .contexts []⟩,
    ⟨[90335, 15], [24903, 84827], .contexts [
        ⟨60266, false, false, [], []⟩,
        ⟨60270, false, false, [], []⟩,
        ⟨60285, false, false, [], []⟩,
        ⟨60286, false, false, [], []⟩,
        ⟨60286, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 942. -/
def y322TCIndexRaw942 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[24917], [24903, 17729], .source 12523⟩,
    ⟨[24919], [24917, 24905], .source 12524⟩,
    ⟨[90335, 7], [90335, 7], .contexts []⟩,
    ⟨[24921], [24918], .source 12525⟩,
    ⟨[24918], [24918], .contexts []⟩,
    ⟨[24921], [24918], .contexts [
        ⟨60291, false, false, [], []⟩,
        ⟨60292, false, false, [], []⟩,
        ⟨60292, false, false, [], []⟩
      ]⟩,
    ⟨[90335, 7], [24921, 90335], .contexts [
        ⟨60290, false, false, [], []⟩,
        ⟨60289, false, false, [24918], [90335, 7]⟩,
        ⟨60271, true, false, [24918, 24917], [7]⟩,
        ⟨60288, false, false, [24918], [84827, 15, 7]⟩,
        ⟨29162, true, false, [24918, 24903], [15, 7]⟩,
        ⟨60287, true, false, [24918], [7, 15, 7]⟩,
        ⟨2651, false, false, [24918, 90335], []⟩,
        ⟨60258, false, false, [24918], []⟩,
        ⟨60293, true, false, [], [90335]⟩
      ]⟩,
    ⟨[24903, 84825], [24903, 84825], .contexts []⟩,
    ⟨[84825, 15], [84825, 15], .contexts []⟩,
    ⟨[84825, 15], [24905, 90333], .contexts [
        ⟨60296, false, false, [], []⟩,
        ⟨60295, true, false, [24902], [15]⟩,
        ⟨28674, true, false, [], [15]⟩,
        ⟨60287, true, false, [24902], [11, 15]⟩,
        ⟨2046, false, false, [24902, 90335], []⟩,
        ⟨60281, false, false, [24902], []⟩,
        ⟨60280, false, false, [24902], []⟩,
        ⟨60283, false, false, [24902], []⟩,
        ⟨60229, true, false, [], [90333]⟩
      ]⟩,
    ⟨[90333, 15], [24903, 84825], .contexts [
        ⟨60297, true, false, [24904], [15]⟩,
        ⟨1, false, false, [24904, 84825], []⟩,
        ⟨60231, true, false, [], [84825]⟩
      ]⟩,
    ⟨[24875, 90333], [24875, 90333], .contexts []⟩,
    ⟨[24875, 90333], [24875, 90333], .contexts []⟩,
    ⟨[90333, 13], [24875, 90333], .contexts [
        ⟨60282, false, false, [], []⟩,
        ⟨60284, false, false, [], []⟩,
        ⟨60299, false, false, [], []⟩,
        ⟨60300, false, false, [], []⟩,
        ⟨60300, false, false, [], []⟩
      ]⟩,
    ⟨[90333, 9], [90331], .contexts [
        ⟨60012, false, false, [], []⟩,
        ⟨60013, false, false, [], []⟩,
        ⟨59955, false, false, [], []⟩,
        ⟨59955, false, false, [], []⟩
      ]⟩,
    ⟨[90333, 8], [90333, 9], .contexts [
        ⟨47, false, false, [90333], []⟩
      ]⟩,
    ⟨[90331], [90331], .contexts []⟩,
    ⟨[24921, 90335], [24921, 90335], .contexts []⟩,
    ⟨[24921, 90335], [24921, 90335], .contexts []⟩,
    ⟨[90333, 7], [90333, 7], .contexts []⟩,
    ⟨[24920], [24920], .contexts []⟩,
    ⟨[24919], [24920], .contexts [
        ⟨60291, true, true, [], []⟩,
        ⟨60308, false, false, [], []⟩,
        ⟨60308, false, false, [], []⟩
      ]⟩,
    ⟨[90333, 7], [24919, 90333], .contexts [
        ⟨60307, false, false, [], []⟩,
        ⟨59960, true, false, [], [7]⟩,
        ⟨60306, true, false, [24920], [11, 7]⟩,
        ⟨60306, true, false, [24920], [11, 7]⟩,
        ⟨60305, true, false, [24920], [11, 7]⟩,
        ⟨60294, true, false, [24920], [11, 7]⟩,
        ⟨60290, true, false, [24920], [11, 7]⟩,
        ⟨555, false, false, [24920, 90335], []⟩,
        ⟨60281, false, false, [24920], []⟩,
        ⟨60280, false, false, [24920], []⟩,
        ⟨60283, false, false, [24920], []⟩,
        ⟨60309, true, false, [], [90333]⟩
      ]⟩,
    ⟨[24905, 90333], [24905, 90333], .contexts []⟩,
    ⟨[24905, 90333], [24905, 90333], .contexts []⟩,
    ⟨[84825, 15], [24905, 90333], .contexts [
        ⟨60296, false, false, [], []⟩,
        ⟨60297, false, false, [], []⟩,
        ⟨60311, false, false, [], []⟩,
        ⟨60312, false, false, [], []⟩,
        ⟨60312, false, false, [], []⟩
      ]⟩,
    ⟨[24923], [20527, 20717], .source 12526⟩,
    ⟨[90333, 5], [90333, 5], .contexts []⟩,
    ⟨[24925], [24903, 24923], .source 12527⟩,
    ⟨[90333, 5], [24925, 83239], .contexts [
        ⟨60315, false, false, [], []⟩,
        ⟨60313, true, false, [24904], [5]⟩,
        ⟨27, false, false, [24904, 84825], []⟩,
        ⟨30, false, false, [24904, 84825], []⟩,
        ⟨43177, false, false, [24904], [15]⟩,
        ⟨43435, false, false, [24904, 20527], []⟩,
        ⟨60314, true, false, [24904], [83239]⟩,
        ⟨43434, false, false, [24904, 24923], []⟩,
        ⟨60267, true, false, [], [24923, 83239]⟩,
        ⟨60316, true, false, [], [83239]⟩
      ]⟩,
    ⟨[24927], [24924], .source 12528⟩,
    ⟨[83239, 5], [24927, 90333], .contexts [
        ⟨60317, true, false, [24924], [5]⟩,
        ⟨28, false, false, [24924, 90333], []⟩,
        ⟨60318, true, false, [], [90333]⟩
      ]⟩,
    ⟨[90331, 15], [90331, 15], .contexts []⟩,
    ⟨[90331, 15], [24903, 84823], .contexts [
        ⟨60320, false, false, [], []⟩,
        ⟨59956, true, false, [], [15]⟩,
        ⟨60313, true, false, [24904], [9, 15]⟩,
        ⟨1671, false, false, [24904, 84825], []⟩,
        ⟨29173, false, false, [24904], []⟩,
        ⟨29172, false, false, [24904], []⟩,
        ⟨29175, false, false, [24904], []⟩,
        ⟨60269, true, false, [], [84823]⟩
      ]⟩,
    ⟨[24919, 90333], [24919, 90333], .contexts []⟩,
    ⟨[24919, 90333], [24919, 90333], .contexts []⟩,
    ⟨[90331, 7], [90331, 7], .contexts []⟩,
    ⟨[90331, 7], [24921, 90331], .contexts [
        ⟨60324, false, false, [], []⟩,
        ⟨59956, true, false, [], [7]⟩,
        ⟨60323, true, false, [24918], [9, 7]⟩,
        ⟨60323, true, false, [24918], [9, 7]⟩,
        ⟨60322, true, false, [24918], [9, 7]⟩,
        ⟨60310, true, false, [24918], [9, 7]⟩,
        ⟨60307, true, false, [24918], [9, 7]⟩,
        ⟨579, false, false, [24918, 90333], []⟩,
        ⟨60303, false, false, [24918], []⟩,
        ⟨60302, false, false, [24918], []⟩,
        ⟨60304, false, false, [24918], []⟩,
        ⟨60293, true, false, [], [90331]⟩
      ]⟩,
    ⟨[24925, 83239], [24925, 83239], .contexts []⟩,
    ⟨[24925, 83239], [24925, 83239], .contexts []⟩,
    ⟨[24929], [24875, 24925], .source 12529⟩,
    ⟨[83239, 13], [83239, 13], .contexts []⟩,
    ⟨[24931], [24927, 24929], .source 12530⟩,
    ⟨[83239, 13], [24931, 83239], .contexts [
        ⟨60329, false, false, [], []⟩,
        ⟨60327, true, false, [24924], [13]⟩,
        ⟨60327, true, false, [24924], [13]⟩,
        ⟨60326, true, false, [24924], [13]⟩,
        ⟨60317, true, false, [24924], [13]⟩,
        ⟨60315, true, false, [24924], [13]⟩,
        ⟨179, false, false, [24924, 90333], []⟩,
        ⟨180, false, false, [24924, 90333], []⟩,
        ⟨60301, false, false, [24924], [5]⟩,
        ⟨60317, false, false, [24924, 24875], []⟩,
        ⟨60328, true, false, [24924], [83239]⟩,
        ⟨43434, false, false, [24924, 24929], []⟩,
        ⟨60318, true, false, [], [24929, 83239]⟩,
        ⟨60330, true, false, [], [83239]⟩
      ]⟩,
    ⟨[24903, 84823], [24903, 84823], .contexts []⟩,
    ⟨[24903, 84823], [24903, 84823], .contexts []⟩,
    ⟨[24933], [24903, 20527], .source 12531⟩,
    ⟨[90331, 1], [90329], .contexts [
        ⟨60015, false, false, [], []⟩,
        ⟨60016, false, false, [], []⟩,
        ⟨59951, false, false, [], []⟩,
        ⟨59951, false, false, [], []⟩
      ]⟩,
    ⟨[90331, 0], [90331, 1], .contexts [
        ⟨9, false, false, [90331], []⟩
      ]⟩,
    ⟨[83609, 15], [83609, 15], .contexts []⟩,
    ⟨[90329], [90329], .contexts []⟩,
    ⟨[24935], [24932], .source 12532⟩,
    ⟨[24932], [24932], .contexts []⟩,
    ⟨[83609, 15], [24935, 90329], .contexts [
        ⟨60337, false, false, [], []⟩,
        ⟨60334, false, false, [24932], [83609, 15]⟩,
        ⟨43335, true, false, [24932, 24903], [15]⟩,
        ⟨28666, true, false, [24932, 24903], [15]⟩,
        ⟨60333, true, false, [24932], [1, 15]⟩,
        ⟨60333, true, false, [24932], [1, 15]⟩,
        ⟨60332, true, false, [24932], [1, 15]⟩,
        ⟨60321, true, false, [24932], [1, 15]⟩,
        ⟨60320, true, false, [24932], [1, 15]⟩,
        ⟨1666, false, false, [24932, 90331], []⟩,
        ⟨60336, false, false, [24932], []⟩,
        ⟨60335, false, false, [24932], []⟩,
        ⟨60338, false, false, [24932], []⟩,
        ⟨60340, true, false, [], [90329]⟩,
        ⟨60340, true, false, [], [90329]⟩,
        ⟨60339, true, false, [], [90329]⟩
      ]⟩,
    ⟨[24933], [24934], .contexts [
        ⟨60339, true, true, [], []⟩
      ]⟩,
    ⟨[24921, 90331], [24921, 90331], .contexts []⟩,
    ⟨[24931, 83239], [24931, 83239], .contexts []⟩,
    ⟨[24931, 83239], [24931, 83239], .contexts []⟩,
    ⟨[83241, 13], [83241, 13], .contexts []⟩,
    ⟨[24937], [24930], .source 12533⟩,
    ⟨[24930], [24930], .contexts []⟩,
    ⟨[83241, 13], [24937, 83241], .contexts [
        ⟨60346, false, false, [], []⟩,
        ⟨20197, true, false, [], [13]⟩,
        ⟨60345, true, false, [24930], [3, 13]⟩,
        ⟨60345, true, false, [24930], [3, 13]⟩,
        ⟨60344, true, false, [24930], [3, 13]⟩,
        ⟨60331, true, false, [24930], [3, 13]⟩,
        ⟨60329, true, false, [24930], [3, 13]⟩,
        ⟨1132, false, false, [24930, 83239], []⟩,
        ⟨21, false, false, [24930, 83239], []⟩,
        ⟨20197, false, false, [24930], []⟩,
        ⟨20445, false, false, [24930], []⟩,
        ⟨20202, false, false, [24930], []⟩,
        ⟨20202, false, false, [24930], []⟩,
        ⟨43512, false, false, [24930], []⟩,
        ⟨60348, true, false, [], [83241]⟩,
        ⟨60348, true, false, [], [83241]⟩,
        ⟨60347, true, false, [], [83241]⟩
      ]⟩,
    ⟨[24935, 90329], [24935, 90329], .contexts []⟩,
    ⟨[83609, 5], [83611], .contexts [
        ⟨22145, false, false, [], []⟩,
        ⟨22269, false, false, [], []⟩,
        ⟨22150, false, false, [], []⟩,
        ⟨22150, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 943. -/
def y322TCIndexRaw943 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83609, 4], [83609, 5], .contexts [
        ⟨29, false, false, [83609], []⟩
      ]⟩,
    ⟨[90327, 15], [90327, 15], .contexts []⟩,
    ⟨[83611], [83611], .contexts []⟩,
    ⟨[24934], [24934], .contexts []⟩,
    ⟨[90327, 15], [24933, 83611], .contexts [
        ⟨60353, false, false, [], []⟩,
        ⟨59948, true, false, [], [15]⟩,
        ⟨60350, true, false, [24934], [5, 15]⟩,
        ⟨60350, true, false, [24934], [5, 15]⟩,
        ⟨60341, true, false, [24934], [5, 15]⟩,
        ⟨60337, true, false, [24934], [5, 15]⟩,
        ⟨2072, false, false, [24934, 83609], []⟩,
        ⟨60352, false, false, [24934], []⟩,
        ⟨60351, false, false, [24934], []⟩,
        ⟨60354, false, false, [24934], []⟩,
        ⟨60355, true, false, [], [83611]⟩,
        ⟨60355, true, false, [], [83611]⟩,
        ⟨60342, true, false, [], [83611]⟩
      ]⟩,
    ⟨[24937, 83241], [24937, 83241], .contexts []⟩,
    ⟨[24937, 83241], [24937, 83241], .contexts []⟩,
    ⟨[83243, 13], [83243, 13], .contexts []⟩,
    ⟨[83243], [83243], .contexts []⟩,
    ⟨[24936], [24936], .contexts []⟩,
    ⟨[83243, 13], [24931, 83243], .contexts [
        ⟨60359, false, false, [], []⟩,
        ⟨20201, true, false, [], [13]⟩,
        ⟨60358, true, false, [24936], [5, 13]⟩,
        ⟨60358, true, false, [24936], [5, 13]⟩,
        ⟨60357, true, false, [24936], [5, 13]⟩,
        ⟨60349, true, false, [24936], [5, 13]⟩,
        ⟨60346, true, false, [24936], [5, 13]⟩,
        ⟨1136, false, false, [24936, 83241], []⟩,
        ⟨29, false, false, [24936, 83241], []⟩,
        ⟨43514, false, false, [24936], []⟩,
        ⟨60360, false, false, [24936], []⟩,
        ⟨60361, true, false, [], [83243]⟩,
        ⟨60361, true, false, [], [83243]⟩,
        ⟨60347, false, true, [], [83243]⟩
      ]⟩,
    ⟨[24933, 83611], [24933, 83611], .contexts []⟩,
    ⟨[24933, 83611], [24933, 83611], .contexts []⟩,
    ⟨[24939], [24933, 20525], .source 12534⟩,
    ⟨[84817, 15], [84817, 15], .contexts []⟩,
    ⟨[24941], [24938], .source 12535⟩,
    ⟨[24941], [24941], .contexts []⟩,
    ⟨[24941], [24938], .contexts [
        ⟨60367, false, false, [], []⟩
      ]⟩,
    ⟨[24938], [24938], .contexts []⟩,
    ⟨[84817, 15], [24941, 90325], .contexts [
        ⟨60366, false, false, [], []⟩,
        ⟨60365, false, false, [24938], [84817, 15]⟩,
        ⟨43331, true, false, [24938, 24933], [15]⟩,
        ⟨60364, true, false, [24938], [3, 15]⟩,
        ⟨60364, true, false, [24938], [3, 15]⟩,
        ⟨60363, true, false, [24938], [3, 15]⟩,
        ⟨60356, true, false, [24938], [3, 15]⟩,
        ⟨60353, true, false, [24938], [3, 15]⟩,
        ⟨1141, false, false, [24938, 90327], []⟩,
        ⟨21, false, false, [24938, 90327], []⟩,
        ⟨60018, false, false, [24938], []⟩,
        ⟨60019, false, false, [24938], []⟩,
        ⟨59943, false, false, [24938], []⟩,
        ⟨59943, false, false, [24938], []⟩,
        ⟨60370, true, false, [], [90325]⟩,
        ⟨60370, true, false, [], [90325]⟩,
        ⟨60369, true, false, [], [90325]⟩,
        ⟨60368, true, false, [], [90325]⟩
      ]⟩,
    ⟨[24939], [24940], .contexts [
        ⟨60367, true, true, [], []⟩
      ]⟩,
    ⟨[90325, 15], [24939, 84817], .contexts [
        ⟨60371, true, false, [24940], [15]⟩,
        ⟨1, false, false, [24940, 84817], []⟩,
        ⟨60372, true, false, [], [84817]⟩
      ]⟩,
    ⟨[24931, 83243], [24931, 83243], .contexts []⟩,
    ⟨[24931, 83243], [24931, 83243], .contexts []⟩,
    ⟨[24943], [24931, 20863], .source 12536⟩,
    ⟨[83243, 9], [20863, 86451], .contexts [
        ⟨43517, false, false, [], []⟩
      ]⟩,
    ⟨[20863, 86451], [20863, 86451], .contexts []⟩,
    ⟨[20863, 86451], [20863, 86451], .contexts []⟩,
    ⟨[86451, 13], [86451, 13], .contexts []⟩,
    ⟨[24945], [24942], .source 12537⟩,
    ⟨[24947], [24945, 20863], .source 12538⟩,
    ⟨[86451, 13], [24947, 86451], .contexts [
        ⟨60380, false, false, [], []⟩,
        ⟨60376, false, false, [24942], [86451, 13]⟩,
        ⟨43517, true, false, [24942, 24931], [13]⟩,
        ⟨60375, true, false, [24942], [9, 13]⟩,
        ⟨60375, true, false, [24942], [9, 13]⟩,
        ⟨60374, true, false, [24942], [9, 13]⟩,
        ⟨60362, true, false, [24942], [9, 13]⟩,
        ⟨60359, true, false, [24942], [9, 13]⟩,
        ⟨942, false, false, [24942, 83243], []⟩,
        ⟨47, false, false, [24942, 83243], []⟩,
        ⟨60377, false, false, [24942], []⟩,
        ⟨60378, false, false, [24942], []⟩,
        ⟨60379, false, false, [24942], []⟩,
        ⟨60379, false, false, [24942], []⟩,
        ⟨60381, true, false, [], [20863, 86451]⟩,
        ⟨60382, true, false, [], [86451]⟩
      ]⟩,
    ⟨[24941, 90325], [24941, 90325], .contexts []⟩,
    ⟨[24941, 90325], [24941, 90325], .contexts []⟩,
    ⟨[24941, 90321], [24941, 90321], .contexts []⟩,
    ⟨[84817], [84817], .contexts []⟩,
    ⟨[24940], [24940], .contexts []⟩,
    ⟨[90321, 1], [24939, 84817], .contexts [
        ⟨60386, true, false, [24940], [1]⟩,
        ⟨59936, true, false, [], [1]⟩,
        ⟨59940, true, false, [], [15, 1]⟩,
        ⟨60385, true, false, [24940], [1, 15, 1]⟩,
        ⟨60385, true, false, [24940], [1, 15, 1]⟩,
        ⟨60384, true, false, [24940], [1, 15, 1]⟩,
        ⟨60371, true, false, [24940], [1, 15, 1]⟩,
        ⟨60366, true, false, [24940], [1, 15, 1]⟩,
        ⟨504, false, false, [24940, 84817], []⟩,
        ⟨60387, false, false, [24940], []⟩,
        ⟨60388, true, false, [], [84817]⟩,
        ⟨60388, true, false, [], [84817]⟩,
        ⟨60372, true, false, [], [84817]⟩
      ]⟩,
    ⟨[90321], [24939, 84815], .contexts [
        ⟨60368, false, false, [24940], [90321]⟩,
        ⟨60386, true, false, [24940], []⟩,
        ⟨60367, false, false, [24940], [90321]⟩,
        ⟨8, true, false, [24940, 24938, 90321], []⟩,
        ⟨60389, false, false, [24940, 24938], [1]⟩,
        ⟨28757, false, false, [24940], []⟩,
        ⟨28758, false, false, [24940], []⟩,
        ⟨28653, false, false, [24940], []⟩,
        ⟨28653, false, false, [24940], []⟩,
        ⟨60372, true, false, [], [84815]⟩
      ]⟩,
    ⟨[24941], [24938], .contexts [
        ⟨60369, false, false, [], []⟩,
        ⟨60370, false, false, [], []⟩,
        ⟨60370, false, false, [], []⟩
      ]⟩,
    ⟨[84815, 13], [24941, 90319], .contexts [
        ⟨60390, true, false, [24938], [13]⟩,
        ⟨59932, false, false, [24938], []⟩,
        ⟨60022, false, false, [24938], []⟩,
        ⟨60391, true, false, [], [90319]⟩
      ]⟩,
    ⟨[90321], [24939, 84815], .contexts [
        ⟨60390, false, false, [], []⟩
      ]⟩,
    ⟨[24939, 84813], [24939, 84813], .contexts []⟩,
    ⟨[90323], [24939, 84813], .contexts [
        ⟨60369, false, false, [24940], [90323]⟩,
        ⟨13, false, false, [24940, 24938], [90323]⟩,
        ⟨60020, true, false, [24940, 24938], []⟩,
        ⟨59934, true, false, [24940, 24938], []⟩,
        ⟨60393, false, false, [24940, 24938], [15]⟩,
        ⟨28650, false, false, [24940], []⟩,
        ⟨60394, false, false, [24940, 24938], []⟩,
        ⟨60372, true, false, [], [84813]⟩
      ]⟩,
    ⟨[24947, 86451], [24947, 86451], .contexts []⟩,
    ⟨[86453, 13], [86453, 13], .contexts []⟩,
    ⟨[86453], [86453], .contexts []⟩,
    ⟨[24949], [24946], .source 12539⟩,
    ⟨[24946], [24946], .contexts []⟩,
    ⟨[24949], [24946], .contexts [
        ⟨60399, false, false, [], []⟩,
        ⟨60400, false, false, [], []⟩,
        ⟨60400, false, false, [], []⟩
      ]⟩,
    ⟨[86453, 13], [24949, 86453], .contexts [
        ⟨60397, false, false, [], []⟩,
        ⟨37167, true, false, [], [13]⟩,
        ⟨60396, true, false, [24946], [11, 13]⟩,
        ⟨60396, true, false, [24946], [11, 13]⟩,
        ⟨60383, true, false, [24946], [11, 13]⟩,
        ⟨60380, true, false, [24946], [11, 13]⟩,
        ⟨931, false, false, [24946, 86451], []⟩,
        ⟨54, false, false, [24946, 86451], []⟩,
        ⟨37167, false, false, [24946], []⟩,
        ⟨37444, false, false, [24946], []⟩,
        ⟨37172, false, false, [24946], []⟩,
        ⟨37172, false, false, [24946], []⟩,
        ⟨60398, false, false, [24946], []⟩,
        ⟨60401, true, false, [], [86453]⟩
      ]⟩,
    ⟨[24949, 86453], [24949, 86453], .contexts []⟩,
    ⟨[24949, 86453], [24949, 86453], .contexts []⟩,
    ⟨[86453, 1], [86455], .contexts [
        ⟨37171, false, false, [], []⟩,
        ⟨37443, false, false, [], []⟩,
        ⟨37176, false, false, [], []⟩,
        ⟨37176, false, false, [], []⟩
      ]⟩,
    ⟨[86457, 1], [86457, 1], .contexts []⟩,
    ⟨[86457], [86457], .contexts []⟩,
    ⟨[24947], [24948], .contexts [
        ⟨60399, true, true, [], []⟩
      ]⟩,
    ⟨[24947], [24947], .contexts []⟩,
    ⟨[24947], [24948], .contexts [
        ⟨60408, false, false, [], []⟩
      ]⟩,
    ⟨[24948], [24948], .contexts []⟩,
    ⟨[86457, 1], [24947, 86457], .contexts [
        ⟨60406, false, false, [], []⟩,
        ⟨37175, true, false, [], [1]⟩,
        ⟨37171, true, false, [], [13, 1]⟩,
        ⟨60404, true, false, [24948], [1, 13, 1]⟩,
        ⟨60404, true, false, [24948], [1, 13, 1]⟩,
        ⟨60403, true, false, [24948], [1, 13, 1]⟩,
        ⟨60402, true, false, [24948], [1, 13, 1]⟩,
        ⟨60397, true, false, [24948], [1, 13, 1]⟩,
        ⟨2181, false, false, [24948, 86453], []⟩,
        ⟨247, false, false, [24948, 86453], []⟩,
        ⟨60405, false, false, [24948], [13]⟩,
        ⟨37175, false, false, [24948], []⟩,
        ⟨37442, false, false, [24948], []⟩,
        ⟨37180, false, false, [24948], []⟩,
        ⟨37180, false, false, [24948], []⟩,
        ⟨60407, false, false, [24948], []⟩,
        ⟨60411, true, false, [], [86457]⟩,
        ⟨60411, true, false, [], [86457]⟩,
        ⟨60410, true, false, [], [86457]⟩,
        ⟨60409, true, false, [], [86457]⟩
      ]⟩,
    ⟨[24947, 86457], [24947, 86457], .contexts []⟩,
    ⟨[24947, 86457], [24947, 86457], .contexts []⟩,
    ⟨[24947, 86461], [24947, 86461], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 944. -/
def y322TCIndexRaw944 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86461, 15], [24949, 86457], .contexts [
        ⟨60415, true, false, [24946], [15]⟩,
        ⟨37183, true, false, [], [15]⟩,
        ⟨37179, true, false, [], [1, 15]⟩,
        ⟨60414, true, false, [24946], [15, 1, 15]⟩,
        ⟨60414, true, false, [24946], [15, 1, 15]⟩,
        ⟨60413, true, false, [24946], [15, 1, 15]⟩,
        ⟨60412, true, false, [24946], [15, 1, 15]⟩,
        ⟨60406, true, false, [24946], [15, 1, 15]⟩,
        ⟨2185, false, false, [24946, 86457], []⟩,
        ⟨60407, false, false, [24946], []⟩,
        ⟨60401, true, false, [], [86457]⟩
      ]⟩,
    ⟨[86457, 15], [86459], .contexts [
        ⟨37179, false, false, [], []⟩,
        ⟨37441, false, false, [], []⟩,
        ⟨37184, false, false, [], []⟩,
        ⟨37184, false, false, [], []⟩
      ]⟩,
    ⟨[86461], [24949, 86459], .contexts [
        ⟨60409, false, false, [24946], [86461]⟩,
        ⟨60415, true, false, [24946], []⟩,
        ⟨60408, false, false, [24946], [86461]⟩,
        ⟨1, true, false, [24946, 24948, 86461], []⟩,
        ⟨60416, false, false, [24946, 24948], [15]⟩,
        ⟨60417, false, false, [24946], []⟩,
        ⟨60399, true, false, [], [86459]⟩
      ]⟩,
    ⟨[86459, 3], [24947, 86463], .contexts [
        ⟨60418, true, false, [24948], [3]⟩,
        ⟨37186, false, false, [24948], []⟩,
        ⟨37439, false, false, [24948], []⟩,
        ⟨60411, true, false, [], [86463]⟩,
        ⟨60411, true, false, [], [86463]⟩,
        ⟨60410, true, false, [], [86463]⟩
      ]⟩,
    ⟨[90355], [84837, 11], .source 45242⟩,
    ⟨[84837, 11], [90355], .contexts [
        ⟨60420, true, false, [], []⟩
      ]⟩,
    ⟨[90355, 11], [84837], .contexts [
        ⟨60421, true, false, [], [11]⟩,
        ⟨53, false, false, [84837], []⟩,
        ⟨28697, false, false, [], []⟩
      ]⟩,
    ⟨[90355], [90355], .contexts []⟩,
    ⟨[90355], [90355], .contexts []⟩,
    ⟨[84837, 11], [90355], .contexts [
        ⟨60421, false, false, [], []⟩,
        ⟨60423, false, false, [], []⟩,
        ⟨60424, false, false, [], []⟩,
        ⟨60424, false, false, [], []⟩
      ]⟩,
    ⟨[17705, 90355], [17705, 90355], .contexts []⟩,
    ⟨[90355], [90355], .contexts []⟩,
    ⟨[17705], [17705], .contexts [
        ⟨13, false, false, [], [17705]⟩
      ]⟩,
    ⟨[90355, 1], [17705, 90355], .contexts [
        ⟨60425, true, false, [], [1]⟩,
        ⟨562, false, false, [84837], []⟩,
        ⟨563, false, false, [84837], []⟩,
        ⟨29095, false, false, [], [11]⟩,
        ⟨60421, false, false, [17705], []⟩,
        ⟨60426, false, false, [], []⟩,
        ⟨60427, false, false, [17705], []⟩,
        ⟨60428, true, false, [], [90355]⟩
      ]⟩,
    ⟨[20347, 89311], [20347, 89311], .contexts []⟩,
    ⟨[20347, 89311], [20347, 89311], .contexts []⟩,
    ⟨[20347, 89311], [20347, 89311], .contexts []⟩,
    ⟨[20347], [20347], .contexts [
        ⟨13, false, false, [], [20347]⟩
      ]⟩,
    ⟨[90355, 3], [20347, 89311], .contexts [
        ⟨60425, true, false, [], [3]⟩,
        ⟨215, false, false, [84837], []⟩,
        ⟨216, false, false, [84837], []⟩,
        ⟨29080, false, false, [], [11]⟩,
        ⟨41898, false, false, [], [11]⟩,
        ⟨41892, false, false, [], [11]⟩,
        ⟨41892, false, false, [], [11]⟩,
        ⟨55499, false, false, [20347], []⟩,
        ⟨60430, false, false, [], []⟩,
        ⟨60431, false, false, [], []⟩,
        ⟨60432, false, false, [], []⟩,
        ⟨55509, false, false, [20347], []⟩,
        ⟨60433, true, false, [], [89311]⟩
      ]⟩,
    ⟨[89311, 3], [20345, 90355], .contexts [
        ⟨60434, true, false, [20346], [3]⟩,
        ⟨20, false, false, [20346, 90355], []⟩,
        ⟨41878, true, false, [], [90355]⟩
      ]⟩,
    ⟨[17701, 90355], [17701, 90355], .contexts []⟩,
    ⟨[90355, 5], [17701, 90355], .contexts [
        ⟨60425, true, false, [], [5]⟩,
        ⟨642, false, false, [84837], []⟩,
        ⟨643, false, false, [84837], []⟩,
        ⟨28696, false, false, [], [11]⟩,
        ⟨29050, false, false, [], [11]⟩,
        ⟨29049, false, false, [], [11]⟩,
        ⟨29049, false, false, [], [11]⟩,
        ⟨60421, false, false, [17701], []⟩,
        ⟨60436, false, false, [], []⟩,
        ⟨60427, false, false, [17701], []⟩,
        ⟨13, true, false, [], [17701, 90355]⟩
      ]⟩,
    ⟨[17715, 90355], [17715, 90355], .contexts []⟩,
    ⟨[17707, 84843], [17707, 84843], .contexts []⟩,
    ⟨[17707, 84843], [17707, 84843], .contexts []⟩,
    ⟨[24951], [17707, 17653], .source 12540⟩,
    ⟨[24953], [24951, 17703], .source 12541⟩,
    ⟨[24953, 90355], [24953, 90355], .contexts []⟩,
    ⟨[90355, 9], [24953, 90355], .contexts [
        ⟨60425, true, false, [], [9]⟩,
        ⟨221, false, false, [84837], []⟩,
        ⟨224, false, false, [84837], []⟩,
        ⟨29047, false, false, [], [11, 9, 11]⟩,
        ⟨60439, false, false, [], [11, 9, 11]⟩,
        ⟨60440, false, false, [], [11, 9, 11]⟩,
        ⟨60440, false, false, [], [11, 9, 11]⟩,
        ⟨28707, false, false, [17707], [9, 11]⟩,
        ⟨28989, false, false, [17707], [9, 11]⟩,
        ⟨60441, true, false, [], [84843, 9, 11]⟩,
        ⟨28705, false, false, [24951], [11]⟩,
        ⟨29041, false, false, [24951], [11]⟩,
        ⟨60442, true, false, [], [84837, 11]⟩,
        ⟨60421, false, false, [24953], []⟩,
        ⟨60443, false, false, [], []⟩,
        ⟨60427, false, false, [24953], []⟩
      ]⟩,
    ⟨[90355, 9], [24953, 90355], .contexts [
        ⟨60444, false, false, [], []⟩,
        ⟨13, true, false, [], [24953, 90355]⟩
      ]⟩,
    ⟨[17711, 90355], [17711, 90355], .contexts []⟩,
    ⟨[90355, 13], [17711, 90355], .contexts [
        ⟨60425, true, false, [], [13]⟩,
        ⟨227, false, false, [84837], []⟩,
        ⟨228, false, false, [84837], []⟩,
        ⟨29079, false, false, [], [11]⟩,
        ⟨60421, false, false, [17711], []⟩,
        ⟨60446, false, false, [], []⟩,
        ⟨60427, false, false, [17711], []⟩,
        ⟨13, true, false, [], [17711, 90355]⟩
      ]⟩,
    ⟨[17723, 83961], [17723, 83961], .contexts []⟩,
    ⟨[17723, 83961], [17723, 83961], .contexts []⟩,
    ⟨[17723, 83963], [17723, 83963], .contexts []⟩,
    ⟨[90355, 15], [17723, 83963], .contexts [
        ⟨60425, true, false, [], [15]⟩,
        ⟨231, false, false, [84837], []⟩,
        ⟨232, false, false, [84837], []⟩,
        ⟨29072, false, false, [], [11]⟩,
        ⟨29074, false, false, [], [11]⟩,
        ⟨60448, false, false, [], [11]⟩,
        ⟨60449, false, false, [], [11]⟩,
        ⟨60449, false, false, [], [11]⟩,
        ⟨24220, false, false, [17723], []⟩,
        ⟨60450, false, false, [], []⟩,
        ⟨24226, false, false, [17723], []⟩,
        ⟨13, true, false, [], [17723, 83963]⟩
      ]⟩,
    ⟨[83963, 15], [17725, 90355], .contexts [
        ⟨60451, true, false, [17722], [15]⟩,
        ⟨1, false, false, [17722, 90355], []⟩,
        ⟨29075, true, false, [], [90355]⟩
      ]⟩,
    ⟨[90357], [83963, 3], .source 45243⟩,
    ⟨[83963, 3], [90357], .contexts [
        ⟨60453, true, false, [], []⟩
      ]⟩,
    ⟨[90357, 3], [83963], .contexts [
        ⟨60454, true, false, [], [3]⟩,
        ⟨20, false, false, [83963], []⟩,
        ⟨24222, false, false, [], []⟩
      ]⟩,
    ⟨[90357], [90357], .contexts []⟩,
    ⟨[90357], [90357], .contexts []⟩,
    ⟨[83963, 3], [90357], .contexts [
        ⟨60454, false, false, [], []⟩,
        ⟨60456, false, false, [], []⟩,
        ⟨60457, false, false, [], []⟩,
        ⟨60457, false, false, [], []⟩
      ]⟩,
    ⟨[16069, 90357], [16069, 90357], .contexts []⟩,
    ⟨[16069, 90357], [16069, 90357], .contexts []⟩,
    ⟨[90357, 7], [90357, 7], .contexts []⟩,
    ⟨[90357], [90357], .contexts []⟩,
    ⟨[90357, 7], [16069, 90357], .contexts [
        ⟨60461, false, false, [], []⟩,
        ⟨60458, true, false, [], [7]⟩,
        ⟨140, false, false, [83963], []⟩,
        ⟨141, false, false, [83963], []⟩,
        ⟨24253, false, false, [], [3]⟩,
        ⟨60454, false, false, [16069], []⟩,
        ⟨60459, false, false, [], []⟩,
        ⟨60460, false, false, [], []⟩,
        ⟨60462, false, false, [16069], []⟩,
        ⟨20009, true, false, [], [90357]⟩
      ]⟩,
    ⟨[15817, 90357], [15817, 90357], .contexts []⟩,
    ⟨[15817, 90357], [15817, 90357], .contexts []⟩,
    ⟨[15817, 90357], [15817, 90357], .contexts []⟩,
    ⟨[90357, 9], [90357, 9], .contexts []⟩,
    ⟨[90357, 9], [15817, 90357], .contexts [
        ⟨60467, false, false, [], []⟩,
        ⟨60458, true, false, [], [9]⟩,
        ⟨669, false, false, [83963], []⟩,
        ⟨670, false, false, [83963], []⟩,
        ⟨24258, false, false, [], [3]⟩,
        ⟨60454, false, false, [15817], []⟩,
        ⟨60464, false, false, [], []⟩,
        ⟨60465, false, false, [], []⟩,
        ⟨60466, false, false, [], []⟩,
        ⟨60462, false, false, [15817], []⟩,
        ⟨18737, true, false, [], [90357]⟩
      ]⟩,
    ⟨[17725, 90355], [17725, 90355], .contexts []⟩,
    ⟨[17725, 90355], [17725, 90355], .contexts []⟩,
    ⟨[24955], [17725, 20347], .source 12542⟩,
    ⟨[90357, 15], [90357, 15], .contexts []⟩,
    ⟨[90357, 15], [24955, 89311], .contexts [
        ⟨60472, false, false, [], []⟩,
        ⟨60458, true, false, [], [15]⟩,
        ⟨151, false, false, [83963], []⟩,
        ⟨152, false, false, [83963], []⟩,
        ⟨60452, false, false, [], [3]⟩,
        ⟨60469, false, false, [], [3]⟩,
        ⟨60470, false, false, [], [3]⟩,
        ⟨60470, false, false, [], [3]⟩,
        ⟨60434, false, false, [17725], []⟩,
        ⟨60471, true, false, [], [89311]⟩,
        ⟨55509, false, false, [24955], []⟩,
        ⟨13, true, false, [], [24955, 89311]⟩
      ]⟩,
    ⟨[24957], [24954], .source 12543⟩,
    ⟨[89311, 15], [24957, 90357], .contexts [
        ⟨60473, true, false, [24954], [15]⟩,
        ⟨1, false, false, [24954, 90357], []⟩,
        ⟨60474, true, false, [], [90357]⟩
      ]⟩,
    ⟨[90359], [90357, 5], .source 45244⟩,
    ⟨[90357, 5], [90359], .contexts [
        ⟨60476, true, false, [], []⟩
      ]⟩,
    ⟨[90359], [90359], .contexts []⟩,
    ⟨[90359], [90359], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 945. -/
def y322TCIndexRaw945 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90357, 5], [90359], .contexts [
        ⟨60477, false, false, [], []⟩,
        ⟨60478, false, false, [], []⟩,
        ⟨60479, false, false, [], []⟩,
        ⟨60479, false, false, [], []⟩
      ]⟩,
    ⟨[90357, 9], [15817, 90357], .contexts [
        ⟨60467, false, false, [], []⟩,
        ⟨60468, false, false, [], []⟩,
        ⟨60464, false, false, [], []⟩,
        ⟨60466, false, false, [], []⟩,
        ⟨60466, false, false, [], []⟩
      ]⟩,
    ⟨[15817, 90359], [15817, 90359], .contexts []⟩,
    ⟨[15817, 90359], [15817, 90359], .contexts []⟩,
    ⟨[15817, 90359], [15817, 90359], .contexts []⟩,
    ⟨[90361], [90359, 1], .source 45245⟩,
    ⟨[90359, 1], [90361], .contexts [
        ⟨60485, true, false, [], []⟩
      ]⟩,
    ⟨[90361, 1], [90359], .contexts [
        ⟨60486, true, false, [], [1]⟩,
        ⟨8, false, false, [90359], []⟩,
        ⟨60479, false, false, [], []⟩
      ]⟩,
    ⟨[90363], [90361, 9], .source 45246⟩,
    ⟨[90361, 9], [90363], .contexts [
        ⟨60488, true, false, [], []⟩
      ]⟩,
    ⟨[90363], [90363], .contexts []⟩,
    ⟨[90363], [90363], .contexts []⟩,
    ⟨[15817, 90361], [15817, 90361], .contexts []⟩,
    ⟨[15817, 90361], [15817, 90361], .contexts []⟩,
    ⟨[15817, 90361], [15817, 90361], .contexts []⟩,
    ⟨[15817, 90363], [15817, 90363], .contexts []⟩,
    ⟨[15817, 90363], [15817, 90363], .contexts []⟩,
    ⟨[90361, 1, 9, 1, 9], [15817, 90363], .contexts [
        ⟨60487, false, false, [], [9, 1, 9]⟩,
        ⟨60478, false, false, [], [9, 1, 9]⟩,
        ⟨60479, false, false, [], [9, 1, 9]⟩,
        ⟨60479, false, false, [], [9, 1, 9]⟩,
        ⟨60480, true, false, [], [9, 1, 9]⟩,
        ⟨1265, false, false, [90357], [1, 9]⟩,
        ⟨1266, false, false, [90357], [1, 9]⟩,
        ⟨60481, false, false, [], [5, 1, 9]⟩,
        ⟨60477, false, false, [15817], [1, 9]⟩,
        ⟨60482, false, false, [], [1, 9]⟩,
        ⟨60483, false, false, [], [1, 9]⟩,
        ⟨60484, false, false, [], [1, 9]⟩,
        ⟨18737, true, false, [], [90359, 1, 9]⟩,
        ⟨60482, false, false, [], [1, 9]⟩,
        ⟨60484, false, false, [], [1, 9]⟩,
        ⟨60484, false, false, [], [1, 9]⟩,
        ⟨60486, false, false, [15817], [9]⟩,
        ⟨60492, false, false, [], [9]⟩,
        ⟨60493, false, false, [], [9]⟩,
        ⟨60494, false, false, [], [9]⟩,
        ⟨60489, false, false, [15817], []⟩,
        ⟨60495, false, false, [], []⟩,
        ⟨60496, false, false, [], []⟩
      ]⟩,
    ⟨[15817, 90363], [15817, 90363], .contexts []⟩,
    ⟨[90363, 1], [90363, 1], .contexts []⟩,
    ⟨[90365], [90363, 11], .source 45247⟩,
    ⟨[90363, 11], [90365], .contexts [
        ⟨60500, true, false, [], []⟩
      ]⟩,
    ⟨[90365], [90365], .contexts []⟩,
    ⟨[90365], [90365], .contexts []⟩,
    ⟨[15817, 90365], [15817, 90365], .contexts []⟩,
    ⟨[15817, 90365], [15817, 90365], .contexts []⟩,
    ⟨[90363, 1, 11], [15817, 90365], .contexts [
        ⟨60499, false, false, [], [11]⟩,
        ⟨60499, false, false, [], [11]⟩,
        ⟨60491, true, false, [], [1, 11]⟩,
        ⟨60491, true, false, [], [1, 11]⟩,
        ⟨60490, true, false, [], [1, 11]⟩,
        ⟨60489, true, false, [], [1, 11]⟩,
        ⟨691, false, false, [90361], [11]⟩,
        ⟨694, false, false, [90361], [11]⟩,
        ⟨60497, false, false, [], [11]⟩,
        ⟨60498, false, false, [], [11]⟩,
        ⟨18737, true, false, [], [90363, 11]⟩,
        ⟨60495, false, false, [], [11]⟩,
        ⟨60498, false, false, [], [11]⟩,
        ⟨60498, false, false, [], [11]⟩,
        ⟨60501, false, false, [15817], []⟩,
        ⟨60504, false, false, [], []⟩,
        ⟨60505, false, false, [], []⟩
      ]⟩,
    ⟨[90367], [90365, 13], .source 45248⟩,
    ⟨[90365, 13], [90367], .contexts [
        ⟨60507, true, false, [], []⟩
      ]⟩,
    ⟨[90369], [90367, 15], .source 45249⟩,
    ⟨[90367, 15], [90369], .contexts [
        ⟨60509, true, false, [], []⟩
      ]⟩,
    ⟨[90367], [90367], .contexts []⟩,
    ⟨[90369, 15], [90367], .contexts [
        ⟨60510, true, false, [], [15]⟩,
        ⟨1, false, false, [90367], []⟩,
        ⟨60511, false, false, [], []⟩
      ]⟩,
    ⟨[90371], [90369, 1], .source 45250⟩,
    ⟨[90369, 1], [90371], .contexts [
        ⟨60513, true, false, [], []⟩
      ]⟩,
    ⟨[90369], [90369], .contexts []⟩,
    ⟨[90371, 1], [90369], .contexts [
        ⟨60514, true, false, [], [1]⟩,
        ⟨8, false, false, [90369], []⟩,
        ⟨60515, false, false, [], []⟩
      ]⟩,
    ⟨[90373], [90371, 3], .source 45251⟩,
    ⟨[90371, 3], [90373], .contexts [
        ⟨60517, true, false, [], []⟩
      ]⟩,
    ⟨[90371], [90371], .contexts []⟩,
    ⟨[90375], [90373, 5], .source 45252⟩,
    ⟨[90373, 5], [90375], .contexts [
        ⟨60520, true, false, [], []⟩
      ]⟩,
    ⟨[90373], [90373], .contexts []⟩,
    ⟨[90377], [90375, 1], .source 45253⟩,
    ⟨[90375, 1], [90377], .contexts [
        ⟨60523, true, false, [], []⟩
      ]⟩,
    ⟨[90375], [90375], .contexts []⟩,
    ⟨[90379], [90377, 9], .source 45254⟩,
    ⟨[90377, 9], [90379], .contexts [
        ⟨60526, true, false, [], []⟩
      ]⟩,
    ⟨[90377], [90377], .contexts []⟩,
    ⟨[90379, 9], [90377], .contexts [
        ⟨60527, true, false, [], [9]⟩,
        ⟨46, false, false, [90377], []⟩,
        ⟨60528, false, false, [], []⟩
      ]⟩,
    ⟨[90381], [90379, 11], .source 45255⟩,
    ⟨[90379, 11], [90381], .contexts [
        ⟨60530, true, false, [], []⟩
      ]⟩,
    ⟨[90379], [90379], .contexts []⟩,
    ⟨[90381, 11], [90379], .contexts [
        ⟨60531, true, false, [], [11]⟩,
        ⟨53, false, false, [90379], []⟩,
        ⟨60532, false, false, [], []⟩
      ]⟩,
    ⟨[90383], [90381, 1], .source 45256⟩,
    ⟨[90381, 1], [90383], .contexts [
        ⟨60534, true, false, [], []⟩
      ]⟩,
    ⟨[90381], [90381], .contexts []⟩,
    ⟨[90383, 1], [90381], .contexts [
        ⟨60535, true, false, [], [1]⟩,
        ⟨8, false, false, [90381], []⟩,
        ⟨60536, false, false, [], []⟩
      ]⟩,
    ⟨[90385], [90383, 13], .source 45257⟩,
    ⟨[90383, 13], [90385], .contexts [
        ⟨60538, true, false, [], []⟩
      ]⟩,
    ⟨[90383], [90383], .contexts []⟩,
    ⟨[90385, 13], [90383], .contexts [
        ⟨60539, true, false, [], [13]⟩,
        ⟨59, false, false, [90383], []⟩,
        ⟨60540, false, false, [], []⟩
      ]⟩,
    ⟨[90387], [90385, 15], .source 45258⟩,
    ⟨[90385, 15], [90387], .contexts [
        ⟨60542, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 946. -/
def y322TCIndexRaw946 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90385], [90385], .contexts []⟩,
    ⟨[90387, 15], [90385], .contexts [
        ⟨60543, true, false, [], [15]⟩,
        ⟨1, false, false, [90385], []⟩,
        ⟨60544, false, false, [], []⟩
      ]⟩,
    ⟨[90389], [90387, 1], .source 45259⟩,
    ⟨[90387, 1], [90389], .contexts [
        ⟨60546, true, false, [], []⟩
      ]⟩,
    ⟨[90387], [90387], .contexts []⟩,
    ⟨[90389, 1], [90387], .contexts [
        ⟨60547, true, false, [], [1]⟩,
        ⟨8, false, false, [90387], []⟩,
        ⟨60548, false, false, [], []⟩
      ]⟩,
    ⟨[90391], [90389, 3], .source 45260⟩,
    ⟨[90389, 3], [90391], .contexts [
        ⟨60550, true, false, [], []⟩
      ]⟩,
    ⟨[90389], [90389], .contexts []⟩,
    ⟨[90391, 3], [90389], .contexts [
        ⟨60551, true, false, [], [3]⟩,
        ⟨20, false, false, [90389], []⟩,
        ⟨60552, false, false, [], []⟩
      ]⟩,
    ⟨[90393], [90391, 5], .source 45261⟩,
    ⟨[90391, 5], [90393], .contexts [
        ⟨60554, true, false, [], []⟩
      ]⟩,
    ⟨[90391], [90391], .contexts []⟩,
    ⟨[90395], [90393, 1], .source 45262⟩,
    ⟨[90393, 1], [90395], .contexts [
        ⟨60557, true, false, [], []⟩
      ]⟩,
    ⟨[90393], [90393], .contexts []⟩,
    ⟨[90395, 1], [90393], .contexts [
        ⟨60558, true, false, [], [1]⟩,
        ⟨8, false, false, [90393], []⟩,
        ⟨60559, false, false, [], []⟩
      ]⟩,
    ⟨[90397], [90395, 9], .source 45263⟩,
    ⟨[90395, 9], [90397], .contexts [
        ⟨60561, true, false, [], []⟩
      ]⟩,
    ⟨[90395], [90395], .contexts []⟩,
    ⟨[90397, 9], [90395], .contexts [
        ⟨60562, true, false, [], [9]⟩,
        ⟨46, false, false, [90395], []⟩,
        ⟨60563, false, false, [], []⟩
      ]⟩,
    ⟨[90399], [90397, 11], .source 45264⟩,
    ⟨[90397, 11], [90399], .contexts [
        ⟨60565, true, false, [], []⟩
      ]⟩,
    ⟨[90397], [90397], .contexts []⟩,
    ⟨[90401], [90399, 1], .source 45265⟩,
    ⟨[90399, 1], [90401], .contexts [
        ⟨60568, true, false, [], []⟩
      ]⟩,
    ⟨[90399], [90399], .contexts []⟩,
    ⟨[90401, 1], [90399], .contexts [
        ⟨60569, true, false, [], [1]⟩,
        ⟨8, false, false, [90399], []⟩,
        ⟨60570, false, false, [], []⟩
      ]⟩,
    ⟨[90403], [90401, 13], .source 45266⟩,
    ⟨[90401, 13], [90403], .contexts [
        ⟨60572, true, false, [], []⟩
      ]⟩,
    ⟨[90401], [90401], .contexts []⟩,
    ⟨[90405], [90403, 15], .source 45267⟩,
    ⟨[90403], [90403], .contexts []⟩,
    ⟨[90405, 15], [90403], .contexts [
        ⟨60575, false, false, [], [15]⟩,
        ⟨1, false, false, [90403], []⟩,
        ⟨60576, false, false, [], []⟩
      ]⟩,
    ⟨[90407], [90405, 1], .source 45268⟩,
    ⟨[90405], [90405], .contexts []⟩,
    ⟨[90407, 1], [90405], .contexts [
        ⟨60578, false, false, [], [1]⟩,
        ⟨8, false, false, [90405], []⟩,
        ⟨60579, false, false, [], []⟩
      ]⟩,
    ⟨[90409], [90407, 3], .source 45269⟩,
    ⟨[90407], [90407], .contexts []⟩,
    ⟨[90409, 3], [90407], .contexts [
        ⟨60581, false, false, [], [3]⟩,
        ⟨20, false, false, [90407], []⟩,
        ⟨60582, false, false, [], []⟩
      ]⟩,
    ⟨[90411], [90409, 5], .source 45270⟩,
    ⟨[90409, 5], [90411], .contexts [
        ⟨60584, true, false, [], []⟩
      ]⟩,
    ⟨[90409], [90409], .contexts []⟩,
    ⟨[90411, 5], [90409], .contexts [
        ⟨60585, true, false, [], [5]⟩,
        ⟨28, false, false, [90409], []⟩,
        ⟨60586, false, false, [], []⟩
      ]⟩,
    ⟨[90413], [90411, 1], .source 45271⟩,
    ⟨[90411], [90411], .contexts []⟩,
    ⟨[90413, 1], [90411], .contexts [
        ⟨60588, false, false, [], [1]⟩,
        ⟨8, false, false, [90411], []⟩,
        ⟨60589, false, false, [], []⟩
      ]⟩,
    ⟨[90415], [90413, 9], .source 45272⟩,
    ⟨[90413, 9], [90415], .contexts [
        ⟨60591, true, false, [], []⟩
      ]⟩,
    ⟨[90413], [90413], .contexts []⟩,
    ⟨[90415, 9], [90413], .contexts [
        ⟨60592, true, false, [], [9]⟩,
        ⟨46, false, false, [90413], []⟩,
        ⟨60593, false, false, [], []⟩
      ]⟩,
    ⟨[90417], [90415, 11], .source 45273⟩,
    ⟨[90415, 11], [90417], .contexts [
        ⟨60595, true, false, [], []⟩
      ]⟩,
    ⟨[90415], [90415], .contexts []⟩,
    ⟨[90417, 11], [90415], .contexts [
        ⟨60596, true, false, [], [11]⟩,
        ⟨53, false, false, [90415], []⟩,
        ⟨60597, false, false, [], []⟩
      ]⟩,
    ⟨[90419], [90417, 1], .source 45274⟩,
    ⟨[90417], [90417], .contexts []⟩,
    ⟨[90419, 1], [90417], .contexts [
        ⟨60599, false, false, [], [1]⟩,
        ⟨8, false, false, [90417], []⟩,
        ⟨60600, false, false, [], []⟩
      ]⟩,
    ⟨[90421], [90419, 13], .source 45275⟩,
    ⟨[90419, 13], [90421], .contexts [
        ⟨60602, true, false, [], []⟩
      ]⟩,
    ⟨[90419], [90419], .contexts []⟩,
    ⟨[90421, 13], [90419], .contexts [
        ⟨60603, true, false, [], [13]⟩,
        ⟨59, false, false, [90419], []⟩,
        ⟨60604, false, false, [], []⟩
      ]⟩,
    ⟨[90423], [90421, 15], .source 45276⟩,
    ⟨[90421], [90421], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 947. -/
def y322TCIndexRaw947 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90423, 15], [90421], .contexts [
        ⟨60606, false, false, [], [15]⟩,
        ⟨1, false, false, [90421], []⟩,
        ⟨60607, false, false, [], []⟩
      ]⟩,
    ⟨[90425], [90423, 1], .source 45277⟩,
    ⟨[90423], [90423], .contexts []⟩,
    ⟨[90425, 1], [90423], .contexts [
        ⟨60609, false, false, [], [1]⟩,
        ⟨8, false, false, [90423], []⟩,
        ⟨60610, false, false, [], []⟩
      ]⟩,
    ⟨[90427], [90425, 3], .source 45278⟩,
    ⟨[90425, 3], [90427], .contexts [
        ⟨60612, true, false, [], []⟩
      ]⟩,
    ⟨[90425], [90425], .contexts []⟩,
    ⟨[90427, 3], [90425], .contexts [
        ⟨60613, true, false, [], [3]⟩,
        ⟨20, false, false, [90425], []⟩,
        ⟨60614, false, false, [], []⟩
      ]⟩,
    ⟨[90429], [90427, 5], .source 45279⟩,
    ⟨[90427, 5], [90429], .contexts [
        ⟨60616, true, false, [], []⟩
      ]⟩,
    ⟨[90427], [90427], .contexts []⟩,
    ⟨[90429, 5], [90427], .contexts [
        ⟨60617, true, false, [], [5]⟩,
        ⟨28, false, false, [90427], []⟩,
        ⟨60618, false, false, [], []⟩
      ]⟩,
    ⟨[90431], [90429, 1], .source 45280⟩,
    ⟨[90429], [90429], .contexts []⟩,
    ⟨[90431, 1], [90429], .contexts [
        ⟨60620, false, false, [], [1]⟩,
        ⟨8, false, false, [90429], []⟩,
        ⟨60621, false, false, [], []⟩
      ]⟩,
    ⟨[90433], [90431, 9], .source 45281⟩,
    ⟨[90431], [90431], .contexts []⟩,
    ⟨[90433, 9], [90431], .contexts [
        ⟨60623, false, false, [], [9]⟩,
        ⟨46, false, false, [90431], []⟩,
        ⟨60624, false, false, [], []⟩
      ]⟩,
    ⟨[90435], [90433, 11], .source 45282⟩,
    ⟨[90433, 11], [90435], .contexts [
        ⟨60626, true, false, [], []⟩
      ]⟩,
    ⟨[90433], [90433], .contexts []⟩,
    ⟨[90435, 11], [90433], .contexts [
        ⟨60627, true, false, [], [11]⟩,
        ⟨53, false, false, [90433], []⟩,
        ⟨60628, false, false, [], []⟩
      ]⟩,
    ⟨[90437], [90435, 1], .source 45283⟩,
    ⟨[90435], [90435], .contexts []⟩,
    ⟨[90439], [90437, 13], .source 45284⟩,
    ⟨[90437], [90437], .contexts []⟩,
    ⟨[90439, 13], [90437], .contexts [
        ⟨60632, false, false, [], [13]⟩,
        ⟨59, false, false, [90437], []⟩,
        ⟨60633, false, false, [], []⟩
      ]⟩,
    ⟨[90441], [90439, 15], .source 45285⟩,
    ⟨[90439, 15], [90441], .contexts [
        ⟨60635, true, false, [], []⟩
      ]⟩,
    ⟨[90439], [90439], .contexts []⟩,
    ⟨[90441, 15], [90439], .contexts [
        ⟨60636, true, false, [], [15]⟩,
        ⟨1, false, false, [90439], []⟩,
        ⟨60637, false, false, [], []⟩
      ]⟩,
    ⟨[90443], [90441, 1], .source 45286⟩,
    ⟨[90441, 1], [90443], .contexts [
        ⟨60639, true, false, [], []⟩
      ]⟩,
    ⟨[90441], [90441], .contexts []⟩,
    ⟨[90443, 1], [90441], .contexts [
        ⟨60640, true, false, [], [1]⟩,
        ⟨8, false, false, [90441], []⟩,
        ⟨60641, false, false, [], []⟩
      ]⟩,
    ⟨[90445], [90443, 3], .source 45287⟩,
    ⟨[90443, 3], [90445], .contexts [
        ⟨60643, true, false, [], []⟩
      ]⟩,
    ⟨[90443], [90443], .contexts []⟩,
    ⟨[90445, 3], [90443], .contexts [
        ⟨60644, true, false, [], [3]⟩,
        ⟨20, false, false, [90443], []⟩,
        ⟨60645, false, false, [], []⟩
      ]⟩,
    ⟨[90447], [90445, 5], .source 45288⟩,
    ⟨[90445, 5], [90447], .contexts [
        ⟨60647, true, false, [], []⟩
      ]⟩,
    ⟨[90445], [90445], .contexts []⟩,
    ⟨[90447, 5], [90445], .contexts [
        ⟨60648, true, false, [], [5]⟩,
        ⟨28, false, false, [90445], []⟩,
        ⟨60649, false, false, [], []⟩
      ]⟩,
    ⟨[90449], [90447, 1], .source 45289⟩,
    ⟨[90447], [90447], .contexts []⟩,
    ⟨[90449, 1], [90447], .contexts [
        ⟨60651, false, false, [], [1]⟩,
        ⟨8, false, false, [90447], []⟩,
        ⟨60652, false, false, [], []⟩
      ]⟩,
    ⟨[90451], [90449, 9], .source 45290⟩,
    ⟨[90449, 9], [90451], .contexts [
        ⟨60654, true, false, [], []⟩
      ]⟩,
    ⟨[90449], [90449], .contexts []⟩,
    ⟨[90451, 9], [90449], .contexts [
        ⟨60655, true, false, [], [9]⟩,
        ⟨46, false, false, [90449], []⟩,
        ⟨60656, false, false, [], []⟩
      ]⟩,
    ⟨[90453], [90451, 11], .source 45291⟩,
    ⟨[90451, 11], [90453], .contexts [
        ⟨60658, true, false, [], []⟩
      ]⟩,
    ⟨[90451], [90451], .contexts []⟩,
    ⟨[90453, 11], [90451], .contexts [
        ⟨60659, true, false, [], [11]⟩,
        ⟨53, false, false, [90451], []⟩,
        ⟨60660, false, false, [], []⟩
      ]⟩,
    ⟨[90455], [90453, 1], .source 45292⟩,
    ⟨[90453], [90453], .contexts []⟩,
    ⟨[90455, 1], [90453], .contexts [
        ⟨60662, false, false, [], [1]⟩,
        ⟨8, false, false, [90453], []⟩,
        ⟨60663, false, false, [], []⟩
      ]⟩,
    ⟨[90457], [90455, 13], .source 45293⟩,
    ⟨[90455, 13], [90457], .contexts [
        ⟨60665, true, false, [], []⟩
      ]⟩,
    ⟨[90455], [90455], .contexts []⟩,
    ⟨[90457, 13], [90455], .contexts [
        ⟨60666, true, false, [], [13]⟩,
        ⟨59, false, false, [90455], []⟩,
        ⟨60667, false, false, [], []⟩
      ]⟩,
    ⟨[90459], [90457, 15], .source 45294⟩,
    ⟨[90457, 15], [90459], .contexts [
        ⟨60669, true, false, [], []⟩
      ]⟩,
    ⟨[90457], [90457], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 948. -/
def y322TCIndexRaw948 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90459, 15], [90457], .contexts [
        ⟨60670, true, false, [], [15]⟩,
        ⟨1, false, false, [90457], []⟩,
        ⟨60671, false, false, [], []⟩
      ]⟩,
    ⟨[90461], [90459, 1], .source 45295⟩,
    ⟨[90459, 1], [90461], .contexts [
        ⟨60673, true, false, [], []⟩
      ]⟩,
    ⟨[90459], [90459], .contexts []⟩,
    ⟨[90461, 1], [90459], .contexts [
        ⟨60674, true, false, [], [1]⟩,
        ⟨8, false, false, [90459], []⟩,
        ⟨60675, false, false, [], []⟩
      ]⟩,
    ⟨[90463], [90461, 3], .source 45296⟩,
    ⟨[90461], [90461], .contexts []⟩,
    ⟨[90463, 3], [90461], .contexts [
        ⟨60677, false, false, [], [3]⟩,
        ⟨20, false, false, [90461], []⟩,
        ⟨60678, false, false, [], []⟩
      ]⟩,
    ⟨[90465], [90463, 5], .source 45297⟩,
    ⟨[90463, 5], [90465], .contexts [
        ⟨60680, true, false, [], []⟩
      ]⟩,
    ⟨[90463], [90463], .contexts []⟩,
    ⟨[90465, 5], [90463], .contexts [
        ⟨60681, true, false, [], [5]⟩,
        ⟨28, false, false, [90463], []⟩,
        ⟨60682, false, false, [], []⟩
      ]⟩,
    ⟨[90467], [90465, 1], .source 45298⟩,
    ⟨[90465], [90465], .contexts []⟩,
    ⟨[90467, 1], [90465], .contexts [
        ⟨60684, false, false, [], [1]⟩,
        ⟨8, false, false, [90465], []⟩,
        ⟨60685, false, false, [], []⟩
      ]⟩,
    ⟨[90469], [90467, 9], .source 45299⟩,
    ⟨[90467, 9], [90469], .contexts [
        ⟨60687, true, false, [], []⟩
      ]⟩,
    ⟨[90467], [90467], .contexts []⟩,
    ⟨[90469, 9], [90467], .contexts [
        ⟨60688, true, false, [], [9]⟩,
        ⟨46, false, false, [90467], []⟩,
        ⟨60689, false, false, [], []⟩
      ]⟩,
    ⟨[90471], [90469, 11], .source 45300⟩,
    ⟨[90469, 11], [90471], .contexts [
        ⟨60691, true, false, [], []⟩
      ]⟩,
    ⟨[90469], [90469], .contexts []⟩,
    ⟨[90471, 11], [90469], .contexts [
        ⟨60692, true, false, [], [11]⟩,
        ⟨53, false, false, [90469], []⟩,
        ⟨60693, false, false, [], []⟩
      ]⟩,
    ⟨[90473], [90471, 1], .source 45301⟩,
    ⟨[90471], [90471], .contexts []⟩,
    ⟨[90473, 1], [90471], .contexts [
        ⟨60695, false, false, [], [1]⟩,
        ⟨8, false, false, [90471], []⟩,
        ⟨60696, false, false, [], []⟩
      ]⟩,
    ⟨[90475], [90473, 13], .source 45302⟩,
    ⟨[90473, 13], [90475], .contexts [
        ⟨60698, true, false, [], []⟩
      ]⟩,
    ⟨[90473], [90473], .contexts []⟩,
    ⟨[90475, 13], [90473], .contexts [
        ⟨60699, true, false, [], [13]⟩,
        ⟨59, false, false, [90473], []⟩,
        ⟨60700, false, false, [], []⟩
      ]⟩,
    ⟨[90477], [90475, 15], .source 45303⟩,
    ⟨[90475, 15], [90477], .contexts [
        ⟨60702, true, false, [], []⟩
      ]⟩,
    ⟨[90475], [90475], .contexts []⟩,
    ⟨[90477, 15], [90475], .contexts [
        ⟨60703, true, false, [], [15]⟩,
        ⟨1, false, false, [90475], []⟩,
        ⟨60704, false, false, [], []⟩
      ]⟩,
    ⟨[90479], [90477, 1], .source 45304⟩,
    ⟨[90477, 1], [90479], .contexts [
        ⟨60706, true, false, [], []⟩
      ]⟩,
    ⟨[90477], [90477], .contexts []⟩,
    ⟨[90479, 1], [90477], .contexts [
        ⟨60707, true, false, [], [1]⟩,
        ⟨8, false, false, [90477], []⟩,
        ⟨60708, false, false, [], []⟩
      ]⟩,
    ⟨[90477, 1], [90479], .contexts [
        ⟨60707, false, false, [], []⟩
      ]⟩,
    ⟨[90479], [90479], .contexts []⟩,
    ⟨[90479], [90479], .contexts []⟩,
    ⟨[90475], [90475], .contexts []⟩,
    ⟨[90477, 15], [90475], .contexts [
        ⟨60705, false, false, [], []⟩,
        ⟨60713, false, false, [], []⟩,
        ⟨60704, false, false, [], []⟩,
        ⟨60704, false, false, [], []⟩
      ]⟩,
    ⟨[90475, 13], [90473], .contexts [
        ⟨60701, false, false, [], []⟩
      ]⟩,
    ⟨[90473], [90473], .contexts []⟩,
    ⟨[90477, 15, 13], [90473], .contexts [
        ⟨60714, false, false, [], [13]⟩,
        ⟨60715, false, false, [], []⟩,
        ⟨60716, false, false, [], []⟩,
        ⟨60700, false, false, [], []⟩,
        ⟨60700, false, false, [], []⟩
      ]⟩,
    ⟨[90473, 1], [90471], .contexts [
        ⟨60697, false, false, [], []⟩
      ]⟩,
    ⟨[90471], [90471], .contexts []⟩,
    ⟨[90469], [90469], .contexts []⟩,
    ⟨[90469, 9], [90467], .contexts [
        ⟨60690, false, false, [], []⟩
      ]⟩,
    ⟨[90467], [90467], .contexts []⟩,
    ⟨[90467, 1], [90465], .contexts [
        ⟨60686, false, false, [], []⟩
      ]⟩,
    ⟨[90465], [90465], .contexts []⟩,
    ⟨[90477, 15, 13, 1, 11, 9, 1, 5], [90463], .contexts [
        ⟨60717, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨60718, false, false, [], [11, 9, 1, 5]⟩,
        ⟨60719, false, false, [], [11, 9, 1, 5]⟩,
        ⟨60696, false, false, [], [11, 9, 1, 5]⟩,
        ⟨60696, false, false, [], [11, 9, 1, 5]⟩,
        ⟨60694, false, false, [], [9, 1, 5]⟩,
        ⟨60720, false, false, [], [9, 1, 5]⟩,
        ⟨60693, false, false, [], [9, 1, 5]⟩,
        ⟨60693, false, false, [], [9, 1, 5]⟩,
        ⟨60721, false, false, [], [1, 5]⟩,
        ⟨60722, false, false, [], [1, 5]⟩,
        ⟨60689, false, false, [], [1, 5]⟩,
        ⟨60689, false, false, [], [1, 5]⟩,
        ⟨60723, false, false, [], [5]⟩,
        ⟨60724, false, false, [], [5]⟩,
        ⟨60685, false, false, [], [5]⟩,
        ⟨60685, false, false, [], [5]⟩,
        ⟨60683, false, false, [], []⟩,
        ⟨60682, false, false, [], []⟩,
        ⟨60682, false, false, [], []⟩
      ]⟩,
    ⟨[90463, 3], [90461], .contexts [
        ⟨60679, false, false, [], []⟩
      ]⟩,
    ⟨[90461], [90461], .contexts []⟩,
    ⟨[90457], [90457], .contexts []⟩,
    ⟨[90457, 13], [90455], .contexts [
        ⟨60668, false, false, [], []⟩
      ]⟩,
    ⟨[90453], [90453], .contexts []⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1
    ], [90453], .contexts [
        ⟨60725, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨60726, false, false, [], [1, 15, 13, 1]⟩,
        ⟨60727, false, false, [], [1, 15, 13, 1]⟩,
        ⟨60678, false, false, [], [1, 15, 13, 1]⟩,
        ⟨60678, false, false, [], [1, 15, 13, 1]⟩,
        ⟨60676, false, false, [], [15, 13, 1]⟩,
        ⟨60675, false, false, [], [15, 13, 1]⟩,
        ⟨60675, false, false, [], [15, 13, 1]⟩,
        ⟨60672, false, false, [], [13, 1]⟩,
        ⟨60728, false, false, [], [13, 1]⟩,
        ⟨60671, false, false, [], [13, 1]⟩,
        ⟨60671, false, false, [], [13, 1]⟩,
        ⟨60729, false, false, [], [1]⟩,
        ⟨60667, false, false, [], [1]⟩,
        ⟨60667, false, false, [], [1]⟩,
        ⟨60664, false, false, [], []⟩,
        ⟨60730, false, false, [], []⟩,
        ⟨60663, false, false, [], []⟩,
        ⟨60663, false, false, [], []⟩
      ]⟩,
    ⟨[90451], [90451], .contexts []⟩,
    ⟨[90451, 9], [90449], .contexts [
        ⟨60657, false, false, [], []⟩
      ]⟩,
    ⟨[90449], [90449], .contexts []⟩,
    ⟨[90449, 1], [90447], .contexts [
        ⟨60653, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 949. -/
def y322TCIndexRaw949 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90447], [90447], .contexts []⟩,
    ⟨[90447, 5], [90445], .contexts [
        ⟨60650, false, false, [], []⟩
      ]⟩,
    ⟨[90445], [90445], .contexts []⟩,
    ⟨[90445, 3], [90443], .contexts [
        ⟨60646, false, false, [], []⟩
      ]⟩,
    ⟨[90443], [90443], .contexts []⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3
    ], [90443], .contexts [
        ⟨60731, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨60661, false, false, [], [9, 1, 5, 3]⟩,
        ⟨60732, false, false, [], [9, 1, 5, 3]⟩,
        ⟨60660, false, false, [], [9, 1, 5, 3]⟩,
        ⟨60660, false, false, [], [9, 1, 5, 3]⟩,
        ⟨60733, false, false, [], [1, 5, 3]⟩,
        ⟨60734, false, false, [], [1, 5, 3]⟩,
        ⟨60656, false, false, [], [1, 5, 3]⟩,
        ⟨60656, false, false, [], [1, 5, 3]⟩,
        ⟨60735, false, false, [], [5, 3]⟩,
        ⟨60736, false, false, [], [5, 3]⟩,
        ⟨60652, false, false, [], [5, 3]⟩,
        ⟨60652, false, false, [], [5, 3]⟩,
        ⟨60737, false, false, [], [3]⟩,
        ⟨60738, false, false, [], [3]⟩,
        ⟨60649, false, false, [], [3]⟩,
        ⟨60649, false, false, [], [3]⟩,
        ⟨60739, false, false, [], []⟩,
        ⟨60740, false, false, [], []⟩,
        ⟨60645, false, false, [], []⟩,
        ⟨60645, false, false, [], []⟩
      ]⟩,
    ⟨[90443, 1], [90441], .contexts [
        ⟨60642, false, false, [], []⟩
      ]⟩,
    ⟨[90441], [90441], .contexts []⟩,
    ⟨[90441, 15], [90439], .contexts [
        ⟨60638, false, false, [], []⟩
      ]⟩,
    ⟨[90439], [90439], .contexts []⟩,
    ⟨[90437], [90437], .contexts []⟩,
    ⟨[90437, 1], [90435], .contexts [
        ⟨60630, false, false, [], [1]⟩,
        ⟨8, false, false, [90435], []⟩,
        ⟨60631, false, false, [], []⟩
      ]⟩,
    ⟨[90435], [90435], .contexts []⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [90433], .contexts [
        ⟨60741, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨60742, false, false, [], [15, 13, 1, 11]⟩,
        ⟨60743, false, false, [], [15, 13, 1, 11]⟩,
        ⟨60641, false, false, [], [15, 13, 1, 11]⟩,
        ⟨60641, false, false, [], [15, 13, 1, 11]⟩,
        ⟨60744, false, false, [], [13, 1, 11]⟩,
        ⟨60745, false, false, [], [13, 1, 11]⟩,
        ⟨60637, false, false, [], [13, 1, 11]⟩,
        ⟨60637, false, false, [], [13, 1, 11]⟩,
        ⟨60634, false, false, [], [1, 11]⟩,
        ⟨60746, false, false, [], [1, 11]⟩,
        ⟨60633, false, false, [], [1, 11]⟩,
        ⟨60633, false, false, [], [1, 11]⟩,
        ⟨60747, false, false, [], [11]⟩,
        ⟨60748, false, false, [], [11]⟩,
        ⟨60631, false, false, [], [11]⟩,
        ⟨60631, false, false, [], [11]⟩,
        ⟨60629, false, false, [], []⟩,
        ⟨60628, false, false, [], []⟩,
        ⟨60628, false, false, [], []⟩
      ]⟩,
    ⟨[90431], [90431], .contexts []⟩,
    ⟨[90429], [90429], .contexts []⟩,
    ⟨[90427], [90427], .contexts []⟩,
    ⟨[90423], [90423], .contexts []⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1
    ], [90423], .contexts [
        ⟨60749, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨60625, false, false, [], [1, 5, 3, 1]⟩,
        ⟨60750, false, false, [], [1, 5, 3, 1]⟩,
        ⟨60624, false, false, [], [1, 5, 3, 1]⟩,
        ⟨60624, false, false, [], [1, 5, 3, 1]⟩,
        ⟨60622, false, false, [], [5, 3, 1]⟩,
        ⟨60751, false, false, [], [5, 3, 1]⟩,
        ⟨60621, false, false, [], [5, 3, 1]⟩,
        ⟨60621, false, false, [], [5, 3, 1]⟩,
        ⟨60619, false, false, [], [3, 1]⟩,
        ⟨60752, false, false, [], [3, 1]⟩,
        ⟨60618, false, false, [], [3, 1]⟩,
        ⟨60618, false, false, [], [3, 1]⟩,
        ⟨60615, false, false, [], [1]⟩,
        ⟨60614, false, false, [], [1]⟩,
        ⟨60614, false, false, [], [1]⟩,
        ⟨60611, false, false, [], []⟩,
        ⟨60753, false, false, [], []⟩,
        ⟨60610, false, false, [], []⟩,
        ⟨60610, false, false, [], []⟩
      ]⟩,
    ⟨[90421], [90421], .contexts []⟩,
    ⟨[90419], [90419], .contexts []⟩,
    ⟨[90417], [90417], .contexts []⟩,
    ⟨[90415], [90415], .contexts []⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [90413], .contexts [
        ⟨60754, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨60608, false, false, [], [13, 1, 11, 9]⟩,
        ⟨60755, false, false, [], [13, 1, 11, 9]⟩,
        ⟨60607, false, false, [], [13, 1, 11, 9]⟩,
        ⟨60607, false, false, [], [13, 1, 11, 9]⟩,
        ⟨60605, false, false, [], [1, 11, 9]⟩,
        ⟨60756, false, false, [], [1, 11, 9]⟩,
        ⟨60604, false, false, [], [1, 11, 9]⟩,
        ⟨60604, false, false, [], [1, 11, 9]⟩,
        ⟨60601, false, false, [], [11, 9]⟩,
        ⟨60757, false, false, [], [11, 9]⟩,
        ⟨60600, false, false, [], [11, 9]⟩,
        ⟨60600, false, false, [], [11, 9]⟩,
        ⟨60598, false, false, [], [9]⟩,
        ⟨60758, false, false, [], [9]⟩,
        ⟨60597, false, false, [], [9]⟩,
        ⟨60597, false, false, [], [9]⟩,
        ⟨60594, false, false, [], []⟩,
        ⟨60593, false, false, [], []⟩,
        ⟨60593, false, false, [], []⟩
      ]⟩,
    ⟨[90411], [90411], .contexts []⟩,
    ⟨[90409], [90409], .contexts []⟩,
    ⟨[90407], [90407], .contexts []⟩,
    ⟨[90405], [90405], .contexts []⟩,
    ⟨[90403], [90403], .contexts []⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15
    ], [90403], .contexts [
        ⟨60759, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨60590, false, false, [], [5, 3, 1, 15]⟩,
        ⟨60760, false, false, [], [5, 3, 1, 15]⟩,
        ⟨60589, false, false, [], [5, 3, 1, 15]⟩,
        ⟨60589, false, false, [], [5, 3, 1, 15]⟩,
        ⟨60587, false, false, [], [3, 1, 15]⟩,
        ⟨60761, false, false, [], [3, 1, 15]⟩,
        ⟨60586, false, false, [], [3, 1, 15]⟩,
        ⟨60586, false, false, [], [3, 1, 15]⟩,
        ⟨60583, false, false, [], [1, 15]⟩,
        ⟨60762, false, false, [], [1, 15]⟩,
        ⟨60582, false, false, [], [1, 15]⟩,
        ⟨60582, false, false, [], [1, 15]⟩,
        ⟨60580, false, false, [], [15]⟩,
        ⟨60763, false, false, [], [15]⟩,
        ⟨60579, false, false, [], [15]⟩,
        ⟨60579, false, false, [], [15]⟩,
        ⟨60577, false, false, [], []⟩,
        ⟨60764, false, false, [], []⟩,
        ⟨60576, false, false, [], []⟩,
        ⟨60576, false, false, [], []⟩
      ]⟩,
    ⟨[90401], [90401], .contexts []⟩,
    ⟨[90397], [90397], .contexts []⟩,
    ⟨[90395], [90395], .contexts []⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9
    ], [90395], .contexts [
        ⟨60765, false, false, [], [13, 1, 11, 9]⟩,
        ⟨60573, true, false, [], [13, 1, 11, 9]⟩,
        ⟨59, false, false, [90401], [1, 11, 9]⟩,
        ⟨60574, false, false, [], [1, 11, 9]⟩,
        ⟨60766, false, false, [], [1, 11, 9]⟩,
        ⟨60574, false, false, [], [1, 11, 9]⟩,
        ⟨60574, false, false, [], [1, 11, 9]⟩,
        ⟨60571, false, false, [], [11, 9]⟩,
        ⟨60570, false, false, [], [11, 9]⟩,
        ⟨60570, false, false, [], [11, 9]⟩,
        ⟨60566, true, false, [], [11, 9]⟩,
        ⟨53, false, false, [90397], [9]⟩,
        ⟨60567, false, false, [], [9]⟩,
        ⟨60767, false, false, [], [9]⟩,
        ⟨60567, false, false, [], [9]⟩,
        ⟨60567, false, false, [], [9]⟩,
        ⟨60564, false, false, [], []⟩,
        ⟨60768, false, false, [], []⟩,
        ⟨60563, false, false, [], []⟩,
        ⟨60563, false, false, [], []⟩
      ]⟩,
    ⟨[90389], [90389], .contexts []⟩,
    ⟨[90387], [90387], .contexts []⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [90385], .contexts [
        ⟨60769, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨60560, false, false, [], [5, 3, 1, 15]⟩,
        ⟨60559, false, false, [], [5, 3, 1, 15]⟩,
        ⟨60559, false, false, [], [5, 3, 1, 15]⟩,
        ⟨60555, true, false, [], [5, 3, 1, 15]⟩,
        ⟨28, false, false, [90391], [3, 1, 15]⟩,
        ⟨60556, false, false, [], [3, 1, 15]⟩,
        ⟨60556, false, false, [], [3, 1, 15]⟩,
        ⟨60556, false, false, [], [3, 1, 15]⟩,
        ⟨60553, false, false, [], [1, 15]⟩,
        ⟨60770, false, false, [], [1, 15]⟩,
        ⟨60552, false, false, [], [1, 15]⟩,
        ⟨60552, false, false, [], [1, 15]⟩,
        ⟨60549, false, false, [], [15]⟩,
        ⟨60771, false, false, [], [15]⟩,
        ⟨60548, false, false, [], [15]⟩,
        ⟨60548, false, false, [], [15]⟩,
        ⟨60545, false, false, [], []⟩,
        ⟨60544, false, false, [], []⟩,
        ⟨60544, false, false, [], []⟩
      ]⟩,
    ⟨[90383], [90383], .contexts []⟩,
    ⟨[90381], [90381], .contexts []⟩,
    ⟨[90379], [90379], .contexts []⟩,
    ⟨[90379, 9], [90377], .contexts [
        ⟨60529, false, false, [], []⟩
      ]⟩,
    ⟨[90377], [90377], .contexts []⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1
    ], [90375], .contexts [
        ⟨60772, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨60541, false, false, [], [1, 11, 9, 1]⟩,
        ⟨60773, false, false, [], [1, 11, 9, 1]⟩,
        ⟨60540, false, false, [], [1, 11, 9, 1]⟩,
        ⟨60540, false, false, [], [1, 11, 9, 1]⟩,
        ⟨60537, false, false, [], [11, 9, 1]⟩,
        ⟨60774, false, false, [], [11, 9, 1]⟩,
        ⟨60536, false, false, [], [11, 9, 1]⟩,
        ⟨60536, false, false, [], [11, 9, 1]⟩,
        ⟨60533, false, false, [], [9, 1]⟩,
        ⟨60775, false, false, [], [9, 1]⟩,
        ⟨60532, false, false, [], [9, 1]⟩,
        ⟨60532, false, false, [], [9, 1]⟩,
        ⟨60776, false, false, [], [1]⟩,
        ⟨60777, false, false, [], [1]⟩,
        ⟨60528, false, false, [], [1]⟩,
        ⟨60528, false, false, [], [1]⟩,
        ⟨60524, true, false, [], [1]⟩,
        ⟨8, false, false, [90375], []⟩,
        ⟨60525, false, false, [], []⟩,
        ⟨60525, false, false, [], []⟩,
        ⟨60525, false, false, [], []⟩
      ]⟩,
    ⟨[90373], [90373], .contexts []⟩,
    ⟨[90371, 1], [90369], .contexts [
        ⟨60516, false, false, [], []⟩
      ]⟩,
    ⟨[90369], [90369], .contexts []⟩,
    ⟨[90367], [90367], .contexts []⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15
    ], [90367], .contexts [
        ⟨60778, false, false, [], [5, 3, 1, 15]⟩,
        ⟨60521, true, false, [], [5, 3, 1, 15]⟩,
        ⟨28, false, false, [90373], [3, 1, 15]⟩,
        ⟨60522, false, false, [], [3, 1, 15]⟩,
        ⟨60779, false, false, [], [3, 1, 15]⟩,
        ⟨60522, false, false, [], [3, 1, 15]⟩,
        ⟨60522, false, false, [], [3, 1, 15]⟩,
        ⟨60518, true, false, [], [3, 1, 15]⟩,
        ⟨20, false, false, [90371], [1, 15]⟩,
        ⟨60519, false, false, [], [1, 15]⟩,
        ⟨60519, false, false, [], [1, 15]⟩,
        ⟨60519, false, false, [], [1, 15]⟩,
        ⟨60780, false, false, [], [15]⟩,
        ⟨60781, false, false, [], [15]⟩,
        ⟨60515, false, false, [], [15]⟩,
        ⟨60515, false, false, [], [15]⟩,
        ⟨60512, false, false, [], []⟩,
        ⟨60782, false, false, [], []⟩,
        ⟨60511, false, false, [], []⟩,
        ⟨60511, false, false, [], []⟩
      ]⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [15817, 90363], .contexts [
        ⟨60783, false, false, [], [13, 1, 11]⟩,
        ⟨60508, true, false, [], [13, 1, 11]⟩,
        ⟨59, false, false, [90365], [1, 11]⟩,
        ⟨60503, false, false, [], [1, 11]⟩,
        ⟨60502, false, false, [], [1, 11]⟩,
        ⟨60503, false, false, [], [1, 11]⟩,
        ⟨60503, false, false, [], [1, 11]⟩,
        ⟨60503, true, false, [], [1, 11]⟩,
        ⟨60503, true, false, [], [1, 11]⟩,
        ⟨60502, true, false, [], [1, 11]⟩,
        ⟨60501, true, false, [], [1, 11]⟩,
        ⟨562, false, false, [90363], [11]⟩,
        ⟨563, false, false, [90363], [11]⟩,
        ⟨60506, false, false, [], [11]⟩,
        ⟨18737, true, false, [], [90365, 11]⟩,
        ⟨60504, false, false, [], [11]⟩,
        ⟨60505, false, false, [], [11]⟩,
        ⟨60505, false, false, [], [11]⟩,
        ⟨60501, true, false, [15817], [11]⟩,
        ⟨53, false, false, [15817, 90363], []⟩,
        ⟨60491, false, false, [15817], []⟩,
        ⟨60495, false, false, [], []⟩,
        ⟨60496, false, false, [], []⟩,
        ⟨60498, false, false, [], []⟩
      ]⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3
    ], [15817, 83963], .contexts [
        ⟨60784, false, false, [], [9, 1, 5, 3]⟩,
        ⟨60489, true, false, [15817], [9, 1, 5, 3]⟩,
        ⟨46, false, false, [15817, 90361], [1, 5, 3]⟩,
        ⟨60492, false, false, [], [1, 5, 3]⟩,
        ⟨60493, false, false, [], [1, 5, 3]⟩,
        ⟨60494, false, false, [], [1, 5, 3]⟩,
        ⟨60487, false, false, [15817], [5, 3]⟩,
        ⟨60482, false, false, [], [5, 3]⟩,
        ⟨60483, false, false, [], [5, 3]⟩,
        ⟨60484, false, false, [], [5, 3]⟩,
        ⟨60477, true, false, [15817], [5, 3]⟩,
        ⟨28, false, false, [15817, 90357], [3]⟩,
        ⟨60457, false, false, [15817], [3]⟩,
        ⟨60464, false, false, [], [3]⟩,
        ⟨60465, false, false, [], [3]⟩,
        ⟨60466, false, false, [], [3]⟩,
        ⟨60455, false, false, [15817], []⟩,
        ⟨24236, false, false, [], []⟩,
        ⟨24237, false, false, [], []⟩,
        ⟨24238, false, false, [], []⟩
      ]⟩,
    ⟨[24959], [15817, 15811], .source 12544⟩,
    ⟨[24961], [24959, 17725], .source 12545⟩,
    ⟨[24963], [24961, 17711], .source 12546⟩,
    ⟨[24965], [24963, 17705], .source 12547⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11
    ], [24965, 84837], .contexts [
        ⟨60785, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨24227, false, false, [15817], [15, 13, 1, 11]⟩,
        ⟨60786, true, false, [], [83963, 15, 13, 1, 11]⟩,
        ⟨60452, false, false, [24959], [13, 1, 11]⟩,
        ⟨60787, true, false, [], [90355, 13, 1, 11]⟩,
        ⟨60447, false, false, [24961], [1, 11]⟩,
        ⟨60788, true, false, [], [90355, 1, 11]⟩,
        ⟨60429, false, false, [24963], [11]⟩,
        ⟨60789, true, false, [], [90355, 11]⟩,
        ⟨60422, false, false, [24965], []⟩
      ]⟩,
    ⟨[24967], [24965, 17707], .source 12548⟩,
    ⟨[24969], [24967, 17641], .source 12549⟩,
    ⟨[24971], [24969, 17647], .source 12550⟩,
    ⟨[24973], [24971, 17645], .source 12551⟩,
    ⟨[24975], [24973, 15839], .source 12552⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1
    ], [24975, 83207], .contexts [
        ⟨60790, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨29047, false, false, [24965], [1, 5, 3, 1]⟩,
        ⟨60791, true, false, [], [84843, 1, 5, 3, 1]⟩,
        ⟨28986, false, false, [24967], [5, 3, 1]⟩,
        ⟨60792, true, false, [], [84847, 5, 3, 1]⟩,
        ⟨28932, false, false, [24969], [3, 1]⟩,
        ⟨60793, true, false, [], [84847, 3, 1]⟩,
        ⟨28914, false, false, [24971], [1]⟩,
        ⟨60794, true, false, [], [83211, 1]⟩,
        ⟨20000, false, false, [24973], []⟩,
        ⟨60795, true, false, [], [83207]⟩
      ]⟩,
    ⟨[24977], [24975, 15841], .source 12553⟩,
    ⟨[24979], [24977, 16135], .source 12554⟩,
    ⟨[24981], [24979, 31], .source 12555⟩]

/-- Exact literal claimed equations and contextual derivations, block 950. -/
def y322TCIndexRaw950 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[24983], [24981, 245], .source 12556⟩,
    ⟨[24985], [24983, 15325], .source 12557⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9
    ], [24985, 83509], .contexts [
        ⟨60796, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨20133, false, false, [24975], [13, 1, 11, 9]⟩,
        ⟨60797, true, false, [], [83221, 13, 1, 11, 9]⟩,
        ⟨20619, false, false, [24977], [1, 11, 9]⟩,
        ⟨60798, true, false, [], [83339, 1, 11, 9]⟩,
        ⟨20604, false, false, [24979], [11, 9]⟩,
        ⟨443, true, false, [24979], [83339, 11, 9]⟩,
        ⟨60799, true, false, [], [83339, 11, 9]⟩,
        ⟨20613, false, false, [24981], [9]⟩,
        ⟨60800, true, false, [], [83339, 9]⟩,
        ⟨21784, false, false, [24983], []⟩,
        ⟨60801, true, false, [], [83509]⟩
      ]⟩,
    ⟨[24987], [24985, 14709], .source 12558⟩,
    ⟨[24989], [24987, 15253], .source 12559⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [24989, 82673], .contexts [
        ⟨60802, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨21800, false, false, [24985], [5, 3, 1, 15]⟩,
        ⟨21793, false, false, [24985], [3, 1, 15]⟩,
        ⟨5198, false, false, [24985], [1, 15]⟩,
        ⟨14539, false, false, [24985], [15]⟩,
        ⟨60803, true, false, [], [79185, 15]⟩,
        ⟨15234, false, false, [24987], []⟩,
        ⟨60804, true, false, [], [82673]⟩
      ]⟩,
    ⟨[24991], [24989, 743], .source 12560⟩,
    ⟨[24993], [24991, 15211], .source 12561⟩,
    ⟨[24995], [24993, 15311], .source 12562⟩,
    ⟨[24995, 82701], [24995, 82701], .contexts []⟩,
    ⟨[24995, 82701], [24995, 82701], .contexts []⟩,
    ⟨[24995, 82701], [24995, 82701], .contexts []⟩,
    ⟨[
      90477, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1
    ], [24995, 82701], .contexts [
        ⟨60805, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨15229, false, false, [24989], [1, 11, 9, 1]⟩,
        ⟨60806, true, false, [], [82673, 1, 11, 9, 1]⟩,
        ⟨16831, false, false, [24991], [11, 9, 1]⟩,
        ⟨60807, true, false, [], [82805, 11, 9, 1]⟩,
        ⟨16825, false, false, [24993], [9, 1]⟩,
        ⟨15450, false, false, [24993], [1]⟩,
        ⟨60808, true, false, [], [82691, 1]⟩,
        ⟨15562, false, false, [24995], []⟩,
        ⟨60809, false, false, [], []⟩,
        ⟨60810, false, false, [], []⟩,
        ⟨60811, false, false, [], []⟩
      ]⟩,
    ⟨[24995, 82703], [24995, 82703], .contexts []⟩,
    ⟨[24995, 82703], [24995, 82703], .contexts []⟩,
    ⟨[90479, 3], [90479, 3], .contexts []⟩,
    ⟨[90479, 3], [24995, 82703], .contexts [
        ⟨60815, false, false, [], []⟩,
        ⟨60712, true, false, [], [3]⟩,
        ⟨60712, true, false, [], [3]⟩,
        ⟨60711, true, false, [], [3]⟩,
        ⟨60710, true, false, [], [3]⟩,
        ⟨1908, false, false, [90477], []⟩,
        ⟨1909, false, false, [90477], []⟩,
        ⟨60812, false, false, [], [5]⟩,
        ⟨15574, false, false, [24995], []⟩,
        ⟨60813, false, false, [], []⟩,
        ⟨60814, false, false, [], []⟩,
        ⟨15585, false, false, [24995], []⟩,
        ⟨13, true, false, [], [24995, 82703]⟩
      ]⟩,
    ⟨[24997], [24994], .source 12563⟩,
    ⟨[82703, 3], [24997, 90479], .contexts [
        ⟨60816, true, false, [24994], [3]⟩,
        ⟨20, false, false, [24994, 90479], []⟩,
        ⟨60817, true, false, [], [90479]⟩
      ]⟩,
    ⟨[90477], [90477], .contexts []⟩,
    ⟨[90479, 1], [90477], .contexts [
        ⟨60709, false, false, [], []⟩,
        ⟨60819, false, false, [], []⟩,
        ⟨60708, false, false, [], []⟩,
        ⟨60708, false, false, [], []⟩
      ]⟩,
    ⟨[90479, 3], [24995, 82703], .contexts [
        ⟨60815, false, false, [], []⟩,
        ⟨60816, false, false, [], []⟩,
        ⟨60813, false, false, [], []⟩,
        ⟨60814, false, false, [], []⟩,
        ⟨60814, false, false, [], []⟩
      ]⟩,
    ⟨[24999], [24995, 22957], .source 12564⟩,
    ⟨[25001], [24999, 22967], .source 12565⟩,
    ⟨[90477, 3], [90477, 3], .contexts []⟩,
    ⟨[25001], [25001], .contexts [
        ⟨13, false, false, [], [25001]⟩
      ]⟩,
    ⟨[90477, 3], [25001, 88597], .contexts [
        ⟨60824, false, false, [], []⟩,
        ⟨60820, true, false, [], [3]⟩,
        ⟨1098, false, false, [90479], []⟩,
        ⟨1100, false, false, [90479], []⟩,
        ⟨60821, false, false, [], [1, 3, 1]⟩,
        ⟨15580, false, false, [24995], [3, 1]⟩,
        ⟨51230, false, false, [24995], [1]⟩,
        ⟨60822, true, false, [], [88601, 1]⟩,
        ⟨51050, false, false, [24999], []⟩,
        ⟨51278, false, false, [24999], []⟩,
        ⟨60823, true, false, [], [88597]⟩,
        ⟨51267, false, false, [25001], []⟩,
        ⟨60825, true, false, [], [88597]⟩
      ]⟩,
    ⟨[25003], [25000], .source 12566⟩,
    ⟨[88597, 3], [25003, 90477], .contexts [
        ⟨60826, true, false, [25000], [3]⟩,
        ⟨20, false, false, [25000, 90477], []⟩,
        ⟨60827, true, false, [], [90477]⟩
      ]⟩,
    ⟨[25005], [24995, 9937], .source 12567⟩,
    ⟨[25007], [25005, 24997], .source 12568⟩,
    ⟨[90479], [90479], .contexts []⟩,
    ⟨[25007, 90479, 5], [90479], .contexts [
        ⟨60830, false, false, [], [90479, 5]⟩,
        ⟨60818, true, false, [25005], [5]⟩,
        ⟨15574, true, false, [25005], [3, 5]⟩,
        ⟨60829, false, false, [], [82701, 5, 3, 5]⟩,
        ⟨15565, true, false, [24995], [5, 3, 5]⟩,
        ⟨60811, true, false, [], [3, 5, 3, 5]⟩,
        ⟨60810, true, false, [], [3, 5, 3, 5]⟩,
        ⟨60809, true, false, [], [3, 5, 3, 5]⟩,
        ⟨15575, true, false, [24995], [3, 5, 3, 5]⟩,
        ⟨60821, true, false, [], [5, 3, 5, 3, 5]⟩,
        ⟨1919, false, false, [90479], []⟩,
        ⟨60831, false, false, [], []⟩
      ]⟩,
    ⟨[90479, 5], [90479, 5], .contexts []⟩,
    ⟨[90479], [90479], .contexts []⟩,
    ⟨[25009], [25006], .source 12569⟩,
    ⟨[25006], [25006], .contexts []⟩,
    ⟨[25009], [25006], .contexts [
        ⟨60835, false, false, [], []⟩,
        ⟨60836, false, false, [], []⟩,
        ⟨60836, false, false, [], []⟩
      ]⟩,
    ⟨[90479, 5], [25009, 90479], .contexts [
        ⟨60833, false, false, [], []⟩,
        ⟨60832, false, false, [25006], []⟩,
        ⟨60834, false, false, [25006], []⟩,
        ⟨60837, true, false, [], [90479]⟩
      ]⟩,
    ⟨[24994], [24994], .contexts []⟩,
    ⟨[88609, 7], [24997, 90479], .contexts [
        ⟨51818, true, false, [], [7]⟩,
        ⟨15588, true, false, [], [3, 7]⟩,
        ⟨60821, true, false, [24994], [7, 3, 7]⟩,
        ⟨18135, false, false, [24994, 90479], []⟩,
        ⟨60831, false, false, [24994], []⟩,
        ⟨60834, false, false, [24994], []⟩,
        ⟨60839, true, false, [], [90479]⟩,
        ⟨60839, true, false, [], [90479]⟩,
        ⟨60817, true, false, [], [90479]⟩
      ]⟩,
    ⟨[25011], [24995, 15531], .source 12570⟩,
    ⟨[25013], [25011, 19023], .source 12571⟩,
    ⟨[25015], [25012], .source 12572⟩,
    ⟨[25012], [25012], .contexts []⟩,
    ⟨[86329, 9], [25015, 90479], .contexts [
        ⟨60842, false, false, [25012], [86329, 9]⟩,
        ⟨36437, true, false, [25012, 25011], [9]⟩,
        ⟨60841, false, false, [25012], [82813, 3, 9]⟩,
        ⟨16949, true, false, [25012, 24995], [3, 9]⟩,
        ⟨60821, true, false, [25012], [9, 3, 9]⟩,
        ⟨1612, false, false, [25012, 90479], []⟩,
        ⟨60831, false, false, [25012], []⟩,
        ⟨60834, false, false, [25012], []⟩,
        ⟨60844, true, false, [], [90479]⟩,
        ⟨60844, true, false, [], [90479]⟩,
        ⟨60843, true, false, [], [90479]⟩
      ]⟩,
    ⟨[90479, 9], [25013, 86329], .contexts [
        ⟨60845, true, false, [25014], [9]⟩,
        ⟨46, false, false, [25014, 86329], []⟩,
        ⟨60843, false, true, [], [86329]⟩
      ]⟩,
    ⟨[25017], [24995, 9927], .source 12573⟩,
    ⟨[25019], [25017, 24997], .source 12574⟩,
    ⟨[25021], [25018], .source 12575⟩,
    ⟨[25018], [25018], .contexts []⟩,
    ⟨[90479, 11], [25021, 90479], .contexts [
        ⟨60848, false, false, [25018], [90479, 11]⟩,
        ⟨60818, true, false, [25018, 25017], [11]⟩,
        ⟨60847, false, false, [25018], [82703, 3, 11]⟩,
        ⟨15586, true, false, [25018, 24995], [3, 11]⟩,
        ⟨60821, true, false, [25018], [11, 3, 11]⟩,
        ⟨1693, false, false, [25018, 90479], []⟩,
        ⟨60831, false, false, [25018], []⟩,
        ⟨60834, false, false, [25018], []⟩,
        ⟨60850, true, false, [], [90479]⟩,
        ⟨60850, true, false, [], [90479]⟩,
        ⟨60849, true, false, [], [90479]⟩
      ]⟩,
    ⟨[25001, 88597], [25001, 88597], .contexts []⟩,
    ⟨[25001, 88597], [25001, 88597], .contexts []⟩,
    ⟨[90477, 3], [25001, 88597], .contexts [
        ⟨60824, false, false, [], []⟩,
        ⟨60826, false, false, [], []⟩,
        ⟨60852, false, false, [], []⟩,
        ⟨60853, false, false, [], []⟩,
        ⟨60853, false, false, [], []⟩
      ]⟩,
    ⟨[25023], [23575, 23565], .source 12576⟩,
    ⟨[25025], [25001, 25023], .source 12577⟩,
    ⟨[25027], [25025, 24455], .source 12578⟩,
    ⟨[90477], [90477], .contexts []⟩,
    ⟨[89971, 7], [89971, 7], .contexts []⟩,
    ⟨[90477], [90477], .contexts []⟩,
    ⟨[25029], [25026], .source 12579⟩,
    ⟨[25026], [25026], .contexts []⟩,
    ⟨[89971, 7], [25029, 90477], .contexts [
        ⟨60859, false, false, [], []⟩,
        ⟨60857, false, false, [25026], [89971, 7]⟩,
        ⟨58355, true, false, [25026, 25025], [7]⟩,
        ⟨60856, false, false, [25026], [89099, 3, 7]⟩,
        ⟨60855, false, false, [25026, 25001], [89099, 3, 7]⟩,
        ⟨54134, true, false, [25026, 25001, 23575], [3, 7]⟩,
        ⟨54118, true, false, [25026, 25001], [3, 7]⟩,
        ⟨60854, true, false, [25026], [7, 3, 7]⟩,
        ⟨18135, false, false, [25026, 90477], []⟩,
        ⟨60858, false, false, [25026], []⟩,
        ⟨60860, false, false, [25026], []⟩,
        ⟨60862, true, false, [], [90477]⟩,
        ⟨60862, true, false, [], [90477]⟩,
        ⟨60861, true, false, [], [90477]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 951. -/
def y322TCIndexRaw951 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[25027], [25028], .contexts [
        ⟨60861, true, true, [], []⟩
      ]⟩,
    ⟨[90477, 7], [25027, 89971], .contexts [
        ⟨60863, true, false, [25028], [7]⟩,
        ⟨38, false, false, [25028, 89971], []⟩,
        ⟨60864, true, false, [], [89971]⟩
      ]⟩,
    ⟨[25031], [25001, 22967], .source 12580⟩,
    ⟨[25033], [25031, 25003], .source 12581⟩,
    ⟨[90477, 11], [90477, 11], .contexts []⟩,
    ⟨[25035], [25032], .source 12582⟩,
    ⟨[25035], [25035], .contexts []⟩,
    ⟨[25032], [25032], .contexts []⟩,
    ⟨[25035], [25032], .contexts [
        ⟨60870, false, false, [], []⟩,
        ⟨60869, false, false, [], []⟩,
        ⟨60871, false, false, [], []⟩,
        ⟨60871, false, false, [], []⟩
      ]⟩,
    ⟨[90477, 11], [25035, 90477], .contexts [
        ⟨60868, false, false, [], []⟩,
        ⟨60867, false, false, [25032], [90477, 11]⟩,
        ⟨60828, true, false, [25032, 25031], [11]⟩,
        ⟨60866, false, false, [25032], [88597, 3, 11]⟩,
        ⟨51278, true, false, [25032, 25001], [3, 11]⟩,
        ⟨51045, true, false, [25032, 25001], [3, 11]⟩,
        ⟨60854, true, false, [25032], [11, 3, 11]⟩,
        ⟨1693, false, false, [25032, 90477], []⟩,
        ⟨60858, false, false, [25032], []⟩,
        ⟨60860, false, false, [25032], []⟩,
        ⟨60872, true, false, [], [90477]⟩
      ]⟩,
    ⟨[25037], [25001, 22921], .source 12583⟩,
    ⟨[25039], [25037, 25003], .source 12584⟩,
    ⟨[90477, 13], [90477, 13], .contexts []⟩,
    ⟨[25041], [25038], .source 12585⟩,
    ⟨[25038], [25038], .contexts []⟩,
    ⟨[25041], [25038], .contexts [
        ⟨60877, false, false, [], []⟩,
        ⟨60878, false, false, [], []⟩,
        ⟨60878, false, false, [], []⟩
      ]⟩,
    ⟨[90477, 13], [25041, 90477], .contexts [
        ⟨60876, false, false, [], []⟩,
        ⟨60875, false, false, [25038], [90477, 13]⟩,
        ⟨60828, true, false, [25038, 25037], [13]⟩,
        ⟨60874, false, false, [25038], [88597, 3, 13]⟩,
        ⟨51268, true, false, [25038, 25001], [3, 13]⟩,
        ⟨60854, true, false, [25038], [13, 3, 13]⟩,
        ⟨1930, false, false, [25038, 90477], []⟩,
        ⟨60858, false, false, [25038], []⟩,
        ⟨60860, false, false, [25038], []⟩,
        ⟨60879, true, false, [], [90477]⟩
      ]⟩,
    ⟨[25009, 90479], [25009, 90479], .contexts []⟩,
    ⟨[25009, 90479], [25009, 90479], .contexts []⟩,
    ⟨[90477, 5], [90477, 5], .contexts []⟩,
    ⟨[25008], [25008], .contexts []⟩,
    ⟨[25007], [25008], .contexts [
        ⟨60835, true, true, [], []⟩,
        ⟨60884, false, false, [], []⟩,
        ⟨60884, false, false, [], []⟩
      ]⟩,
    ⟨[90477, 5], [25007, 90477], .contexts [
        ⟨60883, false, false, [], []⟩,
        ⟨60709, true, false, [], [5]⟩,
        ⟨60882, true, false, [25008], [1, 5]⟩,
        ⟨60882, true, false, [25008], [1, 5]⟩,
        ⟨60881, true, false, [25008], [1, 5]⟩,
        ⟨60838, true, false, [25008], [1, 5]⟩,
        ⟨60833, true, false, [25008], [1, 5]⟩,
        ⟨890, false, false, [25008, 90479], []⟩,
        ⟨9, false, false, [25008, 90479], []⟩,
        ⟨60820, false, false, [25008], []⟩,
        ⟨60860, false, false, [25008], []⟩,
        ⟨60885, true, false, [], [90477]⟩
      ]⟩,
    ⟨[25029, 90477], [25029, 90477], .contexts []⟩,
    ⟨[25029, 90477], [25029, 90477], .contexts []⟩,
    ⟨[90475, 7], [90475, 7], .contexts []⟩,
    ⟨[25043], [25027, 24443], .source 12586⟩,
    ⟨[90475, 7], [25043, 84383], .contexts [
        ⟨60889, false, false, [], []⟩,
        ⟨60705, true, false, [], [7]⟩,
        ⟨60888, true, false, [25028], [15, 7]⟩,
        ⟨60888, true, false, [25028], [15, 7]⟩,
        ⟨60887, true, false, [25028], [15, 7]⟩,
        ⟨60863, true, false, [25028], [15, 7]⟩,
        ⟨60859, true, false, [25028], [15, 7]⟩,
        ⟨18155, false, false, [25028, 89971], []⟩,
        ⟨10, false, false, [25028, 89971], []⟩,
        ⟨58348, false, false, [25028], []⟩,
        ⟨26707, false, false, [25028, 24443], []⟩,
        ⟨60864, true, false, [], [24443, 84383]⟩,
        ⟨60890, true, false, [], [84383]⟩
      ]⟩,
    ⟨[25045], [25042], .source 12587⟩,
    ⟨[84383, 7], [25045, 90475], .contexts [
        ⟨60891, true, false, [25042], [7]⟩,
        ⟨38, false, false, [25042, 90475], []⟩,
        ⟨60892, true, false, [], [90475]⟩
      ]⟩,
    ⟨[90477, 11], [25035, 90477], .contexts [
        ⟨60873, false, false, [], []⟩
      ]⟩,
    ⟨[25035, 90477], [25035, 90477], .contexts []⟩,
    ⟨[25035, 90477], [25035, 90477], .contexts []⟩,
    ⟨[90477, 14], [90477, 15], .contexts [
        ⟨10, false, false, [90477], []⟩
      ]⟩,
    ⟨[90475, 11], [90475, 11], .contexts []⟩,
    ⟨[90475], [90475], .contexts []⟩,
    ⟨[25033], [25034], .contexts [
        ⟨60869, true, true, [], []⟩
      ]⟩,
    ⟨[25034], [25034], .contexts []⟩,
    ⟨[25033], [25034], .contexts [
        ⟨60900, false, false, [], []⟩,
        ⟨60901, false, false, [], []⟩,
        ⟨60901, false, false, [], []⟩
      ]⟩,
    ⟨[90475, 11], [25033, 90475], .contexts [
        ⟨60898, false, false, [], []⟩,
        ⟨60705, true, false, [], [11]⟩,
        ⟨60896, true, false, [25034], [15, 11]⟩,
        ⟨60896, true, false, [25034], [15, 11]⟩,
        ⟨60895, true, false, [25034], [15, 11]⟩,
        ⟨60894, true, false, [25034], [15, 11]⟩,
        ⟨60868, true, false, [25034], [15, 11]⟩,
        ⟨615, false, false, [25034, 90477], []⟩,
        ⟨60897, false, false, [25034], []⟩,
        ⟨60714, false, false, [25034], []⟩,
        ⟨60899, false, false, [25034], []⟩,
        ⟨60902, true, false, [], [90475]⟩
      ]⟩,
    ⟨[25041, 90477], [25041, 90477], .contexts []⟩,
    ⟨[25041, 90477], [25041, 90477], .contexts []⟩,
    ⟨[90477, 13], [25041, 90477], .contexts [
        ⟨60876, false, false, [], []⟩,
        ⟨60880, false, false, [], []⟩,
        ⟨60904, false, false, [], []⟩,
        ⟨60905, false, false, [], []⟩,
        ⟨60905, false, false, [], []⟩
      ]⟩,
    ⟨[90473, 15], [90473, 15], .contexts []⟩,
    ⟨[90473], [90473], .contexts []⟩,
    ⟨[25040], [25040], .contexts []⟩,
    ⟨[90473, 15], [25039, 90473], .contexts [
        ⟨60907, false, false, [], []⟩,
        ⟨60701, true, false, [], [15]⟩,
        ⟨60705, true, false, [], [13, 15]⟩,
        ⟨60906, true, false, [25040], [15, 13, 15]⟩,
        ⟨2022, false, false, [25040, 90477], []⟩,
        ⟨89, false, false, [25040, 90477], []⟩,
        ⟨60717, false, false, [25040], []⟩,
        ⟨60908, false, false, [25040], []⟩,
        ⟨60909, true, false, [], [90473]⟩,
        ⟨60909, true, false, [], [90473]⟩,
        ⟨60877, false, true, [], [90473]⟩
      ]⟩,
    ⟨[25007, 90477], [25007, 90477], .contexts []⟩,
    ⟨[25007, 90477], [25007, 90477], .contexts []⟩,
    ⟨[90477, 5], [25007, 90477], .contexts [
        ⟨60883, false, false, [], []⟩,
        ⟨60886, false, false, [], []⟩,
        ⟨60911, false, false, [], []⟩,
        ⟨60912, false, false, [], []⟩,
        ⟨60912, false, false, [], []⟩
      ]⟩,
    ⟨[90475, 5], [90475, 5], .contexts []⟩,
    ⟨[90475, 5], [25009, 90475], .contexts [
        ⟨60914, false, false, [], []⟩,
        ⟨60705, true, false, [], [5]⟩,
        ⟨60913, true, false, [25006], [15, 5]⟩,
        ⟨1204, false, false, [25006, 90477], []⟩,
        ⟨60897, false, false, [25006], []⟩,
        ⟨60714, false, false, [25006], []⟩,
        ⟨60899, false, false, [25006], []⟩,
        ⟨60837, true, false, [], [90475]⟩
      ]⟩,
    ⟨[25043, 84383], [25043, 84383], .contexts []⟩,
    ⟨[25043, 84383], [25043, 84383], .contexts []⟩,
    ⟨[90475, 7], [25043, 84383], .contexts [
        ⟨60889, false, false, [], []⟩,
        ⟨60891, false, false, [], []⟩,
        ⟨60916, false, false, [], []⟩,
        ⟨60917, false, false, [], []⟩,
        ⟨60917, false, false, [], []⟩
      ]⟩,
    ⟨[25043, 89211], [25043, 89211], .contexts []⟩,
    ⟨[25043, 89211], [25043, 89211], .contexts []⟩,
    ⟨[90475, 13], [90473], .contexts [
        ⟨60715, false, false, [], []⟩,
        ⟨60716, false, false, [], []⟩,
        ⟨60700, false, false, [], []⟩,
        ⟨60700, false, false, [], []⟩
      ]⟩,
    ⟨[90475, 12], [90475, 13], .contexts [
        ⟨64, false, false, [90475], []⟩
      ]⟩,
    ⟨[89211, 7], [89211, 7], .contexts []⟩,
    ⟨[25042], [25042], .contexts []⟩,
    ⟨[89211, 7], [25045, 90473], .contexts [
        ⟨60923, false, false, [], []⟩,
        ⟨60920, true, false, [25042], [7]⟩,
        ⟨60919, true, false, [25042], [7]⟩,
        ⟨54860, true, false, [], [7]⟩,
        ⟨60918, true, false, [25042], [13, 7]⟩,
        ⟨518, false, false, [25042, 90475], []⟩,
        ⟨60922, false, false, [25042], []⟩,
        ⟨60921, false, false, [25042], []⟩,
        ⟨60908, false, false, [25042], []⟩,
        ⟨60924, true, false, [], [90473]⟩,
        ⟨60924, true, false, [], [90473]⟩,
        ⟨60892, true, false, [], [90473]⟩
      ]⟩,
    ⟨[25043], [25044], .contexts [
        ⟨60892, true, true, [], []⟩
      ]⟩,
    ⟨[90473, 7], [25043, 89211], .contexts [
        ⟨60925, true, false, [25044], [7]⟩,
        ⟨38, false, false, [25044, 89211], []⟩,
        ⟨60926, true, false, [], [89211]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 952. -/
def y322TCIndexRaw952 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[25033, 90475], [25033, 90475], .contexts []⟩,
    ⟨[25033, 90475], [25033, 90475], .contexts []⟩,
    ⟨[90475, 11], [25033, 90475], .contexts [
        ⟨60898, false, false, [], []⟩,
        ⟨60903, false, false, [], []⟩,
        ⟨60928, false, false, [], []⟩,
        ⟨60929, false, false, [], []⟩,
        ⟨60929, false, false, [], []⟩
      ]⟩,
    ⟨[25033, 90473], [25033, 90473], .contexts []⟩,
    ⟨[25033, 90473], [25033, 90473], .contexts []⟩,
    ⟨[90473, 11], [90473, 11], .contexts []⟩,
    ⟨[90473, 11], [25035, 90473], .contexts [
        ⟨60933, false, false, [], []⟩,
        ⟨60932, true, false, [25032], [11]⟩,
        ⟨60931, true, false, [25032], [11]⟩,
        ⟨60701, true, false, [], [11]⟩,
        ⟨60930, true, false, [25032], [13, 11]⟩,
        ⟨619, false, false, [25032, 90475], []⟩,
        ⟨60922, false, false, [25032], []⟩,
        ⟨60921, false, false, [25032], []⟩,
        ⟨60908, false, false, [25032], []⟩,
        ⟨60872, true, false, [], [90473]⟩
      ]⟩,
    ⟨[25039, 90473], [25039, 90473], .contexts []⟩,
    ⟨[25039, 90473], [25039, 90473], .contexts []⟩,
    ⟨[90473, 15], [25039, 90473], .contexts [
        ⟨60907, false, false, [], []⟩,
        ⟨60910, false, false, [], []⟩,
        ⟨60935, false, false, [], []⟩,
        ⟨60936, false, false, [], []⟩,
        ⟨60936, false, false, [], []⟩
      ]⟩,
    ⟨[90473, 1], [90471], .contexts [
        ⟨60718, false, false, [], []⟩
      ]⟩,
    ⟨[90473, 1], [90471], .contexts [
        ⟨60938, false, false, [], []⟩,
        ⟨60719, false, false, [], []⟩,
        ⟨60696, false, false, [], []⟩,
        ⟨60696, false, false, [], []⟩
      ]⟩,
    ⟨[90473, 0], [90473, 1], .contexts [
        ⟨9, false, false, [90473], []⟩
      ]⟩,
    ⟨[25009, 90475], [25009, 90475], .contexts []⟩,
    ⟨[25009, 90475], [25009, 90475], .contexts []⟩,
    ⟨[90475, 5], [25009, 90475], .contexts [
        ⟨60914, false, false, [], []⟩,
        ⟨60915, false, false, [], []⟩,
        ⟨60941, false, false, [], []⟩,
        ⟨60942, false, false, [], []⟩,
        ⟨60942, false, false, [], []⟩
      ]⟩,
    ⟨[90473, 5], [90473, 5], .contexts []⟩,
    ⟨[90473, 5], [25007, 90473], .contexts [
        ⟨60944, false, false, [], []⟩,
        ⟨60701, true, false, [], [5]⟩,
        ⟨60943, true, false, [25008], [13, 5]⟩,
        ⟨913, false, false, [25008, 90475], []⟩,
        ⟨60922, false, false, [25008], []⟩,
        ⟨60921, false, false, [25008], []⟩,
        ⟨60908, false, false, [25008], []⟩,
        ⟨60885, true, false, [], [90473]⟩
      ]⟩,
    ⟨[25045, 90473], [25045, 90473], .contexts []⟩,
    ⟨[25045, 90473], [25045, 90473], .contexts []⟩,
    ⟨[25043], [25044], .contexts [
        ⟨60926, false, false, [], []⟩
      ]⟩,
    ⟨[25044], [25044], .contexts []⟩,
    ⟨[90471, 7], [25043, 89213], .contexts [
        ⟨60697, true, false, [], [7]⟩,
        ⟨60947, true, false, [25044], [1, 7]⟩,
        ⟨60947, true, false, [25044], [1, 7]⟩,
        ⟨60946, true, false, [25044], [1, 7]⟩,
        ⟨60925, true, false, [25044], [1, 7]⟩,
        ⟨60923, true, false, [25044], [1, 7]⟩,
        ⟨502, false, false, [25044, 89211], []⟩,
        ⟨9, false, false, [25044, 89211], []⟩,
        ⟨54890, false, false, [25044], []⟩,
        ⟨54897, false, false, [25044], []⟩,
        ⟨60949, true, false, [], [89213]⟩,
        ⟨60949, true, false, [], [89213]⟩,
        ⟨60948, true, false, [], [89213]⟩
      ]⟩,
    ⟨[89213, 7], [25045, 90471], .contexts [
        ⟨60950, true, false, [25042], [7]⟩,
        ⟨38, false, false, [25042, 90471], []⟩,
        ⟨60892, true, false, [], [90471]⟩
      ]⟩,
    ⟨[25035, 90473], [25035, 90473], .contexts []⟩,
    ⟨[25035, 90473], [25035, 90473], .contexts []⟩,
    ⟨[25035, 90469], [25035, 90469], .contexts []⟩,
    ⟨[25035, 90469], [25035, 90469], .contexts []⟩,
    ⟨[90469, 1], [90469, 1], .contexts []⟩,
    ⟨[90469, 1], [25033, 90473], .contexts [
        ⟨60956, false, false, [], []⟩,
        ⟨60955, true, false, [25034], [1]⟩,
        ⟨60954, true, false, [25034], [1]⟩,
        ⟨60694, true, false, [], [1]⟩,
        ⟨60697, true, false, [], [11, 1]⟩,
        ⟨60953, true, false, [25034], [1, 11, 1]⟩,
        ⟨60953, true, false, [25034], [1, 11, 1]⟩,
        ⟨60952, true, false, [25034], [1, 11, 1]⟩,
        ⟨60934, true, false, [25034], [1, 11, 1]⟩,
        ⟨60933, true, false, [25034], [1, 11, 1]⟩,
        ⟨628, false, false, [25034, 90473], []⟩,
        ⟨60908, false, false, [25034], []⟩,
        ⟨60902, true, false, [], [90473]⟩
      ]⟩,
    ⟨[25035], [25035], .contexts []⟩,
    ⟨[25035], [25035], .contexts []⟩,
    ⟨[90471], [25035, 90469], .contexts [
        ⟨60939, true, false, [], []⟩,
        ⟨60957, true, false, [25032], [1]⟩,
        ⟨8, false, false, [25032, 90469], []⟩,
        ⟨60869, true, false, [], [90469]⟩,
        ⟨60954, false, false, [], []⟩,
        ⟨60959, true, false, [], [90469]⟩,
        ⟨60958, true, false, [], [90469]⟩,
        ⟨60870, true, false, [], [90469]⟩
      ]⟩,
    ⟨[90471], [25035, 90469], .contexts [
        ⟨60960, false, false, [], []⟩
      ]⟩,
    ⟨[90471], [25035, 90469], .contexts [
        ⟨60961, false, false, [], []⟩,
        ⟨60955, false, false, [], []⟩
      ]⟩,
    ⟨[25047], [25033, 25041], .source 12588⟩,
    ⟨[25049], [25047, 25035], .source 12589⟩,
    ⟨[90469, 15], [25049, 90469], .contexts [
        ⟨60960, true, false, [25034], [15]⟩,
        ⟨60697, true, false, [25034], [15]⟩,
        ⟨60937, true, false, [25034, 25038], [1, 15]⟩,
        ⟨1666, false, false, [25034, 25038, 90473], []⟩,
        ⟨60940, false, false, [25034, 25038], []⟩,
        ⟨60939, false, false, [25034, 25038], []⟩,
        ⟨60879, true, false, [25034], [90471]⟩,
        ⟨60962, false, false, [25034, 25041], []⟩,
        ⟨60900, true, false, [], [25041, 25035, 90469]⟩,
        ⟨60963, true, false, [], [25035, 90469]⟩,
        ⟨60964, true, false, [], [90469]⟩
      ]⟩,
    ⟨[25051], [25033, 25043], .source 12590⟩,
    ⟨[90469, 7], [25051, 89213], .contexts [
        ⟨60960, true, false, [25034], [7]⟩,
        ⟨60950, false, false, [25034], []⟩,
        ⟨60900, true, false, [], [25043, 89213]⟩,
        ⟨60966, true, false, [], [89213]⟩
      ]⟩,
    ⟨[25049, 90469], [25049, 90469], .contexts []⟩,
    ⟨[25049, 90469], [25049, 90469], .contexts []⟩,
    ⟨[90469, 9], [90467], .contexts [
        ⟨60721, false, false, [], []⟩,
        ⟨60722, false, false, [], []⟩,
        ⟨60689, false, false, [], []⟩,
        ⟨60689, false, false, [], []⟩
      ]⟩,
    ⟨[90469, 8], [90469, 9], .contexts [
        ⟨47, false, false, [90469], []⟩
      ]⟩,
    ⟨[90467, 15], [90467, 15], .contexts []⟩,
    ⟨[90467], [90467], .contexts []⟩,
    ⟨[25053], [25048], .source 12591⟩,
    ⟨[25048], [25048], .contexts []⟩,
    ⟨[90467, 15], [25053, 90467], .contexts [
        ⟨60972, false, false, [], []⟩,
        ⟨60690, true, false, [], [15]⟩,
        ⟨60969, true, false, [25048], [9, 15]⟩,
        ⟨60969, true, false, [25048], [9, 15]⟩,
        ⟨60968, true, false, [25048], [9, 15]⟩,
        ⟨60965, true, false, [25048], [9, 15]⟩,
        ⟨1671, false, false, [25048, 90469], []⟩,
        ⟨60971, false, false, [25048], []⟩,
        ⟨60970, false, false, [25048], []⟩,
        ⟨60973, false, false, [25048], []⟩,
        ⟨60975, true, false, [], [90467]⟩,
        ⟨60975, true, false, [], [90467]⟩,
        ⟨60974, true, false, [], [90467]⟩
      ]⟩,
    ⟨[25007, 90473], [25007, 90473], .contexts []⟩,
    ⟨[25007, 90473], [25007, 90473], .contexts []⟩,
    ⟨[90473, 5], [25007, 90473], .contexts [
        ⟨60944, false, false, [], []⟩,
        ⟨60945, false, false, [], []⟩,
        ⟨60977, false, false, [], []⟩,
        ⟨60978, false, false, [], []⟩,
        ⟨60978, false, false, [], []⟩
      ]⟩,
    ⟨[25055], [25007, 25035], .source 12592⟩,
    ⟨[90471], [25035, 90469], .contexts [
        ⟨60962, false, false, [], []⟩
      ]⟩,
    ⟨[90469, 5], [90469, 5], .contexts []⟩,
    ⟨[90469], [90469], .contexts []⟩,
    ⟨[25057], [25054], .source 12593⟩,
    ⟨[25059], [25057, 25035], .source 12594⟩,
    ⟨[90469, 5], [25059, 90469], .contexts [
        ⟨60982, false, false, [], []⟩,
        ⟨60980, false, false, [25054], [90469, 5]⟩,
        ⟨60962, true, false, [25054, 25007], [5]⟩,
        ⟨60697, true, false, [25054, 25007], [5]⟩,
        ⟨60979, true, false, [25054], [1, 5]⟩,
        ⟨890, false, false, [25054, 90473], []⟩,
        ⟨60940, false, false, [25054], []⟩,
        ⟨60938, false, false, [25054], []⟩,
        ⟨60981, false, false, [25054], []⟩,
        ⟨60955, false, false, [25054], []⟩,
        ⟨60955, false, false, [25054], []⟩,
        ⟨60983, false, false, [25054, 25035], []⟩,
        ⟨60984, true, false, [], [25035, 90469]⟩,
        ⟨60985, true, false, [], [90469]⟩
      ]⟩,
    ⟨[25051, 89213], [25051, 89213], .contexts []⟩,
    ⟨[25051, 89213], [25051, 89213], .contexts []⟩,
    ⟨[90469, 7], [25051, 89213], .contexts [
        ⟨60967, false, false, [], []⟩,
        ⟨60987, false, false, [], []⟩,
        ⟨60988, false, false, [], []⟩,
        ⟨60988, false, false, [], []⟩
      ]⟩,
    ⟨[25061], [25051, 23789], .source 12595⟩,
    ⟨[25063], [25045, 25035], .source 12596⟩]

/-- Exact literal claimed equations and contextual derivations, block 953. -/
def y322TCIndexRaw953 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[25065], [25061, 25063], .source 12597⟩,
    ⟨[90469, 3], [90469, 3], .contexts []⟩,
    ⟨[25067], [25064], .source 12598⟩,
    ⟨[25064], [25064], .contexts []⟩,
    ⟨[90469, 3], [25067, 90469], .contexts [
        ⟨60993, false, false, [], []⟩,
        ⟨60992, false, false, [25064], [90469, 3]⟩,
        ⟨60991, false, false, [25064, 25061], [90469, 3]⟩,
        ⟨60962, true, false, [25064, 25061, 25045], [3]⟩,
        ⟨60951, true, false, [25064, 25061], [3]⟩,
        ⟨60990, false, false, [25064], [89213, 7, 3]⟩,
        ⟨54923, true, false, [25064, 25051], [7, 3]⟩,
        ⟨60989, true, false, [25064], [3, 7, 3]⟩,
        ⟨40656, false, false, [25064, 90469], []⟩,
        ⟨60983, false, false, [25064], []⟩,
        ⟨60995, true, false, [], [90469]⟩,
        ⟨60995, true, false, [], [90469]⟩,
        ⟨60994, true, false, [], [90469]⟩
      ]⟩,
    ⟨[25069], [25051, 24449], .source 12599⟩,
    ⟨[89961, 7], [89961, 7], .contexts []⟩,
    ⟨[25071], [25068], .source 12600⟩,
    ⟨[25068], [25068], .contexts []⟩,
    ⟨[89961, 7], [25071, 90467], .contexts [
        ⟨60998, false, false, [], []⟩,
        ⟨60997, false, false, [25068], [89961, 7]⟩,
        ⟨58346, true, false, [25068, 25051], [7]⟩,
        ⟨60989, true, false, [25068], [9, 7]⟩,
        ⟨579, false, false, [25068, 90469], []⟩,
        ⟨60971, false, false, [25068], []⟩,
        ⟨60970, false, false, [25068], []⟩,
        ⟨60973, false, false, [25068], []⟩,
        ⟨61000, true, false, [], [90467]⟩,
        ⟨61000, true, false, [], [90467]⟩,
        ⟨60999, true, false, [], [90467]⟩
      ]⟩,
    ⟨[25069], [25070], .contexts [
        ⟨60999, true, true, [], []⟩
      ]⟩,
    ⟨[25067, 90469], [25067, 90469], .contexts []⟩,
    ⟨[25067, 90469], [25067, 90469], .contexts []⟩,
    ⟨[25067, 90467], [25067, 90467], .contexts []⟩,
    ⟨[25067, 90467], [25067, 90467], .contexts []⟩,
    ⟨[90467, 3], [90467, 3], .contexts []⟩,
    ⟨[25067], [25067], .contexts [
        ⟨13, false, false, [], [25067]⟩
      ]⟩,
    ⟨[90467, 3], [25067, 90467], .contexts [
        ⟨61007, false, false, [], []⟩,
        ⟨60970, true, false, [], [3]⟩,
        ⟨196, false, false, [90469], []⟩,
        ⟨197, false, false, [90469], []⟩,
        ⟨60993, false, false, [], [9]⟩,
        ⟨60996, false, false, [], [9]⟩,
        ⟨61003, false, false, [], [9]⟩,
        ⟨61004, false, false, [], [9]⟩,
        ⟨61004, false, false, [], [9]⟩,
        ⟨60690, false, false, [25067], []⟩,
        ⟨61005, false, false, [], []⟩,
        ⟨61006, false, false, [], []⟩,
        ⟨60973, false, false, [25067], []⟩,
        ⟨61008, true, false, [], [90467]⟩
      ]⟩,
    ⟨[25059, 90469], [25059, 90469], .contexts []⟩,
    ⟨[25059, 90469], [25059, 90469], .contexts []⟩,
    ⟨[25059, 90467], [25059, 90467], .contexts []⟩,
    ⟨[25059, 90467], [25059, 90467], .contexts []⟩,
    ⟨[90467, 5], [90467, 5], .contexts []⟩,
    ⟨[25059], [25059], .contexts []⟩,
    ⟨[25059], [25059], .contexts []⟩,
    ⟨[25059], [25059], .contexts [
        ⟨13, false, false, [], [25059]⟩,
        ⟨61015, false, false, [], []⟩,
        ⟨61016, false, false, [], []⟩
      ]⟩,
    ⟨[90467, 5], [25059, 90467], .contexts [
        ⟨61014, false, false, [], []⟩,
        ⟨60970, true, false, [], [5]⟩,
        ⟨1079, false, false, [90469], []⟩,
        ⟨1080, false, false, [90469], []⟩,
        ⟨60982, false, false, [], [9]⟩,
        ⟨60986, false, false, [], [9]⟩,
        ⟨61010, false, false, [], [9]⟩,
        ⟨61011, false, false, [], [9]⟩,
        ⟨61011, false, false, [], [9]⟩,
        ⟨60690, false, false, [25059], []⟩,
        ⟨61012, false, false, [], []⟩,
        ⟨61013, false, false, [], []⟩,
        ⟨60973, false, false, [25059], []⟩,
        ⟨61017, true, false, [], [90467]⟩
      ]⟩,
    ⟨[25053, 90467], [25053, 90467], .contexts []⟩,
    ⟨[25053, 90467], [25053, 90467], .contexts []⟩,
    ⟨[90467, 15], [25053, 90467], .contexts [
        ⟨60972, false, false, [], []⟩,
        ⟨60976, false, false, [], []⟩,
        ⟨61019, false, false, [], []⟩,
        ⟨61020, false, false, [], []⟩,
        ⟨61020, false, false, [], []⟩
      ]⟩,
    ⟨[90467, 1], [90465], .contexts [
        ⟨60723, false, false, [], []⟩,
        ⟨60724, false, false, [], []⟩,
        ⟨60685, false, false, [], []⟩,
        ⟨60685, false, false, [], []⟩
      ]⟩,
    ⟨[25052], [25052], .contexts []⟩,
    ⟨[25071, 90467], [25071, 90467], .contexts []⟩,
    ⟨[25071, 90467], [25071, 90467], .contexts []⟩,
    ⟨[25070], [25070], .contexts []⟩,
    ⟨[90465, 7], [25069, 89959], .contexts [
        ⟨60686, true, false, [], [7]⟩,
        ⟨61025, true, false, [25070], [1, 7]⟩,
        ⟨61025, true, false, [25070], [1, 7]⟩,
        ⟨61024, true, false, [25070], [1, 7]⟩,
        ⟨61001, true, false, [25070], [1, 7]⟩,
        ⟨60998, true, false, [25070], [1, 7]⟩,
        ⟨502, false, false, [25070, 89961], []⟩,
        ⟨58405, false, false, [25070], []⟩,
        ⟨58404, false, false, [25070], []⟩,
        ⟨58407, false, false, [25070], []⟩,
        ⟨61026, true, false, [], [89959]⟩,
        ⟨61026, true, false, [], [89959]⟩,
        ⟨61002, true, false, [], [89959]⟩
      ]⟩,
    ⟨[90467, 5], [25059, 90467], .contexts [
        ⟨61014, false, false, [], []⟩,
        ⟨61018, false, false, [], []⟩,
        ⟨61012, false, false, [], []⟩,
        ⟨61013, false, false, [], []⟩,
        ⟨61013, false, false, [], []⟩
      ]⟩,
    ⟨[25059, 90463], [25059, 90463], .contexts []⟩,
    ⟨[25059, 90463], [25059, 90463], .contexts []⟩,
    ⟨[90463, 1], [90463, 1], .contexts []⟩,
    ⟨[25073], [25058], .source 12601⟩,
    ⟨[25073], [25058], .contexts [
        ⟨61032, false, false, [], []⟩
      ]⟩,
    ⟨[25058], [25058], .contexts []⟩,
    ⟨[90463, 1], [25073, 90467], .contexts [
        ⟨61031, false, false, [], []⟩,
        ⟨61030, true, false, [25058], [1]⟩,
        ⟨61029, true, false, [25058], [1]⟩,
        ⟨60683, true, false, [], [1]⟩,
        ⟨60686, true, false, [], [5, 1]⟩,
        ⟨61028, true, false, [25058], [1, 5, 1]⟩,
        ⟨874, false, false, [25058, 90467], []⟩,
        ⟨60973, false, false, [25058], []⟩,
        ⟨61034, true, false, [], [90467]⟩,
        ⟨61034, true, false, [], [90467]⟩,
        ⟨61033, true, false, [], [90467]⟩
      ]⟩,
    ⟨[90465], [25059, 90463], .contexts [
        ⟨61022, true, false, [], []⟩,
        ⟨61035, true, false, [25072], [1]⟩,
        ⟨8, false, false, [25072, 90463], []⟩,
        ⟨61032, false, true, [], [90463]⟩,
        ⟨61029, false, false, [], []⟩,
        ⟨61016, true, false, [], [90463]⟩,
        ⟨61015, true, false, [], [90463]⟩
      ]⟩,
    ⟨[90465], [25059, 90463], .contexts [
        ⟨61036, false, false, [], []⟩
      ]⟩,
    ⟨[90465], [25059, 90463], .contexts [
        ⟨61037, false, false, [], []⟩,
        ⟨61030, false, false, [], []⟩
      ]⟩,
    ⟨[25075], [25073, 25049], .source 12602⟩,
    ⟨[25077], [25075, 25059], .source 12603⟩,
    ⟨[90463, 15], [25077, 90463], .contexts [
        ⟨61036, true, false, [25058], [15]⟩,
        ⟨60686, true, false, [25058], [15]⟩,
        ⟨61021, true, false, [25058, 25052], [1, 15]⟩,
        ⟨1666, false, false, [25058, 25052, 90467], []⟩,
        ⟨9, false, false, [25058, 25052, 90467], []⟩,
        ⟨61022, false, false, [25058, 25052], []⟩,
        ⟨61023, true, false, [25058], [90465]⟩,
        ⟨61023, true, false, [25058], [90465]⟩,
        ⟨60974, false, true, [25058], [90465]⟩,
        ⟨61038, false, false, [25058, 25049], []⟩,
        ⟨61032, true, false, [], [25049, 25059, 90463]⟩,
        ⟨61039, true, false, [], [25059, 90463]⟩,
        ⟨61040, true, false, [], [90463]⟩
      ]⟩,
    ⟨[25079], [25073, 25069], .source 12604⟩,
    ⟨[90463, 7], [25079, 89959], .contexts [
        ⟨61036, true, false, [25058], [7]⟩,
        ⟨61027, false, false, [25058], []⟩,
        ⟨61032, true, false, [], [25069, 89959]⟩,
        ⟨61042, true, false, [], [89959]⟩
      ]⟩,
    ⟨[25077, 90463], [25077, 90463], .contexts []⟩,
    ⟨[25077, 90463], [25077, 90463], .contexts []⟩,
    ⟨[90463, 3], [90461], .contexts [
        ⟨60726, false, false, [], []⟩
      ]⟩,
    ⟨[90463, 3], [90461], .contexts [
        ⟨61046, false, false, [], []⟩,
        ⟨60727, false, false, [], []⟩,
        ⟨60678, false, false, [], []⟩,
        ⟨60678, false, false, [], []⟩
      ]⟩,
    ⟨[25081], [25076], .source 12605⟩,
    ⟨[25076], [25076], .contexts []⟩,
    ⟨[25079, 89959], [25079, 89959], .contexts []⟩,
    ⟨[25079, 89959], [25079, 89959], .contexts []⟩,
    ⟨[90463, 7], [25079, 89959], .contexts [
        ⟨61043, false, false, [], []⟩,
        ⟨61050, false, false, [], []⟩,
        ⟨61051, false, false, [], []⟩,
        ⟨61051, false, false, [], []⟩
      ]⟩,
    ⟨[25083], [25079, 24493], .source 12606⟩,
    ⟨[25085], [25083, 24089], .source 12607⟩,
    ⟨[90463], [90463], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 954. -/
def y322TCIndexRaw954 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90463], [90463], .contexts []⟩,
    ⟨[25087], [25084], .source 12608⟩,
    ⟨[25084], [25084], .contexts []⟩,
    ⟨[89423, 13], [25087, 90463], .contexts [
        ⟨61054, false, false, [25084], [89423, 13]⟩,
        ⟨56088, true, false, [25084, 25083], [13]⟩,
        ⟨61053, false, false, [25084], [83617, 7, 13]⟩,
        ⟨58400, true, false, [25084, 25079], [7, 13]⟩,
        ⟨61052, true, false, [25084], [13, 7, 13]⟩,
        ⟨15654, false, false, [25084, 90463], []⟩,
        ⟨61055, false, false, [25084], []⟩,
        ⟨61056, false, false, [25084], []⟩,
        ⟨61058, true, false, [], [90463]⟩,
        ⟨61058, true, false, [], [90463]⟩,
        ⟨61057, true, false, [], [90463]⟩
      ]⟩,
    ⟨[90463, 13], [25085, 89423], .contexts [
        ⟨61059, true, false, [25086], [13]⟩,
        ⟨59, false, false, [25086, 89423], []⟩,
        ⟨61057, false, true, [], [89423]⟩
      ]⟩,
    ⟨[25073, 90467], [25073, 90467], .contexts []⟩,
    ⟨[25073, 90467], [25073, 90467], .contexts []⟩,
    ⟨[25089], [25073, 25067], .source 12609⟩,
    ⟨[25091], [25089, 25059], .source 12610⟩,
    ⟨[25091, 90459], [25091, 90459], .contexts []⟩,
    ⟨[25091, 90459], [25091, 90459], .contexts []⟩,
    ⟨[90463, 1, 3, 1, 3, 1], [25091, 90459], .contexts [
        ⟨61031, false, false, [], [3, 1, 3, 1]⟩,
        ⟨61035, false, false, [], [3, 1, 3, 1]⟩,
        ⟨61061, false, false, [], [3, 1, 3, 1]⟩,
        ⟨61062, false, false, [], [3, 1, 3, 1]⟩,
        ⟨61062, false, false, [], [3, 1, 3, 1]⟩,
        ⟨61009, false, false, [25073], [1, 3, 1]⟩,
        ⟨61063, true, false, [], [90467, 1, 3, 1]⟩,
        ⟨60686, false, false, [25089], [3, 1]⟩,
        ⟨61038, false, false, [25089], [3, 1]⟩,
        ⟨61064, true, false, [], [90463, 3, 1]⟩,
        ⟨60679, false, false, [25091], [1]⟩,
        ⟨60676, false, false, [25091], []⟩,
        ⟨61065, false, false, [], []⟩,
        ⟨61066, false, false, [], []⟩
      ]⟩,
    ⟨[25093], [25090], .source 12611⟩,
    ⟨[25090], [25090], .contexts []⟩,
    ⟨[90459, 3], [25093, 90463], .contexts [
        ⟨61067, true, false, [25090], [3]⟩,
        ⟨4083, false, false, [25090, 90463], []⟩,
        ⟨61055, false, false, [25090], []⟩,
        ⟨61056, false, false, [25090], []⟩,
        ⟨61069, true, false, [], [90463]⟩,
        ⟨61069, true, false, [], [90463]⟩,
        ⟨61068, true, false, [], [90463]⟩
      ]⟩,
    ⟨[90461], [25091, 90459], .contexts [
        ⟨61047, true, false, [], []⟩,
        ⟨61070, true, false, [25092], [3]⟩,
        ⟨20, false, false, [25092, 90459], []⟩,
        ⟨61068, false, true, [], [90459]⟩,
        ⟨61065, false, false, [], []⟩
      ]⟩,
    ⟨[90461], [25091, 90459], .contexts [
        ⟨61071, false, false, [], []⟩,
        ⟨61066, false, false, [], []⟩
      ]⟩,
    ⟨[25095], [25081, 25091], .source 12612⟩,
    ⟨[25097], [25093, 25095], .source 12613⟩,
    ⟨[90459], [25096, 90457], .contexts [
        ⟨61074, false, false, [25096], [90459]⟩,
        ⟨61068, false, false, [25096], [25095, 90459]⟩,
        ⟨61073, false, false, [25096, 25090], [90459]⟩,
        ⟨61072, true, false, [25096, 25090, 25081], []⟩,
        ⟨61048, false, false, [25096, 25090], [90461]⟩,
        ⟨61049, false, false, [25096, 25090], [90461]⟩,
        ⟨61049, false, false, [25096, 25090], [90461]⟩,
        ⟨61047, true, false, [25096, 25090, 25076], []⟩,
        ⟨21, true, false, [25096, 25090, 25076, 90463], []⟩,
        ⟨1141, true, false, [25096, 25090, 25076, 90463], []⟩,
        ⟨61041, false, false, [25096, 25090, 25076], [3, 15]⟩,
        ⟨61044, false, false, [25096, 25090, 25076], [3, 15]⟩,
        ⟨61045, false, false, [25096, 25090, 25076], [3, 15]⟩,
        ⟨61045, false, false, [25096, 25090, 25076], [3, 15]⟩,
        ⟨60679, false, false, [25096, 25090], [15]⟩,
        ⟨61072, false, false, [25096, 25090], [15]⟩,
        ⟨60672, false, false, [25096], []⟩
      ]⟩,
    ⟨[25099], [25096], .source 12614⟩,
    ⟨[90459], [25099, 90457], .contexts [
        ⟨61075, false, false, [], []⟩,
        ⟨61076, true, false, [], [90457]⟩
      ]⟩,
    ⟨[25091, 90459], [25091, 25099, 90457], .contexts [
        ⟨61077, false, false, [25091], []⟩
      ]⟩,
    ⟨[25101], [25091, 25099], .source 12615⟩,
    ⟨[90461], [25101, 90457], .contexts [
        ⟨61072, false, false, [], []⟩,
        ⟨61078, false, false, [], []⟩,
        ⟨61079, true, false, [], [90457]⟩
      ]⟩,
    ⟨[90461], [25101, 90457], .contexts [
        ⟨61080, false, false, [], []⟩
      ]⟩,
    ⟨[25097], [25098], .contexts [
        ⟨61076, true, true, [], []⟩
      ]⟩,
    ⟨[25103], [25097, 25101], .source 12616⟩,
    ⟨[90457, 1], [25103, 90457], .contexts [
        ⟨61077, true, false, [25098], [1]⟩,
        ⟨60674, false, false, [25098], []⟩,
        ⟨61081, false, false, [25098], []⟩,
        ⟨61082, true, false, [], [25101, 90457]⟩,
        ⟨61083, true, false, [], [90457]⟩
      ]⟩,
    ⟨[25105], [25097, 25093], .source 12617⟩,
    ⟨[25101, 90457], [25101, 90457], .contexts []⟩,
    ⟨[25085, 89423], [25085, 89423], .contexts []⟩,
    ⟨[89423], [89423], .contexts []⟩,
    ⟨[25107], [25100], .source 12618⟩,
    ⟨[25109], [25107, 25085], .source 12619⟩,
    ⟨[25111], [25108], .source 12620⟩,
    ⟨[89421], [25111, 90455], .contexts [
        ⟨55775, true, false, [], []⟩,
        ⟨55775, true, false, [], []⟩,
        ⟨55820, true, false, [], []⟩,
        ⟨55819, true, false, [], []⟩,
        ⟨61090, false, false, [25108], [89423, 3]⟩,
        ⟨61089, false, false, [25108], [25085, 89423, 3]⟩,
        ⟨61088, true, false, [25108, 25100, 25085], [3]⟩,
        ⟨61087, true, false, [25108, 25100], [3]⟩,
        ⟨61087, true, false, [25108, 25100], [3]⟩,
        ⟨61060, true, false, [25108, 25100], [3]⟩,
        ⟨64, true, false, [25108, 25100, 90463], [3]⟩,
        ⟨514, true, false, [25108, 25100, 90463], [3]⟩,
        ⟨61046, false, false, [25108, 25100], [13, 3, 3]⟩,
        ⟨61081, false, false, [25108, 25100], [13, 3, 3]⟩,
        ⟨61086, false, false, [25108, 25100], [13, 3, 3]⟩,
        ⟨61086, false, false, [25108, 25100], [13, 3, 3]⟩,
        ⟨60668, false, false, [25108], [3, 3]⟩,
        ⟨20, false, false, [25108, 90455], []⟩,
        ⟨61091, true, false, [], [90455]⟩
      ]⟩,
    ⟨[25111], [25111], .contexts []⟩,
    ⟨[25111], [25111], .contexts []⟩,
    ⟨[25109], [25110], .contexts [
        ⟨61091, true, true, [], []⟩
      ]⟩,
    ⟨[90455], [25109, 89421], .contexts [
        ⟨61093, false, false, [25110], [90455]⟩,
        ⟨61094, false, false, [25110], [90455]⟩,
        ⟨61092, true, false, [25110], []⟩,
        ⟨61095, true, false, [], [89421]⟩
      ]⟩,
    ⟨[25111], [25108], .contexts [
        ⟨61091, false, false, [], []⟩
      ]⟩,
    ⟨[25108], [25108], .contexts []⟩,
    ⟨[25111], [25108], .contexts [
        ⟨61097, false, false, [], []⟩,
        ⟨61098, false, false, [], []⟩,
        ⟨61098, false, false, [], []⟩
      ]⟩,
    ⟨[89421, 13], [25111, 90457], .contexts [
        ⟨61096, true, false, [25108], [13]⟩,
        ⟨60666, false, false, [25108], []⟩,
        ⟨60728, false, false, [25108], []⟩,
        ⟨61099, true, false, [], [90457]⟩
      ]⟩,
    ⟨[90455], [25109, 89421], .contexts [
        ⟨61096, false, false, [], []⟩
      ]⟩,
    ⟨[25109, 89421], [25109, 89421], .contexts []⟩,
    ⟨[90455], [25109, 89421], .contexts [
        ⟨61101, false, false, [], []⟩,
        ⟨61102, false, false, [], []⟩
      ]⟩,
    ⟨[25109, 89421, 1], [25109, 89419], .contexts [
        ⟨55772, false, false, [25109], []⟩
      ]⟩,
    ⟨[25109, 89419], [25109, 89419], .contexts []⟩,
    ⟨[25109, 89419], [25109, 89419], .contexts []⟩,
    ⟨[25109, 89419], [25109, 89419], .contexts []⟩,
    ⟨[90453], [25109, 89419], .contexts [
        ⟨61097, false, false, [25110], [90453]⟩,
        ⟨13, false, false, [25110, 25108], [90453]⟩,
        ⟨60730, true, false, [25110, 25108], []⟩,
        ⟨60664, true, false, [25110, 25108], []⟩,
        ⟨61103, false, false, [25110, 25108], [1]⟩,
        ⟨61104, false, false, [25110, 25108], []⟩,
        ⟨61105, false, false, [25110, 25108], []⟩,
        ⟨61106, false, false, [25110, 25108], []⟩,
        ⟨61107, false, false, [25110, 25108], []⟩,
        ⟨61095, true, false, [], [89419]⟩
      ]⟩,
    ⟨[89419, 11], [25111, 90451], .contexts [
        ⟨61108, true, false, [25108], [11]⟩,
        ⟨60661, false, false, [25108], []⟩,
        ⟨60732, false, false, [25108], []⟩,
        ⟨61099, true, false, [], [90451]⟩
      ]⟩,
    ⟨[25103, 90457], [25103, 90457], .contexts []⟩,
    ⟨[25103, 90457], [25103, 90457], .contexts []⟩,
    ⟨[90457, 1], [25103, 90457], .contexts [
        ⟨61084, false, false, [], []⟩,
        ⟨61110, false, false, [], []⟩,
        ⟨61111, false, false, [], []⟩,
        ⟨61111, false, false, [], []⟩
      ]⟩,
    ⟨[25113], [25103, 25109], .source 12621⟩,
    ⟨[89419, 13], [89419, 13], .contexts []⟩,
    ⟨[89419], [89419], .contexts []⟩,
    ⟨[25115], [25112], .source 12622⟩,
    ⟨[25117], [25115, 25109], .source 12623⟩,
    ⟨[89419, 13], [25117, 89419], .contexts [
        ⟨61114, false, false, [], []⟩,
        ⟨55772, true, false, [], [13]⟩,
        ⟨61113, false, false, [25112], [89421, 1, 13]⟩,
        ⟨61103, true, false, [25112, 25103], [1, 13]⟩,
        ⟨60668, true, false, [25112, 25103], [1, 13]⟩,
        ⟨61112, true, false, [25112], [13, 1, 13]⟩,
        ⟨919, false, false, [25112, 90457], []⟩,
        ⟨116, false, false, [25112, 90457], []⟩,
        ⟨60729, false, false, [25112], [1]⟩,
        ⟨61103, false, false, [25112], [1]⟩,
        ⟨61102, false, false, [25112], [1]⟩,
        ⟨61102, false, false, [25112], [1]⟩,
        ⟨61104, false, false, [25112], []⟩,
        ⟨61105, false, false, [25112], []⟩,
        ⟨61106, false, false, [25112], []⟩,
        ⟨61107, false, false, [25112], []⟩,
        ⟨61115, false, false, [25112, 25109], []⟩,
        ⟨61116, true, false, [], [25109, 89419]⟩,
        ⟨61117, true, false, [], [89419]⟩
      ]⟩,
    ⟨[89419, 15], [89417], .contexts [
        ⟨55823, false, false, [], []⟩,
        ⟨55824, false, false, [], []⟩,
        ⟨55767, false, false, [], []⟩,
        ⟨55767, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 955. -/
def y322TCIndexRaw955 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[25117, 89419], [25117, 89419], .contexts []⟩,
    ⟨[89419, 13], [25117, 89419], .contexts [
        ⟨61114, false, false, [], []⟩,
        ⟨61118, false, false, [], []⟩,
        ⟨61120, false, false, [], []⟩,
        ⟨61120, false, false, [], []⟩
      ]⟩,
    ⟨[25117, 89415], [25117, 89415], .contexts []⟩,
    ⟨[25117, 89415], [25117, 89415], .contexts []⟩,
    ⟨[89415, 15], [89415, 15], .contexts []⟩,
    ⟨[25117], [25117], .contexts []⟩,
    ⟨[25117], [25117], .contexts []⟩,
    ⟨[89419, 11], [25111, 90451], .contexts [
        ⟨61109, false, false, [], []⟩
      ]⟩,
    ⟨[25111, 90451], [25111, 90451], .contexts []⟩,
    ⟨[25111, 90451], [25111, 90451], .contexts []⟩,
    ⟨[25119], [25117, 25111], .source 12624⟩,
    ⟨[90451, 13], [90451, 13], .contexts []⟩,
    ⟨[25109], [25110], .contexts [
        ⟨61095, false, false, [], []⟩
      ]⟩,
    ⟨[25121], [25109, 25119], .source 12625⟩,
    ⟨[90451, 13], [25121, 90451], .contexts [
        ⟨61131, false, false, [], []⟩,
        ⟨61129, true, false, [25110], [13]⟩,
        ⟨61129, true, false, [25110], [13]⟩,
        ⟨61128, true, false, [25110], [13]⟩,
        ⟨61127, true, false, [25110], [13]⟩,
        ⟨227, false, false, [25110, 89419], []⟩,
        ⟨228, false, false, [25110, 89419], []⟩,
        ⟨61121, false, false, [25110], [11]⟩,
        ⟨61109, false, false, [25110, 25117], []⟩,
        ⟨61130, true, false, [25110], [90451]⟩,
        ⟨61132, true, false, [], [25119, 90451]⟩,
        ⟨61133, true, false, [], [90451]⟩
      ]⟩,
    ⟨[89415, 15, 1], [25117, 89413], .contexts [
        ⟨61124, false, false, [], [1]⟩,
        ⟨61124, false, false, [], [1]⟩,
        ⟨55763, true, false, [], [15, 1]⟩,
        ⟨55763, true, false, [], [15, 1]⟩,
        ⟨55826, true, false, [], [15, 1]⟩,
        ⟨55825, true, false, [], [15, 1]⟩,
        ⟨61119, true, false, [], [13, 15, 1]⟩,
        ⟨3049, false, false, [89419], [1]⟩,
        ⟨261, false, false, [89419], [1]⟩,
        ⟨61121, false, false, [], [15, 13, 1]⟩,
        ⟨55768, false, false, [25117], [13, 1]⟩,
        ⟨55764, false, false, [25117], [1]⟩,
        ⟨61122, false, false, [], [1]⟩,
        ⟨61123, false, false, [], [1]⟩,
        ⟨61126, true, false, [], [89415, 1]⟩,
        ⟨61125, true, false, [], [89415, 1]⟩,
        ⟨13, true, false, [], [25117, 89415, 1]⟩,
        ⟨61122, false, false, [], [1]⟩,
        ⟨61123, false, false, [], [1]⟩,
        ⟨61123, false, false, [], [1]⟩,
        ⟨55761, false, false, [25117], []⟩
      ]⟩,
    ⟨[89413, 15], [89413, 15], .contexts []⟩,
    ⟨[25123], [25116], .source 12626⟩,
    ⟨[25116], [25116], .contexts []⟩,
    ⟨[25123], [25116], .contexts [
        ⟨61137, false, false, [], []⟩,
        ⟨61138, false, false, [], []⟩,
        ⟨61138, false, false, [], []⟩
      ]⟩,
    ⟨[89413, 15], [25123, 89413], .contexts [
        ⟨61136, false, false, [], []⟩,
        ⟨61135, true, false, [25116], [15]⟩,
        ⟨1666, false, false, [25116, 89415], []⟩,
        ⟨9, false, false, [25116, 89415], []⟩,
        ⟨55828, false, false, [25116], []⟩,
        ⟨55829, false, false, [25116], []⟩,
        ⟨55760, false, false, [25116], []⟩,
        ⟨55760, false, false, [25116], []⟩,
        ⟨61139, true, false, [], [89413]⟩
      ]⟩,
    ⟨[25121, 90451], [25121, 90451], .contexts []⟩,
    ⟨[25121, 90451], [25121, 90451], .contexts []⟩,
    ⟨[90451, 9], [90449], .contexts [
        ⟨60733, false, false, [], []⟩,
        ⟨60734, false, false, [], []⟩,
        ⟨60656, false, false, [], []⟩,
        ⟨60656, false, false, [], []⟩
      ]⟩,
    ⟨[90451, 8], [90451, 9], .contexts [
        ⟨47, false, false, [90451], []⟩
      ]⟩,
    ⟨[90449], [90449], .contexts []⟩,
    ⟨[25125], [25120], .source 12627⟩,
    ⟨[25120], [25120], .contexts []⟩,
    ⟨[25123, 89413], [25123, 89413], .contexts []⟩,
    ⟨[25123, 89413], [25123, 89413], .contexts []⟩,
    ⟨[89413, 15], [25123, 89413], .contexts [
        ⟨61136, false, false, [], []⟩,
        ⟨61140, false, false, [], []⟩,
        ⟨61148, false, false, [], []⟩,
        ⟨61149, false, false, [], []⟩,
        ⟨61149, false, false, [], []⟩
      ]⟩,
    ⟨[89413, 11], [89411], .contexts [
        ⟨55830, false, false, [], []⟩,
        ⟨55831, false, false, [], []⟩,
        ⟨55756, false, false, [], []⟩,
        ⟨55756, false, false, [], []⟩
      ]⟩,
    ⟨[89411, 15], [89411, 15], .contexts []⟩,
    ⟨[89411], [89411], .contexts []⟩,
    ⟨[25117], [25122], .contexts [
        ⟨61137, true, true, [], []⟩
      ]⟩,
    ⟨[25117], [25117], .contexts []⟩,
    ⟨[25122], [25122], .contexts []⟩,
    ⟨[25117], [25122], .contexts [
        ⟨61155, false, false, [], []⟩,
        ⟨61154, false, false, [], []⟩,
        ⟨61156, false, false, [], []⟩,
        ⟨61156, false, false, [], []⟩
      ]⟩,
    ⟨[89411, 15], [25117, 89411], .contexts [
        ⟨61152, false, false, [], []⟩,
        ⟨55757, true, false, [], [15]⟩,
        ⟨61150, true, false, [25122], [11, 15]⟩,
        ⟨2046, false, false, [25122, 89413], []⟩,
        ⟨54, false, false, [25122, 89413], []⟩,
        ⟨61151, false, false, [25122], []⟩,
        ⟨61153, false, false, [25122], []⟩,
        ⟨61157, true, false, [], [89411]⟩
      ]⟩,
    ⟨[25117, 89411], [25117, 89411], .contexts []⟩,
    ⟨[25117, 89411], [25117, 89411], .contexts []⟩,
    ⟨[89411, 9], [89409], .contexts [
        ⟨55832, false, false, [], []⟩,
        ⟨55833, false, false, [], []⟩,
        ⟨55752, false, false, [], []⟩,
        ⟨55752, false, false, [], []⟩
      ]⟩,
    ⟨[89411, 8], [89411, 9], .contexts [
        ⟨47, false, false, [89411], []⟩
      ]⟩,
    ⟨[89409, 15], [89409, 15], .contexts []⟩,
    ⟨[89409], [89409], .contexts []⟩,
    ⟨[25123, 89409], [25123, 89409], .contexts []⟩,
    ⟨[89409, 15], [25123, 89409], .contexts [
        ⟨61163, false, false, [], []⟩,
        ⟨61163, false, false, [], []⟩,
        ⟨55753, true, false, [], [15]⟩,
        ⟨61160, true, false, [25116], [9, 15]⟩,
        ⟨61160, true, false, [25116], [9, 15]⟩,
        ⟨61159, true, false, [25116], [9, 15]⟩,
        ⟨61158, true, false, [25116], [9, 15]⟩,
        ⟨61152, true, false, [25116], [9, 15]⟩,
        ⟨1671, false, false, [25116, 89411], []⟩,
        ⟨61162, false, false, [25116], []⟩,
        ⟨61161, false, false, [25116], []⟩,
        ⟨61164, false, false, [25116], []⟩,
        ⟨61139, true, false, [], [89409]⟩,
        ⟨61165, false, false, [], []⟩,
        ⟨61165, false, false, [], []⟩
      ]⟩,
    ⟨[89407, 15], [89407, 15], .contexts []⟩,
    ⟨[89407], [89407], .contexts []⟩,
    ⟨[25117, 89407], [25117, 89407], .contexts []⟩,
    ⟨[89407, 15, 5], [25117, 89405], .contexts [
        ⟨61167, false, false, [], [5]⟩,
        ⟨61167, false, false, [], [5]⟩,
        ⟨55749, true, false, [], [15, 5]⟩,
        ⟨61166, true, false, [25122], [1, 15, 5]⟩,
        ⟨1666, false, false, [25122, 89409], [5]⟩,
        ⟨9, false, false, [25122, 89409], [5]⟩,
        ⟨55834, false, false, [25122], [5]⟩,
        ⟨55835, false, false, [25122], [5]⟩,
        ⟨55748, false, false, [25122], [5]⟩,
        ⟨55748, false, false, [25122], [5]⟩,
        ⟨61168, false, false, [25122], [5]⟩,
        ⟨61157, true, false, [], [89407, 5]⟩,
        ⟨61169, false, false, [], [5]⟩,
        ⟨61169, false, false, [], [5]⟩,
        ⟨55746, false, false, [25117], []⟩
      ]⟩,
    ⟨[89407, 5], [89405], .contexts [
        ⟨55836, false, false, [], []⟩,
        ⟨55837, false, false, [], []⟩,
        ⟨55745, false, false, [], []⟩,
        ⟨55745, false, false, [], []⟩
      ]⟩,
    ⟨[89407, 4], [89407, 5], .contexts [
        ⟨29, false, false, [89407], []⟩
      ]⟩,
    ⟨[89405, 15], [89405, 15], .contexts []⟩,
    ⟨[89405], [89405], .contexts []⟩,
    ⟨[25123, 89405], [25123, 89405], .contexts []⟩,
    ⟨[25123, 89403], [25123, 89403], .contexts []⟩,
    ⟨[89405, 3], [89403], .contexts [
        ⟨55839, false, false, [], []⟩,
        ⟨55840, false, false, [], []⟩,
        ⟨55741, false, false, [], []⟩,
        ⟨55741, false, false, [], []⟩
      ]⟩,
    ⟨[89405, 2], [89405, 3], .contexts [
        ⟨21, false, false, [89405], []⟩
      ]⟩,
    ⟨[25123, 89403, 15], [89403], .contexts [
        ⟨61176, true, false, [], [15]⟩,
        ⟨55742, true, false, [25123], [15]⟩,
        ⟨61175, true, false, [], [3, 15]⟩,
        ⟨61175, true, false, [], [3, 15]⟩,
        ⟨61139, false, false, [], [89405, 3, 15]⟩,
        ⟨61174, true, false, [25116], [3, 15]⟩,
        ⟨61171, true, false, [25116], [3, 15]⟩,
        ⟨61172, true, false, [25116], [3, 15]⟩,
        ⟨2072, true, false, [25116, 89407], [3, 15]⟩,
        ⟨61170, false, false, [25116], [15, 3, 15]⟩,
        ⟨61173, true, false, [], [3, 15]⟩,
        ⟨61173, true, false, [], [3, 15]⟩,
        ⟨1141, false, false, [89405], []⟩,
        ⟨61178, false, false, [], []⟩,
        ⟨61177, false, false, [], []⟩
      ]⟩,
    ⟨[89403, 15], [89403, 15], .contexts []⟩,
    ⟨[89403], [89403], .contexts []⟩,
    ⟨[89403, 15], [25117, 89403], .contexts [
        ⟨61180, false, false, [], []⟩,
        ⟨61179, false, false, [25122], []⟩,
        ⟨61181, false, false, [25122], []⟩,
        ⟨61157, true, false, [], [89403]⟩
      ]⟩,
    ⟨[25117, 89403], [25117, 89403], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 956. -/
def y322TCIndexRaw956 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[25117, 89403], [25117, 89403], .contexts []⟩,
    ⟨[25117, 89399], [25117, 89399], .contexts []⟩,
    ⟨[25117, 89399], [25117, 89399], .contexts []⟩,
    ⟨[89399, 1], [25123, 89403], .contexts [
        ⟨61186, true, false, [25116], [1]⟩,
        ⟨61185, true, false, [25116], [1]⟩,
        ⟨55735, true, false, [], [1]⟩,
        ⟨55738, true, false, [], [15, 1]⟩,
        ⟨61184, true, false, [25116], [1, 15, 1]⟩,
        ⟨61184, true, false, [25116], [1, 15, 1]⟩,
        ⟨61183, true, false, [25116], [1, 15, 1]⟩,
        ⟨61182, true, false, [25116], [1, 15, 1]⟩,
        ⟨61180, true, false, [25116], [1, 15, 1]⟩,
        ⟨504, false, false, [25116, 89403], []⟩,
        ⟨61181, false, false, [25116], []⟩,
        ⟨61139, true, false, [], [89403]⟩
      ]⟩,
    ⟨[90481], [83899, 11], .source 45305⟩,
    ⟨[83899, 11], [90481], .contexts [
        ⟨61188, true, false, [], []⟩
      ]⟩,
    ⟨[90481, 11], [83899], .contexts [
        ⟨61189, true, false, [], [11]⟩,
        ⟨53, false, false, [83899], []⟩,
        ⟨23358, false, false, [], []⟩
      ]⟩,
    ⟨[83899, 11], [90481], .contexts [
        ⟨61189, false, false, [], []⟩
      ]⟩,
    ⟨[90481], [90481], .contexts []⟩,
    ⟨[90481], [90481], .contexts []⟩,
    ⟨[83899, 11], [90481], .contexts [
        ⟨61191, false, false, [], []⟩,
        ⟨61192, false, false, [], []⟩,
        ⟨61193, false, false, [], []⟩,
        ⟨61193, false, false, [], []⟩
      ]⟩,
    ⟨[90481, 3], [88085], .contexts [
        ⟨61194, true, false, [], [3]⟩,
        ⟨215, false, false, [83899], []⟩,
        ⟨216, false, false, [83899], []⟩,
        ⟨23357, false, false, [], [11]⟩,
        ⟨23404, false, false, [], [11]⟩,
        ⟨23362, false, false, [], [11]⟩,
        ⟨23362, false, false, [], [11]⟩,
        ⟨48203, false, false, [], []⟩,
        ⟨48204, false, false, [], []⟩,
        ⟨48205, false, false, [], []⟩,
        ⟨48205, false, false, [], []⟩,
        ⟨51877, false, false, [], []⟩,
        ⟨51878, false, false, [], []⟩
      ]⟩,
    ⟨[88085, 3], [90481], .contexts [
        ⟨61195, true, false, [], [3]⟩,
        ⟨20, false, false, [90481], []⟩,
        ⟨61193, false, false, [], []⟩
      ]⟩,
    ⟨[25127], [19573, 19857], .source 12628⟩,
    ⟨[25129], [25127, 22529], .source 12629⟩,
    ⟨[25131], [25129, 23117], .source 12630⟩,
    ⟨[25133], [25131, 23119], .source 12631⟩,
    ⟨[90481, 9], [90481, 9], .contexts []⟩,
    ⟨[90481, 9], [25133, 88215], .contexts [
        ⟨61201, false, false, [], []⟩,
        ⟨61194, true, false, [], [9]⟩,
        ⟨221, false, false, [83899], []⟩,
        ⟨224, false, false, [83899], []⟩,
        ⟨39526, false, false, [], [11, 9, 11]⟩,
        ⟨40364, false, false, [19573], [11, 9, 11]⟩,
        ⟨61197, true, false, [], [86221, 11, 9, 11]⟩,
        ⟨49269, false, false, [25127], [9, 11]⟩,
        ⟨61198, true, false, [], [88211, 9, 11]⟩,
        ⟨49274, false, false, [25129], [11]⟩,
        ⟨53666, false, false, [25129], [11]⟩,
        ⟨61199, true, false, [], [85209, 11]⟩,
        ⟨51635, false, false, [25131], []⟩,
        ⟨61200, true, false, [], [88215]⟩,
        ⟨49298, false, false, [25133], []⟩
      ]⟩,
    ⟨[90481, 9], [25133, 88215], .contexts [
        ⟨61202, false, false, [], []⟩,
        ⟨13, true, false, [], [25133, 88215]⟩
      ]⟩,
    ⟨[25135], [25132], .source 12632⟩,
    ⟨[88215, 9], [25135, 90481], .contexts [
        ⟨61203, true, false, [25132], [9]⟩,
        ⟨46, false, false, [25132, 90481], []⟩,
        ⟨61204, true, false, [], [90481]⟩
      ]⟩,
    ⟨[19495, 86791, 11], [19495, 19463, 88089], .contexts [
        ⟨48250, false, false, [19495], []⟩
      ]⟩,
    ⟨[19495, 19463, 88089], [19495, 19463, 88089], .contexts []⟩,
    ⟨[19495, 19463, 88089], [19495, 19463, 88089], .contexts []⟩,
    ⟨[19495, 19463, 88089], [21509, 88089], .contexts [
        ⟨45438, true, false, [], [88089]⟩
      ]⟩,
    ⟨[21509, 88089], [21509, 88089], .contexts [
        ⟨48257, false, false, [21509], []⟩
      ]⟩,
    ⟨[21509, 88089], [21509, 88089], .contexts [
        ⟨48209, true, false, [], [88089]⟩
      ]⟩,
    ⟨[90481, 15], [21509, 88089], .contexts [
        ⟨61194, true, false, [], [15]⟩,
        ⟨231, false, false, [83899], []⟩,
        ⟨232, false, false, [83899], []⟩,
        ⟨39015, false, false, [], [11]⟩,
        ⟨61206, false, false, [], []⟩,
        ⟨61207, false, false, [], []⟩,
        ⟨61208, false, false, [], []⟩,
        ⟨61209, false, false, [], []⟩,
        ⟨61210, false, false, [], []⟩,
        ⟨61211, false, false, [], []⟩
      ]⟩,
    ⟨[88089, 15], [21511, 90481], .contexts [
        ⟨61212, true, false, [21508], [15]⟩,
        ⟨1, false, false, [21508, 90481], []⟩,
        ⟨45440, true, false, [], [90481]⟩
      ]⟩,
    ⟨[90483], [90481, 1], .source 45306⟩,
    ⟨[90481, 1], [90483], .contexts [
        ⟨61214, true, false, [], []⟩
      ]⟩,
    ⟨[90483, 1], [90481], .contexts [
        ⟨61215, true, false, [], [1]⟩,
        ⟨8, false, false, [90481], []⟩,
        ⟨61193, false, false, [], []⟩
      ]⟩,
    ⟨[90483], [90483], .contexts []⟩,
    ⟨[90483], [90483], .contexts []⟩,
    ⟨[90481, 1], [90483], .contexts [
        ⟨61215, false, false, [], []⟩,
        ⟨61217, false, false, [], []⟩,
        ⟨61218, false, false, [], []⟩,
        ⟨61218, false, false, [], []⟩
      ]⟩,
    ⟨[25133, 88215], [25133, 88215], .contexts []⟩,
    ⟨[25133, 88215], [25133, 88215], .contexts []⟩,
    ⟨[25137], [25133, 24551], .source 12633⟩,
    ⟨[25137, 89975], [25137, 89975], .contexts []⟩,
    ⟨[89975], [89975], .contexts []⟩,
    ⟨[90483, 9], [25137, 89975], .contexts [
        ⟨61219, true, false, [], [9]⟩,
        ⟨452, false, false, [90481], []⟩,
        ⟨455, false, false, [90481], []⟩,
        ⟨61201, false, false, [], [1, 9, 1]⟩,
        ⟨61203, false, false, [], [1, 9, 1]⟩,
        ⟨61220, false, false, [], [1, 9, 1]⟩,
        ⟨61221, false, false, [], [1, 9, 1]⟩,
        ⟨61221, false, false, [], [1, 9, 1]⟩,
        ⟨49304, false, false, [25133], [9, 1]⟩,
        ⟨58589, false, false, [25133], [1]⟩,
        ⟨61222, true, false, [], [89977, 1]⟩,
        ⟨58557, false, false, [25137], []⟩,
        ⟨61223, false, false, [], []⟩,
        ⟨61224, false, false, [25137], []⟩
      ]⟩,
    ⟨[90483, 9], [25137, 89975], .contexts [
        ⟨61225, false, false, [], []⟩,
        ⟨13, true, false, [], [25137, 89975]⟩
      ]⟩,
    ⟨[25139], [25136], .source 12634⟩,
    ⟨[89975, 9], [25139, 90483], .contexts [
        ⟨61226, true, false, [25136], [9]⟩,
        ⟨46, false, false, [25136, 90483], []⟩,
        ⟨61227, true, false, [], [90483]⟩
      ]⟩,
    ⟨[90483, 11], [90483, 11], .contexts []⟩,
    ⟨[90483, 11], [83897], .contexts [
        ⟨61229, false, false, [], []⟩,
        ⟨61219, true, false, [], [11]⟩,
        ⟨110, false, false, [90481], []⟩,
        ⟨111, false, false, [90481], []⟩,
        ⟨61190, false, false, [], [1]⟩,
        ⟨23406, false, false, [], [1]⟩,
        ⟨23358, false, false, [], [1]⟩,
        ⟨23358, false, false, [], [1]⟩,
        ⟨23407, false, false, [], []⟩,
        ⟨23408, false, false, [], []⟩,
        ⟨23354, false, false, [], []⟩,
        ⟨23354, false, false, [], []⟩,
        ⟨40389, false, false, [], []⟩,
        ⟨672, true, false, [], [83897]⟩
      ]⟩,
    ⟨[83897, 11], [90483], .contexts [
        ⟨61230, true, false, [], [11]⟩,
        ⟨53, false, false, [90483], []⟩,
        ⟨61218, false, false, [], []⟩
      ]⟩,
    ⟨[90485], [90483, 13], .source 45307⟩,
    ⟨[90483, 13], [90485], .contexts [
        ⟨61232, true, false, [], []⟩
      ]⟩,
    ⟨[90485, 13], [90483], .contexts [
        ⟨61233, true, false, [], [13]⟩,
        ⟨59, false, false, [90483], []⟩,
        ⟨61218, false, false, [], []⟩
      ]⟩,
    ⟨[90485], [90485], .contexts []⟩,
    ⟨[90485], [90485], .contexts []⟩,
    ⟨[19495, 86785], [19495, 86785], .contexts []⟩,
    ⟨[19495, 86785], [19495, 86785], .contexts []⟩,
    ⟨[90485, 11], [90485, 11], .contexts []⟩,
    ⟨[86785], [86785], .contexts []⟩,
    ⟨[19495], [19495], .contexts [
        ⟨13, false, false, [], [19495]⟩,
        ⟨39019, false, false, [], []⟩,
        ⟨39020, false, false, [], []⟩
      ]⟩,
    ⟨[90485, 11], [19495, 86785], .contexts [
        ⟨61239, false, false, [], []⟩,
        ⟨61236, true, false, [], [11]⟩,
        ⟨61236, true, false, [], [11]⟩,
        ⟨61235, true, false, [], [11]⟩,
        ⟨61233, true, false, [], [11]⟩,
        ⟨82, false, false, [90483], []⟩,
        ⟨83, false, false, [90483], []⟩,
        ⟨61229, false, false, [], [13]⟩,
        ⟨61230, false, false, [], [13]⟩,
        ⟨23408, false, false, [], [13]⟩,
        ⟨23354, false, false, [], [13]⟩,
        ⟨23354, false, false, [], [13]⟩,
        ⟨39023, false, false, [], []⟩,
        ⟨61237, false, false, [], []⟩,
        ⟨61238, false, false, [], []⟩,
        ⟨61238, false, false, [], []⟩,
        ⟨61240, false, false, [19495], []⟩,
        ⟨61241, true, false, [], [86785]⟩
      ]⟩,
    ⟨[86785, 11], [19493, 90485], .contexts [
        ⟨61242, true, false, [19494], [11]⟩,
        ⟨53, false, false, [19494, 90485], []⟩,
        ⟨38932, true, false, [], [90485]⟩
      ]⟩,
    ⟨[19495, 86783], [19495, 86783], .contexts []⟩,
    ⟨[19495, 86783], [19495, 86783], .contexts []⟩,
    ⟨[19495, 86783], [19495, 86783], .contexts []⟩,
    ⟨[19495, 86781], [19495, 86781], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 957. -/
def y322TCIndexRaw957 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[19495, 86781], [19495, 86781], .contexts []⟩,
    ⟨[86781, 1], [86781, 1], .contexts []⟩,
    ⟨[90485], [90485], .contexts []⟩,
    ⟨[86781, 1], [19493, 90485], .contexts [
        ⟨61249, false, false, [], []⟩,
        ⟨61248, true, false, [19494], [1]⟩,
        ⟨61247, true, false, [19494], [1]⟩,
        ⟨38747, true, false, [], [1]⟩,
        ⟨61246, true, false, [19494], [11, 1]⟩,
        ⟨61245, true, false, [19494], [11, 1]⟩,
        ⟨61244, true, false, [19494], [11, 1]⟩,
        ⟨38751, true, false, [], [11, 1]⟩,
        ⟨61238, true, false, [19494], [1, 11, 1]⟩,
        ⟨61238, true, false, [19494], [1, 11, 1]⟩,
        ⟨61237, true, false, [19494], [1, 11, 1]⟩,
        ⟨61242, true, false, [19494], [1, 11, 1]⟩,
        ⟨61239, true, false, [19494], [1, 11, 1]⟩,
        ⟨628, false, false, [19494, 90485], []⟩,
        ⟨61250, false, false, [19494], []⟩,
        ⟨38996, true, false, [], [90485]⟩
      ]⟩,
    ⟨[90485, 1], [19495, 86781], .contexts [
        ⟨61251, true, false, [19492], [1]⟩,
        ⟨8, false, false, [19492, 86781], []⟩,
        ⟨38925, true, false, [], [86781]⟩
      ]⟩,
    ⟨[90487], [90485, 15], .source 45308⟩,
    ⟨[90485, 15], [90487], .contexts [
        ⟨61253, true, false, [], []⟩
      ]⟩,
    ⟨[90487, 15], [90485], .contexts [
        ⟨61254, true, false, [], [15]⟩,
        ⟨1, false, false, [90485], []⟩,
        ⟨61236, false, false, [], []⟩
      ]⟩,
    ⟨[90489], [90487, 1], .source 45309⟩,
    ⟨[90487, 1], [90489], .contexts [
        ⟨61256, true, false, [], []⟩
      ]⟩,
    ⟨[90487], [90487], .contexts []⟩,
    ⟨[90489, 1], [90487], .contexts [
        ⟨61257, true, false, [], [1]⟩,
        ⟨8, false, false, [90487], []⟩,
        ⟨61258, false, false, [], []⟩
      ]⟩,
    ⟨[90489], [90489], .contexts []⟩,
    ⟨[90489], [90489], .contexts []⟩,
    ⟨[90489, 15], [90489, 15], .contexts []⟩,
    ⟨[90489, 15], [19495, 86781], .contexts [
        ⟨61262, false, false, [], []⟩,
        ⟨61261, true, false, [], [15]⟩,
        ⟨61261, true, false, [], [15]⟩,
        ⟨61260, true, false, [], [15]⟩,
        ⟨61257, true, false, [], [15]⟩,
        ⟨121, false, false, [90487], []⟩,
        ⟨122, false, false, [90487], []⟩,
        ⟨61255, false, false, [], [1]⟩,
        ⟨61235, false, false, [], [1]⟩,
        ⟨61236, false, false, [], [1]⟩,
        ⟨61236, false, false, [], [1]⟩,
        ⟨61252, false, false, [], []⟩,
        ⟨61247, false, false, [], []⟩,
        ⟨61248, false, false, [], []⟩,
        ⟨61248, false, false, [], []⟩,
        ⟨49852, false, false, [19495], []⟩,
        ⟨61241, true, false, [], [86781]⟩
      ]⟩,
    ⟨[86781, 15], [19493, 90489], .contexts [
        ⟨61263, true, false, [19494], [15]⟩,
        ⟨1, false, false, [19494, 90489], []⟩,
        ⟨38932, true, false, [], [90489]⟩
      ]⟩,
    ⟨[90489, 15], [19495, 86781], .contexts [
        ⟨61262, false, false, [], []⟩,
        ⟨61263, false, false, [], []⟩,
        ⟨61247, false, false, [], []⟩,
        ⟨61248, false, false, [], []⟩,
        ⟨61248, false, false, [], []⟩
      ]⟩,
    ⟨[25141], [19495, 22645], .source 12635⟩,
    ⟨[25143], [25141, 19493], .source 12636⟩,
    ⟨[90489], [90489], .contexts []⟩,
    ⟨[90489], [90489], .contexts []⟩,
    ⟨[25145], [25142], .source 12637⟩,
    ⟨[25142], [25142], .contexts []⟩,
    ⟨[90489, 3], [25145, 90489], .contexts [
        ⟨61267, false, false, [25142], [90489, 3]⟩,
        ⟨61264, true, false, [25142, 25141], [3]⟩,
        ⟨61266, false, false, [25142], [86781, 15, 3]⟩,
        ⟨49855, true, false, [25142, 19495], [15, 3]⟩,
        ⟨61265, true, false, [25142], [3, 15, 3]⟩,
        ⟨903, false, false, [25142, 90489], []⟩,
        ⟨61268, false, false, [25142], []⟩,
        ⟨61269, false, false, [25142], []⟩,
        ⟨61271, true, false, [], [90489]⟩,
        ⟨61271, true, false, [], [90489]⟩,
        ⟨61270, true, false, [], [90489]⟩
      ]⟩,
    ⟨[25147], [19495, 22623], .source 12638⟩,
    ⟨[88325, 11], [88325, 11], .contexts []⟩,
    ⟨[25149], [25146], .source 12639⟩,
    ⟨[25149], [25146], .contexts [
        ⟨61275, false, false, [], []⟩
      ]⟩,
    ⟨[25146], [25146], .contexts []⟩,
    ⟨[88325, 11], [25149, 90489], .contexts [
        ⟨61274, false, false, [], []⟩,
        ⟨61273, false, false, [25146], [88325, 11]⟩,
        ⟨49817, true, false, [25146, 19495], [11]⟩,
        ⟨61246, true, false, [25146], [15, 11]⟩,
        ⟨61245, true, false, [25146], [15, 11]⟩,
        ⟨61244, true, false, [25146], [15, 11]⟩,
        ⟨38745, true, false, [25146, 19495], [15, 11]⟩,
        ⟨61265, true, false, [25146], [11, 15, 11]⟩,
        ⟨2289, false, false, [25146, 90489], []⟩,
        ⟨61268, false, false, [25146], []⟩,
        ⟨61269, false, false, [25146], []⟩,
        ⟨61277, true, false, [], [90489]⟩,
        ⟨61277, true, false, [], [90489]⟩,
        ⟨61276, true, false, [], [90489]⟩
      ]⟩,
    ⟨[25147], [25148], .contexts [
        ⟨61275, true, true, [], []⟩
      ]⟩,
    ⟨[25149, 90489], [25149, 90489], .contexts []⟩,
    ⟨[25149, 90489], [25149, 90489], .contexts []⟩,
    ⟨[25151], [22659, 20905], .source 12640⟩,
    ⟨[90489, 7], [90489, 7], .contexts []⟩,
    ⟨[25153], [25147, 25151], .source 12641⟩,
    ⟨[90489, 7], [25153, 83689], .contexts [
        ⟨61283, false, false, [], []⟩,
        ⟨61281, true, false, [25148], [7]⟩,
        ⟨61281, true, false, [25148], [7]⟩,
        ⟨61280, true, false, [25148], [7]⟩,
        ⟨61278, true, false, [25148], [7]⟩,
        ⟨61274, true, false, [25148], [7]⟩,
        ⟨647, false, false, [25148, 88325], []⟩,
        ⟨648, false, false, [25148, 88325], []⟩,
        ⟨49897, false, false, [25148], [11]⟩,
        ⟨43378, false, false, [25148, 22659], []⟩,
        ⟨61282, true, false, [25148], [83689]⟩,
        ⟨43244, false, false, [25148, 25151], []⟩,
        ⟨61279, true, false, [], [25151, 83689]⟩,
        ⟨61284, true, false, [], [83689]⟩
      ]⟩,
    ⟨[25155], [25152], .source 12642⟩,
    ⟨[90489, 7], [25153, 83689], .contexts [
        ⟨61285, false, false, [], []⟩
      ]⟩,
    ⟨[25153, 83689], [25153, 83689], .contexts []⟩,
    ⟨[25153, 83689], [25153, 83689], .contexts []⟩,
    ⟨[25153, 83687], [25153, 83687], .contexts []⟩,
    ⟨[90489, 1], [90487], .contexts [
        ⟨61259, false, false, [], []⟩
      ]⟩,
    ⟨[90487], [90487], .contexts []⟩,
    ⟨[83687, 7], [83687, 7], .contexts []⟩,
    ⟨[90487], [90487], .contexts []⟩,
    ⟨[25152], [25152], .contexts []⟩,
    ⟨[83687, 7], [25155, 90487], .contexts [
        ⟨61293, false, false, [], []⟩,
        ⟨61290, true, false, [25152], [7]⟩,
        ⟨22640, true, false, [], [7]⟩,
        ⟨61289, true, false, [25152], [1, 7]⟩,
        ⟨61289, true, false, [25152], [1, 7]⟩,
        ⟨61288, true, false, [25152], [1, 7]⟩,
        ⟨61287, true, false, [25152], [1, 7]⟩,
        ⟨61283, true, false, [25152], [1, 7]⟩,
        ⟨502, false, false, [25152, 90489], []⟩,
        ⟨9, false, false, [25152, 90489], []⟩,
        ⟨61291, false, false, [25152], []⟩,
        ⟨61292, false, false, [25152], []⟩,
        ⟨61258, false, false, [25152], []⟩,
        ⟨61258, false, false, [25152], []⟩,
        ⟨61294, false, false, [25152], []⟩,
        ⟨61295, true, false, [], [90487]⟩,
        ⟨61295, true, false, [], [90487]⟩,
        ⟨61286, true, false, [], [90487]⟩
      ]⟩,
    ⟨[25153], [25154], .contexts [
        ⟨61286, true, true, [], []⟩
      ]⟩,
    ⟨[90487, 7], [25153, 83687], .contexts [
        ⟨61296, true, false, [25154], [7]⟩,
        ⟨38, false, false, [25154, 83687], []⟩,
        ⟨61297, true, false, [], [83687]⟩
      ]⟩,
    ⟨[90491], [90489, 5], .source 45310⟩,
    ⟨[90489, 5], [90491], .contexts [
        ⟨61299, true, false, [], []⟩
      ]⟩,
    ⟨[90491, 5], [90489], .contexts [
        ⟨61300, true, false, [], [5]⟩,
        ⟨28, false, false, [90489], []⟩,
        ⟨61261, false, false, [], []⟩
      ]⟩,
    ⟨[90493], [90491, 1], .source 45311⟩,
    ⟨[90491, 1], [90493], .contexts [
        ⟨61302, true, false, [], []⟩
      ]⟩,
    ⟨[90491], [90491], .contexts []⟩,
    ⟨[90493, 1], [90491], .contexts [
        ⟨61303, true, false, [], [1]⟩,
        ⟨8, false, false, [90491], []⟩,
        ⟨61304, false, false, [], []⟩
      ]⟩,
    ⟨[90491, 1], [90493], .contexts [
        ⟨61303, false, false, [], []⟩
      ]⟩,
    ⟨[90493], [90493], .contexts []⟩,
    ⟨[90493], [90493], .contexts []⟩,
    ⟨[90491, 1], [90493], .contexts [
        ⟨61306, false, false, [], []⟩,
        ⟨61307, false, false, [], []⟩,
        ⟨61308, false, false, [], []⟩,
        ⟨61308, false, false, [], []⟩
      ]⟩,
    ⟨[90491, 5], [90489], .contexts [
        ⟨61301, false, false, [], []⟩
      ]⟩,
    ⟨[90491, 5], [90489], .contexts [
        ⟨61310, false, false, [], []⟩,
        ⟨61260, false, false, [], []⟩,
        ⟨61261, false, false, [], []⟩,
        ⟨61261, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 958. -/
def y322TCIndexRaw958 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90493, 5], [90487], .contexts [
        ⟨61309, true, false, [], [5]⟩,
        ⟨98, false, false, [90491], []⟩,
        ⟨99, false, false, [90491], []⟩,
        ⟨61311, false, false, [], [1]⟩,
        ⟨61291, false, false, [], []⟩,
        ⟨61292, false, false, [], []⟩,
        ⟨61258, false, false, [], []⟩,
        ⟨61258, false, false, [], []⟩,
        ⟨61294, false, false, [], []⟩,
        ⟨672, true, false, [], [90487]⟩
      ]⟩,
    ⟨[90487, 5], [90493], .contexts [
        ⟨61312, true, false, [], [5]⟩,
        ⟨28, false, false, [90493], []⟩,
        ⟨61308, false, false, [], []⟩
      ]⟩,
    ⟨[90495], [90493, 9], .source 45312⟩,
    ⟨[90493, 9], [90495], .contexts [
        ⟨61314, true, false, [], []⟩
      ]⟩,
    ⟨[90497], [90495, 11], .source 45313⟩,
    ⟨[90495, 11], [90497], .contexts [
        ⟨61316, true, false, [], []⟩
      ]⟩,
    ⟨[90495], [90495], .contexts []⟩,
    ⟨[90499], [90497, 1], .source 45314⟩,
    ⟨[90497, 1], [90499], .contexts [
        ⟨61319, true, false, [], []⟩
      ]⟩,
    ⟨[90497], [90497], .contexts []⟩,
    ⟨[90499, 1], [90497], .contexts [
        ⟨61320, true, false, [], [1]⟩,
        ⟨8, false, false, [90497], []⟩,
        ⟨61321, false, false, [], []⟩
      ]⟩,
    ⟨[90501], [90499, 13], .source 45315⟩,
    ⟨[90499, 13], [90501], .contexts [
        ⟨61323, true, false, [], []⟩
      ]⟩,
    ⟨[90499], [90499], .contexts []⟩,
    ⟨[90501, 13], [90499], .contexts [
        ⟨61324, true, false, [], [13]⟩,
        ⟨59, false, false, [90499], []⟩,
        ⟨61325, false, false, [], []⟩
      ]⟩,
    ⟨[90503], [90501, 15], .source 45316⟩,
    ⟨[90501, 15], [90503], .contexts [
        ⟨61327, true, false, [], []⟩
      ]⟩,
    ⟨[90501], [90501], .contexts []⟩,
    ⟨[90505], [90503, 1], .source 45317⟩,
    ⟨[90503, 1], [90505], .contexts [
        ⟨61330, true, false, [], []⟩
      ]⟩,
    ⟨[90503], [90503], .contexts []⟩,
    ⟨[90505, 1], [90503], .contexts [
        ⟨61331, true, false, [], [1]⟩,
        ⟨8, false, false, [90503], []⟩,
        ⟨61332, false, false, [], []⟩
      ]⟩,
    ⟨[90507], [90505, 3], .source 45318⟩,
    ⟨[90505, 3], [90507], .contexts [
        ⟨61334, true, false, [], []⟩
      ]⟩,
    ⟨[90505], [90505], .contexts []⟩,
    ⟨[90507, 3], [90505], .contexts [
        ⟨61335, true, false, [], [3]⟩,
        ⟨20, false, false, [90505], []⟩,
        ⟨61336, false, false, [], []⟩
      ]⟩,
    ⟨[90509], [90507, 5], .source 45319⟩,
    ⟨[90507, 5], [90509], .contexts [
        ⟨61338, true, false, [], []⟩
      ]⟩,
    ⟨[90507], [90507], .contexts []⟩,
    ⟨[90509, 5], [90507], .contexts [
        ⟨61339, true, false, [], [5]⟩,
        ⟨28, false, false, [90507], []⟩,
        ⟨61340, false, false, [], []⟩
      ]⟩,
    ⟨[90511], [90509, 1], .source 45320⟩,
    ⟨[90509, 1], [90511], .contexts [
        ⟨61342, true, false, [], []⟩
      ]⟩,
    ⟨[90509], [90509], .contexts []⟩,
    ⟨[90511, 1], [90509], .contexts [
        ⟨61343, true, false, [], [1]⟩,
        ⟨8, false, false, [90509], []⟩,
        ⟨61344, false, false, [], []⟩
      ]⟩,
    ⟨[90513], [90511, 9], .source 45321⟩,
    ⟨[90511, 9], [90513], .contexts [
        ⟨61346, true, false, [], []⟩
      ]⟩,
    ⟨[90511], [90511], .contexts []⟩,
    ⟨[90515], [90513, 11], .source 45322⟩,
    ⟨[90513, 11], [90515], .contexts [
        ⟨61349, true, false, [], []⟩
      ]⟩,
    ⟨[90513], [90513], .contexts []⟩,
    ⟨[90517], [90515, 1], .source 45323⟩,
    ⟨[90515, 1], [90517], .contexts [
        ⟨61352, true, false, [], []⟩
      ]⟩,
    ⟨[90515], [90515], .contexts []⟩,
    ⟨[90519], [90517, 13], .source 45324⟩,
    ⟨[90517, 13], [90519], .contexts [
        ⟨61355, true, false, [], []⟩
      ]⟩,
    ⟨[90517], [90517], .contexts []⟩,
    ⟨[90521], [90519, 15], .source 45325⟩,
    ⟨[90519, 15], [90521], .contexts [
        ⟨61358, true, false, [], []⟩
      ]⟩,
    ⟨[90519], [90519], .contexts []⟩,
    ⟨[90521, 15], [90519], .contexts [
        ⟨61359, true, false, [], [15]⟩,
        ⟨1, false, false, [90519], []⟩,
        ⟨61360, false, false, [], []⟩
      ]⟩,
    ⟨[90523], [90521, 1], .source 45326⟩,
    ⟨[90521, 1], [90523], .contexts [
        ⟨61362, true, false, [], []⟩
      ]⟩,
    ⟨[90521], [90521], .contexts []⟩,
    ⟨[90523, 1], [90521], .contexts [
        ⟨61363, true, false, [], [1]⟩,
        ⟨8, false, false, [90521], []⟩,
        ⟨61364, false, false, [], []⟩
      ]⟩,
    ⟨[90525], [90523, 3], .source 45327⟩,
    ⟨[90523, 3], [90525], .contexts [
        ⟨61366, true, false, [], []⟩
      ]⟩,
    ⟨[90523], [90523], .contexts []⟩,
    ⟨[90527], [90525, 5], .source 45328⟩,
    ⟨[90525, 5], [90527], .contexts [
        ⟨61369, true, false, [], []⟩
      ]⟩,
    ⟨[90525], [90525], .contexts []⟩,
    ⟨[90529], [90527, 1], .source 45329⟩,
    ⟨[90527, 1], [90529], .contexts [
        ⟨61372, true, false, [], []⟩
      ]⟩,
    ⟨[90527], [90527], .contexts []⟩,
    ⟨[90531], [90529, 9], .source 45330⟩]

/-- Exact literal claimed equations and contextual derivations, block 959. -/
def y322TCIndexRaw959 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90529, 9], [90531], .contexts [
        ⟨61375, true, false, [], []⟩
      ]⟩,
    ⟨[90529], [90529], .contexts []⟩,
    ⟨[90533], [90531, 11], .source 45331⟩,
    ⟨[90531, 11], [90533], .contexts [
        ⟨61378, true, false, [], []⟩
      ]⟩,
    ⟨[90531], [90531], .contexts []⟩,
    ⟨[90535], [90533, 1], .source 45332⟩,
    ⟨[90533, 1], [90535], .contexts [
        ⟨61381, true, false, [], []⟩
      ]⟩,
    ⟨[90533], [90533], .contexts []⟩,
    ⟨[90537], [90535, 13], .source 45333⟩,
    ⟨[90535, 13], [90537], .contexts [
        ⟨61384, true, false, [], []⟩
      ]⟩,
    ⟨[90535], [90535], .contexts []⟩,
    ⟨[90539], [90537, 15], .source 45334⟩,
    ⟨[90537, 15], [90539], .contexts [
        ⟨61387, true, false, [], []⟩
      ]⟩,
    ⟨[90537], [90537], .contexts []⟩,
    ⟨[90541], [90539, 1], .source 45335⟩,
    ⟨[90539, 1], [90541], .contexts [
        ⟨61390, true, false, [], []⟩
      ]⟩,
    ⟨[90539], [90539], .contexts []⟩,
    ⟨[90543], [90541, 3], .source 45336⟩,
    ⟨[90541, 3], [90543], .contexts [
        ⟨61393, true, false, [], []⟩
      ]⟩,
    ⟨[90541], [90541], .contexts []⟩,
    ⟨[90545], [90543, 5], .source 45337⟩,
    ⟨[90543, 5], [90545], .contexts [
        ⟨61396, true, false, [], []⟩
      ]⟩,
    ⟨[90543], [90543], .contexts []⟩,
    ⟨[90547], [90545, 1], .source 45338⟩,
    ⟨[90545, 1], [90547], .contexts [
        ⟨61399, true, false, [], []⟩
      ]⟩,
    ⟨[90545], [90545], .contexts []⟩,
    ⟨[90549], [90547, 9], .source 45339⟩,
    ⟨[90547, 9], [90549], .contexts [
        ⟨61402, true, false, [], []⟩
      ]⟩,
    ⟨[90547], [90547], .contexts []⟩,
    ⟨[90551], [90549, 11], .source 45340⟩,
    ⟨[90549, 11], [90551], .contexts [
        ⟨61405, true, false, [], []⟩
      ]⟩,
    ⟨[90549], [90549], .contexts []⟩,
    ⟨[90553], [90551, 1], .source 45341⟩,
    ⟨[90551, 1], [90553], .contexts [
        ⟨61408, true, false, [], []⟩
      ]⟩,
    ⟨[90551], [90551], .contexts []⟩,
    ⟨[90555], [90553, 13], .source 45342⟩,
    ⟨[90553, 13], [90555], .contexts [
        ⟨61411, true, false, [], []⟩
      ]⟩,
    ⟨[90553], [90553], .contexts []⟩,
    ⟨[90557], [90555, 15], .source 45343⟩,
    ⟨[90555, 15], [90557], .contexts [
        ⟨61414, true, false, [], []⟩
      ]⟩,
    ⟨[90555], [90555], .contexts []⟩,
    ⟨[90559], [90557, 1], .source 45344⟩,
    ⟨[90557, 1], [90559], .contexts [
        ⟨61417, true, false, [], []⟩
      ]⟩,
    ⟨[90557], [90557], .contexts []⟩,
    ⟨[90561], [90559, 3], .source 45345⟩,
    ⟨[90559, 3], [90561], .contexts [
        ⟨61420, true, false, [], []⟩
      ]⟩,
    ⟨[90559], [90559], .contexts []⟩,
    ⟨[90563], [90561, 5], .source 45346⟩,
    ⟨[90561, 5], [90563], .contexts [
        ⟨61423, true, false, [], []⟩
      ]⟩,
    ⟨[90561], [90561], .contexts []⟩,
    ⟨[90565], [90563, 1], .source 45347⟩,
    ⟨[90563, 1], [90565], .contexts [
        ⟨61426, true, false, [], []⟩
      ]⟩,
    ⟨[90563], [90563], .contexts []⟩,
    ⟨[90567], [90565, 9], .source 45348⟩,
    ⟨[90565, 9], [90567], .contexts [
        ⟨61429, true, false, [], []⟩
      ]⟩,
    ⟨[90565], [90565], .contexts []⟩,
    ⟨[90569], [90567, 11], .source 45349⟩,
    ⟨[90567, 11], [90569], .contexts [
        ⟨61432, true, false, [], []⟩
      ]⟩,
    ⟨[90567], [90567], .contexts []⟩,
    ⟨[90571], [90569, 1], .source 45350⟩,
    ⟨[90569, 1], [90571], .contexts [
        ⟨61435, true, false, [], []⟩
      ]⟩,
    ⟨[90569], [90569], .contexts []⟩,
    ⟨[90573], [90571, 13], .source 45351⟩,
    ⟨[90571, 13], [90573], .contexts [
        ⟨61438, true, false, [], []⟩
      ]⟩]

/-- Literal contextual derivation data in chronological chunk 14. -/
def y322TCIndexRawChunk14 (i : Fin 4096) : Y322RawContextCertificate :=
  if i.val < 2048 then
    if i.val < 1024 then
      if i.val < 512 then
        if i.val < 256 then
          if i.val < 128 then
            if i.val < 64 then
              y322TCIndexRaw896 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw897 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 192 then
              y322TCIndexRaw898 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw899 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 384 then
            if i.val < 320 then
              y322TCIndexRaw900 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw901 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 448 then
              y322TCIndexRaw902 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw903 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 768 then
          if i.val < 640 then
            if i.val < 576 then
              y322TCIndexRaw904 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw905 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 704 then
              y322TCIndexRaw906 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw907 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 896 then
            if i.val < 832 then
              y322TCIndexRaw908 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw909 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 960 then
              y322TCIndexRaw910 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw911 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 1536 then
        if i.val < 1280 then
          if i.val < 1152 then
            if i.val < 1088 then
              y322TCIndexRaw912 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw913 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1216 then
              y322TCIndexRaw914 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw915 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1408 then
            if i.val < 1344 then
              y322TCIndexRaw916 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw917 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1472 then
              y322TCIndexRaw918 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw919 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 1792 then
          if i.val < 1664 then
            if i.val < 1600 then
              y322TCIndexRaw920 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw921 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1728 then
              y322TCIndexRaw922 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw923 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1920 then
            if i.val < 1856 then
              y322TCIndexRaw924 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw925 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1984 then
              y322TCIndexRaw926 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw927 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  else
    if i.val < 3072 then
      if i.val < 2560 then
        if i.val < 2304 then
          if i.val < 2176 then
            if i.val < 2112 then
              y322TCIndexRaw928 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw929 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2240 then
              y322TCIndexRaw930 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw931 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2432 then
            if i.val < 2368 then
              y322TCIndexRaw932 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw933 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2496 then
              y322TCIndexRaw934 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw935 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 2816 then
          if i.val < 2688 then
            if i.val < 2624 then
              y322TCIndexRaw936 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw937 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2752 then
              y322TCIndexRaw938 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw939 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2944 then
            if i.val < 2880 then
              y322TCIndexRaw940 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw941 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3008 then
              y322TCIndexRaw942 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw943 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 3584 then
        if i.val < 3328 then
          if i.val < 3200 then
            if i.val < 3136 then
              y322TCIndexRaw944 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw945 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3264 then
              y322TCIndexRaw946 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw947 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3456 then
            if i.val < 3392 then
              y322TCIndexRaw948 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw949 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3520 then
              y322TCIndexRaw950 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw951 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 3840 then
          if i.val < 3712 then
            if i.val < 3648 then
              y322TCIndexRaw952 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw953 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3776 then
              y322TCIndexRaw954 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw955 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3968 then
            if i.val < 3904 then
              y322TCIndexRaw956 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw957 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 4032 then
              y322TCIndexRaw958 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw959 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
