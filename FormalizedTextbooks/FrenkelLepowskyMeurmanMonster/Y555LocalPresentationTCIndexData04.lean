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

/-- Exact literal claimed equations and contextual derivations, block 256. -/
def y322TCIndexRaw256 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82767], [82767], .contexts []⟩,
    ⟨[82767, 1], [277, 82767], .contexts [
        ⟨16383, false, false, [], []⟩,
        ⟨16380, true, false, [], [1]⟩,
        ⟨691, false, false, [82715], []⟩,
        ⟨694, false, false, [82715], []⟩,
        ⟨16216, false, false, [], [9, 1, 9]⟩,
        ⟨16211, false, false, [], [9, 1, 9]⟩,
        ⟨16212, false, false, [], [9, 1, 9]⟩,
        ⟨16212, false, false, [], [9, 1, 9]⟩,
        ⟨16243, false, false, [], [1, 9]⟩,
        ⟨16217, false, false, [], [1, 9]⟩,
        ⟨16218, false, false, [], [1, 9]⟩,
        ⟨16218, false, false, [], [1, 9]⟩,
        ⟨16215, false, false, [277], [9]⟩,
        ⟨16376, false, false, [277], []⟩,
        ⟨16381, false, false, [], []⟩,
        ⟨16382, false, false, [], []⟩,
        ⟨16384, false, false, [277], []⟩
      ]⟩,
    ⟨[82767, 1], [277, 82767], .contexts [
        ⟨16385, false, false, [], []⟩,
        ⟨1228, true, false, [], [82767]⟩
      ]⟩,
    ⟨[82715, 3], [553, 82715], .contexts [
        ⟨15718, false, false, [], []⟩
      ]⟩,
    ⟨[553, 82767], [553, 82767], .contexts []⟩,
    ⟨[553, 82767], [553, 82767], .contexts []⟩,
    ⟨[82767, 3], [82767, 3], .contexts []⟩,
    ⟨[82767, 3], [553, 82767], .contexts [
        ⟨16390, false, false, [], []⟩,
        ⟨16380, true, false, [], [3]⟩,
        ⟨196, false, false, [82715], []⟩,
        ⟨197, false, false, [82715], []⟩,
        ⟨15715, false, false, [], [9]⟩,
        ⟨16387, false, false, [], [9]⟩,
        ⟨15713, false, false, [], [9]⟩,
        ⟨15714, false, false, [], [9]⟩,
        ⟨15714, false, false, [], [9]⟩,
        ⟨16376, false, false, [553], []⟩,
        ⟨16388, false, false, [], []⟩,
        ⟨16389, false, false, [], []⟩,
        ⟨16384, false, false, [553], []⟩,
        ⟨15717, true, false, [], [82767]⟩
      ]⟩,
    ⟨[82767, 7], [82767, 7], .contexts []⟩,
    ⟨[82767, 7], [77253], .contexts [
        ⟨16392, false, false, [], []⟩,
        ⟨16380, true, false, [], [7]⟩,
        ⟨1084, false, false, [82715], []⟩,
        ⟨1085, false, false, [82715], []⟩,
        ⟨15708, false, false, [], [9]⟩,
        ⟨861, false, false, [], [9]⟩,
        ⟨721, false, false, [], [9]⟩,
        ⟨721, false, false, [], [9]⟩,
        ⟨987, false, false, [], []⟩,
        ⟨860, false, false, [], []⟩,
        ⟨724, false, false, [], []⟩,
        ⟨724, false, false, [], []⟩,
        ⟨989, false, false, [], []⟩,
        ⟨672, true, false, [], [77253]⟩
      ]⟩,
    ⟨[77253, 7], [82767], .contexts [
        ⟨16393, true, false, [], [7]⟩,
        ⟨38, false, false, [82767], []⟩,
        ⟨16379, false, false, [], []⟩
      ]⟩,
    ⟨[15359, 82729], [15359, 82729], .contexts []⟩,
    ⟨[15359, 82729], [15359, 82729], .contexts []⟩,
    ⟨[15413], [15359, 15095], .source 7771⟩,
    ⟨[82767, 15], [82767, 15], .contexts []⟩,
    ⟨[82767, 15], [15413, 80803], .contexts [
        ⟨16398, false, false, [], []⟩,
        ⟨16380, true, false, [], [15]⟩,
        ⟨205, false, false, [82715], []⟩,
        ⟨206, false, false, [82715], []⟩,
        ⟨15900, false, false, [], [9]⟩,
        ⟨16395, false, false, [], [9]⟩,
        ⟨16396, false, false, [], [9]⟩,
        ⟨16396, false, false, [], [9]⟩,
        ⟨15874, false, false, [15359], []⟩,
        ⟨16397, true, false, [], [80803]⟩,
        ⟨8272, false, false, [15413], []⟩,
        ⟨13, true, false, [], [15413, 80803]⟩
      ]⟩,
    ⟨[15415], [15412], .source 7772⟩,
    ⟨[80803, 15], [15415, 82767], .contexts [
        ⟨16399, true, false, [15412], [15]⟩,
        ⟨1, false, false, [15412, 82767], []⟩,
        ⟨16400, true, false, [], [82767]⟩
      ]⟩,
    ⟨[82721, 5], [82769], .source 74532⟩,
    ⟨[82769, 5], [82721], .contexts [
        ⟨16402, true, false, [], [5]⟩,
        ⟨28, false, false, [82721], []⟩,
        ⟨15771, false, false, [], []⟩
      ]⟩,
    ⟨[82769], [82769], .contexts []⟩,
    ⟨[82769], [82769], .source 74533⟩,
    ⟨[15349, 82769], [15349, 82769], .contexts []⟩,
    ⟨[15349, 82769], [15349, 82769], .contexts []⟩,
    ⟨[82769, 1], [82769, 1], .contexts []⟩,
    ⟨[82769], [82769], .contexts []⟩,
    ⟨[82769, 1], [15349, 82769], .contexts [
        ⟨16408, false, false, [], []⟩,
        ⟨16405, true, false, [], [1]⟩,
        ⟨16405, true, false, [], [1]⟩,
        ⟨16404, true, false, [], [1]⟩,
        ⟨16402, true, false, [], [1]⟩,
        ⟨161, false, false, [82721], []⟩,
        ⟨162, false, false, [82721], []⟩,
        ⟨15779, false, false, [], [5]⟩,
        ⟨15783, false, false, [], [5]⟩,
        ⟨15777, false, false, [], [5]⟩,
        ⟨15778, false, false, [], [5]⟩,
        ⟨15778, false, false, [], [5]⟩,
        ⟨16402, false, false, [15349], []⟩,
        ⟨16406, false, false, [], []⟩,
        ⟨16407, false, false, [], []⟩,
        ⟨16409, false, false, [15349], []⟩,
        ⟨15782, true, false, [], [82769]⟩
      ]⟩,
    ⟨[293, 82719], [293, 82719], .contexts []⟩,
    ⟨[293, 82719], [293, 82719], .source 74534⟩,
    ⟨[82769, 9], [293, 82719], .source 74535⟩,
    ⟨[82769, 9], [82769, 9], .contexts []⟩,
    ⟨[82769, 9], [293, 82719], .contexts [
        ⟨16414, false, false, [], []⟩,
        ⟨16413, false, false, [], []⟩,
        ⟨15761, false, false, [293], []⟩,
        ⟨2379, true, false, [], [82719]⟩
      ]⟩,
    ⟨[82719, 9], [295, 82769], .contexts [
        ⟨16415, true, false, [292], [9]⟩,
        ⟨46, false, false, [292, 82769], []⟩,
        ⟨1121, true, false, [], [82769]⟩
      ]⟩,
    ⟨[82771], [82769, 7], .source 41450⟩,
    ⟨[82769, 7], [82771], .contexts [
        ⟨16417, true, false, [], []⟩
      ]⟩,
    ⟨[82771, 7], [82769], .contexts [
        ⟨16418, true, false, [], [7]⟩,
        ⟨38, false, false, [82769], []⟩,
        ⟨16405, false, false, [], []⟩
      ]⟩,
    ⟨[82771], [82771], .contexts []⟩,
    ⟨[82771], [82771], .contexts []⟩,
    ⟨[82769, 7], [82771], .contexts [
        ⟨16418, false, false, [], []⟩,
        ⟨16420, false, false, [], []⟩,
        ⟨16421, false, false, [], []⟩,
        ⟨16421, false, false, [], []⟩
      ]⟩,
    ⟨[15349, 82771], [15349, 82771], .contexts []⟩,
    ⟨[82771], [82771], .contexts []⟩,
    ⟨[15417], [705, 721], .source 7773⟩,
    ⟨[15417, 82767], [15417, 82767], .contexts []⟩,
    ⟨[82771, 5], [15417, 82767], .contexts [
        ⟨16422, true, false, [], [5]⟩,
        ⟨1043, false, false, [82769], []⟩,
        ⟨1046, false, false, [82769], []⟩,
        ⟨16403, false, false, [], [7, 5, 7]⟩,
        ⟨15770, false, false, [], [7, 5, 7]⟩,
        ⟨15771, false, false, [], [7, 5, 7]⟩,
        ⟨15771, false, false, [], [7, 5, 7]⟩,
        ⟨15791, false, false, [], [5, 7]⟩,
        ⟨2003, false, false, [], [5, 7]⟩,
        ⟨2004, false, false, [], [5, 7]⟩,
        ⟨2004, false, false, [], [5, 7]⟩,
        ⟨2005, false, false, [705], [7]⟩,
        ⟨16425, true, false, [], [77253, 7]⟩,
        ⟨16394, false, false, [15417], []⟩,
        ⟨16426, false, false, [], []⟩,
        ⟨16384, false, false, [15417], []⟩
      ]⟩,
    ⟨[82771, 5], [15417, 82767], .contexts [
        ⟨16427, false, false, [], []⟩,
        ⟨13, true, false, [], [15417, 82767]⟩
      ]⟩,
    ⟨[15419], [15416], .source 7774⟩,
    ⟨[82767, 5], [15419, 82771], .contexts [
        ⟨16428, true, false, [15416], [5]⟩,
        ⟨28, false, false, [15416, 82771], []⟩,
        ⟨16429, true, false, [], [82771]⟩
      ]⟩,
    ⟨[293, 82717], [293, 82717], .contexts []⟩,
    ⟨[82771, 9], [293, 82717], .contexts [
        ⟨16422, true, false, [], [9]⟩,
        ⟨1534, false, false, [82769], []⟩,
        ⟨1535, false, false, [82769], []⟩,
        ⟨16414, false, false, [], [7]⟩,
        ⟨16415, false, false, [], [7]⟩,
        ⟨16411, false, false, [], [7]⟩,
        ⟨16412, false, false, [], [7]⟩,
        ⟨16412, false, false, [], [7]⟩,
        ⟨15751, false, false, [293], []⟩,
        ⟨16431, false, false, [], []⟩,
        ⟨15741, false, false, [293], []⟩,
        ⟨2379, true, false, [], [82717]⟩
      ]⟩,
    ⟨[82717, 9], [295, 82771], .contexts [
        ⟨16432, true, false, [292], [9]⟩,
        ⟨46, false, false, [292, 82771], []⟩,
        ⟨1121, true, false, [], [82771]⟩
      ]⟩,
    ⟨[82773], [82767, 11], .source 41451⟩,
    ⟨[82767, 11], [82773], .contexts [
        ⟨16434, true, false, [], []⟩
      ]⟩,
    ⟨[82773, 11], [82767], .contexts [
        ⟨16435, true, false, [], [11]⟩,
        ⟨53, false, false, [82767], []⟩,
        ⟨16379, false, false, [], []⟩
      ]⟩,
    ⟨[82773], [82773], .contexts []⟩,
    ⟨[82773], [82773], .contexts []⟩,
    ⟨[82767, 11], [82773], .contexts [
        ⟨16435, false, false, [], []⟩,
        ⟨16437, false, false, [], []⟩,
        ⟨16438, false, false, [], []⟩,
        ⟨16438, false, false, [], []⟩
      ]⟩,
    ⟨[277, 82773], [277, 82773], .contexts []⟩,
    ⟨[82773], [82773], .contexts []⟩,
    ⟨[82773, 1], [277, 82773], .contexts [
        ⟨16439, true, false, [], [1]⟩,
        ⟨562, false, false, [82767], []⟩,
        ⟨563, false, false, [82767], []⟩,
        ⟨16383, false, false, [], [11]⟩,
        ⟨16386, false, false, [], [11]⟩,
        ⟨16381, false, false, [], [11]⟩,
        ⟨16382, false, false, [], [11]⟩,
        ⟨16382, false, false, [], [11]⟩,
        ⟨16435, false, false, [277], []⟩,
        ⟨16440, false, false, [], []⟩,
        ⟨16441, false, false, [277], []⟩,
        ⟨1228, true, false, [], [82773]⟩
      ]⟩,
    ⟨[82767, 3], [553, 82767], .contexts [
        ⟨16390, false, false, [], []⟩,
        ⟨16391, false, false, [], []⟩,
        ⟨16388, false, false, [], []⟩,
        ⟨16389, false, false, [], []⟩,
        ⟨16389, false, false, [], []⟩
      ]⟩,
    ⟨[553, 82773], [553, 82773], .contexts []⟩,
    ⟨[82773, 3], [553, 82773], .contexts [
        ⟨16439, true, false, [], [3]⟩,
        ⟨215, false, false, [82767], []⟩,
        ⟨216, false, false, [82767], []⟩,
        ⟨16443, false, false, [], [11]⟩,
        ⟨16435, false, false, [553], []⟩,
        ⟨16444, false, false, [], []⟩,
        ⟨16441, false, false, [553], []⟩,
        ⟨15717, true, false, [], [82773]⟩
      ]⟩,
    ⟨[82767, 7], [77253], .contexts [
        ⟨16392, false, false, [], []⟩,
        ⟨16393, false, false, [], []⟩,
        ⟨860, false, false, [], []⟩,
        ⟨724, false, false, [], []⟩,
        ⟨724, false, false, [], []⟩
      ]⟩,
    ⟨[82773, 7], [82773, 7], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 257. -/
def y322TCIndexRaw257 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82773, 7], [77255], .contexts [
        ⟨16447, false, false, [], []⟩,
        ⟨16439, true, false, [], [7]⟩,
        ⟨647, false, false, [82767], []⟩,
        ⟨648, false, false, [82767], []⟩,
        ⟨16446, false, false, [], [11]⟩,
        ⟨995, false, false, [], []⟩,
        ⟨859, false, false, [], []⟩,
        ⟨726, false, false, [], []⟩,
        ⟨726, false, false, [], []⟩,
        ⟨1004, false, false, [], []⟩,
        ⟨672, true, false, [], [77255]⟩
      ]⟩,
    ⟨[77255, 7], [82773], .contexts [
        ⟨16448, true, false, [], [7]⟩,
        ⟨38, false, false, [82773], []⟩,
        ⟨16438, false, false, [], []⟩
      ]⟩,
    ⟨[82767, 9], [82715], .contexts [
        ⟨16377, false, false, [], []⟩,
        ⟨15710, false, false, [], []⟩,
        ⟨15711, false, false, [], []⟩,
        ⟨15711, false, false, [], []⟩
      ]⟩,
    ⟨[243, 82773], [243, 82773], .contexts []⟩,
    ⟨[82773, 9], [243, 82773], .contexts [
        ⟨16439, true, false, [], [9]⟩,
        ⟨221, false, false, [82767], []⟩,
        ⟨224, false, false, [82767], []⟩,
        ⟨16450, false, false, [], [11, 9, 11]⟩,
        ⟨15737, false, false, [], [9, 11]⟩,
        ⟨15719, false, false, [], [9, 11]⟩,
        ⟨15720, false, false, [], [9, 11]⟩,
        ⟨15720, false, false, [], [9, 11]⟩,
        ⟨16376, false, false, [243], [11]⟩,
        ⟨16435, false, false, [243], []⟩,
        ⟨16451, false, false, [], []⟩,
        ⟨16441, false, false, [243], []⟩,
        ⟨3311, true, false, [], [82773]⟩
      ]⟩,
    ⟨[15413, 80803], [15413, 80803], .contexts []⟩,
    ⟨[15413, 80803], [15413, 80803], .contexts []⟩,
    ⟨[82767, 15], [15413, 80803], .contexts [
        ⟨16398, false, false, [], []⟩,
        ⟨16399, false, false, [], []⟩,
        ⟨16453, false, false, [], []⟩,
        ⟨16454, false, false, [], []⟩,
        ⟨16454, false, false, [], []⟩
      ]⟩,
    ⟨[15421], [15413, 9213], .source 7775⟩,
    ⟨[82773, 15], [15421, 80431], .contexts [
        ⟨16439, true, false, [], [15]⟩,
        ⟨231, false, false, [82767], []⟩,
        ⟨232, false, false, [82767], []⟩,
        ⟨16455, false, false, [], [11]⟩,
        ⟨8276, false, false, [15413], []⟩,
        ⟨12048, false, false, [15413], []⟩,
        ⟨16456, true, false, [], [80431]⟩,
        ⟨7895, false, false, [15421], []⟩,
        ⟨13, true, false, [], [15421, 80431]⟩
      ]⟩,
    ⟨[15423], [15420], .source 7776⟩,
    ⟨[80431, 15], [15423, 82773], .contexts [
        ⟨16457, true, false, [15420], [15]⟩,
        ⟨1, false, false, [15420, 82773], []⟩,
        ⟨16458, true, false, [], [82773]⟩
      ]⟩,
    ⟨[275, 82649], [275, 82649], .contexts []⟩,
    ⟨[275, 82649], [275, 82649], .contexts []⟩,
    ⟨[82649, 13], [277, 82773], .contexts [
        ⟨16461, true, false, [274], [13]⟩,
        ⟨16460, true, false, [274], [13]⟩,
        ⟨14926, true, false, [], [13]⟩,
        ⟨1008, true, false, [274], [7, 13]⟩,
        ⟨1008, true, false, [274], [7, 13]⟩,
        ⟨1007, true, false, [274], [7, 13]⟩,
        ⟨1006, true, false, [274], [7, 13]⟩,
        ⟨726, true, false, [274], [13, 7, 13]⟩,
        ⟨726, true, false, [274], [13, 7, 13]⟩,
        ⟨859, true, false, [274], [13, 7, 13]⟩,
        ⟨16448, true, false, [274], [13, 7, 13]⟩,
        ⟨16447, true, false, [274], [13, 7, 13]⟩,
        ⟨15654, false, false, [274, 82773], []⟩,
        ⟨16441, false, false, [274], []⟩,
        ⟨951, true, false, [], [82773]⟩
      ]⟩,
    ⟨[82773, 13], [275, 82649], .contexts [
        ⟨16462, true, false, [276], [13]⟩,
        ⟨59, false, false, [276, 82649], []⟩,
        ⟨963, true, false, [], [82649]⟩
      ]⟩,
    ⟨[82775], [82767, 13], .source 41452⟩,
    ⟨[82767, 13], [82775], .contexts [
        ⟨16464, true, false, [], []⟩
      ]⟩,
    ⟨[82775, 13], [82767], .contexts [
        ⟨16465, true, false, [], [13]⟩,
        ⟨59, false, false, [82767], []⟩,
        ⟨16379, false, false, [], []⟩
      ]⟩,
    ⟨[82775], [82775], .contexts []⟩,
    ⟨[82775], [82775], .contexts []⟩,
    ⟨[82767, 13], [82775], .contexts [
        ⟨16465, false, false, [], []⟩,
        ⟨16467, false, false, [], []⟩,
        ⟨16468, false, false, [], []⟩,
        ⟨16468, false, false, [], []⟩
      ]⟩,
    ⟨[553, 82775], [553, 82775], .contexts []⟩,
    ⟨[82775], [82775], .contexts []⟩,
    ⟨[82775, 3], [553, 82775], .contexts [
        ⟨16469, true, false, [], [3]⟩,
        ⟨63, false, false, [82767], []⟩,
        ⟨65, false, false, [82767], []⟩,
        ⟨16443, false, false, [], [13]⟩,
        ⟨16465, false, false, [553], []⟩,
        ⟨16470, false, false, [], []⟩,
        ⟨16471, false, false, [553], []⟩,
        ⟨15717, true, false, [], [82775]⟩
      ]⟩,
    ⟨[11973, 77291], [11973, 77291], .contexts []⟩,
    ⟨[82775, 7], [82775, 7], .contexts []⟩,
    ⟨[82775, 7], [11973, 77291], .contexts [
        ⟨16474, false, false, [], []⟩,
        ⟨16469, true, false, [], [7]⟩,
        ⟨73, false, false, [82767], []⟩,
        ⟨74, false, false, [82767], []⟩,
        ⟨16446, false, false, [], [13]⟩,
        ⟨3998, false, false, [], []⟩,
        ⟨13348, false, false, [], []⟩,
        ⟨16473, false, false, [], []⟩,
        ⟨16473, false, false, [], []⟩,
        ⟨5304, false, false, [11973], []⟩,
        ⟨13, true, false, [], [11973, 77291]⟩
      ]⟩,
    ⟨[15425], [11972], .source 7777⟩,
    ⟨[77291, 7], [15425, 82775], .contexts [
        ⟨16475, true, false, [11972], [7]⟩,
        ⟨38, false, false, [11972, 82775], []⟩,
        ⟨16476, true, false, [], [82775]⟩
      ]⟩,
    ⟨[82775, 9], [15343, 82701], .contexts [
        ⟨16469, true, false, [], [9]⟩,
        ⟨77, false, false, [82767], []⟩,
        ⟨78, false, false, [82767], []⟩,
        ⟨16450, false, false, [], [13]⟩,
        ⟨15743, false, false, [], []⟩,
        ⟨15724, false, false, [], []⟩,
        ⟨15725, false, false, [], []⟩,
        ⟨15725, false, false, [], []⟩,
        ⟨15727, false, false, [], []⟩,
        ⟨15729, false, false, [], []⟩
      ]⟩,
    ⟨[82701, 9], [15345, 82775], .contexts [
        ⟨16478, true, false, [15342], [9]⟩,
        ⟨46, false, false, [15342, 82775], []⟩,
        ⟨15731, true, false, [], [82775]⟩
      ]⟩,
    ⟨[82775, 11], [275, 82649], .contexts [
        ⟨16469, true, false, [], [11]⟩,
        ⟨82, false, false, [82767], []⟩,
        ⟨83, false, false, [82767], []⟩,
        ⟨16439, false, false, [], [13]⟩,
        ⟨16463, false, false, [], []⟩,
        ⟨16460, false, false, [], []⟩,
        ⟨16461, false, false, [], []⟩,
        ⟨16461, false, false, [], []⟩,
        ⟨14931, false, false, [275], []⟩,
        ⟨4008, true, false, [], [82649]⟩
      ]⟩,
    ⟨[82649, 11], [277, 82775], .contexts [
        ⟨16480, true, false, [274], [11]⟩,
        ⟨53, false, false, [274, 82775], []⟩,
        ⟨949, true, false, [], [82775]⟩
      ]⟩,
    ⟨[15427], [15421, 9215], .source 7778⟩,
    ⟨[15429], [15427, 8411], .source 7779⟩,
    ⟨[82775, 15], [15429, 81405], .contexts [
        ⟨16469, true, false, [], [15]⟩,
        ⟨88, false, false, [82767], []⟩,
        ⟨91, false, false, [82767], []⟩,
        ⟨16455, false, false, [], [13, 15, 13]⟩,
        ⟨8267, false, false, [15413], [15, 13]⟩,
        ⟨12056, false, false, [15413], [15, 13]⟩,
        ⟨16456, true, false, [], [80429, 15, 13]⟩,
        ⟨12061, false, false, [15421], [13]⟩,
        ⟨16482, true, false, [], [80805, 13]⟩,
        ⟨11516, false, false, [15427], []⟩,
        ⟨16483, true, false, [], [81405]⟩,
        ⟨9301, false, false, [15429], []⟩,
        ⟨13, true, false, [], [15429, 81405]⟩
      ]⟩,
    ⟨[15431], [15428], .source 7780⟩,
    ⟨[81405, 15], [15431, 82775], .contexts [
        ⟨16484, true, false, [15428], [15]⟩,
        ⟨1, false, false, [15428, 82775], []⟩,
        ⟨16485, true, false, [], [82775]⟩
      ]⟩,
    ⟨[11973, 77291], [11973, 77291], .contexts []⟩,
    ⟨[15433], [11973, 15243], .source 7781⟩,
    ⟨[7, 1, 7, 1], [], .contexts [
        ⟨501, false, false, [], []⟩
      ]⟩,
    ⟨[15435], [15432], .source 7782⟩,
    ⟨[15432], [15432], .contexts []⟩,
    ⟨[82671, 1], [15435, 82775], .contexts [
        ⟨16488, false, false, [15432], [82671, 1]⟩,
        ⟨15191, true, false, [15432, 11973], [1]⟩,
        ⟨765, true, false, [15432, 11973], [7, 1]⟩,
        ⟨16473, true, false, [15432], [1, 7, 1]⟩,
        ⟨16473, true, false, [15432], [1, 7, 1]⟩,
        ⟨16487, true, false, [15432], [1, 7, 1]⟩,
        ⟨16475, true, false, [15432], [1, 7, 1]⟩,
        ⟨16474, true, false, [15432], [1, 7, 1]⟩,
        ⟨16489, false, false, [15432, 82775], []⟩,
        ⟨16471, false, false, [15432], []⟩,
        ⟨16491, true, false, [], [82775]⟩,
        ⟨16491, true, false, [], [82775]⟩,
        ⟨16490, true, false, [], [82775]⟩
      ]⟩,
    ⟨[82775, 1], [15433, 82671], .contexts [
        ⟨16492, true, false, [15434], [1]⟩,
        ⟨8, false, false, [15434, 82671], []⟩,
        ⟨16490, false, true, [], [82671]⟩
      ]⟩,
    ⟨[78405, 5], [82777], .source 74537⟩,
    ⟨[82777, 5], [78405], .contexts [
        ⟨16494, true, false, [], [5]⟩,
        ⟨28, false, false, [78405], []⟩,
        ⟨4252, false, false, [], []⟩
      ]⟩,
    ⟨[82777], [82777], .contexts []⟩,
    ⟨[82777], [82777], .source 74538⟩,
    ⟨[78405, 5], [82777], .source 74539⟩,
    ⟨[323, 82777], [323, 82777], .contexts []⟩,
    ⟨[323, 82777], [323, 82777], .contexts []⟩,
    ⟨[82777, 1], [323, 82777], .source 74540⟩,
    ⟨[82777], [82777], .contexts []⟩,
    ⟨[82777, 1], [323, 82777], .contexts [
        ⟨16501, false, false, [], []⟩,
        ⟨16502, false, false, [323], []⟩,
        ⟨3220, true, false, [], [82777]⟩
      ]⟩,
    ⟨[1063, 82777], [1063, 82777], .contexts []⟩,
    ⟨[1063, 82777], [1063, 82777], .contexts []⟩,
    ⟨[82777, 9], [82777, 9], .contexts []⟩,
    ⟨[82777, 9], [1063, 82777], .contexts [
        ⟨16506, false, false, [], []⟩,
        ⟨16498, true, false, [], [9]⟩,
        ⟨1265, false, false, [78405], []⟩,
        ⟨1266, false, false, [78405], []⟩,
        ⟨4266, false, false, [], [5]⟩,
        ⟨4267, false, false, [], [5]⟩,
        ⟨4264, false, false, [], [5]⟩,
        ⟨4265, false, false, [], [5]⟩,
        ⟨4265, false, false, [], [5]⟩,
        ⟨16494, false, false, [1063], []⟩,
        ⟨16504, false, false, [], []⟩,
        ⟨16505, false, false, [], []⟩,
        ⟨16502, false, false, [1063], []⟩,
        ⟨3424, true, false, [], [82777]⟩
      ]⟩,
    ⟨[15353, 82721], [15353, 82721], .contexts []⟩,
    ⟨[15353, 82769], [15353, 82769], .contexts []⟩,
    ⟨[15353, 82769], [15353, 82769], .contexts []⟩,
    ⟨[82777, 11], [15353, 82769], .source 74542⟩]

/-- Exact literal claimed equations and contextual derivations, block 258. -/
def y322TCIndexRaw258 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15353], [15353], .contexts [
        ⟨13, false, false, [], [15353]⟩
      ]⟩,
    ⟨[82777, 11], [15353, 82769], .contexts [
        ⟨16511, false, false, [], []⟩,
        ⟨16409, false, false, [15353], []⟩,
        ⟨16512, true, false, [], [82769]⟩
      ]⟩,
    ⟨[82769, 11], [15351, 82777], .contexts [
        ⟨16513, true, false, [15352], [11]⟩,
        ⟨53, false, false, [15352, 82777], []⟩,
        ⟨15799, true, false, [], [82777]⟩
      ]⟩,
    ⟨[15205, 82653], [15205, 82653], .contexts []⟩,
    ⟨[15205, 82653], [15205, 82653], .source 74543⟩,
    ⟨[15205], [15205], .contexts [
        ⟨13, false, false, [], [15205]⟩
      ]⟩,
    ⟨[82777, 13], [15205, 82653], .source 74544⟩,
    ⟨[15203], [15204], .contexts [
        ⟨14966, true, true, [], []⟩
      ]⟩,
    ⟨[82779], [82777, 7], .source 41454⟩,
    ⟨[82777, 7], [82779], .contexts [
        ⟨16520, true, false, [], []⟩
      ]⟩,
    ⟨[82779, 7], [82777], .contexts [
        ⟨16521, true, false, [], [7]⟩,
        ⟨38, false, false, [82777], []⟩,
        ⟨16497, false, false, [], []⟩
      ]⟩,
    ⟨[82779], [82779], .contexts []⟩,
    ⟨[82779], [82779], .contexts []⟩,
    ⟨[82777, 7], [82779], .contexts [
        ⟨16521, false, false, [], []⟩,
        ⟨16523, false, false, [], []⟩,
        ⟨16524, false, false, [], []⟩,
        ⟨16524, false, false, [], []⟩
      ]⟩,
    ⟨[323, 82779], [323, 82779], .contexts []⟩,
    ⟨[323, 82779], [323, 82779], .contexts []⟩,
    ⟨[82779], [82779], .contexts []⟩,
    ⟨[82779, 1], [323, 82779], .contexts [
        ⟨16525, true, false, [], [1]⟩,
        ⟨1027, false, false, [82777], []⟩,
        ⟨1028, false, false, [82777], []⟩,
        ⟨16503, false, false, [], [7]⟩,
        ⟨16499, false, false, [], [7]⟩,
        ⟨16500, false, false, [], [7]⟩,
        ⟨16500, false, false, [], [7]⟩,
        ⟨16521, false, false, [323], []⟩,
        ⟨16526, false, false, [], []⟩,
        ⟨16527, false, false, [], []⟩,
        ⟨16528, false, false, [323], []⟩,
        ⟨3220, true, false, [], [82779]⟩
      ]⟩,
    ⟨[1467, 82773], [1467, 82773], .contexts []⟩,
    ⟨[1467, 82773], [1467, 82773], .contexts []⟩,
    ⟨[82779, 5], [82779, 5], .contexts []⟩,
    ⟨[82779, 5], [1467, 82773], .contexts [
        ⟨16532, false, false, [], []⟩,
        ⟨16525, true, false, [], [5]⟩,
        ⟨1043, false, false, [82777], []⟩,
        ⟨1046, false, false, [82777], []⟩,
        ⟨16495, false, false, [], [7, 5, 7]⟩,
        ⟨4251, false, false, [], [7, 5, 7]⟩,
        ⟨4252, false, false, [], [7, 5, 7]⟩,
        ⟨4252, false, false, [], [7, 5, 7]⟩,
        ⟨4249, false, false, [], [5, 7]⟩,
        ⟨3832, false, false, [], [5, 7]⟩,
        ⟨3833, false, false, [], [5, 7]⟩,
        ⟨3833, false, false, [], [5, 7]⟩,
        ⟨3853, false, false, [], [7]⟩,
        ⟨3849, false, false, [], [7]⟩,
        ⟨3850, false, false, [], [7]⟩,
        ⟨3850, false, false, [], [7]⟩,
        ⟨16449, false, false, [1467], []⟩,
        ⟨16530, false, false, [], []⟩,
        ⟨16531, false, false, [], []⟩,
        ⟨16441, false, false, [1467], []⟩
      ]⟩,
    ⟨[82779, 5], [1467, 82773], .contexts [
        ⟨16533, false, false, [], []⟩,
        ⟨13, true, false, [], [1467, 82773]⟩
      ]⟩,
    ⟨[82773, 5], [1469, 82779], .contexts [
        ⟨16534, true, false, [1466], [5]⟩,
        ⟨28, false, false, [1466, 82779], []⟩,
        ⟨3851, true, false, [], [82779]⟩
      ]⟩,
    ⟨[1063, 82779], [1063, 82779], .contexts []⟩,
    ⟨[1063, 82779], [1063, 82779], .contexts []⟩,
    ⟨[82779, 9], [82779, 9], .contexts []⟩,
    ⟨[82779, 9], [1063, 82779], .contexts [
        ⟨16538, false, false, [], []⟩,
        ⟨16525, true, false, [], [9]⟩,
        ⟨1534, false, false, [82777], []⟩,
        ⟨1535, false, false, [82777], []⟩,
        ⟨16506, false, false, [], [7]⟩,
        ⟨16507, false, false, [], [7]⟩,
        ⟨16504, false, false, [], [7]⟩,
        ⟨16505, false, false, [], [7]⟩,
        ⟨16505, false, false, [], [7]⟩,
        ⟨16521, false, false, [1063], []⟩,
        ⟨16536, false, false, [], []⟩,
        ⟨16537, false, false, [], []⟩,
        ⟨16528, false, false, [1063], []⟩,
        ⟨3424, true, false, [], [82779]⟩
      ]⟩,
    ⟨[15353, 82771], [15353, 82771], .contexts []⟩,
    ⟨[82779, 11], [15353, 82771], .contexts [
        ⟨16525, true, false, [], [11]⟩,
        ⟨1051, false, false, [82777], []⟩,
        ⟨1052, false, false, [82777], []⟩,
        ⟨16513, false, false, [], [7]⟩,
        ⟨16509, false, false, [], [7]⟩,
        ⟨16510, false, false, [], [7]⟩,
        ⟨16510, false, false, [], [7]⟩,
        ⟨16418, false, false, [15353], []⟩,
        ⟨16540, false, false, [], []⟩,
        ⟨16424, false, false, [15353], []⟩,
        ⟨16512, true, false, [], [82771]⟩
      ]⟩,
    ⟨[82771, 11], [15351, 82779], .contexts [
        ⟨16541, true, false, [15352], [11]⟩,
        ⟨53, false, false, [15352, 82779], []⟩,
        ⟨15799, true, false, [], [82779]⟩
      ]⟩,
    ⟨[15205, 82653, 7], [15205, 82651], .contexts [
        ⟨14962, false, false, [15205], []⟩
      ]⟩,
    ⟨[15205, 82651], [15205, 82651], .contexts []⟩,
    ⟨[15205, 82651], [15205, 82651], .contexts []⟩,
    ⟨[15205, 82651], [15205, 82651], .contexts []⟩,
    ⟨[82779, 13], [82779, 13], .contexts []⟩,
    ⟨[15205, 82651], [15205, 82651], .contexts [
        ⟨14953, false, false, [15205], []⟩
      ]⟩,
    ⟨[15205, 82651], [15205, 82651], .contexts [
        ⟨16517, true, false, [], [82651]⟩
      ]⟩,
    ⟨[82779, 13], [15205, 82651], .contexts [
        ⟨16547, false, false, [], []⟩,
        ⟨16525, true, false, [], [13]⟩,
        ⟨1056, false, false, [82777], []⟩,
        ⟨1057, false, false, [82777], []⟩,
        ⟨16518, false, false, [], [7]⟩,
        ⟨16515, false, false, [], [7]⟩,
        ⟨16516, false, false, [], [7]⟩,
        ⟨16516, false, false, [], [7]⟩,
        ⟨16543, false, false, [], []⟩,
        ⟨16544, false, false, [], []⟩,
        ⟨16545, false, false, [], []⟩,
        ⟨16546, false, false, [], []⟩,
        ⟨16548, false, false, [], []⟩,
        ⟨16549, false, false, [], []⟩
      ]⟩,
    ⟨[82651, 13], [15203, 82779], .contexts [
        ⟨16550, true, false, [15204], [13]⟩,
        ⟨59, false, false, [15204, 82779], []⟩,
        ⟨16519, true, false, [], [82779]⟩
      ]⟩,
    ⟨[77265, 7], [82781], .source 74546⟩,
    ⟨[82781, 7], [77265], .contexts [
        ⟨16552, true, false, [], [7]⟩,
        ⟨38, false, false, [77265], []⟩,
        ⟨738, false, false, [], []⟩
      ]⟩,
    ⟨[77265, 7], [82781], .source 74547⟩,
    ⟨[82781], [82781], .source 74548⟩,
    ⟨[82781], [82781], .source 74549⟩,
    ⟨[77265, 7], [82781], .contexts [
        ⟨16554, false, false, [], []⟩,
        ⟨16555, false, false, [], []⟩,
        ⟨16556, false, false, [], []⟩,
        ⟨16556, false, false, [], []⟩
      ]⟩,
    ⟨[561, 82781], [561, 82781], .contexts []⟩,
    ⟨[561, 82781], [561, 82781], .contexts []⟩,
    ⟨[82781, 1], [82781, 1], .contexts []⟩,
    ⟨[82781], [82781], .contexts []⟩,
    ⟨[82781, 1], [561, 82781], .contexts [
        ⟨16560, false, false, [], []⟩,
        ⟨16557, true, false, [], [1]⟩,
        ⟨1027, false, false, [77265], []⟩,
        ⟨1028, false, false, [77265], []⟩,
        ⟨1739, false, false, [], [7]⟩,
        ⟨1741, false, false, [], [7]⟩,
        ⟨1742, false, false, [], [7]⟩,
        ⟨1743, false, false, [], [7]⟩,
        ⟨1743, false, false, [], [7]⟩,
        ⟨16552, false, false, [561], []⟩,
        ⟨16558, false, false, [], []⟩,
        ⟨16559, false, false, [], []⟩,
        ⟨16561, false, false, [561], []⟩,
        ⟨14932, true, false, [], [82781]⟩
      ]⟩,
    ⟨[7425, 79367], [7425, 79367], .contexts []⟩,
    ⟨[7425, 79367], [7425, 79367], .contexts []⟩,
    ⟨[82781, 3], [82781, 3], .contexts []⟩,
    ⟨[7425], [7425], .contexts [
        ⟨13, false, false, [], [7425]⟩
      ]⟩,
    ⟨[82781, 3], [7425, 79367], .contexts [
        ⟨16565, false, false, [], []⟩,
        ⟨16557, true, false, [], [3]⟩,
        ⟨1034, false, false, [77265], []⟩,
        ⟨1035, false, false, [77265], []⟩,
        ⟨5241, false, false, [], [7]⟩,
        ⟨11046, false, false, [], []⟩,
        ⟨16563, false, false, [], []⟩,
        ⟨16564, false, false, [], []⟩,
        ⟨16564, false, false, [], []⟩,
        ⟨6893, false, false, [7425], []⟩,
        ⟨16566, true, false, [], [79367]⟩
      ]⟩,
    ⟨[79367, 3], [7427, 82781], .contexts [
        ⟨16567, true, false, [7424], [3]⟩,
        ⟨20, false, false, [7424, 82781], []⟩,
        ⟨11044, true, false, [], [82781]⟩
      ]⟩,
    ⟨[15437], [14069, 8179], .source 7783⟩,
    ⟨[82781, 9], [82781, 9], .contexts []⟩,
    ⟨[15437], [15437], .contexts [
        ⟨13, false, false, [], [15437]⟩
      ]⟩,
    ⟨[82781, 9], [15437, 79017], .contexts [
        ⟨16570, false, false, [], []⟩,
        ⟨16557, true, false, [], [9]⟩,
        ⟨1534, false, false, [77265], []⟩,
        ⟨1535, false, false, [77265], []⟩,
        ⟨5242, false, false, [], [7]⟩,
        ⟨11336, false, false, [2401], [7]⟩,
        ⟨14274, true, false, [], [77309, 7]⟩,
        ⟨11368, false, false, [14069], []⟩,
        ⟨16569, true, false, [], [79017]⟩,
        ⟨15285, false, false, [15437], []⟩,
        ⟨16571, true, false, [], [79017]⟩
      ]⟩,
    ⟨[15439], [15436], .source 7784⟩,
    ⟨[79017, 9], [15439, 82781], .contexts [
        ⟨16572, true, false, [15436], [9]⟩,
        ⟨46, false, false, [15436, 82781], []⟩,
        ⟨16573, true, false, [], [82781]⟩
      ]⟩,
    ⟨[277, 78283], [277, 78283], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 259. -/
def y322TCIndexRaw259 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[277, 78283], [277, 78283], .source 74550⟩,
    ⟨[277, 78283, 7], [277, 8067, 79377], .source 74551⟩,
    ⟨[15441], [277, 8067], .source 74552⟩,
    ⟨[82781, 11], [82781, 11], .contexts []⟩,
    ⟨[15441], [15441], .contexts [
        ⟨13, false, false, [], [15441]⟩
      ]⟩,
    ⟨[82781, 11], [15441, 79377], .contexts [
        ⟨16579, false, false, [], []⟩,
        ⟨16557, true, false, [], [11]⟩,
        ⟨1051, false, false, [77265], []⟩,
        ⟨1052, false, false, [77265], []⟩,
        ⟨4036, false, false, [], [7]⟩,
        ⟨16575, false, false, [], [7]⟩,
        ⟨16576, false, false, [], [7]⟩,
        ⟨16576, false, false, [], [7]⟩,
        ⟨16577, false, false, [], []⟩,
        ⟨16578, true, false, [], [79377]⟩,
        ⟨6823, false, false, [15441], []⟩,
        ⟨16580, true, false, [], [79377]⟩
      ]⟩,
    ⟨[15443], [15440], .source 74553⟩,
    ⟨[82783], [79367, 9], .source 41456⟩,
    ⟨[79367, 9], [82783], .contexts [
        ⟨16583, true, false, [], []⟩
      ]⟩,
    ⟨[82783, 9], [79367], .contexts [
        ⟨16584, true, false, [], [9]⟩,
        ⟨46, false, false, [79367], []⟩,
        ⟨6778, false, false, [], []⟩
      ]⟩,
    ⟨[82783], [82783], .contexts []⟩,
    ⟨[82783], [82783], .contexts []⟩,
    ⟨[79367, 9], [82783], .contexts [
        ⟨16584, false, false, [], []⟩,
        ⟨16586, false, false, [], []⟩,
        ⟨16587, false, false, [], []⟩,
        ⟨16587, false, false, [], []⟩
      ]⟩,
    ⟨[2009, 82783], [2009, 82783], .contexts []⟩,
    ⟨[82783], [82783], .contexts []⟩,
    ⟨[82783, 1], [2009, 82783], .contexts [
        ⟨16588, true, false, [], [1]⟩,
        ⟨691, false, false, [79367], []⟩,
        ⟨694, false, false, [79367], []⟩,
        ⟨6895, false, false, [], [9, 1, 9]⟩,
        ⟨6888, false, false, [], [9, 1, 9]⟩,
        ⟨6889, false, false, [], [9, 1, 9]⟩,
        ⟨6889, false, false, [], [9, 1, 9]⟩,
        ⟨6917, false, false, [], [1, 9]⟩,
        ⟨6900, false, false, [], [1, 9]⟩,
        ⟨6901, false, false, [], [1, 9]⟩,
        ⟨6901, false, false, [], [1, 9]⟩,
        ⟨6894, false, false, [2009], [9]⟩,
        ⟨16584, false, false, [2009], []⟩,
        ⟨16589, false, false, [], []⟩,
        ⟨16590, false, false, [2009], []⟩
      ]⟩,
    ⟨[82783, 1], [2009, 82783], .contexts [
        ⟨16591, false, false, [], []⟩,
        ⟨5673, true, false, [], [82783]⟩
      ]⟩,
    ⟨[7427, 82781], [7427, 82781], .contexts []⟩,
    ⟨[7427, 82781], [7427, 82781], .contexts []⟩,
    ⟨[15445], [7427, 15437], .source 7787⟩,
    ⟨[82783, 3], [82783, 3], .contexts []⟩,
    ⟨[15445], [15445], .contexts [
        ⟨13, false, false, [], [15445]⟩
      ]⟩,
    ⟨[82783, 3], [15445, 79017], .contexts [
        ⟨16596, false, false, [], []⟩,
        ⟨16588, true, false, [], [3]⟩,
        ⟨196, false, false, [79367], []⟩,
        ⟨197, false, false, [79367], []⟩,
        ⟨16568, false, false, [], [9]⟩,
        ⟨16593, false, false, [], [9]⟩,
        ⟨16594, false, false, [], [9]⟩,
        ⟨16594, false, false, [], [9]⟩,
        ⟨16572, false, false, [7427], []⟩,
        ⟨16595, true, false, [], [79017]⟩,
        ⟨15285, false, false, [15445], []⟩,
        ⟨16597, true, false, [], [79017]⟩
      ]⟩,
    ⟨[15447], [15444], .source 7788⟩,
    ⟨[79017, 3], [15447, 82783], .contexts [
        ⟨16598, true, false, [15444], [3]⟩,
        ⟨20, false, false, [15444, 82783], []⟩,
        ⟨16599, true, false, [], [82783]⟩
      ]⟩,
    ⟨[79367, 7], [7427, 77263], .contexts [
        ⟨6775, false, false, [], []⟩,
        ⟨11049, false, false, [], []⟩,
        ⟨11048, false, false, [], []⟩,
        ⟨11048, false, false, [], []⟩
      ]⟩,
    ⟨[15449], [7427, 14127], .source 7789⟩,
    ⟨[82783, 7], [82783, 7], .contexts []⟩,
    ⟨[82783, 7], [15449, 77427], .contexts [
        ⟨16603, false, false, [], []⟩,
        ⟨16588, true, false, [], [7]⟩,
        ⟨1084, false, false, [79367], []⟩,
        ⟨1085, false, false, [79367], []⟩,
        ⟨16601, false, false, [], [9]⟩,
        ⟨5002, false, false, [7427], []⟩,
        ⟨14315, false, false, [7427], []⟩,
        ⟨16602, true, false, [], [77427]⟩,
        ⟨13, true, false, [], [15449, 77427]⟩
      ]⟩,
    ⟨[15451], [15448], .source 7790⟩,
    ⟨[77427, 7], [15451, 82783], .contexts [
        ⟨16604, true, false, [15448], [7]⟩,
        ⟨38, false, false, [15448, 82783], []⟩,
        ⟨16605, true, false, [], [82783]⟩
      ]⟩,
    ⟨[78823, 11], [11449, 79185], .contexts [
        ⟨12999, false, false, [], []⟩
      ]⟩,
    ⟨[11449, 79185], [11449, 79185], .contexts []⟩,
    ⟨[11449, 79185], [11449, 79185], .contexts []⟩,
    ⟨[15453], [11449, 563], .source 7791⟩,
    ⟨[82783, 11], [82783, 11], .contexts []⟩,
    ⟨[15453], [15453], .contexts [
        ⟨13, false, false, [], [15453]⟩
      ]⟩,
    ⟨[82783, 11], [15453, 79005], .contexts [
        ⟨16611, false, false, [], []⟩,
        ⟨16588, true, false, [], [11]⟩,
        ⟨2344, false, false, [79367], []⟩,
        ⟨2346, false, false, [79367], []⟩,
        ⟨6787, false, false, [], [9, 11, 9]⟩,
        ⟨6293, false, false, [], [11, 9]⟩,
        ⟨5068, false, false, [], [11, 9]⟩,
        ⟨5069, false, false, [], [11, 9]⟩,
        ⟨5069, false, false, [], [11, 9]⟩,
        ⟨16607, false, false, [], [9]⟩,
        ⟨16608, false, false, [], [9]⟩,
        ⟨16609, false, false, [], [9]⟩,
        ⟨16609, false, false, [], [9]⟩,
        ⟨6261, false, false, [11449], []⟩,
        ⟨16610, true, false, [], [79005]⟩,
        ⟨5509, false, false, [15453], []⟩,
        ⟨16612, true, false, [], [79005]⟩
      ]⟩,
    ⟨[15455], [15452], .source 7792⟩,
    ⟨[79005, 11], [15455, 82783], .contexts [
        ⟨16613, true, false, [15452], [11]⟩,
        ⟨53, false, false, [15452, 82783], []⟩,
        ⟨16614, true, false, [], [82783]⟩
      ]⟩,
    ⟨[82785], [79367, 13], .source 41457⟩,
    ⟨[79367, 13], [82785], .contexts [
        ⟨16616, true, false, [], []⟩
      ]⟩,
    ⟨[82785, 13], [79367], .contexts [
        ⟨16617, true, false, [], [13]⟩,
        ⟨59, false, false, [79367], []⟩,
        ⟨6778, false, false, [], []⟩
      ]⟩,
    ⟨[79367, 13], [82785], .contexts [
        ⟨16617, false, false, [], []⟩
      ]⟩,
    ⟨[82785], [82785], .contexts []⟩,
    ⟨[82785], [82785], .contexts []⟩,
    ⟨[79367, 13], [82785], .contexts [
        ⟨16619, false, false, [], []⟩,
        ⟨16620, false, false, [], []⟩,
        ⟨16621, false, false, [], []⟩,
        ⟨16621, false, false, [], []⟩
      ]⟩,
    ⟨[82785, 7], [7429, 77525], .contexts [
        ⟨16622, true, false, [], [7]⟩,
        ⟨73, false, false, [79367], []⟩,
        ⟨74, false, false, [79367], []⟩,
        ⟨16601, false, false, [], [13]⟩,
        ⟨6053, false, false, [7427], []⟩,
        ⟨10724, false, false, [7427, 2921], []⟩,
        ⟨10790, true, false, [7427], [77525]⟩,
        ⟨11050, true, false, [], [77525]⟩,
        ⟨10338, false, false, [7429], []⟩,
        ⟨13, true, false, [], [7429, 77525]⟩
      ]⟩,
    ⟨[15225, 82659], [15225, 82659], .contexts []⟩,
    ⟨[15225, 82659], [15225, 82659], .contexts []⟩,
    ⟨[15457], [15225, 11889], .source 7793⟩,
    ⟨[15459], [15457, 15223], .source 7794⟩,
    ⟨[15459, 82785], [15459, 82785], .contexts []⟩,
    ⟨[15459, 82785], [15459, 82785], .contexts []⟩,
    ⟨[82785, 15], [82785, 15], .contexts []⟩,
    ⟨[82785], [82785], .contexts []⟩,
    ⟨[82785, 15], [15459, 82785], .contexts [
        ⟨16630, false, false, [], []⟩,
        ⟨16622, true, false, [], [15]⟩,
        ⟨88, false, false, [79367], []⟩,
        ⟨91, false, false, [79367], []⟩,
        ⟨15059, false, false, [], [13, 15, 13]⟩,
        ⟨16624, false, false, [], [13, 15, 13]⟩,
        ⟨16625, false, false, [], [13, 15, 13]⟩,
        ⟨16625, false, false, [], [13, 15, 13]⟩,
        ⟨15051, false, false, [15225], [15, 13]⟩,
        ⟨16626, true, false, [], [82659, 15, 13]⟩,
        ⟨15057, false, false, [15457], [13]⟩,
        ⟨16627, true, false, [], [79367, 13]⟩,
        ⟨16617, false, false, [15459], []⟩,
        ⟨16628, false, false, [], []⟩,
        ⟨16629, false, false, [], []⟩,
        ⟨16631, false, false, [15459], []⟩
      ]⟩,
    ⟨[15459], [15459], .contexts [
        ⟨13, false, false, [], [15459]⟩
      ]⟩,
    ⟨[82785, 15], [15459, 82785], .contexts [
        ⟨16632, false, false, [], []⟩,
        ⟨16633, true, false, [], [82785]⟩
      ]⟩,
    ⟨[79005, 5], [82787], .source 74555⟩,
    ⟨[82787, 5], [79005], .contexts [
        ⟨16635, true, false, [], [5]⟩,
        ⟨28, false, false, [79005], []⟩,
        ⟨5499, false, false, [], []⟩
      ]⟩,
    ⟨[79005, 5], [82787], .source 74556⟩,
    ⟨[82787], [82787], .source 74557⟩,
    ⟨[82787], [82787], .source 74558⟩]

/-- Exact literal claimed equations and contextual derivations, block 260. -/
def y322TCIndexRaw260 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[563, 82787], [563, 82787], .source 74559⟩,
    ⟨[79005, 1, 5], [563, 82787], .source 74560⟩,
    ⟨[563, 82787], [563, 82787], .source 74561⟩,
    ⟨[82787, 1], [82787, 1], .source 74562⟩,
    ⟨[82787], [82787], .source 74563⟩,
    ⟨[82787, 1], [563, 82787], .contexts [
        ⟨16643, false, false, [], []⟩,
        ⟨16639, true, false, [], [1]⟩,
        ⟨16639, true, false, [], [1]⟩,
        ⟨16638, true, false, [], [1]⟩,
        ⟨16637, true, false, [], [1]⟩,
        ⟨161, false, false, [79005], []⟩,
        ⟨162, false, false, [79005], []⟩,
        ⟨16641, false, false, [], []⟩,
        ⟨16642, false, false, [], []⟩,
        ⟨16644, false, false, [563], []⟩,
        ⟨5511, true, false, [], [82787]⟩
      ]⟩,
    ⟨[82787, 7], [82789], .source 74565⟩,
    ⟨[82789, 7], [82787], .contexts [
        ⟨16646, true, false, [], [7]⟩,
        ⟨38, false, false, [82787], []⟩,
        ⟨16639, false, false, [], []⟩
      ]⟩,
    ⟨[82787, 7], [82789], .source 74566⟩,
    ⟨[82789], [82789], .source 74567⟩,
    ⟨[82789], [82789], .source 74568⟩,
    ⟨[82787, 7], [82789], .source 74569⟩,
    ⟨[82787, 1, 7], [563, 82789], .source 74570⟩,
    ⟨[82789], [82789], .source 74571⟩,
    ⟨[82789, 1], [563, 82789], .contexts [
        ⟨16651, true, false, [], [1]⟩,
        ⟨1027, false, false, [82787], []⟩,
        ⟨1028, false, false, [82787], []⟩,
        ⟨16652, false, false, [], []⟩,
        ⟨16653, false, false, [563], []⟩,
        ⟨5511, true, false, [], [82789]⟩
      ]⟩,
    ⟨[79005, 7], [77267], .source 74572⟩,
    ⟨[82787, 5, 7, 5, 7], [82781], .source 74573⟩,
    ⟨[82789, 5], [82789, 5], .contexts []⟩,
    ⟨[82789, 5], [82781], .contexts [
        ⟨16657, false, false, [], []⟩,
        ⟨16651, true, false, [], [5]⟩,
        ⟨1043, false, false, [82787], []⟩,
        ⟨1046, false, false, [82787], []⟩,
        ⟨16656, false, false, [], []⟩,
        ⟨16561, false, false, [], []⟩,
        ⟨672, true, false, [], [82781]⟩
      ]⟩,
    ⟨[82781, 5], [82789], .contexts [
        ⟨16658, true, false, [], [5]⟩,
        ⟨28, false, false, [82789], []⟩,
        ⟨16650, false, false, [], []⟩
      ]⟩,
    ⟨[82791], [82781, 13], .source 74574⟩,
    ⟨[82781, 13], [82791], .contexts [
        ⟨16660, true, false, [], []⟩
      ]⟩,
    ⟨[82791, 13], [82781], .contexts [
        ⟨16661, true, false, [], [13]⟩,
        ⟨59, false, false, [82781], []⟩,
        ⟨16556, false, false, [], []⟩
      ]⟩,
    ⟨[82791], [82791], .contexts []⟩,
    ⟨[82791], [82791], .source 74575⟩,
    ⟨[82781, 13], [82791], .contexts [
        ⟨16661, false, false, [], []⟩,
        ⟨16663, false, false, [], []⟩,
        ⟨16664, false, false, [], []⟩,
        ⟨16664, false, false, [], []⟩
      ]⟩,
    ⟨[82781, 3], [7425, 79367], .contexts [
        ⟨16567, false, false, [], []⟩
      ]⟩,
    ⟨[82781, 3], [7425, 79367], .contexts [
        ⟨16565, false, false, [], []⟩,
        ⟨16666, false, false, [], []⟩,
        ⟨16563, false, false, [], []⟩,
        ⟨16564, false, false, [], []⟩,
        ⟨16564, false, false, [], []⟩
      ]⟩,
    ⟨[7425, 82785], [7425, 82785], .contexts []⟩,
    ⟨[7425, 82785], [7425, 82785], .contexts []⟩,
    ⟨[82791, 3], [82791, 3], .contexts []⟩,
    ⟨[82791, 3], [7425, 82785], .contexts [
        ⟨16670, false, false, [], []⟩,
        ⟨16665, true, false, [], [3]⟩,
        ⟨63, false, false, [82781], []⟩,
        ⟨65, false, false, [82781], []⟩,
        ⟨16667, false, false, [], [13]⟩,
        ⟨16617, false, false, [7425], []⟩,
        ⟨16668, false, false, [], []⟩,
        ⟨16669, false, false, [], []⟩,
        ⟨16631, false, false, [7425], []⟩,
        ⟨16566, true, false, [], [82785]⟩
      ]⟩,
    ⟨[82785, 3], [7427, 82791], .contexts [
        ⟨16671, true, false, [7424], [3]⟩,
        ⟨20, false, false, [7424, 82791], []⟩,
        ⟨11044, true, false, [], [82791]⟩
      ]⟩,
    ⟨[82781, 7], [77265], .contexts [
        ⟨16553, false, false, [], []⟩,
        ⟨854, false, false, [], []⟩,
        ⟨738, false, false, [], []⟩,
        ⟨738, false, false, [], []⟩
      ]⟩,
    ⟨[77627, 7], [2923, 82791], .source 74576⟩,
    ⟨[15461], [7425, 15459], .source 7795⟩,
    ⟨[15463], [15461, 7427], .source 7796⟩,
    ⟨[82791], [82791], .source 74577⟩,
    ⟨[15465], [15462], .source 7797⟩,
    ⟨[15462], [15462], .contexts []⟩,
    ⟨[82791, 15], [15465, 82791], .contexts [
        ⟨16676, false, false, [15462], [82791, 15]⟩,
        ⟨16672, true, false, [15462, 15461], [15]⟩,
        ⟨16675, false, false, [15462], [82785, 3, 15]⟩,
        ⟨16634, true, false, [15462, 7425], [3, 15]⟩,
        ⟨16669, true, false, [15462], [15, 3, 15]⟩,
        ⟨16669, true, false, [15462], [15, 3, 15]⟩,
        ⟨16668, true, false, [15462], [15, 3, 15]⟩,
        ⟨16671, true, false, [15462], [15, 3, 15]⟩,
        ⟨16670, true, false, [15462], [15, 3, 15]⟩,
        ⟨1659, false, false, [15462, 82791], []⟩,
        ⟨16677, false, false, [15462], []⟩,
        ⟨16679, true, false, [], [82791]⟩,
        ⟨16679, true, false, [], [82791]⟩,
        ⟨16678, true, false, [], [82791]⟩
      ]⟩,
    ⟨[82793], [82781, 15], .source 41461⟩,
    ⟨[82781, 15], [82793], .contexts [
        ⟨16681, true, false, [], []⟩
      ]⟩,
    ⟨[82793, 15], [82781], .contexts [
        ⟨16682, true, false, [], [15]⟩,
        ⟨1, false, false, [82781], []⟩,
        ⟨16556, false, false, [], []⟩
      ]⟩,
    ⟨[82793], [82793], .contexts []⟩,
    ⟨[82793], [82793], .contexts []⟩,
    ⟨[82781, 15], [82793], .contexts [
        ⟨16682, false, false, [], []⟩,
        ⟨16684, false, false, [], []⟩,
        ⟨16685, false, false, [], []⟩,
        ⟨16685, false, false, [], []⟩
      ]⟩,
    ⟨[561, 82793], [561, 82793], .contexts []⟩,
    ⟨[82793], [82793], .contexts []⟩,
    ⟨[82793, 1], [561, 82793], .contexts [
        ⟨16686, true, false, [], [1]⟩,
        ⟨7, false, false, [82781], []⟩,
        ⟨11, false, false, [82781], []⟩,
        ⟨16560, false, false, [], [15]⟩,
        ⟨16562, false, false, [], [15]⟩,
        ⟨16558, false, false, [], [15]⟩,
        ⟨16559, false, false, [], [15]⟩,
        ⟨16559, false, false, [], [15]⟩,
        ⟨16682, false, false, [561], []⟩,
        ⟨16687, false, false, [], []⟩,
        ⟨16688, false, false, [561], []⟩,
        ⟨14932, true, false, [], [82793]⟩
      ]⟩,
    ⟨[15467], [7425, 15225], .source 7798⟩,
    ⟨[82793, 3], [15467, 82659], .contexts [
        ⟨16686, true, false, [], [3]⟩,
        ⟨19, false, false, [82781], []⟩,
        ⟨22, false, false, [82781], []⟩,
        ⟨16667, false, false, [], [15]⟩,
        ⟨15059, false, false, [7425], []⟩,
        ⟨16690, true, false, [], [82659]⟩,
        ⟨15049, false, false, [15467], []⟩,
        ⟨13, true, false, [], [15467, 82659]⟩
      ]⟩,
    ⟨[15469], [15466], .source 7799⟩,
    ⟨[82659, 3], [15469, 82793], .contexts [
        ⟨16691, true, false, [15466], [3]⟩,
        ⟨20, false, false, [15466, 82793], []⟩,
        ⟨16692, true, false, [], [82793]⟩
      ]⟩,
    ⟨[15471], [8191, 13113], .source 7800⟩,
    ⟨[82793, 7], [15471, 77541], .contexts [
        ⟨16686, true, false, [], [7]⟩,
        ⟨37, false, false, [82781], []⟩,
        ⟨40, false, false, [82781], []⟩,
        ⟨16673, false, false, [], [15]⟩,
        ⟨11375, false, false, [], []⟩,
        ⟨13927, false, false, [8191], []⟩,
        ⟨16694, true, false, [], [77541]⟩,
        ⟨8169, false, false, [15471], []⟩,
        ⟨13, true, false, [], [15471, 77541]⟩
      ]⟩,
    ⟨[15473], [15470], .source 7801⟩,
    ⟨[77541, 7], [15473, 82793], .contexts [
        ⟨16695, true, false, [15470], [7]⟩,
        ⟨38, false, false, [15470, 82793], []⟩,
        ⟨16696, true, false, [], [82793]⟩
      ]⟩,
    ⟨[15437, 79017], [15437, 79017], .contexts []⟩,
    ⟨[15437, 79017], [15437, 79017], .contexts []⟩,
    ⟨[15437, 82677], [15437, 82677], .contexts []⟩,
    ⟨[82793, 9], [15437, 82677], .contexts [
        ⟨16686, true, false, [], [9]⟩,
        ⟨45, false, false, [82781], []⟩,
        ⟨48, false, false, [82781], []⟩,
        ⟨16570, false, false, [], [15]⟩,
        ⟨16572, false, false, [], [15]⟩,
        ⟨16698, false, false, [], [15]⟩,
        ⟨16699, false, false, [], [15]⟩,
        ⟨16699, false, false, [], [15]⟩,
        ⟨15287, false, false, [15437], []⟩,
        ⟨16700, false, false, [], []⟩,
        ⟨15283, false, false, [15437], []⟩,
        ⟨16571, true, false, [], [82677]⟩
      ]⟩,
    ⟨[15441, 79377], [15441, 79377], .contexts []⟩,
    ⟨[15441, 79377], [15441, 79377], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 261. -/
def y322TCIndexRaw261 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15441, 82665], [15441, 82665], .contexts []⟩,
    ⟨[82793, 11], [15441, 82665], .contexts [
        ⟨16686, true, false, [], [11]⟩,
        ⟨52, false, false, [82781], []⟩,
        ⟨55, false, false, [82781], []⟩,
        ⟨16579, false, false, [], [15]⟩,
        ⟨16581, false, false, [], [15]⟩,
        ⟨16702, false, false, [], [15]⟩,
        ⟨16703, false, false, [], [15]⟩,
        ⟨16703, false, false, [], [15]⟩,
        ⟨15130, false, false, [15441], []⟩,
        ⟨16704, false, false, [], []⟩,
        ⟨15118, false, false, [15441], []⟩,
        ⟨16580, true, false, [], [82665]⟩
      ]⟩,
    ⟨[82665, 11], [15443, 82793], .contexts [
        ⟨16705, true, false, [15440], [11]⟩,
        ⟨53, false, false, [15440, 82793], []⟩,
        ⟨16582, true, false, [], [82793]⟩
      ]⟩,
    ⟨[15465, 82791], [15465, 82791], .contexts []⟩,
    ⟨[15465, 82791], [15465, 82791], .contexts []⟩,
    ⟨[15465, 82793], [15465, 82793], .contexts []⟩,
    ⟨[79005, 13], [82795], .source 74579⟩,
    ⟨[82795, 13], [79005], .contexts [
        ⟨16710, true, false, [], [13]⟩,
        ⟨59, false, false, [79005], []⟩,
        ⟨5499, false, false, [], []⟩
      ]⟩,
    ⟨[82795], [82795], .source 74580⟩,
    ⟨[82795], [82795], .source 74581⟩,
    ⟨[79005, 13], [82795], .source 74582⟩,
    ⟨[1755, 79019], [1755, 79019], .contexts []⟩,
    ⟨[82795, 3], [1755, 79019], .contexts [
        ⟨16714, true, false, [], [3]⟩,
        ⟨63, false, false, [79005], []⟩,
        ⟨65, false, false, [79005], []⟩,
        ⟨5517, false, false, [], [13]⟩,
        ⟨5520, false, false, [], [13]⟩,
        ⟨5515, false, false, [], [13]⟩,
        ⟨5516, false, false, [], [13]⟩,
        ⟨5516, false, false, [], [13]⟩,
        ⟨5585, false, false, [1755], []⟩,
        ⟨16715, false, false, [], []⟩,
        ⟨5594, false, false, [1755], []⟩,
        ⟨5519, true, false, [], [79019]⟩
      ]⟩,
    ⟨[79019, 3], [1753, 82795], .contexts [
        ⟨16716, true, false, [1754], [3]⟩,
        ⟨20, false, false, [1754, 82795], []⟩,
        ⟨4745, true, false, [], [82795]⟩
      ]⟩,
    ⟨[82795, 7], [2931, 77629], .contexts [
        ⟨16714, true, false, [], [7]⟩,
        ⟨73, false, false, [79005], []⟩,
        ⟨74, false, false, [79005], []⟩,
        ⟨16655, false, false, [], [13]⟩,
        ⟨853, false, false, [], [13]⟩,
        ⟨741, false, false, [], [13]⟩,
        ⟨741, false, false, [], [13]⟩,
        ⟨5522, false, false, [], []⟩,
        ⟨6059, false, false, [], []⟩,
        ⟨6058, false, false, [], []⟩,
        ⟨6058, false, false, [], []⟩,
        ⟨6264, false, false, [2931], []⟩,
        ⟨13, true, false, [], [2931, 77629]⟩
      ]⟩,
    ⟨[79005, 15, 13, 15], [15475, 11863, 79005], .source 74585⟩,
    ⟨[15477], [15475, 11863], .source 74586⟩,
    ⟨[15477, 82795], [15477, 82795], .source 74587⟩,
    ⟨[15477, 82795], [15477, 82795], .source 74588⟩,
    ⟨[82795, 15], [82795, 15], .source 74589⟩,
    ⟨[82795], [82795], .contexts []⟩,
    ⟨[15477], [15477], .source 74590⟩,
    ⟨[82795, 15], [15477, 82795], .contexts [
        ⟨16723, false, false, [], []⟩,
        ⟨16714, true, false, [], [15]⟩,
        ⟨88, false, false, [79005], []⟩,
        ⟨91, false, false, [79005], []⟩,
        ⟨16719, false, false, [], [13]⟩,
        ⟨16720, true, false, [], [79005, 13]⟩,
        ⟨16710, false, false, [15477], []⟩,
        ⟨16721, false, false, [], []⟩,
        ⟨16722, false, false, [], []⟩,
        ⟨16724, false, false, [15477], []⟩,
        ⟨16725, true, false, [], [82795]⟩
      ]⟩,
    ⟨[82797], [79017, 5], .source 74591⟩,
    ⟨[79017, 5], [82797], .contexts [
        ⟨16727, true, false, [], []⟩
      ]⟩,
    ⟨[82797, 5], [79017], .contexts [
        ⟨16728, true, false, [], [5]⟩,
        ⟨28, false, false, [79017], []⟩,
        ⟨5573, false, false, [], []⟩
      ]⟩,
    ⟨[79017, 5], [82797], .contexts [
        ⟨16728, false, false, [], []⟩
      ]⟩,
    ⟨[82797], [82797], .contexts []⟩,
    ⟨[82797], [82797], .source 74592⟩,
    ⟨[79017, 5], [82797], .contexts [
        ⟨16730, false, false, [], []⟩,
        ⟨16731, false, false, [], []⟩,
        ⟨16732, false, false, [], []⟩,
        ⟨16732, false, false, [], []⟩
      ]⟩,
    ⟨[15439, 82781], [15439, 82781], .contexts []⟩,
    ⟨[15439, 82781], [15439, 82781], .contexts []⟩,
    ⟨[79017, 9], [15439, 82781], .contexts [
        ⟨16574, false, false, [], []⟩,
        ⟨16734, false, false, [], []⟩,
        ⟨16735, false, false, [], []⟩,
        ⟨16735, false, false, [], []⟩
      ]⟩,
    ⟨[15439, 82789], [15439, 82789], .contexts []⟩,
    ⟨[15439, 82789], [15439, 82789], .contexts []⟩,
    ⟨[82797, 9], [82797, 9], .contexts []⟩,
    ⟨[15439], [15439], .contexts [
        ⟨13, false, false, [], [15439]⟩
      ]⟩,
    ⟨[82797, 9], [15439, 82789], .contexts [
        ⟨16739, false, false, [], []⟩,
        ⟨16733, true, false, [], [9]⟩,
        ⟨1265, false, false, [79017], []⟩,
        ⟨1266, false, false, [79017], []⟩,
        ⟨16736, false, false, [], [5]⟩,
        ⟨16659, false, false, [15439], []⟩,
        ⟨16737, false, false, [], []⟩,
        ⟨16738, false, false, [], []⟩,
        ⟨16653, false, false, [15439], []⟩,
        ⟨16740, true, false, [], [82789]⟩
      ]⟩,
    ⟨[15437], [15438], .contexts [
        ⟨16573, true, true, [], []⟩
      ]⟩,
    ⟨[82789, 9], [15437, 82797], .contexts [
        ⟨16741, true, false, [15438], [9]⟩,
        ⟨46, false, false, [15438, 82797], []⟩,
        ⟨16742, true, false, [], [82797]⟩
      ]⟩,
    ⟨[79017, 11], [78987], .contexts [
        ⟨5570, false, false, [], []⟩,
        ⟨5392, false, false, [], []⟩,
        ⟨5393, false, false, [], []⟩,
        ⟨5393, false, false, [], []⟩
      ]⟩,
    ⟨[82797, 11], [82797, 11], .contexts []⟩,
    ⟨[82797, 11], [79013], .contexts [
        ⟨16745, false, false, [], []⟩,
        ⟨16733, true, false, [], [11]⟩,
        ⟨174, false, false, [79017], []⟩,
        ⟨175, false, false, [79017], []⟩,
        ⟨16744, false, false, [], [5]⟩,
        ⟨15146, false, false, [], []⟩,
        ⟨5546, false, false, [], []⟩,
        ⟨5547, false, false, [], []⟩,
        ⟨5547, false, false, [], []⟩,
        ⟨6314, false, false, [], []⟩,
        ⟨6315, false, false, [], []⟩
      ]⟩,
    ⟨[79013, 11], [82797], .contexts [
        ⟨16746, true, false, [], [11]⟩,
        ⟨53, false, false, [82797], []⟩,
        ⟨16732, false, false, [], []⟩
      ]⟩,
    ⟨[82797, 7], [82799], .source 74594⟩,
    ⟨[82799, 7], [82797], .contexts [
        ⟨16748, true, false, [], [7]⟩,
        ⟨38, false, false, [82797], []⟩,
        ⟨16732, false, false, [], []⟩
      ]⟩,
    ⟨[82797, 7], [82799], .contexts [
        ⟨16748, false, false, [], []⟩
      ]⟩,
    ⟨[82799], [82799], .contexts []⟩,
    ⟨[82799], [82799], .source 74595⟩,
    ⟨[82797, 7], [82799], .contexts [
        ⟨16750, false, false, [], []⟩,
        ⟨16751, false, false, [], []⟩,
        ⟨16752, false, false, [], []⟩,
        ⟨16752, false, false, [], []⟩
      ]⟩,
    ⟨[82797, 5, 7, 5], [8181, 8123, 77271], .source 74596⟩,
    ⟨[15479], [8181, 8123], .source 74597⟩,
    ⟨[15479, 79185], [15479, 79185], .contexts []⟩,
    ⟨[82799, 5], [15479, 79185], .contexts [
        ⟨16753, true, false, [], [5]⟩,
        ⟨1043, false, false, [82797], []⟩,
        ⟨1046, false, false, [82797], []⟩,
        ⟨16754, false, false, [], [7]⟩,
        ⟨16755, true, false, [], [77271, 7]⟩,
        ⟨6247, false, false, [15479], []⟩,
        ⟨16756, false, false, [], []⟩,
        ⟨6764, false, false, [15479], []⟩,
        ⟨13, true, false, [], [15479, 79185]⟩
      ]⟩,
    ⟨[15481], [15478], .source 74598⟩,
    ⟨[79185, 5], [15481, 82799], .contexts [
        ⟨16757, true, false, [15478], [5]⟩,
        ⟨28, false, false, [15478, 82799], []⟩,
        ⟨16758, true, false, [], [82799]⟩
      ]⟩,
    ⟨[15439, 82787], [15439, 82787], .contexts []⟩,
    ⟨[82799, 9], [15439, 82787], .contexts [
        ⟨16753, true, false, [], [9]⟩,
        ⟨1534, false, false, [82797], []⟩,
        ⟨1535, false, false, [82797], []⟩,
        ⟨16739, false, false, [], [7]⟩,
        ⟨16741, false, false, [], [7]⟩,
        ⟨16737, false, false, [], [7]⟩,
        ⟨16738, false, false, [], [7]⟩,
        ⟨16738, false, false, [], [7]⟩,
        ⟨16647, false, false, [15439], []⟩,
        ⟨16760, false, false, [], []⟩,
        ⟨16644, false, false, [15439], []⟩,
        ⟨16740, true, false, [], [82787]⟩
      ]⟩,
    ⟨[82787, 9], [15437, 82799], .contexts [
        ⟨16761, true, false, [15438], [9]⟩,
        ⟨46, false, false, [15438, 82799], []⟩,
        ⟨16742, true, false, [], [82799]⟩
      ]⟩,
    ⟨[82799, 11], [79011], .contexts [
        ⟨16753, true, false, [], [11]⟩,
        ⟨1051, false, false, [82797], []⟩,
        ⟨1052, false, false, [82797], []⟩,
        ⟨16745, false, false, [], [7]⟩,
        ⟨16746, false, false, [], [7]⟩,
        ⟨5546, false, false, [], [7]⟩,
        ⟨5547, false, false, [], [7]⟩,
        ⟨5547, false, false, [], [7]⟩,
        ⟨15172, false, false, [], []⟩,
        ⟨5533, false, false, [], []⟩,
        ⟨5534, false, false, [], []⟩,
        ⟨5534, false, false, [], []⟩,
        ⟨6297, false, false, [], []⟩,
        ⟨6298, false, false, [], []⟩
      ]⟩,
    ⟨[79011, 11], [82799], .contexts [
        ⟨16763, true, false, [], [11]⟩,
        ⟨53, false, false, [82799], []⟩,
        ⟨16752, false, false, [], []⟩
      ]⟩,
    ⟨[82801], [79185, 13], .source 41465⟩,
    ⟨[79185, 13], [82801], .contexts [
        ⟨16765, true, false, [], []⟩
      ]⟩,
    ⟨[82801, 13], [79185], .contexts [
        ⟨16766, true, false, [], [13]⟩,
        ⟨59, false, false, [79185], []⟩,
        ⟨6251, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 262. -/
def y322TCIndexRaw262 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82801], [82801], .contexts []⟩,
    ⟨[82801], [82801], .contexts []⟩,
    ⟨[79185, 13], [82801], .contexts [
        ⟨16766, false, false, [], []⟩,
        ⟨16768, false, false, [], []⟩,
        ⟨16769, false, false, [], []⟩,
        ⟨16769, false, false, [], []⟩
      ]⟩,
    ⟨[14707, 78841], [14707, 78841], .contexts []⟩,
    ⟨[14707, 78841], [14707, 78841], .contexts []⟩,
    ⟨[15483], [14707, 1077], .source 7806⟩,
    ⟨[15485], [15483, 14709], .source 7807⟩,
    ⟨[15485, 82801], [15485, 82801], .contexts []⟩,
    ⟨[82801], [82801], .contexts []⟩,
    ⟨[82801, 1], [15485, 82801], .contexts [
        ⟨16770, true, false, [], [1]⟩,
        ⟨246, false, false, [79185], []⟩,
        ⟨249, false, false, [79185], []⟩,
        ⟨14535, false, false, [], [13, 1, 13]⟩,
        ⟨14537, false, false, [], [13, 1, 13]⟩,
        ⟨16771, false, false, [], [13, 1, 13]⟩,
        ⟨16772, false, false, [], [13, 1, 13]⟩,
        ⟨16772, false, false, [], [13, 1, 13]⟩,
        ⟨5210, false, false, [14707], [1, 13]⟩,
        ⟨16773, true, false, [], [78841, 1, 13]⟩,
        ⟨14539, false, false, [15483], [13]⟩,
        ⟨16774, true, false, [], [79185, 13]⟩,
        ⟨16766, false, false, [15485], []⟩,
        ⟨16775, false, false, [], []⟩,
        ⟨16776, false, false, [15485], []⟩
      ]⟩,
    ⟨[82801, 1], [15485, 82801], .contexts [
        ⟨16777, false, false, [], []⟩,
        ⟨13, true, false, [], [15485, 82801]⟩
      ]⟩,
    ⟨[2211, 79199], [2211, 79199], .contexts []⟩,
    ⟨[82801, 3], [2211, 79199], .contexts [
        ⟨16770, true, false, [], [3]⟩,
        ⟨63, false, false, [79185], []⟩,
        ⟨65, false, false, [79185], []⟩,
        ⟨6255, false, false, [], [13]⟩,
        ⟨6257, false, false, [], [13]⟩,
        ⟨6253, false, false, [], [13]⟩,
        ⟨6254, false, false, [], [13]⟩,
        ⟨6254, false, false, [], [13]⟩,
        ⟨6328, false, false, [2211], []⟩,
        ⟨16779, false, false, [], []⟩,
        ⟨6342, false, false, [2211], []⟩,
        ⟨6256, true, false, [], [79199]⟩
      ]⟩,
    ⟨[79199, 3], [2209, 82801], .contexts [
        ⟨16780, true, false, [2210], [3]⟩,
        ⟨20, false, false, [2210, 82801], []⟩,
        ⟨4755, true, false, [], [82801]⟩
      ]⟩,
    ⟨[82801, 7], [7595, 77509], .contexts [
        ⟨16770, true, false, [], [7]⟩,
        ⟨73, false, false, [79185], []⟩,
        ⟨74, false, false, [79185], []⟩,
        ⟨6248, false, false, [], [13]⟩,
        ⟨851, false, false, [], [13]⟩,
        ⟨744, false, false, [], [13]⟩,
        ⟨744, false, false, [], [13]⟩,
        ⟨6263, false, false, [], []⟩,
        ⟨11100, false, false, [], []⟩,
        ⟨11099, false, false, [], []⟩,
        ⟨11099, false, false, [], []⟩,
        ⟨2182, false, false, [7595], []⟩,
        ⟨13, true, false, [], [7595, 77509]⟩
      ]⟩,
    ⟨[77509, 7], [7597, 82801], .contexts [
        ⟨16782, true, false, [7594], [7]⟩,
        ⟨38, false, false, [7594, 82801], []⟩,
        ⟨11101, true, false, [], [82801]⟩
      ]⟩,
    ⟨[563, 82795], [563, 82795], .contexts []⟩,
    ⟨[82801, 9], [563, 82795], .contexts [
        ⟨16770, true, false, [], [9]⟩,
        ⟨77, false, false, [79185], []⟩,
        ⟨78, false, false, [79185], []⟩,
        ⟨6260, false, false, [], [13]⟩,
        ⟨6261, false, false, [], [13]⟩,
        ⟨5505, false, false, [], [13]⟩,
        ⟨5507, false, false, [], [13]⟩,
        ⟨5507, false, false, [], [13]⟩,
        ⟨16710, false, false, [563], []⟩,
        ⟨16784, false, false, [], []⟩,
        ⟨16724, false, false, [563], []⟩,
        ⟨5511, true, false, [], [82795]⟩
      ]⟩,
    ⟨[82795, 9], [561, 82801], .contexts [
        ⟨16785, true, false, [562], [9]⟩,
        ⟨46, false, false, [562, 82801], []⟩,
        ⟨1740, true, false, [], [82801]⟩
      ]⟩,
    ⟨[15253, 82673], [15253, 82673], .contexts []⟩,
    ⟨[15253, 82673], [15253, 82673], .contexts []⟩,
    ⟨[15487], [15253, 743], .source 7808⟩,
    ⟨[15489], [15487, 15251], .source 7809⟩,
    ⟨[15489, 82801], [15489, 82801], .contexts []⟩,
    ⟨[82801, 15], [15489, 82801], .contexts [
        ⟨16770, true, false, [], [15]⟩,
        ⟨88, false, false, [79185], []⟩,
        ⟨91, false, false, [79185], []⟩,
        ⟨15234, false, false, [], [13, 15, 13]⟩,
        ⟨16787, false, false, [], [13, 15, 13]⟩,
        ⟨16788, false, false, [], [13, 15, 13]⟩,
        ⟨16788, false, false, [], [13, 15, 13]⟩,
        ⟨15229, false, false, [15253], [15, 13]⟩,
        ⟨16789, true, false, [], [82673, 15, 13]⟩,
        ⟨15232, false, false, [15487], [13]⟩,
        ⟨16790, true, false, [], [79185, 13]⟩,
        ⟨16766, false, false, [15489], []⟩,
        ⟨16791, false, false, [], []⟩,
        ⟨16776, false, false, [15489], []⟩
      ]⟩,
    ⟨[82801, 15], [15489, 82801], .contexts [
        ⟨16792, false, false, [], []⟩,
        ⟨13, true, false, [], [15489, 82801]⟩
      ]⟩,
    ⟨[82803], [78823, 13], .source 41466⟩,
    ⟨[78823, 13], [82803], .contexts [
        ⟨16794, true, false, [], []⟩
      ]⟩,
    ⟨[78823, 13], [82803], .contexts [
        ⟨16795, false, false, [], []⟩
      ]⟩,
    ⟨[82803], [82803], .contexts []⟩,
    ⟨[82803], [82803], .contexts []⟩,
    ⟨[78823, 13], [82803], .contexts [
        ⟨16796, false, false, [], []⟩,
        ⟨16797, false, false, [], []⟩,
        ⟨16798, false, false, [], []⟩,
        ⟨16798, false, false, [], []⟩
      ]⟩,
    ⟨[1077, 82803], [1077, 82803], .contexts []⟩,
    ⟨[82803], [82803], .contexts []⟩,
    ⟨[82803, 1], [1077, 82803], .contexts [
        ⟨16799, true, false, [], [1]⟩,
        ⟨246, false, false, [78823], []⟩,
        ⟨249, false, false, [78823], []⟩,
        ⟨5535, false, false, [], [13, 1, 13]⟩,
        ⟨5183, false, false, [], [1, 13]⟩,
        ⟨4909, false, false, [], [1, 13]⟩,
        ⟨4910, false, false, [], [1, 13]⟩,
        ⟨4910, false, false, [], [1, 13]⟩,
        ⟨5074, false, false, [1077], [13]⟩,
        ⟨16795, false, false, [1077], []⟩,
        ⟨16800, false, false, [], []⟩,
        ⟨16801, false, false, [1077], []⟩,
        ⟨4913, true, false, [], [82803]⟩
      ]⟩,
    ⟨[11451, 79197], [11451, 79197], .contexts []⟩,
    ⟨[11451, 79197], [11451, 79197], .contexts []⟩,
    ⟨[11451, 79379], [11451, 79379], .contexts []⟩,
    ⟨[82803, 3], [11451, 79379], .contexts [
        ⟨16799, true, false, [], [3]⟩,
        ⟨63, false, false, [78823], []⟩,
        ⟨65, false, false, [78823], []⟩,
        ⟨12997, false, false, [], [13]⟩,
        ⟨16803, false, false, [], [13]⟩,
        ⟨16804, false, false, [], [13]⟩,
        ⟨16804, false, false, [], [13]⟩,
        ⟨6829, false, false, [11451], []⟩,
        ⟨16805, false, false, [], []⟩,
        ⟨6840, false, false, [11451], []⟩,
        ⟨13, true, false, [], [11451, 79379]⟩
      ]⟩,
    ⟨[15491], [11450], .source 7810⟩,
    ⟨[12697, 77273], [12697, 77273], .contexts []⟩,
    ⟨[15493], [12697, 8089], .source 7811⟩,
    ⟨[82803, 7], [15493, 77575], .contexts [
        ⟨16799, true, false, [], [7]⟩,
        ⟨73, false, false, [78823], []⟩,
        ⟨74, false, false, [78823], []⟩,
        ⟨5555, false, false, [], [13]⟩,
        ⟨13740, false, false, [], [13]⟩,
        ⟨16808, false, false, [], [13]⟩,
        ⟨16808, false, false, [], [13]⟩,
        ⟨6768, false, false, [12697], []⟩,
        ⟨11310, false, false, [12697], []⟩,
        ⟨16809, true, false, [], [77575]⟩,
        ⟨2069, false, false, [15493], []⟩,
        ⟨13, true, false, [], [15493, 77575]⟩
      ]⟩,
    ⟨[15495], [15492], .source 7812⟩,
    ⟨[77575, 7], [15495, 82803], .contexts [
        ⟨16810, true, false, [15492], [7]⟩,
        ⟨38, false, false, [15492, 82803], []⟩,
        ⟨16811, true, false, [], [82803]⟩
      ]⟩,
    ⟨[11449, 82801], [11449, 82801], .contexts []⟩,
    ⟨[82803, 11], [11449, 82801], .contexts [
        ⟨16799, true, false, [], [11]⟩,
        ⟨82, false, false, [78823], []⟩,
        ⟨83, false, false, [78823], []⟩,
        ⟨16607, false, false, [], [13]⟩,
        ⟨16608, false, false, [], [13]⟩,
        ⟨16609, false, false, [], [13]⟩,
        ⟨16609, false, false, [], [13]⟩,
        ⟨16766, false, false, [11449], []⟩,
        ⟨16813, false, false, [], []⟩,
        ⟨16776, false, false, [11449], []⟩,
        ⟨13, true, false, [], [11449, 82801]⟩
      ]⟩,
    ⟨[82801, 11], [11447, 82803], .contexts [
        ⟨16814, true, false, [11448], [11]⟩,
        ⟨53, false, false, [11448, 82803], []⟩,
        ⟨12995, false, true, [], [82803]⟩
      ]⟩,
    ⟨[15219, 82657], [15219, 82657], .contexts []⟩,
    ⟨[15219, 82657], [15219, 82657], .contexts []⟩,
    ⟨[15497], [15219, 743], .source 7813⟩,
    ⟨[15499], [15497, 15217], .source 7814⟩,
    ⟨[15499, 82803], [15499, 82803], .contexts []⟩,
    ⟨[82803, 15], [15499, 82803], .contexts [
        ⟨16799, true, false, [], [15]⟩,
        ⟨88, false, false, [78823], []⟩,
        ⟨91, false, false, [78823], []⟩,
        ⟨15030, false, false, [], [13, 15, 13]⟩,
        ⟨16816, false, false, [], [13, 15, 13]⟩,
        ⟨16817, false, false, [], [13, 15, 13]⟩,
        ⟨16817, false, false, [], [13, 15, 13]⟩,
        ⟨15021, false, false, [15219], [15, 13]⟩,
        ⟨16818, true, false, [], [82657, 15, 13]⟩,
        ⟨15028, false, false, [15497], [13]⟩,
        ⟨16819, true, false, [], [78823, 13]⟩,
        ⟨16795, false, false, [15499], []⟩,
        ⟨16820, false, false, [], []⟩,
        ⟨16801, false, false, [15499], []⟩
      ]⟩,
    ⟨[15499], [15499], .contexts [
        ⟨13, false, false, [], [15499]⟩
      ]⟩,
    ⟨[82805], [78843, 11], .source 74599⟩,
    ⟨[78843, 11], [82805], .contexts [
        ⟨16823, true, false, [], []⟩
      ]⟩,
    ⟨[82805, 11], [78843], .contexts [
        ⟨16824, true, false, [], [11]⟩,
        ⟨53, false, false, [78843], []⟩,
        ⟨5214, false, false, [], []⟩
      ]⟩,
    ⟨[82805], [82805], .source 74600⟩,
    ⟨[82805], [82805], .source 74601⟩,
    ⟨[78843, 11], [82805], .source 74602⟩,
    ⟨[15213, 82673], [15213, 82673], .contexts []⟩,
    ⟨[82805, 1], [15213, 82673], .contexts [
        ⟨16828, true, false, [], [1]⟩,
        ⟨562, false, false, [78843], []⟩,
        ⟨563, false, false, [78843], []⟩,
        ⟨15297, false, false, [], [11]⟩,
        ⟨15212, false, false, [15213], []⟩,
        ⟨16829, false, false, [], []⟩,
        ⟨15228, false, false, [15213], []⟩,
        ⟨13, true, false, [], [15213, 82673]⟩
      ]⟩,
    ⟨[82673, 1], [15211, 82805], .contexts [
        ⟨16830, true, false, [15212], [1]⟩,
        ⟨8, false, false, [15212, 82805], []⟩,
        ⟨15007, false, true, [], [82805]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 263. -/
def y322TCIndexRaw263 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82805, 7], [15501, 77377], .source 74604⟩,
    ⟨[82805, 7], [15501, 77377], .contexts [
        ⟨16832, false, false, [], []⟩,
        ⟨1329, false, false, [15501], []⟩,
        ⟨13, true, false, [], [15501, 77377]⟩
      ]⟩,
    ⟨[15503], [15500], .source 7816⟩,
    ⟨[77377, 7], [15503, 82805], .contexts [
        ⟨16833, true, false, [15500], [7]⟩,
        ⟨38, false, false, [15500, 82805], []⟩,
        ⟨16834, true, false, [], [82805]⟩
      ]⟩,
    ⟨[15311, 82691], [15311, 82691], .contexts []⟩,
    ⟨[15311, 82691], [15311, 82691], .contexts []⟩,
    ⟨[15505], [15311, 6019], .source 7817⟩,
    ⟨[15507], [15505, 15309], .source 7818⟩,
    ⟨[15507, 82805], [15507, 82805], .contexts []⟩,
    ⟨[15507, 82805], [15507, 82805], .contexts []⟩,
    ⟨[82805, 9], [82805, 9], .contexts []⟩,
    ⟨[82805], [82805], .contexts []⟩,
    ⟨[82805, 9], [15507, 82805], .contexts [
        ⟨16842, false, false, [], []⟩,
        ⟨16828, true, false, [], [9]⟩,
        ⟨221, false, false, [78843], []⟩,
        ⟨224, false, false, [78843], []⟩,
        ⟨15450, false, false, [], [11, 9, 11]⟩,
        ⟨16836, false, false, [], [11, 9, 11]⟩,
        ⟨16837, false, false, [], [11, 9, 11]⟩,
        ⟨16837, false, false, [], [11, 9, 11]⟩,
        ⟨15458, false, false, [15311], [9, 11]⟩,
        ⟨16838, true, false, [], [82691, 9, 11]⟩,
        ⟨15448, false, false, [15505], [11]⟩,
        ⟨16839, true, false, [], [78843, 11]⟩,
        ⟨16824, false, false, [15507], []⟩,
        ⟨16840, false, false, [], []⟩,
        ⟨16841, false, false, [], []⟩,
        ⟨16843, false, false, [15507], []⟩
      ]⟩,
    ⟨[15507], [15507], .contexts [
        ⟨13, false, false, [], [15507]⟩
      ]⟩,
    ⟨[82805, 9], [15507, 82805], .contexts [
        ⟨16844, false, false, [], []⟩,
        ⟨16845, true, false, [], [82805]⟩
      ]⟩,
    ⟨[82805, 15], [82805, 15], .source 74605⟩,
    ⟨[82805, 15], [78841], .contexts [
        ⟨16847, false, false, [], []⟩,
        ⟨16828, true, false, [], [15]⟩,
        ⟨231, false, false, [78843], []⟩,
        ⟨232, false, false, [78843], []⟩,
        ⟨15304, false, false, [], [11]⟩,
        ⟨5193, false, false, [], []⟩,
        ⟨5194, false, false, [], []⟩,
        ⟨5195, false, false, [], []⟩,
        ⟨5195, false, false, [], []⟩,
        ⟨5205, false, false, [], []⟩,
        ⟨672, true, false, [], [78841]⟩
      ]⟩,
    ⟨[78841, 15], [82805], .contexts [
        ⟨16848, true, false, [], [15]⟩,
        ⟨1, false, false, [82805], []⟩,
        ⟨16827, false, false, [], []⟩
      ]⟩,
    ⟨[82807], [78843, 13], .source 41468⟩,
    ⟨[78843, 13], [82807], .contexts [
        ⟨16850, true, false, [], []⟩
      ]⟩,
    ⟨[82807, 13], [78843], .contexts [
        ⟨16851, true, false, [], [13]⟩,
        ⟨59, false, false, [78843], []⟩,
        ⟨5214, false, false, [], []⟩
      ]⟩,
    ⟨[82807], [82807], .contexts []⟩,
    ⟨[82807], [82807], .contexts []⟩,
    ⟨[78843, 13], [82807], .contexts [
        ⟨16851, false, false, [], []⟩,
        ⟨16853, false, false, [], []⟩,
        ⟨16854, false, false, [], []⟩,
        ⟨16854, false, false, [], []⟩
      ]⟩,
    ⟨[15509], [15213, 743], .source 7819⟩,
    ⟨[15511], [15509, 15211], .source 7820⟩,
    ⟨[15511, 82807], [15511, 82807], .contexts []⟩,
    ⟨[15511, 82807], [15511, 82807], .contexts []⟩,
    ⟨[82807, 1], [82807, 1], .contexts []⟩,
    ⟨[82807], [82807], .contexts []⟩,
    ⟨[15511], [15511], .contexts [
        ⟨13, false, false, [], [15511]⟩
      ]⟩,
    ⟨[82807, 1], [15511, 82807], .contexts [
        ⟨16860, false, false, [], []⟩,
        ⟨16855, true, false, [], [1]⟩,
        ⟨246, false, false, [78843], []⟩,
        ⟨249, false, false, [78843], []⟩,
        ⟨15297, false, false, [], [13, 1, 13]⟩,
        ⟨15021, false, false, [15213], [1, 13]⟩,
        ⟨16856, true, false, [], [82657, 1, 13]⟩,
        ⟨15006, false, false, [15509], [13]⟩,
        ⟨16857, true, false, [], [78843, 13]⟩,
        ⟨16851, false, false, [15511], []⟩,
        ⟨16858, false, false, [], []⟩,
        ⟨16859, false, false, [], []⟩,
        ⟨16861, false, false, [15511], []⟩,
        ⟨16862, true, false, [], [82807]⟩
      ]⟩,
    ⟨[15513], [15271, 11853], .source 7821⟩,
    ⟨[82807, 7], [82807, 7], .contexts []⟩,
    ⟨[15513], [15513], .contexts [
        ⟨13, false, false, [], [15513]⟩
      ]⟩,
    ⟨[82807, 7], [15513, 77373], .contexts [
        ⟨16865, false, false, [], []⟩,
        ⟨16855, true, false, [], [7]⟩,
        ⟨73, false, false, [78843], []⟩,
        ⟨74, false, false, [78843], []⟩,
        ⟨5219, false, false, [], [13]⟩,
        ⟨15322, false, false, [], [13]⟩,
        ⟨15323, false, false, [], [13]⟩,
        ⟨15325, false, false, [], [13]⟩,
        ⟨15326, false, false, [], [13]⟩,
        ⟨13229, false, false, [15271], []⟩,
        ⟨16864, true, false, [], [77373]⟩,
        ⟨1301, false, false, [15513], []⟩,
        ⟨16866, true, false, [], [77373]⟩
      ]⟩,
    ⟨[15515], [15512], .source 7822⟩,
    ⟨[77373, 7], [15515, 82807], .contexts [
        ⟨16867, true, false, [15512], [7]⟩,
        ⟨38, false, false, [15512, 82807], []⟩,
        ⟨16868, true, false, [], [82807]⟩
      ]⟩,
    ⟨[1077, 82807], [1077, 82807], .contexts []⟩,
    ⟨[1077, 82807], [1077, 82807], .contexts []⟩,
    ⟨[82807, 15], [82807, 15], .contexts []⟩,
    ⟨[82807, 15], [1077, 82807], .contexts [
        ⟨16872, false, false, [], []⟩,
        ⟨16855, true, false, [], [15]⟩,
        ⟨88, false, false, [78843], []⟩,
        ⟨91, false, false, [78843], []⟩,
        ⟨15304, false, false, [], [13, 15, 13]⟩,
        ⟨5183, false, false, [], [15, 13]⟩,
        ⟨4909, false, false, [], [15, 13]⟩,
        ⟨4910, false, false, [], [15, 13]⟩,
        ⟨4910, false, false, [], [15, 13]⟩,
        ⟨5211, false, false, [1077], [13]⟩,
        ⟨16851, false, false, [1077], []⟩,
        ⟨16870, false, false, [], []⟩,
        ⟨16871, false, false, [], []⟩,
        ⟨16861, false, false, [1077], []⟩,
        ⟨4913, true, false, [], [82807]⟩
      ]⟩,
    ⟨[82809], [82659, 9], .source 41469⟩,
    ⟨[82659, 9], [82809], .contexts [
        ⟨16874, true, false, [], []⟩
      ]⟩,
    ⟨[82809, 9], [82659], .contexts [
        ⟨16875, true, false, [], [9]⟩,
        ⟨46, false, false, [82659], []⟩,
        ⟨15035, false, false, [], []⟩
      ]⟩,
    ⟨[82809], [82809], .contexts []⟩,
    ⟨[82809], [82809], .contexts []⟩,
    ⟨[82659, 9], [82809], .contexts [
        ⟨16875, false, false, [], []⟩,
        ⟨16877, false, false, [], []⟩,
        ⟨16878, false, false, [], []⟩,
        ⟨16878, false, false, [], []⟩
      ]⟩,
    ⟨[15517], [11909, 15221], .source 7823⟩,
    ⟨[15517, 82809], [15517, 82809], .contexts []⟩,
    ⟨[82809], [82809], .contexts []⟩,
    ⟨[82809, 1], [15517, 82809], .contexts [
        ⟨16879, true, false, [], [1]⟩,
        ⟨691, false, false, [82659], []⟩,
        ⟨694, false, false, [82659], []⟩,
        ⟨15066, false, false, [], [9, 1, 9]⟩,
        ⟨14938, false, false, [11907], [1, 9]⟩,
        ⟨13282, true, false, [], [82649, 1, 9]⟩,
        ⟨15043, false, false, [11909], [9]⟩,
        ⟨16880, true, false, [], [82659, 9]⟩,
        ⟨16875, false, false, [15517], []⟩,
        ⟨16881, false, false, [], []⟩,
        ⟨16882, false, false, [15517], []⟩,
        ⟨13, true, false, [], [15517, 82809]⟩
      ]⟩,
    ⟨[15469, 82793], [15469, 82793], .contexts []⟩,
    ⟨[15469, 82793], [15469, 82793], .contexts []⟩,
    ⟨[15519], [15469, 15437], .source 7824⟩,
    ⟨[82809, 3], [15519, 82677], .contexts [
        ⟨16879, true, false, [], [3]⟩,
        ⟨196, false, false, [82659], []⟩,
        ⟨197, false, false, [82659], []⟩,
        ⟨16693, false, false, [], [9]⟩,
        ⟨16884, false, false, [], [9]⟩,
        ⟨16885, false, false, [], [9]⟩,
        ⟨16885, false, false, [], [9]⟩,
        ⟨16701, false, false, [15469], []⟩,
        ⟨16886, true, false, [], [82677]⟩,
        ⟨15283, false, false, [15519], []⟩,
        ⟨13, true, false, [], [15519, 82677]⟩
      ]⟩,
    ⟨[15521], [15518], .source 7825⟩,
    ⟨[82677, 3], [15521, 82809], .contexts [
        ⟨16887, true, false, [15518], [3]⟩,
        ⟨20, false, false, [15518, 82809], []⟩,
        ⟨16888, true, false, [], [82809]⟩
      ]⟩,
    ⟨[82809, 7], [14813, 77319], .contexts [
        ⟨16879, true, false, [], [7]⟩,
        ⟨1084, false, false, [82659], []⟩,
        ⟨1085, false, false, [82659], []⟩,
        ⟨15095, false, false, [], [9]⟩,
        ⟨848, false, false, [], [9]⟩,
        ⟨758, false, false, [], [9]⟩,
        ⟨758, false, false, [], [9]⟩,
        ⟨13270, false, false, [], []⟩,
        ⟨14641, false, false, [11893], []⟩,
        ⟨14642, true, false, [], [77319]⟩,
        ⟨4296, false, false, [14813], []⟩,
        ⟨13, true, false, [], [14813, 77319]⟩
      ]⟩,
    ⟨[15523], [14812], .source 7826⟩,
    ⟨[77319, 7], [15523, 82809], .contexts [
        ⟨16890, true, false, [14812], [7]⟩,
        ⟨38, false, false, [14812, 82809], []⟩,
        ⟨16891, true, false, [], [82809]⟩
      ]⟩,
    ⟨[15247, 82671], [15247, 82671], .contexts []⟩,
    ⟨[15247, 82671], [15247, 82671], .contexts []⟩,
    ⟨[15525], [15247, 15261], .source 7827⟩]

/-- Exact literal claimed equations and contextual derivations, block 264. -/
def y322TCIndexRaw264 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82809, 11], [15525, 82675], .contexts [
        ⟨16879, true, false, [], [11]⟩,
        ⟨2344, false, false, [82659], []⟩,
        ⟨2346, false, false, [82659], []⟩,
        ⟨15205, false, false, [], [9, 11, 9]⟩,
        ⟨15209, false, false, [], [9, 11, 9]⟩,
        ⟨16893, false, false, [], [9, 11, 9]⟩,
        ⟨16894, false, false, [], [9, 11, 9]⟩,
        ⟨16894, false, false, [], [9, 11, 9]⟩,
        ⟨15178, false, false, [15247], [11, 9]⟩,
        ⟨15212, false, false, [15247], [9]⟩,
        ⟨15258, false, false, [15247], []⟩,
        ⟨16895, true, false, [], [82675]⟩,
        ⟨15243, false, false, [15525], []⟩
      ]⟩,
    ⟨[82809, 11], [15525, 82675], .contexts [
        ⟨16896, false, false, [], []⟩,
        ⟨13, true, false, [], [15525, 82675]⟩
      ]⟩,
    ⟨[15527], [15524], .source 7828⟩,
    ⟨[82675, 11], [15527, 82809], .contexts [
        ⟨16897, true, false, [15524], [11]⟩,
        ⟨53, false, false, [15524, 82809], []⟩,
        ⟨16898, true, false, [], [82809]⟩
      ]⟩,
    ⟨[11889, 82809], [11889, 82809], .contexts []⟩,
    ⟨[82809, 13], [11889, 82809], .contexts [
        ⟨16879, true, false, [], [13]⟩,
        ⟨201, false, false, [82659], []⟩,
        ⟨202, false, false, [82659], []⟩,
        ⟨15072, false, false, [], [9]⟩,
        ⟨16875, false, false, [11889], []⟩,
        ⟨16900, false, false, [], []⟩,
        ⟨16882, false, false, [11889], []⟩,
        ⟨15050, true, false, [], [82809]⟩
      ]⟩,
    ⟨[15223, 82783], [15223, 82783], .contexts []⟩,
    ⟨[82809, 15], [15223, 82783], .contexts [
        ⟨16879, true, false, [], [15]⟩,
        ⟨205, false, false, [82659], []⟩,
        ⟨206, false, false, [82659], []⟩,
        ⟨15080, false, false, [], [9]⟩,
        ⟨16584, false, false, [15223], []⟩,
        ⟨16902, false, false, [], []⟩,
        ⟨16590, false, false, [15223], []⟩,
        ⟨15056, true, false, [], [82783]⟩
      ]⟩,
    ⟨[82783, 15], [15225, 82809], .contexts [
        ⟨16903, true, false, [15222], [15]⟩,
        ⟨1, false, false, [15222, 82809], []⟩,
        ⟨15058, true, false, [], [82809]⟩
      ]⟩,
    ⟨[82811], [82655, 5], .source 41470⟩,
    ⟨[82655, 5], [82811], .contexts [
        ⟨16905, true, false, [], []⟩
      ]⟩,
    ⟨[82811, 5], [82655], .contexts [
        ⟨16906, true, false, [], [5]⟩,
        ⟨28, false, false, [82655], []⟩,
        ⟨14977, false, false, [], []⟩
      ]⟩,
    ⟨[82811], [82811], .contexts []⟩,
    ⟨[82811], [82811], .contexts []⟩,
    ⟨[82655, 5], [82811], .contexts [
        ⟨16906, false, false, [], []⟩,
        ⟨16908, false, false, [], []⟩,
        ⟨16909, false, false, [], []⟩,
        ⟨16909, false, false, [], []⟩
      ]⟩,
    ⟨[15305, 82689], [15305, 82689], .contexts []⟩,
    ⟨[15305, 82689], [15305, 82689], .contexts []⟩,
    ⟨[15529], [15305, 15329], .source 7829⟩,
    ⟨[82811, 9], [82811, 9], .contexts []⟩,
    ⟨[15529], [15529], .contexts [
        ⟨13, false, false, [], [15529]⟩
      ]⟩,
    ⟨[82811, 9], [15529, 82705], .contexts [
        ⟨16914, false, false, [], []⟩,
        ⟨16910, true, false, [], [9]⟩,
        ⟨1265, false, false, [82655], []⟩,
        ⟨1266, false, false, [82655], []⟩,
        ⟨15431, false, false, [], [5]⟩,
        ⟨16911, false, false, [], [5]⟩,
        ⟨16912, false, false, [], [5]⟩,
        ⟨16912, false, false, [], [5]⟩,
        ⟨15603, false, false, [15305], []⟩,
        ⟨16913, true, false, [], [82705]⟩,
        ⟨15607, false, false, [15529], []⟩,
        ⟨16915, true, false, [], [82705]⟩
      ]⟩,
    ⟨[15531], [15528], .source 7830⟩,
    ⟨[82705, 9], [15531, 82811], .contexts [
        ⟨16916, true, false, [15528], [9]⟩,
        ⟨46, false, false, [15528, 82811], []⟩,
        ⟨16917, true, false, [], [82811]⟩
      ]⟩,
    ⟨[82811, 11], [82811, 11], .contexts []⟩,
    ⟨[82811, 11], [15205, 82653], .contexts [
        ⟨16919, false, false, [], []⟩,
        ⟨16910, true, false, [], [11]⟩,
        ⟨174, false, false, [82655], []⟩,
        ⟨175, false, false, [82655], []⟩,
        ⟨14975, false, false, [], [5]⟩,
        ⟨4563, false, false, [], [5]⟩,
        ⟨4564, false, false, [], [5]⟩,
        ⟨4564, false, false, [], [5]⟩,
        ⟨14967, false, false, [], []⟩,
        ⟨16515, false, false, [], []⟩,
        ⟨16516, false, false, [], []⟩,
        ⟨16516, false, false, [], []⟩,
        ⟨14969, false, false, [15205], []⟩,
        ⟨16517, true, false, [], [82653]⟩
      ]⟩,
    ⟨[82653, 11], [15203, 82811], .contexts [
        ⟨16920, true, false, [15204], [11]⟩,
        ⟨53, false, false, [15204, 82811], []⟩,
        ⟨16519, true, false, [], [82811]⟩
      ]⟩,
    ⟨[15305, 82721], [15305, 82721], .contexts []⟩,
    ⟨[15305, 82721], [15305, 82721], .contexts []⟩,
    ⟨[15305, 82769], [15305, 82769], .contexts []⟩,
    ⟨[15305, 82769], [15305, 82769], .contexts []⟩,
    ⟨[82811, 13], [82811, 13], .contexts []⟩,
    ⟨[15305], [15305], .contexts [
        ⟨13, false, false, [], [15305]⟩
      ]⟩,
    ⟨[82811, 13], [15305, 82769], .contexts [
        ⟨16926, false, false, [], []⟩,
        ⟨16910, true, false, [], [13]⟩,
        ⟨179, false, false, [82655], []⟩,
        ⟨180, false, false, [82655], []⟩,
        ⟨15794, false, false, [], [5]⟩,
        ⟨16922, false, false, [], [5]⟩,
        ⟨16923, false, false, [], [5]⟩,
        ⟨16923, false, false, [], [5]⟩,
        ⟨16402, false, false, [15305], []⟩,
        ⟨16924, false, false, [], []⟩,
        ⟨16925, false, false, [], []⟩,
        ⟨16409, false, false, [15305], []⟩,
        ⟨16927, true, false, [], [82769]⟩
      ]⟩,
    ⟨[15303], [15304], .contexts [
        ⟨15430, true, true, [], []⟩
      ]⟩,
    ⟨[82813], [82811, 7], .source 41471⟩,
    ⟨[82811, 7], [82813], .contexts [
        ⟨16930, true, false, [], []⟩
      ]⟩,
    ⟨[82813], [82813], .contexts []⟩,
    ⟨[82813], [82813], .contexts []⟩,
    ⟨[82811, 7], [82813], .contexts [
        ⟨16931, false, false, [], []⟩,
        ⟨16932, false, false, [], []⟩,
        ⟨16933, false, false, [], []⟩,
        ⟨16933, false, false, [], []⟩
      ]⟩,
    ⟨[82811, 5], [82655], .contexts [
        ⟨16907, false, false, [], []⟩,
        ⟨14976, false, false, [], []⟩,
        ⟨14977, false, false, [], []⟩,
        ⟨14977, false, false, [], []⟩
      ]⟩,
    ⟨[15207, 77329], [15207, 77329], .contexts []⟩,
    ⟨[15207, 77329], [15207, 77329], .contexts []⟩,
    ⟨[15533], [721, 11973], .source 7831⟩,
    ⟨[15535], [15207, 15533], .source 7832⟩,
    ⟨[82811, 5, 7, 5], [15535, 77291], .contexts [
        ⟨16935, false, false, [], [7, 5]⟩,
        ⟨14990, false, false, [], [5]⟩,
        ⟨16936, false, false, [], [5]⟩,
        ⟨16937, false, false, [], [5]⟩,
        ⟨16937, false, false, [], [5]⟩,
        ⟨13, false, false, [15207, 722], [723, 77329, 5]⟩,
        ⟨2018, true, false, [15207], [5]⟩,
        ⟨805, true, false, [15207], [5]⟩,
        ⟨4007, true, false, [15207, 722], [13, 5]⟩,
        ⟨4007, true, false, [15207, 722], [13, 5]⟩,
        ⟨4006, true, false, [15207, 722], [13, 5]⟩,
        ⟨2007, true, false, [15207, 722], [13, 5]⟩,
        ⟨69, true, false, [15207, 722, 77253], [5]⟩,
        ⟨68, true, false, [15207, 722, 77253], [5]⟩,
        ⟨4000, false, false, [15207, 722], [5, 5]⟩,
        ⟨28, false, false, [15207, 722, 78277], []⟩,
        ⟨2006, false, true, [15207], [78277]⟩,
        ⟨13348, false, false, [15207, 721], []⟩,
        ⟨16938, true, false, [15207], [77291]⟩,
        ⟨16939, true, false, [], [77291]⟩
      ]⟩,
    ⟨[15537], [15535, 15425], .source 7833⟩,
    ⟨[82813, 5], [15537, 82775], .contexts [
        ⟨16934, true, false, [], [5]⟩,
        ⟨1043, false, false, [82811], []⟩,
        ⟨1046, false, false, [82811], []⟩,
        ⟨16940, false, false, [], [7]⟩,
        ⟨16477, false, false, [15535], []⟩,
        ⟨16941, true, false, [], [82775]⟩,
        ⟨16471, false, false, [15537], []⟩,
        ⟨13, true, false, [], [15537, 82775]⟩
      ]⟩,
    ⟨[15539], [15536], .source 7834⟩,
    ⟨[82775, 5], [15539, 82813], .contexts [
        ⟨16942, true, false, [15536], [5]⟩,
        ⟨28, false, false, [15536, 82813], []⟩,
        ⟨16943, true, false, [], [82813]⟩
      ]⟩,
    ⟨[15529, 82705], [15529, 82705], .contexts []⟩,
    ⟨[15529, 82705], [15529, 82705], .contexts []⟩,
    ⟨[15529, 82703], [15529, 82703], .contexts []⟩,
    ⟨[82813, 9], [15529, 82703], .contexts [
        ⟨16934, true, false, [], [9]⟩,
        ⟨1534, false, false, [82811], []⟩,
        ⟨1535, false, false, [82811], []⟩,
        ⟨16914, false, false, [], [7]⟩,
        ⟨16916, false, false, [], [7]⟩,
        ⟨16945, false, false, [], [7]⟩,
        ⟨16946, false, false, [], [7]⟩,
        ⟨16946, false, false, [], [7]⟩,
        ⟨15589, false, false, [15529], []⟩,
        ⟨16947, false, false, [], []⟩,
        ⟨15585, false, false, [15529], []⟩,
        ⟨16915, true, false, [], [82703]⟩
      ]⟩,
    ⟨[82703, 9], [15531, 82813], .contexts [
        ⟨16948, true, false, [15528], [9]⟩,
        ⟨46, false, false, [15528, 82813], []⟩,
        ⟨16917, true, false, [], [82813]⟩
      ]⟩,
    ⟨[82811, 11], [15205, 82653], .contexts [
        ⟨16919, false, false, [], []⟩,
        ⟨16920, false, false, [], []⟩,
        ⟨16515, false, false, [], []⟩,
        ⟨16516, false, false, [], []⟩,
        ⟨16516, false, false, [], []⟩
      ]⟩,
    ⟨[82813, 11], [15205, 82651], .contexts [
        ⟨16934, true, false, [], [11]⟩,
        ⟨1051, false, false, [82811], []⟩,
        ⟨1052, false, false, [82811], []⟩,
        ⟨16950, false, false, [], [7]⟩,
        ⟨16543, false, false, [], []⟩,
        ⟨16544, false, false, [], []⟩,
        ⟨16545, false, false, [], []⟩,
        ⟨16546, false, false, [], []⟩,
        ⟨16548, false, false, [], []⟩,
        ⟨16549, false, false, [], []⟩
      ]⟩,
    ⟨[82651, 11], [15203, 82813], .contexts [
        ⟨16951, true, false, [15204], [11]⟩,
        ⟨53, false, false, [15204, 82813], []⟩,
        ⟨16519, true, false, [], [82813]⟩
      ]⟩,
    ⟨[82811, 13], [15305, 82769], .contexts [
        ⟨16926, false, false, [], []⟩,
        ⟨16928, false, false, [], []⟩,
        ⟨16924, false, false, [], []⟩,
        ⟨16925, false, false, [], []⟩,
        ⟨16925, false, false, [], []⟩
      ]⟩,
    ⟨[15305, 82771], [15305, 82771], .contexts []⟩,
    ⟨[82813, 13], [15305, 82771], .contexts [
        ⟨16934, true, false, [], [13]⟩,
        ⟨1056, false, false, [82811], []⟩,
        ⟨1057, false, false, [82811], []⟩,
        ⟨16953, false, false, [], [7]⟩,
        ⟨16418, false, false, [15305], []⟩,
        ⟨16954, false, false, [], []⟩,
        ⟨16424, false, false, [15305], []⟩,
        ⟨16927, true, false, [], [82771]⟩
      ]⟩,
    ⟨[82815], [79201, 5], .source 41472⟩,
    ⟨[79201, 5], [82815], .contexts [
        ⟨16956, true, false, [], []⟩
      ]⟩,
    ⟨[82815, 5], [79201], .contexts [
        ⟨16957, true, false, [], [5]⟩,
        ⟨28, false, false, [79201], []⟩,
        ⟨6349, false, false, [], []⟩
      ]⟩,
    ⟨[82815], [82815], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 265. -/
def y322TCIndexRaw265 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82815], [82815], .contexts []⟩,
    ⟨[79201, 5], [82815], .contexts [
        ⟨16957, false, false, [], []⟩,
        ⟨16959, false, false, [], []⟩,
        ⟨16960, false, false, [], []⟩,
        ⟨16960, false, false, [], []⟩
      ]⟩,
    ⟨[7357, 82655], [7357, 82655], .contexts []⟩,
    ⟨[7357, 82655], [7357, 82655], .contexts []⟩,
    ⟨[7357, 82655, 5], [7357, 82811], .contexts [
        ⟨16906, false, false, [7357], []⟩
      ]⟩,
    ⟨[7357, 82811], [7357, 82811], .contexts []⟩,
    ⟨[7357, 82811], [7357, 82811], .contexts []⟩,
    ⟨[7357, 82811], [7357, 82811], .contexts []⟩,
    ⟨[82815, 1], [82815, 1], .contexts []⟩,
    ⟨[7357, 82811], [7357, 82811], .contexts []⟩,
    ⟨[7357], [7357], .contexts [
        ⟨13, false, false, [], [7357]⟩
      ]⟩,
    ⟨[7357, 82811], [7357, 82811], .contexts [
        ⟨16970, true, false, [], [82811]⟩
      ]⟩,
    ⟨[82815, 1], [7357, 82811], .contexts [
        ⟨16968, false, false, [], []⟩,
        ⟨16961, true, false, [], [1]⟩,
        ⟨161, false, false, [79201], []⟩,
        ⟨162, false, false, [79201], []⟩,
        ⟨14985, false, false, [], [5]⟩,
        ⟨16962, false, false, [], [5]⟩,
        ⟨16963, false, false, [], [5]⟩,
        ⟨16963, false, false, [], [5]⟩,
        ⟨16964, false, false, [], []⟩,
        ⟨16965, false, false, [], []⟩,
        ⟨16966, false, false, [], []⟩,
        ⟨16967, false, false, [], []⟩,
        ⟨16969, false, false, [], []⟩,
        ⟨16971, false, false, [], []⟩
      ]⟩,
    ⟨[82811, 1], [7355, 82815], .contexts [
        ⟨16972, true, false, [7356], [1]⟩,
        ⟨8, false, false, [7356, 82815], []⟩,
        ⟨10990, true, false, [], [82815]⟩
      ]⟩,
    ⟨[82815, 9], [82815, 9], .contexts []⟩,
    ⟨[82815, 9], [82667], .contexts [
        ⟨16974, false, false, [], []⟩,
        ⟨16961, true, false, [], [9]⟩,
        ⟨1265, false, false, [79201], []⟩,
        ⟨1266, false, false, [79201], []⟩,
        ⟨6352, false, false, [], [5]⟩,
        ⟨6353, false, false, [], [5]⟩,
        ⟨5603, false, false, [], [5]⟩,
        ⟨5604, false, false, [], [5]⟩,
        ⟨5604, false, false, [], [5]⟩,
        ⟨15134, false, false, [], []⟩,
        ⟨15135, false, false, [], []⟩,
        ⟨15136, false, false, [], []⟩,
        ⟨15136, false, false, [], []⟩,
        ⟨15143, false, false, [], []⟩,
        ⟨672, true, false, [], [82667]⟩
      ]⟩,
    ⟨[79381, 5], [15229, 82663], .contexts [
        ⟨15100, false, false, [], []⟩
      ]⟩,
    ⟨[15229, 82663], [15229, 82663], .contexts []⟩,
    ⟨[15229, 82663], [15229, 82663], .contexts []⟩,
    ⟨[82815, 11], [82815, 11], .contexts []⟩,
    ⟨[15229, 82663], [15229, 82663], .contexts [
        ⟨15102, false, false, [15229], []⟩
      ]⟩,
    ⟨[15229], [15229], .contexts [
        ⟨13, false, false, [], [15229]⟩
      ]⟩,
    ⟨[15229, 82663], [15229, 82663], .contexts [
        ⟨16981, true, false, [], [82663]⟩
      ]⟩,
    ⟨[82815, 11], [15229, 82663], .contexts [
        ⟨16979, false, false, [], []⟩,
        ⟨16961, true, false, [], [11]⟩,
        ⟨174, false, false, [79201], []⟩,
        ⟨175, false, false, [79201], []⟩,
        ⟨6854, false, false, [], [5]⟩,
        ⟨6846, false, false, [], [5]⟩,
        ⟨6847, false, false, [], [5]⟩,
        ⟨6847, false, false, [], [5]⟩,
        ⟨16976, false, false, [], []⟩,
        ⟨16977, false, false, [], []⟩,
        ⟨16978, false, false, [], []⟩,
        ⟨16978, false, false, [], []⟩,
        ⟨16980, false, false, [], []⟩,
        ⟨16982, false, false, [], []⟩
      ]⟩,
    ⟨[15227], [15228], .contexts [
        ⟨15099, true, true, [], []⟩
      ]⟩,
    ⟨[82663, 11], [15227, 82815], .contexts [
        ⟨16983, true, false, [15228], [11]⟩,
        ⟨53, false, false, [15228, 82815], []⟩,
        ⟨16984, true, false, [], [82815]⟩
      ]⟩,
    ⟨[2575, 82815], [2575, 82815], .contexts []⟩,
    ⟨[2575, 82815], [2575, 82815], .contexts []⟩,
    ⟨[82815, 13], [82815, 13], .contexts []⟩,
    ⟨[82815], [82815], .contexts []⟩,
    ⟨[82815, 13], [2575, 82815], .contexts [
        ⟨16988, false, false, [], []⟩,
        ⟨16961, true, false, [], [13]⟩,
        ⟨179, false, false, [79201], []⟩,
        ⟨180, false, false, [79201], []⟩,
        ⟨6359, false, false, [], [5]⟩,
        ⟨6361, false, false, [], [5]⟩,
        ⟨6357, false, false, [], [5]⟩,
        ⟨6358, false, false, [], [5]⟩,
        ⟨6358, false, false, [], [5]⟩,
        ⟨16957, false, false, [2575], []⟩,
        ⟨16986, false, false, [], []⟩,
        ⟨16987, false, false, [], []⟩,
        ⟨16989, false, false, [2575], []⟩,
        ⟨5618, true, false, [], [82815]⟩
      ]⟩,
    ⟨[79015, 5], [79195], .contexts [
        ⟨6311, false, false, [], []⟩
      ]⟩,
    ⟨[82815, 15], [82815, 15], .contexts []⟩,
    ⟨[82815, 15], [79195], .contexts [
        ⟨16992, false, false, [], []⟩,
        ⟨16961, true, false, [], [15]⟩,
        ⟨184, false, false, [79201], []⟩,
        ⟨185, false, false, [79201], []⟩,
        ⟨6346, false, false, [], [5]⟩,
        ⟨5562, false, false, [], [5]⟩,
        ⟨5563, false, false, [], [5]⟩,
        ⟨5563, false, false, [], [5]⟩,
        ⟨16991, false, false, [], []⟩,
        ⟨6305, false, false, [], []⟩,
        ⟨6306, false, false, [], []⟩,
        ⟨6306, false, false, [], []⟩,
        ⟨6805, false, false, [], []⟩,
        ⟨6806, false, false, [], []⟩
      ]⟩,
    ⟨[79195, 15], [82815], .contexts [
        ⟨16993, true, false, [], [15]⟩,
        ⟨1, false, false, [82815], []⟩,
        ⟨16960, false, false, [], []⟩
      ]⟩,
    ⟨[82817], [82815, 7], .source 41473⟩,
    ⟨[82815, 7], [82817], .contexts [
        ⟨16995, true, false, [], []⟩
      ]⟩,
    ⟨[82817, 7], [82815], .contexts [
        ⟨16996, true, false, [], [7]⟩,
        ⟨38, false, false, [82815], []⟩,
        ⟨16960, false, false, [], []⟩
      ]⟩,
    ⟨[82817], [82817], .contexts []⟩,
    ⟨[82817], [82817], .contexts []⟩,
    ⟨[82815, 7], [82817], .contexts [
        ⟨16996, false, false, [], []⟩,
        ⟨16998, false, false, [], []⟩,
        ⟨16999, false, false, [], []⟩,
        ⟨16999, false, false, [], []⟩
      ]⟩,
    ⟨[7357, 82811, 7], [7357, 82813], .contexts [
        ⟨16931, false, false, [7357], []⟩
      ]⟩,
    ⟨[7357, 82813], [7357, 82813], .contexts []⟩,
    ⟨[7357, 82813], [7357, 82813], .contexts []⟩,
    ⟨[7357, 82813], [7357, 82813], .contexts []⟩,
    ⟨[82813], [82813], .contexts []⟩,
    ⟨[7357, 82813], [7357, 82813], .contexts [
        ⟨17005, false, false, [7357], []⟩
      ]⟩,
    ⟨[7357, 82813], [7357, 82813], .contexts [
        ⟨16970, true, false, [], [82813]⟩
      ]⟩,
    ⟨[82817, 1], [7357, 82813], .contexts [
        ⟨17000, true, false, [], [1]⟩,
        ⟨1027, false, false, [82815], []⟩,
        ⟨1028, false, false, [82815], []⟩,
        ⟨16968, false, false, [], [7]⟩,
        ⟨16972, false, false, [], [7]⟩,
        ⟨16965, false, false, [], [7]⟩,
        ⟨16967, false, false, [], [7]⟩,
        ⟨16967, false, false, [], [7]⟩,
        ⟨17001, false, false, [], []⟩,
        ⟨17002, false, false, [], []⟩,
        ⟨17003, false, false, [], []⟩,
        ⟨17004, false, false, [], []⟩,
        ⟨17006, false, false, [], []⟩,
        ⟨17007, false, false, [], []⟩
      ]⟩,
    ⟨[82813, 1], [7355, 82817], .contexts [
        ⟨17008, true, false, [7356], [1]⟩,
        ⟨8, false, false, [7356, 82817], []⟩,
        ⟨10990, true, false, [], [82817]⟩
      ]⟩,
    ⟨[15541], [9043, 11917], .source 7835⟩,
    ⟨[15543], [10117, 15541], .source 7836⟩,
    ⟨[15545], [15543, 15243], .source 7837⟩,
    ⟨[82817, 5], [15545, 82671], .contexts [
        ⟨17000, true, false, [], [5]⟩,
        ⟨1043, false, false, [82815], []⟩,
        ⟨1046, false, false, [82815], []⟩,
        ⟨16958, false, false, [], [7, 5, 7]⟩,
        ⟨6348, false, false, [], [7, 5, 7]⟩,
        ⟨6349, false, false, [], [7, 5, 7]⟩,
        ⟨6349, false, false, [], [7, 5, 7]⟩,
        ⟨6351, false, false, [], [5, 7]⟩,
        ⟨11881, false, false, [1887], [5, 7]⟩,
        ⟨12371, true, false, [], [77327, 5, 7]⟩,
        ⟨11880, false, false, [10117], [7]⟩,
        ⟨13306, false, false, [10117, 9043], [7]⟩,
        ⟨17010, true, false, [10117], [77293, 7]⟩,
        ⟨17011, true, false, [], [77293, 7]⟩,
        ⟨15191, false, false, [15543], []⟩,
        ⟨17012, true, false, [], [82671]⟩,
        ⟨15194, false, false, [15545], []⟩
      ]⟩,
    ⟨[82817, 5], [15545, 82671], .contexts [
        ⟨17013, false, false, [], []⟩,
        ⟨13, true, false, [], [15545, 82671]⟩
      ]⟩,
    ⟨[15547], [15544], .source 7838⟩,
    ⟨[82671, 5], [15547, 82817], .contexts [
        ⟨17014, true, false, [15544], [5]⟩,
        ⟨28, false, false, [15544, 82817], []⟩,
        ⟨17015, true, false, [], [82817]⟩
      ]⟩,
    ⟨[82817, 9], [82669], .contexts [
        ⟨17000, true, false, [], [9]⟩,
        ⟨1534, false, false, [82815], []⟩,
        ⟨1535, false, false, [82815], []⟩,
        ⟨16974, false, false, [], [7]⟩,
        ⟨16975, false, false, [], [7]⟩,
        ⟨15135, false, false, [], [7]⟩,
        ⟨15136, false, false, [], [7]⟩,
        ⟨15136, false, false, [], [7]⟩,
        ⟨15153, false, false, [], []⟩,
        ⟨15154, false, false, [], []⟩,
        ⟨15155, false, false, [], []⟩,
        ⟨15155, false, false, [], []⟩,
        ⟨15170, false, false, [], []⟩,
        ⟨672, true, false, [], [82669]⟩
      ]⟩,
    ⟨[82669, 9], [82817], .contexts [
        ⟨17017, true, false, [], [9]⟩,
        ⟨46, false, false, [82817], []⟩,
        ⟨16999, false, false, [], []⟩
      ]⟩,
    ⟨[15229, 82663, 7], [15229, 82661], .contexts [
        ⟨15088, false, false, [15229], []⟩
      ]⟩,
    ⟨[15229, 82661], [15229, 82661], .contexts []⟩,
    ⟨[15229, 82661], [15229, 82661], .contexts []⟩,
    ⟨[15229, 82661], [15229, 82661], .contexts []⟩,
    ⟨[15229, 82661], [15229, 82661], .contexts [
        ⟨15076, false, false, [15229], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 266. -/
def y322TCIndexRaw266 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15229, 82661], [15229, 82661], .contexts [
        ⟨16981, true, false, [], [82661]⟩
      ]⟩,
    ⟨[82817, 11], [15229, 82661], .contexts [
        ⟨17000, true, false, [], [11]⟩,
        ⟨1051, false, false, [82815], []⟩,
        ⟨1052, false, false, [82815], []⟩,
        ⟨16979, false, false, [], [7]⟩,
        ⟨16983, false, false, [], [7]⟩,
        ⟨16977, false, false, [], [7]⟩,
        ⟨16978, false, false, [], [7]⟩,
        ⟨16978, false, false, [], [7]⟩,
        ⟨17019, false, false, [], []⟩,
        ⟨17020, false, false, [], []⟩,
        ⟨17021, false, false, [], []⟩,
        ⟨17022, false, false, [], []⟩,
        ⟨17023, false, false, [], []⟩,
        ⟨17024, false, false, [], []⟩
      ]⟩,
    ⟨[82661, 11], [15227, 82817], .contexts [
        ⟨17025, true, false, [15228], [11]⟩,
        ⟨53, false, false, [15228, 82817], []⟩,
        ⟨16984, true, false, [], [82817]⟩
      ]⟩,
    ⟨[2575, 82817], [2575, 82817], .contexts []⟩,
    ⟨[82817], [82817], .contexts []⟩,
    ⟨[82817, 13], [2575, 82817], .contexts [
        ⟨17000, true, false, [], [13]⟩,
        ⟨1056, false, false, [82815], []⟩,
        ⟨1057, false, false, [82815], []⟩,
        ⟨16988, false, false, [], [7]⟩,
        ⟨16990, false, false, [], [7]⟩,
        ⟨16986, false, false, [], [7]⟩,
        ⟨16987, false, false, [], [7]⟩,
        ⟨16987, false, false, [], [7]⟩,
        ⟨16996, false, false, [2575], []⟩,
        ⟨17027, false, false, [], []⟩,
        ⟨17028, false, false, [2575], []⟩,
        ⟨5618, true, false, [], [82817]⟩
      ]⟩,
    ⟨[79195, 7], [79193], .contexts [
        ⟨6303, false, false, [], []⟩
      ]⟩,
    ⟨[82817, 15], [79193], .contexts [
        ⟨17000, true, false, [], [15]⟩,
        ⟨1063, false, false, [82815], []⟩,
        ⟨1064, false, false, [82815], []⟩,
        ⟨16992, false, false, [], [7]⟩,
        ⟨16993, false, false, [], [7]⟩,
        ⟨6305, false, false, [], [7]⟩,
        ⟨6306, false, false, [], [7]⟩,
        ⟨6306, false, false, [], [7]⟩,
        ⟨17030, false, false, [], []⟩,
        ⟨6291, false, false, [], []⟩,
        ⟨6292, false, false, [], []⟩,
        ⟨6292, false, false, [], []⟩,
        ⟨6790, false, false, [], []⟩,
        ⟨6791, false, false, [], []⟩
      ]⟩,
    ⟨[79193, 15], [82817], .contexts [
        ⟨17031, true, false, [], [15]⟩,
        ⟨1, false, false, [82817], []⟩,
        ⟨16999, false, false, [], []⟩
      ]⟩,
    ⟨[82819], [79191, 13], .source 41474⟩,
    ⟨[79191, 13], [82819], .contexts [
        ⟨17033, true, false, [], []⟩
      ]⟩,
    ⟨[82819, 13], [79191], .contexts [
        ⟨17034, true, false, [], [13]⟩,
        ⟨59, false, false, [79191], []⟩,
        ⟨6282, false, false, [], []⟩
      ]⟩,
    ⟨[82819], [82819], .contexts []⟩,
    ⟨[82819], [82819], .contexts []⟩,
    ⟨[79191, 13], [82819], .contexts [
        ⟨17034, false, false, [], []⟩,
        ⟨17036, false, false, [], []⟩,
        ⟨17037, false, false, [], []⟩,
        ⟨17037, false, false, [], []⟩
      ]⟩,
    ⟨[14715, 81405], [14715, 81405], .contexts []⟩,
    ⟨[14715, 81405], [14715, 81405], .contexts []⟩,
    ⟨[15549], [14715, 8409], .source 7839⟩,
    ⟨[15551], [15549, 8411], .source 7840⟩,
    ⟨[82819, 1], [15551, 81373], .contexts [
        ⟨17038, true, false, [], [1]⟩,
        ⟨246, false, false, [79191], []⟩,
        ⟨249, false, false, [79191], []⟩,
        ⟨14552, false, false, [], [13, 1, 13]⟩,
        ⟨17039, false, false, [], [13, 1, 13]⟩,
        ⟨17040, false, false, [], [13, 1, 13]⟩,
        ⟨17040, false, false, [], [13, 1, 13]⟩,
        ⟨9040, false, false, [14715], [1, 13]⟩,
        ⟨11518, false, false, [14715], [1, 13]⟩,
        ⟨17041, true, false, [], [80805, 1, 13]⟩,
        ⟨8447, false, false, [15549], [13]⟩,
        ⟨11511, false, false, [15549], []⟩,
        ⟨17042, true, false, [], [81373]⟩,
        ⟨8954, false, false, [15551], []⟩
      ]⟩,
    ⟨[82819, 1], [15551, 81373], .contexts [
        ⟨17043, false, false, [], []⟩,
        ⟨13, true, false, [], [15551, 81373]⟩
      ]⟩,
    ⟨[15553], [15550], .source 7841⟩,
    ⟨[81373, 1], [15553, 82819], .contexts [
        ⟨17044, true, false, [15550], [1]⟩,
        ⟨8, false, false, [15550, 82819], []⟩,
        ⟨17045, true, false, [], [82819]⟩
      ]⟩,
    ⟨[10295, 77385], [10295, 11953, 77297], .contexts [
        ⟨13322, false, false, [10295], []⟩
      ]⟩,
    ⟨[15555], [10295, 11953], .source 7842⟩,
    ⟨[15555, 77297], [15555, 77297], .contexts []⟩,
    ⟨[15557], [15555, 11963], .source 7843⟩,
    ⟨[82819, 7], [15557, 77517], .contexts [
        ⟨17038, true, false, [], [7]⟩,
        ⟨73, false, false, [79191], []⟩,
        ⟨74, false, false, [79191], []⟩,
        ⟨6308, false, false, [], [13]⟩,
        ⟨12481, false, false, [], [13]⟩,
        ⟨17047, false, false, [], [13]⟩,
        ⟨17048, true, false, [], [77297, 13]⟩,
        ⟨17049, false, false, [], [13]⟩,
        ⟨17049, false, false, [], [13]⟩,
        ⟨13335, false, false, [15555], []⟩,
        ⟨17050, true, false, [], [77517]⟩,
        ⟨13, true, false, [], [15557, 77517]⟩
      ]⟩,
    ⟨[15559], [15556], .source 7844⟩,
    ⟨[77517, 7], [15559, 82819], .contexts [
        ⟨17051, true, false, [15556], [7]⟩,
        ⟨38, false, false, [15556, 82819], []⟩,
        ⟨17052, true, false, [], [82819]⟩
      ]⟩,
    ⟨[82819, 9], [82803], .contexts [
        ⟨17038, true, false, [], [9]⟩,
        ⟨77, false, false, [79191], []⟩,
        ⟨78, false, false, [79191], []⟩,
        ⟨6294, false, false, [], [13]⟩,
        ⟨16796, false, false, [], []⟩,
        ⟨16797, false, false, [], []⟩,
        ⟨16798, false, false, [], []⟩,
        ⟨16798, false, false, [], []⟩,
        ⟨16801, false, false, [], []⟩,
        ⟨672, true, false, [], [82803]⟩
      ]⟩,
    ⟨[82803, 9], [82819], .contexts [
        ⟨17054, true, false, [], [9]⟩,
        ⟨46, false, false, [82819], []⟩,
        ⟨17037, false, false, [], []⟩
      ]⟩,
    ⟨[82819, 11], [82819, 11], .contexts []⟩,
    ⟨[82785], [82785], .contexts [
        ⟨16631, false, false, [], []⟩
      ]⟩,
    ⟨[82785], [82785], .contexts [
        ⟨672, true, false, [], [82785]⟩
      ]⟩,
    ⟨[82819, 11], [82785], .contexts [
        ⟨17056, false, false, [], []⟩,
        ⟨17038, true, false, [], [11]⟩,
        ⟨82, false, false, [79191], []⟩,
        ⟨83, false, false, [79191], []⟩,
        ⟨6782, false, false, [], [13]⟩,
        ⟨6777, false, false, [], [13]⟩,
        ⟨6778, false, false, [], [13]⟩,
        ⟨6778, false, false, [], [13]⟩,
        ⟨16619, false, false, [], []⟩,
        ⟨16620, false, false, [], []⟩,
        ⟨16621, false, false, [], []⟩,
        ⟨16621, false, false, [], []⟩,
        ⟨17057, false, false, [], []⟩,
        ⟨17058, false, false, [], []⟩
      ]⟩,
    ⟨[82785, 11], [82819], .contexts [
        ⟨17059, true, false, [], [11]⟩,
        ⟨53, false, false, [82819], []⟩,
        ⟨17037, false, false, [], []⟩
      ]⟩,
    ⟨[15219, 82671], [15219, 82671], .contexts []⟩,
    ⟨[15219, 82671], [15219, 82671], .contexts []⟩,
    ⟨[15499, 82819], [15499, 82819], .contexts []⟩,
    ⟨[15499, 82819], [15499, 82819], .contexts []⟩,
    ⟨[82819, 15], [82819, 15], .contexts []⟩,
    ⟨[82819], [82819], .contexts []⟩,
    ⟨[82819, 15], [15499, 82819], .contexts [
        ⟨17065, false, false, [], []⟩,
        ⟨17038, true, false, [], [15]⟩,
        ⟨88, false, false, [79191], []⟩,
        ⟨91, false, false, [79191], []⟩,
        ⟨15201, false, false, [], [13, 15, 13]⟩,
        ⟨17061, false, false, [], [13, 15, 13]⟩,
        ⟨17062, false, false, [], [13, 15, 13]⟩,
        ⟨17062, false, false, [], [13, 15, 13]⟩,
        ⟨15195, false, false, [15219], [15, 13]⟩,
        ⟨16818, true, false, [], [82671, 15, 13]⟩,
        ⟨15200, false, false, [15497], [13]⟩,
        ⟨16819, true, false, [], [79191, 13]⟩,
        ⟨17034, false, false, [15499], []⟩,
        ⟨17063, false, false, [], []⟩,
        ⟨17064, false, false, [], []⟩,
        ⟨17066, false, false, [15499], []⟩
      ]⟩,
    ⟨[82819, 15], [15499, 82819], .contexts [
        ⟨17067, false, false, [], []⟩,
        ⟨16822, true, false, [], [82819]⟩
      ]⟩,
    ⟨[82821], [79179, 5], .source 41475⟩,
    ⟨[79179, 5], [82821], .contexts [
        ⟨17069, true, false, [], []⟩
      ]⟩,
    ⟨[82821, 5], [79179], .contexts [
        ⟨17070, true, false, [], [5]⟩,
        ⟨28, false, false, [79179], []⟩,
        ⟨6208, false, false, [], []⟩
      ]⟩,
    ⟨[82821], [82821], .contexts []⟩,
    ⟨[82821], [82821], .contexts []⟩,
    ⟨[79179, 5], [82821], .contexts [
        ⟨17070, false, false, [], []⟩,
        ⟨17072, false, false, [], []⟩,
        ⟨17073, false, false, [], []⟩,
        ⟨17073, false, false, [], []⟩
      ]⟩,
    ⟨[82821, 1], [82821, 1], .contexts []⟩,
    ⟨[82821, 1], [79195], .contexts [
        ⟨17075, false, false, [], []⟩,
        ⟨17074, true, false, [], [1]⟩,
        ⟨161, false, false, [79179], []⟩,
        ⟨162, false, false, [79179], []⟩,
        ⟨6210, false, false, [], [5]⟩,
        ⟨6214, false, false, [], [5]⟩,
        ⟨5562, false, false, [], [5]⟩,
        ⟨5563, false, false, [], [5]⟩,
        ⟨5563, false, false, [], [5]⟩,
        ⟨16991, false, false, [], []⟩,
        ⟨6305, false, false, [], []⟩,
        ⟨6306, false, false, [], []⟩,
        ⟨6306, false, false, [], []⟩,
        ⟨6805, false, false, [], []⟩,
        ⟨6806, false, false, [], []⟩
      ]⟩,
    ⟨[79195, 1], [82821], .contexts [
        ⟨17076, true, false, [], [1]⟩,
        ⟨8, false, false, [82821], []⟩,
        ⟨17073, false, false, [], []⟩
      ]⟩,
    ⟨[82821, 11], [82821, 11], .contexts []⟩,
    ⟨[82821, 11], [79513], .contexts [
        ⟨17078, false, false, [], []⟩,
        ⟨17074, true, false, [], [11]⟩,
        ⟨174, false, false, [79179], []⟩,
        ⟨175, false, false, [79179], []⟩,
        ⟨6749, false, false, [], [5]⟩,
        ⟨10996, false, false, [], [5]⟩,
        ⟨10995, false, false, [], [5]⟩,
        ⟨10995, false, false, [], [5]⟩,
        ⟨10998, false, false, [7357], []⟩,
        ⟨10988, false, false, [], [7355, 79513]⟩,
        ⟨7095, false, false, [], []⟩,
        ⟨7096, false, false, [], []⟩
      ]⟩,
    ⟨[82821, 13], [82821, 13], .contexts []⟩,
    ⟨[82821, 13], [8975, 81391], .contexts [
        ⟨17080, false, false, [], []⟩,
        ⟨17074, true, false, [], [13]⟩,
        ⟨179, false, false, [79179], []⟩,
        ⟨180, false, false, [79179], []⟩,
        ⟨7106, false, false, [], [5]⟩,
        ⟨7102, false, false, [], [5]⟩,
        ⟨7103, false, false, [], [5]⟩,
        ⟨7103, false, false, [], [5]⟩,
        ⟨14851, false, false, [], []⟩,
        ⟨14852, false, false, [], []⟩,
        ⟨14853, false, false, [], []⟩,
        ⟨14853, false, false, [], []⟩,
        ⟨14861, false, false, [], []⟩,
        ⟨14863, false, false, [], []⟩
      ]⟩,
    ⟨[81391, 13], [8973, 82821], .contexts [
        ⟨17081, true, false, [8974], [13]⟩,
        ⟨59, false, false, [8974, 82821], []⟩,
        ⟨11833, true, false, [], [82821]⟩
      ]⟩,
    ⟨[82821, 15], [82821, 15], .contexts []⟩,
    ⟨[82821, 15], [7357, 82811], .contexts [
        ⟨17083, false, false, [], []⟩,
        ⟨17074, true, false, [], [15]⟩,
        ⟨184, false, false, [79179], []⟩,
        ⟨185, false, false, [79179], []⟩,
        ⟨14996, false, false, [], [5]⟩,
        ⟨16962, false, false, [], [5]⟩,
        ⟨16963, false, false, [], [5]⟩,
        ⟨16963, false, false, [], [5]⟩,
        ⟨16964, false, false, [], []⟩,
        ⟨16965, false, false, [], []⟩,
        ⟨16966, false, false, [], []⟩,
        ⟨16967, false, false, [], []⟩,
        ⟨16969, false, false, [], []⟩,
        ⟨16971, false, false, [], []⟩
      ]⟩,
    ⟨[82811, 15], [7355, 82821], .contexts [
        ⟨17084, true, false, [7356], [15]⟩,
        ⟨1, false, false, [7356, 82821], []⟩,
        ⟨10990, true, false, [], [82821]⟩
      ]⟩,
    ⟨[82823], [82821, 7], .source 41476⟩,
    ⟨[82821, 7], [82823], .contexts [
        ⟨17086, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 267. -/
def y322TCIndexRaw267 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82823], [82823], .contexts []⟩,
    ⟨[82823], [82823], .contexts []⟩,
    ⟨[82821, 7], [82823], .contexts [
        ⟨17087, false, false, [], []⟩,
        ⟨17088, false, false, [], []⟩,
        ⟨17089, false, false, [], []⟩,
        ⟨17089, false, false, [], []⟩
      ]⟩,
    ⟨[82823, 1], [79193], .contexts [
        ⟨17090, true, false, [], [1]⟩,
        ⟨1027, false, false, [82821], []⟩,
        ⟨1028, false, false, [82821], []⟩,
        ⟨17075, false, false, [], [7]⟩,
        ⟨17076, false, false, [], [7]⟩,
        ⟨6305, false, false, [], [7]⟩,
        ⟨6306, false, false, [], [7]⟩,
        ⟨6306, false, false, [], [7]⟩,
        ⟨17030, false, false, [], []⟩,
        ⟨6291, false, false, [], []⟩,
        ⟨6292, false, false, [], []⟩,
        ⟨6292, false, false, [], []⟩,
        ⟨6790, false, false, [], []⟩,
        ⟨6791, false, false, [], []⟩
      ]⟩,
    ⟨[79193, 1], [82823], .contexts [
        ⟨17091, true, false, [], [1]⟩,
        ⟨8, false, false, [82823], []⟩,
        ⟨17089, false, false, [], []⟩
      ]⟩,
    ⟨[82821, 5], [79179], .contexts [
        ⟨17071, false, false, [], []⟩,
        ⟨6207, false, false, [], []⟩,
        ⟨6208, false, false, [], []⟩,
        ⟨6208, false, false, [], []⟩
      ]⟩,
    ⟨[15561], [10297, 11993], .source 7845⟩,
    ⟨[15561, 77303], [15561, 77303], .contexts []⟩,
    ⟨[15563], [15561, 11989], .source 7846⟩,
    ⟨[15565], [15563, 11985], .source 7847⟩,
    ⟨[82823, 5], [15565, 81405], .contexts [
        ⟨17090, true, false, [], [5]⟩,
        ⟨1043, false, false, [82821], []⟩,
        ⟨1046, false, false, [82821], []⟩,
        ⟨17093, false, false, [], [7, 5, 7]⟩,
        ⟨6206, false, false, [], [5, 7]⟩,
        ⟨11187, false, false, [], [5, 7]⟩,
        ⟨12483, false, false, [], [5, 7]⟩,
        ⟨12484, true, false, [], [77559, 5, 7]⟩,
        ⟨13367, false, false, [10297], [5, 7]⟩,
        ⟨17094, true, false, [], [77303, 5, 7]⟩,
        ⟨17095, false, false, [], [5, 7]⟩,
        ⟨17095, false, false, [], [5, 7]⟩,
        ⟨781, false, false, [15561], [7]⟩,
        ⟨13364, false, false, [15561], [7]⟩,
        ⟨17096, true, false, [], [77299, 7]⟩,
        ⟨13359, false, false, [15563], []⟩,
        ⟨17097, true, false, [], [81405]⟩,
        ⟨9301, false, false, [15565], []⟩,
        ⟨13, true, false, [], [15565, 81405]⟩
      ]⟩,
    ⟨[15567], [15564], .source 7848⟩,
    ⟨[81405, 5], [15567, 82823], .contexts [
        ⟨17098, true, false, [15564], [5]⟩,
        ⟨28, false, false, [15564, 82823], []⟩,
        ⟨17099, true, false, [], [82823]⟩
      ]⟩,
    ⟨[82821, 11], [79513], .contexts [
        ⟨17078, false, false, [], []⟩,
        ⟨17079, false, false, [], []⟩,
        ⟨6925, false, false, [], []⟩,
        ⟨6926, false, false, [], []⟩,
        ⟨6926, false, false, [], []⟩
      ]⟩,
    ⟨[82823, 11], [79511], .contexts [
        ⟨17090, true, false, [], [11]⟩,
        ⟨1051, false, false, [82821], []⟩,
        ⟨1052, false, false, [82821], []⟩,
        ⟨17101, false, false, [], [7]⟩,
        ⟨6924, false, false, [], []⟩,
        ⟨6907, false, false, [], []⟩,
        ⟨6908, false, false, [], []⟩,
        ⟨6908, false, false, [], []⟩,
        ⟨7078, false, false, [], []⟩,
        ⟨7079, false, false, [], []⟩
      ]⟩,
    ⟨[79511, 11], [82823], .contexts [
        ⟨17102, true, false, [], [11]⟩,
        ⟨53, false, false, [82823], []⟩,
        ⟨17089, false, false, [], []⟩
      ]⟩,
    ⟨[82821, 13], [8975, 81391], .contexts [
        ⟨17080, false, false, [], []⟩,
        ⟨17081, false, false, [], []⟩,
        ⟨14852, false, false, [], []⟩,
        ⟨14853, false, false, [], []⟩,
        ⟨14853, false, false, [], []⟩
      ]⟩,
    ⟨[8975, 81393], [8975, 81393], .contexts []⟩,
    ⟨[82823, 13], [8975, 81393], .contexts [
        ⟨17090, true, false, [], [13]⟩,
        ⟨1056, false, false, [82821], []⟩,
        ⟨1057, false, false, [82821], []⟩,
        ⟨17104, false, false, [], [7]⟩,
        ⟨9007, false, false, [8975], []⟩,
        ⟨17105, false, false, [], []⟩,
        ⟨14876, false, false, [8975], []⟩,
        ⟨14862, true, false, [], [81393]⟩
      ]⟩,
    ⟨[81393, 13], [8973, 82823], .contexts [
        ⟨17106, true, false, [8974], [13]⟩,
        ⟨59, false, false, [8974, 82823], []⟩,
        ⟨11833, true, false, [], [82823]⟩
      ]⟩,
    ⟨[82821, 15], [7357, 82811], .contexts [
        ⟨17084, false, false, [], []⟩
      ]⟩,
    ⟨[82821, 15], [7357, 82811], .contexts [
        ⟨17083, false, false, [], []⟩,
        ⟨17108, false, false, [], []⟩,
        ⟨16965, false, false, [], []⟩,
        ⟨16967, false, false, [], []⟩,
        ⟨16967, false, false, [], []⟩
      ]⟩,
    ⟨[82823, 15], [7357, 82813], .contexts [
        ⟨17090, true, false, [], [15]⟩,
        ⟨1063, false, false, [82821], []⟩,
        ⟨1064, false, false, [82821], []⟩,
        ⟨17109, false, false, [], [7]⟩,
        ⟨17001, false, false, [], []⟩,
        ⟨17002, false, false, [], []⟩,
        ⟨17003, false, false, [], []⟩,
        ⟨17004, false, false, [], []⟩,
        ⟨17006, false, false, [], []⟩,
        ⟨17007, false, false, [], []⟩
      ]⟩,
    ⟨[82825], [81405, 9], .source 41477⟩,
    ⟨[81405, 9], [82825], .contexts [
        ⟨17111, true, false, [], []⟩
      ]⟩,
    ⟨[82825], [82825], .contexts []⟩,
    ⟨[82825], [82825], .contexts []⟩,
    ⟨[81405, 9], [82825], .contexts [
        ⟨17112, false, false, [], []⟩,
        ⟨17113, false, false, [], []⟩,
        ⟨17114, false, false, [], []⟩,
        ⟨17114, false, false, [], []⟩
      ]⟩,
    ⟨[14713, 79191], [14713, 79191], .contexts []⟩,
    ⟨[14713, 79191], [14713, 79191], .contexts []⟩,
    ⟨[14713, 78839], [14713, 78839], .contexts []⟩,
    ⟨[82825, 1], [14713, 78839], .contexts [
        ⟨17115, true, false, [], [1]⟩,
        ⟨691, false, false, [81405], []⟩,
        ⟨694, false, false, [81405], []⟩,
        ⟨14547, false, false, [], [9, 1, 9]⟩,
        ⟨14550, false, false, [], [9, 1, 9]⟩,
        ⟨17116, false, false, [], [9, 1, 9]⟩,
        ⟨17117, false, false, [], [9, 1, 9]⟩,
        ⟨17117, false, false, [], [9, 1, 9]⟩,
        ⟨6285, false, false, [14713], [1, 9]⟩,
        ⟨5073, false, false, [14713], [9]⟩,
        ⟨5169, false, false, [14713], []⟩,
        ⟨17118, false, false, [], []⟩,
        ⟨5186, false, false, [14713], []⟩
      ]⟩,
    ⟨[82825, 1], [14713, 78839], .contexts [
        ⟨17119, false, false, [], []⟩,
        ⟨13, true, false, [], [14713, 78839]⟩
      ]⟩,
    ⟨[78839, 1], [14715, 82825], .contexts [
        ⟨17120, true, false, [14712], [1]⟩,
        ⟨8, false, false, [14712, 82825], []⟩,
        ⟨14551, true, false, [], [82825]⟩
      ]⟩,
    ⟨[81595], [8905, 81405], .contexts [
        ⟨11789, false, false, [8906], [81595]⟩,
        ⟨9299, true, false, [8906, 8904], []⟩,
        ⟨9298, true, false, [8906, 8904], []⟩,
        ⟨11786, false, false, [8906, 8904], []⟩,
        ⟨11787, true, false, [8906, 8904], [81405]⟩,
        ⟨11790, true, false, [], [81405]⟩
      ]⟩,
    ⟨[8905, 81405], [8905, 81405], .contexts []⟩,
    ⟨[81595], [8905, 81405], .contexts [
        ⟨17122, false, false, [], []⟩,
        ⟨17123, false, false, [], []⟩
      ]⟩,
    ⟨[8905, 82825], [8905, 82825], .contexts []⟩,
    ⟨[82825], [82825], .contexts []⟩,
    ⟨[82825, 3], [8905, 82825], .contexts [
        ⟨17115, true, false, [], [3]⟩,
        ⟨196, false, false, [81405], []⟩,
        ⟨197, false, false, [81405], []⟩,
        ⟨9302, false, false, [], [9]⟩,
        ⟨17124, false, false, [], [9]⟩,
        ⟨17123, false, false, [], [9]⟩,
        ⟨17123, false, false, [], [9]⟩,
        ⟨17112, false, false, [8905], []⟩,
        ⟨17125, false, false, [], []⟩,
        ⟨17126, false, false, [8905], []⟩,
        ⟨13, true, false, [], [8905, 82825]⟩
      ]⟩,
    ⟨[6417, 77387], [6417, 11953, 77299], .contexts [
        ⟨13344, false, false, [6417], []⟩
      ]⟩,
    ⟨[15569], [6417, 11953], .source 7849⟩,
    ⟨[15571], [3907, 15569], .source 7850⟩,
    ⟨[15573], [15571, 11951], .source 7851⟩,
    ⟨[82825, 7], [15573, 77389], .contexts [
        ⟨17115, true, false, [], [7]⟩,
        ⟨1084, false, false, [81405], []⟩,
        ⟨1085, false, false, [81405], []⟩,
        ⟨9044, false, false, [], [9]⟩,
        ⟨9045, false, false, [], [9]⟩,
        ⟨10677, false, false, [3907], [9]⟩,
        ⟨17128, false, false, [3907], [9]⟩,
        ⟨17129, true, false, [3907], [77299, 9]⟩,
        ⟨17130, true, false, [], [77299, 9]⟩,
        ⟨13345, false, false, [15571], []⟩,
        ⟨17131, true, false, [], [77389]⟩,
        ⟨13, true, false, [], [15573, 77389]⟩
      ]⟩,
    ⟨[15575], [15572], .source 7852⟩,
    ⟨[77389, 7], [15575, 82825], .contexts [
        ⟨17132, true, false, [15572], [7]⟩,
        ⟨38, false, false, [15572, 82825], []⟩,
        ⟨17133, true, false, [], [82825]⟩
      ]⟩,
    ⟨[14733, 79509], [14733, 79509], .contexts []⟩,
    ⟨[14733, 79509], [14733, 79509], .contexts []⟩,
    ⟨[15577], [14733, 2009], .source 7853⟩,
    ⟨[15579], [15577, 14731], .source 7854⟩,
    ⟨[15579, 82825], [15579, 82825], .contexts []⟩,
    ⟨[82825, 11], [15579, 82825], .contexts [
        ⟨17115, true, false, [], [11]⟩,
        ⟨2344, false, false, [81405], []⟩,
        ⟨2346, false, false, [81405], []⟩,
        ⟨14571, false, false, [], [9, 11, 9]⟩,
        ⟨17135, false, false, [], [9, 11, 9]⟩,
        ⟨17136, false, false, [], [9, 11, 9]⟩,
        ⟨17136, false, false, [], [9, 11, 9]⟩,
        ⟨6903, false, false, [14733], [11, 9]⟩,
        ⟨17137, true, false, [], [79509, 11, 9]⟩,
        ⟨14569, false, false, [15577], [9]⟩,
        ⟨17138, true, false, [], [81405, 9]⟩,
        ⟨17112, false, false, [15579], []⟩,
        ⟨17139, false, false, [], []⟩,
        ⟨17126, false, false, [15579], []⟩
      ]⟩,
    ⟨[81349], [8409, 80805], .contexts [
        ⟨11518, false, false, [], []⟩
      ]⟩,
    ⟨[], [8409, 8411], .contexts [
        ⟨11506, true, false, [8409], []⟩
      ]⟩,
    ⟨[82825, 13], [81401], .contexts [
        ⟨17115, true, false, [], [13]⟩,
        ⟨201, false, false, [81405], []⟩,
        ⟨202, false, false, [81405], []⟩,
        ⟨9040, false, false, [], [9]⟩,
        ⟨17141, false, false, [], [9]⟩,
        ⟨11512, false, false, [], [9]⟩,
        ⟨11512, false, false, [], [9]⟩,
        ⟨11515, false, false, [8409], []⟩,
        ⟨17142, true, false, [], [81401]⟩,
        ⟨9027, false, false, [], []⟩,
        ⟨672, true, false, [], [81401]⟩
      ]⟩,
    ⟨[81401, 13], [82825], .contexts [
        ⟨17143, true, false, [], [13]⟩,
        ⟨59, false, false, [82825], []⟩,
        ⟨17114, false, false, [], []⟩
      ]⟩,
    ⟨[15431, 82775], [15431, 82775], .contexts []⟩,
    ⟨[15431, 82775], [15431, 82775], .contexts []⟩,
    ⟨[15581], [15431, 15343], .source 7855⟩,
    ⟨[82825, 15], [15581, 82701], .contexts [
        ⟨17115, true, false, [], [15]⟩,
        ⟨205, false, false, [81405], []⟩,
        ⟨206, false, false, [81405], []⟩,
        ⟨16486, false, false, [], [9]⟩,
        ⟨17145, false, false, [], [9]⟩,
        ⟨17146, false, false, [], [9]⟩,
        ⟨17146, false, false, [], [9]⟩,
        ⟨16478, false, false, [15431], []⟩,
        ⟨17147, true, false, [], [82701]⟩,
        ⟨15564, false, false, [15581], []⟩,
        ⟨13, true, false, [], [15581, 82701]⟩
      ]⟩,
    ⟨[15583], [15580], .source 7856⟩,
    ⟨[82827], [79017, 13], .source 41478⟩,
    ⟨[79017, 13], [82827], .contexts [
        ⟨17150, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 268. -/
def y322TCIndexRaw268 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82827, 13], [79017], .contexts [
        ⟨17151, true, false, [], [13]⟩,
        ⟨59, false, false, [79017], []⟩,
        ⟨5573, false, false, [], []⟩
      ]⟩,
    ⟨[82827], [82827], .contexts []⟩,
    ⟨[82827], [82827], .contexts []⟩,
    ⟨[79017, 13], [82827], .contexts [
        ⟨17151, false, false, [], []⟩,
        ⟨17153, false, false, [], []⟩,
        ⟨17154, false, false, [], []⟩,
        ⟨17154, false, false, [], []⟩
      ]⟩,
    ⟨[78999, 13], [1075, 78999], .contexts [
        ⟨5470, false, false, [], []⟩
      ]⟩,
    ⟨[1075, 82827], [1075, 82827], .contexts []⟩,
    ⟨[1075, 82827], [1075, 82827], .contexts []⟩,
    ⟨[82827, 1], [82827, 1], .contexts []⟩,
    ⟨[82827], [82827], .contexts []⟩,
    ⟨[82827, 1], [1075, 82827], .contexts [
        ⟨17159, false, false, [], []⟩,
        ⟨17155, true, false, [], [1]⟩,
        ⟨246, false, false, [79017], []⟩,
        ⟨249, false, false, [79017], []⟩,
        ⟨5576, false, false, [], [13, 1, 13]⟩,
        ⟨5579, false, false, [], [13, 1, 13]⟩,
        ⟨5456, false, false, [], [13, 1, 13]⟩,
        ⟨5457, false, false, [], [13, 1, 13]⟩,
        ⟨5457, false, false, [], [13, 1, 13]⟩,
        ⟨17156, false, false, [], [1, 13]⟩,
        ⟨5468, false, false, [], [1, 13]⟩,
        ⟨5469, false, false, [], [1, 13]⟩,
        ⟨5469, false, false, [], [1, 13]⟩,
        ⟨5580, false, false, [1075], [13]⟩,
        ⟨17151, false, false, [1075], []⟩,
        ⟨17157, false, false, [], []⟩,
        ⟨17158, false, false, [], []⟩,
        ⟨17160, false, false, [1075], []⟩
      ]⟩,
    ⟨[82827, 1], [1075, 82827], .contexts [
        ⟨17161, false, false, [], []⟩,
        ⟨4778, true, false, [], [82827]⟩
      ]⟩,
    ⟨[15585], [8181, 5761], .source 7857⟩,
    ⟨[82827, 7], [15585, 78337], .contexts [
        ⟨17155, true, false, [], [7]⟩,
        ⟨73, false, false, [79017], []⟩,
        ⟨74, false, false, [79017], []⟩,
        ⟨5581, false, false, [], [13]⟩,
        ⟨5584, false, false, [], [13]⟩,
        ⟨11371, false, false, [], [13]⟩,
        ⟨11370, false, false, [], [13]⟩,
        ⟨11370, false, false, [], [13]⟩,
        ⟨10453, false, false, [8181], []⟩,
        ⟨17163, true, false, [], [78337]⟩,
        ⟨10406, false, false, [15585], []⟩,
        ⟨13, true, false, [], [15585, 78337]⟩
      ]⟩,
    ⟨[15587], [15584], .source 7858⟩,
    ⟨[15439, 82791], [15439, 82791], .contexts []⟩,
    ⟨[82827, 9], [15439, 82791], .contexts [
        ⟨17155, true, false, [], [9]⟩,
        ⟨77, false, false, [79017], []⟩,
        ⟨78, false, false, [79017], []⟩,
        ⟨16736, false, false, [], [13]⟩,
        ⟨16661, false, false, [15439], []⟩,
        ⟨17166, false, false, [], []⟩,
        ⟨16677, false, false, [15439], []⟩,
        ⟨16740, true, false, [], [82791]⟩
      ]⟩,
    ⟨[82791, 9], [15437, 82827], .contexts [
        ⟨17167, true, false, [15438], [9]⟩,
        ⟨46, false, false, [15438, 82827], []⟩,
        ⟨16742, true, false, [], [82827]⟩
      ]⟩,
    ⟨[82827, 11], [79019], .contexts [
        ⟨17155, true, false, [], [11]⟩,
        ⟨82, false, false, [79017], []⟩,
        ⟨83, false, false, [79017], []⟩,
        ⟨16744, false, false, [], [13]⟩,
        ⟨5587, false, false, [], []⟩,
        ⟨5588, false, false, [], []⟩,
        ⟨5589, false, false, [], []⟩,
        ⟨5589, false, false, [], []⟩,
        ⟨6338, false, false, [], []⟩,
        ⟨6339, false, false, [], []⟩
      ]⟩,
    ⟨[79019, 11], [82827], .contexts [
        ⟨17169, true, false, [], [11]⟩,
        ⟨53, false, false, [82827], []⟩,
        ⟨17154, false, false, [], []⟩
      ]⟩,
    ⟨[2575, 82827], [2575, 82827], .contexts []⟩,
    ⟨[2575, 82827], [2575, 82827], .contexts []⟩,
    ⟨[82827, 15], [82827, 15], .contexts []⟩,
    ⟨[82827, 15], [2575, 82827], .contexts [
        ⟨17173, false, false, [], []⟩,
        ⟨17155, true, false, [], [15]⟩,
        ⟨88, false, false, [79017], []⟩,
        ⟨91, false, false, [79017], []⟩,
        ⟨15287, false, false, [], [13, 15, 13]⟩,
        ⟨15274, false, false, [], [13, 15, 13]⟩,
        ⟨15275, false, false, [], [13, 15, 13]⟩,
        ⟨15275, false, false, [], [13, 15, 13]⟩,
        ⟨15284, false, false, [], [15, 13]⟩,
        ⟨15281, false, false, [], [15, 13]⟩,
        ⟨15282, false, false, [], [15, 13]⟩,
        ⟨15282, false, false, [], [15, 13]⟩,
        ⟨15286, false, false, [2575], [13]⟩,
        ⟨17151, false, false, [2575], []⟩,
        ⟨17171, false, false, [], []⟩,
        ⟨17172, false, false, [], []⟩,
        ⟨17160, false, false, [2575], []⟩
      ]⟩,
    ⟨[82827, 15], [2575, 82827], .contexts [
        ⟨17174, false, false, [], []⟩,
        ⟨5618, true, false, [], [82827]⟩
      ]⟩,
    ⟨[82829], [78841, 5], .source 74606⟩,
    ⟨[78841, 5], [82829], .contexts [
        ⟨17176, true, false, [], []⟩
      ]⟩,
    ⟨[82829, 5], [78841], .contexts [
        ⟨17177, true, false, [], [5]⟩,
        ⟨28, false, false, [78841], []⟩,
        ⟨5195, false, false, [], []⟩
      ]⟩,
    ⟨[78841, 5], [82829], .source 74607⟩,
    ⟨[82829], [82829], .source 74608⟩,
    ⟨[82829], [82829], .source 74609⟩,
    ⟨[78841, 5], [82829], .contexts [
        ⟨17179, false, false, [], []⟩,
        ⟨17180, false, false, [], []⟩,
        ⟨17181, false, false, [], []⟩,
        ⟨17181, false, false, [], []⟩
      ]⟩,
    ⟨[82829, 1], [15589, 82799], .source 74613⟩,
    ⟨[82829, 1], [82829, 1], .source 74614⟩,
    ⟨[82799], [82799], .contexts []⟩,
    ⟨[15589], [15589], .source 74615⟩,
    ⟨[82829, 1], [15589, 82799], .contexts [
        ⟨17184, false, false, [], []⟩,
        ⟨17183, false, false, [], []⟩,
        ⟨17185, false, false, [15589], []⟩,
        ⟨17186, true, false, [], [82799]⟩
      ]⟩,
    ⟨[15591], [15588], .source 74616⟩,
    ⟨[82799, 1], [15591, 82829], .contexts [
        ⟨17187, true, false, [15588], [1]⟩,
        ⟨8, false, false, [15588, 82829], []⟩,
        ⟨17188, true, false, [], [82829]⟩
      ]⟩,
    ⟨[2215, 82829], [2215, 82829], .contexts []⟩,
    ⟨[2215, 82829], [2215, 82829], .contexts []⟩,
    ⟨[82829, 9], [82829, 9], .contexts []⟩,
    ⟨[82829], [82829], .contexts []⟩,
    ⟨[82829, 9], [2215, 82829], .contexts [
        ⟨17192, false, false, [], []⟩,
        ⟨17182, true, false, [], [9]⟩,
        ⟨1265, false, false, [78841], []⟩,
        ⟨1266, false, false, [78841], []⟩,
        ⟨5204, false, false, [], [5]⟩,
        ⟨5206, false, false, [], [5]⟩,
        ⟨5202, false, false, [], [5]⟩,
        ⟨5203, false, false, [], [5]⟩,
        ⟨5203, false, false, [], [5]⟩,
        ⟨17177, false, false, [2215], []⟩,
        ⟨17190, false, false, [], []⟩,
        ⟨17191, false, false, [], []⟩,
        ⟨17193, false, false, [2215], []⟩,
        ⟨4800, true, false, [], [82829]⟩
      ]⟩,
    ⟨[82829, 11], [82829, 11], .contexts []⟩,
    ⟨[82829, 11], [78833], .contexts [
        ⟨17195, false, false, [], []⟩,
        ⟨17182, true, false, [], [11]⟩,
        ⟨174, false, false, [78841], []⟩,
        ⟨175, false, false, [78841], []⟩,
        ⟨5192, false, false, [], [5]⟩,
        ⟨4902, false, false, [], [5]⟩,
        ⟨4903, false, false, [], [5]⟩,
        ⟨4903, false, false, [], [5]⟩,
        ⟨5536, false, false, [], []⟩,
        ⟨5133, false, false, [], []⟩,
        ⟨5134, false, false, [], []⟩,
        ⟨5134, false, false, [], []⟩,
        ⟨5538, false, false, [], []⟩,
        ⟨5539, false, false, [], []⟩
      ]⟩,
    ⟨[78833, 11], [82829], .contexts [
        ⟨17196, true, false, [], [11]⟩,
        ⟨53, false, false, [82829], []⟩,
        ⟨17181, false, false, [], []⟩
      ]⟩,
    ⟨[1077, 82829], [1077, 82829], .contexts []⟩,
    ⟨[1077, 82829], [1077, 82829], .contexts []⟩,
    ⟨[82829, 13], [82829, 13], .contexts []⟩,
    ⟨[82829, 13], [1077, 82829], .contexts [
        ⟨17200, false, false, [], []⟩,
        ⟨17182, true, false, [], [13]⟩,
        ⟨179, false, false, [78841], []⟩,
        ⟨180, false, false, [78841], []⟩,
        ⟨5209, false, false, [], [5]⟩,
        ⟨5210, false, false, [], [5]⟩,
        ⟨5207, false, false, [], [5]⟩,
        ⟨5208, false, false, [], [5]⟩,
        ⟨5208, false, false, [], [5]⟩,
        ⟨17177, false, false, [1077], []⟩,
        ⟨17198, false, false, [], []⟩,
        ⟨17199, false, false, [], []⟩,
        ⟨17193, false, false, [1077], []⟩,
        ⟨4913, true, false, [], [82829]⟩
      ]⟩,
    ⟨[82831], [82829, 7], .source 74617⟩,
    ⟨[82829, 7], [82831], .contexts [
        ⟨17202, true, false, [], []⟩
      ]⟩,
    ⟨[82829, 7], [82831], .source 74618⟩,
    ⟨[82831], [82831], .source 74619⟩,
    ⟨[82831], [82831], .source 74620⟩,
    ⟨[82829, 7], [82831], .contexts [
        ⟨17204, false, false, [], []⟩,
        ⟨17205, false, false, [], []⟩,
        ⟨17206, false, false, [], []⟩,
        ⟨17206, false, false, [], []⟩
      ]⟩,
    ⟨[82829, 1], [15589, 82799], .contexts [
        ⟨17187, false, false, [], []⟩
      ]⟩,
    ⟨[15589, 82799], [15589, 82799], .contexts []⟩,
    ⟨[15589, 82799], [15589, 82799], .source 74621⟩,
    ⟨[15589, 82797], [15589, 82797], .contexts []⟩,
    ⟨[82797], [82797], .contexts []⟩,
    ⟨[82831, 1], [15589, 82797], .contexts [
        ⟨17207, true, false, [], [1]⟩,
        ⟨1027, false, false, [82829], []⟩,
        ⟨1028, false, false, [82829], []⟩,
        ⟨17184, false, false, [], [7]⟩,
        ⟨17208, false, false, [], [7]⟩,
        ⟨17209, false, false, [], [7]⟩,
        ⟨17210, false, false, [], [7]⟩,
        ⟨17210, false, false, [], [7]⟩,
        ⟨16749, false, false, [15589], []⟩,
        ⟨17211, false, false, [], []⟩,
        ⟨17212, false, false, [15589], []⟩,
        ⟨17186, true, false, [], [82797]⟩
      ]⟩,
    ⟨[82797, 1], [15591, 82831], .source 74622⟩,
    ⟨[15593], [5935, 9087], .source 7861⟩]

/-- Exact literal claimed equations and contextual derivations, block 269. -/
def y322TCIndexRaw269 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15595], [9093, 15593], .source 7862⟩,
    ⟨[15597], [15595, 9085], .source 7863⟩,
    ⟨[82831, 5], [15597, 78999], .contexts [
        ⟨17207, true, false, [], [5]⟩,
        ⟨1043, false, false, [82829], []⟩,
        ⟨1046, false, false, [82829], []⟩,
        ⟨17178, false, false, [], [7, 5, 7]⟩,
        ⟨5194, false, false, [], [7, 5, 7]⟩,
        ⟨5195, false, false, [], [7, 5, 7]⟩,
        ⟨5195, false, false, [], [7, 5, 7]⟩,
        ⟨5199, false, false, [], [5, 7]⟩,
        ⟨11927, false, false, [], [5, 7]⟩,
        ⟨11928, true, false, [], [77379, 5, 7]⟩,
        ⟨10515, false, false, [9093], [7]⟩,
        ⟨11923, false, false, [9093, 5935], [7]⟩,
        ⟨17215, true, false, [9093], [77311, 7]⟩,
        ⟨17216, true, false, [], [77311, 7]⟩,
        ⟨11925, false, false, [15595], []⟩,
        ⟨17217, true, false, [], [78999]⟩,
        ⟨5460, false, false, [15597], []⟩
      ]⟩,
    ⟨[82831, 5], [15597, 78999], .contexts [
        ⟨17218, false, false, [], []⟩,
        ⟨13, true, false, [], [15597, 78999]⟩
      ]⟩,
    ⟨[15599], [15596], .source 7864⟩,
    ⟨[2215, 82831], [2215, 82831], .contexts []⟩,
    ⟨[82831], [82831], .contexts []⟩,
    ⟨[82831, 9], [2215, 82831], .contexts [
        ⟨17207, true, false, [], [9]⟩,
        ⟨1534, false, false, [82829], []⟩,
        ⟨1535, false, false, [82829], []⟩,
        ⟨17192, false, false, [], [7]⟩,
        ⟨17194, false, false, [], [7]⟩,
        ⟨17190, false, false, [], [7]⟩,
        ⟨17191, false, false, [], [7]⟩,
        ⟨17191, false, false, [], [7]⟩,
        ⟨17203, false, false, [2215], []⟩,
        ⟨17221, false, false, [], []⟩,
        ⟨17222, false, false, [2215], []⟩,
        ⟨4800, true, false, [], [82831]⟩
      ]⟩,
    ⟨[82831, 11], [78831], .contexts [
        ⟨17207, true, false, [], [11]⟩,
        ⟨1051, false, false, [82829], []⟩,
        ⟨1052, false, false, [82829], []⟩,
        ⟨17195, false, false, [], [7]⟩,
        ⟨17196, false, false, [], [7]⟩,
        ⟨5133, false, false, [], [7]⟩,
        ⟨5134, false, false, [], [7]⟩,
        ⟨5134, false, false, [], [7]⟩,
        ⟨5550, false, false, [], []⟩,
        ⟨5120, false, false, [], []⟩,
        ⟨5121, false, false, [], []⟩,
        ⟨5121, false, false, [], []⟩,
        ⟨5551, false, false, [], []⟩,
        ⟨5552, false, false, [], []⟩
      ]⟩,
    ⟨[78831, 11], [82831], .contexts [
        ⟨17224, true, false, [], [11]⟩,
        ⟨53, false, false, [82831], []⟩,
        ⟨17206, false, false, [], []⟩
      ]⟩,
    ⟨[1077, 82831], [1077, 82831], .contexts []⟩,
    ⟨[82831, 13], [1077, 82831], .contexts [
        ⟨17207, true, false, [], [13]⟩,
        ⟨1056, false, false, [82829], []⟩,
        ⟨1057, false, false, [82829], []⟩,
        ⟨17200, false, false, [], [7]⟩,
        ⟨17201, false, false, [], [7]⟩,
        ⟨17198, false, false, [], [7]⟩,
        ⟨17199, false, false, [], [7]⟩,
        ⟨17199, false, false, [], [7]⟩,
        ⟨17203, false, false, [1077], []⟩,
        ⟨17226, false, false, [], []⟩,
        ⟨17222, false, false, [1077], []⟩,
        ⟨4913, true, false, [], [82831]⟩
      ]⟩,
    ⟨[82805, 5], [82833], .source 74624⟩,
    ⟨[82833, 5], [82805], .contexts [
        ⟨17228, true, false, [], [5]⟩,
        ⟨28, false, false, [82805], []⟩,
        ⟨16827, false, false, [], []⟩
      ]⟩,
    ⟨[82833], [82833], .contexts []⟩,
    ⟨[82833], [82833], .source 74625⟩,
    ⟨[82805, 5], [82833], .contexts [
        ⟨17228, false, false, [], []⟩,
        ⟨17230, false, false, [], []⟩,
        ⟨17231, false, false, [], []⟩,
        ⟨17231, false, false, [], []⟩
      ]⟩,
    ⟨[15507, 82833], [15507, 82833], .contexts []⟩,
    ⟨[15507, 82833], [15507, 82833], .contexts []⟩,
    ⟨[82833, 9], [82833, 9], .contexts []⟩,
    ⟨[82833], [82833], .contexts []⟩,
    ⟨[82833, 9], [15507, 82833], .contexts [
        ⟨17235, false, false, [], []⟩,
        ⟨17232, true, false, [], [9]⟩,
        ⟨1265, false, false, [82805], []⟩,
        ⟨1266, false, false, [82805], []⟩,
        ⟨16842, false, false, [], [5]⟩,
        ⟨16846, false, false, [], [5]⟩,
        ⟨16840, false, false, [], [5]⟩,
        ⟨16841, false, false, [], [5]⟩,
        ⟨16841, false, false, [], [5]⟩,
        ⟨17228, false, false, [15507], []⟩,
        ⟨17233, false, false, [], []⟩,
        ⟨17234, false, false, [], []⟩,
        ⟨17236, false, false, [15507], []⟩,
        ⟨16845, true, false, [], [82833]⟩
      ]⟩,
    ⟨[82833, 11], [82833, 11], .contexts []⟩,
    ⟨[82833, 11], [82679], .contexts [
        ⟨17238, false, false, [], []⟩,
        ⟨17232, true, false, [], [11]⟩,
        ⟨174, false, false, [82805], []⟩,
        ⟨175, false, false, [82805], []⟩,
        ⟨16825, false, false, [], [5]⟩,
        ⟨5213, false, false, [], [5]⟩,
        ⟨5214, false, false, [], [5]⟩,
        ⟨5214, false, false, [], [5]⟩,
        ⟨15291, false, false, [], []⟩,
        ⟨15292, false, false, [], []⟩,
        ⟨15293, false, false, [], []⟩,
        ⟨15293, false, false, [], []⟩,
        ⟨15475, false, false, [], []⟩,
        ⟨672, true, false, [], [82679]⟩
      ]⟩,
    ⟨[82679, 11], [82833], .contexts [
        ⟨17239, true, false, [], [11]⟩,
        ⟨53, false, false, [82833], []⟩,
        ⟨17231, false, false, [], []⟩
      ]⟩,
    ⟨[82805, 15], [78841], .source 74626⟩,
    ⟨[82833, 15], [82833, 15], .source 74627⟩,
    ⟨[82829], [82829], .contexts [
        ⟨17193, false, false, [], []⟩
      ]⟩,
    ⟨[82829], [82829], .contexts [
        ⟨672, true, false, [], [82829]⟩
      ]⟩,
    ⟨[82833, 15], [82829], .contexts [
        ⟨17242, false, false, [], []⟩,
        ⟨17232, true, false, [], [15]⟩,
        ⟨184, false, false, [82805], []⟩,
        ⟨185, false, false, [82805], []⟩,
        ⟨17241, false, false, [], [5]⟩,
        ⟨5195, false, false, [], [5]⟩,
        ⟨17179, false, false, [], []⟩,
        ⟨17180, false, false, [], []⟩,
        ⟨17181, false, false, [], []⟩,
        ⟨17181, false, false, [], []⟩,
        ⟨17243, false, false, [], []⟩,
        ⟨17244, false, false, [], []⟩
      ]⟩,
    ⟨[82829, 15], [82833], .contexts [
        ⟨17245, true, false, [], [15]⟩,
        ⟨1, false, false, [82833], []⟩,
        ⟨17231, false, false, [], []⟩
      ]⟩,
    ⟨[82835], [82833, 7], .source 74628⟩,
    ⟨[82833, 7], [82835], .contexts [
        ⟨17247, true, false, [], []⟩
      ]⟩,
    ⟨[82835, 7], [82833], .contexts [
        ⟨17248, true, false, [], [7]⟩,
        ⟨38, false, false, [82833], []⟩,
        ⟨17231, false, false, [], []⟩
      ]⟩,
    ⟨[82835], [82835], .contexts []⟩,
    ⟨[82835], [82835], .source 74629⟩,
    ⟨[82833, 7], [82835], .source 74630⟩,
    ⟨[82833, 5, 7, 5, 7], [15605, 82685], .source 74635⟩,
    ⟨[82835, 5], [82835, 5], .contexts []⟩,
    ⟨[15605], [15605], .contexts [
        ⟨13, false, false, [], [15605]⟩
      ]⟩,
    ⟨[82835, 5], [15605, 82685], .contexts [
        ⟨17254, false, false, [], []⟩,
        ⟨17252, true, false, [], [5]⟩,
        ⟨1043, false, false, [82833], []⟩,
        ⟨1046, false, false, [82833], []⟩,
        ⟨17253, false, false, [], []⟩,
        ⟨15376, false, false, [15605], []⟩,
        ⟨17255, true, false, [], [82685]⟩
      ]⟩,
    ⟨[15607], [15604], .source 74636⟩,
    ⟨[82685, 5], [15607, 82835], .contexts [
        ⟨17256, true, false, [15604], [5]⟩,
        ⟨28, false, false, [15604, 82835], []⟩,
        ⟨17257, true, false, [], [82835]⟩
      ]⟩,
    ⟨[15507, 82835], [15507, 82835], .contexts []⟩,
    ⟨[15507, 82835], [15507, 82835], .contexts []⟩,
    ⟨[82835, 9], [82835, 9], .contexts []⟩,
    ⟨[82835], [82835], .contexts []⟩,
    ⟨[82835, 9], [15507, 82835], .contexts [
        ⟨17261, false, false, [], []⟩,
        ⟨17252, true, false, [], [9]⟩,
        ⟨1534, false, false, [82833], []⟩,
        ⟨1535, false, false, [82833], []⟩,
        ⟨17235, false, false, [], [7]⟩,
        ⟨17237, false, false, [], [7]⟩,
        ⟨17233, false, false, [], [7]⟩,
        ⟨17234, false, false, [], [7]⟩,
        ⟨17234, false, false, [], [7]⟩,
        ⟨17248, false, false, [15507], []⟩,
        ⟨17259, false, false, [], []⟩,
        ⟨17260, false, false, [], []⟩,
        ⟨17262, false, false, [15507], []⟩,
        ⟨16845, true, false, [], [82835]⟩
      ]⟩,
    ⟨[82835, 11], [82835, 11], .contexts []⟩,
    ⟨[82835, 11], [82681], .contexts [
        ⟨17264, false, false, [], []⟩,
        ⟨17252, true, false, [], [11]⟩,
        ⟨1051, false, false, [82833], []⟩,
        ⟨1052, false, false, [82833], []⟩,
        ⟨17238, false, false, [], [7]⟩,
        ⟨17239, false, false, [], [7]⟩,
        ⟨15292, false, false, [], [7]⟩,
        ⟨15293, false, false, [], [7]⟩,
        ⟨15293, false, false, [], [7]⟩,
        ⟨15311, false, false, [], []⟩,
        ⟨15312, false, false, [], []⟩,
        ⟨15313, false, false, [], []⟩,
        ⟨15313, false, false, [], []⟩,
        ⟨15496, false, false, [], []⟩,
        ⟨672, true, false, [], [82681]⟩
      ]⟩,
    ⟨[82681, 11], [82835], .contexts [
        ⟨17265, true, false, [], [11]⟩,
        ⟨53, false, false, [82835], []⟩,
        ⟨17251, false, false, [], []⟩
      ]⟩,
    ⟨[82833, 15, 7], [82831], .source 74637⟩,
    ⟨[82835, 15], [82835, 15], .contexts []⟩,
    ⟨[82831], [82831], .contexts [
        ⟨17222, false, false, [], []⟩
      ]⟩,
    ⟨[82831], [82831], .contexts [
        ⟨672, true, false, [], [82831]⟩
      ]⟩,
    ⟨[82835, 15], [82831], .contexts [
        ⟨17268, false, false, [], []⟩,
        ⟨17252, true, false, [], [15]⟩,
        ⟨1063, false, false, [82833], []⟩,
        ⟨1064, false, false, [82833], []⟩,
        ⟨17267, false, false, [], []⟩,
        ⟨17269, false, false, [], []⟩,
        ⟨17270, false, false, [], []⟩
      ]⟩,
    ⟨[82831, 15], [82835], .contexts [
        ⟨17271, true, false, [], [15]⟩,
        ⟨1, false, false, [82835], []⟩,
        ⟨17251, false, false, [], []⟩
      ]⟩,
    ⟨[82685, 13], [82837], .source 74639⟩,
    ⟨[82837, 13], [82685], .contexts [
        ⟨17273, true, false, [], [13]⟩,
        ⟨59, false, false, [82685], []⟩,
        ⟨15369, false, false, [], []⟩
      ]⟩,
    ⟨[82837], [82837], .contexts []⟩,
    ⟨[82837], [82837], .source 74640⟩,
    ⟨[82685, 13], [82837], .source 74641⟩,
    ⟨[82685, 1, 13, 1], [2575, 82685], .source 74642⟩,
    ⟨[2575, 82837], [2575, 82837], .source 74643⟩]

/-- Exact literal claimed equations and contextual derivations, block 270. -/
def y322TCIndexRaw270 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[2575, 82837], [2575, 82837], .source 74644⟩,
    ⟨[82837, 1], [82837, 1], .source 74645⟩,
    ⟨[82837], [82837], .contexts []⟩,
    ⟨[82837, 1], [2575, 82837], .contexts [
        ⟨17281, false, false, [], []⟩,
        ⟨17277, true, false, [], [1]⟩,
        ⟨246, false, false, [82685], []⟩,
        ⟨249, false, false, [82685], []⟩,
        ⟨17278, false, false, [], [13]⟩,
        ⟨17273, false, false, [2575], []⟩,
        ⟨17279, false, false, [], []⟩,
        ⟨17280, false, false, [], []⟩,
        ⟨17282, false, false, [2575], []⟩,
        ⟨5618, true, false, [], [82837]⟩
      ]⟩,
    ⟨[315, 82837], [315, 82837], .contexts []⟩,
    ⟨[82837, 3], [315, 82837], .contexts [
        ⟨17277, true, false, [], [3]⟩,
        ⟨63, false, false, [82685], []⟩,
        ⟨65, false, false, [82685], []⟩,
        ⟨15375, false, false, [], [13]⟩,
        ⟨15377, false, false, [], [13]⟩,
        ⟨15373, false, false, [], [13]⟩,
        ⟨15374, false, false, [], [13]⟩,
        ⟨15374, false, false, [], [13]⟩,
        ⟨17273, false, false, [315], []⟩,
        ⟨17284, false, false, [], []⟩,
        ⟨17282, false, false, [315], []⟩,
        ⟨1689, true, false, [], [82837]⟩
      ]⟩,
    ⟨[15291, 77315], [15291, 77315], .contexts []⟩,
    ⟨[15291, 77315], [15291, 77315], .contexts []⟩,
    ⟨[15609], [15291, 9079], .source 7869⟩,
    ⟨[82837, 7], [15609, 78417], .contexts [
        ⟨17277, true, false, [], [7]⟩,
        ⟨73, false, false, [82685], []⟩,
        ⟨74, false, false, [82685], []⟩,
        ⟨15379, false, false, [], [13]⟩,
        ⟨15380, false, false, [], [13]⟩,
        ⟨17286, false, false, [], [13]⟩,
        ⟨17287, false, false, [], [13]⟩,
        ⟨17287, false, false, [], [13]⟩,
        ⟨11914, false, false, [15291], []⟩,
        ⟨17288, true, false, [], [78417]⟩,
        ⟨4387, false, false, [15609], []⟩,
        ⟨13, true, false, [], [15609, 78417]⟩
      ]⟩,
    ⟨[15611], [15608], .source 7870⟩,
    ⟨[15289, 82837], [15289, 82837], .contexts []⟩,
    ⟨[15289, 82837], [15289, 82837], .contexts []⟩,
    ⟨[82837, 9], [82837, 9], .contexts []⟩,
    ⟨[82837, 9], [15289, 82837], .contexts [
        ⟨17293, false, false, [], []⟩,
        ⟨17277, true, false, [], [9]⟩,
        ⟨77, false, false, [82685], []⟩,
        ⟨78, false, false, [82685], []⟩,
        ⟨15387, false, false, [], [13]⟩,
        ⟨15389, false, false, [], [13]⟩,
        ⟨15385, false, false, [], [13]⟩,
        ⟨15386, false, false, [], [13]⟩,
        ⟨15386, false, false, [], [13]⟩,
        ⟨17273, false, false, [15289], []⟩,
        ⟨17291, false, false, [], []⟩,
        ⟨17292, false, false, [], []⟩,
        ⟨17282, false, false, [15289], []⟩,
        ⟨15388, true, false, [], [82837]⟩
      ]⟩,
    ⟨[82837, 11], [82837, 11], .source 74646⟩,
    ⟨[82837, 11], [82687], .contexts [
        ⟨17295, false, false, [], []⟩,
        ⟨17277, true, false, [], [11]⟩,
        ⟨82, false, false, [82685], []⟩,
        ⟨83, false, false, [82685], []⟩,
        ⟨15367, false, false, [], [13]⟩,
        ⟨5475, false, false, [], [13]⟩,
        ⟨5476, false, false, [], [13]⟩,
        ⟨5476, false, false, [], [13]⟩,
        ⟨15396, false, false, [], []⟩,
        ⟨15397, false, false, [], []⟩,
        ⟨15398, false, false, [], []⟩,
        ⟨15398, false, false, [], []⟩,
        ⟨15513, false, false, [], []⟩,
        ⟨15514, false, false, [], []⟩
      ]⟩,
    ⟨[82687, 11], [82837], .contexts [
        ⟨17296, true, false, [], [11]⟩,
        ⟨53, false, false, [82837], []⟩,
        ⟨17276, false, false, [], []⟩
      ]⟩,
    ⟨[1075, 82837], [1075, 82837], .contexts []⟩,
    ⟨[1075, 82837], [1075, 82837], .contexts []⟩,
    ⟨[82837, 15], [82837, 15], .contexts []⟩,
    ⟨[82837, 15], [1075, 82837], .contexts [
        ⟨17300, false, false, [], []⟩,
        ⟨17277, true, false, [], [15]⟩,
        ⟨88, false, false, [82685], []⟩,
        ⟨91, false, false, [82685], []⟩,
        ⟨15390, false, false, [], [13, 15, 13]⟩,
        ⟨15391, false, false, [], [13, 15, 13]⟩,
        ⟨5456, false, false, [], [13, 15, 13]⟩,
        ⟨5457, false, false, [], [13, 15, 13]⟩,
        ⟨5457, false, false, [], [13, 15, 13]⟩,
        ⟨17156, false, false, [], [15, 13]⟩,
        ⟨5468, false, false, [], [15, 13]⟩,
        ⟨5469, false, false, [], [15, 13]⟩,
        ⟨5469, false, false, [], [15, 13]⟩,
        ⟨15392, false, false, [1075], [13]⟩,
        ⟨17273, false, false, [1075], []⟩,
        ⟨17298, false, false, [], []⟩,
        ⟨17299, false, false, [], []⟩,
        ⟨17282, false, false, [1075], []⟩
      ]⟩,
    ⟨[82837, 15], [1075, 82837], .contexts [
        ⟨17301, false, false, [], []⟩,
        ⟨4778, true, false, [], [82837]⟩
      ]⟩,
    ⟨[82839], [82673, 5], .source 41484⟩,
    ⟨[82673, 5], [82839], .contexts [
        ⟨17303, true, false, [], []⟩
      ]⟩,
    ⟨[82839, 5], [82673], .contexts [
        ⟨17304, true, false, [], [5]⟩,
        ⟨28, false, false, [82673], []⟩,
        ⟨15215, false, false, [], []⟩
      ]⟩,
    ⟨[82839], [82839], .contexts []⟩,
    ⟨[82839], [82839], .contexts []⟩,
    ⟨[82673, 5], [82839], .contexts [
        ⟨17304, false, false, [], []⟩,
        ⟨17306, false, false, [], []⟩,
        ⟨17307, false, false, [], []⟩,
        ⟨17307, false, false, [], []⟩
      ]⟩,
    ⟨[15211, 82805], [15211, 82805], .contexts []⟩,
    ⟨[15211, 82805], [15211, 82805], .contexts []⟩,
    ⟨[15211, 82833], [15211, 82833], .contexts []⟩,
    ⟨[15211, 82833], [15211, 82833], .contexts []⟩,
    ⟨[82839, 1], [82839, 1], .contexts []⟩,
    ⟨[82839, 1], [15211, 82833], .contexts [
        ⟨17313, false, false, [], []⟩,
        ⟨17308, true, false, [], [1]⟩,
        ⟨161, false, false, [82673], []⟩,
        ⟨162, false, false, [82673], []⟩,
        ⟨16831, false, false, [], [5]⟩,
        ⟨17309, false, false, [], [5]⟩,
        ⟨17310, false, false, [], [5]⟩,
        ⟨17310, false, false, [], [5]⟩,
        ⟨17228, false, false, [15211], []⟩,
        ⟨17311, false, false, [], []⟩,
        ⟨17312, false, false, [], []⟩,
        ⟨17236, false, false, [15211], []⟩,
        ⟨15005, true, false, [], [82833]⟩
      ]⟩,
    ⟨[82833, 1], [15213, 82839], .contexts [
        ⟨17314, true, false, [15210], [1]⟩,
        ⟨8, false, false, [15210, 82839], []⟩,
        ⟨15007, true, false, [], [82839]⟩
      ]⟩,
    ⟨[15239, 82669], [15239, 82669], .contexts []⟩,
    ⟨[15239, 82669], [15239, 82669], .contexts []⟩,
    ⟨[82839, 11], [82839, 11], .contexts []⟩,
    ⟨[15239], [15239], .contexts [
        ⟨13, false, false, [], [15239]⟩
      ]⟩,
    ⟨[82839, 11], [15239, 82669], .contexts [
        ⟨17318, false, false, [], []⟩,
        ⟨17308, true, false, [], [11]⟩,
        ⟨174, false, false, [82673], []⟩,
        ⟨175, false, false, [82673], []⟩,
        ⟨15213, false, false, [], [5]⟩,
        ⟨15000, false, false, [], [5]⟩,
        ⟨15001, false, false, [], [5]⟩,
        ⟨15001, false, false, [], [5]⟩,
        ⟨15166, false, false, [], []⟩,
        ⟨17316, false, false, [], []⟩,
        ⟨17317, false, false, [], []⟩,
        ⟨17317, false, false, [], []⟩,
        ⟨15170, false, false, [15239], []⟩,
        ⟨17319, true, false, [], [82669]⟩
      ]⟩,
    ⟨[11661], [15238], .contexts [
        ⟨15165, true, true, [], []⟩
      ]⟩,
    ⟨[82669, 11], [11661, 82839], .contexts [
        ⟨17320, true, false, [15238], [11]⟩,
        ⟨53, false, false, [15238, 82839], []⟩,
        ⟨17321, true, false, [], [82839]⟩
      ]⟩,
    ⟨[743, 82839], [743, 82839], .contexts []⟩,
    ⟨[743, 82839], [743, 82839], .contexts []⟩,
    ⟨[82839, 13], [82839, 13], .contexts []⟩,
    ⟨[82839], [82839], .contexts []⟩,
    ⟨[82839, 13], [743, 82839], .contexts [
        ⟨17325, false, false, [], []⟩,
        ⟨17308, true, false, [], [13]⟩,
        ⟨179, false, false, [82673], []⟩,
        ⟨180, false, false, [82673], []⟩,
        ⟨15227, false, false, [], [5]⟩,
        ⟨15229, false, false, [], [5]⟩,
        ⟨15225, false, false, [], [5]⟩,
        ⟨15226, false, false, [], [5]⟩,
        ⟨15226, false, false, [], [5]⟩,
        ⟨17304, false, false, [743], []⟩,
        ⟨17323, false, false, [], []⟩,
        ⟨17324, false, false, [], []⟩,
        ⟨17326, false, false, [743], []⟩,
        ⟨15020, true, false, [], [82839]⟩
      ]⟩,
    ⟨[15251, 79185], [15251, 79185], .contexts []⟩,
    ⟨[15251, 79185], [15251, 79185], .contexts []⟩,
    ⟨[15613], [15251, 15481], .source 7871⟩,
    ⟨[82839, 15], [82839, 15], .contexts []⟩,
    ⟨[15613], [15613], .contexts [
        ⟨13, false, false, [], [15613]⟩
      ]⟩,
    ⟨[82839, 15], [15613, 82799], .contexts [
        ⟨17331, false, false, [], []⟩,
        ⟨17308, true, false, [], [15]⟩,
        ⟨184, false, false, [82673], []⟩,
        ⟨185, false, false, [82673], []⟩,
        ⟨15231, false, false, [], [5]⟩,
        ⟨15232, false, false, [], [5]⟩,
        ⟨17328, false, false, [], [5]⟩,
        ⟨17329, false, false, [], [5]⟩,
        ⟨17329, false, false, [], [5]⟩,
        ⟨16759, false, false, [15251], []⟩,
        ⟨17330, true, false, [], [82799]⟩,
        ⟨17185, false, false, [15613], []⟩,
        ⟨17332, true, false, [], [82799]⟩
      ]⟩,
    ⟨[15615], [15612], .source 7872⟩,
    ⟨[82841], [82839, 7], .source 41485⟩,
    ⟨[82839, 7], [82841], .contexts [
        ⟨17335, true, false, [], []⟩
      ]⟩,
    ⟨[82841], [82841], .contexts []⟩,
    ⟨[82841], [82841], .contexts []⟩,
    ⟨[82839, 7], [82841], .contexts [
        ⟨17336, false, false, [], []⟩,
        ⟨17337, false, false, [], []⟩,
        ⟨17338, false, false, [], []⟩,
        ⟨17338, false, false, [], []⟩
      ]⟩,
    ⟨[15211, 82835], [15211, 82835], .contexts []⟩,
    ⟨[82841, 1], [15211, 82835], .contexts [
        ⟨17339, true, false, [], [1]⟩,
        ⟨1027, false, false, [82839], []⟩,
        ⟨1028, false, false, [82839], []⟩,
        ⟨17313, false, false, [], [7]⟩,
        ⟨17314, false, false, [], [7]⟩,
        ⟨17311, false, false, [], [7]⟩,
        ⟨17312, false, false, [], [7]⟩,
        ⟨17312, false, false, [], [7]⟩,
        ⟨17248, false, false, [15211], []⟩,
        ⟨17340, false, false, [], []⟩,
        ⟨17262, false, false, [15211], []⟩,
        ⟨15005, true, false, [], [82835]⟩
      ]⟩,
    ⟨[82835, 1], [15213, 82841], .contexts [
        ⟨17341, true, false, [15210], [1]⟩,
        ⟨8, false, false, [15210, 82841], []⟩,
        ⟨15007, true, false, [], [82841]⟩
      ]⟩,
    ⟨[15617], [11241, 10181], .source 7873⟩]

/-- Exact literal claimed equations and contextual derivations, block 271. -/
def y322TCIndexRaw271 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15619], [15617, 15265], .source 7874⟩,
    ⟨[82841, 5], [82841, 5], .contexts []⟩,
    ⟨[82841, 5], [15619, 82677], .contexts [
        ⟨17345, false, false, [], []⟩,
        ⟨17339, true, false, [], [5]⟩,
        ⟨1043, false, false, [82839], []⟩,
        ⟨1046, false, false, [82839], []⟩,
        ⟨17305, false, false, [], [7, 5, 7]⟩,
        ⟨15214, false, false, [], [7, 5, 7]⟩,
        ⟨15215, false, false, [], [7, 5, 7]⟩,
        ⟨15215, false, false, [], [7, 5, 7]⟩,
        ⟨15222, false, false, [], [5, 7]⟩,
        ⟨15220, false, false, [], [5, 7]⟩,
        ⟨15221, false, false, [], [5, 7]⟩,
        ⟨15221, false, false, [], [5, 7]⟩,
        ⟨5370, false, false, [11241], [7]⟩,
        ⟨11387, false, false, [11241, 2467], [7]⟩,
        ⟨12426, true, false, [11241], [77317, 7]⟩,
        ⟨17343, true, false, [], [77317, 7]⟩,
        ⟨15280, false, false, [15617], []⟩,
        ⟨17344, true, false, [], [82677]⟩,
        ⟨15283, false, false, [15619], []⟩
      ]⟩,
    ⟨[82841, 5], [15619, 82677], .contexts [
        ⟨17346, false, false, [], []⟩,
        ⟨13, true, false, [], [15619, 82677]⟩
      ]⟩,
    ⟨[15621], [15618], .source 7875⟩,
    ⟨[82677, 5], [15621, 82841], .contexts [
        ⟨17347, true, false, [15618], [5]⟩,
        ⟨28, false, false, [15618, 82841], []⟩,
        ⟨17348, true, false, [], [82841]⟩
      ]⟩,
    ⟨[15239, 82667], [15239, 82667], .contexts []⟩,
    ⟨[15239, 82667], [15239, 82667], .contexts []⟩,
    ⟨[82841, 11], [82841, 11], .contexts []⟩,
    ⟨[82841, 11], [15239, 82667], .contexts [
        ⟨17352, false, false, [], []⟩,
        ⟨17339, true, false, [], [11]⟩,
        ⟨1051, false, false, [82839], []⟩,
        ⟨1052, false, false, [82839], []⟩,
        ⟨17318, false, false, [], [7]⟩,
        ⟨17320, false, false, [], [7]⟩,
        ⟨17316, false, false, [], [7]⟩,
        ⟨17317, false, false, [], [7]⟩,
        ⟨17317, false, false, [], [7]⟩,
        ⟨15152, false, false, [15239], []⟩,
        ⟨17350, false, false, [], []⟩,
        ⟨17351, false, false, [], []⟩,
        ⟨15143, false, false, [15239], []⟩,
        ⟨17319, true, false, [], [82667]⟩
      ]⟩,
    ⟨[82667, 11], [11661, 82841], .contexts [
        ⟨17353, true, false, [15238], [11]⟩,
        ⟨53, false, false, [15238, 82841], []⟩,
        ⟨17321, true, false, [], [82841]⟩
      ]⟩,
    ⟨[743, 82841], [743, 82841], .contexts []⟩,
    ⟨[743, 82841], [743, 82841], .contexts []⟩,
    ⟨[82841, 13], [82841, 13], .contexts []⟩,
    ⟨[82841], [82841], .contexts []⟩,
    ⟨[82841, 13], [743, 82841], .contexts [
        ⟨17357, false, false, [], []⟩,
        ⟨17339, true, false, [], [13]⟩,
        ⟨1056, false, false, [82839], []⟩,
        ⟨1057, false, false, [82839], []⟩,
        ⟨17325, false, false, [], [7]⟩,
        ⟨17327, false, false, [], [7]⟩,
        ⟨17323, false, false, [], [7]⟩,
        ⟨17324, false, false, [], [7]⟩,
        ⟨17324, false, false, [], [7]⟩,
        ⟨17336, false, false, [743], []⟩,
        ⟨17355, false, false, [], []⟩,
        ⟨17356, false, false, [], []⟩,
        ⟨17358, false, false, [743], []⟩,
        ⟨15020, true, false, [], [82841]⟩
      ]⟩,
    ⟨[15613, 82799], [15613, 82799], .contexts []⟩,
    ⟨[15613, 82799], [15613, 82799], .contexts []⟩,
    ⟨[15613, 82797], [15613, 82797], .contexts []⟩,
    ⟨[82841, 15], [15613, 82797], .contexts [
        ⟨17339, true, false, [], [15]⟩,
        ⟨1063, false, false, [82839], []⟩,
        ⟨1064, false, false, [82839], []⟩,
        ⟨17331, false, false, [], [7]⟩,
        ⟨17333, false, false, [], [7]⟩,
        ⟨17360, false, false, [], [7]⟩,
        ⟨17361, false, false, [], [7]⟩,
        ⟨17361, false, false, [], [7]⟩,
        ⟨16749, false, false, [15613], []⟩,
        ⟨17362, false, false, [], []⟩,
        ⟨17212, false, false, [15613], []⟩,
        ⟨17332, true, false, [], [82797]⟩
      ]⟩,
    ⟨[82797, 15], [15615, 82841], .contexts [
        ⟨17363, true, false, [15612], [15]⟩,
        ⟨1, false, false, [15612, 82841], []⟩,
        ⟨17334, true, false, [], [82841]⟩
      ]⟩,
    ⟨[82843], [82665, 5], .source 41486⟩,
    ⟨[82665, 5], [82843], .contexts [
        ⟨17365, true, false, [], []⟩
      ]⟩,
    ⟨[82843, 5], [82665], .contexts [
        ⟨17366, true, false, [], [5]⟩,
        ⟨28, false, false, [82665], []⟩,
        ⟨15111, false, false, [], []⟩
      ]⟩,
    ⟨[82665, 5], [82843], .contexts [
        ⟨17366, false, false, [], []⟩
      ]⟩,
    ⟨[82843], [82843], .contexts []⟩,
    ⟨[82843], [82843], .contexts []⟩,
    ⟨[82665, 5], [82843], .contexts [
        ⟨17368, false, false, [], []⟩,
        ⟨17369, false, false, [], []⟩,
        ⟨17370, false, false, [], []⟩,
        ⟨17370, false, false, [], []⟩
      ]⟩,
    ⟨[15233, 82843], [15233, 82843], .contexts []⟩,
    ⟨[15233, 82843], [15233, 82843], .contexts []⟩,
    ⟨[82843, 1], [82843, 1], .contexts []⟩,
    ⟨[82843], [82843], .contexts []⟩,
    ⟨[82843, 1], [15233, 82843], .contexts [
        ⟨17374, false, false, [], []⟩,
        ⟨17371, true, false, [], [1]⟩,
        ⟨161, false, false, [82665], []⟩,
        ⟨162, false, false, [82665], []⟩,
        ⟨15117, false, false, [], [5]⟩,
        ⟨15121, false, false, [], [5]⟩,
        ⟨15115, false, false, [], [5]⟩,
        ⟨15116, false, false, [], [5]⟩,
        ⟨15116, false, false, [], [5]⟩,
        ⟨17366, false, false, [15233], []⟩,
        ⟨17372, false, false, [], []⟩,
        ⟨17373, false, false, [], []⟩,
        ⟨17375, false, false, [15233], []⟩,
        ⟨15120, true, false, [], [82843]⟩
      ]⟩,
    ⟨[82843, 9], [82843, 9], .contexts []⟩,
    ⟨[82843, 9], [15229, 82663], .contexts [
        ⟨17377, false, false, [], []⟩,
        ⟨17371, true, false, [], [9]⟩,
        ⟨1265, false, false, [82665], []⟩,
        ⟨1266, false, false, [82665], []⟩,
        ⟨15109, false, false, [], [5]⟩,
        ⟨6846, false, false, [], [5]⟩,
        ⟨6847, false, false, [], [5]⟩,
        ⟨6847, false, false, [], [5]⟩,
        ⟨16976, false, false, [], []⟩,
        ⟨16977, false, false, [], []⟩,
        ⟨16978, false, false, [], []⟩,
        ⟨16978, false, false, [], []⟩,
        ⟨16980, false, false, [], []⟩,
        ⟨16982, false, false, [], []⟩
      ]⟩,
    ⟨[2575, 82843], [2575, 82843], .contexts []⟩,
    ⟨[2575, 82843], [2575, 82843], .contexts []⟩,
    ⟨[82843, 13], [82843, 13], .contexts []⟩,
    ⟨[82843, 13], [2575, 82843], .contexts [
        ⟨17381, false, false, [], []⟩,
        ⟨17371, true, false, [], [13]⟩,
        ⟨179, false, false, [82665], []⟩,
        ⟨180, false, false, [82665], []⟩,
        ⟨15127, false, false, [], [5]⟩,
        ⟨15128, false, false, [], [5]⟩,
        ⟨15125, false, false, [], [5]⟩,
        ⟨15126, false, false, [], [5]⟩,
        ⟨15126, false, false, [], [5]⟩,
        ⟨17366, false, false, [2575], []⟩,
        ⟨17379, false, false, [], []⟩,
        ⟨17380, false, false, [], []⟩,
        ⟨17375, false, false, [2575], []⟩,
        ⟨5618, true, false, [], [82843]⟩
      ]⟩,
    ⟨[82845], [82843, 7], .source 41487⟩,
    ⟨[82843, 7], [82845], .contexts [
        ⟨17383, true, false, [], []⟩
      ]⟩,
    ⟨[82845, 7], [82843], .contexts [
        ⟨17384, true, false, [], [7]⟩,
        ⟨38, false, false, [82843], []⟩,
        ⟨17370, false, false, [], []⟩
      ]⟩,
    ⟨[82843, 7], [82845], .contexts [
        ⟨17384, false, false, [], []⟩
      ]⟩,
    ⟨[82845], [82845], .contexts []⟩,
    ⟨[82845], [82845], .contexts []⟩,
    ⟨[82843, 7], [82845], .contexts [
        ⟨17386, false, false, [], []⟩,
        ⟨17387, false, false, [], []⟩,
        ⟨17388, false, false, [], []⟩,
        ⟨17388, false, false, [], []⟩
      ]⟩,
    ⟨[15233, 82845], [15233, 82845], .contexts []⟩,
    ⟨[15233, 82845], [15233, 82845], .contexts []⟩,
    ⟨[82845, 1], [82845, 1], .contexts []⟩,
    ⟨[82845], [82845], .contexts []⟩,
    ⟨[82845, 1], [15233, 82845], .contexts [
        ⟨17392, false, false, [], []⟩,
        ⟨17389, true, false, [], [1]⟩,
        ⟨1027, false, false, [82843], []⟩,
        ⟨1028, false, false, [82843], []⟩,
        ⟨17374, false, false, [], [7]⟩,
        ⟨17376, false, false, [], [7]⟩,
        ⟨17372, false, false, [], [7]⟩,
        ⟨17373, false, false, [], [7]⟩,
        ⟨17373, false, false, [], [7]⟩,
        ⟨17384, false, false, [15233], []⟩,
        ⟨17390, false, false, [], []⟩,
        ⟨17391, false, false, [], []⟩,
        ⟨17393, false, false, [15233], []⟩,
        ⟨15120, true, false, [], [82845]⟩
      ]⟩,
    ⟨[15235, 77321], [15235, 77321], .contexts []⟩,
    ⟨[15235, 77321], [15235, 77321], .contexts []⟩,
    ⟨[15623], [15235, 15523], .source 7876⟩,
    ⟨[82845, 5], [15623, 82809], .contexts [
        ⟨17389, true, false, [], [5]⟩,
        ⟨1043, false, false, [82843], []⟩,
        ⟨1046, false, false, [82843], []⟩,
        ⟨17367, false, false, [], [7, 5, 7]⟩,
        ⟨15110, false, false, [], [7, 5, 7]⟩,
        ⟨15111, false, false, [], [7, 5, 7]⟩,
        ⟨15111, false, false, [], [7, 5, 7]⟩,
        ⟨15123, false, false, [], [5, 7]⟩,
        ⟨17395, false, false, [], [5, 7]⟩,
        ⟨17396, false, false, [], [5, 7]⟩,
        ⟨17396, false, false, [], [5, 7]⟩,
        ⟨797, false, false, [15235], [7]⟩,
        ⟨16892, false, false, [15235], []⟩,
        ⟨17397, true, false, [], [82809]⟩,
        ⟨16882, false, false, [15623], []⟩
      ]⟩,
    ⟨[82845, 5], [15623, 82809], .contexts [
        ⟨17398, false, false, [], []⟩,
        ⟨13, true, false, [], [15623, 82809]⟩
      ]⟩,
    ⟨[15625], [15622], .source 7877⟩,
    ⟨[82809, 5], [15625, 82845], .contexts [
        ⟨17399, true, false, [15622], [5]⟩,
        ⟨28, false, false, [15622, 82845], []⟩,
        ⟨17400, true, false, [], [82845]⟩
      ]⟩,
    ⟨[82845, 9], [15229, 82661], .contexts [
        ⟨17389, true, false, [], [9]⟩,
        ⟨1534, false, false, [82843], []⟩,
        ⟨1535, false, false, [82843], []⟩,
        ⟨17377, false, false, [], [7]⟩,
        ⟨17378, false, false, [], [7]⟩,
        ⟨16977, false, false, [], [7]⟩,
        ⟨16978, false, false, [], [7]⟩,
        ⟨16978, false, false, [], [7]⟩,
        ⟨17019, false, false, [], []⟩,
        ⟨17020, false, false, [], []⟩,
        ⟨17021, false, false, [], []⟩,
        ⟨17022, false, false, [], []⟩,
        ⟨17023, false, false, [], []⟩,
        ⟨17024, false, false, [], []⟩
      ]⟩,
    ⟨[82661, 9], [15227, 82845], .contexts [
        ⟨17402, true, false, [15228], [9]⟩,
        ⟨46, false, false, [15228, 82845], []⟩,
        ⟨16984, true, false, [], [82845]⟩
      ]⟩,
    ⟨[2575, 82845], [2575, 82845], .contexts []⟩,
    ⟨[2575, 82845], [2575, 82845], .contexts []⟩,
    ⟨[82845, 13], [82845, 13], .contexts []⟩,
    ⟨[82845, 13], [2575, 82845], .contexts [
        ⟨17406, false, false, [], []⟩,
        ⟨17389, true, false, [], [13]⟩,
        ⟨1056, false, false, [82843], []⟩,
        ⟨1057, false, false, [82843], []⟩,
        ⟨17381, false, false, [], [7]⟩,
        ⟨17382, false, false, [], [7]⟩,
        ⟨17379, false, false, [], [7]⟩,
        ⟨17380, false, false, [], [7]⟩,
        ⟨17380, false, false, [], [7]⟩,
        ⟨17384, false, false, [2575], []⟩,
        ⟨17404, false, false, [], []⟩,
        ⟨17405, false, false, [], []⟩,
        ⟨17393, false, false, [2575], []⟩,
        ⟨5618, true, false, [], [82845]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 272. -/
def y322TCIndexRaw272 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82847], [77337, 7], .source 74647⟩,
    ⟨[77337, 7], [82847], .contexts [
        ⟨17408, true, false, [], []⟩
      ]⟩,
    ⟨[82847, 7], [77337], .contexts [
        ⟨17409, true, false, [], [7]⟩,
        ⟨38, false, false, [77337], []⟩,
        ⟨811, false, false, [], []⟩
      ]⟩,
    ⟨[82847], [82847], .contexts []⟩,
    ⟨[82847], [82847], .source 74648⟩,
    ⟨[77337, 7], [82847], .source 74649⟩,
    ⟨[15627], [267, 537], .source 7878⟩,
    ⟨[82847, 1], [82847, 1], .contexts []⟩,
    ⟨[15627], [15627], .contexts [
        ⟨13, false, false, [], [15627]⟩
      ]⟩,
    ⟨[82847, 1], [15627, 78125], .contexts [
        ⟨17415, false, false, [], []⟩,
        ⟨17413, true, false, [], [1]⟩,
        ⟨1027, false, false, [77337], []⟩,
        ⟨1028, false, false, [77337], []⟩,
        ⟨970, false, false, [], [7]⟩,
        ⟨958, false, false, [], [7]⟩,
        ⟨959, false, false, [], [7]⟩,
        ⟨959, false, false, [], [7]⟩,
        ⟨3731, false, false, [267], []⟩,
        ⟨17414, true, false, [], [78125]⟩,
        ⟨3728, false, false, [15627], []⟩,
        ⟨17416, true, false, [], [78125]⟩
      ]⟩,
    ⟨[15629], [15626], .source 7879⟩,
    ⟨[15626, 82847], [15629, 82847], .contexts [
        ⟨17418, true, false, [], [82847]⟩
      ]⟩,
    ⟨[78125, 1], [15629, 82847], .contexts [
        ⟨17417, true, false, [15626], [1]⟩,
        ⟨8, false, false, [15626, 82847], []⟩,
        ⟨17419, false, false, [], []⟩
      ]⟩,
    ⟨[15631], [501, 703], .source 7880⟩,
    ⟨[82847, 3], [82847, 3], .contexts []⟩,
    ⟨[82847, 3], [15631, 82735], .contexts [
        ⟨17422, false, false, [], []⟩,
        ⟨17413, true, false, [], [3]⟩,
        ⟨1034, false, false, [77337], []⟩,
        ⟨1035, false, false, [77337], []⟩,
        ⟨1566, false, false, [], [7]⟩,
        ⟨1572, false, false, [], [7]⟩,
        ⟨1570, false, false, [], [7]⟩,
        ⟨1570, false, false, [], [7]⟩,
        ⟨15957, false, false, [501], []⟩,
        ⟨17421, true, false, [], [82735]⟩,
        ⟨15952, false, false, [15631], []⟩,
        ⟨13, true, false, [], [15631, 82735]⟩
      ]⟩,
    ⟨[15633], [15630], .source 7881⟩,
    ⟨[82735, 3], [15633, 82847], .contexts [
        ⟨17423, true, false, [15630], [3]⟩,
        ⟨20, false, false, [15630, 82847], []⟩,
        ⟨17424, true, false, [], [82847]⟩
      ]⟩,
    ⟨[679, 77601], [679, 77601], .contexts []⟩,
    ⟨[679, 77601], [679, 77601], .source 74650⟩,
    ⟨[679, 82727], [679, 82727], .contexts []⟩,
    ⟨[82847, 9], [679, 82727], .contexts [
        ⟨17413, true, false, [], [9]⟩,
        ⟨1534, false, false, [77337], []⟩,
        ⟨1535, false, false, [77337], []⟩,
        ⟨1967, false, false, [], [7]⟩,
        ⟨17426, false, false, [], [7]⟩,
        ⟨17427, false, false, [], [7]⟩,
        ⟨17427, false, false, [], [7]⟩,
        ⟨15837, false, false, [679], []⟩,
        ⟨17428, false, false, [], []⟩,
        ⟨15853, false, false, [679], []⟩,
        ⟨13, true, false, [], [679, 82727]⟩
      ]⟩,
    ⟨[82727, 9], [677, 82847], .contexts [
        ⟨17429, true, false, [678], [9]⟩,
        ⟨46, false, false, [678, 82847], []⟩,
        ⟨1966, false, true, [], [82847]⟩
      ]⟩,
    ⟨[267, 77865], [267, 77865], .contexts []⟩,
    ⟨[267, 77865], [267, 77865], .contexts []⟩,
    ⟨[82847, 11], [82847, 11], .contexts []⟩,
    ⟨[82847, 11], [15627, 78415], .contexts [
        ⟨17433, false, false, [], []⟩,
        ⟨17413, true, false, [], [11]⟩,
        ⟨1051, false, false, [77337], []⟩,
        ⟨1052, false, false, [77337], []⟩,
        ⟨2880, false, false, [], [7]⟩,
        ⟨17431, false, false, [], [7]⟩,
        ⟨17432, false, false, [], [7]⟩,
        ⟨17432, false, false, [], [7]⟩,
        ⟨4374, false, false, [267], []⟩,
        ⟨17414, true, false, [], [78415]⟩,
        ⟨4377, false, false, [15627], []⟩,
        ⟨17416, true, false, [], [78415]⟩
      ]⟩,
    ⟨[78415, 11], [15629, 82847], .contexts [
        ⟨17434, true, false, [15626], [11]⟩,
        ⟨53, false, false, [15626, 82847], []⟩,
        ⟨17419, false, false, [], []⟩
      ]⟩,
    ⟨[15635], [1277, 10715], .source 74651⟩,
    ⟨[15637], [15635, 10713], .source 74652⟩,
    ⟨[82847, 15], [82847, 15], .source 74653⟩,
    ⟨[82847, 15], [15637, 78117], .contexts [
        ⟨17438, false, false, [], []⟩,
        ⟨17413, true, false, [], [15]⟩,
        ⟨1063, false, false, [77337], []⟩,
        ⟨1064, false, false, [77337], []⟩,
        ⟨3232, false, false, [], [7]⟩,
        ⟨12704, false, false, [1277], [7]⟩,
        ⟨17436, true, false, [], [77939, 7]⟩,
        ⟨12708, false, false, [15635], []⟩,
        ⟨17437, true, false, [], [78117]⟩,
        ⟨3867, false, false, [15637], []⟩,
        ⟨13, true, false, [], [15637, 78117]⟩
      ]⟩,
    ⟨[15639], [15636], .source 7884⟩,
    ⟨[78117, 15], [15639, 82847], .contexts [
        ⟨17439, true, false, [15636], [15]⟩,
        ⟨1, false, false, [15636, 82847], []⟩,
        ⟨17440, true, false, [], [82847]⟩
      ]⟩,
    ⟨[82849], [80803, 5], .source 41489⟩,
    ⟨[80803, 5], [82849], .contexts [
        ⟨17442, true, false, [], []⟩
      ]⟩,
    ⟨[82849, 5], [80803], .contexts [
        ⟨17443, true, false, [], [5]⟩,
        ⟨28, false, false, [80803], []⟩,
        ⟨8269, false, false, [], []⟩
      ]⟩,
    ⟨[82849], [82849], .contexts []⟩,
    ⟨[82849], [82849], .contexts []⟩,
    ⟨[80803, 5], [82849], .contexts [
        ⟨17443, false, false, [], []⟩,
        ⟨17445, false, false, [], []⟩,
        ⟨17446, false, false, [], []⟩,
        ⟨17446, false, false, [], []⟩
      ]⟩,
    ⟨[15099, 80803], [15099, 80803], .contexts []⟩,
    ⟨[15099, 80803], [15099, 80803], .contexts []⟩,
    ⟨[15099, 82849], [15099, 82849], .contexts []⟩,
    ⟨[15099, 82849], [15099, 82849], .contexts []⟩,
    ⟨[82849, 1], [82849, 1], .contexts []⟩,
    ⟨[82849], [82849], .contexts []⟩,
    ⟨[15099], [15099], .contexts [
        ⟨13, false, false, [], [15099]⟩
      ]⟩,
    ⟨[82849, 1], [15099, 82849], .contexts [
        ⟨17452, false, false, [], []⟩,
        ⟨17447, true, false, [], [1]⟩,
        ⟨161, false, false, [80803], []⟩,
        ⟨162, false, false, [80803], []⟩,
        ⟨14773, false, false, [], [5]⟩,
        ⟨14776, false, false, [], [5]⟩,
        ⟨17448, false, false, [], [5]⟩,
        ⟨17449, false, false, [], [5]⟩,
        ⟨17449, false, false, [], [5]⟩,
        ⟨17443, false, false, [15099], []⟩,
        ⟨17450, false, false, [], []⟩,
        ⟨17451, false, false, [], []⟩,
        ⟨17453, false, false, [15099], []⟩,
        ⟨17454, true, false, [], [82849]⟩
      ]⟩,
    ⟨[15097, 82729], [15097, 82729], .contexts []⟩,
    ⟨[15097, 82729], [15097, 82729], .contexts []⟩,
    ⟨[15097, 82731], [15097, 82731], .contexts []⟩,
    ⟨[15097, 82731], [15097, 82731], .contexts []⟩,
    ⟨[82849, 9], [82849, 9], .contexts []⟩,
    ⟨[15097], [15097], .contexts [
        ⟨13, false, false, [], [15097]⟩
      ]⟩,
    ⟨[82849, 9], [15097, 82731], .contexts [
        ⟨17460, false, false, [], []⟩,
        ⟨17447, true, false, [], [9]⟩,
        ⟨1265, false, false, [80803], []⟩,
        ⟨1266, false, false, [80803], []⟩,
        ⟨15875, false, false, [], [5]⟩,
        ⟨17456, false, false, [], [5]⟩,
        ⟨17457, false, false, [], [5]⟩,
        ⟨17457, false, false, [], [5]⟩,
        ⟨15902, false, false, [15097], []⟩,
        ⟨17458, false, false, [], []⟩,
        ⟨17459, false, false, [], []⟩,
        ⟨15912, false, false, [15097], []⟩,
        ⟨17461, true, false, [], [82731]⟩
      ]⟩,
    ⟨[15095], [15096], .contexts [
        ⟨14774, true, true, [], []⟩
      ]⟩,
    ⟨[82731, 9], [15095, 82849], .contexts [
        ⟨17462, true, false, [15096], [9]⟩,
        ⟨46, false, false, [15096, 82849], []⟩,
        ⟨17463, true, false, [], [82849]⟩
      ]⟩,
    ⟨[82849, 13], [82849, 13], .contexts []⟩,
    ⟨[15157, 80793], [15157, 80793], .contexts [
        ⟨8408, false, false, [15157], []⟩
      ]⟩,
    ⟨[15157], [15157], .contexts [
        ⟨13, false, false, [], [15157]⟩
      ]⟩,
    ⟨[15157, 80793], [15157, 80793], .contexts [
        ⟨17467, true, false, [], [80793]⟩
      ]⟩,
    ⟨[82849, 13], [15157, 80793], .contexts [
        ⟨17465, false, false, [], []⟩,
        ⟨17447, true, false, [], [13]⟩,
        ⟨179, false, false, [80803], []⟩,
        ⟨180, false, false, [80803], []⟩,
        ⟨8267, false, false, [], [5]⟩,
        ⟨14866, false, false, [], [5]⟩,
        ⟨12055, false, false, [], [5]⟩,
        ⟨12055, false, false, [], [5]⟩,
        ⟨14867, false, false, [], []⟩,
        ⟨14868, false, false, [], []⟩,
        ⟨14869, false, false, [], []⟩,
        ⟨14871, false, false, [], []⟩,
        ⟨17466, false, false, [], []⟩,
        ⟨17468, false, false, [], []⟩
      ]⟩,
    ⟨[80793, 13], [15159, 82849], .contexts [
        ⟨17469, true, false, [15156], [13]⟩,
        ⟨59, false, false, [15156, 82849], []⟩,
        ⟨14877, true, false, [], [82849]⟩
      ]⟩,
    ⟨[15415, 82767], [15415, 82767], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 273. -/
def y322TCIndexRaw273 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15415, 82767], [15415, 82767], .contexts []⟩,
    ⟨[15641], [15415, 15419], .source 7885⟩,
    ⟨[82849, 15], [82849, 15], .contexts []⟩,
    ⟨[15641], [15641], .contexts [
        ⟨13, false, false, [], [15641]⟩
      ]⟩,
    ⟨[82849, 15], [15641, 82771], .contexts [
        ⟨17474, false, false, [], []⟩,
        ⟨17447, true, false, [], [15]⟩,
        ⟨184, false, false, [80803], []⟩,
        ⟨185, false, false, [80803], []⟩,
        ⟨16401, false, false, [], [5]⟩,
        ⟨17471, false, false, [], [5]⟩,
        ⟨17472, false, false, [], [5]⟩,
        ⟨17472, false, false, [], [5]⟩,
        ⟨16430, false, false, [15415], []⟩,
        ⟨17473, true, false, [], [82771]⟩,
        ⟨16424, false, false, [15641], []⟩,
        ⟨17475, true, false, [], [82771]⟩
      ]⟩,
    ⟨[15643], [15640], .source 7886⟩,
    ⟨[82851], [82849, 7], .source 41490⟩,
    ⟨[82849, 7], [82851], .contexts [
        ⟨17478, true, false, [], []⟩
      ]⟩,
    ⟨[82851, 7], [82849], .contexts [
        ⟨17479, true, false, [], [7]⟩,
        ⟨38, false, false, [82849], []⟩,
        ⟨17446, false, false, [], []⟩
      ]⟩,
    ⟨[82851], [82851], .contexts []⟩,
    ⟨[82851], [82851], .contexts []⟩,
    ⟨[82849, 7], [82851], .contexts [
        ⟨17479, false, false, [], []⟩,
        ⟨17481, false, false, [], []⟩,
        ⟨17482, false, false, [], []⟩,
        ⟨17482, false, false, [], []⟩
      ]⟩,
    ⟨[15099, 82851], [15099, 82851], .contexts []⟩,
    ⟨[15099, 82851], [15099, 82851], .contexts []⟩,
    ⟨[82851, 1], [82851, 1], .contexts []⟩,
    ⟨[82851], [82851], .contexts []⟩,
    ⟨[82851, 1], [15099, 82851], .contexts [
        ⟨17486, false, false, [], []⟩,
        ⟨17483, true, false, [], [1]⟩,
        ⟨1027, false, false, [82849], []⟩,
        ⟨1028, false, false, [82849], []⟩,
        ⟨17452, false, false, [], [7]⟩,
        ⟨17455, false, false, [], [7]⟩,
        ⟨17450, false, false, [], [7]⟩,
        ⟨17451, false, false, [], [7]⟩,
        ⟨17451, false, false, [], [7]⟩,
        ⟨17479, false, false, [15099], []⟩,
        ⟨17484, false, false, [], []⟩,
        ⟨17485, false, false, [], []⟩,
        ⟨17487, false, false, [15099], []⟩,
        ⟨17454, true, false, [], [82851]⟩
      ]⟩,
    ⟨[8669, 77751], [8669, 77751], .contexts []⟩,
    ⟨[15645], [8669, 5919], .source 7887⟩,
    ⟨[15647], [15645, 703], .source 7888⟩,
    ⟨[82851, 5], [82851, 5], .contexts []⟩,
    ⟨[82851, 5], [15647, 82735], .contexts [
        ⟨17492, false, false, [], []⟩,
        ⟨17483, true, false, [], [5]⟩,
        ⟨1043, false, false, [82849], []⟩,
        ⟨1046, false, false, [82849], []⟩,
        ⟨17444, false, false, [], [7, 5, 7]⟩,
        ⟨8268, false, false, [], [7, 5, 7]⟩,
        ⟨8269, false, false, [], [7, 5, 7]⟩,
        ⟨8269, false, false, [], [7, 5, 7]⟩,
        ⟨8274, false, false, [], [5, 7]⟩,
        ⟨11654, false, false, [], [5, 7]⟩,
        ⟨11680, false, false, [], [5, 7]⟩,
        ⟨11681, true, false, [], [77751, 5, 7]⟩,
        ⟨17489, false, false, [], [5, 7]⟩,
        ⟨17489, false, false, [], [5, 7]⟩,
        ⟨2555, false, false, [8669], [7]⟩,
        ⟨10499, false, false, [8669], [7]⟩,
        ⟨17490, true, false, [], [77333, 7]⟩,
        ⟨15957, false, false, [15645], []⟩,
        ⟨17491, true, false, [], [82735]⟩,
        ⟨15952, false, false, [15647], []⟩
      ]⟩,
    ⟨[82851, 5], [15647, 82735], .contexts [
        ⟨17493, false, false, [], []⟩,
        ⟨13, true, false, [], [15647, 82735]⟩
      ]⟩,
    ⟨[15649], [15646], .source 7889⟩,
    ⟨[82735, 5], [15649, 82851], .contexts [
        ⟨17494, true, false, [15646], [5]⟩,
        ⟨28, false, false, [15646, 82851], []⟩,
        ⟨17495, true, false, [], [82851]⟩
      ]⟩,
    ⟨[15097, 82733], [15097, 82733], .contexts []⟩,
    ⟨[15097, 82733], [15097, 82733], .contexts []⟩,
    ⟨[82851, 9], [82851, 9], .contexts []⟩,
    ⟨[82851, 9], [15097, 82733], .contexts [
        ⟨17499, false, false, [], []⟩,
        ⟨17483, true, false, [], [9]⟩,
        ⟨1534, false, false, [82849], []⟩,
        ⟨1535, false, false, [82849], []⟩,
        ⟨17460, false, false, [], [7]⟩,
        ⟨17462, false, false, [], [7]⟩,
        ⟨17458, false, false, [], [7]⟩,
        ⟨17459, false, false, [], [7]⟩,
        ⟨17459, false, false, [], [7]⟩,
        ⟨15922, false, false, [15097], []⟩,
        ⟨17497, false, false, [], []⟩,
        ⟨17498, false, false, [], []⟩,
        ⟨15937, false, false, [15097], []⟩,
        ⟨17461, true, false, [], [82733]⟩
      ]⟩,
    ⟨[82733, 9], [15095, 82851], .contexts [
        ⟨17500, true, false, [15096], [9]⟩,
        ⟨46, false, false, [15096, 82851], []⟩,
        ⟨17463, true, false, [], [82851]⟩
      ]⟩,
    ⟨[15157, 80793], [15157, 80793], .contexts []⟩,
    ⟨[15157, 80793], [15157, 80793], .contexts []⟩,
    ⟨[15157, 80793, 7], [15157, 80791], .contexts [
        ⟨8237, false, false, [15157], []⟩
      ]⟩,
    ⟨[15157, 80791], [15157, 80791], .contexts []⟩,
    ⟨[15157, 80791], [15157, 80791], .contexts []⟩,
    ⟨[15157, 80791], [15157, 80791], .contexts []⟩,
    ⟨[82851, 13], [82851, 13], .contexts []⟩,
    ⟨[15157, 80791], [15157, 80791], .contexts [
        ⟨8390, false, false, [15157], []⟩
      ]⟩,
    ⟨[15157, 80791], [15157, 80791], .contexts [
        ⟨17467, true, false, [], [80791]⟩
      ]⟩,
    ⟨[82851, 13], [15157, 80791], .contexts [
        ⟨17508, false, false, [], []⟩,
        ⟨17483, true, false, [], [13]⟩,
        ⟨1056, false, false, [82849], []⟩,
        ⟨1057, false, false, [82849], []⟩,
        ⟨17465, false, false, [], [7]⟩,
        ⟨17469, false, false, [], [7]⟩,
        ⟨17502, false, false, [], [7]⟩,
        ⟨17503, false, false, [], [7]⟩,
        ⟨17503, false, false, [], [7]⟩,
        ⟨17504, false, false, [], []⟩,
        ⟨17505, false, false, [], []⟩,
        ⟨17506, false, false, [], []⟩,
        ⟨17507, false, false, [], []⟩,
        ⟨17509, false, false, [], []⟩,
        ⟨17510, false, false, [], []⟩
      ]⟩,
    ⟨[80791, 13], [15159, 82851], .contexts [
        ⟨17511, true, false, [15156], [13]⟩,
        ⟨59, false, false, [15156, 82851], []⟩,
        ⟨14877, true, false, [], [82851]⟩
      ]⟩,
    ⟨[15641, 82771], [15641, 82771], .contexts []⟩,
    ⟨[15641, 82771], [15641, 82771], .contexts []⟩,
    ⟨[15641, 82769], [15641, 82769], .contexts []⟩,
    ⟨[15641, 82769], [15641, 82769], .contexts []⟩,
    ⟨[82851, 15], [82851, 15], .contexts []⟩,
    ⟨[82851, 15], [15641, 82769], .contexts [
        ⟨17517, false, false, [], []⟩,
        ⟨17483, true, false, [], [15]⟩,
        ⟨1063, false, false, [82849], []⟩,
        ⟨1064, false, false, [82849], []⟩,
        ⟨17474, false, false, [], [7]⟩,
        ⟨17476, false, false, [], [7]⟩,
        ⟨17513, false, false, [], [7]⟩,
        ⟨17514, false, false, [], [7]⟩,
        ⟨17514, false, false, [], [7]⟩,
        ⟨16419, false, false, [15641], []⟩,
        ⟨17515, false, false, [], []⟩,
        ⟨17516, false, false, [], []⟩,
        ⟨16409, false, false, [15641], []⟩,
        ⟨17475, true, false, [], [82769]⟩
      ]⟩,
    ⟨[82769, 15], [15643, 82851], .contexts [
        ⟨17518, true, false, [15640], [15]⟩,
        ⟨1, false, false, [15640, 82851], []⟩,
        ⟨17477, true, false, [], [82851]⟩
      ]⟩,
    ⟨[82853], [82847, 5], .source 41491⟩,
    ⟨[82847, 5], [82853], .contexts [
        ⟨17520, true, false, [], []⟩
      ]⟩,
    ⟨[82853, 5], [82847], .contexts [
        ⟨17521, true, false, [], [5]⟩,
        ⟨28, false, false, [82847], []⟩,
        ⟨17412, false, false, [], []⟩
      ]⟩,
    ⟨[82847, 5], [82853], .contexts [
        ⟨17521, false, false, [], []⟩
      ]⟩,
    ⟨[82853], [82853], .contexts []⟩,
    ⟨[82853], [82853], .contexts []⟩,
    ⟨[82847, 7], [77337], .contexts [
        ⟨17410, false, false, [], []⟩,
        ⟨834, false, false, [], []⟩,
        ⟨811, false, false, [], []⟩,
        ⟨811, false, false, [], []⟩
      ]⟩,
    ⟨[261, 82853], [261, 82853], .contexts []⟩,
    ⟨[82853], [82853], .contexts []⟩,
    ⟨[82853, 7], [261, 82853], .contexts [
        ⟨17525, true, false, [], [7]⟩,
        ⟨17525, true, false, [], [7]⟩,
        ⟨17524, true, false, [], [7]⟩,
        ⟨17523, true, false, [], [7]⟩,
        ⟨3272, false, false, [82847], []⟩,
        ⟨3275, false, false, [82847], []⟩,
        ⟨17526, false, false, [], [5, 7, 5]⟩,
        ⟨810, false, false, [], [7, 5]⟩,
        ⟨1563, false, false, [], [7, 5]⟩,
        ⟨969, false, false, [], [7, 5]⟩,
        ⟨969, false, false, [], [7, 5]⟩,
        ⟨17409, false, false, [261], [5]⟩,
        ⟨17521, false, false, [261], []⟩,
        ⟨17527, false, false, [], []⟩,
        ⟨17528, false, false, [261], []⟩,
        ⟨1604, true, false, [], [82853]⟩
      ]⟩,
    ⟨[82847, 13], [82855], .source 74655⟩,
    ⟨[82855, 13], [82847], .contexts [
        ⟨17530, true, false, [], [13]⟩,
        ⟨59, false, false, [82847], []⟩,
        ⟨17412, false, false, [], []⟩
      ]⟩,
    ⟨[82855], [82855], .contexts []⟩,
    ⟨[82855], [82855], .source 74656⟩,
    ⟨[82847, 13], [82855], .contexts [
        ⟨17530, false, false, [], []⟩,
        ⟨17532, false, false, [], []⟩,
        ⟨17533, false, false, [], []⟩,
        ⟨17533, false, false, [], []⟩
      ]⟩,
    ⟨[15627, 78125], [15627, 78125], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 274. -/
def y322TCIndexRaw274 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15627, 78125], [15627, 78125], .contexts []⟩,
    ⟨[15651], [15627, 1389], .source 7890⟩,
    ⟨[15653], [15651, 15629], .source 7891⟩,
    ⟨[15653, 82855], [15653, 82855], .contexts []⟩,
    ⟨[15653, 82855], [15653, 82855], .contexts []⟩,
    ⟨[82855, 1], [82855, 1], .contexts []⟩,
    ⟨[82855], [82855], .contexts []⟩,
    ⟨[82855, 1], [15653, 82855], .contexts [
        ⟨17541, false, false, [], []⟩,
        ⟨17534, true, false, [], [1]⟩,
        ⟨246, false, false, [82847], []⟩,
        ⟨249, false, false, [82847], []⟩,
        ⟨17415, false, false, [], [13, 1, 13]⟩,
        ⟨17417, false, false, [], [13, 1, 13]⟩,
        ⟨17535, false, false, [], [13, 1, 13]⟩,
        ⟨17536, false, false, [], [13, 1, 13]⟩,
        ⟨17536, false, false, [], [13, 1, 13]⟩,
        ⟨3741, false, false, [15627], [1, 13]⟩,
        ⟨17537, true, false, [], [78125, 1, 13]⟩,
        ⟨17420, false, false, [15651], [13]⟩,
        ⟨17538, true, false, [], [82847, 13]⟩,
        ⟨17530, false, false, [15653], []⟩,
        ⟨17539, false, false, [], []⟩,
        ⟨17540, false, false, [], []⟩,
        ⟨17542, false, false, [15653], []⟩
      ]⟩,
    ⟨[82855, 1], [15653, 82855], .contexts [
        ⟨17543, false, false, [], []⟩,
        ⟨13, true, false, [], [15653, 82855]⟩
      ]⟩,
    ⟨[15631, 82735], [15631, 82735], .contexts []⟩,
    ⟨[15631, 82735], [15631, 82735], .contexts []⟩,
    ⟨[15655], [15631, 15369], .source 7892⟩,
    ⟨[82855, 3], [15655, 79899], .contexts [
        ⟨17534, true, false, [], [3]⟩,
        ⟨63, false, false, [82847], []⟩,
        ⟨65, false, false, [82847], []⟩,
        ⟨17422, false, false, [], [13]⟩,
        ⟨17423, false, false, [], [13]⟩,
        ⟨17545, false, false, [], [13]⟩,
        ⟨17546, false, false, [], [13]⟩,
        ⟨17546, false, false, [], [13]⟩,
        ⟨15973, false, false, [15631], []⟩,
        ⟨17547, true, false, [], [79899]⟩,
        ⟨7557, false, false, [15655], []⟩,
        ⟨13, true, false, [], [15655, 79899]⟩
      ]⟩,
    ⟨[15657], [15654], .source 7893⟩,
    ⟨[79899, 3], [15657, 82855], .contexts [
        ⟨17548, true, false, [15654], [3]⟩,
        ⟨20, false, false, [15654, 82855], []⟩,
        ⟨17549, true, false, [], [82855]⟩
      ]⟩,
    ⟨[82855, 7], [82855, 7], .contexts []⟩,
    ⟨[82855, 7], [709, 77455], .contexts [
        ⟨17551, false, false, [], []⟩,
        ⟨17534, true, false, [], [7]⟩,
        ⟨73, false, false, [82847], []⟩,
        ⟨74, false, false, [82847], []⟩,
        ⟨17526, false, false, [], [13]⟩,
        ⟨1981, false, false, [], []⟩,
        ⟨1996, false, false, [], []⟩,
        ⟨1997, false, false, [], []⟩,
        ⟨1997, false, false, [], []⟩,
        ⟨1980, false, false, [709], []⟩,
        ⟨13, true, false, [], [709, 77455]⟩
      ]⟩,
    ⟨[77455, 7], [711, 82855], .contexts [
        ⟨17552, true, false, [708], [7]⟩,
        ⟨38, false, false, [708, 82855], []⟩,
        ⟨1982, true, false, [], [82855]⟩
      ]⟩,
    ⟨[15627, 78415], [15627, 78415], .contexts []⟩,
    ⟨[15627, 78415], [15627, 78415], .contexts []⟩,
    ⟨[15659], [15627, 15077], .source 7894⟩,
    ⟨[82855, 11], [15659, 79885], .contexts [
        ⟨17534, true, false, [], [11]⟩,
        ⟨82, false, false, [82847], []⟩,
        ⟨83, false, false, [82847], []⟩,
        ⟨17433, false, false, [], [13]⟩,
        ⟨17434, false, false, [], [13]⟩,
        ⟨17554, false, false, [], [13]⟩,
        ⟨17555, false, false, [], [13]⟩,
        ⟨17555, false, false, [], [13]⟩,
        ⟨14748, false, false, [15627], []⟩,
        ⟨17556, true, false, [], [79885]⟩,
        ⟨7324, false, false, [15659], []⟩,
        ⟨13, true, false, [], [15659, 79885]⟩
      ]⟩,
    ⟨[15661], [15658], .source 7895⟩,
    ⟨[79885, 11], [15661, 82855], .contexts [
        ⟨17557, true, false, [15658], [11]⟩,
        ⟨53, false, false, [15658, 82855], []⟩,
        ⟨17558, true, false, [], [82855]⟩
      ]⟩,
    ⟨[82847, 15, 13, 15, 13], [15663, 81773], .source 74660⟩,
    ⟨[82855, 15], [15663, 81773], .contexts [
        ⟨17534, true, false, [], [15]⟩,
        ⟨88, false, false, [82847], []⟩,
        ⟨91, false, false, [82847], []⟩,
        ⟨17560, false, false, [], []⟩,
        ⟨9366, false, false, [15663], []⟩,
        ⟨13, true, false, [], [15663, 81773]⟩
      ]⟩,
    ⟨[15665], [15662], .source 7897⟩,
    ⟨[81773, 15], [15665, 82855], .contexts [
        ⟨17561, true, false, [15662], [15]⟩,
        ⟨1, false, false, [15662, 82855], []⟩,
        ⟨17562, true, false, [], [82855]⟩
      ]⟩,
    ⟨[78125, 5], [82857], .source 74662⟩,
    ⟨[82857], [82857], .contexts []⟩,
    ⟨[82857], [82857], .source 74663⟩,
    ⟨[78125, 5], [82857], .source 74664⟩,
    ⟨[15629, 82847], [15629, 82847], .contexts []⟩,
    ⟨[15629, 82847], [15629, 82847], .contexts []⟩,
    ⟨[15629, 82853], [15629, 82853], .contexts []⟩,
    ⟨[15629, 82853], [15629, 82853], .contexts []⟩,
    ⟨[82857, 1], [82857, 1], .contexts []⟩,
    ⟨[15629, 82853], [15629, 82853], .contexts [
        ⟨17528, false, false, [15629], []⟩
      ]⟩,
    ⟨[15629, 82853], [15629, 82853], .contexts [
        ⟨13, true, false, [], [15629, 82853]⟩
      ]⟩,
    ⟨[82857, 1], [15629, 82853], .contexts [
        ⟨17572, false, false, [], []⟩,
        ⟨17567, true, false, [], [1]⟩,
        ⟨161, false, false, [78125], []⟩,
        ⟨162, false, false, [78125], []⟩,
        ⟨17420, false, false, [], [5]⟩,
        ⟨17568, false, false, [], [5]⟩,
        ⟨17569, false, false, [], [5]⟩,
        ⟨17569, false, false, [], [5]⟩,
        ⟨17521, false, false, [15629], []⟩,
        ⟨17570, false, false, [], []⟩,
        ⟨17571, false, false, [], []⟩,
        ⟨17573, false, false, [], []⟩,
        ⟨17574, false, false, [], []⟩
      ]⟩,
    ⟨[15627], [15628], .contexts [
        ⟨17418, true, true, [], []⟩
      ]⟩,
    ⟨[82853, 1], [15627, 82857], .contexts [
        ⟨17575, true, false, [15628], [1]⟩,
        ⟨8, false, false, [15628, 82857], []⟩,
        ⟨17576, true, false, [], [82857]⟩
      ]⟩,
    ⟨[15667], [1275, 537], .source 74665⟩,
    ⟨[15667, 82857], [15667, 82857], .contexts []⟩,
    ⟨[15667, 82857], [15667, 82857], .contexts []⟩,
    ⟨[82857, 7], [82857, 7], .contexts []⟩,
    ⟨[82857], [82857], .contexts []⟩,
    ⟨[82857, 7], [15667, 82857], .contexts [
        ⟨17581, false, false, [], []⟩,
        ⟨17567, true, false, [], [7]⟩,
        ⟨3272, false, false, [78125], []⟩,
        ⟨3275, false, false, [78125], []⟩,
        ⟨3729, false, false, [], [5, 7, 5]⟩,
        ⟨3730, false, false, [], [5, 7, 5]⟩,
        ⟨3228, false, false, [], [5, 7, 5]⟩,
        ⟨3229, false, false, [], [5, 7, 5]⟩,
        ⟨3229, false, false, [], [5, 7, 5]⟩,
        ⟨961, false, false, [539], [7, 5]⟩,
        ⟨3230, true, false, [], [77341, 7, 5]⟩,
        ⟨3731, false, false, [1275], [5]⟩,
        ⟨17578, true, false, [], [78125, 5]⟩,
        ⟨17564, false, false, [15667], []⟩,
        ⟨17579, false, false, [], []⟩,
        ⟨17580, false, false, [], []⟩,
        ⟨17582, false, false, [15667], []⟩
      ]⟩,
    ⟨[15667], [15667], .contexts [
        ⟨13, false, false, [], [15667]⟩
      ]⟩,
    ⟨[82857, 7], [15667, 82857], .contexts [
        ⟨17583, false, false, [], []⟩,
        ⟨17584, true, false, [], [82857]⟩
      ]⟩,
    ⟨[78125, 13], [1389, 78125], .source 74666⟩,
    ⟨[1389, 82857], [1389, 82857], .source 74667⟩,
    ⟨[1389, 82857], [1389, 82857], .source 74668⟩,
    ⟨[82857, 13], [82857, 13], .source 74669⟩,
    ⟨[82857, 13], [1389, 82857], .contexts [
        ⟨17589, false, false, [], []⟩,
        ⟨17567, true, false, [], [13]⟩,
        ⟨179, false, false, [78125], []⟩,
        ⟨180, false, false, [78125], []⟩,
        ⟨17586, false, false, [], [5]⟩,
        ⟨3738, false, false, [], [5]⟩,
        ⟨17564, false, false, [1389], []⟩,
        ⟨17587, false, false, [], []⟩,
        ⟨17588, false, false, [], []⟩,
        ⟨17582, false, false, [1389], []⟩,
        ⟨3740, true, false, [], [82857]⟩
      ]⟩,
    ⟨[82857, 15], [82857, 15], .source 74670⟩,
    ⟨[82857, 15], [78119], .contexts [
        ⟨17591, false, false, [], []⟩,
        ⟨17567, true, false, [], [15]⟩,
        ⟨184, false, false, [78125], []⟩,
        ⟨185, false, false, [78125], []⟩,
        ⟨3722, false, false, [], [5]⟩,
        ⟨3334, false, false, [], [5]⟩,
        ⟨3335, false, false, [], [5]⟩,
        ⟨3335, false, false, [], [5]⟩,
        ⟨3681, false, false, [], []⟩,
        ⟨3682, false, false, [], []⟩,
        ⟨3683, false, false, [], []⟩,
        ⟨3683, false, false, [], []⟩,
        ⟨3889, false, false, [], []⟩,
        ⟨3890, false, false, [], []⟩
      ]⟩,
    ⟨[78119, 15], [82857], .contexts [
        ⟨17592, true, false, [], [15]⟩,
        ⟨1, false, false, [82857], []⟩,
        ⟨17566, false, false, [], []⟩
      ]⟩,
    ⟨[78009, 5], [82859], .source 74672⟩,
    ⟨[78009, 5], [82859], .contexts [
        ⟨17594, false, false, [], []⟩
      ]⟩,
    ⟨[82859], [82859], .source 74673⟩,
    ⟨[82859], [82859], .source 74674⟩,
    ⟨[78009, 5], [82859], .contexts [
        ⟨17595, false, false, [], []⟩,
        ⟨17596, false, false, [], []⟩,
        ⟨17597, false, false, [], []⟩,
        ⟨17597, false, false, [], []⟩
      ]⟩,
    ⟨[15669], [539, 267], .source 7899⟩]

/-- Exact literal claimed equations and contextual derivations, block 275. -/
def y322TCIndexRaw275 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15671], [15669, 537], .source 7900⟩,
    ⟨[15671, 82859], [15671, 82859], .contexts []⟩,
    ⟨[82859], [82859], .contexts []⟩,
    ⟨[82859, 7], [15671, 82859], .contexts [
        ⟨17598, true, false, [], [7]⟩,
        ⟨3272, false, false, [78009], []⟩,
        ⟨3275, false, false, [78009], []⟩,
        ⟨3403, false, false, [], [5, 7, 5]⟩,
        ⟨3405, false, false, [], [5, 7, 5]⟩,
        ⟨3401, false, false, [], [5, 7, 5]⟩,
        ⟨3402, false, false, [], [5, 7, 5]⟩,
        ⟨3402, false, false, [], [5, 7, 5]⟩,
        ⟨941, false, false, [539], [7, 5]⟩,
        ⟨17599, true, false, [], [77343, 7, 5]⟩,
        ⟨3406, false, false, [15669], [5]⟩,
        ⟨17600, true, false, [], [78009, 5]⟩,
        ⟨17594, false, false, [15671], []⟩,
        ⟨17601, false, false, [], []⟩,
        ⟨17602, false, false, [15671], []⟩
      ]⟩,
    ⟨[82859, 9], [82857], .contexts [
        ⟨17598, true, false, [], [9]⟩,
        ⟨1265, false, false, [78009], []⟩,
        ⟨1266, false, false, [78009], []⟩,
        ⟨3733, false, false, [], [5]⟩,
        ⟨3724, false, false, [], [5]⟩,
        ⟨3725, false, false, [], [5]⟩,
        ⟨3725, false, false, [], [5]⟩,
        ⟨17564, false, false, [], []⟩,
        ⟨17565, false, false, [], []⟩,
        ⟨17566, false, false, [], []⟩,
        ⟨17566, false, false, [], []⟩,
        ⟨17582, false, false, [], []⟩,
        ⟨672, true, false, [], [82857]⟩
      ]⟩,
    ⟨[82857, 9], [82859], .contexts [
        ⟨17604, true, false, [], [9]⟩,
        ⟨46, false, false, [82859], []⟩,
        ⟨17597, false, false, [], []⟩
      ]⟩,
    ⟨[1309, 82859], [1309, 82859], .contexts []⟩,
    ⟨[82859, 13], [1309, 82859], .contexts [
        ⟨17598, true, false, [], [13]⟩,
        ⟨179, false, false, [78009], []⟩,
        ⟨180, false, false, [78009], []⟩,
        ⟨3411, false, false, [], [5]⟩,
        ⟨3413, false, false, [], [5]⟩,
        ⟨3409, false, false, [], [5]⟩,
        ⟨3410, false, false, [], [5]⟩,
        ⟨3410, false, false, [], [5]⟩,
        ⟨17594, false, false, [1309], []⟩,
        ⟨17606, false, false, [], []⟩,
        ⟨17602, false, false, [1309], []⟩,
        ⟨3412, true, false, [], [82859]⟩
      ]⟩,
    ⟨[78009, 15], [77991], .source 74675⟩,
    ⟨[82859, 15], [78001], .contexts [
        ⟨17598, true, false, [], [15]⟩,
        ⟨184, false, false, [78009], []⟩,
        ⟨185, false, false, [78009], []⟩,
        ⟨17608, false, false, [], [5]⟩,
        ⟨3319, false, false, [], []⟩,
        ⟨3320, false, false, [], []⟩,
        ⟨3321, false, false, [], []⟩,
        ⟨3321, false, false, [], []⟩,
        ⟨3689, false, false, [], []⟩,
        ⟨3690, false, false, [], []⟩
      ]⟩,
    ⟨[78001, 15], [82859], .contexts [
        ⟨17609, true, false, [], [15]⟩,
        ⟨1, false, false, [82859], []⟩,
        ⟨17597, false, false, [], []⟩
      ]⟩,
    ⟨[78009, 11], [82861], .source 74677⟩,
    ⟨[82861, 11], [78009], .contexts [
        ⟨17611, true, false, [], [11]⟩,
        ⟨53, false, false, [78009], []⟩,
        ⟨3391, false, false, [], []⟩
      ]⟩,
    ⟨[82861], [82861], .source 74678⟩,
    ⟨[82861], [82861], .source 74679⟩,
    ⟨[78009, 11], [82861], .source 74680⟩,
    ⟨[323, 82861], [323, 82861], .contexts []⟩,
    ⟨[323, 82861], [323, 82861], .contexts []⟩,
    ⟨[82861, 3], [82861, 3], .contexts []⟩,
    ⟨[82861], [82861], .source 74681⟩,
    ⟨[82861, 3], [323, 82861], .contexts [
        ⟨17618, false, false, [], []⟩,
        ⟨17615, true, false, [], [3]⟩,
        ⟨215, false, false, [78009], []⟩,
        ⟨216, false, false, [78009], []⟩,
        ⟨3398, false, false, [], [11]⟩,
        ⟨3400, false, false, [], [11]⟩,
        ⟨3396, false, false, [], [11]⟩,
        ⟨3397, false, false, [], [11]⟩,
        ⟨3397, false, false, [], [11]⟩,
        ⟨17611, false, false, [323], []⟩,
        ⟨17616, false, false, [], []⟩,
        ⟨17617, false, false, [], []⟩,
        ⟨17619, false, false, [323], []⟩,
        ⟨3220, true, false, [], [82861]⟩
      ]⟩,
    ⟨[539, 77345], [539, 77345], .source 74682⟩,
    ⟨[539, 77345], [539, 77345], .source 74683⟩,
    ⟨[82861, 7], [82861, 7], .source 74684⟩,
    ⟨[82861, 7], [539, 77345], .source 74686⟩,
    ⟨[77345, 7], [537, 82861], .source 74687⟩,
    ⟨[1309, 82861], [1309, 82861], .source 74688⟩,
    ⟨[82861, 13], [1309, 82861], .source 74691⟩,
    ⟨[82861, 15], [78005], .source 74692⟩,
    ⟨[78005, 15], [82861], .contexts [
        ⟨17628, true, false, [], [15]⟩,
        ⟨1, false, false, [82861], []⟩,
        ⟨17614, false, false, [], []⟩
      ]⟩,
    ⟨[77347, 7], [82863], .source 74694⟩,
    ⟨[82863, 7], [77347], .contexts [
        ⟨17630, true, false, [], [7]⟩,
        ⟨38, false, false, [77347], []⟩,
        ⟨821, false, false, [], []⟩
      ]⟩,
    ⟨[82863], [82863], .contexts []⟩,
    ⟨[82863], [82863], .source 74695⟩,
    ⟨[77347, 7], [82863], .source 74696⟩,
    ⟨[537, 82861], [537, 82861], .source 74697⟩,
    ⟨[82863, 1], [537, 82861], .source 74700⟩,
    ⟨[82861, 1], [539, 82863], .source 74701⟩,
    ⟨[82863, 3], [15673, 77857], .source 74706⟩,
    ⟨[77857, 3], [15675, 82863], .source 74708⟩,
    ⟨[271, 82863], [271, 82863], .source 74710⟩,
    ⟨[271, 82863], [271, 82863], .source 74711⟩,
    ⟨[82863, 9], [82863, 9], .source 74712⟩,
    ⟨[271], [271], .source 74713⟩,
    ⟨[82863, 9], [271, 82863], .source 74714⟩,
    ⟨[82863, 11], [82863, 11], .source 74715⟩,
    ⟨[82863, 11], [77853], .source 74718⟩,
    ⟨[503, 77985], [503, 77985], .contexts []⟩,
    ⟨[503, 77985], [503, 77985], .source 74719⟩,
    ⟨[503, 77999], [503, 77999], .contexts []⟩,
    ⟨[503, 77999], [503, 77999], .contexts []⟩,
    ⟨[82863, 15], [82863, 15], .contexts []⟩,
    ⟨[82863, 15], [503, 77999], .contexts [
        ⟨17651, false, false, [], []⟩,
        ⟨17634, true, false, [], [15]⟩,
        ⟨1063, false, false, [77347], []⟩,
        ⟨1064, false, false, [77347], []⟩,
        ⟨3117, false, false, [], [7]⟩,
        ⟨17647, false, false, [], [7]⟩,
        ⟨17648, false, false, [], [7]⟩,
        ⟨17648, false, false, [], [7]⟩,
        ⟨3304, false, false, [503], []⟩,
        ⟨17649, false, false, [], []⟩,
        ⟨17650, false, false, [], []⟩,
        ⟨3310, false, false, [503], []⟩,
        ⟨1599, true, false, [], [77999]⟩
      ]⟩,
    ⟨[77999, 15], [505, 82863], .contexts [
        ⟨17652, true, false, [502], [15]⟩,
        ⟨1, false, false, [502, 82863], []⟩,
        ⟨1601, true, false, [], [82863]⟩
      ]⟩,
    ⟨[82861, 5], [82865], .source 74721⟩,
    ⟨[82865, 5], [82861], .contexts [
        ⟨17654, true, false, [], [5]⟩,
        ⟨28, false, false, [82861], []⟩,
        ⟨17614, false, false, [], []⟩
      ]⟩,
    ⟨[82861, 5], [82865], .source 74722⟩,
    ⟨[82865], [82865], .source 74723⟩,
    ⟨[82865], [82865], .source 74724⟩,
    ⟨[82861, 5], [82865], .source 74725⟩,
    ⟨[82865], [82865], .source 74726⟩,
    ⟨[82865, 7], [15667, 82865], .source 74727⟩,
    ⟨[82859], [82859], .contexts [
        ⟨17602, false, false, [], []⟩
      ]⟩,
    ⟨[82859], [82859], .contexts [
        ⟨672, true, false, [], [82859]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 276. -/
def y322TCIndexRaw276 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82865, 11], [82859], .contexts [
        ⟨17659, true, false, [], [11]⟩,
        ⟨174, false, false, [82861], []⟩,
        ⟨175, false, false, [82861], []⟩,
        ⟨17612, false, false, [], [5]⟩,
        ⟨3390, false, false, [], [5]⟩,
        ⟨3391, false, false, [], [5]⟩,
        ⟨3391, false, false, [], [5]⟩,
        ⟨17595, false, false, [], []⟩,
        ⟨17596, false, false, [], []⟩,
        ⟨17597, false, false, [], []⟩,
        ⟨17597, false, false, [], []⟩,
        ⟨17662, false, false, [], []⟩,
        ⟨17663, false, false, [], []⟩
      ]⟩,
    ⟨[82861, 13], [1309, 82861], .source 74728⟩,
    ⟨[1309, 82865], [1309, 82865], .contexts []⟩,
    ⟨[82865, 13], [1309, 82865], .contexts [
        ⟨17659, true, false, [], [13]⟩,
        ⟨179, false, false, [82861], []⟩,
        ⟨180, false, false, [82861], []⟩,
        ⟨17665, false, false, [], [5]⟩,
        ⟨17654, false, false, [1309], []⟩,
        ⟨17666, false, false, [], []⟩,
        ⟨17660, false, false, [1309], []⟩,
        ⟨3412, true, false, [], [82865]⟩
      ]⟩,
    ⟨[82861, 9], [82867], .source 74730⟩,
    ⟨[82867, 9], [82861], .contexts [
        ⟨17668, true, false, [], [9]⟩,
        ⟨46, false, false, [82861], []⟩,
        ⟨17614, false, false, [], []⟩
      ]⟩,
    ⟨[82861, 9], [82867], .source 74731⟩,
    ⟨[82867], [82867], .source 74732⟩,
    ⟨[82867], [82867], .source 74733⟩,
    ⟨[82861, 9], [82867], .source 74734⟩,
    ⟨[82867], [82867], .source 74738⟩,
    ⟨[82867, 1], [15679, 82867], .source 74739⟩,
    ⟨[82867, 1], [15679, 82867], .contexts [
        ⟨17675, false, false, [], []⟩,
        ⟨13, true, false, [], [15679, 82867]⟩
      ]⟩,
    ⟨[323, 82867], [323, 82867], .contexts []⟩,
    ⟨[82867, 3], [323, 82867], .contexts [
        ⟨17673, true, false, [], [3]⟩,
        ⟨196, false, false, [82861], []⟩,
        ⟨197, false, false, [82861], []⟩,
        ⟨17618, false, false, [], [9]⟩,
        ⟨17620, false, false, [], [9]⟩,
        ⟨17616, false, false, [], [9]⟩,
        ⟨17617, false, false, [], [9]⟩,
        ⟨17617, false, false, [], [9]⟩,
        ⟨17668, false, false, [323], []⟩,
        ⟨17677, false, false, [], []⟩,
        ⟨17674, false, false, [323], []⟩,
        ⟨3220, true, false, [], [82867]⟩
      ]⟩,
    ⟨[15681], [539, 1181], .source 7905⟩,
    ⟨[82867, 7], [15681, 77973], .contexts [
        ⟨17673, true, false, [], [7]⟩,
        ⟨1084, false, false, [82861], []⟩,
        ⟨1085, false, false, [82861], []⟩,
        ⟨17623, false, false, [], [9]⟩,
        ⟨17624, false, false, [], [9]⟩,
        ⟨17621, false, false, [], [9]⟩,
        ⟨17622, false, false, [], [9]⟩,
        ⟨17622, false, false, [], [9]⟩,
        ⟨3002, false, false, [539], []⟩,
        ⟨3030, false, false, [539, 1119], []⟩,
        ⟨3031, true, false, [539], [77973]⟩,
        ⟨17679, true, false, [], [77973]⟩,
        ⟨3032, false, false, [15681], []⟩,
        ⟨13, true, false, [], [15681, 77973]⟩
      ]⟩,
    ⟨[15683], [15680], .source 7906⟩,
    ⟨[77973, 7], [15683, 82867], .contexts [
        ⟨17680, true, false, [15680], [7]⟩,
        ⟨38, false, false, [15680, 82867], []⟩,
        ⟨17681, true, false, [], [82867]⟩
      ]⟩,
    ⟨[1309, 82867], [1309, 82867], .contexts []⟩,
    ⟨[82863, 5], [82869], .source 74741⟩,
    ⟨[82869, 5], [82863], .contexts [
        ⟨17684, true, false, [], [5]⟩,
        ⟨28, false, false, [82863], []⟩,
        ⟨17633, false, false, [], []⟩
      ]⟩,
    ⟨[82869], [82869], .contexts []⟩,
    ⟨[82869], [82869], .source 74742⟩,
    ⟨[82863, 5], [82869], .source 74743⟩,
    ⟨[82863, 1], [537, 82861], .source 74744⟩,
    ⟨[82869, 1], [537, 82865], .source 74745⟩,
    ⟨[82865, 1], [539, 82869], .contexts [
        ⟨17690, true, false, [536], [1]⟩,
        ⟨8, false, false, [536, 82869], []⟩,
        ⟨1668, true, false, [], [82869]⟩
      ]⟩,
    ⟨[82863, 3], [15673, 77857], .source 74747⟩,
    ⟨[15685], [15673, 759], .source 74748⟩,
    ⟨[15687], [15685, 15675], .source 74749⟩,
    ⟨[15687, 82869], [15687, 82869], .contexts []⟩,
    ⟨[82869], [82869], .source 74750⟩,
    ⟨[82869, 3], [15687, 82869], .contexts [
        ⟨17688, true, false, [], [3]⟩,
        ⟨166, false, false, [82863], []⟩,
        ⟨169, false, false, [82863], []⟩,
        ⟨17692, false, false, [], [5, 3, 5]⟩,
        ⟨2818, false, false, [15673], [3, 5]⟩,
        ⟨17693, true, false, [], [77857, 3, 5]⟩,
        ⟨17639, false, false, [15685], [5]⟩,
        ⟨17694, true, false, [], [82863, 5]⟩,
        ⟨17684, false, false, [15687], []⟩,
        ⟨17695, false, false, [], []⟩,
        ⟨17696, false, false, [15687], []⟩,
        ⟨13, true, false, [], [15687, 82869]⟩
      ]⟩,
    ⟨[82863, 7], [77347], .contexts [
        ⟨17631, false, false, [], []⟩,
        ⟨829, false, false, [], []⟩,
        ⟨821, false, false, [], []⟩,
        ⟨821, false, false, [], []⟩
      ]⟩,
    ⟨[267, 82869], [267, 82869], .contexts []⟩,
    ⟨[271, 82869], [271, 82869], .contexts []⟩,
    ⟨[82869, 9], [271, 82869], .contexts [
        ⟨17688, true, false, [], [9]⟩,
        ⟨1265, false, false, [82863], []⟩,
        ⟨1266, false, false, [82863], []⟩,
        ⟨17642, false, false, [], [5]⟩,
        ⟨17644, false, false, [], [5]⟩,
        ⟨17640, false, false, [], [5]⟩,
        ⟨17641, false, false, [], [5]⟩,
        ⟨17641, false, false, [], [5]⟩,
        ⟨17684, false, false, [271], []⟩,
        ⟨17700, false, false, [], []⟩,
        ⟨17696, false, false, [271], []⟩,
        ⟨17643, true, false, [], [82869]⟩
      ]⟩,
    ⟨[82863, 13], [82871], .source 74752⟩,
    ⟨[82871, 13], [82863], .contexts [
        ⟨17702, true, false, [], [13]⟩,
        ⟨59, false, false, [82863], []⟩,
        ⟨17633, false, false, [], []⟩
      ]⟩,
    ⟨[82871], [82871], .source 74753⟩,
    ⟨[82871], [82871], .source 74754⟩,
    ⟨[82863, 13], [82871], .source 74755⟩,
    ⟨[15689], [537, 1309], .source 74756⟩,
    ⟨[15691], [15689, 539], .source 74757⟩,
    ⟨[15691, 82871], [15691, 82871], .source 74758⟩,
    ⟨[15691, 82871], [15691, 82871], .source 74759⟩,
    ⟨[82871, 1], [82871, 1], .source 74760⟩,
    ⟨[82871], [82871], .source 74761⟩,
    ⟨[15691], [15691], .source 74762⟩,
    ⟨[82871, 1], [15691, 82871], .contexts [
        ⟨17711, false, false, [], []⟩,
        ⟨17706, true, false, [], [1]⟩,
        ⟨246, false, false, [82863], []⟩,
        ⟨249, false, false, [82863], []⟩,
        ⟨17689, false, false, [], [13, 1, 13]⟩,
        ⟨17627, false, false, [537], [1, 13]⟩,
        ⟨17707, true, false, [], [82861, 1, 13]⟩,
        ⟨17637, false, false, [15689], [13]⟩,
        ⟨17708, true, false, [], [82863, 13]⟩,
        ⟨17702, false, false, [15691], []⟩,
        ⟨17709, false, false, [], []⟩,
        ⟨17710, false, false, [], []⟩,
        ⟨17712, false, false, [15691], []⟩,
        ⟨17713, true, false, [], [82871]⟩
      ]⟩,
    ⟨[82871, 3], [15693, 77479], .source 74764⟩,
    ⟨[15695], [15692], .source 7912⟩,
    ⟨[77479, 3], [15695, 82871], .contexts [
        ⟨17715, true, false, [15692], [3]⟩,
        ⟨20, false, false, [15692, 82871], []⟩,
        ⟨17716, true, false, [], [82871]⟩
      ]⟩,
    ⟨[82871, 7], [82871, 7], .contexts []⟩,
    ⟨[82871, 7], [77349], .contexts [
        ⟨17718, false, false, [], []⟩,
        ⟨17706, true, false, [], [7]⟩,
        ⟨73, false, false, [82863], []⟩,
        ⟨74, false, false, [82863], []⟩,
        ⟨17698, false, false, [], [13]⟩,
        ⟨820, false, false, [], []⟩,
        ⟨828, false, false, [], []⟩,
        ⟨824, false, false, [], []⟩,
        ⟨824, false, false, [], []⟩,
        ⟨672, true, false, [], [77349]⟩
      ]⟩,
    ⟨[77349, 7], [82871], .contexts [
        ⟨17719, true, false, [], [7]⟩,
        ⟨38, false, false, [82871], []⟩,
        ⟨17705, false, false, [], []⟩
      ]⟩,
    ⟨[271, 82871], [271, 82871], .source 74765⟩,
    ⟨[271, 82871], [271, 82871], .source 74766⟩,
    ⟨[82871, 9], [82871, 9], .source 74767⟩,
    ⟨[82871, 9], [271, 82871], .source 74768⟩,
    ⟨[82871, 11], [77713], .contexts [
        ⟨17706, true, false, [], [11]⟩,
        ⟨82, false, false, [82863], []⟩,
        ⟨83, false, false, [82863], []⟩,
        ⟨17645, false, false, [], [13]⟩,
        ⟨17646, false, false, [], [13]⟩,
        ⟨2782, false, false, [], [13]⟩,
        ⟨2783, false, false, [], [13]⟩,
        ⟨2783, false, false, [], [13]⟩,
        ⟨2789, false, false, [], []⟩,
        ⟨2323, false, false, [], []⟩,
        ⟨2324, false, false, [], []⟩,
        ⟨2324, false, false, [], []⟩,
        ⟨2787, false, false, [], []⟩,
        ⟨2788, false, false, [], []⟩
      ]⟩,
    ⟨[77713, 11], [82871], .contexts [
        ⟨17725, true, false, [], [11]⟩,
        ⟨53, false, false, [82871], []⟩,
        ⟨17705, false, false, [], []⟩
      ]⟩,
    ⟨[15697], [503, 31], .source 7913⟩]

/-- Exact literal claimed equations and contextual derivations, block 277. -/
def y322TCIndexRaw277 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15699], [15697, 505], .source 7914⟩,
    ⟨[15699, 82871], [15699, 82871], .contexts []⟩,
    ⟨[15699, 82871], [15699, 82871], .contexts []⟩,
    ⟨[82871, 15], [82871, 15], .contexts []⟩,
    ⟨[82871, 15], [15699, 82871], .contexts [
        ⟨17731, false, false, [], []⟩,
        ⟨17706, true, false, [], [15]⟩,
        ⟨88, false, false, [82863], []⟩,
        ⟨91, false, false, [82863], []⟩,
        ⟨17651, false, false, [], [13, 15, 13]⟩,
        ⟨17652, false, false, [], [13, 15, 13]⟩,
        ⟨17649, false, false, [], [13, 15, 13]⟩,
        ⟨17650, false, false, [], [13, 15, 13]⟩,
        ⟨17650, false, false, [], [13, 15, 13]⟩,
        ⟨3316, false, false, [503], [15, 13]⟩,
        ⟨443, true, false, [503], [77999, 15, 13]⟩,
        ⟨17727, true, false, [], [77999, 15, 13]⟩,
        ⟨17653, false, false, [15697], [13]⟩,
        ⟨17728, true, false, [], [82863, 13]⟩,
        ⟨17702, false, false, [15699], []⟩,
        ⟨17729, false, false, [], []⟩,
        ⟨17730, false, false, [], []⟩,
        ⟨17712, false, false, [15699], []⟩
      ]⟩,
    ⟨[15699], [15699], .contexts [
        ⟨13, false, false, [], [15699]⟩
      ]⟩,
    ⟨[82871, 15], [15699, 82871], .contexts [
        ⟨17732, false, false, [], []⟩,
        ⟨17733, true, false, [], [82871]⟩
      ]⟩,
    ⟨[82871, 5], [82873], .source 74770⟩,
    ⟨[82873, 5], [82871], .source 74771⟩,
    ⟨[82873], [82873], .contexts []⟩,
    ⟨[82873], [82873], .source 74772⟩,
    ⟨[82871, 5], [82873], .source 74773⟩,
    ⟨[15691, 82873], [15691, 82873], .source 74775⟩,
    ⟨[15691, 82873], [15691, 82873], .source 74776⟩,
    ⟨[82873, 1], [82873, 1], .source 74777⟩,
    ⟨[82873], [82873], .source 74778⟩,
    ⟨[82873, 1], [15691, 82873], .source 74779⟩,
    ⟨[15693, 77479], [15693, 77479], .contexts []⟩,
    ⟨[15693, 77479], [15693, 77479], .contexts []⟩,
    ⟨[15701], [15693, 475], .source 7915⟩,
    ⟨[15703], [15701, 15695], .source 7916⟩,
    ⟨[15703, 82873], [15703, 82873], .contexts []⟩,
    ⟨[15703, 82873], [15703, 82873], .contexts []⟩,
    ⟨[82873, 3], [82873, 3], .contexts []⟩,
    ⟨[82873, 3], [15703, 82873], .contexts [
        ⟨17751, false, false, [], []⟩,
        ⟨17739, true, false, [], [3]⟩,
        ⟨166, false, false, [82871], []⟩,
        ⟨169, false, false, [82871], []⟩,
        ⟨17715, false, false, [], [5, 3, 5]⟩,
        ⟨17745, false, false, [], [5, 3, 5]⟩,
        ⟨17746, false, false, [], [5, 3, 5]⟩,
        ⟨17746, false, false, [], [5, 3, 5]⟩,
        ⟨1532, false, false, [15693], [3, 5]⟩,
        ⟨17747, true, false, [], [77479, 3, 5]⟩,
        ⟨17717, false, false, [15701], [5]⟩,
        ⟨17748, true, false, [], [82871, 5]⟩,
        ⟨17735, false, false, [15703], []⟩,
        ⟨17749, false, false, [], []⟩,
        ⟨17750, false, false, [], []⟩,
        ⟨17743, false, false, [15703], []⟩
      ]⟩,
    ⟨[15703], [15703], .contexts [
        ⟨13, false, false, [], [15703]⟩
      ]⟩,
    ⟨[82873, 3], [15703, 82873], .contexts [
        ⟨17752, false, false, [], []⟩,
        ⟨17753, true, false, [], [82873]⟩
      ]⟩,
    ⟨[261, 82873], [261, 82873], .contexts []⟩,
    ⟨[261, 82873], [261, 82873], .contexts []⟩,
    ⟨[82873, 7], [82873, 7], .contexts []⟩,
    ⟨[82873, 7], [261, 82873], .contexts [
        ⟨17757, false, false, [], []⟩,
        ⟨17739, true, false, [], [7]⟩,
        ⟨3272, false, false, [82871], []⟩,
        ⟨3275, false, false, [82871], []⟩,
        ⟨17718, false, false, [], [5, 7, 5]⟩,
        ⟨17719, false, false, [], [5, 7, 5]⟩,
        ⟨828, false, false, [], [5, 7, 5]⟩,
        ⟨824, false, false, [], [5, 7, 5]⟩,
        ⟨824, false, false, [], [5, 7, 5]⟩,
        ⟨907, false, false, [], [7, 5]⟩,
        ⟨909, false, false, [], [7, 5]⟩,
        ⟨910, false, false, [], [7, 5]⟩,
        ⟨910, false, false, [], [7, 5]⟩,
        ⟨17720, false, false, [261], [5]⟩,
        ⟨17735, false, false, [261], []⟩,
        ⟨17755, false, false, [], []⟩,
        ⟨17756, false, false, [], []⟩,
        ⟨17743, false, false, [261], []⟩
      ]⟩,
    ⟨[82873, 7], [261, 82873], .contexts [
        ⟨17758, false, false, [], []⟩,
        ⟨1604, true, false, [], [82873]⟩
      ]⟩,
    ⟨[271, 82873], [271, 82873], .contexts []⟩,
    ⟨[82869], [82869], .contexts [
        ⟨17696, false, false, [], []⟩
      ]⟩,
    ⟨[82869], [82869], .contexts [
        ⟨672, true, false, [], [82869]⟩
      ]⟩,
    ⟨[82873, 13], [82869], .contexts [
        ⟨17739, true, false, [], [13]⟩,
        ⟨179, false, false, [82871], []⟩,
        ⟨180, false, false, [82871], []⟩,
        ⟨17703, false, false, [], [5]⟩,
        ⟨17632, false, false, [], [5]⟩,
        ⟨17633, false, false, [], [5]⟩,
        ⟨17633, false, false, [], [5]⟩,
        ⟨17684, false, false, [], []⟩,
        ⟨17686, false, false, [], []⟩,
        ⟨17687, false, false, [], []⟩,
        ⟨17687, false, false, [], []⟩,
        ⟨17761, false, false, [], []⟩,
        ⟨17762, false, false, [], []⟩
      ]⟩,
    ⟨[82869, 13], [82873], .contexts [
        ⟨17763, true, false, [], [13]⟩,
        ⟨59, false, false, [82873], []⟩,
        ⟨17738, false, false, [], []⟩
      ]⟩,
    ⟨[15699, 82873], [15699, 82873], .contexts []⟩,
    ⟨[15699, 82873], [15699, 82873], .contexts []⟩,
    ⟨[82873, 15], [82873, 15], .contexts []⟩,
    ⟨[82873, 15], [15699, 82873], .contexts [
        ⟨17767, false, false, [], []⟩,
        ⟨17739, true, false, [], [15]⟩,
        ⟨184, false, false, [82871], []⟩,
        ⟨185, false, false, [82871], []⟩,
        ⟨17731, false, false, [], [5]⟩,
        ⟨17734, false, false, [], [5]⟩,
        ⟨17729, false, false, [], [5]⟩,
        ⟨17730, false, false, [], [5]⟩,
        ⟨17730, false, false, [], [5]⟩,
        ⟨17735, false, false, [15699], []⟩,
        ⟨17765, false, false, [], []⟩,
        ⟨17766, false, false, [], []⟩,
        ⟨17743, false, false, [15699], []⟩,
        ⟨17733, true, false, [], [82873]⟩
      ]⟩,
    ⟨[82875], [78739, 3], .source 41502⟩,
    ⟨[78739, 3], [82875], .contexts [
        ⟨17769, true, false, [], []⟩
      ]⟩,
    ⟨[82875, 3], [78739], .contexts [
        ⟨17770, true, false, [], [3]⟩,
        ⟨20, false, false, [78739], []⟩,
        ⟨4937, false, false, [], []⟩
      ]⟩,
    ⟨[78739, 3], [82875], .contexts [
        ⟨17770, false, false, [], []⟩
      ]⟩,
    ⟨[82875], [82875], .contexts []⟩,
    ⟨[82875], [82875], .contexts []⟩,
    ⟨[78739, 3], [82875], .contexts [
        ⟨17772, false, false, [], []⟩,
        ⟨17773, false, false, [], []⟩,
        ⟨17774, false, false, [], []⟩,
        ⟨17774, false, false, [], []⟩
      ]⟩,
    ⟨[78739, 7], [317, 78739], .contexts [
        ⟨4949, false, false, [], []⟩,
        ⟨4951, false, false, [], []⟩,
        ⟨4947, false, false, [], []⟩,
        ⟨4948, false, false, [], []⟩,
        ⟨4948, false, false, [], []⟩
      ]⟩,
    ⟨[317, 82875], [317, 82875], .contexts []⟩,
    ⟨[317, 82875], [317, 82875], .contexts []⟩,
    ⟨[82875, 7], [82875, 7], .contexts []⟩,
    ⟨[82875], [82875], .contexts []⟩,
    ⟨[82875, 7], [317, 82875], .contexts [
        ⟨17779, false, false, [], []⟩,
        ⟨17775, true, false, [], [7]⟩,
        ⟨140, false, false, [78739], []⟩,
        ⟨141, false, false, [78739], []⟩,
        ⟨17776, false, false, [], [3]⟩,
        ⟨17770, false, false, [317], []⟩,
        ⟨17777, false, false, [], []⟩,
        ⟨17778, false, false, [], []⟩,
        ⟨17780, false, false, [317], []⟩,
        ⟨1182, true, false, [], [82875]⟩
      ]⟩,
    ⟨[78739, 13], [1075, 78739], .contexts [
        ⟨4955, false, false, [], []⟩,
        ⟨4956, false, false, [], []⟩,
        ⟨4953, false, false, [], []⟩,
        ⟨4954, false, false, [], []⟩,
        ⟨4954, false, false, [], []⟩
      ]⟩,
    ⟨[1075, 82875], [1075, 82875], .contexts []⟩,
    ⟨[1075, 82875], [1075, 82875], .contexts []⟩,
    ⟨[82875, 13], [82875, 13], .contexts []⟩,
    ⟨[82875, 13], [1075, 82875], .contexts [
        ⟨17785, false, false, [], []⟩,
        ⟨17775, true, false, [], [13]⟩,
        ⟨147, false, false, [78739], []⟩,
        ⟨148, false, false, [78739], []⟩,
        ⟨17782, false, false, [], [3]⟩,
        ⟨17770, false, false, [1075], []⟩,
        ⟨17783, false, false, [], []⟩,
        ⟨17784, false, false, [], []⟩,
        ⟨17780, false, false, [1075], []⟩,
        ⟨4778, true, false, [], [82875]⟩
      ]⟩,
    ⟨[82877], [82875, 5], .source 41503⟩,
    ⟨[82875, 5], [82877], .contexts [
        ⟨17787, true, false, [], []⟩
      ]⟩,
    ⟨[82877, 5], [82875], .contexts [
        ⟨17788, true, false, [], [5]⟩,
        ⟨28, false, false, [82875], []⟩,
        ⟨17774, false, false, [], []⟩
      ]⟩,
    ⟨[82875, 5], [82877], .contexts [
        ⟨17788, false, false, [], []⟩
      ]⟩,
    ⟨[82877], [82877], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 278. -/
def y322TCIndexRaw278 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82877], [82877], .contexts []⟩,
    ⟨[82875, 5], [82877], .contexts [
        ⟨17790, false, false, [], []⟩,
        ⟨17791, false, false, [], []⟩,
        ⟨17792, false, false, [], []⟩,
        ⟨17792, false, false, [], []⟩
      ]⟩,
    ⟨[82875, 3], [78739], .contexts [
        ⟨17771, false, false, [], []⟩
      ]⟩,
    ⟨[82875, 3], [78739], .contexts [
        ⟨17794, false, false, [], []⟩,
        ⟨4936, false, false, [], []⟩,
        ⟨4937, false, false, [], []⟩,
        ⟨4937, false, false, [], []⟩
      ]⟩,
    ⟨[78739, 5], [78721], .contexts [
        ⟨4934, false, false, [], []⟩
      ]⟩,
    ⟨[82877, 3], [78833], .contexts [
        ⟨17793, true, false, [], [3]⟩,
        ⟨166, false, false, [82875], []⟩,
        ⟨169, false, false, [82875], []⟩,
        ⟨17795, false, false, [], [5, 3, 5]⟩,
        ⟨17796, false, false, [], [3, 5]⟩,
        ⟨4764, false, false, [], [3, 5]⟩,
        ⟨4765, false, false, [], [3, 5]⟩,
        ⟨4765, false, false, [], [3, 5]⟩,
        ⟨4908, false, false, [], [5]⟩,
        ⟨4902, false, false, [], [5]⟩,
        ⟨4903, false, false, [], [5]⟩,
        ⟨4903, false, false, [], [5]⟩,
        ⟨5536, false, false, [], []⟩,
        ⟨5133, false, false, [], []⟩,
        ⟨5134, false, false, [], []⟩,
        ⟨5134, false, false, [], []⟩,
        ⟨5538, false, false, [], []⟩,
        ⟨5539, false, false, [], []⟩
      ]⟩,
    ⟨[78833, 3], [82877], .contexts [
        ⟨17797, true, false, [], [3]⟩,
        ⟨20, false, false, [82877], []⟩,
        ⟨17792, false, false, [], []⟩
      ]⟩,
    ⟨[82875, 13], [1075, 82875], .contexts [
        ⟨17785, false, false, [], []⟩,
        ⟨17786, false, false, [], []⟩,
        ⟨17783, false, false, [], []⟩,
        ⟨17784, false, false, [], []⟩,
        ⟨17784, false, false, [], []⟩
      ]⟩,
    ⟨[1075, 82877], [1075, 82877], .contexts []⟩,
    ⟨[82877], [82877], .contexts []⟩,
    ⟨[82877, 13], [1075, 82877], .contexts [
        ⟨17793, true, false, [], [13]⟩,
        ⟨179, false, false, [82875], []⟩,
        ⟨180, false, false, [82875], []⟩,
        ⟨17799, false, false, [], [5]⟩,
        ⟨17788, false, false, [1075], []⟩,
        ⟨17800, false, false, [], []⟩,
        ⟨17801, false, false, [1075], []⟩,
        ⟨4778, true, false, [], [82877]⟩
      ]⟩,
    ⟨[82879], [82877, 1], .source 41504⟩,
    ⟨[82877, 1], [82879], .contexts [
        ⟨17803, true, false, [], []⟩
      ]⟩,
    ⟨[82879, 1], [82877], .contexts [
        ⟨17804, true, false, [], [1]⟩,
        ⟨8, false, false, [82877], []⟩,
        ⟨17792, false, false, [], []⟩
      ]⟩,
    ⟨[82881], [82879, 9], .source 41505⟩,
    ⟨[82879, 9], [82881], .contexts [
        ⟨17806, true, false, [], []⟩
      ]⟩,
    ⟨[82879], [82879], .contexts []⟩,
    ⟨[82881, 9], [82879], .contexts [
        ⟨17807, true, false, [], [9]⟩,
        ⟨46, false, false, [82879], []⟩,
        ⟨17808, false, false, [], []⟩
      ]⟩,
    ⟨[82883], [82881, 11], .source 41506⟩,
    ⟨[82881, 11], [82883], .contexts [
        ⟨17810, true, false, [], []⟩
      ]⟩,
    ⟨[82881], [82881], .contexts []⟩,
    ⟨[82883, 11], [82881], .contexts [
        ⟨17811, true, false, [], [11]⟩,
        ⟨53, false, false, [82881], []⟩,
        ⟨17812, false, false, [], []⟩
      ]⟩,
    ⟨[82885], [82883, 1], .source 41507⟩,
    ⟨[82883, 1], [82885], .contexts [
        ⟨17814, true, false, [], []⟩
      ]⟩,
    ⟨[82883], [82883], .contexts []⟩,
    ⟨[82885, 1], [82883], .contexts [
        ⟨17815, true, false, [], [1]⟩,
        ⟨8, false, false, [82883], []⟩,
        ⟨17816, false, false, [], []⟩
      ]⟩,
    ⟨[82887], [82885, 13], .source 41508⟩,
    ⟨[82885, 13], [82887], .contexts [
        ⟨17818, true, false, [], []⟩
      ]⟩,
    ⟨[82885], [82885], .contexts []⟩,
    ⟨[82887, 13], [82885], .contexts [
        ⟨17819, true, false, [], [13]⟩,
        ⟨59, false, false, [82885], []⟩,
        ⟨17820, false, false, [], []⟩
      ]⟩,
    ⟨[82889], [82887, 15], .source 41509⟩,
    ⟨[82887, 15], [82889], .contexts [
        ⟨17822, true, false, [], []⟩
      ]⟩,
    ⟨[82887], [82887], .contexts []⟩,
    ⟨[82891], [82889, 1], .source 41510⟩,
    ⟨[82889, 1], [82891], .contexts [
        ⟨17825, true, false, [], []⟩
      ]⟩,
    ⟨[82889], [82889], .contexts []⟩,
    ⟨[82891, 1], [82889], .contexts [
        ⟨17826, true, false, [], [1]⟩,
        ⟨8, false, false, [82889], []⟩,
        ⟨17827, false, false, [], []⟩
      ]⟩,
    ⟨[82893], [82891, 3], .source 41511⟩,
    ⟨[82891, 3], [82893], .contexts [
        ⟨17829, true, false, [], []⟩
      ]⟩,
    ⟨[82891], [82891], .contexts []⟩,
    ⟨[82893, 3], [82891], .contexts [
        ⟨17830, true, false, [], [3]⟩,
        ⟨20, false, false, [82891], []⟩,
        ⟨17831, false, false, [], []⟩
      ]⟩,
    ⟨[82895], [82893, 5], .source 41512⟩,
    ⟨[82893, 5], [82895], .contexts [
        ⟨17833, true, false, [], []⟩
      ]⟩,
    ⟨[82893], [82893], .contexts []⟩,
    ⟨[82895, 5], [82893], .contexts [
        ⟨17834, true, false, [], [5]⟩,
        ⟨28, false, false, [82893], []⟩,
        ⟨17835, false, false, [], []⟩
      ]⟩,
    ⟨[82897], [82895, 1], .source 41513⟩,
    ⟨[82895, 1], [82897], .contexts [
        ⟨17837, true, false, [], []⟩
      ]⟩,
    ⟨[82895], [82895], .contexts []⟩,
    ⟨[82897, 1], [82895], .contexts [
        ⟨17838, true, false, [], [1]⟩,
        ⟨8, false, false, [82895], []⟩,
        ⟨17839, false, false, [], []⟩
      ]⟩,
    ⟨[82899], [82897, 9], .source 41514⟩,
    ⟨[82897, 9], [82899], .contexts [
        ⟨17841, true, false, [], []⟩
      ]⟩,
    ⟨[82897], [82897], .contexts []⟩,
    ⟨[82899, 9], [82897], .contexts [
        ⟨17842, true, false, [], [9]⟩,
        ⟨46, false, false, [82897], []⟩,
        ⟨17843, false, false, [], []⟩
      ]⟩,
    ⟨[82901], [82899, 11], .source 41515⟩,
    ⟨[82899, 11], [82901], .contexts [
        ⟨17845, true, false, [], []⟩
      ]⟩,
    ⟨[82899], [82899], .contexts []⟩,
    ⟨[82901, 11], [82899], .contexts [
        ⟨17846, true, false, [], [11]⟩,
        ⟨53, false, false, [82899], []⟩,
        ⟨17847, false, false, [], []⟩
      ]⟩,
    ⟨[82903], [82901, 1], .source 41516⟩,
    ⟨[82901, 1], [82903], .contexts [
        ⟨17849, true, false, [], []⟩
      ]⟩,
    ⟨[82901], [82901], .contexts []⟩,
    ⟨[82903, 1], [82901], .contexts [
        ⟨17850, true, false, [], [1]⟩,
        ⟨8, false, false, [82901], []⟩,
        ⟨17851, false, false, [], []⟩
      ]⟩,
    ⟨[82905], [82903, 13], .source 41517⟩,
    ⟨[82903, 13], [82905], .contexts [
        ⟨17853, true, false, [], []⟩
      ]⟩,
    ⟨[82903], [82903], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 279. -/
def y322TCIndexRaw279 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82905, 13], [82903], .contexts [
        ⟨17854, true, false, [], [13]⟩,
        ⟨59, false, false, [82903], []⟩,
        ⟨17855, false, false, [], []⟩
      ]⟩,
    ⟨[82907], [82905, 15], .source 41518⟩,
    ⟨[82905, 15], [82907], .contexts [
        ⟨17857, true, false, [], []⟩
      ]⟩,
    ⟨[82905], [82905], .contexts []⟩,
    ⟨[82907, 15], [82905], .contexts [
        ⟨17858, true, false, [], [15]⟩,
        ⟨1, false, false, [82905], []⟩,
        ⟨17859, false, false, [], []⟩
      ]⟩,
    ⟨[82909], [82907, 1], .source 41519⟩,
    ⟨[82907, 1], [82909], .contexts [
        ⟨17861, true, false, [], []⟩
      ]⟩,
    ⟨[82907], [82907], .contexts []⟩,
    ⟨[82909, 1], [82907], .contexts [
        ⟨17862, true, false, [], [1]⟩,
        ⟨8, false, false, [82907], []⟩,
        ⟨17863, false, false, [], []⟩
      ]⟩,
    ⟨[82911], [82909, 3], .source 41520⟩,
    ⟨[82909, 3], [82911], .contexts [
        ⟨17865, true, false, [], []⟩
      ]⟩,
    ⟨[82909], [82909], .contexts []⟩,
    ⟨[82911, 3], [82909], .contexts [
        ⟨17866, true, false, [], [3]⟩,
        ⟨20, false, false, [82909], []⟩,
        ⟨17867, false, false, [], []⟩
      ]⟩,
    ⟨[82913], [82911, 5], .source 41521⟩,
    ⟨[82911, 5], [82913], .contexts [
        ⟨17869, true, false, [], []⟩
      ]⟩,
    ⟨[82911], [82911], .contexts []⟩,
    ⟨[82913, 5], [82911], .contexts [
        ⟨17870, true, false, [], [5]⟩,
        ⟨28, false, false, [82911], []⟩,
        ⟨17871, false, false, [], []⟩
      ]⟩,
    ⟨[82915], [82913, 1], .source 41522⟩,
    ⟨[82913, 1], [82915], .contexts [
        ⟨17873, true, false, [], []⟩
      ]⟩,
    ⟨[82913], [82913], .contexts []⟩,
    ⟨[82915, 1], [82913], .contexts [
        ⟨17874, true, false, [], [1]⟩,
        ⟨8, false, false, [82913], []⟩,
        ⟨17875, false, false, [], []⟩
      ]⟩,
    ⟨[82917], [82915, 9], .source 41523⟩,
    ⟨[82915, 9], [82917], .contexts [
        ⟨17877, true, false, [], []⟩
      ]⟩,
    ⟨[82915], [82915], .contexts []⟩,
    ⟨[82917, 9], [82915], .contexts [
        ⟨17878, true, false, [], [9]⟩,
        ⟨46, false, false, [82915], []⟩,
        ⟨17879, false, false, [], []⟩
      ]⟩,
    ⟨[82919], [82917, 11], .source 41524⟩,
    ⟨[82917, 11], [82919], .contexts [
        ⟨17881, true, false, [], []⟩
      ]⟩,
    ⟨[82917], [82917], .contexts []⟩,
    ⟨[82919, 11], [82917], .contexts [
        ⟨17882, true, false, [], [11]⟩,
        ⟨53, false, false, [82917], []⟩,
        ⟨17883, false, false, [], []⟩
      ]⟩,
    ⟨[82921], [82919, 1], .source 41525⟩,
    ⟨[82919, 1], [82921], .contexts [
        ⟨17885, true, false, [], []⟩
      ]⟩,
    ⟨[82919], [82919], .contexts []⟩,
    ⟨[82921, 1], [82919], .contexts [
        ⟨17886, true, false, [], [1]⟩,
        ⟨8, false, false, [82919], []⟩,
        ⟨17887, false, false, [], []⟩
      ]⟩,
    ⟨[82923], [82921, 13], .source 41526⟩,
    ⟨[82921, 13], [82923], .contexts [
        ⟨17889, true, false, [], []⟩
      ]⟩,
    ⟨[82921], [82921], .contexts []⟩,
    ⟨[82923, 13], [82921], .contexts [
        ⟨17890, true, false, [], [13]⟩,
        ⟨59, false, false, [82921], []⟩,
        ⟨17891, false, false, [], []⟩
      ]⟩,
    ⟨[82925], [82923, 15], .source 41527⟩,
    ⟨[82923, 15], [82925], .contexts [
        ⟨17893, true, false, [], []⟩
      ]⟩,
    ⟨[82923], [82923], .contexts []⟩,
    ⟨[82925, 15], [82923], .contexts [
        ⟨17894, true, false, [], [15]⟩,
        ⟨1, false, false, [82923], []⟩,
        ⟨17895, false, false, [], []⟩
      ]⟩,
    ⟨[82927], [82925, 1], .source 41528⟩,
    ⟨[82925, 1], [82927], .contexts [
        ⟨17897, true, false, [], []⟩
      ]⟩,
    ⟨[82925], [82925], .contexts []⟩,
    ⟨[82927, 1], [82925], .contexts [
        ⟨17898, true, false, [], [1]⟩,
        ⟨8, false, false, [82925], []⟩,
        ⟨17899, false, false, [], []⟩
      ]⟩,
    ⟨[82929], [82927, 3], .source 41529⟩,
    ⟨[82927, 3], [82929], .contexts [
        ⟨17901, true, false, [], []⟩
      ]⟩,
    ⟨[82927], [82927], .contexts []⟩,
    ⟨[82929, 3], [82927], .contexts [
        ⟨17902, true, false, [], [3]⟩,
        ⟨20, false, false, [82927], []⟩,
        ⟨17903, false, false, [], []⟩
      ]⟩,
    ⟨[82931], [82929, 5], .source 41530⟩,
    ⟨[82929, 5], [82931], .contexts [
        ⟨17905, true, false, [], []⟩
      ]⟩,
    ⟨[82929], [82929], .contexts []⟩,
    ⟨[82931, 5], [82929], .contexts [
        ⟨17906, true, false, [], [5]⟩,
        ⟨28, false, false, [82929], []⟩,
        ⟨17907, false, false, [], []⟩
      ]⟩,
    ⟨[82933], [82931, 1], .source 41531⟩,
    ⟨[82931, 1], [82933], .contexts [
        ⟨17909, true, false, [], []⟩
      ]⟩,
    ⟨[82931], [82931], .contexts []⟩,
    ⟨[82933, 1], [82931], .contexts [
        ⟨17910, true, false, [], [1]⟩,
        ⟨8, false, false, [82931], []⟩,
        ⟨17911, false, false, [], []⟩
      ]⟩,
    ⟨[82935], [82933, 9], .source 41532⟩,
    ⟨[82933], [82933], .contexts []⟩,
    ⟨[82935, 9], [82933], .contexts [
        ⟨17913, false, false, [], [9]⟩,
        ⟨46, false, false, [82933], []⟩,
        ⟨17914, false, false, [], []⟩
      ]⟩,
    ⟨[82937], [82935, 11], .source 41533⟩,
    ⟨[82935, 11], [82937], .contexts [
        ⟨17916, true, false, [], []⟩
      ]⟩,
    ⟨[82935], [82935], .contexts []⟩,
    ⟨[82937, 11], [82935], .contexts [
        ⟨17917, true, false, [], [11]⟩,
        ⟨53, false, false, [82935], []⟩,
        ⟨17918, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 280. -/
def y322TCIndexRaw280 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82939], [82937, 1], .source 41534⟩,
    ⟨[82937, 1], [82939], .contexts [
        ⟨17920, true, false, [], []⟩
      ]⟩,
    ⟨[82937], [82937], .contexts []⟩,
    ⟨[82939, 1], [82937], .contexts [
        ⟨17921, true, false, [], [1]⟩,
        ⟨8, false, false, [82937], []⟩,
        ⟨17922, false, false, [], []⟩
      ]⟩,
    ⟨[82941], [82939, 13], .source 41535⟩,
    ⟨[82939, 13], [82941], .contexts [
        ⟨17924, true, false, [], []⟩
      ]⟩,
    ⟨[82939], [82939], .contexts []⟩,
    ⟨[82941, 13], [82939], .contexts [
        ⟨17925, true, false, [], [13]⟩,
        ⟨59, false, false, [82939], []⟩,
        ⟨17926, false, false, [], []⟩
      ]⟩,
    ⟨[82943], [82941, 15], .source 41536⟩,
    ⟨[82941, 15], [82943], .contexts [
        ⟨17928, true, false, [], []⟩
      ]⟩,
    ⟨[82941], [82941], .contexts []⟩,
    ⟨[82943, 15], [82941], .contexts [
        ⟨17929, true, false, [], [15]⟩,
        ⟨1, false, false, [82941], []⟩,
        ⟨17930, false, false, [], []⟩
      ]⟩,
    ⟨[82945], [82943, 1], .source 41537⟩,
    ⟨[82943, 1], [82945], .contexts [
        ⟨17932, true, false, [], []⟩
      ]⟩,
    ⟨[82943], [82943], .contexts []⟩,
    ⟨[82945, 1], [82943], .contexts [
        ⟨17933, true, false, [], [1]⟩,
        ⟨8, false, false, [82943], []⟩,
        ⟨17934, false, false, [], []⟩
      ]⟩,
    ⟨[82947], [82945, 3], .source 41538⟩,
    ⟨[82945, 3], [82947], .contexts [
        ⟨17936, true, false, [], []⟩
      ]⟩,
    ⟨[82945], [82945], .contexts []⟩,
    ⟨[82947, 3], [82945], .contexts [
        ⟨17937, true, false, [], [3]⟩,
        ⟨20, false, false, [82945], []⟩,
        ⟨17938, false, false, [], []⟩
      ]⟩,
    ⟨[82949], [82947, 5], .source 41539⟩,
    ⟨[82947, 5], [82949], .contexts [
        ⟨17940, true, false, [], []⟩
      ]⟩,
    ⟨[82947], [82947], .contexts []⟩,
    ⟨[82949, 5], [82947], .contexts [
        ⟨17941, true, false, [], [5]⟩,
        ⟨28, false, false, [82947], []⟩,
        ⟨17942, false, false, [], []⟩
      ]⟩,
    ⟨[82951], [82949, 1], .source 41540⟩,
    ⟨[82949], [82949], .contexts []⟩,
    ⟨[82951, 1], [82949], .contexts [
        ⟨17944, false, false, [], [1]⟩,
        ⟨8, false, false, [82949], []⟩,
        ⟨17945, false, false, [], []⟩
      ]⟩,
    ⟨[82953], [82951, 9], .source 41541⟩,
    ⟨[82951, 9], [82953], .contexts [
        ⟨17947, true, false, [], []⟩
      ]⟩,
    ⟨[82951], [82951], .contexts []⟩,
    ⟨[82953, 9], [82951], .contexts [
        ⟨17948, true, false, [], [9]⟩,
        ⟨46, false, false, [82951], []⟩,
        ⟨17949, false, false, [], []⟩
      ]⟩,
    ⟨[82955], [82953, 11], .source 41542⟩,
    ⟨[82953, 11], [82955], .contexts [
        ⟨17951, true, false, [], []⟩
      ]⟩,
    ⟨[82953], [82953], .contexts []⟩,
    ⟨[82955, 11], [82953], .contexts [
        ⟨17952, true, false, [], [11]⟩,
        ⟨53, false, false, [82953], []⟩,
        ⟨17953, false, false, [], []⟩
      ]⟩,
    ⟨[82957], [82955, 1], .source 41543⟩,
    ⟨[82955, 1], [82957], .contexts [
        ⟨17955, true, false, [], []⟩
      ]⟩,
    ⟨[82955], [82955], .contexts []⟩,
    ⟨[82957, 1], [82955], .contexts [
        ⟨17956, true, false, [], [1]⟩,
        ⟨8, false, false, [82955], []⟩,
        ⟨17957, false, false, [], []⟩
      ]⟩,
    ⟨[82959], [82957, 13], .source 41544⟩,
    ⟨[82957, 13], [82959], .contexts [
        ⟨17959, true, false, [], []⟩
      ]⟩,
    ⟨[82957], [82957], .contexts []⟩,
    ⟨[82959, 13], [82957], .contexts [
        ⟨17960, true, false, [], [13]⟩,
        ⟨59, false, false, [82957], []⟩,
        ⟨17961, false, false, [], []⟩
      ]⟩,
    ⟨[82961], [82959, 15], .source 41545⟩,
    ⟨[82959, 15], [82961], .contexts [
        ⟨17963, true, false, [], []⟩
      ]⟩,
    ⟨[82959], [82959], .contexts []⟩,
    ⟨[82961, 15], [82959], .contexts [
        ⟨17964, true, false, [], [15]⟩,
        ⟨1, false, false, [82959], []⟩,
        ⟨17965, false, false, [], []⟩
      ]⟩,
    ⟨[82963], [82961, 1], .source 41546⟩,
    ⟨[82961, 1], [82963], .contexts [
        ⟨17967, true, false, [], []⟩
      ]⟩,
    ⟨[82961], [82961], .contexts []⟩,
    ⟨[82963, 1], [82961], .contexts [
        ⟨17968, true, false, [], [1]⟩,
        ⟨8, false, false, [82961], []⟩,
        ⟨17969, false, false, [], []⟩
      ]⟩,
    ⟨[82965], [82963, 3], .source 41547⟩,
    ⟨[82963, 3], [82965], .contexts [
        ⟨17971, true, false, [], []⟩
      ]⟩,
    ⟨[82963], [82963], .contexts []⟩,
    ⟨[82965, 3], [82963], .contexts [
        ⟨17972, true, false, [], [3]⟩,
        ⟨20, false, false, [82963], []⟩,
        ⟨17973, false, false, [], []⟩
      ]⟩,
    ⟨[82967], [82965, 5], .source 41548⟩,
    ⟨[82965, 5], [82967], .contexts [
        ⟨17975, true, false, [], []⟩
      ]⟩,
    ⟨[82965], [82965], .contexts []⟩,
    ⟨[82967, 5], [82965], .contexts [
        ⟨17976, true, false, [], [5]⟩,
        ⟨28, false, false, [82965], []⟩,
        ⟨17977, false, false, [], []⟩
      ]⟩,
    ⟨[82969], [82967, 1], .source 41549⟩,
    ⟨[82967, 1], [82969], .contexts [
        ⟨17979, true, false, [], []⟩
      ]⟩,
    ⟨[82967], [82967], .contexts []⟩,
    ⟨[82969, 1], [82967], .contexts [
        ⟨17980, true, false, [], [1]⟩,
        ⟨8, false, false, [82967], []⟩,
        ⟨17981, false, false, [], []⟩
      ]⟩,
    ⟨[82971], [82969, 9], .source 41550⟩]

/-- Exact literal claimed equations and contextual derivations, block 281. -/
def y322TCIndexRaw281 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82969, 9], [82971], .contexts [
        ⟨17983, true, false, [], []⟩
      ]⟩,
    ⟨[82969], [82969], .contexts []⟩,
    ⟨[82971, 9], [82969], .contexts [
        ⟨17984, true, false, [], [9]⟩,
        ⟨46, false, false, [82969], []⟩,
        ⟨17985, false, false, [], []⟩
      ]⟩,
    ⟨[82973], [82971, 11], .source 41551⟩,
    ⟨[82971, 11], [82973], .contexts [
        ⟨17987, true, false, [], []⟩
      ]⟩,
    ⟨[82971], [82971], .contexts []⟩,
    ⟨[82973, 11], [82971], .contexts [
        ⟨17988, true, false, [], [11]⟩,
        ⟨53, false, false, [82971], []⟩,
        ⟨17989, false, false, [], []⟩
      ]⟩,
    ⟨[82975], [82973, 1], .source 41552⟩,
    ⟨[82973, 1], [82975], .contexts [
        ⟨17991, true, false, [], []⟩
      ]⟩,
    ⟨[82973], [82973], .contexts []⟩,
    ⟨[82975, 1], [82973], .contexts [
        ⟨17992, true, false, [], [1]⟩,
        ⟨8, false, false, [82973], []⟩,
        ⟨17993, false, false, [], []⟩
      ]⟩,
    ⟨[82977], [82975, 13], .source 41553⟩,
    ⟨[82975, 13], [82977], .contexts [
        ⟨17995, true, false, [], []⟩
      ]⟩,
    ⟨[82975], [82975], .contexts []⟩,
    ⟨[82977, 13], [82975], .contexts [
        ⟨17996, true, false, [], [13]⟩,
        ⟨59, false, false, [82975], []⟩,
        ⟨17997, false, false, [], []⟩
      ]⟩,
    ⟨[82979], [82977, 15], .source 41554⟩,
    ⟨[82977, 15], [82979], .contexts [
        ⟨17999, true, false, [], []⟩
      ]⟩,
    ⟨[82977], [82977], .contexts []⟩,
    ⟨[82979, 15], [82977], .contexts [
        ⟨18000, true, false, [], [15]⟩,
        ⟨1, false, false, [82977], []⟩,
        ⟨18001, false, false, [], []⟩
      ]⟩,
    ⟨[82981], [82979, 1], .source 41555⟩,
    ⟨[82979, 1], [82981], .contexts [
        ⟨18003, true, false, [], []⟩
      ]⟩,
    ⟨[82979], [82979], .contexts []⟩,
    ⟨[82981, 1], [82979], .contexts [
        ⟨18004, true, false, [], [1]⟩,
        ⟨8, false, false, [82979], []⟩,
        ⟨18005, false, false, [], []⟩
      ]⟩,
    ⟨[82981], [82981], .contexts []⟩,
    ⟨[82981], [82981], .contexts []⟩,
    ⟨[82979, 1], [82981], .contexts [
        ⟨18004, false, false, [], []⟩,
        ⟨18007, false, false, [], []⟩,
        ⟨18008, false, false, [], []⟩,
        ⟨18008, false, false, [], []⟩
      ]⟩,
    ⟨[82977], [82977], .contexts []⟩,
    ⟨[82979, 15], [82977], .contexts [
        ⟨18002, false, false, [], []⟩,
        ⟨18010, false, false, [], []⟩,
        ⟨18001, false, false, [], []⟩,
        ⟨18001, false, false, [], []⟩
      ]⟩,
    ⟨[82977, 13], [82975], .contexts [
        ⟨17998, false, false, [], []⟩
      ]⟩,
    ⟨[82975], [82975], .contexts []⟩,
    ⟨[82975, 1], [82973], .contexts [
        ⟨17994, false, false, [], []⟩
      ]⟩,
    ⟨[82973], [82973], .contexts []⟩,
    ⟨[82973, 11], [82971], .contexts [
        ⟨17990, false, false, [], []⟩
      ]⟩,
    ⟨[82971], [82971], .contexts []⟩,
    ⟨[82971, 9], [82969], .contexts [
        ⟨17986, false, false, [], []⟩
      ]⟩,
    ⟨[82969], [82969], .contexts []⟩,
    ⟨[82969, 1], [82967], .contexts [
        ⟨17982, false, false, [], []⟩
      ]⟩,
    ⟨[82967], [82967], .contexts []⟩,
    ⟨[82979, 15, 13, 1, 11, 9, 1], [82967], .contexts [
        ⟨18011, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨18012, false, false, [], [1, 11, 9, 1]⟩,
        ⟨18013, false, false, [], [1, 11, 9, 1]⟩,
        ⟨17997, false, false, [], [1, 11, 9, 1]⟩,
        ⟨17997, false, false, [], [1, 11, 9, 1]⟩,
        ⟨18014, false, false, [], [11, 9, 1]⟩,
        ⟨18015, false, false, [], [11, 9, 1]⟩,
        ⟨17993, false, false, [], [11, 9, 1]⟩,
        ⟨17993, false, false, [], [11, 9, 1]⟩,
        ⟨18016, false, false, [], [9, 1]⟩,
        ⟨18017, false, false, [], [9, 1]⟩,
        ⟨17989, false, false, [], [9, 1]⟩,
        ⟨17989, false, false, [], [9, 1]⟩,
        ⟨18018, false, false, [], [1]⟩,
        ⟨18019, false, false, [], [1]⟩,
        ⟨17985, false, false, [], [1]⟩,
        ⟨17985, false, false, [], [1]⟩,
        ⟨18020, false, false, [], []⟩,
        ⟨18021, false, false, [], []⟩,
        ⟨17981, false, false, [], []⟩,
        ⟨17981, false, false, [], []⟩
      ]⟩,
    ⟨[82967, 5], [82965], .contexts [
        ⟨17978, false, false, [], []⟩
      ]⟩,
    ⟨[82965], [82965], .contexts []⟩,
    ⟨[82965, 3], [82963], .contexts [
        ⟨17974, false, false, [], []⟩
      ]⟩,
    ⟨[82963], [82963], .contexts []⟩,
    ⟨[82963, 1], [82961], .contexts [
        ⟨17970, false, false, [], []⟩
      ]⟩,
    ⟨[82961], [82961], .contexts []⟩,
    ⟨[82961, 15], [82959], .contexts [
        ⟨17966, false, false, [], []⟩
      ]⟩,
    ⟨[82959], [82959], .contexts []⟩,
    ⟨[82959, 13], [82957], .contexts [
        ⟨17962, false, false, [], []⟩
      ]⟩,
    ⟨[82957], [82957], .contexts []⟩,
    ⟨[82979, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13], [82957], .contexts [
        ⟨18022, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨18023, false, false, [], [3, 1, 15, 13]⟩,
        ⟨18024, false, false, [], [3, 1, 15, 13]⟩,
        ⟨17977, false, false, [], [3, 1, 15, 13]⟩,
        ⟨17977, false, false, [], [3, 1, 15, 13]⟩,
        ⟨18025, false, false, [], [1, 15, 13]⟩,
        ⟨18026, false, false, [], [1, 15, 13]⟩,
        ⟨17973, false, false, [], [1, 15, 13]⟩,
        ⟨17973, false, false, [], [1, 15, 13]⟩,
        ⟨18027, false, false, [], [15, 13]⟩,
        ⟨18028, false, false, [], [15, 13]⟩,
        ⟨17969, false, false, [], [15, 13]⟩,
        ⟨17969, false, false, [], [15, 13]⟩,
        ⟨18029, false, false, [], [13]⟩,
        ⟨18030, false, false, [], [13]⟩,
        ⟨17965, false, false, [], [13]⟩,
        ⟨17965, false, false, [], [13]⟩,
        ⟨18031, false, false, [], []⟩,
        ⟨18032, false, false, [], []⟩,
        ⟨17961, false, false, [], []⟩,
        ⟨17961, false, false, [], []⟩
      ]⟩,
    ⟨[82957, 1], [82955], .contexts [
        ⟨17958, false, false, [], []⟩
      ]⟩,
    ⟨[82955], [82955], .contexts []⟩,
    ⟨[82955, 11], [82953], .contexts [
        ⟨17954, false, false, [], []⟩
      ]⟩,
    ⟨[82953], [82953], .contexts []⟩,
    ⟨[82953, 9], [82951], .contexts [
        ⟨17950, false, false, [], []⟩
      ]⟩,
    ⟨[82951], [82951], .contexts []⟩,
    ⟨[82951, 1], [82949], .contexts [
        ⟨17946, false, false, [], []⟩
      ]⟩,
    ⟨[82949], [82949], .contexts []⟩,
    ⟨[82947], [82947], .contexts []⟩,
    ⟨[
      82979, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5
    ], [82947], .contexts [
        ⟨18033, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨18034, false, false, [], [11, 9, 1, 5]⟩,
        ⟨18035, false, false, [], [11, 9, 1, 5]⟩,
        ⟨17957, false, false, [], [11, 9, 1, 5]⟩,
        ⟨17957, false, false, [], [11, 9, 1, 5]⟩,
        ⟨18036, false, false, [], [9, 1, 5]⟩,
        ⟨18037, false, false, [], [9, 1, 5]⟩,
        ⟨17953, false, false, [], [9, 1, 5]⟩,
        ⟨17953, false, false, [], [9, 1, 5]⟩,
        ⟨18038, false, false, [], [1, 5]⟩,
        ⟨18039, false, false, [], [1, 5]⟩,
        ⟨17949, false, false, [], [1, 5]⟩,
        ⟨17949, false, false, [], [1, 5]⟩,
        ⟨18040, false, false, [], [5]⟩,
        ⟨18041, false, false, [], [5]⟩,
        ⟨17945, false, false, [], [5]⟩,
        ⟨17945, false, false, [], [5]⟩,
        ⟨17943, false, false, [], []⟩,
        ⟨18042, false, false, [], []⟩,
        ⟨17942, false, false, [], []⟩,
        ⟨17942, false, false, [], []⟩
      ]⟩,
    ⟨[82947, 3], [82945], .contexts [
        ⟨17939, false, false, [], []⟩
      ]⟩,
    ⟨[82945], [82945], .contexts []⟩,
    ⟨[82943], [82943], .contexts []⟩,
    ⟨[82941], [82941], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 282. -/
def y322TCIndexRaw282 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82941, 13], [82939], .contexts [
        ⟨17927, false, false, [], []⟩
      ]⟩,
    ⟨[82939], [82939], .contexts []⟩,
    ⟨[82939, 1], [82937], .contexts [
        ⟨17923, false, false, [], []⟩
      ]⟩,
    ⟨[82937], [82937], .contexts []⟩,
    ⟨[
      82979, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [82937], .contexts [
        ⟨18043, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨18044, false, false, [], [1, 15, 13, 1]⟩,
        ⟨18045, false, false, [], [1, 15, 13, 1]⟩,
        ⟨17938, false, false, [], [1, 15, 13, 1]⟩,
        ⟨17938, false, false, [], [1, 15, 13, 1]⟩,
        ⟨17935, false, false, [], [15, 13, 1]⟩,
        ⟨18046, false, false, [], [15, 13, 1]⟩,
        ⟨17934, false, false, [], [15, 13, 1]⟩,
        ⟨17934, false, false, [], [15, 13, 1]⟩,
        ⟨17931, false, false, [], [13, 1]⟩,
        ⟨18047, false, false, [], [13, 1]⟩,
        ⟨17930, false, false, [], [13, 1]⟩,
        ⟨17930, false, false, [], [13, 1]⟩,
        ⟨18048, false, false, [], [1]⟩,
        ⟨18049, false, false, [], [1]⟩,
        ⟨17926, false, false, [], [1]⟩,
        ⟨17926, false, false, [], [1]⟩,
        ⟨18050, false, false, [], []⟩,
        ⟨18051, false, false, [], []⟩,
        ⟨17922, false, false, [], []⟩,
        ⟨17922, false, false, [], []⟩
      ]⟩,
    ⟨[82937, 11], [82935], .contexts [
        ⟨17919, false, false, [], []⟩
      ]⟩,
    ⟨[82935], [82935], .contexts []⟩,
    ⟨[82935, 9], [82933], .contexts [
        ⟨17915, false, false, [], []⟩
      ]⟩,
    ⟨[82933], [82933], .contexts []⟩,
    ⟨[82933, 1], [82931], .contexts [
        ⟨17912, false, false, [], []⟩
      ]⟩,
    ⟨[82931], [82931], .contexts []⟩,
    ⟨[82931, 5], [82929], .contexts [
        ⟨17908, false, false, [], []⟩
      ]⟩,
    ⟨[82929], [82929], .contexts []⟩,
    ⟨[82927], [82927], .contexts []⟩,
    ⟨[
      82979, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3
    ], [82927], .contexts [
        ⟨18052, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨18053, false, false, [], [9, 1, 5, 3]⟩,
        ⟨18054, false, false, [], [9, 1, 5, 3]⟩,
        ⟨17918, false, false, [], [9, 1, 5, 3]⟩,
        ⟨17918, false, false, [], [9, 1, 5, 3]⟩,
        ⟨18055, false, false, [], [1, 5, 3]⟩,
        ⟨18056, false, false, [], [1, 5, 3]⟩,
        ⟨17914, false, false, [], [1, 5, 3]⟩,
        ⟨17914, false, false, [], [1, 5, 3]⟩,
        ⟨18057, false, false, [], [5, 3]⟩,
        ⟨18058, false, false, [], [5, 3]⟩,
        ⟨17911, false, false, [], [5, 3]⟩,
        ⟨17911, false, false, [], [5, 3]⟩,
        ⟨18059, false, false, [], [3]⟩,
        ⟨18060, false, false, [], [3]⟩,
        ⟨17907, false, false, [], [3]⟩,
        ⟨17907, false, false, [], [3]⟩,
        ⟨17904, false, false, [], []⟩,
        ⟨18061, false, false, [], []⟩,
        ⟨17903, false, false, [], []⟩,
        ⟨17903, false, false, [], []⟩
      ]⟩,
    ⟨[82927, 1], [82925], .contexts [
        ⟨17900, false, false, [], []⟩
      ]⟩,
    ⟨[82925], [82925], .contexts []⟩,
    ⟨[82925, 15], [82923], .contexts [
        ⟨17896, false, false, [], []⟩
      ]⟩,
    ⟨[82921], [82921], .contexts []⟩,
    ⟨[82921, 1], [82919], .contexts [
        ⟨17888, false, false, [], []⟩
      ]⟩,
    ⟨[82919], [82919], .contexts []⟩,
    ⟨[82917], [82917], .contexts []⟩,
    ⟨[
      82979, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11
    ], [82917], .contexts [
        ⟨18062, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨18063, false, false, [], [15, 13, 1, 11]⟩,
        ⟨18064, false, false, [], [15, 13, 1, 11]⟩,
        ⟨17899, false, false, [], [15, 13, 1, 11]⟩,
        ⟨17899, false, false, [], [15, 13, 1, 11]⟩,
        ⟨18065, false, false, [], [13, 1, 11]⟩,
        ⟨17895, false, false, [], [13, 1, 11]⟩,
        ⟨17895, false, false, [], [13, 1, 11]⟩,
        ⟨17892, false, false, [], [1, 11]⟩,
        ⟨18066, false, false, [], [1, 11]⟩,
        ⟨17891, false, false, [], [1, 11]⟩,
        ⟨17891, false, false, [], [1, 11]⟩,
        ⟨18067, false, false, [], [11]⟩,
        ⟨18068, false, false, [], [11]⟩,
        ⟨17887, false, false, [], [11]⟩,
        ⟨17887, false, false, [], [11]⟩,
        ⟨17884, false, false, [], []⟩,
        ⟨18069, false, false, [], []⟩,
        ⟨17883, false, false, [], []⟩,
        ⟨17883, false, false, [], []⟩
      ]⟩,
    ⟨[82917, 9], [82915], .contexts [
        ⟨17880, false, false, [], []⟩
      ]⟩,
    ⟨[82915], [82915], .contexts []⟩,
    ⟨[82915, 1], [82913], .contexts [
        ⟨17876, false, false, [], []⟩
      ]⟩,
    ⟨[82913], [82913], .contexts []⟩,
    ⟨[82913, 5], [82911], .contexts [
        ⟨17872, false, false, [], []⟩
      ]⟩,
    ⟨[82911], [82911], .contexts []⟩,
    ⟨[82911, 3], [82909], .contexts [
        ⟨17868, false, false, [], []⟩
      ]⟩,
    ⟨[82909], [82909], .contexts []⟩,
    ⟨[82907], [82907], .contexts []⟩,
    ⟨[
      82979, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1
    ], [82907], .contexts [
        ⟨18070, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨18071, false, false, [], [1, 5, 3, 1]⟩,
        ⟨18072, false, false, [], [1, 5, 3, 1]⟩,
        ⟨17879, false, false, [], [1, 5, 3, 1]⟩,
        ⟨17879, false, false, [], [1, 5, 3, 1]⟩,
        ⟨18073, false, false, [], [5, 3, 1]⟩,
        ⟨18074, false, false, [], [5, 3, 1]⟩,
        ⟨17875, false, false, [], [5, 3, 1]⟩,
        ⟨17875, false, false, [], [5, 3, 1]⟩,
        ⟨18075, false, false, [], [3, 1]⟩,
        ⟨18076, false, false, [], [3, 1]⟩,
        ⟨17871, false, false, [], [3, 1]⟩,
        ⟨17871, false, false, [], [3, 1]⟩,
        ⟨18077, false, false, [], [1]⟩,
        ⟨18078, false, false, [], [1]⟩,
        ⟨17867, false, false, [], [1]⟩,
        ⟨17867, false, false, [], [1]⟩,
        ⟨17864, false, false, [], []⟩,
        ⟨18079, false, false, [], []⟩,
        ⟨17863, false, false, [], []⟩,
        ⟨17863, false, false, [], []⟩
      ]⟩,
    ⟨[82905], [82905], .contexts []⟩,
    ⟨[82903], [82903], .contexts []⟩,
    ⟨[82903, 1], [82901], .contexts [
        ⟨17852, false, false, [], []⟩
      ]⟩,
    ⟨[82901], [82901], .contexts []⟩,
    ⟨[82899], [82899], .contexts []⟩,
    ⟨[82897], [82897], .contexts []⟩,
    ⟨[
      82979, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9
    ], [82897], .contexts [
        ⟨18080, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨17860, false, false, [], [13, 1, 11, 9]⟩,
        ⟨18081, false, false, [], [13, 1, 11, 9]⟩,
        ⟨17859, false, false, [], [13, 1, 11, 9]⟩,
        ⟨17859, false, false, [], [13, 1, 11, 9]⟩,
        ⟨17856, false, false, [], [1, 11, 9]⟩,
        ⟨18082, false, false, [], [1, 11, 9]⟩,
        ⟨17855, false, false, [], [1, 11, 9]⟩,
        ⟨17855, false, false, [], [1, 11, 9]⟩,
        ⟨18083, false, false, [], [11, 9]⟩,
        ⟨18084, false, false, [], [11, 9]⟩,
        ⟨17851, false, false, [], [11, 9]⟩,
        ⟨17851, false, false, [], [11, 9]⟩,
        ⟨17848, false, false, [], [9]⟩,
        ⟨18085, false, false, [], [9]⟩,
        ⟨17847, false, false, [], [9]⟩,
        ⟨17847, false, false, [], [9]⟩,
        ⟨17844, false, false, [], []⟩,
        ⟨18086, false, false, [], []⟩,
        ⟨17843, false, false, [], []⟩,
        ⟨17843, false, false, [], []⟩
      ]⟩,
    ⟨[82897, 1], [82895], .contexts [
        ⟨17840, false, false, [], []⟩
      ]⟩,
    ⟨[82895], [82895], .contexts []⟩,
    ⟨[82895, 5], [82893], .contexts [
        ⟨17836, false, false, [], []⟩
      ]⟩,
    ⟨[82893], [82893], .contexts []⟩,
    ⟨[82891], [82891], .contexts []⟩,
    ⟨[82891, 1], [82889], .contexts [
        ⟨17828, false, false, [], []⟩
      ]⟩,
    ⟨[82889], [82889], .contexts []⟩,
    ⟨[82887], [82887], .contexts []⟩,
    ⟨[
      82979, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [82887], .contexts [
        ⟨18087, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨18088, false, false, [], [5, 3, 1, 15]⟩,
        ⟨18089, false, false, [], [5, 3, 1, 15]⟩,
        ⟨17839, false, false, [], [5, 3, 1, 15]⟩,
        ⟨17839, false, false, [], [5, 3, 1, 15]⟩,
        ⟨18090, false, false, [], [3, 1, 15]⟩,
        ⟨18091, false, false, [], [3, 1, 15]⟩,
        ⟨17835, false, false, [], [3, 1, 15]⟩,
        ⟨17835, false, false, [], [3, 1, 15]⟩,
        ⟨17832, false, false, [], [1, 15]⟩,
        ⟨18092, false, false, [], [1, 15]⟩,
        ⟨17831, false, false, [], [1, 15]⟩,
        ⟨17831, false, false, [], [1, 15]⟩,
        ⟨18093, false, false, [], [15]⟩,
        ⟨18094, false, false, [], [15]⟩,
        ⟨17827, false, false, [], [15]⟩,
        ⟨17827, false, false, [], [15]⟩,
        ⟨17823, true, false, [], [15]⟩,
        ⟨1, false, false, [82887], []⟩,
        ⟨17824, false, false, [], []⟩,
        ⟨18095, false, false, [], []⟩,
        ⟨17824, false, false, [], []⟩,
        ⟨17824, false, false, [], []⟩
      ]⟩,
    ⟨[82885], [82885], .contexts []⟩,
    ⟨[82883], [82883], .contexts []⟩,
    ⟨[82881], [82881], .contexts []⟩,
    ⟨[82879], [82879], .contexts []⟩,
    ⟨[
      82979, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1
    ], [82877], .contexts [
        ⟨18096, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨17821, false, false, [], [1, 11, 9, 1]⟩,
        ⟨18097, false, false, [], [1, 11, 9, 1]⟩,
        ⟨17820, false, false, [], [1, 11, 9, 1]⟩,
        ⟨17820, false, false, [], [1, 11, 9, 1]⟩,
        ⟨17817, false, false, [], [11, 9, 1]⟩,
        ⟨18098, false, false, [], [11, 9, 1]⟩,
        ⟨17816, false, false, [], [11, 9, 1]⟩,
        ⟨17816, false, false, [], [11, 9, 1]⟩,
        ⟨17813, false, false, [], [9, 1]⟩,
        ⟨18099, false, false, [], [9, 1]⟩,
        ⟨17812, false, false, [], [9, 1]⟩,
        ⟨17812, false, false, [], [9, 1]⟩,
        ⟨17809, false, false, [], [1]⟩,
        ⟨18100, false, false, [], [1]⟩,
        ⟨17808, false, false, [], [1]⟩,
        ⟨17808, false, false, [], [1]⟩,
        ⟨17805, false, false, [], []⟩,
        ⟨17791, false, false, [], []⟩,
        ⟨17792, false, false, [], []⟩,
        ⟨17792, false, false, [], []⟩
      ]⟩,
    ⟨[82877, 5], [82875], .contexts [
        ⟨17789, false, false, [], []⟩
      ]⟩,
    ⟨[78739, 1], [78729], .contexts [
        ⟨4944, false, false, [], []⟩
      ]⟩,
    ⟨[
      82979, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [78411], .contexts [
        ⟨18101, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨18102, false, false, [], [3, 1, 15, 13]⟩,
        ⟨17773, false, false, [], [3, 1, 15, 13]⟩,
        ⟨17774, false, false, [], [3, 1, 15, 13]⟩,
        ⟨17774, false, false, [], [3, 1, 15, 13]⟩,
        ⟨17794, false, false, [], [1, 15, 13]⟩,
        ⟨4936, false, false, [], [1, 15, 13]⟩,
        ⟨4937, false, false, [], [1, 15, 13]⟩,
        ⟨4937, false, false, [], [1, 15, 13]⟩,
        ⟨18103, false, false, [], [15, 13]⟩,
        ⟨4851, false, false, [], [15, 13]⟩,
        ⟨4852, false, false, [], [15, 13]⟩,
        ⟨4852, false, false, [], [15, 13]⟩,
        ⟨4870, false, false, [], [13]⟩,
        ⟨4590, false, false, [], [13]⟩,
        ⟨4591, false, false, [], [13]⟩,
        ⟨4591, false, false, [], [13]⟩,
        ⟨4602, false, false, [], []⟩,
        ⟨4337, false, false, [], []⟩,
        ⟨4338, false, false, [], []⟩,
        ⟨4338, false, false, [], []⟩
      ]⟩,
    ⟨[
      82979, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5
    ], [315, 77983], .contexts [
        ⟨18104, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨4343, false, false, [], [11, 9, 1, 5]⟩,
        ⟨3883, false, false, [], [11, 9, 1, 5]⟩,
        ⟨3884, false, false, [], [11, 9, 1, 5]⟩,
        ⟨3884, false, false, [], [11, 9, 1, 5]⟩,
        ⟨3891, false, false, [], [9, 1, 5]⟩,
        ⟨3682, false, false, [], [9, 1, 5]⟩,
        ⟨3683, false, false, [], [9, 1, 5]⟩,
        ⟨3683, false, false, [], [9, 1, 5]⟩,
        ⟨3691, false, false, [], [1, 5]⟩,
        ⟨3320, false, false, [], [1, 5]⟩,
        ⟨3321, false, false, [], [1, 5]⟩,
        ⟨3321, false, false, [], [1, 5]⟩,
        ⟨3323, false, false, [], [5]⟩,
        ⟨3268, false, false, [], [5]⟩,
        ⟨3270, false, false, [], [5]⟩,
        ⟨3270, false, false, [], [5]⟩,
        ⟨3257, false, false, [315], []⟩,
        ⟨3212, false, false, [], []⟩,
        ⟨3213, false, false, [], []⟩,
        ⟨3214, false, false, [], []⟩
      ]⟩,
    ⟨[15705], [315, 19], .source 7917⟩,
    ⟨[
      82979, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1
    ], [15705, 77483], .contexts [
        ⟨18105, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨3089, false, false, [315], [1, 15, 13, 1]⟩,
        ⟨2837, false, false, [315], [15, 13, 1]⟩,
        ⟨441, true, false, [315], [77859, 15, 13, 1]⟩,
        ⟨18106, true, false, [], [77859, 15, 13, 1]⟩,
        ⟨2829, false, false, [15705], [13, 1]⟩,
        ⟨2351, false, false, [15705], [1]⟩,
        ⟨2089, false, false, [15705], []⟩
      ]⟩,
    ⟨[15707], [15705, 21], .source 7918⟩,
    ⟨[15709], [15707, 25], .source 7919⟩,
    ⟨[15711], [15709, 23], .source 7920⟩,
    ⟨[
      82979, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [15711, 77357], .contexts [
        ⟨18107, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨1579, false, false, [15705], [9, 1, 5, 3]⟩,
        ⟨1068, false, false, [15705], [1, 5, 3]⟩,
        ⟨1030, false, false, [15705], [5, 3]⟩,
        ⟨442, true, false, [15705], [77357, 5, 3]⟩,
        ⟨18108, true, false, [], [77357, 5, 3]⟩,
        ⟨1048, false, false, [15707], [3]⟩,
        ⟨465, true, false, [15707], [77357, 3]⟩,
        ⟨18109, true, false, [], [77357, 3]⟩,
        ⟨1037, false, false, [15709], []⟩,
        ⟨445, true, false, [15709], [77357]⟩,
        ⟨18110, true, false, [], [77357]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 283. -/
def y322TCIndexRaw283 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15713], [15711, 21], .source 7921⟩,
    ⟨[15715], [15713, 31], .source 7922⟩,
    ⟨[15717], [15715, 19], .source 7923⟩,
    ⟨[15719], [15717, 21], .source 7924⟩,
    ⟨[15721], [15719, 29], .source 7925⟩,
    ⟨[
      82979, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11
    ], [15721, 77357], .contexts [
        ⟨18111, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨1030, false, false, [15711], [15, 13, 1, 11]⟩,
        ⟨442, true, false, [15711], [77357, 15, 13, 1, 11]⟩,
        ⟨18112, true, false, [], [77357, 15, 13, 1, 11]⟩,
        ⟨1066, false, false, [15713], [13, 1, 11]⟩,
        ⟨443, true, false, [15713], [77357, 13, 1, 11]⟩,
        ⟨18113, true, false, [], [77357, 13, 1, 11]⟩,
        ⟨1059, false, false, [15715], [1, 11]⟩,
        ⟨441, true, false, [15715], [77357, 1, 11]⟩,
        ⟨18114, true, false, [], [77357, 1, 11]⟩,
        ⟨1030, false, false, [15717], [11]⟩,
        ⟨442, true, false, [15717], [77357, 11]⟩,
        ⟨18115, true, false, [], [77357, 11]⟩,
        ⟨1053, false, false, [15719], []⟩,
        ⟨444, true, false, [15719], [77357]⟩,
        ⟨18116, true, false, [], [77357]⟩
      ]⟩,
    ⟨[15723], [15721, 211], .source 7926⟩,
    ⟨[15725], [15723, 475], .source 7927⟩,
    ⟨[15727], [15725, 15695], .source 7928⟩,
    ⟨[15729], [15727, 15691], .source 7929⟩,
    ⟨[
      82979, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [15729, 82871], .contexts [
        ⟨18117, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨1067, false, false, [15721], [1, 5, 3, 1]⟩,
        ⟨1527, false, false, [15721], [5, 3, 1]⟩,
        ⟨18118, true, false, [], [77479, 5, 3, 1]⟩,
        ⟨1532, false, false, [15723], [3, 1]⟩,
        ⟨18119, true, false, [], [77479, 3, 1]⟩,
        ⟨17717, false, false, [15725], [1]⟩,
        ⟨18120, true, false, [], [82871, 1]⟩,
        ⟨17714, false, false, [15727], []⟩,
        ⟨18121, true, false, [], [82871]⟩
      ]⟩,
    ⟨[15731], [15729, 15699], .source 7930⟩,
    ⟨[15733], [15731, 537], .source 7931⟩,
    ⟨[
      82979, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9
    ], [15733, 78125], .contexts [
        ⟨18122, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨17734, false, false, [15729], [13, 1, 11, 9]⟩,
        ⟨18123, true, false, [], [82871, 13, 1, 11, 9]⟩,
        ⟨17703, false, false, [15731], [1, 11, 9]⟩,
        ⟨17636, false, false, [15731], [11, 9]⟩,
        ⟨18124, true, false, [], [82861, 11, 9]⟩,
        ⟨17612, false, false, [15733], [9]⟩,
        ⟨3733, false, false, [15733], []⟩
      ]⟩,
    ⟨[15735], [15733, 15629], .source 7932⟩,
    ⟨[15735, 82853], [15735, 82853], .contexts []⟩,
    ⟨[15735, 82853], [15735, 82853], .contexts []⟩,
    ⟨[82981, 3], [82981, 3], .contexts []⟩,
    ⟨[82981, 3], [15735, 82853], .contexts [
        ⟨18129, false, false, [], []⟩,
        ⟨18009, true, false, [], [3]⟩,
        ⟨1908, false, false, [82979], []⟩,
        ⟨1909, false, false, [82979], []⟩,
        ⟨18125, false, false, [], [1, 5]⟩,
        ⟨17420, false, false, [15733], [5]⟩,
        ⟨18126, true, false, [], [82847, 5]⟩,
        ⟨17521, false, false, [15735], []⟩,
        ⟨18127, false, false, [], []⟩,
        ⟨18128, false, false, [], []⟩,
        ⟨17528, false, false, [15735], []⟩,
        ⟨13, true, false, [], [15735, 82853]⟩
      ]⟩,
    ⟨[15737], [15734], .source 7933⟩,
    ⟨[82853, 3], [15737, 82981], .contexts [
        ⟨18130, true, false, [15734], [3]⟩,
        ⟨20, false, false, [15734, 82981], []⟩,
        ⟨18131, true, false, [], [82981]⟩
      ]⟩,
    ⟨[15739], [15735, 261], .source 7934⟩,
    ⟨[15741], [15739, 15737], .source 7935⟩,
    ⟨[3, 7, 3, 7], [], .contexts [
        ⟨139, false, false, [], []⟩
      ]⟩,
    ⟨[82981], [82981], .contexts []⟩,
    ⟨[82981, 7], [82981, 7], .contexts []⟩,
    ⟨[82981], [82981], .contexts []⟩,
    ⟨[15743], [15740], .source 7936⟩,
    ⟨[15740], [15740], .contexts []⟩,
    ⟨[15743], [15740], .contexts [
        ⟨18139, false, false, [], []⟩,
        ⟨18140, false, false, [], []⟩,
        ⟨18140, false, false, [], []⟩
      ]⟩,
    ⟨[82981, 7], [15743, 82981], .contexts [
        ⟨18137, false, false, [], []⟩,
        ⟨18134, false, false, [15740], [82981, 7]⟩,
        ⟨18132, true, false, [15740, 15739], [7]⟩,
        ⟨18133, false, false, [15740], [82853, 3, 7]⟩,
        ⟨17529, true, false, [15740, 15735], [3, 7]⟩,
        ⟨18128, true, false, [15740], [7, 3, 7]⟩,
        ⟨18128, true, false, [15740], [7, 3, 7]⟩,
        ⟨18127, true, false, [15740], [7, 3, 7]⟩,
        ⟨18130, true, false, [15740], [7, 3, 7]⟩,
        ⟨18129, true, false, [15740], [7, 3, 7]⟩,
        ⟨18135, false, false, [15740, 82981], []⟩,
        ⟨18136, false, false, [15740], []⟩,
        ⟨18138, false, false, [15740], []⟩,
        ⟨18141, true, false, [], [82981]⟩
      ]⟩,
    ⟨[15743, 82981], [15743, 82981], .contexts []⟩,
    ⟨[15743, 82981], [15743, 82981], .contexts []⟩,
    ⟨[82979], [82979], .contexts []⟩,
    ⟨[82981, 1], [82979], .contexts [
        ⟨18006, false, false, [], []⟩,
        ⟨18145, false, false, [], []⟩,
        ⟨18005, false, false, [], []⟩,
        ⟨18005, false, false, [], []⟩
      ]⟩,
    ⟨[82979, 7], [82979, 7], .contexts []⟩,
    ⟨[82979], [82979], .contexts []⟩,
    ⟨[15742], [15742], .contexts []⟩,
    ⟨[15741], [15742], .contexts [
        ⟨18139, true, true, [], []⟩,
        ⟨18149, false, false, [], []⟩,
        ⟨18149, false, false, [], []⟩
      ]⟩,
    ⟨[82979, 7], [15741, 82979], .contexts [
        ⟨18147, false, false, [], []⟩,
        ⟨18006, true, false, [], [7]⟩,
        ⟨18144, true, false, [15742], [1, 7]⟩,
        ⟨18144, true, false, [15742], [1, 7]⟩,
        ⟨18143, true, false, [15742], [1, 7]⟩,
        ⟨18142, true, false, [15742], [1, 7]⟩,
        ⟨18137, true, false, [15742], [1, 7]⟩,
        ⟨502, false, false, [15742, 82981], []⟩,
        ⟨9, false, false, [15742, 82981], []⟩,
        ⟨18146, false, false, [15742], []⟩,
        ⟨18148, false, false, [15742], []⟩,
        ⟨18150, true, false, [], [82979]⟩
      ]⟩,
    ⟨[15741, 82979], [15741, 82979], .contexts []⟩,
    ⟨[15741, 82979], [15741, 82979], .contexts []⟩,
    ⟨[82979, 7], [15741, 82979], .contexts [
        ⟨18147, false, false, [], []⟩,
        ⟨18151, false, false, [], []⟩,
        ⟨18152, false, false, [], []⟩,
        ⟨18153, false, false, [], []⟩,
        ⟨18153, false, false, [], []⟩
      ]⟩,
    ⟨[7, 15, 7], [14], .contexts [
        ⟨1062, false, false, [], [14]⟩
      ]⟩,
    ⟨[82979, 14], [82979, 15], .contexts [
        ⟨10, false, false, [82979], []⟩
      ]⟩,
    ⟨[82977, 7], [82977, 7], .contexts []⟩,
    ⟨[82977], [82977], .contexts []⟩,
    ⟨[82977, 7], [15743, 82977], .contexts [
        ⟨18157, false, false, [], []⟩,
        ⟨18002, true, false, [], [7]⟩,
        ⟨18154, true, false, [15740], [15, 7]⟩,
        ⟨18155, false, false, [15740, 82979], []⟩,
        ⟨18156, false, false, [15740], []⟩,
        ⟨18011, false, false, [15740], []⟩,
        ⟨18158, false, false, [15740], []⟩,
        ⟨18141, true, false, [], [82977]⟩
      ]⟩,
    ⟨[15743, 82977], [15743, 82977], .contexts []⟩,
    ⟨[15743, 82977], [15743, 82977], .contexts []⟩,
    ⟨[82977, 7], [15743, 82977], .contexts [
        ⟨18157, false, false, [], []⟩,
        ⟨18159, false, false, [], []⟩,
        ⟨18160, false, false, [], []⟩,
        ⟨18161, false, false, [], []⟩,
        ⟨18161, false, false, [], []⟩
      ]⟩,
    ⟨[82977, 13], [82975], .contexts [
        ⟨18012, false, false, [], []⟩,
        ⟨18013, false, false, [], []⟩,
        ⟨17997, false, false, [], []⟩,
        ⟨17997, false, false, [], []⟩
      ]⟩,
    ⟨[82977, 12], [82977, 13], .contexts [
        ⟨64, false, false, [82977], []⟩
      ]⟩,
    ⟨[82975, 7], [82975, 7], .contexts []⟩,
    ⟨[82975], [82975], .contexts []⟩,
    ⟨[82975, 7], [15741, 82975], .contexts [
        ⟨18165, false, false, [], []⟩,
        ⟨17998, true, false, [], [7]⟩,
        ⟨18162, true, false, [15742], [13, 7]⟩,
        ⟨518, false, false, [15742, 82977], []⟩,
        ⟨18164, false, false, [15742], []⟩,
        ⟨18163, false, false, [15742], []⟩,
        ⟨18166, false, false, [15742], []⟩,
        ⟨18150, true, false, [], [82975]⟩
      ]⟩,
    ⟨[15741, 82975], [15741, 82975], .contexts []⟩,
    ⟨[15741, 82975], [15741, 82975], .contexts []⟩,
    ⟨[82973, 7], [82973, 7], .contexts []⟩,
    ⟨[82973], [82973], .contexts []⟩,
    ⟨[82973, 7], [15743, 82973], .contexts [
        ⟨18170, false, false, [], []⟩,
        ⟨17994, true, false, [], [7]⟩,
        ⟨18169, true, false, [15740], [1, 7]⟩,
        ⟨18169, true, false, [15740], [1, 7]⟩,
        ⟨18168, true, false, [15740], [1, 7]⟩,
        ⟨18167, true, false, [15740], [1, 7]⟩,
        ⟨18165, true, false, [15740], [1, 7]⟩,
        ⟨502, false, false, [15740, 82975], []⟩,
        ⟨9, false, false, [15740, 82975], []⟩,
        ⟨18014, false, false, [15740], []⟩,
        ⟨18015, false, false, [15740], []⟩,
        ⟨17993, false, false, [15740], []⟩,
        ⟨17993, false, false, [15740], []⟩,
        ⟨18171, false, false, [15740], []⟩,
        ⟨18141, true, false, [], [82973]⟩
      ]⟩,
    ⟨[15743, 82973], [15743, 82973], .contexts []⟩,
    ⟨[15743, 82973], [15743, 82973], .contexts []⟩,
    ⟨[82973, 7], [15743, 82973], .contexts [
        ⟨18170, false, false, [], []⟩,
        ⟨18172, false, false, [], []⟩,
        ⟨18173, false, false, [], []⟩,
        ⟨18174, false, false, [], []⟩,
        ⟨18174, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 284. -/
def y322TCIndexRaw284 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82973, 11], [82971], .contexts [
        ⟨18016, false, false, [], []⟩,
        ⟨18017, false, false, [], []⟩,
        ⟨17989, false, false, [], []⟩,
        ⟨17989, false, false, [], []⟩
      ]⟩,
    ⟨[82973, 10], [82973, 11], .contexts [
        ⟨54, false, false, [82973], []⟩
      ]⟩,
    ⟨[82971, 7], [82971, 7], .contexts []⟩,
    ⟨[82971], [82971], .contexts []⟩,
    ⟨[82971, 7], [15741, 82971], .contexts [
        ⟨18178, false, false, [], []⟩,
        ⟨17990, true, false, [], [7]⟩,
        ⟨18175, true, false, [15742], [11, 7]⟩,
        ⟨555, false, false, [15742, 82973], []⟩,
        ⟨18177, false, false, [15742], []⟩,
        ⟨18176, false, false, [15742], []⟩,
        ⟨18179, false, false, [15742], []⟩,
        ⟨18150, true, false, [], [82971]⟩
      ]⟩,
    ⟨[15741, 82971], [15741, 82971], .contexts []⟩,
    ⟨[15741, 82971], [15741, 82971], .contexts []⟩,
    ⟨[82971, 9], [82969], .contexts [
        ⟨18018, false, false, [], []⟩,
        ⟨18019, false, false, [], []⟩,
        ⟨17985, false, false, [], []⟩,
        ⟨17985, false, false, [], []⟩
      ]⟩,
    ⟨[82971, 8], [82971, 9], .contexts [
        ⟨47, false, false, [82971], []⟩
      ]⟩,
    ⟨[82969, 7], [82969, 7], .contexts []⟩,
    ⟨[82969], [82969], .contexts []⟩,
    ⟨[82969, 7], [15743, 82969], .contexts [
        ⟨18185, false, false, [], []⟩,
        ⟨17986, true, false, [], [7]⟩,
        ⟨18182, true, false, [15740], [9, 7]⟩,
        ⟨18182, true, false, [15740], [9, 7]⟩,
        ⟨18181, true, false, [15740], [9, 7]⟩,
        ⟨18180, true, false, [15740], [9, 7]⟩,
        ⟨18178, true, false, [15740], [9, 7]⟩,
        ⟨579, false, false, [15740, 82971], []⟩,
        ⟨18184, false, false, [15740], []⟩,
        ⟨18183, false, false, [15740], []⟩,
        ⟨18186, false, false, [15740], []⟩,
        ⟨18141, true, false, [], [82969]⟩
      ]⟩,
    ⟨[15743, 82969], [15743, 82969], .contexts []⟩,
    ⟨[15743, 82969], [15743, 82969], .contexts []⟩,
    ⟨[82969, 7], [15743, 82969], .contexts [
        ⟨18185, false, false, [], []⟩,
        ⟨18187, false, false, [], []⟩,
        ⟨18188, false, false, [], []⟩,
        ⟨18189, false, false, [], []⟩,
        ⟨18189, false, false, [], []⟩
      ]⟩,
    ⟨[82969, 1], [82967], .contexts [
        ⟨18020, false, false, [], []⟩,
        ⟨18021, false, false, [], []⟩,
        ⟨17981, false, false, [], []⟩,
        ⟨17981, false, false, [], []⟩
      ]⟩,
    ⟨[82967, 7], [82967, 7], .contexts []⟩,
    ⟨[82967], [82967], .contexts []⟩,
    ⟨[82967, 7], [15741, 82967], .contexts [
        ⟨18192, false, false, [], []⟩,
        ⟨17982, true, false, [], [7]⟩,
        ⟨18190, true, false, [15742], [1, 7]⟩,
        ⟨502, false, false, [15742, 82969], []⟩,
        ⟨9, false, false, [15742, 82969], []⟩,
        ⟨18191, false, false, [15742], []⟩,
        ⟨18193, false, false, [15742], []⟩,
        ⟨18150, true, false, [], [82967]⟩
      ]⟩,
    ⟨[82873, 11], [82983], .source 74781⟩,
    ⟨[82983, 11], [82873], .contexts [
        ⟨18195, true, false, [], [11]⟩,
        ⟨53, false, false, [82873], []⟩,
        ⟨17738, false, false, [], []⟩
      ]⟩,
    ⟨[82983], [82983], .contexts []⟩,
    ⟨[82983], [82983], .source 74782⟩,
    ⟨[82873, 11], [82983], .source 74783⟩,
    ⟨[15691, 82983], [15691, 82983], .contexts []⟩,
    ⟨[82983], [82983], .contexts []⟩,
    ⟨[82983, 1], [15691, 82983], .contexts [
        ⟨18199, true, false, [], [1]⟩,
        ⟨562, false, false, [82873], []⟩,
        ⟨563, false, false, [82873], []⟩,
        ⟨17742, false, false, [], [11]⟩,
        ⟨17744, false, false, [], [11]⟩,
        ⟨17740, false, false, [], [11]⟩,
        ⟨17741, false, false, [], [11]⟩,
        ⟨17741, false, false, [], [11]⟩,
        ⟨18195, false, false, [15691], []⟩,
        ⟨18200, false, false, [], []⟩,
        ⟨18201, false, false, [15691], []⟩,
        ⟨17713, true, false, [], [82983]⟩
      ]⟩,
    ⟨[15703, 82983], [15703, 82983], .contexts []⟩,
    ⟨[15703, 82983], [15703, 82983], .contexts []⟩,
    ⟨[82983, 3], [82983, 3], .contexts []⟩,
    ⟨[82983, 3], [15703, 82983], .contexts [
        ⟨18205, false, false, [], []⟩,
        ⟨18199, true, false, [], [3]⟩,
        ⟨215, false, false, [82873], []⟩,
        ⟨216, false, false, [82873], []⟩,
        ⟨17751, false, false, [], [11]⟩,
        ⟨17754, false, false, [], [11]⟩,
        ⟨17749, false, false, [], [11]⟩,
        ⟨17750, false, false, [], [11]⟩,
        ⟨17750, false, false, [], [11]⟩,
        ⟨18195, false, false, [15703], []⟩,
        ⟨18203, false, false, [], []⟩,
        ⟨18204, false, false, [], []⟩,
        ⟨18201, false, false, [15703], []⟩,
        ⟨17753, true, false, [], [82983]⟩
      ]⟩,
    ⟨[82983, 5], [77713], .source 74785⟩,
    ⟨[82983, 5], [77713], .contexts [
        ⟨18207, false, false, [], []⟩,
        ⟨2787, false, false, [], []⟩,
        ⟨2788, false, false, [], []⟩
      ]⟩,
    ⟨[77713, 5], [82983], .contexts [
        ⟨18208, true, false, [], [5]⟩,
        ⟨28, false, false, [82983], []⟩,
        ⟨18198, false, false, [], []⟩
      ]⟩,
    ⟨[261, 82983], [261, 82983], .contexts []⟩,
    ⟨[261, 82983], [261, 82983], .contexts []⟩,
    ⟨[82983, 7], [82983, 7], .contexts []⟩,
    ⟨[82983, 7], [261, 82983], .contexts [
        ⟨18212, false, false, [], []⟩,
        ⟨18199, true, false, [], [7]⟩,
        ⟨647, false, false, [82873], []⟩,
        ⟨648, false, false, [82873], []⟩,
        ⟨17757, false, false, [], [11]⟩,
        ⟨17759, false, false, [], [11]⟩,
        ⟨17755, false, false, [], [11]⟩,
        ⟨17756, false, false, [], [11]⟩,
        ⟨17756, false, false, [], [11]⟩,
        ⟨18195, false, false, [261], []⟩,
        ⟨18210, false, false, [], []⟩,
        ⟨18211, false, false, [], []⟩,
        ⟨18201, false, false, [261], []⟩,
        ⟨1604, true, false, [], [82983]⟩
      ]⟩,
    ⟨[15699, 82983], [15699, 82983], .contexts []⟩,
    ⟨[82983, 13], [82985], .source 74787⟩,
    ⟨[82985], [82985], .contexts []⟩,
    ⟨[82985], [82985], .source 74788⟩,
    ⟨[82983, 13], [82985], .contexts [
        ⟨18215, false, false, [], []⟩,
        ⟨18216, false, false, [], []⟩,
        ⟨18217, false, false, [], []⟩,
        ⟨18217, false, false, [], []⟩
      ]⟩,
    ⟨[15703, 82985], [15703, 82985], .contexts []⟩,
    ⟨[82985], [82985], .source 74789⟩,
    ⟨[82985, 3], [15703, 82985], .contexts [
        ⟨18218, true, false, [], [3]⟩,
        ⟨63, false, false, [82983], []⟩,
        ⟨65, false, false, [82983], []⟩,
        ⟨18205, false, false, [], [13]⟩,
        ⟨18206, false, false, [], [13]⟩,
        ⟨18203, false, false, [], [13]⟩,
        ⟨18204, false, false, [], [13]⟩,
        ⟨18204, false, false, [], [13]⟩,
        ⟨18215, false, false, [15703], []⟩,
        ⟨18219, false, false, [], []⟩,
        ⟨18220, false, false, [15703], []⟩,
        ⟨17753, true, false, [], [82985]⟩
      ]⟩,
    ⟨[82985, 5], [77853], .source 74791⟩,
    ⟨[77853, 5], [82985], .contexts [
        ⟨18222, true, false, [], [5]⟩,
        ⟨28, false, false, [82985], []⟩,
        ⟨18217, false, false, [], []⟩
      ]⟩,
    ⟨[261, 82985], [261, 82985], .contexts []⟩,
    ⟨[82985, 11], [82869], .contexts [
        ⟨18218, true, false, [], [11]⟩,
        ⟨82, false, false, [82983], []⟩,
        ⟨83, false, false, [82983], []⟩,
        ⟨18196, false, false, [], [13]⟩,
        ⟨17737, false, false, [], [13]⟩,
        ⟨17738, false, false, [], [13]⟩,
        ⟨17738, false, false, [], [13]⟩,
        ⟨17763, false, false, [], []⟩,
        ⟨17686, false, false, [], []⟩,
        ⟨17687, false, false, [], []⟩,
        ⟨17687, false, false, [], []⟩,
        ⟨17761, false, false, [], []⟩,
        ⟨17762, false, false, [], []⟩
      ]⟩,
    ⟨[82869, 11], [82985], .contexts [
        ⟨18225, true, false, [], [11]⟩,
        ⟨53, false, false, [82985], []⟩,
        ⟨18217, false, false, [], []⟩
      ]⟩,
    ⟨[82985, 5], [77853], .source 74792⟩,
    ⟨[1313, 78009], [1313, 78009], .contexts []⟩,
    ⟨[1313, 78009], [1313, 78009], .source 74793⟩,
    ⟨[1313, 82859], [1313, 82859], .contexts []⟩,
    ⟨[82985], [82985], .source 74794⟩,
    ⟨[1312], [1312], .source 74795⟩,
    ⟨[82859, 1], [1311, 82985], .contexts [
        ⟨18230, true, false, [1312], [1]⟩,
        ⟨17594, true, false, [], [1]⟩,
        ⟨18229, true, false, [1312], [5, 1]⟩,
        ⟨18229, true, false, [1312], [5, 1]⟩,
        ⟨18228, true, false, [1312], [5, 1]⟩,
        ⟨3395, true, false, [1312], [5, 1]⟩,
        ⟨18227, true, false, [1312], [1, 5, 1]⟩,
        ⟨874, false, false, [1312, 82985], []⟩,
        ⟨18231, false, false, [1312], []⟩,
        ⟨18220, false, false, [1312], []⟩,
        ⟨18232, true, false, [], [82985]⟩,
        ⟨18232, true, false, [], [82985]⟩,
        ⟨3394, false, true, [], [82985]⟩
      ]⟩,
    ⟨[82985, 1], [1313, 82859], .contexts [
        ⟨18233, true, false, [1310], [1]⟩,
        ⟨8, false, false, [1310, 82859], []⟩,
        ⟨3394, true, false, [], [82859]⟩
      ]⟩,
    ⟨[503, 77983], [503, 77983], .contexts []⟩,
    ⟨[503, 77983], [503, 77983], .source 74796⟩,
    ⟨[503, 77995], [503, 77995], .contexts []⟩,
    ⟨[77995, 15], [505, 82985], .contexts [
        ⟨18237, true, false, [502], [15]⟩,
        ⟨3256, true, false, [], [15]⟩,
        ⟨18236, true, false, [502], [5, 15]⟩,
        ⟨18236, true, false, [502], [5, 15]⟩,
        ⟨18235, true, false, [502], [5, 15]⟩,
        ⟨3098, true, false, [502], [5, 15]⟩,
        ⟨18227, true, false, [502], [15, 5, 15]⟩,
        ⟨885, false, false, [502, 82985], []⟩,
        ⟨18231, false, false, [502], []⟩,
        ⟨18220, false, false, [502], []⟩,
        ⟨1660, true, false, [], [82985]⟩
      ]⟩,
    ⟨[78001, 3], [82987], .source 74798⟩]

/-- Exact literal claimed equations and contextual derivations, block 285. -/
def y322TCIndexRaw285 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82987, 3], [78001], .source 74799⟩,
    ⟨[78001, 3], [82987], .source 74800⟩,
    ⟨[82987], [82987], .source 74801⟩,
    ⟨[82987], [82987], .source 74802⟩,
    ⟨[78001, 3], [82987], .source 74803⟩,
    ⟨[78001, 1, 3], [315, 759, 77995], .source 74804⟩,
    ⟨[15745], [315, 759], .source 74805⟩,
    ⟨[315, 759, 77995], [15745, 77995], .contexts [
        ⟨18246, true, false, [], [77995]⟩
      ]⟩,
    ⟨[15745, 77995, 1], [15745, 317, 78001], .contexts [
        ⟨3324, false, false, [15745], []⟩
      ]⟩,
    ⟨[15745, 317, 78001], [15745, 317, 78001], .contexts []⟩,
    ⟨[15745, 317, 78001], [15745, 317, 78001], .contexts []⟩,
    ⟨[15747], [15745, 317], .source 74806⟩,
    ⟨[15745, 317, 78001], [15747, 78001], .contexts [
        ⟨18251, true, false, [], [78001]⟩
      ]⟩,
    ⟨[15747, 82987], [15747, 82987], .source 74807⟩,
    ⟨[15747, 82987], [15747, 82987], .source 74808⟩,
    ⟨[82987, 1], [82987, 1], .source 74809⟩,
    ⟨[82987], [82987], .source 74810⟩,
    ⟨[15747], [15747], .source 74811⟩,
    ⟨[323, 82987], [323, 82987], .contexts []⟩,
    ⟨[323, 82987], [323, 82987], .contexts []⟩,
    ⟨[78001, 5, 3, 5, 3], [323, 82987], .source 74812⟩,
    ⟨[82987, 5], [82987, 5], .contexts []⟩,
    ⟨[82987, 5], [323, 82987], .contexts [
        ⟨18261, false, false, [], []⟩,
        ⟨18244, true, false, [], [5]⟩,
        ⟨871, false, false, [78001], []⟩,
        ⟨873, false, false, [78001], []⟩,
        ⟨18260, false, false, [], []⟩,
        ⟨18256, false, false, [323], []⟩,
        ⟨3220, true, false, [], [82987]⟩
      ]⟩,
    ⟨[317, 82987], [317, 82987], .contexts []⟩,
    ⟨[317, 82987], [317, 82987], .contexts []⟩,
    ⟨[82987, 7], [82987, 7], .contexts []⟩,
    ⟨[82987, 7], [317, 82987], .contexts [
        ⟨18265, false, false, [], []⟩,
        ⟨18244, true, false, [], [7]⟩,
        ⟨140, false, false, [78001], []⟩,
        ⟨141, false, false, [78001], []⟩,
        ⟨3329, false, false, [], [3]⟩,
        ⟨3330, false, false, [], [3]⟩,
        ⟨3327, false, false, [], [3]⟩,
        ⟨3328, false, false, [], [3]⟩,
        ⟨3328, false, false, [], [3]⟩,
        ⟨18239, false, false, [317], []⟩,
        ⟨18263, false, false, [], []⟩,
        ⟨18264, false, false, [], []⟩,
        ⟨18256, false, false, [317], []⟩,
        ⟨1182, true, false, [], [82987]⟩
      ]⟩,
    ⟨[82989], [82987, 9], .source 74813⟩,
    ⟨[82987, 9], [82989], .contexts [
        ⟨18267, true, false, [], []⟩
      ]⟩,
    ⟨[82989, 9], [82987], .contexts [
        ⟨18268, true, false, [], [9]⟩,
        ⟨46, false, false, [82987], []⟩,
        ⟨18243, false, false, [], []⟩
      ]⟩,
    ⟨[82989], [82989], .contexts []⟩,
    ⟨[82989], [82989], .source 74814⟩,
    ⟨[82987, 9], [82989], .contexts [
        ⟨18268, false, false, [], []⟩,
        ⟨18270, false, false, [], []⟩,
        ⟨18271, false, false, [], []⟩,
        ⟨18271, false, false, [], []⟩
      ]⟩,
    ⟨[78001, 9], [78119], .contexts [
        ⟨3692, false, false, [], []⟩
      ]⟩,
    ⟨[82989, 3], [82989, 3], .contexts []⟩,
    ⟨[82989, 3], [78119], .contexts [
        ⟨18274, false, false, [], []⟩,
        ⟨18272, true, false, [], [3]⟩,
        ⟨196, false, false, [82987], []⟩,
        ⟨197, false, false, [82987], []⟩,
        ⟨18240, false, false, [], [9]⟩,
        ⟨3320, false, false, [], [9]⟩,
        ⟨3321, false, false, [], [9]⟩,
        ⟨3321, false, false, [], [9]⟩,
        ⟨18273, false, false, [], []⟩,
        ⟨3682, false, false, [], []⟩,
        ⟨3683, false, false, [], []⟩,
        ⟨3683, false, false, [], []⟩,
        ⟨3889, false, false, [], []⟩,
        ⟨3890, false, false, [], []⟩
      ]⟩,
    ⟨[78119, 3], [82989], .contexts [
        ⟨18275, true, false, [], [3]⟩,
        ⟨20, false, false, [82989], []⟩,
        ⟨18271, false, false, [], []⟩
      ]⟩,
    ⟨[82987, 5], [323, 82987], .contexts [
        ⟨18261, false, false, [], []⟩,
        ⟨18262, false, false, [], []⟩,
        ⟨18258, false, false, [], []⟩,
        ⟨18259, false, false, [], []⟩,
        ⟨18259, false, false, [], []⟩
      ]⟩,
    ⟨[323, 82989], [323, 82989], .contexts []⟩,
    ⟨[323, 82989], [323, 82989], .contexts []⟩,
    ⟨[82989, 5], [82989, 5], .contexts []⟩,
    ⟨[82989], [82989], .contexts []⟩,
    ⟨[82989, 5], [323, 82989], .contexts [
        ⟨18280, false, false, [], []⟩,
        ⟨18272, true, false, [], [5]⟩,
        ⟨1079, false, false, [82987], []⟩,
        ⟨1080, false, false, [82987], []⟩,
        ⟨18277, false, false, [], [9]⟩,
        ⟨18268, false, false, [323], []⟩,
        ⟨18278, false, false, [], []⟩,
        ⟨18279, false, false, [], []⟩,
        ⟨18281, false, false, [323], []⟩,
        ⟨3220, true, false, [], [82989]⟩
      ]⟩,
    ⟨[82987, 7], [317, 82987], .contexts [
        ⟨18265, false, false, [], []⟩,
        ⟨18266, false, false, [], []⟩,
        ⟨18263, false, false, [], []⟩,
        ⟨18264, false, false, [], []⟩,
        ⟨18264, false, false, [], []⟩
      ]⟩,
    ⟨[317, 82989], [317, 82989], .contexts []⟩,
    ⟨[317, 82989], [317, 82989], .contexts []⟩,
    ⟨[82989, 7], [82989, 7], .contexts []⟩,
    ⟨[82989, 7], [317, 82989], .contexts [
        ⟨18286, false, false, [], []⟩,
        ⟨18272, true, false, [], [7]⟩,
        ⟨1084, false, false, [82987], []⟩,
        ⟨1085, false, false, [82987], []⟩,
        ⟨18283, false, false, [], [9]⟩,
        ⟨18268, false, false, [317], []⟩,
        ⟨18284, false, false, [], []⟩,
        ⟨18285, false, false, [], []⟩,
        ⟨18281, false, false, [317], []⟩,
        ⟨1182, true, false, [], [82989]⟩
      ]⟩,
    ⟨[82991], [82989, 11], .source 74815⟩,
    ⟨[82989, 11], [82991], .contexts [
        ⟨18288, true, false, [], []⟩
      ]⟩,
    ⟨[82991, 11], [82989], .contexts [
        ⟨18289, true, false, [], [11]⟩,
        ⟨53, false, false, [82989], []⟩,
        ⟨18271, false, false, [], []⟩
      ]⟩,
    ⟨[82991], [82991], .contexts []⟩,
    ⟨[82991], [82991], .source 74816⟩,
    ⟨[82989, 11], [82991], .contexts [
        ⟨18289, false, false, [], []⟩,
        ⟨18291, false, false, [], []⟩,
        ⟨18292, false, false, [], []⟩,
        ⟨18292, false, false, [], []⟩
      ]⟩,
    ⟨[82989, 3], [78119], .contexts [
        ⟨18274, false, false, [], []⟩,
        ⟨18275, false, false, [], []⟩,
        ⟨3682, false, false, [], []⟩,
        ⟨3683, false, false, [], []⟩,
        ⟨3683, false, false, [], []⟩
      ]⟩,
    ⟨[78119, 11], [78265], .contexts [
        ⟨3892, false, false, [], []⟩
      ]⟩,
    ⟨[82991, 3], [82991, 3], .contexts []⟩,
    ⟨[82991, 3], [78265], .contexts [
        ⟨18296, false, false, [], []⟩,
        ⟨18293, true, false, [], [3]⟩,
        ⟨215, false, false, [82989], []⟩,
        ⟨216, false, false, [82989], []⟩,
        ⟨18294, false, false, [], [11]⟩,
        ⟨18295, false, false, [], []⟩,
        ⟨3883, false, false, [], []⟩,
        ⟨3884, false, false, [], []⟩,
        ⟨3884, false, false, [], []⟩,
        ⟨4341, false, false, [], []⟩,
        ⟨4342, false, false, [], []⟩
      ]⟩,
    ⟨[78265, 3], [82991], .contexts [
        ⟨18297, true, false, [], [3]⟩,
        ⟨20, false, false, [82991], []⟩,
        ⟨18292, false, false, [], []⟩
      ]⟩,
    ⟨[82989, 5], [323, 82989], .contexts [
        ⟨18280, false, false, [], []⟩,
        ⟨18282, false, false, [], []⟩,
        ⟨18278, false, false, [], []⟩,
        ⟨18279, false, false, [], []⟩,
        ⟨18279, false, false, [], []⟩
      ]⟩,
    ⟨[323, 82991], [323, 82991], .contexts []⟩,
    ⟨[323, 82991], [323, 82991], .contexts []⟩,
    ⟨[82991, 5], [82991, 5], .contexts []⟩,
    ⟨[82991], [82991], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 286. -/
def y322TCIndexRaw286 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82991, 5], [323, 82991], .contexts [
        ⟨18302, false, false, [], []⟩,
        ⟨18293, true, false, [], [5]⟩,
        ⟨642, false, false, [82989], []⟩,
        ⟨643, false, false, [82989], []⟩,
        ⟨18299, false, false, [], [11]⟩,
        ⟨18289, false, false, [323], []⟩,
        ⟨18300, false, false, [], []⟩,
        ⟨18301, false, false, [], []⟩,
        ⟨18303, false, false, [323], []⟩,
        ⟨3220, true, false, [], [82991]⟩
      ]⟩,
    ⟨[82989, 7], [317, 82989], .contexts [
        ⟨18286, false, false, [], []⟩,
        ⟨18287, false, false, [], []⟩,
        ⟨18284, false, false, [], []⟩,
        ⟨18285, false, false, [], []⟩,
        ⟨18285, false, false, [], []⟩
      ]⟩,
    ⟨[317, 82991], [317, 82991], .contexts []⟩,
    ⟨[317, 82991], [317, 82991], .contexts []⟩,
    ⟨[82991, 7], [82991, 7], .contexts []⟩,
    ⟨[82991, 7], [317, 82991], .contexts [
        ⟨18308, false, false, [], []⟩,
        ⟨18293, true, false, [], [7]⟩,
        ⟨647, false, false, [82989], []⟩,
        ⟨648, false, false, [82989], []⟩,
        ⟨18305, false, false, [], [11]⟩,
        ⟨18289, false, false, [317], []⟩,
        ⟨18306, false, false, [], []⟩,
        ⟨18307, false, false, [], []⟩,
        ⟨18303, false, false, [317], []⟩,
        ⟨1182, true, false, [], [82991]⟩
      ]⟩,
    ⟨[82993], [82991, 1], .source 74817⟩,
    ⟨[82991, 1], [82993], .contexts [
        ⟨18310, true, false, [], []⟩
      ]⟩,
    ⟨[82993, 1], [82991], .contexts [
        ⟨18311, true, false, [], [1]⟩,
        ⟨8, false, false, [82991], []⟩,
        ⟨18292, false, false, [], []⟩
      ]⟩,
    ⟨[82991, 1], [82993], .contexts [
        ⟨18311, false, false, [], []⟩
      ]⟩,
    ⟨[82993], [82993], .contexts []⟩,
    ⟨[82993], [82993], .source 74818⟩,
    ⟨[82991, 1], [82993], .contexts [
        ⟨18313, false, false, [], []⟩,
        ⟨18314, false, false, [], []⟩,
        ⟨18315, false, false, [], []⟩,
        ⟨18315, false, false, [], []⟩
      ]⟩,
    ⟨[82991, 5], [323, 82991], .contexts [
        ⟨18302, false, false, [], []⟩,
        ⟨18304, false, false, [], []⟩,
        ⟨18300, false, false, [], []⟩,
        ⟨18301, false, false, [], []⟩,
        ⟨18301, false, false, [], []⟩
      ]⟩,
    ⟨[323, 82993], [323, 82993], .contexts []⟩,
    ⟨[323, 82993], [323, 82993], .contexts []⟩,
    ⟨[82993, 5], [82993, 5], .contexts []⟩,
    ⟨[82993], [82993], .contexts []⟩,
    ⟨[82993, 5], [323, 82993], .contexts [
        ⟨18320, false, false, [], []⟩,
        ⟨18316, true, false, [], [5]⟩,
        ⟨98, false, false, [82991], []⟩,
        ⟨99, false, false, [82991], []⟩,
        ⟨18317, false, false, [], [1]⟩,
        ⟨18311, false, false, [323], []⟩,
        ⟨18318, false, false, [], []⟩,
        ⟨18319, false, false, [], []⟩,
        ⟨18321, false, false, [323], []⟩,
        ⟨3220, true, false, [], [82993]⟩
      ]⟩,
    ⟨[82991, 7], [317, 82991], .contexts [
        ⟨18308, false, false, [], []⟩,
        ⟨18309, false, false, [], []⟩,
        ⟨18306, false, false, [], []⟩,
        ⟨18307, false, false, [], []⟩,
        ⟨18307, false, false, [], []⟩
      ]⟩,
    ⟨[317, 82993], [317, 82993], .contexts []⟩,
    ⟨[317, 82993], [317, 82993], .contexts []⟩,
    ⟨[82993, 7], [82993, 7], .contexts []⟩,
    ⟨[82993, 7], [317, 82993], .contexts [
        ⟨18326, false, false, [], []⟩,
        ⟨18316, true, false, [], [7]⟩,
        ⟨104, false, false, [82991], []⟩,
        ⟨105, false, false, [82991], []⟩,
        ⟨18323, false, false, [], [1]⟩,
        ⟨18311, false, false, [317], []⟩,
        ⟨18324, false, false, [], []⟩,
        ⟨18325, false, false, [], []⟩,
        ⟨18321, false, false, [317], []⟩,
        ⟨1182, true, false, [], [82993]⟩
      ]⟩,
    ⟨[82995], [82993, 13], .source 74819⟩,
    ⟨[82993, 13], [82995], .contexts [
        ⟨18328, true, false, [], []⟩
      ]⟩,
    ⟨[82993, 13], [82995], .contexts [
        ⟨18329, false, false, [], []⟩
      ]⟩,
    ⟨[82995], [82995], .contexts []⟩,
    ⟨[82995], [82995], .source 74820⟩,
    ⟨[82993, 13], [82995], .contexts [
        ⟨18330, false, false, [], []⟩,
        ⟨18331, false, false, [], []⟩,
        ⟨18332, false, false, [], []⟩,
        ⟨18332, false, false, [], []⟩
      ]⟩,
    ⟨[323, 82995], [323, 82995], .contexts []⟩,
    ⟨[323, 82995], [323, 82995], .contexts []⟩,
    ⟨[82995, 5], [82995, 5], .contexts []⟩,
    ⟨[82995], [82995], .contexts []⟩,
    ⟨[82995, 5], [323, 82995], .contexts [
        ⟨18336, false, false, [], []⟩,
        ⟨18333, true, false, [], [5]⟩,
        ⟨68, false, false, [82993], []⟩,
        ⟨69, false, false, [82993], []⟩,
        ⟨18320, false, false, [], [13]⟩,
        ⟨18322, false, false, [], [13]⟩,
        ⟨18318, false, false, [], [13]⟩,
        ⟨18319, false, false, [], [13]⟩,
        ⟨18319, false, false, [], [13]⟩,
        ⟨18329, false, false, [323], []⟩,
        ⟨18334, false, false, [], []⟩,
        ⟨18335, false, false, [], []⟩,
        ⟨18337, false, false, [323], []⟩,
        ⟨3220, true, false, [], [82995]⟩
      ]⟩,
    ⟨[317, 82995], [317, 82995], .contexts []⟩,
    ⟨[317, 82995], [317, 82995], .contexts []⟩,
    ⟨[82995, 7], [82995, 7], .contexts []⟩,
    ⟨[82995, 7], [317, 82995], .contexts [
        ⟨18341, false, false, [], []⟩,
        ⟨18333, true, false, [], [7]⟩,
        ⟨73, false, false, [82993], []⟩,
        ⟨74, false, false, [82993], []⟩,
        ⟨18326, false, false, [], [13]⟩,
        ⟨18327, false, false, [], [13]⟩,
        ⟨18324, false, false, [], [13]⟩,
        ⟨18325, false, false, [], [13]⟩,
        ⟨18325, false, false, [], [13]⟩,
        ⟨18329, false, false, [317], []⟩,
        ⟨18339, false, false, [], []⟩,
        ⟨18340, false, false, [], []⟩,
        ⟨18337, false, false, [317], []⟩,
        ⟨1182, true, false, [], [82995]⟩
      ]⟩,
    ⟨[82997], [82995, 15], .source 74821⟩,
    ⟨[82995, 15], [82997], .contexts [
        ⟨18343, true, false, [], []⟩
      ]⟩,
    ⟨[82997], [82997], .contexts []⟩,
    ⟨[82997], [82997], .source 74822⟩,
    ⟨[82995, 15], [82997], .contexts [
        ⟨18344, false, false, [], []⟩,
        ⟨18345, false, false, [], []⟩,
        ⟨18346, false, false, [], []⟩,
        ⟨18346, false, false, [], []⟩
      ]⟩,
    ⟨[82995, 5], [323, 82995], .contexts [
        ⟨18336, false, false, [], []⟩,
        ⟨18338, false, false, [], []⟩,
        ⟨18334, false, false, [], []⟩,
        ⟨18335, false, false, [], []⟩,
        ⟨18335, false, false, [], []⟩
      ]⟩,
    ⟨[323, 82997], [323, 82997], .contexts []⟩,
    ⟨[323, 82997], [323, 82997], .contexts []⟩,
    ⟨[82997, 5], [82997, 5], .contexts []⟩,
    ⟨[82997], [82997], .contexts []⟩,
    ⟨[82997, 5], [323, 82997], .contexts [
        ⟨18351, false, false, [], []⟩,
        ⟨18347, true, false, [], [5]⟩,
        ⟨27, false, false, [82995], []⟩,
        ⟨30, false, false, [82995], []⟩,
        ⟨18348, false, false, [], [15]⟩,
        ⟨18344, false, false, [323], []⟩,
        ⟨18349, false, false, [], []⟩,
        ⟨18350, false, false, [], []⟩,
        ⟨18352, false, false, [323], []⟩,
        ⟨3220, true, false, [], [82997]⟩
      ]⟩,
    ⟨[82995, 7], [317, 82995], .contexts [
        ⟨18341, false, false, [], []⟩,
        ⟨18342, false, false, [], []⟩,
        ⟨18339, false, false, [], []⟩,
        ⟨18340, false, false, [], []⟩,
        ⟨18340, false, false, [], []⟩
      ]⟩,
    ⟨[317, 82997], [317, 82997], .contexts []⟩,
    ⟨[317, 82997], [317, 82997], .contexts []⟩,
    ⟨[82997, 7], [82997, 7], .contexts []⟩,
    ⟨[82997, 7], [317, 82997], .contexts [
        ⟨18357, false, false, [], []⟩,
        ⟨18347, true, false, [], [7]⟩,
        ⟨37, false, false, [82995], []⟩,
        ⟨40, false, false, [82995], []⟩,
        ⟨18354, false, false, [], [15]⟩,
        ⟨18344, false, false, [317], []⟩,
        ⟨18355, false, false, [], []⟩,
        ⟨18356, false, false, [], []⟩,
        ⟨18352, false, false, [317], []⟩,
        ⟨1182, true, false, [], [82997]⟩
      ]⟩,
    ⟨[82999], [82997, 1], .source 74823⟩,
    ⟨[82997, 1], [82999], .contexts [
        ⟨18359, true, false, [], []⟩
      ]⟩,
    ⟨[82999, 1], [82997], .contexts [
        ⟨18360, true, false, [], [1]⟩,
        ⟨8, false, false, [82997], []⟩,
        ⟨18346, false, false, [], []⟩
      ]⟩,
    ⟨[82997, 1], [82999], .contexts [
        ⟨18360, false, false, [], []⟩
      ]⟩,
    ⟨[82999], [82999], .contexts []⟩,
    ⟨[82999], [82999], .source 74824⟩,
    ⟨[82997, 1], [82999], .contexts [
        ⟨18362, false, false, [], []⟩,
        ⟨18363, false, false, [], []⟩,
        ⟨18364, false, false, [], []⟩,
        ⟨18364, false, false, [], []⟩
      ]⟩,
    ⟨[323, 82999], [323, 82999], .contexts []⟩,
    ⟨[323, 82999], [323, 82999], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 287. -/
def y322TCIndexRaw287 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82999], [82999], .contexts []⟩,
    ⟨[82999, 5], [323, 82999], .contexts [
        ⟨18365, true, false, [], [5]⟩,
        ⟨98, false, false, [82997], []⟩,
        ⟨99, false, false, [82997], []⟩,
        ⟨18351, false, false, [], [1]⟩,
        ⟨18353, false, false, [], [1]⟩,
        ⟨18349, false, false, [], [1]⟩,
        ⟨18350, false, false, [], [1]⟩,
        ⟨18350, false, false, [], [1]⟩,
        ⟨18360, false, false, [323], []⟩,
        ⟨18366, false, false, [], []⟩,
        ⟨18367, false, false, [], []⟩,
        ⟨18368, false, false, [323], []⟩,
        ⟨3220, true, false, [], [82999]⟩
      ]⟩,
    ⟨[317, 82999], [317, 82999], .contexts []⟩,
    ⟨[317, 82999], [317, 82999], .contexts []⟩,
    ⟨[82999, 7], [82999, 7], .contexts []⟩,
    ⟨[82999, 7], [317, 82999], .contexts [
        ⟨18372, false, false, [], []⟩,
        ⟨18365, true, false, [], [7]⟩,
        ⟨104, false, false, [82997], []⟩,
        ⟨105, false, false, [82997], []⟩,
        ⟨18357, false, false, [], [1]⟩,
        ⟨18358, false, false, [], [1]⟩,
        ⟨18355, false, false, [], [1]⟩,
        ⟨18356, false, false, [], [1]⟩,
        ⟨18356, false, false, [], [1]⟩,
        ⟨18360, false, false, [317], []⟩,
        ⟨18370, false, false, [], []⟩,
        ⟨18371, false, false, [], []⟩,
        ⟨18368, false, false, [317], []⟩,
        ⟨1182, true, false, [], [82999]⟩
      ]⟩,
    ⟨[83001], [82999, 3], .source 74825⟩,
    ⟨[82999, 3], [83001], .contexts [
        ⟨18374, true, false, [], []⟩
      ]⟩,
    ⟨[83001, 3], [82999], .contexts [
        ⟨18375, true, false, [], [3]⟩,
        ⟨20, false, false, [82999], []⟩,
        ⟨18364, false, false, [], []⟩
      ]⟩,
    ⟨[83001], [83001], .contexts []⟩,
    ⟨[83001], [83001], .source 74826⟩,
    ⟨[317, 83001], [317, 83001], .contexts []⟩,
    ⟨[317, 83001], [317, 83001], .contexts []⟩,
    ⟨[83001], [83001], .contexts []⟩,
    ⟨[83001, 7], [317, 83001], .contexts [
        ⟨18378, true, false, [], [7]⟩,
        ⟨18378, true, false, [], [7]⟩,
        ⟨18377, true, false, [], [7]⟩,
        ⟨18375, true, false, [], [7]⟩,
        ⟨140, false, false, [82999], []⟩,
        ⟨141, false, false, [82999], []⟩,
        ⟨18372, false, false, [], [3]⟩,
        ⟨18373, false, false, [], [3]⟩,
        ⟨18370, false, false, [], [3]⟩,
        ⟨18371, false, false, [], [3]⟩,
        ⟨18371, false, false, [], [3]⟩,
        ⟨18375, false, false, [317], []⟩,
        ⟨18379, false, false, [], []⟩,
        ⟨18380, false, false, [], []⟩,
        ⟨18381, false, false, [317], []⟩,
        ⟨1182, true, false, [], [83001]⟩
      ]⟩,
    ⟨[83003], [83001, 5], .source 74827⟩,
    ⟨[83001, 5], [83003], .contexts [
        ⟨18383, true, false, [], []⟩
      ]⟩,
    ⟨[83003, 5], [83001], .contexts [
        ⟨18384, true, false, [], [5]⟩,
        ⟨28, false, false, [83001], []⟩,
        ⟨18378, false, false, [], []⟩
      ]⟩,
    ⟨[83003], [83003], .contexts []⟩,
    ⟨[83003], [83003], .source 74828⟩,
    ⟨[83001, 5], [83003], .contexts [
        ⟨18384, false, false, [], []⟩,
        ⟨18386, false, false, [], []⟩,
        ⟨18387, false, false, [], []⟩,
        ⟨18387, false, false, [], []⟩
      ]⟩,
    ⟨[83001, 3], [82999], .contexts [
        ⟨18376, false, false, [], []⟩,
        ⟨18363, false, false, [], []⟩,
        ⟨18364, false, false, [], []⟩,
        ⟨18364, false, false, [], []⟩
      ]⟩,
    ⟨[323, 83003], [323, 83003], .contexts []⟩,
    ⟨[323, 83003], [323, 83003], .contexts []⟩,
    ⟨[83003, 3], [83003, 3], .contexts []⟩,
    ⟨[83003], [83003], .contexts []⟩,
    ⟨[83003, 3], [323, 83003], .contexts [
        ⟨18392, false, false, [], []⟩,
        ⟨18388, true, false, [], [3]⟩,
        ⟨166, false, false, [83001], []⟩,
        ⟨169, false, false, [83001], []⟩,
        ⟨18389, false, false, [], [5, 3, 5]⟩,
        ⟨18369, false, false, [], [3, 5]⟩,
        ⟨18366, false, false, [], [3, 5]⟩,
        ⟨18367, false, false, [], [3, 5]⟩,
        ⟨18367, false, false, [], [3, 5]⟩,
        ⟨18375, false, false, [323], [5]⟩,
        ⟨18384, false, false, [323], []⟩,
        ⟨18390, false, false, [], []⟩,
        ⟨18391, false, false, [], []⟩,
        ⟨18393, false, false, [323], []⟩,
        ⟨3220, true, false, [], [83003]⟩
      ]⟩,
    ⟨[83005], [83003, 1], .source 74829⟩,
    ⟨[83003, 1], [83005], .contexts [
        ⟨18395, true, false, [], []⟩
      ]⟩,
    ⟨[83005, 1], [83003], .contexts [
        ⟨18396, true, false, [], [1]⟩,
        ⟨8, false, false, [83003], []⟩,
        ⟨18387, false, false, [], []⟩
      ]⟩,
    ⟨[83007], [83005, 9], .source 74830⟩,
    ⟨[83005, 9], [83007], .contexts [
        ⟨18398, true, false, [], []⟩
      ]⟩,
    ⟨[83005], [83005], .source 74831⟩,
    ⟨[83009], [83007, 11], .source 74832⟩,
    ⟨[83007, 11], [83009], .contexts [
        ⟨18401, true, false, [], []⟩
      ]⟩,
    ⟨[83007], [83007], .source 74833⟩,
    ⟨[83009, 11], [83007], .contexts [
        ⟨18402, true, false, [], [11]⟩,
        ⟨53, false, false, [83007], []⟩,
        ⟨18403, false, false, [], []⟩
      ]⟩,
    ⟨[83011], [83009, 1], .source 74834⟩,
    ⟨[83009, 1], [83011], .contexts [
        ⟨18405, true, false, [], []⟩
      ]⟩,
    ⟨[83009], [83009], .source 74835⟩,
    ⟨[83013], [83011, 13], .source 74836⟩,
    ⟨[83011, 13], [83013], .contexts [
        ⟨18408, true, false, [], []⟩
      ]⟩,
    ⟨[83011], [83011], .source 74837⟩,
    ⟨[83013, 13], [83011], .contexts [
        ⟨18409, true, false, [], [13]⟩,
        ⟨59, false, false, [83011], []⟩,
        ⟨18410, false, false, [], []⟩
      ]⟩,
    ⟨[83015], [83013, 15], .source 74838⟩,
    ⟨[83013, 15], [83015], .contexts [
        ⟨18412, true, false, [], []⟩
      ]⟩,
    ⟨[83013], [83013], .source 74839⟩,
    ⟨[83015, 15], [83013], .contexts [
        ⟨18413, true, false, [], [15]⟩,
        ⟨1, false, false, [83013], []⟩,
        ⟨18414, false, false, [], []⟩
      ]⟩,
    ⟨[83017], [83015, 1], .source 74840⟩,
    ⟨[83015, 1], [83017], .contexts [
        ⟨18416, true, false, [], []⟩
      ]⟩,
    ⟨[83015], [83015], .source 74841⟩,
    ⟨[83017, 1], [83015], .contexts [
        ⟨18417, true, false, [], [1]⟩,
        ⟨8, false, false, [83015], []⟩,
        ⟨18418, false, false, [], []⟩
      ]⟩,
    ⟨[83019], [83017, 3], .source 74842⟩,
    ⟨[83017, 3], [83019], .contexts [
        ⟨18420, true, false, [], []⟩
      ]⟩,
    ⟨[83017], [83017], .source 74843⟩,
    ⟨[83019, 3], [83017], .contexts [
        ⟨18421, true, false, [], [3]⟩,
        ⟨20, false, false, [83017], []⟩,
        ⟨18422, false, false, [], []⟩
      ]⟩,
    ⟨[83021], [83019, 5], .source 74844⟩,
    ⟨[83019, 5], [83021], .contexts [
        ⟨18424, true, false, [], []⟩
      ]⟩,
    ⟨[83019], [83019], .source 74845⟩,
    ⟨[83021, 5], [83019], .contexts [
        ⟨18425, true, false, [], [5]⟩,
        ⟨28, false, false, [83019], []⟩,
        ⟨18426, false, false, [], []⟩
      ]⟩,
    ⟨[83023], [83021, 1], .source 74846⟩,
    ⟨[83021, 1], [83023], .contexts [
        ⟨18428, true, false, [], []⟩
      ]⟩,
    ⟨[83021], [83021], .source 74847⟩,
    ⟨[83023, 1], [83021], .contexts [
        ⟨18429, true, false, [], [1]⟩,
        ⟨8, false, false, [83021], []⟩,
        ⟨18430, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 288. -/
def y322TCIndexRaw288 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83025], [83023, 9], .source 74848⟩,
    ⟨[83023, 9], [83025], .contexts [
        ⟨18432, true, false, [], []⟩
      ]⟩,
    ⟨[83023], [83023], .source 74849⟩,
    ⟨[83025, 9], [83023], .contexts [
        ⟨18433, true, false, [], [9]⟩,
        ⟨46, false, false, [83023], []⟩,
        ⟨18434, false, false, [], []⟩
      ]⟩,
    ⟨[83027], [83025, 11], .source 74850⟩,
    ⟨[83025, 11], [83027], .contexts [
        ⟨18436, true, false, [], []⟩
      ]⟩,
    ⟨[83025], [83025], .source 74851⟩,
    ⟨[83029], [83027, 1], .source 74852⟩,
    ⟨[83027, 1], [83029], .contexts [
        ⟨18439, true, false, [], []⟩
      ]⟩,
    ⟨[83027], [83027], .source 74853⟩,
    ⟨[83031], [83029, 13], .source 74854⟩,
    ⟨[83029, 13], [83031], .contexts [
        ⟨18442, true, false, [], []⟩
      ]⟩,
    ⟨[83029], [83029], .source 74855⟩,
    ⟨[83033], [83031, 15], .source 74856⟩,
    ⟨[83031, 15], [83033], .contexts [
        ⟨18445, true, false, [], []⟩
      ]⟩,
    ⟨[83031], [83031], .source 74857⟩,
    ⟨[83035], [83033, 1], .source 74858⟩,
    ⟨[83033, 1], [83035], .contexts [
        ⟨18448, true, false, [], []⟩
      ]⟩,
    ⟨[83033], [83033], .source 74859⟩,
    ⟨[83035, 1], [83033], .contexts [
        ⟨18449, true, false, [], [1]⟩,
        ⟨8, false, false, [83033], []⟩,
        ⟨18450, false, false, [], []⟩
      ]⟩,
    ⟨[83037], [83035, 3], .source 74860⟩,
    ⟨[83035, 3], [83037], .contexts [
        ⟨18452, true, false, [], []⟩
      ]⟩,
    ⟨[83035], [83035], .source 74861⟩,
    ⟨[83037, 3], [83035], .contexts [
        ⟨18453, true, false, [], [3]⟩,
        ⟨20, false, false, [83035], []⟩,
        ⟨18454, false, false, [], []⟩
      ]⟩,
    ⟨[83039], [83037, 5], .source 74862⟩,
    ⟨[83037, 5], [83039], .contexts [
        ⟨18456, true, false, [], []⟩
      ]⟩,
    ⟨[83037], [83037], .source 74863⟩,
    ⟨[83039, 5], [83037], .contexts [
        ⟨18457, true, false, [], [5]⟩,
        ⟨28, false, false, [83037], []⟩,
        ⟨18458, false, false, [], []⟩
      ]⟩,
    ⟨[83041], [83039, 1], .source 74864⟩,
    ⟨[83039, 1], [83041], .contexts [
        ⟨18460, true, false, [], []⟩
      ]⟩,
    ⟨[83039], [83039], .source 74865⟩,
    ⟨[83043], [83041, 9], .source 74866⟩,
    ⟨[83041, 9], [83043], .contexts [
        ⟨18463, true, false, [], []⟩
      ]⟩,
    ⟨[83041], [83041], .source 74867⟩,
    ⟨[83043, 9], [83041], .contexts [
        ⟨18464, true, false, [], [9]⟩,
        ⟨46, false, false, [83041], []⟩,
        ⟨18465, false, false, [], []⟩
      ]⟩,
    ⟨[83045], [83043, 11], .source 74868⟩,
    ⟨[83043, 11], [83045], .contexts [
        ⟨18467, true, false, [], []⟩
      ]⟩,
    ⟨[83043], [83043], .source 74869⟩,
    ⟨[83047], [83045, 1], .source 74870⟩,
    ⟨[83045, 1], [83047], .contexts [
        ⟨18470, true, false, [], []⟩
      ]⟩,
    ⟨[83045], [83045], .source 74871⟩,
    ⟨[83049], [83047, 13], .source 74872⟩,
    ⟨[83047, 13], [83049], .contexts [
        ⟨18473, true, false, [], []⟩
      ]⟩,
    ⟨[83047], [83047], .source 74873⟩,
    ⟨[83051], [83049, 15], .source 74874⟩,
    ⟨[83049, 15], [83051], .contexts [
        ⟨18476, true, false, [], []⟩
      ]⟩,
    ⟨[83049], [83049], .source 74875⟩,
    ⟨[83051, 15], [83049], .contexts [
        ⟨18477, true, false, [], [15]⟩,
        ⟨1, false, false, [83049], []⟩,
        ⟨18478, false, false, [], []⟩
      ]⟩,
    ⟨[83053], [83051, 1], .source 74876⟩,
    ⟨[83051, 1], [83053], .contexts [
        ⟨18480, true, false, [], []⟩
      ]⟩,
    ⟨[83051], [83051], .source 74877⟩,
    ⟨[83053, 1], [83051], .contexts [
        ⟨18481, true, false, [], [1]⟩,
        ⟨8, false, false, [83051], []⟩,
        ⟨18482, false, false, [], []⟩
      ]⟩,
    ⟨[83055], [83053, 3], .source 74878⟩,
    ⟨[83053], [83053], .source 74879⟩,
    ⟨[83055, 3], [83053], .contexts [
        ⟨18484, false, false, [], [3]⟩,
        ⟨20, false, false, [83053], []⟩,
        ⟨18485, false, false, [], []⟩
      ]⟩,
    ⟨[83057], [83055, 5], .source 74880⟩,
    ⟨[83055, 5], [83057], .contexts [
        ⟨18487, true, false, [], []⟩
      ]⟩,
    ⟨[83055], [83055], .source 74881⟩,
    ⟨[83057, 5], [83055], .contexts [
        ⟨18488, true, false, [], [5]⟩,
        ⟨28, false, false, [83055], []⟩,
        ⟨18489, false, false, [], []⟩
      ]⟩,
    ⟨[83059], [83057, 1], .source 74882⟩,
    ⟨[83057, 1], [83059], .contexts [
        ⟨18491, true, false, [], []⟩
      ]⟩,
    ⟨[83057], [83057], .source 74883⟩,
    ⟨[83059, 1], [83057], .contexts [
        ⟨18492, true, false, [], [1]⟩,
        ⟨8, false, false, [83057], []⟩,
        ⟨18493, false, false, [], []⟩
      ]⟩,
    ⟨[83061], [83059, 9], .source 74884⟩]

/-- Exact literal claimed equations and contextual derivations, block 289. -/
def y322TCIndexRaw289 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83059, 9], [83061], .contexts [
        ⟨18495, true, false, [], []⟩
      ]⟩,
    ⟨[83059], [83059], .source 74885⟩,
    ⟨[83063], [83061, 11], .source 74886⟩,
    ⟨[83061, 11], [83063], .contexts [
        ⟨18498, true, false, [], []⟩
      ]⟩,
    ⟨[83061], [83061], .source 74887⟩,
    ⟨[83063, 11], [83061], .contexts [
        ⟨18499, true, false, [], [11]⟩,
        ⟨53, false, false, [83061], []⟩,
        ⟨18500, false, false, [], []⟩
      ]⟩,
    ⟨[83065], [83063, 1], .source 74888⟩,
    ⟨[83063, 1], [83065], .contexts [
        ⟨18502, true, false, [], []⟩
      ]⟩,
    ⟨[83063], [83063], .source 74889⟩,
    ⟨[83065, 1], [83063], .contexts [
        ⟨18503, true, false, [], [1]⟩,
        ⟨8, false, false, [83063], []⟩,
        ⟨18504, false, false, [], []⟩
      ]⟩,
    ⟨[83067], [83065, 13], .source 74890⟩,
    ⟨[83065, 13], [83067], .contexts [
        ⟨18506, true, false, [], []⟩
      ]⟩,
    ⟨[83065], [83065], .source 74891⟩,
    ⟨[83067, 13], [83065], .contexts [
        ⟨18507, true, false, [], [13]⟩,
        ⟨59, false, false, [83065], []⟩,
        ⟨18508, false, false, [], []⟩
      ]⟩,
    ⟨[83069], [83067, 15], .source 74892⟩,
    ⟨[83067, 15], [83069], .contexts [
        ⟨18510, true, false, [], []⟩
      ]⟩,
    ⟨[83067], [83067], .source 74893⟩,
    ⟨[83069, 15], [83067], .contexts [
        ⟨18511, true, false, [], [15]⟩,
        ⟨1, false, false, [83067], []⟩,
        ⟨18512, false, false, [], []⟩
      ]⟩,
    ⟨[83071], [83069, 1], .source 74894⟩,
    ⟨[83069, 1], [83071], .contexts [
        ⟨18514, true, false, [], []⟩
      ]⟩,
    ⟨[83069], [83069], .source 74895⟩,
    ⟨[83073], [83071, 3], .source 74896⟩,
    ⟨[83071], [83071], .source 74897⟩,
    ⟨[83073, 3], [83071], .contexts [
        ⟨18517, false, false, [], [3]⟩,
        ⟨20, false, false, [83071], []⟩,
        ⟨18518, false, false, [], []⟩
      ]⟩,
    ⟨[83075], [83073, 5], .source 74898⟩,
    ⟨[83073, 5], [83075], .contexts [
        ⟨18520, true, false, [], []⟩
      ]⟩,
    ⟨[83073], [83073], .source 74899⟩,
    ⟨[83075, 5], [83073], .contexts [
        ⟨18521, true, false, [], [5]⟩,
        ⟨28, false, false, [83073], []⟩,
        ⟨18522, false, false, [], []⟩
      ]⟩,
    ⟨[83077], [83075, 1], .source 74900⟩,
    ⟨[83075, 1], [83077], .contexts [
        ⟨18524, true, false, [], []⟩
      ]⟩,
    ⟨[83075], [83075], .source 74901⟩,
    ⟨[83077, 1], [83075], .contexts [
        ⟨18525, true, false, [], [1]⟩,
        ⟨8, false, false, [83075], []⟩,
        ⟨18526, false, false, [], []⟩
      ]⟩,
    ⟨[83079], [83077, 9], .source 74902⟩,
    ⟨[83077, 9], [83079], .contexts [
        ⟨18528, true, false, [], []⟩
      ]⟩,
    ⟨[83077], [83077], .source 74903⟩,
    ⟨[83079, 9], [83077], .contexts [
        ⟨18529, true, false, [], [9]⟩,
        ⟨46, false, false, [83077], []⟩,
        ⟨18530, false, false, [], []⟩
      ]⟩,
    ⟨[83081], [83079, 11], .source 74904⟩,
    ⟨[83079, 11], [83081], .contexts [
        ⟨18532, true, false, [], []⟩
      ]⟩,
    ⟨[83079], [83079], .source 74905⟩,
    ⟨[83081, 11], [83079], .contexts [
        ⟨18533, true, false, [], [11]⟩,
        ⟨53, false, false, [83079], []⟩,
        ⟨18534, false, false, [], []⟩
      ]⟩,
    ⟨[83083], [83081, 1], .source 74906⟩,
    ⟨[83081, 1], [83083], .contexts [
        ⟨18536, true, false, [], []⟩
      ]⟩,
    ⟨[83081], [83081], .source 74907⟩,
    ⟨[83083, 1], [83081], .contexts [
        ⟨18537, true, false, [], [1]⟩,
        ⟨8, false, false, [83081], []⟩,
        ⟨18538, false, false, [], []⟩
      ]⟩,
    ⟨[83085], [83083, 13], .source 74908⟩,
    ⟨[83083, 13], [83085], .contexts [
        ⟨18540, true, false, [], []⟩
      ]⟩,
    ⟨[83083], [83083], .source 74909⟩,
    ⟨[83085, 13], [83083], .contexts [
        ⟨18541, true, false, [], [13]⟩,
        ⟨59, false, false, [83083], []⟩,
        ⟨18542, false, false, [], []⟩
      ]⟩,
    ⟨[83087], [83085, 15], .source 74910⟩,
    ⟨[83085, 15], [83087], .contexts [
        ⟨18544, true, false, [], []⟩
      ]⟩,
    ⟨[83085], [83085], .source 74911⟩,
    ⟨[83087, 15], [83085], .contexts [
        ⟨18545, true, false, [], [15]⟩,
        ⟨1, false, false, [83085], []⟩,
        ⟨18546, false, false, [], []⟩
      ]⟩,
    ⟨[83089], [83087, 1], .source 74912⟩,
    ⟨[83087, 1], [83089], .contexts [
        ⟨18548, true, false, [], []⟩
      ]⟩,
    ⟨[83087], [83087], .source 74913⟩,
    ⟨[83089, 1], [83087], .contexts [
        ⟨18549, true, false, [], [1]⟩,
        ⟨8, false, false, [83087], []⟩,
        ⟨18550, false, false, [], []⟩
      ]⟩,
    ⟨[83091], [83089, 3], .source 74914⟩,
    ⟨[83089, 3], [83091], .contexts [
        ⟨18552, true, false, [], []⟩
      ]⟩,
    ⟨[83089], [83089], .source 74915⟩,
    ⟨[83091, 3], [83089], .contexts [
        ⟨18553, true, false, [], [3]⟩,
        ⟨20, false, false, [83089], []⟩,
        ⟨18554, false, false, [], []⟩
      ]⟩,
    ⟨[83093], [83091, 5], .source 74916⟩,
    ⟨[83091, 5], [83093], .contexts [
        ⟨18556, true, false, [], []⟩
      ]⟩,
    ⟨[83091], [83091], .source 74917⟩,
    ⟨[83093, 5], [83091], .contexts [
        ⟨18557, true, false, [], [5]⟩,
        ⟨28, false, false, [83091], []⟩,
        ⟨18558, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 290. -/
def y322TCIndexRaw290 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83095], [83093, 1], .source 74918⟩,
    ⟨[83093, 1], [83095], .contexts [
        ⟨18560, true, false, [], []⟩
      ]⟩,
    ⟨[83093], [83093], .source 74919⟩,
    ⟨[83095, 1], [83093], .contexts [
        ⟨18561, true, false, [], [1]⟩,
        ⟨8, false, false, [83093], []⟩,
        ⟨18562, false, false, [], []⟩
      ]⟩,
    ⟨[83097], [83095, 9], .source 74920⟩,
    ⟨[83095, 9], [83097], .contexts [
        ⟨18564, true, false, [], []⟩
      ]⟩,
    ⟨[83095], [83095], .source 74921⟩,
    ⟨[83097, 9], [83095], .contexts [
        ⟨18565, true, false, [], [9]⟩,
        ⟨46, false, false, [83095], []⟩,
        ⟨18566, false, false, [], []⟩
      ]⟩,
    ⟨[83099], [83097, 11], .source 74922⟩,
    ⟨[83097, 11], [83099], .contexts [
        ⟨18568, true, false, [], []⟩
      ]⟩,
    ⟨[83097], [83097], .source 74923⟩,
    ⟨[83099, 11], [83097], .contexts [
        ⟨18569, true, false, [], [11]⟩,
        ⟨53, false, false, [83097], []⟩,
        ⟨18570, false, false, [], []⟩
      ]⟩,
    ⟨[83101], [83099, 1], .source 74924⟩,
    ⟨[83099, 1], [83101], .contexts [
        ⟨18572, true, false, [], []⟩
      ]⟩,
    ⟨[83099], [83099], .source 74925⟩,
    ⟨[83101, 1], [83099], .contexts [
        ⟨18573, true, false, [], [1]⟩,
        ⟨8, false, false, [83099], []⟩,
        ⟨18574, false, false, [], []⟩
      ]⟩,
    ⟨[83103], [83101, 13], .source 74926⟩,
    ⟨[83101, 13], [83103], .contexts [
        ⟨18576, true, false, [], []⟩
      ]⟩,
    ⟨[83101], [83101], .source 74927⟩,
    ⟨[83103, 13], [83101], .contexts [
        ⟨18577, true, false, [], [13]⟩,
        ⟨59, false, false, [83101], []⟩,
        ⟨18578, false, false, [], []⟩
      ]⟩,
    ⟨[83105], [83103, 15], .source 74928⟩,
    ⟨[83103, 15], [83105], .contexts [
        ⟨18580, true, false, [], []⟩
      ]⟩,
    ⟨[83103], [83103], .source 74929⟩,
    ⟨[83105, 15], [83103], .contexts [
        ⟨18581, true, false, [], [15]⟩,
        ⟨1, false, false, [83103], []⟩,
        ⟨18582, false, false, [], []⟩
      ]⟩,
    ⟨[83107], [83105, 1], .source 74930⟩,
    ⟨[83105, 1], [83107], .contexts [
        ⟨18584, true, false, [], []⟩
      ]⟩,
    ⟨[83105], [83105], .source 74931⟩,
    ⟨[83107, 1], [83105], .contexts [
        ⟨18585, true, false, [], [1]⟩,
        ⟨8, false, false, [83105], []⟩,
        ⟨18586, false, false, [], []⟩
      ]⟩,
    ⟨[83109], [83107, 3], .source 74932⟩,
    ⟨[83107, 3], [83109], .contexts [
        ⟨18588, true, false, [], []⟩
      ]⟩,
    ⟨[83107], [83107], .source 74933⟩,
    ⟨[83109, 3], [83107], .contexts [
        ⟨18589, true, false, [], [3]⟩,
        ⟨20, false, false, [83107], []⟩,
        ⟨18590, false, false, [], []⟩
      ]⟩,
    ⟨[83111], [83109, 5], .source 74934⟩,
    ⟨[83109, 5], [83111], .contexts [
        ⟨18592, true, false, [], []⟩
      ]⟩,
    ⟨[83109], [83109], .source 74935⟩,
    ⟨[83113], [83111, 1], .source 74936⟩,
    ⟨[83111], [83111], .source 74937⟩,
    ⟨[83115, 9], [83113], .source 74940⟩,
    ⟨[83117], [83115, 11], .source 74941⟩,
    ⟨[83115, 11], [83117], .contexts [
        ⟨18598, true, false, [], []⟩
      ]⟩,
    ⟨[83115], [83115], .source 74942⟩,
    ⟨[83119], [83117, 1], .source 74944⟩,
    ⟨[83117, 1], [83119], .contexts [
        ⟨18601, true, false, [], []⟩
      ]⟩,
    ⟨[83117], [83117], .source 74945⟩,
    ⟨[83119, 1], [83117], .contexts [
        ⟨18602, true, false, [], [1]⟩,
        ⟨8, false, false, [83117], []⟩,
        ⟨18603, false, false, [], []⟩
      ]⟩,
    ⟨[83121], [83119, 13], .source 74946⟩,
    ⟨[83119, 13], [83121], .contexts [
        ⟨18605, true, false, [], []⟩
      ]⟩,
    ⟨[83119], [83119], .source 74947⟩,
    ⟨[83121, 13], [83119], .source 74948⟩,
    ⟨[83121, 15], [83123], .source 74950⟩,
    ⟨[83121], [83121], .source 74951⟩,
    ⟨[83121, 15], [83123], .contexts [
        ⟨18609, false, false, [], []⟩
      ]⟩,
    ⟨[83119], [83119], .source 74953⟩,
    ⟨[83121, 13], [83119], .source 74954⟩,
    ⟨[83121, 13, 1], [83117], .source 74956⟩,
    ⟨[83115], [83115], .contexts []⟩,
    ⟨[83115, 9], [83113], .source 74957⟩,
    ⟨[83109], [83109], .contexts []⟩,
    ⟨[83107], [83107], .contexts []⟩,
    ⟨[83107, 1], [83105], .contexts [
        ⟨18587, false, false, [], []⟩
      ]⟩,
    ⟨[83105], [83105], .contexts []⟩,
    ⟨[83103], [83103], .contexts []⟩,
    ⟨[83101], [83101], .contexts []⟩,
    ⟨[83099], [83099], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 291. -/
def y322TCIndexRaw291 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83097], [83097], .contexts []⟩,
    ⟨[83095], [83095], .contexts []⟩,
    ⟨[83093], [83093], .contexts []⟩,
    ⟨[83091], [83091], .contexts []⟩,
    ⟨[83089], [83089], .contexts []⟩,
    ⟨[83087], [83087], .contexts []⟩,
    ⟨[83085], [83085], .contexts []⟩,
    ⟨[83083], [83083], .contexts []⟩,
    ⟨[83081], [83081], .contexts []⟩,
    ⟨[83079], [83079], .contexts []⟩,
    ⟨[83077], [83077], .contexts []⟩,
    ⟨[83077, 1], [83075], .contexts [
        ⟨18527, false, false, [], []⟩
      ]⟩,
    ⟨[83075], [83075], .contexts []⟩,
    ⟨[83073], [83073], .contexts []⟩,
    ⟨[83067], [83067], .contexts []⟩,
    ⟨[83065], [83065], .contexts []⟩,
    ⟨[83063], [83063], .contexts []⟩,
    ⟨[83057], [83057], .contexts []⟩,
    ⟨[83053], [83053], .contexts []⟩,
    ⟨[83051], [83051], .contexts []⟩,
    ⟨[83051, 15], [83049], .contexts [
        ⟨18479, false, false, [], []⟩
      ]⟩,
    ⟨[83047], [83047], .contexts []⟩,
    ⟨[83045], [83045], .contexts []⟩,
    ⟨[83043], [83043], .contexts []⟩,
    ⟨[83041], [83041], .contexts []⟩,
    ⟨[83039], [83039], .contexts []⟩,
    ⟨[83037], [83037], .contexts []⟩,
    ⟨[83035], [83035], .contexts []⟩,
    ⟨[83033], [83033], .contexts []⟩,
    ⟨[83031], [83031], .contexts []⟩,
    ⟨[83029], [83029], .contexts []⟩,
    ⟨[83027], [83027], .contexts []⟩,
    ⟨[83025], [83025], .contexts []⟩,
    ⟨[83023], [83023], .contexts []⟩,
    ⟨[83021], [83021], .contexts []⟩,
    ⟨[83019], [83019], .contexts []⟩,
    ⟨[83017], [83017], .contexts []⟩,
    ⟨[83015], [83015], .contexts []⟩,
    ⟨[83013], [83013], .contexts []⟩,
    ⟨[83009], [83009], .contexts []⟩,
    ⟨[83007], [83007], .contexts []⟩,
    ⟨[83005], [83005], .contexts []⟩,
    ⟨[82987, 1], [15747, 82987], .source 74974⟩,
    ⟨[15779], [15776], .source 74999⟩,
    ⟨[82749, 1], [15779, 83123], .source 75000⟩,
    ⟨[83121], [83121], .contexts []⟩,
    ⟨[83121, 1], [15781, 82749], .source 75004⟩,
    ⟨[15783], [15780], .source 75005⟩,
    ⟨[82749, 1], [15779, 83123], .contexts [
        ⟨18668, false, false, [], []⟩
      ]⟩,
    ⟨[15779, 83123], [15779, 83123], .source 75006⟩,
    ⟨[15785], [15777, 15783], .source 75007⟩,
    ⟨[83121, 1], [15781, 82749], .source 75009⟩,
    ⟨[83123], [15785, 83121], .contexts [
        ⟨18673, true, false, [15778], []⟩,
        ⟨18673, true, false, [15778], []⟩,
        ⟨18672, true, false, [15778], []⟩,
        ⟨18670, true, false, [15778, 15780], [1]⟩,
        ⟨8, false, false, [15778, 15780, 83121], []⟩,
        ⟨18671, true, false, [15778], [83121]⟩,
        ⟨18667, false, true, [], [15783, 83121]⟩,
        ⟨18674, true, false, [], [83121]⟩
      ]⟩,
    ⟨[15785, 83121], [15785, 83121], .contexts []⟩,
    ⟨[83123], [15785, 83121], .source 75013⟩,
    ⟨[15793], [15779, 15785], .source 75014⟩,
    ⟨[83121], [83121], .source 75016⟩,
    ⟨[15795, 83121, 3], [83121], .source 75017⟩,
    ⟨[83121, 3], [83121, 3], .source 75018⟩,
    ⟨[83121], [83121], .source 75019⟩,
    ⟨[15797], [15794], .source 75020⟩,
    ⟨[15794], [15794], .source 75021⟩,
    ⟨[83121, 3], [15797, 83121], .contexts [
        ⟨18682, false, false, [], []⟩,
        ⟨18681, false, false, [15794], []⟩,
        ⟨18683, false, false, [15794], []⟩,
        ⟨18685, true, false, [], [83121]⟩,
        ⟨18685, true, false, [], [83121]⟩,
        ⟨18684, true, false, [], [83121]⟩
      ]⟩,
    ⟨[15799], [15781, 439], .source 7964⟩]

/-- Exact literal claimed equations and contextual derivations, block 292. -/
def y322TCIndexRaw292 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15801], [15798], .source 7965⟩,
    ⟨[15798], [15798], .contexts []⟩,
    ⟨[77467, 7], [15801, 83121], .contexts [
        ⟨18687, false, false, [15798], [77467, 7]⟩,
        ⟨1482, true, false, [15798, 15781], [7]⟩,
        ⟨1399, true, false, [15798, 15781], [7]⟩,
        ⟨16137, true, false, [15798, 15781], [1, 7]⟩,
        ⟨18675, true, false, [15798], [7, 1, 7]⟩,
        ⟨4091, false, false, [15798, 83121], []⟩,
        ⟨18680, false, false, [15798], []⟩,
        ⟨18683, false, false, [15798], []⟩,
        ⟨18689, true, false, [], [83121]⟩,
        ⟨18689, true, false, [], [83121]⟩,
        ⟨18688, true, false, [], [83121]⟩
      ]⟩,
    ⟨[83121, 7], [15799, 77467], .contexts [
        ⟨18690, true, false, [15800], [7]⟩,
        ⟨38, false, false, [15800, 77467], []⟩,
        ⟨18688, false, true, [], [77467]⟩
      ]⟩,
    ⟨[15809, 83121, 9], [83121], .source 75026⟩,
    ⟨[83121, 9], [83121, 9], .source 75027⟩,
    ⟨[15811], [15808], .source 75028⟩,
    ⟨[15808], [15808], .source 75029⟩,
    ⟨[83121, 9], [15811, 83121], .contexts [
        ⟨18693, false, false, [], []⟩,
        ⟨18692, false, false, [15808], []⟩,
        ⟨18683, false, false, [15808], []⟩,
        ⟨18695, true, false, [], [83121]⟩,
        ⟨18695, true, false, [], [83121]⟩,
        ⟨18694, true, false, [], [83121]⟩
      ]⟩,
    ⟨[15813], [15781, 445], .source 7971⟩,
    ⟨[15815], [15813, 15793], .source 7972⟩,
    ⟨[83121, 11], [83121, 11], .contexts []⟩,
    ⟨[15817], [15814], .source 7973⟩,
    ⟨[15814], [15814], .contexts []⟩,
    ⟨[83121, 11], [15817, 83121], .contexts [
        ⟨18699, false, false, [], []⟩,
        ⟨18698, false, false, [15814], [83121, 11]⟩,
        ⟨18679, false, false, [15814, 15813], [83121, 11]⟩,
        ⟨18678, true, false, [15814, 15813, 15779], [11]⟩,
        ⟨18668, true, false, [15814, 15813], [11]⟩,
        ⟨18697, false, false, [15814], [82749, 1, 11]⟩,
        ⟨16154, true, false, [15814, 15781], [1, 11]⟩,
        ⟨18675, true, false, [15814], [11, 1, 11]⟩,
        ⟨994, false, false, [15814, 83121], []⟩,
        ⟨18680, false, false, [15814], []⟩,
        ⟨18683, false, false, [15814], []⟩,
        ⟨18701, true, false, [], [83121]⟩,
        ⟨18701, true, false, [], [83121]⟩,
        ⟨18700, true, false, [], [83121]⟩
      ]⟩,
    ⟨[15819], [15781, 655], .source 75030⟩,
    ⟨[82727, 13], [82727, 13], .source 75031⟩,
    ⟨[15821], [15818], .source 75032⟩,
    ⟨[15818], [15818], .source 75033⟩,
    ⟨[82727, 13], [15821, 83117], .contexts [
        ⟨18704, false, false, [], []⟩,
        ⟨16165, true, false, [], [13]⟩,
        ⟨18703, false, false, [15818], [82751, 1, 13]⟩,
        ⟨16190, true, false, [15818, 15781], [1, 13]⟩,
        ⟨18675, true, false, [15818], [13, 1, 13]⟩,
        ⟨919, false, false, [15818, 83121], []⟩,
        ⟨116, false, false, [15818, 83121], []⟩,
        ⟨18614, false, false, [15818], []⟩,
        ⟨18706, true, false, [], [83117]⟩,
        ⟨18706, true, false, [], [83117]⟩,
        ⟨18705, true, false, [], [83117]⟩
      ]⟩,
    ⟨[15819], [15820], .source 75034⟩,
    ⟨[15797, 83119], [15797, 83119], .source 75036⟩,
    ⟨[83119, 3], [15797, 83119], .source 75039⟩,
    ⟨[83119], [83119], .source 75040⟩,
    ⟨[15797], [15797], .source 75041⟩,
    ⟨[83119, 3], [15797, 83119], .contexts [
        ⟨18710, false, false, [], []⟩,
        ⟨18711, false, false, [15797], []⟩,
        ⟨18712, true, false, [], [83119]⟩
      ]⟩,
    ⟨[15799, 77467], [15799, 77467], .contexts []⟩,
    ⟨[15799, 77467], [15799, 77467], .contexts []⟩,
    ⟨[83121, 7], [15799, 77467], .contexts [
        ⟨18691, false, false, [], []⟩,
        ⟨18714, false, false, [], []⟩,
        ⟨18715, false, false, [], []⟩,
        ⟨18715, false, false, [], []⟩
      ]⟩,
    ⟨[15799, 77465], [15799, 77465], .contexts []⟩,
    ⟨[15799, 77465], [15799, 77465], .contexts []⟩,
    ⟨[83119, 7], [83119, 7], .contexts []⟩,
    ⟨[15799], [15799], .contexts [
        ⟨13, false, false, [], [15799]⟩
      ]⟩,
    ⟨[83119, 7], [15799, 77465], .contexts [
        ⟨18719, false, false, [], []⟩,
        ⟨18613, true, false, [], [7]⟩,
        ⟨73, false, false, [83121], []⟩,
        ⟨74, false, false, [83121], []⟩,
        ⟨18716, false, false, [], [13]⟩,
        ⟨1397, false, false, [15799], []⟩,
        ⟨18717, false, false, [], []⟩,
        ⟨18718, false, false, [], []⟩,
        ⟨1494, false, false, [15799], []⟩,
        ⟨18720, true, false, [], [77465]⟩
      ]⟩,
    ⟨[77465, 7], [15801, 83119], .contexts [
        ⟨18721, true, false, [15798], [7]⟩,
        ⟨38, false, false, [15798, 83119], []⟩,
        ⟨18688, true, false, [], [83119]⟩
      ]⟩,
    ⟨[15811, 83121], [15811, 83121], .contexts []⟩,
    ⟨[15811, 83121], [15811, 83121], .source 75042⟩,
    ⟨[15811, 83119], [15811, 83119], .source 75043⟩,
    ⟨[15811, 83119], [15811, 83119], .source 75044⟩,
    ⟨[83119, 9], [83119, 9], .source 75045⟩,
    ⟨[83119, 9], [15811, 83119], .source 75046⟩,
    ⟨[15811], [15811], .source 75047⟩,
    ⟨[83119, 9], [15811, 83119], .contexts [
        ⟨18728, false, false, [], []⟩,
        ⟨18711, false, false, [15811], []⟩,
        ⟨18729, true, false, [], [83119]⟩
      ]⟩,
    ⟨[15817, 83121], [15817, 83121], .contexts []⟩,
    ⟨[15817, 83121], [15817, 83121], .contexts []⟩,
    ⟨[83121, 11], [15817, 83121], .contexts [
        ⟨18699, false, false, [], []⟩,
        ⟨18702, false, false, [], []⟩,
        ⟨18731, false, false, [], []⟩,
        ⟨18732, false, false, [], []⟩,
        ⟨18732, false, false, [], []⟩
      ]⟩,
    ⟨[15817, 83119], [15817, 83119], .contexts []⟩,
    ⟨[15817, 83119], [15817, 83119], .contexts []⟩,
    ⟨[83119, 11], [83119, 11], .contexts []⟩,
    ⟨[15817], [15817], .contexts [
        ⟨13, false, false, [], [15817]⟩
      ]⟩,
    ⟨[83119, 11], [15817, 83119], .contexts [
        ⟨18736, false, false, [], []⟩,
        ⟨18613, true, false, [], [11]⟩,
        ⟨82, false, false, [83121], []⟩,
        ⟨83, false, false, [83121], []⟩,
        ⟨18733, false, false, [], [13]⟩,
        ⟨18608, false, false, [15817], []⟩,
        ⟨18734, false, false, [], []⟩,
        ⟨18735, false, false, [], []⟩,
        ⟨18711, false, false, [15817], []⟩,
        ⟨18737, true, false, [], [83119]⟩
      ]⟩,
    ⟨[82727, 13], [15821, 83117], .source 75048⟩,
    ⟨[82727, 13], [15821, 83117], .source 75050⟩,
    ⟨[15819], [15820], .source 75051⟩,
    ⟨[15823], [15819, 629], .source 7976⟩,
    ⟨[83117, 3], [15823, 82737], .contexts [
        ⟨18740, true, false, [15820], [3]⟩,
        ⟨63, false, false, [15820, 82727], []⟩,
        ⟨65, false, false, [15820, 82727], []⟩,
        ⟨15845, false, false, [15820], [13]⟩,
        ⟨15846, false, false, [15820], [13]⟩,
        ⟨15843, false, false, [15820], [13]⟩,
        ⟨15844, false, false, [15820], [13]⟩,
        ⟨15844, false, false, [15820], [13]⟩,
        ⟨15975, false, false, [15820, 629], []⟩,
        ⟨15981, false, false, [15820, 629], []⟩,
        ⟨18741, true, false, [], [629, 82737]⟩,
        ⟨18742, true, false, [], [82737]⟩
      ]⟩,
    ⟨[15825], [15822], .source 7977⟩,
    ⟨[82737, 3], [15825, 83117], .contexts [
        ⟨18743, true, false, [15822], [3]⟩,
        ⟨20, false, false, [15822, 83117], []⟩,
        ⟨18744, true, false, [], [83117]⟩
      ]⟩,
    ⟨[82727, 7], [77601], .contexts [
        ⟨15838, false, false, [], []⟩,
        ⟨1912, false, false, [], []⟩,
        ⟨1888, false, false, [], []⟩,
        ⟨1888, false, false, [], []⟩
      ]⟩,
    ⟨[15827], [15819, 683], .source 7978⟩,
    ⟨[83117, 7], [15827, 77461], .contexts [
        ⟨18740, true, false, [15820], [7]⟩,
        ⟨73, false, false, [15820, 82727], []⟩,
        ⟨74, false, false, [15820, 82727], []⟩,
        ⟨18746, false, false, [15820], [13]⟩,
        ⟨1969, false, false, [15820], []⟩,
        ⟨1978, false, false, [15820], []⟩,
        ⟨1979, false, false, [15820], []⟩,
        ⟨1979, false, false, [15820], []⟩,
        ⟨1625, false, false, [15820, 683], []⟩,
        ⟨18741, true, false, [], [683, 77461]⟩,
        ⟨18747, true, false, [], [77461]⟩
      ]⟩,
    ⟨[15829], [15826], .source 7979⟩,
    ⟨[77461, 7], [15829, 83117], .contexts [
        ⟨18748, true, false, [15826], [7]⟩,
        ⟨38, false, false, [15826, 83117], []⟩,
        ⟨18749, true, false, [], [83117]⟩
      ]⟩,
    ⟨[82727, 9], [677, 82847], .source 75053⟩]

/-- Exact literal claimed equations and contextual derivations, block 293. -/
def y322TCIndexRaw293 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15831], [15819, 677], .source 75054⟩,
    ⟨[83117, 9], [15831, 82855], .contexts [
        ⟨18740, true, false, [15820], [9]⟩,
        ⟨77, false, false, [15820, 82727], []⟩,
        ⟨78, false, false, [15820, 82727], []⟩,
        ⟨18751, false, false, [15820], [13]⟩,
        ⟨17530, false, false, [15820, 677], []⟩,
        ⟨17542, false, false, [15820, 677], []⟩,
        ⟨18741, true, false, [], [677, 82855]⟩,
        ⟨18752, true, false, [], [82855]⟩
      ]⟩,
    ⟨[15833], [15830], .source 7981⟩,
    ⟨[82855, 9], [15833, 83117], .contexts [
        ⟨18753, true, false, [15830], [9]⟩,
        ⟨46, false, false, [15830, 83117], []⟩,
        ⟨18754, true, false, [], [83117]⟩
      ]⟩,
    ⟨[83115, 13], [15835, 82727], .source 75057⟩,
    ⟨[15837], [15834], .source 75058⟩,
    ⟨[15839], [15819, 15837], .source 75059⟩,
    ⟨[83117], [15839, 83115], .contexts [
        ⟨18740, true, false, [15820], []⟩,
        ⟨18756, true, false, [15820, 15834], [13]⟩,
        ⟨59, false, false, [15820, 15834, 83115], []⟩,
        ⟨18757, true, false, [15820], [83115]⟩,
        ⟨18708, true, false, [], [15837, 83115]⟩,
        ⟨18758, true, false, [], [83115]⟩
      ]⟩,
    ⟨[15841], [15838], .source 75060⟩,
    ⟨[15838], [15838], .contexts []⟩,
    ⟨[83115, 1], [15841, 83119], .contexts [
        ⟨18759, true, false, [15838], [1]⟩,
        ⟨18602, false, false, [15838], []⟩,
        ⟨18612, false, false, [15838], []⟩,
        ⟨18761, true, false, [], [83119]⟩,
        ⟨18761, true, false, [], [83119]⟩,
        ⟨18760, true, false, [], [83119]⟩
      ]⟩,
    ⟨[15843], [15841, 15823], .source 7986⟩,
    ⟨[83115, 3], [15843, 82737], .contexts [
        ⟨18759, true, false, [15838], [3]⟩,
        ⟨18743, false, false, [15838], []⟩,
        ⟨18760, true, false, [], [15823, 82737]⟩,
        ⟨18763, true, false, [], [82737]⟩
      ]⟩,
    ⟨[15845], [15841, 15827], .source 7987⟩,
    ⟨[83115, 7], [15845, 77461], .contexts [
        ⟨18759, true, false, [15838], [7]⟩,
        ⟨18748, false, false, [15838], []⟩,
        ⟨18760, true, false, [], [15827, 77461]⟩,
        ⟨18765, true, false, [], [77461]⟩
      ]⟩,
    ⟨[83117], [15839, 83115], .contexts [
        ⟨18759, false, false, [], []⟩
      ]⟩,
    ⟨[15839, 83115], [15839, 83115], .source 75061⟩,
    ⟨[83117], [15839, 83115], .source 75062⟩,
    ⟨[15847], [15841, 15831], .source 75063⟩,
    ⟨[83113], [15847, 82855], .contexts [
        ⟨18597, true, false, [], []⟩,
        ⟨18769, true, false, [15838], [9]⟩,
        ⟨18753, false, false, [15838], []⟩,
        ⟨18760, true, false, [], [15831, 82855]⟩,
        ⟨18770, true, false, [], [82855]⟩
      ]⟩,
    ⟨[15847, 82855], [15847, 82855], .source 75064⟩,
    ⟨[83113], [15847, 82855], .contexts [
        ⟨18771, false, false, [], []⟩,
        ⟨18772, false, false, [], []⟩
      ]⟩,
    ⟨[15849], [15847, 15653], .source 7989⟩,
    ⟨[15851], [15848], .source 7990⟩,
    ⟨[15851], [15848], .contexts [
        ⟨18775, false, false, [], []⟩
      ]⟩,
    ⟨[15849], [15850], .contexts [
        ⟨18775, true, true, [], []⟩
      ]⟩,
    ⟨[83111], [15849, 82855], .contexts [
        ⟨18776, false, false, [15850], [83111]⟩,
        ⟨13, false, false, [15850, 15848], [83111]⟩,
        ⟨18596, true, false, [15850, 15848], []⟩,
        ⟨8, true, false, [15850, 15848, 83111], []⟩,
        ⟨18595, true, false, [15850, 15848], [1]⟩,
        ⟨18773, false, false, [15850, 15848], [1]⟩,
        ⟨17544, false, false, [15850, 15848, 15847], []⟩,
        ⟨18774, true, false, [15850, 15848], [82855]⟩,
        ⟨18777, true, false, [], [82855]⟩
      ]⟩,
    ⟨[15848], [15848], .contexts []⟩,
    ⟨[82855, 5], [15851, 83109], .contexts [
        ⟨18778, true, false, [15848], [5]⟩,
        ⟨18593, true, false, [15848], [5]⟩,
        ⟨28, false, false, [15848, 83109], []⟩,
        ⟨18594, false, false, [15848], []⟩,
        ⟨18617, false, false, [15848], []⟩,
        ⟨18779, true, false, [], [83109]⟩,
        ⟨18779, true, false, [], [83109]⟩,
        ⟨18776, true, false, [], [83109]⟩
      ]⟩,
    ⟨[15851, 83109], [15851, 83109], .contexts []⟩,
    ⟨[15851, 83109], [15851, 83109], .contexts []⟩,
    ⟨[82855, 5], [15851, 83109], .contexts [
        ⟨18780, false, false, [], []⟩,
        ⟨18781, false, false, [], []⟩,
        ⟨18782, false, false, [], []⟩,
        ⟨18782, false, false, [], []⟩
      ]⟩,
    ⟨[82855, 4], [82855, 5], .contexts [
        ⟨29, false, false, [82855], []⟩
      ]⟩,
    ⟨[82853, 13], [82853, 13], .contexts []⟩,
    ⟨[83109], [83109], .contexts []⟩,
    ⟨[82853, 13], [15851, 83109], .contexts [
        ⟨18785, false, false, [], []⟩,
        ⟨17525, true, false, [], [13]⟩,
        ⟨17525, true, false, [], [13]⟩,
        ⟨17524, true, false, [], [13]⟩,
        ⟨17523, true, false, [], [13]⟩,
        ⟨17412, true, false, [], [5, 13]⟩,
        ⟨17412, true, false, [], [5, 13]⟩,
        ⟨17411, true, false, [], [5, 13]⟩,
        ⟨17531, true, false, [], [5, 13]⟩,
        ⟨1136, false, false, [82855], []⟩,
        ⟨18784, false, false, [], []⟩,
        ⟨18783, false, false, [], []⟩,
        ⟨18786, false, false, [15851], []⟩,
        ⟨13, true, false, [], [15851, 83109]⟩
      ]⟩,
    ⟨[15853], [15653, 15851], .source 7991⟩,
    ⟨[83109, 1], [83109, 1], .contexts []⟩,
    ⟨[15855], [15852], .source 7992⟩,
    ⟨[15857], [15855, 15851], .source 7993⟩,
    ⟨[83109, 1], [15857, 83109], .contexts [
        ⟨18789, false, false, [], []⟩,
        ⟨18788, false, false, [15852], [83109, 1]⟩,
        ⟨18780, true, false, [15852, 15653], [1]⟩,
        ⟨17540, true, false, [15852], [5, 1]⟩,
        ⟨17540, true, false, [15852], [5, 1]⟩,
        ⟨17539, true, false, [15852], [5, 1]⟩,
        ⟨17544, true, false, [15852], [5, 1]⟩,
        ⟨17541, true, false, [15852], [5, 1]⟩,
        ⟨14585, false, false, [15852, 82855], []⟩,
        ⟨18784, false, false, [15852], []⟩,
        ⟨18783, false, false, [15852], []⟩,
        ⟨18786, false, false, [15852, 15851], []⟩,
        ⟨18790, true, false, [], [15851, 83109]⟩,
        ⟨18791, true, false, [], [83109]⟩
      ]⟩,
    ⟨[15859], [709, 471], .source 7994⟩,
    ⟨[15861], [15859, 711], .source 7995⟩,
    ⟨[15863], [15861, 15851], .source 7996⟩,
    ⟨[7, 5, 7, 5, 7], [4], .contexts [
        ⟨1042, false, false, [], [4]⟩
      ]⟩,
    ⟨[15863, 83109, 7], [15851, 83109], .contexts [
        ⟨18795, false, false, [], [83109, 7]⟩,
        ⟨18780, true, false, [15861], [7]⟩,
        ⟨18794, false, false, [], [82855, 5, 7]⟩,
        ⟨17553, true, false, [15859], [5, 7]⟩,
        ⟨18793, false, false, [], [77455, 7, 5, 7]⟩,
        ⟨1520, true, false, [709], [7, 5, 7]⟩,
        ⟨1624, true, false, [709], [7, 5, 7]⟩,
        ⟨1391, true, false, [709], [7, 5, 7]⟩,
        ⟨1997, true, false, [], [5, 7, 5, 7]⟩,
        ⟨1997, true, false, [], [5, 7, 5, 7]⟩,
        ⟨1996, true, false, [], [5, 7, 5, 7]⟩,
        ⟨17552, true, false, [], [5, 7, 5, 7]⟩,
        ⟨17551, true, false, [], [5, 7, 5, 7]⟩,
        ⟨18796, false, false, [82855], []⟩,
        ⟨18784, false, false, [], []⟩,
        ⟨18783, false, false, [], []⟩
      ]⟩,
    ⟨[83109, 7], [83109, 7], .contexts []⟩,
    ⟨[15865], [15862], .source 7997⟩,
    ⟨[15867], [15865, 15851], .source 7998⟩,
    ⟨[83109, 7], [15867, 83109], .contexts [
        ⟨18798, false, false, [], []⟩,
        ⟨18797, false, false, [15862], []⟩,
        ⟨18786, false, false, [15862, 15851], []⟩,
        ⟨18799, true, false, [], [15851, 83109]⟩,
        ⟨18800, true, false, [], [83109]⟩
      ]⟩,
    ⟨[15737, 82981], [15737, 82981], .contexts []⟩,
    ⟨[15737, 82981], [15737, 82981], .contexts []⟩,
    ⟨[15869], [15849, 15737], .source 7999⟩,
    ⟨[83107, 13], [15869, 82981], .contexts [
        ⟨18591, true, false, [], [13]⟩,
        ⟨18782, true, false, [15850], [3, 13]⟩,
        ⟨18782, true, false, [15850], [3, 13]⟩,
        ⟨18781, true, false, [15850], [3, 13]⟩,
        ⟨18787, true, false, [15850], [3, 13]⟩,
        ⟨18785, true, false, [15850], [3, 13]⟩,
        ⟨1132, false, false, [15850, 82853], []⟩,
        ⟨21, false, false, [15850, 82853], []⟩,
        ⟨18132, false, false, [15850], []⟩,
        ⟨18802, false, false, [15850], []⟩,
        ⟨18803, false, false, [15850], []⟩,
        ⟨18803, false, false, [15850], []⟩,
        ⟨18138, false, false, [15850, 15737], []⟩,
        ⟨18777, true, false, [], [15737, 82981]⟩,
        ⟨18804, true, false, [], [82981]⟩
      ]⟩,
    ⟨[15871], [15868], .source 8000⟩,
    ⟨[82981, 13], [15871, 83107], .contexts [
        ⟨18805, true, false, [15868], [13]⟩,
        ⟨59, false, false, [15868, 83107], []⟩,
        ⟨18806, true, false, [], [83107]⟩
      ]⟩,
    ⟨[15857, 83109], [15857, 83109], .contexts []⟩,
    ⟨[15857, 83109], [15857, 83109], .contexts []⟩,
    ⟨[83109, 3], [83107], .contexts [
        ⟨18591, false, false, [], []⟩,
        ⟨18618, false, false, [], []⟩,
        ⟨18590, false, false, [], []⟩,
        ⟨18590, false, false, [], []⟩
      ]⟩,
    ⟨[83105, 3], [83105, 3], .contexts []⟩,
    ⟨[83105], [83105], .contexts []⟩,
    ⟨[15873], [15856], .source 8001⟩,
    ⟨[15856], [15856], .contexts []⟩,
    ⟨[15873], [15856], .contexts [
        ⟨18813, false, false, [], []⟩,
        ⟨18814, false, false, [], []⟩,
        ⟨18814, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 294. -/
def y322TCIndexRaw294 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83105, 3], [15873, 83105], .contexts [
        ⟨18811, false, false, [], []⟩,
        ⟨18587, true, false, [], [3]⟩,
        ⟨18591, true, false, [], [1, 3]⟩,
        ⟨18809, true, false, [15856], [3, 1, 3]⟩,
        ⟨18809, true, false, [15856], [3, 1, 3]⟩,
        ⟨18808, true, false, [15856], [3, 1, 3]⟩,
        ⟨18792, true, false, [15856], [3, 1, 3]⟩,
        ⟨18789, true, false, [15856], [3, 1, 3]⟩,
        ⟨484, false, false, [15856, 83109], []⟩,
        ⟨485, false, false, [15856, 83109], []⟩,
        ⟨18810, false, false, [15856], [1]⟩,
        ⟨18619, false, false, [15856], []⟩,
        ⟨18620, false, false, [15856], []⟩,
        ⟨18586, false, false, [15856], []⟩,
        ⟨18586, false, false, [15856], []⟩,
        ⟨18812, false, false, [15856], []⟩,
        ⟨18815, true, false, [], [83105]⟩
      ]⟩,
    ⟨[15867, 83109], [15867, 83109], .contexts []⟩,
    ⟨[15867, 83109], [15867, 83109], .contexts []⟩,
    ⟨[83107, 7], [83107, 7], .contexts []⟩,
    ⟨[83107], [83107], .contexts []⟩,
    ⟨[15875], [15866], .source 8002⟩,
    ⟨[15866], [15866], .contexts []⟩,
    ⟨[15875], [15866], .contexts [
        ⟨18821, false, false, [], []⟩,
        ⟨18822, false, false, [], []⟩,
        ⟨18822, false, false, [], []⟩
      ]⟩,
    ⟨[83107, 7], [15875, 83107], .contexts [
        ⟨18819, false, false, [], []⟩,
        ⟨18591, true, false, [], [7]⟩,
        ⟨18818, true, false, [15866], [3, 7]⟩,
        ⟨18818, true, false, [15866], [3, 7]⟩,
        ⟨18817, true, false, [15866], [3, 7]⟩,
        ⟨18801, true, false, [15866], [3, 7]⟩,
        ⟨18798, true, false, [15866], [3, 7]⟩,
        ⟨14911, false, false, [15866, 83109], []⟩,
        ⟨21, false, false, [15866, 83109], []⟩,
        ⟨18810, false, false, [15866], []⟩,
        ⟨18820, false, false, [15866], []⟩,
        ⟨18823, true, false, [], [83107]⟩
      ]⟩,
    ⟨[15873, 83105], [15873, 83105], .contexts []⟩,
    ⟨[15873, 83105], [15873, 83105], .contexts []⟩,
    ⟨[83105, 3], [15873, 83105], .contexts [
        ⟨18811, false, false, [], []⟩,
        ⟨18816, false, false, [], []⟩,
        ⟨18825, false, false, [], []⟩,
        ⟨18826, false, false, [], []⟩,
        ⟨18826, false, false, [], []⟩
      ]⟩,
    ⟨[83105, 15], [83103], .contexts [
        ⟨18583, false, false, [], []⟩,
        ⟨18621, false, false, [], []⟩,
        ⟨18582, false, false, [], []⟩,
        ⟨18582, false, false, [], []⟩
      ]⟩,
    ⟨[83105, 14], [83105, 15], .contexts [
        ⟨10, false, false, [83105], []⟩
      ]⟩,
    ⟨[83103, 3], [83103, 3], .contexts []⟩,
    ⟨[83103], [83103], .contexts []⟩,
    ⟨[15872], [15872], .contexts []⟩,
    ⟨[83103, 3], [15857, 83103], .contexts [
        ⟨18830, false, false, [], []⟩,
        ⟨18583, true, false, [], [3]⟩,
        ⟨18827, true, false, [15872], [15, 3]⟩,
        ⟨499, false, false, [15872, 83105], []⟩,
        ⟨18829, false, false, [15872], []⟩,
        ⟨18828, false, false, [15872], []⟩,
        ⟨18831, false, false, [15872], []⟩,
        ⟨18832, true, false, [], [83103]⟩,
        ⟨18832, true, false, [], [83103]⟩,
        ⟨18813, false, true, [], [83103]⟩
      ]⟩,
    ⟨[15875, 83107], [15875, 83107], .contexts []⟩,
    ⟨[15875, 83107], [15875, 83107], .contexts []⟩,
    ⟨[83107, 1], [83105], .contexts [
        ⟨18619, false, false, [], []⟩,
        ⟨18620, false, false, [], []⟩,
        ⟨18586, false, false, [], []⟩,
        ⟨18586, false, false, [], []⟩
      ]⟩,
    ⟨[83107, 0], [83107, 1], .contexts [
        ⟨9, false, false, [83107], []⟩
      ]⟩,
    ⟨[83105, 7], [83105, 7], .contexts []⟩,
    ⟨[15874], [15874], .contexts []⟩,
    ⟨[15867], [15874], .contexts [
        ⟨18821, true, true, [], []⟩,
        ⟨18839, false, false, [], []⟩,
        ⟨18839, false, false, [], []⟩
      ]⟩,
    ⟨[83105, 7], [15867, 83105], .contexts [
        ⟨18838, false, false, [], []⟩,
        ⟨18587, true, false, [], [7]⟩,
        ⟨18835, true, false, [15874], [1, 7]⟩,
        ⟨18835, true, false, [15874], [1, 7]⟩,
        ⟨18834, true, false, [15874], [1, 7]⟩,
        ⟨18824, true, false, [15874], [1, 7]⟩,
        ⟨18819, true, false, [15874], [1, 7]⟩,
        ⟨502, false, false, [15874, 83107], []⟩,
        ⟨18837, false, false, [15874], []⟩,
        ⟨18836, false, false, [15874], []⟩,
        ⟨18812, false, false, [15874], []⟩,
        ⟨18840, true, false, [], [83105]⟩
      ]⟩,
    ⟨[15857, 83103], [15857, 83103], .contexts []⟩,
    ⟨[15857, 83103], [15857, 83103], .contexts []⟩,
    ⟨[83103, 13], [83101], .contexts [
        ⟨18579, false, false, [], []⟩,
        ⟨18622, false, false, [], []⟩,
        ⟨18578, false, false, [], []⟩,
        ⟨18578, false, false, [], []⟩
      ]⟩,
    ⟨[83103, 12], [83103, 13], .contexts [
        ⟨64, false, false, [83103], []⟩
      ]⟩,
    ⟨[83101, 3], [83101, 3], .contexts []⟩,
    ⟨[83101], [83101], .contexts []⟩,
    ⟨[83101, 3], [15873, 83101], .contexts [
        ⟨18846, false, false, [], []⟩,
        ⟨18579, true, false, [], [3]⟩,
        ⟨18843, true, false, [15856], [13, 3]⟩,
        ⟨18843, true, false, [15856], [13, 3]⟩,
        ⟨18842, true, false, [15856], [13, 3]⟩,
        ⟨18833, true, false, [15856], [13, 3]⟩,
        ⟨18830, true, false, [15856], [13, 3]⟩,
        ⟨514, false, false, [15856, 83103], []⟩,
        ⟨18845, false, false, [15856], []⟩,
        ⟨18844, false, false, [15856], []⟩,
        ⟨18847, false, false, [15856], []⟩,
        ⟨18815, true, false, [], [83101]⟩
      ]⟩,
    ⟨[15867, 83105], [15867, 83105], .contexts []⟩,
    ⟨[15867, 83105], [15867, 83105], .contexts []⟩,
    ⟨[83105, 7], [15867, 83105], .contexts [
        ⟨18838, false, false, [], []⟩,
        ⟨18841, false, false, [], []⟩,
        ⟨18849, false, false, [], []⟩,
        ⟨18850, false, false, [], []⟩,
        ⟨18850, false, false, [], []⟩
      ]⟩,
    ⟨[83103, 7], [83103, 7], .contexts []⟩,
    ⟨[83103, 7], [15875, 83103], .contexts [
        ⟨18852, false, false, [], []⟩,
        ⟨18583, true, false, [], [7]⟩,
        ⟨18851, true, false, [15866], [15, 7]⟩,
        ⟨18155, false, false, [15866, 83105], []⟩,
        ⟨18829, false, false, [15866], []⟩,
        ⟨18828, false, false, [15866], []⟩,
        ⟨18831, false, false, [15866], []⟩,
        ⟨18823, true, false, [], [83103]⟩
      ]⟩,
    ⟨[15875, 83103], [15875, 83103], .contexts []⟩,
    ⟨[15875, 83103], [15875, 83103], .contexts []⟩,
    ⟨[83101, 7], [83101, 7], .contexts []⟩,
    ⟨[83101, 7], [15867, 83101], .contexts [
        ⟨18856, false, false, [], []⟩,
        ⟨18579, true, false, [], [7]⟩,
        ⟨18855, true, false, [15874], [13, 7]⟩,
        ⟨18855, true, false, [15874], [13, 7]⟩,
        ⟨18854, true, false, [15874], [13, 7]⟩,
        ⟨18853, true, false, [15874], [13, 7]⟩,
        ⟨18852, true, false, [15874], [13, 7]⟩,
        ⟨518, false, false, [15874, 83103], []⟩,
        ⟨18845, false, false, [15874], []⟩,
        ⟨18844, false, false, [15874], []⟩,
        ⟨18847, false, false, [15874], []⟩,
        ⟨18840, true, false, [], [83101]⟩
      ]⟩,
    ⟨[15867, 83101], [15867, 83101], .contexts []⟩,
    ⟨[15867, 83101], [15867, 83101], .contexts []⟩,
    ⟨[83101, 7], [15867, 83101], .contexts [
        ⟨18856, false, false, [], []⟩,
        ⟨18857, false, false, [], []⟩,
        ⟨18858, false, false, [], []⟩,
        ⟨18859, false, false, [], []⟩,
        ⟨18859, false, false, [], []⟩
      ]⟩,
    ⟨[83101, 1], [83099], .contexts [
        ⟨18575, false, false, [], []⟩,
        ⟨18623, false, false, [], []⟩,
        ⟨18574, false, false, [], []⟩,
        ⟨18574, false, false, [], []⟩
      ]⟩,
    ⟨[83101, 0], [83101, 1], .contexts [
        ⟨9, false, false, [83101], []⟩
      ]⟩,
    ⟨[83099, 7], [83099, 7], .contexts []⟩,
    ⟨[83099], [83099], .contexts []⟩,
    ⟨[83099, 7], [15875, 83099], .contexts [
        ⟨18863, false, false, [], []⟩,
        ⟨18575, true, false, [], [7]⟩,
        ⟨18860, true, false, [15866], [1, 7]⟩,
        ⟨502, false, false, [15866, 83101], []⟩,
        ⟨18862, false, false, [15866], []⟩,
        ⟨18861, false, false, [15866], []⟩,
        ⟨18864, false, false, [15866], []⟩,
        ⟨18823, true, false, [], [83099]⟩
      ]⟩,
    ⟨[15875, 83099], [15875, 83099], .contexts []⟩,
    ⟨[15875, 83099], [15875, 83099], .contexts []⟩,
    ⟨[83099, 7], [15875, 83099], .contexts [
        ⟨18863, false, false, [], []⟩,
        ⟨18865, false, false, [], []⟩,
        ⟨18866, false, false, [], []⟩,
        ⟨18867, false, false, [], []⟩,
        ⟨18867, false, false, [], []⟩
      ]⟩,
    ⟨[83099, 11], [83097], .contexts [
        ⟨18571, false, false, [], []⟩,
        ⟨18624, false, false, [], []⟩,
        ⟨18570, false, false, [], []⟩,
        ⟨18570, false, false, [], []⟩
      ]⟩,
    ⟨[83099, 10], [83099, 11], .contexts [
        ⟨54, false, false, [83099], []⟩
      ]⟩,
    ⟨[83097, 7], [83097, 7], .contexts []⟩,
    ⟨[83097], [83097], .contexts []⟩,
    ⟨[83097, 7], [15867, 83097], .contexts [
        ⟨18871, false, false, [], []⟩,
        ⟨18571, true, false, [], [7]⟩,
        ⟨18868, true, false, [15874], [11, 7]⟩,
        ⟨555, false, false, [15874, 83099], []⟩,
        ⟨18870, false, false, [15874], []⟩,
        ⟨18869, false, false, [15874], []⟩,
        ⟨18872, false, false, [15874], []⟩,
        ⟨18840, true, false, [], [83097]⟩
      ]⟩,
    ⟨[15867, 83097], [15867, 83097], .contexts []⟩,
    ⟨[15867, 83097], [15867, 83097], .contexts []⟩,
    ⟨[83097, 9], [83095], .contexts [
        ⟨18567, false, false, [], []⟩,
        ⟨18625, false, false, [], []⟩,
        ⟨18566, false, false, [], []⟩,
        ⟨18566, false, false, [], []⟩
      ]⟩,
    ⟨[83097, 8], [83097, 9], .contexts [
        ⟨47, false, false, [83097], []⟩
      ]⟩,
    ⟨[83095, 7], [83095, 7], .contexts []⟩,
    ⟨[83095], [83095], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 295. -/
def y322TCIndexRaw295 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83095, 7], [15875, 83095], .contexts [
        ⟨18878, false, false, [], []⟩,
        ⟨18567, true, false, [], [7]⟩,
        ⟨18875, true, false, [15866], [9, 7]⟩,
        ⟨18875, true, false, [15866], [9, 7]⟩,
        ⟨18874, true, false, [15866], [9, 7]⟩,
        ⟨18873, true, false, [15866], [9, 7]⟩,
        ⟨18871, true, false, [15866], [9, 7]⟩,
        ⟨579, false, false, [15866, 83097], []⟩,
        ⟨18877, false, false, [15866], []⟩,
        ⟨18876, false, false, [15866], []⟩,
        ⟨18879, false, false, [15866], []⟩,
        ⟨18823, true, false, [], [83095]⟩
      ]⟩,
    ⟨[15875, 83095], [15875, 83095], .contexts []⟩,
    ⟨[15875, 83095], [15875, 83095], .contexts []⟩,
    ⟨[83095, 1], [83093], .contexts [
        ⟨18563, false, false, [], []⟩,
        ⟨18626, false, false, [], []⟩,
        ⟨18562, false, false, [], []⟩,
        ⟨18562, false, false, [], []⟩
      ]⟩,
    ⟨[83093, 7], [83093, 7], .contexts []⟩,
    ⟨[83093], [83093], .contexts []⟩,
    ⟨[83093, 7], [15867, 83093], .contexts [
        ⟨18884, false, false, [], []⟩,
        ⟨18563, true, false, [], [7]⟩,
        ⟨18882, true, false, [15874], [1, 7]⟩,
        ⟨18882, true, false, [15874], [1, 7]⟩,
        ⟨18881, true, false, [15874], [1, 7]⟩,
        ⟨18880, true, false, [15874], [1, 7]⟩,
        ⟨18878, true, false, [15874], [1, 7]⟩,
        ⟨502, false, false, [15874, 83095], []⟩,
        ⟨9, false, false, [15874, 83095], []⟩,
        ⟨18883, false, false, [15874], []⟩,
        ⟨18885, false, false, [15874], []⟩,
        ⟨18840, true, false, [], [83093]⟩
      ]⟩,
    ⟨[83125], [82765, 5], .source 75065⟩,
    ⟨[82765, 5], [83125], .contexts [
        ⟨18887, true, false, [], []⟩
      ]⟩,
    ⟨[83125], [83125], .contexts []⟩,
    ⟨[83125], [83125], .contexts []⟩,
    ⟨[82765, 5], [83125], .contexts [
        ⟨18888, false, false, [], []⟩,
        ⟨18889, false, false, [], []⟩,
        ⟨18890, false, false, [], []⟩,
        ⟨18890, false, false, [], []⟩
      ]⟩,
    ⟨[277, 83125], [277, 83125], .contexts []⟩,
    ⟨[277, 83125], [277, 83125], .contexts []⟩,
    ⟨[83125, 9], [83125, 9], .contexts []⟩,
    ⟨[83125], [83125], .contexts []⟩,
    ⟨[83125, 9], [277, 83125], .contexts [
        ⟨18894, false, false, [], []⟩,
        ⟨18891, true, false, [], [9]⟩,
        ⟨1265, false, false, [82765], []⟩,
        ⟨1266, false, false, [82765], []⟩,
        ⟨16361, false, false, [], [5]⟩,
        ⟨16363, false, false, [], [5]⟩,
        ⟨16359, false, false, [], [5]⟩,
        ⟨16360, false, false, [], [5]⟩,
        ⟨16360, false, false, [], [5]⟩,
        ⟨18888, false, false, [277], []⟩,
        ⟨18892, false, false, [], []⟩,
        ⟨18893, false, false, [], []⟩,
        ⟨18895, false, false, [277], []⟩,
        ⟨1228, true, false, [], [83125]⟩
      ]⟩,
    ⟨[245, 83125], [245, 83125], .contexts []⟩,
    ⟨[245, 83125], [245, 83125], .contexts []⟩,
    ⟨[83125, 11], [83125, 11], .contexts []⟩,
    ⟨[83125, 11], [245, 83125], .contexts [
        ⟨18899, false, false, [], []⟩,
        ⟨18891, true, false, [], [11]⟩,
        ⟨174, false, false, [82765], []⟩,
        ⟨175, false, false, [82765], []⟩,
        ⟨16366, false, false, [], [5]⟩,
        ⟨16367, false, false, [], [5]⟩,
        ⟨16364, false, false, [], [5]⟩,
        ⟨16365, false, false, [], [5]⟩,
        ⟨16365, false, false, [], [5]⟩,
        ⟨18888, false, false, [245], []⟩,
        ⟨18897, false, false, [], []⟩,
        ⟨18898, false, false, [], []⟩,
        ⟨18895, false, false, [245], []⟩,
        ⟨923, true, false, [], [83125]⟩
      ]⟩,
    ⟨[83125, 13], [83125, 13], .contexts []⟩,
    ⟨[83125, 13], [82757], .contexts [
        ⟨18901, false, false, [], []⟩,
        ⟨18891, true, false, [], [13]⟩,
        ⟨179, false, false, [82765], []⟩,
        ⟨180, false, false, [82765], []⟩,
        ⟨16353, false, false, [], [5]⟩,
        ⟨16211, false, false, [], [5]⟩,
        ⟨16212, false, false, [], [5]⟩,
        ⟨16212, false, false, [], [5]⟩,
        ⟨16235, false, false, [], []⟩,
        ⟨16236, false, false, [], []⟩,
        ⟨16237, false, false, [], []⟩,
        ⟨16237, false, false, [], []⟩,
        ⟨16248, false, false, [], []⟩,
        ⟨672, true, false, [], [82757]⟩
      ]⟩,
    ⟨[82757, 13], [83125], .contexts [
        ⟨18902, true, false, [], [13]⟩,
        ⟨59, false, false, [83125], []⟩,
        ⟨18890, false, false, [], []⟩
      ]⟩,
    ⟨[15411, 83125], [15411, 83125], .contexts []⟩,
    ⟨[15411, 83125], [15411, 83125], .contexts []⟩,
    ⟨[83125, 15], [83125, 15], .contexts []⟩,
    ⟨[83125, 15], [15411, 83125], .contexts [
        ⟨18906, false, false, [], []⟩,
        ⟨18891, true, false, [], [15]⟩,
        ⟨184, false, false, [82765], []⟩,
        ⟨185, false, false, [82765], []⟩,
        ⟨16372, false, false, [], [5]⟩,
        ⟨16374, false, false, [], [5]⟩,
        ⟨16370, false, false, [], [5]⟩,
        ⟨16371, false, false, [], [5]⟩,
        ⟨16371, false, false, [], [5]⟩,
        ⟨18888, false, false, [15411], []⟩,
        ⟨18904, false, false, [], []⟩,
        ⟨18905, false, false, [], []⟩,
        ⟨18895, false, false, [15411], []⟩,
        ⟨16373, true, false, [], [83125]⟩
      ]⟩,
    ⟨[83125, 13], [82757], .contexts [
        ⟨18901, false, false, [], []⟩,
        ⟨18902, false, false, [], []⟩,
        ⟨16236, false, false, [], []⟩,
        ⟨16237, false, false, [], []⟩,
        ⟨16237, false, false, [], []⟩
      ]⟩,
    ⟨[83125, 3], [83125, 3], .contexts []⟩,
    ⟨[15398], [15398], .contexts []⟩,
    ⟨[83125, 3], [15397, 83125], .contexts [
        ⟨18909, false, false, [], []⟩,
        ⟨18903, true, false, [], [3]⟩,
        ⟨16278, true, false, [15398], [13, 3]⟩,
        ⟨16278, true, false, [15398], [13, 3]⟩,
        ⟨16277, true, false, [15398], [13, 3]⟩,
        ⟨16276, true, false, [15398], [13, 3]⟩,
        ⟨18908, true, false, [15398], [3, 13, 3]⟩,
        ⟨4550, false, false, [15398, 83125], []⟩,
        ⟨18895, false, false, [15398], []⟩,
        ⟨18910, true, false, [], [83125]⟩,
        ⟨18910, true, false, [], [83125]⟩,
        ⟨16265, false, true, [], [83125]⟩
      ]⟩,
    ⟨[83127], [83125, 7], .source 75066⟩,
    ⟨[83125, 7], [83127], .contexts [
        ⟨18912, true, false, [], []⟩
      ]⟩,
    ⟨[83127, 7], [83125], .contexts [
        ⟨18913, true, false, [], [7]⟩,
        ⟨38, false, false, [83125], []⟩,
        ⟨18890, false, false, [], []⟩
      ]⟩,
    ⟨[83127], [83127], .contexts []⟩,
    ⟨[83127], [83127], .source 75067⟩,
    ⟨[83125, 7], [83127], .contexts [
        ⟨18913, false, false, [], []⟩,
        ⟨18915, false, false, [], []⟩,
        ⟨18916, false, false, [], []⟩,
        ⟨18916, false, false, [], []⟩
      ]⟩,
    ⟨[15397, 83125], [15397, 83125], .contexts []⟩,
    ⟨[15397, 83125], [15397, 83125], .contexts []⟩,
    ⟨[15397, 83127], [15397, 83127], .contexts []⟩,
    ⟨[83127], [83127], .contexts []⟩,
    ⟨[83127, 3], [15397, 83127], .contexts [
        ⟨18917, true, false, [], [3]⟩,
        ⟨1034, false, false, [83125], []⟩,
        ⟨1035, false, false, [83125], []⟩,
        ⟨18909, false, false, [], [7]⟩,
        ⟨18911, false, false, [], [7]⟩,
        ⟨18918, false, false, [], [7]⟩,
        ⟨18919, false, false, [], [7]⟩,
        ⟨18919, false, false, [], [7]⟩,
        ⟨18913, false, false, [15397], []⟩,
        ⟨18920, false, false, [], []⟩,
        ⟨18921, false, false, [15397], []⟩,
        ⟨13, true, false, [], [15397, 83127]⟩
      ]⟩,
    ⟨[83127, 5], [82761], .source 75069⟩,
    ⟨[82761, 5], [83127], .contexts [
        ⟨18923, true, false, [], [5]⟩,
        ⟨28, false, false, [83127], []⟩,
        ⟨18916, false, false, [], []⟩
      ]⟩,
    ⟨[277, 83127], [277, 83127], .contexts []⟩,
    ⟨[245, 83127], [245, 83127], .contexts []⟩,
    ⟨[83127, 13], [82759], .contexts [
        ⟨18917, true, false, [], [13]⟩,
        ⟨1056, false, false, [83125], []⟩,
        ⟨1057, false, false, [83125], []⟩,
        ⟨18908, false, false, [], [7]⟩,
        ⟨16269, false, false, [], []⟩,
        ⟨16270, false, false, [], []⟩,
        ⟨16271, false, false, [], []⟩,
        ⟨16271, false, false, [], []⟩,
        ⟨16280, false, false, [], []⟩,
        ⟨672, true, false, [], [82759]⟩
      ]⟩,
    ⟨[15411, 83127], [15411, 83127], .contexts []⟩,
    ⟨[83127, 15], [15411, 83127], .contexts [
        ⟨18917, true, false, [], [15]⟩,
        ⟨1063, false, false, [83125], []⟩,
        ⟨1064, false, false, [83125], []⟩,
        ⟨18906, false, false, [], [7]⟩,
        ⟨18907, false, false, [], [7]⟩,
        ⟨18904, false, false, [], [7]⟩,
        ⟨18905, false, false, [], [7]⟩,
        ⟨18905, false, false, [], [7]⟩,
        ⟨18913, false, false, [15411], []⟩,
        ⟨18928, false, false, [], []⟩,
        ⟨18921, false, false, [15411], []⟩,
        ⟨16373, true, false, [], [83127]⟩
      ]⟩,
    ⟨[83129], [77371, 7], .source 41629⟩,
    ⟨[77371, 7], [83129], .contexts [
        ⟨18930, true, false, [], []⟩
      ]⟩,
    ⟨[83129], [83129], .contexts []⟩,
    ⟨[83129], [83129], .contexts []⟩,
    ⟨[77371, 7], [83129], .contexts [
        ⟨18931, false, false, [], []⟩,
        ⟨18932, false, false, [], []⟩,
        ⟨18933, false, false, [], []⟩,
        ⟨18933, false, false, [], []⟩
      ]⟩,
    ⟨[83129, 1], [82765], .contexts [
        ⟨18934, true, false, [], [1]⟩,
        ⟨1027, false, false, [77371], []⟩,
        ⟨1028, false, false, [77371], []⟩,
        ⟨1297, false, false, [], [7]⟩,
        ⟨16358, false, false, [], []⟩,
        ⟨16354, false, false, [], []⟩,
        ⟨16355, false, false, [], []⟩,
        ⟨16355, false, false, [], []⟩,
        ⟨16362, false, false, [], []⟩,
        ⟨672, true, false, [], [82765]⟩
      ]⟩,
    ⟨[82765, 1], [83129], .contexts [
        ⟨18935, true, false, [], [1]⟩,
        ⟨8, false, false, [83129], []⟩,
        ⟨18933, false, false, [], []⟩
      ]⟩,
    ⟨[15515, 82807], [15515, 82807], .contexts []⟩,
    ⟨[15515, 82807], [15515, 82807], .contexts []⟩,
    ⟨[83129, 9], [15515, 82807], .contexts [
        ⟨18934, true, false, [], [9]⟩,
        ⟨1534, false, false, [77371], []⟩,
        ⟨1535, false, false, [77371], []⟩,
        ⟨1296, false, false, [], [7]⟩,
        ⟨16869, false, false, [], []⟩,
        ⟨18937, false, false, [], []⟩,
        ⟨18938, false, false, [], []⟩,
        ⟨18938, false, false, [], []⟩,
        ⟨16861, false, false, [15515], []⟩,
        ⟨13, true, false, [], [15515, 82807]⟩
      ]⟩,
    ⟨[82807, 9], [15513, 83129], .contexts [
        ⟨18939, true, false, [15514], [9]⟩,
        ⟨46, false, false, [15514, 83129], []⟩,
        ⟨16868, false, true, [], [83129]⟩
      ]⟩,
    ⟨[245, 83129], [245, 83129], .contexts []⟩,
    ⟨[83129], [83129], .contexts []⟩,
    ⟨[83129, 11], [245, 83129], .contexts [
        ⟨18934, true, false, [], [11]⟩,
        ⟨1051, false, false, [77371], []⟩,
        ⟨1052, false, false, [77371], []⟩,
        ⟨3767, false, false, [], [7]⟩,
        ⟨18931, false, false, [245], []⟩,
        ⟨18941, false, false, [], []⟩,
        ⟨18942, false, false, [245], []⟩,
        ⟨923, true, false, [], [83129]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 296. -/
def y322TCIndexRaw296 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15877], [6025, 9605], .source 8003⟩,
    ⟨[15877, 82691], [15877, 82691], .contexts []⟩,
    ⟨[83129, 13], [15877, 82691], .contexts [
        ⟨18934, true, false, [], [13]⟩,
        ⟨1056, false, false, [77371], []⟩,
        ⟨1057, false, false, [77371], []⟩,
        ⟨10577, false, false, [], [7]⟩,
        ⟨12223, false, false, [6025], [7]⟩,
        ⟨18944, true, false, [], [77397, 7]⟩,
        ⟨15438, false, false, [15877], []⟩,
        ⟨18945, false, false, [], []⟩,
        ⟨15456, false, false, [15877], []⟩,
        ⟨13, true, false, [], [15877, 82691]⟩
      ]⟩,
    ⟨[15879], [15876], .source 8004⟩,
    ⟨[82691, 13], [15879, 83129], .contexts [
        ⟨18946, true, false, [15876], [13]⟩,
        ⟨59, false, false, [15876, 83129], []⟩,
        ⟨18947, true, false, [], [83129]⟩
      ]⟩,
    ⟨[329, 83129], [329, 83129], .contexts []⟩,
    ⟨[83129, 15], [329, 83129], .contexts [
        ⟨18934, true, false, [], [15]⟩,
        ⟨1063, false, false, [77371], []⟩,
        ⟨1064, false, false, [77371], []⟩,
        ⟨1302, false, false, [], [7]⟩,
        ⟨18931, false, false, [329], []⟩,
        ⟨18949, false, false, [], []⟩,
        ⟨18942, false, false, [329], []⟩,
        ⟨1237, true, false, [], [83129]⟩
      ]⟩,
    ⟨[83131], [77727, 7], .source 41630⟩,
    ⟨[77727, 7], [83131], .contexts [
        ⟨18951, true, false, [], []⟩
      ]⟩,
    ⟨[77727, 7], [83131], .contexts [
        ⟨18952, false, false, [], []⟩
      ]⟩,
    ⟨[83131], [83131], .contexts []⟩,
    ⟨[83131], [83131], .contexts []⟩,
    ⟨[77727, 7], [83131], .contexts [
        ⟨18953, false, false, [], []⟩,
        ⟨18954, false, false, [], []⟩,
        ⟨18955, false, false, [], []⟩,
        ⟨18955, false, false, [], []⟩
      ]⟩,
    ⟨[293, 82765], [293, 82765], .contexts []⟩,
    ⟨[83131, 3], [293, 82765], .contexts [
        ⟨18956, true, false, [], [3]⟩,
        ⟨1034, false, false, [77727], []⟩,
        ⟨1035, false, false, [77727], []⟩,
        ⟨2464, false, false, [], [7]⟩,
        ⟨2465, false, false, [], [7]⟩,
        ⟨2462, false, false, [], [7]⟩,
        ⟨2463, false, false, [], [7]⟩,
        ⟨2463, false, false, [], [7]⟩,
        ⟨16358, false, false, [293], []⟩,
        ⟨18957, false, false, [], []⟩,
        ⟨16362, false, false, [293], []⟩,
        ⟨2379, true, false, [], [82765]⟩
      ]⟩,
    ⟨[149, 83131], [149, 83131], .contexts []⟩,
    ⟨[83131], [83131], .contexts []⟩,
    ⟨[83131, 5], [149, 83131], .contexts [
        ⟨18956, true, false, [], [5]⟩,
        ⟨1043, false, false, [77727], []⟩,
        ⟨1046, false, false, [77727], []⟩,
        ⟨3472, false, false, [], [7, 5, 7]⟩,
        ⟨3468, false, false, [], [7, 5, 7]⟩,
        ⟨3469, false, false, [], [7, 5, 7]⟩,
        ⟨3469, false, false, [], [7, 5, 7]⟩,
        ⟨3477, false, false, [], [5, 7]⟩,
        ⟨3474, false, false, [], [5, 7]⟩,
        ⟨3475, false, false, [], [5, 7]⟩,
        ⟨3475, false, false, [], [5, 7]⟩,
        ⟨3471, false, false, [149], [7]⟩,
        ⟨18952, false, false, [149], []⟩,
        ⟨18959, false, false, [], []⟩,
        ⟨18960, false, false, [149], []⟩
      ]⟩,
    ⟨[83131, 5], [149, 83131], .contexts [
        ⟨18961, false, false, [], []⟩,
        ⟨2385, true, false, [], [83131]⟩
      ]⟩,
    ⟨[135, 83131], [135, 83131], .contexts []⟩,
    ⟨[135, 83131], [135, 83131], .contexts []⟩,
    ⟨[83131, 9], [135, 83131], .contexts [
        ⟨18956, true, false, [], [9]⟩,
        ⟨1534, false, false, [77727], []⟩,
        ⟨1535, false, false, [77727], []⟩,
        ⟨2470, false, false, [], [7]⟩,
        ⟨2472, false, false, [], [7]⟩,
        ⟨2468, false, false, [], [7]⟩,
        ⟨2469, false, false, [], [7]⟩,
        ⟨2469, false, false, [], [7]⟩,
        ⟨18952, false, false, [135], []⟩,
        ⟨18963, false, false, [], []⟩,
        ⟨18964, false, false, [], []⟩,
        ⟨18960, false, false, [135], []⟩,
        ⟨564, true, false, [], [83131]⟩
      ]⟩,
    ⟨[151, 83131], [151, 83131], .contexts []⟩,
    ⟨[83131, 13], [82763], .contexts [
        ⟨18956, true, false, [], [13]⟩,
        ⟨1056, false, false, [77727], []⟩,
        ⟨1057, false, false, [77727], []⟩,
        ⟨2458, false, false, [], [7]⟩,
        ⟨2441, false, false, [], [7]⟩,
        ⟨2442, false, false, [], [7]⟩,
        ⟨2442, false, false, [], [7]⟩,
        ⟨16324, false, false, [], []⟩,
        ⟨16325, false, false, [], []⟩,
        ⟨16326, false, false, [], []⟩,
        ⟨16326, false, false, [], []⟩,
        ⟨16331, false, false, [], []⟩,
        ⟨672, true, false, [], [82763]⟩
      ]⟩,
    ⟨[82763, 13], [83131], .contexts [
        ⟨18967, true, false, [], [13]⟩,
        ⟨59, false, false, [83131], []⟩,
        ⟨18955, false, false, [], []⟩
      ]⟩,
    ⟨[863, 83131], [863, 83131], .contexts []⟩,
    ⟨[863, 83131], [863, 83131], .contexts []⟩,
    ⟨[83131, 15], [863, 83131], .contexts [
        ⟨18956, true, false, [], [15]⟩,
        ⟨1063, false, false, [77727], []⟩,
        ⟨1064, false, false, [77727], []⟩,
        ⟨2496, false, false, [], [7]⟩,
        ⟨18952, false, false, [863], []⟩,
        ⟨18969, false, false, [], []⟩,
        ⟨18970, false, false, [], []⟩,
        ⟨18960, false, false, [863], []⟩,
        ⟨2500, true, false, [], [83131]⟩
      ]⟩,
    ⟨[83133], [77735, 7], .source 41631⟩,
    ⟨[77735, 7], [83133], .contexts [
        ⟨18972, true, false, [], []⟩
      ]⟩,
    ⟨[83133, 7], [77735], .contexts [
        ⟨18973, true, false, [], [7]⟩,
        ⟨38, false, false, [77735], []⟩,
        ⟨2527, false, false, [], []⟩
      ]⟩,
    ⟨[77735, 7], [83133], .contexts [
        ⟨18973, false, false, [], []⟩
      ]⟩,
    ⟨[83133], [83133], .contexts []⟩,
    ⟨[83133], [83133], .contexts []⟩,
    ⟨[77735, 7], [83133], .contexts [
        ⟨18975, false, false, [], []⟩,
        ⟨18976, false, false, [], []⟩,
        ⟨18977, false, false, [], []⟩,
        ⟨18977, false, false, [], []⟩
      ]⟩,
    ⟨[1633, 83129], [1633, 83129], .contexts []⟩,
    ⟨[83133, 3], [1633, 83129], .contexts [
        ⟨18978, true, false, [], [3]⟩,
        ⟨1034, false, false, [77735], []⟩,
        ⟨1035, false, false, [77735], []⟩,
        ⟨4137, false, false, [], [7]⟩,
        ⟨4153, false, false, [], [7]⟩,
        ⟨4154, false, false, [], [7]⟩,
        ⟨4154, false, false, [], [7]⟩,
        ⟨18931, false, false, [1633], []⟩,
        ⟨18979, false, false, [], []⟩,
        ⟨18942, false, false, [1633], []⟩,
        ⟨13, true, false, [], [1633, 83129]⟩
      ]⟩,
    ⟨[83129, 3], [1635, 83133], .contexts [
        ⟨18980, true, false, [1632], [3]⟩,
        ⟨20, false, false, [1632, 83133], []⟩,
        ⟨4132, true, false, [], [83133]⟩
      ]⟩,
    ⟨[151, 83133], [151, 83133], .contexts []⟩,
    ⟨[151, 83133], [151, 83133], .contexts []⟩,
    ⟨[83133, 11], [83133, 11], .contexts []⟩,
    ⟨[83133], [83133], .contexts []⟩,
    ⟨[83133, 11], [151, 83133], .contexts [
        ⟨18984, false, false, [], []⟩,
        ⟨18978, true, false, [], [11]⟩,
        ⟨1051, false, false, [77735], []⟩,
        ⟨1052, false, false, [77735], []⟩,
        ⟨2532, false, false, [], [7]⟩,
        ⟨2534, false, false, [], [7]⟩,
        ⟨2529, false, false, [], [7]⟩,
        ⟨2531, false, false, [], [7]⟩,
        ⟨2531, false, false, [], [7]⟩,
        ⟨18973, false, false, [151], []⟩,
        ⟨18982, false, false, [], []⟩,
        ⟨18983, false, false, [], []⟩,
        ⟨18985, false, false, [151], []⟩,
        ⟨2391, true, false, [], [83133]⟩
      ]⟩,
    ⟨[863, 83133], [863, 83133], .contexts []⟩,
    ⟨[863, 83133], [863, 83133], .contexts []⟩,
    ⟨[83133, 15], [83133, 15], .contexts []⟩,
    ⟨[83133, 15], [863, 83133], .contexts [
        ⟨18989, false, false, [], []⟩,
        ⟨18978, true, false, [], [15]⟩,
        ⟨1063, false, false, [77735], []⟩,
        ⟨1064, false, false, [77735], []⟩,
        ⟨2545, false, false, [], [7]⟩,
        ⟨18973, false, false, [863], []⟩,
        ⟨18987, false, false, [], []⟩,
        ⟨18988, false, false, [], []⟩,
        ⟨18985, false, false, [863], []⟩,
        ⟨2500, true, false, [], [83133]⟩
      ]⟩,
    ⟨[83135], [82697, 5], .source 75070⟩,
    ⟨[82697, 5], [83135], .contexts [
        ⟨18991, true, false, [], []⟩
      ]⟩,
    ⟨[83135, 5], [82697], .contexts [
        ⟨18992, true, false, [], [5]⟩,
        ⟨28, false, false, [82697], []⟩,
        ⟨15504, false, false, [], []⟩
      ]⟩,
    ⟨[82697, 5], [83135], .source 75071⟩,
    ⟨[83135], [83135], .source 75072⟩,
    ⟨[83135], [83135], .source 75073⟩,
    ⟨[82697, 5], [83135], .contexts [
        ⟨18994, false, false, [], []⟩,
        ⟨18995, false, false, [], []⟩,
        ⟨18996, false, false, [], []⟩,
        ⟨18996, false, false, [], []⟩
      ]⟩,
    ⟨[15403, 82761], [15403, 82761], .contexts []⟩,
    ⟨[15403, 82761], [15403, 82761], .source 75074⟩,
    ⟨[15403, 83127], [15403, 83127], .contexts []⟩,
    ⟨[15403, 83127], [15403, 83127], .contexts []⟩,
    ⟨[83135, 1], [83135, 1], .contexts []⟩,
    ⟨[15403], [15403], .contexts [
        ⟨13, false, false, [], [15403]⟩
      ]⟩,
    ⟨[83135, 1], [15403, 83127], .contexts [
        ⟨19002, false, false, [], []⟩,
        ⟨18997, true, false, [], [1]⟩,
        ⟨161, false, false, [82697], []⟩,
        ⟨162, false, false, [82697], []⟩,
        ⟨16303, false, false, [], [5]⟩,
        ⟨18998, false, false, [], [5]⟩,
        ⟨18999, false, false, [], [5]⟩,
        ⟨18999, false, false, [], [5]⟩,
        ⟨18924, false, false, [15403], []⟩,
        ⟨19000, false, false, [], []⟩,
        ⟨19001, false, false, [], []⟩,
        ⟨18921, false, false, [15403], []⟩,
        ⟨19003, true, false, [], [83127]⟩
      ]⟩,
    ⟨[15401], [15402], .contexts [
        ⟨16302, true, true, [], []⟩
      ]⟩,
    ⟨[83127, 1], [15401, 83135], .contexts [
        ⟨19004, true, false, [15402], [1]⟩,
        ⟨8, false, false, [15402, 83135], []⟩,
        ⟨19005, true, false, [], [83135]⟩
      ]⟩,
    ⟨[15289, 83135], [15289, 83135], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 297. -/
def y322TCIndexRaw297 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15289, 83135], [15289, 83135], .contexts []⟩,
    ⟨[83135, 11], [83135, 11], .contexts []⟩,
    ⟨[83135], [83135], .contexts []⟩,
    ⟨[83135, 11], [15289, 83135], .contexts [
        ⟨19009, false, false, [], []⟩,
        ⟨18997, true, false, [], [11]⟩,
        ⟨174, false, false, [82697], []⟩,
        ⟨175, false, false, [82697], []⟩,
        ⟨15519, false, false, [], [5]⟩,
        ⟨15520, false, false, [], [5]⟩,
        ⟨15517, false, false, [], [5]⟩,
        ⟨15518, false, false, [], [5]⟩,
        ⟨15518, false, false, [], [5]⟩,
        ⟨18992, false, false, [15289], []⟩,
        ⟨19007, false, false, [], []⟩,
        ⟨19008, false, false, [], []⟩,
        ⟨19010, false, false, [15289], []⟩,
        ⟨15388, true, false, [], [83135]⟩
      ]⟩,
    ⟨[82683, 5], [15319, 82695], .contexts [
        ⟨15494, false, false, [], []⟩
      ]⟩,
    ⟨[15319, 82695], [15319, 82695], .contexts []⟩,
    ⟨[15319, 82695], [15319, 82695], .contexts []⟩,
    ⟨[83135, 13], [83135, 13], .contexts []⟩,
    ⟨[15319, 82695], [15319, 82695], .contexts [
        ⟨15499, false, false, [15319], []⟩
      ]⟩,
    ⟨[15319], [15319], .contexts [
        ⟨13, false, false, [], [15319]⟩
      ]⟩,
    ⟨[15319, 82695], [15319, 82695], .contexts [
        ⟨19017, true, false, [], [82695]⟩
      ]⟩,
    ⟨[83135, 13], [15319, 82695], .contexts [
        ⟨19015, false, false, [], []⟩,
        ⟨18997, true, false, [], [13]⟩,
        ⟨179, false, false, [82697], []⟩,
        ⟨180, false, false, [82697], []⟩,
        ⟨15502, false, false, [], [5]⟩,
        ⟨15339, false, false, [], [5]⟩,
        ⟨15340, false, false, [], [5]⟩,
        ⟨15340, false, false, [], [5]⟩,
        ⟨19012, false, false, [], []⟩,
        ⟨19013, false, false, [], []⟩,
        ⟨19014, false, false, [], []⟩,
        ⟨19014, false, false, [], []⟩,
        ⟨19016, false, false, [], []⟩,
        ⟨19018, false, false, [], []⟩
      ]⟩,
    ⟨[15317], [15318], .contexts [
        ⟨15493, true, true, [], []⟩
      ]⟩,
    ⟨[1075, 83135], [1075, 83135], .contexts []⟩,
    ⟨[1075, 83135], [1075, 83135], .contexts []⟩,
    ⟨[83135, 15], [83135, 15], .contexts []⟩,
    ⟨[83135, 15], [1075, 83135], .contexts [
        ⟨19023, false, false, [], []⟩,
        ⟨18997, true, false, [], [15]⟩,
        ⟨184, false, false, [82697], []⟩,
        ⟨185, false, false, [82697], []⟩,
        ⟨15524, false, false, [], [5]⟩,
        ⟨15526, false, false, [], [5]⟩,
        ⟨15522, false, false, [], [5]⟩,
        ⟨15523, false, false, [], [5]⟩,
        ⟨15523, false, false, [], [5]⟩,
        ⟨18992, false, false, [1075], []⟩,
        ⟨19021, false, false, [], []⟩,
        ⟨19022, false, false, [], []⟩,
        ⟨19010, false, false, [1075], []⟩,
        ⟨4778, true, false, [], [83135]⟩
      ]⟩,
    ⟨[83137], [83135, 7], .source 41633⟩,
    ⟨[83135, 7], [83137], .contexts [
        ⟨19025, true, false, [], []⟩
      ]⟩,
    ⟨[83137, 7], [83135], .contexts [
        ⟨19026, true, false, [], [7]⟩,
        ⟨38, false, false, [83135], []⟩,
        ⟨18996, false, false, [], []⟩
      ]⟩,
    ⟨[83135, 7], [83137], .contexts [
        ⟨19026, false, false, [], []⟩
      ]⟩,
    ⟨[83137], [83137], .contexts []⟩,
    ⟨[83137], [83137], .contexts []⟩,
    ⟨[83135, 7], [83137], .contexts [
        ⟨19028, false, false, [], []⟩,
        ⟨19029, false, false, [], []⟩,
        ⟨19030, false, false, [], []⟩,
        ⟨19030, false, false, [], []⟩
      ]⟩,
    ⟨[83135, 1], [15403, 83127], .contexts [
        ⟨19002, false, false, [], []⟩,
        ⟨19004, false, false, [], []⟩,
        ⟨19000, false, false, [], []⟩,
        ⟨19001, false, false, [], []⟩,
        ⟨19001, false, false, [], []⟩
      ]⟩,
    ⟨[15403, 83125], [15403, 83125], .contexts []⟩,
    ⟨[83137, 1], [15403, 83125], .contexts [
        ⟨19031, true, false, [], [1]⟩,
        ⟨1027, false, false, [83135], []⟩,
        ⟨1028, false, false, [83135], []⟩,
        ⟨19032, false, false, [], [7]⟩,
        ⟨18914, false, false, [15403], []⟩,
        ⟨19033, false, false, [], []⟩,
        ⟨18895, false, false, [15403], []⟩,
        ⟨19003, true, false, [], [83125]⟩
      ]⟩,
    ⟨[83125, 1], [15401, 83137], .contexts [
        ⟨19034, true, false, [15402], [1]⟩,
        ⟨8, false, false, [15402, 83137], []⟩,
        ⟨19005, true, false, [], [83137]⟩
      ]⟩,
    ⟨[83135, 5], [82697], .contexts [
        ⟨18993, false, false, [], []⟩,
        ⟨15503, false, false, [], []⟩,
        ⟨15504, false, false, [], []⟩,
        ⟨15504, false, false, [], []⟩
      ]⟩,
    ⟨[15321, 82369], [15321, 82369], .contexts []⟩,
    ⟨[15321, 82369], [15321, 82369], .contexts []⟩,
    ⟨[82367], [9159, 77371], .contexts [
        ⟨11977, false, false, [], []⟩
      ]⟩,
    ⟨[15881], [15321, 9159], .source 8005⟩,
    ⟨[15881, 83129], [15881, 83129], .contexts []⟩,
    ⟨[83137, 5], [15881, 83129], .contexts [
        ⟨19031, true, false, [], [5]⟩,
        ⟨1043, false, false, [83135], []⟩,
        ⟨1046, false, false, [83135], []⟩,
        ⟨19036, false, false, [], [7, 5, 7]⟩,
        ⟨15511, false, false, [], [5, 7]⟩,
        ⟨19037, false, false, [], [5, 7]⟩,
        ⟨19038, false, false, [], [5, 7]⟩,
        ⟨19038, false, false, [], [5, 7]⟩,
        ⟨10059, false, false, [15321], [7]⟩,
        ⟨19039, false, false, [15321], [7]⟩,
        ⟨19040, true, false, [], [77371, 7]⟩,
        ⟨18931, false, false, [15881], []⟩,
        ⟨19041, false, false, [], []⟩,
        ⟨18942, false, false, [15881], []⟩,
        ⟨13, true, false, [], [15881, 83129]⟩
      ]⟩,
    ⟨[15883], [15880], .source 8006⟩,
    ⟨[83129, 5], [15883, 83137], .contexts [
        ⟨19042, true, false, [15880], [5]⟩,
        ⟨28, false, false, [15880, 83137], []⟩,
        ⟨19043, true, false, [], [83137]⟩
      ]⟩,
    ⟨[83135, 11], [15289, 83135], .contexts [
        ⟨19009, false, false, [], []⟩,
        ⟨19011, false, false, [], []⟩,
        ⟨19007, false, false, [], []⟩,
        ⟨19008, false, false, [], []⟩,
        ⟨19008, false, false, [], []⟩
      ]⟩,
    ⟨[15289, 83137], [15289, 83137], .contexts []⟩,
    ⟨[83137], [83137], .contexts []⟩,
    ⟨[83137, 11], [15289, 83137], .contexts [
        ⟨19031, true, false, [], [11]⟩,
        ⟨1051, false, false, [83135], []⟩,
        ⟨1052, false, false, [83135], []⟩,
        ⟨19045, false, false, [], [7]⟩,
        ⟨19026, false, false, [15289], []⟩,
        ⟨19046, false, false, [], []⟩,
        ⟨19047, false, false, [15289], []⟩,
        ⟨15388, true, false, [], [83137]⟩
      ]⟩,
    ⟨[15319, 82695, 7], [15319, 82693], .contexts [
        ⟨15485, false, false, [15319], []⟩
      ]⟩,
    ⟨[15319, 82693], [15319, 82693], .contexts []⟩,
    ⟨[15319, 82693], [15319, 82693], .contexts []⟩,
    ⟨[15319, 82693], [15319, 82693], .contexts []⟩,
    ⟨[83137, 13], [83137, 13], .contexts []⟩,
    ⟨[15319, 82693], [15319, 82693], .contexts [
        ⟨15481, false, false, [15319], []⟩
      ]⟩,
    ⟨[15319, 82693], [15319, 82693], .contexts [
        ⟨19017, true, false, [], [82693]⟩
      ]⟩,
    ⟨[83137, 13], [15319, 82693], .contexts [
        ⟨19053, false, false, [], []⟩,
        ⟨19031, true, false, [], [13]⟩,
        ⟨1056, false, false, [83135], []⟩,
        ⟨1057, false, false, [83135], []⟩,
        ⟨19015, false, false, [], [7]⟩,
        ⟨19019, false, false, [], [7]⟩,
        ⟨19013, false, false, [], [7]⟩,
        ⟨19014, false, false, [], [7]⟩,
        ⟨19014, false, false, [], [7]⟩,
        ⟨19049, false, false, [], []⟩,
        ⟨19050, false, false, [], []⟩,
        ⟨19051, false, false, [], []⟩,
        ⟨19052, false, false, [], []⟩,
        ⟨19054, false, false, [], []⟩,
        ⟨19055, false, false, [], []⟩
      ]⟩,
    ⟨[83135, 15], [1075, 83135], .contexts [
        ⟨19023, false, false, [], []⟩,
        ⟨19024, false, false, [], []⟩,
        ⟨19021, false, false, [], []⟩,
        ⟨19022, false, false, [], []⟩,
        ⟨19022, false, false, [], []⟩
      ]⟩,
    ⟨[1075, 83137], [1075, 83137], .contexts []⟩,
    ⟨[83137, 15], [1075, 83137], .contexts [
        ⟨19031, true, false, [], [15]⟩,
        ⟨1063, false, false, [83135], []⟩,
        ⟨1064, false, false, [83135], []⟩,
        ⟨19057, false, false, [], [7]⟩,
        ⟨19026, false, false, [1075], []⟩,
        ⟨19058, false, false, [], []⟩,
        ⟨19047, false, false, [1075], []⟩,
        ⟨4778, true, false, [], [83137]⟩
      ]⟩,
    ⟨[83139], [77737, 7], .source 75075⟩,
    ⟨[77737, 7], [83139], .contexts [
        ⟨19060, true, false, [], []⟩
      ]⟩,
    ⟨[83139, 7], [77737], .contexts [
        ⟨19061, true, false, [], [7]⟩,
        ⟨38, false, false, [77737], []⟩,
        ⟨2543, false, false, [], []⟩
      ]⟩,
    ⟨[83139], [83139], .contexts []⟩,
    ⟨[83139], [83139], .source 75076⟩,
    ⟨[77737, 7], [83139], .source 75077⟩,
    ⟨[83139, 1], [5879, 78269], .source 75079⟩,
    ⟨[83139, 1], [5879, 78269], .contexts [
        ⟨19066, false, false, [], []⟩,
        ⟨13, true, false, [], [5879, 78269]⟩
      ]⟩,
    ⟨[15885], [5878], .source 8007⟩,
    ⟨[78269, 1], [15885, 83139], .contexts [
        ⟨19067, true, false, [5878], [1]⟩,
        ⟨8, false, false, [5878, 83139], []⟩,
        ⟨19068, true, false, [], [83139]⟩
      ]⟩,
    ⟨[15887], [1633, 15515], .source 8008⟩,
    ⟨[83139, 3], [15887, 82807], .contexts [
        ⟨19065, true, false, [], [3]⟩,
        ⟨1034, false, false, [77737], []⟩,
        ⟨1035, false, false, [77737], []⟩,
        ⟨4159, false, false, [], [7]⟩,
        ⟨4155, false, false, [], [7]⟩,
        ⟨4156, false, false, [], [7]⟩,
        ⟨4156, false, false, [], [7]⟩,
        ⟨16869, false, false, [1633], []⟩,
        ⟨19070, true, false, [], [82807]⟩,
        ⟨16861, false, false, [15887], []⟩,
        ⟨13, true, false, [], [15887, 82807]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 298. -/
def y322TCIndexRaw298 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15889], [15886], .source 8009⟩,
    ⟨[82807, 3], [15889, 83139], .contexts [
        ⟨19071, true, false, [15886], [3]⟩,
        ⟨20, false, false, [15886, 83139], []⟩,
        ⟨19072, true, false, [], [83139]⟩
      ]⟩,
    ⟨[83139, 9], [83139, 9], .contexts []⟩,
    ⟨[83139, 9], [83133], .contexts [
        ⟨19074, false, false, [], []⟩,
        ⟨19065, true, false, [], [9]⟩,
        ⟨1534, false, false, [77737], []⟩,
        ⟨1535, false, false, [77737], []⟩,
        ⟨2541, false, false, [], [7]⟩,
        ⟨2526, false, false, [], [7]⟩,
        ⟨2527, false, false, [], [7]⟩,
        ⟨2527, false, false, [], [7]⟩,
        ⟨18975, false, false, [], []⟩,
        ⟨18976, false, false, [], []⟩,
        ⟨18977, false, false, [], []⟩,
        ⟨18977, false, false, [], []⟩,
        ⟨18985, false, false, [], []⟩,
        ⟨672, true, false, [], [83133]⟩
      ]⟩,
    ⟨[15891], [1675, 11115], .source 75080⟩,
    ⟨[15893], [15891, 10665], .source 75081⟩,
    ⟨[15895], [15892], .source 75082⟩,
    ⟨[78539, 13], [15895, 83139], .source 75083⟩,
    ⟨[863, 83139], [863, 83139], .contexts []⟩,
    ⟨[863, 83139], [863, 83139], .contexts []⟩,
    ⟨[83139, 15], [83139, 15], .contexts []⟩,
    ⟨[83139], [83139], .contexts []⟩,
    ⟨[83139, 15], [863, 83139], .contexts [
        ⟨19082, false, false, [], []⟩,
        ⟨19065, true, false, [], [15]⟩,
        ⟨1063, false, false, [77737], []⟩,
        ⟨1064, false, false, [77737], []⟩,
        ⟨2548, false, false, [], [7]⟩,
        ⟨2550, false, false, [], [7]⟩,
        ⟨2546, false, false, [], [7]⟩,
        ⟨2547, false, false, [], [7]⟩,
        ⟨2547, false, false, [], [7]⟩,
        ⟨19061, false, false, [863], []⟩,
        ⟨19080, false, false, [], []⟩,
        ⟨19081, false, false, [], []⟩,
        ⟨19083, false, false, [863], []⟩,
        ⟨2500, true, false, [], [83139]⟩
      ]⟩,
    ⟨[83141], [82687, 5], .source 75084⟩,
    ⟨[82687, 5], [83141], .contexts [
        ⟨19085, true, false, [], []⟩
      ]⟩,
    ⟨[83141, 5], [82687], .contexts [
        ⟨19086, true, false, [], [5]⟩,
        ⟨28, false, false, [82687], []⟩,
        ⟨15398, false, false, [], []⟩
      ]⟩,
    ⟨[82687, 5], [83141], .source 75085⟩,
    ⟨[83141], [83141], .source 75086⟩,
    ⟨[83141], [83141], .source 75087⟩,
    ⟨[82687, 5], [83141], .contexts [
        ⟨19088, false, false, [], []⟩,
        ⟨19089, false, false, [], []⟩,
        ⟨19090, false, false, [], []⟩,
        ⟨19090, false, false, [], []⟩
      ]⟩,
    ⟨[2575, 83141], [2575, 83141], .contexts []⟩,
    ⟨[2575, 83141], [2575, 83141], .contexts []⟩,
    ⟨[83141, 1], [83141, 1], .contexts []⟩,
    ⟨[83141], [83141], .contexts []⟩,
    ⟨[83141, 1], [2575, 83141], .contexts [
        ⟨19094, false, false, [], []⟩,
        ⟨19091, true, false, [], [1]⟩,
        ⟨161, false, false, [82687], []⟩,
        ⟨162, false, false, [82687], []⟩,
        ⟨15402, false, false, [], [5]⟩,
        ⟨15405, false, false, [], [5]⟩,
        ⟨15400, false, false, [], [5]⟩,
        ⟨15401, false, false, [], [5]⟩,
        ⟨15401, false, false, [], [5]⟩,
        ⟨19086, false, false, [2575], []⟩,
        ⟨19092, false, false, [], []⟩,
        ⟨19093, false, false, [], []⟩,
        ⟨19095, false, false, [2575], []⟩,
        ⟨5618, true, false, [], [83141]⟩
      ]⟩,
    ⟨[83141, 9], [83141, 9], .contexts []⟩,
    ⟨[83141, 9], [83135], .contexts [
        ⟨19097, false, false, [], []⟩,
        ⟨19091, true, false, [], [9]⟩,
        ⟨1265, false, false, [82687], []⟩,
        ⟨1266, false, false, [82687], []⟩,
        ⟨15516, false, false, [], [5]⟩,
        ⟨15503, false, false, [], [5]⟩,
        ⟨15504, false, false, [], [5]⟩,
        ⟨15504, false, false, [], [5]⟩,
        ⟨18994, false, false, [], []⟩,
        ⟨18995, false, false, [], []⟩,
        ⟨18996, false, false, [], []⟩,
        ⟨18996, false, false, [], []⟩,
        ⟨19010, false, false, [], []⟩,
        ⟨672, true, false, [], [83135]⟩
      ]⟩,
    ⟨[83135, 9], [83141], .contexts [
        ⟨19098, true, false, [], [9]⟩,
        ⟨46, false, false, [83141], []⟩,
        ⟨19090, false, false, [], []⟩
      ]⟩,
    ⟨[79001, 5], [15279, 82681], .contexts [
        ⟨15333, false, false, [], []⟩
      ]⟩,
    ⟨[15279, 82681], [15279, 82681], .contexts []⟩,
    ⟨[15279, 82681], [15279, 82681], .contexts []⟩,
    ⟨[83141, 13], [83141, 13], .contexts []⟩,
    ⟨[15279], [15279], .contexts [
        ⟨13, false, false, [], [15279]⟩
      ]⟩,
    ⟨[83141, 13], [15279, 82681], .contexts [
        ⟨19103, false, false, [], []⟩,
        ⟨19091, true, false, [], [13]⟩,
        ⟨179, false, false, [82687], []⟩,
        ⟨180, false, false, [82687], []⟩,
        ⟨15395, false, false, [], [5]⟩,
        ⟨5475, false, false, [], [5]⟩,
        ⟨5476, false, false, [], [5]⟩,
        ⟨5476, false, false, [], [5]⟩,
        ⟨19100, false, false, [], []⟩,
        ⟨19101, false, false, [], []⟩,
        ⟨19102, false, false, [], []⟩,
        ⟨19102, false, false, [], []⟩,
        ⟨15496, false, false, [15279], []⟩,
        ⟨19104, true, false, [], [82681]⟩
      ]⟩,
    ⟨[15277], [15278], .contexts [
        ⟨15332, true, true, [], []⟩
      ]⟩,
    ⟨[82681, 13], [15277, 83141], .contexts [
        ⟨19105, true, false, [15278], [13]⟩,
        ⟨59, false, false, [15278, 83141], []⟩,
        ⟨19106, true, false, [], [83141]⟩
      ]⟩,
    ⟨[1075, 83141], [1075, 83141], .contexts []⟩,
    ⟨[1075, 83141], [1075, 83141], .contexts []⟩,
    ⟨[83141, 15], [83141, 15], .contexts []⟩,
    ⟨[83141, 15], [1075, 83141], .contexts [
        ⟨19110, false, false, [], []⟩,
        ⟨19091, true, false, [], [15]⟩,
        ⟨184, false, false, [82687], []⟩,
        ⟨185, false, false, [82687], []⟩,
        ⟨15412, false, false, [], [5]⟩,
        ⟨15413, false, false, [], [5]⟩,
        ⟨15410, false, false, [], [5]⟩,
        ⟨15411, false, false, [], [5]⟩,
        ⟨15411, false, false, [], [5]⟩,
        ⟨19086, false, false, [1075], []⟩,
        ⟨19108, false, false, [], []⟩,
        ⟨19109, false, false, [], []⟩,
        ⟨19095, false, false, [1075], []⟩,
        ⟨4778, true, false, [], [83141]⟩
      ]⟩,
    ⟨[83143], [83141, 7], .source 41636⟩,
    ⟨[83141, 7], [83143], .contexts [
        ⟨19112, true, false, [], []⟩
      ]⟩,
    ⟨[83143, 7], [83141], .contexts [
        ⟨19113, true, false, [], [7]⟩,
        ⟨38, false, false, [83141], []⟩,
        ⟨19090, false, false, [], []⟩
      ]⟩,
    ⟨[83141, 7], [83143], .contexts [
        ⟨19113, false, false, [], []⟩
      ]⟩,
    ⟨[83143], [83143], .contexts []⟩,
    ⟨[83143], [83143], .contexts []⟩,
    ⟨[83141, 7], [83143], .contexts [
        ⟨19115, false, false, [], []⟩,
        ⟨19116, false, false, [], []⟩,
        ⟨19117, false, false, [], []⟩,
        ⟨19117, false, false, [], []⟩
      ]⟩,
    ⟨[2575, 83143], [2575, 83143], .contexts []⟩,
    ⟨[83143], [83143], .contexts []⟩,
    ⟨[83143, 1], [2575, 83143], .contexts [
        ⟨19118, true, false, [], [1]⟩,
        ⟨1027, false, false, [83141], []⟩,
        ⟨1028, false, false, [83141], []⟩,
        ⟨19094, false, false, [], [7]⟩,
        ⟨19096, false, false, [], [7]⟩,
        ⟨19092, false, false, [], [7]⟩,
        ⟨19093, false, false, [], [7]⟩,
        ⟨19093, false, false, [], [7]⟩,
        ⟨19113, false, false, [2575], []⟩,
        ⟨19119, false, false, [], []⟩,
        ⟨19120, false, false, [2575], []⟩,
        ⟨5618, true, false, [], [83143]⟩
      ]⟩,
    ⟨[15295, 78419], [15295, 78419], .contexts []⟩,
    ⟨[15295, 78419], [15295, 78419], .contexts []⟩,
    ⟨[15897], [15295, 13147], .source 8013⟩,
    ⟨[15899], [15897, 15515], .source 8014⟩,
    ⟨[83143, 5], [15899, 82807], .contexts [
        ⟨19118, true, false, [], [5]⟩,
        ⟨1043, false, false, [83141], []⟩,
        ⟨1046, false, false, [83141], []⟩,
        ⟨19087, false, false, [], [7, 5, 7]⟩,
        ⟨15397, false, false, [], [7, 5, 7]⟩,
        ⟨15398, false, false, [], [7, 5, 7]⟩,
        ⟨15398, false, false, [], [7, 5, 7]⟩,
        ⟨15408, false, false, [], [5, 7]⟩,
        ⟨19122, false, false, [], [5, 7]⟩,
        ⟨19123, false, false, [], [5, 7]⟩,
        ⟨19123, false, false, [], [5, 7]⟩,
        ⟨5227, false, false, [15295], [7]⟩,
        ⟨10480, false, false, [15295, 1901], [7]⟩,
        ⟨13932, true, false, [15295], [77373, 7]⟩,
        ⟨19124, true, false, [], [77373, 7]⟩,
        ⟨16869, false, false, [15897], []⟩,
        ⟨19125, true, false, [], [82807]⟩,
        ⟨16861, false, false, [15899], []⟩
      ]⟩,
    ⟨[83143, 5], [15899, 82807], .contexts [
        ⟨19126, false, false, [], []⟩,
        ⟨13, true, false, [], [15899, 82807]⟩
      ]⟩,
    ⟨[15901], [15898], .source 8015⟩,
    ⟨[82807, 5], [15901, 83143], .contexts [
        ⟨19127, true, false, [15898], [5]⟩,
        ⟨28, false, false, [15898, 83143], []⟩,
        ⟨19128, true, false, [], [83143]⟩
      ]⟩,
    ⟨[83143, 9], [83137], .contexts [
        ⟨19118, true, false, [], [9]⟩,
        ⟨1534, false, false, [83141], []⟩,
        ⟨1535, false, false, [83141], []⟩,
        ⟨19097, false, false, [], [7]⟩,
        ⟨19098, false, false, [], [7]⟩,
        ⟨18995, false, false, [], [7]⟩,
        ⟨18996, false, false, [], [7]⟩,
        ⟨18996, false, false, [], [7]⟩,
        ⟨19028, false, false, [], []⟩,
        ⟨19029, false, false, [], []⟩,
        ⟨19030, false, false, [], []⟩,
        ⟨19030, false, false, [], []⟩,
        ⟨19047, false, false, [], []⟩,
        ⟨672, true, false, [], [83137]⟩
      ]⟩,
    ⟨[83137, 9], [83143], .contexts [
        ⟨19130, true, false, [], [9]⟩,
        ⟨46, false, false, [83143], []⟩,
        ⟨19117, false, false, [], []⟩
      ]⟩,
    ⟨[15279, 82679], [15279, 82679], .contexts []⟩,
    ⟨[83143, 13], [15279, 82679], .contexts [
        ⟨19118, true, false, [], [13]⟩,
        ⟨1056, false, false, [83141], []⟩,
        ⟨1057, false, false, [83141], []⟩,
        ⟨19103, false, false, [], [7]⟩,
        ⟨19105, false, false, [], [7]⟩,
        ⟨19101, false, false, [], [7]⟩,
        ⟨19102, false, false, [], [7]⟩,
        ⟨19102, false, false, [], [7]⟩,
        ⟨15310, false, false, [15279], []⟩,
        ⟨19132, false, false, [], []⟩,
        ⟨15475, false, false, [15279], []⟩,
        ⟨19104, true, false, [], [82679]⟩
      ]⟩,
    ⟨[82679, 13], [15277, 83143], .contexts [
        ⟨19133, true, false, [15278], [13]⟩,
        ⟨59, false, false, [15278, 83143], []⟩,
        ⟨19106, true, false, [], [83143]⟩
      ]⟩,
    ⟨[1075, 83143], [1075, 83143], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 299. -/
def y322TCIndexRaw299 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83143, 15], [1075, 83143], .contexts [
        ⟨19118, true, false, [], [15]⟩,
        ⟨1063, false, false, [83141], []⟩,
        ⟨1064, false, false, [83141], []⟩,
        ⟨19110, false, false, [], [7]⟩,
        ⟨19111, false, false, [], [7]⟩,
        ⟨19108, false, false, [], [7]⟩,
        ⟨19109, false, false, [], [7]⟩,
        ⟨19109, false, false, [], [7]⟩,
        ⟨19113, false, false, [1075], []⟩,
        ⟨19135, false, false, [], []⟩,
        ⟨19120, false, false, [1075], []⟩,
        ⟨4778, true, false, [], [83143]⟩
      ]⟩,
    ⟨[83145], [82807, 11], .source 41637⟩,
    ⟨[82807, 11], [83145], .contexts [
        ⟨19137, true, false, [], []⟩
      ]⟩,
    ⟨[83145, 11], [82807], .contexts [
        ⟨19138, true, false, [], [11]⟩,
        ⟨53, false, false, [82807], []⟩,
        ⟨16854, false, false, [], []⟩
      ]⟩,
    ⟨[83145], [83145], .contexts []⟩,
    ⟨[83145], [83145], .contexts []⟩,
    ⟨[82807, 11], [83145], .contexts [
        ⟨19138, false, false, [], []⟩,
        ⟨19140, false, false, [], []⟩,
        ⟨19141, false, false, [], []⟩,
        ⟨19141, false, false, [], []⟩
      ]⟩,
    ⟨[15511, 83145], [15511, 83145], .contexts []⟩,
    ⟨[83145], [83145], .contexts []⟩,
    ⟨[83145, 1], [15511, 83145], .contexts [
        ⟨19142, true, false, [], [1]⟩,
        ⟨562, false, false, [82807], []⟩,
        ⟨563, false, false, [82807], []⟩,
        ⟨16860, false, false, [], [11]⟩,
        ⟨16863, false, false, [], [11]⟩,
        ⟨16858, false, false, [], [11]⟩,
        ⟨16859, false, false, [], [11]⟩,
        ⟨16859, false, false, [], [11]⟩,
        ⟨19138, false, false, [15511], []⟩,
        ⟨19143, false, false, [], []⟩,
        ⟨19144, false, false, [15511], []⟩,
        ⟨16862, true, false, [], [83145]⟩
      ]⟩,
    ⟨[15513, 77373], [15513, 77373], .contexts []⟩,
    ⟨[15513, 77373], [15513, 77373], .contexts []⟩,
    ⟨[15513, 77375], [15513, 77375], .contexts []⟩,
    ⟨[83145, 7], [15513, 77375], .contexts [
        ⟨19142, true, false, [], [7]⟩,
        ⟨647, false, false, [82807], []⟩,
        ⟨648, false, false, [82807], []⟩,
        ⟨16865, false, false, [], [11]⟩,
        ⟨16867, false, false, [], [11]⟩,
        ⟨19146, false, false, [], [11]⟩,
        ⟨19147, false, false, [], [11]⟩,
        ⟨19147, false, false, [], [11]⟩,
        ⟨1306, false, false, [15513], []⟩,
        ⟨19148, false, false, [], []⟩,
        ⟨1311, false, false, [15513], []⟩,
        ⟨16866, true, false, [], [77375]⟩
      ]⟩,
    ⟨[77375, 7], [15515, 83145], .contexts [
        ⟨19149, true, false, [15512], [7]⟩,
        ⟨38, false, false, [15512, 83145], []⟩,
        ⟨16868, true, false, [], [83145]⟩
      ]⟩,
    ⟨[15513, 83129], [15513, 83129], .contexts []⟩,
    ⟨[15513, 83129], [15513, 83129], .contexts []⟩,
    ⟨[15903], [15513, 245], .source 8016⟩,
    ⟨[15905], [15903, 15515], .source 8017⟩,
    ⟨[15905, 83145], [15905, 83145], .contexts []⟩,
    ⟨[83145, 9], [15905, 83145], .contexts [
        ⟨19142, true, false, [], [9]⟩,
        ⟨221, false, false, [82807], []⟩,
        ⟨224, false, false, [82807], []⟩,
        ⟨18940, false, false, [], [11, 9, 11]⟩,
        ⟨19151, false, false, [], [11, 9, 11]⟩,
        ⟨19152, false, false, [], [11, 9, 11]⟩,
        ⟨19152, false, false, [], [11, 9, 11]⟩,
        ⟨18943, false, false, [15513], [9, 11]⟩,
        ⟨19153, true, false, [], [83129, 9, 11]⟩,
        ⟨18939, false, false, [15903], [11]⟩,
        ⟨19154, true, false, [], [82807, 11]⟩,
        ⟨19138, false, false, [15905], []⟩,
        ⟨19155, false, false, [], []⟩,
        ⟨19144, false, false, [15905], []⟩
      ]⟩,
    ⟨[83145, 9], [15905, 83145], .contexts [
        ⟨19156, false, false, [], []⟩,
        ⟨13, true, false, [], [15905, 83145]⟩
      ]⟩,
    ⟨[83145, 13], [82805], .contexts [
        ⟨19142, true, false, [], [13]⟩,
        ⟨227, false, false, [82807], []⟩,
        ⟨228, false, false, [82807], []⟩,
        ⟨16852, false, false, [], [11]⟩,
        ⟨5213, false, false, [], [11]⟩,
        ⟨5214, false, false, [], [11]⟩,
        ⟨5214, false, false, [], [11]⟩,
        ⟨16824, false, false, [], []⟩,
        ⟨16826, false, false, [], []⟩,
        ⟨16827, false, false, [], []⟩,
        ⟨16827, false, false, [], []⟩,
        ⟨16843, false, false, [], []⟩,
        ⟨672, true, false, [], [82805]⟩
      ]⟩,
    ⟨[82805, 13], [83145], .contexts [
        ⟨19158, true, false, [], [13]⟩,
        ⟨59, false, false, [83145], []⟩,
        ⟨19141, false, false, [], []⟩
      ]⟩,
    ⟨[1077, 83145], [1077, 83145], .contexts []⟩,
    ⟨[83145, 15], [1077, 83145], .contexts [
        ⟨19142, true, false, [], [15]⟩,
        ⟨231, false, false, [82807], []⟩,
        ⟨232, false, false, [82807], []⟩,
        ⟨16872, false, false, [], [11]⟩,
        ⟨16873, false, false, [], [11]⟩,
        ⟨16870, false, false, [], [11]⟩,
        ⟨16871, false, false, [], [11]⟩,
        ⟨16871, false, false, [], [11]⟩,
        ⟨19138, false, false, [1077], []⟩,
        ⟨19160, false, false, [], []⟩,
        ⟨19144, false, false, [1077], []⟩,
        ⟨4913, true, false, [], [83145]⟩
      ]⟩,
    ⟨[83147], [77699, 7], .source 41638⟩,
    ⟨[77699, 7], [83147], .contexts [
        ⟨19162, true, false, [], []⟩
      ]⟩,
    ⟨[83147, 7], [77699], .contexts [
        ⟨19163, true, false, [], [7]⟩,
        ⟨38, false, false, [77699], []⟩,
        ⟨2248, false, false, [], []⟩
      ]⟩,
    ⟨[83147], [83147], .contexts []⟩,
    ⟨[83147], [83147], .contexts []⟩,
    ⟨[77699, 7], [83147], .contexts [
        ⟨19163, false, false, [], []⟩,
        ⟨19165, false, false, [], []⟩,
        ⟨19166, false, false, [], []⟩,
        ⟨19166, false, false, [], []⟩
      ]⟩,
    ⟨[15907], [841, 1217], .source 8018⟩,
    ⟨[83147, 1], [15907, 78123], .contexts [
        ⟨19167, true, false, [], [1]⟩,
        ⟨1027, false, false, [77699], []⟩,
        ⟨1028, false, false, [77699], []⟩,
        ⟨2316, false, false, [], [7]⟩,
        ⟨2306, false, false, [], [7]⟩,
        ⟨2307, false, false, [], [7]⟩,
        ⟨2307, false, false, [], [7]⟩,
        ⟨3716, false, false, [841], []⟩,
        ⟨19168, true, false, [], [78123]⟩,
        ⟨3713, false, false, [15907], []⟩,
        ⟨13, true, false, [], [15907, 78123]⟩
      ]⟩,
    ⟨[15909], [15906], .source 8019⟩,
    ⟨[78123, 1], [15909, 83147], .contexts [
        ⟨19169, true, false, [15906], [1]⟩,
        ⟨8, false, false, [15906, 83147], []⟩,
        ⟨19170, true, false, [], [83147]⟩
      ]⟩,
    ⟨[5895, 77375], [5895, 77375], .contexts []⟩,
    ⟨[15911], [5895, 15515], .source 8020⟩,
    ⟨[83147, 3], [15911, 83145], .contexts [
        ⟨19167, true, false, [], [3]⟩,
        ⟨1034, false, false, [77699], []⟩,
        ⟨1035, false, false, [77699], []⟩,
        ⟨2320, false, false, [], [7]⟩,
        ⟨3158, false, false, [], [7]⟩,
        ⟨10486, false, false, [], [7]⟩,
        ⟨10487, true, false, [], [77375, 7]⟩,
        ⟨19172, false, false, [], [7]⟩,
        ⟨19172, false, false, [], [7]⟩,
        ⟨19150, false, false, [5895], []⟩,
        ⟨19173, true, false, [], [83145]⟩,
        ⟨19144, false, false, [15911], []⟩,
        ⟨13, true, false, [], [15911, 83145]⟩
      ]⟩,
    ⟨[15913], [15910], .source 8021⟩,
    ⟨[83145, 3], [15913, 83147], .contexts [
        ⟨19174, true, false, [15910], [3]⟩,
        ⟨20, false, false, [15910, 83147], []⟩,
        ⟨19175, true, false, [], [83147]⟩
      ]⟩,
    ⟨[1231, 83147], [1231, 83147], .contexts []⟩,
    ⟨[1231, 83147], [1231, 83147], .contexts []⟩,
    ⟨[83147, 9], [83147, 9], .contexts []⟩,
    ⟨[83147], [83147], .contexts []⟩,
    ⟨[83147, 9], [1231, 83147], .contexts [
        ⟨19179, false, false, [], []⟩,
        ⟨19167, true, false, [], [9]⟩,
        ⟨1534, false, false, [77699], []⟩,
        ⟨1535, false, false, [77699], []⟩,
        ⟨3147, false, false, [], [7]⟩,
        ⟨3148, false, false, [], [7]⟩,
        ⟨3153, false, false, [], [7]⟩,
        ⟨3154, false, false, [], [7]⟩,
        ⟨3154, false, false, [], [7]⟩,
        ⟨19163, false, false, [1231], []⟩,
        ⟨19177, false, false, [], []⟩,
        ⟨19178, false, false, [], []⟩,
        ⟨19180, false, false, [1231], []⟩,
        ⟨13, true, false, [], [1231, 83147]⟩
      ]⟩,
    ⟨[12771, 83139], [12771, 83139], .contexts []⟩,
    ⟨[83147, 11], [12771, 83139], .contexts [
        ⟨19167, true, false, [], [11]⟩,
        ⟨1051, false, false, [77699], []⟩,
        ⟨1052, false, false, [77699], []⟩,
        ⟨3878, false, false, [], [7]⟩,
        ⟨10474, false, false, [1473], [7]⟩,
        ⟨13747, true, false, [], [77737, 7]⟩,
        ⟨19061, false, false, [12771], []⟩,
        ⟨19182, false, false, [], []⟩,
        ⟨19083, false, false, [12771], []⟩,
        ⟨13, true, false, [], [12771, 83139]⟩
      ]⟩,
    ⟨[15915], [12770], .source 8022⟩,
    ⟨[83139, 11], [15915, 83147], .contexts [
        ⟨19183, true, false, [12770], [11]⟩,
        ⟨53, false, false, [12770, 83147], []⟩,
        ⟨19184, true, false, [], [83147]⟩
      ]⟩,
    ⟨[849, 83147], [849, 83147], .contexts []⟩,
    ⟨[849, 83147], [849, 83147], .contexts []⟩,
    ⟨[83147, 15], [83147, 15], .contexts []⟩,
    ⟨[83147, 15], [849, 83147], .contexts [
        ⟨19188, false, false, [], []⟩,
        ⟨19167, true, false, [], [15]⟩,
        ⟨1063, false, false, [77699], []⟩,
        ⟨1064, false, false, [77699], []⟩,
        ⟨2311, false, false, [], [7]⟩,
        ⟨2313, false, false, [], [7]⟩,
        ⟨2318, false, false, [], [7]⟩,
        ⟨2319, false, false, [], [7]⟩,
        ⟨2319, false, false, [], [7]⟩,
        ⟨19163, false, false, [849], []⟩,
        ⟨19186, false, false, [], []⟩,
        ⟨19187, false, false, [], []⟩,
        ⟨19180, false, false, [849], []⟩,
        ⟨13, true, false, [], [849, 83147]⟩
      ]⟩,
    ⟨[82837, 5], [83149], .source 75089⟩,
    ⟨[83149, 5], [82837], .contexts [
        ⟨19190, true, false, [], [5]⟩,
        ⟨28, false, false, [82837], []⟩,
        ⟨17276, false, false, [], []⟩
      ]⟩,
    ⟨[83149], [83149], .contexts []⟩,
    ⟨[83149], [83149], .source 75090⟩,
    ⟨[82837, 5], [83149], .source 75091⟩,
    ⟨[2575, 83149], [2575, 83149], .contexts []⟩,
    ⟨[2575, 83149], [2575, 83149], .contexts []⟩,
    ⟨[83149, 1], [2575, 83149], .source 75092⟩,
    ⟨[83149], [83149], .contexts []⟩,
    ⟨[83149, 1], [2575, 83149], .contexts [
        ⟨19197, false, false, [], []⟩,
        ⟨19198, false, false, [2575], []⟩,
        ⟨5618, true, false, [], [83149]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 300. -/
def y322TCIndexRaw300 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15289, 83149], [15289, 83149], .contexts []⟩,
    ⟨[15289, 83149], [15289, 83149], .contexts []⟩,
    ⟨[83149, 9], [83149, 9], .contexts []⟩,
    ⟨[83149, 9], [15289, 83149], .contexts [
        ⟨19202, false, false, [], []⟩,
        ⟨19194, true, false, [], [9]⟩,
        ⟨1265, false, false, [82837], []⟩,
        ⟨1266, false, false, [82837], []⟩,
        ⟨17293, false, false, [], [5]⟩,
        ⟨17294, false, false, [], [5]⟩,
        ⟨17291, false, false, [], [5]⟩,
        ⟨17292, false, false, [], [5]⟩,
        ⟨17292, false, false, [], [5]⟩,
        ⟨19190, false, false, [15289], []⟩,
        ⟨19200, false, false, [], []⟩,
        ⟨19201, false, false, [], []⟩,
        ⟨19198, false, false, [15289], []⟩,
        ⟨15388, true, false, [], [83149]⟩
      ]⟩,
    ⟨[82837, 11], [82687], .source 75093⟩,
    ⟨[83149, 11], [83149, 11], .contexts []⟩,
    ⟨[83141], [83141], .contexts [
        ⟨19095, false, false, [], []⟩
      ]⟩,
    ⟨[83141], [83141], .contexts [
        ⟨672, true, false, [], [83141]⟩
      ]⟩,
    ⟨[83149, 11], [83141], .contexts [
        ⟨19205, false, false, [], []⟩,
        ⟨19194, true, false, [], [11]⟩,
        ⟨174, false, false, [82837], []⟩,
        ⟨175, false, false, [82837], []⟩,
        ⟨19204, false, false, [], [5]⟩,
        ⟨15398, false, false, [], [5]⟩,
        ⟨19088, false, false, [], []⟩,
        ⟨19089, false, false, [], []⟩,
        ⟨19090, false, false, [], []⟩,
        ⟨19090, false, false, [], []⟩,
        ⟨19206, false, false, [], []⟩,
        ⟨19207, false, false, [], []⟩
      ]⟩,
    ⟨[83141, 11], [83149], .contexts [
        ⟨19208, true, false, [], [11]⟩,
        ⟨53, false, false, [83149], []⟩,
        ⟨19193, false, false, [], []⟩
      ]⟩,
    ⟨[15607, 82835], [15607, 82835], .contexts []⟩,
    ⟨[15607, 82835], [15607, 82835], .source 75094⟩,
    ⟨[83149, 13], [15607, 82835], .source 75095⟩,
    ⟨[15605], [15606], .contexts [
        ⟨17257, true, true, [], []⟩
      ]⟩,
    ⟨[82835, 13], [15605, 83149], .contexts [
        ⟨19212, true, false, [15606], [13]⟩,
        ⟨59, false, false, [15606, 83149], []⟩,
        ⟨19213, true, false, [], [83149]⟩
      ]⟩,
    ⟨[1075, 83149], [1075, 83149], .contexts []⟩,
    ⟨[1075, 83149], [1075, 83149], .contexts []⟩,
    ⟨[83149, 15], [83149, 15], .contexts []⟩,
    ⟨[83149, 15], [1075, 83149], .contexts [
        ⟨19217, false, false, [], []⟩,
        ⟨19194, true, false, [], [15]⟩,
        ⟨184, false, false, [82837], []⟩,
        ⟨185, false, false, [82837], []⟩,
        ⟨17300, false, false, [], [5]⟩,
        ⟨17302, false, false, [], [5]⟩,
        ⟨17298, false, false, [], [5]⟩,
        ⟨17299, false, false, [], [5]⟩,
        ⟨17299, false, false, [], [5]⟩,
        ⟨19190, false, false, [1075], []⟩,
        ⟨19215, false, false, [], []⟩,
        ⟨19216, false, false, [], []⟩,
        ⟨19198, false, false, [1075], []⟩,
        ⟨4778, true, false, [], [83149]⟩
      ]⟩,
    ⟨[83151], [83149, 7], .source 41640⟩,
    ⟨[83149, 7], [83151], .contexts [
        ⟨19219, true, false, [], []⟩
      ]⟩,
    ⟨[83151, 7], [83149], .contexts [
        ⟨19220, true, false, [], [7]⟩,
        ⟨38, false, false, [83149], []⟩,
        ⟨19193, false, false, [], []⟩
      ]⟩,
    ⟨[83151], [83151], .contexts []⟩,
    ⟨[83151], [83151], .contexts []⟩,
    ⟨[83149, 7], [83151], .contexts [
        ⟨19220, false, false, [], []⟩,
        ⟨19222, false, false, [], []⟩,
        ⟨19223, false, false, [], []⟩,
        ⟨19223, false, false, [], []⟩
      ]⟩,
    ⟨[83149, 1], [2575, 83149], .contexts [
        ⟨19199, false, false, [], []⟩
      ]⟩,
    ⟨[2575, 83151], [2575, 83151], .contexts []⟩,
    ⟨[83151], [83151], .contexts []⟩,
    ⟨[83151, 1], [2575, 83151], .contexts [
        ⟨19224, true, false, [], [1]⟩,
        ⟨1027, false, false, [83149], []⟩,
        ⟨1028, false, false, [83149], []⟩,
        ⟨19225, false, false, [], [7]⟩,
        ⟨19195, false, false, [], [7]⟩,
        ⟨19196, false, false, [], [7]⟩,
        ⟨19196, false, false, [], [7]⟩,
        ⟨19220, false, false, [2575], []⟩,
        ⟨19226, false, false, [], []⟩,
        ⟨19227, false, false, [2575], []⟩,
        ⟨5618, true, false, [], [83151]⟩
      ]⟩,
    ⟨[15609, 78417], [15609, 78417], .contexts []⟩,
    ⟨[15609, 78417], [15609, 78417], .contexts []⟩,
    ⟨[15917], [15609, 5891], .source 8023⟩,
    ⟨[15919], [15917, 15515], .source 8024⟩,
    ⟨[83151, 5], [15919, 83145], .contexts [
        ⟨19224, true, false, [], [5]⟩,
        ⟨1043, false, false, [83149], []⟩,
        ⟨1046, false, false, [83149], []⟩,
        ⟨19191, false, false, [], [7, 5, 7]⟩,
        ⟨17275, false, false, [], [7, 5, 7]⟩,
        ⟨17276, false, false, [], [7, 5, 7]⟩,
        ⟨17276, false, false, [], [7, 5, 7]⟩,
        ⟨17289, false, false, [], [5, 7]⟩,
        ⟨19229, false, false, [], [5, 7]⟩,
        ⟨19230, false, false, [], [5, 7]⟩,
        ⟨19230, false, false, [], [5, 7]⟩,
        ⟨4380, false, false, [15609], [7]⟩,
        ⟨10488, false, false, [15609], [7]⟩,
        ⟨19231, true, false, [], [77375, 7]⟩,
        ⟨19150, false, false, [15917], []⟩,
        ⟨19232, true, false, [], [83145]⟩,
        ⟨19144, false, false, [15919], []⟩
      ]⟩,
    ⟨[83151, 5], [15919, 83145], .contexts [
        ⟨19233, false, false, [], []⟩,
        ⟨13, true, false, [], [15919, 83145]⟩
      ]⟩,
    ⟨[15921], [15918], .source 8025⟩,
    ⟨[83145, 5], [15921, 83151], .contexts [
        ⟨19234, true, false, [15918], [5]⟩,
        ⟨28, false, false, [15918, 83151], []⟩,
        ⟨19235, true, false, [], [83151]⟩
      ]⟩,
    ⟨[15289, 83151], [15289, 83151], .contexts []⟩,
    ⟨[83151, 9], [15289, 83151], .contexts [
        ⟨19224, true, false, [], [9]⟩,
        ⟨1534, false, false, [83149], []⟩,
        ⟨1535, false, false, [83149], []⟩,
        ⟨19202, false, false, [], [7]⟩,
        ⟨19203, false, false, [], [7]⟩,
        ⟨19200, false, false, [], [7]⟩,
        ⟨19201, false, false, [], [7]⟩,
        ⟨19201, false, false, [], [7]⟩,
        ⟨19220, false, false, [15289], []⟩,
        ⟨19237, false, false, [], []⟩,
        ⟨19227, false, false, [15289], []⟩,
        ⟨15388, true, false, [], [83151]⟩
      ]⟩,
    ⟨[83151, 11], [83143], .contexts [
        ⟨19224, true, false, [], [11]⟩,
        ⟨1051, false, false, [83149], []⟩,
        ⟨1052, false, false, [83149], []⟩,
        ⟨19205, false, false, [], [7]⟩,
        ⟨19208, false, false, [], [7]⟩,
        ⟨19089, false, false, [], [7]⟩,
        ⟨19090, false, false, [], [7]⟩,
        ⟨19090, false, false, [], [7]⟩,
        ⟨19115, false, false, [], []⟩,
        ⟨19116, false, false, [], []⟩,
        ⟨19117, false, false, [], []⟩,
        ⟨19117, false, false, [], []⟩,
        ⟨19120, false, false, [], []⟩,
        ⟨672, true, false, [], [83143]⟩
      ]⟩,
    ⟨[83143, 11], [83151], .contexts [
        ⟨19239, true, false, [], [11]⟩,
        ⟨53, false, false, [83151], []⟩,
        ⟨19223, false, false, [], []⟩
      ]⟩,
    ⟨[15607, 82833], [15607, 82833], .contexts []⟩,
    ⟨[83151, 13], [15607, 82833], .contexts [
        ⟨19224, true, false, [], [13]⟩,
        ⟨1056, false, false, [83149], []⟩,
        ⟨1057, false, false, [83149], []⟩,
        ⟨19212, false, false, [], [7]⟩,
        ⟨19210, false, false, [], [7]⟩,
        ⟨19211, false, false, [], [7]⟩,
        ⟨19211, false, false, [], [7]⟩,
        ⟨17249, false, false, [15607], []⟩,
        ⟨19241, false, false, [], []⟩,
        ⟨17236, false, false, [15607], []⟩,
        ⟨13, true, false, [], [15607, 82833]⟩
      ]⟩,
    ⟨[1075, 83151], [1075, 83151], .contexts []⟩,
    ⟨[83151, 15], [1075, 83151], .contexts [
        ⟨19224, true, false, [], [15]⟩,
        ⟨1063, false, false, [83149], []⟩,
        ⟨1064, false, false, [83149], []⟩,
        ⟨19217, false, false, [], [7]⟩,
        ⟨19218, false, false, [], [7]⟩,
        ⟨19215, false, false, [], [7]⟩,
        ⟨19216, false, false, [], [7]⟩,
        ⟨19216, false, false, [], [7]⟩,
        ⟨19220, false, false, [1075], []⟩,
        ⟨19243, false, false, [], []⟩,
        ⟨19227, false, false, [1075], []⟩,
        ⟨4778, true, false, [], [83151]⟩
      ]⟩,
    ⟨[83153], [77587, 7], .source 41641⟩,
    ⟨[77587, 7], [83153], .contexts [
        ⟨19245, true, false, [], []⟩
      ]⟩,
    ⟨[83153, 7], [77587], .contexts [
        ⟨19246, true, false, [], [7]⟩,
        ⟨38, false, false, [77587], []⟩,
        ⟨1881, false, false, [], []⟩
      ]⟩,
    ⟨[83153], [83153], .contexts []⟩,
    ⟨[83153], [83153], .contexts []⟩,
    ⟨[77587, 7], [83153], .contexts [
        ⟨19246, false, false, [], []⟩,
        ⟨19248, false, false, [], []⟩,
        ⟨19249, false, false, [], []⟩,
        ⟨19249, false, false, [], []⟩
      ]⟩,
    ⟨[715, 77591], [715, 77591], .contexts []⟩,
    ⟨[715, 77591], [715, 77591], .contexts []⟩,
    ⟨[15923], [715, 695], .source 8026⟩,
    ⟨[83153, 1], [15923, 78549], .contexts [
        ⟨19250, true, false, [], [1]⟩,
        ⟨1027, false, false, [77587], []⟩,
        ⟨1028, false, false, [77587], []⟩,
        ⟨1989, false, false, [], [7]⟩,
        ⟨19251, false, false, [], [7]⟩,
        ⟨19252, false, false, [], [7]⟩,
        ⟨19252, false, false, [], [7]⟩,
        ⟨4613, false, false, [715], []⟩,
        ⟨19253, true, false, [], [78549]⟩,
        ⟨4881, false, false, [15923], []⟩,
        ⟨13, true, false, [], [15923, 78549]⟩
      ]⟩,
    ⟨[15925], [15922], .source 8027⟩,
    ⟨[78549, 1], [15925, 83153], .contexts [
        ⟨19254, true, false, [15922], [1]⟩,
        ⟨8, false, false, [15922, 83153], []⟩,
        ⟨19255, true, false, [], [83153]⟩
      ]⟩,
    ⟨[15927], [5925, 15503], .source 8028⟩,
    ⟨[83153, 3], [15927, 82805], .contexts [
        ⟨19250, true, false, [], [3]⟩,
        ⟨1034, false, false, [77587], []⟩,
        ⟨1035, false, false, [77587], []⟩,
        ⟨1895, false, false, [], [7]⟩,
        ⟨10505, false, false, [], [7]⟩,
        ⟨10504, false, false, [], [7]⟩,
        ⟨10504, false, false, [], [7]⟩,
        ⟨16835, false, false, [5925], []⟩,
        ⟨19257, true, false, [], [82805]⟩,
        ⟨16843, false, false, [15927], []⟩,
        ⟨13, true, false, [], [15927, 82805]⟩
      ]⟩,
    ⟨[15929], [15926], .source 8029⟩,
    ⟨[82805, 3], [15929, 83153], .contexts [
        ⟨19258, true, false, [15926], [3]⟩,
        ⟨20, false, false, [15926, 83153], []⟩,
        ⟨19259, true, false, [], [83153]⟩
      ]⟩,
    ⟨[713, 83153], [713, 83153], .contexts []⟩,
    ⟨[713, 83153], [713, 83153], .contexts []⟩,
    ⟨[83153, 9], [83153, 9], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 301. -/
def y322TCIndexRaw301 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[713], [713], .contexts [
        ⟨13, false, false, [], [713]⟩
      ]⟩,
    ⟨[83153, 9], [713, 83153], .contexts [
        ⟨19263, false, false, [], []⟩,
        ⟨19250, true, false, [], [9]⟩,
        ⟨1534, false, false, [77587], []⟩,
        ⟨1535, false, false, [77587], []⟩,
        ⟨1983, false, false, [], [7]⟩,
        ⟨1985, false, false, [], [7]⟩,
        ⟨2001, false, false, [], [7]⟩,
        ⟨2002, false, false, [], [7]⟩,
        ⟨2002, false, false, [], [7]⟩,
        ⟨19246, false, false, [713], []⟩,
        ⟨19261, false, false, [], []⟩,
        ⟨19262, false, false, [], []⟩,
        ⟨19264, true, false, [], [83153]⟩
      ]⟩,
    ⟨[15931], [1429, 10667], .source 8030⟩,
    ⟨[15933], [15931, 10665], .source 8031⟩,
    ⟨[83153, 11], [15933, 78539], .contexts [
        ⟨19250, true, false, [], [11]⟩,
        ⟨1051, false, false, [77587], []⟩,
        ⟨1052, false, false, [77587], []⟩,
        ⟨3797, false, false, [], [7]⟩,
        ⟨12684, false, false, [1429], [7]⟩,
        ⟨19266, true, false, [], [77913, 7]⟩,
        ⟨12695, false, false, [15931], []⟩,
        ⟨19267, true, false, [], [78539]⟩,
        ⟨4781, false, false, [15933], []⟩,
        ⟨13, true, false, [], [15933, 78539]⟩
      ]⟩,
    ⟨[15935], [15932], .source 8032⟩,
    ⟨[78539, 11], [15935, 83153], .contexts [
        ⟨19268, true, false, [15932], [11]⟩,
        ⟨53, false, false, [15932, 83153], []⟩,
        ⟨19269, true, false, [], [83153]⟩
      ]⟩,
    ⟨[1291, 77699], [1291, 77699], .contexts []⟩,
    ⟨[1291, 77699], [1291, 77699], .contexts []⟩,
    ⟨[1291, 83147], [1291, 83147], .contexts []⟩,
    ⟨[83153, 13], [1291, 83147], .contexts [
        ⟨19250, true, false, [], [13]⟩,
        ⟨1056, false, false, [77587], []⟩,
        ⟨1057, false, false, [77587], []⟩,
        ⟨3246, false, false, [], [7]⟩,
        ⟨19271, false, false, [], [7]⟩,
        ⟨19272, false, false, [], [7]⟩,
        ⟨19272, false, false, [], [7]⟩,
        ⟨19163, false, false, [1291], []⟩,
        ⟨19273, false, false, [], []⟩,
        ⟨19180, false, false, [1291], []⟩,
        ⟨13, true, false, [], [1291, 83147]⟩
      ]⟩,
    ⟨[83147, 13], [1289, 83153], .contexts [
        ⟨19274, true, false, [1290], [13]⟩,
        ⟨59, false, false, [1290, 83153], []⟩,
        ⟨3245, false, true, [], [83153]⟩
      ]⟩,
    ⟨[15937], [1851, 11485], .source 8033⟩,
    ⟨[15939], [15937, 11493], .source 8034⟩,
    ⟨[83153, 15], [15939, 78743], .contexts [
        ⟨19250, true, false, [], [15]⟩,
        ⟨1063, false, false, [77587], []⟩,
        ⟨1064, false, false, [77587], []⟩,
        ⟨4477, false, false, [], [7]⟩,
        ⟨13024, false, false, [1851], [7]⟩,
        ⟨19276, true, false, [], [77673, 7]⟩,
        ⟨13028, false, false, [15937], []⟩,
        ⟨19277, true, false, [], [78743]⟩,
        ⟨4995, false, false, [15939], []⟩,
        ⟨13, true, false, [], [15939, 78743]⟩
      ]⟩,
    ⟨[15941], [15938], .source 8035⟩,
    ⟨[78743, 15], [15941, 83153], .contexts [
        ⟨19278, true, false, [15938], [15]⟩,
        ⟨1, false, false, [15938, 83153], []⟩,
        ⟨19279, true, false, [], [83153]⟩
      ]⟩,
    ⟨[83155], [82709, 5], .source 41642⟩,
    ⟨[82709, 5], [83155], .contexts [
        ⟨19281, true, false, [], []⟩
      ]⟩,
    ⟨[83155, 5], [82709], .contexts [
        ⟨19282, true, false, [], [5]⟩,
        ⟨28, false, false, [82709], []⟩,
        ⟨15629, false, false, [], []⟩
      ]⟩,
    ⟨[83155], [83155], .contexts []⟩,
    ⟨[83155], [83155], .contexts []⟩,
    ⟨[82709, 5], [83155], .contexts [
        ⟨19282, false, false, [], []⟩,
        ⟨19284, false, false, [], []⟩,
        ⟨19285, false, false, [], []⟩,
        ⟨19285, false, false, [], []⟩
      ]⟩,
    ⟨[15331, 79179], [15331, 79179], .contexts []⟩,
    ⟨[15331, 79179], [15331, 79179], .contexts []⟩,
    ⟨[15331, 82821], [15331, 82821], .contexts []⟩,
    ⟨[15331, 82821], [15331, 82821], .contexts []⟩,
    ⟨[83155, 9], [83155, 9], .contexts []⟩,
    ⟨[83155, 9], [15331, 82821], .contexts [
        ⟨19291, false, false, [], []⟩,
        ⟨19286, true, false, [], [9]⟩,
        ⟨1265, false, false, [82709], []⟩,
        ⟨1266, false, false, [82709], []⟩,
        ⟨15642, false, false, [], [5]⟩,
        ⟨15644, false, false, [], [5]⟩,
        ⟨19287, false, false, [], [5]⟩,
        ⟨19288, false, false, [], [5]⟩,
        ⟨19288, false, false, [], [5]⟩,
        ⟨17070, false, false, [15331], []⟩,
        ⟨19289, false, false, [], []⟩,
        ⟨19290, false, false, [], []⟩,
        ⟨15643, true, false, [], [82821]⟩
      ]⟩,
    ⟨[82821, 9], [15333, 83155], .contexts [
        ⟨19292, true, false, [15330], [9]⟩,
        ⟨46, false, false, [15330, 83155], []⟩,
        ⟨15645, true, false, [], [83155]⟩
      ]⟩,
    ⟨[151, 83155], [151, 83155], .contexts []⟩,
    ⟨[151, 83155], [151, 83155], .contexts []⟩,
    ⟨[83155, 11], [83155, 11], .contexts []⟩,
    ⟨[83155], [83155], .contexts []⟩,
    ⟨[83155, 11], [151, 83155], .contexts [
        ⟨19296, false, false, [], []⟩,
        ⟨19286, true, false, [], [11]⟩,
        ⟨174, false, false, [82709], []⟩,
        ⟨175, false, false, [82709], []⟩,
        ⟨15649, false, false, [], [5]⟩,
        ⟨15651, false, false, [], [5]⟩,
        ⟨15647, false, false, [], [5]⟩,
        ⟨15648, false, false, [], [5]⟩,
        ⟨15648, false, false, [], [5]⟩,
        ⟨19282, false, false, [151], []⟩,
        ⟨19294, false, false, [], []⟩,
        ⟨19295, false, false, [], []⟩,
        ⟨19297, false, false, [151], []⟩,
        ⟨2391, true, false, [], [83155]⟩
      ]⟩,
    ⟨[15329, 82705], [15329, 82705], .contexts []⟩,
    ⟨[15329, 82705], [15329, 82705], .contexts []⟩,
    ⟨[83155, 15], [83155, 15], .contexts []⟩,
    ⟨[15329], [15329], .contexts [
        ⟨13, false, false, [], [15329]⟩
      ]⟩,
    ⟨[83155, 15], [15329, 82705], .contexts [
        ⟨19301, false, false, [], []⟩,
        ⟨19286, true, false, [], [15]⟩,
        ⟨184, false, false, [82709], []⟩,
        ⟨185, false, false, [82709], []⟩,
        ⟨15626, false, false, [], [5]⟩,
        ⟨15416, false, false, [], [5]⟩,
        ⟨15417, false, false, [], [5]⟩,
        ⟨15417, false, false, [], [5]⟩,
        ⟨15603, false, false, [], []⟩,
        ⟨19299, false, false, [], []⟩,
        ⟨19300, false, false, [], []⟩,
        ⟨19300, false, false, [], []⟩,
        ⟨15607, false, false, [15329], []⟩,
        ⟨19302, true, false, [], [82705]⟩
      ]⟩,
    ⟨[9933], [15328], .contexts [
        ⟨15602, true, true, [], []⟩
      ]⟩,
    ⟨[82705, 15], [9933, 83155], .contexts [
        ⟨19303, true, false, [15328], [15]⟩,
        ⟨1, false, false, [15328, 83155], []⟩,
        ⟨19304, true, false, [], [83155]⟩
      ]⟩,
    ⟨[83157], [83155, 7], .source 41643⟩,
    ⟨[83155, 7], [83157], .contexts [
        ⟨19306, true, false, [], []⟩
      ]⟩,
    ⟨[83157, 7], [83155], .contexts [
        ⟨19307, true, false, [], [7]⟩,
        ⟨38, false, false, [83155], []⟩,
        ⟨19285, false, false, [], []⟩
      ]⟩,
    ⟨[83157], [83157], .contexts []⟩,
    ⟨[83157], [83157], .contexts []⟩,
    ⟨[83155, 7], [83157], .contexts [
        ⟨19307, false, false, [], []⟩,
        ⟨19309, false, false, [], []⟩,
        ⟨19310, false, false, [], []⟩,
        ⟨19310, false, false, [], []⟩
      ]⟩,
    ⟨[15943], [543, 5979], .source 8036⟩,
    ⟨[15945], [15943, 15575], .source 8037⟩,
    ⟨[83157, 5], [15945, 82825], .contexts [
        ⟨19311, true, false, [], [5]⟩,
        ⟨1043, false, false, [83155], []⟩,
        ⟨1046, false, false, [83155], []⟩,
        ⟨19283, false, false, [], [7, 5, 7]⟩,
        ⟨15628, false, false, [], [7, 5, 7]⟩,
        ⟨15629, false, false, [], [7, 5, 7]⟩,
        ⟨15629, false, false, [], [7, 5, 7]⟩,
        ⟨15652, false, false, [], [5, 7]⟩,
        ⟨2665, false, false, [], [5, 7]⟩,
        ⟨2666, false, false, [], [5, 7]⟩,
        ⟨2666, false, false, [], [5, 7]⟩,
        ⟨1799, false, false, [543], [7]⟩,
        ⟨10542, false, false, [543], [7]⟩,
        ⟨19312, true, false, [], [77389, 7]⟩,
        ⟨17134, false, false, [15943], []⟩,
        ⟨19313, true, false, [], [82825]⟩,
        ⟨17126, false, false, [15945], []⟩
      ]⟩,
    ⟨[83157, 5], [15945, 82825], .contexts [
        ⟨19314, false, false, [], []⟩,
        ⟨13, true, false, [], [15945, 82825]⟩
      ]⟩,
    ⟨[15947], [15944], .source 8038⟩,
    ⟨[82825, 5], [15947, 83157], .contexts [
        ⟨19315, true, false, [15944], [5]⟩,
        ⟨28, false, false, [15944, 83157], []⟩,
        ⟨19316, true, false, [], [83157]⟩
      ]⟩,
    ⟨[15331, 82823], [15331, 82823], .contexts []⟩,
    ⟨[82823], [82823], .contexts []⟩,
    ⟨[83157, 9], [15331, 82823], .contexts [
        ⟨19311, true, false, [], [9]⟩,
        ⟨1534, false, false, [83155], []⟩,
        ⟨1535, false, false, [83155], []⟩,
        ⟨19291, false, false, [], [7]⟩,
        ⟨19292, false, false, [], [7]⟩,
        ⟨19289, false, false, [], [7]⟩,
        ⟨19290, false, false, [], [7]⟩,
        ⟨19290, false, false, [], [7]⟩,
        ⟨17087, false, false, [15331], []⟩,
        ⟨19318, false, false, [], []⟩,
        ⟨19319, false, false, [15331], []⟩,
        ⟨15643, true, false, [], [82823]⟩
      ]⟩,
    ⟨[82823, 9], [15333, 83157], .contexts [
        ⟨19320, true, false, [15330], [9]⟩,
        ⟨46, false, false, [15330, 83157], []⟩,
        ⟨15645, true, false, [], [83157]⟩
      ]⟩,
    ⟨[151, 83157], [151, 83157], .contexts []⟩,
    ⟨[83157], [83157], .contexts []⟩,
    ⟨[83157, 11], [151, 83157], .contexts [
        ⟨19311, true, false, [], [11]⟩,
        ⟨1051, false, false, [83155], []⟩,
        ⟨1052, false, false, [83155], []⟩,
        ⟨19296, false, false, [], [7]⟩,
        ⟨19298, false, false, [], [7]⟩,
        ⟨19294, false, false, [], [7]⟩,
        ⟨19295, false, false, [], [7]⟩,
        ⟨19295, false, false, [], [7]⟩,
        ⟨19307, false, false, [151], []⟩,
        ⟨19322, false, false, [], []⟩,
        ⟨19323, false, false, [151], []⟩,
        ⟨2391, true, false, [], [83157]⟩
      ]⟩,
    ⟨[15329, 82703], [15329, 82703], .contexts []⟩,
    ⟨[83157, 15], [15329, 82703], .contexts [
        ⟨19311, true, false, [], [15]⟩,
        ⟨1063, false, false, [83155], []⟩,
        ⟨1064, false, false, [83155], []⟩,
        ⟨19301, false, false, [], [7]⟩,
        ⟨19303, false, false, [], [7]⟩,
        ⟨19299, false, false, [], [7]⟩,
        ⟨19300, false, false, [], [7]⟩,
        ⟨19300, false, false, [], [7]⟩,
        ⟨15589, false, false, [15329], []⟩,
        ⟨19325, false, false, [], []⟩,
        ⟨15585, false, false, [15329], []⟩,
        ⟨19302, true, false, [], [82703]⟩
      ]⟩,
    ⟨[82703, 15], [9933, 83157], .contexts [
        ⟨19326, true, false, [15328], [15]⟩,
        ⟨1, false, false, [15328, 83157], []⟩,
        ⟨19304, true, false, [], [83157]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 302. -/
def y322TCIndexRaw302 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83159], [78997, 5], .source 41644⟩,
    ⟨[78997, 5], [83159], .contexts [
        ⟨19328, true, false, [], []⟩
      ]⟩,
    ⟨[83159, 5], [78997], .contexts [
        ⟨19329, true, false, [], [5]⟩,
        ⟨28, false, false, [78997], []⟩,
        ⟨5432, false, false, [], []⟩
      ]⟩,
    ⟨[83159], [83159], .contexts []⟩,
    ⟨[83159], [83159], .contexts []⟩,
    ⟨[78997, 5], [83159], .contexts [
        ⟨19329, false, false, [], []⟩,
        ⟨19331, false, false, [], []⟩,
        ⟨19332, false, false, [], []⟩,
        ⟨19332, false, false, [], []⟩
      ]⟩,
    ⟨[15301, 82709], [15301, 82709], .contexts []⟩,
    ⟨[15301, 82709], [15301, 82709], .contexts []⟩,
    ⟨[15301, 83155], [15301, 83155], .contexts []⟩,
    ⟨[15301, 83155], [15301, 83155], .contexts []⟩,
    ⟨[83159, 1], [83159, 1], .contexts []⟩,
    ⟨[15301], [15301], .contexts [
        ⟨13, false, false, [], [15301]⟩
      ]⟩,
    ⟨[83159, 1], [15301, 83155], .contexts [
        ⟨19338, false, false, [], []⟩,
        ⟨19333, true, false, [], [1]⟩,
        ⟨161, false, false, [78997], []⟩,
        ⟨162, false, false, [78997], []⟩,
        ⟨15635, false, false, [], [5]⟩,
        ⟨19334, false, false, [], [5]⟩,
        ⟨19335, false, false, [], [5]⟩,
        ⟨19335, false, false, [], [5]⟩,
        ⟨19282, false, false, [15301], []⟩,
        ⟨19336, false, false, [], []⟩,
        ⟨19337, false, false, [], []⟩,
        ⟨19297, false, false, [15301], []⟩,
        ⟨19339, true, false, [], [83155]⟩
      ]⟩,
    ⟨[15299], [15300], .contexts [
        ⟨15423, true, true, [], []⟩
      ]⟩,
    ⟨[83155, 1], [15299, 83159], .contexts [
        ⟨19340, true, false, [15300], [1]⟩,
        ⟨8, false, false, [15300, 83159], []⟩,
        ⟨19341, true, false, [], [83159]⟩
      ]⟩,
    ⟨[83159, 9], [83159, 9], .contexts []⟩,
    ⟨[83159, 9], [78831], .contexts [
        ⟨19343, false, false, [], []⟩,
        ⟨19333, true, false, [], [9]⟩,
        ⟨1265, false, false, [78997], []⟩,
        ⟨1266, false, false, [78997], []⟩,
        ⟨5429, false, false, [], [5]⟩,
        ⟨5100, false, false, [], [5]⟩,
        ⟨5101, false, false, [], [5]⟩,
        ⟨5101, false, false, [], [5]⟩,
        ⟨5119, false, false, [], []⟩,
        ⟨5120, false, false, [], []⟩,
        ⟨5121, false, false, [], []⟩,
        ⟨5121, false, false, [], []⟩,
        ⟨5551, false, false, [], []⟩,
        ⟨5552, false, false, [], []⟩
      ]⟩,
    ⟨[78831, 9], [83159], .contexts [
        ⟨19344, true, false, [], [9]⟩,
        ⟨46, false, false, [83159], []⟩,
        ⟨19332, false, false, [], []⟩
      ]⟩,
    ⟨[2241, 83159], [2241, 83159], .contexts []⟩,
    ⟨[2241, 83159], [2241, 83159], .contexts []⟩,
    ⟨[83159, 11], [83159, 11], .contexts []⟩,
    ⟨[83159], [83159], .contexts []⟩,
    ⟨[83159, 11], [2241, 83159], .contexts [
        ⟨19348, false, false, [], []⟩,
        ⟨19333, true, false, [], [11]⟩,
        ⟨174, false, false, [78997], []⟩,
        ⟨175, false, false, [78997], []⟩,
        ⟨5449, false, false, [], [5]⟩,
        ⟨5463, false, false, [], [5]⟩,
        ⟨5464, false, false, [], [5]⟩,
        ⟨5465, false, false, [], [5]⟩,
        ⟨5465, false, false, [], [5]⟩,
        ⟨19329, false, false, [2241], []⟩,
        ⟨19346, false, false, [], []⟩,
        ⟨19347, false, false, [], []⟩,
        ⟨19349, false, false, [2241], []⟩,
        ⟨4929, true, false, [], [83159]⟩
      ]⟩,
    ⟨[1075, 83159], [1075, 83159], .contexts []⟩,
    ⟨[1075, 83159], [1075, 83159], .contexts []⟩,
    ⟨[83159, 13], [83159, 13], .contexts []⟩,
    ⟨[83159, 13], [1075, 83159], .contexts [
        ⟨19353, false, false, [], []⟩,
        ⟨19333, true, false, [], [13]⟩,
        ⟨179, false, false, [78997], []⟩,
        ⟨180, false, false, [78997], []⟩,
        ⟨5446, false, false, [], [5]⟩,
        ⟨15521, false, false, [], [5]⟩,
        ⟨5444, false, false, [], [5]⟩,
        ⟨5445, false, false, [], [5]⟩,
        ⟨5445, false, false, [], [5]⟩,
        ⟨19329, false, false, [1075], []⟩,
        ⟨19351, false, false, [], []⟩,
        ⟨19352, false, false, [], []⟩,
        ⟨19349, false, false, [1075], []⟩,
        ⟨4778, true, false, [], [83159]⟩
      ]⟩,
    ⟨[83159, 15], [83159, 15], .contexts []⟩,
    ⟨[83159, 15], [15319, 82695], .contexts [
        ⟨19355, false, false, [], []⟩,
        ⟨19333, true, false, [], [15]⟩,
        ⟨184, false, false, [78997], []⟩,
        ⟨185, false, false, [78997], []⟩,
        ⟨15358, false, false, [], [5]⟩,
        ⟨15339, false, false, [], [5]⟩,
        ⟨15340, false, false, [], [5]⟩,
        ⟨15340, false, false, [], [5]⟩,
        ⟨19012, false, false, [], []⟩,
        ⟨19013, false, false, [], []⟩,
        ⟨19014, false, false, [], []⟩,
        ⟨19014, false, false, [], []⟩,
        ⟨19016, false, false, [], []⟩,
        ⟨19018, false, false, [], []⟩
      ]⟩,
    ⟨[82695, 15], [15317, 83159], .contexts [
        ⟨19356, true, false, [15318], [15]⟩,
        ⟨1, false, false, [15318, 83159], []⟩,
        ⟨19020, true, false, [], [83159]⟩
      ]⟩,
    ⟨[83161], [83159, 7], .source 41645⟩,
    ⟨[83159, 7], [83161], .contexts [
        ⟨19358, true, false, [], []⟩
      ]⟩,
    ⟨[83161, 7], [83159], .contexts [
        ⟨19359, true, false, [], [7]⟩,
        ⟨38, false, false, [83159], []⟩,
        ⟨19332, false, false, [], []⟩
      ]⟩,
    ⟨[83161], [83161], .contexts []⟩,
    ⟨[83161], [83161], .contexts []⟩,
    ⟨[83159, 7], [83161], .contexts [
        ⟨19359, false, false, [], []⟩,
        ⟨19361, false, false, [], []⟩,
        ⟨19362, false, false, [], []⟩,
        ⟨19362, false, false, [], []⟩
      ]⟩,
    ⟨[83159, 1], [15301, 83155], .contexts [
        ⟨19340, false, false, [], []⟩
      ]⟩,
    ⟨[15301, 83157], [15301, 83157], .contexts []⟩,
    ⟨[83161, 1], [15301, 83157], .contexts [
        ⟨19363, true, false, [], [1]⟩,
        ⟨1027, false, false, [83159], []⟩,
        ⟨1028, false, false, [83159], []⟩,
        ⟨19338, false, false, [], [7]⟩,
        ⟨19364, false, false, [], [7]⟩,
        ⟨19336, false, false, [], [7]⟩,
        ⟨19337, false, false, [], [7]⟩,
        ⟨19337, false, false, [], [7]⟩,
        ⟨19307, false, false, [15301], []⟩,
        ⟨19365, false, false, [], []⟩,
        ⟨19323, false, false, [15301], []⟩,
        ⟨19339, true, false, [], [83157]⟩
      ]⟩,
    ⟨[83157, 1], [15299, 83161], .contexts [
        ⟨19366, true, false, [15300], [1]⟩,
        ⟨8, false, false, [15300, 83161], []⟩,
        ⟨19341, true, false, [], [83161]⟩
      ]⟩,
    ⟨[83159, 5], [78997], .contexts [
        ⟨19330, false, false, [], []⟩,
        ⟨5431, false, false, [], []⟩,
        ⟨5432, false, false, [], []⟩,
        ⟨5432, false, false, [], []⟩
      ]⟩,
    ⟨[15949], [8777, 12147], .source 8039⟩,
    ⟨[15951], [8759, 15949], .source 8040⟩,
    ⟨[15953], [8761, 15951], .source 8041⟩,
    ⟨[15955], [15953, 12153], .source 8042⟩,
    ⟨[83161, 5], [83161, 5], .contexts []⟩,
    ⟨[15955], [15955], .contexts [
        ⟨13, false, false, [], [15955]⟩
      ]⟩,
    ⟨[83161, 5], [15955, 78839], .contexts [
        ⟨19373, false, false, [], []⟩,
        ⟨19363, true, false, [], [5]⟩,
        ⟨1043, false, false, [83159], []⟩,
        ⟨1046, false, false, [83159], []⟩,
        ⟨19368, false, false, [], [7, 5, 7]⟩,
        ⟨5448, false, false, [], [5, 7]⟩,
        ⟨12229, false, false, [], [5, 7]⟩,
        ⟨11736, false, false, [], [5, 7]⟩,
        ⟨11736, false, false, [], [5, 7]⟩,
        ⟨11738, false, false, [8761], [7]⟩,
        ⟨11750, false, false, [8761, 8759], [7]⟩,
        ⟨13383, false, false, [8761, 8759, 8777], [7]⟩,
        ⟨19369, true, false, [8761, 8759], [77393, 7]⟩,
        ⟨19370, true, false, [8761], [77393, 7]⟩,
        ⟨19371, true, false, [], [77393, 7]⟩,
        ⟨13387, false, false, [15953], []⟩,
        ⟨19372, true, false, [], [78839]⟩,
        ⟨5186, false, false, [15955], []⟩,
        ⟨19374, true, false, [], [78839]⟩
      ]⟩,
    ⟨[15957], [15954], .source 8043⟩,
    ⟨[83161, 9], [83161, 9], .contexts []⟩,
    ⟨[83161, 9], [78833], .contexts [
        ⟨19377, false, false, [], []⟩,
        ⟨19363, true, false, [], [9]⟩,
        ⟨1534, false, false, [83159], []⟩,
        ⟨1535, false, false, [83159], []⟩,
        ⟨19343, false, false, [], [7]⟩,
        ⟨19344, false, false, [], [7]⟩,
        ⟨5120, false, false, [], [7]⟩,
        ⟨5121, false, false, [], [7]⟩,
        ⟨5121, false, false, [], [7]⟩,
        ⟨5132, false, false, [], []⟩,
        ⟨5133, false, false, [], []⟩,
        ⟨5134, false, false, [], []⟩,
        ⟨5134, false, false, [], []⟩,
        ⟨5538, false, false, [], []⟩,
        ⟨5539, false, false, [], []⟩
      ]⟩,
    ⟨[78833, 9], [83161], .contexts [
        ⟨19378, true, false, [], [9]⟩,
        ⟨46, false, false, [83161], []⟩,
        ⟨19362, false, false, [], []⟩
      ]⟩,
    ⟨[83159, 11], [2241, 83159], .contexts [
        ⟨19348, false, false, [], []⟩,
        ⟨19350, false, false, [], []⟩,
        ⟨19346, false, false, [], []⟩,
        ⟨19347, false, false, [], []⟩,
        ⟨19347, false, false, [], []⟩
      ]⟩,
    ⟨[2241, 83161], [2241, 83161], .contexts []⟩,
    ⟨[2241, 83161], [2241, 83161], .contexts []⟩,
    ⟨[83161, 11], [83161, 11], .contexts []⟩,
    ⟨[83161], [83161], .contexts []⟩,
    ⟨[83161, 11], [2241, 83161], .contexts [
        ⟨19383, false, false, [], []⟩,
        ⟨19363, true, false, [], [11]⟩,
        ⟨1051, false, false, [83159], []⟩,
        ⟨1052, false, false, [83159], []⟩,
        ⟨19380, false, false, [], [7]⟩,
        ⟨19359, false, false, [2241], []⟩,
        ⟨19381, false, false, [], []⟩,
        ⟨19382, false, false, [], []⟩,
        ⟨19384, false, false, [2241], []⟩,
        ⟨4929, true, false, [], [83161]⟩
      ]⟩,
    ⟨[83159, 13], [1075, 83159], .contexts [
        ⟨19353, false, false, [], []⟩,
        ⟨19354, false, false, [], []⟩,
        ⟨19351, false, false, [], []⟩,
        ⟨19352, false, false, [], []⟩,
        ⟨19352, false, false, [], []⟩
      ]⟩,
    ⟨[1075, 83161], [1075, 83161], .contexts []⟩,
    ⟨[1075, 83161], [1075, 83161], .contexts []⟩,
    ⟨[83161, 13], [83161, 13], .contexts []⟩,
    ⟨[83161, 13], [1075, 83161], .contexts [
        ⟨19389, false, false, [], []⟩,
        ⟨19363, true, false, [], [13]⟩,
        ⟨1056, false, false, [83159], []⟩,
        ⟨1057, false, false, [83159], []⟩,
        ⟨19386, false, false, [], [7]⟩,
        ⟨19359, false, false, [1075], []⟩,
        ⟨19387, false, false, [], []⟩,
        ⟨19388, false, false, [], []⟩,
        ⟨19384, false, false, [1075], []⟩,
        ⟨4778, true, false, [], [83161]⟩
      ]⟩,
    ⟨[83161, 15], [15319, 82693], .contexts [
        ⟨19363, true, false, [], [15]⟩,
        ⟨1063, false, false, [83159], []⟩,
        ⟨1064, false, false, [83159], []⟩,
        ⟨19355, false, false, [], [7]⟩,
        ⟨19356, false, false, [], [7]⟩,
        ⟨19013, false, false, [], [7]⟩,
        ⟨19014, false, false, [], [7]⟩,
        ⟨19014, false, false, [], [7]⟩,
        ⟨19049, false, false, [], []⟩,
        ⟨19050, false, false, [], []⟩,
        ⟨19051, false, false, [], []⟩,
        ⟨19052, false, false, [], []⟩,
        ⟨19054, false, false, [], []⟩,
        ⟨19055, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 303. -/
def y322TCIndexRaw303 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[82693, 15], [15317, 83161], .contexts [
        ⟨19391, true, false, [15318], [15]⟩,
        ⟨1, false, false, [15318, 83161], []⟩,
        ⟨19020, true, false, [], [83161]⟩
      ]⟩,
    ⟨[83163], [78377, 7], .source 41646⟩,
    ⟨[78377, 7], [83163], .contexts [
        ⟨19393, true, false, [], []⟩
      ]⟩,
    ⟨[83163], [83163], .contexts []⟩,
    ⟨[83163], [83163], .contexts []⟩,
    ⟨[78377, 7], [83163], .contexts [
        ⟨19394, false, false, [], []⟩,
        ⟨19395, false, false, [], []⟩,
        ⟨19396, false, false, [], []⟩,
        ⟨19396, false, false, [], []⟩
      ]⟩,
    ⟨[1671, 83163], [1671, 83163], .contexts []⟩,
    ⟨[83163], [83163], .contexts []⟩,
    ⟨[83163, 1], [1671, 83163], .contexts [
        ⟨19397, true, false, [], [1]⟩,
        ⟨1027, false, false, [78377], []⟩,
        ⟨1028, false, false, [78377], []⟩,
        ⟨4166, false, false, [], [7]⟩,
        ⟨4186, false, false, [], [7]⟩,
        ⟨4187, false, false, [], [7]⟩,
        ⟨4187, false, false, [], [7]⟩,
        ⟨19394, false, false, [1671], []⟩,
        ⟨19398, false, false, [], []⟩,
        ⟨19399, false, false, [1671], []⟩,
        ⟨13, true, false, [], [1671, 83163]⟩
      ]⟩,
    ⟨[9909, 82691], [9909, 82691], .contexts []⟩,
    ⟨[83163, 3], [9909, 82691], .contexts [
        ⟨19397, true, false, [], [3]⟩,
        ⟨1034, false, false, [78377], []⟩,
        ⟨1035, false, false, [78377], []⟩,
        ⟨10582, false, false, [], [7]⟩,
        ⟨12223, false, false, [6041], [7]⟩,
        ⟨12258, true, false, [], [77397, 7]⟩,
        ⟨15438, false, false, [9909], []⟩,
        ⟨19401, false, false, [], []⟩,
        ⟨15456, false, false, [9909], []⟩,
        ⟨13, true, false, [], [9909, 82691]⟩
      ]⟩,
    ⟨[15959], [9908], .source 8044⟩,
    ⟨[82691, 3], [15959, 83163], .contexts [
        ⟨19402, true, false, [9908], [3]⟩,
        ⟨20, false, false, [9908, 83163], []⟩,
        ⟨19403, true, false, [], [83163]⟩
      ]⟩,
    ⟨[11115, 77913], [11115, 77913], .contexts []⟩,
    ⟨[15961], [11115, 10665], .source 8045⟩,
    ⟨[83163, 9], [15961, 78539], .contexts [
        ⟨19397, true, false, [], [9]⟩,
        ⟨1534, false, false, [78377], []⟩,
        ⟨1535, false, false, [78377], []⟩,
        ⟨4066, false, false, [], [7]⟩,
        ⟨12755, false, false, [], [7]⟩,
        ⟨19405, false, false, [], [7]⟩,
        ⟨19405, false, false, [], [7]⟩,
        ⟨12695, false, false, [11115], []⟩,
        ⟨19406, true, false, [], [78539]⟩,
        ⟨4781, false, false, [15961], []⟩,
        ⟨13, true, false, [], [15961, 78539]⟩
      ]⟩,
    ⟨[15963], [15960], .source 8046⟩,
    ⟨[1665, 83163], [1665, 83163], .contexts []⟩,
    ⟨[1661, 77735], [1661, 77735], .contexts []⟩,
    ⟨[1661, 77735], [1661, 77735], .contexts []⟩,
    ⟨[1661, 83133], [1661, 83133], .contexts []⟩,
    ⟨[83163, 13], [1661, 83133], .contexts [
        ⟨19397, true, false, [], [13]⟩,
        ⟨1056, false, false, [78377], []⟩,
        ⟨1057, false, false, [78377], []⟩,
        ⟨4161, false, false, [], [7]⟩,
        ⟨19410, false, false, [], [7]⟩,
        ⟨19411, false, false, [], [7]⟩,
        ⟨19411, false, false, [], [7]⟩,
        ⟨18973, false, false, [1661], []⟩,
        ⟨19412, false, false, [], []⟩,
        ⟨18985, false, false, [1661], []⟩,
        ⟨13, true, false, [], [1661, 83133]⟩
      ]⟩,
    ⟨[83133, 13], [1659, 83163], .contexts [
        ⟨19413, true, false, [1660], [13]⟩,
        ⟨59, false, false, [1660, 83163], []⟩,
        ⟨4160, false, true, [], [83163]⟩
      ]⟩,
    ⟨[6043, 78723], [6043, 78723], .contexts []⟩,
    ⟨[6043, 78723], [6043, 78723], .contexts []⟩,
    ⟨[6043, 78741], [6043, 78741], .contexts []⟩,
    ⟨[83163, 15], [6043, 78741], .contexts [
        ⟨19397, true, false, [], [15]⟩,
        ⟨1063, false, false, [78377], []⟩,
        ⟨1064, false, false, [78377], []⟩,
        ⟨10584, false, false, [], [7]⟩,
        ⟨19415, false, false, [], [7]⟩,
        ⟨19416, false, false, [], [7]⟩,
        ⟨19416, false, false, [], [7]⟩,
        ⟨4969, false, false, [6043], []⟩,
        ⟨19417, false, false, [], []⟩,
        ⟨4965, false, false, [6043], []⟩,
        ⟨13, true, false, [], [6043, 78741]⟩
      ]⟩,
    ⟨[15965], [6042], .source 8047⟩,
    ⟨[78741, 15], [15965, 83163], .contexts [
        ⟨19418, true, false, [6042], [15]⟩,
        ⟨1, false, false, [6042, 83163], []⟩,
        ⟨19419, true, false, [], [83163]⟩
      ]⟩,
    ⟨[83165], [79377, 5], .source 75096⟩,
    ⟨[79377, 5], [83165], .contexts [
        ⟨19421, true, false, [], []⟩
      ]⟩,
    ⟨[83165, 5], [79377], .contexts [
        ⟨19422, true, false, [], [5]⟩,
        ⟨28, false, false, [79377], []⟩,
        ⟨6817, false, false, [], []⟩
      ]⟩,
    ⟨[83165], [83165], .contexts []⟩,
    ⟨[83165], [83165], .source 75097⟩,
    ⟨[79377, 5], [83165], .source 75098⟩,
    ⟨[2007, 83165], [2007, 83165], .contexts []⟩,
    ⟨[2007, 83165], [2007, 83165], .contexts []⟩,
    ⟨[83165, 1], [83165, 1], .contexts []⟩,
    ⟨[83165], [83165], .contexts []⟩,
    ⟨[83165, 1], [2007, 83165], .contexts [
        ⟨19429, false, false, [], []⟩,
        ⟨19426, true, false, [], [1]⟩,
        ⟨161, false, false, [79377], []⟩,
        ⟨162, false, false, [79377], []⟩,
        ⟨6822, false, false, [], [5]⟩,
        ⟨6825, false, false, [], [5]⟩,
        ⟨6820, false, false, [], [5]⟩,
        ⟨6821, false, false, [], [5]⟩,
        ⟨6821, false, false, [], [5]⟩,
        ⟨19422, false, false, [2007], []⟩,
        ⟨19427, false, false, [], []⟩,
        ⟨19428, false, false, [], []⟩,
        ⟨19430, false, false, [2007], []⟩,
        ⟨5405, true, false, [], [83165]⟩
      ]⟩,
    ⟨[83165, 9], [79371], .source 75099⟩,
    ⟨[83165, 9], [83165, 9], .contexts []⟩,
    ⟨[83165, 9], [79371], .contexts [
        ⟨19433, false, false, [], []⟩,
        ⟨19432, false, false, [], []⟩,
        ⟨6930, false, false, [], []⟩,
        ⟨6931, false, false, [], []⟩
      ]⟩,
    ⟨[79371, 9], [83165], .contexts [
        ⟨19434, true, false, [], [9]⟩,
        ⟨46, false, false, [83165], []⟩,
        ⟨19425, false, false, [], []⟩
      ]⟩,
    ⟨[15443, 82789], [15443, 82789], .contexts []⟩,
    ⟨[15443, 82789], [15443, 82789], .contexts []⟩,
    ⟨[83165, 11], [15443, 82789], .source 75102⟩,
    ⟨[15441], [15442], .contexts [
        ⟨16582, true, true, [], []⟩
      ]⟩,
    ⟨[83165, 15], [83165, 15], .contexts []⟩,
    ⟨[83165, 15], [82843], .contexts [
        ⟨19440, false, false, [], []⟩,
        ⟨19426, true, false, [], [15]⟩,
        ⟨184, false, false, [79377], []⟩,
        ⟨185, false, false, [79377], []⟩,
        ⟨15130, false, false, [], [5]⟩,
        ⟨15110, false, false, [], [5]⟩,
        ⟨15111, false, false, [], [5]⟩,
        ⟨15111, false, false, [], [5]⟩,
        ⟨17368, false, false, [], []⟩,
        ⟨17369, false, false, [], []⟩,
        ⟨17370, false, false, [], []⟩,
        ⟨17370, false, false, [], []⟩,
        ⟨17375, false, false, [], []⟩,
        ⟨672, true, false, [], [82843]⟩
      ]⟩,
    ⟨[83167], [83165, 7], .source 41648⟩,
    ⟨[83165, 7], [83167], .contexts [
        ⟨19442, true, false, [], []⟩
      ]⟩,
    ⟨[83167], [83167], .contexts []⟩,
    ⟨[83167], [83167], .contexts []⟩,
    ⟨[83165, 7], [83167], .contexts [
        ⟨19443, false, false, [], []⟩,
        ⟨19444, false, false, [], []⟩,
        ⟨19445, false, false, [], []⟩,
        ⟨19445, false, false, [], []⟩
      ]⟩,
    ⟨[2007, 83167], [2007, 83167], .contexts []⟩,
    ⟨[83167], [83167], .contexts []⟩,
    ⟨[83167, 1], [2007, 83167], .contexts [
        ⟨19446, true, false, [], [1]⟩,
        ⟨1027, false, false, [83165], []⟩,
        ⟨1028, false, false, [83165], []⟩,
        ⟨19429, false, false, [], [7]⟩,
        ⟨19431, false, false, [], [7]⟩,
        ⟨19427, false, false, [], [7]⟩,
        ⟨19428, false, false, [], [7]⟩,
        ⟨19428, false, false, [], [7]⟩,
        ⟨19443, false, false, [2007], []⟩,
        ⟨19447, false, false, [], []⟩,
        ⟨19448, false, false, [2007], []⟩,
        ⟨5405, true, false, [], [83167]⟩
      ]⟩,
    ⟨[15967], [8065, 9983], .source 8048⟩,
    ⟨[15969], [15967, 15451], .source 8049⟩,
    ⟨[83167, 5], [15969, 82783], .contexts [
        ⟨19446, true, false, [], [5]⟩,
        ⟨1043, false, false, [83165], []⟩,
        ⟨1046, false, false, [83165], []⟩,
        ⟨19423, false, false, [], [7, 5, 7]⟩,
        ⟨6816, false, false, [], [7, 5, 7]⟩,
        ⟨6817, false, false, [], [7, 5, 7]⟩,
        ⟨6817, false, false, [], [7, 5, 7]⟩,
        ⟨6827, false, false, [], [5, 7]⟩,
        ⟨11293, false, false, [], [5, 7]⟩,
        ⟨11292, false, false, [], [5, 7]⟩,
        ⟨11292, false, false, [], [5, 7]⟩,
        ⟨4037, false, false, [8065], [7]⟩,
        ⟨12286, false, false, [8065], [7]⟩,
        ⟨19450, true, false, [], [77427, 7]⟩,
        ⟨16606, false, false, [15967], []⟩,
        ⟨19451, true, false, [], [82783]⟩,
        ⟨16590, false, false, [15969], []⟩
      ]⟩,
    ⟨[83167, 5], [15969, 82783], .contexts [
        ⟨19452, false, false, [], []⟩,
        ⟨13, true, false, [], [15969, 82783]⟩
      ]⟩,
    ⟨[15971], [15968], .source 8050⟩,
    ⟨[82783, 5], [15971, 83167], .contexts [
        ⟨19453, true, false, [15968], [5]⟩,
        ⟨28, false, false, [15968, 83167], []⟩,
        ⟨19454, true, false, [], [83167]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 304. -/
def y322TCIndexRaw304 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83167, 9], [79369], .contexts [
        ⟨19446, true, false, [], [9]⟩,
        ⟨1534, false, false, [83165], []⟩,
        ⟨1535, false, false, [83165], []⟩,
        ⟨19433, false, false, [], [7]⟩,
        ⟨19434, false, false, [], [7]⟩,
        ⟨6798, false, false, [], [7]⟩,
        ⟨6799, false, false, [], [7]⟩,
        ⟨6799, false, false, [], [7]⟩,
        ⟨6796, false, false, [], []⟩,
        ⟨6785, false, false, [], []⟩,
        ⟨6786, false, false, [], []⟩,
        ⟨6786, false, false, [], []⟩,
        ⟨6913, false, false, [], []⟩,
        ⟨6914, false, false, [], []⟩
      ]⟩,
    ⟨[79369, 9], [83167], .contexts [
        ⟨19456, true, false, [], [9]⟩,
        ⟨46, false, false, [83167], []⟩,
        ⟨19445, false, false, [], []⟩
      ]⟩,
    ⟨[15443, 82787], [15443, 82787], .contexts []⟩,
    ⟨[83167, 11], [15443, 82787], .contexts [
        ⟨19446, true, false, [], [11]⟩,
        ⟨1051, false, false, [83165], []⟩,
        ⟨1052, false, false, [83165], []⟩,
        ⟨19438, false, false, [], [7]⟩,
        ⟨19436, false, false, [], [7]⟩,
        ⟨19437, false, false, [], [7]⟩,
        ⟨19437, false, false, [], [7]⟩,
        ⟨16647, false, false, [15443], []⟩,
        ⟨19458, false, false, [], []⟩,
        ⟨16644, false, false, [15443], []⟩,
        ⟨13, true, false, [], [15443, 82787]⟩
      ]⟩,
    ⟨[82787, 11], [15441, 83167], .contexts [
        ⟨19459, true, false, [15442], [11]⟩,
        ⟨53, false, false, [15442, 83167], []⟩,
        ⟨19439, true, false, [], [83167]⟩
      ]⟩,
    ⟨[83167, 15], [82845], .contexts [
        ⟨19446, true, false, [], [15]⟩,
        ⟨1063, false, false, [83165], []⟩,
        ⟨1064, false, false, [83165], []⟩,
        ⟨19440, false, false, [], [7]⟩,
        ⟨19441, false, false, [], [7]⟩,
        ⟨17369, false, false, [], [7]⟩,
        ⟨17370, false, false, [], [7]⟩,
        ⟨17370, false, false, [], [7]⟩,
        ⟨17386, false, false, [], []⟩,
        ⟨17387, false, false, [], []⟩,
        ⟨17388, false, false, [], []⟩,
        ⟨17388, false, false, [], []⟩,
        ⟨17393, false, false, [], []⟩,
        ⟨672, true, false, [], [82845]⟩
      ]⟩,
    ⟨[82845, 15], [83167], .contexts [
        ⟨19461, true, false, [], [15]⟩,
        ⟨1, false, false, [83167], []⟩,
        ⟨19445, false, false, [], []⟩
      ]⟩,
    ⟨[83169], [82783, 13], .source 41649⟩,
    ⟨[82783, 13], [83169], .contexts [
        ⟨19463, true, false, [], []⟩
      ]⟩,
    ⟨[83169, 13], [82783], .contexts [
        ⟨19464, true, false, [], [13]⟩,
        ⟨59, false, false, [82783], []⟩,
        ⟨16587, false, false, [], []⟩
      ]⟩,
    ⟨[83169], [83169], .contexts []⟩,
    ⟨[83169], [83169], .contexts []⟩,
    ⟨[82783, 13], [83169], .contexts [
        ⟨19464, false, false, [], []⟩,
        ⟨19466, false, false, [], []⟩,
        ⟨19467, false, false, [], []⟩,
        ⟨19467, false, false, [], []⟩
      ]⟩,
    ⟨[15445, 79017], [15445, 79017], .contexts []⟩,
    ⟨[15445, 79017], [15445, 79017], .contexts []⟩,
    ⟨[15445, 82827], [15445, 82827], .contexts []⟩,
    ⟨[83169, 3], [15445, 82827], .contexts [
        ⟨19468, true, false, [], [3]⟩,
        ⟨63, false, false, [82783], []⟩,
        ⟨65, false, false, [82783], []⟩,
        ⟨16596, false, false, [], [13]⟩,
        ⟨16598, false, false, [], [13]⟩,
        ⟨19469, false, false, [], [13]⟩,
        ⟨19470, false, false, [], [13]⟩,
        ⟨19470, false, false, [], [13]⟩,
        ⟨17151, false, false, [15445], []⟩,
        ⟨19471, false, false, [], []⟩,
        ⟨17160, false, false, [15445], []⟩,
        ⟨16597, true, false, [], [82827]⟩
      ]⟩,
    ⟨[15449, 77427], [15449, 77427], .contexts []⟩,
    ⟨[15449, 77427], [15449, 77427], .contexts []⟩,
    ⟨[15973], [15449, 3055], .source 8051⟩,
    ⟨[83169, 7], [15973, 77431], .contexts [
        ⟨19468, true, false, [], [7]⟩,
        ⟨73, false, false, [82783], []⟩,
        ⟨74, false, false, [82783], []⟩,
        ⟨16603, false, false, [], [13]⟩,
        ⟨16604, false, false, [], [13]⟩,
        ⟨19473, false, false, [], [13]⟩,
        ⟨19474, false, false, [], [13]⟩,
        ⟨19474, false, false, [], [13]⟩,
        ⟨6169, false, false, [15449], []⟩,
        ⟨19475, true, false, [], [77431]⟩,
        ⟨6168, false, false, [15973], []⟩,
        ⟨13, true, false, [], [15973, 77431]⟩
      ]⟩,
    ⟨[15975], [15972], .source 8052⟩,
    ⟨[77431, 7], [15975, 83169], .contexts [
        ⟨19476, true, false, [15972], [7]⟩,
        ⟨38, false, false, [15972, 83169], []⟩,
        ⟨19477, true, false, [], [83169]⟩
      ]⟩,
    ⟨[83169, 9], [82785], .contexts [
        ⟨19468, true, false, [], [9]⟩,
        ⟨77, false, false, [82783], []⟩,
        ⟨78, false, false, [82783], []⟩,
        ⟨16585, false, false, [], [13]⟩,
        ⟨6777, false, false, [], [13]⟩,
        ⟨6778, false, false, [], [13]⟩,
        ⟨6778, false, false, [], [13]⟩,
        ⟨16619, false, false, [], []⟩,
        ⟨16620, false, false, [], []⟩,
        ⟨16621, false, false, [], []⟩,
        ⟨16621, false, false, [], []⟩,
        ⟨17057, false, false, [], []⟩,
        ⟨17058, false, false, [], []⟩
      ]⟩,
    ⟨[82785, 9], [83169], .contexts [
        ⟨19479, true, false, [], [9]⟩,
        ⟨46, false, false, [83169], []⟩,
        ⟨19467, false, false, [], []⟩
      ]⟩,
    ⟨[15453, 79005], [15453, 79005], .contexts []⟩,
    ⟨[15453, 79005], [15453, 79005], .contexts []⟩,
    ⟨[15453, 82795], [15453, 82795], .contexts []⟩,
    ⟨[83169, 11], [15453, 82795], .contexts [
        ⟨19468, true, false, [], [11]⟩,
        ⟨82, false, false, [82783], []⟩,
        ⟨83, false, false, [82783], []⟩,
        ⟨16611, false, false, [], [13]⟩,
        ⟨16613, false, false, [], [13]⟩,
        ⟨19481, false, false, [], [13]⟩,
        ⟨19482, false, false, [], [13]⟩,
        ⟨19482, false, false, [], [13]⟩,
        ⟨16710, false, false, [15453], []⟩,
        ⟨19483, false, false, [], []⟩,
        ⟨16724, false, false, [15453], []⟩,
        ⟨16612, true, false, [], [82795]⟩
      ]⟩,
    ⟨[82795, 11], [15455, 83169], .contexts [
        ⟨19484, true, false, [15452], [11]⟩,
        ⟨53, false, false, [15452, 83169], []⟩,
        ⟨16614, true, false, [], [83169]⟩
      ]⟩,
    ⟨[15225, 82809], [15225, 82809], .contexts []⟩,
    ⟨[15225, 82809], [15225, 82809], .contexts []⟩,
    ⟨[15459, 83169], [15459, 83169], .contexts []⟩,
    ⟨[83169], [83169], .contexts []⟩,
    ⟨[83169, 15], [15459, 83169], .contexts [
        ⟨19468, true, false, [], [15]⟩,
        ⟨88, false, false, [82783], []⟩,
        ⟨91, false, false, [82783], []⟩,
        ⟨16904, false, false, [], [13, 15, 13]⟩,
        ⟨19486, false, false, [], [13, 15, 13]⟩,
        ⟨19487, false, false, [], [13, 15, 13]⟩,
        ⟨19487, false, false, [], [13, 15, 13]⟩,
        ⟨16901, false, false, [15225], [15, 13]⟩,
        ⟨16626, true, false, [], [82809, 15, 13]⟩,
        ⟨16903, false, false, [15457], [13]⟩,
        ⟨16627, true, false, [], [82783, 13]⟩,
        ⟨19464, false, false, [15459], []⟩,
        ⟨19488, false, false, [], []⟩,
        ⟨19489, false, false, [15459], []⟩
      ]⟩,
    ⟨[83169, 15], [15459, 83169], .contexts [
        ⟨19490, false, false, [], []⟩,
        ⟨16633, true, false, [], [83169]⟩
      ]⟩,
    ⟨[83171], [77435, 7], .source 41650⟩,
    ⟨[77435, 7], [83171], .contexts [
        ⟨19492, true, false, [], []⟩
      ]⟩,
    ⟨[83171, 7], [77435], .contexts [
        ⟨19493, true, false, [], [7]⟩,
        ⟨38, false, false, [77435], []⟩,
        ⟨1367, false, false, [], []⟩
      ]⟩,
    ⟨[83171], [83171], .contexts []⟩,
    ⟨[83171], [83171], .contexts []⟩,
    ⟨[77435, 7], [83171], .contexts [
        ⟨19493, false, false, [], []⟩,
        ⟨19495, false, false, [], []⟩,
        ⟨19496, false, false, [], []⟩,
        ⟨19496, false, false, [], []⟩
      ]⟩,
    ⟨[15977], [727, 15975], .source 8053⟩,
    ⟨[83171, 1], [83171, 1], .contexts []⟩,
    ⟨[83171, 1], [15977, 83169], .contexts [
        ⟨19499, false, false, [], []⟩,
        ⟨19497, true, false, [], [1]⟩,
        ⟨1027, false, false, [77435], []⟩,
        ⟨1028, false, false, [77435], []⟩,
        ⟨2082, false, false, [], [7]⟩,
        ⟨6167, false, false, [], [7]⟩,
        ⟨2080, false, false, [], [7]⟩,
        ⟨2080, false, false, [], [7]⟩,
        ⟨19478, false, false, [727], []⟩,
        ⟨19498, true, false, [], [83169]⟩,
        ⟨19489, false, false, [15977], []⟩,
        ⟨13, true, false, [], [15977, 83169]⟩
      ]⟩,
    ⟨[15979], [15976], .source 8054⟩,
    ⟨[83169, 1], [15979, 83171], .contexts [
        ⟨19500, true, false, [15976], [1]⟩,
        ⟨8, false, false, [15976, 83171], []⟩,
        ⟨19501, true, false, [], [83171]⟩
      ]⟩,
    ⟨[77437], [10729, 77435], .contexts [
        ⟨12722, false, false, [], []⟩
      ]⟩,
    ⟨[10729, 77435, 7], [10729, 83171], .contexts [
        ⟨19493, false, false, [10729], []⟩
      ]⟩,
    ⟨[10729, 83171], [10729, 83171], .contexts []⟩,
    ⟨[10729, 83171], [10729, 83171], .contexts []⟩,
    ⟨[10729, 83171], [10729, 83171], .contexts []⟩,
    ⟨[83171, 3], [83171, 3], .contexts []⟩,
    ⟨[83171], [83171], .contexts []⟩,
    ⟨[10729, 83171], [10729, 83171], .contexts [
        ⟨19509, false, false, [10729], []⟩
      ]⟩,
    ⟨[10729], [10729], .contexts [
        ⟨13, false, false, [], [10729]⟩
      ]⟩,
    ⟨[10729, 83171], [10729, 83171], .contexts [
        ⟨19511, true, false, [], [83171]⟩
      ]⟩,
    ⟨[83171, 3], [10729, 83171], .contexts [
        ⟨19508, false, false, [], []⟩,
        ⟨19497, true, false, [], [3]⟩,
        ⟨1034, false, false, [77435], []⟩,
        ⟨1035, false, false, [77435], []⟩,
        ⟨1366, false, false, [], [7]⟩,
        ⟨19503, false, false, [], [7]⟩,
        ⟨12721, false, false, [], [7]⟩,
        ⟨12721, false, false, [], [7]⟩,
        ⟨19504, false, false, [], []⟩,
        ⟨19505, false, false, [], []⟩,
        ⟨19506, false, false, [], []⟩,
        ⟨19507, false, false, [], []⟩,
        ⟨19510, false, false, [], []⟩,
        ⟨19512, false, false, [], []⟩
      ]⟩,
    ⟨[2959, 83171], [2959, 83171], .contexts []⟩,
    ⟨[2959, 83171], [2959, 83171], .contexts []⟩,
    ⟨[83171, 13], [83171, 13], .contexts []⟩,
    ⟨[2959], [2959], .contexts [
        ⟨13, false, false, [], [2959]⟩
      ]⟩,
    ⟨[83171, 13], [2959, 83171], .contexts [
        ⟨19516, false, false, [], []⟩,
        ⟨19497, true, false, [], [13]⟩,
        ⟨1056, false, false, [77435], []⟩,
        ⟨1057, false, false, [77435], []⟩,
        ⟨6099, false, false, [], [7]⟩,
        ⟨6102, false, false, [], [7]⟩,
        ⟨6165, false, false, [], [7]⟩,
        ⟨6166, false, false, [], [7]⟩,
        ⟨6166, false, false, [], [7]⟩,
        ⟨19493, false, false, [2959], []⟩,
        ⟨19514, false, false, [], []⟩,
        ⟨19515, false, false, [], []⟩,
        ⟨19509, false, false, [2959], []⟩,
        ⟨19517, true, false, [], [83171]⟩
      ]⟩,
    ⟨[727, 83171], [727, 83171], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 305. -/
def y322TCIndexRaw305 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[727, 83171], [727, 83171], .contexts []⟩,
    ⟨[83171, 15], [83171, 15], .contexts []⟩,
    ⟨[727], [727], .contexts [
        ⟨13, false, false, [], [727]⟩,
        ⟨2083, false, false, [], []⟩,
        ⟨2084, false, false, [], []⟩
      ]⟩,
    ⟨[83171, 15], [727, 83171], .contexts [
        ⟨19521, false, false, [], []⟩,
        ⟨19497, true, false, [], [15]⟩,
        ⟨1063, false, false, [77435], []⟩,
        ⟨1064, false, false, [77435], []⟩,
        ⟨2074, false, false, [], [7]⟩,
        ⟨2076, false, false, [], [7]⟩,
        ⟨2077, false, false, [], [7]⟩,
        ⟨2078, false, false, [], [7]⟩,
        ⟨2078, false, false, [], [7]⟩,
        ⟨19493, false, false, [727], []⟩,
        ⟨19519, false, false, [], []⟩,
        ⟨19520, false, false, [], []⟩,
        ⟨19509, false, false, [727], []⟩,
        ⟨19522, true, false, [], [83171]⟩
      ]⟩,
    ⟨[83173], [77441, 7], .source 75103⟩,
    ⟨[77441, 7], [83173], .contexts [
        ⟨19524, true, false, [], []⟩
      ]⟩,
    ⟨[83173, 7], [77441], .contexts [
        ⟨19525, true, false, [], [7]⟩,
        ⟨38, false, false, [77441], []⟩,
        ⟨1374, false, false, [], []⟩
      ]⟩,
    ⟨[77441, 7], [83173], .source 75104⟩,
    ⟨[83173], [83173], .source 75105⟩,
    ⟨[83173], [83173], .source 75106⟩,
    ⟨[77441, 7], [83173], .contexts [
        ⟨19527, false, false, [], []⟩,
        ⟨19528, false, false, [], []⟩,
        ⟨19529, false, false, [], []⟩,
        ⟨19529, false, false, [], []⟩
      ]⟩,
    ⟨[15981], [2665, 7685], .source 8055⟩,
    ⟨[15983], [15981, 15559], .source 8056⟩,
    ⟨[83173, 3], [15983, 82819], .contexts [
        ⟨19530, true, false, [], [3]⟩,
        ⟨1034, false, false, [77441], []⟩,
        ⟨1035, false, false, [77441], []⟩,
        ⟨5952, false, false, [], [7]⟩,
        ⟨11155, false, false, [2665], [7]⟩,
        ⟨19531, true, false, [], [77517, 7]⟩,
        ⟨17053, false, false, [15981], []⟩,
        ⟨19532, true, false, [], [82819]⟩,
        ⟨17066, false, false, [15983], []⟩,
        ⟨13, true, false, [], [15983, 82819]⟩
      ]⟩,
    ⟨[15985], [15982], .source 8057⟩,
    ⟨[82819, 3], [15985, 83173], .contexts [
        ⟨19533, true, false, [15982], [3]⟩,
        ⟨20, false, false, [15982, 83173], []⟩,
        ⟨19534, true, false, [], [83173]⟩
      ]⟩,
    ⟨[7675, 79379], [7675, 79379], .contexts []⟩,
    ⟨[7675, 79379], [7675, 79379], .contexts []⟩,
    ⟨[83173, 9], [7675, 79379], .contexts [
        ⟨19530, true, false, [], [9]⟩,
        ⟨1534, false, false, [77441], []⟩,
        ⟨1535, false, false, [77441], []⟩,
        ⟨1373, false, false, [], [7]⟩,
        ⟨1416, false, false, [], [7]⟩,
        ⟨1377, false, false, [], [7]⟩,
        ⟨1377, false, false, [], [7]⟩,
        ⟨11144, false, false, [], []⟩,
        ⟨19536, false, false, [], []⟩,
        ⟨19537, false, false, [], []⟩,
        ⟨19537, false, false, [], []⟩,
        ⟨6840, false, false, [7675], []⟩,
        ⟨13, true, false, [], [7675, 79379]⟩
      ]⟩,
    ⟨[79379, 9], [7673, 83173], .contexts [
        ⟨19538, true, false, [7674], [9]⟩,
        ⟨46, false, false, [7674, 83173], []⟩,
        ⟨11142, true, false, [], [83173]⟩
      ]⟩,
    ⟨[15987], [11283, 2923], .source 75107⟩,
    ⟨[15987, 82791], [15987, 82791], .source 75108⟩,
    ⟨[15987, 82791], [15987, 82791], .source 75109⟩,
    ⟨[83173, 11], [15987, 82791], .contexts [
        ⟨19530, true, false, [], [11]⟩,
        ⟨1051, false, false, [77441], []⟩,
        ⟨1052, false, false, [77441], []⟩,
        ⟨6555, false, false, [], [7]⟩,
        ⟨11380, false, false, [3251], [7]⟩,
        ⟨12902, true, false, [], [77627, 7]⟩,
        ⟨16674, false, false, [11283], []⟩,
        ⟨19540, true, false, [], [82791]⟩,
        ⟨19541, false, false, [], []⟩,
        ⟨19542, false, false, [], []⟩
      ]⟩,
    ⟨[15989], [15986], .source 8059⟩,
    ⟨[15991], [14063, 8067], .source 8060⟩,
    ⟨[83173, 13], [83173, 13], .contexts []⟩,
    ⟨[15991], [15991], .contexts [
        ⟨13, false, false, [], [15991]⟩
      ]⟩,
    ⟨[83173, 13], [15991, 79377], .contexts [
        ⟨19546, false, false, [], []⟩,
        ⟨19530, true, false, [], [13]⟩,
        ⟨1056, false, false, [77441], []⟩,
        ⟨1057, false, false, [77441], []⟩,
        ⟨14271, false, false, [], [7]⟩,
        ⟨11297, false, false, [14063], []⟩,
        ⟨19545, true, false, [], [79377]⟩,
        ⟨6823, false, false, [15991], []⟩,
        ⟨19547, true, false, [], [79377]⟩
      ]⟩,
    ⟨[15993], [15990], .source 8061⟩,
    ⟨[79377, 13], [15993, 83173], .contexts [
        ⟨19548, true, false, [15990], [13]⟩,
        ⟨59, false, false, [15990, 83173], []⟩,
        ⟨19549, true, false, [], [83173]⟩
      ]⟩,
    ⟨[729, 83173], [729, 83173], .contexts []⟩,
    ⟨[729, 83173], [729, 83173], .contexts []⟩,
    ⟨[83173, 15], [83173, 15], .contexts []⟩,
    ⟨[83173], [83173], .contexts []⟩,
    ⟨[729], [729], .contexts [
        ⟨13, false, false, [], [729]⟩
      ]⟩,
    ⟨[83173, 15], [729, 83173], .contexts [
        ⟨19553, false, false, [], []⟩,
        ⟨19530, true, false, [], [15]⟩,
        ⟨1063, false, false, [77441], []⟩,
        ⟨1064, false, false, [77441], []⟩,
        ⟨2061, false, false, [], [7]⟩,
        ⟨19525, false, false, [729], []⟩,
        ⟨19551, false, false, [], []⟩,
        ⟨19552, false, false, [], []⟩,
        ⟨19554, false, false, [729], []⟩,
        ⟨19555, true, false, [], [83173]⟩
      ]⟩,
    ⟨[83175], [83173, 5], .source 41652⟩,
    ⟨[83173, 5], [83175], .contexts [
        ⟨19557, true, false, [], []⟩
      ]⟩,
    ⟨[83175, 5], [83173], .contexts [
        ⟨19558, true, false, [], [5]⟩,
        ⟨28, false, false, [83173], []⟩,
        ⟨19529, false, false, [], []⟩
      ]⟩,
    ⟨[83173, 5], [83175], .contexts [
        ⟨19558, false, false, [], []⟩
      ]⟩,
    ⟨[83175], [83175], .contexts []⟩,
    ⟨[83175], [83175], .contexts []⟩,
    ⟨[83173, 5], [83175], .contexts [
        ⟨19560, false, false, [], []⟩,
        ⟨19561, false, false, [], []⟩,
        ⟨19562, false, false, [], []⟩,
        ⟨19562, false, false, [], []⟩
      ]⟩,
    ⟨[15991, 79377], [15991, 79377], .contexts []⟩,
    ⟨[15991, 79377], [15991, 79377], .contexts []⟩,
    ⟨[15991, 83165], [15991, 83165], .contexts []⟩,
    ⟨[15991, 83165], [15991, 83165], .contexts []⟩,
    ⟨[83175, 13], [83175, 13], .contexts []⟩,
    ⟨[83175, 13], [15991, 83165], .contexts [
        ⟨19568, false, false, [], []⟩,
        ⟨19563, true, false, [], [13]⟩,
        ⟨179, false, false, [83173], []⟩,
        ⟨180, false, false, [83173], []⟩,
        ⟨19546, false, false, [], [5]⟩,
        ⟨19548, false, false, [], [5]⟩,
        ⟨19564, false, false, [], [5]⟩,
        ⟨19565, false, false, [], [5]⟩,
        ⟨19565, false, false, [], [5]⟩,
        ⟨19422, false, false, [15991], []⟩,
        ⟨19566, false, false, [], []⟩,
        ⟨19567, false, false, [], []⟩,
        ⟨19430, false, false, [15991], []⟩,
        ⟨19547, true, false, [], [83165]⟩
      ]⟩,
    ⟨[729, 83175], [729, 83175], .contexts []⟩,
    ⟨[729, 83175], [729, 83175], .contexts []⟩,
    ⟨[83175, 15], [83175, 15], .contexts []⟩,
    ⟨[83175], [83175], .contexts []⟩,
    ⟨[83175, 15], [729, 83175], .contexts [
        ⟨19572, false, false, [], []⟩,
        ⟨19563, true, false, [], [15]⟩,
        ⟨184, false, false, [83173], []⟩,
        ⟨185, false, false, [83173], []⟩,
        ⟨19553, false, false, [], [5]⟩,
        ⟨19556, false, false, [], [5]⟩,
        ⟨19551, false, false, [], [5]⟩,
        ⟨19552, false, false, [], [5]⟩,
        ⟨19552, false, false, [], [5]⟩,
        ⟨19558, false, false, [729], []⟩,
        ⟨19570, false, false, [], []⟩,
        ⟨19571, false, false, [], []⟩,
        ⟨19573, false, false, [729], []⟩,
        ⟨19555, true, false, [], [83175]⟩
      ]⟩,
    ⟨[83177], [83175, 7], .source 41653⟩,
    ⟨[83175, 7], [83177], .contexts [
        ⟨19575, true, false, [], []⟩
      ]⟩,
    ⟨[83177, 7], [83175], .contexts [
        ⟨19576, true, false, [], [7]⟩,
        ⟨38, false, false, [83175], []⟩,
        ⟨19562, false, false, [], []⟩
      ]⟩,
    ⟨[83175, 7], [83177], .contexts [
        ⟨19576, false, false, [], []⟩
      ]⟩,
    ⟨[83177], [83177], .contexts []⟩,
    ⟨[83177], [83177], .contexts []⟩,
    ⟨[83175, 7], [83177], .contexts [
        ⟨19578, false, false, [], []⟩,
        ⟨19579, false, false, [], []⟩,
        ⟨19580, false, false, [], []⟩,
        ⟨19580, false, false, [], []⟩
      ]⟩,
    ⟨[15995], [13479, 15975], .source 8062⟩,
    ⟨[83177, 5], [15995, 83169], .contexts [
        ⟨19581, true, false, [], [5]⟩,
        ⟨1043, false, false, [83175], []⟩,
        ⟨1046, false, false, [83175], []⟩,
        ⟨19559, false, false, [], [7, 5, 7]⟩,
        ⟨19528, false, false, [], [7, 5, 7]⟩,
        ⟨19529, false, false, [], [7, 5, 7]⟩,
        ⟨19529, false, false, [], [7, 5, 7]⟩,
        ⟨19526, false, false, [], [5, 7]⟩,
        ⟨1417, false, false, [], [5, 7]⟩,
        ⟨1374, false, false, [], [5, 7]⟩,
        ⟨1374, false, false, [], [5, 7]⟩,
        ⟨11151, false, false, [], [7]⟩,
        ⟨12297, false, false, [7679], [7]⟩,
        ⟨14066, true, false, [], [77431, 7]⟩,
        ⟨19478, false, false, [13479], []⟩,
        ⟨19582, true, false, [], [83169]⟩,
        ⟨19489, false, false, [15995], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 306. -/
def y322TCIndexRaw306 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83177, 5], [15995, 83169], .contexts [
        ⟨19583, false, false, [], []⟩,
        ⟨13, true, false, [], [15995, 83169]⟩
      ]⟩,
    ⟨[15997], [15994], .source 8063⟩,
    ⟨[83169, 5], [15997, 83177], .contexts [
        ⟨19584, true, false, [15994], [5]⟩,
        ⟨28, false, false, [15994, 83177], []⟩,
        ⟨19585, true, false, [], [83177]⟩
      ]⟩,
    ⟨[15991, 83167], [15991, 83167], .contexts []⟩,
    ⟨[83177, 13], [15991, 83167], .contexts [
        ⟨19581, true, false, [], [13]⟩,
        ⟨1056, false, false, [83175], []⟩,
        ⟨1057, false, false, [83175], []⟩,
        ⟨19568, false, false, [], [7]⟩,
        ⟨19569, false, false, [], [7]⟩,
        ⟨19566, false, false, [], [7]⟩,
        ⟨19567, false, false, [], [7]⟩,
        ⟨19567, false, false, [], [7]⟩,
        ⟨19443, false, false, [15991], []⟩,
        ⟨19587, false, false, [], []⟩,
        ⟨19448, false, false, [15991], []⟩,
        ⟨19547, true, false, [], [83167]⟩
      ]⟩,
    ⟨[83167, 13], [15993, 83177], .contexts [
        ⟨19588, true, false, [15990], [13]⟩,
        ⟨59, false, false, [15990, 83177], []⟩,
        ⟨19549, true, false, [], [83177]⟩
      ]⟩,
    ⟨[729, 83177], [729, 83177], .contexts []⟩,
    ⟨[83177], [83177], .contexts []⟩,
    ⟨[83177, 15], [729, 83177], .contexts [
        ⟨19581, true, false, [], [15]⟩,
        ⟨1063, false, false, [83175], []⟩,
        ⟨1064, false, false, [83175], []⟩,
        ⟨19572, false, false, [], [7]⟩,
        ⟨19574, false, false, [], [7]⟩,
        ⟨19570, false, false, [], [7]⟩,
        ⟨19571, false, false, [], [7]⟩,
        ⟨19571, false, false, [], [7]⟩,
        ⟨19576, false, false, [729], []⟩,
        ⟨19590, false, false, [], []⟩,
        ⟨19591, false, false, [729], []⟩,
        ⟨19555, true, false, [], [83177]⟩
      ]⟩,
    ⟨[77439, 7], [83179], .source 75111⟩,
    ⟨[83179, 7], [77439], .contexts [
        ⟨19593, true, false, [], [7]⟩,
        ⟨38, false, false, [77439], []⟩,
        ⟨1371, false, false, [], []⟩
      ]⟩,
    ⟨[83179], [83179], .contexts []⟩,
    ⟨[83179], [83179], .source 75112⟩,
    ⟨[77439, 7], [83179], .contexts [
        ⟨19593, false, false, [], []⟩,
        ⟨19595, false, false, [], []⟩,
        ⟨19596, false, false, [], []⟩,
        ⟨19596, false, false, [], []⟩
      ]⟩,
    ⟨[83179, 1], [83179, 1], .source 75113⟩,
    ⟨[83179, 1], [83173], .contexts [
        ⟨19598, false, false, [], []⟩,
        ⟨19597, true, false, [], [1]⟩,
        ⟨1027, false, false, [77439], []⟩,
        ⟨1028, false, false, [77439], []⟩,
        ⟨1370, false, false, [], [7]⟩,
        ⟨1417, false, false, [], [7]⟩,
        ⟨1374, false, false, [], [7]⟩,
        ⟨1374, false, false, [], [7]⟩,
        ⟨19527, false, false, [], []⟩,
        ⟨19528, false, false, [], []⟩,
        ⟨19529, false, false, [], []⟩,
        ⟨19529, false, false, [], []⟩,
        ⟨19554, false, false, [], []⟩,
        ⟨672, true, false, [], [83173]⟩
      ]⟩,
    ⟨[83173, 1], [83179], .contexts [
        ⟨19599, true, false, [], [1]⟩,
        ⟨8, false, false, [83179], []⟩,
        ⟨19596, false, false, [], []⟩
      ]⟩,
    ⟨[2797, 77439], [2797, 77439], .contexts []⟩,
    ⟨[2797, 77439], [2797, 77439], .contexts []⟩,
    ⟨[2797, 83179], [2797, 83179], .contexts []⟩,
    ⟨[2797, 83179], [2797, 83179], .contexts []⟩,
    ⟨[83179, 13], [83179, 13], .contexts []⟩,
    ⟨[83179], [83179], .contexts []⟩,
    ⟨[2797], [2797], .contexts [
        ⟨13, false, false, [], [2797]⟩
      ]⟩,
    ⟨[83179, 13], [2797, 83179], .contexts [
        ⟨19605, false, false, [], []⟩,
        ⟨19597, true, false, [], [13]⟩,
        ⟨1056, false, false, [77439], []⟩,
        ⟨1057, false, false, [77439], []⟩,
        ⟨5961, false, false, [], [7]⟩,
        ⟨5964, false, false, [], [7]⟩,
        ⟨19601, false, false, [], [7]⟩,
        ⟨19602, false, false, [], [7]⟩,
        ⟨19602, false, false, [], [7]⟩,
        ⟨19593, false, false, [2797], []⟩,
        ⟨19603, false, false, [], []⟩,
        ⟨19604, false, false, [], []⟩,
        ⟨19606, false, false, [2797], []⟩,
        ⟨19607, true, false, [], [83179]⟩
      ]⟩,
    ⟨[727, 83179], [727, 83179], .contexts []⟩,
    ⟨[727, 83179], [727, 83179], .contexts []⟩,
    ⟨[83179, 15], [83179, 15], .contexts []⟩,
    ⟨[83179, 15], [727, 83179], .contexts [
        ⟨19611, false, false, [], []⟩,
        ⟨19597, true, false, [], [15]⟩,
        ⟨1063, false, false, [77439], []⟩,
        ⟨1064, false, false, [77439], []⟩,
        ⟨2063, false, false, [], [7]⟩,
        ⟨2065, false, false, [], [7]⟩,
        ⟨2070, false, false, [], [7]⟩,
        ⟨2071, false, false, [], [7]⟩,
        ⟨2071, false, false, [], [7]⟩,
        ⟨19593, false, false, [727], []⟩,
        ⟨19609, false, false, [], []⟩,
        ⟨19610, false, false, [], []⟩,
        ⟨19606, false, false, [727], []⟩,
        ⟨19522, true, false, [], [83179]⟩
      ]⟩,
    ⟨[83181], [83179, 5], .source 41655⟩,
    ⟨[83179, 5], [83181], .contexts [
        ⟨19613, true, false, [], []⟩
      ]⟩,
    ⟨[83181, 5], [83179], .contexts [
        ⟨19614, true, false, [], [5]⟩,
        ⟨28, false, false, [83179], []⟩,
        ⟨19596, false, false, [], []⟩
      ]⟩,
    ⟨[83179, 5], [83181], .contexts [
        ⟨19614, false, false, [], []⟩
      ]⟩,
    ⟨[83181], [83181], .contexts []⟩,
    ⟨[83181], [83181], .contexts []⟩,
    ⟨[83179, 5], [83181], .contexts [
        ⟨19616, false, false, [], []⟩,
        ⟨19617, false, false, [], []⟩,
        ⟨19618, false, false, [], []⟩,
        ⟨19618, false, false, [], []⟩
      ]⟩,
    ⟨[83181, 1], [83181, 1], .contexts []⟩,
    ⟨[83181, 1], [83175], .contexts [
        ⟨19620, false, false, [], []⟩,
        ⟨19619, true, false, [], [1]⟩,
        ⟨161, false, false, [83179], []⟩,
        ⟨162, false, false, [83179], []⟩,
        ⟨19598, false, false, [], [5]⟩,
        ⟨19599, false, false, [], [5]⟩,
        ⟨19528, false, false, [], [5]⟩,
        ⟨19529, false, false, [], [5]⟩,
        ⟨19529, false, false, [], [5]⟩,
        ⟨19560, false, false, [], []⟩,
        ⟨19561, false, false, [], []⟩,
        ⟨19562, false, false, [], []⟩,
        ⟨19562, false, false, [], []⟩,
        ⟨19573, false, false, [], []⟩,
        ⟨672, true, false, [], [83175]⟩
      ]⟩,
    ⟨[83175, 1], [83181], .contexts [
        ⟨19621, true, false, [], [1]⟩,
        ⟨8, false, false, [83181], []⟩,
        ⟨19618, false, false, [], []⟩
      ]⟩,
    ⟨[83179, 13], [2797, 83179], .contexts [
        ⟨19605, false, false, [], []⟩,
        ⟨19608, false, false, [], []⟩,
        ⟨19603, false, false, [], []⟩,
        ⟨19604, false, false, [], []⟩,
        ⟨19604, false, false, [], []⟩
      ]⟩,
    ⟨[2797, 83181], [2797, 83181], .contexts []⟩,
    ⟨[2797, 83181], [2797, 83181], .contexts []⟩,
    ⟨[83181, 13], [83181, 13], .contexts []⟩,
    ⟨[83181], [83181], .contexts []⟩,
    ⟨[83181, 13], [2797, 83181], .contexts [
        ⟨19626, false, false, [], []⟩,
        ⟨19619, true, false, [], [13]⟩,
        ⟨179, false, false, [83179], []⟩,
        ⟨180, false, false, [83179], []⟩,
        ⟨19623, false, false, [], [5]⟩,
        ⟨19614, false, false, [2797], []⟩,
        ⟨19624, false, false, [], []⟩,
        ⟨19625, false, false, [], []⟩,
        ⟨19627, false, false, [2797], []⟩,
        ⟨19607, true, false, [], [83181]⟩
      ]⟩,
    ⟨[83179, 15], [727, 83179], .contexts [
        ⟨19611, false, false, [], []⟩,
        ⟨19612, false, false, [], []⟩,
        ⟨19609, false, false, [], []⟩,
        ⟨19610, false, false, [], []⟩,
        ⟨19610, false, false, [], []⟩
      ]⟩,
    ⟨[727, 83181], [727, 83181], .contexts []⟩,
    ⟨[727, 83181], [727, 83181], .contexts []⟩,
    ⟨[83181, 15], [83181, 15], .contexts []⟩,
    ⟨[83181, 15], [727, 83181], .contexts [
        ⟨19632, false, false, [], []⟩,
        ⟨19619, true, false, [], [15]⟩,
        ⟨184, false, false, [83179], []⟩,
        ⟨185, false, false, [83179], []⟩,
        ⟨19629, false, false, [], [5]⟩,
        ⟨19614, false, false, [727], []⟩,
        ⟨19630, false, false, [], []⟩,
        ⟨19631, false, false, [], []⟩,
        ⟨19627, false, false, [727], []⟩,
        ⟨19522, true, false, [], [83181]⟩
      ]⟩,
    ⟨[83183], [83181, 7], .source 41656⟩,
    ⟨[83181, 7], [83183], .contexts [
        ⟨19634, true, false, [], []⟩
      ]⟩,
    ⟨[83183, 7], [83181], .contexts [
        ⟨19635, true, false, [], [7]⟩,
        ⟨38, false, false, [83181], []⟩,
        ⟨19618, false, false, [], []⟩
      ]⟩,
    ⟨[83181, 7], [83183], .contexts [
        ⟨19635, false, false, [], []⟩
      ]⟩,
    ⟨[83183], [83183], .contexts []⟩,
    ⟨[83183], [83183], .contexts []⟩,
    ⟨[83181, 7], [83183], .contexts [
        ⟨19637, false, false, [], []⟩,
        ⟨19638, false, false, [], []⟩,
        ⟨19639, false, false, [], []⟩,
        ⟨19639, false, false, [], []⟩
      ]⟩,
    ⟨[83183, 1], [83177], .contexts [
        ⟨19640, true, false, [], [1]⟩,
        ⟨1027, false, false, [83181], []⟩,
        ⟨1028, false, false, [83181], []⟩,
        ⟨19620, false, false, [], [7]⟩,
        ⟨19621, false, false, [], [7]⟩,
        ⟨19561, false, false, [], [7]⟩,
        ⟨19562, false, false, [], [7]⟩,
        ⟨19562, false, false, [], [7]⟩,
        ⟨19578, false, false, [], []⟩,
        ⟨19579, false, false, [], []⟩,
        ⟨19580, false, false, [], []⟩,
        ⟨19580, false, false, [], []⟩,
        ⟨19591, false, false, [], []⟩,
        ⟨672, true, false, [], [83177]⟩
      ]⟩,
    ⟨[83177, 1], [83183], .contexts [
        ⟨19641, true, false, [], [1]⟩,
        ⟨8, false, false, [83183], []⟩,
        ⟨19639, false, false, [], []⟩
      ]⟩,
    ⟨[83179, 7], [77439], .contexts [
        ⟨19594, false, false, [], []⟩
      ]⟩,
    ⟨[83183, 5], [83183, 5], .contexts []⟩,
    ⟨[83183, 5], [10729, 83171], .contexts [
        ⟨19644, false, false, [], []⟩,
        ⟨19640, true, false, [], [5]⟩,
        ⟨1043, false, false, [83181], []⟩,
        ⟨1046, false, false, [83181], []⟩,
        ⟨19615, false, false, [], [7, 5, 7]⟩,
        ⟨19595, false, false, [], [7, 5, 7]⟩,
        ⟨19596, false, false, [], [7, 5, 7]⟩,
        ⟨19596, false, false, [], [7, 5, 7]⟩,
        ⟨19643, false, false, [], [5, 7]⟩,
        ⟨1419, false, false, [], [5, 7]⟩,
        ⟨1371, false, false, [], [5, 7]⟩,
        ⟨1371, false, false, [], [5, 7]⟩,
        ⟨1420, false, false, [], [7]⟩,
        ⟨19503, false, false, [], [7]⟩,
        ⟨12721, false, false, [], [7]⟩,
        ⟨12721, false, false, [], [7]⟩,
        ⟨19504, false, false, [], []⟩,
        ⟨19505, false, false, [], []⟩,
        ⟨19506, false, false, [], []⟩,
        ⟨19507, false, false, [], []⟩,
        ⟨19510, false, false, [], []⟩
      ]⟩,
    ⟨[83183, 5], [10729, 83171], .contexts [
        ⟨19645, false, false, [], []⟩,
        ⟨19512, false, false, [], []⟩
      ]⟩,
    ⟨[15999], [10728], .source 8064⟩]

/-- Exact literal claimed equations and contextual derivations, block 307. -/
def y322TCIndexRaw307 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83171, 5], [15999, 83183], .contexts [
        ⟨19646, true, false, [10728], [5]⟩,
        ⟨28, false, false, [10728, 83183], []⟩,
        ⟨19647, true, false, [], [83183]⟩
      ]⟩,
    ⟨[2797, 83183], [2797, 83183], .contexts []⟩,
    ⟨[2797, 83183], [2797, 83183], .contexts []⟩,
    ⟨[83183, 13], [83183, 13], .contexts []⟩,
    ⟨[83183], [83183], .contexts []⟩,
    ⟨[83183, 13], [2797, 83183], .contexts [
        ⟨19651, false, false, [], []⟩,
        ⟨19640, true, false, [], [13]⟩,
        ⟨1056, false, false, [83181], []⟩,
        ⟨1057, false, false, [83181], []⟩,
        ⟨19626, false, false, [], [7]⟩,
        ⟨19628, false, false, [], [7]⟩,
        ⟨19624, false, false, [], [7]⟩,
        ⟨19625, false, false, [], [7]⟩,
        ⟨19625, false, false, [], [7]⟩,
        ⟨19635, false, false, [2797], []⟩,
        ⟨19649, false, false, [], []⟩,
        ⟨19650, false, false, [], []⟩,
        ⟨19652, false, false, [2797], []⟩,
        ⟨19607, true, false, [], [83183]⟩
      ]⟩,
    ⟨[727, 83183], [727, 83183], .contexts []⟩,
    ⟨[727, 83183], [727, 83183], .contexts []⟩,
    ⟨[83183, 15], [83183, 15], .contexts []⟩,
    ⟨[83183, 15], [727, 83183], .contexts [
        ⟨19656, false, false, [], []⟩,
        ⟨19640, true, false, [], [15]⟩,
        ⟨1063, false, false, [83181], []⟩,
        ⟨1064, false, false, [83181], []⟩,
        ⟨19632, false, false, [], [7]⟩,
        ⟨19633, false, false, [], [7]⟩,
        ⟨19630, false, false, [], [7]⟩,
        ⟨19631, false, false, [], [7]⟩,
        ⟨19631, false, false, [], [7]⟩,
        ⟨19635, false, false, [727], []⟩,
        ⟨19654, false, false, [], []⟩,
        ⟨19655, false, false, [], []⟩,
        ⟨19652, false, false, [727], []⟩,
        ⟨19522, true, false, [], [83183]⟩
      ]⟩,
    ⟨[83185], [83171, 9], .source 41657⟩,
    ⟨[83171, 9], [83185], .contexts [
        ⟨19658, true, false, [], []⟩
      ]⟩,
    ⟨[83185, 9], [83171], .contexts [
        ⟨19659, true, false, [], [9]⟩,
        ⟨46, false, false, [83171], []⟩,
        ⟨19496, false, false, [], []⟩
      ]⟩,
    ⟨[83185], [83185], .contexts []⟩,
    ⟨[83185], [83185], .contexts []⟩,
    ⟨[83171, 9], [83185], .contexts [
        ⟨19659, false, false, [], []⟩,
        ⟨19661, false, false, [], []⟩,
        ⟨19662, false, false, [], []⟩,
        ⟨19662, false, false, [], []⟩
      ]⟩,
    ⟨[83171, 3], [10729, 83171], .contexts [
        ⟨19508, false, false, [], []⟩,
        ⟨19513, false, false, [], []⟩,
        ⟨19505, false, false, [], []⟩,
        ⟨19507, false, false, [], []⟩,
        ⟨19507, false, false, [], []⟩
      ]⟩,
    ⟨[10729, 83185], [10729, 83185], .contexts []⟩,
    ⟨[83185], [83185], .contexts []⟩,
    ⟨[83185, 3], [10729, 83185], .contexts [
        ⟨19663, true, false, [], [3]⟩,
        ⟨196, false, false, [83171], []⟩,
        ⟨197, false, false, [83171], []⟩,
        ⟨19664, false, false, [], [9]⟩,
        ⟨19659, false, false, [10729], []⟩,
        ⟨19665, false, false, [], []⟩,
        ⟨19666, false, false, [10729], []⟩,
        ⟨19511, true, false, [], [83185]⟩
      ]⟩,
    ⟨[83171, 7], [77435], .contexts [
        ⟨19494, false, false, [], []⟩,
        ⟨1421, false, false, [], []⟩,
        ⟨1367, false, false, [], []⟩,
        ⟨1367, false, false, [], []⟩
      ]⟩,
    ⟨[13489, 77885], [13489, 77885], .contexts []⟩,
    ⟨[83185, 7], [83185, 7], .contexts []⟩,
    ⟨[83185, 7], [13489, 77885], .contexts [
        ⟨19670, false, false, [], []⟩,
        ⟨19663, true, false, [], [7]⟩,
        ⟨1084, false, false, [83171], []⟩,
        ⟨1085, false, false, [83171], []⟩,
        ⟨19668, false, false, [], [9]⟩,
        ⟨6071, false, false, [], []⟩,
        ⟨12719, false, false, [2883], []⟩,
        ⟨14072, true, false, [], [77885]⟩,
        ⟨19669, false, false, [], []⟩,
        ⟨6033, false, false, [13489], []⟩,
        ⟨13, true, false, [], [13489, 77885]⟩
      ]⟩,
    ⟨[16001], [13488], .source 8065⟩,
    ⟨[77885, 7], [16001, 83185], .contexts [
        ⟨19671, true, false, [13488], [7]⟩,
        ⟨38, false, false, [13488, 83185], []⟩,
        ⟨19672, true, false, [], [83185]⟩
      ]⟩,
    ⟨[83171, 13], [2959, 83171], .contexts [
        ⟨19516, false, false, [], []⟩,
        ⟨19518, false, false, [], []⟩,
        ⟨19514, false, false, [], []⟩,
        ⟨19515, false, false, [], []⟩,
        ⟨19515, false, false, [], []⟩
      ]⟩,
    ⟨[2959, 83185], [2959, 83185], .contexts []⟩,
    ⟨[83171, 15], [727, 83171], .contexts [
        ⟨19521, false, false, [], []⟩,
        ⟨19523, false, false, [], []⟩,
        ⟨19519, false, false, [], []⟩,
        ⟨19520, false, false, [], []⟩,
        ⟨19520, false, false, [], []⟩
      ]⟩,
    ⟨[727, 83185], [727, 83185], .contexts []⟩,
    ⟨[13489, 77885], [13489, 77885], .contexts []⟩,
    ⟨[16003], [13489, 2891], .source 8066⟩,
    ⟨[16005], [16003, 16001], .source 8067⟩,
    ⟨[16007], [16004], .source 8068⟩,
    ⟨[16004], [16004], .contexts []⟩,
    ⟨[83185, 11], [16007, 83185], .contexts [
        ⟨19680, false, false, [16004], [83185, 11]⟩,
        ⟨19673, true, false, [16004, 16003], [11]⟩,
        ⟨19679, false, false, [16004], [77885, 7, 11]⟩,
        ⟨6044, true, false, [16004, 13489], [7, 11]⟩,
        ⟨19669, true, false, [16004], [11, 7, 11]⟩,
        ⟨19669, true, false, [16004], [11, 7, 11]⟩,
        ⟨19678, true, false, [16004], [11, 7, 11]⟩,
        ⟨19671, true, false, [16004], [11, 7, 11]⟩,
        ⟨19670, true, false, [16004], [11, 7, 11]⟩,
        ⟨2806, false, false, [16004, 83185], []⟩,
        ⟨19666, false, false, [16004], []⟩,
        ⟨19682, true, false, [], [83185]⟩,
        ⟨19682, true, false, [], [83185]⟩,
        ⟨19681, true, false, [], [83185]⟩
      ]⟩,
    ⟨[83187], [83171, 11], .source 41658⟩,
    ⟨[83171, 11], [83187], .contexts [
        ⟨19684, true, false, [], []⟩
      ]⟩,
    ⟨[83187, 11], [83171], .contexts [
        ⟨19685, true, false, [], [11]⟩,
        ⟨53, false, false, [83171], []⟩,
        ⟨19496, false, false, [], []⟩
      ]⟩,
    ⟨[83187], [83187], .contexts []⟩,
    ⟨[83187], [83187], .contexts []⟩,
    ⟨[83171, 11], [83187], .contexts [
        ⟨19685, false, false, [], []⟩,
        ⟨19687, false, false, [], []⟩,
        ⟨19688, false, false, [], []⟩,
        ⟨19688, false, false, [], []⟩
      ]⟩,
    ⟨[15977, 83169], [15977, 83169], .contexts []⟩,
    ⟨[15977, 83169], [15977, 83169], .contexts []⟩,
    ⟨[16009], [15977, 15453], .source 8069⟩,
    ⟨[83187, 1], [16009, 82795], .contexts [
        ⟨19689, true, false, [], [1]⟩,
        ⟨562, false, false, [83171], []⟩,
        ⟨563, false, false, [83171], []⟩,
        ⟨19499, false, false, [], [11]⟩,
        ⟨19500, false, false, [], [11]⟩,
        ⟨19690, false, false, [], [11]⟩,
        ⟨19691, false, false, [], [11]⟩,
        ⟨19691, false, false, [], [11]⟩,
        ⟨19484, false, false, [15977], []⟩,
        ⟨19692, true, false, [], [82795]⟩,
        ⟨16724, false, false, [16009], []⟩,
        ⟨13, true, false, [], [16009, 82795]⟩
      ]⟩,
    ⟨[16011], [16008], .source 8070⟩,
    ⟨[82795, 1], [16011, 83187], .contexts [
        ⟨19693, true, false, [16008], [1]⟩,
        ⟨8, false, false, [16008, 83187], []⟩,
        ⟨19694, true, false, [], [83187]⟩
      ]⟩,
    ⟨[10729, 83187], [10729, 83187], .contexts []⟩,
    ⟨[83187], [83187], .contexts []⟩,
    ⟨[83187, 3], [10729, 83187], .contexts [
        ⟨19689, true, false, [], [3]⟩,
        ⟨215, false, false, [83171], []⟩,
        ⟨216, false, false, [83171], []⟩,
        ⟨19664, false, false, [], [11]⟩,
        ⟨19685, false, false, [10729], []⟩,
        ⟨19696, false, false, [], []⟩,
        ⟨19697, false, false, [10729], []⟩,
        ⟨19511, true, false, [], [83187]⟩
      ]⟩,
    ⟨[83187, 7], [14023, 77631], .contexts [
        ⟨19689, true, false, [], [7]⟩,
        ⟨647, false, false, [83171], []⟩,
        ⟨648, false, false, [83171], []⟩,
        ⟨19668, false, false, [], [11]⟩,
        ⟨6610, false, false, [], []⟩,
        ⟨12728, false, false, [3271], []⟩,
        ⟨14245, true, false, [], [77631]⟩,
        ⟨6125, false, false, [14023], []⟩,
        ⟨13, true, false, [], [14023, 77631]⟩
      ]⟩,
    ⟨[16013], [14022], .source 8071⟩,
    ⟨[77631, 7], [16013, 83187], .contexts [
        ⟨19699, true, false, [14022], [7]⟩,
        ⟨38, false, false, [14022, 83187], []⟩,
        ⟨19700, true, false, [], [83187]⟩
      ]⟩,
    ⟨[16007, 83185], [16007, 83185], .contexts []⟩,
    ⟨[16007, 83185], [16007, 83185], .contexts []⟩,
    ⟨[16007, 83187], [16007, 83187], .contexts []⟩,
    ⟨[83187, 9], [16007, 83187], .contexts [
        ⟨19689, true, false, [], [9]⟩,
        ⟨221, false, false, [83171], []⟩,
        ⟨224, false, false, [83171], []⟩,
        ⟨19663, false, false, [], [11, 9, 11]⟩,
        ⟨19683, false, false, [], [9, 11]⟩,
        ⟨19702, false, false, [], [9, 11]⟩,
        ⟨19703, false, false, [], [9, 11]⟩,
        ⟨19703, false, false, [], [9, 11]⟩,
        ⟨19660, false, false, [16007], [11]⟩,
        ⟨19685, false, false, [16007], []⟩,
        ⟨19704, false, false, [], []⟩,
        ⟨19697, false, false, [16007], []⟩,
        ⟨13, true, false, [], [16007, 83187]⟩
      ]⟩,
    ⟨[2959, 83187], [2959, 83187], .contexts []⟩,
    ⟨[83187, 13], [2959, 83187], .contexts [
        ⟨19689, true, false, [], [13]⟩,
        ⟨227, false, false, [83171], []⟩,
        ⟨228, false, false, [83171], []⟩,
        ⟨19674, false, false, [], [11]⟩,
        ⟨19685, false, false, [2959], []⟩,
        ⟨19706, false, false, [], []⟩,
        ⟨19697, false, false, [2959], []⟩,
        ⟨19517, true, false, [], [83187]⟩
      ]⟩,
    ⟨[727, 83187], [727, 83187], .contexts []⟩,
    ⟨[83187, 15], [727, 83187], .contexts [
        ⟨19689, true, false, [], [15]⟩,
        ⟨231, false, false, [83171], []⟩,
        ⟨232, false, false, [83171], []⟩,
        ⟨19676, false, false, [], [11]⟩,
        ⟨19685, false, false, [727], []⟩,
        ⟨19708, false, false, [], []⟩,
        ⟨19697, false, false, [727], []⟩,
        ⟨19522, true, false, [], [83187]⟩
      ]⟩,
    ⟨[83189], [77811, 7], .source 41659⟩,
    ⟨[77811, 7], [83189], .contexts [
        ⟨19710, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 308. -/
def y322TCIndexRaw308 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83189, 7], [77811], .contexts [
        ⟨19711, true, false, [], [7]⟩,
        ⟨38, false, false, [77811], []⟩,
        ⟨2601, false, false, [], []⟩
      ]⟩,
    ⟨[77811, 7], [83189], .contexts [
        ⟨19711, false, false, [], []⟩
      ]⟩,
    ⟨[83189], [83189], .contexts []⟩,
    ⟨[83189], [83189], .contexts []⟩,
    ⟨[77811, 7], [83189], .contexts [
        ⟨19713, false, false, [], []⟩,
        ⟨19714, false, false, [], []⟩,
        ⟨19715, false, false, [], []⟩,
        ⟨19715, false, false, [], []⟩
      ]⟩,
    ⟨[16015], [12509, 8073], .source 8072⟩,
    ⟨[16015, 83179], [16015, 83179], .contexts []⟩,
    ⟨[16015, 83179], [16015, 83179], .contexts []⟩,
    ⟨[83189, 3], [83189, 3], .contexts []⟩,
    ⟨[16015], [16015], .contexts [
        ⟨13, false, false, [], [16015]⟩
      ]⟩,
    ⟨[83189, 3], [16015, 83179], .contexts [
        ⟨19720, false, false, [], []⟩,
        ⟨19716, true, false, [], [3]⟩,
        ⟨1034, false, false, [77811], []⟩,
        ⟨1035, false, false, [77811], []⟩,
        ⟨13541, false, false, [], [7]⟩,
        ⟨13950, false, false, [12509], [7]⟩,
        ⟨13949, false, false, [12509], [7]⟩,
        ⟨19717, true, false, [], [77439, 7]⟩,
        ⟨19593, false, false, [16015], []⟩,
        ⟨19718, false, false, [], []⟩,
        ⟨19719, false, false, [], []⟩,
        ⟨19606, false, false, [16015], []⟩,
        ⟨19721, true, false, [], [83179]⟩
      ]⟩,
    ⟨[16017], [16014], .source 8073⟩,
    ⟨[83179, 3], [16017, 83189], .contexts [
        ⟨19722, true, false, [16014], [3]⟩,
        ⟨20, false, false, [16014, 83189], []⟩,
        ⟨19723, true, false, [], [83189]⟩
      ]⟩,
    ⟨[12659, 77811], [12659, 77811], .contexts []⟩,
    ⟨[12659, 77811], [12659, 77811], .contexts []⟩,
    ⟨[12659, 83189], [12659, 83189], .contexts []⟩,
    ⟨[12659, 83189], [12659, 83189], .contexts []⟩,
    ⟨[83189, 13], [83189, 13], .contexts []⟩,
    ⟨[83189], [83189], .contexts []⟩,
    ⟨[12659], [12659], .contexts [
        ⟨13, false, false, [], [12659]⟩
      ]⟩,
    ⟨[83189, 13], [12659, 83189], .contexts [
        ⟨19729, false, false, [], []⟩,
        ⟨19716, true, false, [], [13]⟩,
        ⟨1056, false, false, [77811], []⟩,
        ⟨1057, false, false, [77811], []⟩,
        ⟨13728, false, false, [], [7]⟩,
        ⟨19725, false, false, [], [7]⟩,
        ⟨19726, false, false, [], [7]⟩,
        ⟨19726, false, false, [], [7]⟩,
        ⟨19711, false, false, [12659], []⟩,
        ⟨19727, false, false, [], []⟩,
        ⟨19728, false, false, [], []⟩,
        ⟨19730, false, false, [12659], []⟩,
        ⟨19731, true, false, [], [83189]⟩
      ]⟩,
    ⟨[12501, 77811], [12501, 77811], .contexts []⟩,
    ⟨[12501, 77811], [12501, 77811], .contexts []⟩,
    ⟨[12501, 83189], [12501, 83189], .contexts []⟩,
    ⟨[12501, 83189], [12501, 83189], .contexts []⟩,
    ⟨[83189, 15], [83189, 15], .contexts []⟩,
    ⟨[12501], [12501], .contexts [
        ⟨13, false, false, [], [12501]⟩
      ]⟩,
    ⟨[83189, 15], [12501, 83189], .contexts [
        ⟨19737, false, false, [], []⟩,
        ⟨19716, true, false, [], [15]⟩,
        ⟨1063, false, false, [77811], []⟩,
        ⟨1064, false, false, [77811], []⟩,
        ⟨13538, false, false, [], [7]⟩,
        ⟨19733, false, false, [], [7]⟩,
        ⟨19734, false, false, [], [7]⟩,
        ⟨19734, false, false, [], [7]⟩,
        ⟨19711, false, false, [12501], []⟩,
        ⟨19735, false, false, [], []⟩,
        ⟨19736, false, false, [], []⟩,
        ⟨19730, false, false, [12501], []⟩,
        ⟨19738, true, false, [], [83189]⟩
      ]⟩,
    ⟨[83179, 9], [83191], .source 75115⟩,
    ⟨[83191, 9], [83179], .contexts [
        ⟨19740, true, false, [], [9]⟩,
        ⟨46, false, false, [83179], []⟩,
        ⟨19596, false, false, [], []⟩
      ]⟩,
    ⟨[83191], [83191], .contexts []⟩,
    ⟨[83191], [83191], .source 75116⟩,
    ⟨[83179, 9], [83191], .source 75117⟩,
    ⟨[11247], [11247], .contexts [
        ⟨13, false, false, [], [11247]⟩
      ]⟩,
    ⟨[83191, 7], [11247, 77889], .source 75119⟩,
    ⟨[77889, 7], [14161, 83191], .contexts [
        ⟨19746, true, false, [11246], [7]⟩,
        ⟨38, false, false, [11246, 83191], []⟩,
        ⟨14349, true, false, [], [83191]⟩
      ]⟩,
    ⟨[2797, 83191], [2797, 83191], .contexts []⟩,
    ⟨[2797, 83191], [2797, 83191], .contexts []⟩,
    ⟨[83191, 13], [83191, 13], .contexts []⟩,
    ⟨[83191], [83191], .contexts []⟩,
    ⟨[83191, 13], [2797, 83191], .contexts [
        ⟨19750, false, false, [], []⟩,
        ⟨19744, true, false, [], [13]⟩,
        ⟨201, false, false, [83179], []⟩,
        ⟨202, false, false, [83179], []⟩,
        ⟨19623, false, false, [], [9]⟩,
        ⟨19740, false, false, [2797], []⟩,
        ⟨19748, false, false, [], []⟩,
        ⟨19749, false, false, [], []⟩,
        ⟨19751, false, false, [2797], []⟩,
        ⟨19607, true, false, [], [83191]⟩
      ]⟩,
    ⟨[727, 83191], [727, 83191], .contexts []⟩,
    ⟨[727, 83191], [727, 83191], .contexts []⟩,
    ⟨[83191, 15], [83191, 15], .contexts []⟩,
    ⟨[83191, 15], [727, 83191], .contexts [
        ⟨19755, false, false, [], []⟩,
        ⟨19744, true, false, [], [15]⟩,
        ⟨205, false, false, [83179], []⟩,
        ⟨206, false, false, [83179], []⟩,
        ⟨19629, false, false, [], [9]⟩,
        ⟨19740, false, false, [727], []⟩,
        ⟨19753, false, false, [], []⟩,
        ⟨19754, false, false, [], []⟩,
        ⟨19751, false, false, [727], []⟩,
        ⟨19522, true, false, [], [83191]⟩
      ]⟩,
    ⟨[11247, 77889], [11247, 77889], .contexts []⟩,
    ⟨[16021, 83191, 11], [83191], .source 75122⟩,
    ⟨[83191, 11], [83191, 11], .contexts []⟩,
    ⟨[16023], [16020], .source 75123⟩,
    ⟨[16020], [16020], .source 75124⟩,
    ⟨[16023], [16020], .contexts [
        ⟨19760, false, false, [], []⟩,
        ⟨19761, false, false, [], []⟩,
        ⟨19761, false, false, [], []⟩
      ]⟩,
    ⟨[83191, 11], [16023, 83191], .contexts [
        ⟨19759, false, false, [], []⟩,
        ⟨19758, false, false, [16020], []⟩,
        ⟨19751, false, false, [16020], []⟩,
        ⟨19762, true, false, [], [83191]⟩
      ]⟩,
    ⟨[83179, 11], [83193], .source 75126⟩,
    ⟨[83193, 11], [83179], .contexts [
        ⟨19764, true, false, [], [11]⟩,
        ⟨53, false, false, [83179], []⟩,
        ⟨19596, false, false, [], []⟩
      ]⟩,
    ⟨[83193], [83193], .contexts []⟩,
    ⟨[83193], [83193], .source 75127⟩,
    ⟨[83179, 11], [83193], .source 75128⟩,
    ⟨[15987, 82791], [15987, 82791], .source 75129⟩,
    ⟨[15987, 82791], [15987, 82791], .source 75130⟩,
    ⟨[83179, 1, 11], [15987, 82791], .source 75131⟩,
    ⟨[83193, 1], [83193, 1], .source 75132⟩,
    ⟨[83193, 1], [15987, 82791], .contexts [
        ⟨19772, false, false, [], []⟩,
        ⟨19768, true, false, [], [1]⟩,
        ⟨562, false, false, [83179], []⟩,
        ⟨563, false, false, [83179], []⟩,
        ⟨19771, false, false, [], []⟩,
        ⟨19770, false, false, [], []⟩,
        ⟨19541, false, false, [], []⟩,
        ⟨19542, false, false, [], []⟩
      ]⟩,
    ⟨[82791, 1], [15989, 83193], .contexts [
        ⟨19773, true, false, [15986], [1]⟩,
        ⟨8, false, false, [15986, 83193], []⟩,
        ⟨19544, true, false, [], [83193]⟩
      ]⟩,
    ⟨[83193, 7], [13089, 78757], .contexts [
        ⟨19768, true, false, [], [7]⟩,
        ⟨647, false, false, [83179], []⟩,
        ⟨648, false, false, [83179], []⟩,
        ⟨19643, false, false, [], [11]⟩,
        ⟨1419, false, false, [], [11]⟩,
        ⟨1371, false, false, [], [11]⟩,
        ⟨1371, false, false, [], [11]⟩,
        ⟨6573, false, false, [], []⟩,
        ⟨14367, false, false, [], []⟩,
        ⟨14368, false, false, [], []⟩,
        ⟨14369, false, false, [], []⟩,
        ⟨6679, false, false, [13089], []⟩,
        ⟨13, true, false, [], [13089, 78757]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 309. -/
def y322TCIndexRaw309 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[78757, 7], [14509, 83193], .contexts [
        ⟨19775, true, false, [13088], [7]⟩,
        ⟨38, false, false, [13088, 83193], []⟩,
        ⟨14371, true, false, [], [83193]⟩
      ]⟩,
    ⟨[16023, 83191], [16023, 83191], .contexts []⟩,
    ⟨[16023, 83191], [16023, 83191], .source 75133⟩,
    ⟨[16023, 83193], [16023, 83193], .source 75134⟩,
    ⟨[83179, 9, 11, 9, 11], [16023, 83193], .source 75135⟩,
    ⟨[16023, 83193], [16023, 83193], .source 75136⟩,
    ⟨[83193, 9], [83193, 9], .source 75137⟩,
    ⟨[83193], [83193], .contexts []⟩,
    ⟨[16023], [16023], .source 75138⟩,
    ⟨[83193, 9], [16023, 83193], .contexts [
        ⟨19782, false, false, [], []⟩,
        ⟨19768, true, false, [], [9]⟩,
        ⟨221, false, false, [83179], []⟩,
        ⟨224, false, false, [83179], []⟩,
        ⟨19780, false, false, [], []⟩,
        ⟨19781, false, false, [], []⟩,
        ⟨19783, false, false, [16023], []⟩,
        ⟨19784, true, false, [], [83193]⟩
      ]⟩,
    ⟨[2797, 83193], [2797, 83193], .contexts []⟩,
    ⟨[2797, 83193], [2797, 83193], .contexts []⟩,
    ⟨[83193, 13], [83193, 13], .contexts []⟩,
    ⟨[83193, 13], [2797, 83193], .contexts [
        ⟨19788, false, false, [], []⟩,
        ⟨19768, true, false, [], [13]⟩,
        ⟨227, false, false, [83179], []⟩,
        ⟨228, false, false, [83179], []⟩,
        ⟨19623, false, false, [], [11]⟩,
        ⟨19764, false, false, [2797], []⟩,
        ⟨19786, false, false, [], []⟩,
        ⟨19787, false, false, [], []⟩,
        ⟨19783, false, false, [2797], []⟩,
        ⟨19607, true, false, [], [83193]⟩
      ]⟩,
    ⟨[727, 83193], [727, 83193], .contexts []⟩,
    ⟨[727, 83193], [727, 83193], .contexts []⟩,
    ⟨[83193, 15], [83193, 15], .contexts []⟩,
    ⟨[83193, 15], [727, 83193], .contexts [
        ⟨19792, false, false, [], []⟩,
        ⟨19768, true, false, [], [15]⟩,
        ⟨231, false, false, [83179], []⟩,
        ⟨232, false, false, [83179], []⟩,
        ⟨19629, false, false, [], [11]⟩,
        ⟨19764, false, false, [727], []⟩,
        ⟨19790, false, false, [], []⟩,
        ⟨19791, false, false, [], []⟩,
        ⟨19783, false, false, [727], []⟩,
        ⟨19522, true, false, [], [83193]⟩
      ]⟩,
    ⟨[83195], [82785, 5], .source 41662⟩,
    ⟨[82785, 5], [83195], .contexts [
        ⟨19794, true, false, [], []⟩
      ]⟩,
    ⟨[83195, 5], [82785], .contexts [
        ⟨19795, true, false, [], [5]⟩,
        ⟨28, false, false, [82785], []⟩,
        ⟨16621, false, false, [], []⟩
      ]⟩,
    ⟨[82785, 5], [83195], .contexts [
        ⟨19795, false, false, [], []⟩
      ]⟩,
    ⟨[83195], [83195], .contexts []⟩,
    ⟨[83195], [83195], .contexts []⟩,
    ⟨[82785, 5], [83195], .contexts [
        ⟨19797, false, false, [], []⟩,
        ⟨19798, false, false, [], []⟩,
        ⟨19799, false, false, [], []⟩,
        ⟨19799, false, false, [], []⟩
      ]⟩,
    ⟨[15997, 83177], [15997, 83177], .contexts []⟩,
    ⟨[15997, 83177], [15997, 83177], .contexts []⟩,
    ⟨[83195, 9], [83195, 9], .contexts []⟩,
    ⟨[15997], [15997], .contexts [
        ⟨13, false, false, [], [15997]⟩
      ]⟩,
    ⟨[83195, 9], [15997, 83177], .contexts [
        ⟨19803, false, false, [], []⟩,
        ⟨19800, true, false, [], [9]⟩,
        ⟨1265, false, false, [82785], []⟩,
        ⟨1266, false, false, [82785], []⟩,
        ⟨19480, false, false, [], [5]⟩,
        ⟨19466, false, false, [], [5]⟩,
        ⟨19467, false, false, [], [5]⟩,
        ⟨19467, false, false, [], [5]⟩,
        ⟨19586, false, false, [], []⟩,
        ⟨19801, false, false, [], []⟩,
        ⟨19802, false, false, [], []⟩,
        ⟨19802, false, false, [], []⟩,
        ⟨19591, false, false, [15997], []⟩,
        ⟨19804, true, false, [], [83177]⟩
      ]⟩,
    ⟨[15995], [15996], .contexts [
        ⟨19585, true, true, [], []⟩
      ]⟩,
    ⟨[83177, 9], [15995, 83195], .contexts [
        ⟨19805, true, false, [15996], [9]⟩,
        ⟨46, false, false, [15996, 83195], []⟩,
        ⟨19806, true, false, [], [83195]⟩
      ]⟩,
    ⟨[83195, 13], [83195, 13], .contexts []⟩,
    ⟨[83195, 13], [79369], .contexts [
        ⟨19808, false, false, [], []⟩,
        ⟨19800, true, false, [], [13]⟩,
        ⟨179, false, false, [82785], []⟩,
        ⟨180, false, false, [82785], []⟩,
        ⟨16618, false, false, [], [5]⟩,
        ⟨6777, false, false, [], [5]⟩,
        ⟨6778, false, false, [], [5]⟩,
        ⟨6778, false, false, [], [5]⟩,
        ⟨6784, false, false, [], []⟩,
        ⟨6785, false, false, [], []⟩,
        ⟨6786, false, false, [], []⟩,
        ⟨6786, false, false, [], []⟩,
        ⟨6913, false, false, [], []⟩,
        ⟨6914, false, false, [], []⟩
      ]⟩,
    ⟨[79369, 13], [83195], .contexts [
        ⟨19809, true, false, [], [13]⟩,
        ⟨59, false, false, [83195], []⟩,
        ⟨19799, false, false, [], []⟩
      ]⟩,
    ⟨[15459, 83195], [15459, 83195], .contexts []⟩,
    ⟨[15459, 83195], [15459, 83195], .contexts []⟩,
    ⟨[83195, 15], [83195, 15], .contexts []⟩,
    ⟨[83195], [83195], .contexts []⟩,
    ⟨[83195, 15], [15459, 83195], .contexts [
        ⟨19813, false, false, [], []⟩,
        ⟨19800, true, false, [], [15]⟩,
        ⟨184, false, false, [82785], []⟩,
        ⟨185, false, false, [82785], []⟩,
        ⟨16630, false, false, [], [5]⟩,
        ⟨16634, false, false, [], [5]⟩,
        ⟨16628, false, false, [], [5]⟩,
        ⟨16629, false, false, [], [5]⟩,
        ⟨16629, false, false, [], [5]⟩,
        ⟨19795, false, false, [15459], []⟩,
        ⟨19811, false, false, [], []⟩,
        ⟨19812, false, false, [], []⟩,
        ⟨19814, false, false, [15459], []⟩,
        ⟨16633, true, false, [], [83195]⟩
      ]⟩,
    ⟨[83197], [83195, 7], .source 41663⟩,
    ⟨[83195, 7], [83197], .contexts [
        ⟨19816, true, false, [], []⟩
      ]⟩,
    ⟨[83197, 7], [83195], .contexts [
        ⟨19817, true, false, [], [7]⟩,
        ⟨38, false, false, [83195], []⟩,
        ⟨19799, false, false, [], []⟩
      ]⟩,
    ⟨[83195, 7], [83197], .contexts [
        ⟨19817, false, false, [], []⟩
      ]⟩,
    ⟨[83197], [83197], .contexts []⟩,
    ⟨[83197], [83197], .contexts []⟩,
    ⟨[83195, 7], [83197], .contexts [
        ⟨19819, false, false, [], []⟩,
        ⟨19820, false, false, [], []⟩,
        ⟨19821, false, false, [], []⟩,
        ⟨19821, false, false, [], []⟩
      ]⟩,
    ⟨[7429, 77525], [7429, 77525], .contexts []⟩,
    ⟨[16025], [7429, 6647], .source 8077⟩,
    ⟨[16027], [16025, 7675], .source 8078⟩,
    ⟨[83197, 5], [16027, 79379], .contexts [
        ⟨19822, true, false, [], [5]⟩,
        ⟨1043, false, false, [83195], []⟩,
        ⟨1046, false, false, [83195], []⟩,
        ⟨19796, false, false, [], [7, 5, 7]⟩,
        ⟨16620, false, false, [], [7, 5, 7]⟩,
        ⟨16621, false, false, [], [7, 5, 7]⟩,
        ⟨16621, false, false, [], [7, 5, 7]⟩,
        ⟨16623, false, false, [], [5, 7]⟩,
        ⟨19823, false, false, [], [5, 7]⟩,
        ⟨11052, false, false, [], [5, 7]⟩,
        ⟨11052, false, false, [], [5, 7]⟩,
        ⟨10722, false, false, [7429], [7]⟩,
        ⟨19824, true, false, [], [77443, 7]⟩,
        ⟨11144, false, false, [16025], []⟩,
        ⟨19825, true, false, [], [79379]⟩,
        ⟨6840, false, false, [16027], []⟩
      ]⟩,
    ⟨[83197, 5], [16027, 79379], .contexts [
        ⟨19826, false, false, [], []⟩,
        ⟨13, true, false, [], [16027, 79379]⟩
      ]⟩,
    ⟨[16029], [16026], .source 8079⟩,
    ⟨[79379, 5], [16029, 83197], .contexts [
        ⟨19827, true, false, [16026], [5]⟩,
        ⟨28, false, false, [16026, 83197], []⟩,
        ⟨19828, true, false, [], [83197]⟩
      ]⟩,
    ⟨[15997, 83175], [15997, 83175], .contexts []⟩,
    ⟨[83197, 9], [15997, 83175], .contexts [
        ⟨19822, true, false, [], [9]⟩,
        ⟨1534, false, false, [83195], []⟩,
        ⟨1535, false, false, [83195], []⟩,
        ⟨19803, false, false, [], [7]⟩,
        ⟨19805, false, false, [], [7]⟩,
        ⟨19801, false, false, [], [7]⟩,
        ⟨19802, false, false, [], [7]⟩,
        ⟨19802, false, false, [], [7]⟩,
        ⟨19577, false, false, [15997], []⟩,
        ⟨19830, false, false, [], []⟩,
        ⟨19573, false, false, [15997], []⟩,
        ⟨19804, true, false, [], [83175]⟩
      ]⟩,
    ⟨[83175, 9], [15995, 83197], .contexts [
        ⟨19831, true, false, [15996], [9]⟩,
        ⟨46, false, false, [15996, 83197], []⟩,
        ⟨19806, true, false, [], [83197]⟩
      ]⟩,
    ⟨[83197, 13], [79371], .contexts [
        ⟨19822, true, false, [], [13]⟩,
        ⟨1056, false, false, [83195], []⟩,
        ⟨1057, false, false, [83195], []⟩,
        ⟨19808, false, false, [], [7]⟩,
        ⟨19809, false, false, [], [7]⟩,
        ⟨6785, false, false, [], [7]⟩,
        ⟨6786, false, false, [], [7]⟩,
        ⟨6786, false, false, [], [7]⟩,
        ⟨6797, false, false, [], []⟩,
        ⟨6798, false, false, [], []⟩,
        ⟨6799, false, false, [], []⟩,
        ⟨6799, false, false, [], []⟩,
        ⟨6930, false, false, [], []⟩,
        ⟨6931, false, false, [], []⟩
      ]⟩,
    ⟨[79371, 13], [83197], .contexts [
        ⟨19833, true, false, [], [13]⟩,
        ⟨59, false, false, [83197], []⟩,
        ⟨19821, false, false, [], []⟩
      ]⟩,
    ⟨[15459, 83197], [15459, 83197], .contexts []⟩,
    ⟨[83197], [83197], .contexts []⟩,
    ⟨[83199], [82819, 5], .source 41664⟩,
    ⟨[82819, 5], [83199], .contexts [
        ⟨19837, true, false, [], []⟩
      ]⟩,
    ⟨[83199, 5], [82819], .contexts [
        ⟨19838, true, false, [], [5]⟩,
        ⟨28, false, false, [82819], []⟩,
        ⟨17037, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 310. -/
def y322TCIndexRaw310 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83199], [83199], .contexts []⟩,
    ⟨[83199], [83199], .contexts []⟩,
    ⟨[82819, 5], [83199], .contexts [
        ⟨19838, false, false, [], []⟩,
        ⟨19840, false, false, [], []⟩,
        ⟨19841, false, false, [], []⟩,
        ⟨19841, false, false, [], []⟩
      ]⟩,
    ⟨[83199, 11], [83199, 11], .contexts []⟩,
    ⟨[83199, 11], [83195], .contexts [
        ⟨19843, false, false, [], []⟩,
        ⟨19842, true, false, [], [11]⟩,
        ⟨174, false, false, [82819], []⟩,
        ⟨175, false, false, [82819], []⟩,
        ⟨17056, false, false, [], [5]⟩,
        ⟨17059, false, false, [], [5]⟩,
        ⟨16620, false, false, [], [5]⟩,
        ⟨16621, false, false, [], [5]⟩,
        ⟨16621, false, false, [], [5]⟩,
        ⟨19797, false, false, [], []⟩,
        ⟨19798, false, false, [], []⟩,
        ⟨19799, false, false, [], []⟩,
        ⟨19799, false, false, [], []⟩,
        ⟨19814, false, false, [], []⟩,
        ⟨672, true, false, [], [83195]⟩
      ]⟩,
    ⟨[83195, 11], [83199], .contexts [
        ⟨19844, true, false, [], [11]⟩,
        ⟨53, false, false, [83199], []⟩,
        ⟨19841, false, false, [], []⟩
      ]⟩,
    ⟨[83199, 13], [83199, 13], .contexts []⟩,
    ⟨[83199, 13], [79193], .contexts [
        ⟨19846, false, false, [], []⟩,
        ⟨19842, true, false, [], [13]⟩,
        ⟨179, false, false, [82819], []⟩,
        ⟨180, false, false, [82819], []⟩,
        ⟨17035, false, false, [], [5]⟩,
        ⟨6281, false, false, [], [5]⟩,
        ⟨6282, false, false, [], [5]⟩,
        ⟨6282, false, false, [], [5]⟩,
        ⟨6290, false, false, [], []⟩,
        ⟨6291, false, false, [], []⟩,
        ⟨6292, false, false, [], []⟩,
        ⟨6292, false, false, [], []⟩,
        ⟨6790, false, false, [], []⟩,
        ⟨6791, false, false, [], []⟩
      ]⟩,
    ⟨[79193, 13], [83199], .contexts [
        ⟨19847, true, false, [], [13]⟩,
        ⟨59, false, false, [83199], []⟩,
        ⟨19841, false, false, [], []⟩
      ]⟩,
    ⟨[15499, 83199], [15499, 83199], .contexts []⟩,
    ⟨[15499, 83199], [15499, 83199], .contexts []⟩,
    ⟨[83199, 15], [83199, 15], .contexts []⟩,
    ⟨[83199], [83199], .contexts []⟩,
    ⟨[83199, 15], [15499, 83199], .contexts [
        ⟨19851, false, false, [], []⟩,
        ⟨19842, true, false, [], [15]⟩,
        ⟨184, false, false, [82819], []⟩,
        ⟨185, false, false, [82819], []⟩,
        ⟨17065, false, false, [], [5]⟩,
        ⟨17068, false, false, [], [5]⟩,
        ⟨17063, false, false, [], [5]⟩,
        ⟨17064, false, false, [], [5]⟩,
        ⟨17064, false, false, [], [5]⟩,
        ⟨19838, false, false, [15499], []⟩,
        ⟨19849, false, false, [], []⟩,
        ⟨19850, false, false, [], []⟩,
        ⟨19852, false, false, [15499], []⟩,
        ⟨16822, true, false, [], [83199]⟩
      ]⟩,
    ⟨[83201], [83199, 7], .source 41665⟩,
    ⟨[83199, 7], [83201], .contexts [
        ⟨19854, true, false, [], []⟩
      ]⟩,
    ⟨[83201, 7], [83199], .contexts [
        ⟨19855, true, false, [], [7]⟩,
        ⟨38, false, false, [83199], []⟩,
        ⟨19841, false, false, [], []⟩
      ]⟩,
    ⟨[83201], [83201], .contexts []⟩,
    ⟨[83201], [83201], .contexts []⟩,
    ⟨[83199, 7], [83201], .contexts [
        ⟨19855, false, false, [], []⟩,
        ⟨19857, false, false, [], []⟩,
        ⟨19858, false, false, [], []⟩,
        ⟨19858, false, false, [], []⟩
      ]⟩,
    ⟨[15557, 77517], [15557, 77517], .contexts []⟩,
    ⟨[15557, 77517], [15557, 77517], .contexts []⟩,
    ⟨[16031], [15557, 7727], .source 8080⟩,
    ⟨[16033], [16031, 7729], .source 8081⟩,
    ⟨[83201, 5], [16033, 79199], .contexts [
        ⟨19859, true, false, [], [5]⟩,
        ⟨1043, false, false, [83199], []⟩,
        ⟨1046, false, false, [83199], []⟩,
        ⟨19839, false, false, [], [7, 5, 7]⟩,
        ⟨17036, false, false, [], [7, 5, 7]⟩,
        ⟨17037, false, false, [], [7, 5, 7]⟩,
        ⟨17037, false, false, [], [7, 5, 7]⟩,
        ⟨17051, false, false, [], [5, 7]⟩,
        ⟨19860, false, false, [], [5, 7]⟩,
        ⟨19861, false, false, [], [5, 7]⟩,
        ⟨19861, false, false, [], [5, 7]⟩,
        ⟨1825, false, false, [15557], [7]⟩,
        ⟨11172, false, false, [15557], [7]⟩,
        ⟨19862, true, false, [], [77445, 7]⟩,
        ⟨11175, false, false, [16031], []⟩,
        ⟨19863, true, false, [], [79199]⟩,
        ⟨6342, false, false, [16033], []⟩
      ]⟩,
    ⟨[83201, 5], [16033, 79199], .contexts [
        ⟨19864, false, false, [], []⟩,
        ⟨13, true, false, [], [16033, 79199]⟩
      ]⟩,
    ⟨[16035], [16032], .source 8082⟩,
    ⟨[79199, 5], [16035, 83201], .contexts [
        ⟨19865, true, false, [16032], [5]⟩,
        ⟨28, false, false, [16032, 83201], []⟩,
        ⟨19866, true, false, [], [83201]⟩
      ]⟩,
    ⟨[83201, 11], [83197], .contexts [
        ⟨19859, true, false, [], [11]⟩,
        ⟨1051, false, false, [83199], []⟩,
        ⟨1052, false, false, [83199], []⟩,
        ⟨19843, false, false, [], [7]⟩,
        ⟨19844, false, false, [], [7]⟩,
        ⟨19798, false, false, [], [7]⟩,
        ⟨19799, false, false, [], [7]⟩,
        ⟨19799, false, false, [], [7]⟩,
        ⟨19819, false, false, [], []⟩,
        ⟨19820, false, false, [], []⟩,
        ⟨19821, false, false, [], []⟩,
        ⟨19821, false, false, [], []⟩,
        ⟨19836, false, false, [], []⟩,
        ⟨672, true, false, [], [83197]⟩
      ]⟩,
    ⟨[83197, 11], [83201], .contexts [
        ⟨19868, true, false, [], [11]⟩,
        ⟨53, false, false, [83201], []⟩,
        ⟨19858, false, false, [], []⟩
      ]⟩,
    ⟨[83201, 13], [83201, 13], .contexts []⟩,
    ⟨[83201, 13], [79195], .contexts [
        ⟨19870, false, false, [], []⟩,
        ⟨19859, true, false, [], [13]⟩,
        ⟨1056, false, false, [83199], []⟩,
        ⟨1057, false, false, [83199], []⟩,
        ⟨19846, false, false, [], [7]⟩,
        ⟨19847, false, false, [], [7]⟩,
        ⟨6291, false, false, [], [7]⟩,
        ⟨6292, false, false, [], [7]⟩,
        ⟨6292, false, false, [], [7]⟩,
        ⟨6304, false, false, [], []⟩,
        ⟨6305, false, false, [], []⟩,
        ⟨6306, false, false, [], []⟩,
        ⟨6306, false, false, [], []⟩,
        ⟨6805, false, false, [], []⟩,
        ⟨6806, false, false, [], []⟩
      ]⟩,
    ⟨[15499, 83201], [15499, 83201], .contexts []⟩,
    ⟨[15499, 83201], [15499, 83201], .contexts []⟩,
    ⟨[83201, 15], [83201, 15], .contexts []⟩,
    ⟨[83201], [83201], .contexts []⟩,
    ⟨[83201, 15], [15499, 83201], .contexts [
        ⟨19874, false, false, [], []⟩,
        ⟨19859, true, false, [], [15]⟩,
        ⟨1063, false, false, [83199], []⟩,
        ⟨1064, false, false, [83199], []⟩,
        ⟨19851, false, false, [], [7]⟩,
        ⟨19853, false, false, [], [7]⟩,
        ⟨19849, false, false, [], [7]⟩,
        ⟨19850, false, false, [], [7]⟩,
        ⟨19850, false, false, [], [7]⟩,
        ⟨19855, false, false, [15499], []⟩,
        ⟨19872, false, false, [], []⟩,
        ⟨19873, false, false, [], []⟩,
        ⟨19875, false, false, [15499], []⟩,
        ⟨16822, true, false, [], [83201]⟩
      ]⟩,
    ⟨[83203], [81373, 5], .source 41666⟩,
    ⟨[81373, 5], [83203], .contexts [
        ⟨19877, true, false, [], []⟩
      ]⟩,
    ⟨[83203, 5], [81373], .contexts [
        ⟨19878, true, false, [], [5]⟩,
        ⟨28, false, false, [81373], []⟩,
        ⟨8945, false, false, [], []⟩
      ]⟩,
    ⟨[83203], [83203], .contexts []⟩,
    ⟨[83203], [83203], .contexts []⟩,
    ⟨[81373, 5], [83203], .contexts [
        ⟨19878, false, false, [], []⟩,
        ⟨19880, false, false, [], []⟩,
        ⟨19881, false, false, [], []⟩,
        ⟨19881, false, false, [], []⟩
      ]⟩,
    ⟨[15553, 82819], [15553, 82819], .contexts []⟩,
    ⟨[15553, 82819], [15553, 82819], .contexts []⟩,
    ⟨[81373, 1], [15553, 82819], .contexts [
        ⟨17046, false, false, [], []⟩,
        ⟨19883, false, false, [], []⟩,
        ⟨19884, false, false, [], []⟩,
        ⟨19884, false, false, [], []⟩
      ]⟩,
    ⟨[15553, 83199], [15553, 83199], .contexts []⟩,
    ⟨[15553, 83199], [15553, 83199], .contexts []⟩,
    ⟨[83203, 1], [83203, 1], .contexts []⟩,
    ⟨[15553], [15553], .contexts [
        ⟨13, false, false, [], [15553]⟩
      ]⟩,
    ⟨[83203, 1], [15553, 83199], .contexts [
        ⟨19888, false, false, [], []⟩,
        ⟨19882, true, false, [], [1]⟩,
        ⟨161, false, false, [81373], []⟩,
        ⟨162, false, false, [81373], []⟩,
        ⟨19885, false, false, [], [5]⟩,
        ⟨19838, false, false, [15553], []⟩,
        ⟨19886, false, false, [], []⟩,
        ⟨19887, false, false, [], []⟩,
        ⟨19852, false, false, [15553], []⟩,
        ⟨19889, true, false, [], [83199]⟩
      ]⟩,
    ⟨[15551], [15552], .contexts [
        ⟨17045, true, true, [], []⟩
      ]⟩,
    ⟨[83199, 1], [15551, 83203], .contexts [
        ⟨19890, true, false, [15552], [1]⟩,
        ⟨8, false, false, [15552, 83203], []⟩,
        ⟨19891, true, false, [], [83203]⟩
      ]⟩,
    ⟨[81373, 9], [4217, 81373], .contexts [
        ⟨8955, false, false, [], []⟩
      ]⟩,
    ⟨[4217, 83203], [4217, 83203], .contexts []⟩,
    ⟨[4217, 83203], [4217, 83203], .contexts []⟩,
    ⟨[83203, 9], [83203, 9], .contexts []⟩,
    ⟨[83203], [83203], .contexts []⟩,
    ⟨[83203, 9], [4217, 83203], .contexts [
        ⟨19896, false, false, [], []⟩,
        ⟨19882, true, false, [], [9]⟩,
        ⟨1265, false, false, [81373], []⟩,
        ⟨1266, false, false, [81373], []⟩,
        ⟨8953, false, false, [], [5]⟩,
        ⟨19893, false, false, [], [5]⟩,
        ⟨8951, false, false, [], [5]⟩,
        ⟨8952, false, false, [], [5]⟩,
        ⟨8952, false, false, [], [5]⟩,
        ⟨19878, false, false, [4217], []⟩,
        ⟨19894, false, false, [], []⟩,
        ⟨19895, false, false, [], []⟩,
        ⟨19897, false, false, [4217], []⟩,
        ⟨7911, true, false, [], [83203]⟩
      ]⟩,
    ⟨[81373, 13], [8409, 80991], .contexts [
        ⟨8943, false, false, [], []⟩,
        ⟨11525, false, false, [], []⟩,
        ⟨11504, false, false, [], []⟩,
        ⟨11504, false, false, [], []⟩
      ]⟩,
    ⟨[83203, 13], [83203, 13], .contexts []⟩,
    ⟨[83203, 13], [81365], .contexts [
        ⟨19900, false, false, [], []⟩,
        ⟨19882, true, false, [], [13]⟩,
        ⟨179, false, false, [81373], []⟩,
        ⟨180, false, false, [81373], []⟩,
        ⟨19899, false, false, [], [5]⟩,
        ⟨11509, false, false, [8409], []⟩,
        ⟨17142, true, false, [], [81365]⟩,
        ⟨9013, false, false, [], []⟩,
        ⟨9014, false, false, [], []⟩
      ]⟩,
    ⟨[81365, 13], [83203], .contexts [
        ⟨19901, true, false, [], [13]⟩,
        ⟨59, false, false, [83203], []⟩,
        ⟨19881, false, false, [], []⟩
      ]⟩,
    ⟨[15119, 81373], [15119, 81373], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 311. -/
def y322TCIndexRaw311 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15119, 81373], [15119, 81373], .contexts []⟩,
    ⟨[81373, 15], [15119, 81373], .contexts [
        ⟨14797, false, false, [], []⟩,
        ⟨14800, false, false, [], []⟩,
        ⟨19903, false, false, [], []⟩,
        ⟨19904, false, false, [], []⟩,
        ⟨19904, false, false, [], []⟩
      ]⟩,
    ⟨[15119, 83203], [15119, 83203], .contexts []⟩,
    ⟨[15119, 83203], [15119, 83203], .contexts []⟩,
    ⟨[83203, 15], [83203, 15], .contexts []⟩,
    ⟨[15119], [15119], .contexts [
        ⟨13, false, false, [], [15119]⟩
      ]⟩,
    ⟨[83203, 15], [15119, 83203], .contexts [
        ⟨19908, false, false, [], []⟩,
        ⟨19882, true, false, [], [15]⟩,
        ⟨184, false, false, [81373], []⟩,
        ⟨185, false, false, [81373], []⟩,
        ⟨19905, false, false, [], [5]⟩,
        ⟨19878, false, false, [15119], []⟩,
        ⟨19906, false, false, [], []⟩,
        ⟨19907, false, false, [], []⟩,
        ⟨19897, false, false, [15119], []⟩,
        ⟨19909, true, false, [], [83203]⟩
      ]⟩,
    ⟨[83205], [83203, 7], .source 41667⟩,
    ⟨[83203, 7], [83205], .contexts [
        ⟨19911, true, false, [], []⟩
      ]⟩,
    ⟨[83205, 7], [83203], .contexts [
        ⟨19912, true, false, [], [7]⟩,
        ⟨38, false, false, [83203], []⟩,
        ⟨19881, false, false, [], []⟩
      ]⟩,
    ⟨[83205], [83205], .contexts []⟩,
    ⟨[83205], [83205], .contexts []⟩,
    ⟨[83203, 7], [83205], .contexts [
        ⟨19912, false, false, [], []⟩,
        ⟨19914, false, false, [], []⟩,
        ⟨19915, false, false, [], []⟩,
        ⟨19915, false, false, [], []⟩
      ]⟩,
    ⟨[15553, 83201], [15553, 83201], .contexts []⟩,
    ⟨[15553, 83201], [15553, 83201], .contexts []⟩,
    ⟨[83205, 1], [15553, 83201], .contexts [
        ⟨19916, true, false, [], [1]⟩,
        ⟨1027, false, false, [83203], []⟩,
        ⟨1028, false, false, [83203], []⟩,
        ⟨19888, false, false, [], [7]⟩,
        ⟨19890, false, false, [], [7]⟩,
        ⟨19886, false, false, [], [7]⟩,
        ⟨19887, false, false, [], [7]⟩,
        ⟨19887, false, false, [], [7]⟩,
        ⟨19855, false, false, [15553], []⟩,
        ⟨19917, false, false, [], []⟩,
        ⟨19918, false, false, [], []⟩,
        ⟨19875, false, false, [15553], []⟩,
        ⟨19889, true, false, [], [83201]⟩
      ]⟩,
    ⟨[83201, 1], [15551, 83205], .contexts [
        ⟨19919, true, false, [15552], [1]⟩,
        ⟨8, false, false, [15552, 83205], []⟩,
        ⟨19891, true, false, [], [83205]⟩
      ]⟩,
    ⟨[81373, 7], [79723], .contexts [
        ⟨8949, false, false, [], []⟩
      ]⟩,
    ⟨[12295, 77519], [12295, 77519], .contexts []⟩,
    ⟨[16037], [5311, 6969], .source 8083⟩,
    ⟨[16039], [12295, 16037], .source 8084⟩,
    ⟨[16041], [16039, 6961], .source 8085⟩,
    ⟨[83205, 5], [83205, 5], .contexts []⟩,
    ⟨[83205, 5], [16041, 81951], .contexts [
        ⟨19926, false, false, [], []⟩,
        ⟨19916, true, false, [], [5]⟩,
        ⟨1043, false, false, [83203], []⟩,
        ⟨1046, false, false, [83203], []⟩,
        ⟨19879, false, false, [], [7, 5, 7]⟩,
        ⟨8944, false, false, [], [7, 5, 7]⟩,
        ⟨8945, false, false, [], [7, 5, 7]⟩,
        ⟨8945, false, false, [], [7, 5, 7]⟩,
        ⟨19921, false, false, [], [5, 7]⟩,
        ⟨13437, false, false, [], [5, 7]⟩,
        ⟨19922, false, false, [], [5, 7]⟩,
        ⟨19922, false, false, [], [5, 7]⟩,
        ⟨10268, false, false, [12295], [7]⟩,
        ⟨10803, false, false, [12295, 5311], [7]⟩,
        ⟨19923, true, false, [12295], [77447, 7]⟩,
        ⟨19924, true, false, [], [77447, 7]⟩,
        ⟨10800, false, false, [16039], []⟩,
        ⟨19925, true, false, [], [81951]⟩,
        ⟨9451, false, false, [16041], []⟩
      ]⟩,
    ⟨[83205, 5], [16041, 81951], .contexts [
        ⟨19927, false, false, [], []⟩,
        ⟨13, true, false, [], [16041, 81951]⟩
      ]⟩,
    ⟨[16043], [16040], .source 8086⟩,
    ⟨[81951, 5], [16043, 83205], .contexts [
        ⟨19928, true, false, [16040], [5]⟩,
        ⟨28, false, false, [16040, 83205], []⟩,
        ⟨19929, true, false, [], [83205]⟩
      ]⟩,
    ⟨[4217, 83205], [4217, 83205], .contexts []⟩,
    ⟨[4217, 83205], [4217, 83205], .contexts []⟩,
    ⟨[83205, 9], [83205, 9], .contexts []⟩,
    ⟨[83205], [83205], .contexts []⟩,
    ⟨[83205, 9], [4217, 83205], .contexts [
        ⟨19933, false, false, [], []⟩,
        ⟨19916, true, false, [], [9]⟩,
        ⟨1534, false, false, [83203], []⟩,
        ⟨1535, false, false, [83203], []⟩,
        ⟨19896, false, false, [], [7]⟩,
        ⟨19898, false, false, [], [7]⟩,
        ⟨19894, false, false, [], [7]⟩,
        ⟨19895, false, false, [], [7]⟩,
        ⟨19895, false, false, [], [7]⟩,
        ⟨19912, false, false, [4217], []⟩,
        ⟨19931, false, false, [], []⟩,
        ⟨19932, false, false, [], []⟩,
        ⟨19934, false, false, [4217], []⟩,
        ⟨7911, true, false, [], [83205]⟩
      ]⟩,
    ⟨[81365, 7], [81363], .contexts [
        ⟨8924, false, false, [], []⟩
      ]⟩,
    ⟨[83205, 13], [83205, 13], .contexts []⟩,
    ⟨[83205, 13], [81363], .contexts [
        ⟨19937, false, false, [], []⟩,
        ⟨19916, true, false, [], [13]⟩,
        ⟨1056, false, false, [83203], []⟩,
        ⟨1057, false, false, [83203], []⟩,
        ⟨19900, false, false, [], [7]⟩,
        ⟨19901, false, false, [], [7]⟩,
        ⟨8925, false, false, [], [7]⟩,
        ⟨8926, false, false, [], [7]⟩,
        ⟨8926, false, false, [], [7]⟩,
        ⟨19936, false, false, [], []⟩,
        ⟨8914, false, false, [], []⟩,
        ⟨8915, false, false, [], []⟩,
        ⟨8915, false, false, [], []⟩,
        ⟨9003, false, false, [], []⟩,
        ⟨9004, false, false, [], []⟩
      ]⟩,
    ⟨[81363, 13], [83205], .contexts [
        ⟨19938, true, false, [], [13]⟩,
        ⟨59, false, false, [83205], []⟩,
        ⟨19915, false, false, [], []⟩
      ]⟩,
    ⟨[15119, 83205], [15119, 83205], .contexts []⟩,
    ⟨[15119, 83205], [15119, 83205], .contexts []⟩,
    ⟨[83205, 15], [83205, 15], .contexts []⟩,
    ⟨[83205, 15], [15119, 83205], .contexts [
        ⟨19942, false, false, [], []⟩,
        ⟨19916, true, false, [], [15]⟩,
        ⟨1063, false, false, [83203], []⟩,
        ⟨1064, false, false, [83203], []⟩,
        ⟨19908, false, false, [], [7]⟩,
        ⟨19910, false, false, [], [7]⟩,
        ⟨19906, false, false, [], [7]⟩,
        ⟨19907, false, false, [], [7]⟩,
        ⟨19907, false, false, [], [7]⟩,
        ⟨19912, false, false, [15119], []⟩,
        ⟨19940, false, false, [], []⟩,
        ⟨19941, false, false, [], []⟩,
        ⟨19934, false, false, [15119], []⟩,
        ⟨19909, true, false, [], [83205]⟩
      ]⟩,
    ⟨[83115, 5], [83207], .source 75140⟩,
    ⟨[83207, 5], [83115], .contexts [
        ⟨19944, true, false, [], [5]⟩,
        ⟨28, false, false, [83115], []⟩,
        ⟨18600, false, false, [], []⟩
      ]⟩,
    ⟨[83207], [83207], .contexts []⟩,
    ⟨[83207], [83207], .contexts []⟩,
    ⟨[83115, 5], [83207], .contexts [
        ⟨19944, false, false, [], []⟩,
        ⟨19946, false, false, [], []⟩,
        ⟨19947, false, false, [], []⟩,
        ⟨19947, false, false, [], []⟩
      ]⟩,
    ⟨[15845, 77461], [15845, 77461], .contexts []⟩,
    ⟨[15845, 77461], [15845, 77461], .contexts []⟩,
    ⟨[83115, 7], [15845, 77461], .contexts [
        ⟨18766, false, false, [], []⟩,
        ⟨19949, false, false, [], []⟩,
        ⟨19950, false, false, [], []⟩,
        ⟨19950, false, false, [], []⟩
      ]⟩,
    ⟨[16045], [15845, 469], .source 8087⟩,
    ⟨[16047], [15829, 15839], .source 8088⟩,
    ⟨[16049], [16045, 16047], .source 8089⟩,
    ⟨[16049, 83207], [16049, 83207], .contexts []⟩,
    ⟨[83207], [83207], .source 75141⟩,
    ⟨[83207, 7], [16049, 83207], .contexts [
        ⟨19948, true, false, [], [7]⟩,
        ⟨3272, false, false, [83115], []⟩,
        ⟨3275, false, false, [83115], []⟩,
        ⟨19951, false, false, [], [5, 7, 5]⟩,
        ⟨1515, false, false, [15845], [7, 5]⟩,
        ⟨19952, true, false, [], [77461, 7, 5]⟩,
        ⟨18750, false, false, [16045], [5]⟩,
        ⟨18769, false, false, [16045, 15829], [5]⟩,
        ⟨19953, true, false, [16045], [83115, 5]⟩,
        ⟨19954, true, false, [], [83115, 5]⟩,
        ⟨19944, false, false, [16049], []⟩,
        ⟨19955, false, false, [], []⟩,
        ⟨19956, false, false, [16049], []⟩,
        ⟨13, true, false, [], [16049, 83207]⟩
      ]⟩,
    ⟨[16051], [15847, 15851], .source 8090⟩,
    ⟨[83207, 9], [16051, 83109], .contexts [
        ⟨19948, true, false, [], [9]⟩,
        ⟨1265, false, false, [83115], []⟩,
        ⟨1266, false, false, [83115], []⟩,
        ⟨18616, false, false, [], [5]⟩,
        ⟨18773, false, false, [], [5]⟩,
        ⟨18772, false, false, [], [5]⟩,
        ⟨18772, false, false, [], [5]⟩,
        ⟨18780, false, false, [15847], []⟩,
        ⟨19958, true, false, [], [83109]⟩,
        ⟨18786, false, false, [16051], []⟩,
        ⟨13, true, false, [], [16051, 83109]⟩
      ]⟩,
    ⟨[16053], [16050], .source 8091⟩,
    ⟨[83109, 9], [16053, 83207], .contexts [
        ⟨19959, true, false, [16050], [9]⟩,
        ⟨46, false, false, [16050, 83207], []⟩,
        ⟨19960, true, false, [], [83207]⟩
      ]⟩,
    ⟨[83115, 11], [15839, 83115], .contexts [
        ⟨18599, false, false, [], []⟩,
        ⟨18769, false, false, [], []⟩,
        ⟨18768, false, false, [], []⟩,
        ⟨18768, false, false, [], []⟩
      ]⟩,
    ⟨[15839, 83115, 5], [15839, 83207], .contexts [
        ⟨19944, false, false, [15839], []⟩
      ]⟩,
    ⟨[15839, 83207], [15839, 83207], .source 75142⟩,
    ⟨[15839, 83207], [15839, 83207], .contexts []⟩,
    ⟨[15839, 83207], [15839, 83207], .source 75143⟩,
    ⟨[15839, 83207], [15839, 83207], .source 75144⟩]

/-- Exact literal claimed equations and contextual derivations, block 312. -/
def y322TCIndexRaw312 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15839, 83207], [15839, 83207], .source 75146⟩,
    ⟨[83207, 11], [15839, 83207], .contexts [
        ⟨19948, true, false, [], [11]⟩,
        ⟨174, false, false, [83115], []⟩,
        ⟨175, false, false, [83115], []⟩,
        ⟨19962, false, false, [], [5]⟩,
        ⟨19963, false, false, [], []⟩,
        ⟨19964, false, false, [], []⟩,
        ⟨19965, false, false, [], []⟩,
        ⟨19966, false, false, [], []⟩,
        ⟨19967, false, false, [], []⟩,
        ⟨19968, false, false, [], []⟩
      ]⟩,
    ⟨[83115, 15], [83209], .source 75148⟩,
    ⟨[83209], [83209], .contexts []⟩,
    ⟨[83209], [83209], .source 75149⟩,
    ⟨[83115, 15], [83209], .contexts [
        ⟨19970, false, false, [], []⟩,
        ⟨19971, false, false, [], []⟩,
        ⟨19972, false, false, [], []⟩,
        ⟨19972, false, false, [], []⟩
      ]⟩,
    ⟨[15843, 82737], [15843, 82737], .contexts []⟩,
    ⟨[15843, 82737], [15843, 82737], .contexts []⟩,
    ⟨[16055], [15843, 15335], .source 8092⟩,
    ⟨[83209, 3], [16055, 81781], .contexts [
        ⟨19973, true, false, [], [3]⟩,
        ⟨19, false, false, [83115], []⟩,
        ⟨22, false, false, [83115], []⟩,
        ⟨18764, false, false, [], [15]⟩,
        ⟨19974, false, false, [], [15]⟩,
        ⟨19975, false, false, [], [15]⟩,
        ⟨19975, false, false, [], [15]⟩,
        ⟨15994, false, false, [15843], []⟩,
        ⟨19976, true, false, [], [81781]⟩,
        ⟨9383, false, false, [16055], []⟩,
        ⟨13, true, false, [], [16055, 81781]⟩
      ]⟩,
    ⟨[16057], [16054], .source 8093⟩,
    ⟨[81781, 3], [16057, 83209], .contexts [
        ⟨19977, true, false, [16054], [3]⟩,
        ⟨20, false, false, [16054, 83209], []⟩,
        ⟨19978, true, false, [], [83209]⟩
      ]⟩,
    ⟨[16059], [15845, 465], .source 8094⟩,
    ⟨[83209, 7], [16059, 77609], .contexts [
        ⟨19973, true, false, [], [7]⟩,
        ⟨37, false, false, [83115], []⟩,
        ⟨40, false, false, [83115], []⟩,
        ⟨19951, false, false, [], [15]⟩,
        ⟨2135, false, false, [15845], []⟩,
        ⟨19980, true, false, [], [77609]⟩,
        ⟨2128, false, false, [16059], []⟩,
        ⟨13, true, false, [], [16059, 77609]⟩
      ]⟩,
    ⟨[16061], [16058], .source 8095⟩,
    ⟨[83115, 9, 15], [15847, 15663, 81773], .source 75150⟩,
    ⟨[16063], [15847, 15663], .source 75151⟩,
    ⟨[83209, 9], [16063, 81773], .contexts [
        ⟨19973, true, false, [], [9]⟩,
        ⟨45, false, false, [83115], []⟩,
        ⟨48, false, false, [83115], []⟩,
        ⟨19983, false, false, [], []⟩,
        ⟨19984, true, false, [], [81773]⟩,
        ⟨9366, false, false, [16063], []⟩,
        ⟨13, true, false, [], [16063, 81773]⟩
      ]⟩,
    ⟨[16065], [16062], .source 75152⟩,
    ⟨[81773, 9], [16065, 83209], .contexts [
        ⟨19985, true, false, [16062], [9]⟩,
        ⟨46, false, false, [16062, 83209], []⟩,
        ⟨19986, true, false, [], [83209]⟩
      ]⟩,
    ⟨[15839, 83209], [15839, 83209], .source 75153⟩,
    ⟨[15839, 83209], [15839, 83209], .source 75154⟩,
    ⟨[83209], [83209], .source 75155⟩,
    ⟨[15839, 83209], [15839, 83209], .source 75156⟩,
    ⟨[15839, 83209], [15839, 83209], .source 75157⟩,
    ⟨[83209, 11], [15839, 83209], .contexts [
        ⟨19973, true, false, [], [11]⟩,
        ⟨52, false, false, [83115], []⟩,
        ⟨55, false, false, [83115], []⟩,
        ⟨19962, false, false, [], [15]⟩,
        ⟨19970, false, false, [15839], []⟩,
        ⟨19988, false, false, [], []⟩,
        ⟨19989, false, false, [], []⟩,
        ⟨19991, false, false, [], []⟩,
        ⟨19992, false, false, [], []⟩
      ]⟩,
    ⟨[83119, 5], [83211], .source 75159⟩,
    ⟨[83211, 5], [83119], .contexts [
        ⟨19994, true, false, [], [5]⟩,
        ⟨28, false, false, [83119], []⟩,
        ⟨18607, false, false, [], []⟩
      ]⟩,
    ⟨[83211], [83211], .source 75160⟩,
    ⟨[83211], [83211], .source 75161⟩,
    ⟨[83119, 5], [83211], .source 75162⟩,
    ⟨[83119, 1], [15839, 83115], .source 75163⟩,
    ⟨[83211, 1], [15839, 83207], .contexts [
        ⟨19998, true, false, [], [1]⟩,
        ⟨161, false, false, [83119], []⟩,
        ⟨162, false, false, [83119], []⟩,
        ⟨19999, false, false, [], [5]⟩,
        ⟨19963, false, false, [], []⟩,
        ⟨19964, false, false, [], []⟩,
        ⟨19965, false, false, [], []⟩,
        ⟨19966, false, false, [], []⟩,
        ⟨19967, false, false, [], []⟩,
        ⟨19968, false, false, [], []⟩
      ]⟩,
    ⟨[83207, 1], [15841, 83211], .contexts [
        ⟨20000, true, false, [15838], [1]⟩,
        ⟨8, false, false, [15838, 83211], []⟩,
        ⟨18760, true, false, [], [83211]⟩
      ]⟩,
    ⟨[83119, 7], [15799, 77465], .contexts [
        ⟨18719, false, false, [], []⟩,
        ⟨18721, false, false, [], []⟩,
        ⟨18717, false, false, [], []⟩,
        ⟨18718, false, false, [], []⟩,
        ⟨18718, false, false, [], []⟩
      ]⟩,
    ⟨[16067], [15799, 463], .source 8098⟩,
    ⟨[16069], [16067, 15801], .source 8099⟩,
    ⟨[16069, 83211], [16069, 83211], .contexts []⟩,
    ⟨[16069, 83211], [16069, 83211], .contexts []⟩,
    ⟨[83211, 7], [83211, 7], .contexts []⟩,
    ⟨[83211], [83211], .contexts []⟩,
    ⟨[16069], [16069], .contexts [
        ⟨13, false, false, [], [16069]⟩
      ]⟩,
    ⟨[83211, 7], [16069, 83211], .contexts [
        ⟨20007, false, false, [], []⟩,
        ⟨19998, true, false, [], [7]⟩,
        ⟨3272, false, false, [83119], []⟩,
        ⟨3275, false, false, [83119], []⟩,
        ⟨20002, false, false, [], [5, 7, 5]⟩,
        ⟨1496, false, false, [15799], [7, 5]⟩,
        ⟨20003, true, false, [], [77465, 7, 5]⟩,
        ⟨18722, false, false, [16067], [5]⟩,
        ⟨20004, true, false, [], [83119, 5]⟩,
        ⟨19994, false, false, [16069], []⟩,
        ⟨20005, false, false, [], []⟩,
        ⟨20006, false, false, [], []⟩,
        ⟨20008, false, false, [16069], []⟩,
        ⟨20009, true, false, [], [83211]⟩
      ]⟩,
    ⟨[83119, 9], [15811, 83119], .contexts [
        ⟨18727, false, false, [], []⟩,
        ⟨18730, false, false, [], []⟩,
        ⟨18725, false, false, [], []⟩,
        ⟨18726, false, false, [], []⟩,
        ⟨18726, false, false, [], []⟩
      ]⟩,
    ⟨[15811, 83211], [15811, 83211], .source 75164⟩,
    ⟨[15811, 83211], [15811, 83211], .source 75165⟩,
    ⟨[83211, 9], [83211, 9], .source 75166⟩,
    ⟨[83211, 9], [15811, 83211], .contexts [
        ⟨20014, false, false, [], []⟩,
        ⟨19998, true, false, [], [9]⟩,
        ⟨1265, false, false, [83119], []⟩,
        ⟨1266, false, false, [83119], []⟩,
        ⟨20011, false, false, [], [5]⟩,
        ⟨19994, false, false, [15811], []⟩,
        ⟨20012, false, false, [], []⟩,
        ⟨20013, false, false, [], []⟩,
        ⟨20008, false, false, [15811], []⟩,
        ⟨18729, true, false, [], [83211]⟩
      ]⟩,
    ⟨[83119, 11], [15817, 83119], .contexts [
        ⟨18736, false, false, [], []⟩,
        ⟨18738, false, false, [], []⟩,
        ⟨18734, false, false, [], []⟩,
        ⟨18735, false, false, [], []⟩,
        ⟨18735, false, false, [], []⟩
      ]⟩,
    ⟨[15817, 83211], [15817, 83211], .contexts []⟩,
    ⟨[15817, 83211], [15817, 83211], .contexts []⟩,
    ⟨[83211, 11], [83211, 11], .contexts []⟩,
    ⟨[83211, 11], [15817, 83211], .contexts [
        ⟨20019, false, false, [], []⟩,
        ⟨19998, true, false, [], [11]⟩,
        ⟨174, false, false, [83119], []⟩,
        ⟨175, false, false, [83119], []⟩,
        ⟨20016, false, false, [], [5]⟩,
        ⟨19994, false, false, [15817], []⟩,
        ⟨20017, false, false, [], []⟩,
        ⟨20018, false, false, [], []⟩,
        ⟨20008, false, false, [15817], []⟩,
        ⟨18737, true, false, [], [83211]⟩
      ]⟩,
    ⟨[83119, 15], [83213], .source 75168⟩,
    ⟨[83213], [83213], .source 75170⟩,
    ⟨[83119, 15], [83213], .source 75172⟩,
    ⟨[83213, 1], [15839, 83209], .source 75173⟩,
    ⟨[83209, 1], [15841, 83213], .contexts [
        ⟨20024, true, false, [15838], [1]⟩,
        ⟨8, false, false, [15838, 83213], []⟩,
        ⟨18760, true, false, [], [83213]⟩
      ]⟩,
    ⟨[15797, 83213], [15797, 83213], .source 75174⟩,
    ⟨[15797, 83213], [15797, 83213], .source 75175⟩,
    ⟨[83213], [83213], .source 75176⟩,
    ⟨[83213, 3], [15797, 83213], .source 75177⟩,
    ⟨[15799, 77607], [15799, 77607], .contexts []⟩,
    ⟨[83213, 7], [15799, 77607], .contexts [
        ⟨20023, true, false, [], [7]⟩,
        ⟨37, false, false, [83119], []⟩,
        ⟨40, false, false, [83119], []⟩,
        ⟨20002, false, false, [], [15]⟩,
        ⟨2102, false, false, [15799], []⟩,
        ⟨20030, false, false, [], []⟩,
        ⟨2108, false, false, [15799], []⟩,
        ⟨18720, true, false, [], [77607]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 313. -/
def y322TCIndexRaw313 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[15811, 83213], [15811, 83213], .contexts []⟩,
    ⟨[15817, 83213], [15817, 83213], .contexts []⟩,
    ⟨[83123], [15785, 83121], .contexts [
        ⟨18678, false, false, [], []⟩
      ]⟩,
    ⟨[15785, 83213], [15785, 83213], .contexts []⟩,
    ⟨[83213, 13], [15785, 83213], .contexts [
        ⟨20023, true, false, [], [13]⟩,
        ⟨259, false, false, [83119], []⟩,
        ⟨262, false, false, [83119], []⟩,
        ⟨18606, false, false, [], [15, 13, 15]⟩,
        ⟨18669, false, false, [], [15, 13, 15]⟩,
        ⟨18610, false, false, [], [15, 13, 15]⟩,
        ⟨18610, false, false, [], [15, 13, 15]⟩,
        ⟨18611, false, false, [], [13, 15]⟩,
        ⟨20034, false, false, [], [13, 15]⟩,
        ⟨18677, false, false, [], [13, 15]⟩,
        ⟨18677, false, false, [], [13, 15]⟩,
        ⟨18608, false, false, [15785], [15]⟩,
        ⟨20021, false, false, [15785], []⟩,
        ⟨20035, false, false, [], []⟩,
        ⟨20028, false, false, [15785], []⟩
      ]⟩,
    ⟨[15785], [15785], .contexts [
        ⟨13, false, false, [], [15785]⟩
      ]⟩,
    ⟨[83213, 13], [15785, 83213], .contexts [
        ⟨20036, false, false, [], []⟩,
        ⟨20037, true, false, [], [83213]⟩
      ]⟩,
    ⟨[83215], [83121, 5], .source 41672⟩,
    ⟨[83121, 5], [83215], .contexts [
        ⟨20039, true, false, [], []⟩
      ]⟩,
    ⟨[83215, 5], [83121], .contexts [
        ⟨20040, true, false, [], [5]⟩,
        ⟨28, false, false, [83121], []⟩,
        ⟨18610, false, false, [], []⟩
      ]⟩,
    ⟨[83215], [83215], .contexts []⟩,
    ⟨[83215], [83215], .contexts []⟩,
    ⟨[83121, 5], [83215], .contexts [
        ⟨20040, false, false, [], []⟩,
        ⟨20042, false, false, [], []⟩,
        ⟨20043, false, false, [], []⟩,
        ⟨20043, false, false, [], []⟩
      ]⟩,
    ⟨[16071], [15799, 455], .source 8100⟩,
    ⟨[16073], [16071, 15801], .source 8101⟩,
    ⟨[16073, 83215], [16073, 83215], .contexts []⟩,
    ⟨[83215], [83215], .contexts []⟩,
    ⟨[83215, 7], [16073, 83215], .contexts [
        ⟨20044, true, false, [], [7]⟩,
        ⟨3272, false, false, [83121], []⟩,
        ⟨3275, false, false, [83121], []⟩,
        ⟨18716, false, false, [], [5, 7, 5]⟩,
        ⟨1483, false, false, [15799], [7, 5]⟩,
        ⟨20045, true, false, [], [77467, 7, 5]⟩,
        ⟨18690, false, false, [16071], [5]⟩,
        ⟨20046, true, false, [], [83121, 5]⟩,
        ⟨20040, false, false, [16073], []⟩,
        ⟨20047, false, false, [], []⟩,
        ⟨20048, false, false, [16073], []⟩,
        ⟨13, true, false, [], [16073, 83215]⟩
      ]⟩,
    ⟨[15811, 83215], [15811, 83215], .contexts []⟩,
    ⟨[83215, 9], [15811, 83215], .contexts [
        ⟨20044, true, false, [], [9]⟩,
        ⟨1265, false, false, [83121], []⟩,
        ⟨1266, false, false, [83121], []⟩,
        ⟨18693, false, false, [], [5]⟩,
        ⟨18696, false, false, [], [5]⟩,
        ⟨18723, false, false, [], [5]⟩,
        ⟨18724, false, false, [], [5]⟩,
        ⟨18724, false, false, [], [5]⟩,
        ⟨20040, false, false, [15811], []⟩,
        ⟨20050, false, false, [], []⟩,
        ⟨20048, false, false, [15811], []⟩,
        ⟨18729, true, false, [], [83215]⟩
      ]⟩,
    ⟨[15817, 83215], [15817, 83215], .contexts []⟩,
    ⟨[83215, 11], [15817, 83215], .contexts [
        ⟨20044, true, false, [], [11]⟩,
        ⟨174, false, false, [83121], []⟩,
        ⟨175, false, false, [83121], []⟩,
        ⟨18733, false, false, [], [5]⟩,
        ⟨20040, false, false, [15817], []⟩,
        ⟨20052, false, false, [], []⟩,
        ⟨20048, false, false, [15817], []⟩,
        ⟨18737, true, false, [], [83215]⟩
      ]⟩,
    ⟨[83215, 13], [83215, 13], .contexts []⟩,
    ⟨[83215, 13], [83211], .contexts [
        ⟨20054, false, false, [], []⟩,
        ⟨20044, true, false, [], [13]⟩,
        ⟨179, false, false, [83121], []⟩,
        ⟨180, false, false, [83121], []⟩,
        ⟨18613, false, false, [], [5]⟩,
        ⟨19994, false, false, [], []⟩,
        ⟨19996, false, false, [], []⟩,
        ⟨19997, false, false, [], []⟩,
        ⟨19997, false, false, [], []⟩,
        ⟨20008, false, false, [], []⟩,
        ⟨672, true, false, [], [83211]⟩
      ]⟩,
    ⟨[83211, 13], [83215], .contexts [
        ⟨20055, true, false, [], [13]⟩,
        ⟨59, false, false, [83215], []⟩,
        ⟨20043, false, false, [], []⟩
      ]⟩,
    ⟨[15785, 83215], [15785, 83215], .contexts []⟩,
    ⟨[15785, 83215], [15785, 83215], .contexts []⟩,
    ⟨[83215, 15], [15785, 83215], .contexts [
        ⟨20044, true, false, [], [15]⟩,
        ⟨184, false, false, [83121], []⟩,
        ⟨185, false, false, [83121], []⟩,
        ⟨18611, false, false, [], [5]⟩,
        ⟨20034, false, false, [], [5]⟩,
        ⟨18677, false, false, [], [5]⟩,
        ⟨18677, false, false, [], [5]⟩,
        ⟨20040, false, false, [15785], []⟩,
        ⟨20057, false, false, [], []⟩,
        ⟨20058, false, false, [], []⟩,
        ⟨20048, false, false, [15785], []⟩,
        ⟨20037, true, false, [], [83215]⟩
      ]⟩,
    ⟨[83217], [82749, 5], .source 41673⟩,
    ⟨[82749, 5], [83217], .contexts [
        ⟨20060, true, false, [], []⟩
      ]⟩,
    ⟨[83217, 5], [82749], .contexts [
        ⟨20061, true, false, [], [5]⟩,
        ⟨28, false, false, [82749], []⟩,
        ⟨16139, false, false, [], []⟩
      ]⟩,
    ⟨[83217], [83217], .contexts []⟩,
    ⟨[83217], [83217], .contexts []⟩,
    ⟨[82749, 5], [83217], .contexts [
        ⟨20061, false, false, [], []⟩,
        ⟨20063, false, false, [], []⟩,
        ⟨20064, false, false, [], []⟩,
        ⟨20064, false, false, [], []⟩
      ]⟩,
    ⟨[15793, 83215], [15793, 83215], .contexts []⟩,
    ⟨[83217, 1], [15793, 83215], .contexts [
        ⟨20065, true, false, [], [1]⟩,
        ⟨161, false, false, [82749], []⟩,
        ⟨162, false, false, [82749], []⟩,
        ⟨18672, false, false, [], [5]⟩,
        ⟨18678, false, false, [15779], [5]⟩,
        ⟨18679, true, false, [], [83121, 5]⟩,
        ⟨20040, false, false, [15793], []⟩,
        ⟨20066, false, false, [], []⟩,
        ⟨20048, false, false, [15793], []⟩,
        ⟨13, true, false, [], [15793, 83215]⟩
      ]⟩,
    ⟨[16075], [15792], .source 8102⟩,
    ⟨[83215, 1], [16075, 83217], .contexts [
        ⟨20067, true, false, [15792], [1]⟩,
        ⟨8, false, false, [15792, 83217], []⟩,
        ⟨20068, true, false, [], [83217]⟩
      ]⟩,
    ⟨[16077], [397, 759], .source 8103⟩,
    ⟨[16079], [16077, 399], .source 8104⟩,
    ⟨[16079, 83217], [16079, 83217], .contexts []⟩,
    ⟨[83217], [83217], .contexts []⟩,
    ⟨[83217, 3], [16079, 83217], .contexts [
        ⟨20065, true, false, [], [3]⟩,
        ⟨166, false, false, [82749], []⟩,
        ⟨169, false, false, [82749], []⟩,
        ⟨16143, false, false, [], [5, 3, 5]⟩,
        ⟨16141, false, false, [], [5, 3, 5]⟩,
        ⟨16142, false, false, [], [5, 3, 5]⟩,
        ⟨16142, false, false, [], [5, 3, 5]⟩,
        ⟨2340, false, false, [397], [3, 5]⟩,
        ⟨20070, true, false, [], [77715, 3, 5]⟩,
        ⟨16144, false, false, [16077], [5]⟩,
        ⟨20071, true, false, [], [82749, 5]⟩,
        ⟨20061, false, false, [16079], []⟩,
        ⟨20072, false, false, [], []⟩,
        ⟨20073, false, false, [16079], []⟩
      ]⟩,
    ⟨[83217, 3], [16079, 83217], .contexts [
        ⟨20074, false, false, [], []⟩,
        ⟨13, true, false, [], [16079, 83217]⟩
      ]⟩,
    ⟨[427, 83217], [427, 83217], .contexts []⟩,
    ⟨[83217, 7], [427, 83217], .contexts [
        ⟨20065, true, false, [], [7]⟩,
        ⟨3272, false, false, [82749], []⟩,
        ⟨3275, false, false, [82749], []⟩,
        ⟨16137, false, false, [], [5, 7, 5]⟩,
        ⟨1405, false, false, [], [5, 7, 5]⟩,
        ⟨1401, false, false, [], [5, 7, 5]⟩,
        ⟨1401, false, false, [], [5, 7, 5]⟩,
        ⟨1470, false, false, [], [7, 5]⟩,
        ⟨1474, false, false, [], [7, 5]⟩,
        ⟨1475, false, false, [], [7, 5]⟩,
        ⟨1475, false, false, [], [7, 5]⟩,
        ⟨16136, false, false, [427], [5]⟩,
        ⟨20061, false, false, [427], []⟩,
        ⟨20076, false, false, [], []⟩,
        ⟨20073, false, false, [427], []⟩
      ]⟩,
    ⟨[509, 82983], [509, 82983], .contexts []⟩,
    ⟨[83217, 9], [509, 82983], .contexts [
        ⟨20065, true, false, [], [9]⟩,
        ⟨1265, false, false, [82749], []⟩,
        ⟨1266, false, false, [82749], []⟩,
        ⟨16147, false, false, [], [5]⟩,
        ⟨16145, false, false, [], [5]⟩,
        ⟨16146, false, false, [], [5]⟩,
        ⟨16146, false, false, [], [5]⟩,
        ⟨18209, false, false, [509], []⟩,
        ⟨20078, false, false, [], []⟩,
        ⟨18201, false, false, [509], []⟩,
        ⟨13, true, false, [], [509, 82983]⟩
      ]⟩,
    ⟨[82983, 9], [507, 83217], .contexts [
        ⟨20079, true, false, [508], [9]⟩,
        ⟨46, false, false, [508, 83217], []⟩,
        ⟨1614, true, false, [], [83217]⟩
      ]⟩,
    ⟨[445, 83217], [445, 83217], .contexts []⟩,
    ⟨[83217, 11], [445, 83217], .contexts [
        ⟨20065, true, false, [], [11]⟩,
        ⟨174, false, false, [82749], []⟩,
        ⟨175, false, false, [82749], []⟩,
        ⟨16151, false, false, [], [5]⟩,
        ⟨16154, false, false, [], [5]⟩,
        ⟨16149, false, false, [], [5]⟩,
        ⟨16150, false, false, [], [5]⟩,
        ⟨16150, false, false, [], [5]⟩,
        ⟨20061, false, false, [445], []⟩,
        ⟨20081, false, false, [], []⟩,
        ⟨20073, false, false, [445], []⟩,
        ⟨16153, true, false, [], [83217]⟩
      ]⟩,
    ⟨[439, 83217], [439, 83217], .contexts []⟩,
    ⟨[83211, 15], [83219], .source 75179⟩,
    ⟨[83219, 15], [83211], .contexts [
        ⟨20084, true, false, [], [15]⟩,
        ⟨1, false, false, [83211], []⟩,
        ⟨19997, false, false, [], []⟩
      ]⟩,
    ⟨[83219], [83219], .contexts []⟩,
    ⟨[83219], [83219], .source 75180⟩,
    ⟨[83211, 15], [83219], .source 75181⟩,
    ⟨[83219, 5], [83213], .source 75183⟩,
    ⟨[83213, 5], [83219], .contexts [
        ⟨20089, true, false, [], [5]⟩,
        ⟨28, false, false, [83219], []⟩,
        ⟨20087, false, false, [], []⟩
      ]⟩,
    ⟨[16069, 83219], [16069, 83219], .contexts []⟩,
    ⟨[16069, 83219], [16069, 83219], .contexts []⟩,
    ⟨[83219, 7], [83219, 7], .contexts []⟩,
    ⟨[83219], [83219], .contexts []⟩,
    ⟨[83219, 7], [16069, 83219], .contexts [
        ⟨20093, false, false, [], []⟩,
        ⟨20088, true, false, [], [7]⟩,
        ⟨37, false, false, [83211], []⟩,
        ⟨40, false, false, [83211], []⟩,
        ⟨20007, false, false, [], [15]⟩,
        ⟨20010, false, false, [], [15]⟩,
        ⟨20005, false, false, [], [15]⟩,
        ⟨20006, false, false, [], [15]⟩,
        ⟨20006, false, false, [], [15]⟩,
        ⟨20084, false, false, [16069], []⟩,
        ⟨20091, false, false, [], []⟩,
        ⟨20092, false, false, [], []⟩,
        ⟨20094, false, false, [16069], []⟩,
        ⟨20009, true, false, [], [83219]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 314. -/
def y322TCIndexRaw314 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83211, 9, 15], [15811, 83211, 15], .source 75184⟩,
    ⟨[15811, 83219], [15811, 83219], .source 75185⟩,
    ⟨[15811, 83219], [15811, 83219], .source 75186⟩,
    ⟨[83219, 9], [83219, 9], .source 75187⟩,
    ⟨[83219, 9], [15811, 83219], .contexts [
        ⟨20099, false, false, [], []⟩,
        ⟨20088, true, false, [], [9]⟩,
        ⟨45, false, false, [83211], []⟩,
        ⟨48, false, false, [83211], []⟩,
        ⟨20096, false, false, [], []⟩,
        ⟨20084, false, false, [15811], []⟩,
        ⟨20097, false, false, [], []⟩,
        ⟨20098, false, false, [], []⟩,
        ⟨20094, false, false, [15811], []⟩,
        ⟨18729, true, false, [], [83219]⟩
      ]⟩,
    ⟨[15817, 83219], [15817, 83219], .contexts []⟩,
    ⟨[15817, 83219], [15817, 83219], .contexts []⟩,
    ⟨[83219, 11], [83219, 11], .contexts []⟩,
    ⟨[83219, 11], [15817, 83219], .contexts [
        ⟨20103, false, false, [], []⟩,
        ⟨20088, true, false, [], [11]⟩,
        ⟨52, false, false, [83211], []⟩,
        ⟨55, false, false, [83211], []⟩,
        ⟨20019, false, false, [], [15]⟩,
        ⟨20020, false, false, [], [15]⟩,
        ⟨20017, false, false, [], [15]⟩,
        ⟨20018, false, false, [], [15]⟩,
        ⟨20018, false, false, [], [15]⟩,
        ⟨20084, false, false, [15817], []⟩,
        ⟨20101, false, false, [], []⟩,
        ⟨20102, false, false, [], []⟩,
        ⟨20094, false, false, [15817], []⟩,
        ⟨18737, true, false, [], [83219]⟩
      ]⟩,
    ⟨[83211, 13], [83215], .contexts [
        ⟨20056, false, false, [], []⟩
      ]⟩,
    ⟨[15785, 83219], [15785, 83219], .contexts []⟩,
    ⟨[15785, 83219], [15785, 83219], .contexts []⟩,
    ⟨[83219, 13], [83219, 13], .contexts []⟩,
    ⟨[83219, 13], [15785, 83219], .contexts [
        ⟨20108, false, false, [], []⟩,
        ⟨20088, true, false, [], [13]⟩,
        ⟨259, false, false, [83211], []⟩,
        ⟨262, false, false, [83211], []⟩,
        ⟨20105, false, false, [], [15, 13, 15]⟩,
        ⟨20042, false, false, [], [15, 13, 15]⟩,
        ⟨20043, false, false, [], [15, 13, 15]⟩,
        ⟨20043, false, false, [], [15, 13, 15]⟩,
        ⟨20059, false, false, [], [13, 15]⟩,
        ⟨20057, false, false, [], [13, 15]⟩,
        ⟨20058, false, false, [], [13, 15]⟩,
        ⟨20058, false, false, [], [13, 15]⟩,
        ⟨20055, false, false, [15785], [15]⟩,
        ⟨20084, false, false, [15785], []⟩,
        ⟨20106, false, false, [], []⟩,
        ⟨20107, false, false, [], []⟩,
        ⟨20094, false, false, [15785], []⟩
      ]⟩,
    ⟨[83219, 13], [15785, 83219], .contexts [
        ⟨20109, false, false, [], []⟩,
        ⟨20037, true, false, [], [83219]⟩
      ]⟩,
    ⟨[83219, 1], [83221], .source 75189⟩,
    ⟨[83221, 1], [83219], .contexts [
        ⟨20111, true, false, [], [1]⟩,
        ⟨8, false, false, [83219], []⟩,
        ⟨20087, false, false, [], []⟩
      ]⟩,
    ⟨[83221], [83221], .contexts []⟩,
    ⟨[83221], [83221], .source 75190⟩,
    ⟨[83219, 1], [83221], .source 75191⟩,
    ⟨[83219, 5], [83213], .source 75192⟩,
    ⟨[83221, 5], [15839, 83209], .contexts [
        ⟨20115, true, false, [], [5]⟩,
        ⟨98, false, false, [83219], []⟩,
        ⟨99, false, false, [83219], []⟩,
        ⟨20116, false, false, [], [1]⟩,
        ⟨20024, false, false, [], []⟩,
        ⟨19988, false, false, [], []⟩,
        ⟨19989, false, false, [], []⟩,
        ⟨19989, false, false, [], []⟩,
        ⟨19991, false, false, [], []⟩,
        ⟨19992, false, false, [], []⟩
      ]⟩,
    ⟨[15838, 83221], [15841, 83221], .contexts [
        ⟨18760, true, false, [], [83221]⟩
      ]⟩,
    ⟨[83209, 5], [15841, 83221], .contexts [
        ⟨20117, true, false, [15838], [5]⟩,
        ⟨28, false, false, [15838, 83221], []⟩,
        ⟨20118, false, false, [], []⟩
      ]⟩,
    ⟨[83219, 7], [16069, 83219], .contexts [
        ⟨20093, false, false, [], []⟩,
        ⟨20095, false, false, [], []⟩,
        ⟨20091, false, false, [], []⟩,
        ⟨20092, false, false, [], []⟩,
        ⟨20092, false, false, [], []⟩
      ]⟩,
    ⟨[16069, 83221], [16069, 83221], .contexts []⟩,
    ⟨[16069, 83221], [16069, 83221], .contexts []⟩,
    ⟨[83221, 7], [83221, 7], .contexts []⟩,
    ⟨[83221], [83221], .contexts []⟩,
    ⟨[83221, 7], [16069, 83221], .contexts [
        ⟨20123, false, false, [], []⟩,
        ⟨20115, true, false, [], [7]⟩,
        ⟨104, false, false, [83219], []⟩,
        ⟨105, false, false, [83219], []⟩,
        ⟨20120, false, false, [], [1]⟩,
        ⟨20111, false, false, [16069], []⟩,
        ⟨20121, false, false, [], []⟩,
        ⟨20122, false, false, [], []⟩,
        ⟨20124, false, false, [16069], []⟩,
        ⟨20009, true, false, [], [83221]⟩
      ]⟩,
    ⟨[83219, 11], [15817, 83219], .contexts [
        ⟨20103, false, false, [], []⟩,
        ⟨20104, false, false, [], []⟩,
        ⟨20101, false, false, [], []⟩,
        ⟨20102, false, false, [], []⟩,
        ⟨20102, false, false, [], []⟩
      ]⟩,
    ⟨[15817, 83221], [15817, 83221], .contexts []⟩,
    ⟨[15817, 83221], [15817, 83221], .contexts []⟩,
    ⟨[83221, 11], [83221, 11], .contexts []⟩,
    ⟨[83221, 11], [15817, 83221], .contexts [
        ⟨20129, false, false, [], []⟩,
        ⟨20115, true, false, [], [11]⟩,
        ⟨110, false, false, [83219], []⟩,
        ⟨111, false, false, [83219], []⟩,
        ⟨20126, false, false, [], [1]⟩,
        ⟨20111, false, false, [15817], []⟩,
        ⟨20127, false, false, [], []⟩,
        ⟨20128, false, false, [], []⟩,
        ⟨20124, false, false, [15817], []⟩,
        ⟨18737, true, false, [], [83221]⟩
      ]⟩,
    ⟨[83219, 15], [83211], .contexts [
        ⟨20085, false, false, [], []⟩
      ]⟩,
    ⟨[83221, 15], [15839, 83207], .contexts [
        ⟨20115, true, false, [], [15]⟩,
        ⟨121, false, false, [83219], []⟩,
        ⟨122, false, false, [83219], []⟩,
        ⟨20131, false, false, [], [1]⟩,
        ⟨19996, false, false, [], [1]⟩,
        ⟨19997, false, false, [], [1]⟩,
        ⟨19997, false, false, [], [1]⟩,
        ⟨20000, false, false, [], []⟩,
        ⟨19964, false, false, [], []⟩,
        ⟨19966, false, false, [], []⟩,
        ⟨19966, false, false, [], []⟩,
        ⟨19967, false, false, [], []⟩,
        ⟨19968, false, false, [], []⟩
      ]⟩,
    ⟨[83207, 15], [15841, 83221], .contexts [
        ⟨20132, true, false, [15838], [15]⟩,
        ⟨1, false, false, [15838, 83221], []⟩,
        ⟨20118, false, false, [], []⟩
      ]⟩,
    ⟨[83223], [83221, 3], .source 41676⟩,
    ⟨[83221, 3], [83223], .contexts [
        ⟨20134, true, false, [], []⟩
      ]⟩,
    ⟨[83223, 3], [83221], .contexts [
        ⟨20135, true, false, [], [3]⟩,
        ⟨20, false, false, [83221], []⟩,
        ⟨20114, false, false, [], []⟩
      ]⟩,
    ⟨[83223], [83223], .contexts []⟩,
    ⟨[83223], [83223], .contexts []⟩,
    ⟨[83221, 3], [83223], .contexts [
        ⟨20135, false, false, [], []⟩,
        ⟨20137, false, false, [], []⟩,
        ⟨20138, false, false, [], []⟩,
        ⟨20138, false, false, [], []⟩
      ]⟩,
    ⟨[16069, 83223], [16069, 83223], .contexts []⟩,
    ⟨[83223], [83223], .contexts []⟩,
    ⟨[15817, 83223], [15817, 83223], .contexts []⟩,
    ⟨[15817, 83223], [15817, 83223], .contexts []⟩,
    ⟨[83223, 11], [83223, 11], .contexts []⟩,
    ⟨[83223, 11], [15817, 83223], .contexts [
        ⟨20144, false, false, [], []⟩,
        ⟨20139, true, false, [], [11]⟩,
        ⟨144, false, false, [83221], []⟩,
        ⟨145, false, false, [83221], []⟩,
        ⟨20129, false, false, [], [3]⟩,
        ⟨20130, false, false, [], [3]⟩,
        ⟨20127, false, false, [], [3]⟩,
        ⟨20128, false, false, [], [3]⟩,
        ⟨20128, false, false, [], [3]⟩,
        ⟨20135, false, false, [15817], []⟩,
        ⟨20142, false, false, [], []⟩,
        ⟨20143, false, false, [], []⟩,
        ⟨20141, false, false, [15817], []⟩,
        ⟨18737, true, false, [], [83223]⟩
      ]⟩,
    ⟨[83225], [83223, 5], .source 41677⟩,
    ⟨[83223, 5], [83225], .contexts [
        ⟨20146, true, false, [], []⟩
      ]⟩,
    ⟨[83225, 5], [83223], .contexts [
        ⟨20147, true, false, [], [5]⟩,
        ⟨28, false, false, [83223], []⟩,
        ⟨20138, false, false, [], []⟩
      ]⟩,
    ⟨[83225], [83225], .contexts []⟩,
    ⟨[83225], [83225], .contexts []⟩,
    ⟨[15817, 83225], [15817, 83225], .contexts []⟩,
    ⟨[15817, 83225], [15817, 83225], .contexts []⟩,
    ⟨[83225, 11], [83225, 11], .contexts []⟩,
    ⟨[83225], [83225], .contexts []⟩,
    ⟨[83225, 11], [15817, 83225], .contexts [
        ⟨20153, false, false, [], []⟩,
        ⟨20150, true, false, [], [11]⟩,
        ⟨20150, true, false, [], [11]⟩,
        ⟨20149, true, false, [], [11]⟩,
        ⟨20147, true, false, [], [11]⟩,
        ⟨174, false, false, [83223], []⟩,
        ⟨175, false, false, [83223], []⟩,
        ⟨20144, false, false, [], [5]⟩,
        ⟨20145, false, false, [], [5]⟩,
        ⟨20142, false, false, [], [5]⟩,
        ⟨20143, false, false, [], [5]⟩,
        ⟨20143, false, false, [], [5]⟩,
        ⟨20147, false, false, [15817], []⟩,
        ⟨20151, false, false, [], []⟩,
        ⟨20152, false, false, [], []⟩,
        ⟨20154, false, false, [15817], []⟩,
        ⟨18737, true, false, [], [83225]⟩
      ]⟩,
    ⟨[83227], [83225, 1], .source 41678⟩,
    ⟨[83225, 1], [83227], .contexts [
        ⟨20156, true, false, [], []⟩
      ]⟩,
    ⟨[83227, 1], [83225], .contexts [
        ⟨20157, true, false, [], [1]⟩,
        ⟨8, false, false, [83225], []⟩,
        ⟨20150, false, false, [], []⟩
      ]⟩,
    ⟨[83227], [83227], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 315. -/
def y322TCIndexRaw315 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83227], [83227], .contexts []⟩,
    ⟨[83225, 1], [83227], .contexts [
        ⟨20157, false, false, [], []⟩,
        ⟨20159, false, false, [], []⟩,
        ⟨20160, false, false, [], []⟩,
        ⟨20160, false, false, [], []⟩
      ]⟩,
    ⟨[15817, 83227], [15817, 83227], .contexts []⟩,
    ⟨[15817, 83227], [15817, 83227], .contexts []⟩,
    ⟨[83227], [83227], .contexts []⟩,
    ⟨[83227, 11], [15817, 83227], .contexts [
        ⟨20161, true, false, [], [11]⟩,
        ⟨110, false, false, [83225], []⟩,
        ⟨111, false, false, [83225], []⟩,
        ⟨20153, false, false, [], [1]⟩,
        ⟨20155, false, false, [], [1]⟩,
        ⟨20151, false, false, [], [1]⟩,
        ⟨20152, false, false, [], [1]⟩,
        ⟨20152, false, false, [], [1]⟩,
        ⟨20157, false, false, [15817], []⟩,
        ⟨20162, false, false, [], []⟩,
        ⟨20163, false, false, [], []⟩,
        ⟨20164, false, false, [15817], []⟩,
        ⟨18737, true, false, [], [83227]⟩
      ]⟩,
    ⟨[83229], [83227, 9], .source 41679⟩,
    ⟨[83227, 9], [83229], .contexts [
        ⟨20166, true, false, [], []⟩
      ]⟩,
    ⟨[83229, 9], [83227], .contexts [
        ⟨20167, true, false, [], [9]⟩,
        ⟨46, false, false, [83227], []⟩,
        ⟨20160, false, false, [], []⟩
      ]⟩,
    ⟨[83231], [83229, 11], .source 41680⟩,
    ⟨[83229, 11], [83231], .contexts [
        ⟨20169, true, false, [], []⟩
      ]⟩,
    ⟨[83229], [83229], .contexts []⟩,
    ⟨[83231, 11], [83229], .contexts [
        ⟨20170, true, false, [], [11]⟩,
        ⟨53, false, false, [83229], []⟩,
        ⟨20171, false, false, [], []⟩
      ]⟩,
    ⟨[83231], [83231], .contexts []⟩,
    ⟨[83231], [83231], .contexts []⟩,
    ⟨[83229, 11], [83231], .contexts [
        ⟨20170, false, false, [], []⟩,
        ⟨20173, false, false, [], []⟩,
        ⟨20174, false, false, [], []⟩,
        ⟨20174, false, false, [], []⟩
      ]⟩,
    ⟨[83229, 9], [83227], .contexts [
        ⟨20168, false, false, [], []⟩
      ]⟩,
    ⟨[15817, 83231], [15817, 83231], .contexts []⟩,
    ⟨[83231], [83231], .contexts []⟩,
    ⟨[83231, 9], [15817, 83231], .contexts [
        ⟨20175, true, false, [], [9]⟩,
        ⟨221, false, false, [83229], []⟩,
        ⟨224, false, false, [83229], []⟩,
        ⟨20176, false, false, [], [11, 9, 11]⟩,
        ⟨20159, false, false, [], [11, 9, 11]⟩,
        ⟨20160, false, false, [], [11, 9, 11]⟩,
        ⟨20160, false, false, [], [11, 9, 11]⟩,
        ⟨20165, false, false, [], [9, 11]⟩,
        ⟨20162, false, false, [], [9, 11]⟩,
        ⟨20163, false, false, [], [9, 11]⟩,
        ⟨20163, false, false, [], [9, 11]⟩,
        ⟨20167, false, false, [15817], [11]⟩,
        ⟨20170, false, false, [15817], []⟩,
        ⟨20177, false, false, [], []⟩,
        ⟨20178, false, false, [15817], []⟩
      ]⟩,
    ⟨[83231, 9], [15817, 83231], .contexts [
        ⟨20179, false, false, [], []⟩,
        ⟨18737, true, false, [], [83231]⟩
      ]⟩,
    ⟨[83233], [83231, 1], .source 41681⟩,
    ⟨[83231, 1], [83233], .contexts [
        ⟨20181, true, false, [], []⟩
      ]⟩,
    ⟨[83233, 1], [83231], .contexts [
        ⟨20182, true, false, [], [1]⟩,
        ⟨8, false, false, [83231], []⟩,
        ⟨20174, false, false, [], []⟩
      ]⟩,
    ⟨[83235], [83233, 13], .source 41682⟩,
    ⟨[83233, 13], [83235], .contexts [
        ⟨20184, true, false, [], []⟩
      ]⟩,
    ⟨[83233], [83233], .contexts []⟩,
    ⟨[83235, 13], [83233], .contexts [
        ⟨20185, true, false, [], [13]⟩,
        ⟨59, false, false, [83233], []⟩,
        ⟨20186, false, false, [], []⟩
      ]⟩,
    ⟨[83237], [83235, 15], .source 41683⟩,
    ⟨[83235, 15], [83237], .contexts [
        ⟨20188, true, false, [], []⟩
      ]⟩,
    ⟨[83235], [83235], .contexts []⟩,
    ⟨[83237, 15], [83235], .contexts [
        ⟨20189, true, false, [], [15]⟩,
        ⟨1, false, false, [83235], []⟩,
        ⟨20190, false, false, [], []⟩
      ]⟩,
    ⟨[83239], [83237, 1], .source 41684⟩,
    ⟨[83237, 1], [83239], .contexts [
        ⟨20192, true, false, [], []⟩
      ]⟩,
    ⟨[83237], [83237], .contexts []⟩,
    ⟨[83239, 1], [83237], .contexts [
        ⟨20193, true, false, [], [1]⟩,
        ⟨8, false, false, [83237], []⟩,
        ⟨20194, false, false, [], []⟩
      ]⟩,
    ⟨[83241], [83239, 3], .source 41685⟩,
    ⟨[83239, 3], [83241], .contexts [
        ⟨20196, true, false, [], []⟩
      ]⟩,
    ⟨[83239], [83239], .contexts []⟩,
    ⟨[83241, 3], [83239], .contexts [
        ⟨20197, true, false, [], [3]⟩,
        ⟨20, false, false, [83239], []⟩,
        ⟨20198, false, false, [], []⟩
      ]⟩,
    ⟨[83243], [83241, 5], .source 41686⟩,
    ⟨[83241, 5], [83243], .contexts [
        ⟨20200, true, false, [], []⟩
      ]⟩,
    ⟨[83241], [83241], .contexts []⟩,
    ⟨[83243, 5], [83241], .contexts [
        ⟨20201, true, false, [], [5]⟩,
        ⟨28, false, false, [83241], []⟩,
        ⟨20202, false, false, [], []⟩
      ]⟩,
    ⟨[83245], [83243, 1], .source 41687⟩,
    ⟨[83243, 1], [83245], .contexts [
        ⟨20204, true, false, [], []⟩
      ]⟩,
    ⟨[83243], [83243], .contexts []⟩,
    ⟨[83245, 1], [83243], .contexts [
        ⟨20205, true, false, [], [1]⟩,
        ⟨8, false, false, [83243], []⟩,
        ⟨20206, false, false, [], []⟩
      ]⟩,
    ⟨[83247], [83245, 9], .source 41688⟩,
    ⟨[83245, 9], [83247], .contexts [
        ⟨20208, true, false, [], []⟩
      ]⟩,
    ⟨[83245], [83245], .contexts []⟩,
    ⟨[83247, 9], [83245], .contexts [
        ⟨20209, true, false, [], [9]⟩,
        ⟨46, false, false, [83245], []⟩,
        ⟨20210, false, false, [], []⟩
      ]⟩,
    ⟨[83249], [83247, 11], .source 41689⟩,
    ⟨[83247, 11], [83249], .contexts [
        ⟨20212, true, false, [], []⟩
      ]⟩,
    ⟨[83247], [83247], .contexts []⟩,
    ⟨[83249, 11], [83247], .contexts [
        ⟨20213, true, false, [], [11]⟩,
        ⟨53, false, false, [83247], []⟩,
        ⟨20214, false, false, [], []⟩
      ]⟩,
    ⟨[83251], [83249, 1], .source 41690⟩,
    ⟨[83249, 1], [83251], .contexts [
        ⟨20216, true, false, [], []⟩
      ]⟩,
    ⟨[83249], [83249], .contexts []⟩,
    ⟨[83251, 1], [83249], .contexts [
        ⟨20217, true, false, [], [1]⟩,
        ⟨8, false, false, [83249], []⟩,
        ⟨20218, false, false, [], []⟩
      ]⟩,
    ⟨[83253], [83251, 13], .source 41691⟩,
    ⟨[83251, 13], [83253], .contexts [
        ⟨20220, true, false, [], []⟩
      ]⟩,
    ⟨[83251], [83251], .contexts []⟩,
    ⟨[83255], [83253, 15], .source 41692⟩]

/-- Exact literal claimed equations and contextual derivations, block 316. -/
def y322TCIndexRaw316 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83253, 15], [83255], .contexts [
        ⟨20223, true, false, [], []⟩
      ]⟩,
    ⟨[83253], [83253], .contexts []⟩,
    ⟨[83255, 15], [83253], .contexts [
        ⟨20224, true, false, [], [15]⟩,
        ⟨1, false, false, [83253], []⟩,
        ⟨20225, false, false, [], []⟩
      ]⟩,
    ⟨[83257], [83255, 1], .source 41693⟩,
    ⟨[83255, 1], [83257], .contexts [
        ⟨20227, true, false, [], []⟩
      ]⟩,
    ⟨[83255], [83255], .contexts []⟩,
    ⟨[83257, 1], [83255], .contexts [
        ⟨20228, true, false, [], [1]⟩,
        ⟨8, false, false, [83255], []⟩,
        ⟨20229, false, false, [], []⟩
      ]⟩,
    ⟨[83259], [83257, 3], .source 41694⟩,
    ⟨[83257, 3], [83259], .contexts [
        ⟨20231, true, false, [], []⟩
      ]⟩,
    ⟨[83257], [83257], .contexts []⟩,
    ⟨[83259, 3], [83257], .contexts [
        ⟨20232, true, false, [], [3]⟩,
        ⟨20, false, false, [83257], []⟩,
        ⟨20233, false, false, [], []⟩
      ]⟩,
    ⟨[83261], [83259, 5], .source 41695⟩,
    ⟨[83259, 5], [83261], .contexts [
        ⟨20235, true, false, [], []⟩
      ]⟩,
    ⟨[83259], [83259], .contexts []⟩,
    ⟨[83261, 5], [83259], .contexts [
        ⟨20236, true, false, [], [5]⟩,
        ⟨28, false, false, [83259], []⟩,
        ⟨20237, false, false, [], []⟩
      ]⟩,
    ⟨[83263], [83261, 1], .source 41696⟩,
    ⟨[83261, 1], [83263], .contexts [
        ⟨20239, true, false, [], []⟩
      ]⟩,
    ⟨[83261], [83261], .contexts []⟩,
    ⟨[83263, 1], [83261], .contexts [
        ⟨20240, true, false, [], [1]⟩,
        ⟨8, false, false, [83261], []⟩,
        ⟨20241, false, false, [], []⟩
      ]⟩,
    ⟨[83265], [83263, 9], .source 41697⟩,
    ⟨[83263, 9], [83265], .contexts [
        ⟨20243, true, false, [], []⟩
      ]⟩,
    ⟨[83263], [83263], .contexts []⟩,
    ⟨[83265, 9], [83263], .contexts [
        ⟨20244, true, false, [], [9]⟩,
        ⟨46, false, false, [83263], []⟩,
        ⟨20245, false, false, [], []⟩
      ]⟩,
    ⟨[83267], [83265, 11], .source 41698⟩,
    ⟨[83265, 11], [83267], .contexts [
        ⟨20247, true, false, [], []⟩
      ]⟩,
    ⟨[83265], [83265], .contexts []⟩,
    ⟨[83267, 11], [83265], .contexts [
        ⟨20248, true, false, [], [11]⟩,
        ⟨53, false, false, [83265], []⟩,
        ⟨20249, false, false, [], []⟩
      ]⟩,
    ⟨[83269], [83267, 1], .source 41699⟩,
    ⟨[83267, 1], [83269], .contexts [
        ⟨20251, true, false, [], []⟩
      ]⟩,
    ⟨[83267], [83267], .contexts []⟩,
    ⟨[83269, 1], [83267], .contexts [
        ⟨20252, true, false, [], [1]⟩,
        ⟨8, false, false, [83267], []⟩,
        ⟨20253, false, false, [], []⟩
      ]⟩,
    ⟨[83271], [83269, 13], .source 41700⟩,
    ⟨[83269, 13], [83271], .contexts [
        ⟨20255, true, false, [], []⟩
      ]⟩,
    ⟨[83269], [83269], .contexts []⟩,
    ⟨[83271, 13], [83269], .contexts [
        ⟨20256, true, false, [], [13]⟩,
        ⟨59, false, false, [83269], []⟩,
        ⟨20257, false, false, [], []⟩
      ]⟩,
    ⟨[83273], [83271, 15], .source 41701⟩,
    ⟨[83271, 15], [83273], .contexts [
        ⟨20259, true, false, [], []⟩
      ]⟩,
    ⟨[83271], [83271], .contexts []⟩,
    ⟨[83273, 15], [83271], .contexts [
        ⟨20260, true, false, [], [15]⟩,
        ⟨1, false, false, [83271], []⟩,
        ⟨20261, false, false, [], []⟩
      ]⟩,
    ⟨[83275], [83273, 1], .source 41702⟩,
    ⟨[83273, 1], [83275], .contexts [
        ⟨20263, true, false, [], []⟩
      ]⟩,
    ⟨[83273], [83273], .contexts []⟩,
    ⟨[83275, 1], [83273], .contexts [
        ⟨20264, true, false, [], [1]⟩,
        ⟨8, false, false, [83273], []⟩,
        ⟨20265, false, false, [], []⟩
      ]⟩,
    ⟨[83277], [83275, 3], .source 41703⟩,
    ⟨[83275, 3], [83277], .contexts [
        ⟨20267, true, false, [], []⟩
      ]⟩,
    ⟨[83275], [83275], .contexts []⟩,
    ⟨[83277, 3], [83275], .contexts [
        ⟨20268, true, false, [], [3]⟩,
        ⟨20, false, false, [83275], []⟩,
        ⟨20269, false, false, [], []⟩
      ]⟩,
    ⟨[83279], [83277, 5], .source 41704⟩,
    ⟨[83277, 5], [83279], .contexts [
        ⟨20271, true, false, [], []⟩
      ]⟩,
    ⟨[83277], [83277], .contexts []⟩,
    ⟨[83279, 5], [83277], .contexts [
        ⟨20272, true, false, [], [5]⟩,
        ⟨28, false, false, [83277], []⟩,
        ⟨20273, false, false, [], []⟩
      ]⟩,
    ⟨[83281], [83279, 1], .source 41705⟩,
    ⟨[83279, 1], [83281], .contexts [
        ⟨20275, true, false, [], []⟩
      ]⟩,
    ⟨[83279], [83279], .contexts []⟩,
    ⟨[83281, 1], [83279], .contexts [
        ⟨20276, true, false, [], [1]⟩,
        ⟨8, false, false, [83279], []⟩,
        ⟨20277, false, false, [], []⟩
      ]⟩,
    ⟨[83283], [83281, 9], .source 41706⟩,
    ⟨[83281, 9], [83283], .contexts [
        ⟨20279, true, false, [], []⟩
      ]⟩,
    ⟨[83281], [83281], .contexts []⟩,
    ⟨[83283, 9], [83281], .contexts [
        ⟨20280, true, false, [], [9]⟩,
        ⟨46, false, false, [83281], []⟩,
        ⟨20281, false, false, [], []⟩
      ]⟩,
    ⟨[83285], [83283, 11], .source 41707⟩,
    ⟨[83283, 11], [83285], .contexts [
        ⟨20283, true, false, [], []⟩
      ]⟩,
    ⟨[83283], [83283], .contexts []⟩,
    ⟨[83285, 11], [83283], .contexts [
        ⟨20284, true, false, [], [11]⟩,
        ⟨53, false, false, [83283], []⟩,
        ⟨20285, false, false, [], []⟩
      ]⟩,
    ⟨[83287], [83285, 1], .source 41708⟩]

/-- Exact literal claimed equations and contextual derivations, block 317. -/
def y322TCIndexRaw317 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83285, 1], [83287], .contexts [
        ⟨20287, true, false, [], []⟩
      ]⟩,
    ⟨[83285], [83285], .contexts []⟩,
    ⟨[83287, 1], [83285], .contexts [
        ⟨20288, true, false, [], [1]⟩,
        ⟨8, false, false, [83285], []⟩,
        ⟨20289, false, false, [], []⟩
      ]⟩,
    ⟨[83289], [83287, 13], .source 41709⟩,
    ⟨[83287, 13], [83289], .contexts [
        ⟨20291, true, false, [], []⟩
      ]⟩,
    ⟨[83287], [83287], .contexts []⟩,
    ⟨[83291], [83289, 15], .source 41710⟩,
    ⟨[83289, 15], [83291], .contexts [
        ⟨20294, true, false, [], []⟩
      ]⟩,
    ⟨[83289], [83289], .contexts []⟩,
    ⟨[83291, 15], [83289], .contexts [
        ⟨20295, true, false, [], [15]⟩,
        ⟨1, false, false, [83289], []⟩,
        ⟨20296, false, false, [], []⟩
      ]⟩,
    ⟨[83293], [83291, 1], .source 41711⟩,
    ⟨[83291, 1], [83293], .contexts [
        ⟨20298, true, false, [], []⟩
      ]⟩,
    ⟨[83291], [83291], .contexts []⟩,
    ⟨[83293, 1], [83291], .contexts [
        ⟨20299, true, false, [], [1]⟩,
        ⟨8, false, false, [83291], []⟩,
        ⟨20300, false, false, [], []⟩
      ]⟩,
    ⟨[83295], [83293, 3], .source 41712⟩,
    ⟨[83293, 3], [83295], .contexts [
        ⟨20302, true, false, [], []⟩
      ]⟩,
    ⟨[83293], [83293], .contexts []⟩,
    ⟨[83295, 3], [83293], .contexts [
        ⟨20303, true, false, [], [3]⟩,
        ⟨20, false, false, [83293], []⟩,
        ⟨20304, false, false, [], []⟩
      ]⟩,
    ⟨[83297], [83295, 5], .source 41713⟩,
    ⟨[83295, 5], [83297], .contexts [
        ⟨20306, true, false, [], []⟩
      ]⟩,
    ⟨[83295], [83295], .contexts []⟩,
    ⟨[83297, 5], [83295], .contexts [
        ⟨20307, true, false, [], [5]⟩,
        ⟨28, false, false, [83295], []⟩,
        ⟨20308, false, false, [], []⟩
      ]⟩,
    ⟨[83299], [83297, 1], .source 41714⟩,
    ⟨[83297, 1], [83299], .contexts [
        ⟨20310, true, false, [], []⟩
      ]⟩,
    ⟨[83297], [83297], .contexts []⟩,
    ⟨[83299, 1], [83297], .contexts [
        ⟨20311, true, false, [], [1]⟩,
        ⟨8, false, false, [83297], []⟩,
        ⟨20312, false, false, [], []⟩
      ]⟩,
    ⟨[83301], [83299, 9], .source 41715⟩,
    ⟨[83299, 9], [83301], .contexts [
        ⟨20314, true, false, [], []⟩
      ]⟩,
    ⟨[83299], [83299], .contexts []⟩,
    ⟨[83301, 9], [83299], .contexts [
        ⟨20315, true, false, [], [9]⟩,
        ⟨46, false, false, [83299], []⟩,
        ⟨20316, false, false, [], []⟩
      ]⟩,
    ⟨[83303], [83301, 11], .source 41716⟩,
    ⟨[83301, 11], [83303], .contexts [
        ⟨20318, true, false, [], []⟩
      ]⟩,
    ⟨[83301], [83301], .contexts []⟩,
    ⟨[83303, 11], [83301], .contexts [
        ⟨20319, true, false, [], [11]⟩,
        ⟨53, false, false, [83301], []⟩,
        ⟨20320, false, false, [], []⟩
      ]⟩,
    ⟨[83305], [83303, 1], .source 41717⟩,
    ⟨[83303, 1], [83305], .contexts [
        ⟨20322, true, false, [], []⟩
      ]⟩,
    ⟨[83303], [83303], .contexts []⟩,
    ⟨[83305, 1], [83303], .contexts [
        ⟨20323, true, false, [], [1]⟩,
        ⟨8, false, false, [83303], []⟩,
        ⟨20324, false, false, [], []⟩
      ]⟩,
    ⟨[83307], [83305, 13], .source 41718⟩,
    ⟨[83305, 13], [83307], .contexts [
        ⟨20326, true, false, [], []⟩
      ]⟩,
    ⟨[83305], [83305], .contexts []⟩,
    ⟨[83307, 13], [83305], .contexts [
        ⟨20327, true, false, [], [13]⟩,
        ⟨59, false, false, [83305], []⟩,
        ⟨20328, false, false, [], []⟩
      ]⟩,
    ⟨[83309], [83307, 15], .source 41719⟩,
    ⟨[83307, 15], [83309], .contexts [
        ⟨20330, true, false, [], []⟩
      ]⟩,
    ⟨[83307], [83307], .contexts []⟩,
    ⟨[83309, 15], [83307], .contexts [
        ⟨20331, true, false, [], [15]⟩,
        ⟨1, false, false, [83307], []⟩,
        ⟨20332, false, false, [], []⟩
      ]⟩,
    ⟨[83311], [83309, 1], .source 41720⟩,
    ⟨[83309, 1], [83311], .contexts [
        ⟨20334, true, false, [], []⟩
      ]⟩,
    ⟨[83309], [83309], .contexts []⟩,
    ⟨[83311, 1], [83309], .contexts [
        ⟨20335, true, false, [], [1]⟩,
        ⟨8, false, false, [83309], []⟩,
        ⟨20336, false, false, [], []⟩
      ]⟩,
    ⟨[83313], [83311, 3], .source 41721⟩,
    ⟨[83311, 3], [83313], .contexts [
        ⟨20338, true, false, [], []⟩
      ]⟩,
    ⟨[83311], [83311], .contexts []⟩,
    ⟨[83313, 3], [83311], .contexts [
        ⟨20339, true, false, [], [3]⟩,
        ⟨20, false, false, [83311], []⟩,
        ⟨20340, false, false, [], []⟩
      ]⟩,
    ⟨[83315], [83313, 5], .source 41722⟩,
    ⟨[83313, 5], [83315], .contexts [
        ⟨20342, true, false, [], []⟩
      ]⟩,
    ⟨[83313], [83313], .contexts []⟩,
    ⟨[83315, 5], [83313], .contexts [
        ⟨20343, true, false, [], [5]⟩,
        ⟨28, false, false, [83313], []⟩,
        ⟨20344, false, false, [], []⟩
      ]⟩,
    ⟨[83317], [83315, 1], .source 41723⟩,
    ⟨[83315, 1], [83317], .contexts [
        ⟨20346, true, false, [], []⟩
      ]⟩,
    ⟨[83315], [83315], .contexts []⟩,
    ⟨[83317, 1], [83315], .contexts [
        ⟨20347, true, false, [], [1]⟩,
        ⟨8, false, false, [83315], []⟩,
        ⟨20348, false, false, [], []⟩
      ]⟩,
    ⟨[83319], [83317, 9], .source 41724⟩,
    ⟨[83317, 9], [83319], .contexts [
        ⟨20350, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 318. -/
def y322TCIndexRaw318 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83317], [83317], .contexts []⟩,
    ⟨[83319, 9], [83317], .contexts [
        ⟨20351, true, false, [], [9]⟩,
        ⟨46, false, false, [83317], []⟩,
        ⟨20352, false, false, [], []⟩
      ]⟩,
    ⟨[83321], [83319, 11], .source 41725⟩,
    ⟨[83319, 11], [83321], .contexts [
        ⟨20354, true, false, [], []⟩
      ]⟩,
    ⟨[83319], [83319], .contexts []⟩,
    ⟨[83321, 11], [83319], .contexts [
        ⟨20355, true, false, [], [11]⟩,
        ⟨53, false, false, [83319], []⟩,
        ⟨20356, false, false, [], []⟩
      ]⟩,
    ⟨[83323], [83321, 1], .source 41726⟩,
    ⟨[83321, 1], [83323], .contexts [
        ⟨20358, true, false, [], []⟩
      ]⟩,
    ⟨[83321], [83321], .contexts []⟩,
    ⟨[83323, 1], [83321], .contexts [
        ⟨20359, true, false, [], [1]⟩,
        ⟨8, false, false, [83321], []⟩,
        ⟨20360, false, false, [], []⟩
      ]⟩,
    ⟨[83325], [83323, 13], .source 41727⟩,
    ⟨[83323, 13], [83325], .contexts [
        ⟨20362, true, false, [], []⟩
      ]⟩,
    ⟨[83323], [83323], .contexts []⟩,
    ⟨[83325, 13], [83323], .contexts [
        ⟨20363, true, false, [], [13]⟩,
        ⟨59, false, false, [83323], []⟩,
        ⟨20364, false, false, [], []⟩
      ]⟩,
    ⟨[83327], [83325, 15], .source 41728⟩,
    ⟨[83325, 15], [83327], .contexts [
        ⟨20366, true, false, [], []⟩
      ]⟩,
    ⟨[83325], [83325], .contexts []⟩,
    ⟨[83327, 15], [83325], .contexts [
        ⟨20367, true, false, [], [15]⟩,
        ⟨1, false, false, [83325], []⟩,
        ⟨20368, false, false, [], []⟩
      ]⟩,
    ⟨[83329], [83327, 1], .source 41729⟩,
    ⟨[83327, 1], [83329], .contexts [
        ⟨20370, true, false, [], []⟩
      ]⟩,
    ⟨[83327], [83327], .contexts []⟩,
    ⟨[83329, 1], [83327], .contexts [
        ⟨20371, true, false, [], [1]⟩,
        ⟨8, false, false, [83327], []⟩,
        ⟨20372, false, false, [], []⟩
      ]⟩,
    ⟨[83329], [83329], .contexts []⟩,
    ⟨[83329], [83329], .contexts []⟩,
    ⟨[83327, 1], [83329], .contexts [
        ⟨20371, false, false, [], []⟩,
        ⟨20374, false, false, [], []⟩,
        ⟨20375, false, false, [], []⟩,
        ⟨20375, false, false, [], []⟩
      ]⟩,
    ⟨[83325], [83325], .contexts []⟩,
    ⟨[83327, 15], [83325], .contexts [
        ⟨20369, false, false, [], []⟩,
        ⟨20377, false, false, [], []⟩,
        ⟨20368, false, false, [], []⟩,
        ⟨20368, false, false, [], []⟩
      ]⟩,
    ⟨[83325, 13], [83323], .contexts [
        ⟨20365, false, false, [], []⟩
      ]⟩,
    ⟨[83323], [83323], .contexts []⟩,
    ⟨[83327, 15, 13], [83323], .contexts [
        ⟨20378, false, false, [], [13]⟩,
        ⟨20379, false, false, [], []⟩,
        ⟨20380, false, false, [], []⟩,
        ⟨20364, false, false, [], []⟩,
        ⟨20364, false, false, [], []⟩
      ]⟩,
    ⟨[83321], [83321], .contexts []⟩,
    ⟨[83321, 11], [83319], .contexts [
        ⟨20357, false, false, [], []⟩
      ]⟩,
    ⟨[83319], [83319], .contexts []⟩,
    ⟨[83319, 9], [83317], .contexts [
        ⟨20353, false, false, [], []⟩
      ]⟩,
    ⟨[83317], [83317], .contexts []⟩,
    ⟨[83317, 1], [83315], .contexts [
        ⟨20349, false, false, [], []⟩
      ]⟩,
    ⟨[83315], [83315], .contexts []⟩,
    ⟨[83327, 15, 13, 1, 11, 9, 1, 5], [83313], .contexts [
        ⟨20381, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨20361, false, false, [], [11, 9, 1, 5]⟩,
        ⟨20382, false, false, [], [11, 9, 1, 5]⟩,
        ⟨20360, false, false, [], [11, 9, 1, 5]⟩,
        ⟨20360, false, false, [], [11, 9, 1, 5]⟩,
        ⟨20383, false, false, [], [9, 1, 5]⟩,
        ⟨20384, false, false, [], [9, 1, 5]⟩,
        ⟨20356, false, false, [], [9, 1, 5]⟩,
        ⟨20356, false, false, [], [9, 1, 5]⟩,
        ⟨20385, false, false, [], [1, 5]⟩,
        ⟨20386, false, false, [], [1, 5]⟩,
        ⟨20352, false, false, [], [1, 5]⟩,
        ⟨20352, false, false, [], [1, 5]⟩,
        ⟨20387, false, false, [], [5]⟩,
        ⟨20388, false, false, [], [5]⟩,
        ⟨20348, false, false, [], [5]⟩,
        ⟨20348, false, false, [], [5]⟩,
        ⟨20345, false, false, [], []⟩,
        ⟨20344, false, false, [], []⟩,
        ⟨20344, false, false, [], []⟩
      ]⟩,
    ⟨[83311], [83311], .contexts []⟩,
    ⟨[83309], [83309], .contexts []⟩,
    ⟨[83309, 15], [83307], .contexts [
        ⟨20333, false, false, [], []⟩
      ]⟩,
    ⟨[83307], [83307], .contexts []⟩,
    ⟨[83307, 13], [83305], .contexts [
        ⟨20329, false, false, [], []⟩
      ]⟩,
    ⟨[83305], [83305], .contexts []⟩,
    ⟨[83305, 1], [83303], .contexts [
        ⟨20325, false, false, [], []⟩
      ]⟩,
    ⟨[83303], [83303], .contexts []⟩,
    ⟨[
      83327, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1
    ], [83303], .contexts [
        ⟨20389, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨20341, false, false, [], [1, 15, 13, 1]⟩,
        ⟨20390, false, false, [], [1, 15, 13, 1]⟩,
        ⟨20340, false, false, [], [1, 15, 13, 1]⟩,
        ⟨20340, false, false, [], [1, 15, 13, 1]⟩,
        ⟨20337, false, false, [], [15, 13, 1]⟩,
        ⟨20391, false, false, [], [15, 13, 1]⟩,
        ⟨20336, false, false, [], [15, 13, 1]⟩,
        ⟨20336, false, false, [], [15, 13, 1]⟩,
        ⟨20392, false, false, [], [13, 1]⟩,
        ⟨20393, false, false, [], [13, 1]⟩,
        ⟨20332, false, false, [], [13, 1]⟩,
        ⟨20332, false, false, [], [13, 1]⟩,
        ⟨20394, false, false, [], [1]⟩,
        ⟨20395, false, false, [], [1]⟩,
        ⟨20328, false, false, [], [1]⟩,
        ⟨20328, false, false, [], [1]⟩,
        ⟨20396, false, false, [], []⟩,
        ⟨20397, false, false, [], []⟩,
        ⟨20324, false, false, [], []⟩,
        ⟨20324, false, false, [], []⟩
      ]⟩,
    ⟨[83303, 11], [83301], .contexts [
        ⟨20321, false, false, [], []⟩
      ]⟩,
    ⟨[83301], [83301], .contexts []⟩,
    ⟨[83301, 9], [83299], .contexts [
        ⟨20317, false, false, [], []⟩
      ]⟩,
    ⟨[83299], [83299], .contexts []⟩,
    ⟨[83297], [83297], .contexts []⟩,
    ⟨[83295], [83295], .contexts []⟩,
    ⟨[83293], [83293], .contexts []⟩,
    ⟨[
      83327, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3
    ], [83293], .contexts [
        ⟨20398, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨20399, false, false, [], [9, 1, 5, 3]⟩,
        ⟨20400, false, false, [], [9, 1, 5, 3]⟩,
        ⟨20320, false, false, [], [9, 1, 5, 3]⟩,
        ⟨20320, false, false, [], [9, 1, 5, 3]⟩,
        ⟨20401, false, false, [], [1, 5, 3]⟩,
        ⟨20402, false, false, [], [1, 5, 3]⟩,
        ⟨20316, false, false, [], [1, 5, 3]⟩,
        ⟨20316, false, false, [], [1, 5, 3]⟩,
        ⟨20313, false, false, [], [5, 3]⟩,
        ⟨20403, false, false, [], [5, 3]⟩,
        ⟨20312, false, false, [], [5, 3]⟩,
        ⟨20312, false, false, [], [5, 3]⟩,
        ⟨20309, false, false, [], [3]⟩,
        ⟨20404, false, false, [], [3]⟩,
        ⟨20308, false, false, [], [3]⟩,
        ⟨20308, false, false, [], [3]⟩,
        ⟨20305, false, false, [], []⟩,
        ⟨20405, false, false, [], []⟩,
        ⟨20304, false, false, [], []⟩,
        ⟨20304, false, false, [], []⟩
      ]⟩,
    ⟨[83293, 1], [83291], .contexts [
        ⟨20301, false, false, [], []⟩
      ]⟩,
    ⟨[83291], [83291], .contexts []⟩,
    ⟨[83291, 15], [83289], .contexts [
        ⟨20297, false, false, [], []⟩
      ]⟩,
    ⟨[83289], [83289], .contexts []⟩,
    ⟨[83289, 13], [83287], .contexts [
        ⟨20292, true, false, [], [13]⟩,
        ⟨59, false, false, [83287], []⟩,
        ⟨20293, false, false, [], []⟩
      ]⟩,
    ⟨[83287], [83287], .contexts []⟩,
    ⟨[83287, 1], [83285], .contexts [
        ⟨20290, false, false, [], []⟩
      ]⟩,
    ⟨[83285], [83285], .contexts []⟩,
    ⟨[83285, 11], [83283], .contexts [
        ⟨20286, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 319. -/
def y322TCIndexRaw319 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83283], [83283], .contexts []⟩,
    ⟨[
      83327, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [83283], .contexts [
        ⟨20406, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨20407, false, false, [], [15, 13, 1, 11]⟩,
        ⟨20408, false, false, [], [15, 13, 1, 11]⟩,
        ⟨20300, false, false, [], [15, 13, 1, 11]⟩,
        ⟨20300, false, false, [], [15, 13, 1, 11]⟩,
        ⟨20409, false, false, [], [13, 1, 11]⟩,
        ⟨20410, false, false, [], [13, 1, 11]⟩,
        ⟨20296, false, false, [], [13, 1, 11]⟩,
        ⟨20296, false, false, [], [13, 1, 11]⟩,
        ⟨20411, false, false, [], [1, 11]⟩,
        ⟨20412, false, false, [], [1, 11]⟩,
        ⟨20293, false, false, [], [1, 11]⟩,
        ⟨20293, false, false, [], [1, 11]⟩,
        ⟨20413, false, false, [], [11]⟩,
        ⟨20414, false, false, [], [11]⟩,
        ⟨20289, false, false, [], [11]⟩,
        ⟨20289, false, false, [], [11]⟩,
        ⟨20415, false, false, [], []⟩,
        ⟨20416, false, false, [], []⟩,
        ⟨20285, false, false, [], []⟩,
        ⟨20285, false, false, [], []⟩
      ]⟩,
    ⟨[83281], [83281], .contexts []⟩,
    ⟨[83281, 1], [83279], .contexts [
        ⟨20278, false, false, [], []⟩
      ]⟩,
    ⟨[83279], [83279], .contexts []⟩,
    ⟨[83279, 5], [83277], .contexts [
        ⟨20274, false, false, [], []⟩
      ]⟩,
    ⟨[83277], [83277], .contexts []⟩,
    ⟨[83275], [83275], .contexts []⟩,
    ⟨[83273], [83273], .contexts []⟩,
    ⟨[
      83327, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1
    ], [83273], .contexts [
        ⟨20417, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨20282, false, false, [], [1, 5, 3, 1]⟩,
        ⟨20418, false, false, [], [1, 5, 3, 1]⟩,
        ⟨20281, false, false, [], [1, 5, 3, 1]⟩,
        ⟨20281, false, false, [], [1, 5, 3, 1]⟩,
        ⟨20419, false, false, [], [5, 3, 1]⟩,
        ⟨20420, false, false, [], [5, 3, 1]⟩,
        ⟨20277, false, false, [], [5, 3, 1]⟩,
        ⟨20277, false, false, [], [5, 3, 1]⟩,
        ⟨20421, false, false, [], [3, 1]⟩,
        ⟨20422, false, false, [], [3, 1]⟩,
        ⟨20273, false, false, [], [3, 1]⟩,
        ⟨20273, false, false, [], [3, 1]⟩,
        ⟨20270, false, false, [], [1]⟩,
        ⟨20423, false, false, [], [1]⟩,
        ⟨20269, false, false, [], [1]⟩,
        ⟨20269, false, false, [], [1]⟩,
        ⟨20266, false, false, [], []⟩,
        ⟨20424, false, false, [], []⟩,
        ⟨20265, false, false, [], []⟩,
        ⟨20265, false, false, [], []⟩
      ]⟩,
    ⟨[83271], [83271], .contexts []⟩,
    ⟨[83269], [83269], .contexts []⟩,
    ⟨[83267], [83267], .contexts []⟩,
    ⟨[83265], [83265], .contexts []⟩,
    ⟨[83263], [83263], .contexts []⟩,
    ⟨[
      83327, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [83263], .contexts [
        ⟨20425, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨20262, false, false, [], [13, 1, 11, 9]⟩,
        ⟨20426, false, false, [], [13, 1, 11, 9]⟩,
        ⟨20261, false, false, [], [13, 1, 11, 9]⟩,
        ⟨20261, false, false, [], [13, 1, 11, 9]⟩,
        ⟨20258, false, false, [], [1, 11, 9]⟩,
        ⟨20427, false, false, [], [1, 11, 9]⟩,
        ⟨20257, false, false, [], [1, 11, 9]⟩,
        ⟨20257, false, false, [], [1, 11, 9]⟩,
        ⟨20254, false, false, [], [11, 9]⟩,
        ⟨20428, false, false, [], [11, 9]⟩,
        ⟨20253, false, false, [], [11, 9]⟩,
        ⟨20253, false, false, [], [11, 9]⟩,
        ⟨20250, false, false, [], [9]⟩,
        ⟨20429, false, false, [], [9]⟩,
        ⟨20249, false, false, [], [9]⟩,
        ⟨20249, false, false, [], [9]⟩,
        ⟨20246, false, false, [], []⟩,
        ⟨20430, false, false, [], []⟩,
        ⟨20245, false, false, [], []⟩,
        ⟨20245, false, false, [], []⟩
      ]⟩,
    ⟨[83261], [83261], .contexts []⟩,
    ⟨[83259], [83259], .contexts []⟩,
    ⟨[83257], [83257], .contexts []⟩,
    ⟨[83255], [83255], .contexts []⟩,
    ⟨[83255, 15], [83253], .contexts [
        ⟨20226, false, false, [], []⟩
      ]⟩,
    ⟨[83253], [83253], .contexts []⟩,
    ⟨[
      83327, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15
    ], [83253], .contexts [
        ⟨20431, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨20242, false, false, [], [5, 3, 1, 15]⟩,
        ⟨20432, false, false, [], [5, 3, 1, 15]⟩,
        ⟨20241, false, false, [], [5, 3, 1, 15]⟩,
        ⟨20241, false, false, [], [5, 3, 1, 15]⟩,
        ⟨20238, false, false, [], [3, 1, 15]⟩,
        ⟨20433, false, false, [], [3, 1, 15]⟩,
        ⟨20237, false, false, [], [3, 1, 15]⟩,
        ⟨20237, false, false, [], [3, 1, 15]⟩,
        ⟨20234, false, false, [], [1, 15]⟩,
        ⟨20434, false, false, [], [1, 15]⟩,
        ⟨20233, false, false, [], [1, 15]⟩,
        ⟨20233, false, false, [], [1, 15]⟩,
        ⟨20230, false, false, [], [15]⟩,
        ⟨20435, false, false, [], [15]⟩,
        ⟨20229, false, false, [], [15]⟩,
        ⟨20229, false, false, [], [15]⟩,
        ⟨20436, false, false, [], []⟩,
        ⟨20437, false, false, [], []⟩,
        ⟨20225, false, false, [], []⟩,
        ⟨20225, false, false, [], []⟩
      ]⟩,
    ⟨[83251], [83251], .contexts []⟩,
    ⟨[83249], [83249], .contexts []⟩,
    ⟨[83247], [83247], .contexts []⟩,
    ⟨[83245], [83245], .contexts []⟩,
    ⟨[
      83327, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9
    ], [83245], .contexts [
        ⟨20438, false, false, [], [13, 1, 11, 9]⟩,
        ⟨20221, true, false, [], [13, 1, 11, 9]⟩,
        ⟨59, false, false, [83251], [1, 11, 9]⟩,
        ⟨20222, false, false, [], [1, 11, 9]⟩,
        ⟨20439, false, false, [], [1, 11, 9]⟩,
        ⟨20222, false, false, [], [1, 11, 9]⟩,
        ⟨20222, false, false, [], [1, 11, 9]⟩,
        ⟨20219, false, false, [], [11, 9]⟩,
        ⟨20440, false, false, [], [11, 9]⟩,
        ⟨20218, false, false, [], [11, 9]⟩,
        ⟨20218, false, false, [], [11, 9]⟩,
        ⟨20215, false, false, [], [9]⟩,
        ⟨20441, false, false, [], [9]⟩,
        ⟨20214, false, false, [], [9]⟩,
        ⟨20214, false, false, [], [9]⟩,
        ⟨20211, false, false, [], []⟩,
        ⟨20442, false, false, [], []⟩,
        ⟨20210, false, false, [], []⟩,
        ⟨20210, false, false, [], []⟩
      ]⟩,
    ⟨[83243], [83243], .contexts []⟩,
    ⟨[83241], [83241], .contexts []⟩,
    ⟨[83239], [83239], .contexts []⟩,
    ⟨[83237], [83237], .contexts []⟩,
    ⟨[83235], [83235], .contexts []⟩,
    ⟨[
      83327, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [83235], .contexts [
        ⟨20443, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨20207, false, false, [], [5, 3, 1, 15]⟩,
        ⟨20444, false, false, [], [5, 3, 1, 15]⟩,
        ⟨20206, false, false, [], [5, 3, 1, 15]⟩,
        ⟨20206, false, false, [], [5, 3, 1, 15]⟩,
        ⟨20203, false, false, [], [3, 1, 15]⟩,
        ⟨20445, false, false, [], [3, 1, 15]⟩,
        ⟨20202, false, false, [], [3, 1, 15]⟩,
        ⟨20202, false, false, [], [3, 1, 15]⟩,
        ⟨20199, false, false, [], [1, 15]⟩,
        ⟨20446, false, false, [], [1, 15]⟩,
        ⟨20198, false, false, [], [1, 15]⟩,
        ⟨20198, false, false, [], [1, 15]⟩,
        ⟨20195, false, false, [], [15]⟩,
        ⟨20447, false, false, [], [15]⟩,
        ⟨20194, false, false, [], [15]⟩,
        ⟨20194, false, false, [], [15]⟩,
        ⟨20191, false, false, [], []⟩,
        ⟨20448, false, false, [], []⟩,
        ⟨20190, false, false, [], []⟩,
        ⟨20190, false, false, [], []⟩
      ]⟩,
    ⟨[83233], [83233], .contexts []⟩,
    ⟨[83229], [83229], .contexts []⟩,
    ⟨[
      83327, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1
    ], [83225], .contexts [
        ⟨20449, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨20187, false, false, [], [1, 11, 9, 1]⟩,
        ⟨20450, false, false, [], [1, 11, 9, 1]⟩,
        ⟨20186, false, false, [], [1, 11, 9, 1]⟩,
        ⟨20186, false, false, [], [1, 11, 9, 1]⟩,
        ⟨20183, false, false, [], [11, 9, 1]⟩,
        ⟨20173, false, false, [], [11, 9, 1]⟩,
        ⟨20174, false, false, [], [11, 9, 1]⟩,
        ⟨20174, false, false, [], [11, 9, 1]⟩,
        ⟨20172, false, false, [], [9, 1]⟩,
        ⟨20451, false, false, [], [9, 1]⟩,
        ⟨20171, false, false, [], [9, 1]⟩,
        ⟨20171, false, false, [], [9, 1]⟩,
        ⟨20176, false, false, [], [1]⟩,
        ⟨20159, false, false, [], [1]⟩,
        ⟨20160, false, false, [], [1]⟩,
        ⟨20160, false, false, [], [1]⟩,
        ⟨20158, false, false, [], []⟩,
        ⟨20149, false, false, [], []⟩,
        ⟨20150, false, false, [], []⟩,
        ⟨20150, false, false, [], []⟩
      ]⟩,
    ⟨[
      83327, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [83215], .contexts [
        ⟨20452, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨20148, false, false, [], [3, 1, 15, 13]⟩,
        ⟨20137, false, false, [], [3, 1, 15, 13]⟩,
        ⟨20138, false, false, [], [3, 1, 15, 13]⟩,
        ⟨20138, false, false, [], [3, 1, 15, 13]⟩,
        ⟨20136, false, false, [], [1, 15, 13]⟩,
        ⟨20113, false, false, [], [1, 15, 13]⟩,
        ⟨20114, false, false, [], [1, 15, 13]⟩,
        ⟨20114, false, false, [], [1, 15, 13]⟩,
        ⟨20112, false, false, [], [15, 13]⟩,
        ⟨20086, false, false, [], [15, 13]⟩,
        ⟨20087, false, false, [], [15, 13]⟩,
        ⟨20087, false, false, [], [15, 13]⟩,
        ⟨20131, false, false, [], [13]⟩,
        ⟨19996, false, false, [], [13]⟩,
        ⟨19997, false, false, [], [13]⟩,
        ⟨19997, false, false, [], [13]⟩,
        ⟨20105, false, false, [], []⟩,
        ⟨20042, false, false, [], []⟩,
        ⟨20043, false, false, [], []⟩,
        ⟨20043, false, false, [], []⟩
      ]⟩,
    ⟨[16075, 83217], [16075, 83217], .contexts []⟩,
    ⟨[16075, 83217], [16075, 83217], .contexts []⟩,
    ⟨[16081], [16075, 445], .source 8105⟩,
    ⟨[16083], [16081, 509], .source 8106⟩,
    ⟨[16085], [16083, 15691], .source 8107⟩,
    ⟨[
      83327, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5
    ], [16085, 77713], .contexts [
        ⟨20453, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨20069, false, false, [], [11, 9, 1, 5]⟩,
        ⟨20454, false, false, [], [11, 9, 1, 5]⟩,
        ⟨20455, false, false, [], [11, 9, 1, 5]⟩,
        ⟨20455, false, false, [], [11, 9, 1, 5]⟩,
        ⟨20082, false, false, [16075], [9, 1, 5]⟩,
        ⟨20456, true, false, [], [83217, 9, 1, 5]⟩,
        ⟨20079, false, false, [16081], [1, 5]⟩,
        ⟨20457, true, false, [], [82983, 1, 5]⟩,
        ⟨18202, false, false, [16083], [5]⟩,
        ⟨20458, true, false, [], [82983, 5]⟩,
        ⟨18208, false, false, [16085], []⟩
      ]⟩,
    ⟨[16087], [16085, 503], .source 8108⟩,
    ⟨[16089], [16087, 31], .source 8109⟩,
    ⟨[16091], [16089, 19], .source 8110⟩,
    ⟨[
      83327, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1
    ], [16091, 77605], .contexts [
        ⟨20459, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨2329, false, false, [16085], [1, 15, 13, 1]⟩,
        ⟨20460, true, false, [], [77605, 1, 15, 13, 1]⟩,
        ⟨2089, false, false, [16087], [15, 13, 1]⟩,
        ⟨1593, false, false, [16087], [13, 1]⟩,
        ⟨443, true, false, [16087], [77483, 13, 1]⟩,
        ⟨20461, true, false, [], [77483, 13, 1]⟩,
        ⟨1591, false, false, [16089], [1]⟩,
        ⟨441, true, false, [16089], [77483, 1]⟩,
        ⟨20462, true, false, [], [77483, 1]⟩,
        ⟨2090, false, false, [16091], []⟩
      ]⟩,
    ⟨[16093], [16091, 211], .source 8111⟩,
    ⟨[16095], [16093, 217], .source 8112⟩,
    ⟨[16097], [16095, 209], .source 8113⟩,
    ⟨[16099], [16097, 25], .source 8114⟩,
    ⟨[16101], [16099, 23], .source 8115⟩,
    ⟨[
      83327, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [16101, 77359], .contexts [
        ⟨20463, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨2097, false, false, [16091], [9, 1, 5, 3]⟩,
        ⟨20464, true, false, [], [77479, 9, 1, 5, 3]⟩,
        ⟨1537, false, false, [16093], [1, 5, 3]⟩,
        ⟨20465, true, false, [], [77479, 1, 5, 3]⟩,
        ⟨1526, false, false, [16095], [5, 3]⟩,
        ⟨20466, true, false, [], [77359, 5, 3]⟩,
        ⟨1083, false, false, [16097], [3]⟩,
        ⟨465, true, false, [16097], [77359, 3]⟩,
        ⟨20467, true, false, [], [77359, 3]⟩,
        ⟨1076, false, false, [16099], []⟩,
        ⟨445, true, false, [16099], [77359]⟩,
        ⟨20468, true, false, [], [77359]⟩
      ]⟩,
    ⟨[16103], [16101, 211], .source 8116⟩,
    ⟨[16105], [16103, 223], .source 8117⟩,
    ⟨[16107], [16105, 209], .source 8118⟩,
    ⟨[16109], [16107, 19], .source 8119⟩,
    ⟨[
      83327, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11
    ], [16109, 77717], .contexts [
        ⟨20469, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨1527, false, false, [16101], [15, 13, 1, 11]⟩,
        ⟨20470, true, false, [], [77479, 15, 13, 1, 11]⟩,
        ⟨1540, false, false, [16103], [13, 1, 11]⟩,
        ⟨20471, true, false, [], [77479, 13, 1, 11]⟩,
        ⟨2827, false, false, [16105], [1, 11]⟩,
        ⟨20472, true, false, [], [77857, 1, 11]⟩,
        ⟨2817, false, false, [16107], [11]⟩,
        ⟨441, true, false, [16107], [77857, 11]⟩,
        ⟨20473, true, false, [], [77857, 11]⟩,
        ⟨2809, false, false, [16109], []⟩
      ]⟩,
    ⟨[16111], [16109, 15377], .source 8120⟩,
    ⟨[16113], [16111, 155], .source 8121⟩,
    ⟨[
      83327, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [16113, 82723], .contexts [
        ⟨20474, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨2791, false, false, [16109], [1, 5, 3, 1]⟩,
        ⟨16006, false, false, [16109], [5, 3, 1]⟩,
        ⟨20475, true, false, [], [82739, 5, 3, 1]⟩,
        ⟨16014, false, false, [16111], [3, 1]⟩,
        ⟨20476, true, false, [], [82739, 3, 1]⟩,
        ⟨16008, false, false, [16113], [1]⟩,
        ⟨15821, false, false, [16113], []⟩
      ]⟩,
    ⟨[16115], [16113, 15299], .source 8122⟩,
    ⟨[16117], [16115, 15289], .source 8123⟩]

/-- Literal contextual derivation data in chronological chunk 04. -/
def y322TCIndexRawChunk04 (i : Fin 4096) : Y322RawContextCertificate :=
  if i.val < 2048 then
    if i.val < 1024 then
      if i.val < 512 then
        if i.val < 256 then
          if i.val < 128 then
            if i.val < 64 then
              y322TCIndexRaw256 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw257 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 192 then
              y322TCIndexRaw258 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw259 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 384 then
            if i.val < 320 then
              y322TCIndexRaw260 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw261 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 448 then
              y322TCIndexRaw262 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw263 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 768 then
          if i.val < 640 then
            if i.val < 576 then
              y322TCIndexRaw264 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw265 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 704 then
              y322TCIndexRaw266 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw267 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 896 then
            if i.val < 832 then
              y322TCIndexRaw268 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw269 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 960 then
              y322TCIndexRaw270 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw271 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 1536 then
        if i.val < 1280 then
          if i.val < 1152 then
            if i.val < 1088 then
              y322TCIndexRaw272 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw273 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1216 then
              y322TCIndexRaw274 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw275 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1408 then
            if i.val < 1344 then
              y322TCIndexRaw276 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw277 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1472 then
              y322TCIndexRaw278 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw279 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 1792 then
          if i.val < 1664 then
            if i.val < 1600 then
              y322TCIndexRaw280 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw281 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1728 then
              y322TCIndexRaw282 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw283 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1920 then
            if i.val < 1856 then
              y322TCIndexRaw284 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw285 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1984 then
              y322TCIndexRaw286 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw287 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  else
    if i.val < 3072 then
      if i.val < 2560 then
        if i.val < 2304 then
          if i.val < 2176 then
            if i.val < 2112 then
              y322TCIndexRaw288 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw289 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2240 then
              y322TCIndexRaw290 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw291 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2432 then
            if i.val < 2368 then
              y322TCIndexRaw292 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw293 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2496 then
              y322TCIndexRaw294 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw295 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 2816 then
          if i.val < 2688 then
            if i.val < 2624 then
              y322TCIndexRaw296 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw297 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2752 then
              y322TCIndexRaw298 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw299 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2944 then
            if i.val < 2880 then
              y322TCIndexRaw300 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw301 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3008 then
              y322TCIndexRaw302 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw303 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 3584 then
        if i.val < 3328 then
          if i.val < 3200 then
            if i.val < 3136 then
              y322TCIndexRaw304 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw305 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3264 then
              y322TCIndexRaw306 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw307 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3456 then
            if i.val < 3392 then
              y322TCIndexRaw308 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw309 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3520 then
              y322TCIndexRaw310 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw311 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 3840 then
          if i.val < 3712 then
            if i.val < 3648 then
              y322TCIndexRaw312 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw313 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3776 then
              y322TCIndexRaw314 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw315 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3968 then
            if i.val < 3904 then
              y322TCIndexRaw316 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw317 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 4032 then
              y322TCIndexRaw318 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw319 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
