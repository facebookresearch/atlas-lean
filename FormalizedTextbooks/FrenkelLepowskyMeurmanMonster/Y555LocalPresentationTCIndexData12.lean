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

/-- Exact literal claimed equations and contextual derivations, block 768. -/
def y322TCIndexRaw768 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[22501], [22502], .contexts [
        ⟨49138, true, true, [], []⟩
      ]⟩,
    ⟨[22501], [22501], .contexts []⟩,
    ⟨[22502], [22502], .contexts []⟩,
    ⟨[22501], [22502], .contexts [
        ⟨49153, false, false, [], []⟩,
        ⟨49152, false, false, [], []⟩,
        ⟨49154, false, false, [], []⟩,
        ⟨49154, false, false, [], []⟩
      ]⟩,
    ⟨[22501, 87643], [22501, 87643], .contexts []⟩,
    ⟨[87643, 11], [22501, 87643], .contexts [
        ⟨49151, false, false, [], []⟩,
        ⟨49151, false, false, [], []⟩,
        ⟨44976, true, false, [], [11]⟩,
        ⟨49150, true, false, [22502], [1, 11]⟩,
        ⟨49150, true, false, [22502], [1, 11]⟩,
        ⟨49149, true, false, [22502], [1, 11]⟩,
        ⟨49141, true, false, [22502], [1, 11]⟩,
        ⟨49136, true, false, [22502], [1, 11]⟩,
        ⟨567, false, false, [22502, 87645], []⟩,
        ⟨9, false, false, [22502, 87645], []⟩,
        ⟨45142, false, false, [22502], []⟩,
        ⟨45143, false, false, [22502], []⟩,
        ⟨44975, false, false, [22502], []⟩,
        ⟨44975, false, false, [22502], []⟩,
        ⟨49155, true, false, [], [87643]⟩,
        ⟨49156, false, false, [], []⟩,
        ⟨49156, false, false, [], []⟩
      ]⟩,
    ⟨[87641, 11], [87641, 11], .contexts []⟩,
    ⟨[87641], [87641], .contexts []⟩,
    ⟨[87641, 11], [22503, 87641], .contexts [
        ⟨49158, false, false, [], []⟩,
        ⟨44972, true, false, [], [11]⟩,
        ⟨49157, true, false, [22500], [15, 11]⟩,
        ⟨615, false, false, [22500, 87643], []⟩,
        ⟨10, false, false, [22500, 87643], []⟩,
        ⟨45144, false, false, [22500], []⟩,
        ⟨45145, false, false, [22500], []⟩,
        ⟨44971, false, false, [22500], []⟩,
        ⟨44971, false, false, [22500], []⟩,
        ⟨49159, false, false, [22500], []⟩,
        ⟨49140, true, false, [], [87641]⟩
      ]⟩,
    ⟨[22503, 87641], [22503, 87641], .contexts []⟩,
    ⟨[22503, 87641], [22503, 87641], .contexts []⟩,
    ⟨[87641, 11], [22503, 87641], .contexts [
        ⟨49158, false, false, [], []⟩,
        ⟨49160, false, false, [], []⟩,
        ⟨49161, false, false, [], []⟩,
        ⟨49162, false, false, [], []⟩,
        ⟨49162, false, false, [], []⟩
      ]⟩,
    ⟨[22503, 87639], [22503, 87639], .contexts []⟩,
    ⟨[87639, 11], [87639, 11], .contexts []⟩,
    ⟨[87639], [87639], .contexts []⟩,
    ⟨[87639, 11], [22501, 87639], .contexts [
        ⟨49165, false, false, [], []⟩,
        ⟨49164, true, false, [22502], [11]⟩,
        ⟨44968, true, false, [], [11]⟩,
        ⟨49163, true, false, [22502], [13, 11]⟩,
        ⟨619, false, false, [22502, 87641], []⟩,
        ⟨64, false, false, [22502, 87641], []⟩,
        ⟨45147, false, false, [22502], []⟩,
        ⟨45148, false, false, [22502], []⟩,
        ⟨44967, false, false, [22502], []⟩,
        ⟨44967, false, false, [22502], []⟩,
        ⟨49166, false, false, [22502], []⟩,
        ⟨49155, true, false, [], [87639]⟩
      ]⟩,
    ⟨[22501, 87639], [22501, 87639], .contexts []⟩,
    ⟨[22501, 87639], [22501, 87639], .contexts []⟩,
    ⟨[22501, 87635], [22501, 87635], .contexts []⟩,
    ⟨[22501, 87635], [22501, 87635], .contexts []⟩,
    ⟨[87635, 1], [22503, 87639], .contexts [
        ⟨49171, true, false, [22500], [1]⟩,
        ⟨49170, true, false, [22500], [1]⟩,
        ⟨44961, true, false, [], [1]⟩,
        ⟨44964, true, false, [], [11, 1]⟩,
        ⟨49169, true, false, [22500], [1, 11, 1]⟩,
        ⟨49169, true, false, [22500], [1, 11, 1]⟩,
        ⟨49168, true, false, [22500], [1, 11, 1]⟩,
        ⟨49167, true, false, [22500], [1, 11, 1]⟩,
        ⟨49165, true, false, [22500], [1, 11, 1]⟩,
        ⟨628, false, false, [22500, 87639], []⟩,
        ⟨49166, false, false, [22500], []⟩,
        ⟨49140, true, false, [], [87639]⟩
      ]⟩,
    ⟨[22501], [22501], .contexts []⟩,
    ⟨[22501], [22501], .contexts []⟩,
    ⟨[88205], [78831, 3], .source 44167⟩,
    ⟨[78831, 3], [88205], .contexts [
        ⟨49175, true, false, [], []⟩
      ]⟩,
    ⟨[88205, 3], [78831], .contexts [
        ⟨49176, true, false, [], [3]⟩,
        ⟨20, false, false, [78831], []⟩,
        ⟨5121, false, false, [], []⟩
      ]⟩,
    ⟨[88205], [88205], .contexts []⟩,
    ⟨[88205], [88205], .contexts []⟩,
    ⟨[78831, 3], [88205], .contexts [
        ⟨49176, false, false, [], []⟩,
        ⟨49178, false, false, [], []⟩,
        ⟨49179, false, false, [], []⟩,
        ⟨49179, false, false, [], []⟩
      ]⟩,
    ⟨[22505], [19093, 20771], .source 11317⟩,
    ⟨[22507], [22505, 20773], .source 11318⟩,
    ⟨[22509], [22507, 22215], .source 11319⟩,
    ⟨[88205, 1], [22509, 88025], .contexts [
        ⟨49180, true, false, [], [1]⟩,
        ⟨130, false, false, [78831], []⟩,
        ⟨133, false, false, [78831], []⟩,
        ⟨5554, false, false, [], [3, 1, 3]⟩,
        ⟨5546, false, false, [], [3, 1, 3]⟩,
        ⟨5547, false, false, [], [3, 1, 3]⟩,
        ⟨5547, false, false, [], [3, 1, 3]⟩,
        ⟨36934, false, false, [], [1, 3]⟩,
        ⟨42698, false, false, [19093], [1, 3]⟩,
        ⟨49181, true, false, [], [85259, 1, 3]⟩,
        ⟨42690, false, false, [22505], [3]⟩,
        ⟨49182, true, false, [], [83325, 3]⟩,
        ⟨48133, false, false, [22507], []⟩,
        ⟨49183, true, false, [], [88025]⟩,
        ⟨48139, false, false, [22509], []⟩
      ]⟩,
    ⟨[88205, 1], [22509, 88025], .contexts [
        ⟨49184, false, false, [], []⟩,
        ⟨13, true, false, [], [22509, 88025]⟩
      ]⟩,
    ⟨[22511], [22508], .source 11320⟩,
    ⟨[88025, 1], [22511, 88205], .contexts [
        ⟨49185, true, false, [22508], [1]⟩,
        ⟨8, false, false, [22508, 88205], []⟩,
        ⟨49186, true, false, [], [88205]⟩
      ]⟩,
    ⟨[315, 88205], [315, 88205], .contexts []⟩,
    ⟨[315, 88205], [315, 88205], .contexts []⟩,
    ⟨[88205, 5], [88205, 5], .contexts []⟩,
    ⟨[88205], [88205], .contexts []⟩,
    ⟨[88205, 5], [315, 88205], .contexts [
        ⟨49190, false, false, [], []⟩,
        ⟨49180, true, false, [], [5]⟩,
        ⟨871, false, false, [78831], []⟩,
        ⟨873, false, false, [78831], []⟩,
        ⟨5136, false, false, [], [3, 5, 3]⟩,
        ⟨5434, false, false, [], [5, 3]⟩,
        ⟨5105, false, false, [], [5, 3]⟩,
        ⟨5106, false, false, [], [5, 3]⟩,
        ⟨5106, false, false, [], [5, 3]⟩,
        ⟨5117, false, false, [315], [3]⟩,
        ⟨49176, false, false, [315], []⟩,
        ⟨49188, false, false, [], []⟩,
        ⟨49189, false, false, [], []⟩,
        ⟨49191, false, false, [315], []⟩,
        ⟨1689, true, false, [], [88205]⟩
      ]⟩,
    ⟨[88205, 7], [88205, 7], .contexts []⟩,
    ⟨[88205, 7], [82877], .contexts [
        ⟨49193, false, false, [], []⟩,
        ⟨49180, true, false, [], [7]⟩,
        ⟨140, false, false, [78831], []⟩,
        ⟨141, false, false, [78831], []⟩,
        ⟨5135, false, false, [], [3]⟩,
        ⟨39045, false, false, [], []⟩,
        ⟨17791, false, false, [], []⟩,
        ⟨17792, false, false, [], []⟩,
        ⟨17792, false, false, [], []⟩,
        ⟨36025, false, false, [], []⟩,
        ⟨36026, false, false, [], []⟩
      ]⟩,
    ⟨[88205, 9], [88205, 9], .contexts []⟩,
    ⟨[88205, 9], [84613], .contexts [
        ⟨49195, false, false, [], []⟩,
        ⟨49180, true, false, [], [9]⟩,
        ⟨669, false, false, [78831], []⟩,
        ⟨670, false, false, [78831], []⟩,
        ⟨19345, false, false, [], [3]⟩,
        ⟨19331, false, false, [], [3]⟩,
        ⟨19332, false, false, [], [3]⟩,
        ⟨19332, false, false, [], [3]⟩,
        ⟨27859, false, false, [], []⟩,
        ⟨27860, false, false, [], []⟩,
        ⟨27861, false, false, [], []⟩,
        ⟨27861, false, false, [], []⟩,
        ⟨47415, false, false, [], []⟩,
        ⟨47416, false, false, [], []⟩
      ]⟩,
    ⟨[84613, 9], [88205], .contexts [
        ⟨49196, true, false, [], [9]⟩,
        ⟨46, false, false, [88205], []⟩,
        ⟨49179, false, false, [], []⟩
      ]⟩,
    ⟨[1075, 88205], [1075, 88205], .contexts []⟩,
    ⟨[1075, 88205], [1075, 88205], .contexts []⟩,
    ⟨[88205, 13], [88205, 13], .contexts []⟩,
    ⟨[88205, 13], [1075, 88205], .contexts [
        ⟨49200, false, false, [], []⟩,
        ⟨49180, true, false, [], [13]⟩,
        ⟨147, false, false, [78831], []⟩,
        ⟨148, false, false, [78831], []⟩,
        ⟨5140, false, false, [], [3]⟩,
        ⟨49176, false, false, [1075], []⟩,
        ⟨49198, false, false, [], []⟩,
        ⟨49199, false, false, [], []⟩,
        ⟨49191, false, false, [1075], []⟩,
        ⟨4778, true, false, [], [88205]⟩
      ]⟩,
    ⟨[88205, 15], [22199, 88029], .contexts [
        ⟨49180, true, false, [], [15]⟩,
        ⟨151, false, false, [78831], []⟩,
        ⟨152, false, false, [78831], []⟩,
        ⟨15336, false, false, [], [3]⟩,
        ⟨15312, false, false, [], [3]⟩,
        ⟨15313, false, false, [], [3]⟩,
        ⟨15313, false, false, [], [3]⟩,
        ⟨48079, false, false, [], []⟩,
        ⟨48080, false, false, [], []⟩,
        ⟨48081, false, false, [], []⟩,
        ⟨48081, false, false, [], []⟩,
        ⟨48085, false, false, [], []⟩,
        ⟨48087, false, false, [], []⟩
      ]⟩,
    ⟨[88207], [82669, 3], .source 44168⟩,
    ⟨[82669, 3], [88207], .contexts [
        ⟨49203, true, false, [], []⟩
      ]⟩,
    ⟨[88207, 3], [82669], .contexts [
        ⟨49204, true, false, [], [3]⟩,
        ⟨20, false, false, [82669], []⟩,
        ⟨15155, false, false, [], []⟩
      ]⟩,
    ⟨[88207], [88207], .contexts []⟩,
    ⟨[88207], [88207], .contexts []⟩,
    ⟨[82669, 3], [88207], .contexts [
        ⟨49204, false, false, [], []⟩,
        ⟨49206, false, false, [], []⟩,
        ⟨49207, false, false, [], []⟩,
        ⟨49207, false, false, [], []⟩
      ]⟩,
    ⟨[16119, 83329], [16119, 83329], .contexts []⟩,
    ⟨[16119, 83329], [16119, 83329], .contexts []⟩,
    ⟨[88207, 7], [16119, 83329], .contexts [
        ⟨49208, true, false, [], [7]⟩,
        ⟨140, false, false, [82669], []⟩,
        ⟨141, false, false, [82669], []⟩,
        ⟨15152, false, false, [], [3]⟩,
        ⟨15135, false, false, [], [3]⟩,
        ⟨15136, false, false, [], [3]⟩,
        ⟨15136, false, false, [], [3]⟩,
        ⟨20486, false, false, [], []⟩,
        ⟨49209, false, false, [], []⟩,
        ⟨49210, false, false, [], []⟩,
        ⟨49210, false, false, [], []⟩,
        ⟨20490, false, false, [16119], []⟩,
        ⟨13, true, false, [], [16119, 83329]⟩
      ]⟩,
    ⟨[21715, 87803], [21715, 87803], .contexts []⟩,
    ⟨[21715, 87803], [21715, 87803], .contexts []⟩,
    ⟨[88207, 9], [88207, 9], .contexts []⟩,
    ⟨[88207, 9], [21715, 87803], .contexts [
        ⟨49214, false, false, [], []⟩,
        ⟨49208, true, false, [], [9]⟩,
        ⟨669, false, false, [82669], []⟩,
        ⟨670, false, false, [82669], []⟩,
        ⟨17018, false, false, [], [3]⟩,
        ⟨16998, false, false, [], [3]⟩,
        ⟨16999, false, false, [], [3]⟩,
        ⟨16999, false, false, [], [3]⟩,
        ⟨46161, false, false, [], []⟩,
        ⟨49212, false, false, [], []⟩,
        ⟨49213, false, false, [], []⟩,
        ⟨49213, false, false, [], []⟩,
        ⟨46179, false, false, [21715], []⟩,
        ⟨13, true, false, [], [21715, 87803]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 769. -/
def y322TCIndexRaw769 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[11661, 82839], [11661, 82839], .contexts []⟩,
    ⟨[11661, 82839], [11661, 82839], .contexts []⟩,
    ⟨[22513], [11661, 22317], .source 11321⟩,
    ⟨[88207, 11], [88207, 11], .contexts []⟩,
    ⟨[88207, 11], [22513, 88203], .contexts [
        ⟨49219, false, false, [], []⟩,
        ⟨49208, true, false, [], [11]⟩,
        ⟨144, false, false, [82669], []⟩,
        ⟨145, false, false, [82669], []⟩,
        ⟨17322, false, false, [], [3]⟩,
        ⟨49216, false, false, [], [3]⟩,
        ⟨49217, false, false, [], [3]⟩,
        ⟨49217, false, false, [], [3]⟩,
        ⟨48705, false, false, [11661], []⟩,
        ⟨49218, true, false, [], [88203]⟩,
        ⟨48712, false, false, [22513], []⟩,
        ⟨13, true, false, [], [22513, 88203]⟩
      ]⟩,
    ⟨[22515], [22512], .source 11322⟩,
    ⟨[2575, 88207], [2575, 88207], .contexts []⟩,
    ⟨[2575, 88207], [2575, 88207], .contexts []⟩,
    ⟨[88207, 13], [88207, 13], .contexts []⟩,
    ⟨[88207], [88207], .contexts []⟩,
    ⟨[88207, 13], [2575, 88207], .contexts [
        ⟨49224, false, false, [], []⟩,
        ⟨49208, true, false, [], [13]⟩,
        ⟨147, false, false, [82669], []⟩,
        ⟨148, false, false, [82669], []⟩,
        ⟨15169, false, false, [], [3]⟩,
        ⟨15171, false, false, [], [3]⟩,
        ⟨15167, false, false, [], [3]⟩,
        ⟨15168, false, false, [], [3]⟩,
        ⟨15168, false, false, [], [3]⟩,
        ⟨49204, false, false, [2575], []⟩,
        ⟨49222, false, false, [], []⟩,
        ⟨49223, false, false, [], []⟩,
        ⟨49225, false, false, [2575], []⟩,
        ⟨5618, true, false, [], [88207]⟩
      ]⟩,
    ⟨[16221, 83375], [16221, 83375], .contexts []⟩,
    ⟨[16221, 83375], [16221, 83375], .contexts []⟩,
    ⟨[88207, 15], [88207, 15], .contexts []⟩,
    ⟨[88207, 15], [16221, 83375], .contexts [
        ⟨49229, false, false, [], []⟩,
        ⟨49208, true, false, [], [15]⟩,
        ⟨151, false, false, [82669], []⟩,
        ⟨152, false, false, [82669], []⟩,
        ⟨15173, false, false, [], [3]⟩,
        ⟨15174, false, false, [], [3]⟩,
        ⟨5533, false, false, [], [3]⟩,
        ⟨5534, false, false, [], [3]⟩,
        ⟨5534, false, false, [], [3]⟩,
        ⟨21081, false, false, [], []⟩,
        ⟨49227, false, false, [], []⟩,
        ⟨49228, false, false, [], []⟩,
        ⟨49228, false, false, [], []⟩,
        ⟨32865, false, false, [16221], []⟩,
        ⟨32841, true, false, [], [83375]⟩
      ]⟩,
    ⟨[83375, 15], [16219, 88207], .contexts [
        ⟨49230, true, false, [16220], [15]⟩,
        ⟨1, false, false, [16220, 88207], []⟩,
        ⟨32470, true, false, [], [88207]⟩
      ]⟩,
    ⟨[88209], [88207, 5], .source 44169⟩,
    ⟨[88207, 5], [88209], .contexts [
        ⟨49232, true, false, [], []⟩
      ]⟩,
    ⟨[88209, 5], [88207], .contexts [
        ⟨49233, true, false, [], [5]⟩,
        ⟨28, false, false, [88207], []⟩,
        ⟨49207, false, false, [], []⟩
      ]⟩,
    ⟨[88209], [88209], .contexts []⟩,
    ⟨[88207, 5], [88209], .contexts [
        ⟨49233, false, false, [], []⟩,
        ⟨49235, false, false, [], []⟩,
        ⟨49235, false, false, [], []⟩
      ]⟩,
    ⟨[22517], [11661, 11217], .source 11323⟩,
    ⟨[22519], [22517, 15229], .source 11324⟩,
    ⟨[88209, 3], [22519, 82663], .contexts [
        ⟨49236, true, false, [], [3]⟩,
        ⟨166, false, false, [88207], []⟩,
        ⟨169, false, false, [88207], []⟩,
        ⟨49205, false, false, [], [5, 3, 5]⟩,
        ⟨15154, false, false, [], [5, 3, 5]⟩,
        ⟨15155, false, false, [], [5, 3, 5]⟩,
        ⟨15155, false, false, [], [5, 3, 5]⟩,
        ⟨15164, false, false, [], [3, 5]⟩,
        ⟨15161, false, false, [], [3, 5]⟩,
        ⟨15162, false, false, [], [3, 5]⟩,
        ⟨15162, false, false, [], [3, 5]⟩,
        ⟨15013, false, false, [11661], [5]⟩,
        ⟨49237, true, false, [], [79381, 5]⟩,
        ⟨15100, false, false, [22517], []⟩,
        ⟨49238, true, false, [], [82663]⟩,
        ⟨15102, false, false, [22519], []⟩
      ]⟩,
    ⟨[88209, 3], [22519, 82663], .contexts [
        ⟨49239, false, false, [], []⟩,
        ⟨13, true, false, [], [22519, 82663]⟩
      ]⟩,
    ⟨[22521], [22518], .source 11325⟩,
    ⟨[82663, 3], [22521, 88209], .contexts [
        ⟨49240, true, false, [22518], [3]⟩,
        ⟨20, false, false, [22518, 88209], []⟩,
        ⟨49241, true, false, [], [88209]⟩
      ]⟩,
    ⟨[22523], [21715, 21727], .source 11326⟩,
    ⟨[88209, 9], [22523, 84485], .contexts [
        ⟨49236, true, false, [], [9]⟩,
        ⟨1265, false, false, [88207], []⟩,
        ⟨1266, false, false, [88207], []⟩,
        ⟨49214, false, false, [], [5]⟩,
        ⟨49215, false, false, [], [5]⟩,
        ⟨49212, false, false, [], [5]⟩,
        ⟨49213, false, false, [], [5]⟩,
        ⟨49213, false, false, [], [5]⟩,
        ⟨46187, false, false, [21715], []⟩,
        ⟨49243, true, false, [], [84485]⟩,
        ⟨27040, false, false, [22523], []⟩,
        ⟨13, true, false, [], [22523, 84485]⟩
      ]⟩,
    ⟨[22525], [22522], .source 11327⟩,
    ⟨[84485, 9], [22525, 88209], .contexts [
        ⟨49244, true, false, [22522], [9]⟩,
        ⟨46, false, false, [22522, 88209], []⟩,
        ⟨49245, true, false, [], [88209]⟩
      ]⟩,
    ⟨[22513, 88203], [22513, 88203], .contexts []⟩,
    ⟨[22527], [22513, 22321], .source 11328⟩,
    ⟨[88209, 11], [88209, 11], .contexts []⟩,
    ⟨[22527], [22527], .contexts []⟩,
    ⟨[22527], [22527], .contexts []⟩,
    ⟨[22527], [22527], .contexts [
        ⟨13, false, false, [], [22527]⟩,
        ⟨49250, false, false, [], []⟩,
        ⟨49251, false, false, [], []⟩
      ]⟩,
    ⟨[88209, 11], [22527, 86223], .contexts [
        ⟨49249, false, false, [], []⟩,
        ⟨49236, true, false, [], [11]⟩,
        ⟨174, false, false, [88207], []⟩,
        ⟨175, false, false, [88207], []⟩,
        ⟨49219, false, false, [], [5]⟩,
        ⟨49220, false, false, [], [5]⟩,
        ⟨49247, false, false, [], [5]⟩,
        ⟨49247, false, false, [], [5]⟩,
        ⟨48717, false, false, [22513], []⟩,
        ⟨49248, true, false, [], [86223]⟩,
        ⟨35815, false, false, [22527], []⟩,
        ⟨49252, true, false, [], [86223]⟩
      ]⟩,
    ⟨[22529], [22526], .source 11329⟩,
    ⟨[88209, 13], [2575, 88209], .contexts [
        ⟨49236, true, false, [], [13]⟩,
        ⟨179, false, false, [88207], []⟩,
        ⟨180, false, false, [88207], []⟩,
        ⟨49224, false, false, [], [5]⟩,
        ⟨49226, false, false, [], [5]⟩,
        ⟨49222, false, false, [], [5]⟩,
        ⟨49223, false, false, [], [5]⟩,
        ⟨49223, false, false, [], [5]⟩,
        ⟨49233, false, false, [2575], []⟩,
        ⟨5618, true, false, [], [88209]⟩
      ]⟩,
    ⟨[16221, 83373], [16221, 83373], .contexts []⟩,
    ⟨[16221, 83373], [16221, 83373], .contexts []⟩,
    ⟨[88209, 15], [88209, 15], .contexts []⟩,
    ⟨[88209, 15], [16221, 83373], .contexts [
        ⟨49258, false, false, [], []⟩,
        ⟨49236, true, false, [], [15]⟩,
        ⟨184, false, false, [88207], []⟩,
        ⟨185, false, false, [88207], []⟩,
        ⟨49229, false, false, [], [5]⟩,
        ⟨49230, false, false, [], [5]⟩,
        ⟨49227, false, false, [], [5]⟩,
        ⟨49228, false, false, [], [5]⟩,
        ⟨49228, false, false, [], [5]⟩,
        ⟨21069, false, false, [16221], []⟩,
        ⟨49256, false, false, [], []⟩,
        ⟨49257, false, false, [], []⟩,
        ⟨32429, false, false, [16221], []⟩,
        ⟨32841, true, false, [], [83373]⟩
      ]⟩,
    ⟨[88211], [88209, 1], .source 44170⟩,
    ⟨[88209, 1], [88211], .contexts [
        ⟨49260, true, false, [], []⟩
      ]⟩,
    ⟨[88211, 1], [88209], .contexts [
        ⟨49261, true, false, [], [1]⟩,
        ⟨8, false, false, [88209], []⟩,
        ⟨49235, false, false, [], []⟩
      ]⟩,
    ⟨[88211], [88211], .contexts []⟩,
    ⟨[88211], [88211], .contexts []⟩,
    ⟨[88209, 1], [88211], .contexts [
        ⟨49261, false, false, [], []⟩,
        ⟨49263, false, false, [], []⟩,
        ⟨49264, false, false, [], []⟩,
        ⟨49264, false, false, [], []⟩
      ]⟩,
    ⟨[22527, 86223], [22527, 86223], .contexts []⟩,
    ⟨[22527, 86223], [22527, 86223], .contexts []⟩,
    ⟨[88211, 11], [22527, 86221], .contexts [
        ⟨49265, true, false, [], [11]⟩,
        ⟨110, false, false, [88209], []⟩,
        ⟨111, false, false, [88209], []⟩,
        ⟨49249, false, false, [], [1]⟩,
        ⟨49253, false, false, [], [1]⟩,
        ⟨49266, false, false, [], [1]⟩,
        ⟨49267, false, false, [], [1]⟩,
        ⟨49267, false, false, [], [1]⟩,
        ⟨35698, false, false, [22527], []⟩,
        ⟨48741, false, false, [22527], []⟩,
        ⟨49252, true, false, [], [86221]⟩
      ]⟩,
    ⟨[86221, 11], [22529, 88211], .contexts [
        ⟨49268, true, false, [22526], [11]⟩,
        ⟨53, false, false, [22526, 88211], []⟩,
        ⟨49254, true, false, [], [88211]⟩
      ]⟩,
    ⟨[88211, 15], [88211, 15], .contexts []⟩,
    ⟨[88211, 15], [21103, 85495], .contexts [
        ⟨49270, false, false, [], []⟩,
        ⟨49265, true, false, [], [15]⟩,
        ⟨121, false, false, [88209], []⟩,
        ⟨122, false, false, [88209], []⟩,
        ⟨49258, false, false, [], [1]⟩,
        ⟨49259, false, false, [], [1]⟩,
        ⟨49256, false, false, [], [1]⟩,
        ⟨49257, false, false, [], [1]⟩,
        ⟨49257, false, false, [], [1]⟩,
        ⟨32431, false, false, [16221], []⟩,
        ⟨44224, false, false, [], []⟩,
        ⟨44225, false, false, [], []⟩,
        ⟨44227, false, false, [], []⟩,
        ⟨32437, false, false, [21103], []⟩,
        ⟨44234, true, false, [], [85495]⟩
      ]⟩,
    ⟨[85495, 15], [21105, 88211], .contexts [
        ⟨49271, true, false, [21102], [15]⟩,
        ⟨1, false, false, [21102, 88211], []⟩,
        ⟨44236, true, false, [], [88211]⟩
      ]⟩,
    ⟨[88213], [88211, 9], .source 44171⟩,
    ⟨[88211, 9], [88213], .contexts [
        ⟨49273, true, false, [], []⟩
      ]⟩,
    ⟨[88213, 9], [88211], .contexts [
        ⟨49274, true, false, [], [9]⟩,
        ⟨46, false, false, [88211], []⟩,
        ⟨49264, false, false, [], []⟩
      ]⟩,
    ⟨[88213], [88213], .contexts []⟩,
    ⟨[21103, 85495], [21103, 85495], .contexts []⟩,
    ⟨[21103, 85495], [21103, 85495], .contexts []⟩,
    ⟨[21103, 85721], [21103, 85721], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 770. -/
def y322TCIndexRaw770 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[21103, 85721], [21103, 85721], .contexts []⟩,
    ⟨[88213, 15], [88213, 15], .contexts []⟩,
    ⟨[88213, 15], [21103, 85721], .contexts [
        ⟨49281, false, false, [], []⟩,
        ⟨49276, true, false, [], [15]⟩,
        ⟨49276, true, false, [], [15]⟩,
        ⟨49274, true, false, [], [15]⟩,
        ⟨205, false, false, [88211], []⟩,
        ⟨206, false, false, [88211], []⟩,
        ⟨49270, false, false, [], [9]⟩,
        ⟨49271, false, false, [], [9]⟩,
        ⟨49277, false, false, [], [9]⟩,
        ⟨49278, false, false, [], [9]⟩,
        ⟨49278, false, false, [], [9]⟩,
        ⟨33211, false, false, [21103], []⟩,
        ⟨49279, false, false, [], []⟩,
        ⟨49280, false, false, [], []⟩,
        ⟨39122, false, false, [21103], []⟩,
        ⟨44234, true, false, [], [85721]⟩
      ]⟩,
    ⟨[88215], [88213, 11], .source 44172⟩,
    ⟨[88213, 11], [88215], .contexts [
        ⟨49283, true, false, [], []⟩
      ]⟩,
    ⟨[88215, 11], [88213], .contexts [
        ⟨49284, true, false, [], [11]⟩,
        ⟨53, false, false, [88213], []⟩,
        ⟨49276, false, false, [], []⟩
      ]⟩,
    ⟨[88215], [88215], .contexts []⟩,
    ⟨[88215], [88215], .contexts []⟩,
    ⟨[21103, 85723], [21103, 85723], .contexts []⟩,
    ⟨[21103, 85723], [21103, 85723], .contexts []⟩,
    ⟨[88215, 15], [88215, 15], .contexts []⟩,
    ⟨[85723], [85723], .contexts []⟩,
    ⟨[88215, 15], [21103, 85723], .contexts [
        ⟨49290, false, false, [], []⟩,
        ⟨49287, true, false, [], [15]⟩,
        ⟨49287, true, false, [], [15]⟩,
        ⟨49286, true, false, [], [15]⟩,
        ⟨49284, true, false, [], [15]⟩,
        ⟨231, false, false, [88213], []⟩,
        ⟨232, false, false, [88213], []⟩,
        ⟨49281, false, false, [], [11]⟩,
        ⟨49282, false, false, [], [11]⟩,
        ⟨49279, false, false, [], [11]⟩,
        ⟨49280, false, false, [], [11]⟩,
        ⟨49280, false, false, [], [11]⟩,
        ⟨33226, false, false, [21103], []⟩,
        ⟨49288, false, false, [], []⟩,
        ⟨49289, false, false, [], []⟩,
        ⟨49291, false, false, [21103], []⟩,
        ⟨44234, true, false, [], [85723]⟩
      ]⟩,
    ⟨[85723, 15], [21105, 88215], .contexts [
        ⟨49292, true, false, [21102], [15]⟩,
        ⟨1, false, false, [21102, 88215], []⟩,
        ⟨44236, true, false, [], [88215]⟩
      ]⟩,
    ⟨[88215, 15], [21103, 85723], .contexts [
        ⟨49290, false, false, [], []⟩,
        ⟨49292, false, false, [], []⟩,
        ⟨49288, false, false, [], []⟩,
        ⟨49289, false, false, [], []⟩,
        ⟨49289, false, false, [], []⟩
      ]⟩,
    ⟨[22531], [21103, 19523], .source 11330⟩,
    ⟨[22533], [22531, 17269], .source 11331⟩,
    ⟨[83583, 7], [83583, 7], .contexts []⟩,
    ⟨[88215], [88215], .contexts []⟩,
    ⟨[22535], [22532], .source 11332⟩,
    ⟨[22532], [22532], .contexts []⟩,
    ⟨[83583, 7], [22535, 88215], .contexts [
        ⟨49297, false, false, [], []⟩,
        ⟨49296, false, false, [22532], [83583, 7]⟩,
        ⟨27171, true, false, [22532, 22531], [7]⟩,
        ⟨49295, false, false, [22532], [84497, 15, 7]⟩,
        ⟨39139, true, false, [22532, 21103], [15, 7]⟩,
        ⟨49294, true, false, [22532], [7, 15, 7]⟩,
        ⟨2651, false, false, [22532, 88215], []⟩,
        ⟨49298, false, false, [22532], []⟩,
        ⟨49300, true, false, [], [88215]⟩,
        ⟨49300, true, false, [], [88215]⟩,
        ⟨49299, true, false, [], [88215]⟩
      ]⟩,
    ⟨[88215, 7], [22533, 83583], .contexts [
        ⟨49301, true, false, [22534], [7]⟩,
        ⟨38, false, false, [22534, 83583], []⟩,
        ⟨49299, false, true, [], [83583]⟩
      ]⟩,
    ⟨[88217], [88215, 1], .source 44173⟩,
    ⟨[88215, 1], [88217], .contexts [
        ⟨49303, true, false, [], []⟩
      ]⟩,
    ⟨[88217, 1], [88215], .contexts [
        ⟨49304, true, false, [], [1]⟩,
        ⟨8, false, false, [88215], []⟩,
        ⟨49287, false, false, [], []⟩
      ]⟩,
    ⟨[88217], [88217], .contexts []⟩,
    ⟨[88217], [88217], .contexts []⟩,
    ⟨[88215, 1], [88217], .contexts [
        ⟨49304, false, false, [], []⟩,
        ⟨49306, false, false, [], []⟩,
        ⟨49307, false, false, [], []⟩,
        ⟨49307, false, false, [], []⟩
      ]⟩,
    ⟨[22533, 83583], [22533, 83583], .contexts []⟩,
    ⟨[22533, 83583], [22533, 83583], .contexts []⟩,
    ⟨[22533, 83581], [22533, 83581], .contexts []⟩,
    ⟨[22533, 83581], [22533, 83581], .contexts []⟩,
    ⟨[88217, 7], [88217, 7], .contexts []⟩,
    ⟨[88217, 7], [22533, 83581], .contexts [
        ⟨49313, false, false, [], []⟩,
        ⟨49308, true, false, [], [7]⟩,
        ⟨104, false, false, [88215], []⟩,
        ⟨105, false, false, [88215], []⟩,
        ⟨49302, false, false, [], [1]⟩,
        ⟨49309, false, false, [], [1]⟩,
        ⟨49310, false, false, [], [1]⟩,
        ⟨49310, false, false, [], [1]⟩,
        ⟨22096, false, false, [22533], []⟩,
        ⟨49311, false, false, [], []⟩,
        ⟨49312, false, false, [], []⟩,
        ⟨26546, false, false, [22533], []⟩,
        ⟨13, true, false, [], [22533, 83581]⟩
      ]⟩,
    ⟨[83581, 7], [22535, 88217], .contexts [
        ⟨49314, true, false, [22532], [7]⟩,
        ⟨38, false, false, [22532, 88217], []⟩,
        ⟨49299, true, false, [], [88217]⟩
      ]⟩,
    ⟨[21103, 85725], [21103, 85725], .contexts []⟩,
    ⟨[21103, 85725], [21103, 85725], .contexts []⟩,
    ⟨[88217, 15], [21103, 85725], .contexts [
        ⟨49308, true, false, [], [15]⟩,
        ⟨121, false, false, [88215], []⟩,
        ⟨122, false, false, [88215], []⟩,
        ⟨49294, false, false, [], [1]⟩,
        ⟨33240, false, false, [21103], []⟩,
        ⟨49316, false, false, [], []⟩,
        ⟨49317, false, false, [], []⟩,
        ⟨33254, false, false, [21103], []⟩,
        ⟨44234, true, false, [], [85725]⟩
      ]⟩,
    ⟨[22537], [22533, 17171], .source 11333⟩,
    ⟨[22539], [22537, 22535], .source 11334⟩,
    ⟨[88217, 3], [88217, 3], .contexts []⟩,
    ⟨[88217], [88217], .contexts []⟩,
    ⟨[22541], [22538], .source 11335⟩,
    ⟨[22538], [22538], .contexts []⟩,
    ⟨[88217, 3], [22541, 88217], .contexts [
        ⟨49321, false, false, [], []⟩,
        ⟨49320, false, false, [22538], [88217, 3]⟩,
        ⟨49315, true, false, [22538, 22537], [3]⟩,
        ⟨49319, false, false, [22538], [83581, 7, 3]⟩,
        ⟨26548, true, false, [22538, 22533], [7, 3]⟩,
        ⟨49312, true, false, [22538], [3, 7, 3]⟩,
        ⟨49312, true, false, [22538], [3, 7, 3]⟩,
        ⟨49311, true, false, [22538], [3, 7, 3]⟩,
        ⟨49314, true, false, [22538], [3, 7, 3]⟩,
        ⟨49313, true, false, [22538], [3, 7, 3]⟩,
        ⟨40656, false, false, [22538, 88217], []⟩,
        ⟨49322, false, false, [22538], []⟩,
        ⟨49324, true, false, [], [88217]⟩,
        ⟨49324, true, false, [], [88217]⟩,
        ⟨49323, true, false, [], [88217]⟩
      ]⟩,
    ⟨[88219], [88217, 13], .source 44174⟩,
    ⟨[88217, 13], [88219], .contexts [
        ⟨49326, true, false, [], []⟩
      ]⟩,
    ⟨[88219, 13], [88217], .contexts [
        ⟨49327, true, false, [], [13]⟩,
        ⟨59, false, false, [88217], []⟩,
        ⟨49307, false, false, [], []⟩
      ]⟩,
    ⟨[88219], [88219], .contexts []⟩,
    ⟨[88219], [88219], .contexts []⟩,
    ⟨[22541, 88217], [22541, 88217], .contexts []⟩,
    ⟨[22541, 88217], [22541, 88217], .contexts []⟩,
    ⟨[22541, 88219], [22541, 88219], .contexts []⟩,
    ⟨[22541, 88219], [22541, 88219], .contexts []⟩,
    ⟨[22541, 88219], [22541, 88219], .contexts []⟩,
    ⟨[88219, 3], [88219, 3], .contexts []⟩,
    ⟨[88219], [88219], .contexts []⟩,
    ⟨[22541], [22541], .contexts [
        ⟨13, false, false, [], [22541]⟩
      ]⟩,
    ⟨[88221], [88219, 15], .source 44175⟩,
    ⟨[88219, 15], [88221], .contexts [
        ⟨49339, true, false, [], []⟩
      ]⟩,
    ⟨[88221, 15], [88219], .contexts [
        ⟨49340, true, false, [], [15]⟩,
        ⟨1, false, false, [88219], []⟩,
        ⟨49330, false, false, [], []⟩
      ]⟩,
    ⟨[88221], [88221], .contexts []⟩,
    ⟨[88221], [88221], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 771. -/
def y322TCIndexRaw771 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88219, 15], [88221], .contexts [
        ⟨49340, false, false, [], []⟩,
        ⟨49342, false, false, [], []⟩,
        ⟨49343, false, false, [], []⟩,
        ⟨49343, false, false, [], []⟩
      ]⟩,
    ⟨[22541, 88221], [22541, 88221], .contexts []⟩,
    ⟨[22541, 88221], [22541, 88221], .contexts []⟩,
    ⟨[88219, 3, 15], [22541, 88221], .contexts [
        ⟨49336, false, false, [], [15]⟩,
        ⟨49336, false, false, [], [15]⟩,
        ⟨49330, true, false, [], [3, 15]⟩,
        ⟨49330, true, false, [], [3, 15]⟩,
        ⟨49329, true, false, [], [3, 15]⟩,
        ⟨49327, true, false, [], [3, 15]⟩,
        ⟨63, false, false, [88217], [15]⟩,
        ⟨65, false, false, [88217], [15]⟩,
        ⟨49321, false, false, [], [13, 15]⟩,
        ⟨49325, false, false, [], [13, 15]⟩,
        ⟨49331, false, false, [], [13, 15]⟩,
        ⟨49332, false, false, [], [13, 15]⟩,
        ⟨49332, false, false, [], [13, 15]⟩,
        ⟨49327, false, false, [22541], [15]⟩,
        ⟨49333, false, false, [], [15]⟩,
        ⟨49334, false, false, [], [15]⟩,
        ⟨49335, false, false, [], [15]⟩,
        ⟨49337, false, false, [22541], [15]⟩,
        ⟨49338, true, false, [], [88219, 15]⟩,
        ⟨49333, false, false, [], [15]⟩,
        ⟨49335, false, false, [], [15]⟩,
        ⟨49335, false, false, [], [15]⟩,
        ⟨49340, false, false, [22541], []⟩,
        ⟨49345, false, false, [], []⟩,
        ⟨49346, false, false, [], []⟩
      ]⟩,
    ⟨[22541, 88221], [22541, 88221], .contexts []⟩,
    ⟨[88221], [88221], .contexts []⟩,
    ⟨[88221, 3], [22541, 88221], .contexts [
        ⟨49344, true, false, [], [3]⟩,
        ⟨19, false, false, [88219], []⟩,
        ⟨22, false, false, [88219], []⟩,
        ⟨49347, false, false, [], []⟩,
        ⟨49348, false, false, [], []⟩,
        ⟨49349, false, false, [22541], []⟩,
        ⟨49338, true, false, [], [88221]⟩
      ]⟩,
    ⟨[21103, 85729], [21103, 85729], .contexts []⟩,
    ⟨[88221, 13], [21103, 85729], .contexts [
        ⟨49344, true, false, [], [13]⟩,
        ⟨259, false, false, [88219], []⟩,
        ⟨262, false, false, [88219], []⟩,
        ⟨49328, false, false, [], [15, 13, 15]⟩,
        ⟨49306, false, false, [], [15, 13, 15]⟩,
        ⟨49307, false, false, [], [15, 13, 15]⟩,
        ⟨49307, false, false, [], [15, 13, 15]⟩,
        ⟨49318, false, false, [], [13, 15]⟩,
        ⟨49316, false, false, [], [13, 15]⟩,
        ⟨49317, false, false, [], [13, 15]⟩,
        ⟨49317, false, false, [], [13, 15]⟩,
        ⟨33263, false, false, [21103], [15]⟩,
        ⟨33279, false, false, [21103], []⟩,
        ⟨49351, false, false, [], []⟩,
        ⟨33288, false, false, [21103], []⟩
      ]⟩,
    ⟨[88221, 13], [21103, 85729], .contexts [
        ⟨49352, false, false, [], []⟩,
        ⟨44234, true, false, [], [85729]⟩
      ]⟩,
    ⟨[85729, 13], [21105, 88221], .contexts [
        ⟨49353, true, false, [21102], [13]⟩,
        ⟨59, false, false, [21102, 88221], []⟩,
        ⟨44236, true, false, [], [88221]⟩
      ]⟩,
    ⟨[88223], [88221, 1], .source 44176⟩,
    ⟨[88221, 1], [88223], .contexts [
        ⟨49355, true, false, [], []⟩
      ]⟩,
    ⟨[88223, 1], [88221], .contexts [
        ⟨49356, true, false, [], [1]⟩,
        ⟨8, false, false, [88221], []⟩,
        ⟨49343, false, false, [], []⟩
      ]⟩,
    ⟨[88225], [88223, 3], .source 44177⟩,
    ⟨[88223, 3], [88225], .contexts [
        ⟨49358, true, false, [], []⟩
      ]⟩,
    ⟨[88223], [88223], .contexts []⟩,
    ⟨[88225, 3], [88223], .contexts [
        ⟨49359, true, false, [], [3]⟩,
        ⟨20, false, false, [88223], []⟩,
        ⟨49360, false, false, [], []⟩
      ]⟩,
    ⟨[88225], [88225], .contexts []⟩,
    ⟨[88225], [88225], .contexts []⟩,
    ⟨[88223, 3], [88225], .contexts [
        ⟨49359, false, false, [], []⟩,
        ⟨49362, false, false, [], []⟩,
        ⟨49363, false, false, [], []⟩,
        ⟨49363, false, false, [], []⟩
      ]⟩,
    ⟨[22541, 88223], [22541, 88223], .contexts []⟩,
    ⟨[22541, 88223], [22541, 88223], .contexts []⟩,
    ⟨[22541, 88223], [22541, 88223], .contexts []⟩,
    ⟨[22541, 88225], [22541, 88225], .contexts []⟩,
    ⟨[22541, 88225], [22541, 88225], .contexts []⟩,
    ⟨[22541, 88225], [22541, 88225], .contexts []⟩,
    ⟨[88225, 1], [88225, 1], .contexts []⟩,
    ⟨[88225], [88225], .contexts []⟩,
    ⟨[88225, 1], [22541, 88225], .contexts [
        ⟨49371, false, false, [], []⟩,
        ⟨49364, true, false, [], [1]⟩,
        ⟨130, false, false, [88223], []⟩,
        ⟨133, false, false, [88223], []⟩,
        ⟨49357, false, false, [], [3, 1, 3]⟩,
        ⟨49342, false, false, [], [3, 1, 3]⟩,
        ⟨49343, false, false, [], [3, 1, 3]⟩,
        ⟨49343, false, false, [], [3, 1, 3]⟩,
        ⟨49350, false, false, [], [1, 3]⟩,
        ⟨49345, false, false, [], [1, 3]⟩,
        ⟨49348, false, false, [], [1, 3]⟩,
        ⟨49348, false, false, [], [1, 3]⟩,
        ⟨49356, false, false, [22541], [3]⟩,
        ⟨49365, false, false, [], [3]⟩,
        ⟨49366, false, false, [], [3]⟩,
        ⟨49367, false, false, [], [3]⟩,
        ⟨49359, false, false, [22541], []⟩,
        ⟨49368, false, false, [], []⟩,
        ⟨49369, false, false, [], []⟩,
        ⟨49370, false, false, [], []⟩,
        ⟨49372, false, false, [22541], []⟩
      ]⟩,
    ⟨[88225, 1], [22541, 88225], .contexts [
        ⟨49373, false, false, [], []⟩,
        ⟨49338, true, false, [], [88225]⟩
      ]⟩,
    ⟨[88227], [88225, 5], .source 44178⟩,
    ⟨[88225, 5], [88227], .contexts [
        ⟨49375, true, false, [], []⟩
      ]⟩,
    ⟨[88225, 5], [88227], .contexts [
        ⟨49376, false, false, [], []⟩
      ]⟩,
    ⟨[88227], [88227], .contexts []⟩,
    ⟨[88227], [88227], .contexts []⟩,
    ⟨[88225, 1], [22541, 88225], .contexts [
        ⟨49371, false, false, [], []⟩,
        ⟨49374, false, false, [], []⟩,
        ⟨49368, false, false, [], []⟩,
        ⟨49370, false, false, [], []⟩,
        ⟨49370, false, false, [], []⟩
      ]⟩,
    ⟨[22541, 88227], [22541, 88227], .contexts []⟩,
    ⟨[22541, 88227], [22541, 88227], .contexts []⟩,
    ⟨[88229], [88227, 9], .source 44179⟩,
    ⟨[88227, 9], [88229], .contexts [
        ⟨49383, true, false, [], []⟩
      ]⟩,
    ⟨[88229, 9], [88227], .contexts [
        ⟨49384, true, false, [], [9]⟩,
        ⟨46, false, false, [88227], []⟩,
        ⟨49379, false, false, [], []⟩
      ]⟩,
    ⟨[88231], [88229, 11], .source 44180⟩,
    ⟨[88229, 11], [88231], .contexts [
        ⟨49386, true, false, [], []⟩
      ]⟩,
    ⟨[88229], [88229], .contexts []⟩,
    ⟨[88233], [88231, 1], .source 44181⟩,
    ⟨[88231, 1], [88233], .contexts [
        ⟨49389, true, false, [], []⟩
      ]⟩,
    ⟨[88231], [88231], .contexts []⟩,
    ⟨[88233, 1], [88231], .contexts [
        ⟨49390, true, false, [], [1]⟩,
        ⟨8, false, false, [88231], []⟩,
        ⟨49391, false, false, [], []⟩
      ]⟩,
    ⟨[88235], [88233, 13], .source 44182⟩,
    ⟨[88233, 13], [88235], .contexts [
        ⟨49393, true, false, [], []⟩
      ]⟩,
    ⟨[88233], [88233], .contexts []⟩,
    ⟨[88235, 13], [88233], .contexts [
        ⟨49394, true, false, [], [13]⟩,
        ⟨59, false, false, [88233], []⟩,
        ⟨49395, false, false, [], []⟩
      ]⟩,
    ⟨[88237], [88235, 15], .source 44183⟩,
    ⟨[88235, 15], [88237], .contexts [
        ⟨49397, true, false, [], []⟩
      ]⟩,
    ⟨[88235], [88235], .contexts []⟩,
    ⟨[88237, 15], [88235], .contexts [
        ⟨49398, true, false, [], [15]⟩,
        ⟨1, false, false, [88235], []⟩,
        ⟨49399, false, false, [], []⟩
      ]⟩,
    ⟨[88239], [88237, 1], .source 44184⟩,
    ⟨[88237, 1], [88239], .contexts [
        ⟨49401, true, false, [], []⟩
      ]⟩,
    ⟨[88237], [88237], .contexts []⟩,
    ⟨[88239, 1], [88237], .contexts [
        ⟨49402, true, false, [], [1]⟩,
        ⟨8, false, false, [88237], []⟩,
        ⟨49403, false, false, [], []⟩
      ]⟩,
    ⟨[88241], [88239, 3], .source 44185⟩,
    ⟨[88239, 3], [88241], .contexts [
        ⟨49405, true, false, [], []⟩
      ]⟩,
    ⟨[88239], [88239], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 772. -/
def y322TCIndexRaw772 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88241, 3], [88239], .contexts [
        ⟨49406, true, false, [], [3]⟩,
        ⟨20, false, false, [88239], []⟩,
        ⟨49407, false, false, [], []⟩
      ]⟩,
    ⟨[88243], [88241, 5], .source 44186⟩,
    ⟨[88241, 5], [88243], .contexts [
        ⟨49409, true, false, [], []⟩
      ]⟩,
    ⟨[88241], [88241], .contexts []⟩,
    ⟨[88243, 5], [88241], .contexts [
        ⟨49410, true, false, [], [5]⟩,
        ⟨28, false, false, [88241], []⟩,
        ⟨49411, false, false, [], []⟩
      ]⟩,
    ⟨[88245], [88243, 1], .source 44187⟩,
    ⟨[88243, 1], [88245], .contexts [
        ⟨49413, true, false, [], []⟩
      ]⟩,
    ⟨[88243], [88243], .contexts []⟩,
    ⟨[88245, 1], [88243], .contexts [
        ⟨49414, true, false, [], [1]⟩,
        ⟨8, false, false, [88243], []⟩,
        ⟨49415, false, false, [], []⟩
      ]⟩,
    ⟨[88247], [88245, 9], .source 44188⟩,
    ⟨[88245, 9], [88247], .contexts [
        ⟨49417, true, false, [], []⟩
      ]⟩,
    ⟨[88245], [88245], .contexts []⟩,
    ⟨[88247, 9], [88245], .contexts [
        ⟨49418, true, false, [], [9]⟩,
        ⟨46, false, false, [88245], []⟩,
        ⟨49419, false, false, [], []⟩
      ]⟩,
    ⟨[88249], [88247, 11], .source 44189⟩,
    ⟨[88247, 11], [88249], .contexts [
        ⟨49421, true, false, [], []⟩
      ]⟩,
    ⟨[88247], [88247], .contexts []⟩,
    ⟨[88249, 11], [88247], .contexts [
        ⟨49422, true, false, [], [11]⟩,
        ⟨53, false, false, [88247], []⟩,
        ⟨49423, false, false, [], []⟩
      ]⟩,
    ⟨[88251], [88249, 1], .source 44190⟩,
    ⟨[88249], [88249], .contexts []⟩,
    ⟨[88251, 1], [88249], .contexts [
        ⟨49425, false, false, [], [1]⟩,
        ⟨8, false, false, [88249], []⟩,
        ⟨49426, false, false, [], []⟩
      ]⟩,
    ⟨[88253], [88251, 13], .source 44191⟩,
    ⟨[88251], [88251], .contexts []⟩,
    ⟨[88253, 13], [88251], .contexts [
        ⟨49428, false, false, [], [13]⟩,
        ⟨59, false, false, [88251], []⟩,
        ⟨49429, false, false, [], []⟩
      ]⟩,
    ⟨[88255], [88253, 15], .source 44192⟩,
    ⟨[88253], [88253], .contexts []⟩,
    ⟨[88255, 15], [88253], .contexts [
        ⟨49431, false, false, [], [15]⟩,
        ⟨1, false, false, [88253], []⟩,
        ⟨49432, false, false, [], []⟩
      ]⟩,
    ⟨[88257], [88255, 1], .source 44193⟩,
    ⟨[88255, 1], [88257], .contexts [
        ⟨49434, true, false, [], []⟩
      ]⟩,
    ⟨[88255], [88255], .contexts []⟩,
    ⟨[88257, 1], [88255], .contexts [
        ⟨49435, true, false, [], [1]⟩,
        ⟨8, false, false, [88255], []⟩,
        ⟨49436, false, false, [], []⟩
      ]⟩,
    ⟨[88259], [88257, 3], .source 44194⟩,
    ⟨[88257, 3], [88259], .contexts [
        ⟨49438, true, false, [], []⟩
      ]⟩,
    ⟨[88257], [88257], .contexts []⟩,
    ⟨[88259, 3], [88257], .contexts [
        ⟨49439, true, false, [], [3]⟩,
        ⟨20, false, false, [88257], []⟩,
        ⟨49440, false, false, [], []⟩
      ]⟩,
    ⟨[88261], [88259, 5], .source 44195⟩,
    ⟨[88259, 5], [88261], .contexts [
        ⟨49442, true, false, [], []⟩
      ]⟩,
    ⟨[88259], [88259], .contexts []⟩,
    ⟨[88261, 5], [88259], .contexts [
        ⟨49443, true, false, [], [5]⟩,
        ⟨28, false, false, [88259], []⟩,
        ⟨49444, false, false, [], []⟩
      ]⟩,
    ⟨[88263], [88261, 1], .source 44196⟩,
    ⟨[88261, 1], [88263], .contexts [
        ⟨49446, true, false, [], []⟩
      ]⟩,
    ⟨[88261], [88261], .contexts []⟩,
    ⟨[88263, 1], [88261], .contexts [
        ⟨49447, true, false, [], [1]⟩,
        ⟨8, false, false, [88261], []⟩,
        ⟨49448, false, false, [], []⟩
      ]⟩,
    ⟨[88265], [88263, 9], .source 44197⟩,
    ⟨[88263, 9], [88265], .contexts [
        ⟨49450, true, false, [], []⟩
      ]⟩,
    ⟨[88263], [88263], .contexts []⟩,
    ⟨[88265, 9], [88263], .contexts [
        ⟨49451, true, false, [], [9]⟩,
        ⟨46, false, false, [88263], []⟩,
        ⟨49452, false, false, [], []⟩
      ]⟩,
    ⟨[88267], [88265, 11], .source 44198⟩,
    ⟨[88265], [88265], .contexts []⟩,
    ⟨[88267, 11], [88265], .contexts [
        ⟨49454, false, false, [], [11]⟩,
        ⟨53, false, false, [88265], []⟩,
        ⟨49455, false, false, [], []⟩
      ]⟩,
    ⟨[88269], [88267, 1], .source 44199⟩,
    ⟨[88267, 1], [88269], .contexts [
        ⟨49457, true, false, [], []⟩
      ]⟩,
    ⟨[88267], [88267], .contexts []⟩,
    ⟨[88269, 1], [88267], .contexts [
        ⟨49458, true, false, [], [1]⟩,
        ⟨8, false, false, [88267], []⟩,
        ⟨49459, false, false, [], []⟩
      ]⟩,
    ⟨[88271], [88269, 13], .source 44200⟩,
    ⟨[88269, 13], [88271], .contexts [
        ⟨49461, true, false, [], []⟩
      ]⟩,
    ⟨[88269], [88269], .contexts []⟩,
    ⟨[88271, 13], [88269], .contexts [
        ⟨49462, true, false, [], [13]⟩,
        ⟨59, false, false, [88269], []⟩,
        ⟨49463, false, false, [], []⟩
      ]⟩,
    ⟨[88273], [88271, 15], .source 44201⟩,
    ⟨[88271, 15], [88273], .contexts [
        ⟨49465, true, false, [], []⟩
      ]⟩,
    ⟨[88271], [88271], .contexts []⟩,
    ⟨[88273, 15], [88271], .contexts [
        ⟨49466, true, false, [], [15]⟩,
        ⟨1, false, false, [88271], []⟩,
        ⟨49467, false, false, [], []⟩
      ]⟩,
    ⟨[88275], [88273, 1], .source 44202⟩,
    ⟨[88273], [88273], .contexts []⟩,
    ⟨[88275, 1], [88273], .contexts [
        ⟨49469, false, false, [], [1]⟩,
        ⟨8, false, false, [88273], []⟩,
        ⟨49470, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 773. -/
def y322TCIndexRaw773 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88277], [88275, 3], .source 44203⟩,
    ⟨[88275], [88275], .contexts []⟩,
    ⟨[88277, 3], [88275], .contexts [
        ⟨49472, false, false, [], [3]⟩,
        ⟨20, false, false, [88275], []⟩,
        ⟨49473, false, false, [], []⟩
      ]⟩,
    ⟨[88279], [88277, 5], .source 44204⟩,
    ⟨[88277], [88277], .contexts []⟩,
    ⟨[88279, 5], [88277], .contexts [
        ⟨49475, false, false, [], [5]⟩,
        ⟨28, false, false, [88277], []⟩,
        ⟨49476, false, false, [], []⟩
      ]⟩,
    ⟨[88281], [88279, 1], .source 44205⟩,
    ⟨[88279], [88279], .contexts []⟩,
    ⟨[88281, 1], [88279], .contexts [
        ⟨49478, false, false, [], [1]⟩,
        ⟨8, false, false, [88279], []⟩,
        ⟨49479, false, false, [], []⟩
      ]⟩,
    ⟨[88283], [88281, 9], .source 44206⟩,
    ⟨[88281], [88281], .contexts []⟩,
    ⟨[88283, 9], [88281], .contexts [
        ⟨49481, false, false, [], [9]⟩,
        ⟨46, false, false, [88281], []⟩,
        ⟨49482, false, false, [], []⟩
      ]⟩,
    ⟨[88285], [88283, 11], .source 44207⟩,
    ⟨[88283], [88283], .contexts []⟩,
    ⟨[88285, 11], [88283], .contexts [
        ⟨49484, false, false, [], [11]⟩,
        ⟨53, false, false, [88283], []⟩,
        ⟨49485, false, false, [], []⟩
      ]⟩,
    ⟨[88287], [88285, 1], .source 44208⟩,
    ⟨[88285], [88285], .contexts []⟩,
    ⟨[88287, 1], [88285], .contexts [
        ⟨49487, false, false, [], [1]⟩,
        ⟨8, false, false, [88285], []⟩,
        ⟨49488, false, false, [], []⟩
      ]⟩,
    ⟨[88289], [88287, 13], .source 44209⟩,
    ⟨[88287], [88287], .contexts []⟩,
    ⟨[88289, 13], [88287], .contexts [
        ⟨49490, false, false, [], [13]⟩,
        ⟨59, false, false, [88287], []⟩,
        ⟨49491, false, false, [], []⟩
      ]⟩,
    ⟨[88291], [88289, 15], .source 44210⟩,
    ⟨[88289, 15], [88291], .contexts [
        ⟨49493, true, false, [], []⟩
      ]⟩,
    ⟨[88289], [88289], .contexts []⟩,
    ⟨[88291, 15], [88289], .contexts [
        ⟨49494, true, false, [], [15]⟩,
        ⟨1, false, false, [88289], []⟩,
        ⟨49495, false, false, [], []⟩
      ]⟩,
    ⟨[88293], [88291, 1], .source 44211⟩,
    ⟨[88291, 1], [88293], .contexts [
        ⟨49497, true, false, [], []⟩
      ]⟩,
    ⟨[88291], [88291], .contexts []⟩,
    ⟨[88293, 1], [88291], .contexts [
        ⟨49498, true, false, [], [1]⟩,
        ⟨8, false, false, [88291], []⟩,
        ⟨49499, false, false, [], []⟩
      ]⟩,
    ⟨[88295], [88293, 3], .source 44212⟩,
    ⟨[88293, 3], [88295], .contexts [
        ⟨49501, true, false, [], []⟩
      ]⟩,
    ⟨[88293], [88293], .contexts []⟩,
    ⟨[88295, 3], [88293], .contexts [
        ⟨49502, true, false, [], [3]⟩,
        ⟨20, false, false, [88293], []⟩,
        ⟨49503, false, false, [], []⟩
      ]⟩,
    ⟨[88297], [88295, 5], .source 44213⟩,
    ⟨[88295], [88295], .contexts []⟩,
    ⟨[88297, 5], [88295], .contexts [
        ⟨49505, false, false, [], [5]⟩,
        ⟨28, false, false, [88295], []⟩,
        ⟨49506, false, false, [], []⟩
      ]⟩,
    ⟨[88299], [88297, 1], .source 44214⟩,
    ⟨[88297, 1], [88299], .contexts [
        ⟨49508, true, false, [], []⟩
      ]⟩,
    ⟨[88297], [88297], .contexts []⟩,
    ⟨[88299, 1], [88297], .contexts [
        ⟨49509, true, false, [], [1]⟩,
        ⟨8, false, false, [88297], []⟩,
        ⟨49510, false, false, [], []⟩
      ]⟩,
    ⟨[88301], [88299, 9], .source 44215⟩,
    ⟨[88299, 9], [88301], .contexts [
        ⟨49512, true, false, [], []⟩
      ]⟩,
    ⟨[88299], [88299], .contexts []⟩,
    ⟨[88301, 9], [88299], .contexts [
        ⟨49513, true, false, [], [9]⟩,
        ⟨46, false, false, [88299], []⟩,
        ⟨49514, false, false, [], []⟩
      ]⟩,
    ⟨[88303], [88301, 11], .source 44216⟩,
    ⟨[88301, 11], [88303], .contexts [
        ⟨49516, true, false, [], []⟩
      ]⟩,
    ⟨[88301], [88301], .contexts []⟩,
    ⟨[88303, 11], [88301], .contexts [
        ⟨49517, true, false, [], [11]⟩,
        ⟨53, false, false, [88301], []⟩,
        ⟨49518, false, false, [], []⟩
      ]⟩,
    ⟨[88305], [88303, 1], .source 44217⟩,
    ⟨[88303], [88303], .contexts []⟩,
    ⟨[88305, 1], [88303], .contexts [
        ⟨49520, false, false, [], [1]⟩,
        ⟨8, false, false, [88303], []⟩,
        ⟨49521, false, false, [], []⟩
      ]⟩,
    ⟨[88307], [88305, 13], .source 44218⟩,
    ⟨[88305, 13], [88307], .contexts [
        ⟨49523, true, false, [], []⟩
      ]⟩,
    ⟨[88305], [88305], .contexts []⟩,
    ⟨[88307, 13], [88305], .contexts [
        ⟨49524, true, false, [], [13]⟩,
        ⟨59, false, false, [88305], []⟩,
        ⟨49525, false, false, [], []⟩
      ]⟩,
    ⟨[88309], [88307, 15], .source 44219⟩,
    ⟨[88307, 15], [88309], .contexts [
        ⟨49527, true, false, [], []⟩
      ]⟩,
    ⟨[88307], [88307], .contexts []⟩,
    ⟨[88309, 15], [88307], .contexts [
        ⟨49528, true, false, [], [15]⟩,
        ⟨1, false, false, [88307], []⟩,
        ⟨49529, false, false, [], []⟩
      ]⟩,
    ⟨[88311], [88309, 1], .source 44220⟩,
    ⟨[88309], [88309], .contexts []⟩,
    ⟨[88311, 1], [88309], .contexts [
        ⟨49531, false, false, [], [1]⟩,
        ⟨8, false, false, [88309], []⟩,
        ⟨49532, false, false, [], []⟩
      ]⟩,
    ⟨[88313], [88311, 3], .source 44221⟩,
    ⟨[88311, 3], [88313], .contexts [
        ⟨49534, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 774. -/
def y322TCIndexRaw774 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88311], [88311], .contexts []⟩,
    ⟨[88313, 3], [88311], .contexts [
        ⟨49535, true, false, [], [3]⟩,
        ⟨20, false, false, [88311], []⟩,
        ⟨49536, false, false, [], []⟩
      ]⟩,
    ⟨[88315], [88313, 5], .source 44222⟩,
    ⟨[88313, 5], [88315], .contexts [
        ⟨49538, true, false, [], []⟩
      ]⟩,
    ⟨[88313], [88313], .contexts []⟩,
    ⟨[88315, 5], [88313], .contexts [
        ⟨49539, true, false, [], [5]⟩,
        ⟨28, false, false, [88313], []⟩,
        ⟨49540, false, false, [], []⟩
      ]⟩,
    ⟨[88317], [88315, 1], .source 44223⟩,
    ⟨[88315, 1], [88317], .contexts [
        ⟨49542, true, false, [], []⟩
      ]⟩,
    ⟨[88315], [88315], .contexts []⟩,
    ⟨[88317, 1], [88315], .contexts [
        ⟨49543, true, false, [], [1]⟩,
        ⟨8, false, false, [88315], []⟩,
        ⟨49544, false, false, [], []⟩
      ]⟩,
    ⟨[88319], [88317, 9], .source 44224⟩,
    ⟨[88317, 9], [88319], .contexts [
        ⟨49546, true, false, [], []⟩
      ]⟩,
    ⟨[88317], [88317], .contexts []⟩,
    ⟨[88319, 9], [88317], .contexts [
        ⟨49547, true, false, [], [9]⟩,
        ⟨46, false, false, [88317], []⟩,
        ⟨49548, false, false, [], []⟩
      ]⟩,
    ⟨[88321], [88319, 11], .source 44225⟩,
    ⟨[88319, 11], [88321], .contexts [
        ⟨49550, true, false, [], []⟩
      ]⟩,
    ⟨[88319], [88319], .contexts []⟩,
    ⟨[88321, 11], [88319], .contexts [
        ⟨49551, true, false, [], [11]⟩,
        ⟨53, false, false, [88319], []⟩,
        ⟨49552, false, false, [], []⟩
      ]⟩,
    ⟨[88323], [88321, 1], .source 44226⟩,
    ⟨[88321], [88321], .contexts []⟩,
    ⟨[88323, 1], [88321], .contexts [
        ⟨49554, false, false, [], [1]⟩,
        ⟨8, false, false, [88321], []⟩,
        ⟨49555, false, false, [], []⟩
      ]⟩,
    ⟨[88325], [88323, 13], .source 44227⟩,
    ⟨[88323, 13], [88325], .contexts [
        ⟨49557, true, false, [], []⟩
      ]⟩,
    ⟨[88323], [88323], .contexts []⟩,
    ⟨[88325, 13], [88323], .contexts [
        ⟨49558, true, false, [], [13]⟩,
        ⟨59, false, false, [88323], []⟩,
        ⟨49559, false, false, [], []⟩
      ]⟩,
    ⟨[88327], [88325, 15], .source 44228⟩,
    ⟨[88325, 15], [88327], .contexts [
        ⟨49561, true, false, [], []⟩
      ]⟩,
    ⟨[88325], [88325], .contexts []⟩,
    ⟨[88327, 15], [88325], .contexts [
        ⟨49562, true, false, [], [15]⟩,
        ⟨1, false, false, [88325], []⟩,
        ⟨49563, false, false, [], []⟩
      ]⟩,
    ⟨[88329], [88327, 1], .source 44229⟩,
    ⟨[88327], [88327], .contexts []⟩,
    ⟨[88329, 1], [88327], .contexts [
        ⟨49565, false, false, [], [1]⟩,
        ⟨8, false, false, [88327], []⟩,
        ⟨49566, false, false, [], []⟩
      ]⟩,
    ⟨[88331], [88329, 3], .source 44230⟩,
    ⟨[88329, 3], [88331], .contexts [
        ⟨49568, true, false, [], []⟩
      ]⟩,
    ⟨[88329], [88329], .contexts []⟩,
    ⟨[88331, 3], [88329], .contexts [
        ⟨49569, true, false, [], [3]⟩,
        ⟨20, false, false, [88329], []⟩,
        ⟨49570, false, false, [], []⟩
      ]⟩,
    ⟨[88333], [88331, 5], .source 44231⟩,
    ⟨[88331, 5], [88333], .contexts [
        ⟨49572, true, false, [], []⟩
      ]⟩,
    ⟨[88331], [88331], .contexts []⟩,
    ⟨[88333, 5], [88331], .contexts [
        ⟨49573, true, false, [], [5]⟩,
        ⟨28, false, false, [88331], []⟩,
        ⟨49574, false, false, [], []⟩
      ]⟩,
    ⟨[88335], [88333, 1], .source 44232⟩,
    ⟨[88333], [88333], .contexts []⟩,
    ⟨[88335, 1], [88333], .contexts [
        ⟨49576, false, false, [], [1]⟩,
        ⟨8, false, false, [88333], []⟩,
        ⟨49577, false, false, [], []⟩
      ]⟩,
    ⟨[88337], [88335, 9], .source 44233⟩,
    ⟨[88335, 9], [88337], .contexts [
        ⟨49579, true, false, [], []⟩
      ]⟩,
    ⟨[88335], [88335], .contexts []⟩,
    ⟨[88337, 9], [88335], .contexts [
        ⟨49580, true, false, [], [9]⟩,
        ⟨46, false, false, [88335], []⟩,
        ⟨49581, false, false, [], []⟩
      ]⟩,
    ⟨[88339], [88337, 11], .source 44234⟩,
    ⟨[88337, 11], [88339], .contexts [
        ⟨49583, true, false, [], []⟩
      ]⟩,
    ⟨[88337], [88337], .contexts []⟩,
    ⟨[88339, 11], [88337], .contexts [
        ⟨49584, true, false, [], [11]⟩,
        ⟨53, false, false, [88337], []⟩,
        ⟨49585, false, false, [], []⟩
      ]⟩,
    ⟨[88339], [88339], .contexts []⟩,
    ⟨[88339], [88339], .contexts []⟩,
    ⟨[88337, 11], [88339], .contexts [
        ⟨49584, false, false, [], []⟩,
        ⟨49587, false, false, [], []⟩,
        ⟨49588, false, false, [], []⟩,
        ⟨49588, false, false, [], []⟩
      ]⟩,
    ⟨[88337, 9], [88335], .contexts [
        ⟨49582, false, false, [], []⟩,
        ⟨49581, false, false, [], []⟩,
        ⟨49581, false, false, [], []⟩
      ]⟩,
    ⟨[88335, 1], [88333], .contexts [
        ⟨49578, false, false, [], []⟩
      ]⟩,
    ⟨[88333], [88333], .contexts []⟩,
    ⟨[88331], [88331], .contexts []⟩,
    ⟨[88331, 3], [88329], .contexts [
        ⟨49571, false, false, [], []⟩
      ]⟩,
    ⟨[88329], [88329], .contexts []⟩,
    ⟨[88329, 1], [88327], .contexts [
        ⟨49567, false, false, [], []⟩
      ]⟩,
    ⟨[88327], [88327], .contexts []⟩,
    ⟨[88325], [88325], .contexts []⟩,
    ⟨[88337, 9, 1, 5, 3, 1, 15], [88325], .contexts [
        ⟨49590, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨49591, false, false, [], [5, 3, 1, 15]⟩,
        ⟨49592, false, false, [], [5, 3, 1, 15]⟩,
        ⟨49577, false, false, [], [5, 3, 1, 15]⟩,
        ⟨49577, false, false, [], [5, 3, 1, 15]⟩,
        ⟨49575, false, false, [], [3, 1, 15]⟩,
        ⟨49593, false, false, [], [3, 1, 15]⟩,
        ⟨49574, false, false, [], [3, 1, 15]⟩,
        ⟨49574, false, false, [], [3, 1, 15]⟩,
        ⟨49594, false, false, [], [1, 15]⟩,
        ⟨49595, false, false, [], [1, 15]⟩,
        ⟨49570, false, false, [], [1, 15]⟩,
        ⟨49570, false, false, [], [1, 15]⟩,
        ⟨49596, false, false, [], [15]⟩,
        ⟨49597, false, false, [], [15]⟩,
        ⟨49566, false, false, [], [15]⟩,
        ⟨49566, false, false, [], [15]⟩,
        ⟨49564, false, false, [], []⟩,
        ⟨49598, false, false, [], []⟩,
        ⟨49563, false, false, [], []⟩,
        ⟨49563, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 775. -/
def y322TCIndexRaw775 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88325, 13], [88323], .contexts [
        ⟨49560, false, false, [], []⟩
      ]⟩,
    ⟨[88323], [88323], .contexts []⟩,
    ⟨[88323, 1], [88321], .contexts [
        ⟨49556, false, false, [], []⟩
      ]⟩,
    ⟨[88321], [88321], .contexts []⟩,
    ⟨[88321, 11], [88319], .contexts [
        ⟨49553, false, false, [], []⟩
      ]⟩,
    ⟨[88319], [88319], .contexts []⟩,
    ⟨[88319, 9], [88317], .contexts [
        ⟨49549, false, false, [], []⟩
      ]⟩,
    ⟨[88317], [88317], .contexts []⟩,
    ⟨[88317, 1], [88315], .contexts [
        ⟨49545, false, false, [], []⟩
      ]⟩,
    ⟨[88315], [88315], .contexts []⟩,
    ⟨[88337, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1], [88315], .contexts [
        ⟨49599, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨49600, false, false, [], [1, 11, 9, 1]⟩,
        ⟨49601, false, false, [], [1, 11, 9, 1]⟩,
        ⟨49559, false, false, [], [1, 11, 9, 1]⟩,
        ⟨49559, false, false, [], [1, 11, 9, 1]⟩,
        ⟨49602, false, false, [], [11, 9, 1]⟩,
        ⟨49603, false, false, [], [11, 9, 1]⟩,
        ⟨49555, false, false, [], [11, 9, 1]⟩,
        ⟨49555, false, false, [], [11, 9, 1]⟩,
        ⟨49604, false, false, [], [9, 1]⟩,
        ⟨49605, false, false, [], [9, 1]⟩,
        ⟨49552, false, false, [], [9, 1]⟩,
        ⟨49552, false, false, [], [9, 1]⟩,
        ⟨49606, false, false, [], [1]⟩,
        ⟨49607, false, false, [], [1]⟩,
        ⟨49548, false, false, [], [1]⟩,
        ⟨49548, false, false, [], [1]⟩,
        ⟨49608, false, false, [], []⟩,
        ⟨49609, false, false, [], []⟩,
        ⟨49544, false, false, [], []⟩,
        ⟨49544, false, false, [], []⟩
      ]⟩,
    ⟨[88313, 3], [88311], .contexts [
        ⟨49537, false, false, [], []⟩
      ]⟩,
    ⟨[88311], [88311], .contexts []⟩,
    ⟨[88311, 1], [88309], .contexts [
        ⟨49533, false, false, [], []⟩
      ]⟩,
    ⟨[88309], [88309], .contexts []⟩,
    ⟨[88307], [88307], .contexts []⟩,
    ⟨[88307, 13], [88305], .contexts [
        ⟨49526, false, false, [], []⟩
      ]⟩,
    ⟨[
      88337, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13
    ], [88305], .contexts [
        ⟨49610, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨49541, false, false, [], [3, 1, 15, 13]⟩,
        ⟨49540, false, false, [], [3, 1, 15, 13]⟩,
        ⟨49540, false, false, [], [3, 1, 15, 13]⟩,
        ⟨49611, false, false, [], [1, 15, 13]⟩,
        ⟨49612, false, false, [], [1, 15, 13]⟩,
        ⟨49536, false, false, [], [1, 15, 13]⟩,
        ⟨49536, false, false, [], [1, 15, 13]⟩,
        ⟨49613, false, false, [], [15, 13]⟩,
        ⟨49614, false, false, [], [15, 13]⟩,
        ⟨49532, false, false, [], [15, 13]⟩,
        ⟨49532, false, false, [], [15, 13]⟩,
        ⟨49530, false, false, [], [13]⟩,
        ⟨49615, false, false, [], [13]⟩,
        ⟨49529, false, false, [], [13]⟩,
        ⟨49529, false, false, [], [13]⟩,
        ⟨49616, false, false, [], []⟩,
        ⟨49525, false, false, [], []⟩,
        ⟨49525, false, false, [], []⟩
      ]⟩,
    ⟨[88303], [88303], .contexts []⟩,
    ⟨[88301], [88301], .contexts []⟩,
    ⟨[88299], [88299], .contexts []⟩,
    ⟨[88299, 1], [88297], .contexts [
        ⟨49511, false, false, [], []⟩
      ]⟩,
    ⟨[88297], [88297], .contexts []⟩,
    ⟨[88297, 5], [88295], .contexts [
        ⟨49507, false, false, [], []⟩
      ]⟩,
    ⟨[88295], [88295], .contexts []⟩,
    ⟨[
      88337, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [88295], .contexts [
        ⟨49617, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨49522, false, false, [], [11, 9, 1, 5]⟩,
        ⟨49618, false, false, [], [11, 9, 1, 5]⟩,
        ⟨49521, false, false, [], [11, 9, 1, 5]⟩,
        ⟨49521, false, false, [], [11, 9, 1, 5]⟩,
        ⟨49519, false, false, [], [9, 1, 5]⟩,
        ⟨49619, false, false, [], [9, 1, 5]⟩,
        ⟨49518, false, false, [], [9, 1, 5]⟩,
        ⟨49518, false, false, [], [9, 1, 5]⟩,
        ⟨49515, false, false, [], [1, 5]⟩,
        ⟨49620, false, false, [], [1, 5]⟩,
        ⟨49514, false, false, [], [1, 5]⟩,
        ⟨49514, false, false, [], [1, 5]⟩,
        ⟨49621, false, false, [], [5]⟩,
        ⟨49622, false, false, [], [5]⟩,
        ⟨49510, false, false, [], [5]⟩,
        ⟨49510, false, false, [], [5]⟩,
        ⟨49623, false, false, [], []⟩,
        ⟨49624, false, false, [], []⟩,
        ⟨49506, false, false, [], []⟩,
        ⟨49506, false, false, [], []⟩
      ]⟩,
    ⟨[88293], [88293], .contexts []⟩,
    ⟨[88291], [88291], .contexts []⟩,
    ⟨[88287], [88287], .contexts []⟩,
    ⟨[88285], [88285], .contexts []⟩,
    ⟨[
      88337, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1
    ], [88285], .contexts [
        ⟨49625, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨49504, false, false, [], [1, 15, 13, 1]⟩,
        ⟨49626, false, false, [], [1, 15, 13, 1]⟩,
        ⟨49503, false, false, [], [1, 15, 13, 1]⟩,
        ⟨49503, false, false, [], [1, 15, 13, 1]⟩,
        ⟨49500, false, false, [], [15, 13, 1]⟩,
        ⟨49627, false, false, [], [15, 13, 1]⟩,
        ⟨49499, false, false, [], [15, 13, 1]⟩,
        ⟨49499, false, false, [], [15, 13, 1]⟩,
        ⟨49496, false, false, [], [13, 1]⟩,
        ⟨49495, false, false, [], [13, 1]⟩,
        ⟨49495, false, false, [], [13, 1]⟩,
        ⟨49492, false, false, [], [1]⟩,
        ⟨49628, false, false, [], [1]⟩,
        ⟨49491, false, false, [], [1]⟩,
        ⟨49491, false, false, [], [1]⟩,
        ⟨49489, false, false, [], []⟩,
        ⟨49629, false, false, [], []⟩,
        ⟨49488, false, false, [], []⟩,
        ⟨49488, false, false, [], []⟩
      ]⟩,
    ⟨[88283], [88283], .contexts []⟩,
    ⟨[88281], [88281], .contexts []⟩,
    ⟨[88279], [88279], .contexts []⟩,
    ⟨[88277], [88277], .contexts []⟩,
    ⟨[88275], [88275], .contexts []⟩,
    ⟨[
      88337, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3
    ], [88275], .contexts [
        ⟨49630, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨49486, false, false, [], [9, 1, 5, 3]⟩,
        ⟨49631, false, false, [], [9, 1, 5, 3]⟩,
        ⟨49485, false, false, [], [9, 1, 5, 3]⟩,
        ⟨49485, false, false, [], [9, 1, 5, 3]⟩,
        ⟨49483, false, false, [], [1, 5, 3]⟩,
        ⟨49632, false, false, [], [1, 5, 3]⟩,
        ⟨49482, false, false, [], [1, 5, 3]⟩,
        ⟨49482, false, false, [], [1, 5, 3]⟩,
        ⟨49480, false, false, [], [5, 3]⟩,
        ⟨49633, false, false, [], [5, 3]⟩,
        ⟨49479, false, false, [], [5, 3]⟩,
        ⟨49479, false, false, [], [5, 3]⟩,
        ⟨49477, false, false, [], [3]⟩,
        ⟨49634, false, false, [], [3]⟩,
        ⟨49476, false, false, [], [3]⟩,
        ⟨49476, false, false, [], [3]⟩,
        ⟨49474, false, false, [], []⟩,
        ⟨49635, false, false, [], []⟩,
        ⟨49473, false, false, [], []⟩,
        ⟨49473, false, false, [], []⟩
      ]⟩,
    ⟨[88273], [88273], .contexts []⟩,
    ⟨[88271], [88271], .contexts []⟩,
    ⟨[88269], [88269], .contexts []⟩,
    ⟨[88267], [88267], .contexts []⟩,
    ⟨[88267, 11], [88265], .contexts [
        ⟨49456, false, false, [], []⟩
      ]⟩,
    ⟨[88265], [88265], .contexts []⟩,
    ⟨[
      88337, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11
    ], [88265], .contexts [
        ⟨49636, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨49471, false, false, [], [15, 13, 1, 11]⟩,
        ⟨49637, false, false, [], [15, 13, 1, 11]⟩,
        ⟨49470, false, false, [], [15, 13, 1, 11]⟩,
        ⟨49470, false, false, [], [15, 13, 1, 11]⟩,
        ⟨49468, false, false, [], [13, 1, 11]⟩,
        ⟨49638, false, false, [], [13, 1, 11]⟩,
        ⟨49467, false, false, [], [13, 1, 11]⟩,
        ⟨49467, false, false, [], [13, 1, 11]⟩,
        ⟨49464, false, false, [], [1, 11]⟩,
        ⟨49639, false, false, [], [1, 11]⟩,
        ⟨49463, false, false, [], [1, 11]⟩,
        ⟨49463, false, false, [], [1, 11]⟩,
        ⟨49460, false, false, [], [11]⟩,
        ⟨49640, false, false, [], [11]⟩,
        ⟨49459, false, false, [], [11]⟩,
        ⟨49459, false, false, [], [11]⟩,
        ⟨49641, false, false, [], []⟩,
        ⟨49642, false, false, [], []⟩,
        ⟨49455, false, false, [], []⟩,
        ⟨49455, false, false, [], []⟩
      ]⟩,
    ⟨[88263], [88263], .contexts []⟩,
    ⟨[88261], [88261], .contexts []⟩,
    ⟨[88259], [88259], .contexts []⟩,
    ⟨[88259, 3], [88257], .contexts [
        ⟨49441, false, false, [], []⟩
      ]⟩,
    ⟨[88257], [88257], .contexts []⟩,
    ⟨[88255], [88255], .contexts []⟩,
    ⟨[
      88337, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1
    ], [88255], .contexts [
        ⟨49643, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨49453, false, false, [], [1, 5, 3, 1]⟩,
        ⟨49644, false, false, [], [1, 5, 3, 1]⟩,
        ⟨49452, false, false, [], [1, 5, 3, 1]⟩,
        ⟨49452, false, false, [], [1, 5, 3, 1]⟩,
        ⟨49449, false, false, [], [5, 3, 1]⟩,
        ⟨49645, false, false, [], [5, 3, 1]⟩,
        ⟨49448, false, false, [], [5, 3, 1]⟩,
        ⟨49448, false, false, [], [5, 3, 1]⟩,
        ⟨49445, false, false, [], [3, 1]⟩,
        ⟨49646, false, false, [], [3, 1]⟩,
        ⟨49444, false, false, [], [3, 1]⟩,
        ⟨49444, false, false, [], [3, 1]⟩,
        ⟨49647, false, false, [], [1]⟩,
        ⟨49648, false, false, [], [1]⟩,
        ⟨49440, false, false, [], [1]⟩,
        ⟨49440, false, false, [], [1]⟩,
        ⟨49437, false, false, [], []⟩,
        ⟨49649, false, false, [], []⟩,
        ⟨49436, false, false, [], []⟩,
        ⟨49436, false, false, [], []⟩
      ]⟩,
    ⟨[88251], [88251], .contexts []⟩,
    ⟨[88249], [88249], .contexts []⟩,
    ⟨[88247], [88247], .contexts []⟩,
    ⟨[88247, 9], [88245], .contexts [
        ⟨49420, false, false, [], []⟩
      ]⟩,
    ⟨[88245], [88245], .contexts []⟩,
    ⟨[
      88337, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [88245], .contexts [
        ⟨49650, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨49433, false, false, [], [13, 1, 11, 9]⟩,
        ⟨49432, false, false, [], [13, 1, 11, 9]⟩,
        ⟨49432, false, false, [], [13, 1, 11, 9]⟩,
        ⟨49430, false, false, [], [1, 11, 9]⟩,
        ⟨49651, false, false, [], [1, 11, 9]⟩,
        ⟨49429, false, false, [], [1, 11, 9]⟩,
        ⟨49429, false, false, [], [1, 11, 9]⟩,
        ⟨49427, false, false, [], [11, 9]⟩,
        ⟨49652, false, false, [], [11, 9]⟩,
        ⟨49426, false, false, [], [11, 9]⟩,
        ⟨49426, false, false, [], [11, 9]⟩,
        ⟨49424, false, false, [], [9]⟩,
        ⟨49653, false, false, [], [9]⟩,
        ⟨49423, false, false, [], [9]⟩,
        ⟨49423, false, false, [], [9]⟩,
        ⟨49654, false, false, [], []⟩,
        ⟨49655, false, false, [], []⟩,
        ⟨49419, false, false, [], []⟩,
        ⟨49419, false, false, [], []⟩
      ]⟩,
    ⟨[88243], [88243], .contexts []⟩,
    ⟨[88241], [88241], .contexts []⟩,
    ⟨[88239], [88239], .contexts []⟩,
    ⟨[88237], [88237], .contexts []⟩,
    ⟨[88235], [88235], .contexts []⟩,
    ⟨[
      88337, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15
    ], [88235], .contexts [
        ⟨49656, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨49416, false, false, [], [5, 3, 1, 15]⟩,
        ⟨49657, false, false, [], [5, 3, 1, 15]⟩,
        ⟨49415, false, false, [], [5, 3, 1, 15]⟩,
        ⟨49415, false, false, [], [5, 3, 1, 15]⟩,
        ⟨49412, false, false, [], [3, 1, 15]⟩,
        ⟨49658, false, false, [], [3, 1, 15]⟩,
        ⟨49411, false, false, [], [3, 1, 15]⟩,
        ⟨49411, false, false, [], [3, 1, 15]⟩,
        ⟨49408, false, false, [], [1, 15]⟩,
        ⟨49659, false, false, [], [1, 15]⟩,
        ⟨49407, false, false, [], [1, 15]⟩,
        ⟨49407, false, false, [], [1, 15]⟩,
        ⟨49404, false, false, [], [15]⟩,
        ⟨49660, false, false, [], [15]⟩,
        ⟨49403, false, false, [], [15]⟩,
        ⟨49403, false, false, [], [15]⟩,
        ⟨49400, false, false, [], []⟩,
        ⟨49661, false, false, [], []⟩,
        ⟨49399, false, false, [], []⟩,
        ⟨49399, false, false, [], []⟩
      ]⟩,
    ⟨[88233], [88233], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 776. -/
def y322TCIndexRaw776 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88229], [88229], .contexts []⟩,
    ⟨[88229, 9], [88227], .contexts [
        ⟨49385, false, false, [], []⟩
      ]⟩,
    ⟨[
      88337, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [22541, 88227], .contexts [
        ⟨49662, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨49396, false, false, [], [1, 11, 9, 1]⟩,
        ⟨49663, false, false, [], [1, 11, 9, 1]⟩,
        ⟨49395, false, false, [], [1, 11, 9, 1]⟩,
        ⟨49395, false, false, [], [1, 11, 9, 1]⟩,
        ⟨49392, false, false, [], [11, 9, 1]⟩,
        ⟨49391, false, false, [], [11, 9, 1]⟩,
        ⟨49391, false, false, [], [11, 9, 1]⟩,
        ⟨49387, true, false, [], [11, 9, 1]⟩,
        ⟨53, false, false, [88229], [9, 1]⟩,
        ⟨49388, false, false, [], [9, 1]⟩,
        ⟨49664, false, false, [], [9, 1]⟩,
        ⟨49388, false, false, [], [9, 1]⟩,
        ⟨49388, false, false, [], [9, 1]⟩,
        ⟨49665, false, false, [], [1]⟩,
        ⟨49378, false, false, [], [1]⟩,
        ⟨49379, false, false, [], [1]⟩,
        ⟨49379, false, false, [], [1]⟩,
        ⟨49379, true, false, [], [1]⟩,
        ⟨49379, true, false, [], [1]⟩,
        ⟨49378, true, false, [], [1]⟩,
        ⟨49377, true, false, [], [1]⟩,
        ⟨161, false, false, [88225], []⟩,
        ⟨162, false, false, [88225], []⟩,
        ⟨49380, false, false, [], [5]⟩,
        ⟨49376, false, false, [22541], []⟩,
        ⟨49381, false, false, [], []⟩,
        ⟨49382, false, false, [], []⟩,
        ⟨49338, true, false, [], [88227]⟩,
        ⟨49381, false, false, [], []⟩,
        ⟨49382, false, false, [], []⟩,
        ⟨49382, false, false, [], []⟩
      ]⟩,
    ⟨[
      88337, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15
    ], [22541, 88219], .contexts [
        ⟨49666, false, false, [], [5, 3, 1, 15]⟩,
        ⟨49376, true, false, [22541], [5, 3, 1, 15]⟩,
        ⟨28, false, false, [22541, 88225], [3, 1, 15]⟩,
        ⟨49363, false, false, [22541], [3, 1, 15]⟩,
        ⟨49368, false, false, [], [3, 1, 15]⟩,
        ⟨49369, false, false, [], [3, 1, 15]⟩,
        ⟨49370, false, false, [], [3, 1, 15]⟩,
        ⟨49361, false, false, [22541], [1, 15]⟩,
        ⟨49365, false, false, [], [1, 15]⟩,
        ⟨49366, false, false, [], [1, 15]⟩,
        ⟨49367, false, false, [], [1, 15]⟩,
        ⟨49357, false, false, [22541], [15]⟩,
        ⟨49345, false, false, [], [15]⟩,
        ⟨49346, false, false, [], [15]⟩,
        ⟨49348, false, false, [], [15]⟩,
        ⟨49341, false, false, [22541], []⟩,
        ⟨49333, false, false, [], []⟩,
        ⟨49334, false, false, [], []⟩,
        ⟨49335, false, false, [], []⟩
      ]⟩,
    ⟨[
      88337, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1
    ], [22541, 88209], .contexts [
        ⟨49667, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨49328, false, false, [22541], [1, 11, 9, 1]⟩,
        ⟨49331, false, false, [], [1, 11, 9, 1]⟩,
        ⟨49332, false, false, [], [1, 11, 9, 1]⟩,
        ⟨49305, false, false, [22541], [11, 9, 1]⟩,
        ⟨49285, false, false, [22541], [9, 1]⟩,
        ⟨49275, false, false, [22541], [1]⟩,
        ⟨49262, false, false, [22541], []⟩
      ]⟩,
    ⟨[22543], [22541, 15269], .source 11336⟩,
    ⟨[22545], [22543, 1075], .source 11337⟩,
    ⟨[
      88337, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [22545, 78833], .contexts [
        ⟨49668, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨49234, false, false, [22541], [3, 1, 15, 13]⟩,
        ⟨49205, false, false, [22541], [1, 15, 13]⟩,
        ⟨15303, false, false, [22541], [15, 13]⟩,
        ⟨49669, true, false, [], [82679, 15, 13]⟩,
        ⟨15306, false, false, [22543], [13]⟩,
        ⟨5143, false, false, [22543], []⟩,
        ⟨49670, true, false, [], [78833]⟩
      ]⟩,
    ⟨[22547], [22545, 15439], .source 11338⟩,
    ⟨[22549], [22547, 563], .source 11339⟩,
    ⟨[
      88337, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5
    ], [22549, 79005], .contexts [
        ⟨49671, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨5541, false, false, [22545], [11, 9, 1, 5]⟩,
        ⟨16764, false, false, [22545], [9, 1, 5]⟩,
        ⟨16761, false, false, [22545], [1, 5]⟩,
        ⟨49672, true, false, [], [82787, 1, 5]⟩,
        ⟨16645, false, false, [22547], [5]⟩,
        ⟨49673, true, false, [], [82787, 5]⟩,
        ⟨16636, false, false, [22549], []⟩
      ]⟩,
    ⟨[22551], [22549, 1755], .source 11340⟩,
    ⟨[22553], [22551, 2575], .source 11341⟩,
    ⟨[
      88337, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [22553, 82687], .contexts [
        ⟨49674, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨5520, false, false, [22549], [1, 15, 13, 1]⟩,
        ⟨49675, true, false, [], [78987, 1, 15, 13, 1]⟩,
        ⟨5396, false, false, [22551], [15, 13, 1]⟩,
        ⟨5472, false, false, [22551], [13, 1]⟩,
        ⟨15394, false, false, [22551], [1]⟩,
        ⟨15405, false, false, [22551], []⟩,
        ⟨49676, true, false, [], [82687]⟩
      ]⟩,
    ⟨[22555], [22553, 15289], .source 11342⟩,
    ⟨[22557], [22555, 2575], .source 11343⟩,
    ⟨[
      88337, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1,
      15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1,
      11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1,
      5, 3
    ], [22557, 84969], .contexts [
        ⟨49677, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨17297, false, false, [22553], [9, 1, 5, 3]⟩,
        ⟨17294, false, false, [22553], [1, 5, 3]⟩,
        ⟨49678, true, false, [], [82837, 1, 5, 3]⟩,
        ⟨17283, false, false, [22555], [5, 3]⟩,
        ⟨49679, true, false, [], [82837, 5, 3]⟩,
        ⟨19190, false, false, [22557], [3]⟩,
        ⟨29535, false, false, [22557], []⟩
      ]⟩,
    ⟨[22559], [22557, 1075], .source 11344⟩,
    ⟨[22559, 84973], [22559, 84973], .contexts []⟩,
    ⟨[22559, 84973], [22559, 84973], .contexts []⟩,
    ⟨[88339, 1], [88339, 1], .contexts []⟩,
    ⟨[88339, 1], [22559, 84973], .contexts [
        ⟨49684, false, false, [], []⟩,
        ⟨49589, true, false, [], [1]⟩,
        ⟨3787, false, false, [88337], []⟩,
        ⟨3788, false, false, [88337], []⟩,
        ⟨49680, false, false, [], [1, 15, 13]⟩,
        ⟨29549, false, false, [22557], [15, 13]⟩,
        ⟨29570, false, false, [22557], [13]⟩,
        ⟨49681, true, false, [], [84971, 13]⟩,
        ⟨29572, false, false, [22559], []⟩,
        ⟨49682, false, false, [], []⟩,
        ⟨49683, false, false, [], []⟩,
        ⟨29581, false, false, [22559], []⟩,
        ⟨13, true, false, [], [22559, 84973]⟩
      ]⟩,
    ⟨[22561], [22558], .source 11345⟩,
    ⟨[84973, 1], [22561, 88339], .contexts [
        ⟨49685, true, false, [22558], [1]⟩,
        ⟨8, false, false, [22558, 88339], []⟩,
        ⟨49686, true, false, [], [88339]⟩
      ]⟩,
    ⟨[88339, 1], [22559, 84973], .contexts [
        ⟨49684, false, false, [], []⟩,
        ⟨49685, false, false, [], []⟩,
        ⟨49682, false, false, [], []⟩,
        ⟨49683, false, false, [], []⟩,
        ⟨49683, false, false, [], []⟩
      ]⟩,
    ⟨[22563], [22559, 315], .source 11346⟩,
    ⟨[22565], [22563, 22561], .source 11347⟩,
    ⟨[88339], [88339], .contexts []⟩,
    ⟨[88339, 5], [88339, 5], .contexts []⟩,
    ⟨[88339], [88339], .contexts []⟩,
    ⟨[22567], [22564], .source 11348⟩,
    ⟨[22567], [22567], .contexts []⟩,
    ⟨[22564], [22564], .contexts []⟩,
    ⟨[22567], [22564], .contexts [
        ⟨49695, false, false, [], []⟩,
        ⟨49694, false, false, [], []⟩,
        ⟨49696, false, false, [], []⟩,
        ⟨49696, false, false, [], []⟩
      ]⟩,
    ⟨[88339, 5], [22567, 88339], .contexts [
        ⟨49692, false, false, [], []⟩,
        ⟨49690, false, false, [22564], [88339, 5]⟩,
        ⟨49687, true, false, [22564, 22563], [5]⟩,
        ⟨49689, false, false, [22564], [84973, 1, 5]⟩,
        ⟨29586, true, false, [22564, 22559], [1, 5]⟩,
        ⟨49688, true, false, [22564], [5, 1, 5]⟩,
        ⟨1152, false, false, [22564, 88339], []⟩,
        ⟨49691, false, false, [22564], []⟩,
        ⟨49693, false, false, [22564], []⟩,
        ⟨49697, true, false, [], [88339]⟩
      ]⟩,
    ⟨[22569], [22559, 21885], .source 11349⟩,
    ⟨[22569, 87935], [22569, 87935], .contexts []⟩,
    ⟨[22569, 87935], [22569, 87935], .contexts []⟩,
    ⟨[87935, 7], [87935, 7], .contexts []⟩,
    ⟨[22571], [22568], .source 11350⟩,
    ⟨[22568], [22568], .contexts []⟩,
    ⟨[87935, 7], [22571, 88339], .contexts [
        ⟨49702, false, false, [], []⟩,
        ⟨49701, true, false, [22568], [7]⟩,
        ⟨49700, true, false, [22568], [7]⟩,
        ⟨46897, true, false, [], [7]⟩,
        ⟨49699, false, false, [22568], [87937, 1, 7]⟩,
        ⟨47019, true, false, [22568, 22559], [1, 7]⟩,
        ⟨49688, true, false, [22568], [7, 1, 7]⟩,
        ⟨4091, false, false, [22568, 88339], []⟩,
        ⟨49691, false, false, [22568], []⟩,
        ⟨49693, false, false, [22568], []⟩,
        ⟨49704, true, false, [], [88339]⟩,
        ⟨49704, true, false, [], [88339]⟩,
        ⟨49703, true, false, [], [88339]⟩
      ]⟩,
    ⟨[22569], [22570], .contexts [
        ⟨49703, true, true, [], []⟩
      ]⟩,
    ⟨[88339, 7], [22569, 87935], .contexts [
        ⟨49705, true, false, [22570], [7]⟩,
        ⟨38, false, false, [22570, 87935], []⟩,
        ⟨49706, true, false, [], [87935]⟩
      ]⟩,
    ⟨[22559, 84977], [22559, 84977], .contexts []⟩,
    ⟨[22558], [22558], .contexts []⟩,
    ⟨[84977, 15], [22561, 88339], .contexts [
        ⟨49708, true, false, [22558], [15]⟩,
        ⟨29605, true, false, [], [15]⟩,
        ⟨29588, true, false, [], [1, 15]⟩,
        ⟨49688, true, false, [22558], [15, 1, 15]⟩,
        ⟨2185, false, false, [22558, 88339], []⟩,
        ⟨49691, false, false, [22558], []⟩,
        ⟨49693, false, false, [22558], []⟩,
        ⟨49709, true, false, [], [88339]⟩,
        ⟨49709, true, false, [], [88339]⟩,
        ⟨49686, true, false, [], [88339]⟩
      ]⟩,
    ⟨[88339, 15], [22559, 84977], .contexts [
        ⟨49710, true, false, [22560], [15]⟩,
        ⟨1, false, false, [22560, 84977], []⟩,
        ⟨49686, false, true, [], [84977]⟩
      ]⟩,
    ⟨[22567, 88339], [22567, 88339], .contexts []⟩,
    ⟨[22567, 88339], [22567, 88339], .contexts []⟩,
    ⟨[88339, 5], [22567, 88339], .contexts [
        ⟨49692, false, false, [], []⟩,
        ⟨49698, false, false, [], []⟩,
        ⟨49712, false, false, [], []⟩,
        ⟨49713, false, false, [], []⟩,
        ⟨49713, false, false, [], []⟩
      ]⟩,
    ⟨[88337], [88337], .contexts []⟩,
    ⟨[88337, 5], [88337, 5], .contexts []⟩,
    ⟨[88337], [88337], .contexts []⟩,
    ⟨[22566], [22566], .contexts []⟩,
    ⟨[22565], [22566], .contexts [
        ⟨49694, true, true, [], []⟩,
        ⟨49718, false, false, [], []⟩,
        ⟨49718, false, false, [], []⟩
      ]⟩,
    ⟨[88337, 5], [22565, 88337], .contexts [
        ⟨49716, false, false, [], []⟩,
        ⟨49586, true, false, [], [5]⟩,
        ⟨49714, true, false, [22566], [11, 5]⟩,
        ⟨940, false, false, [22566, 88339], []⟩,
        ⟨54, false, false, [22566, 88339], []⟩,
        ⟨49586, false, false, [22566], []⟩,
        ⟨49715, false, false, [22566], []⟩,
        ⟨49585, false, false, [22566], []⟩,
        ⟨49585, false, false, [22566], []⟩,
        ⟨49717, false, false, [22566], []⟩,
        ⟨49719, true, false, [], [88337]⟩
      ]⟩,
    ⟨[22571, 88339], [22571, 88339], .contexts []⟩,
    ⟨[22571, 88339], [22571, 88339], .contexts []⟩,
    ⟨[88337, 7], [88337, 7], .contexts []⟩,
    ⟨[22573], [22569, 21899], .source 11351⟩,
    ⟨[88337, 7], [22573, 86687], .contexts [
        ⟨49723, false, false, [], []⟩,
        ⟨49586, true, false, [], [7]⟩,
        ⟨49722, true, false, [22570], [11, 7]⟩,
        ⟨49722, true, false, [22570], [11, 7]⟩,
        ⟨49721, true, false, [22570], [11, 7]⟩,
        ⟨49705, true, false, [22570], [11, 7]⟩,
        ⟨49702, true, false, [22570], [11, 7]⟩,
        ⟨555, false, false, [22570, 87935], []⟩,
        ⟨54, false, false, [22570, 87935], []⟩,
        ⟨46900, false, false, [22570], []⟩,
        ⟨47056, false, false, [22570], []⟩,
        ⟨47055, false, false, [22570], []⟩,
        ⟨47055, false, false, [22570], []⟩,
        ⟨38531, false, false, [22570, 21899], []⟩,
        ⟨49706, true, false, [], [21899, 86687]⟩,
        ⟨49724, true, false, [], [86687]⟩
      ]⟩,
    ⟨[22575], [22572], .source 11352⟩,
    ⟨[22565, 88337], [22565, 88337], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 777. -/
def y322TCIndexRaw777 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[22565, 88337], [22565, 88337], .contexts []⟩,
    ⟨[88337, 8], [88337, 9], .contexts [
        ⟨47, false, false, [88337], []⟩
      ]⟩,
    ⟨[88335, 5], [88335, 5], .contexts []⟩,
    ⟨[88335], [88335], .contexts []⟩,
    ⟨[22573, 86687], [22573, 86687], .contexts []⟩,
    ⟨[88337, 7], [22573, 86687], .contexts [
        ⟨49723, false, false, [], []⟩,
        ⟨49725, false, false, [], []⟩,
        ⟨49732, false, false, [], []⟩,
        ⟨49732, false, false, [], []⟩
      ]⟩,
    ⟨[22577], [22573, 19391], .source 11353⟩,
    ⟨[83463, 7], [83463, 7], .contexts []⟩,
    ⟨[22579], [22576], .source 11354⟩,
    ⟨[22576], [22576], .contexts []⟩,
    ⟨[83463, 7], [22579, 88335], .contexts [
        ⟨49735, false, false, [], []⟩,
        ⟨49734, false, false, [22576], [83463, 7]⟩,
        ⟨38533, true, false, [22576, 22573], [7]⟩,
        ⟨49733, true, false, [22576], [9, 7]⟩,
        ⟨579, false, false, [22576, 88337], []⟩,
        ⟨49729, false, false, [22576], []⟩,
        ⟨49590, false, false, [22576], []⟩,
        ⟨49731, false, false, [22576], []⟩,
        ⟨49737, true, false, [], [88335]⟩,
        ⟨49737, true, false, [], [88335]⟩,
        ⟨49736, true, false, [], [88335]⟩
      ]⟩,
    ⟨[22581], [22573, 20683], .source 11355⟩,
    ⟨[22583], [22581, 22199], .source 11356⟩,
    ⟨[88027, 13], [88027, 13], .contexts []⟩,
    ⟨[22585], [22582], .source 11357⟩,
    ⟨[22582], [22582], .contexts []⟩,
    ⟨[88027, 13], [22585, 88337], .contexts [
        ⟨49741, false, false, [], []⟩,
        ⟨49740, false, false, [22582], [88027, 13]⟩,
        ⟨48117, true, false, [22582, 22581], [13]⟩,
        ⟨49739, false, false, [22582], [87035, 7, 13]⟩,
        ⟨42481, true, false, [22582, 22573], [7, 13]⟩,
        ⟨49733, true, false, [22582], [13, 7, 13]⟩,
        ⟨15654, false, false, [22582, 88337], []⟩,
        ⟨49717, false, false, [22582], []⟩,
        ⟨49743, true, false, [], [88337]⟩,
        ⟨49743, true, false, [], [88337]⟩,
        ⟨49742, true, false, [], [88337]⟩
      ]⟩,
    ⟨[22583], [22584], .contexts [
        ⟨49742, true, true, [], []⟩
      ]⟩,
    ⟨[22567, 88335], [22567, 88335], .contexts []⟩,
    ⟨[88335, 5], [22567, 88335], .contexts [
        ⟨49730, false, false, [], []⟩,
        ⟨49730, false, false, [], []⟩,
        ⟨49582, true, false, [], [5]⟩,
        ⟨49728, true, false, [22564], [9, 5]⟩,
        ⟨49728, true, false, [22564], [9, 5]⟩,
        ⟨49727, true, false, [22564], [9, 5]⟩,
        ⟨49720, true, false, [22564], [9, 5]⟩,
        ⟨49716, true, false, [22564], [9, 5]⟩,
        ⟨960, false, false, [22564, 88337], []⟩,
        ⟨49729, false, false, [22564], []⟩,
        ⟨49590, false, false, [22564], []⟩,
        ⟨49731, false, false, [22564], []⟩,
        ⟨49697, true, false, [], [88335]⟩,
        ⟨49746, false, false, [], []⟩,
        ⟨49746, false, false, [], []⟩
      ]⟩,
    ⟨[22567, 88331], [22567, 88331], .contexts []⟩,
    ⟨[22567, 88331], [22567, 88331], .contexts []⟩,
    ⟨[88331, 1], [88331, 1], .contexts []⟩,
    ⟨[88331, 1], [22565, 88335], .contexts [
        ⟨49750, false, false, [], []⟩,
        ⟨49749, true, false, [22566], [1]⟩,
        ⟨49748, true, false, [22566], [1]⟩,
        ⟨49575, true, false, [], [1]⟩,
        ⟨49578, true, false, [], [5, 1]⟩,
        ⟨49747, true, false, [22566], [1, 5, 1]⟩,
        ⟨874, false, false, [22566, 88335], []⟩,
        ⟨49731, false, false, [22566], []⟩,
        ⟨49719, true, false, [], [88335]⟩
      ]⟩,
    ⟨[83463, 7], [22579, 88335], .contexts [
        ⟨49735, false, false, [], []⟩,
        ⟨49738, false, false, [], []⟩
      ]⟩,
    ⟨[22579, 88335], [22579, 88335], .contexts []⟩,
    ⟨[83463, 7], [22579, 88335], .contexts [
        ⟨49752, false, false, [], []⟩,
        ⟨49753, false, false, [], []⟩,
        ⟨49753, false, false, [], []⟩
      ]⟩,
    ⟨[88333], [22567, 88331], .contexts [
        ⟨49577, true, false, [], []⟩,
        ⟨49577, true, false, [], []⟩,
        ⟨49592, true, false, [], []⟩,
        ⟨49591, true, false, [], []⟩,
        ⟨49751, true, false, [22564], [1]⟩,
        ⟨8, false, false, [22564, 88331], []⟩,
        ⟨49694, true, false, [], [88331]⟩,
        ⟨49748, false, false, [], []⟩,
        ⟨49695, true, false, [], [88331]⟩
      ]⟩,
    ⟨[22587], [22579, 22567], .source 11358⟩,
    ⟨[22589], [22586], .source 11359⟩,
    ⟨[22591], [22589, 20587], .source 11360⟩,
    ⟨[88331, 7], [22591, 83463], .contexts [
        ⟨49756, false, false, [22586], [88331, 7]⟩,
        ⟨49749, true, false, [22586, 22579], [7]⟩,
        ⟨49755, true, false, [22586, 22579], [7]⟩,
        ⟨49578, true, false, [22586, 22579], [7]⟩,
        ⟨49754, true, false, [22586], [1, 7]⟩,
        ⟨502, false, false, [22586, 83463], []⟩,
        ⟨9, false, false, [22586, 83463], []⟩,
        ⟨42815, false, false, [22586], []⟩,
        ⟨42486, false, false, [22586, 20587], []⟩,
        ⟨49757, true, false, [], [20587, 83463]⟩,
        ⟨49758, true, false, [], [83463]⟩
      ]⟩,
    ⟨[22593], [22590], .source 11361⟩,
    ⟨[22595], [22577, 22593], .source 11362⟩,
    ⟨[88335], [22595, 88331], .contexts [
        ⟨49754, true, false, [22578], []⟩,
        ⟨49759, true, false, [22578, 22590], [7]⟩,
        ⟨38, false, false, [22578, 22590, 88331], []⟩,
        ⟨49760, true, false, [22578], [88331]⟩,
        ⟨49736, false, true, [], [22593, 88331]⟩,
        ⟨49761, true, false, [], [88331]⟩
      ]⟩,
    ⟨[22597], [22594], .source 11363⟩,
    ⟨[22594], [22594], .contexts []⟩,
    ⟨[88331, 9], [22597, 88337], .contexts [
        ⟨49762, true, false, [22594], [9]⟩,
        ⟨49580, false, false, [22594], []⟩,
        ⟨49715, false, false, [22594], []⟩,
        ⟨49764, true, false, [], [88337]⟩,
        ⟨49764, true, false, [], [88337]⟩,
        ⟨49763, true, false, [], [88337]⟩
      ]⟩,
    ⟨[88335], [22595, 88331], .contexts [
        ⟨49762, false, false, [], []⟩
      ]⟩,
    ⟨[88335], [22595, 88331], .contexts [
        ⟨49766, false, false, [], []⟩
      ]⟩,
    ⟨[22599], [22579, 22595], .source 11364⟩,
    ⟨[83463, 7], [22599, 88331], .contexts [
        ⟨49752, false, false, [], []⟩,
        ⟨49767, false, false, [22579], []⟩,
        ⟨49768, true, false, [], [88331]⟩
      ]⟩,
    ⟨[22601], [22598], .source 11365⟩,
    ⟨[22601], [22598], .contexts [
        ⟨49770, false, false, [], []⟩
      ]⟩,
    ⟨[22598], [22598], .contexts []⟩,
    ⟨[88329, 7], [22601, 83461], .contexts [
        ⟨49571, true, false, [], [7]⟩,
        ⟨49769, true, false, [22598], [3, 7]⟩,
        ⟨14911, false, false, [22598, 83463], []⟩,
        ⟨38536, false, false, [22598], []⟩,
        ⟨38535, false, false, [22598], []⟩,
        ⟨38537, false, false, [22598], []⟩,
        ⟨49772, true, false, [], [83461]⟩,
        ⟨49772, true, false, [], [83461]⟩,
        ⟨49771, true, false, [], [83461]⟩
      ]⟩,
    ⟨[20837, 87037], [20837, 87037], .contexts []⟩,
    ⟨[20837, 87037], [20837, 87037], .contexts []⟩,
    ⟨[22603], [20837, 21631], .source 11366⟩,
    ⟨[22605], [22601, 22603], .source 11367⟩,
    ⟨[88331, 13], [22605, 87661], .contexts [
        ⟨49769, true, false, [22598], [13]⟩,
        ⟨1056, false, false, [22598, 83463], []⟩,
        ⟨1057, false, false, [22598, 83463], []⟩,
        ⟨42809, false, false, [22598], [7]⟩,
        ⟨42813, false, false, [22598], [7]⟩,
        ⟨49774, false, false, [22598], [7]⟩,
        ⟨49775, false, false, [22598], [7]⟩,
        ⟨49775, false, false, [22598], [7]⟩,
        ⟨45710, false, false, [22598, 20837], []⟩,
        ⟨49776, true, false, [22598], [87661]⟩,
        ⟨45526, false, false, [22598, 22603], []⟩,
        ⟨49771, true, false, [], [22603, 87661]⟩,
        ⟨49777, true, false, [], [87661]⟩
      ]⟩,
    ⟨[22607], [22604], .source 11368⟩,
    ⟨[87661, 13], [22607, 88331], .contexts [
        ⟨49778, true, false, [22604], [13]⟩,
        ⟨59, false, false, [22604, 88331], []⟩,
        ⟨49779, true, false, [], [88331]⟩
      ]⟩,
    ⟨[22585, 88337], [22585, 88337], .contexts []⟩,
    ⟨[22585, 88337], [22585, 88337], .contexts []⟩,
    ⟨[88027, 13], [22585, 88337], .contexts [
        ⟨49741, false, false, [], []⟩,
        ⟨49744, false, false, [], []⟩,
        ⟨49781, false, false, [], []⟩,
        ⟨49782, false, false, [], []⟩,
        ⟨49782, false, false, [], []⟩
      ]⟩,
    ⟨[22217, 83327], [22217, 83327], .contexts []⟩,
    ⟨[22217, 83327], [22217, 83327], .contexts []⟩,
    ⟨[22609], [22217, 19911], .source 11369⟩,
    ⟨[88337, 3], [88337, 3], .contexts []⟩,
    ⟨[22611], [22583, 22609], .source 11370⟩,
    ⟨[88337, 3], [22611, 86423], .contexts [
        ⟨49787, false, false, [], []⟩,
        ⟨49783, true, false, [22584], [3]⟩,
        ⟨63, false, false, [22584, 88027], []⟩,
        ⟨65, false, false, [22584, 88027], []⟩,
        ⟨48100, false, false, [22584], [13]⟩,
        ⟨49784, false, false, [22584], [13]⟩,
        ⟨49785, false, false, [22584], [13]⟩,
        ⟨49785, false, false, [22584], [13]⟩,
        ⟨36972, false, false, [22584, 22217], []⟩,
        ⟨36993, false, false, [22584, 22217, 19101], []⟩,
        ⟨40440, true, false, [22584, 22217], [86423]⟩,
        ⟨49786, true, false, [22584], [86423]⟩,
        ⟨40443, false, false, [22584, 22609], []⟩,
        ⟨49745, true, false, [], [22609, 86423]⟩,
        ⟨49788, true, false, [], [86423]⟩
      ]⟩,
    ⟨[22613], [22610], .source 11371⟩,
    ⟨[86423, 3], [22613, 88337], .contexts [
        ⟨49789, true, false, [22610], [3]⟩,
        ⟨20, false, false, [22610, 88337], []⟩,
        ⟨49790, true, false, [], [88337]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 778. -/
def y322TCIndexRaw778 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[22615], [22565, 22595], .source 11372⟩,
    ⟨[88331, 3], [88329], .contexts [
        ⟨49594, false, false, [], []⟩,
        ⟨49595, false, false, [], []⟩,
        ⟨49570, false, false, [], []⟩,
        ⟨49570, false, false, [], []⟩
      ]⟩,
    ⟨[22617], [22614], .source 11373⟩,
    ⟨[22614], [22614], .contexts []⟩,
    ⟨[88327, 3], [22617, 88327], .contexts [
        ⟨49567, true, false, [], [3]⟩,
        ⟨49571, true, false, [], [1, 3]⟩,
        ⟨49792, false, false, [22614], [88331, 3, 1, 3]⟩,
        ⟨49767, true, false, [22614, 22565], [3, 1, 3]⟩,
        ⟨49751, true, false, [22614], [3, 1, 3]⟩,
        ⟨49750, true, false, [22614], [3, 1, 3]⟩,
        ⟨484, false, false, [22614, 88331], []⟩,
        ⟨485, false, false, [22614, 88331], []⟩,
        ⟨49793, false, false, [22614], [1]⟩,
        ⟨49596, false, false, [22614], []⟩,
        ⟨49597, false, false, [22614], []⟩,
        ⟨49566, false, false, [22614], []⟩,
        ⟨49566, false, false, [22614], []⟩,
        ⟨49795, true, false, [], [88327]⟩,
        ⟨49795, true, false, [], [88327]⟩,
        ⟨49794, true, false, [], [88327]⟩
      ]⟩,
    ⟨[22597, 88337], [22597, 88337], .contexts []⟩,
    ⟨[22597, 88337], [22597, 88337], .contexts []⟩,
    ⟨[22619], [22597, 22611], .source 11374⟩,
    ⟨[22621], [22618], .source 11375⟩,
    ⟨[19917, 86785], [19917, 86785], .contexts []⟩,
    ⟨[19917, 86785], [19917, 86785], .contexts []⟩,
    ⟨[86423, 9], [19917, 86785], .contexts [
        ⟨40448, false, false, [], []⟩,
        ⟨49801, false, false, [], []⟩,
        ⟨49802, false, false, [], []⟩,
        ⟨49802, false, false, [], []⟩
      ]⟩,
    ⟨[22623], [19915, 22621], .source 11376⟩,
    ⟨[88329], [22622, 86785], .contexts [
        ⟨49804, false, false, [22622], [88329]⟩,
        ⟨40447, true, true, [22622], [22621, 88329]⟩,
        ⟨49800, false, false, [22622, 19916], [88329]⟩,
        ⟨46, true, false, [22622, 19916, 22618, 88329], []⟩,
        ⟨49793, true, false, [22622, 19916, 22618], [9, 9]⟩,
        ⟨669, false, false, [22622, 19916, 22618, 88331], [9]⟩,
        ⟨670, false, false, [22622, 19916, 22618, 88331], [9]⟩,
        ⟨49765, false, false, [22622, 19916, 22618], [3, 9]⟩,
        ⟨49797, false, false, [22622, 19916, 22618], [3, 9]⟩,
        ⟨49798, false, false, [22622, 19916, 22618], [3, 9]⟩,
        ⟨49798, false, false, [22622, 19916, 22618], [3, 9]⟩,
        ⟨49789, false, false, [22622, 19916, 22618, 22597], [9]⟩,
        ⟨49799, true, false, [22622, 19916, 22618], [86423, 9]⟩,
        ⟨40443, false, false, [22622, 19916], [9]⟩,
        ⟨13, true, false, [22622, 19916, 22618], [22619, 86423, 9]⟩,
        ⟨49803, false, false, [22622, 19916], []⟩
      ]⟩,
    ⟨[22625], [22622], .source 11377⟩,
    ⟨[88329], [22625, 86785], .contexts [
        ⟨49805, false, false, [], []⟩,
        ⟨49806, true, false, [], [86785]⟩
      ]⟩,
    ⟨[22623], [22624], .contexts [
        ⟨49806, true, true, [], []⟩
      ]⟩,
    ⟨[22623], [22624], .contexts [
        ⟨49808, false, false, [], []⟩
      ]⟩,
    ⟨[22624], [22624], .contexts []⟩,
    ⟨[22623], [22624], .contexts [
        ⟨49809, false, false, [], []⟩,
        ⟨49810, false, false, [], []⟩,
        ⟨49810, false, false, [], []⟩
      ]⟩,
    ⟨[22627], [22623, 22601], .source 11378⟩,
    ⟨[86785, 7], [22627, 83461], .contexts [
        ⟨49807, true, false, [22624], [7]⟩,
        ⟨49773, false, false, [22624], []⟩,
        ⟨49808, true, false, [], [22601, 83461]⟩,
        ⟨49812, true, false, [], [83461]⟩
      ]⟩,
    ⟨[88329], [22625, 86785], .contexts [
        ⟨49807, false, false, [], []⟩
      ]⟩,
    ⟨[22625, 86783], [22625, 86783], .contexts []⟩,
    ⟨[88327], [22625, 86783], .contexts [
        ⟨49809, false, false, [22622], [88327]⟩,
        ⟨13, false, false, [22622, 22624], [88327]⟩,
        ⟨49597, true, false, [22622, 22624], []⟩,
        ⟨49567, true, false, [22622, 22624], []⟩,
        ⟨49814, false, false, [22622, 22624], [1]⟩,
        ⟨38751, false, false, [22622], []⟩,
        ⟨49815, false, false, [22622, 22624], []⟩,
        ⟨49806, true, false, [], [86783]⟩
      ]⟩,
    ⟨[86783, 15], [22623, 88325], .contexts [
        ⟨49816, true, false, [22624], [15]⟩,
        ⟨49564, false, false, [22624], []⟩,
        ⟨49598, false, false, [22624], []⟩,
        ⟨49811, true, false, [], [88325]⟩
      ]⟩,
    ⟨[88327], [22625, 86783], .contexts [
        ⟨49816, false, false, [], []⟩,
        ⟨49815, false, false, [], []⟩
      ]⟩,
    ⟨[22629], [22623, 22617], .source 11379⟩,
    ⟨[22631], [22629, 22625], .source 11380⟩,
    ⟨[86783, 3], [22631, 86783], .contexts [
        ⟨49816, true, false, [22624], [3]⟩,
        ⟨49796, false, false, [22624], []⟩,
        ⟨49818, false, false, [22624, 22617], []⟩,
        ⟨49808, true, false, [], [22617, 22625, 86783]⟩,
        ⟨49819, true, false, [], [22625, 86783]⟩,
        ⟨49820, true, false, [], [86783]⟩
      ]⟩,
    ⟨[22627, 83461], [22627, 83461], .contexts []⟩,
    ⟨[22627, 83461], [22627, 83461], .contexts []⟩,
    ⟨[86785, 7], [22627, 83461], .contexts [
        ⟨49813, false, false, [], []⟩,
        ⟨49822, false, false, [], []⟩,
        ⟨49823, false, false, [], []⟩,
        ⟨49823, false, false, [], []⟩
      ]⟩,
    ⟨[22627, 83459], [22627, 83459], .contexts []⟩,
    ⟨[22627, 83459], [22627, 83459], .contexts []⟩,
    ⟨[22633], [22626], .source 11381⟩,
    ⟨[22626], [22626], .contexts []⟩,
    ⟨[83459, 7], [22633, 86783], .contexts [
        ⟨49826, true, false, [22626], [7]⟩,
        ⟨49825, true, false, [22626], [7]⟩,
        ⟨21253, true, false, [], [7]⟩,
        ⟨49824, true, false, [22626], [1, 7]⟩,
        ⟨502, false, false, [22626, 86785], []⟩,
        ⟨40497, false, false, [22626], []⟩,
        ⟨40496, false, false, [22626], []⟩,
        ⟨40499, false, false, [22626], []⟩,
        ⟨49828, true, false, [], [86783]⟩,
        ⟨49828, true, false, [], [86783]⟩,
        ⟨49827, true, false, [], [86783]⟩
      ]⟩,
    ⟨[86783, 7], [22627, 83459], .contexts [
        ⟨49829, true, false, [22632], [7]⟩,
        ⟨38, false, false, [22632, 83459], []⟩,
        ⟨49827, false, true, [], [83459]⟩
      ]⟩,
    ⟨[22635], [19393, 20893], .source 11382⟩,
    ⟨[22637], [22627, 22635], .source 11383⟩,
    ⟨[22639], [22636], .source 11384⟩,
    ⟨[22641], [22639, 19915], .source 11385⟩,
    ⟨[86683, 7], [22641, 86423], .contexts [
        ⟨49832, false, false, [22636], [86683, 7]⟩,
        ⟨49831, false, false, [22636, 22627], [86683, 7]⟩,
        ⟨43017, true, false, [22636, 22627, 19393], [7]⟩,
        ⟨38539, true, false, [22636, 22627], [7]⟩,
        ⟨49824, true, false, [22636], [9, 7]⟩,
        ⟨579, false, false, [22636, 86785], []⟩,
        ⟨47, false, false, [22636, 86785], []⟩,
        ⟨40493, false, false, [22636], []⟩,
        ⟨40443, false, false, [22636, 19915], []⟩,
        ⟨49833, true, false, [], [19915, 86423]⟩,
        ⟨49834, true, false, [], [86423]⟩
      ]⟩,
    ⟨[22643], [22640], .source 11386⟩,
    ⟨[86423, 7], [22643, 86683], .contexts [
        ⟨49835, true, false, [22640], [7]⟩,
        ⟨38, false, false, [22640, 86683], []⟩,
        ⟨49836, true, false, [], [86683]⟩
      ]⟩,
    ⟨[22611, 86423], [22611, 86423], .contexts []⟩,
    ⟨[22611, 86423], [22611, 86423], .contexts []⟩,
    ⟨[22611, 86421], [22611, 86421], .contexts []⟩,
    ⟨[22611, 86421], [22611, 86421], .contexts []⟩,
    ⟨[86421, 3], [86421, 3], .contexts []⟩,
    ⟨[22613], [22610], .contexts [
        ⟨49790, false, false, [], []⟩
      ]⟩,
    ⟨[22610], [22610], .contexts []⟩,
    ⟨[86421, 3], [22613, 88339], .contexts [
        ⟨49842, false, false, [], []⟩,
        ⟨49841, true, false, [22610], [3]⟩,
        ⟨49840, true, false, [22610], [3]⟩,
        ⟨36822, true, false, [], [3]⟩,
        ⟨49839, true, false, [22610], [11, 3]⟩,
        ⟨49839, true, false, [22610], [11, 3]⟩,
        ⟨49838, true, false, [22610], [11, 3]⟩,
        ⟨49789, true, false, [22610], [11, 3]⟩,
        ⟨49787, true, false, [22610], [11, 3]⟩,
        ⟨545, false, false, [22610, 88337], []⟩,
        ⟨54, false, false, [22610, 88337], []⟩,
        ⟨49589, false, false, [22610], []⟩,
        ⟨49693, false, false, [22610], []⟩,
        ⟨49844, true, false, [], [88339]⟩,
        ⟨49844, true, false, [], [88339]⟩,
        ⟨49843, true, false, [], [88339]⟩
      ]⟩,
    ⟨[22611], [22612], .contexts [
        ⟨49790, true, true, [], []⟩
      ]⟩,
    ⟨[88339, 3], [22611, 86421], .contexts [
        ⟨49845, true, false, [22612], [3]⟩,
        ⟨20, false, false, [22612, 86421], []⟩,
        ⟨49846, true, false, [], [86421]⟩
      ]⟩,
    ⟨[22631, 86783], [22631, 86783], .contexts []⟩,
    ⟨[22631, 86783], [22631, 86783], .contexts []⟩,
    ⟨[86783, 3], [22631, 86783], .contexts [
        ⟨49821, false, false, [], []⟩,
        ⟨49848, false, false, [], []⟩,
        ⟨49849, false, false, [], []⟩,
        ⟨49849, false, false, [], []⟩
      ]⟩,
    ⟨[86781, 3], [86781, 3], .contexts []⟩,
    ⟨[86781], [86781], .contexts []⟩,
    ⟨[22645], [22630], .source 11387⟩,
    ⟨[22630], [22630], .contexts []⟩,
    ⟨[86781, 3], [22645, 86781], .contexts [
        ⟨49851, false, false, [], []⟩,
        ⟨38747, true, false, [], [3]⟩,
        ⟨49850, true, false, [22630], [11, 3]⟩,
        ⟨545, false, false, [22630, 86783], []⟩,
        ⟨54, false, false, [22630, 86783], []⟩,
        ⟨40517, false, false, [22630], []⟩,
        ⟨49852, false, false, [22630], []⟩,
        ⟨49854, true, false, [], [86781]⟩,
        ⟨49854, true, false, [], [86781]⟩,
        ⟨49853, true, false, [], [86781]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 779. -/
def y322TCIndexRaw779 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[22647], [22631, 22623], .source 11388⟩,
    ⟨[22623, 88325], [22623, 88325], .contexts []⟩,
    ⟨[86783, 15], [22623, 88325], .contexts [
        ⟨49817, false, false, [], []⟩,
        ⟨49857, false, false, [], []⟩,
        ⟨49857, false, false, [], []⟩
      ]⟩,
    ⟨[86783, 14], [86783, 15], .contexts [
        ⟨10, false, false, [86783], []⟩
      ]⟩,
    ⟨[88325, 3], [88325, 3], .contexts []⟩,
    ⟨[88325], [88325], .contexts []⟩,
    ⟨[22649], [22646], .source 11389⟩,
    ⟨[22651], [22649, 22623], .source 11390⟩,
    ⟨[88325, 3], [22651, 88325], .contexts [
        ⟨49860, false, false, [], []⟩,
        ⟨49856, false, false, [22646], [88325, 3]⟩,
        ⟨49817, true, false, [22646, 22631], [3]⟩,
        ⟨49850, true, false, [22646], [15, 3]⟩,
        ⟨499, false, false, [22646, 86783], []⟩,
        ⟨49859, false, false, [22646], []⟩,
        ⟨49858, false, false, [22646], []⟩,
        ⟨49861, false, false, [22646, 22623], []⟩,
        ⟨49862, true, false, [], [22623, 88325]⟩,
        ⟨49863, true, false, [], [88325]⟩
      ]⟩,
    ⟨[22653], [19929, 22623], .source 11391⟩,
    ⟨[22655], [22652], .source 11392⟩,
    ⟨[22657], [22655, 22623], .source 11393⟩,
    ⟨[88325, 7], [88325, 7], .contexts []⟩,
    ⟨[22659], [22625, 22627], .source 11394⟩,
    ⟨[88325, 7], [22659, 83457], .contexts [
        ⟨49868, false, false, [], []⟩,
        ⟨49858, true, false, [22622], [7]⟩,
        ⟨37, false, false, [22622, 86783], []⟩,
        ⟨40, false, false, [22622, 86783], []⟩,
        ⟨49830, false, false, [22622], [15]⟩,
        ⟨49825, false, false, [22622], [15]⟩,
        ⟨49826, false, false, [22622], [15]⟩,
        ⟨49826, false, false, [22622], [15]⟩,
        ⟨21249, false, false, [22622, 22627], []⟩,
        ⟨43041, false, false, [22622, 22627], []⟩,
        ⟨49806, true, false, [], [22627, 83457]⟩,
        ⟨49869, true, false, [], [83457]⟩
      ]⟩,
    ⟨[22661], [22658], .source 11395⟩,
    ⟨[22613, 88339], [22613, 88339], .contexts []⟩,
    ⟨[22613, 88339], [22613, 88339], .contexts []⟩,
    ⟨[22663], [22613, 22559], .source 11396⟩,
    ⟨[22663, 84979], [22663, 84979], .contexts []⟩,
    ⟨[22663, 84979], [22663, 84979], .contexts []⟩,
    ⟨[22665], [22662], .source 11397⟩,
    ⟨[22665], [22662], .contexts [
        ⟨49877, false, false, [], []⟩
      ]⟩,
    ⟨[22662], [22662], .contexts []⟩,
    ⟨[84979, 15], [22665, 86421], .contexts [
        ⟨49876, true, false, [22662], [15]⟩,
        ⟨49875, true, false, [22662], [15]⟩,
        ⟨29615, true, false, [], [15]⟩,
        ⟨49874, false, false, [22662], [84977, 3, 15]⟩,
        ⟨49711, true, false, [22662, 22613], [3, 15]⟩,
        ⟨49873, true, false, [22662], [15, 3, 15]⟩,
        ⟨49873, true, false, [22662], [15, 3, 15]⟩,
        ⟨49872, true, false, [22662], [15, 3, 15]⟩,
        ⟨49845, true, false, [22662], [15, 3, 15]⟩,
        ⟨49842, true, false, [22662], [15, 3, 15]⟩,
        ⟨1659, false, false, [22662, 86421], []⟩,
        ⟨36998, false, false, [22662], []⟩,
        ⟨49879, true, false, [], [86421]⟩,
        ⟨49879, true, false, [], [86421]⟩,
        ⟨49878, true, false, [], [86421]⟩
      ]⟩,
    ⟨[86421, 15], [22663, 84979], .contexts [
        ⟨49880, true, false, [22664], [15]⟩,
        ⟨1, false, false, [22664, 84979], []⟩,
        ⟨49877, false, true, [], [84979]⟩
      ]⟩,
    ⟨[22645, 86781], [22645, 86781], .contexts []⟩,
    ⟨[22645, 86781], [22645, 86781], .contexts []⟩,
    ⟨[86781, 9], [86779], .contexts [
        ⟨38800, false, false, [], []⟩,
        ⟨38801, false, false, [], []⟩,
        ⟨38742, false, false, [], []⟩,
        ⟨38742, false, false, [], []⟩
      ]⟩,
    ⟨[86781, 8], [86781, 9], .contexts [
        ⟨47, false, false, [86781], []⟩
      ]⟩,
    ⟨[86779, 3], [86779, 3], .contexts []⟩,
    ⟨[22644], [22644], .contexts []⟩,
    ⟨[86779, 3], [22631, 86779], .contexts [
        ⟨49886, false, false, [], []⟩,
        ⟨38743, true, false, [], [3]⟩,
        ⟨49883, true, false, [22644], [9, 3]⟩,
        ⟨49883, true, false, [22644], [9, 3]⟩,
        ⟨49882, true, false, [22644], [9, 3]⟩,
        ⟨49855, true, false, [22644], [9, 3]⟩,
        ⟨49851, true, false, [22644], [9, 3]⟩,
        ⟨573, false, false, [22644, 86781], []⟩,
        ⟨49885, false, false, [22644], []⟩,
        ⟨49884, false, false, [22644], []⟩,
        ⟨40519, false, false, [22644], []⟩,
        ⟨49887, true, false, [], [86779]⟩,
        ⟨49887, true, false, [], [86779]⟩,
        ⟨49853, false, true, [], [86779]⟩
      ]⟩,
    ⟨[22651, 88325], [22651, 88325], .contexts []⟩,
    ⟨[88325, 13], [88323], .contexts [
        ⟨49600, false, false, [], []⟩,
        ⟨49601, false, false, [], []⟩,
        ⟨49559, false, false, [], []⟩,
        ⟨49559, false, false, [], []⟩
      ]⟩,
    ⟨[88325, 12], [88325, 13], .contexts [
        ⟨64, false, false, [88325], []⟩
      ]⟩,
    ⟨[88323], [88323], .contexts []⟩,
    ⟨[22667], [22650], .source 11398⟩,
    ⟨[22650], [22650], .contexts []⟩,
    ⟨[22659, 83457], [22659, 83457], .contexts []⟩,
    ⟨[22659, 83457], [22659, 83457], .contexts []⟩,
    ⟨[88325, 7], [22659, 83457], .contexts [
        ⟨49868, false, false, [], []⟩,
        ⟨49870, false, false, [], []⟩,
        ⟨49895, false, false, [], []⟩,
        ⟨49896, false, false, [], []⟩,
        ⟨49896, false, false, [], []⟩
      ]⟩,
    ⟨[83455, 7], [83455, 7], .contexts []⟩,
    ⟨[22658], [22658], .contexts []⟩,
    ⟨[22661], [22658], .contexts [
        ⟨49871, false, false, [], []⟩,
        ⟨49899, false, false, [], []⟩,
        ⟨49899, false, false, [], []⟩
      ]⟩,
    ⟨[83455, 7], [22661, 88323], .contexts [
        ⟨49898, false, false, [], []⟩,
        ⟨21245, true, false, [], [7]⟩,
        ⟨49897, true, false, [22658], [13, 7]⟩,
        ⟨518, false, false, [22658, 88325], []⟩,
        ⟨49891, false, false, [22658], []⟩,
        ⟨49890, false, false, [22658], []⟩,
        ⟨49892, false, false, [22658], []⟩,
        ⟨49900, true, false, [], [88323]⟩
      ]⟩,
    ⟨[22659], [22660], .contexts [
        ⟨49871, true, true, [], []⟩
      ]⟩,
    ⟨[22661, 88323], [22661, 88323], .contexts []⟩,
    ⟨[83455, 7], [22661, 88323], .contexts [
        ⟨49898, false, false, [], []⟩,
        ⟨49901, false, false, [], []⟩,
        ⟨49903, false, false, [], []⟩,
        ⟨49903, false, false, [], []⟩
      ]⟩,
    ⟨[83455, 0], [83455, 1], .contexts [
        ⟨9, false, false, [83455], []⟩
      ]⟩,
    ⟨[88321, 7], [88321, 7], .contexts []⟩,
    ⟨[83453], [83453], .contexts []⟩,
    ⟨[22660], [22660], .contexts []⟩,
    ⟨[22659], [22660], .contexts [
        ⟨49902, false, false, [], []⟩,
        ⟨49908, false, false, [], []⟩,
        ⟨49908, false, false, [], []⟩
      ]⟩,
    ⟨[88321, 7], [22659, 83453], .contexts [
        ⟨49906, false, false, [], []⟩,
        ⟨49556, true, false, [], [7]⟩,
        ⟨49904, true, false, [22660], [1, 7]⟩,
        ⟨502, false, false, [22660, 83455], []⟩,
        ⟨49905, false, false, [22660], []⟩,
        ⟨43544, false, false, [22660], []⟩,
        ⟨49907, false, false, [22660], []⟩,
        ⟨49909, true, false, [], [83453]⟩
      ]⟩,
    ⟨[83453, 7], [22661, 88321], .contexts [
        ⟨49910, true, false, [22658], [7]⟩,
        ⟨38, false, false, [22658, 88321], []⟩,
        ⟨49871, true, false, [], [88321]⟩
      ]⟩,
    ⟨[22659, 83453], [22659, 83453], .contexts []⟩,
    ⟨[22659, 83453], [22659, 83453], .contexts []⟩,
    ⟨[22659, 83451], [22659, 83451], .contexts []⟩,
    ⟨[22659, 83451], [22659, 83451], .contexts []⟩,
    ⟨[88321, 11], [88319], .contexts [
        ⟨49604, false, false, [], []⟩,
        ⟨49605, false, false, [], []⟩,
        ⟨49552, false, false, [], []⟩,
        ⟨49552, false, false, [], []⟩
      ]⟩,
    ⟨[88321, 10], [88321, 11], .contexts [
        ⟨54, false, false, [88321], []⟩
      ]⟩,
    ⟨[83451, 7], [83451, 7], .contexts []⟩,
    ⟨[88319], [88319], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 780. -/
def y322TCIndexRaw780 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83451, 7], [22661, 88319], .contexts [
        ⟨49918, false, false, [], []⟩,
        ⟨49915, true, false, [22658], [7]⟩,
        ⟨49914, true, false, [22658], [7]⟩,
        ⟨21237, true, false, [], [7]⟩,
        ⟨49913, true, false, [22658], [11, 7]⟩,
        ⟨49913, true, false, [22658], [11, 7]⟩,
        ⟨49912, true, false, [22658], [11, 7]⟩,
        ⟨49910, true, false, [22658], [11, 7]⟩,
        ⟨49906, true, false, [22658], [11, 7]⟩,
        ⟨555, false, false, [22658, 88321], []⟩,
        ⟨49917, false, false, [22658], []⟩,
        ⟨49916, false, false, [22658], []⟩,
        ⟨49919, false, false, [22658], []⟩,
        ⟨49900, true, false, [], [88319]⟩
      ]⟩,
    ⟨[88319, 7], [22659, 83451], .contexts [
        ⟨49920, true, false, [22660], [7]⟩,
        ⟨38, false, false, [22660, 83451], []⟩,
        ⟨49902, true, false, [], [83451]⟩
      ]⟩,
    ⟨[22661, 88319], [22661, 88319], .contexts []⟩,
    ⟨[83451, 7], [22661, 88319], .contexts [
        ⟨49918, false, false, [], []⟩,
        ⟨49920, false, false, [], []⟩,
        ⟨49922, false, false, [], []⟩,
        ⟨49922, false, false, [], []⟩
      ]⟩,
    ⟨[88317, 7], [88317, 7], .contexts []⟩,
    ⟨[83449], [83449], .contexts []⟩,
    ⟨[88317, 7], [22659, 83449], .contexts [
        ⟨49924, false, false, [], []⟩,
        ⟨49549, true, false, [], [7]⟩,
        ⟨49923, true, false, [22660], [9, 7]⟩,
        ⟨579, false, false, [22660, 83451], []⟩,
        ⟨47, false, false, [22660, 83451], []⟩,
        ⟨21320, false, false, [22660], []⟩,
        ⟨21321, false, false, [22660], []⟩,
        ⟨21232, false, false, [22660], []⟩,
        ⟨21232, false, false, [22660], []⟩,
        ⟨49925, false, false, [22660], []⟩,
        ⟨49909, true, false, [], [83449]⟩
      ]⟩,
    ⟨[22659, 83449], [22659, 83449], .contexts []⟩,
    ⟨[22659, 83449], [22659, 83449], .contexts []⟩,
    ⟨[88317, 7], [22659, 83449], .contexts [
        ⟨49924, false, false, [], []⟩,
        ⟨49926, false, false, [], []⟩,
        ⟨49927, false, false, [], []⟩,
        ⟨49928, false, false, [], []⟩,
        ⟨49928, false, false, [], []⟩
      ]⟩,
    ⟨[22659, 83447], [22659, 83447], .contexts []⟩,
    ⟨[88315], [88315], .contexts []⟩,
    ⟨[83447, 7], [22661, 88315], .contexts [
        ⟨49930, true, false, [22658], [7]⟩,
        ⟨21229, true, false, [], [7]⟩,
        ⟨49929, true, false, [22658], [1, 7]⟩,
        ⟨502, false, false, [22658, 88317], []⟩,
        ⟨9, false, false, [22658, 88317], []⟩,
        ⟨49608, false, false, [22658], []⟩,
        ⟨49609, false, false, [22658], []⟩,
        ⟨49544, false, false, [22658], []⟩,
        ⟨49544, false, false, [22658], []⟩,
        ⟨49931, false, false, [22658], []⟩,
        ⟨49900, true, false, [], [88315]⟩
      ]⟩,
    ⟨[88341], [88205, 11], .source 44235⟩,
    ⟨[88205, 11], [88341], .contexts [
        ⟨49933, true, false, [], []⟩
      ]⟩,
    ⟨[88341, 11], [88205], .contexts [
        ⟨49934, true, false, [], [11]⟩,
        ⟨53, false, false, [88205], []⟩,
        ⟨49179, false, false, [], []⟩
      ]⟩,
    ⟨[88341], [88341], .contexts []⟩,
    ⟨[88341], [88341], .contexts []⟩,
    ⟨[88205, 11], [88341], .contexts [
        ⟨49934, false, false, [], []⟩,
        ⟨49936, false, false, [], []⟩,
        ⟨49937, false, false, [], []⟩,
        ⟨49937, false, false, [], []⟩
      ]⟩,
    ⟨[88341, 3], [82831], .contexts [
        ⟨49938, true, false, [], [3]⟩,
        ⟨215, false, false, [88205], []⟩,
        ⟨216, false, false, [88205], []⟩,
        ⟨49177, false, false, [], [11]⟩,
        ⟨5120, false, false, [], [11]⟩,
        ⟨5121, false, false, [], [11]⟩,
        ⟨5121, false, false, [], [11]⟩,
        ⟨17225, false, false, [], []⟩,
        ⟨17205, false, false, [], []⟩,
        ⟨17206, false, false, [], []⟩,
        ⟨17206, false, false, [], []⟩,
        ⟨17269, false, false, [], []⟩,
        ⟨17270, false, false, [], []⟩
      ]⟩,
    ⟨[82831, 3], [88341], .contexts [
        ⟨49939, true, false, [], [3]⟩,
        ⟨20, false, false, [88341], []⟩,
        ⟨49937, false, false, [], []⟩
      ]⟩,
    ⟨[315, 88341], [315, 88341], .contexts []⟩,
    ⟨[88341], [88341], .contexts []⟩,
    ⟨[86227], [20639, 85249], .contexts [
        ⟨42633, false, false, [], []⟩
      ]⟩,
    ⟨[88341, 7], [88341, 7], .contexts []⟩,
    ⟨[20639], [20639], .contexts [
        ⟨13, false, false, [], [20639]⟩
      ]⟩,
    ⟨[88341, 7], [20639, 85249], .contexts [
        ⟨49944, false, false, [], []⟩,
        ⟨49938, true, false, [], [7]⟩,
        ⟨647, false, false, [88205], []⟩,
        ⟨648, false, false, [88205], []⟩,
        ⟨49193, false, false, [], [11]⟩,
        ⟨49194, false, false, [], [11]⟩,
        ⟨17791, false, false, [], [11]⟩,
        ⟨17792, false, false, [], [11]⟩,
        ⟨17792, false, false, [], [11]⟩,
        ⟨36028, false, false, [], []⟩,
        ⟨49943, false, false, [], []⟩,
        ⟨42632, false, false, [], []⟩,
        ⟨42632, false, false, [], []⟩,
        ⟨30951, false, false, [20639], []⟩,
        ⟨49945, true, false, [], [85249]⟩
      ]⟩,
    ⟨[2241, 88341], [2241, 88341], .contexts []⟩,
    ⟨[88341, 9], [2241, 88341], .contexts [
        ⟨49938, true, false, [], [9]⟩,
        ⟨221, false, false, [88205], []⟩,
        ⟨224, false, false, [88205], []⟩,
        ⟨49195, false, false, [], [11, 9, 11]⟩,
        ⟨49196, false, false, [], [11, 9, 11]⟩,
        ⟨27860, false, false, [], [11, 9, 11]⟩,
        ⟨27861, false, false, [], [11, 9, 11]⟩,
        ⟨27861, false, false, [], [11, 9, 11]⟩,
        ⟨27898, false, false, [], [9, 11]⟩,
        ⟨27871, false, false, [], [9, 11]⟩,
        ⟨27872, false, false, [], [9, 11]⟩,
        ⟨27872, false, false, [], [9, 11]⟩,
        ⟨49197, false, false, [2241], [11]⟩,
        ⟨49934, false, false, [2241], []⟩,
        ⟨49947, false, false, [], []⟩,
        ⟨49942, false, false, [2241], []⟩
      ]⟩,
    ⟨[88341, 9], [2241, 88341], .contexts [
        ⟨49948, false, false, [], []⟩,
        ⟨4929, true, false, [], [88341]⟩
      ]⟩,
    ⟨[1075, 88341], [1075, 88341], .contexts []⟩,
    ⟨[1075, 88341], [1075, 88341], .contexts []⟩,
    ⟨[88341, 13], [88341, 13], .contexts []⟩,
    ⟨[88341, 13], [1075, 88341], .contexts [
        ⟨49952, false, false, [], []⟩,
        ⟨49938, true, false, [], [13]⟩,
        ⟨227, false, false, [88205], []⟩,
        ⟨228, false, false, [88205], []⟩,
        ⟨49200, false, false, [], [11]⟩,
        ⟨49201, false, false, [], [11]⟩,
        ⟨49198, false, false, [], [11]⟩,
        ⟨49199, false, false, [], [11]⟩,
        ⟨49199, false, false, [], [11]⟩,
        ⟨49934, false, false, [1075], []⟩,
        ⟨49950, false, false, [], []⟩,
        ⟨49951, false, false, [], []⟩,
        ⟨49942, false, false, [1075], []⟩,
        ⟨4778, true, false, [], [88341]⟩
      ]⟩,
    ⟨[88343], [85259, 5], .source 44236⟩,
    ⟨[85259, 5], [88343], .contexts [
        ⟨49954, true, false, [], []⟩
      ]⟩,
    ⟨[88343, 5], [85259], .contexts [
        ⟨49955, true, false, [], [5]⟩,
        ⟨28, false, false, [85259], []⟩,
        ⟨30973, false, false, [], []⟩
      ]⟩,
    ⟨[88343], [88343], .contexts []⟩,
    ⟨[85259, 5], [88343], .contexts [
        ⟨49955, false, false, [], []⟩,
        ⟨49957, false, false, [], []⟩,
        ⟨49957, false, false, [], []⟩
      ]⟩,
    ⟨[20773, 83325], [20773, 83325], .contexts []⟩,
    ⟨[20773, 83325], [20773, 83325], .contexts []⟩,
    ⟨[22671], [20773, 20419], .source 11400⟩,
    ⟨[88343, 1], [88343, 1], .contexts []⟩,
    ⟨[22671], [22671], .contexts []⟩,
    ⟨[22671], [22671], .contexts []⟩,
    ⟨[22671], [22671], .contexts [
        ⟨13, false, false, [], [22671]⟩,
        ⟨49963, false, false, [], []⟩,
        ⟨49964, false, false, [], []⟩
      ]⟩,
    ⟨[88343, 1], [22671, 87417], .contexts [
        ⟨49962, false, false, [], []⟩,
        ⟨49958, true, false, [], [1]⟩,
        ⟨161, false, false, [85259], []⟩,
        ⟨162, false, false, [85259], []⟩,
        ⟨42690, false, false, [], [5]⟩,
        ⟨49959, false, false, [], [5]⟩,
        ⟨49960, false, false, [], [5]⟩,
        ⟨49960, false, false, [], [5]⟩,
        ⟨42332, false, false, [20773], []⟩,
        ⟨49961, true, false, [], [87417]⟩,
        ⟨42129, false, false, [22671], []⟩,
        ⟨49965, true, false, [], [87417]⟩
      ]⟩,
    ⟨[22673], [22670], .source 11401⟩,
    ⟨[87417, 1], [22673, 88343], .contexts [
        ⟨49966, true, false, [22670], [1]⟩,
        ⟨8, false, false, [22670, 88343], []⟩,
        ⟨49967, true, false, [], [88343]⟩
      ]⟩,
    ⟨[20775, 79013], [20775, 79013], .contexts []⟩,
    ⟨[20775, 79013], [20775, 79013], .contexts []⟩,
    ⟨[85259, 3], [20775, 79013], .contexts [
        ⟨42693, false, false, [], []⟩,
        ⟨49969, false, false, [], []⟩,
        ⟨49970, false, false, [], []⟩,
        ⟨49970, false, false, [], []⟩
      ]⟩,
    ⟨[22675], [20775, 1753], .source 11402⟩,
    ⟨[22675, 82787], [22675, 82787], .contexts []⟩,
    ⟨[88343, 3], [22675, 82787], .contexts [
        ⟨49958, true, false, [], [3]⟩,
        ⟨166, false, false, [85259], []⟩,
        ⟨169, false, false, [85259], []⟩,
        ⟨49971, false, false, [], [5, 3, 5]⟩,
        ⟨5557, false, false, [20775], [3, 5]⟩,
        ⟨5521, false, false, [20775], [5]⟩,
        ⟨49972, true, false, [], [79005, 5]⟩,
        ⟨16635, false, false, [22675], []⟩,
        ⟨49973, false, false, [], []⟩,
        ⟨16644, false, false, [22675], []⟩,
        ⟨13, true, false, [], [22675, 82787]⟩
      ]⟩,
    ⟨[22677], [22674], .source 11403⟩,
    ⟨[82787, 3], [22677, 88343], .contexts [
        ⟨49974, true, false, [22674], [3]⟩,
        ⟨20, false, false, [22674, 88343], []⟩,
        ⟨49975, true, false, [], [88343]⟩
      ]⟩,
    ⟨[20777, 83375], [20777, 83375], .contexts []⟩,
    ⟨[20777, 83375], [20777, 83375], .contexts []⟩,
    ⟨[85259, 7], [20777, 83375], .contexts [
        ⟨42695, false, false, [], []⟩,
        ⟨49977, false, false, [], []⟩,
        ⟨49978, false, false, [], []⟩,
        ⟨49978, false, false, [], []⟩
      ]⟩,
    ⟨[22679], [20777, 16221], .source 11404⟩,
    ⟨[22681], [22679, 19521], .source 11405⟩,
    ⟨[86807], [86807], .contexts []⟩,
    ⟨[88343, 7], [22681, 86807], .contexts [
        ⟨49958, true, false, [], [7]⟩,
        ⟨3272, false, false, [85259], []⟩,
        ⟨3275, false, false, [85259], []⟩,
        ⟨49979, false, false, [], [5, 7, 5]⟩,
        ⟨21069, false, false, [20777], [7, 5]⟩,
        ⟨32469, false, false, [20777], [5]⟩,
        ⟨49980, true, false, [], [85499, 5]⟩,
        ⟨39095, false, false, [22679], []⟩,
        ⟨49981, true, false, [], [86807]⟩,
        ⟨49982, false, false, [22681], []⟩,
        ⟨13, true, false, [], [22681, 86807]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 781. -/
def y322TCIndexRaw781 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[22683], [22680], .source 11406⟩,
    ⟨[86807, 7], [22683, 88343], .contexts [
        ⟨49983, true, false, [22680], [7]⟩,
        ⟨38, false, false, [22680, 88343], []⟩,
        ⟨49984, true, false, [], [88343]⟩
      ]⟩,
    ⟨[85259, 9], [85257], .contexts [
        ⟨31148, false, false, [], []⟩,
        ⟨31149, false, false, [], []⟩,
        ⟨30969, false, false, [], []⟩,
        ⟨30969, false, false, [], []⟩
      ]⟩,
    ⟨[20759, 85615], [20759, 85615], .contexts []⟩,
    ⟨[20759, 85615], [20759, 85615], .contexts []⟩,
    ⟨[88343, 9], [20759, 85615], .contexts [
        ⟨49958, true, false, [], [9]⟩,
        ⟨1265, false, false, [85259], []⟩,
        ⟨1266, false, false, [85259], []⟩,
        ⟨49986, false, false, [], [5]⟩,
        ⟨42678, false, false, [], []⟩,
        ⟨49987, false, false, [], []⟩,
        ⟨49988, false, false, [], []⟩,
        ⟨49988, false, false, [], []⟩,
        ⟨32873, false, false, [20759], []⟩,
        ⟨13, true, false, [], [20759, 85615]⟩
      ]⟩,
    ⟨[20775, 84489], [20775, 84489], .contexts []⟩,
    ⟨[20775], [20775], .contexts [
        ⟨13, false, false, [], [20775]⟩
      ]⟩,
    ⟨[88343, 11], [20775, 84489], .contexts [
        ⟨49958, true, false, [], [11]⟩,
        ⟨174, false, false, [85259], []⟩,
        ⟨175, false, false, [85259], []⟩,
        ⟨30972, false, false, [], [5]⟩,
        ⟨42701, false, false, [], [5]⟩,
        ⟨42700, false, false, [], [5]⟩,
        ⟨42700, false, false, [], [5]⟩,
        ⟨27080, false, false, [20775], []⟩,
        ⟨49990, false, false, [], []⟩,
        ⟨49991, true, false, [], [84489]⟩
      ]⟩,
    ⟨[20773, 83329], [20773, 83329], .contexts []⟩,
    ⟨[20773, 83329], [20773, 83329], .contexts []⟩,
    ⟨[85259, 15], [20773, 83329], .contexts [
        ⟨42696, false, false, [], []⟩,
        ⟨49993, false, false, [], []⟩,
        ⟨49994, false, false, [], []⟩,
        ⟨49994, false, false, [], []⟩
      ]⟩,
    ⟨[88345], [87417, 9], .source 44237⟩,
    ⟨[87417, 9], [88345], .contexts [
        ⟨49996, true, false, [], []⟩
      ]⟩,
    ⟨[88345, 9], [87417], .contexts [
        ⟨49997, true, false, [], [9]⟩,
        ⟨46, false, false, [87417], []⟩,
        ⟨41574, false, false, [], []⟩
      ]⟩,
    ⟨[87417, 9], [88345], .contexts [
        ⟨49997, false, false, [], []⟩
      ]⟩,
    ⟨[88345], [88345], .contexts []⟩,
    ⟨[88345], [88345], .contexts []⟩,
    ⟨[87417, 9], [88345], .contexts [
        ⟨49999, false, false, [], []⟩,
        ⟨50000, false, false, [], []⟩,
        ⟨50001, false, false, [], []⟩,
        ⟨50001, false, false, [], []⟩
      ]⟩,
    ⟨[22673, 88343], [22673, 88343], .contexts []⟩,
    ⟨[22673, 88343], [22673, 88343], .contexts []⟩,
    ⟨[22685], [22673, 20759], .source 11407⟩,
    ⟨[22687], [22685, 20745], .source 11408⟩,
    ⟨[22689], [22687, 20743], .source 11409⟩,
    ⟨[88345, 1], [88345, 1], .contexts []⟩,
    ⟨[88345, 1], [22689, 85619], .contexts [
        ⟨50008, false, false, [], []⟩,
        ⟨50002, true, false, [], [1]⟩,
        ⟨691, false, false, [87417], []⟩,
        ⟨694, false, false, [87417], []⟩,
        ⟨49968, false, false, [], [9, 1, 9]⟩,
        ⟨50003, false, false, [], [9, 1, 9]⟩,
        ⟨50004, false, false, [], [9, 1, 9]⟩,
        ⟨50004, false, false, [], [9, 1, 9]⟩,
        ⟨49989, false, false, [22673], [1, 9]⟩,
        ⟨50005, true, false, [], [85615, 1, 9]⟩,
        ⟨32878, false, false, [22685], [9]⟩,
        ⟨42655, false, false, [22685], [9]⟩,
        ⟨50006, true, false, [], [85253, 9]⟩,
        ⟨42650, false, false, [22687], []⟩,
        ⟨50007, true, false, [], [85619]⟩,
        ⟨36074, false, false, [22689], []⟩
      ]⟩,
    ⟨[88345, 1], [22689, 85619], .contexts [
        ⟨50009, false, false, [], []⟩,
        ⟨13, true, false, [], [22689, 85619]⟩
      ]⟩,
    ⟨[22691], [22688], .source 11410⟩,
    ⟨[20517, 88345], [20517, 88345], .contexts []⟩,
    ⟨[88345], [88345], .contexts []⟩,
    ⟨[22693], [20421, 19893], .source 11411⟩,
    ⟨[88345, 5], [22693, 83895], .contexts [
        ⟨50002, true, false, [], [5]⟩,
        ⟨1079, false, false, [87417], []⟩,
        ⟨1080, false, false, [87417], []⟩,
        ⟨42332, true, false, [20418], [5, 9]⟩,
        ⟨28, false, false, [20418, 83325], [9]⟩,
        ⟨41969, true, false, [], [83325, 9]⟩,
        ⟨42325, false, false, [], [9]⟩,
        ⟨42326, false, false, [], [9]⟩,
        ⟨42326, false, false, [], [9]⟩,
        ⟨40414, false, false, [20421], []⟩,
        ⟨50014, true, false, [], [83895]⟩,
        ⟨40456, false, false, [22693], []⟩,
        ⟨13, true, false, [], [22693, 83895]⟩
      ]⟩,
    ⟨[22695], [22692], .source 11412⟩,
    ⟨[83895, 5], [22695, 88345], .contexts [
        ⟨50015, true, false, [22692], [5]⟩,
        ⟨28, false, false, [22692, 88345], []⟩,
        ⟨50016, true, false, [], [88345]⟩
      ]⟩,
    ⟨[87417, 11], [20625, 84491], .contexts [
        ⟨42349, false, false, [], []⟩
      ]⟩,
    ⟨[20625, 84491], [20625, 84491], .contexts []⟩,
    ⟨[20625, 84491], [20625, 84491], .contexts []⟩,
    ⟨[22697], [20625, 22267], .source 11413⟩,
    ⟨[22697, 85623], [22697, 85623], .contexts [
        ⟨36112, false, false, [22697], []⟩
      ]⟩,
    ⟨[88345, 11], [22697, 85623], .contexts [
        ⟨50002, true, false, [], [11]⟩,
        ⟨2344, false, false, [87417], []⟩,
        ⟨2346, false, false, [87417], []⟩,
        ⟨50018, false, false, [], [9, 11, 9]⟩,
        ⟨50019, false, false, [], [9, 11, 9]⟩,
        ⟨50020, false, false, [], [9, 11, 9]⟩,
        ⟨50020, false, false, [], [9, 11, 9]⟩,
        ⟨27131, false, false, [20625], [11, 9]⟩,
        ⟨27146, false, false, [20625], [9]⟩,
        ⟨48315, false, false, [20625], []⟩,
        ⟨50021, true, false, [], [85623]⟩,
        ⟨50022, false, false, [], []⟩
      ]⟩,
    ⟨[22697], [22697], .contexts [
        ⟨13, false, false, [], [22697]⟩
      ]⟩,
    ⟨[22697, 85623], [22697, 85623], .contexts [
        ⟨50024, true, false, [], [85623]⟩
      ]⟩,
    ⟨[88345, 11], [22697, 85623], .contexts [
        ⟨50023, false, false, [], []⟩,
        ⟨50025, false, false, [], []⟩
      ]⟩,
    ⟨[22699], [22696], .source 11414⟩,
    ⟨[85623, 11], [22699, 88345], .contexts [
        ⟨50026, true, false, [22696], [11]⟩,
        ⟨53, false, false, [22696, 88345], []⟩,
        ⟨50027, true, false, [], [88345]⟩
      ]⟩,
    ⟨[88347], [85621, 13], .source 44238⟩,
    ⟨[85621, 13], [88347], .contexts [
        ⟨50029, true, false, [], []⟩
      ]⟩,
    ⟨[88347, 13], [85621], .contexts [
        ⟨50030, true, false, [], [13]⟩,
        ⟨59, false, false, [85621], []⟩,
        ⟨32894, false, false, [], []⟩
      ]⟩,
    ⟨[85621, 13], [88347], .contexts [
        ⟨50030, false, false, [], []⟩
      ]⟩,
    ⟨[88347], [88347], .contexts []⟩,
    ⟨[88347], [88347], .contexts []⟩,
    ⟨[18975, 86233], [18975, 86233], .contexts []⟩,
    ⟨[18975, 86233], [18975, 86233], .contexts []⟩,
    ⟨[18975, 86235], [18975, 86235], .contexts []⟩,
    ⟨[18975, 86235], [18975, 86235], .contexts []⟩,
    ⟨[88347, 3], [88347, 3], .contexts []⟩,
    ⟨[86235], [86235], .contexts []⟩,
    ⟨[18975], [18975], .contexts [
        ⟨13, false, false, [], [18975]⟩
      ]⟩,
    ⟨[88347, 3], [18975, 86235], .contexts [
        ⟨50039, false, false, [], []⟩,
        ⟨50034, true, false, [], [3]⟩,
        ⟨50034, true, false, [], [3]⟩,
        ⟨50033, true, false, [], [3]⟩,
        ⟨50032, true, false, [], [3]⟩,
        ⟨63, false, false, [85621], []⟩,
        ⟨65, false, false, [85621], []⟩,
        ⟨36095, false, false, [], [13]⟩,
        ⟨50035, false, false, [], [13]⟩,
        ⟨50036, false, false, [], [13]⟩,
        ⟨50036, false, false, [], [13]⟩,
        ⟨36162, false, false, [18975], []⟩,
        ⟨50037, false, false, [], []⟩,
        ⟨50038, false, false, [], []⟩,
        ⟨50040, false, false, [18975], []⟩,
        ⟨50041, true, false, [], [86235]⟩
      ]⟩,
    ⟨[18973], [18974], .contexts [
        ⟨36045, true, true, [], []⟩
      ]⟩,
    ⟨[88349], [88347, 15], .source 44239⟩,
    ⟨[88347, 15], [88349], .contexts [
        ⟨50044, true, false, [], []⟩
      ]⟩,
    ⟨[88349, 15], [88347], .contexts [
        ⟨50045, true, false, [], [15]⟩,
        ⟨1, false, false, [88347], []⟩,
        ⟨50034, false, false, [], []⟩
      ]⟩,
    ⟨[88349], [88349], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 782. -/
def y322TCIndexRaw782 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88349], [88349], .contexts []⟩,
    ⟨[88347, 15], [88349], .contexts [
        ⟨50045, false, false, [], []⟩,
        ⟨50047, false, false, [], []⟩,
        ⟨50048, false, false, [], []⟩,
        ⟨50048, false, false, [], []⟩
      ]⟩,
    ⟨[18975, 86237], [18975, 86237], .contexts []⟩,
    ⟨[18975, 86237], [18975, 86237], .contexts []⟩,
    ⟨[86237], [86237], .contexts []⟩,
    ⟨[88349, 3], [18975, 86237], .contexts [
        ⟨50049, true, false, [], [3]⟩,
        ⟨19, false, false, [88347], []⟩,
        ⟨22, false, false, [88347], []⟩,
        ⟨50039, false, false, [], [15]⟩,
        ⟨50042, false, false, [], [15]⟩,
        ⟨50037, false, false, [], [15]⟩,
        ⟨50038, false, false, [], [15]⟩,
        ⟨50038, false, false, [], [15]⟩,
        ⟨36165, false, false, [18975], []⟩,
        ⟨50050, false, false, [], []⟩,
        ⟨50051, false, false, [], []⟩,
        ⟨50052, false, false, [18975], []⟩,
        ⟨50041, true, false, [], [86237]⟩
      ]⟩,
    ⟨[86237, 3], [18973, 88349], .contexts [
        ⟨50053, true, false, [18974], [3]⟩,
        ⟨20, false, false, [18974, 88349], []⟩,
        ⟨50043, true, false, [], [88349]⟩
      ]⟩,
    ⟨[88351], [88349, 1], .source 44240⟩,
    ⟨[88349, 1], [88351], .contexts [
        ⟨50055, true, false, [], []⟩
      ]⟩,
    ⟨[88351, 1], [88349], .contexts [
        ⟨50056, true, false, [], [1]⟩,
        ⟨8, false, false, [88349], []⟩,
        ⟨50048, false, false, [], []⟩
      ]⟩,
    ⟨[88353], [88351, 3], .source 44241⟩,
    ⟨[88351, 3], [88353], .contexts [
        ⟨50058, true, false, [], []⟩
      ]⟩,
    ⟨[88351], [88351], .contexts []⟩,
    ⟨[88353, 3], [88351], .contexts [
        ⟨50059, true, false, [], [3]⟩,
        ⟨20, false, false, [88351], []⟩,
        ⟨50060, false, false, [], []⟩
      ]⟩,
    ⟨[88353], [88353], .contexts []⟩,
    ⟨[88353], [88353], .contexts []⟩,
    ⟨[88351, 3], [88353], .contexts [
        ⟨50059, false, false, [], []⟩,
        ⟨50062, false, false, [], []⟩,
        ⟨50063, false, false, [], []⟩,
        ⟨50063, false, false, [], []⟩
      ]⟩,
    ⟨[18975, 86241], [18975, 86241], .contexts []⟩,
    ⟨[18975, 86241], [18975, 86241], .contexts []⟩,
    ⟨[88353, 1], [88353, 1], .contexts []⟩,
    ⟨[86241], [86241], .contexts []⟩,
    ⟨[88353, 1], [18975, 86241], .contexts [
        ⟨50067, false, false, [], []⟩,
        ⟨50064, true, false, [], [1]⟩,
        ⟨130, false, false, [88351], []⟩,
        ⟨133, false, false, [88351], []⟩,
        ⟨50057, false, false, [], [3, 1, 3]⟩,
        ⟨50047, false, false, [], [3, 1, 3]⟩,
        ⟨50048, false, false, [], [3, 1, 3]⟩,
        ⟨50048, false, false, [], [3, 1, 3]⟩,
        ⟨50053, false, false, [], [1, 3]⟩,
        ⟨50050, false, false, [], [1, 3]⟩,
        ⟨50051, false, false, [], [1, 3]⟩,
        ⟨50051, false, false, [], [1, 3]⟩,
        ⟨36169, false, false, [18975], [3]⟩,
        ⟨36173, false, false, [18975], []⟩,
        ⟨50065, false, false, [], []⟩,
        ⟨50066, false, false, [], []⟩,
        ⟨50068, false, false, [18975], []⟩
      ]⟩,
    ⟨[88353, 1], [18975, 86241], .contexts [
        ⟨50069, false, false, [], []⟩,
        ⟨50041, true, false, [], [86241]⟩
      ]⟩,
    ⟨[86241, 1], [18973, 88353], .contexts [
        ⟨50070, true, false, [18974], [1]⟩,
        ⟨8, false, false, [18974, 88353], []⟩,
        ⟨50043, true, false, [], [88353]⟩
      ]⟩,
    ⟨[18975, 86245], [18975, 86245], .contexts []⟩,
    ⟨[88353], [88353], .contexts []⟩,
    ⟨[18974], [18974], .contexts []⟩,
    ⟨[86245, 5], [18973, 88353], .contexts [
        ⟨50072, true, false, [18974], [5]⟩,
        ⟨36181, true, false, [], [5]⟩,
        ⟨36177, true, false, [], [1, 5]⟩,
        ⟨50066, true, false, [18974], [5, 1, 5]⟩,
        ⟨50066, true, false, [18974], [5, 1, 5]⟩,
        ⟨50065, true, false, [18974], [5, 1, 5]⟩,
        ⟨50070, true, false, [18974], [5, 1, 5]⟩,
        ⟨50067, true, false, [18974], [5, 1, 5]⟩,
        ⟨1152, false, false, [18974, 88353], []⟩,
        ⟨50073, false, false, [18974], []⟩,
        ⟨50074, true, false, [], [88353]⟩,
        ⟨50074, true, false, [], [88353]⟩,
        ⟨50043, true, false, [], [88353]⟩
      ]⟩,
    ⟨[88353, 5], [18975, 86245], .contexts [
        ⟨50075, true, false, [18972], [5]⟩,
        ⟨28, false, false, [18972, 86245], []⟩,
        ⟨36045, true, false, [], [86245]⟩
      ]⟩,
    ⟨[88355], [86243, 9], .source 44242⟩,
    ⟨[86243, 9], [88355], .contexts [
        ⟨50077, true, false, [], []⟩
      ]⟩,
    ⟨[88355, 9], [86243], .contexts [
        ⟨50078, true, false, [], [9]⟩,
        ⟨46, false, false, [86243], []⟩,
        ⟨36182, false, false, [], []⟩
      ]⟩,
    ⟨[88357], [88355, 11], .source 44243⟩,
    ⟨[88355, 11], [88357], .contexts [
        ⟨50080, true, false, [], []⟩
      ]⟩,
    ⟨[88355], [88355], .contexts []⟩,
    ⟨[88359], [88357, 1], .source 44244⟩,
    ⟨[88357, 1], [88359], .contexts [
        ⟨50083, true, false, [], []⟩
      ]⟩,
    ⟨[88357], [88357], .contexts []⟩,
    ⟨[88359, 1], [88357], .contexts [
        ⟨50084, true, false, [], [1]⟩,
        ⟨8, false, false, [88357], []⟩,
        ⟨50085, false, false, [], []⟩
      ]⟩,
    ⟨[88361], [88359, 13], .source 44245⟩,
    ⟨[88359, 13], [88361], .contexts [
        ⟨50087, true, false, [], []⟩
      ]⟩,
    ⟨[88359], [88359], .contexts []⟩,
    ⟨[88361, 13], [88359], .contexts [
        ⟨50088, true, false, [], [13]⟩,
        ⟨59, false, false, [88359], []⟩,
        ⟨50089, false, false, [], []⟩
      ]⟩,
    ⟨[88363], [88361, 15], .source 44246⟩,
    ⟨[88361, 15], [88363], .contexts [
        ⟨50091, true, false, [], []⟩
      ]⟩,
    ⟨[88361], [88361], .contexts []⟩,
    ⟨[88363, 15], [88361], .contexts [
        ⟨50092, true, false, [], [15]⟩,
        ⟨1, false, false, [88361], []⟩,
        ⟨50093, false, false, [], []⟩
      ]⟩,
    ⟨[88365], [88363, 1], .source 44247⟩,
    ⟨[88363, 1], [88365], .contexts [
        ⟨50095, true, false, [], []⟩
      ]⟩,
    ⟨[88363], [88363], .contexts []⟩,
    ⟨[88365, 1], [88363], .contexts [
        ⟨50096, true, false, [], [1]⟩,
        ⟨8, false, false, [88363], []⟩,
        ⟨50097, false, false, [], []⟩
      ]⟩,
    ⟨[88367], [88365, 3], .source 44248⟩,
    ⟨[88365, 3], [88367], .contexts [
        ⟨50099, true, false, [], []⟩
      ]⟩,
    ⟨[88365], [88365], .contexts []⟩,
    ⟨[88367, 3], [88365], .contexts [
        ⟨50100, true, false, [], [3]⟩,
        ⟨20, false, false, [88365], []⟩,
        ⟨50101, false, false, [], []⟩
      ]⟩,
    ⟨[88369], [88367, 5], .source 44249⟩,
    ⟨[88367, 5], [88369], .contexts [
        ⟨50103, true, false, [], []⟩
      ]⟩,
    ⟨[88367], [88367], .contexts []⟩,
    ⟨[88371], [88369, 1], .source 44250⟩,
    ⟨[88369], [88369], .contexts []⟩,
    ⟨[88371, 1], [88369], .contexts [
        ⟨50106, false, false, [], [1]⟩,
        ⟨8, false, false, [88369], []⟩,
        ⟨50107, false, false, [], []⟩
      ]⟩,
    ⟨[88373], [88371, 9], .source 44251⟩,
    ⟨[88371, 9], [88373], .contexts [
        ⟨50109, true, false, [], []⟩
      ]⟩,
    ⟨[88371], [88371], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 783. -/
def y322TCIndexRaw783 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88373, 9], [88371], .contexts [
        ⟨50110, true, false, [], [9]⟩,
        ⟨46, false, false, [88371], []⟩,
        ⟨50111, false, false, [], []⟩
      ]⟩,
    ⟨[88375], [88373, 11], .source 44252⟩,
    ⟨[88373], [88373], .contexts []⟩,
    ⟨[88375, 11], [88373], .contexts [
        ⟨50113, false, false, [], [11]⟩,
        ⟨53, false, false, [88373], []⟩,
        ⟨50114, false, false, [], []⟩
      ]⟩,
    ⟨[88377], [88375, 1], .source 44253⟩,
    ⟨[88375], [88375], .contexts []⟩,
    ⟨[88377, 1], [88375], .contexts [
        ⟨50116, false, false, [], [1]⟩,
        ⟨8, false, false, [88375], []⟩,
        ⟨50117, false, false, [], []⟩
      ]⟩,
    ⟨[88379], [88377, 13], .source 44254⟩,
    ⟨[88377], [88377], .contexts []⟩,
    ⟨[88379, 13], [88377], .contexts [
        ⟨50119, false, false, [], [13]⟩,
        ⟨59, false, false, [88377], []⟩,
        ⟨50120, false, false, [], []⟩
      ]⟩,
    ⟨[88381], [88379, 15], .source 44255⟩,
    ⟨[88379], [88379], .contexts []⟩,
    ⟨[88381, 15], [88379], .contexts [
        ⟨50122, false, false, [], [15]⟩,
        ⟨1, false, false, [88379], []⟩,
        ⟨50123, false, false, [], []⟩
      ]⟩,
    ⟨[88383], [88381, 1], .source 44256⟩,
    ⟨[88381], [88381], .contexts []⟩,
    ⟨[88383, 1], [88381], .contexts [
        ⟨50125, false, false, [], [1]⟩,
        ⟨8, false, false, [88381], []⟩,
        ⟨50126, false, false, [], []⟩
      ]⟩,
    ⟨[88385], [88383, 3], .source 44257⟩,
    ⟨[88383, 3], [88385], .contexts [
        ⟨50128, true, false, [], []⟩
      ]⟩,
    ⟨[88383], [88383], .contexts []⟩,
    ⟨[88385, 3], [88383], .contexts [
        ⟨50129, true, false, [], [3]⟩,
        ⟨20, false, false, [88383], []⟩,
        ⟨50130, false, false, [], []⟩
      ]⟩,
    ⟨[88387], [88385, 5], .source 44258⟩,
    ⟨[88385, 5], [88387], .contexts [
        ⟨50132, true, false, [], []⟩
      ]⟩,
    ⟨[88385], [88385], .contexts []⟩,
    ⟨[88387, 5], [88385], .contexts [
        ⟨50133, true, false, [], [5]⟩,
        ⟨28, false, false, [88385], []⟩,
        ⟨50134, false, false, [], []⟩
      ]⟩,
    ⟨[88389], [88387, 1], .source 44259⟩,
    ⟨[88387], [88387], .contexts []⟩,
    ⟨[88389, 1], [88387], .contexts [
        ⟨50136, false, false, [], [1]⟩,
        ⟨8, false, false, [88387], []⟩,
        ⟨50137, false, false, [], []⟩
      ]⟩,
    ⟨[88391], [88389, 9], .source 44260⟩,
    ⟨[88389], [88389], .contexts []⟩,
    ⟨[88391, 9], [88389], .contexts [
        ⟨50139, false, false, [], [9]⟩,
        ⟨46, false, false, [88389], []⟩,
        ⟨50140, false, false, [], []⟩
      ]⟩,
    ⟨[88393], [88391, 11], .source 44261⟩,
    ⟨[88391], [88391], .contexts []⟩,
    ⟨[88393, 11], [88391], .contexts [
        ⟨50142, false, false, [], [11]⟩,
        ⟨53, false, false, [88391], []⟩,
        ⟨50143, false, false, [], []⟩
      ]⟩,
    ⟨[88395], [88393, 1], .source 44262⟩,
    ⟨[88393, 1], [88395], .contexts [
        ⟨50145, true, false, [], []⟩
      ]⟩,
    ⟨[88393], [88393], .contexts []⟩,
    ⟨[88395, 1], [88393], .contexts [
        ⟨50146, true, false, [], [1]⟩,
        ⟨8, false, false, [88393], []⟩,
        ⟨50147, false, false, [], []⟩
      ]⟩,
    ⟨[88397], [88395, 13], .source 44263⟩,
    ⟨[88395, 13], [88397], .contexts [
        ⟨50149, true, false, [], []⟩
      ]⟩,
    ⟨[88395], [88395], .contexts []⟩,
    ⟨[88397, 13], [88395], .contexts [
        ⟨50150, true, false, [], [13]⟩,
        ⟨59, false, false, [88395], []⟩,
        ⟨50151, false, false, [], []⟩
      ]⟩,
    ⟨[88399], [88397, 15], .source 44264⟩,
    ⟨[88397, 15], [88399], .contexts [
        ⟨50153, true, false, [], []⟩
      ]⟩,
    ⟨[88397], [88397], .contexts []⟩,
    ⟨[88399, 15], [88397], .contexts [
        ⟨50154, true, false, [], [15]⟩,
        ⟨1, false, false, [88397], []⟩,
        ⟨50155, false, false, [], []⟩
      ]⟩,
    ⟨[88401], [88399, 1], .source 44265⟩,
    ⟨[88399, 1], [88401], .contexts [
        ⟨50157, true, false, [], []⟩
      ]⟩,
    ⟨[88399], [88399], .contexts []⟩,
    ⟨[88401, 1], [88399], .contexts [
        ⟨50158, true, false, [], [1]⟩,
        ⟨8, false, false, [88399], []⟩,
        ⟨50159, false, false, [], []⟩
      ]⟩,
    ⟨[88403], [88401, 3], .source 44266⟩,
    ⟨[88401, 3], [88403], .contexts [
        ⟨50161, true, false, [], []⟩
      ]⟩,
    ⟨[88401], [88401], .contexts []⟩,
    ⟨[88403, 3], [88401], .contexts [
        ⟨50162, true, false, [], [3]⟩,
        ⟨20, false, false, [88401], []⟩,
        ⟨50163, false, false, [], []⟩
      ]⟩,
    ⟨[88405], [88403, 5], .source 44267⟩,
    ⟨[88403, 5], [88405], .contexts [
        ⟨50165, true, false, [], []⟩
      ]⟩,
    ⟨[88403], [88403], .contexts []⟩,
    ⟨[88405, 5], [88403], .contexts [
        ⟨50166, true, false, [], [5]⟩,
        ⟨28, false, false, [88403], []⟩,
        ⟨50167, false, false, [], []⟩
      ]⟩,
    ⟨[88407], [88405, 1], .source 44268⟩,
    ⟨[88405, 1], [88407], .contexts [
        ⟨50169, true, false, [], []⟩
      ]⟩,
    ⟨[88405], [88405], .contexts []⟩,
    ⟨[88407, 1], [88405], .contexts [
        ⟨50170, true, false, [], [1]⟩,
        ⟨8, false, false, [88405], []⟩,
        ⟨50171, false, false, [], []⟩
      ]⟩,
    ⟨[88409], [88407, 9], .source 44269⟩,
    ⟨[88407, 9], [88409], .contexts [
        ⟨50173, true, false, [], []⟩
      ]⟩,
    ⟨[88407], [88407], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 784. -/
def y322TCIndexRaw784 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88409, 9], [88407], .contexts [
        ⟨50174, true, false, [], [9]⟩,
        ⟨46, false, false, [88407], []⟩,
        ⟨50175, false, false, [], []⟩
      ]⟩,
    ⟨[88411], [88409, 11], .source 44270⟩,
    ⟨[88409, 11], [88411], .contexts [
        ⟨50177, true, false, [], []⟩
      ]⟩,
    ⟨[88409], [88409], .contexts []⟩,
    ⟨[88411, 11], [88409], .contexts [
        ⟨50178, true, false, [], [11]⟩,
        ⟨53, false, false, [88409], []⟩,
        ⟨50179, false, false, [], []⟩
      ]⟩,
    ⟨[88413], [88411, 1], .source 44271⟩,
    ⟨[88411], [88411], .contexts []⟩,
    ⟨[88413, 1], [88411], .contexts [
        ⟨50181, false, false, [], [1]⟩,
        ⟨8, false, false, [88411], []⟩,
        ⟨50182, false, false, [], []⟩
      ]⟩,
    ⟨[88415], [88413, 13], .source 44272⟩,
    ⟨[88413, 13], [88415], .contexts [
        ⟨50184, true, false, [], []⟩
      ]⟩,
    ⟨[88413], [88413], .contexts []⟩,
    ⟨[88415, 13], [88413], .contexts [
        ⟨50185, true, false, [], [13]⟩,
        ⟨59, false, false, [88413], []⟩,
        ⟨50186, false, false, [], []⟩
      ]⟩,
    ⟨[88417], [88415, 15], .source 44273⟩,
    ⟨[88415, 15], [88417], .contexts [
        ⟨50188, true, false, [], []⟩
      ]⟩,
    ⟨[88415], [88415], .contexts []⟩,
    ⟨[88417, 15], [88415], .contexts [
        ⟨50189, true, false, [], [15]⟩,
        ⟨1, false, false, [88415], []⟩,
        ⟨50190, false, false, [], []⟩
      ]⟩,
    ⟨[88419], [88417, 1], .source 44274⟩,
    ⟨[88417], [88417], .contexts []⟩,
    ⟨[88419, 1], [88417], .contexts [
        ⟨50192, false, false, [], [1]⟩,
        ⟨8, false, false, [88417], []⟩,
        ⟨50193, false, false, [], []⟩
      ]⟩,
    ⟨[88421], [88419, 3], .source 44275⟩,
    ⟨[88419], [88419], .contexts []⟩,
    ⟨[88421, 3], [88419], .contexts [
        ⟨50195, false, false, [], [3]⟩,
        ⟨20, false, false, [88419], []⟩,
        ⟨50196, false, false, [], []⟩
      ]⟩,
    ⟨[88423], [88421, 5], .source 44276⟩,
    ⟨[88421], [88421], .contexts []⟩,
    ⟨[88423, 5], [88421], .contexts [
        ⟨50198, false, false, [], [5]⟩,
        ⟨28, false, false, [88421], []⟩,
        ⟨50199, false, false, [], []⟩
      ]⟩,
    ⟨[88425], [88423, 1], .source 44277⟩,
    ⟨[88423], [88423], .contexts []⟩,
    ⟨[88425, 1], [88423], .contexts [
        ⟨50201, false, false, [], [1]⟩,
        ⟨8, false, false, [88423], []⟩,
        ⟨50202, false, false, [], []⟩
      ]⟩,
    ⟨[88427], [88425, 9], .source 44278⟩,
    ⟨[88425], [88425], .contexts []⟩,
    ⟨[88427, 9], [88425], .contexts [
        ⟨50204, false, false, [], [9]⟩,
        ⟨46, false, false, [88425], []⟩,
        ⟨50205, false, false, [], []⟩
      ]⟩,
    ⟨[88429], [88427, 11], .source 44279⟩,
    ⟨[88427], [88427], .contexts []⟩,
    ⟨[88429, 11], [88427], .contexts [
        ⟨50207, false, false, [], [11]⟩,
        ⟨53, false, false, [88427], []⟩,
        ⟨50208, false, false, [], []⟩
      ]⟩,
    ⟨[88431], [88429, 1], .source 44280⟩,
    ⟨[88429], [88429], .contexts []⟩,
    ⟨[88431, 1], [88429], .contexts [
        ⟨50210, false, false, [], [1]⟩,
        ⟨8, false, false, [88429], []⟩,
        ⟨50211, false, false, [], []⟩
      ]⟩,
    ⟨[88433], [88431, 13], .source 44281⟩,
    ⟨[88431], [88431], .contexts []⟩,
    ⟨[88433, 13], [88431], .contexts [
        ⟨50213, false, false, [], [13]⟩,
        ⟨59, false, false, [88431], []⟩,
        ⟨50214, false, false, [], []⟩
      ]⟩,
    ⟨[88435], [88433, 15], .source 44282⟩,
    ⟨[88433, 15], [88435], .contexts [
        ⟨50216, true, false, [], []⟩
      ]⟩,
    ⟨[88433], [88433], .contexts []⟩,
    ⟨[88435, 15], [88433], .contexts [
        ⟨50217, true, false, [], [15]⟩,
        ⟨1, false, false, [88433], []⟩,
        ⟨50218, false, false, [], []⟩
      ]⟩,
    ⟨[88437], [88435, 1], .source 44283⟩,
    ⟨[88435], [88435], .contexts []⟩,
    ⟨[88437, 1], [88435], .contexts [
        ⟨50220, false, false, [], [1]⟩,
        ⟨8, false, false, [88435], []⟩,
        ⟨50221, false, false, [], []⟩
      ]⟩,
    ⟨[88439], [88437, 3], .source 44284⟩,
    ⟨[88437, 3], [88439], .contexts [
        ⟨50223, true, false, [], []⟩
      ]⟩,
    ⟨[88437], [88437], .contexts []⟩,
    ⟨[88439, 3], [88437], .contexts [
        ⟨50224, true, false, [], [3]⟩,
        ⟨20, false, false, [88437], []⟩,
        ⟨50225, false, false, [], []⟩
      ]⟩,
    ⟨[88441], [88439, 5], .source 44285⟩,
    ⟨[88439, 5], [88441], .contexts [
        ⟨50227, true, false, [], []⟩
      ]⟩,
    ⟨[88439], [88439], .contexts []⟩,
    ⟨[88441, 5], [88439], .contexts [
        ⟨50228, true, false, [], [5]⟩,
        ⟨28, false, false, [88439], []⟩,
        ⟨50229, false, false, [], []⟩
      ]⟩,
    ⟨[88443], [88441, 1], .source 44286⟩,
    ⟨[88441], [88441], .contexts []⟩,
    ⟨[88443, 1], [88441], .contexts [
        ⟨50231, false, false, [], [1]⟩,
        ⟨8, false, false, [88441], []⟩,
        ⟨50232, false, false, [], []⟩
      ]⟩,
    ⟨[88445], [88443, 9], .source 44287⟩,
    ⟨[88443], [88443], .contexts []⟩,
    ⟨[88445, 9], [88443], .contexts [
        ⟨50234, false, false, [], [9]⟩,
        ⟨46, false, false, [88443], []⟩,
        ⟨50235, false, false, [], []⟩
      ]⟩,
    ⟨[88447], [88445, 11], .source 44288⟩,
    ⟨[88445, 11], [88447], .contexts [
        ⟨50237, true, false, [], []⟩
      ]⟩,
    ⟨[88445], [88445], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 785. -/
def y322TCIndexRaw785 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88447, 11], [88445], .contexts [
        ⟨50238, true, false, [], [11]⟩,
        ⟨53, false, false, [88445], []⟩,
        ⟨50239, false, false, [], []⟩
      ]⟩,
    ⟨[88449], [88447, 1], .source 44289⟩,
    ⟨[88447], [88447], .contexts []⟩,
    ⟨[88449, 1], [88447], .contexts [
        ⟨50241, false, false, [], [1]⟩,
        ⟨8, false, false, [88447], []⟩,
        ⟨50242, false, false, [], []⟩
      ]⟩,
    ⟨[88451], [88449, 13], .source 44290⟩,
    ⟨[88449, 13], [88451], .contexts [
        ⟨50244, true, false, [], []⟩
      ]⟩,
    ⟨[88449], [88449], .contexts []⟩,
    ⟨[88451, 13], [88449], .contexts [
        ⟨50245, true, false, [], [13]⟩,
        ⟨59, false, false, [88449], []⟩,
        ⟨50246, false, false, [], []⟩
      ]⟩,
    ⟨[88453], [88451, 15], .source 44291⟩,
    ⟨[88451, 15], [88453], .contexts [
        ⟨50248, true, false, [], []⟩
      ]⟩,
    ⟨[88451], [88451], .contexts []⟩,
    ⟨[88453, 15], [88451], .contexts [
        ⟨50249, true, false, [], [15]⟩,
        ⟨1, false, false, [88451], []⟩,
        ⟨50250, false, false, [], []⟩
      ]⟩,
    ⟨[88455], [88453, 1], .source 44292⟩,
    ⟨[88453, 1], [88455], .contexts [
        ⟨50252, true, false, [], []⟩
      ]⟩,
    ⟨[88453], [88453], .contexts []⟩,
    ⟨[88455, 1], [88453], .contexts [
        ⟨50253, true, false, [], [1]⟩,
        ⟨8, false, false, [88453], []⟩,
        ⟨50254, false, false, [], []⟩
      ]⟩,
    ⟨[88457], [88455, 3], .source 44293⟩,
    ⟨[88455], [88455], .contexts []⟩,
    ⟨[88457, 3], [88455], .contexts [
        ⟨50256, false, false, [], [3]⟩,
        ⟨20, false, false, [88455], []⟩,
        ⟨50257, false, false, [], []⟩
      ]⟩,
    ⟨[88459], [88457, 5], .source 44294⟩,
    ⟨[88457], [88457], .contexts []⟩,
    ⟨[88459, 5], [88457], .contexts [
        ⟨50259, false, false, [], [5]⟩,
        ⟨28, false, false, [88457], []⟩,
        ⟨50260, false, false, [], []⟩
      ]⟩,
    ⟨[88461], [88459, 1], .source 44295⟩,
    ⟨[88459, 1], [88461], .contexts [
        ⟨50262, true, false, [], []⟩
      ]⟩,
    ⟨[88459], [88459], .contexts []⟩,
    ⟨[88461, 1], [88459], .contexts [
        ⟨50263, true, false, [], [1]⟩,
        ⟨8, false, false, [88459], []⟩,
        ⟨50264, false, false, [], []⟩
      ]⟩,
    ⟨[88463], [88461, 9], .source 44296⟩,
    ⟨[88461, 9], [88463], .contexts [
        ⟨50266, true, false, [], []⟩
      ]⟩,
    ⟨[88461], [88461], .contexts []⟩,
    ⟨[88463, 9], [88461], .contexts [
        ⟨50267, true, false, [], [9]⟩,
        ⟨46, false, false, [88461], []⟩,
        ⟨50268, false, false, [], []⟩
      ]⟩,
    ⟨[88465], [88463, 11], .source 44297⟩,
    ⟨[88463, 11], [88465], .contexts [
        ⟨50270, true, false, [], []⟩
      ]⟩,
    ⟨[88463], [88463], .contexts []⟩,
    ⟨[88465, 11], [88463], .contexts [
        ⟨50271, true, false, [], [11]⟩,
        ⟨53, false, false, [88463], []⟩,
        ⟨50272, false, false, [], []⟩
      ]⟩,
    ⟨[88467], [88465, 1], .source 44298⟩,
    ⟨[88465, 1], [88467], .contexts [
        ⟨50274, true, false, [], []⟩
      ]⟩,
    ⟨[88465], [88465], .contexts []⟩,
    ⟨[88467, 1], [88465], .contexts [
        ⟨50275, true, false, [], [1]⟩,
        ⟨8, false, false, [88465], []⟩,
        ⟨50276, false, false, [], []⟩
      ]⟩,
    ⟨[88469], [88467, 13], .source 44299⟩,
    ⟨[88467, 13], [88469], .contexts [
        ⟨50278, true, false, [], []⟩
      ]⟩,
    ⟨[88469, 13], [88467], .contexts [
        ⟨50279, true, false, [], [13]⟩,
        ⟨59, false, false, [88467], []⟩
      ]⟩,
    ⟨[88469], [88469], .contexts []⟩,
    ⟨[88469], [88469], .contexts []⟩,
    ⟨[88463], [88463], .contexts []⟩,
    ⟨[88461], [88461], .contexts []⟩,
    ⟨[88461, 1], [88459], .contexts [
        ⟨50265, false, false, [], []⟩
      ]⟩,
    ⟨[88457], [88457], .contexts []⟩,
    ⟨[88467, 1, 11, 9, 1, 5], [88457], .contexts [
        ⟨50277, false, false, [], [11, 9, 1, 5]⟩,
        ⟨50276, false, false, [], [11, 9, 1, 5]⟩,
        ⟨50276, false, false, [], [11, 9, 1, 5]⟩,
        ⟨50273, false, false, [], [9, 1, 5]⟩,
        ⟨50283, false, false, [], [9, 1, 5]⟩,
        ⟨50272, false, false, [], [9, 1, 5]⟩,
        ⟨50272, false, false, [], [9, 1, 5]⟩,
        ⟨50269, false, false, [], [1, 5]⟩,
        ⟨50284, false, false, [], [1, 5]⟩,
        ⟨50268, false, false, [], [1, 5]⟩,
        ⟨50268, false, false, [], [1, 5]⟩,
        ⟨50285, false, false, [], [5]⟩,
        ⟨50264, false, false, [], [5]⟩,
        ⟨50264, false, false, [], [5]⟩,
        ⟨50261, false, false, [], []⟩,
        ⟨50286, false, false, [], []⟩,
        ⟨50260, false, false, [], []⟩,
        ⟨50260, false, false, [], []⟩
      ]⟩,
    ⟨[88455], [88455], .contexts []⟩,
    ⟨[88453], [88453], .contexts []⟩,
    ⟨[88453, 15], [88451], .contexts [
        ⟨50251, false, false, [], []⟩
      ]⟩,
    ⟨[88451], [88451], .contexts []⟩,
    ⟨[88451, 13], [88449], .contexts [
        ⟨50247, false, false, [], []⟩
      ]⟩,
    ⟨[88449], [88449], .contexts []⟩,
    ⟨[88449, 1], [88447], .contexts [
        ⟨50243, false, false, [], []⟩
      ]⟩,
    ⟨[88447], [88447], .contexts []⟩,
    ⟨[88467, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1], [88447], .contexts [
        ⟨50287, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨50258, false, false, [], [1, 15, 13, 1]⟩,
        ⟨50288, false, false, [], [1, 15, 13, 1]⟩,
        ⟨50257, false, false, [], [1, 15, 13, 1]⟩,
        ⟨50257, false, false, [], [1, 15, 13, 1]⟩,
        ⟨50255, false, false, [], [15, 13, 1]⟩,
        ⟨50289, false, false, [], [15, 13, 1]⟩,
        ⟨50254, false, false, [], [15, 13, 1]⟩,
        ⟨50254, false, false, [], [15, 13, 1]⟩,
        ⟨50290, false, false, [], [13, 1]⟩,
        ⟨50291, false, false, [], [13, 1]⟩,
        ⟨50250, false, false, [], [13, 1]⟩,
        ⟨50250, false, false, [], [13, 1]⟩,
        ⟨50292, false, false, [], [1]⟩,
        ⟨50293, false, false, [], [1]⟩,
        ⟨50246, false, false, [], [1]⟩,
        ⟨50246, false, false, [], [1]⟩,
        ⟨50294, false, false, [], []⟩,
        ⟨50295, false, false, [], []⟩,
        ⟨50242, false, false, [], []⟩,
        ⟨50242, false, false, [], []⟩
      ]⟩,
    ⟨[88447, 11], [88445], .contexts [
        ⟨50240, false, false, [], []⟩
      ]⟩,
    ⟨[88445], [88445], .contexts []⟩,
    ⟨[88445, 9], [88443], .contexts [
        ⟨50236, false, false, [], []⟩
      ]⟩,
    ⟨[88443], [88443], .contexts []⟩,
    ⟨[88443, 1], [88441], .contexts [
        ⟨50233, false, false, [], []⟩
      ]⟩,
    ⟨[88441], [88441], .contexts []⟩,
    ⟨[88441, 5], [88439], .contexts [
        ⟨50230, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 786. -/
def y322TCIndexRaw786 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88439], [88439], .contexts []⟩,
    ⟨[88439, 3], [88437], .contexts [
        ⟨50226, false, false, [], []⟩
      ]⟩,
    ⟨[88437], [88437], .contexts []⟩,
    ⟨[
      88467, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3
    ], [88437], .contexts [
        ⟨50296, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨50297, false, false, [], [9, 1, 5, 3]⟩,
        ⟨50298, false, false, [], [9, 1, 5, 3]⟩,
        ⟨50239, false, false, [], [9, 1, 5, 3]⟩,
        ⟨50239, false, false, [], [9, 1, 5, 3]⟩,
        ⟨50299, false, false, [], [1, 5, 3]⟩,
        ⟨50300, false, false, [], [1, 5, 3]⟩,
        ⟨50235, false, false, [], [1, 5, 3]⟩,
        ⟨50235, false, false, [], [1, 5, 3]⟩,
        ⟨50301, false, false, [], [5, 3]⟩,
        ⟨50302, false, false, [], [5, 3]⟩,
        ⟨50232, false, false, [], [5, 3]⟩,
        ⟨50232, false, false, [], [5, 3]⟩,
        ⟨50303, false, false, [], [3]⟩,
        ⟨50304, false, false, [], [3]⟩,
        ⟨50229, false, false, [], [3]⟩,
        ⟨50229, false, false, [], [3]⟩,
        ⟨50305, false, false, [], []⟩,
        ⟨50306, false, false, [], []⟩,
        ⟨50225, false, false, [], []⟩,
        ⟨50225, false, false, [], []⟩
      ]⟩,
    ⟨[88437, 1], [88435], .contexts [
        ⟨50222, false, false, [], []⟩
      ]⟩,
    ⟨[88435], [88435], .contexts []⟩,
    ⟨[88429], [88429], .contexts []⟩,
    ⟨[88427], [88427], .contexts []⟩,
    ⟨[
      88467, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [88427], .contexts [
        ⟨50307, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨50308, false, false, [], [15, 13, 1, 11]⟩,
        ⟨50309, false, false, [], [15, 13, 1, 11]⟩,
        ⟨50221, false, false, [], [15, 13, 1, 11]⟩,
        ⟨50221, false, false, [], [15, 13, 1, 11]⟩,
        ⟨50219, false, false, [], [13, 1, 11]⟩,
        ⟨50218, false, false, [], [13, 1, 11]⟩,
        ⟨50218, false, false, [], [13, 1, 11]⟩,
        ⟨50215, false, false, [], [1, 11]⟩,
        ⟨50214, false, false, [], [1, 11]⟩,
        ⟨50214, false, false, [], [1, 11]⟩,
        ⟨50212, false, false, [], [11]⟩,
        ⟨50310, false, false, [], [11]⟩,
        ⟨50211, false, false, [], [11]⟩,
        ⟨50211, false, false, [], [11]⟩,
        ⟨50209, false, false, [], []⟩,
        ⟨50311, false, false, [], []⟩,
        ⟨50208, false, false, [], []⟩,
        ⟨50208, false, false, [], []⟩
      ]⟩,
    ⟨[88425], [88425], .contexts []⟩,
    ⟨[88423], [88423], .contexts []⟩,
    ⟨[88421], [88421], .contexts []⟩,
    ⟨[88419], [88419], .contexts []⟩,
    ⟨[88417], [88417], .contexts []⟩,
    ⟨[
      88467, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1
    ], [88417], .contexts [
        ⟨50312, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨50206, false, false, [], [1, 5, 3, 1]⟩,
        ⟨50313, false, false, [], [1, 5, 3, 1]⟩,
        ⟨50205, false, false, [], [1, 5, 3, 1]⟩,
        ⟨50205, false, false, [], [1, 5, 3, 1]⟩,
        ⟨50203, false, false, [], [5, 3, 1]⟩,
        ⟨50314, false, false, [], [5, 3, 1]⟩,
        ⟨50202, false, false, [], [5, 3, 1]⟩,
        ⟨50202, false, false, [], [5, 3, 1]⟩,
        ⟨50200, false, false, [], [3, 1]⟩,
        ⟨50315, false, false, [], [3, 1]⟩,
        ⟨50199, false, false, [], [3, 1]⟩,
        ⟨50199, false, false, [], [3, 1]⟩,
        ⟨50197, false, false, [], [1]⟩,
        ⟨50316, false, false, [], [1]⟩,
        ⟨50196, false, false, [], [1]⟩,
        ⟨50196, false, false, [], [1]⟩,
        ⟨50194, false, false, [], []⟩,
        ⟨50317, false, false, [], []⟩,
        ⟨50193, false, false, [], []⟩,
        ⟨50193, false, false, [], []⟩
      ]⟩,
    ⟨[88415], [88415], .contexts []⟩,
    ⟨[88413], [88413], .contexts []⟩,
    ⟨[88409], [88409], .contexts []⟩,
    ⟨[88407], [88407], .contexts []⟩,
    ⟨[
      88467, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9
    ], [88407], .contexts [
        ⟨50318, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨50191, false, false, [], [13, 1, 11, 9]⟩,
        ⟨50319, false, false, [], [13, 1, 11, 9]⟩,
        ⟨50190, false, false, [], [13, 1, 11, 9]⟩,
        ⟨50190, false, false, [], [13, 1, 11, 9]⟩,
        ⟨50187, false, false, [], [1, 11, 9]⟩,
        ⟨50320, false, false, [], [1, 11, 9]⟩,
        ⟨50186, false, false, [], [1, 11, 9]⟩,
        ⟨50186, false, false, [], [1, 11, 9]⟩,
        ⟨50183, false, false, [], [11, 9]⟩,
        ⟨50182, false, false, [], [11, 9]⟩,
        ⟨50182, false, false, [], [11, 9]⟩,
        ⟨50180, false, false, [], [9]⟩,
        ⟨50321, false, false, [], [9]⟩,
        ⟨50179, false, false, [], [9]⟩,
        ⟨50179, false, false, [], [9]⟩,
        ⟨50176, false, false, [], []⟩,
        ⟨50322, false, false, [], []⟩,
        ⟨50175, false, false, [], []⟩,
        ⟨50175, false, false, [], []⟩
      ]⟩,
    ⟨[88405], [88405], .contexts []⟩,
    ⟨[88401], [88401], .contexts []⟩,
    ⟨[88399], [88399], .contexts []⟩,
    ⟨[88397], [88397], .contexts []⟩,
    ⟨[
      88467, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [88397], .contexts [
        ⟨50323, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨50172, false, false, [], [5, 3, 1, 15]⟩,
        ⟨50324, false, false, [], [5, 3, 1, 15]⟩,
        ⟨50171, false, false, [], [5, 3, 1, 15]⟩,
        ⟨50171, false, false, [], [5, 3, 1, 15]⟩,
        ⟨50168, false, false, [], [3, 1, 15]⟩,
        ⟨50167, false, false, [], [3, 1, 15]⟩,
        ⟨50167, false, false, [], [3, 1, 15]⟩,
        ⟨50164, false, false, [], [1, 15]⟩,
        ⟨50325, false, false, [], [1, 15]⟩,
        ⟨50163, false, false, [], [1, 15]⟩,
        ⟨50163, false, false, [], [1, 15]⟩,
        ⟨50160, false, false, [], [15]⟩,
        ⟨50326, false, false, [], [15]⟩,
        ⟨50159, false, false, [], [15]⟩,
        ⟨50159, false, false, [], [15]⟩,
        ⟨50156, false, false, [], []⟩,
        ⟨50327, false, false, [], []⟩,
        ⟨50155, false, false, [], []⟩,
        ⟨50155, false, false, [], []⟩
      ]⟩,
    ⟨[88395], [88395], .contexts []⟩,
    ⟨[88393], [88393], .contexts []⟩,
    ⟨[88393, 11], [88391], .contexts [
        ⟨50144, false, false, [], []⟩
      ]⟩,
    ⟨[88389], [88389], .contexts []⟩,
    ⟨[88387], [88387], .contexts []⟩,
    ⟨[
      88467, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1
    ], [88387], .contexts [
        ⟨50328, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨50152, false, false, [], [1, 11, 9, 1]⟩,
        ⟨50329, false, false, [], [1, 11, 9, 1]⟩,
        ⟨50151, false, false, [], [1, 11, 9, 1]⟩,
        ⟨50151, false, false, [], [1, 11, 9, 1]⟩,
        ⟨50148, false, false, [], [11, 9, 1]⟩,
        ⟨50330, false, false, [], [11, 9, 1]⟩,
        ⟨50147, false, false, [], [11, 9, 1]⟩,
        ⟨50147, false, false, [], [11, 9, 1]⟩,
        ⟨50331, false, false, [], [9, 1]⟩,
        ⟨50143, false, false, [], [9, 1]⟩,
        ⟨50143, false, false, [], [9, 1]⟩,
        ⟨50141, false, false, [], [1]⟩,
        ⟨50332, false, false, [], [1]⟩,
        ⟨50140, false, false, [], [1]⟩,
        ⟨50140, false, false, [], [1]⟩,
        ⟨50138, false, false, [], []⟩,
        ⟨50333, false, false, [], []⟩,
        ⟨50137, false, false, [], []⟩,
        ⟨50137, false, false, [], []⟩
      ]⟩,
    ⟨[88385], [88385], .contexts []⟩,
    ⟨[88383], [88383], .contexts []⟩,
    ⟨[88379], [88379], .contexts []⟩,
    ⟨[88377], [88377], .contexts []⟩,
    ⟨[
      88467, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [88377], .contexts [
        ⟨50334, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨50135, false, false, [], [3, 1, 15, 13]⟩,
        ⟨50335, false, false, [], [3, 1, 15, 13]⟩,
        ⟨50134, false, false, [], [3, 1, 15, 13]⟩,
        ⟨50134, false, false, [], [3, 1, 15, 13]⟩,
        ⟨50131, false, false, [], [1, 15, 13]⟩,
        ⟨50336, false, false, [], [1, 15, 13]⟩,
        ⟨50130, false, false, [], [1, 15, 13]⟩,
        ⟨50130, false, false, [], [1, 15, 13]⟩,
        ⟨50127, false, false, [], [15, 13]⟩,
        ⟨50126, false, false, [], [15, 13]⟩,
        ⟨50126, false, false, [], [15, 13]⟩,
        ⟨50124, false, false, [], [13]⟩,
        ⟨50337, false, false, [], [13]⟩,
        ⟨50123, false, false, [], [13]⟩,
        ⟨50123, false, false, [], [13]⟩,
        ⟨50121, false, false, [], []⟩,
        ⟨50338, false, false, [], []⟩,
        ⟨50120, false, false, [], []⟩,
        ⟨50120, false, false, [], []⟩
      ]⟩,
    ⟨[88375], [88375], .contexts []⟩,
    ⟨[88373], [88373], .contexts []⟩,
    ⟨[88371], [88371], .contexts []⟩,
    ⟨[88371, 1], [88369], .contexts [
        ⟨50108, false, false, [], []⟩
      ]⟩,
    ⟨[88369], [88369], .contexts []⟩,
    ⟨[88369, 5], [88367], .contexts [
        ⟨50104, true, false, [], [5]⟩,
        ⟨28, false, false, [88367], []⟩,
        ⟨50105, false, false, [], []⟩
      ]⟩,
    ⟨[88367], [88367], .contexts []⟩,
    ⟨[
      88467, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5
    ], [88367], .contexts [
        ⟨50339, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨50118, false, false, [], [11, 9, 1, 5]⟩,
        ⟨50340, false, false, [], [11, 9, 1, 5]⟩,
        ⟨50117, false, false, [], [11, 9, 1, 5]⟩,
        ⟨50117, false, false, [], [11, 9, 1, 5]⟩,
        ⟨50115, false, false, [], [9, 1, 5]⟩,
        ⟨50341, false, false, [], [9, 1, 5]⟩,
        ⟨50114, false, false, [], [9, 1, 5]⟩,
        ⟨50114, false, false, [], [9, 1, 5]⟩,
        ⟨50112, false, false, [], [1, 5]⟩,
        ⟨50342, false, false, [], [1, 5]⟩,
        ⟨50111, false, false, [], [1, 5]⟩,
        ⟨50111, false, false, [], [1, 5]⟩,
        ⟨50343, false, false, [], [5]⟩,
        ⟨50344, false, false, [], [5]⟩,
        ⟨50107, false, false, [], [5]⟩,
        ⟨50107, false, false, [], [5]⟩,
        ⟨50345, false, false, [], []⟩,
        ⟨50346, false, false, [], []⟩,
        ⟨50105, false, false, [], []⟩,
        ⟨50105, false, false, [], []⟩
      ]⟩,
    ⟨[88367, 3], [88365], .contexts [
        ⟨50102, false, false, [], []⟩
      ]⟩,
    ⟨[88365], [88365], .contexts []⟩,
    ⟨[88365, 1], [88363], .contexts [
        ⟨50098, false, false, [], []⟩
      ]⟩,
    ⟨[88363], [88363], .contexts []⟩,
    ⟨[88361], [88361], .contexts []⟩,
    ⟨[88357], [88357], .contexts []⟩,
    ⟨[
      88467, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1
    ], [88357], .contexts [
        ⟨50347, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨50348, false, false, [], [1, 15, 13, 1]⟩,
        ⟨50349, false, false, [], [1, 15, 13, 1]⟩,
        ⟨50101, false, false, [], [1, 15, 13, 1]⟩,
        ⟨50101, false, false, [], [1, 15, 13, 1]⟩,
        ⟨50350, false, false, [], [15, 13, 1]⟩,
        ⟨50351, false, false, [], [15, 13, 1]⟩,
        ⟨50097, false, false, [], [15, 13, 1]⟩,
        ⟨50097, false, false, [], [15, 13, 1]⟩,
        ⟨50094, false, false, [], [13, 1]⟩,
        ⟨50352, false, false, [], [13, 1]⟩,
        ⟨50093, false, false, [], [13, 1]⟩,
        ⟨50093, false, false, [], [13, 1]⟩,
        ⟨50090, false, false, [], [1]⟩,
        ⟨50089, false, false, [], [1]⟩,
        ⟨50089, false, false, [], [1]⟩,
        ⟨50086, false, false, [], []⟩,
        ⟨50353, false, false, [], []⟩,
        ⟨50085, false, false, [], []⟩,
        ⟨50085, false, false, [], []⟩
      ]⟩,
    ⟨[88355], [88355], .contexts []⟩,
    ⟨[86243, 1], [86245], .contexts [
        ⟨36181, false, false, [], []⟩
      ]⟩,
    ⟨[18973, 88353], [18973, 88353], .contexts []⟩,
    ⟨[18973, 88353], [18973, 88353], .contexts []⟩,
    ⟨[
      88467, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [18973, 88353], .contexts [
        ⟨50354, false, false, [], [11, 9, 1, 5]⟩,
        ⟨50081, true, false, [], [11, 9, 1, 5]⟩,
        ⟨53, false, false, [88355], [9, 1, 5]⟩,
        ⟨50082, false, false, [], [9, 1, 5]⟩,
        ⟨50355, false, false, [], [9, 1, 5]⟩,
        ⟨50082, false, false, [], [9, 1, 5]⟩,
        ⟨50082, false, false, [], [9, 1, 5]⟩,
        ⟨50079, false, false, [], [1, 5]⟩,
        ⟨36399, false, false, [], [1, 5]⟩,
        ⟨36182, false, false, [], [1, 5]⟩,
        ⟨36182, false, false, [], [1, 5]⟩,
        ⟨50356, false, false, [], [5]⟩,
        ⟨36397, false, false, [], [5]⟩,
        ⟨36186, false, false, [], [5]⟩,
        ⟨36186, false, false, [], [5]⟩,
        ⟨50075, false, false, [], []⟩,
        ⟨50357, false, false, [], []⟩,
        ⟨50358, false, false, [], []⟩,
        ⟨50358, false, false, [], []⟩
      ]⟩,
    ⟨[18973, 88349], [18973, 88349], .contexts []⟩,
    ⟨[18973, 88347], [18973, 88347], .contexts []⟩,
    ⟨[
      88467, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1
    ], [18973, 85623], .contexts [
        ⟨50359, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨50061, false, false, [18973], [1, 15, 13, 1]⟩,
        ⟨50057, false, false, [18973], [15, 13, 1]⟩,
        ⟨50360, false, false, [], [15, 13, 1]⟩,
        ⟨50046, false, false, [18973], [13, 1]⟩,
        ⟨50361, false, false, [], [13, 1]⟩,
        ⟨50031, false, false, [18973], [1]⟩,
        ⟨36089, false, false, [], [1]⟩,
        ⟨36090, false, false, [], [1]⟩,
        ⟨36091, false, false, [], [1]⟩,
        ⟨36107, false, false, [], []⟩,
        ⟨36108, false, false, [], []⟩,
        ⟨36109, false, false, [], []⟩,
        ⟨36110, false, false, [], []⟩
      ]⟩,
    ⟨[22701], [18973, 22699], .source 11415⟩,
    ⟨[22703], [22701, 22673], .source 11416⟩,
    ⟨[22705], [22703, 20775], .source 11417⟩,
    ⟨[
      88467, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [22705, 79013], .contexts [
        ⟨50362, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨50028, false, false, [18973], [9, 1, 5, 3]⟩,
        ⟨50363, true, false, [], [88345, 9, 1, 5, 3]⟩,
        ⟨49998, false, false, [22701], [1, 5, 3]⟩,
        ⟨49968, false, false, [22701], [5, 3]⟩,
        ⟨50364, true, false, [], [88343, 5, 3]⟩,
        ⟨49956, false, false, [22703], [3]⟩,
        ⟨42693, false, false, [22703], []⟩,
        ⟨50365, true, false, [], [79013]⟩
      ]⟩,
    ⟨[22707], [22705, 15277], .source 11418⟩]

/-- Exact literal claimed equations and contextual derivations, block 787. -/
def y322TCIndexRaw787 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[22709], [22707, 2575], .source 11419⟩,
    ⟨[
      88467, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11
    ], [22709, 83149], .contexts [
        ⟨50366, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨5553, false, false, [22705], [15, 13, 1, 11]⟩,
        ⟨15336, false, false, [22705], [13, 1, 11]⟩,
        ⟨19107, false, false, [22705], [1, 11]⟩,
        ⟨50367, true, false, [], [83141, 1, 11]⟩,
        ⟨19096, false, false, [22707], [11]⟩,
        ⟨50368, true, false, [], [83141, 11]⟩,
        ⟨19209, false, false, [22709], []⟩
      ]⟩,
    ⟨[22711], [22709, 15289], .source 11420⟩,
    ⟨[22713], [22711, 2575], .source 11421⟩,
    ⟨[22715], [22713, 315], .source 11422⟩,
    ⟨[22717], [22715, 2575], .source 11423⟩,
    ⟨[
      88467, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1
    ], [22717, 82837], .contexts [
        ⟨50369, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨19203, false, false, [22709], [1, 5, 3, 1]⟩,
        ⟨50370, true, false, [], [83149, 1, 5, 3, 1]⟩,
        ⟨19199, false, false, [22711], [5, 3, 1]⟩,
        ⟨50371, true, false, [], [83149, 5, 3, 1]⟩,
        ⟨19191, false, false, [22713], [3, 1]⟩,
        ⟨17285, false, false, [22713], [1]⟩,
        ⟨50372, true, false, [], [82837, 1]⟩,
        ⟨17283, false, false, [22715], []⟩,
        ⟨50373, true, false, [], [82837]⟩
      ]⟩,
    ⟨[22719], [22717, 1075], .source 11424⟩,
    ⟨[
      88467, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9, 1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5,
      3, 1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15,
      13, 1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11,
      9
    ], [22719, 79201], .contexts [
        ⟨50374, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨17302, false, false, [22717], [13, 1, 11, 9]⟩,
        ⟨50375, true, false, [], [82837, 13, 1, 11, 9]⟩,
        ⟨17274, false, false, [22719], [1, 11, 9]⟩,
        ⟨15371, false, false, [22719], [11, 9]⟩,
        ⟨15272, false, false, [22719], [9]⟩,
        ⟨6354, false, false, [22719], []⟩
      ]⟩,
    ⟨[22721], [22719, 7357], .source 11425⟩,
    ⟨[22723], [22721, 19847], .source 11426⟩,
    ⟨[88469, 15], [88469, 15], .contexts []⟩,
    ⟨[88469, 15], [22723, 86923], .contexts [
        ⟨50379, false, false, [], []⟩,
        ⟨50282, true, false, [], [15]⟩,
        ⟨50282, true, false, [], [15]⟩,
        ⟨50281, true, false, [], [15]⟩,
        ⟨50279, true, false, [], [15]⟩,
        ⟨2277, false, false, [88467], []⟩,
        ⟨2278, false, false, [88467], []⟩,
        ⟨50376, false, false, [], [1, 5, 3, 1]⟩,
        ⟨14985, false, false, [22719], [5, 3, 1]⟩,
        ⟨50377, true, false, [], [82655, 5, 3, 1]⟩,
        ⟨16906, false, false, [22721], [3, 1]⟩,
        ⟨40310, false, false, [22721], [1]⟩,
        ⟨40340, false, false, [22721], []⟩,
        ⟨50378, true, false, [], [86923]⟩,
        ⟨39515, false, false, [22723], []⟩
      ]⟩,
    ⟨[88469, 15], [22723, 86923], .contexts [
        ⟨50380, false, false, [], []⟩,
        ⟨13, true, false, [], [22723, 86923]⟩
      ]⟩,
    ⟨[22725], [22722], .source 11427⟩,
    ⟨[22723, 86923], [22723, 86923], .contexts []⟩,
    ⟨[22723, 86923], [22723, 86923], .contexts []⟩,
    ⟨[88469, 15], [22723, 86923], .contexts [
        ⟨50379, false, false, [], []⟩,
        ⟨50381, false, false, [], []⟩,
        ⟨50383, false, false, [], []⟩,
        ⟨50384, false, false, [], []⟩,
        ⟨50384, false, false, [], []⟩
      ]⟩,
    ⟨[22727], [22723, 19849], .source 11428⟩,
    ⟨[22729], [22727, 7355], .source 11429⟩,
    ⟨[88469], [88469], .contexts []⟩,
    ⟨[87575, 1], [87575, 1], .contexts []⟩,
    ⟨[88469], [88469], .contexts []⟩,
    ⟨[22731], [22728], .source 11430⟩,
    ⟨[22728], [22728], .contexts []⟩,
    ⟨[87575, 1], [22731, 88469], .contexts [
        ⟨50389, false, false, [], []⟩,
        ⟨50387, false, false, [22728], [87575, 1]⟩,
        ⟨44740, true, false, [22728, 22727], [1]⟩,
        ⟨50386, false, false, [22728], [87201, 15, 1]⟩,
        ⟨40339, true, false, [22728, 22723], [15, 1]⟩,
        ⟨50385, true, false, [22728], [1, 15, 1]⟩,
        ⟨504, false, false, [22728, 88469], []⟩,
        ⟨50388, false, false, [22728], []⟩,
        ⟨50390, false, false, [22728], []⟩,
        ⟨50392, true, false, [], [88469]⟩,
        ⟨50392, true, false, [], [88469]⟩,
        ⟨50391, true, false, [], [88469]⟩
      ]⟩,
    ⟨[22729], [22730], .contexts [
        ⟨50391, true, true, [], []⟩
      ]⟩,
    ⟨[88469, 1], [22729, 87575], .contexts [
        ⟨50393, true, false, [22730], [1]⟩,
        ⟨8, false, false, [22730, 87575], []⟩,
        ⟨50394, true, false, [], [87575]⟩
      ]⟩,
    ⟨[22733], [22723, 19857], .source 11431⟩,
    ⟨[22735], [22733, 20751], .source 11432⟩,
    ⟨[22737], [22734], .source 11433⟩,
    ⟨[22734], [22734], .contexts []⟩,
    ⟨[85255, 3], [22737, 88469], .contexts [
        ⟨50397, false, false, [22734], [85255, 3]⟩,
        ⟨42670, true, false, [22734, 22733], [3]⟩,
        ⟨35694, true, false, [22734, 22733], [3]⟩,
        ⟨50396, false, false, [22734], [86221, 15, 3]⟩,
        ⟨40364, true, false, [22734, 22723], [15, 3]⟩,
        ⟨39405, true, false, [22734, 22723], [15, 3]⟩,
        ⟨50385, true, false, [22734], [3, 15, 3]⟩,
        ⟨903, false, false, [22734, 88469], []⟩,
        ⟨50388, false, false, [22734], []⟩,
        ⟨50390, false, false, [22734], []⟩,
        ⟨50399, true, false, [], [88469]⟩,
        ⟨50399, true, false, [], [88469]⟩,
        ⟨50398, true, false, [], [88469]⟩
      ]⟩,
    ⟨[22739], [22723, 19567], .source 11434⟩,
    ⟨[22741], [22739, 18309], .source 11435⟩,
    ⟨[22743], [22740], .source 11436⟩,
    ⟨[22740], [22740], .contexts []⟩,
    ⟨[85611, 5], [22743, 88469], .contexts [
        ⟨50402, false, false, [22740], [85611, 5]⟩,
        ⟨32785, true, false, [22740, 22739], [5]⟩,
        ⟨50401, false, false, [22740], [85219, 15, 5]⟩,
        ⟨39507, true, false, [22740, 22723], [15, 5]⟩,
        ⟨50385, true, false, [22740], [5, 15, 5]⟩,
        ⟨2284, false, false, [22740, 88469], []⟩,
        ⟨50388, false, false, [22740], []⟩,
        ⟨50390, false, false, [22740], []⟩,
        ⟨50404, true, false, [], [88469]⟩,
        ⟨50404, true, false, [], [88469]⟩,
        ⟨50403, true, false, [], [88469]⟩
      ]⟩,
    ⟨[88469, 5], [22741, 85611], .contexts [
        ⟨50405, true, false, [22742], [5]⟩,
        ⟨28, false, false, [22742, 85611], []⟩,
        ⟨50403, false, true, [], [85611]⟩
      ]⟩,
    ⟨[22745], [22723, 19853], .source 11437⟩,
    ⟨[22745, 86325], [22745, 86325], .contexts []⟩,
    ⟨[86325, 7], [86325, 7], .contexts []⟩,
    ⟨[22747], [22744], .source 11438⟩,
    ⟨[22744], [22744], .contexts []⟩,
    ⟨[86325, 7], [22747, 88469], .contexts [
        ⟨50409, false, false, [], []⟩,
        ⟨50408, true, false, [22744], [7]⟩,
        ⟨36335, true, false, [], [7]⟩,
        ⟨50407, false, false, [22744], [86327, 15, 7]⟩,
        ⟨40347, true, false, [22744, 22723], [15, 7]⟩,
        ⟨50385, true, false, [22744], [7, 15, 7]⟩,
        ⟨2651, false, false, [22744, 88469], []⟩,
        ⟨50388, false, false, [22744], []⟩,
        ⟨50390, false, false, [22744], []⟩,
        ⟨50411, true, false, [], [88469]⟩,
        ⟨50411, true, false, [], [88469]⟩,
        ⟨50410, true, false, [], [88469]⟩
      ]⟩,
    ⟨[22749], [22723, 19571], .source 11439⟩,
    ⟨[22751], [22749, 19495], .source 11440⟩,
    ⟨[22753], [22750], .source 11441⟩,
    ⟨[22750], [22750], .contexts []⟩,
    ⟨[86793, 9], [22753, 88469], .contexts [
        ⟨50414, false, false, [22750], [86793, 9]⟩,
        ⟨38998, true, false, [22750, 22749], [9]⟩,
        ⟨50413, false, false, [22750], [83901, 15, 9]⟩,
        ⟨39520, true, false, [22750, 22723], [15, 9]⟩,
        ⟨50385, true, false, [22750], [9, 15, 9]⟩,
        ⟨2656, false, false, [22750, 88469], []⟩,
        ⟨50388, false, false, [22750], []⟩,
        ⟨50390, false, false, [22750], []⟩,
        ⟨50416, true, false, [], [88469]⟩,
        ⟨50416, true, false, [], [88469]⟩,
        ⟨50415, true, false, [], [88469]⟩
      ]⟩,
    ⟨[88469, 9], [22751, 86793], .contexts [
        ⟨50417, true, false, [22752], [9]⟩,
        ⟨46, false, false, [22752, 86793], []⟩,
        ⟨50415, false, true, [], [86793]⟩
      ]⟩,
    ⟨[22731, 88469], [22731, 88469], .contexts []⟩,
    ⟨[22731, 88469], [22731, 88469], .contexts []⟩,
    ⟨[87575, 1], [22731, 88469], .contexts [
        ⟨50389, false, false, [], []⟩,
        ⟨50393, false, false, [], []⟩,
        ⟨50419, false, false, [], []⟩,
        ⟨50420, false, false, [], []⟩,
        ⟨50420, false, false, [], []⟩
      ]⟩,
    ⟨[22729], [22730], .contexts [
        ⟨50394, false, false, [], []⟩
      ]⟩,
    ⟨[22755], [22729, 7357], .source 11442⟩,
    ⟨[88469, 11], [22755, 85109], .contexts [
        ⟨50421, true, false, [22730], [11]⟩,
        ⟨110, false, false, [22730, 87575], []⟩,
        ⟨111, false, false, [22730, 87575], []⟩,
        ⟨44729, false, false, [22730], [1]⟩,
        ⟨44732, false, false, [22730], [1]⟩,
        ⟨32758, false, false, [22730], [1]⟩,
        ⟨32759, false, false, [22730], [1]⟩,
        ⟨32759, false, false, [22730], [1]⟩,
        ⟨30235, false, false, [22730, 7357], []⟩,
        ⟨32755, false, false, [22730], []⟩,
        ⟨32756, false, false, [22730], []⟩,
        ⟨32757, false, false, [22730], []⟩,
        ⟨44231, false, false, [22730, 7357], []⟩,
        ⟨50422, true, false, [], [7357, 85109]⟩,
        ⟨50423, true, false, [], [85109]⟩
      ]⟩,
    ⟨[22757], [22754], .source 11443⟩,
    ⟨[22759], [21277, 21539], .source 11444⟩,
    ⟨[22761], [22759, 21549], .source 11445⟩,
    ⟨[22763], [22729, 22761], .source 11446⟩,
    ⟨[22765], [22762], .source 11447⟩,
    ⟨[85317], [22765, 88465], .contexts [
        ⟨42567, true, false, [], []⟩,
        ⟨50428, false, false, [22762], [85319, 13]⟩,
        ⟨50422, false, false, [22762], [22761, 85319, 13]⟩,
        ⟨31224, true, false, [22762, 22730, 22761], [13]⟩,
        ⟨50427, false, false, [22762, 22730], [85319, 13]⟩,
        ⟨45486, true, false, [22762, 22730, 22759], [13]⟩,
        ⟨38198, true, false, [22762, 22730, 22759], [13]⟩,
        ⟨50426, false, false, [22762, 22730], [86593, 1, 13]⟩,
        ⟨45483, true, false, [22762, 22730, 21277], [1, 13]⟩,
        ⟨44736, true, false, [22762, 22730], [1, 13]⟩,
        ⟨44735, true, false, [22762, 22730], [1, 13]⟩,
        ⟨116, true, false, [22762, 22730, 87575], [13]⟩,
        ⟨919, true, false, [22762, 22730, 87575], [13]⟩,
        ⟨50421, false, false, [22762, 22730], [13, 1, 13, 13]⟩,
        ⟨50280, false, false, [22762], [1, 13, 13]⟩,
        ⟨50277, false, false, [22762], [13, 13]⟩,
        ⟨59, false, false, [22762, 88465], []⟩,
        ⟨50429, true, false, [], [88465]⟩
      ]⟩,
    ⟨[22765], [22765], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 788. -/
def y322TCIndexRaw788 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[22765], [22765], .contexts []⟩,
    ⟨[22763], [22764], .contexts [
        ⟨50429, true, true, [], []⟩
      ]⟩,
    ⟨[88465], [22763, 85317], .contexts [
        ⟨50431, false, false, [22764], [88465]⟩,
        ⟨50432, false, false, [22764], [88465]⟩,
        ⟨50430, true, false, [22764], []⟩,
        ⟨50433, true, false, [], [85317]⟩
      ]⟩,
    ⟨[22765], [22762], .contexts [
        ⟨50429, false, false, [], []⟩
      ]⟩,
    ⟨[22762], [22762], .contexts []⟩,
    ⟨[22765], [22762], .contexts [
        ⟨50435, false, false, [], []⟩,
        ⟨50436, false, false, [], []⟩,
        ⟨50436, false, false, [], []⟩
      ]⟩,
    ⟨[85317, 11], [22765, 88463], .contexts [
        ⟨50434, true, false, [22762], [11]⟩,
        ⟨50273, false, false, [22762], []⟩,
        ⟨50283, false, false, [22762], []⟩,
        ⟨50437, true, false, [], [88463]⟩
      ]⟩,
    ⟨[88465], [22763, 85317], .contexts [
        ⟨50434, false, false, [], []⟩
      ]⟩,
    ⟨[88467], [22763, 85315], .contexts [
        ⟨50435, false, false, [22764], [88467]⟩,
        ⟨13, false, false, [22764, 22762], [88467]⟩,
        ⟨50275, true, false, [22764, 22762], []⟩,
        ⟨50439, false, false, [22764, 22762], [1]⟩,
        ⟨31084, false, false, [22764], []⟩,
        ⟨50433, true, false, [], [85315]⟩
      ]⟩,
    ⟨[85317, 13], [85319], .contexts [
        ⟨31086, false, false, [], []⟩,
        ⟨31099, false, false, [], []⟩,
        ⟨31091, false, false, [], []⟩,
        ⟨31091, false, false, [], []⟩
      ]⟩,
    ⟨[18213, 83799], [18213, 83799], .contexts []⟩,
    ⟨[18213, 83799], [18213, 83799], .contexts []⟩,
    ⟨[85317, 11], [22765, 88463], .contexts [
        ⟨50438, false, false, [], []⟩
      ]⟩,
    ⟨[22765, 88463], [22765, 88463], .contexts []⟩,
    ⟨[22765, 88463], [22765, 88463], .contexts []⟩,
    ⟨[85317, 11], [22765, 88463], .contexts [
        ⟨50444, false, false, [], []⟩,
        ⟨50445, false, false, [], []⟩,
        ⟨50446, false, false, [], []⟩,
        ⟨50446, false, false, [], []⟩
      ]⟩,
    ⟨[85317, 10], [85317, 11], .contexts [
        ⟨54, false, false, [85317], []⟩
      ]⟩,
    ⟨[83799, 13], [83799, 13], .contexts []⟩,
    ⟨[88463], [88463], .contexts []⟩,
    ⟨[22767], [18211, 22765], .source 11448⟩,
    ⟨[83799, 13], [22767, 88463], .contexts [
        ⟨50449, false, false, [], []⟩,
        ⟨50443, true, false, [18212], [13]⟩,
        ⟨50443, true, false, [18212], [13]⟩,
        ⟨50442, true, false, [18212], [13]⟩,
        ⟨32264, true, false, [18212], [13]⟩,
        ⟨50441, true, false, [18212], [11, 13]⟩,
        ⟨931, false, false, [18212, 85317], []⟩,
        ⟨50448, false, false, [18212], []⟩,
        ⟨50447, false, false, [18212], []⟩,
        ⟨50450, false, false, [18212, 22765], []⟩,
        ⟨32263, false, true, [], [22765, 88463]⟩,
        ⟨50451, true, false, [], [88463]⟩
      ]⟩,
    ⟨[22769], [22766], .source 11449⟩,
    ⟨[85313, 1], [85313, 1], .contexts []⟩,
    ⟨[85313, 1], [22765, 88463], .contexts [
        ⟨50454, false, false, [], []⟩,
        ⟨31079, true, false, [], [1]⟩,
        ⟨31079, true, false, [], [1]⟩,
        ⟨31106, true, false, [], [1]⟩,
        ⟨31105, true, false, [], [1]⟩,
        ⟨31263, true, false, [], [11, 1]⟩,
        ⟨4506, false, false, [85317], []⟩,
        ⟨50448, false, false, [], []⟩,
        ⟨50447, false, false, [], []⟩,
        ⟨50450, false, false, [22765], []⟩,
        ⟨50432, true, false, [], [88463]⟩,
        ⟨50431, true, false, [], [88463]⟩,
        ⟨13, true, false, [], [22765, 88463]⟩
      ]⟩,
    ⟨[88463, 1], [22763, 85313], .contexts [
        ⟨50455, true, false, [22764], [1]⟩,
        ⟨8, false, false, [22764, 85313], []⟩,
        ⟨50433, true, false, [], [85313]⟩
      ]⟩,
    ⟨[18077, 84339], [18077, 84339], .contexts []⟩,
    ⟨[18077, 84339], [18077, 84339], .contexts []⟩,
    ⟨[85317, 3], [18077, 84339], .contexts [
        ⟨31242, false, false, [], []⟩,
        ⟨31244, false, false, [], []⟩,
        ⟨50457, false, false, [], []⟩,
        ⟨50458, false, false, [], []⟩,
        ⟨50458, false, false, [], []⟩
      ]⟩,
    ⟨[22771], [18077, 21591], .source 11450⟩,
    ⟨[22773], [22770], .source 11451⟩,
    ⟨[22775], [22773, 22765], .source 11452⟩,
    ⟨[86609, 3], [22775, 88463], .contexts [
        ⟨50460, false, false, [22770], [86609, 3]⟩,
        ⟨45561, true, false, [22770, 18077], [3]⟩,
        ⟨50459, true, false, [22770], [11, 3]⟩,
        ⟨545, false, false, [22770, 85317], []⟩,
        ⟨50448, false, false, [22770], []⟩,
        ⟨50447, false, false, [22770], []⟩,
        ⟨50450, false, false, [22770, 22765], []⟩,
        ⟨50461, true, false, [], [22765, 88463]⟩,
        ⟨50462, true, false, [], [88463]⟩
      ]⟩,
    ⟨[22777], [22774], .source 11453⟩,
    ⟨[22779], [18085, 18199], .source 11454⟩,
    ⟨[85479, 5], [85479, 5], .contexts []⟩,
    ⟨[22781], [22778], .source 11455⟩,
    ⟨[22783], [22781, 22765], .source 11456⟩,
    ⟨[85479, 5], [22783, 88463], .contexts [
        ⟨50466, false, false, [], []⟩,
        ⟨50465, false, false, [22778], [85479, 5]⟩,
        ⟨32267, true, false, [22778, 18085], [5]⟩,
        ⟨31261, true, false, [22778], [11, 5]⟩,
        ⟨940, false, false, [22778, 85317], []⟩,
        ⟨50448, false, false, [22778], []⟩,
        ⟨50447, false, false, [22778], []⟩,
        ⟨50450, false, false, [22778, 22765], []⟩,
        ⟨50467, true, false, [], [22765, 88463]⟩,
        ⟨50468, true, false, [], [88463]⟩
      ]⟩,
    ⟨[22785], [22782], .source 11457⟩,
    ⟨[85317, 9], [20523, 83619], .contexts [
        ⟨42570, false, false, [], []⟩,
        ⟨42565, false, false, [], []⟩,
        ⟨42566, false, false, [], []⟩,
        ⟨42566, false, false, [], []⟩
      ]⟩,
    ⟨[22787], [20523, 20717], .source 11458⟩,
    ⟨[22789], [22787, 20943], .source 11459⟩,
    ⟨[22765, 88463, 9], [22765, 88461], .contexts [
        ⟨50269, false, false, [22765], []⟩
      ]⟩,
    ⟨[22765, 88461], [22765, 88461], .contexts []⟩,
    ⟨[22765, 88461], [22765, 88461], .contexts []⟩,
    ⟨[22765, 88461], [22765, 88461], .contexts []⟩,
    ⟨[22791], [22788], .source 11460⟩,
    ⟨[22793], [22791, 22765], .source 11461⟩,
    ⟨[83805, 11], [22793, 88461], .contexts [
        ⟨50473, false, false, [22788], [83805, 11]⟩,
        ⟨43303, true, false, [22788, 22787], [11]⟩,
        ⟨50472, false, false, [22788], [83235, 9, 11]⟩,
        ⟨43163, true, false, [22788, 20523], [9, 11]⟩,
        ⟨50471, true, false, [22788], [11, 9, 11]⟩,
        ⟨536, false, false, [22788, 85317], []⟩,
        ⟨537, false, false, [22788, 85317], []⟩,
        ⟨50447, false, false, [22788], [9]⟩,
        ⟨50474, false, false, [22788], []⟩,
        ⟨50475, false, false, [22788], []⟩,
        ⟨50476, false, false, [22788], []⟩,
        ⟨50477, false, false, [22788], []⟩,
        ⟨50478, true, false, [], [22765, 88461]⟩,
        ⟨50479, true, false, [], [88461]⟩
      ]⟩,
    ⟨[22795], [22792], .source 11462⟩,
    ⟨[88461, 11], [22795, 83805], .contexts [
        ⟨50480, true, false, [22792], [11]⟩,
        ⟨53, false, false, [22792, 83805], []⟩,
        ⟨50481, true, false, [], [83805]⟩
      ]⟩,
    ⟨[21763, 86321], [21763, 86321], .contexts []⟩,
    ⟨[21763, 86321], [21763, 86321], .contexts []⟩,
    ⟨[85317, 7], [21763, 86321], .contexts [
        ⟨46308, false, false, [], []⟩,
        ⟨46310, false, false, [], []⟩,
        ⟨50483, false, false, [], []⟩,
        ⟨50484, false, false, [], []⟩,
        ⟨50484, false, false, [], []⟩
      ]⟩,
    ⟨[86319, 7], [86319, 7], .contexts []⟩,
    ⟨[22797], [21761, 22765], .source 11463⟩,
    ⟨[86319, 7], [22797, 88463], .contexts [
        ⟨50486, false, false, [], []⟩,
        ⟨36323, true, false, [], [7]⟩,
        ⟨50485, true, false, [21762], [11, 7]⟩,
        ⟨555, false, false, [21762, 85317], []⟩,
        ⟨50448, false, false, [21762], []⟩,
        ⟨50447, false, false, [21762], []⟩,
        ⟨50450, false, false, [21762, 22765], []⟩,
        ⟨46311, true, false, [], [22765, 88463]⟩,
        ⟨50487, true, false, [], [88463]⟩
      ]⟩,
    ⟨[22799], [22796], .source 11464⟩,
    ⟨[88463, 7], [22799, 86319], .contexts [
        ⟨50488, true, false, [22796], [7]⟩,
        ⟨38, false, false, [22796, 86319], []⟩,
        ⟨50489, true, false, [], [86319]⟩
      ]⟩,
    ⟨[22767, 88463], [22767, 88463], .contexts []⟩,
    ⟨[22767, 88461], [22767, 88461], .contexts []⟩,
    ⟨[22766], [22766], .contexts []⟩,
    ⟨[88461, 13], [22769, 83801], .contexts [
        ⟨50492, true, false, [22766], [13]⟩,
        ⟨50269, true, false, [], [13]⟩,
        ⟨50491, true, false, [22766], [9, 13]⟩,
        ⟨50491, true, false, [22766], [9, 13]⟩,
        ⟨50452, true, false, [22766], [9, 13]⟩,
        ⟨50449, true, false, [22766], [9, 13]⟩,
        ⟨942, false, false, [22766, 83799], []⟩,
        ⟨47, false, false, [22766, 83799], []⟩,
        ⟨23150, false, false, [22766], []⟩,
        ⟨23158, false, false, [22766], []⟩,
        ⟨50493, true, false, [], [83801]⟩,
        ⟨50493, true, false, [], [83801]⟩,
        ⟨50453, true, false, [], [83801]⟩
      ]⟩,
    ⟨[83801, 13], [22767, 88461], .contexts [
        ⟨50494, true, false, [22768], [13]⟩,
        ⟨59, false, false, [22768, 88461], []⟩,
        ⟨50453, false, true, [], [88461]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 789. -/
def y322TCIndexRaw789 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[22801], [22763, 18085], .source 11465⟩,
    ⟨[88459, 9], [22801, 83091], .contexts [
        ⟨50265, true, false, [], [9]⟩,
        ⟨50477, true, false, [22764], [1, 9]⟩,
        ⟨50476, true, false, [22764], [1, 9]⟩,
        ⟨50475, true, false, [22764], [1, 9]⟩,
        ⟨50474, true, false, [22764], [1, 9]⟩,
        ⟨50446, true, false, [22764], [9, 1, 9]⟩,
        ⟨50446, true, false, [22764], [9, 1, 9]⟩,
        ⟨50445, true, false, [22764], [9, 1, 9]⟩,
        ⟨50455, true, false, [22764], [9, 1, 9]⟩,
        ⟨50454, true, false, [22764], [9, 1, 9]⟩,
        ⟨582, false, false, [22764, 85313], []⟩,
        ⟨453, false, false, [22764, 85313], []⟩,
        ⟨31277, false, false, [22764], [1]⟩,
        ⟨31109, false, false, [22764], []⟩,
        ⟨44378, false, false, [22764], []⟩,
        ⟨31291, false, false, [22764], []⟩,
        ⟨31291, false, false, [22764], []⟩,
        ⟨33866, false, false, [22764, 18085], []⟩,
        ⟨50433, true, false, [], [18085, 83091]⟩,
        ⟨50496, true, false, [], [83091]⟩
      ]⟩,
    ⟨[22803], [22800], .source 11466⟩,
    ⟨[22805], [21159, 22803], .source 11467⟩,
    ⟨[22807], [22804], .source 11468⟩,
    ⟨[88459], [22807, 85599], .contexts [
        ⟨50499, false, false, [22804], [88459]⟩,
        ⟨44337, false, false, [22804], [22803, 88459]⟩,
        ⟨50498, false, false, [22804, 21156], [88459]⟩,
        ⟨46, true, false, [22804, 21156, 22800, 88459], []⟩,
        ⟨50497, false, false, [22804, 21156, 22800], [9]⟩,
        ⟨44449, false, false, [22804, 21156], []⟩,
        ⟨50500, true, false, [], [85599]⟩
      ]⟩,
    ⟨[22805], [22806], .contexts [
        ⟨50500, true, true, [], []⟩
      ]⟩,
    ⟨[22806], [22806], .contexts []⟩,
    ⟨[22805], [22806], .contexts [
        ⟨50502, false, false, [], []⟩,
        ⟨50503, false, false, [], []⟩,
        ⟨50503, false, false, [], []⟩
      ]⟩,
    ⟨[88459], [22807, 85599], .contexts [
        ⟨50501, false, false, [], []⟩
      ]⟩,
    ⟨[22807, 85599], [22807, 85599], .contexts []⟩,
    ⟨[88459], [22807, 85599], .contexts [
        ⟨50505, false, false, [], []⟩,
        ⟨50506, false, false, [], []⟩
      ]⟩,
    ⟨[85601, 3], [22805, 88455], .contexts [
        ⟨50500, false, false, [22806], [85601, 3]⟩,
        ⟨32649, true, false, [22806, 22804], [3]⟩,
        ⟨50507, true, false, [22806, 22804, 22806], [5, 3]⟩,
        ⟨50261, false, false, [22806, 22804, 22806], [3]⟩,
        ⟨50286, false, false, [22806, 22804, 22806], [3]⟩,
        ⟨13, true, false, [22806, 22804, 22806], [88457, 3]⟩,
        ⟨50502, true, false, [22806, 22804], [88457, 3]⟩,
        ⟨50258, false, false, [22806], []⟩,
        ⟨50288, false, false, [22806], []⟩,
        ⟨50504, true, false, [], [88455]⟩
      ]⟩,
    ⟨[22783, 88463], [22783, 88463], .contexts []⟩,
    ⟨[22783, 88463], [22783, 88463], .contexts []⟩,
    ⟨[22809], [22785, 21131], .source 11469⟩,
    ⟨[22797, 88463], [22797, 88463], .contexts []⟩,
    ⟨[22797, 88461], [22797, 88461], .contexts []⟩,
    ⟨[22796], [22796], .contexts []⟩,
    ⟨[88461, 7], [22799, 86317], .contexts [
        ⟨50513, true, false, [22796], [7]⟩,
        ⟨50269, true, false, [], [7]⟩,
        ⟨50512, true, false, [22796], [9, 7]⟩,
        ⟨50512, true, false, [22796], [9, 7]⟩,
        ⟨50488, true, false, [22796], [9, 7]⟩,
        ⟨50486, true, false, [22796], [9, 7]⟩,
        ⟨579, false, false, [22796, 86319], []⟩,
        ⟨36491, false, false, [22796], []⟩,
        ⟨36490, false, false, [22796], []⟩,
        ⟨36493, false, false, [22796], []⟩,
        ⟨50514, true, false, [], [86317]⟩,
        ⟨50514, true, false, [], [86317]⟩,
        ⟨50489, true, false, [], [86317]⟩
      ]⟩,
    ⟨[22805, 88461], [22805, 88461], .contexts []⟩,
    ⟨[22813], [22805, 22799], .source 11471⟩,
    ⟨[22815], [22813, 19033], .source 11472⟩,
    ⟨[22815, 86313, 7], [85599], .contexts [
        ⟨50518, false, false, [], [86313, 7]⟩,
        ⟨46601, true, false, [22813], [7]⟩,
        ⟨36315, true, false, [22813], [7]⟩,
        ⟨50517, false, false, [], [86317, 1, 7]⟩,
        ⟨50515, true, false, [22805], [1, 7]⟩,
        ⟨50516, true, false, [], [7, 1, 7]⟩,
        ⟨50516, true, false, [], [7, 1, 7]⟩,
        ⟨50504, false, false, [], [88461, 7, 1, 7]⟩,
        ⟨50284, true, false, [22806], [7, 1, 7]⟩,
        ⟨50263, true, false, [22806], [7, 1, 7]⟩,
        ⟨50501, false, false, [22806], [1, 7, 1, 7]⟩,
        ⟨4091, false, false, [85599], []⟩
      ]⟩,
    ⟨[86313, 7], [86313, 7], .contexts []⟩,
    ⟨[22817], [22814], .source 11473⟩,
    ⟨[22817], [22814], .contexts [
        ⟨50521, false, false, [], []⟩
      ]⟩,
    ⟨[22814], [22814], .contexts []⟩,
    ⟨[22817], [22814], .contexts [
        ⟨50522, false, false, [], []⟩,
        ⟨50523, false, false, [], []⟩,
        ⟨50523, false, false, [], []⟩
      ]⟩,
    ⟨[86313, 7], [22817, 85599], .contexts [
        ⟨50520, false, false, [], []⟩,
        ⟨50519, false, false, [22814], []⟩,
        ⟨44450, false, false, [22814], []⟩,
        ⟨50524, true, false, [], [85599]⟩
      ]⟩,
    ⟨[22815], [22816], .contexts [
        ⟨50521, true, true, [], []⟩
      ]⟩,
    ⟨[85599, 7], [22815, 86313], .contexts [
        ⟨50525, true, false, [22816], [7]⟩,
        ⟨38, false, false, [22816, 86313], []⟩,
        ⟨50526, true, false, [], [86313]⟩
      ]⟩,
    ⟨[85601, 1], [85603], .contexts [
        ⟨32653, false, false, [], []⟩,
        ⟨32676, false, false, [], []⟩,
        ⟨32657, false, false, [], []⟩,
        ⟨32657, false, false, [], []⟩
      ]⟩,
    ⟨[18969, 85603], [18969, 85603], .contexts []⟩,
    ⟨[85601, 1, 3, 1, 3], [18969, 22805, 88455], .contexts [
        ⟨50528, false, false, [], [3, 1, 3]⟩,
        ⟨36005, true, false, [18970], [3, 1, 3]⟩,
        ⟨573, false, false, [18970, 85605], [1, 3]⟩,
        ⟨32824, false, false, [18970], [1, 3]⟩,
        ⟨32823, false, false, [18970], [1, 3]⟩,
        ⟨32826, false, false, [18970], [1, 3]⟩,
        ⟨36006, true, false, [], [85603, 1, 3]⟩,
        ⟨36006, true, false, [], [85603, 1, 3]⟩,
        ⟨35994, false, true, [], [85603, 1, 3]⟩,
        ⟨50529, false, false, [], [1, 3]⟩,
        ⟨50529, false, false, [], [1, 3]⟩,
        ⟨32655, false, false, [18969], [3]⟩,
        ⟨50508, false, false, [18969], []⟩
      ]⟩,
    ⟨[22819], [18969, 22805], .source 11474⟩,
    ⟨[22819, 88453], [22819, 88453], .contexts []⟩,
    ⟨[88453, 3], [88453, 3], .contexts []⟩,
    ⟨[22821], [22818], .source 11475⟩,
    ⟨[22818], [22818], .contexts []⟩,
    ⟨[88453, 3], [22821, 85601], .contexts [
        ⟨50533, false, false, [], []⟩,
        ⟨50532, true, false, [22818], [3]⟩,
        ⟨50255, true, false, [], [3]⟩,
        ⟨50531, false, false, [22818], [88455, 1, 3]⟩,
        ⟨50530, true, false, [22818], [1, 3]⟩,
        ⟨4083, false, false, [22818, 85601], []⟩,
        ⟨32830, false, false, [22818], []⟩,
        ⟨50535, true, false, [], [85601]⟩,
        ⟨50535, true, false, [], [85601]⟩,
        ⟨50534, true, false, [], [85601]⟩
      ]⟩,
    ⟨[85601, 3], [22805, 88455], .contexts [
        ⟨50508, false, false, [], []⟩
      ]⟩,
    ⟨[22805, 88455], [22805, 88455], .contexts []⟩,
    ⟨[22823], [22807, 22819], .source 11476⟩,
    ⟨[18317, 85601], [18317, 85601], .contexts []⟩,
    ⟨[85601, 7], [18317, 85601], .contexts [
        ⟨32829, false, false, [], []⟩,
        ⟨32829, false, false, [], []⟩,
        ⟨32655, true, false, [], [7]⟩,
        ⟨32828, true, false, [18318], [1, 7]⟩,
        ⟨32828, true, false, [18318], [1, 7]⟩,
        ⟨32827, true, false, [18318], [1, 7]⟩,
        ⟨32825, true, false, [18318], [1, 7]⟩,
        ⟨502, false, false, [18318, 85603], []⟩,
        ⟨9, false, false, [18318, 85603], []⟩,
        ⟨32677, false, false, [18318], []⟩,
        ⟨32678, false, false, [18318], []⟩,
        ⟨32654, false, false, [18318], []⟩,
        ⟨32654, false, false, [18318], []⟩,
        ⟨32830, false, false, [18318], []⟩,
        ⟨32811, true, false, [], [85601]⟩,
        ⟨50540, false, false, [], []⟩,
        ⟨50540, false, false, [], []⟩
      ]⟩,
    ⟨[88455], [22823, 88453], .contexts [
        ⟨50538, true, false, [22804], []⟩,
        ⟨50538, true, false, [22804], []⟩,
        ⟨50537, true, false, [22804], []⟩,
        ⟨50536, true, false, [22804, 22820], [3]⟩,
        ⟨20, false, false, [22804, 22820, 88453], []⟩,
        ⟨50534, false, true, [22804], [88453]⟩,
        ⟨50532, false, false, [22804], []⟩,
        ⟨50500, true, false, [], [22819, 88453]⟩,
        ⟨50539, true, false, [], [88453]⟩
      ]⟩,
    ⟨[22823, 88453], [22823, 88453], .contexts []⟩,
    ⟨[88455], [22823, 88453], .contexts [
        ⟨50542, false, false, [], []⟩,
        ⟨50543, false, false, [], []⟩
      ]⟩,
    ⟨[22825], [22805, 22823], .source 11477⟩,
    ⟨[22827], [18317, 22825], .source 11478⟩,
    ⟨[22805, 88455], [22805, 22823, 88453], .contexts [
        ⟨50544, false, false, [22805], []⟩
      ]⟩,
    ⟨[85601, 3], [22825, 88453], .contexts [
        ⟨50537, false, false, [], []⟩,
        ⟨50547, false, false, [], []⟩,
        ⟨50545, true, false, [], [88453]⟩
      ]⟩,
    ⟨[85601, 2], [85601, 3], .contexts [
        ⟨21, false, false, [85601], []⟩
      ]⟩,
    ⟨[88453, 7], [88453, 7], .contexts []⟩,
    ⟨[88453], [88453], .contexts []⟩,
    ⟨[22829], [22826], .source 11479⟩,
    ⟨[22831], [22829, 22825], .source 11480⟩,
    ⟨[88453, 7], [22831, 88453], .contexts [
        ⟨50550, false, false, [], []⟩,
        ⟨50546, false, false, [22826], [88453, 7]⟩,
        ⟨50545, false, false, [22826, 18317], [88453, 7]⟩,
        ⟨50544, true, false, [22826, 18317, 22805], [7]⟩,
        ⟨50508, true, false, [22826, 18317], [7]⟩,
        ⟨50541, true, false, [22826], [3, 7]⟩,
        ⟨14911, false, false, [22826, 85601], []⟩,
        ⟨50549, false, false, [22826], []⟩,
        ⟨50548, false, false, [22826], []⟩,
        ⟨50551, false, false, [22826, 22825], []⟩,
        ⟨50552, true, false, [], [22825, 88453]⟩,
        ⟨50553, true, false, [], [88453]⟩
      ]⟩,
    ⟨[21159, 83093], [21159, 83093], .contexts []⟩,
    ⟨[22833], [21159, 18087], .source 11481⟩,
    ⟨[22835], [22832], .source 11482⟩,
    ⟨[22837], [22835, 22825], .source 11483⟩,
    ⟨[85305, 9], [22837, 88453], .contexts [
        ⟨50556, false, false, [22832], [85305, 9]⟩,
        ⟨31289, true, false, [22832, 21159], [9]⟩,
        ⟨50555, true, false, [22832], [3, 9]⟩,
        ⟨50555, true, false, [22832], [3, 9]⟩,
        ⟨44337, false, false, [22832], [83093, 3, 9]⟩,
        ⟨46, true, false, [22832, 21156, 83093], [3, 9]⟩,
        ⟨44336, false, false, [22832, 21156], [9, 3, 9]⟩,
        ⟨479, false, false, [22832, 85601], []⟩,
        ⟨50549, false, false, [22832], []⟩,
        ⟨50548, false, false, [22832], []⟩,
        ⟨50551, false, false, [22832, 22825], []⟩,
        ⟨50557, true, false, [], [22825, 88453]⟩,
        ⟨50558, true, false, [], [88453]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 790. -/
def y322TCIndexRaw790 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[22839], [22836], .source 11484⟩,
    ⟨[88453, 9], [22839, 85305], .contexts [
        ⟨50559, true, false, [22836], [9]⟩,
        ⟨46, false, false, [22836, 85305], []⟩,
        ⟨50560, true, false, [], [85305]⟩
      ]⟩,
    ⟨[21217, 85601], [21217, 85601], .contexts []⟩,
    ⟨[22841], [21217, 22825], .source 11485⟩,
    ⟨[85601, 13, 3], [22841, 88453], .contexts [
        ⟨44512, false, false, [], [3]⟩,
        ⟨44512, false, false, [], [3]⟩,
        ⟨44499, false, false, [21212], [85601, 13, 3]⟩,
        ⟨44336, true, false, [21212, 21191], [13, 3]⟩,
        ⟨44508, true, false, [21212], [9, 13, 3]⟩,
        ⟨942, false, false, [21212, 83093], [3]⟩,
        ⟨47, false, false, [21212, 83093], [3]⟩,
        ⟨44399, false, false, [21212], [3]⟩,
        ⟨32830, false, false, [21212, 21157], [3]⟩,
        ⟨44505, true, false, [], [85601, 3]⟩,
        ⟨50562, false, false, [], [3]⟩,
        ⟨50562, false, false, [], [3]⟩,
        ⟨50508, false, false, [21217], []⟩,
        ⟨50544, false, false, [21217, 22805], []⟩,
        ⟨50545, true, false, [21217], [88453]⟩,
        ⟨50563, true, false, [], [88453]⟩
      ]⟩,
    ⟨[88453, 13], [88453, 13], .contexts []⟩,
    ⟨[22843], [22840], .source 11486⟩,
    ⟨[22845], [22843, 22825], .source 11487⟩,
    ⟨[88453, 13], [22845, 88453], .contexts [
        ⟨50565, false, false, [], []⟩,
        ⟨50564, true, false, [22840], [13]⟩,
        ⟨1132, false, false, [22840, 85601], []⟩,
        ⟨50549, false, false, [22840], []⟩,
        ⟨50548, false, false, [22840], []⟩,
        ⟨50551, false, false, [22840, 22825], []⟩,
        ⟨50566, true, false, [], [22825, 88453]⟩,
        ⟨50567, true, false, [], [88453]⟩
      ]⟩,
    ⟨[22817, 85599], [22817, 85599], .contexts []⟩,
    ⟨[86313, 7], [22817, 85599], .contexts [
        ⟨50520, false, false, [], []⟩,
        ⟨50525, false, false, [], []⟩,
        ⟨50569, false, false, [], []⟩,
        ⟨50569, false, false, [], []⟩
      ]⟩,
    ⟨[85597, 7], [85597, 7], .contexts []⟩,
    ⟨[86311], [86311], .contexts []⟩,
    ⟨[22816], [22816], .contexts []⟩,
    ⟨[22815], [22816], .contexts [
        ⟨50526, false, false, [], []⟩,
        ⟨50573, false, false, [], []⟩,
        ⟨50573, false, false, [], []⟩
      ]⟩,
    ⟨[85597, 7], [22815, 86311], .contexts [
        ⟨50571, false, false, [], []⟩,
        ⟨32647, true, false, [], [7]⟩,
        ⟨50570, true, false, [22816], [3, 7]⟩,
        ⟨14911, false, false, [22816, 86313], []⟩,
        ⟨21, false, false, [22816, 86313], []⟩,
        ⟨36355, false, false, [22816], []⟩,
        ⟨36356, false, false, [22816], []⟩,
        ⟨36307, false, false, [22816], []⟩,
        ⟨36307, false, false, [22816], []⟩,
        ⟨50572, false, false, [22816], []⟩,
        ⟨50574, true, false, [], [86311]⟩
      ]⟩,
    ⟨[86311, 7], [22817, 85597], .contexts [
        ⟨50575, true, false, [22814], [7]⟩,
        ⟨38, false, false, [22814, 85597], []⟩,
        ⟨50521, true, false, [], [85597]⟩
      ]⟩,
    ⟨[22847], [22817, 21197], .source 11488⟩,
    ⟨[22849], [22847, 22815], .source 11489⟩,
    ⟨[86313, 7, 13, 7], [22849, 86313], .contexts [
        ⟨50570, false, false, [], [13, 7]⟩,
        ⟨44448, false, false, [22817, 21192], [85599, 13, 7]⟩,
        ⟨44406, true, false, [22817, 21192, 21173], [13, 7]⟩,
        ⟨44439, true, false, [22817, 21192], [9, 13, 7]⟩,
        ⟨942, false, false, [22817, 21192, 83091], [7]⟩,
        ⟨47, false, false, [22817, 21192, 83091], [7]⟩,
        ⟨44449, false, false, [22817, 21192], [7]⟩,
        ⟨44450, false, false, [22817, 21192, 21157], [7]⟩,
        ⟨44451, true, false, [22817], [21157, 85599, 7]⟩,
        ⟨44452, true, false, [22817], [85599, 7]⟩,
        ⟨50577, true, false, [], [85599, 7]⟩,
        ⟨50527, false, false, [22847], []⟩,
        ⟨50578, true, false, [], [86313]⟩
      ]⟩,
    ⟨[22851], [22848], .source 11490⟩,
    ⟨[22848], [22848], .contexts []⟩,
    ⟨[88453, 15], [88451], .contexts [
        ⟨50290, false, false, [], []⟩,
        ⟨50291, false, false, [], []⟩,
        ⟨50250, false, false, [], []⟩,
        ⟨50250, false, false, [], []⟩
      ]⟩,
    ⟨[88453, 1], [22823, 88453], .contexts [
        ⟨50253, false, false, [], []⟩,
        ⟨50544, false, false, [], []⟩,
        ⟨50543, false, false, [], []⟩,
        ⟨50543, false, false, [], []⟩
      ]⟩,
    ⟨[22823, 88451], [22823, 88451], .contexts []⟩,
    ⟨[22823, 88451], [22823, 88451], .contexts []⟩,
    ⟨[88451, 1], [88451, 1], .contexts []⟩,
    ⟨[88451], [88451], .contexts []⟩,
    ⟨[22823], [22823], .contexts [
        ⟨13, false, false, [], [22823]⟩
      ]⟩,
    ⟨[88451, 1], [22823, 88451], .contexts [
        ⟨50586, false, false, [], []⟩,
        ⟨50582, true, false, [], [1]⟩,
        ⟨7, false, false, [88453], []⟩,
        ⟨11, false, false, [88453], []⟩,
        ⟨50583, false, false, [], [15]⟩,
        ⟨50251, false, false, [22823], []⟩,
        ⟨50584, false, false, [], []⟩,
        ⟨50585, false, false, [], []⟩,
        ⟨50587, false, false, [22823], []⟩,
        ⟨50588, true, false, [], [88451]⟩
      ]⟩,
    ⟨[22831, 88453], [22831, 88453], .contexts []⟩,
    ⟨[22831, 88453], [22831, 88453], .contexts []⟩,
    ⟨[88453, 7], [22831, 88453], .contexts [
        ⟨50550, false, false, [], []⟩,
        ⟨50554, false, false, [], []⟩,
        ⟨50590, false, false, [], []⟩,
        ⟨50591, false, false, [], []⟩,
        ⟨50591, false, false, [], []⟩
      ]⟩,
    ⟨[22831, 88451], [22831, 88451], .contexts []⟩,
    ⟨[22831, 88451], [22831, 88451], .contexts []⟩,
    ⟨[88451, 7], [88451, 7], .contexts []⟩,
    ⟨[22831], [22831], .contexts [
        ⟨13, false, false, [], [22831]⟩
      ]⟩,
    ⟨[88451, 7], [22831, 88451], .contexts [
        ⟨50595, false, false, [], []⟩,
        ⟨50582, true, false, [], [7]⟩,
        ⟨37, false, false, [88453], []⟩,
        ⟨40, false, false, [88453], []⟩,
        ⟨50592, false, false, [], [15]⟩,
        ⟨50251, false, false, [22831], []⟩,
        ⟨50593, false, false, [], []⟩,
        ⟨50594, false, false, [], []⟩,
        ⟨50587, false, false, [22831], []⟩,
        ⟨50596, true, false, [], [88451]⟩
      ]⟩,
    ⟨[22845, 88453], [22845, 88453], .contexts []⟩,
    ⟨[22845, 88453], [22845, 88453], .contexts []⟩,
    ⟨[88453, 13], [22845, 88453], .contexts [
        ⟨50565, false, false, [], []⟩,
        ⟨50568, false, false, [], []⟩,
        ⟨50598, false, false, [], []⟩,
        ⟨50599, false, false, [], []⟩,
        ⟨50599, false, false, [], []⟩
      ]⟩,
    ⟨[22845, 88449], [22845, 88449], .contexts []⟩,
    ⟨[22845, 88449], [22845, 88449], .contexts []⟩,
    ⟨[88449, 15], [88449, 15], .contexts []⟩,
    ⟨[88449], [88449], .contexts []⟩,
    ⟨[22845], [22845], .contexts []⟩,
    ⟨[22845], [22845], .contexts []⟩,
    ⟨[22845], [22845], .contexts [
        ⟨13, false, false, [], [22845]⟩,
        ⟨50605, false, false, [], []⟩,
        ⟨50606, false, false, [], []⟩
      ]⟩,
    ⟨[22815, 86311], [22815, 86311], .contexts []⟩,
    ⟨[85597, 7], [22815, 86311], .contexts [
        ⟨50571, false, false, [], []⟩,
        ⟨50575, false, false, [], []⟩,
        ⟨50608, false, false, [], []⟩,
        ⟨50608, false, false, [], []⟩
      ]⟩,
    ⟨[22815, 86309], [22815, 86309], .contexts []⟩,
    ⟨[86309, 7], [86309, 7], .contexts []⟩,
    ⟨[85595], [85595], .contexts []⟩,
    ⟨[86309, 7], [22817, 85595], .contexts [
        ⟨50611, false, false, [], []⟩,
        ⟨50610, true, false, [22814], [7]⟩,
        ⟨36304, true, false, [], [7]⟩,
        ⟨50609, true, false, [22814], [1, 7]⟩,
        ⟨502, false, false, [22814, 85597], []⟩,
        ⟨9, false, false, [22814, 85597], []⟩,
        ⟨32682, false, false, [22814], []⟩,
        ⟨32683, false, false, [22814], []⟩,
        ⟨32643, false, false, [22814], []⟩,
        ⟨32643, false, false, [22814], []⟩,
        ⟨50612, false, false, [22814], []⟩,
        ⟨50524, true, false, [], [85595]⟩
      ]⟩,
    ⟨[21217, 85597], [21217, 85597], .contexts []⟩,
    ⟨[22853], [21217, 22815], .source 11491⟩,
    ⟨[85597, 13, 7], [22853, 86311], .contexts [
        ⟨44502, false, false, [], [7]⟩,
        ⟨44502, false, false, [], [7]⟩,
        ⟨44499, false, false, [21212], [85597, 13, 7]⟩,
        ⟨44471, true, false, [21212, 21191], [13, 7]⟩,
        ⟨44490, true, false, [21212], [9, 13, 7]⟩,
        ⟨942, false, false, [21212, 83089], [7]⟩,
        ⟨47, false, false, [21212, 83089], [7]⟩,
        ⟨44500, false, false, [21212], [7]⟩,
        ⟨44501, false, false, [21212], [7]⟩,
        ⟨44501, false, false, [21212], [7]⟩,
        ⟨44469, false, false, [21212, 21157], [7]⟩,
        ⟨44505, true, false, [], [85597, 7]⟩,
        ⟨50614, false, false, [], [7]⟩,
        ⟨50614, false, false, [], [7]⟩,
        ⟨50575, false, false, [21217], []⟩,
        ⟨50615, true, false, [], [86311]⟩
      ]⟩,
    ⟨[22855], [22817, 22853], .source 11492⟩,
    ⟨[86311, 13], [22855, 86311], .contexts [
        ⟨50609, true, false, [22814], [13]⟩,
        ⟨1056, false, false, [22814, 85597], []⟩,
        ⟨1057, false, false, [22814, 85597], []⟩,
        ⟨50616, false, false, [22814], []⟩,
        ⟨50572, false, false, [22814, 22853], []⟩,
        ⟨50522, true, false, [], [22853, 86311]⟩,
        ⟨50617, true, false, [], [86311]⟩
      ]⟩,
    ⟨[88451, 13], [88449], .contexts [
        ⟨50292, false, false, [], []⟩,
        ⟨50293, false, false, [], []⟩,
        ⟨50246, false, false, [], []⟩,
        ⟨50246, false, false, [], []⟩
      ]⟩,
    ⟨[88447, 13], [88447, 13], .contexts []⟩,
    ⟨[88447], [88447], .contexts []⟩,
    ⟨[22857], [22822], .source 11493⟩,
    ⟨[22822], [22822], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 791. -/
def y322TCIndexRaw791 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88447, 13], [22857, 88447], .contexts [
        ⟨50620, false, false, [], []⟩,
        ⟨50243, true, false, [], [13]⟩,
        ⟨50247, true, false, [], [1, 13]⟩,
        ⟨50585, true, false, [22822], [13, 1, 13]⟩,
        ⟨50585, true, false, [22822], [13, 1, 13]⟩,
        ⟨50584, true, false, [22822], [13, 1, 13]⟩,
        ⟨50589, true, false, [22822], [13, 1, 13]⟩,
        ⟨50586, true, false, [22822], [13, 1, 13]⟩,
        ⟨919, false, false, [22822, 88451], []⟩,
        ⟨116, false, false, [22822, 88451], []⟩,
        ⟨50619, false, false, [22822], [1]⟩,
        ⟨50294, false, false, [22822], []⟩,
        ⟨50295, false, false, [22822], []⟩,
        ⟨50242, false, false, [22822], []⟩,
        ⟨50242, false, false, [22822], []⟩,
        ⟨50621, false, false, [22822], []⟩,
        ⟨50623, true, false, [], [88447]⟩,
        ⟨50623, true, false, [], [88447]⟩,
        ⟨50622, true, false, [], [88447]⟩
      ]⟩,
    ⟨[88449, 7], [88449, 7], .contexts []⟩,
    ⟨[22859], [22830], .source 11494⟩,
    ⟨[22830], [22830], .contexts []⟩,
    ⟨[22859], [22830], .contexts [
        ⟨50626, false, false, [], []⟩,
        ⟨50627, false, false, [], []⟩,
        ⟨50627, false, false, [], []⟩
      ]⟩,
    ⟨[88449, 15, 1], [22845, 88447], .contexts [
        ⟨50603, false, false, [], [1]⟩,
        ⟨50603, false, false, [], [1]⟩,
        ⟨50246, true, false, [], [15, 1]⟩,
        ⟨50246, true, false, [], [15, 1]⟩,
        ⟨50293, true, false, [], [15, 1]⟩,
        ⟨50292, true, false, [], [15, 1]⟩,
        ⟨50582, true, false, [], [13, 15, 1]⟩,
        ⟨3049, false, false, [88453], [1]⟩,
        ⟨261, false, false, [88453], [1]⟩,
        ⟨50600, false, false, [], [15, 13, 1]⟩,
        ⟨50251, false, false, [22845], [13, 1]⟩,
        ⟨50247, false, false, [22845], [1]⟩,
        ⟨50601, false, false, [], [1]⟩,
        ⟨50602, false, false, [], [1]⟩,
        ⟨50604, false, false, [22845], [1]⟩,
        ⟨50607, true, false, [], [88449, 1]⟩,
        ⟨50601, false, false, [], [1]⟩,
        ⟨50602, false, false, [], [1]⟩,
        ⟨50602, false, false, [], [1]⟩,
        ⟨50243, false, false, [22845], []⟩
      ]⟩,
    ⟨[88449, 1], [88447], .contexts [
        ⟨50294, false, false, [], []⟩,
        ⟨50295, false, false, [], []⟩,
        ⟨50242, false, false, [], []⟩,
        ⟨50242, false, false, [], []⟩
      ]⟩,
    ⟨[88449, 0], [88449, 1], .contexts [
        ⟨9, false, false, [88449], []⟩
      ]⟩,
    ⟨[88447, 15], [88447, 15], .contexts []⟩,
    ⟨[22861], [22844], .source 11495⟩,
    ⟨[22844], [22844], .contexts []⟩,
    ⟨[22861], [22844], .contexts [
        ⟨50633, false, false, [], []⟩,
        ⟨50634, false, false, [], []⟩,
        ⟨50634, false, false, [], []⟩
      ]⟩,
    ⟨[22817, 85595], [22817, 85595], .contexts []⟩,
    ⟨[86309, 7], [22817, 85595], .contexts [
        ⟨50611, false, false, [], []⟩,
        ⟨50613, false, false, [], []⟩,
        ⟨50636, false, false, [], []⟩,
        ⟨50636, false, false, [], []⟩
      ]⟩,
    ⟨[22863], [22817, 21245], .source 11496⟩,
    ⟨[22865], [22863, 21791], .source 11497⟩,
    ⟨[7, 9, 7, 9], [], .contexts [
        ⟨578, false, false, [], []⟩
      ]⟩,
    ⟨[84465, 9], [84465, 9], .contexts []⟩,
    ⟨[22867], [22864], .source 11498⟩,
    ⟨[22864], [22864], .contexts []⟩,
    ⟨[22867], [22864], .contexts [
        ⟨50642, false, false, [], []⟩,
        ⟨50643, false, false, [], []⟩,
        ⟨50643, false, false, [], []⟩
      ]⟩,
    ⟨[84465, 9], [22867, 86309], .contexts [
        ⟨50641, false, false, [], []⟩,
        ⟨50639, false, false, [22864], [84465, 9]⟩,
        ⟨46432, true, false, [22864, 22863], [9]⟩,
        ⟨50638, false, false, [22864], [84327, 7, 9]⟩,
        ⟨44593, true, false, [22864, 22817], [7, 9]⟩,
        ⟨50637, true, false, [22864], [9, 7, 9]⟩,
        ⟨50640, false, false, [22864, 86309], []⟩,
        ⟨50644, true, false, [], [86309]⟩
      ]⟩,
    ⟨[22865], [22866], .contexts [
        ⟨50642, true, true, [], []⟩
      ]⟩,
    ⟨[22817, 85593], [22817, 85593], .contexts []⟩,
    ⟨[85593, 7], [85593, 7], .contexts []⟩,
    ⟨[85593, 7], [22815, 86307], .contexts [
        ⟨50648, false, false, [], []⟩,
        ⟨50647, true, false, [22816], [7]⟩,
        ⟨32640, true, false, [], [7]⟩,
        ⟨50637, true, false, [22816], [15, 7]⟩,
        ⟨18155, false, false, [22816, 86309], []⟩,
        ⟨10, false, false, [22816, 86309], []⟩,
        ⟨36359, false, false, [22816], []⟩,
        ⟨36360, false, false, [22816], []⟩,
        ⟨36299, false, false, [22816], []⟩,
        ⟨36299, false, false, [22816], []⟩,
        ⟨50574, true, false, [], [86307]⟩
      ]⟩,
    ⟨[22857, 88447], [22857, 88447], .contexts []⟩,
    ⟨[88447, 11], [88445], .contexts [
        ⟨50297, false, false, [], []⟩,
        ⟨50298, false, false, [], []⟩,
        ⟨50239, false, false, [], []⟩,
        ⟨50239, false, false, [], []⟩
      ]⟩,
    ⟨[88447, 10], [88447, 11], .contexts [
        ⟨54, false, false, [88447], []⟩
      ]⟩,
    ⟨[88445], [88445], .contexts []⟩,
    ⟨[22856], [22856], .contexts []⟩,
    ⟨[88445, 13], [22823, 88445], .contexts [
        ⟨50240, true, false, [], [13]⟩,
        ⟨50650, true, false, [22856], [11, 13]⟩,
        ⟨50650, true, false, [22856], [11, 13]⟩,
        ⟨50624, true, false, [22856], [11, 13]⟩,
        ⟨50620, true, false, [22856], [11, 13]⟩,
        ⟨931, false, false, [22856, 88447], []⟩,
        ⟨50652, false, false, [22856], []⟩,
        ⟨50651, false, false, [22856], []⟩,
        ⟨50653, false, false, [22856], []⟩,
        ⟨50654, true, false, [], [88445]⟩,
        ⟨50654, true, false, [], [88445]⟩,
        ⟨50622, false, true, [], [88445]⟩
      ]⟩,
    ⟨[22859, 88449], [22859, 88449], .contexts []⟩,
    ⟨[88449, 7], [22859, 88449], .contexts [
        ⟨50625, false, false, [], []⟩,
        ⟨50625, false, false, [], []⟩,
        ⟨50247, true, false, [], [7]⟩,
        ⟨50594, true, false, [22830], [13, 7]⟩,
        ⟨50594, true, false, [22830], [13, 7]⟩,
        ⟨50593, true, false, [22830], [13, 7]⟩,
        ⟨50597, true, false, [22830], [13, 7]⟩,
        ⟨50595, true, false, [22830], [13, 7]⟩,
        ⟨518, false, false, [22830, 88451], []⟩,
        ⟨64, false, false, [22830, 88451], []⟩,
        ⟨50619, false, false, [22830], []⟩,
        ⟨50604, false, false, [22830], []⟩,
        ⟨50628, true, false, [], [88449]⟩,
        ⟨50656, false, false, [], []⟩,
        ⟨50656, false, false, [], []⟩
      ]⟩,
    ⟨[88447, 7], [88447, 7], .contexts []⟩,
    ⟨[22858], [22858], .contexts []⟩,
    ⟨[22861, 88447], [22861, 88447], .contexts []⟩,
    ⟨[22861, 88445, 15], [88447, 10], .contexts [
        ⟨50240, true, false, [22861], [15]⟩,
        ⟨50660, true, false, [], [11, 15]⟩,
        ⟨50660, true, false, [], [11, 15]⟩,
        ⟨50635, false, false, [], [88447, 11, 15]⟩,
        ⟨50621, true, false, [22844], [11, 15]⟩,
        ⟨50630, true, false, [22844], [11, 15]⟩,
        ⟨50631, true, false, [22844], [11, 15]⟩,
        ⟨1666, true, false, [22844, 88449], [11, 15]⟩,
        ⟨50629, false, false, [22844], [15, 11, 15]⟩,
        ⟨50632, true, false, [], [11, 15]⟩,
        ⟨50632, true, false, [], [11, 15]⟩,
        ⟨2046, false, false, [88447], []⟩
      ]⟩,
    ⟨[88445, 15], [88445, 15], .contexts []⟩,
    ⟨[22845], [22860], .contexts [
        ⟨50633, true, true, [], []⟩
      ]⟩,
    ⟨[22845], [22845], .contexts []⟩,
    ⟨[22860], [22860], .contexts []⟩,
    ⟨[22845], [22860], .contexts [
        ⟨50664, false, false, [], []⟩,
        ⟨50663, false, false, [], []⟩,
        ⟨50665, false, false, [], []⟩,
        ⟨50665, false, false, [], []⟩
      ]⟩,
    ⟨[88445, 15], [22845, 88445], .contexts [
        ⟨50662, false, false, [], []⟩,
        ⟨50661, false, false, [22860], []⟩,
        ⟨50652, false, false, [22860], []⟩,
        ⟨50651, false, false, [22860], []⟩,
        ⟨50653, false, false, [22860], []⟩,
        ⟨50666, true, false, [], [88445]⟩
      ]⟩,
    ⟨[84465, 9], [22867, 86309], .contexts [
        ⟨50645, false, false, [], []⟩
      ]⟩,
    ⟨[22867, 86309], [22867, 86309], .contexts []⟩,
    ⟨[22867, 86309], [22867, 86309], .contexts []⟩,
    ⟨[84465, 15], [84463], .contexts [
        ⟨26938, false, false, [], []⟩,
        ⟨26939, false, false, [], []⟩,
        ⟨26878, false, false, [], []⟩,
        ⟨26878, false, false, [], []⟩
      ]⟩,
    ⟨[86307, 9], [86307, 9], .contexts []⟩,
    ⟨[22866], [22866], .contexts []⟩,
    ⟨[86307, 9], [22865, 84463], .contexts [
        ⟨50672, false, false, [], []⟩,
        ⟨36300, true, false, [], [9]⟩,
        ⟨50670, true, false, [22866], [15, 9]⟩,
        ⟨50670, true, false, [22866], [15, 9]⟩,
        ⟨50669, true, false, [22866], [15, 9]⟩,
        ⟨50668, true, false, [22866], [15, 9]⟩,
        ⟨50641, true, false, [22866], [15, 9]⟩,
        ⟨935, false, false, [22866, 84465], []⟩,
        ⟨10, false, false, [22866, 84465], []⟩,
        ⟨50671, false, false, [22866], []⟩,
        ⟨50673, true, false, [], [84463]⟩,
        ⟨50673, true, false, [], [84463]⟩,
        ⟨50646, true, false, [], [84463]⟩
      ]⟩,
    ⟨[22815, 86307], [22815, 86307], .contexts []⟩,
    ⟨[22815, 86305], [22815, 86305], .contexts []⟩,
    ⟨[86305, 7], [86305, 7], .contexts []⟩,
    ⟨[86305, 7], [22817, 85591], .contexts [
        ⟨50677, false, false, [], []⟩,
        ⟨50676, true, false, [22814], [7]⟩,
        ⟨36296, true, false, [], [7]⟩,
        ⟨50675, true, false, [22814], [13, 7]⟩,
        ⟨50675, true, false, [22814], [13, 7]⟩,
        ⟨50649, true, false, [22814], [13, 7]⟩,
        ⟨50648, true, false, [22814], [13, 7]⟩,
        ⟨518, false, false, [22814, 85593], []⟩,
        ⟨64, false, false, [22814, 85593], []⟩,
        ⟨32686, false, false, [22814], []⟩,
        ⟨32687, false, false, [22814], []⟩,
        ⟨32636, false, false, [22814], []⟩,
        ⟨32636, false, false, [22814], []⟩,
        ⟨50524, true, false, [], [85591]⟩
      ]⟩,
    ⟨[22831, 88447], [22831, 88447], .contexts []⟩,
    ⟨[88447, 7, 11], [22831, 88445], .contexts [
        ⟨50658, false, false, [], [11]⟩,
        ⟨50658, false, false, [], [11]⟩,
        ⟨50243, true, false, [], [7, 11]⟩,
        ⟨50657, true, false, [22858], [1, 7, 11]⟩,
        ⟨502, false, false, [22858, 88449], [11]⟩,
        ⟨50631, false, false, [22858], [11]⟩,
        ⟨50630, false, false, [22858], [11]⟩,
        ⟨50621, false, false, [22858], [11]⟩,
        ⟨50659, true, false, [], [88447, 11]⟩,
        ⟨50659, true, false, [], [88447, 11]⟩,
        ⟨50626, false, true, [], [88447, 11]⟩,
        ⟨50679, false, false, [], [11]⟩,
        ⟨50679, false, false, [], [11]⟩,
        ⟨50240, false, false, [22831], []⟩
      ]⟩,
    ⟨[22845, 88445], [22845, 88445], .contexts []⟩,
    ⟨[22845, 88445], [22845, 88445], .contexts []⟩,
    ⟨[88443, 15], [88443, 15], .contexts []⟩,
    ⟨[22865, 84463], [22865, 84463], .contexts []⟩,
    ⟨[22865, 84463], [22865, 84463], .contexts []⟩,
    ⟨[22817, 85591], [22817, 85591], .contexts []⟩,
    ⟨[85589, 7], [85589, 7], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 792. -/
def y322TCIndexRaw792 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[22861, 88443], [22861, 88443], .contexts []⟩,
    ⟨[88443, 15], [22861, 88443], .contexts [
        ⟨50683, false, false, [], []⟩,
        ⟨50683, false, false, [], []⟩,
        ⟨50236, true, false, [], [15]⟩,
        ⟨50682, true, false, [22844], [9, 15]⟩,
        ⟨50682, true, false, [22844], [9, 15]⟩,
        ⟨50681, true, false, [22844], [9, 15]⟩,
        ⟨50667, true, false, [22844], [9, 15]⟩,
        ⟨50662, true, false, [22844], [9, 15]⟩,
        ⟨1671, false, false, [22844, 88445], []⟩,
        ⟨47, false, false, [22844, 88445], []⟩,
        ⟨50299, false, false, [22844], []⟩,
        ⟨50300, false, false, [22844], []⟩,
        ⟨50235, false, false, [22844], []⟩,
        ⟨50235, false, false, [22844], []⟩,
        ⟨50635, true, false, [], [88443]⟩,
        ⟨50688, false, false, [], []⟩,
        ⟨50688, false, false, [], []⟩
      ]⟩,
    ⟨[88441, 15], [88441, 15], .contexts []⟩,
    ⟨[22815, 86303], [22815, 86303], .contexts []⟩,
    ⟨[85589, 7], [22815, 86303], .contexts [
        ⟨50687, false, false, [], []⟩,
        ⟨50687, false, false, [], []⟩,
        ⟨32634, true, false, [], [7]⟩,
        ⟨50686, true, false, [22816], [1, 7]⟩,
        ⟨50686, true, false, [22816], [1, 7]⟩,
        ⟨50678, true, false, [22816], [1, 7]⟩,
        ⟨50677, true, false, [22816], [1, 7]⟩,
        ⟨502, false, false, [22816, 86305], []⟩,
        ⟨9, false, false, [22816, 86305], []⟩,
        ⟨36364, false, false, [22816], []⟩,
        ⟨36365, false, false, [22816], []⟩,
        ⟨36292, false, false, [22816], []⟩,
        ⟨36292, false, false, [22816], []⟩,
        ⟨50574, true, false, [], [86303]⟩,
        ⟨50691, false, false, [], []⟩,
        ⟨50691, false, false, [], []⟩
      ]⟩,
    ⟨[85589, 11], [85587], .contexts [
        ⟨32690, false, false, [], []⟩,
        ⟨32691, false, false, [], []⟩,
        ⟨32630, false, false, [], []⟩,
        ⟨32630, false, false, [], []⟩
      ]⟩,
    ⟨[85589, 10], [85589, 11], .contexts [
        ⟨54, false, false, [85589], []⟩
      ]⟩,
    ⟨[86301, 7], [86301, 7], .contexts []⟩,
    ⟨[85587], [85587], .contexts []⟩,
    ⟨[22845, 88441], [22845, 88441], .contexts []⟩,
    ⟨[88441, 15, 5], [22845, 88439], .contexts [
        ⟨50690, false, false, [], [5]⟩,
        ⟨50690, false, false, [], [5]⟩,
        ⟨50233, true, false, [], [15, 5]⟩,
        ⟨50689, true, false, [22860], [1, 15, 5]⟩,
        ⟨1666, false, false, [22860, 88443], [5]⟩,
        ⟨9, false, false, [22860, 88443], [5]⟩,
        ⟨50301, false, false, [22860], [5]⟩,
        ⟨50302, false, false, [22860], [5]⟩,
        ⟨50232, false, false, [22860], [5]⟩,
        ⟨50232, false, false, [22860], [5]⟩,
        ⟨50666, true, false, [], [88441, 5]⟩,
        ⟨50697, false, false, [], [5]⟩,
        ⟨50697, false, false, [], [5]⟩,
        ⟨50230, false, false, [22845], []⟩
      ]⟩,
    ⟨[88439, 15], [88439, 15], .contexts []⟩,
    ⟨[88439, 15], [22861, 88439], .contexts [
        ⟨50699, false, false, [], []⟩,
        ⟨50698, true, false, [22844], [15]⟩,
        ⟨2072, false, false, [22844, 88441], []⟩,
        ⟨29, false, false, [22844, 88441], []⟩,
        ⟨50303, false, false, [22844], []⟩,
        ⟨50304, false, false, [22844], []⟩,
        ⟨50229, false, false, [22844], []⟩,
        ⟨50229, false, false, [22844], []⟩,
        ⟨50635, true, false, [], [88439]⟩
      ]⟩,
    ⟨[22817, 85587], [22817, 85587], .contexts []⟩,
    ⟨[86301, 7, 9], [22817, 85585], .contexts [
        ⟨50695, false, false, [], [9]⟩,
        ⟨50695, false, false, [], [9]⟩,
        ⟨36290, true, false, [], [7, 9]⟩,
        ⟨50692, true, false, [22814], [11, 7, 9]⟩,
        ⟨555, false, false, [22814, 85589], [9]⟩,
        ⟨50694, false, false, [22814], [9]⟩,
        ⟨50693, false, false, [22814], [9]⟩,
        ⟨50696, false, false, [22814], [9]⟩,
        ⟨50524, true, false, [], [85587, 9]⟩,
        ⟨50701, false, false, [], [9]⟩,
        ⟨50701, false, false, [], [9]⟩,
        ⟨32628, false, false, [22817], []⟩
      ]⟩,
    ⟨[85585, 7], [85585, 7], .contexts []⟩,
    ⟨[22861, 88439], [22861, 88439], .contexts []⟩,
    ⟨[22861, 88439], [22861, 88439], .contexts []⟩,
    ⟨[22861, 88437], [22861, 88437], .contexts []⟩,
    ⟨[88437, 15], [88437, 15], .contexts []⟩,
    ⟨[88437], [88437], .contexts []⟩,
    ⟨[88437, 15], [22845, 88437], .contexts [
        ⟨50707, false, false, [], []⟩,
        ⟨50706, true, false, [22860], [15]⟩,
        ⟨50226, true, false, [], [15]⟩,
        ⟨50705, true, false, [22860], [3, 15]⟩,
        ⟨50705, true, false, [22860], [3, 15]⟩,
        ⟨50704, true, false, [22860], [3, 15]⟩,
        ⟨50700, true, false, [22860], [3, 15]⟩,
        ⟨50699, true, false, [22860], [3, 15]⟩,
        ⟨1141, false, false, [22860, 88439], []⟩,
        ⟨21, false, false, [22860, 88439], []⟩,
        ⟨50305, false, false, [22860], []⟩,
        ⟨50306, false, false, [22860], []⟩,
        ⟨50225, false, false, [22860], []⟩,
        ⟨50225, false, false, [22860], []⟩,
        ⟨50708, false, false, [22860], []⟩,
        ⟨50666, true, false, [], [88437]⟩
      ]⟩,
    ⟨[22815, 86299], [22815, 86299], .contexts []⟩,
    ⟨[22815, 86297], [22815, 86297], .contexts []⟩,
    ⟨[22815, 86297, 7], [85585, 1], .contexts [
        ⟨50711, true, false, [], [7]⟩,
        ⟨36285, true, false, [22815], [7]⟩,
        ⟨50710, true, false, [], [1, 7]⟩,
        ⟨50710, true, false, [], [1, 7]⟩,
        ⟨50574, false, false, [], [86299, 1, 7]⟩,
        ⟨36287, true, false, [22816], [1, 7]⟩,
        ⟨36287, true, false, [22816], [1, 7]⟩,
        ⟨36367, true, false, [22816], [1, 7]⟩,
        ⟨36366, true, false, [22816], [1, 7]⟩,
        ⟨47, true, false, [22816, 86301], [1, 7]⟩,
        ⟨579, true, false, [22816, 86301], [1, 7]⟩,
        ⟨50702, false, false, [22816], [7, 1, 7]⟩,
        ⟨50703, true, false, [], [1, 7]⟩,
        ⟨50703, true, false, [], [1, 7]⟩,
        ⟨502, false, false, [85585], []⟩,
        ⟨9, false, false, [85585], []⟩
      ]⟩,
    ⟨[22845, 88437], [22845, 88437], .contexts []⟩,
    ⟨[22845, 88437], [22845, 88437], .contexts []⟩,
    ⟨[22845, 88433], [22845, 88433], .contexts []⟩,
    ⟨[22845, 88433], [22845, 88433], .contexts []⟩,
    ⟨[88433, 1], [22861, 88437], .contexts [
        ⟨50716, true, false, [22844], [1]⟩,
        ⟨50715, true, false, [22844], [1]⟩,
        ⟨50219, true, false, [], [1]⟩,
        ⟨50222, true, false, [], [15, 1]⟩,
        ⟨50714, true, false, [22844], [1, 15, 1]⟩,
        ⟨50714, true, false, [22844], [1, 15, 1]⟩,
        ⟨50713, true, false, [22844], [1, 15, 1]⟩,
        ⟨50709, true, false, [22844], [1, 15, 1]⟩,
        ⟨50707, true, false, [22844], [1, 15, 1]⟩,
        ⟨504, false, false, [22844, 88437], []⟩,
        ⟨50708, false, false, [22844], []⟩,
        ⟨50635, true, false, [], [88437]⟩
      ]⟩,
    ⟨[88471], [83343, 3], .source 44300⟩,
    ⟨[83343, 3], [88471], .contexts [
        ⟨50718, true, false, [], []⟩
      ]⟩,
    ⟨[88471, 3], [83343], .contexts [
        ⟨50719, true, false, [], [3]⟩,
        ⟨20, false, false, [83343], []⟩,
        ⟨20647, false, false, [], []⟩
      ]⟩,
    ⟨[88471], [88471], .contexts []⟩,
    ⟨[88471], [88471], .contexts []⟩,
    ⟨[83343, 3], [88471], .contexts [
        ⟨50719, false, false, [], []⟩,
        ⟨50721, false, false, [], []⟩,
        ⟨50722, false, false, [], []⟩,
        ⟨50722, false, false, [], []⟩
      ]⟩,
    ⟨[16139, 82801], [16139, 82801], .contexts []⟩,
    ⟨[16139, 82801], [16139, 82801], .contexts []⟩,
    ⟨[22869], [16139, 2211], .source 11499⟩,
    ⟨[22871], [22869, 16035], .source 11500⟩,
    ⟨[22873], [22871, 18655], .source 11501⟩,
    ⟨[88471, 5], [88471, 5], .contexts []⟩,
    ⟨[88471, 5], [22873, 85945], .contexts [
        ⟨50729, false, false, [], []⟩,
        ⟨50723, true, false, [], [5]⟩,
        ⟨871, false, false, [83343], []⟩,
        ⟨873, false, false, [83343], []⟩,
        ⟨20657, false, false, [], [3, 5, 3]⟩,
        ⟨20659, false, false, [], [3, 5, 3]⟩,
        ⟨50724, false, false, [], [3, 5, 3]⟩,
        ⟨50725, false, false, [], [3, 5, 3]⟩,
        ⟨50725, false, false, [], [3, 5, 3]⟩,
        ⟨16780, false, false, [16139], [5, 3]⟩,
        ⟨50726, true, false, [], [79199, 5, 3]⟩,
        ⟨19867, false, false, [22869], [3]⟩,
        ⟨50727, true, false, [], [83201, 3]⟩,
        ⟨34497, false, false, [22871], []⟩,
        ⟨50728, true, false, [], [85945]⟩,
        ⟨34502, false, false, [22873], []⟩
      ]⟩,
    ⟨[88471, 5], [22873, 85945], .contexts [
        ⟨50730, false, false, [], []⟩,
        ⟨13, true, false, [], [22873, 85945]⟩
      ]⟩,
    ⟨[22875], [22872], .source 11502⟩,
    ⟨[85945, 5], [22875, 88471], .contexts [
        ⟨50731, true, false, [22872], [5]⟩,
        ⟨28, false, false, [22872, 88471], []⟩,
        ⟨50732, true, false, [], [88471]⟩
      ]⟩,
    ⟨[88471, 13], [88471, 13], .contexts []⟩,
    ⟨[88471, 13], [18323, 85615], .contexts [
        ⟨50734, false, false, [], []⟩,
        ⟨50723, true, false, [], [13]⟩,
        ⟨147, false, false, [83343], []⟩,
        ⟨148, false, false, [83343], []⟩,
        ⟨20662, false, false, [], [3]⟩,
        ⟨20663, false, false, [], [3]⟩,
        ⟨16751, false, false, [], [3]⟩,
        ⟨16752, false, false, [], [3]⟩,
        ⟨16752, false, false, [], [3]⟩,
        ⟨32863, false, false, [], []⟩,
        ⟨40602, false, false, [], []⟩,
        ⟨40603, false, false, [], []⟩,
        ⟨40603, false, false, [], []⟩,
        ⟨32873, false, false, [18323], []⟩,
        ⟨40608, true, false, [], [85615]⟩
      ]⟩,
    ⟨[85615, 13], [18321, 88471], .contexts [
        ⟨50735, true, false, [18322], [13]⟩,
        ⟨59, false, false, [18322, 88471], []⟩,
        ⟨32876, true, false, [], [88471]⟩
      ]⟩,
    ⟨[2575, 88471], [2575, 88471], .contexts []⟩,
    ⟨[2575, 88471], [2575, 88471], .contexts []⟩,
    ⟨[88471, 15], [88471, 15], .contexts []⟩,
    ⟨[88471], [88471], .contexts []⟩,
    ⟨[88471, 15], [2575, 88471], .contexts [
        ⟨50739, false, false, [], []⟩,
        ⟨50723, true, false, [], [15]⟩,
        ⟨151, false, false, [83343], []⟩,
        ⟨152, false, false, [83343], []⟩,
        ⟨20666, false, false, [], [3]⟩,
        ⟨20667, false, false, [], [3]⟩,
        ⟨20664, false, false, [], [3]⟩,
        ⟨20665, false, false, [], [3]⟩,
        ⟨20665, false, false, [], [3]⟩,
        ⟨50719, false, false, [2575], []⟩,
        ⟨50737, false, false, [], []⟩,
        ⟨50738, false, false, [], []⟩,
        ⟨50740, false, false, [2575], []⟩,
        ⟨5618, true, false, [], [88471]⟩
      ]⟩,
    ⟨[88473], [85941, 9], .source 44301⟩,
    ⟨[85941, 9], [88473], .contexts [
        ⟨50742, true, false, [], []⟩
      ]⟩,
    ⟨[88473, 9], [85941], .contexts [
        ⟨50743, true, false, [], [9]⟩,
        ⟨46, false, false, [85941], []⟩,
        ⟨34246, false, false, [], []⟩
      ]⟩,
    ⟨[88473], [88473], .contexts []⟩,
    ⟨[88473], [88473], .contexts []⟩,
    ⟨[85941, 9], [88473], .contexts [
        ⟨50743, false, false, [], []⟩,
        ⟨50745, false, false, [], []⟩,
        ⟨50746, false, false, [], []⟩,
        ⟨50746, false, false, [], []⟩
      ]⟩,
    ⟨[21817, 87807], [21817, 87807], .contexts []⟩,
    ⟨[21817, 87807], [21817, 87807], .contexts []⟩,
    ⟨[21817, 87809], [21817, 87809], .contexts []⟩,
    ⟨[21817, 87809], [21817, 87809], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 793. -/
def y322TCIndexRaw793 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88473, 3], [88473, 3], .contexts []⟩,
    ⟨[21817], [21817], .contexts [
        ⟨13, false, false, [], [21817]⟩
      ]⟩,
    ⟨[88473, 3], [21817, 87809], .contexts [
        ⟨50752, false, false, [], []⟩,
        ⟨50747, true, false, [], [3]⟩,
        ⟨196, false, false, [85941], []⟩,
        ⟨197, false, false, [85941], []⟩,
        ⟨46525, false, false, [], [9]⟩,
        ⟨50748, false, false, [], [9]⟩,
        ⟨50749, false, false, [], [9]⟩,
        ⟨50749, false, false, [], [9]⟩,
        ⟨46612, false, false, [21817], []⟩,
        ⟨50750, false, false, [], []⟩,
        ⟨50751, false, false, [], []⟩,
        ⟨46624, false, false, [21817], []⟩,
        ⟨50753, true, false, [], [87809]⟩
      ]⟩,
    ⟨[21815], [21816], .contexts [
        ⟨46524, true, true, [], []⟩
      ]⟩,
    ⟨[87809, 3], [21815, 88473], .contexts [
        ⟨50754, true, false, [21816], [3]⟩,
        ⟨20, false, false, [21816, 88473], []⟩,
        ⟨50755, true, false, [], [88473]⟩
      ]⟩,
    ⟨[18661, 88473], [18661, 88473], .contexts []⟩,
    ⟨[18661, 88473], [18661, 88473], .contexts []⟩,
    ⟨[88473, 15], [88473, 15], .contexts []⟩,
    ⟨[88473], [88473], .contexts []⟩,
    ⟨[18661], [18661], .contexts [
        ⟨13, false, false, [], [18661]⟩,
        ⟨34516, false, false, [], []⟩,
        ⟨34517, false, false, [], []⟩
      ]⟩,
    ⟨[88473, 15], [18661, 88473], .contexts [
        ⟨50759, false, false, [], []⟩,
        ⟨50747, true, false, [], [15]⟩,
        ⟨205, false, false, [85941], []⟩,
        ⟨206, false, false, [85941], []⟩,
        ⟨40424, false, false, [], [9]⟩,
        ⟨50743, false, false, [18661], []⟩,
        ⟨50757, false, false, [], []⟩,
        ⟨50758, false, false, [], []⟩,
        ⟨50760, false, false, [18661], []⟩,
        ⟨50761, true, false, [], [88473]⟩
      ]⟩,
    ⟨[88475], [88473, 11], .source 44302⟩,
    ⟨[88473, 11], [88475], .contexts [
        ⟨50763, true, false, [], []⟩
      ]⟩,
    ⟨[88475, 11], [88473], .contexts [
        ⟨50764, true, false, [], [11]⟩,
        ⟨53, false, false, [88473], []⟩,
        ⟨50746, false, false, [], []⟩
      ]⟩,
    ⟨[88475], [88475], .contexts []⟩,
    ⟨[88475], [88475], .contexts []⟩,
    ⟨[88473, 11], [88475], .contexts [
        ⟨50764, false, false, [], []⟩,
        ⟨50766, false, false, [], []⟩,
        ⟨50767, false, false, [], []⟩,
        ⟨50767, false, false, [], []⟩
      ]⟩,
    ⟨[88473, 3], [21817, 87809], .contexts [
        ⟨50752, false, false, [], []⟩,
        ⟨50754, false, false, [], []⟩,
        ⟨50750, false, false, [], []⟩,
        ⟨50751, false, false, [], []⟩,
        ⟨50751, false, false, [], []⟩
      ]⟩,
    ⟨[21817, 87811], [21817, 87811], .contexts []⟩,
    ⟨[21817, 87811], [21817, 87811], .contexts []⟩,
    ⟨[88475, 3], [88475, 3], .contexts []⟩,
    ⟨[88475, 3], [21817, 87811], .contexts [
        ⟨50772, false, false, [], []⟩,
        ⟨50768, true, false, [], [3]⟩,
        ⟨215, false, false, [88473], []⟩,
        ⟨216, false, false, [88473], []⟩,
        ⟨50769, false, false, [], [11]⟩,
        ⟨46636, false, false, [21817], []⟩,
        ⟨50770, false, false, [], []⟩,
        ⟨50771, false, false, [], []⟩,
        ⟨46644, false, false, [21817], []⟩,
        ⟨50753, true, false, [], [87811]⟩
      ]⟩,
    ⟨[87811, 3], [21815, 88475], .contexts [
        ⟨50773, true, false, [21816], [3]⟩,
        ⟨20, false, false, [21816, 88475], []⟩,
        ⟨50755, true, false, [], [88475]⟩
      ]⟩,
    ⟨[88473, 15], [18661, 88473], .contexts [
        ⟨50759, false, false, [], []⟩,
        ⟨50762, false, false, [], []⟩,
        ⟨50757, false, false, [], []⟩,
        ⟨50758, false, false, [], []⟩,
        ⟨50758, false, false, [], []⟩
      ]⟩,
    ⟨[18661, 88475], [18661, 88475], .contexts []⟩,
    ⟨[18661, 88475], [18661, 88475], .contexts []⟩,
    ⟨[88475, 15], [88475, 15], .contexts []⟩,
    ⟨[88475], [88475], .contexts []⟩,
    ⟨[88475, 15], [18661, 88475], .contexts [
        ⟨50778, false, false, [], []⟩,
        ⟨50768, true, false, [], [15]⟩,
        ⟨231, false, false, [88473], []⟩,
        ⟨232, false, false, [88473], []⟩,
        ⟨50775, false, false, [], [11]⟩,
        ⟨50764, false, false, [18661], []⟩,
        ⟨50776, false, false, [], []⟩,
        ⟨50777, false, false, [], []⟩,
        ⟨50779, false, false, [18661], []⟩,
        ⟨50761, true, false, [], [88475]⟩
      ]⟩,
    ⟨[88477], [88475, 1], .source 44303⟩,
    ⟨[88475, 1], [88477], .contexts [
        ⟨50781, true, false, [], []⟩
      ]⟩,
    ⟨[88477, 1], [88475], .contexts [
        ⟨50782, true, false, [], [1]⟩,
        ⟨8, false, false, [88475], []⟩,
        ⟨50767, false, false, [], []⟩
      ]⟩,
    ⟨[88475, 1], [88477], .contexts [
        ⟨50782, false, false, [], []⟩
      ]⟩,
    ⟨[88477], [88477], .contexts []⟩,
    ⟨[88477], [88477], .contexts []⟩,
    ⟨[88475, 1], [88477], .contexts [
        ⟨50784, false, false, [], []⟩,
        ⟨50785, false, false, [], []⟩,
        ⟨50786, false, false, [], []⟩,
        ⟨50786, false, false, [], []⟩
      ]⟩,
    ⟨[88475, 3], [21817, 87811], .contexts [
        ⟨50772, false, false, [], []⟩,
        ⟨50773, false, false, [], []⟩,
        ⟨50770, false, false, [], []⟩,
        ⟨50771, false, false, [], []⟩,
        ⟨50771, false, false, [], []⟩
      ]⟩,
    ⟨[22877], [21817, 4217], .source 11503⟩,
    ⟨[22879], [22877, 21815], .source 11504⟩,
    ⟨[22879, 88477], [22879, 88477], .contexts []⟩,
    ⟨[22879, 88477], [22879, 88477], .contexts []⟩,
    ⟨[22879, 88477], [22879, 88477], .contexts []⟩,
    ⟨[88477, 3], [88477, 3], .contexts []⟩,
    ⟨[88477], [88477], .contexts []⟩,
    ⟨[22879], [22879], .contexts [
        ⟨13, false, false, [], [22879]⟩
      ]⟩,
    ⟨[88477, 3], [22879, 88477], .contexts [
        ⟨50794, false, false, [], []⟩,
        ⟨50787, true, false, [], [3]⟩,
        ⟨1098, false, false, [88475], []⟩,
        ⟨1100, false, false, [88475], []⟩,
        ⟨50788, false, false, [], [1, 3, 1]⟩,
        ⟨46645, false, false, [21817], [3, 1]⟩,
        ⟨50789, true, false, [], [87811, 3, 1]⟩,
        ⟨50774, false, false, [22877], [1]⟩,
        ⟨50790, true, false, [], [88475, 1]⟩,
        ⟨50782, false, false, [22879], []⟩,
        ⟨50791, false, false, [], []⟩,
        ⟨50792, false, false, [], []⟩,
        ⟨50793, false, false, [], []⟩,
        ⟨50795, false, false, [22879], []⟩,
        ⟨50796, true, false, [], [88477]⟩
      ]⟩,
    ⟨[18661, 88477], [18661, 88477], .contexts []⟩,
    ⟨[18661, 88477], [18661, 88477], .contexts []⟩,
    ⟨[88477, 15], [18661, 88477], .contexts [
        ⟨50787, true, false, [], [15]⟩,
        ⟨121, false, false, [88475], []⟩,
        ⟨122, false, false, [88475], []⟩,
        ⟨50778, false, false, [], [1]⟩,
        ⟨50780, false, false, [], [1]⟩,
        ⟨50776, false, false, [], [1]⟩,
        ⟨50777, false, false, [], [1]⟩,
        ⟨50777, false, false, [], [1]⟩,
        ⟨50782, false, false, [18661], []⟩,
        ⟨50798, false, false, [], []⟩,
        ⟨50799, false, false, [], []⟩,
        ⟨50795, false, false, [18661], []⟩,
        ⟨50761, true, false, [], [88477]⟩
      ]⟩,
    ⟨[88479], [88477, 13], .source 44304⟩,
    ⟨[88477, 13], [88479], .contexts [
        ⟨50801, true, false, [], []⟩
      ]⟩,
    ⟨[88479, 13], [88477], .contexts [
        ⟨50802, true, false, [], [13]⟩,
        ⟨59, false, false, [88477], []⟩,
        ⟨50786, false, false, [], []⟩
      ]⟩,
    ⟨[88479], [88479], .contexts []⟩,
    ⟨[88479], [88479], .contexts []⟩,
    ⟨[22879, 88479], [22879, 88479], .contexts []⟩,
    ⟨[22879, 88479], [22879, 88479], .contexts []⟩,
    ⟨[22879, 88479], [22879, 88479], .contexts []⟩,
    ⟨[88479, 3], [88479, 3], .contexts []⟩,
    ⟨[88479], [88479], .contexts []⟩,
    ⟨[88479, 3], [22879, 88479], .contexts [
        ⟨50809, false, false, [], []⟩,
        ⟨50805, true, false, [], [3]⟩,
        ⟨50805, true, false, [], [3]⟩,
        ⟨50804, true, false, [], [3]⟩,
        ⟨50802, true, false, [], [3]⟩,
        ⟨63, false, false, [88477], []⟩,
        ⟨65, false, false, [88477], []⟩,
        ⟨50794, false, false, [], [13]⟩,
        ⟨50797, false, false, [], [13]⟩,
        ⟨50791, false, false, [], [13]⟩,
        ⟨50793, false, false, [], [13]⟩,
        ⟨50793, false, false, [], [13]⟩,
        ⟨50802, false, false, [22879], []⟩,
        ⟨50806, false, false, [], []⟩,
        ⟨50807, false, false, [], []⟩,
        ⟨50808, false, false, [], []⟩,
        ⟨50810, false, false, [22879], []⟩,
        ⟨50796, true, false, [], [88479]⟩
      ]⟩,
    ⟨[88481], [88479, 15], .source 44305⟩,
    ⟨[88479, 15], [88481], .contexts [
        ⟨50812, true, false, [], []⟩
      ]⟩,
    ⟨[88481], [88481], .contexts []⟩,
    ⟨[88481], [88481], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 794. -/
def y322TCIndexRaw794 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88479, 15], [88481], .contexts [
        ⟨50813, false, false, [], []⟩,
        ⟨50814, false, false, [], []⟩,
        ⟨50815, false, false, [], []⟩,
        ⟨50815, false, false, [], []⟩
      ]⟩,
    ⟨[22879, 88481], [22879, 88481], .contexts []⟩,
    ⟨[22879, 88481], [22879, 88481], .contexts []⟩,
    ⟨[22879, 88481], [22879, 88481], .contexts []⟩,
    ⟨[88481], [88481], .contexts []⟩,
    ⟨[88481, 3], [22879, 88481], .contexts [
        ⟨50816, true, false, [], [3]⟩,
        ⟨19, false, false, [88479], []⟩,
        ⟨22, false, false, [88479], []⟩,
        ⟨50809, false, false, [], [15]⟩,
        ⟨50811, false, false, [], [15]⟩,
        ⟨50806, false, false, [], [15]⟩,
        ⟨50808, false, false, [], [15]⟩,
        ⟨50808, false, false, [], [15]⟩,
        ⟨50813, false, false, [22879], []⟩,
        ⟨50817, false, false, [], []⟩,
        ⟨50818, false, false, [], []⟩,
        ⟨50819, false, false, [], []⟩,
        ⟨50820, false, false, [22879], []⟩,
        ⟨50796, true, false, [], [88481]⟩
      ]⟩,
    ⟨[88481, 13], [18661, 88481], .contexts [
        ⟨50816, true, false, [], [13]⟩,
        ⟨259, false, false, [88479], []⟩,
        ⟨262, false, false, [88479], []⟩,
        ⟨50803, false, false, [], [15, 13, 15]⟩,
        ⟨50785, false, false, [], [15, 13, 15]⟩,
        ⟨50786, false, false, [], [15, 13, 15]⟩,
        ⟨50786, false, false, [], [15, 13, 15]⟩,
        ⟨50800, false, false, [], [13, 15]⟩,
        ⟨50798, false, false, [], [13, 15]⟩,
        ⟨50799, false, false, [], [13, 15]⟩,
        ⟨50799, false, false, [], [13, 15]⟩,
        ⟨50802, false, false, [18661], [15]⟩,
        ⟨50813, false, false, [18661], []⟩,
        ⟨50820, false, false, [18661], []⟩
      ]⟩,
    ⟨[88483], [88481, 1], .source 44306⟩,
    ⟨[88481, 1], [88483], .contexts [
        ⟨50823, true, false, [], []⟩
      ]⟩,
    ⟨[88483, 1], [88481], .contexts [
        ⟨50824, true, false, [], [1]⟩,
        ⟨8, false, false, [88481], []⟩,
        ⟨50815, false, false, [], []⟩
      ]⟩,
    ⟨[88485], [88483, 3], .source 44307⟩,
    ⟨[88483, 3], [88485], .contexts [
        ⟨50826, true, false, [], []⟩
      ]⟩,
    ⟨[88485], [88485], .contexts []⟩,
    ⟨[88485], [88485], .contexts []⟩,
    ⟨[22879, 88483], [22879, 88483], .contexts []⟩,
    ⟨[22879, 88483], [22879, 88483], .contexts []⟩,
    ⟨[22879, 88483], [22879, 88483], .contexts []⟩,
    ⟨[22879, 88485], [22879, 88485], .contexts []⟩,
    ⟨[22879, 88485], [22879, 88485], .contexts []⟩,
    ⟨[22879, 88485], [22879, 88485], .contexts []⟩,
    ⟨[88485, 1], [88485, 1], .contexts []⟩,
    ⟨[88485, 1], [22879, 88485], .contexts [
        ⟨50836, false, false, [], []⟩,
        ⟨50829, true, false, [], [1]⟩,
        ⟨50829, true, false, [], [1]⟩,
        ⟨50828, true, false, [], [1]⟩,
        ⟨50827, true, false, [], [1]⟩,
        ⟨130, false, false, [88483], []⟩,
        ⟨133, false, false, [88483], []⟩,
        ⟨50825, false, false, [], [3, 1, 3]⟩,
        ⟨50814, false, false, [], [3, 1, 3]⟩,
        ⟨50815, false, false, [], [3, 1, 3]⟩,
        ⟨50815, false, false, [], [3, 1, 3]⟩,
        ⟨50821, false, false, [], [1, 3]⟩,
        ⟨50817, false, false, [], [1, 3]⟩,
        ⟨50819, false, false, [], [1, 3]⟩,
        ⟨50819, false, false, [], [1, 3]⟩,
        ⟨50824, false, false, [22879], [3]⟩,
        ⟨50830, false, false, [], [3]⟩,
        ⟨50831, false, false, [], [3]⟩,
        ⟨50832, false, false, [], [3]⟩,
        ⟨50827, false, false, [22879], []⟩,
        ⟨50833, false, false, [], []⟩,
        ⟨50834, false, false, [], []⟩,
        ⟨50835, false, false, [], []⟩
      ]⟩,
    ⟨[88485, 1], [22879, 88485], .contexts [
        ⟨50837, false, false, [], []⟩,
        ⟨50796, true, false, [], [88485]⟩
      ]⟩,
    ⟨[88487], [88485, 5], .source 44308⟩,
    ⟨[88485, 5], [88487], .contexts [
        ⟨50839, true, false, [], []⟩
      ]⟩,
    ⟨[88487, 5], [88485], .contexts [
        ⟨50840, true, false, [], [5]⟩,
        ⟨28, false, false, [88485], []⟩,
        ⟨50829, false, false, [], []⟩
      ]⟩,
    ⟨[88487], [88487], .contexts []⟩,
    ⟨[88487], [88487], .contexts []⟩,
    ⟨[22879, 88487], [22879, 88487], .contexts []⟩,
    ⟨[22879, 88487], [22879, 88487], .contexts []⟩,
    ⟨[88487], [88487], .contexts []⟩,
    ⟨[88487, 1], [22879, 88487], .contexts [
        ⟨50843, true, false, [], [1]⟩,
        ⟨50843, true, false, [], [1]⟩,
        ⟨50842, true, false, [], [1]⟩,
        ⟨50840, true, false, [], [1]⟩,
        ⟨161, false, false, [88485], []⟩,
        ⟨162, false, false, [88485], []⟩,
        ⟨50836, false, false, [], [5]⟩,
        ⟨50838, false, false, [], [5]⟩,
        ⟨50833, false, false, [], [5]⟩,
        ⟨50835, false, false, [], [5]⟩,
        ⟨50835, false, false, [], [5]⟩,
        ⟨50840, false, false, [22879], []⟩,
        ⟨50844, false, false, [], []⟩,
        ⟨50845, false, false, [], []⟩,
        ⟨50846, false, false, [22879], []⟩,
        ⟨50796, true, false, [], [88487]⟩
      ]⟩,
    ⟨[88489], [88487, 9], .source 44309⟩,
    ⟨[88487, 9], [88489], .contexts [
        ⟨50848, true, false, [], []⟩
      ]⟩,
    ⟨[88489, 9], [88487], .contexts [
        ⟨50849, true, false, [], [9]⟩,
        ⟨46, false, false, [88487], []⟩,
        ⟨50843, false, false, [], []⟩
      ]⟩,
    ⟨[88491], [88489, 11], .source 44310⟩,
    ⟨[88489, 11], [88491], .contexts [
        ⟨50851, true, false, [], []⟩
      ]⟩,
    ⟨[88489], [88489], .contexts []⟩,
    ⟨[88491, 11], [88489], .contexts [
        ⟨50852, true, false, [], [11]⟩,
        ⟨53, false, false, [88489], []⟩,
        ⟨50853, false, false, [], []⟩
      ]⟩,
    ⟨[88493], [88491, 1], .source 44311⟩,
    ⟨[88491, 1], [88493], .contexts [
        ⟨50855, true, false, [], []⟩
      ]⟩,
    ⟨[88491], [88491], .contexts []⟩,
    ⟨[88493, 1], [88491], .contexts [
        ⟨50856, true, false, [], [1]⟩,
        ⟨8, false, false, [88491], []⟩,
        ⟨50857, false, false, [], []⟩
      ]⟩,
    ⟨[88495], [88493, 13], .source 44312⟩,
    ⟨[88493, 13], [88495], .contexts [
        ⟨50859, true, false, [], []⟩
      ]⟩,
    ⟨[88493], [88493], .contexts []⟩,
    ⟨[88495, 13], [88493], .contexts [
        ⟨50860, true, false, [], [13]⟩,
        ⟨59, false, false, [88493], []⟩,
        ⟨50861, false, false, [], []⟩
      ]⟩,
    ⟨[88497], [88495, 15], .source 44313⟩,
    ⟨[88495, 15], [88497], .contexts [
        ⟨50863, true, false, [], []⟩
      ]⟩,
    ⟨[88495], [88495], .contexts []⟩,
    ⟨[88497, 15], [88495], .contexts [
        ⟨50864, true, false, [], [15]⟩,
        ⟨1, false, false, [88495], []⟩,
        ⟨50865, false, false, [], []⟩
      ]⟩,
    ⟨[88499], [88497, 1], .source 44314⟩,
    ⟨[88497, 1], [88499], .contexts [
        ⟨50867, true, false, [], []⟩
      ]⟩,
    ⟨[88497], [88497], .contexts []⟩,
    ⟨[88499, 1], [88497], .contexts [
        ⟨50868, true, false, [], [1]⟩,
        ⟨8, false, false, [88497], []⟩,
        ⟨50869, false, false, [], []⟩
      ]⟩,
    ⟨[88501], [88499, 3], .source 44315⟩,
    ⟨[88499, 3], [88501], .contexts [
        ⟨50871, true, false, [], []⟩
      ]⟩,
    ⟨[88499], [88499], .contexts []⟩,
    ⟨[88501, 3], [88499], .contexts [
        ⟨50872, true, false, [], [3]⟩,
        ⟨20, false, false, [88499], []⟩,
        ⟨50873, false, false, [], []⟩
      ]⟩,
    ⟨[88503], [88501, 5], .source 44316⟩,
    ⟨[88501, 5], [88503], .contexts [
        ⟨50875, true, false, [], []⟩
      ]⟩,
    ⟨[88501], [88501], .contexts []⟩,
    ⟨[88503, 5], [88501], .contexts [
        ⟨50876, true, false, [], [5]⟩,
        ⟨28, false, false, [88501], []⟩,
        ⟨50877, false, false, [], []⟩
      ]⟩,
    ⟨[88505], [88503, 1], .source 44317⟩]

/-- Exact literal claimed equations and contextual derivations, block 795. -/
def y322TCIndexRaw795 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88503], [88503], .contexts []⟩,
    ⟨[88505, 1], [88503], .contexts [
        ⟨50879, false, false, [], [1]⟩,
        ⟨8, false, false, [88503], []⟩,
        ⟨50880, false, false, [], []⟩
      ]⟩,
    ⟨[88507], [88505, 9], .source 44318⟩,
    ⟨[88505], [88505], .contexts []⟩,
    ⟨[88507, 9], [88505], .contexts [
        ⟨50882, false, false, [], [9]⟩,
        ⟨46, false, false, [88505], []⟩,
        ⟨50883, false, false, [], []⟩
      ]⟩,
    ⟨[88509], [88507, 11], .source 44319⟩,
    ⟨[88507], [88507], .contexts []⟩,
    ⟨[88509, 11], [88507], .contexts [
        ⟨50885, false, false, [], [11]⟩,
        ⟨53, false, false, [88507], []⟩,
        ⟨50886, false, false, [], []⟩
      ]⟩,
    ⟨[88511], [88509, 1], .source 44320⟩,
    ⟨[88509, 1], [88511], .contexts [
        ⟨50888, true, false, [], []⟩
      ]⟩,
    ⟨[88509], [88509], .contexts []⟩,
    ⟨[88511, 1], [88509], .contexts [
        ⟨50889, true, false, [], [1]⟩,
        ⟨8, false, false, [88509], []⟩,
        ⟨50890, false, false, [], []⟩
      ]⟩,
    ⟨[88513], [88511, 13], .source 44321⟩,
    ⟨[88511, 13], [88513], .contexts [
        ⟨50892, true, false, [], []⟩
      ]⟩,
    ⟨[88511], [88511], .contexts []⟩,
    ⟨[88513, 13], [88511], .contexts [
        ⟨50893, true, false, [], [13]⟩,
        ⟨59, false, false, [88511], []⟩,
        ⟨50894, false, false, [], []⟩
      ]⟩,
    ⟨[88515], [88513, 15], .source 44322⟩,
    ⟨[88513, 15], [88515], .contexts [
        ⟨50896, true, false, [], []⟩
      ]⟩,
    ⟨[88513], [88513], .contexts []⟩,
    ⟨[88515, 15], [88513], .contexts [
        ⟨50897, true, false, [], [15]⟩,
        ⟨1, false, false, [88513], []⟩,
        ⟨50898, false, false, [], []⟩
      ]⟩,
    ⟨[88517], [88515, 1], .source 44323⟩,
    ⟨[88515, 1], [88517], .contexts [
        ⟨50900, true, false, [], []⟩
      ]⟩,
    ⟨[88515], [88515], .contexts []⟩,
    ⟨[88517, 1], [88515], .contexts [
        ⟨50901, true, false, [], [1]⟩,
        ⟨8, false, false, [88515], []⟩,
        ⟨50902, false, false, [], []⟩
      ]⟩,
    ⟨[88519], [88517, 3], .source 44324⟩,
    ⟨[88517, 3], [88519], .contexts [
        ⟨50904, true, false, [], []⟩
      ]⟩,
    ⟨[88517], [88517], .contexts []⟩,
    ⟨[88519, 3], [88517], .contexts [
        ⟨50905, true, false, [], [3]⟩,
        ⟨20, false, false, [88517], []⟩,
        ⟨50906, false, false, [], []⟩
      ]⟩,
    ⟨[88521], [88519, 5], .source 44325⟩,
    ⟨[88519, 5], [88521], .contexts [
        ⟨50908, true, false, [], []⟩
      ]⟩,
    ⟨[88519], [88519], .contexts []⟩,
    ⟨[88521, 5], [88519], .contexts [
        ⟨50909, true, false, [], [5]⟩,
        ⟨28, false, false, [88519], []⟩,
        ⟨50910, false, false, [], []⟩
      ]⟩,
    ⟨[88523], [88521, 1], .source 44326⟩,
    ⟨[88521, 1], [88523], .contexts [
        ⟨50912, true, false, [], []⟩
      ]⟩,
    ⟨[88521], [88521], .contexts []⟩,
    ⟨[88523, 1], [88521], .contexts [
        ⟨50913, true, false, [], [1]⟩,
        ⟨8, false, false, [88521], []⟩,
        ⟨50914, false, false, [], []⟩
      ]⟩,
    ⟨[88525], [88523, 9], .source 44327⟩,
    ⟨[88523], [88523], .contexts []⟩,
    ⟨[88525, 9], [88523], .contexts [
        ⟨50916, false, false, [], [9]⟩,
        ⟨46, false, false, [88523], []⟩,
        ⟨50917, false, false, [], []⟩
      ]⟩,
    ⟨[88527], [88525, 11], .source 44328⟩,
    ⟨[88525], [88525], .contexts []⟩,
    ⟨[88527, 11], [88525], .contexts [
        ⟨50919, false, false, [], [11]⟩,
        ⟨53, false, false, [88525], []⟩,
        ⟨50920, false, false, [], []⟩
      ]⟩,
    ⟨[88529], [88527, 1], .source 44329⟩,
    ⟨[88527], [88527], .contexts []⟩,
    ⟨[88529, 1], [88527], .contexts [
        ⟨50922, false, false, [], [1]⟩,
        ⟨8, false, false, [88527], []⟩,
        ⟨50923, false, false, [], []⟩
      ]⟩,
    ⟨[88531], [88529, 13], .source 44330⟩,
    ⟨[88529], [88529], .contexts []⟩,
    ⟨[88531, 13], [88529], .contexts [
        ⟨50925, false, false, [], [13]⟩,
        ⟨59, false, false, [88529], []⟩,
        ⟨50926, false, false, [], []⟩
      ]⟩,
    ⟨[88533], [88531, 15], .source 44331⟩,
    ⟨[88531], [88531], .contexts []⟩,
    ⟨[88533, 15], [88531], .contexts [
        ⟨50928, false, false, [], [15]⟩,
        ⟨1, false, false, [88531], []⟩,
        ⟨50929, false, false, [], []⟩
      ]⟩,
    ⟨[88535], [88533, 1], .source 44332⟩,
    ⟨[88533], [88533], .contexts []⟩,
    ⟨[88535, 1], [88533], .contexts [
        ⟨50931, false, false, [], [1]⟩,
        ⟨8, false, false, [88533], []⟩,
        ⟨50932, false, false, [], []⟩
      ]⟩,
    ⟨[88537], [88535, 3], .source 44333⟩,
    ⟨[88535], [88535], .contexts []⟩,
    ⟨[88537, 3], [88535], .contexts [
        ⟨50934, false, false, [], [3]⟩,
        ⟨20, false, false, [88535], []⟩,
        ⟨50935, false, false, [], []⟩
      ]⟩,
    ⟨[88539], [88537, 5], .source 44334⟩,
    ⟨[88537, 5], [88539], .contexts [
        ⟨50937, true, false, [], []⟩
      ]⟩,
    ⟨[88537], [88537], .contexts []⟩,
    ⟨[88539, 5], [88537], .contexts [
        ⟨50938, true, false, [], [5]⟩,
        ⟨28, false, false, [88537], []⟩,
        ⟨50939, false, false, [], []⟩
      ]⟩,
    ⟨[88541], [88539, 1], .source 44335⟩,
    ⟨[88539, 1], [88541], .contexts [
        ⟨50941, true, false, [], []⟩
      ]⟩,
    ⟨[88539], [88539], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 796. -/
def y322TCIndexRaw796 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88541, 1], [88539], .contexts [
        ⟨50942, true, false, [], [1]⟩,
        ⟨8, false, false, [88539], []⟩,
        ⟨50943, false, false, [], []⟩
      ]⟩,
    ⟨[88543], [88541, 9], .source 44336⟩,
    ⟨[88541], [88541], .contexts []⟩,
    ⟨[88543, 9], [88541], .contexts [
        ⟨50945, false, false, [], [9]⟩,
        ⟨46, false, false, [88541], []⟩,
        ⟨50946, false, false, [], []⟩
      ]⟩,
    ⟨[88545], [88543, 11], .source 44337⟩,
    ⟨[88543], [88543], .contexts []⟩,
    ⟨[88545, 11], [88543], .contexts [
        ⟨50948, false, false, [], [11]⟩,
        ⟨53, false, false, [88543], []⟩,
        ⟨50949, false, false, [], []⟩
      ]⟩,
    ⟨[88547], [88545, 1], .source 44338⟩,
    ⟨[88545, 1], [88547], .contexts [
        ⟨50951, true, false, [], []⟩
      ]⟩,
    ⟨[88545], [88545], .contexts []⟩,
    ⟨[88547, 1], [88545], .contexts [
        ⟨50952, true, false, [], [1]⟩,
        ⟨8, false, false, [88545], []⟩,
        ⟨50953, false, false, [], []⟩
      ]⟩,
    ⟨[88549], [88547, 13], .source 44339⟩,
    ⟨[88547, 13], [88549], .contexts [
        ⟨50955, true, false, [], []⟩
      ]⟩,
    ⟨[88547], [88547], .contexts []⟩,
    ⟨[88549, 13], [88547], .contexts [
        ⟨50956, true, false, [], [13]⟩,
        ⟨59, false, false, [88547], []⟩,
        ⟨50957, false, false, [], []⟩
      ]⟩,
    ⟨[88551], [88549, 15], .source 44340⟩,
    ⟨[88549], [88549], .contexts []⟩,
    ⟨[88551, 15], [88549], .contexts [
        ⟨50959, false, false, [], [15]⟩,
        ⟨1, false, false, [88549], []⟩,
        ⟨50960, false, false, [], []⟩
      ]⟩,
    ⟨[88553], [88551, 1], .source 44341⟩,
    ⟨[88551], [88551], .contexts []⟩,
    ⟨[88553, 1], [88551], .contexts [
        ⟨50962, false, false, [], [1]⟩,
        ⟨8, false, false, [88551], []⟩,
        ⟨50963, false, false, [], []⟩
      ]⟩,
    ⟨[88555], [88553, 3], .source 44342⟩,
    ⟨[88553], [88553], .contexts []⟩,
    ⟨[88555, 3], [88553], .contexts [
        ⟨50965, false, false, [], [3]⟩,
        ⟨20, false, false, [88553], []⟩,
        ⟨50966, false, false, [], []⟩
      ]⟩,
    ⟨[88557], [88555, 5], .source 44343⟩,
    ⟨[88555, 5], [88557], .contexts [
        ⟨50968, true, false, [], []⟩
      ]⟩,
    ⟨[88555], [88555], .contexts []⟩,
    ⟨[88557, 5], [88555], .contexts [
        ⟨50969, true, false, [], [5]⟩,
        ⟨28, false, false, [88555], []⟩,
        ⟨50970, false, false, [], []⟩
      ]⟩,
    ⟨[88559], [88557, 1], .source 44344⟩,
    ⟨[88557], [88557], .contexts []⟩,
    ⟨[88559, 1], [88557], .contexts [
        ⟨50972, false, false, [], [1]⟩,
        ⟨8, false, false, [88557], []⟩,
        ⟨50973, false, false, [], []⟩
      ]⟩,
    ⟨[88561], [88559, 9], .source 44345⟩,
    ⟨[88559], [88559], .contexts []⟩,
    ⟨[88561, 9], [88559], .contexts [
        ⟨50975, false, false, [], [9]⟩,
        ⟨46, false, false, [88559], []⟩,
        ⟨50976, false, false, [], []⟩
      ]⟩,
    ⟨[88563], [88561, 11], .source 44346⟩,
    ⟨[88561, 11], [88563], .contexts [
        ⟨50978, true, false, [], []⟩
      ]⟩,
    ⟨[88561], [88561], .contexts []⟩,
    ⟨[88563, 11], [88561], .contexts [
        ⟨50979, true, false, [], [11]⟩,
        ⟨53, false, false, [88561], []⟩,
        ⟨50980, false, false, [], []⟩
      ]⟩,
    ⟨[88565], [88563, 1], .source 44347⟩,
    ⟨[88563], [88563], .contexts []⟩,
    ⟨[88565, 1], [88563], .contexts [
        ⟨50982, false, false, [], [1]⟩,
        ⟨8, false, false, [88563], []⟩,
        ⟨50983, false, false, [], []⟩
      ]⟩,
    ⟨[88567], [88565, 13], .source 44348⟩,
    ⟨[88565], [88565], .contexts []⟩,
    ⟨[88567, 13], [88565], .contexts [
        ⟨50985, false, false, [], [13]⟩,
        ⟨59, false, false, [88565], []⟩,
        ⟨50986, false, false, [], []⟩
      ]⟩,
    ⟨[88569], [88567, 15], .source 44349⟩,
    ⟨[88567, 15], [88569], .contexts [
        ⟨50988, true, false, [], []⟩
      ]⟩,
    ⟨[88567], [88567], .contexts []⟩,
    ⟨[88569, 15], [88567], .contexts [
        ⟨50989, true, false, [], [15]⟩,
        ⟨1, false, false, [88567], []⟩,
        ⟨50990, false, false, [], []⟩
      ]⟩,
    ⟨[88571], [88569, 1], .source 44350⟩,
    ⟨[88569, 1], [88571], .contexts [
        ⟨50992, true, false, [], []⟩
      ]⟩,
    ⟨[88569], [88569], .contexts []⟩,
    ⟨[88571, 1], [88569], .contexts [
        ⟨50993, true, false, [], [1]⟩,
        ⟨8, false, false, [88569], []⟩,
        ⟨50994, false, false, [], []⟩
      ]⟩,
    ⟨[88573], [88571, 3], .source 44351⟩,
    ⟨[88571, 3], [88573], .contexts [
        ⟨50996, true, false, [], []⟩
      ]⟩,
    ⟨[88571], [88571], .contexts []⟩,
    ⟨[88573, 3], [88571], .contexts [
        ⟨50997, true, false, [], [3]⟩,
        ⟨20, false, false, [88571], []⟩,
        ⟨50998, false, false, [], []⟩
      ]⟩,
    ⟨[88575], [88573, 5], .source 44352⟩,
    ⟨[88573, 5], [88575], .contexts [
        ⟨51000, true, false, [], []⟩
      ]⟩,
    ⟨[88573], [88573], .contexts []⟩,
    ⟨[88575, 5], [88573], .contexts [
        ⟨51001, true, false, [], [5]⟩,
        ⟨28, false, false, [88573], []⟩,
        ⟨51002, false, false, [], []⟩
      ]⟩,
    ⟨[88577], [88575, 1], .source 44353⟩,
    ⟨[88575, 1], [88577], .contexts [
        ⟨51004, true, false, [], []⟩
      ]⟩,
    ⟨[88575], [88575], .contexts []⟩,
    ⟨[88577, 1], [88575], .contexts [
        ⟨51005, true, false, [], [1]⟩,
        ⟨8, false, false, [88575], []⟩,
        ⟨51006, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 797. -/
def y322TCIndexRaw797 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88579], [88577, 9], .source 44354⟩,
    ⟨[88577, 9], [88579], .contexts [
        ⟨51008, true, false, [], []⟩
      ]⟩,
    ⟨[88577], [88577], .contexts []⟩,
    ⟨[88579, 9], [88577], .contexts [
        ⟨51009, true, false, [], [9]⟩,
        ⟨46, false, false, [88577], []⟩,
        ⟨51010, false, false, [], []⟩
      ]⟩,
    ⟨[88581], [88579, 11], .source 44355⟩,
    ⟨[88579, 11], [88581], .contexts [
        ⟨51012, true, false, [], []⟩
      ]⟩,
    ⟨[88579], [88579], .contexts []⟩,
    ⟨[88581, 11], [88579], .contexts [
        ⟨51013, true, false, [], [11]⟩,
        ⟨53, false, false, [88579], []⟩,
        ⟨51014, false, false, [], []⟩
      ]⟩,
    ⟨[88583], [88581, 1], .source 44356⟩,
    ⟨[88581], [88581], .contexts []⟩,
    ⟨[88583, 1], [88581], .contexts [
        ⟨51016, false, false, [], [1]⟩,
        ⟨8, false, false, [88581], []⟩,
        ⟨51017, false, false, [], []⟩
      ]⟩,
    ⟨[88585], [88583, 13], .source 44357⟩,
    ⟨[88583], [88583], .contexts []⟩,
    ⟨[88585, 13], [88583], .contexts [
        ⟨51019, false, false, [], [13]⟩,
        ⟨59, false, false, [88583], []⟩,
        ⟨51020, false, false, [], []⟩
      ]⟩,
    ⟨[88587], [88585, 15], .source 44358⟩,
    ⟨[88585, 15], [88587], .contexts [
        ⟨51022, true, false, [], []⟩
      ]⟩,
    ⟨[88585], [88585], .contexts []⟩,
    ⟨[88587, 15], [88585], .contexts [
        ⟨51023, true, false, [], [15]⟩,
        ⟨1, false, false, [88585], []⟩,
        ⟨51024, false, false, [], []⟩
      ]⟩,
    ⟨[88589], [88587, 1], .source 44359⟩,
    ⟨[88587], [88587], .contexts []⟩,
    ⟨[88589, 1], [88587], .contexts [
        ⟨51026, false, false, [], [1]⟩,
        ⟨8, false, false, [88587], []⟩,
        ⟨51027, false, false, [], []⟩
      ]⟩,
    ⟨[88591], [88589, 3], .source 44360⟩,
    ⟨[88589, 3], [88591], .contexts [
        ⟨51029, true, false, [], []⟩
      ]⟩,
    ⟨[88589], [88589], .contexts []⟩,
    ⟨[88591, 3], [88589], .contexts [
        ⟨51030, true, false, [], [3]⟩,
        ⟨20, false, false, [88589], []⟩,
        ⟨51031, false, false, [], []⟩
      ]⟩,
    ⟨[88593], [88591, 5], .source 44361⟩,
    ⟨[88591, 5], [88593], .contexts [
        ⟨51033, true, false, [], []⟩
      ]⟩,
    ⟨[88591], [88591], .contexts []⟩,
    ⟨[88593, 5], [88591], .contexts [
        ⟨51034, true, false, [], [5]⟩,
        ⟨28, false, false, [88591], []⟩,
        ⟨51035, false, false, [], []⟩
      ]⟩,
    ⟨[88595], [88593, 1], .source 44362⟩,
    ⟨[88593], [88593], .contexts []⟩,
    ⟨[88595, 1], [88593], .contexts [
        ⟨51037, false, false, [], [1]⟩,
        ⟨8, false, false, [88593], []⟩,
        ⟨51038, false, false, [], []⟩
      ]⟩,
    ⟨[88597], [88595, 9], .source 44363⟩,
    ⟨[88595, 9], [88597], .contexts [
        ⟨51040, true, false, [], []⟩
      ]⟩,
    ⟨[88595], [88595], .contexts []⟩,
    ⟨[88597, 9], [88595], .contexts [
        ⟨51041, true, false, [], [9]⟩,
        ⟨46, false, false, [88595], []⟩,
        ⟨51042, false, false, [], []⟩
      ]⟩,
    ⟨[88599], [88597, 11], .source 44364⟩,
    ⟨[88597, 11], [88599], .contexts [
        ⟨51044, true, false, [], []⟩
      ]⟩,
    ⟨[88597], [88597], .contexts []⟩,
    ⟨[88599, 11], [88597], .contexts [
        ⟨51045, true, false, [], [11]⟩,
        ⟨53, false, false, [88597], []⟩,
        ⟨51046, false, false, [], []⟩
      ]⟩,
    ⟨[88601], [88599, 1], .source 44365⟩,
    ⟨[88599], [88599], .contexts []⟩,
    ⟨[88601, 1], [88599], .contexts [
        ⟨51048, false, false, [], [1]⟩,
        ⟨8, false, false, [88599], []⟩,
        ⟨51049, false, false, [], []⟩
      ]⟩,
    ⟨[88603], [88601, 13], .source 44366⟩,
    ⟨[88601, 13], [88603], .contexts [
        ⟨51051, true, false, [], []⟩
      ]⟩,
    ⟨[88601], [88601], .contexts []⟩,
    ⟨[88603, 13], [88601], .contexts [
        ⟨51052, true, false, [], [13]⟩,
        ⟨59, false, false, [88601], []⟩,
        ⟨51053, false, false, [], []⟩
      ]⟩,
    ⟨[88605], [88603, 15], .source 44367⟩,
    ⟨[88603, 15], [88605], .contexts [
        ⟨51055, true, false, [], []⟩
      ]⟩,
    ⟨[88603], [88603], .contexts []⟩,
    ⟨[88605, 15], [88603], .contexts [
        ⟨51056, true, false, [], [15]⟩,
        ⟨1, false, false, [88603], []⟩,
        ⟨51057, false, false, [], []⟩
      ]⟩,
    ⟨[88607], [88605, 1], .source 44368⟩,
    ⟨[88605, 1], [88607], .contexts [
        ⟨51059, true, false, [], []⟩
      ]⟩,
    ⟨[88605], [88605], .contexts []⟩,
    ⟨[88605, 1], [88607], .contexts [
        ⟨51060, false, false, [], []⟩
      ]⟩,
    ⟨[88607], [88607], .contexts []⟩,
    ⟨[88603], [88603], .contexts []⟩,
    ⟨[88605, 15], [88603], .contexts [
        ⟨51058, false, false, [], []⟩,
        ⟨51064, false, false, [], []⟩,
        ⟨51057, false, false, [], []⟩,
        ⟨51057, false, false, [], []⟩
      ]⟩,
    ⟨[88603, 13], [88601], .contexts [
        ⟨51054, false, false, [], []⟩
      ]⟩,
    ⟨[88601], [88601], .contexts []⟩,
    ⟨[88601, 1], [88599], .contexts [
        ⟨51050, false, false, [], []⟩
      ]⟩,
    ⟨[88599], [88599], .contexts []⟩,
    ⟨[88599, 11], [88597], .contexts [
        ⟨51047, false, false, [], []⟩
      ]⟩,
    ⟨[88597], [88597], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 798. -/
def y322TCIndexRaw798 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88597, 9], [88595], .contexts [
        ⟨51043, false, false, [], []⟩
      ]⟩,
    ⟨[88595], [88595], .contexts []⟩,
    ⟨[88595, 1], [88593], .contexts [
        ⟨51039, false, false, [], []⟩
      ]⟩,
    ⟨[88593], [88593], .contexts []⟩,
    ⟨[88605, 15, 13, 1, 11, 9, 1], [88593], .contexts [
        ⟨51065, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨51066, false, false, [], [1, 11, 9, 1]⟩,
        ⟨51067, false, false, [], [1, 11, 9, 1]⟩,
        ⟨51053, false, false, [], [1, 11, 9, 1]⟩,
        ⟨51053, false, false, [], [1, 11, 9, 1]⟩,
        ⟨51068, false, false, [], [11, 9, 1]⟩,
        ⟨51069, false, false, [], [11, 9, 1]⟩,
        ⟨51049, false, false, [], [11, 9, 1]⟩,
        ⟨51049, false, false, [], [11, 9, 1]⟩,
        ⟨51070, false, false, [], [9, 1]⟩,
        ⟨51071, false, false, [], [9, 1]⟩,
        ⟨51046, false, false, [], [9, 1]⟩,
        ⟨51046, false, false, [], [9, 1]⟩,
        ⟨51072, false, false, [], [1]⟩,
        ⟨51073, false, false, [], [1]⟩,
        ⟨51042, false, false, [], [1]⟩,
        ⟨51042, false, false, [], [1]⟩,
        ⟨51074, false, false, [], []⟩,
        ⟨51075, false, false, [], []⟩,
        ⟨51038, false, false, [], []⟩,
        ⟨51038, false, false, [], []⟩
      ]⟩,
    ⟨[88591], [88591], .contexts []⟩,
    ⟨[88587], [88587], .contexts []⟩,
    ⟨[88585], [88585], .contexts []⟩,
    ⟨[88585, 13], [88583], .contexts [
        ⟨51021, false, false, [], []⟩
      ]⟩,
    ⟨[88583], [88583], .contexts []⟩,
    ⟨[88605, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13], [88583], .contexts [
        ⟨51076, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨51036, false, false, [], [3, 1, 15, 13]⟩,
        ⟨51077, false, false, [], [3, 1, 15, 13]⟩,
        ⟨51035, false, false, [], [3, 1, 15, 13]⟩,
        ⟨51035, false, false, [], [3, 1, 15, 13]⟩,
        ⟨51032, false, false, [], [1, 15, 13]⟩,
        ⟨51031, false, false, [], [1, 15, 13]⟩,
        ⟨51031, false, false, [], [1, 15, 13]⟩,
        ⟨51028, false, false, [], [15, 13]⟩,
        ⟨51078, false, false, [], [15, 13]⟩,
        ⟨51027, false, false, [], [15, 13]⟩,
        ⟨51027, false, false, [], [15, 13]⟩,
        ⟨51025, false, false, [], [13]⟩,
        ⟨51079, false, false, [], [13]⟩,
        ⟨51024, false, false, [], [13]⟩,
        ⟨51024, false, false, [], [13]⟩,
        ⟨51080, false, false, [], []⟩,
        ⟨51081, false, false, [], []⟩,
        ⟨51020, false, false, [], []⟩,
        ⟨51020, false, false, [], []⟩
      ]⟩,
    ⟨[88581], [88581], .contexts []⟩,
    ⟨[88579], [88579], .contexts []⟩,
    ⟨[88579, 9], [88577], .contexts [
        ⟨51011, false, false, [], []⟩
      ]⟩,
    ⟨[88577], [88577], .contexts []⟩,
    ⟨[88577, 1], [88575], .contexts [
        ⟨51007, false, false, [], []⟩
      ]⟩,
    ⟨[88575], [88575], .contexts []⟩,
    ⟨[88575, 5], [88573], .contexts [
        ⟨51003, false, false, [], []⟩
      ]⟩,
    ⟨[88573], [88573], .contexts []⟩,
    ⟨[
      88605, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5
    ], [88573], .contexts [
        ⟨51082, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨51018, false, false, [], [11, 9, 1, 5]⟩,
        ⟨51083, false, false, [], [11, 9, 1, 5]⟩,
        ⟨51017, false, false, [], [11, 9, 1, 5]⟩,
        ⟨51017, false, false, [], [11, 9, 1, 5]⟩,
        ⟨51015, false, false, [], [9, 1, 5]⟩,
        ⟨51084, false, false, [], [9, 1, 5]⟩,
        ⟨51014, false, false, [], [9, 1, 5]⟩,
        ⟨51014, false, false, [], [9, 1, 5]⟩,
        ⟨51085, false, false, [], [1, 5]⟩,
        ⟨51086, false, false, [], [1, 5]⟩,
        ⟨51010, false, false, [], [1, 5]⟩,
        ⟨51010, false, false, [], [1, 5]⟩,
        ⟨51087, false, false, [], [5]⟩,
        ⟨51088, false, false, [], [5]⟩,
        ⟨51006, false, false, [], [5]⟩,
        ⟨51006, false, false, [], [5]⟩,
        ⟨51089, false, false, [], []⟩,
        ⟨51090, false, false, [], []⟩,
        ⟨51002, false, false, [], []⟩,
        ⟨51002, false, false, [], []⟩
      ]⟩,
    ⟨[88573, 3], [88571], .contexts [
        ⟨50999, false, false, [], []⟩
      ]⟩,
    ⟨[88571], [88571], .contexts []⟩,
    ⟨[88571, 1], [88569], .contexts [
        ⟨50995, false, false, [], []⟩
      ]⟩,
    ⟨[88569], [88569], .contexts []⟩,
    ⟨[88565], [88565], .contexts []⟩,
    ⟨[88563], [88563], .contexts []⟩,
    ⟨[
      88605, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1
    ], [88563], .contexts [
        ⟨51091, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨51092, false, false, [], [1, 15, 13, 1]⟩,
        ⟨51093, false, false, [], [1, 15, 13, 1]⟩,
        ⟨50998, false, false, [], [1, 15, 13, 1]⟩,
        ⟨50998, false, false, [], [1, 15, 13, 1]⟩,
        ⟨51094, false, false, [], [15, 13, 1]⟩,
        ⟨51095, false, false, [], [15, 13, 1]⟩,
        ⟨50994, false, false, [], [15, 13, 1]⟩,
        ⟨50994, false, false, [], [15, 13, 1]⟩,
        ⟨50991, false, false, [], [13, 1]⟩,
        ⟨50990, false, false, [], [13, 1]⟩,
        ⟨50990, false, false, [], [13, 1]⟩,
        ⟨50987, false, false, [], [1]⟩,
        ⟨51096, false, false, [], [1]⟩,
        ⟨50986, false, false, [], [1]⟩,
        ⟨50986, false, false, [], [1]⟩,
        ⟨50984, false, false, [], []⟩,
        ⟨51097, false, false, [], []⟩,
        ⟨50983, false, false, [], []⟩,
        ⟨50983, false, false, [], []⟩
      ]⟩,
    ⟨[88561], [88561], .contexts []⟩,
    ⟨[88561, 9], [88559], .contexts [
        ⟨50977, false, false, [], []⟩
      ]⟩,
    ⟨[88559], [88559], .contexts []⟩,
    ⟨[88559, 1], [88557], .contexts [
        ⟨50974, false, false, [], []⟩
      ]⟩,
    ⟨[88557], [88557], .contexts []⟩,
    ⟨[88557, 5], [88555], .contexts [
        ⟨50971, false, false, [], []⟩
      ]⟩,
    ⟨[88555], [88555], .contexts []⟩,
    ⟨[88555, 3], [88553], .contexts [
        ⟨50967, false, false, [], []⟩
      ]⟩,
    ⟨[88553], [88553], .contexts []⟩,
    ⟨[
      88605, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3
    ], [88553], .contexts [
        ⟨51098, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨50981, false, false, [], [9, 1, 5, 3]⟩,
        ⟨51099, false, false, [], [9, 1, 5, 3]⟩,
        ⟨50980, false, false, [], [9, 1, 5, 3]⟩,
        ⟨50980, false, false, [], [9, 1, 5, 3]⟩,
        ⟨51100, false, false, [], [1, 5, 3]⟩,
        ⟨51101, false, false, [], [1, 5, 3]⟩,
        ⟨50976, false, false, [], [1, 5, 3]⟩,
        ⟨50976, false, false, [], [1, 5, 3]⟩,
        ⟨51102, false, false, [], [5, 3]⟩,
        ⟨51103, false, false, [], [5, 3]⟩,
        ⟨50973, false, false, [], [5, 3]⟩,
        ⟨50973, false, false, [], [5, 3]⟩,
        ⟨51104, false, false, [], [3]⟩,
        ⟨51105, false, false, [], [3]⟩,
        ⟨50970, false, false, [], [3]⟩,
        ⟨50970, false, false, [], [3]⟩,
        ⟨51106, false, false, [], []⟩,
        ⟨51107, false, false, [], []⟩,
        ⟨50966, false, false, [], []⟩,
        ⟨50966, false, false, [], []⟩
      ]⟩,
    ⟨[88551], [88551], .contexts []⟩,
    ⟨[88549], [88549], .contexts []⟩,
    ⟨[88547], [88547], .contexts []⟩,
    ⟨[
      88605, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11
    ], [88543], .contexts [
        ⟨51108, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨50964, false, false, [], [15, 13, 1, 11]⟩,
        ⟨51109, false, false, [], [15, 13, 1, 11]⟩,
        ⟨50963, false, false, [], [15, 13, 1, 11]⟩,
        ⟨50963, false, false, [], [15, 13, 1, 11]⟩,
        ⟨50961, false, false, [], [13, 1, 11]⟩,
        ⟨51110, false, false, [], [13, 1, 11]⟩,
        ⟨50960, false, false, [], [13, 1, 11]⟩,
        ⟨50960, false, false, [], [13, 1, 11]⟩,
        ⟨50958, false, false, [], [1, 11]⟩,
        ⟨51111, false, false, [], [1, 11]⟩,
        ⟨50957, false, false, [], [1, 11]⟩,
        ⟨50957, false, false, [], [1, 11]⟩,
        ⟨50954, false, false, [], [11]⟩,
        ⟨50953, false, false, [], [11]⟩,
        ⟨50953, false, false, [], [11]⟩,
        ⟨50950, false, false, [], []⟩,
        ⟨50949, false, false, [], []⟩,
        ⟨50949, false, false, [], []⟩
      ]⟩,
    ⟨[88541], [88541], .contexts []⟩,
    ⟨[88539], [88539], .contexts []⟩,
    ⟨[88535], [88535], .contexts []⟩,
    ⟨[88533], [88533], .contexts []⟩,
    ⟨[
      88605, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1
    ], [88533], .contexts [
        ⟨51112, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨50947, false, false, [], [1, 5, 3, 1]⟩,
        ⟨51113, false, false, [], [1, 5, 3, 1]⟩,
        ⟨50946, false, false, [], [1, 5, 3, 1]⟩,
        ⟨50946, false, false, [], [1, 5, 3, 1]⟩,
        ⟨50944, false, false, [], [5, 3, 1]⟩,
        ⟨51114, false, false, [], [5, 3, 1]⟩,
        ⟨50943, false, false, [], [5, 3, 1]⟩,
        ⟨50943, false, false, [], [5, 3, 1]⟩,
        ⟨50940, false, false, [], [3, 1]⟩,
        ⟨50939, false, false, [], [3, 1]⟩,
        ⟨50939, false, false, [], [3, 1]⟩,
        ⟨50936, false, false, [], [1]⟩,
        ⟨51115, false, false, [], [1]⟩,
        ⟨50935, false, false, [], [1]⟩,
        ⟨50935, false, false, [], [1]⟩,
        ⟨50933, false, false, [], []⟩,
        ⟨51116, false, false, [], []⟩,
        ⟨50932, false, false, [], []⟩,
        ⟨50932, false, false, [], []⟩
      ]⟩,
    ⟨[88531], [88531], .contexts []⟩,
    ⟨[88529], [88529], .contexts []⟩,
    ⟨[88527], [88527], .contexts []⟩,
    ⟨[88525], [88525], .contexts []⟩,
    ⟨[88523], [88523], .contexts []⟩,
    ⟨[
      88605, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9
    ], [88523], .contexts [
        ⟨51117, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨50930, false, false, [], [13, 1, 11, 9]⟩,
        ⟨51118, false, false, [], [13, 1, 11, 9]⟩,
        ⟨50929, false, false, [], [13, 1, 11, 9]⟩,
        ⟨50929, false, false, [], [13, 1, 11, 9]⟩,
        ⟨50927, false, false, [], [1, 11, 9]⟩,
        ⟨51119, false, false, [], [1, 11, 9]⟩,
        ⟨50926, false, false, [], [1, 11, 9]⟩,
        ⟨50926, false, false, [], [1, 11, 9]⟩,
        ⟨50924, false, false, [], [11, 9]⟩,
        ⟨51120, false, false, [], [11, 9]⟩,
        ⟨50923, false, false, [], [11, 9]⟩,
        ⟨50923, false, false, [], [11, 9]⟩,
        ⟨50921, false, false, [], [9]⟩,
        ⟨51121, false, false, [], [9]⟩,
        ⟨50920, false, false, [], [9]⟩,
        ⟨50920, false, false, [], [9]⟩,
        ⟨50918, false, false, [], []⟩,
        ⟨51122, false, false, [], []⟩,
        ⟨50917, false, false, [], []⟩,
        ⟨50917, false, false, [], []⟩
      ]⟩,
    ⟨[88521], [88521], .contexts []⟩,
    ⟨[88521, 5], [88519], .contexts [
        ⟨50911, false, false, [], []⟩
      ]⟩,
    ⟨[88519], [88519], .contexts []⟩,
    ⟨[88517], [88517], .contexts []⟩,
    ⟨[88515], [88515], .contexts []⟩,
    ⟨[88513], [88513], .contexts []⟩,
    ⟨[
      88605, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15
    ], [88513], .contexts [
        ⟨51123, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨50915, false, false, [], [5, 3, 1, 15]⟩,
        ⟨51124, false, false, [], [5, 3, 1, 15]⟩,
        ⟨50914, false, false, [], [5, 3, 1, 15]⟩,
        ⟨50914, false, false, [], [5, 3, 1, 15]⟩,
        ⟨51125, false, false, [], [3, 1, 15]⟩,
        ⟨51126, false, false, [], [3, 1, 15]⟩,
        ⟨50910, false, false, [], [3, 1, 15]⟩,
        ⟨50910, false, false, [], [3, 1, 15]⟩,
        ⟨50907, false, false, [], [1, 15]⟩,
        ⟨51127, false, false, [], [1, 15]⟩,
        ⟨50906, false, false, [], [1, 15]⟩,
        ⟨50906, false, false, [], [1, 15]⟩,
        ⟨50903, false, false, [], [15]⟩,
        ⟨51128, false, false, [], [15]⟩,
        ⟨50902, false, false, [], [15]⟩,
        ⟨50902, false, false, [], [15]⟩,
        ⟨50899, false, false, [], []⟩,
        ⟨51129, false, false, [], []⟩,
        ⟨50898, false, false, [], []⟩,
        ⟨50898, false, false, [], []⟩
      ]⟩,
    ⟨[88505], [88505], .contexts []⟩,
    ⟨[88503], [88503], .contexts []⟩,
    ⟨[
      88605, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1
    ], [88503], .contexts [
        ⟨51130, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨50895, false, false, [], [1, 11, 9, 1]⟩,
        ⟨50894, false, false, [], [1, 11, 9, 1]⟩,
        ⟨50894, false, false, [], [1, 11, 9, 1]⟩,
        ⟨50891, false, false, [], [11, 9, 1]⟩,
        ⟨50890, false, false, [], [11, 9, 1]⟩,
        ⟨50890, false, false, [], [11, 9, 1]⟩,
        ⟨50887, false, false, [], [9, 1]⟩,
        ⟨50886, false, false, [], [9, 1]⟩,
        ⟨50886, false, false, [], [9, 1]⟩,
        ⟨50884, false, false, [], [1]⟩,
        ⟨51131, false, false, [], [1]⟩,
        ⟨50883, false, false, [], [1]⟩,
        ⟨50883, false, false, [], [1]⟩,
        ⟨50881, false, false, [], []⟩,
        ⟨51132, false, false, [], []⟩,
        ⟨50880, false, false, [], []⟩,
        ⟨50880, false, false, [], []⟩
      ]⟩,
    ⟨[88501], [88501], .contexts []⟩,
    ⟨[88501, 3], [88499], .contexts [
        ⟨50874, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 799. -/
def y322TCIndexRaw799 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88499], [88499], .contexts []⟩,
    ⟨[88499, 1], [88497], .contexts [
        ⟨50870, false, false, [], []⟩
      ]⟩,
    ⟨[88497], [88497], .contexts []⟩,
    ⟨[88497, 15], [88495], .contexts [
        ⟨50866, false, false, [], []⟩
      ]⟩,
    ⟨[88495], [88495], .contexts []⟩,
    ⟨[88493], [88493], .contexts []⟩,
    ⟨[
      88605, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [88493], .contexts [
        ⟨51133, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨50878, false, false, [], [3, 1, 15, 13]⟩,
        ⟨51134, false, false, [], [3, 1, 15, 13]⟩,
        ⟨50877, false, false, [], [3, 1, 15, 13]⟩,
        ⟨50877, false, false, [], [3, 1, 15, 13]⟩,
        ⟨51135, false, false, [], [1, 15, 13]⟩,
        ⟨51136, false, false, [], [1, 15, 13]⟩,
        ⟨50873, false, false, [], [1, 15, 13]⟩,
        ⟨50873, false, false, [], [1, 15, 13]⟩,
        ⟨51137, false, false, [], [15, 13]⟩,
        ⟨51138, false, false, [], [15, 13]⟩,
        ⟨50869, false, false, [], [15, 13]⟩,
        ⟨50869, false, false, [], [15, 13]⟩,
        ⟨51139, false, false, [], [13]⟩,
        ⟨51140, false, false, [], [13]⟩,
        ⟨50865, false, false, [], [13]⟩,
        ⟨50865, false, false, [], [13]⟩,
        ⟨50862, false, false, [], []⟩,
        ⟨51141, false, false, [], []⟩,
        ⟨50861, false, false, [], []⟩,
        ⟨50861, false, false, [], []⟩
      ]⟩,
    ⟨[88489], [88489], .contexts []⟩,
    ⟨[
      88605, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5
    ], [22879, 88485], .contexts [
        ⟨51142, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨50858, false, false, [], [11, 9, 1, 5]⟩,
        ⟨50857, false, false, [], [11, 9, 1, 5]⟩,
        ⟨50857, false, false, [], [11, 9, 1, 5]⟩,
        ⟨50854, false, false, [], [9, 1, 5]⟩,
        ⟨51143, false, false, [], [9, 1, 5]⟩,
        ⟨50853, false, false, [], [9, 1, 5]⟩,
        ⟨50853, false, false, [], [9, 1, 5]⟩,
        ⟨50850, false, false, [], [1, 5]⟩,
        ⟨50842, false, false, [], [1, 5]⟩,
        ⟨50843, false, false, [], [1, 5]⟩,
        ⟨50843, false, false, [], [1, 5]⟩,
        ⟨50847, false, false, [], [5]⟩,
        ⟨50844, false, false, [], [5]⟩,
        ⟨50845, false, false, [], [5]⟩,
        ⟨50845, false, false, [], [5]⟩,
        ⟨50841, false, false, [22879], []⟩,
        ⟨50833, false, false, [], []⟩,
        ⟨50834, false, false, [], []⟩,
        ⟨50835, false, false, [], []⟩
      ]⟩,
    ⟨[
      88605, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13
    ], [22879, 88477], .contexts [
        ⟨51144, false, false, [], [3, 1, 15, 13]⟩,
        ⟨50827, true, false, [22879], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [22879, 88483], [1, 15, 13]⟩,
        ⟨50830, false, false, [], [1, 15, 13]⟩,
        ⟨50831, false, false, [], [1, 15, 13]⟩,
        ⟨50832, false, false, [], [1, 15, 13]⟩,
        ⟨50825, false, false, [22879], [15, 13]⟩,
        ⟨50817, false, false, [], [15, 13]⟩,
        ⟨50818, false, false, [], [15, 13]⟩,
        ⟨50819, false, false, [], [15, 13]⟩,
        ⟨50813, true, false, [22879], [15, 13]⟩,
        ⟨1, false, false, [22879, 88479], [13]⟩,
        ⟨50805, false, false, [22879], [13]⟩,
        ⟨50806, false, false, [], [13]⟩,
        ⟨50807, false, false, [], [13]⟩,
        ⟨50808, false, false, [], [13]⟩,
        ⟨50803, false, false, [22879], []⟩,
        ⟨50791, false, false, [], []⟩,
        ⟨50792, false, false, [], []⟩,
        ⟨50793, false, false, [], []⟩
      ]⟩,
    ⟨[22881], [22879, 18663], .source 11505⟩,
    ⟨[22883], [22881, 22875], .source 11506⟩,
    ⟨[
      88605, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5
    ], [22883, 88471], .contexts [
        ⟨51145, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨50783, false, false, [22879], [11, 9, 1, 5]⟩,
        ⟨50765, false, false, [22879], [9, 1, 5]⟩,
        ⟨50744, false, false, [22879], [1, 5]⟩,
        ⟨34515, false, false, [22879], [5]⟩,
        ⟨51146, true, false, [], [85945, 5]⟩,
        ⟨50733, false, false, [22881], []⟩,
        ⟨51147, true, false, [], [88471]⟩
      ]⟩,
    ⟨[22885], [22883, 1075], .source 11507⟩,
    ⟨[22887], [22885, 2575], .source 11508⟩,
    ⟨[22889], [22887, 15591], .source 11509⟩,
    ⟨[
      88605, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1
    ], [22889, 82829], .contexts [
        ⟨51148, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨50720, false, false, [22883], [1, 15, 13, 1]⟩,
        ⟨20652, false, false, [22883], [15, 13, 1]⟩,
        ⟨51149, true, false, [], [83343, 15, 13, 1]⟩,
        ⟨20667, false, false, [22885], [13, 1]⟩,
        ⟨51150, true, false, [], [83343, 13, 1]⟩,
        ⟨20663, false, false, [22887], [1]⟩,
        ⟨17189, false, false, [22887], []⟩,
        ⟨51151, true, false, [], [82829]⟩
      ]⟩,
    ⟨[22891], [22889, 15301], .source 11510⟩,
    ⟨[22893], [22891, 15945], .source 11511⟩,
    ⟨[22895], [22893, 8905], .source 11512⟩,
    ⟨[
      88605, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [22895, 82825], .contexts [
        ⟨51152, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨17196, false, false, [22889], [9, 1, 5, 3]⟩,
        ⟨19379, false, false, [22889], [1, 5, 3]⟩,
        ⟨19366, false, false, [22889], [5, 3]⟩,
        ⟨51153, true, false, [], [83157, 5, 3]⟩,
        ⟨19315, false, false, [22891], [3]⟩,
        ⟨51154, true, false, [], [82825, 3]⟩,
        ⟨17127, false, false, [22893], []⟩,
        ⟨51155, true, false, [], [82825]⟩
      ]⟩,
    ⟨[22897], [22895, 14713], .source 11513⟩,
    ⟨[22899], [22897, 15315], .source 11514⟩,
    ⟨[22901], [22899, 15879], .source 11515⟩,
    ⟨[22903], [22901, 245], .source 11516⟩,
    ⟨[
      88605, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11
    ], [22903, 82765], .contexts [
        ⟨51156, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨17120, false, false, [22895], [15, 13, 1, 11]⟩,
        ⟨51157, true, false, [], [78839, 15, 13, 1, 11]⟩,
        ⟨15462, false, false, [22897], [13, 1, 11]⟩,
        ⟨51158, true, false, [], [82691, 13, 1, 11]⟩,
        ⟨18948, false, false, [22899], [1, 11]⟩,
        ⟨51159, true, false, [], [83129, 1, 11]⟩,
        ⟨18935, false, false, [22901], [11]⟩,
        ⟨16367, false, false, [22901], []⟩,
        ⟨51160, true, false, [], [82765]⟩
      ]⟩,
    ⟨[22905], [22903, 277], .source 11517⟩,
    ⟨[22907], [22905, 15883], .source 11518⟩,
    ⟨[88607, 3], [88607, 3], .contexts []⟩,
    ⟨[88607, 3], [22907, 83137], .contexts [
        ⟨51164, false, false, [], []⟩,
        ⟨51063, true, false, [], [3]⟩,
        ⟨51063, true, false, [], [3]⟩,
        ⟨51062, true, false, [], [3]⟩,
        ⟨1908, false, false, [88605], []⟩,
        ⟨1909, false, false, [88605], []⟩,
        ⟨51161, false, false, [], [9, 1, 5]⟩,
        ⟨16363, false, false, [22903], [1, 5]⟩,
        ⟨51162, true, false, [], [82765, 1, 5]⟩,
        ⟨18936, false, false, [22905], [5]⟩,
        ⟨19044, false, false, [22905], []⟩,
        ⟨51163, true, false, [], [83137]⟩,
        ⟨19047, false, false, [22907], []⟩,
        ⟨13, true, false, [], [22907, 83137]⟩
      ]⟩,
    ⟨[22909], [22906], .source 11519⟩,
    ⟨[83137, 3], [22909, 88607], .contexts [
        ⟨51165, true, false, [22906], [3]⟩,
        ⟨20, false, false, [22906, 88607], []⟩,
        ⟨51166, true, false, [], [88607]⟩
      ]⟩,
    ⟨[22907, 83137], [22907, 83137], .contexts []⟩,
    ⟨[22911], [22907, 15403], .source 11520⟩,
    ⟨[22913], [22911, 15397], .source 11521⟩,
    ⟨[22915], [22913, 15401], .source 11522⟩,
    ⟨[88605, 3], [88605, 3], .contexts []⟩,
    ⟨[88605, 3], [22915, 83137], .contexts [
        ⟨51172, false, false, [], []⟩,
        ⟨51061, true, false, [], [3]⟩,
        ⟨51061, true, false, [], [3]⟩,
        ⟨51061, true, false, [], [3]⟩,
        ⟨8, true, false, [88605], [3]⟩,
        ⟨51060, false, false, [], [1, 3]⟩,
        ⟨1098, false, false, [88607], []⟩,
        ⟨1100, false, false, [88607], []⟩,
        ⟨51164, false, false, [], [1, 3, 1]⟩,
        ⟨51165, false, false, [], [1, 3, 1]⟩,
        ⟨51168, false, false, [], [1, 3, 1]⟩,
        ⟨51168, false, false, [], [1, 3, 1]⟩,
        ⟨19034, false, false, [22907], [3, 1]⟩,
        ⟨51169, true, false, [], [83125, 3, 1]⟩,
        ⟨18911, false, false, [22911], [1]⟩,
        ⟨51170, true, false, [], [83125, 1]⟩,
        ⟨19035, false, false, [22913], []⟩,
        ⟨51171, true, false, [], [83137]⟩,
        ⟨19047, false, false, [22915], []⟩
      ]⟩,
    ⟨[88605, 3], [22915, 83137], .contexts [
        ⟨51173, false, false, [], []⟩,
        ⟨13, true, false, [], [22915, 83137]⟩
      ]⟩,
    ⟨[22917], [22914], .source 11523⟩,
    ⟨[83137, 3], [22909, 88607], .contexts [
        ⟨51167, false, false, [], []⟩
      ]⟩,
    ⟨[22909, 88607], [22909, 88607], .contexts []⟩,
    ⟨[22919], [22907, 22917], .source 11524⟩,
    ⟨[88607], [22919, 88605], .contexts [
        ⟨51177, true, false, [22908], []⟩,
        ⟨51177, true, false, [22908], []⟩,
        ⟨51176, true, false, [22908], []⟩,
        ⟨51174, true, false, [22908, 22914], [3]⟩,
        ⟨20, false, false, [22908, 22914, 88605], []⟩,
        ⟨51175, true, false, [22908], [88605]⟩,
        ⟨51166, false, true, [], [22917, 88605]⟩,
        ⟨51178, true, false, [], [88605]⟩
      ]⟩,
    ⟨[22919, 88605], [22919, 88605], .contexts []⟩,
    ⟨[88607], [22919, 88605], .contexts [
        ⟨51179, false, false, [], []⟩,
        ⟨51180, false, false, [], []⟩
      ]⟩,
    ⟨[88603, 1], [88603, 1], .contexts []⟩,
    ⟨[22921], [22918], .source 11525⟩,
    ⟨[22918], [22918], .contexts []⟩,
    ⟨[22921], [22918], .contexts [
        ⟨51183, false, false, [], []⟩,
        ⟨51184, false, false, [], []⟩,
        ⟨51184, false, false, [], []⟩
      ]⟩,
    ⟨[88603, 1], [22921, 88603], .contexts [
        ⟨51182, false, false, [], []⟩,
        ⟨51058, true, false, [], [1]⟩,
        ⟨51180, true, false, [22918], [15, 1]⟩,
        ⟨51180, true, false, [22918], [15, 1]⟩,
        ⟨51181, true, false, [22918], [15, 1]⟩,
        ⟨51062, true, false, [22918], [15, 1]⟩,
        ⟨3040, false, false, [22918, 88605], []⟩,
        ⟨10, false, false, [22918, 88605], []⟩,
        ⟨51065, false, false, [22918], []⟩,
        ⟨51185, true, false, [], [88603]⟩
      ]⟩,
    ⟨[22915, 83137], [22915, 83137], .contexts []⟩,
    ⟨[22915, 83137], [22915, 83137], .contexts []⟩,
    ⟨[88605, 3], [22915, 83137], .contexts [
        ⟨51172, false, false, [], []⟩,
        ⟨51174, false, false, [], []⟩,
        ⟨51187, false, false, [], []⟩,
        ⟨51188, false, false, [], []⟩,
        ⟨51188, false, false, [], []⟩
      ]⟩,
    ⟨[22915, 84965], [22915, 84965], .contexts []⟩,
    ⟨[88605], [88605], .contexts []⟩,
    ⟨[88605], [88605], .contexts []⟩,
    ⟨[22914], [22914], .contexts []⟩,
    ⟨[84965, 7], [22917, 88605], .contexts [
        ⟨51190, true, false, [22914], [7]⟩,
        ⟨29488, true, false, [], [7]⟩,
        ⟨19027, true, false, [], [3, 7]⟩,
        ⟨51189, true, false, [22914], [7, 3, 7]⟩,
        ⟨18135, false, false, [22914, 88605], []⟩,
        ⟨51191, false, false, [22914], []⟩,
        ⟨51192, false, false, [22914], []⟩,
        ⟨51193, true, false, [], [88605]⟩,
        ⟨51193, true, false, [], [88605]⟩,
        ⟨51175, true, false, [], [88605]⟩
      ]⟩,
    ⟨[22923], [22915, 18023], .source 11526⟩,
    ⟨[85237, 9], [85237, 9], .contexts []⟩,
    ⟨[22925], [22922], .source 11527⟩,
    ⟨[22922], [22922], .contexts []⟩,
    ⟨[85237, 9], [22925, 88605], .contexts [
        ⟨51196, false, false, [], []⟩,
        ⟨51195, false, false, [22922], [85237, 9]⟩,
        ⟨30869, true, false, [22922, 22915], [9]⟩,
        ⟨19131, true, false, [22922, 22915], [3, 9]⟩,
        ⟨51189, true, false, [22922], [9, 3, 9]⟩,
        ⟨1612, false, false, [22922, 88605], []⟩,
        ⟨51191, false, false, [22922], []⟩,
        ⟨51192, false, false, [22922], []⟩,
        ⟨51198, true, false, [], [88605]⟩,
        ⟨51198, true, false, [], [88605]⟩,
        ⟨51197, true, false, [], [88605]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 800. -/
def y322TCIndexRaw800 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[22927], [22915, 15289], .source 11528⟩,
    ⟨[22929], [22909, 22919], .source 11529⟩,
    ⟨[22931], [22927, 22929], .source 11530⟩,
    ⟨[22933], [22930], .source 11531⟩,
    ⟨[22930], [22930], .contexts []⟩,
    ⟨[22935], [22915, 1075], .source 11532⟩,
    ⟨[22937], [22935, 22929], .source 11533⟩,
    ⟨[22937, 88603], [22937, 88603], .contexts []⟩,
    ⟨[22937], [22937], .contexts []⟩,
    ⟨[88605], [22937, 88603], .contexts [
        ⟨51192, false, false, [], []⟩,
        ⟨150, true, false, [88605], []⟩,
        ⟨51189, false, false, [], [15, 3, 15]⟩,
        ⟨19059, false, false, [22915], [3, 15]⟩,
        ⟨51205, true, false, [], [83137, 3, 15]⟩,
        ⟨51167, false, false, [22935], [15]⟩,
        ⟨51181, false, false, [22935, 22909], [15]⟩,
        ⟨51201, true, false, [22935], [88605, 15]⟩,
        ⟨51206, true, false, [], [88605, 15]⟩,
        ⟨51058, false, false, [22937], []⟩,
        ⟨51207, false, false, [], []⟩,
        ⟨51208, true, false, [], [88603]⟩
      ]⟩,
    ⟨[22919, 88605], [22919, 22937, 88603], .contexts [
        ⟨51209, false, false, [22919], []⟩
      ]⟩,
    ⟨[22939], [22919, 22937], .source 11534⟩,
    ⟨[22941], [22936], .source 11535⟩,
    ⟨[22943], [22941, 22915], .source 11536⟩,
    ⟨[22943], [22936, 22915], .contexts [
        ⟨51213, false, false, [], []⟩,
        ⟨51212, false, false, [], [22915]⟩
      ]⟩,
    ⟨[88603, 3], [22943, 83137], .contexts [
        ⟨51209, true, false, [22936], [3]⟩,
        ⟨51174, false, false, [22936], []⟩,
        ⟨51187, false, false, [22936], []⟩,
        ⟨51214, true, false, [], [83137]⟩
      ]⟩,
    ⟨[88603, 7], [22943, 84965], .contexts [
        ⟨51209, true, false, [22936], [7]⟩,
        ⟨51194, true, false, [22936, 22916], [7]⟩,
        ⟨38, false, false, [22936, 22916, 84965], []⟩,
        ⟨51175, false, true, [22936], [84965]⟩,
        ⟨51190, false, false, [22936], []⟩,
        ⟨51214, true, false, [], [84965]⟩
      ]⟩,
    ⟨[22945], [22941, 22923], .source 11537⟩,
    ⟨[88603, 9], [22945, 85237], .contexts [
        ⟨51209, true, false, [22936], [9]⟩,
        ⟨51199, true, false, [22936, 22924], [9]⟩,
        ⟨46, false, false, [22936, 22924, 85237], []⟩,
        ⟨51197, false, true, [22936], [85237]⟩,
        ⟨51212, true, false, [], [22923, 85237]⟩,
        ⟨51217, true, false, [], [85237]⟩
      ]⟩,
    ⟨[88605], [22937, 88603], .contexts [
        ⟨51209, false, false, [], []⟩
      ]⟩,
    ⟨[88605], [22937, 88603], .contexts [
        ⟨51219, false, false, [], []⟩,
        ⟨51207, false, false, [], []⟩
      ]⟩,
    ⟨[22947], [22941, 22933], .source 11538⟩,
    ⟨[22949], [22947, 22937], .source 11539⟩,
    ⟨[88603, 11], [22949, 88603], .contexts [
        ⟨51209, true, false, [22936], [11]⟩,
        ⟨51202, false, false, [22936, 22930], [88605, 11]⟩,
        ⟨51201, false, false, [22936, 22930, 22927], [88605, 11]⟩,
        ⟨51181, true, false, [22936, 22930, 22927, 22909], [11]⟩,
        ⟨51167, true, false, [22936, 22930, 22927], [11]⟩,
        ⟨51200, false, false, [22936, 22930], [83137, 3, 11]⟩,
        ⟨19048, true, false, [22936, 22930, 22915], [3, 11]⟩,
        ⟨51189, true, false, [22936, 22930], [11, 3, 11]⟩,
        ⟨1693, false, false, [22936, 22930, 88605], []⟩,
        ⟨51191, false, false, [22936, 22930], []⟩,
        ⟨51192, false, false, [22936, 22930], []⟩,
        ⟨51204, true, false, [22936], [88605]⟩,
        ⟨51204, true, false, [22936], [88605]⟩,
        ⟨51203, true, false, [22936], [88605]⟩,
        ⟨51220, false, false, [22936, 22933], []⟩,
        ⟨51212, true, false, [], [22933, 22937, 88603]⟩,
        ⟨51221, true, false, [], [22937, 88603]⟩,
        ⟨51222, true, false, [], [88603]⟩
      ]⟩,
    ⟨[22951], [22909, 22939], .source 11540⟩,
    ⟨[88601, 3], [88601, 3], .contexts []⟩,
    ⟨[22953], [22950], .source 11541⟩,
    ⟨[22955], [22953, 15319], .source 11542⟩,
    ⟨[88601, 3], [22955, 82693], .contexts [
        ⟨51225, false, false, [], []⟩,
        ⟨51054, true, false, [], [3]⟩,
        ⟨51224, false, false, [22950], [88603, 13, 3]⟩,
        ⟨51211, false, false, [22950, 22909], [88603, 13, 3]⟩,
        ⟨51210, true, false, [22950, 22909], [13, 3]⟩,
        ⟨51181, true, false, [22950, 22909], [13, 3]⟩,
        ⟨51176, true, false, [22950], [13, 3]⟩,
        ⟨514, false, false, [22950, 83137], []⟩,
        ⟨64, false, false, [22950, 83137], []⟩,
        ⟨19053, false, false, [22950], []⟩,
        ⟨19056, false, false, [22950], []⟩,
        ⟨19050, false, false, [22950], []⟩,
        ⟨19052, false, false, [22950], []⟩,
        ⟨19052, false, false, [22950], []⟩,
        ⟨15481, false, false, [22950, 15319], []⟩,
        ⟨51226, true, false, [], [15319, 82693]⟩,
        ⟨51227, true, false, [], [82693]⟩
      ]⟩,
    ⟨[22957], [22954], .source 11543⟩,
    ⟨[82693, 3], [22957, 88601], .contexts [
        ⟨51228, true, false, [22954], [3]⟩,
        ⟨20, false, false, [22954, 88601], []⟩,
        ⟨51229, true, false, [], [88601]⟩
      ]⟩,
    ⟨[22921, 88603], [22921, 88603], .contexts []⟩,
    ⟨[22921, 88603], [22921, 88603], .contexts []⟩,
    ⟨[88603, 1], [22921, 88603], .contexts [
        ⟨51182, false, false, [], []⟩,
        ⟨51186, false, false, [], []⟩,
        ⟨51231, false, false, [], []⟩,
        ⟨51232, false, false, [], []⟩,
        ⟨51232, false, false, [], []⟩
      ]⟩,
    ⟨[88603, 13], [88601], .contexts [
        ⟨51066, false, false, [], []⟩,
        ⟨51067, false, false, [], []⟩,
        ⟨51053, false, false, [], []⟩,
        ⟨51053, false, false, [], []⟩
      ]⟩,
    ⟨[88599, 13], [88599, 13], .contexts []⟩,
    ⟨[22920], [22920], .contexts []⟩,
    ⟨[22919], [22920], .contexts [
        ⟨51183, true, true, [], []⟩,
        ⟨51236, false, false, [], []⟩,
        ⟨51236, false, false, [], []⟩
      ]⟩,
    ⟨[22959], [22925, 22937], .source 11544⟩,
    ⟨[19505, 86803], [19505, 86803], .contexts []⟩,
    ⟨[22961], [22958], .source 11545⟩,
    ⟨[22963], [22961, 19505], .source 11546⟩,
    ⟨[88601, 9], [22963, 86803], .contexts [
        ⟨51054, true, false, [], [9]⟩,
        ⟨51238, false, false, [22958], [88603, 13, 9]⟩,
        ⟨51220, true, false, [22958, 22925], [13, 9]⟩,
        ⟨51199, true, false, [22958], [13, 9]⟩,
        ⟨51196, true, false, [22958], [13, 9]⟩,
        ⟨511, false, false, [22958, 85237], []⟩,
        ⟨64, false, false, [22958, 85237], []⟩,
        ⟨39044, false, false, [22958], []⟩,
        ⟨51239, false, false, [22958], []⟩,
        ⟨51239, false, false, [22958], []⟩,
        ⟨42415, false, false, [22958, 19505], []⟩,
        ⟨51240, true, false, [], [19505, 86803]⟩,
        ⟨51241, true, false, [], [86803]⟩
      ]⟩,
    ⟨[22965], [22962], .source 11547⟩,
    ⟨[22949, 88603], [22949, 88603], .contexts []⟩,
    ⟨[22949, 88603], [22949, 88603], .contexts []⟩,
    ⟨[88603, 11], [22949, 88603], .contexts [
        ⟨51223, false, false, [], []⟩,
        ⟨51244, false, false, [], []⟩,
        ⟨51245, false, false, [], []⟩,
        ⟨51245, false, false, [], []⟩
      ]⟩,
    ⟨[22949, 88601], [22949, 88601], .contexts []⟩,
    ⟨[22949, 88601], [22949, 88601], .contexts []⟩,
    ⟨[88601, 11], [88601, 11], .contexts []⟩,
    ⟨[88601], [88601], .contexts []⟩,
    ⟨[22967], [22948], .source 11548⟩,
    ⟨[22967], [22967], .contexts []⟩,
    ⟨[22948], [22948], .contexts []⟩,
    ⟨[88601, 11], [22967, 88601], .contexts [
        ⟨51249, false, false, [], []⟩,
        ⟨51248, true, false, [22948], [11]⟩,
        ⟨51247, true, false, [22948], [11]⟩,
        ⟨51054, true, false, [], [11]⟩,
        ⟨51246, true, false, [22948], [13, 11]⟩,
        ⟨619, false, false, [22948, 88603], []⟩,
        ⟨64, false, false, [22948, 88603], []⟩,
        ⟨51234, false, false, [22948], []⟩,
        ⟨51250, false, false, [22948], []⟩,
        ⟨51253, true, false, [], [88601]⟩,
        ⟨51253, true, false, [], [88601]⟩,
        ⟨51251, true, false, [], [88601]⟩,
        ⟨51252, true, false, [], [88601]⟩
      ]⟩,
    ⟨[22955, 82693], [22955, 82693], .contexts []⟩,
    ⟨[22955, 82693], [22955, 82693], .contexts []⟩,
    ⟨[22969], [22955, 15317], .source 11549⟩,
    ⟨[22969, 87941], [22969, 87941], .contexts []⟩,
    ⟨[88601], [88601], .contexts []⟩,
    ⟨[22971], [22968], .source 11550⟩,
    ⟨[22968], [22968], .contexts []⟩,
    ⟨[87941, 15], [22971, 88601], .contexts [
        ⟨51258, true, false, [22968], [15]⟩,
        ⟨47404, true, false, [], [15]⟩,
        ⟨51257, false, false, [22968], [83161, 3, 15]⟩,
        ⟨19392, true, false, [22968, 22955], [3, 15]⟩,
        ⟨51256, true, false, [22968], [15, 3, 15]⟩,
        ⟨51256, true, false, [22968], [15, 3, 15]⟩,
        ⟨51255, true, false, [22968], [15, 3, 15]⟩,
        ⟨51228, true, false, [22968], [15, 3, 15]⟩,
        ⟨51225, true, false, [22968], [15, 3, 15]⟩,
        ⟨1659, false, false, [22968, 88601], []⟩,
        ⟨51259, false, false, [22968], []⟩,
        ⟨51250, false, false, [22968], []⟩,
        ⟨51261, true, false, [], [88601]⟩,
        ⟨51261, true, false, [], [88601]⟩,
        ⟨51260, true, false, [], [88601]⟩
      ]⟩,
    ⟨[88601, 15], [22969, 87941], .contexts [
        ⟨51262, true, false, [22970], [15]⟩,
        ⟨1, false, false, [22970, 87941], []⟩,
        ⟨51260, false, true, [], [87941]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 801. -/
def y322TCIndexRaw801 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[22919, 88599], [22919, 88599], .contexts []⟩,
    ⟨[88599, 13], [22919, 88599], .contexts [
        ⟨51235, false, false, [], []⟩,
        ⟨51235, false, false, [], []⟩,
        ⟨51050, true, false, [], [13]⟩,
        ⟨51054, true, false, [], [1, 13]⟩,
        ⟨51233, true, false, [22920], [13, 1, 13]⟩,
        ⟨919, false, false, [22920, 88603], []⟩,
        ⟨116, false, false, [22920, 88603], []⟩,
        ⟨51234, false, false, [22920], [1]⟩,
        ⟨51068, false, false, [22920], []⟩,
        ⟨51069, false, false, [22920], []⟩,
        ⟨51049, false, false, [22920], []⟩,
        ⟨51049, false, false, [22920], []⟩,
        ⟨51237, true, false, [], [88599]⟩,
        ⟨51264, false, false, [], []⟩,
        ⟨51264, false, false, [], []⟩
      ]⟩,
    ⟨[88597, 13], [88597, 13], .contexts []⟩,
    ⟨[88597], [88597], .contexts []⟩,
    ⟨[88597, 13], [22921, 88597], .contexts [
        ⟨51266, false, false, [], []⟩,
        ⟨51047, true, false, [], [13]⟩,
        ⟨51265, true, false, [22918], [11, 13]⟩,
        ⟨931, false, false, [22918, 88599], []⟩,
        ⟨54, false, false, [22918, 88599], []⟩,
        ⟨51070, false, false, [22918], []⟩,
        ⟨51071, false, false, [22918], []⟩,
        ⟨51046, false, false, [22918], []⟩,
        ⟨51046, false, false, [22918], []⟩,
        ⟨51267, false, false, [22918], []⟩,
        ⟨51185, true, false, [], [88597]⟩
      ]⟩,
    ⟨[22967, 88601], [22967, 88601], .contexts []⟩,
    ⟨[22967, 88601], [22967, 88601], .contexts []⟩,
    ⟨[22967, 88597], [22967, 88597], .contexts []⟩,
    ⟨[22967, 88597], [22967, 88597], .contexts []⟩,
    ⟨[88597, 1], [88597, 1], .contexts []⟩,
    ⟨[22966], [22966], .contexts []⟩,
    ⟨[88597, 1], [22949, 88601], .contexts [
        ⟨51273, false, false, [], []⟩,
        ⟨51272, true, false, [22966], [1]⟩,
        ⟨51271, true, false, [22966], [1]⟩,
        ⟨51047, true, false, [], [1]⟩,
        ⟨51050, true, false, [], [11, 1]⟩,
        ⟨51270, true, false, [22966], [1, 11, 1]⟩,
        ⟨51270, true, false, [22966], [1, 11, 1]⟩,
        ⟨51269, true, false, [22966], [1, 11, 1]⟩,
        ⟨51254, true, false, [22966], [1, 11, 1]⟩,
        ⟨51249, true, false, [22966], [1, 11, 1]⟩,
        ⟨628, false, false, [22966, 88601], []⟩,
        ⟨51259, false, false, [22966], []⟩,
        ⟨51250, false, false, [22966], []⟩,
        ⟨51274, true, false, [], [88601]⟩,
        ⟨51274, true, false, [], [88601]⟩,
        ⟨51251, false, true, [], [88601]⟩
      ]⟩,
    ⟨[88601, 1], [88599], .contexts [
        ⟨51068, false, false, [], []⟩
      ]⟩,
    ⟨[88599], [22967, 88597], .contexts [
        ⟨51049, true, false, [], []⟩,
        ⟨51049, true, false, [], []⟩,
        ⟨51069, true, false, [], []⟩,
        ⟨51276, true, false, [], []⟩,
        ⟨51275, true, false, [22948], [1]⟩,
        ⟨8, false, false, [22948, 88597], []⟩,
        ⟨51251, true, false, [], [88597]⟩,
        ⟨51271, false, false, [], []⟩,
        ⟨51252, true, false, [], [88597]⟩
      ]⟩,
    ⟨[88599], [22967, 88597], .contexts [
        ⟨51277, false, false, [], []⟩,
        ⟨51272, false, false, [], []⟩
      ]⟩,
    ⟨[22921, 88597], [22921, 88597], .contexts []⟩,
    ⟨[22921, 88597], [22921, 88597], .contexts []⟩,
    ⟨[88597, 9], [88595], .contexts [
        ⟨51072, false, false, [], []⟩,
        ⟨51073, false, false, [], []⟩,
        ⟨51042, false, false, [], []⟩,
        ⟨51042, false, false, [], []⟩
      ]⟩,
    ⟨[88597, 8], [88597, 9], .contexts [
        ⟨47, false, false, [88597], []⟩
      ]⟩,
    ⟨[88595, 13], [88595, 13], .contexts []⟩,
    ⟨[88595], [88595], .contexts []⟩,
    ⟨[88595, 13], [22919, 88595], .contexts [
        ⟨51283, false, false, [], []⟩,
        ⟨51043, true, false, [], [13]⟩,
        ⟨51280, true, false, [22920], [9, 13]⟩,
        ⟨51280, true, false, [22920], [9, 13]⟩,
        ⟨51279, true, false, [22920], [9, 13]⟩,
        ⟨51268, true, false, [22920], [9, 13]⟩,
        ⟨51266, true, false, [22920], [9, 13]⟩,
        ⟨942, false, false, [22920, 88597], []⟩,
        ⟨51282, false, false, [22920], []⟩,
        ⟨51281, false, false, [22920], []⟩,
        ⟨51284, false, false, [22920], []⟩,
        ⟨51237, true, false, [], [88595]⟩
      ]⟩,
    ⟨[22973], [22949, 22963], .source 11551⟩,
    ⟨[22973, 87037], [22973, 87037], .contexts []⟩,
    ⟨[22973, 87037], [22973, 87037], .contexts []⟩,
    ⟨[22973, 87037, 1], [88595], .contexts [
        ⟨51288, true, false, [], [1]⟩,
        ⟨51287, true, false, [], [1]⟩,
        ⟨40048, true, false, [22973], [1]⟩,
        ⟨40036, true, false, [22973], [9, 1]⟩,
        ⟨51286, false, false, [], [86803, 1, 9, 1]⟩,
        ⟨51242, true, false, [22949], [1, 9, 1]⟩,
        ⟨51248, true, false, [], [9, 1, 9, 1]⟩,
        ⟨51248, true, false, [], [9, 1, 9, 1]⟩,
        ⟨51247, true, false, [], [9, 1, 9, 1]⟩,
        ⟨51275, true, false, [], [9, 1, 9, 1]⟩,
        ⟨51273, true, false, [], [9, 1, 9, 1]⟩,
        ⟨10332, false, false, [88597], []⟩,
        ⟨51282, false, false, [], []⟩,
        ⟨51281, false, false, [], []⟩
      ]⟩,
    ⟨[87037, 1], [87037, 1], .contexts []⟩,
    ⟨[22975], [22972], .source 11552⟩,
    ⟨[22975], [22972], .contexts [
        ⟨51291, false, false, [], []⟩
      ]⟩,
    ⟨[22975], [22972], .contexts [
        ⟨51292, false, false, [], []⟩
      ]⟩,
    ⟨[22972], [22972], .contexts []⟩,
    ⟨[87037, 1], [22975, 88595], .contexts [
        ⟨51290, false, false, [], []⟩,
        ⟨51289, false, false, [22972], []⟩,
        ⟨51284, false, false, [22972], []⟩,
        ⟨51294, true, false, [], [88595]⟩,
        ⟨51294, true, false, [], [88595]⟩,
        ⟨51293, true, false, [], [88595]⟩
      ]⟩,
    ⟨[22973], [22974], .contexts [
        ⟨51291, true, true, [], []⟩
      ]⟩,
    ⟨[22973], [22973], .contexts []⟩,
    ⟨[88593], [22973, 87037], .contexts [
        ⟨51038, true, false, [], []⟩,
        ⟨51038, true, false, [], []⟩,
        ⟨51075, true, false, [], []⟩,
        ⟨51074, true, false, [], []⟩,
        ⟨51295, true, false, [22974], [1]⟩,
        ⟨8, false, false, [22974, 87037], []⟩,
        ⟨51296, true, false, [], [87037]⟩,
        ⟨51287, false, false, [], []⟩,
        ⟨51297, true, false, [], [87037]⟩
      ]⟩,
    ⟨[87037, 5], [22975, 88591], .contexts [
        ⟨51298, true, false, [22972], [5]⟩,
        ⟨51036, false, false, [22972], []⟩,
        ⟨51077, false, false, [22972], []⟩,
        ⟨51294, true, false, [], [88591]⟩,
        ⟨51294, true, false, [], [88591]⟩,
        ⟨51292, true, false, [], [88591]⟩
      ]⟩,
    ⟨[22975, 88595], [22975, 88595], .contexts []⟩,
    ⟨[22975, 88595], [22975, 88595], .contexts []⟩,
    ⟨[87037, 1], [22975, 88595], .contexts [
        ⟨51290, false, false, [], []⟩,
        ⟨51295, false, false, [], []⟩,
        ⟨51300, false, false, [], []⟩,
        ⟨51301, false, false, [], []⟩,
        ⟨51301, false, false, [], []⟩
      ]⟩,
    ⟨[21631, 87661], [21631, 87661], .contexts []⟩,
    ⟨[21631, 87661], [21631, 87661], .contexts []⟩,
    ⟨[87037, 7], [21631, 87661], .contexts [
        ⟨45708, false, false, [], []⟩,
        ⟨45710, false, false, [], []⟩,
        ⟨51303, false, false, [], []⟩,
        ⟨51304, false, false, [], []⟩,
        ⟨51304, false, false, [], []⟩
      ]⟩,
    ⟨[22973], [22974], .contexts [
        ⟨51297, false, false, [], []⟩,
        ⟨51296, false, false, [], []⟩
      ]⟩,
    ⟨[22977], [22973, 21631], .source 11553⟩,
    ⟨[88595, 7], [22977, 87663], .contexts [
        ⟨51302, true, false, [22974], [7]⟩,
        ⟨104, false, false, [22974, 87037], []⟩,
        ⟨105, false, false, [22974, 87037], []⟩,
        ⟨51305, false, false, [22974], [1]⟩,
        ⟨45009, false, false, [22974, 21631], []⟩,
        ⟨45432, false, false, [22974, 21631], []⟩,
        ⟨51306, true, false, [], [21631, 87663]⟩,
        ⟨51307, true, false, [], [87663]⟩
      ]⟩,
    ⟨[22979], [22976], .source 11554⟩,
    ⟨[87663, 7], [22979, 88595], .contexts [
        ⟨51308, true, false, [22976], [7]⟩,
        ⟨38, false, false, [22976, 88595], []⟩,
        ⟨51309, true, false, [], [88595]⟩
      ]⟩,
    ⟨[88595, 11], [88595, 11], .contexts []⟩,
    ⟨[22974], [22974], .contexts []⟩,
    ⟨[88595, 11], [22973, 87041], .contexts [
        ⟨51311, false, false, [], []⟩,
        ⟨51302, true, false, [22974], [11]⟩,
        ⟨110, false, false, [22974, 87037], []⟩,
        ⟨111, false, false, [22974, 87037], []⟩,
        ⟨40063, false, false, [22974], [1]⟩,
        ⟨40070, false, false, [22974], []⟩,
        ⟨40071, false, false, [22974], []⟩,
        ⟨40072, false, false, [22974], []⟩,
        ⟨40072, false, false, [22974], []⟩,
        ⟨40080, false, false, [22974], []⟩,
        ⟨51312, true, false, [], [87041]⟩,
        ⟨51312, true, false, [], [87041]⟩,
        ⟨51306, true, false, [], [87041]⟩
      ]⟩,
    ⟨[87041, 11], [22975, 88595], .contexts [
        ⟨51313, true, false, [22972], [11]⟩,
        ⟨53, false, false, [22972, 88595], []⟩,
        ⟨51291, true, false, [], [88595]⟩
      ]⟩,
    ⟨[87037, 9], [87035], .contexts [
        ⟨40049, false, false, [], []⟩,
        ⟨40037, false, false, [], []⟩,
        ⟨40038, false, false, [], []⟩,
        ⟨40038, false, false, [], []⟩
      ]⟩,
    ⟨[22975, 88591], [22975, 88591], .contexts []⟩,
    ⟨[22975, 88591], [22975, 88591], .contexts []⟩,
    ⟨[87037, 5], [22975, 88591], .contexts [
        ⟨51299, false, false, [], []⟩,
        ⟨51316, false, false, [], []⟩,
        ⟨51317, false, false, [], []⟩,
        ⟨51317, false, false, [], []⟩
      ]⟩,
    ⟨[87037, 4], [87037, 5], .contexts [
        ⟨29, false, false, [87037], []⟩
      ]⟩,
    ⟨[87033, 9], [87033, 9], .contexts []⟩,
    ⟨[88591], [88591], .contexts []⟩,
    ⟨[22975, 88591], [22975, 88591], .contexts [
        ⟨51321, false, false, [22975], []⟩
      ]⟩,
    ⟨[22975, 88591], [22975, 88591], .contexts [
        ⟨13, true, false, [], [22975, 88591]⟩
      ]⟩,
    ⟨[87033, 9], [22975, 88591], .contexts [
        ⟨51320, false, false, [], []⟩,
        ⟨40000, true, false, [], [9]⟩,
        ⟨40000, true, false, [], [9]⟩,
        ⟨39999, true, false, [], [9]⟩,
        ⟨40042, true, false, [], [9]⟩,
        ⟨51315, true, false, [], [5, 9]⟩,
        ⟨598, false, false, [87037], []⟩,
        ⟨51319, false, false, [], []⟩,
        ⟨51318, false, false, [], []⟩,
        ⟨51322, false, false, [], []⟩,
        ⟨51323, false, false, [], []⟩
      ]⟩,
    ⟨[88591, 9], [22973, 87033], .contexts [
        ⟨51324, true, false, [22974], [9]⟩,
        ⟨46, false, false, [22974, 87033], []⟩,
        ⟨51296, true, false, [], [87033]⟩
      ]⟩,
    ⟨[87037, 13], [20835, 83463], .contexts [
        ⟨42814, false, false, [], []⟩
      ]⟩,
    ⟨[20835, 83463], [20835, 83463], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 802. -/
def y322TCIndexRaw802 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[20835, 83463], [20835, 83463], .contexts []⟩,
    ⟨[87037, 13], [20835, 83463], .contexts [
        ⟨51326, false, false, [], []⟩,
        ⟨51327, false, false, [], []⟩,
        ⟨51328, false, false, [], []⟩,
        ⟨51328, false, false, [], []⟩
      ]⟩,
    ⟨[83465, 13], [83465, 13], .contexts []⟩,
    ⟨[22981], [20837, 22975], .source 11555⟩,
    ⟨[83465, 13], [22981, 88591], .contexts [
        ⟨51330, false, false, [], []⟩,
        ⟨21259, true, false, [], [13]⟩,
        ⟨51329, true, false, [20834], [5, 13]⟩,
        ⟨1136, false, false, [20834, 87037], []⟩,
        ⟨51319, false, false, [20834], []⟩,
        ⟨51318, false, false, [20834], []⟩,
        ⟨51321, false, false, [20834, 22975], []⟩,
        ⟨42811, true, false, [], [22975, 88591]⟩,
        ⟨51331, true, false, [], [88591]⟩
      ]⟩,
    ⟨[22983], [22980], .source 11556⟩,
    ⟨[88591, 13], [22983, 83465], .contexts [
        ⟨51332, true, false, [22980], [13]⟩,
        ⟨59, false, false, [22980, 83465], []⟩,
        ⟨51333, true, false, [], [83465]⟩
      ]⟩,
    ⟨[22985], [21631, 21573], .source 11557⟩,
    ⟨[22987], [22985, 21629], .source 11558⟩,
    ⟨[22989], [22987, 22975], .source 11559⟩,
    ⟨[22991], [22988], .source 11560⟩,
    ⟨[22993], [22991, 22975], .source 11561⟩,
    ⟨[88591, 7], [22993, 88591], .contexts [
        ⟨51337, false, false, [22988], [88591, 7]⟩,
        ⟨51299, true, false, [22988, 22987], [7]⟩,
        ⟨51336, false, false, [22988], [87037, 5, 7]⟩,
        ⟨45711, true, false, [22988, 22985], [5, 7]⟩,
        ⟨51335, false, false, [22988], [87661, 7, 5, 7]⟩,
        ⟨45530, true, false, [22988, 21631], [7, 5, 7]⟩,
        ⟨51305, true, false, [22988], [5, 7, 5, 7]⟩,
        ⟨18796, false, false, [22988, 87037], []⟩,
        ⟨51319, false, false, [22988], []⟩,
        ⟨51318, false, false, [22988], []⟩,
        ⟨51321, false, false, [22988, 22975], []⟩,
        ⟨51338, true, false, [], [22975, 88591]⟩,
        ⟨51339, true, false, [], [88591]⟩
      ]⟩,
    ⟨[22973, 87041], [22973, 87041], .contexts []⟩,
    ⟨[22973, 87041], [22973, 87041], .contexts []⟩,
    ⟨[88595, 11], [22973, 87041], .contexts [
        ⟨51311, false, false, [], []⟩,
        ⟨51313, false, false, [], []⟩,
        ⟨51341, false, false, [], []⟩,
        ⟨51342, false, false, [], []⟩,
        ⟨51342, false, false, [], []⟩
      ]⟩,
    ⟨[22919, 88595], [22919, 88595], .contexts []⟩,
    ⟨[22919, 88595], [22919, 88595], .contexts []⟩,
    ⟨[22995], [22975, 22919], .source 11562⟩,
    ⟨[22997], [22994], .source 11563⟩,
    ⟨[22999], [22975, 22997], .source 11564⟩,
    ⟨[23001], [22998], .source 11565⟩,
    ⟨[87043], [23001, 87041], .contexts [
        ⟨51348, false, false, [22998], [87043]⟩,
        ⟨51291, false, false, [22998], [22997, 87043]⟩,
        ⟨51347, false, false, [22998, 22972], [87043]⟩,
        ⟨53, true, false, [22998, 22972, 22994, 87043], []⟩,
        ⟨40083, true, false, [22998, 22972, 22994], [11, 11]⟩,
        ⟨51343, true, false, [22998, 22972, 22994, 22972], [13, 11, 11]⟩,
        ⟨619, false, false, [22998, 22972, 22994, 22972, 88595], [11]⟩,
        ⟨64, false, false, [22998, 22972, 22994, 22972, 88595], [11]⟩,
        ⟨51283, false, false, [22998, 22972, 22994, 22972], [11]⟩,
        ⟨51285, false, false, [22998, 22972, 22994, 22972], [11]⟩,
        ⟨51344, false, false, [22998, 22972, 22994, 22972], [11]⟩,
        ⟨51345, false, false, [22998, 22972, 22994, 22972], [11]⟩,
        ⟨51345, false, false, [22998, 22972, 22994, 22972], [11]⟩,
        ⟨51284, false, false, [22998, 22972, 22994, 22972, 22919], [11]⟩,
        ⟨51293, true, false, [22998, 22972, 22994], [22919, 88595, 11]⟩,
        ⟨51346, true, false, [22998, 22972, 22994], [88595, 11]⟩,
        ⟨51343, false, false, [22998, 22972], []⟩,
        ⟨51349, true, false, [], [87041]⟩
      ]⟩,
    ⟨[87043], [23001, 87041], .contexts [
        ⟨51350, false, false, [], []⟩
      ]⟩,
    ⟨[23001, 87041], [23001, 87041], .contexts []⟩,
    ⟨[87043], [23001, 87041], .contexts [
        ⟨51351, false, false, [], []⟩,
        ⟨51352, false, false, [], []⟩
      ]⟩,
    ⟨[23001, 82885], [23001, 82885], .contexts []⟩,
    ⟨[22999], [23000], .contexts [
        ⟨51349, true, true, [], []⟩
      ]⟩,
    ⟨[22999], [23000], .contexts [
        ⟨51355, false, false, [], []⟩,
        ⟨13, false, false, [23000], []⟩
      ]⟩,
    ⟨[87045], [23001, 82885], .contexts [
        ⟨51356, false, false, [22998], [87045]⟩,
        ⟨40086, true, false, [22998, 23000], []⟩,
        ⟨40085, true, false, [22998, 23000], []⟩,
        ⟨51353, false, false, [22998, 23000], [15]⟩,
        ⟨40077, false, false, [22998], []⟩,
        ⟨51354, false, false, [22998, 23000], []⟩,
        ⟨51349, true, false, [], [82885]⟩,
        ⟨51354, false, false, [], []⟩
      ]⟩,
    ⟨[23001, 82883], [23001, 82883], .contexts []⟩,
    ⟨[23003], [23001, 16221], .source 11566⟩,
    ⟨[23005], [23002], .source 11567⟩,
    ⟨[83381], [23005, 87049], .contexts [
        ⟨51359, false, false, [23002], [83381]⟩,
        ⟨21121, true, false, [23002, 23001], []⟩,
        ⟨51358, true, false, [23002], [3]⟩,
        ⟨51349, false, false, [23002], [82883, 3]⟩,
        ⟨51358, true, false, [23002, 22998, 23000], [3]⟩,
        ⟨17817, true, false, [23002, 22998], [3]⟩,
        ⟨51357, true, false, [23002, 22998, 23000], [1, 3]⟩,
        ⟨40089, true, false, [23002, 22998, 23000], [3]⟩,
        ⟨51356, true, false, [23002, 22998], [87047, 3]⟩,
        ⟨40090, true, false, [23002], []⟩,
        ⟨13, true, false, [23002], [87049]⟩,
        ⟨51360, true, false, [], [87049]⟩
      ]⟩,
    ⟨[23007], [23003, 7357], .source 11568⟩,
    ⟨[23009], [23006], .source 11569⟩,
    ⟨[23009], [23006], .contexts [
        ⟨51363, false, false, [], []⟩,
        ⟨13, false, false, [23006], []⟩
      ]⟩,
    ⟨[23007], [23008], .contexts [
        ⟨51363, true, true, [], []⟩
      ]⟩,
    ⟨[87051, 1], [23007, 85725], .contexts [
        ⟨51364, false, false, [23008], [87051, 1]⟩,
        ⟨40091, false, false, [23008, 23006], [1]⟩,
        ⟨51361, true, false, [23008, 23006, 23004], [5, 1]⟩,
        ⟨51360, false, true, [23008, 23006], [83381, 5, 1]⟩,
        ⟨33238, false, false, [23008, 23006, 23003], [1]⟩,
        ⟨51362, true, false, [23008, 23006], [85723, 1]⟩,
        ⟨51365, true, false, [], [85723, 1]⟩,
        ⟨33240, false, false, [23007], []⟩
      ]⟩,
    ⟨[23007, 85725], [23007, 85725], .contexts []⟩,
    ⟨[87053], [23007, 85725], .contexts [
        ⟨51364, false, false, [23008], [87053]⟩,
        ⟨40092, false, false, [23008, 23006], []⟩,
        ⟨51366, false, false, [23008, 23006], []⟩,
        ⟨51367, false, false, [23008, 23006], []⟩,
        ⟨51365, true, false, [], [85725]⟩,
        ⟨51367, false, false, [], []⟩
      ]⟩,
    ⟨[23011], [23007, 22271], .source 11570⟩,
    ⟨[23013], [23010], .source 11571⟩,
    ⟨[87209], [23013, 87055], .contexts [
        ⟨51369, false, false, [23010], [87209]⟩,
        ⟨48322, false, false, [23010, 23007], [87209]⟩,
        ⟨46, true, false, [23010, 23007, 22268, 87209], []⟩,
        ⟨48321, false, false, [23010, 23007, 22268], [9]⟩,
        ⟨51368, true, false, [23010], [9]⟩,
        ⟨40094, false, false, [23010], []⟩,
        ⟨13, true, false, [23010], [87055]⟩,
        ⟨51370, true, false, [], [87055]⟩
      ]⟩,
    ⟨[23011], [23012], .contexts [
        ⟨51370, true, true, [], []⟩
      ]⟩,
    ⟨[23012], [23012], .contexts []⟩,
    ⟨[23011], [23012], .contexts [
        ⟨51372, false, false, [], []⟩,
        ⟨51373, false, false, [], []⟩
      ]⟩,
    ⟨[23011], [23012], .contexts [
        ⟨51374, false, false, [], []⟩,
        ⟨51373, false, false, [], []⟩
      ]⟩,
    ⟨[87055, 1], [23011, 87207], .contexts [
        ⟨51371, true, false, [23012], [1]⟩,
        ⟨40640, false, false, [23012], []⟩,
        ⟨40628, false, false, [23012], []⟩,
        ⟨51375, true, false, [], [87207]⟩
      ]⟩,
    ⟨[87055, 5], [23011, 84497], .contexts [
        ⟨51371, true, false, [23012], [5]⟩,
        ⟨40645, false, false, [23012], []⟩,
        ⟨27166, false, false, [23012], []⟩,
        ⟨51375, true, false, [], [84497]⟩
      ]⟩,
    ⟨[23015], [23011, 18323], .source 11572⟩,
    ⟨[23015], [23012, 18323], .contexts [
        ⟨51378, false, false, [], []⟩,
        ⟨51372, false, false, [], [18323]⟩
      ]⟩,
    ⟨[87209], [23013, 87055], .contexts [
        ⟨51371, false, false, [], []⟩
      ]⟩,
    ⟨[87209], [23013, 87055], .contexts [
        ⟨51380, false, false, [], []⟩
      ]⟩,
    ⟨[23017], [23011, 19937], .source 11573⟩,
    ⟨[23019], [23017, 23013], .source 11574⟩,
    ⟨[87055, 3], [23019, 87055], .contexts [
        ⟨51371, true, false, [23012], [3]⟩,
        ⟨40661, false, false, [23012], []⟩,
        ⟨51381, false, false, [23012, 19937], []⟩,
        ⟨51372, true, false, [], [19937, 23013, 87055]⟩,
        ⟨51382, true, false, [], [23013, 87055]⟩,
        ⟨51383, true, false, [], [87055]⟩
      ]⟩,
    ⟨[87055, 13], [23011, 87211], .contexts [
        ⟨51371, true, false, [23012], [13]⟩,
        ⟨40663, false, false, [23012], []⟩,
        ⟨40665, false, false, [23012], []⟩,
        ⟨51375, true, false, [], [87211]⟩
      ]⟩,
    ⟨[23001, 82887], [23001, 82887], .contexts []⟩,
    ⟨[82889], [23001, 82887], .contexts [
        ⟨51356, false, false, [22998], [82889]⟩,
        ⟨18094, true, false, [22998, 23000], []⟩,
        ⟨672, false, false, [22998, 23000], [82889]⟩,
        ⟨40088, true, false, [22998, 23000], []⟩,
        ⟨262, true, false, [22998, 23000, 87043], []⟩,
        ⟨259, true, false, [22998, 23000, 87043], []⟩,
        ⟨40085, false, false, [22998, 23000], [13]⟩,
        ⟨40086, false, false, [22998, 23000], [13]⟩,
        ⟨40087, false, false, [22998, 23000], [13]⟩,
        ⟨40087, false, false, [22998, 23000], [13]⟩,
        ⟨51357, false, false, [22998, 23000], [13]⟩,
        ⟨17819, false, false, [22998], []⟩,
        ⟨51386, false, false, [22998, 23000], []⟩,
        ⟨51349, true, false, [], [82887]⟩
      ]⟩,
    ⟨[23000], [23000], .contexts []⟩,
    ⟨[82887, 1], [22999, 82891], .contexts [
        ⟨51387, true, false, [23000], [1]⟩,
        ⟨17826, false, false, [23000], []⟩,
        ⟨18092, false, false, [23000], []⟩,
        ⟨51388, true, false, [], [82891]⟩,
        ⟨51388, true, false, [], [82891]⟩,
        ⟨51355, true, false, [], [82891]⟩
      ]⟩,
    ⟨[82889], [23001, 82887], .contexts [
        ⟨51387, false, false, [], []⟩
      ]⟩,
    ⟨[82889], [23001, 82887], .contexts [
        ⟨51390, false, false, [], []⟩,
        ⟨51386, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 803. -/
def y322TCIndexRaw803 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[87033, 9], [22975, 88591], .contexts [
        ⟨51324, false, false, [], []⟩
      ]⟩,
    ⟨[22975, 88591, 3], [22975, 88589], .contexts [
        ⟨51032, false, false, [22975], []⟩
      ]⟩,
    ⟨[23021], [22973, 19687], .source 11575⟩,
    ⟨[23023], [23020], .source 11576⟩,
    ⟨[19341, 85213], [23023, 88589], .contexts [
        ⟨37986, true, false, [], []⟩,
        ⟨37986, true, false, [], []⟩,
        ⟨37994, true, false, [], []⟩,
        ⟨30796, true, false, [], []⟩,
        ⟨51394, false, false, [23020], [85217, 9]⟩,
        ⟨51306, false, false, [23020], [19687, 85217, 9]⟩,
        ⟨30788, true, false, [23020, 22974, 19687], [9]⟩,
        ⟨40022, true, false, [23020, 22974], [9]⟩,
        ⟨21, true, false, [23020, 22974, 87033], [9]⟩,
        ⟨479, true, false, [23020, 22974, 87033], [9]⟩,
        ⟨51320, false, false, [23020, 22974], [3, 9, 9]⟩,
        ⟨51392, false, false, [23020, 22974], [3, 9, 9]⟩,
        ⟨51316, false, false, [23020, 22974], [3, 9, 9]⟩,
        ⟨51317, false, false, [23020, 22974], [3, 9, 9]⟩,
        ⟨51317, false, false, [23020, 22974], [3, 9, 9]⟩,
        ⟨51393, false, false, [23020, 22974], [9, 9]⟩,
        ⟨46, false, false, [23020, 88589], []⟩,
        ⟨51395, true, false, [], [88589]⟩
      ]⟩,
    ⟨[23025], [19339, 23023], .source 11577⟩,
    ⟨[23027], [23024], .source 11578⟩,
    ⟨[88589], [23027, 85213], .contexts [
        ⟨51397, false, false, [23024], [88589]⟩,
        ⟨37982, false, false, [23024], [23023, 88589]⟩,
        ⟨51396, true, false, [23024, 19340], []⟩,
        ⟨51398, true, false, [], [85213]⟩
      ]⟩,
    ⟨[23026], [23026], .contexts []⟩,
    ⟨[85213, 3], [23025, 88591], .contexts [
        ⟨51399, true, false, [23026], [3]⟩,
        ⟨51030, false, false, [23026], []⟩,
        ⟨51077, false, false, [23026], []⟩,
        ⟨51400, true, false, [], [88591]⟩,
        ⟨51400, true, false, [], [88591]⟩,
        ⟨51398, false, true, [], [88591]⟩
      ]⟩,
    ⟨[88589], [23027, 85213], .contexts [
        ⟨51399, false, false, [], []⟩
      ]⟩,
    ⟨[88589], [23027, 85213], .contexts [
        ⟨51402, false, false, [], []⟩
      ]⟩,
    ⟨[23029], [23027, 19341], .source 11579⟩,
    ⟨[23031], [23028], .source 11580⟩,
    ⟨[23031], [23028], .contexts [
        ⟨51405, false, false, [], []⟩
      ]⟩,
    ⟨[23029], [23030], .contexts [
        ⟨51405, true, true, [], []⟩
      ]⟩,
    ⟨[88587], [23029, 85213], .contexts [
        ⟨51406, false, false, [23030], [88587]⟩,
        ⟨13, false, false, [23030, 23028], [88587]⟩,
        ⟨51078, true, false, [23030, 23028], []⟩,
        ⟨51028, true, false, [23030, 23028], []⟩,
        ⟨51403, false, false, [23030, 23028], [1]⟩,
        ⟨30459, false, false, [23030, 23028, 23027], []⟩,
        ⟨37987, false, false, [23030, 23028, 23027], []⟩,
        ⟨51404, true, false, [23030, 23028], [85213]⟩,
        ⟨51407, true, false, [], [85213]⟩
      ]⟩,
    ⟨[23028], [23028], .contexts []⟩,
    ⟨[85213, 15], [23031, 88585], .contexts [
        ⟨51408, true, false, [23028], [15]⟩,
        ⟨51025, false, false, [23028], []⟩,
        ⟨51079, false, false, [23028], []⟩,
        ⟨51409, true, false, [], [88585]⟩,
        ⟨51409, true, false, [], [88585]⟩,
        ⟨51406, true, false, [], [88585]⟩
      ]⟩,
    ⟨[87055, 11], [87057], .contexts [
        ⟨40097, false, false, [], []⟩,
        ⟨40259, false, false, [], []⟩,
        ⟨40101, false, false, [], []⟩,
        ⟨40101, false, false, [], []⟩
      ]⟩,
    ⟨[23011, 87207], [23011, 87207], .contexts []⟩,
    ⟨[23011, 87207], [23011, 87207], .contexts []⟩,
    ⟨[87207], [87207], .contexts []⟩,
    ⟨[23011], [23011], .contexts []⟩,
    ⟨[23011], [23011], .contexts []⟩,
    ⟨[87059, 11], [23011, 87207], .contexts [
        ⟨40105, true, false, [], [11]⟩,
        ⟨40105, true, false, [], [11]⟩,
        ⟨40100, true, false, [], [11]⟩,
        ⟨51411, true, false, [], [1, 11]⟩,
        ⟨567, false, false, [87055], []⟩,
        ⟨9, false, false, [87055], []⟩,
        ⟨51376, false, false, [], []⟩,
        ⟨51412, false, false, [], []⟩,
        ⟨51413, false, false, [], []⟩,
        ⟨51413, false, false, [], []⟩,
        ⟨51414, false, false, [23011], []⟩,
        ⟨51416, true, false, [], [87207]⟩,
        ⟨51415, true, false, [], [87207]⟩,
        ⟨13, true, false, [], [23011, 87207]⟩
      ]⟩,
    ⟨[87207, 11], [87205], .contexts [
        ⟨40627, false, false, [], []⟩
      ]⟩,
    ⟨[23013], [23013], .contexts []⟩,
    ⟨[23013], [23013], .contexts []⟩,
    ⟨[87205], [23013, 87059], .contexts [
        ⟨40617, true, false, [], []⟩,
        ⟨40617, true, false, [], []⟩,
        ⟨40616, true, false, [], []⟩,
        ⟨51418, true, false, [], []⟩,
        ⟨51417, true, false, [23010], [11]⟩,
        ⟨53, false, false, [23010, 87059], []⟩,
        ⟨51370, true, false, [], [87059]⟩,
        ⟨51420, true, false, [], [87059]⟩,
        ⟨51419, true, false, [], [87059]⟩
      ]⟩,
    ⟨[87203], [20779, 85263], .contexts [
        ⟨48769, false, false, [], []⟩
      ]⟩,
    ⟨[23033], [23011, 20779], .source 11581⟩,
    ⟨[87059, 9], [23033, 85263], .contexts [
        ⟨51421, true, false, [23012], [9]⟩,
        ⟨40615, false, false, [23012], []⟩,
        ⟨51422, false, false, [23012], []⟩,
        ⟨51374, true, false, [], [20779, 85263]⟩,
        ⟨51423, true, false, [], [85263]⟩
      ]⟩,
    ⟨[23019, 87055], [23019, 87055], .contexts []⟩,
    ⟨[23019, 87057], [23019, 87057], .contexts []⟩,
    ⟨[87057], [87057], .contexts []⟩,
    ⟨[23011, 84497], [23011, 84497], .contexts []⟩,
    ⟨[23011, 84497], [23011, 84497], .contexts []⟩,
    ⟨[23035], [23011, 18275], .source 11582⟩,
    ⟨[87057, 5], [23035, 86809], .contexts [
        ⟨51411, true, false, [], [5]⟩,
        ⟨642, false, false, [87055], []⟩,
        ⟨643, false, false, [87055], []⟩,
        ⟨51377, false, false, [], [11]⟩,
        ⟨51428, false, false, [], [11]⟩,
        ⟨51429, false, false, [], [11]⟩,
        ⟨51429, false, false, [], [11]⟩,
        ⟨39133, false, false, [23011], []⟩,
        ⟨51430, true, false, [], [86809]⟩,
        ⟨39132, false, false, [23035], []⟩,
        ⟨13, true, false, [], [23035, 86809]⟩
      ]⟩,
    ⟨[23037], [23034], .source 11583⟩,
    ⟨[23015, 85623], [23015, 85623], .contexts []⟩,
    ⟨[23039], [23015, 22699], .source 11584⟩,
    ⟨[87057, 7], [23039, 88345], .contexts [
        ⟨51411, true, false, [], [7]⟩,
        ⟨647, false, false, [87055], []⟩,
        ⟨648, false, false, [87055], []⟩,
        ⟨51371, true, false, [23012], [7, 11]⟩,
        ⟨40651, false, false, [23012], [11]⟩,
        ⟨40648, false, false, [23012], [11]⟩,
        ⟨51379, true, false, [], [85623, 11]⟩,
        ⟨51433, false, false, [], [11]⟩,
        ⟨51433, false, false, [], [11]⟩,
        ⟨50028, false, false, [23015], []⟩,
        ⟨51434, true, false, [], [88345]⟩,
        ⟨50013, false, false, [23039], []⟩,
        ⟨13, true, false, [], [23039, 88345]⟩
      ]⟩,
    ⟨[23041], [23038], .source 11585⟩,
    ⟨[82889], [23001, 82887], .contexts [
        ⟨51391, false, false, [], []⟩
      ]⟩,
    ⟨[82887, 1], [22999, 82891], .contexts [
        ⟨51389, false, false, [], []⟩
      ]⟩,
    ⟨[22999, 82891], [22999, 82891], .contexts []⟩,
    ⟨[22999, 82891], [22999, 82891], .contexts []⟩,
    ⟨[82891, 15], [82891, 15], .contexts []⟩,
    ⟨[82891], [82891], .contexts []⟩,
    ⟨[22999, 82891], [22999, 82891], .contexts [
        ⟨51442, false, false, [22999], []⟩
      ]⟩,
    ⟨[22999], [22999], .contexts [
        ⟨13, false, false, [], [22999]⟩
      ]⟩,
    ⟨[22999, 82891], [22999, 82891], .contexts [
        ⟨51444, true, false, [], [82891]⟩
      ]⟩,
    ⟨[82891, 15], [22999, 82891], .contexts [
        ⟨51441, false, false, [], []⟩,
        ⟨51349, true, false, [], [22999, 82891, 15]⟩,
        ⟨51389, true, false, [23001], [15]⟩,
        ⟨51386, true, false, [], [1, 15]⟩,
        ⟨51386, true, false, [], [1, 15]⟩,
        ⟨51437, true, false, [], [1, 15]⟩,
        ⟨36146, true, false, [], [1, 15]⟩,
        ⟨1666, false, false, [82887], []⟩,
        ⟨9, false, false, [82887], []⟩,
        ⟨51438, false, false, [], []⟩,
        ⟨51439, false, false, [], []⟩,
        ⟨51440, false, false, [], []⟩,
        ⟨51440, false, false, [], []⟩,
        ⟨51443, false, false, [], []⟩,
        ⟨51445, false, false, [], []⟩
      ]⟩,
    ⟨[19339, 85217], [19339, 85217], .contexts []⟩,
    ⟨[19339, 85217], [19339, 85217], .contexts []⟩,
    ⟨[85213, 9], [19339, 85217], .contexts [
        ⟨37974, false, false, [], []⟩,
        ⟨37976, false, false, [], []⟩,
        ⟨51447, false, false, [], []⟩,
        ⟨51448, false, false, [], []⟩,
        ⟨51448, false, false, [], []⟩
      ]⟩,
    ⟨[23043], [19339, 19689], .source 11586⟩,
    ⟨[23031, 88585], [23031, 88585], .contexts []⟩,
    ⟨[23031, 88585], [23031, 88585], .contexts []⟩,
    ⟨[85213, 15], [23031, 88585], .contexts [
        ⟨51410, false, false, [], []⟩,
        ⟨51451, false, false, [], []⟩,
        ⟨51452, false, false, [], []⟩,
        ⟨51452, false, false, [], []⟩
      ]⟩,
    ⟨[85213, 14], [85213, 15], .contexts [
        ⟨10, false, false, [85213], []⟩
      ]⟩,
    ⟨[87571, 9], [87571, 9], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 804. -/
def y322TCIndexRaw804 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88585], [88585], .contexts []⟩,
    ⟨[23045], [23042], .source 11587⟩,
    ⟨[23047], [23045, 23031], .source 11588⟩,
    ⟨[87571, 9], [23047, 88585], .contexts [
        ⟨51455, false, false, [], []⟩,
        ⟨51450, false, false, [23042], [87571, 9]⟩,
        ⟨44250, true, false, [23042, 19339], [9]⟩,
        ⟨51449, true, false, [23042], [15, 9]⟩,
        ⟨935, false, false, [23042, 85213], []⟩,
        ⟨51454, false, false, [23042], []⟩,
        ⟨51453, false, false, [23042], []⟩,
        ⟨51456, false, false, [23042, 23031], []⟩,
        ⟨51457, true, false, [], [23031, 88585]⟩,
        ⟨51458, true, false, [], [88585]⟩
      ]⟩,
    ⟨[23049], [23046], .source 11589⟩,
    ⟨[88585, 9], [23049, 87571], .contexts [
        ⟨51459, true, false, [23046], [9]⟩,
        ⟨46, false, false, [23046, 87571], []⟩,
        ⟨51460, true, false, [], [87571]⟩
      ]⟩,
    ⟨[23051], [19341, 23031], .source 11590⟩,
    ⟨[88585, 1], [88585, 1], .contexts []⟩,
    ⟨[23053], [23050], .source 11591⟩,
    ⟨[23055], [23053, 23031], .source 11592⟩,
    ⟨[88585, 1], [23055, 88585], .contexts [
        ⟨51463, false, false, [], []⟩,
        ⟨51462, false, false, [23050], [88585, 1]⟩,
        ⟨51410, true, false, [23050, 19341], [1]⟩,
        ⟨37995, true, false, [23050], [15, 1]⟩,
        ⟨3040, false, false, [23050, 85213], []⟩,
        ⟨51454, false, false, [23050], []⟩,
        ⟨51453, false, false, [23050], []⟩,
        ⟨51456, false, false, [23050, 23031], []⟩,
        ⟨51464, true, false, [], [23031, 88585]⟩,
        ⟨51465, true, false, [], [88585]⟩
      ]⟩,
    ⟨[18011, 85213], [18011, 85213], .contexts []⟩,
    ⟨[18011, 85213], [18011, 85213], .contexts []⟩,
    ⟨[23057], [18011, 23031], .source 11593⟩,
    ⟨[88585, 7], [88585, 7], .contexts []⟩,
    ⟨[23059], [23056], .source 11594⟩,
    ⟨[23061], [23059, 23031], .source 11595⟩,
    ⟨[88585, 7], [23061, 88585], .contexts [
        ⟨51470, false, false, [], []⟩,
        ⟨51469, false, false, [23056], [88585, 7]⟩,
        ⟨51410, true, false, [23056, 18011], [7]⟩,
        ⟨51468, true, false, [23056], [15, 7]⟩,
        ⟨51468, true, false, [23056], [15, 7]⟩,
        ⟨51467, true, false, [23056], [15, 7]⟩,
        ⟨30828, true, false, [23056], [15, 7]⟩,
        ⟨30827, true, false, [23056], [15, 7]⟩,
        ⟨18155, false, false, [23056, 85213], []⟩,
        ⟨51454, false, false, [23056], []⟩,
        ⟨51453, false, false, [23056], []⟩,
        ⟨51456, false, false, [23056, 23031], []⟩,
        ⟨51471, true, false, [], [23031, 88585]⟩,
        ⟨51472, true, false, [], [88585]⟩
      ]⟩,
    ⟨[23063], [19343, 20933], .source 11596⟩,
    ⟨[23065], [23063, 21163], .source 11597⟩,
    ⟨[23067], [23065, 18505], .source 11598⟩,
    ⟨[23069], [23066], .source 11599⟩,
    ⟨[23071], [23069, 23031], .source 11600⟩,
    ⟨[83095, 13], [23071, 88585], .contexts [
        ⟨51476, false, false, [23066], [83095, 13]⟩,
        ⟨33841, true, false, [23066, 23065], [13]⟩,
        ⟨51475, false, false, [23066], [85825, 15, 13]⟩,
        ⟨44347, true, false, [23066, 23063], [15, 13]⟩,
        ⟨40171, true, false, [23066, 23063], [15, 13]⟩,
        ⟨51474, false, false, [23066], [87097, 13, 15, 13]⟩,
        ⟨43123, true, false, [23066, 19343], [13, 15, 13]⟩,
        ⟨38007, true, false, [23066], [15, 13, 15, 13]⟩,
        ⟨9624, false, false, [23066, 85213], []⟩,
        ⟨51454, false, false, [23066], []⟩,
        ⟨51453, false, false, [23066], []⟩,
        ⟨51456, false, false, [23066, 23031], []⟩,
        ⟨51477, true, false, [], [23031, 88585]⟩,
        ⟨51478, true, false, [], [88585]⟩
      ]⟩,
    ⟨[23073], [23070], .source 11601⟩,
    ⟨[23073, 83095], [23073, 83095], .contexts []⟩,
    ⟨[23073], [23073], .contexts []⟩,
    ⟨[23073], [23073], .contexts []⟩,
    ⟨[88583], [23073, 83095], .contexts [
        ⟨51020, true, false, [], []⟩,
        ⟨51020, true, false, [], []⟩,
        ⟨51081, true, false, [], []⟩,
        ⟨51080, true, false, [], []⟩,
        ⟨51479, true, false, [23070], [13]⟩,
        ⟨59, false, false, [23070, 83095], []⟩,
        ⟨51480, true, false, [], [83095]⟩,
        ⟨51481, false, false, [], []⟩,
        ⟨51483, true, false, [], [83095]⟩,
        ⟨51482, true, false, [], [83095]⟩
      ]⟩,
    ⟨[23073, 83095], [23073, 83095], .contexts []⟩,
    ⟨[88583], [23073, 83095], .contexts [
        ⟨51484, false, false, [], []⟩,
        ⟨51485, false, false, [], []⟩
      ]⟩,
    ⟨[23073, 83095, 1], [23073, 83093], .contexts [
        ⟨18563, false, false, [23073], []⟩
      ]⟩,
    ⟨[23073, 83093], [23073, 83093], .contexts []⟩,
    ⟨[23073, 83093], [23073, 83093], .contexts []⟩,
    ⟨[23073, 83093], [23073, 83093], .contexts []⟩,
    ⟨[23071], [23072], .contexts [
        ⟨51480, true, true, [], []⟩
      ]⟩,
    ⟨[23071], [23072], .contexts [
        ⟨51491, false, false, [], []⟩
      ]⟩,
    ⟨[88581], [23073, 83093], .contexts [
        ⟨51492, false, false, [23070], [88581]⟩,
        ⟨13, false, false, [23070, 23072], [88581]⟩,
        ⟨51083, true, false, [23070, 23072], []⟩,
        ⟨51018, true, false, [23070, 23072], []⟩,
        ⟨51486, false, false, [23070, 23072], [1]⟩,
        ⟨51487, false, false, [23070, 23072], []⟩,
        ⟨51488, false, false, [23070, 23072], []⟩,
        ⟨51489, false, false, [23070, 23072], []⟩,
        ⟨51490, false, false, [23070, 23072], []⟩,
        ⟨51480, true, false, [], [83093]⟩
      ]⟩,
    ⟨[23072], [23072], .contexts []⟩,
    ⟨[83093, 11], [23071, 88579], .contexts [
        ⟨51493, true, false, [23072], [11]⟩,
        ⟨51015, false, false, [23072], []⟩,
        ⟨51084, false, false, [23072], []⟩,
        ⟨51494, true, false, [], [88579]⟩,
        ⟨51494, true, false, [], [88579]⟩,
        ⟨51492, true, false, [], [88579]⟩
      ]⟩,
    ⟨[23033, 85263], [23033, 85263], .contexts []⟩,
    ⟨[23033, 85263], [23033, 85263], .contexts []⟩,
    ⟨[23033, 85265], [23033, 85265], .contexts []⟩,
    ⟨[23033, 85265], [23033, 85265], .contexts []⟩,
    ⟨[87061, 9], [87061, 9], .contexts []⟩,
    ⟨[87061, 9], [23033, 85265], .contexts [
        ⟨51500, false, false, [], []⟩,
        ⟨40108, true, false, [], [9]⟩,
        ⟨40108, true, false, [], [9]⟩,
        ⟨40258, true, false, [], [9]⟩,
        ⟨40104, true, false, [], [9]⟩,
        ⟨77, false, false, [87059], []⟩,
        ⟨78, false, false, [87059], []⟩,
        ⟨51424, false, false, [], [13]⟩,
        ⟨51496, false, false, [], [13]⟩,
        ⟨51497, false, false, [], [13]⟩,
        ⟨51497, false, false, [], [13]⟩,
        ⟨30979, false, false, [23033], []⟩,
        ⟨51498, false, false, [], []⟩,
        ⟨51499, false, false, [], []⟩,
        ⟨43193, false, false, [23033], []⟩,
        ⟨13, true, false, [], [23033, 85265]⟩
      ]⟩,
    ⟨[23075], [23032], .source 11602⟩,
    ⟨[85265, 9], [23075, 87061], .contexts [
        ⟨51501, true, false, [23032], [9]⟩,
        ⟨46, false, false, [23032, 87061], []⟩,
        ⟨51502, true, false, [], [87061]⟩
      ]⟩,
    ⟨[82891, 15], [22999, 82891], .contexts [
        ⟨51441, false, false, [], []⟩,
        ⟨51446, false, false, [], []⟩,
        ⟨51439, false, false, [], []⟩,
        ⟨51440, false, false, [], []⟩,
        ⟨51440, false, false, [], []⟩
      ]⟩,
    ⟨[22999, 82891, 3], [22999, 82893], .contexts [
        ⟨17830, false, false, [22999], []⟩
      ]⟩,
    ⟨[22999, 82893], [22999, 82893], .contexts []⟩,
    ⟨[22999, 82893], [22999, 82893], .contexts []⟩,
    ⟨[22999, 82893], [22999, 82893], .contexts []⟩,
    ⟨[82891, 3], [82893], .contexts [
        ⟨17830, false, false, [], []⟩,
        ⟨18091, false, false, [], []⟩,
        ⟨17835, false, false, [], []⟩,
        ⟨17835, false, false, [], []⟩
      ]⟩,
    ⟨[82893, 15], [82893, 15], .contexts []⟩,
    ⟨[82893], [82893], .contexts []⟩,
    ⟨[23001], [22998], .contexts [
        ⟨51349, false, false, [], []⟩
      ]⟩,
    ⟨[22998], [22998], .contexts []⟩,
    ⟨[23001], [22998], .contexts [
        ⟨51512, false, false, [], []⟩,
        ⟨51513, false, false, [], []⟩,
        ⟨51513, false, false, [], []⟩
      ]⟩,
    ⟨[82893, 15], [23001, 82893], .contexts [
        ⟨51510, false, false, [], []⟩,
        ⟨51508, true, false, [22998], [15]⟩,
        ⟨51507, true, false, [22998], [15]⟩,
        ⟨51506, true, false, [22998], [15]⟩,
        ⟨51505, true, false, [22998], [15]⟩,
        ⟨51504, true, false, [22998], [3, 15]⟩,
        ⟨1141, false, false, [22998, 82891], []⟩,
        ⟨21, false, false, [22998, 82891], []⟩,
        ⟨51509, false, false, [22998], []⟩,
        ⟨51511, false, false, [22998], []⟩,
        ⟨51514, true, false, [], [82893]⟩
      ]⟩,
    ⟨[87571, 9], [23047, 88585], .contexts [
        ⟨51459, false, false, [], []⟩
      ]⟩,
    ⟨[23047, 88585], [23047, 88585], .contexts []⟩,
    ⟨[23047, 88585], [23047, 88585], .contexts []⟩,
    ⟨[88585, 5], [88585, 5], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 805. -/
def y322TCIndexRaw805 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[23077], [23049, 21103], .source 11603⟩,
    ⟨[88585, 5], [23077, 85111], .contexts [
        ⟨51519, false, false, [], []⟩,
        ⟨51518, true, false, [23046], [5]⟩,
        ⟨51518, true, false, [23046], [5]⟩,
        ⟨51517, true, false, [23046], [5]⟩,
        ⟨51516, true, false, [23046], [5]⟩,
        ⟨51455, true, false, [23046], [5]⟩,
        ⟨1079, false, false, [23046, 87571], []⟩,
        ⟨1080, false, false, [23046, 87571], []⟩,
        ⟨44258, false, false, [23046], [9]⟩,
        ⟨30238, false, false, [23046, 21103], []⟩,
        ⟨30253, false, false, [23046, 21103], []⟩,
        ⟨51460, true, false, [], [21103, 85111]⟩,
        ⟨51520, true, false, [], [85111]⟩
      ]⟩,
    ⟨[23079], [23076], .source 11604⟩,
    ⟨[85111, 5], [23079, 88585], .contexts [
        ⟨51521, true, false, [23076], [5]⟩,
        ⟨28, false, false, [23076, 88585], []⟩,
        ⟨51522, true, false, [], [88585]⟩
      ]⟩,
    ⟨[23081], [15867, 23071], .source 11605⟩,
    ⟨[23071, 88579], [23071, 88579], .contexts []⟩,
    ⟨[23071, 88579], [23071, 88579], .contexts []⟩,
    ⟨[83093, 11], [23071, 88579], .contexts [
        ⟨51495, false, false, [], []⟩,
        ⟨51525, false, false, [], []⟩,
        ⟨51526, false, false, [], []⟩,
        ⟨51526, false, false, [], []⟩
      ]⟩,
    ⟨[83093, 10], [83093, 11], .contexts [
        ⟨54, false, false, [83093], []⟩
      ]⟩,
    ⟨[88579, 7], [88579, 7], .contexts []⟩,
    ⟨[88579], [88579], .contexts []⟩,
    ⟨[23083], [23080], .source 11606⟩,
    ⟨[23085], [23083, 23071], .source 11607⟩,
    ⟨[88579, 7], [23085, 88579], .contexts [
        ⟨51529, false, false, [], []⟩,
        ⟨51524, false, false, [23080], [88579, 7]⟩,
        ⟨51495, true, false, [23080, 15867], [7]⟩,
        ⟨31295, true, false, [23080], [11, 7]⟩,
        ⟨555, false, false, [23080, 83093], []⟩,
        ⟨51528, false, false, [23080], []⟩,
        ⟨51527, false, false, [23080], []⟩,
        ⟨51530, false, false, [23080, 23071], []⟩,
        ⟨51531, true, false, [], [23071, 88579]⟩,
        ⟨51532, true, false, [], [88579]⟩
      ]⟩,
    ⟨[23087], [18503, 21161], .source 11608⟩,
    ⟨[87091, 15], [87091, 15], .contexts []⟩,
    ⟨[23089], [23086], .source 11609⟩,
    ⟨[23091], [23089, 23071], .source 11610⟩,
    ⟨[87091, 15], [23091, 88579], .contexts [
        ⟨51535, false, false, [], []⟩,
        ⟨51534, false, false, [23086], [87091, 15]⟩,
        ⟨44352, true, false, [23086, 18503], [15]⟩,
        ⟨33861, true, false, [23086], [11, 15]⟩,
        ⟨2046, false, false, [23086, 83093], []⟩,
        ⟨51528, false, false, [23086], []⟩,
        ⟨51527, false, false, [23086], []⟩,
        ⟨51530, false, false, [23086, 23071], []⟩,
        ⟨51536, true, false, [], [23071, 88579]⟩,
        ⟨51537, true, false, [], [88579]⟩
      ]⟩,
    ⟨[23093], [23090], .source 11611⟩,
    ⟨[88579, 15], [23093, 87091], .contexts [
        ⟨51538, true, false, [23090], [15]⟩,
        ⟨1, false, false, [23090, 87091], []⟩,
        ⟨51539, true, false, [], [87091]⟩
      ]⟩,
    ⟨[23095], [21191, 23071], .source 11612⟩,
    ⟨[88579, 13], [88579, 13], .contexts []⟩,
    ⟨[23097], [23094], .source 11613⟩,
    ⟨[23099], [23097, 23071], .source 11614⟩,
    ⟨[88579, 13], [23099, 88579], .contexts [
        ⟨51542, false, false, [], []⟩,
        ⟨51541, false, false, [23094], [88579, 13]⟩,
        ⟨51495, true, false, [23094, 21191], [13]⟩,
        ⟨44508, true, false, [23094], [11, 13]⟩,
        ⟨931, false, false, [23094, 83093], []⟩,
        ⟨51528, false, false, [23094], []⟩,
        ⟨51527, false, false, [23094], []⟩,
        ⟨51530, false, false, [23094, 23071], []⟩,
        ⟨51543, true, false, [], [23071, 88579]⟩,
        ⟨51544, true, false, [], [88579]⟩
      ]⟩,
    ⟨[87061, 9], [23033, 85265], .contexts [
        ⟨51500, false, false, [], []⟩,
        ⟨51501, false, false, [], []⟩,
        ⟨51498, false, false, [], []⟩,
        ⟨51499, false, false, [], []⟩,
        ⟨51499, false, false, [], []⟩
      ]⟩,
    ⟨[23101], [23033, 22469], .source 11615⟩,
    ⟨[23101, 88017], [23101, 88017], .contexts []⟩,
    ⟨[23101, 88017], [23101, 88017], .contexts []⟩,
    ⟨[88017, 3], [88017, 3], .contexts []⟩,
    ⟨[87061], [87061], .contexts []⟩,
    ⟨[23103], [23100], .source 11616⟩,
    ⟨[23100], [23100], .contexts []⟩,
    ⟨[88017, 3], [23103, 87061], .contexts [
        ⟨51550, false, false, [], []⟩,
        ⟨51549, true, false, [23100], [3]⟩,
        ⟨51548, true, false, [23100], [3]⟩,
        ⟨47721, true, false, [], [3]⟩,
        ⟨51547, false, false, [23100], [88019, 9, 3]⟩,
        ⟨49007, true, false, [23100, 23033], [9, 3]⟩,
        ⟨51546, true, false, [23100], [3, 9, 3]⟩,
        ⟨1439, false, false, [23100, 87061], []⟩,
        ⟨51551, false, false, [23100], []⟩,
        ⟨51553, true, false, [], [87061]⟩,
        ⟨51553, true, false, [], [87061]⟩,
        ⟨51552, true, false, [], [87061]⟩
      ]⟩,
    ⟨[87061, 3], [23101, 88017], .contexts [
        ⟨51554, true, false, [23102], [3]⟩,
        ⟨20, false, false, [23102, 88017], []⟩,
        ⟨51552, false, true, [], [88017]⟩
      ]⟩,
    ⟨[23033, 85267], [23033, 85267], .contexts []⟩,
    ⟨[87061, 15], [87063], .contexts [
        ⟨40107, false, false, [], []⟩,
        ⟨40257, false, false, [], []⟩,
        ⟨40111, false, false, [], []⟩,
        ⟨40111, false, false, [], []⟩
      ]⟩,
    ⟨[85267, 9], [85267, 9], .contexts []⟩,
    ⟨[87063], [87063], .contexts []⟩,
    ⟨[23032], [23032], .contexts []⟩,
    ⟨[85267, 9], [23075, 87063], .contexts [
        ⟨51558, false, false, [], []⟩,
        ⟨51556, true, false, [23032], [9]⟩,
        ⟨30983, true, false, [], [9]⟩,
        ⟨51546, true, false, [23032], [15, 9]⟩,
        ⟨935, false, false, [23032, 87061], []⟩,
        ⟨10, false, false, [23032, 87061], []⟩,
        ⟨51557, false, false, [23032], []⟩,
        ⟨51559, false, false, [23032], []⟩,
        ⟨51560, true, false, [], [87063]⟩,
        ⟨51560, true, false, [], [87063]⟩,
        ⟨51502, true, false, [], [87063]⟩
      ]⟩,
    ⟨[23033], [23074], .contexts [
        ⟨51502, true, true, [], []⟩
      ]⟩,
    ⟨[23001, 82893], [23001, 82893], .contexts []⟩,
    ⟨[23001, 82893], [23001, 82893], .contexts []⟩,
    ⟨[82893, 5], [82895], .contexts [
        ⟨17834, false, false, [], []⟩,
        ⟨18089, false, false, [], []⟩,
        ⟨17839, false, false, [], []⟩,
        ⟨17839, false, false, [], []⟩
      ]⟩,
    ⟨[82893, 4], [82893, 5], .contexts [
        ⟨29, false, false, [82893], []⟩
      ]⟩,
    ⟨[82895, 15], [82895, 15], .contexts []⟩,
    ⟨[82895], [82895], .contexts []⟩,
    ⟨[22999], [23000], .contexts [
        ⟨51355, false, false, [], []⟩,
        ⟨51388, false, false, [], []⟩,
        ⟨51388, false, false, [], []⟩
      ]⟩,
    ⟨[82895, 15], [22999, 82895], .contexts [
        ⟨51567, false, false, [], []⟩,
        ⟨17834, true, false, [], [15]⟩,
        ⟨51564, true, false, [23000], [5, 15]⟩,
        ⟨51564, true, false, [23000], [5, 15]⟩,
        ⟨51563, true, false, [23000], [5, 15]⟩,
        ⟨51515, true, false, [23000], [5, 15]⟩,
        ⟨51510, true, false, [23000], [5, 15]⟩,
        ⟨2072, false, false, [23000, 82893], []⟩,
        ⟨51566, false, false, [23000], []⟩,
        ⟨51565, false, false, [23000], []⟩,
        ⟨51568, false, false, [23000], []⟩,
        ⟨51569, true, false, [], [82895]⟩
      ]⟩,
    ⟨[23077, 85111], [23077, 85111], .contexts []⟩,
    ⟨[23077, 85111], [23077, 85111], .contexts []⟩,
    ⟨[88585, 5], [23077, 85111], .contexts [
        ⟨51519, false, false, [], []⟩,
        ⟨51521, false, false, [], []⟩,
        ⟨51571, false, false, [], []⟩,
        ⟨51572, false, false, [], []⟩,
        ⟨51572, false, false, [], []⟩
      ]⟩,
    ⟨[88587], [23029, 85213], .contexts [
        ⟨51408, false, false, [], []⟩
      ]⟩,
    ⟨[23029, 85213], [23029, 85213], .contexts []⟩,
    ⟨[85111, 15], [85111, 15], .contexts []⟩,
    ⟨[23105], [23079, 23029], .source 11617⟩,
    ⟨[85111, 15], [23105, 85211], .contexts [
        ⟨51576, false, false, [], []⟩,
        ⟨51573, true, false, [23076], [15]⟩,
        ⟨184, false, false, [23076, 88585], []⟩,
        ⟨185, false, false, [23076, 88585], []⟩,
        ⟨51023, false, false, [23076], [5]⟩,
        ⟨51574, false, false, [23076], [5]⟩,
        ⟨51575, false, false, [23076], [5]⟩,
        ⟨51575, false, false, [23076], [5]⟩,
        ⟨51575, false, false, [23076], [5]⟩,
        ⟨30457, false, false, [23076, 23029], []⟩,
        ⟨38000, false, false, [23076, 23029], []⟩,
        ⟨51522, true, false, [], [23029, 85211]⟩,
        ⟨51577, true, false, [], [85211]⟩
      ]⟩,
    ⟨[23107], [23104], .source 11618⟩,
    ⟨[85211, 15], [23107, 85111], .contexts [
        ⟨51578, true, false, [23104], [15]⟩,
        ⟨1, false, false, [23104, 85111], []⟩,
        ⟨51579, true, false, [], [85111]⟩
      ]⟩,
    ⟨[23085, 88579], [23085, 88579], .contexts []⟩,
    ⟨[23085, 88579], [23085, 88579], .contexts []⟩,
    ⟨[88579, 9], [88577], .contexts [
        ⟨51085, false, false, [], []⟩,
        ⟨51086, false, false, [], []⟩,
        ⟨51010, false, false, [], []⟩,
        ⟨51010, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 806. -/
def y322TCIndexRaw806 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88579, 8], [88579, 9], .contexts [
        ⟨47, false, false, [88579], []⟩
      ]⟩,
    ⟨[88577, 7], [88577, 7], .contexts []⟩,
    ⟨[88577], [88577], .contexts []⟩,
    ⟨[23109], [23084], .source 11619⟩,
    ⟨[23084], [23084], .contexts []⟩,
    ⟨[88577, 7], [23109, 88577], .contexts [
        ⟨51585, false, false, [], []⟩,
        ⟨51011, true, false, [], [7]⟩,
        ⟨51582, true, false, [23084], [9, 7]⟩,
        ⟨51582, true, false, [23084], [9, 7]⟩,
        ⟨51581, true, false, [23084], [9, 7]⟩,
        ⟨51533, true, false, [23084], [9, 7]⟩,
        ⟨51529, true, false, [23084], [9, 7]⟩,
        ⟨579, false, false, [23084, 88579], []⟩,
        ⟨51584, false, false, [23084], []⟩,
        ⟨51583, false, false, [23084], []⟩,
        ⟨51586, false, false, [23084], []⟩,
        ⟨51588, true, false, [], [88577]⟩,
        ⟨51588, true, false, [], [88577]⟩,
        ⟨51587, true, false, [], [88577]⟩
      ]⟩,
    ⟨[23091, 88579], [23091, 88579], .contexts []⟩,
    ⟨[23091, 88579], [23091, 88579], .contexts []⟩,
    ⟨[23091, 88577], [23091, 88577], .contexts []⟩,
    ⟨[88577, 15], [88577, 15], .contexts []⟩,
    ⟨[23090], [23090], .contexts []⟩,
    ⟨[23093], [23090], .contexts [
        ⟨51539, false, false, [], []⟩,
        ⟨51594, false, false, [], []⟩,
        ⟨51594, false, false, [], []⟩
      ]⟩,
    ⟨[88577, 15], [23093, 87089], .contexts [
        ⟨51593, false, false, [], []⟩,
        ⟨51592, true, false, [23090], [15]⟩,
        ⟨51011, true, false, [], [15]⟩,
        ⟨51591, true, false, [23090], [9, 15]⟩,
        ⟨51591, true, false, [23090], [9, 15]⟩,
        ⟨51590, true, false, [23090], [9, 15]⟩,
        ⟨51538, true, false, [23090], [9, 15]⟩,
        ⟨51535, true, false, [23090], [9, 15]⟩,
        ⟨1671, false, false, [23090, 87091], []⟩,
        ⟨43639, false, false, [23090], []⟩,
        ⟨43638, false, false, [23090], []⟩,
        ⟨43641, false, false, [23090], []⟩,
        ⟨51595, true, false, [], [87089]⟩
      ]⟩,
    ⟨[23091], [23092], .contexts [
        ⟨51539, true, true, [], []⟩
      ]⟩,
    ⟨[23099, 88579], [23099, 88579], .contexts []⟩,
    ⟨[23099, 88579], [23099, 88579], .contexts []⟩,
    ⟨[23111], [23098], .source 11620⟩,
    ⟨[23098], [23098], .contexts []⟩,
    ⟨[23075, 87063], [23075, 87063], .contexts []⟩,
    ⟨[23075, 87063], [23075, 87063], .contexts []⟩,
    ⟨[85277], [85277], .contexts []⟩,
    ⟨[23113], [23033, 22409], .source 11621⟩,
    ⟨[87063, 5], [23113, 85277], .contexts [
        ⟨51603, true, false, [23074], [5]⟩,
        ⟨51603, true, false, [23074], [5]⟩,
        ⟨51602, true, false, [23074], [5]⟩,
        ⟨51561, true, false, [23074], [5]⟩,
        ⟨51558, true, false, [23074], [5]⟩,
        ⟨1079, false, false, [23074, 85267], []⟩,
        ⟨1080, false, false, [23074, 85267], []⟩,
        ⟨48946, false, false, [23074], [9]⟩,
        ⟨48948, false, false, [23074], [9]⟩,
        ⟨48944, false, false, [23074], [9]⟩,
        ⟨48945, false, false, [23074], [9]⟩,
        ⟨48945, false, false, [23074], [9]⟩,
        ⟨31002, false, false, [23074, 22409], []⟩,
        ⟨51604, false, false, [23074, 22409], []⟩,
        ⟨51562, true, false, [], [22409, 85277]⟩,
        ⟨51605, true, false, [], [85277]⟩
      ]⟩,
    ⟨[23115], [23112], .source 11622⟩,
    ⟨[22999, 82895], [22999, 82895], .contexts []⟩,
    ⟨[22999, 82895], [22999, 82895], .contexts []⟩,
    ⟨[82895, 15], [22999, 82895], .contexts [
        ⟨51567, false, false, [], []⟩,
        ⟨51570, false, false, [], []⟩,
        ⟨51608, false, false, [], []⟩,
        ⟨51609, false, false, [], []⟩,
        ⟨51609, false, false, [], []⟩
      ]⟩,
    ⟨[22999, 82895, 1], [22999, 82897], .contexts [
        ⟨17838, false, false, [22999], []⟩
      ]⟩,
    ⟨[22999, 82897], [22999, 82897], .contexts []⟩,
    ⟨[22999, 82897], [22999, 82897], .contexts []⟩,
    ⟨[22999, 82897], [22999, 82897], .contexts []⟩,
    ⟨[82895, 1], [82897], .contexts [
        ⟨17838, false, false, [], []⟩
      ]⟩,
    ⟨[82897, 15], [82897, 15], .contexts []⟩,
    ⟨[82897], [82897], .contexts []⟩,
    ⟨[82897, 15], [23001, 82897], .contexts [
        ⟨51616, false, false, [], []⟩,
        ⟨51614, true, false, [22998], [15]⟩,
        ⟨51613, true, false, [22998], [15]⟩,
        ⟨51612, true, false, [22998], [15]⟩,
        ⟨51611, true, false, [22998], [15]⟩,
        ⟨51610, true, false, [22998], [1, 15]⟩,
        ⟨1666, false, false, [22998, 82895], []⟩,
        ⟨9, false, false, [22998, 82895], []⟩,
        ⟨51615, false, false, [22998], []⟩,
        ⟨18086, false, false, [22998], []⟩,
        ⟨17843, false, false, [22998], []⟩,
        ⟨17843, false, false, [22998], []⟩,
        ⟨51617, false, false, [22998], []⟩,
        ⟨51514, true, false, [], [82897]⟩
      ]⟩,
    ⟨[23105, 85211], [23105, 85211], .contexts []⟩,
    ⟨[23105, 85211], [23105, 85211], .contexts []⟩,
    ⟨[23105, 85209], [23105, 85209], .contexts []⟩,
    ⟨[85209, 15], [85209, 15], .contexts []⟩,
    ⟨[23107], [23104], .contexts [
        ⟨51579, false, false, [], []⟩
      ]⟩,
    ⟨[23104], [23104], .contexts []⟩,
    ⟨[23107], [23104], .contexts [
        ⟨51623, false, false, [], []⟩,
        ⟨51624, false, false, [], []⟩,
        ⟨51624, false, false, [], []⟩
      ]⟩,
    ⟨[85209, 15], [23107, 85721], .contexts [
        ⟨51622, false, false, [], []⟩,
        ⟨51621, true, false, [23104], [15]⟩,
        ⟨30453, true, false, [], [15]⟩,
        ⟨51620, true, false, [23104], [3, 15]⟩,
        ⟨51620, true, false, [23104], [3, 15]⟩,
        ⟨51619, true, false, [23104], [3, 15]⟩,
        ⟨51578, true, false, [23104], [3, 15]⟩,
        ⟨51576, true, false, [23104], [3, 15]⟩,
        ⟨1141, false, false, [23104, 85111], []⟩,
        ⟨21, false, false, [23104, 85111], []⟩,
        ⟨33219, false, false, [23104], []⟩,
        ⟨33213, false, false, [23104], []⟩,
        ⟨33214, false, false, [23104], []⟩,
        ⟨33214, false, false, [23104], []⟩,
        ⟨39122, false, false, [23104], []⟩,
        ⟨51625, true, false, [], [85721]⟩
      ]⟩,
    ⟨[23105], [23106], .contexts [
        ⟨51579, true, true, [], []⟩
      ]⟩,
    ⟨[21105, 88213], [21105, 88213], .contexts []⟩,
    ⟨[23117], [21103, 23105], .source 11623⟩,
    ⟨[88213], [23117, 85209], .contexts [
        ⟨51628, true, false, [21104], []⟩,
        ⟨51628, true, false, [21104], []⟩,
        ⟨44236, false, false, [21104], [88213]⟩,
        ⟨1, true, false, [21104, 21102, 88213], []⟩,
        ⟨49282, false, false, [21104, 21102], [15]⟩,
        ⟨51626, true, false, [21104, 23106], [15]⟩,
        ⟨1, false, false, [21104, 23106, 85209], []⟩,
        ⟨51627, true, false, [21104], [85209]⟩,
        ⟨51621, false, false, [21104], []⟩,
        ⟨44236, false, true, [], [23105, 85209]⟩,
        ⟨51629, true, false, [], [85209]⟩
      ]⟩,
    ⟨[23119], [23116], .source 11624⟩,
    ⟨[23116], [23116], .contexts []⟩,
    ⟨[23119], [23116], .contexts [
        ⟨51631, false, false, [], []⟩,
        ⟨51632, false, false, [], []⟩,
        ⟨51632, false, false, [], []⟩
      ]⟩,
    ⟨[85209, 9], [23119, 88211], .contexts [
        ⟨51630, true, false, [23116], [9]⟩,
        ⟨49275, false, false, [23116], []⟩,
        ⟨49263, false, false, [23116], []⟩,
        ⟨51633, true, false, [], [88211]⟩
      ]⟩,
    ⟨[85209, 11], [23119, 88215], .contexts [
        ⟨51630, true, false, [23116], [11]⟩,
        ⟨49284, false, false, [23116], []⟩,
        ⟨49286, false, false, [23116], []⟩,
        ⟨51633, true, false, [], [88215]⟩
      ]⟩,
    ⟨[23109, 88577], [23109, 88577], .contexts []⟩,
    ⟨[23109, 88577], [23109, 88577], .contexts []⟩,
    ⟨[88577, 1], [88575], .contexts [
        ⟨51087, false, false, [], []⟩,
        ⟨51088, false, false, [], []⟩,
        ⟨51006, false, false, [], []⟩,
        ⟨51006, false, false, [], []⟩
      ]⟩,
    ⟨[88577, 0], [88577, 1], .contexts [
        ⟨9, false, false, [88577], []⟩
      ]⟩,
    ⟨[88575, 7], [88575, 7], .contexts []⟩,
    ⟨[88575], [88575], .contexts []⟩,
    ⟨[23108], [23108], .contexts []⟩,
    ⟨[88575, 7], [23085, 88575], .contexts [
        ⟨51640, false, false, [], []⟩,
        ⟨51007, true, false, [], [7]⟩,
        ⟨51637, true, false, [23108], [1, 7]⟩,
        ⟨51637, true, false, [23108], [1, 7]⟩,
        ⟨51636, true, false, [23108], [1, 7]⟩,
        ⟨51589, true, false, [23108], [1, 7]⟩,
        ⟨51585, true, false, [23108], [1, 7]⟩,
        ⟨502, false, false, [23108, 88577], []⟩,
        ⟨51639, false, false, [23108], []⟩,
        ⟨51638, false, false, [23108], []⟩,
        ⟨51641, false, false, [23108], []⟩,
        ⟨51642, true, false, [], [88575]⟩,
        ⟨51642, true, false, [], [88575]⟩,
        ⟨51587, false, true, [], [88575]⟩
      ]⟩,
    ⟨[23093, 87089], [23093, 87089], .contexts []⟩,
    ⟨[23093, 87087], [23093, 87087], .contexts []⟩,
    ⟨[87087, 15], [87087, 15], .contexts []⟩,
    ⟨[23091], [23091], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 807. -/
def y322TCIndexRaw807 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[23091], [23092], .contexts [
        ⟨51597, false, false, [], []⟩
      ]⟩,
    ⟨[23091], [23092], .contexts [
        ⟨51647, false, false, [], []⟩,
        ⟨51648, false, false, [], []⟩
      ]⟩,
    ⟨[23092], [23092], .contexts []⟩,
    ⟨[23091], [23092], .contexts [
        ⟨51649, false, false, [], []⟩,
        ⟨51650, false, false, [], []⟩,
        ⟨51650, false, false, [], []⟩
      ]⟩,
    ⟨[87087, 15], [23091, 88575], .contexts [
        ⟨51646, false, false, [], []⟩,
        ⟨51645, true, false, [23092], [15]⟩,
        ⟨40158, true, false, [], [15]⟩,
        ⟨51644, true, false, [23092], [1, 15]⟩,
        ⟨51644, true, false, [23092], [1, 15]⟩,
        ⟨51596, true, false, [23092], [1, 15]⟩,
        ⟨51593, true, false, [23092], [1, 15]⟩,
        ⟨1666, false, false, [23092, 88577], []⟩,
        ⟨51639, false, false, [23092], []⟩,
        ⟨51638, false, false, [23092], []⟩,
        ⟨51641, false, false, [23092], []⟩,
        ⟨51651, true, false, [], [88575]⟩
      ]⟩,
    ⟨[88575, 15], [23093, 87087], .contexts [
        ⟨51652, true, false, [23090], [15]⟩,
        ⟨1, false, false, [23090, 87087], []⟩,
        ⟨51539, true, false, [], [87087]⟩
      ]⟩,
    ⟨[23001, 82897], [23001, 82897], .contexts []⟩,
    ⟨[23001, 82897], [23001, 82897], .contexts []⟩,
    ⟨[82897, 9], [82899], .contexts [
        ⟨17842, false, false, [], []⟩,
        ⟨18085, false, false, [], []⟩,
        ⟨17847, false, false, [], []⟩,
        ⟨17847, false, false, [], []⟩
      ]⟩,
    ⟨[82897, 8], [82897, 9], .contexts [
        ⟨47, false, false, [82897], []⟩
      ]⟩,
    ⟨[82899, 15], [82899, 15], .contexts []⟩,
    ⟨[82899], [82899], .contexts []⟩,
    ⟨[82899, 15], [22999, 82899], .contexts [
        ⟨51658, false, false, [], []⟩,
        ⟨17842, true, false, [], [15]⟩,
        ⟨51655, true, false, [23000], [9, 15]⟩,
        ⟨51655, true, false, [23000], [9, 15]⟩,
        ⟨51654, true, false, [23000], [9, 15]⟩,
        ⟨51618, true, false, [23000], [9, 15]⟩,
        ⟨51616, true, false, [23000], [9, 15]⟩,
        ⟨1671, false, false, [23000, 82897], []⟩,
        ⟨51657, false, false, [23000], []⟩,
        ⟨51656, false, false, [23000], []⟩,
        ⟨51659, false, false, [23000], []⟩,
        ⟨51569, true, false, [], [82899]⟩
      ]⟩,
    ⟨[23107, 85721], [23107, 85721], .contexts []⟩,
    ⟨[85209, 1], [85207], .contexts [
        ⟨30513, false, false, [], []⟩,
        ⟨30514, false, false, [], []⟩,
        ⟨30448, false, false, [], []⟩,
        ⟨30448, false, false, [], []⟩
      ]⟩,
    ⟨[85721, 1], [85721, 1], .contexts []⟩,
    ⟨[23106], [23106], .contexts []⟩,
    ⟨[23105], [23106], .contexts [
        ⟨51627, false, false, [], []⟩,
        ⟨51664, false, false, [], []⟩,
        ⟨51664, false, false, [], []⟩
      ]⟩,
    ⟨[85721, 1], [23105, 85205], .contexts [
        ⟨51663, false, false, [], []⟩,
        ⟨51661, true, false, [23106], [1]⟩,
        ⟨51661, true, false, [23106], [1]⟩,
        ⟨51626, true, false, [23106], [1]⟩,
        ⟨51622, true, false, [23106], [1]⟩,
        ⟨7, false, false, [23106, 85209], []⟩,
        ⟨11, false, false, [23106, 85209], []⟩,
        ⟨51662, false, false, [23106], [15]⟩,
        ⟨30515, false, false, [23106], []⟩,
        ⟨30516, false, false, [23106], []⟩,
        ⟨30444, false, false, [23106], []⟩,
        ⟨30444, false, false, [23106], []⟩,
        ⟨38029, false, false, [23106], []⟩,
        ⟨51665, true, false, [], [85205]⟩
      ]⟩,
    ⟨[23119, 88211], [23119, 88211], .contexts []⟩,
    ⟨[23119, 88211], [23119, 88211], .contexts []⟩,
    ⟨[85209, 9], [23119, 88211], .contexts [
        ⟨51634, false, false, [], []⟩,
        ⟨51667, false, false, [], []⟩,
        ⟨51668, false, false, [], []⟩,
        ⟨51668, false, false, [], []⟩
      ]⟩,
    ⟨[23121], [23119, 22523], .source 11625⟩,
    ⟨[23121, 84483], [23121, 84483], .contexts []⟩,
    ⟨[23121, 84483], [23121, 84483], .contexts []⟩,
    ⟨[85207, 9], [85207, 9], .contexts []⟩,
    ⟨[85207, 9], [23121, 84483], .contexts [
        ⟨51673, false, false, [], []⟩,
        ⟨51662, true, false, [], [9]⟩,
        ⟨452, false, false, [85209], []⟩,
        ⟨455, false, false, [85209], []⟩,
        ⟨51669, false, false, [], [1, 9, 1]⟩,
        ⟨49262, false, false, [23119], [9, 1]⟩,
        ⟨49244, false, false, [23119], [1]⟩,
        ⟨51670, true, false, [], [84485, 1]⟩,
        ⟨26918, false, false, [23121], []⟩,
        ⟨51671, false, false, [], []⟩,
        ⟨51672, false, false, [], []⟩,
        ⟨27035, false, false, [23121], []⟩,
        ⟨13, true, false, [], [23121, 84483]⟩
      ]⟩,
    ⟨[23123], [23120], .source 11626⟩,
    ⟨[84483, 9], [23123, 85207], .contexts [
        ⟨51674, true, false, [23120], [9]⟩,
        ⟨46, false, false, [23120, 85207], []⟩,
        ⟨51675, true, false, [], [85207]⟩
      ]⟩,
    ⟨[85209, 11], [23119, 88215], .contexts [
        ⟨51635, false, false, [], []⟩
      ]⟩,
    ⟨[23119, 88215], [23119, 88215], .contexts []⟩,
    ⟨[23119, 88215], [23119, 88215], .contexts []⟩,
    ⟨[85209, 11], [23119, 88215], .contexts [
        ⟨51677, false, false, [], []⟩,
        ⟨51678, false, false, [], []⟩,
        ⟨51679, false, false, [], []⟩,
        ⟨51679, false, false, [], []⟩
      ]⟩,
    ⟨[23119, 88217], [23119, 88217], .contexts []⟩,
    ⟨[23119, 88217], [23119, 88217], .contexts []⟩,
    ⟨[85207, 11], [85207, 11], .contexts []⟩,
    ⟨[23119], [23119], .contexts [
        ⟨13, false, false, [], [23119]⟩
      ]⟩,
    ⟨[85207, 11], [23119, 88217], .contexts [
        ⟨51683, false, false, [], []⟩,
        ⟨51662, true, false, [], [11]⟩,
        ⟨110, false, false, [85209], []⟩,
        ⟨111, false, false, [85209], []⟩,
        ⟨51680, false, false, [], [1]⟩,
        ⟨49304, false, false, [23119], []⟩,
        ⟨51681, false, false, [], []⟩,
        ⟨51682, false, false, [], []⟩,
        ⟨49322, false, false, [23119], []⟩,
        ⟨51684, true, false, [], [88217]⟩
      ]⟩,
    ⟨[23117], [23118], .contexts [
        ⟨51631, true, true, [], []⟩
      ]⟩,
    ⟨[23091, 88575], [23091, 88575], .contexts []⟩,
    ⟨[23091, 88575], [23091, 88575], .contexts []⟩,
    ⟨[23091, 88573], [23091, 88573], .contexts []⟩,
    ⟨[88573, 15], [88573, 15], .contexts []⟩,
    ⟨[87085], [87085], .contexts []⟩,
    ⟨[88573, 15], [23093, 87085], .contexts [
        ⟨51690, false, false, [], []⟩,
        ⟨51689, true, false, [23090], [15]⟩,
        ⟨51003, true, false, [], [15]⟩,
        ⟨51688, true, false, [23090], [5, 15]⟩,
        ⟨51688, true, false, [23090], [5, 15]⟩,
        ⟨51687, true, false, [23090], [5, 15]⟩,
        ⟨51652, true, false, [23090], [5, 15]⟩,
        ⟨51646, true, false, [23090], [5, 15]⟩,
        ⟨2072, false, false, [23090, 87087], []⟩,
        ⟨29, false, false, [23090, 87087], []⟩,
        ⟨40154, false, false, [23090], []⟩,
        ⟨40153, false, false, [23090], []⟩,
        ⟨40153, false, false, [23090], []⟩,
        ⟨51691, false, false, [23090], []⟩,
        ⟨51595, true, false, [], [87085]⟩
      ]⟩,
    ⟨[22999, 82899], [22999, 82899], .contexts []⟩,
    ⟨[22999, 82899], [22999, 82899], .contexts []⟩,
    ⟨[82899, 11], [82901], .contexts [
        ⟨17846, false, false, [], []⟩,
        ⟨18084, false, false, [], []⟩,
        ⟨17851, false, false, [], []⟩,
        ⟨17851, false, false, [], []⟩
      ]⟩,
    ⟨[82899, 10], [82899, 11], .contexts [
        ⟨54, false, false, [82899], []⟩
      ]⟩,
    ⟨[82901, 15], [82901, 15], .contexts []⟩,
    ⟨[82901], [82901], .contexts []⟩,
    ⟨[82901, 15], [23001, 82901], .contexts [
        ⟨51697, false, false, [], []⟩,
        ⟨17846, true, false, [], [15]⟩,
        ⟨51694, true, false, [22998], [11, 15]⟩,
        ⟨51694, true, false, [22998], [11, 15]⟩,
        ⟨51693, true, false, [22998], [11, 15]⟩,
        ⟨51660, true, false, [22998], [11, 15]⟩,
        ⟨51658, true, false, [22998], [11, 15]⟩,
        ⟨2046, false, false, [22998, 82899], []⟩,
        ⟨51696, false, false, [22998], []⟩,
        ⟨51695, false, false, [22998], []⟩,
        ⟨51698, false, false, [22998], []⟩,
        ⟨51514, true, false, [], [82901]⟩
      ]⟩,
    ⟨[23105, 85205], [23105, 85205], .contexts []⟩,
    ⟨[23105, 85205], [23105, 85205], .contexts []⟩,
    ⟨[85721, 1], [23105, 85205], .contexts [
        ⟨51663, false, false, [], []⟩,
        ⟨51666, false, false, [], []⟩,
        ⟨51700, false, false, [], []⟩,
        ⟨51701, false, false, [], []⟩,
        ⟨51701, false, false, [], []⟩
      ]⟩,
    ⟨[18279, 86809], [18279, 86809], .contexts []⟩,
    ⟨[18279, 86809], [18279, 86809], .contexts []⟩,
    ⟨[23125], [23107, 19523], .source 11627⟩,
    ⟨[85205, 7], [23125, 84493], .contexts [
        ⟨51702, true, false, [23104], [7]⟩,
        ⟨104, false, false, [23104, 85721], []⟩,
        ⟨105, false, false, [23104, 85721], []⟩,
        ⟨39124, false, false, [23104], [1]⟩,
        ⟨51703, false, false, [23104], [1]⟩,
        ⟨51704, false, false, [23104], [1]⟩,
        ⟨51704, false, false, [23104], [1]⟩,
        ⟨39116, false, false, [23104, 18279], []⟩,
        ⟨39138, true, false, [23104], [84493]⟩,
        ⟨27139, false, false, [23104, 19523], []⟩,
        ⟨51623, true, false, [], [19523, 84493]⟩,
        ⟨51705, true, false, [], [84493]⟩
      ]⟩,
    ⟨[23127], [23124], .source 11628⟩,
    ⟨[23129], [7355, 21049], .source 11629⟩,
    ⟨[23131], [23129, 21077], .source 11630⟩,
    ⟨[85205, 9], [85205, 9], .contexts []⟩,
    ⟨[85205, 9], [23104, 23131, 84481], .contexts [
        ⟨51710, false, false, [], []⟩,
        ⟨51702, true, false, [23104], [9]⟩,
        ⟨452, false, false, [23104, 85721], []⟩,
        ⟨455, false, false, [23104, 85721], []⟩,
        ⟨33212, false, false, [23104], [1, 9, 1]⟩,
        ⟨32423, false, false, [23104], [1, 9, 1]⟩,
        ⟨32424, false, false, [23104], [1, 9, 1]⟩,
        ⟨32424, false, false, [23104], [1, 9, 1]⟩,
        ⟨32432, false, false, [23104], [9, 1]⟩,
        ⟨32426, false, false, [23104], [9, 1]⟩,
        ⟨32427, false, false, [23104], [9, 1]⟩,
        ⟨32427, false, false, [23104], [9, 1]⟩,
        ⟨44103, false, false, [23104, 7355], [1]⟩,
        ⟨51708, true, false, [23104], [87567, 1]⟩,
        ⟨43984, false, false, [23104, 23129], []⟩,
        ⟨44127, false, false, [23104, 23129], []⟩,
        ⟨51709, true, false, [23104], [84481]⟩,
        ⟨27051, false, false, [23104, 23131], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 808. -/
def y322TCIndexRaw808 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[23133], [23107, 23131], .source 11631⟩,
    ⟨[85205, 9], [23133, 84481], .contexts [
        ⟨51711, false, false, [], []⟩,
        ⟨51623, true, false, [], [23131, 84481]⟩,
        ⟨51712, true, false, [], [84481]⟩
      ]⟩,
    ⟨[23135], [23132], .source 11632⟩,
    ⟨[85205, 11], [85205, 11], .contexts []⟩,
    ⟨[85205, 11], [23107, 85725], .contexts [
        ⟨51715, false, false, [], []⟩,
        ⟨51702, true, false, [23104], [11]⟩,
        ⟨110, false, false, [23104, 85721], []⟩,
        ⟨111, false, false, [23104, 85721], []⟩,
        ⟨33230, false, false, [23104], [1]⟩,
        ⟨33242, false, false, [23104], []⟩,
        ⟨33243, false, false, [23104], []⟩,
        ⟨33244, false, false, [23104], []⟩,
        ⟨33244, false, false, [23104], []⟩,
        ⟨33254, false, false, [23104], []⟩,
        ⟨51625, true, false, [], [85725]⟩
      ]⟩,
    ⟨[23105, 85203], [23105, 85203], .contexts []⟩,
    ⟨[23105, 85203], [23105, 85203], .contexts []⟩,
    ⟨[23105, 85203, 1], [23105, 85201], .contexts [
        ⟨30437, false, false, [23105], []⟩
      ]⟩,
    ⟨[23105, 85201], [23105, 85201], .contexts []⟩,
    ⟨[23105, 85201], [23105, 85201], .contexts []⟩,
    ⟨[23105, 85201], [23105, 85201], .contexts []⟩,
    ⟨[18945, 85933], [18945, 85933], .contexts []⟩,
    ⟨[85201, 13], [85201, 13], .contexts []⟩,
    ⟨[23137], [23107, 18945], .source 11633⟩,
    ⟨[85201, 13], [23137, 85931], .contexts [
        ⟨51724, false, false, [], []⟩,
        ⟨51722, true, false, [23104], [13]⟩,
        ⟨51721, true, false, [23104], [13]⟩,
        ⟨51720, true, false, [23104], [13]⟩,
        ⟨51719, true, false, [23104], [13]⟩,
        ⟨51718, true, false, [23104], [1, 13]⟩,
        ⟨51717, true, false, [23104], [1, 13]⟩,
        ⟨30441, true, false, [], [1, 13]⟩,
        ⟨51702, true, false, [23104], [13, 1, 13]⟩,
        ⟨919, false, false, [23104, 85721], []⟩,
        ⟨116, false, false, [23104, 85721], []⟩,
        ⟨35900, false, false, [23104], [1]⟩,
        ⟨35903, false, false, [23104], [1]⟩,
        ⟨51723, false, false, [23104], [1]⟩,
        ⟨51723, false, false, [23104], [1]⟩,
        ⟨34228, false, false, [23104, 18945], []⟩,
        ⟨35907, false, false, [23104, 18945], []⟩,
        ⟨51623, true, false, [], [18945, 85931]⟩,
        ⟨51725, true, false, [], [85931]⟩
      ]⟩,
    ⟨[23139], [23136], .source 11634⟩,
    ⟨[23141], [23121, 17257], .source 11635⟩,
    ⟨[23141, 83579], [23141, 83579], .contexts []⟩,
    ⟨[23143], [23140], .source 11636⟩,
    ⟨[23140], [23140], .contexts []⟩,
    ⟨[83579, 7], [23143, 85207], .contexts [
        ⟨51729, true, false, [23140], [7]⟩,
        ⟨22088, true, false, [], [7]⟩,
        ⟨51728, false, false, [23140], [83577, 9, 7]⟩,
        ⟨27061, true, false, [23140, 23121], [9, 7]⟩,
        ⟨51672, true, false, [23140], [7, 9, 7]⟩,
        ⟨51672, true, false, [23140], [7, 9, 7]⟩,
        ⟨51671, true, false, [23140], [7, 9, 7]⟩,
        ⟨51674, true, false, [23140], [7, 9, 7]⟩,
        ⟨51673, true, false, [23140], [7, 9, 7]⟩,
        ⟨469, false, false, [23140, 85207], []⟩,
        ⟨38015, false, false, [23140], []⟩,
        ⟨51731, true, false, [], [85207]⟩,
        ⟨51731, true, false, [], [85207]⟩,
        ⟨51730, true, false, [], [85207]⟩
      ]⟩,
    ⟨[88573, 15], [23093, 87085], .contexts [
        ⟨51690, false, false, [], []⟩,
        ⟨51692, false, false, [], []⟩
      ]⟩,
    ⟨[23093, 87085], [23093, 87085], .contexts []⟩,
    ⟨[23093, 87083], [23093, 87083], .contexts []⟩,
    ⟨[88573, 3], [88571], .contexts [
        ⟨51092, false, false, [], []⟩,
        ⟨51093, false, false, [], []⟩,
        ⟨50998, false, false, [], []⟩,
        ⟨50998, false, false, [], []⟩
      ]⟩,
    ⟨[87083, 15], [87083, 15], .contexts []⟩,
    ⟨[88571], [88571], .contexts []⟩,
    ⟨[87083, 15], [23091, 88571], .contexts [
        ⟨51737, false, false, [], []⟩,
        ⟨51735, true, false, [23092], [15]⟩,
        ⟨40150, true, false, [], [15]⟩,
        ⟨51734, true, false, [23092], [3, 15]⟩,
        ⟨51734, true, false, [23092], [3, 15]⟩,
        ⟨51733, true, false, [23092], [3, 15]⟩,
        ⟨1141, false, false, [23092, 88573], []⟩,
        ⟨21, false, false, [23092, 88573], []⟩,
        ⟨51736, false, false, [23092], []⟩,
        ⟨51738, false, false, [23092], []⟩,
        ⟨51651, true, false, [], [88571]⟩
      ]⟩,
    ⟨[23001, 82901], [23001, 82901], .contexts []⟩,
    ⟨[23001, 82901], [23001, 82901], .contexts []⟩,
    ⟨[82901, 1], [82903], .contexts [
        ⟨17850, false, false, [], []⟩
      ]⟩,
    ⟨[82901, 1], [82903], .contexts [
        ⟨51742, false, false, [], []⟩,
        ⟨18082, false, false, [], []⟩,
        ⟨17855, false, false, [], []⟩,
        ⟨17855, false, false, [], []⟩
      ]⟩,
    ⟨[82901, 0], [82901, 1], .contexts [
        ⟨9, false, false, [82901], []⟩
      ]⟩,
    ⟨[82903, 15], [82903, 15], .contexts []⟩,
    ⟨[82903], [82903], .contexts []⟩,
    ⟨[82903, 15], [22999, 82903], .contexts [
        ⟨51745, false, false, [], []⟩,
        ⟨17850, true, false, [], [15]⟩,
        ⟨51741, true, false, [23000], [1, 15]⟩,
        ⟨51741, true, false, [23000], [1, 15]⟩,
        ⟨51740, true, false, [23000], [1, 15]⟩,
        ⟨51699, true, false, [23000], [1, 15]⟩,
        ⟨51697, true, false, [23000], [1, 15]⟩,
        ⟨1666, false, false, [23000, 82901], []⟩,
        ⟨51744, false, false, [23000], []⟩,
        ⟨51743, false, false, [23000], []⟩,
        ⟨51746, false, false, [23000], []⟩,
        ⟨51569, true, false, [], [82903]⟩
      ]⟩,
    ⟨[23133, 84481], [23133, 84481], .contexts []⟩,
    ⟨[23133, 84481], [23133, 84481], .contexts []⟩,
    ⟨[84479, 9], [84479, 9], .contexts []⟩,
    ⟨[23132], [23132], .contexts []⟩,
    ⟨[84479, 9], [23135, 85203], .contexts [
        ⟨51750, false, false, [], []⟩,
        ⟨26910, true, false, [], [9]⟩,
        ⟨51749, true, false, [23132], [13, 9]⟩,
        ⟨51749, true, false, [23132], [13, 9]⟩,
        ⟨51748, true, false, [23132], [13, 9]⟩,
        ⟨51713, true, false, [23132], [13, 9]⟩,
        ⟨51710, true, false, [23132], [13, 9]⟩,
        ⟨511, false, false, [23132, 85205], []⟩,
        ⟨38038, false, false, [23132], []⟩,
        ⟨38037, false, false, [23132], []⟩,
        ⟨38039, false, false, [23132], []⟩,
        ⟨51751, true, false, [], [85203]⟩,
        ⟨51751, true, false, [], [85203]⟩,
        ⟨51714, true, false, [], [85203]⟩
      ]⟩,
    ⟨[23107, 85725], [23107, 85725], .contexts []⟩,
    ⟨[23107, 85727], [23107, 85727], .contexts []⟩,
    ⟨[23107, 85727], [23107, 85727], .contexts []⟩,
    ⟨[85727, 11], [85727, 11], .contexts []⟩,
    ⟨[85727, 11], [23105, 85203], .contexts [
        ⟨51756, false, false, [], []⟩,
        ⟨51755, true, false, [23106], [11]⟩,
        ⟨51754, true, false, [23106], [11]⟩,
        ⟨33263, true, false, [], [11]⟩,
        ⟨51753, true, false, [23106], [13, 11]⟩,
        ⟨51753, true, false, [23106], [13, 11]⟩,
        ⟨51716, true, false, [23106], [13, 11]⟩,
        ⟨51715, true, false, [23106], [13, 11]⟩,
        ⟨619, false, false, [23106, 85205], []⟩,
        ⟨38038, false, false, [23106], []⟩,
        ⟨38037, false, false, [23106], []⟩,
        ⟨38039, false, false, [23106], []⟩,
        ⟨51665, true, false, [], [85203]⟩
      ]⟩,
    ⟨[85203, 11], [23107, 85727], .contexts [
        ⟨51757, true, false, [23104], [11]⟩,
        ⟨53, false, false, [23104, 85727], []⟩,
        ⟨51579, true, false, [], [85727]⟩
      ]⟩,
    ⟨[23137, 85931], [23137, 85931], .contexts []⟩,
    ⟨[85201, 13], [23137, 85931], .contexts [
        ⟨51724, false, false, [], []⟩,
        ⟨51726, false, false, [], []⟩,
        ⟨51759, false, false, [], []⟩,
        ⟨51759, false, false, [], []⟩
      ]⟩,
    ⟨[23145], [23137, 21183], .source 11637⟩,
    ⟨[23147], [23145, 21247], .source 11638⟩,
    ⟨[85811, 3], [85811, 3], .contexts []⟩,
    ⟨[85201], [85201], .contexts []⟩,
    ⟨[23149], [23146], .source 11639⟩,
    ⟨[23149], [23146], .contexts [
        ⟨51765, false, false, [], []⟩
      ]⟩,
    ⟨[23146], [23146], .contexts []⟩,
    ⟨[23149], [23146], .contexts [
        ⟨51766, false, false, [], []⟩,
        ⟨51767, false, false, [], []⟩,
        ⟨51767, false, false, [], []⟩
      ]⟩,
    ⟨[85811, 3], [23149, 85201], .contexts [
        ⟨51763, false, false, [], []⟩,
        ⟨51762, false, false, [23146], [85811, 3]⟩,
        ⟨44595, false, false, [23146, 23145], [85811, 3]⟩,
        ⟨44533, true, false, [23146, 23145, 18503], [3]⟩,
        ⟨33884, true, false, [23146, 23145], [3]⟩,
        ⟨51761, false, false, [23146], [83087, 13, 3]⟩,
        ⟨44423, true, false, [23146, 23137], [13, 3]⟩,
        ⟨51760, true, false, [23146], [3, 13, 3]⟩,
        ⟨4550, false, false, [23146, 85201], []⟩,
        ⟨51764, false, false, [23146], []⟩,
        ⟨51768, true, false, [], [85201]⟩
      ]⟩,
    ⟨[23147], [23148], .contexts [
        ⟨51765, true, true, [], []⟩
      ]⟩,
    ⟨[85201, 3], [23147, 85811], .contexts [
        ⟨51769, true, false, [23148], [3]⟩,
        ⟨20, false, false, [23148, 85811], []⟩,
        ⟨51770, true, false, [], [85811]⟩
      ]⟩,
    ⟨[23091, 88571], [23091, 88571], .contexts []⟩,
    ⟨[23091, 88571], [23091, 88571], .contexts []⟩,
    ⟨[23091, 88567], [23091, 88567], .contexts []⟩,
    ⟨[87083], [87083], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 809. -/
def y322TCIndexRaw809 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88567, 1], [23093, 87083], .contexts [
        ⟨51774, true, false, [23090], [1]⟩,
        ⟨50991, true, false, [], [1]⟩,
        ⟨50995, true, false, [], [15, 1]⟩,
        ⟨51773, true, false, [23090], [1, 15, 1]⟩,
        ⟨51773, true, false, [23090], [1, 15, 1]⟩,
        ⟨51772, true, false, [23090], [1, 15, 1]⟩,
        ⟨51739, true, false, [23090], [1, 15, 1]⟩,
        ⟨51737, true, false, [23090], [1, 15, 1]⟩,
        ⟨504, false, false, [23090, 87083], []⟩,
        ⟨51775, false, false, [23090], []⟩,
        ⟨51595, true, false, [], [87083]⟩
      ]⟩,
    ⟨[88567], [23093, 87081], .contexts [
        ⟨51647, false, false, [23090], [88567]⟩,
        ⟨51774, true, false, [23090], []⟩,
        ⟨51597, false, false, [23090], [88567]⟩,
        ⟨8, true, false, [23090, 23092, 88567], []⟩,
        ⟨51776, false, false, [23090, 23092], [1]⟩,
        ⟨40146, false, false, [23090], []⟩,
        ⟨40249, false, false, [23090], []⟩,
        ⟨40145, false, false, [23090], []⟩,
        ⟨40145, false, false, [23090], []⟩,
        ⟨51539, true, false, [], [87081]⟩
      ]⟩,
    ⟨[23091], [23092], .contexts [
        ⟨51648, false, false, [], []⟩,
        ⟨51650, false, false, [], []⟩,
        ⟨51650, false, false, [], []⟩
      ]⟩,
    ⟨[87081, 13], [23091, 88565], .contexts [
        ⟨51777, true, false, [23092], [13]⟩,
        ⟨50987, false, false, [23092], []⟩,
        ⟨51096, false, false, [23092], []⟩,
        ⟨51778, true, false, [], [88565]⟩
      ]⟩,
    ⟨[23093, 87079], [23093, 87079], .contexts []⟩,
    ⟨[88569], [23093, 87079], .contexts [
        ⟨51648, false, false, [23090], [88569]⟩,
        ⟨13, false, false, [23090, 23092], [88569]⟩,
        ⟨51095, true, false, [23090, 23092], []⟩,
        ⟨50989, true, false, [23090, 23092], []⟩,
        ⟨51777, false, false, [23090, 23092], [15]⟩,
        ⟨40142, false, false, [23090], []⟩,
        ⟨51780, false, false, [23090, 23092], []⟩,
        ⟨51539, true, false, [], [87079]⟩
      ]⟩,
    ⟨[87079, 1], [23091, 88571], .contexts [
        ⟨51781, true, false, [23092], [1]⟩,
        ⟨50993, false, false, [23092], []⟩,
        ⟨51093, false, false, [23092], []⟩,
        ⟨51778, true, false, [], [88571]⟩
      ]⟩,
    ⟨[22999, 82903], [22999, 82903], .contexts []⟩,
    ⟨[22999, 82903], [22999, 82903], .contexts []⟩,
    ⟨[82903, 15], [22999, 82903], .contexts [
        ⟨51745, false, false, [], []⟩,
        ⟨51747, false, false, [], []⟩,
        ⟨51783, false, false, [], []⟩,
        ⟨51784, false, false, [], []⟩,
        ⟨51784, false, false, [], []⟩
      ]⟩,
    ⟨[82903, 13], [82905], .contexts [
        ⟨17854, false, false, [], []⟩,
        ⟨18081, false, false, [], []⟩,
        ⟨17859, false, false, [], []⟩,
        ⟨17859, false, false, [], []⟩
      ]⟩,
    ⟨[82907], [82907], .contexts []⟩,
    ⟨[82907, 13], [23001, 82907], .contexts [
        ⟨17858, true, false, [], [13]⟩,
        ⟨17854, true, false, [], [15, 13]⟩,
        ⟨51785, true, false, [22998], [13, 15, 13]⟩,
        ⟨6196, false, false, [22998, 82903], []⟩,
        ⟨260, false, false, [22998, 82903], []⟩,
        ⟨51786, false, false, [22998], [15]⟩,
        ⟨17858, false, false, [22998], []⟩,
        ⟨18079, false, false, [22998], []⟩,
        ⟨17863, false, false, [22998], []⟩,
        ⟨17863, false, false, [22998], []⟩,
        ⟨51787, false, false, [22998], []⟩,
        ⟨51514, true, false, [], [82907]⟩
      ]⟩,
    ⟨[23105, 85199], [23105, 85199], .contexts []⟩,
    ⟨[85199, 1], [85199, 1], .contexts []⟩,
    ⟨[85199, 1], [23107, 85727], .contexts [
        ⟨51790, false, false, [], []⟩,
        ⟨51789, true, false, [23104], [1]⟩,
        ⟨30433, true, false, [], [1]⟩,
        ⟨51722, true, false, [23104], [11, 1]⟩,
        ⟨51721, true, false, [23104], [11, 1]⟩,
        ⟨51720, true, false, [23104], [11, 1]⟩,
        ⟨51719, true, false, [23104], [11, 1]⟩,
        ⟨51718, true, false, [23104], [1, 11, 1]⟩,
        ⟨51718, true, false, [23104], [1, 11, 1]⟩,
        ⟨51717, true, false, [23104], [1, 11, 1]⟩,
        ⟨51757, true, false, [23104], [1, 11, 1]⟩,
        ⟨51756, true, false, [23104], [1, 11, 1]⟩,
        ⟨628, false, false, [23104, 85727], []⟩,
        ⟨33271, false, false, [23104], []⟩,
        ⟨51625, true, false, [], [85727]⟩
      ]⟩,
    ⟨[85727, 1], [23105, 85199], .contexts [
        ⟨51791, true, false, [23106], [1]⟩,
        ⟨8, false, false, [23106, 85199], []⟩,
        ⟨51627, true, false, [], [85199]⟩
      ]⟩,
    ⟨[23149, 85201], [23149, 85201], .contexts []⟩,
    ⟨[23149, 85201], [23149, 85201], .contexts []⟩,
    ⟨[85199, 3], [85199, 3], .contexts []⟩,
    ⟨[23148], [23148], .contexts []⟩,
    ⟨[85199, 3], [23147, 85809], .contexts [
        ⟨51795, false, false, [], []⟩,
        ⟨30433, true, false, [], [3]⟩,
        ⟨51794, true, false, [23148], [11, 3]⟩,
        ⟨51794, true, false, [23148], [11, 3]⟩,
        ⟨51793, true, false, [23148], [11, 3]⟩,
        ⟨51769, true, false, [23148], [11, 3]⟩,
        ⟨51763, true, false, [23148], [11, 3]⟩,
        ⟨545, false, false, [23148, 85811], []⟩,
        ⟨54, false, false, [23148, 85811], []⟩,
        ⟨44530, false, false, [23148], []⟩,
        ⟨44538, false, false, [23148], []⟩,
        ⟨51796, true, false, [], [85809]⟩,
        ⟨51796, true, false, [], [85809]⟩,
        ⟨51770, true, false, [], [85809]⟩
      ]⟩,
    ⟨[85199, 1], [23107, 85727], .contexts [
        ⟨51790, false, false, [], []⟩,
        ⟨51791, false, false, [], []⟩,
        ⟨51754, false, false, [], []⟩,
        ⟨51755, false, false, [], []⟩,
        ⟨51755, false, false, [], []⟩
      ]⟩,
    ⟨[23107, 85731], [23107, 85731], .contexts []⟩,
    ⟨[23107, 85731], [23107, 85731], .contexts []⟩,
    ⟨[85199], [85199], .contexts []⟩,
    ⟨[85199], [85199], .contexts []⟩,
    ⟨[85731, 15], [23105, 85199], .contexts [
        ⟨51800, true, false, [23106], [15]⟩,
        ⟨51799, true, false, [23106], [15]⟩,
        ⟨33296, true, false, [], [15]⟩,
        ⟨33279, true, false, [], [1, 15]⟩,
        ⟨51798, true, false, [23106], [15, 1, 15]⟩,
        ⟨2185, false, false, [23106, 85199], []⟩,
        ⟨51801, false, false, [23106], []⟩,
        ⟨51802, false, false, [23106], []⟩,
        ⟨51665, true, false, [], [85199]⟩
      ]⟩,
    ⟨[85199, 15], [23107, 85731], .contexts [
        ⟨51803, true, false, [23104], [15]⟩,
        ⟨1, false, false, [23104, 85731], []⟩,
        ⟨51579, true, false, [], [85731]⟩
      ]⟩,
    ⟨[23147, 85809], [23147, 85809], .contexts []⟩,
    ⟨[23147, 85809], [23147, 85809], .contexts []⟩,
    ⟨[85199, 3], [23147, 85809], .contexts [
        ⟨51795, false, false, [], []⟩,
        ⟨51797, false, false, [], []⟩,
        ⟨51805, false, false, [], []⟩,
        ⟨51806, false, false, [], []⟩,
        ⟨51806, false, false, [], []⟩
      ]⟩,
    ⟨[23147, 85807], [23147, 85807], .contexts []⟩,
    ⟨[85197], [85197], .contexts []⟩,
    ⟨[85807, 3], [23149, 85197], .contexts [
        ⟨51808, true, false, [23146], [3]⟩,
        ⟨33498, true, false, [], [3]⟩,
        ⟨51807, true, false, [23146], [9, 3]⟩,
        ⟨573, false, false, [23146, 85199], []⟩,
        ⟨47, false, false, [23146, 85199], []⟩,
        ⟨30521, false, false, [23146], []⟩,
        ⟨30522, false, false, [23146], []⟩,
        ⟨30428, false, false, [23146], []⟩,
        ⟨30428, false, false, [23146], []⟩,
        ⟨51809, false, false, [23146], []⟩,
        ⟨51768, true, false, [], [85197]⟩
      ]⟩,
    ⟨[85197, 3], [23147, 85807], .contexts [
        ⟨51810, true, false, [23148], [3]⟩,
        ⟨20, false, false, [23148, 85807], []⟩,
        ⟨51770, true, false, [], [85807]⟩
      ]⟩,
    ⟨[85199, 15], [23107, 85731], .contexts [
        ⟨51804, false, false, [], []⟩,
        ⟨51799, false, false, [], []⟩,
        ⟨51800, false, false, [], []⟩,
        ⟨51800, false, false, [], []⟩
      ]⟩,
    ⟨[23151], [23149, 23107], .source 11640⟩,
    ⟨[85809, 15], [23151, 85733], .contexts [
        ⟨51807, true, false, [23146], [15]⟩,
        ⟨151, false, false, [23146, 85199], []⟩,
        ⟨152, false, false, [23146, 85199], []⟩,
        ⟨51812, false, false, [23146], [3]⟩,
        ⟨33307, false, false, [23146, 23107], []⟩,
        ⟨33320, false, false, [23146, 23107], []⟩,
        ⟨51766, true, false, [], [23107, 85733]⟩,
        ⟨51813, true, false, [], [85733]⟩
      ]⟩,
    ⟨[23153], [23150], .source 11641⟩,
    ⟨[85733, 15], [23153, 85809], .contexts [
        ⟨51814, true, false, [23150], [15]⟩,
        ⟨1, false, false, [23150, 85809], []⟩,
        ⟨51815, true, false, [], [85809]⟩
      ]⟩,
    ⟨[88609], [82705, 3], .source 44369⟩,
    ⟨[82705, 3], [88609], .contexts [
        ⟨51817, true, false, [], []⟩
      ]⟩,
    ⟨[88609, 3], [82705], .contexts [
        ⟨51818, true, false, [], [3]⟩,
        ⟨20, false, false, [82705], []⟩,
        ⟨15591, false, false, [], []⟩
      ]⟩,
    ⟨[88609], [88609], .contexts []⟩,
    ⟨[82705, 3], [88609], .contexts [
        ⟨51818, false, false, [], []⟩,
        ⟨51820, false, false, [], []⟩,
        ⟨51820, false, false, [], []⟩
      ]⟩,
    ⟨[23155], [9933, 543], .source 11642⟩,
    ⟨[23157], [23155, 16635], .source 11643⟩,
    ⟨[88609, 5], [23157, 83911], .contexts [
        ⟨51821, true, false, [], [5]⟩,
        ⟨871, false, false, [82705], []⟩,
        ⟨873, false, false, [82705], []⟩,
        ⟨15599, false, false, [], [3, 5, 3]⟩,
        ⟨15601, false, false, [], [3, 5, 3]⟩,
        ⟨15597, false, false, [], [3, 5, 3]⟩,
        ⟨15598, false, false, [], [3, 5, 3]⟩,
        ⟨15598, false, false, [], [3, 5, 3]⟩,
        ⟨15543, false, false, [9933], [5, 3]⟩,
        ⟨51822, true, false, [], [82699, 5, 3]⟩,
        ⟨20539, false, false, [23155], [3]⟩,
        ⟨23588, false, false, [23155], []⟩,
        ⟨51823, true, false, [], [83911]⟩,
        ⟨23585, false, false, [23157], []⟩
      ]⟩,
    ⟨[88609, 5], [23157, 83911], .contexts [
        ⟨51824, false, false, [], []⟩,
        ⟨13, true, false, [], [23157, 83911]⟩
      ]⟩,
    ⟨[23159], [23156], .source 11644⟩,
    ⟨[83911, 5], [23159, 88609], .contexts [
        ⟨51825, true, false, [23156], [5]⟩,
        ⟨28, false, false, [23156, 88609], []⟩,
        ⟨51826, true, false, [], [88609]⟩
      ]⟩,
    ⟨[15531, 82811], [15531, 82811], .contexts []⟩,
    ⟨[15531, 82811], [15531, 82811], .contexts []⟩,
    ⟨[15531, 87201], [15531, 87201], .contexts []⟩,
    ⟨[15531], [15531], .contexts []⟩,
    ⟨[15531], [15531], .contexts []⟩,
    ⟨[88609, 9], [15531, 87201], .contexts [
        ⟨51821, true, false, [], [9]⟩,
        ⟨669, false, false, [82705], []⟩,
        ⟨670, false, false, [82705], []⟩,
        ⟨16918, false, false, [], [3]⟩,
        ⟨51828, false, false, [], [3]⟩,
        ⟨51829, false, false, [], [3]⟩,
        ⟨51829, false, false, [], [3]⟩,
        ⟨40310, false, false, [15531], []⟩,
        ⟨51830, false, false, [], []⟩,
        ⟨40336, false, false, [15531], []⟩,
        ⟨51832, true, false, [], [87201]⟩,
        ⟨51831, true, false, [], [87201]⟩,
        ⟨13, true, false, [], [15531, 87201]⟩
      ]⟩,
    ⟨[88609], [88609], .contexts []⟩,
    ⟨[88609, 11], [9927, 88609], .contexts [
        ⟨51821, true, false, [], [11]⟩,
        ⟨144, false, false, [82705], []⟩,
        ⟨145, false, false, [82705], []⟩,
        ⟨15606, false, false, [], [3]⟩,
        ⟨15608, false, false, [], [3]⟩,
        ⟨15604, false, false, [], [3]⟩,
        ⟨15605, false, false, [], [3]⟩,
        ⟨15605, false, false, [], [3]⟩,
        ⟨51818, false, false, [9927], []⟩,
        ⟨51834, false, false, [9927], []⟩,
        ⟨15571, true, false, [], [88609]⟩
      ]⟩,
    ⟨[15345, 82719], [15345, 82719], .contexts []⟩,
    ⟨[15345, 82719], [15345, 82719], .contexts []⟩,
    ⟨[23161], [15345, 551], .source 11645⟩,
    ⟨[88609, 13], [23161, 83667], .contexts [
        ⟨51821, true, false, [], [13]⟩,
        ⟨147, false, false, [82705], []⟩,
        ⟨148, false, false, [82705], []⟩,
        ⟨15766, false, false, [], [3]⟩,
        ⟨51836, false, false, [], [3]⟩,
        ⟨51837, false, false, [], [3]⟩,
        ⟨51837, false, false, [], [3]⟩,
        ⟨22523, false, false, [15345], []⟩,
        ⟨51838, true, false, [], [83667]⟩,
        ⟨22518, false, false, [23161], []⟩,
        ⟨13, true, false, [], [23161, 83667]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 810. -/
def y322TCIndexRaw810 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[23163], [23160], .source 11646⟩,
    ⟨[83667, 13], [23163, 88609], .contexts [
        ⟨51839, true, false, [23160], [13]⟩,
        ⟨59, false, false, [23160, 88609], []⟩,
        ⟨51840, true, false, [], [88609]⟩
      ]⟩,
    ⟨[9933, 83155], [9933, 83155], .contexts []⟩,
    ⟨[9933, 83155], [9933, 83155], .contexts []⟩,
    ⟨[88609, 15], [23155, 84381], .contexts [
        ⟨51821, true, false, [], [15]⟩,
        ⟨151, false, false, [82705], []⟩,
        ⟨152, false, false, [82705], []⟩,
        ⟨19305, false, false, [], [3]⟩,
        ⟨51842, false, false, [], [3]⟩,
        ⟨51843, false, false, [], [3]⟩,
        ⟨51843, false, false, [], [3]⟩,
        ⟨26689, false, false, [9933], []⟩,
        ⟨51822, true, false, [], [84381]⟩,
        ⟨26693, false, false, [23155], []⟩,
        ⟨13, true, false, [], [23155, 84381]⟩
      ]⟩,
    ⟨[23165], [23154], .source 11647⟩,
    ⟨[88611], [83905, 11], .source 44370⟩,
    ⟨[83905, 11], [88611], .contexts [
        ⟨51846, true, false, [], []⟩
      ]⟩,
    ⟨[88611, 11], [83905], .contexts [
        ⟨51847, true, false, [], [11]⟩,
        ⟨53, false, false, [83905], []⟩,
        ⟨23370, false, false, [], []⟩
      ]⟩,
    ⟨[88611], [88611], .contexts []⟩,
    ⟨[88611], [88611], .contexts []⟩,
    ⟨[83905, 11], [88611], .contexts [
        ⟨51847, false, false, [], []⟩,
        ⟨51849, false, false, [], []⟩,
        ⟨51850, false, false, [], []⟩,
        ⟨51850, false, false, [], []⟩
      ]⟩,
    ⟨[16681, 88611], [16681, 88611], .contexts []⟩,
    ⟨[88611], [88611], .contexts []⟩,
    ⟨[88611, 3], [16681, 88611], .contexts [
        ⟨51851, true, false, [], [3]⟩,
        ⟨215, false, false, [83905], []⟩,
        ⟨216, false, false, [83905], []⟩,
        ⟨45425, false, false, [], [11]⟩,
        ⟨51847, false, false, [16681], []⟩,
        ⟨51852, false, false, [], []⟩,
        ⟨51853, false, false, [16681], []⟩,
        ⟨13, true, false, [], [16681, 88611]⟩
      ]⟩,
    ⟨[88611, 5], [88611, 5], .contexts []⟩,
    ⟨[88611, 5], [88087], .contexts [
        ⟨51855, false, false, [], []⟩,
        ⟨51851, true, false, [], [5]⟩,
        ⟨642, false, false, [83905], []⟩,
        ⟨643, false, false, [83905], []⟩,
        ⟨45417, false, false, [], [11]⟩,
        ⟨48220, false, false, [21455], []⟩,
        ⟨45350, false, false, [], [21453, 88087]⟩,
        ⟨48232, false, false, [], []⟩,
        ⟨672, true, false, [], [88087]⟩
      ]⟩,
    ⟨[88087, 5], [88611], .contexts [
        ⟨51856, true, false, [], [5]⟩,
        ⟨28, false, false, [88611], []⟩,
        ⟨51850, false, false, [], []⟩
      ]⟩,
    ⟨[16683, 88611], [16683, 88611], .contexts []⟩,
    ⟨[16683, 88611], [16683, 88611], .contexts []⟩,
    ⟨[88611, 7], [88611, 7], .contexts []⟩,
    ⟨[16683], [16683], .contexts [
        ⟨13, false, false, [], [16683]⟩
      ]⟩,
    ⟨[88611, 7], [16683, 88611], .contexts [
        ⟨51860, false, false, [], []⟩,
        ⟨51851, true, false, [], [7]⟩,
        ⟨647, false, false, [83905], []⟩,
        ⟨648, false, false, [83905], []⟩,
        ⟨23670, false, false, [], [11]⟩,
        ⟨51847, false, false, [16683], []⟩,
        ⟨51858, false, false, [], []⟩,
        ⟨51859, false, false, [], []⟩,
        ⟨51853, false, false, [16683], []⟩,
        ⟨51861, true, false, [], [88611]⟩
      ]⟩,
    ⟨[16659, 88611], [16659, 88611], .contexts []⟩,
    ⟨[88611, 9], [16659, 88611], .contexts [
        ⟨51851, true, false, [], [9]⟩,
        ⟨221, false, false, [83905], []⟩,
        ⟨224, false, false, [83905], []⟩,
        ⟨23369, false, false, [], [11, 9, 11]⟩,
        ⟨23397, false, false, [], [11, 9, 11]⟩,
        ⟨23374, false, false, [], [11, 9, 11]⟩,
        ⟨23374, false, false, [], [11, 9, 11]⟩,
        ⟨23373, false, false, [], [9, 11]⟩,
        ⟨30776, false, false, [], [9, 11]⟩,
        ⟨23628, false, false, [], [9, 11]⟩,
        ⟨23628, false, false, [], [9, 11]⟩,
        ⟨30777, false, false, [], [11]⟩,
        ⟨30778, false, false, [], [11]⟩,
        ⟨30779, false, false, [], [11]⟩,
        ⟨30780, false, false, [], [11]⟩,
        ⟨51847, false, false, [16659], []⟩,
        ⟨51863, false, false, [], []⟩,
        ⟨51853, false, false, [16659], []⟩
      ]⟩,
    ⟨[16647, 88611], [16647, 88611], .contexts []⟩,
    ⟨[16647, 88611], [16647, 88611], .contexts []⟩,
    ⟨[16647, 88611], [16647, 88611], .contexts []⟩,
    ⟨[16647], [16647], .contexts [
        ⟨13, false, false, [], [16647]⟩
      ]⟩,
    ⟨[88611, 13], [16647, 88611], .contexts [
        ⟨51851, true, false, [], [13]⟩,
        ⟨227, false, false, [83905], []⟩,
        ⟨228, false, false, [83905], []⟩,
        ⟨45415, false, false, [], [11]⟩,
        ⟨51847, false, false, [16647], []⟩,
        ⟨51865, false, false, [], []⟩,
        ⟨51866, false, false, [], []⟩,
        ⟨51867, false, false, [], []⟩,
        ⟨51853, false, false, [16647], []⟩,
        ⟨51868, true, false, [], [88611]⟩
      ]⟩,
    ⟨[88613], [88611, 1], .source 44371⟩,
    ⟨[88611, 1], [88613], .contexts [
        ⟨51870, true, false, [], []⟩
      ]⟩,
    ⟨[88613, 1], [88611], .contexts [
        ⟨51871, true, false, [], [1]⟩,
        ⟨8, false, false, [88611], []⟩,
        ⟨51850, false, false, [], []⟩
      ]⟩,
    ⟨[88613], [88613], .contexts []⟩,
    ⟨[88613], [88613], .contexts []⟩,
    ⟨[88611, 1], [88613], .contexts [
        ⟨51871, false, false, [], []⟩,
        ⟨51873, false, false, [], []⟩,
        ⟨51874, false, false, [], []⟩,
        ⟨51874, false, false, [], []⟩
      ]⟩,
    ⟨[88085], [88085], .contexts []⟩,
    ⟨[88085], [88085], .contexts [
        ⟨51876, false, false, [], []⟩
      ]⟩,
    ⟨[88085], [88085], .contexts [
        ⟨672, true, false, [], [88085]⟩
      ]⟩,
    ⟨[88613, 5], [88085], .contexts [
        ⟨51875, true, false, [], [5]⟩,
        ⟨98, false, false, [88611], []⟩,
        ⟨99, false, false, [88611], []⟩,
        ⟨51855, false, false, [], [1]⟩,
        ⟨51856, false, false, [], [1]⟩,
        ⟨48214, false, false, [], [1]⟩,
        ⟨48215, false, false, [], [1]⟩,
        ⟨48215, false, false, [], [1]⟩,
        ⟨48213, false, false, [], []⟩,
        ⟨48204, false, false, [], []⟩,
        ⟨48205, false, false, [], []⟩,
        ⟨48205, false, false, [], []⟩,
        ⟨51877, false, false, [], []⟩,
        ⟨51878, false, false, [], []⟩
      ]⟩,
    ⟨[88085, 5], [88613], .contexts [
        ⟨51879, true, false, [], [5]⟩,
        ⟨28, false, false, [88613], []⟩,
        ⟨51874, false, false, [], []⟩
      ]⟩,
    ⟨[16683, 88613], [16683, 88613], .contexts []⟩,
    ⟨[16683, 88613], [16683, 88613], .contexts []⟩,
    ⟨[88613, 7], [88613, 7], .contexts []⟩,
    ⟨[88613], [88613], .contexts []⟩,
    ⟨[88613, 7], [16683, 88613], .contexts [
        ⟨51883, false, false, [], []⟩,
        ⟨51875, true, false, [], [7]⟩,
        ⟨104, false, false, [88611], []⟩,
        ⟨105, false, false, [88611], []⟩,
        ⟨51860, false, false, [], [1]⟩,
        ⟨51862, false, false, [], [1]⟩,
        ⟨51858, false, false, [], [1]⟩,
        ⟨51859, false, false, [], [1]⟩,
        ⟨51859, false, false, [], [1]⟩,
        ⟨51871, false, false, [16683], []⟩,
        ⟨51881, false, false, [], []⟩,
        ⟨51882, false, false, [], []⟩,
        ⟨51884, false, false, [16683], []⟩,
        ⟨51861, true, false, [], [88613]⟩
      ]⟩,
    ⟨[88613, 11], [83903], .contexts [
        ⟨51875, true, false, [], [11]⟩,
        ⟨110, false, false, [88611], []⟩,
        ⟨111, false, false, [88611], []⟩,
        ⟨51848, false, false, [], [1]⟩,
        ⟨23399, false, false, [], [1]⟩,
        ⟨23370, false, false, [], [1]⟩,
        ⟨23370, false, false, [], [1]⟩,
        ⟨23400, false, false, [], []⟩,
        ⟨23401, false, false, [], []⟩,
        ⟨23366, false, false, [], []⟩,
        ⟨23366, false, false, [], []⟩,
        ⟨23671, false, false, [], []⟩,
        ⟨672, true, false, [], [83903]⟩
      ]⟩,
    ⟨[83903, 11], [88613], .contexts [
        ⟨51886, true, false, [], [11]⟩,
        ⟨53, false, false, [88613], []⟩,
        ⟨51874, false, false, [], []⟩
      ]⟩,
    ⟨[88615], [88613, 13], .source 44372⟩,
    ⟨[88613, 13], [88615], .contexts [
        ⟨51888, true, false, [], []⟩
      ]⟩,
    ⟨[88615, 13], [88613], .contexts [
        ⟨51889, true, false, [], [13]⟩,
        ⟨59, false, false, [88613], []⟩,
        ⟨51874, false, false, [], []⟩
      ]⟩,
    ⟨[88613, 13], [88615], .contexts [
        ⟨51889, false, false, [], []⟩
      ]⟩,
    ⟨[88615], [88615], .contexts []⟩,
    ⟨[88615], [88615], .contexts []⟩,
    ⟨[88613, 13], [88615], .contexts [
        ⟨51891, false, false, [], []⟩,
        ⟨51892, false, false, [], []⟩,
        ⟨51893, false, false, [], []⟩,
        ⟨51893, false, false, [], []⟩
      ]⟩,
    ⟨[16647, 88613], [16647, 88613], .contexts []⟩,
    ⟨[16647, 88613], [16647, 88613], .contexts []⟩,
    ⟨[16647, 88613], [16647, 88613], .contexts []⟩,
    ⟨[16647, 88615], [16647, 88615], .contexts []⟩,
    ⟨[16647, 88615], [16647, 88615], .contexts []⟩,
    ⟨[16647, 88615], [16647, 88615], .contexts []⟩,
    ⟨[88615, 1], [88615, 1], .contexts []⟩,
    ⟨[88615], [88615], .contexts []⟩,
    ⟨[88615, 1], [16647, 88615], .contexts [
        ⟨51901, false, false, [], []⟩,
        ⟨51894, true, false, [], [1]⟩,
        ⟨246, false, false, [88613], []⟩,
        ⟨249, false, false, [88613], []⟩,
        ⟨51872, false, false, [], [13, 1, 13]⟩,
        ⟨51849, false, false, [], [13, 1, 13]⟩,
        ⟨51850, false, false, [], [13, 1, 13]⟩,
        ⟨51850, false, false, [], [13, 1, 13]⟩,
        ⟨51869, false, false, [], [1, 13]⟩,
        ⟨51865, false, false, [], [1, 13]⟩,
        ⟨51867, false, false, [], [1, 13]⟩,
        ⟨51867, false, false, [], [1, 13]⟩,
        ⟨51871, false, false, [16647], [13]⟩,
        ⟨51895, false, false, [], [13]⟩,
        ⟨51896, false, false, [], [13]⟩,
        ⟨51897, false, false, [], [13]⟩,
        ⟨51889, false, false, [16647], []⟩,
        ⟨51898, false, false, [], []⟩,
        ⟨51899, false, false, [], []⟩,
        ⟨51900, false, false, [], []⟩,
        ⟨51902, false, false, [16647], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 811. -/
def y322TCIndexRaw811 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88615, 1], [16647, 88615], .contexts [
        ⟨51903, false, false, [], []⟩,
        ⟨51868, true, false, [], [88615]⟩
      ]⟩,
    ⟨[16683, 88615], [16683, 88615], .contexts []⟩,
    ⟨[16683, 88615], [16683, 88615], .contexts []⟩,
    ⟨[88615, 7], [88615, 7], .contexts []⟩,
    ⟨[88615, 7], [16683, 88615], .contexts [
        ⟨51907, false, false, [], []⟩,
        ⟨51894, true, false, [], [7]⟩,
        ⟨73, false, false, [88613], []⟩,
        ⟨74, false, false, [88613], []⟩,
        ⟨51883, false, false, [], [13]⟩,
        ⟨51885, false, false, [], [13]⟩,
        ⟨51881, false, false, [], [13]⟩,
        ⟨51882, false, false, [], [13]⟩,
        ⟨51882, false, false, [], [13]⟩,
        ⟨51889, false, false, [16683], []⟩,
        ⟨51905, false, false, [], []⟩,
        ⟨51906, false, false, [], []⟩,
        ⟨51902, false, false, [16683], []⟩,
        ⟨51861, true, false, [], [88615]⟩
      ]⟩,
    ⟨[88617], [88615, 15], .source 44373⟩,
    ⟨[88615, 15], [88617], .contexts [
        ⟨51909, true, false, [], []⟩
      ]⟩,
    ⟨[88617, 15], [88615], .contexts [
        ⟨51910, true, false, [], [15]⟩,
        ⟨1, false, false, [88615], []⟩,
        ⟨51893, false, false, [], []⟩
      ]⟩,
    ⟨[88615, 15], [88617], .contexts [
        ⟨51910, false, false, [], []⟩
      ]⟩,
    ⟨[88617], [88617], .contexts []⟩,
    ⟨[88617], [88617], .contexts []⟩,
    ⟨[88615, 15], [88617], .contexts [
        ⟨51912, false, false, [], []⟩,
        ⟨51913, false, false, [], []⟩,
        ⟨51914, false, false, [], []⟩,
        ⟨51914, false, false, [], []⟩
      ]⟩,
    ⟨[16647, 88617], [16647, 88617], .contexts []⟩,
    ⟨[16647, 88617], [16647, 88617], .contexts []⟩,
    ⟨[88617, 1], [88617, 1], .contexts []⟩,
    ⟨[88617], [88617], .contexts []⟩,
    ⟨[88617, 1], [16647, 88617], .contexts [
        ⟨51918, false, false, [], []⟩,
        ⟨51915, true, false, [], [1]⟩,
        ⟨7, false, false, [88615], []⟩,
        ⟨11, false, false, [88615], []⟩,
        ⟨51901, false, false, [], [15]⟩,
        ⟨51904, false, false, [], [15]⟩,
        ⟨51898, false, false, [], [15]⟩,
        ⟨51900, false, false, [], [15]⟩,
        ⟨51900, false, false, [], [15]⟩,
        ⟨51910, false, false, [16647], []⟩,
        ⟨51916, false, false, [], []⟩,
        ⟨51917, false, false, [], []⟩,
        ⟨51919, false, false, [16647], []⟩,
        ⟨51868, true, false, [], [88617]⟩
      ]⟩,
    ⟨[16683, 88617], [16683, 88617], .contexts []⟩,
    ⟨[16683, 88617], [16683, 88617], .contexts []⟩,
    ⟨[88617, 7], [88617, 7], .contexts []⟩,
    ⟨[88617, 7], [16683, 88617], .contexts [
        ⟨51923, false, false, [], []⟩,
        ⟨51915, true, false, [], [7]⟩,
        ⟨37, false, false, [88615], []⟩,
        ⟨40, false, false, [88615], []⟩,
        ⟨51907, false, false, [], [15]⟩,
        ⟨51908, false, false, [], [15]⟩,
        ⟨51905, false, false, [], [15]⟩,
        ⟨51906, false, false, [], [15]⟩,
        ⟨51906, false, false, [], [15]⟩,
        ⟨51910, false, false, [16683], []⟩,
        ⟨51921, false, false, [], []⟩,
        ⟨51922, false, false, [], []⟩,
        ⟨51919, false, false, [16683], []⟩,
        ⟨51861, true, false, [], [88617]⟩
      ]⟩,
    ⟨[88619], [88617, 3], .source 44374⟩,
    ⟨[88617, 3], [88619], .contexts [
        ⟨51925, true, false, [], []⟩
      ]⟩,
    ⟨[88619, 3], [88617], .contexts [
        ⟨51926, true, false, [], [3]⟩,
        ⟨20, false, false, [88617], []⟩,
        ⟨51914, false, false, [], []⟩
      ]⟩,
    ⟨[88619], [88619], .contexts []⟩,
    ⟨[88619], [88619], .contexts []⟩,
    ⟨[88617, 3], [88619], .contexts [
        ⟨51926, false, false, [], []⟩,
        ⟨51928, false, false, [], []⟩,
        ⟨51929, false, false, [], []⟩,
        ⟨51929, false, false, [], []⟩
      ]⟩,
    ⟨[16683, 88619], [16683, 88619], .contexts []⟩,
    ⟨[16683, 88619], [16683, 88619], .contexts []⟩,
    ⟨[88619, 7], [88619, 7], .contexts []⟩,
    ⟨[88619], [88619], .contexts []⟩,
    ⟨[88619, 7], [16683, 88619], .contexts [
        ⟨51933, false, false, [], []⟩,
        ⟨51930, true, false, [], [7]⟩,
        ⟨140, false, false, [88617], []⟩,
        ⟨141, false, false, [88617], []⟩,
        ⟨51923, false, false, [], [3]⟩,
        ⟨51924, false, false, [], [3]⟩,
        ⟨51921, false, false, [], [3]⟩,
        ⟨51922, false, false, [], [3]⟩,
        ⟨51922, false, false, [], [3]⟩,
        ⟨51926, false, false, [16683], []⟩,
        ⟨51931, false, false, [], []⟩,
        ⟨51932, false, false, [], []⟩,
        ⟨51934, false, false, [16683], []⟩,
        ⟨51861, true, false, [], [88619]⟩
      ]⟩,
    ⟨[88621], [88619, 5], .source 44375⟩,
    ⟨[88619, 5], [88621], .contexts [
        ⟨51936, true, false, [], []⟩
      ]⟩,
    ⟨[88621, 5], [88619], .contexts [
        ⟨51937, true, false, [], [5]⟩,
        ⟨28, false, false, [88619], []⟩,
        ⟨51929, false, false, [], []⟩
      ]⟩,
    ⟨[88623], [88621, 1], .source 44376⟩,
    ⟨[88621, 1], [88623], .contexts [
        ⟨51939, true, false, [], []⟩
      ]⟩,
    ⟨[88621], [88621], .contexts []⟩,
    ⟨[88625], [88623, 9], .source 44377⟩,
    ⟨[88623, 9], [88625], .contexts [
        ⟨51942, true, false, [], []⟩
      ]⟩,
    ⟨[88623], [88623], .contexts []⟩,
    ⟨[88627], [88625, 11], .source 44378⟩,
    ⟨[88625, 11], [88627], .contexts [
        ⟨51945, true, false, [], []⟩
      ]⟩,
    ⟨[88625], [88625], .contexts []⟩,
    ⟨[88629], [88627, 1], .source 44379⟩,
    ⟨[88627, 1], [88629], .contexts [
        ⟨51948, true, false, [], []⟩
      ]⟩,
    ⟨[88627], [88627], .contexts []⟩,
    ⟨[88629, 1], [88627], .contexts [
        ⟨51949, true, false, [], [1]⟩,
        ⟨8, false, false, [88627], []⟩,
        ⟨51950, false, false, [], []⟩
      ]⟩,
    ⟨[88631], [88629, 13], .source 44380⟩,
    ⟨[88629, 13], [88631], .contexts [
        ⟨51952, true, false, [], []⟩
      ]⟩,
    ⟨[88629], [88629], .contexts []⟩,
    ⟨[88631, 13], [88629], .contexts [
        ⟨51953, true, false, [], [13]⟩,
        ⟨59, false, false, [88629], []⟩,
        ⟨51954, false, false, [], []⟩
      ]⟩,
    ⟨[88633], [88631, 15], .source 44381⟩,
    ⟨[88631, 15], [88633], .contexts [
        ⟨51956, true, false, [], []⟩
      ]⟩,
    ⟨[88631], [88631], .contexts []⟩,
    ⟨[88633, 15], [88631], .contexts [
        ⟨51957, true, false, [], [15]⟩,
        ⟨1, false, false, [88631], []⟩,
        ⟨51958, false, false, [], []⟩
      ]⟩,
    ⟨[88635], [88633, 1], .source 44382⟩,
    ⟨[88633, 1], [88635], .contexts [
        ⟨51960, true, false, [], []⟩
      ]⟩,
    ⟨[88633], [88633], .contexts []⟩,
    ⟨[88637], [88635, 3], .source 44383⟩,
    ⟨[88635, 3], [88637], .contexts [
        ⟨51963, true, false, [], []⟩
      ]⟩,
    ⟨[88635], [88635], .contexts []⟩,
    ⟨[88637, 3], [88635], .contexts [
        ⟨51964, true, false, [], [3]⟩,
        ⟨20, false, false, [88635], []⟩,
        ⟨51965, false, false, [], []⟩
      ]⟩,
    ⟨[88639], [88637, 5], .source 44384⟩]

/-- Exact literal claimed equations and contextual derivations, block 812. -/
def y322TCIndexRaw812 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88637, 5], [88639], .contexts [
        ⟨51967, true, false, [], []⟩
      ]⟩,
    ⟨[88637], [88637], .contexts []⟩,
    ⟨[88639, 5], [88637], .contexts [
        ⟨51968, true, false, [], [5]⟩,
        ⟨28, false, false, [88637], []⟩,
        ⟨51969, false, false, [], []⟩
      ]⟩,
    ⟨[88641], [88639, 1], .source 44385⟩,
    ⟨[88639, 1], [88641], .contexts [
        ⟨51971, true, false, [], []⟩
      ]⟩,
    ⟨[88639], [88639], .contexts []⟩,
    ⟨[88641, 1], [88639], .contexts [
        ⟨51972, true, false, [], [1]⟩,
        ⟨8, false, false, [88639], []⟩,
        ⟨51973, false, false, [], []⟩
      ]⟩,
    ⟨[88643], [88641, 9], .source 44386⟩,
    ⟨[88641, 9], [88643], .contexts [
        ⟨51975, true, false, [], []⟩
      ]⟩,
    ⟨[88641], [88641], .contexts []⟩,
    ⟨[88643, 9], [88641], .contexts [
        ⟨51976, true, false, [], [9]⟩,
        ⟨46, false, false, [88641], []⟩,
        ⟨51977, false, false, [], []⟩
      ]⟩,
    ⟨[88645], [88643, 11], .source 44387⟩,
    ⟨[88643, 11], [88645], .contexts [
        ⟨51979, true, false, [], []⟩
      ]⟩,
    ⟨[88643], [88643], .contexts []⟩,
    ⟨[88645, 11], [88643], .contexts [
        ⟨51980, true, false, [], [11]⟩,
        ⟨53, false, false, [88643], []⟩,
        ⟨51981, false, false, [], []⟩
      ]⟩,
    ⟨[88647], [88645, 1], .source 44388⟩,
    ⟨[88645, 1], [88647], .contexts [
        ⟨51983, true, false, [], []⟩
      ]⟩,
    ⟨[88645], [88645], .contexts []⟩,
    ⟨[88649], [88647, 13], .source 44389⟩,
    ⟨[88647, 13], [88649], .contexts [
        ⟨51986, true, false, [], []⟩
      ]⟩,
    ⟨[88647], [88647], .contexts []⟩,
    ⟨[88649, 13], [88647], .contexts [
        ⟨51987, true, false, [], [13]⟩,
        ⟨59, false, false, [88647], []⟩,
        ⟨51988, false, false, [], []⟩
      ]⟩,
    ⟨[88651], [88649, 15], .source 44390⟩,
    ⟨[88649, 15], [88651], .contexts [
        ⟨51990, true, false, [], []⟩
      ]⟩,
    ⟨[88649], [88649], .contexts []⟩,
    ⟨[88651, 15], [88649], .contexts [
        ⟨51991, true, false, [], [15]⟩,
        ⟨1, false, false, [88649], []⟩,
        ⟨51992, false, false, [], []⟩
      ]⟩,
    ⟨[88653], [88651, 1], .source 44391⟩,
    ⟨[88651, 1], [88653], .contexts [
        ⟨51994, true, false, [], []⟩
      ]⟩,
    ⟨[88651], [88651], .contexts []⟩,
    ⟨[88653, 1], [88651], .contexts [
        ⟨51995, true, false, [], [1]⟩,
        ⟨8, false, false, [88651], []⟩,
        ⟨51996, false, false, [], []⟩
      ]⟩,
    ⟨[88655], [88653, 3], .source 44392⟩,
    ⟨[88653, 3], [88655], .contexts [
        ⟨51998, true, false, [], []⟩
      ]⟩,
    ⟨[88653], [88653], .contexts []⟩,
    ⟨[88655, 3], [88653], .contexts [
        ⟨51999, true, false, [], [3]⟩,
        ⟨20, false, false, [88653], []⟩,
        ⟨52000, false, false, [], []⟩
      ]⟩,
    ⟨[88657], [88655, 5], .source 44393⟩,
    ⟨[88655, 5], [88657], .contexts [
        ⟨52002, true, false, [], []⟩
      ]⟩,
    ⟨[88655], [88655], .contexts []⟩,
    ⟨[88657, 5], [88655], .contexts [
        ⟨52003, true, false, [], [5]⟩,
        ⟨28, false, false, [88655], []⟩,
        ⟨52004, false, false, [], []⟩
      ]⟩,
    ⟨[88659], [88657, 1], .source 44394⟩,
    ⟨[88657, 1], [88659], .contexts [
        ⟨52006, true, false, [], []⟩
      ]⟩,
    ⟨[88657], [88657], .contexts []⟩,
    ⟨[88659, 1], [88657], .contexts [
        ⟨52007, true, false, [], [1]⟩,
        ⟨8, false, false, [88657], []⟩,
        ⟨52008, false, false, [], []⟩
      ]⟩,
    ⟨[88661], [88659, 9], .source 44395⟩,
    ⟨[88659], [88659], .contexts []⟩,
    ⟨[88661, 9], [88659], .contexts [
        ⟨52010, false, false, [], [9]⟩,
        ⟨46, false, false, [88659], []⟩,
        ⟨52011, false, false, [], []⟩
      ]⟩,
    ⟨[88663], [88661, 11], .source 44396⟩,
    ⟨[88661, 11], [88663], .contexts [
        ⟨52013, true, false, [], []⟩
      ]⟩,
    ⟨[88661], [88661], .contexts []⟩,
    ⟨[88663, 11], [88661], .contexts [
        ⟨52014, true, false, [], [11]⟩,
        ⟨53, false, false, [88661], []⟩,
        ⟨52015, false, false, [], []⟩
      ]⟩,
    ⟨[88665], [88663, 1], .source 44397⟩,
    ⟨[88663, 1], [88665], .contexts [
        ⟨52017, true, false, [], []⟩
      ]⟩,
    ⟨[88663], [88663], .contexts []⟩,
    ⟨[88665, 1], [88663], .contexts [
        ⟨52018, true, false, [], [1]⟩,
        ⟨8, false, false, [88663], []⟩,
        ⟨52019, false, false, [], []⟩
      ]⟩,
    ⟨[88667], [88665, 13], .source 44398⟩,
    ⟨[88665], [88665], .contexts []⟩,
    ⟨[88667, 13], [88665], .contexts [
        ⟨52021, false, false, [], [13]⟩,
        ⟨59, false, false, [88665], []⟩,
        ⟨52022, false, false, [], []⟩
      ]⟩,
    ⟨[88669], [88667, 15], .source 44399⟩,
    ⟨[88667], [88667], .contexts []⟩,
    ⟨[88669, 15], [88667], .contexts [
        ⟨52024, false, false, [], [15]⟩,
        ⟨1, false, false, [88667], []⟩,
        ⟨52025, false, false, [], []⟩
      ]⟩,
    ⟨[88671], [88669, 1], .source 44400⟩,
    ⟨[88669], [88669], .contexts []⟩,
    ⟨[88671, 1], [88669], .contexts [
        ⟨52027, false, false, [], [1]⟩,
        ⟨8, false, false, [88669], []⟩,
        ⟨52028, false, false, [], []⟩
      ]⟩,
    ⟨[88673], [88671, 3], .source 44401⟩,
    ⟨[88671, 3], [88673], .contexts [
        ⟨52030, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 813. -/
def y322TCIndexRaw813 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88671], [88671], .contexts []⟩,
    ⟨[88673, 3], [88671], .contexts [
        ⟨52031, true, false, [], [3]⟩,
        ⟨20, false, false, [88671], []⟩,
        ⟨52032, false, false, [], []⟩
      ]⟩,
    ⟨[88675], [88673, 5], .source 44402⟩,
    ⟨[88673, 5], [88675], .contexts [
        ⟨52034, true, false, [], []⟩
      ]⟩,
    ⟨[88673], [88673], .contexts []⟩,
    ⟨[88675, 5], [88673], .contexts [
        ⟨52035, true, false, [], [5]⟩,
        ⟨28, false, false, [88673], []⟩,
        ⟨52036, false, false, [], []⟩
      ]⟩,
    ⟨[88677], [88675, 1], .source 44403⟩,
    ⟨[88675], [88675], .contexts []⟩,
    ⟨[88677, 1], [88675], .contexts [
        ⟨52038, false, false, [], [1]⟩,
        ⟨8, false, false, [88675], []⟩,
        ⟨52039, false, false, [], []⟩
      ]⟩,
    ⟨[88679], [88677, 9], .source 44404⟩,
    ⟨[88677, 9], [88679], .contexts [
        ⟨52041, true, false, [], []⟩
      ]⟩,
    ⟨[88677], [88677], .contexts []⟩,
    ⟨[88679, 9], [88677], .contexts [
        ⟨52042, true, false, [], [9]⟩,
        ⟨46, false, false, [88677], []⟩,
        ⟨52043, false, false, [], []⟩
      ]⟩,
    ⟨[88681], [88679, 11], .source 44405⟩,
    ⟨[88679, 11], [88681], .contexts [
        ⟨52045, true, false, [], []⟩
      ]⟩,
    ⟨[88679], [88679], .contexts []⟩,
    ⟨[88681, 11], [88679], .contexts [
        ⟨52046, true, false, [], [11]⟩,
        ⟨53, false, false, [88679], []⟩,
        ⟨52047, false, false, [], []⟩
      ]⟩,
    ⟨[88683], [88681, 1], .source 44406⟩,
    ⟨[88681, 1], [88683], .contexts [
        ⟨52049, true, false, [], []⟩
      ]⟩,
    ⟨[88681], [88681], .contexts []⟩,
    ⟨[88683, 1], [88681], .contexts [
        ⟨52050, true, false, [], [1]⟩,
        ⟨8, false, false, [88681], []⟩,
        ⟨52051, false, false, [], []⟩
      ]⟩,
    ⟨[88685], [88683, 13], .source 44407⟩,
    ⟨[88683, 13], [88685], .contexts [
        ⟨52053, true, false, [], []⟩
      ]⟩,
    ⟨[88683], [88683], .contexts []⟩,
    ⟨[88685, 13], [88683], .contexts [
        ⟨52054, true, false, [], [13]⟩,
        ⟨59, false, false, [88683], []⟩,
        ⟨52055, false, false, [], []⟩
      ]⟩,
    ⟨[88687], [88685, 15], .source 44408⟩,
    ⟨[88685, 15], [88687], .contexts [
        ⟨52057, true, false, [], []⟩
      ]⟩,
    ⟨[88685], [88685], .contexts []⟩,
    ⟨[88687, 15], [88685], .contexts [
        ⟨52058, true, false, [], [15]⟩,
        ⟨1, false, false, [88685], []⟩,
        ⟨52059, false, false, [], []⟩
      ]⟩,
    ⟨[88689], [88687, 1], .source 44409⟩,
    ⟨[88687, 1], [88689], .contexts [
        ⟨52061, true, false, [], []⟩
      ]⟩,
    ⟨[88687], [88687], .contexts []⟩,
    ⟨[88689, 1], [88687], .contexts [
        ⟨52062, true, false, [], [1]⟩,
        ⟨8, false, false, [88687], []⟩,
        ⟨52063, false, false, [], []⟩
      ]⟩,
    ⟨[88691], [88689, 3], .source 44410⟩,
    ⟨[88689, 3], [88691], .contexts [
        ⟨52065, true, false, [], []⟩
      ]⟩,
    ⟨[88689], [88689], .contexts []⟩,
    ⟨[88691, 3], [88689], .contexts [
        ⟨52066, true, false, [], [3]⟩,
        ⟨20, false, false, [88689], []⟩,
        ⟨52067, false, false, [], []⟩
      ]⟩,
    ⟨[88693], [88691, 5], .source 44411⟩,
    ⟨[88691, 5], [88693], .contexts [
        ⟨52069, true, false, [], []⟩
      ]⟩,
    ⟨[88691], [88691], .contexts []⟩,
    ⟨[88693, 5], [88691], .contexts [
        ⟨52070, true, false, [], [5]⟩,
        ⟨28, false, false, [88691], []⟩,
        ⟨52071, false, false, [], []⟩
      ]⟩,
    ⟨[88695], [88693, 1], .source 44412⟩,
    ⟨[88693], [88693], .contexts []⟩,
    ⟨[88695, 1], [88693], .contexts [
        ⟨52073, false, false, [], [1]⟩,
        ⟨8, false, false, [88693], []⟩,
        ⟨52074, false, false, [], []⟩
      ]⟩,
    ⟨[88697], [88695, 9], .source 44413⟩,
    ⟨[88695], [88695], .contexts []⟩,
    ⟨[88697, 9], [88695], .contexts [
        ⟨52076, false, false, [], [9]⟩,
        ⟨46, false, false, [88695], []⟩,
        ⟨52077, false, false, [], []⟩
      ]⟩,
    ⟨[88699], [88697, 11], .source 44414⟩,
    ⟨[88697, 11], [88699], .contexts [
        ⟨52079, true, false, [], []⟩
      ]⟩,
    ⟨[88697], [88697], .contexts []⟩,
    ⟨[88699, 11], [88697], .contexts [
        ⟨52080, true, false, [], [11]⟩,
        ⟨53, false, false, [88697], []⟩,
        ⟨52081, false, false, [], []⟩
      ]⟩,
    ⟨[88701], [88699, 1], .source 44415⟩,
    ⟨[88699, 1], [88701], .contexts [
        ⟨52083, true, false, [], []⟩
      ]⟩,
    ⟨[88699], [88699], .contexts []⟩,
    ⟨[88701, 1], [88699], .contexts [
        ⟨52084, true, false, [], [1]⟩,
        ⟨8, false, false, [88699], []⟩,
        ⟨52085, false, false, [], []⟩
      ]⟩,
    ⟨[88703], [88701, 13], .source 44416⟩,
    ⟨[88701, 13], [88703], .contexts [
        ⟨52087, true, false, [], []⟩
      ]⟩,
    ⟨[88701], [88701], .contexts []⟩,
    ⟨[88703, 13], [88701], .contexts [
        ⟨52088, true, false, [], [13]⟩,
        ⟨59, false, false, [88701], []⟩,
        ⟨52089, false, false, [], []⟩
      ]⟩,
    ⟨[88705], [88703, 15], .source 44417⟩,
    ⟨[88703, 15], [88705], .contexts [
        ⟨52091, true, false, [], []⟩
      ]⟩,
    ⟨[88703], [88703], .contexts []⟩,
    ⟨[88705, 15], [88703], .contexts [
        ⟨52092, true, false, [], [15]⟩,
        ⟨1, false, false, [88703], []⟩,
        ⟨52093, false, false, [], []⟩
      ]⟩,
    ⟨[88707], [88705, 1], .source 44418⟩]

/-- Exact literal claimed equations and contextual derivations, block 814. -/
def y322TCIndexRaw814 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88705, 1], [88707], .contexts [
        ⟨52095, true, false, [], []⟩
      ]⟩,
    ⟨[88705], [88705], .contexts []⟩,
    ⟨[88707, 1], [88705], .contexts [
        ⟨52096, true, false, [], [1]⟩,
        ⟨8, false, false, [88705], []⟩,
        ⟨52097, false, false, [], []⟩
      ]⟩,
    ⟨[88707], [88707], .contexts []⟩,
    ⟨[88703], [88703], .contexts []⟩,
    ⟨[88701], [88701], .contexts []⟩,
    ⟨[88699], [88699], .contexts []⟩,
    ⟨[88699, 11], [88697], .contexts [
        ⟨52082, false, false, [], []⟩
      ]⟩,
    ⟨[88695], [88695], .contexts []⟩,
    ⟨[88705, 15, 13, 1, 11, 9], [88695], .contexts [
        ⟨52094, false, false, [], [13, 1, 11, 9]⟩,
        ⟨52100, false, false, [], [13, 1, 11, 9]⟩,
        ⟨52093, false, false, [], [13, 1, 11, 9]⟩,
        ⟨52093, false, false, [], [13, 1, 11, 9]⟩,
        ⟨52090, false, false, [], [1, 11, 9]⟩,
        ⟨52101, false, false, [], [1, 11, 9]⟩,
        ⟨52089, false, false, [], [1, 11, 9]⟩,
        ⟨52089, false, false, [], [1, 11, 9]⟩,
        ⟨52086, false, false, [], [11, 9]⟩,
        ⟨52102, false, false, [], [11, 9]⟩,
        ⟨52085, false, false, [], [11, 9]⟩,
        ⟨52085, false, false, [], [11, 9]⟩,
        ⟨52103, false, false, [], [9]⟩,
        ⟨52081, false, false, [], [9]⟩,
        ⟨52081, false, false, [], [9]⟩,
        ⟨52078, false, false, [], []⟩,
        ⟨52104, false, false, [], []⟩,
        ⟨52077, false, false, [], []⟩,
        ⟨52077, false, false, [], []⟩
      ]⟩,
    ⟨[88693], [88693], .contexts []⟩,
    ⟨[88691], [88691], .contexts []⟩,
    ⟨[88689], [88689], .contexts []⟩,
    ⟨[88689, 1], [88687], .contexts [
        ⟨52064, false, false, [], []⟩
      ]⟩,
    ⟨[88687], [88687], .contexts []⟩,
    ⟨[88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15], [88685], .contexts [
        ⟨52105, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨52075, false, false, [], [5, 3, 1, 15]⟩,
        ⟨52106, false, false, [], [5, 3, 1, 15]⟩,
        ⟨52074, false, false, [], [5, 3, 1, 15]⟩,
        ⟨52074, false, false, [], [5, 3, 1, 15]⟩,
        ⟨52072, false, false, [], [3, 1, 15]⟩,
        ⟨52107, false, false, [], [3, 1, 15]⟩,
        ⟨52071, false, false, [], [3, 1, 15]⟩,
        ⟨52071, false, false, [], [3, 1, 15]⟩,
        ⟨52068, false, false, [], [1, 15]⟩,
        ⟨52108, false, false, [], [1, 15]⟩,
        ⟨52067, false, false, [], [1, 15]⟩,
        ⟨52067, false, false, [], [1, 15]⟩,
        ⟨52109, false, false, [], [15]⟩,
        ⟨52110, false, false, [], [15]⟩,
        ⟨52063, false, false, [], [15]⟩,
        ⟨52063, false, false, [], [15]⟩,
        ⟨52060, false, false, [], []⟩,
        ⟨52059, false, false, [], []⟩,
        ⟨52059, false, false, [], []⟩
      ]⟩,
    ⟨[88683], [88683], .contexts []⟩,
    ⟨[88683, 1], [88681], .contexts [
        ⟨52052, false, false, [], []⟩
      ]⟩,
    ⟨[88681], [88681], .contexts []⟩,
    ⟨[88681, 11], [88679], .contexts [
        ⟨52048, false, false, [], []⟩
      ]⟩,
    ⟨[88679, 9], [88677], .contexts [
        ⟨52044, false, false, [], []⟩
      ]⟩,
    ⟨[88677], [88677], .contexts []⟩,
    ⟨[88677, 1], [88675], .contexts [
        ⟨52040, false, false, [], []⟩
      ]⟩,
    ⟨[88675], [88675], .contexts []⟩,
    ⟨[
      88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1
    ], [88675], .contexts [
        ⟨52111, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨52056, false, false, [], [1, 11, 9, 1]⟩,
        ⟨52112, false, false, [], [1, 11, 9, 1]⟩,
        ⟨52055, false, false, [], [1, 11, 9, 1]⟩,
        ⟨52055, false, false, [], [1, 11, 9, 1]⟩,
        ⟨52113, false, false, [], [11, 9, 1]⟩,
        ⟨52114, false, false, [], [11, 9, 1]⟩,
        ⟨52051, false, false, [], [11, 9, 1]⟩,
        ⟨52051, false, false, [], [11, 9, 1]⟩,
        ⟨52115, false, false, [], [9, 1]⟩,
        ⟨52047, false, false, [], [9, 1]⟩,
        ⟨52047, false, false, [], [9, 1]⟩,
        ⟨52116, false, false, [], [1]⟩,
        ⟨52117, false, false, [], [1]⟩,
        ⟨52043, false, false, [], [1]⟩,
        ⟨52043, false, false, [], [1]⟩,
        ⟨52118, false, false, [], []⟩,
        ⟨52119, false, false, [], []⟩,
        ⟨52039, false, false, [], []⟩,
        ⟨52039, false, false, [], []⟩
      ]⟩,
    ⟨[88673], [88673], .contexts []⟩,
    ⟨[88669], [88669], .contexts []⟩,
    ⟨[88667], [88667], .contexts []⟩,
    ⟨[88665], [88665], .contexts []⟩,
    ⟨[
      88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [88665], .contexts [
        ⟨52120, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨52037, false, false, [], [3, 1, 15, 13]⟩,
        ⟨52121, false, false, [], [3, 1, 15, 13]⟩,
        ⟨52036, false, false, [], [3, 1, 15, 13]⟩,
        ⟨52036, false, false, [], [3, 1, 15, 13]⟩,
        ⟨52033, false, false, [], [1, 15, 13]⟩,
        ⟨52032, false, false, [], [1, 15, 13]⟩,
        ⟨52032, false, false, [], [1, 15, 13]⟩,
        ⟨52029, false, false, [], [15, 13]⟩,
        ⟨52122, false, false, [], [15, 13]⟩,
        ⟨52028, false, false, [], [15, 13]⟩,
        ⟨52028, false, false, [], [15, 13]⟩,
        ⟨52026, false, false, [], [13]⟩,
        ⟨52123, false, false, [], [13]⟩,
        ⟨52025, false, false, [], [13]⟩,
        ⟨52025, false, false, [], [13]⟩,
        ⟨52023, false, false, [], []⟩,
        ⟨52124, false, false, [], []⟩,
        ⟨52022, false, false, [], []⟩,
        ⟨52022, false, false, [], []⟩
      ]⟩,
    ⟨[88663], [88663], .contexts []⟩,
    ⟨[88659], [88659], .contexts []⟩,
    ⟨[88657], [88657], .contexts []⟩,
    ⟨[88657, 5], [88655], .contexts [
        ⟨52005, false, false, [], []⟩
      ]⟩,
    ⟨[
      88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5
    ], [88655], .contexts [
        ⟨52125, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨52020, false, false, [], [11, 9, 1, 5]⟩,
        ⟨52126, false, false, [], [11, 9, 1, 5]⟩,
        ⟨52019, false, false, [], [11, 9, 1, 5]⟩,
        ⟨52019, false, false, [], [11, 9, 1, 5]⟩,
        ⟨52016, false, false, [], [9, 1, 5]⟩,
        ⟨52015, false, false, [], [9, 1, 5]⟩,
        ⟨52015, false, false, [], [9, 1, 5]⟩,
        ⟨52012, false, false, [], [1, 5]⟩,
        ⟨52127, false, false, [], [1, 5]⟩,
        ⟨52011, false, false, [], [1, 5]⟩,
        ⟨52011, false, false, [], [1, 5]⟩,
        ⟨52009, false, false, [], [5]⟩,
        ⟨52128, false, false, [], [5]⟩,
        ⟨52008, false, false, [], [5]⟩,
        ⟨52008, false, false, [], [5]⟩,
        ⟨52129, false, false, [], []⟩,
        ⟨52004, false, false, [], []⟩,
        ⟨52004, false, false, [], []⟩
      ]⟩,
    ⟨[88653], [88653], .contexts []⟩,
    ⟨[88653, 1], [88651], .contexts [
        ⟨51997, false, false, [], []⟩
      ]⟩,
    ⟨[88651], [88651], .contexts []⟩,
    ⟨[88651, 15], [88649], .contexts [
        ⟨51993, false, false, [], []⟩
      ]⟩,
    ⟨[88649], [88649], .contexts []⟩,
    ⟨[88645], [88645], .contexts []⟩,
    ⟨[
      88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1
    ], [88645], .contexts [
        ⟨52130, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨52001, false, false, [], [1, 15, 13, 1]⟩,
        ⟨52131, false, false, [], [1, 15, 13, 1]⟩,
        ⟨52000, false, false, [], [1, 15, 13, 1]⟩,
        ⟨52000, false, false, [], [1, 15, 13, 1]⟩,
        ⟨52132, false, false, [], [15, 13, 1]⟩,
        ⟨52133, false, false, [], [15, 13, 1]⟩,
        ⟨51996, false, false, [], [15, 13, 1]⟩,
        ⟨51996, false, false, [], [15, 13, 1]⟩,
        ⟨52134, false, false, [], [13, 1]⟩,
        ⟨52135, false, false, [], [13, 1]⟩,
        ⟨51992, false, false, [], [13, 1]⟩,
        ⟨51992, false, false, [], [13, 1]⟩,
        ⟨51989, false, false, [], [1]⟩,
        ⟨51988, false, false, [], [1]⟩,
        ⟨51988, false, false, [], [1]⟩,
        ⟨51984, true, false, [], [1]⟩,
        ⟨8, false, false, [88645], []⟩,
        ⟨51985, false, false, [], []⟩,
        ⟨52136, false, false, [], []⟩,
        ⟨51985, false, false, [], []⟩,
        ⟨51985, false, false, [], []⟩
      ]⟩,
    ⟨[88643], [88643], .contexts []⟩,
    ⟨[88643, 9], [88641], .contexts [
        ⟨51978, false, false, [], []⟩
      ]⟩,
    ⟨[88641], [88641], .contexts []⟩,
    ⟨[88639], [88639], .contexts []⟩,
    ⟨[88639, 5], [88637], .contexts [
        ⟨51970, false, false, [], []⟩
      ]⟩,
    ⟨[88637], [88637], .contexts []⟩,
    ⟨[88635], [88635], .contexts []⟩,
    ⟨[
      88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [88635], .contexts [
        ⟨52137, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨51982, false, false, [], [9, 1, 5, 3]⟩,
        ⟨52138, false, false, [], [9, 1, 5, 3]⟩,
        ⟨51981, false, false, [], [9, 1, 5, 3]⟩,
        ⟨51981, false, false, [], [9, 1, 5, 3]⟩,
        ⟨52139, false, false, [], [1, 5, 3]⟩,
        ⟨52140, false, false, [], [1, 5, 3]⟩,
        ⟨51977, false, false, [], [1, 5, 3]⟩,
        ⟨51977, false, false, [], [1, 5, 3]⟩,
        ⟨51974, false, false, [], [5, 3]⟩,
        ⟨52141, false, false, [], [5, 3]⟩,
        ⟨51973, false, false, [], [5, 3]⟩,
        ⟨51973, false, false, [], [5, 3]⟩,
        ⟨52142, false, false, [], [3]⟩,
        ⟨52143, false, false, [], [3]⟩,
        ⟨51969, false, false, [], [3]⟩,
        ⟨51969, false, false, [], [3]⟩,
        ⟨51966, false, false, [], []⟩,
        ⟨52144, false, false, [], []⟩,
        ⟨51965, false, false, [], []⟩,
        ⟨51965, false, false, [], []⟩
      ]⟩,
    ⟨[88633], [88633], .contexts []⟩,
    ⟨[88631], [88631], .contexts []⟩,
    ⟨[88629], [88629], .contexts []⟩,
    ⟨[88627], [88627], .contexts []⟩,
    ⟨[
      88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1
    ], [88627], .contexts [
        ⟨52145, false, false, [], [1, 15, 13, 1]⟩,
        ⟨51961, true, false, [], [1, 15, 13, 1]⟩,
        ⟨8, false, false, [88633], [15, 13, 1]⟩,
        ⟨51962, false, false, [], [15, 13, 1]⟩,
        ⟨52146, false, false, [], [15, 13, 1]⟩,
        ⟨51962, false, false, [], [15, 13, 1]⟩,
        ⟨51962, false, false, [], [15, 13, 1]⟩,
        ⟨51959, false, false, [], [13, 1]⟩,
        ⟨52147, false, false, [], [13, 1]⟩,
        ⟨51958, false, false, [], [13, 1]⟩,
        ⟨51958, false, false, [], [13, 1]⟩,
        ⟨51955, false, false, [], [1]⟩,
        ⟨52148, false, false, [], [1]⟩,
        ⟨51954, false, false, [], [1]⟩,
        ⟨51954, false, false, [], [1]⟩,
        ⟨51951, false, false, [], []⟩,
        ⟨52149, false, false, [], []⟩,
        ⟨51950, false, false, [], []⟩,
        ⟨51950, false, false, [], []⟩
      ]⟩,
    ⟨[88625], [88625], .contexts []⟩,
    ⟨[88623], [88623], .contexts []⟩,
    ⟨[
      88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5
    ], [88619], .contexts [
        ⟨52150, false, false, [], [11, 9, 1, 5]⟩,
        ⟨51946, true, false, [], [11, 9, 1, 5]⟩,
        ⟨53, false, false, [88625], [9, 1, 5]⟩,
        ⟨51947, false, false, [], [9, 1, 5]⟩,
        ⟨52151, false, false, [], [9, 1, 5]⟩,
        ⟨51947, false, false, [], [9, 1, 5]⟩,
        ⟨51947, false, false, [], [9, 1, 5]⟩,
        ⟨51943, true, false, [], [9, 1, 5]⟩,
        ⟨46, false, false, [88623], [1, 5]⟩,
        ⟨51944, false, false, [], [1, 5]⟩,
        ⟨52152, false, false, [], [1, 5]⟩,
        ⟨51944, false, false, [], [1, 5]⟩,
        ⟨51944, false, false, [], [1, 5]⟩,
        ⟨51940, true, false, [], [1, 5]⟩,
        ⟨8, false, false, [88621], [5]⟩,
        ⟨51941, false, false, [], [5]⟩,
        ⟨51941, false, false, [], [5]⟩,
        ⟨51941, false, false, [], [5]⟩,
        ⟨51938, false, false, [], []⟩,
        ⟨51928, false, false, [], []⟩,
        ⟨51929, false, false, [], []⟩,
        ⟨51929, false, false, [], []⟩
      ]⟩,
    ⟨[88617, 1], [16647, 88617], .contexts [
        ⟨51920, false, false, [], []⟩
      ]⟩,
    ⟨[
      88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1
    ], [16647, 88611], .contexts [
        ⟨52153, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨51927, false, false, [], [1, 15, 13, 1]⟩,
        ⟨51913, false, false, [], [1, 15, 13, 1]⟩,
        ⟨51914, false, false, [], [1, 15, 13, 1]⟩,
        ⟨51914, false, false, [], [1, 15, 13, 1]⟩,
        ⟨52154, false, false, [], [15, 13, 1]⟩,
        ⟨51916, false, false, [], [15, 13, 1]⟩,
        ⟨51917, false, false, [], [15, 13, 1]⟩,
        ⟨51917, false, false, [], [15, 13, 1]⟩,
        ⟨51911, false, false, [16647], [13, 1]⟩,
        ⟨51898, false, false, [], [13, 1]⟩,
        ⟨51899, false, false, [], [13, 1]⟩,
        ⟨51900, false, false, [], [13, 1]⟩,
        ⟨51890, false, false, [16647], [1]⟩,
        ⟨51895, false, false, [], [1]⟩,
        ⟨51896, false, false, [], [1]⟩,
        ⟨51897, false, false, [], [1]⟩,
        ⟨51872, false, false, [16647], []⟩,
        ⟨51865, false, false, [], []⟩,
        ⟨51866, false, false, [], []⟩,
        ⟨51867, false, false, [], []⟩
      ]⟩,
    ⟨[23167], [16647, 16671], .source 11648⟩,
    ⟨[23169], [23167, 23159], .source 11649⟩,
    ⟨[
      88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3
    ], [23169, 82705], .contexts [
        ⟨52155, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨51848, false, false, [16647], [9, 1, 5, 3]⟩,
        ⟨45413, false, false, [], [9, 1, 5, 3]⟩,
        ⟨45414, false, false, [], [9, 1, 5, 3]⟩,
        ⟨23369, false, false, [16647], [1, 5, 3]⟩,
        ⟨23609, false, false, [], [1, 5, 3]⟩,
        ⟨23610, false, false, [], [1, 5, 3]⟩,
        ⟨23611, false, false, [], [1, 5, 3]⟩,
        ⟨23631, false, false, [16647], [5, 3]⟩,
        ⟨52156, true, false, [], [83911, 5, 3]⟩,
        ⟨51827, false, false, [23167], [3]⟩,
        ⟨52157, true, false, [], [88609, 3]⟩,
        ⟨51819, false, false, [23169], []⟩
      ]⟩,
    ⟨[23171], [23169, 15317], .source 11650⟩]

/-- Exact literal claimed equations and contextual derivations, block 815. -/
def y322TCIndexRaw815 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[23173], [23171, 1075], .source 11651⟩,
    ⟨[23175], [23173, 15301], .source 11652⟩,
    ⟨[23177], [23175, 151], .source 11653⟩,
    ⟨[
      88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [23177, 83155], .contexts [
        ⟨52158, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨15593, false, false, [23169], [15, 13, 1, 11]⟩,
        ⟨19357, false, false, [23169], [13, 1, 11]⟩,
        ⟨52159, true, false, [], [83159, 13, 1, 11]⟩,
        ⟨19354, false, false, [23171], [1, 11]⟩,
        ⟨52160, true, false, [], [83159, 1, 11]⟩,
        ⟨19340, false, false, [23173], [11]⟩,
        ⟨52161, true, false, [], [83155, 11]⟩,
        ⟨19298, false, false, [23175], []⟩,
        ⟨52162, true, false, [], [83155]⟩
      ]⟩,
    ⟨[23179], [23177, 15331], .source 11654⟩,
    ⟨[23181], [23179, 2209], .source 11655⟩,
    ⟨[23183], [23181, 14707], .source 11656⟩,
    ⟨[
      88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1
    ], [23183, 78841], .contexts [
        ⟨52163, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨19292, false, false, [23177], [1, 5, 3, 1]⟩,
        ⟨52164, true, false, [], [82821, 1, 5, 3, 1]⟩,
        ⟨17076, false, false, [23179], [5, 3, 1]⟩,
        ⟨6310, false, false, [23179], [3, 1]⟩,
        ⟨6258, false, false, [23179], [1]⟩,
        ⟨52165, true, false, [], [79185, 1]⟩,
        ⟨14537, false, false, [23181], []⟩,
        ⟨52166, true, false, [], [78841]⟩
      ]⟩,
    ⟨[23185], [23183, 15511], .source 11657⟩,
    ⟨[23187], [23185, 15513], .source 11658⟩,
    ⟨[
      88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [23187, 83129], .contexts [
        ⟨52167, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨16849, false, false, [23183], [13, 1, 11, 9]⟩,
        ⟨19159, false, false, [23183], [1, 11, 9]⟩,
        ⟨19145, false, false, [23183], [11, 9]⟩,
        ⟨52168, true, false, [], [83145, 11, 9]⟩,
        ⟨19139, false, false, [23185], [9]⟩,
        ⟨18940, false, false, [23185], []⟩,
        ⟨52169, true, false, [], [83129]⟩
      ]⟩,
    ⟨[23189], [23187, 15397], .source 11659⟩,
    ⟨[23191], [23189, 15401], .source 11660⟩,
    ⟨[23193], [23191, 1075], .source 11661⟩,
    ⟨[
      88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15
    ], [23193, 83137], .contexts [
        ⟨52170, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨18935, false, false, [23187], [5, 3, 1, 15]⟩,
        ⟨18888, false, false, [23187], [3, 1, 15]⟩,
        ⟨18911, false, false, [23187], [1, 15]⟩,
        ⟨52171, true, false, [], [83125, 1, 15]⟩,
        ⟨19035, false, false, [23189], [15]⟩,
        ⟨52172, true, false, [], [83137, 15]⟩,
        ⟨19059, false, false, [23191], []⟩,
        ⟨52173, true, false, [], [83137]⟩
      ]⟩,
    ⟨[23195], [23193, 15319], .source 11662⟩,
    ⟨[23197], [23195, 9927], .source 11663⟩,
    ⟨[23199], [23197, 15531], .source 11664⟩,
    ⟨[23201], [23199, 7355], .source 11665⟩,
    ⟨[
      88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1
    ], [23201, 82817], .contexts [
        ⟨52174, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨19056, false, false, [23193], [1, 11, 9, 1]⟩,
        ⟨52175, true, false, [], [82693, 1, 11, 9, 1]⟩,
        ⟨15581, false, false, [23195], [11, 9, 1]⟩,
        ⟨15586, false, false, [23195], [9, 1]⟩,
        ⟨52176, true, false, [], [82703, 9, 1]⟩,
        ⟨16949, false, false, [23197], [1]⟩,
        ⟨52177, true, false, [], [82813, 1]⟩,
        ⟨17009, false, false, [23199], []⟩,
        ⟨52178, true, false, [], [82817]⟩
      ]⟩,
    ⟨[23203], [23201, 15545], .source 11666⟩,
    ⟨[23205], [23203, 11217], .source 11667⟩,
    ⟨[23207], [23205, 15233], .source 11668⟩,
    ⟨[23209], [23207, 15993], .source 11669⟩,
    ⟨[
      88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [23209, 83173], .contexts [
        ⟨52179, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨17014, false, false, [23201], [3, 1, 15, 13]⟩,
        ⟨52180, true, false, [], [82671, 3, 1, 15, 13]⟩,
        ⟨15184, false, false, [23203], [1, 15, 13]⟩,
        ⟨52181, true, false, [], [82665, 1, 15, 13]⟩,
        ⟨15121, false, false, [23205], [15, 13]⟩,
        ⟨52182, true, false, [], [82665, 15, 13]⟩,
        ⟨15129, false, false, [23207], [13]⟩,
        ⟨19550, false, false, [23207], []⟩,
        ⟨52183, true, false, [], [83173]⟩
      ]⟩,
    ⟨[23211], [23209, 16023], .source 11670⟩,
    ⟨[23213], [23211, 15987], .source 11671⟩,
    ⟨[23215], [23213, 16377], .source 11672⟩,
    ⟨[
      88705, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5
    ], [23215, 83503], .contexts [
        ⟨52184, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨19600, false, false, [23209], [11, 9, 1, 5]⟩,
        ⟨19764, false, false, [23209], [9, 1, 5]⟩,
        ⟨19785, false, false, [23209], [1, 5]⟩,
        ⟨52185, true, false, [], [83193, 1, 5]⟩,
        ⟨19773, false, false, [23211], [5]⟩,
        ⟨52186, true, false, [], [82791, 5]⟩,
        ⟨21679, false, false, [23213], []⟩,
        ⟨52187, true, false, [], [83503]⟩
      ]⟩,
    ⟨[88707, 3], [88707, 3], .contexts []⟩,
    ⟨[88707, 3], [23215, 83503], .contexts [
        ⟨52189, false, false, [], []⟩,
        ⟨52099, true, false, [], [3]⟩,
        ⟨52099, true, false, [], [3]⟩,
        ⟨52096, true, false, [], [3]⟩,
        ⟨1908, false, false, [88705], []⟩,
        ⟨1909, false, false, [88705], []⟩,
        ⟨52188, false, false, [], []⟩,
        ⟨21693, false, false, [23215], []⟩,
        ⟨13, true, false, [], [23215, 83503]⟩
      ]⟩,
    ⟨[23217], [23214], .source 11673⟩,
    ⟨[83503, 3], [23217, 88707], .contexts [
        ⟨52190, true, false, [23214], [3]⟩,
        ⟨20, false, false, [23214, 88707], []⟩,
        ⟨52191, true, false, [], [88707]⟩
      ]⟩,
    ⟨[23215, 83503], [23215, 83503], .contexts []⟩,
    ⟨[23215, 83503], [23215, 83503], .contexts []⟩,
    ⟨[88707, 3], [23215, 83503], .contexts [
        ⟨52189, false, false, [], []⟩,
        ⟨52190, false, false, [], []⟩,
        ⟨52193, false, false, [], []⟩,
        ⟨52194, false, false, [], []⟩,
        ⟨52194, false, false, [], []⟩
      ]⟩,
    ⟨[23215, 86807], [23215, 86807], .contexts []⟩,
    ⟨[88707], [88707], .contexts []⟩,
    ⟨[88707], [88707], .contexts []⟩,
    ⟨[23214], [23214], .contexts []⟩,
    ⟨[86807, 13], [23217, 88707], .contexts [
        ⟨52196, true, false, [23214], [13]⟩,
        ⟨39086, true, false, [], [13]⟩,
        ⟨21691, true, false, [], [3, 13]⟩,
        ⟨52195, true, false, [23214], [13, 3, 13]⟩,
        ⟨1930, false, false, [23214, 88707], []⟩,
        ⟨52197, false, false, [23214], []⟩,
        ⟨52198, false, false, [23214], []⟩,
        ⟨52199, true, false, [], [88707]⟩,
        ⟨52199, true, false, [], [88707]⟩,
        ⟨52191, true, false, [], [88707]⟩
      ]⟩,
    ⟨[23219], [23215, 15477], .source 11674⟩,
    ⟨[23221], [23219, 23217], .source 11675⟩,
    ⟨[88707, 15], [88707, 15], .contexts []⟩,
    ⟨[23223], [23220], .source 11676⟩,
    ⟨[23223], [23223], .contexts []⟩,
    ⟨[23220], [23220], .contexts []⟩,
    ⟨[88707, 15], [23223, 88707], .contexts [
        ⟨52203, false, false, [], []⟩,
        ⟨52202, false, false, [23220], [88707, 15]⟩,
        ⟨52192, true, false, [23220, 23219], [15]⟩,
        ⟨52201, false, false, [23220], [83503, 3, 15]⟩,
        ⟨21694, true, false, [23220, 23215], [3, 15]⟩,
        ⟨52195, true, false, [23220], [15, 3, 15]⟩,
        ⟨1659, false, false, [23220, 88707], []⟩,
        ⟨52197, false, false, [23220], []⟩,
        ⟨52198, false, false, [23220], []⟩,
        ⟨52206, true, false, [], [88707]⟩,
        ⟨52206, true, false, [], [88707]⟩,
        ⟨52204, true, false, [], [88707]⟩,
        ⟨52205, true, false, [], [88707]⟩
      ]⟩,
    ⟨[23223, 88707], [23223, 88707], .contexts []⟩,
    ⟨[23223, 88707], [23223, 88707], .contexts []⟩,
    ⟨[23223, 88703], [23223, 88703], .contexts []⟩,
    ⟨[23223, 88703], [23223, 88703], .contexts []⟩,
    ⟨[23222], [23222], .contexts []⟩,
    ⟨[88703, 1], [23221, 88707], .contexts [
        ⟨52211, true, false, [23222], [1]⟩,
        ⟨52210, true, false, [23222], [1]⟩,
        ⟨52094, true, false, [], [1]⟩,
        ⟨52098, true, false, [], [15, 1]⟩,
        ⟨52209, true, false, [23222], [1, 15, 1]⟩,
        ⟨52209, true, false, [23222], [1, 15, 1]⟩,
        ⟨52208, true, false, [23222], [1, 15, 1]⟩,
        ⟨52207, true, false, [23222], [1, 15, 1]⟩,
        ⟨52203, true, false, [23222], [1, 15, 1]⟩,
        ⟨504, false, false, [23222, 88707], []⟩,
        ⟨52197, false, false, [23222], []⟩,
        ⟨52198, false, false, [23222], []⟩,
        ⟨52212, true, false, [], [88707]⟩,
        ⟨52212, true, false, [], [88707]⟩,
        ⟨52204, false, true, [], [88707]⟩
      ]⟩,
    ⟨[88707, 1], [88705], .contexts [
        ⟨52098, false, false, [], []⟩
      ]⟩,
    ⟨[88709], [86795, 11], .source 44419⟩,
    ⟨[86795, 11], [88709], .contexts [
        ⟨52215, true, false, [], []⟩
      ]⟩,
    ⟨[88709, 11], [86795], .contexts [
        ⟨52216, true, false, [], [11]⟩,
        ⟨53, false, false, [86795], []⟩,
        ⟨38774, false, false, [], []⟩
      ]⟩,
    ⟨[88709], [88709], .contexts []⟩,
    ⟨[88709], [88709], .contexts []⟩,
    ⟨[86795, 11], [88709], .contexts [
        ⟨52216, false, false, [], []⟩,
        ⟨52218, false, false, [], []⟩,
        ⟨52219, false, false, [], []⟩,
        ⟨52219, false, false, [], []⟩
      ]⟩,
    ⟨[86795, 5], [86793], .contexts [
        ⟨38788, false, false, [], []⟩,
        ⟨38789, false, false, [], []⟩,
        ⟨38770, false, false, [], []⟩,
        ⟨38770, false, false, [], []⟩
      ]⟩,
    ⟨[19463, 84389], [19463, 84389], .contexts []⟩,
    ⟨[19463, 84389], [19463, 84389], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 816. -/
def y322TCIndexRaw816 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88709, 5], [88709, 5], .contexts []⟩,
    ⟨[88709, 5], [19463, 84389], .contexts [
        ⟨52224, false, false, [], []⟩,
        ⟨52220, true, false, [], [5]⟩,
        ⟨642, false, false, [86795], []⟩,
        ⟨643, false, false, [86795], []⟩,
        ⟨52221, false, false, [], [11]⟩,
        ⟨38985, false, false, [], []⟩,
        ⟨52222, false, false, [], []⟩,
        ⟨52223, false, false, [], []⟩,
        ⟨52223, false, false, [], []⟩,
        ⟨38982, false, false, [19463], []⟩,
        ⟨38878, true, false, [], [84389]⟩
      ]⟩,
    ⟨[84389, 5], [19465, 88709], .contexts [
        ⟨52225, true, false, [19462], [5]⟩,
        ⟨28, false, false, [19462, 88709], []⟩,
        ⟨38880, true, false, [], [88709]⟩
      ]⟩,
    ⟨[19479, 86795], [19479, 86795], .contexts []⟩,
    ⟨[19479, 86795], [19479, 86795], .contexts []⟩,
    ⟨[19479, 88709], [19479, 88709], .contexts []⟩,
    ⟨[19479, 88709], [19479, 88709], .contexts []⟩,
    ⟨[88709, 7], [88709, 7], .contexts []⟩,
    ⟨[88709], [88709], .contexts []⟩,
    ⟨[19479], [19479], .contexts [
        ⟨13, false, false, [], [19479]⟩
      ]⟩,
    ⟨[88709, 7], [19479, 88709], .contexts [
        ⟨52231, false, false, [], []⟩,
        ⟨52220, true, false, [], [7]⟩,
        ⟨647, false, false, [86795], []⟩,
        ⟨648, false, false, [86795], []⟩,
        ⟨38971, false, false, [], [11]⟩,
        ⟨38974, false, false, [], [11]⟩,
        ⟨52227, false, false, [], [11]⟩,
        ⟨52228, false, false, [], [11]⟩,
        ⟨52228, false, false, [], [11]⟩,
        ⟨52216, false, false, [19479], []⟩,
        ⟨52229, false, false, [], []⟩,
        ⟨52230, false, false, [], []⟩,
        ⟨52232, false, false, [19479], []⟩,
        ⟨52233, true, false, [], [88709]⟩
      ]⟩,
    ⟨[19493, 88613], [19493, 88613], .contexts []⟩,
    ⟨[19493, 88613], [19493, 88613], .contexts []⟩,
    ⟨[88709, 15], [88709, 15], .contexts []⟩,
    ⟨[88709, 15], [19493, 88613], .contexts [
        ⟨52237, false, false, [], []⟩,
        ⟨52220, true, false, [], [15]⟩,
        ⟨231, false, false, [86795], []⟩,
        ⟨232, false, false, [86795], []⟩,
        ⟨38979, false, false, [], [11]⟩,
        ⟨38975, false, false, [], [11]⟩,
        ⟨38976, false, false, [], [11]⟩,
        ⟨38976, false, false, [], [11]⟩,
        ⟨51887, false, false, [19493], []⟩,
        ⟨52235, false, false, [], []⟩,
        ⟨52236, false, false, [], []⟩,
        ⟨51884, false, false, [19493], []⟩,
        ⟨38962, true, false, [], [88613]⟩
      ]⟩,
    ⟨[88613, 15], [19495, 88709], .contexts [
        ⟨52238, true, false, [19492], [15]⟩,
        ⟨1, false, false, [19492, 88709], []⟩,
        ⟨38925, true, false, [], [88709]⟩
      ]⟩,
    ⟨[88711], [88709, 1], .source 44420⟩,
    ⟨[88709, 1], [88711], .contexts [
        ⟨52240, true, false, [], []⟩
      ]⟩,
    ⟨[88711, 1], [88709], .contexts [
        ⟨52241, true, false, [], [1]⟩,
        ⟨8, false, false, [88709], []⟩,
        ⟨52219, false, false, [], []⟩
      ]⟩,
    ⟨[88711], [88711], .contexts []⟩,
    ⟨[88711], [88711], .contexts []⟩,
    ⟨[88709, 1], [88711], .contexts [
        ⟨52241, false, false, [], []⟩,
        ⟨52243, false, false, [], []⟩,
        ⟨52244, false, false, [], []⟩,
        ⟨52244, false, false, [], []⟩
      ]⟩,
    ⟨[19463, 84387], [19463, 84387], .contexts []⟩,
    ⟨[19463, 84387], [19463, 84387], .contexts []⟩,
    ⟨[88711, 5], [88711, 5], .contexts []⟩,
    ⟨[88711, 5], [19463, 84387], .contexts [
        ⟨52248, false, false, [], []⟩,
        ⟨52245, true, false, [], [5]⟩,
        ⟨98, false, false, [88709], []⟩,
        ⟨99, false, false, [88709], []⟩,
        ⟨52224, false, false, [], [1]⟩,
        ⟨52225, false, false, [], [1]⟩,
        ⟨52222, false, false, [], [1]⟩,
        ⟨52223, false, false, [], [1]⟩,
        ⟨52223, false, false, [], [1]⟩,
        ⟨26729, false, false, [19463], []⟩,
        ⟨52246, false, false, [], []⟩,
        ⟨52247, false, false, [], []⟩,
        ⟨26725, false, false, [19463], []⟩,
        ⟨38878, true, false, [], [84387]⟩
      ]⟩,
    ⟨[84387, 5], [19465, 88711], .contexts [
        ⟨52249, true, false, [19462], [5]⟩,
        ⟨28, false, false, [19462, 88711], []⟩,
        ⟨38880, true, false, [], [88711]⟩
      ]⟩,
    ⟨[19479, 88711], [19479, 88711], .contexts []⟩,
    ⟨[19479, 88711], [19479, 88711], .contexts []⟩,
    ⟨[88711, 7], [88711, 7], .contexts []⟩,
    ⟨[88711], [88711], .contexts []⟩,
    ⟨[88711, 7], [19479, 88711], .contexts [
        ⟨52253, false, false, [], []⟩,
        ⟨52245, true, false, [], [7]⟩,
        ⟨104, false, false, [88709], []⟩,
        ⟨105, false, false, [88709], []⟩,
        ⟨52231, false, false, [], [1]⟩,
        ⟨52234, false, false, [], [1]⟩,
        ⟨52229, false, false, [], [1]⟩,
        ⟨52230, false, false, [], [1]⟩,
        ⟨52230, false, false, [], [1]⟩,
        ⟨52241, false, false, [19479], []⟩,
        ⟨52251, false, false, [], []⟩,
        ⟨52252, false, false, [], []⟩,
        ⟨52254, false, false, [19479], []⟩,
        ⟨52233, true, false, [], [88711]⟩
      ]⟩,
    ⟨[88711, 11], [88711, 11], .contexts []⟩,
    ⟨[88711, 11], [86797], .contexts [
        ⟨52256, false, false, [], []⟩,
        ⟨52245, true, false, [], [11]⟩,
        ⟨110, false, false, [88709], []⟩,
        ⟨111, false, false, [88709], []⟩,
        ⟨52217, false, false, [], [1]⟩,
        ⟨38787, false, false, [], [1]⟩,
        ⟨38774, false, false, [], [1]⟩,
        ⟨38774, false, false, [], [1]⟩,
        ⟨38773, false, false, [], []⟩,
        ⟨38784, false, false, [], []⟩,
        ⟨38778, false, false, [], []⟩,
        ⟨38778, false, false, [], []⟩,
        ⟨38937, false, false, [], []⟩,
        ⟨672, true, false, [], [86797]⟩
      ]⟩,
    ⟨[19493, 88611], [19493, 88611], .contexts []⟩,
    ⟨[19493, 88611], [19493, 88611], .contexts []⟩,
    ⟨[88711, 15], [88711, 15], .contexts []⟩,
    ⟨[88711, 15], [19493, 88611], .contexts [
        ⟨52260, false, false, [], []⟩,
        ⟨52245, true, false, [], [15]⟩,
        ⟨121, false, false, [88709], []⟩,
        ⟨122, false, false, [88709], []⟩,
        ⟨52237, false, false, [], [1]⟩,
        ⟨52238, false, false, [], [1]⟩,
        ⟨52235, false, false, [], [1]⟩,
        ⟨52236, false, false, [], [1]⟩,
        ⟨52236, false, false, [], [1]⟩,
        ⟨51872, false, false, [19493], []⟩,
        ⟨52258, false, false, [], []⟩,
        ⟨52259, false, false, [], []⟩,
        ⟨51853, false, false, [19493], []⟩,
        ⟨38962, true, false, [], [88611]⟩
      ]⟩,
    ⟨[88611, 15], [19495, 88711], .contexts [
        ⟨52261, true, false, [19492], [15]⟩,
        ⟨1, false, false, [19492, 88711], []⟩,
        ⟨38925, true, false, [], [88711]⟩
      ]⟩,
    ⟨[88711, 5], [19463, 84387], .contexts [
        ⟨52248, false, false, [], []⟩,
        ⟨52249, false, false, [], []⟩,
        ⟨52246, false, false, [], []⟩,
        ⟨52247, false, false, [], []⟩,
        ⟨52247, false, false, [], []⟩
      ]⟩,
    ⟨[23225], [19463, 17469], .source 11677⟩,
    ⟨[23227], [23225, 315], .source 11678⟩,
    ⟨[23229], [23227, 17467], .source 11679⟩,
    ⟨[23231], [23229, 19465], .source 11680⟩,
    ⟨[88711], [88711], .contexts []⟩,
    ⟨[23231, 88711, 3], [88711], .contexts [
        ⟨52267, false, false, [], [88711, 3]⟩,
        ⟨52250, true, false, [23229], [3]⟩,
        ⟨52266, false, false, [], [84387, 5, 3]⟩,
        ⟨27926, true, false, [23227], [5, 3]⟩,
        ⟨52265, false, false, [], [84619, 3, 5, 3]⟩,
        ⟨27932, true, false, [23225], [3, 5, 3]⟩,
        ⟨52264, false, false, [], [84619, 5, 3, 5, 3]⟩,
        ⟨27927, true, false, [19463], [5, 3, 5, 3]⟩,
        ⟨52263, true, false, [], [3, 5, 3, 5, 3]⟩,
        ⟨7129, false, false, [88711], []⟩,
        ⟨52268, false, false, [], []⟩
      ]⟩,
    ⟨[88711, 3], [88711, 3], .contexts []⟩,
    ⟨[23233], [23230], .source 11681⟩,
    ⟨[23230], [23230], .contexts []⟩,
    ⟨[88711, 3], [23233, 88711], .contexts [
        ⟨52270, false, false, [], []⟩,
        ⟨52269, false, false, [23230], []⟩,
        ⟨52254, false, false, [23230], []⟩,
        ⟨52272, true, false, [], [88711]⟩,
        ⟨52272, true, false, [], [88711]⟩,
        ⟨52271, true, false, [], [88711]⟩
      ]⟩,
    ⟨[23235], [19463, 245], .source 11682⟩,
    ⟨[23237], [23235, 19465], .source 11683⟩,
    ⟨[88711, 9], [88711, 9], .contexts []⟩,
    ⟨[23239], [23236], .source 11684⟩,
    ⟨[23236], [23236], .contexts []⟩,
    ⟨[88711, 9], [23239, 88711], .contexts [
        ⟨52276, false, false, [], []⟩,
        ⟨52275, false, false, [23236], [88711, 9]⟩,
        ⟨52250, true, false, [23236, 23235], [9]⟩,
        ⟨52274, false, false, [23236], [84387, 5, 9]⟩,
        ⟨26726, true, false, [23236, 19463], [5, 9]⟩,
        ⟨52263, true, false, [23236], [9, 5, 9]⟩,
        ⟨882, false, false, [23236, 88711], []⟩,
        ⟨52268, false, false, [23236], []⟩,
        ⟨52254, false, false, [23236], []⟩,
        ⟨52278, true, false, [], [88711]⟩,
        ⟨52278, true, false, [], [88711]⟩,
        ⟨52277, true, false, [], [88711]⟩
      ]⟩,
    ⟨[88713], [88711, 13], .source 44421⟩,
    ⟨[88711, 13], [88713], .contexts [
        ⟨52280, true, false, [], []⟩
      ]⟩,
    ⟨[88713, 13], [88711], .contexts [
        ⟨52281, true, false, [], [13]⟩,
        ⟨59, false, false, [88711], []⟩,
        ⟨52244, false, false, [], []⟩
      ]⟩,
    ⟨[88713], [88713], .contexts []⟩,
    ⟨[88713], [88713], .contexts []⟩,
    ⟨[88711, 13], [88713], .contexts [
        ⟨52281, false, false, [], []⟩,
        ⟨52283, false, false, [], []⟩,
        ⟨52284, false, false, [], []⟩,
        ⟨52284, false, false, [], []⟩
      ]⟩,
    ⟨[23233, 88711], [23233, 88711], .contexts []⟩,
    ⟨[23233, 88711], [23233, 88711], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 817. -/
def y322TCIndexRaw817 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[23233, 88713], [23233, 88713], .contexts []⟩,
    ⟨[23233, 88713], [23233, 88713], .contexts []⟩,
    ⟨[23233, 88713], [23233, 88713], .contexts []⟩,
    ⟨[88713], [88713], .contexts []⟩,
    ⟨[23233], [23233], .contexts [
        ⟨13, false, false, [], [23233]⟩
      ]⟩,
    ⟨[88713, 3], [23233, 88713], .contexts [
        ⟨52285, true, false, [], [3]⟩,
        ⟨63, false, false, [88711], []⟩,
        ⟨65, false, false, [88711], []⟩,
        ⟨52270, false, false, [], [13]⟩,
        ⟨52273, false, false, [], [13]⟩,
        ⟨52286, false, false, [], [13]⟩,
        ⟨52287, false, false, [], [13]⟩,
        ⟨52287, false, false, [], [13]⟩,
        ⟨52281, false, false, [23233], []⟩,
        ⟨52288, false, false, [], []⟩,
        ⟨52289, false, false, [], []⟩,
        ⟨52290, false, false, [], []⟩,
        ⟨52291, false, false, [23233], []⟩,
        ⟨52292, true, false, [], [88713]⟩
      ]⟩,
    ⟨[19479, 88713], [19479, 88713], .contexts []⟩,
    ⟨[19479, 88713], [19479, 88713], .contexts []⟩,
    ⟨[88713, 7], [88713, 7], .contexts []⟩,
    ⟨[88713, 7], [19479, 88713], .contexts [
        ⟨52296, false, false, [], []⟩,
        ⟨52285, true, false, [], [7]⟩,
        ⟨73, false, false, [88711], []⟩,
        ⟨74, false, false, [88711], []⟩,
        ⟨52253, false, false, [], [13]⟩,
        ⟨52255, false, false, [], [13]⟩,
        ⟨52251, false, false, [], [13]⟩,
        ⟨52252, false, false, [], [13]⟩,
        ⟨52252, false, false, [], [13]⟩,
        ⟨52281, false, false, [19479], []⟩,
        ⟨52294, false, false, [], []⟩,
        ⟨52295, false, false, [], []⟩,
        ⟨52291, false, false, [19479], []⟩,
        ⟨52233, true, false, [], [88713]⟩
      ]⟩,
    ⟨[23239, 88711], [23239, 88711], .contexts []⟩,
    ⟨[23239, 88711], [23239, 88711], .contexts []⟩,
    ⟨[23239, 88713], [23239, 88713], .contexts []⟩,
    ⟨[23239, 88713], [23239, 88713], .contexts []⟩,
    ⟨[23239], [23239], .contexts [
        ⟨13, false, false, [], [23239]⟩
      ]⟩,
    ⟨[88713, 9], [23239, 88713], .contexts [
        ⟨52285, true, false, [], [9]⟩,
        ⟨77, false, false, [88711], []⟩,
        ⟨78, false, false, [88711], []⟩,
        ⟨52276, false, false, [], [13]⟩,
        ⟨52279, false, false, [], [13]⟩,
        ⟨52298, false, false, [], [13]⟩,
        ⟨52299, false, false, [], [13]⟩,
        ⟨52299, false, false, [], [13]⟩,
        ⟨52281, false, false, [23239], []⟩,
        ⟨52300, false, false, [], []⟩,
        ⟨52301, false, false, [], []⟩,
        ⟨52291, false, false, [23239], []⟩,
        ⟨52302, true, false, [], [88713]⟩
      ]⟩,
    ⟨[88713, 11], [88713, 11], .contexts []⟩,
    ⟨[88713, 11], [19487, 84207], .contexts [
        ⟨52304, false, false, [], []⟩,
        ⟨52285, true, false, [], [11]⟩,
        ⟨82, false, false, [88711], []⟩,
        ⟨83, false, false, [88711], []⟩,
        ⟨52256, false, false, [], [13]⟩,
        ⟨52257, false, false, [], [13]⟩,
        ⟨38784, false, false, [], [13]⟩,
        ⟨38778, false, false, [], [13]⟩,
        ⟨38778, false, false, [], [13]⟩,
        ⟨38956, false, false, [], []⟩,
        ⟨38951, false, false, [], []⟩,
        ⟨38952, false, false, [], []⟩,
        ⟨38952, false, false, [], []⟩,
        ⟨38953, false, false, [], []⟩,
        ⟨38955, false, false, [], []⟩
      ]⟩,
    ⟨[23241], [19493, 16647], .source 11685⟩,
    ⟨[23243], [23241, 19495], .source 11686⟩,
    ⟨[23243, 88713], [23243, 88713], .contexts []⟩,
    ⟨[23243, 88713], [23243, 88713], .contexts []⟩,
    ⟨[88713, 15], [88713, 15], .contexts []⟩,
    ⟨[88713, 15], [23243, 88713], .contexts [
        ⟨52310, false, false, [], []⟩,
        ⟨52285, true, false, [], [15]⟩,
        ⟨88, false, false, [88711], []⟩,
        ⟨91, false, false, [88711], []⟩,
        ⟨52260, false, false, [], [13, 15, 13]⟩,
        ⟨52261, false, false, [], [13, 15, 13]⟩,
        ⟨52258, false, false, [], [13, 15, 13]⟩,
        ⟨52259, false, false, [], [13, 15, 13]⟩,
        ⟨52259, false, false, [], [13, 15, 13]⟩,
        ⟨51869, false, false, [19493], [15, 13]⟩,
        ⟨52306, true, false, [], [88611, 15, 13]⟩,
        ⟨52262, false, false, [23241], [13]⟩,
        ⟨52307, true, false, [], [88711, 13]⟩,
        ⟨52281, false, false, [23243], []⟩,
        ⟨52308, false, false, [], []⟩,
        ⟨52309, false, false, [], []⟩,
        ⟨52291, false, false, [23243], []⟩
      ]⟩,
    ⟨[23243], [23243], .contexts [
        ⟨13, false, false, [], [23243]⟩
      ]⟩,
    ⟨[88713, 15], [23243, 88713], .contexts [
        ⟨52311, false, false, [], []⟩,
        ⟨52312, true, false, [], [88713]⟩
      ]⟩,
    ⟨[88715], [88713, 1], .source 44422⟩,
    ⟨[88713, 1], [88715], .contexts [
        ⟨52314, true, false, [], []⟩
      ]⟩,
    ⟨[88715, 1], [88713], .contexts [
        ⟨52315, true, false, [], [1]⟩,
        ⟨8, false, false, [88713], []⟩,
        ⟨52284, false, false, [], []⟩
      ]⟩,
    ⟨[88715], [88715], .contexts []⟩,
    ⟨[88715], [88715], .contexts []⟩,
    ⟨[88713, 1], [88715], .contexts [
        ⟨52315, false, false, [], []⟩,
        ⟨52317, false, false, [], []⟩,
        ⟨52318, false, false, [], []⟩,
        ⟨52318, false, false, [], []⟩
      ]⟩,
    ⟨[19479, 88715], [19479, 88715], .contexts []⟩,
    ⟨[19479, 88715], [19479, 88715], .contexts []⟩,
    ⟨[88715, 7], [88715, 7], .contexts []⟩,
    ⟨[88715], [88715], .contexts []⟩,
    ⟨[88715, 7], [19479, 88715], .contexts [
        ⟨52322, false, false, [], []⟩,
        ⟨52319, true, false, [], [7]⟩,
        ⟨104, false, false, [88713], []⟩,
        ⟨105, false, false, [88713], []⟩,
        ⟨52296, false, false, [], [1]⟩,
        ⟨52297, false, false, [], [1]⟩,
        ⟨52294, false, false, [], [1]⟩,
        ⟨52295, false, false, [], [1]⟩,
        ⟨52295, false, false, [], [1]⟩,
        ⟨52315, false, false, [19479], []⟩,
        ⟨52320, false, false, [], []⟩,
        ⟨52321, false, false, [], []⟩,
        ⟨52323, false, false, [19479], []⟩,
        ⟨52233, true, false, [], [88715]⟩
      ]⟩,
    ⟨[88713, 11], [19487, 84207], .contexts [
        ⟨52305, false, false, [], []⟩
      ]⟩,
    ⟨[19487, 84205], [19487, 84205], .contexts []⟩,
    ⟨[19487, 84205], [19487, 84205], .contexts []⟩,
    ⟨[88715, 11], [88715, 11], .contexts []⟩,
    ⟨[88715, 11], [19487, 84205], .contexts [
        ⟨52328, false, false, [], []⟩,
        ⟨52319, true, false, [], [11]⟩,
        ⟨110, false, false, [88713], []⟩,
        ⟨111, false, false, [88713], []⟩,
        ⟨52304, false, false, [], [1]⟩,
        ⟨52325, false, false, [], [1]⟩,
        ⟨38951, false, false, [], [1]⟩,
        ⟨38952, false, false, [], [1]⟩,
        ⟨38952, false, false, [], [1]⟩,
        ⟨25151, false, false, [19487], []⟩,
        ⟨52326, false, false, [], []⟩,
        ⟨52327, false, false, [], []⟩,
        ⟨25439, false, false, [19487], []⟩,
        ⟨38954, true, false, [], [84205]⟩
      ]⟩,
    ⟨[84205, 11], [19489, 88715], .contexts [
        ⟨52329, true, false, [19486], [11]⟩,
        ⟨53, false, false, [19486, 88715], []⟩,
        ⟨38918, true, false, [], [88715]⟩
      ]⟩,
    ⟨[23243, 88715], [23243, 88715], .contexts []⟩,
    ⟨[23243, 88715], [23243, 88715], .contexts []⟩,
    ⟨[88715, 15], [88715, 15], .contexts []⟩,
    ⟨[88715, 15], [23243, 88715], .contexts [
        ⟨52333, false, false, [], []⟩,
        ⟨52319, true, false, [], [15]⟩,
        ⟨121, false, false, [88713], []⟩,
        ⟨122, false, false, [88713], []⟩,
        ⟨52310, false, false, [], [1]⟩,
        ⟨52313, false, false, [], [1]⟩,
        ⟨52308, false, false, [], [1]⟩,
        ⟨52309, false, false, [], [1]⟩,
        ⟨52309, false, false, [], [1]⟩,
        ⟨52315, false, false, [23243], []⟩,
        ⟨52331, false, false, [], []⟩,
        ⟨52332, false, false, [], []⟩,
        ⟨52323, false, false, [23243], []⟩,
        ⟨52312, true, false, [], [88715]⟩
      ]⟩,
    ⟨[88717], [88715, 3], .source 44423⟩,
    ⟨[88715, 3], [88717], .contexts [
        ⟨52335, true, false, [], []⟩
      ]⟩,
    ⟨[88717, 3], [88715], .contexts [
        ⟨52336, true, false, [], [3]⟩,
        ⟨20, false, false, [88715], []⟩,
        ⟨52318, false, false, [], []⟩
      ]⟩,
    ⟨[88717], [88717], .contexts []⟩,
    ⟨[88717], [88717], .contexts []⟩,
    ⟨[88715, 3], [88717], .contexts [
        ⟨52336, false, false, [], []⟩,
        ⟨52338, false, false, [], []⟩,
        ⟨52339, false, false, [], []⟩,
        ⟨52339, false, false, [], []⟩
      ]⟩,
    ⟨[88715, 1], [88713], .contexts [
        ⟨52316, false, false, [], []⟩
      ]⟩,
    ⟨[88715, 1], [88713], .contexts [
        ⟨52341, false, false, [], []⟩,
        ⟨52283, false, false, [], []⟩,
        ⟨52284, false, false, [], []⟩,
        ⟨52284, false, false, [], []⟩
      ]⟩,
    ⟨[23233, 88715], [23233, 88715], .contexts []⟩,
    ⟨[23233, 88715], [23233, 88715], .contexts []⟩,
    ⟨[23233, 88715], [23233, 88715], .contexts []⟩,
    ⟨[23233, 88717], [23233, 88717], .contexts []⟩,
    ⟨[23233, 88717], [23233, 88717], .contexts []⟩,
    ⟨[23233, 88717], [23233, 88717], .contexts []⟩,
    ⟨[88717, 1], [88717, 1], .contexts []⟩,
    ⟨[88717], [88717], .contexts []⟩,
    ⟨[88717, 1], [23233, 88717], .contexts [
        ⟨52349, false, false, [], []⟩,
        ⟨52340, true, false, [], [1]⟩,
        ⟨130, false, false, [88715], []⟩,
        ⟨133, false, false, [88715], []⟩,
        ⟨52342, false, false, [], [3, 1, 3]⟩,
        ⟨52293, false, false, [], [1, 3]⟩,
        ⟨52288, false, false, [], [1, 3]⟩,
        ⟨52290, false, false, [], [1, 3]⟩,
        ⟨52290, false, false, [], [1, 3]⟩,
        ⟨52315, false, false, [23233], [3]⟩,
        ⟨52343, false, false, [], [3]⟩,
        ⟨52344, false, false, [], [3]⟩,
        ⟨52345, false, false, [], [3]⟩,
        ⟨52336, false, false, [23233], []⟩,
        ⟨52346, false, false, [], []⟩,
        ⟨52347, false, false, [], []⟩,
        ⟨52348, false, false, [], []⟩,
        ⟨52350, false, false, [23233], []⟩,
        ⟨52292, true, false, [], [88717]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 818. -/
def y322TCIndexRaw818 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88715, 7], [19479, 88715], .contexts [
        ⟨52322, false, false, [], []⟩,
        ⟨52324, false, false, [], []⟩,
        ⟨52320, false, false, [], []⟩,
        ⟨52321, false, false, [], []⟩,
        ⟨52321, false, false, [], []⟩
      ]⟩,
    ⟨[19479, 88717], [19479, 88717], .contexts []⟩,
    ⟨[88715, 15], [23243, 88715], .contexts [
        ⟨52334, false, false, [], []⟩
      ]⟩,
    ⟨[88715, 15], [23243, 88715], .contexts [
        ⟨52333, false, false, [], []⟩,
        ⟨52354, false, false, [], []⟩,
        ⟨52331, false, false, [], []⟩,
        ⟨52332, false, false, [], []⟩,
        ⟨52332, false, false, [], []⟩
      ]⟩,
    ⟨[23243, 88717], [23243, 88717], .contexts []⟩,
    ⟨[23243, 88717], [23243, 88717], .contexts []⟩,
    ⟨[88717, 15], [88717, 15], .contexts []⟩,
    ⟨[88717, 15], [23243, 88717], .contexts [
        ⟨52358, false, false, [], []⟩,
        ⟨52340, true, false, [], [15]⟩,
        ⟨151, false, false, [88715], []⟩,
        ⟨152, false, false, [88715], []⟩,
        ⟨52355, false, false, [], [3]⟩,
        ⟨52336, false, false, [23243], []⟩,
        ⟨52356, false, false, [], []⟩,
        ⟨52357, false, false, [], []⟩,
        ⟨52350, false, false, [23243], []⟩,
        ⟨52312, true, false, [], [88717]⟩
      ]⟩,
    ⟨[88719], [88717, 5], .source 44424⟩,
    ⟨[88717, 5], [88719], .contexts [
        ⟨52360, true, false, [], []⟩
      ]⟩,
    ⟨[88719, 5], [88717], .contexts [
        ⟨52361, true, false, [], [5]⟩,
        ⟨28, false, false, [88717], []⟩,
        ⟨52339, false, false, [], []⟩
      ]⟩,
    ⟨[88719], [88719], .contexts []⟩,
    ⟨[88719], [88719], .contexts []⟩,
    ⟨[88717, 5], [88719], .contexts [
        ⟨52361, false, false, [], []⟩,
        ⟨52363, false, false, [], []⟩,
        ⟨52364, false, false, [], []⟩,
        ⟨52364, false, false, [], []⟩
      ]⟩,
    ⟨[23233, 88719], [23233, 88719], .contexts []⟩,
    ⟨[23233, 88719], [23233, 88719], .contexts []⟩,
    ⟨[88719, 1], [88719, 1], .contexts []⟩,
    ⟨[88719], [88719], .contexts []⟩,
    ⟨[88719, 1], [23233, 88719], .contexts [
        ⟨52368, false, false, [], []⟩,
        ⟨52365, true, false, [], [1]⟩,
        ⟨161, false, false, [88717], []⟩,
        ⟨162, false, false, [88717], []⟩,
        ⟨52349, false, false, [], [5]⟩,
        ⟨52351, false, false, [], [5]⟩,
        ⟨52346, false, false, [], [5]⟩,
        ⟨52348, false, false, [], [5]⟩,
        ⟨52348, false, false, [], [5]⟩,
        ⟨52361, false, false, [23233], []⟩,
        ⟨52366, false, false, [], []⟩,
        ⟨52367, false, false, [], []⟩,
        ⟨52369, false, false, [23233], []⟩,
        ⟨52292, true, false, [], [88719]⟩
      ]⟩,
    ⟨[23243, 88719], [23243, 88719], .contexts []⟩,
    ⟨[23243, 88719], [23243, 88719], .contexts []⟩,
    ⟨[88719, 15], [88719, 15], .contexts []⟩,
    ⟨[88719, 15], [23243, 88719], .contexts [
        ⟨52373, false, false, [], []⟩,
        ⟨52365, true, false, [], [15]⟩,
        ⟨184, false, false, [88717], []⟩,
        ⟨185, false, false, [88717], []⟩,
        ⟨52358, false, false, [], [5]⟩,
        ⟨52359, false, false, [], [5]⟩,
        ⟨52356, false, false, [], [5]⟩,
        ⟨52357, false, false, [], [5]⟩,
        ⟨52357, false, false, [], [5]⟩,
        ⟨52361, false, false, [23243], []⟩,
        ⟨52371, false, false, [], []⟩,
        ⟨52372, false, false, [], []⟩,
        ⟨52369, false, false, [23243], []⟩,
        ⟨52312, true, false, [], [88719]⟩
      ]⟩,
    ⟨[88721], [88719, 9], .source 44425⟩,
    ⟨[88719, 9], [88721], .contexts [
        ⟨52375, true, false, [], []⟩
      ]⟩,
    ⟨[88719, 9], [88721], .contexts [
        ⟨52376, false, false, [], []⟩
      ]⟩,
    ⟨[88721], [88721], .contexts []⟩,
    ⟨[88721], [88721], .contexts []⟩,
    ⟨[88719, 15], [23243, 88719], .contexts [
        ⟨52373, false, false, [], []⟩,
        ⟨52374, false, false, [], []⟩,
        ⟨52371, false, false, [], []⟩,
        ⟨52372, false, false, [], []⟩,
        ⟨52372, false, false, [], []⟩
      ]⟩,
    ⟨[23243, 88721], [23243, 88721], .contexts []⟩,
    ⟨[23243, 88721], [23243, 88721], .contexts []⟩,
    ⟨[88721, 15], [88721, 15], .contexts []⟩,
    ⟨[88723], [88721, 11], .source 44426⟩,
    ⟨[88721, 11], [88723], .contexts [
        ⟨52384, true, false, [], []⟩
      ]⟩,
    ⟨[88723], [88723], .contexts []⟩,
    ⟨[88723], [88723], .contexts []⟩,
    ⟨[23243, 88723], [23243, 88723], .contexts []⟩,
    ⟨[23243, 88723], [23243, 88723], .contexts []⟩,
    ⟨[88723, 15], [23243, 88723], .contexts [
        ⟨52387, true, false, [], [15]⟩,
        ⟨52387, true, false, [], [15]⟩,
        ⟨52386, true, false, [], [15]⟩,
        ⟨52385, true, false, [], [15]⟩,
        ⟨231, false, false, [88721], []⟩,
        ⟨232, false, false, [88721], []⟩,
        ⟨52383, false, false, [], [11]⟩,
        ⟨52383, false, false, [], [11]⟩,
        ⟨52379, true, false, [], [15, 11]⟩,
        ⟨52379, true, false, [], [15, 11]⟩,
        ⟨52378, true, false, [], [15, 11]⟩,
        ⟨52377, true, false, [], [15, 11]⟩,
        ⟨205, false, false, [88719], [11]⟩,
        ⟨206, false, false, [88719], [11]⟩,
        ⟨52380, false, false, [], [9, 11]⟩,
        ⟨52376, false, false, [23243], [11]⟩,
        ⟨52381, false, false, [], [11]⟩,
        ⟨52382, false, false, [], [11]⟩,
        ⟨52312, true, false, [], [88721, 11]⟩,
        ⟨52381, false, false, [], [11]⟩,
        ⟨52382, false, false, [], [11]⟩,
        ⟨52382, false, false, [], [11]⟩,
        ⟨52385, false, false, [23243], []⟩,
        ⟨52388, false, false, [], []⟩,
        ⟨52389, false, false, [], []⟩
      ]⟩,
    ⟨[88723, 15], [88723, 15], .contexts []⟩,
    ⟨[88725], [88723, 1], .source 44427⟩,
    ⟨[88723, 1], [88725], .contexts [
        ⟨52392, true, false, [], []⟩
      ]⟩,
    ⟨[88725, 1], [88723], .contexts [
        ⟨52393, true, false, [], [1]⟩,
        ⟨8, false, false, [88723], []⟩,
        ⟨52387, false, false, [], []⟩
      ]⟩,
    ⟨[88725], [88725], .contexts []⟩,
    ⟨[88725], [88725], .contexts []⟩,
    ⟨[23243, 88725], [23243, 88725], .contexts []⟩,
    ⟨[23243, 88725], [23243, 88725], .contexts []⟩,
    ⟨[88725, 15], [23243, 88725], .contexts [
        ⟨52396, true, false, [], [15]⟩,
        ⟨52396, true, false, [], [15]⟩,
        ⟨52395, true, false, [], [15]⟩,
        ⟨52393, true, false, [], [15]⟩,
        ⟨121, false, false, [88723], []⟩,
        ⟨122, false, false, [88723], []⟩,
        ⟨52391, false, false, [], [1]⟩,
        ⟨52391, false, false, [], [1]⟩,
        ⟨52390, false, false, [], [1]⟩,
        ⟨52312, true, false, [], [88723, 1]⟩,
        ⟨52388, false, false, [], [1]⟩,
        ⟨52389, false, false, [], [1]⟩,
        ⟨52389, false, false, [], [1]⟩,
        ⟨52393, false, false, [23243], []⟩,
        ⟨52397, false, false, [], []⟩,
        ⟨52398, false, false, [], []⟩,
        ⟨52312, true, false, [], [88725]⟩
      ]⟩,
    ⟨[88727], [88725, 13], .source 44428⟩,
    ⟨[88725, 13], [88727], .contexts [
        ⟨52400, true, false, [], []⟩
      ]⟩,
    ⟨[88727, 13], [88725], .contexts [
        ⟨52401, true, false, [], [13]⟩,
        ⟨59, false, false, [88725], []⟩,
        ⟨52396, false, false, [], []⟩
      ]⟩,
    ⟨[88729], [88727, 15], .source 44429⟩,
    ⟨[88727, 15], [88729], .contexts [
        ⟨52403, true, false, [], []⟩
      ]⟩,
    ⟨[88727], [88727], .contexts []⟩,
    ⟨[88729, 15], [88727], .contexts [
        ⟨52404, true, false, [], [15]⟩,
        ⟨1, false, false, [88727], []⟩,
        ⟨52405, false, false, [], []⟩
      ]⟩,
    ⟨[88729], [88729], .contexts []⟩,
    ⟨[88729], [88729], .contexts []⟩,
    ⟨[88727, 13], [88725], .contexts [
        ⟨52402, false, false, [], []⟩
      ]⟩,
    ⟨[23243, 88729], [23243, 88729], .contexts []⟩,
    ⟨[88729, 13], [23243, 88729], .contexts [
        ⟨52408, true, false, [], [13]⟩,
        ⟨52408, true, false, [], [13]⟩,
        ⟨52407, true, false, [], [13]⟩,
        ⟨52404, true, false, [], [13]⟩,
        ⟨259, false, false, [88727], []⟩,
        ⟨262, false, false, [88727], []⟩,
        ⟨52409, false, false, [], [15, 13, 15]⟩,
        ⟨52395, false, false, [], [15, 13, 15]⟩,
        ⟨52396, false, false, [], [15, 13, 15]⟩,
        ⟨52396, false, false, [], [15, 13, 15]⟩,
        ⟨52399, false, false, [], [13, 15]⟩,
        ⟨52397, false, false, [], [13, 15]⟩,
        ⟨52398, false, false, [], [13, 15]⟩,
        ⟨52398, false, false, [], [13, 15]⟩,
        ⟨52401, false, false, [23243], [15]⟩,
        ⟨52404, false, false, [23243], []⟩,
        ⟨52410, false, false, [], []⟩
      ]⟩,
    ⟨[88729, 13], [23243, 88729], .contexts [
        ⟨52411, false, false, [], []⟩,
        ⟨52312, true, false, [], [88729]⟩
      ]⟩,
    ⟨[88731], [88729, 1], .source 44430⟩,
    ⟨[88729, 1], [88731], .contexts [
        ⟨52413, true, false, [], []⟩
      ]⟩,
    ⟨[88731, 1], [88729], .contexts [
        ⟨52414, true, false, [], [1]⟩,
        ⟨8, false, false, [88729], []⟩,
        ⟨52408, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 819. -/
def y322TCIndexRaw819 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88733], [88731, 3], .source 44431⟩,
    ⟨[88731, 3], [88733], .contexts [
        ⟨52416, true, false, [], []⟩
      ]⟩,
    ⟨[88731], [88731], .contexts []⟩,
    ⟨[88735], [88733, 5], .source 44432⟩,
    ⟨[88733, 5], [88735], .contexts [
        ⟨52419, true, false, [], []⟩
      ]⟩,
    ⟨[88733], [88733], .contexts []⟩,
    ⟨[88737], [88735, 1], .source 44433⟩,
    ⟨[88735, 1], [88737], .contexts [
        ⟨52422, true, false, [], []⟩
      ]⟩,
    ⟨[88735], [88735], .contexts []⟩,
    ⟨[88737, 1], [88735], .contexts [
        ⟨52423, true, false, [], [1]⟩,
        ⟨8, false, false, [88735], []⟩,
        ⟨52424, false, false, [], []⟩
      ]⟩,
    ⟨[88739], [88737, 9], .source 44434⟩,
    ⟨[88737, 9], [88739], .contexts [
        ⟨52426, true, false, [], []⟩
      ]⟩,
    ⟨[88737], [88737], .contexts []⟩,
    ⟨[88739, 9], [88737], .contexts [
        ⟨52427, true, false, [], [9]⟩,
        ⟨46, false, false, [88737], []⟩,
        ⟨52428, false, false, [], []⟩
      ]⟩,
    ⟨[88741], [88739, 11], .source 44435⟩,
    ⟨[88739, 11], [88741], .contexts [
        ⟨52430, true, false, [], []⟩
      ]⟩,
    ⟨[88739], [88739], .contexts []⟩,
    ⟨[88741, 11], [88739], .contexts [
        ⟨52431, true, false, [], [11]⟩,
        ⟨53, false, false, [88739], []⟩,
        ⟨52432, false, false, [], []⟩
      ]⟩,
    ⟨[88743], [88741, 1], .source 44436⟩,
    ⟨[88741, 1], [88743], .contexts [
        ⟨52434, true, false, [], []⟩
      ]⟩,
    ⟨[88741], [88741], .contexts []⟩,
    ⟨[88745], [88743, 13], .source 44437⟩,
    ⟨[88743], [88743], .contexts []⟩,
    ⟨[88747], [88745, 15], .source 44438⟩,
    ⟨[88745], [88745], .contexts []⟩,
    ⟨[88749], [88747, 1], .source 44439⟩,
    ⟨[88747], [88747], .contexts []⟩,
    ⟨[88751], [88749, 3], .source 44440⟩,
    ⟨[88749], [88749], .contexts []⟩,
    ⟨[88753], [88751, 5], .source 44441⟩,
    ⟨[88751], [88751], .contexts []⟩,
    ⟨[88755], [88753, 1], .source 44442⟩,
    ⟨[88753], [88753], .contexts []⟩,
    ⟨[88757], [88755, 9], .source 44443⟩,
    ⟨[88755], [88755], .contexts []⟩,
    ⟨[88759], [88757, 11], .source 44444⟩,
    ⟨[88757], [88757], .contexts []⟩,
    ⟨[88761], [88759, 1], .source 44445⟩,
    ⟨[88759], [88759], .contexts []⟩,
    ⟨[88763], [88761, 13], .source 44446⟩,
    ⟨[88761], [88761], .contexts []⟩,
    ⟨[88765], [88763, 15], .source 44447⟩,
    ⟨[88763], [88763], .contexts []⟩,
    ⟨[88767], [88765, 1], .source 44448⟩,
    ⟨[88765], [88765], .contexts []⟩,
    ⟨[88769], [88767, 3], .source 44449⟩,
    ⟨[88767], [88767], .contexts []⟩,
    ⟨[88771], [88769, 5], .source 44450⟩,
    ⟨[88769], [88769], .contexts []⟩,
    ⟨[88773], [88771, 1], .source 44451⟩,
    ⟨[88771], [88771], .contexts []⟩,
    ⟨[88775], [88773, 9], .source 44452⟩,
    ⟨[88773], [88773], .contexts []⟩,
    ⟨[88777], [88775, 11], .source 44453⟩,
    ⟨[88775], [88775], .contexts []⟩,
    ⟨[88779], [88777, 1], .source 44454⟩,
    ⟨[88777], [88777], .contexts []⟩,
    ⟨[88781], [88779, 13], .source 44455⟩,
    ⟨[88779], [88779], .contexts []⟩,
    ⟨[88783], [88781, 15], .source 44456⟩,
    ⟨[88781], [88781], .contexts []⟩,
    ⟨[88785], [88783, 1], .source 44457⟩,
    ⟨[88783], [88783], .contexts []⟩,
    ⟨[88787], [88785, 3], .source 44458⟩]

/-- Exact literal claimed equations and contextual derivations, block 820. -/
def y322TCIndexRaw820 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88785], [88785], .contexts []⟩,
    ⟨[88789], [88787, 5], .source 44459⟩,
    ⟨[88787], [88787], .contexts []⟩,
    ⟨[88791], [88789, 1], .source 44460⟩,
    ⟨[88789], [88789], .contexts []⟩,
    ⟨[88793], [88791, 9], .source 44461⟩,
    ⟨[88791], [88791], .contexts []⟩,
    ⟨[88795], [88793, 11], .source 44462⟩,
    ⟨[88793], [88793], .contexts []⟩,
    ⟨[88797], [88795, 1], .source 44463⟩,
    ⟨[88795], [88795], .contexts []⟩,
    ⟨[88799], [88797, 13], .source 44464⟩,
    ⟨[88797], [88797], .contexts []⟩,
    ⟨[88801], [88799, 15], .source 44465⟩,
    ⟨[88799], [88799], .contexts []⟩,
    ⟨[88803], [88801, 1], .source 44466⟩,
    ⟨[88801], [88801], .contexts []⟩,
    ⟨[88805], [88803, 3], .source 44467⟩,
    ⟨[88803], [88803], .contexts []⟩,
    ⟨[88807], [88805, 5], .source 44468⟩,
    ⟨[88805, 5], [88807], .contexts [
        ⟨52499, true, false, [], []⟩
      ]⟩,
    ⟨[88805], [88805], .contexts []⟩,
    ⟨[88807, 5], [88805], .contexts [
        ⟨52500, true, false, [], [5]⟩,
        ⟨28, false, false, [88805], []⟩,
        ⟨52501, false, false, [], []⟩
      ]⟩,
    ⟨[88809], [88807, 1], .source 44469⟩,
    ⟨[88807, 1], [88809], .contexts [
        ⟨52503, true, false, [], []⟩
      ]⟩,
    ⟨[88807], [88807], .contexts []⟩,
    ⟨[88809, 1], [88807], .contexts [
        ⟨52504, true, false, [], [1]⟩,
        ⟨8, false, false, [88807], []⟩,
        ⟨52505, false, false, [], []⟩
      ]⟩,
    ⟨[88811], [88809, 9], .source 44470⟩,
    ⟨[88809], [88809], .contexts []⟩,
    ⟨[88811, 9], [88809], .contexts [
        ⟨52507, false, false, [], [9]⟩,
        ⟨46, false, false, [88809], []⟩,
        ⟨52508, false, false, [], []⟩
      ]⟩,
    ⟨[88813], [88811, 11], .source 44471⟩,
    ⟨[88811], [88811], .contexts []⟩,
    ⟨[88813, 11], [88811], .contexts [
        ⟨52510, false, false, [], [11]⟩,
        ⟨53, false, false, [88811], []⟩,
        ⟨52511, false, false, [], []⟩
      ]⟩,
    ⟨[88815], [88813, 1], .source 44472⟩,
    ⟨[88813, 1], [88815], .contexts [
        ⟨52513, true, false, [], []⟩
      ]⟩,
    ⟨[88813], [88813], .contexts []⟩,
    ⟨[88815, 1], [88813], .contexts [
        ⟨52514, true, false, [], [1]⟩,
        ⟨8, false, false, [88813], []⟩,
        ⟨52515, false, false, [], []⟩
      ]⟩,
    ⟨[88817], [88815, 13], .source 44473⟩,
    ⟨[88815, 13], [88817], .contexts [
        ⟨52517, true, false, [], []⟩
      ]⟩,
    ⟨[88815], [88815], .contexts []⟩,
    ⟨[88817, 13], [88815], .contexts [
        ⟨52518, true, false, [], [13]⟩,
        ⟨59, false, false, [88815], []⟩,
        ⟨52519, false, false, [], []⟩
      ]⟩,
    ⟨[88819], [88817, 15], .source 44474⟩,
    ⟨[88817, 15], [88819], .contexts [
        ⟨52521, true, false, [], []⟩
      ]⟩,
    ⟨[88817], [88817], .contexts []⟩,
    ⟨[88819, 15], [88817], .contexts [
        ⟨52522, true, false, [], [15]⟩,
        ⟨1, false, false, [88817], []⟩,
        ⟨52523, false, false, [], []⟩
      ]⟩,
    ⟨[88821], [88819, 1], .source 44475⟩,
    ⟨[88819, 1], [88821], .contexts [
        ⟨52525, true, false, [], []⟩
      ]⟩,
    ⟨[88819], [88819], .contexts []⟩,
    ⟨[88821, 1], [88819], .contexts [
        ⟨52526, true, false, [], [1]⟩,
        ⟨8, false, false, [88819], []⟩,
        ⟨52527, false, false, [], []⟩
      ]⟩,
    ⟨[88823], [88821, 3], .source 44476⟩,
    ⟨[88821, 3], [88823], .contexts [
        ⟨52529, true, false, [], []⟩
      ]⟩,
    ⟨[88821], [88821], .contexts []⟩,
    ⟨[88823, 3], [88821], .contexts [
        ⟨52530, true, false, [], [3]⟩,
        ⟨20, false, false, [88821], []⟩,
        ⟨52531, false, false, [], []⟩
      ]⟩,
    ⟨[88825], [88823, 5], .source 44477⟩,
    ⟨[88823, 5], [88825], .contexts [
        ⟨52533, true, false, [], []⟩
      ]⟩,
    ⟨[88823], [88823], .contexts []⟩,
    ⟨[88825, 5], [88823], .contexts [
        ⟨52534, true, false, [], [5]⟩,
        ⟨28, false, false, [88823], []⟩,
        ⟨52535, false, false, [], []⟩
      ]⟩,
    ⟨[88827], [88825, 1], .source 44478⟩,
    ⟨[88825, 1], [88827], .contexts [
        ⟨52537, true, false, [], []⟩
      ]⟩,
    ⟨[88825], [88825], .contexts []⟩,
    ⟨[88827, 1], [88825], .contexts [
        ⟨52538, true, false, [], [1]⟩,
        ⟨8, false, false, [88825], []⟩,
        ⟨52539, false, false, [], []⟩
      ]⟩,
    ⟨[88829], [88827, 9], .source 44479⟩,
    ⟨[88827, 9], [88829], .contexts [
        ⟨52541, true, false, [], []⟩
      ]⟩,
    ⟨[88827], [88827], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 821. -/
def y322TCIndexRaw821 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88829, 9], [88827], .contexts [
        ⟨52542, true, false, [], [9]⟩,
        ⟨46, false, false, [88827], []⟩,
        ⟨52543, false, false, [], []⟩
      ]⟩,
    ⟨[88831], [88829, 11], .source 44480⟩,
    ⟨[88829, 11], [88831], .contexts [
        ⟨52545, true, false, [], []⟩
      ]⟩,
    ⟨[88829], [88829], .contexts []⟩,
    ⟨[88831, 11], [88829], .contexts [
        ⟨52546, true, false, [], [11]⟩,
        ⟨53, false, false, [88829], []⟩,
        ⟨52547, false, false, [], []⟩
      ]⟩,
    ⟨[88833], [88831, 1], .source 44481⟩,
    ⟨[88831, 1], [88833], .contexts [
        ⟨52549, true, false, [], []⟩
      ]⟩,
    ⟨[88831], [88831], .contexts []⟩,
    ⟨[88831, 1], [88833], .contexts [
        ⟨52550, false, false, [], []⟩
      ]⟩,
    ⟨[88833], [88833], .contexts []⟩,
    ⟨[88829], [88829], .contexts []⟩,
    ⟨[88831, 11], [88829], .contexts [
        ⟨52548, false, false, [], []⟩,
        ⟨52554, false, false, [], []⟩,
        ⟨52547, false, false, [], []⟩,
        ⟨52547, false, false, [], []⟩
      ]⟩,
    ⟨[88829, 9], [88827], .contexts [
        ⟨52544, false, false, [], []⟩
      ]⟩,
    ⟨[88827], [88827], .contexts []⟩,
    ⟨[88827, 1], [88825], .contexts [
        ⟨52540, false, false, [], []⟩
      ]⟩,
    ⟨[88825], [88825], .contexts []⟩,
    ⟨[88821], [88821], .contexts []⟩,
    ⟨[88821, 1], [88819], .contexts [
        ⟨52528, false, false, [], []⟩
      ]⟩,
    ⟨[88819], [88819], .contexts []⟩,
    ⟨[88831, 11, 9, 1, 5, 3, 1], [88819], .contexts [
        ⟨52555, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨52556, false, false, [], [1, 5, 3, 1]⟩,
        ⟨52557, false, false, [], [1, 5, 3, 1]⟩,
        ⟨52543, false, false, [], [1, 5, 3, 1]⟩,
        ⟨52543, false, false, [], [1, 5, 3, 1]⟩,
        ⟨52558, false, false, [], [5, 3, 1]⟩,
        ⟨52559, false, false, [], [5, 3, 1]⟩,
        ⟨52539, false, false, [], [5, 3, 1]⟩,
        ⟨52539, false, false, [], [5, 3, 1]⟩,
        ⟨52536, false, false, [], [3, 1]⟩,
        ⟨52535, false, false, [], [3, 1]⟩,
        ⟨52535, false, false, [], [3, 1]⟩,
        ⟨52532, false, false, [], [1]⟩,
        ⟨52560, false, false, [], [1]⟩,
        ⟨52531, false, false, [], [1]⟩,
        ⟨52531, false, false, [], [1]⟩,
        ⟨52561, false, false, [], []⟩,
        ⟨52562, false, false, [], []⟩,
        ⟨52527, false, false, [], []⟩,
        ⟨52527, false, false, [], []⟩
      ]⟩,
    ⟨[88819, 15], [88817], .contexts [
        ⟨52524, false, false, [], []⟩
      ]⟩,
    ⟨[88817], [88817], .contexts []⟩,
    ⟨[88817, 13], [88815], .contexts [
        ⟨52520, false, false, [], []⟩
      ]⟩,
    ⟨[88815], [88815], .contexts []⟩,
    ⟨[88815, 1], [88813], .contexts [
        ⟨52516, false, false, [], []⟩
      ]⟩,
    ⟨[88813], [88813], .contexts []⟩,
    ⟨[88813, 11], [88811], .contexts [
        ⟨52512, false, false, [], []⟩
      ]⟩,
    ⟨[88811], [88811], .contexts []⟩,
    ⟨[88811, 9], [88809], .contexts [
        ⟨52509, false, false, [], []⟩
      ]⟩,
    ⟨[88809], [88809], .contexts []⟩,
    ⟨[88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9], [88809], .contexts [
        ⟨52563, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨52564, false, false, [], [13, 1, 11, 9]⟩,
        ⟨52565, false, false, [], [13, 1, 11, 9]⟩,
        ⟨52523, false, false, [], [13, 1, 11, 9]⟩,
        ⟨52523, false, false, [], [13, 1, 11, 9]⟩,
        ⟨52566, false, false, [], [1, 11, 9]⟩,
        ⟨52567, false, false, [], [1, 11, 9]⟩,
        ⟨52519, false, false, [], [1, 11, 9]⟩,
        ⟨52519, false, false, [], [1, 11, 9]⟩,
        ⟨52568, false, false, [], [11, 9]⟩,
        ⟨52569, false, false, [], [11, 9]⟩,
        ⟨52515, false, false, [], [11, 9]⟩,
        ⟨52515, false, false, [], [11, 9]⟩,
        ⟨52570, false, false, [], [9]⟩,
        ⟨52571, false, false, [], [9]⟩,
        ⟨52511, false, false, [], [9]⟩,
        ⟨52511, false, false, [], [9]⟩,
        ⟨52572, false, false, [], []⟩,
        ⟨52573, false, false, [], []⟩,
        ⟨52508, false, false, [], []⟩,
        ⟨52508, false, false, [], []⟩
      ]⟩,
    ⟨[88809, 1], [88807], .contexts [
        ⟨52506, false, false, [], []⟩
      ]⟩,
    ⟨[88807], [88807], .contexts []⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15
    ], [88799], .contexts [
        ⟨52574, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨52575, false, false, [], [5, 3, 1, 15]⟩,
        ⟨52576, false, false, [], [5, 3, 1, 15]⟩,
        ⟨52505, false, false, [], [5, 3, 1, 15]⟩,
        ⟨52505, false, false, [], [5, 3, 1, 15]⟩,
        ⟨52502, false, false, [], [3, 1, 15]⟩,
        ⟨52501, false, false, [], [3, 1, 15]⟩,
        ⟨52501, false, false, [], [3, 1, 15]⟩,
        ⟨52497, false, false, [], [3, 1, 15]⟩,
        ⟨20, false, false, [88803], [1, 15]⟩,
        ⟨52498, false, false, [], [1, 15]⟩,
        ⟨52498, false, false, [], [1, 15]⟩,
        ⟨52498, false, false, [], [1, 15]⟩,
        ⟨52495, false, false, [], [1, 15]⟩,
        ⟨8, false, false, [88801], [15]⟩,
        ⟨52496, false, false, [], [15]⟩,
        ⟨52496, false, false, [], [15]⟩,
        ⟨52496, false, false, [], [15]⟩,
        ⟨52493, false, false, [], [15]⟩,
        ⟨1, false, false, [88799], []⟩,
        ⟨52494, false, false, [], []⟩,
        ⟨52494, false, false, [], []⟩,
        ⟨52494, false, false, [], []⟩
      ]⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [88791], .contexts [
        ⟨52577, false, false, [], [13, 1, 11, 9]⟩,
        ⟨52491, false, false, [], [13, 1, 11, 9]⟩,
        ⟨59, false, false, [88797], [1, 11, 9]⟩,
        ⟨52492, false, false, [], [1, 11, 9]⟩,
        ⟨52492, false, false, [], [1, 11, 9]⟩,
        ⟨52492, false, false, [], [1, 11, 9]⟩,
        ⟨52489, false, false, [], [1, 11, 9]⟩,
        ⟨8, false, false, [88795], [11, 9]⟩,
        ⟨52490, false, false, [], [11, 9]⟩,
        ⟨52490, false, false, [], [11, 9]⟩,
        ⟨52490, false, false, [], [11, 9]⟩,
        ⟨52487, false, false, [], [11, 9]⟩,
        ⟨53, false, false, [88793], [9]⟩,
        ⟨52488, false, false, [], [9]⟩,
        ⟨52488, false, false, [], [9]⟩,
        ⟨52488, false, false, [], [9]⟩,
        ⟨52485, false, false, [], [9]⟩,
        ⟨46, false, false, [88791], []⟩,
        ⟨52486, false, false, [], []⟩,
        ⟨52486, false, false, [], []⟩,
        ⟨52486, false, false, [], []⟩
      ]⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1
    ], [88783], .contexts [
        ⟨52578, false, false, [], [1, 5, 3, 1]⟩,
        ⟨52483, false, false, [], [1, 5, 3, 1]⟩,
        ⟨8, false, false, [88789], [5, 3, 1]⟩,
        ⟨52484, false, false, [], [5, 3, 1]⟩,
        ⟨52484, false, false, [], [5, 3, 1]⟩,
        ⟨52484, false, false, [], [5, 3, 1]⟩,
        ⟨52481, false, false, [], [5, 3, 1]⟩,
        ⟨28, false, false, [88787], [3, 1]⟩,
        ⟨52482, false, false, [], [3, 1]⟩,
        ⟨52482, false, false, [], [3, 1]⟩,
        ⟨52482, false, false, [], [3, 1]⟩,
        ⟨52479, false, false, [], [3, 1]⟩,
        ⟨20, false, false, [88785], [1]⟩,
        ⟨52480, false, false, [], [1]⟩,
        ⟨52480, false, false, [], [1]⟩,
        ⟨52480, false, false, [], [1]⟩,
        ⟨52477, false, false, [], [1]⟩,
        ⟨8, false, false, [88783], []⟩,
        ⟨52478, false, false, [], []⟩,
        ⟨52478, false, false, [], []⟩,
        ⟨52478, false, false, [], []⟩
      ]⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11
    ], [88775], .contexts [
        ⟨52579, false, false, [], [15, 13, 1, 11]⟩,
        ⟨52475, false, false, [], [15, 13, 1, 11]⟩,
        ⟨1, false, false, [88781], [13, 1, 11]⟩,
        ⟨52476, false, false, [], [13, 1, 11]⟩,
        ⟨52476, false, false, [], [13, 1, 11]⟩,
        ⟨52476, false, false, [], [13, 1, 11]⟩,
        ⟨52473, false, false, [], [13, 1, 11]⟩,
        ⟨59, false, false, [88779], [1, 11]⟩,
        ⟨52474, false, false, [], [1, 11]⟩,
        ⟨52474, false, false, [], [1, 11]⟩,
        ⟨52474, false, false, [], [1, 11]⟩,
        ⟨52471, false, false, [], [1, 11]⟩,
        ⟨8, false, false, [88777], [11]⟩,
        ⟨52472, false, false, [], [11]⟩,
        ⟨52472, false, false, [], [11]⟩,
        ⟨52472, false, false, [], [11]⟩,
        ⟨52469, false, false, [], [11]⟩,
        ⟨53, false, false, [88775], []⟩,
        ⟨52470, false, false, [], []⟩,
        ⟨52470, false, false, [], []⟩,
        ⟨52470, false, false, [], []⟩
      ]⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [88767], .contexts [
        ⟨52580, false, false, [], [9, 1, 5, 3]⟩,
        ⟨52467, false, false, [], [9, 1, 5, 3]⟩,
        ⟨46, false, false, [88773], [1, 5, 3]⟩,
        ⟨52468, false, false, [], [1, 5, 3]⟩,
        ⟨52468, false, false, [], [1, 5, 3]⟩,
        ⟨52468, false, false, [], [1, 5, 3]⟩,
        ⟨52465, false, false, [], [1, 5, 3]⟩,
        ⟨8, false, false, [88771], [5, 3]⟩,
        ⟨52466, false, false, [], [5, 3]⟩,
        ⟨52466, false, false, [], [5, 3]⟩,
        ⟨52466, false, false, [], [5, 3]⟩,
        ⟨52463, false, false, [], [5, 3]⟩,
        ⟨28, false, false, [88769], [3]⟩,
        ⟨52464, false, false, [], [3]⟩,
        ⟨52464, false, false, [], [3]⟩,
        ⟨52464, false, false, [], [3]⟩,
        ⟨52461, false, false, [], [3]⟩,
        ⟨20, false, false, [88767], []⟩,
        ⟨52462, false, false, [], []⟩,
        ⟨52462, false, false, [], []⟩,
        ⟨52462, false, false, [], []⟩
      ]⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1
    ], [88759], .contexts [
        ⟨52581, false, false, [], [1, 15, 13, 1]⟩,
        ⟨52459, false, false, [], [1, 15, 13, 1]⟩,
        ⟨8, false, false, [88765], [15, 13, 1]⟩,
        ⟨52460, false, false, [], [15, 13, 1]⟩,
        ⟨52460, false, false, [], [15, 13, 1]⟩,
        ⟨52460, false, false, [], [15, 13, 1]⟩,
        ⟨52457, false, false, [], [15, 13, 1]⟩,
        ⟨1, false, false, [88763], [13, 1]⟩,
        ⟨52458, false, false, [], [13, 1]⟩,
        ⟨52458, false, false, [], [13, 1]⟩,
        ⟨52458, false, false, [], [13, 1]⟩,
        ⟨52455, false, false, [], [13, 1]⟩,
        ⟨59, false, false, [88761], [1]⟩,
        ⟨52456, false, false, [], [1]⟩,
        ⟨52456, false, false, [], [1]⟩,
        ⟨52456, false, false, [], [1]⟩,
        ⟨52453, false, false, [], [1]⟩,
        ⟨8, false, false, [88759], []⟩,
        ⟨52454, false, false, [], []⟩,
        ⟨52454, false, false, [], []⟩,
        ⟨52454, false, false, [], []⟩
      ]⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5
    ], [88751], .contexts [
        ⟨52582, false, false, [], [11, 9, 1, 5]⟩,
        ⟨52451, false, false, [], [11, 9, 1, 5]⟩,
        ⟨53, false, false, [88757], [9, 1, 5]⟩,
        ⟨52452, false, false, [], [9, 1, 5]⟩,
        ⟨52452, false, false, [], [9, 1, 5]⟩,
        ⟨52452, false, false, [], [9, 1, 5]⟩,
        ⟨52449, false, false, [], [9, 1, 5]⟩,
        ⟨46, false, false, [88755], [1, 5]⟩,
        ⟨52450, false, false, [], [1, 5]⟩,
        ⟨52450, false, false, [], [1, 5]⟩,
        ⟨52450, false, false, [], [1, 5]⟩,
        ⟨52447, false, false, [], [1, 5]⟩,
        ⟨8, false, false, [88753], [5]⟩,
        ⟨52448, false, false, [], [5]⟩,
        ⟨52448, false, false, [], [5]⟩,
        ⟨52448, false, false, [], [5]⟩,
        ⟨52445, false, false, [], [5]⟩,
        ⟨28, false, false, [88751], []⟩,
        ⟨52446, false, false, [], []⟩,
        ⟨52446, false, false, [], []⟩,
        ⟨52446, false, false, [], []⟩
      ]⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [88743], .contexts [
        ⟨52583, false, false, [], [3, 1, 15, 13]⟩,
        ⟨52443, false, false, [], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [88749], [1, 15, 13]⟩,
        ⟨52444, false, false, [], [1, 15, 13]⟩,
        ⟨52444, false, false, [], [1, 15, 13]⟩,
        ⟨52444, false, false, [], [1, 15, 13]⟩,
        ⟨52441, false, false, [], [1, 15, 13]⟩,
        ⟨8, false, false, [88747], [15, 13]⟩,
        ⟨52442, false, false, [], [15, 13]⟩,
        ⟨52442, false, false, [], [15, 13]⟩,
        ⟨52442, false, false, [], [15, 13]⟩,
        ⟨52439, false, false, [], [15, 13]⟩,
        ⟨1, false, false, [88745], [13]⟩,
        ⟨52440, false, false, [], [13]⟩,
        ⟨52440, false, false, [], [13]⟩,
        ⟨52440, false, false, [], [13]⟩,
        ⟨52437, false, false, [], [13]⟩,
        ⟨59, false, false, [88743], []⟩,
        ⟨52438, false, false, [], []⟩,
        ⟨52438, false, false, [], []⟩,
        ⟨52438, false, false, [], []⟩
      ]⟩,
    ⟨[88741], [88741], .contexts []⟩,
    ⟨[88739], [88739], .contexts []⟩,
    ⟨[88737], [88737], .contexts []⟩,
    ⟨[88735], [88735], .contexts []⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1
    ], [88735], .contexts [
        ⟨52584, false, false, [], [1, 11, 9, 1]⟩,
        ⟨52435, true, false, [], [1, 11, 9, 1]⟩,
        ⟨8, false, false, [88741], [11, 9, 1]⟩,
        ⟨52436, false, false, [], [11, 9, 1]⟩,
        ⟨52585, false, false, [], [11, 9, 1]⟩,
        ⟨52436, false, false, [], [11, 9, 1]⟩,
        ⟨52436, false, false, [], [11, 9, 1]⟩,
        ⟨52433, false, false, [], [9, 1]⟩,
        ⟨52586, false, false, [], [9, 1]⟩,
        ⟨52432, false, false, [], [9, 1]⟩,
        ⟨52432, false, false, [], [9, 1]⟩,
        ⟨52429, false, false, [], [1]⟩,
        ⟨52587, false, false, [], [1]⟩,
        ⟨52428, false, false, [], [1]⟩,
        ⟨52428, false, false, [], [1]⟩,
        ⟨52425, false, false, [], []⟩,
        ⟨52588, false, false, [], []⟩,
        ⟨52424, false, false, [], []⟩,
        ⟨52424, false, false, [], []⟩
      ]⟩,
    ⟨[88731], [88731], .contexts []⟩,
    ⟨[88727], [88727], .contexts []⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15
    ], [88727], .contexts [
        ⟨52589, false, false, [], [5, 3, 1, 15]⟩,
        ⟨52420, true, false, [], [5, 3, 1, 15]⟩,
        ⟨28, false, false, [88733], [3, 1, 15]⟩,
        ⟨52421, false, false, [], [3, 1, 15]⟩,
        ⟨52421, false, false, [], [3, 1, 15]⟩,
        ⟨52421, false, false, [], [3, 1, 15]⟩,
        ⟨52417, true, false, [], [3, 1, 15]⟩,
        ⟨20, false, false, [88731], [1, 15]⟩,
        ⟨52418, false, false, [], [1, 15]⟩,
        ⟨52590, false, false, [], [1, 15]⟩,
        ⟨52418, false, false, [], [1, 15]⟩,
        ⟨52418, false, false, [], [1, 15]⟩,
        ⟨52415, false, false, [], [15]⟩,
        ⟨52407, false, false, [], [15]⟩,
        ⟨52408, false, false, [], [15]⟩,
        ⟨52408, false, false, [], [15]⟩,
        ⟨52406, false, false, [], []⟩,
        ⟨52591, false, false, [], []⟩,
        ⟨52405, false, false, [], []⟩,
        ⟨52405, false, false, [], []⟩
      ]⟩,
    ⟨[88719, 1], [23233, 88719], .contexts [
        ⟨52370, false, false, [], []⟩
      ]⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [23233, 88719], .contexts [
        ⟨52592, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨52409, false, false, [], [1, 11, 9, 1]⟩,
        ⟨52395, false, false, [], [1, 11, 9, 1]⟩,
        ⟨52396, false, false, [], [1, 11, 9, 1]⟩,
        ⟨52396, false, false, [], [1, 11, 9, 1]⟩,
        ⟨52394, false, false, [], [11, 9, 1]⟩,
        ⟨52386, false, false, [], [11, 9, 1]⟩,
        ⟨52387, false, false, [], [11, 9, 1]⟩,
        ⟨52387, false, false, [], [11, 9, 1]⟩,
        ⟨52385, true, false, [], [11, 9, 1]⟩,
        ⟨53, false, false, [88721], [9, 1]⟩,
        ⟨52379, false, false, [], [9, 1]⟩,
        ⟨52378, false, false, [], [9, 1]⟩,
        ⟨52379, false, false, [], [9, 1]⟩,
        ⟨52379, false, false, [], [9, 1]⟩,
        ⟨52376, true, false, [], [9, 1]⟩,
        ⟨46, false, false, [88719], [1]⟩,
        ⟨52364, false, false, [], [1]⟩,
        ⟨52363, false, false, [], [1]⟩,
        ⟨52364, false, false, [], [1]⟩,
        ⟨52364, false, false, [], [1]⟩,
        ⟨52593, false, false, [], []⟩,
        ⟨52366, false, false, [], []⟩,
        ⟨52367, false, false, [], []⟩,
        ⟨52367, false, false, [], []⟩
      ]⟩,
    ⟨[23245], [23233, 23243], .source 11687⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13
    ], [23245, 88711], .contexts [
        ⟨52594, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨52362, false, false, [23233], [3, 1, 15, 13]⟩,
        ⟨52346, false, false, [], [3, 1, 15, 13]⟩,
        ⟨52347, false, false, [], [3, 1, 15, 13]⟩,
        ⟨52348, false, false, [], [3, 1, 15, 13]⟩,
        ⟨52337, false, false, [23233], [1, 15, 13]⟩,
        ⟨52343, false, false, [], [1, 15, 13]⟩,
        ⟨52344, false, false, [], [1, 15, 13]⟩,
        ⟨52345, false, false, [], [1, 15, 13]⟩,
        ⟨52316, false, false, [23233], [15, 13]⟩,
        ⟨52288, false, false, [], [15, 13]⟩,
        ⟨52289, false, false, [], [15, 13]⟩,
        ⟨52290, false, false, [], [15, 13]⟩,
        ⟨52313, false, false, [23233], [13]⟩,
        ⟨52595, true, false, [], [88713, 13]⟩,
        ⟨52282, false, false, [23245], []⟩
      ]⟩,
    ⟨[23247], [23245, 19499], .source 11688⟩,
    ⟨[23249], [23247, 21109], .source 11689⟩,
    ⟨[23251], [23249, 15065], .source 11690⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5
    ], [23251, 87575], .contexts [
        ⟨52596, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨52242, false, false, [23245], [11, 9, 1, 5]⟩,
        ⟨52217, false, false, [23245], [9, 1, 5]⟩,
        ⟨39003, false, false, [23245], [1, 5]⟩,
        ⟨52597, true, false, [], [85611, 1, 5]⟩,
        ⟨44701, true, false, [23247, 21106], [1, 5]⟩,
        ⟨8, false, false, [23247, 21106, 87573], [5]⟩,
        ⟨44245, true, false, [23247], [87573, 5]⟩,
        ⟨52598, true, false, [], [87573, 5]⟩,
        ⟨44721, false, false, [23249], []⟩,
        ⟨52599, true, false, [], [87575]⟩
      ]⟩,
    ⟨[23253], [23251, 2575], .source 11691⟩,
    ⟨[23255], [23253, 7357], .source 11692⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1
    ], [23255, 82811], .contexts [
        ⟨52600, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨44714, false, false, [23251], [1, 15, 13, 1]⟩,
        ⟨17076, false, false, [23251], [15, 13, 1]⟩,
        ⟨16994, false, false, [23251], [13, 1]⟩,
        ⟨16990, false, false, [23251], [1]⟩,
        ⟨52601, true, false, [], [82815, 1]⟩,
        ⟨16972, false, false, [23253], []⟩,
        ⟨52602, true, false, [], [82811]⟩
      ]⟩,
    ⟨[23257], [23255, 15205], .source 11693⟩,
    ⟨[23259], [23257, 281], .source 11694⟩,
    ⟨[23261], [23259, 15221], .source 11695⟩,
    ⟨[23263], [23261, 15227], .source 11696⟩]

/-- Exact literal claimed equations and contextual derivations, block 822. -/
def y322TCIndexRaw822 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[23265], [23263, 15215], .source 11697⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3
    ], [23265, 82657], .contexts [
        ⟨52603, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨16920, false, false, [23255], [9, 1, 5, 3]⟩,
        ⟨52604, true, false, [], [82653, 9, 1, 5, 3]⟩,
        ⟨14970, false, false, [23257], [1, 5, 3]⟩,
        ⟨52605, true, false, [], [82653, 1, 5, 3]⟩,
        ⟨15094, false, false, [23259], [5, 3]⟩,
        ⟨52606, true, false, [], [82663, 5, 3]⟩,
        ⟨15098, false, false, [23261], [3]⟩,
        ⟨52607, true, false, [], [79381, 3]⟩,
        ⟨15015, false, false, [23263], []⟩,
        ⟨52608, true, false, [], [82657]⟩
      ]⟩,
    ⟨[23267], [23265, 15211], .source 11698⟩,
    ⟨[23269], [23267, 1077], .source 11699⟩,
    ⟨[23271], [23269, 11449], .source 11700⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [23271, 79185], .contexts [
        ⟨52609, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨15006, false, false, [23265], [15, 13, 1, 11]⟩,
        ⟨52610, true, false, [], [78843, 15, 13, 1, 11]⟩,
        ⟨5212, false, false, [23267], [13, 1, 11]⟩,
        ⟨4914, false, false, [23267], [1, 11]⟩,
        ⟨52611, true, false, [], [78735, 1, 11]⟩,
        ⟨5074, false, false, [23269], [11]⟩,
        ⟨12999, false, false, [23269], []⟩,
        ⟨52612, true, false, [], [79185]⟩
      ]⟩,
    ⟨[23273], [23271, 563], .source 11701⟩,
    ⟨[23275], [23273, 563], .source 11702⟩,
    ⟨[23277], [23275, 22677], .source 11703⟩,
    ⟨[23279], [23277, 22671], .source 11704⟩,
    ⟨[
      88831, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1
    ], [23279, 87417], .contexts [
        ⟨52613, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨6261, false, false, [23271], [1, 5, 3, 1]⟩,
        ⟨52614, true, false, [], [79005, 1, 5, 3, 1]⟩,
        ⟨5513, false, false, [23273], [5, 3, 1]⟩,
        ⟨52615, true, false, [], [79005, 5, 3, 1]⟩,
        ⟨16635, false, false, [23275], [3, 1]⟩,
        ⟨49976, false, false, [23275], [1]⟩,
        ⟨52616, true, false, [], [88343, 1]⟩,
        ⟨49966, false, false, [23277], []⟩,
        ⟨52617, true, false, [], [87417]⟩
      ]⟩,
    ⟨[23279, 87419], [23279, 87419], .contexts []⟩,
    ⟨[23279, 87419], [23279, 87419], .contexts []⟩,
    ⟨[88833, 13], [88833, 13], .contexts []⟩,
    ⟨[88833, 13], [23279, 87419], .contexts [
        ⟨52621, false, false, [], []⟩,
        ⟨52553, true, false, [], [13]⟩,
        ⟨52553, true, false, [], [13]⟩,
        ⟨52552, true, false, [], [13]⟩,
        ⟨5361, false, false, [88831], []⟩,
        ⟨5362, false, false, [88831], []⟩,
        ⟨52618, false, false, [], [15]⟩,
        ⟨41573, false, false, [23279], []⟩,
        ⟨52619, false, false, [], []⟩,
        ⟨52620, false, false, [], []⟩,
        ⟨41974, false, false, [23279], []⟩,
        ⟨13, true, false, [], [23279, 87419]⟩
      ]⟩,
    ⟨[23281], [23278], .source 11705⟩,
    ⟨[87419, 13], [23281, 88833], .contexts [
        ⟨52622, true, false, [23278], [13]⟩,
        ⟨59, false, false, [23278, 88833], []⟩,
        ⟨52623, true, false, [], [88833]⟩
      ]⟩,
    ⟨[88831], [88831], .contexts []⟩,
    ⟨[23283], [23279, 20441], .source 11706⟩,
    ⟨[23283, 87419], [23283, 87419], .contexts []⟩,
    ⟨[23283, 87419], [23283, 87419], .contexts []⟩,
    ⟨[88831, 13], [88831, 13], .contexts []⟩,
    ⟨[88831, 13], [23283, 87419], .contexts [
        ⟨52629, false, false, [], []⟩,
        ⟨52551, true, false, [], [13]⟩,
        ⟨52551, true, false, [], [13]⟩,
        ⟨52625, true, false, [], [13]⟩,
        ⟨52551, true, false, [], [13]⟩,
        ⟨8, true, false, [88831], [13]⟩,
        ⟨52550, false, false, [], [1, 13]⟩,
        ⟨115, false, false, [88833], []⟩,
        ⟨118, false, false, [88833], []⟩,
        ⟨52621, false, false, [], [1, 13, 1]⟩,
        ⟨52622, false, false, [], [1, 13, 1]⟩,
        ⟨52619, false, false, [], [1, 13, 1]⟩,
        ⟨52620, false, false, [], [1, 13, 1]⟩,
        ⟨52620, false, false, [], [1, 13, 1]⟩,
        ⟨41577, false, false, [23279], [13, 1]⟩,
        ⟨41988, false, false, [23279], [1]⟩,
        ⟨52626, true, false, [], [87421, 1]⟩,
        ⟨41579, false, false, [23283], []⟩,
        ⟨52627, false, false, [], []⟩,
        ⟨52628, false, false, [], []⟩,
        ⟨41974, false, false, [23283], []⟩
      ]⟩,
    ⟨[88831, 13], [23283, 87419], .contexts [
        ⟨52630, false, false, [], []⟩,
        ⟨13, true, false, [], [23283, 87419]⟩
      ]⟩,
    ⟨[23285], [23282], .source 11707⟩,
    ⟨[23281, 88833], [23281, 88833], .contexts []⟩,
    ⟨[23287], [23279, 23285], .source 11708⟩,
    ⟨[88831, 13], [23283, 87419], .contexts [
        ⟨52629, false, false, [], []⟩,
        ⟨52631, false, false, [], []⟩,
        ⟨52627, false, false, [], []⟩,
        ⟨52628, false, false, [], []⟩,
        ⟨52628, false, false, [], []⟩
      ]⟩,
    ⟨[23289], [23283, 20427], .source 11709⟩,
    ⟨[23287, 88831], [23287, 88831], .contexts []⟩,
    ⟨[88833], [23287, 88831], .contexts [
        ⟨52633, true, false, [23280], []⟩,
        ⟨52633, true, false, [23280], []⟩,
        ⟨52624, true, false, [23280], []⟩,
        ⟨52631, true, false, [23280, 23282], [13]⟩,
        ⟨59, false, false, [23280, 23282, 88831], []⟩,
        ⟨52632, true, false, [23280], [88831]⟩,
        ⟨52623, false, true, [], [23285, 88831]⟩,
        ⟨52634, true, false, [], [88831]⟩,
        ⟨52637, false, false, [], []⟩
      ]⟩,
    ⟨[23291], [23281, 23287], .source 11710⟩,
    ⟨[23293], [23289, 23291], .source 11711⟩,
    ⟨[88831], [88831], .contexts []⟩,
    ⟨[88831, 3], [88831, 3], .contexts []⟩,
    ⟨[88831], [88831], .contexts []⟩,
    ⟨[23295], [23292], .source 11712⟩,
    ⟨[23292], [23292], .contexts []⟩,
    ⟨[88831, 3], [23295, 88831], .contexts [
        ⟨52642, false, false, [], []⟩,
        ⟨52640, false, false, [23292], [88831, 3]⟩,
        ⟨52639, false, false, [23292, 23289], [88831, 3]⟩,
        ⟨52638, true, false, [23292, 23289, 23281], [3]⟩,
        ⟨52624, true, false, [23292, 23289], [3]⟩,
        ⟨52636, false, false, [23292], [87419, 13, 3]⟩,
        ⟨41977, true, false, [23292, 23283], [13, 3]⟩,
        ⟨52635, true, false, [23292], [3, 13, 3]⟩,
        ⟨4550, false, false, [23292, 88831], []⟩,
        ⟨52641, false, false, [23292], []⟩,
        ⟨52643, false, false, [23292], []⟩,
        ⟨52645, true, false, [], [88831]⟩,
        ⟨52645, true, false, [], [88831]⟩,
        ⟨52644, true, false, [], [88831]⟩
      ]⟩,
    ⟨[23297], [23283, 20421], .source 11713⟩,
    ⟨[23299], [23297, 19911], .source 11714⟩,
    ⟨[23301], [23298], .source 11715⟩,
    ⟨[23301], [23301], .contexts []⟩,
    ⟨[23301], [23298], .contexts [
        ⟨52649, false, false, [], []⟩
      ]⟩,
    ⟨[23298], [23298], .contexts []⟩,
    ⟨[23301], [23298], .contexts [
        ⟨52650, false, false, [], []⟩,
        ⟨52651, false, false, [], []⟩,
        ⟨52652, false, false, [], []⟩,
        ⟨52652, false, false, [], []⟩
      ]⟩,
    ⟨[86423, 5], [23301, 88831], .contexts [
        ⟨52648, false, false, [23298], [86423, 5]⟩,
        ⟨40440, false, false, [23298, 23297], [86423, 5]⟩,
        ⟨36993, true, false, [23298, 23297, 19101], [5]⟩,
        ⟨36972, true, false, [23298, 23297], [5]⟩,
        ⟨52647, false, false, [23298], [83327, 13, 5]⟩,
        ⟨42122, true, false, [23298, 23283], [13, 5]⟩,
        ⟨52635, true, false, [23298], [5, 13, 5]⟩,
        ⟨1116, false, false, [23298, 88831], []⟩,
        ⟨52641, false, false, [23298], []⟩,
        ⟨52643, false, false, [23298], []⟩,
        ⟨52653, true, false, [], [88831]⟩
      ]⟩,
    ⟨[23299], [23300], .contexts [
        ⟨52649, true, true, [], []⟩
      ]⟩,
    ⟨[88831, 5], [23299, 86423], .contexts [
        ⟨52654, true, false, [23300], [5]⟩,
        ⟨28, false, false, [23300, 86423], []⟩,
        ⟨52655, true, false, [], [86423]⟩
      ]⟩,
    ⟨[23303], [23283, 20435], .source 11716⟩,
    ⟨[83577, 13], [83577, 13], .contexts []⟩,
    ⟨[88829], [88829], .contexts []⟩,
    ⟨[23305], [23302], .source 11717⟩,
    ⟨[23302], [23302], .contexts []⟩,
    ⟨[83577, 13], [23305, 88829], .contexts [
        ⟨52658, false, false, [], []⟩,
        ⟨52657, false, false, [23302], [83577, 13]⟩,
        ⟨42136, true, false, [23302, 23283], [13]⟩,
        ⟨52635, true, false, [23302], [11, 13]⟩,
        ⟨931, false, false, [23302, 88831], []⟩,
        ⟨54, false, false, [23302, 88831], []⟩,
        ⟨52555, false, false, [23302], []⟩,
        ⟨52659, false, false, [23302], []⟩,
        ⟨52661, true, false, [], [88829]⟩,
        ⟨52661, true, false, [], [88829]⟩,
        ⟨52660, true, false, [], [88829]⟩
      ]⟩,
    ⟨[23303], [23304], .contexts [
        ⟨52660, true, true, [], []⟩
      ]⟩,
    ⟨[88829, 1], [23287, 88829], .contexts [
        ⟨52555, true, false, [], [1]⟩,
        ⟨562, false, false, [88831], []⟩,
        ⟨563, false, false, [88831], []⟩,
        ⟨52552, false, false, [], [11]⟩,
        ⟨52638, false, false, [], [11]⟩,
        ⟨52637, false, false, [], [11]⟩,
        ⟨52637, false, false, [], [11]⟩,
        ⟨52548, false, false, [23287], []⟩,
        ⟨52659, false, false, [23287], []⟩,
        ⟨13, true, false, [], [23287, 88829]⟩
      ]⟩,
    ⟨[23295, 88831], [23295, 88831], .contexts []⟩,
    ⟨[23295, 88829], [23295, 88829], .contexts []⟩,
    ⟨[23295, 88829], [23295, 88829], .contexts []⟩,
    ⟨[88829, 3], [88829, 3], .contexts []⟩,
    ⟨[88829, 3], [23295, 88829], .contexts [
        ⟨52668, false, false, [], []⟩,
        ⟨52555, true, false, [], [3]⟩,
        ⟨215, false, false, [88831], []⟩,
        ⟨216, false, false, [88831], []⟩,
        ⟨52642, false, false, [], [11]⟩,
        ⟨52646, false, false, [], [11]⟩,
        ⟨52665, false, false, [], [11]⟩,
        ⟨52665, false, false, [], [11]⟩,
        ⟨52548, false, false, [23295], []⟩,
        ⟨52666, false, false, [], []⟩,
        ⟨52667, false, false, [], []⟩,
        ⟨52659, false, false, [23295], []⟩,
        ⟨13, true, false, [], [23295, 88829]⟩
      ]⟩,
    ⟨[23299, 86423], [23299, 86423], .contexts []⟩,
    ⟨[23299, 86423], [23299, 86423], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 823. -/
def y322TCIndexRaw823 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[23299, 86421], [23299, 86421], .contexts []⟩,
    ⟨[23299, 86421], [23299, 86421], .contexts []⟩,
    ⟨[88829, 5], [88829, 5], .contexts []⟩,
    ⟨[23299], [23299], .contexts []⟩,
    ⟨[88829, 5], [23299, 86421], .contexts [
        ⟨52674, false, false, [], []⟩,
        ⟨52555, true, false, [], [5]⟩,
        ⟨642, false, false, [88831], []⟩,
        ⟨643, false, false, [88831], []⟩,
        ⟨52656, false, false, [], [11]⟩,
        ⟨52670, false, false, [], [11]⟩,
        ⟨52671, false, false, [], [11]⟩,
        ⟨52671, false, false, [], [11]⟩,
        ⟨36822, false, false, [23299], []⟩,
        ⟨52672, false, false, [], []⟩,
        ⟨52673, false, false, [], []⟩,
        ⟨36998, false, false, [23299], []⟩,
        ⟨52675, true, false, [], [86421]⟩,
        ⟨13, true, false, [], [23299, 86421]⟩
      ]⟩,
    ⟨[86421, 5], [23301, 88829], .contexts [
        ⟨52676, true, false, [23298], [5]⟩,
        ⟨28, false, false, [23298, 88829], []⟩,
        ⟨52649, true, false, [], [88829]⟩
      ]⟩,
    ⟨[23305, 88829], [23305, 88829], .contexts []⟩,
    ⟨[83577, 13], [23305, 88829], .contexts [
        ⟨52658, false, false, [], []⟩,
        ⟨52662, false, false, [], []⟩,
        ⟨52678, false, false, [], []⟩,
        ⟨52678, false, false, [], []⟩
      ]⟩,
    ⟨[23307], [21075, 21089], .source 11718⟩,
    ⟨[23309], [17259, 23307], .source 11719⟩,
    ⟨[88829, 7], [88829, 7], .contexts []⟩,
    ⟨[87559], [87559], .contexts []⟩,
    ⟨[23303], [23304], .contexts [
        ⟨52663, false, false, [], []⟩
      ]⟩,
    ⟨[23311], [23303, 23309], .source 11720⟩,
    ⟨[88829, 7], [23311, 87559], .contexts [
        ⟨52682, false, false, [], []⟩,
        ⟨52679, true, false, [23304], [7]⟩,
        ⟨73, false, false, [23304, 83577], []⟩,
        ⟨74, false, false, [23304, 83577], []⟩,
        ⟨27062, false, false, [23304], [13]⟩,
        ⟨27056, false, false, [23304], [13]⟩,
        ⟨27057, false, false, [23304], [13]⟩,
        ⟨27057, false, false, [23304], [13]⟩,
        ⟨44128, false, false, [23304, 17259], []⟩,
        ⟨44147, false, false, [23304, 17259, 21075], []⟩,
        ⟨52680, true, false, [23304, 17259], [87559]⟩,
        ⟨52681, true, false, [23304], [87559]⟩,
        ⟨52683, false, false, [23304, 23309], []⟩,
        ⟨52684, true, false, [], [23309, 87559]⟩,
        ⟨52685, true, false, [], [87559]⟩
      ]⟩,
    ⟨[23313], [23310], .source 11721⟩,
    ⟨[87559, 7], [23313, 88829], .contexts [
        ⟨52686, true, false, [23310], [7]⟩,
        ⟨38, false, false, [23310, 88829], []⟩,
        ⟨52687, true, false, [], [88829]⟩
      ]⟩,
    ⟨[23305, 88827], [23305, 88827], .contexts []⟩,
    ⟨[23305, 88827], [23305, 88827], .contexts []⟩,
    ⟨[88827, 13], [88827, 13], .contexts []⟩,
    ⟨[23304], [23304], .contexts []⟩,
    ⟨[88827, 13], [23303, 83579], .contexts [
        ⟨52691, false, false, [], []⟩,
        ⟨52690, true, false, [23304], [13]⟩,
        ⟨52689, true, false, [23304], [13]⟩,
        ⟨52544, true, false, [], [13]⟩,
        ⟨52679, true, false, [23304], [9, 13]⟩,
        ⟨942, false, false, [23304, 83577], []⟩,
        ⟨26538, false, false, [23304], []⟩,
        ⟨26537, false, false, [23304], []⟩,
        ⟨26540, false, false, [23304], []⟩,
        ⟨52692, true, false, [], [83579]⟩,
        ⟨52692, true, false, [], [83579]⟩,
        ⟨52684, true, false, [], [83579]⟩
      ]⟩,
    ⟨[83579, 13], [23305, 88827], .contexts [
        ⟨52693, true, false, [23302], [13]⟩,
        ⟨59, false, false, [23302, 88827], []⟩,
        ⟨52660, true, false, [], [88827]⟩
      ]⟩,
    ⟨[88829, 9], [88827], .contexts [
        ⟨52556, false, false, [], []⟩,
        ⟨52557, false, false, [], []⟩,
        ⟨52543, false, false, [], []⟩,
        ⟨52543, false, false, [], []⟩
      ]⟩,
    ⟨[88829, 8], [88829, 9], .contexts [
        ⟨47, false, false, [88829], []⟩
      ]⟩,
    ⟨[88827], [88827], .contexts []⟩,
    ⟨[23294], [23294], .contexts []⟩,
    ⟨[88827, 3], [23293, 88827], .contexts [
        ⟨52544, true, false, [], [3]⟩,
        ⟨52667, true, false, [23294], [9, 3]⟩,
        ⟨52667, true, false, [23294], [9, 3]⟩,
        ⟨52666, true, false, [23294], [9, 3]⟩,
        ⟨52669, true, false, [23294], [9, 3]⟩,
        ⟨52668, true, false, [23294], [9, 3]⟩,
        ⟨573, false, false, [23294, 88829], []⟩,
        ⟨52696, false, false, [23294], []⟩,
        ⟨52695, false, false, [23294], []⟩,
        ⟨52697, false, false, [23294], []⟩,
        ⟨52698, true, false, [], [88827]⟩,
        ⟨52698, true, false, [], [88827]⟩,
        ⟨52644, false, true, [], [88827]⟩
      ]⟩,
    ⟨[88829, 5], [23299, 86421], .contexts [
        ⟨52674, false, false, [], []⟩,
        ⟨52676, false, false, [], []⟩,
        ⟨52672, false, false, [], []⟩,
        ⟨52673, false, false, [], []⟩,
        ⟨52673, false, false, [], []⟩
      ]⟩,
    ⟨[23299, 86419], [23299, 86419], .contexts []⟩,
    ⟨[86419, 5], [86419, 5], .contexts []⟩,
    ⟨[86419, 5], [23301, 88827], .contexts [
        ⟨52702, false, false, [], []⟩,
        ⟨52701, true, false, [23298], [5]⟩,
        ⟨36818, true, false, [], [5]⟩,
        ⟨52700, true, false, [23298], [9, 5]⟩,
        ⟨960, false, false, [23298, 88829], []⟩,
        ⟨52696, false, false, [23298], []⟩,
        ⟨52695, false, false, [23298], []⟩,
        ⟨52697, false, false, [23298], []⟩,
        ⟨52653, true, false, [], [88827]⟩
      ]⟩,
    ⟨[23317], [23299, 22663], .source 11723⟩,
    ⟨[23317, 84981], [23317, 84981], .contexts []⟩,
    ⟨[84981, 15], [84981, 15], .contexts []⟩,
    ⟨[23319], [23316], .source 11724⟩,
    ⟨[23316], [23316], .contexts []⟩,
    ⟨[84981, 15], [23319, 88829], .contexts [
        ⟨52706, false, false, [], []⟩,
        ⟨52705, true, false, [23316], [15]⟩,
        ⟨29631, true, false, [], [15]⟩,
        ⟨52704, false, false, [23316], [84979, 5, 15]⟩,
        ⟨49881, true, false, [23316, 23299], [5, 15]⟩,
        ⟨52700, true, false, [23316], [15, 5, 15]⟩,
        ⟨885, false, false, [23316, 88829], []⟩,
        ⟨52659, false, false, [23316], []⟩,
        ⟨52708, true, false, [], [88829]⟩,
        ⟨52708, true, false, [], [88829]⟩,
        ⟨52707, true, false, [], [88829]⟩
      ]⟩,
    ⟨[23317], [23318], .contexts [
        ⟨52707, true, true, [], []⟩
      ]⟩,
    ⟨[23311, 87559], [23311, 87559], .contexts []⟩,
    ⟨[23311, 87557], [23311, 87557], .contexts []⟩,
    ⟨[23310], [23310], .contexts []⟩,
    ⟨[87557, 7], [23313, 88831], .contexts [
        ⟨52712, true, false, [23310], [7]⟩,
        ⟨43971, true, false, [], [7]⟩,
        ⟨52711, true, false, [23310], [11, 7]⟩,
        ⟨52711, true, false, [23310], [11, 7]⟩,
        ⟨52686, true, false, [23310], [11, 7]⟩,
        ⟨52682, true, false, [23310], [11, 7]⟩,
        ⟨555, false, false, [23310, 88829], []⟩,
        ⟨54, false, false, [23310, 88829], []⟩,
        ⟨52546, false, false, [23310], []⟩,
        ⟨52625, false, false, [23310], []⟩,
        ⟨52551, false, false, [23310], []⟩,
        ⟨52551, false, false, [23310], []⟩,
        ⟨52643, false, false, [23310], []⟩,
        ⟨52713, true, false, [], [88831]⟩,
        ⟨52713, true, false, [], [88831]⟩,
        ⟨52687, true, false, [], [88831]⟩
      ]⟩,
    ⟨[23311], [23312], .contexts [
        ⟨52687, true, true, [], []⟩
      ]⟩,
    ⟨[88831, 7], [23311, 87557], .contexts [
        ⟨52714, true, false, [23312], [7]⟩,
        ⟨38, false, false, [23312, 87557], []⟩,
        ⟨52715, true, false, [], [87557]⟩
      ]⟩,
    ⟨[23301, 88827], [23301, 88827], .contexts []⟩,
    ⟨[23301, 88827], [23301, 88827], .contexts []⟩,
    ⟨[23301, 88823], [23301, 88823], .contexts []⟩,
    ⟨[86419], [86419], .contexts []⟩,
    ⟨[23299], [23299], .contexts []⟩,
    ⟨[23300], [23300], .contexts []⟩,
    ⟨[88823, 1], [23299, 86419], .contexts [
        ⟨52719, true, false, [23300], [1]⟩,
        ⟨52536, true, false, [], [1]⟩,
        ⟨52540, true, false, [], [5, 1]⟩,
        ⟨52718, true, false, [23300], [1, 5, 1]⟩,
        ⟨52718, true, false, [23300], [1, 5, 1]⟩,
        ⟨52717, true, false, [23300], [1, 5, 1]⟩,
        ⟨52703, true, false, [23300], [1, 5, 1]⟩,
        ⟨52702, true, false, [23300], [1, 5, 1]⟩,
        ⟨874, false, false, [23300, 86419], []⟩,
        ⟨52720, false, false, [23300], []⟩,
        ⟨52722, true, false, [], [86419]⟩,
        ⟨52722, true, false, [], [86419]⟩,
        ⟨52655, true, false, [], [86419]⟩,
        ⟨52721, true, false, [], [86419]⟩
      ]⟩,
    ⟨[86419, 1], [86417], .contexts [
        ⟨36846, false, false, [], []⟩,
        ⟨36847, false, false, [], []⟩,
        ⟨36813, false, false, [], []⟩,
        ⟨36813, false, false, [], []⟩
      ]⟩,
    ⟨[88823], [23299, 86417], .contexts [
        ⟨52650, false, false, [23300], [88823]⟩,
        ⟨52719, true, false, [23300], []⟩,
        ⟨52649, false, false, [23300], [88823]⟩,
        ⟨8, true, false, [23300, 23298, 88823], []⟩,
        ⟨52723, false, false, [23300, 23298], [1]⟩,
        ⟨52724, false, false, [23300], []⟩,
        ⟨52655, true, false, [], [86417]⟩
      ]⟩,
    ⟨[23301], [23298], .contexts [
        ⟨52651, false, false, [], []⟩,
        ⟨52652, false, false, [], []⟩,
        ⟨52652, false, false, [], []⟩
      ]⟩,
    ⟨[86417, 3], [23301, 88821], .contexts [
        ⟨52725, true, false, [23298], [3]⟩,
        ⟨52532, false, false, [23298], []⟩,
        ⟨52560, false, false, [23298], []⟩,
        ⟨52726, true, false, [], [88821]⟩
      ]⟩,
    ⟨[88823], [23299, 86417], .contexts [
        ⟨52725, false, false, [], []⟩
      ]⟩,
    ⟨[23299, 86415], [23299, 86415], .contexts []⟩,
    ⟨[88825], [23299, 86415], .contexts [
        ⟨52651, false, false, [23300], [88825]⟩,
        ⟨13, false, false, [23300, 23298], [88825]⟩,
        ⟨52559, true, false, [23300, 23298], []⟩,
        ⟨52534, true, false, [23300, 23298], []⟩,
        ⟨52728, false, false, [23300, 23298], [5]⟩,
        ⟨36810, false, false, [23300], []⟩,
        ⟨52729, false, false, [23300, 23298], []⟩,
        ⟨52655, true, false, [], [86415]⟩
      ]⟩,
    ⟨[86415, 1], [23301, 88827], .contexts [
        ⟨52730, true, false, [23298], [1]⟩,
        ⟨52538, false, false, [23298], []⟩,
        ⟨52557, false, false, [23298], []⟩,
        ⟨52726, true, false, [], [88827]⟩
      ]⟩,
    ⟨[88825], [23299, 86415], .contexts [
        ⟨52730, false, false, [], []⟩,
        ⟨52729, false, false, [], []⟩
      ]⟩,
    ⟨[23319, 88829], [23319, 88829], .contexts []⟩,
    ⟨[23319, 88827], [23319, 88827], .contexts []⟩,
    ⟨[23319, 88827], [23319, 88827], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 824. -/
def y322TCIndexRaw824 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88827, 15], [88827, 15], .contexts []⟩,
    ⟨[23318], [23318], .contexts []⟩,
    ⟨[88827, 15], [23317, 84983], .contexts [
        ⟨52736, false, false, [], []⟩,
        ⟨52735, true, false, [23318], [15]⟩,
        ⟨52734, true, false, [23318], [15]⟩,
        ⟨52544, true, false, [], [15]⟩,
        ⟨52733, true, false, [23318], [9, 15]⟩,
        ⟨52733, true, false, [23318], [9, 15]⟩,
        ⟨52709, true, false, [23318], [9, 15]⟩,
        ⟨52706, true, false, [23318], [9, 15]⟩,
        ⟨1671, false, false, [23318, 84981], []⟩,
        ⟨47, false, false, [23318, 84981], []⟩,
        ⟨29651, false, false, [23318], []⟩,
        ⟨29655, false, false, [23318], []⟩,
        ⟨52737, true, false, [], [84983]⟩,
        ⟨52737, true, false, [], [84983]⟩,
        ⟨52710, true, false, [], [84983]⟩
      ]⟩,
    ⟨[84983, 15], [23319, 88827], .contexts [
        ⟨52738, true, false, [23316], [15]⟩,
        ⟨1, false, false, [23316, 88827], []⟩,
        ⟨52707, true, false, [], [88827]⟩
      ]⟩,
    ⟨[23321], [19111, 23301], .source 11725⟩,
    ⟨[23301, 88821], [23301, 88821], .contexts []⟩,
    ⟨[86417, 3], [23301, 88821], .contexts [
        ⟨52727, false, false, [], []⟩,
        ⟨52741, false, false, [], []⟩,
        ⟨52741, false, false, [], []⟩
      ]⟩,
    ⟨[86417, 2], [86417, 3], .contexts [
        ⟨21, false, false, [86417], []⟩
      ]⟩,
    ⟨[88821, 9], [88821, 9], .contexts []⟩,
    ⟨[88821], [88821], .contexts []⟩,
    ⟨[23323], [23320], .source 11726⟩,
    ⟨[23325], [23323, 23301], .source 11727⟩,
    ⟨[88821, 9], [23325, 88821], .contexts [
        ⟨52744, false, false, [], []⟩,
        ⟨52740, false, false, [23320], [88821, 9]⟩,
        ⟨52727, true, false, [23320, 19111], [9]⟩,
        ⟨37008, true, false, [23320], [3, 9]⟩,
        ⟨479, false, false, [23320, 86417], []⟩,
        ⟨52743, false, false, [23320], []⟩,
        ⟨52742, false, false, [23320], []⟩,
        ⟨52745, false, false, [23320, 23301], []⟩,
        ⟨52746, true, false, [], [23301, 88821]⟩,
        ⟨52747, true, false, [], [88821]⟩
      ]⟩,
    ⟨[23327], [23301, 23293], .source 11728⟩,
    ⟨[23329], [23327, 23299], .source 11729⟩,
    ⟨[86411, 3], [23329, 86415], .contexts [
        ⟨36803, true, false, [], [3]⟩,
        ⟨36803, true, false, [], [3]⟩,
        ⟨36853, true, false, [], [3]⟩,
        ⟨36852, true, false, [], [3]⟩,
        ⟨37016, true, false, [], [1, 3]⟩,
        ⟨1634, false, false, [86415], []⟩,
        ⟨132, false, false, [86415], []⟩,
        ⟨52731, false, false, [], [3, 1]⟩,
        ⟨52717, false, false, [], [3, 1]⟩,
        ⟨52718, false, false, [], [3, 1]⟩,
        ⟨52718, false, false, [], [3, 1]⟩,
        ⟨52699, false, false, [23301], [1]⟩,
        ⟨52749, true, false, [], [88827, 1]⟩,
        ⟨52540, false, false, [23327], []⟩,
        ⟨52732, false, false, [23327], []⟩,
        ⟨52750, true, false, [], [86415]⟩,
        ⟨37010, false, false, [23329], []⟩,
        ⟨13, true, false, [], [23329, 86415]⟩
      ]⟩,
    ⟨[23331], [23328], .source 11730⟩,
    ⟨[23331], [23331], .contexts []⟩,
    ⟨[23331], [23331], .contexts []⟩,
    ⟨[23331], [23331], .contexts []⟩,
    ⟨[86413], [23331, 86411], .contexts [
        ⟨37016, true, false, [], []⟩,
        ⟨52751, true, false, [23328], [3]⟩,
        ⟨20, false, false, [23328, 86411], []⟩,
        ⟨52752, true, false, [], [86411]⟩,
        ⟨52755, true, false, [], [86411]⟩,
        ⟨52754, true, false, [], [86411]⟩,
        ⟨52753, true, false, [], [86411]⟩
      ]⟩,
    ⟨[86413], [23331, 86411], .contexts [
        ⟨52756, false, false, [], []⟩
      ]⟩,
    ⟨[23331, 86411], [23331, 86411], .contexts []⟩,
    ⟨[86413], [23331, 86411], .contexts [
        ⟨52757, false, false, [], []⟩,
        ⟨52758, false, false, [], []⟩
      ]⟩,
    ⟨[23329], [23330], .contexts [
        ⟨52752, true, true, [], []⟩
      ]⟩,
    ⟨[23333], [23329, 19111], .source 11731⟩,
    ⟨[23335], [23333, 23331], .source 11732⟩,
    ⟨[86411, 9], [23335, 86411], .contexts [
        ⟨52756, true, false, [23330], [9]⟩,
        ⟨36806, true, false, [23330], [9]⟩,
        ⟨37014, true, false, [23330, 19108], [3, 9]⟩,
        ⟨37014, true, false, [23330, 19108], [3, 9]⟩,
        ⟨37013, true, false, [23330, 19108], [3, 9]⟩,
        ⟨37012, true, false, [23330, 19108], [3, 9]⟩,
        ⟨37009, true, false, [23330, 19108], [3, 9]⟩,
        ⟨479, false, false, [23330, 19108, 86415], []⟩,
        ⟨37017, false, false, [23330, 19108], []⟩,
        ⟨37016, false, false, [23330, 19108], []⟩,
        ⟨37004, true, false, [23330], [86413]⟩,
        ⟨52759, false, false, [23330, 19111], []⟩,
        ⟨52760, true, false, [], [19111, 23331, 86411]⟩,
        ⟨52761, true, false, [], [23331, 86411]⟩,
        ⟨52762, true, false, [], [86411]⟩
      ]⟩,
    ⟨[86411, 15], [86409], .contexts [
        ⟨36854, false, false, [], []⟩,
        ⟨36855, false, false, [], []⟩,
        ⟨36799, false, false, [], []⟩,
        ⟨36799, false, false, [], []⟩
      ]⟩,
    ⟨[86413], [23331, 86411], .contexts [
        ⟨52759, false, false, [], []⟩
      ]⟩,
    ⟨[86411, 1], [23331, 86411], .contexts [
        ⟨36802, false, false, [], []⟩,
        ⟨52765, false, false, [], []⟩,
        ⟨52758, false, false, [], []⟩,
        ⟨52758, false, false, [], []⟩
      ]⟩,
    ⟨[23331, 86411, 15], [23331, 86409], .contexts [
        ⟨36800, false, false, [23331], []⟩
      ]⟩,
    ⟨[23331, 86409], [23331, 86409], .contexts []⟩,
    ⟨[23331, 86409], [23331, 86409], .contexts []⟩,
    ⟨[23331, 86409], [23331, 86409], .contexts []⟩,
    ⟨[86409, 1], [86409, 1], .contexts []⟩,
    ⟨[86409], [86409], .contexts []⟩,
    ⟨[86409, 1], [23331, 86409], .contexts [
        ⟨52771, false, false, [], []⟩,
        ⟨52764, true, false, [], [1]⟩,
        ⟨7, false, false, [86411], []⟩,
        ⟨11, false, false, [86411], []⟩,
        ⟨52766, false, false, [], [15]⟩,
        ⟨52767, false, false, [], []⟩,
        ⟨52768, false, false, [], []⟩,
        ⟨52769, false, false, [], []⟩,
        ⟨52770, false, false, [], []⟩,
        ⟨52772, false, false, [23331], []⟩,
        ⟨52755, true, false, [], [86409]⟩,
        ⟨52754, true, false, [], [86409]⟩,
        ⟨13, true, false, [], [23331, 86409]⟩
      ]⟩,
    ⟨[23335, 86411], [23335, 86411], .contexts []⟩,
    ⟨[23335, 86411], [23335, 86411], .contexts []⟩,
    ⟨[23335, 86409], [23335, 86409], .contexts []⟩,
    ⟨[23335, 86409], [23335, 86409], .contexts []⟩,
    ⟨[86409, 9], [86409, 9], .contexts []⟩,
    ⟨[86409, 9], [23335, 86409], .contexts [
        ⟨52778, false, false, [], []⟩,
        ⟨52764, true, false, [], [9]⟩,
        ⟨45, false, false, [86411], []⟩,
        ⟨48, false, false, [86411], []⟩,
        ⟨52763, false, false, [], [15]⟩,
        ⟨52774, false, false, [], [15]⟩,
        ⟨52775, false, false, [], [15]⟩,
        ⟨52775, false, false, [], [15]⟩,
        ⟨36800, false, false, [23335], []⟩,
        ⟨52776, false, false, [], []⟩,
        ⟨52777, false, false, [], []⟩,
        ⟨52772, false, false, [23335], []⟩,
        ⟨13, true, false, [], [23335, 86409]⟩
      ]⟩,
    ⟨[86409, 13], [86407], .contexts [
        ⟨36857, false, false, [], []⟩,
        ⟨36858, false, false, [], []⟩,
        ⟨36795, false, false, [], []⟩,
        ⟨36795, false, false, [], []⟩
      ]⟩,
    ⟨[86405, 13], [86405, 13], .contexts []⟩,
    ⟨[23330], [23330], .contexts []⟩,
    ⟨[23329], [23330], .contexts [
        ⟨52760, false, false, [], []⟩,
        ⟨52782, false, false, [], []⟩,
        ⟨52782, false, false, [], []⟩
      ]⟩,
    ⟨[86405, 13], [23329, 86405], .contexts [
        ⟨52781, false, false, [], []⟩,
        ⟨36792, true, false, [], [13]⟩,
        ⟨36796, true, false, [], [1, 13]⟩,
        ⟨52770, true, false, [23330], [13, 1, 13]⟩,
        ⟨52770, true, false, [23330], [13, 1, 13]⟩,
        ⟨52768, true, false, [23330], [13, 1, 13]⟩,
        ⟨52773, true, false, [23330], [13, 1, 13]⟩,
        ⟨52771, true, false, [23330], [13, 1, 13]⟩,
        ⟨919, false, false, [23330, 86409], []⟩,
        ⟨116, false, false, [23330, 86409], []⟩,
        ⟨52780, false, false, [23330], [1]⟩,
        ⟨36859, false, false, [23330], []⟩,
        ⟨36860, false, false, [23330], []⟩,
        ⟨36791, false, false, [23330], []⟩,
        ⟨36791, false, false, [23330], []⟩,
        ⟨52783, true, false, [], [86405]⟩
      ]⟩,
    ⟨[86407], [86407], .contexts []⟩,
    ⟨[23337], [23334], .source 11733⟩,
    ⟨[23334], [23334], .contexts []⟩,
    ⟨[23329, 86405], [23329, 86405], .contexts []⟩,
    ⟨[86403, 13], [86403, 13], .contexts []⟩,
    ⟨[86403], [86403], .contexts []⟩,
    ⟨[23328], [23328], .contexts []⟩,
    ⟨[86403, 13], [23331, 86403], .contexts [
        ⟨52789, false, false, [], []⟩,
        ⟨36788, true, false, [], [13]⟩,
        ⟨52788, true, false, [23328], [11, 13]⟩,
        ⟨52788, true, false, [23328], [11, 13]⟩,
        ⟨52784, true, false, [23328], [11, 13]⟩,
        ⟨52781, true, false, [23328], [11, 13]⟩,
        ⟨931, false, false, [23328, 86405], []⟩,
        ⟨54, false, false, [23328, 86405], []⟩,
        ⟨36861, false, false, [23328], []⟩,
        ⟨36862, false, false, [23328], []⟩,
        ⟨36787, false, false, [23328], []⟩,
        ⟨36787, false, false, [23328], []⟩,
        ⟨52790, false, false, [23328], []⟩,
        ⟨52791, true, false, [], [86403]⟩,
        ⟨52791, true, false, [], [86403]⟩,
        ⟨52752, true, false, [], [86403]⟩,
        ⟨52753, true, false, [], [86403]⟩
      ]⟩,
    ⟨[23331, 86403], [23331, 86403], .contexts []⟩,
    ⟨[88835], [83945, 5], .source 44482⟩,
    ⟨[83945, 5], [88835], .contexts [
        ⟨52794, true, false, [], []⟩
      ]⟩,
    ⟨[88835], [88835], .contexts []⟩,
    ⟨[88835], [88835], .contexts []⟩,
    ⟨[83945, 5], [88835], .contexts [
        ⟨52795, false, false, [], []⟩,
        ⟨52796, false, false, [], []⟩,
        ⟨52797, false, false, [], []⟩,
        ⟨52797, false, false, [], []⟩
      ]⟩,
    ⟨[12505, 88835], [12505, 88835], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 825. -/
def y322TCIndexRaw825 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[12505, 88835], [12505, 88835], .contexts []⟩,
    ⟨[88835, 1], [88835, 1], .contexts []⟩,
    ⟨[88835], [88835], .contexts []⟩,
    ⟨[88835, 1], [12505, 88835], .contexts [
        ⟨52801, false, false, [], []⟩,
        ⟨52798, true, false, [], [1]⟩,
        ⟨161, false, false, [83945], []⟩,
        ⟨162, false, false, [83945], []⟩,
        ⟨23986, false, false, [], [5]⟩,
        ⟨23989, false, false, [], [5]⟩,
        ⟨23984, false, false, [], [5]⟩,
        ⟨23985, false, false, [], [5]⟩,
        ⟨23985, false, false, [], [5]⟩,
        ⟨52795, false, false, [12505], []⟩,
        ⟨52799, false, false, [], []⟩,
        ⟨52800, false, false, [], []⟩,
        ⟨52802, false, false, [12505], []⟩,
        ⟨20688, true, false, [], [88835]⟩
      ]⟩,
    ⟨[16015, 87717], [16015, 87717], .contexts []⟩,
    ⟨[16015, 87717], [16015, 87717], .contexts []⟩,
    ⟨[88835, 3], [88835, 3], .contexts []⟩,
    ⟨[88835, 3], [16015, 87717], .contexts [
        ⟨52806, false, false, [], []⟩,
        ⟨52798, true, false, [], [3]⟩,
        ⟨166, false, false, [83945], []⟩,
        ⟨169, false, false, [83945], []⟩,
        ⟨23992, false, false, [], [5, 3, 5]⟩,
        ⟨23993, false, false, [], [5, 3, 5]⟩,
        ⟨23990, false, false, [], [5, 3, 5]⟩,
        ⟨23991, false, false, [], [5, 3, 5]⟩,
        ⟨23991, false, false, [], [5, 3, 5]⟩,
        ⟨26274, false, false, [16015], [3, 5]⟩,
        ⟨45820, false, false, [16015], [5]⟩,
        ⟨45842, false, false, [16015], []⟩,
        ⟨52804, false, false, [], []⟩,
        ⟨52805, false, false, [], []⟩,
        ⟨45850, false, false, [16015], []⟩
      ]⟩,
    ⟨[88835, 3], [16015, 87717], .contexts [
        ⟨52807, false, false, [], []⟩,
        ⟨19721, true, false, [], [87717]⟩
      ]⟩,
    ⟨[23339], [12491, 2427], .source 11734⟩,
    ⟨[23341], [23339, 12493], .source 11735⟩,
    ⟨[23341, 88835], [23341, 88835], .contexts []⟩,
    ⟨[23341, 88835], [23341, 88835], .contexts []⟩,
    ⟨[88835, 7], [88835, 7], .contexts []⟩,
    ⟨[88835, 7], [23341, 88835], .contexts [
        ⟨52813, false, false, [], []⟩,
        ⟨52798, true, false, [], [7]⟩,
        ⟨3272, false, false, [83945], []⟩,
        ⟨3275, false, false, [83945], []⟩,
        ⟨23996, false, false, [], [5, 7, 5]⟩,
        ⟨23997, false, false, [], [5, 7, 5]⟩,
        ⟨23994, false, false, [], [5, 7, 5]⟩,
        ⟨23995, false, false, [], [5, 7, 5]⟩,
        ⟨23995, false, false, [], [5, 7, 5]⟩,
        ⟨5347, false, false, [12491], [7, 5]⟩,
        ⟨52809, true, false, [], [78855, 7, 5]⟩,
        ⟨23998, false, false, [23339], [5]⟩,
        ⟨52810, true, false, [], [83945, 5]⟩,
        ⟨52795, false, false, [23341], []⟩,
        ⟨52811, false, false, [], []⟩,
        ⟨52812, false, false, [], []⟩,
        ⟨52802, false, false, [23341], []⟩
      ]⟩,
    ⟨[88835, 7], [23341, 88835], .contexts [
        ⟨52814, false, false, [], []⟩,
        ⟨13, true, false, [], [23341, 88835]⟩
      ]⟩,
    ⟨[88835, 9], [83943], .contexts [
        ⟨52798, true, false, [], [9]⟩,
        ⟨1265, false, false, [83945], []⟩,
        ⟨1266, false, false, [83945], []⟩,
        ⟨23979, false, false, [], [5]⟩,
        ⟨19714, false, false, [], [5]⟩,
        ⟨19715, false, false, [], [5]⟩,
        ⟨19715, false, false, [], [5]⟩,
        ⟨23964, false, false, [], []⟩,
        ⟨23965, false, false, [], []⟩,
        ⟨23966, false, false, [], []⟩,
        ⟨23966, false, false, [], []⟩,
        ⟨24020, false, false, [], []⟩,
        ⟨24021, false, false, [], []⟩
      ]⟩,
    ⟨[16719, 88835], [16719, 88835], .contexts []⟩,
    ⟨[12659, 88835], [12659, 88835], .contexts []⟩,
    ⟨[12501, 88835], [12501, 88835], .contexts []⟩,
    ⟨[23343], [12505, 16015], .source 11736⟩,
    ⟨[88835, 3], [16015, 87717], .contexts [
        ⟨52806, false, false, [], []⟩,
        ⟨52808, false, false, [], []⟩,
        ⟨52804, false, false, [], []⟩,
        ⟨52805, false, false, [], []⟩,
        ⟨52805, false, false, [], []⟩
      ]⟩,
    ⟨[87719, 3], [87719, 3], .contexts []⟩,
    ⟨[23345], [23342], .source 11737⟩,
    ⟨[23347], [23345, 16015], .source 11738⟩,
    ⟨[87719, 3], [23347, 87719], .contexts [
        ⟨52822, false, false, [], []⟩,
        ⟨45859, true, false, [], [3]⟩,
        ⟨52820, false, false, [23342], [87717, 1, 3]⟩,
        ⟨52808, true, false, [23342, 12505], [1, 3]⟩,
        ⟨52800, true, false, [23342], [3, 1, 3]⟩,
        ⟨52800, true, false, [23342], [3, 1, 3]⟩,
        ⟨52799, true, false, [23342], [3, 1, 3]⟩,
        ⟨52803, true, false, [23342], [3, 1, 3]⟩,
        ⟨52801, true, false, [23342], [3, 1, 3]⟩,
        ⟨484, false, false, [23342, 88835], []⟩,
        ⟨485, false, false, [23342, 88835], []⟩,
        ⟨52821, false, false, [23342], [1]⟩,
        ⟨45859, false, false, [23342, 16015], []⟩,
        ⟨45866, false, false, [23342, 16015], []⟩,
        ⟨52823, true, false, [], [16015, 87719]⟩,
        ⟨52824, true, false, [], [87719]⟩
      ]⟩,
    ⟨[23349], [23341, 16015], .source 11739⟩,
    ⟨[87717, 7], [87717, 7], .contexts []⟩,
    ⟨[23351], [16017, 23349], .source 11740⟩,
    ⟨[87717, 7], [23351, 87717], .contexts [
        ⟨52827, false, false, [], []⟩,
        ⟨52821, true, false, [16014], [7]⟩,
        ⟨140, false, false, [16014, 88835], []⟩,
        ⟨141, false, false, [16014, 88835], []⟩,
        ⟨52813, false, false, [16014], [3]⟩,
        ⟨52815, false, false, [16014], [3]⟩,
        ⟨52811, false, false, [16014], [3]⟩,
        ⟨52812, false, false, [16014], [3]⟩,
        ⟨52812, false, false, [16014], [3]⟩,
        ⟨52808, false, false, [16014, 23341], []⟩,
        ⟨52826, true, false, [16014], [87717]⟩,
        ⟨45850, false, false, [16014, 23349], []⟩,
        ⟨19723, true, false, [], [23349, 87717]⟩,
        ⟨52828, true, false, [], [87717]⟩
      ]⟩,
    ⟨[23347, 87719], [23347, 87719], .contexts []⟩,
    ⟨[23347, 87719], [23347, 87719], .contexts []⟩,
    ⟨[87719, 8], [87719, 9], .contexts [
        ⟨47, false, false, [87719], []⟩
      ]⟩,
    ⟨[87721, 3], [87721, 3], .contexts []⟩,
    ⟨[23353], [23346], .source 11741⟩,
    ⟨[23346], [23346], .contexts []⟩,
    ⟨[87721, 3], [23353, 87721], .contexts [
        ⟨52833, false, false, [], []⟩,
        ⟨45873, true, false, [], [3]⟩,
        ⟨52831, true, false, [23346], [9, 3]⟩,
        ⟨52831, true, false, [23346], [9, 3]⟩,
        ⟨52830, true, false, [23346], [9, 3]⟩,
        ⟨52825, true, false, [23346], [9, 3]⟩,
        ⟨52822, true, false, [23346], [9, 3]⟩,
        ⟨573, false, false, [23346, 87719], []⟩,
        ⟨52832, false, false, [23346], []⟩,
        ⟨45877, false, false, [23346], []⟩,
        ⟨45882, false, false, [23346], []⟩,
        ⟨52835, true, false, [], [87721]⟩,
        ⟨52835, true, false, [], [87721]⟩,
        ⟨52834, true, false, [], [87721]⟩
      ]⟩,
    ⟨[23351, 87717], [23351, 87717], .contexts []⟩,
    ⟨[23351, 87717], [23351, 87717], .contexts []⟩,
    ⟨[87719, 7], [87719, 7], .contexts []⟩,
    ⟨[23355], [23350], .source 11742⟩,
    ⟨[23350], [23350], .contexts []⟩,
    ⟨[23355], [23350], .contexts [
        ⟨52840, false, false, [], []⟩,
        ⟨52841, false, false, [], []⟩,
        ⟨52841, false, false, [], []⟩
      ]⟩,
    ⟨[87719, 7], [23355, 87719], .contexts [
        ⟨52839, false, false, [], []⟩,
        ⟨45859, true, false, [], [7]⟩,
        ⟨52838, true, false, [23350], [1, 7]⟩,
        ⟨52838, true, false, [23350], [1, 7]⟩,
        ⟨52837, true, false, [23350], [1, 7]⟩,
        ⟨52829, true, false, [23350], [1, 7]⟩,
        ⟨52827, true, false, [23350], [1, 7]⟩,
        ⟨502, false, false, [23350, 87717], []⟩,
        ⟨9, false, false, [23350, 87717], []⟩,
        ⟨45863, false, false, [23350], []⟩,
        ⟨45866, false, false, [23350], []⟩,
        ⟨52842, true, false, [], [87719]⟩
      ]⟩,
    ⟨[23353, 87721], [23353, 87721], .contexts []⟩,
    ⟨[23353, 87721], [23353, 87721], .contexts []⟩,
    ⟨[87721, 10], [87721, 11], .contexts [
        ⟨54, false, false, [87721], []⟩
      ]⟩,
    ⟨[87723, 3], [87723, 3], .contexts []⟩,
    ⟨[23352], [23352], .contexts []⟩,
    ⟨[87723, 3], [23347, 87723], .contexts [
        ⟨52847, false, false, [], []⟩,
        ⟨45885, true, false, [], [3]⟩,
        ⟨52845, true, false, [23352], [11, 3]⟩,
        ⟨52845, true, false, [23352], [11, 3]⟩,
        ⟨52844, true, false, [23352], [11, 3]⟩,
        ⟨52836, true, false, [23352], [11, 3]⟩,
        ⟨52833, true, false, [23352], [11, 3]⟩,
        ⟨545, false, false, [23352, 87721], []⟩,
        ⟨52846, false, false, [23352], []⟩,
        ⟨45889, false, false, [23352], []⟩,
        ⟨45894, false, false, [23352], []⟩,
        ⟨52848, true, false, [], [87723]⟩,
        ⟨52848, true, false, [], [87723]⟩,
        ⟨52834, false, true, [], [87723]⟩
      ]⟩,
    ⟨[23355, 87719], [23355, 87719], .contexts []⟩,
    ⟨[23355, 87719], [23355, 87719], .contexts []⟩,
    ⟨[87721, 7], [87721, 7], .contexts []⟩,
    ⟨[23354], [23354], .contexts []⟩,
    ⟨[23351], [23354], .contexts [
        ⟨52840, true, true, [], []⟩,
        ⟨52853, false, false, [], []⟩,
        ⟨52853, false, false, [], []⟩
      ]⟩,
    ⟨[87721, 7], [23351, 87721], .contexts [
        ⟨52852, false, false, [], []⟩,
        ⟨45873, true, false, [], [7]⟩,
        ⟨52851, true, false, [23354], [9, 7]⟩,
        ⟨52851, true, false, [23354], [9, 7]⟩,
        ⟨52850, true, false, [23354], [9, 7]⟩,
        ⟨52843, true, false, [23354], [9, 7]⟩,
        ⟨52839, true, false, [23354], [9, 7]⟩,
        ⟨579, false, false, [23354, 87719], []⟩,
        ⟨52832, false, false, [23354], []⟩,
        ⟨45877, false, false, [23354], []⟩,
        ⟨45882, false, false, [23354], []⟩,
        ⟨52854, true, false, [], [87721]⟩
      ]⟩,
    ⟨[23351, 87721], [23351, 87721], .contexts []⟩,
    ⟨[23351, 87721], [23351, 87721], .contexts []⟩,
    ⟨[87723, 7], [87723, 7], .contexts []⟩,
    ⟨[87723, 7], [23355, 87723], .contexts [
        ⟨52858, false, false, [], []⟩,
        ⟨45885, true, false, [], [7]⟩,
        ⟨52857, true, false, [23350], [11, 7]⟩,
        ⟨52857, true, false, [23350], [11, 7]⟩,
        ⟨52856, true, false, [23350], [11, 7]⟩,
        ⟨52855, true, false, [23350], [11, 7]⟩,
        ⟨52852, true, false, [23350], [11, 7]⟩,
        ⟨555, false, false, [23350, 87721], []⟩,
        ⟨52846, false, false, [23350], []⟩,
        ⟨45889, false, false, [23350], []⟩,
        ⟨45894, false, false, [23350], []⟩,
        ⟨52842, true, false, [], [87723]⟩
      ]⟩,
    ⟨[23355, 87723], [23355, 87723], .contexts []⟩,
    ⟨[23355, 87723], [23355, 87723], .contexts []⟩,
    ⟨[87723, 7], [23355, 87723], .contexts [
        ⟨52858, false, false, [], []⟩,
        ⟨52859, false, false, [], []⟩,
        ⟨52860, false, false, [], []⟩,
        ⟨52861, false, false, [], []⟩,
        ⟨52861, false, false, [], []⟩
      ]⟩,
    ⟨[87725, 7], [87725, 7], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 826. -/
def y322TCIndexRaw826 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[87725, 7], [23351, 87725], .contexts [
        ⟨52863, false, false, [], []⟩,
        ⟨45902, true, false, [], [7]⟩,
        ⟨52862, true, false, [23354], [1, 7]⟩,
        ⟨502, false, false, [23354, 87723], []⟩,
        ⟨9, false, false, [23354, 87723], []⟩,
        ⟨45906, false, false, [23354], []⟩,
        ⟨45910, false, false, [23354], []⟩,
        ⟨52854, true, false, [], [87725]⟩
      ]⟩,
    ⟨[23351, 87725], [23351, 87725], .contexts []⟩,
    ⟨[23351, 87725], [23351, 87725], .contexts []⟩,
    ⟨[87725, 13], [87727], .contexts [
        ⟨45913, false, false, [], []⟩
      ]⟩,
    ⟨[87727, 7], [87727, 7], .contexts []⟩,
    ⟨[23355, 87727], [23355, 87727], .contexts []⟩,
    ⟨[87727, 7], [23355, 87727], .contexts [
        ⟨52868, false, false, [], []⟩,
        ⟨52868, false, false, [], []⟩,
        ⟨45913, true, false, [], [7]⟩,
        ⟨52866, true, false, [23350], [13, 7]⟩,
        ⟨52866, true, false, [23350], [13, 7]⟩,
        ⟨52865, true, false, [23350], [13, 7]⟩,
        ⟨52864, true, false, [23350], [13, 7]⟩,
        ⟨52863, true, false, [23350], [13, 7]⟩,
        ⟨518, false, false, [23350, 87725], []⟩,
        ⟨64, false, false, [23350, 87725], []⟩,
        ⟨52867, false, false, [23350], []⟩,
        ⟨46117, false, false, [23350], []⟩,
        ⟨45917, false, false, [23350], []⟩,
        ⟨45917, false, false, [23350], []⟩,
        ⟨52842, true, false, [], [87727]⟩,
        ⟨52869, false, false, [], []⟩,
        ⟨52869, false, false, [], []⟩
      ]⟩,
    ⟨[87727, 14], [87727, 15], .contexts [
        ⟨10, false, false, [87727], []⟩
      ]⟩,
    ⟨[87729, 7], [87729, 7], .contexts []⟩,
    ⟨[87729, 7], [23351, 87729], .contexts [
        ⟨52872, false, false, [], []⟩,
        ⟨45916, true, false, [], [7]⟩,
        ⟨52870, true, false, [23354], [15, 7]⟩,
        ⟨18155, false, false, [23354, 87727], []⟩,
        ⟨52871, false, false, [23354], []⟩,
        ⟨45921, false, false, [23354], []⟩,
        ⟨45924, false, false, [23354], []⟩,
        ⟨52854, true, false, [], [87729]⟩
      ]⟩,
    ⟨[23351, 87729], [23351, 87729], .contexts []⟩,
    ⟨[23351, 87729], [23351, 87729], .contexts []⟩,
    ⟨[87731, 7], [87731, 7], .contexts []⟩,
    ⟨[87731], [87731], .contexts []⟩,
    ⟨[87731, 7], [23355, 87731], .contexts [
        ⟨52876, false, false, [], []⟩,
        ⟨45927, true, false, [], [7]⟩,
        ⟨52875, true, false, [23350], [1, 7]⟩,
        ⟨52875, true, false, [23350], [1, 7]⟩,
        ⟨52874, true, false, [23350], [1, 7]⟩,
        ⟨52873, true, false, [23350], [1, 7]⟩,
        ⟨52872, true, false, [23350], [1, 7]⟩,
        ⟨502, false, false, [23350, 87729], []⟩,
        ⟨9, false, false, [23350, 87729], []⟩,
        ⟨45927, false, false, [23350], []⟩,
        ⟨46114, false, false, [23350], []⟩,
        ⟨45931, false, false, [23350], []⟩,
        ⟨45931, false, false, [23350], []⟩,
        ⟨52877, false, false, [23350], []⟩,
        ⟨52842, true, false, [], [87731]⟩
      ]⟩,
    ⟨[23355, 87731], [23355, 87731], .contexts []⟩,
    ⟨[23355, 87731], [23355, 87731], .contexts []⟩,
    ⟨[87731, 7], [23355, 87731], .contexts [
        ⟨52876, false, false, [], []⟩,
        ⟨52878, false, false, [], []⟩,
        ⟨52879, false, false, [], []⟩,
        ⟨52880, false, false, [], []⟩,
        ⟨52880, false, false, [], []⟩
      ]⟩,
    ⟨[87731, 3], [87733], .contexts [
        ⟨45930, false, false, [], []⟩,
        ⟨46113, false, false, [], []⟩,
        ⟨45935, false, false, [], []⟩,
        ⟨45935, false, false, [], []⟩
      ]⟩,
    ⟨[87733], [87733], .contexts []⟩,
    ⟨[88837], [79915, 3], .source 44483⟩,
    ⟨[79915, 3], [88837], .contexts [
        ⟨52884, true, false, [], []⟩
      ]⟩,
    ⟨[88837, 3], [79915], .contexts [
        ⟨52885, true, false, [], [3]⟩,
        ⟨20, false, false, [79915], []⟩,
        ⟨7517, false, false, [], []⟩
      ]⟩,
    ⟨[88837], [88837], .contexts []⟩,
    ⟨[88837], [88837], .contexts []⟩,
    ⟨[79915, 3], [88837], .contexts [
        ⟨52885, false, false, [], []⟩,
        ⟨52887, false, false, [], []⟩,
        ⟨52888, false, false, [], []⟩,
        ⟨52888, false, false, [], []⟩
      ]⟩,
    ⟨[7829, 88837], [7829, 88837], .contexts []⟩,
    ⟨[7829, 88837], [7829, 88837], .contexts []⟩,
    ⟨[88837, 5], [88837, 5], .contexts []⟩,
    ⟨[88837], [88837], .contexts []⟩,
    ⟨[88837, 5], [7829, 88837], .contexts [
        ⟨52892, false, false, [], []⟩,
        ⟨52889, true, false, [], [5]⟩,
        ⟨871, false, false, [79915], []⟩,
        ⟨873, false, false, [79915], []⟩,
        ⟨7522, false, false, [], [3, 5, 3]⟩,
        ⟨7524, false, false, [], [3, 5, 3]⟩,
        ⟨7286, false, false, [], [3, 5, 3]⟩,
        ⟨7287, false, false, [], [3, 5, 3]⟩,
        ⟨7287, false, false, [], [3, 5, 3]⟩,
        ⟨7416, false, false, [], [5, 3]⟩,
        ⟨11239, false, false, [], [5, 3]⟩,
        ⟨11234, false, false, [], [5, 3]⟩,
        ⟨11234, false, false, [], [5, 3]⟩,
        ⟨7525, false, false, [7829], [3]⟩,
        ⟨52885, false, false, [7829], []⟩,
        ⟨52890, false, false, [], []⟩,
        ⟨52891, false, false, [], []⟩,
        ⟨52893, false, false, [7829], []⟩
      ]⟩,
    ⟨[7829], [7829], .contexts [
        ⟨13, false, false, [], [7829]⟩
      ]⟩,
    ⟨[88837, 5], [7829, 88837], .contexts [
        ⟨52894, false, false, [], []⟩,
        ⟨52895, true, false, [], [88837]⟩
      ]⟩,
    ⟨[88837, 7], [88837, 7], .contexts []⟩,
    ⟨[88837, 7], [84857], .contexts [
        ⟨52897, false, false, [], []⟩,
        ⟨52889, true, false, [], [7]⟩,
        ⟨140, false, false, [79915], []⟩,
        ⟨141, false, false, [79915], []⟩,
        ⟨31661, false, false, [], [3]⟩,
        ⟨7500, false, false, [], [3]⟩,
        ⟨7501, false, false, [], [3]⟩,
        ⟨7501, false, false, [], [3]⟩,
        ⟨29201, false, false, [], []⟩,
        ⟨29202, false, false, [], []⟩,
        ⟨29203, false, false, [], []⟩,
        ⟨29203, false, false, [], []⟩,
        ⟨29207, false, false, [], []⟩,
        ⟨672, true, false, [], [84857]⟩
      ]⟩,
    ⟨[84857, 7], [88837], .contexts [
        ⟨52898, true, false, [], [7]⟩,
        ⟨38, false, false, [88837], []⟩,
        ⟨52888, false, false, [], []⟩
      ]⟩,
    ⟨[23357], [8293, 17017], .source 11743⟩,
    ⟨[88837, 11], [88837, 11], .contexts []⟩,
    ⟨[23357], [23357], .contexts [
        ⟨13, false, false, [], [23357]⟩
      ]⟩,
    ⟨[88837, 11], [23357, 84345], .contexts [
        ⟨52901, false, false, [], []⟩,
        ⟨52889, true, false, [], [11]⟩,
        ⟨144, false, false, [79915], []⟩,
        ⟨145, false, false, [79915], []⟩,
        ⟨14835, false, false, [], [3]⟩,
        ⟨14836, false, false, [], [3]⟩,
        ⟨14833, false, false, [], [3]⟩,
        ⟨14834, false, false, [], [3]⟩,
        ⟨14834, false, false, [], [3]⟩,
        ⟨26022, false, false, [8293], []⟩,
        ⟨52900, true, false, [], [84345]⟩,
        ⟨26033, false, false, [23357], []⟩,
        ⟨52902, true, false, [], [84345]⟩
      ]⟩,
    ⟨[23359], [23356], .source 11744⟩,
    ⟨[84345, 11], [23359, 88837], .contexts [
        ⟨52903, true, false, [23356], [11]⟩,
        ⟨53, false, false, [23356, 88837], []⟩,
        ⟨52904, true, false, [], [88837]⟩
      ]⟩,
    ⟨[2021, 88837], [2021, 88837], .contexts []⟩,
    ⟨[2021, 88837], [2021, 88837], .contexts []⟩,
    ⟨[88837, 13], [88837, 13], .contexts []⟩,
    ⟨[88837, 13], [2021, 88837], .contexts [
        ⟨52908, false, false, [], []⟩,
        ⟨52889, true, false, [], [13]⟩,
        ⟨147, false, false, [79915], []⟩,
        ⟨148, false, false, [79915], []⟩,
        ⟨7529, false, false, [], [3]⟩,
        ⟨7531, false, false, [], [3]⟩,
        ⟨7527, false, false, [], [3]⟩,
        ⟨7528, false, false, [], [3]⟩,
        ⟨7528, false, false, [], [3]⟩,
        ⟨52885, false, false, [2021], []⟩,
        ⟨52906, false, false, [], []⟩,
        ⟨52907, false, false, [], []⟩,
        ⟨52893, false, false, [2021], []⟩,
        ⟨5692, true, false, [], [88837]⟩
      ]⟩,
    ⟨[8325, 84099], [8325, 84099], .contexts []⟩,
    ⟨[8325, 84099], [8325, 84099], .contexts []⟩,
    ⟨[88837, 15], [88837, 15], .contexts []⟩,
    ⟨[88837, 15], [8325, 84099], .contexts [
        ⟨52912, false, false, [], []⟩,
        ⟨52889, true, false, [], [15]⟩,
        ⟨151, false, false, [79915], []⟩,
        ⟨152, false, false, [79915], []⟩,
        ⟨14840, false, false, [], [3]⟩,
        ⟨14842, false, false, [], [3]⟩,
        ⟨14838, false, false, [], [3]⟩,
        ⟨14839, false, false, [], [3]⟩,
        ⟨14839, false, false, [], [3]⟩,
        ⟨24790, false, false, [8325], []⟩,
        ⟨52910, false, false, [], []⟩,
        ⟨52911, false, false, [], []⟩,
        ⟨24800, false, false, [8325], []⟩,
        ⟨14841, true, false, [], [84099]⟩
      ]⟩,
    ⟨[84099, 15], [15145, 88837], .contexts [
        ⟨52913, true, false, [8324], [15]⟩,
        ⟨1, false, false, [8324, 88837], []⟩,
        ⟨14843, true, false, [], [88837]⟩
      ]⟩,
    ⟨[88839], [88837, 1], .source 44484⟩,
    ⟨[88837, 1], [88839], .contexts [
        ⟨52915, true, false, [], []⟩
      ]⟩,
    ⟨[88839, 1], [88837], .contexts [
        ⟨52916, true, false, [], [1]⟩,
        ⟨8, false, false, [88837], []⟩,
        ⟨52888, false, false, [], []⟩
      ]⟩,
    ⟨[88837, 1], [88839], .contexts [
        ⟨52916, false, false, [], []⟩
      ]⟩,
    ⟨[88839], [88839], .contexts []⟩,
    ⟨[88839], [88839], .contexts []⟩,
    ⟨[88837, 1], [88839], .contexts [
        ⟨52918, false, false, [], []⟩,
        ⟨52919, false, false, [], []⟩,
        ⟨52920, false, false, [], []⟩,
        ⟨52920, false, false, [], []⟩
      ]⟩,
    ⟨[88837, 5], [7829, 88837], .contexts [
        ⟨52892, false, false, [], []⟩,
        ⟨52896, false, false, [], []⟩,
        ⟨52890, false, false, [], []⟩,
        ⟨52891, false, false, [], []⟩,
        ⟨52891, false, false, [], []⟩
      ]⟩,
    ⟨[7829, 88839], [7829, 88839], .contexts []⟩,
    ⟨[7829, 88839], [7829, 88839], .contexts []⟩,
    ⟨[88839, 5], [88839, 5], .contexts []⟩,
    ⟨[88839], [88839], .contexts []⟩,
    ⟨[88839, 5], [7829, 88839], .contexts [
        ⟨52925, false, false, [], []⟩,
        ⟨52921, true, false, [], [5]⟩,
        ⟨98, false, false, [88837], []⟩,
        ⟨99, false, false, [88837], []⟩,
        ⟨52922, false, false, [], [1]⟩,
        ⟨52916, false, false, [7829], []⟩,
        ⟨52923, false, false, [], []⟩,
        ⟨52924, false, false, [], []⟩,
        ⟨52926, false, false, [7829], []⟩,
        ⟨52895, true, false, [], [88839]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 827. -/
def y322TCIndexRaw827 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[23357, 84345], [23357, 84345], .contexts []⟩,
    ⟨[23357, 84345], [23357, 84345], .contexts []⟩,
    ⟨[88837, 11], [23357, 84345], .contexts [
        ⟨52901, false, false, [], []⟩,
        ⟨52903, false, false, [], []⟩,
        ⟨52928, false, false, [], []⟩,
        ⟨52929, false, false, [], []⟩,
        ⟨52929, false, false, [], []⟩
      ]⟩,
    ⟨[23357, 84343], [23357, 84343], .contexts []⟩,
    ⟨[88839, 11], [23357, 84343], .contexts [
        ⟨52921, true, false, [], [11]⟩,
        ⟨110, false, false, [88837], []⟩,
        ⟨111, false, false, [88837], []⟩,
        ⟨52930, false, false, [], [1]⟩,
        ⟨25911, false, false, [23357], []⟩,
        ⟨52931, false, false, [], []⟩,
        ⟨26052, false, false, [23357], []⟩,
        ⟨52902, true, false, [], [84343]⟩
      ]⟩,
    ⟨[84343, 11], [23359, 88839], .contexts [
        ⟨52932, true, false, [23356], [11]⟩,
        ⟨53, false, false, [23356, 88839], []⟩,
        ⟨52904, true, false, [], [88839]⟩
      ]⟩,
    ⟨[88837, 15], [8325, 84099], .contexts [
        ⟨52912, false, false, [], []⟩,
        ⟨52913, false, false, [], []⟩,
        ⟨52910, false, false, [], []⟩,
        ⟨52911, false, false, [], []⟩,
        ⟨52911, false, false, [], []⟩
      ]⟩,
    ⟨[8325, 84101], [8325, 84101], .contexts []⟩,
    ⟨[8325, 84101], [8325, 84101], .contexts []⟩,
    ⟨[88839, 15], [88839, 15], .contexts []⟩,
    ⟨[88839, 15], [8325, 84101], .contexts [
        ⟨52937, false, false, [], []⟩,
        ⟨52921, true, false, [], [15]⟩,
        ⟨121, false, false, [88837], []⟩,
        ⟨122, false, false, [88837], []⟩,
        ⟨52934, false, false, [], [1]⟩,
        ⟨24805, false, false, [8325], []⟩,
        ⟨52935, false, false, [], []⟩,
        ⟨52936, false, false, [], []⟩,
        ⟨24828, false, false, [8325], []⟩,
        ⟨14841, true, false, [], [84101]⟩
      ]⟩,
    ⟨[84101, 15], [15145, 88839], .contexts [
        ⟨52938, true, false, [8324], [15]⟩,
        ⟨1, false, false, [8324, 88839], []⟩,
        ⟨14843, true, false, [], [88839]⟩
      ]⟩,
    ⟨[88841], [88839, 9], .source 44485⟩,
    ⟨[88839, 9], [88841], .contexts [
        ⟨52940, true, false, [], []⟩
      ]⟩,
    ⟨[88841, 9], [88839], .contexts [
        ⟨52941, true, false, [], [9]⟩,
        ⟨46, false, false, [88839], []⟩,
        ⟨52920, false, false, [], []⟩
      ]⟩,
    ⟨[88841], [88841], .contexts []⟩,
    ⟨[88841], [88841], .contexts []⟩,
    ⟨[88839, 9], [88841], .contexts [
        ⟨52941, false, false, [], []⟩,
        ⟨52943, false, false, [], []⟩,
        ⟨52944, false, false, [], []⟩,
        ⟨52944, false, false, [], []⟩
      ]⟩,
    ⟨[7829, 88841], [7829, 88841], .contexts []⟩,
    ⟨[7829, 88841], [7829, 88841], .contexts []⟩,
    ⟨[88841, 5], [88841, 5], .contexts []⟩,
    ⟨[88841], [88841], .contexts []⟩,
    ⟨[88841, 5], [7829, 88841], .contexts [
        ⟨52948, false, false, [], []⟩,
        ⟨52945, true, false, [], [5]⟩,
        ⟨1079, false, false, [88839], []⟩,
        ⟨1080, false, false, [88839], []⟩,
        ⟨52925, false, false, [], [9]⟩,
        ⟨52927, false, false, [], [9]⟩,
        ⟨52923, false, false, [], [9]⟩,
        ⟨52924, false, false, [], [9]⟩,
        ⟨52924, false, false, [], [9]⟩,
        ⟨52941, false, false, [7829], []⟩,
        ⟨52946, false, false, [], []⟩,
        ⟨52947, false, false, [], []⟩,
        ⟨52949, false, false, [7829], []⟩,
        ⟨52895, true, false, [], [88841]⟩
      ]⟩,
    ⟨[88839, 15], [8325, 84101], .contexts [
        ⟨52937, false, false, [], []⟩,
        ⟨52938, false, false, [], []⟩,
        ⟨52935, false, false, [], []⟩,
        ⟨52936, false, false, [], []⟩,
        ⟨52936, false, false, [], []⟩
      ]⟩,
    ⟨[8325, 84103], [8325, 84103], .contexts []⟩,
    ⟨[8325, 84103], [8325, 84103], .contexts []⟩,
    ⟨[88841, 15], [88841, 15], .contexts []⟩,
    ⟨[88841, 15], [8325, 84103], .contexts [
        ⟨52954, false, false, [], []⟩,
        ⟨52945, true, false, [], [15]⟩,
        ⟨205, false, false, [88839], []⟩,
        ⟨206, false, false, [88839], []⟩,
        ⟨52951, false, false, [], [9]⟩,
        ⟨24831, false, false, [8325], []⟩,
        ⟨52952, false, false, [], []⟩,
        ⟨52953, false, false, [], []⟩,
        ⟨24850, false, false, [8325], []⟩,
        ⟨14841, true, false, [], [84103]⟩
      ]⟩,
    ⟨[84103, 15], [15145, 88841], .contexts [
        ⟨52955, true, false, [8324], [15]⟩,
        ⟨1, false, false, [8324, 88841], []⟩,
        ⟨14843, true, false, [], [88841]⟩
      ]⟩,
    ⟨[88843], [88841, 11], .source 44486⟩,
    ⟨[88841, 11], [88843], .contexts [
        ⟨52957, true, false, [], []⟩
      ]⟩,
    ⟨[88843, 11], [88841], .contexts [
        ⟨52958, true, false, [], [11]⟩,
        ⟨53, false, false, [88841], []⟩,
        ⟨52944, false, false, [], []⟩
      ]⟩,
    ⟨[88843], [88843], .contexts []⟩,
    ⟨[88843], [88843], .contexts []⟩,
    ⟨[88841, 11], [88843], .contexts [
        ⟨52958, false, false, [], []⟩,
        ⟨52960, false, false, [], []⟩,
        ⟨52961, false, false, [], []⟩,
        ⟨52961, false, false, [], []⟩
      ]⟩,
    ⟨[7829, 88843], [7829, 88843], .contexts []⟩,
    ⟨[7829, 88843], [7829, 88843], .contexts []⟩,
    ⟨[88843, 5], [88843, 5], .contexts []⟩,
    ⟨[88843], [88843], .contexts []⟩,
    ⟨[88843, 5], [7829, 88843], .contexts [
        ⟨52965, false, false, [], []⟩,
        ⟨52962, true, false, [], [5]⟩,
        ⟨642, false, false, [88841], []⟩,
        ⟨643, false, false, [88841], []⟩,
        ⟨52948, false, false, [], [11]⟩,
        ⟨52950, false, false, [], [11]⟩,
        ⟨52946, false, false, [], [11]⟩,
        ⟨52947, false, false, [], [11]⟩,
        ⟨52947, false, false, [], [11]⟩,
        ⟨52958, false, false, [7829], []⟩,
        ⟨52963, false, false, [], []⟩,
        ⟨52964, false, false, [], []⟩,
        ⟨52966, false, false, [7829], []⟩,
        ⟨52895, true, false, [], [88843]⟩
      ]⟩,
    ⟨[8325, 84105], [8325, 84105], .contexts []⟩,
    ⟨[8325, 84105], [8325, 84105], .contexts []⟩,
    ⟨[88843, 15], [88843, 15], .contexts []⟩,
    ⟨[88843, 15], [8325, 84105], .contexts [
        ⟨52970, false, false, [], []⟩,
        ⟨52962, true, false, [], [15]⟩,
        ⟨231, false, false, [88841], []⟩,
        ⟨232, false, false, [88841], []⟩,
        ⟨52954, false, false, [], [11]⟩,
        ⟨52955, false, false, [], [11]⟩,
        ⟨52952, false, false, [], [11]⟩,
        ⟨52953, false, false, [], [11]⟩,
        ⟨52953, false, false, [], [11]⟩,
        ⟨24853, false, false, [8325], []⟩,
        ⟨52968, false, false, [], []⟩,
        ⟨52969, false, false, [], []⟩,
        ⟨24871, false, false, [8325], []⟩,
        ⟨14841, true, false, [], [84105]⟩
      ]⟩,
    ⟨[88845], [88843, 1], .source 44487⟩,
    ⟨[88843, 1], [88845], .contexts [
        ⟨52972, true, false, [], []⟩
      ]⟩,
    ⟨[88845, 1], [88843], .contexts [
        ⟨52973, true, false, [], [1]⟩,
        ⟨8, false, false, [88843], []⟩,
        ⟨52961, false, false, [], []⟩
      ]⟩,
    ⟨[88845], [88845], .contexts []⟩,
    ⟨[88845], [88845], .contexts []⟩,
    ⟨[88843, 1], [88845], .contexts [
        ⟨52973, false, false, [], []⟩,
        ⟨52975, false, false, [], []⟩,
        ⟨52976, false, false, [], []⟩,
        ⟨52976, false, false, [], []⟩
      ]⟩,
    ⟨[7829, 88845], [7829, 88845], .contexts []⟩,
    ⟨[7829, 88845], [7829, 88845], .contexts []⟩,
    ⟨[88845, 5], [88845, 5], .contexts []⟩,
    ⟨[88845], [88845], .contexts []⟩,
    ⟨[88845, 5], [7829, 88845], .contexts [
        ⟨52980, false, false, [], []⟩,
        ⟨52977, true, false, [], [5]⟩,
        ⟨98, false, false, [88843], []⟩,
        ⟨99, false, false, [88843], []⟩,
        ⟨52965, false, false, [], [1]⟩,
        ⟨52967, false, false, [], [1]⟩,
        ⟨52963, false, false, [], [1]⟩,
        ⟨52964, false, false, [], [1]⟩,
        ⟨52964, false, false, [], [1]⟩,
        ⟨52973, false, false, [7829], []⟩,
        ⟨52978, false, false, [], []⟩,
        ⟨52979, false, false, [], []⟩,
        ⟨52981, false, false, [7829], []⟩,
        ⟨52895, true, false, [], [88845]⟩
      ]⟩,
    ⟨[88843, 15], [8325, 84105], .contexts [
        ⟨52970, false, false, [], []⟩,
        ⟨52971, false, false, [], []⟩,
        ⟨52968, false, false, [], []⟩,
        ⟨52969, false, false, [], []⟩,
        ⟨52969, false, false, [], []⟩
      ]⟩,
    ⟨[8325, 84107], [8325, 84107], .contexts []⟩,
    ⟨[8325, 84107], [8325, 84107], .contexts []⟩,
    ⟨[88845, 15], [88845, 15], .contexts []⟩,
    ⟨[88845, 15], [8325, 84107], .contexts [
        ⟨52986, false, false, [], []⟩,
        ⟨52977, true, false, [], [15]⟩,
        ⟨121, false, false, [88843], []⟩,
        ⟨122, false, false, [88843], []⟩,
        ⟨52983, false, false, [], [1]⟩,
        ⟨24874, false, false, [8325], []⟩,
        ⟨52984, false, false, [], []⟩,
        ⟨52985, false, false, [], []⟩,
        ⟨24887, false, false, [8325], []⟩,
        ⟨14841, true, false, [], [84107]⟩
      ]⟩,
    ⟨[84107, 15], [15145, 88845], .contexts [
        ⟨52987, true, false, [8324], [15]⟩,
        ⟨1, false, false, [8324, 88845], []⟩,
        ⟨14843, true, false, [], [88845]⟩
      ]⟩,
    ⟨[88845, 15], [8325, 84107], .contexts [
        ⟨52987, false, false, [], []⟩
      ]⟩,
    ⟨[88845, 15], [8325, 84107], .contexts [
        ⟨52986, false, false, [], []⟩,
        ⟨52989, false, false, [], []⟩,
        ⟨52984, false, false, [], []⟩,
        ⟨52985, false, false, [], []⟩,
        ⟨52985, false, false, [], []⟩
      ]⟩,
    ⟨[23361], [8325, 16873], .source 11745⟩]

/-- Exact literal claimed equations and contextual derivations, block 828. -/
def y322TCIndexRaw828 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[23363], [23361, 15145], .source 11746⟩,
    ⟨[88845], [88845], .contexts []⟩,
    ⟨[88845, 3], [88845, 3], .contexts []⟩,
    ⟨[23365], [23362], .source 11747⟩,
    ⟨[23362], [23362], .contexts []⟩,
    ⟨[88845, 3], [23365, 88845], .contexts [
        ⟨52994, false, false, [], []⟩,
        ⟨52992, false, false, [23362], [88845, 3]⟩,
        ⟨52988, true, false, [23362, 23361], [3]⟩,
        ⟨52991, false, false, [23362], [84107, 15, 3]⟩,
        ⟨24889, true, false, [23362, 8325], [15, 3]⟩,
        ⟨52990, true, false, [23362], [3, 15, 3]⟩,
        ⟨903, false, false, [23362, 88845], []⟩,
        ⟨52993, false, false, [23362], []⟩,
        ⟨52981, false, false, [23362], []⟩,
        ⟨52996, true, false, [], [88845]⟩,
        ⟨52996, true, false, [], [88845]⟩,
        ⟨52995, true, false, [], [88845]⟩
      ]⟩,
    ⟨[23367], [8325, 19129], .source 11748⟩,
    ⟨[23369], [23367, 15145], .source 11749⟩,
    ⟨[88845, 9], [88845, 9], .contexts []⟩,
    ⟨[23371], [23368], .source 11750⟩,
    ⟨[23368], [23368], .contexts []⟩,
    ⟨[88845, 9], [23371, 88845], .contexts [
        ⟨53000, false, false, [], []⟩,
        ⟨52999, false, false, [23368], [88845, 9]⟩,
        ⟨52988, true, false, [23368, 23367], [9]⟩,
        ⟨52998, false, false, [23368], [84107, 15, 9]⟩,
        ⟨37102, true, false, [23368, 8325], [15, 9]⟩,
        ⟨52990, true, false, [23368], [9, 15, 9]⟩,
        ⟨2656, false, false, [23368, 88845], []⟩,
        ⟨52993, false, false, [23368], []⟩,
        ⟨52981, false, false, [23368], []⟩,
        ⟨53002, true, false, [], [88845]⟩,
        ⟨53002, true, false, [], [88845]⟩,
        ⟨53001, true, false, [], [88845]⟩
      ]⟩,
    ⟨[88847], [88845, 13], .source 44488⟩,
    ⟨[88845, 13], [88847], .contexts [
        ⟨53004, true, false, [], []⟩
      ]⟩,
    ⟨[88847, 13], [88845], .contexts [
        ⟨53005, true, false, [], [13]⟩,
        ⟨59, false, false, [88845], []⟩,
        ⟨52976, false, false, [], []⟩
      ]⟩,
    ⟨[88847], [88847], .contexts []⟩,
    ⟨[88847], [88847], .contexts []⟩,
    ⟨[88845, 13], [88847], .contexts [
        ⟨53005, false, false, [], []⟩,
        ⟨53007, false, false, [], []⟩,
        ⟨53008, false, false, [], []⟩,
        ⟨53008, false, false, [], []⟩
      ]⟩,
    ⟨[23365, 88845], [23365, 88845], .contexts []⟩,
    ⟨[23365, 88845], [23365, 88845], .contexts []⟩,
    ⟨[23365, 88847], [23365, 88847], .contexts []⟩,
    ⟨[23365, 88847], [23365, 88847], .contexts []⟩,
    ⟨[23365, 88847], [23365, 88847], .contexts []⟩,
    ⟨[88847, 3], [88847, 3], .contexts []⟩,
    ⟨[88847], [88847], .contexts []⟩,
    ⟨[23365], [23365], .contexts [
        ⟨13, false, false, [], [23365]⟩
      ]⟩,
    ⟨[88847, 3], [23365, 88847], .contexts [
        ⟨53015, false, false, [], []⟩,
        ⟨53009, true, false, [], [3]⟩,
        ⟨63, false, false, [88845], []⟩,
        ⟨65, false, false, [88845], []⟩,
        ⟨52994, false, false, [], [13]⟩,
        ⟨52997, false, false, [], [13]⟩,
        ⟨53010, false, false, [], [13]⟩,
        ⟨53011, false, false, [], [13]⟩,
        ⟨53011, false, false, [], [13]⟩,
        ⟨53005, false, false, [23365], []⟩,
        ⟨53012, false, false, [], []⟩,
        ⟨53013, false, false, [], []⟩,
        ⟨53014, false, false, [], []⟩,
        ⟨53016, false, false, [23365], []⟩,
        ⟨53017, true, false, [], [88847]⟩
      ]⟩,
    ⟨[7829, 88847], [7829, 88847], .contexts []⟩,
    ⟨[7829, 88847], [7829, 88847], .contexts []⟩,
    ⟨[88847, 5], [88847, 5], .contexts []⟩,
    ⟨[88847, 5], [7829, 88847], .contexts [
        ⟨53021, false, false, [], []⟩,
        ⟨53009, true, false, [], [5]⟩,
        ⟨68, false, false, [88845], []⟩,
        ⟨69, false, false, [88845], []⟩,
        ⟨52980, false, false, [], [13]⟩,
        ⟨52982, false, false, [], [13]⟩,
        ⟨52978, false, false, [], [13]⟩,
        ⟨52979, false, false, [], [13]⟩,
        ⟨52979, false, false, [], [13]⟩,
        ⟨53005, false, false, [7829], []⟩,
        ⟨53019, false, false, [], []⟩,
        ⟨53020, false, false, [], []⟩,
        ⟨53016, false, false, [7829], []⟩,
        ⟨52895, true, false, [], [88847]⟩
      ]⟩,
    ⟨[23371, 88845], [23371, 88845], .contexts []⟩,
    ⟨[23371, 88845], [23371, 88845], .contexts []⟩,
    ⟨[23371, 88847], [23371, 88847], .contexts []⟩,
    ⟨[23371, 88847], [23371, 88847], .contexts []⟩,
    ⟨[88847, 9], [88847, 9], .contexts []⟩,
    ⟨[23371], [23371], .contexts [
        ⟨13, false, false, [], [23371]⟩
      ]⟩,
    ⟨[88847, 9], [23371, 88847], .contexts [
        ⟨53027, false, false, [], []⟩,
        ⟨53009, true, false, [], [9]⟩,
        ⟨77, false, false, [88845], []⟩,
        ⟨78, false, false, [88845], []⟩,
        ⟨53000, false, false, [], [13]⟩,
        ⟨53003, false, false, [], [13]⟩,
        ⟨53023, false, false, [], [13]⟩,
        ⟨53024, false, false, [], [13]⟩,
        ⟨53024, false, false, [], [13]⟩,
        ⟨53005, false, false, [23371], []⟩,
        ⟨53025, false, false, [], []⟩,
        ⟨53026, false, false, [], []⟩,
        ⟨53016, false, false, [23371], []⟩,
        ⟨53028, true, false, [], [88847]⟩
      ]⟩,
    ⟨[88849], [88847, 15], .source 44489⟩,
    ⟨[88847, 15], [88849], .contexts [
        ⟨53030, true, false, [], []⟩
      ]⟩,
    ⟨[88849, 15], [88847], .contexts [
        ⟨53031, true, false, [], [15]⟩,
        ⟨1, false, false, [88847], []⟩,
        ⟨53008, false, false, [], []⟩
      ]⟩,
    ⟨[88849], [88849], .contexts []⟩,
    ⟨[88849], [88849], .contexts []⟩,
    ⟨[88847, 15], [88849], .contexts [
        ⟨53031, false, false, [], []⟩,
        ⟨53033, false, false, [], []⟩,
        ⟨53034, false, false, [], []⟩,
        ⟨53034, false, false, [], []⟩
      ]⟩,
    ⟨[23365, 88849], [23365, 88849], .contexts []⟩,
    ⟨[23365, 88849], [23365, 88849], .contexts []⟩,
    ⟨[23365, 88849], [23365, 88849], .contexts []⟩,
    ⟨[88849], [88849], .contexts []⟩,
    ⟨[88849, 3], [23365, 88849], .contexts [
        ⟨53035, true, false, [], [3]⟩,
        ⟨19, false, false, [88847], []⟩,
        ⟨22, false, false, [88847], []⟩,
        ⟨53015, false, false, [], [15]⟩,
        ⟨53018, false, false, [], [15]⟩,
        ⟨53012, false, false, [], [15]⟩,
        ⟨53014, false, false, [], [15]⟩,
        ⟨53014, false, false, [], [15]⟩,
        ⟨53031, false, false, [23365], []⟩,
        ⟨53036, false, false, [], []⟩,
        ⟨53037, false, false, [], []⟩,
        ⟨53038, false, false, [], []⟩,
        ⟨53039, false, false, [23365], []⟩,
        ⟨53017, true, false, [], [88849]⟩
      ]⟩,
    ⟨[7829, 88849], [7829, 88849], .contexts []⟩,
    ⟨[7829, 88849], [7829, 88849], .contexts []⟩,
    ⟨[88849, 5], [88849, 5], .contexts []⟩,
    ⟨[88849, 5], [7829, 88849], .contexts [
        ⟨53043, false, false, [], []⟩,
        ⟨53035, true, false, [], [5]⟩,
        ⟨27, false, false, [88847], []⟩,
        ⟨30, false, false, [88847], []⟩,
        ⟨53021, false, false, [], [15]⟩,
        ⟨53022, false, false, [], [15]⟩,
        ⟨53019, false, false, [], [15]⟩,
        ⟨53020, false, false, [], [15]⟩,
        ⟨53020, false, false, [], [15]⟩,
        ⟨53031, false, false, [7829], []⟩,
        ⟨53041, false, false, [], []⟩,
        ⟨53042, false, false, [], []⟩,
        ⟨53039, false, false, [7829], []⟩,
        ⟨52895, true, false, [], [88849]⟩
      ]⟩,
    ⟨[23371, 88849], [23371, 88849], .contexts []⟩,
    ⟨[8325, 84111], [8325, 84111], .contexts []⟩,
    ⟨[88849, 13], [8325, 84111], .contexts [
        ⟨53035, true, false, [], [13]⟩,
        ⟨259, false, false, [88847], []⟩,
        ⟨262, false, false, [88847], []⟩,
        ⟨53006, false, false, [], [15, 13, 15]⟩,
        ⟨52975, false, false, [], [15, 13, 15]⟩,
        ⟨52976, false, false, [], [15, 13, 15]⟩,
        ⟨52976, false, false, [], [15, 13, 15]⟩,
        ⟨52989, false, false, [], [13, 15]⟩,
        ⟨52984, false, false, [], [13, 15]⟩,
        ⟨52985, false, false, [], [13, 15]⟩,
        ⟨52985, false, false, [], [13, 15]⟩,
        ⟨24896, false, false, [8325], [15]⟩,
        ⟨24913, false, false, [8325], []⟩,
        ⟨53046, false, false, [], []⟩,
        ⟨24922, false, false, [8325], []⟩
      ]⟩,
    ⟨[88849, 13], [8325, 84111], .contexts [
        ⟨53047, false, false, [], []⟩,
        ⟨14841, true, false, [], [84111]⟩
      ]⟩,
    ⟨[84111, 13], [15145, 88849], .contexts [
        ⟨53048, true, false, [8324], [13]⟩,
        ⟨59, false, false, [8324, 88849], []⟩,
        ⟨14843, true, false, [], [88849]⟩
      ]⟩,
    ⟨[88851], [88849, 1], .source 44490⟩,
    ⟨[88849, 1], [88851], .contexts [
        ⟨53050, true, false, [], []⟩
      ]⟩,
    ⟨[88851, 1], [88849], .contexts [
        ⟨53051, true, false, [], [1]⟩,
        ⟨8, false, false, [88849], []⟩,
        ⟨53034, false, false, [], []⟩
      ]⟩,
    ⟨[88851], [88851], .contexts []⟩,
    ⟨[88851], [88851], .contexts []⟩,
    ⟨[7829, 88851], [7829, 88851], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 829. -/
def y322TCIndexRaw829 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88853], [88851, 3], .source 44491⟩,
    ⟨[88851, 3], [88853], .contexts [
        ⟨53056, true, false, [], []⟩
      ]⟩,
    ⟨[88853], [88853], .contexts []⟩,
    ⟨[23365, 88851], [23365, 88851], .contexts []⟩,
    ⟨[23365, 88851], [23365, 88851], .contexts []⟩,
    ⟨[23365, 88851], [23365, 88851], .contexts []⟩,
    ⟨[23365, 88853], [23365, 88853], .contexts []⟩,
    ⟨[23365, 88853], [23365, 88853], .contexts []⟩,
    ⟨[23365, 88853], [23365, 88853], .contexts []⟩,
    ⟨[88853, 1], [88853, 1], .contexts []⟩,
    ⟨[88853, 1], [23365, 88853], .contexts [
        ⟨53065, false, false, [], []⟩,
        ⟨53058, true, false, [], [1]⟩,
        ⟨53058, true, false, [], [1]⟩,
        ⟨53057, true, false, [], [1]⟩,
        ⟨130, false, false, [88851], []⟩,
        ⟨133, false, false, [88851], []⟩,
        ⟨53052, false, false, [], [3, 1, 3]⟩,
        ⟨53033, false, false, [], [3, 1, 3]⟩,
        ⟨53034, false, false, [], [3, 1, 3]⟩,
        ⟨53034, false, false, [], [3, 1, 3]⟩,
        ⟨53040, false, false, [], [1, 3]⟩,
        ⟨53036, false, false, [], [1, 3]⟩,
        ⟨53038, false, false, [], [1, 3]⟩,
        ⟨53038, false, false, [], [1, 3]⟩,
        ⟨53051, false, false, [23365], [3]⟩,
        ⟨53059, false, false, [], [3]⟩,
        ⟨53060, false, false, [], [3]⟩,
        ⟨53061, false, false, [], [3]⟩,
        ⟨53057, false, false, [23365], []⟩,
        ⟨53062, false, false, [], []⟩,
        ⟨53063, false, false, [], []⟩,
        ⟨53064, false, false, [], []⟩
      ]⟩,
    ⟨[88855], [88853, 5], .source 44492⟩,
    ⟨[88853, 5], [88855], .contexts [
        ⟨53067, true, false, [], []⟩
      ]⟩,
    ⟨[88855], [88855], .contexts []⟩,
    ⟨[88855], [88855], .contexts []⟩,
    ⟨[23365, 88855], [23365, 88855], .contexts []⟩,
    ⟨[23365, 88855], [23365, 88855], .contexts []⟩,
    ⟨[88857], [88855, 9], .source 44493⟩,
    ⟨[88855, 9], [88857], .contexts [
        ⟨53073, true, false, [], []⟩
      ]⟩,
    ⟨[88857], [88857], .contexts []⟩,
    ⟨[88857], [88857], .contexts []⟩,
    ⟨[88859], [88857, 11], .source 44494⟩,
    ⟨[88857, 11], [88859], .contexts [
        ⟨53077, true, false, [], []⟩
      ]⟩,
    ⟨[88859], [88859], .contexts []⟩,
    ⟨[88859], [88859], .contexts []⟩,
    ⟨[88861], [88859, 1], .source 44495⟩,
    ⟨[88859, 1], [88861], .contexts [
        ⟨53081, true, false, [], []⟩
      ]⟩,
    ⟨[88863], [88861, 13], .source 44496⟩,
    ⟨[88861, 13], [88863], .contexts [
        ⟨53083, true, false, [], []⟩
      ]⟩,
    ⟨[88861], [88861], .contexts []⟩,
    ⟨[88865], [88863, 15], .source 44497⟩,
    ⟨[88863, 15], [88865], .contexts [
        ⟨53086, true, false, [], []⟩
      ]⟩,
    ⟨[88863], [88863], .contexts []⟩,
    ⟨[88867], [88865, 1], .source 44498⟩,
    ⟨[88865, 1], [88867], .contexts [
        ⟨53089, true, false, [], []⟩
      ]⟩,
    ⟨[88865], [88865], .contexts []⟩,
    ⟨[88869], [88867, 3], .source 44499⟩,
    ⟨[88867, 3], [88869], .contexts [
        ⟨53092, true, false, [], []⟩
      ]⟩,
    ⟨[88867], [88867], .contexts []⟩,
    ⟨[88871], [88869, 5], .source 44500⟩,
    ⟨[88869, 5], [88871], .contexts [
        ⟨53095, true, false, [], []⟩
      ]⟩,
    ⟨[88869], [88869], .contexts []⟩,
    ⟨[88873], [88871, 1], .source 44501⟩,
    ⟨[88871, 1], [88873], .contexts [
        ⟨53098, true, false, [], []⟩
      ]⟩,
    ⟨[88871], [88871], .contexts []⟩,
    ⟨[88875], [88873, 9], .source 44502⟩,
    ⟨[88873, 9], [88875], .contexts [
        ⟨53101, true, false, [], []⟩
      ]⟩,
    ⟨[88873], [88873], .contexts []⟩,
    ⟨[88877], [88875, 11], .source 44503⟩,
    ⟨[88875, 11], [88877], .contexts [
        ⟨53104, true, false, [], []⟩
      ]⟩,
    ⟨[88875], [88875], .contexts []⟩,
    ⟨[88879], [88877, 1], .source 44504⟩,
    ⟨[88877, 1], [88879], .contexts [
        ⟨53107, true, false, [], []⟩
      ]⟩,
    ⟨[88877], [88877], .contexts []⟩,
    ⟨[88881], [88879, 13], .source 44505⟩,
    ⟨[88879, 13], [88881], .contexts [
        ⟨53110, true, false, [], []⟩
      ]⟩,
    ⟨[88879], [88879], .contexts []⟩,
    ⟨[88883], [88881, 15], .source 44506⟩,
    ⟨[88881, 15], [88883], .contexts [
        ⟨53113, true, false, [], []⟩
      ]⟩,
    ⟨[88881], [88881], .contexts []⟩,
    ⟨[88885], [88883, 1], .source 44507⟩,
    ⟨[88883, 1], [88885], .contexts [
        ⟨53116, true, false, [], []⟩
      ]⟩,
    ⟨[88883], [88883], .contexts []⟩,
    ⟨[88887], [88885, 3], .source 44508⟩]

/-- Exact literal claimed equations and contextual derivations, block 830. -/
def y322TCIndexRaw830 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88885, 3], [88887], .contexts [
        ⟨53119, true, false, [], []⟩
      ]⟩,
    ⟨[88885], [88885], .contexts []⟩,
    ⟨[88889], [88887, 5], .source 44509⟩,
    ⟨[88887, 5], [88889], .contexts [
        ⟨53122, true, false, [], []⟩
      ]⟩,
    ⟨[88887], [88887], .contexts []⟩,
    ⟨[88891], [88889, 1], .source 44510⟩,
    ⟨[88889, 1], [88891], .contexts [
        ⟨53125, true, false, [], []⟩
      ]⟩,
    ⟨[88889], [88889], .contexts []⟩,
    ⟨[88893], [88891, 9], .source 44511⟩,
    ⟨[88891, 9], [88893], .contexts [
        ⟨53128, true, false, [], []⟩
      ]⟩,
    ⟨[88891], [88891], .contexts []⟩,
    ⟨[88895], [88893, 11], .source 44512⟩,
    ⟨[88893, 11], [88895], .contexts [
        ⟨53131, true, false, [], []⟩
      ]⟩,
    ⟨[88893], [88893], .contexts []⟩,
    ⟨[88897], [88895, 1], .source 44513⟩,
    ⟨[88895, 1], [88897], .contexts [
        ⟨53134, true, false, [], []⟩
      ]⟩,
    ⟨[88895], [88895], .contexts []⟩,
    ⟨[88899], [88897, 13], .source 44514⟩,
    ⟨[88897, 13], [88899], .contexts [
        ⟨53137, true, false, [], []⟩
      ]⟩,
    ⟨[88897], [88897], .contexts []⟩,
    ⟨[88901], [88899, 15], .source 44515⟩,
    ⟨[88899, 15], [88901], .contexts [
        ⟨53140, true, false, [], []⟩
      ]⟩,
    ⟨[88899], [88899], .contexts []⟩,
    ⟨[88903], [88901, 1], .source 44516⟩,
    ⟨[88901, 1], [88903], .contexts [
        ⟨53143, true, false, [], []⟩
      ]⟩,
    ⟨[88901], [88901], .contexts []⟩,
    ⟨[88905], [88903, 3], .source 44517⟩,
    ⟨[88903, 3], [88905], .contexts [
        ⟨53146, true, false, [], []⟩
      ]⟩,
    ⟨[88903], [88903], .contexts []⟩,
    ⟨[88907], [88905, 5], .source 44518⟩,
    ⟨[88905, 5], [88907], .contexts [
        ⟨53149, true, false, [], []⟩
      ]⟩,
    ⟨[88905], [88905], .contexts []⟩,
    ⟨[88909], [88907, 1], .source 44519⟩,
    ⟨[88907, 1], [88909], .contexts [
        ⟨53152, true, false, [], []⟩
      ]⟩,
    ⟨[88907], [88907], .contexts []⟩,
    ⟨[88911], [88909, 9], .source 44520⟩,
    ⟨[88909, 9], [88911], .contexts [
        ⟨53155, true, false, [], []⟩
      ]⟩,
    ⟨[88909], [88909], .contexts []⟩,
    ⟨[88913], [88911, 11], .source 44521⟩,
    ⟨[88911, 11], [88913], .contexts [
        ⟨53158, true, false, [], []⟩
      ]⟩,
    ⟨[88911], [88911], .contexts []⟩,
    ⟨[88915], [88913, 1], .source 44522⟩,
    ⟨[88913, 1], [88915], .contexts [
        ⟨53161, true, false, [], []⟩
      ]⟩,
    ⟨[88913], [88913], .contexts []⟩,
    ⟨[88917], [88915, 13], .source 44523⟩,
    ⟨[88915, 13], [88917], .contexts [
        ⟨53164, true, false, [], []⟩
      ]⟩,
    ⟨[88915], [88915], .contexts []⟩,
    ⟨[88919], [88917, 15], .source 44524⟩,
    ⟨[88917, 15], [88919], .contexts [
        ⟨53167, true, false, [], []⟩
      ]⟩,
    ⟨[88917], [88917], .contexts []⟩,
    ⟨[88919, 15], [88917], .contexts [
        ⟨53168, true, false, [], [15]⟩,
        ⟨1, false, false, [88917], []⟩,
        ⟨53169, false, false, [], []⟩
      ]⟩,
    ⟨[88921], [88919, 1], .source 44525⟩,
    ⟨[88919, 1], [88921], .contexts [
        ⟨53171, true, false, [], []⟩
      ]⟩,
    ⟨[88919], [88919], .contexts []⟩,
    ⟨[88921, 1], [88919], .contexts [
        ⟨53172, true, false, [], [1]⟩,
        ⟨8, false, false, [88919], []⟩,
        ⟨53173, false, false, [], []⟩
      ]⟩,
    ⟨[88923], [88921, 3], .source 44526⟩,
    ⟨[88921, 3], [88923], .contexts [
        ⟨53175, true, false, [], []⟩
      ]⟩,
    ⟨[88921], [88921], .contexts []⟩,
    ⟨[88923, 3], [88921], .contexts [
        ⟨53176, true, false, [], [3]⟩,
        ⟨20, false, false, [88921], []⟩,
        ⟨53177, false, false, [], []⟩
      ]⟩,
    ⟨[88925], [88923, 5], .source 44527⟩,
    ⟨[88923, 5], [88925], .contexts [
        ⟨53179, true, false, [], []⟩
      ]⟩,
    ⟨[88923], [88923], .contexts []⟩,
    ⟨[88927], [88925, 1], .source 44528⟩,
    ⟨[88925, 1], [88927], .contexts [
        ⟨53182, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 831. -/
def y322TCIndexRaw831 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[88925], [88925], .contexts []⟩,
    ⟨[88929], [88927, 9], .source 44529⟩,
    ⟨[88927, 9], [88929], .contexts [
        ⟨53185, true, false, [], []⟩
      ]⟩,
    ⟨[88927], [88927], .contexts []⟩,
    ⟨[88931], [88929, 11], .source 44530⟩,
    ⟨[88929, 11], [88931], .contexts [
        ⟨53188, true, false, [], []⟩
      ]⟩,
    ⟨[88929], [88929], .contexts []⟩,
    ⟨[88933], [88931, 1], .source 44531⟩,
    ⟨[88931, 1], [88933], .contexts [
        ⟨53191, true, false, [], []⟩
      ]⟩,
    ⟨[88931], [88931], .contexts []⟩,
    ⟨[88935], [88933, 13], .source 44532⟩,
    ⟨[88933, 13], [88935], .contexts [
        ⟨53194, true, false, [], []⟩
      ]⟩,
    ⟨[88933], [88933], .contexts []⟩,
    ⟨[88935, 13], [88933], .contexts [
        ⟨53195, true, false, [], [13]⟩,
        ⟨59, false, false, [88933], []⟩,
        ⟨53196, false, false, [], []⟩
      ]⟩,
    ⟨[88937], [88935, 15], .source 44533⟩,
    ⟨[88935, 15], [88937], .contexts [
        ⟨53198, true, false, [], []⟩
      ]⟩,
    ⟨[88935], [88935], .contexts []⟩,
    ⟨[88937, 15], [88935], .contexts [
        ⟨53199, true, false, [], [15]⟩,
        ⟨1, false, false, [88935], []⟩,
        ⟨53200, false, false, [], []⟩
      ]⟩,
    ⟨[88939], [88937, 1], .source 44534⟩,
    ⟨[88937], [88937], .contexts []⟩,
    ⟨[88939, 1], [88937], .contexts [
        ⟨53202, false, false, [], [1]⟩,
        ⟨8, false, false, [88937], []⟩,
        ⟨53203, false, false, [], []⟩
      ]⟩,
    ⟨[88941], [88939, 3], .source 44535⟩,
    ⟨[88939, 3], [88941], .contexts [
        ⟨53205, true, false, [], []⟩
      ]⟩,
    ⟨[88939], [88939], .contexts []⟩,
    ⟨[88941, 3], [88939], .contexts [
        ⟨53206, true, false, [], [3]⟩,
        ⟨20, false, false, [88939], []⟩,
        ⟨53207, false, false, [], []⟩
      ]⟩,
    ⟨[88943], [88941, 5], .source 44536⟩,
    ⟨[88941, 5], [88943], .contexts [
        ⟨53209, true, false, [], []⟩
      ]⟩,
    ⟨[88941], [88941], .contexts []⟩,
    ⟨[88943, 5], [88941], .contexts [
        ⟨53210, true, false, [], [5]⟩,
        ⟨28, false, false, [88941], []⟩,
        ⟨53211, false, false, [], []⟩
      ]⟩,
    ⟨[88945], [88943, 1], .source 44537⟩,
    ⟨[88943, 1], [88945], .contexts [
        ⟨53213, true, false, [], []⟩
      ]⟩,
    ⟨[88943], [88943], .contexts []⟩,
    ⟨[88945, 1], [88943], .contexts [
        ⟨53214, true, false, [], [1]⟩,
        ⟨8, false, false, [88943], []⟩,
        ⟨53215, false, false, [], []⟩
      ]⟩,
    ⟨[88947], [88945, 9], .source 44538⟩,
    ⟨[88945, 9], [88947], .contexts [
        ⟨53217, true, false, [], []⟩
      ]⟩,
    ⟨[88945], [88945], .contexts []⟩,
    ⟨[88947, 9], [88945], .contexts [
        ⟨53218, true, false, [], [9]⟩,
        ⟨46, false, false, [88945], []⟩,
        ⟨53219, false, false, [], []⟩
      ]⟩,
    ⟨[88949], [88947, 11], .source 44539⟩,
    ⟨[88947, 11], [88949], .contexts [
        ⟨53221, true, false, [], []⟩
      ]⟩,
    ⟨[88947], [88947], .contexts []⟩,
    ⟨[88949, 11], [88947], .contexts [
        ⟨53222, true, false, [], [11]⟩,
        ⟨53, false, false, [88947], []⟩,
        ⟨53223, false, false, [], []⟩
      ]⟩,
    ⟨[88951], [88949, 1], .source 44540⟩,
    ⟨[88949, 1], [88951], .contexts [
        ⟨53225, true, false, [], []⟩
      ]⟩,
    ⟨[88949], [88949], .contexts []⟩,
    ⟨[88951, 1], [88949], .contexts [
        ⟨53226, true, false, [], [1]⟩,
        ⟨8, false, false, [88949], []⟩,
        ⟨53227, false, false, [], []⟩
      ]⟩,
    ⟨[88953], [88951, 13], .source 44541⟩,
    ⟨[88951, 13], [88953], .contexts [
        ⟨53229, true, false, [], []⟩
      ]⟩,
    ⟨[88951], [88951], .contexts []⟩,
    ⟨[88953, 13], [88951], .contexts [
        ⟨53230, true, false, [], [13]⟩,
        ⟨59, false, false, [88951], []⟩,
        ⟨53231, false, false, [], []⟩
      ]⟩,
    ⟨[88955], [88953, 15], .source 44542⟩,
    ⟨[88953, 15], [88955], .contexts [
        ⟨53233, true, false, [], []⟩
      ]⟩,
    ⟨[88953], [88953], .contexts []⟩,
    ⟨[88955, 15], [88953], .contexts [
        ⟨53234, true, false, [], [15]⟩,
        ⟨1, false, false, [88953], []⟩,
        ⟨53235, false, false, [], []⟩
      ]⟩,
    ⟨[88957], [88955, 1], .source 44543⟩,
    ⟨[88955, 1], [88957], .contexts [
        ⟨53237, true, false, [], []⟩
      ]⟩,
    ⟨[88955], [88955], .contexts []⟩,
    ⟨[88957, 1], [88955], .contexts [
        ⟨53238, true, false, [], [1]⟩,
        ⟨8, false, false, [88955], []⟩,
        ⟨53239, false, false, [], []⟩
      ]⟩,
    ⟨[88959], [88957, 3], .source 44544⟩,
    ⟨[88957, 3], [88959], .contexts [
        ⟨53241, true, false, [], []⟩
      ]⟩,
    ⟨[88957], [88957], .contexts []⟩,
    ⟨[88959, 3], [88957], .contexts [
        ⟨53242, true, false, [], [3]⟩,
        ⟨20, false, false, [88957], []⟩,
        ⟨53243, false, false, [], []⟩
      ]⟩,
    ⟨[88961], [88959, 5], .source 44545⟩,
    ⟨[88959, 5], [88961], .contexts [
        ⟨53245, true, false, [], []⟩
      ]⟩,
    ⟨[88959], [88959], .contexts []⟩]

/-- Literal contextual derivation data in chronological chunk 12. -/
def y322TCIndexRawChunk12 (i : Fin 4096) : Y322RawContextCertificate :=
  if i.val < 2048 then
    if i.val < 1024 then
      if i.val < 512 then
        if i.val < 256 then
          if i.val < 128 then
            if i.val < 64 then
              y322TCIndexRaw768 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw769 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 192 then
              y322TCIndexRaw770 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw771 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 384 then
            if i.val < 320 then
              y322TCIndexRaw772 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw773 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 448 then
              y322TCIndexRaw774 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw775 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 768 then
          if i.val < 640 then
            if i.val < 576 then
              y322TCIndexRaw776 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw777 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 704 then
              y322TCIndexRaw778 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw779 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 896 then
            if i.val < 832 then
              y322TCIndexRaw780 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw781 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 960 then
              y322TCIndexRaw782 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw783 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 1536 then
        if i.val < 1280 then
          if i.val < 1152 then
            if i.val < 1088 then
              y322TCIndexRaw784 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw785 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1216 then
              y322TCIndexRaw786 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw787 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1408 then
            if i.val < 1344 then
              y322TCIndexRaw788 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw789 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1472 then
              y322TCIndexRaw790 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw791 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 1792 then
          if i.val < 1664 then
            if i.val < 1600 then
              y322TCIndexRaw792 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw793 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1728 then
              y322TCIndexRaw794 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw795 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1920 then
            if i.val < 1856 then
              y322TCIndexRaw796 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw797 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1984 then
              y322TCIndexRaw798 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw799 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  else
    if i.val < 3072 then
      if i.val < 2560 then
        if i.val < 2304 then
          if i.val < 2176 then
            if i.val < 2112 then
              y322TCIndexRaw800 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw801 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2240 then
              y322TCIndexRaw802 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw803 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2432 then
            if i.val < 2368 then
              y322TCIndexRaw804 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw805 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2496 then
              y322TCIndexRaw806 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw807 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 2816 then
          if i.val < 2688 then
            if i.val < 2624 then
              y322TCIndexRaw808 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw809 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2752 then
              y322TCIndexRaw810 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw811 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2944 then
            if i.val < 2880 then
              y322TCIndexRaw812 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw813 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3008 then
              y322TCIndexRaw814 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw815 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 3584 then
        if i.val < 3328 then
          if i.val < 3200 then
            if i.val < 3136 then
              y322TCIndexRaw816 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw817 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3264 then
              y322TCIndexRaw818 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw819 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3456 then
            if i.val < 3392 then
              y322TCIndexRaw820 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw821 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3520 then
              y322TCIndexRaw822 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw823 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 3840 then
          if i.val < 3712 then
            if i.val < 3648 then
              y322TCIndexRaw824 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw825 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3776 then
              y322TCIndexRaw826 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw827 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3968 then
            if i.val < 3904 then
              y322TCIndexRaw828 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw829 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 4032 then
              y322TCIndexRaw830 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw831 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
