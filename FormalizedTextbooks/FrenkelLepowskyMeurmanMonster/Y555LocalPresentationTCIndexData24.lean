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

/-- Exact literal claimed equations and contextual derivations, block 1536. -/
def y322TCIndexRaw1536 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[20673, 85869], [20673, 85869], .contexts []⟩,
    ⟨[96549, 11], [96549, 11], .contexts []⟩,
    ⟨[96549, 11], [20673, 85869], .contexts [
        ⟨98305, false, false, [], []⟩,
        ⟨98292, true, false, [], [11]⟩,
        ⟨82, false, false, [83005], []⟩,
        ⟨83, false, false, [83005], []⟩,
        ⟨98302, false, false, [], [13]⟩,
        ⟨34100, false, false, [20673], []⟩,
        ⟨98303, false, false, [], []⟩,
        ⟨98304, false, false, [], []⟩,
        ⟨47246, false, false, [20673], []⟩,
        ⟨43003, true, false, [], [85869]⟩
      ]⟩,
    ⟨[85869, 11], [20825, 96549], .contexts [
        ⟨98306, true, false, [20672], [11]⟩,
        ⟨53, false, false, [20672, 96549], []⟩,
        ⟨42777, true, false, [], [96549]⟩
      ]⟩,
    ⟨[35819], [20677, 20683], .source 17974⟩,
    ⟨[94057], [30889, 94055], .contexts [
        ⟨82501, true, false, [30882], []⟩,
        ⟨82501, true, false, [30882], []⟩,
        ⟨82493, true, false, [30882], []⟩,
        ⟨82499, true, false, [30882, 30884], [13]⟩,
        ⟨59, false, false, [30882, 30884, 94055], []⟩,
        ⟨82500, true, false, [30882], [94055]⟩,
        ⟨82492, false, true, [], [30887, 94055]⟩,
        ⟨82502, true, false, [], [94055]⟩
      ]⟩,
    ⟨[94057], [30889, 94055], .contexts [
        ⟨98309, false, false, [], []⟩
      ]⟩,
    ⟨[35821], [30883, 30889], .source 17975⟩,
    ⟨[35823], [35819, 35821], .source 17976⟩,
    ⟨[96549, 15], [35823, 94055], .contexts [
        ⟨98292, true, false, [], [15]⟩,
        ⟨88, false, false, [83005], []⟩,
        ⟨91, false, false, [83005], []⟩,
        ⟨42790, false, false, [], [13, 15, 13]⟩,
        ⟨42481, false, false, [20677], [15, 13]⟩,
        ⟨98308, true, false, [], [87035, 15, 13]⟩,
        ⟨40045, false, false, [35819], [13]⟩,
        ⟨82493, false, false, [35819], []⟩,
        ⟨98310, false, false, [35819, 30883], []⟩,
        ⟨98311, true, false, [35819], [94055]⟩,
        ⟨98312, true, false, [], [94055]⟩,
        ⟨82507, false, false, [35823], []⟩,
        ⟨13, true, false, [], [35823, 94055]⟩
      ]⟩,
    ⟨[35825], [35822], .source 17977⟩,
    ⟨[94055, 15], [35825, 96549], .contexts [
        ⟨98313, true, false, [35822], [15]⟩,
        ⟨1, false, false, [35822, 96549], []⟩,
        ⟨98314, true, false, [], [96549]⟩
      ]⟩,
    ⟨[96551], [86211, 11], .source 48340⟩,
    ⟨[86211, 11], [96551], .contexts [
        ⟨98316, true, false, [], []⟩
      ]⟩,
    ⟨[96551, 11], [86211], .contexts [
        ⟨98317, true, false, [], [11]⟩,
        ⟨53, false, false, [86211], []⟩,
        ⟨35679, false, false, [], []⟩
      ]⟩,
    ⟨[86211, 11], [96551], .contexts [
        ⟨98317, false, false, [], []⟩
      ]⟩,
    ⟨[96551], [96551], .contexts []⟩,
    ⟨[96551], [96551], .contexts []⟩,
    ⟨[86211, 11], [96551], .contexts [
        ⟨98319, false, false, [], []⟩,
        ⟨98320, false, false, [], []⟩,
        ⟨98321, false, false, [], []⟩,
        ⟨98321, false, false, [], []⟩
      ]⟩,
    ⟨[18941, 85939], [18941, 27079, 85879], .contexts [
        ⟨69280, false, false, [18941], []⟩
      ]⟩,
    ⟨[35827], [18941, 27079], .source 17978⟩,
    ⟨[35827, 85879], [35827, 85879], .contexts []⟩,
    ⟨[35827, 85883], [35827, 85883], .contexts []⟩,
    ⟨[96551, 9], [35827, 85883], .contexts [
        ⟨98322, true, false, [], [9]⟩,
        ⟨221, false, false, [86211], []⟩,
        ⟨224, false, false, [86211], []⟩,
        ⟨35678, false, false, [], [11, 9, 11]⟩,
        ⟨35706, false, false, [], [11, 9, 11]⟩,
        ⟨35683, false, false, [], [11, 9, 11]⟩,
        ⟨35683, false, false, [], [11, 9, 11]⟩,
        ⟨35682, false, false, [], [9, 11]⟩,
        ⟨57794, false, false, [], [9, 11]⟩,
        ⟨98323, false, false, [], [9, 11]⟩,
        ⟨98324, true, false, [], [85879, 9, 11]⟩,
        ⟨98325, false, false, [], [9, 11]⟩,
        ⟨98325, false, false, [], [9, 11]⟩,
        ⟨34123, false, false, [35827], [11]⟩,
        ⟨34127, false, false, [35827], []⟩,
        ⟨98326, false, false, [], []⟩,
        ⟨69359, false, false, [35827], []⟩
      ]⟩,
    ⟨[96551, 9], [35827, 85883], .contexts [
        ⟨98327, false, false, [], []⟩,
        ⟨13, true, false, [], [35827, 85883]⟩
      ]⟩,
    ⟨[35829], [35826], .source 17979⟩,
    ⟨[19895, 90227], [19895, 90227], .contexts []⟩,
    ⟨[19895, 90227], [19895, 90227], .contexts []⟩,
    ⟨[19895], [19895], .contexts [
        ⟨13, false, false, [], [19895]⟩
      ]⟩,
    ⟨[96551, 13], [19895, 90227], .contexts [
        ⟨98322, true, false, [], [13]⟩,
        ⟨227, false, false, [86211], []⟩,
        ⟨228, false, false, [86211], []⟩,
        ⟨40481, false, false, [], [11]⟩,
        ⟨40472, false, false, [], [11]⟩,
        ⟨40473, false, false, [], [11]⟩,
        ⟨40473, false, false, [], [11]⟩,
        ⟨59733, false, false, [19895], []⟩,
        ⟨98330, false, false, [], []⟩,
        ⟨98331, false, false, [], []⟩,
        ⟨59749, false, false, [19895], []⟩,
        ⟨98332, true, false, [], [90227]⟩
      ]⟩,
    ⟨[90227, 13], [19897, 96551], .contexts [
        ⟨98333, true, false, [19894], [13]⟩,
        ⟨59, false, false, [19894, 96551], []⟩,
        ⟨40423, true, false, [], [96551]⟩
      ]⟩,
    ⟨[96553], [96551, 1], .source 48341⟩,
    ⟨[96551, 1], [96553], .contexts [
        ⟨98335, true, false, [], []⟩
      ]⟩,
    ⟨[96553, 1], [96551], .contexts [
        ⟨98336, true, false, [], [1]⟩,
        ⟨8, false, false, [96551], []⟩,
        ⟨98321, false, false, [], []⟩
      ]⟩,
    ⟨[96553], [96553], .contexts []⟩,
    ⟨[96553], [96553], .contexts []⟩,
    ⟨[96553, 11], [96553, 11], .contexts []⟩,
    ⟨[96553, 11], [86209], .contexts [
        ⟨98340, false, false, [], []⟩,
        ⟨98339, true, false, [], [11]⟩,
        ⟨98339, true, false, [], [11]⟩,
        ⟨98338, true, false, [], [11]⟩,
        ⟨98336, true, false, [], [11]⟩,
        ⟨110, false, false, [96551], []⟩,
        ⟨111, false, false, [96551], []⟩,
        ⟨98318, false, false, [], [1]⟩,
        ⟨35708, false, false, [], [1]⟩,
        ⟨35679, false, false, [], [1]⟩,
        ⟨35679, false, false, [], [1]⟩,
        ⟨35709, false, false, [], []⟩,
        ⟨35710, false, false, [], []⟩,
        ⟨35675, false, false, [], []⟩,
        ⟨35675, false, false, [], []⟩,
        ⟨61735, false, false, [], []⟩,
        ⟨672, true, false, [], [86209]⟩
      ]⟩,
    ⟨[86209, 11], [96553], .contexts [
        ⟨98341, true, false, [], [11]⟩,
        ⟨53, false, false, [96553], []⟩,
        ⟨98339, false, false, [], []⟩
      ]⟩,
    ⟨[96555], [96553, 13], .source 48342⟩,
    ⟨[96553, 13], [96555], .contexts [
        ⟨98343, true, false, [], []⟩
      ]⟩,
    ⟨[96555], [96555], .contexts []⟩,
    ⟨[96555], [96555], .contexts []⟩,
    ⟨[96553, 13], [96555], .contexts [
        ⟨98344, false, false, [], []⟩,
        ⟨98345, false, false, [], []⟩,
        ⟨98346, false, false, [], []⟩,
        ⟨98346, false, false, [], []⟩
      ]⟩,
    ⟨[19895, 90231], [19895, 90231], .contexts []⟩,
    ⟨[19895, 90231], [19895, 90231], .contexts []⟩,
    ⟨[96555, 1], [96555, 1], .contexts []⟩,
    ⟨[96555, 1], [19895, 90231], .contexts [
        ⟨98350, false, false, [], []⟩,
        ⟨98347, true, false, [], [1]⟩,
        ⟨246, false, false, [96553], []⟩,
        ⟨249, false, false, [96553], []⟩,
        ⟨98337, false, false, [], [13, 1, 13]⟩,
        ⟨98320, false, false, [], [13, 1, 13]⟩,
        ⟨98321, false, false, [], [13, 1, 13]⟩,
        ⟨98321, false, false, [], [13, 1, 13]⟩,
        ⟨98333, false, false, [], [1, 13]⟩,
        ⟨98330, false, false, [], [1, 13]⟩,
        ⟨98331, false, false, [], [1, 13]⟩,
        ⟨98331, false, false, [], [1, 13]⟩,
        ⟨59753, false, false, [19895], [13]⟩,
        ⟨59766, false, false, [19895], []⟩,
        ⟨98348, false, false, [], []⟩,
        ⟨98349, false, false, [], []⟩,
        ⟨66979, false, false, [19895], []⟩
      ]⟩,
    ⟨[96555, 1], [19895, 90231], .contexts [
        ⟨98351, false, false, [], []⟩,
        ⟨98332, true, false, [], [90231]⟩
      ]⟩,
    ⟨[90231, 1], [19897, 96555], .contexts [
        ⟨98352, true, false, [19894], [1]⟩,
        ⟨8, false, false, [19894, 96555], []⟩,
        ⟨40423, true, false, [], [96555]⟩
      ]⟩,
    ⟨[96555, 11], [96555, 11], .contexts []⟩,
    ⟨[25265], [25265], .contexts []⟩,
    ⟨[25265], [25265], .contexts []⟩,
    ⟨[96555, 11], [25265, 90597], .contexts [
        ⟨98354, false, false, [], []⟩,
        ⟨98347, true, false, [], [11]⟩,
        ⟨82, false, false, [96553], []⟩,
        ⟨83, false, false, [96553], []⟩,
        ⟨98340, false, false, [], [13]⟩,
        ⟨98341, false, false, [], [13]⟩,
        ⟨35710, false, false, [], [13]⟩,
        ⟨35675, false, false, [], [13]⟩,
        ⟨35675, false, false, [], [13]⟩,
        ⟨61738, false, false, [], []⟩,
        ⟨61732, false, false, [], []⟩,
        ⟨61733, false, false, [], []⟩,
        ⟨61733, false, false, [], []⟩,
        ⟨61746, false, false, [25265], []⟩,
        ⟨98356, true, false, [], [90597]⟩,
        ⟨98355, true, false, [], [90597]⟩,
        ⟨13, true, false, [], [25265, 90597]⟩
      ]⟩,
    ⟨[96555, 1], [19895, 90231], .contexts [
        ⟨98350, false, false, [], []⟩,
        ⟨98352, false, false, [], []⟩,
        ⟨98348, false, false, [], []⟩,
        ⟨98349, false, false, [], []⟩,
        ⟨98349, false, false, [], []⟩
      ]⟩,
    ⟨[35831], [19895, 32755], .source 17980⟩,
    ⟨[35833], [35831, 35479], .source 17981⟩,
    ⟨[35833, 96345], [35833, 96345], .contexts []⟩,
    ⟨[35833, 96345], [35833, 96345], .contexts []⟩,
    ⟨[96555], [96555], .contexts []⟩,
    ⟨[35833, 96345, 9], [96555], .contexts [
        ⟨98362, true, false, [], [9]⟩,
        ⟨98361, true, false, [], [9]⟩,
        ⟨97188, true, false, [35833], [9]⟩,
        ⟨97191, true, false, [35833], [1, 9]⟩,
        ⟨98360, false, false, [], [96349, 9, 1, 9]⟩,
        ⟨97385, false, false, [35831], [96349, 9, 1, 9]⟩,
        ⟨8, true, false, [35831, 35476, 96349], [9, 1, 9]⟩,
        ⟨97384, false, false, [35831, 35476], [1, 9, 1, 9]⟩,
        ⟨98359, false, false, [], [95525, 1, 9, 1, 9]⟩,
        ⟨92562, true, false, [19895], [1, 9, 1, 9]⟩,
        ⟨98358, true, false, [], [9, 1, 9, 1, 9]⟩,
        ⟨4283, false, false, [96555], []⟩,
        ⟨98363, false, false, [], []⟩
      ]⟩,
    ⟨[96555], [96555], .contexts []⟩,
    ⟨[35835], [35832], .source 17982⟩,
    ⟨[35832], [35832], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1537. -/
def y322TCIndexRaw1537 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[96345, 9], [35835, 96555], .contexts [
        ⟨98364, false, false, [35832], []⟩,
        ⟨98365, false, false, [35832], []⟩,
        ⟨98367, true, false, [], [96555]⟩,
        ⟨98367, true, false, [], [96555]⟩,
        ⟨98366, true, false, [], [96555]⟩
      ]⟩,
    ⟨[96555, 9], [35833, 96345], .contexts [
        ⟨98368, true, false, [35834], [9]⟩,
        ⟨46, false, false, [35834, 96345], []⟩,
        ⟨98366, false, true, [], [96345]⟩
      ]⟩,
    ⟨[19895, 90235], [19895, 90235], .contexts []⟩,
    ⟨[90235, 15], [19897, 96555], .contexts [
        ⟨98370, true, false, [19894], [15]⟩,
        ⟨59782, true, false, [], [15]⟩,
        ⟨59769, true, false, [], [1, 15]⟩,
        ⟨98358, true, false, [19894], [15, 1, 15]⟩,
        ⟨2185, false, false, [19894, 96555], []⟩,
        ⟨98363, false, false, [19894], []⟩,
        ⟨98365, false, false, [19894], []⟩,
        ⟨40478, true, false, [], [96555]⟩
      ]⟩,
    ⟨[35837], [25265, 25267], .source 17983⟩,
    ⟨[35837, 85197, 11], [35833, 96345], .contexts [
        ⟨30429, true, false, [35837], [11]⟩,
        ⟨30433, true, false, [35837], [9, 11]⟩,
        ⟨98372, false, false, [], [85201, 11, 9, 11]⟩,
        ⟨61728, true, false, [25265], [11, 9, 11]⟩,
        ⟨61733, true, false, [], [9, 11, 9, 11]⟩,
        ⟨61733, true, false, [], [9, 11, 9, 11]⟩,
        ⟨61732, true, false, [], [9, 11, 9, 11]⟩,
        ⟨98357, true, false, [], [9, 11, 9, 11]⟩,
        ⟨98354, true, false, [], [9, 11, 9, 11]⟩,
        ⟨42243, false, false, [96555], []⟩,
        ⟨47, false, false, [96555], []⟩,
        ⟨98369, false, false, [], []⟩,
        ⟨98361, false, false, [], []⟩,
        ⟨98362, false, false, [], []⟩,
        ⟨98362, false, false, [], []⟩
      ]⟩,
    ⟨[85197, 11], [85197, 11], .contexts []⟩,
    ⟨[96345], [96345], .contexts []⟩,
    ⟨[35839], [35836], .source 17984⟩,
    ⟨[35841], [35839, 35833], .source 17985⟩,
    ⟨[85197, 11], [35841, 96345], .contexts [
        ⟨98374, false, false, [], []⟩,
        ⟨98373, false, false, [35836], []⟩,
        ⟨98375, false, false, [35836, 35833], []⟩,
        ⟨98376, true, false, [], [35833, 96345]⟩,
        ⟨98377, true, false, [], [96345]⟩
      ]⟩,
    ⟨[35843], [35840], .source 17986⟩,
    ⟨[35841, 96345], [35841, 96345], .contexts []⟩,
    ⟨[35841, 96345], [35841, 96345], .contexts []⟩,
    ⟨[85197, 11], [35841, 96345], .contexts [
        ⟨98374, false, false, [], []⟩,
        ⟨98378, false, false, [], []⟩,
        ⟨98380, false, false, [], []⟩,
        ⟨98381, false, false, [], []⟩,
        ⟨98381, false, false, [], []⟩
      ]⟩,
    ⟨[85197, 1], [85195], .contexts [
        ⟨30523, false, false, [], []⟩,
        ⟨30524, false, false, [], []⟩,
        ⟨30424, false, false, [], []⟩,
        ⟨30424, false, false, [], []⟩
      ]⟩,
    ⟨[35840], [35840], .contexts []⟩,
    ⟨[96557], [90233, 3], .source 48343⟩,
    ⟨[90233, 3], [96557], .contexts [
        ⟨98385, true, false, [], []⟩
      ]⟩,
    ⟨[96557, 3], [90233], .contexts [
        ⟨98386, true, false, [], [3]⟩,
        ⟨20, false, false, [90233], []⟩,
        ⟨59773, false, false, [], []⟩
      ]⟩,
    ⟨[90233, 3], [96557], .contexts [
        ⟨98386, false, false, [], []⟩
      ]⟩,
    ⟨[96557], [96557], .contexts []⟩,
    ⟨[90233, 3], [96557], .contexts [
        ⟨98388, false, false, [], []⟩,
        ⟨98389, false, false, [], []⟩,
        ⟨98389, false, false, [], []⟩
      ]⟩,
    ⟨[26445, 91633], [26445, 91633], .contexts []⟩,
    ⟨[35845], [26445, 32771], .source 17987⟩,
    ⟨[96557, 7], [35845, 93685], .contexts [
        ⟨98390, true, false, [], [7]⟩,
        ⟨140, false, false, [90233], []⟩,
        ⟨141, false, false, [90233], []⟩,
        ⟨66991, false, false, [], [3]⟩,
        ⟨98391, false, false, [], [3]⟩,
        ⟨98391, false, false, [], [3]⟩,
        ⟨89218, true, false, [26445, 32772], [3]⟩,
        ⟨20, false, false, [26445, 32772, 93685], []⟩,
        ⟨89187, true, false, [26445], [93685]⟩,
        ⟨98392, true, false, [], [93685]⟩,
        ⟨80741, false, false, [35845], []⟩,
        ⟨13, true, false, [], [35845, 93685]⟩
      ]⟩,
    ⟨[35847], [35844], .source 17988⟩,
    ⟨[32755, 95527], [32755, 95527], .contexts []⟩,
    ⟨[35849], [32755, 31389], .source 17989⟩,
    ⟨[96557, 9], [96557, 9], .contexts []⟩,
    ⟨[96557, 9], [35849, 94437], .contexts [
        ⟨98397, false, false, [], []⟩,
        ⟨98390, true, false, [], [9]⟩,
        ⟨669, false, false, [90233], []⟩,
        ⟨670, false, false, [90233], []⟩,
        ⟨92580, false, false, [], [3]⟩,
        ⟨98395, false, false, [], [3]⟩,
        ⟨98395, false, false, [], [3]⟩,
        ⟨92572, false, false, [32755], []⟩,
        ⟨98396, true, false, [], [94437]⟩,
        ⟨84637, false, false, [35849], []⟩,
        ⟨13, true, false, [], [35849, 94437]⟩
      ]⟩,
    ⟨[35851], [35848], .source 17990⟩,
    ⟨[35849, 94437], [35849, 94437], .contexts []⟩,
    ⟨[35853], [35849, 24695], .source 17991⟩,
    ⟨[35853, 87729], [35853, 87729], .contexts []⟩,
    ⟨[35855], [35852], .source 17992⟩,
    ⟨[35852], [35852], .contexts []⟩,
    ⟨[87729, 5], [35855, 96557], .contexts [
        ⟨98402, true, false, [35852], [5]⟩,
        ⟨57925, true, false, [], [5]⟩,
        ⟨98401, false, false, [35852], [87347, 9, 5]⟩,
        ⟨84631, true, false, [35852, 35849], [9, 5]⟩,
        ⟨98400, true, false, [35852], [5, 9, 5]⟩,
        ⟨98400, true, false, [35852], [5, 9, 5]⟩,
        ⟨98398, true, false, [35852], [5, 9, 5]⟩,
        ⟨98397, true, false, [35852], [5, 9, 5]⟩,
        ⟨497, false, false, [35852, 96557], []⟩,
        ⟨98404, true, false, [], [96557]⟩,
        ⟨98404, true, false, [], [96557]⟩,
        ⟨98403, true, false, [], [96557]⟩
      ]⟩,
    ⟨[96559], [87731, 9], .source 48344⟩,
    ⟨[87731, 9], [96559], .contexts [
        ⟨98406, true, false, [], []⟩
      ]⟩,
    ⟨[96559, 9], [87731], .contexts [
        ⟨98407, true, false, [], [9]⟩,
        ⟨46, false, false, [87731], []⟩,
        ⟨45931, false, false, [], []⟩
      ]⟩,
    ⟨[87731, 9], [96559], .contexts [
        ⟨98407, false, false, [], []⟩
      ]⟩,
    ⟨[96559], [96559], .contexts []⟩,
    ⟨[96559], [96559], .contexts []⟩,
    ⟨[23355, 96559], [23355, 96559], .contexts []⟩,
    ⟨[23355, 96559], [23355, 96559], .contexts []⟩,
    ⟨[96559, 7], [96559, 7], .contexts []⟩,
    ⟨[96561], [96559, 11], .source 48345⟩,
    ⟨[96559, 11], [96561], .contexts [
        ⟨98415, true, false, [], []⟩
      ]⟩,
    ⟨[96561], [96561], .contexts []⟩,
    ⟨[96561], [96561], .contexts []⟩,
    ⟨[23355, 96561], [23355, 96561], .contexts []⟩,
    ⟨[23355, 96561], [23355, 96561], .contexts []⟩,
    ⟨[96561, 7], [23355, 96561], .contexts [
        ⟨98418, true, false, [], [7]⟩,
        ⟨98418, true, false, [], [7]⟩,
        ⟨98417, true, false, [], [7]⟩,
        ⟨98416, true, false, [], [7]⟩,
        ⟨647, false, false, [96559], []⟩,
        ⟨648, false, false, [96559], []⟩,
        ⟨98414, false, false, [], [11]⟩,
        ⟨98414, false, false, [], [11]⟩,
        ⟨98411, true, false, [], [7, 11]⟩,
        ⟨98411, true, false, [], [7, 11]⟩,
        ⟨98410, true, false, [], [7, 11]⟩,
        ⟨98409, true, false, [], [7, 11]⟩,
        ⟨1084, false, false, [87731], [11]⟩,
        ⟨1085, false, false, [87731], [11]⟩,
        ⟨52881, false, false, [], [9, 11]⟩,
        ⟨98407, false, false, [23355], [11]⟩,
        ⟨98412, false, false, [], [11]⟩,
        ⟨98413, false, false, [], [11]⟩,
        ⟨57942, true, false, [], [96559, 11]⟩,
        ⟨98412, false, false, [], [11]⟩,
        ⟨98413, false, false, [], [11]⟩,
        ⟨98413, false, false, [], [11]⟩,
        ⟨98416, false, false, [23355], []⟩,
        ⟨98419, false, false, [], []⟩,
        ⟨98420, false, false, [], []⟩
      ]⟩,
    ⟨[96561, 7], [96561, 7], .contexts []⟩,
    ⟨[96563], [96561, 1], .source 48346⟩,
    ⟨[96561, 1], [96563], .contexts [
        ⟨98423, true, false, [], []⟩
      ]⟩,
    ⟨[96563], [96563], .contexts []⟩,
    ⟨[96563], [96563], .contexts []⟩,
    ⟨[23355, 96563], [23355, 96563], .contexts []⟩,
    ⟨[23355, 96563], [23355, 96563], .contexts []⟩,
    ⟨[96563, 7], [96563, 7], .contexts []⟩,
    ⟨[96565], [96563, 13], .source 48347⟩,
    ⟨[96563, 13], [96565], .contexts [
        ⟨98430, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1538. -/
def y322TCIndexRaw1538 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[96565, 13], [96563], .contexts [
        ⟨98431, true, false, [], [13]⟩,
        ⟨59, false, false, [96563], []⟩,
        ⟨98426, false, false, [], []⟩
      ]⟩,
    ⟨[96565], [96565], .contexts []⟩,
    ⟨[96565], [96565], .contexts []⟩,
    ⟨[96563, 7], [23355, 96563], .contexts [
        ⟨98429, false, false, [], []⟩,
        ⟨98429, false, false, [], []⟩,
        ⟨98426, true, false, [], [7]⟩,
        ⟨98426, true, false, [], [7]⟩,
        ⟨98425, true, false, [], [7]⟩,
        ⟨98424, true, false, [], [7]⟩,
        ⟨104, false, false, [96561], []⟩,
        ⟨105, false, false, [96561], []⟩,
        ⟨98422, false, false, [], [1]⟩,
        ⟨98422, false, false, [], [1]⟩,
        ⟨98421, false, false, [], [1]⟩,
        ⟨57942, true, false, [], [96561, 1]⟩,
        ⟨98419, false, false, [], [1]⟩,
        ⟨98420, false, false, [], [1]⟩,
        ⟨98420, false, false, [], [1]⟩,
        ⟨98424, false, false, [23355], []⟩,
        ⟨98427, false, false, [], []⟩,
        ⟨98428, false, false, [], []⟩,
        ⟨57942, true, false, [], [96563]⟩,
        ⟨98427, false, false, [], []⟩,
        ⟨98428, false, false, [], []⟩,
        ⟨98428, false, false, [], []⟩
      ]⟩,
    ⟨[23355, 96565], [23355, 96565], .contexts []⟩,
    ⟨[23355, 96565], [23355, 96565], .contexts []⟩,
    ⟨[96565, 7], [96565, 7], .contexts []⟩,
    ⟨[96565], [96565], .contexts []⟩,
    ⟨[96565, 7], [23355, 96565], .contexts [
        ⟨98438, false, false, [], []⟩,
        ⟨98434, true, false, [], [7]⟩,
        ⟨98434, true, false, [], [7]⟩,
        ⟨98433, true, false, [], [7]⟩,
        ⟨98431, true, false, [], [7]⟩,
        ⟨73, false, false, [96563], []⟩,
        ⟨74, false, false, [96563], []⟩,
        ⟨98435, false, false, [], [13]⟩,
        ⟨98431, false, false, [23355], []⟩,
        ⟨98436, false, false, [], []⟩,
        ⟨98437, false, false, [], []⟩,
        ⟨98439, false, false, [23355], []⟩,
        ⟨57942, true, false, [], [96565]⟩
      ]⟩,
    ⟨[96567], [96565, 15], .source 48348⟩,
    ⟨[96565, 15], [96567], .contexts [
        ⟨98441, true, false, [], []⟩
      ]⟩,
    ⟨[96567], [96567], .contexts []⟩,
    ⟨[96567], [96567], .contexts []⟩,
    ⟨[23355, 96567], [23355, 96567], .contexts []⟩,
    ⟨[23355, 96567], [23355, 96567], .contexts []⟩,
    ⟨[96567, 7], [96567, 7], .contexts []⟩,
    ⟨[96569], [96567, 1], .source 48349⟩,
    ⟨[96567, 1], [96569], .contexts [
        ⟨98448, true, false, [], []⟩
      ]⟩,
    ⟨[96569, 1], [96567], .contexts [
        ⟨98449, true, false, [], [1]⟩,
        ⟨8, false, false, [96567], []⟩,
        ⟨98444, false, false, [], []⟩
      ]⟩,
    ⟨[96569], [96569], .contexts []⟩,
    ⟨[96569], [96569], .contexts []⟩,
    ⟨[23355, 96569], [23355, 96569], .contexts []⟩,
    ⟨[96567, 7, 1], [23355, 96569], .contexts [
        ⟨98447, false, false, [], [1]⟩,
        ⟨98447, false, false, [], [1]⟩,
        ⟨98444, true, false, [], [7, 1]⟩,
        ⟨98444, true, false, [], [7, 1]⟩,
        ⟨98443, true, false, [], [7, 1]⟩,
        ⟨98442, true, false, [], [7, 1]⟩,
        ⟨37, false, false, [96565], [1]⟩,
        ⟨40, false, false, [96565], [1]⟩,
        ⟨98438, false, false, [], [15, 1]⟩,
        ⟨98440, false, false, [], [15, 1]⟩,
        ⟨98436, false, false, [], [15, 1]⟩,
        ⟨98437, false, false, [], [15, 1]⟩,
        ⟨98437, false, false, [], [15, 1]⟩,
        ⟨98442, false, false, [23355], [1]⟩,
        ⟨98445, false, false, [], [1]⟩,
        ⟨98446, false, false, [], [1]⟩,
        ⟨57942, true, false, [], [96567, 1]⟩,
        ⟨98445, false, false, [], [1]⟩,
        ⟨98446, false, false, [], [1]⟩,
        ⟨98446, false, false, [], [1]⟩,
        ⟨98449, false, false, [23355], []⟩,
        ⟨98453, false, false, [], []⟩
      ]⟩,
    ⟨[96569], [96569], .contexts []⟩,
    ⟨[96571], [96569, 3], .source 48350⟩,
    ⟨[96569, 3], [96571], .contexts [
        ⟨98456, true, false, [], []⟩
      ]⟩,
    ⟨[96571], [96571], .contexts []⟩,
    ⟨[96571], [96571], .contexts []⟩,
    ⟨[96573], [96571, 5], .source 48351⟩,
    ⟨[96571, 5], [96573], .contexts [
        ⟨98460, true, false, [], []⟩
      ]⟩,
    ⟨[96573, 5], [96571], .contexts [
        ⟨98461, true, false, [], [5]⟩,
        ⟨28, false, false, [96571], []⟩,
        ⟨98459, false, false, [], []⟩
      ]⟩,
    ⟨[96575], [96573, 1], .source 48352⟩,
    ⟨[96573], [96573], .contexts []⟩,
    ⟨[96575, 1], [96573], .contexts [
        ⟨98463, false, false, [], [1]⟩,
        ⟨8, false, false, [96573], []⟩,
        ⟨98464, false, false, [], []⟩
      ]⟩,
    ⟨[96577], [96575, 9], .source 48353⟩,
    ⟨[96575], [96575], .contexts []⟩,
    ⟨[96577, 9], [96575], .contexts [
        ⟨98466, false, false, [], [9]⟩,
        ⟨46, false, false, [96575], []⟩,
        ⟨98467, false, false, [], []⟩
      ]⟩,
    ⟨[96579], [96577, 11], .source 48354⟩,
    ⟨[96577], [96577], .contexts []⟩,
    ⟨[96579, 11], [96577], .contexts [
        ⟨98469, false, false, [], [11]⟩,
        ⟨53, false, false, [96577], []⟩,
        ⟨98470, false, false, [], []⟩
      ]⟩,
    ⟨[96581], [96579, 1], .source 48355⟩,
    ⟨[96579, 1], [96581], .contexts [
        ⟨98472, true, false, [], []⟩
      ]⟩,
    ⟨[96579], [96579], .contexts []⟩,
    ⟨[96581, 1], [96579], .contexts [
        ⟨98473, true, false, [], [1]⟩,
        ⟨8, false, false, [96579], []⟩,
        ⟨98474, false, false, [], []⟩
      ]⟩,
    ⟨[96583], [96581, 13], .source 48356⟩,
    ⟨[96581], [96581], .contexts []⟩,
    ⟨[96583, 13], [96581], .contexts [
        ⟨98476, false, false, [], [13]⟩,
        ⟨59, false, false, [96581], []⟩,
        ⟨98477, false, false, [], []⟩
      ]⟩,
    ⟨[96585], [96583, 15], .source 48357⟩,
    ⟨[96583, 15], [96585], .contexts [
        ⟨98479, true, false, [], []⟩
      ]⟩,
    ⟨[96583], [96583], .contexts []⟩,
    ⟨[96585, 15], [96583], .contexts [
        ⟨98480, true, false, [], [15]⟩,
        ⟨1, false, false, [96583], []⟩,
        ⟨98481, false, false, [], []⟩
      ]⟩,
    ⟨[96587], [96585, 1], .source 48358⟩,
    ⟨[96585], [96585], .contexts []⟩,
    ⟨[96587, 1], [96585], .contexts [
        ⟨98483, false, false, [], [1]⟩,
        ⟨8, false, false, [96585], []⟩,
        ⟨98484, false, false, [], []⟩
      ]⟩,
    ⟨[96589], [96587, 3], .source 48359⟩,
    ⟨[96587], [96587], .contexts []⟩,
    ⟨[96589, 3], [96587], .contexts [
        ⟨98486, false, false, [], [3]⟩,
        ⟨20, false, false, [96587], []⟩,
        ⟨98487, false, false, [], []⟩
      ]⟩,
    ⟨[96591], [96589, 5], .source 48360⟩,
    ⟨[96589], [96589], .contexts []⟩,
    ⟨[96591, 5], [96589], .contexts [
        ⟨98489, false, false, [], [5]⟩,
        ⟨28, false, false, [96589], []⟩,
        ⟨98490, false, false, [], []⟩
      ]⟩,
    ⟨[96593], [96591, 1], .source 48361⟩,
    ⟨[96591], [96591], .contexts []⟩,
    ⟨[96593, 1], [96591], .contexts [
        ⟨98492, false, false, [], [1]⟩,
        ⟨8, false, false, [96591], []⟩,
        ⟨98493, false, false, [], []⟩
      ]⟩,
    ⟨[96595], [96593, 9], .source 48362⟩]

/-- Exact literal claimed equations and contextual derivations, block 1539. -/
def y322TCIndexRaw1539 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[96593], [96593], .contexts []⟩,
    ⟨[96595, 9], [96593], .contexts [
        ⟨98495, false, false, [], [9]⟩,
        ⟨46, false, false, [96593], []⟩,
        ⟨98496, false, false, [], []⟩
      ]⟩,
    ⟨[96597], [96595, 11], .source 48363⟩,
    ⟨[96595], [96595], .contexts []⟩,
    ⟨[96597, 11], [96595], .contexts [
        ⟨98498, false, false, [], [11]⟩,
        ⟨53, false, false, [96595], []⟩,
        ⟨98499, false, false, [], []⟩
      ]⟩,
    ⟨[96599], [96597, 1], .source 48364⟩,
    ⟨[96597, 1], [96599], .contexts [
        ⟨98501, true, false, [], []⟩
      ]⟩,
    ⟨[96597], [96597], .contexts []⟩,
    ⟨[96599, 1], [96597], .contexts [
        ⟨98502, true, false, [], [1]⟩,
        ⟨8, false, false, [96597], []⟩,
        ⟨98503, false, false, [], []⟩
      ]⟩,
    ⟨[96601], [96599, 13], .source 48365⟩,
    ⟨[96599], [96599], .contexts []⟩,
    ⟨[96601, 13], [96599], .contexts [
        ⟨98505, false, false, [], [13]⟩,
        ⟨59, false, false, [96599], []⟩,
        ⟨98506, false, false, [], []⟩
      ]⟩,
    ⟨[96603], [96601, 15], .source 48366⟩,
    ⟨[96601], [96601], .contexts []⟩,
    ⟨[96603, 15], [96601], .contexts [
        ⟨98508, false, false, [], [15]⟩,
        ⟨1, false, false, [96601], []⟩,
        ⟨98509, false, false, [], []⟩
      ]⟩,
    ⟨[96605], [96603, 1], .source 48367⟩,
    ⟨[96603], [96603], .contexts []⟩,
    ⟨[96607], [96605, 3], .source 48368⟩,
    ⟨[96605], [96605], .contexts []⟩,
    ⟨[96607, 3], [96605], .contexts [
        ⟨98513, false, false, [], [3]⟩,
        ⟨20, false, false, [96605], []⟩,
        ⟨98514, false, false, [], []⟩
      ]⟩,
    ⟨[96609], [96607, 5], .source 48369⟩,
    ⟨[96607], [96607], .contexts []⟩,
    ⟨[96609, 5], [96607], .contexts [
        ⟨98516, false, false, [], [5]⟩,
        ⟨28, false, false, [96607], []⟩,
        ⟨98517, false, false, [], []⟩
      ]⟩,
    ⟨[96611], [96609, 1], .source 48370⟩,
    ⟨[96609], [96609], .contexts []⟩,
    ⟨[96611, 1], [96609], .contexts [
        ⟨98519, false, false, [], [1]⟩,
        ⟨8, false, false, [96609], []⟩,
        ⟨98520, false, false, [], []⟩
      ]⟩,
    ⟨[96613], [96611, 9], .source 48371⟩,
    ⟨[96611], [96611], .contexts []⟩,
    ⟨[96613, 9], [96611], .contexts [
        ⟨98522, false, false, [], [9]⟩,
        ⟨46, false, false, [96611], []⟩,
        ⟨98523, false, false, [], []⟩
      ]⟩,
    ⟨[96615], [96613, 11], .source 48372⟩,
    ⟨[96613], [96613], .contexts []⟩,
    ⟨[96615, 11], [96613], .contexts [
        ⟨98525, false, false, [], [11]⟩,
        ⟨53, false, false, [96613], []⟩,
        ⟨98526, false, false, [], []⟩
      ]⟩,
    ⟨[96617], [96615, 1], .source 48373⟩,
    ⟨[96615, 1], [96617], .contexts [
        ⟨98528, true, false, [], []⟩
      ]⟩,
    ⟨[96615], [96615], .contexts []⟩,
    ⟨[96619], [96617, 13], .source 48374⟩,
    ⟨[96617, 13], [96619], .contexts [
        ⟨98531, true, false, [], []⟩
      ]⟩,
    ⟨[96617], [96617], .contexts []⟩,
    ⟨[96619, 13], [96617], .contexts [
        ⟨98532, true, false, [], [13]⟩,
        ⟨59, false, false, [96617], []⟩,
        ⟨98533, false, false, [], []⟩
      ]⟩,
    ⟨[96621], [96619, 15], .source 48375⟩,
    ⟨[96619, 15], [96621], .contexts [
        ⟨98535, true, false, [], []⟩
      ]⟩,
    ⟨[96619], [96619], .contexts []⟩,
    ⟨[96621, 15], [96619], .contexts [
        ⟨98536, true, false, [], [15]⟩,
        ⟨1, false, false, [96619], []⟩,
        ⟨98537, false, false, [], []⟩
      ]⟩,
    ⟨[96623], [96621, 1], .source 48376⟩,
    ⟨[96621, 1], [96623], .contexts [
        ⟨98539, true, false, [], []⟩
      ]⟩,
    ⟨[96621], [96621], .contexts []⟩,
    ⟨[96625], [96623, 3], .source 48377⟩,
    ⟨[96623, 3], [96625], .contexts [
        ⟨98542, true, false, [], []⟩
      ]⟩,
    ⟨[96623], [96623], .contexts []⟩,
    ⟨[96625, 3], [96623], .contexts [
        ⟨98543, true, false, [], [3]⟩,
        ⟨20, false, false, [96623], []⟩,
        ⟨98544, false, false, [], []⟩
      ]⟩,
    ⟨[96627], [96625, 5], .source 48378⟩,
    ⟨[96625], [96625], .contexts []⟩,
    ⟨[96627, 5], [96625], .contexts [
        ⟨98546, false, false, [], [5]⟩,
        ⟨28, false, false, [96625], []⟩,
        ⟨98547, false, false, [], []⟩
      ]⟩,
    ⟨[96629], [96627, 1], .source 48379⟩,
    ⟨[96627], [96627], .contexts []⟩,
    ⟨[96629, 1], [96627], .contexts [
        ⟨98549, false, false, [], [1]⟩,
        ⟨8, false, false, [96627], []⟩,
        ⟨98550, false, false, [], []⟩
      ]⟩,
    ⟨[96631], [96629, 9], .source 48380⟩,
    ⟨[96629], [96629], .contexts []⟩,
    ⟨[96631, 9], [96629], .contexts [
        ⟨98552, false, false, [], [9]⟩,
        ⟨46, false, false, [96629], []⟩,
        ⟨98553, false, false, [], []⟩
      ]⟩,
    ⟨[96633], [96631, 11], .source 48381⟩,
    ⟨[96631], [96631], .contexts []⟩,
    ⟨[96633, 11], [96631], .contexts [
        ⟨98555, false, false, [], [11]⟩,
        ⟨53, false, false, [96631], []⟩,
        ⟨98556, false, false, [], []⟩
      ]⟩,
    ⟨[96635], [96633, 1], .source 48382⟩,
    ⟨[96633, 1], [96635], .contexts [
        ⟨98558, true, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1540. -/
def y322TCIndexRaw1540 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[96633], [96633], .contexts []⟩,
    ⟨[96635], [96635], .contexts []⟩,
    ⟨[96631, 9], [96629], .contexts [
        ⟨98554, false, false, [], []⟩
      ]⟩,
    ⟨[96629], [96629], .contexts []⟩,
    ⟨[96629, 1], [96627], .contexts [
        ⟨98551, false, false, [], []⟩
      ]⟩,
    ⟨[96627], [96627], .contexts []⟩,
    ⟨[96627, 5], [96625], .contexts [
        ⟨98548, false, false, [], []⟩
      ]⟩,
    ⟨[96625], [96625], .contexts []⟩,
    ⟨[96625, 3], [96623], .contexts [
        ⟨98545, false, false, [], []⟩
      ]⟩,
    ⟨[96623], [96623], .contexts []⟩,
    ⟨[96633, 11, 9, 1, 5, 3], [96623], .contexts [
        ⟨98557, false, false, [], [9, 1, 5, 3]⟩,
        ⟨98556, false, false, [], [9, 1, 5, 3]⟩,
        ⟨98556, false, false, [], [9, 1, 5, 3]⟩,
        ⟨98562, false, false, [], [1, 5, 3]⟩,
        ⟨98563, false, false, [], [1, 5, 3]⟩,
        ⟨98553, false, false, [], [1, 5, 3]⟩,
        ⟨98553, false, false, [], [1, 5, 3]⟩,
        ⟨98564, false, false, [], [5, 3]⟩,
        ⟨98565, false, false, [], [5, 3]⟩,
        ⟨98550, false, false, [], [5, 3]⟩,
        ⟨98550, false, false, [], [5, 3]⟩,
        ⟨98566, false, false, [], [3]⟩,
        ⟨98567, false, false, [], [3]⟩,
        ⟨98547, false, false, [], [3]⟩,
        ⟨98547, false, false, [], [3]⟩,
        ⟨98568, false, false, [], []⟩,
        ⟨98569, false, false, [], []⟩,
        ⟨98544, false, false, [], []⟩,
        ⟨98544, false, false, [], []⟩
      ]⟩,
    ⟨[96623, 1], [96621], .contexts [
        ⟨98540, true, false, [], [1]⟩,
        ⟨8, false, false, [96621], []⟩,
        ⟨98541, false, false, [], []⟩
      ]⟩,
    ⟨[96621], [96621], .contexts []⟩,
    ⟨[96619], [96619], .contexts []⟩,
    ⟨[96617], [96617], .contexts []⟩,
    ⟨[96617, 1], [96615], .contexts [
        ⟨98529, true, false, [], [1]⟩,
        ⟨8, false, false, [96615], []⟩,
        ⟨98530, false, false, [], []⟩
      ]⟩,
    ⟨[96615], [96615], .contexts []⟩,
    ⟨[96615, 11], [96613], .contexts [
        ⟨98527, false, false, [], []⟩
      ]⟩,
    ⟨[96613], [96613], .contexts []⟩,
    ⟨[96633, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11], [96613], .contexts [
        ⟨98570, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨98571, false, false, [], [15, 13, 1, 11]⟩,
        ⟨98572, false, false, [], [15, 13, 1, 11]⟩,
        ⟨98541, false, false, [], [15, 13, 1, 11]⟩,
        ⟨98541, false, false, [], [15, 13, 1, 11]⟩,
        ⟨98538, false, false, [], [13, 1, 11]⟩,
        ⟨98573, false, false, [], [13, 1, 11]⟩,
        ⟨98537, false, false, [], [13, 1, 11]⟩,
        ⟨98537, false, false, [], [13, 1, 11]⟩,
        ⟨98534, false, false, [], [1, 11]⟩,
        ⟨98574, false, false, [], [1, 11]⟩,
        ⟨98533, false, false, [], [1, 11]⟩,
        ⟨98533, false, false, [], [1, 11]⟩,
        ⟨98575, false, false, [], [11]⟩,
        ⟨98576, false, false, [], [11]⟩,
        ⟨98530, false, false, [], [11]⟩,
        ⟨98530, false, false, [], [11]⟩,
        ⟨98577, false, false, [], []⟩,
        ⟨98578, false, false, [], []⟩,
        ⟨98526, false, false, [], []⟩,
        ⟨98526, false, false, [], []⟩
      ]⟩,
    ⟨[96613, 9], [96611], .contexts [
        ⟨98524, false, false, [], []⟩
      ]⟩,
    ⟨[96611], [96611], .contexts []⟩,
    ⟨[96611, 1], [96609], .contexts [
        ⟨98521, false, false, [], []⟩
      ]⟩,
    ⟨[96609], [96609], .contexts []⟩,
    ⟨[96609, 5], [96607], .contexts [
        ⟨98518, false, false, [], []⟩
      ]⟩,
    ⟨[96607], [96607], .contexts []⟩,
    ⟨[96605, 1], [96603], .contexts [
        ⟨98511, false, false, [], [1]⟩,
        ⟨8, false, false, [96603], []⟩,
        ⟨98512, false, false, [], []⟩
      ]⟩,
    ⟨[96603], [96603], .contexts []⟩,
    ⟨[
      96633, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1
    ], [96603], .contexts [
        ⟨98579, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨98580, false, false, [], [1, 5, 3, 1]⟩,
        ⟨98581, false, false, [], [1, 5, 3, 1]⟩,
        ⟨98523, false, false, [], [1, 5, 3, 1]⟩,
        ⟨98523, false, false, [], [1, 5, 3, 1]⟩,
        ⟨98582, false, false, [], [5, 3, 1]⟩,
        ⟨98583, false, false, [], [5, 3, 1]⟩,
        ⟨98520, false, false, [], [5, 3, 1]⟩,
        ⟨98520, false, false, [], [5, 3, 1]⟩,
        ⟨98584, false, false, [], [3, 1]⟩,
        ⟨98585, false, false, [], [3, 1]⟩,
        ⟨98517, false, false, [], [3, 1]⟩,
        ⟨98517, false, false, [], [3, 1]⟩,
        ⟨98515, false, false, [], [1]⟩,
        ⟨98514, false, false, [], [1]⟩,
        ⟨98514, false, false, [], [1]⟩,
        ⟨98586, false, false, [], []⟩,
        ⟨98587, false, false, [], []⟩,
        ⟨98512, false, false, [], []⟩,
        ⟨98512, false, false, [], []⟩
      ]⟩,
    ⟨[96601], [96601], .contexts []⟩,
    ⟨[96599], [96599], .contexts []⟩,
    ⟨[96597], [96597], .contexts []⟩,
    ⟨[96597, 11], [96595], .contexts [
        ⟨98500, false, false, [], []⟩
      ]⟩,
    ⟨[96595], [96595], .contexts []⟩,
    ⟨[96593], [96593], .contexts []⟩,
    ⟨[
      96633, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [96593], .contexts [
        ⟨98588, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨98510, false, false, [], [13, 1, 11, 9]⟩,
        ⟨98589, false, false, [], [13, 1, 11, 9]⟩,
        ⟨98509, false, false, [], [13, 1, 11, 9]⟩,
        ⟨98509, false, false, [], [13, 1, 11, 9]⟩,
        ⟨98507, false, false, [], [1, 11, 9]⟩,
        ⟨98590, false, false, [], [1, 11, 9]⟩,
        ⟨98506, false, false, [], [1, 11, 9]⟩,
        ⟨98506, false, false, [], [1, 11, 9]⟩,
        ⟨98504, false, false, [], [11, 9]⟩,
        ⟨98591, false, false, [], [11, 9]⟩,
        ⟨98503, false, false, [], [11, 9]⟩,
        ⟨98503, false, false, [], [11, 9]⟩,
        ⟨98592, false, false, [], [9]⟩,
        ⟨98593, false, false, [], [9]⟩,
        ⟨98499, false, false, [], [9]⟩,
        ⟨98499, false, false, [], [9]⟩,
        ⟨98497, false, false, [], []⟩,
        ⟨98594, false, false, [], []⟩,
        ⟨98496, false, false, [], []⟩,
        ⟨98496, false, false, [], []⟩
      ]⟩,
    ⟨[96591], [96591], .contexts []⟩,
    ⟨[96589], [96589], .contexts []⟩,
    ⟨[96587], [96587], .contexts []⟩,
    ⟨[96585], [96585], .contexts []⟩,
    ⟨[96583], [96583], .contexts []⟩,
    ⟨[
      96633, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15
    ], [96583], .contexts [
        ⟨98595, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨98494, false, false, [], [5, 3, 1, 15]⟩,
        ⟨98596, false, false, [], [5, 3, 1, 15]⟩,
        ⟨98493, false, false, [], [5, 3, 1, 15]⟩,
        ⟨98493, false, false, [], [5, 3, 1, 15]⟩,
        ⟨98491, false, false, [], [3, 1, 15]⟩,
        ⟨98597, false, false, [], [3, 1, 15]⟩,
        ⟨98490, false, false, [], [3, 1, 15]⟩,
        ⟨98490, false, false, [], [3, 1, 15]⟩,
        ⟨98488, false, false, [], [1, 15]⟩,
        ⟨98598, false, false, [], [1, 15]⟩,
        ⟨98487, false, false, [], [1, 15]⟩,
        ⟨98487, false, false, [], [1, 15]⟩,
        ⟨98485, false, false, [], [15]⟩,
        ⟨98599, false, false, [], [15]⟩,
        ⟨98484, false, false, [], [15]⟩,
        ⟨98484, false, false, [], [15]⟩,
        ⟨98482, false, false, [], []⟩,
        ⟨98600, false, false, [], []⟩,
        ⟨98481, false, false, [], []⟩,
        ⟨98481, false, false, [], []⟩
      ]⟩,
    ⟨[96581], [96581], .contexts []⟩,
    ⟨[96575], [96575], .contexts []⟩,
    ⟨[96573], [96573], .contexts []⟩,
    ⟨[
      96633, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1
    ], [96573], .contexts [
        ⟨98601, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨98478, false, false, [], [1, 11, 9, 1]⟩,
        ⟨98602, false, false, [], [1, 11, 9, 1]⟩,
        ⟨98477, false, false, [], [1, 11, 9, 1]⟩,
        ⟨98477, false, false, [], [1, 11, 9, 1]⟩,
        ⟨98475, false, false, [], [11, 9, 1]⟩,
        ⟨98474, false, false, [], [11, 9, 1]⟩,
        ⟨98474, false, false, [], [11, 9, 1]⟩,
        ⟨98471, false, false, [], [9, 1]⟩,
        ⟨98470, false, false, [], [9, 1]⟩,
        ⟨98470, false, false, [], [9, 1]⟩,
        ⟨98468, false, false, [], [1]⟩,
        ⟨98603, false, false, [], [1]⟩,
        ⟨98467, false, false, [], [1]⟩,
        ⟨98467, false, false, [], [1]⟩,
        ⟨98465, false, false, [], []⟩,
        ⟨98604, false, false, [], []⟩,
        ⟨98464, false, false, [], []⟩,
        ⟨98464, false, false, [], []⟩
      ]⟩,
    ⟨[
      96633, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [96563], .contexts [
        ⟨98605, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨98462, false, false, [], [3, 1, 15, 13]⟩,
        ⟨98458, false, false, [], [3, 1, 15, 13]⟩,
        ⟨98459, false, false, [], [3, 1, 15, 13]⟩,
        ⟨98459, false, false, [], [3, 1, 15, 13]⟩,
        ⟨98457, true, false, [], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [96569], [1, 15, 13]⟩,
        ⟨98452, false, false, [], [1, 15, 13]⟩,
        ⟨98451, false, false, [], [1, 15, 13]⟩,
        ⟨98452, false, false, [], [1, 15, 13]⟩,
        ⟨98452, false, false, [], [1, 15, 13]⟩,
        ⟨98450, false, false, [], [15, 13]⟩,
        ⟨98443, false, false, [], [15, 13]⟩,
        ⟨98444, false, false, [], [15, 13]⟩,
        ⟨98444, false, false, [], [15, 13]⟩,
        ⟨98442, true, false, [], [15, 13]⟩,
        ⟨1, false, false, [96565], [13]⟩,
        ⟨98434, false, false, [], [13]⟩,
        ⟨98433, false, false, [], [13]⟩,
        ⟨98434, false, false, [], [13]⟩,
        ⟨98434, false, false, [], [13]⟩,
        ⟨98432, false, false, [], []⟩,
        ⟨98425, false, false, [], []⟩,
        ⟨98426, false, false, [], []⟩,
        ⟨98426, false, false, [], []⟩
      ]⟩,
    ⟨[
      96633, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1
    ], [87729], .contexts [
        ⟨98606, false, false, [], [1, 11, 9, 1]⟩,
        ⟨98424, true, false, [], [1, 11, 9, 1]⟩,
        ⟨8, false, false, [96561], [11, 9, 1]⟩,
        ⟨98418, false, false, [], [11, 9, 1]⟩,
        ⟨98417, false, false, [], [11, 9, 1]⟩,
        ⟨98418, false, false, [], [11, 9, 1]⟩,
        ⟨98418, false, false, [], [11, 9, 1]⟩,
        ⟨98416, true, false, [], [11, 9, 1]⟩,
        ⟨53, false, false, [96559], [9, 1]⟩,
        ⟨98411, false, false, [], [9, 1]⟩,
        ⟨98410, false, false, [], [9, 1]⟩,
        ⟨98411, false, false, [], [9, 1]⟩,
        ⟨98411, false, false, [], [9, 1]⟩,
        ⟨98408, false, false, [], [1]⟩,
        ⟨46114, false, false, [], [1]⟩,
        ⟨45931, false, false, [], [1]⟩,
        ⟨45931, false, false, [], [1]⟩,
        ⟨46115, false, false, [], []⟩,
        ⟨45919, false, false, [], []⟩,
        ⟨45920, false, false, [], []⟩,
        ⟨45920, false, false, [], []⟩
      ]⟩,
    ⟨[35855, 96557], [35855, 96557], .contexts []⟩,
    ⟨[35857], [35855, 19897], .source 17993⟩,
    ⟨[
      96633, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [35857, 96553], .contexts [
        ⟨98607, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨98405, false, false, [], [3, 1, 15, 13]⟩,
        ⟨98608, false, false, [], [3, 1, 15, 13]⟩,
        ⟨98608, false, false, [], [3, 1, 15, 13]⟩,
        ⟨98387, false, false, [35855], [1, 15, 13]⟩,
        ⟨59782, false, false, [35855], [15, 13]⟩,
        ⟨98371, false, false, [35855], [13]⟩,
        ⟨98609, true, false, [], [96555, 13]⟩,
        ⟨98344, true, false, [35857], [13]⟩,
        ⟨59, false, false, [35857, 96553], []⟩,
        ⟨98339, false, false, [35857], []⟩
      ]⟩,
    ⟨[35859], [35857, 18941], .source 17994⟩,
    ⟨[35861], [35859, 26723], .source 17995⟩,
    ⟨[
      96633, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5
    ], [35861, 91935], .contexts [
        ⟨98610, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨98337, false, false, [35857], [11, 9, 1, 5]⟩,
        ⟨98318, false, false, [35857], [9, 1, 5]⟩,
        ⟨35678, false, false, [35857], [1, 5]⟩,
        ⟨35888, false, false, [35857], [5]⟩,
        ⟨98611, true, false, [], [85935, 5]⟩,
        ⟨68261, false, false, [35859], []⟩,
        ⟨98612, true, false, [], [91935]⟩
      ]⟩,
    ⟨[35863], [35861, 30895], .source 17996⟩,
    ⟨[35865], [35863, 30889], .source 17997⟩,
    ⟨[35867], [35865, 35825], .source 17998⟩,
    ⟨[
      96633, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1
    ], [35867, 83003], .contexts [
        ⟨98613, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨82510, false, false, [35861], [1, 15, 13, 1]⟩,
        ⟨98614, true, false, [], [94055, 1, 15, 13, 1]⟩,
        ⟨82388, false, false, [35863], [15, 13, 1]⟩,
        ⟨98310, false, false, [35863], [15, 13, 1]⟩,
        ⟨98615, true, false, [], [94055, 15, 13, 1]⟩,
        ⟨98315, false, false, [35865], [13, 1]⟩,
        ⟨98616, true, false, [], [96549, 13, 1]⟩,
        ⟨98289, false, false, [35867], [1]⟩,
        ⟨18397, false, false, [35867], []⟩
      ]⟩,
    ⟨[35869], [35867, 20673], .source 17999⟩,
    ⟨[35871], [35869, 21967], .source 18000⟩,
    ⟨[35873], [35871, 20551], .source 18001⟩,
    ⟨[35875], [35873, 19297], .source 18002⟩,
    ⟨[
      96633, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [35875, 85079], .contexts [
        ⟨98617, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨42788, false, false, [35867], [9, 1, 5, 3]⟩,
        ⟨98618, true, false, [], [85865, 9, 1, 5, 3]⟩,
        ⟨47184, false, false, [35869], [1, 5, 3]⟩,
        ⟨98619, true, false, [], [84731, 1, 5, 3]⟩,
        ⟨28492, false, false, [35871], [5, 3]⟩,
        ⟨42429, false, false, [35871], [3]⟩,
        ⟨98620, true, false, [], [85079, 3]⟩,
        ⟨37709, false, false, [35873], []⟩,
        ⟨98621, true, false, [], [85079]⟩
      ]⟩,
    ⟨[35877], [35875, 20553], .source 18003⟩]

/-- Exact literal claimed equations and contextual derivations, block 1541. -/
def y322TCIndexRaw1541 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[35879], [35877, 20375], .source 18004⟩,
    ⟨[35881], [35879, 17441], .source 18005⟩,
    ⟨[35883], [35881, 20469], .source 18006⟩,
    ⟨[
      96633, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11
    ], [35883, 84589], .contexts [
        ⟨98622, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨42219, false, false, [35875], [15, 13, 1, 11]⟩,
        ⟨98623, true, false, [], [84729, 15, 13, 1, 11]⟩,
        ⟨42049, false, false, [35877], [13, 1, 11]⟩,
        ⟨98624, true, false, [], [84587, 13, 1, 11]⟩,
        ⟨27335, false, false, [35879], [1, 11]⟩,
        ⟨27743, false, false, [35879], [11]⟩,
        ⟨98625, true, false, [], [84589, 11]⟩,
        ⟨42043, false, false, [35881], []⟩,
        ⟨98626, true, false, [], [84589]⟩
      ]⟩,
    ⟨[35885], [35883, 19201], .source 18007⟩,
    ⟨[35887], [35885, 16309], .source 18008⟩,
    ⟨[35889], [35887, 20541], .source 18009⟩,
    ⟨[35891], [35889, 20547], .source 18010⟩,
    ⟨[35893], [35891, 2575], .source 18011⟩,
    ⟨[
      96633, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1
    ], [35893, 83151], .contexts [
        ⟨98627, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨37534, false, false, [35883], [1, 5, 3, 1]⟩,
        ⟨98628, true, false, [], [83475, 1, 5, 3, 1]⟩,
        ⟨21461, false, false, [35885], [5, 3, 1]⟩,
        ⟨98629, true, false, [], [83479, 5, 3, 1]⟩,
        ⟨34519, false, false, [35887], [3, 1]⟩,
        ⟨42211, false, false, [35887], [3, 1]⟩,
        ⟨98630, true, false, [], [85245, 3, 1]⟩,
        ⟨42209, false, false, [35889], [1]⟩,
        ⟨98631, true, false, [], [83151, 1]⟩,
        ⟨19228, false, false, [35891], []⟩,
        ⟨98632, true, false, [], [83151]⟩
      ]⟩,
    ⟨[35895], [35893, 1075], .source 18012⟩,
    ⟨[35897], [35895, 15607], .source 18013⟩,
    ⟨[35899], [35897, 15213], .source 18014⟩,
    ⟨[35901], [35899, 15239], .source 18015⟩,
    ⟨[
      96633, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9
    ], [35901, 82817], .contexts [
        ⟨98633, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨19244, false, false, [35893], [13, 1, 11, 9]⟩,
        ⟨98634, true, false, [], [83151, 13, 1, 11, 9]⟩,
        ⟨19242, false, false, [35895], [1, 11, 9]⟩,
        ⟨98635, true, false, [], [82833, 1, 11, 9]⟩,
        ⟨17315, false, false, [35897], [11, 9]⟩,
        ⟨98636, true, false, [], [82839, 11, 9]⟩,
        ⟨17320, false, false, [35899], [9]⟩,
        ⟨98637, true, false, [], [82669, 9]⟩,
        ⟨17018, false, false, [35901], []⟩
      ]⟩,
    ⟨[35903], [35901, 7357], .source 18016⟩,
    ⟨[35905], [35903, 15537], .source 18017⟩,
    ⟨[35907], [35905, 553], .source 18018⟩,
    ⟨[35909], [35907, 15433], .source 18019⟩,
    ⟨[35911], [35909, 15217], .source 18020⟩,
    ⟨[
      96633, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15
    ], [35911, 79191], .contexts [
        ⟨98638, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨17008, false, false, [35901], [5, 3, 1, 15]⟩,
        ⟨98639, true, false, [], [82813, 5, 3, 1, 15]⟩,
        ⟨16942, false, false, [35903], [3, 1, 15]⟩,
        ⟨98640, true, false, [], [82775, 3, 1, 15]⟩,
        ⟨16472, false, false, [35905], [1, 15]⟩,
        ⟨98641, true, false, [], [82775, 1, 15]⟩,
        ⟨16493, false, false, [35907], [15]⟩,
        ⟨98642, true, false, [], [82671, 15]⟩,
        ⟨15200, false, false, [35909], []⟩,
        ⟨98643, true, false, [], [79191]⟩
      ]⟩,
    ⟨[35913], [35911, 15551], .source 18021⟩,
    ⟨[35915], [35913, 16187], .source 18022⟩,
    ⟨[
      96633, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1
    ], [35915, 83185], .contexts [
        ⟨98644, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨17034, false, false, [35911], [1, 11, 9, 1]⟩,
        ⟨17044, false, false, [35911], [11, 9, 1]⟩,
        ⟨98645, true, false, [], [81373, 11, 9, 1]⟩,
        ⟨20701, false, false, [35913], [9, 1]⟩,
        ⟨20837, false, false, [35913], [1]⟩,
        ⟨20844, false, false, [35913], []⟩,
        ⟨98646, true, false, [], [83185]⟩
      ]⟩,
    ⟨[35917], [35915, 17071], .source 18023⟩,
    ⟨[35919], [35917, 727], .source 18024⟩,
    ⟨[96635, 13], [96635, 13], .contexts []⟩,
    ⟨[96635, 13], [35919, 93679], .contexts [
        ⟨98650, false, false, [], []⟩,
        ⟨98561, true, false, [], [13]⟩,
        ⟨98561, true, false, [], [13]⟩,
        ⟨98559, true, false, [], [13]⟩,
        ⟨5361, false, false, [96633], []⟩,
        ⟨5362, false, false, [96633], []⟩,
        ⟨98647, false, false, [], [5, 3, 1, 15]⟩,
        ⟨26319, false, false, [35915], [3, 1, 15]⟩,
        ⟨98648, true, false, [], [84363, 3, 1, 15]⟩,
        ⟨80651, false, false, [35917], [1, 15]⟩,
        ⟨80676, false, false, [35917], [15]⟩,
        ⟨80700, false, false, [35917], []⟩,
        ⟨98649, true, false, [], [93679]⟩,
        ⟨80691, false, false, [35919], []⟩
      ]⟩,
    ⟨[96635, 13], [35919, 93679], .contexts [
        ⟨98651, false, false, [], []⟩,
        ⟨13, true, false, [], [35919, 93679]⟩
      ]⟩,
    ⟨[35921], [35918], .source 18025⟩,
    ⟨[93679, 13], [35921, 96635], .contexts [
        ⟨98652, true, false, [35918], [13]⟩,
        ⟨59, false, false, [35918, 96635], []⟩,
        ⟨98653, true, false, [], [96635]⟩
      ]⟩,
    ⟨[35919, 93679], [35919, 93679], .contexts []⟩,
    ⟨[35923], [35919, 2797], .source 18026⟩,
    ⟨[35923, 93679], [35923, 93679], .contexts []⟩,
    ⟨[96635, 13, 1, 13, 1], [35923, 93679], .contexts [
        ⟨98650, false, false, [], [1, 13, 1]⟩,
        ⟨98652, false, false, [], [1, 13, 1]⟩,
        ⟨98655, false, false, [], [1, 13, 1]⟩,
        ⟨98655, false, false, [], [1, 13, 1]⟩,
        ⟨80677, false, false, [35919], [13, 1]⟩,
        ⟨80655, true, false, [35919], [13, 1]⟩,
        ⟨147, false, false, [35919, 84363], [1]⟩,
        ⟨148, false, false, [35919, 84363], [1]⟩,
        ⟨26332, false, false, [35919], [3, 1]⟩,
        ⟨26333, false, false, [35919], [3, 1]⟩,
        ⟨26330, false, false, [35919], [3, 1]⟩,
        ⟨26331, false, false, [35919], [3, 1]⟩,
        ⟨26331, false, false, [35919], [3, 1]⟩,
        ⟨80651, false, false, [35919, 2797], [1]⟩,
        ⟨80663, false, false, [35919, 2797], [1]⟩,
        ⟨19607, true, false, [35919], [93677, 1]⟩,
        ⟨98656, true, false, [], [93677, 1]⟩,
        ⟨80676, false, false, [35923], []⟩,
        ⟨98657, false, false, [], []⟩
      ]⟩,
    ⟨[35923, 93679], [35923, 93679], .contexts []⟩,
    ⟨[96633, 13], [96633, 13], .contexts []⟩,
    ⟨[96633, 13], [35923, 93679], .contexts [
        ⟨98660, false, false, [], []⟩,
        ⟨98560, true, false, [], [13]⟩,
        ⟨98560, true, false, [], [13]⟩,
        ⟨98560, true, false, [], [13]⟩,
        ⟨8, true, false, [96633], [13]⟩,
        ⟨98559, false, false, [], [1, 13]⟩,
        ⟨115, false, false, [96635], []⟩,
        ⟨118, false, false, [96635], []⟩,
        ⟨98658, false, false, [], []⟩,
        ⟨98659, false, false, [], []⟩,
        ⟨80691, false, false, [35923], []⟩,
        ⟨13, true, false, [], [35923, 93679]⟩
      ]⟩,
    ⟨[35925], [35922], .source 18027⟩,
    ⟨[93679, 13], [35921, 96635], .contexts [
        ⟨98654, false, false, [], []⟩
      ]⟩,
    ⟨[35921, 96635], [35921, 96635], .contexts []⟩,
    ⟨[35927], [35919, 35925], .source 18028⟩,
    ⟨[96633, 13], [35923, 93679], .contexts [
        ⟨98660, false, false, [], []⟩,
        ⟨98661, false, false, [], []⟩,
        ⟨98657, false, false, [], []⟩,
        ⟨98659, false, false, [], []⟩,
        ⟨98659, false, false, [], []⟩
      ]⟩,
    ⟨[35929], [35923, 30495], .source 18029⟩,
    ⟨[96633], [96633], .contexts []⟩,
    ⟨[92037, 3], [92037, 3], .contexts []⟩,
    ⟨[96633], [96633], .contexts []⟩,
    ⟨[35931], [35928], .source 18030⟩,
    ⟨[35928], [35928], .contexts []⟩,
    ⟨[92037, 3], [35931, 96633], .contexts [
        ⟨98669, false, false, [], []⟩,
        ⟨68982, true, false, [], [3]⟩,
        ⟨98667, false, false, [35928], [92039, 13, 3]⟩,
        ⟨80685, true, false, [35928, 35923], [13, 3]⟩,
        ⟨98666, true, false, [35928], [3, 13, 3]⟩,
        ⟨4550, false, false, [35928, 96633], []⟩,
        ⟨98668, false, false, [35928], []⟩,
        ⟨98670, false, false, [35928], []⟩,
        ⟨98672, true, false, [], [96633]⟩,
        ⟨98672, true, false, [], [96633]⟩,
        ⟨98671, true, false, [], [96633]⟩
      ]⟩,
    ⟨[35933], [35923, 30491], .source 18031⟩,
    ⟨[96635], [35927, 96633], .contexts [
        ⟨98664, true, false, [35920], []⟩,
        ⟨98664, true, false, [35920], []⟩,
        ⟨98663, true, false, [35920], []⟩,
        ⟨98661, true, false, [35920, 35922], [13]⟩,
        ⟨59, false, false, [35920, 35922, 96633], []⟩,
        ⟨98662, true, false, [35920], [96633]⟩,
        ⟨98653, false, true, [], [35925, 96633]⟩,
        ⟨98665, true, false, [], [96633]⟩
      ]⟩,
    ⟨[35935], [35921, 35927], .source 18032⟩,
    ⟨[35937], [35933, 35935], .source 18033⟩,
    ⟨[35939], [35936], .source 18034⟩,
    ⟨[35936], [35936], .contexts []⟩,
    ⟨[35941], [35923, 25829], .source 18035⟩,
    ⟨[35943], [35941, 25851], .source 18036⟩,
    ⟨[91107, 7], [91107, 7], .contexts []⟩,
    ⟨[35945], [35942], .source 18037⟩,
    ⟨[35942], [35942], .contexts []⟩,
    ⟨[91107, 7], [35945, 96633], .contexts [
        ⟨98682, false, false, [], []⟩,
        ⟨98681, false, false, [35942], [91107, 7]⟩,
        ⟨64381, true, false, [35942, 35941], [7]⟩,
        ⟨64225, true, false, [35942, 35941], [7]⟩,
        ⟨98680, false, false, [35942], [91113, 13, 7]⟩,
        ⟨80693, true, false, [35942, 35923], [13, 7]⟩,
        ⟨98666, true, false, [35942], [7, 13, 7]⟩,
        ⟨21371, false, false, [35942, 96633], []⟩,
        ⟨98668, false, false, [35942], []⟩,
        ⟨98670, false, false, [35942], []⟩,
        ⟨98684, true, false, [], [96633]⟩,
        ⟨98684, true, false, [], [96633]⟩,
        ⟨98683, true, false, [], [96633]⟩
      ]⟩,
    ⟨[35947], [35923, 16023], .source 18038⟩,
    ⟨[35949], [35947, 35935], .source 18039⟩]

/-- Exact literal claimed equations and contextual derivations, block 1542. -/
def y322TCIndexRaw1542 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[35949, 96631], [35949, 96631], .contexts []⟩,
    ⟨[96633, 13, 11, 13, 11], [35949, 96631], .contexts [
        ⟨98666, false, false, [], [11, 13, 11]⟩,
        ⟨80680, true, false, [35923], [11, 13, 11]⟩,
        ⟨110, false, false, [35923, 93677], [13, 11]⟩,
        ⟨111, false, false, [35923, 93677], [13, 11]⟩,
        ⟨80695, false, false, [35923], [13, 11]⟩,
        ⟨80691, false, false, [35923, 16023], [13, 11]⟩,
        ⟨19784, true, false, [35923], [93679, 13, 11]⟩,
        ⟨98686, true, false, [], [93679, 13, 11]⟩,
        ⟨98654, false, false, [35947], [11]⟩,
        ⟨98675, false, false, [35947, 35921], [11]⟩,
        ⟨98676, true, false, [35947], [96633, 11]⟩,
        ⟨98687, true, false, [], [96633, 11]⟩,
        ⟨98557, false, false, [35949], []⟩,
        ⟨98688, false, false, [], []⟩
      ]⟩,
    ⟨[96633], [35949, 96631], .contexts [
        ⟨98670, false, false, [], []⟩,
        ⟨81, true, false, [96633], []⟩,
        ⟨98689, false, false, [], []⟩
      ]⟩,
    ⟨[35951], [35927, 35949], .source 18040⟩,
    ⟨[96635], [35951, 96631], .contexts [
        ⟨98675, false, false, [], []⟩,
        ⟨98690, false, false, [35927], []⟩,
        ⟨98691, true, false, [], [96631]⟩
      ]⟩,
    ⟨[35953], [35948], .source 18041⟩,
    ⟨[35955], [35953, 35951], .source 18042⟩,
    ⟨[96633], [35949, 96631], .contexts [
        ⟨98690, false, false, [], []⟩,
        ⟨98688, false, false, [], []⟩
      ]⟩,
    ⟨[35961], [35953, 35939], .source 18045⟩,
    ⟨[35963], [35961, 35949], .source 18046⟩,
    ⟨[35965], [35953, 35943], .source 18047⟩,
    ⟨[35967], [35921, 35951], .source 18048⟩,
    ⟨[96629, 13], [96629, 13], .contexts []⟩,
    ⟨[35969], [35966], .source 18049⟩,
    ⟨[35966], [35966], .contexts []⟩,
    ⟨[96629, 13], [35969, 93681], .contexts [
        ⟨98700, false, false, [], []⟩,
        ⟨98554, true, false, [], [13]⟩,
        ⟨98699, false, false, [35966], [96631, 9, 13]⟩,
        ⟨98692, true, false, [35966, 35921], [9, 13]⟩,
        ⟨98663, true, false, [35966], [9, 13]⟩,
        ⟨942, false, false, [35966, 93679], []⟩,
        ⟨47, false, false, [35966, 93679], []⟩,
        ⟨80706, false, false, [35966], []⟩,
        ⟨80717, false, false, [35966], []⟩,
        ⟨98702, true, false, [], [93681]⟩,
        ⟨98702, true, false, [], [93681]⟩,
        ⟨98701, true, false, [], [93681]⟩
      ]⟩,
    ⟨[35967], [35968], .contexts [
        ⟨98701, true, true, [], []⟩
      ]⟩,
    ⟨[35955, 96631], [35955, 96631], .contexts []⟩,
    ⟨[96631, 9], [96629], .contexts [
        ⟨98562, false, false, [], []⟩,
        ⟨98563, false, false, [], []⟩,
        ⟨98553, false, false, [], []⟩,
        ⟨98553, false, false, [], []⟩
      ]⟩,
    ⟨[35955, 96627, 9], [96631, 1, 9, 1, 9], .contexts [
        ⟨98551, true, false, [35955], [9]⟩,
        ⟨98554, true, false, [35955], [1, 9]⟩,
        ⟨98705, true, false, [], [9, 1, 9]⟩,
        ⟨98705, true, false, [], [9, 1, 9]⟩,
        ⟨98694, false, false, [], [96631, 9, 1, 9]⟩,
        ⟨98693, false, false, [], [35951, 96631, 9, 1, 9]⟩,
        ⟨98692, true, false, [35948], [9, 1, 9]⟩,
        ⟨98559, true, false, [35948], [9, 1, 9]⟩,
        ⟨98690, false, false, [35948], [1, 9, 1, 9]⟩
      ]⟩,
    ⟨[96627, 9], [96627, 9], .contexts []⟩,
    ⟨[96627], [96627], .contexts []⟩,
    ⟨[35971], [35954], .source 18050⟩,
    ⟨[35954], [35954], .contexts []⟩,
    ⟨[35971], [35954], .contexts [
        ⟨98710, false, false, [], []⟩,
        ⟨98711, false, false, [], []⟩,
        ⟨98711, false, false, [], []⟩
      ]⟩,
    ⟨[35931, 96633], [35931, 35949, 96631], .contexts [
        ⟨98695, false, false, [35931], []⟩
      ]⟩,
    ⟨[35973], [35931, 35949], .source 18051⟩,
    ⟨[35975], [35972], .source 18052⟩,
    ⟨[35977], [35975, 29621], .source 18053⟩,
    ⟨[96629, 3], [35977, 91719], .contexts [
        ⟨98554, true, false, [], [3]⟩,
        ⟨98714, false, false, [35972], [96631, 9, 3]⟩,
        ⟨98713, true, false, [35972], [9, 3]⟩,
        ⟨98673, true, false, [35972], [9, 3]⟩,
        ⟨98669, true, false, [35972], [9, 3]⟩,
        ⟨573, false, false, [35972, 92037], []⟩,
        ⟨47, false, false, [35972, 92037], []⟩,
        ⟨77661, false, false, [35972], []⟩,
        ⟨77583, false, false, [35972, 29621], []⟩,
        ⟨98715, true, false, [], [29621, 91719]⟩,
        ⟨98716, true, false, [], [91719]⟩
      ]⟩,
    ⟨[96631, 5], [35963, 96631], .contexts [
        ⟨98690, true, false, [35948], [5]⟩,
        ⟨98677, false, false, [35948, 35936], [96633, 5]⟩,
        ⟨98676, false, false, [35948, 35936, 35933], [96633, 5]⟩,
        ⟨98675, true, false, [35948, 35936, 35933, 35921], [5]⟩,
        ⟨98654, true, false, [35948, 35936, 35933], [5]⟩,
        ⟨98674, false, false, [35948, 35936], [93679, 13, 5]⟩,
        ⟨80692, true, false, [35948, 35936, 35923], [13, 5]⟩,
        ⟨98666, true, false, [35948, 35936], [5, 13, 5]⟩,
        ⟨1116, false, false, [35948, 35936, 96633], []⟩,
        ⟨98668, false, false, [35948, 35936], []⟩,
        ⟨98670, false, false, [35948, 35936], []⟩,
        ⟨98679, true, false, [35948], [96633]⟩,
        ⟨98679, true, false, [35948], [96633]⟩,
        ⟨98678, true, false, [35948], [96633]⟩,
        ⟨98695, false, false, [35948, 35939], []⟩,
        ⟨98693, true, false, [], [35939, 35949, 96631]⟩,
        ⟨98696, true, false, [], [35949, 96631]⟩,
        ⟨98697, true, false, [], [96631]⟩
      ]⟩,
    ⟨[35963, 96631], [35963, 96631], .contexts []⟩,
    ⟨[35963, 96629], [35963, 96629], .contexts []⟩,
    ⟨[35963, 96629], [35963, 96629], .contexts []⟩,
    ⟨[96629, 5], [96629, 5], .contexts []⟩,
    ⟨[96629], [96629], .contexts []⟩,
    ⟨[35981], [35962], .source 18055⟩,
    ⟨[35981], [35981], .contexts []⟩,
    ⟨[35962], [35962], .contexts []⟩,
    ⟨[35983], [35945, 35949], .source 18056⟩,
    ⟨[96629, 7], [96629, 7], .contexts []⟩,
    ⟨[35985], [35982], .source 18057⟩,
    ⟨[35982], [35982], .contexts []⟩,
    ⟨[96629, 7], [35985, 91105], .contexts [
        ⟨98728, false, false, [], []⟩,
        ⟨98554, true, false, [], [7]⟩,
        ⟨98727, false, false, [35982], [96631, 9, 7]⟩,
        ⟨98695, true, false, [35982, 35945], [9, 7]⟩,
        ⟨98685, true, false, [35982], [9, 7]⟩,
        ⟨98682, true, false, [35982], [9, 7]⟩,
        ⟨579, false, false, [35982, 91107], []⟩,
        ⟨78988, false, false, [35982], []⟩,
        ⟨64386, false, false, [35982], []⟩,
        ⟨78990, false, false, [35982], []⟩,
        ⟨98730, true, false, [], [91105]⟩,
        ⟨98730, true, false, [], [91105]⟩,
        ⟨98729, true, false, [], [91105]⟩
      ]⟩,
    ⟨[35983], [35984], .contexts [
        ⟨98729, true, true, [], []⟩
      ]⟩,
    ⟨[35969, 93681], [35969, 93681], .contexts []⟩,
    ⟨[35969, 93681], [35969, 93681], .contexts []⟩,
    ⟨[96629, 13], [35969, 93681], .contexts [
        ⟨98700, false, false, [], []⟩,
        ⟨98703, false, false, [], []⟩,
        ⟨98733, false, false, [], []⟩,
        ⟨98734, false, false, [], []⟩,
        ⟨98734, false, false, [], []⟩
      ]⟩,
    ⟨[35987], [35969, 34937], .source 18058⟩,
    ⟨[35989], [35987, 34927], .source 18059⟩,
    ⟨[96629, 1], [96627], .contexts [
        ⟨98564, false, false, [], []⟩
      ]⟩,
    ⟨[96629, 1], [96627], .contexts [
        ⟨98738, false, false, [], []⟩,
        ⟨98565, false, false, [], []⟩,
        ⟨98550, false, false, [], []⟩,
        ⟨98550, false, false, [], []⟩
      ]⟩,
    ⟨[96629, 0], [96629, 1], .contexts [
        ⟨9, false, false, [96629], []⟩
      ]⟩,
    ⟨[96041, 13], [96041, 13], .contexts []⟩,
    ⟨[35991], [35988], .source 18060⟩,
    ⟨[35988], [35988], .contexts []⟩,
    ⟨[96041, 13], [35991, 96627], .contexts [
        ⟨98741, false, false, [], []⟩,
        ⟨98737, false, false, [35988], [96041, 13]⟩,
        ⟨95513, true, false, [35988, 35987], [13]⟩,
        ⟨95377, true, false, [35988, 35987], [13]⟩,
        ⟨98736, false, false, [35988], [96045, 1, 13]⟩,
        ⟨95498, true, false, [35988, 35969], [1, 13]⟩,
        ⟨80710, true, false, [35988, 35969], [13, 1, 13]⟩,
        ⟨98735, true, false, [35988], [1, 13, 1, 13]⟩,
        ⟨2012, false, false, [35988, 96629], []⟩,
        ⟨98740, false, false, [35988], []⟩,
        ⟨98739, false, false, [35988], []⟩,
        ⟨98709, false, false, [35988], []⟩,
        ⟨98743, true, false, [], [96627]⟩,
        ⟨98743, true, false, [], [96627]⟩,
        ⟨98742, true, false, [], [96627]⟩
      ]⟩,
    ⟨[35969, 87587], [35969, 87587], .contexts []⟩,
    ⟨[96629], [96629], .contexts []⟩,
    ⟨[35968], [35968], .contexts []⟩,
    ⟨[35971, 96627], [35971, 96627], .contexts []⟩,
    ⟨[35971, 96625, 9], [96627, 5], .contexts [
        ⟨98548, true, false, [35971], [9]⟩,
        ⟨98748, true, false, [], [5, 9]⟩,
        ⟨98748, true, false, [], [5, 9]⟩,
        ⟨98712, false, false, [], [96627, 5, 9]⟩,
        ⟨98709, true, false, [35954], [5, 9]⟩,
        ⟨98550, true, false, [35954], [5, 9]⟩,
        ⟨98550, true, false, [35954], [5, 9]⟩,
        ⟨98565, true, false, [35954], [5, 9]⟩,
        ⟨98564, true, false, [35954], [5, 9]⟩,
        ⟨98706, true, false, [35954], [1, 5, 9]⟩,
        ⟨453, true, false, [35954, 96631], [5, 9]⟩,
        ⟨582, true, false, [35954, 96631], [5, 9]⟩,
        ⟨98707, true, false, [35954], [5, 9]⟩,
        ⟨98708, true, false, [], [5, 9]⟩,
        ⟨98708, true, false, [], [5, 9]⟩,
        ⟨598, false, false, [96627], []⟩,
        ⟨29, false, false, [96627], []⟩
      ]⟩,
    ⟨[96625, 9], [96625, 9], .contexts []⟩,
    ⟨[96625], [96625], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1543. -/
def y322TCIndexRaw1543 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[35970], [35970], .contexts []⟩,
    ⟨[35981, 96629], [35981, 96629], .contexts []⟩,
    ⟨[96629, 5], [35981, 96629], .contexts [
        ⟨98722, false, false, [], []⟩,
        ⟨98722, false, false, [], []⟩,
        ⟨98721, true, false, [35962], [5]⟩,
        ⟨98720, true, false, [35962], [5]⟩,
        ⟨98554, true, false, [], [5]⟩,
        ⟨98719, true, false, [35962], [9, 5]⟩,
        ⟨98719, true, false, [35962], [9, 5]⟩,
        ⟨98718, true, false, [35962], [9, 5]⟩,
        ⟨960, false, false, [35962, 96631], []⟩,
        ⟨47, false, false, [35962, 96631], []⟩,
        ⟨98706, false, false, [35962], []⟩,
        ⟨98723, false, false, [35962], []⟩,
        ⟨98726, true, false, [], [96629]⟩,
        ⟨98726, true, false, [], [96629]⟩,
        ⟨98724, true, false, [], [96629]⟩,
        ⟨98725, true, false, [], [96629]⟩,
        ⟨98753, false, false, [], []⟩,
        ⟨98753, false, false, [], []⟩
      ]⟩,
    ⟨[35981, 96625], [35981, 96625], .contexts []⟩,
    ⟨[35981, 96625], [35981, 96625], .contexts []⟩,
    ⟨[96625, 1], [96625, 1], .contexts []⟩,
    ⟨[35980], [35980], .contexts []⟩,
    ⟨[96625, 1], [35963, 96629], .contexts [
        ⟨98757, false, false, [], []⟩,
        ⟨98756, true, false, [35980], [1]⟩,
        ⟨98755, true, false, [35980], [1]⟩,
        ⟨98548, true, false, [], [1]⟩,
        ⟨98551, true, false, [], [5, 1]⟩,
        ⟨98754, true, false, [35980], [1, 5, 1]⟩,
        ⟨874, false, false, [35980, 96629], []⟩,
        ⟨98746, false, false, [35980], []⟩,
        ⟨98723, false, false, [35980], []⟩,
        ⟨98758, true, false, [], [96629]⟩,
        ⟨98758, true, false, [], [96629]⟩,
        ⟨98724, false, true, [], [96629]⟩
      ]⟩,
    ⟨[96627], [35981, 96625], .contexts [
        ⟨98739, true, false, [], []⟩,
        ⟨98759, true, false, [35962], [1]⟩,
        ⟨8, false, false, [35962, 96625], []⟩,
        ⟨98724, true, false, [], [96625]⟩,
        ⟨98755, false, false, [], []⟩,
        ⟨98725, true, false, [], [96625]⟩,
        ⟨98756, false, false, [], []⟩
      ]⟩,
    ⟨[35985, 91105], [35985, 91105], .contexts []⟩,
    ⟨[35985, 91105], [35985, 91105], .contexts []⟩,
    ⟨[35995], [35983, 35981], .source 18062⟩,
    ⟨[91103, 7], [35995, 96625], .contexts [
        ⟨64211, true, false, [], [7]⟩,
        ⟨98762, true, false, [35984], [1, 7]⟩,
        ⟨98762, true, false, [35984], [1, 7]⟩,
        ⟨98761, true, false, [35984], [1, 7]⟩,
        ⟨98731, true, false, [35984], [1, 7]⟩,
        ⟨98728, true, false, [35984], [1, 7]⟩,
        ⟨502, false, false, [35984, 96629], []⟩,
        ⟨98740, false, false, [35984], []⟩,
        ⟨98738, false, false, [35984], []⟩,
        ⟨98760, false, false, [35984], []⟩,
        ⟨98756, false, false, [35984], []⟩,
        ⟨98756, false, false, [35984], []⟩,
        ⟨98751, false, false, [35984, 35981], []⟩,
        ⟨98732, true, false, [], [35981, 96625]⟩,
        ⟨98763, true, false, [], [96625]⟩
      ]⟩,
    ⟨[35997], [35994], .source 18063⟩,
    ⟨[96625, 7], [35997, 91103], .contexts [
        ⟨98764, true, false, [35994], [7]⟩,
        ⟨38, false, false, [35994, 91103], []⟩,
        ⟨98765, true, false, [], [91103]⟩
      ]⟩,
    ⟨[35991, 96627], [35991, 35981, 96625], .contexts [
        ⟨98760, false, false, [35991], []⟩
      ]⟩,
    ⟨[35999], [35991, 35981], .source 18064⟩,
    ⟨[96041, 13], [35999, 96625], .contexts [
        ⟨98741, false, false, [], []⟩,
        ⟨98744, false, false, [], []⟩,
        ⟨98767, false, false, [], []⟩,
        ⟨98768, true, false, [], [96625]⟩
      ]⟩,
    ⟨[96623, 13], [96623, 13], .contexts []⟩,
    ⟨[36001], [35998], .source 18065⟩,
    ⟨[36003], [36001, 34945], .source 18066⟩,
    ⟨[96623, 13], [36003, 83309], .contexts [
        ⟨98770, false, false, [], []⟩,
        ⟨98545, true, false, [], [13]⟩,
        ⟨98769, true, false, [35998], [3, 13]⟩,
        ⟨1132, false, false, [35998, 96041], []⟩,
        ⟨21, false, false, [35998, 96041], []⟩,
        ⟨95531, false, false, [35998], []⟩,
        ⟨61783, false, false, [35998, 34945], []⟩,
        ⟨98771, true, false, [], [34945, 83309]⟩,
        ⟨98772, true, false, [], [83309]⟩
      ]⟩,
    ⟨[36005], [36002], .source 18067⟩,
    ⟨[83309, 13], [36005, 96623], .contexts [
        ⟨98773, true, false, [36002], [13]⟩,
        ⟨59, false, false, [36002, 96623], []⟩,
        ⟨98774, true, false, [], [96623]⟩
      ]⟩,
    ⟨[36007], [35999, 35997], .source 18068⟩,
    ⟨[91103, 13], [91103, 13], .contexts []⟩,
    ⟨[36009], [36006], .source 18069⟩,
    ⟨[36011], [36009, 34951], .source 18070⟩,
    ⟨[91103, 13], [36011, 90209], .contexts [
        ⟨98777, false, false, [], []⟩,
        ⟨98776, false, false, [36006], [91103, 13]⟩,
        ⟨98766, true, false, [36006, 35999], [13]⟩,
        ⟨98769, true, false, [36006], [7, 13]⟩,
        ⟨14716, false, false, [36006, 96041], []⟩,
        ⟨95536, false, false, [36006], []⟩,
        ⟨95535, false, false, [36006], []⟩,
        ⟨59629, false, false, [36006, 34951], []⟩,
        ⟨98778, true, false, [], [34951, 90209]⟩,
        ⟨98779, true, false, [], [90209]⟩
      ]⟩,
    ⟨[36013], [36010], .source 18071⟩,
    ⟨[90209, 13], [36013, 91103], .contexts [
        ⟨98780, true, false, [36010], [13]⟩,
        ⟨59, false, false, [36010, 91103], []⟩,
        ⟨98781, true, false, [], [91103]⟩
      ]⟩,
    ⟨[35955, 96625], [35955, 96625], .contexts []⟩,
    ⟨[96625, 3], [96623], .contexts [
        ⟨98568, false, false, [], []⟩,
        ⟨98569, false, false, [], []⟩,
        ⟨98544, false, false, [], []⟩,
        ⟨98544, false, false, [], []⟩
      ]⟩,
    ⟨[35955, 96623, 9], [96625, 2], .contexts [
        ⟨98545, true, false, [35955], [9]⟩,
        ⟨98783, true, false, [], [3, 9]⟩,
        ⟨98783, true, false, [], [3, 9]⟩,
        ⟨98710, true, true, [], [96625, 3, 9]⟩,
        ⟨98752, false, false, [], [96625, 3, 9]⟩,
        ⟨98752, false, false, [], [96625, 3, 9]⟩,
        ⟨98751, true, false, [35970], [3, 9]⟩,
        ⟨98547, true, false, [35970], [3, 9]⟩,
        ⟨98547, true, false, [35970], [3, 9]⟩,
        ⟨98567, true, false, [35970], [3, 9]⟩,
        ⟨98566, true, false, [35970], [3, 9]⟩,
        ⟨98749, true, false, [35970], [3, 9]⟩,
        ⟨98750, true, false, [], [3, 9]⟩,
        ⟨98750, true, false, [], [3, 9]⟩,
        ⟨479, false, false, [96625], []⟩
      ]⟩,
    ⟨[36015], [35963, 35977], .source 18072⟩,
    ⟨[36015, 91717], [36015, 91717], .contexts []⟩,
    ⟨[91717, 3], [91717, 3], .contexts []⟩,
    ⟨[96621], [96621], .contexts []⟩,
    ⟨[36017], [36014], .source 18073⟩,
    ⟨[36014], [36014], .contexts []⟩,
    ⟨[91717, 3], [36017, 96621], .contexts [
        ⟨98788, false, false, [], []⟩,
        ⟨98787, true, false, [36014], [3]⟩,
        ⟨67147, true, false, [], [3]⟩,
        ⟨98786, false, false, [36014], [91719, 1, 3]⟩,
        ⟨98717, true, false, [36014, 35963], [1, 3]⟩,
        ⟨98721, true, false, [36014], [3, 1, 3]⟩,
        ⟨98721, true, false, [36014], [3, 1, 3]⟩,
        ⟨98720, true, false, [36014], [3, 1, 3]⟩,
        ⟨98759, true, false, [36014], [3, 1, 3]⟩,
        ⟨98757, true, false, [36014], [3, 1, 3]⟩,
        ⟨484, false, false, [36014, 96625], []⟩,
        ⟨485, false, false, [36014, 96625], []⟩,
        ⟨98784, false, false, [36014], [1]⟩,
        ⟨98571, false, false, [36014], []⟩,
        ⟨98572, false, false, [36014], []⟩,
        ⟨98541, false, false, [36014], []⟩,
        ⟨98541, false, false, [36014], []⟩,
        ⟨98789, false, false, [36014], []⟩,
        ⟨98791, true, false, [], [96621]⟩,
        ⟨98791, true, false, [], [96621]⟩,
        ⟨98790, true, false, [], [96621]⟩
      ]⟩,
    ⟨[36015], [36016], .contexts [
        ⟨98790, true, true, [], []⟩
      ]⟩,
    ⟨[35997, 91103], [35997, 91103], .contexts []⟩,
    ⟨[35997, 91103], [35997, 91103], .contexts []⟩,
    ⟨[36019], [35997, 30067], .source 18074⟩,
    ⟨[96623, 7], [96623, 7], .contexts []⟩,
    ⟨[96623, 7], [36019, 93401], .contexts [
        ⟨98797, false, false, [], []⟩,
        ⟨98784, true, false, [], [7]⟩,
        ⟨140, false, false, [96625], []⟩,
        ⟨141, false, false, [96625], []⟩,
        ⟨98766, false, false, [], [3]⟩,
        ⟨98794, false, false, [], [3]⟩,
        ⟨98795, false, false, [], [3]⟩,
        ⟨98795, false, false, [], [3]⟩,
        ⟨79023, false, false, [35997], []⟩,
        ⟨98796, true, false, [], [93401]⟩,
        ⟨79035, false, false, [36019], []⟩,
        ⟨13, true, false, [], [36019, 93401]⟩
      ]⟩,
    ⟨[36021], [36018], .source 18075⟩,
    ⟨[36003, 83309], [36003, 83309], .contexts []⟩,
    ⟨[36003, 83309], [36003, 83309], .contexts []⟩,
    ⟨[96623, 13], [36003, 83309], .contexts [
        ⟨98770, false, false, [], []⟩,
        ⟨98773, false, false, [], []⟩,
        ⟨98800, false, false, [], []⟩,
        ⟨98801, false, false, [], []⟩,
        ⟨98801, false, false, [], []⟩
      ]⟩,
    ⟨[36023], [36003, 25301], .source 18076⟩,
    ⟨[36023, 84465], [36023, 84465], .contexts []⟩,
    ⟨[96623, 1], [96621], .contexts [
        ⟨98571, false, false, [], []⟩,
        ⟨98572, false, false, [], []⟩,
        ⟨98541, false, false, [], []⟩,
        ⟨98541, false, false, [], []⟩
      ]⟩,
    ⟨[96623, 0], [96623, 1], .contexts [
        ⟨9, false, false, [96623], []⟩
      ]⟩,
    ⟨[84465, 13], [84465, 13], .contexts []⟩,
    ⟨[36025], [36022], .source 18077⟩,
    ⟨[36025], [36022], .contexts [
        ⟨98808, false, false, [], []⟩
      ]⟩,
    ⟨[36022], [36022], .contexts []⟩,
    ⟨[36025], [36022], .contexts [
        ⟨98809, false, false, [], []⟩,
        ⟨98810, false, false, [], []⟩,
        ⟨98810, false, false, [], []⟩
      ]⟩,
    ⟨[84465, 13], [36025, 96621], .contexts [
        ⟨98807, false, false, [], []⟩,
        ⟨98804, true, false, [36022], [13]⟩,
        ⟨26883, true, false, [], [13]⟩,
        ⟨98803, false, false, [36022], [84467, 1, 13]⟩,
        ⟨61793, true, false, [36022, 36003], [1, 13]⟩,
        ⟨20335, true, false, [36022, 36003], [13, 1, 13]⟩,
        ⟨98802, true, false, [36022], [1, 13, 1, 13]⟩,
        ⟨2012, false, false, [36022, 96623], []⟩,
        ⟨98806, false, false, [36022], []⟩,
        ⟨98805, false, false, [36022], []⟩,
        ⟨98789, false, false, [36022], []⟩,
        ⟨98811, true, false, [], [96621]⟩
      ]⟩,
    ⟨[36023], [36024], .contexts [
        ⟨98808, true, true, [], []⟩
      ]⟩,
    ⟨[36027], [36003, 25293], .source 18078⟩,
    ⟨[36019, 93401], [36019, 93401], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1544. -/
def y322TCIndexRaw1544 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[36019, 93401], [36019, 93401], .contexts []⟩,
    ⟨[96623, 7], [36019, 93401], .contexts [
        ⟨98797, false, false, [], []⟩,
        ⟨98798, false, false, [], []⟩,
        ⟨98815, false, false, [], []⟩,
        ⟨98816, false, false, [], []⟩,
        ⟨98816, false, false, [], []⟩
      ]⟩,
    ⟨[87295, 13], [87295, 13], .contexts []⟩,
    ⟨[36029], [36026], .source 18079⟩,
    ⟨[36031], [36029, 36019], .source 18080⟩,
    ⟨[87295, 13], [36031, 93401], .contexts [
        ⟨98818, false, false, [], []⟩,
        ⟨98814, false, false, [36026], [87295, 13]⟩,
        ⟨61785, true, false, [36026, 36003], [13]⟩,
        ⟨98802, true, false, [36026], [7, 13]⟩,
        ⟨14716, false, false, [36026, 96623], []⟩,
        ⟨39, false, false, [36026, 96623], []⟩,
        ⟨98817, false, false, [36026], []⟩,
        ⟨79035, false, false, [36026, 36019], []⟩,
        ⟨98819, true, false, [], [36019, 93401]⟩,
        ⟨98820, true, false, [], [93401]⟩
      ]⟩,
    ⟨[36033], [36030], .source 18081⟩,
    ⟨[36011, 90209], [36011, 90209], .contexts []⟩,
    ⟨[36011, 90209], [36011, 90209], .contexts []⟩,
    ⟨[36011, 90207], [36011, 90207], .contexts []⟩,
    ⟨[90207, 13], [90207, 13], .contexts []⟩,
    ⟨[36010], [36010], .contexts []⟩,
    ⟨[90207, 13], [36013, 91101], .contexts [
        ⟨98826, false, false, [], []⟩,
        ⟨98825, true, false, [36010], [13]⟩,
        ⟨59389, true, false, [], [13]⟩,
        ⟨98824, true, false, [36010], [5, 13]⟩,
        ⟨98824, true, false, [36010], [5, 13]⟩,
        ⟨98823, true, false, [36010], [5, 13]⟩,
        ⟨98780, true, false, [36010], [5, 13]⟩,
        ⟨98777, true, false, [36010], [5, 13]⟩,
        ⟨1136, false, false, [36010, 91103], []⟩,
        ⟨64399, false, false, [36010], []⟩,
        ⟨64398, false, false, [36010], []⟩,
        ⟨64401, false, false, [36010], []⟩,
        ⟨98827, true, false, [], [91101]⟩,
        ⟨98827, true, false, [], [91101]⟩,
        ⟨98781, true, false, [], [91101]⟩
      ]⟩,
    ⟨[36019, 93399], [36019, 93399], .contexts []⟩,
    ⟨[93399, 7], [93399, 7], .contexts []⟩,
    ⟨[36018], [36018], .contexts []⟩,
    ⟨[93399, 7], [36021, 96621], .contexts [
        ⟨98830, false, false, [], []⟩,
        ⟨98829, true, false, [36018], [7]⟩,
        ⟨78799, true, false, [], [7]⟩,
        ⟨98817, true, false, [36018], [1, 7]⟩,
        ⟨502, false, false, [36018, 96623], []⟩,
        ⟨98806, false, false, [36018], []⟩,
        ⟨98805, false, false, [36018], []⟩,
        ⟨98789, false, false, [36018], []⟩,
        ⟨98831, true, false, [], [96621]⟩,
        ⟨98831, true, false, [], [96621]⟩,
        ⟨98799, true, false, [], [96621]⟩
      ]⟩,
    ⟨[36019], [36020], .contexts [
        ⟨98799, true, true, [], []⟩
      ]⟩,
    ⟨[96621, 7], [36019, 93399], .contexts [
        ⟨98832, true, false, [36020], [7]⟩,
        ⟨38, false, false, [36020, 93399], []⟩,
        ⟨98833, true, false, [], [93399]⟩
      ]⟩,
    ⟨[36025, 96621], [36025, 96621], .contexts []⟩,
    ⟨[84465, 13], [36025, 96621], .contexts [
        ⟨98807, false, false, [], []⟩,
        ⟨98812, false, false, [], []⟩,
        ⟨98835, false, false, [], []⟩,
        ⟨98835, false, false, [], []⟩
      ]⟩,
    ⟨[36035], [36025, 36019], .source 18082⟩,
    ⟨[93399, 13], [93399, 13], .contexts []⟩,
    ⟨[36037], [36034], .source 18083⟩,
    ⟨[36039], [36037, 21789], .source 18084⟩,
    ⟨[93399, 13], [36039, 84327], .contexts [
        ⟨98838, false, false, [], []⟩,
        ⟨98837, false, false, [36034], [93399, 13]⟩,
        ⟨98834, true, false, [36034, 36025], [13]⟩,
        ⟨98836, true, false, [36034], [7, 13]⟩,
        ⟨14716, false, false, [36034, 84465], []⟩,
        ⟨39, false, false, [36034, 84465], []⟩,
        ⟨46434, false, false, [36034], []⟩,
        ⟨46427, false, false, [36034], []⟩,
        ⟨46428, false, false, [36034], []⟩,
        ⟨46428, false, false, [36034], []⟩,
        ⟨41292, false, false, [36034, 21789], []⟩,
        ⟨98839, true, false, [], [21789, 84327]⟩,
        ⟨98840, true, false, [], [84327]⟩
      ]⟩,
    ⟨[36041], [36038], .source 18085⟩,
    ⟨[84327, 13], [36041, 93399], .contexts [
        ⟨98841, true, false, [36038], [13]⟩,
        ⟨59, false, false, [36038, 93399], []⟩,
        ⟨98842, true, false, [], [93399]⟩
      ]⟩,
    ⟨[96617, 15], [96617, 15], .contexts []⟩,
    ⟨[36023], [36023], .contexts []⟩,
    ⟨[36023], [36024], .contexts [
        ⟨98845, false, false, [], []⟩,
        ⟨98813, false, false, [], []⟩
      ]⟩,
    ⟨[36024], [36024], .contexts []⟩,
    ⟨[36023], [36024], .contexts [
        ⟨98846, false, false, [], []⟩,
        ⟨98847, false, false, [], []⟩,
        ⟨98847, false, false, [], []⟩
      ]⟩,
    ⟨[96617, 15], [36023, 84461], .contexts [
        ⟨98844, false, false, [], []⟩,
        ⟨98534, true, false, [], [15]⟩,
        ⟨98538, true, false, [], [13, 15]⟩,
        ⟨98836, true, false, [36024], [15, 13, 15]⟩,
        ⟨2022, false, false, [36024, 84465], []⟩,
        ⟨89, false, false, [36024, 84465], []⟩,
        ⟨50671, false, false, [36024], [13]⟩,
        ⟨26940, false, false, [36024], []⟩,
        ⟨26941, false, false, [36024], []⟩,
        ⟨26874, false, false, [36024], []⟩,
        ⟨26874, false, false, [36024], []⟩,
        ⟨98848, true, false, [], [84461]⟩
      ]⟩,
    ⟨[36013, 91101], [36013, 91101], .contexts []⟩,
    ⟨[36043], [36013, 30087], .source 18086⟩,
    ⟨[91097, 13], [91097, 13], .contexts []⟩,
    ⟨[36045], [36042], .source 18087⟩,
    ⟨[36042], [36042], .contexts []⟩,
    ⟨[91097, 13], [36045, 90205], .contexts [
        ⟨98852, false, false, [], []⟩,
        ⟨98851, false, false, [36042], [91097, 13]⟩,
        ⟨79054, true, false, [36042, 36013], [13]⟩,
        ⟨64203, true, false, [36042, 36013], [13]⟩,
        ⟨98850, true, false, [36042], [3, 13]⟩,
        ⟨98850, true, false, [36042], [3, 13]⟩,
        ⟨98828, true, false, [36042], [3, 13]⟩,
        ⟨98826, true, false, [36042], [3, 13]⟩,
        ⟨1132, false, false, [36042, 90207], []⟩,
        ⟨59656, false, false, [36042], []⟩,
        ⟨59655, false, false, [36042], []⟩,
        ⟨59657, false, false, [36042], []⟩,
        ⟨98854, true, false, [], [90205]⟩,
        ⟨98854, true, false, [], [90205]⟩,
        ⟨98853, true, false, [], [90205]⟩
      ]⟩,
    ⟨[36043], [36044], .contexts [
        ⟨98853, true, true, [], []⟩
      ]⟩,
    ⟨[90205, 13], [36043, 91097], .contexts [
        ⟨98855, true, false, [36044], [13]⟩,
        ⟨59, false, false, [36044, 91097], []⟩,
        ⟨98856, true, false, [], [91097]⟩
      ]⟩,
    ⟨[93399, 7], [36021, 96621], .contexts [
        ⟨98830, false, false, [], []⟩,
        ⟨98832, false, false, [], []⟩
      ]⟩,
    ⟨[36021, 96621], [36021, 96621], .contexts []⟩,
    ⟨[36021, 96619], [36021, 96619], .contexts []⟩,
    ⟨[93399, 15], [93397], .contexts [
        ⟨78831, false, false, [], []⟩,
        ⟨78832, false, false, [], []⟩,
        ⟨78794, false, false, [], []⟩,
        ⟨78794, false, false, [], []⟩
      ]⟩,
    ⟨[93399, 14], [93399, 15], .contexts [
        ⟨10, false, false, [93399], []⟩
      ]⟩,
    ⟨[93397], [93397], .contexts []⟩,
    ⟨[36020], [36020], .contexts []⟩,
    ⟨[96619, 7], [36019, 93397], .contexts [
        ⟨98860, true, false, [36020], [7]⟩,
        ⟨98538, true, false, [], [7]⟩,
        ⟨98859, true, false, [36020], [15, 7]⟩,
        ⟨98859, true, false, [36020], [15, 7]⟩,
        ⟨98858, true, false, [36020], [15, 7]⟩,
        ⟨18155, false, false, [36020, 93399], []⟩,
        ⟨98862, false, false, [36020], []⟩,
        ⟨98861, false, false, [36020], []⟩,
        ⟨98863, false, false, [36020], []⟩,
        ⟨98864, true, false, [], [93397]⟩,
        ⟨98864, true, false, [], [93397]⟩,
        ⟨98833, true, false, [], [93397]⟩
      ]⟩,
    ⟨[36039, 84327], [36039, 84327], .contexts []⟩,
    ⟨[36039, 84327], [36039, 84327], .contexts []⟩,
    ⟨[93399, 13], [36039, 84327], .contexts [
        ⟨98838, false, false, [], []⟩,
        ⟨98841, false, false, [], []⟩,
        ⟨98866, false, false, [], []⟩,
        ⟨98867, false, false, [], []⟩,
        ⟨98867, false, false, [], []⟩
      ]⟩,
    ⟨[36047], [36039, 20039], .source 18088⟩,
    ⟨[36049], [36047, 22419], .source 18089⟩,
    ⟨[88179, 15], [88179, 15], .contexts []⟩,
    ⟨[93395], [93395], .contexts []⟩,
    ⟨[36051], [36048], .source 18090⟩,
    ⟨[36051], [36051], .contexts []⟩,
    ⟨[36051], [36048], .contexts [
        ⟨98873, false, false, [], []⟩
      ]⟩,
    ⟨[36048], [36048], .contexts []⟩,
    ⟨[36051], [36048], .contexts [
        ⟨98874, false, false, [], []⟩,
        ⟨98875, false, false, [], []⟩,
        ⟨98876, false, false, [], []⟩,
        ⟨98876, false, false, [], []⟩
      ]⟩,
    ⟨[88179, 15], [36051, 93395], .contexts [
        ⟨98871, false, false, [], []⟩,
        ⟨98870, false, false, [36048], [88179, 15]⟩,
        ⟨48898, true, false, [36048, 36047], [15]⟩,
        ⟨98869, false, false, [36048], [87303, 13, 15]⟩,
        ⟨41285, true, false, [36048, 36039], [13, 15]⟩,
        ⟨98868, true, false, [36048], [15, 13, 15]⟩,
        ⟨2022, false, false, [36048, 93399], []⟩,
        ⟨89, false, false, [36048, 93399], []⟩,
        ⟨98861, false, false, [36048], [13]⟩,
        ⟨78833, false, false, [36048], []⟩,
        ⟨78834, false, false, [36048], []⟩,
        ⟨78790, false, false, [36048], []⟩,
        ⟨78790, false, false, [36048], []⟩,
        ⟨98872, false, false, [36048], []⟩,
        ⟨98877, true, false, [], [93395]⟩
      ]⟩,
    ⟨[36049], [36050], .contexts [
        ⟨98873, true, true, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1545. -/
def y322TCIndexRaw1545 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[36023, 84461], [36023, 84461], .contexts []⟩,
    ⟨[36023, 84461], [36023, 84461], .contexts []⟩,
    ⟨[96617, 15], [36023, 84461], .contexts [
        ⟨98844, false, false, [], []⟩,
        ⟨98849, false, false, [], []⟩,
        ⟨98880, false, false, [], []⟩,
        ⟨98881, false, false, [], []⟩,
        ⟨98881, false, false, [], []⟩
      ]⟩,
    ⟨[84459, 15], [84459, 15], .contexts []⟩,
    ⟨[84459, 15], [36025, 96615], .contexts [
        ⟨98883, false, false, [], []⟩,
        ⟨26871, true, false, [], [15]⟩,
        ⟨98882, true, false, [36022], [1, 15]⟩,
        ⟨1666, false, false, [36022, 96617], []⟩,
        ⟨9, false, false, [36022, 96617], []⟩,
        ⟨98575, false, false, [36022], []⟩,
        ⟨98576, false, false, [36022], []⟩,
        ⟨98530, false, false, [36022], []⟩,
        ⟨98530, false, false, [36022], []⟩,
        ⟨98811, true, false, [], [96615]⟩
      ]⟩,
    ⟨[36053], [36023, 22463], .source 18091⟩,
    ⟨[36055], [36053, 36051], .source 18092⟩,
    ⟨[36057], [36054], .source 18093⟩,
    ⟨[36054], [36054], .contexts []⟩,
    ⟨[93395, 7], [36057, 96617], .contexts [
        ⟨98886, false, false, [36054], [93395, 7]⟩,
        ⟨98878, true, false, [36054, 36053], [7]⟩,
        ⟨98885, false, false, [36054], [88179, 15, 7]⟩,
        ⟨48989, true, false, [36054, 36023], [15, 7]⟩,
        ⟨98882, true, false, [36054], [7, 15, 7]⟩,
        ⟨2651, false, false, [36054, 96617], []⟩,
        ⟨98888, true, false, [], [96617]⟩,
        ⟨98888, true, false, [], [96617]⟩,
        ⟨98887, true, false, [], [96617]⟩
      ]⟩,
    ⟨[36045, 90205], [36045, 90205], .contexts []⟩,
    ⟨[36045, 90205], [36045, 90205], .contexts []⟩,
    ⟨[36059], [30087, 36045], .source 18094⟩,
    ⟨[90203, 13], [90203, 13], .contexts []⟩,
    ⟨[36061], [36043, 36059], .source 18095⟩,
    ⟨[90203, 13], [36061, 90203], .contexts [
        ⟨98893, false, false, [], []⟩,
        ⟨59381, true, false, [], [13]⟩,
        ⟨98891, true, false, [36044], [1, 13]⟩,
        ⟨98891, true, false, [36044], [1, 13]⟩,
        ⟨98890, true, false, [36044], [1, 13]⟩,
        ⟨98855, true, false, [36044], [1, 13]⟩,
        ⟨98852, true, false, [36044], [1, 13]⟩,
        ⟨1968, false, false, [36044, 91097], []⟩,
        ⟨248, false, false, [36044, 91097], []⟩,
        ⟨79067, false, false, [36044], [13, 1]⟩,
        ⟨98855, false, false, [36044, 30087], [1]⟩,
        ⟨98892, true, false, [36044], [90205, 1]⟩,
        ⟨59381, false, false, [36044, 36059], []⟩,
        ⟨95579, false, false, [36044, 36059], []⟩,
        ⟨98856, true, false, [], [36059, 90203]⟩,
        ⟨98894, true, false, [], [90203]⟩
      ]⟩,
    ⟨[36051, 93395], [36051, 93395], .contexts []⟩,
    ⟨[36051, 93395], [36051, 93395], .contexts []⟩,
    ⟨[36051, 93393], [36051, 93393], .contexts []⟩,
    ⟨[93393, 15], [93393, 15], .contexts []⟩,
    ⟨[36050], [36050], .contexts []⟩,
    ⟨[36049], [36050], .contexts [
        ⟨98879, false, false, [], []⟩,
        ⟨98900, false, false, [], []⟩,
        ⟨98900, false, false, [], []⟩
      ]⟩,
    ⟨[93393, 15], [36049, 88177], .contexts [
        ⟨98899, false, false, [], []⟩,
        ⟨98898, true, false, [36050], [15]⟩,
        ⟨78787, true, false, [], [15]⟩,
        ⟨98897, true, false, [36050], [1, 15]⟩,
        ⟨98897, true, false, [36050], [1, 15]⟩,
        ⟨98896, true, false, [36050], [1, 15]⟩,
        ⟨98878, true, false, [36050], [1, 15]⟩,
        ⟨98871, true, false, [36050], [1, 15]⟩,
        ⟨1666, false, false, [36050, 88179], []⟩,
        ⟨9, false, false, [36050, 88179], []⟩,
        ⟨48628, false, false, [36050], []⟩,
        ⟨48629, false, false, [36050], []⟩,
        ⟨48567, false, false, [36050], []⟩,
        ⟨48567, false, false, [36050], []⟩,
        ⟨48973, false, false, [36050], []⟩,
        ⟨98901, true, false, [], [88177]⟩
      ]⟩,
    ⟨[88177, 15], [36051, 93393], .contexts [
        ⟨98902, true, false, [36048], [15]⟩,
        ⟨1, false, false, [36048, 93393], []⟩,
        ⟨98873, true, false, [], [93393]⟩
      ]⟩,
    ⟨[36025, 96615], [36025, 96615], .contexts []⟩,
    ⟨[84459, 15], [36025, 96615], .contexts [
        ⟨98883, false, false, [], []⟩,
        ⟨98884, false, false, [], []⟩,
        ⟨98904, false, false, [], []⟩,
        ⟨98904, false, false, [], []⟩
      ]⟩,
    ⟨[36063], [22463, 36051], .source 18096⟩,
    ⟨[96615, 7], [96615, 7], .contexts []⟩,
    ⟨[36065], [36023, 36063], .source 18097⟩,
    ⟨[96615, 7], [36065, 93393], .contexts [
        ⟨98907, false, false, [], []⟩,
        ⟨98905, true, false, [36024], [7]⟩,
        ⟨37, false, false, [36024, 84459], []⟩,
        ⟨40, false, false, [36024, 84459], []⟩,
        ⟨49057, false, false, [36024], [15]⟩,
        ⟨49050, false, false, [36024], [15]⟩,
        ⟨49051, false, false, [36024], [15]⟩,
        ⟨49051, false, false, [36024], [15]⟩,
        ⟨98903, false, false, [36024, 22463], []⟩,
        ⟨98906, true, false, [36024], [93393]⟩,
        ⟨98846, true, false, [], [36063, 93393]⟩,
        ⟨98908, true, false, [], [93393]⟩
      ]⟩,
    ⟨[36067], [36064], .source 18098⟩,
    ⟨[96613, 15], [96613, 15], .contexts []⟩,
    ⟨[96613, 15], [36023, 84457], .contexts [
        ⟨98911, false, false, [], []⟩,
        ⟨98527, true, false, [], [15]⟩,
        ⟨98905, true, false, [36024], [11, 15]⟩,
        ⟨2046, false, false, [36024, 84459], []⟩,
        ⟨54, false, false, [36024, 84459], []⟩,
        ⟨26945, false, false, [36024], []⟩,
        ⟨26946, false, false, [36024], []⟩,
        ⟨26866, false, false, [36024], []⟩,
        ⟨26866, false, false, [36024], []⟩,
        ⟨98848, true, false, [], [84457]⟩
      ]⟩,
    ⟨[36061, 90203], [36061, 90203], .contexts []⟩,
    ⟨[36061, 90203], [36061, 90203], .contexts []⟩,
    ⟨[90199, 15], [90199, 15], .contexts []⟩,
    ⟨[36069], [36060], .source 18099⟩,
    ⟨[36069], [36069], .contexts []⟩,
    ⟨[36069], [36060], .contexts [
        ⟨98917, false, false, [], []⟩,
        ⟨98916, false, false, [], []⟩
      ]⟩,
    ⟨[36060], [36060], .contexts []⟩,
    ⟨[36069], [36060], .contexts [
        ⟨98918, false, false, [], []⟩,
        ⟨98919, false, false, [], []⟩,
        ⟨98919, false, false, [], []⟩
      ]⟩,
    ⟨[90199, 15], [36069, 90199], .contexts [
        ⟨98915, false, false, [], []⟩,
        ⟨59374, true, false, [], [15]⟩,
        ⟨59377, true, false, [], [13, 15]⟩,
        ⟨98914, true, false, [36060], [15, 13, 15]⟩,
        ⟨98914, true, false, [36060], [15, 13, 15]⟩,
        ⟨98913, true, false, [36060], [15, 13, 15]⟩,
        ⟨98895, true, false, [36060], [15, 13, 15]⟩,
        ⟨98893, true, false, [36060], [15, 13, 15]⟩,
        ⟨2022, false, false, [36060, 90203], []⟩,
        ⟨89, false, false, [36060, 90203], []⟩,
        ⟨95589, false, false, [36060], [13]⟩,
        ⟨59428, false, false, [36060], []⟩,
        ⟨59429, false, false, [36060], []⟩,
        ⟨59373, false, false, [36060], []⟩,
        ⟨59373, false, false, [36060], []⟩,
        ⟨95595, false, false, [36060], []⟩,
        ⟨98920, true, false, [], [90199]⟩
      ]⟩,
    ⟨[36049, 88177], [36049, 88177], .contexts []⟩,
    ⟨[88175, 15], [88175, 15], .contexts []⟩,
    ⟨[88175, 15], [36051, 93391], .contexts [
        ⟨98923, false, false, [], []⟩,
        ⟨48565, true, false, [], [15]⟩,
        ⟨98922, true, false, [36048], [11, 15]⟩,
        ⟨98922, true, false, [36048], [11, 15]⟩,
        ⟨98902, true, false, [36048], [11, 15]⟩,
        ⟨98899, true, false, [36048], [11, 15]⟩,
        ⟨2046, false, false, [36048, 93393], []⟩,
        ⟨54, false, false, [36048, 93393], []⟩,
        ⟨78835, false, false, [36048], []⟩,
        ⟨78836, false, false, [36048], []⟩,
        ⟨78782, false, false, [36048], []⟩,
        ⟨78782, false, false, [36048], []⟩,
        ⟨98877, true, false, [], [93391]⟩
      ]⟩,
    ⟨[36065, 93393], [36065, 93393], .contexts []⟩,
    ⟨[93391, 7], [93391, 7], .contexts []⟩,
    ⟨[36064], [36064], .contexts []⟩,
    ⟨[36067], [36064], .contexts [
        ⟨98910, false, false, [], []⟩,
        ⟨98927, false, false, [], []⟩,
        ⟨98927, false, false, [], []⟩
      ]⟩,
    ⟨[93391, 7], [36067, 96613], .contexts [
        ⟨98926, false, false, [], []⟩,
        ⟨78783, true, false, [], [7]⟩,
        ⟨98925, true, false, [36064], [11, 7]⟩,
        ⟨98925, true, false, [36064], [11, 7]⟩,
        ⟨98909, true, false, [36064], [11, 7]⟩,
        ⟨98907, true, false, [36064], [11, 7]⟩,
        ⟨555, false, false, [36064, 96615], []⟩,
        ⟨54, false, false, [36064, 96615], []⟩,
        ⟨98577, false, false, [36064], []⟩,
        ⟨98578, false, false, [36064], []⟩,
        ⟨98526, false, false, [36064], []⟩,
        ⟨98526, false, false, [36064], []⟩,
        ⟨98928, true, false, [], [96613]⟩
      ]⟩,
    ⟨[36065], [36066], .contexts [
        ⟨98910, true, true, [], []⟩
      ]⟩,
    ⟨[36023, 84457], [36023, 84457], .contexts []⟩,
    ⟨[36023, 84457], [36023, 84457], .contexts []⟩,
    ⟨[36023, 84455], [36023, 84455], .contexts []⟩,
    ⟨[84455, 15], [84455, 15], .contexts []⟩,
    ⟨[84455, 15], [36025, 96611], .contexts [
        ⟨98934, false, false, [], []⟩,
        ⟨98933, true, false, [36022], [15]⟩,
        ⟨26863, true, false, [], [15]⟩,
        ⟨98932, true, false, [36022], [9, 15]⟩,
        ⟨98932, true, false, [36022], [9, 15]⟩,
        ⟨98931, true, false, [36022], [9, 15]⟩,
        ⟨98912, true, false, [36022], [9, 15]⟩,
        ⟨98911, true, false, [36022], [9, 15]⟩,
        ⟨1671, false, false, [36022, 96613], []⟩,
        ⟨47, false, false, [36022, 96613], []⟩,
        ⟨98580, false, false, [36022], []⟩,
        ⟨98581, false, false, [36022], []⟩,
        ⟨98523, false, false, [36022], []⟩,
        ⟨98523, false, false, [36022], []⟩,
        ⟨98811, true, false, [], [96611]⟩
      ]⟩,
    ⟨[36069, 90199], [36069, 90199], .contexts []⟩,
    ⟨[90197, 15], [90197, 15], .contexts []⟩,
    ⟨[36068], [36068], .contexts []⟩,
    ⟨[36061], [36068], .contexts [
        ⟨98916, true, true, [], []⟩,
        ⟨98938, false, false, [], []⟩,
        ⟨98938, false, false, [], []⟩
      ]⟩,
    ⟨[90197, 15], [36061, 90197], .contexts [
        ⟨98937, false, false, [], []⟩,
        ⟨59371, true, false, [], [15]⟩,
        ⟨98936, true, false, [36068], [1, 15]⟩,
        ⟨98936, true, false, [36068], [1, 15]⟩,
        ⟨98921, true, false, [36068], [1, 15]⟩,
        ⟨98915, true, false, [36068], [1, 15]⟩,
        ⟨1666, false, false, [36068, 90199], []⟩,
        ⟨95599, false, false, [36068], []⟩,
        ⟨95598, false, false, [36068], []⟩,
        ⟨95601, false, false, [36068], []⟩,
        ⟨98939, true, false, [], [90197]⟩
      ]⟩,
    ⟨[36051, 93391], [36051, 93391], .contexts []⟩,
    ⟨[36051, 93391], [36051, 93391], .contexts []⟩,
    ⟨[36051, 93389], [36051, 93389], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1546. -/
def y322TCIndexRaw1546 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93389, 15], [93389, 15], .contexts []⟩,
    ⟨[93389, 15], [36049, 88173], .contexts [
        ⟨98944, false, false, [], []⟩,
        ⟨98943, true, false, [36050], [15]⟩,
        ⟨78780, true, false, [], [15]⟩,
        ⟨98942, true, false, [36050], [9, 15]⟩,
        ⟨98942, true, false, [36050], [9, 15]⟩,
        ⟨98941, true, false, [36050], [9, 15]⟩,
        ⟨98924, true, false, [36050], [9, 15]⟩,
        ⟨98923, true, false, [36050], [9, 15]⟩,
        ⟨1671, false, false, [36050, 88175], []⟩,
        ⟨49092, false, false, [36050], []⟩,
        ⟨49091, false, false, [36050], []⟩,
        ⟨49093, false, false, [36050], []⟩,
        ⟨98901, true, false, [], [88173]⟩
      ]⟩,
    ⟨[36067, 96613], [36067, 96613], .contexts []⟩,
    ⟨[36067, 96613], [36067, 96613], .contexts []⟩,
    ⟨[36067, 96611], [36067, 96611], .contexts []⟩,
    ⟨[96611, 7], [96611, 7], .contexts []⟩,
    ⟨[36066], [36066], .contexts []⟩,
    ⟨[96611, 7], [36065, 93389], .contexts [
        ⟨98949, false, false, [], []⟩,
        ⟨98948, true, false, [36066], [7]⟩,
        ⟨98524, true, false, [], [7]⟩,
        ⟨98947, true, false, [36066], [9, 7]⟩,
        ⟨98947, true, false, [36066], [9, 7]⟩,
        ⟨98946, true, false, [36066], [9, 7]⟩,
        ⟨98929, true, false, [36066], [9, 7]⟩,
        ⟨98926, true, false, [36066], [9, 7]⟩,
        ⟨579, false, false, [36066, 93391], []⟩,
        ⟨47, false, false, [36066, 93391], []⟩,
        ⟨78838, false, false, [36066], []⟩,
        ⟨78839, false, false, [36066], []⟩,
        ⟨78779, false, false, [36066], []⟩,
        ⟨78779, false, false, [36066], []⟩,
        ⟨98950, true, false, [], [93389]⟩,
        ⟨98950, true, false, [], [93389]⟩,
        ⟨98930, true, false, [], [93389]⟩
      ]⟩,
    ⟨[36025, 96611], [36025, 96611], .contexts []⟩,
    ⟨[96609, 15], [96609, 15], .contexts []⟩,
    ⟨[84453], [84453], .contexts []⟩,
    ⟨[96609, 15], [36023, 84453], .contexts [
        ⟨98953, false, false, [], []⟩,
        ⟨98521, true, false, [], [15]⟩,
        ⟨98952, true, false, [36024], [1, 15]⟩,
        ⟨98952, true, false, [36024], [1, 15]⟩,
        ⟨98935, true, false, [36024], [1, 15]⟩,
        ⟨98934, true, false, [36024], [1, 15]⟩,
        ⟨1666, false, false, [36024, 84455], []⟩,
        ⟨9, false, false, [36024, 84455], []⟩,
        ⟨26949, false, false, [36024], []⟩,
        ⟨26950, false, false, [36024], []⟩,
        ⟨26858, false, false, [36024], []⟩,
        ⟨26858, false, false, [36024], []⟩,
        ⟨98954, false, false, [36024], []⟩,
        ⟨98848, true, false, [], [84453]⟩
      ]⟩,
    ⟨[84453, 15], [36025, 96609], .contexts [
        ⟨98955, true, false, [36022], [15]⟩,
        ⟨1, false, false, [36022, 96609], []⟩,
        ⟨98808, true, false, [], [96609]⟩
      ]⟩,
    ⟨[36061, 90197], [36061, 90197], .contexts []⟩,
    ⟨[90195, 15], [90195, 15], .contexts []⟩,
    ⟨[36049, 88173], [36049, 88173], .contexts []⟩,
    ⟨[36049, 88171], [36049, 88171], .contexts []⟩,
    ⟨[88171, 15], [88171, 15], .contexts []⟩,
    ⟨[88171, 15], [36051, 93387], .contexts [
        ⟨98961, false, false, [], []⟩,
        ⟨98960, true, false, [36048], [15]⟩,
        ⟨48559, true, false, [], [15]⟩,
        ⟨98959, true, false, [36048], [1, 15]⟩,
        ⟨98959, true, false, [36048], [1, 15]⟩,
        ⟨98945, true, false, [36048], [1, 15]⟩,
        ⟨98944, true, false, [36048], [1, 15]⟩,
        ⟨1666, false, false, [36048, 93389], []⟩,
        ⟨9, false, false, [36048, 93389], []⟩,
        ⟨78840, false, false, [36048], []⟩,
        ⟨78841, false, false, [36048], []⟩,
        ⟨78776, false, false, [36048], []⟩,
        ⟨78776, false, false, [36048], []⟩,
        ⟨98877, true, false, [], [93387]⟩
      ]⟩,
    ⟨[36065, 93389], [36065, 93389], .contexts []⟩,
    ⟨[36065, 93387], [36065, 93387], .contexts []⟩,
    ⟨[36023, 84453], [36023, 84453], .contexts []⟩,
    ⟨[36023, 84451], [36023, 84451], .contexts []⟩,
    ⟨[84451, 15], [84451, 15], .contexts []⟩,
    ⟨[84451, 15], [36025, 96607], .contexts [
        ⟨98967, false, false, [], []⟩,
        ⟨98966, true, false, [36022], [15]⟩,
        ⟨26855, true, false, [], [15]⟩,
        ⟨98965, true, false, [36022], [5, 15]⟩,
        ⟨98965, true, false, [36022], [5, 15]⟩,
        ⟨98955, true, false, [36022], [5, 15]⟩,
        ⟨98953, true, false, [36022], [5, 15]⟩,
        ⟨2072, false, false, [36022, 96609], []⟩,
        ⟨29, false, false, [36022, 96609], []⟩,
        ⟨98584, false, false, [36022], []⟩,
        ⟨98585, false, false, [36022], []⟩,
        ⟨98517, false, false, [36022], []⟩,
        ⟨98517, false, false, [36022], []⟩,
        ⟨98811, true, false, [], [96607]⟩
      ]⟩,
    ⟨[36069, 90195], [36069, 90195], .contexts []⟩,
    ⟨[90195, 15], [36069, 90195], .contexts [
        ⟨98958, false, false, [], []⟩,
        ⟨98958, false, false, [], []⟩,
        ⟨59368, true, false, [], [15]⟩,
        ⟨98957, true, false, [36060], [11, 15]⟩,
        ⟨98957, true, false, [36060], [11, 15]⟩,
        ⟨98940, true, false, [36060], [11, 15]⟩,
        ⟨98937, true, false, [36060], [11, 15]⟩,
        ⟨2046, false, false, [36060, 90197], []⟩,
        ⟨95604, false, false, [36060], []⟩,
        ⟨95603, false, false, [36060], []⟩,
        ⟨95607, false, false, [36060], []⟩,
        ⟨98920, true, false, [], [90195]⟩,
        ⟨98969, false, false, [], []⟩,
        ⟨98969, false, false, [], []⟩
      ]⟩,
    ⟨[90193, 15], [90193, 15], .contexts []⟩,
    ⟨[90193, 15], [36061, 90193], .contexts [
        ⟨98971, false, false, [], []⟩,
        ⟨59365, true, false, [], [15]⟩,
        ⟨98970, true, false, [36068], [9, 15]⟩,
        ⟨1671, false, false, [36068, 90195], []⟩,
        ⟨95610, false, false, [36068], []⟩,
        ⟨95609, false, false, [36068], []⟩,
        ⟨95612, false, false, [36068], []⟩,
        ⟨98939, true, false, [], [90193]⟩
      ]⟩,
    ⟨[36051, 93387], [36051, 93387], .contexts []⟩,
    ⟨[36051, 93385], [36051, 93385], .contexts []⟩,
    ⟨[93385, 15], [93385, 15], .contexts []⟩,
    ⟨[93385, 15], [36049, 88169], .contexts [
        ⟨98975, false, false, [], []⟩,
        ⟨98974, true, false, [36050], [15]⟩,
        ⟨78774, true, false, [], [15]⟩,
        ⟨98973, true, false, [36050], [5, 15]⟩,
        ⟨98973, true, false, [36050], [5, 15]⟩,
        ⟨98962, true, false, [36050], [5, 15]⟩,
        ⟨98961, true, false, [36050], [5, 15]⟩,
        ⟨2072, false, false, [36050, 88171], []⟩,
        ⟨29, false, false, [36050, 88171], []⟩,
        ⟨48637, false, false, [36050], []⟩,
        ⟨48638, false, false, [36050], []⟩,
        ⟨48555, false, false, [36050], []⟩,
        ⟨48555, false, false, [36050], []⟩,
        ⟨98901, true, false, [], [88169]⟩
      ]⟩,
    ⟨[36025, 96607], [36025, 96607], .contexts []⟩,
    ⟨[36025, 96605], [36025, 96605], .contexts []⟩,
    ⟨[96605, 15], [96605, 15], .contexts []⟩,
    ⟨[96605, 15], [36023, 84449], .contexts [
        ⟨98979, false, false, [], []⟩,
        ⟨98978, true, false, [36024], [15]⟩,
        ⟨98515, true, false, [], [15]⟩,
        ⟨98977, true, false, [36024], [3, 15]⟩,
        ⟨98977, true, false, [36024], [3, 15]⟩,
        ⟨98968, true, false, [36024], [3, 15]⟩,
        ⟨98967, true, false, [36024], [3, 15]⟩,
        ⟨1141, false, false, [36024, 84451], []⟩,
        ⟨21, false, false, [36024, 84451], []⟩,
        ⟨26952, false, false, [36024], []⟩,
        ⟨26953, false, false, [36024], []⟩,
        ⟨26850, false, false, [36024], []⟩,
        ⟨26850, false, false, [36024], []⟩,
        ⟨98848, true, false, [], [84449]⟩
      ]⟩,
    ⟨[36061, 90193], [36061, 90193], .contexts []⟩,
    ⟨[36061, 90193], [36061, 90193], .contexts []⟩,
    ⟨[90191, 15], [90191, 15], .contexts []⟩,
    ⟨[90191, 15], [36069, 90191], .contexts [
        ⟨98983, false, false, [], []⟩,
        ⟨59361, true, false, [], [15]⟩,
        ⟨98982, true, false, [36060], [1, 15]⟩,
        ⟨98982, true, false, [36060], [1, 15]⟩,
        ⟨98981, true, false, [36060], [1, 15]⟩,
        ⟨98972, true, false, [36060], [1, 15]⟩,
        ⟨98971, true, false, [36060], [1, 15]⟩,
        ⟨1666, false, false, [36060, 90193], []⟩,
        ⟨95617, false, false, [36060], []⟩,
        ⟨95616, false, false, [36060], []⟩,
        ⟨95618, false, false, [36060], []⟩,
        ⟨98920, true, false, [], [90191]⟩
      ]⟩,
    ⟨[36049, 88169], [36049, 88169], .contexts []⟩,
    ⟨[36049, 88167], [36049, 88167], .contexts []⟩,
    ⟨[88167, 15], [88167, 15], .contexts []⟩,
    ⟨[88167, 15], [36051, 93383], .contexts [
        ⟨98987, false, false, [], []⟩,
        ⟨98986, true, false, [36048], [15]⟩,
        ⟨48553, true, false, [], [15]⟩,
        ⟨98985, true, false, [36048], [3, 15]⟩,
        ⟨98985, true, false, [36048], [3, 15]⟩,
        ⟨98976, true, false, [36048], [3, 15]⟩,
        ⟨98975, true, false, [36048], [3, 15]⟩,
        ⟨1141, false, false, [36048, 93385], []⟩,
        ⟨21, false, false, [36048, 93385], []⟩,
        ⟨78842, false, false, [36048], []⟩,
        ⟨78843, false, false, [36048], []⟩,
        ⟨78770, false, false, [36048], []⟩,
        ⟨78770, false, false, [36048], []⟩,
        ⟨98877, true, false, [], [93383]⟩
      ]⟩,
    ⟨[36023, 84449], [36023, 84449], .contexts []⟩,
    ⟨[36023, 84447], [36023, 84447], .contexts []⟩,
    ⟨[36023, 84447], [36023, 84447], .contexts []⟩,
    ⟨[36023, 84447], [36023, 84447], .contexts []⟩,
    ⟨[36023, 84445], [36023, 84445], .contexts []⟩,
    ⟨[36023, 84445], [36023, 84445], .contexts []⟩,
    ⟨[84445, 1], [36025, 96605], .contexts [
        ⟨98994, true, false, [36022], [1]⟩,
        ⟨98993, true, false, [36022], [1]⟩,
        ⟨26843, true, false, [], [1]⟩,
        ⟨98992, true, false, [36022], [15, 1]⟩,
        ⟨98991, true, false, [36022], [15, 1]⟩,
        ⟨98990, true, false, [36022], [15, 1]⟩,
        ⟨26847, true, false, [], [15, 1]⟩,
        ⟨98989, true, false, [36022], [1, 15, 1]⟩,
        ⟨98989, true, false, [36022], [1, 15, 1]⟩,
        ⟨98980, true, false, [36022], [1, 15, 1]⟩,
        ⟨98979, true, false, [36022], [1, 15, 1]⟩,
        ⟨504, false, false, [36022, 96605], []⟩,
        ⟨98811, true, false, [], [96605]⟩
      ]⟩,
    ⟨[36023], [36023], .contexts []⟩,
    ⟨[36023], [36023], .contexts []⟩,
    ⟨[96601], [36023, 84447], .contexts [
        ⟨98809, false, false, [36024], [96601]⟩,
        ⟨13, false, false, [36024, 36022], [96601]⟩,
        ⟨98589, true, false, [36024, 36022], []⟩,
        ⟨98510, true, false, [36024, 36022], []⟩,
        ⟨98512, true, false, [36024, 36022], [15]⟩,
        ⟨98512, true, false, [36024, 36022], [15]⟩,
        ⟨98587, true, false, [36024, 36022], [15]⟩,
        ⟨98586, true, false, [36024, 36022], [15]⟩,
        ⟨98995, true, false, [36024, 36022, 36024], [1, 15]⟩,
        ⟨8, false, false, [36024, 36022, 36024, 84445], [15]⟩,
        ⟨98813, true, false, [36024, 36022], [84445, 15]⟩,
        ⟨98993, false, false, [36024, 36022], [15]⟩,
        ⟨98997, true, false, [36024, 36022], [84445, 15]⟩,
        ⟨98996, true, false, [36024, 36022], [84445, 15]⟩,
        ⟨98845, true, false, [36024, 36022], [84445, 15]⟩,
        ⟨98994, false, false, [36024, 36022], [15]⟩,
        ⟨26841, false, false, [36024], []⟩,
        ⟨98990, false, false, [36024, 36022], []⟩,
        ⟨98991, false, false, [36024, 36022], []⟩,
        ⟨98992, false, false, [36024, 36022], []⟩,
        ⟨98813, true, false, [], [84447]⟩
      ]⟩,
    ⟨[84447, 13], [36025, 96599], .contexts [
        ⟨98998, true, false, [36022], [13]⟩,
        ⟨98507, false, false, [36022], []⟩,
        ⟨98590, false, false, [36022], []⟩,
        ⟨98810, true, false, [], [96599]⟩,
        ⟨98810, true, false, [], [96599]⟩,
        ⟨98809, true, false, [], [96599]⟩
      ]⟩,
    ⟨[36069, 90191], [36069, 90191], .contexts []⟩,
    ⟨[36069, 90191], [36069, 90191], .contexts []⟩,
    ⟨[90189, 15], [90189, 15], .contexts []⟩,
    ⟨[36051, 93383], [36051, 93383], .contexts []⟩,
    ⟨[36051, 93379], [36051, 93379], .contexts []⟩,
    ⟨[93379, 1], [36049, 88167], .contexts [
        ⟨99004, true, false, [36050], [1]⟩,
        ⟨78765, true, false, [], [1]⟩,
        ⟨78768, true, false, [], [15, 1]⟩,
        ⟨99003, true, false, [36050], [1, 15, 1]⟩,
        ⟨99003, true, false, [36050], [1, 15, 1]⟩,
        ⟨98988, true, false, [36050], [1, 15, 1]⟩,
        ⟨98987, true, false, [36050], [1, 15, 1]⟩,
        ⟨504, false, false, [36050, 88167], []⟩,
        ⟨98901, true, false, [], [88167]⟩
      ]⟩,
    ⟨[36051], [36051], .contexts []⟩,
    ⟨[36051], [36051], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1547. -/
def y322TCIndexRaw1547 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93379], [36049, 88165], .contexts [
        ⟨98874, false, false, [36050], [93379]⟩,
        ⟨99006, false, false, [36050], [93379]⟩,
        ⟨99007, false, false, [36050], [93379]⟩,
        ⟨99004, true, false, [36050], []⟩,
        ⟨98873, false, false, [36050], [93379]⟩,
        ⟨8, true, false, [36050, 36048, 93379], []⟩,
        ⟨99005, false, false, [36050, 36048], [1]⟩,
        ⟨48639, false, false, [36050], []⟩,
        ⟨48640, false, false, [36050], []⟩,
        ⟨48549, false, false, [36050], []⟩,
        ⟨48549, false, false, [36050], []⟩,
        ⟨98879, true, false, [], [88165]⟩
      ]⟩,
    ⟨[36061, 90189], [36061, 90189], .contexts []⟩,
    ⟨[90189, 15], [36061, 90189], .contexts [
        ⟨99002, false, false, [], []⟩,
        ⟨99002, false, false, [], []⟩,
        ⟨59357, true, false, [], [15]⟩,
        ⟨99001, true, false, [36068], [5, 15]⟩,
        ⟨99001, true, false, [36068], [5, 15]⟩,
        ⟨99000, true, false, [36068], [5, 15]⟩,
        ⟨98984, true, false, [36068], [5, 15]⟩,
        ⟨98983, true, false, [36068], [5, 15]⟩,
        ⟨2072, false, false, [36068, 90191], []⟩,
        ⟨29, false, false, [36068, 90191], []⟩,
        ⟨59439, false, false, [36068], []⟩,
        ⟨59440, false, false, [36068], []⟩,
        ⟨59356, false, false, [36068], []⟩,
        ⟨59356, false, false, [36068], []⟩,
        ⟨98939, true, false, [], [90189]⟩,
        ⟨99009, false, false, [], []⟩,
        ⟨99009, false, false, [], []⟩
      ]⟩,
    ⟨[36061, 90187], [36061, 90187], .contexts []⟩,
    ⟨[36061, 90187], [36061, 90187], .contexts []⟩,
    ⟨[90187, 15], [90187, 15], .contexts []⟩,
    ⟨[90187], [90187], .contexts []⟩,
    ⟨[36069, 90187], [36069, 90187], .contexts []⟩,
    ⟨[90187, 15, 1], [36069, 90185], .contexts [
        ⟨99013, false, false, [], [1]⟩,
        ⟨99013, false, false, [], [1]⟩,
        ⟨99012, true, false, [36060], [15, 1]⟩,
        ⟨99011, true, false, [36060], [15, 1]⟩,
        ⟨59353, true, false, [], [15, 1]⟩,
        ⟨99010, true, false, [36060], [3, 15, 1]⟩,
        ⟨1141, false, false, [36060, 90189], [1]⟩,
        ⟨21, false, false, [36060, 90189], [1]⟩,
        ⟨59441, false, false, [36060], [1]⟩,
        ⟨59442, false, false, [36060], [1]⟩,
        ⟨59352, false, false, [36060], [1]⟩,
        ⟨59352, false, false, [36060], [1]⟩,
        ⟨99014, false, false, [36060], [1]⟩,
        ⟨98920, true, false, [], [90187, 1]⟩,
        ⟨99015, false, false, [], [1]⟩,
        ⟨99015, false, false, [], [1]⟩,
        ⟨59349, false, false, [36069], []⟩
      ]⟩,
    ⟨[36069, 90183], [36069, 90183], .contexts []⟩,
    ⟨[36069, 90183], [36069, 90183], .contexts []⟩,
    ⟨[90183, 1], [36061, 90187], .contexts [
        ⟨99018, true, false, [36068], [1]⟩,
        ⟨99017, true, false, [36068], [1]⟩,
        ⟨59346, true, false, [], [1]⟩,
        ⟨99016, true, false, [36068], [15, 1]⟩,
        ⟨504, false, false, [36068, 90187], []⟩,
        ⟨99014, false, false, [36068], []⟩,
        ⟨98939, true, false, [], [90187]⟩
      ]⟩,
    ⟨[36069], [36069], .contexts []⟩,
    ⟨[36069], [36069], .contexts []⟩,
    ⟨[96637], [83381, 13], .source 48383⟩,
    ⟨[83381, 13], [96637], .contexts [
        ⟨99022, true, false, [], []⟩
      ]⟩,
    ⟨[96637, 13], [83381], .contexts [
        ⟨99023, true, false, [], [13]⟩,
        ⟨59, false, false, [83381], []⟩,
        ⟨21113, false, false, [], []⟩
      ]⟩,
    ⟨[96637], [96637], .contexts []⟩,
    ⟨[96637], [96637], .contexts []⟩,
    ⟨[83381, 13], [96637], .contexts [
        ⟨99023, false, false, [], []⟩,
        ⟨99025, false, false, [], []⟩,
        ⟨99026, false, false, [], []⟩,
        ⟨99026, false, false, [], []⟩
      ]⟩,
    ⟨[36071], [16219, 25535], .source 18100⟩,
    ⟨[96637, 3], [96637, 3], .contexts []⟩,
    ⟨[96637, 3], [36071, 83015], .contexts [
        ⟨99029, false, false, [], []⟩,
        ⟨99027, true, false, [], [3]⟩,
        ⟨63, false, false, [83381], []⟩,
        ⟨65, false, false, [83381], []⟩,
        ⟨21118, false, false, [], [13]⟩,
        ⟨21120, false, false, [], [13]⟩,
        ⟨21116, false, false, [], [13]⟩,
        ⟨21117, false, false, [], [13]⟩,
        ⟨21117, false, false, [], [13]⟩,
        ⟨62824, false, false, [16219], []⟩,
        ⟨99028, true, false, [], [83015]⟩,
        ⟨62822, false, false, [36071], []⟩,
        ⟨13, true, false, [], [36071, 83015]⟩
      ]⟩,
    ⟨[36073], [36070], .source 18101⟩,
    ⟨[83015, 3], [36073, 96637], .contexts [
        ⟨99030, true, false, [36070], [3]⟩,
        ⟨20, false, false, [36070, 96637], []⟩,
        ⟨99031, true, false, [], [96637]⟩
      ]⟩,
    ⟨[96637, 9], [96637, 9], .contexts []⟩,
    ⟨[96637, 9], [88347], .contexts [
        ⟨99033, false, false, [], []⟩,
        ⟨99027, true, false, [], [9]⟩,
        ⟨77, false, false, [83381], []⟩,
        ⟨78, false, false, [83381], []⟩,
        ⟨48309, false, false, [], [13]⟩,
        ⟨32893, false, false, [], [13]⟩,
        ⟨32894, false, false, [], [13]⟩,
        ⟨32894, false, false, [], [13]⟩,
        ⟨50032, false, false, [], []⟩,
        ⟨50033, false, false, [], []⟩,
        ⟨50034, false, false, [], []⟩,
        ⟨50034, false, false, [], []⟩,
        ⟨67807, false, false, [], []⟩,
        ⟨672, true, false, [], [88347]⟩
      ]⟩,
    ⟨[88347, 9], [96637], .contexts [
        ⟨99034, true, false, [], [9]⟩,
        ⟨46, false, false, [96637], []⟩,
        ⟨99026, false, false, [], []⟩
      ]⟩,
    ⟨[96637, 11], [96637, 11], .contexts []⟩,
    ⟨[96637, 11], [32899, 95361], .contexts [
        ⟨99036, false, false, [], []⟩,
        ⟨99027, true, false, [], [11]⟩,
        ⟨82, false, false, [83381], []⟩,
        ⟨83, false, false, [83381], []⟩,
        ⟨21110, false, false, [], [13]⟩,
        ⟨21100, false, false, [], [13]⟩,
        ⟨21101, false, false, [], [13]⟩,
        ⟨21101, false, false, [], [13]⟩,
        ⟨89795, false, false, [], []⟩,
        ⟨89796, false, false, [], []⟩,
        ⟨89797, false, false, [], []⟩,
        ⟨89797, false, false, [], []⟩,
        ⟨89789, false, false, [32899], []⟩,
        ⟨97416, true, false, [], [95361]⟩
      ]⟩,
    ⟨[36071, 83015], [36071, 83015], .contexts []⟩,
    ⟨[36071, 83015], [36071, 83015], .contexts []⟩,
    ⟨[96637, 3], [36071, 83015], .contexts [
        ⟨99029, false, false, [], []⟩,
        ⟨99030, false, false, [], []⟩,
        ⟨99038, false, false, [], []⟩,
        ⟨99039, false, false, [], []⟩,
        ⟨99039, false, false, [], []⟩
      ]⟩,
    ⟨[36075], [36071, 30723], .source 18102⟩,
    ⟨[36077], [36075, 32959], .source 18103⟩,
    ⟨[3, 1, 3, 1, 3, 1], [], .contexts [
        ⟨129, false, false, [], []⟩
      ]⟩,
    ⟨[96637], [96637], .contexts []⟩,
    ⟨[36077, 95357, 1], [96637], .contexts [
        ⟨99042, false, false, [], [95357, 1]⟩,
        ⟨89836, true, false, [36075], [1]⟩,
        ⟨99041, false, false, [], [93785, 3, 1]⟩,
        ⟨81287, true, false, [36071], [3, 1]⟩,
        ⟨18421, true, false, [36071], [1, 3, 1]⟩,
        ⟨18417, true, false, [36071], [3, 1, 3, 1]⟩,
        ⟨99040, true, false, [], [1, 3, 1, 3, 1]⟩,
        ⟨99043, false, false, [96637], []⟩,
        ⟨99044, false, false, [], []⟩
      ]⟩,
    ⟨[96637], [96637], .contexts []⟩,
    ⟨[36079], [36076], .source 18104⟩,
    ⟨[36079], [36076], .contexts [
        ⟨99047, false, false, [], []⟩
      ]⟩,
    ⟨[36076], [36076], .contexts []⟩,
    ⟨[95357, 1], [36079, 96637], .contexts [
        ⟨99045, false, false, [36076], []⟩,
        ⟨99046, false, false, [36076], []⟩,
        ⟨99049, true, false, [], [96637]⟩,
        ⟨99049, true, false, [], [96637]⟩,
        ⟨99048, true, false, [], [96637]⟩
      ]⟩,
    ⟨[96637, 1], [36077, 95357], .contexts [
        ⟨99050, true, false, [36078], [1]⟩,
        ⟨8, false, false, [36078, 95357], []⟩,
        ⟨99047, false, true, [], [95357]⟩
      ]⟩,
    ⟨[36081], [36071, 26871], .source 18105⟩,
    ⟨[36083], [36080], .source 18106⟩,
    ⟨[36080], [36080], .contexts []⟩,
    ⟨[86623, 15], [36083, 96637], .contexts [
        ⟨99052, false, false, [36080], [86623, 15]⟩,
        ⟨68486, true, false, [36080, 36071], [15]⟩,
        ⟨18415, true, false, [36080, 36071], [3, 15]⟩,
        ⟨99040, true, false, [36080], [15, 3, 15]⟩,
        ⟨1659, false, false, [36080, 96637], []⟩,
        ⟨99044, false, false, [36080], []⟩,
        ⟨99046, false, false, [36080], []⟩,
        ⟨99054, true, false, [], [96637]⟩,
        ⟨99054, true, false, [], [96637]⟩,
        ⟨99053, true, false, [], [96637]⟩
      ]⟩,
    ⟨[96639], [85917, 5], .source 48384⟩,
    ⟨[85917, 5], [96639], .contexts [
        ⟨99056, true, false, [], []⟩
      ]⟩,
    ⟨[96639, 5], [85917], .contexts [
        ⟨99057, true, false, [], [5]⟩,
        ⟨28, false, false, [85917], []⟩,
        ⟨34199, false, false, [], []⟩
      ]⟩,
    ⟨[96639], [96639], .contexts []⟩,
    ⟨[85917, 5], [96639], .contexts [
        ⟨99057, false, false, [], []⟩,
        ⟨99059, false, false, [], []⟩,
        ⟨99059, false, false, [], []⟩
      ]⟩,
    ⟨[36085], [30733, 30721], .source 18107⟩,
    ⟨[96639, 15], [96639, 15], .contexts []⟩,
    ⟨[83023], [83023], .contexts []⟩,
    ⟨[36085], [36085], .contexts [
        ⟨13, false, false, [], [36085]⟩
      ]⟩,
    ⟨[96639, 15], [36085, 83023], .contexts [
        ⟨99062, false, false, [], []⟩,
        ⟨99060, true, false, [], [15]⟩,
        ⟨184, false, false, [85917], []⟩,
        ⟨185, false, false, [85917], []⟩,
        ⟨81346, false, false, [], [5]⟩,
        ⟨81336, false, false, [30733], []⟩,
        ⟨99061, true, false, [], [83023]⟩,
        ⟨99063, false, false, [36085], []⟩,
        ⟨99064, true, false, [], [83023]⟩
      ]⟩,
    ⟨[36087], [36084], .source 18108⟩,
    ⟨[83023, 15], [36087, 96639], .contexts [
        ⟨99065, true, false, [36084], [15]⟩,
        ⟨1, false, false, [36084, 96639], []⟩,
        ⟨99066, true, false, [], [96639]⟩
      ]⟩,
    ⟨[96641], [96639, 1], .source 48385⟩,
    ⟨[96639, 1], [96641], .contexts [
        ⟨99068, true, false, [], []⟩
      ]⟩,
    ⟨[96639, 1], [96641], .contexts [
        ⟨99069, false, false, [], []⟩
      ]⟩,
    ⟨[96641], [96641], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1548. -/
def y322TCIndexRaw1548 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[96641], [96641], .contexts []⟩,
    ⟨[36085, 83023], [36085, 83023], .contexts []⟩,
    ⟨[36085, 83021], [36085, 83021], .contexts []⟩,
    ⟨[36085, 83021], [36085, 83021], .contexts []⟩,
    ⟨[96641, 15], [96641, 15], .contexts []⟩,
    ⟨[96641, 15], [36085, 83021], .contexts [
        ⟨99076, false, false, [], []⟩,
        ⟨99072, true, false, [], [15]⟩,
        ⟨99072, true, false, [], [15]⟩,
        ⟨99071, true, false, [], [15]⟩,
        ⟨99070, true, false, [], [15]⟩,
        ⟨121, false, false, [96639], []⟩,
        ⟨122, false, false, [96639], []⟩,
        ⟨99062, false, false, [], [1]⟩,
        ⟨99065, false, false, [], [1]⟩,
        ⟨99073, false, false, [], [1]⟩,
        ⟨99073, false, false, [], [1]⟩,
        ⟨18431, false, false, [36085], []⟩,
        ⟨99074, false, false, [], []⟩,
        ⟨99075, false, false, [], []⟩,
        ⟨99064, true, false, [], [83021]⟩
      ]⟩,
    ⟨[83021, 15], [36087, 96641], .contexts [
        ⟨99077, true, false, [36084], [15]⟩,
        ⟨1, false, false, [36084, 96641], []⟩,
        ⟨99066, true, false, [], [96641]⟩
      ]⟩,
    ⟨[36089], [36085, 25539], .source 18109⟩,
    ⟨[36091], [36089, 22999], .source 18110⟩,
    ⟨[36093], [36091, 25541], .source 18111⟩,
    ⟨[36095], [36093, 36087], .source 18112⟩,
    ⟨[96641, 15, 13, 15, 13, 15], [36095, 96641], .contexts [
        ⟨99076, false, false, [], [13, 15, 13, 15]⟩,
        ⟨99077, false, false, [], [13, 15, 13, 15]⟩,
        ⟨99074, false, false, [], [13, 15, 13, 15]⟩,
        ⟨99075, false, false, [], [13, 15, 13, 15]⟩,
        ⟨99075, false, false, [], [13, 15, 13, 15]⟩,
        ⟨62886, false, false, [36085], [15, 13, 15]⟩,
        ⟨99079, true, false, [], [82895, 15, 13, 15]⟩,
        ⟨51570, false, false, [36089], [13, 15]⟩,
        ⟨99080, true, false, [], [82895, 13, 15]⟩,
        ⟨62887, false, false, [36091], [15]⟩,
        ⟨99081, true, false, [], [83021, 15]⟩,
        ⟨99078, false, false, [36093], []⟩,
        ⟨99082, true, false, [], [96641]⟩
      ]⟩,
    ⟨[96641, 13], [96641, 13], .contexts []⟩,
    ⟨[96641], [96641], .contexts []⟩,
    ⟨[36097], [36094], .source 18113⟩,
    ⟨[36094], [36094], .contexts []⟩,
    ⟨[96641, 13], [36097, 96641], .contexts [
        ⟨99084, false, false, [], []⟩,
        ⟨99083, true, false, [36094], [13]⟩,
        ⟨2137, false, false, [36094, 96641], []⟩,
        ⟨99085, false, false, [36094], []⟩,
        ⟨99087, true, false, [], [96641]⟩,
        ⟨99087, true, false, [], [96641]⟩,
        ⟨99086, true, false, [], [96641]⟩
      ]⟩,
    ⟨[96643], [96641, 9], .source 48386⟩,
    ⟨[96641, 9], [96643], .contexts [
        ⟨99089, true, false, [], []⟩
      ]⟩,
    ⟨[96643, 9], [96641], .contexts [
        ⟨99090, true, false, [], [9]⟩,
        ⟨46, false, false, [96641], []⟩,
        ⟨99072, false, false, [], []⟩
      ]⟩,
    ⟨[96643], [96643], .contexts []⟩,
    ⟨[96643], [96643], .contexts []⟩,
    ⟨[36097, 96641], [36097, 96641], .contexts []⟩,
    ⟨[36097, 96641], [36097, 96641], .contexts []⟩,
    ⟨[36097, 96643], [36097, 96643], .contexts []⟩,
    ⟨[36097, 96643], [36097, 96643], .contexts []⟩,
    ⟨[36097, 96643], [36097, 96643], .contexts []⟩,
    ⟨[96643, 13], [96643, 13], .contexts []⟩,
    ⟨[96643], [96643], .contexts []⟩,
    ⟨[36097], [36097], .contexts [
        ⟨13, false, false, [], [36097]⟩
      ]⟩,
    ⟨[96643, 13], [36097, 96643], .contexts [
        ⟨99099, false, false, [], []⟩,
        ⟨99093, true, false, [], [13]⟩,
        ⟨99093, true, false, [], [13]⟩,
        ⟨99092, true, false, [], [13]⟩,
        ⟨99090, true, false, [], [13]⟩,
        ⟨201, false, false, [96641], []⟩,
        ⟨202, false, false, [96641], []⟩,
        ⟨99084, false, false, [], [9]⟩,
        ⟨99088, false, false, [], [9]⟩,
        ⟨99094, false, false, [], [9]⟩,
        ⟨99095, false, false, [], [9]⟩,
        ⟨99095, false, false, [], [9]⟩,
        ⟨99090, false, false, [36097], []⟩,
        ⟨99096, false, false, [], []⟩,
        ⟨99097, false, false, [], []⟩,
        ⟨99098, false, false, [], []⟩,
        ⟨99100, false, false, [36097], []⟩,
        ⟨99101, true, false, [], [96643]⟩
      ]⟩,
    ⟨[96645], [96643, 11], .source 48387⟩,
    ⟨[96643, 11], [96645], .contexts [
        ⟨99103, true, false, [], []⟩
      ]⟩,
    ⟨[96645], [96645], .contexts []⟩,
    ⟨[96645], [96645], .contexts []⟩,
    ⟨[36097, 96645], [36097, 96645], .contexts []⟩,
    ⟨[36097, 96645], [36097, 96645], .contexts []⟩,
    ⟨[36097, 96645], [36097, 96645], .contexts []⟩,
    ⟨[96647], [96645, 1], .source 48388⟩,
    ⟨[96645, 1], [96647], .contexts [
        ⟨99110, true, false, [], []⟩
      ]⟩,
    ⟨[96647, 1], [96645], .contexts [
        ⟨99111, true, false, [], [1]⟩,
        ⟨8, false, false, [96645], []⟩,
        ⟨99106, false, false, [], []⟩
      ]⟩,
    ⟨[96649], [96647, 13], .source 48389⟩,
    ⟨[96647, 13], [96649], .contexts [
        ⟨99113, true, false, [], []⟩
      ]⟩,
    ⟨[96649], [96649], .contexts []⟩,
    ⟨[96649], [96649], .contexts []⟩,
    ⟨[36097, 96647], [36097, 96647], .contexts []⟩,
    ⟨[36097, 96647], [36097, 96647], .contexts []⟩,
    ⟨[96647, 1, 13, 1], [36097, 96647], .contexts [
        ⟨99112, false, false, [], [13, 1]⟩,
        ⟨99105, false, false, [], [13, 1]⟩,
        ⟨99106, false, false, [], [13, 1]⟩,
        ⟨99106, false, false, [], [13, 1]⟩,
        ⟨99106, true, false, [], [13, 1]⟩,
        ⟨99106, true, false, [], [13, 1]⟩,
        ⟨99105, true, false, [], [13, 1]⟩,
        ⟨99104, true, false, [], [13, 1]⟩,
        ⟨227, false, false, [96643], [1]⟩,
        ⟨228, false, false, [96643], [1]⟩,
        ⟨99099, false, false, [], [11, 1]⟩,
        ⟨99102, false, false, [], [11, 1]⟩,
        ⟨99096, false, false, [], [11, 1]⟩,
        ⟨99098, false, false, [], [11, 1]⟩,
        ⟨99098, false, false, [], [11, 1]⟩,
        ⟨99104, false, false, [36097], [1]⟩,
        ⟨99107, false, false, [], [1]⟩,
        ⟨99108, false, false, [], [1]⟩,
        ⟨99109, false, false, [], [1]⟩,
        ⟨99101, true, false, [], [96645, 1]⟩,
        ⟨99107, false, false, [], [1]⟩,
        ⟨99109, false, false, [], [1]⟩,
        ⟨99109, false, false, [], [1]⟩,
        ⟨99111, false, false, [36097], []⟩,
        ⟨99117, false, false, [], []⟩,
        ⟨99118, false, false, [], []⟩
      ]⟩,
    ⟨[36097, 96647], [36097, 96647], .contexts []⟩,
    ⟨[36097, 96649], [36097, 96649], .contexts []⟩,
    ⟨[36097, 96649], [36097, 96649], .contexts []⟩,
    ⟨[36097, 96649], [36097, 96649], .contexts []⟩,
    ⟨[96649, 1], [96649, 1], .contexts []⟩,
    ⟨[96649], [96649], .contexts []⟩,
    ⟨[96651], [96649, 15], .source 48390⟩,
    ⟨[96649, 15], [96651], .contexts [
        ⟨99126, true, false, [], []⟩
      ]⟩,
    ⟨[96651, 15], [96649], .contexts [
        ⟨99127, true, false, [], [15]⟩,
        ⟨1, false, false, [96649], []⟩,
        ⟨99116, false, false, [], []⟩
      ]⟩,
    ⟨[96651], [96651], .contexts []⟩,
    ⟨[96651], [96651], .contexts []⟩,
    ⟨[96649, 15], [96651], .contexts [
        ⟨99127, false, false, [], []⟩,
        ⟨99129, false, false, [], []⟩,
        ⟨99130, false, false, [], []⟩,
        ⟨99130, false, false, [], []⟩
      ]⟩,
    ⟨[36097, 96651], [36097, 96651], .contexts []⟩,
    ⟨[36097, 96651], [36097, 96651], .contexts []⟩,
    ⟨[96649, 1, 15], [36097, 96651], .contexts [
        ⟨99124, false, false, [], [15]⟩,
        ⟨99124, false, false, [], [15]⟩,
        ⟨99116, true, false, [], [1, 15]⟩,
        ⟨99116, true, false, [], [1, 15]⟩,
        ⟨99115, true, false, [], [1, 15]⟩,
        ⟨99114, true, false, [], [1, 15]⟩,
        ⟨246, false, false, [96647], [15]⟩,
        ⟨249, false, false, [96647], [15]⟩,
        ⟨99119, false, false, [], [13, 15]⟩,
        ⟨99120, false, false, [], [13, 15]⟩,
        ⟨99114, false, false, [36097], [15]⟩,
        ⟨99121, false, false, [], [15]⟩,
        ⟨99122, false, false, [], [15]⟩,
        ⟨99123, false, false, [], [15]⟩,
        ⟨99125, false, false, [36097], [15]⟩,
        ⟨99101, true, false, [], [96649, 15]⟩,
        ⟨99121, false, false, [], [15]⟩,
        ⟨99123, false, false, [], [15]⟩,
        ⟨99123, false, false, [], [15]⟩,
        ⟨99127, false, false, [36097], []⟩,
        ⟨99132, false, false, [], []⟩,
        ⟨99133, false, false, [], []⟩
      ]⟩,
    ⟨[96651, 1], [96651, 1], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1549. -/
def y322TCIndexRaw1549 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[96651], [96651], .contexts []⟩,
    ⟨[96651, 1], [36097, 96651], .contexts [
        ⟨99135, false, false, [], []⟩,
        ⟨99131, true, false, [], [1]⟩,
        ⟨7, false, false, [96649], []⟩,
        ⟨11, false, false, [96649], []⟩,
        ⟨99134, false, false, [], []⟩,
        ⟨99136, false, false, [36097], []⟩,
        ⟨99101, true, false, [], [96651]⟩
      ]⟩,
    ⟨[96653], [96651, 3], .source 48391⟩,
    ⟨[96651, 3], [96653], .contexts [
        ⟨99138, true, false, [], []⟩
      ]⟩,
    ⟨[96653, 3], [96651], .contexts [
        ⟨99139, true, false, [], [3]⟩,
        ⟨20, false, false, [96651], []⟩,
        ⟨99130, false, false, [], []⟩
      ]⟩,
    ⟨[96655], [96653, 5], .source 48392⟩,
    ⟨[96653, 5], [96655], .contexts [
        ⟨99141, true, false, [], []⟩
      ]⟩,
    ⟨[96653], [96653], .contexts []⟩,
    ⟨[96655, 5], [96653], .contexts [
        ⟨99142, true, false, [], [5]⟩,
        ⟨28, false, false, [96653], []⟩,
        ⟨99143, false, false, [], []⟩
      ]⟩,
    ⟨[96657], [96655, 1], .source 48393⟩,
    ⟨[96655, 1], [96657], .contexts [
        ⟨99145, true, false, [], []⟩
      ]⟩,
    ⟨[96655], [96655], .contexts []⟩,
    ⟨[96657, 1], [96655], .contexts [
        ⟨99146, true, false, [], [1]⟩,
        ⟨8, false, false, [96655], []⟩,
        ⟨99147, false, false, [], []⟩
      ]⟩,
    ⟨[96659], [96657, 9], .source 48394⟩,
    ⟨[96657, 9], [96659], .contexts [
        ⟨99149, true, false, [], []⟩
      ]⟩,
    ⟨[96657], [96657], .contexts []⟩,
    ⟨[96659, 9], [96657], .contexts [
        ⟨99150, true, false, [], [9]⟩,
        ⟨46, false, false, [96657], []⟩,
        ⟨99151, false, false, [], []⟩
      ]⟩,
    ⟨[96661], [96659, 11], .source 48395⟩,
    ⟨[96659, 11], [96661], .contexts [
        ⟨99153, true, false, [], []⟩
      ]⟩,
    ⟨[96659], [96659], .contexts []⟩,
    ⟨[96661, 11], [96659], .contexts [
        ⟨99154, true, false, [], [11]⟩,
        ⟨53, false, false, [96659], []⟩,
        ⟨99155, false, false, [], []⟩
      ]⟩,
    ⟨[96663], [96661, 1], .source 48396⟩,
    ⟨[96661, 1], [96663], .contexts [
        ⟨99157, true, false, [], []⟩
      ]⟩,
    ⟨[96661], [96661], .contexts []⟩,
    ⟨[96663, 1], [96661], .contexts [
        ⟨99158, true, false, [], [1]⟩,
        ⟨8, false, false, [96661], []⟩,
        ⟨99159, false, false, [], []⟩
      ]⟩,
    ⟨[96665], [96663, 13], .source 48397⟩,
    ⟨[96663, 13], [96665], .contexts [
        ⟨99161, true, false, [], []⟩
      ]⟩,
    ⟨[96663], [96663], .contexts []⟩,
    ⟨[96665, 13], [96663], .contexts [
        ⟨99162, true, false, [], [13]⟩,
        ⟨59, false, false, [96663], []⟩,
        ⟨99163, false, false, [], []⟩
      ]⟩,
    ⟨[96667], [96665, 15], .source 48398⟩,
    ⟨[96665, 15], [96667], .contexts [
        ⟨99165, true, false, [], []⟩
      ]⟩,
    ⟨[96665], [96665], .contexts []⟩,
    ⟨[96669], [96667, 1], .source 48399⟩,
    ⟨[96667, 1], [96669], .contexts [
        ⟨99168, true, false, [], []⟩
      ]⟩,
    ⟨[96667], [96667], .contexts []⟩,
    ⟨[96671], [96669, 3], .source 48400⟩,
    ⟨[96669, 3], [96671], .contexts [
        ⟨99171, true, false, [], []⟩
      ]⟩,
    ⟨[96669], [96669], .contexts []⟩,
    ⟨[96673], [96671, 5], .source 48401⟩,
    ⟨[96671, 5], [96673], .contexts [
        ⟨99174, true, false, [], []⟩
      ]⟩,
    ⟨[96671], [96671], .contexts []⟩,
    ⟨[96675], [96673, 1], .source 48402⟩,
    ⟨[96673, 1], [96675], .contexts [
        ⟨99177, true, false, [], []⟩
      ]⟩,
    ⟨[96673], [96673], .contexts []⟩,
    ⟨[96677], [96675, 9], .source 48403⟩,
    ⟨[96675, 9], [96677], .contexts [
        ⟨99180, true, false, [], []⟩
      ]⟩,
    ⟨[96675], [96675], .contexts []⟩,
    ⟨[96679], [96677, 11], .source 48404⟩,
    ⟨[96677, 11], [96679], .contexts [
        ⟨99183, true, false, [], []⟩
      ]⟩,
    ⟨[96677], [96677], .contexts []⟩,
    ⟨[96679, 11], [96677], .contexts [
        ⟨99184, true, false, [], [11]⟩,
        ⟨53, false, false, [96677], []⟩,
        ⟨99185, false, false, [], []⟩
      ]⟩,
    ⟨[96681], [96679, 1], .source 48405⟩,
    ⟨[96679, 1], [96681], .contexts [
        ⟨99187, true, false, [], []⟩
      ]⟩,
    ⟨[96679], [96679], .contexts []⟩,
    ⟨[96683], [96681, 13], .source 48406⟩,
    ⟨[96681, 13], [96683], .contexts [
        ⟨99190, true, false, [], []⟩
      ]⟩,
    ⟨[96681], [96681], .contexts []⟩,
    ⟨[96685], [96683, 15], .source 48407⟩,
    ⟨[96683, 15], [96685], .contexts [
        ⟨99193, true, false, [], []⟩
      ]⟩,
    ⟨[96683], [96683], .contexts []⟩,
    ⟨[96687], [96685, 1], .source 48408⟩,
    ⟨[96685, 1], [96687], .contexts [
        ⟨99196, true, false, [], []⟩
      ]⟩,
    ⟨[96685], [96685], .contexts []⟩,
    ⟨[96689], [96687, 3], .source 48409⟩]

/-- Exact literal claimed equations and contextual derivations, block 1550. -/
def y322TCIndexRaw1550 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[96687, 3], [96689], .contexts [
        ⟨99199, true, false, [], []⟩
      ]⟩,
    ⟨[96687], [96687], .contexts []⟩,
    ⟨[96691], [96689, 5], .source 48410⟩,
    ⟨[96689, 5], [96691], .contexts [
        ⟨99202, true, false, [], []⟩
      ]⟩,
    ⟨[96689], [96689], .contexts []⟩,
    ⟨[96693], [96691, 1], .source 48411⟩,
    ⟨[96691, 1], [96693], .contexts [
        ⟨99205, true, false, [], []⟩
      ]⟩,
    ⟨[96691], [96691], .contexts []⟩,
    ⟨[96695], [96693, 9], .source 48412⟩,
    ⟨[96693, 9], [96695], .contexts [
        ⟨99208, true, false, [], []⟩
      ]⟩,
    ⟨[96693], [96693], .contexts []⟩,
    ⟨[96697], [96695, 11], .source 48413⟩,
    ⟨[96695, 11], [96697], .contexts [
        ⟨99211, true, false, [], []⟩
      ]⟩,
    ⟨[96695], [96695], .contexts []⟩,
    ⟨[96699], [96697, 1], .source 48414⟩,
    ⟨[96697, 1], [96699], .contexts [
        ⟨99214, true, false, [], []⟩
      ]⟩,
    ⟨[96697], [96697], .contexts []⟩,
    ⟨[96701], [96699, 13], .source 48415⟩,
    ⟨[96699, 13], [96701], .contexts [
        ⟨99217, true, false, [], []⟩
      ]⟩,
    ⟨[96699], [96699], .contexts []⟩,
    ⟨[96703], [96701, 15], .source 48416⟩,
    ⟨[96701, 15], [96703], .contexts [
        ⟨99220, true, false, [], []⟩
      ]⟩,
    ⟨[96701], [96701], .contexts []⟩,
    ⟨[96705], [96703, 1], .source 48417⟩,
    ⟨[96703, 1], [96705], .contexts [
        ⟨99223, true, false, [], []⟩
      ]⟩,
    ⟨[96703], [96703], .contexts []⟩,
    ⟨[96707], [96705, 3], .source 48418⟩,
    ⟨[96705, 3], [96707], .contexts [
        ⟨99226, true, false, [], []⟩
      ]⟩,
    ⟨[96705], [96705], .contexts []⟩,
    ⟨[96709], [96707, 5], .source 48419⟩,
    ⟨[96707], [96707], .contexts []⟩,
    ⟨[96709, 5], [96707], .contexts [
        ⟨99229, false, false, [], [5]⟩,
        ⟨28, false, false, [96707], []⟩,
        ⟨99230, false, false, [], []⟩
      ]⟩,
    ⟨[96711], [96709, 1], .source 48420⟩,
    ⟨[96709], [96709], .contexts []⟩,
    ⟨[96711, 1], [96709], .contexts [
        ⟨99232, false, false, [], [1]⟩,
        ⟨8, false, false, [96709], []⟩,
        ⟨99233, false, false, [], []⟩
      ]⟩,
    ⟨[96713], [96711, 9], .source 48421⟩,
    ⟨[96711, 9], [96713], .contexts [
        ⟨99235, true, false, [], []⟩
      ]⟩,
    ⟨[96711], [96711], .contexts []⟩,
    ⟨[96713, 9], [96711], .contexts [
        ⟨99236, true, false, [], [9]⟩,
        ⟨46, false, false, [96711], []⟩,
        ⟨99237, false, false, [], []⟩
      ]⟩,
    ⟨[96715], [96713, 11], .source 48422⟩,
    ⟨[96713, 11], [96715], .contexts [
        ⟨99239, true, false, [], []⟩
      ]⟩,
    ⟨[96713], [96713], .contexts []⟩,
    ⟨[96715, 11], [96713], .contexts [
        ⟨99240, true, false, [], [11]⟩,
        ⟨53, false, false, [96713], []⟩,
        ⟨99241, false, false, [], []⟩
      ]⟩,
    ⟨[96717], [96715, 1], .source 48423⟩,
    ⟨[96715, 1], [96717], .contexts [
        ⟨99243, true, false, [], []⟩
      ]⟩,
    ⟨[96715], [96715], .contexts []⟩,
    ⟨[96717, 1], [96715], .contexts [
        ⟨99244, true, false, [], [1]⟩,
        ⟨8, false, false, [96715], []⟩,
        ⟨99245, false, false, [], []⟩
      ]⟩,
    ⟨[96719], [96717, 13], .source 48424⟩,
    ⟨[96717, 13], [96719], .contexts [
        ⟨99247, true, false, [], []⟩
      ]⟩,
    ⟨[96717], [96717], .contexts []⟩,
    ⟨[96719, 13], [96717], .contexts [
        ⟨99248, true, false, [], [13]⟩,
        ⟨59, false, false, [96717], []⟩,
        ⟨99249, false, false, [], []⟩
      ]⟩,
    ⟨[96721], [96719, 15], .source 48425⟩,
    ⟨[96719], [96719], .contexts []⟩,
    ⟨[96721, 15], [96719], .contexts [
        ⟨99251, false, false, [], [15]⟩,
        ⟨1, false, false, [96719], []⟩,
        ⟨99252, false, false, [], []⟩
      ]⟩,
    ⟨[96723], [96721, 1], .source 48426⟩,
    ⟨[96721], [96721], .contexts []⟩,
    ⟨[96723, 1], [96721], .contexts [
        ⟨99254, false, false, [], [1]⟩,
        ⟨8, false, false, [96721], []⟩,
        ⟨99255, false, false, [], []⟩
      ]⟩,
    ⟨[96725], [96723, 3], .source 48427⟩,
    ⟨[96723, 3], [96725], .contexts [
        ⟨99257, true, false, [], []⟩
      ]⟩,
    ⟨[96723], [96723], .contexts []⟩,
    ⟨[96725, 3], [96723], .contexts [
        ⟨99258, true, false, [], [3]⟩,
        ⟨20, false, false, [96723], []⟩,
        ⟨99259, false, false, [], []⟩
      ]⟩,
    ⟨[96727], [96725, 5], .source 48428⟩,
    ⟨[96725, 5], [96727], .contexts [
        ⟨99261, true, false, [], []⟩
      ]⟩,
    ⟨[96725], [96725], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1551. -/
def y322TCIndexRaw1551 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[96727, 5], [96725], .contexts [
        ⟨99262, true, false, [], [5]⟩,
        ⟨28, false, false, [96725], []⟩,
        ⟨99263, false, false, [], []⟩
      ]⟩,
    ⟨[96729], [96727, 1], .source 48429⟩,
    ⟨[96727, 1], [96729], .contexts [
        ⟨99265, true, false, [], []⟩
      ]⟩,
    ⟨[96727], [96727], .contexts []⟩,
    ⟨[96729, 1], [96727], .contexts [
        ⟨99266, true, false, [], [1]⟩,
        ⟨8, false, false, [96727], []⟩,
        ⟨99267, false, false, [], []⟩
      ]⟩,
    ⟨[96731], [96729, 9], .source 48430⟩,
    ⟨[96729], [96729], .contexts []⟩,
    ⟨[96731, 9], [96729], .contexts [
        ⟨99269, false, false, [], [9]⟩,
        ⟨46, false, false, [96729], []⟩,
        ⟨99270, false, false, [], []⟩
      ]⟩,
    ⟨[96733], [96731, 11], .source 48431⟩,
    ⟨[96731], [96731], .contexts []⟩,
    ⟨[96733, 11], [96731], .contexts [
        ⟨99272, false, false, [], [11]⟩,
        ⟨53, false, false, [96731], []⟩,
        ⟨99273, false, false, [], []⟩
      ]⟩,
    ⟨[96735], [96733, 1], .source 48432⟩,
    ⟨[96733], [96733], .contexts []⟩,
    ⟨[96735, 1], [96733], .contexts [
        ⟨99275, false, false, [], [1]⟩,
        ⟨8, false, false, [96733], []⟩,
        ⟨99276, false, false, [], []⟩
      ]⟩,
    ⟨[96737], [96735, 13], .source 48433⟩,
    ⟨[96735], [96735], .contexts []⟩,
    ⟨[96737, 13], [96735], .contexts [
        ⟨99278, false, false, [], [13]⟩,
        ⟨59, false, false, [96735], []⟩,
        ⟨99279, false, false, [], []⟩
      ]⟩,
    ⟨[96739], [96737, 15], .source 48434⟩,
    ⟨[96737], [96737], .contexts []⟩,
    ⟨[96739, 15], [96737], .contexts [
        ⟨99281, false, false, [], [15]⟩,
        ⟨1, false, false, [96737], []⟩,
        ⟨99282, false, false, [], []⟩
      ]⟩,
    ⟨[96741], [96739, 1], .source 48435⟩,
    ⟨[96739], [96739], .contexts []⟩,
    ⟨[96741, 1], [96739], .contexts [
        ⟨99284, false, false, [], [1]⟩,
        ⟨8, false, false, [96739], []⟩,
        ⟨99285, false, false, [], []⟩
      ]⟩,
    ⟨[96743], [96741, 3], .source 48436⟩,
    ⟨[96741], [96741], .contexts []⟩,
    ⟨[96743, 3], [96741], .contexts [
        ⟨99287, false, false, [], [3]⟩,
        ⟨20, false, false, [96741], []⟩,
        ⟨99288, false, false, [], []⟩
      ]⟩,
    ⟨[96745], [96743, 5], .source 48437⟩,
    ⟨[96743, 5], [96745], .contexts [
        ⟨99290, true, false, [], []⟩
      ]⟩,
    ⟨[96743], [96743], .contexts []⟩,
    ⟨[96745, 5], [96743], .contexts [
        ⟨99291, true, false, [], [5]⟩,
        ⟨28, false, false, [96743], []⟩,
        ⟨99292, false, false, [], []⟩
      ]⟩,
    ⟨[96747], [96745, 1], .source 48438⟩,
    ⟨[96745, 1], [96747], .contexts [
        ⟨99294, true, false, [], []⟩
      ]⟩,
    ⟨[96745], [96745], .contexts []⟩,
    ⟨[96747, 1], [96745], .contexts [
        ⟨99295, true, false, [], [1]⟩,
        ⟨8, false, false, [96745], []⟩,
        ⟨99296, false, false, [], []⟩
      ]⟩,
    ⟨[96747], [96747], .contexts []⟩,
    ⟨[96747], [96747], .contexts []⟩,
    ⟨[96739], [96739], .contexts []⟩,
    ⟨[96737], [96737], .contexts []⟩,
    ⟨[96735], [96735], .contexts []⟩,
    ⟨[96745, 5, 3, 1, 15, 13], [96735], .contexts [
        ⟨99293, false, false, [], [3, 1, 15, 13]⟩,
        ⟨99292, false, false, [], [3, 1, 15, 13]⟩,
        ⟨99292, false, false, [], [3, 1, 15, 13]⟩,
        ⟨99289, false, false, [], [1, 15, 13]⟩,
        ⟨99288, false, false, [], [1, 15, 13]⟩,
        ⟨99288, false, false, [], [1, 15, 13]⟩,
        ⟨99286, false, false, [], [15, 13]⟩,
        ⟨99300, false, false, [], [15, 13]⟩,
        ⟨99285, false, false, [], [15, 13]⟩,
        ⟨99285, false, false, [], [15, 13]⟩,
        ⟨99283, false, false, [], [13]⟩,
        ⟨99301, false, false, [], [13]⟩,
        ⟨99282, false, false, [], [13]⟩,
        ⟨99282, false, false, [], [13]⟩,
        ⟨99280, false, false, [], []⟩,
        ⟨99302, false, false, [], []⟩,
        ⟨99279, false, false, [], []⟩,
        ⟨99279, false, false, [], []⟩
      ]⟩,
    ⟨[96733], [96733], .contexts []⟩,
    ⟨[96733, 11], [96731], .contexts [
        ⟨99274, false, false, [], []⟩
      ]⟩,
    ⟨[96731], [96731], .contexts []⟩,
    ⟨[96731, 9], [96729], .contexts [
        ⟨99271, false, false, [], []⟩
      ]⟩,
    ⟨[96729], [96729], .contexts []⟩,
    ⟨[96729, 1], [96727], .contexts [
        ⟨99268, false, false, [], []⟩
      ]⟩,
    ⟨[96727], [96727], .contexts []⟩,
    ⟨[96727, 5], [96725], .contexts [
        ⟨99264, false, false, [], []⟩
      ]⟩,
    ⟨[96725], [96725], .contexts []⟩,
    ⟨[96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5], [96725], .contexts [
        ⟨99303, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨99277, false, false, [], [11, 9, 1, 5]⟩,
        ⟨99304, false, false, [], [11, 9, 1, 5]⟩,
        ⟨99276, false, false, [], [11, 9, 1, 5]⟩,
        ⟨99276, false, false, [], [11, 9, 1, 5]⟩,
        ⟨99305, false, false, [], [9, 1, 5]⟩,
        ⟨99306, false, false, [], [9, 1, 5]⟩,
        ⟨99273, false, false, [], [9, 1, 5]⟩,
        ⟨99273, false, false, [], [9, 1, 5]⟩,
        ⟨99307, false, false, [], [1, 5]⟩,
        ⟨99308, false, false, [], [1, 5]⟩,
        ⟨99270, false, false, [], [1, 5]⟩,
        ⟨99270, false, false, [], [1, 5]⟩,
        ⟨99309, false, false, [], [5]⟩,
        ⟨99310, false, false, [], [5]⟩,
        ⟨99267, false, false, [], [5]⟩,
        ⟨99267, false, false, [], [5]⟩,
        ⟨99311, false, false, [], []⟩,
        ⟨99312, false, false, [], []⟩,
        ⟨99263, false, false, [], []⟩,
        ⟨99263, false, false, [], []⟩
      ]⟩,
    ⟨[96725, 3], [96723], .contexts [
        ⟨99260, false, false, [], []⟩
      ]⟩,
    ⟨[96723], [96723], .contexts []⟩,
    ⟨[96723, 1], [96721], .contexts [
        ⟨99256, false, false, [], []⟩
      ]⟩,
    ⟨[96721], [96721], .contexts []⟩,
    ⟨[96721, 15], [96719], .contexts [
        ⟨99253, false, false, [], []⟩
      ]⟩,
    ⟨[96719], [96719], .contexts []⟩,
    ⟨[96719, 13], [96717], .contexts [
        ⟨99250, false, false, [], []⟩
      ]⟩,
    ⟨[96717], [96717], .contexts []⟩,
    ⟨[96717, 1], [96715], .contexts [
        ⟨99246, false, false, [], []⟩
      ]⟩,
    ⟨[96715], [96715], .contexts []⟩,
    ⟨[
      96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1
    ], [96715], .contexts [
        ⟨99313, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨99314, false, false, [], [1, 15, 13, 1]⟩,
        ⟨99315, false, false, [], [1, 15, 13, 1]⟩,
        ⟨99259, false, false, [], [1, 15, 13, 1]⟩,
        ⟨99259, false, false, [], [1, 15, 13, 1]⟩,
        ⟨99316, false, false, [], [15, 13, 1]⟩,
        ⟨99317, false, false, [], [15, 13, 1]⟩,
        ⟨99255, false, false, [], [15, 13, 1]⟩,
        ⟨99255, false, false, [], [15, 13, 1]⟩,
        ⟨99318, false, false, [], [13, 1]⟩,
        ⟨99319, false, false, [], [13, 1]⟩,
        ⟨99252, false, false, [], [13, 1]⟩,
        ⟨99252, false, false, [], [13, 1]⟩,
        ⟨99320, false, false, [], [1]⟩,
        ⟨99321, false, false, [], [1]⟩,
        ⟨99249, false, false, [], [1]⟩,
        ⟨99249, false, false, [], [1]⟩,
        ⟨99322, false, false, [], []⟩,
        ⟨99323, false, false, [], []⟩,
        ⟨99245, false, false, [], []⟩,
        ⟨99245, false, false, [], []⟩
      ]⟩,
    ⟨[96715, 11], [96713], .contexts [
        ⟨99242, false, false, [], []⟩
      ]⟩,
    ⟨[96713], [96713], .contexts []⟩,
    ⟨[96713, 9], [96711], .contexts [
        ⟨99238, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1552. -/
def y322TCIndexRaw1552 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[96711], [96711], .contexts []⟩,
    ⟨[96707], [96707], .contexts []⟩,
    ⟨[96705], [96705], .contexts []⟩,
    ⟨[
      96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3
    ], [96705], .contexts [
        ⟨99324, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨99325, false, false, [], [9, 1, 5, 3]⟩,
        ⟨99326, false, false, [], [9, 1, 5, 3]⟩,
        ⟨99241, false, false, [], [9, 1, 5, 3]⟩,
        ⟨99241, false, false, [], [9, 1, 5, 3]⟩,
        ⟨99327, false, false, [], [1, 5, 3]⟩,
        ⟨99328, false, false, [], [1, 5, 3]⟩,
        ⟨99237, false, false, [], [1, 5, 3]⟩,
        ⟨99237, false, false, [], [1, 5, 3]⟩,
        ⟨99234, false, false, [], [5, 3]⟩,
        ⟨99233, false, false, [], [5, 3]⟩,
        ⟨99233, false, false, [], [5, 3]⟩,
        ⟨99231, false, false, [], [3]⟩,
        ⟨99329, false, false, [], [3]⟩,
        ⟨99230, false, false, [], [3]⟩,
        ⟨99230, false, false, [], [3]⟩,
        ⟨99227, true, false, [], [3]⟩,
        ⟨20, false, false, [96705], []⟩,
        ⟨99228, false, false, [], []⟩,
        ⟨99330, false, false, [], []⟩,
        ⟨99228, false, false, [], []⟩,
        ⟨99228, false, false, [], []⟩
      ]⟩,
    ⟨[96703], [96703], .contexts []⟩,
    ⟨[96701], [96701], .contexts []⟩,
    ⟨[96699], [96699], .contexts []⟩,
    ⟨[96697], [96697], .contexts []⟩,
    ⟨[
      96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1
    ], [96697], .contexts [
        ⟨99331, false, false, [], [1, 15, 13, 1]⟩,
        ⟨99224, true, false, [], [1, 15, 13, 1]⟩,
        ⟨8, false, false, [96703], [15, 13, 1]⟩,
        ⟨99225, false, false, [], [15, 13, 1]⟩,
        ⟨99332, false, false, [], [15, 13, 1]⟩,
        ⟨99225, false, false, [], [15, 13, 1]⟩,
        ⟨99225, false, false, [], [15, 13, 1]⟩,
        ⟨99221, true, false, [], [15, 13, 1]⟩,
        ⟨1, false, false, [96701], [13, 1]⟩,
        ⟨99222, false, false, [], [13, 1]⟩,
        ⟨99333, false, false, [], [13, 1]⟩,
        ⟨99222, false, false, [], [13, 1]⟩,
        ⟨99222, false, false, [], [13, 1]⟩,
        ⟨99218, true, false, [], [13, 1]⟩,
        ⟨59, false, false, [96699], [1]⟩,
        ⟨99219, false, false, [], [1]⟩,
        ⟨99334, false, false, [], [1]⟩,
        ⟨99219, false, false, [], [1]⟩,
        ⟨99219, false, false, [], [1]⟩,
        ⟨99215, true, false, [], [1]⟩,
        ⟨8, false, false, [96697], []⟩,
        ⟨99216, false, false, [], []⟩,
        ⟨99335, false, false, [], []⟩,
        ⟨99216, false, false, [], []⟩,
        ⟨99216, false, false, [], []⟩
      ]⟩,
    ⟨[96695], [96695], .contexts []⟩,
    ⟨[96693], [96693], .contexts []⟩,
    ⟨[96691], [96691], .contexts []⟩,
    ⟨[96689], [96689], .contexts []⟩,
    ⟨[
      96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5
    ], [96689], .contexts [
        ⟨99336, false, false, [], [11, 9, 1, 5]⟩,
        ⟨99212, true, false, [], [11, 9, 1, 5]⟩,
        ⟨53, false, false, [96695], [9, 1, 5]⟩,
        ⟨99213, false, false, [], [9, 1, 5]⟩,
        ⟨99337, false, false, [], [9, 1, 5]⟩,
        ⟨99213, false, false, [], [9, 1, 5]⟩,
        ⟨99213, false, false, [], [9, 1, 5]⟩,
        ⟨99209, true, false, [], [9, 1, 5]⟩,
        ⟨46, false, false, [96693], [1, 5]⟩,
        ⟨99210, false, false, [], [1, 5]⟩,
        ⟨99338, false, false, [], [1, 5]⟩,
        ⟨99210, false, false, [], [1, 5]⟩,
        ⟨99210, false, false, [], [1, 5]⟩,
        ⟨99206, true, false, [], [1, 5]⟩,
        ⟨8, false, false, [96691], [5]⟩,
        ⟨99207, false, false, [], [5]⟩,
        ⟨99339, false, false, [], [5]⟩,
        ⟨99207, false, false, [], [5]⟩,
        ⟨99207, false, false, [], [5]⟩,
        ⟨99203, true, false, [], [5]⟩,
        ⟨28, false, false, [96689], []⟩,
        ⟨99204, false, false, [], []⟩,
        ⟨99340, false, false, [], []⟩,
        ⟨99204, false, false, [], []⟩,
        ⟨99204, false, false, [], []⟩
      ]⟩,
    ⟨[96687], [96687], .contexts []⟩,
    ⟨[96685], [96685], .contexts []⟩,
    ⟨[96683], [96683], .contexts []⟩,
    ⟨[96681], [96681], .contexts []⟩,
    ⟨[
      96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13
    ], [96681], .contexts [
        ⟨99341, false, false, [], [3, 1, 15, 13]⟩,
        ⟨99200, true, false, [], [3, 1, 15, 13]⟩,
        ⟨20, false, false, [96687], [1, 15, 13]⟩,
        ⟨99201, false, false, [], [1, 15, 13]⟩,
        ⟨99342, false, false, [], [1, 15, 13]⟩,
        ⟨99201, false, false, [], [1, 15, 13]⟩,
        ⟨99201, false, false, [], [1, 15, 13]⟩,
        ⟨99197, true, false, [], [1, 15, 13]⟩,
        ⟨8, false, false, [96685], [15, 13]⟩,
        ⟨99198, false, false, [], [15, 13]⟩,
        ⟨99343, false, false, [], [15, 13]⟩,
        ⟨99198, false, false, [], [15, 13]⟩,
        ⟨99198, false, false, [], [15, 13]⟩,
        ⟨99194, true, false, [], [15, 13]⟩,
        ⟨1, false, false, [96683], [13]⟩,
        ⟨99195, false, false, [], [13]⟩,
        ⟨99344, false, false, [], [13]⟩,
        ⟨99195, false, false, [], [13]⟩,
        ⟨99195, false, false, [], [13]⟩,
        ⟨99191, true, false, [], [13]⟩,
        ⟨59, false, false, [96681], []⟩,
        ⟨99192, false, false, [], []⟩,
        ⟨99345, false, false, [], []⟩,
        ⟨99192, false, false, [], []⟩,
        ⟨99192, false, false, [], []⟩
      ]⟩,
    ⟨[96679], [96679], .contexts []⟩,
    ⟨[96677], [96677], .contexts []⟩,
    ⟨[96675], [96675], .contexts []⟩,
    ⟨[96673], [96673], .contexts []⟩,
    ⟨[
      96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1
    ], [96673], .contexts [
        ⟨99346, false, false, [], [1, 11, 9, 1]⟩,
        ⟨99188, true, false, [], [1, 11, 9, 1]⟩,
        ⟨8, false, false, [96679], [11, 9, 1]⟩,
        ⟨99189, false, false, [], [11, 9, 1]⟩,
        ⟨99347, false, false, [], [11, 9, 1]⟩,
        ⟨99189, false, false, [], [11, 9, 1]⟩,
        ⟨99189, false, false, [], [11, 9, 1]⟩,
        ⟨99186, false, false, [], [9, 1]⟩,
        ⟨99348, false, false, [], [9, 1]⟩,
        ⟨99185, false, false, [], [9, 1]⟩,
        ⟨99185, false, false, [], [9, 1]⟩,
        ⟨99181, true, false, [], [9, 1]⟩,
        ⟨46, false, false, [96675], [1]⟩,
        ⟨99182, false, false, [], [1]⟩,
        ⟨99349, false, false, [], [1]⟩,
        ⟨99182, false, false, [], [1]⟩,
        ⟨99182, false, false, [], [1]⟩,
        ⟨99178, true, false, [], [1]⟩,
        ⟨8, false, false, [96673], []⟩,
        ⟨99179, false, false, [], []⟩,
        ⟨99350, false, false, [], []⟩,
        ⟨99179, false, false, [], []⟩,
        ⟨99179, false, false, [], []⟩
      ]⟩,
    ⟨[96671], [96671], .contexts []⟩,
    ⟨[96669], [96669], .contexts []⟩,
    ⟨[96667], [96667], .contexts []⟩,
    ⟨[96665], [96665], .contexts []⟩,
    ⟨[
      96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15
    ], [96665], .contexts [
        ⟨99351, false, false, [], [5, 3, 1, 15]⟩,
        ⟨99175, true, false, [], [5, 3, 1, 15]⟩,
        ⟨28, false, false, [96671], [3, 1, 15]⟩,
        ⟨99176, false, false, [], [3, 1, 15]⟩,
        ⟨99352, false, false, [], [3, 1, 15]⟩,
        ⟨99176, false, false, [], [3, 1, 15]⟩,
        ⟨99176, false, false, [], [3, 1, 15]⟩,
        ⟨99172, true, false, [], [3, 1, 15]⟩,
        ⟨20, false, false, [96669], [1, 15]⟩,
        ⟨99173, false, false, [], [1, 15]⟩,
        ⟨99353, false, false, [], [1, 15]⟩,
        ⟨99173, false, false, [], [1, 15]⟩,
        ⟨99173, false, false, [], [1, 15]⟩,
        ⟨99169, true, false, [], [1, 15]⟩,
        ⟨8, false, false, [96667], [15]⟩,
        ⟨99170, false, false, [], [15]⟩,
        ⟨99354, false, false, [], [15]⟩,
        ⟨99170, false, false, [], [15]⟩,
        ⟨99170, false, false, [], [15]⟩,
        ⟨99166, true, false, [], [15]⟩,
        ⟨1, false, false, [96665], []⟩,
        ⟨99167, false, false, [], []⟩,
        ⟨99355, false, false, [], []⟩,
        ⟨99167, false, false, [], []⟩,
        ⟨99167, false, false, [], []⟩
      ]⟩,
    ⟨[96663], [96663], .contexts []⟩,
    ⟨[96661], [96661], .contexts []⟩,
    ⟨[96659], [96659], .contexts []⟩,
    ⟨[96657], [96657], .contexts []⟩,
    ⟨[96655], [96655], .contexts []⟩,
    ⟨[
      96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1
    ], [96655], .contexts [
        ⟨99356, false, false, [], [13, 1, 11, 9, 1]⟩,
        ⟨99164, false, false, [], [1, 11, 9, 1]⟩,
        ⟨99357, false, false, [], [1, 11, 9, 1]⟩,
        ⟨99163, false, false, [], [1, 11, 9, 1]⟩,
        ⟨99163, false, false, [], [1, 11, 9, 1]⟩,
        ⟨99160, false, false, [], [11, 9, 1]⟩,
        ⟨99358, false, false, [], [11, 9, 1]⟩,
        ⟨99159, false, false, [], [11, 9, 1]⟩,
        ⟨99159, false, false, [], [11, 9, 1]⟩,
        ⟨99156, false, false, [], [9, 1]⟩,
        ⟨99359, false, false, [], [9, 1]⟩,
        ⟨99155, false, false, [], [9, 1]⟩,
        ⟨99155, false, false, [], [9, 1]⟩,
        ⟨99152, false, false, [], [1]⟩,
        ⟨99360, false, false, [], [1]⟩,
        ⟨99151, false, false, [], [1]⟩,
        ⟨99151, false, false, [], [1]⟩,
        ⟨99148, false, false, [], []⟩,
        ⟨99361, false, false, [], []⟩,
        ⟨99147, false, false, [], []⟩,
        ⟨99147, false, false, [], []⟩
      ]⟩,
    ⟨[96655, 5], [96653], .contexts [
        ⟨99144, false, false, [], []⟩
      ]⟩,
    ⟨[96653], [96653], .contexts []⟩,
    ⟨[96653, 3], [96651], .contexts [
        ⟨99140, false, false, [], []⟩
      ]⟩,
    ⟨[96651, 1], [36097, 96651], .contexts [
        ⟨99137, false, false, [], []⟩
      ]⟩,
    ⟨[
      96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13
    ], [36097, 96647], .contexts [
        ⟨99362, false, false, [], [5, 3, 1, 15, 13]⟩,
        ⟨99363, false, false, [], [3, 1, 15, 13]⟩,
        ⟨99364, false, false, [], [3, 1, 15, 13]⟩,
        ⟨99143, false, false, [], [3, 1, 15, 13]⟩,
        ⟨99143, false, false, [], [3, 1, 15, 13]⟩,
        ⟨99365, false, false, [], [1, 15, 13]⟩,
        ⟨99129, false, false, [], [1, 15, 13]⟩,
        ⟨99130, false, false, [], [1, 15, 13]⟩,
        ⟨99130, false, false, [], [1, 15, 13]⟩,
        ⟨99366, false, false, [], [15, 13]⟩,
        ⟨99132, false, false, [], [15, 13]⟩,
        ⟨99133, false, false, [], [15, 13]⟩,
        ⟨99133, false, false, [], [15, 13]⟩,
        ⟨99128, false, false, [36097], [13]⟩,
        ⟨99121, false, false, [], [13]⟩,
        ⟨99122, false, false, [], [13]⟩,
        ⟨99123, false, false, [], [13]⟩,
        ⟨99114, true, false, [36097], [13]⟩,
        ⟨59, false, false, [36097, 96647], []⟩,
        ⟨99117, false, false, [], []⟩,
        ⟨99118, false, false, [], []⟩,
        ⟨99120, false, false, [], []⟩
      ]⟩,
    ⟨[
      96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5
    ], [36097, 85917], .contexts [
        ⟨99367, false, false, [], [1, 11, 9, 1, 5]⟩,
        ⟨99112, false, false, [36097], [11, 9, 1, 5]⟩,
        ⟨99107, false, false, [], [11, 9, 1, 5]⟩,
        ⟨99108, false, false, [], [11, 9, 1, 5]⟩,
        ⟨99109, false, false, [], [11, 9, 1, 5]⟩,
        ⟨99104, true, false, [36097], [11, 9, 1, 5]⟩,
        ⟨53, false, false, [36097, 96643], [9, 1, 5]⟩,
        ⟨99093, false, false, [36097], [9, 1, 5]⟩,
        ⟨99096, false, false, [], [9, 1, 5]⟩,
        ⟨99097, false, false, [], [9, 1, 5]⟩,
        ⟨99098, false, false, [], [9, 1, 5]⟩,
        ⟨99091, false, false, [36097], [1, 5]⟩,
        ⟨99094, false, false, [], [1, 5]⟩,
        ⟨99095, false, false, [], [1, 5]⟩,
        ⟨99069, true, false, [36097], [1, 5]⟩,
        ⟨8, false, false, [36097, 96639], [5]⟩,
        ⟨99059, false, false, [36097], [5]⟩,
        ⟨99058, false, false, [36097], []⟩
      ]⟩,
    ⟨[36099], [36097, 30849], .source 18114⟩,
    ⟨[36101], [36099, 36083], .source 18115⟩,
    ⟨[
      96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1
    ], [36101, 83383], .contexts [
        ⟨99368, false, false, [], [3, 1, 15, 13, 1]⟩,
        ⟨81983, false, false, [36097], [1, 15, 13, 1]⟩,
        ⟨99369, true, false, [], [86625, 1, 15, 13, 1]⟩,
        ⟨38253, false, false, [36099], [15, 13, 1]⟩,
        ⟨99055, false, false, [36099], [13, 1]⟩,
        ⟨99370, true, false, [], [96637, 13, 1]⟩,
        ⟨99024, false, false, [36101], [1]⟩,
        ⟨21123, false, false, [36101], []⟩
      ]⟩,
    ⟨[36103], [36101, 21743], .source 18116⟩,
    ⟨[36105], [36103, 21741], .source 18117⟩,
    ⟨[36107], [36105, 21059], .source 18118⟩,
    ⟨[36109], [36107, 21047], .source 18119⟩,
    ⟨[
      96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3
    ], [36109, 83165], .contexts [
        ⟨99371, false, false, [], [11, 9, 1, 5, 3]⟩,
        ⟨97411, false, false, [36101], [9, 1, 5, 3]⟩,
        ⟨97408, false, false, [36101], [1, 5, 3]⟩,
        ⟨99372, true, false, [], [87799, 1, 5, 3]⟩,
        ⟨46239, false, false, [36103], [5, 3]⟩,
        ⟨99373, true, false, [], [85497, 5, 3]⟩,
        ⟨44094, false, false, [36105], [3]⟩,
        ⟨99374, true, false, [], [87567, 3]⟩,
        ⟨44083, false, false, [36107], []⟩,
        ⟨99375, true, false, [], [83165]⟩
      ]⟩,
    ⟨[36111], [36109, 2007], .source 18120⟩,
    ⟨[36113], [36111, 2575], .source 18121⟩,
    ⟨[36115], [36113, 15233], .source 18122⟩,
    ⟨[36117], [36115, 16197], .source 18123⟩,
    ⟨[
      96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11
    ], [36117, 83359], .contexts [
        ⟨99376, false, false, [], [1, 15, 13, 1, 11]⟩,
        ⟨19431, false, false, [36109], [15, 13, 1, 11]⟩,
        ⟨99377, true, false, [], [83165, 15, 13, 1, 11]⟩,
        ⟨19441, false, false, [36111], [13, 1, 11]⟩,
        ⟨17382, false, false, [36111], [1, 11]⟩,
        ⟨99378, true, false, [], [82843, 1, 11]⟩,
        ⟨17376, false, false, [36113], [11]⟩,
        ⟨99379, true, false, [], [82843, 11]⟩,
        ⟨20916, false, false, [36115], []⟩,
        ⟨99380, true, false, [], [83359]⟩
      ]⟩,
    ⟨[36119], [36117, 15259], .source 18124⟩,
    ⟨[36121], [36119, 15211], .source 18125⟩,
    ⟨[36123], [36121, 15605], .source 18126⟩,
    ⟨[36125], [36123, 315], .source 18127⟩,
    ⟨[
      96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1
    ], [36125, 82677], .contexts [
        ⟨99381, false, false, [], [9, 1, 5, 3, 1]⟩,
        ⟨20909, false, false, [36117], [1, 5, 3, 1]⟩,
        ⟨99382, true, false, [], [82841, 1, 5, 3, 1]⟩,
        ⟨17341, false, false, [36119], [5, 3, 1]⟩,
        ⟨99383, true, false, [], [82835, 5, 3, 1]⟩,
        ⟨17256, false, false, [36121], [3, 1]⟩,
        ⟨99384, true, false, [], [82685, 3, 1]⟩,
        ⟨15377, false, false, [36123], [1]⟩,
        ⟨99385, true, false, [], [82685, 1]⟩,
        ⟨15371, false, false, [36125], []⟩
      ]⟩,
    ⟨[36127], [36125, 1075], .source 18128⟩,
    ⟨[
      96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9
    ], [36127, 79199], .contexts [
        ⟨99386, false, false, [], [15, 13, 1, 11, 9]⟩,
        ⟨15286, false, false, [36125], [13, 1, 11, 9]⟩,
        ⟨17151, false, false, [36125], [1, 11, 9]⟩,
        ⟨17162, false, false, [36125], [11, 9]⟩,
        ⟨99387, true, false, [], [82827, 11, 9]⟩,
        ⟨17169, false, false, [36127], [9]⟩,
        ⟨6341, false, false, [36127], []⟩
      ]⟩,
    ⟨[36129], [36127, 14693], .source 18129⟩,
    ⟨[36131], [36129, 16043], .source 18130⟩,
    ⟨[36133], [36131, 15119], .source 18131⟩]

/-- Exact literal claimed equations and contextual derivations, block 1553. -/
def y322TCIndexRaw1553 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[
      96745, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15, 13, 1, 11, 9, 1, 5, 3, 1, 15, 13,
      1, 11, 9, 1, 5, 3, 1, 15, 13, 1, 11, 9,
      1, 5, 3, 1, 15, 13, 1, 11, 9, 1, 5, 3,
      1, 15
    ], [36133, 87807], .contexts [
        ⟨99388, false, false, [], [1, 5, 3, 1, 15]⟩,
        ⟨14511, false, false, [36127], [5, 3, 1, 15]⟩,
        ⟨99389, true, false, [], [81951, 5, 3, 1, 15]⟩,
        ⟨19930, false, false, [36129], [3, 1, 15]⟩,
        ⟨99390, true, false, [], [83205, 3, 1, 15]⟩,
        ⟨46476, false, false, [36131], [1, 15]⟩,
        ⟨46514, false, false, [36131], [15]⟩,
        ⟨46549, false, false, [36131], []⟩,
        ⟨99391, true, false, [], [87807]⟩
      ]⟩,
    ⟨[36135], [36133, 19117], .source 18132⟩,
    ⟨[36137], [36135, 21591], .source 18133⟩,
    ⟨[96747, 9], [96747, 9], .contexts []⟩,
    ⟨[96747, 9], [36137, 86609], .contexts [
        ⟨99395, false, false, [], []⟩,
        ⟨99299, true, false, [], [9]⟩,
        ⟨99299, true, false, [], [9]⟩,
        ⟨99298, true, false, [], [9]⟩,
        ⟨99295, true, false, [], [9]⟩,
        ⟨447, false, false, [96745], []⟩,
        ⟨449, false, false, [96745], []⟩,
        ⟨99392, false, false, [], [13, 1, 11]⟩,
        ⟨46544, false, false, [36133], [1, 11]⟩,
        ⟨99393, true, false, [], [84337, 1, 11]⟩,
        ⟨25897, false, false, [36135], [11]⟩,
        ⟨45561, false, false, [36135], []⟩,
        ⟨99394, true, false, [], [86609]⟩,
        ⟨45560, false, false, [36137], []⟩,
        ⟨13, true, false, [], [36137, 86609]⟩
      ]⟩,
    ⟨[36139], [36136], .source 18134⟩,
    ⟨[36137, 86609], [36137, 86609], .contexts []⟩,
    ⟨[36137, 86609], [36137, 86609], .contexts []⟩,
    ⟨[96747, 9], [36137, 86609], .contexts [
        ⟨99395, false, false, [], []⟩,
        ⟨99396, false, false, [], []⟩,
        ⟨99398, false, false, [], []⟩,
        ⟨99399, false, false, [], []⟩,
        ⟨99399, false, false, [], []⟩
      ]⟩,
    ⟨[36141], [36137, 21593], .source 18135⟩,
    ⟨[36143], [36141, 17027], .source 18136⟩,
    ⟨[96745, 9], [96745, 9], .contexts []⟩,
    ⟨[96745, 9], [36143, 84329], .contexts [
        ⟨99403, false, false, [], []⟩,
        ⟨99296, true, false, [], [9]⟩,
        ⟨99296, true, false, [], [9]⟩,
        ⟨99297, true, false, [], [9]⟩,
        ⟨452, false, false, [96747], []⟩,
        ⟨455, false, false, [96747], []⟩,
        ⟨99400, false, false, [], [1, 9, 1]⟩,
        ⟨45635, false, false, [36137], [9, 1]⟩,
        ⟨99401, true, false, [], [84335, 9, 1]⟩,
        ⟨25891, false, false, [36141], [1]⟩,
        ⟨25887, false, false, [36141], []⟩,
        ⟨41257, false, false, [36141], []⟩,
        ⟨99402, true, false, [], [84329]⟩,
        ⟨41260, false, false, [36143], []⟩,
        ⟨13, true, false, [], [36143, 84329]⟩
      ]⟩,
    ⟨[36145], [36142], .source 18137⟩,
    ⟨[84329, 9], [36145, 96745], .contexts [
        ⟨99404, true, false, [36142], [9]⟩,
        ⟨46, false, false, [36142, 96745], []⟩,
        ⟨99405, true, false, [], [96745]⟩
      ]⟩,
    ⟨[36147], [36137, 22775], .source 18138⟩,
    ⟨[96747], [96747], .contexts []⟩,
    ⟨[88461, 3], [88461, 3], .contexts []⟩,
    ⟨[96747], [96747], .contexts []⟩,
    ⟨[36149], [36146], .source 18139⟩,
    ⟨[36146], [36146], .contexts []⟩,
    ⟨[88461, 3], [36149, 96747], .contexts [
        ⟨99409, false, false, [], []⟩,
        ⟨50269, true, false, [], [3]⟩,
        ⟨99407, false, false, [36146], [88463, 9, 3]⟩,
        ⟨50463, true, false, [36146, 36137], [9, 3]⟩,
        ⟨99400, true, false, [36146], [3, 9, 3]⟩,
        ⟨1439, false, false, [36146, 96747], []⟩,
        ⟨99408, false, false, [36146], []⟩,
        ⟨99410, false, false, [36146], []⟩,
        ⟨99412, true, false, [], [96747]⟩,
        ⟨99412, true, false, [], [96747]⟩,
        ⟨99411, true, false, [], [96747]⟩
      ]⟩,
    ⟨[36157], [36137, 21841], .source 18143⟩,
    ⟨[36157, 85707], [36157, 85707], .contexts []⟩,
    ⟨[85707, 7], [85707, 7], .contexts []⟩,
    ⟨[36159], [36156], .source 18144⟩,
    ⟨[36156], [36156], .contexts []⟩,
    ⟨[85707, 7], [36159, 96747], .contexts [
        ⟨99416, false, false, [], []⟩,
        ⟨99415, true, false, [36156], [7]⟩,
        ⟨33062, true, false, [], [7]⟩,
        ⟨99414, false, false, [36156], [85709, 9, 7]⟩,
        ⟨46582, true, false, [36156, 36137], [9, 7]⟩,
        ⟨99400, true, false, [36156], [7, 9, 7]⟩,
        ⟨469, false, false, [36156, 96747], []⟩,
        ⟨99408, false, false, [36156], []⟩,
        ⟨99410, false, false, [36156], []⟩,
        ⟨99418, true, false, [], [96747]⟩,
        ⟨99418, true, false, [], [96747]⟩,
        ⟨99417, true, false, [], [96747]⟩
      ]⟩,
    ⟨[86607], [21567, 84101], .contexts [
        ⟨45504, false, false, [], []⟩
      ]⟩,
    ⟨[36161], [36137, 21567], .source 18145⟩,
    ⟨[36161, 84103], [36161, 84103], .contexts []⟩,
    ⟨[84103, 13], [84103, 13], .contexts []⟩,
    ⟨[36163], [36160], .source 18146⟩,
    ⟨[36160], [36160], .contexts []⟩,
    ⟨[84103, 13], [36163, 96747], .contexts [
        ⟨99423, false, false, [], []⟩,
        ⟨99422, true, false, [36160], [13]⟩,
        ⟨24831, true, false, [], [13]⟩,
        ⟨99421, false, false, [36160], [84101, 9, 13]⟩,
        ⟨45503, true, false, [36160, 36137], [9, 13]⟩,
        ⟨99420, true, false, [36160, 36137], [9, 13]⟩,
        ⟨38221, true, false, [36160, 36137], [9, 13]⟩,
        ⟨99400, true, false, [36160], [13, 9, 13]⟩,
        ⟨475, false, false, [36160, 96747], []⟩,
        ⟨99408, false, false, [36160], []⟩,
        ⟨99410, false, false, [36160], []⟩,
        ⟨99425, true, false, [], [96747]⟩,
        ⟨99425, true, false, [], [96747]⟩,
        ⟨99424, true, false, [], [96747]⟩
      ]⟩,
    ⟨[36143, 84329], [36143, 84329], .contexts []⟩,
    ⟨[36143, 84329], [36143, 84329], .contexts []⟩,
    ⟨[96745, 9], [36143, 84329], .contexts [
        ⟨99403, false, false, [], []⟩,
        ⟨99404, false, false, [], []⟩,
        ⟨99427, false, false, [], []⟩,
        ⟨99428, false, false, [], []⟩,
        ⟨99428, false, false, [], []⟩
      ]⟩,
    ⟨[36165], [36143, 21243], .source 18147⟩,
    ⟨[85595, 3], [85595, 3], .contexts []⟩,
    ⟨[96745], [96745], .contexts []⟩,
    ⟨[36167], [36164], .source 18148⟩,
    ⟨[36164], [36164], .contexts []⟩,
    ⟨[85595, 3], [36167, 96745], .contexts [
        ⟨99431, false, false, [], []⟩,
        ⟨99430, false, false, [36164], [85595, 3]⟩,
        ⟨44594, true, false, [36164, 36143], [3]⟩,
        ⟨25880, true, false, [36164, 36143], [9, 3]⟩,
        ⟨99429, true, false, [36164], [3, 9, 3]⟩,
        ⟨1439, false, false, [36164, 96745], []⟩,
        ⟨99432, false, false, [36164], []⟩,
        ⟨99434, true, false, [], [96745]⟩,
        ⟨99434, true, false, [], [96745]⟩,
        ⟨99433, true, false, [], [96745]⟩
      ]⟩,
    ⟨[36169], [36143, 17027], .source 18149⟩,
    ⟨[36171], [36169, 36145], .source 18150⟩,
    ⟨[36171, 96743], [36171, 96743], .contexts []⟩,
    ⟨[96745], [36171, 96743], .contexts [
        ⟨99432, false, false, [], []⟩,
        ⟨457, true, false, [96745], []⟩,
        ⟨99429, false, false, [], [5, 9, 5]⟩,
        ⟨25882, false, false, [36143], [9, 5]⟩,
        ⟨41257, false, false, [36143], [9, 5]⟩,
        ⟨99436, true, false, [], [84329, 9, 5]⟩,
        ⟨99406, false, false, [36169], [5]⟩,
        ⟨99437, true, false, [], [96745, 5]⟩,
        ⟨99293, false, false, [36171], []⟩,
        ⟨99438, false, false, [], []⟩
      ]⟩,
    ⟨[36173], [36170], .source 18151⟩,
    ⟨[36170], [36170], .contexts []⟩,
    ⟨[36175], [36173, 36143], .source 18152⟩,
    ⟨[96745], [36171, 96743], .contexts [
        ⟨99439, false, false, [], []⟩
      ]⟩,
    ⟨[96745], [36171, 96743], .contexts [
        ⟨99443, false, false, [], []⟩,
        ⟨99438, false, false, [], []⟩
      ]⟩,
    ⟨[36177], [36173, 36165], .source 18153⟩,
    ⟨[36177, 85597], [36177, 85597], .contexts []⟩,
    ⟨[36179], [36176], .source 18154⟩,
    ⟨[96739], [36177, 85597], .contexts [
        ⟨99447, false, false, [36178], [96739]⟩,
        ⟨13, false, false, [36178, 36176], [96739]⟩,
        ⟨99300, true, false, [36178, 36176], []⟩,
        ⟨99286, true, false, [36178, 36176], []⟩,
        ⟨99289, true, false, [36178, 36176], [1]⟩,
        ⟨99444, true, false, [36178, 36176, 36170], [3, 1]⟩,
        ⟨99435, true, false, [36178, 36176, 36170, 36166], [3, 1]⟩,
        ⟨20, false, false, [36178, 36176, 36170, 36166, 85595], [1]⟩,
        ⟨99433, false, true, [36178, 36176, 36170], [85595, 1]⟩,
        ⟨99440, true, false, [36178, 36176], [36165, 85595, 1]⟩,
        ⟨99445, true, false, [36178, 36176], [85595, 1]⟩,
        ⟨32642, false, false, [36178], []⟩,
        ⟨99446, false, false, [36178, 36176], []⟩,
        ⟨99447, false, true, [], [85597]⟩
      ]⟩,
    ⟨[36181], [36177, 27921], .source 18155⟩,
    ⟨[36183], [36180], .source 18156⟩,
    ⟨[36185], [36181, 34261], .source 18157⟩,
    ⟨[96737, 13], [36185, 89333], .contexts [
        ⟨99450, false, false, [36182], [96737, 13]⟩,
        ⟨13, false, false, [36182, 36180], [96737, 13]⟩,
        ⟨99301, true, false, [36182, 36180], [13]⟩,
        ⟨99283, true, false, [36182, 36180], [13]⟩,
        ⟨99448, false, false, [36182, 36180], [15, 13]⟩,
        ⟨99446, false, false, [36182, 36180], [15, 13]⟩,
        ⟨72122, true, false, [36182, 36180, 36177, 27922], [15, 13]⟩,
        ⟨1, false, false, [36182, 36180, 36177, 27922, 90373], [13]⟩,
        ⟨72123, true, false, [36182, 36180, 36177], [90373, 13]⟩,
        ⟨99449, true, false, [36182, 36180], [90373, 13]⟩,
        ⟨99450, false, true, [], [90373, 13]⟩,
        ⟨93274, false, false, [36181], []⟩,
        ⟨99451, true, false, [], [89333]⟩
      ]⟩,
    ⟨[36187], [36184], .source 18158⟩,
    ⟨[36187], [36184], .contexts [
        ⟨99453, false, false, [], []⟩
      ]⟩,
    ⟨[36185], [36186], .contexts [
        ⟨99453, true, true, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1554. -/
def y322TCIndexRaw1554 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[36184], [36184], .contexts []⟩,
    ⟨[89333, 1], [36187, 96733], .contexts [
        ⟨99455, false, false, [36184], [89333, 1]⟩,
        ⟨99452, true, false, [36184, 36186, 36184], [1]⟩,
        ⟨99280, false, false, [36184, 36186, 36184], [1]⟩,
        ⟨99302, false, false, [36184, 36186, 36184], [1]⟩,
        ⟨13, true, false, [36184, 36186, 36184], [96735, 1]⟩,
        ⟨99454, true, false, [36184, 36186], [96735, 1]⟩,
        ⟨99277, false, false, [36184], []⟩,
        ⟨99304, false, false, [36184], []⟩,
        ⟨99456, true, false, [], [96733]⟩,
        ⟨99456, true, false, [], [96733]⟩,
        ⟨99454, true, false, [], [96733]⟩
      ]⟩,
    ⟨[36149, 96747], [36149, 96747], .contexts []⟩,
    ⟨[36189], [22795, 16869], .source 18159⟩,
    ⟨[36191], [36147, 36189], .source 18160⟩,
    ⟨[96747, 11], [36191, 92579], .contexts [
        ⟨99458, true, false, [36148], [11]⟩,
        ⟨99458, true, false, [36148], [11]⟩,
        ⟨99413, true, false, [36148], [11]⟩,
        ⟨99409, true, false, [36148], [11]⟩,
        ⟨144, false, false, [36148, 88461], []⟩,
        ⟨145, false, false, [36148, 88461], []⟩,
        ⟨72108, false, false, [36148], [3]⟩,
        ⟨73281, false, false, [36148, 22795], []⟩,
        ⟨99459, true, false, [36148], [92579]⟩,
        ⟨73285, false, false, [36148, 36189], []⟩,
        ⟨99411, false, true, [], [36189, 92579]⟩,
        ⟨99460, true, false, [], [92579]⟩
      ]⟩,
    ⟨[36193], [36190], .source 18161⟩,
    ⟨[36159, 96747], [36159, 96747], .contexts []⟩,
    ⟨[36195], [36159, 36171], .source 18162⟩,
    ⟨[96743, 7], [96743, 7], .contexts []⟩,
    ⟨[36197], [36194], .source 18163⟩,
    ⟨[36194], [36194], .contexts []⟩,
    ⟨[96743, 7], [36197, 85705], .contexts [
        ⟨99465, false, false, [], []⟩,
        ⟨99464, false, false, [36194], [96743, 7]⟩,
        ⟨99444, true, false, [36194, 36159], [7]⟩,
        ⟨99297, true, false, [36194, 36159], [7]⟩,
        ⟨99463, true, false, [36194], [1, 7]⟩,
        ⟨99463, true, false, [36194], [1, 7]⟩,
        ⟨99419, true, false, [36194], [1, 7]⟩,
        ⟨99416, true, false, [36194], [1, 7]⟩,
        ⟨502, false, false, [36194, 85707], []⟩,
        ⟨46605, false, false, [36194], []⟩,
        ⟨46604, false, false, [36194], []⟩,
        ⟨46607, false, false, [36194], []⟩,
        ⟨99467, true, false, [], [85705]⟩,
        ⟨99467, true, false, [], [85705]⟩,
        ⟨99466, true, false, [], [85705]⟩
      ]⟩,
    ⟨[36195], [36196], .contexts [
        ⟨99466, true, true, [], []⟩
      ]⟩,
    ⟨[36163, 96747], [36163, 96747], .contexts []⟩,
    ⟨[36199], [36163, 36171], .source 18164⟩,
    ⟨[24137, 92577], [24137, 92577], .contexts []⟩,
    ⟨[36201], [24137, 25507], .source 18165⟩,
    ⟨[36203], [36201, 25515], .source 18166⟩,
    ⟨[96743, 13], [96743, 13], .contexts []⟩,
    ⟨[36205], [36198], .source 18167⟩,
    ⟨[36207], [36205, 36203], .source 18168⟩,
    ⟨[96743, 13], [36207, 90731], .contexts [
        ⟨99475, false, false, [], []⟩,
        ⟨99471, false, false, [36198], [96743, 13]⟩,
        ⟨99444, true, false, [36198, 36163], [13]⟩,
        ⟨99297, true, false, [36198, 36163], [13]⟩,
        ⟨99470, true, false, [36198], [1, 13]⟩,
        ⟨99470, true, false, [36198], [1, 13]⟩,
        ⟨99426, true, false, [36198], [1, 13]⟩,
        ⟨99423, true, false, [36198], [1, 13]⟩,
        ⟨1968, false, false, [36198, 84103], []⟩,
        ⟨248, false, false, [36198, 84103], []⟩,
        ⟨73253, false, false, [36198], [13, 1]⟩,
        ⟨99472, false, false, [36198], [13, 1]⟩,
        ⟨99472, false, false, [36198], [13, 1]⟩,
        ⟨73258, false, false, [36198, 24137], [1]⟩,
        ⟨99473, true, false, [36198], [90735, 1]⟩,
        ⟨62503, false, false, [36198, 36201], []⟩,
        ⟨62752, false, false, [36198, 36201], []⟩,
        ⟨99474, true, false, [36198], [90731]⟩,
        ⟨62757, false, false, [36198, 36203], []⟩,
        ⟨99476, true, false, [], [36203, 90731]⟩,
        ⟨99477, true, false, [], [90731]⟩
      ]⟩,
    ⟨[36209], [36206], .source 18169⟩,
    ⟨[36167, 96745], [36167, 36171, 96743], .contexts [
        ⟨99444, false, false, [36167], []⟩
      ]⟩,
    ⟨[36211], [36167, 36171], .source 18170⟩,
    ⟨[36213], [36211, 36207], .source 18171⟩,
    ⟨[36215], [36213, 25523], .source 18172⟩,
    ⟨[90727, 13], [90727, 13], .contexts []⟩,
    ⟨[36217], [36214], .source 18173⟩,
    ⟨[36217], [36214], .contexts [
        ⟨99485, false, false, [], []⟩
      ]⟩,
    ⟨[36214], [36214], .contexts []⟩,
    ⟨[36217], [36214], .contexts [
        ⟨99486, false, false, [], []⟩,
        ⟨99487, false, false, [], []⟩,
        ⟨99487, false, false, [], []⟩
      ]⟩,
    ⟨[90727, 13], [36217, 85595], .contexts [
        ⟨99484, false, false, [], []⟩,
        ⟨99483, false, false, [36214], [90727, 13]⟩,
        ⟨62766, true, false, [36214, 36213], [13]⟩,
        ⟨62496, true, false, [36214, 36213], [13]⟩,
        ⟨99482, false, false, [36214], [90731, 3, 13]⟩,
        ⟨99478, true, false, [36214, 36211], [3, 13]⟩,
        ⟨99481, false, false, [36214], [96743, 13, 3, 13]⟩,
        ⟨99480, true, false, [36214], [13, 3, 13]⟩,
        ⟨99435, true, false, [36214], [13, 3, 13]⟩,
        ⟨99431, true, false, [36214], [13, 3, 13]⟩,
        ⟨1930, false, false, [36214, 85595], []⟩,
        ⟨50612, false, false, [36214], []⟩,
        ⟨99488, true, false, [], [85595]⟩
      ]⟩,
    ⟨[36215], [36216], .contexts [
        ⟨99485, true, true, [], []⟩
      ]⟩,
    ⟨[36219], [36171, 36197], .source 18174⟩,
    ⟨[36197, 85705], [36197, 85705], .contexts []⟩,
    ⟨[36197, 85705], [36197, 85705], .contexts []⟩,
    ⟨[96743, 7], [36197, 85705], .contexts [
        ⟨99465, false, false, [], []⟩,
        ⟨99468, false, false, [], []⟩,
        ⟨99492, false, false, [], []⟩,
        ⟨99493, false, false, [], []⟩,
        ⟨99493, false, false, [], []⟩
      ]⟩,
    ⟨[85703, 7], [85703, 7], .contexts []⟩,
    ⟨[85703], [85703], .contexts []⟩,
    ⟨[36221], [36218], .source 18175⟩,
    ⟨[36223], [36221, 36197], .source 18176⟩,
    ⟨[85703, 7], [36223, 85703], .contexts [
        ⟨99495, false, false, [], []⟩,
        ⟨33054, true, false, [], [7]⟩,
        ⟨99491, false, false, [36218], [85705, 5, 7]⟩,
        ⟨99468, true, false, [36218, 36171], [5, 7]⟩,
        ⟨99438, true, false, [36218], [7, 5, 7]⟩,
        ⟨99438, true, false, [36218], [7, 5, 7]⟩,
        ⟨99444, true, false, [36218], [7, 5, 7]⟩,
        ⟨99291, true, false, [36218], [7, 5, 7]⟩,
        ⟨48805, false, false, [36218, 96743], []⟩,
        ⟨3273, false, false, [36218, 96743], []⟩,
        ⟨99494, false, false, [36218], [5]⟩,
        ⟨33054, false, false, [36218, 36197], []⟩,
        ⟨99496, false, false, [36218, 36197], []⟩,
        ⟨99497, true, false, [], [36197, 85703]⟩,
        ⟨99498, true, false, [], [85703]⟩
      ]⟩,
    ⟨[36215, 90727], [36215, 90727], .contexts []⟩,
    ⟨[85595, 13], [36215, 90727], .contexts [
        ⟨99489, true, false, [36216], [13]⟩,
        ⟨59, false, false, [36216, 90727], []⟩,
        ⟨99490, true, false, [], [90727]⟩,
        ⟨99500, false, false, [], []⟩,
        ⟨99500, false, false, [], []⟩
      ]⟩,
    ⟨[36215, 90723], [36215, 90723], .contexts []⟩,
    ⟨[36215, 90723], [36215, 90723], .contexts []⟩,
    ⟨[85591, 15], [85591, 15], .contexts []⟩,
    ⟨[36215], [36215], .contexts []⟩,
    ⟨[36215], [36215], .contexts []⟩,
    ⟨[85591, 15], [36215, 90723], .contexts [
        ⟨99504, false, false, [], []⟩,
        ⟨32636, true, false, [], [15]⟩,
        ⟨32636, true, false, [], [15]⟩,
        ⟨32687, true, false, [], [15]⟩,
        ⟨32686, true, false, [], [15]⟩,
        ⟨44619, true, false, [], [13, 15]⟩,
        ⟨3049, false, false, [85595], []⟩,
        ⟨261, false, false, [85595], []⟩,
        ⟨99501, false, false, [], [15, 13]⟩,
        ⟨62489, false, false, [36215], [13]⟩,
        ⟨62485, false, false, [36215], []⟩,
        ⟨99502, false, false, [], []⟩,
        ⟨99503, false, false, [], []⟩,
        ⟨99506, true, false, [], [90723]⟩,
        ⟨99505, true, false, [], [90723]⟩,
        ⟨13, true, false, [], [36215, 90723]⟩
      ]⟩,
    ⟨[36225], [21245, 36041], .source 18177⟩,
    ⟨[93399, 9], [93399, 9], .contexts []⟩,
    ⟨[36227], [36224], .source 18178⟩,
    ⟨[36229], [36227, 36215], .source 18179⟩,
    ⟨[93399, 9], [36229, 90727], .contexts [
        ⟨99509, false, false, [], []⟩,
        ⟨99508, false, false, [36224], [93399, 9]⟩,
        ⟨98843, true, false, [36224, 21245], [9]⟩,
        ⟨44617, true, false, [36224], [13, 9]⟩,
        ⟨511, false, false, [36224, 85595], []⟩,
        ⟨64, false, false, [36224, 85595], []⟩,
        ⟨99501, false, false, [36224], []⟩,
        ⟨99510, true, false, [], [36215, 90727]⟩,
        ⟨99511, true, false, [], [90727]⟩
      ]⟩,
    ⟨[36231], [36228], .source 18180⟩,
    ⟨[90727, 9], [36231, 93399], .contexts [
        ⟨99512, true, false, [36228], [9]⟩,
        ⟨46, false, false, [36228, 93399], []⟩,
        ⟨99513, true, false, [], [93399]⟩
      ]⟩,
    ⟨[36233], [34261, 36187], .source 18181⟩,
    ⟨[85589, 13], [85589, 13], .contexts []⟩,
    ⟨[96733], [96733], .contexts []⟩,
    ⟨[36235], [27921, 36233], .source 18182⟩,
    ⟨[85589, 13], [36235, 96733], .contexts [
        ⟨99516, false, false, [], []⟩,
        ⟨32634, true, false, [], [13]⟩,
        ⟨32637, true, false, [], [1, 13]⟩,
        ⟨72142, true, false, [27922], [13, 1, 13]⟩,
        ⟨72142, true, false, [27922], [13, 1, 13]⟩,
        ⟨72141, true, false, [27922], [13, 1, 13]⟩,
        ⟨72149, true, false, [27922], [13, 1, 13]⟩,
        ⟨919, false, false, [27922, 90373], []⟩,
        ⟨116, false, false, [27922, 90373], []⟩,
        ⟨93274, false, false, [27922], [1]⟩,
        ⟨93268, false, false, [27922], [1]⟩,
        ⟨93269, false, false, [27922], [1]⟩,
        ⟨93269, false, false, [27922], [1]⟩,
        ⟨99457, false, false, [27922, 34261], []⟩,
        ⟨99515, true, false, [27922], [96733]⟩,
        ⟨99517, false, false, [27922, 36233], []⟩,
        ⟨72146, true, false, [], [36233, 96733]⟩,
        ⟨99518, true, false, [], [96733]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1555. -/
def y322TCIndexRaw1555 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[36237], [36234], .source 18183⟩,
    ⟨[36239], [34247, 34215], .source 18184⟩,
    ⟨[36187, 96733], [36187, 96733], .contexts []⟩,
    ⟨[89333, 1], [36187, 96733], .contexts [
        ⟨99457, false, false, [], []⟩,
        ⟨99522, false, false, [], []⟩,
        ⟨99522, false, false, [], []⟩
      ]⟩,
    ⟨[89333, 0], [89333, 1], .contexts [
        ⟨9, false, false, [89333], []⟩
      ]⟩,
    ⟨[36239, 91473, 3], [36187, 96733], .contexts [
        ⟨66002, true, false, [36239], [3]⟩,
        ⟨99521, false, false, [], [91475, 1, 3]⟩,
        ⟨93203, true, false, [34247], [1, 3]⟩,
        ⟨93253, true, false, [], [3, 1, 3]⟩,
        ⟨93253, true, false, [], [3, 1, 3]⟩,
        ⟨93255, true, false, [], [3, 1, 3]⟩,
        ⟨55889, true, false, [], [3, 1, 3]⟩,
        ⟨55611, true, false, [], [1, 3, 1, 3]⟩,
        ⟨55611, true, false, [], [1, 3, 1, 3]⟩,
        ⟨55887, true, false, [], [1, 3, 1, 3]⟩,
        ⟨55886, true, false, [], [1, 3, 1, 3]⟩,
        ⟨1178, false, false, [89333], []⟩,
        ⟨99524, false, false, [], []⟩,
        ⟨99523, false, false, [], []⟩
      ]⟩,
    ⟨[91473, 3], [91473, 3], .contexts []⟩,
    ⟨[36241], [36238], .source 18185⟩,
    ⟨[36243], [36241, 36187], .source 18186⟩,
    ⟨[36245], [36242], .source 18187⟩,
    ⟨[36247], [34247, 36187], .source 18188⟩,
    ⟨[96733, 15], [96733, 15], .contexts []⟩,
    ⟨[36249], [36246], .source 18189⟩,
    ⟨[36251], [36249, 36187], .source 18190⟩,
    ⟨[36207, 90731], [36207, 90731], .contexts []⟩,
    ⟨[36253], [36207, 27045], .source 18191⟩,
    ⟨[85705, 13], [85705, 13], .contexts []⟩,
    ⟨[36255], [36195, 36253], .source 18192⟩,
    ⟨[85705, 13], [36255, 92029], .contexts [
        ⟨99536, false, false, [], []⟩,
        ⟨99494, true, false, [36196], [13]⟩,
        ⟨1056, false, false, [36196, 96743], []⟩,
        ⟨1057, false, false, [36196, 96743], []⟩,
        ⟨99475, false, false, [36196], [7]⟩,
        ⟨99478, false, false, [36196], [7]⟩,
        ⟨99534, false, false, [36196], [7]⟩,
        ⟨99534, false, false, [36196], [7]⟩,
        ⟨69181, false, false, [36196, 36207], []⟩,
        ⟨99535, true, false, [36196], [92029]⟩,
        ⟨77662, false, false, [36196, 36253], []⟩,
        ⟨99469, true, false, [], [36253, 92029]⟩,
        ⟨99537, true, false, [], [92029]⟩
      ]⟩,
    ⟨[36257], [36254], .source 18193⟩,
    ⟨[36223, 85703], [36223, 85703], .contexts []⟩,
    ⟨[85701, 7], [85701, 7], .contexts []⟩,
    ⟨[85701], [85701], .contexts []⟩,
    ⟨[36259], [36222], .source 18194⟩,
    ⟨[36222], [36222], .contexts []⟩,
    ⟨[36259], [36222], .contexts [
        ⟨99543, false, false, [], []⟩,
        ⟨99544, false, false, [], []⟩,
        ⟨99544, false, false, [], []⟩
      ]⟩,
    ⟨[85591, 15], [36215, 90723], .contexts [
        ⟨99504, false, false, [], []⟩,
        ⟨99507, false, false, [], []⟩,
        ⟨99502, false, false, [], []⟩,
        ⟨99503, false, false, [], []⟩,
        ⟨99503, false, false, [], []⟩
      ]⟩,
    ⟨[90721, 15], [90721, 15], .contexts []⟩,
    ⟨[90721, 15], [36217, 85589], .contexts [
        ⟨99547, false, false, [], []⟩,
        ⟨62481, true, false, [], [15]⟩,
        ⟨99546, true, false, [36214], [1, 15]⟩,
        ⟨1666, false, false, [36214, 85591], []⟩,
        ⟨9, false, false, [36214, 85591], []⟩,
        ⟨32688, false, false, [36214], []⟩,
        ⟨32689, false, false, [36214], []⟩,
        ⟨32633, false, false, [36214], []⟩,
        ⟨32633, false, false, [36214], []⟩,
        ⟨99488, true, false, [], [85589]⟩
      ]⟩,
    ⟨[22459, 88179], [22459, 88179], .contexts []⟩,
    ⟨[36261], [22459, 36051], .source 18195⟩,
    ⟨[36263], [36217, 36261], .source 18196⟩,
    ⟨[90723, 9], [36263, 93395], .contexts [
        ⟨99546, true, false, [36214], [9]⟩,
        ⟨45, false, false, [36214, 85591], []⟩,
        ⟨48, false, false, [36214, 85591], []⟩,
        ⟨48979, false, false, [36214], [15]⟩,
        ⟨48982, false, false, [36214], [15]⟩,
        ⟨99549, false, false, [36214], [15]⟩,
        ⟨99549, false, false, [36214], [15]⟩,
        ⟨98878, false, false, [36214, 22459], []⟩,
        ⟨99550, true, false, [36214], [93395]⟩,
        ⟨98872, false, false, [36214, 36261], []⟩,
        ⟨99486, true, false, [], [36261, 93395]⟩,
        ⟨99551, true, false, [], [93395]⟩
      ]⟩,
    ⟨[36265], [36262], .source 18197⟩,
    ⟨[36229, 90727], [36229, 90727], .contexts []⟩,
    ⟨[36229, 90727], [36229, 90727], .contexts []⟩,
    ⟨[93399, 9], [36229, 90727], .contexts [
        ⟨99509, false, false, [], []⟩,
        ⟨99512, false, false, [], []⟩,
        ⟨99554, false, false, [], []⟩,
        ⟨99555, false, false, [], []⟩,
        ⟨99555, false, false, [], []⟩
      ]⟩,
    ⟨[36229, 90725], [36229, 90725], .contexts []⟩,
    ⟨[36228], [36228], .contexts []⟩,
    ⟨[90725, 9], [36231, 93397], .contexts [
        ⟨99557, true, false, [36228], [9]⟩,
        ⟨62489, true, false, [], [9]⟩,
        ⟨99556, true, false, [36228], [15, 9]⟩,
        ⟨935, false, false, [36228, 93399], []⟩,
        ⟨98862, false, false, [36228], []⟩,
        ⟨98861, false, false, [36228], []⟩,
        ⟨98863, false, false, [36228], []⟩,
        ⟨99558, true, false, [], [93397]⟩,
        ⟨99558, true, false, [], [93397]⟩,
        ⟨99513, true, false, [], [93397]⟩
      ]⟩,
    ⟨[36229], [36230], .contexts [
        ⟨99513, true, true, [], []⟩
      ]⟩,
    ⟨[36235, 96733], [36235, 96733], .contexts []⟩,
    ⟨[36235, 96733], [36235, 96733], .contexts []⟩,
    ⟨[36234], [36234], .contexts []⟩,
    ⟨[36243, 96733], [36243, 96733], .contexts []⟩,
    ⟨[36243, 96731], [36243, 96731], .contexts []⟩,
    ⟨[36243, 96731, 3], [91473, 11], .contexts [
        ⟨99565, true, false, [], [3]⟩,
        ⟨99274, true, false, [36243], [3]⟩,
        ⟨99564, true, false, [], [11, 3]⟩,
        ⟨99564, true, false, [], [11, 3]⟩,
        ⟨99528, false, false, [], [96733, 11, 3]⟩,
        ⟨99527, false, false, [], [36187, 96733, 11, 3]⟩,
        ⟨99517, true, false, [36238, 36187], [11, 3]⟩,
        ⟨99525, true, false, [36238], [11, 3]⟩,
        ⟨99526, true, false, [], [11, 3]⟩,
        ⟨99526, true, false, [], [11, 3]⟩,
        ⟨545, false, false, [91473], []⟩,
        ⟨54, false, false, [91473], []⟩
      ]⟩,
    ⟨[96731, 3], [96731, 3], .contexts []⟩,
    ⟨[36242], [36242], .contexts []⟩,
    ⟨[96731, 3], [36245, 91471], .contexts [
        ⟨99567, false, false, [], []⟩,
        ⟨99566, false, false, [36242], []⟩,
        ⟨66042, false, false, [36242], []⟩,
        ⟨66043, false, false, [36242], []⟩,
        ⟨65998, false, false, [36242], []⟩,
        ⟨65998, false, false, [36242], []⟩,
        ⟨88447, false, false, [36242], []⟩,
        ⟨99568, true, false, [], [91471]⟩,
        ⟨99568, true, false, [], [91471]⟩,
        ⟨99529, true, false, [], [91471]⟩
      ]⟩,
    ⟨[36251, 96733], [36251, 96733], .contexts []⟩,
    ⟨[96733, 15, 11], [36251, 96731], .contexts [
        ⟨99531, false, false, [], [11]⟩,
        ⟨99531, false, false, [], [11]⟩,
        ⟨99530, false, false, [36246], [96733, 15, 11]⟩,
        ⟨99457, true, false, [36246, 34247], [15, 11]⟩,
        ⟨93295, true, false, [36246], [1, 15, 11]⟩,
        ⟨1666, false, false, [36246, 89333], [11]⟩,
        ⟨99524, false, false, [36246], [11]⟩,
        ⟨99523, false, false, [36246], [11]⟩,
        ⟨99517, false, false, [36246, 36187], [11]⟩,
        ⟨99532, true, false, [], [36187, 96733, 11]⟩,
        ⟨99533, true, false, [], [96733, 11]⟩,
        ⟨99570, false, false, [], [11]⟩,
        ⟨99570, false, false, [], [11]⟩,
        ⟨99274, false, false, [36251], []⟩
      ]⟩,
    ⟨[96731, 15], [96731, 15], .contexts []⟩,
    ⟨[36267], [36250], .source 18198⟩,
    ⟨[36267], [36267], .contexts []⟩,
    ⟨[36250], [36250], .contexts []⟩,
    ⟨[36267], [36250], .contexts [
        ⟨99574, false, false, [], []⟩,
        ⟨99573, false, false, [], []⟩,
        ⟨99575, false, false, [], []⟩,
        ⟨99575, false, false, [], []⟩
      ]⟩,
    ⟨[36255, 92029], [36255, 92029], .contexts []⟩,
    ⟨[92027, 13], [92027, 13], .contexts []⟩,
    ⟨[36254], [36254], .contexts []⟩,
    ⟨[92027, 13], [36257, 85703], .contexts [
        ⟨99578, false, false, [], []⟩,
        ⟨68964, true, false, [], [13]⟩,
        ⟨99577, true, false, [36254], [5, 13]⟩,
        ⟨99577, true, false, [36254], [5, 13]⟩,
        ⟨99538, true, false, [36254], [5, 13]⟩,
        ⟨99536, true, false, [36254], [5, 13]⟩,
        ⟨1136, false, false, [36254, 85705], []⟩,
        ⟨29, false, false, [36254, 85705], []⟩,
        ⟨33092, false, false, [36254], []⟩,
        ⟨33093, false, false, [36254], []⟩,
        ⟨33053, false, false, [36254], []⟩,
        ⟨33053, false, false, [36254], []⟩,
        ⟨99496, false, false, [36254], []⟩,
        ⟨99579, true, false, [], [85703]⟩,
        ⟨99579, true, false, [], [85703]⟩,
        ⟨99539, true, false, [], [85703]⟩
      ]⟩,
    ⟨[36259, 85701], [36259, 85701], .contexts []⟩,
    ⟨[85701, 7], [36259, 85701], .contexts [
        ⟨99541, false, false, [], []⟩,
        ⟨99541, false, false, [], []⟩,
        ⟨33050, true, false, [], [7]⟩,
        ⟨99540, true, false, [36222], [3, 7]⟩,
        ⟨99540, true, false, [36222], [3, 7]⟩,
        ⟨99499, true, false, [36222], [3, 7]⟩,
        ⟨99495, true, false, [36222], [3, 7]⟩,
        ⟨14911, false, false, [36222, 85703], []⟩,
        ⟨21, false, false, [36222, 85703], []⟩,
        ⟨33094, false, false, [36222], []⟩,
        ⟨33095, false, false, [36222], []⟩,
        ⟨33049, false, false, [36222], []⟩,
        ⟨33049, false, false, [36222], []⟩,
        ⟨99542, false, false, [36222], []⟩,
        ⟨99545, true, false, [], [85701]⟩,
        ⟨99581, false, false, [], []⟩,
        ⟨99581, false, false, [], []⟩
      ]⟩,
    ⟨[85699, 7], [85699, 7], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1556. -/
def y322TCIndexRaw1556 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85699], [85699], .contexts []⟩,
    ⟨[36258], [36258], .contexts []⟩,
    ⟨[36223], [36258], .contexts [
        ⟨99543, true, true, [], []⟩,
        ⟨99585, false, false, [], []⟩,
        ⟨99585, false, false, [], []⟩
      ]⟩,
    ⟨[85699, 7], [36223, 85699], .contexts [
        ⟨99583, false, false, [], []⟩,
        ⟨33046, true, false, [], [7]⟩,
        ⟨99582, true, false, [36258], [1, 7]⟩,
        ⟨502, false, false, [36258, 85701], []⟩,
        ⟨9, false, false, [36258, 85701], []⟩,
        ⟨33096, false, false, [36258], []⟩,
        ⟨33097, false, false, [36258], []⟩,
        ⟨33045, false, false, [36258], []⟩,
        ⟨33045, false, false, [36258], []⟩,
        ⟨99584, false, false, [36258], []⟩,
        ⟨99586, true, false, [], [85699]⟩
      ]⟩,
    ⟨[36217, 85589], [36217, 85589], .contexts []⟩,
    ⟨[36217, 85589], [36217, 85589], .contexts []⟩,
    ⟨[85587, 15], [85587, 15], .contexts []⟩,
    ⟨[36215], [36215], .contexts []⟩,
    ⟨[36215], [36216], .contexts [
        ⟨99490, false, false, [], []⟩
      ]⟩,
    ⟨[36216], [36216], .contexts []⟩,
    ⟨[36215], [36216], .contexts [
        ⟨99591, false, false, [], []⟩,
        ⟨99592, false, false, [], []⟩,
        ⟨99593, false, false, [], []⟩,
        ⟨99593, false, false, [], []⟩
      ]⟩,
    ⟨[85587, 15], [36215, 90719], .contexts [
        ⟨99590, false, false, [], []⟩,
        ⟨32631, true, false, [], [15]⟩,
        ⟨99589, true, false, [36216], [11, 15]⟩,
        ⟨99589, true, false, [36216], [11, 15]⟩,
        ⟨99588, true, false, [36216], [11, 15]⟩,
        ⟨99548, true, false, [36216], [11, 15]⟩,
        ⟨99547, true, false, [36216], [11, 15]⟩,
        ⟨2046, false, false, [36216, 90721], []⟩,
        ⟨54, false, false, [36216, 90721], []⟩,
        ⟨62544, false, false, [36216], []⟩,
        ⟨62545, false, false, [36216], []⟩,
        ⟨62478, false, false, [36216], []⟩,
        ⟨62478, false, false, [36216], []⟩,
        ⟨99594, true, false, [], [90719]⟩
      ]⟩,
    ⟨[96731, 9], [96729], .contexts [
        ⟨99307, false, false, [], []⟩,
        ⟨99308, false, false, [], []⟩,
        ⟨99270, false, false, [], []⟩,
        ⟨99270, false, false, [], []⟩
      ]⟩,
    ⟨[96731, 8], [96731, 9], .contexts [
        ⟨47, false, false, [96731], []⟩
      ]⟩,
    ⟨[96729], [96729], .contexts []⟩,
    ⟨[36245, 91471], [36245, 91471], .contexts []⟩,
    ⟨[36269], [36245, 34251], .source 18199⟩,
    ⟨[91467, 3], [91467, 3], .contexts []⟩,
    ⟨[36271], [36268], .source 18200⟩,
    ⟨[36268], [36268], .contexts []⟩,
    ⟨[91467, 3], [36271, 96729], .contexts [
        ⟨99601, false, false, [], []⟩,
        ⟨99600, false, false, [36268], [91467, 3]⟩,
        ⟨93235, true, false, [36268, 36245], [3]⟩,
        ⟨65996, true, false, [36268, 36245], [3]⟩,
        ⟨99599, true, false, [36268], [9, 3]⟩,
        ⟨99599, true, false, [36268], [9, 3]⟩,
        ⟨99569, true, false, [36268], [9, 3]⟩,
        ⟨99567, true, false, [36268], [9, 3]⟩,
        ⟨573, false, false, [36268, 96731], []⟩,
        ⟨99597, false, false, [36268], []⟩,
        ⟨99596, false, false, [36268], []⟩,
        ⟨99598, false, false, [36268], []⟩,
        ⟨99603, true, false, [], [96729]⟩,
        ⟨99603, true, false, [], [96729]⟩,
        ⟨99602, true, false, [], [96729]⟩
      ]⟩,
    ⟨[36269], [36270], .contexts [
        ⟨99602, true, true, [], []⟩
      ]⟩,
    ⟨[36267, 96731], [36267, 96731], .contexts []⟩,
    ⟨[36267, 96729, 15], [96731, 9], .contexts [
        ⟨99271, true, false, [36267], [15]⟩,
        ⟨99606, true, false, [], [9, 15]⟩,
        ⟨99606, true, false, [], [9, 15]⟩,
        ⟨99576, false, false, [], [96731, 9, 15]⟩,
        ⟨99273, true, false, [36250], [9, 15]⟩,
        ⟨99273, true, false, [36250], [9, 15]⟩,
        ⟨99306, true, false, [36250], [9, 15]⟩,
        ⟨99305, true, false, [36250], [9, 15]⟩,
        ⟨54, true, false, [36250, 96733], [9, 15]⟩,
        ⟨2046, true, false, [36250, 96733], [9, 15]⟩,
        ⟨99571, false, false, [36250], [15, 9, 15]⟩,
        ⟨99572, true, false, [], [9, 15]⟩,
        ⟨99572, true, false, [], [9, 15]⟩,
        ⟨1671, false, false, [96731], []⟩,
        ⟨99597, false, false, [], []⟩
      ]⟩,
    ⟨[96729, 15], [96729, 15], .contexts []⟩,
    ⟨[36266], [36266], .contexts []⟩,
    ⟨[36251], [36266], .contexts [
        ⟨99573, true, true, [], []⟩,
        ⟨99609, false, false, [], []⟩,
        ⟨99609, false, false, [], []⟩
      ]⟩,
    ⟨[36257, 85703], [36257, 85703], .contexts []⟩,
    ⟨[36257, 85703], [36257, 85703], .contexts []⟩,
    ⟨[85701, 13], [85701, 13], .contexts []⟩,
    ⟨[36256], [36256], .contexts []⟩,
    ⟨[85701, 13], [36255, 92025], .contexts [
        ⟨99613, false, false, [], []⟩,
        ⟨33050, true, false, [], [13]⟩,
        ⟨99612, true, false, [36256], [3, 13]⟩,
        ⟨99612, true, false, [36256], [3, 13]⟩,
        ⟨99611, true, false, [36256], [3, 13]⟩,
        ⟨99580, true, false, [36256], [3, 13]⟩,
        ⟨99578, true, false, [36256], [3, 13]⟩,
        ⟨1132, false, false, [36256, 92027], []⟩,
        ⟨21, false, false, [36256, 92027], []⟩,
        ⟨69005, false, false, [36256], []⟩,
        ⟨69006, false, false, [36256], []⟩,
        ⟨68959, false, false, [36256], []⟩,
        ⟨68959, false, false, [36256], []⟩,
        ⟨69183, false, false, [36256], []⟩,
        ⟨99614, true, false, [], [92025]⟩,
        ⟨99614, true, false, [], [92025]⟩,
        ⟨99539, false, true, [], [92025]⟩
      ]⟩,
    ⟨[92025, 13], [36257, 85701], .contexts [
        ⟨99615, true, false, [36254], [13]⟩,
        ⟨59, false, false, [36254, 85701], []⟩,
        ⟨99539, true, false, [], [85701]⟩
      ]⟩,
    ⟨[36223, 85699], [36223, 85699], .contexts []⟩,
    ⟨[36223, 85699], [36223, 85699], .contexts []⟩,
    ⟨[85699, 15], [85697], .contexts [
        ⟨33098, false, false, [], []⟩,
        ⟨33099, false, false, [], []⟩,
        ⟨33041, false, false, [], []⟩,
        ⟨33041, false, false, [], []⟩
      ]⟩,
    ⟨[85697, 7], [85697, 7], .contexts []⟩,
    ⟨[85697], [85697], .contexts []⟩,
    ⟨[36215, 90719], [36215, 90719], .contexts []⟩,
    ⟨[36215, 90719], [36215, 90719], .contexts []⟩,
    ⟨[90717, 15], [90717, 15], .contexts []⟩,
    ⟨[36271, 96729], [36271, 96729], .contexts []⟩,
    ⟨[36273], [34251, 36271], .source 18201⟩,
    ⟨[96727, 3], [96727, 3], .contexts []⟩,
    ⟨[96727], [96727], .contexts []⟩,
    ⟨[36275], [36269, 36273], .source 18202⟩,
    ⟨[36251, 96729], [36251, 96729], .contexts []⟩,
    ⟨[96727, 15], [96727, 15], .contexts []⟩,
    ⟨[96727, 15], [36250, 96727], .contexts [
        ⟨99631, false, false, [], []⟩,
        ⟨99268, true, false, [], [15]⟩,
        ⟨99630, true, false, [36250], [1, 15]⟩,
        ⟨99630, true, false, [36250], [1, 15]⟩,
        ⟨99610, false, false, [36250], [96729, 1, 15]⟩,
        ⟨99598, true, false, [36250, 36266], [1, 15]⟩,
        ⟨99596, true, false, [36250, 36266], [1, 15]⟩,
        ⟨99607, true, false, [36250, 36266], [1, 15]⟩,
        ⟨99608, true, false, [36250], [1, 15]⟩,
        ⟨99608, true, false, [36250], [1, 15]⟩,
        ⟨1666, false, false, [36250, 96729], []⟩,
        ⟨9, false, false, [36250, 96729], []⟩,
        ⟨99309, false, false, [36250], []⟩,
        ⟨99310, false, false, [36250], []⟩,
        ⟨99267, false, false, [36250], []⟩,
        ⟨99267, false, false, [36250], []⟩,
        ⟨99628, false, false, [36250], []⟩
      ]⟩,
    ⟨[36255, 92025], [36255, 92025], .contexts []⟩,
    ⟨[36255, 92025], [36255, 92025], .contexts []⟩,
    ⟨[36277], [36255, 32247], .source 18203⟩,
    ⟨[36279], [36277, 36257], .source 18204⟩,
    ⟨[85701, 13, 1, 13, 1, 13], [36279, 85701], .contexts [
        ⟨99613, false, false, [], [1, 13, 1, 13]⟩,
        ⟨99615, false, false, [], [1, 13, 1, 13]⟩,
        ⟨99633, false, false, [], [1, 13, 1, 13]⟩,
        ⟨99634, false, false, [], [1, 13, 1, 13]⟩,
        ⟨99634, false, false, [], [1, 13, 1, 13]⟩,
        ⟨68957, false, false, [36255], [13, 1, 13]⟩,
        ⟨87496, false, false, [36255], [1, 13]⟩,
        ⟨99635, true, false, [], [92023, 1, 13]⟩,
        ⟨68955, false, false, [36277], [13]⟩,
        ⟨99616, false, false, [36277], []⟩,
        ⟨99636, true, false, [], [85701]⟩
      ]⟩,
    ⟨[36279, 85699], [36279, 85699], .contexts []⟩,
    ⟨[36279], [36279], .contexts []⟩,
    ⟨[36279], [36279], .contexts []⟩,
    ⟨[85701], [36279, 85699], .contexts [
        ⟨99542, false, false, [], []⟩,
        ⟨245, true, false, [85701], []⟩,
        ⟨99637, false, false, [], [1]⟩,
        ⟨33046, false, false, [36279], []⟩,
        ⟨99638, false, false, [], []⟩,
        ⟨99640, true, false, [], [85699]⟩,
        ⟨99639, true, false, [], [85699]⟩
      ]⟩,
    ⟨[36281], [36278], .source 18205⟩,
    ⟨[36281], [36278], .contexts [
        ⟨99642, false, false, [], []⟩
      ]⟩,
    ⟨[36278], [36278], .contexts []⟩,
    ⟨[85701], [36279, 85699], .contexts [
        ⟨99641, false, false, [], []⟩
      ]⟩,
    ⟨[85701], [36279, 85699], .contexts [
        ⟨99645, false, false, [], []⟩,
        ⟨99638, false, false, [], []⟩
      ]⟩,
    ⟨[36283], [36281, 36255], .source 18206⟩]

/-- Exact literal claimed equations and contextual derivations, block 1557. -/
def y322TCIndexRaw1557 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85699, 13], [36283, 92025], .contexts [
        ⟨99641, true, false, [36278], [13]⟩,
        ⟨99615, false, false, [36278], []⟩,
        ⟨99633, false, false, [36278], []⟩,
        ⟨99642, true, false, [], [36255, 92025]⟩,
        ⟨99647, true, false, [], [92025]⟩
      ]⟩,
    ⟨[36283, 92025], [36283, 92025], .contexts []⟩,
    ⟨[36285], [36283, 31717], .source 18207⟩,
    ⟨[36287], [36285, 32251], .source 18208⟩,
    ⟨[94991, 15], [94991, 15], .contexts []⟩,
    ⟨[85695], [85695], .contexts []⟩,
    ⟨[36289], [36286], .source 18209⟩,
    ⟨[36289], [36289], .contexts []⟩,
    ⟨[36286], [36286], .contexts []⟩,
    ⟨[36289], [36286], .contexts [
        ⟨99655, false, false, [], []⟩,
        ⟨99654, false, false, [], []⟩,
        ⟨99656, false, false, [], []⟩,
        ⟨99656, false, false, [], []⟩
      ]⟩,
    ⟨[94991, 15], [36289, 85695], .contexts [
        ⟨99652, false, false, [], []⟩,
        ⟨99651, false, false, [36286], [94991, 15]⟩,
        ⟨87504, true, false, [36286, 36285], [15]⟩,
        ⟨99650, false, false, [36286], [94677, 13, 15]⟩,
        ⟨85888, true, false, [36286, 36283], [13, 15]⟩,
        ⟨99649, true, false, [36286], [15, 13, 15]⟩,
        ⟨99649, true, false, [36286], [15, 13, 15]⟩,
        ⟨99648, true, false, [36286], [15, 13, 15]⟩,
        ⟨2022, false, false, [36286, 85699], []⟩,
        ⟨89, false, false, [36286, 85699], []⟩,
        ⟨99619, false, false, [36286], [13]⟩,
        ⟨33101, false, false, [36286], []⟩,
        ⟨33102, false, false, [36286], []⟩,
        ⟨33038, false, false, [36286], []⟩,
        ⟨33038, false, false, [36286], []⟩,
        ⟨99653, false, false, [36286], []⟩,
        ⟨99657, true, false, [], [85695]⟩
      ]⟩,
    ⟨[36287], [36288], .contexts [
        ⟨99654, true, true, [], []⟩
      ]⟩,
    ⟨[85695, 15], [36287, 94991], .contexts [
        ⟨99658, true, false, [36288], [15]⟩,
        ⟨1, false, false, [36288, 94991], []⟩,
        ⟨99659, true, false, [], [94991]⟩
      ]⟩,
    ⟨[36259, 85697], [36259, 85697], .contexts []⟩,
    ⟨[85697, 7], [36259, 85697], .contexts [
        ⟨99620, false, false, [], []⟩,
        ⟨99620, false, false, [], []⟩,
        ⟨33042, true, false, [], [7]⟩,
        ⟨99618, true, false, [36222], [15, 7]⟩,
        ⟨99618, true, false, [36222], [15, 7]⟩,
        ⟨99617, true, false, [36222], [15, 7]⟩,
        ⟨99587, true, false, [36222], [15, 7]⟩,
        ⟨99583, true, false, [36222], [15, 7]⟩,
        ⟨18155, false, false, [36222, 85699], []⟩,
        ⟨10, false, false, [36222, 85699], []⟩,
        ⟨99619, false, false, [36222], []⟩,
        ⟨99621, false, false, [36222], []⟩,
        ⟨99545, true, false, [], [85697]⟩,
        ⟨99661, false, false, [], []⟩,
        ⟨99661, false, false, [], []⟩
      ]⟩,
    ⟨[85697, 13], [85695], .contexts [
        ⟨33101, false, false, [], []⟩,
        ⟨33102, false, false, [], []⟩,
        ⟨33038, false, false, [], []⟩,
        ⟨33038, false, false, [], []⟩
      ]⟩,
    ⟨[85695, 7], [85695, 7], .contexts []⟩,
    ⟨[85695, 7], [36223, 85695], .contexts [
        ⟨99664, false, false, [], []⟩,
        ⟨33039, true, false, [], [7]⟩,
        ⟨99662, true, false, [36258], [13, 7]⟩,
        ⟨518, false, false, [36258, 85697], []⟩,
        ⟨64, false, false, [36258, 85697], []⟩,
        ⟨99663, false, false, [36258], []⟩,
        ⟨99653, false, false, [36258], []⟩,
        ⟨99586, true, false, [], [85695]⟩
      ]⟩,
    ⟨[36217, 85585], [36217, 85585], .contexts []⟩,
    ⟨[90717, 15], [36217, 85585], .contexts [
        ⟨99624, false, false, [], []⟩,
        ⟨99624, false, false, [], []⟩,
        ⟨62475, true, false, [], [15]⟩,
        ⟨99623, true, false, [36214], [9, 15]⟩,
        ⟨99623, true, false, [36214], [9, 15]⟩,
        ⟨99622, true, false, [36214], [9, 15]⟩,
        ⟨99595, true, false, [36214], [9, 15]⟩,
        ⟨99590, true, false, [36214], [9, 15]⟩,
        ⟨1671, false, false, [36214, 85587], []⟩,
        ⟨47, false, false, [36214, 85587], []⟩,
        ⟨32693, false, false, [36214], []⟩,
        ⟨32694, false, false, [36214], []⟩,
        ⟨32627, false, false, [36214], []⟩,
        ⟨32627, false, false, [36214], []⟩,
        ⟨99488, true, false, [], [85585]⟩,
        ⟨99666, false, false, [], []⟩,
        ⟨99666, false, false, [], []⟩
      ]⟩,
    ⟨[36217, 85583], [36217, 85583], .contexts []⟩,
    ⟨[85583, 15], [85583, 15], .contexts []⟩,
    ⟨[85583, 15], [36215, 90715], .contexts [
        ⟨99669, false, false, [], []⟩,
        ⟨99668, true, false, [36216], [15]⟩,
        ⟨32625, true, false, [], [15]⟩,
        ⟨99667, true, false, [36216], [1, 15]⟩,
        ⟨1666, false, false, [36216, 90717], []⟩,
        ⟨9, false, false, [36216, 90717], []⟩,
        ⟨62546, false, false, [36216], []⟩,
        ⟨62547, false, false, [36216], []⟩,
        ⟨62472, false, false, [36216], []⟩,
        ⟨62472, false, false, [36216], []⟩,
        ⟨99594, true, false, [], [90715]⟩
      ]⟩,
    ⟨[36275, 96727], [36275, 96727], .contexts []⟩,
    ⟨[96727, 3], [36275, 96727], .contexts [
        ⟨99627, false, false, [], []⟩,
        ⟨99627, false, false, [], []⟩,
        ⟨99268, true, false, [], [3]⟩,
        ⟨99625, true, false, [36270], [1, 3]⟩,
        ⟨99625, true, false, [36270], [1, 3]⟩,
        ⟨99604, true, false, [36270], [1, 3]⟩,
        ⟨99601, true, false, [36270], [1, 3]⟩,
        ⟨1634, false, false, [36270, 91467], []⟩,
        ⟨132, false, false, [36270, 91467], []⟩,
        ⟨65991, false, false, [36270], [3, 1]⟩,
        ⟨93235, false, false, [36270], [3, 1]⟩,
        ⟨93231, false, false, [36270], [3, 1]⟩,
        ⟨93231, false, false, [36270], [3, 1]⟩,
        ⟨99604, false, false, [36270, 34251], [1]⟩,
        ⟨99626, true, false, [36270], [96729, 1]⟩,
        ⟨99268, false, false, [36270, 36273], []⟩,
        ⟨99628, false, false, [36270, 36273], []⟩,
        ⟨99605, true, false, [], [36273, 96727]⟩,
        ⟨99629, true, false, [], [96727]⟩,
        ⟨99671, false, false, [], []⟩
      ]⟩,
    ⟨[96727, 5], [96725], .contexts [
        ⟨99311, false, false, [], []⟩,
        ⟨99312, false, false, [], []⟩,
        ⟨99263, false, false, [], []⟩,
        ⟨99263, false, false, [], []⟩
      ]⟩,
    ⟨[96723, 5], [96723, 5], .contexts []⟩,
    ⟨[96723], [96723], .contexts []⟩,
    ⟨[36291], [36274], .source 18210⟩,
    ⟨[36274], [36274], .contexts []⟩,
    ⟨[36291], [36274], .contexts [
        ⟨99676, false, false, [], []⟩,
        ⟨99677, false, false, [], []⟩,
        ⟨99677, false, false, [], []⟩
      ]⟩,
    ⟨[96723, 5], [36291, 96723], .contexts [
        ⟨99674, false, false, [], []⟩,
        ⟨99260, true, false, [], [5]⟩,
        ⟨99264, true, false, [], [3, 5]⟩,
        ⟨99671, true, false, [36274], [5, 3, 5]⟩,
        ⟨99672, true, false, [36274], [5, 3, 5]⟩,
        ⟨2709, false, false, [36274, 96727], []⟩,
        ⟨448, false, false, [36274, 96727], []⟩,
        ⟨99673, false, false, [36274], [3]⟩,
        ⟨99314, false, false, [36274], []⟩,
        ⟨99315, false, false, [36274], []⟩,
        ⟨99259, false, false, [36274], []⟩,
        ⟨99259, false, false, [36274], []⟩,
        ⟨99675, false, false, [36274], []⟩,
        ⟨99678, true, false, [], [96723]⟩
      ]⟩,
    ⟨[36267, 96727], [36267, 96727], .contexts []⟩,
    ⟨[96725, 15], [96725, 15], .contexts []⟩,
    ⟨[85701], [36279, 85699], .contexts [
        ⟨99646, false, false, [], []⟩
      ]⟩,
    ⟨[36279, 85697], [36279, 85697], .contexts []⟩,
    ⟨[36279, 85697], [36279, 85697], .contexts []⟩,
    ⟨[85697, 1], [85697, 1], .contexts []⟩,
    ⟨[36289, 85695], [36289, 85695], .contexts []⟩,
    ⟨[36289, 85693], [36289, 85693], .contexts []⟩,
    ⟨[85693, 15], [85693, 15], .contexts []⟩,
    ⟨[36287], [36288], .contexts [
        ⟨99659, false, false, [], []⟩
      ]⟩,
    ⟨[36288], [36288], .contexts []⟩,
    ⟨[36287], [36288], .contexts [
        ⟨99689, false, false, [], []⟩,
        ⟨99690, false, false, [], []⟩,
        ⟨99690, false, false, [], []⟩
      ]⟩,
    ⟨[85693, 15], [36287, 94989], .contexts [
        ⟨99688, false, false, [], []⟩,
        ⟨99687, true, false, [36288], [15]⟩,
        ⟨33035, true, false, [], [15]⟩,
        ⟨99686, true, false, [36288], [1, 15]⟩,
        ⟨99686, true, false, [36288], [1, 15]⟩,
        ⟨99658, true, false, [36288], [1, 15]⟩,
        ⟨99652, true, false, [36288], [1, 15]⟩,
        ⟨1666, false, false, [36288, 94991], []⟩,
        ⟨9, false, false, [36288, 94991], []⟩,
        ⟨87246, false, false, [36288], []⟩,
        ⟨87247, false, false, [36288], []⟩,
        ⟨87187, false, false, [36288], []⟩,
        ⟨87187, false, false, [36288], []⟩,
        ⟨87540, false, false, [36288], []⟩,
        ⟨99691, true, false, [], [94989]⟩
      ]⟩,
    ⟨[36223, 85695], [36223, 85695], .contexts []⟩,
    ⟨[36223, 85695], [36223, 85695], .contexts []⟩,
    ⟨[85693, 7], [85693, 7], .contexts []⟩,
    ⟨[85693], [85693], .contexts []⟩,
    ⟨[36215, 90715], [36215, 90715], .contexts []⟩,
    ⟨[36215, 90713], [36215, 90713], .contexts []⟩,
    ⟨[90713, 15], [90713, 15], .contexts []⟩,
    ⟨[90713, 15], [36217, 85581], .contexts [
        ⟨99699, false, false, [], []⟩,
        ⟨99698, true, false, [36214], [15]⟩,
        ⟨62470, true, false, [], [15]⟩,
        ⟨99697, true, false, [36214], [5, 15]⟩,
        ⟨99697, true, false, [36214], [5, 15]⟩,
        ⟨99670, true, false, [36214], [5, 15]⟩,
        ⟨99669, true, false, [36214], [5, 15]⟩,
        ⟨2072, false, false, [36214, 85583], []⟩,
        ⟨29, false, false, [36214, 85583], []⟩,
        ⟨32697, false, false, [36214], []⟩,
        ⟨32698, false, false, [36214], []⟩,
        ⟨32622, false, false, [36214], []⟩,
        ⟨32622, false, false, [36214], []⟩,
        ⟨99488, true, false, [], [85581]⟩
      ]⟩,
    ⟨[36291, 96723], [36291, 96723], .contexts []⟩,
    ⟨[36291, 96723], [36291, 96723], .contexts []⟩,
    ⟨[96723, 1], [96721], .contexts [
        ⟨99316, false, false, [], []⟩,
        ⟨99317, false, false, [], []⟩,
        ⟨99255, false, false, [], []⟩,
        ⟨99255, false, false, [], []⟩
      ]⟩,
    ⟨[96721, 5], [96721, 5], .contexts []⟩,
    ⟨[36290], [36290], .contexts []⟩,
    ⟨[36275], [36290], .contexts [
        ⟨99676, true, true, [], []⟩,
        ⟨99705, false, false, [], []⟩,
        ⟨99705, false, false, [], []⟩
      ]⟩,
    ⟨[96725, 15], [36251, 96725], .contexts [
        ⟨99681, false, false, [], []⟩,
        ⟨99681, false, false, [], []⟩,
        ⟨99264, true, false, [], [15]⟩,
        ⟨99680, true, false, [36266], [5, 15]⟩,
        ⟨99680, true, false, [36266], [5, 15]⟩,
        ⟨99576, false, false, [36266], [96727, 5, 15]⟩,
        ⟨99632, true, false, [36266], [5, 15]⟩,
        ⟨99631, true, false, [36266], [5, 15]⟩,
        ⟨2072, false, false, [36266, 96727], []⟩,
        ⟨29, false, false, [36266, 96727], []⟩,
        ⟨99673, false, false, [36266], []⟩,
        ⟨99610, true, false, [], [96725]⟩
      ]⟩,
    ⟨[36251, 96725], [36251, 96725], .contexts []⟩,
    ⟨[36251, 96723], [36251, 96723], .contexts []⟩,
    ⟨[96723, 15], [96723, 15], .contexts []⟩,
    ⟨[96723, 15], [36267, 96723], .contexts [
        ⟨99710, false, false, [], []⟩,
        ⟨99709, true, false, [36250], [15]⟩,
        ⟨99260, true, false, [], [15]⟩,
        ⟨99708, true, false, [36250], [3, 15]⟩,
        ⟨99708, true, false, [36250], [3, 15]⟩,
        ⟨99707, true, false, [36250], [3, 15]⟩,
        ⟨1141, false, false, [36250, 96725], []⟩,
        ⟨21, false, false, [36250, 96725], []⟩,
        ⟨99314, false, false, [36250], []⟩,
        ⟨99315, false, false, [36250], []⟩,
        ⟨99259, false, false, [36250], []⟩,
        ⟨99259, false, false, [36250], []⟩,
        ⟨99675, false, false, [36250], []⟩,
        ⟨99576, true, false, [], [96723]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1558. -/
def y322TCIndexRaw1558 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85697, 1, 13], [36279, 85695], .contexts [
        ⟨99685, false, false, [], [13]⟩,
        ⟨99685, false, false, [], [13]⟩,
        ⟨99619, true, false, [], [1, 13]⟩,
        ⟨7, false, false, [85699], [13]⟩,
        ⟨11, false, false, [85699], [13]⟩,
        ⟨33044, false, false, [], [15, 13]⟩,
        ⟨99682, false, false, [], [15, 13]⟩,
        ⟨99638, false, false, [], [15, 13]⟩,
        ⟨99638, false, false, [], [15, 13]⟩,
        ⟨33042, false, false, [36279], [13]⟩,
        ⟨99683, false, false, [], [13]⟩,
        ⟨99684, false, false, [], [13]⟩,
        ⟨99621, false, false, [36279], [13]⟩,
        ⟨99640, true, false, [], [85697, 13]⟩,
        ⟨13, true, false, [], [36279, 85697, 13]⟩,
        ⟨99683, false, false, [], [13]⟩,
        ⟨99684, false, false, [], [13]⟩,
        ⟨99684, false, false, [], [13]⟩,
        ⟨33039, false, false, [36279], []⟩
      ]⟩,
    ⟨[85693, 13], [85693, 13], .contexts []⟩,
    ⟨[36281], [36278], .contexts [
        ⟨99643, false, false, [], []⟩,
        ⟨99644, false, false, [], []⟩,
        ⟨99644, false, false, [], []⟩
      ]⟩,
    ⟨[36287, 94989], [36287, 94989], .contexts []⟩,
    ⟨[85693, 11], [85691], .contexts [
        ⟨33105, false, false, [], []⟩,
        ⟨33106, false, false, [], []⟩,
        ⟨33031, false, false, [], []⟩,
        ⟨33031, false, false, [], []⟩
      ]⟩,
    ⟨[85693, 10], [85693, 11], .contexts [
        ⟨54, false, false, [85693], []⟩
      ]⟩,
    ⟨[94987, 15], [94987, 15], .contexts []⟩,
    ⟨[85691], [85691], .contexts []⟩,
    ⟨[94987, 15], [36289, 85691], .contexts [
        ⟨99718, false, false, [], []⟩,
        ⟨87185, true, false, [], [15]⟩,
        ⟨99715, true, false, [36286], [11, 15]⟩,
        ⟨99715, true, false, [36286], [11, 15]⟩,
        ⟨99692, true, false, [36286], [11, 15]⟩,
        ⟨99688, true, false, [36286], [11, 15]⟩,
        ⟨2046, false, false, [36286, 85693], []⟩,
        ⟨99717, false, false, [36286], []⟩,
        ⟨99716, false, false, [36286], []⟩,
        ⟨99719, false, false, [36286], []⟩,
        ⟨99657, true, false, [], [85691]⟩
      ]⟩,
    ⟨[36259, 85693], [36259, 85693], .contexts []⟩,
    ⟨[85693, 7], [36259, 85693], .contexts [
        ⟨99695, false, false, [], []⟩,
        ⟨99695, false, false, [], []⟩,
        ⟨33035, true, false, [], [7]⟩,
        ⟨99694, true, false, [36222], [1, 7]⟩,
        ⟨99694, true, false, [36222], [1, 7]⟩,
        ⟨99693, true, false, [36222], [1, 7]⟩,
        ⟨99665, true, false, [36222], [1, 7]⟩,
        ⟨99664, true, false, [36222], [1, 7]⟩,
        ⟨502, false, false, [36222, 85695], []⟩,
        ⟨9, false, false, [36222, 85695], []⟩,
        ⟨33103, false, false, [36222], []⟩,
        ⟨33104, false, false, [36222], []⟩,
        ⟨33034, false, false, [36222], []⟩,
        ⟨33034, false, false, [36222], []⟩,
        ⟨99696, false, false, [36222], []⟩,
        ⟨99545, true, false, [], [85693]⟩,
        ⟨99721, false, false, [], []⟩,
        ⟨99721, false, false, [], []⟩
      ]⟩,
    ⟨[85691, 7], [85691, 7], .contexts []⟩,
    ⟨[36217, 85581], [36217, 85581], .contexts []⟩,
    ⟨[36217, 85579], [36217, 85579], .contexts []⟩,
    ⟨[85579, 15], [85579, 15], .contexts []⟩,
    ⟨[85579, 15], [36215, 90711], .contexts [
        ⟨99726, false, false, [], []⟩,
        ⟨99725, true, false, [36216], [15]⟩,
        ⟨32620, true, false, [], [15]⟩,
        ⟨99724, true, false, [36216], [3, 15]⟩,
        ⟨99724, true, false, [36216], [3, 15]⟩,
        ⟨99700, true, false, [36216], [3, 15]⟩,
        ⟨99699, true, false, [36216], [3, 15]⟩,
        ⟨1141, false, false, [36216, 90713], []⟩,
        ⟨21, false, false, [36216, 90713], []⟩,
        ⟨62549, false, false, [36216], []⟩,
        ⟨62550, false, false, [36216], []⟩,
        ⟨62466, false, false, [36216], []⟩,
        ⟨62466, false, false, [36216], []⟩,
        ⟨99594, true, false, [], [90711]⟩
      ]⟩,
    ⟨[36275, 96721], [36275, 96721], .contexts []⟩,
    ⟨[96721, 5], [36275, 96721], .contexts [
        ⟨99704, false, false, [], []⟩,
        ⟨99704, false, false, [], []⟩,
        ⟨99256, true, false, [], [5]⟩,
        ⟨99702, true, false, [36290], [1, 5]⟩,
        ⟨99702, true, false, [36290], [1, 5]⟩,
        ⟨99701, true, false, [36290], [1, 5]⟩,
        ⟨99679, true, false, [36290], [1, 5]⟩,
        ⟨99674, true, false, [36290], [1, 5]⟩,
        ⟨890, false, false, [36290, 96723], []⟩,
        ⟨9, false, false, [36290, 96723], []⟩,
        ⟨99703, false, false, [36290], []⟩,
        ⟨99706, true, false, [], [96721]⟩,
        ⟨99728, false, false, [], []⟩,
        ⟨99728, false, false, [], []⟩
      ]⟩,
    ⟨[96719, 5], [96719, 5], .contexts []⟩,
    ⟨[36267, 96723], [36267, 96723], .contexts []⟩,
    ⟨[36267, 96723], [36267, 96723], .contexts []⟩,
    ⟨[36267, 96719], [36267, 96719], .contexts []⟩,
    ⟨[96719, 1], [36251, 96723], .contexts [
        ⟨99733, true, false, [36266], [1]⟩,
        ⟨99253, true, false, [], [1]⟩,
        ⟨99256, true, false, [], [15, 1]⟩,
        ⟨99732, true, false, [36266], [1, 15, 1]⟩,
        ⟨99732, true, false, [36266], [1, 15, 1]⟩,
        ⟨99731, true, false, [36266], [1, 15, 1]⟩,
        ⟨99711, true, false, [36266], [1, 15, 1]⟩,
        ⟨99710, true, false, [36266], [1, 15, 1]⟩,
        ⟨504, false, false, [36266, 96723], []⟩,
        ⟨99675, false, false, [36266], []⟩,
        ⟨99610, true, false, [], [96723]⟩
      ]⟩,
    ⟨[36281, 85693], [36281, 85693], .contexts []⟩,
    ⟨[85693, 13, 11], [36281, 85691], .contexts [
        ⟨99713, false, false, [], [11]⟩,
        ⟨99713, false, false, [], [11]⟩,
        ⟨33035, true, false, [], [13, 11]⟩,
        ⟨99712, true, false, [36278], [1, 13, 11]⟩,
        ⟨919, false, false, [36278, 85697], [11]⟩,
        ⟨116, false, false, [36278, 85697], [11]⟩,
        ⟨99663, false, false, [36278], [1, 11]⟩,
        ⟨33103, false, false, [36278], [11]⟩,
        ⟨33104, false, false, [36278], [11]⟩,
        ⟨33034, false, false, [36278], [11]⟩,
        ⟨33034, false, false, [36278], [11]⟩,
        ⟨99696, false, false, [36278], [11]⟩,
        ⟨99714, true, false, [], [85693, 11]⟩,
        ⟨99735, false, false, [], [11]⟩,
        ⟨99735, false, false, [], [11]⟩,
        ⟨33032, false, false, [36281], []⟩
      ]⟩,
    ⟨[85691, 13], [85691, 13], .contexts []⟩,
    ⟨[36280], [36280], .contexts []⟩,
    ⟨[36289, 85691], [36289, 85691], .contexts []⟩,
    ⟨[36289, 85689], [36289, 85689], .contexts []⟩,
    ⟨[85689, 15], [85689, 15], .contexts []⟩,
    ⟨[85689, 15], [36287, 94985], .contexts [
        ⟨99741, false, false, [], []⟩,
        ⟨99740, true, false, [36288], [15]⟩,
        ⟨33028, true, false, [], [15]⟩,
        ⟨99739, true, false, [36288], [9, 15]⟩,
        ⟨99739, true, false, [36288], [9, 15]⟩,
        ⟨99720, true, false, [36288], [9, 15]⟩,
        ⟨99718, true, false, [36288], [9, 15]⟩,
        ⟨1671, false, false, [36288, 94987], []⟩,
        ⟨87610, false, false, [36288], []⟩,
        ⟨87609, false, false, [36288], []⟩,
        ⟨87611, false, false, [36288], []⟩,
        ⟨99691, true, false, [], [94985]⟩
      ]⟩,
    ⟨[36223, 85691], [36223, 85691], .contexts []⟩,
    ⟨[85691, 7, 9], [36223, 85689], .contexts [
        ⟨99723, false, false, [], [9]⟩,
        ⟨99723, false, false, [], [9]⟩,
        ⟨33032, true, false, [], [7, 9]⟩,
        ⟨99722, true, false, [36258], [11, 7, 9]⟩,
        ⟨555, false, false, [36258, 85693], [9]⟩,
        ⟨99717, false, false, [36258], [9]⟩,
        ⟨99716, false, false, [36258], [9]⟩,
        ⟨99719, false, false, [36258], [9]⟩,
        ⟨99586, true, false, [], [85691, 9]⟩,
        ⟨99743, false, false, [], [9]⟩,
        ⟨99743, false, false, [], [9]⟩,
        ⟨33028, false, false, [36223], []⟩
      ]⟩,
    ⟨[85691, 9], [85689], .contexts [
        ⟨33107, false, false, [], []⟩,
        ⟨33108, false, false, [], []⟩,
        ⟨33027, false, false, [], []⟩,
        ⟨33027, false, false, [], []⟩
      ]⟩,
    ⟨[85691, 8], [85691, 9], .contexts [
        ⟨47, false, false, [85691], []⟩
      ]⟩,
    ⟨[85689], [85689], .contexts []⟩,
    ⟨[36215, 90711], [36215, 90711], .contexts []⟩,
    ⟨[36215, 90711], [36215, 90711], .contexts []⟩,
    ⟨[36215, 90707], [36215, 90707], .contexts []⟩,
    ⟨[90707, 1], [36217, 85579], .contexts [
        ⟨99750, true, false, [36214], [1]⟩,
        ⟨62460, true, false, [], [1]⟩,
        ⟨62464, true, false, [], [15, 1]⟩,
        ⟨99749, true, false, [36214], [1, 15, 1]⟩,
        ⟨99749, true, false, [36214], [1, 15, 1]⟩,
        ⟨99748, true, false, [36214], [1, 15, 1]⟩,
        ⟨99727, true, false, [36214], [1, 15, 1]⟩,
        ⟨99726, true, false, [36214], [1, 15, 1]⟩,
        ⟨504, false, false, [36214, 85579], []⟩,
        ⟨99488, true, false, [], [85579]⟩
      ]⟩,
    ⟨[90707], [36217, 85577], .contexts [
        ⟨99591, false, false, [36214], [90707]⟩,
        ⟨99505, false, false, [36214], [90707]⟩,
        ⟨99506, false, false, [36214], [90707]⟩,
        ⟨99750, true, false, [36214], []⟩,
        ⟨99490, false, false, [36214], [90707]⟩,
        ⟨8, true, false, [36214, 36216, 90707], []⟩,
        ⟨99751, false, false, [36214, 36216], [1]⟩,
        ⟨32699, false, false, [36214], []⟩,
        ⟨32700, false, false, [36214], []⟩,
        ⟨32615, false, false, [36214], []⟩,
        ⟨32615, false, false, [36214], []⟩,
        ⟨99485, true, false, [], [85577]⟩
      ]⟩,
    ⟨[36215], [36216], .contexts [
        ⟨99592, false, false, [], []⟩,
        ⟨99593, false, false, [], []⟩,
        ⟨99593, false, false, [], []⟩
      ]⟩,
    ⟨[36291, 96719], [36291, 96719], .contexts []⟩,
    ⟨[96719, 5, 13], [36291, 96717], .contexts [
        ⟨99730, false, false, [], [13]⟩,
        ⟨99730, false, false, [], [13]⟩,
        ⟨99253, true, false, [], [5, 13]⟩,
        ⟨99729, true, false, [36274], [15, 5, 13]⟩,
        ⟨1204, false, false, [36274, 96721], [13]⟩,
        ⟨10, false, false, [36274, 96721], [13]⟩,
        ⟨99318, false, false, [36274], [13]⟩,
        ⟨99319, false, false, [36274], [13]⟩,
        ⟨99252, false, false, [36274], [13]⟩,
        ⟨99252, false, false, [36274], [13]⟩,
        ⟨99678, true, false, [], [96719, 13]⟩,
        ⟨99754, false, false, [], [13]⟩,
        ⟨99754, false, false, [], [13]⟩,
        ⟨99250, false, false, [36291], []⟩
      ]⟩,
    ⟨[96717, 5], [96717, 5], .contexts []⟩,
    ⟨[36279, 85691], [36279, 85691], .contexts []⟩,
    ⟨[36279, 85689, 13], [85691, 13, 9, 13], .contexts [
        ⟨33028, true, false, [36279], [13]⟩,
        ⟨99757, true, false, [], [9, 13]⟩,
        ⟨99757, true, false, [], [9, 13]⟩,
        ⟨99639, false, false, [], [85691, 9, 13]⟩,
        ⟨99642, true, true, [], [85691, 9, 13]⟩,
        ⟨99738, false, false, [], [85691, 9, 13]⟩,
        ⟨99738, false, false, [], [85691, 9, 13]⟩,
        ⟨99719, true, false, [36280], [9, 13]⟩,
        ⟨99716, true, false, [36280], [9, 13]⟩,
        ⟨99717, true, false, [36280], [9, 13]⟩,
        ⟨931, true, false, [36280, 85693], [9, 13]⟩,
        ⟨99736, false, false, [36280], [13, 9, 13]⟩,
        ⟨99737, true, false, [], [9, 13]⟩,
        ⟨99737, true, false, [], [9, 13]⟩
      ]⟩,
    ⟨[85689, 13], [36281, 85689], .contexts [
        ⟨99758, false, false, [36278], []⟩,
        ⟨942, false, false, [36278, 85691], []⟩,
        ⟨99746, false, false, [36278], []⟩,
        ⟨99745, false, false, [36278], []⟩,
        ⟨99747, false, false, [36278], []⟩,
        ⟨99714, true, false, [], [85689]⟩
      ]⟩,
    ⟨[36287, 94985], [36287, 94985], .contexts []⟩,
    ⟨[36287, 94983], [36287, 94983], .contexts []⟩,
    ⟨[94983, 15], [94983, 15], .contexts []⟩,
    ⟨[94983, 15], [36289, 85687], .contexts [
        ⟨99762, false, false, [], []⟩,
        ⟨99761, true, false, [36286], [15]⟩,
        ⟨87180, true, false, [], [15]⟩,
        ⟨99760, true, false, [36286], [1, 15]⟩,
        ⟨99760, true, false, [36286], [1, 15]⟩,
        ⟨99742, true, false, [36286], [1, 15]⟩,
        ⟨99741, true, false, [36286], [1, 15]⟩,
        ⟨1666, false, false, [36286, 85689], []⟩,
        ⟨9, false, false, [36286, 85689], []⟩,
        ⟨33109, false, false, [36286], []⟩,
        ⟨33110, false, false, [36286], []⟩,
        ⟨33023, false, false, [36286], []⟩,
        ⟨33023, false, false, [36286], []⟩,
        ⟨99657, true, false, [], [85687]⟩
      ]⟩,
    ⟨[36275, 96717], [36275, 96717], .contexts []⟩,
    ⟨[36275, 96715, 5], [96717, 1], .contexts [
        ⟨99246, true, false, [36275], [5]⟩,
        ⟨99764, true, false, [], [1, 5]⟩,
        ⟨99764, true, false, [], [1, 5]⟩,
        ⟨99706, false, false, [], [96717, 1, 5]⟩,
        ⟨99249, true, false, [36290], [1, 5]⟩,
        ⟨99249, true, false, [36290], [1, 5]⟩,
        ⟨99321, true, false, [36290], [1, 5]⟩,
        ⟨99320, true, false, [36290], [1, 5]⟩,
        ⟨64, true, false, [36290, 96719], [1, 5]⟩,
        ⟨913, true, false, [36290, 96719], [1, 5]⟩,
        ⟨99755, false, false, [36290], [5, 1, 5]⟩,
        ⟨99756, true, false, [], [1, 5]⟩,
        ⟨99756, true, false, [], [1, 5]⟩,
        ⟨890, false, false, [96717], []⟩,
        ⟨9, false, false, [96717], []⟩
      ]⟩,
    ⟨[96715, 5], [96715, 5], .contexts []⟩,
    ⟨[36289, 85687], [36289, 85687], .contexts []⟩,
    ⟨[36289, 85685], [36289, 85685], .contexts []⟩,
    ⟨[85685, 15], [85685, 15], .contexts []⟩,
    ⟨[85685, 15], [36287, 94981], .contexts [
        ⟨99769, false, false, [], []⟩,
        ⟨99768, true, false, [36288], [15]⟩,
        ⟨33021, true, false, [], [15]⟩,
        ⟨99767, true, false, [36288], [5, 15]⟩,
        ⟨99767, true, false, [36288], [5, 15]⟩,
        ⟨99763, true, false, [36288], [5, 15]⟩,
        ⟨99762, true, false, [36288], [5, 15]⟩,
        ⟨2072, false, false, [36288, 94983], []⟩,
        ⟨29, false, false, [36288, 94983], []⟩,
        ⟨87251, false, false, [36288], []⟩,
        ⟨87252, false, false, [36288], []⟩,
        ⟨87176, false, false, [36288], []⟩,
        ⟨87176, false, false, [36288], []⟩,
        ⟨99691, true, false, [], [94981]⟩
      ]⟩,
    ⟨[36291, 96715], [36291, 96715], .contexts []⟩,
    ⟨[36291, 96713, 5], [96715, 11], .contexts [
        ⟨99242, true, false, [36291], [5]⟩,
        ⟨99771, true, false, [], [11, 5]⟩,
        ⟨99771, true, false, [], [11, 5]⟩,
        ⟨99678, false, false, [], [96715, 11, 5]⟩,
        ⟨99245, true, false, [36274], [11, 5]⟩,
        ⟨99245, true, false, [36274], [11, 5]⟩,
        ⟨99323, true, false, [36274], [11, 5]⟩,
        ⟨99322, true, false, [36274], [11, 5]⟩,
        ⟨99765, true, false, [36274], [11, 5]⟩,
        ⟨99766, true, false, [], [11, 5]⟩,
        ⟨99766, true, false, [], [11, 5]⟩,
        ⟨940, false, false, [96715], []⟩,
        ⟨54, false, false, [96715], []⟩
      ]⟩,
    ⟨[96713, 5], [96713, 5], .contexts []⟩,
    ⟨[36287, 94981], [36287, 94981], .contexts []⟩,
    ⟨[36287, 94979], [36287, 94979], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1559. -/
def y322TCIndexRaw1559 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[94979, 15], [94979, 15], .contexts []⟩,
    ⟨[94979, 15], [36289, 85683], .contexts [
        ⟨99776, false, false, [], []⟩,
        ⟨99775, true, false, [36286], [15]⟩,
        ⟨87174, true, false, [], [15]⟩,
        ⟨99774, true, false, [36286], [3, 15]⟩,
        ⟨99774, true, false, [36286], [3, 15]⟩,
        ⟨99770, true, false, [36286], [3, 15]⟩,
        ⟨99769, true, false, [36286], [3, 15]⟩,
        ⟨1141, false, false, [36286, 85685], []⟩,
        ⟨21, false, false, [36286, 85685], []⟩,
        ⟨33112, false, false, [36286], []⟩,
        ⟨33113, false, false, [36286], []⟩,
        ⟨33017, false, false, [36286], []⟩,
        ⟨33017, false, false, [36286], []⟩,
        ⟨99657, true, false, [], [85683]⟩
      ]⟩,
    ⟨[36275, 96713], [36275, 96713], .contexts []⟩,
    ⟨[36275, 96711], [36275, 96711], .contexts []⟩,
    ⟨[36275, 96711, 5], [96713, 9], .contexts [
        ⟨99779, true, false, [], [5]⟩,
        ⟨99238, true, false, [36275], [5]⟩,
        ⟨99778, true, false, [], [9, 5]⟩,
        ⟨99778, true, false, [], [9, 5]⟩,
        ⟨99706, false, false, [], [96713, 9, 5]⟩,
        ⟨99241, true, false, [36290], [9, 5]⟩,
        ⟨99241, true, false, [36290], [9, 5]⟩,
        ⟨99326, true, false, [36290], [9, 5]⟩,
        ⟨99325, true, false, [36290], [9, 5]⟩,
        ⟨99772, true, false, [36290], [9, 5]⟩,
        ⟨99773, true, false, [], [9, 5]⟩,
        ⟨99773, true, false, [], [9, 5]⟩,
        ⟨960, false, false, [96713], []⟩,
        ⟨47, false, false, [96713], []⟩
      ]⟩,
    ⟨[96711, 5], [96711, 5], .contexts []⟩,
    ⟨[96711], [96711], .contexts []⟩,
    ⟨[36289, 85683], [36289, 85683], .contexts []⟩,
    ⟨[36289, 85681], [36289, 85681], .contexts []⟩,
    ⟨[36289, 85681], [36289, 85681], .contexts []⟩,
    ⟨[36289, 85681], [36289, 85681], .contexts []⟩,
    ⟨[36289, 85679], [36289, 85679], .contexts []⟩,
    ⟨[36289, 85679], [36289, 85679], .contexts []⟩,
    ⟨[85679, 1], [36287, 94979], .contexts [
        ⟨99788, true, false, [36288], [1]⟩,
        ⟨99787, true, false, [36288], [1]⟩,
        ⟨33012, true, false, [], [1]⟩,
        ⟨99786, true, false, [36288], [15, 1]⟩,
        ⟨99785, true, false, [36288], [15, 1]⟩,
        ⟨99784, true, false, [36288], [15, 1]⟩,
        ⟨33015, true, false, [], [15, 1]⟩,
        ⟨99783, true, false, [36288], [1, 15, 1]⟩,
        ⟨99783, true, false, [36288], [1, 15, 1]⟩,
        ⟨99777, true, false, [36288], [1, 15, 1]⟩,
        ⟨99776, true, false, [36288], [1, 15, 1]⟩,
        ⟨504, false, false, [36288, 94979], []⟩,
        ⟨99691, true, false, [], [94979]⟩
      ]⟩,
    ⟨[36289], [36289], .contexts []⟩,
    ⟨[36289], [36289], .contexts [
        ⟨99655, false, false, [], []⟩,
        ⟨99790, false, false, [], []⟩
      ]⟩,
    ⟨[36289], [36289], .contexts []⟩,
    ⟨[94977], [36289, 85679], .contexts [
        ⟨87170, true, false, [], []⟩,
        ⟨87170, true, false, [], []⟩,
        ⟨87254, true, false, [], []⟩,
        ⟨87253, true, false, [], []⟩,
        ⟨99789, true, false, [36286], [1]⟩,
        ⟨8, false, false, [36286, 85679], []⟩,
        ⟨99654, true, false, [], [85679]⟩,
        ⟨99787, false, false, [], []⟩,
        ⟨99792, true, false, [], [85679]⟩,
        ⟨99791, true, false, [], [85679]⟩,
        ⟨99788, false, false, [], []⟩
      ]⟩,
    ⟨[36291, 96711], [36291, 96711], .contexts []⟩,
    ⟨[96711, 5, 1, 5], [36291, 96707], .contexts [
        ⟨99781, false, false, [], [1, 5]⟩,
        ⟨99781, false, false, [], [1, 5]⟩,
        ⟨99780, false, false, [36274], [1, 5]⟩,
        ⟨99327, false, false, [36274], [1, 5]⟩,
        ⟨99328, false, false, [36274], [1, 5]⟩,
        ⟨99237, false, false, [36274], [1, 5]⟩,
        ⟨99237, false, false, [36274], [1, 5]⟩,
        ⟨99782, false, false, [36274], [1, 5]⟩,
        ⟨99678, true, false, [], [96711, 1, 5]⟩,
        ⟨99794, false, false, [], [1, 5]⟩,
        ⟨99794, false, false, [], [1, 5]⟩,
        ⟨99234, false, false, [36291], [5]⟩,
        ⟨99231, false, false, [36291], []⟩
      ]⟩,
    ⟨[96749], [85827, 3], .source 48439⟩,
    ⟨[96749], [96749], .contexts []⟩,
    ⟨[85827, 3], [96749], .contexts [
        ⟨99796, true, false, [], []⟩,
        ⟨99797, false, false, [], []⟩,
        ⟨99797, false, false, [], []⟩
      ]⟩,
    ⟨[33285, 95417], [33285, 95417], .contexts []⟩,
    ⟨[21141, 85859], [21141, 85859], .contexts []⟩,
    ⟨[21141, 85861], [21141, 85861], .contexts []⟩,
    ⟨[21141, 85861], [21141, 85861], .contexts []⟩,
    ⟨[96749, 13], [96749, 13], .contexts []⟩,
    ⟨[96749, 13], [21141, 85861], .contexts [
        ⟨99803, false, false, [], []⟩,
        ⟨99798, true, false, [], [13]⟩,
        ⟨147, false, false, [85827], []⟩,
        ⟨148, false, false, [85827], []⟩,
        ⟨44297, true, false, [21138], [13, 3]⟩,
        ⟨59, false, false, [21138, 85859], [3]⟩,
        ⟨44298, true, false, [], [85859, 3]⟩,
        ⟨99800, false, false, [], [3]⟩,
        ⟨99800, false, false, [], [3]⟩,
        ⟨34012, false, false, [21141], []⟩,
        ⟨99801, false, false, [], []⟩,
        ⟨99802, false, false, [], []⟩,
        ⟨34026, false, false, [21141], []⟩,
        ⟨13, true, false, [], [21141, 85861]⟩
      ]⟩,
    ⟨[85861, 13], [21139, 96749], .contexts [
        ⟨99804, true, false, [21140], [13]⟩,
        ⟨59, false, false, [21140, 96749], []⟩,
        ⟨44298, false, true, [], [96749]⟩
      ]⟩,
    ⟨[36297], [18505, 21143], .source 18213⟩,
    ⟨[36297], [36297], .contexts []⟩,
    ⟨[36297], [36297], .contexts []⟩,
    ⟨[96749, 15], [36297, 83775], .contexts [
        ⟨99798, true, false, [], [15]⟩,
        ⟨151, false, false, [85827], []⟩,
        ⟨152, false, false, [85827], []⟩,
        ⟨33833, false, false, [], [3]⟩,
        ⟨33822, false, false, [], [3]⟩,
        ⟨33823, false, false, [], [3]⟩,
        ⟨33823, false, false, [], [3]⟩,
        ⟨44308, false, false, [18505], []⟩,
        ⟨99806, true, false, [], [83775]⟩,
        ⟨22992, false, false, [36297], []⟩,
        ⟨99808, true, false, [], [83775]⟩,
        ⟨99807, true, false, [], [83775]⟩,
        ⟨13, true, false, [], [36297, 83775]⟩
      ]⟩,
    ⟨[36299], [36296], .source 18214⟩,
    ⟨[36301], [21141, 17753], .source 18215⟩,
    ⟨[36301, 96549], [36301, 96549], .contexts []⟩,
    ⟨[36303], [36300], .source 18216⟩,
    ⟨[36300], [36300], .contexts []⟩,
    ⟨[96549, 5], [36303, 96749], .contexts [
        ⟨99812, true, false, [36300], [5]⟩,
        ⟨98288, true, false, [], [5]⟩,
        ⟨99811, false, false, [36300], [83005, 13, 5]⟩,
        ⟨34041, true, false, [36300, 21141], [13, 5]⟩,
        ⟨99802, true, false, [36300], [5, 13, 5]⟩,
        ⟨99802, true, false, [36300], [5, 13, 5]⟩,
        ⟨99801, true, false, [36300], [5, 13, 5]⟩,
        ⟨99804, true, false, [36300], [5, 13, 5]⟩,
        ⟨99803, true, false, [36300], [5, 13, 5]⟩,
        ⟨1116, false, false, [36300, 96749], []⟩,
        ⟨99814, true, false, [], [96749]⟩,
        ⟨99814, true, false, [], [96749]⟩,
        ⟨99813, true, false, [], [96749]⟩
      ]⟩,
    ⟨[96751], [96549, 9], .source 48440⟩,
    ⟨[96549, 9], [96751], .contexts [
        ⟨99816, true, false, [], []⟩
      ]⟩,
    ⟨[96751], [96751], .contexts []⟩,
    ⟨[96549, 9], [96751], .contexts [
        ⟨99817, false, false, [], []⟩,
        ⟨99818, false, false, [], []⟩,
        ⟨99818, false, false, [], []⟩
      ]⟩,
    ⟨[35815, 86619], [35815, 86619], .contexts []⟩,
    ⟨[35815, 86619], [35815, 86619], .contexts []⟩,
    ⟨[86621, 3], [35817, 96751], .contexts [
        ⟨98299, false, false, [35814], [86621, 3]⟩,
        ⟨81906, true, false, [], [3]⟩,
        ⟨38243, true, false, [], [3]⟩,
        ⟨99821, true, false, [35814], [9, 3]⟩,
        ⟨99821, true, false, [35814], [9, 3]⟩,
        ⟨99820, true, false, [35814], [9, 3]⟩,
        ⟨98300, true, false, [35814], [9, 3]⟩,
        ⟨98297, true, false, [35814], [9, 3]⟩,
        ⟨197, true, false, [35814, 96549], [3]⟩,
        ⟨196, true, false, [35814, 96549], [3]⟩,
        ⟨99819, false, false, [35814], [3, 3]⟩,
        ⟨20, false, false, [35814, 96751], []⟩,
        ⟨98301, true, false, [], [96751]⟩
      ]⟩,
    ⟨[36305], [20673, 33417], .source 18217⟩,
    ⟨[36307], [36305, 33399], .source 18218⟩,
    ⟨[36309], [36307, 28673], .source 18219⟩,
    ⟨[96751, 11], [36309, 83013], .contexts [
        ⟨99819, true, false, [], [11]⟩,
        ⟨2344, false, false, [96549], []⟩,
        ⟨2346, false, false, [96549], []⟩,
        ⟨98305, false, false, [], [9, 11, 9]⟩,
        ⟨98306, false, false, [], [9, 11, 9]⟩,
        ⟨98303, false, false, [], [9, 11, 9]⟩,
        ⟨98304, false, false, [], [9, 11, 9]⟩,
        ⟨98304, false, false, [], [9, 11, 9]⟩,
        ⟨91022, false, false, [20673], [11, 9]⟩,
        ⟨99823, true, false, [], [88631, 11, 9]⟩,
        ⟨90998, false, false, [36305], [9]⟩,
        ⟨99824, true, false, [], [84741, 9]⟩,
        ⟨74558, false, false, [36307], []⟩,
        ⟨99825, true, false, [], [83013]⟩,
        ⟨62871, false, false, [36309], []⟩
      ]⟩,
    ⟨[96751, 11], [36309, 83013], .contexts [
        ⟨99826, false, false, [], []⟩,
        ⟨13, true, false, [], [36309, 83013]⟩
      ]⟩,
    ⟨[36311], [36308], .source 18220⟩,
    ⟨[83013, 11], [36311, 96751], .contexts [
        ⟨99827, true, false, [36308], [11]⟩,
        ⟨53, false, false, [36308, 96751], []⟩,
        ⟨99828, true, false, [], [96751]⟩
      ]⟩,
    ⟨[96751, 13], [83007], .contexts [
        ⟨99819, true, false, [], [13]⟩,
        ⟨201, false, false, [96549], []⟩,
        ⟨202, false, false, [96549], []⟩,
        ⟨98289, false, false, [], [9]⟩,
        ⟨18665, false, false, [], [9]⟩,
        ⟨18400, false, false, [], [9]⟩,
        ⟨18400, false, false, [], [9]⟩,
        ⟨42798, false, false, [], []⟩,
        ⟨18664, false, false, [], []⟩,
        ⟨18403, false, false, [], []⟩,
        ⟨18403, false, false, [], []⟩,
        ⟨42800, false, false, [], []⟩,
        ⟨672, true, false, [], [83007]⟩
      ]⟩,
    ⟨[83007, 13], [96751], .contexts [
        ⟨99830, true, false, [], [13]⟩,
        ⟨59, false, false, [96751], []⟩,
        ⟨99818, false, false, [], []⟩
      ]⟩,
    ⟨[96753], [83013, 1], .source 48441⟩,
    ⟨[83013, 1], [96753], .contexts [
        ⟨99832, true, false, [], []⟩
      ]⟩,
    ⟨[96753], [96753], .contexts []⟩,
    ⟨[96753], [96753], .contexts []⟩,
    ⟨[83013, 1], [96753], .contexts [
        ⟨99833, false, false, [], []⟩,
        ⟨99834, false, false, [], []⟩,
        ⟨99835, false, false, [], []⟩,
        ⟨99835, false, false, [], []⟩
      ]⟩,
    ⟨[25543, 84627], [25543, 84627], .contexts []⟩,
    ⟨[25543, 84627], [25543, 84627], .contexts []⟩,
    ⟨[96753, 7], [96753, 7], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1560. -/
def y322TCIndexRaw1560 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[96753, 7], [25543, 84627], .contexts [
        ⟨99839, false, false, [], []⟩,
        ⟨99836, true, false, [], [7]⟩,
        ⟨104, false, false, [83013], []⟩,
        ⟨105, false, false, [83013], []⟩,
        ⟨62874, false, false, [], [1]⟩,
        ⟨62867, false, false, [], [1]⟩,
        ⟨62868, false, false, [], [1]⟩,
        ⟨62868, false, false, [], [1]⟩,
        ⟨27973, false, false, [25543], []⟩,
        ⟨99837, false, false, [], []⟩,
        ⟨99838, false, false, [], []⟩,
        ⟨27979, false, false, [25543], []⟩,
        ⟨13, true, false, [], [25543, 84627]⟩
      ]⟩,
    ⟨[36313], [20907, 20907], .source 18221⟩,
    ⟨[36315], [36313, 20843], .source 18222⟩,
    ⟨[36315, 96753], [36315, 96753], .contexts []⟩,
    ⟨[36315, 96753], [36315, 96753], .contexts []⟩,
    ⟨[96753, 13], [96753, 13], .contexts []⟩,
    ⟨[96753], [96753], .contexts []⟩,
    ⟨[96753, 13], [36315, 96753], .contexts [
        ⟨99845, false, false, [], []⟩,
        ⟨99836, true, false, [], [13]⟩,
        ⟨115, false, false, [83013], []⟩,
        ⟨118, false, false, [83013], []⟩,
        ⟨18411, false, false, [], [1, 13, 1]⟩,
        ⟨43241, false, false, [], [1, 13, 1]⟩,
        ⟨43239, false, false, [], [1, 13, 1]⟩,
        ⟨43239, false, false, [], [1, 13, 1]⟩,
        ⟨18406, false, false, [20907], [13, 1]⟩,
        ⟨43240, false, false, [20907], [13, 1]⟩,
        ⟨99841, true, false, [], [83009, 13, 1]⟩,
        ⟨43054, false, false, [36313], [1]⟩,
        ⟨99842, true, false, [], [83013, 1]⟩,
        ⟨99833, false, false, [36315], []⟩,
        ⟨99843, false, false, [], []⟩,
        ⟨99844, false, false, [], []⟩,
        ⟨99846, false, false, [36315], []⟩
      ]⟩,
    ⟨[96753, 13], [36315, 96753], .contexts [
        ⟨99847, false, false, [], []⟩,
        ⟨13, true, false, [], [36315, 96753]⟩
      ]⟩,
    ⟨[96753, 15], [83017], .contexts [
        ⟨99836, true, false, [], [15]⟩,
        ⟨121, false, false, [83013], []⟩,
        ⟨122, false, false, [83013], []⟩,
        ⟨18413, false, false, [], [1]⟩,
        ⟨18661, false, false, [], [1]⟩,
        ⟨18418, false, false, [], [1]⟩,
        ⟨18418, false, false, [], [1]⟩,
        ⟨18417, false, false, [], []⟩,
        ⟨18660, false, false, [], []⟩,
        ⟨18422, false, false, [], []⟩,
        ⟨18422, false, false, [], []⟩,
        ⟨62858, false, false, [], []⟩,
        ⟨672, true, false, [], [83017]⟩
      ]⟩,
    ⟨[83017, 15], [96753], .contexts [
        ⟨99849, true, false, [], [15]⟩,
        ⟨1, false, false, [96753], []⟩,
        ⟨99835, false, false, [], []⟩
      ]⟩,
    ⟨[96755], [96637, 5], .source 48442⟩,
    ⟨[96637, 5], [96755], .contexts [
        ⟨99851, true, false, [], []⟩
      ]⟩,
    ⟨[96755, 5], [96637], .contexts [
        ⟨99852, true, false, [], [5]⟩,
        ⟨28, false, false, [96637], []⟩,
        ⟨99026, false, false, [], []⟩
      ]⟩,
    ⟨[96755], [96755], .contexts []⟩,
    ⟨[96755], [96755], .contexts []⟩,
    ⟨[96637, 5], [96755], .contexts [
        ⟨99852, false, false, [], []⟩,
        ⟨99854, false, false, [], []⟩,
        ⟨99855, false, false, [], []⟩,
        ⟨99855, false, false, [], []⟩
      ]⟩,
    ⟨[88347, 5], [22243, 96049], .contexts [
        ⟨95659, false, false, [], []⟩
      ]⟩,
    ⟨[22243, 96049], [22243, 96049], .contexts []⟩,
    ⟨[22243, 96049], [22243, 96049], .contexts []⟩,
    ⟨[96755, 9], [96755, 9], .contexts []⟩,
    ⟨[96755, 9], [22243, 96049], .contexts [
        ⟨99860, false, false, [], []⟩,
        ⟨99856, true, false, [], [9]⟩,
        ⟨1265, false, false, [96637], []⟩,
        ⟨1266, false, false, [96637], []⟩,
        ⟨99033, false, false, [], [5]⟩,
        ⟨99034, false, false, [], [5]⟩,
        ⟨50033, false, false, [], [5]⟩,
        ⟨50034, false, false, [], [5]⟩,
        ⟨50034, false, false, [], [5]⟩,
        ⟨99857, false, false, [], []⟩,
        ⟨99858, false, false, [], []⟩,
        ⟨99859, false, false, [], []⟩,
        ⟨99859, false, false, [], []⟩,
        ⟨95677, false, false, [22243], []⟩,
        ⟨13, true, false, [], [22243, 96049]⟩
      ]⟩,
    ⟨[36317], [32899, 32943], .source 18223⟩,
    ⟨[96755, 11], [96755, 11], .contexts []⟩,
    ⟨[36317], [36317], .contexts [
        ⟨13, false, false, [], [36317]⟩
      ]⟩,
    ⟨[96755, 11], [36317, 85933], .contexts [
        ⟨99863, false, false, [], []⟩,
        ⟨99856, true, false, [], [11]⟩,
        ⟨174, false, false, [96637], []⟩,
        ⟨175, false, false, [96637], []⟩,
        ⟨99036, false, false, [], [5]⟩,
        ⟨99037, false, false, [], [5]⟩,
        ⟨89796, false, false, [], [5]⟩,
        ⟨89797, false, false, [], [5]⟩,
        ⟨89797, false, false, [], [5]⟩,
        ⟨89809, false, false, [32899], []⟩,
        ⟨99862, true, false, [], [85933]⟩,
        ⟨35901, false, false, [36317], []⟩,
        ⟨99864, true, false, [], [85933]⟩
      ]⟩,
    ⟨[36319], [36316], .source 18224⟩,
    ⟨[7357, 85723], [7357, 85723], .contexts []⟩,
    ⟨[7357, 85723], [7357, 85723], .contexts []⟩,
    ⟨[96755, 13], [96755, 13], .contexts []⟩,
    ⟨[96755, 13], [7357, 85723], .contexts [
        ⟨99869, false, false, [], []⟩,
        ⟨99856, true, false, [], [13]⟩,
        ⟨179, false, false, [96637], []⟩,
        ⟨180, false, false, [96637], []⟩,
        ⟨99024, false, false, [], [5]⟩,
        ⟨21112, false, false, [], [5]⟩,
        ⟨21113, false, false, [], [5]⟩,
        ⟨21113, false, false, [], [5]⟩,
        ⟨33238, false, false, [], []⟩,
        ⟨99867, false, false, [], []⟩,
        ⟨99868, false, false, [], []⟩,
        ⟨99868, false, false, [], []⟩,
        ⟨49291, false, false, [7357], []⟩,
        ⟨16970, true, false, [], [85723]⟩
      ]⟩,
    ⟨[96755, 9], [22243, 96049], .contexts [
        ⟨99860, false, false, [], []⟩,
        ⟨99861, false, false, [], []⟩,
        ⟨99858, false, false, [], []⟩,
        ⟨99859, false, false, [], []⟩,
        ⟨99859, false, false, [], []⟩
      ]⟩,
    ⟨[36321], [22249, 33517], .source 18225⟩,
    ⟨[36323], [22243, 36321], .source 18226⟩,
    ⟨[96755], [96755], .contexts []⟩,
    ⟨[96755], [96755], .contexts []⟩,
    ⟨[36325], [36322], .source 18227⟩,
    ⟨[36322], [36322], .contexts []⟩,
    ⟨[84253, 3], [36325, 96755], .contexts [
        ⟨99873, false, false, [36322], [84253, 3]⟩,
        ⟨99872, false, false, [36322, 22243], [84253, 3]⟩,
        ⟨91356, true, false, [36322, 22243, 22249], [3]⟩,
        ⟨48306, true, false, [36322, 22243], [3]⟩,
        ⟨95652, true, false, [36322, 22243], [9, 3]⟩,
        ⟨99871, true, false, [36322], [3, 9, 3]⟩,
        ⟨1439, false, false, [36322, 96755], []⟩,
        ⟨99874, false, false, [36322], []⟩,
        ⟨99875, false, false, [36322], []⟩,
        ⟨99877, true, false, [], [96755]⟩,
        ⟨99877, true, false, [], [96755]⟩,
        ⟨99876, true, false, [], [96755]⟩
      ]⟩,
    ⟨[36327], [22243, 22257], .source 18228⟩,
    ⟨[36329], [36327, 22265], .source 18229⟩,
    ⟨[36331], [36328], .source 18230⟩,
    ⟨[36328], [36328], .contexts []⟩,
    ⟨[84499, 7], [36331, 96755], .contexts [
        ⟨99880, false, false, [36328], [84499, 7]⟩,
        ⟨48327, true, false, [36328, 36327], [7]⟩,
        ⟨99879, false, false, [36328], [83385, 9, 7]⟩,
        ⟨95666, true, false, [36328, 22243], [9, 7]⟩,
        ⟨99871, true, false, [36328], [7, 9, 7]⟩,
        ⟨469, false, false, [36328, 96755], []⟩,
        ⟨99874, false, false, [36328], []⟩,
        ⟨99875, false, false, [36328], []⟩,
        ⟨99882, true, false, [], [96755]⟩,
        ⟨99882, true, false, [], [96755]⟩,
        ⟨99881, true, false, [], [96755]⟩
      ]⟩,
    ⟨[96755, 7], [36329, 84499], .contexts [
        ⟨99883, true, false, [36330], [7]⟩,
        ⟨38, false, false, [36330, 84499], []⟩,
        ⟨99881, false, true, [], [84499]⟩
      ]⟩,
    ⟨[96757], [96755, 1], .source 48443⟩,
    ⟨[96755, 1], [96757], .contexts [
        ⟨99885, true, false, [], []⟩
      ]⟩,
    ⟨[96757], [96757], .contexts []⟩,
    ⟨[96755, 1], [96757], .contexts [
        ⟨99886, false, false, [], []⟩,
        ⟨99887, false, false, [], []⟩,
        ⟨99887, false, false, [], []⟩
      ]⟩,
    ⟨[96637, 1], [36077, 95357], .contexts [
        ⟨99051, false, false, [], []⟩
      ]⟩,
    ⟨[36077, 95357], [36077, 95357], .contexts []⟩,
    ⟨[36077, 95357], [36077, 95357], .contexts []⟩,
    ⟨[96757, 5], [96757, 5], .contexts []⟩,
    ⟨[96757, 5], [36077, 95357], .contexts [
        ⟨99892, false, false, [], []⟩,
        ⟨99888, true, false, [], [5]⟩,
        ⟨98, false, false, [96755], []⟩,
        ⟨99, false, false, [96755], []⟩,
        ⟨99853, false, false, [], [1]⟩,
        ⟨99025, false, false, [], [1]⟩,
        ⟨99026, false, false, [], [1]⟩,
        ⟨99026, false, false, [], [1]⟩,
        ⟨99889, false, false, [], []⟩,
        ⟨99890, false, false, [], []⟩,
        ⟨99891, false, false, [], []⟩,
        ⟨99891, false, false, [], []⟩,
        ⟨89834, false, false, [36077], []⟩,
        ⟨13, true, false, [], [36077, 95357]⟩
      ]⟩,
    ⟨[95357, 5], [36079, 96757], .contexts [
        ⟨99893, true, false, [36076], [5]⟩,
        ⟨28, false, false, [36076, 96757], []⟩,
        ⟨99047, true, false, [], [96757]⟩
      ]⟩,
    ⟨[36333], [22243, 34991], .source 18231⟩,
    ⟨[36333, 89077], [36333, 89077], .contexts []⟩,
    ⟨[36333, 89077], [36333, 89077], .contexts []⟩,
    ⟨[96757, 9], [96757, 9], .contexts []⟩,
    ⟨[89077], [89077], .contexts []⟩,
    ⟨[96757, 9], [36333, 89077], .contexts [
        ⟨99898, false, false, [], []⟩,
        ⟨99888, true, false, [], [9]⟩,
        ⟨452, false, false, [96755], []⟩,
        ⟨455, false, false, [96755], []⟩,
        ⟨99871, false, false, [], [1, 9, 1]⟩,
        ⟨95679, false, false, [22243], [9, 1]⟩,
        ⟨99895, true, false, [], [89081, 9, 1]⟩,
        ⟨53901, false, false, [36333], [1]⟩,
        ⟨53897, false, false, [36333], []⟩,
        ⟨99896, false, false, [], []⟩,
        ⟨99897, false, false, [], []⟩,
        ⟨99899, false, false, [36333], []⟩,
        ⟨13, true, false, [], [36333, 89077]⟩
      ]⟩,
    ⟨[36335], [36332], .source 18232⟩,
    ⟨[36317, 85933], [36317, 85933], .contexts []⟩,
    ⟨[36317, 85931], [36317, 85931], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1561. -/
def y322TCIndexRaw1561 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[96757, 11], [36317, 85931], .contexts [
        ⟨99888, true, false, [], [11]⟩,
        ⟨110, false, false, [96755], []⟩,
        ⟨111, false, false, [96755], []⟩,
        ⟨99863, false, false, [], [1]⟩,
        ⟨99865, false, false, [], [1]⟩,
        ⟨99902, false, false, [], [1]⟩,
        ⟨99902, false, false, [], [1]⟩,
        ⟨34228, false, false, [36317], []⟩,
        ⟨99903, false, false, [], []⟩,
        ⟨35907, false, false, [36317], []⟩,
        ⟨99864, true, false, [], [85931]⟩
      ]⟩,
    ⟨[96757, 13], [96757, 13], .contexts []⟩,
    ⟨[96757, 13], [35481, 85199], .contexts [
        ⟨99905, false, false, [], []⟩,
        ⟨99888, true, false, [], [13]⟩,
        ⟨115, false, false, [96755], []⟩,
        ⟨118, false, false, [96755], []⟩,
        ⟨99869, false, false, [], [1, 13, 1]⟩,
        ⟨99870, false, false, [], [1, 13, 1]⟩,
        ⟨99867, false, false, [], [1, 13, 1]⟩,
        ⟨99868, false, false, [], [1, 13, 1]⟩,
        ⟨99868, false, false, [], [1, 13, 1]⟩,
        ⟨33240, false, false, [7357], [13, 1]⟩,
        ⟨48317, false, false, [], [13, 1]⟩,
        ⟨48318, false, false, [], [13, 1]⟩,
        ⟨33263, false, false, [7357], [1]⟩,
        ⟨51792, false, false, [7357], []⟩,
        ⟨97396, true, false, [], [85199]⟩,
        ⟨51802, false, false, [35481], []⟩
      ]⟩,
    ⟨[96757, 13], [35481, 85199], .contexts [
        ⟨99906, false, false, [], []⟩,
        ⟨97400, true, false, [], [85199]⟩
      ]⟩,
    ⟨[85199, 13], [35483, 96757], .contexts [
        ⟨99907, true, false, [35480], [13]⟩,
        ⟨59, false, false, [35480, 96757], []⟩,
        ⟨97402, true, false, [], [96757]⟩
      ]⟩,
    ⟨[36077, 95357, 9], [36077, 95355], .contexts [
        ⟨89513, false, false, [36077], []⟩
      ]⟩,
    ⟨[96757, 9], [36333, 89077], .contexts [
        ⟨99898, false, false, [], []⟩,
        ⟨99900, false, false, [], []⟩,
        ⟨99896, false, false, [], []⟩,
        ⟨99897, false, false, [], []⟩,
        ⟨99897, false, false, [], []⟩
      ]⟩,
    ⟨[36337], [36079, 36333], .source 18233⟩,
    ⟨[36339], [36336], .source 18234⟩,
    ⟨[89075], [36339, 95355], .contexts [
        ⟨83770, true, false, [], []⟩,
        ⟨99911, false, false, [36336], [89077, 5]⟩,
        ⟨99048, false, false, [36336], [36333, 89077, 5]⟩,
        ⟨99899, true, false, [36336, 36076, 36333], [5]⟩,
        ⟨99910, true, false, [36336, 36076], [5]⟩,
        ⟨47, true, false, [36336, 36076, 96757], [5]⟩,
        ⟨960, true, false, [36336, 36076, 96757], [5]⟩,
        ⟨99892, false, false, [36336, 36076], [9, 5, 5]⟩,
        ⟨99893, false, false, [36336, 36076], [9, 5, 5]⟩,
        ⟨99890, false, false, [36336, 36076], [9, 5, 5]⟩,
        ⟨99891, false, false, [36336, 36076], [9, 5, 5]⟩,
        ⟨99891, false, false, [36336, 36076], [9, 5, 5]⟩,
        ⟨99909, false, false, [36336, 36076], [5, 5]⟩,
        ⟨28, false, false, [36336, 95355], []⟩,
        ⟨99912, true, false, [], [95355]⟩
      ]⟩,
    ⟨[36339], [36339], .contexts []⟩,
    ⟨[36339], [36339], .contexts []⟩,
    ⟨[36337], [36338], .contexts [
        ⟨99912, true, true, [], []⟩
      ]⟩,
    ⟨[95355], [36337, 89075], .contexts [
        ⟨99914, false, false, [36338], [95355]⟩,
        ⟨99915, false, false, [36338], [95355]⟩,
        ⟨99913, true, false, [36338], []⟩,
        ⟨99916, true, false, [], [89075]⟩
      ]⟩,
    ⟨[36336], [36336], .contexts []⟩,
    ⟨[36339], [36336], .contexts [
        ⟨99912, false, false, [], []⟩,
        ⟨99918, false, false, [], []⟩,
        ⟨99918, false, false, [], []⟩
      ]⟩,
    ⟨[89075, 1], [36339, 95353], .contexts [
        ⟨99917, true, false, [36336], [1]⟩,
        ⟨89509, false, false, [36336], []⟩,
        ⟨89551, false, false, [36336], []⟩,
        ⟨99919, true, false, [], [95353]⟩
      ]⟩,
    ⟨[89075, 9], [36339, 95357], .contexts [
        ⟨99917, true, false, [36336], [9]⟩,
        ⟨89511, false, false, [36336], []⟩,
        ⟨89547, false, false, [36336], []⟩,
        ⟨99919, true, false, [], [95357]⟩
      ]⟩,
    ⟨[36341], [36339, 32965], .source 18235⟩,
    ⟨[89075, 7], [36341, 83887], .contexts [
        ⟨99917, true, false, [36336], [7]⟩,
        ⟨89858, false, false, [36336], []⟩,
        ⟨89860, false, false, [36336], []⟩,
        ⟨99912, true, false, [], [32965, 83887]⟩,
        ⟨99922, true, false, [], [83887]⟩
      ]⟩,
    ⟨[95355], [36337, 89075], .contexts [
        ⟨99917, false, false, [], []⟩
      ]⟩,
    ⟨[36337, 89075], [36337, 89075], .contexts []⟩,
    ⟨[95355], [36337, 89075], .contexts [
        ⟨99924, false, false, [], []⟩,
        ⟨99925, false, false, [], []⟩
      ]⟩,
    ⟨[36343], [36339, 32961], .source 18236⟩,
    ⟨[36345], [36342], .source 18237⟩,
    ⟨[93783], [36345, 89073], .contexts [
        ⟨99927, false, false, [36342], [93783]⟩,
        ⟨99912, false, false, [36342], [32961, 93783]⟩,
        ⟨89846, false, false, [36342, 36336], [93783]⟩,
        ⟨89847, false, false, [36342, 36336], [93783]⟩,
        ⟨89847, false, false, [36342, 36336], [93783]⟩,
        ⟨80914, true, false, [36342, 36336, 32958], []⟩,
        ⟨80914, true, false, [36342, 36336, 32958], []⟩,
        ⟨80975, true, false, [36342, 36336, 32958], []⟩,
        ⟨80974, true, false, [36342, 36336, 32958], []⟩,
        ⟨47, true, false, [36342, 36336, 32958, 93785], []⟩,
        ⟨573, true, false, [36342, 36336, 32958, 93785], []⟩,
        ⟨89845, false, false, [36342, 36336, 32958], [9, 3]⟩,
        ⟨89513, false, false, [36342, 36336], [3]⟩,
        ⟨99926, false, false, [36342, 36336], [3]⟩,
        ⟨53889, false, false, [36342], []⟩,
        ⟨99928, true, false, [], [89073]⟩
      ]⟩,
    ⟨[36343], [36344], .contexts [
        ⟨99928, true, true, [], []⟩
      ]⟩,
    ⟨[36344], [36344], .contexts []⟩,
    ⟨[36347], [36343, 30731], .source 18238⟩,
    ⟨[36349], [36343, 30721], .source 18239⟩,
    ⟨[93783], [36345, 89073], .contexts [
        ⟨99929, false, false, [], []⟩
      ]⟩,
    ⟨[93783], [36345, 89073], .contexts [
        ⟨99934, false, false, [], []⟩
      ]⟩,
    ⟨[36351], [36345, 31181], .source 18240⟩,
    ⟨[30735], [30735], .contexts []⟩,
    ⟨[36353], [36350], .source 18241⟩,
    ⟨[36355], [36353, 30735], .source 18242⟩,
    ⟨[94283], [36355, 85915], .contexts [
        ⟨99936, false, false, [36350], [94283]⟩,
        ⟨83780, true, false, [36350, 36345], []⟩,
        ⟨99935, true, false, [36350], [15]⟩,
        ⟨81353, false, false, [36350], []⟩,
        ⟨81382, false, false, [36350], []⟩,
        ⟨99937, true, false, [36350], [85915]⟩,
        ⟨99938, true, false, [], [30735, 85915]⟩,
        ⟨99939, true, false, [], [85915]⟩
      ]⟩,
    ⟨[36357], [36354], .source 18243⟩,
    ⟨[36354], [36354], .contexts []⟩,
    ⟨[94283], [36355, 85915], .contexts [
        ⟨99940, false, false, [], []⟩
      ]⟩,
    ⟨[36359], [36357, 31183], .source 18244⟩,
    ⟨[36361], [36358], .source 18245⟩,
    ⟨[89069], [36361, 85913], .contexts [
        ⟨99944, false, false, [36358], [89069]⟩,
        ⟨99941, false, false, [36358], [31183, 89069]⟩,
        ⟨83654, false, false, [36358, 36354], [89069]⟩,
        ⟨83788, true, false, [36358, 36354], []⟩,
        ⟨83641, false, false, [36358, 36354], [89069]⟩,
        ⟨83788, true, false, [36358, 36354, 31180, 31182], []⟩,
        ⟨53883, true, false, [36358, 36354, 31180], []⟩,
        ⟨83786, true, false, [36358, 36354, 31180, 31182], [15]⟩,
        ⟨83423, false, false, [36358, 36354, 31180, 31182], []⟩,
        ⟨83495, false, false, [36358, 36354, 31180, 31182], []⟩,
        ⟨13, true, false, [36358, 36354, 31180, 31182], [94281]⟩,
        ⟨83689, true, false, [36358, 36354, 31180], [94281]⟩,
        ⟨83428, true, false, [36358, 36354], []⟩,
        ⟨99943, false, false, [36358, 36354], [1]⟩,
        ⟨34192, false, false, [36358], []⟩,
        ⟨99945, true, false, [], [85913]⟩
      ]⟩,
    ⟨[36360], [36360], .contexts []⟩,
    ⟨[85913, 13], [36359, 89067], .contexts [
        ⟨99946, true, false, [36360], [13]⟩,
        ⟨53879, false, false, [36360], []⟩,
        ⟨53960, false, false, [36360], []⟩,
        ⟨99947, true, false, [], [89067]⟩,
        ⟨99947, true, false, [], [89067]⟩,
        ⟨99945, false, true, [], [89067]⟩
      ]⟩,
    ⟨[89069], [36361, 85913], .contexts [
        ⟨99946, false, false, [], []⟩
      ]⟩,
    ⟨[89069], [36361, 85913], .contexts [
        ⟨99949, false, false, [], []⟩
      ]⟩,
    ⟨[36363], [36361, 30733], .source 18246⟩,
    ⟨[36365], [36362], .source 18247⟩,
    ⟨[93781], [36365, 89071], .contexts [
        ⟨99951, false, false, [36362], [93781]⟩,
        ⟨81389, true, false, [36362, 36361], []⟩,
        ⟨99950, true, false, [36362], [15]⟩,
        ⟨53881, false, false, [36362], []⟩,
        ⟨53958, false, false, [36362], []⟩,
        ⟨13, true, false, [36362], [89071]⟩,
        ⟨99952, true, false, [], [89071]⟩
      ]⟩,
    ⟨[36363], [36364], .contexts [
        ⟨99952, true, true, [], []⟩
      ]⟩,
    ⟨[36364], [36364], .contexts []⟩,
    ⟨[36367], [36363, 30731], .source 18248⟩,
    ⟨[35481, 85199], [35481, 85199], .contexts []⟩,
    ⟨[89077, 13], [89077, 13], .contexts []⟩,
    ⟨[36369], [36335, 35481], .source 18249⟩,
    ⟨[89077, 13], [36369, 85197], .contexts [
        ⟨99958, false, false, [], []⟩,
        ⟨99910, true, false, [36332], [13]⟩,
        ⟨201, false, false, [36332, 96757], []⟩,
        ⟨202, false, false, [36332, 96757], []⟩,
        ⟨99905, false, false, [36332], [9]⟩,
        ⟨99907, false, false, [36332], [9]⟩,
        ⟨99957, false, false, [36332], [9]⟩,
        ⟨99957, false, false, [36332], [9]⟩,
        ⟨30429, false, false, [36332, 35481], []⟩,
        ⟨51809, false, false, [36332, 35481], []⟩,
        ⟨99901, true, false, [], [35481, 85197]⟩,
        ⟨99959, true, false, [], [85197]⟩
      ]⟩,
    ⟨[36371], [36368], .source 18250⟩,
    ⟨[89077, 1], [89079], .contexts [
        ⟨53895, false, false, [], []⟩
      ]⟩,
    ⟨[36339, 95353], [36339, 95353], .contexts []⟩,
    ⟨[36339, 95353], [36339, 95353], .contexts []⟩,
    ⟨[89079, 5], [36339, 95353], .contexts [
        ⟨53900, true, false, [], [5]⟩,
        ⟨53900, true, false, [], [5]⟩,
        ⟨53952, true, false, [], [5]⟩,
        ⟨99962, true, false, [], [5]⟩,
        ⟨53896, true, false, [], [1, 5]⟩,
        ⟨53896, true, false, [], [1, 5]⟩,
        ⟨53954, true, false, [], [1, 5]⟩,
        ⟨53891, true, false, [], [1, 5]⟩,
        ⟨890, false, false, [89075], []⟩,
        ⟨9, false, false, [89075], []⟩,
        ⟨99920, false, false, [], []⟩,
        ⟨99963, false, false, [], []⟩,
        ⟨99964, false, false, [], []⟩,
        ⟨99964, false, false, [], []⟩,
        ⟨89863, false, false, [36339], []⟩,
        ⟨99915, true, false, [], [95353]⟩,
        ⟨99914, true, false, [], [95353]⟩,
        ⟨13, true, false, [], [36339, 95353]⟩
      ]⟩,
    ⟨[36373], [36337, 26437], .source 18251⟩,
    ⟨[36375], [36372], .source 18252⟩]

/-- Exact literal claimed equations and contextual derivations, block 1562. -/
def y322TCIndexRaw1562 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[36375], [36372], .contexts [
        ⟨99967, false, false, [], []⟩,
        ⟨13, false, false, [36372], []⟩
      ]⟩,
    ⟨[36373], [36374], .contexts [
        ⟨99967, true, true, [], []⟩
      ]⟩,
    ⟨[95349], [36373, 90845], .contexts [
        ⟨99968, false, false, [36374], [95349]⟩,
        ⟨89554, true, false, [36374, 36372], []⟩,
        ⟨89503, true, false, [36374, 36372], []⟩,
        ⟨89505, true, false, [36374, 36372], [3]⟩,
        ⟨89505, true, false, [36374, 36372], [3]⟩,
        ⟨89553, true, false, [36374, 36372], [3]⟩,
        ⟨89552, true, false, [36374, 36372], [3]⟩,
        ⟨99965, true, false, [36374, 36372, 36338], [5, 3]⟩,
        ⟨28, false, false, [36374, 36372, 36338, 89079], [3]⟩,
        ⟨99916, true, false, [36374, 36372], [89079, 3]⟩,
        ⟨66889, false, false, [36374, 36372, 36337], []⟩,
        ⟨99966, true, false, [36374, 36372], [90845]⟩,
        ⟨99969, true, false, [], [90845]⟩
      ]⟩,
    ⟨[36373, 90843], [36373, 90843], .contexts []⟩,
    ⟨[36377], [36373, 29315], .source 18253⟩,
    ⟨[36377, 92931], [95345], .contexts [
        ⟨99972, false, false, [], [92931]⟩,
        ⟨76389, true, false, [36373], []⟩,
        ⟨99971, true, false, [], [15]⟩,
        ⟨99969, false, false, [], [90843, 15]⟩,
        ⟨99971, true, false, [36374, 36372], [15]⟩,
        ⟨63053, true, false, [36374], [15]⟩,
        ⟨99970, true, false, [36374, 36372], [1, 15]⟩,
        ⟨89500, false, false, [36374, 36372], [15]⟩,
        ⟨89555, false, false, [36374, 36372], [15]⟩,
        ⟨99968, true, false, [36374], [95347, 15]⟩,
        ⟨89497, false, false, [], []⟩
      ]⟩,
    ⟨[36379], [36376], .source 18254⟩,
    ⟨[36379], [36376], .contexts [
        ⟨99974, false, false, [], []⟩
      ]⟩,
    ⟨[36377], [36378], .contexts [
        ⟨99974, true, true, [], []⟩
      ]⟩,
    ⟨[36376], [36376], .contexts []⟩,
    ⟨[92931, 13], [36379, 95343], .contexts [
        ⟨99976, false, false, [36376], [92931, 13]⟩,
        ⟨99973, false, false, [36376, 36378, 36376], [13]⟩,
        ⟨89556, false, false, [36376, 36378, 36376], [13]⟩,
        ⟨13, true, false, [36376, 36378, 36376], [95345, 13]⟩,
        ⟨99975, true, false, [36376, 36378], [95345, 13]⟩,
        ⟨89494, false, false, [36376], []⟩,
        ⟨89558, false, false, [36376], []⟩,
        ⟨99977, true, false, [], [95343]⟩,
        ⟨99977, true, false, [], [95343]⟩,
        ⟨99975, true, false, [], [95343]⟩
      ]⟩,
    ⟨[89075, 15], [31181, 94285], .contexts [
        ⟨83773, true, false, [31182], [15]⟩,
        ⟨1, false, false, [31182, 94285], []⟩,
        ⟨83659, true, false, [], [94285]⟩,
        ⟨83768, false, false, [], []⟩,
        ⟨83769, false, false, [], []⟩,
        ⟨83769, false, false, [], []⟩
      ]⟩,
    ⟨[36341, 83887], [36341, 83887], .contexts []⟩,
    ⟨[36341, 83887], [36341, 83887], .contexts []⟩,
    ⟨[89075, 7], [36341, 83887], .contexts [
        ⟨99923, false, false, [], []⟩,
        ⟨99980, false, false, [], []⟩,
        ⟨99981, false, false, [], []⟩,
        ⟨99981, false, false, [], []⟩
      ]⟩,
    ⟨[36381], [36341, 30805], .source 18255⟩,
    ⟨[94285, 7], [94285, 7], .contexts []⟩,
    ⟨[36383], [31183, 36381], .source 18256⟩,
    ⟨[94285, 7], [36383, 93915], .contexts [
        ⟨99984, false, false, [], []⟩,
        ⟨99979, true, false, [31180], [7]⟩,
        ⟨37, false, false, [31180, 89075], []⟩,
        ⟨40, false, false, [31180, 89075], []⟩,
        ⟨99982, false, false, [31180], [15]⟩,
        ⟨81955, false, false, [31180, 36341], []⟩,
        ⟨99983, true, false, [31180], [93915]⟩,
        ⟨81954, false, false, [31180, 36381], []⟩,
        ⟨83655, true, false, [], [36381, 93915]⟩,
        ⟨99985, true, false, [], [93915]⟩
      ]⟩,
    ⟨[36385], [36382], .source 18257⟩,
    ⟨[93915, 7], [36385, 94285], .contexts [
        ⟨99986, true, false, [36382], [7]⟩,
        ⟨38, false, false, [36382, 94285], []⟩,
        ⟨99987, true, false, [], [94285]⟩
      ]⟩,
    ⟨[36339, 95357], [36339, 95357], .contexts []⟩,
    ⟨[36339, 95357], [36339, 95357], .contexts []⟩,
    ⟨[36387], [36339, 32969], .source 18258⟩,
    ⟨[36389], [31183, 36387], .source 18259⟩,
    ⟨[36391], [36388], .source 18260⟩,
    ⟨[36369, 85197], [36369, 85197], .contexts []⟩,
    ⟨[89077, 13], [36369, 85197], .contexts [
        ⟨99958, false, false, [], []⟩,
        ⟨99960, false, false, [], []⟩,
        ⟨99994, false, false, [], []⟩,
        ⟨99994, false, false, [], []⟩
      ]⟩,
    ⟨[89079, 13], [23609, 83887], .contexts [
        ⟨54198, false, false, [], []⟩
      ]⟩,
    ⟨[85195, 13], [85195, 13], .contexts []⟩,
    ⟨[36393], [36371, 23609], .source 18261⟩,
    ⟨[85195, 13], [36393, 83885], .contexts [
        ⟨99997, false, false, [], []⟩,
        ⟨30425, true, false, [], [13]⟩,
        ⟨99995, true, false, [36368], [1, 13]⟩,
        ⟨1968, false, false, [36368, 89077], []⟩,
        ⟨248, false, false, [36368, 89077], []⟩,
        ⟨99962, false, false, [36368], [13, 1]⟩,
        ⟨53952, false, false, [36368], [13, 1]⟩,
        ⟨53900, false, false, [36368], [13, 1]⟩,
        ⟨53900, false, false, [36368], [13, 1]⟩,
        ⟨99996, false, false, [36368], [1]⟩,
        ⟨54191, false, false, [36368], [1]⟩,
        ⟨54192, false, false, [36368], [1]⟩,
        ⟨54192, false, false, [36368], [1]⟩,
        ⟨23331, false, false, [36368, 23609], []⟩,
        ⟨81989, false, false, [36368, 23609], []⟩,
        ⟨99961, true, false, [], [23609, 83885]⟩,
        ⟨99998, true, false, [], [83885]⟩
      ]⟩,
    ⟨[36395], [36392], .source 18262⟩,
    ⟨[83885, 13], [36395, 85195], .contexts [
        ⟨99999, true, false, [36392], [13]⟩,
        ⟨59, false, false, [36392, 85195], []⟩,
        ⟨100000, true, false, [], [85195]⟩
      ]⟩,
    ⟨[29313, 85455], [29313, 85455], .contexts []⟩,
    ⟨[29313, 85455], [29313, 85455], .contexts []⟩,
    ⟨[36379, 95343], [36379, 95343], .contexts []⟩,
    ⟨[92931, 13], [36379, 95343], .contexts [
        ⟨99978, false, false, [], []⟩,
        ⟨100004, false, false, [], []⟩,
        ⟨100004, false, false, [], []⟩
      ]⟩,
    ⟨[85453, 13], [85453, 13], .contexts []⟩,
    ⟨[95341], [95341], .contexts []⟩,
    ⟨[36397], [29311, 36379], .source 18263⟩,
    ⟨[85453, 13], [36397, 95341], .contexts [
        ⟨100006, false, false, [], []⟩,
        ⟨31991, true, false, [], [13]⟩,
        ⟨100003, true, false, [29312], [1, 13]⟩,
        ⟨100003, true, false, [29312], [1, 13]⟩,
        ⟨100002, true, false, [29312], [1, 13]⟩,
        ⟨76355, true, false, [29312], [1, 13]⟩,
        ⟨75933, true, false, [29312], [13, 1, 13]⟩,
        ⟨75933, true, false, [29312], [13, 1, 13]⟩,
        ⟨75996, true, false, [29312], [13, 1, 13]⟩,
        ⟨75928, true, false, [29312], [13, 1, 13]⟩,
        ⟨919, false, false, [29312, 92931], []⟩,
        ⟨116, false, false, [29312, 92931], []⟩,
        ⟨100005, false, false, [29312], [1]⟩,
        ⟨89491, false, false, [29312, 36379], []⟩,
        ⟨100007, false, false, [29312, 36379], []⟩,
        ⟨76356, true, false, [], [36379, 95341]⟩,
        ⟨100008, true, false, [], [95341]⟩
      ]⟩,
    ⟨[36399], [36396], .source 18264⟩,
    ⟨[95341, 13], [36399, 85453], .contexts [
        ⟨100009, true, false, [36396], [13]⟩,
        ⟨59, false, false, [36396, 85453], []⟩,
        ⟨100010, true, false, [], [85453]⟩
      ]⟩,
    ⟨[36383, 93915], [36383, 93915], .contexts []⟩,
    ⟨[36383, 93915], [36383, 93915], .contexts []⟩,
    ⟨[36401], [36383, 30807], .source 18265⟩,
    ⟨[36403], [36401, 22659], .source 18266⟩,
    ⟨[36405], [36402], .source 18267⟩,
    ⟨[36402], [36402], .contexts []⟩,
    ⟨[83449, 13], [36405, 94285], .contexts [
        ⟨100015, false, false, [36402], [83449, 13]⟩,
        ⟨49926, true, false, [36402, 36401], [13]⟩,
        ⟨100014, false, false, [36402], [88317, 7, 13]⟩,
        ⟨81974, true, false, [36402, 36383], [7, 13]⟩,
        ⟨100013, true, false, [36402], [13, 7, 13]⟩,
        ⟨100013, true, false, [36402], [13, 7, 13]⟩,
        ⟨100012, true, false, [36402], [13, 7, 13]⟩,
        ⟨99986, true, false, [36402], [13, 7, 13]⟩,
        ⟨99984, true, false, [36402], [13, 7, 13]⟩,
        ⟨15654, false, false, [36402, 94285], []⟩,
        ⟨100017, true, false, [], [94285]⟩,
        ⟨100017, true, false, [], [94285]⟩,
        ⟨100016, true, false, [], [94285]⟩
      ]⟩,
    ⟨[36393, 83885], [36393, 83885], .contexts []⟩,
    ⟨[36393, 83885], [36393, 83885], .contexts []⟩,
    ⟨[36393, 83883], [36393, 83883], .contexts []⟩,
    ⟨[36393, 83883], [36393, 83883], .contexts []⟩,
    ⟨[83883, 13], [83883, 13], .contexts []⟩,
    ⟨[85193], [85193], .contexts []⟩,
    ⟨[36392], [36392], .contexts []⟩,
    ⟨[83883, 13], [36395, 85193], .contexts [
        ⟨100023, false, false, [], []⟩,
        ⟨100022, true, false, [36392], [13]⟩,
        ⟨100021, true, false, [36392], [13]⟩,
        ⟨23327, true, false, [], [13]⟩,
        ⟨100020, true, false, [36392], [5, 13]⟩,
        ⟨100020, true, false, [36392], [5, 13]⟩,
        ⟨100019, true, false, [36392], [5, 13]⟩,
        ⟨99999, true, false, [36392], [5, 13]⟩,
        ⟨99997, true, false, [36392], [5, 13]⟩,
        ⟨1136, false, false, [36392, 85195], []⟩,
        ⟨29, false, false, [36392, 85195], []⟩,
        ⟨30525, false, false, [36392], []⟩,
        ⟨30526, false, false, [36392], []⟩,
        ⟨30420, false, false, [36392], []⟩,
        ⟨30420, false, false, [36392], []⟩,
        ⟨100024, false, false, [36392], []⟩,
        ⟨100025, true, false, [], [85193]⟩,
        ⟨100025, true, false, [], [85193]⟩,
        ⟨100000, true, false, [], [85193]⟩
      ]⟩,
    ⟨[36393], [36394], .contexts [
        ⟨100000, true, true, [], []⟩
      ]⟩,
    ⟨[85193, 13], [36393, 83883], .contexts [
        ⟨100026, true, false, [36394], [13]⟩,
        ⟨59, false, false, [36394, 83883], []⟩,
        ⟨100027, true, false, [], [83883]⟩
      ]⟩,
    ⟨[36397, 95341], [36397, 95341], .contexts []⟩,
    ⟨[36407], [29293, 36397], .source 18268⟩,
    ⟨[95341, 9], [95341, 9], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1563. -/
def y322TCIndexRaw1563 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[36409], [36399, 36407], .source 18269⟩,
    ⟨[95341, 9], [36409, 95341], .contexts [
        ⟨100031, false, false, [], []⟩,
        ⟨100029, true, false, [36396], [9]⟩,
        ⟨100029, true, false, [36396], [9]⟩,
        ⟨100009, true, false, [36396], [9]⟩,
        ⟨100006, true, false, [36396], [9]⟩,
        ⟨77, false, false, [36396, 85453], []⟩,
        ⟨78, false, false, [36396, 85453], []⟩,
        ⟨76396, false, false, [36396], [13]⟩,
        ⟨100009, false, false, [36396, 29293], []⟩,
        ⟨100030, true, false, [36396], [95341]⟩,
        ⟨100007, false, false, [36396, 36407], []⟩,
        ⟨100010, true, false, [], [36407, 95341]⟩,
        ⟨100032, true, false, [], [95341]⟩
      ]⟩,
    ⟨[36395, 85193], [36395, 85193], .contexts []⟩,
    ⟨[36395, 85193], [36395, 85193], .contexts []⟩,
    ⟨[36395, 85191], [36395, 85191], .contexts []⟩,
    ⟨[85191, 13], [85191, 13], .contexts []⟩,
    ⟨[36394], [36394], .contexts []⟩,
    ⟨[85191, 13], [36393, 83881], .contexts [
        ⟨100037, false, false, [], []⟩,
        ⟨100036, true, false, [36394], [13]⟩,
        ⟨30417, true, false, [], [13]⟩,
        ⟨100035, true, false, [36394], [3, 13]⟩,
        ⟨100035, true, false, [36394], [3, 13]⟩,
        ⟨100034, true, false, [36394], [3, 13]⟩,
        ⟨100026, true, false, [36394], [3, 13]⟩,
        ⟨100023, true, false, [36394], [3, 13]⟩,
        ⟨1132, false, false, [36394, 83883], []⟩,
        ⟨82006, false, false, [36394], []⟩,
        ⟨82005, false, false, [36394], []⟩,
        ⟨82008, false, false, [36394], []⟩,
        ⟨100038, true, false, [], [83881]⟩,
        ⟨100038, true, false, [], [83881]⟩,
        ⟨100027, true, false, [], [83881]⟩
      ]⟩,
    ⟨[36409, 95341], [36409, 95341], .contexts []⟩,
    ⟨[95341, 11], [95339], .contexts [
        ⟨89560, false, false, [], []⟩,
        ⟨89561, false, false, [], []⟩,
        ⟨89487, false, false, [], []⟩,
        ⟨89487, false, false, [], []⟩
      ]⟩,
    ⟨[95337, 11], [95337, 11], .contexts []⟩,
    ⟨[95337], [95337], .contexts []⟩,
    ⟨[36411], [36408], .source 18270⟩,
    ⟨[36411], [36411], .contexts []⟩,
    ⟨[36408], [36408], .contexts []⟩,
    ⟨[36411], [36408], .contexts [
        ⟨100045, false, false, [], []⟩,
        ⟨100044, false, false, [], []⟩,
        ⟨100046, false, false, [], []⟩,
        ⟨100046, false, false, [], []⟩
      ]⟩,
    ⟨[95337, 11], [36411, 95337], .contexts [
        ⟨100042, false, false, [], []⟩,
        ⟨89485, true, false, [], [11]⟩,
        ⟨89488, true, false, [], [9, 11]⟩,
        ⟨100040, true, false, [36408], [11, 9, 11]⟩,
        ⟨100040, true, false, [36408], [11, 9, 11]⟩,
        ⟨100033, true, false, [36408], [11, 9, 11]⟩,
        ⟨100031, true, false, [36408], [11, 9, 11]⟩,
        ⟨536, false, false, [36408, 95341], []⟩,
        ⟨537, false, false, [36408, 95341], []⟩,
        ⟨100041, false, false, [36408], [9]⟩,
        ⟨89562, false, false, [36408], []⟩,
        ⟨89563, false, false, [36408], []⟩,
        ⟨89484, false, false, [36408], []⟩,
        ⟨89484, false, false, [36408], []⟩,
        ⟨100043, false, false, [36408], []⟩,
        ⟨100047, true, false, [], [95337]⟩
      ]⟩,
    ⟨[36393, 83881], [36393, 83881], .contexts []⟩,
    ⟨[36393, 83881], [36393, 83881], .contexts []⟩,
    ⟨[36413], [36393, 30805], .source 18271⟩,
    ⟨[36413, 93901], [36413, 93901], .contexts []⟩,
    ⟨[36413, 93901], [36413, 93901], .contexts []⟩,
    ⟨[36413, 93901, 13], [85189], .contexts [
        ⟨100053, true, false, [], [13]⟩,
        ⟨100052, true, false, [], [13]⟩,
        ⟨81726, true, false, [36413], [13]⟩,
        ⟨100051, false, false, [], [93903, 1, 13]⟩,
        ⟨82023, true, false, [36393], [1, 13]⟩,
        ⟨23319, true, false, [36393], [13, 1, 13]⟩,
        ⟨100050, true, false, [], [1, 13, 1, 13]⟩,
        ⟨100050, true, false, [], [1, 13, 1, 13]⟩,
        ⟨100049, true, false, [], [1, 13, 1, 13]⟩,
        ⟨100039, true, false, [], [1, 13, 1, 13]⟩,
        ⟨100037, true, false, [], [1, 13, 1, 13]⟩,
        ⟨2012, false, false, [85191], []⟩,
        ⟨9, false, false, [85191], []⟩,
        ⟨30529, false, false, [], []⟩,
        ⟨30530, false, false, [], []⟩,
        ⟨30412, false, false, [], []⟩,
        ⟨30412, false, false, [], []⟩
      ]⟩,
    ⟨[93901, 13], [93901, 13], .contexts []⟩,
    ⟨[85189], [85189], .contexts []⟩,
    ⟨[36415], [36412], .source 18272⟩,
    ⟨[36415], [36412], .contexts [
        ⟨100057, false, false, [], []⟩
      ]⟩,
    ⟨[36412], [36412], .contexts []⟩,
    ⟨[93901, 13], [36415, 85189], .contexts [
        ⟨100055, false, false, [], []⟩,
        ⟨100054, false, false, [36412], []⟩,
        ⟨100056, false, false, [36412], []⟩,
        ⟨100059, true, false, [], [85189]⟩,
        ⟨100059, true, false, [], [85189]⟩,
        ⟨100058, true, false, [], [85189]⟩
      ]⟩,
    ⟨[85189, 13], [36413, 93901], .contexts [
        ⟨100060, true, false, [36414], [13]⟩,
        ⟨59, false, false, [36414, 93901], []⟩,
        ⟨100057, false, true, [], [93901]⟩
      ]⟩,
    ⟨[36411, 95337], [36411, 95337], .contexts []⟩,
    ⟨[36411, 95337], [36411, 95337], .contexts []⟩,
    ⟨[95335, 11], [95335, 11], .contexts []⟩,
    ⟨[95335], [95335], .contexts []⟩,
    ⟨[36410], [36410], .contexts []⟩,
    ⟨[36409], [36410], .contexts [
        ⟨100044, true, true, [], []⟩,
        ⟨100066, false, false, [], []⟩,
        ⟨100066, false, false, [], []⟩
      ]⟩,
    ⟨[95335, 11], [36409, 95335], .contexts [
        ⟨100064, false, false, [], []⟩,
        ⟨89481, true, false, [], [11]⟩,
        ⟨100063, true, false, [36410], [1, 11]⟩,
        ⟨100063, true, false, [36410], [1, 11]⟩,
        ⟨100062, true, false, [36410], [1, 11]⟩,
        ⟨100048, true, false, [36410], [1, 11]⟩,
        ⟨100042, true, false, [36410], [1, 11]⟩,
        ⟨567, false, false, [36410, 95337], []⟩,
        ⟨9, false, false, [36410, 95337], []⟩,
        ⟨89564, false, false, [36410], []⟩,
        ⟨89565, false, false, [36410], []⟩,
        ⟨89480, false, false, [36410], []⟩,
        ⟨89480, false, false, [36410], []⟩,
        ⟨100065, false, false, [36410], []⟩,
        ⟨100067, true, false, [], [95335]⟩
      ]⟩,
    ⟨[36409, 95335], [36409, 95335], .contexts []⟩,
    ⟨[36409, 95335], [36409, 95335], .contexts []⟩,
    ⟨[95333, 11], [95333, 11], .contexts []⟩,
    ⟨[95333], [95333], .contexts []⟩,
    ⟨[95333, 11], [36411, 95333], .contexts [
        ⟨100071, false, false, [], []⟩,
        ⟨89477, true, false, [], [11]⟩,
        ⟨100070, true, false, [36408], [5, 11]⟩,
        ⟨100070, true, false, [36408], [5, 11]⟩,
        ⟨100069, true, false, [36408], [5, 11]⟩,
        ⟨100068, true, false, [36408], [5, 11]⟩,
        ⟨100064, true, false, [36408], [5, 11]⟩,
        ⟨588, false, false, [36408, 95335], []⟩,
        ⟨29, false, false, [36408, 95335], []⟩,
        ⟨89567, false, false, [36408], []⟩,
        ⟨89568, false, false, [36408], []⟩,
        ⟨89476, false, false, [36408], []⟩,
        ⟨89476, false, false, [36408], []⟩,
        ⟨100072, false, false, [36408], []⟩,
        ⟨100047, true, false, [], [95333]⟩
      ]⟩,
    ⟨[36411, 95333], [36411, 95333], .contexts []⟩,
    ⟨[36411, 95333], [36411, 95333], .contexts []⟩,
    ⟨[95331, 11], [95331, 11], .contexts []⟩,
    ⟨[95331], [95331], .contexts []⟩,
    ⟨[95331, 11], [36409, 95331], .contexts [
        ⟨100076, false, false, [], []⟩,
        ⟨89473, true, false, [], [11]⟩,
        ⟨100075, true, false, [36410], [3, 11]⟩,
        ⟨100075, true, false, [36410], [3, 11]⟩,
        ⟨100074, true, false, [36410], [3, 11]⟩,
        ⟨100073, true, false, [36410], [3, 11]⟩,
        ⟨100071, true, false, [36410], [3, 11]⟩,
        ⟨603, false, false, [36410, 95333], []⟩,
        ⟨21, false, false, [36410, 95333], []⟩,
        ⟨89569, false, false, [36410], []⟩,
        ⟨89570, false, false, [36410], []⟩,
        ⟨89472, false, false, [36410], []⟩,
        ⟨89472, false, false, [36410], []⟩,
        ⟨100077, false, false, [36410], []⟩,
        ⟨100067, true, false, [], [95331]⟩
      ]⟩,
    ⟨[36409, 95331], [36409, 95331], .contexts []⟩,
    ⟨[36409, 95331], [36409, 95331], .contexts []⟩,
    ⟨[95331, 1], [95329], .contexts [
        ⟨89571, false, false, [], []⟩,
        ⟨89572, false, false, [], []⟩,
        ⟨89468, false, false, [], []⟩,
        ⟨89468, false, false, [], []⟩
      ]⟩,
    ⟨[95329, 11], [95329, 11], .contexts []⟩,
    ⟨[36411, 95329], [36411, 95329], .contexts []⟩,
    ⟨[95329, 11], [36411, 95329], .contexts [
        ⟨100082, false, false, [], []⟩,
        ⟨100082, false, false, [], []⟩,
        ⟨89469, true, false, [], [11]⟩,
        ⟨100080, true, false, [36408], [1, 11]⟩,
        ⟨100080, true, false, [36408], [1, 11]⟩,
        ⟨100079, true, false, [36408], [1, 11]⟩,
        ⟨100078, true, false, [36408], [1, 11]⟩,
        ⟨100076, true, false, [36408], [1, 11]⟩,
        ⟨567, false, false, [36408, 95331], []⟩,
        ⟨9, false, false, [36408, 95331], []⟩,
        ⟨100081, false, false, [36408], []⟩,
        ⟨100047, true, false, [], [95329]⟩,
        ⟨100083, false, false, [], []⟩,
        ⟨100083, false, false, [], []⟩
      ]⟩,
    ⟨[95327, 11], [95327, 11], .contexts []⟩,
    ⟨[36409, 95327], [36409, 95327], .contexts []⟩,
    ⟨[95327, 11, 13], [36409, 95325], .contexts [
        ⟨100085, false, false, [], [13]⟩,
        ⟨100085, false, false, [], [13]⟩,
        ⟨89466, true, false, [], [11, 13]⟩,
        ⟨100084, true, false, [36410], [15, 11, 13]⟩,
        ⟨615, false, false, [36410, 95329], [13]⟩,
        ⟨10, false, false, [36410, 95329], [13]⟩,
        ⟨89573, false, false, [36410], [13]⟩,
        ⟨89574, false, false, [36410], [13]⟩,
        ⟨89465, false, false, [36410], [13]⟩,
        ⟨89465, false, false, [36410], [13]⟩,
        ⟨100067, true, false, [], [95327, 13]⟩,
        ⟨100086, false, false, [], [13]⟩,
        ⟨100086, false, false, [], [13]⟩,
        ⟨89463, false, false, [36409], []⟩
      ]⟩,
    ⟨[95325, 11], [95325, 11], .contexts []⟩,
    ⟨[95325], [95325], .contexts []⟩,
    ⟨[36411, 95325], [36411, 95325], .contexts []⟩,
    ⟨[36411, 95321], [36411, 95321], .contexts []⟩,
    ⟨[95325, 11, 1, 11], [36411, 95321], .contexts [
        ⟨100088, false, false, [], [1, 11]⟩,
        ⟨100088, false, false, [], [1, 11]⟩,
        ⟨100087, true, false, [36408], [11, 1, 11]⟩,
        ⟨619, false, false, [36408, 95327], [1, 11]⟩,
        ⟨64, false, false, [36408, 95327], [1, 11]⟩,
        ⟨89575, false, false, [36408], [1, 11]⟩,
        ⟨89576, false, false, [36408], [1, 11]⟩,
        ⟨89462, false, false, [36408], [1, 11]⟩,
        ⟨89462, false, false, [36408], [1, 11]⟩,
        ⟨100089, false, false, [36408], [1, 11]⟩,
        ⟨100047, true, false, [], [95325, 1, 11]⟩,
        ⟨100090, false, false, [], [1, 11]⟩,
        ⟨100090, false, false, [], [1, 11]⟩,
        ⟨89460, false, false, [36411], [11]⟩,
        ⟨89457, false, false, [36411], []⟩,
        ⟨100091, false, false, [], []⟩
      ]⟩,
    ⟨[36411, 95321], [36411, 95321], .contexts []⟩,
    ⟨[36411], [36411], .contexts [
        ⟨100045, false, false, [], []⟩
      ]⟩,
    ⟨[96759], [89077, 11], .source 48444⟩]

/-- Exact literal claimed equations and contextual derivations, block 1564. -/
def y322TCIndexRaw1564 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[89077, 11], [96759], .contexts [
        ⟨100095, true, false, [], []⟩
      ]⟩,
    ⟨[96759, 11], [89077], .contexts [
        ⟨100096, true, false, [], [11]⟩,
        ⟨53, false, false, [89077], []⟩,
        ⟨53896, false, false, [], []⟩
      ]⟩,
    ⟨[96759], [96759], .contexts []⟩,
    ⟨[96759], [96759], .contexts []⟩,
    ⟨[89077, 11], [96759], .contexts [
        ⟨100096, false, false, [], []⟩,
        ⟨100098, false, false, [], []⟩,
        ⟨100099, false, false, [], []⟩,
        ⟨100099, false, false, [], []⟩
      ]⟩,
    ⟨[36335, 96757], [36335, 96757], .contexts []⟩,
    ⟨[36417], [36335, 36317], .source 18273⟩,
    ⟨[36419], [36417, 18943], .source 18274⟩,
    ⟨[36419, 96553], [36419, 96553], .contexts []⟩,
    ⟨[36419, 96553], [36419, 96553], .contexts []⟩,
    ⟨[89077, 9, 11, 9, 11], [36419, 96553], .contexts [
        ⟨99900, true, false, [36332], [9, 11, 9, 11]⟩,
        ⟨46, false, false, [36332, 96757], [11, 9, 11]⟩,
        ⟨99901, true, false, [], [96757, 11, 9, 11]⟩,
        ⟨100101, false, false, [], [11, 9, 11]⟩,
        ⟨100101, false, false, [], [11, 9, 11]⟩,
        ⟨99904, false, false, [36335], [9, 11]⟩,
        ⟨100102, true, false, [], [85931, 9, 11]⟩,
        ⟨35912, false, false, [36417], [11]⟩,
        ⟨100103, true, false, [], [86209, 11]⟩,
        ⟨98342, false, false, [36419], []⟩,
        ⟨100104, false, false, [], []⟩,
        ⟨100105, false, false, [], []⟩
      ]⟩,
    ⟨[96759, 9], [96759, 9], .contexts []⟩,
    ⟨[96759, 9], [36419, 96553], .contexts [
        ⟨100107, false, false, [], []⟩,
        ⟨100100, true, false, [], [9]⟩,
        ⟨221, false, false, [89077], []⟩,
        ⟨224, false, false, [89077], []⟩,
        ⟨100106, false, false, [], []⟩,
        ⟨13, true, false, [], [36419, 96553]⟩
      ]⟩,
    ⟨[36421], [36418], .source 18275⟩,
    ⟨[36423], [36369, 35841], .source 18276⟩,
    ⟨[96759, 13], [36423, 96345], .contexts [
        ⟨100100, true, false, [], [13]⟩,
        ⟨227, false, false, [89077], []⟩,
        ⟨228, false, false, [89077], []⟩,
        ⟨99995, false, false, [], [11]⟩,
        ⟨98378, false, false, [36369], []⟩,
        ⟨100110, true, false, [], [96345]⟩,
        ⟨98375, false, false, [36423], []⟩,
        ⟨13, true, false, [], [36423, 96345]⟩
      ]⟩,
    ⟨[36425], [36422], .source 18277⟩,
    ⟨[96761], [96759, 1], .source 48445⟩,
    ⟨[96759, 1], [96761], .contexts [
        ⟨100113, true, false, [], []⟩
      ]⟩,
    ⟨[96761, 1], [96759], .contexts [
        ⟨100114, true, false, [], [1]⟩,
        ⟨8, false, false, [96759], []⟩,
        ⟨100099, false, false, [], []⟩
      ]⟩,
    ⟨[96761], [96761], .contexts []⟩,
    ⟨[96761], [96761], .contexts []⟩,
    ⟨[96759, 1], [96761], .contexts [
        ⟨100114, false, false, [], []⟩,
        ⟨100116, false, false, [], []⟩,
        ⟨100117, false, false, [], []⟩,
        ⟨100117, false, false, [], []⟩
      ]⟩,
    ⟨[36427], [36419, 35827], .source 18278⟩,
    ⟨[36427, 85885], [36427, 85885], .contexts []⟩,
    ⟨[36427, 85885], [36427, 85885], .contexts []⟩,
    ⟨[96761, 9], [96761, 9], .contexts []⟩,
    ⟨[96761, 9], [36427, 85885], .contexts [
        ⟨100122, false, false, [], []⟩,
        ⟨100118, true, false, [], [9]⟩,
        ⟨452, false, false, [96759], []⟩,
        ⟨455, false, false, [96759], []⟩,
        ⟨100107, false, false, [], [1, 9, 1]⟩,
        ⟨100108, false, false, [], [1, 9, 1]⟩,
        ⟨100104, false, false, [], [1, 9, 1]⟩,
        ⟨100105, false, false, [], [1, 9, 1]⟩,
        ⟨100105, false, false, [], [1, 9, 1]⟩,
        ⟨98337, false, false, [36419], [9, 1]⟩,
        ⟨98328, false, false, [36419], [1]⟩,
        ⟨100119, true, false, [], [85883, 1]⟩,
        ⟨34131, false, false, [36427], []⟩,
        ⟨100120, false, false, [], []⟩,
        ⟨100121, false, false, [], []⟩,
        ⟨69337, false, false, [36427], []⟩
      ]⟩,
    ⟨[36427], [36427], .contexts [
        ⟨13, false, false, [], [36427]⟩
      ]⟩,
    ⟨[96761, 9], [36427, 85885], .contexts [
        ⟨100123, false, false, [], []⟩,
        ⟨100124, true, false, [], [85885]⟩
      ]⟩,
    ⟨[36429], [36426], .source 18279⟩,
    ⟨[96761, 11], [96761, 11], .contexts []⟩,
    ⟨[96761, 11], [89079], .contexts [
        ⟨100127, false, false, [], []⟩,
        ⟨100118, true, false, [], [11]⟩,
        ⟨110, false, false, [96759], []⟩,
        ⟨111, false, false, [96759], []⟩,
        ⟨100097, false, false, [], [1]⟩,
        ⟨53954, false, false, [], [1]⟩,
        ⟨53896, false, false, [], [1]⟩,
        ⟨53896, false, false, [], [1]⟩,
        ⟨99962, false, false, [], []⟩,
        ⟨53952, false, false, [], []⟩,
        ⟨53900, false, false, [], []⟩,
        ⟨53900, false, false, [], []⟩,
        ⟨54195, false, false, [], []⟩,
        ⟨672, true, false, [], [89079]⟩
      ]⟩,
    ⟨[89079, 11], [96761], .contexts [
        ⟨100128, true, false, [], [11]⟩,
        ⟨53, false, false, [96761], []⟩,
        ⟨100117, false, false, [], []⟩
      ]⟩,
    ⟨[96761, 9], [36427, 85885], .contexts [
        ⟨100122, false, false, [], []⟩,
        ⟨100125, false, false, [], []⟩,
        ⟨100120, false, false, [], []⟩,
        ⟨100121, false, false, [], []⟩,
        ⟨100121, false, false, [], []⟩
      ]⟩,
    ⟨[36431], [36427, 27123], .source 18280⟩,
    ⟨[36431, 86655], [36431, 86655], .contexts []⟩,
    ⟨[96761], [96761], .contexts []⟩,
    ⟨[36433], [36430], .source 18281⟩,
    ⟨[36430], [36430], .contexts []⟩,
    ⟨[86655, 3], [36433, 96761], .contexts [
        ⟨100132, true, false, [36430], [3]⟩,
        ⟨38314, true, false, [], [3]⟩,
        ⟨100131, false, false, [36430], [86657, 9, 3]⟩,
        ⟨69340, true, false, [36430, 36427], [9, 3]⟩,
        ⟨100130, true, false, [36430], [3, 9, 3]⟩,
        ⟨1439, false, false, [36430, 96761], []⟩,
        ⟨100133, false, false, [36430], []⟩,
        ⟨100135, true, false, [], [96761]⟩,
        ⟨100135, true, false, [], [96761]⟩,
        ⟨100134, true, false, [], [96761]⟩
      ]⟩,
    ⟨[96761, 3], [36431, 86655], .contexts [
        ⟨100136, true, false, [36432], [3]⟩,
        ⟨20, false, false, [36432, 86655], []⟩,
        ⟨100134, false, true, [], [86655]⟩
      ]⟩,
    ⟨[96763], [96761, 13], .source 48446⟩,
    ⟨[96761, 13], [96763], .contexts [
        ⟨100138, true, false, [], []⟩
      ]⟩,
    ⟨[96763], [96763], .contexts []⟩,
    ⟨[96763], [96763], .contexts []⟩,
    ⟨[96761, 13], [96763], .contexts [
        ⟨100139, false, false, [], []⟩,
        ⟨100140, false, false, [], []⟩,
        ⟨100141, false, false, [], []⟩,
        ⟨100141, false, false, [], []⟩
      ]⟩,
    ⟨[36427, 85887], [36427, 85887], .contexts []⟩,
    ⟨[36427, 85887], [36427, 85887], .contexts []⟩,
    ⟨[96763, 9], [96763, 9], .contexts []⟩,
    ⟨[96763, 9], [36427, 85887], .contexts [
        ⟨100145, false, false, [], []⟩,
        ⟨100142, true, false, [], [9]⟩,
        ⟨77, false, false, [96761], []⟩,
        ⟨78, false, false, [96761], []⟩,
        ⟨100130, false, false, [], [13]⟩,
        ⟨34135, false, false, [36427], []⟩,
        ⟨100143, false, false, [], []⟩,
        ⟨100144, false, false, [], []⟩,
        ⟨69344, false, false, [36427], []⟩,
        ⟨100124, true, false, [], [85887]⟩
      ]⟩,
    ⟨[96763, 11], [96763, 11], .contexts []⟩,
    ⟨[96763, 11], [23609, 83887], .contexts [
        ⟨100147, false, false, [], []⟩,
        ⟨100142, true, false, [], [11]⟩,
        ⟨82, false, false, [96761], []⟩,
        ⟨83, false, false, [96761], []⟩,
        ⟨100127, false, false, [], [13]⟩,
        ⟨100128, false, false, [], [13]⟩,
        ⟨53952, false, false, [], [13]⟩,
        ⟨53900, false, false, [], [13]⟩,
        ⟨53900, false, false, [], [13]⟩,
        ⟨99996, false, false, [], []⟩,
        ⟨54191, false, false, [], []⟩,
        ⟨54192, false, false, [], []⟩,
        ⟨54192, false, false, [], []⟩,
        ⟨89856, false, false, [23609], []⟩,
        ⟨13, true, false, [], [23609, 83887]⟩
      ]⟩,
    ⟨[83887, 11], [23607, 96763], .contexts [
        ⟨100148, true, false, [23608], [11]⟩,
        ⟨53, false, false, [23608, 96763], []⟩,
        ⟨54187, true, false, [], [96763]⟩
      ]⟩,
    ⟨[96765], [96763, 15], .source 48447⟩,
    ⟨[96763, 15], [96765], .contexts [
        ⟨100150, true, false, [], []⟩
      ]⟩,
    ⟨[96765], [96765], .contexts []⟩,
    ⟨[96765], [96765], .contexts []⟩,
    ⟨[96763, 15], [96765], .contexts [
        ⟨100151, false, false, [], []⟩,
        ⟨100152, false, false, [], []⟩,
        ⟨100153, false, false, [], []⟩,
        ⟨100153, false, false, [], []⟩
      ]⟩,
    ⟨[36427, 85889], [36427, 85889], .contexts []⟩,
    ⟨[36427, 85889], [36427, 85889], .contexts []⟩,
    ⟨[96765, 9], [96765, 9], .contexts []⟩,
    ⟨[85889], [85889], .contexts []⟩,
    ⟨[96765, 9], [36427, 85889], .contexts [
        ⟨100157, false, false, [], []⟩,
        ⟨100154, true, false, [], [9]⟩,
        ⟨45, false, false, [96763], []⟩,
        ⟨48, false, false, [96763], []⟩,
        ⟨100145, false, false, [], [15]⟩,
        ⟨100146, false, false, [], [15]⟩,
        ⟨100143, false, false, [], [15]⟩,
        ⟨100144, false, false, [], [15]⟩,
        ⟨100144, false, false, [], [15]⟩,
        ⟨34139, false, false, [36427], []⟩,
        ⟨100155, false, false, [], []⟩,
        ⟨100156, false, false, [], []⟩,
        ⟨100158, false, false, [36427], []⟩,
        ⟨100124, true, false, [], [85889]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1565. -/
def y322TCIndexRaw1565 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85889, 9], [36429, 96765], .contexts [
        ⟨100159, true, false, [36426], [9]⟩,
        ⟨46, false, false, [36426, 96765], []⟩,
        ⟨100126, true, false, [], [96765]⟩
      ]⟩,
    ⟨[36435], [23609, 30805], .source 18282⟩,
    ⟨[96765, 11], [96765, 11], .contexts []⟩,
    ⟨[96765, 11], [36435, 93915], .contexts [
        ⟨100162, false, false, [], []⟩,
        ⟨100154, true, false, [], [11]⟩,
        ⟨52, false, false, [96763], []⟩,
        ⟨55, false, false, [96763], []⟩,
        ⟨100147, false, false, [], [15]⟩,
        ⟨100148, false, false, [], [15]⟩,
        ⟨54191, false, false, [], [15]⟩,
        ⟨54192, false, false, [], [15]⟩,
        ⟨54192, false, false, [], [15]⟩,
        ⟨81955, false, false, [23609], []⟩,
        ⟨100161, true, false, [], [93915]⟩,
        ⟨81954, false, false, [36435], []⟩,
        ⟨13, true, false, [], [36435, 93915]⟩
      ]⟩,
    ⟨[36437], [36434], .source 18283⟩,
    ⟨[93915, 11], [36437, 96765], .contexts [
        ⟨100163, true, false, [36434], [11]⟩,
        ⟨53, false, false, [36434, 96765], []⟩,
        ⟨100164, true, false, [], [96765]⟩
      ]⟩,
    ⟨[96765, 9], [36427, 85889], .contexts [
        ⟨100157, false, false, [], []⟩,
        ⟨100159, false, false, [], []⟩,
        ⟨100155, false, false, [], []⟩,
        ⟨100156, false, false, [], []⟩,
        ⟨100156, false, false, [], []⟩
      ]⟩,
    ⟨[91953], [27151, 85897], .contexts [
        ⟨69412, false, false, [], []⟩
      ]⟩,
    ⟨[91953], [27151, 85897], .contexts [
        ⟨100167, false, false, [], []⟩,
        ⟨69411, false, false, [], []⟩
      ]⟩,
    ⟨[36439], [27143, 27151], .source 18284⟩,
    ⟨[36441], [36427, 36439], .source 18285⟩,
    ⟨[36441, 85899], [36441, 85899], .contexts []⟩,
    ⟨[36441, 85899], [36441, 85899], .contexts []⟩,
    ⟨[96765], [96765], .contexts []⟩,
    ⟨[36443], [36440], .source 18286⟩,
    ⟨[36440], [36440], .contexts []⟩,
    ⟨[85899, 5], [36443, 96765], .contexts [
        ⟨100172, true, false, [36440], [5]⟩,
        ⟨100171, true, false, [36440], [5]⟩,
        ⟨34158, true, false, [], [5]⟩,
        ⟨100170, false, false, [36440], [85897, 9, 5]⟩,
        ⟨100169, false, false, [36440, 36427], [85897, 9, 5]⟩,
        ⟨100168, true, false, [36440, 36427, 27143], [9, 5]⟩,
        ⟨69392, true, false, [36440, 36427], [9, 5]⟩,
        ⟨100166, true, false, [36440], [5, 9, 5]⟩,
        ⟨497, false, false, [36440, 96765], []⟩,
        ⟨100173, false, false, [36440], []⟩,
        ⟨100175, true, false, [], [96765]⟩,
        ⟨100175, true, false, [], [96765]⟩,
        ⟨100174, true, false, [], [96765]⟩
      ]⟩,
    ⟨[96765, 5], [36441, 85899], .contexts [
        ⟨100176, true, false, [36442], [5]⟩,
        ⟨28, false, false, [36442, 85899], []⟩,
        ⟨100174, false, true, [], [85899]⟩
      ]⟩,
    ⟨[36435, 93915], [36435, 93915], .contexts []⟩,
    ⟨[93915, 5], [93915, 5], .contexts []⟩,
    ⟨[85901], [85901], .contexts []⟩,
    ⟨[36445], [36437, 36441], .source 18287⟩,
    ⟨[93915, 5], [36445, 85901], .contexts [
        ⟨100179, false, false, [], []⟩,
        ⟨100178, true, false, [36434], [5]⟩,
        ⟨100178, true, false, [36434], [5]⟩,
        ⟨100163, true, false, [36434], [5]⟩,
        ⟨100162, true, false, [36434], [5]⟩,
        ⟨642, false, false, [36434, 96765], []⟩,
        ⟨643, false, false, [36434, 96765], []⟩,
        ⟨100177, false, false, [36434], [11]⟩,
        ⟨100171, false, false, [36434], [11]⟩,
        ⟨100172, false, false, [36434], [11]⟩,
        ⟨100172, false, false, [36434], [11]⟩,
        ⟨34162, false, false, [36434, 36441], []⟩,
        ⟨100180, false, false, [36434, 36441], []⟩,
        ⟨100164, true, false, [], [36441, 85901]⟩,
        ⟨100181, true, false, [], [85901]⟩
      ]⟩,
    ⟨[36447], [36444], .source 18288⟩,
    ⟨[85901, 5], [36447, 93915], .contexts [
        ⟨100182, true, false, [36444], [5]⟩,
        ⟨28, false, false, [36444, 93915], []⟩,
        ⟨100183, true, false, [], [93915]⟩
      ]⟩,
    ⟨[36445, 85901], [36445, 85901], .contexts []⟩,
    ⟨[36445, 85901], [36445, 85901], .contexts []⟩,
    ⟨[93915, 5], [36445, 85901], .contexts [
        ⟨100179, false, false, [], []⟩,
        ⟨100182, false, false, [], []⟩,
        ⟨100185, false, false, [], []⟩,
        ⟨100186, false, false, [], []⟩,
        ⟨100186, false, false, [], []⟩
      ]⟩,
    ⟨[36445, 85903], [36445, 85903], .contexts []⟩,
    ⟨[36445, 85903], [36445, 85903], .contexts []⟩,
    ⟨[85903, 5], [85903, 5], .contexts []⟩,
    ⟨[93913], [93913], .contexts []⟩,
    ⟨[36447], [36444], .contexts [
        ⟨100183, false, false, [], []⟩
      ]⟩,
    ⟨[36447], [36444], .contexts [
        ⟨100192, false, false, [], []⟩
      ]⟩,
    ⟨[36444], [36444], .contexts []⟩,
    ⟨[85903, 5], [36447, 93913], .contexts [
        ⟨100190, false, false, [], []⟩,
        ⟨100189, true, false, [36444], [5]⟩,
        ⟨100188, true, false, [36444], [5]⟩,
        ⟨34166, true, false, [], [5]⟩,
        ⟨100187, true, false, [36444], [1, 5]⟩,
        ⟨890, false, false, [36444, 93915], []⟩,
        ⟨9, false, false, [36444, 93915], []⟩,
        ⟨81770, false, false, [36444], []⟩,
        ⟨81771, false, false, [36444], []⟩,
        ⟨81745, false, false, [36444], []⟩,
        ⟨81745, false, false, [36444], []⟩,
        ⟨100191, false, false, [36444], []⟩,
        ⟨100194, true, false, [], [93913]⟩,
        ⟨100194, true, false, [], [93913]⟩,
        ⟨100193, true, false, [], [93913]⟩
      ]⟩,
    ⟨[93911], [36445, 85903], .contexts [
        ⟨82001, true, false, [], []⟩,
        ⟨100195, true, false, [36446], [5]⟩,
        ⟨28, false, false, [36446, 85903], []⟩,
        ⟨100183, false, true, [], [85903]⟩,
        ⟨100188, false, false, [], []⟩
      ]⟩,
    ⟨[85903, 3], [36447, 93909], .contexts [
        ⟨100196, true, false, [36444], [3]⟩,
        ⟨81739, false, false, [36444], []⟩,
        ⟨81774, false, false, [36444], []⟩,
        ⟨100194, true, false, [], [93909]⟩,
        ⟨100194, true, false, [], [93909]⟩,
        ⟨100192, true, false, [], [93909]⟩
      ]⟩,
    ⟨[36449], [36447, 30803], .source 18289⟩,
    ⟨[85903, 15], [36449, 83883], .contexts [
        ⟨100196, true, false, [36444], [15]⟩,
        ⟨82003, true, false, [36444, 30804], [15]⟩,
        ⟨1, false, false, [36444, 30804, 83883], []⟩,
        ⟨81894, true, false, [36444], [83883]⟩,
        ⟨82000, false, false, [36444], []⟩,
        ⟨100183, true, false, [], [30803, 83883]⟩,
        ⟨100198, true, false, [], [83883]⟩
      ]⟩,
    ⟨[36385, 94285], [36385, 94285], .contexts []⟩,
    ⟨[36451], [36385, 31187], .source 18290⟩,
    ⟨[85901, 7], [85901, 7], .contexts []⟩,
    ⟨[89275], [89275], .contexts []⟩,
    ⟨[85901, 7], [36444, 36451, 89275], .contexts [
        ⟨100202, false, false, [], []⟩,
        ⟨100187, true, false, [36444], [7]⟩,
        ⟨3272, false, false, [36444, 93915], []⟩,
        ⟨3275, false, false, [36444, 93915], []⟩,
        ⟨99988, false, false, [36444], [5, 7, 5]⟩,
        ⟨100200, false, false, [36444], [5, 7, 5]⟩,
        ⟨100200, false, false, [36444], [5, 7, 5]⟩,
        ⟨83434, false, false, [36444, 36385], [7, 5]⟩,
        ⟨83776, false, false, [36444, 36385], [5]⟩,
        ⟨100201, true, false, [36444], [89277, 5]⟩,
        ⟨55067, false, false, [36444, 36451], []⟩,
        ⟨100203, false, false, [36444, 36451], []⟩
      ]⟩,
    ⟨[36453], [36447, 36451], .source 18291⟩,
    ⟨[85901, 7], [36453, 89275], .contexts [
        ⟨100204, false, false, [], []⟩,
        ⟨100193, true, false, [], [36451, 89275]⟩,
        ⟨100205, true, false, [], [89275]⟩
      ]⟩,
    ⟨[36455], [36452], .source 18292⟩,
    ⟨[85903, 13], [85905], .contexts [
        ⟨34170, false, false, [], []⟩,
        ⟨34352, false, false, [], []⟩,
        ⟨34175, false, false, [], []⟩,
        ⟨34175, false, false, [], []⟩
      ]⟩,
    ⟨[30733, 93771], [30733, 93771], .contexts []⟩,
    ⟨[36449, 83883], [36449, 83883], .contexts []⟩,
    ⟨[36449, 83883], [36449, 83883], .contexts []⟩,
    ⟨[85903, 15], [36449, 83883], .contexts [
        ⟨100199, false, false, [], []⟩,
        ⟨100210, false, false, [], []⟩,
        ⟨100211, false, false, [], []⟩,
        ⟨100211, false, false, [], []⟩
      ]⟩,
    ⟨[36457], [36449, 36395], .source 18293⟩,
    ⟨[36459], [30735, 36457], .source 18294⟩,
    ⟨[36461], [36458], .source 18295⟩,
    ⟨[85193, 15], [36461, 93771], .contexts [
        ⟨100214, false, false, [36458], [85193, 15]⟩,
        ⟨81350, false, false, [36458], [36457, 85193, 15]⟩,
        ⟨100024, true, false, [36458, 30732, 36457], [15]⟩,
        ⟨100213, false, false, [36458, 30732], [85193, 15]⟩,
        ⟨100026, true, false, [36458, 30732, 36449], [15]⟩,
        ⟨100212, true, false, [36458, 30732], [13, 15]⟩,
        ⟨89, true, false, [36458, 30732, 85903], [15]⟩,
        ⟨2022, true, false, [36458, 30732, 85903], [15]⟩,
        ⟨100208, false, false, [36458, 30732], [15, 13, 15, 15]⟩,
        ⟨34174, false, false, [36458, 30732], [13, 15, 15]⟩,
        ⟨34350, false, false, [36458, 30732], [13, 15, 15]⟩,
        ⟨34179, false, false, [36458, 30732], [13, 15, 15]⟩,
        ⟨34179, false, false, [36458, 30732], [13, 15, 15]⟩,
        ⟨81436, false, false, [36458, 30732], [15, 15]⟩,
        ⟨100209, false, false, [36458, 30732], [15, 15]⟩,
        ⟨100209, false, false, [36458, 30732], [15, 15]⟩,
        ⟨1, false, false, [36458, 93771], []⟩,
        ⟨100215, true, false, [], [93771]⟩
      ]⟩,
    ⟨[85901, 7], [36453, 89275], .contexts [
        ⟨100202, false, false, [], []⟩,
        ⟨100206, false, false, [], []⟩
      ]⟩,
    ⟨[36453, 89275], [36453, 89275], .contexts []⟩,
    ⟨[36463], [36453, 33051], .source 18296⟩,
    ⟨[36465], [36463, 18323], .source 18297⟩,
    ⟨[85901], [85901], .contexts []⟩,
    ⟨[85629, 9], [85629, 9], .contexts []⟩,
    ⟨[36467], [36464], .source 18298⟩]

/-- Exact literal claimed equations and contextual derivations, block 1566. -/
def y322TCIndexRaw1566 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[36467], [36464], .contexts [
        ⟨100223, false, false, [], []⟩
      ]⟩,
    ⟨[36464], [36464], .contexts []⟩,
    ⟨[85629, 9], [36467, 85901], .contexts [
        ⟨100222, false, false, [], []⟩,
        ⟨100220, false, false, [36464], [85629, 9]⟩,
        ⟨40720, true, false, [36464, 36463], [9]⟩,
        ⟨100219, false, false, [36464], [87215, 7, 9]⟩,
        ⟨90185, true, false, [36464, 36453], [7, 9]⟩,
        ⟨100218, true, false, [36464], [9, 7, 9]⟩,
        ⟨100218, true, false, [36464], [9, 7, 9]⟩,
        ⟨100217, true, false, [36464], [9, 7, 9]⟩,
        ⟨50640, false, false, [36464, 85901], []⟩,
        ⟨100221, false, false, [36464], []⟩,
        ⟨100180, false, false, [36464], []⟩,
        ⟨100225, true, false, [], [85901]⟩,
        ⟨100225, true, false, [], [85901]⟩,
        ⟨100224, true, false, [], [85901]⟩
      ]⟩,
    ⟨[36465], [36466], .contexts [
        ⟨100223, true, true, [], []⟩
      ]⟩,
    ⟨[85901, 9], [36465, 85629], .contexts [
        ⟨100226, true, false, [36466], [9]⟩,
        ⟨46, false, false, [36466, 85629], []⟩,
        ⟨100227, true, false, [], [85629]⟩
      ]⟩,
    ⟨[36467, 85901], [36467, 85901], .contexts []⟩,
    ⟨[36467, 85901], [36467, 85901], .contexts []⟩,
    ⟨[85629, 9], [36467, 85901], .contexts [
        ⟨100222, false, false, [], []⟩,
        ⟨100226, false, false, [], []⟩,
        ⟨100229, false, false, [], []⟩,
        ⟨100230, false, false, [], []⟩,
        ⟨100230, false, false, [], []⟩
      ]⟩,
    ⟨[85627, 9], [22265, 86813], .contexts [
        ⟨48353, false, false, [], []⟩
      ]⟩,
    ⟨[22265, 86813], [22265, 24299, 85279], .contexts [
        ⟨57233, false, false, [22265], []⟩
      ]⟩,
    ⟨[36469], [22265, 24299], .source 18299⟩,
    ⟨[22265, 24299, 85279], [36469, 85279], .contexts [
        ⟨100234, true, false, [], [85279]⟩
      ]⟩,
    ⟨[36469, 85279], [36469, 85279], .contexts []⟩,
    ⟨[85903, 9], [85903, 9], .contexts []⟩,
    ⟨[36471], [36465, 36469], .source 18300⟩,
    ⟨[85903, 9], [36471, 85281], .contexts [
        ⟨100237, false, false, [], []⟩,
        ⟨34166, true, false, [], [9]⟩,
        ⟨100231, true, false, [36466], [1, 9]⟩,
        ⟨1964, false, false, [36466, 85629], []⟩,
        ⟨693, false, false, [36466, 85629], []⟩,
        ⟨33149, false, false, [36466], [9, 1]⟩,
        ⟨33150, false, false, [36466], [9, 1]⟩,
        ⟨32914, false, false, [36466], [9, 1]⟩,
        ⟨32914, false, false, [36466], [9, 1]⟩,
        ⟨100232, false, false, [36466], [1]⟩,
        ⟨100233, false, false, [36466], [1]⟩,
        ⟨100235, false, false, [36466], [1]⟩,
        ⟨100236, false, false, [36466], [1]⟩,
        ⟨31010, false, false, [36466, 36469], []⟩,
        ⟨67840, false, false, [36466, 36469], []⟩,
        ⟨100227, true, false, [], [36469, 85281]⟩,
        ⟨100238, true, false, [], [85281]⟩
      ]⟩,
    ⟨[36473], [36470], .source 18301⟩,
    ⟨[36475], [36467, 36447], .source 18302⟩,
    ⟨[36475, 93917], [36475, 93917], .contexts []⟩,
    ⟨[36475, 93917], [36475, 93917], .contexts []⟩,
    ⟨[36477], [36474], .source 18303⟩,
    ⟨[36477], [36474], .contexts [
        ⟨100244, false, false, [], []⟩
      ]⟩,
    ⟨[36474], [36474], .contexts []⟩,
    ⟨[93917, 5], [36477, 85629], .contexts [
        ⟨100243, true, false, [36474], [5]⟩,
        ⟨100242, true, false, [36474], [5]⟩,
        ⟨81748, true, false, [], [5]⟩,
        ⟨100241, false, false, [36474], [93915, 9, 5]⟩,
        ⟨100184, true, false, [36474, 36467], [9, 5]⟩,
        ⟨100231, true, false, [36474], [5, 9, 5]⟩,
        ⟨497, false, false, [36474, 85629], []⟩,
        ⟨40719, false, false, [36474], []⟩,
        ⟨100246, true, false, [], [85629]⟩,
        ⟨100246, true, false, [], [85629]⟩,
        ⟨100245, true, false, [], [85629]⟩
      ]⟩,
    ⟨[85629, 5], [36475, 93917], .contexts [
        ⟨100247, true, false, [36476], [5]⟩,
        ⟨28, false, false, [36476, 93917], []⟩,
        ⟨100244, false, true, [], [93917]⟩
      ]⟩,
    ⟨[85903, 9], [36471, 85281], .contexts [
        ⟨100237, false, false, [], []⟩,
        ⟨100239, false, false, [], []⟩
      ]⟩,
    ⟨[36471, 85281], [36471, 85281], .contexts []⟩,
    ⟨[85903, 9], [36471, 85281], .contexts [
        ⟨100249, false, false, [], []⟩,
        ⟨100250, false, false, [], []⟩,
        ⟨100250, false, false, [], []⟩
      ]⟩,
    ⟨[36479], [36471, 24297], .source 18304⟩,
    ⟨[85903, 3], [36447, 93909], .contexts [
        ⟨100197, false, false, [], []⟩
      ]⟩,
    ⟨[36447, 93909], [36447, 93909], .contexts []⟩,
    ⟨[86817, 9], [86817, 9], .contexts []⟩,
    ⟨[36481], [36478], .source 18305⟩,
    ⟨[36483], [36481, 36447], .source 18306⟩,
    ⟨[36483], [36478, 36447], .contexts [
        ⟨100257, false, false, [], []⟩,
        ⟨100256, false, false, [], [36447]⟩
      ]⟩,
    ⟨[86817, 9], [36483, 93909], .contexts [
        ⟨100255, false, false, [], []⟩,
        ⟨100252, false, false, [36478], [86817, 9]⟩,
        ⟨57243, true, false, [36478, 36471], [9]⟩,
        ⟨100251, true, false, [36478], [3, 9]⟩,
        ⟨479, false, false, [36478, 85903], []⟩,
        ⟨21, false, false, [36478, 85903], []⟩,
        ⟨100253, false, false, [36478], []⟩,
        ⟨100254, false, false, [36478], []⟩,
        ⟨100254, false, false, [36478], []⟩,
        ⟨82019, false, false, [36478, 36447], []⟩,
        ⟨100258, true, false, [], [93909]⟩
      ]⟩,
    ⟨[36485], [36482], .source 18307⟩,
    ⟨[36447, 93913], [36447, 93913], .contexts []⟩,
    ⟨[85283, 9], [85283, 9], .contexts []⟩,
    ⟨[36470], [36470], .contexts []⟩,
    ⟨[85283, 9], [36473, 85905], .contexts [
        ⟨100262, false, false, [], []⟩,
        ⟨31014, true, false, [], [9]⟩,
        ⟨100251, true, false, [36470], [13, 9]⟩,
        ⟨511, false, false, [36470, 85903], []⟩,
        ⟨64, false, false, [36470, 85903], []⟩,
        ⟨100208, false, false, [36470], []⟩,
        ⟨100263, true, false, [], [85905]⟩,
        ⟨100263, true, false, [], [85905]⟩,
        ⟨100240, true, false, [], [85905]⟩
      ]⟩,
    ⟨[36471], [36472], .contexts [
        ⟨100240, true, true, [], []⟩
      ]⟩,
    ⟨[86817, 9], [36483, 93909], .contexts [
        ⟨100255, false, false, [], []⟩,
        ⟨100259, false, false, [], []⟩
      ]⟩,
    ⟨[36483, 93909], [36483, 93909], .contexts []⟩,
    ⟨[86817, 9], [36483, 93909], .contexts [
        ⟨100266, false, false, [], []⟩,
        ⟨100267, false, false, [], []⟩,
        ⟨100267, false, false, [], []⟩
      ]⟩,
    ⟨[36487], [36483, 30803], .source 18308⟩,
    ⟨[36489], [17279, 36483], .source 18309⟩,
    ⟨[36491], [36489, 30803], .source 18310⟩,
    ⟨[83877, 9], [83877, 9], .contexts []⟩,
    ⟨[83877], [83877], .contexts []⟩,
    ⟨[36493], [36486], .source 18311⟩,
    ⟨[36495], [36493, 36491], .source 18312⟩,
    ⟨[83877, 9], [36495, 83877], .contexts [
        ⟨100272, false, false, [], []⟩,
        ⟨100269, false, false, [36486], [83877, 9]⟩,
        ⟨82021, true, false, [36486, 36483], [9]⟩,
        ⟨81736, true, false, [36486, 36483], [9]⟩,
        ⟨100268, true, false, [36486], [1, 9]⟩,
        ⟨1964, false, false, [36486, 86817], []⟩,
        ⟨693, false, false, [36486, 86817], []⟩,
        ⟨39216, false, false, [36486], [9, 1]⟩,
        ⟨100259, false, false, [36486, 17279], [1]⟩,
        ⟨100270, true, false, [36486], [93909, 1]⟩,
        ⟨81736, false, false, [36486, 36489], []⟩,
        ⟨82021, false, false, [36486, 36489], []⟩,
        ⟨100271, true, false, [36486], [83877]⟩,
        ⟨100273, false, false, [36486, 36491], []⟩,
        ⟨100274, true, false, [], [36491, 83877]⟩,
        ⟨100275, true, false, [], [83877]⟩
      ]⟩,
    ⟨[36482], [36482], .contexts []⟩,
    ⟨[93909, 5], [36485, 86821], .contexts [
        ⟨100268, true, false, [36482], [5]⟩,
        ⟨1079, false, false, [36482, 86817], []⟩,
        ⟨1080, false, false, [36482, 86817], []⟩,
        ⟨39215, false, false, [36482], [9]⟩,
        ⟨39223, false, false, [36482], []⟩,
        ⟨39473, false, false, [36482], []⟩,
        ⟨39227, false, false, [36482], []⟩,
        ⟨39227, false, false, [36482], []⟩,
        ⟨100277, true, false, [], [86821]⟩,
        ⟨100277, true, false, [], [86821]⟩,
        ⟨100260, true, false, [], [86821]⟩
      ]⟩,
    ⟨[86821, 5], [36483, 93909], .contexts [
        ⟨100278, true, false, [36484], [5]⟩,
        ⟨28, false, false, [36484, 93909], []⟩,
        ⟨100260, false, true, [], [93909]⟩
      ]⟩,
    ⟨[36473, 85905], [36473, 85905], .contexts []⟩,
    ⟨[36473, 85905], [36473, 85905], .contexts []⟩,
    ⟨[85283, 9], [36473, 85905], .contexts [
        ⟨100262, false, false, [], []⟩,
        ⟨100264, false, false, [], []⟩,
        ⟨100280, false, false, [], []⟩,
        ⟨100281, false, false, [], []⟩,
        ⟨100281, false, false, [], []⟩
      ]⟩,
    ⟨[33093, 86637], [33093, 86637], .contexts []⟩,
    ⟨[33093, 86637], [33093, 86637], .contexts []⟩,
    ⟨[85905, 7], [85905, 7], .contexts []⟩,
    ⟨[36471], [36472], .contexts [
        ⟨100265, false, false, [], []⟩
      ]⟩,
    ⟨[36497], [36471, 33093], .source 18313⟩]

/-- Exact literal claimed equations and contextual derivations, block 1567. -/
def y322TCIndexRaw1567 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85905, 7], [36497, 86639], .contexts [
        ⟨100285, false, false, [], []⟩,
        ⟨100282, true, false, [36472], [7]⟩,
        ⟨1084, false, false, [36472, 85283], []⟩,
        ⟨1085, false, false, [36472, 85283], []⟩,
        ⟨90200, false, false, [36472], [9]⟩,
        ⟨100283, false, false, [36472], [9]⟩,
        ⟨100284, false, false, [36472], [9]⟩,
        ⟨100284, false, false, [36472], [9]⟩,
        ⟨38276, false, false, [36472, 33093], []⟩,
        ⟨85167, false, false, [36472, 33093], []⟩,
        ⟨100286, true, false, [], [33093, 86639]⟩,
        ⟨100287, true, false, [], [86639]⟩
      ]⟩,
    ⟨[36499], [36496], .source 18314⟩,
    ⟨[85285], [23461, 84993], .contexts [
        ⟨53602, false, false, [], []⟩,
        ⟨53601, false, false, [], []⟩
      ]⟩,
    ⟨[85285], [23461, 84993], .contexts [
        ⟨100290, false, false, [], []⟩
      ]⟩,
    ⟨[85907, 9], [85907, 9], .contexts []⟩,
    ⟨[84993], [84993], .contexts []⟩,
    ⟨[36501], [36471, 23461], .source 18315⟩,
    ⟨[85907, 9], [36501, 84993], .contexts [
        ⟨100292, false, false, [], []⟩,
        ⟨34174, true, false, [], [9]⟩,
        ⟨100282, true, false, [36472], [15, 9]⟩,
        ⟨935, false, false, [36472, 85283], []⟩,
        ⟨10, false, false, [36472, 85283], []⟩,
        ⟨31018, false, false, [36472], []⟩,
        ⟨100291, false, false, [36472], []⟩,
        ⟨53601, false, false, [36472], []⟩,
        ⟨53601, false, false, [36472], []⟩,
        ⟨100293, false, false, [36472, 23461], []⟩,
        ⟨100286, true, false, [], [23461, 84993]⟩,
        ⟨100294, true, false, [], [84993]⟩
      ]⟩,
    ⟨[36503], [36500], .source 18316⟩,
    ⟨[84993, 9], [36503, 85907], .contexts [
        ⟨100295, true, false, [36500], [9]⟩,
        ⟨46, false, false, [36500, 85907], []⟩,
        ⟨100296, true, false, [], [85907]⟩
      ]⟩,
    ⟨[36495, 83877], [36495, 83877], .contexts []⟩,
    ⟨[36495, 83877], [36495, 83877], .contexts []⟩,
    ⟨[83877, 9], [36495, 83877], .contexts [
        ⟨100272, false, false, [], []⟩,
        ⟨100276, false, false, [], []⟩,
        ⟨100298, false, false, [], []⟩,
        ⟨100299, false, false, [], []⟩,
        ⟨100299, false, false, [], []⟩
      ]⟩,
    ⟨[83877, 13], [83875], .contexts [
        ⟨23429, false, false, [], []⟩,
        ⟨23430, false, false, [], []⟩,
        ⟨23310, false, false, [], []⟩,
        ⟨23310, false, false, [], []⟩
      ]⟩,
    ⟨[83875, 9], [83875, 9], .contexts []⟩,
    ⟨[83875], [83875], .contexts []⟩,
    ⟨[36505], [36494], .source 18317⟩,
    ⟨[36494], [36494], .contexts []⟩,
    ⟨[36505], [36494], .contexts [
        ⟨100304, false, false, [], []⟩,
        ⟨100305, false, false, [], []⟩,
        ⟨100305, false, false, [], []⟩
      ]⟩,
    ⟨[83875, 9], [36505, 83875], .contexts [
        ⟨100302, false, false, [], []⟩,
        ⟨23311, true, false, [], [9]⟩,
        ⟨100300, true, false, [36494], [13, 9]⟩,
        ⟨511, false, false, [36494, 83877], []⟩,
        ⟨64, false, false, [36494, 83877], []⟩,
        ⟨100301, false, false, [36494], []⟩,
        ⟨100303, false, false, [36494], []⟩,
        ⟨100306, true, false, [], [83875]⟩
      ]⟩,
    ⟨[83877, 15], [83879], .contexts [
        ⟨23313, false, false, [], []⟩,
        ⟨23427, false, false, [], []⟩,
        ⟨23318, false, false, [], []⟩,
        ⟨23318, false, false, [], []⟩
      ]⟩,
    ⟨[83879, 9], [83879, 9], .contexts []⟩,
    ⟨[83879], [83879], .contexts []⟩,
    ⟨[83879, 9], [36505, 83879], .contexts [
        ⟨100309, false, false, [], []⟩,
        ⟨23313, true, false, [], [9]⟩,
        ⟨100300, true, false, [36494], [15, 9]⟩,
        ⟨935, false, false, [36494, 83877], []⟩,
        ⟨10, false, false, [36494, 83877], []⟩,
        ⟨100308, false, false, [36494], []⟩,
        ⟨100310, false, false, [36494], []⟩,
        ⟨100306, true, false, [], [83879]⟩
      ]⟩,
    ⟨[36497, 86639], [36497, 86639], .contexts []⟩,
    ⟨[36507], [36497, 26899], .source 18318⟩,
    ⟨[90833, 7], [90833, 7], .contexts []⟩,
    ⟨[36509], [36506], .source 18319⟩,
    ⟨[36511], [36509, 30733], .source 18320⟩,
    ⟨[90833, 7], [36511, 93777], .contexts [
        ⟨100314, false, false, [], []⟩,
        ⟨100313, false, false, [36506], [90833, 7]⟩,
        ⟨68684, true, false, [36506, 36497], [7]⟩,
        ⟨100312, true, false, [36506], [1, 7]⟩,
        ⟨100312, true, false, [36506], [1, 7]⟩,
        ⟨100288, true, false, [36506], [1, 7]⟩,
        ⟨100285, true, false, [36506], [1, 7]⟩,
        ⟨502, false, false, [36506, 85905], []⟩,
        ⟨9, false, false, [36506, 85905], []⟩,
        ⟨81439, true, false, [36506, 30734], [1]⟩,
        ⟨80899, false, false, [36506, 30734], []⟩,
        ⟨80981, false, false, [36506, 30734], []⟩,
        ⟨81435, true, false, [36506], [93777]⟩,
        ⟨81427, false, false, [36506], []⟩,
        ⟨81428, false, false, [36506], []⟩,
        ⟨81428, false, false, [36506], []⟩,
        ⟨81421, false, false, [36506, 30733], []⟩,
        ⟨100315, true, false, [], [30733, 93777]⟩,
        ⟨100316, true, false, [], [93777]⟩
      ]⟩,
    ⟨[36513], [36510], .source 18321⟩,
    ⟨[36501, 84993], [36501, 84993], .contexts []⟩,
    ⟨[36501, 84993], [36501, 84993], .contexts []⟩,
    ⟨[36515], [36501, 33109], .source 18322⟩,
    ⟨[36515, 92291, 9], [85909], .contexts [
        ⟨71326, true, false, [36515], [9]⟩,
        ⟨100321, false, false, [], [92289, 1, 9]⟩,
        ⟨90325, true, false, [36501], [1, 9]⟩,
        ⟨29679, true, false, [36501], [9, 1, 9]⟩,
        ⟨100320, true, false, [], [1, 9, 1, 9]⟩,
        ⟨100320, true, false, [], [1, 9, 1, 9]⟩,
        ⟨100319, true, false, [], [1, 9, 1, 9]⟩,
        ⟨100295, true, false, [], [1, 9, 1, 9]⟩,
        ⟨100292, true, false, [], [1, 9, 1, 9]⟩,
        ⟨495, false, false, [85907], []⟩,
        ⟨9, false, false, [85907], []⟩,
        ⟨34178, false, false, [], []⟩,
        ⟨34348, false, false, [], []⟩,
        ⟨34183, false, false, [], []⟩,
        ⟨34183, false, false, [], []⟩
      ]⟩,
    ⟨[92291, 9], [92291, 9], .contexts []⟩,
    ⟨[36517], [36514], .source 18323⟩,
    ⟨[36517], [36514], .contexts [
        ⟨100324, false, false, [], []⟩
      ]⟩,
    ⟨[36514], [36514], .contexts []⟩,
    ⟨[36517], [36514], .contexts [
        ⟨100325, false, false, [], []⟩,
        ⟨100326, false, false, [], []⟩,
        ⟨100326, false, false, [], []⟩
      ]⟩,
    ⟨[92291, 9], [36517, 85909], .contexts [
        ⟨100323, false, false, [], []⟩,
        ⟨100322, false, false, [36514], []⟩,
        ⟨81431, false, false, [36514], []⟩,
        ⟨100327, true, false, [], [85909]⟩
      ]⟩,
    ⟨[36515], [36516], .contexts [
        ⟨100324, true, true, [], []⟩
      ]⟩,
    ⟨[85909, 9], [36515, 92291], .contexts [
        ⟨100328, true, false, [36516], [9]⟩,
        ⟨46, false, false, [36516, 92291], []⟩,
        ⟨100329, true, false, [], [92291]⟩
      ]⟩,
    ⟨[36505, 83879], [36505, 83879], .contexts []⟩,
    ⟨[36505, 83879], [36505, 83879], .contexts []⟩,
    ⟨[36519], [36505, 30805], .source 18324⟩,
    ⟨[30805, 93903], [30805, 93903], .contexts []⟩,
    ⟨[30805, 93903], [30805, 93903], .contexts []⟩,
    ⟨[93903], [93903], .contexts []⟩,
    ⟨[36521], [36518], .source 18325⟩,
    ⟨[36523], [36521, 30805], .source 18326⟩,
    ⟨[93903, 9], [36523, 93903], .contexts [
        ⟨100333, false, false, [36518], [93903, 9]⟩,
        ⟨82023, true, false, [36518, 36505], [9]⟩,
        ⟨100332, true, false, [36518], [13, 9]⟩,
        ⟨100332, true, false, [36518], [13, 9]⟩,
        ⟨100331, true, false, [36518], [13, 9]⟩,
        ⟨100311, true, false, [36518], [13, 9]⟩,
        ⟨100309, true, false, [36518], [13, 9]⟩,
        ⟨511, false, false, [36518, 83879], []⟩,
        ⟨64, false, false, [36518, 83879], []⟩,
        ⟨82023, false, false, [36518], []⟩,
        ⟨100334, false, false, [36518], []⟩,
        ⟨100335, false, false, [36518], []⟩,
        ⟨100335, false, false, [36518], []⟩,
        ⟨100336, false, false, [36518, 30805], []⟩,
        ⟨100337, true, false, [], [30805, 93903]⟩,
        ⟨100338, true, false, [], [93903]⟩
      ]⟩,
    ⟨[90833, 7], [36511, 93777], .contexts [
        ⟨100317, false, false, [], []⟩
      ]⟩,
    ⟨[36511, 93777], [36511, 93777], .contexts []⟩,
    ⟨[36511, 93777], [36511, 93777], .contexts []⟩,
    ⟨[90833, 7], [36511, 93777], .contexts [
        ⟨100314, false, false, [], []⟩,
        ⟨100340, false, false, [], []⟩,
        ⟨100341, false, false, [], []⟩,
        ⟨100342, false, false, [], []⟩,
        ⟨100342, false, false, [], []⟩
      ]⟩,
    ⟨[93779, 7], [93779, 7], .contexts []⟩,
    ⟨[36525], [36513, 31547], .source 18327⟩,
    ⟨[93779, 7], [36525, 94529], .contexts [
        ⟨100344, false, false, [], []⟩,
        ⟨80903, true, false, [], [7]⟩,
        ⟨100343, true, false, [36510], [3, 7]⟩,
        ⟨14911, false, false, [36510, 90833], []⟩,
        ⟨21, false, false, [36510, 90833], []⟩,
        ⟨85187, false, false, [36510], []⟩,
        ⟨85205, false, false, [36510, 31547], []⟩,
        ⟨100318, true, false, [], [31547, 94529]⟩,
        ⟨100345, true, false, [], [94529]⟩
      ]⟩,
    ⟨[36527], [36524], .source 18328⟩,
    ⟨[36529], [36511, 30735], .source 18329⟩,
    ⟨[85909, 7], [85909, 7], .contexts []⟩,
    ⟨[36531], [36528], .source 18330⟩,
    ⟨[36533], [36531, 31553], .source 18331⟩]

/-- Exact literal claimed equations and contextual derivations, block 1568. -/
def y322TCIndexRaw1568 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85909, 7], [36533, 83445], .contexts [
        ⟨100349, false, false, [], []⟩,
        ⟨100348, false, false, [36528], [85909, 7]⟩,
        ⟨81306, false, false, [36528, 36511], [85909, 7]⟩,
        ⟨1, true, false, [36528, 36511, 30732, 85909], [7]⟩,
        ⟨81422, false, false, [36528, 36511, 30732], [15, 7]⟩,
        ⟨100343, true, false, [36528], [15, 7]⟩,
        ⟨18155, false, false, [36528, 90833], []⟩,
        ⟨10, false, false, [36528, 90833], []⟩,
        ⟨85190, false, false, [36528], []⟩,
        ⟨100350, true, false, [], [31553, 83445]⟩,
        ⟨100351, true, false, [], [83445]⟩
      ]⟩,
    ⟨[36535], [36532], .source 18332⟩,
    ⟨[83445, 7], [36535, 85909], .contexts [
        ⟨100352, true, false, [36532], [7]⟩,
        ⟨38, false, false, [36532, 85909], []⟩,
        ⟨100353, true, false, [], [85909]⟩
      ]⟩,
    ⟨[36517, 85909], [36517, 85909], .contexts []⟩,
    ⟨[36517, 85909], [36517, 85909], .contexts []⟩,
    ⟨[85911, 9], [85911, 9], .contexts []⟩,
    ⟨[36515], [36515], .contexts []⟩,
    ⟨[36515], [36516], .contexts [
        ⟨100329, false, false, [], []⟩
      ]⟩,
    ⟨[36516], [36516], .contexts []⟩,
    ⟨[36515], [36516], .contexts [
        ⟨100358, false, false, [], []⟩,
        ⟨100359, false, false, [], []⟩,
        ⟨100360, false, false, [], []⟩,
        ⟨100360, false, false, [], []⟩
      ]⟩,
    ⟨[85911, 9], [36515, 92293], .contexts [
        ⟨100357, false, false, [], []⟩,
        ⟨34182, true, false, [], [9]⟩,
        ⟨100356, true, false, [36516], [3, 9]⟩,
        ⟨100356, true, false, [36516], [3, 9]⟩,
        ⟨100355, true, false, [36516], [3, 9]⟩,
        ⟨100328, true, false, [36516], [3, 9]⟩,
        ⟨100323, true, false, [36516], [3, 9]⟩,
        ⟨479, false, false, [36516, 92291], []⟩,
        ⟨90367, false, false, [36516], []⟩,
        ⟨90366, false, false, [36516], []⟩,
        ⟨90369, false, false, [36516], []⟩,
        ⟨100361, true, false, [], [92293]⟩
      ]⟩,
    ⟨[36525, 94529], [36525, 94529], .contexts []⟩,
    ⟨[36525, 94529], [36525, 94529], .contexts []⟩,
    ⟨[93779, 7], [36525, 94529], .contexts [
        ⟨100344, false, false, [], []⟩,
        ⟨100346, false, false, [], []⟩,
        ⟨100363, false, false, [], []⟩,
        ⟨100364, false, false, [], []⟩,
        ⟨100364, false, false, [], []⟩
      ]⟩,
    ⟨[36537], [36525, 31555], .source 18333⟩,
    ⟨[83439, 7], [83439, 7], .contexts []⟩,
    ⟨[36539], [36536], .source 18334⟩,
    ⟨[36539], [36536], .contexts [
        ⟨100368, false, false, [], []⟩
      ]⟩,
    ⟨[36541], [36539, 30721], .source 18335⟩,
    ⟨[83439, 7], [36541, 83025], .contexts [
        ⟨100367, false, false, [], []⟩,
        ⟨100366, false, false, [36536], [83439, 7]⟩,
        ⟨85211, true, false, [36536, 36525], [7]⟩,
        ⟨84806, true, false, [36536, 36525], [7]⟩,
        ⟨100365, true, false, [36536], [1, 7]⟩,
        ⟨502, false, false, [36536, 93779], []⟩,
        ⟨9, false, false, [36536, 93779], []⟩,
        ⟨81400, false, false, [36536], []⟩,
        ⟨81396, false, false, [36536], []⟩,
        ⟨81397, false, false, [36536], []⟩,
        ⟨81397, false, false, [36536], []⟩,
        ⟨81368, false, false, [36536, 30721], []⟩,
        ⟨100369, true, false, [], [30721, 83025]⟩,
        ⟨100370, true, false, [], [83025]⟩
      ]⟩,
    ⟨[36543], [36540], .source 18336⟩,
    ⟨[83025, 7], [36543, 83439], .contexts [
        ⟨100371, true, false, [36540], [7]⟩,
        ⟨38, false, false, [36540, 83439], []⟩,
        ⟨100372, true, false, [], [83439]⟩
      ]⟩,
    ⟨[83443, 7], [83443, 7], .contexts []⟩,
    ⟨[36545], [36539, 30735], .source 18337⟩,
    ⟨[83443, 7], [36545, 85911], .contexts [
        ⟨100374, false, false, [], []⟩,
        ⟨100366, false, false, [36536], [83443, 7]⟩,
        ⟨85194, true, false, [36536, 36525], [7]⟩,
        ⟨100365, true, false, [36536], [15, 7]⟩,
        ⟨18155, false, false, [36536, 93779], []⟩,
        ⟨10, false, false, [36536, 93779], []⟩,
        ⟨81419, false, false, [36536], []⟩,
        ⟨81404, false, false, [36536, 30735], []⟩,
        ⟨100369, true, false, [], [30735, 85911]⟩,
        ⟨100375, true, false, [], [85911]⟩
      ]⟩,
    ⟨[36547], [36544], .source 18338⟩,
    ⟨[36515, 92293], [36515, 92293], .contexts []⟩,
    ⟨[36515, 92293], [36515, 92293], .contexts []⟩,
    ⟨[36515, 92295], [36515, 92295], .contexts []⟩,
    ⟨[36515, 92295], [36515, 92295], .contexts []⟩,
    ⟨[36515, 92295], [36515, 92295], .contexts []⟩,
    ⟨[92295, 9], [92295, 9], .contexts []⟩,
    ⟨[92295, 9], [36517, 85913], .contexts [
        ⟨100383, false, false, [], []⟩,
        ⟨100382, true, false, [36514], [9]⟩,
        ⟨100381, true, false, [36514], [9]⟩,
        ⟨100380, true, false, [36514], [9]⟩,
        ⟨71334, true, false, [], [9]⟩,
        ⟨100379, true, false, [36514], [5, 9]⟩,
        ⟨100379, true, false, [36514], [5, 9]⟩,
        ⟨100378, true, false, [36514], [5, 9]⟩,
        ⟨100362, true, false, [36514], [5, 9]⟩,
        ⟨100357, true, false, [36514], [5, 9]⟩,
        ⟨598, false, false, [36514, 85911], []⟩,
        ⟨29, false, false, [36514, 85911], []⟩,
        ⟨34186, false, false, [36514], []⟩,
        ⟨34344, false, false, [36514], []⟩,
        ⟨34191, false, false, [36514], []⟩,
        ⟨34191, false, false, [36514], []⟩,
        ⟨79901, false, false, [36514], []⟩,
        ⟨100327, true, false, [], [85913]⟩
      ]⟩,
    ⟨[85913, 9], [36515, 92295], .contexts [
        ⟨100384, true, false, [36516], [9]⟩,
        ⟨46, false, false, [36516, 92295], []⟩,
        ⟨100329, true, false, [], [92295]⟩
      ]⟩,
    ⟨[36517, 85913], [36517, 85913], .contexts []⟩,
    ⟨[36517, 85913], [36517, 85913], .contexts []⟩,
    ⟨[92295, 9], [36517, 85913], .contexts [
        ⟨100383, false, false, [], []⟩,
        ⟨100384, false, false, [], []⟩,
        ⟨100386, false, false, [], []⟩,
        ⟨100387, false, false, [], []⟩,
        ⟨100387, false, false, [], []⟩
      ]⟩,
    ⟨[36517, 85917], [36517, 85917], .contexts []⟩,
    ⟨[85917, 1], [85917, 1], .contexts []⟩,
    ⟨[92299], [92299], .contexts []⟩,
    ⟨[85917, 1], [36515, 92299], .contexts [
        ⟨100390, false, false, [], []⟩,
        ⟨100389, true, false, [36516], [1]⟩,
        ⟨34194, true, false, [], [1]⟩,
        ⟨34190, true, false, [], [9, 1]⟩,
        ⟨100388, true, false, [36516], [1, 9, 1]⟩,
        ⟨988, false, false, [36516, 92295], []⟩,
        ⟨692, false, false, [36516, 92295], []⟩,
        ⟨90382, false, false, [36516], [9]⟩,
        ⟨71342, false, false, [36516], []⟩,
        ⟨71555, false, false, [36516], []⟩,
        ⟨71347, false, false, [36516], []⟩,
        ⟨71347, false, false, [36516], []⟩,
        ⟨100391, false, false, [36516], []⟩,
        ⟨100361, true, false, [], [92299]⟩
      ]⟩,
    ⟨[92299, 1], [36517, 85917], .contexts [
        ⟨100392, true, false, [36514], [1]⟩,
        ⟨8, false, false, [36514, 85917], []⟩,
        ⟨100324, true, false, [], [85917]⟩
      ]⟩,
    ⟨[36515, 92299], [36515, 92299], .contexts []⟩,
    ⟨[36515, 92299], [36515, 92299], .contexts []⟩,
    ⟨[85917, 1], [36515, 92299], .contexts [
        ⟨100390, false, false, [], []⟩,
        ⟨100392, false, false, [], []⟩,
        ⟨100394, false, false, [], []⟩,
        ⟨100395, false, false, [], []⟩,
        ⟨100395, false, false, [], []⟩
      ]⟩,
    ⟨[30849, 86625], [30849, 86625], .contexts []⟩,
    ⟨[36549], [30849, 26869], .source 18339⟩,
    ⟨[92299, 3], [92299, 3], .contexts []⟩,
    ⟨[92299, 3], [36514, 36549, 96753], .contexts [
        ⟨100399, false, false, [], []⟩,
        ⟨100396, true, false, [36514], [3]⟩,
        ⟨1098, false, false, [36514, 85917], []⟩,
        ⟨1100, false, false, [36514, 85917], []⟩,
        ⟨81983, false, false, [36514], [1, 3, 1]⟩,
        ⟨100397, false, false, [36514], [1, 3, 1]⟩,
        ⟨100397, false, false, [36514], [1, 3, 1]⟩,
        ⟨38253, false, false, [36514, 30849], [3, 1]⟩,
        ⟨68484, false, false, [36514, 30849], [1]⟩,
        ⟨100398, true, false, [36514], [83013, 1]⟩,
        ⟨99833, false, false, [36514, 36549], []⟩,
        ⟨99846, false, false, [36514, 36549], []⟩
      ]⟩,
    ⟨[36551], [36517, 36549], .source 18340⟩,
    ⟨[92299, 3], [36551, 96753], .contexts [
        ⟨100400, false, false, [], []⟩,
        ⟨100325, true, false, [], [36549, 96753]⟩,
        ⟨100401, true, false, [], [96753]⟩
      ]⟩,
    ⟨[36553], [36550], .source 18341⟩,
    ⟨[96753, 3], [36553, 92299], .contexts [
        ⟨100402, true, false, [36550], [3]⟩,
        ⟨20, false, false, [36550, 92299], []⟩,
        ⟨100403, true, false, [], [92299]⟩
      ]⟩,
    ⟨[92299, 5], [92299, 5], .contexts []⟩,
    ⟨[92299, 5], [36517, 96641], .contexts [
        ⟨100405, false, false, [], []⟩,
        ⟨100396, true, false, [36514], [5]⟩,
        ⟨98, false, false, [36514, 85917], []⟩,
        ⟨99, false, false, [36514, 85917], []⟩,
        ⟨99060, false, false, [36514], [1]⟩,
        ⟨99070, false, false, [36514], []⟩,
        ⟨99071, false, false, [36514], []⟩,
        ⟨99072, false, false, [36514], []⟩,
        ⟨99072, false, false, [36514], []⟩,
        ⟨99085, false, false, [36514], []⟩,
        ⟨100327, true, false, [], [96641]⟩
      ]⟩,
    ⟨[36515, 92303], [36515, 92303], .contexts []⟩,
    ⟨[85919], [36515, 92303], .contexts [
        ⟨34203, true, false, [], []⟩,
        ⟨34203, true, false, [], []⟩,
        ⟨34339, true, false, [], []⟩,
        ⟨34198, true, false, [], []⟩,
        ⟨100327, false, false, [36516], [85917, 11]⟩,
        ⟨79838, true, false, [36516, 36514], [11]⟩,
        ⟨994, true, false, [36516, 36514, 85917], [11]⟩,
        ⟨100396, false, false, [36516, 36514], [11, 1, 11, 11]⟩,
        ⟨71346, false, false, [36516], [1, 11, 11]⟩,
        ⟨71350, false, false, [36516], [11, 11]⟩,
        ⟨100407, false, false, [36516, 36514], [11, 11]⟩,
        ⟨53, false, false, [36516, 92303], []⟩,
        ⟨100329, true, false, [], [92303]⟩
      ]⟩,
    ⟨[36515], [36515], .contexts []⟩,
    ⟨[36515], [36515], .contexts []⟩,
    ⟨[92303], [36517, 85919], .contexts [
        ⟨100358, false, false, [36514], [92303]⟩,
        ⟨100409, false, false, [36514], [92303]⟩,
        ⟨100410, false, false, [36514], [92303]⟩,
        ⟨100407, true, false, [36514], []⟩,
        ⟨100408, true, false, [36514], []⟩,
        ⟨100324, true, false, [], [85919]⟩
      ]⟩,
    ⟨[36515], [36516], .contexts [
        ⟨100359, false, false, [], []⟩,
        ⟨100360, false, false, [], []⟩,
        ⟨100360, false, false, [], []⟩
      ]⟩,
    ⟨[85919, 13], [36515, 92305], .contexts [
        ⟨100411, true, false, [36516], [13]⟩,
        ⟨71354, false, false, [36516], []⟩,
        ⟨71553, false, false, [36516], []⟩,
        ⟨100412, true, false, [], [92305]⟩
      ]⟩,
    ⟨[36517, 85921], [36517, 85921], .contexts []⟩,
    ⟨[92301], [36517, 85921], .contexts [
        ⟨100359, false, false, [36514], [92301]⟩,
        ⟨13, false, false, [36514, 36516], [92301]⟩,
        ⟨71554, true, false, [36514, 36516], []⟩,
        ⟨71352, true, false, [36514, 36516], []⟩,
        ⟨100411, false, false, [36514, 36516], [1]⟩,
        ⟨34202, false, false, [36514], []⟩,
        ⟨100414, false, false, [36514, 36516], []⟩,
        ⟨100324, true, false, [], [85921]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1569. -/
def y322TCIndexRaw1569 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85921, 11], [36515, 92299], .contexts [
        ⟨100415, true, false, [36516], [11]⟩,
        ⟨71348, false, false, [36516], []⟩,
        ⟨71555, false, false, [36516], []⟩,
        ⟨100412, true, false, [], [92299]⟩
      ]⟩,
    ⟨[36555], [36517, 36085], .source 18342⟩,
    ⟨[92299, 15], [36555, 83019], .contexts [
        ⟨100396, true, false, [36514], [15]⟩,
        ⟨121, false, false, [36514, 85917], []⟩,
        ⟨122, false, false, [36514, 85917], []⟩,
        ⟨81346, false, false, [36514], [1]⟩,
        ⟨81285, false, false, [36514, 30733], []⟩,
        ⟨99061, true, false, [36514], [83019]⟩,
        ⟨62849, false, false, [36514, 36085], []⟩,
        ⟨100325, true, false, [], [36085, 83019]⟩,
        ⟨100417, true, false, [], [83019]⟩
      ]⟩,
    ⟨[36557], [36554], .source 18343⟩,
    ⟨[83019, 15], [36557, 92299], .contexts [
        ⟨100418, true, false, [36554], [15]⟩,
        ⟨1, false, false, [36554, 92299], []⟩,
        ⟨100419, true, false, [], [92299]⟩
      ]⟩,
    ⟨[36551, 96753], [36551, 96753], .contexts []⟩,
    ⟨[36551, 96753], [36551, 96753], .contexts []⟩,
    ⟨[92299, 3], [36551, 96753], .contexts [
        ⟨100399, false, false, [], []⟩,
        ⟨100402, false, false, [], []⟩,
        ⟨100421, false, false, [], []⟩,
        ⟨100422, false, false, [], []⟩,
        ⟨100422, false, false, [], []⟩
      ]⟩,
    ⟨[36559], [36551, 25543], .source 18344⟩,
    ⟨[36559, 84629], [36559, 84629], .contexts []⟩,
    ⟨[92299], [92299], .contexts []⟩,
    ⟨[84629, 7], [84629, 7], .contexts []⟩,
    ⟨[36561], [36558], .source 18345⟩,
    ⟨[36558], [36558], .contexts []⟩,
    ⟨[84629, 7], [36561, 92299], .contexts [
        ⟨100427, false, false, [], []⟩,
        ⟨100425, true, false, [36558], [7]⟩,
        ⟨27982, true, false, [], [7]⟩,
        ⟨100424, false, false, [36558], [84627, 3, 7]⟩,
        ⟨99840, true, false, [36558, 36551], [3, 7]⟩,
        ⟨100423, true, false, [36558], [7, 3, 7]⟩,
        ⟨18135, false, false, [36558, 92299], []⟩,
        ⟨100426, false, false, [36558], []⟩,
        ⟨100391, false, false, [36558], []⟩,
        ⟨100429, true, false, [], [92299]⟩,
        ⟨100429, true, false, [], [92299]⟩,
        ⟨100428, true, false, [], [92299]⟩
      ]⟩,
    ⟨[92299, 7], [36559, 84629], .contexts [
        ⟨100430, true, false, [36560], [7]⟩,
        ⟨38, false, false, [36560, 84629], []⟩,
        ⟨100428, false, true, [], [84629]⟩
      ]⟩,
    ⟨[36563], [36551, 36315], .source 18346⟩,
    ⟨[36565], [36563, 36553], .source 18347⟩,
    ⟨[92299, 13], [92299, 13], .contexts []⟩,
    ⟨[36567], [36564], .source 18348⟩,
    ⟨[36564], [36564], .contexts []⟩,
    ⟨[92299, 13], [36567, 92299], .contexts [
        ⟨100434, false, false, [], []⟩,
        ⟨100433, false, false, [36564], [92299, 13]⟩,
        ⟨100404, true, false, [36564, 36563], [13]⟩,
        ⟨100432, false, false, [36564], [96753, 3, 13]⟩,
        ⟨99848, true, false, [36564, 36551], [3, 13]⟩,
        ⟨100423, true, false, [36564], [13, 3, 13]⟩,
        ⟨1930, false, false, [36564, 92299], []⟩,
        ⟨100426, false, false, [36564], []⟩,
        ⟨100391, false, false, [36564], []⟩,
        ⟨100436, true, false, [], [92299]⟩,
        ⟨100436, true, false, [], [92299]⟩,
        ⟨100435, true, false, [], [92299]⟩
      ]⟩,
    ⟨[36517, 96641], [36517, 96641], .contexts []⟩,
    ⟨[36517, 96643], [36517, 96643], .contexts []⟩,
    ⟨[92299, 9], [92297], .contexts [
        ⟨71556, false, false, [], []⟩,
        ⟨71557, false, false, [], []⟩,
        ⟨71343, false, false, [], []⟩,
        ⟨71343, false, false, [], []⟩
      ]⟩,
    ⟨[92299, 8], [92299, 9], .contexts [
        ⟨47, false, false, [92299], []⟩
      ]⟩,
    ⟨[96643, 5], [96643, 5], .contexts []⟩,
    ⟨[96643, 5], [36515, 92297], .contexts [
        ⟨100442, false, false, [], []⟩,
        ⟨100439, true, false, [36516], [5]⟩,
        ⟨99090, true, false, [], [5]⟩,
        ⟨100438, true, false, [36516], [9, 5]⟩,
        ⟨100438, true, false, [36516], [9, 5]⟩,
        ⟨100406, true, false, [36516], [9, 5]⟩,
        ⟨100405, true, false, [36516], [9, 5]⟩,
        ⟨960, false, false, [36516, 92299], []⟩,
        ⟨100441, false, false, [36516], []⟩,
        ⟨100440, false, false, [36516], []⟩,
        ⟨90383, false, false, [36516], []⟩,
        ⟨100361, true, false, [], [92297]⟩
      ]⟩,
    ⟨[92297, 5], [36517, 96643], .contexts [
        ⟨100443, true, false, [36514], [5]⟩,
        ⟨28, false, false, [36514, 96643], []⟩,
        ⟨100324, true, false, [], [96643]⟩
      ]⟩,
    ⟨[85923], [30301, 85921], .contexts [
        ⟨79812, false, false, [], []⟩
      ]⟩,
    ⟨[36569], [30301, 36515], .source 18349⟩,
    ⟨[36515, 92305], [36515, 92305], .contexts []⟩,
    ⟨[36515, 92305], [36515, 92305], .contexts []⟩,
    ⟨[85919, 13], [36515, 92305], .contexts [
        ⟨100413, false, false, [], []⟩,
        ⟨100447, false, false, [], []⟩,
        ⟨100448, false, false, [], []⟩,
        ⟨100448, false, false, [], []⟩
      ]⟩,
    ⟨[85919, 12], [85919, 13], .contexts [
        ⟨64, false, false, [85919], []⟩
      ]⟩,
    ⟨[36569, 92305, 1], [36515, 92305], .contexts [
        ⟨100446, false, false, [], [92305, 1]⟩,
        ⟨100413, true, false, [30301], [1]⟩,
        ⟨81300, true, false, [], [13, 1]⟩,
        ⟨81299, true, false, [], [13, 1]⟩,
        ⟨34204, true, false, [30301], [13, 1]⟩,
        ⟨79811, true, false, [], [1, 13, 1]⟩,
        ⟨79811, true, false, [], [1, 13, 1]⟩,
        ⟨100445, true, false, [], [1, 13, 1]⟩,
        ⟨34206, true, false, [], [1, 13, 1]⟩,
        ⟨34207, true, false, [], [13, 1, 13, 1]⟩,
        ⟨34207, true, false, [], [13, 1, 13, 1]⟩,
        ⟨34337, true, false, [], [13, 1, 13, 1]⟩,
        ⟨34202, true, false, [], [13, 1, 13, 1]⟩,
        ⟨70918, false, false, [85919], []⟩,
        ⟨100450, false, false, [], []⟩,
        ⟨100449, false, false, [], []⟩
      ]⟩,
    ⟨[92305, 1], [92305, 1], .contexts []⟩,
    ⟨[92305], [92305], .contexts []⟩,
    ⟨[36571], [36568], .source 18350⟩,
    ⟨[36573], [36571, 36515], .source 18351⟩,
    ⟨[92305, 1], [36573, 92305], .contexts [
        ⟨100452, false, false, [], []⟩,
        ⟨100451, false, false, [36568], []⟩,
        ⟨100453, false, false, [36568, 36515], []⟩,
        ⟨100454, true, false, [], [36515, 92305]⟩,
        ⟨100455, true, false, [], [92305]⟩
      ]⟩,
    ⟨[30319, 91603], [30319, 91603], .contexts []⟩,
    ⟨[30319, 91603], [30319, 91603], .contexts []⟩,
    ⟨[36575], [30319, 29301], .source 18352⟩,
    ⟨[91599, 7], [91599, 7], .contexts []⟩,
    ⟨[36577], [36574], .source 18353⟩,
    ⟨[36579], [36577, 36515], .source 18354⟩,
    ⟨[91599, 7], [36579, 92305], .contexts [
        ⟨100460, false, false, [], []⟩,
        ⟨100459, false, false, [36574], [91599, 7]⟩,
        ⟨76334, true, false, [36574, 30319], [7]⟩,
        ⟨66593, true, false, [36574, 30319], [7]⟩,
        ⟨100458, true, false, [36574], [13, 7]⟩,
        ⟨100458, true, false, [36574], [13, 7]⟩,
        ⟨100457, true, false, [36574], [13, 7]⟩,
        ⟨79835, true, false, [36574], [13, 7]⟩,
        ⟨79832, true, false, [36574], [13, 7]⟩,
        ⟨518, false, false, [36574, 85919], []⟩,
        ⟨100450, false, false, [36574], []⟩,
        ⟨100449, false, false, [36574], []⟩,
        ⟨100453, false, false, [36574, 36515], []⟩,
        ⟨100461, true, false, [], [36515, 92305]⟩,
        ⟨100462, true, false, [], [92305]⟩
      ]⟩,
    ⟨[36581], [36578], .source 18355⟩,
    ⟨[36583], [30303, 23927], .source 18356⟩,
    ⟨[36585], [36583, 29307], .source 18357⟩,
    ⟨[88681, 13], [88681, 13], .contexts []⟩,
    ⟨[36587], [36584], .source 18358⟩,
    ⟨[36589], [36587, 36515], .source 18359⟩,
    ⟨[88681, 13], [36589, 92307], .contexts [
        ⟨100467, false, false, [], []⟩,
        ⟨100466, false, false, [36584], [88681, 13]⟩,
        ⟨76351, true, false, [36584, 36583], [13]⟩,
        ⟨100465, false, false, [36584], [88689, 15, 13]⟩,
        ⟨55437, true, false, [36584, 30303], [15, 13]⟩,
        ⟨79876, true, false, [36584], [13, 15, 13]⟩,
        ⟨6196, false, false, [36584, 85919], []⟩,
        ⟨260, false, false, [36584, 85919], []⟩,
        ⟨100449, false, false, [36584], [15]⟩,
        ⟨71357, false, false, [36584, 36515], []⟩,
        ⟨100468, true, false, [], [36515, 92307]⟩,
        ⟨100469, true, false, [], [92307]⟩
      ]⟩,
    ⟨[36591], [36588], .source 18360⟩,
    ⟨[36593], [30329, 36515], .source 18361⟩,
    ⟨[86199, 9], [36593, 92305], .contexts [
        ⟨35657, true, false, [], [9]⟩,
        ⟨79880, true, false, [30326], [13, 9]⟩,
        ⟨79880, true, false, [30326], [13, 9]⟩,
        ⟨79879, true, false, [30326], [13, 9]⟩,
        ⟨79885, true, false, [30326], [13, 9]⟩,
        ⟨511, false, false, [30326, 85919], []⟩,
        ⟨100450, false, false, [30326], []⟩,
        ⟨100449, false, false, [30326], []⟩,
        ⟨100453, false, false, [30326, 36515], []⟩,
        ⟨79882, true, false, [], [36515, 92305]⟩,
        ⟨100472, true, false, [], [92305]⟩
      ]⟩,
    ⟨[36595], [36592], .source 18362⟩,
    ⟨[92305, 9], [36595, 86199], .contexts [
        ⟨100473, true, false, [36592], [9]⟩,
        ⟨46, false, false, [36592, 86199], []⟩,
        ⟨100474, true, false, [], [86199]⟩
      ]⟩,
    ⟨[30299, 93525], [30299, 93525], .contexts []⟩,
    ⟨[36597], [36515, 36559], .source 18363⟩,
    ⟨[93525, 11], [93525, 11], .contexts []⟩,
    ⟨[36599], [30297, 36597], .source 18364⟩]

/-- Exact literal claimed equations and contextual derivations, block 1570. -/
def y322TCIndexRaw1570 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[93525, 11], [36599, 84629], .contexts [
        ⟨100478, false, false, [], []⟩,
        ⟨100476, true, false, [30298], [11]⟩,
        ⟨100476, true, false, [30298], [11]⟩,
        ⟨79801, true, false, [30298], [11]⟩,
        ⟨79798, true, false, [30298], [11]⟩,
        ⟨1051, false, false, [30298, 85921], []⟩,
        ⟨1052, false, false, [30298, 85921], []⟩,
        ⟨100416, false, false, [30298], [7]⟩,
        ⟨100394, false, false, [30298], [7]⟩,
        ⟨100395, false, false, [30298], [7]⟩,
        ⟨100395, false, false, [30298], [7]⟩,
        ⟨100431, false, false, [30298, 36515], []⟩,
        ⟨100477, true, false, [30298], [84629]⟩,
        ⟨56730, false, false, [30298, 36597], []⟩,
        ⟨79802, true, false, [], [36597, 84629]⟩,
        ⟨100479, true, false, [], [84629]⟩
      ]⟩,
    ⟨[36601], [36598], .source 18365⟩,
    ⟨[36561, 92299], [36561, 92299], .contexts []⟩,
    ⟨[36603], [36561, 36517], .source 18366⟩,
    ⟨[36605], [36603, 30323], .source 18367⟩,
    ⟨[93521, 1], [93521, 1], .contexts []⟩,
    ⟨[36607], [36604], .source 18368⟩,
    ⟨[36604], [36604], .contexts []⟩,
    ⟨[36607], [36604], .contexts [
        ⟨100486, false, false, [], []⟩,
        ⟨100487, false, false, [], []⟩,
        ⟨100487, false, false, [], []⟩
      ]⟩,
    ⟨[93521, 1], [36607, 84629], .contexts [
        ⟨100485, false, false, [], []⟩,
        ⟨100484, false, false, [36604], [93521, 1]⟩,
        ⟨79843, true, false, [36604, 36603], [1]⟩,
        ⟨100483, false, false, [36604], [85917, 7, 1]⟩,
        ⟨100393, true, false, [36604, 36561], [7, 1]⟩,
        ⟨100482, true, false, [36604], [1, 7, 1]⟩,
        ⟨100482, true, false, [36604], [1, 7, 1]⟩,
        ⟨100430, true, false, [36604], [1, 7, 1]⟩,
        ⟨100427, true, false, [36604], [1, 7, 1]⟩,
        ⟨16489, false, false, [36604, 84629], []⟩,
        ⟨56730, false, false, [36604], []⟩,
        ⟨100488, true, false, [], [84629]⟩
      ]⟩,
    ⟨[36605], [36606], .contexts [
        ⟨100486, true, true, [], []⟩
      ]⟩,
    ⟨[36567, 92299], [36567, 92299], .contexts []⟩,
    ⟨[36566], [36566], .contexts []⟩,
    ⟨[36515, 92297], [36515, 92297], .contexts []⟩,
    ⟨[36515, 92297], [36515, 92297], .contexts []⟩,
    ⟨[96643, 5], [36515, 92297], .contexts [
        ⟨100442, false, false, [], []⟩,
        ⟨100443, false, false, [], []⟩,
        ⟨100493, false, false, [], []⟩,
        ⟨100494, false, false, [], []⟩,
        ⟨100494, false, false, [], []⟩
      ]⟩,
    ⟨[96643], [96643], .contexts []⟩,
    ⟨[92293, 1], [36517, 96643], .contexts [
        ⟨100379, true, false, [36514], [1]⟩,
        ⟨100378, true, false, [36514], [1]⟩,
        ⟨71336, true, false, [], [1]⟩,
        ⟨100382, true, false, [36514], [5, 1]⟩,
        ⟨100381, true, false, [36514], [5, 1]⟩,
        ⟨100380, true, false, [36514], [5, 1]⟩,
        ⟨71340, true, false, [], [5, 1]⟩,
        ⟨100495, true, false, [36514], [1, 5, 1]⟩,
        ⟨874, false, false, [36514, 96643], []⟩,
        ⟨100496, false, false, [36514], []⟩,
        ⟨99100, false, false, [36514], []⟩,
        ⟨100327, true, false, [], [96643]⟩
      ]⟩,
    ⟨[96643, 1], [36515, 92293], .contexts [
        ⟨100497, true, false, [36516], [1]⟩,
        ⟨8, false, false, [36516, 92293], []⟩,
        ⟨100329, true, false, [], [92293]⟩
      ]⟩,
    ⟨[36609], [36515, 33083], .source 18369⟩,
    ⟨[36611], [36609, 36517], .source 18370⟩,
    ⟨[36613], [36610], .source 18371⟩,
    ⟨[96645], [36613, 96643], .contexts [
        ⟨99104, true, false, [], []⟩,
        ⟨100500, false, false, [36610], [96643, 11]⟩,
        ⟨100444, true, false, [36610, 36609], [11]⟩,
        ⟨100499, false, false, [36610], [92297, 5, 11]⟩,
        ⟨90384, true, false, [36610, 36515], [5, 11]⟩,
        ⟨100495, true, false, [36610], [11, 5, 11]⟩,
        ⟨173, false, false, [36610, 96643], []⟩,
        ⟨99100, true, false, [36610], []⟩,
        ⟨100501, true, false, [], [96643]⟩
      ]⟩,
    ⟨[36615], [36613, 36515], .source 18372⟩,
    ⟨[36617], [36614], .source 18373⟩,
    ⟨[36617], [36614], .contexts [
        ⟨100504, false, false, [], []⟩
      ]⟩,
    ⟨[36615], [36616], .contexts [
        ⟨100504, true, true, [], []⟩
      ]⟩,
    ⟨[36614], [36614], .contexts []⟩,
    ⟨[92293, 13], [36617, 96649], .contexts [
        ⟨100506, false, false, [36614], [92293, 13]⟩,
        ⟨100503, false, false, [36614, 36616, 36614], [92293, 13]⟩,
        ⟨100498, true, false, [36614, 36616, 36614, 36613], [13]⟩,
        ⟨100502, true, false, [36614, 36616, 36614], [1, 13]⟩,
        ⟨99111, false, false, [36614, 36616, 36614], [13]⟩,
        ⟨13, true, false, [36614, 36616, 36614], [96647, 13]⟩,
        ⟨100505, true, false, [36614, 36616], [96647, 13]⟩,
        ⟨99114, false, false, [36614], []⟩,
        ⟨99115, false, false, [36614], []⟩,
        ⟨100507, true, false, [], [96649]⟩,
        ⟨100507, true, false, [], [96649]⟩,
        ⟨100505, true, false, [], [96649]⟩
      ]⟩,
    ⟨[36573, 92305], [36573, 92305], .contexts []⟩,
    ⟨[36573, 92309], [36573, 92309], .contexts []⟩,
    ⟨[36619], [36572], .source 18374⟩,
    ⟨[36619], [36619], .contexts []⟩,
    ⟨[36572], [36572], .contexts []⟩,
    ⟨[92309, 15], [36619, 92305], .contexts [
        ⟨100510, true, false, [36572], [15]⟩,
        ⟨71361, true, false, [], [15]⟩,
        ⟨71357, true, false, [], [1, 15]⟩,
        ⟨100509, true, false, [36572], [15, 1, 15]⟩,
        ⟨100509, true, false, [36572], [15, 1, 15]⟩,
        ⟨100456, true, false, [36572], [15, 1, 15]⟩,
        ⟨100452, true, false, [36572], [15, 1, 15]⟩,
        ⟨2185, false, false, [36572, 92305], []⟩,
        ⟨100453, false, false, [36572], []⟩,
        ⟨100513, true, false, [], [92305]⟩,
        ⟨100513, true, false, [], [92305]⟩,
        ⟨100511, true, false, [], [92305]⟩,
        ⟨100512, true, false, [], [92305]⟩
      ]⟩,
    ⟨[36573], [36618], .contexts [
        ⟨100511, true, true, [], []⟩
      ]⟩,
    ⟨[92309], [36619, 92307], .contexts [
        ⟨100510, true, false, [36572], []⟩,
        ⟨100515, false, false, [36572], [92309]⟩,
        ⟨1, true, false, [36572, 36618, 92309], []⟩,
        ⟨100514, false, false, [36572, 36618], [15]⟩,
        ⟨71357, false, false, [36572], []⟩,
        ⟨71551, false, false, [36572], []⟩,
        ⟨71362, false, false, [36572], []⟩,
        ⟨71362, false, false, [36572], []⟩,
        ⟨100511, true, false, [], [92307]⟩
      ]⟩,
    ⟨[36618], [36618], .contexts []⟩,
    ⟨[91599, 7], [36579, 92305], .contexts [
        ⟨100460, false, false, [], []⟩,
        ⟨100463, false, false, [], []⟩
      ]⟩,
    ⟨[36579, 92305], [36579, 92305], .contexts []⟩,
    ⟨[91599, 7], [36579, 92305], .contexts [
        ⟨100518, false, false, [], []⟩,
        ⟨100519, false, false, [], []⟩,
        ⟨100519, false, false, [], []⟩
      ]⟩,
    ⟨[91599, 3], [30831, 88321], .contexts [
        ⟨81937, false, false, [], []⟩
      ]⟩,
    ⟨[30831, 88321], [30831, 88321], .contexts []⟩,
    ⟨[36621], [30831, 22659], .source 18375⟩,
    ⟨[36581], [36578], .contexts [
        ⟨100464, false, false, [], []⟩
      ]⟩,
    ⟨[36623], [36581, 36621], .source 18376⟩,
    ⟨[92305, 3], [36623, 83453], .contexts [
        ⟨100520, true, false, [36578], [3]⟩,
        ⟨1034, false, false, [36578, 91599], []⟩,
        ⟨1035, false, false, [36578, 91599], []⟩,
        ⟨100521, false, false, [36578], [7]⟩,
        ⟨100522, false, false, [36578], [7]⟩,
        ⟨100522, false, false, [36578], [7]⟩,
        ⟨49910, false, false, [36578, 30831], []⟩,
        ⟨100523, true, false, [36578], [83453]⟩,
        ⟨49907, false, false, [36578, 36621], []⟩,
        ⟨100524, true, false, [], [36621, 83453]⟩,
        ⟨100525, true, false, [], [83453]⟩
      ]⟩,
    ⟨[36625], [36622], .source 18377⟩,
    ⟨[83453, 3], [36625, 92305], .contexts [
        ⟨100526, true, false, [36622], [3]⟩,
        ⟨20, false, false, [36622, 92305], []⟩,
        ⟨100527, true, false, [], [92305]⟩
      ]⟩,
    ⟨[36627], [36581, 27401], .source 18378⟩,
    ⟨[92307, 7], [36627, 85459], .contexts [
        ⟨71357, true, false, [], [7]⟩,
        ⟨100520, true, false, [36578], [15, 7]⟩,
        ⟨18155, false, false, [36578, 91599], []⟩,
        ⟨10, false, false, [36578, 91599], []⟩,
        ⟨70279, false, false, [36578], []⟩,
        ⟨70254, false, false, [36578, 27401], []⟩,
        ⟨100524, true, false, [], [27401, 85459]⟩,
        ⟨100529, true, false, [], [85459]⟩
      ]⟩,
    ⟨[36629], [36626], .source 18379⟩,
    ⟨[88681, 13], [36589, 92307], .contexts [
        ⟨100467, false, false, [], []⟩,
        ⟨100470, false, false, [], []⟩
      ]⟩,
    ⟨[36589, 92307], [36589, 92307], .contexts []⟩,
    ⟨[88681, 13], [36589, 92307], .contexts [
        ⟨100532, false, false, [], []⟩,
        ⟨100533, false, false, [], []⟩,
        ⟨100533, false, false, [], []⟩
      ]⟩,
    ⟨[36631], [36589, 36573], .source 18380⟩,
    ⟨[31205, 89283], [31205, 89283], .contexts []⟩,
    ⟨[31205, 89283], [31205, 89283], .contexts []⟩,
    ⟨[88681, 3], [31205, 89283], .contexts [
        ⟨83712, false, false, [], []⟩,
        ⟨100536, false, false, [], []⟩,
        ⟨100537, false, false, [], []⟩,
        ⟨100537, false, false, [], []⟩
      ]⟩,
    ⟨[36633], [36630], .source 18381⟩,
    ⟨[36635], [36633, 31205], .source 18382⟩,
    ⟨[92311, 13], [36635, 89283], .contexts [
        ⟨100535, false, false, [36630], [92311, 13]⟩,
        ⟨100515, false, false, [36630, 36589], [92311, 13]⟩,
        ⟨100517, false, false, [36630, 36589], [92311, 13]⟩,
        ⟨100517, false, false, [36630, 36589], [92311, 13]⟩,
        ⟨71550, true, false, [36630, 36589, 36618], [13]⟩,
        ⟨71364, true, false, [36630, 36589, 36618], [13]⟩,
        ⟨100516, false, false, [36630, 36589, 36618], [3, 13]⟩,
        ⟨100534, true, false, [36630], [3, 13]⟩,
        ⟨1132, false, false, [36630, 88681], []⟩,
        ⟨21, false, false, [36630, 88681], []⟩,
        ⟨100538, false, false, [36630], []⟩,
        ⟨83734, false, false, [36630, 31205], []⟩,
        ⟨100539, true, false, [], [31205, 89283]⟩,
        ⟨100540, true, false, [], [89283]⟩
      ]⟩,
    ⟨[36637], [36634], .source 18383⟩,
    ⟨[89283, 13], [31491, 94539], .contexts [
        ⟨85090, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1571. -/
def y322TCIndexRaw1571 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[36639], [31493, 36637], .source 18384⟩,
    ⟨[94539], [36639, 92311], .contexts [
        ⟨85086, true, false, [31490], []⟩,
        ⟨85086, true, false, [31490], []⟩,
        ⟨85085, true, false, [31490], []⟩,
        ⟨100543, true, false, [31490], []⟩,
        ⟨100541, true, false, [31490, 36634], [13]⟩,
        ⟨59, false, false, [31490, 36634, 92311], []⟩,
        ⟨100542, true, false, [31490], [92311]⟩,
        ⟨85038, true, false, [], [36637, 92311]⟩,
        ⟨100544, true, false, [], [92311]⟩
      ]⟩,
    ⟨[36641], [36638], .source 18385⟩,
    ⟨[36638], [36638], .contexts []⟩,
    ⟨[36641], [36638], .contexts [
        ⟨100546, false, false, [], []⟩,
        ⟨100547, false, false, [], []⟩
      ]⟩,
    ⟨[36643], [36641, 31515], .source 18386⟩,
    ⟨[92311, 11], [36643, 83695], .contexts [
        ⟨100545, true, false, [36638], [11]⟩,
        ⟨84823, false, false, [36638], []⟩,
        ⟨85119, false, false, [36638], []⟩,
        ⟨100548, true, false, [], [31515, 83695]⟩,
        ⟨100549, true, false, [], [83695]⟩
      ]⟩,
    ⟨[92311, 1], [36641, 94541], .contexts [
        ⟨100545, true, false, [36638], [1]⟩,
        ⟨84825, false, false, [36638], []⟩,
        ⟨84868, false, false, [36638], []⟩,
        ⟨100547, true, false, [], [94541]⟩,
        ⟨100548, true, false, [], [94541]⟩
      ]⟩,
    ⟨[36645], [36641, 31509], .source 18387⟩,
    ⟨[36647], [33035, 33039], .source 18388⟩,
    ⟨[36649], [36591, 36647], .source 18389⟩,
    ⟨[92307, 11], [36649, 83697], .contexts [
        ⟨100534, true, false, [36588], [11]⟩,
        ⟨82, false, false, [36588, 88681], []⟩,
        ⟨83, false, false, [36588, 88681], []⟩,
        ⟨97461, false, false, [36588], [13]⟩,
        ⟨90081, false, false, [36588, 33035], []⟩,
        ⟨100553, true, false, [36588], [83697]⟩,
        ⟨43555, false, false, [36588, 36647], []⟩,
        ⟨100471, true, false, [], [36647, 83697]⟩,
        ⟨100554, true, false, [], [83697]⟩
      ]⟩,
    ⟨[36651], [36648], .source 18390⟩,
    ⟨[83697, 11], [36651, 92307], .contexts [
        ⟨100555, true, false, [36648], [11]⟩,
        ⟨53, false, false, [36648, 92307], []⟩,
        ⟨100556, true, false, [], [92307]⟩
      ]⟩,
    ⟨[36607, 84629], [36607, 84629], .contexts []⟩,
    ⟨[36607, 84633], [36607, 84633], .contexts []⟩,
    ⟨[84633, 5], [84633, 5], .contexts []⟩,
    ⟨[36606], [36606], .contexts []⟩,
    ⟨[36605], [36606], .contexts [
        ⟨100490, false, false, [], []⟩,
        ⟨100561, false, false, [], []⟩,
        ⟨100561, false, false, [], []⟩
      ]⟩,
    ⟨[84633, 5], [36605, 93521], .contexts [
        ⟨100560, false, false, [], []⟩,
        ⟨100559, true, false, [36606], [5]⟩,
        ⟨27996, true, false, [], [5]⟩,
        ⟨27985, true, false, [], [1, 5]⟩,
        ⟨100558, true, false, [36606], [5, 1, 5]⟩,
        ⟨100558, true, false, [36606], [5, 1, 5]⟩,
        ⟨100489, true, false, [36606], [5, 1, 5]⟩,
        ⟨100485, true, false, [36606], [5, 1, 5]⟩,
        ⟨1152, false, false, [36606, 93521], []⟩,
        ⟨79817, false, false, [36606], []⟩,
        ⟨100562, true, false, [], [93521]⟩
      ]⟩,
    ⟨[36653], [33083, 36617], .source 18391⟩,
    ⟨[36617, 96649], [36617, 96649], .contexts []⟩,
    ⟨[92293, 13], [36617, 96649], .contexts [
        ⟨100508, false, false, [], []⟩,
        ⟨100565, false, false, [], []⟩,
        ⟨100565, false, false, [], []⟩
      ]⟩,
    ⟨[96649, 11], [96649, 11], .contexts []⟩,
    ⟨[36655], [36652], .source 18392⟩,
    ⟨[36657], [36655, 36617], .source 18393⟩,
    ⟨[92311, 5], [92313], .contexts [
        ⟨71368, false, false, [], []⟩,
        ⟨71548, false, false, [], []⟩,
        ⟨71373, false, false, [], []⟩,
        ⟨71373, false, false, [], []⟩
      ]⟩,
    ⟨[36641, 94541], [36641, 94541], .contexts []⟩,
    ⟨[36641, 94541], [36641, 94541], .contexts []⟩,
    ⟨[92315, 5], [92315, 5], .contexts []⟩,
    ⟨[92315, 5], [36641, 94541], .contexts [
        ⟨100573, false, false, [], []⟩,
        ⟨71376, true, false, [], [5]⟩,
        ⟨71376, true, false, [], [5]⟩,
        ⟨71546, true, false, [], [5]⟩,
        ⟨71372, true, false, [], [5]⟩,
        ⟨100570, true, false, [], [1, 5]⟩,
        ⟨890, false, false, [92311], []⟩,
        ⟨9, false, false, [92311], []⟩,
        ⟨100551, false, false, [], []⟩,
        ⟨100571, false, false, [], []⟩,
        ⟨100572, false, false, [], []⟩,
        ⟨100572, false, false, [], []⟩,
        ⟨85076, false, false, [36641], []⟩,
        ⟨13, true, false, [], [36641, 94541]⟩
      ]⟩,
    ⟨[94541, 5], [36639, 92315], .contexts [
        ⟨100574, true, false, [36640], [5]⟩,
        ⟨28, false, false, [36640, 92315], []⟩,
        ⟨100546, false, true, [], [92315]⟩
      ]⟩,
    ⟨[36643, 83695], [36643, 83695], .contexts []⟩,
    ⟨[36643, 83695], [36643, 83695], .contexts []⟩,
    ⟨[36659], [36643, 26865], .source 18394⟩,
    ⟨[92313, 11], [92313, 11], .contexts []⟩,
    ⟨[36659], [36659], .contexts []⟩,
    ⟨[36659], [36659], .contexts []⟩,
    ⟨[92313, 11], [36659, 86637], .contexts [
        ⟨100579, false, false, [], []⟩,
        ⟨100570, true, false, [], [11]⟩,
        ⟨174, false, false, [92311], []⟩,
        ⟨175, false, false, [92311], []⟩,
        ⟨100550, false, false, [], [5]⟩,
        ⟨100576, false, false, [], [5]⟩,
        ⟨100577, false, false, [], [5]⟩,
        ⟨100577, false, false, [], [5]⟩,
        ⟨68518, false, false, [36643], []⟩,
        ⟨100578, true, false, [], [86637]⟩,
        ⟨90128, false, false, [36659], []⟩,
        ⟨100581, true, false, [], [86637]⟩,
        ⟨100580, true, false, [], [86637]⟩,
        ⟨13, true, false, [], [36659, 86637]⟩
      ]⟩,
    ⟨[36661], [36658], .source 18395⟩,
    ⟨[84633, 5], [36605, 93521], .contexts [
        ⟨100560, false, false, [], []⟩,
        ⟨100563, false, false, [], []⟩
      ]⟩,
    ⟨[36605, 93521], [36605, 93521], .contexts []⟩,
    ⟨[36605, 93521], [36605, 93521], .contexts []⟩,
    ⟨[84633, 5], [36605, 93521], .contexts [
        ⟨100584, false, false, [], []⟩,
        ⟨100585, false, false, [], []⟩,
        ⟨100586, false, false, [], []⟩,
        ⟨100586, false, false, [], []⟩
      ]⟩,
    ⟨[36663], [36605, 30835], .source 18396⟩,
    ⟨[36665], [36663, 36477], .source 18397⟩,
    ⟨[36665, 85633], [36665, 85633], .contexts []⟩,
    ⟨[36665, 85633], [36665, 85633], .contexts []⟩,
    ⟨[36665, 85633, 3], [84633], .contexts [
        ⟨100591, true, false, [], [3]⟩,
        ⟨100590, true, false, [], [3]⟩,
        ⟨32921, true, false, [36665], [3]⟩,
        ⟨32917, true, false, [36665], [5, 3]⟩,
        ⟨100589, false, false, [], [85629, 3, 5, 3]⟩,
        ⟨100247, true, false, [36663], [3, 5, 3]⟩,
        ⟨100588, false, false, [], [93917, 5, 3, 5, 3]⟩,
        ⟨81949, true, false, [36605], [5, 3, 5, 3]⟩,
        ⟨100587, true, false, [], [3, 5, 3, 5, 3]⟩,
        ⟨7129, false, false, [84633], []⟩
      ]⟩,
    ⟨[85633, 3], [85633, 3], .contexts []⟩,
    ⟨[84633], [84633], .contexts []⟩,
    ⟨[36667], [36664], .source 18398⟩,
    ⟨[36664], [36664], .contexts []⟩,
    ⟨[85633, 3], [36667, 84633], .contexts [
        ⟨100593, false, false, [], []⟩,
        ⟨100592, false, false, [36664], []⟩,
        ⟨100594, false, false, [36664], []⟩,
        ⟨100596, true, false, [], [84633]⟩,
        ⟨100596, true, false, [], [84633]⟩,
        ⟨100595, true, false, [], [84633]⟩
      ]⟩,
    ⟨[36665], [36666], .contexts [
        ⟨100595, true, true, [], []⟩
      ]⟩,
    ⟨[84633, 3], [36665, 85633], .contexts [
        ⟨100597, true, false, [36666], [3]⟩,
        ⟨20, false, false, [36666, 85633], []⟩,
        ⟨100598, true, false, [], [85633]⟩
      ]⟩,
    ⟨[36605, 93519], [36605, 93519], .contexts []⟩,
    ⟨[84633, 9], [84635], .contexts [
        ⟨27999, false, false, [], []⟩
      ]⟩,
    ⟨[93519, 5], [93519, 5], .contexts []⟩,
    ⟨[84635], [84635], .contexts []⟩,
    ⟨[93519, 5], [36607, 84635], .contexts [
        ⟨100602, false, false, [], []⟩,
        ⟨100600, true, false, [36604], [5]⟩,
        ⟨79440, true, false, [], [5]⟩,
        ⟨100587, true, false, [36604], [9, 5]⟩,
        ⟨960, false, false, [36604, 84633], []⟩,
        ⟨47, false, false, [36604, 84633], []⟩,
        ⟨100601, false, false, [36604], []⟩,
        ⟨28219, false, false, [36604], []⟩,
        ⟨28004, false, false, [36604], []⟩,
        ⟨28004, false, false, [36604], []⟩,
        ⟨100603, false, false, [36604], []⟩,
        ⟨100488, true, false, [], [84635]⟩
      ]⟩,
    ⟨[36657, 96649], [36657, 96649], .contexts []⟩,
    ⟨[96649, 11, 15], [36657, 96651], .contexts [
        ⟨100567, false, false, [], [15]⟩,
        ⟨100567, false, false, [], [15]⟩,
        ⟨100564, false, false, [36652], [96649, 11, 15]⟩,
        ⟨100508, true, false, [36652, 33083], [11, 15]⟩,
        ⟨90376, true, false, [36652], [13, 11, 15]⟩,
        ⟨619, false, false, [36652, 92293], [15]⟩,
        ⟨64, false, false, [36652, 92293], [15]⟩,
        ⟨100566, false, false, [36652], [15]⟩,
        ⟨99125, false, false, [36652, 36617], [15]⟩,
        ⟨100568, true, false, [], [36617, 96649, 15]⟩,
        ⟨100569, true, false, [], [96649, 15]⟩,
        ⟨100605, false, false, [], [15]⟩,
        ⟨100605, false, false, [], [15]⟩,
        ⟨99127, false, false, [36657], []⟩
      ]⟩,
    ⟨[96651, 11], [96651, 11], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1572. -/
def y322TCIndexRaw1572 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[36669], [36656], .source 18399⟩,
    ⟨[36656], [36656], .contexts []⟩,
    ⟨[36669], [36656], .contexts [
        ⟨100608, false, false, [], []⟩,
        ⟨100609, false, false, [], []⟩,
        ⟨100609, false, false, [], []⟩
      ]⟩,
    ⟨[96651, 11], [36669, 96651], .contexts [
        ⟨100607, false, false, [], []⟩,
        ⟨100606, true, false, [36656], [11]⟩,
        ⟨615, false, false, [36656, 96649], []⟩,
        ⟨10, false, false, [36656, 96649], []⟩,
        ⟨99131, false, false, [36656], []⟩,
        ⟨99136, false, false, [36656], []⟩,
        ⟨100610, true, false, [], [96651]⟩
      ]⟩,
    ⟨[92315, 5], [36641, 94541], .contexts [
        ⟨100573, false, false, [], []⟩,
        ⟨100574, false, false, [], []⟩,
        ⟨100571, false, false, [], []⟩,
        ⟨100572, false, false, [], []⟩,
        ⟨100572, false, false, [], []⟩
      ]⟩,
    ⟨[36671], [36641, 31513], .source 18400⟩,
    ⟨[36673], [36671, 36639], .source 18401⟩,
    ⟨[92315], [92315], .contexts []⟩,
    ⟨[36675], [36672], .source 18402⟩,
    ⟨[92315, 11], [36674, 92319], .contexts [
        ⟨100616, false, false, [36674], [92315, 11]⟩,
        ⟨100615, false, false, [36674, 36672], [11]⟩,
        ⟨881, true, false, [36674, 36672, 92315], [11]⟩,
        ⟨100612, false, false, [36674, 36672], [9, 5, 9, 11]⟩,
        ⟨85094, false, false, [36674, 36672, 36641], [5, 9, 11]⟩,
        ⟨100613, true, false, [36674, 36672], [94541, 5, 9, 11]⟩,
        ⟨100575, false, false, [36674, 36672, 36671], [9, 11]⟩,
        ⟨100614, true, false, [36674, 36672], [92315, 9, 11]⟩,
        ⟨71375, false, false, [36674], [11]⟩,
        ⟨71378, false, false, [36674], []⟩,
        ⟨71545, false, false, [36674], []⟩
      ]⟩,
    ⟨[36674], [36674], .contexts []⟩,
    ⟨[92315, 11], [36673, 92319], .contexts [
        ⟨100617, false, false, [], []⟩,
        ⟨100618, true, false, [], [92319]⟩,
        ⟨100618, true, false, [], [92319]⟩,
        ⟨100616, false, true, [], [92319]⟩
      ]⟩,
    ⟨[92315], [92315], .contexts []⟩,
    ⟨[36658], [36658], .contexts []⟩,
    ⟨[86635, 11], [36661, 92315], .contexts [
        ⟨100578, false, false, [36658], [86635, 11]⟩,
        ⟨68480, true, false, [36658, 36643], [11]⟩,
        ⟨100549, false, false, [36658], [83693, 5, 11]⟩,
        ⟨85103, true, false, [36658, 36641], [5, 11]⟩,
        ⟨100612, true, false, [36658], [11, 5, 11]⟩,
        ⟨4188, false, false, [36658, 92315], []⟩,
        ⟨100620, false, false, [36658], []⟩,
        ⟨100615, false, false, [36658], []⟩,
        ⟨100621, true, false, [], [92315]⟩,
        ⟨100621, true, false, [], [92315]⟩,
        ⟨100583, true, false, [], [92315]⟩
      ]⟩,
    ⟨[92315, 11], [36673, 92319], .contexts [
        ⟨100619, false, false, [], []⟩
      ]⟩,
    ⟨[36673, 92319], [36673, 92319], .contexts []⟩,
    ⟨[36677], [36675, 36659], .source 18403⟩,
    ⟨[92319], [36677, 86635], .contexts [
        ⟨100624, true, false, [36672], []⟩,
        ⟨100624, true, false, [36672], []⟩,
        ⟨100623, true, false, [36672], []⟩,
        ⟨100622, true, false, [36672, 36660], [11]⟩,
        ⟨53, false, false, [36672, 36660, 86635], []⟩,
        ⟨100583, false, true, [36672], [86635]⟩,
        ⟨100616, true, false, [], [36659, 86635]⟩,
        ⟨100625, true, false, [], [86635]⟩
      ]⟩,
    ⟨[36677, 86637], [36677, 86637], .contexts []⟩,
    ⟨[36679], [36676], .source 18404⟩,
    ⟨[36681], [36677, 33071], .source 18405⟩,
    ⟨[36683], [36680], .source 18406⟩,
    ⟨[85731], [36683, 92323], .contexts [
        ⟨100629, false, false, [36680], [85731]⟩,
        ⟨90132, true, false, [36680, 36677], []⟩,
        ⟨100627, true, false, [36680], [13]⟩,
        ⟨100628, true, true, [36680], [86637, 13]⟩,
        ⟨100627, true, false, [36680, 36678, 36676], [13]⟩,
        ⟨38272, true, false, [36680, 36678], [13]⟩,
        ⟨100626, true, false, [36680, 36678, 36676], [1, 13]⟩,
        ⟨71381, false, false, [36680, 36678, 36676], [13]⟩,
        ⟨71544, false, false, [36680, 36678, 36676], [13]⟩,
        ⟨13, true, false, [36680, 36678, 36676], [92321, 13]⟩,
        ⟨100628, true, false, [36680, 36678], [92321, 13]⟩,
        ⟨71384, false, false, [36680], []⟩,
        ⟨71542, false, false, [36680], []⟩,
        ⟨13, true, false, [36680], [92323]⟩,
        ⟨100630, true, false, [], [92323]⟩
      ]⟩,
    ⟨[36685], [36681, 23105], .source 18407⟩,
    ⟨[36687], [36684], .source 18408⟩,
    ⟨[92325, 1], [36685, 23107, 85727], .contexts [
        ⟨100633, false, false, [36686], [92325, 1]⟩,
        ⟨13, false, false, [36686, 36684], [92325, 1]⟩,
        ⟨71541, true, false, [36686, 36684], [1]⟩,
        ⟨71387, true, false, [36686, 36684], [1]⟩,
        ⟨100631, true, false, [36686, 36684, 36682], [15, 1]⟩,
        ⟨100630, false, true, [36686, 36684], [85731, 15, 1]⟩,
        ⟨51803, false, false, [36686, 36684, 36681], [1]⟩,
        ⟨100632, true, false, [36686, 36684], [85199, 1]⟩,
        ⟨100633, false, true, [], [85199, 1]⟩,
        ⟨51791, false, false, [36685], []⟩
      ]⟩,
    ⟨[36689], [36685, 23107], .source 18409⟩,
    ⟨[36691], [36688], .source 18410⟩,
    ⟨[36693], [36689, 1063], .source 18411⟩,
    ⟨[36695], [36692], .source 18412⟩,
    ⟨[92329], [36693, 85727], .contexts [
        ⟨100638, false, false, [36694], [92329]⟩,
        ⟨13, false, false, [36694, 36692], [92329]⟩,
        ⟨71539, true, false, [36694, 36692], []⟩,
        ⟨71393, true, false, [36694, 36692], []⟩,
        ⟨100636, false, false, [36694, 36692, 36690], [92327, 3]⟩,
        ⟨13, false, false, [36694, 36692, 36690, 36688], [92327, 3]⟩,
        ⟨71540, true, false, [36694, 36692, 36690, 36688], [3]⟩,
        ⟨71390, true, false, [36694, 36692, 36690, 36688], [3]⟩,
        ⟨100634, false, false, [36694, 36692, 36690, 36688], [3]⟩,
        ⟨100635, true, false, [36694, 36692, 36690, 36688], [85727, 3]⟩,
        ⟨100636, false, true, [36694, 36692], [85727, 3]⟩,
        ⟨33272, false, false, [36694, 36692, 36689], []⟩,
        ⟨100637, true, false, [36694, 36692], [85727]⟩,
        ⟨100638, false, true, [], [85727]⟩
      ]⟩,
    ⟨[36697], [36693, 7355], .source 18413⟩,
    ⟨[36699], [36696], .source 18414⟩,
    ⟨[36699], [36696], .contexts [
        ⟨100641, false, false, [], []⟩
      ]⟩,
    ⟨[92331], [36697, 83385], .contexts [
        ⟨100642, false, false, [36698], [92331]⟩,
        ⟨13, false, false, [36698, 36696], [92331]⟩,
        ⟨71538, true, false, [36698, 36696], []⟩,
        ⟨71396, true, false, [36698, 36696], []⟩,
        ⟨100639, false, false, [36698, 36696], [5]⟩,
        ⟨33277, false, false, [36698, 36696, 36693], []⟩,
        ⟨100640, true, false, [36698, 36696], [83385]⟩,
        ⟨100641, false, true, [], [83385]⟩
      ]⟩,
    ⟨[36696], [36696], .contexts []⟩,
    ⟨[83385, 1], [36699, 92333], .contexts [
        ⟨100643, true, false, [36696], [1]⟩,
        ⟨71399, false, false, [36696], []⟩,
        ⟨71536, false, false, [36696], []⟩,
        ⟨100644, true, false, [], [92333]⟩,
        ⟨100644, true, false, [], [92333]⟩,
        ⟨100642, true, false, [], [92333]⟩
      ]⟩,
    ⟨[36667, 84633], [36667, 84633], .contexts []⟩,
    ⟨[36667, 84633], [36667, 84633], .contexts []⟩,
    ⟨[85633, 3], [36667, 84633], .contexts [
        ⟨100593, false, false, [], []⟩,
        ⟨100597, false, false, [], []⟩,
        ⟨100646, false, false, [], []⟩,
        ⟨100647, false, false, [], []⟩,
        ⟨100647, false, false, [], []⟩
      ]⟩,
    ⟨[85633, 9], [18983, 85637], .contexts [
        ⟨36160, false, false, [], []⟩
      ]⟩,
    ⟨[18983, 85637], [18983, 85637], .contexts []⟩,
    ⟨[84635, 3], [84635, 3], .contexts []⟩,
    ⟨[85637], [85637], .contexts []⟩,
    ⟨[36701], [36665, 18983], .source 18415⟩,
    ⟨[84635, 3], [36701, 85637], .contexts [
        ⟨100651, false, false, [], []⟩,
        ⟨27999, true, false, [], [3]⟩,
        ⟨100648, true, false, [36666], [9, 3]⟩,
        ⟨573, false, false, [36666, 85633], []⟩,
        ⟨47, false, false, [36666, 85633], []⟩,
        ⟨100649, false, false, [36666], []⟩,
        ⟨100650, false, false, [36666], []⟩,
        ⟨100650, false, false, [36666], []⟩,
        ⟨100652, false, false, [36666, 18983], []⟩,
        ⟨100598, true, false, [], [18983, 85637]⟩,
        ⟨100653, true, false, [], [85637]⟩
      ]⟩,
    ⟨[36703], [36700], .source 18416⟩,
    ⟨[93519, 5], [36607, 84635], .contexts [
        ⟨100602, false, false, [], []⟩,
        ⟨100604, false, false, [], []⟩
      ]⟩,
    ⟨[36607, 84635], [36607, 84635], .contexts []⟩,
    ⟨[84635, 1], [84635, 1], .contexts []⟩,
    ⟨[84635, 1], [36605, 93515], .contexts [
        ⟨100658, false, false, [], []⟩,
        ⟨100657, true, false, [36606], [1]⟩,
        ⟨100657, true, false, [36606], [1]⟩,
        ⟨100656, true, false, [36606], [1]⟩,
        ⟨161, false, false, [36606, 93519], []⟩,
        ⟨162, false, false, [36606, 93519], []⟩,
        ⟨79889, false, false, [36606], [5]⟩,
        ⟨79509, false, false, [36606], []⟩,
        ⟨79510, false, false, [36606], []⟩,
        ⟨79431, false, false, [36606], []⟩,
        ⟨79431, false, false, [36606], []⟩,
        ⟨100562, true, false, [], [93515]⟩
      ]⟩,
    ⟨[36669, 96651], [36669, 96651], .contexts []⟩,
    ⟨[36669, 96651], [36669, 96651], .contexts []⟩,
    ⟨[96651, 11], [36669, 96651], .contexts [
        ⟨100607, false, false, [], []⟩,
        ⟨100611, false, false, [], []⟩,
        ⟨100660, false, false, [], []⟩,
        ⟨100661, false, false, [], []⟩,
        ⟨100661, false, false, [], []⟩
      ]⟩,
    ⟨[96651, 3], [96653], .contexts [
        ⟨99139, false, false, [], []⟩,
        ⟨99364, false, false, [], []⟩,
        ⟨99143, false, false, [], []⟩,
        ⟨99143, false, false, [], []⟩
      ]⟩,
    ⟨[96653, 11], [96653, 11], .contexts []⟩,
    ⟨[96653], [96653], .contexts []⟩,
    ⟨[36668], [36668], .contexts []⟩,
    ⟨[36657], [36668], .contexts [
        ⟨100608, true, true, [], []⟩,
        ⟨100666, false, false, [], []⟩,
        ⟨100666, false, false, [], []⟩
      ]⟩,
    ⟨[96653, 11], [36657, 96653], .contexts [
        ⟨100664, false, false, [], []⟩,
        ⟨99139, true, false, [], [11]⟩,
        ⟨100662, true, false, [36668], [3, 11]⟩,
        ⟨603, false, false, [36668, 96651], []⟩,
        ⟨21, false, false, [36668, 96651], []⟩,
        ⟨100663, false, false, [36668], []⟩,
        ⟨100665, false, false, [36668], []⟩,
        ⟨100667, true, false, [], [96653]⟩
      ]⟩,
    ⟨[36673, 92319], [36673, 36677, 86635], .contexts [
        ⟨100626, false, false, [36673], []⟩
      ]⟩,
    ⟨[36705], [36673, 36677], .source 18417⟩,
    ⟨[36707], [36705, 33113], .source 18418⟩]

/-- Exact literal claimed equations and contextual derivations, block 1573. -/
def y322TCIndexRaw1573 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[36709], [36707, 28923], .source 18419⟩,
    ⟨[36711], [36708], .source 18420⟩,
    ⟨[36708], [36708], .contexts []⟩,
    ⟨[90501, 7], [36711, 92315], .contexts [
        ⟨100672, false, false, [36708], [90501, 7]⟩,
        ⟨75297, true, false, [36708, 36707], [7]⟩,
        ⟨100671, false, false, [36708], [84989, 11, 7]⟩,
        ⟨90266, true, false, [36708, 36705], [11, 7]⟩,
        ⟨100670, false, false, [36708], [86635, 7, 11, 7]⟩,
        ⟨100669, true, false, [36708], [7, 11, 7]⟩,
        ⟨100623, true, false, [36708], [7, 11, 7]⟩,
        ⟨14923, false, false, [36708, 92315], []⟩,
        ⟨100620, false, false, [36708], []⟩,
        ⟨100615, false, false, [36708], []⟩,
        ⟨100674, true, false, [], [92315]⟩,
        ⟨100674, true, false, [], [92315]⟩,
        ⟨100673, true, false, [], [92315]⟩
      ]⟩,
    ⟨[36713], [23107, 7355], .source 18421⟩,
    ⟨[36715], [36713, 36699], .source 18422⟩,
    ⟨[92333, 5], [92333, 5], .contexts []⟩,
    ⟨[36717], [36714], .source 18423⟩,
    ⟨[36717], [36714], .contexts [
        ⟨100679, false, false, [], []⟩
      ]⟩,
    ⟨[36714], [36714], .contexts []⟩,
    ⟨[36717], [36714], .contexts [
        ⟨100680, false, false, [], []⟩,
        ⟨100681, false, false, [], []⟩,
        ⟨100681, false, false, [], []⟩
      ]⟩,
    ⟨[92333, 5], [36717, 85199], .contexts [
        ⟨100678, false, false, [], []⟩,
        ⟨100677, false, false, [36714], [92333, 5]⟩,
        ⟨100645, true, false, [36714, 36713], [5]⟩,
        ⟨100676, false, false, [36714], [83385, 1, 5]⟩,
        ⟨33277, true, false, [36714, 23107], [1, 5]⟩,
        ⟨51798, true, false, [36714], [5, 1, 5]⟩,
        ⟨1152, false, false, [36714, 85199], []⟩,
        ⟨51801, false, false, [36714], []⟩,
        ⟨51802, false, false, [36714], []⟩,
        ⟨100682, true, false, [], [85199]⟩
      ]⟩,
    ⟨[36715], [36716], .contexts [
        ⟨100679, true, true, [], []⟩
      ]⟩,
    ⟨[85199, 5], [36715, 92333], .contexts [
        ⟨100683, true, false, [36716], [5]⟩,
        ⟨28, false, false, [36716, 92333], []⟩,
        ⟨100684, true, false, [], [92333]⟩
      ]⟩,
    ⟨[36715, 92333], [36715, 92333], .contexts []⟩,
    ⟨[36715, 92333], [36715, 92333], .contexts []⟩,
    ⟨[85199, 5], [36715, 92333], .contexts [
        ⟨100685, false, false, [], []⟩,
        ⟨100686, false, false, [], []⟩,
        ⟨100687, false, false, [], []⟩,
        ⟨100687, false, false, [], []⟩
      ]⟩,
    ⟨[85199, 4], [85199, 5], .contexts [
        ⟨29, false, false, [85199], []⟩
      ]⟩,
    ⟨[83389, 15], [83389, 15], .contexts []⟩,
    ⟨[92333], [92333], .contexts []⟩,
    ⟨[36719], [36712], .source 18424⟩,
    ⟨[36721], [36719, 36715], .source 18425⟩,
    ⟨[83389, 15], [36721, 92333], .contexts [
        ⟨100690, false, false, [], []⟩,
        ⟨100676, false, false, [36712], [83389, 15]⟩,
        ⟨33304, true, false, [36712, 23107], [15]⟩,
        ⟨51812, true, false, [36712], [5, 15]⟩,
        ⟨2072, false, false, [36712, 85199], []⟩,
        ⟨100689, false, false, [36712], []⟩,
        ⟨100688, false, false, [36712], []⟩,
        ⟨100691, false, false, [36712, 36715], []⟩,
        ⟨100692, true, false, [], [36715, 92333]⟩,
        ⟨100693, true, false, [], [92333]⟩
      ]⟩,
    ⟨[36723], [36720], .source 18426⟩,
    ⟨[35483, 96757], [35483, 96757], .contexts []⟩,
    ⟨[35483, 96757], [35483, 96757], .contexts []⟩,
    ⟨[36725], [35483, 36077], .source 18427⟩,
    ⟨[95357, 13], [95357, 13], .contexts []⟩,
    ⟨[36727], [36724], .source 18428⟩,
    ⟨[36729], [36727, 36715], .source 18429⟩,
    ⟨[95357, 13], [36729, 92333], .contexts [
        ⟨100699, false, false, [], []⟩,
        ⟨100698, false, false, [36724], [95357, 13]⟩,
        ⟨99893, true, false, [36724, 35483], [13]⟩,
        ⟨100697, true, false, [36724], [5, 13]⟩,
        ⟨100697, true, false, [36724], [5, 13]⟩,
        ⟨100696, true, false, [36724], [5, 13]⟩,
        ⟨99908, true, false, [36724], [5, 13]⟩,
        ⟨1136, false, false, [36724, 85199], []⟩,
        ⟨100689, false, false, [36724], []⟩,
        ⟨100688, false, false, [36724], []⟩,
        ⟨100691, false, false, [36724, 36715], []⟩,
        ⟨100700, true, false, [], [36715, 92333]⟩,
        ⟨100701, true, false, [], [92333]⟩
      ]⟩,
    ⟨[36731], [36728], .source 18430⟩,
    ⟨[22259, 96049], [22259, 96049], .contexts []⟩,
    ⟨[36733], [22259, 34991], .source 18431⟩,
    ⟨[36699, 92333], [36699, 92333], .contexts []⟩,
    ⟨[36699, 92333], [36699, 92333], .contexts []⟩,
    ⟨[83385, 1], [36699, 92333], .contexts [
        ⟨100645, false, false, [], []⟩,
        ⟨100706, false, false, [], []⟩,
        ⟨100707, false, false, [], []⟩,
        ⟨100707, false, false, [], []⟩
      ]⟩,
    ⟨[83385, 0], [83385, 1], .contexts [
        ⟨9, false, false, [83385], []⟩
      ]⟩,
    ⟨[89081, 7], [89081, 7], .contexts []⟩,
    ⟨[36735], [36732], .source 18432⟩,
    ⟨[36737], [36735, 36699], .source 18433⟩,
    ⟨[89081, 7], [36737, 92333], .contexts [
        ⟨100710, false, false, [], []⟩,
        ⟨100705, false, false, [36732], [89081, 7]⟩,
        ⟨95679, true, false, [36732, 22259], [7]⟩,
        ⟨100704, true, false, [36732], [1, 7]⟩,
        ⟨100704, true, false, [36732], [1, 7]⟩,
        ⟨95667, true, false, [36732], [1, 7]⟩,
        ⟨502, false, false, [36732, 83385], []⟩,
        ⟨100709, false, false, [36732], []⟩,
        ⟨100708, false, false, [36732], []⟩,
        ⟨100691, false, false, [36732, 36699], []⟩,
        ⟨100711, true, false, [], [36699, 92333]⟩,
        ⟨100712, true, false, [], [92333]⟩
      ]⟩,
    ⟨[36739], [36736], .source 18434⟩,
    ⟨[35495, 88691], [35495, 88691], .contexts []⟩,
    ⟨[35495, 88691], [35495, 88691], .contexts []⟩,
    ⟨[36741], [35497, 36699], .source 18435⟩,
    ⟨[88691, 11], [36741, 92333], .contexts [
        ⟨100716, true, false, [35494], [11]⟩,
        ⟨100716, true, false, [35494], [11]⟩,
        ⟨100715, true, false, [35494], [11]⟩,
        ⟨97437, true, false, [35494], [11]⟩,
        ⟨97428, true, false, [35494], [1, 11]⟩,
        ⟨97428, true, false, [35494], [1, 11]⟩,
        ⟨97427, true, false, [35494], [1, 11]⟩,
        ⟨97445, true, false, [35494], [1, 11]⟩,
        ⟨567, false, false, [35494, 83385], []⟩,
        ⟨100709, false, false, [35494], []⟩,
        ⟨100708, false, false, [35494], []⟩,
        ⟨100691, false, false, [35494, 36699], []⟩,
        ⟨97438, true, false, [], [36699, 92333]⟩,
        ⟨100717, true, false, [], [92333]⟩
      ]⟩,
    ⟨[36743], [36740], .source 18436⟩,
    ⟨[36701, 85637], [36701, 85637], .contexts []⟩,
    ⟨[36701, 85637], [36701, 85637], .contexts []⟩,
    ⟨[84635, 3], [36701, 85637], .contexts [
        ⟨100651, false, false, [], []⟩,
        ⟨100654, false, false, [], []⟩,
        ⟨100720, false, false, [], []⟩,
        ⟨100721, false, false, [], []⟩,
        ⟨100721, false, false, [], []⟩
      ]⟩,
    ⟨[36701, 85639], [36701, 85639], .contexts []⟩,
    ⟨[36701, 85639], [36701, 85639], .contexts []⟩,
    ⟨[84635, 11], [84637], .contexts [
        ⟨28003, false, false, [], []⟩,
        ⟨28217, false, false, [], []⟩,
        ⟨28008, false, false, [], []⟩,
        ⟨28008, false, false, [], []⟩
      ]⟩,
    ⟨[85639, 3], [85639, 3], .contexts []⟩,
    ⟨[84637], [84637], .contexts []⟩,
    ⟨[36700], [36700], .contexts []⟩,
    ⟨[85639, 3], [36703, 84637], .contexts [
        ⟨100726, false, false, [], []⟩,
        ⟨100724, true, false, [36700], [3]⟩,
        ⟨100723, true, false, [36700], [3]⟩,
        ⟨32932, true, false, [], [3]⟩,
        ⟨100722, true, false, [36700], [11, 3]⟩,
        ⟨545, false, false, [36700, 84635], []⟩,
        ⟨54, false, false, [36700, 84635], []⟩,
        ⟨100725, false, false, [36700], []⟩,
        ⟨100727, false, false, [36700], []⟩,
        ⟨100728, true, false, [], [84637]⟩,
        ⟨100728, true, false, [], [84637]⟩,
        ⟨100655, true, false, [], [84637]⟩
      ]⟩,
    ⟨[36701], [36702], .contexts [
        ⟨100655, true, true, [], []⟩
      ]⟩,
    ⟨[84637, 3], [36701, 85639], .contexts [
        ⟨100729, true, false, [36702], [3]⟩,
        ⟨20, false, false, [36702, 85639], []⟩,
        ⟨100730, true, false, [], [85639]⟩
      ]⟩,
    ⟨[36605, 93515], [36605, 93515], .contexts []⟩,
    ⟨[84637, 1], [84639], .contexts [
        ⟨28007, false, false, [], []⟩
      ]⟩,
    ⟨[84639], [84639], .contexts []⟩,
    ⟨[84639, 11], [36605, 93515], .contexts [
        ⟨100488, false, false, [36606], [84639, 11]⟩,
        ⟨100734, true, false, [36606, 36604], [11]⟩,
        ⟨28012, true, false, [36606, 36604], [11]⟩,
        ⟨28012, true, false, [36606, 36604], [11]⟩,
        ⟨28216, true, false, [36606, 36604], [11]⟩,
        ⟨100733, true, false, [36606, 36604], [11]⟩,
        ⟨100725, true, false, [36606, 36604], [1, 11]⟩,
        ⟨111, true, false, [36606, 36604, 84635], [11]⟩,
        ⟨110, true, false, [36606, 36604, 84635], [11]⟩,
        ⟨100658, false, false, [36606, 36604], [11, 11]⟩,
        ⟨100659, false, false, [36606, 36604], [11, 11]⟩,
        ⟨100732, false, false, [36606, 36604], [11, 11]⟩,
        ⟨100732, false, false, [36606, 36604], [11, 11]⟩,
        ⟨53, false, false, [36606, 93515], []⟩,
        ⟨100490, true, false, [], [93515]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1574. -/
def y322TCIndexRaw1574 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[36657, 96653], [36657, 96653], .contexts []⟩,
    ⟨[36657, 96653], [36657, 96653], .contexts []⟩,
    ⟨[96653, 5], [96655], .contexts [
        ⟨99142, false, false, [], []⟩
      ]⟩,
    ⟨[96653, 5], [96655], .contexts [
        ⟨100738, false, false, [], []⟩,
        ⟨99361, false, false, [], []⟩,
        ⟨99147, false, false, [], []⟩,
        ⟨99147, false, false, [], []⟩
      ]⟩,
    ⟨[96653, 4], [96653, 5], .contexts [
        ⟨29, false, false, [96653], []⟩
      ]⟩,
    ⟨[96655, 11], [96655, 11], .contexts []⟩,
    ⟨[96655], [96655], .contexts []⟩,
    ⟨[96655, 11], [36669, 96655], .contexts [
        ⟨100741, false, false, [], []⟩,
        ⟨99142, true, false, [], [11]⟩,
        ⟨100737, true, false, [36656], [5, 11]⟩,
        ⟨100737, true, false, [36656], [5, 11]⟩,
        ⟨100736, true, false, [36656], [5, 11]⟩,
        ⟨100668, true, false, [36656], [5, 11]⟩,
        ⟨100664, true, false, [36656], [5, 11]⟩,
        ⟨588, false, false, [36656, 96653], []⟩,
        ⟨100740, false, false, [36656], []⟩,
        ⟨100739, false, false, [36656], []⟩,
        ⟨100742, false, false, [36656], []⟩,
        ⟨100610, true, false, [], [96655]⟩
      ]⟩,
    ⟨[36717, 85199], [36717, 85199], .contexts []⟩,
    ⟨[85197, 5], [85197, 5], .contexts []⟩,
    ⟨[36716], [36716], .contexts []⟩,
    ⟨[36715], [36716], .contexts [
        ⟨100684, false, false, [], []⟩,
        ⟨100746, false, false, [], []⟩,
        ⟨100746, false, false, [], []⟩
      ]⟩,
    ⟨[85197, 5], [36715, 92335], .contexts [
        ⟨100745, false, false, [], []⟩,
        ⟨30429, true, false, [], [5]⟩,
        ⟨100744, true, false, [36716], [9, 5]⟩,
        ⟨100744, true, false, [36716], [9, 5]⟩,
        ⟨100683, true, false, [36716], [9, 5]⟩,
        ⟨100678, true, false, [36716], [9, 5]⟩,
        ⟨960, false, false, [36716, 92333], []⟩,
        ⟨47, false, false, [36716, 92333], []⟩,
        ⟨71403, false, false, [36716], []⟩,
        ⟨71535, false, false, [36716], []⟩,
        ⟨71408, false, false, [36716], []⟩,
        ⟨71408, false, false, [36716], []⟩,
        ⟨100747, true, false, [], [92335]⟩
      ]⟩,
    ⟨[36721, 92333], [36721, 92333], .contexts []⟩,
    ⟨[36721, 92333], [36721, 92333], .contexts []⟩,
    ⟨[92335, 15], [92335, 15], .contexts []⟩,
    ⟨[36745], [36723, 33013], .source 18437⟩,
    ⟨[92335, 15], [36745, 89279], .contexts [
        ⟨100751, false, false, [], []⟩,
        ⟨71403, true, false, [], [15]⟩,
        ⟨100750, true, false, [36720], [9, 15]⟩,
        ⟨100750, true, false, [36720], [9, 15]⟩,
        ⟨100749, true, false, [36720], [9, 15]⟩,
        ⟨100694, true, false, [36720], [9, 15]⟩,
        ⟨100690, true, false, [36720], [9, 15]⟩,
        ⟨1671, false, false, [36720, 83389], []⟩,
        ⟨47, false, false, [36720, 83389], []⟩,
        ⟨90101, false, false, [36720], []⟩,
        ⟨85129, false, false, [36720, 33013], []⟩,
        ⟨100695, true, false, [], [33013, 89279]⟩,
        ⟨100752, true, false, [], [89279]⟩
      ]⟩,
    ⟨[36747], [36744], .source 18438⟩,
    ⟨[89279, 15], [36747, 92335], .contexts [
        ⟨100753, true, false, [36744], [15]⟩,
        ⟨1, false, false, [36744, 92335], []⟩,
        ⟨100754, true, false, [], [92335]⟩
      ]⟩,
    ⟨[36729, 92333], [36729, 92333], .contexts []⟩,
    ⟨[36729, 92333], [36729, 92333], .contexts []⟩,
    ⟨[95355], [36337, 89075], .contexts [
        ⟨99926, false, false, [], []⟩
      ]⟩,
    ⟨[36749], [36731, 36337], .source 18439⟩,
    ⟨[92335, 13], [36749, 89075], .contexts [
        ⟨71403, true, false, [], [13]⟩,
        ⟨100757, true, false, [36728], [9, 13]⟩,
        ⟨100757, true, false, [36728], [9, 13]⟩,
        ⟨100756, true, false, [36728], [9, 13]⟩,
        ⟨100702, true, false, [36728], [9, 13]⟩,
        ⟨100699, true, false, [36728], [9, 13]⟩,
        ⟨942, false, false, [36728, 95357], []⟩,
        ⟨47, false, false, [36728, 95357], []⟩,
        ⟨89548, false, false, [36728], []⟩,
        ⟨100758, false, false, [36728], []⟩,
        ⟨99925, false, false, [36728], []⟩,
        ⟨99925, false, false, [36728], []⟩,
        ⟨83772, false, false, [36728, 36337], []⟩,
        ⟨100703, true, false, [], [36337, 89075]⟩,
        ⟨100759, true, false, [], [89075]⟩
      ]⟩,
    ⟨[36751], [36748], .source 18440⟩,
    ⟨[89075, 13], [36751, 92335], .contexts [
        ⟨100760, true, false, [36748], [13]⟩,
        ⟨59, false, false, [36748, 92335], []⟩,
        ⟨100761, true, false, [], [92335]⟩
      ]⟩,
    ⟨[36737, 92333], [36737, 92333], .contexts []⟩,
    ⟨[36737, 92333], [36737, 92333], .contexts []⟩,
    ⟨[36737, 92335], [36737, 92335], .contexts []⟩,
    ⟨[92335, 7], [92335, 7], .contexts []⟩,
    ⟨[36736], [36736], .contexts []⟩,
    ⟨[92335, 7], [36739, 89079], .contexts [
        ⟨100766, false, false, [], []⟩,
        ⟨100765, true, false, [36736], [7]⟩,
        ⟨71403, true, false, [], [7]⟩,
        ⟨100764, true, false, [36736], [9, 7]⟩,
        ⟨100764, true, false, [36736], [9, 7]⟩,
        ⟨100763, true, false, [36736], [9, 7]⟩,
        ⟨100713, true, false, [36736], [9, 7]⟩,
        ⟨100710, true, false, [36736], [9, 7]⟩,
        ⟨579, false, false, [36736, 89081], []⟩,
        ⟨54194, false, false, [36736], []⟩,
        ⟨54193, false, false, [36736], []⟩,
        ⟨54195, false, false, [36736], []⟩,
        ⟨100767, true, false, [], [89079]⟩,
        ⟨100767, true, false, [], [89079]⟩,
        ⟨100714, true, false, [], [89079]⟩
      ]⟩,
    ⟨[36737], [36738], .contexts [
        ⟨100714, true, true, [], []⟩
      ]⟩,
    ⟨[36669, 96655], [36669, 96655], .contexts []⟩,
    ⟨[36669, 96655], [36669, 96655], .contexts []⟩,
    ⟨[96655, 1], [96657], .contexts [
        ⟨99146, false, false, [], []⟩
      ]⟩,
    ⟨[96655, 1], [96657], .contexts [
        ⟨100772, false, false, [], []⟩,
        ⟨99360, false, false, [], []⟩,
        ⟨99151, false, false, [], []⟩,
        ⟨99151, false, false, [], []⟩
      ]⟩,
    ⟨[96655, 0], [96655, 1], .contexts [
        ⟨9, false, false, [96655], []⟩
      ]⟩,
    ⟨[96657], [96657], .contexts []⟩,
    ⟨[36715, 92335], [36715, 92335], .contexts []⟩,
    ⟨[36715, 92335], [36715, 92335], .contexts []⟩,
    ⟨[85197, 5], [36715, 92335], .contexts [
        ⟨100745, false, false, [], []⟩,
        ⟨100748, false, false, [], []⟩,
        ⟨100776, false, false, [], []⟩,
        ⟨100777, false, false, [], []⟩,
        ⟨100777, false, false, [], []⟩
      ]⟩,
    ⟨[92335, 1], [92335, 1], .contexts []⟩,
    ⟨[92335, 1], [36717, 85193], .contexts [
        ⟨100779, false, false, [], []⟩,
        ⟨100778, true, false, [36714], [1]⟩,
        ⟨161, false, false, [36714, 85197], []⟩,
        ⟨162, false, false, [36714, 85197], []⟩,
        ⟨98383, false, false, [36714], [5]⟩,
        ⟨30525, false, false, [36714], []⟩,
        ⟨30526, false, false, [36714], []⟩,
        ⟨30420, false, false, [36714], []⟩,
        ⟨30420, false, false, [36714], []⟩,
        ⟨100024, false, false, [36714], []⟩,
        ⟨100682, true, false, [], [85193]⟩
      ]⟩,
    ⟨[36753], [36715, 36739], .source 18441⟩,
    ⟨[36755], [36753, 36339], .source 18442⟩,
    ⟨[36757], [36755, 32965], .source 18443⟩,
    ⟨[36757, 83883], [36757, 83883], .contexts []⟩,
    ⟨[36757, 83883, 7], [85197], .contexts [
        ⟨100784, true, false, [], [7]⟩,
        ⟨23327, true, false, [36757], [7]⟩,
        ⟨100783, false, false, [], [83885, 5, 7]⟩,
        ⟨89866, true, false, [36755], [5, 7]⟩,
        ⟨100782, false, false, [], [95353, 7, 5, 7]⟩,
        ⟨99965, true, false, [36753], [7, 5, 7]⟩,
        ⟨100781, false, false, [], [89079, 5, 7, 5, 7]⟩,
        ⟨100768, true, false, [36715], [5, 7, 5, 7]⟩,
        ⟨100778, true, false, [], [7, 5, 7, 5, 7]⟩,
        ⟨22319, false, false, [85197], []⟩
      ]⟩,
    ⟨[83883, 7], [83883, 7], .contexts []⟩,
    ⟨[36759], [36756], .source 18444⟩,
    ⟨[36756], [36756], .contexts []⟩,
    ⟨[83883, 7], [36759, 85197], .contexts [
        ⟨100786, false, false, [], []⟩,
        ⟨100785, false, false, [36756], []⟩,
        ⟨51809, false, false, [36756], []⟩,
        ⟨100788, true, false, [], [85197]⟩,
        ⟨100788, true, false, [], [85197]⟩,
        ⟨100787, true, false, [], [85197]⟩
      ]⟩,
    ⟨[92337, 5], [92337, 5], .contexts []⟩,
    ⟨[36761], [36717, 35841], .source 18445⟩,
    ⟨[92337, 5], [36761, 96345], .contexts [
        ⟨100790, false, false, [], []⟩,
        ⟨71407, true, false, [], [5]⟩,
        ⟨100778, true, false, [36714], [11, 5]⟩,
        ⟨940, false, false, [36714, 85197], []⟩,
        ⟨54, false, false, [36714, 85197], []⟩,
        ⟨98382, false, false, [36714], []⟩,
        ⟨98375, false, false, [36714, 35841], []⟩,
        ⟨100680, true, false, [], [35841, 96345]⟩,
        ⟨100791, true, false, [], [96345]⟩
      ]⟩,
    ⟨[36763], [36760], .source 18446⟩,
    ⟨[36763], [36763], .contexts []⟩,
    ⟨[96343], [36763, 92337], .contexts [
        ⟨97183, true, false, [], []⟩,
        ⟨97183, true, false, [], []⟩,
        ⟨97228, true, false, [], []⟩,
        ⟨97227, true, false, [], []⟩,
        ⟨100792, true, false, [36760], [5]⟩,
        ⟨28, false, false, [36760, 92337], []⟩,
        ⟨100793, true, false, [], [92337]⟩,
        ⟨100794, true, false, [], [92337]⟩
      ]⟩,
    ⟨[36761], [36762], .contexts [
        ⟨100793, true, true, [], []⟩
      ]⟩,
    ⟨[36762], [36762], .contexts []⟩,
    ⟨[92337, 3], [36761, 96341], .contexts [
        ⟨100795, true, false, [36762], [3]⟩,
        ⟨97181, false, false, [36762], []⟩,
        ⟨97229, false, false, [36762], []⟩,
        ⟨100797, true, false, [], [96341]⟩,
        ⟨100797, true, false, [], [96341]⟩,
        ⟨100796, true, false, [], [96341]⟩
      ]⟩,
    ⟨[36745, 89279], [36745, 89279], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1575. -/
def y322TCIndexRaw1575 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[92335, 15], [36745, 89279], .contexts [
        ⟨100751, false, false, [], []⟩,
        ⟨100753, false, false, [], []⟩,
        ⟨100799, false, false, [], []⟩,
        ⟨100799, false, false, [], []⟩
      ]⟩,
    ⟨[36717, 85193], [36717, 85193], .contexts []⟩,
    ⟨[36717, 85193], [36717, 85193], .contexts []⟩,
    ⟨[92335, 1], [36717, 85193], .contexts [
        ⟨100779, false, false, [], []⟩,
        ⟨100780, false, false, [], []⟩,
        ⟨100801, false, false, [], []⟩,
        ⟨100802, false, false, [], []⟩,
        ⟨100802, false, false, [], []⟩
      ]⟩,
    ⟨[92335, 0], [92335, 1], .contexts [
        ⟨9, false, false, [92335], []⟩
      ]⟩,
    ⟨[89277, 15], [89277, 15], .contexts []⟩,
    ⟨[36765], [36747, 36717], .source 18447⟩,
    ⟨[89277, 15], [36765, 85193], .contexts [
        ⟨100805, false, false, [], []⟩,
        ⟨55071, true, false, [], [15]⟩,
        ⟨100800, true, false, [36744], [1, 15]⟩,
        ⟨1666, false, false, [36744, 92335], []⟩,
        ⟨100804, false, false, [36744], []⟩,
        ⟨100803, false, false, [36744], []⟩,
        ⟨100024, false, false, [36744, 36717], []⟩,
        ⟨100754, true, false, [], [36717, 85193]⟩,
        ⟨100806, true, false, [], [85193]⟩
      ]⟩,
    ⟨[36767], [36764], .source 18448⟩,
    ⟨[36461, 93771], [36461, 93771], .contexts []⟩,
    ⟨[36769], [36459, 36767], .source 18449⟩,
    ⟨[93771], [36769, 89277], .contexts [
        ⟨100809, true, false, [36460], []⟩,
        ⟨100809, true, false, [36460], []⟩,
        ⟨100216, true, false, [36460], []⟩,
        ⟨100807, true, false, [36460, 36764], [15]⟩,
        ⟨1, false, false, [36460, 36764, 89277], []⟩,
        ⟨100808, true, false, [36460], [89277]⟩,
        ⟨100215, false, true, [], [36767, 89277]⟩,
        ⟨100810, true, false, [], [89277]⟩
      ]⟩,
    ⟨[36771], [36768], .source 18450⟩,
    ⟨[36771], [36768], .contexts [
        ⟨100812, false, false, [], []⟩
      ]⟩,
    ⟨[36768], [36768], .contexts []⟩,
    ⟨[36771], [36768], .contexts [
        ⟨100813, false, false, [], []⟩,
        ⟨100814, false, false, [], []⟩
      ]⟩,
    ⟨[36773], [36771, 30735], .source 18451⟩,
    ⟨[89277, 13], [36773, 85907], .contexts [
        ⟨100811, true, false, [36768], [13]⟩,
        ⟨80891, false, false, [36768], []⟩,
        ⟨81437, false, false, [36768], []⟩,
        ⟨100815, true, false, [], [30735, 85907]⟩,
        ⟨100816, true, false, [], [85907]⟩
      ]⟩,
    ⟨[93771], [36769, 89277], .contexts [
        ⟨100811, false, false, [], []⟩
      ]⟩,
    ⟨[93771], [36769, 89277], .contexts [
        ⟨100818, false, false, [], []⟩
      ]⟩,
    ⟨[36769, 89279], [36769, 89279], .contexts []⟩,
    ⟨[36769], [36770], .contexts [
        ⟨100812, true, true, [], []⟩
      ]⟩,
    ⟨[93769], [36769, 89279], .contexts [
        ⟨100813, false, false, [36770], [93769]⟩,
        ⟨13, false, false, [36770, 36768], [93769]⟩,
        ⟨80985, true, false, [36770, 36768], []⟩,
        ⟨80889, true, false, [36770, 36768], []⟩,
        ⟨100819, false, false, [36770, 36768], [1]⟩,
        ⟨55069, false, false, [36770], []⟩,
        ⟨100820, false, false, [36770, 36768], []⟩,
        ⟨100821, true, false, [], [89279]⟩
      ]⟩,
    ⟨[89279, 11], [36771, 93767], .contexts [
        ⟨100822, true, false, [36768], [11]⟩,
        ⟨80886, false, false, [36768], []⟩,
        ⟨80986, false, false, [36768], []⟩,
        ⟨100814, true, false, [], [93767]⟩,
        ⟨100815, true, false, [], [93767]⟩
      ]⟩,
    ⟨[36775], [36745, 36771], .source 18452⟩,
    ⟨[92335, 11], [92337], .contexts [
        ⟨71407, false, false, [], []⟩,
        ⟨71534, false, false, [], []⟩,
        ⟨71412, false, false, [], []⟩,
        ⟨71412, false, false, [], []⟩
      ]⟩,
    ⟨[92335, 10], [92335, 11], .contexts [
        ⟨54, false, false, [92335], []⟩
      ]⟩,
    ⟨[92337], [92337], .contexts []⟩,
    ⟨[36777], [36774], .source 18453⟩,
    ⟨[36774], [36774], .contexts []⟩,
    ⟨[93767, 15], [36777, 92337], .contexts [
        ⟨100824, false, false, [36774], [93767, 15]⟩,
        ⟨100823, true, false, [36774, 36745], [15]⟩,
        ⟨100800, true, false, [36774], [11, 15]⟩,
        ⟨2046, false, false, [36774, 92335], []⟩,
        ⟨100826, false, false, [36774], []⟩,
        ⟨100825, false, false, [36774], []⟩,
        ⟨100827, false, false, [36774], []⟩,
        ⟨100829, true, false, [], [92337]⟩,
        ⟨100829, true, false, [], [92337]⟩,
        ⟨100828, true, false, [], [92337]⟩
      ]⟩,
    ⟨[92337, 15], [36775, 93767], .contexts [
        ⟨100830, true, false, [36776], [15]⟩,
        ⟨1, false, false, [36776, 93767], []⟩,
        ⟨100828, false, true, [], [93767]⟩
      ]⟩,
    ⟨[36739, 89079], [36739, 89079], .contexts []⟩,
    ⟨[92335, 7], [36739, 89079], .contexts [
        ⟨100766, false, false, [], []⟩,
        ⟨100768, false, false, [], []⟩,
        ⟨100832, false, false, [], []⟩,
        ⟨100832, false, false, [], []⟩
      ]⟩,
    ⟨[36737], [36738], .contexts [
        ⟨100769, false, false, [], []⟩
      ]⟩,
    ⟨[36779], [36737, 36717], .source 18454⟩,
    ⟨[89077, 7], [36779, 85193], .contexts [
        ⟨53897, true, false, [], [7]⟩,
        ⟨100833, true, false, [36738], [1, 7]⟩,
        ⟨502, false, false, [36738, 92335], []⟩,
        ⟨100804, false, false, [36738], []⟩,
        ⟨100803, false, false, [36738], []⟩,
        ⟨100024, false, false, [36738, 36717], []⟩,
        ⟨100834, true, false, [], [36717, 85193]⟩,
        ⟨100835, true, false, [], [85193]⟩
      ]⟩,
    ⟨[36781], [36778], .source 18455⟩,
    ⟨[36739, 96761], [36739, 96761], .contexts []⟩,
    ⟨[36739, 96761], [36739, 96761], .contexts []⟩,
    ⟨[36738], [36738], .contexts []⟩,
    ⟨[96761, 7], [36737, 92337], .contexts [
        ⟨100839, true, false, [36738], [7]⟩,
        ⟨100838, true, false, [36738], [7]⟩,
        ⟨100129, true, false, [], [7]⟩,
        ⟨100833, true, false, [36738], [11, 7]⟩,
        ⟨555, false, false, [36738, 92335], []⟩,
        ⟨100826, false, false, [36738], []⟩,
        ⟨100825, false, false, [36738], []⟩,
        ⟨100827, false, false, [36738], []⟩,
        ⟨100840, true, false, [], [92337]⟩,
        ⟨100840, true, false, [], [92337]⟩,
        ⟨100834, true, false, [], [92337]⟩
      ]⟩,
    ⟨[92337, 7], [36739, 96761], .contexts [
        ⟨100841, true, false, [36736], [7]⟩,
        ⟨38, false, false, [36736, 96761], []⟩,
        ⟨100714, true, false, [], [96761]⟩
      ]⟩,
    ⟨[96661], [96661], .contexts []⟩,
    ⟨[92337, 1], [92339], .contexts [
        ⟨71411, false, false, [], []⟩
      ]⟩,
    ⟨[85193, 11], [85193, 11], .contexts []⟩,
    ⟨[92339], [92339], .contexts []⟩,
    ⟨[85193, 11], [36715, 92339], .contexts [
        ⟨100845, false, false, [], []⟩,
        ⟨100803, true, false, [36716], [11]⟩,
        ⟨110, false, false, [36716, 92335], []⟩,
        ⟨111, false, false, [36716, 92335], []⟩,
        ⟨100825, false, false, [36716], [1]⟩,
        ⟨100844, false, false, [36716], []⟩,
        ⟨71533, false, false, [36716], []⟩,
        ⟨71416, false, false, [36716], []⟩,
        ⟨71416, false, false, [36716], []⟩,
        ⟨100846, false, false, [36716], []⟩,
        ⟨100747, true, false, [], [92339]⟩
      ]⟩,
    ⟨[36759, 85197], [36759, 85197], .contexts []⟩,
    ⟨[36783], [36759, 23147], .source 18456⟩,
    ⟨[85807, 7], [85807, 7], .contexts []⟩,
    ⟨[36785], [36782], .source 18457⟩,
    ⟨[36782], [36782], .contexts []⟩,
    ⟨[85807, 7], [36785, 83881], .contexts [
        ⟨100850, false, false, [], []⟩,
        ⟨100849, false, false, [36782], [85807, 7]⟩,
        ⟨51811, true, false, [36782, 36759], [7]⟩,
        ⟨100848, true, false, [36782], [3, 7]⟩,
        ⟨100848, true, false, [36782], [3, 7]⟩,
        ⟨100789, true, false, [36782], [3, 7]⟩,
        ⟨100786, true, false, [36782], [3, 7]⟩,
        ⟨14911, false, false, [36782, 83883], []⟩,
        ⟨82006, false, false, [36782], []⟩,
        ⟨82005, false, false, [36782], []⟩,
        ⟨82008, false, false, [36782], []⟩,
        ⟨100852, true, false, [], [83881]⟩,
        ⟨100852, true, false, [], [83881]⟩,
        ⟨100851, true, false, [], [83881]⟩
      ]⟩,
    ⟨[36783], [36784], .contexts [
        ⟨100851, true, true, [], []⟩
      ]⟩,
    ⟨[83881, 7], [36783, 85807], .contexts [
        ⟨100853, true, false, [36784], [7]⟩,
        ⟨38, false, false, [36784, 85807], []⟩,
        ⟨100854, true, false, [], [85807]⟩
      ]⟩,
    ⟨[36761, 96345], [36761, 96345], .contexts []⟩,
    ⟨[36761, 96345], [36761, 96345], .contexts []⟩,
    ⟨[92337, 1], [92339], .contexts [
        ⟨100844, false, false, [], []⟩,
        ⟨71533, false, false, [], []⟩,
        ⟨71416, false, false, [], []⟩,
        ⟨71416, false, false, [], []⟩
      ]⟩,
    ⟨[36763], [36760], .contexts [
        ⟨100794, false, false, [], []⟩,
        ⟨100793, false, false, [], []⟩
      ]⟩,
    ⟨[36760], [36760], .contexts []⟩,
    ⟨[96347, 5], [36763, 92339], .contexts [
        ⟨97186, true, false, [], [5]⟩,
        ⟨100857, true, false, [36760], [1, 5]⟩,
        ⟨100857, true, false, [36760], [1, 5]⟩,
        ⟨100856, true, false, [36760], [1, 5]⟩,
        ⟨100792, true, false, [36760], [1, 5]⟩,
        ⟨100790, true, false, [36760], [1, 5]⟩,
        ⟨890, false, false, [36760, 92337], []⟩,
        ⟨9, false, false, [36760, 92337], []⟩,
        ⟨100858, false, false, [36760], []⟩,
        ⟨100846, false, false, [36760], []⟩,
        ⟨100860, true, false, [], [92339]⟩,
        ⟨100860, true, false, [], [92339]⟩,
        ⟨100859, true, false, [], [92339]⟩
      ]⟩,
    ⟨[92337, 7], [36739, 96761], .contexts [
        ⟨100842, false, false, [], []⟩,
        ⟨100838, false, false, [], []⟩,
        ⟨100839, false, false, [], []⟩,
        ⟨100839, false, false, [], []⟩
      ]⟩,
    ⟨[36739, 96759], [36739, 96759], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1576. -/
def y322TCIndexRaw1576 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[36739, 96759], [36739, 96759], .contexts []⟩,
    ⟨[92339, 7], [92339, 7], .contexts []⟩,
    ⟨[96759], [96759], .contexts []⟩,
    ⟨[92339, 7], [36739, 96759], .contexts [
        ⟨100865, false, false, [], []⟩,
        ⟨100858, true, false, [], [7]⟩,
        ⟨104, false, false, [92337], []⟩,
        ⟨105, false, false, [92337], []⟩,
        ⟨100862, false, false, [], [1]⟩,
        ⟨100115, false, false, [36739], []⟩,
        ⟨100863, false, false, [], []⟩,
        ⟨100864, false, false, [], []⟩,
        ⟨100866, false, false, [36739], []⟩,
        ⟨13, true, false, [], [36739, 96759]⟩
      ]⟩,
    ⟨[96759, 7], [36737, 92339], .contexts [
        ⟨100867, true, false, [36738], [7]⟩,
        ⟨38, false, false, [36738, 92339], []⟩,
        ⟨100769, true, false, [], [92339]⟩
      ]⟩,
    ⟨[36761, 96341], [36761, 96341], .contexts []⟩,
    ⟨[36787], [36739, 36431], .source 18458⟩,
    ⟨[96341, 7], [96341, 7], .contexts []⟩,
    ⟨[36789], [36763, 36787], .source 18459⟩,
    ⟨[96341, 7], [36789, 86655], .contexts [
        ⟨100871, false, false, [], []⟩,
        ⟨100869, true, false, [36760], [7]⟩,
        ⟨100869, true, false, [36760], [7]⟩,
        ⟨100798, true, false, [36760], [7]⟩,
        ⟨140, false, false, [36760, 92337], []⟩,
        ⟨141, false, false, [36760, 92337], []⟩,
        ⟨100862, false, false, [36760], [3]⟩,
        ⟨100137, false, false, [36760, 36739], []⟩,
        ⟨100870, true, false, [36760], [86655]⟩,
        ⟨100859, true, false, [], [36787, 86655]⟩,
        ⟨100872, true, false, [], [86655]⟩
      ]⟩,
    ⟨[36791], [36788], .source 18460⟩,
    ⟨[86655, 7], [36791, 96341], .contexts [
        ⟨100873, true, false, [36788], [7]⟩,
        ⟨38, false, false, [36788, 96341], []⟩,
        ⟨100874, true, false, [], [96341]⟩
      ]⟩,
    ⟨[36765, 85193], [36765, 85193], .contexts []⟩,
    ⟨[36765, 85193], [36765, 85193], .contexts []⟩,
    ⟨[36765, 85195], [36765, 85195], .contexts []⟩,
    ⟨[36765, 85195], [36765, 85195], .contexts []⟩,
    ⟨[36764], [36764], .contexts []⟩,
    ⟨[85195, 15], [36767, 89275], .contexts [
        ⟨100879, true, false, [36764], [15]⟩,
        ⟨100878, true, false, [36764], [15]⟩,
        ⟨30419, true, false, [], [15]⟩,
        ⟨100877, true, false, [36764], [5, 15]⟩,
        ⟨100877, true, false, [36764], [5, 15]⟩,
        ⟨100876, true, false, [36764], [5, 15]⟩,
        ⟨100807, true, false, [36764], [5, 15]⟩,
        ⟨100805, true, false, [36764], [5, 15]⟩,
        ⟨2072, false, false, [36764, 89277], []⟩,
        ⟨29, false, false, [36764, 89277], []⟩,
        ⟨55154, false, false, [36764], []⟩,
        ⟨55155, false, false, [36764], []⟩,
        ⟨55066, false, false, [36764], []⟩,
        ⟨55066, false, false, [36764], []⟩,
        ⟨100203, false, false, [36764], []⟩,
        ⟨100880, true, false, [], [89275]⟩,
        ⟨100880, true, false, [], [89275]⟩,
        ⟨100808, true, false, [], [89275]⟩
      ]⟩,
    ⟨[31529, 94535], [31529, 94535], .contexts []⟩,
    ⟨[36773, 85907], [36773, 85907], .contexts []⟩,
    ⟨[36773, 85907], [36773, 85907], .contexts []⟩,
    ⟨[89277, 13], [36773, 85907], .contexts [
        ⟨100817, false, false, [], []⟩,
        ⟨100883, false, false, [], []⟩,
        ⟨100884, false, false, [], []⟩,
        ⟨100884, false, false, [], []⟩
      ]⟩,
    ⟨[94533, 13], [94533, 13], .contexts []⟩,
    ⟨[36793], [31531, 36773], .source 18461⟩,
    ⟨[94533, 13], [36793, 85909], .contexts [
        ⟨100886, false, false, [], []⟩,
        ⟨84817, true, false, [], [13]⟩,
        ⟨100882, true, false, [31528], [1, 13]⟩,
        ⟨100882, true, false, [31528], [1, 13]⟩,
        ⟨85134, true, false, [31528], [1, 13]⟩,
        ⟨55074, true, false, [31528], [13, 1, 13]⟩,
        ⟨55074, true, false, [31528], [13, 1, 13]⟩,
        ⟨55151, true, false, [31528], [13, 1, 13]⟩,
        ⟨55069, true, false, [31528], [13, 1, 13]⟩,
        ⟨919, false, false, [31528, 89277], []⟩,
        ⟨116, false, false, [31528, 89277], []⟩,
        ⟨100885, false, false, [31528], [1]⟩,
        ⟨34178, false, false, [31528, 36773], []⟩,
        ⟨81431, false, false, [31528, 36773], []⟩,
        ⟨85131, true, false, [], [36773, 85909]⟩,
        ⟨100887, true, false, [], [85909]⟩
      ]⟩,
    ⟨[36795], [36792], .source 18462⟩,
    ⟨[33051, 84503], [33051, 84503], .contexts []⟩,
    ⟨[33051, 84503], [33051, 84503], .contexts []⟩,
    ⟨[36797], [36773, 36501], .source 18463⟩,
    ⟨[84503, 13], [84503, 13], .contexts []⟩,
    ⟨[36799], [33049, 36797], .source 18464⟩,
    ⟨[84503, 13], [36799, 84993], .contexts [
        ⟨100893, false, false, [], []⟩,
        ⟨100891, true, false, [33050], [13]⟩,
        ⟨100891, true, false, [33050], [13]⟩,
        ⟨100890, true, false, [33050], [13]⟩,
        ⟨90106, true, false, [33050], [13]⟩,
        ⟨201, false, false, [33050, 89277], []⟩,
        ⟨202, false, false, [33050, 89277], []⟩,
        ⟨100885, false, false, [33050], [9]⟩,
        ⟨100295, false, false, [33050, 36773], []⟩,
        ⟨100892, true, false, [33050], [84993]⟩,
        ⟨100293, false, false, [33050, 36797], []⟩,
        ⟨90252, true, false, [], [36797, 84993]⟩,
        ⟨100894, true, false, [], [84993]⟩
      ]⟩,
    ⟨[36801], [36798], .source 18465⟩,
    ⟨[84993, 13], [36801, 84503], .contexts [
        ⟨100895, true, false, [36798], [13]⟩,
        ⟨59, false, false, [36798, 84503], []⟩,
        ⟨100896, true, false, [], [84503]⟩
      ]⟩,
    ⟨[36715, 92339], [36715, 92339], .contexts []⟩,
    ⟨[85193, 13], [36393, 83883], .contexts [
        ⟨100028, false, false, [], []⟩,
        ⟨100021, false, false, [], []⟩,
        ⟨100022, false, false, [], []⟩,
        ⟨100022, false, false, [], []⟩
      ]⟩,
    ⟨[92341, 11], [92341, 11], .contexts []⟩,
    ⟨[83883], [83883], .contexts []⟩,
    ⟨[36803], [36717, 36393], .source 18466⟩,
    ⟨[92341, 11], [36803, 83883], .contexts [
        ⟨100900, false, false, [], []⟩,
        ⟨71415, true, false, [], [11]⟩,
        ⟨100898, true, false, [36714], [13, 11]⟩,
        ⟨100898, true, false, [36714], [13, 11]⟩,
        ⟨100847, true, false, [36714], [13, 11]⟩,
        ⟨100845, true, false, [36714], [13, 11]⟩,
        ⟨619, false, false, [36714, 85193], []⟩,
        ⟨64, false, false, [36714, 85193], []⟩,
        ⟨100899, false, false, [36714], []⟩,
        ⟨100901, false, false, [36714, 36393], []⟩,
        ⟨100680, true, false, [], [36393, 83883]⟩,
        ⟨100902, true, false, [], [83883]⟩
      ]⟩,
    ⟨[36805], [36802], .source 18467⟩,
    ⟨[83883, 11], [36805, 92341], .contexts [
        ⟨100903, true, false, [36802], [11]⟩,
        ⟨53, false, false, [36802, 92341], []⟩,
        ⟨100904, true, false, [], [92341]⟩
      ]⟩,
    ⟨[36785, 83881], [36785, 83881], .contexts []⟩,
    ⟨[36785, 83881], [36785, 83881], .contexts []⟩,
    ⟨[36785, 83879], [36785, 83879], .contexts []⟩,
    ⟨[85807, 1], [85805], .contexts [
        ⟨33601, false, false, [], []⟩,
        ⟨33602, false, false, [], []⟩,
        ⟨33493, false, false, [], []⟩,
        ⟨33493, false, false, [], []⟩
      ]⟩,
    ⟨[85807, 0], [85807, 1], .contexts [
        ⟨9, false, false, [85807], []⟩
      ]⟩,
    ⟨[36784], [36784], .contexts []⟩,
    ⟨[83879, 7], [36783, 85805], .contexts [
        ⟨100908, true, false, [36784], [7]⟩,
        ⟨23319, true, false, [], [7]⟩,
        ⟨100907, true, false, [36784], [1, 7]⟩,
        ⟨100907, true, false, [36784], [1, 7]⟩,
        ⟨100906, true, false, [36784], [1, 7]⟩,
        ⟨100853, true, false, [36784], [1, 7]⟩,
        ⟨100850, true, false, [36784], [1, 7]⟩,
        ⟨502, false, false, [36784, 85807], []⟩,
        ⟨100910, false, false, [36784], []⟩,
        ⟨100909, false, false, [36784], []⟩,
        ⟨44567, false, false, [36784], []⟩,
        ⟨100911, true, false, [], [85805]⟩,
        ⟨100911, true, false, [], [85805]⟩,
        ⟨100854, true, false, [], [85805]⟩
      ]⟩,
    ⟨[85805, 7], [36785, 83879], .contexts [
        ⟨100912, true, false, [36782], [7]⟩,
        ⟨38, false, false, [36782, 83879], []⟩,
        ⟨100851, true, false, [], [83879]⟩
      ]⟩,
    ⟨[36807], [36739, 36423], .source 18468⟩,
    ⟨[36809], [36806], .source 18469⟩,
    ⟨[36806], [36806], .contexts []⟩,
    ⟨[96345, 7], [36809, 92341], .contexts [
        ⟨100914, false, false, [36806], [96345, 7]⟩,
        ⟨100111, true, false, [36806, 36739], [7]⟩,
        ⟨100864, true, false, [36806], [13, 7]⟩,
        ⟨100864, true, false, [36806], [13, 7]⟩,
        ⟨100863, true, false, [36806], [13, 7]⟩,
        ⟨100867, true, false, [36806], [13, 7]⟩,
        ⟨100865, true, false, [36806], [13, 7]⟩,
        ⟨518, false, false, [36806, 92339], []⟩,
        ⟨64, false, false, [36806, 92339], []⟩,
        ⟨71415, false, false, [36806], []⟩,
        ⟨71532, false, false, [36806], []⟩,
        ⟨71419, false, false, [36806], []⟩,
        ⟨71419, false, false, [36806], []⟩,
        ⟨100916, true, false, [], [92341]⟩,
        ⟨100916, true, false, [], [92341]⟩,
        ⟨100915, true, false, [], [92341]⟩
      ]⟩,
    ⟨[36789, 86655], [36789, 86655], .contexts []⟩,
    ⟨[36789, 86653], [36789, 86653], .contexts []⟩,
    ⟨[36788], [36788], .contexts []⟩,
    ⟨[86653, 7], [36791, 96339], .contexts [
        ⟨100919, true, false, [36788], [7]⟩,
        ⟨38310, true, false, [], [7]⟩,
        ⟨100918, true, false, [36788], [1, 7]⟩,
        ⟨100918, true, false, [36788], [1, 7]⟩,
        ⟨100873, true, false, [36788], [1, 7]⟩,
        ⟨100871, true, false, [36788], [1, 7]⟩,
        ⟨502, false, false, [36788, 96341], []⟩,
        ⟨9, false, false, [36788, 96341], []⟩,
        ⟨97231, false, false, [36788], []⟩,
        ⟨97232, false, false, [36788], []⟩,
        ⟨97176, false, false, [36788], []⟩,
        ⟨97176, false, false, [36788], []⟩,
        ⟨100920, true, false, [], [96339]⟩,
        ⟨100920, true, false, [], [96339]⟩,
        ⟨100874, true, false, [], [96339]⟩
      ]⟩,
    ⟨[36793, 85909], [36793, 85909], .contexts []⟩,
    ⟨[94533, 13], [36793, 85909], .contexts [
        ⟨100886, false, false, [], []⟩,
        ⟨100888, false, false, [], []⟩,
        ⟨100922, false, false, [], []⟩,
        ⟨100922, false, false, [], []⟩
      ]⟩,
    ⟨[85909, 5], [85909, 5], .contexts []⟩,
    ⟨[90835], [90835], .contexts []⟩,
    ⟨[36811], [36795, 31549], .source 18470⟩,
    ⟨[85909, 5], [36811, 90835], .contexts [
        ⟨100924, false, false, [], []⟩,
        ⟨100923, true, false, [36792], [5]⟩,
        ⟨68, false, false, [36792, 94533], []⟩,
        ⟨69, false, false, [36792, 94533], []⟩,
        ⟨85180, false, false, [36792], [13]⟩,
        ⟨63033, false, false, [36792, 31549], []⟩,
        ⟨100925, false, false, [36792, 31549], []⟩,
        ⟨100889, true, false, [], [31549, 90835]⟩,
        ⟨100926, true, false, [], [90835]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1577. -/
def y322TCIndexRaw1577 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[36813], [36810], .source 18471⟩,
    ⟨[36815], [36793, 36515], .source 18472⟩,
    ⟨[33715, 95433], [33715, 95433], .contexts []⟩,
    ⟨[92291, 13], [92291, 13], .contexts []⟩,
    ⟨[36817], [36814], .source 18473⟩,
    ⟨[36819], [36817, 33715], .source 18474⟩,
    ⟨[92291, 13], [36819, 95433], .contexts [
        ⟨100931, false, false, [], []⟩,
        ⟨100929, false, false, [36814], [92291, 13]⟩,
        ⟨100330, true, false, [36814, 36793], [13]⟩,
        ⟨100923, true, false, [36814], [9, 13]⟩,
        ⟨942, false, false, [36814, 94533], []⟩,
        ⟨47, false, false, [36814, 94533], []⟩,
        ⟨91842, false, false, [36814], []⟩,
        ⟨100930, false, false, [36814], []⟩,
        ⟨100930, false, false, [36814], []⟩,
        ⟨91846, false, false, [36814, 33715], []⟩,
        ⟨100932, true, false, [], [33715, 95433]⟩,
        ⟨100933, true, false, [], [95433]⟩
      ]⟩,
    ⟨[36821], [36818], .source 18475⟩,
    ⟨[84503, 13], [36799, 84993], .contexts [
        ⟨100895, false, false, [], []⟩
      ]⟩,
    ⟨[36799, 84993], [36799, 84993], .contexts []⟩,
    ⟨[36799, 84993], [36799, 84993], .contexts []⟩,
    ⟨[84503, 13], [36799, 84993], .contexts [
        ⟨100893, false, false, [], []⟩,
        ⟨100936, false, false, [], []⟩,
        ⟨100937, false, false, [], []⟩,
        ⟨100938, false, false, [], []⟩,
        ⟨100938, false, false, [], []⟩
      ]⟩,
    ⟨[84503, 1], [84501], .contexts [
        ⟨27190, false, false, [], []⟩,
        ⟨27180, false, false, [], []⟩,
        ⟨27181, false, false, [], []⟩,
        ⟨27181, false, false, [], []⟩
      ]⟩,
    ⟨[84991, 13], [84991, 13], .contexts []⟩,
    ⟨[36801], [36798], .contexts [
        ⟨100896, false, false, [], []⟩
      ]⟩,
    ⟨[36823], [36801, 17269], .source 18476⟩,
    ⟨[84991, 13], [36823, 83589], .contexts [
        ⟨100941, false, false, [], []⟩,
        ⟨29679, true, false, [], [13]⟩,
        ⟨100939, true, false, [36798], [1, 13]⟩,
        ⟨1968, false, false, [36798, 84503], []⟩,
        ⟨248, false, false, [36798, 84503], []⟩,
        ⟨100940, false, false, [36798], [13, 1]⟩,
        ⟨27187, false, false, [36798], [1]⟩,
        ⟨27183, false, false, [36798], [1]⟩,
        ⟨27184, false, false, [36798], [1]⟩,
        ⟨27184, false, false, [36798], [1]⟩,
        ⟨22105, false, false, [36798, 17269], []⟩,
        ⟨58661, false, false, [36798, 17269], []⟩,
        ⟨100942, true, false, [], [17269, 83589]⟩,
        ⟨100943, true, false, [], [83589]⟩
      ]⟩,
    ⟨[36825], [36822], .source 18477⟩,
    ⟨[83589, 13], [36825, 84991], .contexts [
        ⟨100944, true, false, [36822], [13]⟩,
        ⟨59, false, false, [36822, 84991], []⟩,
        ⟨100945, true, false, [], [84991]⟩
      ]⟩,
    ⟨[36799, 84995], [36799, 84995], .contexts []⟩,
    ⟨[84503, 3], [84505], .contexts [
        ⟨40751, false, false, [], []⟩,
        ⟨27411, false, false, [], []⟩,
        ⟨27197, false, false, [], []⟩,
        ⟨27197, false, false, [], []⟩
      ]⟩,
    ⟨[84995, 13], [84995, 13], .contexts []⟩,
    ⟨[36798], [36798], .contexts []⟩,
    ⟨[84995, 13], [36801, 84505], .contexts [
        ⟨100949, false, false, [], []⟩,
        ⟨100947, true, false, [36798], [13]⟩,
        ⟨29681, true, false, [], [13]⟩,
        ⟨100939, true, false, [36798], [3, 13]⟩,
        ⟨1132, false, false, [36798, 84503], []⟩,
        ⟨21, false, false, [36798, 84503], []⟩,
        ⟨100948, false, false, [36798], []⟩,
        ⟨48404, false, false, [36798], []⟩,
        ⟨100950, true, false, [], [84505]⟩,
        ⟨100950, true, false, [], [84505]⟩,
        ⟨100942, true, false, [], [84505]⟩
      ]⟩,
    ⟨[36799], [36800], .contexts [
        ⟨100896, true, true, [], []⟩
      ]⟩,
    ⟨[84505, 13], [36799, 84995], .contexts [
        ⟨100951, true, false, [36800], [13]⟩,
        ⟨59, false, false, [36800, 84995], []⟩,
        ⟨100952, true, false, [], [84995]⟩
      ]⟩,
    ⟨[36827], [36799, 28923], .source 18478⟩,
    ⟨[84503, 11], [18275, 88095], .contexts [
        ⟨48395, false, false, [], []⟩
      ]⟩,
    ⟨[18275, 88095], [18275, 88095], .contexts []⟩,
    ⟨[36829], [36826], .source 18479⟩,
    ⟨[36831], [36829, 18275], .source 18480⟩,
    ⟨[36831], [36826, 18275], .contexts [
        ⟨100958, false, false, [], []⟩,
        ⟨100957, false, false, [], [18275]⟩
      ]⟩,
    ⟨[36833], [36830], .source 18481⟩,
    ⟨[36803, 83883], [36803, 83883], .contexts []⟩,
    ⟨[36803, 83883], [36803, 83883], .contexts []⟩,
    ⟨[93911], [36445, 85903], .contexts [
        ⟨100196, false, false, [], []⟩
      ]⟩,
    ⟨[93911], [36445, 85903], .contexts [
        ⟨100963, false, false, [], []⟩,
        ⟨100189, false, false, [], []⟩
      ]⟩,
    ⟨[36835], [30805, 36445], .source 18482⟩,
    ⟨[36837], [36803, 36835], .source 18483⟩,
    ⟨[85903, 11], [85903, 11], .contexts []⟩,
    ⟨[92343], [92343], .contexts []⟩,
    ⟨[36839], [36836], .source 18484⟩,
    ⟨[36839], [36839], .contexts []⟩,
    ⟨[36839], [36836], .contexts [
        ⟨100969, false, false, [], []⟩
      ]⟩,
    ⟨[36836], [36836], .contexts []⟩,
    ⟨[85903, 11], [36839, 92343], .contexts [
        ⟨100967, false, false, [], []⟩,
        ⟨100966, false, false, [36836], [85903, 11]⟩,
        ⟨100965, false, false, [36836, 36803], [85903, 11]⟩,
        ⟨100964, true, false, [36836, 36803, 30805], [11]⟩,
        ⟨82003, true, false, [36836, 36803], [11]⟩,
        ⟨100962, true, false, [36836], [15, 11]⟩,
        ⟨100962, true, false, [36836], [15, 11]⟩,
        ⟨100961, true, false, [36836], [15, 11]⟩,
        ⟨100903, true, false, [36836], [15, 11]⟩,
        ⟨100900, true, false, [36836], [15, 11]⟩,
        ⟨615, false, false, [36836, 92341], []⟩,
        ⟨10, false, false, [36836, 92341], []⟩,
        ⟨71418, false, false, [36836], []⟩,
        ⟨71530, false, false, [36836], []⟩,
        ⟨71423, false, false, [36836], []⟩,
        ⟨71423, false, false, [36836], []⟩,
        ⟨100968, false, false, [36836], []⟩,
        ⟨100972, true, false, [], [92343]⟩,
        ⟨100972, true, false, [], [92343]⟩,
        ⟨100971, true, false, [], [92343]⟩,
        ⟨100970, true, false, [], [92343]⟩
      ]⟩,
    ⟨[36837], [36838], .contexts [
        ⟨100969, true, true, [], []⟩
      ]⟩,
    ⟨[36811, 90835], [36811, 90835], .contexts []⟩,
    ⟨[36811, 90835], [36811, 90835], .contexts []⟩,
    ⟨[85909, 5], [36811, 90835], .contexts [
        ⟨100924, false, false, [], []⟩,
        ⟨100927, false, false, [], []⟩,
        ⟨100975, false, false, [], []⟩,
        ⟨100976, false, false, [], []⟩,
        ⟨100976, false, false, [], []⟩
      ]⟩,
    ⟨[36841], [36811, 29315], .source 18485⟩,
    ⟨[92927, 5], [92927, 5], .contexts []⟩,
    ⟨[85907], [85907], .contexts []⟩,
    ⟨[36843], [36840], .source 18486⟩,
    ⟨[36840], [36840], .contexts []⟩,
    ⟨[92927, 5], [36843, 85907], .contexts [
        ⟨100979, false, false, [], []⟩,
        ⟨100978, false, false, [36840], [92927, 5]⟩,
        ⟨76432, true, false, [36840, 36811], [5]⟩,
        ⟨100977, true, false, [36840], [1, 5]⟩,
        ⟨890, false, false, [36840, 85909], []⟩,
        ⟨9, false, false, [36840, 85909], []⟩,
        ⟨81432, false, false, [36840], []⟩,
        ⟨100980, false, false, [36840], []⟩,
        ⟨100982, true, false, [], [85907]⟩,
        ⟨100982, true, false, [], [85907]⟩,
        ⟨100981, true, false, [], [85907]⟩
      ]⟩,
    ⟨[36841], [36842], .contexts [
        ⟨100981, true, true, [], []⟩
      ]⟩,
    ⟨[36533, 83445], [36533, 83445], .contexts []⟩,
    ⟨[36533, 83445], [36533, 83445], .contexts []⟩,
    ⟨[36845], [36533, 22661], .source 18487⟩,
    ⟨[90835, 7], [90835, 7], .contexts []⟩,
    ⟨[90835, 7], [36810, 36845, 88313], .contexts [
        ⟨100988, false, false, [], []⟩,
        ⟨100977, true, false, [36810], [7]⟩,
        ⟨3272, false, false, [36810, 85909], []⟩,
        ⟨3275, false, false, [36810, 85909], []⟩,
        ⟨100349, false, false, [36810], [5, 7, 5]⟩,
        ⟨100352, false, false, [36810], [5, 7, 5]⟩,
        ⟨100985, false, false, [36810], [5, 7, 5]⟩,
        ⟨100986, false, false, [36810], [5, 7, 5]⟩,
        ⟨100986, false, false, [36810], [5, 7, 5]⟩,
        ⟨21223, false, false, [36810, 36533], [7, 5]⟩,
        ⟨49932, false, false, [36810, 36533], [5]⟩,
        ⟨100987, true, false, [36810], [88315, 5]⟩,
        ⟨49541, false, false, [36810, 36845], []⟩
      ]⟩,
    ⟨[36813], [36810], .contexts [
        ⟨100928, false, false, [], []⟩
      ]⟩,
    ⟨[36847], [36813, 36845], .source 18488⟩]

/-- Exact literal claimed equations and contextual derivations, block 1578. -/
def y322TCIndexRaw1578 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90835, 7], [36847, 88313], .contexts [
        ⟨100989, false, false, [], []⟩,
        ⟨100990, true, false, [], [36845, 88313]⟩,
        ⟨100991, true, false, [], [88313]⟩
      ]⟩,
    ⟨[36849], [36846], .source 18489⟩,
    ⟨[90837, 5], [90837, 5], .contexts []⟩,
    ⟨[36851], [36813, 30733], .source 18490⟩,
    ⟨[90837, 5], [36851, 93777], .contexts [
        ⟨100994, false, false, [], []⟩,
        ⟨63037, true, false, [], [5]⟩,
        ⟨100977, true, false, [36810], [15, 5]⟩,
        ⟨1204, false, false, [36810, 85909], []⟩,
        ⟨10, false, false, [36810, 85909], []⟩,
        ⟨81429, false, false, [36810], []⟩,
        ⟨81421, false, false, [36810, 30733], []⟩,
        ⟨100990, true, false, [], [30733, 93777]⟩,
        ⟨100995, true, false, [], [93777]⟩
      ]⟩,
    ⟨[36853], [36850], .source 18491⟩,
    ⟨[36819, 95433], [36819, 95433], .contexts []⟩,
    ⟨[36819, 95433], [36819, 95433], .contexts []⟩,
    ⟨[36819, 95435], [36819, 95435], .contexts []⟩,
    ⟨[95435, 13], [95435, 13], .contexts []⟩,
    ⟨[36821], [36818], .contexts [
        ⟨100935, false, false, [], []⟩
      ]⟩,
    ⟨[36818], [36818], .contexts []⟩,
    ⟨[95435, 13], [36821, 92293], .contexts [
        ⟨101001, false, false, [], []⟩,
        ⟨101000, true, false, [36818], [13]⟩,
        ⟨91849, true, false, [], [13]⟩,
        ⟨100999, true, false, [36818], [3, 13]⟩,
        ⟨100999, true, false, [36818], [3, 13]⟩,
        ⟨100998, true, false, [36818], [3, 13]⟩,
        ⟨100934, true, false, [36818], [3, 13]⟩,
        ⟨100931, true, false, [36818], [3, 13]⟩,
        ⟨1132, false, false, [36818, 92291], []⟩,
        ⟨90367, false, false, [36818], []⟩,
        ⟨90366, false, false, [36818], []⟩,
        ⟨90369, false, false, [36818], []⟩,
        ⟨101003, true, false, [], [92293]⟩,
        ⟨101003, true, false, [], [92293]⟩,
        ⟨101002, true, false, [], [92293]⟩
      ]⟩,
    ⟨[36819], [36820], .contexts [
        ⟨100935, true, true, [], []⟩
      ]⟩,
    ⟨[36855], [36615, 36819], .source 18492⟩,
    ⟨[96649], [36855, 95435], .contexts [
        ⟨100566, true, false, [36616], []⟩,
        ⟨101004, true, false, [36616, 36820], [13]⟩,
        ⟨59, false, false, [36616, 36820, 95435], []⟩,
        ⟨101005, true, false, [36616], [95435]⟩,
        ⟨101000, false, false, [36616], []⟩,
        ⟨100506, true, false, [], [36819, 95435]⟩,
        ⟨101006, true, false, [], [95435]⟩
      ]⟩,
    ⟨[96649], [36855, 95435], .contexts [
        ⟨101007, false, false, [], []⟩
      ]⟩,
    ⟨[36855, 95435], [36855, 95435], .contexts []⟩,
    ⟨[36857], [36854], .source 18493⟩,
    ⟨[36857], [36854], .contexts [
        ⟨101010, false, false, [], []⟩
      ]⟩,
    ⟨[36854], [36854], .contexts []⟩,
    ⟨[95435, 15], [36857, 96651], .contexts [
        ⟨101007, true, false, [36854], [15]⟩,
        ⟨99127, false, false, [36854], []⟩,
        ⟨99129, false, false, [36854], []⟩,
        ⟨101012, true, false, [], [96651]⟩,
        ⟨101012, true, false, [], [96651]⟩,
        ⟨101011, true, false, [], [96651]⟩
      ]⟩,
    ⟨[36823, 83589], [36823, 83589], .contexts []⟩,
    ⟨[84991, 13], [36823, 83589], .contexts [
        ⟨100941, false, false, [], []⟩,
        ⟨100944, false, false, [], []⟩,
        ⟨101014, false, false, [], []⟩,
        ⟨101014, false, false, [], []⟩
      ]⟩,
    ⟨[84991, 3], [23459, 85289], .contexts [
        ⟨53598, true, false, [23460], [3]⟩,
        ⟨31026, false, false, [23460], []⟩,
        ⟨31129, false, false, [23460], []⟩,
        ⟨53599, true, false, [], [85289]⟩
      ]⟩,
    ⟨[23459, 85289], [23459, 85289], .contexts []⟩,
    ⟨[23459, 85289], [23459, 85289], .contexts []⟩,
    ⟨[83591, 13], [83591, 13], .contexts []⟩,
    ⟨[85289], [85289], .contexts []⟩,
    ⟨[36859], [36825, 23459], .source 18494⟩,
    ⟨[83591, 13], [36859, 85289], .contexts [
        ⟨101019, false, false, [], []⟩,
        ⟨22108, true, false, [], [13]⟩,
        ⟨101015, true, false, [36822], [3, 13]⟩,
        ⟨1132, false, false, [36822, 84991], []⟩,
        ⟨21, false, false, [36822, 84991], []⟩,
        ⟨101016, false, false, [36822], []⟩,
        ⟨101017, false, false, [36822], []⟩,
        ⟨101018, false, false, [36822], []⟩,
        ⟨101018, false, false, [36822], []⟩,
        ⟨101020, false, false, [36822, 23459], []⟩,
        ⟨100945, true, false, [], [23459, 85289]⟩,
        ⟨101021, true, false, [], [85289]⟩
      ]⟩,
    ⟨[36861], [36858], .source 18495⟩,
    ⟨[85289, 13], [36861, 83591], .contexts [
        ⟨101022, true, false, [36858], [13]⟩,
        ⟨59, false, false, [36858, 83591], []⟩,
        ⟨101023, true, false, [], [83591]⟩
      ]⟩,
    ⟨[36863], [36823, 23403], .source 18496⟩,
    ⟨[36865], [36863, 34809], .source 18497⟩,
    ⟨[94329, 5], [94329, 5], .contexts []⟩,
    ⟨[36867], [36864], .source 18498⟩,
    ⟨[36867], [36864], .contexts [
        ⟨101028, false, false, [], []⟩
      ]⟩,
    ⟨[36864], [36864], .contexts []⟩,
    ⟨[94329, 5], [36867, 84991], .contexts [
        ⟨101027, false, false, [], []⟩,
        ⟨101026, false, false, [36864], [94329, 5]⟩,
        ⟨95106, true, false, [36864, 36863], [5]⟩,
        ⟨101025, false, false, [36864], [89983, 13, 5]⟩,
        ⟨53401, false, false, [36864, 36823], [89983, 13, 5]⟩,
        ⟨28, true, false, [36864, 36823, 23400, 89983], [13, 5]⟩,
        ⟨58662, false, false, [36864, 36823, 23400], [5, 13, 5]⟩,
        ⟨101015, true, false, [36864], [5, 13, 5]⟩,
        ⟨1116, false, false, [36864, 84991], []⟩,
        ⟨75342, false, false, [36864], []⟩,
        ⟨101030, true, false, [], [84991]⟩,
        ⟨101030, true, false, [], [84991]⟩,
        ⟨101029, true, false, [], [84991]⟩
      ]⟩,
    ⟨[36865], [36866], .contexts [
        ⟨101028, true, true, [], []⟩
      ]⟩,
    ⟨[36801, 84505], [36801, 84505], .contexts []⟩,
    ⟨[36801, 84505], [36801, 84505], .contexts []⟩,
    ⟨[84995, 13], [36801, 84505], .contexts [
        ⟨100949, false, false, [], []⟩,
        ⟨100951, false, false, [], []⟩,
        ⟨101033, false, false, [], []⟩,
        ⟨101034, false, false, [], []⟩,
        ⟨101034, false, false, [], []⟩
      ]⟩,
    ⟨[36801, 84507], [36801, 84507], .contexts []⟩,
    ⟨[84995, 5], [84997], .contexts [
        ⟨29685, false, false, [], []⟩,
        ⟨29956, false, false, [], []⟩,
        ⟨29690, false, false, [], []⟩,
        ⟨29690, false, false, [], []⟩
      ]⟩,
    ⟨[84507, 13], [84507, 13], .contexts []⟩,
    ⟨[84997], [84997], .contexts []⟩,
    ⟨[36799], [36800], .contexts [
        ⟨100952, false, false, [], []⟩
      ]⟩,
    ⟨[36800], [36800], .contexts []⟩,
    ⟨[84507, 13], [36799, 84997], .contexts [
        ⟨101038, false, false, [], []⟩,
        ⟨101036, true, false, [36800], [13]⟩,
        ⟨27196, true, false, [], [13]⟩,
        ⟨101035, true, false, [36800], [5, 13]⟩,
        ⟨1136, false, false, [36800, 84995], []⟩,
        ⟨29, false, false, [36800, 84995], []⟩,
        ⟨101037, false, false, [36800], []⟩,
        ⟨101039, false, false, [36800], []⟩,
        ⟨101041, true, false, [], [84997]⟩,
        ⟨101041, true, false, [], [84997]⟩,
        ⟨101040, true, false, [], [84997]⟩
      ]⟩,
    ⟨[36869], [36801, 18275], .source 18499⟩,
    ⟨[84995, 11], [28923, 90507], .contexts [
        ⟨75437, false, false, [], []⟩,
        ⟨75433, false, false, [], []⟩,
        ⟨75434, false, false, [], []⟩,
        ⟨75434, false, false, [], []⟩
      ]⟩,
    ⟨[88097, 13], [88097, 13], .contexts []⟩,
    ⟨[36871], [36868], .source 18500⟩,
    ⟨[36873], [36871, 28923], .source 18501⟩,
    ⟨[88097, 13], [36873, 90507], .contexts [
        ⟨101045, false, false, [], []⟩,
        ⟨101043, false, false, [36868], [88097, 13]⟩,
        ⟨48406, true, false, [36868, 36801], [13]⟩,
        ⟨101035, true, false, [36868], [11, 13]⟩,
        ⟨931, false, false, [36868, 84995], []⟩,
        ⟨54, false, false, [36868, 84995], []⟩,
        ⟨101044, false, false, [36868], []⟩,
        ⟨101046, true, false, [], [28923, 90507]⟩,
        ⟨101047, true, false, [], [90507]⟩
      ]⟩,
    ⟨[36875], [36872], .source 18502⟩,
    ⟨[85903, 11], [36839, 92343], .contexts [
        ⟨100973, false, false, [], []⟩
      ]⟩,
    ⟨[85903, 11], [36839, 92343], .contexts [
        ⟨100967, false, false, [], []⟩,
        ⟨101050, false, false, [], []⟩
      ]⟩,
    ⟨[36839, 92343], [36839, 92343], .contexts []⟩,
    ⟨[36839, 92343], [36839, 92343], .contexts []⟩,
    ⟨[36839, 92345], [36839, 92345], .contexts []⟩,
    ⟨[36838], [36838], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1579. -/
def y322TCIndexRaw1579 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85899], [36839, 92345], .contexts [
        ⟨34163, true, false, [], []⟩,
        ⟨34163, true, false, [], []⟩,
        ⟨34359, true, false, [], []⟩,
        ⟨34358, true, false, [], []⟩,
        ⟨100974, false, false, [36836], [85901, 11]⟩,
        ⟨101055, false, false, [36836], [85901, 11]⟩,
        ⟨101055, false, false, [36836], [85901, 11]⟩,
        ⟨100180, true, false, [36836, 36838], [11]⟩,
        ⟨34167, true, false, [36836, 36838], [11]⟩,
        ⟨34167, true, false, [36836, 36838], [11]⟩,
        ⟨34357, true, false, [36836, 36838], [11]⟩,
        ⟨34356, true, false, [36836, 36838], [11]⟩,
        ⟨9, true, false, [36836, 36838, 85903], [11]⟩,
        ⟨567, true, false, [36836, 36838, 85903], [11]⟩,
        ⟨101051, false, false, [36836, 36838], [1, 11, 11]⟩,
        ⟨101052, false, false, [36836, 36838], [1, 11, 11]⟩,
        ⟨101053, false, false, [36836, 36838], [1, 11, 11]⟩,
        ⟨101053, false, false, [36836, 36838], [1, 11, 11]⟩,
        ⟨71422, false, false, [36836], [11, 11]⟩,
        ⟨101054, false, false, [36836, 36838], [11, 11]⟩,
        ⟨53, false, false, [36836, 92345], []⟩,
        ⟨100969, true, false, [], [92345]⟩,
        ⟨101054, false, false, [], []⟩
      ]⟩,
    ⟨[92345], [36837, 85899], .contexts [
        ⟨100970, false, false, [36838], [92345]⟩,
        ⟨101056, true, false, [36838], []⟩,
        ⟨100974, true, false, [], [85899]⟩
      ]⟩,
    ⟨[36839], [36836], .contexts [
        ⟨100971, false, false, [], []⟩,
        ⟨100972, false, false, [], []⟩,
        ⟨100972, false, false, [], []⟩
      ]⟩,
    ⟨[85899, 1], [36839, 92343], .contexts [
        ⟨101057, true, false, [36836], [1]⟩,
        ⟨71424, false, false, [36836], []⟩,
        ⟨71530, false, false, [36836], []⟩,
        ⟨101058, true, false, [], [92343]⟩
      ]⟩,
    ⟨[85899, 3], [36839, 92347], .contexts [
        ⟨101057, true, false, [36836], [3]⟩,
        ⟨71426, false, false, [36836], []⟩,
        ⟨71529, false, false, [36836], []⟩,
        ⟨101058, true, false, [], [92347]⟩
      ]⟩,
    ⟨[36843, 85907], [36843, 85907], .contexts []⟩,
    ⟨[36843, 85907], [36843, 85907], .contexts []⟩,
    ⟨[92927, 5], [36843, 85907], .contexts [
        ⟨100979, false, false, [], []⟩,
        ⟨100983, false, false, [], []⟩,
        ⟨101061, false, false, [], []⟩,
        ⟨101062, false, false, [], []⟩,
        ⟨101062, false, false, [], []⟩
      ]⟩,
    ⟨[36877], [30733, 36769], .source 18503⟩,
    ⟨[36879], [36843, 36877], .source 18504⟩,
    ⟨[89275, 13], [89275, 13], .contexts []⟩,
    ⟨[36881], [36878], .source 18505⟩,
    ⟨[36881], [36878], .contexts [
        ⟨101067, false, false, [], []⟩
      ]⟩,
    ⟨[36878], [36878], .contexts []⟩,
    ⟨[89275, 13], [36881, 92927], .contexts [
        ⟨101066, false, false, [], []⟩,
        ⟨55067, true, false, [], [13]⟩,
        ⟨101065, false, false, [36878], [89277, 5, 13]⟩,
        ⟨101064, false, false, [36878, 36843], [89277, 5, 13]⟩,
        ⟨100819, true, false, [36878, 36843, 30733], [5, 13]⟩,
        ⟨81436, true, false, [36878, 36843], [5, 13]⟩,
        ⟨101063, true, false, [36878], [13, 5, 13]⟩,
        ⟨4632, false, false, [36878, 92927], []⟩,
        ⟨76419, false, false, [36878], []⟩,
        ⟨101069, true, false, [], [92927]⟩,
        ⟨101069, true, false, [], [92927]⟩,
        ⟨101068, true, false, [], [92927]⟩
      ]⟩,
    ⟨[36879], [36880], .contexts [
        ⟨101067, true, true, [], []⟩
      ]⟩,
    ⟨[85905, 5], [85905, 5], .contexts []⟩,
    ⟨[36883], [36841, 29317], .source 18506⟩,
    ⟨[85905, 5], [36883, 90839], .contexts [
        ⟨101072, false, false, [], []⟩,
        ⟨34176, true, false, [], [5]⟩,
        ⟨101063, true, false, [36842], [15, 5]⟩,
        ⟨1204, false, false, [36842, 92927], []⟩,
        ⟨10, false, false, [36842, 92927], []⟩,
        ⟨76421, false, false, [36842], []⟩,
        ⟨76416, false, false, [36842], []⟩,
        ⟨76417, false, false, [36842], []⟩,
        ⟨76417, false, false, [36842], []⟩,
        ⟨76425, false, false, [36842, 29317], []⟩,
        ⟨100984, true, false, [], [29317, 90839]⟩,
        ⟨101073, true, false, [], [90839]⟩
      ]⟩,
    ⟨[36885], [36882], .source 18507⟩,
    ⟨[36847, 88313], [36847, 88313], .contexts []⟩,
    ⟨[36847, 88313], [36847, 88313], .contexts []⟩,
    ⟨[88313, 13], [88313, 13], .contexts []⟩,
    ⟨[36887], [36849, 36511], .source 18508⟩,
    ⟨[88313, 13], [36887, 93777], .contexts [
        ⟨101078, false, false, [], []⟩,
        ⟨101077, true, false, [36846], [13]⟩,
        ⟨101077, true, false, [36846], [13]⟩,
        ⟨101076, true, false, [36846], [13]⟩,
        ⟨100992, true, false, [36846], [13]⟩,
        ⟨100988, true, false, [36846], [13]⟩,
        ⟨1056, false, false, [36846, 90835], []⟩,
        ⟨1057, false, false, [36846, 90835], []⟩,
        ⟨68663, false, false, [36846], [7]⟩,
        ⟨100340, false, false, [36846], []⟩,
        ⟨100341, false, false, [36846], []⟩,
        ⟨100342, false, false, [36846], []⟩,
        ⟨100342, false, false, [36846], []⟩,
        ⟨81421, false, false, [36846, 36511], []⟩,
        ⟨100993, true, false, [], [36511, 93777]⟩,
        ⟨101079, true, false, [], [93777]⟩
      ]⟩,
    ⟨[36889], [36886], .source 18509⟩,
    ⟨[93777, 13], [36889, 88313], .contexts [
        ⟨101080, true, false, [36886], [13]⟩,
        ⟨59, false, false, [36886, 88313], []⟩,
        ⟨101081, true, false, [], [88313]⟩
      ]⟩,
    ⟨[36851, 93777], [36851, 93777], .contexts []⟩,
    ⟨[36891], [36851, 36889], .source 18510⟩,
    ⟨[36891, 88315], [36891, 88315], .contexts []⟩,
    ⟨[36893], [36890], .source 18511⟩,
    ⟨[36890], [36890], .contexts []⟩,
    ⟨[88315, 13], [36893, 90837], .contexts [
        ⟨101085, true, false, [36890], [13]⟩,
        ⟨49539, true, false, [], [13]⟩,
        ⟨101084, false, false, [36890], [88313, 5, 13]⟩,
        ⟨101082, true, false, [36890, 36851], [5, 13]⟩,
        ⟨101083, true, false, [36890], [13, 5, 13]⟩,
        ⟨101083, true, false, [36890], [13, 5, 13]⟩,
        ⟨100996, true, false, [36890], [13, 5, 13]⟩,
        ⟨100994, true, false, [36890], [13, 5, 13]⟩,
        ⟨4632, false, false, [36890, 90837], []⟩,
        ⟨68640, false, false, [36890], []⟩,
        ⟨101087, true, false, [], [90837]⟩,
        ⟨101087, true, false, [], [90837]⟩,
        ⟨101086, true, false, [], [90837]⟩
      ]⟩,
    ⟨[29315, 92921], [29315, 92921], .contexts []⟩,
    ⟨[36895], [29317, 36891], .source 18512⟩,
    ⟨[92921], [36895, 88315], .contexts [
        ⟨101089, true, false, [29314], []⟩,
        ⟨101089, true, false, [29314], []⟩,
        ⟨76431, true, false, [29314], []⟩,
        ⟨101088, true, false, [29314, 36892], [13]⟩,
        ⟨59, false, false, [29314, 36892, 88315], []⟩,
        ⟨101086, false, true, [29314], [88315]⟩,
        ⟨101085, false, false, [29314], []⟩,
        ⟨76307, true, false, [], [36891, 88315]⟩,
        ⟨101090, true, false, [], [88315]⟩
      ]⟩,
    ⟨[36897], [36894], .source 18513⟩,
    ⟨[36897], [36894], .contexts [
        ⟨101092, false, false, [], []⟩
      ]⟩,
    ⟨[36895], [36896], .contexts [
        ⟨101092, true, true, [], []⟩
      ]⟩,
    ⟨[36894], [36894], .contexts []⟩,
    ⟨[88317, 11], [36897, 92917], .contexts [
        ⟨101094, false, false, [36894], [88317, 11]⟩,
        ⟨49543, true, false, [36894, 36896], [11]⟩,
        ⟨101091, true, false, [36894, 36896, 36894], [1, 11]⟩,
        ⟨75907, false, false, [36894, 36896, 36894], [11]⟩,
        ⟨76006, false, false, [36894, 36896, 36894], [11]⟩,
        ⟨13, true, false, [36894, 36896, 36894], [92919, 11]⟩,
        ⟨101093, true, false, [36894, 36896], [92919, 11]⟩,
        ⟨75904, false, false, [36894], []⟩,
        ⟨76007, false, false, [36894], []⟩,
        ⟨101095, true, false, [], [92917]⟩,
        ⟨101095, true, false, [], [92917]⟩,
        ⟨101093, true, false, [], [92917]⟩
      ]⟩,
    ⟨[36821, 92293], [36821, 92293], .contexts []⟩,
    ⟨[36821, 92293], [36821, 92293], .contexts []⟩,
    ⟨[36821, 92295], [36821, 92295], .contexts []⟩,
    ⟨[92295, 13], [92295, 13], .contexts []⟩,
    ⟨[36820], [36820], .contexts []⟩,
    ⟨[92295, 13], [36819, 95437], .contexts [
        ⟨101100, false, false, [], []⟩,
        ⟨101099, true, false, [36820], [13]⟩,
        ⟨71334, true, false, [], [13]⟩,
        ⟨101098, true, false, [36820], [5, 13]⟩,
        ⟨101098, true, false, [36820], [5, 13]⟩,
        ⟨101097, true, false, [36820], [5, 13]⟩,
        ⟨101004, true, false, [36820], [5, 13]⟩,
        ⟨101001, true, false, [36820], [5, 13]⟩,
        ⟨1136, false, false, [36820, 95435], []⟩,
        ⟨29, false, false, [36820, 95435], []⟩,
        ⟨91874, false, false, [36820], []⟩,
        ⟨91877, false, false, [36820], []⟩,
        ⟨101101, true, false, [], [95437]⟩,
        ⟨101101, true, false, [], [95437]⟩,
        ⟨101005, true, false, [], [95437]⟩
      ]⟩,
    ⟨[36857, 96651], [36857, 96651], .contexts []⟩,
    ⟨[36857, 96651], [36857, 96651], .contexts []⟩,
    ⟨[36857, 96653], [36857, 96653], .contexts []⟩,
    ⟨[36857, 96653], [36857, 96653], .contexts []⟩,
    ⟨[95433, 15], [95433, 15], .contexts []⟩,
    ⟨[95433, 15], [36857, 96653], .contexts [
        ⟨101107, false, false, [], []⟩,
        ⟨91832, true, false, [], [15]⟩,
        ⟨91832, true, false, [], [15]⟩,
        ⟨91831, true, false, [], [15]⟩,
        ⟨91850, true, false, [], [15]⟩,
        ⟨151, false, false, [95435], []⟩,
        ⟨152, false, false, [95435], []⟩,
        ⟨101013, false, false, [], [3]⟩,
        ⟨101103, false, false, [], [3]⟩,
        ⟨101104, false, false, [], [3]⟩,
        ⟨101104, false, false, [], [3]⟩,
        ⟨99139, false, false, [36857], []⟩,
        ⟨101105, false, false, [], []⟩,
        ⟨101106, false, false, [], []⟩,
        ⟨100665, false, false, [36857], []⟩,
        ⟨13, true, false, [], [36857, 96653]⟩
      ]⟩,
    ⟨[36855], [36856], .contexts [
        ⟨101010, true, true, [], []⟩
      ]⟩,
    ⟨[96653, 15], [36855, 95433], .contexts [
        ⟨101108, true, false, [36856], [15]⟩,
        ⟨1, false, false, [36856, 95433], []⟩,
        ⟨101109, true, false, [], [95433]⟩
      ]⟩,
    ⟨[36859, 85289], [36859, 85289], .contexts []⟩,
    ⟨[36859, 85289], [36859, 85289], .contexts []⟩,
    ⟨[83591, 13], [36859, 85289], .contexts [
        ⟨101019, false, false, [], []⟩,
        ⟨101022, false, false, [], []⟩,
        ⟨101111, false, false, [], []⟩,
        ⟨101112, false, false, [], []⟩,
        ⟨101112, false, false, [], []⟩
      ]⟩,
    ⟨[36859, 85291], [36859, 85291], .contexts []⟩,
    ⟨[36859, 85291], [36859, 85291], .contexts []⟩,
    ⟨[85291, 13], [85291, 13], .contexts []⟩,
    ⟨[36861], [36858], .contexts [
        ⟨101023, false, false, [], []⟩
      ]⟩,
    ⟨[36858], [36858], .contexts []⟩,
    ⟨[85291, 13], [36861, 83593], .contexts [
        ⟨101116, false, false, [], []⟩,
        ⟨101115, true, false, [36858], [13]⟩,
        ⟨101114, true, false, [36858], [13]⟩,
        ⟨31030, true, false, [], [13]⟩,
        ⟨101113, true, false, [36858], [5, 13]⟩,
        ⟨1136, false, false, [36858, 83591], []⟩,
        ⟨29, false, false, [36858, 83591], []⟩,
        ⟨22110, false, false, [36858], []⟩,
        ⟨22277, false, false, [36858], []⟩,
        ⟨22114, false, false, [36858], []⟩,
        ⟨22114, false, false, [36858], []⟩,
        ⟨43704, false, false, [36858], []⟩,
        ⟨101118, true, false, [], [83593]⟩,
        ⟨101118, true, false, [], [83593]⟩,
        ⟨101117, true, false, [], [83593]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1580. -/
def y322TCIndexRaw1580 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83593, 13], [36859, 85291], .contexts [
        ⟨101119, true, false, [36860], [13]⟩,
        ⟨59, false, false, [36860, 85291], []⟩,
        ⟨101023, false, true, [], [85291]⟩
      ]⟩,
    ⟨[33629, 86127], [33629, 86127], .contexts []⟩,
    ⟨[33629, 86127], [33629, 86127], .contexts []⟩,
    ⟨[85289, 7], [85289, 7], .contexts []⟩,
    ⟨[36899], [36861, 33629], .source 18514⟩,
    ⟨[85289, 7], [36899, 86129], .contexts [
        ⟨101123, false, false, [], []⟩,
        ⟨101113, true, false, [36858], [7]⟩,
        ⟨73, false, false, [36858, 83591], []⟩,
        ⟨74, false, false, [36858, 83591], []⟩,
        ⟨91431, false, false, [36858], [13]⟩,
        ⟨101121, false, false, [36858], [13]⟩,
        ⟨101122, false, false, [36858], [13]⟩,
        ⟨101122, false, false, [36858], [13]⟩,
        ⟨35519, false, false, [36858, 33629], []⟩,
        ⟨43579, false, false, [36858, 33629], []⟩,
        ⟨101117, true, false, [], [33629, 86129]⟩,
        ⟨101124, true, false, [], [86129]⟩
      ]⟩,
    ⟨[36901], [36898], .source 18515⟩,
    ⟨[36867, 84991], [36867, 84991], .contexts []⟩,
    ⟨[94329, 5], [36867, 84991], .contexts [
        ⟨101027, false, false, [], []⟩,
        ⟨101031, false, false, [], []⟩,
        ⟨101127, false, false, [], []⟩,
        ⟨101127, false, false, [], []⟩
      ]⟩,
    ⟨[36903], [36867, 33109], .source 18516⟩,
    ⟨[34815, 91513], [34815, 91513], .contexts []⟩,
    ⟨[34815, 91513], [34815, 91513], .contexts []⟩,
    ⟨[92289, 5], [92289, 5], .contexts []⟩,
    ⟨[36905], [36902], .source 18517⟩,
    ⟨[36907], [36905, 34815], .source 18518⟩,
    ⟨[92289, 5], [36907, 91513], .contexts [
        ⟨101132, false, false, [], []⟩,
        ⟨101129, false, false, [36902], [92289, 5]⟩,
        ⟨90325, true, false, [36902, 36867], [5]⟩,
        ⟨101128, true, false, [36902], [9, 5]⟩,
        ⟨960, false, false, [36902, 94329], []⟩,
        ⟨47, false, false, [36902, 94329], []⟩,
        ⟨95116, false, false, [36902], []⟩,
        ⟨101130, false, false, [36902], []⟩,
        ⟨101131, false, false, [36902], []⟩,
        ⟨101131, false, false, [36902], []⟩,
        ⟨90171, false, false, [36902, 34815], []⟩,
        ⟨101133, true, false, [], [34815, 91513]⟩,
        ⟨101134, true, false, [], [91513]⟩
      ]⟩,
    ⟨[36909], [36906], .source 18519⟩,
    ⟨[91513, 5], [36909, 92289], .contexts [
        ⟨101135, true, false, [36906], [5]⟩,
        ⟨28, false, false, [36906, 92289], []⟩,
        ⟨101136, true, false, [], [92289]⟩
      ]⟩,
    ⟨[36911], [36867, 28923], .source 18520⟩,
    ⟨[34811, 95385], [34811, 95385], .contexts []⟩,
    ⟨[90503, 5], [90503, 5], .contexts []⟩,
    ⟨[36913], [36910], .source 18521⟩,
    ⟨[36915], [36913, 34811], .source 18522⟩,
    ⟨[90503, 5], [36915, 95385], .contexts [
        ⟨101140, false, false, [], []⟩,
        ⟨101138, false, false, [36910], [90503, 5]⟩,
        ⟨75344, true, false, [36910, 36867], [5]⟩,
        ⟨101128, true, false, [36910], [11, 5]⟩,
        ⟨940, false, false, [36910, 94329], []⟩,
        ⟨54, false, false, [36910, 94329], []⟩,
        ⟨95119, false, false, [36910], []⟩,
        ⟨101139, false, false, [36910], []⟩,
        ⟨101139, false, false, [36910], []⟩,
        ⟨90567, false, false, [36910, 34811], []⟩,
        ⟨101141, true, false, [], [34811, 95385]⟩,
        ⟨101142, true, false, [], [95385]⟩
      ]⟩,
    ⟨[36917], [36914], .source 18523⟩,
    ⟨[36867, 84989], [36867, 84989], .contexts []⟩,
    ⟨[84989, 5], [84989, 5], .contexts []⟩,
    ⟨[36866], [36866], .contexts []⟩,
    ⟨[84989, 5], [36865, 94331], .contexts [
        ⟨101146, false, false, [], []⟩,
        ⟨101145, true, false, [36866], [5]⟩,
        ⟨29675, true, false, [], [5]⟩,
        ⟨101128, true, false, [36866], [15, 5]⟩,
        ⟨1204, false, false, [36866, 94329], []⟩,
        ⟨10, false, false, [36866, 94329], []⟩,
        ⟨83951, false, false, [36866], []⟩,
        ⟨84190, false, false, [36866], []⟩,
        ⟨83956, false, false, [36866], []⟩,
        ⟨83956, false, false, [36866], []⟩,
        ⟨101147, true, false, [], [94331]⟩,
        ⟨101147, true, false, [], [94331]⟩,
        ⟨101032, true, false, [], [94331]⟩
      ]⟩,
    ⟨[84507, 13], [36799, 84997], .contexts [
        ⟨101042, false, false, [], []⟩
      ]⟩,
    ⟨[36799, 84997], [36799, 84997], .contexts []⟩,
    ⟨[36799, 84997], [36799, 84997], .contexts []⟩,
    ⟨[84507, 11], [18275, 88099], .contexts [
        ⟨48417, false, false, [], []⟩
      ]⟩,
    ⟨[18275, 88099], [18275, 88099], .contexts []⟩,
    ⟨[18275, 88099], [18275, 88099], .contexts []⟩,
    ⟨[90509, 13], [36831, 88099], .contexts [
        ⟨100954, false, false, [36826], [90509, 13]⟩,
        ⟨75493, true, false, [36826, 36799], [13]⟩,
        ⟨101151, true, false, [36826], [11, 13]⟩,
        ⟨101151, true, false, [36826], [11, 13]⟩,
        ⟨101150, true, false, [36826], [11, 13]⟩,
        ⟨101149, true, false, [36826], [11, 13]⟩,
        ⟨101038, true, false, [36826], [11, 13]⟩,
        ⟨931, false, false, [36826, 84507], []⟩,
        ⟨54, false, false, [36826, 84507], []⟩,
        ⟨101152, false, false, [36826], []⟩,
        ⟨101153, false, false, [36826], []⟩,
        ⟨101154, false, false, [36826], []⟩,
        ⟨101154, false, false, [36826], []⟩,
        ⟨100959, true, false, [], [88099]⟩
      ]⟩,
    ⟨[36873, 90507], [36873, 90507], .contexts []⟩,
    ⟨[88097, 13], [36873, 90507], .contexts [
        ⟨101045, false, false, [], []⟩,
        ⟨101048, false, false, [], []⟩,
        ⟨101156, false, false, [], []⟩,
        ⟨101156, false, false, [], []⟩
      ]⟩,
    ⟨[29933, 83085], [29933, 83085], .contexts []⟩,
    ⟨[90507, 7], [90507, 7], .contexts []⟩,
    ⟨[36875], [36872], .contexts [
        ⟨101049, false, false, [], []⟩
      ]⟩,
    ⟨[36919], [36875, 29933], .source 18524⟩,
    ⟨[90507, 7], [36919, 83083], .contexts [
        ⟨101159, false, false, [], []⟩,
        ⟨101157, true, false, [36872], [7]⟩,
        ⟨73, false, false, [36872, 88097], []⟩,
        ⟨74, false, false, [36872, 88097], []⟩,
        ⟨78412, true, false, [36872, 29930], [7, 13]⟩,
        ⟨38, false, false, [36872, 29930, 83085], [13]⟩,
        ⟨78413, true, false, [36872], [83085, 13]⟩,
        ⟨101158, false, false, [36872], [13]⟩,
        ⟨101158, false, false, [36872], [13]⟩,
        ⟨18543, false, false, [36872, 29933], []⟩,
        ⟨44635, false, false, [36872, 29933], []⟩,
        ⟨101160, true, false, [], [29933, 83083]⟩,
        ⟨101161, true, false, [], [83083]⟩
      ]⟩,
    ⟨[36921], [36918], .source 18525⟩,
    ⟨[36923], [29881, 29915], .source 18526⟩,
    ⟨[88097, 15, 13, 15, 13], [36923, 92569], .contexts [
        ⟨78389, true, false, [29882], [15, 13, 15, 13]⟩,
        ⟨1, false, false, [29882, 93263], [13, 15, 13]⟩,
        ⟨78335, true, false, [], [93263, 13, 15, 13]⟩,
        ⟨78385, false, false, [], [13, 15, 13]⟩,
        ⟨78386, false, false, [], [13, 15, 13]⟩,
        ⟨78386, false, false, [], [13, 15, 13]⟩,
        ⟨78382, false, false, [29881], [15, 13]⟩,
        ⟨101164, true, false, [], [92573, 15, 13]⟩,
        ⟨73115, false, false, [36923], [13]⟩,
        ⟨73111, false, false, [36923], []⟩
      ]⟩,
    ⟨[90507, 15], [90507, 15], .contexts []⟩,
    ⟨[36925], [36875, 36923], .source 18527⟩,
    ⟨[90507, 15], [36925, 92569], .contexts [
        ⟨101166, false, false, [], []⟩,
        ⟨101157, true, false, [36872], [15]⟩,
        ⟨88, false, false, [36872, 88097], []⟩,
        ⟨91, false, false, [36872, 88097], []⟩,
        ⟨101165, false, false, [36872], []⟩,
        ⟨95571, false, false, [36872, 36923], []⟩,
        ⟨101160, true, false, [], [36923, 92569]⟩,
        ⟨101167, true, false, [], [92569]⟩
      ]⟩,
    ⟨[36927], [36924], .source 18528⟩,
    ⟨[85899, 9], [85897], .contexts [
        ⟨34360, false, false, [], []⟩,
        ⟨34361, false, false, [], []⟩,
        ⟨34159, false, false, [], []⟩,
        ⟨34159, false, false, [], []⟩
      ]⟩,
    ⟨[32783, 91633], [32783, 91633], .contexts []⟩,
    ⟨[36929], [32781, 36839], .source 18529⟩,
    ⟨[91635, 9], [36929, 92343], .contexts [
        ⟨66994, true, false, [], [9]⟩,
        ⟨101171, true, false, [32782], [1, 9]⟩,
        ⟨101171, true, false, [32782], [1, 9]⟩,
        ⟨89215, true, false, [32782], [1, 9]⟩,
        ⟨34155, true, false, [32782], [9, 1, 9]⟩,
        ⟨34155, true, false, [32782], [9, 1, 9]⟩,
        ⟨34363, true, false, [32782], [9, 1, 9]⟩,
        ⟨34362, true, false, [32782], [9, 1, 9]⟩,
        ⟨101170, true, false, [32782], [1, 9, 1, 9]⟩,
        ⟨495, false, false, [32782, 85899], []⟩,
        ⟨9, false, false, [32782, 85899], []⟩,
        ⟨101059, false, false, [32782], []⟩,
        ⟨101052, false, false, [32782], []⟩,
        ⟨101053, false, false, [32782], []⟩,
        ⟨101053, false, false, [32782], []⟩,
        ⟨100968, false, false, [32782, 36839], []⟩,
        ⟨89214, false, true, [], [36839, 92343]⟩,
        ⟨101172, true, false, [], [92343]⟩
      ]⟩,
    ⟨[36931], [36928], .source 18530⟩,
    ⟨[85897, 3], [27149, 91955], .contexts [
        ⟨69415, false, false, [], []⟩
      ]⟩,
    ⟨[27149, 91955], [27149, 91955], .contexts []⟩,
    ⟨[27149, 91955], [27149, 91955], .contexts []⟩,
    ⟨[36839, 92347], [36839, 92347], .contexts []⟩,
    ⟨[91955, 9], [91955, 9], .contexts []⟩,
    ⟨[36933], [27151, 36839], .source 18531⟩,
    ⟨[91955, 9], [36933, 92347], .contexts [
        ⟨101179, false, false, [], []⟩,
        ⟨101177, true, false, [27148], [9]⟩,
        ⟨101177, true, false, [27148], [9]⟩,
        ⟨101176, true, false, [27148], [9]⟩,
        ⟨101175, true, false, [27148], [9]⟩,
        ⟨101170, true, false, [27148], [3, 9]⟩,
        ⟨479, false, false, [27148, 85899], []⟩,
        ⟨21, false, false, [27148, 85899], []⟩,
        ⟨101060, false, false, [27148], []⟩,
        ⟨101178, false, false, [27148], []⟩,
        ⟨101178, false, false, [27148], []⟩,
        ⟨69399, true, false, [], [36839, 92347]⟩,
        ⟨101180, true, false, [], [92347]⟩
      ]⟩,
    ⟨[36935], [36932], .source 18532⟩,
    ⟨[36881, 92927], [36881, 92927], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1581. -/
def y322TCIndexRaw1581 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[36881, 92927], [36881, 92927], .contexts []⟩,
    ⟨[89275, 13], [36881, 92927], .contexts [
        ⟨101066, false, false, [], []⟩,
        ⟨101070, false, false, [], []⟩,
        ⟨101183, false, false, [], []⟩,
        ⟨101184, false, false, [], []⟩,
        ⟨101184, false, false, [], []⟩
      ]⟩,
    ⟨[92929, 13], [92929, 13], .contexts []⟩,
    ⟨[36880], [36880], .contexts []⟩,
    ⟨[92929, 13], [36879, 89273], .contexts [
        ⟨101186, false, false, [], []⟩,
        ⟨75920, true, false, [], [13]⟩,
        ⟨101185, true, false, [36880], [3, 13]⟩,
        ⟨1132, false, false, [36880, 89275], []⟩,
        ⟨90249, false, false, [36880], []⟩,
        ⟨90248, false, false, [36880], []⟩,
        ⟨90251, false, false, [36880], []⟩,
        ⟨101187, true, false, [], [89273]⟩,
        ⟨101187, true, false, [], [89273]⟩,
        ⟨101071, true, false, [], [89273]⟩
      ]⟩,
    ⟨[36937], [36881, 29317], .source 18533⟩,
    ⟨[36939], [36765, 36393], .source 18534⟩,
    ⟨[36941], [36939, 30805], .source 18535⟩,
    ⟨[90839, 13], [36936, 36941, 93913], .contexts [
        ⟨101189, false, false, [36936], [90839, 13]⟩,
        ⟨76421, true, false, [36936, 36881], [13]⟩,
        ⟨101185, true, false, [36936], [15, 13]⟩,
        ⟨6730, false, false, [36936, 89275], []⟩,
        ⟨90, false, false, [36936, 89275], []⟩,
        ⟨100881, true, false, [36936, 36766], [15, 13, 15]⟩,
        ⟨1, false, false, [36936, 36766, 85195], [13, 15]⟩,
        ⟨100808, false, true, [36936], [85195, 13, 15]⟩,
        ⟨100878, false, false, [36936], [13, 15]⟩,
        ⟨100879, false, false, [36936], [13, 15]⟩,
        ⟨100879, false, false, [36936], [13, 15]⟩,
        ⟨99999, false, false, [36936, 36765], [15]⟩,
        ⟨101190, true, false, [36936], [83885, 15]⟩,
        ⟨81991, false, false, [36936, 36939], []⟩,
        ⟨101191, true, false, [36936], [93913]⟩,
        ⟨100191, false, false, [36936, 36941], []⟩
      ]⟩,
    ⟨[36943], [36936], .source 18536⟩,
    ⟨[36945], [36943, 36941], .source 18537⟩,
    ⟨[90839, 13], [36945, 93913], .contexts [
        ⟨101192, false, false, [], []⟩,
        ⟨101193, true, false, [], [36941, 93913]⟩,
        ⟨101194, true, false, [], [93913]⟩
      ]⟩,
    ⟨[36947], [36944], .source 18538⟩,
    ⟨[36887, 93777], [36887, 93777], .contexts []⟩,
    ⟨[36887, 93777], [36887, 93777], .contexts []⟩,
    ⟨[93779, 13], [93779, 13], .contexts []⟩,
    ⟨[36886], [36886], .contexts []⟩,
    ⟨[93779, 13], [36889, 88311], .contexts [
        ⟨101199, false, false, [], []⟩,
        ⟨80903, true, false, [], [13]⟩,
        ⟨101198, true, false, [36886], [3, 13]⟩,
        ⟨101198, true, false, [36886], [3, 13]⟩,
        ⟨101197, true, false, [36886], [3, 13]⟩,
        ⟨101080, true, false, [36886], [3, 13]⟩,
        ⟨101078, true, false, [36886], [3, 13]⟩,
        ⟨1132, false, false, [36886, 88313], []⟩,
        ⟨21, false, false, [36886, 88313], []⟩,
        ⟨49611, false, false, [36886], []⟩,
        ⟨49612, false, false, [36886], []⟩,
        ⟨49536, false, false, [36886], []⟩,
        ⟨49536, false, false, [36886], []⟩,
        ⟨101200, true, false, [], [88311]⟩,
        ⟨101200, true, false, [], [88311]⟩,
        ⟨101081, true, false, [], [88311]⟩
      ]⟩,
    ⟨[36887], [36888], .contexts [
        ⟨101081, true, true, [], []⟩
      ]⟩,
    ⟨[36949], [30809, 36437], .source 18539⟩,
    ⟨[88317, 11], [36897, 92917], .contexts [
        ⟨101096, false, false, [], []⟩
      ]⟩,
    ⟨[36897, 92917], [36897, 92917], .contexts []⟩,
    ⟨[88317, 11], [36897, 92917], .contexts [
        ⟨101204, false, false, [], []⟩,
        ⟨101205, false, false, [], []⟩,
        ⟨101205, false, false, [], []⟩
      ]⟩,
    ⟨[88317, 10], [88317, 11], .contexts [
        ⟨54, false, false, [88317], []⟩
      ]⟩,
    ⟨[96765, 13], [96765, 13], .contexts []⟩,
    ⟨[36951], [36948], .source 18540⟩,
    ⟨[36953], [36951, 36897], .source 18541⟩,
    ⟨[96765, 13], [36953, 92917], .contexts [
        ⟨101208, false, false, [], []⟩,
        ⟨101203, false, false, [36948], [96765, 13]⟩,
        ⟨100165, true, false, [36948, 30809], [13]⟩,
        ⟨81972, true, false, [36948], [11, 13]⟩,
        ⟨81972, true, false, [36948], [11, 13]⟩,
        ⟨81971, true, false, [36948], [11, 13]⟩,
        ⟨81876, false, false, [36948], [93915, 11, 13]⟩,
        ⟨59, true, false, [36948, 30806, 93915], [11, 13]⟩,
        ⟨81974, false, false, [36948, 30806], [13, 11, 13]⟩,
        ⟨931, false, false, [36948, 88317], []⟩,
        ⟨101207, false, false, [36948], []⟩,
        ⟨101206, false, false, [36948], []⟩,
        ⟨101209, true, false, [], [36897, 92917]⟩,
        ⟨101210, true, false, [], [92917]⟩
      ]⟩,
    ⟨[36955], [36952], .source 18542⟩,
    ⟨[36819, 95437], [36819, 95437], .contexts []⟩,
    ⟨[36819, 95437], [36819, 95437], .contexts []⟩,
    ⟨[36957], [36821, 36517], .source 18543⟩,
    ⟨[36959], [36956], .source 18544⟩,
    ⟨[36359, 89067], [36359, 89067], .contexts []⟩,
    ⟨[36359, 89067], [36359, 89067], .contexts []⟩,
    ⟨[85913, 13], [36359, 89067], .contexts [
        ⟨99948, false, false, [], []⟩,
        ⟨101217, false, false, [], []⟩,
        ⟨101218, false, false, [], []⟩,
        ⟨101218, false, false, [], []⟩
      ]⟩,
    ⟨[36359, 89067], [36959, 95439], .contexts [
        ⟨101219, true, false, [], []⟩,
        ⟨101215, false, false, [36956], [85913, 13]⟩,
        ⟨101002, false, false, [36956], [36517, 85913, 13]⟩,
        ⟨79901, true, false, [36956, 36818, 36517], [13]⟩,
        ⟨100388, true, false, [36956, 36818], [13]⟩,
        ⟨47, true, false, [36956, 36818, 92295], [13]⟩,
        ⟨942, true, false, [36956, 36818, 92295], [13]⟩,
        ⟨101100, false, false, [36956, 36818], [9, 13, 13]⟩,
        ⟨101102, false, false, [36956, 36818], [9, 13, 13]⟩,
        ⟨101213, false, false, [36956, 36818], [9, 13, 13]⟩,
        ⟨101214, false, false, [36956, 36818], [9, 13, 13]⟩,
        ⟨101214, false, false, [36956, 36818], [9, 13, 13]⟩,
        ⟨91883, false, false, [36956], [13, 13]⟩,
        ⟨59, false, false, [36956, 95439], []⟩,
        ⟨101216, true, false, [], [95439]⟩
      ]⟩,
    ⟨[36961], [36361, 36959], .source 18545⟩,
    ⟨[36963], [36960], .source 18546⟩,
    ⟨[95439], [36963, 89067], .contexts [
        ⟨101221, false, false, [36960], [95439]⟩,
        ⟨99945, false, false, [36960], [36959, 95439]⟩,
        ⟨101220, true, false, [36960, 36358], []⟩,
        ⟨101222, true, false, [], [89067]⟩
      ]⟩,
    ⟨[36962], [36962], .contexts []⟩,
    ⟨[36961], [36962], .contexts [
        ⟨101222, true, true, [], []⟩,
        ⟨101224, false, false, [], []⟩,
        ⟨101224, false, false, [], []⟩
      ]⟩,
    ⟨[89067, 9], [36961, 95437], .contexts [
        ⟨101223, true, false, [36962], [9]⟩,
        ⟨91884, false, false, [36962], []⟩,
        ⟨91872, false, false, [36962], []⟩,
        ⟨101225, true, false, [], [95437]⟩
      ]⟩,
    ⟨[89067, 11], [36961, 95441], .contexts [
        ⟨101223, true, false, [36962], [11]⟩,
        ⟨91886, false, false, [36962], []⟩,
        ⟨91889, false, false, [36962], []⟩,
        ⟨101225, true, false, [], [95441]⟩
      ]⟩,
    ⟨[95433, 15], [36857, 96653], .contexts [
        ⟨101107, false, false, [], []⟩,
        ⟨101108, false, false, [], []⟩,
        ⟨101105, false, false, [], []⟩,
        ⟨101106, false, false, [], []⟩,
        ⟨101106, false, false, [], []⟩
      ]⟩,
    ⟨[96653, 1], [96653, 1], .contexts []⟩,
    ⟨[36855], [36856], .contexts [
        ⟨101109, false, false, [], []⟩
      ]⟩,
    ⟨[36856], [36856], .contexts []⟩,
    ⟨[96653, 1], [36855, 95429], .contexts [
        ⟨101229, false, false, [], []⟩,
        ⟨101228, true, false, [36856], [1]⟩,
        ⟨7, false, false, [36856, 95433], []⟩,
        ⟨11, false, false, [36856, 95433], []⟩,
        ⟨91854, false, false, [36856], [15]⟩,
        ⟨91810, false, false, [36856], []⟩,
        ⟨91790, false, false, [36856], []⟩,
        ⟨91791, false, false, [36856], []⟩,
        ⟨91791, false, false, [36856], []⟩,
        ⟨91797, false, false, [36856], []⟩,
        ⟨101231, true, false, [], [95429]⟩,
        ⟨101231, true, false, [], [95429]⟩,
        ⟨101230, true, false, [], [95429]⟩
      ]⟩,
    ⟨[95429, 1], [36857, 96653], .contexts [
        ⟨101232, true, false, [36854], [1]⟩,
        ⟨8, false, false, [36854, 96653], []⟩,
        ⟨101010, true, false, [], [96653]⟩
      ]⟩,
    ⟨[36965], [33713, 31535], .source 18547⟩,
    ⟨[96653, 9], [96653, 9], .contexts []⟩,
    ⟨[36967], [36855, 36965], .source 18548⟩,
    ⟨[96653, 9], [36967, 83447], .contexts [
        ⟨101235, false, false, [], []⟩,
        ⟨101228, true, false, [36856], [9]⟩,
        ⟨45, false, false, [36856, 95433], []⟩,
        ⟨48, false, false, [36856, 95433], []⟩,
        ⟨91837, false, false, [36856], [15]⟩,
        ⟨91840, false, false, [36856], [15]⟩,
        ⟨91835, false, false, [36856], [15]⟩,
        ⟨91836, false, false, [36856], [15]⟩,
        ⟨91836, false, false, [36856], [15]⟩,
        ⟨85163, false, false, [36856, 33713], []⟩,
        ⟨101234, true, false, [36856], [83447]⟩,
        ⟨85161, false, false, [36856, 36965], []⟩,
        ⟨101230, true, false, [], [36965, 83447]⟩,
        ⟨101236, true, false, [], [83447]⟩
      ]⟩,
    ⟨[36969], [36966], .source 18549⟩,
    ⟨[36861, 83593], [36861, 83593], .contexts []⟩,
    ⟨[36861, 83593], [36861, 83593], .contexts []⟩,
    ⟨[36971], [36861, 35239], .source 18550⟩,
    ⟨[36971, 83603], [36971, 83603], .contexts []⟩,
    ⟨[36971, 83603], [36971, 83603], .contexts []⟩,
    ⟨[85291], [85291], .contexts []⟩,
    ⟨[83603, 11], [83603, 11], .contexts []⟩,
    ⟨[36973], [36970], .source 18551⟩,
    ⟨[36970], [36970], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1582. -/
def y322TCIndexRaw1582 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[83603, 11], [36973, 85291], .contexts [
        ⟨101245, false, false, [], []⟩,
        ⟨101243, true, false, [36970], [11]⟩,
        ⟨101242, true, false, [36970], [11]⟩,
        ⟨22129, true, false, [], [11]⟩,
        ⟨101241, false, false, [36970], [83601, 13, 11]⟩,
        ⟨96533, true, false, [36970, 36861], [13, 11]⟩,
        ⟨101240, true, false, [36970], [11, 13, 11]⟩,
        ⟨101240, true, false, [36970], [11, 13, 11]⟩,
        ⟨101239, true, false, [36970], [11, 13, 11]⟩,
        ⟨101119, true, false, [36970], [11, 13, 11]⟩,
        ⟨101116, true, false, [36970], [11, 13, 11]⟩,
        ⟨4838, false, false, [36970, 85291], []⟩,
        ⟨101244, false, false, [36970], []⟩,
        ⟨31341, false, false, [36970], []⟩,
        ⟨101247, true, false, [], [85291]⟩,
        ⟨101247, true, false, [], [85291]⟩,
        ⟨101246, true, false, [], [85291]⟩
      ]⟩,
    ⟨[85291, 11], [36971, 83603], .contexts [
        ⟨101248, true, false, [36972], [11]⟩,
        ⟨53, false, false, [36972, 83603], []⟩,
        ⟨101246, false, true, [], [83603]⟩
      ]⟩,
    ⟨[36907, 91513], [36907, 91513], .contexts []⟩,
    ⟨[36907, 91513], [36907, 91513], .contexts []⟩,
    ⟨[36906], [36906], .contexts []⟩,
    ⟨[91515, 5], [36909, 92287], .contexts [
        ⟨66435, true, false, [], [5]⟩,
        ⟨101251, true, false, [36906], [15, 5]⟩,
        ⟨101251, true, false, [36906], [15, 5]⟩,
        ⟨101250, true, false, [36906], [15, 5]⟩,
        ⟨101135, true, false, [36906], [15, 5]⟩,
        ⟨101132, true, false, [36906], [15, 5]⟩,
        ⟨1204, false, false, [36906, 92289], []⟩,
        ⟨10, false, false, [36906, 92289], []⟩,
        ⟨71563, false, false, [36906], []⟩,
        ⟨71564, false, false, [36906], []⟩,
        ⟨71323, false, false, [36906], []⟩,
        ⟨71323, false, false, [36906], []⟩,
        ⟨90294, false, false, [36906], []⟩,
        ⟨101252, true, false, [], [92287]⟩,
        ⟨101252, true, false, [], [92287]⟩,
        ⟨101136, true, false, [], [92287]⟩
      ]⟩,
    ⟨[36915, 95385], [36915, 95385], .contexts []⟩,
    ⟨[36915, 95385], [36915, 95385], .contexts []⟩,
    ⟨[36915, 95387], [36915, 95387], .contexts []⟩,
    ⟨[36914], [36914], .contexts []⟩,
    ⟨[95387, 5], [36917, 90501], .contexts [
        ⟨101256, true, false, [36914], [5]⟩,
        ⟨90569, true, false, [], [5]⟩,
        ⟨101255, true, false, [36914], [15, 5]⟩,
        ⟨101255, true, false, [36914], [15, 5]⟩,
        ⟨101254, true, false, [36914], [15, 5]⟩,
        ⟨101143, true, false, [36914], [15, 5]⟩,
        ⟨101140, true, false, [36914], [15, 5]⟩,
        ⟨1204, false, false, [36914, 90503], []⟩,
        ⟨10, false, false, [36914, 90503], []⟩,
        ⟨61569, false, false, [36914], []⟩,
        ⟨61570, false, false, [36914], []⟩,
        ⟨61329, false, false, [36914], []⟩,
        ⟨61329, false, false, [36914], []⟩,
        ⟨75296, false, false, [36914], []⟩,
        ⟨101257, true, false, [], [90501]⟩,
        ⟨101257, true, false, [], [90501]⟩,
        ⟨101144, true, false, [], [90501]⟩
      ]⟩,
    ⟨[90501, 5], [36915, 95387], .contexts [
        ⟨101258, true, false, [36916], [5]⟩,
        ⟨28, false, false, [36916, 95387], []⟩,
        ⟨101144, false, true, [], [95387]⟩
      ]⟩,
    ⟨[36865, 94331], [36865, 94331], .contexts []⟩,
    ⟨[84989, 5], [36865, 94331], .contexts [
        ⟨101146, false, false, [], []⟩,
        ⟨101148, false, false, [], []⟩,
        ⟨101260, false, false, [], []⟩,
        ⟨101260, false, false, [], []⟩
      ]⟩,
    ⟨[94333, 5], [94333, 5], .contexts []⟩,
    ⟨[36975], [36867, 23459], .source 18552⟩,
    ⟨[94333, 5], [36975, 85283], .contexts [
        ⟨101262, false, false, [], []⟩,
        ⟨83955, true, false, [], [5]⟩,
        ⟨101261, true, false, [36864], [1, 5]⟩,
        ⟨890, false, false, [36864, 84989], []⟩,
        ⟨9, false, false, [36864, 84989], []⟩,
        ⟨53593, false, false, [36864], []⟩,
        ⟨53583, false, false, [36864, 23459], []⟩,
        ⟨101029, true, false, [], [23459, 85283]⟩,
        ⟨101263, true, false, [], [85283]⟩
      ]⟩,
    ⟨[36977], [36974], .source 18553⟩,
    ⟨[85283, 5], [36977, 94333], .contexts [
        ⟨101264, true, false, [36974], [5]⟩,
        ⟨28, false, false, [36974, 94333], []⟩,
        ⟨101265, true, false, [], [94333]⟩
      ]⟩,
    ⟨[31935, 94769], [31935, 94769], .contexts []⟩,
    ⟨[31935, 94769], [31935, 94769], .contexts []⟩,
    ⟨[94769], [94769], .contexts []⟩,
    ⟨[36979], [36867, 31935], .source 18554⟩,
    ⟨[94331, 13], [36979, 94769], .contexts [
        ⟨101261, true, false, [36864], [13]⟩,
        ⟨179, false, false, [36864, 84989], []⟩,
        ⟨180, false, false, [36864, 84989], []⟩,
        ⟨29964, false, false, [36864], [5]⟩,
        ⟨29965, false, false, [36864], [5]⟩,
        ⟨29670, false, false, [36864], [5]⟩,
        ⟨29670, false, false, [36864], [5]⟩,
        ⟨86407, false, false, [36864], []⟩,
        ⟨101267, false, false, [36864], []⟩,
        ⟨101268, false, false, [36864], []⟩,
        ⟨101268, false, false, [36864], []⟩,
        ⟨101269, false, false, [36864, 31935], []⟩,
        ⟨101029, true, false, [], [31935, 94769]⟩,
        ⟨101270, true, false, [], [94769]⟩
      ]⟩,
    ⟨[36981], [36978], .source 18555⟩,
    ⟨[36933, 92347], [36933, 92347], .contexts []⟩,
    ⟨[91957], [31369, 91137], .contexts [
        ⟨84441, false, false, [], []⟩
      ]⟩,
    ⟨[36983], [36935, 31369], .source 18556⟩,
    ⟨[36985], [36982], .source 18557⟩,
    ⟨[91139], [36985, 92349], .contexts [
        ⟨84467, true, false, [], []⟩,
        ⟨101275, false, false, [36982], [91137, 9]⟩,
        ⟨101182, false, false, [36982], [31369, 91137, 9]⟩,
        ⟨84432, true, false, [36982, 36932], [9]⟩,
        ⟨84432, true, false, [36982, 36932], [9]⟩,
        ⟨101274, true, false, [36982, 36932], [9]⟩,
        ⟨68822, true, false, [36982, 36932], [9]⟩,
        ⟨29, true, false, [36982, 36932, 91955], [9]⟩,
        ⟨598, true, false, [36982, 36932, 91955], [9]⟩,
        ⟨101179, false, false, [36982, 36932], [5, 9, 9]⟩,
        ⟨101181, false, false, [36982, 36932], [5, 9, 9]⟩,
        ⟨101273, false, false, [36982, 36932], [5, 9, 9]⟩,
        ⟨101273, false, false, [36982, 36932], [5, 9, 9]⟩,
        ⟨71430, false, false, [36982], [9, 9]⟩,
        ⟨46, false, false, [36982, 92349], []⟩,
        ⟨101276, true, false, [], [92349]⟩
      ]⟩,
    ⟨[36985], [36985], .contexts []⟩,
    ⟨[36985], [36985], .contexts []⟩,
    ⟨[36983], [36984], .contexts [
        ⟨101276, true, true, [], []⟩
      ]⟩,
    ⟨[92349], [36983, 91139], .contexts [
        ⟨101278, false, false, [36984], [92349]⟩,
        ⟨101279, false, false, [36984], [92349]⟩,
        ⟨101277, true, false, [36984], []⟩,
        ⟨101280, true, false, [], [91139]⟩
      ]⟩,
    ⟨[36982], [36982], .contexts []⟩,
    ⟨[91139, 1], [36985, 92351], .contexts [
        ⟨101281, true, false, [36982], [1]⟩,
        ⟨71433, false, false, [36982], []⟩,
        ⟨71528, false, false, [36982], []⟩,
        ⟨101282, true, false, [], [92351]⟩,
        ⟨101282, true, false, [], [92351]⟩,
        ⟨101276, true, false, [], [92351]⟩
      ]⟩,
    ⟨[36879, 89273], [36879, 89273], .contexts []⟩,
    ⟨[36879, 89273], [36879, 89273], .contexts []⟩,
    ⟨[92929, 13], [36879, 89273], .contexts [
        ⟨101186, false, false, [], []⟩,
        ⟨101188, false, false, [], []⟩,
        ⟨101284, false, false, [], []⟩,
        ⟨101285, false, false, [], []⟩,
        ⟨101285, false, false, [], []⟩
      ]⟩,
    ⟨[36987], [36879, 33051], .source 18558⟩,
    ⟨[36989], [36986], .source 18559⟩,
    ⟨[36986], [36986], .contexts []⟩,
    ⟨[87221, 13], [36989, 92931], .contexts [
        ⟨101287, false, false, [36986], [87221, 13]⟩,
        ⟨90313, true, false, [36986, 36879], [13]⟩,
        ⟨101286, true, false, [36986], [5, 13]⟩,
        ⟨1136, false, false, [36986, 92929], []⟩,
        ⟨29, false, false, [36986, 92929], []⟩,
        ⟨75924, false, false, [36986], []⟩,
        ⟨75998, false, false, [36986], []⟩,
        ⟨75929, false, false, [36986], []⟩,
        ⟨75929, false, false, [36986], []⟩,
        ⟨76384, false, false, [36986], []⟩,
        ⟨101289, true, false, [], [92931]⟩,
        ⟨101289, true, false, [], [92931]⟩,
        ⟨101288, true, false, [], [92931]⟩
      ]⟩,
    ⟨[36991], [36377, 36987], .source 18560⟩,
    ⟨[95343], [36991, 87221], .contexts [
        ⟨100005, true, false, [36378], []⟩,
        ⟨101290, true, false, [36378, 36988], [13]⟩,
        ⟨59, false, false, [36378, 36988, 87221], []⟩,
        ⟨101288, false, true, [36378], [87221]⟩,
        ⟨99976, true, false, [], [36987, 87221]⟩,
        ⟨101291, true, false, [], [87221]⟩
      ]⟩,
    ⟨[36993], [36990], .source 18561⟩,
    ⟨[36990], [36990], .contexts []⟩,
    ⟨[36993], [36990], .contexts [
        ⟨101293, false, false, [], []⟩,
        ⟨101294, false, false, [], []⟩,
        ⟨101294, false, false, [], []⟩
      ]⟩,
    ⟨[87221, 1], [36993, 95341], .contexts [
        ⟨101292, true, false, [36990], [1]⟩,
        ⟨89491, false, false, [36990], []⟩,
        ⟨89559, false, false, [36990], []⟩,
        ⟨101295, true, false, [], [95341]⟩
      ]⟩,
    ⟨[84409], [84409], .contexts []⟩,
    ⟨[36995], [36881, 35001], .source 18562⟩,
    ⟨[89273, 11], [36995, 84409], .contexts [
        ⟨101286, true, false, [36878], [11]⟩,
        ⟨82, false, false, [36878, 92929], []⟩,
        ⟨83, false, false, [36878, 92929], []⟩,
        ⟨95772, false, false, [36878], [13]⟩,
        ⟨26767, false, false, [36878, 35001], []⟩,
        ⟨101297, false, false, [36878, 35001], []⟩,
        ⟨101068, true, false, [], [35001, 84409]⟩,
        ⟨101298, true, false, [], [84409]⟩
      ]⟩,
    ⟨[36997], [36994], .source 18563⟩,
    ⟨[36889, 88311], [36889, 88311], .contexts []⟩,
    ⟨[36889, 88311], [36889, 88311], .contexts []⟩,
    ⟨[93779, 13], [36889, 88311], .contexts [
        ⟨101199, false, false, [], []⟩,
        ⟨101201, false, false, [], []⟩,
        ⟨101301, false, false, [], []⟩,
        ⟨101302, false, false, [], []⟩,
        ⟨101302, false, false, [], []⟩
      ]⟩,
    ⟨[93781], [36365, 89071], .contexts [
        ⟨99953, false, false, [], []⟩
      ]⟩,
    ⟨[36365, 89071], [36365, 89071], .contexts []⟩,
    ⟨[93781], [36365, 89071], .contexts [
        ⟨101304, false, false, [], []⟩,
        ⟨101305, false, false, [], []⟩
      ]⟩,
    ⟨[36999], [36365, 31181], .source 18564⟩,
    ⟨[88311, 5], [88311, 5], .contexts []⟩,
    ⟨[36887], [36888], .contexts [
        ⟨101202, false, false, [], []⟩
      ]⟩,
    ⟨[37001], [36887, 36999], .source 18565⟩,
    ⟨[88311, 5], [37001, 94277], .contexts [
        ⟨101308, false, false, [], []⟩,
        ⟨101303, true, false, [36888], [5]⟩,
        ⟨68, false, false, [36888, 93779], []⟩,
        ⟨69, false, false, [36888, 93779], []⟩,
        ⟨80907, false, false, [36888], [13]⟩,
        ⟨101306, false, false, [36888], [13]⟩,
        ⟨101305, false, false, [36888], [13]⟩,
        ⟨101305, false, false, [36888], [13]⟩,
        ⟨83787, false, false, [36888, 36365], []⟩,
        ⟨101307, true, false, [36888], [94277]⟩,
        ⟨101309, true, false, [], [36999, 94277]⟩,
        ⟨101310, true, false, [], [94277]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1583. -/
def y322TCIndexRaw1583 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[37003], [37000], .source 18566⟩,
    ⟨[30721, 83029], [30721, 83029], .contexts []⟩,
    ⟨[83031], [83031], .contexts []⟩,
    ⟨[37005], [36887, 30721], .source 18567⟩,
    ⟨[88311, 11], [37005, 83031], .contexts [
        ⟨101303, true, false, [36888], [11]⟩,
        ⟨82, false, false, [36888, 93779], []⟩,
        ⟨83, false, false, [36888, 93779], []⟩,
        ⟨81414, false, false, [36888], [13]⟩,
        ⟨81416, false, false, [36888], [13]⟩,
        ⟨101313, false, false, [36888], [13]⟩,
        ⟨101313, false, false, [36888], [13]⟩,
        ⟨18443, false, false, [36888, 30721], []⟩,
        ⟨101314, false, false, [36888, 30721], []⟩,
        ⟨101309, true, false, [], [30721, 83031]⟩,
        ⟨101315, true, false, [], [83031]⟩
      ]⟩,
    ⟨[37007], [37004], .source 18568⟩,
    ⟨[83031, 11], [37007, 88311], .contexts [
        ⟨101316, true, false, [37004], [11]⟩,
        ⟨53, false, false, [37004, 88311], []⟩,
        ⟨101317, true, false, [], [88311]⟩
      ]⟩,
    ⟨[36953, 92917], [36953, 92917], .contexts []⟩,
    ⟨[92915, 13], [92915, 13], .contexts []⟩,
    ⟨[37009], [36955, 36427], .source 18569⟩,
    ⟨[92915, 13], [37009, 85889], .contexts [
        ⟨101320, false, false, [], []⟩,
        ⟨75901, true, false, [], [13]⟩,
        ⟨101319, true, false, [36952], [9, 13]⟩,
        ⟨101319, true, false, [36952], [9, 13]⟩,
        ⟨101211, true, false, [36952], [9, 13]⟩,
        ⟨101208, true, false, [36952], [9, 13]⟩,
        ⟨942, false, false, [36952, 96765], []⟩,
        ⟨47, false, false, [36952, 96765], []⟩,
        ⟨100166, false, false, [36952], []⟩,
        ⟨100158, false, false, [36952, 36427], []⟩,
        ⟨101212, true, false, [], [36427, 85889]⟩,
        ⟨101321, true, false, [], [85889]⟩
      ]⟩,
    ⟨[37011], [37008], .source 18570⟩,
    ⟨[85889, 13], [37011, 92915], .contexts [
        ⟨101322, true, false, [37008], [13]⟩,
        ⟨59, false, false, [37008, 92915], []⟩,
        ⟨101323, true, false, [], [92915]⟩
      ]⟩,
    ⟨[89067, 1], [89065], .contexts [
        ⟨53961, false, false, [], []⟩,
        ⟨53962, false, false, [], []⟩,
        ⟨53874, false, false, [], []⟩,
        ⟨53874, false, false, [], []⟩
      ]⟩,
    ⟨[36961, 95437], [36961, 95437], .contexts []⟩,
    ⟨[36961, 95437], [36961, 95437], .contexts []⟩,
    ⟨[37013], [36961, 33707], .source 18571⟩,
    ⟨[95439], [36963, 89067], .contexts [
        ⟨101223, false, false, [], []⟩
      ]⟩,
    ⟨[36963, 89067], [36963, 89067], .contexts []⟩,
    ⟨[95439], [36963, 89067], .contexts [
        ⟨101329, false, false, [], []⟩,
        ⟨101330, false, false, [], []⟩
      ]⟩,
    ⟨[37015], [37013, 36963], .source 18572⟩,
    ⟨[37015, 89065], [37015, 89065], .contexts []⟩,
    ⟨[37015, 89065], [37015, 89065], .contexts []⟩,
    ⟨[89065, 9], [89065, 9], .contexts []⟩,
    ⟨[89065], [89065], .contexts []⟩,
    ⟨[89065, 9], [37015, 89065], .contexts [
        ⟨101335, false, false, [], []⟩,
        ⟨101325, true, false, [], [9]⟩,
        ⟨452, false, false, [89067], []⟩,
        ⟨455, false, false, [89067], []⟩,
        ⟨101226, false, false, [], [1, 9, 1]⟩,
        ⟨101326, false, false, [], [1, 9, 1]⟩,
        ⟨101327, false, false, [], [1, 9, 1]⟩,
        ⟨101327, false, false, [], [1, 9, 1]⟩,
        ⟨91878, false, false, [36961], [9, 1]⟩,
        ⟨101328, true, false, [], [95437, 9, 1]⟩,
        ⟨91883, false, false, [37013], [1]⟩,
        ⟨101331, false, false, [37013], [1]⟩,
        ⟨101332, true, false, [], [89067, 1]⟩,
        ⟨53875, false, false, [37015], []⟩,
        ⟨101333, false, false, [], []⟩,
        ⟨101334, false, false, [], []⟩,
        ⟨101336, false, false, [37015], []⟩
      ]⟩,
    ⟨[89065, 9], [37015, 89065], .contexts [
        ⟨101337, false, false, [], []⟩,
        ⟨13, true, false, [], [37015, 89065]⟩
      ]⟩,
    ⟨[36961, 95441], [36961, 95441], .contexts []⟩,
    ⟨[36961, 95441], [36961, 95441], .contexts []⟩,
    ⟨[89063, 1], [89063, 1], .contexts []⟩,
    ⟨[89063, 1], [36961, 95441], .contexts [
        ⟨101341, false, false, [], []⟩,
        ⟨53870, true, false, [], [1]⟩,
        ⟨53870, true, false, [], [1]⟩,
        ⟨53964, true, false, [], [1]⟩,
        ⟨53963, true, false, [], [1]⟩,
        ⟨101325, true, false, [], [11, 1]⟩,
        ⟨4506, false, false, [89067], []⟩,
        ⟨54, false, false, [89067], []⟩,
        ⟨101227, false, false, [], []⟩,
        ⟨101339, false, false, [], []⟩,
        ⟨101340, false, false, [], []⟩,
        ⟨101340, false, false, [], []⟩,
        ⟨91892, false, false, [36961], []⟩,
        ⟨13, true, false, [], [36961, 95441]⟩
      ]⟩,
    ⟨[36963], [36963], .contexts []⟩,
    ⟨[95443], [36963, 89063], .contexts [
        ⟨91899, true, false, [], []⟩,
        ⟨91899, true, false, [], []⟩,
        ⟨92082, true, false, [], []⟩,
        ⟨91896, true, false, [], []⟩,
        ⟨101342, true, false, [36960], [1]⟩,
        ⟨8, false, false, [36960, 89063], []⟩,
        ⟨101222, true, false, [], [89063]⟩,
        ⟨101343, true, false, [], [89063]⟩
      ]⟩,
    ⟨[89063, 13], [36961, 95445], .contexts [
        ⟨101344, true, false, [36962], [13]⟩,
        ⟨91898, false, false, [36962], []⟩,
        ⟨92081, false, false, [36962], []⟩,
        ⟨101225, true, false, [], [95445]⟩
      ]⟩,
    ⟨[36855, 95429], [36855, 95429], .contexts []⟩,
    ⟨[36855, 95429], [36855, 95429], .contexts []⟩,
    ⟨[95429, 5], [95429, 5], .contexts []⟩,
    ⟨[95429, 5], [36857, 96657], .contexts [
        ⟨101348, false, false, [], []⟩,
        ⟨101347, true, false, [36854], [5]⟩,
        ⟨101347, true, false, [36854], [5]⟩,
        ⟨101346, true, false, [36854], [5]⟩,
        ⟨101232, true, false, [36854], [5]⟩,
        ⟨101229, true, false, [36854], [5]⟩,
        ⟨98, false, false, [36854, 96653], []⟩,
        ⟨99, false, false, [36854, 96653], []⟩,
        ⟨100739, false, false, [36854], [1]⟩,
        ⟨100772, false, false, [36854], []⟩,
        ⟨99360, false, false, [36854], []⟩,
        ⟨99151, false, false, [36854], []⟩,
        ⟨99151, false, false, [36854], []⟩,
        ⟨100775, false, false, [36854], []⟩,
        ⟨101012, true, false, [], [96657]⟩,
        ⟨101012, true, false, [], [96657]⟩,
        ⟨101011, true, false, [], [96657]⟩
      ]⟩,
    ⟨[36967, 83447], [36967, 83447], .contexts []⟩,
    ⟨[36967, 83447], [36967, 83447], .contexts []⟩,
    ⟨[36967, 83445], [36967, 83445], .contexts []⟩,
    ⟨[83445, 9], [83445, 9], .contexts []⟩,
    ⟨[36966], [36966], .contexts []⟩,
    ⟨[83445, 9], [36969, 96655], .contexts [
        ⟨101353, false, false, [], []⟩,
        ⟨101352, true, false, [36966], [9]⟩,
        ⟨21225, true, false, [], [9]⟩,
        ⟨101351, true, false, [36966], [5, 9]⟩,
        ⟨101351, true, false, [36966], [5, 9]⟩,
        ⟨101350, true, false, [36966], [5, 9]⟩,
        ⟨101237, true, false, [36966], [5, 9]⟩,
        ⟨101235, true, false, [36966], [5, 9]⟩,
        ⟨598, false, false, [36966, 96653], []⟩,
        ⟨100740, false, false, [36966], []⟩,
        ⟨100739, false, false, [36966], []⟩,
        ⟨100742, false, false, [36966], []⟩,
        ⟨101354, true, false, [], [96655]⟩,
        ⟨101354, true, false, [], [96655]⟩,
        ⟨101238, true, false, [], [96655]⟩
      ]⟩,
    ⟨[36967], [36968], .contexts [
        ⟨101238, true, true, [], []⟩
      ]⟩,
    ⟨[96655, 9], [36967, 83445], .contexts [
        ⟨101355, true, false, [36968], [9]⟩,
        ⟨46, false, false, [36968, 83445], []⟩,
        ⟨101356, true, false, [], [83445]⟩
      ]⟩,
    ⟨[36975, 85283], [36975, 85283], .contexts []⟩,
    ⟨[94333, 5], [36975, 85283], .contexts [
        ⟨101262, false, false, [], []⟩,
        ⟨101264, false, false, [], []⟩,
        ⟨101358, false, false, [], []⟩,
        ⟨101358, false, false, [], []⟩
      ]⟩,
    ⟨[37017], [36975, 36473], .source 18573⟩,
    ⟨[37019], [37017, 36883], .source 18574⟩,
    ⟨[94333], [94333], .contexts []⟩,
    ⟨[90839, 9], [90839, 9], .contexts []⟩,
    ⟨[37021], [37018], .source 18575⟩,
    ⟨[37018], [37018], .contexts []⟩,
    ⟨[37021], [37018], .contexts [
        ⟨101364, false, false, [], []⟩,
        ⟨101365, false, false, [], []⟩,
        ⟨101365, false, false, [], []⟩
      ]⟩,
    ⟨[90839, 9], [37021, 94333], .contexts [
        ⟨101363, false, false, [], []⟩,
        ⟨101361, false, false, [37018], [90839, 9]⟩,
        ⟨101074, true, false, [37018, 37017], [9]⟩,
        ⟨101360, false, false, [37018], [85905, 5, 9]⟩,
        ⟨100264, true, false, [37018, 36975], [5, 9]⟩,
        ⟨101359, true, false, [37018], [9, 5, 9]⟩,
        ⟨882, false, false, [37018, 94333], []⟩,
        ⟨101362, false, false, [37018], []⟩,
        ⟨95130, false, false, [37018], []⟩,
        ⟨101366, true, false, [], [94333]⟩
      ]⟩,
    ⟨[37019], [37020], .contexts [
        ⟨101364, true, true, [], []⟩
      ]⟩,
    ⟨[37023], [36975, 24297], .source 18576⟩,
    ⟨[91839, 13], [91839, 13], .contexts []⟩,
    ⟨[37025], [37022], .source 18577⟩,
    ⟨[37022], [37022], .contexts []⟩,
    ⟨[91839, 13], [37025, 94333], .contexts [
        ⟨101370, false, false, [], []⟩,
        ⟨101369, false, false, [37022], [91839, 13]⟩,
        ⟨67842, true, false, [37022, 36975], [13]⟩,
        ⟨31016, true, false, [37022, 36975], [5, 13]⟩,
        ⟨101359, true, false, [37022], [13, 5, 13]⟩,
        ⟨4632, false, false, [37022, 94333], []⟩,
        ⟨101362, false, false, [37022], []⟩,
        ⟨95130, false, false, [37022], []⟩,
        ⟨101372, true, false, [], [94333]⟩,
        ⟨101372, true, false, [], [94333]⟩,
        ⟨101371, true, false, [], [94333]⟩
      ]⟩,
    ⟨[37023], [37024], .contexts [
        ⟨101371, true, true, [], []⟩
      ]⟩,
    ⟨[31367, 91961], [31367, 91961], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1584. -/
def y322TCIndexRaw1584 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[31367, 91961], [31367, 91961], .contexts []⟩,
    ⟨[36985, 92351], [36985, 92351], .contexts []⟩,
    ⟨[36985, 92351], [36985, 92351], .contexts []⟩,
    ⟨[91139, 1], [36985, 92351], .contexts [
        ⟨101283, false, false, [], []⟩,
        ⟨101377, false, false, [], []⟩,
        ⟨101378, false, false, [], []⟩,
        ⟨101378, false, false, [], []⟩
      ]⟩,
    ⟨[37027], [31369, 36985], .source 18578⟩,
    ⟨[91961, 1], [37027, 92353], .contexts [
        ⟨101376, true, false, [31366], [1]⟩,
        ⟨101376, true, false, [31366], [1]⟩,
        ⟨101375, true, false, [31366], [1]⟩,
        ⟨84443, true, false, [31366], [1]⟩,
        ⟨64585, true, false, [31366], [9, 1]⟩,
        ⟨64585, true, false, [31366], [9, 1]⟩,
        ⟨64584, true, false, [31366], [9, 1]⟩,
        ⟨64857, true, false, [31366], [9, 1]⟩,
        ⟨64593, true, false, [31366], [1, 9, 1]⟩,
        ⟨64593, true, false, [31366], [1, 9, 1]⟩,
        ⟨64856, true, false, [31366], [1, 9, 1]⟩,
        ⟨64855, true, false, [31366], [1, 9, 1]⟩,
        ⟨988, false, false, [31366, 91139], []⟩,
        ⟨692, false, false, [31366, 91139], []⟩,
        ⟨101379, false, false, [31366], [9]⟩,
        ⟨71436, false, false, [31366, 36985], []⟩,
        ⟨84403, true, false, [], [36985, 92353]⟩,
        ⟨101380, true, false, [], [92353]⟩
      ]⟩,
    ⟨[37029], [37026], .source 18579⟩,
    ⟨[37031], [27875, 37029], .source 18580⟩,
    ⟨[92357], [37031, 91961], .contexts [
        ⟨71983, true, false, [27872], []⟩,
        ⟨71983, true, false, [27872], []⟩,
        ⟨71982, true, false, [27872], []⟩,
        ⟨72010, true, false, [27872], []⟩,
        ⟨72008, true, false, [27872], []⟩,
        ⟨101381, true, false, [27872, 37026], [1]⟩,
        ⟨8, false, false, [27872, 37026, 91961], []⟩,
        ⟨101382, true, false, [27872], [91961]⟩,
        ⟨71987, true, false, [], [37029, 91961]⟩,
        ⟨101383, true, false, [], [91961]⟩
      ]⟩,
    ⟨[37033], [37030], .source 18581⟩,
    ⟨[37030], [37030], .contexts []⟩,
    ⟨[91961, 13], [37033, 92359], .contexts [
        ⟨101384, true, false, [37030], [13]⟩,
        ⟨71447, false, false, [37030], []⟩,
        ⟨71522, false, false, [37030], []⟩,
        ⟨101386, true, false, [], [92359]⟩,
        ⟨101386, true, false, [], [92359]⟩,
        ⟨101385, true, false, [], [92359]⟩
      ]⟩,
    ⟨[92357], [37031, 91961], .contexts [
        ⟨101384, false, false, [], []⟩
      ]⟩,
    ⟨[37035], [27875, 37031], .source 18582⟩,
    ⟨[37037], [37033, 37035], .source 18583⟩,
    ⟨[91963], [37037, 91961], .contexts [
        ⟨68853, true, false, [], []⟩,
        ⟨101388, true, false, [37030], [11]⟩,
        ⟨71990, false, false, [37030], []⟩,
        ⟨101388, false, false, [37030, 27875], []⟩,
        ⟨101389, true, false, [37030], [91961]⟩,
        ⟨101385, true, false, [], [37035, 91961]⟩,
        ⟨101390, true, false, [], [91961]⟩
      ]⟩,
    ⟨[37039], [37037, 37027], .source 18584⟩,
    ⟨[37041], [37038], .source 18585⟩,
    ⟨[92353], [37041, 91965], .contexts [
        ⟨101392, false, false, [37038], [92353]⟩,
        ⟨101381, true, false, [37038, 37037], []⟩,
        ⟨101391, true, false, [37038], [1]⟩,
        ⟨68856, false, false, [37038], []⟩,
        ⟨69048, false, false, [37038], []⟩,
        ⟨13, true, false, [37038], [91965]⟩,
        ⟨101393, true, false, [], [91965]⟩
      ]⟩,
    ⟨[37040], [37040], .contexts []⟩,
    ⟨[37039], [37040], .contexts [
        ⟨101393, true, true, [], []⟩,
        ⟨101395, false, false, [], []⟩
      ]⟩,
    ⟨[91965, 9], [37039, 92351], .contexts [
        ⟨101394, true, false, [37040], [9]⟩,
        ⟨71438, false, false, [37040], []⟩,
        ⟨71528, false, false, [37040], []⟩,
        ⟨101395, true, false, [], [92351]⟩,
        ⟨101396, true, false, [], [92351]⟩
      ]⟩,
    ⟨[37043], [27875, 37041], .source 18586⟩,
    ⟨[37045], [37039, 37043], .source 18587⟩,
    ⟨[92351, 11], [36983, 91143], .contexts [
        ⟨13, false, false, [36984], [36985, 92351, 11]⟩,
        ⟨101278, false, false, [36984], [92351, 11]⟩,
        ⟨101279, false, false, [36984], [92351, 11]⟩,
        ⟨101379, true, false, [36984], [11]⟩,
        ⟨9, true, false, [36984, 91139], [11]⟩,
        ⟨567, true, false, [36984, 91139], [11]⟩,
        ⟨84495, false, false, [36984], [1, 11, 11]⟩,
        ⟨64600, false, false, [36984], [11, 11]⟩,
        ⟨64851, false, false, [36984], [11, 11]⟩,
        ⟨64605, false, false, [36984], [11, 11]⟩,
        ⟨64605, false, false, [36984], [11, 11]⟩,
        ⟨53, false, false, [36984, 91143], []⟩,
        ⟨101280, true, false, [], [91143]⟩
      ]⟩,
    ⟨[87221, 11], [87223], .contexts [
        ⟨65336, false, false, [], []⟩,
        ⟨41062, false, false, [], []⟩,
        ⟨40784, false, false, [], []⟩,
        ⟨40784, false, false, [], []⟩
      ]⟩,
    ⟨[87223, 1], [87225], .contexts [
        ⟨40783, false, false, [], []⟩
      ]⟩,
    ⟨[87221, 1], [36993, 95341], .contexts [
        ⟨101296, false, false, [], []⟩
      ]⟩,
    ⟨[36993, 95341], [36993, 95341], .contexts []⟩,
    ⟨[36993, 95341], [36993, 95341], .contexts []⟩,
    ⟨[87221, 1], [36993, 95341], .contexts [
        ⟨101403, false, false, [], []⟩,
        ⟨101404, false, false, [], []⟩,
        ⟨101405, false, false, [], []⟩,
        ⟨101405, false, false, [], []⟩
      ]⟩,
    ⟨[87221, 0], [87221, 1], .contexts [
        ⟨9, false, false, [87221], []⟩
      ]⟩,
    ⟨[87225, 11], [87225, 11], .contexts []⟩,
    ⟨[87225, 11], [36993, 95341], .contexts [
        ⟨101408, false, false, [], []⟩,
        ⟨40788, true, false, [], [11]⟩,
        ⟨40788, true, false, [], [11]⟩,
        ⟨41060, true, false, [], [11]⟩,
        ⟨101402, true, false, [], [11]⟩,
        ⟨101401, true, false, [], [1, 11]⟩,
        ⟨567, false, false, [87221], []⟩,
        ⟨101407, false, false, [], []⟩,
        ⟨101406, false, false, [], []⟩,
        ⟨100007, false, false, [36993], []⟩,
        ⟨13, true, false, [], [36993, 95341]⟩
      ]⟩,
    ⟨[36991], [36992], .contexts [
        ⟨101293, true, true, [], []⟩
      ]⟩,
    ⟨[36991], [36991], .contexts []⟩,
    ⟨[95339], [36991, 87225], .contexts [
        ⟨100041, true, false, [], []⟩,
        ⟨101409, true, false, [36992], [11]⟩,
        ⟨53, false, false, [36992, 87225], []⟩,
        ⟨101410, true, false, [], [87225]⟩,
        ⟨101411, true, false, [], [87225]⟩
      ]⟩,
    ⟨[87225, 9], [36993, 95337], .contexts [
        ⟨101412, true, false, [36990], [9]⟩,
        ⟨89485, false, false, [36990], []⟩,
        ⟨89563, false, false, [36990], []⟩,
        ⟨101295, true, false, [], [95337]⟩
      ]⟩,
    ⟨[87221, 5], [33049, 89273], .contexts [
        ⟨90314, false, false, [], []⟩
      ]⟩,
    ⟨[87221, 5], [33049, 89273], .contexts [
        ⟨101414, false, false, [], []⟩,
        ⟨90301, false, false, [], []⟩,
        ⟨90302, false, false, [], []⟩,
        ⟨90302, false, false, [], []⟩
      ]⟩,
    ⟨[37047], [33049, 36995], .source 18588⟩,
    ⟨[87223, 5], [87223, 5], .contexts []⟩,
    ⟨[87223, 5], [37047, 84409], .contexts [
        ⟨101417, false, false, [], []⟩,
        ⟨101401, true, false, [], [5]⟩,
        ⟨642, false, false, [87221], []⟩,
        ⟨643, false, false, [87221], []⟩,
        ⟨101415, false, false, [], [11]⟩,
        ⟨101299, false, false, [33049], []⟩,
        ⟨101416, true, false, [], [84409]⟩,
        ⟨101297, false, false, [37047], []⟩,
        ⟨13, true, false, [], [37047, 84409]⟩
      ]⟩,
    ⟨[89271, 5], [89271, 5], .contexts []⟩,
    ⟨[37051], [33051, 36993], .source 18590⟩,
    ⟨[89271, 5], [37051, 95341], .contexts [
        ⟨101419, false, false, [], []⟩,
        ⟨90307, true, false, [33048], [5]⟩,
        ⟨90306, true, false, [33048], [5]⟩,
        ⟨90305, true, false, [33048], [5]⟩,
        ⟨90304, true, false, [33048], [5]⟩,
        ⟨101415, true, false, [33048], [1, 5]⟩,
        ⟨890, false, false, [33048, 87221], []⟩,
        ⟨101407, false, false, [33048], []⟩,
        ⟨101406, false, false, [33048], []⟩,
        ⟨100007, false, false, [33048, 36993], []⟩,
        ⟨90182, true, false, [], [36993, 95341]⟩,
        ⟨101420, true, false, [], [95341]⟩
      ]⟩,
    ⟨[37053], [37050], .source 18591⟩,
    ⟨[37001, 94277], [37001, 94277], .contexts []⟩,
    ⟨[37001, 94275], [37001, 94275], .contexts []⟩,
    ⟨[88309], [88309], .contexts []⟩,
    ⟨[37000], [37000], .contexts []⟩,
    ⟨[94275, 5], [37003, 88309], .contexts [
        ⟨101424, true, false, [37000], [5]⟩,
        ⟨83418, true, false, [], [5]⟩,
        ⟨101423, true, false, [37000], [1, 5]⟩,
        ⟨101423, true, false, [37000], [1, 5]⟩,
        ⟨101311, true, false, [37000], [1, 5]⟩,
        ⟨101308, true, false, [37000], [1, 5]⟩,
        ⟨890, false, false, [37000, 88311], []⟩,
        ⟨9, false, false, [37000, 88311], []⟩,
        ⟨49613, false, false, [37000], []⟩,
        ⟨49614, false, false, [37000], []⟩,
        ⟨49532, false, false, [37000], []⟩,
        ⟨49532, false, false, [37000], []⟩,
        ⟨101425, false, false, [37000], []⟩,
        ⟨101426, true, false, [], [88309]⟩,
        ⟨101426, true, false, [], [88309]⟩,
        ⟨101312, true, false, [], [88309]⟩
      ]⟩,
    ⟨[37009, 85889], [37009, 85889], .contexts []⟩,
    ⟨[37009, 85889], [37009, 85889], .contexts []⟩,
    ⟨[37055], [37009, 27141], .source 18592⟩,
    ⟨[37057], [37055, 37011], .source 18593⟩,
    ⟨[92915, 13, 1, 13, 1, 13], [37057, 92915], .contexts [
        ⟨101320, false, false, [], [1, 13, 1, 13]⟩,
        ⟨101322, false, false, [], [1, 13, 1, 13]⟩,
        ⟨101428, false, false, [], [1, 13, 1, 13]⟩,
        ⟨101429, false, false, [], [1, 13, 1, 13]⟩,
        ⟨101429, false, false, [], [1, 13, 1, 13]⟩,
        ⟨34143, false, false, [37009], [13, 1, 13]⟩,
        ⟨69386, false, false, [37009], [1, 13]⟩,
        ⟨101430, true, false, [], [85891, 1, 13]⟩,
        ⟨34145, false, false, [37055], [13]⟩,
        ⟨101324, false, false, [37055], []⟩,
        ⟨101431, true, false, [], [92915]⟩
      ]⟩,
    ⟨[37057, 92913], [37057, 92913], .contexts []⟩,
    ⟨[37057], [37057], .contexts []⟩,
    ⟨[37057], [37057], .contexts []⟩,
    ⟨[92915], [37057, 92913], .contexts [
        ⟨245, true, false, [92915], []⟩,
        ⟨101432, false, false, [], [1]⟩,
        ⟨75897, false, false, [37057], []⟩,
        ⟨101433, false, false, [], []⟩,
        ⟨101435, true, false, [], [92913]⟩,
        ⟨101434, true, false, [], [92913]⟩
      ]⟩,
    ⟨[37059], [37056], .source 18594⟩,
    ⟨[37059], [37056], .contexts [
        ⟨101437, false, false, [], []⟩
      ]⟩,
    ⟨[37056], [37056], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1585. -/
def y322TCIndexRaw1585 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[37061], [37059, 37009], .source 18595⟩,
    ⟨[92913, 13], [37061, 85889], .contexts [
        ⟨101436, true, false, [37056], [13]⟩,
        ⟨101322, false, false, [37056], []⟩,
        ⟨101428, false, false, [37056], []⟩,
        ⟨101437, true, false, [], [37009, 85889]⟩,
        ⟨101440, true, false, [], [85889]⟩
      ]⟩,
    ⟨[37061, 85889], [37061, 85889], .contexts []⟩,
    ⟨[37061, 85889], [37061, 85889], .contexts []⟩,
    ⟨[37063], [37061, 36439], .source 18596⟩,
    ⟨[92913, 5], [92911], .contexts [
        ⟨76010, false, false, [], []⟩,
        ⟨76011, false, false, [], []⟩,
        ⟨75892, false, false, [], []⟩,
        ⟨75892, false, false, [], []⟩
      ]⟩,
    ⟨[85897, 13], [85897, 13], .contexts []⟩,
    ⟨[92911], [92911], .contexts []⟩,
    ⟨[37065], [37062], .source 18597⟩,
    ⟨[37062], [37062], .contexts []⟩,
    ⟨[85897, 13], [37065, 92911], .contexts [
        ⟨101446, false, false, [], []⟩,
        ⟨101444, false, false, [37062], [85897, 13]⟩,
        ⟨100169, false, false, [37062, 37061], [85897, 13]⟩,
        ⟨100168, true, false, [37062, 37061, 27143], [13]⟩,
        ⟨69392, true, false, [37062, 37061], [13]⟩,
        ⟨101443, true, false, [37062], [5, 13]⟩,
        ⟨101443, true, false, [37062], [5, 13]⟩,
        ⟨101442, true, false, [37062], [5, 13]⟩,
        ⟨101441, true, false, [37062], [5, 13]⟩,
        ⟨1136, false, false, [37062, 92913], []⟩,
        ⟨29, false, false, [37062, 92913], []⟩,
        ⟨101445, false, false, [37062], []⟩,
        ⟨101447, false, false, [37062], []⟩,
        ⟨101449, true, false, [], [92911]⟩,
        ⟨101449, true, false, [], [92911]⟩,
        ⟨101448, true, false, [], [92911]⟩
      ]⟩,
    ⟨[37063], [37064], .contexts [
        ⟨101448, true, true, [], []⟩
      ]⟩,
    ⟨[92911, 13], [37063, 85897], .contexts [
        ⟨101450, true, false, [37064], [13]⟩,
        ⟨59, false, false, [37064, 85897], []⟩,
        ⟨101451, true, false, [], [85897]⟩
      ]⟩,
    ⟨[89065, 9], [37015, 89065], .contexts [
        ⟨101335, false, false, [], []⟩,
        ⟨101338, false, false, [], []⟩,
        ⟨101333, false, false, [], []⟩,
        ⟨101334, false, false, [], []⟩,
        ⟨101334, false, false, [], []⟩
      ]⟩,
    ⟨[37067], [37014], .source 18598⟩,
    ⟨[37014], [37014], .contexts []⟩,
    ⟨[37069], [36961, 33703], .source 18599⟩,
    ⟨[95443], [36963, 89063], .contexts [
        ⟨101344, false, false, [], []⟩
      ]⟩,
    ⟨[37071], [37069, 36963], .source 18600⟩,
    ⟨[37071, 89059], [37071, 89059], .contexts []⟩,
    ⟨[37071, 89059], [37071, 89059], .contexts []⟩,
    ⟨[89063, 1, 9, 1, 9, 1], [37071, 89059], .contexts [
        ⟨101341, false, false, [], [9, 1, 9, 1]⟩,
        ⟨101342, false, false, [], [9, 1, 9, 1]⟩,
        ⟨101339, false, false, [], [9, 1, 9, 1]⟩,
        ⟨101340, false, false, [], [9, 1, 9, 1]⟩,
        ⟨101340, false, false, [], [9, 1, 9, 1]⟩,
        ⟨91894, false, false, [36961], [1, 9, 1]⟩,
        ⟨101456, true, false, [], [95441, 1, 9, 1]⟩,
        ⟨91896, false, false, [37069], [9, 1]⟩,
        ⟨101457, false, false, [37069], [9, 1]⟩,
        ⟨101458, true, false, [], [89063, 9, 1]⟩,
        ⟨53867, false, false, [37071], [1]⟩,
        ⟨53864, false, false, [37071], []⟩,
        ⟨101459, false, false, [], []⟩,
        ⟨101460, false, false, [], []⟩
      ]⟩,
    ⟨[89063], [89063], .contexts []⟩,
    ⟨[37073], [37070], .source 18601⟩,
    ⟨[37073], [37070], .contexts [
        ⟨101463, false, false, [], []⟩
      ]⟩,
    ⟨[37070], [37070], .contexts []⟩,
    ⟨[37073], [37070], .contexts [
        ⟨101464, false, false, [], []⟩,
        ⟨101465, false, false, [], []⟩,
        ⟨101465, false, false, [], []⟩
      ]⟩,
    ⟨[89059, 9], [37073, 89063], .contexts [
        ⟨101461, true, false, [37070], [9]⟩,
        ⟨4283, false, false, [37070, 89063], []⟩,
        ⟨101462, false, false, [37070], []⟩,
        ⟨101466, true, false, [], [89063]⟩
      ]⟩,
    ⟨[37071], [37072], .contexts [
        ⟨101463, true, true, [], []⟩
      ]⟩,
    ⟨[89063, 9], [89061], .contexts [
        ⟨53965, false, false, [], []⟩
      ]⟩,
    ⟨[37071], [37071], .contexts []⟩,
    ⟨[37071], [37071], .contexts []⟩,
    ⟨[37071], [37071], .contexts []⟩,
    ⟨[89061], [37071, 89059], .contexts [
        ⟨53866, true, false, [], []⟩,
        ⟨53866, true, false, [], []⟩,
        ⟨53966, true, false, [], []⟩,
        ⟨101469, true, false, [], []⟩,
        ⟨101467, true, false, [37072], [9]⟩,
        ⟨46, false, false, [37072, 89059], []⟩,
        ⟨101468, true, false, [], [89059]⟩,
        ⟨101459, false, false, [], []⟩,
        ⟨101472, true, false, [], [89059]⟩,
        ⟨101471, true, false, [], [89059]⟩,
        ⟨101470, true, false, [], [89059]⟩
      ]⟩,
    ⟨[89061], [37071, 89059], .contexts [
        ⟨101473, false, false, [], []⟩
      ]⟩,
    ⟨[89061], [37071, 89059], .contexts [
        ⟨101474, false, false, [], []⟩,
        ⟨101460, false, false, [], []⟩
      ]⟩,
    ⟨[37075], [37073, 37067], .source 18602⟩,
    ⟨[37077], [37075, 37071], .source 18603⟩,
    ⟨[89059, 11], [37077, 89059], .contexts [
        ⟨101473, true, false, [37070], [11]⟩,
        ⟨53867, true, false, [37070], [11]⟩,
        ⟨53871, true, false, [37070], [9, 11]⟩,
        ⟨101453, true, false, [37070, 37014], [11, 9, 11]⟩,
        ⟨536, false, false, [37070, 37014, 89065], []⟩,
        ⟨537, false, false, [37070, 37014, 89065], []⟩,
        ⟨53963, false, false, [37070, 37014], [9]⟩,
        ⟨53964, false, false, [37070, 37014], [9]⟩,
        ⟨53870, false, false, [37070, 37014], [9]⟩,
        ⟨53870, false, false, [37070, 37014], [9]⟩,
        ⟨53965, false, false, [37070, 37014], []⟩,
        ⟨53966, false, false, [37070, 37014], []⟩,
        ⟨53866, false, false, [37070, 37014], []⟩,
        ⟨53866, false, false, [37070, 37014], []⟩,
        ⟨101455, true, false, [37070], [89061]⟩,
        ⟨101455, true, false, [37070], [89061]⟩,
        ⟨101454, true, false, [37070], [89061]⟩,
        ⟨101475, false, false, [37070, 37067], []⟩,
        ⟨101463, true, false, [], [37067, 37071, 89059]⟩,
        ⟨101476, true, false, [], [37071, 89059]⟩,
        ⟨101477, true, false, [], [89059]⟩
      ]⟩,
    ⟨[36857, 96657], [36857, 96657], .contexts []⟩,
    ⟨[95429, 5], [36857, 96657], .contexts [
        ⟨101348, false, false, [], []⟩,
        ⟨101349, false, false, [], []⟩,
        ⟨101479, false, false, [], []⟩,
        ⟨101479, false, false, [], []⟩
      ]⟩,
    ⟨[96659, 5], [96659, 5], .contexts []⟩,
    ⟨[37079], [36855, 26913], .source 18604⟩,
    ⟨[37079], [36856, 26913], .contexts [
        ⟨101482, false, false, [], []⟩,
        ⟨101230, false, false, [], [26913]⟩
      ]⟩,
    ⟨[96659, 5], [37079, 83691], .contexts [
        ⟨101481, false, false, [], []⟩,
        ⟨99150, true, false, [], [5]⟩,
        ⟨101480, true, false, [36856], [9, 5]⟩,
        ⟨960, false, false, [36856, 95429], []⟩,
        ⟨47, false, false, [36856, 95429], []⟩,
        ⟨91818, false, false, [36856], []⟩,
        ⟨43385, false, false, [36856, 26913], []⟩,
        ⟨101483, true, false, [], [83691]⟩
      ]⟩,
    ⟨[37081], [37078], .source 18605⟩,
    ⟨[96657, 13], [96657, 13], .contexts []⟩,
    ⟨[96657, 13], [37079, 90757], .contexts [
        ⟨101486, false, false, [], []⟩,
        ⟨101480, true, false, [36856], [13]⟩,
        ⟨179, false, false, [36856, 95429], []⟩,
        ⟨180, false, false, [36856, 95429], []⟩,
        ⟨91789, false, false, [36856], [5]⟩,
        ⟨91745, false, false, [36856], [5]⟩,
        ⟨91746, false, false, [36856], [5]⟩,
        ⟨91746, false, false, [36856], [5]⟩,
        ⟨91781, false, false, [36856], []⟩,
        ⟨91776, false, false, [36856], []⟩,
        ⟨91777, false, false, [36856], []⟩,
        ⟨91777, false, false, [36856], []⟩,
        ⟨91323, false, false, [36856, 26913], []⟩,
        ⟨101483, true, false, [], [90757]⟩
      ]⟩,
    ⟨[90757, 13], [37081, 96657], .contexts [
        ⟨101487, true, false, [37078], [13]⟩,
        ⟨59, false, false, [37078, 96657], []⟩,
        ⟨101485, true, false, [], [96657]⟩
      ]⟩,
    ⟨[36969, 96655], [36969, 96655], .contexts []⟩,
    ⟨[36969, 96655], [36969, 96655], .contexts []⟩,
    ⟨[36535, 85909], [36535, 85909], .contexts []⟩,
    ⟨[37083], [36535, 36515], .source 18606⟩,
    ⟨[96655, 7], [96655, 7], .contexts []⟩,
    ⟨[37085], [36967, 37083], .source 18607⟩,
    ⟨[96655, 7], [37085, 92291], .contexts [
        ⟨101493, false, false, [], []⟩,
        ⟨101490, true, false, [36968], [7]⟩,
        ⟨101490, true, false, [36968], [7]⟩,
        ⟨101489, true, false, [36968], [7]⟩,
        ⟨101355, true, false, [36968], [7]⟩,
        ⟨101353, true, false, [36968], [7]⟩,
        ⟨1084, false, false, [36968, 83445], []⟩,
        ⟨1085, false, false, [36968, 83445], []⟩,
        ⟨100354, false, false, [36968], [9]⟩,
        ⟨101491, false, false, [36968], [9]⟩,
        ⟨101491, false, false, [36968], [9]⟩,
        ⟨100330, false, false, [36968, 36535], []⟩,
        ⟨101492, true, false, [36968], [92291]⟩,
        ⟨90348, false, false, [36968, 37083], []⟩,
        ⟨101356, true, false, [], [37083, 92291]⟩,
        ⟨101494, true, false, [], [92291]⟩
      ]⟩,
    ⟨[37087], [37084], .source 18608⟩,
    ⟨[37021, 94333], [37021, 94333], .contexts []⟩,
    ⟨[90839, 9], [37021, 94333], .contexts [
        ⟨101363, false, false, [], []⟩,
        ⟨101367, false, false, [], []⟩,
        ⟨101497, false, false, [], []⟩,
        ⟨101497, false, false, [], []⟩
      ]⟩,
    ⟨[37089], [37021, 34815], .source 18609⟩,
    ⟨[91517, 9], [91517, 9], .contexts []⟩,
    ⟨[37091], [37088], .source 18610⟩,
    ⟨[37088], [37088], .contexts []⟩,
    ⟨[91517, 9], [37091, 90837], .contexts [
        ⟨101500, false, false, [], []⟩,
        ⟨66439, true, false, [], [9]⟩,
        ⟨101499, false, false, [37088], [91515, 1, 9]⟩,
        ⟨95122, true, false, [37088, 37021], [1, 9]⟩,
        ⟨83957, true, false, [37088, 37021], [9, 1, 9]⟩,
        ⟨101498, true, false, [37088], [1, 9, 1, 9]⟩,
        ⟨495, false, false, [37088, 90839], []⟩,
        ⟨68638, false, false, [37088], []⟩,
        ⟨68637, false, false, [37088], []⟩,
        ⟨68640, false, false, [37088], []⟩,
        ⟨101502, true, false, [], [90837]⟩,
        ⟨101502, true, false, [], [90837]⟩,
        ⟨101501, true, false, [], [90837]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1586. -/
def y322TCIndexRaw1586 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[37021, 94335], [37021, 94335], .contexts []⟩,
    ⟨[94335, 9], [94335, 9], .contexts []⟩,
    ⟨[37020], [37020], .contexts []⟩,
    ⟨[94335, 9], [37019, 90841], .contexts [
        ⟨101505, false, false, [], []⟩,
        ⟨101504, true, false, [37020], [9]⟩,
        ⟨83959, true, false, [], [9]⟩,
        ⟨101498, true, false, [37020], [3, 9]⟩,
        ⟨479, false, false, [37020, 90839], []⟩,
        ⟨21, false, false, [37020, 90839], []⟩,
        ⟨63044, false, false, [37020], []⟩,
        ⟨63117, false, false, [37020], []⟩,
        ⟨63049, false, false, [37020], []⟩,
        ⟨63049, false, false, [37020], []⟩,
        ⟨68612, false, false, [37020], []⟩,
        ⟨101506, true, false, [], [90841]⟩,
        ⟨101506, true, false, [], [90841]⟩,
        ⟨101368, true, false, [], [90841]⟩
      ]⟩,
    ⟨[37025, 94333], [37025, 94333], .contexts []⟩,
    ⟨[91839, 13], [37025, 94333], .contexts [
        ⟨101370, false, false, [], []⟩,
        ⟨101373, false, false, [], []⟩,
        ⟨101508, false, false, [], []⟩,
        ⟨101508, false, false, [], []⟩
      ]⟩,
    ⟨[37025, 94335], [37025, 94335], .contexts []⟩,
    ⟨[94335, 13], [94335, 13], .contexts []⟩,
    ⟨[37024], [37024], .contexts []⟩,
    ⟨[94335, 13], [37023, 91841], .contexts [
        ⟨101511, false, false, [], []⟩,
        ⟨101510, true, false, [37024], [13]⟩,
        ⟨83959, true, false, [], [13]⟩,
        ⟨101509, true, false, [37024], [3, 13]⟩,
        ⟨1132, false, false, [37024, 91839], []⟩,
        ⟨21, false, false, [37024, 91839], []⟩,
        ⟨67857, false, false, [37024], []⟩,
        ⟨67869, false, false, [37024], []⟩,
        ⟨101512, true, false, [], [91841]⟩,
        ⟨101512, true, false, [], [91841]⟩,
        ⟨101374, true, false, [], [91841]⟩
      ]⟩,
    ⟨[37093], [37025, 34811], .source 18611⟩,
    ⟨[37095], [37092], .source 18612⟩,
    ⟨[37097], [37095, 23013], .source 18613⟩,
    ⟨[95389, 13], [37097, 87065], .contexts [
        ⟨101514, false, false, [37092], [95389, 13]⟩,
        ⟨95133, true, false, [37092, 37025], [13]⟩,
        ⟨101509, true, false, [37092], [11, 13]⟩,
        ⟨931, false, false, [37092, 91839], []⟩,
        ⟨54, false, false, [37092, 91839], []⟩,
        ⟨67861, false, false, [37092], []⟩,
        ⟨57265, false, false, [37092, 23013], []⟩,
        ⟨101515, true, false, [], [23013, 87065]⟩,
        ⟨101516, true, false, [], [87065]⟩
      ]⟩,
    ⟨[37099], [37096], .source 18614⟩,
    ⟨[87065, 13], [37099, 95389], .contexts [
        ⟨101517, true, false, [37096], [13]⟩,
        ⟨59, false, false, [37096, 95389], []⟩,
        ⟨101518, true, false, [], [95389]⟩
      ]⟩,
    ⟨[91961, 3, 13], [26941, 37033, 92359], .contexts [
        ⟨68851, false, false, [], [13]⟩,
        ⟨68851, false, false, [], [13]⟩,
        ⟨68848, true, false, [], [3, 13]⟩,
        ⟨68848, true, false, [], [3, 13]⟩,
        ⟨68847, true, false, [], [3, 13]⟩,
        ⟨68845, true, false, [], [3, 13]⟩,
        ⟨196, false, false, [91959], [13]⟩,
        ⟨197, false, false, [91959], [13]⟩,
        ⟨68841, false, false, [], [9, 13]⟩,
        ⟨68842, false, false, [], [9, 13]⟩,
        ⟨68843, true, false, [], [91959, 9, 13]⟩,
        ⟨68839, false, false, [], [9, 13]⟩,
        ⟨68840, false, false, [], [9, 13]⟩,
        ⟨68840, false, false, [], [9, 13]⟩,
        ⟨68845, false, false, [26941], [13]⟩,
        ⟨68849, false, false, [], [13]⟩,
        ⟨68850, false, false, [], [13]⟩,
        ⟨68843, true, false, [], [91961, 13]⟩,
        ⟨68849, false, false, [], [13]⟩,
        ⟨68850, false, false, [], [13]⟩,
        ⟨68850, false, false, [], [13]⟩,
        ⟨101387, false, false, [26941], []⟩
      ]⟩,
    ⟨[37101], [26941, 37033], .source 18615⟩,
    ⟨[37033, 92359], [37033, 92359], .contexts []⟩,
    ⟨[37033, 92359], [37033, 92359], .contexts []⟩,
    ⟨[92359, 3], [92359, 3], .contexts []⟩,
    ⟨[37103], [37100], .source 18616⟩,
    ⟨[37105], [37103, 37033], .source 18617⟩,
    ⟨[37045, 91965], [37045, 91965], .contexts []⟩,
    ⟨[91965, 11], [37045, 91965], .contexts [
        ⟨101394, true, false, [37040], [11]⟩,
        ⟨71440, false, false, [37040], []⟩,
        ⟨71444, true, false, [37040], []⟩,
        ⟨71444, true, false, [37040], []⟩,
        ⟨71526, true, false, [37040], []⟩,
        ⟨71525, true, false, [37040], []⟩,
        ⟨72010, true, false, [37040, 27872], [1]⟩,
        ⟨8, false, false, [37040, 27872, 92353], []⟩,
        ⟨71987, true, false, [37040], [92353]⟩,
        ⟨72006, false, false, [37040], []⟩,
        ⟨71988, true, false, [37040], [92353]⟩,
        ⟨72007, false, false, [37040], []⟩,
        ⟨101394, false, false, [37040, 27875], []⟩,
        ⟨101398, true, false, [37040], [91965]⟩,
        ⟨101396, true, false, [], [37043, 91965]⟩,
        ⟨101399, true, false, [], [91965]⟩,
        ⟨101527, false, false, [], []⟩,
        ⟨101527, false, false, [], []⟩
      ]⟩,
    ⟨[37045, 91967], [37045, 91967], .contexts []⟩,
    ⟨[37045, 91967], [37045, 91967], .contexts []⟩,
    ⟨[91967, 11], [91967, 11], .contexts []⟩,
    ⟨[91967, 11], [37045, 91967], .contexts [
        ⟨101531, false, false, [], []⟩,
        ⟨68864, true, false, [], [11]⟩,
        ⟨68864, true, false, [], [11]⟩,
        ⟨69047, true, false, [], [11]⟩,
        ⟨68859, true, false, [], [11]⟩,
        ⟨82, false, false, [91965], []⟩,
        ⟨83, false, false, [91965], []⟩,
        ⟨101528, false, false, [], [13]⟩,
        ⟨68859, false, false, [37045], []⟩,
        ⟨101529, false, false, [], []⟩,
        ⟨101530, false, false, [], []⟩,
        ⟨13, true, false, [], [37045, 91967]⟩
      ]⟩,
    ⟨[37039, 92351], [37039, 92351], .contexts []⟩,
    ⟨[37107], [37039, 36983], .source 18618⟩,
    ⟨[37109], [37045, 37039], .source 18619⟩,
    ⟨[37111], [37109, 36983], .source 18620⟩,
    ⟨[91143, 9], [91143, 9], .contexts []⟩,
    ⟨[37113], [37106], .source 18621⟩,
    ⟨[37115], [37113, 37111], .source 18622⟩,
    ⟨[87225, 11], [36993, 95341], .contexts [
        ⟨101408, false, false, [], []⟩,
        ⟨101409, false, false, [], []⟩
      ]⟩,
    ⟨[37117], [36993, 36399], .source 18623⟩,
    ⟨[87225, 13], [87227], .contexts [
        ⟨40787, false, false, [], []⟩,
        ⟨41059, false, false, [], []⟩,
        ⟨40792, false, false, [], []⟩,
        ⟨40792, false, false, [], []⟩
      ]⟩,
    ⟨[85453, 11], [85453, 11], .contexts []⟩,
    ⟨[37119], [37116], .source 18624⟩,
    ⟨[37119], [37116], .contexts [
        ⟨101544, false, false, [], []⟩
      ]⟩,
    ⟨[37116], [37116], .contexts []⟩,
    ⟨[85453, 11], [37119, 87227], .contexts [
        ⟨101543, false, false, [], []⟩,
        ⟨101541, false, false, [37116], [85453, 11]⟩,
        ⟨100011, true, false, [37116, 36993], [11]⟩,
        ⟨101405, true, false, [37116], [13, 11]⟩,
        ⟨101405, true, false, [37116], [13, 11]⟩,
        ⟨101404, true, false, [37116], [13, 11]⟩,
        ⟨101540, true, false, [37116], [13, 11]⟩,
        ⟨619, false, false, [37116, 87225], []⟩,
        ⟨64, false, false, [37116, 87225], []⟩,
        ⟨101542, false, false, [37116], []⟩,
        ⟨101546, true, false, [], [87227]⟩,
        ⟨101546, true, false, [], [87227]⟩,
        ⟨101545, true, false, [], [87227]⟩
      ]⟩,
    ⟨[37117], [37118], .contexts [
        ⟨101544, true, true, [], []⟩
      ]⟩,
    ⟨[87227, 11], [37117, 85453], .contexts [
        ⟨101547, true, false, [37118], [11]⟩,
        ⟨53, false, false, [37118, 85453], []⟩,
        ⟨101548, true, false, [], [85453]⟩
      ]⟩,
    ⟨[37051, 95341], [37051, 95341], .contexts []⟩,
    ⟨[37051, 95341], [37051, 95341], .contexts []⟩,
    ⟨[37121], [37051, 36399], .source 18625⟩,
    ⟨[37121, 85451], [37121, 85451], .contexts []⟩,
    ⟨[37123], [37120], .source 18626⟩,
    ⟨[37120], [37120], .contexts []⟩,
    ⟨[85451, 13], [37123, 89271], .contexts [
        ⟨101553, true, false, [37120], [13]⟩,
        ⟨31987, true, false, [], [13]⟩,
        ⟨101552, false, false, [37120], [85453, 5, 13]⟩,
        ⟨100011, true, false, [37120, 37051], [5, 13]⟩,
        ⟨101551, true, false, [37120], [13, 5, 13]⟩,
        ⟨101551, true, false, [37120], [13, 5, 13]⟩,
        ⟨101550, true, false, [37120], [13, 5, 13]⟩,
        ⟨101421, true, false, [37120], [13, 5, 13]⟩,
        ⟨101419, true, false, [37120], [13, 5, 13]⟩,
        ⟨4632, false, false, [37120, 89271], []⟩,
        ⟨90310, false, false, [37120], []⟩,
        ⟨101555, true, false, [], [89271]⟩,
        ⟨101555, true, false, [], [89271]⟩,
        ⟨101554, true, false, [], [89271]⟩
      ]⟩,
    ⟨[92915], [37057, 92913], .contexts [
        ⟨101436, false, false, [], []⟩
      ]⟩,
    ⟨[92915], [37057, 92913], .contexts [
        ⟨101557, false, false, [], []⟩,
        ⟨101433, false, false, [], []⟩
      ]⟩,
    ⟨[92915], [37057, 92913], .contexts [
        ⟨101558, false, false, [], []⟩
      ]⟩,
    ⟨[37057, 92911], [37057, 92911], .contexts []⟩,
    ⟨[37057, 92911], [37057, 92911], .contexts []⟩,
    ⟨[92911, 1], [92911, 1], .contexts []⟩,
    ⟨[92911, 1], [37057, 92911], .contexts [
        ⟨101562, false, false, [], []⟩,
        ⟨101445, true, false, [], [1]⟩,
        ⟨161, false, false, [92913], []⟩,
        ⟨162, false, false, [92913], []⟩,
        ⟨75895, false, false, [], [5]⟩,
        ⟨101559, false, false, [], [5]⟩,
        ⟨101433, false, false, [], [5]⟩,
        ⟨101433, false, false, [], [5]⟩,
        ⟨75893, false, false, [37057], []⟩,
        ⟨101560, false, false, [], []⟩,
        ⟨101561, false, false, [], []⟩,
        ⟨101447, false, false, [37057], []⟩,
        ⟨101435, true, false, [], [92911]⟩,
        ⟨13, true, false, [], [37057, 92911]⟩
      ]⟩,
    ⟨[37065, 92911], [37065, 92911], .contexts []⟩,
    ⟨[37065, 92911], [37065, 92911], .contexts []⟩,
    ⟨[92909, 13], [92909, 13], .contexts []⟩,
    ⟨[37125], [37063, 27149], .source 18627⟩]

/-- Exact literal claimed equations and contextual derivations, block 1587. -/
def y322TCIndexRaw1587 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[92909, 13], [37125, 91955], .contexts [
        ⟨101566, false, false, [], []⟩,
        ⟨75889, true, false, [], [13]⟩,
        ⟨101565, true, false, [37064], [3, 13]⟩,
        ⟨101565, true, false, [37064], [3, 13]⟩,
        ⟨101564, true, false, [37064], [3, 13]⟩,
        ⟨101450, true, false, [37064], [3, 13]⟩,
        ⟨101446, true, false, [37064], [3, 13]⟩,
        ⟨1132, false, false, [37064, 85897], []⟩,
        ⟨21, false, false, [37064, 85897], []⟩,
        ⟨101175, false, false, [37064], []⟩,
        ⟨101176, false, false, [37064], []⟩,
        ⟨101177, false, false, [37064], []⟩,
        ⟨101177, false, false, [37064], []⟩,
        ⟨84433, false, false, [37064, 27149], []⟩,
        ⟨101451, true, false, [], [27149, 91955]⟩,
        ⟨101567, true, false, [], [91955]⟩
      ]⟩,
    ⟨[37127], [37124], .source 18628⟩,
    ⟨[37077, 89059], [37077, 89059], .contexts []⟩,
    ⟨[37077, 89059], [37077, 89059], .contexts []⟩,
    ⟨[89059, 5], [89057], .contexts [
        ⟨53969, false, false, [], []⟩,
        ⟨53970, false, false, [], []⟩,
        ⟨53859, false, false, [], []⟩,
        ⟨53859, false, false, [], []⟩
      ]⟩,
    ⟨[89057, 11], [89057, 11], .contexts []⟩,
    ⟨[89057], [89057], .contexts []⟩,
    ⟨[37129], [37076], .source 18629⟩,
    ⟨[37129], [37129], .contexts []⟩,
    ⟨[37076], [37076], .contexts []⟩,
    ⟨[37129], [37076], .contexts [
        ⟨101576, false, false, [], []⟩,
        ⟨101575, false, false, [], []⟩,
        ⟨101577, false, false, [], []⟩,
        ⟨101577, false, false, [], []⟩
      ]⟩,
    ⟨[89057, 11], [37129, 89057], .contexts [
        ⟨101573, false, false, [], []⟩,
        ⟨53860, true, false, [], [11]⟩,
        ⟨101571, true, false, [37076], [5, 11]⟩,
        ⟨101571, true, false, [37076], [5, 11]⟩,
        ⟨101570, true, false, [37076], [5, 11]⟩,
        ⟨101478, true, false, [37076], [5, 11]⟩,
        ⟨588, false, false, [37076, 89059], []⟩,
        ⟨29, false, false, [37076, 89059], []⟩,
        ⟨101572, false, false, [37076], []⟩,
        ⟨101574, false, false, [37076], []⟩,
        ⟨101578, true, false, [], [89057]⟩
      ]⟩,
    ⟨[89061], [37071, 89059], .contexts [
        ⟨101475, false, false, [], []⟩
      ]⟩,
    ⟨[37071, 89059, 5], [37071, 89057], .contexts [
        ⟨53860, false, false, [37071], []⟩
      ]⟩,
    ⟨[37071, 89057], [37071, 89057], .contexts []⟩,
    ⟨[37071, 89057], [37071, 89057], .contexts []⟩,
    ⟨[37071, 89057], [37071, 89057], .contexts []⟩,
    ⟨[89057, 1], [89057, 1], .contexts []⟩,
    ⟨[89057, 1], [37071, 89057], .contexts [
        ⟨101585, false, false, [], []⟩,
        ⟨101572, true, false, [], [1]⟩,
        ⟨161, false, false, [89059], []⟩,
        ⟨162, false, false, [89059], []⟩,
        ⟨53862, false, false, [], [5]⟩,
        ⟨101580, false, false, [], [5]⟩,
        ⟨101460, false, false, [], [5]⟩,
        ⟨101460, false, false, [], [5]⟩,
        ⟨101581, false, false, [], []⟩,
        ⟨101582, false, false, [], []⟩,
        ⟨101583, false, false, [], []⟩,
        ⟨101584, false, false, [], []⟩,
        ⟨101574, false, false, [37071], []⟩,
        ⟨101472, true, false, [], [89057]⟩,
        ⟨101471, true, false, [], [89057]⟩,
        ⟨13, true, false, [], [37071, 89057]⟩
      ]⟩,
    ⟨[37079, 83691], [37079, 83691], .contexts []⟩,
    ⟨[37079, 83691], [37079, 83691], .contexts []⟩,
    ⟨[96659, 5], [37079, 83691], .contexts [
        ⟨101481, false, false, [], []⟩,
        ⟨101484, false, false, [], []⟩,
        ⟨101587, false, false, [], []⟩,
        ⟨101588, false, false, [], []⟩,
        ⟨101588, false, false, [], []⟩
      ]⟩,
    ⟨[37131], [37079, 20903], .source 18630⟩,
    ⟨[96659, 11], [96661], .contexts [
        ⟨99154, false, false, [], []⟩,
        ⟨99358, false, false, [], []⟩,
        ⟨99159, false, false, [], []⟩,
        ⟨99159, false, false, [], []⟩
      ]⟩,
    ⟨[96659, 10], [96659, 11], .contexts [
        ⟨54, false, false, [96659], []⟩
      ]⟩,
    ⟨[83455, 5], [83455, 5], .contexts []⟩,
    ⟨[37133], [37130], .source 18631⟩,
    ⟨[37130], [37130], .contexts []⟩,
    ⟨[83455, 5], [37133, 96661], .contexts [
        ⟨101593, false, false, [], []⟩,
        ⟨101590, false, false, [37130], [83455, 5]⟩,
        ⟨43473, true, false, [37130, 37079], [5]⟩,
        ⟨101589, true, false, [37130], [11, 5]⟩,
        ⟨940, false, false, [37130, 96659], []⟩,
        ⟨101592, false, false, [37130], []⟩,
        ⟨101591, false, false, [37130], []⟩,
        ⟨100843, false, false, [37130], []⟩,
        ⟨101595, true, false, [], [96661]⟩,
        ⟨101595, true, false, [], [96661]⟩,
        ⟨101594, true, false, [], [96661]⟩
      ]⟩,
    ⟨[37131], [37132], .contexts [
        ⟨101594, true, true, [], []⟩
      ]⟩,
    ⟨[37079, 90755], [37079, 90755], .contexts []⟩,
    ⟨[37079, 90755], [37079, 90755], .contexts []⟩,
    ⟨[96659], [96659], .contexts []⟩,
    ⟨[90755, 13], [90755, 13], .contexts []⟩,
    ⟨[96659], [96659], .contexts []⟩,
    ⟨[37078], [37078], .contexts []⟩,
    ⟨[90755, 13], [37081, 96659], .contexts [
        ⟨101601, false, false, [], []⟩,
        ⟨101599, true, false, [37078], [13]⟩,
        ⟨101598, true, false, [37078], [13]⟩,
        ⟨62900, true, false, [], [13]⟩,
        ⟨22644, true, false, [], [5, 13]⟩,
        ⟨101589, true, false, [37078], [13, 5, 13]⟩,
        ⟨4632, false, false, [37078, 96659], []⟩,
        ⟨101600, false, false, [37078], []⟩,
        ⟨101602, false, false, [37078], []⟩,
        ⟨101603, true, false, [], [96659]⟩,
        ⟨101603, true, false, [], [96659]⟩,
        ⟨101485, true, false, [], [96659]⟩
      ]⟩,
    ⟨[37079], [37080], .contexts [
        ⟨101485, true, true, [], []⟩
      ]⟩,
    ⟨[96659, 13], [37079, 90755], .contexts [
        ⟨101604, true, false, [37080], [13]⟩,
        ⟨59, false, false, [37080, 90755], []⟩,
        ⟨101605, true, false, [], [90755]⟩
      ]⟩,
    ⟨[37135], [37079, 26865], .source 18632⟩,
    ⟨[86635, 15], [86635, 15], .contexts []⟩,
    ⟨[37137], [37134], .source 18633⟩,
    ⟨[37134], [37134], .contexts []⟩,
    ⟨[86635, 15], [37137, 96659], .contexts [
        ⟨101608, false, false, [], []⟩,
        ⟨101607, false, false, [37134], [86635, 15]⟩,
        ⟨68480, true, false, [37134, 37079], [15]⟩,
        ⟨22646, true, false, [37134, 37079], [5, 15]⟩,
        ⟨101589, true, false, [37134], [15, 5, 15]⟩,
        ⟨885, false, false, [37134, 96659], []⟩,
        ⟨101600, false, false, [37134], []⟩,
        ⟨101602, false, false, [37134], []⟩,
        ⟨101610, true, false, [], [96659]⟩,
        ⟨101610, true, false, [], [96659]⟩,
        ⟨101609, true, false, [], [96659]⟩
      ]⟩,
    ⟨[37079, 90757], [37079, 90757], .contexts []⟩,
    ⟨[37139], [37079, 33587], .source 18634⟩,
    ⟨[37141], [37139, 33583], .source 18635⟩,
    ⟨[37143], [37140], .source 18636⟩,
    ⟨[37140], [37140], .contexts []⟩,
    ⟨[88997, 3], [37143, 96657], .contexts [
        ⟨101614, false, false, [37140], [88997, 3]⟩,
        ⟨91319, true, false, [37140, 37139], [3]⟩,
        ⟨101613, false, false, [37140], [88991, 13, 3]⟩,
        ⟨91328, true, false, [37140, 37079], [13, 3]⟩,
        ⟨101612, true, false, [37140], [3, 13, 3]⟩,
        ⟨101612, true, false, [37140], [3, 13, 3]⟩,
        ⟨101487, true, false, [37140], [3, 13, 3]⟩,
        ⟨101486, true, false, [37140], [3, 13, 3]⟩,
        ⟨4550, false, false, [37140, 96657], []⟩,
        ⟨100775, false, false, [37140], []⟩,
        ⟨101616, true, false, [], [96657]⟩,
        ⟨101616, true, false, [], [96657]⟩,
        ⟨101615, true, false, [], [96657]⟩
      ]⟩,
    ⟨[37085, 92291], [37085, 92291], .contexts []⟩,
    ⟨[37084], [37084], .contexts []⟩,
    ⟨[92289, 7], [37087, 96657], .contexts [
        ⟨71328, true, false, [], [7]⟩,
        ⟨101618, true, false, [37084], [1, 7]⟩,
        ⟨101618, true, false, [37084], [1, 7]⟩,
        ⟨101495, true, false, [37084], [1, 7]⟩,
        ⟨101493, true, false, [37084], [1, 7]⟩,
        ⟨502, false, false, [37084, 96655], []⟩,
        ⟨100774, false, false, [37084], []⟩,
        ⟨100773, false, false, [37084], []⟩,
        ⟨100775, false, false, [37084], []⟩,
        ⟨101619, true, false, [], [96657]⟩,
        ⟨101619, true, false, [], [96657]⟩,
        ⟨101496, true, false, [], [96657]⟩
      ]⟩,
    ⟨[37091, 90837], [37091, 90837], .contexts []⟩,
    ⟨[37091, 90837], [37091, 90837], .contexts []⟩,
    ⟨[37145], [37091, 26915], .source 18637⟩,
    ⟨[37147], [33021, 37091], .source 18638⟩,
    ⟨[37149], [37147, 26915], .source 18639⟩,
    ⟨[86647, 9], [86647, 9], .contexts []⟩,
    ⟨[37151], [37144], .source 18640⟩,
    ⟨[37153], [37151, 37149], .source 18641⟩,
    ⟨[86647, 9], [37153, 86647], .contexts [
        ⟨101626, false, false, [], []⟩,
        ⟨101623, false, false, [37144], [86647, 9]⟩,
        ⟨68642, true, false, [37144, 37091], [9]⟩,
        ⟨101622, true, false, [37144], [11, 9]⟩,
        ⟨101622, true, false, [37144], [11, 9]⟩,
        ⟨101621, true, false, [37144], [11, 9]⟩,
        ⟨101503, true, false, [37144], [11, 9]⟩,
        ⟨101500, true, false, [37144], [11, 9]⟩,
        ⟨10202, false, false, [37144, 91517], []⟩,
        ⟨2345, false, false, [37144, 91517], []⟩,
        ⟨90331, false, false, [37144], [9, 11]⟩,
        ⟨101503, false, false, [37144, 33021], [11]⟩,
        ⟨101624, true, false, [37144], [90837, 11]⟩,
        ⟨68642, false, false, [37144, 37147], []⟩,
        ⟨101625, true, false, [37144], [86647]⟩,
        ⟨101627, true, false, [], [37149, 86647]⟩,
        ⟨101628, true, false, [], [86647]⟩
      ]⟩,
    ⟨[94335, 9], [37019, 90841], .contexts [
        ⟨101505, false, false, [], []⟩,
        ⟨101507, false, false, [], []⟩
      ]⟩,
    ⟨[37019, 90841], [37019, 90841], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1588. -/
def y322TCIndexRaw1588 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[37019, 90843], [37019, 90843], .contexts []⟩,
    ⟨[90843, 9], [90843, 9], .contexts []⟩,
    ⟨[90843, 9], [37021, 94337], .contexts [
        ⟨101633, false, false, [], []⟩,
        ⟨101632, true, false, [37018], [9]⟩,
        ⟨63048, true, false, [], [9]⟩,
        ⟨101631, true, false, [37018], [5, 9]⟩,
        ⟨101631, true, false, [37018], [5, 9]⟩,
        ⟨101630, true, false, [37018], [5, 9]⟩,
        ⟨598, false, false, [37018, 94335], []⟩,
        ⟨95142, false, false, [37018], []⟩,
        ⟨95141, false, false, [37018], []⟩,
        ⟨95144, false, false, [37018], []⟩,
        ⟨101366, true, false, [], [94337]⟩
      ]⟩,
    ⟨[37023, 91841], [37023, 91841], .contexts []⟩,
    ⟨[94335, 13], [37023, 91841], .contexts [
        ⟨101511, false, false, [], []⟩,
        ⟨101513, false, false, [], []⟩,
        ⟨101635, false, false, [], []⟩,
        ⟨101635, false, false, [], []⟩
      ]⟩,
    ⟨[37155], [37023, 26613], .source 18642⟩,
    ⟨[37155, 87079], [37155, 87079], .contexts []⟩,
    ⟨[37155, 87079], [37155, 87079], .contexts []⟩,
    ⟨[94335], [94335], .contexts []⟩,
    ⟨[94335], [94335], .contexts []⟩,
    ⟨[37157], [37154], .source 18643⟩,
    ⟨[37154], [37154], .contexts []⟩,
    ⟨[87079, 5], [37157, 94335], .contexts [
        ⟨101639, true, false, [37154], [5]⟩,
        ⟨101638, true, false, [37154], [5]⟩,
        ⟨40136, true, false, [], [5]⟩,
        ⟨101637, false, false, [37154], [87077, 13, 5]⟩,
        ⟨67873, true, false, [37154, 37023], [13, 5]⟩,
        ⟨101636, true, false, [37154], [5, 13, 5]⟩,
        ⟨1116, false, false, [37154, 94335], []⟩,
        ⟨101640, false, false, [37154], []⟩,
        ⟨101641, false, false, [37154], []⟩,
        ⟨101643, true, false, [], [94335]⟩,
        ⟨101643, true, false, [], [94335]⟩,
        ⟨101642, true, false, [], [94335]⟩
      ]⟩,
    ⟨[94337], [37155, 87079], .contexts [
        ⟨95141, true, false, [], []⟩,
        ⟨101644, true, false, [37156], [5]⟩,
        ⟨28, false, false, [37156, 87079], []⟩,
        ⟨101642, false, true, [], [87079]⟩,
        ⟨101638, false, false, [], []⟩
      ]⟩,
    ⟨[37159], [37157, 34811], .source 18644⟩,
    ⟨[87079, 11], [37159, 95393], .contexts [
        ⟨101645, true, false, [37154], [11]⟩,
        ⟨95145, true, false, [37154, 34808], [11]⟩,
        ⟨53, false, false, [37154, 34808, 95393], []⟩,
        ⟨95097, true, false, [37154], [95393]⟩,
        ⟨95139, false, false, [37154], []⟩,
        ⟨101642, true, false, [], [34811, 95393]⟩,
        ⟨101646, true, false, [], [95393]⟩
      ]⟩,
    ⟨[37161], [37157, 37019], .source 18645⟩,
    ⟨[94337], [37155, 87079], .contexts [
        ⟨101645, false, false, [], []⟩
      ]⟩,
    ⟨[94337], [37155, 87079], .contexts [
        ⟨101649, false, false, [], []⟩,
        ⟨101639, false, false, [], []⟩
      ]⟩,
    ⟨[37155, 87079, 1], [37155, 23091, 88571], .contexts [
        ⟨51782, false, false, [37155], []⟩
      ]⟩,
    ⟨[37155, 23091, 88571], [37155, 23091, 88571], .contexts []⟩,
    ⟨[37155, 23091, 88571], [37155, 23091, 88571], .contexts []⟩,
    ⟨[37163], [37155, 23091], .source 18646⟩,
    ⟨[37155, 23091, 88571], [37163, 88571], .contexts [
        ⟨101654, true, false, [], [88571]⟩
      ]⟩,
    ⟨[37165], [37162], .source 18647⟩,
    ⟨[37165], [37162], .contexts [
        ⟨101656, false, false, [], []⟩
      ]⟩,
    ⟨[94339], [37163, 88571], .contexts [
        ⟨101657, false, false, [37164], [94339]⟩,
        ⟨13, false, false, [37164, 37162], [94339]⟩,
        ⟨84185, true, false, [37164, 37162], []⟩,
        ⟨83966, true, false, [37164, 37162], []⟩,
        ⟨101650, false, false, [37164, 37162], [1]⟩,
        ⟨101651, false, false, [37164, 37162], []⟩,
        ⟨101652, false, false, [37164, 37162], []⟩,
        ⟨101653, false, false, [37164, 37162], []⟩,
        ⟨101655, false, false, [37164, 37162], []⟩,
        ⟨101656, false, true, [], [88571]⟩
      ]⟩,
    ⟨[37162], [37162], .contexts []⟩,
    ⟨[88571, 9], [37165, 94341], .contexts [
        ⟨101658, true, false, [37162], [9]⟩,
        ⟨83969, false, false, [37162], []⟩,
        ⟨84184, false, false, [37162], []⟩,
        ⟨101659, true, false, [], [94341]⟩,
        ⟨101659, true, false, [], [94341]⟩,
        ⟨101657, true, false, [], [94341]⟩
      ]⟩,
    ⟨[37167], [37165, 34811], .source 18648⟩,
    ⟨[37169], [37023, 23013], .source 18649⟩,
    ⟨[37171], [37169, 24329], .source 18650⟩,
    ⟨[88005, 11], [88005, 11], .contexts []⟩,
    ⟨[37173], [37170], .source 18651⟩,
    ⟨[37173], [37170], .contexts [
        ⟨101665, false, false, [], []⟩
      ]⟩,
    ⟨[37170], [37170], .contexts []⟩,
    ⟨[88005, 11], [37173, 94335], .contexts [
        ⟨101664, false, false, [], []⟩,
        ⟨101663, false, false, [37170], [88005, 11]⟩,
        ⟨57304, true, false, [37170, 37169], [11]⟩,
        ⟨101662, false, false, [37170], [87067, 13, 11]⟩,
        ⟨67865, true, false, [37170, 37023], [13, 11]⟩,
        ⟨101636, true, false, [37170], [11, 13, 11]⟩,
        ⟨4838, false, false, [37170, 94335], []⟩,
        ⟨101640, false, false, [37170], []⟩,
        ⟨101641, false, false, [37170], []⟩,
        ⟨101667, true, false, [], [94335]⟩,
        ⟨101667, true, false, [], [94335]⟩,
        ⟨101666, true, false, [], [94335]⟩
      ]⟩,
    ⟨[37171], [37172], .contexts [
        ⟨101665, true, true, [], []⟩
      ]⟩,
    ⟨[37175], [34809, 37171], .source 18652⟩,
    ⟨[95391], [37175, 88005], .contexts [
        ⟨95138, true, false, [34810], []⟩,
        ⟨101668, true, false, [34810, 37172], [11]⟩,
        ⟨53, false, false, [34810, 37172, 88005], []⟩,
        ⟨101669, true, false, [34810], [88005]⟩,
        ⟨95102, true, false, [], [37171, 88005]⟩,
        ⟨101670, true, false, [], [88005]⟩
      ]⟩,
    ⟨[37177], [37174], .source 18653⟩,
    ⟨[37174], [37174], .contexts []⟩,
    ⟨[37177], [37174], .contexts [
        ⟨101672, false, false, [], []⟩,
        ⟨101673, false, false, [], []⟩,
        ⟨101673, false, false, [], []⟩
      ]⟩,
    ⟨[88005, 5], [37177, 95393], .contexts [
        ⟨101671, true, false, [37174], [5]⟩,
        ⟨90582, false, false, [37174], []⟩,
        ⟨90640, false, false, [37174], []⟩,
        ⟨101674, true, false, [], [95393]⟩
      ]⟩,
    ⟨[37105, 92359], [37105, 92359], .contexts []⟩,
    ⟨[37179], [37105, 27847], .source 18654⟩,
    ⟨[92359, 3, 1, 3], [37179, 92363, 3], .contexts [
        ⟨101524, false, false, [], [1, 3]⟩,
        ⟨101524, false, false, [], [1, 3]⟩,
        ⟨101521, false, false, [37100], [92359, 3, 1, 3]⟩,
        ⟨101520, true, false, [37100], [3, 1, 3]⟩,
        ⟨514, false, false, [37100, 91961], [1, 3]⟩,
        ⟨64, false, false, [37100, 91961], [1, 3]⟩,
        ⟨101387, false, false, [37100], [1, 3]⟩,
        ⟨101522, false, false, [37100], [1, 3]⟩,
        ⟨101523, false, false, [37100], [1, 3]⟩,
        ⟨101523, false, false, [37100], [1, 3]⟩,
        ⟨101525, true, false, [], [37033, 92359, 1, 3]⟩,
        ⟨101526, true, false, [], [92359, 1, 3]⟩,
        ⟨101676, false, false, [], [1, 3]⟩,
        ⟨101676, false, false, [], [1, 3]⟩,
        ⟨71973, false, false, [37105], [3]⟩,
        ⟨101677, true, false, [], [92363, 3]⟩
      ]⟩,
    ⟨[92365, 1], [92365, 1], .contexts []⟩,
    ⟨[37181], [37178], .source 18655⟩,
    ⟨[37183], [37181, 27847], .source 18656⟩,
    ⟨[91967, 15], [91969], .contexts [
        ⟨68863, false, false, [], []⟩
      ]⟩,
    ⟨[91969, 11], [91969, 11], .contexts []⟩,
    ⟨[37185], [37044], .source 18657⟩,
    ⟨[37044], [37044], .contexts []⟩,
    ⟨[37185], [37044], .contexts [
        ⟨101684, false, false, [], []⟩,
        ⟨101685, false, false, [], []⟩,
        ⟨101685, false, false, [], []⟩
      ]⟩,
    ⟨[37115, 91143], [37115, 91143], .contexts []⟩,
    ⟨[91143, 9], [37115, 91143], .contexts [
        ⟨101537, false, false, [], []⟩,
        ⟨101537, false, false, [], []⟩,
        ⟨101534, false, false, [37106], [91143, 9]⟩,
        ⟨101400, true, false, [37106, 37039], [9]⟩,
        ⟨101533, true, false, [37106], [11, 9]⟩,
        ⟨101533, true, false, [37106], [11, 9]⟩,
        ⟨101397, true, false, [37106], [11, 9]⟩,
        ⟨10202, false, false, [37106, 91965], []⟩,
        ⟨2345, false, false, [37106, 91965], []⟩,
        ⟨101528, false, false, [37106], [9, 11]⟩,
        ⟨101397, false, false, [37106, 37045], [11]⟩,
        ⟨101535, true, false, [37106], [92351, 11]⟩,
        ⟨101400, false, false, [37106, 37109], []⟩,
        ⟨101536, true, false, [37106], [91143]⟩,
        ⟨101538, true, false, [], [37111, 91143]⟩,
        ⟨101539, true, false, [], [91143]⟩,
        ⟨101687, false, false, [], []⟩,
        ⟨101687, false, false, [], []⟩
      ]⟩,
    ⟨[91145, 9], [91145, 9], .contexts []⟩,
    ⟨[91145], [91145], .contexts []⟩,
    ⟨[37187], [37114], .source 18658⟩,
    ⟨[37114], [37114], .contexts []⟩,
    ⟨[91145, 9], [37187, 91145], .contexts [
        ⟨101689, false, false, [], []⟩,
        ⟨64604, true, false, [], [9]⟩,
        ⟨101688, true, false, [37114], [13, 9]⟩,
        ⟨511, false, false, [37114, 91143], []⟩,
        ⟨64, false, false, [37114, 91143], []⟩,
        ⟨64604, false, false, [37114], []⟩,
        ⟨64849, false, false, [37114], []⟩,
        ⟨64609, false, false, [37114], []⟩,
        ⟨64609, false, false, [37114], []⟩,
        ⟨101690, false, false, [37114], []⟩,
        ⟨101692, true, false, [], [91145]⟩,
        ⟨101692, true, false, [], [91145]⟩,
        ⟨101691, true, false, [], [91145]⟩
      ]⟩,
    ⟨[37119, 87227], [37119, 87227], .contexts []⟩,
    ⟨[87229, 11], [87229, 11], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1589. -/
def y322TCIndexRaw1589 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[37189], [37117, 27399], .source 18659⟩,
    ⟨[87229, 11], [37189, 91593], .contexts [
        ⟨101695, false, false, [], []⟩,
        ⟨40791, true, false, [], [11]⟩,
        ⟨101694, true, false, [37118], [15, 11]⟩,
        ⟨101694, true, false, [37118], [15, 11]⟩,
        ⟨101547, true, false, [37118], [15, 11]⟩,
        ⟨101543, true, false, [37118], [15, 11]⟩,
        ⟨615, false, false, [37118, 85453], []⟩,
        ⟨10, false, false, [37118, 85453], []⟩,
        ⟨70318, false, false, [37118], []⟩,
        ⟨70313, false, false, [37118, 27399], []⟩,
        ⟨101548, true, false, [], [27399, 91593]⟩,
        ⟨101696, true, false, [], [91593]⟩
      ]⟩,
    ⟨[37191], [37188], .source 18660⟩,
    ⟨[91593, 11], [37191, 87229], .contexts [
        ⟨101697, true, false, [37188], [11]⟩,
        ⟨53, false, false, [37188, 87229], []⟩,
        ⟨101698, true, false, [], [87229]⟩
      ]⟩,
    ⟨[92907, 3], [92907, 3], .contexts []⟩,
    ⟨[92907, 3], [37059, 92907], .contexts [
        ⟨101700, false, false, [], []⟩,
        ⟨75885, true, false, [], [3]⟩,
        ⟨75889, true, false, [], [1, 3]⟩,
        ⟨101561, true, false, [37056], [3, 1, 3]⟩,
        ⟨101561, true, false, [37056], [3, 1, 3]⟩,
        ⟨101560, true, false, [37056], [3, 1, 3]⟩,
        ⟨101563, true, false, [37056], [3, 1, 3]⟩,
        ⟨101562, true, false, [37056], [3, 1, 3]⟩,
        ⟨484, false, false, [37056, 92911], []⟩,
        ⟨485, false, false, [37056, 92911], []⟩,
        ⟨76012, false, false, [37056], [1]⟩,
        ⟨76013, false, false, [37056], [1]⟩,
        ⟨75888, false, false, [37056], [1]⟩,
        ⟨75888, false, false, [37056], [1]⟩,
        ⟨76014, false, false, [37056], []⟩,
        ⟨76015, false, false, [37056], []⟩,
        ⟨75884, false, false, [37056], []⟩,
        ⟨75884, false, false, [37056], []⟩,
        ⟨101439, true, false, [], [92907]⟩,
        ⟨101439, true, false, [], [92907]⟩,
        ⟨101438, true, false, [], [92907]⟩
      ]⟩,
    ⟨[37125, 91955], [37125, 91955], .contexts []⟩,
    ⟨[37193], [37125, 35811], .source 18661⟩,
    ⟨[37193, 93657], [37193, 93657], .contexts []⟩,
    ⟨[93657, 11], [93657, 11], .contexts []⟩,
    ⟨[92909], [92909], .contexts []⟩,
    ⟨[37195], [37192], .source 18662⟩,
    ⟨[37195], [37195], .contexts []⟩,
    ⟨[37195], [37192], .contexts [
        ⟨101708, false, false, [], []⟩,
        ⟨101707, false, false, [], []⟩
      ]⟩,
    ⟨[37192], [37192], .contexts []⟩,
    ⟨[93657, 11], [37195, 92909], .contexts [
        ⟨101705, false, false, [], []⟩,
        ⟨101704, true, false, [37192], [11]⟩,
        ⟨80233, true, false, [], [11]⟩,
        ⟨101703, false, false, [37192], [93659, 13, 11]⟩,
        ⟨98282, true, false, [37192, 37125], [13, 11]⟩,
        ⟨101702, true, false, [37192], [11, 13, 11]⟩,
        ⟨101702, true, false, [37192], [11, 13, 11]⟩,
        ⟨101568, true, false, [37192], [11, 13, 11]⟩,
        ⟨101566, true, false, [37192], [11, 13, 11]⟩,
        ⟨4838, false, false, [37192, 92909], []⟩,
        ⟨101706, false, false, [37192], []⟩,
        ⟨101710, true, false, [], [92909]⟩,
        ⟨101710, true, false, [], [92909]⟩,
        ⟨101709, true, false, [], [92909]⟩
      ]⟩,
    ⟨[37193], [37194], .contexts [
        ⟨101707, true, true, [], []⟩
      ]⟩,
    ⟨[37129, 89057], [37129, 89057], .contexts []⟩,
    ⟨[37129, 89057], [37129, 89057], .contexts []⟩,
    ⟨[89057, 3], [89055], .contexts [
        ⟨53971, false, false, [], []⟩,
        ⟨53972, false, false, [], []⟩,
        ⟨53855, false, false, [], []⟩,
        ⟨53855, false, false, [], []⟩
      ]⟩,
    ⟨[89055, 11], [89055, 11], .contexts []⟩,
    ⟨[89055], [89055], .contexts []⟩,
    ⟨[37128], [37128], .contexts []⟩,
    ⟨[37077], [37128], .contexts [
        ⟨101575, true, true, [], []⟩,
        ⟨101718, false, false, [], []⟩,
        ⟨101718, false, false, [], []⟩
      ]⟩,
    ⟨[89055, 11], [37077, 89055], .contexts [
        ⟨101716, false, false, [], []⟩,
        ⟨53856, true, false, [], [11]⟩,
        ⟨101714, true, false, [37128], [3, 11]⟩,
        ⟨101714, true, false, [37128], [3, 11]⟩,
        ⟨101713, true, false, [37128], [3, 11]⟩,
        ⟨101579, true, false, [37128], [3, 11]⟩,
        ⟨101573, true, false, [37128], [3, 11]⟩,
        ⟨603, false, false, [37128, 89057], []⟩,
        ⟨21, false, false, [37128, 89057], []⟩,
        ⟨101715, false, false, [37128], []⟩,
        ⟨101717, false, false, [37128], []⟩,
        ⟨101719, true, false, [], [89055]⟩
      ]⟩,
    ⟨[89053, 3], [89053, 3], .contexts []⟩,
    ⟨[89053], [89053], .contexts []⟩,
    ⟨[89053, 3], [37073, 89053], .contexts [
        ⟨101721, false, false, [], []⟩,
        ⟨53852, true, false, [], [3]⟩,
        ⟨53856, true, false, [], [1, 3]⟩,
        ⟨101584, true, false, [37070], [3, 1, 3]⟩,
        ⟨101584, true, false, [37070], [3, 1, 3]⟩,
        ⟨101582, true, false, [37070], [3, 1, 3]⟩,
        ⟨101586, true, false, [37070], [3, 1, 3]⟩,
        ⟨101585, true, false, [37070], [3, 1, 3]⟩,
        ⟨484, false, false, [37070, 89057], []⟩,
        ⟨485, false, false, [37070, 89057], []⟩,
        ⟨101715, false, false, [37070], [1]⟩,
        ⟨53973, false, false, [37070], []⟩,
        ⟨53974, false, false, [37070], []⟩,
        ⟨53851, false, false, [37070], []⟩,
        ⟨53851, false, false, [37070], []⟩,
        ⟨101722, false, false, [37070], []⟩,
        ⟨101466, true, false, [], [89053]⟩
      ]⟩,
    ⟨[37133, 96661], [37133, 96661], .contexts []⟩,
    ⟨[83455, 5], [37133, 96661], .contexts [
        ⟨101593, false, false, [], []⟩,
        ⟨101596, false, false, [], []⟩,
        ⟨101724, false, false, [], []⟩,
        ⟨101724, false, false, [], []⟩
      ]⟩,
    ⟨[96663, 5], [96663, 5], .contexts []⟩,
    ⟨[37131], [37132], .contexts [
        ⟨101597, false, false, [], []⟩
      ]⟩,
    ⟨[37132], [37132], .contexts []⟩,
    ⟨[96663, 5], [37131, 83453], .contexts [
        ⟨101726, false, false, [], []⟩,
        ⟨99158, true, false, [], [5]⟩,
        ⟨101725, true, false, [37132], [1, 5]⟩,
        ⟨890, false, false, [37132, 83455], []⟩,
        ⟨49905, false, false, [37132], []⟩,
        ⟨43544, false, false, [37132], []⟩,
        ⟨49907, false, false, [37132], []⟩,
        ⟨101728, true, false, [], [83453]⟩,
        ⟨101728, true, false, [], [83453]⟩,
        ⟨101727, true, false, [], [83453]⟩
      ]⟩,
    ⟨[83453, 5], [37133, 96663], .contexts [
        ⟨101729, true, false, [37130], [5]⟩,
        ⟨28, false, false, [37130, 96663], []⟩,
        ⟨101594, true, false, [], [96663]⟩
      ]⟩,
    ⟨[37197], [31507, 36639], .source 18663⟩,
    ⟨[96661, 15], [96661, 15], .contexts []⟩,
    ⟨[37199], [37131, 37197], .source 18664⟩,
    ⟨[96661, 15], [37199, 92315], .contexts [
        ⟨101732, false, false, [], []⟩,
        ⟨101725, true, false, [37132], [15]⟩,
        ⟨184, false, false, [37132, 83455], []⟩,
        ⟨185, false, false, [37132, 83455], []⟩,
        ⟨85096, false, false, [37132], [5]⟩,
        ⟨100575, false, false, [37132, 31507], []⟩,
        ⟨101731, true, false, [37132], [92315]⟩,
        ⟨100615, false, false, [37132, 37197], []⟩,
        ⟨101727, true, false, [], [37197, 92315]⟩,
        ⟨101733, true, false, [], [92315]⟩
      ]⟩,
    ⟨[37201], [37198], .source 18665⟩,
    ⟨[37081, 96659], [37081, 96659], .contexts []⟩,
    ⟨[90755, 13], [37081, 96659], .contexts [
        ⟨101601, false, false, [], []⟩,
        ⟨101604, false, false, [], []⟩,
        ⟨101736, false, false, [], []⟩,
        ⟨101736, false, false, [], []⟩
      ]⟩,
    ⟨[96659, 3], [96659, 3], .contexts []⟩,
    ⟨[37079], [37080], .contexts [
        ⟨101605, false, false, [], []⟩
      ]⟩,
    ⟨[37203], [37079, 33559], .source 18666⟩,
    ⟨[96659, 3], [37203, 86129], .contexts [
        ⟨101738, false, false, [], []⟩,
        ⟨101737, true, false, [37080], [3]⟩,
        ⟨63, false, false, [37080, 90755], []⟩,
        ⟨65, false, false, [37080, 90755], []⟩,
        ⟨91423, false, false, [37080], [13]⟩,
        ⟨35519, false, false, [37080, 33559], []⟩,
        ⟨43579, false, false, [37080, 33559], []⟩,
        ⟨101739, true, false, [], [33559, 86129]⟩,
        ⟨101740, true, false, [], [86129]⟩
      ]⟩,
    ⟨[37205], [37202], .source 18667⟩,
    ⟨[37207], [28975, 36825], .source 18668⟩,
    ⟨[37209], [37079, 37207], .source 18669⟩,
    ⟨[96659, 7], [37209, 84991], .contexts [
        ⟨101737, true, false, [37080], [7]⟩,
        ⟨73, false, false, [37080, 90755], []⟩,
        ⟨74, false, false, [37080, 90755], []⟩,
        ⟨91425, false, false, [37080], [13]⟩,
        ⟨100946, false, false, [37080, 28975], []⟩,
        ⟨101743, true, false, [37080], [84991]⟩,
        ⟨75342, false, false, [37080, 37207], []⟩,
        ⟨101739, true, false, [], [37207, 84991]⟩,
        ⟨101744, true, false, [], [84991]⟩
      ]⟩,
    ⟨[37211], [37208], .source 18670⟩,
    ⟨[37137, 96659], [37137, 96659], .contexts []⟩,
    ⟨[37213], [37137, 37203], .source 18671⟩,
    ⟨[86131, 3], [86131, 3], .contexts []⟩,
    ⟨[37215], [37212], .source 18672⟩,
    ⟨[37212], [37212], .contexts []⟩,
    ⟨[86131, 3], [37215, 86635], .contexts [
        ⟨101749, false, false, [], []⟩,
        ⟨35523, true, false, [], [3]⟩,
        ⟨101748, false, false, [37212], [86129, 15, 3]⟩,
        ⟨101741, true, false, [37212, 37137], [15, 3]⟩,
        ⟨101747, true, false, [37212], [3, 15, 3]⟩,
        ⟨101747, true, false, [37212], [3, 15, 3]⟩,
        ⟨101611, true, false, [37212], [3, 15, 3]⟩,
        ⟨101608, true, false, [37212], [3, 15, 3]⟩,
        ⟨903, false, false, [37212, 86635], []⟩,
        ⟨90261, false, false, [37212], []⟩,
        ⟨90262, false, false, [37212], []⟩,
        ⟨101751, true, false, [], [86635]⟩,
        ⟨101751, true, false, [], [86635]⟩,
        ⟨101750, true, false, [], [86635]⟩
      ]⟩,
    ⟨[37153, 86647], [37153, 86647], .contexts []⟩,
    ⟨[37153, 86647], [37153, 86647], .contexts []⟩,
    ⟨[86645, 9], [86645, 9], .contexts []⟩,
    ⟨[37217], [37152], .source 18673⟩,
    ⟨[37152], [37152], .contexts []⟩,
    ⟨[37021, 94337], [37021, 37155, 87079], .contexts [
        ⟨101650, false, false, [37021], []⟩
      ]⟩,
    ⟨[37219], [37021, 37155], .source 18674⟩]

/-- Exact literal claimed equations and contextual derivations, block 1590. -/
def y322TCIndexRaw1590 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[90843, 9], [37219, 87079], .contexts [
        ⟨101633, false, false, [], []⟩,
        ⟨101634, false, false, [], []⟩,
        ⟨101758, false, false, [], []⟩,
        ⟨101759, true, false, [], [87079]⟩
      ]⟩,
    ⟨[37221], [37219, 23091], .source 18675⟩,
    ⟨[37223], [37221, 37165], .source 18676⟩,
    ⟨[94341, 1], [94341, 1], .contexts []⟩,
    ⟨[37225], [37222], .source 18677⟩,
    ⟨[37222], [37222], .contexts []⟩,
    ⟨[94341, 1], [37225, 90847], .contexts [
        ⟨101763, false, false, [], []⟩,
        ⟨101762, false, false, [37222], [94341, 1]⟩,
        ⟨101660, true, false, [37222, 37221], [1]⟩,
        ⟨101761, false, false, [37222], [88571, 9, 1]⟩,
        ⟨51782, true, false, [37222, 37219], [9, 1]⟩,
        ⟨101760, true, false, [37222], [1, 9, 1]⟩,
        ⟨988, false, false, [37222, 90843], []⟩,
        ⟨692, false, false, [37222, 90843], []⟩,
        ⟨63051, false, false, [37222], [9]⟩,
        ⟨63114, false, false, [37222], [9]⟩,
        ⟨63056, false, false, [37222], [9]⟩,
        ⟨63056, false, false, [37222], [9]⟩,
        ⟨63055, false, false, [37222], []⟩,
        ⟨63111, false, false, [37222], []⟩,
        ⟨63060, false, false, [37222], []⟩,
        ⟨63060, false, false, [37222], []⟩,
        ⟨66881, false, false, [37222], []⟩,
        ⟨101765, true, false, [], [90847]⟩,
        ⟨101765, true, false, [], [90847]⟩,
        ⟨101764, true, false, [], [90847]⟩
      ]⟩,
    ⟨[87081, 9], [87081, 9], .contexts []⟩,
    ⟨[37227], [37218], .source 18678⟩,
    ⟨[37229], [37227, 29315], .source 18679⟩,
    ⟨[87081, 9], [37229, 92931], .contexts [
        ⟨101767, false, false, [], []⟩,
        ⟨40140, true, false, [], [9]⟩,
        ⟨101760, true, false, [37218], [15, 9]⟩,
        ⟨935, false, false, [37218, 90843], []⟩,
        ⟨10, false, false, [37218, 90843], []⟩,
        ⟨76407, false, false, [37218], []⟩,
        ⟨76384, false, false, [37218, 29315], []⟩,
        ⟨101768, true, false, [], [29315, 92931]⟩,
        ⟨101769, true, false, [], [92931]⟩
      ]⟩,
    ⟨[37231], [37228], .source 18680⟩,
    ⟨[24353, 87069], [24353, 87069], .contexts []⟩,
    ⟨[24353, 87069], [24353, 87069], .contexts []⟩,
    ⟨[37159, 95393], [37159, 95393], .contexts []⟩,
    ⟨[37159, 95393], [37159, 95393], .contexts []⟩,
    ⟨[95393], [95393], .contexts []⟩,
    ⟨[37233], [24351, 37159], .source 18681⟩,
    ⟨[87069, 13], [37233, 95393], .contexts [
        ⟨101773, true, false, [24352], [13]⟩,
        ⟨101773, true, false, [24352], [13]⟩,
        ⟨101772, true, false, [24352], [13]⟩,
        ⟨57372, true, false, [24352], [13]⟩,
        ⟨40137, true, false, [24352], [11, 13]⟩,
        ⟨40137, true, false, [24352], [11, 13]⟩,
        ⟨40251, true, false, [24352], [11, 13]⟩,
        ⟨40138, true, false, [24352], [11, 13]⟩,
        ⟨931, false, false, [24352, 87079], []⟩,
        ⟨54, false, false, [24352, 87079], []⟩,
        ⟨101647, false, false, [24352], []⟩,
        ⟨101774, false, false, [24352], []⟩,
        ⟨101775, false, false, [24352], []⟩,
        ⟨101775, false, false, [24352], []⟩,
        ⟨101776, false, false, [24352, 37159], []⟩,
        ⟨57355, true, false, [], [37159, 95393]⟩,
        ⟨101777, true, false, [], [95393]⟩
      ]⟩,
    ⟨[37235], [37232], .source 18682⟩,
    ⟨[95393, 13], [37235, 87069], .contexts [
        ⟨101778, true, false, [37232], [13]⟩,
        ⟨59, false, false, [37232, 87069], []⟩,
        ⟨101779, true, false, [], [87069]⟩
      ]⟩,
    ⟨[37173, 94335], [37173, 94335], .contexts []⟩,
    ⟨[37173, 94335], [37173, 94335], .contexts []⟩,
    ⟨[88005, 1], [88003], .contexts [
        ⟨47881, false, false, [], []⟩,
        ⟨47882, false, false, [], []⟩,
        ⟨47693, false, false, [], []⟩,
        ⟨47693, false, false, [], []⟩
      ]⟩,
    ⟨[94335, 1], [94335, 1], .contexts []⟩,
    ⟨[37172], [37172], .contexts []⟩,
    ⟨[94335, 1], [37171, 88001], .contexts [
        ⟨101784, false, false, [], []⟩,
        ⟨101782, true, false, [37172], [1]⟩,
        ⟨101782, true, false, [37172], [1]⟩,
        ⟨101781, true, false, [37172], [1]⟩,
        ⟨101668, true, false, [37172], [1]⟩,
        ⟨101664, true, false, [37172], [1]⟩,
        ⟨562, false, false, [37172, 88005], []⟩,
        ⟨563, false, false, [37172, 88005], []⟩,
        ⟨101783, false, false, [37172], [11]⟩,
        ⟨47883, false, false, [37172], []⟩,
        ⟨47884, false, false, [37172], []⟩,
        ⟨47689, false, false, [37172], []⟩,
        ⟨47689, false, false, [37172], []⟩,
        ⟨96310, false, false, [37172], []⟩,
        ⟨101785, true, false, [], [88001]⟩,
        ⟨101785, true, false, [], [88001]⟩,
        ⟨101669, true, false, [], [88001]⟩
      ]⟩,
    ⟨[88001, 1], [37173, 94335], .contexts [
        ⟨101786, true, false, [37170], [1]⟩,
        ⟨8, false, false, [37170, 94335], []⟩,
        ⟨101665, true, false, [], [94335]⟩
      ]⟩,
    ⟨[37177, 95393], [37177, 95393], .contexts []⟩,
    ⟨[37177, 95393], [37177, 95393], .contexts []⟩,
    ⟨[37177, 95395], [37177, 95395], .contexts []⟩,
    ⟨[37177], [37177], .contexts []⟩,
    ⟨[37177], [37177], .contexts []⟩,
    ⟨[88003, 5], [37177, 95395], .contexts [
        ⟨101783, true, false, [], [5]⟩,
        ⟨98, false, false, [88005], []⟩,
        ⟨99, false, false, [88005], []⟩,
        ⟨101675, false, false, [], [1]⟩,
        ⟨101788, false, false, [], [1]⟩,
        ⟨101789, false, false, [], [1]⟩,
        ⟨101789, false, false, [], [1]⟩,
        ⟨90586, false, false, [37177], []⟩,
        ⟨101790, false, false, [], []⟩,
        ⟨95148, false, false, [37177], []⟩,
        ⟨101792, true, false, [], [95395]⟩,
        ⟨101791, true, false, [], [95395]⟩,
        ⟨13, true, false, [], [37177, 95395]⟩
      ]⟩,
    ⟨[95395, 5], [37175, 88003], .contexts [
        ⟨101793, true, false, [37176], [5]⟩,
        ⟨28, false, false, [37176, 88003], []⟩,
        ⟨101672, false, true, [], [88003]⟩
      ]⟩,
    ⟨[37183, 92365], [37183, 92365], .contexts []⟩,
    ⟨[92365, 1, 5], [37183, 92367], .contexts [
        ⟨101679, false, false, [], [5]⟩,
        ⟨101679, false, false, [], [5]⟩,
        ⟨71458, true, false, [], [1, 5]⟩,
        ⟨101678, true, false, [37178], [1, 5]⟩,
        ⟨1738, false, false, [37178, 92359], [5]⟩,
        ⟨131, false, false, [37178, 92359], [5]⟩,
        ⟨71972, false, false, [37178], [3, 5]⟩,
        ⟨71973, false, false, [37178], [3, 5]⟩,
        ⟨71946, false, false, [37178], [3, 5]⟩,
        ⟨71947, false, false, [37178], [3, 5]⟩,
        ⟨71947, false, false, [37178], [3, 5]⟩,
        ⟨71458, false, false, [37178, 27847], [5]⟩,
        ⟨71944, false, false, [37178], [5]⟩,
        ⟨71945, false, false, [37178], [5]⟩,
        ⟨71882, false, false, [37178, 27847], [5]⟩,
        ⟨101680, true, false, [], [27847, 92365, 5]⟩,
        ⟨101681, true, false, [], [92365, 5]⟩,
        ⟨101795, false, false, [], [5]⟩,
        ⟨101795, false, false, [], [5]⟩,
        ⟨71462, false, false, [37183], []⟩
      ]⟩,
    ⟨[37183, 92369], [37183, 92369], .contexts []⟩,
    ⟨[37237], [37182], .source 18683⟩,
    ⟨[37182], [37182], .contexts []⟩,
    ⟨[37183], [37236], .contexts [
        ⟨101798, true, true, [], []⟩
      ]⟩,
    ⟨[92367], [37183, 92369], .contexts [
        ⟨71467, true, false, [], []⟩,
        ⟨71467, true, false, [], []⟩,
        ⟨71514, true, false, [], []⟩,
        ⟨71462, true, false, [], []⟩,
        ⟨101798, false, false, [37236], [92365, 5]⟩,
        ⟨101799, false, false, [37236], [92365, 5]⟩,
        ⟨101799, false, false, [37236], [92365, 5]⟩,
        ⟨71882, true, false, [37236, 37182], [5]⟩,
        ⟨1152, true, false, [37236, 37182, 92365], [5]⟩,
        ⟨101796, false, false, [37236, 37182], [1, 5, 5]⟩,
        ⟨71466, false, false, [37236], [5, 5]⟩,
        ⟨101797, false, false, [37236, 37182], [5, 5]⟩,
        ⟨28, false, false, [37236, 92369], []⟩,
        ⟨101800, true, false, [], [92369]⟩,
        ⟨101797, false, false, [], []⟩
      ]⟩,
    ⟨[92369], [37237, 92367], .contexts [
        ⟨101801, true, false, [37182], []⟩,
        ⟨101798, true, false, [], [92367]⟩
      ]⟩,
    ⟨[37236], [37236], .contexts []⟩,
    ⟨[92369], [37237, 92367], .contexts [
        ⟨101802, false, false, [], []⟩
      ]⟩,
    ⟨[37185, 91969], [37185, 91969], .contexts []⟩,
    ⟨[91969, 11], [37185, 91969], .contexts [
        ⟨101683, false, false, [], []⟩,
        ⟨101683, false, false, [], []⟩,
        ⟨68863, true, false, [], [11]⟩,
        ⟨101530, true, false, [37044], [15, 11]⟩,
        ⟨101530, true, false, [37044], [15, 11]⟩,
        ⟨101529, true, false, [37044], [15, 11]⟩,
        ⟨101532, true, false, [37044], [15, 11]⟩,
        ⟨101531, true, false, [37044], [15, 11]⟩,
        ⟨615, false, false, [37044, 91967], []⟩,
        ⟨10, false, false, [37044, 91967], []⟩,
        ⟨101682, false, false, [37044], []⟩,
        ⟨69046, false, false, [37044], []⟩,
        ⟨68867, false, false, [37044], []⟩,
        ⟨68867, false, false, [37044], []⟩,
        ⟨101686, true, false, [], [91969]⟩,
        ⟨101805, false, false, [], []⟩,
        ⟨101805, false, false, [], []⟩
      ]⟩,
    ⟨[91971, 11], [91971, 11], .contexts []⟩,
    ⟨[37184], [37184], .contexts []⟩,
    ⟨[37045], [37184], .contexts [
        ⟨101684, true, true, [], []⟩,
        ⟨101808, false, false, [], []⟩,
        ⟨101808, false, false, [], []⟩
      ]⟩,
    ⟨[37187, 91145], [37187, 91145], .contexts []⟩,
    ⟨[37187, 91145], [37187, 91145], .contexts []⟩,
    ⟨[91145, 9], [37187, 91145], .contexts [
        ⟨101689, false, false, [], []⟩,
        ⟨101693, false, false, [], []⟩,
        ⟨101810, false, false, [], []⟩,
        ⟨101811, false, false, [], []⟩,
        ⟨101811, false, false, [], []⟩
      ]⟩,
    ⟨[37186], [37186], .contexts []⟩,
    ⟨[37189, 91593], [37189, 91593], .contexts []⟩,
    ⟨[87229, 1], [87231], .contexts [
        ⟨40795, false, false, [], []⟩
      ]⟩,
    ⟨[87229, 1], [87231], .contexts [
        ⟨101815, false, false, [], []⟩,
        ⟨41057, false, false, [], []⟩,
        ⟨40799, false, false, [], []⟩,
        ⟨40799, false, false, [], []⟩
      ]⟩,
    ⟨[91595, 11], [91595, 11], .contexts []⟩,
    ⟨[87231], [87231], .contexts []⟩,
    ⟨[37188], [37188], .contexts []⟩,
    ⟨[91595, 11], [37191, 87231], .contexts [
        ⟨101817, false, false, [], []⟩,
        ⟨66575, true, false, [], [11]⟩,
        ⟨101814, true, false, [37188], [1, 11]⟩,
        ⟨101814, true, false, [37188], [1, 11]⟩,
        ⟨101697, true, false, [37188], [1, 11]⟩,
        ⟨101695, true, false, [37188], [1, 11]⟩,
        ⟨567, false, false, [37188, 87229], []⟩,
        ⟨9, false, false, [37188, 87229], []⟩,
        ⟨101816, false, false, [37188], []⟩,
        ⟨101818, false, false, [37188], []⟩,
        ⟨101819, true, false, [], [87231]⟩,
        ⟨101819, true, false, [], [87231]⟩,
        ⟨101698, true, false, [], [87231]⟩
      ]⟩,
    ⟨[37189], [37190], .contexts [
        ⟨101698, true, true, [], []⟩
      ]⟩,
    ⟨[37059, 92907], [37059, 92907], .contexts []⟩,
    ⟨[92907, 3], [37059, 92907], .contexts [
        ⟨101700, false, false, [], []⟩,
        ⟨101701, false, false, [], []⟩,
        ⟨101822, false, false, [], []⟩,
        ⟨101822, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1591. -/
def y322TCIndexRaw1591 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[92907, 15], [92905], .contexts [
        ⟨76017, false, false, [], []⟩
      ]⟩,
    ⟨[37058], [37058], .contexts []⟩,
    ⟨[37195, 92909], [37195, 92909], .contexts []⟩,
    ⟨[37195, 92907], [37195, 92907], .contexts []⟩,
    ⟨[37195, 92907], [37195, 92907], .contexts []⟩,
    ⟨[93657, 1], [93655], .contexts [
        ⟨80279, false, false, [], []⟩
      ]⟩,
    ⟨[92907, 11], [92907, 11], .contexts []⟩,
    ⟨[93655], [93655], .contexts []⟩,
    ⟨[37193], [37194], .contexts [
        ⟨101712, false, false, [], []⟩
      ]⟩,
    ⟨[37194], [37194], .contexts []⟩,
    ⟨[92907, 11], [37193, 93655], .contexts [
        ⟨101830, false, false, [], []⟩,
        ⟨101828, true, false, [37194], [11]⟩,
        ⟨101827, true, false, [37194], [11]⟩,
        ⟨75885, true, false, [], [11]⟩,
        ⟨101826, true, false, [37194], [1, 11]⟩,
        ⟨101826, true, false, [37194], [1, 11]⟩,
        ⟨101711, true, false, [37194], [1, 11]⟩,
        ⟨101705, true, false, [37194], [1, 11]⟩,
        ⟨567, false, false, [37194, 93657], []⟩,
        ⟨9, false, false, [37194, 93657], []⟩,
        ⟨101829, false, false, [37194], []⟩,
        ⟨80280, false, false, [37194], []⟩,
        ⟨80228, false, false, [37194], []⟩,
        ⟨80228, false, false, [37194], []⟩,
        ⟨101831, false, false, [37194], []⟩,
        ⟨101833, true, false, [], [93655]⟩,
        ⟨101833, true, false, [], [93655]⟩,
        ⟨101832, true, false, [], [93655]⟩
      ]⟩,
    ⟨[93653], [37195, 92907], .contexts [
        ⟨80576, true, false, [], []⟩,
        ⟨101834, true, false, [37192], [11]⟩,
        ⟨53, false, false, [37192, 92907], []⟩,
        ⟨101707, true, false, [], [92907]⟩,
        ⟨101827, false, false, [], []⟩,
        ⟨101708, true, false, [], [92907]⟩
      ]⟩,
    ⟨[92907, 9], [37193, 93651], .contexts [
        ⟨101835, true, false, [37194], [9]⟩,
        ⟨80223, false, false, [37194], []⟩,
        ⟨80283, false, false, [37194], []⟩,
        ⟨101833, true, false, [], [93651]⟩,
        ⟨101833, true, false, [], [93651]⟩,
        ⟨101832, true, false, [], [93651]⟩
      ]⟩,
    ⟨[37239], [37193, 30471], .source 18684⟩,
    ⟨[92907, 13], [37239, 88947], .contexts [
        ⟨101835, true, false, [37194], [13]⟩,
        ⟨80580, true, false, [37194, 30468], [13]⟩,
        ⟨59, false, false, [37194, 30468, 88947], []⟩,
        ⟨80511, true, false, [37194], [88947]⟩,
        ⟨80575, false, false, [37194], []⟩,
        ⟨101712, true, false, [], [30471, 88947]⟩,
        ⟨101837, true, false, [], [88947]⟩
      ]⟩,
    ⟨[93653], [37195, 92907], .contexts [
        ⟨101835, false, false, [], []⟩
      ]⟩,
    ⟨[93653], [37195, 92907], .contexts [
        ⟨101839, false, false, [], []⟩,
        ⟨101828, false, false, [], []⟩
      ]⟩,
    ⟨[37241], [37193, 30485], .source 18685⟩,
    ⟨[92905], [37241, 89821], .contexts [
        ⟨75881, true, false, [], []⟩,
        ⟨101840, true, false, [37194], [15]⟩,
        ⟨80589, true, false, [37194, 30482], [15]⟩,
        ⟨1, false, false, [37194, 30482, 89821], []⟩,
        ⟨80543, true, false, [37194], [89821]⟩,
        ⟨80583, false, false, [37194], []⟩,
        ⟨101712, true, false, [], [30485, 89821]⟩,
        ⟨101841, true, false, [], [89821]⟩
      ]⟩,
    ⟨[37241, 89821], [37241, 89821], .contexts []⟩,
    ⟨[92905], [37241, 89821], .contexts [
        ⟨101842, false, false, [], []⟩,
        ⟨101843, false, false, [], []⟩
      ]⟩,
    ⟨[37243], [37240], .source 18686⟩,
    ⟨[37245], [37243, 37057], .source 18687⟩,
    ⟨[37247], [37245, 37241], .source 18688⟩,
    ⟨[89821, 3], [37247, 89821], .contexts [
        ⟨101842, true, false, [37240], [3]⟩,
        ⟨75881, true, false, [37240], [3]⟩,
        ⟨101823, true, false, [37240, 37058], [15, 3]⟩,
        ⟨499, false, false, [37240, 37058, 92907], []⟩,
        ⟨10, false, false, [37240, 37058, 92907], []⟩,
        ⟨101824, false, false, [37240, 37058], []⟩,
        ⟨76018, false, false, [37240, 37058], []⟩,
        ⟨75880, false, false, [37240, 37058], []⟩,
        ⟨75880, false, false, [37240, 37058], []⟩,
        ⟨101825, true, false, [37240], [92905]⟩,
        ⟨101825, true, false, [37240], [92905]⟩,
        ⟨101437, false, true, [37240], [92905]⟩,
        ⟨101434, true, false, [37240], [92905]⟩,
        ⟨101844, false, false, [37240, 37057], []⟩,
        ⟨101845, true, false, [], [37057, 37241, 89821]⟩,
        ⟨101846, true, false, [], [37241, 89821]⟩,
        ⟨101847, true, false, [], [89821]⟩
      ]⟩,
    ⟨[37249], [37241, 25343], .source 18689⟩,
    ⟨[37251], [37248], .source 18690⟩,
    ⟨[37251], [37248], .contexts [
        ⟨101850, false, false, [], []⟩
      ]⟩,
    ⟨[37249], [37250], .contexts [
        ⟨101850, true, true, [], []⟩
      ]⟩,
    ⟨[92903], [37249, 89821], .contexts [
        ⟨101851, false, false, [37250], [92903]⟩,
        ⟨13, false, false, [37250, 37248], [92903]⟩,
        ⟨76019, true, false, [37250, 37248], []⟩,
        ⟨75878, true, false, [37250, 37248], []⟩,
        ⟨101844, false, false, [37250, 37248], [13]⟩,
        ⟨62002, false, false, [37250, 37248, 37241], []⟩,
        ⟨101849, true, false, [37250, 37248], [89821]⟩,
        ⟨101852, true, false, [], [89821]⟩
      ]⟩,
    ⟨[37248], [37248], .contexts []⟩,
    ⟨[37251], [37248], .contexts [
        ⟨101851, false, false, [], []⟩,
        ⟨101854, false, false, [], []⟩,
        ⟨101854, false, false, [], []⟩
      ]⟩,
    ⟨[89821, 1], [37251, 92901], .contexts [
        ⟨101853, true, false, [37248], [1]⟩,
        ⟨75875, false, false, [37248], []⟩,
        ⟨76020, false, false, [37248], []⟩,
        ⟨101855, true, false, [], [92901]⟩
      ]⟩,
    ⟨[37077, 89055], [37077, 89055], .contexts []⟩,
    ⟨[37077, 89055], [37077, 89055], .contexts []⟩,
    ⟨[89053, 11], [89053, 11], .contexts []⟩,
    ⟨[89053, 11], [37129, 89053], .contexts [
        ⟨101859, false, false, [], []⟩,
        ⟨53852, true, false, [], [11]⟩,
        ⟨101858, true, false, [37076], [1, 11]⟩,
        ⟨101858, true, false, [37076], [1, 11]⟩,
        ⟨101857, true, false, [37076], [1, 11]⟩,
        ⟨101720, true, false, [37076], [1, 11]⟩,
        ⟨101716, true, false, [37076], [1, 11]⟩,
        ⟨567, false, false, [37076, 89055], []⟩,
        ⟨9, false, false, [37076, 89055], []⟩,
        ⟨53973, false, false, [37076], []⟩,
        ⟨53974, false, false, [37076], []⟩,
        ⟨53851, false, false, [37076], []⟩,
        ⟨53851, false, false, [37076], []⟩,
        ⟨101722, false, false, [37076], []⟩,
        ⟨101578, true, false, [], [89053]⟩
      ]⟩,
    ⟨[37073, 89053], [37073, 89053], .contexts []⟩,
    ⟨[37073, 89053], [37073, 89053], .contexts []⟩,
    ⟨[89053, 15], [89051], .contexts [
        ⟨53975, false, false, [], []⟩,
        ⟨53976, false, false, [], []⟩,
        ⟨53847, false, false, [], []⟩,
        ⟨53847, false, false, [], []⟩
      ]⟩,
    ⟨[89053, 14], [89053, 15], .contexts [
        ⟨10, false, false, [89053], []⟩
      ]⟩,
    ⟨[89051], [89051], .contexts []⟩,
    ⟨[37072], [37072], .contexts []⟩,
    ⟨[37131, 83453], [37131, 83453], .contexts []⟩,
    ⟨[37131, 83453], [37131, 83453], .contexts []⟩,
    ⟨[94539], [36639, 92311], .contexts [
        ⟨100545, false, false, [], []⟩
      ]⟩,
    ⟨[94539], [36639, 92311], .contexts [
        ⟨101869, false, false, [], []⟩
      ]⟩,
    ⟨[37199, 92313], [37199, 92313], .contexts []⟩,
    ⟨[96663], [96663], .contexts []⟩,
    ⟨[96663], [96663], .contexts []⟩,
    ⟨[37198], [37198], .contexts []⟩,
    ⟨[92313, 15], [37201, 96663], .contexts [
        ⟨101871, true, false, [37198], [15]⟩,
        ⟨71368, true, false, [], [15]⟩,
        ⟨101733, false, false, [37198], [92311, 5, 15]⟩,
        ⟨101731, false, false, [37198, 37131], [92311, 5, 15]⟩,
        ⟨101870, true, false, [37198, 37131, 31507], [5, 15]⟩,
        ⟨85101, true, false, [37198, 37131], [5, 15]⟩,
        ⟨101868, true, false, [37198], [15, 5, 15]⟩,
        ⟨101868, true, false, [37198], [15, 5, 15]⟩,
        ⟨101867, true, false, [37198], [15, 5, 15]⟩,
        ⟨101729, true, false, [37198], [15, 5, 15]⟩,
        ⟨101726, true, false, [37198], [15, 5, 15]⟩,
        ⟨885, false, false, [37198, 96663], []⟩,
        ⟨101872, false, false, [37198], []⟩,
        ⟨101873, false, false, [37198], []⟩,
        ⟨101874, true, false, [], [96663]⟩,
        ⟨101874, true, false, [], [96663]⟩,
        ⟨101735, true, false, [], [96663]⟩
      ]⟩,
    ⟨[37199, 92315], [37199, 92315], .contexts []⟩,
    ⟨[37253], [37199, 36709], .source 18691⟩,
    ⟨[90503, 7], [90503, 7], .contexts []⟩,
    ⟨[37255], [37252], .source 18692⟩,
    ⟨[37252], [37252], .contexts []⟩,
    ⟨[90503, 7], [37255, 96661], .contexts [
        ⟨101878, false, false, [], []⟩,
        ⟨61328, true, false, [], [7]⟩,
        ⟨101877, false, false, [37252], [90501, 15, 7]⟩,
        ⟨100673, true, true, [37252, 37199], [90501, 15, 7]⟩,
        ⟨38, true, false, [37252, 37199, 36710, 90501], [15, 7]⟩,
        ⟨100675, false, false, [37252, 37199, 36710], [7, 15, 7]⟩,
        ⟨101876, true, false, [37252], [7, 15, 7]⟩,
        ⟨101876, true, false, [37252], [7, 15, 7]⟩,
        ⟨101734, true, false, [37252], [7, 15, 7]⟩,
        ⟨101732, true, false, [37252], [7, 15, 7]⟩,
        ⟨2651, false, false, [37252, 96661], []⟩,
        ⟨100843, false, false, [37252], []⟩,
        ⟨101880, true, false, [], [96661]⟩,
        ⟨101880, true, false, [], [96661]⟩,
        ⟨101879, true, false, [], [96661]⟩
      ]⟩,
    ⟨[37203, 86129], [37203, 86129], .contexts []⟩,
    ⟨[37257], [37203, 22007], .source 18693⟩,
    ⟨[37259], [37256], .source 18694⟩,
    ⟨[37256], [37256], .contexts []⟩,
    ⟨[82957, 3], [37259, 96661], .contexts [
        ⟨101883, false, false, [37256], [82957, 3]⟩,
        ⟨47365, true, false, [37256, 37203], [3]⟩,
        ⟨101882, true, false, [37256], [11, 3]⟩,
        ⟨101882, true, false, [37256], [11, 3]⟩,
        ⟨101741, true, false, [37256], [11, 3]⟩,
        ⟨101738, true, false, [37256], [11, 3]⟩,
        ⟨545, false, false, [37256, 96659], []⟩,
        ⟨101592, false, false, [37256], []⟩,
        ⟨101591, false, false, [37256], []⟩,
        ⟨100843, false, false, [37256], []⟩,
        ⟨101885, true, false, [], [96661]⟩,
        ⟨101885, true, false, [], [96661]⟩,
        ⟨101884, true, false, [], [96661]⟩
      ]⟩,
    ⟨[96661, 3], [37257, 82957], .contexts [
        ⟨101886, true, false, [37258], [3]⟩,
        ⟨20, false, false, [37258, 82957], []⟩,
        ⟨101884, false, true, [], [82957]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1592. -/
def y322TCIndexRaw1592 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[37215, 86635], [37215, 86635], .contexts []⟩,
    ⟨[37215, 86635], [37215, 86635], .contexts []⟩,
    ⟨[86131, 3], [37215, 86635], .contexts [
        ⟨101749, false, false, [], []⟩,
        ⟨101752, false, false, [], []⟩,
        ⟨101888, false, false, [], []⟩,
        ⟨101889, false, false, [], []⟩,
        ⟨101889, false, false, [], []⟩
      ]⟩,
    ⟨[37261], [37215, 33087], .source 18695⟩,
    ⟨[37261, 88225], [37261, 88225], .contexts []⟩,
    ⟨[88225, 13], [88225, 13], .contexts []⟩,
    ⟨[37263], [37260], .source 18696⟩,
    ⟨[37260], [37260], .contexts []⟩,
    ⟨[88225, 13], [37263, 86131], .contexts [
        ⟨101893, false, false, [], []⟩,
        ⟨101892, true, false, [37260], [13]⟩,
        ⟨49359, true, false, [], [13]⟩,
        ⟨101891, false, false, [37260], [88223, 3, 13]⟩,
        ⟨90194, true, false, [37260, 37215], [3, 13]⟩,
        ⟨101890, true, false, [37260], [13, 3, 13]⟩,
        ⟨1930, false, false, [37260, 86131], []⟩,
        ⟨43635, false, false, [37260], []⟩,
        ⟨101895, true, false, [], [86131]⟩,
        ⟨101895, true, false, [], [86131]⟩,
        ⟨101894, true, false, [], [86131]⟩
      ]⟩,
    ⟨[37261], [37262], .contexts [
        ⟨101894, true, true, [], []⟩
      ]⟩,
    ⟨[37217, 86645], [37217, 86645], .contexts []⟩,
    ⟨[86645, 9], [37217, 86645], .contexts [
        ⟨101755, false, false, [], []⟩,
        ⟨101755, false, false, [], []⟩,
        ⟨38294, true, false, [], [9]⟩,
        ⟨101754, true, false, [37152], [15, 9]⟩,
        ⟨101754, true, false, [37152], [15, 9]⟩,
        ⟨101753, true, false, [37152], [15, 9]⟩,
        ⟨101629, true, false, [37152], [15, 9]⟩,
        ⟨101626, true, false, [37152], [15, 9]⟩,
        ⟨935, false, false, [37152, 86647], []⟩,
        ⟨68651, false, false, [37152], []⟩,
        ⟨68650, false, false, [37152], []⟩,
        ⟨68653, false, false, [37152], []⟩,
        ⟨101757, true, false, [], [86645]⟩,
        ⟨101757, true, false, [], [86645]⟩,
        ⟨101756, true, false, [], [86645]⟩,
        ⟨101898, false, false, [], []⟩,
        ⟨101898, false, false, [], []⟩
      ]⟩,
    ⟨[86643, 9], [86643, 9], .contexts []⟩,
    ⟨[37216], [37216], .contexts []⟩,
    ⟨[37225, 90847], [37225, 90847], .contexts []⟩,
    ⟨[94341, 1], [37225, 90847], .contexts [
        ⟨101763, false, false, [], []⟩,
        ⟨101766, false, false, [], []⟩,
        ⟨101902, false, false, [], []⟩,
        ⟨101902, false, false, [], []⟩
      ]⟩,
    ⟨[37265], [37225, 27335], .source 18697⟩,
    ⟨[37265, 85467], [37265, 85467], .contexts []⟩,
    ⟨[37265, 85467], [37265, 85467], .contexts []⟩,
    ⟨[94341], [94341], .contexts []⟩,
    ⟨[85467, 11], [85467, 11], .contexts []⟩,
    ⟨[94341], [94341], .contexts []⟩,
    ⟨[37267], [37264], .source 18698⟩,
    ⟨[37267], [37264], .contexts [
        ⟨101910, false, false, [], []⟩
      ]⟩,
    ⟨[37264], [37264], .contexts []⟩,
    ⟨[85467, 11], [37267, 94341], .contexts [
        ⟨101908, false, false, [], []⟩,
        ⟨101906, true, false, [37264], [11]⟩,
        ⟨101905, true, false, [37264], [11]⟩,
        ⟨32012, true, false, [], [11]⟩,
        ⟨101904, false, false, [37264], [85465, 1, 11]⟩,
        ⟨70130, true, false, [37264, 37225], [1, 11]⟩,
        ⟨63059, true, false, [37264, 37225], [1, 11]⟩,
        ⟨101903, true, false, [37264], [11, 1, 11]⟩,
        ⟨994, false, false, [37264, 94341], []⟩,
        ⟨101907, false, false, [37264], []⟩,
        ⟨101909, false, false, [37264], []⟩,
        ⟨101912, true, false, [], [94341]⟩,
        ⟨101912, true, false, [], [94341]⟩,
        ⟨101911, true, false, [], [94341]⟩
      ]⟩,
    ⟨[37265], [37266], .contexts [
        ⟨101910, true, true, [], []⟩
      ]⟩,
    ⟨[37265], [37265], .contexts []⟩,
    ⟨[37265], [37265], .contexts [
        ⟨101915, false, false, [], []⟩
      ]⟩,
    ⟨[94343], [37265, 85467], .contexts [
        ⟨83977, true, false, [], []⟩,
        ⟨83977, true, false, [], []⟩,
        ⟨84183, true, false, [], []⟩,
        ⟨95154, true, false, [], []⟩,
        ⟨101913, true, false, [37266], [11]⟩,
        ⟨53, false, false, [37266, 85467], []⟩,
        ⟨101914, true, false, [], [85467]⟩,
        ⟨101905, false, false, [], []⟩,
        ⟨101916, true, false, [], [85467]⟩
      ]⟩,
    ⟨[37269], [37267, 34811], .source 18699⟩,
    ⟨[85467, 9], [37269, 95399], .contexts [
        ⟨101917, true, false, [37264], [9]⟩,
        ⟨95155, true, false, [37264, 34808], [9]⟩,
        ⟨46, false, false, [37264, 34808, 95399], []⟩,
        ⟨95097, true, false, [37264], [95399]⟩,
        ⟨95153, false, false, [37264], []⟩,
        ⟨101910, true, false, [], [34811, 95399]⟩,
        ⟨101918, true, false, [], [95399]⟩
      ]⟩,
    ⟨[94343], [37265, 85467], .contexts [
        ⟨101917, false, false, [], []⟩,
        ⟨101906, false, false, [], []⟩
      ]⟩,
    ⟨[37265, 85465], [37265, 85465], .contexts []⟩,
    ⟨[37271], [37265, 21227], .source 18700⟩,
    ⟨[37273], [37270], .source 18701⟩,
    ⟨[84193], [37273, 94347], .contexts [
        ⟨101922, false, false, [37270], [84193]⟩,
        ⟨44552, true, false, [37270, 37265], []⟩,
        ⟨101921, true, false, [37270], [13]⟩,
        ⟨101914, false, false, [37270], [85465, 13]⟩,
        ⟨101921, true, false, [37270, 37266, 37264], [13]⟩,
        ⟨32014, true, false, [37270, 37266], [13]⟩,
        ⟨101920, true, false, [37270, 37266, 37264], [1, 13]⟩,
        ⟨83976, false, false, [37270, 37266, 37264], [13]⟩,
        ⟨84182, false, false, [37270, 37266, 37264], [13]⟩,
        ⟨13, true, false, [37270, 37266, 37264], [94345, 13]⟩,
        ⟨101911, true, false, [37270, 37266], [94345, 13]⟩,
        ⟨83979, false, false, [37270], []⟩,
        ⟨84180, false, false, [37270], []⟩,
        ⟨13, true, false, [37270], [94347]⟩,
        ⟨101923, true, false, [], [94347]⟩
      ]⟩,
    ⟨[37275], [37271, 27315], .source 18702⟩,
    ⟨[37277], [37274], .source 18703⟩,
    ⟨[94349, 1], [37275, 30313, 93525], .contexts [
        ⟨101926, false, false, [37276], [94349, 1]⟩,
        ⟨13, false, false, [37276, 37274], [94349, 1]⟩,
        ⟨84179, true, false, [37276, 37274], [1]⟩,
        ⟨83982, true, false, [37276, 37274], [1]⟩,
        ⟨101924, true, false, [37276, 37274, 37272], [15, 1]⟩,
        ⟨101923, false, true, [37276, 37274], [84193, 15, 1]⟩,
        ⟨70107, false, false, [37276, 37274, 37271], [1]⟩,
        ⟨101925, true, false, [37276, 37274], [91603, 1]⟩,
        ⟨101926, false, true, [], [91603, 1]⟩,
        ⟨79756, false, false, [37275], []⟩,
        ⟨79770, false, false, [37275, 30269], []⟩,
        ⟨79827, true, false, [37275], [93525]⟩
      ]⟩,
    ⟨[37279], [37275, 30313], .source 18704⟩,
    ⟨[37281], [37278], .source 18705⟩,
    ⟨[37281], [37278], .contexts [
        ⟨101929, false, false, [], []⟩
      ]⟩,
    ⟨[94351], [37279, 93525], .contexts [
        ⟨101930, false, false, [37280], [94351]⟩,
        ⟨13, false, false, [37280, 37278], [94351]⟩,
        ⟨84178, true, false, [37280, 37278], []⟩,
        ⟨83985, true, false, [37280, 37278], []⟩,
        ⟨101927, false, false, [37280, 37278], []⟩,
        ⟨101928, true, false, [37280, 37278], [93525]⟩,
        ⟨101929, false, true, [], [93525]⟩
      ]⟩,
    ⟨[37278], [37278], .contexts []⟩,
    ⟨[93525, 3], [37281, 94353], .contexts [
        ⟨101931, true, false, [37278], [3]⟩,
        ⟨83988, false, false, [37278], []⟩,
        ⟨84176, false, false, [37278], []⟩,
        ⟨101932, true, false, [], [94353]⟩,
        ⟨101932, true, false, [], [94353]⟩,
        ⟨101930, true, false, [], [94353]⟩
      ]⟩,
    ⟨[37283], [37225, 29315], .source 18706⟩,
    ⟨[37285], [37283, 35001], .source 18707⟩,
    ⟨[84397, 15], [84397, 15], .contexts []⟩,
    ⟨[37287], [37284], .source 18708⟩,
    ⟨[37284], [37284], .contexts []⟩,
    ⟨[84397, 15], [37287, 94341], .contexts [
        ⟨101936, false, false, [], []⟩,
        ⟨101935, false, false, [37284], [84397, 15]⟩,
        ⟨95711, true, false, [37284, 37283], [15]⟩,
        ⟨101934, false, false, [37284], [92935, 1, 15]⟩,
        ⟨76306, true, false, [37284, 37225], [1, 15]⟩,
        ⟨101903, true, false, [37284], [15, 1, 15]⟩,
        ⟨2185, false, false, [37284, 94341], []⟩,
        ⟨101907, false, false, [37284], []⟩,
        ⟨101909, false, false, [37284], []⟩,
        ⟨101938, true, false, [], [94341]⟩,
        ⟨101938, true, false, [], [94341]⟩,
        ⟨101937, true, false, [], [94341]⟩
      ]⟩,
    ⟨[37285], [37286], .contexts [
        ⟨101937, true, true, [], []⟩
      ]⟩,
    ⟨[37229, 92931], [37229, 92931], .contexts []⟩,
    ⟨[37229, 92931], [37229, 92931], .contexts []⟩,
    ⟨[87081, 9], [37229, 92931], .contexts [
        ⟨101767, false, false, [], []⟩,
        ⟨101770, false, false, [], []⟩,
        ⟨101941, false, false, [], []⟩,
        ⟨101942, false, false, [], []⟩,
        ⟨101942, false, false, [], []⟩
      ]⟩,
    ⟨[37289], [37229, 35001], .source 18709⟩,
    ⟨[84397, 9], [84397, 9], .contexts []⟩,
    ⟨[37291], [37288], .source 18710⟩,
    ⟨[37291], [37288], .contexts [
        ⟨101946, false, false, [], []⟩
      ]⟩,
    ⟨[37288], [37288], .contexts []⟩,
    ⟨[84397, 9], [37291, 87083], .contexts [
        ⟨101945, false, false, [], []⟩,
        ⟨101944, false, false, [37288], [84397, 9]⟩,
        ⟨95711, true, false, [37288, 37229], [9]⟩,
        ⟨75932, true, false, [37288, 37229], [1, 9]⟩,
        ⟨75928, true, false, [37288, 37229], [9, 1, 9]⟩,
        ⟨101943, true, false, [37288], [1, 9, 1, 9]⟩,
        ⟨495, false, false, [37288, 87081], []⟩,
        ⟨9, false, false, [37288, 87081], []⟩,
        ⟨40144, false, false, [37288], []⟩,
        ⟨40248, false, false, [37288], []⟩,
        ⟨40149, false, false, [37288], []⟩,
        ⟨40149, false, false, [37288], []⟩,
        ⟨51775, false, false, [37288], []⟩,
        ⟨101948, true, false, [], [87083]⟩,
        ⟨101948, true, false, [], [87083]⟩,
        ⟨101947, true, false, [], [87083]⟩
      ]⟩,
    ⟨[37289], [37290], .contexts [
        ⟨101946, true, true, [], []⟩
      ]⟩,
    ⟨[95343], [36991, 87221], .contexts [
        ⟨101292, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1593. -/
def y322TCIndexRaw1593 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[37293], [36379, 36991], .source 18711⟩,
    ⟨[37295], [37229, 37293], .source 18712⟩,
    ⟨[37295, 87219], [37295, 87219], .contexts []⟩,
    ⟨[87219, 13], [87219, 13], .contexts []⟩,
    ⟨[87081], [87081], .contexts []⟩,
    ⟨[37297], [37294], .source 18713⟩,
    ⟨[37294], [37294], .contexts []⟩,
    ⟨[87219, 13], [37297, 87081], .contexts [
        ⟨101955, false, false, [], []⟩,
        ⟨101954, true, false, [37294], [13]⟩,
        ⟨40777, true, false, [], [13]⟩,
        ⟨101953, false, false, [37294], [87221, 9, 13]⟩,
        ⟨101952, false, false, [37294, 37229], [87221, 9, 13]⟩,
        ⟨101951, true, false, [37294, 37229, 36379], [9, 13]⟩,
        ⟨99978, true, false, [37294, 37229], [9, 13]⟩,
        ⟨101943, true, false, [37294], [13, 9, 13]⟩,
        ⟨475, false, false, [37294, 87081], []⟩,
        ⟨101956, false, false, [37294], []⟩,
        ⟨101958, true, false, [], [87081]⟩,
        ⟨101958, true, false, [], [87081]⟩,
        ⟨101957, true, false, [], [87081]⟩
      ]⟩,
    ⟨[37295], [37296], .contexts [
        ⟨101957, true, true, [], []⟩
      ]⟩,
    ⟨[23091, 88565], [23091, 88565], .contexts []⟩,
    ⟨[37299], [23093, 37295], .source 18714⟩,
    ⟨[88565], [37299, 87219], .contexts [
        ⟨101961, true, false, [23090], []⟩,
        ⟨101961, true, false, [23090], []⟩,
        ⟨51779, true, false, [23090], []⟩,
        ⟨101959, true, false, [23090, 37296], [13]⟩,
        ⟨59, false, false, [23090, 37296, 87219], []⟩,
        ⟨101960, true, false, [23090], [87219]⟩,
        ⟨101954, false, false, [23090], []⟩,
        ⟨51539, true, false, [], [37295, 87219]⟩,
        ⟨101962, true, false, [], [87219]⟩
      ]⟩,
    ⟨[88565], [37299, 87219], .contexts [
        ⟨101963, false, false, [], []⟩
      ]⟩,
    ⟨[37301], [37299, 19937], .source 18715⟩,
    ⟨[37303], [37300], .source 18716⟩,
    ⟨[37303], [37300], .contexts [
        ⟨101966, false, false, [], []⟩
      ]⟩,
    ⟨[88563], [37301, 87219], .contexts [
        ⟨101967, false, false, [37302], [88563]⟩,
        ⟨13, false, false, [37302, 37300], [88563]⟩,
        ⟨51097, true, false, [37302, 37300], []⟩,
        ⟨50984, true, false, [37302, 37300], []⟩,
        ⟨101964, false, false, [37302, 37300], [1]⟩,
        ⟨40749, false, false, [37302, 37300, 37299], []⟩,
        ⟨101965, true, false, [37302, 37300], [87219]⟩,
        ⟨101966, false, true, [], [87219]⟩
      ]⟩,
    ⟨[37300], [37300], .contexts []⟩,
    ⟨[87219, 11], [37303, 88561], .contexts [
        ⟨101968, true, false, [37300], [11]⟩,
        ⟨50981, false, false, [37300], []⟩,
        ⟨51099, false, false, [37300], []⟩,
        ⟨101969, true, false, [], [88561]⟩,
        ⟨101969, true, false, [], [88561]⟩,
        ⟨101967, true, false, [], [88561]⟩
      ]⟩,
    ⟨[37171, 88001], [37171, 88001], .contexts []⟩,
    ⟨[37171, 88001], [37171, 88001], .contexts []⟩,
    ⟨[88001, 5], [88001, 5], .contexts []⟩,
    ⟨[37305], [37173, 37163], .source 18717⟩,
    ⟨[88001, 5], [37305, 88571], .contexts [
        ⟨101973, false, false, [], []⟩,
        ⟨101972, true, false, [37170], [5]⟩,
        ⟨101972, true, false, [37170], [5]⟩,
        ⟨101971, true, false, [37170], [5]⟩,
        ⟨101786, true, false, [37170], [5]⟩,
        ⟨101784, true, false, [37170], [5]⟩,
        ⟨98, false, false, [37170, 94335], []⟩,
        ⟨99, false, false, [37170, 94335], []⟩,
        ⟨95140, false, false, [37170], [1]⟩,
        ⟨101650, false, false, [37170], [1]⟩,
        ⟨101639, false, false, [37170], [1]⟩,
        ⟨101639, false, false, [37170], [1]⟩,
        ⟨101651, false, false, [37170], []⟩,
        ⟨101652, false, false, [37170], []⟩,
        ⟨101653, false, false, [37170], []⟩,
        ⟨101655, false, false, [37170], []⟩,
        ⟨51738, false, false, [37170, 37163], []⟩,
        ⟨101666, true, false, [], [37163, 88571]⟩,
        ⟨101974, true, false, [], [88571]⟩
      ]⟩,
    ⟨[37307], [37304], .source 18718⟩,
    ⟨[88571, 5], [37307, 88001], .contexts [
        ⟨101975, true, false, [37304], [5]⟩,
        ⟨28, false, false, [37304, 88001], []⟩,
        ⟨101976, true, false, [], [88001]⟩
      ]⟩,
    ⟨[37045, 91971], [37045, 91971], .contexts []⟩,
    ⟨[91971, 11, 3], [37045, 91973], .contexts [
        ⟨101807, false, false, [], [3]⟩,
        ⟨101807, false, false, [], [3]⟩,
        ⟨68866, true, false, [], [11, 3]⟩,
        ⟨101806, true, false, [37184], [1, 11, 3]⟩,
        ⟨567, false, false, [37184, 91969], [3]⟩,
        ⟨9, false, false, [37184, 91969], [3]⟩,
        ⟨68866, false, false, [37184], [3]⟩,
        ⟨69044, false, false, [37184], [3]⟩,
        ⟨68870, false, false, [37184], [3]⟩,
        ⟨68870, false, false, [37184], [3]⟩,
        ⟨101809, true, false, [], [91971, 3]⟩,
        ⟨101978, false, false, [], [3]⟩,
        ⟨101978, false, false, [], [3]⟩,
        ⟨68869, false, false, [37045], []⟩
      ]⟩,
    ⟨[91973, 11], [91973, 11], .contexts []⟩,
    ⟨[91973, 11], [37185, 91973], .contexts [
        ⟨101980, false, false, [], []⟩,
        ⟨101979, true, false, [37044], [11]⟩,
        ⟨603, false, false, [37044, 91971], []⟩,
        ⟨21, false, false, [37044, 91971], []⟩,
        ⟨68869, false, false, [37044], []⟩,
        ⟨69043, false, false, [37044], []⟩,
        ⟨68874, false, false, [37044], []⟩,
        ⟨68874, false, false, [37044], []⟩,
        ⟨101686, true, false, [], [91973]⟩
      ]⟩,
    ⟨[37191, 87231], [37191, 87231], .contexts []⟩,
    ⟨[37191, 87231], [37191, 87231], .contexts []⟩,
    ⟨[91595, 11], [37191, 87231], .contexts [
        ⟨101817, false, false, [], []⟩,
        ⟨101820, false, false, [], []⟩,
        ⟨101982, false, false, [], []⟩,
        ⟨101983, false, false, [], []⟩,
        ⟨101983, false, false, [], []⟩
      ]⟩,
    ⟨[91595, 3], [30831, 88317], .contexts [
        ⟨81997, false, false, [], []⟩,
        ⟨81993, false, false, [], []⟩,
        ⟨81994, false, false, [], []⟩,
        ⟨81994, false, false, [], []⟩
      ]⟩,
    ⟨[37189], [37190], .contexts [
        ⟨101821, false, false, [], []⟩
      ]⟩,
    ⟨[37309], [37189, 30831], .source 18719⟩,
    ⟨[87233, 11], [37309, 88317], .contexts [
        ⟨40798, true, false, [], [11]⟩,
        ⟨101984, true, false, [37190], [3, 11]⟩,
        ⟨603, false, false, [37190, 91595], []⟩,
        ⟨21, false, false, [37190, 91595], []⟩,
        ⟨101985, false, false, [37190], []⟩,
        ⟨81973, false, false, [37190, 30831], []⟩,
        ⟨101986, true, false, [], [30831, 88317]⟩,
        ⟨101987, true, false, [], [88317]⟩
      ]⟩,
    ⟨[37311], [37308], .source 18720⟩,
    ⟨[37313], [36895, 37311], .source 18721⟩,
    ⟨[92917], [37313, 87233], .contexts [
        ⟨101206, true, false, [36896], []⟩,
        ⟨101988, true, false, [36896, 37308], [11]⟩,
        ⟨53, false, false, [36896, 37308, 87233], []⟩,
        ⟨101989, true, false, [36896], [87233]⟩,
        ⟨101094, true, false, [], [37311, 87233]⟩,
        ⟨101990, true, false, [], [87233]⟩
      ]⟩,
    ⟨[37315], [37312], .source 18722⟩,
    ⟨[37317], [37315, 37057], .source 18723⟩,
    ⟨[87233, 9], [37317, 92913], .contexts [
        ⟨101991, true, false, [37312], [9]⟩,
        ⟨75901, false, false, [37312], []⟩,
        ⟨101559, false, false, [37312], []⟩,
        ⟨101992, true, false, [], [37057, 92913]⟩,
        ⟨101993, true, false, [], [92913]⟩
      ]⟩,
    ⟨[37319], [37315, 36955], .source 18724⟩,
    ⟨[87233, 13], [37319, 96765], .contexts [
        ⟨101991, true, false, [37312], [13]⟩,
        ⟨101211, true, false, [37312, 36952], [13]⟩,
        ⟨59, false, false, [37312, 36952, 96765], []⟩,
        ⟨101212, true, false, [37312], [96765]⟩,
        ⟨101992, true, false, [], [36955, 96765]⟩,
        ⟨101995, true, false, [], [96765]⟩
      ]⟩,
    ⟨[37247, 89821], [37247, 89821], .contexts []⟩,
    ⟨[89821, 3], [37247, 89821], .contexts [
        ⟨101848, false, false, [], []⟩,
        ⟨101997, false, false, [], []⟩,
        ⟨101997, false, false, [], []⟩
      ]⟩,
    ⟨[37321], [37247, 25351], .source 18725⟩,
    ⟨[87393, 3], [87393, 3], .contexts []⟩,
    ⟨[37323], [37320], .source 18726⟩,
    ⟨[37325], [37323, 25351], .source 18727⟩,
    ⟨[37327], [37246], .source 18728⟩,
    ⟨[37246], [37246], .contexts []⟩,
    ⟨[89821, 11], [89823], .contexts [
        ⟨57666, false, false, [], []⟩,
        ⟨57708, false, false, [], []⟩,
        ⟨57671, false, false, [], []⟩,
        ⟨57671, false, false, [], []⟩
      ]⟩,
    ⟨[89823, 3], [89823, 3], .contexts []⟩,
    ⟨[89823, 3], [37327, 89823], .contexts [
        ⟨102006, false, false, [], []⟩,
        ⟨57666, true, false, [], [3]⟩,
        ⟨101998, true, false, [37246], [11, 3]⟩,
        ⟨545, false, false, [37246, 89821], []⟩,
        ⟨54, false, false, [37246, 89821], []⟩,
        ⟨102005, false, false, [37246], []⟩,
        ⟨61962, false, false, [37246], []⟩,
        ⟨102004, true, false, [], [89823]⟩,
        ⟨102004, true, false, [], [89823]⟩,
        ⟨102003, true, false, [], [89823]⟩
      ]⟩,
    ⟨[37193, 93655], [37193, 93655], .contexts []⟩,
    ⟨[37193, 93655], [37193, 93655], .contexts []⟩,
    ⟨[37329], [37059, 37193], .source 18729⟩,
    ⟨[93655, 3], [93655, 3], .contexts []⟩,
    ⟨[37331], [37195, 37329], .source 18730⟩,
    ⟨[93655, 3], [37331, 93655], .contexts [
        ⟨102011, false, false, [], []⟩,
        ⟨102009, true, false, [37192], [3]⟩,
        ⟨102009, true, false, [37192], [3]⟩,
        ⟨102008, true, false, [37192], [3]⟩,
        ⟨101834, true, false, [37192], [3]⟩,
        ⟨101830, true, false, [37192], [3]⟩,
        ⟨215, false, false, [37192, 92907], []⟩,
        ⟨216, false, false, [37192, 92907], []⟩,
        ⟨101823, false, false, [37192], [11]⟩,
        ⟨101834, false, false, [37192, 37059], []⟩,
        ⟨102010, true, false, [37192], [93655]⟩,
        ⟨101831, false, false, [37192, 37329], []⟩,
        ⟨101709, true, false, [], [37329, 93655]⟩,
        ⟨102012, true, false, [], [93655]⟩
      ]⟩,
    ⟨[92905], [37241, 89821], .contexts [
        ⟨101844, false, false, [], []⟩
      ]⟩,
    ⟨[37333], [37241, 37251], .source 18731⟩]

/-- Exact literal claimed equations and contextual derivations, block 1594. -/
def y322TCIndexRaw1594 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[92901, 15], [92901, 15], .contexts []⟩,
    ⟨[37335], [37332], .source 18732⟩,
    ⟨[37332], [37332], .contexts []⟩,
    ⟨[92901, 15], [37335, 92909], .contexts [
        ⟨102016, false, false, [], []⟩,
        ⟨102015, false, false, [37332], [92901, 15]⟩,
        ⟨101856, true, false, [37332, 37241], [15]⟩,
        ⟨101843, true, false, [37332], [1, 15]⟩,
        ⟨101843, true, false, [37332], [1, 15]⟩,
        ⟨102014, true, false, [37332], [1, 15]⟩,
        ⟨101824, true, false, [37332], [1, 15]⟩,
        ⟨1666, false, false, [37332, 92907], []⟩,
        ⟨9, false, false, [37332, 92907], []⟩,
        ⟨75883, false, false, [37332], []⟩,
        ⟨76013, false, false, [37332], []⟩,
        ⟨75888, false, false, [37332], []⟩,
        ⟨75888, false, false, [37332], []⟩,
        ⟨101706, false, false, [37332], []⟩,
        ⟨102018, true, false, [], [92909]⟩,
        ⟨102018, true, false, [], [92909]⟩,
        ⟨102017, true, false, [], [92909]⟩
      ]⟩,
    ⟨[37193, 93651], [37193, 93651], .contexts []⟩,
    ⟨[37193, 93651], [37193, 93651], .contexts []⟩,
    ⟨[93651, 3], [93651, 3], .contexts []⟩,
    ⟨[93651], [93651], .contexts []⟩,
    ⟨[37337], [37328], .source 18733⟩,
    ⟨[37339], [37337, 37193], .source 18734⟩,
    ⟨[93651, 3], [37339, 93651], .contexts [
        ⟨102022, false, false, [], []⟩,
        ⟨102010, false, false, [37328], [93651, 3]⟩,
        ⟨101836, true, false, [37328, 37059], [3]⟩,
        ⟨101823, true, false, [37328], [9, 3]⟩,
        ⟨573, false, false, [37328, 92907], []⟩,
        ⟨47, false, false, [37328, 92907], []⟩,
        ⟨101836, false, false, [37328], []⟩,
        ⟨102020, false, false, [37328], []⟩,
        ⟨102021, false, false, [37328], []⟩,
        ⟨102021, false, false, [37328], []⟩,
        ⟨102023, false, false, [37328, 37193], []⟩,
        ⟨102024, true, false, [], [37193, 93651]⟩,
        ⟨102025, true, false, [], [93651]⟩
      ]⟩,
    ⟨[37341], [37059, 37239], .source 18735⟩,
    ⟨[37239, 88947], [37239, 88947], .contexts []⟩,
    ⟨[37239, 88947], [37239, 88947], .contexts []⟩,
    ⟨[37343], [37340], .source 18736⟩,
    ⟨[37345], [37343, 37239], .source 18737⟩,
    ⟨[37251, 92901], [37251, 92901], .contexts []⟩,
    ⟨[37251, 92901], [37251, 92901], .contexts []⟩,
    ⟨[89825, 11], [89825, 11], .contexts []⟩,
    ⟨[89825, 11], [37251, 92901], .contexts [
        ⟨102034, false, false, [], []⟩,
        ⟨57675, true, false, [], [11]⟩,
        ⟨57675, true, false, [], [11]⟩,
        ⟨57706, true, false, [], [11]⟩,
        ⟨57670, true, false, [], [11]⟩,
        ⟨102005, true, false, [], [1, 11]⟩,
        ⟨567, false, false, [89821], []⟩,
        ⟨9, false, false, [89821], []⟩,
        ⟨101856, false, false, [], []⟩,
        ⟨102032, false, false, [], []⟩,
        ⟨102033, false, false, [], []⟩,
        ⟨102033, false, false, [], []⟩,
        ⟨13, true, false, [], [37251, 92901]⟩
      ]⟩,
    ⟨[37249], [37249], .contexts []⟩,
    ⟨[92899], [37249, 89825], .contexts [
        ⟨75870, true, false, [], []⟩,
        ⟨75870, true, false, [], []⟩,
        ⟨76022, true, false, [], []⟩,
        ⟨76021, true, false, [], []⟩,
        ⟨102035, true, false, [37250], [11]⟩,
        ⟨53, false, false, [37250, 89825], []⟩,
        ⟨101852, true, false, [], [89825]⟩,
        ⟨102036, true, false, [], [89825]⟩
      ]⟩,
    ⟨[89825, 9], [37251, 92897], .contexts [
        ⟨102037, true, false, [37248], [9]⟩,
        ⟨75868, false, false, [37248], []⟩,
        ⟨76023, false, false, [37248], []⟩,
        ⟨101855, true, false, [], [92897]⟩
      ]⟩,
    ⟨[37129, 89053], [37129, 89053], .contexts []⟩,
    ⟨[37129, 89053], [37129, 89053], .contexts []⟩,
    ⟨[89051, 11], [89051, 11], .contexts []⟩,
    ⟨[89049], [89049], .contexts []⟩,
    ⟨[37255, 96661], [37255, 96661], .contexts []⟩,
    ⟨[96663, 7], [96663, 7], .contexts []⟩,
    ⟨[37254], [37254], .contexts []⟩,
    ⟨[96663, 7], [37253, 90505], .contexts [
        ⟨102044, false, false, [], []⟩,
        ⟨99158, true, false, [], [7]⟩,
        ⟨102043, true, false, [37254], [1, 7]⟩,
        ⟨102043, true, false, [37254], [1, 7]⟩,
        ⟨101881, true, false, [37254], [1, 7]⟩,
        ⟨101878, true, false, [37254], [1, 7]⟩,
        ⟨502, false, false, [37254, 90503], []⟩,
        ⟨75404, false, false, [37254], []⟩,
        ⟨75403, false, false, [37254], []⟩,
        ⟨75406, false, false, [37254], []⟩,
        ⟨102045, true, false, [], [90505]⟩,
        ⟨102045, true, false, [], [90505]⟩,
        ⟨101879, false, true, [], [90505]⟩
      ]⟩,
    ⟨[37263, 86131], [37263, 86131], .contexts []⟩,
    ⟨[88225, 13], [37263, 86131], .contexts [
        ⟨101893, false, false, [], []⟩,
        ⟨101896, false, false, [], []⟩,
        ⟨102047, false, false, [], []⟩,
        ⟨102047, false, false, [], []⟩
      ]⟩,
    ⟨[37347], [22541, 37263], .source 18738⟩,
    ⟨[86133, 13], [86133, 13], .contexts []⟩,
    ⟨[37349], [37261, 37347], .source 18739⟩,
    ⟨[86133, 13], [37349, 86133], .contexts [
        ⟨102050, false, false, [], []⟩,
        ⟨35527, true, false, [], [13]⟩,
        ⟨102048, true, false, [37262], [1, 13]⟩,
        ⟨1968, false, false, [37262, 88225], []⟩,
        ⟨248, false, false, [37262, 88225], []⟩,
        ⟨49380, false, false, [37262], [13, 1]⟩,
        ⟨101896, false, false, [37262, 22541], [1]⟩,
        ⟨102049, true, false, [37262], [86131, 1]⟩,
        ⟨35527, false, false, [37262, 37347], []⟩,
        ⟨43671, false, false, [37262, 37347], []⟩,
        ⟨101897, true, false, [], [37347, 86133]⟩,
        ⟨102051, true, false, [], [86133]⟩
      ]⟩,
    ⟨[37351], [37263, 33589], .source 18740⟩,
    ⟨[37353], [37350], .source 18741⟩,
    ⟨[37355], [37353, 33143], .source 18742⟩,
    ⟨[88999, 13], [37355, 88229], .contexts [
        ⟨102053, false, false, [37350], [88999, 13]⟩,
        ⟨91479, true, false, [37350, 37263], [13]⟩,
        ⟨102048, true, false, [37350], [9, 13]⟩,
        ⟨942, false, false, [37350, 88225], []⟩,
        ⟨90426, false, false, [37350], []⟩,
        ⟨90425, false, false, [37350], []⟩,
        ⟨90428, false, false, [37350, 33143], []⟩,
        ⟨102054, true, false, [], [33143, 88229]⟩,
        ⟨102055, true, false, [], [88229]⟩
      ]⟩,
    ⟨[37357], [37354], .source 18743⟩,
    ⟨[37153, 86643], [37153, 86643], .contexts []⟩,
    ⟨[86643, 9, 1], [37153, 86641], .contexts [
        ⟨101900, false, false, [], [1]⟩,
        ⟨101900, false, false, [], [1]⟩,
        ⟨38290, true, false, [], [9, 1]⟩,
        ⟨101899, true, false, [37216], [13, 9, 1]⟩,
        ⟨511, false, false, [37216, 86645], [1]⟩,
        ⟨64, false, false, [37216, 86645], [1]⟩,
        ⟨38420, false, false, [37216], [1]⟩,
        ⟨38421, false, false, [37216], [1]⟩,
        ⟨38289, false, false, [37216], [1]⟩,
        ⟨38289, false, false, [37216], [1]⟩,
        ⟨68676, false, false, [37216], [1]⟩,
        ⟨101901, true, false, [], [86643, 1]⟩,
        ⟨101901, true, false, [], [86643, 1]⟩,
        ⟨101756, false, true, [], [86643, 1]⟩,
        ⟨102058, false, false, [], [1]⟩,
        ⟨102058, false, false, [], [1]⟩,
        ⟨38286, false, false, [37153], []⟩
      ]⟩,
    ⟨[37359], [37153, 26899], .source 18744⟩,
    ⟨[37359, 90825], [37359, 90825], .contexts []⟩,
    ⟨[86641], [86641], .contexts []⟩,
    ⟨[37361], [37358], .source 18745⟩,
    ⟨[37358], [37358], .contexts []⟩,
    ⟨[86641, 9], [26899, 90827], .contexts [
        ⟨68681, false, false, [], []⟩
      ]⟩,
    ⟨[26899, 90827], [26899, 90827], .contexts []⟩,
    ⟨[26899, 90827], [37359, 90825], .contexts [
        ⟨102066, true, false, [], []⟩,
        ⟨102066, true, false, [], []⟩,
        ⟨102065, true, false, [], []⟩,
        ⟨102063, false, false, [37360], [86641, 9]⟩,
        ⟨102064, false, false, [37360], [86641, 9]⟩,
        ⟨102064, false, false, [37360], [86641, 9]⟩,
        ⟨102062, true, false, [37360, 37358], [9]⟩,
        ⟨68678, true, false, [37360, 37358], [9]⟩,
        ⟨9, true, false, [37360, 37358, 86643], [9]⟩,
        ⟨495, true, false, [37360, 37358, 86643], [9]⟩,
        ⟨102059, false, false, [37360, 37358], [9, 1, 9, 9]⟩,
        ⟨68681, false, false, [37360, 37358, 37153], [1, 9, 9]⟩,
        ⟨102060, true, false, [37360, 37358], [90827, 1, 9, 9]⟩,
        ⟨63020, false, false, [37360], [9, 9]⟩,
        ⟨102061, false, false, [37360, 37358], [9, 9]⟩,
        ⟨46, false, false, [37360, 90825], []⟩,
        ⟨102063, false, true, [], [90825]⟩
      ]⟩,
    ⟨[37363], [26915, 37359], .source 18746⟩,
    ⟨[37267, 94341], [37267, 94341], .contexts []⟩,
    ⟨[85467, 5], [96291], .contexts [
        ⟨97079, false, false, [], []⟩
      ]⟩,
    ⟨[85467, 5], [96291], .contexts [
        ⟨102070, false, false, [], []⟩
      ]⟩,
    ⟨[35621, 96471], [35621, 96471], .contexts []⟩,
    ⟨[37365], [37265, 35621], .source 18747⟩,
    ⟨[94341, 5], [37365, 96471], .contexts [
        ⟨102069, true, false, [37266], [5]⟩,
        ⟨102069, true, false, [37266], [5]⟩,
        ⟨101913, true, false, [37266], [5]⟩,
        ⟨101908, true, false, [37266], [5]⟩,
        ⟨642, false, false, [37266, 85467], []⟩,
        ⟨643, false, false, [37266, 85467], []⟩,
        ⟨102071, false, false, [37266], [11]⟩,
        ⟨97256, false, false, [37266], [11]⟩,
        ⟨97083, false, false, [37266], [11]⟩,
        ⟨97083, false, false, [37266], [11]⟩,
        ⟨97863, false, false, [37266], []⟩,
        ⟨102072, false, false, [37266], []⟩,
        ⟨102072, false, false, [37266], []⟩,
        ⟨101914, true, false, [], [35621, 96471]⟩,
        ⟨101915, true, false, [], [35621, 96471]⟩,
        ⟨102073, true, false, [], [96471]⟩
      ]⟩,
    ⟨[37367], [37364], .source 18748⟩,
    ⟨[85467, 9], [37269, 95399], .contexts [
        ⟨101919, false, false, [], []⟩
      ]⟩,
    ⟨[37269, 95399], [37269, 95399], .contexts []⟩,
    ⟨[85467, 9], [37269, 95399], .contexts [
        ⟨102076, false, false, [], []⟩,
        ⟨102077, false, false, [], []⟩,
        ⟨102077, false, false, [], []⟩
      ]⟩,
    ⟨[86661, 9], [86661, 9], .contexts []⟩]

/-- Exact literal claimed equations and contextual derivations, block 1595. -/
def y322TCIndexRaw1595 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[95401], [95401], .contexts []⟩,
    ⟨[37369], [35353, 37269], .source 18749⟩,
    ⟨[86661, 9], [37369, 95401], .contexts [
        ⟨102079, false, false, [], []⟩,
        ⟨38320, true, false, [], [9]⟩,
        ⟨70214, true, false, [27342], [1, 9]⟩,
        ⟨70214, true, false, [27342], [1, 9]⟩,
        ⟨70213, true, false, [27342], [1, 9]⟩,
        ⟨70212, true, false, [27342], [1, 9]⟩,
        ⟨32013, true, false, [27342], [9, 1, 9]⟩,
        ⟨32013, true, false, [27342], [9, 1, 9]⟩,
        ⟨32066, true, false, [27342], [9, 1, 9]⟩,
        ⟨32065, true, false, [27342], [9, 1, 9]⟩,
        ⟨582, false, false, [27342, 85467], []⟩,
        ⟨453, false, false, [27342, 85467], []⟩,
        ⟨102078, false, false, [27342], [1]⟩,
        ⟨90598, false, false, [27342, 37269], []⟩,
        ⟨102080, false, false, [27342, 37269], []⟩,
        ⟨97098, true, false, [], [37269, 95401]⟩,
        ⟨102081, true, false, [], [95401]⟩
      ]⟩,
    ⟨[37371], [37368], .source 18750⟩,
    ⟨[85467, 3], [85469], .contexts [
        ⟨97257, false, false, [], []⟩,
        ⟨32062, false, false, [], []⟩,
        ⟨32021, false, false, [], []⟩,
        ⟨32021, false, false, [], []⟩
      ]⟩,
    ⟨[20867, 83617], [20867, 83617], .contexts []⟩,
    ⟨[20867, 83617], [20867, 83617], .contexts []⟩,
    ⟨[85467, 8], [85467, 9], .contexts [
        ⟨47, false, false, [85467], []⟩
      ]⟩,
    ⟨[83617, 3], [83617, 3], .contexts []⟩,
    ⟨[95399], [95399], .contexts []⟩,
    ⟨[37373], [20865, 37269], .source 18751⟩,
    ⟨[83617, 3], [37373, 95399], .contexts [
        ⟨102088, false, false, [], []⟩,
        ⟨102086, true, false, [20866], [3]⟩,
        ⟨102086, true, false, [20866], [3]⟩,
        ⟨102085, true, false, [20866], [3]⟩,
        ⟨42918, true, false, [20866], [3]⟩,
        ⟨102084, true, false, [20866], [9, 3]⟩,
        ⟨573, false, false, [20866, 85467], []⟩,
        ⟨102087, false, false, [20866], []⟩,
        ⟨102078, false, false, [20866], []⟩,
        ⟨102089, false, false, [20866, 37269], []⟩,
        ⟨42919, true, false, [], [37269, 95399]⟩,
        ⟨102090, true, false, [], [95399]⟩
      ]⟩,
    ⟨[37375], [37372], .source 18752⟩,
    ⟨[37377], [27337, 30717], .source 18753⟩,
    ⟨[89421, 7], [89421, 7], .contexts []⟩,
    ⟨[37379], [37376], .source 18754⟩,
    ⟨[37381], [37379, 37269], .source 18755⟩,
    ⟨[89421, 7], [37381, 95399], .contexts [
        ⟨102094, false, false, [], []⟩,
        ⟨102093, false, false, [37376], [89421, 7]⟩,
        ⟨81274, true, false, [37376, 27337], [7]⟩,
        ⟨76235, true, false, [37376], [9, 7]⟩,
        ⟨579, false, false, [37376, 85467], []⟩,
        ⟨102087, false, false, [37376], []⟩,
        ⟨102078, false, false, [37376], []⟩,
        ⟨102089, false, false, [37376, 37269], []⟩,
        ⟨102095, true, false, [], [37269, 95399]⟩,
        ⟨102096, true, false, [], [95399]⟩
      ]⟩,
    ⟨[37383], [37380], .source 18756⟩,
    ⟨[37385], [30275, 37281], .source 18757⟩,
    ⟨[37281, 94353], [37281, 94353], .contexts []⟩,
    ⟨[37281, 94353], [37281, 94353], .contexts []⟩,
    ⟨[93525, 3], [37281, 94353], .contexts [
        ⟨101933, false, false, [], []⟩,
        ⟨102100, false, false, [], []⟩,
        ⟨102101, false, false, [], []⟩,
        ⟨102101, false, false, [], []⟩
      ]⟩,
    ⟨[93525, 2], [93525, 3], .contexts [
        ⟨21, false, false, [93525], []⟩
      ]⟩,
    ⟨[94353], [94353], .contexts []⟩,
    ⟨[37387], [37384], .source 18758⟩,
    ⟨[37389], [37387, 37281], .source 18759⟩,
    ⟨[30273, 84195], [30273, 84195], .contexts []⟩,
    ⟨[30273, 84195], [30273, 84195], .contexts []⟩,
    ⟨[37391], [30273, 27319], .source 18760⟩,
    ⟨[87655, 15], [87655, 15], .contexts []⟩,
    ⟨[37393], [37390], .source 18761⟩,
    ⟨[37395], [37393, 37281], .source 18762⟩,
    ⟨[87655, 15], [37395, 94353], .contexts [
        ⟨102110, false, false, [], []⟩,
        ⟨102109, false, false, [37390], [87655, 15]⟩,
        ⟨70096, true, false, [37390, 30273], [15]⟩,
        ⟨102108, true, false, [37390], [3, 15]⟩,
        ⟨102108, true, false, [37390], [3, 15]⟩,
        ⟨102107, true, false, [37390], [3, 15]⟩,
        ⟨79765, true, false, [37390], [3, 15]⟩,
        ⟨79761, true, false, [37390], [3, 15]⟩,
        ⟨1141, false, false, [37390, 93525], []⟩,
        ⟨102103, false, false, [37390], []⟩,
        ⟨102102, false, false, [37390], []⟩,
        ⟨102104, false, false, [37390, 37281], []⟩,
        ⟨102111, true, false, [], [37281, 94353]⟩,
        ⟨102112, true, false, [], [94353]⟩
      ]⟩,
    ⟨[37397], [37394], .source 18763⟩,
    ⟨[94353, 15], [37397, 87655], .contexts [
        ⟨102113, true, false, [37394], [15]⟩,
        ⟨1, false, false, [37394, 87655], []⟩,
        ⟨102114, true, false, [], [87655]⟩
      ]⟩,
    ⟨[30289, 93525], [30289, 93525], .contexts []⟩,
    ⟨[37399], [30289, 37281], .source 18764⟩,
    ⟨[93525, 9, 3], [37399, 94353], .contexts [
        ⟨79784, false, false, [], [3]⟩,
        ⟨79784, false, false, [], [3]⟩,
        ⟨79781, false, false, [30284], [93525, 9, 3]⟩,
        ⟨79780, false, false, [30284, 27323], [93525, 9, 3]⟩,
        ⟨79770, true, false, [30284, 27323, 30259], [9, 3]⟩,
        ⟨79733, true, false, [30284, 27323], [9, 3]⟩,
        ⟨79779, true, false, [30284], [15, 9, 3]⟩,
        ⟨935, false, false, [30284, 84195], [3]⟩,
        ⟨79783, false, false, [30284], [3]⟩,
        ⟨79782, false, false, [30284], [3]⟩,
        ⟨79785, false, false, [30284, 30283], [3]⟩,
        ⟨79786, true, false, [], [30283, 93525, 3]⟩,
        ⟨79787, true, false, [], [93525, 3]⟩,
        ⟨102116, false, false, [], [3]⟩,
        ⟨102116, false, false, [], [3]⟩,
        ⟨101933, false, false, [30289], []⟩,
        ⟨102117, true, false, [], [94353]⟩
      ]⟩,
    ⟨[94353, 9], [94353, 9], .contexts []⟩,
    ⟨[37401], [37398], .source 18765⟩,
    ⟨[37403], [37401, 37281], .source 18766⟩,
    ⟨[94353, 9], [37403, 94353], .contexts [
        ⟨102119, false, false, [], []⟩,
        ⟨102118, true, false, [37398], [9]⟩,
        ⟨479, false, false, [37398, 93525], []⟩,
        ⟨102103, false, false, [37398], []⟩,
        ⟨102102, false, false, [37398], []⟩,
        ⟨102104, false, false, [37398, 37281], []⟩,
        ⟨102120, true, false, [], [37281, 94353]⟩,
        ⟨102121, true, false, [], [94353]⟩
      ]⟩,
    ⟨[36599, 84629], [36599, 84629], .contexts []⟩,
    ⟨[84627, 11], [84627, 11], .contexts []⟩,
    ⟨[37405], [36601, 37281], .source 18767⟩,
    ⟨[84627, 11], [37405, 94353], .contexts [
        ⟨102124, false, false, [], []⟩,
        ⟨27983, true, false, [], [11]⟩,
        ⟨102123, true, false, [36598], [3, 11]⟩,
        ⟨102123, true, false, [36598], [3, 11]⟩,
        ⟨100480, true, false, [36598], [3, 11]⟩,
        ⟨100478, true, false, [36598], [3, 11]⟩,
        ⟨603, false, false, [36598, 93525], []⟩,
        ⟨102103, false, false, [36598], []⟩,
        ⟨102102, false, false, [36598], []⟩,
        ⟨102104, false, false, [36598, 37281], []⟩,
        ⟨100481, true, false, [], [37281, 94353]⟩,
        ⟨102125, true, false, [], [94353]⟩
      ]⟩,
    ⟨[37407], [37404], .source 18768⟩,
    ⟨[37287, 94341], [37287, 94341], .contexts []⟩,
    ⟨[84397, 15], [37287, 94341], .contexts [
        ⟨101936, false, false, [], []⟩,
        ⟨101939, false, false, [], []⟩,
        ⟨102128, false, false, [], []⟩,
        ⟨102128, false, false, [], []⟩
      ]⟩,
    ⟨[37409], [37287, 37365], .source 18769⟩,
    ⟨[37409, 96473], [37409, 96473], .contexts []⟩,
    ⟨[37411], [37408], .source 18770⟩,
    ⟨[37411], [37411], .contexts []⟩,
    ⟨[37408], [37408], .contexts []⟩,
    ⟨[37409], [37410], .contexts [
        ⟨102132, true, true, [], []⟩
      ]⟩,
    ⟨[84399], [37409, 96473], .contexts [
        ⟨90879, true, false, [], []⟩,
        ⟨102133, false, false, [37410], [84397, 5]⟩,
        ⟨102132, false, false, [37410], [84397, 5]⟩,
        ⟨102134, false, false, [37410], [84397, 5]⟩,
        ⟨102134, false, false, [37410], [84397, 5]⟩,
        ⟨90866, true, false, [37410, 37408], [5]⟩,
        ⟨2284, true, false, [37410, 37408, 84397], [5]⟩,
        ⟨102129, false, false, [37410, 37408], [5, 15, 5, 5]⟩,
        ⟨102074, false, false, [37410, 37408, 37287], [15, 5, 5]⟩,
        ⟨102130, true, false, [37410, 37408], [96471, 15, 5, 5]⟩,
        ⟨97865, false, false, [37410], [5, 5]⟩,
        ⟨102131, false, false, [37410, 37408], [5, 5]⟩,
        ⟨28, false, false, [37410, 96473], []⟩,
        ⟨102135, true, false, [], [96473]⟩
      ]⟩,
    ⟨[96473], [37411, 84399], .contexts [
        ⟨102131, true, false, [37408], []⟩,
        ⟨102136, true, false, [37408], []⟩,
        ⟨102132, true, false, [], [84399]⟩
      ]⟩,
    ⟨[37409], [37410], .contexts [
        ⟨102135, false, false, [], []⟩
      ]⟩,
    ⟨[37410], [37410], .contexts []⟩,
    ⟨[84399, 15], [37409, 96471], .contexts [
        ⟨102137, true, false, [37410], [15]⟩,
        ⟨97866, false, false, [37410], []⟩,
        ⟨97858, false, false, [37410], []⟩,
        ⟨102139, true, false, [], [96471]⟩,
        ⟨102139, true, false, [], [96471]⟩,
        ⟨102138, true, false, [], [96471]⟩
      ]⟩,
    ⟨[96473], [37411, 84399], .contexts [
        ⟨102137, false, false, [], []⟩
      ]⟩,
    ⟨[37411, 84401], [37411, 84401], .contexts []⟩,
    ⟨[37413], [37411, 35013], .source 18771⟩]

/-- Exact literal claimed equations and contextual derivations, block 1596. -/
def y322TCIndexRaw1596 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[37415], [37412], .source 18772⟩,
    ⟨[86245], [37415, 96477], .contexts [
        ⟨102143, false, false, [37412], [86245]⟩,
        ⟨95742, true, false, [37412, 37411], []⟩,
        ⟨102142, true, false, [37412], [3]⟩,
        ⟨102132, false, false, [37412], [84401, 3]⟩,
        ⟨102142, true, false, [37412, 37408, 37410], [3]⟩,
        ⟨26751, true, false, [37412, 37408], [3]⟩,
        ⟨102141, true, false, [37412, 37408, 37410], [1, 3]⟩,
        ⟨97869, false, false, [37412, 37408, 37410], [3]⟩,
        ⟨98032, false, false, [37412, 37408, 37410], [3]⟩,
        ⟨13, true, false, [37412, 37408, 37410], [96475, 3]⟩,
        ⟨102138, true, false, [37412, 37408], [96475, 3]⟩,
        ⟨97871, false, false, [37412], []⟩,
        ⟨98031, false, false, [37412], []⟩,
        ⟨13, true, false, [37412], [96477]⟩,
        ⟨102144, true, false, [], [96477]⟩
      ]⟩,
    ⟨[37417], [37413, 18973], .source 18773⟩,
    ⟨[37419], [37416], .source 18774⟩,
    ⟨[96479, 1], [37417, 18975, 86241], .contexts [
        ⟨102147, false, false, [37418], [96479, 1]⟩,
        ⟨13, false, false, [37418, 37416], [96479, 1]⟩,
        ⟨98030, true, false, [37418, 37416], [1]⟩,
        ⟨97874, true, false, [37418, 37416], [1]⟩,
        ⟨102145, true, false, [37418, 37416, 37414], [5, 1]⟩,
        ⟨102144, false, true, [37418, 37416], [86245, 5, 1]⟩,
        ⟨50075, false, false, [37418, 37416, 37413], [1]⟩,
        ⟨102146, true, false, [37418, 37416], [88353, 1]⟩,
        ⟨102147, false, true, [], [88353, 1]⟩,
        ⟨50070, false, false, [37417], []⟩
      ]⟩,
    ⟨[37421], [37417, 18975], .source 18775⟩,
    ⟨[37423], [37420], .source 18776⟩,
    ⟨[37423], [37420], .contexts [
        ⟨102150, false, false, [], []⟩
      ]⟩,
    ⟨[37421], [37422], .contexts [
        ⟨102150, true, true, [], []⟩
      ]⟩,
    ⟨[96481], [37421, 86241], .contexts [
        ⟨102151, false, false, [37422], [96481]⟩,
        ⟨13, false, false, [37422, 37420], [96481]⟩,
        ⟨98028, true, false, [37422, 37420], []⟩,
        ⟨97877, true, false, [37422, 37420], []⟩,
        ⟨102148, false, false, [37422, 37420], []⟩,
        ⟨102149, true, false, [37422, 37420], [86241]⟩,
        ⟨102152, true, false, [], [86241]⟩
      ]⟩,
    ⟨[37420], [37420], .contexts []⟩,
    ⟨[86241, 9], [37423, 96483], .contexts [
        ⟨102153, true, false, [37420], [9]⟩,
        ⟨97880, false, false, [37420], []⟩,
        ⟨98027, false, false, [37420], []⟩,
        ⟨102154, true, false, [], [96483]⟩,
        ⟨102154, true, false, [], [96483]⟩,
        ⟨102151, true, false, [], [96483]⟩
      ]⟩,
    ⟨[37291, 87083], [37291, 87083], .contexts []⟩,
    ⟨[37291, 87083], [37291, 87083], .contexts []⟩,
    ⟨[84397, 9], [37291, 87083], .contexts [
        ⟨101945, false, false, [], []⟩,
        ⟨101949, false, false, [], []⟩,
        ⟨102156, false, false, [], []⟩,
        ⟨102157, false, false, [], []⟩,
        ⟨102157, false, false, [], []⟩
      ]⟩,
    ⟨[87085, 9], [87085, 9], .contexts []⟩,
    ⟨[37289], [37290], .contexts [
        ⟨101950, false, false, [], []⟩
      ]⟩,
    ⟨[37290], [37290], .contexts []⟩,
    ⟨[37289], [37290], .contexts [
        ⟨102160, false, false, [], []⟩,
        ⟨102161, false, false, [], []⟩,
        ⟨102161, false, false, [], []⟩
      ]⟩,
    ⟨[87085, 9], [37289, 84395], .contexts [
        ⟨102159, false, false, [], []⟩,
        ⟨40148, true, false, [], [9]⟩,
        ⟨102158, true, false, [37290], [3, 9]⟩,
        ⟨479, false, false, [37290, 84397], []⟩,
        ⟨21, false, false, [37290, 84397], []⟩,
        ⟨26985, false, false, [37290], []⟩,
        ⟨26986, false, false, [37290], []⟩,
        ⟨26744, false, false, [37290], []⟩,
        ⟨26744, false, false, [37290], []⟩,
        ⟨90851, false, false, [37290], []⟩,
        ⟨102162, true, false, [], [84395]⟩
      ]⟩,
    ⟨[84395, 9], [37291, 87085], .contexts [
        ⟨102163, true, false, [37288], [9]⟩,
        ⟨46, false, false, [37288, 87085], []⟩,
        ⟨101946, true, false, [], [87085]⟩
      ]⟩,
    ⟨[87083, 5], [87083, 5], .contexts []⟩,
    ⟨[87083, 5], [37289, 96053], .contexts [
        ⟨102165, false, false, [], []⟩,
        ⟨102158, true, false, [37290], [5]⟩,
        ⟨1079, false, false, [37290, 84397], []⟩,
        ⟨1080, false, false, [37290, 84397], []⟩,
        ⟨90879, false, false, [37290], [9]⟩,
        ⟨95782, false, false, [37290], []⟩,
        ⟨95784, false, false, [37290], []⟩,
        ⟨95785, false, false, [37290], []⟩,
        ⟨95785, false, false, [37290], []⟩,
        ⟨95793, false, false, [37290], []⟩,
        ⟨102162, true, false, [], [96053]⟩
      ]⟩,
    ⟨[37425], [33339, 37291], .source 18777⟩,
    ⟨[37427], [37289, 37425], .source 18778⟩,
    ⟨[37297, 87081], [37297, 87081], .contexts []⟩,
    ⟨[37297, 87081], [37297, 87081], .contexts []⟩,
    ⟨[37429], [37295, 36799], .source 18779⟩,
    ⟨[87081, 3], [37429, 84997], .contexts [
        ⟨102170, true, false, [37296], [3]⟩,
        ⟨102170, true, false, [37296], [3]⟩,
        ⟨102169, true, false, [37296], [3]⟩,
        ⟨101959, true, false, [37296], [3]⟩,
        ⟨101955, true, false, [37296], [3]⟩,
        ⟨63, false, false, [37296, 87219], []⟩,
        ⟨65, false, false, [37296, 87219], []⟩,
        ⟨40760, false, false, [37296], [13]⟩,
        ⟨101149, false, false, [37296], []⟩,
        ⟨101150, false, false, [37296], []⟩,
        ⟨101151, false, false, [37296], []⟩,
        ⟨101151, false, false, [37296], []⟩,
        ⟨101039, false, false, [37296, 36799], []⟩,
        ⟨101960, true, false, [], [36799, 84997]⟩,
        ⟨102171, true, false, [], [84997]⟩
      ]⟩,
    ⟨[37431], [37428], .source 18780⟩,
    ⟨[84997, 3], [37431, 87081], .contexts [
        ⟨102172, true, false, [37428], [3]⟩,
        ⟨20, false, false, [37428, 87081], []⟩,
        ⟨102173, true, false, [], [87081]⟩
      ]⟩,
    ⟨[37433], [19937, 37303], .source 18781⟩,
    ⟨[37303, 88561], [37303, 88561], .contexts []⟩,
    ⟨[87219, 11], [37303, 88561], .contexts [
        ⟨101970, false, false, [], []⟩,
        ⟨102176, false, false, [], []⟩,
        ⟨102176, false, false, [], []⟩
      ]⟩,
    ⟨[87219, 10], [87219, 11], .contexts [
        ⟨54, false, false, [87219], []⟩
      ]⟩,
    ⟨[88561, 1], [88561, 1], .contexts []⟩,
    ⟨[88561], [88561], .contexts []⟩,
    ⟨[37435], [37432], .source 18782⟩,
    ⟨[37437], [37435, 37303], .source 18783⟩,
    ⟨[37439], [18273, 37303], .source 18784⟩,
    ⟨[37305, 88571], [37305, 88571], .contexts []⟩,
    ⟨[37305, 88571], [37305, 88571], .contexts []⟩,
    ⟨[37443], [37305, 37165], .source 18786⟩,
    ⟨[37445], [37443, 37365], .source 18787⟩,
    ⟨[37447], [37444], .source 18788⟩,
    ⟨[37444], [37444], .contexts []⟩,
    ⟨[96471, 9], [37447, 88001], .contexts [
        ⟨102187, false, false, [37444], [96471, 9]⟩,
        ⟨102074, true, false, [37444, 37443], [9]⟩,
        ⟨102186, false, false, [37444], [94341, 5, 9]⟩,
        ⟨101660, true, false, [37444, 37305], [5, 9]⟩,
        ⟨102185, true, false, [37444], [9, 5, 9]⟩,
        ⟨102185, true, false, [37444], [9, 5, 9]⟩,
        ⟨102184, true, false, [37444], [9, 5, 9]⟩,
        ⟨101975, true, false, [37444], [9, 5, 9]⟩,
        ⟨101973, true, false, [37444], [9, 5, 9]⟩,
        ⟨882, false, false, [37444, 88001], []⟩,
        ⟨96310, false, false, [37444], []⟩,
        ⟨102189, true, false, [], [88001]⟩,
        ⟨102189, true, false, [], [88001]⟩,
        ⟨102188, true, false, [], [88001]⟩
      ]⟩,
    ⟨[37445], [37446], .contexts [
        ⟨102188, true, true, [], []⟩
      ]⟩,
    ⟨[96471], [37447, 87999], .contexts [
        ⟨102191, false, false, [37444], [96471]⟩,
        ⟨46, true, false, [37444, 37446, 96471], []⟩,
        ⟨102190, false, false, [37444, 37446], [9]⟩,
        ⟨57375, false, false, [37444], []⟩,
        ⟨102188, true, false, [], [87999]⟩
      ]⟩,
    ⟨[37449], [37445, 35619], .source 18789⟩,
    ⟨[87999, 11], [37449, 96291], .contexts [
        ⟨102192, true, false, [37446], [11]⟩,
        ⟨97861, false, false, [37446], []⟩,
        ⟨102191, true, false, [], [35619, 96291]⟩,
        ⟨102193, true, false, [], [96291]⟩
      ]⟩,
    ⟨[37451], [37445, 37367], .source 18790⟩,
    ⟨[96471], [37447, 87999], .contexts [
        ⟨102192, false, false, [], []⟩
      ]⟩,
    ⟨[96471], [37447, 87999], .contexts [
        ⟨102196, false, false, [], []⟩
      ]⟩,
    ⟨[37453], [37447, 35163], .source 18791⟩,
    ⟨[37455], [37452], .source 18792⟩,
    ⟨[37457], [37455, 37411], .source 18793⟩,
    ⟨[96139], [37457, 84399], .contexts [
        ⟨102198, false, false, [37452], [96139]⟩,
        ⟨96322, true, false, [37452, 37447], []⟩,
        ⟨102197, true, false, [37452], [15]⟩,
        ⟨97865, false, false, [37452], []⟩,
        ⟨102141, false, false, [37452], []⟩,
        ⟨102133, true, false, [37452], [84399]⟩,
        ⟨102199, true, false, [], [37411, 84399]⟩,
        ⟨102200, true, false, [], [84399]⟩
      ]⟩,
    ⟨[96139], [37457, 84399], .contexts [
        ⟨102201, false, false, [], []⟩
      ]⟩,
    ⟨[96139], [37457, 84399], .contexts [
        ⟨102202, false, false, [], []⟩
      ]⟩,
    ⟨[37459], [37456], .source 18794⟩,
    ⟨[37461], [37459, 35313], .source 18795⟩,
    ⟨[37461], [37456, 35313], .contexts [
        ⟨102205, false, false, [], []⟩,
        ⟨102204, false, false, [], [35313]⟩
      ]⟩,
    ⟨[84399, 7], [37461, 96267], .contexts [
        ⟨102201, true, false, [37456], [7]⟩,
        ⟨96973, true, false, [37456, 35310], [7]⟩,
        ⟨38, false, false, [37456, 35310, 96267], []⟩,
        ⟨96914, true, false, [37456], [96267]⟩,
        ⟨96971, false, false, [37456], []⟩,
        ⟨102206, true, false, [], [96267]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1597. -/
def y322TCIndexRaw1597 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[37457, 96053], [37457, 96053], .contexts []⟩,
    ⟨[37459], [37456], .contexts [
        ⟨102204, false, false, [], []⟩,
        ⟨13, false, false, [37456], []⟩
      ]⟩,
    ⟨[37457], [37458], .contexts [
        ⟨102204, true, true, [], []⟩
      ]⟩,
    ⟨[96141], [37457, 96053], .contexts [
        ⟨102209, false, false, [37458], [96141]⟩,
        ⟨96009, true, false, [37458, 37456], []⟩,
        ⟨95949, true, false, [37458, 37456], []⟩,
        ⟨102203, false, false, [37458, 37456], [9]⟩,
        ⟨95780, false, false, [37458], []⟩,
        ⟨102208, false, false, [37458, 37456], []⟩,
        ⟨102210, true, false, [], [96053]⟩
      ]⟩,
    ⟨[96141], [37457, 96053], .contexts [
        ⟨102211, false, false, [], []⟩
      ]⟩,
    ⟨[96141], [37457, 96053], .contexts [
        ⟨102212, false, false, [], []⟩,
        ⟨102208, false, false, [], []⟩
      ]⟩,
    ⟨[37463], [37459, 35161], .source 18796⟩,
    ⟨[37463], [37456, 35161], .contexts [
        ⟨102214, false, false, [], []⟩,
        ⟨102204, false, false, [], [35161]⟩
      ]⟩,
    ⟨[37457, 96055], [37457, 96055], .contexts []⟩,
    ⟨[96143], [37457, 96055], .contexts [
        ⟨102209, false, false, [37458], [96143]⟩,
        ⟨96007, true, false, [37458, 37456], []⟩,
        ⟨95952, true, false, [37458, 37456], []⟩,
        ⟨102213, false, false, [37458, 37456], [11]⟩,
        ⟨95796, false, false, [37458], []⟩,
        ⟨102216, false, false, [37458, 37456], []⟩,
        ⟨102210, true, false, [], [96055]⟩
      ]⟩,
    ⟨[96143], [37457, 96055], .contexts [
        ⟨102217, false, false, [], []⟩,
        ⟨102216, false, false, [], []⟩
      ]⟩,
    ⟨[37457, 96057], [37457, 96057], .contexts []⟩,
    ⟨[96145], [37457, 96057], .contexts [
        ⟨102209, false, false, [37458], [96145]⟩,
        ⟨96005, true, false, [37458, 37456], []⟩,
        ⟨95956, true, false, [37458, 37456], []⟩,
        ⟨102218, false, false, [37458, 37456], [1]⟩,
        ⟨95805, false, false, [37458], []⟩,
        ⟨102219, false, false, [37458, 37456], []⟩,
        ⟨102210, true, false, [], [96057]⟩
      ]⟩,
    ⟨[96145], [37457, 96057], .contexts [
        ⟨102220, false, false, [], []⟩,
        ⟨102219, false, false, [], []⟩
      ]⟩,
    ⟨[37457, 96059], [37457, 96059], .contexts []⟩,
    ⟨[96147], [37457, 96059], .contexts [
        ⟨102209, false, false, [37458], [96147]⟩,
        ⟨96003, true, false, [37458, 37456], []⟩,
        ⟨95959, true, false, [37458, 37456], []⟩,
        ⟨102221, false, false, [37458, 37456], [13]⟩,
        ⟨95808, false, false, [37458], []⟩,
        ⟨102222, false, false, [37458, 37456], []⟩,
        ⟨102210, true, false, [], [96059]⟩
      ]⟩,
    ⟨[96147], [37457, 96059], .contexts [
        ⟨102223, false, false, [], []⟩,
        ⟨102222, false, false, [], []⟩
      ]⟩,
    ⟨[96059, 7], [37461, 96275], .contexts [
        ⟨102223, true, false, [37456], [7]⟩,
        ⟨96931, true, false, [37456, 35310], [7]⟩,
        ⟨38, false, false, [37456, 35310, 96275], []⟩,
        ⟨96914, true, false, [37456], [96275]⟩,
        ⟨102206, true, false, [], [96275]⟩
      ]⟩,
    ⟨[37465], [37459, 35779], .source 18797⟩,
    ⟨[37457, 96061], [37457, 96061], .contexts []⟩,
    ⟨[96149], [37457, 96061], .contexts [
        ⟨102209, false, false, [37458], [96149]⟩,
        ⟨96001, true, false, [37458, 37456], []⟩,
        ⟨95963, true, false, [37458, 37456], []⟩,
        ⟨102224, false, false, [37458, 37456], [15]⟩,
        ⟨95823, false, false, [37458], []⟩,
        ⟨102227, false, false, [37458, 37456], []⟩,
        ⟨102210, true, false, [], [96061]⟩
      ]⟩,
    ⟨[35127, 96149], [35127, 37457, 96061], .contexts [
        ⟨102228, false, false, [35127], []⟩
      ]⟩,
    ⟨[37467], [35127, 37457], .source 18798⟩,
    ⟨[37469], [37459, 35137], .source 18799⟩,
    ⟨[96061, 9], [37469, 87785], .contexts [
        ⟨102228, true, false, [37456], [9]⟩,
        ⟨96199, true, false, [37456, 35134], [9]⟩,
        ⟨46, false, false, [37456, 35134, 87785], []⟩,
        ⟨96200, true, false, [37456], [87785]⟩,
        ⟨102204, true, false, [], [35137, 87785]⟩,
        ⟨102231, true, false, [], [87785]⟩
      ]⟩,
    ⟨[37471], [37459, 35145], .source 18800⟩,
    ⟨[96149], [37457, 96061], .contexts [
        ⟨102228, false, false, [], []⟩
      ]⟩,
    ⟨[96149], [37457, 96061], .contexts [
        ⟨102234, false, false, [], []⟩,
        ⟨102227, false, false, [], []⟩
      ]⟩,
    ⟨[37473], [37459, 35125], .source 18801⟩,
    ⟨[96063], [37473, 93267], .contexts [
        ⟨95832, true, false, [], []⟩,
        ⟨102235, true, false, [37456], [3]⟩,
        ⟨96184, false, false, [37456], []⟩,
        ⟨102204, true, false, [], [35125, 93267]⟩,
        ⟨102236, true, false, [], [93267]⟩
      ]⟩,
    ⟨[37473, 93265], [37473, 93265], .contexts []⟩,
    ⟨[37475], [37472], .source 18802⟩,
    ⟨[37477], [37473, 29883], .source 18803⟩,
    ⟨[37477, 88091], [96067], .contexts [
        ⟨102240, false, false, [], [88091]⟩,
        ⟨78334, true, false, [37473], []⟩,
        ⟨102238, true, false, [], [1]⟩,
        ⟨102239, true, true, [], [93265, 1]⟩,
        ⟨102238, true, false, [37474, 37472], [1]⟩,
        ⟨78072, true, false, [37474], [1]⟩,
        ⟨102237, true, false, [37474, 37472], [5, 1]⟩,
        ⟨95834, false, false, [37474, 37472], [1]⟩,
        ⟨96056, false, false, [37474, 37472], [1]⟩,
        ⟨13, true, false, [37474, 37472], [96065, 1]⟩,
        ⟨102239, true, false, [37474], [96065, 1]⟩,
        ⟨95837, false, false, [], []⟩,
        ⟨96055, false, false, [], []⟩
      ]⟩,
    ⟨[37479], [37476], .source 18804⟩,
    ⟨[37479], [37476], .contexts [
        ⟨102242, false, false, [], []⟩,
        ⟨13, false, false, [37476], []⟩
      ]⟩,
    ⟨[37477], [37478], .contexts [
        ⟨102242, true, true, [], []⟩
      ]⟩,
    ⟨[37477, 85503], [37477, 85503], .contexts []⟩,
    ⟨[96069, 11], [37477, 21743, 87797], .contexts [
        ⟨102243, false, false, [37478], [96069, 11]⟩,
        ⟨96054, true, false, [37478, 37476], [11]⟩,
        ⟨95840, true, false, [37478, 37476], [11]⟩,
        ⟨102243, false, false, [37478, 37476, 37478], [96067, 9, 11]⟩,
        ⟨102241, true, false, [37478, 37476, 37478, 37476], [9, 11]⟩,
        ⟨102244, true, false, [37478, 37476], [88091, 9, 11]⟩,
        ⟨48367, false, false, [37478], [11]⟩,
        ⟨102245, false, false, [37478, 37476], [11]⟩,
        ⟨102244, true, false, [], [85503, 11]⟩,
        ⟨102245, false, false, [], [11]⟩,
        ⟨46295, false, false, [37477], []⟩
      ]⟩,
    ⟨[37481], [37477, 21743], .source 18805⟩,
    ⟨[37483], [37480], .source 18806⟩,
    ⟨[37483], [37480], .contexts [
        ⟨102248, false, false, [], []⟩,
        ⟨13, false, false, [37480], []⟩
      ]⟩,
    ⟨[37481], [37482], .contexts [
        ⟨102248, true, true, [], []⟩
      ]⟩,
    ⟨[37481, 87795], [37481, 87795], .contexts []⟩,
    ⟨[96073], [37481, 87795], .contexts [
        ⟨102249, false, false, [37482], [96073]⟩,
        ⟨96052, true, false, [37482, 37480], []⟩,
        ⟨95846, true, false, [37482, 37480], []⟩,
        ⟨102249, false, false, [37482, 37480, 37482], [96071, 1]⟩,
        ⟨96053, true, false, [37482, 37480, 37482, 37480], [1]⟩,
        ⟨95843, true, false, [37482, 37480, 37482, 37480], [1]⟩,
        ⟨102246, false, false, [37482, 37480, 37482, 37480], [1]⟩,
        ⟨102247, true, false, [37482, 37480, 37482, 37480], [87797, 1]⟩,
        ⟨102250, true, false, [37482, 37480], [87797, 1]⟩,
        ⟨46046, false, false, [37482], []⟩,
        ⟨102251, false, false, [37482, 37480], []⟩,
        ⟨102250, true, false, [], [87795]⟩
      ]⟩,
    ⟨[96073], [37481, 87795], .contexts [
        ⟨102252, false, false, [], []⟩
      ]⟩,
    ⟨[37485], [37481, 35097], .source 18807⟩,
    ⟨[37487], [37484], .source 18808⟩,
    ⟨[96165], [37487, 96075], .contexts [
        ⟨102254, false, false, [37484], [96165]⟩,
        ⟨96140, true, false, [37484, 37481], []⟩,
        ⟨102251, true, false, [37484], [13]⟩,
        ⟨102253, true, false, [37484], [13]⟩,
        ⟨95849, false, false, [37484], []⟩,
        ⟨96050, false, false, [37484], []⟩,
        ⟨13, true, false, [37484], [96075]⟩,
        ⟨102255, true, false, [], [96075]⟩
      ]⟩,
    ⟨[35071, 96165], [35071, 37487, 96075], .contexts [
        ⟨102256, false, false, [35071], []⟩
      ]⟩,
    ⟨[37489], [35071, 37487], .source 18809⟩,
    ⟨[96167], [37489, 96075], .contexts [
        ⟨97302, false, false, [], []⟩,
        ⟨102257, false, false, [], []⟩,
        ⟨102258, true, false, [], [96075]⟩
      ]⟩,
    ⟨[37485], [37486], .contexts [
        ⟨102255, true, true, [], []⟩
      ]⟩,
    ⟨[37491], [37485, 35067], .source 18810⟩,
    ⟨[37491], [37486, 35067], .contexts [
        ⟨102261, false, false, [], []⟩,
        ⟨102260, false, false, [], [35067]⟩
      ]⟩,
    ⟨[96075, 1], [37491, 90615], .contexts [
        ⟨102256, true, false, [37486], [1]⟩,
        ⟨96094, false, false, [37486], []⟩,
        ⟨96098, false, false, [37486], []⟩,
        ⟨102262, true, false, [], [90615]⟩
      ]⟩,
    ⟨[37493], [37485, 35079], .source 18811⟩,
    ⟨[96075, 3], [37493, 85715], .contexts [
        ⟨102256, true, false, [37486], [3]⟩,
        ⟨96111, false, false, [37486], []⟩,
        ⟨96212, false, false, [37486], []⟩,
        ⟨102260, true, false, [], [35079, 85715]⟩,
        ⟨102264, true, false, [], [85715]⟩
      ]⟩,
    ⟨[37495], [37485, 35085], .source 18812⟩,
    ⟨[37497], [37485, 35091], .source 18813⟩,
    ⟨[37499], [37485, 35107], .source 18814⟩,
    ⟨[96075, 9], [37499, 86905], .contexts [
        ⟨102256, true, false, [37486], [9]⟩,
        ⟨96162, false, false, [37486], []⟩,
        ⟨96210, false, false, [37486], []⟩,
        ⟨102260, true, false, [], [35107, 86905]⟩,
        ⟨102268, true, false, [], [86905]⟩
      ]⟩,
    ⟨[96165], [37487, 96075], .contexts [
        ⟨102256, false, false, [], []⟩
      ]⟩,
    ⟨[96165], [37487, 96075], .contexts [
        ⟨102270, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 1598. -/
def y322TCIndexRaw1598 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[37501], [37485, 37489], .source 18815⟩,
    ⟨[96077], [37501, 96075], .contexts [
        ⟨95853, true, false, [], []⟩,
        ⟨102271, true, false, [37486], [15]⟩,
        ⟨95990, false, false, [37486], []⟩,
        ⟨102259, false, false, [37486], []⟩,
        ⟨102260, true, false, [], [37489, 96075]⟩,
        ⟨102272, true, false, [], [96075]⟩
      ]⟩,
    ⟨[37503], [37501, 37491], .source 18816⟩,
    ⟨[37505], [37502], .source 18817⟩,
    ⟨[37507], [37503, 16219], .source 18818⟩,
    ⟨[37507, 83199], [96081], .contexts [
        ⟨102276, false, false, [], [83199]⟩,
        ⟨62097, true, false, [37503], []⟩,
        ⟨102275, true, true, [], [90615, 3]⟩,
        ⟨102274, false, false, [37504, 37502], [90615, 3]⟩,
        ⟨102263, true, false, [37504, 37502, 37501], [3]⟩,
        ⟨102273, true, false, [37504, 37502], [1, 3]⟩,
        ⟨95856, false, false, [37504, 37502], [3]⟩,
        ⟨96049, false, false, [37504, 37502], [3]⟩,
        ⟨13, true, false, [37504, 37502], [96079, 3]⟩,
        ⟨102275, true, false, [37504], [96079, 3]⟩,
        ⟨95859, false, false, [], []⟩,
        ⟨96048, false, false, [], []⟩
      ]⟩,
    ⟨[37509], [37506], .source 18819⟩,
    ⟨[37509], [37506], .contexts [
        ⟨102278, false, false, [], []⟩,
        ⟨13, false, false, [37506], []⟩
      ]⟩,
    ⟨[37507], [37508], .contexts [
        ⟨102278, true, true, [], []⟩
      ]⟩,
    ⟨[37507, 82819], [37507, 82819], .contexts []⟩,
    ⟨[96083, 1], [37507, 15551, 81373], .contexts [
        ⟨102279, false, false, [37508], [96083, 1]⟩,
        ⟨96046, true, false, [37508, 37506], [1]⟩,
        ⟨95862, true, false, [37508, 37506], [1]⟩,
        ⟨102279, false, false, [37508, 37506, 37508], [96081, 5, 1]⟩,
        ⟨102277, true, false, [37508, 37506, 37508, 37506], [5, 1]⟩,
        ⟨102280, true, false, [37508, 37506], [83199, 5, 1]⟩,
        ⟨19839, false, false, [37508], [1]⟩,
        ⟨102281, false, false, [37508, 37506], [1]⟩,
        ⟨102280, true, false, [], [82819, 1]⟩,
        ⟨102281, false, false, [], [1]⟩,
        ⟨17044, false, false, [37507], []⟩
      ]⟩,
    ⟨[37511], [37507, 15551], .source 18820⟩,
    ⟨[37513], [37510], .source 18821⟩,
    ⟨[37515], [37511, 4217], .source 18822⟩,
    ⟨[37517], [37514], .source 18823⟩,
    ⟨[37517], [37514], .contexts [
        ⟨102286, false, false, [], []⟩,
        ⟨13, false, false, [37514], []⟩
      ]⟩,
    ⟨[37515], [37516], .contexts [
        ⟨102286, true, true, [], []⟩
      ]⟩,
    ⟨[96087], [37515, 81373], .contexts [
        ⟨102287, false, false, [37516], [96087]⟩,
        ⟨96044, true, false, [37516, 37514], []⟩,
        ⟨95868, true, false, [37516, 37514], []⟩,
        ⟨102284, false, false, [37516, 37514, 37512], [96085, 9]⟩,
        ⟨13, false, false, [37516, 37514, 37512, 37510], [96085, 9]⟩,
        ⟨96045, true, false, [37516, 37514, 37512, 37510], [9]⟩,
        ⟨95865, true, false, [37516, 37514, 37512, 37510], [9]⟩,
        ⟨102282, false, false, [37516, 37514, 37512, 37510], [9]⟩,
        ⟨102283, true, false, [37516, 37514, 37512, 37510], [81373, 9]⟩,
        ⟨102284, false, true, [37516, 37514], [81373, 9]⟩,
        ⟨8955, false, false, [37516, 37514, 37511], []⟩,
        ⟨102285, true, false, [37516, 37514], [81373]⟩,
        ⟨102288, true, false, [], [81373]⟩
      ]⟩,
    ⟨[37515, 83347], [37515, 83347], .contexts []⟩,
    ⟨[37519], [37515, 15553], .source 18824⟩,
    ⟨[37519, 82785], [96091], .contexts [
        ⟨102291, false, false, [], [82785]⟩,
        ⟨20709, true, false, [37515], []⟩,
        ⟨102290, true, false, [], [1]⟩,
        ⟨102288, false, false, [], [83347, 1]⟩,
        ⟨102290, true, false, [37516, 37514], [1]⟩,
        ⟨20701, true, false, [37516], [1]⟩,
        ⟨102289, true, false, [37516, 37514], [11, 1]⟩,
        ⟨95871, false, false, [37516, 37514], [1]⟩,
        ⟨96043, false, false, [37516, 37514], [1]⟩,
        ⟨102287, true, false, [37516], [96089, 1]⟩,
        ⟨95874, false, false, [], []⟩
      ]⟩,
    ⟨[37521], [37518], .source 18825⟩,
    ⟨[37521], [37518], .contexts [
        ⟨102293, false, false, [], []⟩,
        ⟨13, false, false, [37518], []⟩
      ]⟩,
    ⟨[37519], [37520], .contexts [
        ⟨102293, true, true, [], []⟩
      ]⟩,
    ⟨[37519, 79367], [37519, 79367], .contexts []⟩,
    ⟨[96093, 15], [37519, 15225, 82659], .contexts [
        ⟨102294, false, false, [37520], [96093, 15]⟩,
        ⟨96040, true, false, [37520, 37518], [15]⟩,
        ⟨95877, true, false, [37520, 37518], [15]⟩,
        ⟨102294, false, false, [37520, 37518, 37520], [96091, 13, 15]⟩,
        ⟨96041, true, false, [37520, 37518, 37520, 37518], [13, 15]⟩,
        ⟨102292, true, false, [37520, 37518, 37520, 37518], [13, 15]⟩,
        ⟨102295, true, false, [37520, 37518], [82785, 13, 15]⟩,
        ⟨16618, false, false, [37520], [15]⟩,
        ⟨102296, false, false, [37520, 37518], [15]⟩,
        ⟨102295, true, false, [], [79367, 15]⟩,
        ⟨102296, false, false, [], [15]⟩,
        ⟨15059, false, false, [37519], []⟩
      ]⟩,
    ⟨[37523], [37519, 15225], .source 18826⟩,
    ⟨[37525], [37522], .source 18827⟩,
    ⟨[37527], [37523, 11907], .source 18828⟩,
    ⟨[37529], [37526], .source 18829⟩,
    ⟨[96097], [37528, 82649], .contexts [
        ⟨102301, false, false, [37528], [96097]⟩,
        ⟨13, false, false, [37528, 37526], [96097]⟩,
        ⟨96038, true, false, [37528, 37526], []⟩,
        ⟨95883, true, false, [37528, 37526], []⟩,
        ⟨102299, false, false, [37528, 37526, 37524], [96095, 1]⟩,
        ⟨13, false, false, [37528, 37526, 37524, 37522], [96095, 1]⟩,
        ⟨96039, true, false, [37528, 37526, 37524, 37522], [1]⟩,
        ⟨95880, true, false, [37528, 37526, 37524, 37522], [1]⟩,
        ⟨102297, false, false, [37528, 37526, 37524, 37522], [1]⟩,
        ⟨102298, true, false, [37528, 37526, 37524, 37522], [82659, 1]⟩,
        ⟨102299, false, true, [37528, 37526], [82659, 1]⟩,
        ⟨15041, false, false, [37528, 37526, 37523], []⟩,
        ⟨102300, true, false, [37528, 37526], [82649]⟩
      ]⟩,
    ⟨[37531], [37527, 561], .source 18830⟩,
    ⟨[37533], [37530], .source 18831⟩,
    ⟨[37533], [37530], .contexts [
        ⟨102304, false, false, [], []⟩,
        ⟨13, false, false, [37530], []⟩
      ]⟩,
    ⟨[37531], [37532], .contexts [
        ⟨102304, true, true, [], []⟩
      ]⟩,
    ⟨[96099, 5], [37531, 82651], .contexts [
        ⟨102305, false, false, [37532], [96099, 5]⟩,
        ⟨96036, true, false, [37532, 37530], [5]⟩,
        ⟨95886, true, false, [37532, 37530], [5]⟩,
        ⟨102302, false, false, [37532, 37530], [3, 5]⟩,
        ⟨102301, false, true, [37532, 37530], [82649, 3, 5]⟩,
        ⟨14933, false, false, [37532, 37530, 37527], [5]⟩,
        ⟨102303, true, false, [37532, 37530], [82649, 5]⟩,
        ⟨102306, true, false, [], [82649, 5]⟩,
        ⟨14945, false, false, [37531], []⟩
      ]⟩,
    ⟨[37531, 82651], [37531, 82651], .contexts []⟩,
    ⟨[37535], [37531, 15221], .source 18832⟩,
    ⟨[37537], [37534], .source 18833⟩,
    ⟨[96103], [37535, 82661], .contexts [
        ⟨102310, false, false, [37536], [96103]⟩,
        ⟨13, false, false, [37536, 37534], [96103]⟩,
        ⟨96034, true, false, [37536, 37534], []⟩,
        ⟨95892, true, false, [37536, 37534], []⟩,
        ⟨102305, false, false, [37536, 37534, 37532], [96101, 1]⟩,
        ⟨96035, true, false, [37536, 37534, 37532, 37530], [1]⟩,
        ⟨95889, true, false, [37536, 37534, 37532, 37530], [1]⟩,
        ⟨102307, false, false, [37536, 37534, 37532, 37530], [1]⟩,
        ⟨102308, false, false, [37536, 37534, 37532, 37530], [1]⟩,
        ⟨102306, true, false, [37536, 37534], [82651, 1]⟩,
        ⟨102308, false, false, [37536, 37534], [1]⟩,
        ⟨15071, false, false, [37536, 37534, 37531], []⟩,
        ⟨102309, true, false, [37536, 37534], [82661]⟩,
        ⟨102310, false, true, [], [82661]⟩
      ]⟩,
    ⟨[37539], [37535, 15227], .source 18834⟩,
    ⟨[37541], [37538], .source 18835⟩,
    ⟨[37543], [37539, 16197], .source 18836⟩,
    ⟨[37543, 83357], [96107], .contexts [
        ⟨102314, false, false, [], [83357]⟩,
        ⟨20882, true, false, [37539], []⟩,
        ⟨102313, true, true, [], [82845, 11]⟩,
        ⟨102312, false, false, [37540, 37538], [82845, 11]⟩,
        ⟨17403, true, false, [37540, 37538, 37535], [11]⟩,
        ⟨102311, true, false, [37540, 37538], [9, 11]⟩,
        ⟨95895, false, false, [37540, 37538], [11]⟩,
        ⟨96033, false, false, [37540, 37538], [11]⟩,
        ⟨13, true, false, [37540, 37538], [96105, 11]⟩,
        ⟨102313, true, false, [37540], [96105, 11]⟩,
        ⟨95898, false, false, [], []⟩,
        ⟨96031, false, false, [], []⟩
      ]⟩,
    ⟨[37545], [37542], .source 18837⟩,
    ⟨[37547], [37543, 2409], .source 18838⟩,
    ⟨[37549], [37546], .source 18839⟩,
    ⟨[96109], [37547, 83357], .contexts [
        ⟨102318, false, false, [37548], [96109]⟩,
        ⟨13, false, false, [37548, 37546], [96109]⟩,
        ⟨96030, true, false, [37548, 37546], []⟩,
        ⟨95901, true, false, [37548, 37546], []⟩,
        ⟨102316, false, false, [37548, 37546, 37544], [96107, 1]⟩,
        ⟨13, false, false, [37548, 37546, 37544, 37542], [96107, 1]⟩,
        ⟨102315, true, false, [37548, 37546, 37544, 37542], [1]⟩,
        ⟨102316, false, true, [37548, 37546], [83357, 1]⟩,
        ⟨20867, false, false, [37548, 37546, 37543], []⟩,
        ⟨102317, true, false, [37548, 37546], [83357]⟩,
        ⟨102318, false, true, [], [83357]⟩
      ]⟩,
    ⟨[37551], [37547, 11869], .source 18840⟩,
    ⟨[37553], [37550], .source 18841⟩,
    ⟨[37555], [37551, 11863], .source 18842⟩,
    ⟨[37557], [37554], .source 18843⟩,
    ⟨[82787], [37557, 96113], .contexts [
        ⟨102322, false, false, [37554], [82787]⟩,
        ⟨20890, true, false, [37554, 37551], []⟩,
        ⟨102321, true, true, [37554], [83357, 15]⟩,
        ⟨102320, false, false, [37554, 37552, 37550], [83357, 15]⟩,
        ⟨20886, true, false, [37554, 37552, 37550, 37547], [15]⟩,
        ⟨102319, true, false, [37554, 37552, 37550], [13, 15]⟩,
        ⟨95904, false, false, [37554, 37552, 37550], [15]⟩,
        ⟨96029, false, false, [37554, 37552, 37550], [15]⟩,
        ⟨13, true, false, [37554, 37552, 37550], [96111, 15]⟩,
        ⟨102321, true, false, [37554, 37552], [96111, 15]⟩,
        ⟨95907, false, false, [37554], []⟩,
        ⟨96028, false, false, [37554], []⟩,
        ⟨13, true, false, [37554], [96113]⟩,
        ⟨102323, true, false, [], [96113]⟩
      ]⟩,
    ⟨[37559], [37555, 563], .source 18844⟩,
    ⟨[37561], [37558], .source 18845⟩,
    ⟨[96115, 3], [37559, 22677, 88343], .contexts [
        ⟨102326, false, false, [37560], [96115, 3]⟩,
        ⟨13, false, false, [37560, 37558], [96115, 3]⟩,
        ⟨96026, true, false, [37560, 37558], [3]⟩,
        ⟨95910, true, false, [37560, 37558], [3]⟩,
        ⟨102324, true, false, [37560, 37558, 37556], [1, 3]⟩,
        ⟨102323, false, true, [37560, 37558], [82787, 1, 3]⟩,
        ⟨16645, false, false, [37560, 37558, 37555], [3]⟩,
        ⟨102325, true, false, [37560, 37558], [82787, 3]⟩,
        ⟨102326, false, true, [], [82787, 3]⟩,
        ⟨49976, false, false, [37559], []⟩
      ]⟩,
    ⟨[37563], [37559, 22677], .source 18846⟩,
    ⟨[37565], [37562], .source 18847⟩,
    ⟨[37565], [37562], .contexts [
        ⟨102329, false, false, [], []⟩,
        ⟨13, false, false, [37562], []⟩
      ]⟩,
    ⟨[37563], [37564], .contexts [
        ⟨102329, true, true, [], []⟩
      ]⟩,
    ⟨[37563, 85259], [37563, 85259], .contexts []⟩,
    ⟨[96119], [37563, 85259], .contexts [
        ⟨102330, false, false, [37564], [96119]⟩,
        ⟨96024, true, false, [37564, 37562], []⟩,
        ⟨95916, true, false, [37564, 37562], []⟩,
        ⟨102330, false, false, [37564, 37562, 37564], [96117, 5]⟩,
        ⟨96025, true, false, [37564, 37562, 37564, 37562], [5]⟩,
        ⟨95913, true, false, [37564, 37562, 37564, 37562], [5]⟩,
        ⟨102327, false, false, [37564, 37562, 37564, 37562], [5]⟩,
        ⟨102328, true, false, [37564, 37562, 37564, 37562], [88343, 5]⟩,
        ⟨102331, true, false, [37564, 37562], [88343, 5]⟩,
        ⟨49956, false, false, [37564], []⟩,
        ⟨102332, false, false, [37564, 37562], []⟩,
        ⟨102331, true, false, [], [85259]⟩
      ]⟩,
    ⟨[37567], [37563, 20773], .source 18848⟩,
    ⟨[37569], [37566], .source 18849⟩]

/-- Exact literal claimed equations and contextual derivations, block 1599. -/
def y322TCIndexRaw1599 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[37571], [37567, 19893], .source 18850⟩,
    ⟨[37571, 83895], [96123], .contexts [
        ⟨102336, false, false, [], [83895]⟩,
        ⟨40414, true, false, [37567], []⟩,
        ⟨102335, true, true, [], [83325, 9]⟩,
        ⟨102334, false, false, [37568, 37566], [83325, 9]⟩,
        ⟨42690, true, false, [37568, 37566, 37563], [9]⟩,
        ⟨102332, true, false, [37568, 37566], [1, 9]⟩,
        ⟨102333, true, false, [37568, 37566], [1, 9]⟩,
        ⟨95919, false, false, [37568, 37566], [9]⟩,
        ⟨96023, false, false, [37568, 37566], [9]⟩,
        ⟨13, true, false, [37568, 37566], [96121, 9]⟩,
        ⟨102335, true, false, [37568], [96121, 9]⟩,
        ⟨95922, false, false, [], []⟩,
        ⟨96021, false, false, [], []⟩
      ]⟩,
    ⟨[37573], [37570], .source 18851⟩,
    ⟨[37573], [37570], .contexts [
        ⟨102338, false, false, [], []⟩,
        ⟨13, false, false, [37570], []⟩
      ]⟩,
    ⟨[37571], [37572], .contexts [
        ⟨102338, true, true, [], []⟩
      ]⟩,
    ⟨[37571, 96047], [37571, 96047], .contexts []⟩,
    ⟨[96125, 1], [37571, 21509, 88089], .contexts [
        ⟨102339, false, false, [37572], [96125, 1]⟩,
        ⟨96020, true, false, [37572, 37570], [1]⟩,
        ⟨95925, true, false, [37572, 37570], [1]⟩,
        ⟨102339, false, false, [37572, 37570, 37572], [96123, 11, 1]⟩,
        ⟨102337, true, false, [37572, 37570, 37572, 37570], [11, 1]⟩,
        ⟨102340, true, false, [37572, 37570], [83895, 11, 1]⟩,
        ⟨95620, false, false, [37572], [1]⟩,
        ⟨102341, false, false, [37572, 37570], [1]⟩,
        ⟨102340, true, false, [], [96047, 1]⟩,
        ⟨102341, false, false, [], [1]⟩,
        ⟨95624, false, false, [37571], []⟩
      ]⟩,
    ⟨[37575], [37571, 21509], .source 18852⟩,
    ⟨[37577], [37574], .source 18853⟩,
    ⟨[96127], [37575, 88089], .contexts [
        ⟨102344, false, false, [37576], [96127]⟩,
        ⟨13, false, false, [37576, 37574], [96127]⟩,
        ⟨96019, true, false, [37576, 37574], []⟩,
        ⟨95928, true, false, [37576, 37574], []⟩,
        ⟨102342, false, false, [37576, 37574], []⟩,
        ⟨102343, true, false, [37576, 37574], [88089]⟩,
        ⟨102344, false, true, [], [88089]⟩
      ]⟩,
    ⟨[37579], [37577, 35161], .source 18854⟩,
    ⟨[96049], [37579, 87991], .contexts [
        ⟨95648, true, false, [], []⟩,
        ⟨102345, true, false, [37574], [13]⟩,
        ⟨95931, false, false, [37574], []⟩,
        ⟨96346, false, false, [37574], []⟩,
        ⟨96341, false, false, [37574], []⟩,
        ⟨96345, true, false, [37574], [87991]⟩,
        ⟨102344, true, false, [], [35161, 87991]⟩,
        ⟨102346, true, false, [], [87991]⟩
      ]⟩,
    ⟨[37581], [37578], .source 18855⟩,
    ⟨[37581], [37578], .contexts [
        ⟨102348, false, false, [], []⟩
      ]⟩,
    ⟨[37578], [37578], .contexts []⟩,
    ⟨[37581], [37578], .contexts [
        ⟨102349, false, false, [], []⟩,
        ⟨102350, false, false, [], []⟩,
        ⟨102350, false, false, [], []⟩
      ]⟩,
    ⟨[87991, 3], [37581, 84391], .contexts [
        ⟨102347, true, false, [37578], [3]⟩,
        ⟨95652, false, false, [37578], []⟩,
        ⟨26989, false, false, [37578], []⟩,
        ⟨102351, true, false, [], [84391]⟩
      ]⟩,
    ⟨[37583], [37581, 22241], .source 18856⟩,
    ⟨[37583], [37578, 22241], .contexts [
        ⟨102353, false, false, [], []⟩,
        ⟨102348, false, false, [], [22241]⟩
      ]⟩,
    ⟨[37585], [37581, 22257], .source 18857⟩,
    ⟨[37585], [37578, 22257], .contexts [
        ⟨102355, false, false, [], []⟩,
        ⟨102348, false, false, [], [22257]⟩
      ]⟩,
    ⟨[37587], [37581, 34991], .source 18858⟩,
    ⟨[87991, 9], [37583, 96755], .contexts [
        ⟨102347, true, false, [37578], [9]⟩,
        ⟨99861, true, false, [37578, 22242], [9]⟩,
        ⟨46, false, false, [37578, 22242, 96755], []⟩,
        ⟨48261, true, false, [37578], [96755]⟩,
        ⟨102354, true, false, [], [96755]⟩
      ]⟩,
    ⟨[96049], [37579, 87991], .contexts [
        ⟨102347, false, false, [], []⟩
      ]⟩,
    ⟨[37579, 87991], [37579, 87991], .contexts []⟩,
    ⟨[96049], [37579, 87991], .contexts [
        ⟨102359, false, false, [], []⟩,
        ⟨102360, false, false, [], []⟩
      ]⟩,
    ⟨[37579, 87989], [37579, 87989], .contexts []⟩,
    ⟨[96051], [37579, 87989], .contexts [
        ⟨102349, false, false, [37580], [96051]⟩,
        ⟨13, false, false, [37580, 37578], [96051]⟩,
        ⟨95682, true, false, [37580, 37578], []⟩,
        ⟨95681, true, false, [37580, 37578], []⟩,
        ⟨102361, false, false, [37580, 37578], [15]⟩,
        ⟨47666, false, false, [37580], []⟩,
        ⟨102362, false, false, [37580, 37578], []⟩,
        ⟨102348, false, true, [], [87989]⟩
      ]⟩,
    ⟨[87989, 5], [37583, 88349], .contexts [
        ⟨102363, true, false, [37578], [5]⟩,
        ⟨95697, false, false, [37578], []⟩,
        ⟨95696, false, false, [37578], []⟩,
        ⟨102354, true, false, [], [88349]⟩
      ]⟩,
    ⟨[37589], [37581, 34995], .source 18859⟩,
    ⟨[87989, 11], [37589, 94295], .contexts [
        ⟨102363, true, false, [37578], [11]⟩,
        ⟨95701, false, false, [37578], []⟩,
        ⟨102348, true, false, [], [34995, 94295]⟩,
        ⟨102365, true, false, [], [94295]⟩
      ]⟩,
    ⟨[96051], [37579, 87989], .contexts [
        ⟨102363, false, false, [], []⟩
      ]⟩,
    ⟨[96051], [37579, 87989], .contexts [
        ⟨102367, false, false, [], []⟩,
        ⟨102362, false, false, [], []⟩
      ]⟩,
    ⟨[37579, 87987], [21511, 95423], .contexts [
        ⟨47662, true, false, [37579], []⟩,
        ⟨102368, true, false, [], [13]⟩,
        ⟨45440, true, true, [21508], [96051, 13]⟩,
        ⟨95716, false, false, [21508], [96051, 13]⟩,
        ⟨95716, false, false, [21508], [96051, 13]⟩,
        ⟨1930, true, false, [21508, 21510, 96051], [13]⟩,
        ⟨95705, false, false, [21508, 21510], [13, 3, 13, 13]⟩,
        ⟨90837, false, false, [21508, 21510], [3, 13, 13]⟩,
        ⟨95714, false, false, [21508, 21510], [3, 13, 13]⟩,
        ⟨95714, false, false, [21508, 21510], [3, 13, 13]⟩,
        ⟨90897, false, false, [21508], [13, 13]⟩,
        ⟨95715, false, false, [21508, 21510], [13, 13]⟩,
        ⟨59, false, false, [21508, 95423], []⟩,
        ⟨45440, true, false, [], [95423]⟩
      ]⟩,
    ⟨[37591], [37581, 21511], .source 18860⟩,
    ⟨[37593], [37590], .source 18861⟩,
    ⟨[95423], [37593, 87987], .contexts [
        ⟨102370, false, false, [37590], [95423]⟩,
        ⟨102348, false, false, [37590], [21511, 95423]⟩,
        ⟨95715, true, false, [37590, 37578], []⟩,
        ⟨102369, true, false, [37590, 37578], []⟩,
        ⟨102371, true, false, [], [87987]⟩
      ]⟩,
    ⟨[37591], [37592], .contexts [
        ⟨102371, true, true, [], []⟩
      ]⟩,
    ⟨[37592], [37592], .contexts []⟩,
    ⟨[87987, 3], [37591, 95421], .contexts [
        ⟨102372, true, false, [37592], [3]⟩,
        ⟨90898, false, false, [37592], []⟩,
        ⟨90811, false, false, [37592], []⟩,
        ⟨102374, true, false, [], [95421]⟩,
        ⟨102374, true, false, [], [95421]⟩,
        ⟨102373, true, false, [], [95421]⟩
      ]⟩,
    ⟨[37595], [37591, 26321], .source 18862⟩,
    ⟨[87987, 7], [37595, 91501], .contexts [
        ⟨102372, true, false, [37592], [7]⟩,
        ⟨90904, false, false, [37592], []⟩,
        ⟨90901, false, false, [37592], []⟩,
        ⟨102373, true, false, [], [26321, 91501]⟩,
        ⟨102376, true, false, [], [91501]⟩
      ]⟩,
    ⟨[37597], [37591, 33347], .source 18863⟩,
    ⟨[87987, 5], [37597, 91745], .contexts [
        ⟨102372, true, false, [37592], [5]⟩,
        ⟨90917, true, false, [37592, 33348], [5]⟩,
        ⟨28, false, false, [37592, 33348, 91745], []⟩,
        ⟨90918, true, false, [37592], [91745]⟩,
        ⟨102373, true, false, [], [33347, 91745]⟩,
        ⟨102378, true, false, [], [91745]⟩
      ]⟩,
    ⟨[37599], [37591, 33353], .source 18864⟩,
    ⟨[87987, 9], [37599, 90753], .contexts [
        ⟨102372, true, false, [37592], [9]⟩,
        ⟨90924, true, false, [37592, 33354], [9]⟩,
        ⟨46, false, false, [37592, 33354, 90753], []⟩,
        ⟨90922, false, true, [37592], [90753]⟩,
        ⟨102373, true, false, [], [33353, 90753]⟩,
        ⟨102380, true, false, [], [90753]⟩
      ]⟩,
    ⟨[37601], [37591, 33359], .source 18865⟩,
    ⟨[87987, 11], [37601, 94297], .contexts [
        ⟨102372, true, false, [37592], [11]⟩,
        ⟨90930, false, false, [37592], []⟩,
        ⟨97054, false, false, [37592], []⟩,
        ⟨102373, true, false, [], [33359, 94297]⟩,
        ⟨102382, true, false, [], [94297]⟩
      ]⟩,
    ⟨[37603], [37579, 35163], .source 18866⟩,
    ⟨[37605], [37602], .source 18867⟩,
    ⟨[37607], [37605, 34995], .source 18868⟩,
    ⟨[96133], [37607, 94291], .contexts [
        ⟨102384, false, false, [37602], [96133]⟩,
        ⟨96344, true, false, [37602, 37579], []⟩,
        ⟨102368, true, false, [37602], [1]⟩,
        ⟨95690, false, false, [37602], []⟩,
        ⟨95702, false, false, [37602], []⟩,
        ⟨95688, true, false, [37602], [94291]⟩,
        ⟨95687, true, false, [37602], [94291]⟩,
        ⟨102385, true, false, [], [34995, 94291]⟩,
        ⟨102386, true, false, [], [94291]⟩
      ]⟩,
    ⟨[96133], [37607, 94291], .contexts [
        ⟨102387, false, false, [], []⟩
      ]⟩,
    ⟨[37609], [37607, 31183], .source 18869⟩,
    ⟨[37611], [37608], .source 18870⟩,
    ⟨[37613], [37611, 35161], .source 18871⟩,
    ⟨[89081], [37613, 87993], .contexts [
        ⟨102389, false, false, [37608], [89081]⟩,
        ⟨83693, true, false, [37608, 37607], []⟩,
        ⟨102388, true, false, [37608], [15]⟩,
        ⟨96335, false, false, [37608], []⟩,
        ⟨96337, false, false, [37608], []⟩,
        ⟨96237, true, false, [37608], [87993]⟩,
        ⟨96236, true, false, [37608], [87993]⟩,
        ⟨102390, true, false, [], [35161, 87993]⟩,
        ⟨102391, true, false, [], [87993]⟩
      ]⟩,
    ⟨[37615], [37612], .source 18872⟩,
    ⟨[37612], [37612], .contexts []⟩,
    ⟨[37615], [37612], .contexts [
        ⟨102393, false, false, [], []⟩,
        ⟨102394, false, false, [], []⟩,
        ⟨102394, false, false, [], []⟩
      ]⟩,
    ⟨[37617], [37615, 23609], .source 18873⟩,
    ⟨[37619], [37615, 36737], .source 18874⟩,
    ⟨[87993, 7], [37619, 92333], .contexts [
        ⟨102392, true, false, [37612], [7]⟩,
        ⟨100713, false, false, [37612], []⟩,
        ⟨100763, false, false, [37612], []⟩,
        ⟨102393, true, false, [], [36737, 92333]⟩,
        ⟨102397, true, false, [], [92333]⟩
      ]⟩,
    ⟨[89081], [37613, 87993], .contexts [
        ⟨102392, false, false, [], []⟩
      ]⟩]

/-- Literal contextual derivation data in chronological chunk 24. -/
def y322TCIndexRawChunk24 (i : Fin 4096) : Y322RawContextCertificate :=
  if i.val < 2048 then
    if i.val < 1024 then
      if i.val < 512 then
        if i.val < 256 then
          if i.val < 128 then
            if i.val < 64 then
              y322TCIndexRaw1536 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1537 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 192 then
              y322TCIndexRaw1538 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1539 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 384 then
            if i.val < 320 then
              y322TCIndexRaw1540 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1541 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 448 then
              y322TCIndexRaw1542 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1543 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 768 then
          if i.val < 640 then
            if i.val < 576 then
              y322TCIndexRaw1544 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1545 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 704 then
              y322TCIndexRaw1546 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1547 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 896 then
            if i.val < 832 then
              y322TCIndexRaw1548 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1549 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 960 then
              y322TCIndexRaw1550 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1551 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 1536 then
        if i.val < 1280 then
          if i.val < 1152 then
            if i.val < 1088 then
              y322TCIndexRaw1552 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1553 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1216 then
              y322TCIndexRaw1554 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1555 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1408 then
            if i.val < 1344 then
              y322TCIndexRaw1556 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1557 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1472 then
              y322TCIndexRaw1558 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1559 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 1792 then
          if i.val < 1664 then
            if i.val < 1600 then
              y322TCIndexRaw1560 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1561 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1728 then
              y322TCIndexRaw1562 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1563 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1920 then
            if i.val < 1856 then
              y322TCIndexRaw1564 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1565 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1984 then
              y322TCIndexRaw1566 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1567 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  else
    if i.val < 3072 then
      if i.val < 2560 then
        if i.val < 2304 then
          if i.val < 2176 then
            if i.val < 2112 then
              y322TCIndexRaw1568 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1569 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2240 then
              y322TCIndexRaw1570 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1571 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2432 then
            if i.val < 2368 then
              y322TCIndexRaw1572 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1573 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2496 then
              y322TCIndexRaw1574 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1575 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 2816 then
          if i.val < 2688 then
            if i.val < 2624 then
              y322TCIndexRaw1576 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1577 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2752 then
              y322TCIndexRaw1578 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1579 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2944 then
            if i.val < 2880 then
              y322TCIndexRaw1580 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1581 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3008 then
              y322TCIndexRaw1582 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1583 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 3584 then
        if i.val < 3328 then
          if i.val < 3200 then
            if i.val < 3136 then
              y322TCIndexRaw1584 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1585 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3264 then
              y322TCIndexRaw1586 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1587 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3456 then
            if i.val < 3392 then
              y322TCIndexRaw1588 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1589 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3520 then
              y322TCIndexRaw1590 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1591 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 3840 then
          if i.val < 3712 then
            if i.val < 3648 then
              y322TCIndexRaw1592 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1593 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3776 then
              y322TCIndexRaw1594 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1595 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3968 then
            if i.val < 3904 then
              y322TCIndexRaw1596 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1597 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 4032 then
              y322TCIndexRaw1598 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw1599 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
