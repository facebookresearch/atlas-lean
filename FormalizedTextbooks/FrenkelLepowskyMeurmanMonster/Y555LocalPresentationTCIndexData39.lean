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

/-- Exact literal claimed equations and contextual derivations, block 2496. -/
def y322TCIndexRaw2496 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85003, 15], [38677, 83089], .contexts [
        ⟨103657, false, false, [], []⟩
      ]⟩,
    ⟨[85009, 1], [85011], .contexts [
        ⟨29711, false, false, [], []⟩,
        ⟨29946, false, false, [], []⟩
      ]⟩,
    ⟨[85009, 3], [45161, 62791, 84655], .contexts [
        ⟨110209, false, false, [], []⟩,
        ⟨130653, false, false, [45161], []⟩
      ]⟩,
    ⟨[85009, 5], [51909, 65395, 90795], .contexts [
        ⟨117803, false, false, [], []⟩,
        ⟨133647, false, false, [51909], []⟩
      ]⟩,
    ⟨[85009, 7], [45123, 57729, 88513], .contexts [
        ⟨110164, false, false, [], []⟩,
        ⟨124631, false, false, [45123], []⟩
      ]⟩,
    ⟨[85009, 9], [59751, 95287], .contexts [
        ⟨126986, true, false, [59748], [9]⟩,
        ⟨46, false, false, [59748, 95287], []⟩,
        ⟨126987, true, false, [], [95287]⟩
      ]⟩,
    ⟨[85009, 11], [46511, 91635], .contexts [
        ⟨111847, true, false, [46508], [11]⟩,
        ⟨53, false, false, [46508, 91635], []⟩,
        ⟨111848, true, false, [], [91635]⟩
      ]⟩,
    ⟨[85009, 13], [74579, 97023], .contexts [
        ⟨145398, true, false, [74576], [13]⟩,
        ⟨59, false, false, [74576, 97023], []⟩,
        ⟨145399, true, false, [], [97023]⟩
      ]⟩,
    ⟨[85009, 15], [38677, 83083], .contexts [
        ⟨29709, false, false, [], []⟩,
        ⟨103683, false, false, [], []⟩
      ]⟩,
    ⟨[85011, 1], [85009], .contexts [
        ⟨29713, false, false, [], []⟩,
        ⟨29948, false, false, [], []⟩
      ]⟩,
    ⟨[85011, 3], [85013], .contexts [
        ⟨29715, false, false, [], []⟩,
        ⟨29945, false, false, [], []⟩
      ]⟩,
    ⟨[85011, 5], [51723, 65395, 90797], .contexts [
        ⟨117568, false, false, [], []⟩,
        ⟨133656, false, false, [51723], []⟩
      ]⟩,
    ⟨[85011, 7], [53433, 92567], .contexts [
        ⟨119607, false, false, [], []⟩
      ]⟩,
    ⟨[85011, 9], [51801, 85273], .contexts [
        ⟨117642, false, false, [], []⟩,
        ⟨125866, false, false, [], []⟩
      ]⟩,
    ⟨[85011, 11], [51767, 86135], .contexts [
        ⟨117608, false, false, [], []⟩,
        ⟨125861, false, false, [], []⟩
      ]⟩,
    ⟨[85011, 13], [51821, 85011], .contexts [
        ⟨117657, false, false, [51816], []⟩,
        ⟨110184, false, false, [51816, 38695], []⟩,
        ⟨117658, true, false, [], [38695, 85011]⟩,
        ⟨117659, true, false, [], [85011]⟩
      ]⟩,
    ⟨[85011, 15], [38677, 83081], .contexts [
        ⟨110185, true, false, [38694], [15]⟩,
        ⟨1, false, false, [38694, 83081], []⟩,
        ⟨103682, true, false, [], [83081]⟩
      ]⟩,
    ⟨[85013, 1], [51723, 51731, 85017], .contexts [
        ⟨117553, false, false, [], []⟩,
        ⟨117733, false, false, [51723], []⟩
      ]⟩,
    ⟨[85013, 3], [85011], .contexts [
        ⟨29717, false, false, [], []⟩,
        ⟨29946, false, false, [], []⟩
      ]⟩,
    ⟨[85015], [51727, 85013], .contexts [
        ⟨117558, false, false, [], []⟩
      ]⟩,
    ⟨[85013, 5], [51727, 85013], .contexts [
        ⟨29719, false, false, [], []⟩,
        ⟨159763, false, false, [], []⟩
      ]⟩,
    ⟨[85013, 7], [51873, 57805, 83849], .contexts [
        ⟨117747, true, false, [51870], [7]⟩,
        ⟨38, false, false, [51870, 86405], []⟩,
        ⟨117748, true, false, [], [86405]⟩,
        ⟨124710, false, false, [51873], []⟩
      ]⟩,
    ⟨[85013, 9], [74497, 97015], .contexts [
        ⟨145266, true, false, [74494], [9]⟩,
        ⟨46, false, false, [74494, 97015], []⟩,
        ⟨145267, true, false, [], [97015]⟩
      ]⟩,
    ⟨[85013, 11], [51751, 51943, 85023], .contexts [
        ⟨117587, false, false, [], []⟩,
        ⟨117857, false, false, [51751], []⟩
      ]⟩,
    ⟨[85013, 13], [51747, 85013], .contexts [
        ⟨117583, false, false, [], []⟩
      ]⟩,
    ⟨[85013, 15], [51719, 82955], .contexts [
        ⟨117546, false, false, [], []⟩
      ]⟩,
    ⟨[85017, 1], [51727, 85013], .contexts [
        ⟨29724, false, false, [], []⟩,
        ⟨159763, false, false, [], []⟩
      ]⟩,
    ⟨[85017, 3], [52025, 83307], .contexts [
        ⟨117925, false, false, [], []⟩,
        ⟨143592, false, false, [], []⟩
      ]⟩,
    ⟨[85017, 5], [51931, 85017], .contexts [
        ⟨117824, false, false, [], []⟩,
        ⟨143596, false, false, [], []⟩
      ]⟩,
    ⟨[85017, 7], [55641, 57805, 83851], .contexts [
        ⟨122184, false, false, [], []⟩,
        ⟨124725, false, false, [55641], []⟩
      ]⟩,
    ⟨[85019], [51957, 85017], .contexts [
        ⟨117918, false, false, [], []⟩
      ]⟩,
    ⟨[85017, 9], [51957, 85017], .contexts [
        ⟨29726, false, false, [], []⟩,
        ⟨159774, false, false, [], []⟩
      ]⟩,
    ⟨[85017, 11], [51867, 51943, 85021], .contexts [
        ⟨117743, false, false, [], []⟩,
        ⟨117844, false, false, [51867], []⟩
      ]⟩,
    ⟨[85017, 13], [96923], .contexts [
        ⟨143582, false, false, [], []⟩,
        ⟨143583, false, false, [], []⟩
      ]⟩,
    ⟨[85017, 15], [51733, 82957], .contexts [
        ⟨117565, false, false, [], []⟩,
        ⟨143611, false, false, [], []⟩
      ]⟩,
    ⟨[85021, 1], [85023], .contexts [
        ⟨29733, false, false, [], []⟩,
        ⟨29939, false, false, [], []⟩
      ]⟩,
    ⟨[85021, 3], [51953, 86635], .contexts [
        ⟨117850, false, false, [], []⟩,
        ⟨117914, false, false, [], []⟩
      ]⟩,
    ⟨[85021, 5], [51949, 85021], .contexts [
        ⟨117839, true, false, [51942], [5]⟩,
        ⟨43636, false, false, [51942], []⟩,
        ⟨117845, false, false, [51942, 20923], []⟩,
        ⟨117840, true, false, [], [20923, 51943, 85021]⟩,
        ⟨117846, true, false, [], [51943, 85021]⟩,
        ⟨117847, true, false, [], [85021]⟩
      ]⟩,
    ⟨[85021, 7], [58159, 83855], .contexts [
        ⟨125063, false, false, [], []⟩
      ]⟩,
    ⟨[85021, 9], [51951, 88999], .contexts [
        ⟨117839, true, false, [51942], [9]⟩,
        ⟨91479, false, false, [51942], []⟩,
        ⟨117722, false, false, [51942], []⟩,
        ⟨117840, true, false, [], [33589, 88999]⟩,
        ⟨117848, true, false, [], [88999]⟩
      ]⟩,
    ⟨[85021, 11], [51957, 85017], .contexts [
        ⟨29731, false, false, [], []⟩,
        ⟨159774, false, false, [], []⟩
      ]⟩,
    ⟨[85021, 13], [51955, 88225], .contexts [
        ⟨117852, false, false, [], []⟩
      ]⟩,
    ⟨[85021, 15], [51945, 51983, 85029], .contexts [
        ⟨117839, true, false, [51942], [15]⟩,
        ⟨35525, false, false, [51942], []⟩,
        ⟨35771, false, false, [51942], []⟩,
        ⟨117843, true, false, [], [86129]⟩,
        ⟨117882, false, false, [51945], []⟩
      ]⟩,
    ⟨[85023, 1], [85021], .contexts [
        ⟨29735, false, false, [], []⟩,
        ⟨29940, false, false, [], []⟩
      ]⟩,
    ⟨[85023, 3], [51945, 86135], .contexts [
        ⟨117856, false, false, [], []⟩
      ]⟩,
    ⟨[85023, 5], [51961, 85023], .contexts [
        ⟨117861, false, false, [], []⟩
      ]⟩,
    ⟨[85023, 7], [51969, 57875, 83857], .contexts [
        ⟨117855, true, false, [51942], [7]⟩,
        ⟨108961, false, false, [51942], []⟩,
        ⟨117744, false, false, [51942], []⟩,
        ⟨117840, true, false, [], [44181, 50509, 86403]⟩,
        ⟨117865, true, false, [], [50509, 86403]⟩,
        ⟨117866, true, false, [], [86403]⟩,
        ⟨124791, false, false, [51969], []⟩
      ]⟩,
    ⟨[85023, 9], [51965, 61303, 84533], .contexts [
        ⟨117855, true, false, [51942], [9]⟩,
        ⟨108959, false, false, [51942], []⟩,
        ⟨117724, false, false, [51942], []⟩,
        ⟨117840, true, false, [], [44179, 91129]⟩,
        ⟨117864, true, false, [], [91129]⟩,
        ⟨128826, false, false, [51965], []⟩
      ]⟩,
    ⟨[85023, 11], [51971, 85013], .contexts [
        ⟨117855, true, false, [51942], [11]⟩,
        ⟨117589, false, false, [51942], []⟩,
        ⟨117730, false, false, [51942], []⟩,
        ⟨117840, true, false, [], [51753, 85013]⟩,
        ⟨117867, true, false, [], [85013]⟩
      ]⟩,
    ⟨[85023, 13], [51975, 85023], .contexts [
        ⟨29737, false, false, [], []⟩,
        ⟨117870, false, false, [], []⟩
      ]⟩,
    ⟨[85023, 15], [51963, 82953], .contexts [
        ⟨117863, false, false, [], []⟩
      ]⟩,
    ⟨[85029, 1], [51977, 82953], .contexts [
        ⟨29745, false, false, [], []⟩,
        ⟨117873, false, false, [], []⟩
      ]⟩,
    ⟨[85029, 3], [85031], .contexts [
        ⟨29747, false, false, [], []⟩,
        ⟨29935, false, false, [], []⟩
      ]⟩,
    ⟨[85029, 5], [51989, 85029], .contexts [
        ⟨117876, true, false, [51982], [5]⟩,
        ⟨43580, false, false, [51982], []⟩,
        ⟨117883, false, false, [51982, 20925], []⟩,
        ⟨117877, true, false, [], [20925, 51983, 85029]⟩,
        ⟨117884, true, false, [], [51983, 85029]⟩,
        ⟨117885, true, false, [], [85029]⟩
      ]⟩,
    ⟨[85029, 7], [51995, 57919, 83863], .contexts [
        ⟨117876, true, false, [51982], [7]⟩,
        ⟨101125, true, false, [51982, 36898], [7]⟩,
        ⟨38, false, false, [51982, 36898, 85289], []⟩,
        ⟨101126, true, false, [51982], [85289]⟩,
        ⟨117877, true, false, [], [36901, 85289]⟩,
        ⟨117889, true, false, [], [85289]⟩,
        ⟨124835, false, false, [51995], []⟩
      ]⟩,
    ⟨[85029, 9], [51993, 53801, 88371], .contexts [
        ⟨117888, false, false, [], []⟩,
        ⟨119949, false, false, [51993], []⟩
      ]⟩,
    ⟨[85029, 11], [51991, 82957], .contexts [
        ⟨117876, true, false, [51982], [11]⟩,
        ⟨47365, false, false, [51982], []⟩,
        ⟨47374, false, false, [51982], []⟩,
        ⟨117877, true, false, [], [22007, 82957]⟩,
        ⟨117886, true, false, [], [82957]⟩
      ]⟩,
    ⟨[85029, 13], [51981, 86127], .contexts [
        ⟨117876, true, false, [51982], [13]⟩,
        ⟨35521, false, false, [51982], []⟩,
        ⟨35772, false, false, [51982], []⟩,
        ⟨117878, true, false, [], [86127]⟩,
        ⟨117879, true, false, [], [86127]⟩
      ]⟩,
    ⟨[85029, 15], [51985, 85021], .contexts [
        ⟨117881, false, false, [], []⟩
      ]⟩,
    ⟨[85031, 1], [72163, 96829], .contexts [
        ⟨141662, true, false, [72160], [1]⟩,
        ⟨8, false, false, [72160, 96829], []⟩,
        ⟨141663, true, false, [], [96829]⟩
      ]⟩,
    ⟨[85031, 3], [85029], .contexts [
        ⟨29749, false, false, [], []⟩,
        ⟨29937, false, false, [], []⟩
      ]⟩,
    ⟨[85031, 5], [52005, 83691], .contexts [
        ⟨29751, false, false, [], []⟩,
        ⟨117904, false, false, [], []⟩
      ]⟩,
    ⟨[85031, 7], [52011, 57939, 83865], .contexts [
        ⟨117892, true, false, [51998], [7]⟩,
        ⟨101745, false, false, [51998], []⟩,
        ⟨117893, true, false, [], [37209, 84991]⟩,
        ⟨117901, true, false, [], [84991]⟩,
        ⟨124853, false, false, [52011], []⟩
      ]⟩,
    ⟨[85031, 9], [52001, 93455], .contexts [
        ⟨117892, true, false, [51998], [9]⟩,
        ⟨99152, false, false, [51998], []⟩,
        ⟨116773, false, false, [51998], []⟩,
        ⟨117894, true, false, [], [51023, 93455]⟩,
        ⟨117895, true, false, [], [93455]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2497. -/
def y322TCIndexRaw2497 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85031, 11], [52003, 83309], .contexts [
        ⟨117892, true, false, [51998], [11]⟩,
        ⟨99154, false, false, [51998], []⟩,
        ⟨103943, false, false, [51998], []⟩,
        ⟨117894, true, false, [], [38897, 83309]⟩,
        ⟨117896, true, false, [], [83309]⟩
      ]⟩,
    ⟨[85031, 13], [52007, 84127], .contexts [
        ⟨117892, true, false, [51998], [13]⟩,
        ⟨101606, false, false, [51998], []⟩,
        ⟨113664, false, false, [51998, 37079], []⟩,
        ⟨117898, true, false, [], [48323, 84127]⟩,
        ⟨117897, true, false, [], [48323, 84127]⟩,
        ⟨117899, true, false, [], [84127]⟩
      ]⟩,
    ⟨[85031, 15], [52009, 86635], .contexts [
        ⟨117892, true, false, [51998], [15]⟩,
        ⟨101611, true, false, [51998, 37136], [15]⟩,
        ⟨1, false, false, [51998, 37136, 86635], []⟩,
        ⟨101609, false, true, [51998], [86635]⟩,
        ⟨117893, true, false, [], [37135, 86635]⟩,
        ⟨117900, true, false, [], [86635]⟩
      ]⟩,
    ⟨[85039, 1], [85041], .contexts [
        ⟨29764, false, false, [], []⟩,
        ⟨29930, false, false, [], []⟩
      ]⟩,
    ⟨[85039, 3], [68791, 89041], .contexts [
        ⟨137387, false, false, [], []⟩
      ]⟩,
    ⟨[85039, 5], [58997, 83881], .contexts [
        ⟨126089, false, false, [], []⟩
      ]⟩,
    ⟨[85039, 7], [54745, 87233], .contexts [
        ⟨121113, false, false, [], []⟩
      ]⟩,
    ⟨[85039, 9], [73715, 96949], .contexts [
        ⟨144058, false, false, [], []⟩
      ]⟩,
    ⟨[85039, 11], [52013, 83449], .contexts [
        ⟨29762, false, false, [], []⟩,
        ⟨117911, false, false, [], []⟩
      ]⟩,
    ⟨[85039, 13], [57581, 85441], .contexts [
        ⟨124467, true, false, [57578], [13]⟩,
        ⟨59, false, false, [57578, 85441], []⟩,
        ⟨124468, true, false, [], [85441]⟩
      ]⟩,
    ⟨[85039, 15], [52151, 53041, 86821], .contexts [
        ⟨118079, true, false, [52148], [15]⟩,
        ⟨1, false, false, [52148, 90313], []⟩,
        ⟨118080, true, false, [], [90313]⟩,
        ⟨119163, false, false, [52151], []⟩
      ]⟩,
    ⟨[85041, 1], [85039], .contexts [
        ⟨29766, false, false, [], []⟩,
        ⟨29932, false, false, [], []⟩
      ]⟩,
    ⟨[85041, 3], [69233, 95567], .contexts [
        ⟨137844, false, false, [], []⟩
      ]⟩,
    ⟨[85041, 5], [59079, 83879], .contexts [
        ⟨126198, true, false, [59076], [5]⟩,
        ⟨28, false, false, [59076, 83879], []⟩,
        ⟨126199, true, false, [], [83879]⟩
      ]⟩,
    ⟨[85041, 7], [65691, 89025], .contexts [
        ⟨133964, false, false, [], []⟩
      ]⟩,
    ⟨[85041, 9], [59003, 59115, 85041], .contexts [
        ⟨126100, false, false, [], []⟩,
        ⟨126250, false, false, [59003], []⟩
      ]⟩,
    ⟨[85041, 11], [52013, 83447], .contexts [
        ⟨126057, false, false, [], []⟩
      ]⟩,
    ⟨[85041, 13], [85043], .contexts [
        ⟨29768, false, false, [], []⟩,
        ⟨29929, false, false, [], []⟩
      ]⟩,
    ⟨[85041, 15], [59065, 88501], .contexts [
        ⟨126163, true, false, [59062], [15]⟩,
        ⟨1, false, false, [59062, 88501], []⟩,
        ⟨126164, true, false, [], [88501]⟩
      ]⟩,
    ⟨[85043, 1], [60105, 85445], .contexts [
        ⟨127401, false, false, [], []⟩
      ]⟩,
    ⟨[85043, 3], [60107, 83033], .contexts [
        ⟨127404, false, false, [], []⟩
      ]⟩,
    ⟨[85043, 5], [60277, 93903], .contexts [
        ⟨127569, false, false, [], []⟩,
        ⟨133966, false, false, [], []⟩
      ]⟩,
    ⟨[85043, 7], [60235, 86647], .contexts [
        ⟨127530, true, false, [60232], [7]⟩,
        ⟨38, false, false, [60232, 86647], []⟩,
        ⟨127531, true, false, [], [86647]⟩
      ]⟩,
    ⟨[85043, 9], [60111, 85043], .contexts [
        ⟨127397, true, false, [60102], [9]⟩,
        ⟨66569, true, false, [60102], [9]⟩,
        ⟨76412, true, false, [60102, 29300], [3, 9]⟩,
        ⟨76412, true, false, [60102, 29300], [3, 9]⟩,
        ⟨76404, true, false, [60102, 29300], [3, 9]⟩,
        ⟨76402, true, false, [60102, 29300], [3, 9]⟩,
        ⟨479, false, false, [60102, 29300, 91591], []⟩,
        ⟨70327, false, false, [60102, 29300], []⟩,
        ⟨70326, false, false, [60102, 29300], []⟩,
        ⟨70329, false, false, [60102, 29300], []⟩,
        ⟨76378, true, false, [60102], [91589]⟩,
        ⟨127405, false, false, [60102, 29299], []⟩,
        ⟨127398, true, false, [], [29299, 60103, 85043]⟩,
        ⟨127406, true, false, [], [60103, 85043]⟩,
        ⟨127407, true, false, [], [85043]⟩
      ]⟩,
    ⟨[85043, 11], [60861, 61931, 84561], .contexts [
        ⟨128256, false, false, [], []⟩,
        ⟨129596, false, false, [60861], []⟩
      ]⟩,
    ⟨[85043, 13], [85041], .contexts [
        ⟨29770, false, false, [], []⟩,
        ⟨29930, false, false, [], []⟩
      ]⟩,
    ⟨[85043, 15], [85045], .contexts [
        ⟨29772, false, false, [], []⟩,
        ⟨29927, false, false, [], []⟩
      ]⟩,
    ⟨[85045, 1], [85047], .contexts [
        ⟨29776, false, false, [], []⟩,
        ⟨29926, false, false, [], []⟩
      ]⟩,
    ⟨[85045, 3], [60091, 83031], .contexts [
        ⟨127383, false, false, [], []⟩,
        ⟨128241, false, false, [], []⟩
      ]⟩,
    ⟨[85045, 5], [65643, 89025], .contexts [
        ⟨133909, false, false, [], []⟩,
        ⟨133913, false, false, [], []⟩
      ]⟩,
    ⟨[85045, 7], [60099, 83875], .contexts [
        ⟨127393, false, false, [], []⟩,
        ⟨128243, false, false, [], []⟩
      ]⟩,
    ⟨[85045, 9], [60095, 85045], .contexts [
        ⟨127388, false, false, [], []⟩,
        ⟨133922, false, false, [], []⟩
      ]⟩,
    ⟨[85045, 11], [60097, 87241], .contexts [
        ⟨127391, false, false, [], []⟩,
        ⟨128252, false, false, [], []⟩
      ]⟩,
    ⟨[85045, 13], [59087, 63727, 85771], .contexts [
        ⟨126207, false, false, [], []⟩,
        ⟨131819, false, false, [59087], []⟩
      ]⟩,
    ⟨[85045, 15], [85043], .contexts [
        ⟨29774, false, false, [], []⟩,
        ⟨29929, false, false, [], []⟩
      ]⟩,
    ⟨[85047, 1], [85045], .contexts [
        ⟨29778, false, false, [], []⟩,
        ⟨29927, false, false, [], []⟩
      ]⟩,
    ⟨[85049], [60623, 83437], .contexts [
        ⟨129107, false, false, [], []⟩
      ]⟩,
    ⟨[85047, 3], [60623, 83437], .contexts [
        ⟨29780, false, false, [], []⟩,
        ⟨159844, false, false, [], []⟩
      ]⟩,
    ⟨[85047, 5], [60115, 87233], .contexts [
        ⟨127412, false, false, [], []⟩,
        ⟨133901, false, false, [], []⟩
      ]⟩,
    ⟨[85047, 7], [60119, 83873], .contexts [
        ⟨127408, true, false, [60088], [7]⟩,
        ⟨126852, true, false, [60088, 59610], [7]⟩,
        ⟨38, false, false, [60088, 59610, 83873], []⟩,
        ⟨126853, true, false, [60088], [83873]⟩,
        ⟨127378, true, false, [], [59613, 83873]⟩,
        ⟨127414, true, false, [], [83873]⟩
      ]⟩,
    ⟨[85047, 9], [60117, 92911], .contexts [
        ⟨127408, true, false, [60088], [9]⟩,
        ⟨120348, true, false, [60088, 54112], [9]⟩,
        ⟨102557, false, false, [60088, 54112], []⟩,
        ⟨102554, false, false, [60088, 54112], []⟩,
        ⟨120342, true, false, [60088], [37317, 92911]⟩,
        ⟨120350, true, false, [60088], [92911]⟩,
        ⟨127378, true, false, [], [54119, 92911]⟩,
        ⟨127413, true, false, [], [92911]⟩
      ]⟩,
    ⟨[85047, 11], [60097, 87243], .contexts [
        ⟨127408, true, false, [60088], [11]⟩,
        ⟨120348, true, false, [60088, 54112], [11]⟩,
        ⟨103131, false, false, [60088, 54112], []⟩,
        ⟨103127, false, false, [60088, 54112], []⟩,
        ⟨120344, true, false, [60088], [87243]⟩,
        ⟨127390, true, false, [], [87243]⟩
      ]⟩,
    ⟨[85047, 13], [60113, 85899], .contexts [
        ⟨127408, true, false, [60088], [13]⟩,
        ⟨70340, false, false, [60088], []⟩,
        ⟨120357, false, false, [60088, 27399], []⟩,
        ⟨127395, true, false, [], [54125, 85899]⟩,
        ⟨127394, true, false, [], [54125, 85899]⟩,
        ⟨127410, true, false, [], [85899]⟩
      ]⟩,
    ⟨[85047, 15], [60087, 85445], .contexts [
        ⟨127409, false, false, [], []⟩,
        ⟨133972, false, false, [], []⟩
      ]⟩,
    ⟨[85051, 1], [85053], .contexts [
        ⟨29787, false, false, [], []⟩,
        ⟨29921, false, false, [], []⟩
      ]⟩,
    ⟨[85051, 3], [61571, 88307], .contexts [
        ⟨129117, false, false, [], []⟩
      ]⟩,
    ⟨[85051, 5], [60623, 83437], .contexts [
        ⟨29785, false, false, [], []⟩,
        ⟨159844, false, false, [], []⟩
      ]⟩,
    ⟨[85051, 7], [64751, 89391], .contexts [
        ⟨132931, false, false, [], []⟩
      ]⟩,
    ⟨[85051, 9], [64749, 91775], .contexts [
        ⟨132929, false, false, [], []⟩,
        ⟨136927, false, false, [], []⟩
      ]⟩,
    ⟨[85051, 11], [64747, 83037], .contexts [
        ⟨132921, true, false, [64744], [11]⟩,
        ⟨34732, false, false, [64744], []⟩,
        ⟨132924, false, false, [64744], []⟩,
        ⟨132926, true, false, [], [62555, 83037]⟩,
        ⟨132927, true, false, [], [83037]⟩
      ]⟩,
    ⟨[85051, 13], [60625, 60645, 85639], .contexts [
        ⟨128003, false, false, [], []⟩,
        ⟨128038, false, false, [60625], []⟩
      ]⟩,
    ⟨[85051, 15], [61657, 83041], .contexts [
        ⟨129242, false, false, [], []⟩
      ]⟩,
    ⟨[85053, 1], [85051], .contexts [
        ⟨29789, false, false, [], []⟩,
        ⟨29923, false, false, [], []⟩
      ]⟩,
    ⟨[85053, 3], [67081, 84563], .contexts [
        ⟨135536, true, false, [67078], [3]⟩,
        ⟨20, false, false, [67078, 84563], []⟩,
        ⟨135537, true, false, [], [84563]⟩
      ]⟩,
    ⟨[85053, 5], [60623, 83435], .contexts [
        ⟨134647, true, false, [60620], [5]⟩,
        ⟨28, false, false, [60620, 83435], []⟩,
        ⟨127991, true, false, [], [83435]⟩
      ]⟩,
    ⟨[85053, 7], [65007, 89389], .contexts [
        ⟨133206, false, false, [], []⟩
      ]⟩,
    ⟨[85053, 9], [85055], .contexts [
        ⟨29791, false, false, [], []⟩,
        ⟨29919, false, false, [], []⟩
      ]⟩,
    ⟨[85053, 11], [66305, 83729], .contexts [
        ⟨134664, false, false, [], []⟩
      ]⟩,
    ⟨[96509], [64603, 64757, 86019], .contexts [
        ⟨132890, false, false, [], []⟩,
        ⟨135164, false, false, [], []⟩
      ]⟩,
    ⟨[85053, 13], [61041, 64603, 64757, 86019], .contexts [
        ⟨128469, false, false, [], []⟩,
        ⟨159866, false, false, [61041], []⟩
      ]⟩,
    ⟨[85053, 15], [65251, 83039], .contexts [
        ⟨133478, true, false, [65248], [15]⟩,
        ⟨1, false, false, [65248, 83039], []⟩,
        ⟨133479, true, false, [], [83039]⟩
      ]⟩,
    ⟨[85055, 1], [67031, 94005], .contexts [
        ⟨135464, false, false, [], []⟩,
        ⟨135526, false, false, [], []⟩
      ]⟩,
    ⟨[85055, 3], [63315, 84565], .contexts [
        ⟨131268, true, false, [63310], [3]⟩,
        ⟨80211, false, false, [63310], []⟩,
        ⟨129539, false, false, [63310], []⟩,
        ⟨131272, true, false, [], [61243, 84565]⟩,
        ⟨131273, true, false, [], [84565]⟩
      ]⟩,
    ⟨[85055, 5], [63313, 93649], .contexts [
        ⟨131268, true, false, [63310], [5]⟩,
        ⟨80213, false, false, [63310], []⟩,
        ⟨80286, false, false, [63310], []⟩,
        ⟨131271, true, false, [], [93649]⟩,
        ⟨131272, true, false, [], [93649]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2498. -/
def y322TCIndexRaw2498 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85055, 7], [63321, 94335], .contexts [
        ⟨131268, true, false, [63310], [7]⟩,
        ⟨126352, true, false, [63310, 59202], [7]⟩,
        ⟨38, false, false, [63310, 59202, 94335], []⟩,
        ⟨126350, false, true, [63310], [94335]⟩,
        ⟨131269, true, false, [], [59201, 94335]⟩,
        ⟨131278, true, false, [], [94335]⟩
      ]⟩,
    ⟨[85055, 9], [85053], .contexts [
        ⟨29793, false, false, [], []⟩,
        ⟨29921, false, false, [], []⟩
      ]⟩,
    ⟨[85055, 11], [85057], .contexts [
        ⟨29795, false, false, [], []⟩,
        ⟨29918, false, false, [], []⟩
      ]⟩,
    ⟨[85055, 13], [63319, 88353], .contexts [
        ⟨131277, false, false, [], []⟩,
        ⟨131312, false, false, [], []⟩
      ]⟩,
    ⟨[85055, 15], [63317, 89815], .contexts [
        ⟨131275, false, false, [], []⟩
      ]⟩,
    ⟨[85057, 1], [85059], .contexts [
        ⟨29799, false, false, [], []⟩,
        ⟨29915, false, false, [], []⟩
      ]⟩,
    ⟨[85057, 3], [67071, 84567], .contexts [
        ⟨135517, true, false, [67072], [3]⟩,
        ⟨20, false, false, [67072, 84567], []⟩,
        ⟨135515, false, true, [], [84567]⟩,
        ⟨135514, false, false, [], []⟩
      ]⟩,
    ⟨[85057, 5], [63557, 92889], .contexts [
        ⟨131588, false, false, [], []⟩,
        ⟨136532, false, false, [], []⟩
      ]⟩,
    ⟨[85057, 7], [63331, 85155], .contexts [
        ⟨131298, false, false, [], []⟩,
        ⟨136545, false, false, [], []⟩
      ]⟩,
    ⟨[85057, 9], [63327, 89825], .contexts [
        ⟨131294, false, false, [], []⟩,
        ⟨136529, false, false, [], []⟩
      ]⟩,
    ⟨[85057, 11], [85055], .contexts [
        ⟨29797, false, false, [], []⟩,
        ⟨29919, false, false, [], []⟩
      ]⟩,
    ⟨[85057, 13], [63337, 93867], .contexts [
        ⟨131303, false, false, [], []⟩,
        ⟨131316, false, false, [], []⟩
      ]⟩,
    ⟨[85057, 15], [63335, 69295, 88257], .contexts [
        ⟨131288, true, false, [63324], [15]⟩,
        ⟨102601, true, false, [63324, 37854], [15]⟩,
        ⟨1, false, false, [63324, 37854, 96273], []⟩,
        ⟨102602, true, false, [63324], [96273]⟩,
        ⟨130424, false, false, [63324, 37857], []⟩,
        ⟨131300, true, false, [], [62591, 93871]⟩,
        ⟨131301, true, false, [], [93871]⟩,
        ⟨137929, false, false, [63335], []⟩
      ]⟩,
    ⟨[85059, 1], [85057], .contexts [
        ⟨29801, false, false, [], []⟩,
        ⟨29918, false, false, [], []⟩
      ]⟩,
    ⟨[85059, 3], [63343, 94589], .contexts [
        ⟨131311, false, false, [], []⟩,
        ⟨135508, false, false, [], []⟩
      ]⟩,
    ⟨[85059, 5], [63339, 92891], .contexts [
        ⟨131306, true, false, [63324], [5]⟩,
        ⟨75861, false, false, [63324], []⟩,
        ⟨131011, false, false, [63324], []⟩,
        ⟨131292, true, false, [], [62623, 92891]⟩,
        ⟨131307, true, false, [], [92891]⟩
      ]⟩,
    ⟨[85059, 7], [63331, 85153], .contexts [
        ⟨131308, false, false, [], []⟩,
        ⟨136935, false, false, [], []⟩
      ]⟩,
    ⟨[85059, 9], [75309, 97175], .contexts [
        ⟨146627, true, false, [75306], [9]⟩,
        ⟨46, false, false, [75306, 97175], []⟩,
        ⟨146628, true, false, [], [97175]⟩
      ]⟩,
    ⟨[85059, 11], [67031, 94005], .contexts [
        ⟨135532, false, false, [], []⟩,
        ⟨135526, false, false, [], []⟩
      ]⟩,
    ⟨[85059, 13], [85061], .contexts [
        ⟨29803, false, false, [], []⟩,
        ⟨29914, false, false, [], []⟩
      ]⟩,
    ⟨[85059, 15], [63341, 69317, 88255], .contexts [
        ⟨131306, true, false, [63324], [15]⟩,
        ⟨102848, false, false, [63324], []⟩,
        ⟨130320, false, false, [63324, 37857], []⟩,
        ⟨131300, true, false, [], [62513, 91767]⟩,
        ⟨131309, true, false, [], [91767]⟩,
        ⟨137939, false, false, [63341], []⟩
      ]⟩,
    ⟨[85061, 1], [19307, 85065], .contexts [
        ⟨37849, false, false, [], []⟩,
        ⟨37839, false, false, [], []⟩
      ]⟩,
    ⟨[85061, 3], [67075, 90983], .contexts [
        ⟨135524, true, false, [67076], [3]⟩,
        ⟨20, false, false, [67076, 90983], []⟩,
        ⟨135522, false, true, [], [90983]⟩
      ]⟩,
    ⟨[85061, 5], [67937, 91793], .contexts [
        ⟨136564, false, false, [], []⟩
      ]⟩,
    ⟨[85061, 7], [68297, 89593], .contexts [
        ⟨136938, false, false, [], []⟩
      ]⟩,
    ⟨[85061, 9], [75309, 97183], .contexts [
        ⟨146770, true, false, [75306], [9]⟩,
        ⟨46, false, false, [75306, 97183], []⟩,
        ⟨146628, true, false, [], [97183]⟩
      ]⟩,
    ⟨[85061, 11], [67031, 94003], .contexts [
        ⟨136941, false, false, [], []⟩,
        ⟨136940, false, false, [], []⟩
      ]⟩,
    ⟨[85061, 13], [85059], .contexts [
        ⟨29805, false, false, [], []⟩,
        ⟨29915, false, false, [], []⟩
      ]⟩,
    ⟨[85063], [19293, 85061], .contexts [
        ⟨29811, true, false, [], []⟩,
        ⟨29811, true, false, [], []⟩,
        ⟨29913, true, false, [], []⟩,
        ⟨29912, true, false, [], []⟩,
        ⟨37849, true, false, [19306], [1]⟩,
        ⟨8, false, false, [19306, 85061], []⟩,
        ⟨37772, true, false, [], [85061]⟩,
        ⟨37848, false, false, [], []⟩,
        ⟨37773, true, false, [], [85061]⟩
      ]⟩,
    ⟨[85061, 15], [19293, 85061], .contexts [
        ⟨29807, false, false, [], []⟩,
        ⟨159900, false, false, [], []⟩
      ]⟩,
    ⟨[85065, 1], [19293, 85061], .contexts [
        ⟨29812, false, false, [], []⟩,
        ⟨159900, false, false, [], []⟩
      ]⟩,
    ⟨[85065, 3], [85067], .contexts [
        ⟨29814, false, false, [], []⟩,
        ⟨29909, false, false, [], []⟩
      ]⟩,
    ⟨[85065, 5], [69951, 91795], .contexts [
        ⟨138556, true, false, [69948], [5]⟩,
        ⟨28, false, false, [69948, 91795], []⟩,
        ⟨138557, true, false, [], [91795]⟩
      ]⟩,
    ⟨[85065, 7], [68197, 89595], .contexts [
        ⟨136814, true, false, [68194], [7]⟩,
        ⟨38, false, false, [68194, 89595], []⟩,
        ⟨136815, true, false, [], [89595]⟩
      ]⟩,
    ⟨[85065, 9], [20821, 85065], .contexts [
        ⟨43206, false, false, [], []⟩
      ]⟩,
    ⟨[94001], [68153, 69347, 88247], .contexts [
        ⟨137958, false, false, [], []⟩,
        ⟨139412, false, false, [], []⟩
      ]⟩,
    ⟨[85065, 11], [67949, 68153, 69347, 88247], .contexts [
        ⟨136576, false, false, [], []⟩,
        ⟨159907, false, false, [67949], []⟩
      ]⟩,
    ⟨[85065, 13], [67901, 93865], .contexts [
        ⟨136526, false, false, [], []⟩
      ]⟩,
    ⟨[85065, 15], [19293, 85065], .contexts [
        ⟨37845, false, false, [], []⟩,
        ⟨37846, false, false, [], []⟩
      ]⟩,
    ⟨[85067, 1], [71263, 90011], .contexts [
        ⟨140085, false, false, [], []⟩,
        ⟨140101, false, false, [], []⟩
      ]⟩,
    ⟨[85067, 3], [85065], .contexts [
        ⟨29816, false, false, [], []⟩,
        ⟨29911, false, false, [], []⟩
      ]⟩,
    ⟨[85067, 5], [85069], .contexts [
        ⟨29818, false, false, [], []⟩,
        ⟨29906, false, false, [], []⟩
      ]⟩,
    ⟨[85067, 7], [70309, 89933], .contexts [
        ⟨139020, false, false, [], []⟩,
        ⟨140098, false, false, [], []⟩
      ]⟩,
    ⟨[85067, 9], [20815, 85067], .contexts [
        ⟨42994, false, false, [], []⟩,
        ⟨43204, false, false, [], []⟩
      ]⟩,
    ⟨[85067, 11], [70685, 88939], .contexts [
        ⟨139418, false, false, [], []⟩,
        ⟨140139, false, false, [], []⟩
      ]⟩,
    ⟨[85067, 13], [70313, 87365], .contexts [
        ⟨139025, true, false, [70310], [13]⟩,
        ⟨59, false, false, [70310, 87365], []⟩,
        ⟨139026, true, false, [], [87365]⟩
      ]⟩,
    ⟨[85067, 15], [19307, 85067], .contexts [
        ⟨37830, false, false, [], []⟩,
        ⟨37837, false, false, [], []⟩
      ]⟩,
    ⟨[85069, 1], [85071], .contexts [
        ⟨29822, false, false, [], []⟩,
        ⟨29904, false, false, [], []⟩
      ]⟩,
    ⟨[85069, 3], [71687, 95853], .contexts [
        ⟨140562, false, false, [], []⟩
      ]⟩,
    ⟨[85069, 5], [85067], .contexts [
        ⟨29820, false, false, [], []⟩,
        ⟨29909, false, false, [], []⟩
      ]⟩,
    ⟨[85069, 7], [17881, 85069], .contexts [
        ⟨30173, false, false, [], []⟩,
        ⟨71773, false, false, [], []⟩
      ]⟩,
    ⟨[85069, 9], [20821, 85069], .contexts [
        ⟨42768, false, false, [], []⟩,
        ⟨42989, false, false, [], []⟩
      ]⟩,
    ⟨[85069, 11], [27791, 92371], .contexts [
        ⟨71754, false, false, [], []⟩,
        ⟨71777, false, false, [], []⟩
      ]⟩,
    ⟨[85069, 13], [72361, 96847], .contexts [
        ⟨142025, true, false, [72358], [13]⟩,
        ⟨59, false, false, [72358, 96847], []⟩,
        ⟨142026, true, false, [], [96847]⟩
      ]⟩,
    ⟨[85069, 15], [19293, 85069], .contexts [
        ⟨37813, false, false, [], []⟩,
        ⟨37823, false, false, [], []⟩
      ]⟩,
    ⟨[85071, 1], [85069], .contexts [
        ⟨29824, false, false, [], []⟩,
        ⟨29906, false, false, [], []⟩
      ]⟩,
    ⟨[85071, 3], [20823, 85071], .contexts [
        ⟨29828, true, false, [], [3]⟩,
        ⟨42770, true, false, [20818], [9, 3]⟩,
        ⟨42770, true, false, [20818], [9, 3]⟩,
        ⟨42769, true, false, [20818], [9, 3]⟩,
        ⟨42761, true, false, [20818], [9, 3]⟩,
        ⟨573, false, false, [20818, 85073], []⟩,
        ⟨30163, false, false, [20818], []⟩,
        ⟨30162, false, false, [20818], []⟩,
        ⟨30165, false, false, [20818], []⟩,
        ⟨42772, true, false, [], [85071]⟩,
        ⟨42772, true, false, [], [85071]⟩,
        ⟨42771, true, false, [], [85071]⟩
      ]⟩,
    ⟨[85071, 5], [71577, 90011], .contexts [
        ⟨140434, false, false, [], []⟩
      ]⟩,
    ⟨[85071, 7], [17879, 85071], .contexts [
        ⟨30166, false, false, [], []⟩,
        ⟨30167, false, false, [], []⟩
      ]⟩,
    ⟨[85071, 9], [85073], .contexts [
        ⟨29826, false, false, [], []⟩,
        ⟨29902, false, false, [], []⟩
      ]⟩,
    ⟨[85071, 11], [27791, 96883], .contexts [
        ⟨142839, true, false, [27788], [11]⟩,
        ⟨53, false, false, [27788, 96883], []⟩,
        ⟨71743, true, false, [], [96883]⟩
      ]⟩,
    ⟨[85071, 13], [27791, 43587, 47523, 84011], .contexts [
        ⟨71749, false, false, [], []⟩,
        ⟨158756, false, false, [27791], []⟩
      ]⟩,
    ⟨[85071, 15], [19307, 85071], .contexts [
        ⟨37793, false, false, [], []⟩,
        ⟨37810, false, false, [], []⟩
      ]⟩,
    ⟨[85073, 1], [20815, 85073], .contexts [
        ⟨42756, false, false, [], []⟩,
        ⟨42762, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2499. -/
def y322TCIndexRaw2499 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85073, 3], [20819, 85073], .contexts [
        ⟨42761, false, false, [], []⟩,
        ⟨42769, false, false, [], []⟩
      ]⟩,
    ⟨[85073, 5], [74447, 97005], .contexts [
        ⟨145150, true, false, [74444], [5]⟩,
        ⟨28, false, false, [74444, 97005], []⟩,
        ⟨145151, true, false, [], [97005]⟩
      ]⟩,
    ⟨[85073, 7], [17881, 85073], .contexts [
        ⟨30159, false, false, [], []⟩,
        ⟨30160, false, false, [], []⟩
      ]⟩,
    ⟨[85073, 9], [85071], .contexts [
        ⟨29828, false, false, [], []⟩,
        ⟨29904, false, false, [], []⟩
      ]⟩,
    ⟨[85073, 11], [20809, 85073], .contexts [
        ⟨29830, false, false, [], []⟩,
        ⟨42757, false, false, [], []⟩
      ]⟩,
    ⟨[85073, 13], [20807, 47541, 84013], .contexts [
        ⟨42749, false, false, [], []⟩,
        ⟨112948, false, false, [20807], []⟩
      ]⟩,
    ⟨[85073, 15], [19293, 85073], .contexts [
        ⟨37777, false, false, [], []⟩,
        ⟨37790, false, false, [], []⟩
      ]⟩,
    ⟨[85091, 1], [19227, 86561], .contexts [
        ⟨37587, false, false, [], []⟩,
        ⟨37630, false, false, [], []⟩
      ]⟩,
    ⟨[85091, 3], [19231, 83473], .contexts [
        ⟨37590, true, false, [19228], [3]⟩,
        ⟨37524, false, false, [19228], []⟩,
        ⟨37523, false, false, [19228], []⟩,
        ⟨37591, true, false, [], [19169, 83473]⟩,
        ⟨37594, true, false, [], [83473]⟩
      ]⟩,
    ⟨[85091, 5], [17871, 85091], .contexts [
        ⟨30088, false, false, [], []⟩,
        ⟨30095, false, false, [], []⟩
      ]⟩,
    ⟨[85091, 7], [17873, 85091], .contexts [
        ⟨30094, false, false, [], []⟩,
        ⟨30106, false, false, [], []⟩
      ]⟩,
    ⟨[85091, 9], [19265, 20373, 84725], .contexts [
        ⟨29858, false, false, [], []⟩,
        ⟨37641, false, false, [], []⟩,
        ⟨41926, false, false, [], []⟩
      ]⟩,
    ⟨[85091, 11], [85093], .contexts [
        ⟨29860, false, false, [], []⟩,
        ⟨29882, false, false, [], []⟩
      ]⟩,
    ⟨[85091, 13], [19227, 86565], .contexts [
        ⟨37593, false, false, [], []⟩,
        ⟨37653, false, false, [], []⟩
      ]⟩,
    ⟨[85091, 15], [48119, 48979, 88921], .contexts [
        ⟨113455, false, false, [], []⟩,
        ⟨114340, false, false, [48119], []⟩
      ]⟩,
    ⟨[85093, 1], [17837, 82995], .contexts [
        ⟨29864, false, false, [], []⟩,
        ⟨42277, false, false, [], []⟩
      ]⟩,
    ⟨[85093, 3], [19397, 20575, 86691], .contexts [
        ⟨38502, false, false, [], []⟩,
        ⟨42253, false, false, [19397], []⟩
      ]⟩,
    ⟨[85093, 5], [17863, 85093], .contexts [
        ⟨30069, false, false, [], []⟩,
        ⟨30079, false, false, [], []⟩
      ]⟩,
    ⟨[85093, 7], [17869, 85093], .contexts [
        ⟨30074, false, false, [], []⟩,
        ⟨30089, false, false, [], []⟩
      ]⟩,
    ⟨[85093, 9], [20485, 85093], .contexts [
        ⟨42066, false, false, [], []⟩,
        ⟨42274, false, false, [], []⟩
      ]⟩,
    ⟨[85093, 11], [85091], .contexts [
        ⟨29862, false, false, [], []⟩,
        ⟨29884, false, false, [], []⟩
      ]⟩,
    ⟨[85093, 13], [17837, 92503], .contexts [
        ⟨72794, true, false, [17838], [13]⟩,
        ⟨59, false, false, [17838, 92503], []⟩,
        ⟨30025, true, false, [], [92503]⟩
      ]⟩,
    ⟨[85093, 15], [17837, 82999], .contexts [
        ⟨30078, false, false, [], []⟩,
        ⟨42303, false, false, [], []⟩
      ]⟩,
    ⟨[85099, 1], [85101], .contexts [
        ⟨29875, false, false, [], []⟩,
        ⟨29878, false, false, [], []⟩
      ]⟩,
    ⟨[85099, 3], [21431, 87681], .contexts [
        ⟨45322, false, false, [], []⟩,
        ⟨45324, false, false, [], []⟩
      ]⟩,
    ⟨[85099, 5], [17843, 85099], .contexts [
        ⟨30034, false, false, [], []⟩
      ]⟩,
    ⟨[85099, 7], [17849, 85099], .contexts [
        ⟨30039, false, false, [], []⟩,
        ⟨45367, false, false, [], []⟩
      ]⟩,
    ⟨[85099, 9], [20729, 86579], .contexts [
        ⟨42590, false, false, [], []⟩,
        ⟨45386, false, false, [], []⟩
      ]⟩,
    ⟨[85099, 11], [17971, 85229], .contexts [
        ⟨30707, false, false, [], []⟩,
        ⟨45372, false, false, [], []⟩
      ]⟩,
    ⟨[85099, 13], [18409, 18415, 85847], .contexts [
        ⟨33664, false, false, [], []⟩,
        ⟨33679, false, false, [18409], []⟩
      ]⟩,
    ⟨[85099, 15], [17837, 82993], .contexts [
        ⟨29873, false, false, [], []⟩,
        ⟨30053, false, false, [], []⟩
      ]⟩,
    ⟨[85101, 1], [85099], .contexts [
        ⟨29877, false, false, [], []⟩,
        ⟨30029, false, false, [], []⟩
      ]⟩,
    ⟨[85101, 3], [17837, 83787], .contexts [
        ⟨29994, false, false, [], []⟩,
        ⟨29990, false, false, [], []⟩
      ]⟩,
    ⟨[85101, 5], [17845, 85101], .contexts [
        ⟨30006, false, false, [], []⟩,
        ⟨30027, false, false, [], []⟩
      ]⟩,
    ⟨[85101, 7], [17851, 85101], .contexts [
        ⟨30012, false, false, [], []⟩,
        ⟨30035, false, false, [], []⟩
      ]⟩,
    ⟨[85101, 9], [21425, 87689], .contexts [
        ⟨45311, false, false, [], []⟩
      ]⟩,
    ⟨[85101, 11], [17955, 85233], .contexts [
        ⟨30671, true, false, [17952], [11]⟩,
        ⟨53, false, false, [17952, 85233], []⟩,
        ⟨30672, true, false, [], [85233]⟩
      ]⟩,
    ⟨[85101, 13], [17857, 85101], .contexts [
        ⟨30017, false, false, [], []⟩
      ]⟩,
    ⟨[85101, 15], [17837, 82991], .contexts [
        ⟨30026, false, false, [], []⟩,
        ⟨30018, false, false, [], []⟩
      ]⟩,
    ⟨[85103, 1], [17883, 83933], .contexts [
        ⟨30184, false, false, [], []⟩,
        ⟨72777, false, false, [], []⟩
      ]⟩,
    ⟨[85103, 3], [86109], .contexts [
        ⟨35382, false, false, [], []⟩,
        ⟨35377, false, false, [], []⟩
      ]⟩,
    ⟨[85103, 5], [78269], .contexts [
        ⟨30187, false, false, [], []⟩,
        ⟨3912, false, false, [], []⟩
      ]⟩,
    ⟨[85103, 7], [16407, 85103], .contexts [
        ⟨30179, true, false, [], [7]⟩,
        ⟨647, false, false, [83513], []⟩,
        ⟨648, false, false, [83513], []⟩,
        ⟨21844, false, false, [], [11]⟩,
        ⟨21848, false, false, [], [11]⟩,
        ⟨21842, false, false, [], [11]⟩,
        ⟨21843, false, false, [], [11]⟩,
        ⟨21843, false, false, [], [11]⟩,
        ⟨30175, false, false, [16407], []⟩,
        ⟨30188, false, false, [], []⟩,
        ⟨30189, false, false, [16407], []⟩,
        ⟨21847, true, false, [], [85103]⟩,
        ⟨30188, false, false, [], []⟩
      ]⟩,
    ⟨[85103, 9], [17887, 83531], .contexts [
        ⟨30192, false, false, [], []⟩
      ]⟩,
    ⟨[85103, 11], [83513], .contexts [
        ⟨30176, false, false, [], []⟩,
        ⟨21830, false, false, [], []⟩
      ]⟩,
    ⟨[85103, 13], [78265], .contexts [
        ⟨30195, false, false, [], []⟩,
        ⟨3883, false, false, [], []⟩
      ]⟩,
    ⟨[85103, 15], [1389, 85103], .contexts [
        ⟨30198, false, false, [], []⟩,
        ⟨30197, false, false, [], []⟩
      ]⟩,
    ⟨[85105, 1], [87571], .contexts [
        ⟨44220, false, false, [], []⟩,
        ⟨44214, false, false, [], []⟩
      ]⟩,
    ⟨[85105, 3], [78729], .contexts [
        ⟨30201, false, false, [], []⟩,
        ⟨4851, false, false, [], []⟩
      ]⟩,
    ⟨[85105, 5], [85107], .contexts [
        ⟨30217, false, false, [], []⟩,
        ⟨30219, false, false, [], []⟩
      ]⟩,
    ⟨[85105, 7], [315, 85105], .contexts [
        ⟨30205, true, false, [], [7]⟩,
        ⟨140, false, false, [78729], []⟩,
        ⟨141, false, false, [78729], []⟩,
        ⟨4857, false, false, [], [3]⟩,
        ⟨4859, false, false, [], [3]⟩,
        ⟨4855, false, false, [], [3]⟩,
        ⟨4856, false, false, [], [3]⟩,
        ⟨4856, false, false, [], [3]⟩,
        ⟨30200, false, false, [315], []⟩,
        ⟨30206, false, false, [], []⟩,
        ⟨30207, false, false, [315], []⟩,
        ⟨1689, true, false, [], [85105]⟩,
        ⟨30206, false, false, [], []⟩
      ]⟩,
    ⟨[85105, 9], [1063, 85105], .contexts [
        ⟨30213, false, false, [], []⟩,
        ⟨30209, false, false, [], []⟩
      ]⟩,
    ⟨[85105, 11], [42271, 86355], .contexts [
        ⟨44697, false, false, [], []⟩,
        ⟨155293, false, false, [], []⟩
      ]⟩,
    ⟨[85105, 13], [83795], .contexts [
        ⟨30215, false, false, [], []⟩,
        ⟨23112, false, false, [], []⟩
      ]⟩,
    ⟨[85105, 15], [17755, 86571], .contexts [
        ⟨37991, false, false, [], []⟩,
        ⟨40002, false, false, [], []⟩
      ]⟩,
    ⟨[85107, 1], [85109], .contexts [
        ⟨30235, false, false, [], []⟩,
        ⟨33216, false, false, [], []⟩
      ]⟩,
    ⟨[85107, 3], [7355, 79513], .contexts [
        ⟨30225, false, false, [], []⟩,
        ⟨30223, false, false, [], []⟩
      ]⟩,
    ⟨[85107, 5], [85105], .contexts [
        ⟨30218, false, false, [], []⟩,
        ⟨30203, false, false, [], []⟩
      ]⟩,
    ⟨[85107, 7], [7355, 91255], .contexts [
        ⟨65123, true, false, [7356], [7]⟩,
        ⟨38, false, false, [7356, 91255], []⟩,
        ⟨10990, true, false, [], [91255]⟩
      ]⟩,
    ⟨[85107, 9], [1063, 85107], .contexts [
        ⟨30231, false, false, [], []⟩,
        ⟨30227, false, false, [], []⟩
      ]⟩,
    ⟨[7355, 87575], [7355, 87575], .contexts []⟩,
    ⟨[85107, 11], [7355, 87575], .contexts [
        ⟨44732, true, false, [7356], [11]⟩,
        ⟨53, false, false, [7356, 87575], []⟩,
        ⟨44733, false, false, [], []⟩,
        ⟨159996, false, false, [], []⟩
      ]⟩,
    ⟨[85107, 13], [83797], .contexts [
        ⟨30233, false, false, [], []⟩,
        ⟨23126, false, false, [], []⟩
      ]⟩,
    ⟨[85107, 15], [18271, 85493], .contexts [
        ⟨32418, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2500. -/
def y322TCIndexRaw2500 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85109, 1], [85107], .contexts [
        ⟨30236, false, false, [], []⟩,
        ⟨30219, false, false, [], []⟩
      ]⟩,
    ⟨[85109, 3], [85495], .contexts [
        ⟨32421, false, false, [], []⟩,
        ⟨32423, false, false, [], []⟩
      ]⟩,
    ⟨[85109, 5], [21105, 87571], .contexts [
        ⟨44235, true, false, [21102], [5]⟩,
        ⟨28, false, false, [21102, 87571], []⟩,
        ⟨44236, true, false, [], [87571]⟩
      ]⟩,
    ⟨[85109, 7], [24057, 89435], .contexts [
        ⟨55992, false, false, [], []⟩,
        ⟨56011, false, false, [], []⟩
      ]⟩,
    ⟨[85109, 9], [85111], .contexts [
        ⟨30238, false, false, [], []⟩,
        ⟨30242, false, false, [], []⟩
      ]⟩,
    ⟨[85109, 11], [22757, 88469], .contexts [
        ⟨50424, true, false, [22754], [11]⟩,
        ⟨53, false, false, [22754, 88469], []⟩,
        ⟨50425, true, false, [], [88469]⟩
      ]⟩,
    ⟨[85109, 13], [21117, 85313], .contexts [
        ⟨44266, false, false, [], []⟩,
        ⟨44309, false, false, [], []⟩
      ]⟩,
    ⟨[85109, 15], [18271, 46227, 87507], .contexts [
        ⟨53664, false, false, [], []⟩,
        ⟨111533, false, false, [18271], []⟩
      ]⟩,
    ⟨[85111, 1], [1063, 85111], .contexts [
        ⟨30254, false, false, [], []⟩,
        ⟨30249, false, false, [], []⟩
      ]⟩,
    ⟨[85721], [39863, 84461], .contexts [
        ⟨104960, false, false, [], []⟩
      ]⟩,
    ⟨[85111, 3], [39863, 84461], .contexts [
        ⟨33219, false, false, [], []⟩,
        ⟨160009, false, false, [], []⟩
      ]⟩,
    ⟨[85111, 5], [23079, 88585], .contexts [
        ⟨51523, false, false, [], []⟩
      ]⟩,
    ⟨[85111, 7], [24057, 91259], .contexts [
        ⟨65204, true, false, [24054], [7]⟩,
        ⟨38, false, false, [24054, 91259], []⟩,
        ⟨55990, true, false, [], [91259]⟩
      ]⟩,
    ⟨[85111, 9], [85109], .contexts [
        ⟨30240, false, false, [], []⟩,
        ⟨33216, false, false, [], []⟩
      ]⟩,
    ⟨[85111, 11], [85113], .contexts [
        ⟨30256, false, false, [], []⟩,
        ⟨30259, false, false, [], []⟩
      ]⟩,
    ⟨[85111, 13], [21117, 85311], .contexts [
        ⟨44322, false, false, [], []⟩,
        ⟨44317, false, false, [], []⟩
      ]⟩,
    ⟨[85111, 15], [23105, 85211], .contexts [
        ⟨51578, false, false, [], []⟩,
        ⟨51619, false, false, [], []⟩
      ]⟩,
    ⟨[85113, 1], [1063, 85113], .contexts [
        ⟨30264, false, false, [], []⟩,
        ⟨30261, false, false, [], []⟩
      ]⟩,
    ⟨[85113, 3], [85723], .contexts [
        ⟨33233, false, false, [], []⟩,
        ⟨33228, false, false, [], []⟩
      ]⟩,
    ⟨[85113, 5], [23079, 91369], .contexts [
        ⟨65766, false, false, [], []⟩
      ]⟩,
    ⟨[85113, 7], [24057, 91261], .contexts [
        ⟨65227, true, false, [24054], [7]⟩,
        ⟨38, false, false, [24054, 91261], []⟩,
        ⟨55990, true, false, [], [91261]⟩
      ]⟩,
    ⟨[85113, 9], [22251, 84389], .contexts [
        ⟨48291, true, false, [22248], [9]⟩,
        ⟨46, false, false, [22248, 84389], []⟩,
        ⟨48269, true, false, [], [84389]⟩,
        ⟨48287, false, false, [], []⟩
      ]⟩,
    ⟨[85113, 11], [85111], .contexts [
        ⟨30257, false, false, [], []⟩,
        ⟨30242, false, false, [], []⟩
      ]⟩,
    ⟨[85113, 13], [33517, 84253], .contexts [
        ⟨30266, false, false, [], []⟩,
        ⟨91355, false, false, [], []⟩
      ]⟩,
    ⟨[85113, 15], [23105, 88977], .contexts [
        ⟨53703, true, false, [23106], [15]⟩,
        ⟨1, false, false, [23106, 88977], []⟩,
        ⟨51627, true, false, [], [88977]⟩
      ]⟩,
    ⟨[85119, 1], [33517, 50151, 83829], .contexts [
        ⟨30275, false, false, [], []⟩,
        ⟨158162, false, false, [], []⟩
      ]⟩,
    ⟨[85121], [38689, 85001], .contexts [
        ⟨110044, false, false, [], []⟩
      ]⟩,
    ⟨[85119, 3], [38689, 85001], .contexts [
        ⟨30277, false, false, [], []⟩,
        ⟨160026, false, false, [], []⟩
      ]⟩,
    ⟨[85119, 5], [26195, 50185, 83833], .contexts [
        ⟨65828, true, false, [26192], [5]⟩,
        ⟨28, false, false, [26192, 87091], []⟩,
        ⟨65829, true, false, [], [87091]⟩,
        ⟨115715, false, false, [26195], []⟩
      ]⟩,
    ⟨[85119, 7], [24057, 91267], .contexts [
        ⟨65293, true, false, [24054], [7]⟩,
        ⟨38, false, false, [24054, 91267], []⟩,
        ⟨55990, true, false, [], [91267]⟩
      ]⟩,
    ⟨[85119, 9], [38689, 96957], .contexts [
        ⟨144193, true, false, [38686], [9]⟩,
        ⟨46, false, false, [38686, 96957], []⟩,
        ⟨103667, true, false, [], [96957]⟩
      ]⟩,
    ⟨[85119, 11], [26197, 85821], .contexts [
        ⟨65837, false, false, [], []⟩,
        ⟨65839, false, false, [], []⟩
      ]⟩,
    ⟨[85119, 13], [71435, 87875], .contexts [
        ⟨140273, false, false, [], []⟩
      ]⟩,
    ⟨[85119, 15], [33517, 84255], .contexts [
        ⟨91337, true, false, [33514], [15]⟩,
        ⟨1, false, false, [33514, 84255], []⟩,
        ⟨91198, true, false, [], [84255]⟩
      ]⟩,
    ⟨[85123, 1], [85125], .contexts [
        ⟨30285, false, false, [], []⟩,
        ⟨30574, false, false, [], []⟩
      ]⟩,
    ⟨[85123, 3], [26195, 54391, 84163], .contexts [
        ⟨65859, false, false, [], []⟩,
        ⟨120713, false, false, [26195], []⟩
      ]⟩,
    ⟨[85123, 5], [38689, 85001], .contexts [
        ⟨30283, false, false, [], []⟩,
        ⟨160026, false, false, [], []⟩
      ]⟩,
    ⟨[85123, 7], [44345, 83077], .contexts [
        ⟨109198, false, false, [], []⟩
      ]⟩,
    ⟨[85123, 9], [44347, 90231], .contexts [
        ⟨109200, false, false, [], []⟩
      ]⟩,
    ⟨[85123, 11], [44349, 84473], .contexts [
        ⟨109193, true, false, [44340], [11]⟩,
        ⟨92563, false, false, [44340], []⟩,
        ⟨67359, false, false, [44340], []⟩,
        ⟨109194, true, false, [], [26521, 84473]⟩,
        ⟨109201, true, false, [], [84473]⟩
      ]⟩,
    ⟨[85123, 13], [44339, 44487, 93251], .contexts [
        ⟨109193, true, false, [44340], [13]⟩,
        ⟨92547, false, false, [44340], []⟩,
        ⟨89125, false, false, [44340], []⟩,
        ⟨109195, true, false, [], [95253]⟩,
        ⟨109195, true, false, [], [95253]⟩,
        ⟨109194, true, false, [], [95253]⟩,
        ⟨109405, false, false, [44339], []⟩
      ]⟩,
    ⟨[85123, 15], [33607, 84259], .contexts [
        ⟨91497, false, false, [], []⟩,
        ⟨91490, false, false, [], []⟩
      ]⟩,
    ⟨[85125, 1], [85123], .contexts [
        ⟨30287, false, false, [], []⟩,
        ⟨30576, false, false, [], []⟩
      ]⟩,
    ⟨[85125, 3], [44337, 61443, 83255], .contexts [
        ⟨109188, false, false, [], []⟩,
        ⟨128990, false, false, [44337], []⟩
      ]⟩,
    ⟨[85125, 5], [52345, 94129], .contexts [
        ⟨118344, false, false, [], []⟩,
        ⟨118346, false, false, [], []⟩
      ]⟩,
    ⟨[85125, 7], [51843, 83075], .contexts [
        ⟨117692, false, false, [], []⟩,
        ⟨118379, false, false, [], []⟩
      ]⟩,
    ⟨[85125, 9], [85127], .contexts [
        ⟨30289, false, false, [], []⟩,
        ⟨30573, false, false, [], []⟩
      ]⟩,
    ⟨[85125, 11], [44335, 84471], .contexts [
        ⟨109185, false, false, [], []⟩,
        ⟨118362, false, false, [], []⟩
      ]⟩,
    ⟨[85125, 13], [59777, 96909], .contexts [
        ⟨143293, false, false, [], []⟩
      ]⟩,
    ⟨[85125, 15], [33607, 84261], .contexts [
        ⟨91561, false, false, [], []⟩,
        ⟨91613, false, false, [], []⟩
      ]⟩,
    ⟨[85127, 1], [44331, 96345], .contexts [
        ⟨109237, false, false, [], []⟩,
        ⟨118509, false, false, [], []⟩
      ]⟩,
    ⟨[85127, 3], [44337, 52499, 84411], .contexts [
        ⟨109239, false, false, [], []⟩,
        ⟨118505, false, false, [44337], []⟩
      ]⟩,
    ⟨[85127, 5], [44379, 52731, 89381], .contexts [
        ⟨109241, false, false, [], []⟩,
        ⟨118787, false, false, [44379], []⟩
      ]⟩,
    ⟨[85127, 7], [56433, 89377], .contexts [
        ⟨123122, true, false, [56434], [7]⟩,
        ⟨38, false, false, [56434, 89377], []⟩,
        ⟨123120, false, true, [], [89377]⟩
      ]⟩,
    ⟨[85127, 9], [85125], .contexts [
        ⟨30291, false, false, [], []⟩,
        ⟨30574, false, false, [], []⟩
      ]⟩,
    ⟨[85127, 11], [85129], .contexts [
        ⟨30293, false, false, [], []⟩,
        ⟨30570, false, false, [], []⟩
      ]⟩,
    ⟨[85127, 13], [59777, 85183], .contexts [
        ⟨127021, true, false, [59774], [13]⟩,
        ⟨59, false, false, [59774, 85183], []⟩,
        ⟨127022, true, false, [], [85183]⟩
      ]⟩,
    ⟨[85127, 15], [33607, 84263], .contexts [
        ⟨91622, false, false, [], []⟩,
        ⟨91616, false, false, [], []⟩
      ]⟩,
    ⟨[85129, 1], [85131], .contexts [
        ⟨30297, false, false, [], []⟩,
        ⟨30569, false, false, [], []⟩
      ]⟩,
    ⟨[85129, 3], [60037, 67753, 87833], .contexts [
        ⟨127306, false, false, [], []⟩,
        ⟨136323, false, false, [60037], []⟩
      ]⟩,
    ⟨[85129, 5], [44381, 85193], .contexts [
        ⟨109246, true, false, [44382], [5]⟩,
        ⟨30421, false, false, [44382], []⟩,
        ⟨30526, false, false, [44382], []⟩,
        ⟨109249, true, false, [], [85193]⟩,
        ⟨109250, true, false, [], [85193]⟩
      ]⟩,
    ⟨[85129, 7], [48211, 52561, 55033, 63819, 85783], .contexts [
        ⟨113544, false, false, [], []⟩,
        ⟨156494, false, false, [48211], []⟩
      ]⟩,
    ⟨[85129, 9], [45845, 55533, 86463], .contexts [
        ⟨111087, false, false, [], []⟩,
        ⟨122080, false, false, [45845], []⟩
      ]⟩,
    ⟨[85129, 11], [85127], .contexts [
        ⟨30295, false, false, [], []⟩,
        ⟨30573, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2501. -/
def y322TCIndexRaw2501 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85129, 13], [44385, 83885], .contexts [
        ⟨109252, false, false, [], []⟩,
        ⟨118613, false, false, [], []⟩
      ]⟩,
    ⟨[85129, 15], [33607, 84265], .contexts [
        ⟨91660, false, false, [], []⟩,
        ⟨91681, false, false, [], []⟩
      ]⟩,
    ⟨[85131, 1], [85129], .contexts [
        ⟨30299, false, false, [], []⟩,
        ⟨30570, false, false, [], []⟩
      ]⟩,
    ⟨[85131, 3], [44419, 85807], .contexts [
        ⟨109294, true, false, [44382], [3]⟩,
        ⟨51811, false, false, [44382], []⟩,
        ⟨51808, false, false, [44382], []⟩,
        ⟨109247, true, false, [], [23147, 85807]⟩,
        ⟨109296, true, false, [], [85807]⟩
      ]⟩,
    ⟨[85131, 5], [44423, 53167, 91297], .contexts [
        ⟨109299, false, false, [], []⟩,
        ⟨119302, false, false, [44423], []⟩
      ]⟩,
    ⟨[85131, 7], [44425, 83883], .contexts [
        ⟨109294, true, false, [44382], [7]⟩,
        ⟨100789, true, false, [44382, 36758], [7]⟩,
        ⟨38, false, false, [44382, 36758, 83883], []⟩,
        ⟨100787, false, true, [44382], [83883]⟩,
        ⟨100784, false, false, [44382], []⟩,
        ⟨109247, true, false, [], [36757, 83883]⟩,
        ⟨109300, true, false, [], [83883]⟩
      ]⟩,
    ⟨[85131, 9], [44417, 83821], .contexts [
        ⟨109294, true, false, [44382], [9]⟩,
        ⟨30427, false, false, [44382], []⟩,
        ⟨104440, false, false, [44382], []⟩,
        ⟨109250, true, false, [], [39363, 83821]⟩,
        ⟨109295, true, false, [], [83821]⟩
      ]⟩,
    ⟨[85131, 11], [44421, 96345], .contexts [
        ⟨109294, true, false, [44382], [11]⟩,
        ⟨98378, false, false, [44382], []⟩,
        ⟨98380, false, false, [44382], []⟩,
        ⟨109247, true, false, [], [35841, 96345]⟩,
        ⟨109297, true, false, [], [96345]⟩
      ]⟩,
    ⟨[85131, 13], [85133], .contexts [
        ⟨30301, false, false, [], []⟩,
        ⟨30568, false, false, [], []⟩
      ]⟩,
    ⟨[85131, 15], [33607, 84267], .contexts [
        ⟨91686, true, false, [33608], [15]⟩,
        ⟨1, false, false, [33608, 84267], []⟩,
        ⟨91496, true, false, [], [84267]⟩,
        ⟨91684, false, false, [], []⟩
      ]⟩,
    ⟨[85133, 1], [44429, 85651], .contexts [
        ⟨109310, false, false, [], []⟩,
        ⟨118688, false, false, [], []⟩
      ]⟩,
    ⟨[85133, 3], [52661, 57493, 86837], .contexts [
        ⟨118701, false, false, [], []⟩,
        ⟨124380, false, false, [52661], []⟩
      ]⟩,
    ⟨[85133, 5], [44435, 59129, 87265], .contexts [
        ⟨109315, false, false, [], []⟩,
        ⟨126273, false, false, [44435], []⟩
      ]⟩,
    ⟨[85133, 7], [44437, 85193], .contexts [
        ⟨109318, false, false, [], []⟩,
        ⟨118726, false, false, [], []⟩
      ]⟩,
    ⟨[85133, 9], [44433, 83823], .contexts [
        ⟨109312, false, false, [], []⟩,
        ⟨118702, false, false, [], []⟩
      ]⟩,
    ⟨[85133, 11], [44435, 58137, 91155], .contexts [
        ⟨109316, false, false, [], []⟩,
        ⟨125051, false, false, [44435], []⟩
      ]⟩,
    ⟨[85133, 13], [85131], .contexts [
        ⟨30303, false, false, [], []⟩,
        ⟨30569, false, false, [], []⟩
      ]⟩,
    ⟨[85133, 15], [85135], .contexts [
        ⟨30305, false, false, [], []⟩,
        ⟨30566, false, false, [], []⟩
      ]⟩,
    ⟨[85135, 1], [85137], .contexts [
        ⟨30309, false, false, [], []⟩,
        ⟨30564, false, false, [], []⟩
      ]⟩,
    ⟨[85135, 3], [52661, 89381], .contexts [
        ⟨118737, false, false, [], []⟩,
        ⟨118733, false, false, [], []⟩
      ]⟩,
    ⟨[85135, 5], [44439, 50243, 85439], .contexts [
        ⟨109325, false, false, [], []⟩,
        ⟨118757, false, false, [44439], []⟩
      ]⟩,
    ⟨[85135, 7], [44445, 89277], .contexts [
        ⟨109332, false, false, [], []⟩,
        ⟨118746, false, false, [], []⟩
      ]⟩,
    ⟨[85135, 9], [46381, 83825], .contexts [
        ⟨111696, true, false, [46378], [9]⟩,
        ⟨46, false, false, [46378, 83825], []⟩,
        ⟨111697, true, false, [], [83825]⟩
      ]⟩,
    ⟨[85135, 11], [44447, 52753, 85191], .contexts [
        ⟨115809, false, false, [], []⟩,
        ⟨118806, false, false, [44447], []⟩
      ]⟩,
    ⟨[85135, 13], [33607, 84271], .contexts [
        ⟨91712, false, false, [], []⟩,
        ⟨118738, false, false, [], []⟩
      ]⟩,
    ⟨[85135, 15], [85133], .contexts [
        ⟨30307, false, false, [], []⟩,
        ⟨30568, false, false, [], []⟩
      ]⟩,
    ⟨[85137, 1], [85135], .contexts [
        ⟨30311, false, false, [], []⟩,
        ⟨30566, false, false, [], []⟩
      ]⟩,
    ⟨[85137, 3], [85139], .contexts [
        ⟨30313, false, false, [], []⟩,
        ⟨30561, false, false, [], []⟩
      ]⟩,
    ⟨[85137, 5], [96767], .contexts [
        ⟨140564, false, false, [], []⟩,
        ⟨140565, false, false, [], []⟩
      ]⟩,
    ⟨[85137, 7], [44453, 89279], .contexts [
        ⟨109346, false, false, [], []⟩,
        ⟨115810, false, false, [], []⟩
      ]⟩,
    ⟨[85137, 9], [44447, 92861], .contexts [
        ⟨109341, false, false, [], []⟩,
        ⟨140579, false, false, [], []⟩
      ]⟩,
    ⟨[85137, 11], [44447, 52753, 85189], .contexts [
        ⟨109342, false, false, [], []⟩,
        ⟨118831, false, false, [44447], []⟩
      ]⟩,
    ⟨[93899], [55133, 59233, 85747], .contexts [
        ⟨126395, false, false, [], []⟩,
        ⟨140587, false, false, [], []⟩
      ]⟩,
    ⟨[85137, 13], [52839, 55133, 59233, 85747], .contexts [
        ⟨118916, false, false, [], []⟩,
        ⟨160096, false, false, [52839], []⟩
      ]⟩,
    ⟨[85137, 15], [44451, 85651], .contexts [
        ⟨109344, false, false, [], []⟩,
        ⟨118917, false, false, [], []⟩
      ]⟩,
    ⟨[85139, 1], [44455, 92931], .contexts [
        ⟨109352, true, false, [44456], [1]⟩,
        ⟨75930, false, false, [44456], []⟩,
        ⟨75998, false, false, [44456], []⟩,
        ⟨109354, true, false, [], [92931]⟩,
        ⟨109355, true, false, [], [92931]⟩
      ]⟩,
    ⟨[85139, 3], [85137], .contexts [
        ⟨30315, false, false, [], []⟩,
        ⟨30564, false, false, [], []⟩
      ]⟩,
    ⟨[85141], [44469, 84403], .contexts [
        ⟨109368, false, false, [], []⟩
      ]⟩,
    ⟨[85139, 5], [44469, 84403], .contexts [
        ⟨30317, false, false, [], []⟩,
        ⟨160101, false, false, [], []⟩
      ]⟩,
    ⟨[85139, 7], [44465, 52809, 86653], .contexts [
        ⟨109362, false, false, [], []⟩,
        ⟨118882, false, false, [44465], []⟩
      ]⟩,
    ⟨[85139, 9], [44459, 91339], .contexts [
        ⟨109352, true, false, [44456], [9]⟩,
        ⟨75932, false, false, [44456], []⟩,
        ⟨108120, false, false, [44456], []⟩,
        ⟨109355, true, false, [], [43319, 91339]⟩,
        ⟨109356, true, false, [], [91339]⟩
      ]⟩,
    ⟨[85139, 11], [63631, 93965], .contexts [
        ⟨131686, false, false, [], []⟩
      ]⟩,
    ⟨[85139, 13], [44461, 85455], .contexts [
        ⟨109358, false, false, [], []⟩,
        ⟨118939, false, false, [], []⟩
      ]⟩,
    ⟨[85139, 15], [44463, 90845], .contexts [
        ⟨109360, false, false, [], []⟩
      ]⟩,
    ⟨[85143, 1], [44469, 84403], .contexts [
        ⟨30322, false, false, [], []⟩,
        ⟨160101, false, false, [], []⟩
      ]⟩,
    ⟨[85143, 3], [44471, 52541, 57977, 83871], .contexts [
        ⟨109377, false, false, [], []⟩,
        ⟨157726, false, false, [44471], []⟩
      ]⟩,
    ⟨[85143, 5], [44471, 92931], .contexts [
        ⟨109378, false, false, [], []⟩
      ]⟩,
    ⟨[85143, 7], [59529, 83039], .contexts [
        ⟨126729, false, false, [], []⟩,
        ⟨133468, false, false, [], []⟩
      ]⟩,
    ⟨[85143, 9], [85145], .contexts [
        ⟨30324, false, false, [], []⟩,
        ⟨30558, false, false, [], []⟩
      ]⟩,
    ⟨[85143, 11], [44477, 84407], .contexts [
        ⟨109382, false, false, [], []⟩
      ]⟩,
    ⟨[85143, 13], [44479, 45219, 83027], .contexts [
        ⟨109384, false, false, [], []⟩,
        ⟨110289, false, false, [44479], []⟩
      ]⟩,
    ⟨[85143, 15], [44475, 50841, 89389], .contexts [
        ⟨109380, false, false, [], []⟩,
        ⟨116581, false, false, [44475], []⟩
      ]⟩,
    ⟨[85145, 1], [50747, 86453], .contexts [
        ⟨116434, false, false, [], []⟩,
        ⟨125197, false, false, [], []⟩
      ]⟩,
    ⟨[85145, 3], [52869, 57977, 83869], .contexts [
        ⟨118946, false, false, [], []⟩,
        ⟨124883, false, false, [52869], []⟩
      ]⟩,
    ⟨[85145, 5], [50749, 87081], .contexts [
        ⟨116431, true, false, [50744], [5]⟩,
        ⟨116420, true, false, [50744, 50740], [5]⟩,
        ⟨28, false, false, [50744, 50740, 87081], []⟩,
        ⟨116418, false, true, [50744], [87081]⟩,
        ⟨116416, false, false, [50744], []⟩,
        ⟨116428, true, false, [], [50739, 87081]⟩,
        ⟨116436, true, false, [], [87081]⟩
      ]⟩,
    ⟨[85145, 7], [58263, 89815], .contexts [
        ⟨125185, false, false, [], []⟩,
        ⟨125188, false, false, [], []⟩
      ]⟩,
    ⟨[85145, 9], [85143], .contexts [
        ⟨30326, false, false, [], []⟩,
        ⟨30559, false, false, [], []⟩
      ]⟩,
    ⟨[85145, 11], [85147], .contexts [
        ⟨30328, false, false, [], []⟩,
        ⟨30557, false, false, [], []⟩
      ]⟩,
    ⟨[85145, 13], [50747, 86457], .contexts [
        ⟨116435, false, false, [], []⟩,
        ⟨118948, false, false, [], []⟩
      ]⟩,
    ⟨[85145, 15], [52891, 94335], .contexts [
        ⟨118971, false, false, [], []⟩
      ]⟩,
    ⟨[85147, 1], [85149], .contexts [
        ⟨30332, false, false, [], []⟩,
        ⟨30555, false, false, [], []⟩
      ]⟩,
    ⟨[85147, 3], [54257, 84423], .contexts [
        ⟨120531, false, false, [], []⟩
      ]⟩,
    ⟨[85147, 5], [54255, 91347], .contexts [
        ⟨120524, true, false, [54246], [5]⟩,
        ⟨110367, true, false, [54246, 45280], [5]⟩,
        ⟨28, false, false, [54246, 45280, 91347], []⟩,
        ⟨110368, true, false, [54246], [91347]⟩,
        ⟨120522, true, false, [], [45283, 91347]⟩,
        ⟨120529, true, false, [], [91347]⟩
      ]⟩,
    ⟨[96273], [62591, 69295, 88257], .contexts [
        ⟨130423, false, false, [], []⟩,
        ⟨137943, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2502. -/
def y322TCIndexRaw2502 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85147, 7], [54253, 62591, 69295, 88257], .contexts [
        ⟨120528, false, false, [], []⟩,
        ⟨160127, false, false, [54253], []⟩
      ]⟩,
    ⟨[85147, 9], [70599, 89887], .contexts [
        ⟨139333, false, false, [], []⟩
      ]⟩,
    ⟨[85147, 11], [85145], .contexts [
        ⟨30330, false, false, [], []⟩,
        ⟨30558, false, false, [], []⟩
      ]⟩,
    ⟨[85147, 13], [54249, 96059], .contexts [
        ⟨120524, true, false, [54246], [13]⟩,
        ⟨95808, false, false, [54246], []⟩,
        ⟨95810, false, false, [54246], []⟩,
        ⟨120525, true, false, [], [96059]⟩,
        ⟨120525, true, false, [], [96059]⟩,
        ⟨120522, true, false, [], [96059]⟩
      ]⟩,
    ⟨[85147, 15], [54251, 54277, 85155], .contexts [
        ⟨120524, true, false, [54246], [15]⟩,
        ⟨102220, true, false, [54246, 37456], [15]⟩,
        ⟨96238, false, false, [54246, 37456], []⟩,
        ⟨96284, false, false, [54246, 37456], []⟩,
        ⟨102215, true, false, [54246], [88005]⟩,
        ⟨120522, true, false, [], [37463, 88005]⟩,
        ⟨120526, true, false, [], [88005]⟩,
        ⟨120584, false, false, [54251], []⟩
      ]⟩,
    ⟨[85149, 1], [85147], .contexts [
        ⟨30334, false, false, [], []⟩,
        ⟨30557, false, false, [], []⟩
      ]⟩,
    ⟨[85149, 3], [71875, 96793], .contexts [
        ⟨141006, true, false, [71872], [3]⟩,
        ⟨20, false, false, [71872, 96793], []⟩,
        ⟨141007, true, false, [], [96793]⟩
      ]⟩,
    ⟨[85149, 5], [54265, 91345], .contexts [
        ⟨120544, false, false, [], []⟩
      ]⟩,
    ⟨[85149, 7], [54269, 62513, 69317, 88255], .contexts [
        ⟨120548, false, false, [], []⟩,
        ⟨153155, false, false, [54269], []⟩
      ]⟩,
    ⟨[85149, 9], [54263, 83243], .contexts [
        ⟨120540, false, false, [], []⟩
      ]⟩,
    ⟨[85149, 11], [54259, 86453], .contexts [
        ⟨120535, true, false, [54260], [11]⟩,
        ⟨37167, false, false, [54260], []⟩,
        ⟨37444, false, false, [54260], []⟩,
        ⟨120537, true, false, [], [86453]⟩,
        ⟨120538, true, false, [], [86453]⟩
      ]⟩,
    ⟨[85151], [54273, 85149], .contexts [
        ⟨120551, false, false, [], []⟩
      ]⟩,
    ⟨[85149, 13], [54273, 85149], .contexts [
        ⟨30336, false, false, [], []⟩,
        ⟨160139, false, false, [], []⟩
      ]⟩,
    ⟨[85149, 15], [54267, 54277, 85153], .contexts [
        ⟨120546, false, false, [], []⟩,
        ⟨120570, false, false, [54267], []⟩
      ]⟩,
    ⟨[85153, 1], [85155], .contexts [
        ⟨30343, false, false, [], []⟩,
        ⟨30553, false, false, [], []⟩
      ]⟩,
    ⟨[85153, 3], [57793, 92245], .contexts [
        ⟨124689, false, false, [], []⟩,
        ⟨128669, false, false, [], []⟩
      ]⟩,
    ⟨[85153, 5], [54287, 95395], .contexts [
        ⟨120554, true, false, [54276], [5]⟩,
        ⟨101793, false, false, [54276], []⟩,
        ⟨101790, false, false, [54276], []⟩,
        ⟨120566, true, false, [], [95395]⟩
      ]⟩,
    ⟨[85153, 7], [54289, 63325, 85059], .contexts [
        ⟨120569, false, false, [], []⟩,
        ⟨136559, false, false, [54289], []⟩
      ]⟩,
    ⟨[85153, 9], [75349, 97181], .contexts [
        ⟨146728, true, false, [75346], [9]⟩,
        ⟨46, false, false, [75346, 97181], []⟩,
        ⟨146729, true, false, [], [97181]⟩
      ]⟩,
    ⟨[85153, 11], [54275, 88001], .contexts [
        ⟨120554, true, false, [54276], [11]⟩,
        ⟨47690, false, false, [54276], []⟩,
        ⟨47884, false, false, [54276], []⟩,
        ⟨120557, true, false, [], [88001]⟩,
        ⟨120558, true, false, [], [88001]⟩
      ]⟩,
    ⟨[85153, 13], [54281, 89593], .contexts [
        ⟨120561, false, false, [], []⟩,
        ⟨128676, false, false, [], []⟩
      ]⟩,
    ⟨[85153, 15], [54273, 85149], .contexts [
        ⟨30341, false, false, [], []⟩,
        ⟨160139, false, false, [], []⟩
      ]⟩,
    ⟨[85155, 1], [85153], .contexts [
        ⟨30345, false, false, [], []⟩,
        ⟨30554, false, false, [], []⟩
      ]⟩,
    ⟨[85155, 3], [85157], .contexts [
        ⟨30347, false, false, [], []⟩,
        ⟨30552, false, false, [], []⟩
      ]⟩,
    ⟨[85155, 5], [54287, 95393], .contexts [
        ⟨120573, true, false, [54276], [5]⟩,
        ⟨101675, false, false, [54276], []⟩,
        ⟨101788, false, false, [54276], []⟩,
        ⟨120566, true, false, [], [95393]⟩
      ]⟩,
    ⟨[85155, 7], [54289, 63325, 85057], .contexts [
        ⟨120583, false, false, [], []⟩,
        ⟨131304, false, false, [54289], []⟩
      ]⟩,
    ⟨[85155, 9], [54293, 87397], .contexts [
        ⟨120573, true, false, [54276], [9]⟩,
        ⟨57316, false, false, [54276], []⟩,
        ⟨114998, false, false, [54276], []⟩,
        ⟨120555, true, false, [], [24339, 87397]⟩,
        ⟨120576, true, false, [], [87397]⟩
      ]⟩,
    ⟨[85155, 11], [54301, 94335], .contexts [
        ⟨120582, false, false, [], []⟩,
        ⟨128692, false, false, [], []⟩
      ]⟩,
    ⟨[85155, 13], [54291, 87067], .contexts [
        ⟨120575, false, false, [], []⟩
      ]⟩,
    ⟨[85155, 15], [54299, 85147], .contexts [
        ⟨120573, true, false, [54276], [15]⟩,
        ⟨96238, true, false, [54276, 35160], [15]⟩,
        ⟨1, false, false, [54276, 35160, 96145], []⟩,
        ⟨96239, true, false, [54276], [96145]⟩,
        ⟨120578, false, false, [54276, 35163], []⟩,
        ⟨120555, true, false, [], [35163, 54295, 85147]⟩,
        ⟨120579, true, false, [], [54295, 85147]⟩,
        ⟨120580, true, false, [], [85147]⟩
      ]⟩,
    ⟨[85157, 1], [54287, 62063, 86077], .contexts [
        ⟨120590, false, false, [], []⟩,
        ⟨129807, false, false, [54287], []⟩
      ]⟩,
    ⟨[85157, 3], [85155], .contexts [
        ⟨30349, false, false, [], []⟩,
        ⟨30553, false, false, [], []⟩
      ]⟩,
    ⟨[85157, 5], [85159], .contexts [
        ⟨30351, false, false, [], []⟩,
        ⟨30550, false, false, [], []⟩
      ]⟩,
    ⟨[85157, 7], [61235, 84567], .contexts [
        ⟨128720, false, false, [], []⟩,
        ⟨128714, false, false, [], []⟩
      ]⟩,
    ⟨[85157, 9], [75977, 97233], .contexts [
        ⟨147674, true, false, [75974], [9]⟩,
        ⟨46, false, false, [75974, 97233], []⟩,
        ⟨147675, true, false, [], [97233]⟩
      ]⟩,
    ⟨[85157, 11], [54309, 90239], .contexts [
        ⟨120595, false, false, [], []⟩,
        ⟨128699, false, false, [], []⟩
      ]⟩,
    ⟨[85157, 13], [54311, 87065], .contexts [
        ⟨120597, false, false, [], []⟩,
        ⟨128708, false, false, [], []⟩
      ]⟩,
    ⟨[85157, 15], [55191, 84423], .contexts [
        ⟨121606, false, false, [], []⟩
      ]⟩,
    ⟨[85159, 1], [85161], .contexts [
        ⟨30355, false, false, [], []⟩,
        ⟨30549, false, false, [], []⟩
      ]⟩,
    ⟨[85159, 3], [60347, 88513], .contexts [
        ⟨127669, true, false, [60344], [3]⟩,
        ⟨20, false, false, [60344, 88513], []⟩,
        ⟨127670, true, false, [], [88513]⟩
      ]⟩,
    ⟨[85159, 5], [85157], .contexts [
        ⟨30353, false, false, [], []⟩,
        ⟨30552, false, false, [], []⟩
      ]⟩,
    ⟨[85159, 7], [63387, 84655], .contexts [
        ⟨131372, true, false, [63384], [7]⟩,
        ⟨38, false, false, [63384, 84655], []⟩,
        ⟨131373, true, false, [], [84655]⟩
      ]⟩,
    ⟨[85159, 9], [74575, 97023], .contexts [
        ⟨145393, true, false, [74572], [9]⟩,
        ⟨46, false, false, [74572, 97023], []⟩,
        ⟨145394, true, false, [], [97023]⟩
      ]⟩,
    ⟨[85159, 11], [61227, 85167], .contexts [
        ⟨128705, false, false, [], []⟩
      ]⟩,
    ⟨[85159, 13], [61231, 95287], .contexts [
        ⟨128711, false, false, [], []⟩
      ]⟩,
    ⟨[85159, 15], [61193, 87297], .contexts [
        ⟨128664, true, false, [61190], [15]⟩,
        ⟨1, false, false, [61190, 87297], []⟩,
        ⟨128665, true, false, [], [87297]⟩
      ]⟩,
    ⟨[85161, 1], [85159], .contexts [
        ⟨30357, false, false, [], []⟩,
        ⟨30550, false, false, [], []⟩
      ]⟩,
    ⟨[85161, 3], [59731, 83851], .contexts [
        ⟨126966, true, false, [59722], [3]⟩,
        ⟨126950, true, false, [59722, 59704], [3]⟩,
        ⟨75352, false, false, [59722, 59704], []⟩,
        ⟨124726, false, false, [59722, 59704, 28979], []⟩,
        ⟨126951, true, false, [59722], [28979, 57805, 83851]⟩,
        ⟨126957, true, false, [59722], [57805, 83851]⟩,
        ⟨126958, true, false, [59722], [83851]⟩,
        ⟨126967, true, false, [], [59711, 83851]⟩,
        ⟨126971, true, false, [], [83851]⟩
      ]⟩,
    ⟨[85161, 5], [59735, 62063, 86077], .contexts [
        ⟨126974, false, false, [], []⟩,
        ⟨129807, false, false, [59735], []⟩
      ]⟩,
    ⟨[85161, 7], [59733, 83307], .contexts [
        ⟨126966, true, false, [59722], [7]⟩,
        ⟨126950, true, false, [59722, 59704], [7]⟩,
        ⟨100675, false, false, [59722, 59704], []⟩,
        ⟨103935, false, false, [59722, 59704, 36711], []⟩,
        ⟨126951, true, false, [59722], [36711, 38883, 83307]⟩,
        ⟨126959, true, false, [59722], [38883, 83307]⟩,
        ⟨126960, true, false, [59722], [83307]⟩,
        ⟨126967, true, false, [], [59715, 83307]⟩,
        ⟨126972, true, false, [], [83307]⟩
      ]⟩,
    ⟨[85161, 9], [59723, 85161], .contexts [
        ⟨30359, false, false, [], []⟩,
        ⟨126966, false, false, [], []⟩
      ]⟩,
    ⟨[85161, 11], [59725, 84989], .contexts [
        ⟨126966, true, false, [59722], [11]⟩,
        ⟨30363, false, false, [59722], []⟩,
        ⟨126947, false, false, [59722], []⟩,
        ⟨126967, true, false, [], [59691, 84989]⟩,
        ⟨126968, true, false, [], [84989]⟩
      ]⟩,
    ⟨[85161, 13], [59727, 90499], .contexts [
        ⟨126966, true, false, [59722], [13]⟩,
        ⟨126950, true, false, [59722, 59704], [13]⟩,
        ⟨61326, false, false, [59722, 59704], []⟩,
        ⟨61571, false, false, [59722, 59704], []⟩,
        ⟨126952, true, false, [59722], [90499]⟩,
        ⟨126953, true, false, [59722], [90499]⟩,
        ⟨126967, true, false, [], [59703, 90499]⟩,
        ⟨126969, true, false, [], [90499]⟩
      ]⟩,
    ⟨[85161, 15], [59729, 87295], .contexts [
        ⟨126966, true, false, [59722], [15]⟩,
        ⟨126950, true, false, [59722, 59704], [15]⟩,
        ⟨61328, false, false, [59722, 59704], []⟩,
        ⟨111143, false, false, [59722, 59704], []⟩,
        ⟨126953, true, false, [59722], [39445, 87295]⟩,
        ⟨126954, true, false, [59722], [87295]⟩,
        ⟨126967, true, false, [], [59707, 87295]⟩,
        ⟨126970, true, false, [], [87295]⟩
      ]⟩,
    ⟨[85167, 1], [59691, 84989], .contexts [
        ⟨30368, false, false, [], []⟩,
        ⟨126946, false, false, [], []⟩
      ]⟩,
    ⟨[85167, 3], [59701, 90235], .contexts [
        ⟨126936, true, false, [59678], [3]⟩,
        ⟨109082, false, false, [59678], []⟩,
        ⟨118120, false, false, [59678], []⟩,
        ⟨126918, true, false, [], [44265, 90235]⟩,
        ⟨126943, true, false, [], [90235]⟩
      ]⟩,
    ⟨[85167, 5], [59699, 90239], .contexts [
        ⟨126936, true, false, [59678], [5]⟩,
        ⟨101266, false, false, [59678], []⟩,
        ⟨109101, false, false, [59678, 36977], []⟩,
        ⟨126918, true, false, [], [36977, 44271, 90239]⟩,
        ⟨126941, true, false, [], [44271, 90239]⟩,
        ⟨126942, true, false, [], [90239]⟩
      ]⟩,
    ⟨[85167, 7], [59693, 62809, 84653], .contexts [
        ⟨126936, true, false, [59678], [7]⟩,
        ⟨90200, false, false, [59678], []⟩,
        ⟨100283, false, false, [59678], []⟩,
        ⟨126918, true, false, [], [33093, 86637]⟩,
        ⟨126939, true, false, [], [86637]⟩,
        ⟨130670, false, false, [59693], []⟩
      ]⟩,
    ⟨[85167, 9], [59695, 63781, 85777], .contexts [
        ⟨126936, true, false, [59678], [9]⟩,
        ⟨100264, false, false, [59678], []⟩,
        ⟨100280, false, false, [59678], []⟩,
        ⟨126918, true, false, [], [36473, 85905]⟩,
        ⟨126940, true, false, [], [85905]⟩,
        ⟨131861, false, false, [59695], []⟩
      ]⟩,
    ⟨[85167, 11], [61229, 85159], .contexts [
        ⟨128707, false, false, [], []⟩
      ]⟩,
    ⟨[85167, 13], [85169], .contexts [
        ⟨30370, false, false, [], []⟩,
        ⟨30545, false, false, [], []⟩
      ]⟩,
    ⟨[85167, 15], [59691, 84993], .contexts [
        ⟨126938, false, false, [], []⟩
      ]⟩,
    ⟨[85169, 1], [59681, 85279], .contexts [
        ⟨126922, false, false, [], []⟩,
        ⟨128358, false, false, [], []⟩
      ]⟩,
    ⟨[85169, 3], [59685, 86817], .contexts [
        ⟨126927, false, false, [], []⟩,
        ⟨146596, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2503. -/
def y322TCIndexRaw2503 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85169, 5], [59687, 90387], .contexts [
        ⟨126929, false, false, [], []⟩,
        ⟨128391, false, false, [], []⟩
      ]⟩,
    ⟨[85169, 7], [59683, 85731], .contexts [
        ⟨126924, false, false, [], []⟩,
        ⟨128384, false, false, [], []⟩
      ]⟩,
    ⟨[85169, 9], [59677, 63781, 85779], .contexts [
        ⟨126915, false, false, [], []⟩,
        ⟨131873, false, false, [59677], []⟩
      ]⟩,
    ⟨[85169, 11], [59689, 95287], .contexts [
        ⟨126931, false, false, [], []⟩,
        ⟨128360, false, false, [], []⟩
      ]⟩,
    ⟨[85169, 13], [85167], .contexts [
        ⟨30372, false, false, [], []⟩,
        ⟨30547, false, false, [], []⟩
      ]⟩,
    ⟨[85169, 15], [85171], .contexts [
        ⟨30374, false, false, [], []⟩,
        ⟨30543, false, false, [], []⟩
      ]⟩,
    ⟨[85171, 1], [59591, 84317], .contexts [
        ⟨30378, false, false, [], []⟩,
        ⟨146561, false, false, [], []⟩
      ]⟩,
    ⟨[85171, 3], [97173], .contexts [
        ⟨146557, false, false, [], []⟩,
        ⟨146558, false, false, [], []⟩
      ]⟩,
    ⟨[85171, 5], [59765, 85179], .contexts [
        ⟨127004, false, false, [], []⟩,
        ⟨146568, false, false, [], []⟩
      ]⟩,
    ⟨[85171, 7], [60531, 83821], .contexts [
        ⟨127876, false, false, [], []⟩,
        ⟨146576, false, false, [], []⟩
      ]⟩,
    ⟨[85171, 9], [59599, 83883], .contexts [
        ⟨126838, false, false, [], []⟩,
        ⟨146581, false, false, [], []⟩
      ]⟩,
    ⟨[85171, 11], [59787, 84321], .contexts [
        ⟨127033, false, false, [], []⟩,
        ⟨146585, false, false, [], []⟩
      ]⟩,
    ⟨[85171, 13], [60321, 86465], .contexts [
        ⟨127622, false, false, [], []⟩,
        ⟨146590, false, false, [], []⟩
      ]⟩,
    ⟨[85171, 15], [85169], .contexts [
        ⟨30376, false, false, [], []⟩,
        ⟨30545, false, false, [], []⟩
      ]⟩,
    ⟨[85177, 1], [85179], .contexts [
        ⟨30388, false, false, [], []⟩,
        ⟨30539, false, false, [], []⟩
      ]⟩,
    ⟨[85177, 3], [65255, 91563], .contexts [
        ⟨133487, false, false, [], []⟩,
        ⟨133491, false, false, [], []⟩
      ]⟩,
    ⟨[85177, 5], [59589, 84317], .contexts [
        ⟨30386, false, false, [], []⟩,
        ⟨126825, false, false, [], []⟩
      ]⟩,
    ⟨[85177, 7], [59579, 88347], .contexts [
        ⟨126814, false, false, [], []⟩,
        ⟨133480, false, false, [], []⟩
      ]⟩,
    ⟨[85177, 9], [59759, 87625], .contexts [
        ⟨126995, false, false, [], []⟩,
        ⟨133687, false, false, [], []⟩
      ]⟩,
    ⟨[85177, 11], [59583, 86269], .contexts [
        ⟨126817, false, false, [], []⟩,
        ⟨133488, false, false, [], []⟩
      ]⟩,
    ⟨[85177, 13], [59577, 84453], .contexts [
        ⟨126809, true, false, [59574], [13]⟩,
        ⟨67798, false, false, [59574], []⟩,
        ⟨104663, false, false, [59574], []⟩,
        ⟨126811, true, false, [], [39555, 84453]⟩,
        ⟨126812, true, false, [], [84453]⟩
      ]⟩,
    ⟨[85177, 15], [59585, 90389], .contexts [
        ⟨126819, false, false, [], []⟩,
        ⟨133556, false, false, [], []⟩
      ]⟩,
    ⟨[85179, 1], [85177], .contexts [
        ⟨30390, false, false, [], []⟩,
        ⟨30541, false, false, [], []⟩
      ]⟩,
    ⟨[85179, 3], [73863, 96967], .contexts [
        ⟨144345, false, false, [], []⟩
      ]⟩,
    ⟨[85179, 5], [59763, 85171], .contexts [
        ⟨127002, false, false, [], []⟩,
        ⟨127869, false, false, [], []⟩
      ]⟩,
    ⟨[85179, 7], [59571, 94205], .contexts [
        ⟨126805, false, false, [], []⟩,
        ⟨127863, false, false, [], []⟩
      ]⟩,
    ⟨[85181], [59559, 83885], .contexts [
        ⟨126789, false, false, [], []⟩
      ]⟩,
    ⟨[85179, 9], [59559, 83885], .contexts [
        ⟨30392, false, false, [], []⟩,
        ⟨160218, false, false, [], []⟩
      ]⟩,
    ⟨[85179, 11], [59563, 86267], .contexts [
        ⟨126799, false, false, [], []⟩
      ]⟩,
    ⟨[85179, 13], [59569, 86463], .contexts [
        ⟨126803, false, false, [], []⟩
      ]⟩,
    ⟨[85179, 15], [59567, 90387], .contexts [
        ⟨126796, true, false, [59564], [15]⟩,
        ⟨121423, false, false, [59564], []⟩,
        ⟨121443, false, false, [59564], []⟩,
        ⟨126801, true, false, [], [90387]⟩
      ]⟩,
    ⟨[85183, 1], [85185], .contexts [
        ⟨30399, false, false, [], []⟩,
        ⟨30535, false, false, [], []⟩
      ]⟩,
    ⟨[85183, 3], [75473, 97197], .contexts [
        ⟨146986, true, false, [66830], [3]⟩,
        ⟨20, false, false, [66830, 97197], []⟩,
        ⟨146987, true, false, [], [97197]⟩
      ]⟩,
    ⟨[85183, 5], [58931, 89379], .contexts [
        ⟨125995, false, false, [], []⟩,
        ⟨143274, false, false, [], []⟩
      ]⟩,
    ⟨[85183, 7], [59803, 60871, 90269], .contexts [
        ⟨127046, false, false, [], []⟩,
        ⟨128282, false, false, [59803], []⟩
      ]⟩,
    ⟨[85183, 9], [96909], .contexts [
        ⟨143262, false, false, [], []⟩,
        ⟨143264, false, false, [], []⟩
      ]⟩,
    ⟨[85183, 11], [59559, 83885], .contexts [
        ⟨30397, false, false, [], []⟩,
        ⟨160218, false, false, [], []⟩
      ]⟩,
    ⟨[85183, 13], [59775, 85127], .contexts [
        ⟨127021, false, false, [], []⟩,
        ⟨143289, false, false, [], []⟩
      ]⟩,
    ⟨[85183, 15], [58901, 86141], .contexts [
        ⟨125963, false, false, [], []⟩,
        ⟨143294, false, false, [], []⟩
      ]⟩,
    ⟨[85185, 1], [85183], .contexts [
        ⟨30401, false, false, [], []⟩,
        ⟨30536, false, false, [], []⟩
      ]⟩,
    ⟨[85185, 3], [59959, 66811, 83747], .contexts [
        ⟨127226, false, false, [], []⟩,
        ⟨153670, false, false, [59959], []⟩
      ]⟩,
    ⟨[85185, 5], [56413, 89377], .contexts [
        ⟨123087, false, false, [], []⟩,
        ⟨127142, false, false, [], []⟩
      ]⟩,
    ⟨[85185, 7], [54017, 60885, 90271], .contexts [
        ⟨120217, true, false, [54014], [7]⟩,
        ⟨38, false, false, [54014, 91271], []⟩,
        ⟨120218, true, false, [], [91271]⟩,
        ⟨128300, false, false, [54017], []⟩
      ]⟩,
    ⟨[85185, 9], [52795, 83073], .contexts [
        ⟨118858, false, false, [], []⟩,
        ⟨143267, false, false, [], []⟩
      ]⟩,
    ⟨[85185, 11], [52797, 83887], .contexts [
        ⟨118854, true, false, [52784], [11]⟩,
        ⟨100148, false, false, [52784], []⟩,
        ⟨54191, false, false, [52784], []⟩,
        ⟨118837, true, false, [], [23609, 83887]⟩,
        ⟨118859, true, false, [], [83887]⟩
      ]⟩,
    ⟨[85185, 13], [85187], .contexts [
        ⟨30403, false, false, [], []⟩,
        ⟨30533, false, false, [], []⟩
      ]⟩,
    ⟨[96765], [55817, 65377, 90789], .contexts [
        ⟨122391, false, false, [], []⟩,
        ⟨135743, false, false, [], []⟩
      ]⟩,
    ⟨[85185, 15], [52783, 55817, 65377, 90789], .contexts [
        ⟨118854, true, false, [52784], [15]⟩,
        ⟨100151, false, false, [52784], []⟩,
        ⟨100152, false, false, [52784], []⟩,
        ⟨118841, true, false, [], [96765]⟩,
        ⟨160238, false, false, [52783], []⟩
      ]⟩,
    ⟨[85187, 1], [52783, 58137, 91155], .contexts [
        ⟨118842, false, false, [], []⟩,
        ⟨125051, false, false, [52783], []⟩
      ]⟩,
    ⟨[85187, 3], [52791, 86655], .contexts [
        ⟨118849, false, false, [], []⟩,
        ⟨127164, false, false, [], []⟩
      ]⟩,
    ⟨[85187, 5], [58157, 60871, 90269], .contexts [
        ⟨125057, false, false, [], []⟩,
        ⟨128282, false, false, [58157], []⟩
      ]⟩,
    ⟨[85187, 7], [52793, 92337], .contexts [
        ⟨118836, true, false, [52784], [7]⟩,
        ⟨100841, false, false, [52784], []⟩,
        ⟨118837, true, false, [], [36737, 92337]⟩,
        ⟨118850, true, false, [], [92337]⟩
      ]⟩,
    ⟨[85187, 9], [52787, 53217, 84801], .contexts [
        ⟨118845, false, false, [], []⟩,
        ⟨119373, false, false, [52787], []⟩
      ]⟩,
    ⟨[85187, 11], [52789, 85651], .contexts [
        ⟨118847, false, false, [], []⟩,
        ⟨127158, false, false, [], []⟩
      ]⟩,
    ⟨[85187, 13], [85185], .contexts [
        ⟨30405, false, false, [], []⟩,
        ⟨30535, false, false, [], []⟩
      ]⟩,
    ⟨[85187, 15], [85189], .contexts [
        ⟨30407, false, false, [], []⟩,
        ⟨30530, false, false, [], []⟩
      ]⟩,
    ⟨[85189, 1], [85191], .contexts [
        ⟨30411, false, false, [], []⟩,
        ⟨30528, false, false, [], []⟩
      ]⟩,
    ⟨[85189, 3], [65601, 93965], .contexts [
        ⟨133858, false, false, [], []⟩,
        ⟨138197, false, false, [], []⟩
      ]⟩,
    ⟨[85189, 5], [57585, 85443], .contexts [
        ⟨124476, false, false, [], []⟩,
        ⟨127129, false, false, [], []⟩
      ]⟩,
    ⟨[85189, 7], [52781, 57593, 86835], .contexts [
        ⟨118830, false, false, [], []⟩,
        ⟨124495, false, false, [52781], []⟩
      ]⟩,
    ⟨[85189, 9], [52779, 87377], .contexts [
        ⟨118828, false, false, [], []⟩,
        ⟨123095, false, false, [], []⟩
      ]⟩,
    ⟨[85189, 11], [52777, 85137], .contexts [
        ⟨118825, true, false, [52752], [11]⟩,
        ⟨75809, false, false, [52752], []⟩,
        ⟨115789, false, false, [52752], []⟩,
        ⟨118824, true, false, [], [44449, 85137]⟩,
        ⟨118826, true, false, [], [85137]⟩
      ]⟩,
    ⟨[85189, 13], [36413, 93901], .contexts [
        ⟨100061, false, false, [], []⟩,
        ⟨100052, false, false, [], []⟩
      ]⟩,
    ⟨[85189, 15], [85187], .contexts [
        ⟨30409, false, false, [], []⟩,
        ⟨30533, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2504. -/
def y322TCIndexRaw2504 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85191, 1], [85189], .contexts [
        ⟨30413, false, false, [], []⟩,
        ⟨30530, false, false, [], []⟩
      ]⟩,
    ⟨[85191, 3], [85193], .contexts [
        ⟨30415, false, false, [], []⟩,
        ⟨30526, false, false, [], []⟩
      ]⟩,
    ⟨[85191, 5], [52759, 85441], .contexts [
        ⟨118805, false, false, [], []⟩,
        ⟨127589, false, false, [], []⟩
      ]⟩,
    ⟨[85191, 7], [52697, 57493, 86837], .contexts [
        ⟨118730, false, false, [], []⟩,
        ⟨124380, false, false, [52697], []⟩
      ]⟩,
    ⟨[85191, 9], [53411, 92595], .contexts [
        ⟨119581, false, false, [], []⟩
      ]⟩,
    ⟨[85191, 11], [52751, 85135], .contexts [
        ⟨118799, false, false, [], []⟩
      ]⟩,
    ⟨[85191, 13], [36393, 83881], .contexts [
        ⟨100039, false, false, [], []⟩,
        ⟨100049, false, false, [], []⟩
      ]⟩,
    ⟨[85191, 15], [52757, 58137, 91155], .contexts [
        ⟨118801, true, false, [52752], [15]⟩,
        ⟨118685, false, false, [52752], []⟩,
        ⟨118802, true, false, [], [52655, 96759]⟩,
        ⟨118803, true, false, [], [96759]⟩,
        ⟨125051, false, false, [52757], []⟩
      ]⟩,
    ⟨[85193, 1], [36715, 53167, 91297], .contexts [
        ⟨100780, true, false, [36716], [1]⟩,
        ⟨8, false, false, [36716, 92335], []⟩,
        ⟨100684, true, false, [], [92335]⟩,
        ⟨119302, false, false, [36715], []⟩
      ]⟩,
    ⟨[85193, 3], [85191], .contexts [
        ⟨30417, false, false, [], []⟩,
        ⟨30528, false, false, [], []⟩
      ]⟩,
    ⟨[85193, 5], [44383, 85129], .contexts [
        ⟨30419, false, false, [], []⟩,
        ⟨109253, false, false, [], []⟩
      ]⟩,
    ⟨[85193, 7], [36781, 40667, 44431, 85133], .contexts [
        ⟨100836, true, false, [36778], [7]⟩,
        ⟨38, false, false, [36778, 89077], []⟩,
        ⟨100837, true, false, [], [89077]⟩,
        ⟨156290, false, false, [36781], []⟩
      ]⟩,
    ⟨[85193, 9], [45885, 55549, 86465], .contexts [
        ⟨111134, false, false, [], []⟩,
        ⟨122094, false, false, [45885], []⟩
      ]⟩,
    ⟨[85193, 11], [36715, 52731, 89381], .contexts [
        ⟨100847, false, false, [], []⟩,
        ⟨118787, false, false, [36715], []⟩
      ]⟩,
    ⟨[85193, 13], [36393, 83883], .contexts [
        ⟨100028, false, false, [], []⟩,
        ⟨100021, false, false, [], []⟩
      ]⟩,
    ⟨[85193, 15], [36461, 36769, 89277], .contexts [
        ⟨100216, false, false, [], []⟩,
        ⟨100818, false, false, [36461], []⟩
      ]⟩,
    ⟨[85201, 1], [39347, 83817], .contexts [
        ⟨30435, false, false, [], []⟩,
        ⟨104412, false, false, [], []⟩
      ]⟩,
    ⟨[85201, 3], [23147, 85811], .contexts [
        ⟨51771, false, false, [], []⟩
      ]⟩,
    ⟨[85201, 5], [23909, 55585, 86473], .contexts [
        ⟨55351, false, false, [], []⟩,
        ⟨122131, false, false, [23909], []⟩
      ]⟩,
    ⟨[89695], [37669, 39477, 84321], .contexts [
        ⟨102483, false, false, [], []⟩,
        ⟨104573, false, false, [37669], []⟩
      ]⟩,
    ⟨[85201, 7], [24289, 37669, 39477, 84321], .contexts [
        ⟨57208, false, false, [], []⟩,
        ⟨160275, false, false, [24289], []⟩
      ]⟩,
    ⟨[90597], [38585, 57711, 88515], .contexts [
        ⟨103558, false, false, [], []⟩,
        ⟨124604, false, false, [38585], []⟩
      ]⟩,
    ⟨[85201, 9], [25269, 38585, 57711, 88515], .contexts [
        ⟨61730, false, false, [], []⟩,
        ⟨160277, false, false, [25269], []⟩
      ]⟩,
    ⟨[85201, 11], [39363, 83821], .contexts [
        ⟨30433, false, false, [], []⟩,
        ⟨104439, false, false, [], []⟩
      ]⟩,
    ⟨[85201, 13], [23137, 40645, 85657], .contexts [
        ⟨51726, false, false, [], []⟩,
        ⟨105678, false, false, [23137], []⟩
      ]⟩,
    ⟨[85201, 15], [45137, 71607, 95793], .contexts [
        ⟨110176, true, false, [45134], [15]⟩,
        ⟨1, false, false, [45134, 96033], []⟩,
        ⟨110177, true, false, [], [96033]⟩,
        ⟨140497, false, false, [45137], []⟩
      ]⟩,
    ⟨[85207, 1], [85209], .contexts [
        ⟨30447, false, false, [], []⟩,
        ⟨30511, false, false, [], []⟩
      ]⟩,
    ⟨[85207, 3], [19339, 85207], .contexts [
        ⟨38017, false, false, [], []⟩,
        ⟨38027, false, false, [], []⟩
      ]⟩,
    ⟨[85207, 5], [32929, 40613, 85669], .contexts [
        ⟨89780, false, false, [], []⟩,
        ⟨105642, false, false, [32929], []⟩
      ]⟩,
    ⟨[85207, 7], [23141, 83579], .contexts [
        ⟨51732, true, false, [23142], [7]⟩,
        ⟨38, false, false, [23142, 83579], []⟩,
        ⟨51730, false, true, [], [83579]⟩,
        ⟨51729, false, false, [], []⟩
      ]⟩,
    ⟨[85207, 9], [23121, 84483], .contexts [
        ⟨51674, false, false, [], []⟩,
        ⟨51671, false, false, [], []⟩
      ]⟩,
    ⟨[85207, 11], [23119, 88217], .contexts [
        ⟨51685, false, false, [], []⟩,
        ⟨51681, false, false, [], []⟩
      ]⟩,
    ⟨[85207, 13], [23941, 40879, 84119], .contexts [
        ⟨55421, false, false, [], []⟩,
        ⟨105843, false, false, [23941], []⟩
      ]⟩,
    ⟨[85207, 15], [39823, 84459], .contexts [
        ⟨30445, false, false, [], []⟩,
        ⟨104920, false, false, [], []⟩
      ]⟩,
    ⟨[85209, 1], [85207], .contexts [
        ⟨30449, false, false, [], []⟩,
        ⟨30514, false, false, [], []⟩
      ]⟩,
    ⟨[85209, 3], [85211], .contexts [
        ⟨30451, false, false, [], []⟩,
        ⟨30509, false, false, [], []⟩
      ]⟩,
    ⟨[85209, 5], [32883, 40613, 85671], .contexts [
        ⟨89716, false, false, [], []⟩,
        ⟨105634, false, false, [32883], []⟩
      ]⟩,
    ⟨[85209, 7], [39857, 42507, 86279], .contexts [
        ⟨104945, true, false, [39854], [7]⟩,
        ⟨98889, true, false, [39854, 36056], [7]⟩,
        ⟨38, false, false, [39854, 36056, 93395], []⟩,
        ⟨98887, false, true, [39854], [93395]⟩,
        ⟨104943, true, false, [], [36055, 93395]⟩,
        ⟨104948, true, false, [], [93395]⟩,
        ⟨110605, false, false, [39857], []⟩
      ]⟩,
    ⟨[85209, 9], [23119, 88211], .contexts [
        ⟨51634, false, false, [], []⟩,
        ⟨51667, false, false, [], []⟩
      ]⟩,
    ⟨[85209, 11], [23119, 88215], .contexts [
        ⟨51635, false, false, [], []⟩,
        ⟨51678, false, false, [], []⟩
      ]⟩,
    ⟨[85209, 13], [39853, 71209, 90923], .contexts [
        ⟨104947, false, false, [], []⟩,
        ⟨140051, false, false, [39853], []⟩
      ]⟩,
    ⟨[85209, 15], [23107, 39863, 84461], .contexts [
        ⟨51626, false, false, [], []⟩,
        ⟨104960, false, false, [23107], []⟩
      ]⟩,
    ⟨[85211, 1], [19341, 85211], .contexts [
        ⟨38002, false, false, [], []⟩,
        ⟨37996, false, false, [], []⟩
      ]⟩,
    ⟨[85211, 3], [85209], .contexts [
        ⟨30453, false, false, [], []⟩,
        ⟨30511, false, false, [], []⟩
      ]⟩,
    ⟨[85211, 5], [85213], .contexts [
        ⟨30455, false, false, [], []⟩,
        ⟨30507, false, false, [], []⟩
      ]⟩,
    ⟨[85211, 7], [35209, 96169], .contexts [
        ⟨96368, true, false, [35206], [7]⟩,
        ⟨38, false, false, [35206, 96169], []⟩,
        ⟨96369, true, false, [], [96169]⟩
      ]⟩,
    ⟨[85211, 9], [23495, 46227, 87507], .contexts [
        ⟨53673, false, false, [], []⟩,
        ⟨111533, false, false, [23495], []⟩
      ]⟩,
    ⟨[85211, 11], [88977], .contexts [
        ⟨53676, false, false, [], []⟩,
        ⟨53679, false, false, [], []⟩
      ]⟩,
    ⟨[85211, 13], [20939, 47189, 86509], .contexts [
        ⟨43128, false, false, [], []⟩,
        ⟨112564, false, false, [20939], []⟩
      ]⟩,
    ⟨[85211, 15], [23107, 85111], .contexts [
        ⟨51580, false, false, [], []⟩,
        ⟨53696, false, false, [], []⟩
      ]⟩,
    ⟨[85215], [19341, 85213], .contexts [
        ⟨37985, false, false, [], []⟩
      ]⟩,
    ⟨[85213, 1], [19341, 85213], .contexts [
        ⟨30459, false, false, [], []⟩,
        ⟨160306, false, false, [], []⟩
      ]⟩,
    ⟨[85213, 3], [23025, 88591], .contexts [
        ⟨51401, false, false, [], []⟩,
        ⟨96982, false, false, [], []⟩
      ]⟩,
    ⟨[85213, 5], [85211], .contexts [
        ⟨30457, false, false, [], []⟩,
        ⟨30509, false, false, [], []⟩
      ]⟩,
    ⟨[85213, 7], [18011, 85213], .contexts [
        ⟨30828, false, false, [], []⟩,
        ⟨51467, false, false, [], []⟩
      ]⟩,
    ⟨[85213, 9], [19339, 85217], .contexts [
        ⟨37976, false, false, [], []⟩,
        ⟨51447, false, false, [], []⟩
      ]⟩,
    ⟨[96281], [43809, 92521], .contexts [
        ⟨108605, false, false, [], []⟩
      ]⟩,
    ⟨[85213, 11], [43809, 92521], .contexts [
        ⟨96978, false, false, [], []⟩,
        ⟨160312, false, false, [], []⟩
      ]⟩,
    ⟨[85213, 13], [19343, 82969], .contexts [
        ⟨37984, false, false, [], []⟩,
        ⟨38005, false, false, [], []⟩
      ]⟩,
    ⟨[85213, 15], [23031, 88585], .contexts [
        ⟨51410, false, false, [], []⟩,
        ⟨51451, false, false, [], []⟩
      ]⟩,
    ⟨[85217, 1], [19335, 86571], .contexts [
        ⟨37954, false, false, [], []⟩
      ]⟩,
    ⟨[85217, 3], [19689, 87033], .contexts [
        ⟨40008, true, false, [19686], [3]⟩,
        ⟨20, false, false, [19686, 87033], []⟩,
        ⟨40009, true, false, [], [87033]⟩
      ]⟩,
    ⟨[85217, 5], [23487, 46227, 87507], .contexts [
        ⟨53651, true, false, [23484], [5]⟩,
        ⟨28, false, false, [23484, 88975], []⟩,
        ⟨53652, true, false, [], [88975]⟩,
        ⟨111533, false, false, [23487], []⟩
      ]⟩,
    ⟨[85217, 7], [18011, 85217], .contexts [
        ⟨30792, false, false, [], []⟩,
        ⟨30813, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2505. -/
def y322TCIndexRaw2505 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85217, 9], [19341, 85213], .contexts [
        ⟨30464, false, false, [], []⟩,
        ⟨160306, false, false, [], []⟩
      ]⟩,
    ⟨[85217, 11], [85219], .contexts [
        ⟨30466, false, false, [], []⟩,
        ⟨30500, false, false, [], []⟩
      ]⟩,
    ⟨[85217, 13], [17977, 82971], .contexts [
        ⟨30759, false, false, [], []⟩,
        ⟨30793, false, false, [], []⟩
      ]⟩,
    ⟨[85217, 15], [19689, 87571], .contexts [
        ⟨44250, false, false, [], []⟩
      ]⟩,
    ⟨[85219, 1], [85221], .contexts [
        ⟨30470, false, false, [], []⟩,
        ⟨30499, false, false, [], []⟩
      ]⟩,
    ⟨[85219, 3], [18003, 83783], .contexts [
        ⟨30772, false, false, [], []⟩,
        ⟨30802, false, false, [], []⟩
      ]⟩,
    ⟨[85219, 5], [19569, 86923], .contexts [
        ⟨39509, false, false, [], []⟩
      ]⟩,
    ⟨[85219, 7], [17999, 85219], .contexts [
        ⟨30755, false, false, [], []⟩,
        ⟨30785, false, false, [], []⟩
      ]⟩,
    ⟨[85219, 9], [18007, 83903], .contexts [
        ⟨30782, false, false, [], []⟩
      ]⟩,
    ⟨[85219, 11], [85217], .contexts [
        ⟨30468, false, false, [], []⟩,
        ⟨30503, false, false, [], []⟩
      ]⟩,
    ⟨[85219, 13], [17977, 82973], .contexts [
        ⟨30728, false, false, [], []⟩,
        ⟨30805, false, false, [], []⟩
      ]⟩,
    ⟨[85219, 15], [18309, 42621, 85521], .contexts [
        ⟨32785, false, false, [], []⟩,
        ⟨107458, false, false, [18309], []⟩
      ]⟩,
    ⟨[85221, 1], [85219], .contexts [
        ⟨30472, false, false, [], []⟩,
        ⟨30500, false, false, [], []⟩
      ]⟩,
    ⟨[85221, 3], [17981, 83367], .contexts [
        ⟨30736, false, false, [], []⟩
      ]⟩,
    ⟨[85221, 5], [17981, 87201], .contexts [
        ⟨40320, true, false, [17978], [5]⟩,
        ⟨28, false, false, [17978, 87201], []⟩,
        ⟨30735, true, false, [], [87201]⟩
      ]⟩,
    ⟨[85221, 7], [17987, 85221], .contexts [
        ⟨30737, false, false, [17982], [85221, 7]⟩,
        ⟨30695, true, false, [17982, 17767], [7]⟩,
        ⟨29438, true, false, [17982], [13, 7]⟩,
        ⟨518, false, false, [17982, 84963], []⟩,
        ⟨30729, false, false, [17982], []⟩,
        ⟨30722, false, false, [17982], []⟩,
        ⟨30731, false, false, [17982, 17963], []⟩,
        ⟨30738, true, false, [], [17963, 85221]⟩,
        ⟨30739, true, false, [], [85221]⟩
      ]⟩,
    ⟨[85221, 9], [17995, 83911], .contexts [
        ⟨30747, false, false, [], []⟩
      ]⟩,
    ⟨[85221, 11], [17961, 86571], .contexts [
        ⟨37970, true, false, [17962], [11]⟩,
        ⟨53, false, false, [17962, 86571], []⟩,
        ⟨30692, true, false, [], [86571]⟩
      ]⟩,
    ⟨[85221, 13], [17961, 41043, 84873], .contexts [
        ⟨30474, false, false, [], []⟩,
        ⟨30693, false, false, [], []⟩,
        ⟨106012, false, false, [17961], []⟩
      ]⟩,
    ⟨[85221, 15], [17981, 42271, 86355], .contexts [
        ⟨44705, true, false, [17978], [15]⟩,
        ⟨1, false, false, [17978, 87573], []⟩,
        ⟨30735, true, false, [], [87573]⟩,
        ⟨107153, false, false, [17981], []⟩
      ]⟩,
    ⟨[85229, 1], [17929, 85233], .contexts [
        ⟨30679, false, false, [], []⟩
      ]⟩,
    ⟨[85229, 3], [17957, 82979], .contexts [
        ⟨30485, false, false, [], []⟩,
        ⟨30683, false, false, [], []⟩
      ]⟩,
    ⟨[85231], [17931, 85229], .contexts [
        ⟨30680, false, false, [], []⟩
      ]⟩,
    ⟨[85229, 5], [17931, 85229], .contexts [
        ⟨30487, false, false, [], []⟩,
        ⟨160342, false, false, [], []⟩
      ]⟩,
    ⟨[85229, 7], [17969, 85229], .contexts [
        ⟨30698, false, false, [17964], [85229, 7]⟩,
        ⟨30681, true, false, [17964, 17937], [7]⟩,
        ⟨30493, true, false, [17964, 17937], [7]⟩,
        ⟨30697, true, false, [17964], [1, 7]⟩,
        ⟨30697, true, false, [17964], [1, 7]⟩,
        ⟨30696, true, false, [17964], [1, 7]⟩,
        ⟨30644, true, false, [17964], [1, 7]⟩,
        ⟨30641, true, false, [17964], [1, 7]⟩,
        ⟨502, false, false, [17964, 85233], []⟩,
        ⟨30700, false, false, [17964], []⟩,
        ⟨30699, false, false, [17964], []⟩,
        ⟨30656, false, false, [17964, 17931], []⟩,
        ⟨30701, true, false, [], [17931, 85229]⟩,
        ⟨30702, true, false, [], [85229]⟩
      ]⟩,
    ⟨[85229, 9], [17945, 85229], .contexts [
        ⟨30659, false, false, [], []⟩,
        ⟨33714, false, false, [], []⟩
      ]⟩,
    ⟨[85229, 11], [17973, 85099], .contexts [
        ⟨30709, false, false, [], []⟩
      ]⟩,
    ⟨[85845], [18443, 18461, 18481, 85839], .contexts [
        ⟨33723, false, false, [], []⟩,
        ⟨33734, false, false, [], []⟩,
        ⟨33749, false, false, [18443, 18461], []⟩
      ]⟩,
    ⟨[85229, 13], [18433, 18443, 18461, 18481, 85839], .contexts [
        ⟨33701, false, false, [], []⟩,
        ⟨160347, false, false, [18433], []⟩
      ]⟩,
    ⟨[85229, 15], [18243, 85487], .contexts [
        ⟨32338, false, false, [], []⟩
      ]⟩,
    ⟨[85233, 1], [17931, 85229], .contexts [
        ⟨30493, false, false, [], []⟩,
        ⟨160342, false, false, [], []⟩
      ]⟩,
    ⟨[85233, 3], [17919, 82857], .contexts [
        ⟨30630, true, false, [17920], [3]⟩,
        ⟨20, false, false, [17920, 82857], []⟩,
        ⟨30631, true, false, [], [82857]⟩,
        ⟨30623, false, false, [], []⟩
      ]⟩,
    ⟨[85233, 5], [17931, 85233], .contexts [
        ⟨30638, false, false, [], []⟩,
        ⟨30673, false, false, [], []⟩
      ]⟩,
    ⟨[85233, 7], [17937, 85233], .contexts [
        ⟨30644, false, false, [], []⟩,
        ⟨30696, false, false, [], []⟩
      ]⟩,
    ⟨[85233, 9], [17919, 84855], .contexts [
        ⟨30610, false, false, [], []⟩,
        ⟨30615, false, false, [], []⟩
      ]⟩,
    ⟨[85233, 11], [17953, 85101], .contexts [
        ⟨30671, false, false, [], []⟩,
        ⟨30703, false, false, [], []⟩
      ]⟩,
    ⟨[85233, 13], [17943, 85233], .contexts [
        ⟨30649, false, false, [], []⟩
      ]⟩,
    ⟨[85233, 15], [17919, 82989], .contexts [
        ⟨30653, false, false, [], []⟩,
        ⟨30650, false, false, [], []⟩
      ]⟩,
    ⟨[85235, 1], [89209], .contexts [
        ⟨54831, false, false, [], []⟩,
        ⟨54833, false, false, [], []⟩
      ]⟩,
    ⟨[85235, 3], [83933], .contexts [
        ⟨30835, false, false, [], []⟩,
        ⟨23818, false, false, [], []⟩
      ]⟩,
    ⟨[85235, 5], [85237], .contexts [
        ⟨30856, false, false, [], []⟩,
        ⟨30858, false, false, [], []⟩
      ]⟩,
    ⟨[85235, 7], [1673, 85235], .contexts [
        ⟨30843, false, false, [], []⟩,
        ⟨30839, false, false, [], []⟩
      ]⟩,
    ⟨[85235, 9], [72855, 96873], .contexts [
        ⟨142648, true, false, [22944], [9]⟩,
        ⟨46, false, false, [22944, 96873], []⟩,
        ⟨142649, true, false, [], [96873]⟩
      ]⟩,
    ⟨[85235, 11], [16699, 83479], .contexts [
        ⟨30849, false, false, [], []⟩,
        ⟨30846, false, false, [], []⟩
      ]⟩,
    ⟨[85235, 13], [19505, 86805], .contexts [
        ⟨39066, false, false, [], []⟩,
        ⟨54845, false, false, [], []⟩
      ]⟩,
    ⟨[85235, 15], [863, 85235], .contexts [
        ⟨30854, false, false, [], []⟩,
        ⟨30851, false, false, [], []⟩
      ]⟩,
    ⟨[85237, 1], [85239], .contexts [
        ⟨30883, false, false, [], []⟩,
        ⟨30886, false, false, [], []⟩
      ]⟩,
    ⟨[85237, 3], [18021, 83143], .contexts [
        ⟨30867, false, false, [], []⟩,
        ⟨30876, false, false, [], []⟩
      ]⟩,
    ⟨[85237, 5], [85235], .contexts [
        ⟨30857, false, false, [], []⟩,
        ⟨30836, false, false, [], []⟩
      ]⟩,
    ⟨[85237, 7], [18021, 84967], .contexts [
        ⟨30881, true, false, [18022], [7]⟩,
        ⟨38, false, false, [18022, 84967], []⟩,
        ⟨30868, false, true, [], [84967]⟩,
        ⟨30879, false, false, [], []⟩
      ]⟩,
    ⟨[85237, 9], [22925, 22937, 88603], .contexts [
        ⟨51199, false, false, [], []⟩,
        ⟨51219, false, false, [22925], []⟩
      ]⟩,
    ⟨[85237, 11], [16699, 20541, 85245], .contexts [
        ⟨34549, true, false, [16700], [11]⟩,
        ⟨53, false, false, [16700, 85977], []⟩,
        ⟨34550, true, false, [], [85977]⟩,
        ⟨42210, false, false, [16699], []⟩
      ]⟩,
    ⟨[85237, 13], [19505, 42573, 86369], .contexts [
        ⟨39044, false, false, [], []⟩,
        ⟨107413, false, false, [19505], []⟩
      ]⟩,
    ⟨[85237, 15], [863, 85237], .contexts [
        ⟨30875, false, false, [], []⟩,
        ⟨30871, false, false, [], []⟩
      ]⟩,
    ⟨[85239, 1], [85237], .contexts [
        ⟨30884, false, false, [], []⟩,
        ⟨30858, false, false, [], []⟩
      ]⟩,
    ⟨[85239, 3], [18027, 85239], .contexts [
        ⟨30896, false, false, [], []⟩,
        ⟨30891, false, false, [], []⟩
      ]⟩,
    ⟨[85239, 5], [89209], .contexts [
        ⟨54838, false, false, [], []⟩,
        ⟨54833, false, false, [], []⟩
      ]⟩,
    ⟨[85239, 7], [27553, 92267], .contexts [
        ⟨70903, false, false, [], []⟩
      ]⟩,
    ⟨[85241], [20549, 85239], .contexts [
        ⟨42201, false, false, [], []⟩
      ]⟩,
    ⟨[85239, 9], [20549, 85239], .contexts [
        ⟨30902, false, false, [], []⟩,
        ⟨160378, false, false, [], []⟩
      ]⟩,
    ⟨[85239, 11], [16699, 20541, 85243], .contexts [
        ⟨34584, false, false, [], []⟩,
        ⟨42191, false, false, [16699], []⟩
      ]⟩,
    ⟨[85239, 13], [28541, 47689, 84033], .contexts [
        ⟨74368, false, false, [], []⟩,
        ⟨113074, false, false, [28541], []⟩
      ]⟩,
    ⟨[85239, 15], [863, 85239], .contexts [
        ⟨30900, false, false, [], []⟩,
        ⟨30897, false, false, [], []⟩
      ]⟩,
    ⟨[85243, 1], [85245], .contexts [
        ⟨30930, false, false, [], []⟩,
        ⟨30932, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2506. -/
def y322TCIndexRaw2506 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85243, 3], [18027, 85243], .contexts [
        ⟨30923, false, false, [], []⟩,
        ⟨30920, false, false, [], []⟩
      ]⟩,
    ⟨[85243, 5], [20545, 83475], .contexts [
        ⟨42195, false, false, [], []⟩
      ]⟩,
    ⟨[85243, 7], [20547, 84971], .contexts [
        ⟨42198, false, false, [], []⟩
      ]⟩,
    ⟨[85243, 9], [16699, 20539, 85981], .contexts [
        ⟨34626, false, false, [], []⟩,
        ⟨42182, false, false, [16699], []⟩
      ]⟩,
    ⟨[85243, 11], [20549, 85239], .contexts [
        ⟨30916, false, false, [], []⟩,
        ⟨160378, false, false, [], []⟩
      ]⟩,
    ⟨[85243, 13], [21871, 47673, 84031], .contexts [
        ⟨46996, false, false, [], []⟩,
        ⟨113062, false, false, [21871], []⟩
      ]⟩,
    ⟨[85243, 15], [863, 85243], .contexts [
        ⟨30928, false, false, [], []⟩,
        ⟨30924, false, false, [], []⟩
      ]⟩,
    ⟨[85245, 1], [85243], .contexts [
        ⟨30931, false, false, [], []⟩,
        ⟨30917, false, false, [], []⟩
      ]⟩,
    ⟨[85245, 3], [20547, 83151], .contexts [
        ⟨42209, false, false, [], []⟩,
        ⟨42394, false, false, [], []⟩
      ]⟩,
    ⟨[85245, 5], [20543, 83479], .contexts [
        ⟨42208, false, false, [], []⟩,
        ⟨42404, false, false, [], []⟩
      ]⟩,
    ⟨[85245, 7], [20547, 84969], .contexts [
        ⟨42206, true, false, [20540], [7]⟩,
        ⟨34562, false, false, [20540], []⟩,
        ⟨34558, false, false, [20540], []⟩,
        ⟨42197, true, false, [], [84969]⟩
      ]⟩,
    ⟨[85245, 9], [18679, 85245], .contexts [
        ⟨34631, false, false, [], []⟩,
        ⟨34632, false, false, [], []⟩
      ]⟩,
    ⟨[85245, 11], [20549, 85237], .contexts [
        ⟨42212, false, false, [], []⟩,
        ⟨42411, false, false, [], []⟩
      ]⟩,
    ⟨[85245, 13], [85247], .contexts [
        ⟨30939, false, false, [], []⟩,
        ⟨31154, false, false, [], []⟩
      ]⟩,
    ⟨[85245, 15], [863, 85245], .contexts [
        ⟨30937, false, false, [], []⟩,
        ⟨30934, false, false, [], []⟩
      ]⟩,
    ⟨[92045], [40707, 42555, 86363], .contexts [
        ⟨156122, false, false, [], []⟩
      ]⟩,
    ⟨[85247, 1], [40707, 42555, 86363], .contexts [
        ⟨69190, false, false, [], []⟩,
        ⟨160399, false, false, [], []⟩
      ]⟩,
    ⟨[85247, 3], [20637, 82833], .contexts [
        ⟨42401, false, false, [], []⟩,
        ⟨42618, false, false, [], []⟩
      ]⟩,
    ⟨[85247, 5], [20641, 83785], .contexts [
        ⟨42409, false, false, [], []⟩,
        ⟨69200, false, false, [], []⟩
      ]⟩,
    ⟨[85247, 7], [20637, 90871], .contexts [
        ⟨63383, false, false, [], []⟩,
        ⟨69203, false, false, [], []⟩
      ]⟩,
    ⟨[85247, 9], [18681, 85247], .contexts [
        ⟨34639, false, false, [], []⟩,
        ⟨34641, false, false, [], []⟩
      ]⟩,
    ⟨[85247, 11], [20645, 42573, 86369], .contexts [
        ⟨42419, false, false, [], []⟩,
        ⟨107413, false, false, [20645], []⟩
      ]⟩,
    ⟨[85247, 13], [85245], .contexts [
        ⟨30940, false, false, [], []⟩,
        ⟨30932, false, false, [], []⟩
      ]⟩,
    ⟨[85247, 15], [85249], .contexts [
        ⟨30942, false, false, [], []⟩,
        ⟨30945, false, false, [], []⟩
      ]⟩,
    ⟨[85249, 1], [85251], .contexts [
        ⟨30953, false, false, [], []⟩,
        ⟨31152, false, false, [], []⟩
      ]⟩,
    ⟨[85249, 3], [20637, 82829], .contexts [
        ⟨42627, true, false, [20638], [3]⟩,
        ⟨36018, false, false, [20638], []⟩,
        ⟨17180, false, false, [20638], []⟩,
        ⟨42630, true, false, [], [82829]⟩,
        ⟨42621, false, false, [], []⟩
      ]⟩,
    ⟨[85249, 5], [20637, 40451, 40491, 85689], .contexts [
        ⟨42627, true, false, [20638], [5]⟩,
        ⟨36012, false, false, [20638], []⟩,
        ⟨35930, false, false, [20638], []⟩,
        ⟨42630, true, false, [], [86225]⟩,
        ⟨152941, false, false, [20637], []⟩
      ]⟩,
    ⟨[85249, 7], [20637, 88341], .contexts [
        ⟨49946, true, false, [20638], [7]⟩,
        ⟨38, false, false, [20638, 88341], []⟩,
        ⟨42625, true, false, [], [88341]⟩
      ]⟩,
    ⟨[85249, 9], [18679, 85249], .contexts [
        ⟨30942, true, false, [], [9]⟩,
        ⟨34642, true, false, [18680], [15, 9]⟩,
        ⟨34642, true, false, [18680], [15, 9]⟩,
        ⟨34641, true, false, [18680], [15, 9]⟩,
        ⟨34640, true, false, [18680], [15, 9]⟩,
        ⟨34635, true, false, [18680], [15, 9]⟩,
        ⟨935, false, false, [18680, 85247], []⟩,
        ⟨10, false, false, [18680, 85247], []⟩,
        ⟨30947, false, false, [18680], []⟩,
        ⟨30951, false, false, [18680], []⟩,
        ⟨34643, true, false, [], [85249]⟩,
        ⟨34643, true, false, [], [85249]⟩,
        ⟨34637, false, true, [], [85249]⟩
      ]⟩,
    ⟨[85249, 11], [20637, 82877], .contexts [
        ⟨42627, true, false, [20638], [11]⟩,
        ⟨36027, false, false, [20638], []⟩,
        ⟨17791, false, false, [20638], []⟩,
        ⟨42630, true, false, [], [82877]⟩
      ]⟩,
    ⟨[85249, 13], [863, 85249], .contexts [
        ⟨30947, true, false, [], [13]⟩,
        ⟨259, false, false, [85247], []⟩,
        ⟨262, false, false, [85247], []⟩,
        ⟨30949, false, false, [], [15, 13, 15]⟩,
        ⟨30937, false, false, [], [13, 15]⟩,
        ⟨30934, false, false, [], [13, 15]⟩,
        ⟨30935, false, false, [], [13, 15]⟩,
        ⟨30935, false, false, [], [13, 15]⟩,
        ⟨30939, false, false, [863], [15]⟩,
        ⟨30942, false, false, [863], []⟩,
        ⟨30950, false, false, [], []⟩,
        ⟨30951, false, false, [863], []⟩,
        ⟨2500, true, false, [], [85249]⟩,
        ⟨30950, false, false, [], []⟩
      ]⟩,
    ⟨[85249, 15], [85247], .contexts [
        ⟨30944, false, false, [], []⟩,
        ⟨31154, false, false, [], []⟩
      ]⟩,
    ⟨[85251, 1], [85249], .contexts [
        ⟨30954, false, false, [], []⟩,
        ⟨30945, false, false, [], []⟩
      ]⟩,
    ⟨[85251, 3], [85253], .contexts [
        ⟨30956, false, false, [], []⟩,
        ⟨31151, false, false, [], []⟩
      ]⟩,
    ⟨[85251, 5], [20741, 83781], .contexts [
        ⟨42640, false, false, [], []⟩
      ]⟩,
    ⟨[85251, 7], [26375, 91621], .contexts [
        ⟨66776, false, false, [], []⟩
      ]⟩,
    ⟨[85251, 9], [20637, 86231], .contexts [
        ⟨42641, false, false, [], []⟩,
        ⟨69441, false, false, [], []⟩
      ]⟩,
    ⟨[85251, 11], [20637, 82879], .contexts [
        ⟨42638, true, false, [20638], [11]⟩,
        ⟨36053, false, false, [20638], []⟩,
        ⟨18100, false, false, [20638], []⟩,
        ⟨42630, true, false, [], [82879]⟩
      ]⟩,
    ⟨[85251, 13], [27059, 85871], .contexts [
        ⟨69229, false, false, [], []⟩,
        ⟨69223, false, false, [], []⟩
      ]⟩,
    ⟨[85251, 15], [40707, 42555, 86363], .contexts [
        ⟨69220, false, false, [], []⟩,
        ⟨160399, false, false, [], []⟩
      ]⟩,
    ⟨[85253, 1], [20743, 85615], .contexts [
        ⟨42646, true, false, [20744], [1]⟩,
        ⟨32879, false, false, [20744], []⟩,
        ⟨32851, false, false, [20744], []⟩,
        ⟨42649, true, false, [], [85615]⟩
      ]⟩,
    ⟨[85253, 3], [85251], .contexts [
        ⟨30958, false, false, [], []⟩,
        ⟨31152, false, false, [], []⟩
      ]⟩,
    ⟨[85253, 5], [85255], .contexts [
        ⟨30960, false, false, [], []⟩,
        ⟨31150, false, false, [], []⟩
      ]⟩,
    ⟨[85253, 7], [20747, 20779, 85263], .contexts [
        ⟨42652, false, false, [], []⟩,
        ⟨48767, false, false, [20747], []⟩
      ]⟩,
    ⟨[85253, 9], [20743, 85619], .contexts [
        ⟨42650, false, false, [], []⟩
      ]⟩,
    ⟨[85253, 11], [20743, 83377], .contexts [
        ⟨42646, true, false, [20744], [11]⟩,
        ⟨32884, false, false, [20744], []⟩,
        ⟨21086, false, false, [20744], []⟩,
        ⟨42649, true, false, [], [83377]⟩
      ]⟩,
    ⟨[85253, 13], [22347, 27069, 85875], .contexts [
        ⟨48754, false, false, [], []⟩,
        ⟨69257, false, false, [22347], []⟩
      ]⟩,
    ⟨[88201], [39669, 40577, 85675], .contexts [
        ⟨104788, false, false, [], []⟩,
        ⟨105613, false, false, [], []⟩
      ]⟩,
    ⟨[85253, 15], [22347, 39669, 40577, 85675], .contexts [
        ⟨48756, false, false, [], []⟩,
        ⟨160431, false, false, [22347], []⟩
      ]⟩,
    ⟨[85255, 1], [85257], .contexts [
        ⟨30964, false, false, [], []⟩,
        ⟨31149, false, false, [], []⟩
      ]⟩,
    ⟨[85255, 3], [22737, 88469], .contexts [
        ⟨50400, false, false, [], []⟩
      ]⟩,
    ⟨[85255, 5], [85253], .contexts [
        ⟨30962, false, false, [], []⟩,
        ⟨31151, false, false, [], []⟩
      ]⟩,
    ⟨[85255, 7], [21753, 47141, 86523], .contexts [
        ⟨46245, true, false, [21750], [7]⟩,
        ⟨38, false, false, [21750, 87799], []⟩,
        ⟨46246, true, false, [], [87799]⟩,
        ⟨112524, false, false, [21753], []⟩
      ]⟩,
    ⟨[85255, 9], [20757, 86791], .contexts [
        ⟨42658, true, false, [20750], [9]⟩,
        ⟨40383, false, false, [20750], []⟩,
        ⟨40430, false, false, [20750], []⟩,
        ⟨42659, true, false, [], [19875, 86791]⟩,
        ⟨42667, true, false, [], [86791]⟩
      ]⟩,
    ⟨[85255, 11], [20755, 85495], .contexts [
        ⟨42666, false, false, [], []⟩
      ]⟩,
    ⟨[85255, 13], [20753, 27079, 85877], .contexts [
        ⟨42663, false, false, [], []⟩,
        ⟨69277, false, false, [20753], []⟩
      ]⟩,
    ⟨[85255, 15], [20749, 41383, 85389], .contexts [
        ⟨42658, true, false, [20750], [15]⟩,
        ⟨35692, false, false, [20750], []⟩,
        ⟨42664, false, false, [20750], []⟩,
        ⟨42660, true, false, [], [86221]⟩,
        ⟨42661, true, false, [], [86221]⟩,
        ⟨106307, false, false, [20749], []⟩
      ]⟩,
    ⟨[85257, 1], [85255], .contexts [
        ⟨30966, false, false, [], []⟩,
        ⟨31150, false, false, [], []⟩
      ]⟩,
    ⟨[85257, 3], [20759, 79195], .contexts [
        ⟨42673, true, false, [20760], [3]⟩,
        ⟨32833, false, false, [20760], []⟩,
        ⟨6305, false, false, [20760], []⟩,
        ⟨42676, true, false, [], [79195]⟩
      ]⟩,
    ⟨[85257, 5], [20759, 85615], .contexts [
        ⟨42678, false, false, [], []⟩,
        ⟨49987, false, false, [], []⟩
      ]⟩,
    ⟨[85257, 7], [20763, 85497], .contexts [
        ⟨42673, true, false, [20760], [7]⟩,
        ⟨32842, false, false, [20760], []⟩,
        ⟨32838, false, false, [20760], []⟩,
        ⟨42674, true, false, [], [16221, 85497]⟩,
        ⟨42677, true, false, [], [85497]⟩
      ]⟩,
    ⟨[85257, 9], [85259], .contexts [
        ⟨30968, false, false, [], []⟩,
        ⟨31146, false, false, [], []⟩
      ]⟩,
    ⟨[85257, 11], [20759, 83373], .contexts [
        ⟨42673, true, false, [20760], [11]⟩,
        ⟨32847, false, false, [20760], []⟩,
        ⟨21344, false, false, [20760], []⟩,
        ⟨42676, true, false, [], [83373]⟩
      ]⟩,
    ⟨[85257, 13], [20765, 85945], .contexts [
        ⟨42680, false, false, [], []⟩,
        ⟨56652, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2507. -/
def y322TCIndexRaw2507 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85257, 15], [20767, 41383, 85387], .contexts [
        ⟨42673, true, false, [20760], [15]⟩,
        ⟨35830, false, false, [20760], []⟩,
        ⟨35833, false, false, [20760], []⟩,
        ⟨42674, true, false, [], [18923, 86223]⟩,
        ⟨42681, true, false, [], [86223]⟩,
        ⟨106267, false, false, [20767], []⟩
      ]⟩,
    ⟨[85259, 1], [20773, 83325], .contexts [
        ⟨42690, false, false, [], []⟩,
        ⟨49959, false, false, [], []⟩
      ]⟩,
    ⟨[85259, 3], [20775, 79013], .contexts [
        ⟨42693, false, false, [], []⟩,
        ⟨49969, false, false, [], []⟩
      ]⟩,
    ⟨[85259, 5], [42431, 86291], .contexts [
        ⟨49955, false, false, [], []⟩,
        ⟨107295, false, false, [], []⟩
      ]⟩,
    ⟨[85259, 7], [20777, 83375], .contexts [
        ⟨42695, false, false, [], []⟩,
        ⟨49977, false, false, [], []⟩
      ]⟩,
    ⟨[85259, 9], [85257], .contexts [
        ⟨30970, false, false, [], []⟩,
        ⟨31149, false, false, [], []⟩
      ]⟩,
    ⟨[85261], [20775, 84487], .contexts [
        ⟨42699, false, false, [], []⟩
      ]⟩,
    ⟨[85259, 11], [20775, 84487], .contexts [
        ⟨30972, false, false, [], []⟩,
        ⟨160454, false, false, [], []⟩
      ]⟩,
    ⟨[85259, 13], [38401, 89341], .contexts [
        ⟨56641, false, false, [], []⟩,
        ⟨103371, false, false, [], []⟩
      ]⟩,
    ⟨[85259, 15], [20773, 83329], .contexts [
        ⟨42696, false, false, [], []⟩,
        ⟨49993, false, false, [], []⟩
      ]⟩,
    ⟨[85263, 1], [20775, 84487], .contexts [
        ⟨30977, false, false, [], []⟩,
        ⟨160454, false, false, [], []⟩
      ]⟩,
    ⟨[85263, 3], [26361, 91621], .contexts [
        ⟨66751, false, false, [], []⟩,
        ⟨66782, false, false, [], []⟩
      ]⟩,
    ⟨[85263, 5], [20775, 84491], .contexts [
        ⟨42707, false, false, [], []⟩
      ]⟩,
    ⟨[85263, 7], [20783, 85253], .contexts [
        ⟨42711, false, false, [], []⟩
      ]⟩,
    ⟨[85263, 9], [20775, 23013, 45539, 86271], .contexts [
        ⟨42714, false, false, [], []⟩,
        ⟨158487, false, false, [20775], []⟩
      ]⟩,
    ⟨[85263, 11], [20785, 83325], .contexts [
        ⟨42713, false, false, [], []⟩,
        ⟨42961, false, false, [], []⟩
      ]⟩,
    ⟨[85263, 13], [85265], .contexts [
        ⟨30979, false, false, [], []⟩,
        ⟨31144, false, false, [], []⟩
      ]⟩,
    ⟨[85263, 15], [23391, 88973], .contexts [
        ⟨53378, false, false, [], []⟩
      ]⟩,
    ⟨[85265, 1], [20785, 83319], .contexts [
        ⟨43197, false, false, [], []⟩,
        ⟨43190, false, false, [], []⟩
      ]⟩,
    ⟨[85265, 3], [22469, 88019], .contexts [
        ⟨49007, false, false, [], []⟩,
        ⟨66789, false, false, [], []⟩
      ]⟩,
    ⟨[85265, 5], [24261, 37669, 89609], .contexts [
        ⟨57126, false, false, [], []⟩,
        ⟨102500, false, false, [24261], []⟩
      ]⟩,
    ⟨[85265, 7], [22361, 27069, 85875], .contexts [
        ⟨48774, false, false, [], []⟩,
        ⟨69257, false, false, [22361], []⟩
      ]⟩,
    ⟨[85265, 9], [23075, 45539, 86269], .contexts [
        ⟨51503, false, false, [], []⟩,
        ⟨110679, false, false, [23075], []⟩
      ]⟩,
    ⟨[85265, 11], [20785, 83323], .contexts [
        ⟨42966, false, false, [], []⟩,
        ⟨42963, false, false, [], []⟩
      ]⟩,
    ⟨[85265, 13], [85263], .contexts [
        ⟨30981, false, false, [], []⟩,
        ⟨31145, false, false, [], []⟩
      ]⟩,
    ⟨[85265, 15], [85267], .contexts [
        ⟨30983, false, false, [], []⟩,
        ⟨31143, false, false, [], []⟩
      ]⟩,
    ⟨[85267, 1], [85269], .contexts [
        ⟨30987, false, false, [], []⟩,
        ⟨31140, false, false, [], []⟩
      ]⟩,
    ⟨[85267, 3], [38279, 49763, 94111], .contexts [
        ⟨103238, true, false, [38276], [3]⟩,
        ⟨20, false, false, [38276, 94361], []⟩,
        ⟨103239, true, false, [], [94361]⟩,
        ⟨115267, false, false, [38279], []⟩
      ]⟩,
    ⟨[85267, 5], [22409, 85275], .contexts [
        ⟨48948, false, false, [], []⟩,
        ⟨48944, false, false, [], []⟩
      ]⟩,
    ⟨[85267, 7], [57441, 86859], .contexts [
        ⟨124317, false, false, [], []⟩
      ]⟩,
    ⟨[85267, 9], [23075, 87063], .contexts [
        ⟨51561, false, false, [], []⟩,
        ⟨51602, false, false, [], []⟩
      ]⟩,
    ⟨[85267, 11], [44809, 89349], .contexts [
        ⟨119484, false, false, [], []⟩,
        ⟨119481, false, false, [], []⟩
      ]⟩,
    ⟨[85267, 13], [23441, 84979], .contexts [
        ⟨53460, true, false, [23438], [13]⟩,
        ⟨59, false, false, [23438, 84979], []⟩,
        ⟨53461, true, false, [], [84979]⟩
      ]⟩,
    ⟨[85267, 15], [85265], .contexts [
        ⟨30985, false, false, [], []⟩,
        ⟨31144, false, false, [], []⟩
      ]⟩,
    ⟨[85269, 1], [85267], .contexts [
        ⟨30989, false, false, [], []⟩,
        ⟨31143, false, false, [], []⟩
      ]⟩,
    ⟨[85271], [22411, 85269], .contexts [
        ⟨48871, false, false, [], []⟩
      ]⟩,
    ⟨[85269, 3], [22411, 85269], .contexts [
        ⟨30991, false, false, [], []⟩,
        ⟨160483, false, false, [], []⟩
      ]⟩,
    ⟨[85269, 5], [22409, 85273], .contexts [
        ⟨48873, false, false, [], []⟩,
        ⟨48933, false, false, [], []⟩
      ]⟩,
    ⟨[85269, 7], [26799, 86675], .contexts [
        ⟨68361, false, false, [], []⟩
      ]⟩,
    ⟨[85269, 9], [53253, 65395, 90797], .contexts [
        ⟨119411, false, false, [], []⟩,
        ⟨133656, false, false, [53253], []⟩
      ]⟩,
    ⟨[85269, 11], [44809, 89347], .contexts [
        ⟨109789, false, false, [], []⟩,
        ⟨119479, false, false, [], []⟩
      ]⟩,
    ⟨[85269, 13], [23457, 85269], .contexts [
        ⟨53492, false, false, [], []⟩,
        ⟨53515, false, false, [], []⟩
      ]⟩,
    ⟨[85269, 15], [20785, 83319], .contexts [
        ⟨43347, false, false, [], []⟩,
        ⟨43190, false, false, [], []⟩
      ]⟩,
    ⟨[85273, 1], [85275], .contexts [
        ⟨30998, false, false, [], []⟩,
        ⟨31138, false, false, [], []⟩
      ]⟩,
    ⟨[85273, 3], [74491, 97015], .contexts [
        ⟨145261, true, false, [74488], [3]⟩,
        ⟨20, false, false, [74488, 97015], []⟩,
        ⟨145262, true, false, [], [97015]⟩
      ]⟩,
    ⟨[85273, 5], [22411, 85269], .contexts [
        ⟨30996, false, false, [], []⟩,
        ⟨160483, false, false, [], []⟩
      ]⟩,
    ⟨[85273, 7], [72147, 96827], .contexts [
        ⟨141635, true, false, [72144], [7]⟩,
        ⟨38, false, false, [72144, 96827], []⟩,
        ⟨141636, true, false, [], [96827]⟩
      ]⟩,
    ⟨[85273, 9], [51799, 85011], .contexts [
        ⟨117640, false, false, [], []⟩
      ]⟩,
    ⟨[85273, 11], [58829, 96249], .contexts [
        ⟨125871, true, false, [58826], [11]⟩,
        ⟨53, false, false, [58826, 96249], []⟩,
        ⟨125872, true, false, [], [96249]⟩
      ]⟩,
    ⟨[85273, 13], [23471, 85273], .contexts [
        ⟨53517, false, false, [23466], [85273, 13]⟩,
        ⟨48873, true, false, [23466, 23457], [13]⟩,
        ⟨53516, true, false, [23466], [5, 13]⟩,
        ⟨53516, true, false, [23466], [5, 13]⟩,
        ⟨53515, true, false, [23466], [5, 13]⟩,
        ⟨53492, true, false, [23466], [5, 13]⟩,
        ⟨53490, true, false, [23466], [5, 13]⟩,
        ⟨1136, false, false, [23466, 85269], []⟩,
        ⟨48936, false, false, [23466], []⟩,
        ⟨48935, false, false, [23466], []⟩,
        ⟨48938, false, false, [23466, 22409], []⟩,
        ⟨53518, true, false, [], [22409, 85273]⟩,
        ⟨53519, true, false, [], [85273]⟩
      ]⟩,
    ⟨[85273, 15], [22443, 87411], .contexts [
        ⟨48941, true, false, [22440], [15]⟩,
        ⟨1, false, false, [22440, 87411], []⟩,
        ⟨48942, true, false, [], [87411]⟩
      ]⟩,
    ⟨[85275, 1], [85273], .contexts [
        ⟨31000, false, false, [], []⟩,
        ⟨31139, false, false, [], []⟩
      ]⟩,
    ⟨[85275, 3], [23477, 85275], .contexts [
        ⟨53529, false, false, [], []⟩,
        ⟨53550, false, false, [], []⟩
      ]⟩,
    ⟨[85275, 5], [22411, 85267], .contexts [
        ⟨48948, true, false, [22408], [5]⟩,
        ⟨28, false, false, [22408, 85267], []⟩,
        ⟨48870, true, false, [], [85267]⟩
      ]⟩,
    ⟨[85275, 7], [71601, 95797], .contexts [
        ⟨140468, true, false, [71598], [7]⟩,
        ⟨38, false, false, [71598, 95797], []⟩,
        ⟨140469, true, false, [], [95797]⟩
      ]⟩,
    ⟨[85275, 9], [85277], .contexts [
        ⟨31002, false, false, [], []⟩,
        ⟨31137, false, false, [], []⟩
      ]⟩,
    ⟨[85275, 11], [63083, 96247], .contexts [
        ⟨130938, true, false, [63080], [11]⟩,
        ⟨53, false, false, [63080, 96247], []⟩,
        ⟨130939, true, false, [], [96247]⟩
      ]⟩,
    ⟨[85275, 13], [23461, 84981], .contexts [
        ⟨53500, false, false, [], []⟩,
        ⟨53520, false, false, [], []⟩
      ]⟩,
    ⟨[85275, 15], [24279, 37669, 89609], .contexts [
        ⟨57150, true, false, [24276], [15]⟩,
        ⟨1, false, false, [24276, 89699], []⟩,
        ⟨57151, true, false, [], [89699]⟩,
        ⟨102500, false, false, [24279], []⟩
      ]⟩,
    ⟨[85277, 1], [60961, 95287], .contexts [
        ⟨128366, false, false, [], []⟩
      ]⟩,
    ⟨[85277, 3], [23475, 85277], .contexts [
        ⟨53554, false, false, [], []⟩,
        ⟨53574, false, false, [], []⟩
      ]⟩,
    ⟨[85277, 5], [23115, 87063], .contexts [
        ⟨51606, true, false, [23112], [5]⟩,
        ⟨28, false, false, [23112, 87063], []⟩,
        ⟨51607, true, false, [], [87063]⟩
      ]⟩,
    ⟨[85277, 7], [45837, 71607, 95795], .contexts [
        ⟨111071, false, false, [], []⟩,
        ⟨140480, false, false, [45837], []⟩
      ]⟩,
    ⟨[85277, 9], [85275], .contexts [
        ⟨31004, false, false, [], []⟩,
        ⟨31138, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2508. -/
def y322TCIndexRaw2508 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85277, 11], [85279], .contexts [
        ⟨31006, false, false, [], []⟩,
        ⟨31135, false, false, [], []⟩
      ]⟩,
    ⟨[85277, 13], [23461, 84983], .contexts [
        ⟨53540, false, false, [], []⟩,
        ⟨53530, false, false, [], []⟩
      ]⟩,
    ⟨[85277, 15], [24279, 37669, 39477, 84319], .contexts [
        ⟨57190, false, false, [], []⟩,
        ⟨158492, false, false, [24279], []⟩
      ]⟩,
    ⟨[85279, 1], [59679, 85169], .contexts [
        ⟨31010, false, false, [], []⟩,
        ⟨126932, false, false, [], []⟩
      ]⟩,
    ⟨[85279, 3], [23477, 85279], .contexts [
        ⟨31006, true, false, [], [3]⟩,
        ⟨53575, true, false, [23474], [11, 3]⟩,
        ⟨53575, true, false, [23474], [11, 3]⟩,
        ⟨53574, true, false, [23474], [11, 3]⟩,
        ⟨53554, true, false, [23474], [11, 3]⟩,
        ⟨53552, true, false, [23474], [11, 3]⟩,
        ⟨545, false, false, [23474, 85277], []⟩,
        ⟨54, false, false, [23474, 85277], []⟩,
        ⟨53576, false, false, [23474], []⟩,
        ⟨53577, false, false, [23474], []⟩,
        ⟨53528, true, false, [], [85279]⟩
      ]⟩,
    ⟨[91837], [54149, 55067, 90389], .contexts [
        ⟨121454, false, false, [], []⟩,
        ⟨121565, false, false, [], []⟩
      ]⟩,
    ⟨[85279, 5], [24297, 54149, 55067, 90389], .contexts [
        ⟨67824, false, false, [], []⟩,
        ⟨160517, false, false, [24297], []⟩
      ]⟩,
    ⟨[85279, 7], [24301, 85729], .contexts [
        ⟨57236, false, false, [], []⟩,
        ⟨57277, false, false, [], []⟩
      ]⟩,
    ⟨[85279, 9], [24303, 85627], .contexts [
        ⟨57227, true, false, [24298], [9]⟩,
        ⟨48352, false, false, [24298], []⟩,
        ⟨57226, true, false, [], [22267, 85627]⟩,
        ⟨57237, true, false, [], [85627]⟩
      ]⟩,
    ⟨[85279, 11], [85277], .contexts [
        ⟨31008, false, false, [], []⟩,
        ⟨31137, false, false, [], []⟩
      ]⟩,
    ⟨[85279, 13], [23461, 84985], .contexts [
        ⟨53559, false, false, [], []⟩,
        ⟨53578, false, false, [], []⟩
      ]⟩,
    ⟨[85279, 15], [24297, 39495, 84317], .contexts [
        ⟨57227, true, false, [24298], [15]⟩,
        ⟨39168, false, false, [24298], []⟩,
        ⟨39150, false, false, [24298], []⟩,
        ⟨57230, true, false, [], [86811]⟩,
        ⟨104595, false, false, [24297], []⟩
      ]⟩,
    ⟨[85291, 1], [62181, 83265], .contexts [
        ⟨31034, false, false, [], []⟩,
        ⟨129921, false, false, [], []⟩
      ]⟩,
    ⟨[85291, 3], [73547, 96931], .contexts [
        ⟨143731, true, false, [73544], [3]⟩,
        ⟨20, false, false, [73544, 96931], []⟩,
        ⟨143732, true, false, [], [96931]⟩
      ]⟩,
    ⟨[85291, 5], [57919, 83863], .contexts [
        ⟨31032, false, false, [], []⟩,
        ⟨124835, false, false, [], []⟩
      ]⟩,
    ⟨[85291, 7], [18095, 85291], .contexts [
        ⟨31036, true, false, [], [7]⟩,
        ⟨31340, true, false, [18092], [1, 7]⟩,
        ⟨502, false, false, [18092, 85293], []⟩,
        ⟨9, false, false, [18092, 85293], []⟩,
        ⟨31126, false, false, [18092], []⟩,
        ⟨31127, false, false, [18092], []⟩,
        ⟨31035, false, false, [18092], []⟩,
        ⟨31035, false, false, [18092], []⟩,
        ⟨31341, false, false, [18092], []⟩,
        ⟨31312, true, false, [], [85291]⟩
      ]⟩,
    ⟨[85291, 9], [55461, 96185], .contexts [
        ⟨121977, false, false, [], []⟩,
        ⟨121979, false, false, [], []⟩
      ]⟩,
    ⟨[85291, 11], [36971, 62133, 83269], .contexts [
        ⟨101249, false, false, [], []⟩,
        ⟨129890, false, false, [36971], []⟩
      ]⟩,
    ⟨[85291, 13], [36861, 83593], .contexts [
        ⟨101119, false, false, [], []⟩,
        ⟨101239, false, false, [], []⟩
      ]⟩,
    ⟨[85291, 15], [45789, 55471, 87731], .contexts [
        ⟨110991, false, false, [], []⟩,
        ⟨122000, false, false, [45789], []⟩
      ]⟩,
    ⟨[85297, 1], [50529, 84701], .contexts [
        ⟨31046, false, false, [], []⟩,
        ⟨122153, false, false, [], []⟩
      ]⟩,
    ⟨[85297, 3], [50435, 85823], .contexts [
        ⟨116015, true, false, [50432], [3]⟩,
        ⟨20, false, false, [50432, 85823], []⟩,
        ⟨116016, true, false, [], [85823]⟩
      ]⟩,
    ⟨[85297, 5], [50529, 84705], .contexts [
        ⟨116129, true, false, [50530], [5]⟩,
        ⟨28, false, false, [50530, 84705], []⟩,
        ⟨116130, true, false, [], [84705]⟩
      ]⟩,
    ⟨[85297, 7], [18093, 85297], .contexts [
        ⟨31327, false, false, [], []⟩,
        ⟨31328, false, false, [], []⟩
      ]⟩,
    ⟨[85297, 9], [51189, 88451], .contexts [
        ⟨116961, false, false, [], []⟩,
        ⟨122188, false, false, [], []⟩
      ]⟩,
    ⟨[85297, 11], [62181, 83263], .contexts [
        ⟨31044, false, false, [], []⟩,
        ⟨129933, false, false, [], []⟩
      ]⟩,
    ⟨[85297, 13], [45949, 87341], .contexts [
        ⟨118491, false, false, [], []⟩,
        ⟨118486, false, false, [], []⟩
      ]⟩,
    ⟨[85297, 15], [51181, 84149], .contexts [
        ⟨116945, false, false, [], []⟩
      ]⟩,
    ⟨[85303, 1], [48455, 84149], .contexts [
        ⟨31058, false, false, [], []⟩,
        ⟨113790, false, false, [], []⟩
      ]⟩,
    ⟨[85303, 3], [21181, 83771], .contexts [
        ⟨44413, false, false, [], []⟩,
        ⟨125584, false, false, [], []⟩
      ]⟩,
    ⟨[85303, 5], [48455, 84153], .contexts [
        ⟨116900, false, false, [], []⟩
      ]⟩,
    ⟨[85303, 7], [18095, 85303], .contexts [
        ⟨31313, false, false, [], []⟩,
        ⟨31314, false, false, [], []⟩
      ]⟩,
    ⟨[85303, 9], [21201, 85303], .contexts [
        ⟨44478, false, false, [], []⟩
      ]⟩,
    ⟨[85303, 11], [51155, 86397], .contexts [
        ⟨116907, false, false, [], []⟩
      ]⟩,
    ⟨[85303, 13], [51163, 91235], .contexts [
        ⟨116913, true, false, [51160], [13]⟩,
        ⟨64748, false, false, [51160], []⟩,
        ⟨64800, false, false, [51160], []⟩,
        ⟨116915, true, false, [], [91235]⟩,
        ⟨116915, true, false, [], [91235]⟩,
        ⟨116914, true, false, [], [91235]⟩
      ]⟩,
    ⟨[85303, 15], [55617, 84701], .contexts [
        ⟨31056, false, false, [], []⟩,
        ⟨122161, false, false, [], []⟩
      ]⟩,
    ⟨[85311, 1], [18085, 83091], .contexts [
        ⟨31072, false, false, [], []⟩,
        ⟨44375, false, false, [], []⟩
      ]⟩,
    ⟨[85311, 3], [21147, 39913, 84463], .contexts [
        ⟨44365, true, false, [21148], [3]⟩,
        ⟨20, false, false, [21148, 85933], []⟩,
        ⟨44366, true, false, [], [85933]⟩,
        ⟨105666, false, false, [21147], []⟩
      ]⟩,
    ⟨[85311, 5], [18085, 83095], .contexts [
        ⟨31282, false, false, [], []⟩,
        ⟨31276, false, false, [], []⟩
      ]⟩,
    ⟨[85311, 7], [46423, 87305], .contexts [
        ⟨111732, true, false, [46420], [7]⟩,
        ⟨38, false, false, [46420, 87305], []⟩,
        ⟨111733, true, false, [], [87305]⟩
      ]⟩,
    ⟨[85311, 9], [85313], .contexts [
        ⟨31074, false, false, [], []⟩,
        ⟨31106, false, false, [], []⟩
      ]⟩,
    ⟨[85311, 11], [21119, 33517, 84253], .contexts [
        ⟨44385, false, false, [], []⟩,
        ⟨91355, false, false, [21119], []⟩
      ]⟩,
    ⟨[85311, 13], [21119, 85111], .contexts [
        ⟨44320, false, false, [], []⟩,
        ⟨44370, false, false, [], []⟩
      ]⟩,
    ⟨[85311, 15], [33549, 94903], .contexts [
        ⟨91254, true, false, [33550], [15]⟩,
        ⟨87050, false, false, [33550], []⟩,
        ⟨87297, false, false, [33550], []⟩,
        ⟨91255, true, false, [], [94903]⟩,
        ⟨91255, true, false, [], [94903]⟩,
        ⟨91253, false, true, [], [94903]⟩
      ]⟩,
    ⟨[22765, 88463], [22765, 48729, 85417], .contexts [
        ⟨114072, false, false, [22765], []⟩
      ]⟩,
    ⟨[85313, 1], [22765, 48729, 85417], .contexts [
        ⟨50455, false, false, [], []⟩,
        ⟨160556, false, false, [], []⟩
      ]⟩,
    ⟨[85313, 3], [21147, 85935], .contexts [
        ⟨44315, false, false, [], []⟩,
        ⟨44359, false, false, [], []⟩
      ]⟩,
    ⟨[85313, 5], [18085, 83097], .contexts [
        ⟨31272, false, false, [], []⟩,
        ⟨31274, false, false, [], []⟩
      ]⟩,
    ⟨[85313, 7], [24065, 89433], .contexts [
        ⟨56024, true, false, [24062], [7]⟩,
        ⟨38, false, false, [24062, 89433], []⟩,
        ⟨56025, true, false, [], [89433]⟩
      ]⟩,
    ⟨[85313, 9], [85311], .contexts [
        ⟨31076, false, false, [], []⟩,
        ⟨31108, false, false, [], []⟩
      ]⟩,
    ⟨[85313, 11], [85315], .contexts [
        ⟨31078, false, false, [], []⟩,
        ⟨31104, false, false, [], []⟩
      ]⟩,
    ⟨[85313, 13], [21119, 85109], .contexts [
        ⟨44266, true, false, [21116], [13]⟩,
        ⟨59, false, false, [21116, 85109], []⟩,
        ⟨44267, true, false, [], [85109]⟩
      ]⟩,
    ⟨[85313, 15], [45989, 85705], .contexts [
        ⟨111277, false, false, [], []⟩
      ]⟩,
    ⟨[85315, 1], [85317], .contexts [
        ⟨31082, false, false, [], []⟩,
        ⟨31102, false, false, [], []⟩
      ]⟩,
    ⟨[85315, 3], [21147, 27079, 85877], .contexts [
        ⟨44369, false, false, [], []⟩,
        ⟨69277, false, false, [21147], []⟩
      ]⟩,
    ⟨[85315, 5], [18085, 83099], .contexts [
        ⟨31267, false, false, [], []⟩,
        ⟨31262, false, false, [], []⟩
      ]⟩,
    ⟨[85315, 7], [21763, 86323], .contexts [
        ⟨46280, true, false, [21760], [7]⟩,
        ⟨38, false, false, [21760, 86323], []⟩,
        ⟨46281, true, false, [], [86323]⟩
      ]⟩,
    ⟨[85315, 9], [34447, 46829, 90659], .contexts [
        ⟨94295, false, false, [], []⟩,
        ⟨112229, false, false, [34447], []⟩
      ]⟩,
    ⟨[85315, 11], [85313], .contexts [
        ⟨31080, false, false, [], []⟩,
        ⟨31106, false, false, [], []⟩
      ]⟩,
    ⟨[85315, 13], [22765, 88469], .contexts [
        ⟨50440, true, false, [22762], [13]⟩,
        ⟨50279, false, false, [22762], []⟩,
        ⟨50281, false, false, [22762], []⟩,
        ⟨50437, true, false, [], [88469]⟩
      ]⟩,
    ⟨[85315, 15], [96887], .contexts [
        ⟨142909, true, false, [], [15]⟩,
        ⟨1, false, false, [96887], []⟩,
        ⟨142883, false, false, [], []⟩,
        ⟨142882, false, false, [], []⟩
      ]⟩,
    ⟨[85317, 1], [85315], .contexts [
        ⟨31084, false, false, [], []⟩,
        ⟨31104, false, false, [], []⟩
      ]⟩,
    ⟨[85317, 3], [18077, 84339], .contexts [
        ⟨31244, false, false, [], []⟩,
        ⟨50457, false, false, [], []⟩
      ]⟩,
    ⟨[85317, 5], [18085, 83101], .contexts [
        ⟨31258, false, false, [], []⟩,
        ⟨31259, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2509. -/
def y322TCIndexRaw2509 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85317, 7], [21763, 86321], .contexts [
        ⟨46310, false, false, [], []⟩,
        ⟨50483, false, false, [], []⟩
      ]⟩,
    ⟨[85317, 9], [20523, 83619], .contexts [
        ⟨42570, false, false, [], []⟩,
        ⟨42565, false, false, [], []⟩
      ]⟩,
    ⟨[85317, 11], [22765, 48729, 85417], .contexts [
        ⟨50438, false, false, [], []⟩,
        ⟨160556, false, false, [], []⟩
      ]⟩,
    ⟨[85317, 13], [85319], .contexts [
        ⟨31086, false, false, [], []⟩,
        ⟨31099, false, false, [], []⟩
      ]⟩,
    ⟨[85317, 15], [96885], .contexts [
        ⟨142849, false, false, [], []⟩,
        ⟨142851, false, false, [], []⟩
      ]⟩,
    ⟨[19647, 87031], [19647, 21539, 86593], .contexts [
        ⟨45482, false, false, [19647], []⟩
      ]⟩,
    ⟨[85319, 1], [19647, 21539, 86593], .contexts [
        ⟨39889, false, false, [], []⟩,
        ⟨160581, false, false, [], []⟩
      ]⟩,
    ⟨[85319, 3], [18077, 84341], .contexts [
        ⟨31228, false, false, [], []⟩,
        ⟨31220, false, false, [], []⟩
      ]⟩,
    ⟨[85319, 5], [18085, 83103], .contexts [
        ⟨31252, false, false, [], []⟩,
        ⟨31249, false, false, [], []⟩
      ]⟩,
    ⟨[85319, 7], [29947, 39311, 85369], .contexts [
        ⟨78471, true, false, [29944], [7]⟩,
        ⟨38, false, false, [29944, 93283], []⟩,
        ⟨78472, true, false, [], [93283]⟩,
        ⟨104373, false, false, [29947], []⟩
      ]⟩,
    ⟨[85319, 9], [20523, 83621], .contexts [
        ⟨42356, false, false, [], []⟩,
        ⟨42549, false, false, [], []⟩
      ]⟩,
    ⟨[85319, 11], [18213, 83799], .contexts [
        ⟨32264, false, false, [], []⟩,
        ⟨50442, false, false, [], []⟩
      ]⟩,
    ⟨[85319, 13], [85317], .contexts [
        ⟨31088, false, false, [], []⟩,
        ⟨31102, false, false, [], []⟩
      ]⟩,
    ⟨[85319, 15], [85321], .contexts [
        ⟨31090, false, false, [], []⟩,
        ⟨31194, false, false, [], []⟩
      ]⟩,
    ⟨[85321, 1], [85323], .contexts [
        ⟨31094, false, false, [], []⟩,
        ⟨31097, false, false, [], []⟩
      ]⟩,
    ⟨[85321, 3], [18077, 84343], .contexts [
        ⟨31203, false, false, [], []⟩,
        ⟨31200, false, false, [], []⟩
      ]⟩,
    ⟨[85321, 5], [18085, 83105], .contexts [
        ⟨31235, false, false, [], []⟩,
        ⟨31246, false, false, [], []⟩
      ]⟩,
    ⟨[85321, 7], [31073, 94183], .contexts [
        ⟨83178, true, false, [31070], [7]⟩,
        ⟨38, false, false, [31070, 94183], []⟩,
        ⟨83179, true, false, [], [94183]⟩
      ]⟩,
    ⟨[85321, 9], [20523, 83623], .contexts [
        ⟨42148, false, false, [], []⟩
      ]⟩,
    ⟨[85321, 11], [24363, 46927, 89147], .contexts [
        ⟨57439, false, false, [], []⟩,
        ⟨112322, false, false, [24363], []⟩
      ]⟩,
    ⟨[85321, 13], [19647, 41143, 86935], .contexts [
        ⟨39897, false, false, [], []⟩,
        ⟨106058, false, false, [19647], []⟩
      ]⟩,
    ⟨[85321, 15], [85319], .contexts [
        ⟨31092, false, false, [], []⟩,
        ⟨31099, false, false, [], []⟩
      ]⟩,
    ⟨[85323, 1], [85321], .contexts [
        ⟨31096, false, false, [], []⟩,
        ⟨31194, false, false, [], []⟩
      ]⟩,
    ⟨[85323, 3], [18071, 80791], .contexts [
        ⟨31191, false, false, [], []⟩,
        ⟨31195, false, false, [], []⟩
      ]⟩,
    ⟨[85323, 5], [18085, 83107], .contexts [
        ⟨31218, true, false, [18086], [5]⟩,
        ⟨28, false, false, [18086, 83107], []⟩,
        ⟨31219, true, false, [], [83107]⟩,
        ⟨31209, false, false, [], []⟩
      ]⟩,
    ⟨[85323, 7], [29125, 92825], .contexts [
        ⟨75651, true, false, [29122], [7]⟩,
        ⟨38, false, false, [29122, 92825], []⟩,
        ⟨75652, true, false, [], [92825]⟩
      ]⟩,
    ⟨[85323, 9], [23981, 46909, 89141], .contexts [
        ⟨55489, false, false, [], []⟩,
        ⟨112291, false, false, [23981], []⟩
      ]⟩,
    ⟨[85323, 11], [24363, 46927, 89145], .contexts [
        ⟨57411, false, false, [], []⟩,
        ⟨112309, false, false, [24363], []⟩
      ]⟩,
    ⟨[85323, 13], [18147, 85351], .contexts [
        ⟨31725, false, false, [], []⟩
      ]⟩,
    ⟨[85323, 15], [19647, 21539, 86593], .contexts [
        ⟨39907, false, false, [], []⟩,
        ⟨160581, false, false, [], []⟩
      ]⟩,
    ⟨[85325, 1], [15099, 85325], .contexts [
        ⟨31349, false, false, [], []⟩,
        ⟨31347, false, false, [], []⟩
      ]⟩,
    ⟨[85325, 3], [15097, 86335], .contexts [
        ⟨36559, false, false, [], []⟩
      ]⟩,
    ⟨[85325, 5], [18101, 80431], .contexts [
        ⟨31356, false, false, [], []⟩
      ]⟩,
    ⟨[85325, 7], [84097], .contexts [
        ⟨31343, true, false, [], [7]⟩,
        ⟨38, false, false, [84097], []⟩,
        ⟨24754, false, false, [], []⟩,
        ⟨24753, false, false, [], []⟩
      ]⟩,
    ⟨[85325, 9], [16853, 85325], .contexts [
        ⟨31360, false, false, [], []⟩,
        ⟨31359, false, false, [], []⟩
      ]⟩,
    ⟨[85325, 11], [82849], .contexts [
        ⟨31361, false, false, [], []⟩,
        ⟨17445, false, false, [], []⟩
      ]⟩,
    ⟨[85325, 13], [16855, 79891], .contexts [
        ⟨31366, false, false, [], []⟩,
        ⟨31365, false, false, [], []⟩
      ]⟩,
    ⟨[85325, 15], [16859, 82779], .contexts [
        ⟨31371, false, false, [], []⟩,
        ⟨31370, false, false, [], []⟩
      ]⟩,
    ⟨[85327, 1], [14671, 85327], .contexts [
        ⟨31381, false, false, [], []⟩,
        ⟨31379, false, false, [], []⟩
      ]⟩,
    ⟨[85327, 3], [27453, 92185], .contexts [
        ⟨70491, false, false, [], []⟩
      ]⟩,
    ⟨[85327, 5], [83497], .contexts [
        ⟨31375, false, false, [], []⟩,
        ⟨21584, false, false, [], []⟩
      ]⟩,
    ⟨[85327, 7], [3067, 85327], .contexts [
        ⟨31383, false, false, [], []⟩,
        ⟨6194, true, false, [], [85327]⟩,
        ⟨6193, true, false, [], [85327]⟩,
        ⟨13, true, false, [], [3067, 85327]⟩,
        ⟨31382, false, false, [], []⟩
      ]⟩,
    ⟨[85327, 9], [7259, 85331], .contexts [
        ⟨31431, false, false, [], []⟩
      ]⟩,
    ⟨[85327, 11], [16349, 83949], .contexts [
        ⟨31387, false, false, [], []⟩,
        ⟨31386, false, false, [], []⟩
      ]⟩,
    ⟨[85327, 13], [14141, 83937], .contexts [
        ⟨31389, false, false, [], []⟩,
        ⟨31388, false, false, [], []⟩
      ]⟩,
    ⟨[85327, 15], [16355, 47739, 84063], .contexts [
        ⟨37885, false, false, [], []⟩,
        ⟨113137, false, false, [16355], []⟩
      ]⟩,
    ⟨[85329, 1], [1369, 84349], .contexts [
        ⟨31398, false, false, [], []⟩,
        ⟨26136, false, false, [], []⟩
      ]⟩,
    ⟨[85329, 3], [2909, 85329], .contexts [
        ⟨31404, false, false, [], []⟩,
        ⟨31400, false, false, [], []⟩
      ]⟩,
    ⟨[85329, 5], [85335], .contexts [
        ⟨31481, false, false, [], []⟩,
        ⟨31484, false, false, [], []⟩
      ]⟩,
    ⟨[85329, 7], [78101], .contexts [
        ⟨31393, false, false, [], []⟩,
        ⟨3600, false, false, [], []⟩
      ]⟩,
    ⟨[85329, 9], [13035, 85329], .contexts [
        ⟨31409, false, false, [], []⟩,
        ⟨31405, false, false, [], []⟩
      ]⟩,
    ⟨[85329, 11], [1369, 85329], .contexts [
        ⟨31413, false, false, [], []⟩,
        ⟨31410, false, false, [], []⟩
      ]⟩,
    ⟨[85329, 13], [11513, 85329], .contexts [
        ⟨31418, false, false, [], []⟩,
        ⟨31414, false, false, [], []⟩
      ]⟩,
    ⟨[85329, 15], [85337], .contexts [
        ⟨31513, false, false, [], []⟩,
        ⟨31515, false, false, [], []⟩
      ]⟩,
    ⟨[85331, 1], [1383, 85335], .contexts [
        ⟨31489, false, false, [], []⟩,
        ⟨39837, false, false, [], []⟩
      ]⟩,
    ⟨[85331, 3], [29141, 40319, 90097], .contexts [
        ⟨75702, false, false, [], []⟩,
        ⟨105390, false, false, [29141], []⟩
      ]⟩,
    ⟨[85331, 5], [84349], .contexts [
        ⟨31420, true, false, [], [5]⟩,
        ⟨28, false, false, [84349], []⟩,
        ⟨26121, false, false, [], []⟩,
        ⟨26120, false, false, [], []⟩
      ]⟩,
    ⟨[85331, 7], [3023, 85331], .contexts [
        ⟨31424, true, false, [], [7]⟩,
        ⟨3272, false, false, [84349], []⟩,
        ⟨3275, false, false, [84349], []⟩,
        ⟨31425, false, false, [], [5, 7, 5]⟩,
        ⟨6145, false, false, [], [7, 5]⟩,
        ⟨6171, false, false, [], [7, 5]⟩,
        ⟨6172, false, false, [], [7, 5]⟩,
        ⟨6172, false, false, [], [7, 5]⟩,
        ⟨26118, false, false, [3023], [5]⟩,
        ⟨31420, false, false, [3023], []⟩,
        ⟨31426, false, false, [], []⟩,
        ⟨31427, false, false, [3023], []⟩,
        ⟨13, true, false, [], [3023, 85331]⟩,
        ⟨31426, false, false, [], []⟩
      ]⟩,
    ⟨[85331, 9], [7257, 85327], .contexts [
        ⟨31430, false, false, [], []⟩,
        ⟨31429, false, false, [], []⟩
      ]⟩,
    ⟨[85331, 11], [1369, 85331], .contexts [
        ⟨31439, false, false, [], []⟩,
        ⟨31434, false, false, [], []⟩
      ]⟩,
    ⟨[85331, 13], [17045, 91117], .contexts [
        ⟨64426, false, false, [], []⟩
      ]⟩,
    ⟨[85343], [47753, 84067], .contexts [
        ⟨113148, false, false, [], []⟩
      ]⟩,
    ⟨[85331, 15], [47753, 84067], .contexts [
        ⟨31618, false, false, [], []⟩,
        ⟨160637, false, false, [], []⟩
      ]⟩,
    ⟨[85333, 1], [1383, 85337], .contexts [
        ⟨31520, false, false, [], []⟩,
        ⟨31593, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2510. -/
def y322TCIndexRaw2510 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85333, 3], [17041, 80259], .contexts [
        ⟨31450, false, false, [], []⟩,
        ⟨31448, false, false, [], []⟩
      ]⟩,
    ⟨[85333, 5], [47753, 84067], .contexts [
        ⟨31588, false, false, [], []⟩,
        ⟨160637, false, false, [], []⟩
      ]⟩,
    ⟨[85333, 7], [10303, 78107], .contexts [
        ⟨31454, false, false, [], []⟩,
        ⟨31451, false, false, [], []⟩
      ]⟩,
    ⟨[85333, 9], [18107, 80253], .contexts [
        ⟨31458, false, false, [], []⟩
      ]⟩,
    ⟨[85333, 11], [1369, 85333], .contexts [
        ⟨31469, false, false, [], []⟩,
        ⟨31462, false, false, [], []⟩
      ]⟩,
    ⟨[85333, 13], [18113, 85333], .contexts [
        ⟨31479, false, false, [], []⟩,
        ⟨31474, false, false, [], []⟩
      ]⟩,
    ⟨[85333, 15], [84349], .contexts [
        ⟨31442, false, false, [], []⟩,
        ⟨26120, false, false, [], []⟩
      ]⟩,
    ⟨[85335, 1], [1369, 85331], .contexts [
        ⟨31488, false, false, [], []⟩,
        ⟨31434, false, false, [], []⟩
      ]⟩,
    ⟨[85335, 3], [93415], .contexts [
        ⟨79130, false, false, [], []⟩,
        ⟨79132, false, false, [], []⟩
      ]⟩,
    ⟨[85335, 5], [85329], .contexts [
        ⟨31482, false, false, [], []⟩,
        ⟨31394, false, false, [], []⟩
      ]⟩,
    ⟨[85335, 7], [2939, 85335], .contexts [
        ⟨31496, false, false, [], []⟩,
        ⟨31491, false, false, [], []⟩
      ]⟩,
    ⟨[85335, 9], [13035, 85335], .contexts [
        ⟨31501, false, false, [], []⟩,
        ⟨31498, false, false, [], []⟩
      ]⟩,
    ⟨[85335, 11], [1369, 85335], .contexts [
        ⟨31506, false, false, [], []⟩,
        ⟨31503, false, false, [], []⟩
      ]⟩,
    ⟨[85335, 13], [11513, 85335], .contexts [
        ⟨31511, false, false, [], []⟩,
        ⟨31508, false, false, [], []⟩
      ]⟩,
    ⟨[85339], [47761, 84071], .contexts [
        ⟨113155, false, false, [], []⟩
      ]⟩,
    ⟨[85335, 15], [47761, 84071], .contexts [
        ⟨31556, true, false, [], [15]⟩,
        ⟨1, false, false, [85339], []⟩,
        ⟨31544, false, false, [], []⟩,
        ⟨160654, false, false, [], []⟩
      ]⟩,
    ⟨[85337, 1], [1369, 85333], .contexts [
        ⟨31519, false, false, [], []⟩,
        ⟨31462, false, false, [], []⟩
      ]⟩,
    ⟨[85337, 3], [2909, 85337], .contexts [
        ⟨31526, false, false, [], []⟩,
        ⟨31522, false, false, [], []⟩
      ]⟩,
    ⟨[85337, 5], [47761, 84071], .contexts [
        ⟨31541, false, false, [], []⟩,
        ⟨160654, false, false, [], []⟩
      ]⟩,
    ⟨[85337, 7], [11743, 78105], .contexts [
        ⟨31529, false, false, [], []⟩,
        ⟨31546, false, false, [], []⟩
      ]⟩,
    ⟨[85337, 9], [13035, 85337], .contexts [
        ⟨31535, false, false, [], []⟩,
        ⟨31532, false, false, [], []⟩
      ]⟩,
    ⟨[85337, 11], [1369, 85337], .contexts [
        ⟨31539, false, false, [], []⟩,
        ⟨31536, false, false, [], []⟩
      ]⟩,
    ⟨[85337, 13], [85341], .contexts [
        ⟨31558, false, false, [], []⟩,
        ⟨31560, false, false, [], []⟩
      ]⟩,
    ⟨[85337, 15], [85329], .contexts [
        ⟨31514, false, false, [], []⟩,
        ⟨31394, false, false, [], []⟩
      ]⟩,
    ⟨[85341, 1], [18123, 85341], .contexts [
        ⟨31571, false, false, [], []⟩,
        ⟨31565, false, false, [], []⟩
      ]⟩,
    ⟨[85341, 3], [2909, 85341], .contexts [
        ⟨31574, false, false, [], []⟩,
        ⟨31572, false, false, [], []⟩
      ]⟩,
    ⟨[85341, 5], [47761, 84073], .contexts [
        ⟨59689, false, false, [], []⟩,
        ⟨113163, false, false, [], []⟩
      ]⟩,
    ⟨[85341, 7], [18125, 79051], .contexts [
        ⟨31576, false, false, [], []⟩
      ]⟩,
    ⟨[85341, 9], [13035, 85341], .contexts [
        ⟨31581, false, false, [], []⟩,
        ⟨31578, false, false, [], []⟩
      ]⟩,
    ⟨[85341, 11], [1369, 85341], .contexts [
        ⟨31562, true, false, [], [11]⟩,
        ⟨82, false, false, [85337], []⟩,
        ⟨83, false, false, [85337], []⟩,
        ⟨31553, false, false, [], [13]⟩,
        ⟨31558, false, false, [1369], []⟩,
        ⟨31582, false, false, [], []⟩,
        ⟨31568, false, false, [1369], []⟩,
        ⟨3620, true, false, [], [85341]⟩,
        ⟨31582, false, false, [], []⟩
      ]⟩,
    ⟨[85341, 13], [85337], .contexts [
        ⟨31559, false, false, [], []⟩,
        ⟨31515, false, false, [], []⟩
      ]⟩,
    ⟨[85341, 15], [11513, 85341], .contexts [
        ⟨31586, false, false, [], []⟩,
        ⟨31583, false, false, [], []⟩
      ]⟩,
    ⟨[85345, 1], [2007, 85345], .contexts [
        ⟨31629, false, false, [], []⟩,
        ⟨31625, false, false, [], []⟩
      ]⟩,
    ⟨[85345, 3], [93053], .contexts [
        ⟨76804, false, false, [], []⟩,
        ⟨76800, false, false, [], []⟩
      ]⟩,
    ⟨[85345, 5], [79921], .contexts [
        ⟨31621, false, false, [], []⟩,
        ⟨7535, false, false, [], []⟩
      ]⟩,
    ⟨[85345, 7], [85347], .contexts [
        ⟨31650, false, false, [], []⟩,
        ⟨31652, false, false, [], []⟩
      ]⟩,
    ⟨[85345, 9], [79915], .contexts [
        ⟨31631, false, false, [], []⟩,
        ⟨7516, false, false, [], []⟩
      ]⟩,
    ⟨[85345, 11], [3621, 85345], .contexts [
        ⟨31636, false, false, [], []⟩,
        ⟨31633, false, false, [], []⟩
      ]⟩,
    ⟨[85345, 13], [2019, 85345], .contexts [
        ⟨31640, false, false, [], []⟩,
        ⟨31637, false, false, [], []⟩
      ]⟩,
    ⟨[85345, 15], [15141, 84351], .contexts [
        ⟨31647, false, false, [], []⟩,
        ⟨31643, false, false, [], []⟩
      ]⟩,
    ⟨[85347, 1], [2007, 85347], .contexts [
        ⟨31657, false, false, [], []⟩,
        ⟨31655, false, false, [], []⟩
      ]⟩,
    ⟨[85347, 3], [19581, 86927], .contexts [
        ⟨39562, false, false, [], []⟩
      ]⟩,
    ⟨[85347, 5], [7827, 80259], .contexts [
        ⟨31659, false, false, [], []⟩
      ]⟩,
    ⟨[85347, 7], [85345], .contexts [
        ⟨31651, false, false, [], []⟩,
        ⟨31622, false, false, [], []⟩
      ]⟩,
    ⟨[85347, 9], [79913], .contexts [
        ⟨31662, false, false, [], []⟩,
        ⟨7500, false, false, [], []⟩
      ]⟩,
    ⟨[85347, 11], [3621, 85347], .contexts [
        ⟨31664, false, false, [], []⟩,
        ⟨31663, false, false, [], []⟩
      ]⟩,
    ⟨[85347, 13], [2019, 85347], .contexts [
        ⟨31666, false, false, [], []⟩,
        ⟨31665, false, false, [], []⟩
      ]⟩,
    ⟨[85347, 15], [15141, 84353], .contexts [
        ⟨31668, false, false, [], []⟩,
        ⟨31667, false, false, [], []⟩
      ]⟩,
    ⟨[85349, 1], [16609, 85349], .contexts [
        ⟨31678, false, false, [], []⟩,
        ⟨31676, false, false, [], []⟩
      ]⟩,
    ⟨[85349, 3], [18135, 82733], .contexts [
        ⟨31682, false, false, [], []⟩,
        ⟨31702, false, false, [], []⟩
      ]⟩,
    ⟨[85349, 5], [83915], .contexts [
        ⟨31672, false, false, [], []⟩,
        ⟨23508, false, false, [], []⟩
      ]⟩,
    ⟨[85349, 7], [18135, 86331], .contexts [
        ⟨36525, true, false, [18136], [7]⟩,
        ⟨38, false, false, [18136, 86331], []⟩,
        ⟨36526, true, false, [], [86331]⟩
      ]⟩,
    ⟨[85349, 9], [85351], .contexts [
        ⟨31697, false, false, [], []⟩,
        ⟨31699, false, false, [], []⟩
      ]⟩,
    ⟨[85349, 11], [16631, 85349], .contexts [
        ⟨31690, false, false, [], []⟩,
        ⟨31687, false, false, [], []⟩
      ]⟩,
    ⟨[85349, 13], [23985, 46909, 89141], .contexts [
        ⟨55493, true, false, [23982], [13]⟩,
        ⟨59, false, false, [23982, 89309], []⟩,
        ⟨55494, true, false, [], [89309]⟩,
        ⟨112291, false, false, [23985], []⟩
      ]⟩,
    ⟨[85349, 15], [16633, 83667], .contexts [
        ⟨31695, false, false, [], []⟩,
        ⟨31691, false, false, [], []⟩
      ]⟩,
    ⟨[20231, 87117], [20231, 21523, 86587], .contexts [
        ⟨45463, false, false, [20231], []⟩
      ]⟩,
    ⟨[85351, 1], [20231, 21523, 86587], .contexts [
        ⟨41728, false, false, [], []⟩,
        ⟨160696, false, false, [], []⟩
      ]⟩,
    ⟨[85351, 3], [18139, 82851], .contexts [
        ⟨31707, false, false, [], []⟩,
        ⟨31717, false, false, [], []⟩
      ]⟩,
    ⟨[85351, 5], [16623, 82981], .contexts [
        ⟨31711, false, false, [], []⟩,
        ⟨23561, false, false, [], []⟩
      ]⟩,
    ⟨[85351, 7], [18135, 86333], .contexts [
        ⟨36548, true, false, [18136], [7]⟩,
        ⟨38, false, false, [18136, 86333], []⟩,
        ⟨36526, true, false, [], [86333]⟩
      ]⟩,
    ⟨[85351, 9], [85349], .contexts [
        ⟨31698, false, false, [], []⟩,
        ⟨31673, false, false, [], []⟩
      ]⟩,
    ⟨[85351, 11], [85353], .contexts [
        ⟨31728, false, false, [], []⟩,
        ⟨31730, false, false, [], []⟩
      ]⟩,
    ⟨[85351, 13], [18145, 85323], .contexts [
        ⟨31726, false, false, [], []⟩,
        ⟨41948, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2511. -/
def y322TCIndexRaw2511 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85351, 15], [16633, 83669], .contexts [
        ⟨31716, false, false, [], []⟩,
        ⟨31712, false, false, [], []⟩
      ]⟩,
    ⟨[85353, 1], [85355], .contexts [
        ⟨31748, false, false, [], []⟩,
        ⟨31751, false, false, [], []⟩
      ]⟩,
    ⟨[85353, 3], [18139, 84097], .contexts [
        ⟨31736, false, false, [], []⟩,
        ⟨31733, false, false, [], []⟩
      ]⟩,
    ⟨[85353, 5], [19355, 20313, 83639], .contexts [
        ⟨38049, true, false, [19352], [5]⟩,
        ⟨28, false, false, [19352, 86573], []⟩,
        ⟨38050, true, false, [], [86573]⟩,
        ⟨41840, false, false, [19355], []⟩
      ]⟩,
    ⟨[85353, 7], [18135, 86335], .contexts [
        ⟨36568, true, false, [18136], [7]⟩,
        ⟨38, false, false, [18136, 86335], []⟩,
        ⟨36526, true, false, [], [86335]⟩
      ]⟩,
    ⟨[85353, 9], [16631, 85353], .contexts [
        ⟨31740, false, false, [], []⟩,
        ⟨31689, true, false, [], [85353]⟩,
        ⟨31738, false, false, [], []⟩
      ]⟩,
    ⟨[85353, 11], [85351], .contexts [
        ⟨31729, false, false, [], []⟩,
        ⟨31699, false, false, [], []⟩
      ]⟩,
    ⟨[85353, 13], [21491, 46927, 89145], .contexts [
        ⟨57412, true, false, [20324], [13]⟩,
        ⟨59, false, false, [20324, 89711], []⟩,
        ⟨45399, true, false, [], [89711]⟩,
        ⟨112309, false, false, [21491], []⟩
      ]⟩,
    ⟨[85353, 15], [16633, 83671], .contexts [
        ⟨31745, false, false, [], []⟩,
        ⟨31742, false, false, [], []⟩
      ]⟩,
    ⟨[85355, 1], [85353], .contexts [
        ⟨31749, false, false, [], []⟩,
        ⟨31730, false, false, [], []⟩
      ]⟩,
    ⟨[85355, 3], [18151, 85355], .contexts [
        ⟨31763, false, false, [], []⟩,
        ⟨31756, false, false, [], []⟩
      ]⟩,
    ⟨[85355, 5], [21493, 87681], .contexts [
        ⟨45401, false, false, [], []⟩
      ]⟩,
    ⟨[85355, 7], [18135, 86337], .contexts [
        ⟨36597, false, false, [], []⟩,
        ⟨45542, false, false, [], []⟩
      ]⟩,
    ⟨[85355, 9], [21519, 86583], .contexts [
        ⟨45451, false, false, [], []⟩,
        ⟨45539, false, false, [], []⟩
      ]⟩,
    ⟨[85355, 11], [20231, 21523, 86587], .contexts [
        ⟨41957, false, false, [], []⟩,
        ⟨160696, false, false, [], []⟩
      ]⟩,
    ⟨[85355, 13], [85357], .contexts [
        ⟨31770, false, false, [], []⟩,
        ⟨31772, false, false, [], []⟩
      ]⟩,
    ⟨[85355, 15], [16633, 83673], .contexts [
        ⟨31767, false, false, [], []⟩,
        ⟨31764, false, false, [], []⟩
      ]⟩,
    ⟨[24823, 90353], [24823, 46949, 89149], .contexts [
        ⟨112339, false, false, [24823], []⟩
      ]⟩,
    ⟨[85357, 1], [24823, 46949, 89149], .contexts [
        ⟨60104, false, false, [], []⟩,
        ⟨160721, false, false, [], []⟩
      ]⟩,
    ⟨[85357, 3], [18151, 85357], .contexts [
        ⟨31780, false, false, [], []⟩,
        ⟨31775, false, false, [], []⟩
      ]⟩,
    ⟨[85357, 5], [20515, 87331], .contexts [
        ⟨42114, true, false, [20510], [5]⟩,
        ⟨41126, false, false, [20510], []⟩,
        ⟨42109, true, false, [], [19991, 87331]⟩,
        ⟨42117, true, false, [], [87331]⟩
      ]⟩,
    ⟨[85357, 7], [18135, 86339], .contexts [
        ⟨36620, true, false, [18136], [7]⟩,
        ⟨38, false, false, [18136, 86339], []⟩,
        ⟨36526, true, false, [], [86339]⟩
      ]⟩,
    ⟨[85357, 9], [20513, 41545, 86929], .contexts [
        ⟨42115, false, false, [], []⟩,
        ⟨106412, false, false, [20513], []⟩
      ]⟩,
    ⟨[85357, 11], [20513, 41119, 86933], .contexts [
        ⟨42112, false, false, [], []⟩,
        ⟨106036, false, false, [20513], []⟩
      ]⟩,
    ⟨[85357, 13], [85355], .contexts [
        ⟨31771, false, false, [], []⟩,
        ⟨31751, false, false, [], []⟩
      ]⟩,
    ⟨[85357, 15], [85359], .contexts [
        ⟨31782, false, false, [], []⟩,
        ⟨31784, false, false, [], []⟩
      ]⟩,
    ⟨[85359, 1], [85361], .contexts [
        ⟨31801, false, false, [], []⟩,
        ⟨86122, false, false, [], []⟩
      ]⟩,
    ⟨[85359, 3], [18151, 85359], .contexts [
        ⟨31792, false, false, [], []⟩,
        ⟨31787, false, false, [], []⟩
      ]⟩,
    ⟨[94759], [40329, 46979, 89157], .contexts [
        ⟨105402, false, false, [], []⟩,
        ⟨114009, false, false, [], []⟩
      ]⟩,
    ⟨[85359, 5], [31795, 40329, 46979, 89157], .contexts [
        ⟨86110, false, false, [], []⟩,
        ⟨160732, false, false, [31795], []⟩
      ]⟩,
    ⟨[85359, 7], [18135, 86341], .contexts [
        ⟨36640, false, false, [], []⟩,
        ⟨140613, false, false, [], []⟩
      ]⟩,
    ⟨[85359, 9], [96769], .contexts [
        ⟨140598, false, false, [], []⟩,
        ⟨140599, false, false, [], []⟩
      ]⟩,
    ⟨[85359, 11], [39165, 93815], .contexts [
        ⟨111347, false, false, [], []⟩,
        ⟨111344, false, false, [], []⟩
      ]⟩,
    ⟨[85359, 13], [16633, 83677], .contexts [
        ⟨31798, false, false, [], []⟩,
        ⟨31794, false, false, [], []⟩
      ]⟩,
    ⟨[85359, 15], [85357], .contexts [
        ⟨31783, false, false, [], []⟩,
        ⟨31772, false, false, [], []⟩
      ]⟩,
    ⟨[85361, 1], [85359], .contexts [
        ⟨31802, false, false, [], []⟩,
        ⟨31784, false, false, [], []⟩
      ]⟩,
    ⟨[85361, 3], [85363], .contexts [
        ⟨31804, false, false, [], []⟩,
        ⟨31807, false, false, [], []⟩
      ]⟩,
    ⟨[94757], [39159, 46991, 89159], .contexts [
        ⟨104203, false, false, [], []⟩,
        ⟨144595, false, false, [], []⟩
      ]⟩,
    ⟨[85361, 5], [31795, 39159, 46991, 89159], .contexts [
        ⟨86125, true, false, [31792], [5]⟩,
        ⟨28, false, false, [31792, 94757], []⟩,
        ⟨86108, true, false, [], [94757]⟩,
        ⟨160741, false, false, [31795], []⟩
      ]⟩,
    ⟨[85361, 7], [18135, 39045, 84103], .contexts [
        ⟨36653, true, false, [18136], [7]⟩,
        ⟨38, false, false, [18136, 86343], []⟩,
        ⟨36526, true, false, [], [86343]⟩,
        ⟨104100, false, false, [18135], []⟩
      ]⟩,
    ⟨[85361, 9], [32599, 89323], .contexts [
        ⟨88551, false, false, [], []⟩,
        ⟨140602, false, false, [], []⟩
      ]⟩,
    ⟨[85361, 11], [39165, 93813], .contexts [
        ⟨104215, false, false, [], []⟩,
        ⟨111342, false, false, [], []⟩
      ]⟩,
    ⟨[85361, 13], [39167, 85707], .contexts [
        ⟨104212, false, false, [], []⟩
      ]⟩,
    ⟨[85361, 15], [24823, 46949, 89149], .contexts [
        ⟨60131, false, false, [], []⟩,
        ⟨160721, false, false, [], []⟩
      ]⟩,
    ⟨[85363, 1], [18151, 85363], .contexts [
        ⟨31819, false, false, [], []⟩,
        ⟨31814, false, false, [], []⟩
      ]⟩,
    ⟨[85363, 3], [85361], .contexts [
        ⟨31806, false, false, [], []⟩,
        ⟨86122, false, false, [], []⟩
      ]⟩,
    ⟨[85365], [26275, 85363], .contexts [
        ⟨66185, false, false, [], []⟩
      ]⟩,
    ⟨[85363, 5], [26275, 85363], .contexts [
        ⟨31821, false, false, [], []⟩,
        ⟨160750, false, false, [], []⟩
      ]⟩,
    ⟨[85363, 7], [18135, 43525, 83801], .contexts [
        ⟨36668, false, false, [], []⟩,
        ⟨108339, false, false, [18135], []⟩
      ]⟩,
    ⟨[85363, 9], [26273, 85367], .contexts [
        ⟨66189, false, false, [], []⟩
      ]⟩,
    ⟨[85363, 11], [26291, 87317], .contexts [
        ⟨66213, false, false, [], []⟩
      ]⟩,
    ⟨[85363, 13], [26283, 43533, 86317], .contexts [
        ⟨66202, false, false, [], []⟩,
        ⟨108346, false, false, [26283], []⟩
      ]⟩,
    ⟨[85363, 15], [26267, 91489], .contexts [
        ⟨66161, true, false, [26264], [15]⟩,
        ⟨1, false, false, [26264, 91489], []⟩,
        ⟨66162, true, false, [], [91489]⟩
      ]⟩,
    ⟨[32569, 94073], [32569, 41191, 91833], .contexts [
        ⟨106099, false, false, [32569], []⟩
      ]⟩,
    ⟨[85367, 1], [32569, 41191, 91833], .contexts [
        ⟨88524, false, false, [], []⟩,
        ⟨160757, false, false, [], []⟩
      ]⟩,
    ⟨[85367, 3], [32571, 89323], .contexts [
        ⟨88523, false, false, [], []⟩,
        ⟨88548, false, false, [], []⟩
      ]⟩,
    ⟨[85367, 5], [26299, 85367], .contexts [
        ⟨66229, false, false, [], []⟩,
        ⟨66237, false, false, [], []⟩
      ]⟩,
    ⟨[85367, 7], [41183, 83799], .contexts [
        ⟨106091, true, false, [41180], [7]⟩,
        ⟨70411, false, false, [41180], []⟩,
        ⟨24813, false, false, [41180], []⟩,
        ⟨106092, true, false, [], [16867, 83799]⟩,
        ⟨106093, true, false, [], [83799]⟩
      ]⟩,
    ⟨[85367, 9], [26275, 85363], .contexts [
        ⟨31829, false, false, [], []⟩,
        ⟨160750, false, false, [], []⟩
      ]⟩,
    ⟨[85367, 11], [85369], .contexts [
        ⟨31831, false, false, [], []⟩,
        ⟨32128, false, false, [], []⟩
      ]⟩,
    ⟨[85367, 13], [41185, 86319], .contexts [
        ⟨106091, true, false, [41180], [13]⟩,
        ⟨70419, false, false, [41180], []⟩,
        ⟨83218, false, false, [41180], []⟩,
        ⟨106092, true, false, [], [27427, 86319]⟩,
        ⟨106094, true, false, [], [86319]⟩
      ]⟩,
    ⟨[85367, 15], [26289, 91487], .contexts [
        ⟨66210, false, false, [], []⟩,
        ⟨88553, false, false, [], []⟩
      ]⟩,
    ⟨[85369, 1], [85371], .contexts [
        ⟨31835, false, false, [], []⟩,
        ⟨32126, false, false, [], []⟩
      ]⟩,
    ⟨[85369, 3], [32571, 89321], .contexts [
        ⟨88513, false, false, [], []⟩,
        ⟨88628, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2512. -/
def y322TCIndexRaw2512 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85369, 5], [26307, 85369], .contexts [
        ⟨66243, false, false, [], []⟩,
        ⟨66251, false, false, [], []⟩
      ]⟩,
    ⟨[85369, 7], [32575, 39211, 85319], .contexts [
        ⟨88520, false, false, [], []⟩,
        ⟨104275, false, false, [32575], []⟩
      ]⟩,
    ⟨[85369, 9], [32569, 39249, 93285], .contexts [
        ⟨88510, false, false, [], []⟩,
        ⟨104320, false, false, [32569], []⟩
      ]⟩,
    ⟨[85369, 11], [85367], .contexts [
        ⟨31833, false, false, [], []⟩,
        ⟨32130, false, false, [], []⟩
      ]⟩,
    ⟨[85369, 13], [32573, 39317, 86321], .contexts [
        ⟨88518, false, false, [], []⟩,
        ⟨104382, false, false, [32573], []⟩
      ]⟩,
    ⟨[95137], [34105, 39305, 94183], .contexts [
        ⟨92991, false, false, [], []⟩,
        ⟨106073, false, false, [], []⟩
      ]⟩,
    ⟨[85369, 15], [32565, 34105, 39305, 94183], .contexts [
        ⟨88502, false, false, [], []⟩,
        ⟨160773, false, false, [32565], []⟩
      ]⟩,
    ⟨[85371, 1], [85369], .contexts [
        ⟨31837, false, false, [], []⟩,
        ⟨32128, false, false, [], []⟩
      ]⟩,
    ⟨[85371, 3], [41481, 81393], .contexts [
        ⟨88625, false, false, [], []⟩,
        ⟨106355, false, false, [], []⟩
      ]⟩,
    ⟨[85371, 5], [26299, 85371], .contexts [
        ⟨66259, false, false, [], []⟩,
        ⟨66265, false, false, [], []⟩
      ]⟩,
    ⟨[85371, 7], [32575, 41473, 86593], .contexts [
        ⟨88546, false, false, [], []⟩,
        ⟨106349, false, false, [32575], []⟩
      ]⟩,
    ⟨[85371, 9], [32627, 95027], .contexts [
        ⟨88599, false, false, [], []⟩,
        ⟨88604, false, false, [], []⟩
      ]⟩,
    ⟨[85371, 11], [32569, 41191, 91833], .contexts [
        ⟨88532, true, false, [32566], [11]⟩,
        ⟨53, false, false, [32566, 94073], []⟩,
        ⟨88506, true, false, [], [94073]⟩,
        ⟨160757, false, false, [], []⟩
      ]⟩,
    ⟨[85371, 13], [85373], .contexts [
        ⟨31839, false, false, [], []⟩,
        ⟨32125, false, false, [], []⟩
      ]⟩,
    ⟨[85371, 15], [34163, 41203, 92825], .contexts [
        ⟨93050, true, false, [34160], [15]⟩,
        ⟨1, false, false, [34160, 94731], []⟩,
        ⟨93051, true, false, [], [94731]⟩,
        ⟨106109, false, false, [34163], []⟩
      ]⟩,
    ⟨[85373, 1], [41239, 86325], .contexts [
        ⟨106132, true, false, [41234], [1]⟩,
        ⟨54526, false, false, [41234], []⟩,
        ⟨54650, false, false, [41234], []⟩,
        ⟨106133, true, false, [], [23687, 86325]⟩,
        ⟨106134, true, false, [], [86325]⟩
      ]⟩,
    ⟨[85373, 3], [41241, 82823], .contexts [
        ⟨106132, true, false, [41234], [3]⟩,
        ⟨54628, false, false, [41234], []⟩,
        ⟨54632, false, false, [41234], []⟩,
        ⟨106133, true, false, [], [23675, 82823]⟩,
        ⟨106135, true, false, [], [82823]⟩
      ]⟩,
    ⟨[85373, 5], [26307, 85373], .contexts [
        ⟨66271, false, false, [], []⟩,
        ⟨66277, false, false, [], []⟩
      ]⟩,
    ⟨[85373, 7], [41243, 87575], .contexts [
        ⟨106132, true, false, [41234], [7]⟩,
        ⟨54662, true, false, [41234, 23698], [7]⟩,
        ⟨38, false, false, [41234, 23698, 87575], []⟩,
        ⟨54660, false, true, [41234], [87575]⟩,
        ⟨106133, true, false, [], [23697, 87575]⟩,
        ⟨106137, true, false, [], [87575]⟩
      ]⟩,
    ⟨[85373, 9], [32627, 41229, 92505], .contexts [
        ⟨88608, true, false, [32628], [9]⟩,
        ⟨46, false, false, [32628, 95029], []⟩,
        ⟨88609, true, false, [], [95029]⟩,
        ⟨106128, false, false, [32627], []⟩
      ]⟩,
    ⟨[85373, 11], [32569, 41249, 91255], .contexts [
        ⟨88565, false, false, [], []⟩,
        ⟨106141, false, false, [32569], []⟩
      ]⟩,
    ⟨[85373, 13], [85371], .contexts [
        ⟨31841, false, false, [], []⟩,
        ⟨32126, false, false, [], []⟩
      ]⟩,
    ⟨[85373, 15], [85375], .contexts [
        ⟨31843, false, false, [], []⟩,
        ⟨32124, false, false, [], []⟩
      ]⟩,
    ⟨[85375, 1], [85377], .contexts [
        ⟨31847, false, false, [], []⟩,
        ⟨32122, false, false, [], []⟩
      ]⟩,
    ⟨[85375, 3], [41263, 82813], .contexts [
        ⟨106149, true, false, [41258], [3]⟩,
        ⟨36435, false, false, [41258], []⟩,
        ⟨36438, false, false, [41258], []⟩,
        ⟨106152, true, false, [], [82813]⟩
      ]⟩,
    ⟨[85375, 5], [26299, 85375], .contexts [
        ⟨66283, false, false, [], []⟩,
        ⟨66288, false, false, [], []⟩
      ]⟩,
    ⟨[85375, 7], [41263, 87201], .contexts [
        ⟨106149, true, false, [41258], [7]⟩,
        ⟨40324, true, false, [41258, 19022], [7]⟩,
        ⟨38, false, false, [41258, 19022, 87201], []⟩,
        ⟨40325, true, false, [41258], [87201]⟩,
        ⟨106152, true, false, [], [87201]⟩
      ]⟩,
    ⟨[85375, 9], [32627, 41271, 90479], .contexts [
        ⟨88617, false, false, [], []⟩,
        ⟨106160, false, false, [32627], []⟩
      ]⟩,
    ⟨[85375, 11], [32569, 41251, 89439], .contexts [
        ⟨88572, true, false, [32566], [11]⟩,
        ⟨53, false, false, [32566, 94077], []⟩,
        ⟨88506, true, false, [], [94077]⟩,
        ⟨106144, false, false, [32569], []⟩
      ]⟩,
    ⟨[85375, 13], [41265, 48477, 88851], .contexts [
        ⟨106156, false, false, [], []⟩,
        ⟨113816, false, false, [41265], []⟩
      ]⟩,
    ⟨[85375, 15], [85373], .contexts [
        ⟨31845, false, false, [], []⟩,
        ⟨32125, false, false, [], []⟩
      ]⟩,
    ⟨[85377, 1], [85375], .contexts [
        ⟨31849, false, false, [], []⟩,
        ⟨32124, false, false, [], []⟩
      ]⟩,
    ⟨[85377, 3], [85379], .contexts [
        ⟨31851, false, false, [], []⟩,
        ⟨32121, false, false, [], []⟩
      ]⟩,
    ⟨[85377, 5], [26307, 85377], .contexts [
        ⟨31847, true, false, [], [5]⟩,
        ⟨66289, true, false, [26298], [1, 5]⟩,
        ⟨66289, true, false, [26298], [1, 5]⟩,
        ⟨66288, true, false, [26298], [1, 5]⟩,
        ⟨66283, true, false, [26298], [1, 5]⟩,
        ⟨66281, true, false, [26298], [1, 5]⟩,
        ⟨890, false, false, [26298, 85375], []⟩,
        ⟨9, false, false, [26298, 85375], []⟩,
        ⟨31847, false, false, [26298], []⟩,
        ⟨32122, false, false, [26298], []⟩,
        ⟨31852, false, false, [26298], []⟩,
        ⟨31852, false, false, [26298], []⟩,
        ⟨66242, true, false, [], [85377]⟩
      ]⟩,
    ⟨[85377, 7], [41295, 86923], .contexts [
        ⟨106190, true, false, [41258], [7]⟩,
        ⟨40345, false, false, [41258], []⟩,
        ⟨54672, false, false, [41258], []⟩,
        ⟨106150, true, false, [], [19851, 86923]⟩,
        ⟨106194, true, false, [], [86923]⟩
      ]⟩,
    ⟨[85377, 9], [41301, 95369], .contexts [
        ⟨106190, true, false, [41258], [9]⟩,
        ⟨89691, false, false, [41258], []⟩,
        ⟨106150, true, false, [], [32873, 95369]⟩,
        ⟨106197, true, false, [], [95369]⟩
      ]⟩,
    ⟨[85377, 11], [32569, 41307, 89437], .contexts [
        ⟨88591, false, false, [], []⟩,
        ⟨106201, false, false, [32569], []⟩
      ]⟩,
    ⟨[85377, 13], [41299, 84113], .contexts [
        ⟨106190, true, false, [41258], [13]⟩,
        ⟨54649, false, false, [41258], []⟩,
        ⟨105878, false, false, [41258, 23685], []⟩,
        ⟨106150, true, false, [], [23685, 40913, 84113]⟩,
        ⟨106195, true, false, [], [40913, 84113]⟩,
        ⟨106196, true, false, [], [84113]⟩
      ]⟩,
    ⟨[85377, 15], [41261, 86325], .contexts [
        ⟨106190, true, false, [41258], [15]⟩,
        ⟨36335, false, false, [41258], []⟩,
        ⟨36341, false, false, [41258], []⟩,
        ⟨106191, true, false, [], [86325]⟩,
        ⟨106191, true, false, [], [86325]⟩,
        ⟨106189, true, false, [], [86325]⟩
      ]⟩,
    ⟨[85379, 1], [41321, 87803], .contexts [
        ⟨106210, true, false, [41318], [1]⟩,
        ⟨46056, false, false, [41318], []⟩,
        ⟨46059, false, false, [41318], []⟩,
        ⟨106213, true, false, [], [87803]⟩
      ]⟩,
    ⟨[85379, 3], [85377], .contexts [
        ⟨31853, false, false, [], []⟩,
        ⟨32122, false, false, [], []⟩
      ]⟩,
    ⟨[85379, 5], [41333, 84483], .contexts [
        ⟨31855, false, false, [], []⟩,
        ⟨106224, false, false, [], []⟩
      ]⟩,
    ⟨[85379, 7], [41323, 41383, 85389], .contexts [
        ⟨106210, true, false, [41318], [7]⟩,
        ⟨46212, true, false, [41318, 21748], [7]⟩,
        ⟨38, false, false, [41318, 21748, 86221], []⟩,
        ⟨46213, true, false, [41318], [86221]⟩,
        ⟨106211, true, false, [], [21747, 86221]⟩,
        ⟨106214, true, false, [], [86221]⟩,
        ⟨106307, false, false, [41323], []⟩
      ]⟩,
    ⟨[85379, 9], [41327, 85669], .contexts [
        ⟨106217, false, false, [], []⟩
      ]⟩,
    ⟨[85379, 11], [32569, 41311, 90521], .contexts [
        ⟨88603, true, false, [32566], [11]⟩,
        ⟨53, false, false, [32566, 94081], []⟩,
        ⟨88506, true, false, [], [94081]⟩,
        ⟨106206, false, false, [32569], []⟩
      ]⟩,
    ⟨[85379, 13], [41331, 84115], .contexts [
        ⟨106220, false, false, [], []⟩
      ]⟩,
    ⟨[85379, 15], [41321, 47141, 86523], .contexts [
        ⟨106210, true, false, [41318], [15]⟩,
        ⟨46054, false, false, [41318], []⟩,
        ⟨46061, false, false, [41318], []⟩,
        ⟨106213, true, false, [], [87799]⟩,
        ⟨112524, false, false, [41321], []⟩
      ]⟩,
    ⟨[85385, 1], [41365, 88211], .contexts [
        ⟨106249, true, false, [41366], [1]⟩,
        ⟨49261, false, false, [41366], []⟩,
        ⟨49263, false, false, [41366], []⟩,
        ⟨106252, true, false, [], [88211]⟩
      ]⟩,
    ⟨[85385, 3], [41369, 82663], .contexts [
        ⟨106249, true, false, [41366], [3]⟩,
        ⟨49240, false, false, [41366], []⟩,
        ⟨106250, true, false, [], [22519, 82663]⟩,
        ⟨106253, true, false, [], [82663]⟩
      ]⟩,
    ⟨[85385, 5], [41365, 88207], .contexts [
        ⟨106249, true, false, [41366], [5]⟩,
        ⟨49234, false, false, [41366], []⟩,
        ⟨49206, false, false, [41366], []⟩,
        ⟨106252, true, false, [], [88207]⟩
      ]⟩,
    ⟨[85385, 7], [41379, 90523], .contexts [
        ⟨106249, true, false, [41366], [7]⟩,
        ⟨61623, false, false, [41366], []⟩,
        ⟨103712, false, false, [41366, 25197], []⟩,
        ⟨106250, true, false, [], [25197, 38709, 90523]⟩,
        ⟨106259, true, false, [], [38709, 90523]⟩,
        ⟨106260, true, false, [], [90523]⟩
      ]⟩,
    ⟨[85385, 9], [41363, 84485], .contexts [
        ⟨31863, false, false, [], []⟩,
        ⟨106246, false, false, [], []⟩
      ]⟩,
    ⟨[85385, 11], [85387], .contexts [
        ⟨31865, false, false, [], []⟩,
        ⟨32117, false, false, [], []⟩
      ]⟩,
    ⟨[85385, 13], [41373, 85385], .contexts [
        ⟨106249, true, false, [41366], [13]⟩,
        ⟨49255, false, false, [41366], []⟩,
        ⟨106255, false, false, [41366, 2575], []⟩,
        ⟨106250, true, false, [], [2575, 41367, 85385]⟩,
        ⟨106256, true, false, [], [41367, 85385]⟩,
        ⟨106257, true, false, [], [85385]⟩
      ]⟩,
    ⟨[85385, 15], [41375, 83373], .contexts [
        ⟨106249, true, false, [41366], [15]⟩,
        ⟨49259, false, false, [41366], []⟩,
        ⟨49256, false, false, [41366], []⟩,
        ⟨106250, true, false, [], [16221, 83373]⟩,
        ⟨106258, true, false, [], [83373]⟩
      ]⟩,
    ⟨[85387, 1], [85389], .contexts [
        ⟨31869, false, false, [], []⟩,
        ⟨32116, false, false, [], []⟩
      ]⟩,
    ⟨[85387, 3], [41385, 82815], .contexts [
        ⟨106263, true, false, [41382], [3]⟩,
        ⟨35809, false, false, [41382], []⟩,
        ⟨35804, false, false, [41382], []⟩,
        ⟨106266, true, false, [], [82815]⟩
      ]⟩,
    ⟨[85387, 5], [41401, 85677], .contexts [
        ⟨106263, true, false, [41382], [5]⟩,
        ⟨48715, false, false, [41382], []⟩,
        ⟨106276, false, false, [41382, 22323], []⟩,
        ⟨106278, true, false, [], [41397, 85677]⟩,
        ⟨106279, true, false, [], [85677]⟩
      ]⟩,
    ⟨[85387, 7], [41393, 87803], .contexts [
        ⟨106263, true, false, [41382], [7]⟩,
        ⟨46191, false, false, [41382], []⟩,
        ⟨106264, true, false, [], [21733, 87803]⟩,
        ⟨106272, true, false, [], [87803]⟩
      ]⟩,
    ⟨[85387, 9], [32569, 41407, 83329], .contexts [
        ⟨88623, false, false, [], []⟩,
        ⟨106283, false, false, [32569], []⟩
      ]⟩,
    ⟨[85387, 11], [85385], .contexts [
        ⟨31867, false, false, [], []⟩,
        ⟨32119, false, false, [], []⟩
      ]⟩,
    ⟨[85387, 13], [41389, 85387], .contexts [
        ⟨106263, true, false, [41382], [13]⟩,
        ⟨35822, false, false, [41382, 18930], [86223, 13]⟩,
        ⟨35811, true, false, [41382, 18930, 18929], [13]⟩,
        ⟨35821, false, false, [41382, 18930], [82815, 3, 13]⟩,
        ⟨16990, true, false, [41382, 18930, 18921], [3, 13]⟩,
        ⟨35812, true, false, [41382, 18930], [13, 3, 13]⟩,
        ⟨1930, false, false, [41382, 18930, 86223], []⟩,
        ⟨35814, false, false, [41382, 18930], []⟩,
        ⟨35815, false, false, [41382, 18930], []⟩,
        ⟨35824, true, false, [41382], [86223]⟩,
        ⟨35824, true, false, [41382], [86223]⟩,
        ⟨35823, true, false, [41382], [86223]⟩,
        ⟨106268, false, false, [41382, 18933], []⟩,
        ⟨106264, true, false, [], [18933, 41383, 85387]⟩,
        ⟨106269, true, false, [], [41383, 85387]⟩,
        ⟨106270, true, false, [], [85387]⟩
      ]⟩,
    ⟨[85387, 15], [41391, 85257], .contexts [
        ⟨106263, true, false, [41382], [15]⟩,
        ⟨35832, false, false, [41382], []⟩,
        ⟨42683, false, false, [41382, 18921], []⟩,
        ⟨106266, true, false, [], [20761, 85257]⟩,
        ⟨106271, true, false, [], [85257]⟩
      ]⟩,
    ⟨[85389, 1], [85387], .contexts [
        ⟨31871, false, false, [], []⟩,
        ⟨32117, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2513. -/
def y322TCIndexRaw2513 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85389, 3], [41421, 86923], .contexts [
        ⟨106299, true, false, [41382], [3]⟩,
        ⟨40358, false, false, [41382], []⟩,
        ⟨106264, true, false, [], [19859, 86923]⟩,
        ⟨106301, true, false, [], [86923]⟩
      ]⟩,
    ⟨[85389, 5], [41429, 85675], .contexts [
        ⟨106299, true, false, [41382], [5]⟩,
        ⟨48743, true, false, [41382, 22320], [5]⟩,
        ⟨28, false, false, [41382, 22320, 88201], []⟩,
        ⟨48713, true, false, [41382], [88201]⟩,
        ⟨105615, false, false, [41382, 22323], []⟩,
        ⟨106278, true, false, [], [40607, 85675]⟩,
        ⟨106305, true, false, [], [85675]⟩
      ]⟩,
    ⟨[85389, 7], [41427, 85379], .contexts [
        ⟨106299, true, false, [41382], [7]⟩,
        ⟨46212, false, false, [41382], []⟩,
        ⟨106222, false, false, [41382, 21749], []⟩,
        ⟨106264, true, false, [], [21749, 41319, 85379]⟩,
        ⟨106303, true, false, [], [41319, 85379]⟩,
        ⟨106304, true, false, [], [85379]⟩
      ]⟩,
    ⟨[85389, 9], [41423, 83899], .contexts [
        ⟨106299, true, false, [41382], [9]⟩,
        ⟨40362, false, false, [41382], []⟩,
        ⟨40378, false, false, [41382], []⟩,
        ⟨106264, true, false, [], [19861, 83899]⟩,
        ⟨106302, true, false, [], [83899]⟩
      ]⟩,
    ⟨[85389, 11], [41431, 88211], .contexts [
        ⟨106299, true, false, [41382], [11]⟩,
        ⟨49269, false, false, [41382], []⟩,
        ⟨106264, true, false, [], [22529, 88211]⟩,
        ⟨106306, true, false, [], [88211]⟩
      ]⟩,
    ⟨[85389, 13], [85391], .contexts [
        ⟨31873, false, false, [], []⟩,
        ⟨32115, false, false, [], []⟩
      ]⟩,
    ⟨[85389, 15], [41419, 85255], .contexts [
        ⟨106299, true, false, [41382], [15]⟩,
        ⟨35694, false, false, [41382], []⟩,
        ⟨46242, false, false, [41382], []⟩,
        ⟨106298, true, false, [], [20751, 85255]⟩,
        ⟨106300, true, false, [], [85255]⟩
      ]⟩,
    ⟨[85391, 1], [41439, 85391], .contexts [
        ⟨106310, true, false, [41434], [1]⟩,
        ⟨63872, false, false, [41434], []⟩,
        ⟨106317, false, false, [41434, 25719], []⟩,
        ⟨106311, true, false, [], [25719, 41435, 85391]⟩,
        ⟨106318, true, false, [], [41435, 85391]⟩,
        ⟨106319, true, false, [], [85391]⟩
      ]⟩,
    ⟨[85391, 3], [41441, 87111], .contexts [
        ⟨106321, false, false, [], []⟩,
        ⟨113607, false, false, [], []⟩
      ]⟩,
    ⟨[85391, 5], [41445, 93825], .contexts [
        ⟨106324, false, false, [], []⟩,
        ⟨114508, false, false, [], []⟩
      ]⟩,
    ⟨[85391, 7], [41449, 84115], .contexts [
        ⟨106310, true, false, [41434], [7]⟩,
        ⟨98101, false, false, [41434], []⟩,
        ⟨105825, false, false, [41434, 35695], []⟩,
        ⟨106311, true, false, [], [35695, 40859, 84115]⟩,
        ⟨106325, true, false, [], [40859, 84115]⟩,
        ⟨106326, true, false, [], [84115]⟩
      ]⟩,
    ⟨[85391, 9], [41433, 71105, 90021], .contexts [
        ⟨106314, false, false, [], []⟩,
        ⟨139944, false, false, [41433], []⟩
      ]⟩,
    ⟨[85391, 11], [41433, 91001], .contexts [
        ⟨106315, false, false, [], []⟩,
        ⟨113598, false, false, [], []⟩
      ]⟩,
    ⟨[85391, 13], [85389], .contexts [
        ⟨31875, false, false, [], []⟩,
        ⟨32116, false, false, [], []⟩
      ]⟩,
    ⟨[85391, 15], [85393], .contexts [
        ⟨31877, false, false, [], []⟩,
        ⟨32114, false, false, [], []⟩
      ]⟩,
    ⟨[85395], [41465, 85393], .contexts [
        ⟨113947, false, false, [], []⟩
      ]⟩,
    ⟨[85393, 1], [41465, 85393], .contexts [
        ⟨31881, false, false, [], []⟩,
        ⟨160847, false, false, [], []⟩
      ]⟩,
    ⟨[85393, 3], [41467, 85397], .contexts [
        ⟨106345, false, false, [], []⟩,
        ⟨113611, false, false, [], []⟩
      ]⟩,
    ⟨[85393, 5], [48621, 89799], .contexts [
        ⟨113958, false, false, [], []⟩,
        ⟨114506, false, false, [], []⟩
      ]⟩,
    ⟨[85393, 7], [41461, 96543], .contexts [
        ⟨106329, true, false, [41452], [7]⟩,
        ⟨98121, true, false, [41452, 35708], [7]⟩,
        ⟨38, false, false, [41452, 35708, 96543], []⟩,
        ⟨98122, true, false, [41452], [96543]⟩,
        ⟨106330, true, false, [], [35711, 96543]⟩,
        ⟨106339, true, false, [], [96543]⟩
      ]⟩,
    ⟨[85393, 9], [41459, 87979], .contexts [
        ⟨106338, false, false, [], []⟩,
        ⟨114533, false, false, [], []⟩
      ]⟩,
    ⟨[85393, 11], [41455, 83681], .contexts [
        ⟨106335, false, false, [], []⟩,
        ⟨114525, false, false, [], []⟩
      ]⟩,
    ⟨[85393, 13], [41451, 91365], .contexts [
        ⟨106329, true, false, [41452], [13]⟩,
        ⟨65493, false, false, [41452], []⟩,
        ⟨65596, false, false, [41452], []⟩,
        ⟨106331, true, false, [], [91365]⟩,
        ⟨106331, true, false, [], [91365]⟩,
        ⟨106330, true, false, [], [91365]⟩
      ]⟩,
    ⟨[85393, 15], [85391], .contexts [
        ⟨31879, false, false, [], []⟩,
        ⟨32115, false, false, [], []⟩
      ]⟩,
    ⟨[85397, 1], [48615, 89793], .contexts [
        ⟨113945, true, false, [48616], [1]⟩,
        ⟨57616, false, false, [48616], []⟩,
        ⟨57730, false, false, [48616], []⟩,
        ⟨113946, true, false, [], [89793]⟩,
        ⟨113946, true, false, [], [89793]⟩,
        ⟨113944, false, true, [], [89793]⟩
      ]⟩,
    ⟨[85397, 3], [41465, 85393], .contexts [
        ⟨31886, false, false, [], []⟩,
        ⟨160847, false, false, [], []⟩
      ]⟩,
    ⟨[85397, 5], [85399], .contexts [
        ⟨31888, false, false, [], []⟩,
        ⟨32111, false, false, [], []⟩
      ]⟩,
    ⟨[85397, 7], [76197, 97241], .contexts [
        ⟨147893, true, false, [76194], [7]⟩,
        ⟨38, false, false, [76194, 97241], []⟩,
        ⟨147894, true, false, [], [97241]⟩
      ]⟩,
    ⟨[85397, 9], [44587, 96287], .contexts [
        ⟨109499, false, false, [], []⟩
      ]⟩,
    ⟨[85397, 11], [48609, 83679], .contexts [
        ⟨113936, true, false, [48606], [11]⟩,
        ⟨53, false, false, [48606, 83679], []⟩,
        ⟨113937, true, false, [], [83679]⟩
      ]⟩,
    ⟨[85397, 13], [72981, 96887], .contexts [
        ⟨142907, true, false, [72978], [13]⟩,
        ⟨59, false, false, [72978, 96887], []⟩,
        ⟨142908, true, false, [], [96887]⟩
      ]⟩,
    ⟨[85397, 15], [48293, 87111], .contexts [
        ⟨113617, true, false, [48290], [15]⟩,
        ⟨1, false, false, [48290, 87111], []⟩,
        ⟨113618, true, false, [], [87111]⟩
      ]⟩,
    ⟨[85399, 1], [85401], .contexts [
        ⟨31892, false, false, [], []⟩,
        ⟨32110, false, false, [], []⟩
      ]⟩,
    ⟨[85399, 3], [48785, 95049], .contexts [
        ⟨114110, false, false, [], []⟩
      ]⟩,
    ⟨[85399, 5], [85397], .contexts [
        ⟨31890, false, false, [], []⟩,
        ⟨32112, false, false, [], []⟩
      ]⟩,
    ⟨[85399, 7], [48763, 85399], .contexts [
        ⟨114094, false, false, [48758], [85399, 7]⟩,
        ⟨113962, true, false, [48758, 15743], [7]⟩,
        ⟨18175, true, false, [48758], [15, 7]⟩,
        ⟨18155, false, false, [48758, 82973], []⟩,
        ⟨113967, false, false, [48758], []⟩,
        ⟨113966, false, false, [48758], []⟩,
        ⟨113960, false, false, [48758, 48623], []⟩,
        ⟨114095, true, false, [], [48623, 85399]⟩,
        ⟨114096, true, false, [], [85399]⟩
      ]⟩,
    ⟨[85399, 9], [73819, 96961], .contexts [
        ⟨144255, true, false, [73816], [9]⟩,
        ⟨46, false, false, [73816, 96961], []⟩,
        ⟨144256, true, false, [], [96961]⟩
      ]⟩,
    ⟨[85399, 11], [48629, 48657, 85407], .contexts [
        ⟨113969, true, false, [48626], [11]⟩,
        ⟨53, false, false, [48626, 85859], []⟩,
        ⟨113970, true, false, [], [85859]⟩,
        ⟨114016, false, false, [48629], []⟩
      ]⟩,
    ⟨[85399, 13], [48777, 85829], .contexts [
        ⟨114103, true, false, [48774], [13]⟩,
        ⟨59, false, false, [48774, 85829], []⟩,
        ⟨114104, true, false, [], [85829]⟩
      ]⟩,
    ⟨[85399, 15], [48625, 82973], .contexts [
        ⟨113962, true, false, [48622], [15]⟩,
        ⟨1, false, false, [48622, 82973], []⟩,
        ⟨113963, true, false, [], [82973]⟩
      ]⟩,
    ⟨[85401, 1], [85399], .contexts [
        ⟨31894, false, false, [], []⟩,
        ⟨32111, false, false, [], []⟩
      ]⟩,
    ⟨[85401, 3], [48643, 88919], .contexts [
        ⟨113975, true, false, [48630], [3]⟩,
        ⟨79252, true, false, [48630, 30106], [3]⟩,
        ⟨20, false, false, [48630, 30106, 93423], []⟩,
        ⟨79224, true, false, [48630], [93423]⟩,
        ⟨113921, false, false, [48630, 30109], []⟩,
        ⟨113973, true, false, [], [30109, 48587, 88919]⟩,
        ⟨113983, true, false, [], [48587, 88919]⟩,
        ⟨113984, true, false, [], [88919]⟩
      ]⟩,
    ⟨[85401, 5], [48645, 89793], .contexts [
        ⟨113986, false, false, [], []⟩
      ]⟩,
    ⟨[85401, 7], [48637, 85401], .contexts [
        ⟨113975, true, false, [48630], [7]⟩,
        ⟨70639, true, false, [48630], [7]⟩,
        ⟨73, false, false, [48630, 92193], []⟩,
        ⟨74, false, false, [48630, 92193], []⟩,
        ⟨70618, false, false, [48630], [13]⟩,
        ⟨70620, false, false, [48630], [13]⟩,
        ⟨70616, false, false, [48630], [13]⟩,
        ⟨70617, false, false, [48630], [13]⟩,
        ⟨70617, false, false, [48630], [13]⟩,
        ⟨70634, false, false, [48630, 16865], []⟩,
        ⟨70640, false, false, [48630, 16865], []⟩,
        ⟨24802, true, false, [48630], [92195]⟩,
        ⟨113979, false, false, [48630, 16865], []⟩,
        ⟨113973, true, false, [], [16865, 48631, 85401]⟩,
        ⟨113980, true, false, [], [48631, 85401]⟩,
        ⟨113981, true, false, [], [85401]⟩
      ]⟩,
    ⟨[85403], [48653, 85401], .contexts [
        ⟨113992, false, false, [], []⟩
      ]⟩,
    ⟨[85401, 9], [48653, 85401], .contexts [
        ⟨31896, false, false, [], []⟩,
        ⟨160876, false, false, [], []⟩
      ]⟩,
    ⟨[85401, 11], [48649, 48657, 85405], .contexts [
        ⟨113989, false, false, [], []⟩,
        ⟨114003, false, false, [48649], []⟩
      ]⟩,
    ⟨[85401, 13], [48633, 92193], .contexts [
        ⟨113975, true, false, [48630], [13]⟩,
        ⟨70635, false, false, [48630], []⟩,
        ⟨70613, false, false, [48630], []⟩,
        ⟨113976, true, false, [], [92193]⟩,
        ⟨113977, true, false, [], [92193]⟩
      ]⟩,
    ⟨[85401, 15], [48639, 82975], .contexts [
        ⟨113975, true, false, [48630], [15]⟩,
        ⟨70645, false, false, [48630], []⟩,
        ⟨105985, false, false, [48630], []⟩,
        ⟨113977, true, false, [], [41015, 82975]⟩,
        ⟨113982, true, false, [], [82975]⟩
      ]⟩,
    ⟨[85405, 1], [85407], .contexts [
        ⟨31903, false, false, [], []⟩,
        ⟨32107, false, false, [], []⟩
      ]⟩,
    ⟨[85405, 3], [48659, 82997], .contexts [
        ⟨113995, true, false, [48656], [3]⟩,
        ⟨33980, false, false, [48656], []⟩,
        ⟨33978, false, false, [48656], []⟩,
        ⟨113996, true, false, [], [17753, 82997]⟩,
        ⟨114000, true, false, [], [82997]⟩
      ]⟩,
    ⟨[85405, 5], [48661, 83677], .contexts [
        ⟨113995, true, false, [48656], [5]⟩,
        ⟨33986, false, false, [48656], []⟩,
        ⟨33983, false, false, [48656], []⟩,
        ⟨114002, true, false, [], [83677]⟩
      ]⟩,
    ⟨[85405, 7], [48665, 85405], .contexts [
        ⟨113995, true, false, [48656], [7]⟩,
        ⟨33992, false, false, [48656], []⟩,
        ⟨114004, false, false, [48656, 17767], []⟩,
        ⟨114007, true, false, [], [85405]⟩
      ]⟩,
    ⟨[85405, 9], [48667, 84239], .contexts [
        ⟨113995, true, false, [48656], [9]⟩,
        ⟨42520, false, false, [48656], []⟩,
        ⟨42853, false, false, [48656], []⟩,
        ⟨113996, true, false, [], [20711, 84239]⟩,
        ⟨114008, true, false, [], [84239]⟩
      ]⟩,
    ⟨[85405, 11], [48653, 85401], .contexts [
        ⟨31901, false, false, [], []⟩,
        ⟨160876, false, false, [], []⟩
      ]⟩,
    ⟨[85405, 13], [48673, 89157], .contexts [
        ⟨113995, true, false, [48656], [13]⟩,
        ⟨86100, true, false, [48656, 31786], [13]⟩,
        ⟨59, false, false, [48656, 31786, 94759], []⟩,
        ⟨86101, true, false, [48656], [94759]⟩,
        ⟨114011, false, false, [48656, 31789], []⟩,
        ⟨113996, true, false, [], [31789, 48669, 89157]⟩,
        ⟨114012, true, false, [], [48669, 89157]⟩,
        ⟨114013, true, false, [], [89157]⟩
      ]⟩,
    ⟨[85405, 15], [48655, 85855], .contexts [
        ⟨113995, true, false, [48656], [15]⟩,
        ⟨33974, false, false, [48656], []⟩,
        ⟨33947, false, false, [48656], []⟩,
        ⟨113999, true, false, [], [85855]⟩
      ]⟩,
    ⟨[85407, 1], [85405], .contexts [
        ⟨31905, false, false, [], []⟩,
        ⟨32109, false, false, [], []⟩
      ]⟩,
    ⟨[85407, 3], [48655, 85861], .contexts [
        ⟨114015, true, false, [48656], [3]⟩,
        ⟨34012, false, false, [48656], []⟩,
        ⟨34014, false, false, [48656], []⟩,
        ⟨113999, true, false, [], [85861]⟩
      ]⟩,
    ⟨[85407, 5], [48661, 83679], .contexts [
        ⟨114015, true, false, [48656], [5]⟩,
        ⟨34002, false, false, [48656], []⟩,
        ⟨34000, false, false, [48656], []⟩,
        ⟨114002, true, false, [], [83679]⟩
      ]⟩,
    ⟨[85407, 7], [48665, 85407], .contexts [
        ⟨114015, true, false, [48656], [7]⟩,
        ⟨34006, false, false, [48656], []⟩,
        ⟨114017, false, false, [48656, 17767], []⟩,
        ⟨114007, true, false, [], [85407]⟩
      ]⟩,
    ⟨[85407, 9], [48679, 84141], .contexts [
        ⟨114015, true, false, [48656], [9]⟩,
        ⟨43282, false, false, [48656], []⟩,
        ⟨113752, false, false, [48656, 20965], []⟩,
        ⟨113996, true, false, [], [20965, 48415, 84141]⟩,
        ⟨114020, true, false, [], [48415, 84141]⟩,
        ⟨114021, true, false, [], [84141]⟩
      ]⟩,
    ⟨[85407, 11], [48681, 85399], .contexts [
        ⟨114015, true, false, [48656], [11]⟩,
        ⟨113969, false, false, [48656], []⟩,
        ⟨113996, true, false, [], [48627, 85399]⟩,
        ⟨114022, true, false, [], [85399]⟩
      ]⟩,
    ⟨[85407, 13], [85409], .contexts [
        ⟨31907, false, false, [], []⟩,
        ⟨32106, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2514. -/
def y322TCIndexRaw2514 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85407, 15], [48675, 82971], .contexts [
        ⟨114019, false, false, [], []⟩
      ]⟩,
    ⟨[85409, 1], [48701, 95417], .contexts [
        ⟨114026, true, false, [48686], [1]⟩,
        ⟨105902, true, false, [48686, 40942], [1]⟩,
        ⟨90711, true, false, [48686, 40942, 33282], [1]⟩,
        ⟨8, false, false, [48686, 40942, 33282, 95417], []⟩,
        ⟨90712, true, false, [48686, 40942], [95417]⟩,
        ⟨99799, false, false, [48686, 40942], []⟩,
        ⟨105903, true, false, [48686], [33285, 95417]⟩,
        ⟨105909, true, false, [48686], [95417]⟩,
        ⟨114027, true, false, [], [40949, 95417]⟩,
        ⟨114038, true, false, [], [95417]⟩
      ]⟩,
    ⟨[85409, 3], [48689, 85699], .contexts [
        ⟨114026, true, false, [48686], [3]⟩,
        ⟨33050, false, false, [48686], []⟩,
        ⟨99682, false, false, [48686], []⟩,
        ⟨114029, true, false, [], [36279, 85699]⟩,
        ⟨114030, true, false, [], [85699]⟩
      ]⟩,
    ⟨[85409, 5], [48685, 85705], .contexts [
        ⟨114026, true, false, [48686], [5]⟩,
        ⟨33052, false, false, [48686], []⟩,
        ⟨33091, false, false, [48686], []⟩,
        ⟨114028, true, false, [], [85705]⟩,
        ⟨114029, true, false, [], [85705]⟩
      ]⟩,
    ⟨[85409, 7], [48693, 85409], .contexts [
        ⟨114026, true, false, [48686], [7]⟩,
        ⟨99499, false, false, [48686], []⟩,
        ⟨114032, false, false, [48686, 36223], []⟩,
        ⟨114027, true, false, [], [36223, 48687, 85409]⟩,
        ⟨114033, true, false, [], [48687, 85409]⟩,
        ⟨114034, true, false, [], [85409]⟩
      ]⟩,
    ⟨[85409, 9], [48699, 84143], .contexts [
        ⟨114026, true, false, [48686], [9]⟩,
        ⟨105902, true, false, [48686, 40942], [9]⟩,
        ⟨33533, false, false, [48686, 40942], []⟩,
        ⟨33586, false, false, [48686, 40942], []⟩,
        ⟨105905, true, false, [48686], [85825]⟩,
        ⟨113772, false, false, [48686, 40945], []⟩,
        ⟨114036, true, false, [], [48437, 84143]⟩,
        ⟨114037, true, false, [], [84143]⟩
      ]⟩,
    ⟨[85409, 11], [48697, 85829], .contexts [
        ⟨114026, true, false, [48686], [11]⟩,
        ⟨105902, true, false, [48686, 40942], [11]⟩,
        ⟨33535, false, false, [48686, 40942], []⟩,
        ⟨33582, false, false, [48686, 40942], []⟩,
        ⟨105905, true, false, [48686], [85829]⟩,
        ⟨114036, true, false, [], [85829]⟩
      ]⟩,
    ⟨[85409, 13], [85407], .contexts [
        ⟨31909, false, false, [], []⟩,
        ⟨32107, false, false, [], []⟩
      ]⟩,
    ⟨[85411], [48703, 83097], .contexts [
        ⟨114040, false, false, [], []⟩
      ]⟩,
    ⟨[85409, 15], [48703, 83097], .contexts [
        ⟨31911, false, false, [], []⟩,
        ⟨160904, false, false, [], []⟩
      ]⟩,
    ⟨[85413, 1], [48703, 83097], .contexts [
        ⟨31916, false, false, [], []⟩,
        ⟨160904, false, false, [], []⟩
      ]⟩,
    ⟨[85415], [48725, 85413], .contexts [
        ⟨114059, false, false, [], []⟩
      ]⟩,
    ⟨[85413, 3], [48725, 85413], .contexts [
        ⟨31918, false, false, [], []⟩,
        ⟨160907, false, false, [], []⟩
      ]⟩,
    ⟨[85413, 5], [48719, 48729, 85417], .contexts [
        ⟨114054, false, false, [], []⟩,
        ⟨114072, false, false, [48719], []⟩
      ]⟩,
    ⟨[85413, 7], [48711, 85413], .contexts [
        ⟨114043, true, false, [48706], [7]⟩,
        ⟨32040, true, false, [48706], [7]⟩,
        ⟨32254, true, false, [48706, 18188], [13, 7]⟩,
        ⟨518, false, false, [48706, 18188, 85481], []⟩,
        ⟨32227, false, false, [48706, 18188], []⟩,
        ⟨32226, false, false, [48706, 18188], []⟩,
        ⟨32228, false, false, [48706, 18188], []⟩,
        ⟨32208, true, false, [48706], [85479]⟩,
        ⟨114047, false, false, [48706, 18187], []⟩,
        ⟨114044, true, false, [], [18187, 48707, 85413]⟩,
        ⟨114048, true, false, [], [48707, 85413]⟩,
        ⟨114049, true, false, [], [85413]⟩
      ]⟩,
    ⟨[85413, 9], [48717, 85513], .contexts [
        ⟨114043, true, false, [48706], [9]⟩,
        ⟨44291, false, false, [48706], []⟩,
        ⟨105219, false, false, [48706], []⟩,
        ⟨114044, true, false, [], [21131, 39087, 85513]⟩,
        ⟨114051, true, false, [], [39087, 85513]⟩,
        ⟨114052, true, false, [], [85513]⟩
      ]⟩,
    ⟨[85413, 11], [48713, 83101], .contexts [
        ⟨114043, true, false, [48706], [11]⟩,
        ⟨32266, false, false, [48706], []⟩,
        ⟨32280, false, false, [48706], []⟩,
        ⟨114044, true, false, [], [18197, 83101]⟩,
        ⟨114050, true, false, [], [83101]⟩
      ]⟩,
    ⟨[85413, 13], [48705, 85481], .contexts [
        ⟨114043, true, false, [48706], [13]⟩,
        ⟨32038, false, false, [48706], []⟩,
        ⟨32050, false, false, [48706], []⟩,
        ⟨114045, true, false, [], [85481]⟩,
        ⟨114045, true, false, [], [85481]⟩,
        ⟨114044, true, false, [], [85481]⟩
      ]⟩,
    ⟨[85413, 15], [48721, 95417], .contexts [
        ⟨114056, false, false, [], []⟩
      ]⟩,
    ⟨[85417, 1], [48731, 85313], .contexts [
        ⟨31925, false, false, [], []⟩,
        ⟨114074, false, false, [], []⟩
      ]⟩,
    ⟨[85417, 3], [48735, 86609], .contexts [
        ⟨114062, true, false, [48728], [3]⟩,
        ⟨50463, true, false, [48728, 22774], [3]⟩,
        ⟨20, false, false, [48728, 22774, 86609], []⟩,
        ⟨50464, true, false, [48728], [86609]⟩,
        ⟨114063, true, false, [], [22777, 86609]⟩,
        ⟨114068, true, false, [], [86609]⟩
      ]⟩,
    ⟨[85417, 5], [48725, 85413], .contexts [
        ⟨31923, false, false, [], []⟩,
        ⟨160907, false, false, [], []⟩
      ]⟩,
    ⟨[85417, 7], [48737, 86319], .contexts [
        ⟨114062, true, false, [48728], [7]⟩,
        ⟨50490, false, false, [48728], []⟩,
        ⟨114063, true, false, [], [22799, 86319]⟩,
        ⟨114069, true, false, [], [86319]⟩
      ]⟩,
    ⟨[85417, 9], [48727, 88461], .contexts [
        ⟨114062, true, false, [48728], [9]⟩,
        ⟨50269, false, false, [48728], []⟩,
        ⟨50284, false, false, [48728], []⟩,
        ⟨114064, true, false, [], [88461]⟩,
        ⟨114065, true, false, [], [88461]⟩
      ]⟩,
    ⟨[85417, 11], [48731, 85317], .contexts [
        ⟨114062, true, false, [48728], [11]⟩,
        ⟨50271, false, false, [48728], []⟩,
        ⟨50439, false, false, [48728], []⟩,
        ⟨114065, true, false, [], [22763, 85317]⟩,
        ⟨114066, true, false, [], [85317]⟩
      ]⟩,
    ⟨[85417, 13], [48733, 83799], .contexts [
        ⟨114062, true, false, [48728], [13]⟩,
        ⟨50452, true, false, [48728, 22766], [13]⟩,
        ⟨59, false, false, [48728, 22766, 83799], []⟩,
        ⟨50453, true, false, [48728], [83799]⟩,
        ⟨114063, true, false, [], [22769, 83799]⟩,
        ⟨114067, true, false, [], [83799]⟩
      ]⟩,
    ⟨[85417, 15], [48739, 85707], .contexts [
        ⟨114071, false, false, [], []⟩
      ]⟩,
    ⟨[85435, 1], [85437], .contexts [
        ⟨31954, false, false, [], []⟩,
        ⟨32092, false, false, [], []⟩
      ]⟩,
    ⟨[85435, 3], [50225, 83013], .contexts [
        ⟨115751, true, false, [50220], [3]⟩,
        ⟨68484, false, false, [50220], []⟩,
        ⟨68519, false, false, [50220], []⟩,
        ⟨115752, true, false, [], [26869, 83013]⟩,
        ⟨115758, true, false, [], [83013]⟩
      ]⟩,
    ⟨[85435, 5], [50117, 83827], .contexts [
        ⟨31952, false, false, [], []⟩,
        ⟨115650, false, false, [], []⟩
      ]⟩,
    ⟨[85435, 7], [52635, 57017, 87623], .contexts [
        ⟨118669, false, false, [], []⟩,
        ⟨123803, false, false, [52635], []⟩
      ]⟩,
    ⟨[85435, 9], [50227, 88349], .contexts [
        ⟨115751, true, false, [50220], [9]⟩,
        ⟨68526, true, false, [50220, 26878], [9]⟩,
        ⟨46, false, false, [50220, 26878, 88349], []⟩,
        ⟨68524, false, true, [50220], [88349]⟩,
        ⟨115752, true, false, [], [26877, 88349]⟩,
        ⟨115759, true, false, [], [88349]⟩
      ]⟩,
    ⟨[85435, 11], [50219, 55977, 86479], .contexts [
        ⟨115751, true, false, [50220], [11]⟩,
        ⟨38249, false, false, [50220], []⟩,
        ⟨38436, false, false, [50220], []⟩,
        ⟨115754, true, false, [], [86621]⟩,
        ⟨115755, true, false, [], [86621]⟩,
        ⟨122588, false, false, [50219], []⟩
      ]⟩,
    ⟨[85435, 13], [50223, 83687], .contexts [
        ⟨115757, false, false, [], []⟩,
        ⟨124437, false, false, [], []⟩
      ]⟩,
    ⟨[85435, 15], [50229, 96637], .contexts [
        ⟨115761, false, false, [], []⟩,
        ⟨124440, false, false, [], []⟩
      ]⟩,
    ⟨[85437, 1], [85435], .contexts [
        ⟨31956, false, false, [], []⟩,
        ⟨32093, false, false, [], []⟩
      ]⟩,
    ⟨[85437, 3], [50235, 54449, 84171], .contexts [
        ⟨115769, false, false, [], []⟩,
        ⟨120775, false, false, [50235], []⟩
      ]⟩,
    ⟨[85437, 5], [50239, 83825], .contexts [
        ⟨115772, false, false, [], []⟩
      ]⟩,
    ⟨[85437, 7], [50233, 68059, 88271], .contexts [
        ⟨115765, true, false, [50220], [7]⟩,
        ⟨81969, true, false, [50220, 30838], [7]⟩,
        ⟨38, false, false, [50220, 30838, 93917], []⟩,
        ⟨81970, true, false, [50220], [93917]⟩,
        ⟨115752, true, false, [], [30841, 93917]⟩,
        ⟨115767, true, false, [], [93917]⟩,
        ⟨136700, false, false, [50233], []⟩
      ]⟩,
    ⟨[85437, 9], [85439], .contexts [
        ⟨31958, false, false, [], []⟩,
        ⟨32091, false, false, [], []⟩
      ]⟩,
    ⟨[85437, 11], [56007, 86477], .contexts [
        ⟨122616, false, false, [], []⟩,
        ⟨124451, false, false, [], []⟩
      ]⟩,
    ⟨[85437, 13], [50231, 83451], .contexts [
        ⟨115765, true, false, [50220], [13]⟩,
        ⟨38255, false, false, [50220], []⟩,
        ⟨68467, false, false, [50220], []⟩,
        ⟨115755, true, false, [], [26857, 83451]⟩,
        ⟨115766, true, false, [], [83451]⟩
      ]⟩,
    ⟨[85437, 15], [50237, 95357], .contexts [
        ⟨115765, true, false, [50220], [15]⟩,
        ⟨89851, true, false, [50220, 32968], [15]⟩,
        ⟨1, false, false, [50220, 32968, 95357], []⟩,
        ⟨89852, true, false, [50220], [95357]⟩,
        ⟨115752, true, false, [], [32971, 95357]⟩,
        ⟨115770, true, false, [], [95357]⟩
      ]⟩,
    ⟨[85439, 1], [52717, 96767], .contexts [
        ⟨140568, true, false, [52714], [1]⟩,
        ⟨8, false, false, [52714, 96767], []⟩,
        ⟨118764, true, false, [], [96767]⟩
      ]⟩,
    ⟨[85439, 3], [50245, 54449, 84173], .contexts [
        ⟨115778, true, false, [50242], [3]⟩,
        ⟨83432, false, false, [50242], []⟩,
        ⟨99943, false, false, [50242], []⟩,
        ⟨115780, true, false, [], [36355, 85915]⟩,
        ⟨115781, true, false, [], [85915]⟩,
        ⟨120964, false, false, [50245], []⟩
      ]⟩,
    ⟨[85439, 5], [50247, 85135], .contexts [
        ⟨115778, true, false, [50242], [5]⟩,
        ⟨83434, false, false, [50242], []⟩,
        ⟨109334, false, false, [50242], []⟩,
        ⟨115780, true, false, [], [44441, 85135]⟩,
        ⟨115782, true, false, [], [85135]⟩
      ]⟩,
    ⟨[85439, 7], [50251, 55099, 86145], .contexts [
        ⟨115786, false, false, [], []⟩,
        ⟨121526, false, false, [50251], []⟩
      ]⟩,
    ⟨[85439, 9], [85437], .contexts [
        ⟨31960, false, false, [], []⟩,
        ⟨32092, false, false, [], []⟩
      ]⟩,
    ⟨[85439, 11], [85441], .contexts [
        ⟨31962, false, false, [], []⟩,
        ⟨32089, false, false, [], []⟩
      ]⟩,
    ⟨[85439, 13], [50253, 83449], .contexts [
        ⟨115788, false, false, [], []⟩,
        ⟨124464, false, false, [], []⟩
      ]⟩,
    ⟨[85439, 15], [50249, 59129, 87265], .contexts [
        ⟨115784, false, false, [], []⟩,
        ⟨126273, false, false, [50249], []⟩
      ]⟩,
    ⟨[85441, 1], [85443], .contexts [
        ⟨31966, false, false, [], []⟩,
        ⟨32088, false, false, [], []⟩
      ]⟩,
    ⟨[85441, 3], [54631, 84175], .contexts [
        ⟨120977, false, false, [], []⟩
      ]⟩,
    ⟨[85441, 5], [52719, 52753, 85191], .contexts [
        ⟨118766, false, false, [], []⟩,
        ⟨118806, false, false, [52719], []⟩
      ]⟩,
    ⟨[85441, 7], [57575, 65377, 90789], .contexts [
        ⟨124461, false, false, [], []⟩,
        ⟨133629, false, false, [57575], []⟩
      ]⟩,
    ⟨[85441, 9], [73705, 96947], .contexts [
        ⟨144029, true, false, [73702], [9]⟩,
        ⟨46, false, false, [73702, 96947], []⟩,
        ⟨144030, true, false, [], [96947]⟩
      ]⟩,
    ⟨[85441, 11], [85439], .contexts [
        ⟨31964, false, false, [], []⟩,
        ⟨32091, false, false, [], []⟩
      ]⟩,
    ⟨[85441, 13], [57579, 85039], .contexts [
        ⟨124467, false, false, [], []⟩
      ]⟩,
    ⟨[85441, 15], [53945, 60885, 90271], .contexts [
        ⟨120127, false, false, [], []⟩,
        ⟨128300, false, false, [53945], []⟩
      ]⟩,
    ⟨[85443, 1], [85441], .contexts [
        ⟨31968, false, false, [], []⟩,
        ⟨32089, false, false, [], []⟩
      ]⟩,
    ⟨[85443, 3], [65533, 94235], .contexts [
        ⟨133778, false, false, [], []⟩,
        ⟨134870, false, false, [], []⟩
      ]⟩,
    ⟨[85443, 5], [57587, 85189], .contexts [
        ⟨124475, false, false, [], []⟩
      ]⟩,
    ⟨[85443, 7], [58897, 86141], .contexts [
        ⟨125955, false, false, [], []⟩,
        ⟨127625, false, false, [], []⟩
      ]⟩,
    ⟨[85443, 9], [53183, 91307], .contexts [
        ⟨119316, false, false, [], []⟩,
        ⟨127632, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2515. -/
def y322TCIndexRaw2515 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85443, 11], [71711, 96767], .contexts [
        ⟨140585, true, false, [71708], [11]⟩,
        ⟨53, false, false, [71708, 96767], []⟩,
        ⟨140586, true, false, [], [96767]⟩
      ]⟩,
    ⟨[85443, 13], [85445], .contexts [
        ⟨31970, false, false, [], []⟩,
        ⟨32087, false, false, [], []⟩
      ]⟩,
    ⟨[85443, 15], [59875, 60871, 90269], .contexts [
        ⟨127135, false, false, [], []⟩,
        ⟨128282, false, false, [59875], []⟩
      ]⟩,
    ⟨[85445, 1], [27399, 60103, 85043], .contexts [
        ⟨70342, true, false, [27400], [1]⟩,
        ⟨66563, false, false, [27400], []⟩,
        ⟨66647, false, false, [27400], []⟩,
        ⟨70339, true, false, [], [91589]⟩,
        ⟨127405, false, false, [27399], []⟩
      ]⟩,
    ⟨[85445, 3], [65705, 83729], .contexts [
        ⟨133978, false, false, [], []⟩,
        ⟨134028, false, false, [], []⟩
      ]⟩,
    ⟨[85445, 5], [59879, 93901], .contexts [
        ⟨127139, true, false, [59876], [5]⟩,
        ⟨28, false, false, [59876, 93901], []⟩,
        ⟨127140, true, false, [], [93901]⟩
      ]⟩,
    ⟨[85445, 7], [60327, 85737], .contexts [
        ⟨127630, false, false, [], []⟩,
        ⟨134024, false, false, [], []⟩
      ]⟩,
    ⟨[85445, 9], [60331, 96259], .contexts [
        ⟨127637, false, false, [], []⟩,
        ⟨134037, false, false, [], []⟩
      ]⟩,
    ⟨[85445, 11], [61907, 84563], .contexts [
        ⟨129554, false, false, [], []⟩
      ]⟩,
    ⟨[85445, 13], [85443], .contexts [
        ⟨31972, false, false, [], []⟩,
        ⟨32088, false, false, [], []⟩
      ]⟩,
    ⟨[85445, 15], [60089, 85047], .contexts [
        ⟨31974, false, false, [], []⟩,
        ⟨156454, false, false, [], []⟩
      ]⟩,
    ⟨[85453, 1], [85455], .contexts [
        ⟨31989, false, false, [], []⟩,
        ⟨32077, false, false, [], []⟩
      ]⟩,
    ⟨[85453, 3], [65045, 84555], .contexts [
        ⟨133251, false, false, [], []⟩
      ]⟩,
    ⟨[85453, 5], [45237, 83031], .contexts [
        ⟨31987, false, false, [], []⟩,
        ⟨110309, false, false, [], []⟩
      ]⟩,
    ⟨[85453, 7], [61153, 95485], .contexts [
        ⟨128612, false, false, [], []⟩
      ]⟩,
    ⟨[85453, 9], [29293, 85453], .contexts [
        ⟨76374, false, false, [], []⟩,
        ⟨76394, false, false, [], []⟩
      ]⟩,
    ⟨[85453, 11], [37119, 61063, 84765], .contexts [
        ⟨101547, false, false, [], []⟩,
        ⟨128516, false, false, [37119], []⟩
      ]⟩,
    ⟨[85453, 13], [36397, 45353, 94451], .contexts [
        ⟨100009, false, false, [], []⟩,
        ⟨110446, false, false, [36397], []⟩
      ]⟩,
    ⟨[85453, 15], [27399, 65803, 83737], .contexts [
        ⟨70314, false, false, [], []⟩,
        ⟨134105, false, false, [27399], []⟩
      ]⟩,
    ⟨[85455, 1], [85453], .contexts [
        ⟨31991, false, false, [], []⟩,
        ⟨32079, false, false, [], []⟩
      ]⟩,
    ⟨[85455, 3], [52867, 55133, 59233, 85747], .contexts [
        ⟨118943, true, false, [52864], [3]⟩,
        ⟨20, false, false, [52864, 93899], []⟩,
        ⟨118944, true, false, [], [93899]⟩,
        ⟨160096, false, false, [52867], []⟩
      ]⟩,
    ⟨[85455, 5], [59243, 85751], .contexts [
        ⟨126423, false, false, [], []⟩,
        ⟨128585, false, false, [], []⟩
      ]⟩,
    ⟨[85455, 7], [52097, 95267], .contexts [
        ⟨118018, false, false, [], []⟩,
        ⟨126208, false, false, [], []⟩
      ]⟩,
    ⟨[85455, 9], [85457], .contexts [
        ⟨31993, false, false, [], []⟩,
        ⟨32075, false, false, [], []⟩
      ]⟩,
    ⟨[85455, 11], [54205, 94275], .contexts [
        ⟨120477, false, false, [], []⟩,
        ⟨126211, false, false, [], []⟩
      ]⟩,
    ⟨[85455, 13], [29311, 44457, 85139], .contexts [
        ⟨76357, false, false, [], []⟩,
        ⟨109365, false, false, [29311], []⟩
      ]⟩,
    ⟨[85455, 15], [27399, 65803, 83735], .contexts [
        ⟨70305, true, false, [27400], [15]⟩,
        ⟨1, false, false, [27400, 91595], []⟩,
        ⟨70258, true, false, [], [91595]⟩,
        ⟨134100, false, false, [27399], []⟩
      ]⟩,
    ⟨[85457, 1], [29291, 85457], .contexts [
        ⟨76331, false, false, [], []⟩,
        ⟨76291, false, false, [], []⟩
      ]⟩,
    ⟨[85457, 3], [58317, 93897], .contexts [
        ⟨125281, false, false, [], []⟩,
        ⟨128635, false, false, [], []⟩
      ]⟩,
    ⟨[85457, 5], [54211, 94267], .contexts [
        ⟨120488, false, false, [], []⟩,
        ⟨128616, false, false, [], []⟩
      ]⟩,
    ⟨[85457, 7], [31545, 83697], .contexts [
        ⟨85155, false, false, [], []⟩
      ]⟩,
    ⟨[85457, 9], [85455], .contexts [
        ⟨31995, false, false, [], []⟩,
        ⟨32077, false, false, [], []⟩
      ]⟩,
    ⟨[85457, 11], [85459], .contexts [
        ⟨31997, false, false, [], []⟩,
        ⟨32073, false, false, [], []⟩
      ]⟩,
    ⟨[85457, 13], [29311, 43319, 91339], .contexts [
        ⟨76300, false, false, [], []⟩,
        ⟨108119, false, false, [29311], []⟩
      ]⟩,
    ⟨[85457, 15], [27399, 91597], .contexts [
        ⟨70288, false, false, [], []⟩,
        ⟨70299, false, false, [], []⟩
      ]⟩,
    ⟨[85461], [29291, 85459], .contexts [
        ⟨76265, false, false, [], []⟩
      ]⟩,
    ⟨[85459, 1], [29291, 85459], .contexts [
        ⟨32001, false, false, [], []⟩,
        ⟨160995, false, false, [], []⟩
      ]⟩,
    ⟨[85459, 3], [50789, 90651], .contexts [
        ⟨116493, false, false, [], []⟩,
        ⟨125275, false, false, [], []⟩
      ]⟩,
    ⟨[85459, 5], [74657, 97033], .contexts [
        ⟨145559, true, false, [74654], [5]⟩,
        ⟨28, false, false, [74654, 97033], []⟩,
        ⟨145560, true, false, [], [97033]⟩
      ]⟩,
    ⟨[85459, 7], [36629, 45659, 90171], .contexts [
        ⟨100530, true, false, [36626], [7]⟩,
        ⟨38, false, false, [36626, 92307], []⟩,
        ⟨100531, true, false, [], [92307]⟩,
        ⟨115036, false, false, [36629], []⟩
      ]⟩,
    ⟨[85459, 9], [32441, 95117], .contexts [
        ⟨88156, false, false, [], []⟩,
        ⟨88175, false, false, [], []⟩
      ]⟩,
    ⟨[85459, 11], [85457], .contexts [
        ⟨31999, false, false, [], []⟩,
        ⟨32075, false, false, [], []⟩
      ]⟩,
    ⟨[85459, 13], [29293, 85463], .contexts [
        ⟨76259, false, false, [], []⟩
      ]⟩,
    ⟨[85459, 15], [27399, 91599], .contexts [
        ⟨70259, false, false, [], []⟩,
        ⟨70252, false, false, [], []⟩
      ]⟩,
    ⟨[29259, 92941], [29259, 29273, 43287, 68241, 87753], .contexts [
        ⟨76224, false, false, [29259], []⟩,
        ⟨108070, false, false, [29259], []⟩,
        ⟨136870, false, false, [29259, 29273, 43287], []⟩
      ]⟩,
    ⟨[85463, 1], [29259, 29273, 43287, 68241, 87753], .contexts [
        ⟨76215, false, false, [], []⟩,
        ⟨161004, false, false, [], []⟩
      ]⟩,
    ⟨[94293], [46849, 50091, 87373], .contexts [
        ⟨114951, false, false, [], []⟩,
        ⟨115790, false, false, [], []⟩
      ]⟩,
    ⟨[85463, 3], [31191, 46849, 50091, 87373], .contexts [
        ⟨83679, false, false, [], []⟩,
        ⟨161006, false, false, [31191], []⟩
      ]⟩,
    ⟨[85463, 5], [43373, 90445], .contexts [
        ⟨108179, true, false, [43374], [5]⟩,
        ⟨60650, false, false, [43374], []⟩,
        ⟨60738, false, false, [43374], []⟩,
        ⟨108180, true, false, [], [90445]⟩,
        ⟨108180, true, false, [], [90445]⟩,
        ⟨108178, false, true, [], [90445]⟩
      ]⟩,
    ⟨[85463, 7], [29321, 88681], .contexts [
        ⟨76319, false, false, [], []⟩,
        ⟨76313, false, false, [], []⟩
      ]⟩,
    ⟨[85463, 9], [27403, 86667], .contexts [
        ⟨70216, false, false, [], []⟩
      ]⟩,
    ⟨[85463, 11], [29279, 43319, 91339], .contexts [
        ⟨76232, false, false, [], []⟩,
        ⟨108119, false, false, [29279], []⟩
      ]⟩,
    ⟨[85463, 13], [29291, 85459], .contexts [
        ⟨32006, false, false, [], []⟩,
        ⟨160995, false, false, [], []⟩
      ]⟩,
    ⟨[85463, 15], [85465], .contexts [
        ⟨32008, false, false, [], []⟩,
        ⟨32066, false, false, [], []⟩
      ]⟩,
    ⟨[85465, 1], [85467], .contexts [
        ⟨32012, false, false, [], []⟩,
        ⟨32064, false, false, [], []⟩
      ]⟩,
    ⟨[85465, 3], [27339, 89083], .contexts [
        ⟨70125, false, false, [], []⟩
      ]⟩,
    ⟨[96293], [43369, 43427, 89395], .contexts [
        ⟨108174, false, false, [], []⟩,
        ⟨116537, false, false, [], []⟩
      ]⟩,
    ⟨[85465, 5], [43369, 43427, 89395], .contexts [
        ⟨97088, true, false, [], [5]⟩,
        ⟨28, false, false, [96293], []⟩,
        ⟨97085, false, false, [], []⟩,
        ⟨161016, false, false, [], []⟩
      ]⟩,
    ⟨[85465, 7], [27337, 88689], .contexts [
        ⟨70123, false, false, [], []⟩
      ]⟩,
    ⟨[85465, 9], [27343, 86659], .contexts [
        ⟨70128, false, false, [], []⟩,
        ⟨70213, false, false, [], []⟩
      ]⟩,
    ⟨[85465, 11], [27333, 37623, 87995], .contexts [
        ⟨70120, false, false, [], []⟩,
        ⟨102412, false, false, [27333], []⟩
      ]⟩,
    ⟨[85465, 13], [21227, 84193], .contexts [
        ⟨44552, false, false, [], []⟩
      ]⟩,
    ⟨[85465, 15], [85463], .contexts [
        ⟨32010, false, false, [], []⟩,
        ⟨32068, false, false, [], []⟩
      ]⟩,
    ⟨[85467, 1], [85465], .contexts [
        ⟨32014, false, false, [], []⟩,
        ⟨32066, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2516. -/
def y322TCIndexRaw2516 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85467, 3], [85469], .contexts [
        ⟨32016, false, false, [], []⟩,
        ⟨32062, false, false, [], []⟩
      ]⟩,
    ⟨[85467, 5], [43419, 89397], .contexts [
        ⟨97079, false, false, [], []⟩,
        ⟨108234, false, false, [], []⟩
      ]⟩,
    ⟨[85467, 7], [27337, 88687], .contexts [
        ⟨70132, false, false, [], []⟩,
        ⟨76233, false, false, [], []⟩
      ]⟩,
    ⟨[85467, 9], [37269, 43441, 70397, 89907], .contexts [
        ⟨101919, false, false, [], []⟩,
        ⟨155557, false, false, [37269], []⟩
      ]⟩,
    ⟨[85467, 11], [37267, 70379, 89911], .contexts [
        ⟨101913, false, false, [], []⟩,
        ⟨139110, false, false, [37267], []⟩
      ]⟩,
    ⟨[85467, 13], [21175, 84201], .contexts [
        ⟨44520, false, false, [], []⟩,
        ⟨44515, false, false, [], []⟩
      ]⟩,
    ⟨[85467, 15], [29259, 29273, 43287, 68241, 87753], .contexts [
        ⟨76198, false, false, [], []⟩,
        ⟨161004, false, false, [], []⟩
      ]⟩,
    ⟨[85469, 1], [34453, 46829, 90659], .contexts [
        ⟨94306, false, false, [], []⟩,
        ⟨112229, false, false, [34453], []⟩
      ]⟩,
    ⟨[85469, 3], [85467], .contexts [
        ⟨32018, false, false, [], []⟩,
        ⟨32064, false, false, [], []⟩
      ]⟩,
    ⟨[85469, 5], [85471], .contexts [
        ⟨32020, false, false, [], []⟩,
        ⟨32059, false, false, [], []⟩
      ]⟩,
    ⟨[85469, 7], [50793, 50885, 92609], .contexts [
        ⟨116496, false, false, [], []⟩,
        ⟨116625, false, false, [50793], []⟩
      ]⟩,
    ⟨[85469, 9], [20867, 83617], .contexts [
        ⟨42918, false, false, [], []⟩,
        ⟨102085, false, false, [], []⟩
      ]⟩,
    ⟨[85469, 11], [56879, 93581], .contexts [
        ⟨123617, false, false, [], []⟩
      ]⟩,
    ⟨[85469, 13], [21175, 84203], .contexts [
        ⟨44461, false, false, [], []⟩,
        ⟨44513, false, false, [], []⟩
      ]⟩,
    ⟨[85469, 15], [73387, 96913], .contexts [
        ⟨143460, false, false, [], []⟩
      ]⟩,
    ⟨[85471, 1], [85473], .contexts [
        ⟨32024, false, false, [], []⟩,
        ⟨32057, false, false, [], []⟩
      ]⟩,
    ⟨[85471, 3], [27381, 92151], .contexts [
        ⟨70175, false, false, [], []⟩,
        ⟨122755, false, false, [], []⟩
      ]⟩,
    ⟨[85471, 5], [85469], .contexts [
        ⟨32022, false, false, [], []⟩,
        ⟨32062, false, false, [], []⟩
      ]⟩,
    ⟨[85471, 7], [18235, 85471], .contexts [
        ⟨32309, true, false, [18222], [7]⟩,
        ⟨1084, false, false, [18222, 84827], []⟩,
        ⟨1085, false, false, [18222, 84827], []⟩,
        ⟨29165, false, false, [18222], [9]⟩,
        ⟨32301, false, false, [18222, 17729], []⟩,
        ⟨32310, true, false, [18222], [85471]⟩,
        ⟨32299, false, false, [18222, 18233], []⟩,
        ⟨32302, true, false, [], [18233, 85471]⟩,
        ⟨32311, true, false, [], [85471]⟩
      ]⟩,
    ⟨[85471, 9], [18225, 84827], .contexts [
        ⟨32301, true, false, [18222], [9]⟩,
        ⟨46, false, false, [18222, 84827], []⟩,
        ⟨32302, true, false, [], [84827]⟩
      ]⟩,
    ⟨[85471, 11], [23793, 89215], .contexts [
        ⟨54941, false, false, [], []⟩,
        ⟨111603, false, false, [], []⟩
      ]⟩,
    ⟨[85471, 13], [21175, 84205], .contexts [
        ⟨44397, false, false, [], []⟩,
        ⟨44389, false, false, [], []⟩
      ]⟩,
    ⟨[85471, 15], [23793, 96959], .contexts [
        ⟨144233, true, false, [23790], [15]⟩,
        ⟨1, false, false, [23790, 96959], []⟩,
        ⟨54940, true, false, [], [96959]⟩
      ]⟩,
    ⟨[85473, 1], [85471], .contexts [
        ⟨32026, false, false, [], []⟩,
        ⟨32059, false, false, [], []⟩
      ]⟩,
    ⟨[85473, 3], [33817, 49975, 86875], .contexts [
        ⟨92225, true, false, [33814], [3]⟩,
        ⟨20, false, false, [33814, 95515], []⟩,
        ⟨92226, true, false, [], [95515]⟩,
        ⟨115506, false, false, [33817], []⟩
      ]⟩,
    ⟨[85473, 5], [34487, 46829, 90659], .contexts [
        ⟨94344, false, false, [], []⟩,
        ⟨112229, false, false, [34487], []⟩
      ]⟩,
    ⟨[85473, 7], [18231, 85473], .contexts [
        ⟨32303, false, false, [18226], [85473, 7]⟩,
        ⟨32292, true, false, [18226, 15875], [7]⟩,
        ⟨18868, true, false, [18226], [9, 7]⟩,
        ⟨579, false, false, [18226, 83099], []⟩,
        ⟨47, false, false, [18226, 83099], []⟩,
        ⟨32297, false, false, [18226], []⟩,
        ⟨32304, false, false, [18226, 18199], []⟩,
        ⟨32305, true, false, [], [18199, 85473]⟩,
        ⟨32306, true, false, [], [85473]⟩
      ]⟩,
    ⟨[85473, 9], [18197, 83099], .contexts [
        ⟨32028, false, false, [], []⟩,
        ⟨32291, false, false, [], []⟩
      ]⟩,
    ⟨[85473, 11], [46307, 93203], .contexts [
        ⟨111606, false, false, [], []⟩
      ]⟩,
    ⟨[85473, 13], [21153, 86795], .contexts [
        ⟨44327, false, false, [], []⟩,
        ⟨44386, false, false, [], []⟩
      ]⟩,
    ⟨[85473, 15], [73519, 96927], .contexts [
        ⟨143677, true, false, [73516], [15]⟩,
        ⟨1, false, false, [73516, 96927], []⟩,
        ⟨143678, true, false, [], [96927]⟩
      ]⟩,
    ⟨[85481, 1], [18177, 83795], .contexts [
        ⟨32221, false, false, [], []⟩,
        ⟨32191, false, false, [], []⟩
      ]⟩,
    ⟨[85481, 3], [18201, 85481], .contexts [
        ⟨32203, false, false, [], []⟩,
        ⟨32223, false, false, [], []⟩
      ]⟩,
    ⟨[85481, 5], [18177, 83799], .contexts [
        ⟨32251, false, false, [], []⟩,
        ⟨32248, false, false, [], []⟩
      ]⟩,
    ⟨[85481, 7], [18189, 85481], .contexts [
        ⟨32233, false, false, [], []⟩,
        ⟨32252, false, false, [], []⟩
      ]⟩,
    ⟨[95643], [39077, 86347], .contexts [
        ⟨104130, false, false, [], []⟩
      ]⟩,
    ⟨[85481, 9], [39077, 86347], .contexts [
        ⟨93383, false, false, [], []⟩,
        ⟨161059, false, false, [], []⟩
      ]⟩,
    ⟨[85481, 11], [18197, 83103], .contexts [
        ⟨32246, false, false, [], []⟩,
        ⟨32242, false, false, [], []⟩
      ]⟩,
    ⟨[85481, 13], [48707, 85413], .contexts [
        ⟨32040, false, false, [], []⟩,
        ⟨114046, false, false, [], []⟩
      ]⟩,
    ⟨[85481, 15], [20329, 83635], .contexts [
        ⟨32042, false, false, [], []⟩,
        ⟨41864, false, false, [], []⟩
      ]⟩,
    ⟨[85487, 1], [18237, 82989], .contexts [
        ⟨32323, false, false, [], []⟩,
        ⟨32319, false, false, [], []⟩
      ]⟩,
    ⟨[85487, 3], [82977], .contexts [
        ⟨32314, false, false, [], []⟩,
        ⟨18010, false, false, [], []⟩
      ]⟩,
    ⟨[85487, 5], [18249, 85487], .contexts [
        ⟨32346, false, false, [], []⟩,
        ⟨37543, false, false, [], []⟩
      ]⟩,
    ⟨[85487, 7], [15743, 85487], .contexts [
        ⟨32330, false, false, [], []⟩,
        ⟨32326, false, false, [], []⟩
      ]⟩,
    ⟨[85487, 9], [16661, 85487], .contexts [
        ⟨32334, false, false, [], []⟩,
        ⟨32331, false, false, [], []⟩
      ]⟩,
    ⟨[85487, 11], [18237, 82993], .contexts [
        ⟨32351, false, false, [], []⟩,
        ⟨32347, false, false, [], []⟩
      ]⟩,
    ⟨[85487, 13], [19195, 86561], .contexts [
        ⟨37518, false, false, [], []⟩,
        ⟨37536, false, false, [], []⟩
      ]⟩,
    ⟨[85487, 15], [18241, 85229], .contexts [
        ⟨32336, false, false, [], []⟩
      ]⟩,
    ⟨[85489, 1], [19159, 19165, 86565], .contexts [
        ⟨37473, false, false, [], []⟩,
        ⟨37496, false, false, [19159], []⟩
      ]⟩,
    ⟨[85489, 3], [83513], .contexts [
        ⟨32359, false, false, [], []⟩,
        ⟨21830, false, false, [], []⟩
      ]⟩,
    ⟨[85489, 5], [323, 85489], .contexts [
        ⟨32363, false, false, [], []⟩,
        ⟨32361, false, false, [], []⟩
      ]⟩,
    ⟨[85489, 7], [317, 85489], .contexts [
        ⟨32365, false, false, [], []⟩,
        ⟨32364, false, false, [], []⟩
      ]⟩,
    ⟨[85489, 9], [84719], .contexts [
        ⟨32366, false, false, [], []⟩,
        ⟨28357, false, false, [], []⟩
      ]⟩,
    ⟨[85489, 11], [86109], .contexts [
        ⟨35393, true, false, [], [11]⟩,
        ⟨53, false, false, [86109], []⟩,
        ⟨35378, false, false, [], []⟩,
        ⟨35377, false, false, [], []⟩
      ]⟩,
    ⟨[85489, 13], [82989], .contexts [
        ⟨32354, false, false, [], []⟩,
        ⟨18270, false, false, [], []⟩
      ]⟩,
    ⟨[85489, 15], [18253, 85489], .contexts [
        ⟨32371, false, false, [], []⟩,
        ⟨32369, false, false, [], []⟩
      ]⟩,
    ⟨[85491, 1], [83669], .contexts [
        ⟨32374, false, false, [], []⟩,
        ⟨22531, false, false, [], []⟩
      ]⟩,
    ⟨[85491, 3], [18257, 85491], .contexts [
        ⟨32384, false, false, [], []⟩,
        ⟨32380, false, false, [], []⟩
      ]⟩,
    ⟨[85491, 5], [18259, 82977], .contexts [
        ⟨32388, false, false, [], []⟩,
        ⟨42090, false, false, [], []⟩
      ]⟩,
    ⟨[85491, 7], [48963, 88849], .contexts [
        ⟨114318, false, false, [], []⟩
      ]⟩,
    ⟨[85491, 9], [759, 85491], .contexts [
        ⟨32393, false, false, [], []⟩,
        ⟨32390, false, false, [], []⟩
      ]⟩,
    ⟨[85491, 11], [83673], .contexts [
        ⟨32395, false, false, [], []⟩,
        ⟨22564, false, false, [], []⟩
      ]⟩,
    ⟨[85491, 13], [20403, 87113], .contexts [
        ⟨41947, false, false, [], []⟩,
        ⟨42070, false, false, [], []⟩
      ]⟩,
    ⟨[85491, 15], [20403, 21523, 86587], .contexts [
        ⟨41940, false, false, [], []⟩,
        ⟨45463, false, false, [20403], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2517. -/
def y322TCIndexRaw2517 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85493, 1], [46227, 87507], .contexts [
        ⟨53636, false, false, [], []⟩,
        ⟨111533, false, false, [], []⟩
      ]⟩,
    ⟨[85493, 3], [18263, 82653], .contexts [
        ⟨32405, false, false, [], []⟩,
        ⟨32411, false, false, [], []⟩
      ]⟩,
    ⟨[85493, 5], [17761, 86571], .contexts [
        ⟨37962, false, false, [], []⟩,
        ⟨53648, false, false, [], []⟩
      ]⟩,
    ⟨[85493, 7], [24041, 89439], .contexts [
        ⟨55942, false, false, [], []⟩,
        ⟨55966, false, false, [], []⟩
      ]⟩,
    ⟨[85493, 9], [245, 85493], .contexts [
        ⟨32402, true, false, [], [9]⟩,
        ⟨77, false, false, [83671], []⟩,
        ⟨78, false, false, [83671], []⟩,
        ⟨22557, false, false, [], [13]⟩,
        ⟨32408, false, false, [], [13]⟩,
        ⟨22555, false, false, [], [13]⟩,
        ⟨22556, false, false, [], [13]⟩,
        ⟨22556, false, false, [], [13]⟩,
        ⟨32398, false, false, [245], []⟩,
        ⟨32409, false, false, [], []⟩,
        ⟨32410, false, false, [245], []⟩,
        ⟨923, true, false, [], [85493]⟩,
        ⟨32409, false, false, [], []⟩
      ]⟩,
    ⟨[85493, 11], [19841, 87201], .contexts [
        ⟨40329, false, false, [], []⟩,
        ⟨53653, false, false, [], []⟩
      ]⟩,
    ⟨[85493, 13], [83671], .contexts [
        ⟨32399, false, false, [], []⟩,
        ⟨22543, false, false, [], []⟩
      ]⟩,
    ⟨[85493, 15], [18269, 85107], .contexts [
        ⟨32419, false, false, [], []⟩,
        ⟨53660, false, false, [], []⟩
      ]⟩,
    ⟨[85495, 1], [7355, 83373], .contexts [
        ⟨32430, false, false, [], []⟩,
        ⟨32426, false, false, [], []⟩
      ]⟩,
    ⟨[85495, 3], [85109], .contexts [
        ⟨32422, false, false, [], []⟩,
        ⟨33216, false, false, [], []⟩
      ]⟩,
    ⟨[85495, 5], [7355, 83377], .contexts [
        ⟨32440, false, false, [], []⟩,
        ⟨32433, false, false, [], []⟩
      ]⟩,
    ⟨[85495, 7], [18279, 85501], .contexts [
        ⟨32491, false, false, [], []⟩,
        ⟨56014, false, false, [], []⟩
      ]⟩,
    ⟨[85495, 9], [39863, 84461], .contexts [
        ⟨33211, false, false, [], []⟩,
        ⟨160009, false, false, [], []⟩
      ]⟩,
    ⟨[85495, 11], [18937, 20751, 85255], .contexts [
        ⟨35850, false, false, [], []⟩,
        ⟨42668, false, false, [18937], []⟩
      ]⟩,
    ⟨[85495, 13], [18945, 85935], .contexts [
        ⟨35880, false, false, [], []⟩,
        ⟨35873, false, false, [], []⟩
      ]⟩,
    ⟨[85495, 15], [21105, 88211], .contexts [
        ⟨49272, false, false, [], []⟩
      ]⟩,
    ⟨[21743, 87799], [21743, 47141, 86523], .contexts [
        ⟨112524, false, false, [21743], []⟩
      ]⟩,
    ⟨[85497, 1], [21743, 47141, 86523], .contexts [
        ⟨46240, false, false, [], []⟩,
        ⟨161104, false, false, [], []⟩
      ]⟩,
    ⟨[85497, 3], [16219, 79193], .contexts [
        ⟨32450, false, false, [], []⟩,
        ⟨32447, false, false, [], []⟩
      ]⟩,
    ⟨[85497, 5], [21059, 87567], .contexts [
        ⟨44094, false, false, [], []⟩
      ]⟩,
    ⟨[85497, 7], [16219, 20761, 85257], .contexts [
        ⟨32843, false, false, [], []⟩,
        ⟨42682, false, false, [16219], []⟩
      ]⟩,
    ⟨[85497, 9], [83375], .contexts [
        ⟨32443, false, false, [], []⟩,
        ⟨21071, false, false, [], []⟩
      ]⟩,
    ⟨[85497, 11], [85499], .contexts [
        ⟨32453, false, false, [], []⟩,
        ⟨32455, false, false, [], []⟩
      ]⟩,
    ⟨[85497, 13], [90615], .contexts [
        ⟨62090, false, false, [], []⟩,
        ⟨62093, false, false, [], []⟩
      ]⟩,
    ⟨[85497, 15], [21743, 87803], .contexts [
        ⟨46202, false, false, [], []⟩,
        ⟨46230, false, false, [], []⟩
      ]⟩,
    ⟨[85499, 1], [85501], .contexts [
        ⟨32480, false, false, [], []⟩,
        ⟨32483, false, false, [], []⟩
      ]⟩,
    ⟨[85499, 3], [16219, 79369], .contexts [
        ⟨32461, false, false, [], []⟩,
        ⟨32458, false, false, [], []⟩
      ]⟩,
    ⟨[85499, 5], [19521, 86807], .contexts [
        ⟨39095, false, false, [], []⟩,
        ⟨65148, false, false, [], []⟩
      ]⟩,
    ⟨[85499, 7], [16219, 83373], .contexts [
        ⟨32471, false, false, [], []⟩,
        ⟨32464, false, false, [], []⟩
      ]⟩,
    ⟨[85499, 9], [18273, 84489], .contexts [
        ⟨32478, false, false, [], []⟩,
        ⟨39107, false, false, [], []⟩
      ]⟩,
    ⟨[85499, 11], [85497], .contexts [
        ⟨32454, false, false, [], []⟩,
        ⟨32445, false, false, [], []⟩
      ]⟩,
    ⟨[91257], [47127, 86529], .contexts [
        ⟨112507, false, false, [], []⟩
      ]⟩,
    ⟨[85499, 13], [47127, 86529], .contexts [
        ⟨65139, false, false, [], []⟩,
        ⟨161119, false, false, [], []⟩
      ]⟩,
    ⟨[85499, 15], [25219, 38709, 90523], .contexts [
        ⟨61647, false, false, [], []⟩,
        ⟨103711, false, false, [25219], []⟩
      ]⟩,
    ⟨[85501, 1], [85499], .contexts [
        ⟨32481, false, false, [], []⟩,
        ⟨32455, false, false, [], []⟩
      ]⟩,
    ⟨[85501, 3], [24061, 89435], .contexts [
        ⟨56021, false, false, [], []⟩
      ]⟩,
    ⟨[85501, 5], [23859, 89307], .contexts [
        ⟨55252, false, false, [], []⟩,
        ⟨55307, false, false, [], []⟩
      ]⟩,
    ⟨[85501, 7], [18277, 85495], .contexts [
        ⟨32489, false, false, [], []⟩,
        ⟨39117, false, false, [], []⟩
      ]⟩,
    ⟨[85501, 9], [86809], .contexts [
        ⟨39102, false, false, [], []⟩,
        ⟨39104, false, false, [], []⟩
      ]⟩,
    ⟨[85501, 11], [21743, 47141, 86523], .contexts [
        ⟨46262, false, false, [], []⟩,
        ⟨161104, false, false, [], []⟩
      ]⟩,
    ⟨[85501, 13], [85503], .contexts [
        ⟨32493, false, false, [], []⟩,
        ⟨32746, false, false, [], []⟩
      ]⟩,
    ⟨[85501, 15], [25235, 39889, 90521], .contexts [
        ⟨61668, false, false, [], []⟩,
        ⟨106202, false, false, [25235], []⟩
      ]⟩,
    ⟨[85503, 1], [21743, 87793], .contexts [
        ⟨46323, false, false, [], []⟩,
        ⟨46343, false, false, [], []⟩
      ]⟩,
    ⟨[85503, 3], [24061, 89433], .contexts [
        ⟨56040, false, false, [], []⟩
      ]⟩,
    ⟨[85503, 5], [23895, 88699], .contexts [
        ⟨55315, false, false, [], []⟩
      ]⟩,
    ⟨[85503, 7], [18951, 85935], .contexts [
        ⟨35897, false, false, [], []⟩
      ]⟩,
    ⟨[88091], [39403, 87303], .contexts [
        ⟨104479, false, false, [], []⟩
      ]⟩,
    ⟨[85503, 9], [39403, 87303], .contexts [
        ⟨48368, false, false, [], []⟩,
        ⟨161134, false, false, [], []⟩
      ]⟩,
    ⟨[85503, 11], [21743, 87797], .contexts [
        ⟨46295, false, false, [], []⟩,
        ⟨46286, false, false, [], []⟩
      ]⟩,
    ⟨[85503, 13], [85501], .contexts [
        ⟨32494, false, false, [], []⟩,
        ⟨32483, false, false, [], []⟩
      ]⟩,
    ⟨[85503, 15], [85505], .contexts [
        ⟨32496, false, false, [], []⟩,
        ⟨32745, false, false, [], []⟩
      ]⟩,
    ⟨[85505, 1], [85507], .contexts [
        ⟨32500, false, false, [], []⟩,
        ⟨32743, false, false, [], []⟩
      ]⟩,
    ⟨[85505, 3], [24061, 92507], .contexts [
        ⟨72831, false, false, [], []⟩
      ]⟩,
    ⟨[85505, 5], [23895, 71391, 95799], .contexts [
        ⟨95069, false, false, [], []⟩,
        ⟨140234, false, false, [23895], []⟩
      ]⟩,
    ⟨[85505, 7], [39013, 86309], .contexts [
        ⟨104069, false, false, [], []⟩
      ]⟩,
    ⟨[85505, 9], [39419, 84327], .contexts [
        ⟨48379, false, false, [], []⟩,
        ⟨124924, false, false, [], []⟩
      ]⟩,
    ⟨[85505, 11], [21743, 40111, 95199], .contexts [
        ⟨94513, false, false, [], []⟩,
        ⟨105177, false, false, [21743], []⟩
      ]⟩,
    ⟨[85505, 13], [31237, 38997, 90727], .contexts [
        ⟨83916, false, false, [], []⟩,
        ⟨104055, false, false, [31237], []⟩
      ]⟩,
    ⟨[85505, 15], [85503], .contexts [
        ⟨32498, false, false, [], []⟩,
        ⟨32746, false, false, [], []⟩
      ]⟩,
    ⟨[85507, 1], [85505], .contexts [
        ⟨32502, false, false, [], []⟩,
        ⟨32745, false, false, [], []⟩
      ]⟩,
    ⟨[85507, 3], [85509], .contexts [
        ⟨32504, false, false, [], []⟩,
        ⟨32742, false, false, [], []⟩
      ]⟩,
    ⟨[85507, 5], [23895, 58033, 91205], .contexts [
        ⟨95165, false, false, [], []⟩,
        ⟨124944, false, false, [23895], []⟩
      ]⟩,
    ⟨[85507, 7], [21773, 38513, 86311], .contexts [
        ⟨46361, false, false, [], []⟩,
        ⟨103492, false, false, [21773], []⟩
      ]⟩,
    ⟨[85507, 9], [35715, 38535, 83089], .contexts [
        ⟨98141, false, false, [], []⟩,
        ⟨103506, false, false, [35715], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2518. -/
def y322TCIndexRaw2518 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85507, 11], [21743, 40111, 95201], .contexts [
        ⟨94535, true, false, [21740], [11]⟩,
        ⟨53, false, false, [21740, 95871], []⟩,
        ⟨46199, true, false, [], [95871]⟩,
        ⟨105187, false, false, [21743], []⟩
      ]⟩,
    ⟨[85507, 13], [21781, 85507], .contexts [
        ⟨46384, false, false, [21778], [85507, 13]⟩,
        ⟨46362, false, false, [21778, 21777], [85507, 13]⟩,
        ⟨38, true, false, [21778, 21777, 21772, 85507], [13]⟩,
        ⟨46361, false, false, [21778, 21777, 21772], [7, 13]⟩,
        ⟨46383, false, false, [21778], [86615, 7, 13]⟩,
        ⟨45750, true, false, [21778, 21773], [7, 13]⟩,
        ⟨46376, true, false, [21778], [13, 7, 13]⟩,
        ⟨15654, false, false, [21778, 85507], []⟩,
        ⟨46346, false, false, [21778], []⟩,
        ⟨46386, true, false, [], [85507]⟩,
        ⟨46386, true, false, [], [85507]⟩,
        ⟨46385, true, false, [], [85507]⟩
      ]⟩,
    ⟨[85507, 15], [21743, 87793], .contexts [
        ⟨46348, false, false, [], []⟩,
        ⟨46343, false, false, [], []⟩
      ]⟩,
    ⟨[24061, 92511], [24061, 43517, 88461], .contexts [
        ⟨108333, false, false, [24061], []⟩
      ]⟩,
    ⟨[85509, 1], [24061, 43517, 88461], .contexts [
        ⟨72859, true, false, [24058], [1]⟩,
        ⟨8, false, false, [24058, 92511], []⟩,
        ⟨56020, true, false, [], [92511]⟩,
        ⟨161155, false, false, [], []⟩
      ]⟩,
    ⟨[85509, 3], [85507], .contexts [
        ⟨32506, false, false, [], []⟩,
        ⟨32743, false, false, [], []⟩
      ]⟩,
    ⟨[85509, 5], [85511], .contexts [
        ⟨32508, false, false, [], []⟩,
        ⟨32740, false, false, [], []⟩
      ]⟩,
    ⟨[85509, 7], [21773, 38513, 86313], .contexts [
        ⟨46382, false, false, [], []⟩,
        ⟨103483, false, false, [21773], []⟩
      ]⟩,
    ⟨[85509, 9], [38507, 83091], .contexts [
        ⟨103472, false, false, [], []⟩,
        ⟨109924, false, false, [], []⟩
      ]⟩,
    ⟨[85509, 11], [21743, 40111, 95203], .contexts [
        ⟨94557, true, false, [21740], [11]⟩,
        ⟨53, false, false, [21740, 95873], []⟩,
        ⟨46199, true, false, [], [95873]⟩,
        ⟨105196, false, false, [21743], []⟩
      ]⟩,
    ⟨[85509, 13], [21799, 85509], .contexts [
        ⟨46423, false, false, [], []⟩,
        ⟨46444, false, false, [], []⟩
      ]⟩,
    ⟨[85509, 15], [29597, 38493, 90371], .contexts [
        ⟨77524, false, false, [], []⟩,
        ⟨103464, false, false, [29597], []⟩
      ]⟩,
    ⟨[85511, 1], [85513], .contexts [
        ⟨32512, false, false, [], []⟩,
        ⟨32739, false, false, [], []⟩
      ]⟩,
    ⟨[85511, 3], [23895, 43785, 88453], .contexts [
        ⟨95210, false, false, [], []⟩,
        ⟨108573, false, false, [23895], []⟩
      ]⟩,
    ⟨[85511, 5], [85509], .contexts [
        ⟨32510, false, false, [], []⟩,
        ⟨32742, false, false, [], []⟩
      ]⟩,
    ⟨[85511, 7], [21795, 85511], .contexts [
        ⟨46419, false, false, [], []⟩,
        ⟨46435, false, false, [], []⟩
      ]⟩,
    ⟨[85511, 9], [43799, 83093], .contexts [
        ⟨72955, false, false, [], []⟩,
        ⟨108585, false, false, [], []⟩
      ]⟩,
    ⟨[85511, 11], [21743, 40111, 95205], .contexts [
        ⟨94578, false, false, [], []⟩,
        ⟨105202, false, false, [21743], []⟩
      ]⟩,
    ⟨[85511, 13], [21803, 85511], .contexts [
        ⟨46449, false, false, [], []⟩,
        ⟨72963, false, false, [], []⟩
      ]⟩,
    ⟨[85511, 15], [28147, 91831], .contexts [
        ⟨72910, false, false, [], []⟩,
        ⟨116873, false, false, [], []⟩
      ]⟩,
    ⟨[85513, 1], [85511], .contexts [
        ⟨32514, false, false, [], []⟩,
        ⟨32740, false, false, [], []⟩
      ]⟩,
    ⟨[85513, 3], [28153, 85513], .contexts [
        ⟨72897, false, false, [], []⟩
      ]⟩,
    ⟨[85513, 5], [24061, 43517, 88461], .contexts [
        ⟨72872, false, false, [], []⟩,
        ⟨161155, false, false, [], []⟩
      ]⟩,
    ⟨[85513, 7], [21801, 85513], .contexts [
        ⟨46443, false, false, [], []⟩,
        ⟨46457, false, false, [], []⟩
      ]⟩,
    ⟨[85513, 9], [42199, 48707, 85413], .contexts [
        ⟨32516, false, false, [], []⟩,
        ⟨107078, false, false, [], []⟩,
        ⟨114043, false, false, [42199], []⟩
      ]⟩,
    ⟨[95877], [39093, 40135, 95207], .contexts [
        ⟨104144, false, false, [], []⟩,
        ⟨105208, false, false, [39093], []⟩
      ]⟩,
    ⟨[85513, 11], [21743, 39093, 40135, 95207], .contexts [
        ⟨94587, false, false, [], []⟩,
        ⟨161177, false, false, [21743], []⟩
      ]⟩,
    ⟨[85513, 13], [28163, 86347], .contexts [
        ⟨72923, false, false, [], []⟩
      ]⟩,
    ⟨[85513, 15], [28147, 91829], .contexts [
        ⟨72890, false, false, [], []⟩,
        ⟨111308, false, false, [], []⟩
      ]⟩,
    ⟨[85521, 1], [28163, 86355], .contexts [
        ⟨72944, false, false, [], []⟩,
        ⟨72945, false, false, [], []⟩
      ]⟩,
    ⟨[85521, 3], [42623, 83781], .contexts [
        ⟨107455, true, false, [42620], [3]⟩,
        ⟨32796, false, false, [42620], []⟩,
        ⟨32788, false, false, [42620], []⟩,
        ⟨107456, true, false, [], [18311, 83781]⟩,
        ⟨107457, true, false, [], [83781]⟩
      ]⟩,
    ⟨[85521, 5], [42629, 88469], .contexts [
        ⟨107455, true, false, [42620], [5]⟩,
        ⟨50405, false, false, [42620], []⟩,
        ⟨107456, true, false, [], [22743, 88469]⟩,
        ⟨107462, true, false, [], [88469]⟩
      ]⟩,
    ⟨[85521, 7], [21801, 85521], .contexts [
        ⟨46473, false, false, [21794], []⟩,
        ⟨32525, false, false, [21794], []⟩,
        ⟨32734, false, false, [21794], []⟩,
        ⟨32530, false, false, [21794], []⟩,
        ⟨32530, false, false, [21794], []⟩,
        ⟨46474, false, false, [21794], []⟩,
        ⟨46442, true, false, [], [85521]⟩
      ]⟩,
    ⟨[85521, 9], [42625, 86795], .contexts [
        ⟨107455, true, false, [42620], [9]⟩,
        ⟨39005, false, false, [42620], []⟩,
        ⟨107456, true, false, [], [19501, 86795]⟩,
        ⟨107460, true, false, [], [86795]⟩
      ]⟩,
    ⟨[85521, 11], [42627, 87571], .contexts [
        ⟨107455, true, false, [42620], [11]⟩,
        ⟨44246, false, false, [42620], []⟩,
        ⟨107456, true, false, [], [21109, 87571]⟩,
        ⟨107461, true, false, [], [87571]⟩
      ]⟩,
    ⟨[85521, 13], [42631, 83099], .contexts [
        ⟨32527, false, false, [], []⟩,
        ⟨107464, false, false, [], []⟩
      ]⟩,
    ⟨[85521, 15], [42281, 85219], .contexts [
        ⟨32529, false, false, [], []⟩,
        ⟨107378, false, false, [], []⟩
      ]⟩,
    ⟨[85615, 1], [20745, 85253], .contexts [
        ⟨32878, false, false, [], []⟩,
        ⟨154849, false, false, [], []⟩
      ]⟩,
    ⟨[85615, 3], [18321, 82799], .contexts [
        ⟨32861, false, false, [], []⟩,
        ⟨32868, false, false, [], []⟩
      ]⟩,
    ⟨[85615, 5], [20761, 85257], .contexts [
        ⟨32850, false, false, [], []⟩,
        ⟨151453, false, false, [], []⟩
      ]⟩,
    ⟨[85615, 7], [18321, 84487], .contexts [
        ⟨32875, true, false, [18322], [7]⟩,
        ⟨38, false, false, [18322, 84487], []⟩,
        ⟨32876, true, false, [], [84487]⟩,
        ⟨32870, false, false, [], []⟩
      ]⟩,
    ⟨[85615, 9], [20761, 42431, 86291], .contexts [
        ⟨49989, true, false, [20758], [9]⟩,
        ⟨46, false, false, [20758, 88343], []⟩,
        ⟨42672, true, false, [], [88343]⟩,
        ⟨107295, false, false, [20761], []⟩
      ]⟩,
    ⟨[85615, 11], [83375], .contexts [
        ⟨32866, false, false, [], []⟩,
        ⟨21071, false, false, [], []⟩
      ]⟩,
    ⟨[85615, 13], [18321, 88471], .contexts [
        ⟨50736, false, false, [], []⟩,
        ⟨56101, false, false, [], []⟩
      ]⟩,
    ⟨[85615, 15], [22345, 39669, 40525, 40559, 85677], .contexts [
        ⟨48737, false, false, [], []⟩,
        ⟨152790, false, false, [22345], []⟩
      ]⟩,
    ⟨[85619, 1], [22691, 88345], .contexts [
        ⟨50010, true, false, [22688], [1]⟩,
        ⟨8, false, false, [22688, 88345], []⟩,
        ⟨50011, true, false, [], [88345]⟩
      ]⟩,
    ⟨[85619, 3], [18975, 86231], .contexts [
        ⟨36076, false, false, [], []⟩
      ]⟩,
    ⟨[85619, 5], [19907, 86791], .contexts [
        ⟨40435, false, false, [], []⟩
      ]⟩,
    ⟨[85619, 7], [18321, 23013, 45539, 86271], .contexts [
        ⟨40624, true, false, [18322], [7]⟩,
        ⟨38, false, false, [18322, 87205], []⟩,
        ⟨32876, true, false, [], [87205]⟩,
        ⟨158487, false, false, [18321], []⟩
      ]⟩,
    ⟨[85619, 9], [20745, 85253], .contexts [
        ⟨32888, false, false, [], []⟩,
        ⟨154849, false, false, [], []⟩
      ]⟩,
    ⟨[85619, 11], [85621], .contexts [
        ⟨32890, false, false, [], []⟩,
        ⟨32893, false, false, [], []⟩
      ]⟩,
    ⟨[85619, 13], [29243, 92951], .contexts [
        ⟨76166, false, false, [], []⟩,
        ⟨76206, false, false, [], []⟩
      ]⟩,
    ⟨[85619, 15], [34399, 95759], .contexts [
        ⟨93928, true, false, [34396], [15]⟩,
        ⟨1, false, false, [34396, 95759], []⟩,
        ⟨93929, true, false, [], [95759]⟩
      ]⟩,
    ⟨[85621, 1], [85623], .contexts [
        ⟨32902, false, false, [], []⟩,
        ⟨33153, false, false, [], []⟩
      ]⟩,
    ⟨[85621, 3], [18975, 86233], .contexts [
        ⟨36095, false, false, [], []⟩,
        ⟨50035, false, false, [], []⟩
      ]⟩,
    ⟨[85621, 5], [22243, 88089], .contexts [
        ⟨48260, false, false, [], []⟩,
        ⟨48274, false, false, [], []⟩
      ]⟩,
    ⟨[85621, 7], [18321, 39555, 84453], .contexts [
        ⟨40637, false, false, [], []⟩,
        ⟨104662, false, false, [18321], []⟩
      ]⟩,
    ⟨[85621, 9], [83381], .contexts [
        ⟨32899, false, false, [], []⟩,
        ⟨21112, false, false, [], []⟩
      ]⟩,
    ⟨[85621, 11], [85619], .contexts [
        ⟨32892, false, false, [], []⟩,
        ⟨33154, false, false, [], []⟩
      ]⟩,
    ⟨[85621, 13], [88347], .contexts [
        ⟨50030, false, false, [], []⟩,
        ⟨50033, false, false, [], []⟩
      ]⟩,
    ⟨[85621, 15], [22699, 91741], .contexts [
        ⟨67467, true, false, [22696], [15]⟩,
        ⟨1, false, false, [22696, 91741], []⟩,
        ⟨50027, true, false, [], [91741]⟩
      ]⟩,
    ⟨[85623, 1], [85621], .contexts [
        ⟨32903, false, false, [], []⟩,
        ⟨32893, false, false, [], []⟩
      ]⟩,
    ⟨[85623, 3], [18981, 85623], .contexts [
        ⟨36115, false, false, [], []⟩,
        ⟨36120, false, false, [], []⟩
      ]⟩,
    ⟨[85623, 5], [34979, 42021, 70205, 90035], .contexts [
        ⟨95637, false, false, [], []⟩,
        ⟨154867, false, false, [34979], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2519. -/
def y322TCIndexRaw2519 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[87209], [23013, 39545, 84455], .contexts [
        ⟨51380, false, false, [], []⟩,
        ⟨104658, false, false, [], []⟩
      ]⟩,
    ⟨[85623, 7], [18321, 23013, 39545, 84455], .contexts [
        ⟨40652, false, false, [], []⟩,
        ⟨161216, false, false, [18321], []⟩
      ]⟩,
    ⟨[85623, 9], [22265, 39773, 43861, 84449], .contexts [
        ⟨48315, true, false, [22266], [9]⟩,
        ⟨46, false, false, [22266, 84495], []⟩,
        ⟨48316, true, false, [], [84495]⟩,
        ⟨155455, false, false, [22265], []⟩
      ]⟩,
    ⟨[85623, 11], [22699, 88345], .contexts [
        ⟨50028, false, false, [], []⟩
      ]⟩,
    ⟨[85625], [39511, 84315], .contexts [
        ⟨104615, false, false, [], []⟩
      ]⟩,
    ⟨[85623, 13], [39511, 84315], .contexts [
        ⟨32905, false, false, [], []⟩,
        ⟨161220, false, false, [], []⟩
      ]⟩,
    ⟨[85623, 15], [22699, 91739], .contexts [
        ⟨67443, false, false, [], []⟩
      ]⟩,
    ⟨[85627, 1], [85629], .contexts [
        ⟨32913, false, false, [], []⟩,
        ⟨33148, false, false, [], []⟩
      ]⟩,
    ⟨[85627, 3], [18981, 85627], .contexts [
        ⟨36145, false, false, [], []⟩,
        ⟨36147, false, false, [], []⟩
      ]⟩,
    ⟨[85627, 5], [46535, 57017, 87623], .contexts [
        ⟨111886, false, false, [], []⟩,
        ⟨123803, false, false, [46535], []⟩
      ]⟩,
    ⟨[85627, 7], [18321, 63451, 86067], .contexts [
        ⟨40703, true, false, [18322], [7]⟩,
        ⟨38, false, false, [18322, 87213], []⟩,
        ⟨32876, true, false, [], [87213]⟩,
        ⟨131443, false, false, [18321], []⟩
      ]⟩,
    ⟨[85627, 9], [22265, 24299, 85279], .contexts [
        ⟨48353, false, false, [], []⟩,
        ⟨57231, false, false, [22265], []⟩
      ]⟩,
    ⟨[85627, 11], [69577, 90953], .contexts [
        ⟨138177, false, false, [], []⟩
      ]⟩,
    ⟨[85627, 13], [28915, 90493], .contexts [
        ⟨75116, false, false, [], []⟩,
        ⟨122406, false, false, [], []⟩
      ]⟩,
    ⟨[85627, 15], [39511, 84315], .contexts [
        ⟨32911, false, false, [], []⟩,
        ⟨161220, false, false, [], []⟩
      ]⟩,
    ⟨[85629, 1], [85627], .contexts [
        ⟨32915, false, false, [], []⟩,
        ⟨33150, false, false, [], []⟩
      ]⟩,
    ⟨[85629, 3], [85631], .contexts [
        ⟨32917, false, false, [], []⟩,
        ⟨33147, false, false, [], []⟩
      ]⟩,
    ⟨[85629, 5], [36475, 68059, 88271], .contexts [
        ⟨100248, false, false, [], []⟩,
        ⟨136700, false, false, [36475], []⟩
      ]⟩,
    ⟨[85629, 7], [18321, 87215], .contexts [
        ⟨40721, false, false, [], []⟩,
        ⟨122432, false, false, [], []⟩
      ]⟩,
    ⟨[85629, 9], [36467, 85901], .contexts [
        ⟨100226, false, false, [], []⟩,
        ⟨100229, false, false, [], []⟩
      ]⟩,
    ⟨[85629, 11], [67603, 68757, 90955], .contexts [
        ⟨136153, false, false, [], []⟩,
        ⟨138005, false, false, [67603], []⟩
      ]⟩,
    ⟨[85629, 13], [55701, 89813], .contexts [
        ⟨122243, false, false, [], []⟩,
        ⟨122399, false, false, [], []⟩
      ]⟩,
    ⟨[85629, 15], [46537, 84313], .contexts [
        ⟨111893, false, false, [], []⟩
      ]⟩,
    ⟨[85631, 1], [18983, 85631], .contexts [
        ⟨36153, false, false, [], []⟩,
        ⟨36154, false, false, [], []⟩
      ]⟩,
    ⟨[85631, 3], [85629], .contexts [
        ⟨32919, false, false, [], []⟩,
        ⟨33148, false, false, [], []⟩
      ]⟩,
    ⟨[85631, 5], [85633], .contexts [
        ⟨32921, false, false, [], []⟩,
        ⟨33145, false, false, [], []⟩
      ]⟩,
    ⟨[85631, 7], [18321, 52881, 86457], .contexts [
        ⟨40736, true, false, [18322], [7]⟩,
        ⟨38, false, false, [18322, 87217], []⟩,
        ⟨32876, true, false, [], [87217]⟩,
        ⟨118962, false, false, [18321], []⟩
      ]⟩,
    ⟨[85631, 9], [59651, 59827, 63889, 83717], .contexts [
        ⟨126886, false, false, [], []⟩,
        ⟨153529, false, false, [59651], []⟩
      ]⟩,
    ⟨[85631, 11], [54327, 67611, 67633, 68739, 90957], .contexts [
        ⟨120614, true, false, [54324], [11]⟩,
        ⟨53, false, false, [54324, 96275], []⟩,
        ⟨120615, true, false, [], [96275]⟩,
        ⟨154987, false, false, [54327], []⟩
      ]⟩,
    ⟨[85631, 13], [55701, 89815], .contexts [
        ⟨122429, false, false, [], []⟩,
        ⟨122426, false, false, [], []⟩
      ]⟩,
    ⟨[85631, 15], [73149, 96905], .contexts [
        ⟨143228, false, false, [], []⟩,
        ⟨146951, false, false, [], []⟩
      ]⟩,
    ⟨[85633, 1], [18981, 85633], .contexts [
        ⟨32925, false, false, [], []⟩,
        ⟨131959, false, false, [], []⟩
      ]⟩,
    ⟨[85633, 3], [36667, 84633], .contexts [
        ⟨100597, false, false, [], []⟩,
        ⟨100646, false, false, [], []⟩
      ]⟩,
    ⟨[85633, 5], [85631], .contexts [
        ⟨32923, false, false, [], []⟩,
        ⟨33147, false, false, [], []⟩
      ]⟩,
    ⟨[85633, 7], [75203, 97165], .contexts [
        ⟨146448, false, false, [], []⟩,
        ⟨146954, false, false, [], []⟩
      ]⟩,
    ⟨[85633, 9], [18983, 63877, 83715], .contexts [
        ⟨36160, false, false, [], []⟩,
        ⟨131971, false, false, [18983], []⟩
      ]⟩,
    ⟨[85633, 11], [64103, 68707, 68725, 90959], .contexts [
        ⟨132211, false, false, [], []⟩,
        ⟨154960, false, false, [64103], []⟩
      ]⟩,
    ⟨[85633, 13], [55701, 62535, 86011], .contexts [
        ⟨130187, false, false, [], []⟩,
        ⟨130362, false, false, [55701], []⟩
      ]⟩,
    ⟨[85633, 15], [97195], .contexts [
        ⟨146943, false, false, [], []⟩,
        ⟨146944, false, false, [], []⟩
      ]⟩,
    ⟨[85639, 1], [85641], .contexts [
        ⟨32936, false, false, [], []⟩,
        ⟨33139, false, false, [], []⟩
      ]⟩,
    ⟨[85639, 3], [36703, 84637], .contexts [
        ⟨100729, false, false, [], []⟩,
        ⟨132696, false, false, [], []⟩
      ]⟩,
    ⟨[85639, 5], [60641, 83439], .contexts [
        ⟨128028, false, false, [], []⟩
      ]⟩,
    ⟨[85639, 7], [68287, 95559], .contexts [
        ⟨136925, false, false, [], []⟩
      ]⟩,
    ⟨[85639, 9], [60649, 88651], .contexts [
        ⟨128031, true, false, [60644], [9]⟩,
        ⟨64594, false, false, [60644], []⟩,
        ⟨128033, false, false, [60644], []⟩,
        ⟨128034, true, false, [], [60607, 88651]⟩,
        ⟨128035, true, false, [], [88651]⟩
      ]⟩,
    ⟨[85639, 11], [63877, 83715], .contexts [
        ⟨32934, false, false, [], []⟩,
        ⟨131971, false, false, [], []⟩
      ]⟩,
    ⟨[85639, 13], [60651, 85051], .contexts [
        ⟨128037, false, false, [], []⟩,
        ⟨128465, false, false, [], []⟩
      ]⟩,
    ⟨[85639, 15], [64037, 65193, 84279], .contexts [
        ⟨132132, false, false, [], []⟩,
        ⟨133425, false, false, [64037], []⟩
      ]⟩,
    ⟨[85641, 1], [85639], .contexts [
        ⟨32938, false, false, [], []⟩,
        ⟨33141, false, false, [], []⟩
      ]⟩,
    ⟨[85641, 3], [59481, 89067], .contexts [
        ⟨126682, false, false, [], []⟩,
        ⟨132672, false, false, [], []⟩
      ]⟩,
    ⟨[85641, 5], [59479, 63925, 83723], .contexts [
        ⟨126680, false, false, [], []⟩,
        ⟨132026, false, false, [59479], []⟩
      ]⟩,
    ⟨[85641, 7], [59991, 63841, 83709], .contexts [
        ⟨127252, false, false, [], []⟩,
        ⟨131917, false, false, [59991], []⟩
      ]⟩,
    ⟨[85641, 9], [59477, 89007], .contexts [
        ⟨126677, false, false, [], []⟩
      ]⟩,
    ⟨[85641, 11], [59477, 68917, 86167], .contexts [
        ⟨126678, false, false, [], []⟩,
        ⟨137498, false, false, [59477], []⟩
      ]⟩,
    ⟨[85641, 13], [85643], .contexts [
        ⟨32940, false, false, [], []⟩,
        ⟨33137, false, false, [], []⟩
      ]⟩,
    ⟨[85641, 15], [64545, 84277], .contexts [
        ⟨132693, false, false, [], []⟩,
        ⟨133393, false, false, [], []⟩
      ]⟩,
    ⟨[54185, 96509], [54185, 64603, 64757, 86019], .contexts [
        ⟨159866, false, false, [54185], []⟩
      ]⟩,
    ⟨[85643, 1], [54185, 64603, 64757, 86019], .contexts [
        ⟨120435, false, false, [], []⟩,
        ⟨161271, false, false, [], []⟩
      ]⟩,
    ⟨[85643, 3], [54187, 85913], .contexts [
        ⟨120439, false, false, [], []⟩,
        ⟨128471, false, false, [], []⟩
      ]⟩,
    ⟨[85643, 5], [66523, 93977], .contexts [
        ⟨134914, false, false, [], []⟩
      ]⟩,
    ⟨[85643, 7], [63991, 83707], .contexts [
        ⟨132086, false, false, [], []⟩
      ]⟩,
    ⟨[85643, 9], [59185, 60701, 91967], .contexts [
        ⟨126330, false, false, [], []⟩,
        ⟨128099, false, false, [59185], []⟩
      ]⟩,
    ⟨[85643, 11], [61035, 91145], .contexts [
        ⟨128464, false, false, [], []⟩,
        ⟨128474, false, false, [], []⟩
      ]⟩,
    ⟨[85643, 13], [85641], .contexts [
        ⟨32942, false, false, [], []⟩,
        ⟨33139, false, false, [], []⟩
      ]⟩,
    ⟨[85643, 15], [85645], .contexts [
        ⟨32944, false, false, [], []⟩,
        ⟨33135, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2520. -/
def y322TCIndexRaw2520 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85645, 1], [85647], .contexts [
        ⟨32948, false, false, [], []⟩,
        ⟨33132, false, false, [], []⟩
      ]⟩,
    ⟨[85645, 3], [48189, 64771, 86025], .contexts [
        ⟨113521, false, false, [], []⟩,
        ⟨132968, false, false, [48189], []⟩
      ]⟩,
    ⟨[85645, 5], [54199, 59153, 87273], .contexts [
        ⟨120452, false, false, [], []⟩,
        ⟨126296, false, false, [54199], []⟩
      ]⟩,
    ⟨[85645, 7], [66755, 97189], .contexts [
        ⟨146848, true, false, [66756], [7]⟩,
        ⟨38, false, false, [66756, 97189], []⟩,
        ⟨135141, true, false, [], [97189]⟩
      ]⟩,
    ⟨[85645, 9], [59275, 91521], .contexts [
        ⟨126457, false, false, [], []⟩,
        ⟨133304, false, false, [], []⟩
      ]⟩,
    ⟨[85645, 11], [59673, 60955, 90295], .contexts [
        ⟨126910, false, false, [], []⟩,
        ⟨128452, false, false, [59673], []⟩
      ]⟩,
    ⟨[85645, 13], [61059, 84763], .contexts [
        ⟨128497, false, false, [], []⟩,
        ⟨128489, false, false, [], []⟩
      ]⟩,
    ⟨[85645, 15], [85643], .contexts [
        ⟨32946, false, false, [], []⟩,
        ⟨33137, false, false, [], []⟩
      ]⟩,
    ⟨[85647, 1], [85645], .contexts [
        ⟨32950, false, false, [], []⟩,
        ⟨33135, false, false, [], []⟩
      ]⟩,
    ⟨[85647, 3], [85649], .contexts [
        ⟨32952, false, false, [], []⟩,
        ⟨33130, false, false, [], []⟩
      ]⟩,
    ⟨[85647, 5], [54021, 84753], .contexts [
        ⟨120226, false, false, [], []⟩,
        ⟨127853, false, false, [], []⟩
      ]⟩,
    ⟨[85647, 7], [66755, 89039], .contexts [
        ⟨135142, false, false, [], []⟩,
        ⟨135148, false, false, [], []⟩
      ]⟩,
    ⟨[85647, 9], [73129, 96903], .contexts [
        ⟨143186, true, false, [73126], [9]⟩,
        ⟨46, false, false, [73126, 96903], []⟩,
        ⟨143187, true, false, [], [96903]⟩
      ]⟩,
    ⟨[85647, 11], [60515, 60947, 90293], .contexts [
        ⟨127862, false, false, [], []⟩,
        ⟨128345, false, false, [60515], []⟩
      ]⟩,
    ⟨[85647, 13], [59553, 63819, 85785], .contexts [
        ⟨126781, false, false, [], []⟩,
        ⟨131979, false, false, [59553], []⟩
      ]⟩,
    ⟨[85647, 15], [54185, 64603, 64757, 86019], .contexts [
        ⟨128442, false, false, [], []⟩,
        ⟨161271, false, false, [], []⟩
      ]⟩,
    ⟨[85649, 1], [40689, 59129, 87265], .contexts [
        ⟨105714, false, false, [], []⟩,
        ⟨126273, false, false, [40689], []⟩
      ]⟩,
    ⟨[85649, 3], [85647], .contexts [
        ⟨32954, false, false, [], []⟩,
        ⟨33132, false, false, [], []⟩
      ]⟩,
    ⟨[85649, 5], [85651], .contexts [
        ⟨32956, false, false, [], []⟩,
        ⟨33128, false, false, [], []⟩
      ]⟩,
    ⟨[85649, 7], [40691, 83885], .contexts [
        ⟨105716, false, false, [], []⟩,
        ⟨113536, false, false, [], []⟩
      ]⟩,
    ⟨[85649, 9], [46093, 94205], .contexts [
        ⟨111408, false, false, [], []⟩,
        ⟨120229, false, false, [], []⟩
      ]⟩,
    ⟨[85649, 11], [59901, 60871, 90269], .contexts [
        ⟨127162, false, false, [], []⟩,
        ⟨128282, false, false, [59901], []⟩
      ]⟩,
    ⟨[85649, 13], [45199, 52561, 55033, 63819, 85783], .contexts [
        ⟨110250, false, false, [], []⟩,
        ⟨156494, false, false, [45199], []⟩
      ]⟩,
    ⟨[85649, 15], [71721, 96767], .contexts [
        ⟨140595, true, false, [44450], [15]⟩,
        ⟨1, false, false, [44450, 96767], []⟩,
        ⟨140596, true, false, [], [96767]⟩
      ]⟩,
    ⟨[85651, 1], [44431, 85133], .contexts [
        ⟨32960, false, false, [], []⟩,
        ⟨109319, false, false, [], []⟩
      ]⟩,
    ⟨[85651, 3], [40679, 90845], .contexts [
        ⟨105703, false, false, [], []⟩,
        ⟨120219, false, false, [], []⟩
      ]⟩,
    ⟨[85651, 5], [85649], .contexts [
        ⟨32958, false, false, [], []⟩,
        ⟨33130, false, false, [], []⟩
      ]⟩,
    ⟨[85651, 7], [40681, 53167, 91297], .contexts [
        ⟨105698, true, false, [40666], [7]⟩,
        ⟨100768, true, false, [40666, 36738], [7]⟩,
        ⟨38, false, false, [40666, 36738, 92335], []⟩,
        ⟨100769, true, false, [40666], [92335]⟩,
        ⟨100765, false, false, [40666], []⟩,
        ⟨105687, true, false, [], [36737, 92335]⟩,
        ⟨105706, true, false, [], [92335]⟩,
        ⟨119302, false, false, [40681], []⟩
      ]⟩,
    ⟨[85651, 9], [40675, 87993], .contexts [
        ⟨105698, true, false, [40666], [9]⟩,
        ⟨53899, false, false, [40666], []⟩,
        ⟨102400, false, false, [40666], []⟩,
        ⟨105690, true, false, [], [37613, 87993]⟩,
        ⟨105699, true, false, [], [87993]⟩
      ]⟩,
    ⟨[85651, 11], [40665, 52785, 85187], .contexts [
        ⟨105705, false, false, [], []⟩,
        ⟨118851, false, false, [40665], []⟩
      ]⟩,
    ⟨[85651, 13], [40677, 83887], .contexts [
        ⟨105701, false, false, [], []⟩,
        ⟨113503, false, false, [], []⟩
      ]⟩,
    ⟨[94289], [42683, 44449, 85137], .contexts [
        ⟨109326, false, false, [], []⟩,
        ⟨109363, false, false, [], []⟩
      ]⟩,
    ⟨[85651, 15], [40669, 42683, 44449, 85137], .contexts [
        ⟨105704, false, false, [], []⟩,
        ⟨161311, false, false, [40669], []⟩
      ]⟩,
    ⟨[85657, 1], [40639, 84463], .contexts [
        ⟨32971, false, false, [], []⟩,
        ⟨105659, false, false, [], []⟩
      ]⟩,
    ⟨[85657, 3], [40649, 83087], .contexts [
        ⟨105662, true, false, [40644], [3]⟩,
        ⟨44423, false, false, [40644], []⟩,
        ⟨44417, false, false, [40644], []⟩,
        ⟨105663, true, false, [], [21183, 83087]⟩,
        ⟨105669, true, false, [], [83087]⟩
      ]⟩,
    ⟨[85657, 5], [40643, 85929], .contexts [
        ⟨105665, false, false, [], []⟩
      ]⟩,
    ⟨[85657, 7], [40655, 84323], .contexts [
        ⟨105662, true, false, [40644], [7]⟩,
        ⟨78350, false, false, [40644], []⟩,
        ⟨104490, false, false, [40644, 29895], []⟩,
        ⟨105663, true, false, [], [29895, 39413, 84323]⟩,
        ⟨105671, true, false, [], [39413, 84323]⟩,
        ⟨105672, true, false, [], [84323]⟩
      ]⟩,
    ⟨[85657, 9], [40647, 86209], .contexts [
        ⟨105662, true, false, [40644], [9]⟩,
        ⟨35912, false, false, [40644], []⟩,
        ⟨35905, false, false, [40644], []⟩,
        ⟨105663, true, false, [], [18943, 86209]⟩,
        ⟨105668, true, false, [], [86209]⟩
      ]⟩,
    ⟨[85657, 11], [40663, 83823], .contexts [
        ⟨32969, false, false, [], []⟩,
        ⟨105682, false, false, [], []⟩
      ]⟩,
    ⟨[85657, 13], [40651, 85201], .contexts [
        ⟨105662, true, false, [40644], [13]⟩,
        ⟨51726, true, false, [40644, 23136], [13]⟩,
        ⟨59, false, false, [40644, 23136, 85201], []⟩,
        ⟨51727, true, false, [40644], [85201]⟩,
        ⟨105663, true, false, [], [23139, 85201]⟩,
        ⟨105670, true, false, [], [85201]⟩
      ]⟩,
    ⟨[85657, 15], [40659, 84467], .contexts [
        ⟨105677, false, false, [], []⟩
      ]⟩,
    ⟨[85669, 1], [85671], .contexts [
        ⟨32990, false, false, [], []⟩,
        ⟨33118, false, false, [], []⟩
      ]⟩,
    ⟨[85669, 3], [40611, 95369], .contexts [
        ⟨105637, true, false, [40612], [3]⟩,
        ⟨89534, false, false, [40612], []⟩,
        ⟨89654, false, false, [40612], []⟩,
        ⟨105633, true, false, [], [95369]⟩
      ]⟩,
    ⟨[85669, 5], [40631, 85207], .contexts [
        ⟨32988, false, false, [], []⟩,
        ⟨105645, false, false, [], []⟩
      ]⟩,
    ⟨[85669, 7], [40625, 83899], .contexts [
        ⟨105637, true, false, [40612], [7]⟩,
        ⟨89703, false, false, [40612], []⟩,
        ⟨89700, false, false, [40612], []⟩,
        ⟨105622, true, false, [], [32867, 83899]⟩,
        ⟨105638, true, false, [], [83899]⟩
      ]⟩,
    ⟨[85669, 9], [40627, 41319, 85379], .contexts [
        ⟨105637, true, false, [40612], [9]⟩,
        ⟨89706, false, false, [40612], []⟩,
        ⟨89774, false, false, [40612], []⟩,
        ⟨105622, true, false, [], [32875, 87801]⟩,
        ⟨105639, true, false, [], [87801]⟩,
        ⟨106221, false, false, [40627], []⟩
      ]⟩,
    ⟨[85669, 11], [40611, 56567, 84677], .contexts [
        ⟨105641, false, false, [], []⟩,
        ⟨123274, false, false, [40611], []⟩
      ]⟩,
    ⟨[85669, 13], [40629, 62741, 84667], .contexts [
        ⟨105637, true, false, [40612], [13]⟩,
        ⟨89773, false, false, [40612], []⟩,
        ⟨89960, false, false, [40612], []⟩,
        ⟨105622, true, false, [], [32921, 89289]⟩,
        ⟨105640, true, false, [], [89289]⟩,
        ⟨130613, false, false, [40629], []⟩
      ]⟩,
    ⟨[85669, 15], [40615, 42033, 47157, 86521], .contexts [
        ⟨105637, true, false, [40612], [15]⟩,
        ⟨97417, true, false, [40612, 32898], [15]⟩,
        ⟨1, false, false, [40612, 32898, 96365], []⟩,
        ⟨89735, true, false, [40612], [96365]⟩,
        ⟨105627, true, false, [], [96365]⟩,
        ⟨105622, true, false, [], [32901, 96365]⟩,
        ⟨105626, true, false, [], [96365]⟩,
        ⟨154853, false, false, [40615], []⟩
      ]⟩,
    ⟨[85671, 1], [85669], .contexts [
        ⟨32992, false, false, [], []⟩,
        ⟨33119, false, false, [], []⟩
      ]⟩,
    ⟨[85671, 3], [40617, 87037], .contexts [
        ⟨105621, true, false, [40612], [3]⟩,
        ⟨89674, false, false, [40612], []⟩,
        ⟨89873, false, false, [40612], []⟩,
        ⟨105622, true, false, [], [32861, 87037]⟩,
        ⟨105628, true, false, [], [87037]⟩
      ]⟩,
    ⟨[85671, 5], [40619, 85209], .contexts [
        ⟨105621, true, false, [40612], [5]⟩,
        ⟨89714, false, false, [40612], []⟩,
        ⟨89879, false, false, [40612], []⟩,
        ⟨105622, true, false, [], [32881, 85209]⟩,
        ⟨105629, true, false, [], [85209]⟩
      ]⟩,
    ⟨[85671, 7], [40621, 83897], .contexts [
        ⟨105621, true, false, [40612], [7]⟩,
        ⟨89720, false, false, [40612], []⟩,
        ⟨89886, false, false, [40612], []⟩,
        ⟨105622, true, false, [], [32887, 83897]⟩,
        ⟨105630, true, false, [], [83897]⟩
      ]⟩,
    ⟨[85671, 9], [85673], .contexts [
        ⟨32994, false, false, [], []⟩,
        ⟨33117, false, false, [], []⟩
      ]⟩,
    ⟨[85671, 11], [40611, 95373], .contexts [
        ⟨105621, true, false, [40612], [11]⟩,
        ⟨89868, false, false, [40612], []⟩,
        ⟨89870, false, false, [40612], []⟩,
        ⟨105633, true, false, [], [95373]⟩
      ]⟩,
    ⟨[85671, 13], [40623, 83461], .contexts [
        ⟨105632, false, false, [], []⟩
      ]⟩,
    ⟨[85671, 15], [40615, 83379], .contexts [
        ⟨105621, true, false, [40612], [15]⟩,
        ⟨89529, false, false, [40612], []⟩,
        ⟨89786, false, false, [40612], []⟩,
        ⟨105627, true, false, [], [83379]⟩,
        ⟨105625, true, false, [], [32901, 83379]⟩,
        ⟨105626, true, false, [], [83379]⟩
      ]⟩,
    ⟨[85673, 1], [40599, 88207], .contexts [
        ⟨105605, true, false, [40594], [1]⟩,
        ⟨68208, false, false, [40594], []⟩,
        ⟨68205, false, false, [40594], []⟩,
        ⟨105606, true, false, [], [26689, 88207]⟩,
        ⟨105609, true, false, [], [88207]⟩
      ]⟩,
    ⟨[85673, 3], [40601, 42573, 47713, 84037], .contexts [
        ⟨105605, true, false, [40594], [3]⟩,
        ⟨68231, true, false, [40594, 26698], [3]⟩,
        ⟨20, false, false, [40594, 26698, 87035], []⟩,
        ⟨68232, true, false, [40594], [87035]⟩,
        ⟨68225, false, false, [40594], []⟩,
        ⟨105606, true, false, [], [26697, 87035]⟩,
        ⟨105610, true, false, [], [87035]⟩,
        ⟨152962, false, false, [40601], []⟩
      ]⟩,
    ⟨[85673, 5], [40603, 88211], .contexts [
        ⟨105605, true, false, [40594], [5]⟩,
        ⟨68237, true, false, [40594, 26704], [5]⟩,
        ⟨28, false, false, [40594, 26704, 88211], []⟩,
        ⟨68235, false, true, [40594], [88211]⟩,
        ⟨105606, true, false, [], [26703, 88211]⟩,
        ⟨105611, true, false, [], [88211]⟩
      ]⟩,
    ⟨[85673, 7], [40605, 83327], .contexts [
        ⟨105605, true, false, [40594], [7]⟩,
        ⟨68243, true, false, [40594, 26710], [7]⟩,
        ⟨38, false, false, [40594, 26710, 83327], []⟩,
        ⟨68241, false, true, [40594], [83327]⟩,
        ⟨68240, false, false, [40594], []⟩,
        ⟨105606, true, false, [], [26709, 83327]⟩,
        ⟨105612, true, false, [], [83327]⟩
      ]⟩,
    ⟨[85673, 9], [85671], .contexts [
        ⟨32996, false, false, [], []⟩,
        ⟨33118, false, false, [], []⟩
      ]⟩,
    ⟨[85673, 11], [85675], .contexts [
        ⟨32998, false, false, [], []⟩,
        ⟨33116, false, false, [], []⟩
      ]⟩,
    ⟨[85673, 13], [40609, 86683], .contexts [
        ⟨105605, true, false, [40594], [13]⟩,
        ⟨68280, false, false, [40594], []⟩,
        ⟨68299, false, false, [40594], []⟩,
        ⟨105606, true, false, [], [26743, 86683]⟩,
        ⟨105616, true, false, [], [86683]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2521. -/
def y322TCIndexRaw2521 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85673, 15], [40597, 83377], .contexts [
        ⟨105608, false, false, [], []⟩
      ]⟩,
    ⟨[85675, 1], [85677], .contexts [
        ⟨33002, false, false, [], []⟩,
        ⟨33114, false, false, [], []⟩
      ]⟩,
    ⟨[85675, 3], [40587, 40707, 42555, 86363], .contexts [
        ⟨105594, true, false, [40576], [3]⟩,
        ⟨104782, true, false, [40576, 39668], [3]⟩,
        ⟨69199, false, false, [40576, 39668], []⟩,
        ⟨93901, false, false, [40576, 39668], []⟩,
        ⟨104769, true, false, [40576], [27057, 92045]⟩,
        ⟨104785, true, false, [40576], [92045]⟩,
        ⟨105595, true, false, [], [39689, 92045]⟩,
        ⟨105599, true, false, [], [92045]⟩,
        ⟨156122, false, false, [40587], []⟩
      ]⟩,
    ⟨[85675, 5], [40583, 41383, 85389], .contexts [
        ⟨105594, true, false, [40576], [5]⟩,
        ⟨104782, true, false, [40576, 39668], [5]⟩,
        ⟨48743, false, false, [40576, 39668], []⟩,
        ⟨93906, false, false, [40576, 39668], []⟩,
        ⟨104771, true, false, [40576], [86221]⟩,
        ⟨105595, true, false, [], [39671, 86221]⟩,
        ⟨105597, true, false, [], [86221]⟩,
        ⟨106307, false, false, [40583], []⟩
      ]⟩,
    ⟨[85675, 7], [40585, 88973], .contexts [
        ⟨105594, true, false, [40576], [7]⟩,
        ⟨104782, true, false, [40576, 39668], [7]⟩,
        ⟨53411, false, false, [40576, 39668], []⟩,
        ⟨93911, false, false, [40576, 39668], []⟩,
        ⟨104769, true, false, [40576], [23409, 88973]⟩,
        ⟨104783, true, false, [40576], [88973]⟩,
        ⟨105595, true, false, [], [39685, 88973]⟩,
        ⟨105598, true, false, [], [88973]⟩
      ]⟩,
    ⟨[85675, 9], [40591, 95759], .contexts [
        ⟨105594, true, false, [40576], [9]⟩,
        ⟨104782, true, false, [40576, 39668], [9]⟩,
        ⟨93892, false, false, [40576, 39668], []⟩,
        ⟨93894, false, false, [40576, 39668], []⟩,
        ⟨104787, true, false, [40576], [95759]⟩,
        ⟨104787, true, false, [40576], [95759]⟩,
        ⟨104781, true, false, [40576], [95759]⟩,
        ⟨105595, true, false, [], [39667, 95759]⟩,
        ⟨105602, true, false, [], [95759]⟩
      ]⟩,
    ⟨[85675, 11], [85673], .contexts [
        ⟨33000, false, false, [], []⟩,
        ⟨33117, false, false, [], []⟩
      ]⟩,
    ⟨[85675, 13], [40589, 40845, 93825], .contexts [
        ⟨105601, false, false, [], []⟩,
        ⟨105808, false, false, [40589], []⟩
      ]⟩,
    ⟨[85675, 15], [40579, 85253], .contexts [
        ⟨105594, true, false, [40576], [15]⟩,
        ⟨48464, false, false, [40576], []⟩,
        ⟨104791, false, false, [40576], []⟩,
        ⟨105595, true, false, [], [39693, 85253]⟩,
        ⟨105596, true, false, [], [85253]⟩
      ]⟩,
    ⟨[85677, 1], [85675], .contexts [
        ⟨33004, false, false, [], []⟩,
        ⟨33116, false, false, [], []⟩
      ]⟩,
    ⟨[85677, 3], [40563, 82839], .contexts [
        ⟨105582, true, false, [40558], [3]⟩,
        ⟨105555, true, false, [40558, 40524], [3]⟩,
        ⟨48470, false, false, [40558, 40524], []⟩,
        ⟨104765, false, false, [40558, 40524], []⟩,
        ⟨105556, true, false, [40558], [39663, 82839]⟩,
        ⟨105557, true, false, [40558], [82839]⟩,
        ⟨105583, true, false, [], [40529, 82839]⟩,
        ⟨105585, true, false, [], [82839]⟩
      ]⟩,
    ⟨[85677, 5], [40565, 41383, 85387], .contexts [
        ⟨105582, true, false, [40558], [5]⟩,
        ⟨105555, true, false, [40558, 40524], [5]⟩,
        ⟨104768, true, false, [40558, 40524, 39668], [5]⟩,
        ⟨48717, false, false, [40558, 40524, 39668], []⟩,
        ⟨104771, true, false, [40558, 40524], [86223]⟩,
        ⟨105556, true, false, [40558], [39671, 86223]⟩,
        ⟨105558, true, false, [40558], [86223]⟩,
        ⟨105583, true, false, [], [40531, 86223]⟩,
        ⟨105586, true, false, [], [86223]⟩,
        ⟨106267, false, false, [40565], []⟩
      ]⟩,
    ⟨[85677, 7], [40567, 83573], .contexts [
        ⟨105582, true, false, [40558], [7]⟩,
        ⟨105555, true, false, [40558, 40524], [7]⟩,
        ⟨104768, true, false, [40558, 40524, 39668], [7]⟩,
        ⟨48721, true, false, [40558, 40524, 39668, 22326], [7]⟩,
        ⟨38, false, false, [40558, 40524, 39668, 22326, 83573], []⟩,
        ⟨48719, false, true, [40558, 40524, 39668], [83573]⟩,
        ⟨104769, true, false, [40558, 40524], [22325, 83573]⟩,
        ⟨104772, true, false, [40558, 40524], [83573]⟩,
        ⟨105556, true, false, [40558], [39673, 83573]⟩,
        ⟨105559, true, false, [40558], [83573]⟩,
        ⟨105583, true, false, [], [40533, 83573]⟩,
        ⟨105587, true, false, [], [83573]⟩
      ]⟩,
    ⟨[85677, 9], [40569, 42449, 42469, 86287], .contexts [
        ⟨105582, true, false, [40558], [9]⟩,
        ⟨105555, true, false, [40558, 40524], [9]⟩,
        ⟨104768, true, false, [40558, 40524, 39668], [9]⟩,
        ⟨48727, false, false, [40558, 40524, 39668], []⟩,
        ⟨93897, false, false, [40558, 40524, 39668], []⟩,
        ⟨104769, true, false, [40558, 40524], [22331, 87421]⟩,
        ⟨104773, true, false, [40558, 40524], [87421]⟩,
        ⟨105556, true, false, [40558], [39675, 87421]⟩,
        ⟨105560, true, false, [40558], [87421]⟩,
        ⟨105583, true, false, [], [40535, 87421]⟩,
        ⟨105588, true, false, [], [87421]⟩,
        ⟨154652, false, false, [40569], []⟩
      ]⟩,
    ⟨[85677, 11], [40571, 88207], .contexts [
        ⟨105582, true, false, [40558], [11]⟩,
        ⟨105555, true, false, [40558, 40524], [11]⟩,
        ⟨104768, true, false, [40558, 40524, 39668], [11]⟩,
        ⟨49220, true, false, [40558, 40524, 39668, 22512], [11]⟩,
        ⟨53, false, false, [40558, 40524, 39668, 22512, 88207], []⟩,
        ⟨49221, true, false, [40558, 40524, 39668], [88207]⟩,
        ⟨104769, true, false, [40558, 40524], [22515, 88207]⟩,
        ⟨104779, true, false, [40558, 40524], [88207]⟩,
        ⟨105556, true, false, [40558], [39683, 88207]⟩,
        ⟨105562, true, false, [40558], [88207]⟩,
        ⟨105583, true, false, [], [40537, 88207]⟩,
        ⟨105589, true, false, [], [88207]⟩
      ]⟩,
    ⟨[85677, 13], [40559, 85677], .contexts [
        ⟨33006, false, false, [], []⟩,
        ⟨105590, false, false, [], []⟩
      ]⟩,
    ⟨[85677, 15], [40561, 85615], .contexts [
        ⟨105582, true, false, [40558], [15]⟩,
        ⟨33010, false, false, [40558], []⟩,
        ⟨105564, false, false, [40558], []⟩,
        ⟨105583, true, false, [], [40539, 85615]⟩,
        ⟨105584, true, false, [], [85615]⟩
      ]⟩,
    ⟨[85689, 1], [40499, 83781], .contexts [
        ⟨33024, false, false, [], []⟩,
        ⟨105534, false, false, [], []⟩
      ]⟩,
    ⟨[85689, 3], [40495, 83511], .contexts [
        ⟨105527, true, false, [40490], [3]⟩,
        ⟨105498, true, false, [40490, 40450], [3]⟩,
        ⟨35929, false, false, [40490, 40450], []⟩,
        ⟨21794, false, false, [40490, 40450], []⟩,
        ⟨105499, true, false, [40490], [83511]⟩,
        ⟨105500, true, false, [40490], [83511]⟩,
        ⟨105530, true, false, [], [83511]⟩,
        ⟨105528, true, false, [], [40453, 83511]⟩,
        ⟨105529, true, false, [], [83511]⟩
      ]⟩,
    ⟨[85689, 5], [40497, 85249], .contexts [
        ⟨105527, true, false, [40490], [5]⟩,
        ⟨105498, true, false, [40490, 40450], [5]⟩,
        ⟨36011, false, false, [40490, 40450], []⟩,
        ⟨49943, false, false, [40490, 40450], []⟩,
        ⟨105500, true, false, [40490], [20639, 85249]⟩,
        ⟨105504, true, false, [40490], [85249]⟩,
        ⟨105528, true, false, [], [40457, 85249]⟩,
        ⟨105532, true, false, [], [85249]⟩
      ]⟩,
    ⟨[85689, 7], [36259, 85689], .contexts [
        ⟨99744, true, false, [36222], [7]⟩,
        ⟨579, false, false, [36222, 85691], []⟩,
        ⟨99746, false, false, [36222], []⟩,
        ⟨99745, false, false, [36222], []⟩,
        ⟨99747, false, false, [36222], []⟩,
        ⟨99545, true, false, [], [85689]⟩
      ]⟩,
    ⟨[85689, 9], [40491, 85689], .contexts [
        ⟨33026, false, false, [], []⟩,
        ⟨105531, false, false, [], []⟩
      ]⟩,
    ⟨[85689, 11], [40495, 82875], .contexts [
        ⟨105527, true, false, [40490], [11]⟩,
        ⟨33030, false, false, [40490], []⟩,
        ⟨105497, false, false, [40490], []⟩,
        ⟨105530, true, false, [], [82875]⟩,
        ⟨105528, true, false, [], [40453, 82875]⟩,
        ⟨105529, true, false, [], [82875]⟩
      ]⟩,
    ⟨[85689, 13], [36281, 85689], .contexts [
        ⟨99759, false, false, [], []⟩
      ]⟩,
    ⟨[85689, 15], [36287, 40483, 83785], .contexts [
        ⟨99742, false, false, [], []⟩,
        ⟨105522, false, false, [36287], []⟩
      ]⟩,
    ⟨[85695, 1], [40453, 82875], .contexts [
        ⟨33035, false, false, [], []⟩,
        ⟨105496, false, false, [], []⟩
      ]⟩,
    ⟨[85695, 3], [40387, 87571], .contexts [
        ⟨105444, true, false, [40388], [3]⟩,
        ⟨44212, false, false, [40388], []⟩,
        ⟨44214, false, false, [40388], []⟩,
        ⟨105447, true, false, [], [87571]⟩
      ]⟩,
    ⟨[85695, 5], [40387, 82879], .contexts [
        ⟨105444, true, false, [40388], [5]⟩,
        ⟨44190, false, false, [40388], []⟩,
        ⟨18100, false, false, [40388], []⟩,
        ⟨105447, true, false, [], [82879]⟩
      ]⟩,
    ⟨[85695, 7], [36223, 85695], .contexts [
        ⟨99665, false, false, [], []⟩,
        ⟨99693, false, false, [], []⟩
      ]⟩,
    ⟨[85695, 9], [40387, 41761, 56491, 84693], .contexts [
        ⟨105452, false, false, [], []⟩,
        ⟨152967, false, false, [40387], []⟩
      ]⟩,
    ⟨[85695, 11], [40391, 83781], .contexts [
        ⟨105444, true, false, [40388], [11]⟩,
        ⟨44199, false, false, [40388], []⟩,
        ⟨35954, false, false, [40388], []⟩,
        ⟨105445, true, false, [], [18953, 83781]⟩,
        ⟨105451, true, false, [], [83781]⟩
      ]⟩,
    ⟨[85697], [40385, 83775], .contexts [
        ⟨105441, false, false, [], []⟩
      ]⟩,
    ⟨[85695, 13], [40385, 83775], .contexts [
        ⟨33037, false, false, [], []⟩,
        ⟨161375, false, false, [], []⟩
      ]⟩,
    ⟨[85695, 15], [36287, 40395, 87033], .contexts [
        ⟨99660, false, false, [], []⟩,
        ⟨105455, false, false, [36287], []⟩
      ]⟩,
    ⟨[85699, 1], [36279, 85699], .contexts [
        ⟨33044, false, false, [], []⟩,
        ⟨99645, false, false, [], []⟩
      ]⟩,
    ⟨[85699, 3], [36281, 48687, 85409], .contexts [
        ⟨99641, true, false, [36278], [3]⟩,
        ⟨33048, false, false, [36278], []⟩,
        ⟨33093, false, false, [36278], []⟩,
        ⟨99644, true, false, [], [85703]⟩,
        ⟨99644, true, false, [], [85703]⟩,
        ⟨99643, true, false, [], [85703]⟩,
        ⟨114031, false, false, [36281], []⟩
      ]⟩,
    ⟨[85699, 5], [40383, 58471, 91679], .contexts [
        ⟨105439, false, false, [], []⟩,
        ⟨125477, false, false, [40383], []⟩
      ]⟩,
    ⟨[85699, 7], [36223, 85699], .contexts [
        ⟨99587, false, false, [], []⟩,
        ⟨99617, false, false, [], []⟩
      ]⟩,
    ⟨[85699, 9], [56053, 56475, 84697], .contexts [
        ⟨122680, false, false, [], []⟩,
        ⟨123183, false, false, [56053], []⟩
      ]⟩,
    ⟨[85699, 11], [75649, 97213], .contexts [
        ⟨147274, true, false, [75646], [11]⟩,
        ⟨53, false, false, [75646, 97213], []⟩,
        ⟨147275, true, false, [], [97213]⟩
      ]⟩,
    ⟨[85699, 13], [36283, 40369, 85861], .contexts [
        ⟨99648, false, false, [], []⟩,
        ⟨105429, false, false, [36283], []⟩
      ]⟩,
    ⟨[85699, 15], [40385, 83775], .contexts [
        ⟨33042, false, false, [], []⟩,
        ⟨161375, false, false, [], []⟩
      ]⟩,
    ⟨[85705, 1], [85707], .contexts [
        ⟨33056, false, false, [], []⟩,
        ⟨33088, false, false, [], []⟩
      ]⟩,
    ⟨[85705, 3], [21843, 86309], .contexts [
        ⟨46610, true, false, [21844], [3]⟩,
        ⟨20, false, false, [21844, 86309], []⟩,
        ⟨46608, false, true, [], [86309]⟩,
        ⟨46603, false, false, [], []⟩
      ]⟩,
    ⟨[85705, 5], [48687, 85409], .contexts [
        ⟨33054, false, false, [], []⟩,
        ⟨114031, false, false, [], []⟩
      ]⟩,
    ⟨[85705, 7], [36195, 39021, 92507], .contexts [
        ⟨99468, true, false, [36196], [7]⟩,
        ⟨38, false, false, [36196, 96743], []⟩,
        ⟨99469, true, false, [], [96743]⟩,
        ⟨104085, false, false, [36195], []⟩
      ]⟩,
    ⟨[85705, 9], [44909, 94903], .contexts [
        ⟨109906, false, false, [], []⟩
      ]⟩,
    ⟨[85705, 11], [72965, 96887], .contexts [
        ⟨142901, true, false, [72962], [11]⟩,
        ⟨53, false, false, [72962, 96887], []⟩,
        ⟨142873, true, false, [], [96887]⟩
      ]⟩,
    ⟨[85705, 13], [36255, 40951, 83679], .contexts [
        ⟨99538, false, false, [], []⟩,
        ⟨105916, false, false, [36255], []⟩
      ]⟩,
    ⟨[85705, 15], [45991, 85313], .contexts [
        ⟨111277, true, false, [45988], [15]⟩,
        ⟨1, false, false, [45988, 85313], []⟩,
        ⟨111278, true, false, [], [85313]⟩
      ]⟩,
    ⟨[85707, 1], [85705], .contexts [
        ⟨33058, false, false, [], []⟩,
        ⟨33091, false, false, [], []⟩
      ]⟩,
    ⟨[85707, 3], [21835, 86317], .contexts [
        ⟨46597, false, false, [], []⟩,
        ⟨46598, false, false, [], []⟩
      ]⟩,
    ⟨[85707, 5], [46047, 95417], .contexts [
        ⟨111340, false, false, [], []⟩
      ]⟩,
    ⟨[85707, 7], [36159, 39033, 92509], .contexts [
        ⟨99419, false, false, [], []⟩,
        ⟨104092, false, false, [36159], []⟩
      ]⟩,
    ⟨[85707, 9], [85709], .contexts [
        ⟨33060, false, false, [], []⟩,
        ⟨33087, false, false, [], []⟩
      ]⟩,
    ⟨[85707, 11], [72965, 96885], .contexts [
        ⟨142872, true, false, [72962], [11]⟩,
        ⟨53, false, false, [72962, 96885], []⟩,
        ⟨142873, true, false, [], [96885]⟩
      ]⟩,
    ⟨[85707, 13], [27425, 39163, 85361], .contexts [
        ⟨81474, true, false, [27422], [13]⟩,
        ⟨59, false, false, [27422, 93811], []⟩,
        ⟨70388, true, false, [], [93811]⟩,
        ⟨104216, false, false, [27425], []⟩
      ]⟩,
    ⟨[85707, 15], [46007, 48729, 85417], .contexts [
        ⟨111291, true, false, [46004], [15]⟩,
        ⟨1, false, false, [46004, 88463], []⟩,
        ⟨111292, true, false, [], [88463]⟩,
        ⟨114072, false, false, [46007], []⟩
      ]⟩,
    ⟨[85709, 1], [29569, 38493, 90371], .contexts [
        ⟨77484, false, false, [], []⟩,
        ⟨103464, false, false, [29569], []⟩
      ]⟩,
    ⟨[85709, 3], [21835, 86319], .contexts [
        ⟨46591, false, false, [], []⟩,
        ⟨46585, false, false, [], []⟩
      ]⟩,
    ⟨[85709, 5], [27469, 91829], .contexts [
        ⟨70550, false, false, [], []⟩,
        ⟨70558, false, false, [], []⟩
      ]⟩,
    ⟨[85709, 7], [21839, 86609], .contexts [
        ⟨46580, false, false, [], []⟩,
        ⟨77512, false, false, [], []⟩
      ]⟩,
    ⟨[85709, 9], [85707], .contexts [
        ⟨33062, false, false, [], []⟩,
        ⟨33088, false, false, [], []⟩
      ]⟩,
    ⟨[85709, 11], [43229, 83807], .contexts [
        ⟨33064, false, false, [], []⟩,
        ⟨108005, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2522. -/
def y322TCIndexRaw2522 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85709, 13], [27425, 42773, 89323], .contexts [
        ⟨70391, false, false, [], []⟩,
        ⟨107595, false, false, [27425], []⟩
      ]⟩,
    ⟨[85709, 15], [28135, 43517, 88461], .contexts [
        ⟨72865, false, false, [], []⟩,
        ⟨108333, false, false, [28135], []⟩
      ]⟩,
    ⟨[85715, 1], [18375, 85719], .contexts [
        ⟨33209, false, false, [], []⟩
      ]⟩,
    ⟨[85715, 3], [35081, 37487, 96075], .contexts [
        ⟨96110, false, false, [], []⟩,
        ⟨102270, false, false, [35081], []⟩
      ]⟩,
    ⟨[85715, 5], [51607, 53735, 88393], .contexts [
        ⟨117407, false, false, [], []⟩,
        ⟨119874, false, false, [51607], []⟩
      ]⟩,
    ⟨[85715, 7], [21821, 87807], .contexts [
        ⟨46536, true, false, [21818], [7]⟩,
        ⟨38, false, false, [21818, 87807], []⟩,
        ⟨46537, true, false, [], [87807]⟩
      ]⟩,
    ⟨[85715, 9], [35149, 35173, 86899], .contexts [
        ⟨96218, false, false, [], []⟩,
        ⟨96252, false, false, [35149], []⟩
      ]⟩,
    ⟨[85715, 11], [29563, 39975, 47097, 86535], .contexts [
        ⟨77476, false, false, [], []⟩,
        ⟨105058, false, false, [29563], []⟩,
        ⟨138270, false, false, [29563], []⟩
      ]⟩,
    ⟨[85715, 13], [38479, 83809], .contexts [
        ⟨33073, false, false, [], []⟩,
        ⟨103452, false, false, [], []⟩
      ]⟩,
    ⟨[85717], [18377, 85715], .contexts [
        ⟨46531, false, false, [], []⟩
      ]⟩,
    ⟨[85715, 15], [18377, 85715], .contexts [
        ⟨33075, false, false, [], []⟩,
        ⟨161417, false, false, [], []⟩
      ]⟩,
    ⟨[85719, 1], [18377, 85715], .contexts [
        ⟨33081, false, false, [], []⟩,
        ⟨161417, false, false, [], []⟩
      ]⟩,
    ⟨[85719, 3], [18363, 83203], .contexts [
        ⟨33186, false, false, [], []⟩,
        ⟨33183, false, false, [], []⟩
      ]⟩,
    ⟨[85719, 5], [32489, 47039, 53697, 88395], .contexts [
        ⟨88332, true, false, [32486], [5]⟩,
        ⟨28, false, false, [32486, 95133], []⟩,
        ⟨88333, true, false, [], [95133]⟩,
        ⟨156730, false, false, [32489], []⟩
      ]⟩,
    ⟨[85719, 7], [18363, 87805], .contexts [
        ⟨46498, true, false, [18364], [7]⟩,
        ⟨38, false, false, [18364, 87805], []⟩,
        ⟨46499, true, false, [], [87805]⟩
      ]⟩,
    ⟨[85719, 9], [18371, 85719], .contexts [
        ⟨33196, false, false, [], []⟩
      ]⟩,
    ⟨[85719, 11], [22023, 87943], .contexts [
        ⟨47433, true, false, [22020], [11]⟩,
        ⟨53, false, false, [22020, 87943], []⟩,
        ⟨47434, true, false, [], [87943]⟩
      ]⟩,
    ⟨[85719, 13], [18363, 42787, 89723], .contexts [
        ⟨82043, true, false, [18364], [13]⟩,
        ⟨59, false, false, [18364, 93925], []⟩,
        ⟨46499, true, false, [], [93925]⟩,
        ⟨107607, false, false, [18363], []⟩
      ]⟩,
    ⟨[85719, 15], [18377, 85719], .contexts [
        ⟨33203, false, false, [], []⟩,
        ⟨33204, false, false, [], []⟩
      ]⟩,
    ⟨[85723, 1], [39809, 84457], .contexts [
        ⟨33240, false, false, [], []⟩,
        ⟨104907, false, false, [], []⟩
      ]⟩,
    ⟨[85723, 3], [85113], .contexts [
        ⟨33232, false, false, [], []⟩,
        ⟨30259, false, false, [], []⟩
      ]⟩,
    ⟨[85723, 5], [7355, 83381], .contexts [
        ⟨33237, false, false, [], []⟩,
        ⟨33234, false, false, [], []⟩
      ]⟩,
    ⟨[85723, 7], [19523, 43873, 84447], .contexts [
        ⟨39139, false, false, [], []⟩,
        ⟨108674, false, false, [19523], []⟩
      ]⟩,
    ⟨[85723, 9], [22251, 88089], .contexts [
        ⟨48272, false, false, [], []⟩,
        ⟨48284, false, false, [], []⟩
      ]⟩,
    ⟨[85723, 11], [39863, 84461], .contexts [
        ⟨33227, false, false, [], []⟩,
        ⟨160009, false, false, [], []⟩
      ]⟩,
    ⟨[85723, 13], [7355, 50127, 92555], .contexts [
        ⟨99870, true, false, [7356], [13]⟩,
        ⟨59, false, false, [7356, 96755], []⟩,
        ⟨10990, true, false, [], [96755]⟩,
        ⟨115666, false, false, [7355], []⟩
      ]⟩,
    ⟨[85723, 15], [21105, 88215], .contexts [
        ⟨49293, false, false, [], []⟩
      ]⟩,
    ⟨[85729, 1], [85731], .contexts [
        ⟨33296, false, false, [], []⟩,
        ⟨33298, false, false, [], []⟩
      ]⟩,
    ⟨[85729, 3], [1063, 85729], .contexts [
        ⟨33289, false, false, [], []⟩,
        ⟨33284, false, false, [], []⟩
      ]⟩,
    ⟨[85729, 5], [7355, 83387], .contexts [
        ⟨33294, false, false, [], []⟩,
        ⟨33290, false, false, [], []⟩
      ]⟩,
    ⟨[85729, 7], [19523, 24299, 85279], .contexts [
        ⟨39180, false, false, [], []⟩,
        ⟨57231, false, false, [19523], []⟩
      ]⟩,
    ⟨[85729, 9], [22271, 63451, 86067], .contexts [
        ⟨48360, false, false, [], []⟩,
        ⟨131443, false, false, [22271], []⟩
      ]⟩,
    ⟨[85729, 11], [38861, 71607, 95795], .contexts [
        ⟨103891, false, false, [], []⟩,
        ⟨140480, false, false, [38861], []⟩
      ]⟩,
    ⟨[85729, 13], [21105, 38845, 83301], .contexts [
        ⟨49354, false, false, [], []⟩,
        ⟨103877, false, false, [21105], []⟩
      ]⟩,
    ⟨[85729, 15], [39355, 83819], .contexts [
        ⟨33280, false, false, [], []⟩,
        ⟨104423, false, false, [], []⟩
      ]⟩,
    ⟨[85731, 1], [85729], .contexts [
        ⟨33297, false, false, [], []⟩,
        ⟨33281, false, false, [], []⟩
      ]⟩,
    ⟨[85731, 3], [85733], .contexts [
        ⟨33307, false, false, [], []⟩,
        ⟨33309, false, false, [], []⟩
      ]⟩,
    ⟨[85731, 5], [7355, 83389], .contexts [
        ⟨33304, false, false, [], []⟩,
        ⟨33302, false, false, [], []⟩
      ]⟩,
    ⟨[86815], [24299, 59679, 85169], .contexts [
        ⟨90110, false, false, [], []⟩,
        ⟨127504, false, false, [], []⟩
      ]⟩,
    ⟨[85731, 7], [19523, 24299, 59679, 85169], .contexts [
        ⟨39190, false, false, [], []⟩,
        ⟨161446, false, false, [19523], []⟩
      ]⟩,
    ⟨[85731, 9], [45831, 84267], .contexts [
        ⟨111064, false, false, [], []⟩,
        ⟨111061, false, false, [], []⟩
      ]⟩,
    ⟨[85731, 11], [38861, 71607, 95793], .contexts [
        ⟨111067, false, false, [], []⟩,
        ⟨140497, false, false, [38861], []⟩
      ]⟩,
    ⟨[85731, 13], [33069, 62809, 84653], .contexts [
        ⟨90130, false, false, [], []⟩,
        ⟨130670, false, false, [33069], []⟩
      ]⟩,
    ⟨[85731, 15], [23105, 39363, 83821], .contexts [
        ⟨51803, false, false, [], []⟩,
        ⟨104439, false, false, [23105], []⟩
      ]⟩,
    ⟨[85733, 1], [1063, 85733], .contexts [
        ⟨33321, false, false, [], []⟩,
        ⟨33316, false, false, [], []⟩
      ]⟩,
    ⟨[85733, 3], [85731], .contexts [
        ⟨33308, false, false, [], []⟩,
        ⟨33298, false, false, [], []⟩
      ]⟩,
    ⟨[85733, 5], [85735], .contexts [
        ⟨33323, false, false, [], []⟩,
        ⟨33325, false, false, [], []⟩
      ]⟩,
    ⟨[85733, 7], [19523, 86817], .contexts [
        ⟨39209, false, false, [], []⟩,
        ⟨145382, false, false, [], []⟩
      ]⟩,
    ⟨[85733, 9], [60165, 63727, 85769], .contexts [
        ⟨127455, false, false, [], []⟩,
        ⟨131810, false, false, [60165], []⟩
      ]⟩,
    ⟨[85733, 11], [97023], .contexts [
        ⟨145372, false, false, [], []⟩,
        ⟨145374, false, false, [], []⟩
      ]⟩,
    ⟨[85733, 13], [52063, 91635], .contexts [
        ⟨117969, false, false, [], []⟩,
        ⟨145395, false, false, [], []⟩
      ]⟩,
    ⟨[85733, 15], [23153, 85809], .contexts [
        ⟨51816, false, false, [], []⟩,
        ⟨145400, false, false, [], []⟩
      ]⟩,
    ⟨[85735, 1], [1063, 85735], .contexts [
        ⟨33333, false, false, [], []⟩,
        ⟨33329, false, false, [], []⟩
      ]⟩,
    ⟨[85735, 3], [7355, 83393], .contexts [
        ⟨33339, false, false, [], []⟩,
        ⟨33335, false, false, [], []⟩
      ]⟩,
    ⟨[85735, 5], [85733], .contexts [
        ⟨33324, false, false, [], []⟩,
        ⟨33309, false, false, [], []⟩
      ]⟩,
    ⟨[85735, 7], [38061, 38283, 96259], .contexts [
        ⟨102963, false, false, [], []⟩,
        ⟨109679, false, false, [38061], []⟩
      ]⟩,
    ⟨[85735, 9], [85737], .contexts [
        ⟨33366, false, false, [], []⟩,
        ⟨33641, false, false, [], []⟩
      ]⟩,
    ⟨[85735, 11], [97233], .contexts [
        ⟨147657, false, false, [], []⟩,
        ⟨147658, false, false, [], []⟩
      ]⟩,
    ⟨[85735, 13], [51925, 86139], .contexts [
        ⟨117817, false, false, [], []⟩,
        ⟨147676, false, false, [], []⟩
      ]⟩,
    ⟨[85735, 15], [68785, 87843], .contexts [
        ⟨137381, false, false, [], []⟩,
        ⟨147682, false, false, [], []⟩
      ]⟩,
    ⟨[85737, 1], [57257, 86647], .contexts [
        ⟨124101, true, false, [57254], [1]⟩,
        ⟨38298, false, false, [57254], []⟩,
        ⟨38417, false, false, [57254], []⟩,
        ⟨124103, true, false, [], [86647]⟩
      ]⟩,
    ⟨[85737, 3], [57257, 63711, 85765], .contexts [
        ⟨124104, false, false, [], []⟩,
        ⟨131793, false, false, [57257], []⟩
      ]⟩,
    ⟨[85737, 5], [60265, 63727, 85769], .contexts [
        ⟨127559, false, false, [], []⟩,
        ⟨131810, false, false, [60265], []⟩
      ]⟩,
    ⟨[85737, 7], [60329, 85445], .contexts [
        ⟨127630, true, false, [60326], [7]⟩,
        ⟨38, false, false, [60326, 85445], []⟩,
        ⟨127631, true, false, [], [85445]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2523. -/
def y322TCIndexRaw2523 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85737, 9], [85735], .contexts [
        ⟨33367, false, false, [], []⟩,
        ⟨33325, false, false, [], []⟩
      ]⟩,
    ⟨[85737, 11], [85739], .contexts [
        ⟨33369, false, false, [], []⟩,
        ⟨33640, false, false, [], []⟩
      ]⟩,
    ⟨[85737, 13], [58907, 86141], .contexts [
        ⟨125972, false, false, [], []⟩
      ]⟩,
    ⟨[85737, 15], [58911, 59539, 83873], .contexts [
        ⟨125978, false, false, [], []⟩,
        ⟨126751, false, false, [58911], []⟩
      ]⟩,
    ⟨[85739, 1], [85741], .contexts [
        ⟨33373, false, false, [], []⟩,
        ⟨33639, false, false, [], []⟩
      ]⟩,
    ⟨[85739, 3], [57263, 89389], .contexts [
        ⟨124109, true, false, [57260], [3]⟩,
        ⟨63044, false, false, [57260], []⟩,
        ⟨116582, false, false, [57260], []⟩,
        ⟨124112, true, false, [], [50841, 89389]⟩,
        ⟨124113, true, false, [], [89389]⟩
      ]⟩,
    ⟨[85739, 5], [57269, 63781, 85777], .contexts [
        ⟨124109, true, false, [57260], [5]⟩,
        ⟨101074, true, false, [57260, 36882], [5]⟩,
        ⟨28, false, false, [57260, 36882, 85905], []⟩,
        ⟨101075, true, false, [57260], [85905]⟩,
        ⟨124110, true, false, [], [36885, 85905]⟩,
        ⟨124116, true, false, [], [85905]⟩,
        ⟨131861, false, false, [57269], []⟩
      ]⟩,
    ⟨[85739, 7], [61919, 84563], .contexts [
        ⟨129564, false, false, [], []⟩
      ]⟩,
    ⟨[85739, 9], [57277, 90239], .contexts [
        ⟨124122, false, false, [], []⟩,
        ⟨147670, false, false, [], []⟩
      ]⟩,
    ⟨[85739, 11], [85737], .contexts [
        ⟨33371, false, false, [], []⟩,
        ⟨33641, false, false, [], []⟩
      ]⟩,
    ⟨[85739, 13], [57273, 86143], .contexts [
        ⟨124119, false, false, [], []⟩
      ]⟩,
    ⟨[85739, 15], [57267, 57977, 83871], .contexts [
        ⟨124109, true, false, [57260], [15]⟩,
        ⟨76420, false, false, [57260], []⟩,
        ⟨118630, false, false, [57260, 29315], []⟩,
        ⟨124110, true, false, [], [29315, 52541, 84419]⟩,
        ⟨124114, true, false, [], [52541, 84419]⟩,
        ⟨124115, true, false, [], [84419]⟩,
        ⟨145084, false, false, [57267], []⟩
      ]⟩,
    ⟨[85741, 1], [85739], .contexts [
        ⟨33375, false, false, [], []⟩,
        ⟨33640, false, false, [], []⟩
      ]⟩,
    ⟨[85741, 3], [57291, 59153, 87273], .contexts [
        ⟨124136, false, false, [], []⟩,
        ⟨126296, false, false, [57291], []⟩
      ]⟩,
    ⟨[85741, 5], [57285, 63759, 85775], .contexts [
        ⟨124126, true, false, [57260], [5]⟩,
        ⟨100996, false, false, [57260], []⟩,
        ⟨119267, false, false, [57260, 36851], []⟩,
        ⟨124110, true, false, [], [36851, 53131, 86829]⟩,
        ⟨124131, true, false, [], [53131, 86829]⟩,
        ⟨124132, true, false, [], [86829]⟩,
        ⟨131841, false, false, [57285], []⟩
      ]⟩,
    ⟨[85741, 7], [60133, 61931, 84561], .contexts [
        ⟨127430, false, false, [], []⟩,
        ⟨129596, false, false, [60133], []⟩
      ]⟩,
    ⟨[85741, 9], [57289, 90247], .contexts [
        ⟨124126, true, false, [57260], [9]⟩,
        ⟨101503, true, false, [57260, 37090], [9]⟩,
        ⟨46, false, false, [57260, 37090, 91517], []⟩,
        ⟨101501, false, true, [57260], [91517]⟩,
        ⟨109135, false, false, [57260, 37089], []⟩,
        ⟨124110, true, false, [], [37089, 44295, 90247]⟩,
        ⟨124133, true, false, [], [44295, 90247]⟩,
        ⟨124134, true, false, [], [90247]⟩
      ]⟩,
    ⟨[85741, 11], [57281, 86647], .contexts [
        ⟨124130, false, false, [], []⟩
      ]⟩,
    ⟨[85741, 13], [85743], .contexts [
        ⟨33377, false, false, [], []⟩,
        ⟨33638, false, false, [], []⟩
      ]⟩,
    ⟨[85741, 15], [57279, 84417], .contexts [
        ⟨124126, true, false, [57260], [15]⟩,
        ⟨63039, false, false, [57260], []⟩,
        ⟨124127, false, false, [57260], []⟩,
        ⟨124112, true, false, [], [52531, 84417]⟩,
        ⟨124128, true, false, [], [84417]⟩
      ]⟩,
    ⟨[85743, 1], [57299, 86147], .contexts [
        ⟨124148, false, false, [], []⟩
      ]⟩,
    ⟨[85743, 3], [68275, 86161], .contexts [
        ⟨136911, false, false, [], []⟩
      ]⟩,
    ⟨[85743, 5], [57297, 87241], .contexts [
        ⟨124141, true, false, [57294], [5]⟩,
        ⟨49541, false, false, [57294], []⟩,
        ⟨124142, false, false, [57294], []⟩,
        ⟨124144, true, false, [], [44623, 87241]⟩,
        ⟨124145, true, false, [], [87241]⟩
      ]⟩,
    ⟨[85743, 7], [57301, 83447], .contexts [
        ⟨124141, true, false, [57294], [7]⟩,
        ⟨49932, true, false, [57294, 22660], [7]⟩,
        ⟨38, false, false, [57294, 22660, 83447], []⟩,
        ⟨49902, true, false, [57294], [83447]⟩,
        ⟨49930, false, false, [57294], []⟩,
        ⟨124143, true, false, [], [22659, 83447]⟩,
        ⟨124149, true, false, [], [83447]⟩
      ]⟩,
    ⟨[85743, 9], [57303, 90249], .contexts [
        ⟨124141, true, false, [57294], [9]⟩,
        ⟨118190, false, false, [57294], []⟩,
        ⟨124143, true, false, [], [52239, 90249]⟩,
        ⟨124150, true, false, [], [90249]⟩
      ]⟩,
    ⟨[85743, 11], [65671, 89025], .contexts [
        ⟨133938, false, false, [], []⟩
      ]⟩,
    ⟨[85743, 13], [85741], .contexts [
        ⟨33379, false, false, [], []⟩,
        ⟨33639, false, false, [], []⟩
      ]⟩,
    ⟨[85745], [61945, 84559], .contexts [
        ⟨129612, false, false, [], []⟩
      ]⟩,
    ⟨[85743, 15], [61945, 84559], .contexts [
        ⟨33381, false, false, [], []⟩,
        ⟨161499, false, false, [], []⟩
      ]⟩,
    ⟨[85747, 1], [61945, 84559], .contexts [
        ⟨33387, false, false, [], []⟩,
        ⟨161499, false, false, [], []⟩
      ]⟩,
    ⟨[85749], [59241, 85455], .contexts [
        ⟨127313, false, false, [], []⟩
      ]⟩,
    ⟨[85747, 3], [59241, 85455], .contexts [
        ⟨33389, false, false, [], []⟩,
        ⟨161502, false, false, [], []⟩
      ]⟩,
    ⟨[85747, 5], [61899, 84563], .contexts [
        ⟨129547, false, false, [], []⟩,
        ⟨129542, false, false, [], []⟩
      ]⟩,
    ⟨[85747, 7], [59239, 86823], .contexts [
        ⟨126417, false, false, [], []⟩,
        ⟨129556, false, false, [], []⟩
      ]⟩,
    ⟨[85747, 9], [59235, 93897], .contexts [
        ⟨126413, false, false, [], []⟩,
        ⟨129536, false, false, [], []⟩
      ]⟩,
    ⟨[85747, 11], [59235, 93901], .contexts [
        ⟨126414, false, false, [], []⟩,
        ⟨127317, false, false, [], []⟩
      ]⟩,
    ⟨[85747, 13], [59237, 85137], .contexts [
        ⟨126410, true, false, [59232], [13]⟩,
        ⟨121545, true, false, [59232, 55132], [13]⟩,
        ⟨118915, false, false, [59232, 55132], []⟩,
        ⟨121546, true, false, [59232], [52841, 85137]⟩,
        ⟨121549, true, false, [59232], [85137]⟩,
        ⟨126405, true, false, [], [55135, 85137]⟩,
        ⟨126415, true, false, [], [85137]⟩
      ]⟩,
    ⟨[85747, 15], [59231, 86147], .contexts [
        ⟨126410, true, false, [59232], [15]⟩,
        ⟨35561, false, false, [59232], []⟩,
        ⟨35759, false, false, [59232], []⟩,
        ⟨126408, true, false, [], [86147]⟩
      ]⟩,
    ⟨[85751, 1], [61137, 83031], .contexts [
        ⟨33396, false, false, [], []⟩,
        ⟨128592, false, false, [], []⟩
      ]⟩,
    ⟨[85751, 3], [65501, 83435], .contexts [
        ⟨133744, false, false, [], []⟩
      ]⟩,
    ⟨[85751, 5], [59241, 85455], .contexts [
        ⟨33394, false, false, [], []⟩,
        ⟨161502, false, false, [], []⟩
      ]⟩,
    ⟨[85751, 7], [64071, 85799], .contexts [
        ⟨132182, false, false, [], []⟩
      ]⟩,
    ⟨[85751, 9], [61159, 94267], .contexts [
        ⟨128622, false, false, [], []⟩
      ]⟩,
    ⟨[85751, 11], [60839, 61079, 84769], .contexts [
        ⟨128219, false, false, [], []⟩,
        ⟨128554, false, false, [60839], []⟩
      ]⟩,
    ⟨[85751, 13], [59921, 84403], .contexts [
        ⟨127178, true, false, [59918], [13]⟩,
        ⟨59, false, false, [59918, 84403], []⟩,
        ⟨127179, true, false, [], [84403]⟩
      ]⟩,
    ⟨[85751, 15], [61001, 83035], .contexts [
        ⟨128403, false, false, [], []⟩
      ]⟩,
    ⟨[85763, 1], [85765], .contexts [
        ⟨33415, false, false, [], []⟩,
        ⟨33625, false, false, [], []⟩
      ]⟩,
    ⟨[85763, 3], [63699, 84755], .contexts [
        ⟨131769, true, false, [63696], [3]⟩,
        ⟨52033, false, false, [63696], []⟩,
        ⟨125367, false, false, [63696], []⟩,
        ⟨131771, true, false, [], [58375, 84755]⟩,
        ⟨131772, true, false, [], [84755]⟩
      ]⟩,
    ⟨[85763, 5], [63701, 86655], .contexts [
        ⟨131774, false, false, [], []⟩,
        ⟨134947, false, false, [], []⟩
      ]⟩,
    ⟨[85763, 7], [63707, 83037], .contexts [
        ⟨131778, false, false, [], []⟩
      ]⟩,
    ⟨[85763, 9], [63705, 87389], .contexts [
        ⟨131769, true, false, [63696], [9]⟩,
        ⟨127188, true, false, [63696, 59926], [9]⟩,
        ⟨46, false, false, [63696, 59926, 87389], []⟩,
        ⟨127189, true, false, [63696], [87389]⟩,
        ⟨131770, true, false, [], [59929, 87389]⟩,
        ⟨131776, true, false, [], [87389]⟩
      ]⟩,
    ⟨[85763, 11], [63703, 89391], .contexts [
        ⟨131769, true, false, [63696], [11]⟩,
        ⟨125297, true, false, [63696, 58326], [11]⟩,
        ⟨53, false, false, [63696, 58326, 89391], []⟩,
        ⟨125298, true, false, [63696], [89391]⟩,
        ⟨131770, true, false, [], [58329, 89391]⟩,
        ⟨131775, true, false, [], [89391]⟩
      ]⟩,
    ⟨[85763, 13], [65527, 95579], .contexts [
        ⟨133773, false, false, [], []⟩
      ]⟩,
    ⟨[85763, 15], [61149, 84405], .contexts [
        ⟨33413, false, false, [], []⟩,
        ⟨133788, false, false, [], []⟩
      ]⟩,
    ⟨[85765, 1], [85763], .contexts [
        ⟨33417, false, false, [], []⟩,
        ⟨33627, false, false, [], []⟩
      ]⟩,
    ⟨[85767], [63723, 85737], .contexts [
        ⟨131796, false, false, [], []⟩
      ]⟩,
    ⟨[85765, 3], [63723, 85737], .contexts [
        ⟨33419, false, false, [], []⟩,
        ⟨161527, false, false, [], []⟩
      ]⟩,
    ⟨[85765, 5], [63709, 86653], .contexts [
        ⟨131786, false, false, [], []⟩
      ]⟩,
    ⟨[85765, 7], [65757, 83729], .contexts [
        ⟨134035, false, false, [], []⟩
      ]⟩,
    ⟨[85765, 9], [63719, 83393], .contexts [
        ⟨131783, true, false, [63710], [9]⟩,
        ⟨115094, true, false, [63710, 49634], [9]⟩,
        ⟨46, false, false, [63710, 49634, 83393], []⟩,
        ⟨115095, true, false, [63710], [83393]⟩,
        ⟨131784, true, false, [], [49637, 83393]⟩,
        ⟨131790, true, false, [], [83393]⟩
      ]⟩,
    ⟨[85765, 11], [63715, 89389], .contexts [
        ⟨131783, true, false, [63710], [11]⟩,
        ⟨68617, false, false, [63710], []⟩,
        ⟨116582, false, false, [63710, 26899], []⟩,
        ⟨131784, true, false, [], [26899, 50841, 89389]⟩,
        ⟨131787, true, false, [], [50841, 89389]⟩,
        ⟨131788, true, false, [], [89389]⟩
      ]⟩,
    ⟨[85765, 13], [63721, 83703], .contexts [
        ⟨131792, false, false, [], []⟩
      ]⟩,
    ⟨[85765, 15], [63717, 84407], .contexts [
        ⟨131783, true, false, [63710], [15]⟩,
        ⟨95777, true, false, [63710, 35018], [15]⟩,
        ⟨1, false, false, [63710, 35018, 84407], []⟩,
        ⟨95778, true, false, [63710], [84407]⟩,
        ⟨131784, true, false, [], [35021, 84407]⟩,
        ⟨131789, true, false, [], [84407]⟩
      ]⟩,
    ⟨[85769, 1], [85771], .contexts [
        ⟨33426, false, false, [], []⟩,
        ⟨33623, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2524. -/
def y322TCIndexRaw2524 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85769, 3], [63729, 84267], .contexts [
        ⟨131799, true, false, [63726], [3]⟩,
        ⟨80785, false, false, [63726], []⟩,
        ⟨127463, false, false, [63726], []⟩,
        ⟨131802, true, false, [], [60175, 84267]⟩,
        ⟨131803, true, false, [], [84267]⟩
      ]⟩,
    ⟨[85769, 5], [63723, 85737], .contexts [
        ⟨33424, false, false, [], []⟩,
        ⟨161527, false, false, [], []⟩
      ]⟩,
    ⟨[85769, 7], [63731, 86641], .contexts [
        ⟨131799, true, false, [63726], [7]⟩,
        ⟨127111, true, false, [63726, 59850], [7]⟩,
        ⟨38, false, false, [63726, 59850, 86641], []⟩,
        ⟨127112, true, false, [63726], [86641]⟩,
        ⟨131800, true, false, [], [59853, 86641]⟩,
        ⟨131804, true, false, [], [86641]⟩
      ]⟩,
    ⟨[85769, 9], [63735, 85733], .contexts [
        ⟨131799, true, false, [63726], [9]⟩,
        ⟨127455, true, false, [63726, 60164], [9]⟩,
        ⟨46, false, false, [63726, 60164, 85733], []⟩,
        ⟨127456, true, false, [63726], [85733]⟩,
        ⟨131800, true, false, [], [60167, 85733]⟩,
        ⟨131807, true, false, [], [85733]⟩
      ]⟩,
    ⟨[85769, 11], [63733, 63781, 85777], .contexts [
        ⟨131806, false, false, [], []⟩,
        ⟨131861, false, false, [63733], []⟩
      ]⟩,
    ⟨[85769, 13], [63739, 91581], .contexts [
        ⟨131799, true, false, [63726], [13]⟩,
        ⟨127553, true, false, [63726, 60256], [13]⟩,
        ⟨59, false, false, [63726, 60256, 91581], []⟩,
        ⟨127554, true, false, [63726], [91581]⟩,
        ⟨131800, true, false, [], [60259, 91581]⟩,
        ⟨131809, true, false, [], [91581]⟩
      ]⟩,
    ⟨[85769, 15], [63737, 85807], .contexts [
        ⟨131799, true, false, [63726], [15]⟩,
        ⟨127502, true, false, [63726, 60206], [15]⟩,
        ⟨1, false, false, [63726, 60206, 85807], []⟩,
        ⟨127503, true, false, [63726], [85807]⟩,
        ⟨131800, true, false, [], [60209, 85807]⟩,
        ⟨131808, true, false, [], [85807]⟩
      ]⟩,
    ⟨[85771, 1], [85769], .contexts [
        ⟨33428, false, false, [], []⟩,
        ⟨33624, false, false, [], []⟩
      ]⟩,
    ⟨[85771, 3], [63751, 83029], .contexts [
        ⟨131813, true, false, [63726], [3]⟩,
        ⟨127547, false, false, [63726], []⟩,
        ⟨131800, true, false, [], [60253, 83029]⟩,
        ⟨131823, true, false, [], [83029]⟩
      ]⟩,
    ⟨[85771, 5], [63749, 86647], .contexts [
        ⟨131822, false, false, [], []⟩
      ]⟩,
    ⟨[85771, 7], [63747, 83877], .contexts [
        ⟨131813, true, false, [63726], [7]⟩,
        ⟨127102, false, false, [63726], []⟩,
        ⟨131800, true, false, [], [59845, 83877]⟩,
        ⟨131818, true, false, [], [83877]⟩
      ]⟩,
    ⟨[85773], [63755, 85771], .contexts [
        ⟨131826, false, false, [], []⟩
      ]⟩,
    ⟨[85771, 9], [63755, 85771], .contexts [
        ⟨33430, false, false, [], []⟩,
        ⟨161547, false, false, [], []⟩
      ]⟩,
    ⟨[85771, 11], [63745, 63759, 85775], .contexts [
        ⟨131817, false, false, [], []⟩,
        ⟨131841, false, false, [63745], []⟩
      ]⟩,
    ⟨[85771, 13], [63743, 85045], .contexts [
        ⟨131813, true, false, [63726], [13]⟩,
        ⟨126205, false, false, [63726], []⟩,
        ⟨127372, false, false, [63726], []⟩,
        ⟨131800, true, false, [], [59085, 85045]⟩,
        ⟨131815, true, false, [], [85045]⟩
      ]⟩,
    ⟨[85771, 15], [63741, 85805], .contexts [
        ⟨131813, true, false, [63726], [15]⟩,
        ⟨80779, false, false, [63726], []⟩,
        ⟨126180, false, false, [63726], []⟩,
        ⟨131802, true, false, [], [59055, 85805]⟩,
        ⟨131814, true, false, [], [85805]⟩
      ]⟩,
    ⟨[85775, 1], [85777], .contexts [
        ⟨33437, false, false, [], []⟩,
        ⟨33620, false, false, [], []⟩
      ]⟩,
    ⟨[85775, 3], [63765, 64787, 86027], .contexts [
        ⟨131829, true, false, [63758], [3]⟩,
        ⟨119256, false, false, [63758], []⟩,
        ⟨128322, false, false, [63758, 53129], []⟩,
        ⟨131830, true, false, [], [53129, 60913, 90281]⟩,
        ⟨131832, true, false, [], [60913, 90281]⟩,
        ⟨131833, true, false, [], [90281]⟩,
        ⟨132987, false, false, [63765], []⟩
      ]⟩,
    ⟨[85775, 5], [63773, 85741], .contexts [
        ⟨131829, true, false, [63758], [5]⟩,
        ⟨119259, false, false, [63758], []⟩,
        ⟨124138, false, false, [63758, 53135], []⟩,
        ⟨131830, true, false, [], [53135, 57261, 85741]⟩,
        ⟨131836, true, false, [], [57261, 85741]⟩,
        ⟨131837, true, false, [], [85741]⟩
      ]⟩,
    ⟨[85775, 7], [63769, 84649], .contexts [
        ⟨131829, true, false, [63758], [7]⟩,
        ⟨119253, true, false, [63758, 53130], [7]⟩,
        ⟨100317, true, false, [63758, 53130, 36510], [7]⟩,
        ⟨38, false, false, [63758, 53130, 36510, 90833], []⟩,
        ⟨100318, true, false, [63758, 53130], [90833]⟩,
        ⟨119254, true, false, [63758], [36513, 90833]⟩,
        ⟨119257, true, false, [63758], [90833]⟩,
        ⟨130689, false, false, [63758, 53133], []⟩,
        ⟨131830, true, false, [], [53133, 62825, 84649]⟩,
        ⟨131834, true, false, [], [62825, 84649]⟩,
        ⟨131835, true, false, [], [84649]⟩
      ]⟩,
    ⟨[85775, 9], [63777, 91651], .contexts [
        ⟨131840, false, false, [], []⟩
      ]⟩,
    ⟨[85775, 11], [63755, 85771], .contexts [
        ⟨33435, false, false, [], []⟩,
        ⟨161547, false, false, [], []⟩
      ]⟩,
    ⟨[85775, 13], [63775, 87241], .contexts [
        ⟨131829, true, false, [63758], [13]⟩,
        ⟨119253, true, false, [63758, 53130], [13]⟩,
        ⟨101082, false, false, [63758, 53130], []⟩,
        ⟨119261, false, false, [63758, 53130, 36889], []⟩,
        ⟨119254, true, false, [63758], [36889, 44623, 87241]⟩,
        ⟨119262, true, false, [63758], [44623, 87241]⟩,
        ⟨119263, true, false, [63758], [87241]⟩,
        ⟨131830, true, false, [], [53139, 87241]⟩,
        ⟨131838, true, false, [], [87241]⟩
      ]⟩,
    ⟨[85775, 15], [63761, 84415], .contexts [
        ⟨131829, true, false, [63758], [15]⟩,
        ⟨39239, false, false, [63758], []⟩,
        ⟨130697, false, false, [63758], []⟩,
        ⟨131830, true, false, [], [53127, 84415]⟩,
        ⟨131831, true, false, [], [84415]⟩
      ]⟩,
    ⟨[85777, 1], [85775], .contexts [
        ⟨33439, false, false, [], []⟩,
        ⟨33621, false, false, [], []⟩
      ]⟩,
    ⟨[85777, 3], [63797, 86833], .contexts [
        ⟨131845, true, false, [63780], [3]⟩,
        ⟨119272, false, false, [63780], []⟩,
        ⟨120175, false, false, [63780], []⟩,
        ⟨131846, true, false, [], [53145, 86833]⟩,
        ⟨131858, true, false, [], [86833]⟩
      ]⟩,
    ⟨[85777, 5], [63795, 85739], .contexts [
        ⟨131845, true, false, [63780], [5]⟩,
        ⟨101074, false, false, [63780], []⟩,
        ⟨127555, false, false, [63780], []⟩,
        ⟨131846, true, false, [], [36883, 57261, 85739]⟩,
        ⟨131856, true, false, [], [57261, 85739]⟩,
        ⟨131857, true, false, [], [85739]⟩
      ]⟩,
    ⟨[85777, 7], [63791, 84269], .contexts [
        ⟨131845, true, false, [63780], [7]⟩,
        ⟨100288, false, false, [63780], []⟩,
        ⟨118058, false, false, [63780, 36497], []⟩,
        ⟨131846, true, false, [], [36497, 52049, 84269]⟩,
        ⟨131854, true, false, [], [52049, 84269]⟩,
        ⟨131855, true, false, [], [84269]⟩
      ]⟩,
    ⟨[85777, 9], [63787, 85167], .contexts [
        ⟨131853, false, false, [], []⟩
      ]⟩,
    ⟨[85777, 11], [63801, 85769], .contexts [
        ⟨131845, true, false, [63780], [11]⟩,
        ⟨127448, false, false, [63780], []⟩,
        ⟨131811, false, false, [63780, 60155], []⟩,
        ⟨131846, true, false, [], [60155, 63727, 85769]⟩,
        ⟨131859, true, false, [], [63727, 85769]⟩,
        ⟨131860, true, false, [], [85769]⟩
      ]⟩,
    ⟨[85777, 13], [85779], .contexts [
        ⟨33441, false, false, [], []⟩,
        ⟨33619, false, false, [], []⟩
      ]⟩,
    ⟨[85777, 15], [63779, 85907], .contexts [
        ⟨131845, true, false, [63780], [15]⟩,
        ⟨34174, false, false, [63780], []⟩,
        ⟨34350, false, false, [63780], []⟩,
        ⟨131849, true, false, [], [85907]⟩
      ]⟩,
    ⟨[85779, 1], [63779, 85901], .contexts [
        ⟨131864, true, false, [63780], [1]⟩,
        ⟨34168, false, false, [63780], []⟩,
        ⟨34357, false, false, [63780], []⟩,
        ⟨131849, true, false, [], [85901]⟩
      ]⟩,
    ⟨[85779, 3], [63807, 86641], .contexts [
        ⟨131864, true, false, [63780], [3]⟩,
        ⟨100197, false, false, [63780], []⟩,
        ⟨126854, false, false, [63780], []⟩,
        ⟨131866, true, false, [], [57763, 86641]⟩,
        ⟨131869, true, false, [], [86641]⟩
      ]⟩,
    ⟨[85779, 5], [63805, 86143], .contexts [
        ⟨131868, false, false, [], []⟩
      ]⟩,
    ⟨[85779, 7], [63813, 84267], .contexts [
        ⟨131864, true, false, [63780], [7]⟩,
        ⟨118627, false, false, [63780], []⟩,
        ⟨131846, true, false, [], [52593, 84267]⟩,
        ⟨131872, true, false, [], [84267]⟩
      ]⟩,
    ⟨[85779, 9], [63787, 85169], .contexts [
        ⟨131864, true, false, [63780], [9]⟩,
        ⟨100239, false, false, [63780], []⟩,
        ⟨126975, false, false, [63780], []⟩,
        ⟨131852, true, false, [], [85169]⟩
      ]⟩,
    ⟨[85779, 11], [63811, 91581], .contexts [
        ⟨131864, true, false, [63780], [11]⟩,
        ⟨100973, false, false, [63780], []⟩,
        ⟨126978, false, false, [63780], []⟩,
        ⟨131846, true, false, [], [36839, 54129, 91581]⟩,
        ⟨131870, true, false, [], [54129, 91581]⟩,
        ⟨131871, true, false, [], [91581]⟩
      ]⟩,
    ⟨[85779, 13], [85777], .contexts [
        ⟨33443, false, false, [], []⟩,
        ⟨33620, false, false, [], []⟩
      ]⟩,
    ⟨[85781], [63815, 83883], .contexts [
        ⟨131876, false, false, [], []⟩
      ]⟩,
    ⟨[85779, 15], [63815, 83883], .contexts [
        ⟨33445, false, false, [], []⟩,
        ⟨161575, false, false, [], []⟩
      ]⟩,
    ⟨[85783, 1], [63815, 83883], .contexts [
        ⟨33450, false, false, [], []⟩,
        ⟨161575, false, false, [], []⟩
      ]⟩,
    ⟨[85783, 3], [85785], .contexts [
        ⟨33452, false, false, [], []⟩,
        ⟨33616, false, false, [], []⟩
      ]⟩,
    ⟨[85783, 5], [63821, 83887], .contexts [
        ⟨131880, true, false, [63818], [5]⟩,
        ⟨36212, false, false, [63818], []⟩,
        ⟨123079, false, false, [63818], []⟩,
        ⟨131884, true, false, [], [55025, 83887]⟩,
        ⟨131885, true, false, [], [83887]⟩
      ]⟩,
    ⟨[85783, 7], [63825, 85129], .contexts [
        ⟨131880, true, false, [63818], [7]⟩,
        ⟨121435, true, false, [63818, 55032], [7]⟩,
        ⟨118574, false, false, [63818, 55032], []⟩,
        ⟨121436, true, false, [63818], [52559, 85129]⟩,
        ⟨121438, true, false, [63818], [85129]⟩,
        ⟨131881, true, false, [], [55039, 85129]⟩,
        ⟨131887, true, false, [], [85129]⟩
      ]⟩,
    ⟨[85783, 9], [63829, 84313], .contexts [
        ⟨131880, true, false, [63818], [9]⟩,
        ⟨121442, false, false, [63818], []⟩,
        ⟨131881, true, false, [], [55043, 84313]⟩,
        ⟨131890, true, false, [], [84313]⟩
      ]⟩,
    ⟨[85783, 11], [63831, 89377], .contexts [
        ⟨131880, true, false, [63818], [11]⟩,
        ⟨123078, false, false, [63818], []⟩,
        ⟨123081, false, false, [63818], []⟩,
        ⟨131881, true, false, [], [56407, 89377]⟩,
        ⟨131891, true, false, [], [89377]⟩
      ]⟩,
    ⟨[85783, 13], [63827, 85649], .contexts [
        ⟨131880, true, false, [63818], [13]⟩,
        ⟨121440, false, false, [63818], []⟩,
        ⟨126774, false, false, [63818], []⟩,
        ⟨131889, true, false, [], [85649]⟩
      ]⟩,
    ⟨[85783, 15], [63823, 85901], .contexts [
        ⟨131880, true, false, [63818], [15]⟩,
        ⟨121435, true, false, [63818, 55032], [15]⟩,
        ⟨40827, false, false, [63818, 55032], []⟩,
        ⟨118591, false, false, [63818, 55032], []⟩,
        ⟨121436, true, false, [63818], [44625, 85901]⟩,
        ⟨121437, true, false, [63818], [85901]⟩,
        ⟨131881, true, false, [], [55035, 85901]⟩,
        ⟨131886, true, false, [], [85901]⟩
      ]⟩,
    ⟨[85785, 1], [63817, 86255], .contexts [
        ⟨131894, false, false, [], []⟩,
        ⟨133584, false, false, [], []⟩
      ]⟩,
    ⟨[85785, 3], [85783], .contexts [
        ⟨33454, false, false, [], []⟩,
        ⟨33618, false, false, [], []⟩
      ]⟩,
    ⟨[85785, 5], [66057, 84549], .contexts [
        ⟨33456, false, false, [], []⟩,
        ⟨134417, false, false, [], []⟩
      ]⟩,
    ⟨[85785, 7], [63839, 67753, 87833], .contexts [
        ⟨131900, false, false, [], []⟩,
        ⟨136323, false, false, [63839], []⟩
      ]⟩,
    ⟨[85785, 9], [73141, 96905], .contexts [
        ⟨143213, true, false, [73138], [9]⟩,
        ⟨46, false, false, [73138, 96905], []⟩,
        ⟨143214, true, false, [], [96905]⟩
      ]⟩,
    ⟨[85785, 11], [63837, 83441], .contexts [
        ⟨131898, false, false, [], []⟩
      ]⟩,
    ⟨[85785, 13], [63827, 85647], .contexts [
        ⟨131893, true, false, [63818], [13]⟩,
        ⟨126782, false, false, [63818], []⟩,
        ⟨126776, false, false, [63818], []⟩,
        ⟨131889, true, false, [], [85647]⟩
      ]⟩,
    ⟨[85785, 15], [63835, 63889, 83717], .contexts [
        ⟨131893, true, false, [63818], [15]⟩,
        ⟨126898, false, false, [63818], []⟩,
        ⟨127926, false, false, [63818, 59667], []⟩,
        ⟨131881, true, false, [], [59667, 59827, 88663]⟩,
        ⟨131895, true, false, [], [59827, 88663]⟩,
        ⟨131896, true, false, [], [88663]⟩,
        ⟨131989, false, false, [63835], []⟩
      ]⟩,
    ⟨[85799, 1], [85801], .contexts [
        ⟨33481, false, false, [], []⟩,
        ⟨33607, false, false, [], []⟩
      ]⟩,
    ⟨[85799, 3], [59823, 84405], .contexts [
        ⟨127079, false, false, [], []⟩,
        ⟨133734, false, false, [], []⟩
      ]⟩,
    ⟨[85799, 5], [64065, 94235], .contexts [
        ⟨132174, false, false, [], []⟩,
        ⟨133710, false, false, [], []⟩
      ]⟩,
    ⟨[85799, 7], [64069, 85751], .contexts [
        ⟨132180, false, false, [], []⟩,
        ⟨133738, false, false, [], []⟩
      ]⟩,
    ⟨[85799, 9], [64023, 96307], .contexts [
        ⟨132116, false, false, [], []⟩,
        ⟨133745, false, false, [], []⟩
      ]⟩,
    ⟨[85799, 11], [59819, 86247], .contexts [
        ⟨127077, false, false, [], []⟩,
        ⟨133717, false, false, [], []⟩
      ]⟩,
    ⟨[85799, 13], [60833, 83041], .contexts [
        ⟨128214, false, false, [], []⟩,
        ⟨134852, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2525. -/
def y322TCIndexRaw2525 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85799, 15], [59821, 84755], .contexts [
        ⟨33479, false, false, [], []⟩,
        ⟨133416, false, false, [], []⟩
      ]⟩,
    ⟨[85801, 1], [85799], .contexts [
        ⟨33483, false, false, [], []⟩,
        ⟨33609, false, false, [], []⟩
      ]⟩,
    ⟨[85803], [59075, 83875], .contexts [
        ⟨126192, false, false, [], []⟩
      ]⟩,
    ⟨[85801, 3], [59075, 83875], .contexts [
        ⟨33485, false, false, [], []⟩,
        ⟨161602, false, false, [], []⟩
      ]⟩,
    ⟨[85801, 5], [59545, 61611, 91145], .contexts [
        ⟨126760, false, false, [], []⟩,
        ⟨132167, false, false, [59545], []⟩
      ]⟩,
    ⟨[85801, 7], [60859, 83031], .contexts [
        ⟨128251, false, false, [], []⟩,
        ⟨132176, false, false, [], []⟩
      ]⟩,
    ⟨[85801, 9], [21235, 85801], .contexts [
        ⟨33487, true, false, [], [9]⟩,
        ⟨44614, true, false, [21210], [3, 9]⟩,
        ⟨479, false, false, [21210, 85803], []⟩,
        ⟨21, false, false, [21210, 85803], []⟩,
        ⟨33606, false, false, [21210], []⟩,
        ⟨33607, false, false, [21210], []⟩,
        ⟨33486, false, false, [21210], []⟩,
        ⟨33486, false, false, [21210], []⟩,
        ⟨44615, false, false, [21210], []⟩,
        ⟨44570, true, false, [], [85801]⟩
      ]⟩,
    ⟨[85801, 11], [66803, 93977], .contexts [
        ⟨135187, true, false, [66800], [11]⟩,
        ⟨53, false, false, [66800, 93977], []⟩,
        ⟨135188, true, false, [], [93977]⟩
      ]⟩,
    ⟨[85801, 13], [59805, 59811, 63907, 83719], .contexts [
        ⟨127053, false, false, [], []⟩,
        ⟨127064, false, false, [59805], []⟩,
        ⟨132183, false, false, [59805], []⟩
      ]⟩,
    ⟨[85801, 15], [59821, 84757], .contexts [
        ⟨127067, true, false, [59816], [15]⟩,
        ⟨75324, true, false, [59816, 28640], [15]⟩,
        ⟨1, false, false, [59816, 28640, 84757], []⟩,
        ⟨74546, true, false, [59816], [84757]⟩,
        ⟨75321, false, false, [59816], []⟩,
        ⟨127070, true, false, [], [84757]⟩,
        ⟨127069, true, false, [], [84757]⟩
      ]⟩,
    ⟨[85805, 1], [85807], .contexts [
        ⟨33492, false, false, [], []⟩,
        ⟨33600, false, false, [], []⟩
      ]⟩,
    ⟨[85805, 3], [59437, 67771, 87835], .contexts [
        ⟨126641, false, false, [], []⟩,
        ⟨136334, false, false, [59437], []⟩
      ]⟩,
    ⟨[85805, 5], [59075, 83875], .contexts [
        ⟨33490, false, false, [], []⟩,
        ⟨161602, false, false, [], []⟩
      ]⟩,
    ⟨[85805, 7], [36785, 83879], .contexts [
        ⟨100913, false, false, [], []⟩,
        ⟨100908, false, false, [], []⟩
      ]⟩,
    ⟨[85805, 9], [21235, 85805], .contexts [
        ⟨44571, false, false, [], []⟩,
        ⟨44581, false, false, [], []⟩
      ]⟩,
    ⟨[85805, 11], [55773, 84415], .contexts [
        ⟨122327, true, false, [55774], [11]⟩,
        ⟨53, false, false, [55774, 84415], []⟩,
        ⟨122328, true, false, [], [84415]⟩
      ]⟩,
    ⟨[85805, 13], [59061, 88501], .contexts [
        ⟨126153, true, false, [59054], [13]⟩,
        ⟨80775, false, false, [59054], []⟩,
        ⟨117994, false, false, [59054], []⟩,
        ⟨117992, false, false, [59054], []⟩,
        ⟨126117, false, false, [59054, 52079], []⟩,
        ⟨126154, true, false, [59054], [88501]⟩,
        ⟨126156, true, false, [], [59059, 88501]⟩,
        ⟨126157, true, false, [], [88501]⟩
      ]⟩,
    ⟨[85805, 15], [59057, 63727, 85771], .contexts [
        ⟨126158, false, false, [], []⟩,
        ⟨131819, false, false, [59057], []⟩
      ]⟩,
    ⟨[85807, 1], [85805], .contexts [
        ⟨33494, false, false, [], []⟩,
        ⟨33602, false, false, [], []⟩
      ]⟩,
    ⟨[85807, 3], [23149, 44383, 85131], .contexts [
        ⟨51810, false, false, [], []⟩,
        ⟨109301, false, false, [23149], []⟩
      ]⟩,
    ⟨[85807, 5], [59549, 83873], .contexts [
        ⟨126766, false, false, [], []⟩
      ]⟩,
    ⟨[85807, 7], [36785, 83881], .contexts [
        ⟨100853, false, false, [], []⟩,
        ⟨100906, false, false, [], []⟩
      ]⟩,
    ⟨[85807, 9], [85809], .contexts [
        ⟨33496, false, false, [], []⟩,
        ⟨33598, false, false, [], []⟩
      ]⟩,
    ⟨[85807, 11], [46449, 85907], .contexts [
        ⟨111774, false, false, [], []⟩,
        ⟨122320, false, false, [], []⟩
      ]⟩,
    ⟨[85807, 13], [55779, 57493, 86837], .contexts [
        ⟨122334, true, false, [55780], [13]⟩,
        ⟨59, false, false, [55780, 89383], []⟩,
        ⟨122332, false, true, [], [89383]⟩,
        ⟨124380, false, false, [55779], []⟩
      ]⟩,
    ⟨[85807, 15], [60207, 63727, 85769], .contexts [
        ⟨127502, false, false, [], []⟩,
        ⟨131810, false, false, [60207], []⟩
      ]⟩,
    ⟨[85809, 1], [21211, 85809], .contexts [
        ⟨44539, false, false, [], []⟩,
        ⟨44535, false, false, [], []⟩
      ]⟩,
    ⟨[85809, 3], [23149, 39363, 83821], .contexts [
        ⟨51797, true, false, [23146], [3]⟩,
        ⟨20, false, false, [23146, 85199], []⟩,
        ⟨51765, true, false, [], [85199]⟩,
        ⟨104439, false, false, [23149], []⟩
      ]⟩,
    ⟨[85809, 5], [69079, 87843], .contexts [
        ⟨137670, false, false, [], []⟩
      ]⟩,
    ⟨[85809, 7], [75283, 97173], .contexts [
        ⟨146579, true, false, [75280], [7]⟩,
        ⟨38, false, false, [75280, 97173], []⟩,
        ⟨146580, true, false, [], [97173]⟩
      ]⟩,
    ⟨[85809, 9], [85807], .contexts [
        ⟨33498, false, false, [], []⟩,
        ⟨33600, false, false, [], []⟩
      ]⟩,
    ⟨[85809, 11], [85811], .contexts [
        ⟨33500, false, false, [], []⟩,
        ⟨33596, false, false, [], []⟩
      ]⟩,
    ⟨[85809, 13], [57545, 86839], .contexts [
        ⟨124434, false, false, [], []⟩
      ]⟩,
    ⟨[85809, 15], [23151, 85733], .contexts [
        ⟨51814, false, false, [], []⟩
      ]⟩,
    ⟨[85811, 1], [21211, 85811], .contexts [
        ⟨33504, false, false, [], []⟩,
        ⟨44531, false, false, [], []⟩
      ]⟩,
    ⟨[85811, 3], [23149, 85201], .contexts [
        ⟨51769, false, false, [], []⟩,
        ⟨51793, false, false, [], []⟩
      ]⟩,
    ⟨[85811, 5], [70807, 87845], .contexts [
        ⟨139554, false, false, [], []⟩
      ]⟩,
    ⟨[85811, 7], [28249, 92573], .contexts [
        ⟨73228, false, false, [], []⟩
      ]⟩,
    ⟨[85811, 9], [21253, 87297], .contexts [
        ⟨44603, false, false, [], []⟩,
        ⟨44626, false, false, [], []⟩
      ]⟩,
    ⟨[85811, 11], [85809], .contexts [
        ⟨33502, false, false, [], []⟩,
        ⟨33598, false, false, [], []⟩
      ]⟩,
    ⟨[85811, 13], [21209, 83087], .contexts [
        ⟨44496, false, false, [], []⟩
      ]⟩,
    ⟨[85811, 15], [23151, 97023], .contexts [
        ⟨145403, true, false, [23152], [15]⟩,
        ⟨1, false, false, [23152, 97023], []⟩,
        ⟨51815, false, true, [], [97023]⟩
      ]⟩,
    ⟨[85821, 1], [33545, 94903], .contexts [
        ⟨91244, false, false, [], []⟩
      ]⟩,
    ⟨[85821, 3], [38673, 85003], .contexts [
        ⟨33521, false, false, [], []⟩,
        ⟨103664, false, false, [], []⟩
      ]⟩,
    ⟨[85821, 5], [85823], .contexts [
        ⟨33523, false, false, [], []⟩,
        ⟨33589, false, false, [], []⟩
      ]⟩,
    ⟨[85821, 7], [44917, 84333], .contexts [
        ⟨109917, false, false, [], []⟩
      ]⟩,
    ⟨[85821, 9], [27933, 90371], .contexts [
        ⟨72127, true, false, [27930], [9]⟩,
        ⟨46, false, false, [27930, 90371], []⟩,
        ⟨72128, true, false, [], [90371]⟩
      ]⟩,
    ⟨[85821, 11], [26199, 85119], .contexts [
        ⟨65837, true, false, [26196], [11]⟩,
        ⟨53, false, false, [26196, 85119], []⟩,
        ⟨65838, true, false, [], [85119]⟩
      ]⟩,
    ⟨[85821, 13], [44923, 69675, 87883], .contexts [
        ⟨109921, false, false, [], []⟩,
        ⟨138266, false, false, [44923], []⟩
      ]⟩,
    ⟨[85821, 15], [18505, 83091], .contexts [
        ⟨33867, false, false, [], []⟩,
        ⟨33869, false, false, [], []⟩
      ]⟩,
    ⟨[85823, 1], [48437, 84143], .contexts [
        ⟨33527, false, false, [], []⟩,
        ⟨113771, false, false, [], []⟩
      ]⟩,
    ⟨[85823, 3], [50433, 85297], .contexts [
        ⟨116015, false, false, [], []⟩
      ]⟩,
    ⟨[85823, 5], [85821], .contexts [
        ⟨33525, false, false, [], []⟩,
        ⟨33590, false, false, [], []⟩
      ]⟩,
    ⟨[85823, 7], [18529, 85823], .contexts [
        ⟨33858, false, false, [], []⟩,
        ⟨47198, false, false, [], []⟩
      ]⟩,
    ⟨[85823, 9], [44913, 91831], .contexts [
        ⟨109912, false, false, [], []⟩
      ]⟩,
    ⟨[85823, 11], [21161, 50185, 83833], .contexts [
        ⟨44352, false, false, [], []⟩,
        ⟨115715, false, false, [21161], []⟩
      ]⟩,
    ⟨[85823, 13], [21949, 87917], .contexts [
        ⟨47135, false, false, [], []⟩,
        ⟨47195, false, false, [], []⟩
      ]⟩,
    ⟨[85823, 15], [18505, 83093], .contexts [
        ⟨33855, true, false, [18502], [15]⟩,
        ⟨1, false, false, [18502, 83093], []⟩,
        ⟨33781, true, false, [], [83093]⟩,
        ⟨33850, false, false, [], []⟩
      ]⟩,
    ⟨[85829, 1], [85831], .contexts [
        ⟨33539, false, false, [], []⟩,
        ⟨33581, false, false, [], []⟩
      ]⟩,
    ⟨[85829, 3], [73525, 97213], .contexts [
        ⟨147265, true, false, [73522], [3]⟩,
        ⟨20, false, false, [73522, 97213], []⟩,
        ⟨143684, true, false, [], [97213]⟩
      ]⟩,
    ⟨[85829, 5], [72955, 96887], .contexts [
        ⟨142897, true, false, [72952], [5]⟩,
        ⟨28, false, false, [72952, 96887], []⟩,
        ⟨142862, true, false, [], [96887]⟩
      ]⟩,
    ⟨[85829, 7], [18531, 85829], .contexts [
        ⟨33821, false, false, [], []⟩,
        ⟨33834, false, false, [], []⟩
      ]⟩,
    ⟨[85829, 9], [73525, 96927], .contexts [
        ⟨143686, false, false, [], []⟩
      ]⟩,
    ⟨[85829, 11], [40943, 48687, 85409], .contexts [
        ⟨33537, false, false, [], []⟩,
        ⟨153782, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2526. -/
def y322TCIndexRaw2526 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85829, 13], [48775, 85399], .contexts [
        ⟨114103, false, false, [], []⟩
      ]⟩,
    ⟨[85829, 15], [18505, 83099], .contexts [
        ⟨33800, false, false, [], []⟩,
        ⟨33811, false, false, [], []⟩
      ]⟩,
    ⟨[85831, 1], [85829], .contexts [
        ⟨33541, false, false, [], []⟩,
        ⟨33582, false, false, [], []⟩
      ]⟩,
    ⟨[85831, 3], [18521, 85831], .contexts [
        ⟨33807, false, false, [], []⟩
      ]⟩,
    ⟨[85831, 5], [72955, 96885], .contexts [
        ⟨142861, true, false, [72952], [5]⟩,
        ⟨28, false, false, [72952, 96885], []⟩,
        ⟨142862, true, false, [], [96885]⟩
      ]⟩,
    ⟨[85831, 7], [18525, 85831], .contexts [
        ⟨33810, false, false, [], []⟩
      ]⟩,
    ⟨[85831, 9], [24899, 90337], .contexts [
        ⟨60254, false, false, [], []⟩
      ]⟩,
    ⟨[85831, 11], [33285, 95417], .contexts [
        ⟨90718, false, false, [], []⟩,
        ⟨99799, false, false, [], []⟩
      ]⟩,
    ⟨[85831, 13], [85833], .contexts [
        ⟨33543, false, false, [], []⟩,
        ⟨33580, false, false, [], []⟩
      ]⟩,
    ⟨[85831, 15], [18505, 83101], .contexts [
        ⟨33782, false, false, [], []⟩
      ]⟩,
    ⟨[85833, 1], [42751, 92193], .contexts [
        ⟨107567, true, false, [42752], [1]⟩,
        ⟨70610, false, false, [42752], []⟩,
        ⟨70613, false, false, [42752], []⟩,
        ⟨107571, true, false, [], [92193]⟩
      ]⟩,
    ⟨[85833, 3], [18511, 85833], .contexts [
        ⟨33783, false, false, [18506], [85833, 3]⟩,
        ⟨33772, true, false, [18506, 17801], [3]⟩,
        ⟨29483, true, false, [18506], [15, 3]⟩,
        ⟨499, false, false, [18506, 84955], []⟩,
        ⟨33784, false, false, [18506], []⟩,
        ⟨33776, false, false, [18506], []⟩,
        ⟨33785, false, false, [18506, 18501], []⟩,
        ⟨33786, true, false, [], [18501, 85833]⟩,
        ⟨33787, true, false, [], [85833]⟩
      ]⟩,
    ⟨[85833, 5], [42751, 93813], .contexts [
        ⟨107572, false, false, [], []⟩
      ]⟩,
    ⟨[85833, 7], [18517, 85833], .contexts [
        ⟨33788, false, false, [18512], [85833, 7]⟩,
        ⟨33772, true, false, [18512, 17805], [7]⟩,
        ⟨29486, true, false, [18512], [15, 7]⟩,
        ⟨18155, false, false, [18512, 84955], []⟩,
        ⟨33784, false, false, [18512], []⟩,
        ⟨33776, false, false, [18512], []⟩,
        ⟨33785, false, false, [18512, 18501], []⟩,
        ⟨33789, true, false, [], [18501, 85833]⟩,
        ⟨33790, true, false, [], [85833]⟩
      ]⟩,
    ⟨[85833, 9], [24899, 90339], .contexts [
        ⟨60207, false, false, [], []⟩
      ]⟩,
    ⟨[85833, 11], [31827, 39159, 46991, 89159], .contexts [
        ⟨86144, false, false, [], []⟩,
        ⟨160741, false, false, [31827], []⟩
      ]⟩,
    ⟨[85833, 13], [85831], .contexts [
        ⟨33545, false, false, [], []⟩,
        ⟨33581, false, false, [], []⟩
      ]⟩,
    ⟨[85833, 15], [18499, 42759, 84865], .contexts [
        ⟨33547, false, false, [], []⟩,
        ⟨107573, false, false, [], []⟩,
        ⟨107577, false, false, [18499], []⟩
      ]⟩,
    ⟨[85839, 1], [18485, 85839], .contexts [
        ⟨33753, false, false, [], []⟩
      ]⟩,
    ⟨[85839, 3], [18499, 41043, 84867], .contexts [
        ⟨33555, false, false, [], []⟩,
        ⟨33765, false, false, [], []⟩,
        ⟨106025, false, false, [18499], []⟩
      ]⟩,
    ⟨[85839, 5], [18481, 85839], .contexts [
        ⟨33557, false, false, [], []⟩,
        ⟨33754, false, false, [], []⟩
      ]⟩,
    ⟨[85839, 7], [18497, 85839], .contexts [
        ⟨33761, false, false, [18480], []⟩,
        ⟨33755, false, false, [18480, 18473], []⟩,
        ⟨33751, true, false, [], [18473, 18481, 85839]⟩,
        ⟨33762, true, false, [], [18481, 85839]⟩,
        ⟨33763, true, false, [], [85839]⟩
      ]⟩,
    ⟨[85839, 9], [18489, 85839], .contexts [
        ⟨33749, true, false, [18480], [9]⟩,
        ⟨33733, true, false, [18480, 18460], [9]⟩,
        ⟨33565, false, false, [18480, 18460], []⟩,
        ⟨33736, false, false, [18480, 18460], []⟩,
        ⟨33737, true, false, [18480], [18463, 85841]⟩,
        ⟨33738, true, false, [18480], [85841]⟩,
        ⟨33755, false, false, [18480, 18465], []⟩,
        ⟨33751, true, false, [], [18465, 18481, 85839]⟩,
        ⟨33756, true, false, [], [18481, 85839]⟩,
        ⟨33757, true, false, [], [85839]⟩
      ]⟩,
    ⟨[85839, 11], [18493, 85847], .contexts [
        ⟨33760, false, false, [], []⟩
      ]⟩,
    ⟨[85839, 13], [18491, 85229], .contexts [
        ⟨33749, true, false, [18480], [13]⟩,
        ⟨33733, true, false, [18480, 18460], [13]⟩,
        ⟨33717, false, false, [18480, 18460], []⟩,
        ⟨33737, true, false, [18480], [18439, 85229]⟩,
        ⟨33739, true, false, [18480], [85229]⟩,
        ⟨33751, true, false, [], [18467, 85229]⟩,
        ⟨33758, true, false, [], [85229]⟩
      ]⟩,
    ⟨[85839, 15], [49023, 93421], .contexts [
        ⟨114380, false, false, [], []⟩
      ]⟩,
    ⟨[85847, 1], [18415, 85847], .contexts [
        ⟨33573, false, false, [], []⟩,
        ⟨33679, false, false, [], []⟩
      ]⟩,
    ⟨[85847, 3], [19987, 87331], .contexts [
        ⟨41121, false, false, [], []⟩
      ]⟩,
    ⟨[85847, 5], [18423, 85847], .contexts [
        ⟨33689, false, false, [], []⟩,
        ⟨33703, false, false, [], []⟩
      ]⟩,
    ⟨[85847, 7], [18429, 85847], .contexts [
        ⟨33695, false, false, [], []⟩,
        ⟨33705, false, false, [], []⟩
      ]⟩,
    ⟨[85847, 9], [49457, 94665], .contexts [
        ⟨114897, false, false, [], []⟩
      ]⟩,
    ⟨[85847, 11], [18443, 18461, 18481, 85839], .contexts [
        ⟨33571, false, false, [], []⟩,
        ⟨160347, false, false, [], []⟩
      ]⟩,
    ⟨[85847, 13], [18411, 85099], .contexts [
        ⟨33672, false, false, [], []⟩,
        ⟨33668, false, false, [], []⟩
      ]⟩,
    ⟨[85847, 15], [47217, 93419], .contexts [
        ⟨112593, true, false, [47214], [15]⟩,
        ⟨1, false, false, [47214, 93419], []⟩,
        ⟨112594, true, false, [], [93419]⟩
      ]⟩,
    ⟨[85855, 1], [17775, 82971], .contexts [
        ⟨33971, false, false, [], []⟩,
        ⟨33968, false, false, [], []⟩
      ]⟩,
    ⟨[85855, 3], [17753, 82995], .contexts [
        ⟨33953, false, false, [], []⟩,
        ⟨33950, false, false, [], []⟩
      ]⟩,
    ⟨[85855, 5], [17759, 83675], .contexts [
        ⟨33958, false, false, [], []⟩,
        ⟨33955, false, false, [], []⟩
      ]⟩,
    ⟨[85855, 7], [17767, 85855], .contexts [
        ⟨33964, false, false, [], []⟩,
        ⟨33959, false, false, [], []⟩
      ]⟩,
    ⟨[85855, 9], [20695, 86551], .contexts [
        ⟨42503, false, false, [], []⟩,
        ⟨42837, false, false, [], []⟩
      ]⟩,
    ⟨[85855, 11], [17775, 82975], .contexts [
        ⟨33966, false, false, [], []⟩,
        ⟨30712, false, false, [], []⟩
      ]⟩,
    ⟨[85855, 13], [20313, 83643], .contexts [
        ⟨33945, false, false, [], []⟩,
        ⟨41815, false, false, [], []⟩
      ]⟩,
    ⟨[85855, 15], [48657, 85405], .contexts [
        ⟨33973, false, false, [], []⟩,
        ⟨114003, false, false, [], []⟩
      ]⟩,
    ⟨[85861, 1], [17753, 83001], .contexts [
        ⟨34021, false, false, [], []⟩,
        ⟨34017, false, false, [], []⟩
      ]⟩,
    ⟨[85861, 3], [48657, 85407], .contexts [
        ⟨34013, false, false, [], []⟩,
        ⟨114016, false, false, [], []⟩
      ]⟩,
    ⟨[85861, 5], [17753, 83005], .contexts [
        ⟨34041, false, false, [], []⟩,
        ⟨34033, false, false, [], []⟩
      ]⟩,
    ⟨[85861, 7], [17767, 85861], .contexts [
        ⟨34027, false, false, [], []⟩,
        ⟨34023, false, false, [], []⟩
      ]⟩,
    ⟨[85861, 9], [42617, 86385], .contexts [
        ⟨107452, false, false, [], []⟩,
        ⟨113398, false, false, [], []⟩
      ]⟩,
    ⟨[85861, 11], [48093, 95049], .contexts [
        ⟨113421, false, false, [], []⟩,
        ⟨113426, false, false, [], []⟩
      ]⟩,
    ⟨[85861, 13], [21139, 40379, 85699], .contexts [
        ⟨99805, false, false, [], []⟩,
        ⟨105435, false, false, [21139], []⟩
      ]⟩,
    ⟨[85861, 15], [18537, 83469], .contexts [
        ⟨34030, false, false, [], []⟩,
        ⟨113408, false, false, [], []⟩
      ]⟩,
    ⟨[85865, 1], [85867], .contexts [
        ⟨34097, false, false, [], []⟩,
        ⟨34379, false, false, [], []⟩
      ]⟩,
    ⟨[85865, 3], [323, 85865], .contexts [
        ⟨34094, false, false, [], []⟩,
        ⟨34095, false, false, [323], []⟩,
        ⟨3220, true, false, [], [85865]⟩,
        ⟨34093, false, false, [], []⟩
      ]⟩,
    ⟨[85865, 5], [48147, 48979, 88923], .contexts [
        ⟨113472, false, false, [], []⟩,
        ⟨114346, false, false, [48147], []⟩
      ]⟩,
    ⟨[85865, 7], [21961, 84975], .contexts [
        ⟨47178, false, false, [], []⟩,
        ⟨47170, false, false, [], []⟩
      ]⟩,
    ⟨[85865, 9], [21967, 84731], .contexts [
        ⟨47184, false, false, [], []⟩
      ]⟩,
    ⟨[85865, 11], [20825, 83003], .contexts [
        ⟨34090, false, false, [], []⟩,
        ⟨153432, false, false, [], []⟩
      ]⟩,
    ⟨[85865, 13], [21979, 85865], .contexts [
        ⟨47194, false, false, [], []⟩,
        ⟨47242, false, false, [], []⟩
      ]⟩,
    ⟨[85865, 15], [21919, 47673, 84031], .contexts [
        ⟨47124, false, false, [], []⟩,
        ⟨113062, false, false, [21919], []⟩
      ]⟩,
    ⟨[85867, 1], [85865], .contexts [
        ⟨34098, false, false, [], []⟩,
        ⟨34091, false, false, [], []⟩
      ]⟩,
    ⟨[85867, 3], [49215, 89799], .contexts [
        ⟨114577, false, false, [], []⟩,
        ⟨123446, false, false, [], []⟩
      ]⟩,
    ⟨[85867, 5], [48101, 95049], .contexts [
        ⟨113431, false, false, [], []⟩
      ]⟩,
    ⟨[85867, 7], [21961, 84977], .contexts [
        ⟨47241, false, false, [], []⟩,
        ⟨103203, false, false, [], []⟩
      ]⟩,
    ⟨[85867, 9], [28629, 33377, 38189, 47485, 84007], .contexts [
        ⟨74459, false, false, [], []⟩,
        ⟨158739, false, false, [28629], []⟩
      ]⟩,
    ⟨[85867, 11], [20825, 83005], .contexts [
        ⟨43004, true, false, [20672], [11]⟩,
        ⟨53, false, false, [20672, 83005], []⟩,
        ⟨42777, true, false, [], [83005]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2527. -/
def y322TCIndexRaw2527 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85867, 13], [85869], .contexts [
        ⟨34100, false, false, [], []⟩,
        ⟨34378, false, false, [], []⟩
      ]⟩,
    ⟨[85867, 15], [21919, 87935], .contexts [
        ⟨47082, true, false, [21916], [15]⟩,
        ⟨1, false, false, [21916, 87935], []⟩,
        ⟨47083, true, false, [], [87935]⟩
      ]⟩,
    ⟨[85869, 1], [21977, 85869], .contexts [
        ⟨47251, false, false, [], []⟩,
        ⟨47285, false, false, [], []⟩
      ]⟩,
    ⟨[85869, 3], [63307, 86859], .contexts [
        ⟨131262, false, false, [], []⟩
      ]⟩,
    ⟨[85869, 5], [75643, 97213], .contexts [
        ⟨147267, true, false, [75640], [5]⟩,
        ⟨28, false, false, [75640, 97213], []⟩,
        ⟨147268, true, false, [], [97213]⟩
      ]⟩,
    ⟨[85869, 7], [38231, 49763, 94111], .contexts [
        ⟨103195, false, false, [], []⟩,
        ⟨115267, false, false, [38231], []⟩
      ]⟩,
    ⟨[85869, 9], [33417, 49829, 87367], .contexts [
        ⟨91022, false, false, [], []⟩,
        ⟨115329, false, false, [33417], []⟩
      ]⟩,
    ⟨[85869, 11], [20825, 58471, 91679], .contexts [
        ⟨98307, false, false, [], []⟩,
        ⟨125477, false, false, [20825], []⟩
      ]⟩,
    ⟨[85869, 13], [85867], .contexts [
        ⟨34102, false, false, [], []⟩,
        ⟨34379, false, false, [], []⟩
      ]⟩,
    ⟨[85869, 15], [85871], .contexts [
        ⟨34104, false, false, [], []⟩,
        ⟨34377, false, false, [], []⟩
      ]⟩,
    ⟨[85873], [21979, 85871], .contexts [
        ⟨82529, false, false, [], []⟩
      ]⟩,
    ⟨[85871, 1], [21979, 85871], .contexts [
        ⟨34108, false, false, [], []⟩,
        ⟨161738, false, false, [], []⟩
      ]⟩,
    ⟨[85871, 3], [21977, 85875], .contexts [
        ⟨47290, false, false, [], []⟩,
        ⟨69238, false, false, [], []⟩
      ]⟩,
    ⟨[85871, 5], [27109, 83777], .contexts [
        ⟨69303, true, false, [27110], [5]⟩,
        ⟨28, false, false, [27110, 83777], []⟩,
        ⟨69301, false, true, [], [83777]⟩
      ]⟩,
    ⟨[85871, 7], [27115, 88019], .contexts [
        ⟨69310, false, false, [], []⟩,
        ⟨82554, false, false, [], []⟩
      ]⟩,
    ⟨[85871, 9], [30911, 33425, 45397, 87359], .contexts [
        ⟨82528, false, false, [], []⟩,
        ⟨159216, false, false, [30911], []⟩
      ]⟩,
    ⟨[85871, 11], [30911, 94055], .contexts [
        ⟨82526, false, false, [], []⟩
      ]⟩,
    ⟨[85871, 13], [27061, 85251], .contexts [
        ⟨69228, false, false, [], []⟩,
        ⟨69230, false, false, [], []⟩
      ]⟩,
    ⟨[85871, 15], [85869], .contexts [
        ⟨34106, false, false, [], []⟩,
        ⟨34378, false, false, [], []⟩
      ]⟩,
    ⟨[85875, 1], [27067, 39703, 50007, 86865], .contexts [
        ⟨69248, false, false, [], []⟩,
        ⟨154610, false, false, [27067], []⟩
      ]⟩,
    ⟨[85875, 3], [21979, 85871], .contexts [
        ⟨34113, false, false, [], []⟩,
        ⟨161738, false, false, [], []⟩
      ]⟩,
    ⟨[85875, 5], [85877], .contexts [
        ⟨34115, false, false, [], []⟩,
        ⟨34374, false, false, [], []⟩
      ]⟩,
    ⟨[85875, 7], [27073, 85265], .contexts [
        ⟨69254, false, false, [], []⟩,
        ⟨76168, false, false, [], []⟩
      ]⟩,
    ⟨[85875, 9], [29221, 92951], .contexts [
        ⟨76135, false, false, [], []⟩,
        ⟨76138, false, false, [], []⟩
      ]⟩,
    ⟨[85875, 11], [27075, 91935], .contexts [
        ⟨69256, false, false, [], []⟩,
        ⟨124319, false, false, [], []⟩
      ]⟩,
    ⟨[85875, 13], [27071, 85253], .contexts [
        ⟨69252, false, false, [], []⟩,
        ⟨76159, false, false, [], []⟩
      ]⟩,
    ⟨[85875, 15], [57419, 86859], .contexts [
        ⟨124300, false, false, [], []⟩,
        ⟨124306, false, false, [], []⟩
      ]⟩,
    ⟨[85877, 1], [85879], .contexts [
        ⟨34119, false, false, [], []⟩,
        ⟨34373, false, false, [], []⟩
      ]⟩,
    ⟨[85877, 3], [27085, 85315], .contexts [
        ⟨69261, true, false, [27078], [3]⟩,
        ⟨44368, false, false, [27078], []⟩,
        ⟨44424, false, false, [27078], []⟩,
        ⟨69262, true, false, [], [21149, 85315]⟩,
        ⟨69269, true, false, [], [85315]⟩
      ]⟩,
    ⟨[85877, 5], [85875], .contexts [
        ⟨34117, false, false, [], []⟩,
        ⟨34375, false, false, [], []⟩
      ]⟩,
    ⟨[85877, 7], [27087, 87797], .contexts [
        ⟨69261, true, false, [27078], [7]⟩,
        ⟨46270, false, false, [27078], []⟩,
        ⟨46296, false, false, [27078], []⟩,
        ⟨69271, true, false, [], [87797]⟩
      ]⟩,
    ⟨[85877, 9], [27089, 89085], .contexts [
        ⟨69273, false, false, [], []⟩,
        ⟨76136, false, false, [], []⟩
      ]⟩,
    ⟨[85877, 11], [27077, 85935], .contexts [
        ⟨69261, true, false, [27078], [11]⟩,
        ⟨34235, false, false, [27078], []⟩,
        ⟨34322, false, false, [27078], []⟩,
        ⟨69265, true, false, [], [85935]⟩
      ]⟩,
    ⟨[85877, 13], [27083, 85255], .contexts [
        ⟨69261, true, false, [27078], [13]⟩,
        ⟨35865, false, false, [27078], []⟩,
        ⟨42670, false, false, [27078, 18943], []⟩,
        ⟨69267, true, false, [], [20751, 85255]⟩,
        ⟨69268, true, false, [], [85255]⟩
      ]⟩,
    ⟨[85877, 15], [27091, 91365], .contexts [
        ⟨69276, false, false, [], []⟩
      ]⟩,
    ⟨[85879, 1], [85877], .contexts [
        ⟨34121, false, false, [], []⟩,
        ⟨34374, false, false, [], []⟩
      ]⟩,
    ⟨[85879, 3], [27093, 84337], .contexts [
        ⟨69280, true, false, [27078], [3]⟩,
        ⟨44436, false, false, [27078], []⟩,
        ⟨44427, false, false, [27078], []⟩,
        ⟨69262, true, false, [], [21187, 84337]⟩,
        ⟨69281, true, false, [], [84337]⟩
      ]⟩,
    ⟨[85879, 5], [27095, 39703, 50007, 86865], .contexts [
        ⟨69283, false, false, [], []⟩,
        ⟨154610, false, false, [27095], []⟩
      ]⟩,
    ⟨[85879, 7], [27087, 38469, 83811], .contexts [
        ⟨69280, true, false, [27078], [7]⟩,
        ⟨46302, false, false, [27078], []⟩,
        ⟨46298, false, false, [27078], []⟩,
        ⟨69271, true, false, [], [87795]⟩,
        ⟨103441, false, false, [27087], []⟩
      ]⟩,
    ⟨[85879, 9], [85881], .contexts [
        ⟨34123, false, false, [], []⟩,
        ⟨34371, false, false, [], []⟩
      ]⟩,
    ⟨[85879, 11], [27081, 86213], .contexts [
        ⟨69280, true, false, [27078], [11]⟩,
        ⟨35870, false, false, [27078], []⟩,
        ⟨35883, false, false, [27078], []⟩,
        ⟨69267, true, false, [], [86213]⟩
      ]⟩,
    ⟨[85879, 13], [27077, 85941], .contexts [
        ⟨69280, true, false, [27078], [13]⟩,
        ⟨34241, false, false, [27078], []⟩,
        ⟨34318, false, false, [27078], []⟩,
        ⟨69265, true, false, [], [85941]⟩
      ]⟩,
    ⟨[85879, 15], [27091, 91363], .contexts [
        ⟨69284, false, false, [], []⟩,
        ⟨147302, false, false, [], []⟩
      ]⟩,
    ⟨[85881, 1], [27097, 89835], .contexts [
        ⟨69292, false, false, [], []⟩,
        ⟨69313, false, false, [], []⟩
      ]⟩,
    ⟨[85881, 3], [32377, 95129], .contexts [
        ⟨88063, false, false, [], []⟩,
        ⟨88084, false, false, [], []⟩
      ]⟩,
    ⟨[85881, 5], [27105, 39721, 84513], .contexts [
        ⟨69298, false, false, [], []⟩,
        ⟨104819, false, false, [27105], []⟩
      ]⟩,
    ⟨[85881, 7], [27103, 38643, 50627, 90325], .contexts [
        ⟨69296, false, false, [], []⟩,
        ⟨156240, false, false, [27103], []⟩
      ]⟩,
    ⟨[85881, 9], [85879], .contexts [
        ⟨34125, false, false, [], []⟩,
        ⟨34373, false, false, [], []⟩
      ]⟩,
    ⟨[85881, 11], [85883], .contexts [
        ⟨34127, false, false, [], []⟩,
        ⟨34370, false, false, [], []⟩
      ]⟩,
    ⟨[85881, 13], [27101, 88473], .contexts [
        ⟨69294, false, false, [], []⟩,
        ⟨69319, false, false, [], []⟩
      ]⟩,
    ⟨[85881, 15], [97215], .contexts [
        ⟨147283, false, false, [], []⟩,
        ⟨147284, false, false, [], []⟩
      ]⟩,
    ⟨[85883, 1], [53217, 84801], .contexts [
        ⟨34131, false, false, [], []⟩,
        ⟨119373, false, false, [], []⟩
      ]⟩,
    ⟨[85883, 3], [27131, 87813], .contexts [
        ⟨69363, false, false, [], []⟩,
        ⟨69356, false, false, [], []⟩
      ]⟩,
    ⟨[85883, 5], [45061, 84511], .contexts [
        ⟨110064, true, false, [45058], [5]⟩,
        ⟨28, false, false, [45058, 84511], []⟩,
        ⟨110065, true, false, [], [84511]⟩
      ]⟩,
    ⟨[85883, 7], [45057, 84999], .contexts [
        ⟨110061, true, false, [45054], [7]⟩,
        ⟨38, false, false, [45054, 84999], []⟩,
        ⟨110062, true, false, [], [84999]⟩
      ]⟩,
    ⟨[85883, 9], [35829, 38557, 91269], .contexts [
        ⟨98328, true, false, [35826], [9]⟩,
        ⟨46, false, false, [35826, 96551], []⟩,
        ⟨98329, true, false, [], [96551]⟩,
        ⟨103530, false, false, [35829], []⟩
      ]⟩,
    ⟨[85883, 11], [85881], .contexts [
        ⟨34129, false, false, [], []⟩,
        ⟨34371, false, false, [], []⟩
      ]⟩,
    ⟨[85883, 13], [27101, 88475], .contexts [
        ⟨69325, false, false, [], []⟩,
        ⟨69322, false, false, [], []⟩
      ]⟩,
    ⟨[85883, 15], [53887, 87379], .contexts [
        ⟨120052, false, false, [], []⟩,
        ⟨147306, false, false, [], []⟩
      ]⟩,
    ⟨[85889, 1], [85891], .contexts [
        ⟨34143, false, false, [], []⟩,
        ⟨34365, false, false, [], []⟩
      ]⟩,
    ⟨[85889, 3], [27101, 58865, 83067], .contexts [
        ⟨69391, false, false, [], []⟩,
        ⟨125917, false, false, [27101], []⟩
      ]⟩,
    ⟨[85889, 5], [27143, 27151, 85897], .contexts [
        ⟨69392, false, false, [], []⟩,
        ⟨100167, false, false, [27143], []⟩
      ]⟩,
    ⟨[85889, 7], [73695, 96947], .contexts [
        ⟨144022, true, false, [73692], [7]⟩,
        ⟨38, false, false, [73692, 96947], []⟩,
        ⟨143989, true, false, [], [96947]⟩
      ]⟩,
    ⟨[85889, 9], [36429, 55817, 65377, 90789], .contexts [
        ⟨100160, false, false, [], []⟩,
        ⟨160238, false, false, [36429], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2528. -/
def y322TCIndexRaw2528 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85889, 11], [72193, 96833], .contexts [
        ⟨141744, true, false, [72190], [11]⟩,
        ⟨53, false, false, [72190, 96833], []⟩,
        ⟨141716, true, false, [], [96833]⟩
      ]⟩,
    ⟨[85889, 13], [37011, 37057, 92913], .contexts [
        ⟨101324, false, false, [], []⟩,
        ⟨101557, false, false, [37011], []⟩
      ]⟩,
    ⟨[85889, 15], [51831, 83073], .contexts [
        ⟨34141, false, false, [], []⟩,
        ⟨118855, false, false, [], []⟩
      ]⟩,
    ⟨[85891, 1], [85889], .contexts [
        ⟨34145, false, false, [], []⟩,
        ⟨34366, false, false, [], []⟩
      ]⟩,
    ⟨[85893], [27147, 85891], .contexts [
        ⟨69395, false, false, [], []⟩
      ]⟩,
    ⟨[85891, 3], [27147, 85891], .contexts [
        ⟨34147, false, false, [], []⟩,
        ⟨161796, false, false, [], []⟩
      ]⟩,
    ⟨[85891, 5], [27143, 27151, 85895], .contexts [
        ⟨69389, false, false, [], []⟩,
        ⟨69405, false, false, [27143], []⟩
      ]⟩,
    ⟨[85891, 7], [73695, 96945], .contexts [
        ⟨143988, true, false, [73692], [7]⟩,
        ⟨38, false, false, [73692, 96945], []⟩,
        ⟨143989, true, false, [], [96945]⟩
      ]⟩,
    ⟨[85891, 9], [32801, 44195, 86137], .contexts [
        ⟨89316, true, false, [32798], [9]⟩,
        ⟨46, false, false, [32798, 95259], []⟩,
        ⟨89317, true, false, [], [95259]⟩,
        ⟨108983, false, false, [32801], []⟩
      ]⟩,
    ⟨[85891, 11], [72193, 96831], .contexts [
        ⟨141715, true, false, [72190], [11]⟩,
        ⟨53, false, false, [72190, 96831], []⟩,
        ⟨141716, true, false, [], [96831]⟩
      ]⟩,
    ⟨[85891, 13], [27141, 85891], .contexts [
        ⟨69386, false, false, [], []⟩
      ]⟩,
    ⟨[85891, 15], [27101, 88479], .contexts [
        ⟨69380, false, false, [], []⟩,
        ⟨69349, false, false, [], []⟩
      ]⟩,
    ⟨[85895, 1], [85897], .contexts [
        ⟨34154, false, false, [], []⟩,
        ⟨34361, false, false, [], []⟩
      ]⟩,
    ⟨[85895, 3], [31361, 61303, 84533], .contexts [
        ⟨84372, false, false, [], []⟩,
        ⟨128826, false, false, [31361], []⟩
      ]⟩,
    ⟨[85895, 5], [27147, 85891], .contexts [
        ⟨34152, false, false, [], []⟩,
        ⟨161796, false, false, [], []⟩
      ]⟩,
    ⟨[85895, 7], [33931, 44351, 84259], .contexts [
        ⟨92576, true, false, [33928], [7]⟩,
        ⟨38, false, false, [33928, 95527], []⟩,
        ⟨92577, true, false, [], [95527]⟩,
        ⟨109212, false, false, [33931], []⟩
      ]⟩,
    ⟨[85895, 9], [32783, 44185, 86135], .contexts [
        ⟨89215, false, false, [], []⟩,
        ⟨108970, false, false, [32783], []⟩
      ]⟩,
    ⟨[85895, 11], [51855, 84521], .contexts [
        ⟨117717, false, false, [], []⟩,
        ⟨125937, false, false, [], []⟩
      ]⟩,
    ⟨[85895, 13], [27155, 85895], .contexts [
        ⟨69410, false, false, [], []⟩,
        ⟨125939, false, false, [], []⟩
      ]⟩,
    ⟨[85895, 15], [27149, 44165, 83077], .contexts [
        ⟨69400, true, false, [27150], [15]⟩,
        ⟨68798, false, false, [27150], []⟩,
        ⟨68789, false, false, [27150], []⟩,
        ⟨69404, true, false, [], [91949]⟩,
        ⟨109149, false, false, [27149], []⟩
      ]⟩,
    ⟨[85897, 1], [85895], .contexts [
        ⟨34156, false, false, [], []⟩,
        ⟨34363, false, false, [], []⟩
      ]⟩,
    ⟨[85897, 3], [27149, 54555, 82941], .contexts [
        ⟨69415, false, false, [], []⟩,
        ⟨120887, false, false, [27149], []⟩
      ]⟩,
    ⟨[85897, 5], [27159, 85889], .contexts [
        ⟨69412, true, false, [27150], [5]⟩,
        ⟨68815, false, false, [27150], []⟩,
        ⟨69390, false, false, [27150, 26919], []⟩,
        ⟨69375, false, false, [27150, 26919], []⟩,
        ⟨69401, true, false, [], [26919, 27119, 85889]⟩,
        ⟨69413, true, false, [], [27119, 85889]⟩,
        ⟨69414, true, false, [], [85889]⟩
      ]⟩,
    ⟨[85897, 7], [33931, 44323, 84261], .contexts [
        ⟨92591, true, false, [33928], [7]⟩,
        ⟨38, false, false, [33928, 95529], []⟩,
        ⟨92577, true, false, [], [95529]⟩,
        ⟨109173, false, false, [33931], []⟩
      ]⟩,
    ⟨[85897, 9], [85899], .contexts [
        ⟨34158, false, false, [], []⟩,
        ⟨34359, false, false, [], []⟩
      ]⟩,
    ⟨[85897, 11], [52319, 84519], .contexts [
        ⟨118306, false, false, [], []⟩
      ]⟩,
    ⟨[85897, 13], [37065, 92911], .contexts [
        ⟨101450, false, false, [], []⟩,
        ⟨101564, false, false, [], []⟩
      ]⟩,
    ⟨[85897, 15], [51851, 83075], .contexts [
        ⟨117708, true, false, [44168], [15]⟩,
        ⟨1, false, false, [44168, 83075], []⟩,
        ⟨117709, true, false, [], [83075]⟩
      ]⟩,
    ⟨[85899, 1], [36839, 54129, 91581], .contexts [
        ⟨101059, false, false, [], []⟩,
        ⟨120369, false, false, [36839], []⟩
      ]⟩,
    ⟨[85899, 3], [36839, 54063, 83439], .contexts [
        ⟨101060, false, false, [], []⟩,
        ⟨120884, false, false, [36839], []⟩
      ]⟩,
    ⟨[85899, 5], [36443, 55817, 65377, 90789], .contexts [
        ⟨100176, false, false, [], []⟩,
        ⟨160238, false, false, [36443], []⟩
      ]⟩,
    ⟨[85899, 7], [52327, 84263], .contexts [
        ⟨118318, true, false, [44324], [7]⟩,
        ⟨38, false, false, [44324, 84263], []⟩,
        ⟨118319, true, false, [], [84263]⟩
      ]⟩,
    ⟨[85899, 9], [85897], .contexts [
        ⟨34160, false, false, [], []⟩,
        ⟨34361, false, false, [], []⟩
      ]⟩,
    ⟨[85899, 11], [85901], .contexts [
        ⟨34162, false, false, [], []⟩,
        ⟨34357, false, false, [], []⟩
      ]⟩,
    ⟨[87235], [54113, 60089, 85047], .contexts [
        ⟨120351, false, false, [], []⟩,
        ⟨127984, false, false, [], []⟩
      ]⟩,
    ⟨[85899, 13], [37821, 54113, 60089, 85047], .contexts [
        ⟨102568, false, false, [], []⟩,
        ⟨161826, false, false, [37821], []⟩
      ]⟩,
    ⟨[85899, 15], [58885, 89377], .contexts [
        ⟨125935, false, false, [], []⟩
      ]⟩,
    ⟨[85901, 1], [63781, 85779], .contexts [
        ⟨34166, false, false, [], []⟩,
        ⟨131873, false, false, [], []⟩
      ]⟩,
    ⟨[85901, 3], [59621, 59827, 63889, 83717], .contexts [
        ⟨126867, false, false, [], []⟩,
        ⟨153529, false, false, [59621], []⟩
      ]⟩,
    ⟨[85901, 5], [36447, 55099, 86145], .contexts [
        ⟨100184, false, false, [], []⟩,
        ⟨121526, false, false, [36447], []⟩
      ]⟩,
    ⟨[85901, 7], [36453, 44393, 84265], .contexts [
        ⟨100206, false, false, [], []⟩,
        ⟨109269, false, false, [36453], []⟩
      ]⟩,
    ⟨[85901, 9], [36465, 85629], .contexts [
        ⟨100228, false, false, [], []⟩,
        ⟨119126, false, false, [], []⟩
      ]⟩,
    ⟨[85901, 11], [85899], .contexts [
        ⟨34164, false, false, [], []⟩,
        ⟨34359, false, false, [], []⟩
      ]⟩,
    ⟨[85901, 13], [44627, 87243], .contexts [
        ⟨109548, false, false, [], []⟩,
        ⟨126888, false, false, [], []⟩
      ]⟩,
    ⟨[85901, 15], [44627, 55033, 63819, 85783], .contexts [
        ⟨109549, false, false, [], []⟩,
        ⟨157849, false, false, [44627], []⟩
      ]⟩,
    ⟨[85907, 1], [52509, 84415], .contexts [
        ⟨34178, false, false, [], []⟩,
        ⟨118545, false, false, [], []⟩
      ]⟩,
    ⟨[85907, 3], [45101, 96345], .contexts [
        ⟨110135, false, false, [], []⟩,
        ⟨120173, false, false, [], []⟩
      ]⟩,
    ⟨[85907, 5], [36841, 52541, 57977, 83871], .contexts [
        ⟨100983, true, false, [36842], [5]⟩,
        ⟨28, false, false, [36842, 92927], []⟩,
        ⟨100984, true, false, [], [92927]⟩,
        ⟨157726, false, false, [36841], []⟩
      ]⟩,
    ⟨[85907, 7], [52709, 84271], .contexts [
        ⟨118751, true, false, [52706], [7]⟩,
        ⟨38, false, false, [52706, 84271], []⟩,
        ⟨118752, true, false, [], [84271]⟩
      ]⟩,
    ⟨[85907, 9], [36501, 84993], .contexts [
        ⟨100295, false, false, [], []⟩,
        ⟨100319, false, false, [], []⟩
      ]⟩,
    ⟨[85907, 11], [46451, 85807], .contexts [
        ⟨111776, false, false, [], []⟩
      ]⟩,
    ⟨[85907, 13], [30733, 36769, 89277], .contexts [
        ⟨81436, false, false, [], []⟩,
        ⟨100818, false, false, [30733], []⟩
      ]⟩,
    ⟨[85907, 15], [63781, 85777], .contexts [
        ⟨34176, false, false, [], []⟩,
        ⟨131861, false, false, [], []⟩
      ]⟩,
    ⟨[85913, 1], [54449, 84173], .contexts [
        ⟨34190, false, false, [], []⟩,
        ⟨120964, false, false, [], []⟩
      ]⟩,
    ⟨[85913, 3], [52519, 54183, 85643], .contexts [
        ⟨118534, false, false, [], []⟩,
        ⟨126324, false, false, [52519], []⟩
      ]⟩,
    ⟨[85913, 5], [52509, 84413], .contexts [
        ⟨34188, false, false, [], []⟩,
        ⟨118528, false, false, [], []⟩
      ]⟩,
    ⟨[85913, 7], [30323, 68885, 86175], .contexts [
        ⟨79904, false, false, [], []⟩,
        ⟨137476, false, false, [30323], []⟩
      ]⟩,
    ⟨[85913, 9], [36515, 92295], .contexts [
        ⟨100385, false, false, [], []⟩,
        ⟨100380, false, false, [], []⟩
      ]⟩,
    ⟨[85913, 11], [54655, 84177], .contexts [
        ⟨121010, false, false, [], []⟩,
        ⟨126684, false, false, [], []⟩
      ]⟩,
    ⟨[85913, 13], [36359, 89067], .contexts [
        ⟨99948, false, false, [], []⟩,
        ⟨101217, false, false, [], []⟩
      ]⟩,
    ⟨[85913, 15], [30733, 36365, 45191, 64771, 86025], .contexts [
        ⟨81389, false, false, [], []⟩,
        ⟨157455, false, false, [30733], []⟩
      ]⟩,
    ⟨[85921, 1], [54501, 83763], .contexts [
        ⟨34204, false, false, [], []⟩,
        ⟨120833, false, false, [], []⟩
      ]⟩,
    ⟨[85921, 3], [58815, 71177, 90911], .contexts [
        ⟨125859, false, false, [], []⟩,
        ⟨140014, false, false, [58815], []⟩
      ]⟩,
    ⟨[85921, 5], [45431, 87783], .contexts [
        ⟨110548, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2529. -/
def y322TCIndexRaw2529 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85921, 7], [30299, 70135, 90055], .contexts [
        ⟨79801, false, false, [], []⟩,
        ⟨138822, false, false, [30299], []⟩
      ]⟩,
    ⟨[85921, 9], [22481, 85921], .contexts [
        ⟨49130, false, false, [], []⟩
      ]⟩,
    ⟨[85921, 11], [36515, 54435, 84169], .contexts [
        ⟨100416, false, false, [], []⟩,
        ⟨120755, false, false, [36515], []⟩
      ]⟩,
    ⟨[85921, 13], [30301, 85921], .contexts [
        ⟨34206, false, false, [], []⟩,
        ⟨79810, false, false, [], []⟩
      ]⟩,
    ⟨[85921, 15], [30303, 54479, 83767], .contexts [
        ⟨79809, false, false, [], []⟩,
        ⟨120804, false, false, [30303], []⟩
      ]⟩,
    ⟨[85929, 1], [32955, 69645, 87893], .contexts [
        ⟨89828, false, false, [], []⟩,
        ⟨138248, false, false, [32955], []⟩
      ]⟩,
    ⟨[85929, 3], [54479, 83765], .contexts [
        ⟨34220, false, false, [], []⟩,
        ⟨120821, false, false, [], []⟩
      ]⟩,
    ⟨[85929, 5], [40645, 85657], .contexts [
        ⟨34222, false, false, [], []⟩,
        ⟨105678, false, false, [], []⟩
      ]⟩,
    ⟨[85929, 7], [23451, 83891], .contexts [
        ⟨53482, false, false, [], []⟩,
        ⟨55438, false, false, [], []⟩
      ]⟩,
    ⟨[85929, 9], [18943, 50655, 84811], .contexts [
        ⟨35919, false, false, [], []⟩,
        ⟨116321, false, false, [18943], []⟩
      ]⟩,
    ⟨[85929, 11], [32955, 95357], .contexts [
        ⟨89827, false, false, [], []⟩,
        ⟨89829, false, false, [], []⟩
      ]⟩,
    ⟨[85929, 13], [23927, 55585, 86473], .contexts [
        ⟨55402, false, false, [], []⟩,
        ⟨122131, false, false, [23927], []⟩
      ]⟩,
    ⟨[85929, 15], [55603, 86477], .contexts [
        ⟨122138, false, false, [], []⟩
      ]⟩,
    ⟨[85935, 1], [18943, 86213], .contexts [
        ⟨35887, false, false, [], []⟩,
        ⟨35883, false, false, [], []⟩
      ]⟩,
    ⟨[85935, 3], [21149, 85313], .contexts [
        ⟨44315, true, false, [21146], [3]⟩,
        ⟨20, false, false, [21146, 85313], []⟩,
        ⟨44316, true, false, [], [85313]⟩
      ]⟩,
    ⟨[85935, 5], [26723, 91935], .contexts [
        ⟨68261, false, false, [], []⟩,
        ⟨68283, false, false, [], []⟩
      ]⟩,
    ⟨[85935, 7], [18949, 85503], .contexts [
        ⟨35898, false, false, [], []⟩,
        ⟨35893, false, false, [], []⟩
      ]⟩,
    ⟨[85935, 9], [39913, 84463], .contexts [
        ⟨34231, false, false, [], []⟩,
        ⟨105666, false, false, [], []⟩
      ]⟩,
    ⟨[85935, 11], [27079, 85877], .contexts [
        ⟨34233, false, false, [], []⟩,
        ⟨69277, false, false, [], []⟩
      ]⟩,
    ⟨[85935, 13], [18947, 85495], .contexts [
        ⟨35878, false, false, [], []⟩,
        ⟨35889, false, false, [], []⟩
      ]⟩,
    ⟨[85935, 15], [39911, 86309], .contexts [
        ⟨104996, true, false, [39908], [15]⟩,
        ⟨36298, false, false, [39908], []⟩,
        ⟨36358, false, false, [39908], []⟩,
        ⟨104997, true, false, [], [86309]⟩,
        ⟨104997, true, false, [], [86309]⟩,
        ⟨104995, true, false, [], [86309]⟩
      ]⟩,
    ⟨[85941, 1], [18663, 85945], .contexts [
        ⟨34515, false, false, [], []⟩,
        ⟨143028, false, false, [], []⟩
      ]⟩,
    ⟨[85941, 3], [21817, 87807], .contexts [
        ⟨46525, false, false, [], []⟩,
        ⟨50748, false, false, [], []⟩
      ]⟩,
    ⟨[85941, 5], [26921, 91941], .contexts [
        ⟨68703, true, false, [26918], [5]⟩,
        ⟨28, false, false, [26918, 91941], []⟩,
        ⟨68704, true, false, [], [91941]⟩
      ]⟩,
    ⟨[85941, 7], [35093, 37487, 96075], .contexts [
        ⟨96124, false, false, [], []⟩,
        ⟨102270, false, false, [35093], []⟩
      ]⟩,
    ⟨[85941, 9], [88473], .contexts [
        ⟨50743, false, false, [], []⟩,
        ⟨50745, false, false, [], []⟩
      ]⟩,
    ⟨[85941, 11], [19873, 86911], .contexts [
        ⟨40377, false, false, [], []⟩,
        ⟨40415, false, false, [], []⟩
      ]⟩,
    ⟨[85941, 13], [27079, 85879], .contexts [
        ⟨34243, false, false, [], []⟩,
        ⟨69285, false, false, [], []⟩
      ]⟩,
    ⟨[85943], [18661, 85941], .contexts [
        ⟨35852, false, false, [], []⟩
      ]⟩,
    ⟨[85941, 15], [18661, 85941], .contexts [
        ⟨34245, false, false, [], []⟩,
        ⟨161884, false, false, [], []⟩
      ]⟩,
    ⟨[85945, 1], [18661, 85941], .contexts [
        ⟨34250, false, false, [], []⟩,
        ⟨161884, false, false, [], []⟩
      ]⟩,
    ⟨[85945, 3], [18653, 83201], .contexts [
        ⟨34252, false, false, [], []⟩,
        ⟨69053, false, false, [], []⟩
      ]⟩,
    ⟨[85945, 5], [22875, 88471], .contexts [
        ⟨50733, false, false, [], []⟩
      ]⟩,
    ⟨[85945, 7], [25379, 90615], .contexts [
        ⟨62101, true, false, [25376], [7]⟩,
        ⟨38, false, false, [25376, 90615], []⟩,
        ⟨62102, true, false, [], [90615]⟩
      ]⟩,
    ⟨[85945, 9], [24155, 38401, 89341], .contexts [
        ⟨56656, false, false, [], []⟩,
        ⟨103371, false, false, [24155], []⟩
      ]⟩,
    ⟨[85945, 11], [24785, 90225], .contexts [
        ⟨59718, true, false, [24782], [11]⟩,
        ⟨53, false, false, [24782, 90225], []⟩,
        ⟨59719, true, false, [], [90225]⟩
      ]⟩,
    ⟨[85945, 13], [18653, 20761, 85257], .contexts [
        ⟨34503, true, false, [18654], [13]⟩,
        ⟨59, false, false, [18654, 85613], []⟩,
        ⟨34494, true, false, [], [85613]⟩,
        ⟨42682, false, false, [18653], []⟩
      ]⟩,
    ⟨[85945, 15], [18661, 85945], .contexts [
        ⟨34508, false, false, [], []⟩,
        ⟨34509, false, false, [], []⟩
      ]⟩,
    ⟨[85971, 1], [18617, 85971], .contexts [
        ⟨34452, false, false, [], []⟩,
        ⟨86841, false, false, [], []⟩
      ]⟩,
    ⟨[85971, 3], [90749], .contexts [
        ⟨62769, false, false, [], []⟩,
        ⟨62771, false, false, [], []⟩
      ]⟩,
    ⟨[85971, 5], [18621, 83163], .contexts [
        ⟨34455, false, false, [], []⟩,
        ⟨62774, false, false, [], []⟩
      ]⟩,
    ⟨[85971, 7], [18625, 85971], .contexts [
        ⟨34460, false, false, [], []⟩,
        ⟨62783, false, false, [], []⟩
      ]⟩,
    ⟨[85971, 9], [18627, 84365], .contexts [
        ⟨34290, false, false, [], []⟩,
        ⟨34462, false, false, [], []⟩
      ]⟩,
    ⟨[85971, 11], [18611, 85971], .contexts [
        ⟨34292, false, false, [], []⟩,
        ⟨34456, false, false, [], []⟩
      ]⟩,
    ⟨[85971, 13], [18619, 83931], .contexts [
        ⟨34447, true, false, [18610], [13]⟩,
        ⟨34419, false, false, [18610], []⟩,
        ⟨34423, false, false, [18610], []⟩,
        ⟨34450, true, false, [], [18587, 83931]⟩,
        ⟨34453, true, false, [], [83931]⟩
      ]⟩,
    ⟨[85971, 15], [20045, 87333], .contexts [
        ⟨41328, false, false, [], []⟩,
        ⟨62797, false, false, [], []⟩
      ]⟩,
    ⟨[85981, 1], [16317, 85981], .contexts [
        ⟨34599, false, false, [], []⟩,
        ⟨34595, false, false, [], []⟩
      ]⟩,
    ⟨[85981, 3], [18673, 85981], .contexts [
        ⟨34604, false, false, [], []⟩,
        ⟨34601, false, false, [], []⟩
      ]⟩,
    ⟨[85981, 5], [19225, 84589], .contexts [
        ⟨37574, false, false, [], []⟩,
        ⟨42382, false, false, [], []⟩
      ]⟩,
    ⟨[85981, 7], [75497, 97199], .contexts [
        ⟨147037, false, false, [], []⟩
      ]⟩,
    ⟨[85981, 9], [20541, 85243], .contexts [
        ⟨34591, false, false, [], []⟩,
        ⟨42191, false, false, [], []⟩
      ]⟩,
    ⟨[85981, 11], [20539, 85981], .contexts [
        ⟨34608, false, false, [], []⟩,
        ⟨42182, false, false, [], []⟩
      ]⟩,
    ⟨[85981, 13], [20537, 47649, 84029], .contexts [
        ⟨42187, false, false, [], []⟩,
        ⟨113042, false, false, [20537], []⟩
      ]⟩,
    ⟨[85981, 15], [16319, 85981], .contexts [
        ⟨34606, false, false, [], []⟩,
        ⟨34605, false, false, [], []⟩
      ]⟩,
    ⟨[85991, 1], [18673, 85991], .contexts [
        ⟨34682, false, false, [], []⟩,
        ⟨34677, false, false, [], []⟩
      ]⟩,
    ⟨[85991, 3], [20737, 84733], .contexts [
        ⟨34670, false, false, [], []⟩,
        ⟨145062, false, false, [], []⟩
      ]⟩,
    ⟨[85993], [20797, 85991], .contexts [
        ⟨42732, false, false, [], []⟩
      ]⟩,
    ⟨[85991, 5], [20797, 85991], .contexts [
        ⟨34684, false, false, [], []⟩,
        ⟨161912, false, false, [], []⟩
      ]⟩,
    ⟨[85991, 7], [28847, 47827, 92403], .contexts [
        ⟨74942, false, false, [], []⟩,
        ⟨113245, false, false, [28847], []⟩
      ]⟩,
    ⟨[85991, 9], [20795, 85995], .contexts [
        ⟨42737, false, false, [], []⟩,
        ⟨42971, false, false, [], []⟩
      ]⟩,
    ⟨[85991, 11], [20883, 85991], .contexts [
        ⟨42959, false, false, [], []⟩,
        ⟨42980, false, false, [], []⟩
      ]⟩,
    ⟨[85991, 13], [74293, 97001], .contexts [
        ⟨144994, false, false, [], []⟩,
        ⟨148352, false, false, [], []⟩
      ]⟩,
    ⟨[85991, 15], [97265], .contexts [
        ⟨148334, false, false, [], []⟩,
        ⟨148335, false, false, [], []⟩
      ]⟩,
    ⟨[85995, 1], [28661, 91759], .contexts [
        ⟨74530, false, false, [], []⟩,
        ⟨74595, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2530. -/
def y322TCIndexRaw2530 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[85995, 3], [20879, 84735], .contexts [
        ⟨42946, false, false, [], []⟩,
        ⟨74603, false, false, [], []⟩
      ]⟩,
    ⟨[85995, 5], [20795, 85995], .contexts [
        ⟨42975, false, false, [], []⟩,
        ⟨42971, false, false, [], []⟩
      ]⟩,
    ⟨[85995, 7], [28795, 68331, 88727], .contexts [
        ⟨74806, false, false, [], []⟩,
        ⟨137006, false, false, [28795], []⟩
      ]⟩,
    ⟨[85995, 9], [20797, 85991], .contexts [
        ⟨34693, false, false, [], []⟩,
        ⟨161912, false, false, [], []⟩
      ]⟩,
    ⟨[85995, 11], [85997], .contexts [
        ⟨34695, false, false, [], []⟩,
        ⟨34972, false, false, [], []⟩
      ]⟩,
    ⟨[85995, 13], [28791, 90985], .contexts [
        ⟨74800, false, false, [], []⟩
      ]⟩,
    ⟨[85995, 15], [28791, 90989], .contexts [
        ⟨74801, false, false, [], []⟩,
        ⟨146249, false, false, [], []⟩
      ]⟩,
    ⟨[85997, 1], [85999], .contexts [
        ⟨34699, false, false, [], []⟩,
        ⟨34971, false, false, [], []⟩
      ]⟩,
    ⟨[85997, 3], [20879, 84737], .contexts [
        ⟨43188, false, false, [], []⟩,
        ⟨146224, false, false, [], []⟩
      ]⟩,
    ⟨[85997, 5], [20797, 85997], .contexts [
        ⟨43203, false, false, [], []⟩,
        ⟨43349, false, false, [], []⟩
      ]⟩,
    ⟨[85997, 7], [28649, 47367, 83983], .contexts [
        ⟨74514, false, false, [], []⟩,
        ⟨112752, false, false, [28649], []⟩
      ]⟩,
    ⟨[85997, 9], [20889, 85997], .contexts [
        ⟨42988, false, false, [], []⟩,
        ⟨146243, false, false, [], []⟩
      ]⟩,
    ⟨[85997, 11], [85995], .contexts [
        ⟨34697, false, false, [], []⟩,
        ⟨34974, false, false, [], []⟩
      ]⟩,
    ⟨[85997, 13], [75075, 97151], .contexts [
        ⟨146215, false, false, [], []⟩,
        ⟨146254, false, false, [], []⟩
      ]⟩,
    ⟨[85997, 15], [97153], .contexts [
        ⟨146219, false, false, [], []⟩,
        ⟨146221, false, false, [], []⟩
      ]⟩,
    ⟨[85999, 1], [85997], .contexts [
        ⟨34701, false, false, [], []⟩,
        ⟨34972, false, false, [], []⟩
      ]⟩,
    ⟨[91747], [45599, 49185, 89807], .contexts [
        ⟨110747, false, false, [], []⟩,
        ⟨119091, false, false, [], []⟩
      ]⟩,
    ⟨[85999, 3], [28667, 45599, 49185, 89807], .contexts [
        ⟨74544, false, false, [], []⟩,
        ⟨161936, false, false, [28667], []⟩
      ]⟩,
    ⟨[85999, 5], [20795, 85999], .contexts [
        ⟨43357, false, false, [], []⟩,
        ⟨43450, false, false, [], []⟩
      ]⟩,
    ⟨[85999, 7], [31939, 94771], .contexts [
        ⟨86431, false, false, [], []⟩,
        ⟨132261, false, false, [], []⟩
      ]⟩,
    ⟨[85999, 9], [28655, 92059], .contexts [
        ⟨74536, false, false, [], []⟩,
        ⟨74628, false, false, [], []⟩
      ]⟩,
    ⟨[85999, 11], [28661, 91759], .contexts [
        ⟨74534, false, false, [], []⟩,
        ⟨74595, false, false, [], []⟩
      ]⟩,
    ⟨[85999, 13], [86001], .contexts [
        ⟨34703, false, false, [], []⟩,
        ⟨34969, false, false, [], []⟩
      ]⟩,
    ⟨[85999, 15], [97155], .contexts [
        ⟨146293, false, false, [], []⟩,
        ⟨146263, false, false, [], []⟩
      ]⟩,
    ⟨[86001, 1], [56331, 58437, 93889], .contexts [
        ⟨123006, false, false, [], []⟩,
        ⟨130296, false, false, [56331], []⟩
      ]⟩,
    ⟨[86001, 3], [55203, 89809], .contexts [
        ⟨121631, false, false, [], []⟩,
        ⟨129571, false, false, [], []⟩
      ]⟩,
    ⟨[86001, 5], [20797, 86001], .contexts [
        ⟨43457, false, false, [], []⟩,
        ⟨43533, false, false, [], []⟩
      ]⟩,
    ⟨[86001, 7], [59211, 87735], .contexts [
        ⟨126361, false, false, [], []⟩,
        ⟨130437, false, false, [], []⟩
      ]⟩,
    ⟨[86001, 9], [28741, 92063], .contexts [
        ⟨74664, false, false, [], []⟩,
        ⟨74738, false, false, [], []⟩
      ]⟩,
    ⟨[86001, 11], [28661, 91761], .contexts [
        ⟨74624, false, false, [], []⟩,
        ⟨74620, false, false, [], []⟩
      ]⟩,
    ⟨[86001, 13], [85999], .contexts [
        ⟨34705, false, false, [], []⟩,
        ⟨34971, false, false, [], []⟩
      ]⟩,
    ⟨[86001, 15], [86003], .contexts [
        ⟨34707, false, false, [], []⟩,
        ⟨34968, false, false, [], []⟩
      ]⟩,
    ⟨[86003, 1], [86005], .contexts [
        ⟨34711, false, false, [], []⟩,
        ⟨34966, false, false, [], []⟩
      ]⟩,
    ⟨[86003, 3], [55203, 89811], .contexts [
        ⟨129577, false, false, [], []⟩,
        ⟨129573, false, false, [], []⟩
      ]⟩,
    ⟨[86003, 5], [20795, 86003], .contexts [
        ⟨43540, false, false, [], []⟩,
        ⟨43602, false, false, [], []⟩
      ]⟩,
    ⟨[86003, 7], [71871, 96853], .contexts [
        ⟨142105, true, false, [71868], [7]⟩,
        ⟨38, false, false, [71868, 96853], []⟩,
        ⟨140984, true, false, [], [96853]⟩
      ]⟩,
    ⟨[86003, 9], [28741, 92065], .contexts [
        ⟨74766, false, false, [], []⟩,
        ⟨74906, false, false, [], []⟩
      ]⟩,
    ⟨[86003, 11], [28661, 28805, 90083], .contexts [
        ⟨74747, false, false, [], []⟩,
        ⟨74831, false, false, [28661], []⟩
      ]⟩,
    ⟨[86003, 13], [62421, 95761], .contexts [
        ⟨130182, true, false, [62418], [13]⟩,
        ⟨59, false, false, [62418, 95761], []⟩,
        ⟨130183, true, false, [], [95761]⟩
      ]⟩,
    ⟨[86003, 15], [86001], .contexts [
        ⟨34709, false, false, [], []⟩,
        ⟨34969, false, false, [], []⟩
      ]⟩,
    ⟨[86005, 1], [86003], .contexts [
        ⟨34713, false, false, [], []⟩,
        ⟨34968, false, false, [], []⟩
      ]⟩,
    ⟨[86005, 3], [86007], .contexts [
        ⟨34715, false, false, [], []⟩,
        ⟨34965, false, false, [], []⟩
      ]⟩,
    ⟨[86005, 5], [20797, 86005], .contexts [
        ⟨43607, false, false, [], []⟩,
        ⟨43650, false, false, [], []⟩
      ]⟩,
    ⟨[86005, 7], [71871, 96791], .contexts [
        ⟨140983, true, false, [71868], [7]⟩,
        ⟨38, false, false, [71868, 96791], []⟩,
        ⟨140984, true, false, [], [96791]⟩
      ]⟩,
    ⟨[86005, 9], [28831, 90077], .contexts [
        ⟨74892, false, false, [], []⟩,
        ⟨74908, false, false, [], []⟩
      ]⟩,
    ⟨[86005, 11], [28831, 90081], .contexts [
        ⟨74890, false, false, [], []⟩
      ]⟩,
    ⟨[86005, 13], [28835, 86005], .contexts [
        ⟨74897, false, false, [], []⟩,
        ⟨75026, false, false, [], []⟩
      ]⟩,
    ⟨[86005, 15], [62563, 93889], .contexts [
        ⟨130384, true, false, [62564], [15]⟩,
        ⟨81699, false, false, [62564], []⟩,
        ⟨81788, false, false, [62564], []⟩,
        ⟨130385, true, false, [], [93889]⟩,
        ⟨130385, true, false, [], [93889]⟩,
        ⟨130383, false, true, [], [93889]⟩
      ]⟩,
    ⟨[86007, 1], [62531, 89815], .contexts [
        ⟨130339, false, false, [], []⟩,
        ⟨131511, false, false, [], []⟩
      ]⟩,
    ⟨[86007, 3], [86005], .contexts [
        ⟨34717, false, false, [], []⟩,
        ⟨34966, false, false, [], []⟩
      ]⟩,
    ⟨[86007, 5], [86009], .contexts [
        ⟨34719, false, false, [], []⟩,
        ⟨34963, false, false, [], []⟩
      ]⟩,
    ⟨[86007, 7], [62529, 86453], .contexts [
        ⟨130330, true, false, [62522], [7]⟩,
        ⟨96968, true, false, [62522, 35312], [7]⟩,
        ⟨38, false, false, [62522, 35312, 96141], []⟩,
        ⟨96918, true, false, [62522], [96141]⟩,
        ⟨102213, false, false, [62522, 35311], []⟩,
        ⟨130335, false, false, [62522, 35311], []⟩,
        ⟨120562, true, false, [62522, 35311], [86453]⟩,
        ⟨130328, true, false, [], [35311, 54283, 86453]⟩,
        ⟨130336, true, false, [], [54283, 86453]⟩,
        ⟨130337, true, false, [], [86453]⟩
      ]⟩,
    ⟨[86007, 9], [62525, 66243, 83429], .contexts [
        ⟨130332, false, false, [], []⟩,
        ⟨134606, false, false, [62525], []⟩
      ]⟩,
    ⟨[86007, 11], [28857, 69317, 88255], .contexts [
        ⟨74966, false, false, [], []⟩,
        ⟨137939, false, false, [28857], []⟩
      ]⟩,
    ⟨[86007, 13], [28835, 86007], .contexts [
        ⟨75031, false, false, [], []⟩,
        ⟨75028, false, false, [], []⟩
      ]⟩,
    ⟨[86007, 15], [65041, 94005], .contexts [
        ⟨133243, false, false, [], []⟩,
        ⟨134137, false, false, [], []⟩
      ]⟩,
    ⟨[86009, 1], [86011], .contexts [
        ⟨34723, false, false, [], []⟩,
        ⟨34961, false, false, [], []⟩
      ]⟩,
    ⟨[86009, 3], [20795, 86009], .contexts [
        ⟨43655, false, false, [], []⟩
      ]⟩,
    ⟨[86009, 5], [86007], .contexts [
        ⟨34721, false, false, [], []⟩,
        ⟨34965, false, false, [], []⟩
      ]⟩,
    ⟨[86009, 7], [62539, 83397], .contexts [
        ⟨130342, true, false, [62534], [7]⟩,
        ⟨62038, false, false, [62534], []⟩,
        ⟨115030, false, false, [62534, 25351], []⟩,
        ⟨130351, true, false, [], [49571, 83397]⟩,
        ⟨130352, true, false, [], [83397]⟩
      ]⟩,
    ⟨[86009, 9], [62533, 66219, 83425], .contexts [
        ⟨130347, false, false, [], []⟩,
        ⟨134586, false, false, [62533], []⟩
      ]⟩,
    ⟨[86009, 11], [28857, 91769], .contexts [
        ⟨75064, false, false, [], []⟩,
        ⟨75056, false, false, [], []⟩
      ]⟩,
    ⟨[86009, 13], [28931, 86009], .contexts [
        ⟨34719, true, false, [], [13]⟩,
        ⟨75157, true, false, [28834], [5, 13]⟩,
        ⟨1136, false, false, [28834, 86007], []⟩,
        ⟨75058, false, false, [28834], []⟩,
        ⟨75057, false, false, [28834], []⟩,
        ⟨43654, false, false, [28834], []⟩,
        ⟨75159, true, false, [], [86009]⟩,
        ⟨75159, true, false, [], [86009]⟩,
        ⟨75158, true, false, [], [86009]⟩
      ]⟩,
    ⟨[86009, 15], [62541, 58283, 93319], .contexts [
        ⟨130355, false, false, [], []⟩,
        ⟨131548, false, false, [62541], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2531. -/
def y322TCIndexRaw2531 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86011, 1], [86009], .contexts [
        ⟨34725, false, false, [], []⟩,
        ⟨34963, false, false, [], []⟩
      ]⟩,
    ⟨[86011, 3], [73425, 96919], .contexts [
        ⟨143527, true, false, [73422], [3]⟩,
        ⟨20, false, false, [73422, 96919], []⟩,
        ⟨143528, true, false, [], [96919]⟩
      ]⟩,
    ⟨[86011, 5], [62533, 89815], .contexts [
        ⟨130357, true, false, [62534], [5]⟩,
        ⟨57657, false, false, [62534], []⟩,
        ⟨57717, false, false, [62534], []⟩,
        ⟨130346, true, false, [], [89815]⟩
      ]⟩,
    ⟨[86011, 7], [62537, 87389], .contexts [
        ⟨130358, false, false, [], []⟩,
        ⟨135487, false, false, [], []⟩
      ]⟩,
    ⟨[86011, 9], [62555, 83037], .contexts [
        ⟨34727, false, false, [], []⟩,
        ⟨132922, false, false, [], []⟩
      ]⟩,
    ⟨[86011, 11], [28857, 91771], .contexts [
        ⟨75180, false, false, [], []⟩,
        ⟨75263, false, false, [], []⟩
      ]⟩,
    ⟨[86011, 13], [62543, 85633], .contexts [
        ⟨130361, false, false, [], []⟩,
        ⟨135496, false, false, [], []⟩
      ]⟩,
    ⟨[86011, 15], [62541, 93649], .contexts [
        ⟨130359, false, false, [], []⟩
      ]⟩,
    ⟨[86019, 1], [64759, 85643], .contexts [
        ⟨132944, false, false, [], []⟩
      ]⟩,
    ⟨[86019, 3], [71693, 96767], .contexts [
        ⟨140571, true, false, [71690], [3]⟩,
        ⟨20, false, false, [71690, 96767], []⟩,
        ⟨140572, true, false, [], [96767]⟩
      ]⟩,
    ⟨[86019, 5], [64763, 86247], .contexts [
        ⟨132938, true, false, [64756], [5]⟩,
        ⟨132896, true, false, [64756, 64716], [5]⟩,
        ⟨28, false, false, [64756, 64716, 86247], []⟩,
        ⟨132897, true, false, [64756], [86247]⟩,
        ⟨132939, true, false, [], [64719, 86247]⟩,
        ⟨132946, true, false, [], [86247]⟩
      ]⟩,
    ⟨[86019, 7], [65589, 83705], .contexts [
        ⟨133841, false, false, [], []⟩
      ]⟩,
    ⟨[86019, 9], [64761, 88353], .contexts [
        ⟨132938, true, false, [64756], [9]⟩,
        ⟨132770, true, false, [64756, 64602], [9]⟩,
        ⟨131201, true, false, [64756, 64602, 63262], [9]⟩,
        ⟨46, false, false, [64756, 64602, 63262, 88353], []⟩,
        ⟨131202, true, false, [64756, 64602], [88353]⟩,
        ⟨132771, true, false, [64756], [63265, 88353]⟩,
        ⟨132773, true, false, [64756], [88353]⟩,
        ⟨132939, true, false, [], [64609, 88353]⟩,
        ⟨132945, true, false, [], [88353]⟩
      ]⟩,
    ⟨[86019, 11], [64755, 65491, 94235], .contexts [
        ⟨132942, false, false, [], []⟩,
        ⟨133732, false, false, [64755], []⟩
      ]⟩,
    ⟨[86019, 13], [64745, 85053], .contexts [
        ⟨34739, false, false, [], []⟩,
        ⟨132934, false, false, [], []⟩
      ]⟩,
    ⟨[86019, 15], [64765, 85647], .contexts [
        ⟨34741, false, false, [], []⟩,
        ⟨132950, false, false, [], []⟩
      ]⟩,
    ⟨[86025, 1], [64769, 87223], .contexts [
        ⟨132956, true, false, [64770], [1]⟩,
        ⟨40785, false, false, [64770], []⟩,
        ⟨41062, false, false, [64770], []⟩,
        ⟨132958, true, false, [], [87223]⟩,
        ⟨132959, true, false, [], [87223]⟩
      ]⟩,
    ⟨[86025, 3], [64765, 85645], .contexts [
        ⟨34749, false, false, [], []⟩,
        ⟨132953, false, false, [], []⟩
      ]⟩,
    ⟨[86025, 5], [86027], .contexts [
        ⟨34751, false, false, [], []⟩,
        ⟨34951, false, false, [], []⟩
      ]⟩,
    ⟨[86025, 7], [64781, 84187], .contexts [
        ⟨132956, true, false, [64770], [7]⟩,
        ⟨110333, false, false, [64770], []⟩,
        ⟨120405, false, false, [64770], []⟩,
        ⟨132957, true, false, [], [45255, 84187]⟩,
        ⟨132967, true, false, [], [84187]⟩
      ]⟩,
    ⟨[86025, 9], [64775, 95337], .contexts [
        ⟨132965, false, false, [], []⟩,
        ⟨147380, false, false, [], []⟩
      ]⟩,
    ⟨[86025, 11], [64777, 94451], .contexts [
        ⟨132956, true, false, [64770], [11]⟩,
        ⟨101409, false, false, [64770], []⟩,
        ⟨120400, false, false, [64770], []⟩,
        ⟨132963, true, false, [], [45353, 94451]⟩,
        ⟨132964, true, false, [], [94451]⟩
      ]⟩,
    ⟨[86025, 13], [64773, 84765], .contexts [
        ⟨132956, true, false, [64770], [13]⟩,
        ⟨40787, false, false, [64770], []⟩,
        ⟨132960, false, false, [64770], []⟩,
        ⟨132959, true, false, [], [61063, 84765]⟩,
        ⟨132961, true, false, [], [84765]⟩
      ]⟩,
    ⟨[86025, 15], [64779, 85913], .contexts [
        ⟨132956, true, false, [64770], [15]⟩,
        ⟨110329, false, false, [64770], []⟩,
        ⟨120414, false, false, [64770], []⟩,
        ⟨132957, true, false, [], [45251, 85913]⟩,
        ⟨132966, true, false, [], [85913]⟩
      ]⟩,
    ⟨[86027, 1], [64805, 83025], .contexts [
        ⟨34755, false, false, [], []⟩,
        ⟨132990, false, false, [], []⟩
      ]⟩,
    ⟨[86027, 3], [64793, 85775], .contexts [
        ⟨132978, false, false, [], []⟩,
        ⟨147375, false, false, [], []⟩
      ]⟩,
    ⟨[86027, 5], [86025], .contexts [
        ⟨34753, false, false, [], []⟩,
        ⟨34953, false, false, [], []⟩
      ]⟩,
    ⟨[86027, 7], [64799, 83723], .contexts [
        ⟨132983, false, false, [], []⟩,
        ⟨147384, false, false, [], []⟩
      ]⟩,
    ⟨[86027, 9], [97221], .contexts [
        ⟨147367, false, false, [], []⟩,
        ⟨147368, false, false, [], []⟩
      ]⟩,
    ⟨[86027, 11], [64789, 83029], .contexts [
        ⟨132975, false, false, [], []⟩,
        ⟨147389, false, false, [], []⟩
      ]⟩,
    ⟨[86027, 13], [64803, 84767], .contexts [
        ⟨132986, false, false, [], []⟩,
        ⟨147398, false, false, [], []⟩
      ]⟩,
    ⟨[86027, 15], [64795, 84413], .contexts [
        ⟨132980, false, false, [], []⟩,
        ⟨147403, false, false, [], []⟩
      ]⟩,
    ⟨[86033, 1], [86035], .contexts [
        ⟨34765, false, false, [], []⟩,
        ⟨34947, false, false, [], []⟩
      ]⟩,
    ⟨[86033, 3], [64815, 70735, 87849], .contexts [
        ⟨133001, true, false, [64810], [3]⟩,
        ⟨97959, false, false, [64810], []⟩,
        ⟨109162, false, false, [64810], []⟩,
        ⟨133002, false, false, [64810], []⟩,
        ⟨133003, true, false, [64810], [92095]⟩,
        ⟨133004, true, false, [], [64813, 92095]⟩,
        ⟨133005, true, false, [], [92095]⟩,
        ⟨139493, false, false, [64815], []⟩
      ]⟩,
    ⟨[86033, 5], [64827, 83765], .contexts [
        ⟨133001, true, false, [64810], [5]⟩,
        ⟨110216, true, false, [64810, 45170], [5]⟩,
        ⟨28, false, false, [64810, 45170, 85927], []⟩,
        ⟨110217, true, false, [64810], [85927]⟩,
        ⟨120822, false, false, [64810, 45173], []⟩,
        ⟨133004, true, false, [], [45173, 54479, 83765]⟩,
        ⟨133011, true, false, [], [54479, 83765]⟩,
        ⟨133012, true, false, [], [83765]⟩
      ]⟩,
    ⟨[86033, 7], [64819, 66147, 83411], .contexts [
        ⟨133001, true, false, [64810], [7]⟩,
        ⟨98235, true, false, [64810, 35774], [7]⟩,
        ⟨38, false, false, [64810, 35774, 93659], []⟩,
        ⟨98233, false, true, [64810], [93659]⟩,
        ⟨133004, true, false, [], [35773, 93659]⟩,
        ⟨133008, true, false, [], [93659]⟩,
        ⟨134524, false, false, [64819], []⟩
      ]⟩,
    ⟨[86033, 9], [64823, 96059], .contexts [
        ⟨133001, true, false, [64810], [9]⟩,
        ⟨98239, true, false, [64810, 35778], [9]⟩,
        ⟨46, false, false, [64810, 35778, 96147], []⟩,
        ⟨98237, false, true, [64810], [96147]⟩,
        ⟨102224, false, false, [64810, 35777], []⟩,
        ⟨133004, true, false, [], [35777, 37457, 96059]⟩,
        ⟨133009, true, false, [], [37457, 96059]⟩,
        ⟨133010, true, false, [], [96059]⟩
      ]⟩,
    ⟨[86033, 11], [64805, 83023], .contexts [
        ⟨34763, false, false, [], []⟩,
        ⟨132998, false, false, [], []⟩
      ]⟩,
    ⟨[86033, 13], [70583, 89887], .contexts [
        ⟨139317, false, false, [], []⟩
      ]⟩,
    ⟨[86033, 15], [64817, 87785], .contexts [
        ⟨133001, true, false, [64810], [15]⟩,
        ⟨98194, false, false, [64810], []⟩,
        ⟨98202, false, false, [64810], []⟩,
        ⟨133007, true, false, [], [87785]⟩,
        ⟨133006, true, false, [], [87785]⟩
      ]⟩,
    ⟨[86035, 1], [86033], .contexts [
        ⟨34767, false, false, [], []⟩,
        ⟨34949, false, false, [], []⟩
      ]⟩,
    ⟨[86035, 3], [64843, 84153], .contexts [
        ⟨133016, true, false, [64828], [3]⟩,
        ⟨110395, false, false, [64828], []⟩,
        ⟨120636, false, false, [64828], []⟩,
        ⟨133017, true, false, [], [45301, 52305, 84153]⟩,
        ⟨133030, true, false, [], [52305, 84153]⟩,
        ⟨133031, true, false, [], [84153]⟩
      ]⟩,
    ⟨[86035, 5], [64847, 83767], .contexts [
        ⟨133016, true, false, [64828], [5]⟩,
        ⟨110397, false, false, [64828], []⟩,
        ⟨120805, false, false, [64828, 45305], []⟩,
        ⟨133017, true, false, [], [45305, 54479, 83767]⟩,
        ⟨133032, true, false, [], [54479, 83767]⟩,
        ⟨133033, true, false, [], [83767]⟩
      ]⟩,
    ⟨[86035, 7], [64831, 66163, 83413], .contexts [
        ⟨133023, false, false, [], []⟩,
        ⟨134534, false, false, [64831], []⟩
      ]⟩,
    ⟨[86035, 9], [64835, 86035], .contexts [
        ⟨133016, true, false, [64828], [9]⟩,
        ⟨59670, false, false, [64828], []⟩,
        ⟨133025, false, false, [64828, 24767], []⟩,
        ⟨133017, true, false, [], [24767, 64829, 86035]⟩,
        ⟨133026, true, false, [], [64829, 86035]⟩,
        ⟨133027, true, false, [], [86035]⟩
      ]⟩,
    ⟨[86035, 11], [64839, 83021], .contexts [
        ⟨133016, true, false, [64828], [11]⟩,
        ⟨98258, false, false, [64828], []⟩,
        ⟨120623, false, false, [64828], []⟩,
        ⟨133017, true, false, [], [35783, 45379, 83021]⟩,
        ⟨133028, true, false, [], [45379, 83021]⟩,
        ⟨133029, true, false, [], [83021]⟩
      ]⟩,
    ⟨[86035, 13], [86037], .contexts [
        ⟨34769, false, false, [], []⟩,
        ⟨34946, false, false, [], []⟩
      ]⟩,
    ⟨[86035, 15], [64817, 87783], .contexts [
        ⟨133016, true, false, [64828], [15]⟩,
        ⟨46018, false, false, [64828], []⟩,
        ⟨46076, false, false, [64828], []⟩,
        ⟨133020, true, false, [], [87783]⟩
      ]⟩,
    ⟨[86037, 1], [64817, 64867, 86041], .contexts [
        ⟨133036, false, false, [], []⟩,
        ⟨133058, false, false, [64817], []⟩
      ]⟩,
    ⟨[86037, 3], [64859, 96579], .contexts [
        ⟨133035, true, false, [64828], [3]⟩,
        ⟨120863, false, false, [64828], []⟩,
        ⟨125648, false, false, [64828, 54543], []⟩,
        ⟨133017, true, false, [], [54543, 58633, 96579]⟩,
        ⟨133044, true, false, [], [58633, 96579]⟩,
        ⟨133045, true, false, [], [96579]⟩
      ]⟩,
    ⟨[86037, 5], [64853, 64907, 86047], .contexts [
        ⟨133035, true, false, [64828], [5]⟩,
        ⟨110566, true, false, [64828, 45448], [5]⟩,
        ⟨28, false, false, [64828, 45448, 93791], []⟩,
        ⟨110567, true, false, [64828], [93791]⟩,
        ⟨133017, true, false, [], [45451, 93791]⟩,
        ⟨133042, true, false, [], [93791]⟩,
        ⟨133103, false, false, [64853], []⟩
      ]⟩,
    ⟨[86037, 7], [64831, 88951], .contexts [
        ⟨133035, true, false, [64828], [7]⟩,
        ⟨53591, false, false, [64828], []⟩,
        ⟨53603, false, false, [64828], []⟩,
        ⟨133022, true, false, [], [88951]⟩
      ]⟩,
    ⟨[86037, 9], [64851, 86037], .contexts [
        ⟨133041, false, false, [], []⟩
      ]⟩,
    ⟨[86037, 11], [64855, 82895], .contexts [
        ⟨133035, true, false, [64828], [11]⟩,
        ⟨120630, false, false, [64828], []⟩,
        ⟨128747, false, false, [64828], []⟩,
        ⟨133017, true, false, [], [54333, 82895]⟩,
        ⟨133043, true, false, [], [82895]⟩
      ]⟩,
    ⟨[86037, 13], [86035], .contexts [
        ⟨34771, false, false, [], []⟩,
        ⟨34947, false, false, [], []⟩
      ]⟩,
    ⟨[86039], [64863, 86037], .contexts [
        ⟨133048, false, false, [], []⟩
      ]⟩,
    ⟨[86037, 15], [64863, 86037], .contexts [
        ⟨34773, false, false, [], []⟩,
        ⟨162039, false, false, [], []⟩
      ]⟩,
    ⟨[86041, 1], [64863, 86037], .contexts [
        ⟨34778, false, false, [], []⟩,
        ⟨162039, false, false, [], []⟩
      ]⟩,
    ⟨[86043], [64883, 86041], .contexts [
        ⟨133069, false, false, [], []⟩
      ]⟩,
    ⟨[86041, 3], [64883, 86041], .contexts [
        ⟨34780, false, false, [], []⟩,
        ⟨162042, false, false, [], []⟩
      ]⟩,
    ⟨[86041, 5], [64877, 64887, 86045], .contexts [
        ⟨133064, false, false, [], []⟩,
        ⟨133082, false, false, [64877], []⟩
      ]⟩,
    ⟨[86041, 7], [64871, 88949], .contexts [
        ⟨133053, true, false, [64866], [7]⟩,
        ⟨53610, true, false, [64866, 23462], [7]⟩,
        ⟨38, false, false, [64866, 23462, 88949], []⟩,
        ⟨53513, true, false, [64866], [88949]⟩,
        ⟨53605, false, false, [64866], []⟩,
        ⟨133054, true, false, [], [23465, 88949]⟩,
        ⟨133057, true, false, [], [88949]⟩
      ]⟩,
    ⟨[86041, 9], [96915], .contexts [
        ⟨143462, false, false, [], []⟩,
        ⟨143463, false, false, [], []⟩
      ]⟩,
    ⟨[86041, 11], [64869, 82897], .contexts [
        ⟨133056, false, false, [], []⟩,
        ⟨143476, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2532. -/
def y322TCIndexRaw2532 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86041, 13], [64879, 83247], .contexts [
        ⟨133066, false, false, [], []⟩,
        ⟨143482, false, false, [], []⟩
      ]⟩,
    ⟨[86041, 15], [64875, 86041], .contexts [
        ⟨133062, false, false, [], []⟩,
        ⟨143488, false, false, [], []⟩
      ]⟩,
    ⟨[86045, 1], [86047], .contexts [
        ⟨34787, false, false, [], []⟩,
        ⟨34941, false, false, [], []⟩
      ]⟩,
    ⟨[86045, 3], [64891, 92611], .contexts [
        ⟨133074, true, false, [64886], [3]⟩,
        ⟨80936, false, false, [64886], []⟩,
        ⟨133077, false, false, [64886], []⟩,
        ⟨133078, true, false, [], [64889, 92611]⟩,
        ⟨133079, true, false, [], [92611]⟩
      ]⟩,
    ⟨[86045, 5], [64883, 86041], .contexts [
        ⟨34785, false, false, [], []⟩,
        ⟨162042, false, false, [], []⟩
      ]⟩,
    ⟨[86045, 7], [64899, 84201], .contexts [
        ⟨133087, false, false, [], []⟩
      ]⟩,
    ⟨[86045, 9], [64893, 90457], .contexts [
        ⟨133081, false, false, [], []⟩
      ]⟩,
    ⟨[86045, 11], [64903, 64937, 86053], .contexts [
        ⟨133091, false, false, [], []⟩,
        ⟨133125, false, false, [64903], []⟩
      ]⟩,
    ⟨[86045, 13], [64901, 88687], .contexts [
        ⟨133089, false, false, [], []⟩,
        ⟨137846, false, false, [], []⟩
      ]⟩,
    ⟨[86045, 15], [64897, 86045], .contexts [
        ⟨133074, true, false, [64886], [15]⟩,
        ⟨80938, true, false, [64886], [15]⟩,
        ⟨81181, true, false, [64886, 30626], [3, 15]⟩,
        ⟨81181, true, false, [64886, 30626], [3, 15]⟩,
        ⟨81147, true, false, [64886, 30626], [3, 15]⟩,
        ⟨1141, false, false, [64886, 30626, 93797], []⟩,
        ⟨81159, false, false, [64886, 30626], []⟩,
        ⟨81158, false, false, [64886, 30626], []⟩,
        ⟨81161, false, false, [64886, 30626], []⟩,
        ⟨81183, true, false, [64886], [93795]⟩,
        ⟨81183, true, false, [64886], [93795]⟩,
        ⟨81182, true, false, [64886], [93795]⟩,
        ⟨133083, false, false, [64886, 30653], []⟩,
        ⟨133078, true, false, [], [30653, 64887, 86045]⟩,
        ⟨133084, true, false, [], [64887, 86045]⟩,
        ⟨133085, true, false, [], [86045]⟩
      ]⟩,
    ⟨[86047, 1], [86045], .contexts [
        ⟨34789, false, false, [], []⟩,
        ⟨34942, false, false, [], []⟩
      ]⟩,
    ⟨[86047, 3], [64917, 91243], .contexts [
        ⟨133094, true, false, [64906], [3]⟩,
        ⟨81227, false, false, [64906], []⟩,
        ⟨121404, false, false, [64906], []⟩,
        ⟨133096, true, false, [], [30679, 91243]⟩,
        ⟨133102, true, false, [], [91243]⟩
      ]⟩,
    ⟨[86047, 5], [64925, 86037], .contexts [
        ⟨133094, true, false, [64906], [5]⟩,
        ⟨110566, false, false, [64906], []⟩,
        ⟨133038, false, false, [64906, 45449], []⟩,
        ⟨133096, true, false, [], [45449, 64829, 86037]⟩,
        ⟨133108, true, false, [], [64829, 86037]⟩,
        ⟨133109, true, false, [], [86037]⟩
      ]⟩,
    ⟨[86047, 7], [64919, 84197], .contexts [
        ⟨133094, true, false, [64906], [7]⟩,
        ⟨81223, true, false, [64906, 30674], [7]⟩,
        ⟨81212, true, false, [64906, 30674, 30666], [7]⟩,
        ⟨38, false, false, [64906, 30674, 30666, 84197], []⟩,
        ⟨81210, false, true, [64906, 30674], [84197]⟩,
        ⟨81224, true, false, [64906], [30665, 84197]⟩,
        ⟨81232, true, false, [64906], [84197]⟩,
        ⟨133096, true, false, [], [30685, 84197]⟩,
        ⟨133105, true, false, [], [84197]⟩
      ]⟩,
    ⟨[86047, 9], [64929, 86047], .contexts [
        ⟨34791, false, false, [], []⟩,
        ⟨133113, false, false, [], []⟩
      ]⟩,
    ⟨[86047, 11], [64921, 82893], .contexts [
        ⟨133107, false, false, [], []⟩
      ]⟩,
    ⟨[86047, 13], [64911, 83767], .contexts [
        ⟨133094, true, false, [64906], [13]⟩,
        ⟨80926, false, false, [64906], []⟩,
        ⟨81255, false, false, [64906], []⟩,
        ⟨120797, false, false, [64906, 30703], []⟩,
        ⟨133095, true, false, [64906], [83767]⟩,
        ⟨133097, true, false, [], [64909, 83767]⟩,
        ⟨133098, true, false, [], [83767]⟩
      ]⟩,
    ⟨[86047, 15], [64915, 86047], .contexts [
        ⟨133094, true, false, [64906], [15]⟩,
        ⟨80928, false, false, [64906], []⟩,
        ⟨81229, false, false, [64906], []⟩,
        ⟨133099, false, false, [64906], []⟩,
        ⟨133100, true, false, [64906], [86047]⟩,
        ⟨133097, true, false, [], [64913, 86047]⟩,
        ⟨133101, true, false, [], [86047]⟩
      ]⟩,
    ⟨[86053, 1], [64931, 82893], .contexts [
        ⟨34799, false, false, [], []⟩,
        ⟨133116, false, false, [], []⟩
      ]⟩,
    ⟨[86053, 3], [64935, 90625], .contexts [
        ⟨133124, false, false, [], []⟩,
        ⟨144692, false, false, [], []⟩
      ]⟩,
    ⟨[86053, 5], [64943, 82897], .contexts [
        ⟨133131, false, false, [], []⟩,
        ⟨144697, false, false, [], []⟩
      ]⟩,
    ⟨[86053, 7], [96983], .contexts [
        ⟨144685, false, false, [], []⟩,
        ⟨144686, false, false, [], []⟩
      ]⟩,
    ⟨[86053, 9], [67103, 84793], .contexts [
        ⟨135564, false, false, [], []⟩,
        ⟨137876, false, false, [], []⟩
      ]⟩,
    ⟨[86053, 11], [64947, 86045], .contexts [
        ⟨133134, false, false, [], []⟩,
        ⟨144705, false, false, [], []⟩
      ]⟩,
    ⟨[86053, 13], [86055], .contexts [
        ⟨34801, false, false, [], []⟩,
        ⟨34936, false, false, [], []⟩
      ]⟩,
    ⟨[86053, 15], [64941, 86053], .contexts [
        ⟨133129, false, false, [], []⟩,
        ⟨144713, false, false, [], []⟩
      ]⟩,
    ⟨[86055, 1], [69243, 96825], .contexts [
        ⟨141590, true, false, [69240], [1]⟩,
        ⟨8, false, false, [69240, 96825], []⟩,
        ⟨137852, true, false, [], [96825]⟩
      ]⟩,
    ⟨[86055, 3], [75709, 97219], .contexts [
        ⟨147349, true, false, [73766], [3]⟩,
        ⟨20, false, false, [73766, 97219], []⟩,
        ⟨147350, true, false, [], [97219]⟩
      ]⟩,
    ⟨[86055, 5], [67107, 83249], .contexts [
        ⟨135569, false, false, [], []⟩
      ]⟩,
    ⟨[86055, 7], [68649, 70379, 89911], .contexts [
        ⟨137242, false, false, [], []⟩,
        ⟨139110, false, false, [68649], []⟩
      ]⟩,
    ⟨[86055, 9], [67103, 84795], .contexts [
        ⟨137879, false, false, [], []⟩,
        ⟨137878, false, false, [], []⟩
      ]⟩,
    ⟨[86055, 11], [69243, 88687], .contexts [
        ⟨137851, true, false, [69240], [11]⟩,
        ⟨53, false, false, [69240, 88687], []⟩,
        ⟨137852, true, false, [], [88687]⟩
      ]⟩,
    ⟨[86055, 13], [86053], .contexts [
        ⟨34803, false, false, [], []⟩,
        ⟨34938, false, false, [], []⟩
      ]⟩,
    ⟨[86055, 15], [86057], .contexts [
        ⟨34805, false, false, [], []⟩,
        ⟨34935, false, false, [], []⟩
      ]⟩,
    ⟨[86057, 1], [63469, 83391], .contexts [
        ⟨34809, false, false, [], []⟩,
        ⟨131461, false, false, [], []⟩
      ]⟩,
    ⟨[86057, 3], [76521, 97267], .contexts [
        ⟨148367, true, false, [76518], [3]⟩,
        ⟨20, false, false, [76518, 97267], []⟩,
        ⟨148368, true, false, [], [97267]⟩
      ]⟩,
    ⟨[86057, 5], [63469, 83395], .contexts [
        ⟨137080, true, false, [63470], [5]⟩,
        ⟨28, false, false, [63470, 83395], []⟩,
        ⟨131460, true, false, [], [83395]⟩
      ]⟩,
    ⟨[86057, 7], [68521, 84397], .contexts [
        ⟨137098, true, false, [68518], [7]⟩,
        ⟨38, false, false, [68518, 84397], []⟩,
        ⟨137099, true, false, [], [84397]⟩
      ]⟩,
    ⟨[86057, 9], [68507, 84797], .contexts [
        ⟨137086, true, false, [68504], [9]⟩,
        ⟨46, false, false, [68504, 84797], []⟩,
        ⟨137087, true, false, [], [84797]⟩
      ]⟩,
    ⟨[86057, 11], [68511, 88683], .contexts [
        ⟨137091, true, false, [68508], [11]⟩,
        ⟨53, false, false, [68508, 88683], []⟩,
        ⟨137092, true, false, [], [88683]⟩
      ]⟩,
    ⟨[86057, 13], [68531, 86057], .contexts [
        ⟨137105, false, false, [], []⟩
      ]⟩,
    ⟨[86057, 15], [86055], .contexts [
        ⟨34807, false, false, [], []⟩,
        ⟨34936, false, false, [], []⟩
      ]⟩,
    ⟨[86067, 1], [63453, 87215], .contexts [
        ⟨131440, true, false, [63450], [1]⟩,
        ⟨40705, false, false, [63450], []⟩,
        ⟨40707, false, false, [63450], []⟩,
        ⟨131442, true, false, [], [87215]⟩
      ]⟩,
    ⟨[86067, 3], [63457, 86067], .contexts [
        ⟨131440, true, false, [63450], [3]⟩,
        ⟨40694, false, false, [63450], []⟩,
        ⟨131444, false, false, [63450, 19937], []⟩,
        ⟨131439, true, false, [], [19937, 63451, 86067]⟩,
        ⟨131445, true, false, [], [63451, 86067]⟩,
        ⟨131446, true, false, [], [86067]⟩
      ]⟩,
    ⟨[86067, 5], [63453, 84501], .contexts [
        ⟨131440, true, false, [63450], [5]⟩,
        ⟨40697, false, false, [63450], []⟩,
        ⟨27180, false, false, [63450], []⟩,
        ⟨131442, true, false, [], [84501]⟩
      ]⟩,
    ⟨[86067, 7], [63459, 85627], .contexts [
        ⟨131440, true, false, [63450], [7]⟩,
        ⟨40703, false, false, [63450], []⟩,
        ⟨40700, false, false, [63450], []⟩,
        ⟨131439, true, false, [], [18323, 85627]⟩,
        ⟨131447, true, false, [], [85627]⟩
      ]⟩,
    ⟨[86067, 9], [63465, 85729], .contexts [
        ⟨34823, false, false, [], []⟩,
        ⟨131451, false, false, [], []⟩
      ]⟩,
    ⟨[86067, 11], [86069], .contexts [
        ⟨34825, false, false, [], []⟩,
        ⟨34928, false, false, [], []⟩
      ]⟩,
    ⟨[86067, 13], [63463, 83299], .contexts [
        ⟨131440, true, false, [63450], [13]⟩,
        ⟨58650, false, false, [63450], []⟩,
        ⟨118644, false, false, [63450], []⟩,
        ⟨131439, true, false, [], [24561, 38795, 83299]⟩,
        ⟨131448, true, false, [], [38795, 83299]⟩,
        ⟨131449, true, false, [], [83299]⟩
      ]⟩,
    ⟨[86067, 15], [63453, 87211], .contexts [
        ⟨131440, true, false, [63450], [15]⟩,
        ⟨40686, false, false, [63450], []⟩,
        ⟨40665, false, false, [63450], []⟩,
        ⟨131442, true, false, [], [87211]⟩
      ]⟩,
    ⟨[86069, 1], [86071], .contexts [
        ⟨34829, false, false, [], []⟩,
        ⟨34927, false, false, [], []⟩
      ]⟩,
    ⟨[86069, 3], [63423, 86069], .contexts [
        ⟨131419, false, false, [], []⟩
      ]⟩,
    ⟨[86069, 5], [63417, 84327], .contexts [
        ⟨131411, false, false, [], []⟩
      ]⟩,
    ⟨[86069, 7], [69557, 90953], .contexts [
        ⟨138161, false, false, [], []⟩
      ]⟩,
    ⟨[86069, 9], [63439, 71391, 95799], .contexts [
        ⟨131428, true, false, [63436], [9]⟩,
        ⟨46, false, false, [63436, 95969], []⟩,
        ⟨131429, true, false, [], [95969]⟩,
        ⟨140234, false, false, [63439], []⟩
      ]⟩,
    ⟨[86069, 11], [86067], .contexts [
        ⟨34827, false, false, [], []⟩,
        ⟨34930, false, false, [], []⟩
      ]⟩,
    ⟨[86069, 13], [63447, 94323], .contexts [
        ⟨131435, true, false, [63444], [13]⟩,
        ⟨59, false, false, [63444, 94323], []⟩,
        ⟨131436, true, false, [], [94323]⟩
      ]⟩,
    ⟨[86069, 15], [63431, 90379], .contexts [
        ⟨131423, true, false, [63428], [15]⟩,
        ⟨1, false, false, [63428, 90379], []⟩,
        ⟨131424, true, false, [], [90379]⟩
      ]⟩,
    ⟨[86071, 1], [86069], .contexts [
        ⟨34831, false, false, [], []⟩,
        ⟨34928, false, false, [], []⟩
      ]⟩,
    ⟨[86071, 3], [62091, 96059], .contexts [
        ⟨129829, false, false, [], []⟩,
        ⟨136155, false, false, [], []⟩
      ]⟩,
    ⟨[86071, 5], [62089, 84325], .contexts [
        ⟨129820, true, false, [62084], [5]⟩,
        ⟨91485, false, false, [62084], []⟩,
        ⟨129821, true, false, [], [33661, 84325]⟩,
        ⟨129827, true, false, [], [84325]⟩
      ]⟩,
    ⟨[86071, 7], [65717, 68757, 90955], .contexts [
        ⟨133988, false, false, [], []⟩,
        ⟨138005, false, false, [65717], []⟩
      ]⟩,
    ⟨[86071, 9], [62083, 64303, 70735, 87849], .contexts [
        ⟨129824, false, false, [], []⟩,
        ⟨153734, false, false, [62083], []⟩
      ]⟩,
    ⟨[86071, 11], [62087, 87215], .contexts [
        ⟨129826, false, false, [], []⟩,
        ⟨136148, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2533. -/
def y322TCIndexRaw2533 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86071, 13], [62079, 84423], .contexts [
        ⟨34833, false, false, [], []⟩,
        ⟨129817, false, false, [], []⟩
      ]⟩,
    ⟨[86071, 15], [62093, 93267], .contexts [
        ⟨129831, false, false, [], []⟩,
        ⟨136201, false, false, [], []⟩
      ]⟩,
    ⟨[86077, 1], [62077, 85157], .contexts [
        ⟨34841, false, false, [], []⟩,
        ⟨129814, false, false, [], []⟩
      ]⟩,
    ⟨[86077, 3], [86079], .contexts [
        ⟨34843, false, false, [], []⟩,
        ⟨34922, false, false, [], []⟩
      ]⟩,
    ⟨[86077, 5], [62073, 85161], .contexts [
        ⟨129804, true, false, [62062], [5]⟩,
        ⟨101258, false, false, [62062], []⟩,
        ⟨129765, false, false, [62062, 36917], []⟩,
        ⟨129805, true, false, [], [36917, 62037, 85161]⟩,
        ⟨129810, true, false, [], [62037, 85161]⟩,
        ⟨129811, true, false, [], [85161]⟩
      ]⟩,
    ⟨[86077, 7], [62075, 84569], .contexts [
        ⟨129804, true, false, [62062], [7]⟩,
        ⟨125729, false, false, [62062], []⟩,
        ⟨129805, true, false, [], [58717, 84569]⟩,
        ⟨129812, true, false, [], [84569]⟩
      ]⟩,
    ⟨[86077, 9], [18869, 86077], .contexts [
        ⟨34845, true, false, [], [9]⟩,
        ⟨35367, true, false, [18866], [3, 9]⟩,
        ⟨35367, true, false, [18866], [3, 9]⟩,
        ⟨35366, true, false, [18866], [3, 9]⟩,
        ⟨35360, true, false, [18866], [3, 9]⟩,
        ⟨35357, true, false, [18866], [3, 9]⟩,
        ⟨479, false, false, [18866, 86079], []⟩,
        ⟨21, false, false, [18866, 86079], []⟩,
        ⟨34923, false, false, [18866], []⟩,
        ⟨34924, false, false, [18866], []⟩,
        ⟨34844, false, false, [18866], []⟩,
        ⟨34844, false, false, [18866], []⟩,
        ⟨35368, false, false, [18866], []⟩,
        ⟨35297, true, false, [], [86077]⟩
      ]⟩,
    ⟨[86077, 11], [62069, 90241], .contexts [
        ⟨129804, true, false, [62062], [11]⟩,
        ⟨95125, true, false, [62062, 34810], [11]⟩,
        ⟨53, false, false, [62062, 34810, 94331], []⟩,
        ⟨95102, true, false, [62062], [94331]⟩,
        ⟨109110, false, false, [62062, 34809], []⟩,
        ⟨129805, true, false, [], [34809, 44271, 90241]⟩,
        ⟨129808, true, false, [], [44271, 90241]⟩,
        ⟨129809, true, false, [], [90241]⟩
      ]⟩,
    ⟨[86077, 13], [62055, 96999], .contexts [
        ⟨144954, true, false, [62056], [13]⟩,
        ⟨59, false, false, [62056, 96999], []⟩,
        ⟨129790, true, false, [], [96999]⟩
      ]⟩,
    ⟨[86077, 15], [62065, 84425], .contexts [
        ⟨129804, true, false, [62062], [15]⟩,
        ⟨90570, false, false, [62062], []⟩,
        ⟨117143, false, false, [62062], []⟩,
        ⟨129805, true, false, [], [51333, 84425]⟩,
        ⟨129806, true, false, [], [84425]⟩
      ]⟩,
    ⟨[86079, 1], [62055, 92245], .contexts [
        ⟨129789, true, false, [62056], [1]⟩,
        ⟨70742, false, false, [62056], []⟩,
        ⟨70799, false, false, [62056], []⟩,
        ⟨129792, true, false, [], [92245]⟩
      ]⟩,
    ⟨[86079, 3], [86077], .contexts [
        ⟨34845, false, false, [], []⟩,
        ⟨34924, false, false, [], []⟩
      ]⟩,
    ⟨[86079, 5], [86081], .contexts [
        ⟨34847, false, false, [], []⟩,
        ⟨34920, false, false, [], []⟩
      ]⟩,
    ⟨[86079, 7], [62059, 91761], .contexts [
        ⟨129789, true, false, [62056], [7]⟩,
        ⟨74957, true, false, [62056, 28798], [7]⟩,
        ⟨38, false, false, [62056, 28798, 91761], []⟩,
        ⟨74810, true, false, [62056], [91761]⟩,
        ⟨74954, false, false, [62056], []⟩,
        ⟨129790, true, false, [], [28801, 91761]⟩,
        ⟨129797, true, false, [], [91761]⟩
      ]⟩,
    ⟨[86079, 9], [18867, 86079], .contexts [
        ⟨35360, false, false, [], []⟩,
        ⟨35366, false, false, [], []⟩
      ]⟩,
    ⟨[86079, 11], [64141, 87735], .contexts [
        ⟨132273, false, false, [], []⟩
      ]⟩,
    ⟨[86079, 13], [62055, 92249], .contexts [
        ⟨129793, false, false, [], []⟩
      ]⟩,
    ⟨[86079, 15], [71907, 96795], .contexts [
        ⟨141074, true, false, [71904], [15]⟩,
        ⟨1, false, false, [71904, 96795], []⟩,
        ⟨141075, true, false, [], [96795]⟩
      ]⟩,
    ⟨[86081, 1], [86083], .contexts [
        ⟨34851, false, false, [], []⟩,
        ⟨34918, false, false, [], []⟩
      ]⟩,
    ⟨[86081, 3], [57783, 83605], .contexts [
        ⟨124678, true, false, [57780], [3]⟩,
        ⟨20, false, false, [57780, 83605], []⟩,
        ⟨124679, true, false, [], [83605]⟩
      ]⟩,
    ⟨[86081, 5], [86079], .contexts [
        ⟨34849, false, false, [], []⟩,
        ⟨34922, false, false, [], []⟩
      ]⟩,
    ⟨[86081, 7], [18875, 86081], .contexts [
        ⟨34853, true, false, [], [7]⟩,
        ⟨35350, true, false, [18872], [1, 7]⟩,
        ⟨35350, true, false, [18872], [1, 7]⟩,
        ⟨35349, true, false, [18872], [1, 7]⟩,
        ⟨35340, true, false, [18872], [1, 7]⟩,
        ⟨35337, true, false, [18872], [1, 7]⟩,
        ⟨502, false, false, [18872, 86083], []⟩,
        ⟨9, false, false, [18872, 86083], []⟩,
        ⟨34919, false, false, [18872], []⟩,
        ⟨34920, false, false, [18872], []⟩,
        ⟨34852, false, false, [18872], []⟩,
        ⟨34852, false, false, [18872], []⟩,
        ⟨35347, false, false, [18872], []⟩,
        ⟨35316, true, false, [], [86081]⟩
      ]⟩,
    ⟨[86081, 9], [18869, 86081], .contexts [
        ⟨35348, false, false, [], []⟩,
        ⟨35355, false, false, [], []⟩
      ]⟩,
    ⟨[86081, 11], [58601, 87733], .contexts [
        ⟨125605, false, false, [], []⟩
      ]⟩,
    ⟨[86081, 13], [62051, 94775], .contexts [
        ⟨129783, false, false, [], []⟩
      ]⟩,
    ⟨[86081, 15], [62051, 62235, 90205], .contexts [
        ⟨129786, false, false, [], []⟩,
        ⟨129980, false, false, [62051], []⟩
      ]⟩,
    ⟨[86083, 1], [86081], .contexts [
        ⟨34853, false, false, [], []⟩,
        ⟨34920, false, false, [], []⟩
      ]⟩,
    ⟨[86083, 3], [56097, 83843], .contexts [
        ⟨122746, true, false, [56094], [3]⟩,
        ⟨20, false, false, [56094, 83843], []⟩,
        ⟨122747, true, false, [], [83843]⟩
      ]⟩,
    ⟨[86083, 5], [56213, 92245], .contexts [
        ⟨122866, false, false, [], []⟩
      ]⟩,
    ⟨[86083, 7], [18873, 86083], .contexts [
        ⟨35340, false, false, [], []⟩,
        ⟨35349, false, false, [], []⟩
      ]⟩,
    ⟨[86083, 9], [86085], .contexts [
        ⟨34855, false, false, [], []⟩,
        ⟨34915, false, false, [], []⟩
      ]⟩,
    ⟨[86083, 11], [73113, 96901], .contexts [
        ⟨143158, false, false, [], []⟩
      ]⟩,
    ⟨[86083, 13], [56091, 89943], .contexts [
        ⟨122739, false, false, [], []⟩
      ]⟩,
    ⟨[86083, 15], [57311, 57641, 90203], .contexts [
        ⟨124163, false, false, [], []⟩,
        ⟨124545, false, false, [57311], []⟩
      ]⟩,
    ⟨[86085, 1], [18867, 86085], .contexts [
        ⟨35333, false, false, [], []⟩,
        ⟨35329, false, false, [], []⟩
      ]⟩,
    ⟨[86085, 3], [49673, 84825], .contexts [
        ⟨115151, true, false, [49668], [3]⟩,
        ⟨115143, true, false, [49668, 49664], [3]⟩,
        ⟨20, false, false, [49668, 49664, 84825], []⟩,
        ⟨115144, true, false, [49668], [84825]⟩,
        ⟨115150, true, false, [], [49663, 84825]⟩,
        ⟨115157, true, false, [], [84825]⟩
      ]⟩,
    ⟨[86085, 5], [75605, 97209], .contexts [
        ⟨147201, true, false, [75602], [5]⟩,
        ⟨28, false, false, [75602, 97209], []⟩,
        ⟨147202, true, false, [], [97209]⟩
      ]⟩,
    ⟨[86085, 7], [18875, 86085], .contexts [
        ⟨35317, false, false, [], []⟩,
        ⟨35334, false, false, [], []⟩
      ]⟩,
    ⟨[86085, 9], [86083], .contexts [
        ⟨34857, false, false, [], []⟩,
        ⟨34918, false, false, [], []⟩
      ]⟩,
    ⟨[86085, 11], [86087], .contexts [
        ⟨34859, false, false, [], []⟩,
        ⟨34913, false, false, [], []⟩
      ]⟩,
    ⟨[86085, 13], [27973, 46723, 89945], .contexts [
        ⟨72288, false, false, [], []⟩,
        ⟨112111, false, false, [27973], []⟩
      ]⟩,
    ⟨[86085, 15], [49671, 93163], .contexts [
        ⟨115153, false, false, [], []⟩,
        ⟨124160, false, false, [], []⟩
      ]⟩,
    ⟨[86089], [18867, 86087], .contexts [
        ⟨35304, false, false, [], []⟩
      ]⟩,
    ⟨[86087, 1], [18867, 86087], .contexts [
        ⟨34863, false, false, [], []⟩,
        ⟨162154, false, false, [], []⟩
      ]⟩,
    ⟨[86087, 3], [46699, 84827], .contexts [
        ⟨112081, true, false, [46696], [3]⟩,
        ⟨82176, false, false, [46696], []⟩,
        ⟨107109, false, false, [46696], []⟩,
        ⟨112084, true, false, [], [42225, 84827]⟩,
        ⟨112085, true, false, [], [84827]⟩
      ]⟩,
    ⟨[86087, 5], [46695, 93943], .contexts [
        ⟨112088, false, false, [], []⟩
      ]⟩,
    ⟨[86087, 7], [18873, 86087], .contexts [
        ⟨35308, false, false, [], []⟩,
        ⟨35309, false, false, [], []⟩
      ]⟩,
    ⟨[86087, 9], [46701, 92151], .contexts [
        ⟨112090, false, false, [], []⟩
      ]⟩,
    ⟨[86087, 11], [86085], .contexts [
        ⟨34861, false, false, [], []⟩,
        ⟨34915, false, false, [], []⟩
      ]⟩,
    ⟨[86087, 13], [18869, 86091], .contexts [
        ⟨35298, false, false, [], []⟩
      ]⟩,
    ⟨[86087, 15], [49671, 96907], .contexts [
        ⟨143255, true, false, [49668], [15]⟩,
        ⟨1, false, false, [49668, 96907], []⟩,
        ⟨115150, true, false, [], [96907]⟩
      ]⟩,
    ⟨[86091, 1], [18853, 86095], .contexts [
        ⟨35261, false, false, [], []⟩,
        ⟨35288, false, false, [], []⟩
      ]⟩,
    ⟨[86091, 3], [46687, 89957], .contexts [
        ⟨112070, false, false, [], []⟩
      ]⟩,
    ⟨[86091, 5], [49695, 93149], .contexts [
        ⟨115174, false, false, [], []⟩,
        ⟨122287, false, false, [], []⟩
      ]⟩,
    ⟨[86091, 7], [18857, 86091], .contexts [
        ⟨35267, false, false, [], []⟩,
        ⟨35275, false, false, [], []⟩
      ]⟩,
    ⟨[86091, 9], [46689, 92153], .contexts [
        ⟨112076, false, false, [], []⟩
      ]⟩,
    ⟨[86091, 11], [27969, 46723, 89945], .contexts [
        ⟨72281, false, false, [], []⟩,
        ⟨112111, false, false, [27969], []⟩
      ]⟩,
    ⟨[86091, 13], [18867, 86087], .contexts [
        ⟨34868, false, false, [], []⟩,
        ⟨162154, false, false, [], []⟩
      ]⟩,
    ⟨[86093], [18811, 86091], .contexts [
        ⟨35263, false, false, [], []⟩
      ]⟩,
    ⟨[86091, 15], [18811, 86091], .contexts [
        ⟨34870, false, false, [], []⟩,
        ⟨162170, false, false, [], []⟩
      ]⟩,
    ⟨[86095, 1], [18811, 86091], .contexts [
        ⟨34875, false, false, [], []⟩,
        ⟨162170, false, false, [], []⟩
      ]⟩,
    ⟨[86095, 3], [86097], .contexts [
        ⟨34877, false, false, [], []⟩,
        ⟨34905, false, false, [], []⟩
      ]⟩,
    ⟨[86095, 5], [18827, 97257], .contexts [
        ⟨148234, true, false, [18828], [5]⟩,
        ⟨28, false, false, [18828, 97257], []⟩,
        ⟨35202, false, true, [], [97257]⟩
      ]⟩,
    ⟨[86095, 7], [18805, 86095], .contexts [
        ⟨35212, false, false, [], []⟩,
        ⟨35209, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2534. -/
def y322TCIndexRaw2534 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86095, 9], [18783, 86095], .contexts [
        ⟨35206, false, false, [], []⟩
      ]⟩,
    ⟨[86095, 11], [18827, 83971], .contexts [
        ⟨35219, false, false, [], []⟩,
        ⟨35216, false, false, [], []⟩
      ]⟩,
    ⟨[86095, 13], [18821, 86095], .contexts [
        ⟨35193, false, false, [], []⟩,
        ⟨35241, false, false, [], []⟩
      ]⟩,
    ⟨[86095, 15], [18811, 86095], .contexts [
        ⟨35229, false, false, [], []⟩,
        ⟨35224, false, false, [], []⟩
      ]⟩,
    ⟨[86097, 1], [18753, 86101], .contexts [
        ⟨35150, false, false, [], []⟩,
        ⟨35095, false, false, [], []⟩
      ]⟩,
    ⟨[86097, 3], [86095], .contexts [
        ⟨34879, false, false, [], []⟩,
        ⟨34907, false, false, [], []⟩
      ]⟩,
    ⟨[86099], [18785, 86097], .contexts [
        ⟨35152, false, false, [], []⟩
      ]⟩,
    ⟨[86097, 5], [18785, 86097], .contexts [
        ⟨34881, false, false, [], []⟩,
        ⟨162182, false, false, [], []⟩
      ]⟩,
    ⟨[86097, 7], [18805, 86097], .contexts [
        ⟨35164, false, false, [], []⟩,
        ⟨35207, false, false, [], []⟩
      ]⟩,
    ⟨[86097, 9], [18745, 86097], .contexts [
        ⟨35143, false, false, [], []⟩,
        ⟨35204, false, false, [], []⟩
      ]⟩,
    ⟨[86097, 11], [18827, 83969], .contexts [
        ⟨35201, false, false, [], []⟩,
        ⟨35213, false, false, [], []⟩
      ]⟩,
    ⟨[86097, 13], [18799, 86097], .contexts [
        ⟨35156, false, false, [], []⟩,
        ⟨35184, false, false, [], []⟩
      ]⟩,
    ⟨[86097, 15], [18811, 86097], .contexts [
        ⟨35170, false, false, [], []⟩,
        ⟨35221, false, false, [], []⟩
      ]⟩,
    ⟨[86101, 1], [18785, 86097], .contexts [
        ⟨34886, false, false, [], []⟩,
        ⟨162182, false, false, [], []⟩
      ]⟩,
    ⟨[86101, 3], [43759, 55897, 93367], .contexts [
        ⟨108550, true, false, [43760], [3]⟩,
        ⟨88813, false, false, [43760], []⟩,
        ⟨88893, false, false, [43760], []⟩,
        ⟨108551, true, false, [], [95219]⟩,
        ⟨108551, true, false, [], [95219]⟩,
        ⟨108549, false, true, [], [95219]⟩,
        ⟨122485, false, false, [43759], []⟩
      ]⟩,
    ⟨[86101, 5], [18785, 86101], .contexts [
        ⟨35102, false, false, [], []⟩,
        ⟨35144, false, false, [], []⟩
      ]⟩,
    ⟨[86101, 7], [18787, 86101], .contexts [
        ⟨35108, false, false, [], []⟩,
        ⟨35157, false, false, [], []⟩
      ]⟩,
    ⟨[86101, 9], [86103], .contexts [
        ⟨34888, false, false, [], []⟩,
        ⟨34899, false, false, [], []⟩
      ]⟩,
    ⟨[86101, 11], [18771, 83965], .contexts [
        ⟨35132, false, false, [], []⟩,
        ⟨35126, false, false, [], []⟩
      ]⟩,
    ⟨[86101, 13], [18771, 83961], .contexts [
        ⟨35071, false, false, [], []⟩,
        ⟨35115, false, false, [], []⟩
      ]⟩,
    ⟨[86101, 15], [18769, 86101], .contexts [
        ⟨35114, false, false, [], []⟩,
        ⟨35111, false, false, [], []⟩
      ]⟩,
    ⟨[86103, 1], [18745, 86103], .contexts [
        ⟨35041, false, false, [], []⟩,
        ⟨35074, false, false, [], []⟩
      ]⟩,
    ⟨[86103, 3], [18749, 84213], .contexts [
        ⟨35045, false, false, [], []⟩,
        ⟨35079, false, false, [], []⟩
      ]⟩,
    ⟨[86103, 5], [18753, 86103], .contexts [
        ⟨35050, false, false, [], []⟩,
        ⟨35093, false, false, [], []⟩
      ]⟩,
    ⟨[86103, 7], [18757, 86103], .contexts [
        ⟨35053, false, false, [], []⟩,
        ⟨35103, false, false, [], []⟩
      ]⟩,
    ⟨[86103, 9], [86101], .contexts [
        ⟨34890, false, false, [], []⟩,
        ⟨34901, false, false, [], []⟩
      ]⟩,
    ⟨[86103, 11], [18739, 86103], .contexts [
        ⟨34892, false, false, [], []⟩,
        ⟨35046, false, false, [], []⟩
      ]⟩,
    ⟨[86103, 13], [18747, 83959], .contexts [
        ⟨35043, false, false, [], []⟩,
        ⟨35054, false, false, [], []⟩
      ]⟩,
    ⟨[86103, 15], [18769, 86103], .contexts [
        ⟨35065, false, false, [], []⟩,
        ⟨35109, false, false, [], []⟩
      ]⟩,
    ⟨[86109, 1], [92503], .contexts [
        ⟨72772, false, false, [], []⟩,
        ⟨72774, false, false, [], []⟩
      ]⟩,
    ⟨[86109, 3], [85103], .contexts [
        ⟨35381, false, false, [], []⟩,
        ⟨30177, false, false, [], []⟩
      ]⟩,
    ⟨[86109, 5], [323, 86109], .contexts [
        ⟨35387, false, false, [], []⟩,
        ⟨35383, false, false, [], []⟩
      ]⟩,
    ⟨[86109, 7], [317, 86109], .contexts [
        ⟨35391, false, false, [], []⟩,
        ⟨35388, false, false, [], []⟩
      ]⟩,
    ⟨[86109, 9], [22103, 22119, 88079], .contexts [
        ⟨47973, false, false, [], []⟩,
        ⟨47992, false, false, [22103], []⟩
      ]⟩,
    ⟨[86109, 11], [85489], .contexts [
        ⟨35393, false, false, [], []⟩,
        ⟨32356, false, false, [], []⟩
      ]⟩,
    ⟨[86109, 13], [82991], .contexts [
        ⟨35376, false, false, [], []⟩,
        ⟨18291, false, false, [], []⟩
      ]⟩,
    ⟨[86109, 15], [18879, 86109], .contexts [
        ⟨35400, false, false, [], []⟩,
        ⟨35396, false, false, [], []⟩
      ]⟩,
    ⟨[86111, 1], [245, 86111], .contexts [
        ⟨35410, false, false, [], []⟩,
        ⟨35407, false, false, [], []⟩
      ]⟩,
    ⟨[86111, 3], [16499, 86111], .contexts [
        ⟨35415, false, false, [], []⟩,
        ⟨35411, false, false, [], []⟩
      ]⟩,
    ⟨[86111, 5], [73009, 96891], .contexts [
        ⟨142961, true, false, [20314], [5]⟩,
        ⟨28, false, false, [20314, 96891], []⟩,
        ⟨142962, true, false, [], [96891]⟩
      ]⟩,
    ⟨[86111, 7], [16493, 93555], .contexts [
        ⟨80008, false, false, [], []⟩
      ]⟩,
    ⟨[86111, 9], [83673], .contexts [
        ⟨35403, false, false, [], []⟩,
        ⟨22564, false, false, [], []⟩
      ]⟩,
    ⟨[86111, 11], [759, 86111], .contexts [
        ⟨35421, false, false, [], []⟩,
        ⟨35417, false, false, [], []⟩
      ]⟩,
    ⟨[86111, 13], [86113], .contexts [
        ⟨35423, false, false, [], []⟩,
        ⟨35425, false, false, [], []⟩
      ]⟩,
    ⟨[86111, 15], [21589, 86583], .contexts [
        ⟨45556, true, false, [21586], [15]⟩,
        ⟨1, false, false, [21586, 86583], []⟩,
        ⟨45557, true, false, [], [86583]⟩
      ]⟩,
    ⟨[86113, 1], [28307, 92689], .contexts [
        ⟨73637, false, false, [], []⟩,
        ⟨73667, false, false, [], []⟩
      ]⟩,
    ⟨[86113, 3], [16499, 86113], .contexts [
        ⟨35433, false, false, [], []⟩,
        ⟨35428, false, false, [], []⟩
      ]⟩,
    ⟨[86113, 5], [20853, 86551], .contexts [
        ⟨42847, true, false, [20850], [5]⟩,
        ⟨28, false, false, [20850, 86551], []⟩,
        ⟨42848, true, false, [], [86551]⟩
      ]⟩,
    ⟨[86113, 7], [23731, 89195], .contexts [
        ⟨54756, false, false, [], []⟩,
        ⟨54751, false, false, [], []⟩
      ]⟩,
    ⟨[86113, 9], [83675], .contexts [
        ⟨35435, false, false, [], []⟩,
        ⟨22582, false, false, [], []⟩
      ]⟩,
    ⟨[86113, 11], [759, 86113], .contexts [
        ⟨35440, false, false, [], []⟩,
        ⟨35437, false, false, [], []⟩
      ]⟩,
    ⟨[86113, 13], [86111], .contexts [
        ⟨35424, false, false, [], []⟩,
        ⟨35404, false, false, [], []⟩
      ]⟩,
    ⟨[86113, 15], [20859, 84241], .contexts [
        ⟨35442, false, false, [], []⟩,
        ⟨155759, false, false, [], []⟩
      ]⟩,
    ⟨[86119, 1], [16499, 86119], .contexts [
        ⟨35480, false, false, [], []⟩,
        ⟨35474, false, false, [], []⟩
      ]⟩,
    ⟨[86119, 3], [20859, 84243], .contexts [
        ⟨35467, false, false, [], []⟩,
        ⟨42864, false, false, [], []⟩
      ]⟩,
    ⟨[86121], [20925, 86119], .contexts [
        ⟨43088, false, false, [], []⟩
      ]⟩,
    ⟨[86119, 5], [20925, 86119], .contexts [
        ⟨35487, false, false, [], []⟩,
        ⟨162231, false, false, [], []⟩
      ]⟩,
    ⟨[86119, 7], [28379, 89185], .contexts [
        ⟨73742, false, false, [], []⟩,
        ⟨73774, false, false, [], []⟩
      ]⟩,
    ⟨[86119, 9], [20923, 86123], .contexts [
        ⟨43092, false, false, [], []⟩,
        ⟨43261, false, false, [], []⟩
      ]⟩,
    ⟨[86119, 11], [759, 86119], .contexts [
        ⟨35485, false, false, [], []⟩,
        ⟨35481, false, false, [], []⟩
      ]⟩,
    ⟨[86119, 13], [28369, 92681], .contexts [
        ⟨73724, false, false, [], []⟩,
        ⟨73756, false, false, [], []⟩
      ]⟩,
    ⟨[86119, 15], [28369, 92685], .contexts [
        ⟨73720, true, false, [28370], [15]⟩,
        ⟨73509, false, false, [28370], []⟩,
        ⟨73521, false, false, [28370], []⟩,
        ⟨73723, true, false, [], [92685]⟩
      ]⟩,
    ⟨[86123, 1], [22007, 82959], .contexts [
        ⟨47315, false, false, [], []⟩,
        ⟨47330, false, false, [], []⟩
      ]⟩,
    ⟨[86123, 3], [20929, 84245], .contexts [
        ⟨43098, false, false, [], []⟩,
        ⟨43266, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2535. -/
def y322TCIndexRaw2535 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86123, 5], [20923, 86123], .contexts [
        ⟨43265, false, false, [], []⟩,
        ⟨43261, false, false, [], []⟩
      ]⟩,
    ⟨[86123, 7], [38933, 53819, 87545], .contexts [
        ⟨103975, false, false, [], []⟩,
        ⟨119975, false, false, [38933], []⟩
      ]⟩,
    ⟨[86123, 9], [20925, 86119], .contexts [
        ⟨35501, false, false, [], []⟩,
        ⟨162231, false, false, [], []⟩
      ]⟩,
    ⟨[86123, 11], [86125], .contexts [
        ⟨35503, false, false, [], []⟩,
        ⟨35506, false, false, [], []⟩
      ]⟩,
    ⟨[86123, 13], [38931, 53771, 88383], .contexts [
        ⟨103972, false, false, [], []⟩,
        ⟨119920, false, false, [38931], []⟩
      ]⟩,
    ⟨[86123, 15], [22007, 82963], .contexts [
        ⟨47284, false, false, [], []⟩,
        ⟨111186, false, false, [], []⟩
      ]⟩,
    ⟨[86125, 1], [86127], .contexts [
        ⟨35516, false, false, [], []⟩,
        ⟨35772, false, false, [], []⟩
      ]⟩,
    ⟨[86125, 3], [20929, 84247], .contexts [
        ⟨43272, true, false, [20926], [3]⟩,
        ⟨20, false, false, [20926, 84247], []⟩,
        ⟨43096, true, false, [], [84247]⟩,
        ⟨43268, false, false, [], []⟩
      ]⟩,
    ⟨[86125, 5], [20925, 86125], .contexts [
        ⟨43410, false, false, [], []⟩,
        ⟨43496, false, false, [], []⟩
      ]⟩,
    ⟨[86125, 7], [35233, 38817, 83291], .contexts [
        ⟨96505, false, false, [], []⟩,
        ⟨103842, false, false, [35233], []⟩
      ]⟩,
    ⟨[86125, 9], [759, 86125], .contexts [
        ⟨35514, false, false, [], []⟩,
        ⟨35511, false, false, [], []⟩
      ]⟩,
    ⟨[86125, 11], [86123], .contexts [
        ⟨35505, false, false, [], []⟩,
        ⟨35773, false, false, [], []⟩
      ]⟩,
    ⟨[86125, 13], [38931, 87585], .contexts [
        ⟨103978, true, false, [38934], [13]⟩,
        ⟨44838, false, false, [38934], []⟩,
        ⟨44823, false, false, [38934], []⟩,
        ⟨103980, true, false, [], [87585]⟩
      ]⟩,
    ⟨[86125, 15], [38931, 87589], .contexts [
        ⟨103984, false, false, [], []⟩,
        ⟨111184, false, false, [], []⟩
      ]⟩,
    ⟨[86127, 1], [86125], .contexts [
        ⟨35517, false, false, [], []⟩,
        ⟨35506, false, false, [], []⟩
      ]⟩,
    ⟨[86127, 3], [33561, 48323, 84127], .contexts [
        ⟨91297, false, false, [], []⟩,
        ⟨113663, false, false, [33561], []⟩
      ]⟩,
    ⟨[86127, 5], [20923, 86127], .contexts [
        ⟨43503, false, false, [], []⟩,
        ⟨43573, false, false, [], []⟩
      ]⟩,
    ⟨[86127, 7], [33627, 38805, 83293], .contexts [
        ⟨91429, false, false, [], []⟩,
        ⟨103832, false, false, [33627], []⟩
      ]⟩,
    ⟨[86127, 9], [33505, 88991], .contexts [
        ⟨91184, false, false, [], []⟩,
        ⟨91299, false, false, [], []⟩
      ]⟩,
    ⟨[86127, 11], [22007, 82959], .contexts [
        ⟨47344, false, false, [], []⟩,
        ⟨47330, false, false, [], []⟩
      ]⟩,
    ⟨[86127, 13], [51983, 85029], .contexts [
        ⟨35519, false, false, [], []⟩,
        ⟨117882, false, false, [], []⟩
      ]⟩,
    ⟨[86127, 15], [38931, 87591], .contexts [
        ⟨111194, false, false, [], []⟩,
        ⟨111191, false, false, [], []⟩
      ]⟩,
    ⟨[86135, 1], [44183, 91635], .contexts [
        ⟨108972, false, false, [], []⟩
      ]⟩,
    ⟨[86135, 3], [51943, 85023], .contexts [
        ⟨35533, false, false, [], []⟩,
        ⟨117857, false, false, [], []⟩
      ]⟩,
    ⟨[86135, 5], [86137], .contexts [
        ⟨35535, false, false, [], []⟩,
        ⟨35765, false, false, [], []⟩
      ]⟩,
    ⟨[86135, 7], [44189, 90233], .contexts [
        ⟨108964, true, false, [44184], [7]⟩,
        ⟨66990, false, false, [44184], []⟩,
        ⟨66987, false, false, [44184], []⟩,
        ⟨108965, true, false, [], [26443, 90233]⟩,
        ⟨108969, true, false, [], [90233]⟩
      ]⟩,
    ⟨[86135, 9], [44191, 85895], .contexts [
        ⟨108974, false, false, [], []⟩
      ]⟩,
    ⟨[86135, 11], [51769, 85011], .contexts [
        ⟨117610, false, false, [], []⟩,
        ⟨117749, false, false, [], []⟩
      ]⟩,
    ⟨[86135, 13], [37867, 86135], .contexts [
        ⟨102626, false, false, [], []⟩,
        ⟨102874, false, false, [], []⟩
      ]⟩,
    ⟨[86135, 15], [44187, 83079], .contexts [
        ⟨108964, true, false, [44184], [15]⟩,
        ⟨66983, false, false, [44184], []⟩,
        ⟨108923, false, false, [44184], []⟩,
        ⟨108967, true, false, [], [44147, 83079]⟩,
        ⟨108968, true, false, [], [83079]⟩
      ]⟩,
    ⟨[86137, 1], [86139], .contexts [
        ⟨35539, false, false, [], []⟩,
        ⟨35764, false, false, [], []⟩
      ]⟩,
    ⟨[86137, 3], [20923, 86137], .contexts [
        ⟨43689, false, false, [], []⟩,
        ⟨117771, false, false, [], []⟩
      ]⟩,
    ⟨[86137, 5], [86135], .contexts [
        ⟨35537, false, false, [], []⟩,
        ⟨35766, false, false, [], []⟩
      ]⟩,
    ⟨[86137, 7], [72995, 96889], .contexts [
        ⟨142932, true, false, [72992], [7]⟩,
        ⟨38, false, false, [72992, 96889], []⟩,
        ⟨142933, true, false, [], [96889]⟩
      ]⟩,
    ⟨[86137, 9], [44197, 85891], .contexts [
        ⟨108985, false, false, [], []⟩,
        ⟨117758, false, false, [], []⟩
      ]⟩,
    ⟨[86137, 11], [51875, 65395, 90797], .contexts [
        ⟨117754, false, false, [], []⟩,
        ⟨133656, false, false, [51875], []⟩
      ]⟩,
    ⟨[86137, 13], [37349, 86137], .contexts [
        ⟨102879, false, false, [], []⟩,
        ⟨117777, false, false, [], []⟩
      ]⟩,
    ⟨[86137, 15], [44193, 95257], .contexts [
        ⟨108978, true, false, [44194], [15]⟩,
        ⟨89303, false, false, [44194], []⟩,
        ⟨89279, false, false, [44194], []⟩,
        ⟨108982, true, false, [], [95257]⟩
      ]⟩,
    ⟨[86139, 1], [86137], .contexts [
        ⟨35541, false, false, [], []⟩,
        ⟨35765, false, false, [], []⟩
      ]⟩,
    ⟨[86139, 3], [44193, 44215, 83699], .contexts [
        ⟨108990, false, false, [], []⟩,
        ⟨109020, false, false, [44193], []⟩
      ]⟩,
    ⟨[86139, 5], [44199, 91635], .contexts [
        ⟨108989, false, false, [], []⟩,
        ⟨117790, false, false, [], []⟩
      ]⟩,
    ⟨[86139, 7], [53283, 91307], .contexts [
        ⟨119446, true, false, [53280], [7]⟩,
        ⟨38, false, false, [53280, 91307], []⟩,
        ⟨119447, true, false, [], [91307]⟩
      ]⟩,
    ⟨[86139, 9], [86141], .contexts [
        ⟨35543, false, false, [], []⟩,
        ⟨35762, false, false, [], []⟩
      ]⟩,
    ⟨[86139, 11], [51875, 65395, 90795], .contexts [
        ⟨117770, false, false, [], []⟩,
        ⟨133647, false, false, [51875], []⟩
      ]⟩,
    ⟨[86139, 13], [51923, 85735], .contexts [
        ⟨117817, true, false, [51924], [13]⟩,
        ⟨59, false, false, [51924, 85735], []⟩,
        ⟨117815, false, true, [], [85735]⟩
      ]⟩,
    ⟨[86139, 15], [58899, 96909], .contexts [
        ⟨143297, true, false, [58900], [15]⟩,
        ⟨1, false, false, [58900, 96909], []⟩,
        ⟨125964, true, false, [], [96909]⟩
      ]⟩,
    ⟨[86141, 1], [51879, 55817, 65377, 90789], .contexts [
        ⟨117762, false, false, [], []⟩,
        ⟨160238, false, false, [51879], []⟩
      ]⟩,
    ⟨[86141, 3], [51897, 83703], .contexts [
        ⟨117788, false, false, [], []⟩,
        ⟨125966, false, false, [], []⟩
      ]⟩,
    ⟨[86141, 5], [51901, 54129, 91581], .contexts [
        ⟨117795, false, false, [], []⟩,
        ⟨120369, false, false, [51901], []⟩
      ]⟩,
    ⟨[86141, 7], [58895, 85443], .contexts [
        ⟨125956, false, false, [], []⟩,
        ⟨125948, false, false, [], []⟩
      ]⟩,
    ⟨[86141, 9], [86139], .contexts [
        ⟨35545, false, false, [], []⟩,
        ⟨35764, false, false, [], []⟩
      ]⟩,
    ⟨[86141, 11], [86143], .contexts [
        ⟨35547, false, false, [], []⟩,
        ⟨35761, false, false, [], []⟩
      ]⟩,
    ⟨[86141, 13], [55831, 58909, 85737], .contexts [
        ⟨122397, false, false, [], []⟩,
        ⟨126747, false, false, [55831], []⟩
      ]⟩,
    ⟨[86141, 15], [58899, 85183], .contexts [
        ⟨125965, false, false, [], []⟩,
        ⟨125958, false, false, [], []⟩
      ]⟩,
    ⟨[86143, 1], [86145], .contexts [
        ⟨35551, false, false, [], []⟩,
        ⟨35760, false, false, [], []⟩
      ]⟩,
    ⟨[86143, 3], [57211, 83705], .contexts [
        ⟨124054, false, false, [], []⟩,
        ⟨129528, false, false, [], []⟩
      ]⟩,
    ⟨[86143, 5], [55103, 63781, 85779], .contexts [
        ⟨121504, true, false, [55098], [5]⟩,
        ⟨81742, false, false, [55098], []⟩,
        ⟨100964, false, false, [55098], []⟩,
        ⟨121510, true, false, [], [85903]⟩,
        ⟨121508, true, false, [], [36445, 85903]⟩,
        ⟨121509, true, false, [], [85903]⟩,
        ⟨131873, false, false, [55103], []⟩
      ]⟩,
    ⟨[86143, 7], [71703, 96767], .contexts [
        ⟨140577, true, false, [71700], [7]⟩,
        ⟨38, false, false, [71700, 96767], []⟩,
        ⟨140578, true, false, [], [96767]⟩
      ]⟩,
    ⟨[86143, 9], [51875, 55091, 90387], .contexts [
        ⟨117798, false, false, [], []⟩,
        ⟨121499, false, false, [51875], []⟩
      ]⟩,
    ⟨[86143, 11], [86141], .contexts [
        ⟨35549, false, false, [], []⟩,
        ⟨35762, false, false, [], []⟩
      ]⟩,
    ⟨[86143, 13], [55107, 57261, 85739], .contexts [
        ⟨121504, true, false, [55098], [13]⟩,
        ⟨101195, true, false, [55098, 36944], [13]⟩,
        ⟨59, false, false, [55098, 36944, 90839], []⟩,
        ⟨101196, true, false, [55098], [90839]⟩,
        ⟨121505, true, false, [], [36947, 90839]⟩,
        ⟨121513, true, false, [], [90839]⟩,
        ⟨124123, false, false, [55107], []⟩
      ]⟩,
    ⟨[86143, 15], [55105, 83885], .contexts [
        ⟨121504, true, false, [55098], [15]⟩,
        ⟨81990, false, false, [55098], []⟩,
        ⟨81998, false, false, [55098], []⟩,
        ⟨121512, true, false, [], [83885]⟩
      ]⟩,
    ⟨[86145, 1], [86143], .contexts [
        ⟨35553, false, false, [], []⟩,
        ⟨35761, false, false, [], []⟩
      ]⟩,
    ⟨[86145, 3], [55109, 68885, 86173], .contexts [
        ⟨121520, false, false, [], []⟩,
        ⟨137487, false, false, [55109], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2536. -/
def y322TCIndexRaw2536 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86145, 5], [55103, 85901], .contexts [
        ⟨121525, false, false, [], []⟩
      ]⟩,
    ⟨[86145, 7], [55113, 85439], .contexts [
        ⟨121517, true, false, [55098], [7]⟩,
        ⟨99988, false, false, [55098], []⟩,
        ⟨118758, false, false, [55098, 36385], []⟩,
        ⟨121505, true, false, [], [36385, 50243, 85439]⟩,
        ⟨121521, true, false, [], [50243, 85439]⟩,
        ⟨121522, true, false, [], [85439]⟩
      ]⟩,
    ⟨[86145, 9], [55101, 68059, 88271], .contexts [
        ⟨121517, true, false, [55098], [9]⟩,
        ⟨81748, false, false, [55098], []⟩,
        ⟨81767, false, false, [55098], []⟩,
        ⟨121507, true, false, [], [93917]⟩,
        ⟨121508, true, false, [], [93917]⟩,
        ⟨136700, false, false, [55101], []⟩
      ]⟩,
    ⟨[86145, 11], [55115, 55817, 65377, 90789], .contexts [
        ⟨121524, false, false, [], []⟩,
        ⟨160238, false, false, [55115], []⟩
      ]⟩,
    ⟨[86145, 13], [86147], .contexts [
        ⟨35555, false, false, [], []⟩,
        ⟨35759, false, false, [], []⟩
      ]⟩,
    ⟨[86145, 15], [55105, 83887], .contexts [
        ⟨121518, false, false, [], []⟩
      ]⟩,
    ⟨[86147, 1], [55117, 57295, 85743], .contexts [
        ⟨121531, true, false, [55118], [1]⟩,
        ⟨49545, false, false, [55118], []⟩,
        ⟨49609, false, false, [55118], []⟩,
        ⟨121534, true, false, [], [88315]⟩,
        ⟨126362, false, false, [55117], []⟩
      ]⟩,
    ⟨[86147, 3], [55123, 65803, 83735], .contexts [
        ⟨121531, true, false, [55118], [3]⟩,
        ⟨81996, false, false, [55118], []⟩,
        ⟨121532, true, false, [], [30829, 91595]⟩,
        ⟨121537, true, false, [], [91595]⟩,
        ⟨134100, false, false, [55123], []⟩
      ]⟩,
    ⟨[86147, 5], [55129, 87243], .contexts [
        ⟨121531, true, false, [55118], [5]⟩,
        ⟨109540, false, false, [55118], []⟩,
        ⟨121532, true, false, [], [44623, 87243]⟩,
        ⟨121540, true, false, [], [87243]⟩
      ]⟩,
    ⟨[86147, 7], [55121, 83449], .contexts [
        ⟨121531, true, false, [55118], [7]⟩,
        ⟨49926, false, false, [55118], []⟩,
        ⟨49927, false, false, [55118], []⟩,
        ⟨121532, true, false, [], [22659, 83449]⟩,
        ⟨121536, true, false, [], [83449]⟩
      ]⟩,
    ⟨[86147, 9], [55117, 68081, 88269], .contexts [
        ⟨121535, false, false, [], []⟩,
        ⟨136714, false, false, [55117], []⟩
      ]⟩,
    ⟨[86147, 11], [55127, 87233], .contexts [
        ⟨121531, true, false, [55118], [11]⟩,
        ⟨101096, false, false, [55118], []⟩,
        ⟨121108, false, false, [55118], []⟩,
        ⟨121532, true, false, [], [36897, 37313, 87233]⟩,
        ⟨121538, true, false, [], [37313, 87233]⟩,
        ⟨121539, true, false, [], [87233]⟩
      ]⟩,
    ⟨[86147, 13], [86145], .contexts [
        ⟨35557, false, false, [], []⟩,
        ⟨35760, false, false, [], []⟩
      ]⟩,
    ⟨[86147, 15], [59233, 85747], .contexts [
        ⟨35559, false, false, [], []⟩,
        ⟨126418, false, false, [], []⟩
      ]⟩,
    ⟨[86155, 1], [65515, 84759], .contexts [
        ⟨35574, false, false, [], []⟩,
        ⟨133760, false, false, [], []⟩
      ]⟩,
    ⟨[86155, 3], [66839, 83741], .contexts [
        ⟨135230, false, false, [], []⟩
      ]⟩,
    ⟨[86155, 5], [61957, 84557], .contexts [
        ⟨35572, false, false, [], []⟩,
        ⟨144863, false, false, [], []⟩
      ]⟩,
    ⟨[86155, 7], [65177, 88495], .contexts [
        ⟨133384, false, false, [], []⟩
      ]⟩,
    ⟨[86155, 9], [74217, 96991], .contexts [
        ⟨144829, true, false, [74214], [9]⟩,
        ⟨46, false, false, [74214, 96991], []⟩,
        ⟨144830, true, false, [], [96991]⟩
      ]⟩,
    ⟨[86155, 11], [67555, 84553], .contexts [
        ⟨136097, false, false, [], []⟩
      ]⟩,
    ⟨[86155, 13], [64641, 84277], .contexts [
        ⟨132801, true, false, [64638], [13]⟩,
        ⟨59, false, false, [64638, 84277], []⟩,
        ⟨132802, true, false, [], [84277]⟩
      ]⟩,
    ⟨[86155, 15], [65189, 84763], .contexts [
        ⟨133398, true, false, [65186], [15]⟩,
        ⟨1, false, false, [65186, 84763], []⟩,
        ⟨133399, true, false, [], [84763]⟩
      ]⟩,
    ⟨[86161, 1], [68935, 84553], .contexts [
        ⟨35584, false, false, [], []⟩,
        ⟨137511, false, false, [], []⟩
      ]⟩,
    ⟨[86161, 3], [68277, 85743], .contexts [
        ⟨136911, true, false, [68274], [3]⟩,
        ⟨20, false, false, [68274, 85743], []⟩,
        ⟨136912, true, false, [], [85743]⟩
      ]⟩,
    ⟨[86161, 5], [69095, 84763], .contexts [
        ⟨137682, true, false, [69092], [5]⟩,
        ⟨28, false, false, [69092, 84763], []⟩,
        ⟨137683, true, false, [], [84763]⟩
      ]⟩,
    ⟨[86161, 7], [69415, 95571], .contexts [
        ⟨138025, true, false, [69412], [7]⟩,
        ⟨38, false, false, [69412, 95571], []⟩,
        ⟨138026, true, false, [], [95571]⟩
      ]⟩,
    ⟨[86161, 9], [69023, 90769], .contexts [
        ⟨137623, false, false, [], []⟩
      ]⟩,
    ⟨[86161, 11], [65517, 84759], .contexts [
        ⟨35582, false, false, [], []⟩,
        ⟨133765, false, false, [], []⟩
      ]⟩,
    ⟨[86161, 13], [68271, 87273], .contexts [
        ⟨136902, false, false, [], []⟩
      ]⟩,
    ⟨[86161, 15], [68843, 84557], .contexts [
        ⟨137431, true, false, [68840], [15]⟩,
        ⟨1, false, false, [68840, 84557], []⟩,
        ⟨137432, true, false, [], [84557]⟩
      ]⟩,
    ⟨[86167, 1], [68911, 83715], .contexts [
        ⟨35594, false, false, [], []⟩,
        ⟨137492, false, false, [], []⟩
      ]⟩,
    ⟨[86167, 3], [68929, 84179], .contexts [
        ⟨137495, true, false, [68916], [3]⟩,
        ⟨132193, true, false, [68916, 64086], [3]⟩,
        ⟨131381, false, false, [68916, 64086], []⟩,
        ⟨132195, true, false, [68916], [63395, 84179]⟩,
        ⟨132197, true, false, [68916], [84179]⟩,
        ⟨137496, true, false, [], [64093, 84179]⟩,
        ⟨137504, true, false, [], [84179]⟩
      ]⟩,
    ⟨[86167, 5], [68927, 83719], .contexts [
        ⟨137495, true, false, [68916], [5]⟩,
        ⟨132193, true, false, [68916, 64086], [5]⟩,
        ⟨75829, false, false, [68916, 64086], []⟩,
        ⟨127118, false, false, [68916, 64086], []⟩,
        ⟨131992, false, false, [68916, 64086, 59861], []⟩,
        ⟨132194, true, false, [68916, 64086], [83719]⟩,
        ⟨132195, true, false, [68916], [64089, 83719]⟩,
        ⟨132196, true, false, [68916], [83719]⟩,
        ⟨137496, true, false, [], [64091, 83719]⟩,
        ⟨137503, true, false, [], [83719]⟩
      ]⟩,
    ⟨[86167, 7], [68931, 95577], .contexts [
        ⟨137495, true, false, [68916], [7]⟩,
        ⟨134679, false, false, [68916], []⟩,
        ⟨134674, false, false, [68916], []⟩,
        ⟨137496, true, false, [], [66317, 95577]⟩,
        ⟨137505, true, false, [], [95577]⟩
      ]⟩,
    ⟨[86167, 9], [68923, 86167], .contexts [
        ⟨137495, true, false, [68916], [9]⟩,
        ⟨91719, false, false, [68916], []⟩,
        ⟨137499, false, false, [68916, 33649], []⟩,
        ⟨137496, true, false, [], [33649, 68917, 86167]⟩,
        ⟨137500, true, false, [], [68917, 86167]⟩,
        ⟨137501, true, false, [], [86167]⟩
      ]⟩,
    ⟨[86167, 11], [68919, 85641], .contexts [
        ⟨137495, true, false, [68916], [11]⟩,
        ⟨53779, false, false, [68916], []⟩,
        ⟨134756, false, false, [68916], []⟩,
        ⟨137496, true, false, [], [59475, 85641]⟩,
        ⟨137497, true, false, [], [85641]⟩
      ]⟩,
    ⟨[86167, 13], [68925, 91145], .contexts [
        ⟨137495, true, false, [68916], [13]⟩,
        ⟨128047, true, false, [68916, 60664], [13]⟩,
        ⟨64604, false, false, [68916, 60664], []⟩,
        ⟨64849, false, false, [68916, 60664], []⟩,
        ⟨128050, true, false, [68916], [91145]⟩,
        ⟨128051, true, false, [68916], [91145]⟩,
        ⟨137496, true, false, [], [60663, 91145]⟩,
        ⟨137502, true, false, [], [91145]⟩
      ]⟩,
    ⟨[86167, 15], [68935, 84551], .contexts [
        ⟨35592, false, false, [], []⟩,
        ⟨137508, false, false, [], []⟩
      ]⟩,
    ⟨[86173, 1], [86175], .contexts [
        ⟨35604, false, false, [], []⟩,
        ⟨35745, false, false, [], []⟩
      ]⟩,
    ⟨[86173, 3], [68907, 86145], .contexts [
        ⟨137479, true, false, [68884], [3]⟩,
        ⟨81986, false, false, [68884], []⟩,
        ⟨121527, false, false, [68884, 30835], []⟩,
        ⟨137465, true, false, [], [30835, 55099, 86145]⟩,
        ⟨137484, true, false, [], [55099, 86145]⟩,
        ⟨137485, true, false, [], [86145]⟩
      ]⟩,
    ⟨[86173, 5], [68911, 83713], .contexts [
        ⟨35602, false, false, [], []⟩,
        ⟨137489, false, false, [], []⟩
      ]⟩,
    ⟨[86173, 7], [68903, 84173], .contexts [
        ⟨137479, true, false, [68884], [7]⟩,
        ⟨79875, false, false, [68884], []⟩,
        ⟨132095, false, false, [68884], []⟩,
        ⟨137472, true, false, [], [54449, 84173]⟩,
        ⟨137483, true, false, [], [84173]⟩
      ]⟩,
    ⟨[86173, 9], [68897, 84301], .contexts [
        ⟨137479, true, false, [68884], [9]⟩,
        ⟨79438, false, false, [68884], []⟩,
        ⟨132076, false, false, [68884], []⟩,
        ⟨137467, true, false, [], [54883, 84301]⟩,
        ⟨137480, true, false, [], [84301]⟩
      ]⟩,
    ⟨[86173, 11], [68909, 83745], .contexts [
        ⟨137479, true, false, [68884], [11]⟩,
        ⟨135720, false, false, [68884], []⟩,
        ⟨137465, true, false, [], [67237, 83745]⟩,
        ⟨137486, true, false, [], [83745]⟩
      ]⟩,
    ⟨[86173, 13], [68901, 83735], .contexts [
        ⟨137479, true, false, [68884], [13]⟩,
        ⟨79857, false, false, [68884], []⟩,
        ⟨134101, false, false, [68884, 30307], []⟩,
        ⟨137465, true, false, [], [30307, 65803, 83735]⟩,
        ⟨137481, true, false, [], [65803, 83735]⟩,
        ⟨137482, true, false, [], [83735]⟩
      ]⟩,
    ⟨[86173, 15], [68889, 84189], .contexts [
        ⟨137479, true, false, [68884], [15]⟩,
        ⟨79864, false, false, [68884], []⟩,
        ⟨79886, false, false, [68884], []⟩,
        ⟨137470, true, false, [], [84189]⟩
      ]⟩,
    ⟨[86175, 1], [86173], .contexts [
        ⟨35606, false, false, [], []⟩,
        ⟨35746, false, false, [], []⟩
      ]⟩,
    ⟨[86175, 3], [68895, 83707], .contexts [
        ⟨137464, true, false, [68884], [3]⟩,
        ⟨129534, false, false, [68884], []⟩,
        ⟨132058, false, false, [68884], []⟩,
        ⟨137465, true, false, [], [61893, 83707]⟩,
        ⟨137475, true, false, [], [83707]⟩
      ]⟩,
    ⟨[86175, 5], [68887, 83711], .contexts [
        ⟨137464, true, false, [68884], [5]⟩,
        ⟨79432, false, false, [68884], []⟩,
        ⟨132054, false, false, [68884], []⟩,
        ⟨137467, true, false, [], [63871, 83711]⟩,
        ⟨137468, true, false, [], [83711]⟩
      ]⟩,
    ⟨[86175, 7], [68891, 85913], .contexts [
        ⟨137464, true, false, [68884], [7]⟩,
        ⟨79903, false, false, [68884], []⟩,
        ⟨132080, false, false, [68884], []⟩,
        ⟨137472, true, false, [], [85913]⟩
      ]⟩,
    ⟨[86175, 9], [86177], .contexts [
        ⟨35608, false, false, [], []⟩,
        ⟨35744, false, false, [], []⟩
      ]⟩,
    ⟨[86175, 11], [71979, 96805], .contexts [
        ⟨141264, true, false, [71976], [11]⟩,
        ⟨53, false, false, [71976, 96805], []⟩,
        ⟨141265, true, false, [], [96805]⟩
      ]⟩,
    ⟨[86175, 13], [68893, 84183], .contexts [
        ⟨137474, false, false, [], []⟩
      ]⟩,
    ⟨[86175, 15], [68889, 84187], .contexts [
        ⟨137464, true, false, [68884], [15]⟩,
        ⟨79895, true, false, [68884, 30308], [15]⟩,
        ⟨1, false, false, [68884, 30308, 84187], []⟩,
        ⟨79825, true, false, [68884], [84187]⟩,
        ⟨79888, false, false, [68884], []⟩,
        ⟨137470, true, false, [], [84187]⟩
      ]⟩,
    ⟨[86177, 1], [31373, 86181], .contexts [
        ⟨84546, false, false, [], []⟩,
        ⟨84536, false, false, [], []⟩
      ]⟩,
    ⟨[86177, 3], [68881, 87641], .contexts [
        ⟨137454, true, false, [68870], [3]⟩,
        ⟨134807, false, false, [68870], []⟩,
        ⟨137455, true, false, [], [66419, 87641]⟩,
        ⟨137461, true, false, [], [87641]⟩
      ]⟩,
    ⟨[86177, 5], [68877, 88299], .contexts [
        ⟨137454, true, false, [68870], [5]⟩,
        ⟨132074, true, false, [68870, 63978], [5]⟩,
        ⟨28, false, false, [68870, 63978, 88299], []⟩,
        ⟨132075, true, false, [68870], [88299]⟩,
        ⟨137455, true, false, [], [63981, 88299]⟩,
        ⟨137459, true, false, [], [88299]⟩
      ]⟩,
    ⟨[86177, 7], [68879, 92295], .contexts [
        ⟨137454, true, false, [68870], [7]⟩,
        ⟨132093, true, false, [68870, 63998], [7]⟩,
        ⟨38, false, false, [68870, 63998, 92295], []⟩,
        ⟨132094, true, false, [68870], [92295]⟩,
        ⟨137455, true, false, [], [64001, 92295]⟩,
        ⟨137460, true, false, [], [92295]⟩
      ]⟩,
    ⟨[86177, 9], [86175], .contexts [
        ⟨35610, false, false, [], []⟩,
        ⟨35745, false, false, [], []⟩
      ]⟩,
    ⟨[86179], [31379, 86177], .contexts [
        ⟨137449, false, false, [], []⟩
      ]⟩,
    ⟨[86177, 11], [31379, 86177], .contexts [
        ⟨35612, false, false, [], []⟩,
        ⟨162363, false, false, [], []⟩
      ]⟩,
    ⟨[86177, 13], [76697, 97285], .contexts [
        ⟨148658, true, false, [76694], [13]⟩,
        ⟨59, false, false, [76694, 97285], []⟩,
        ⟨148659, true, false, [], [97285]⟩
      ]⟩,
    ⟨[86177, 15], [68873, 86187], .contexts [
        ⟨137454, true, false, [68870], [15]⟩,
        ⟨67937, false, false, [68870], []⟩,
        ⟨133819, false, false, [68870], []⟩,
        ⟨137455, true, false, [], [64997, 86187]⟩,
        ⟨137456, true, false, [], [86187]⟩
      ]⟩,
    ⟨[86181, 1], [31379, 86177], .contexts [
        ⟨35617, false, false, [], []⟩,
        ⟨162363, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2537. -/
def y322TCIndexRaw2537 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86181, 3], [68861, 88293], .contexts [
        ⟨137447, false, false, [], []⟩
      ]⟩,
    ⟨[86181, 5], [68863, 88297], .contexts [
        ⟨137440, true, false, [68852], [5]⟩,
        ⟨136026, false, false, [68852], []⟩,
        ⟨137441, true, false, [], [67485, 88297]⟩,
        ⟨137448, true, false, [], [88297]⟩
      ]⟩,
    ⟨[86181, 7], [68857, 92297], .contexts [
        ⟨137440, true, false, [68852], [7]⟩,
        ⟨134274, true, false, [68852, 65956], [7]⟩,
        ⟨38, false, false, [68852, 65956, 92297], []⟩,
        ⟨134275, true, false, [68852], [92297]⟩,
        ⟨137441, true, false, [], [65959, 92297]⟩,
        ⟨137444, true, false, [], [92297]⟩
      ]⟩,
    ⟨[86181, 9], [68849, 84303], .contexts [
        ⟨137437, false, false, [], []⟩
      ]⟩,
    ⟨[86181, 11], [31379, 86181], .contexts [
        ⟨84539, false, false, [], []⟩,
        ⟨84542, false, false, [], []⟩
      ]⟩,
    ⟨[86183], [68853, 86181], .contexts [
        ⟨137443, false, false, [], []⟩
      ]⟩,
    ⟨[86181, 13], [68853, 86181], .contexts [
        ⟨35619, false, false, [], []⟩,
        ⟨162373, false, false, [], []⟩
      ]⟩,
    ⟨[86181, 15], [68855, 86185], .contexts [
        ⟨137440, true, false, [68852], [15]⟩,
        ⟨35623, false, false, [68852], []⟩,
        ⟨35736, false, false, [68852], []⟩,
        ⟨137442, true, false, [], [86185]⟩,
        ⟨137442, true, false, [], [86185]⟩,
        ⟨137441, true, false, [], [86185]⟩
      ]⟩,
    ⟨[86185, 1], [86187], .contexts [
        ⟨35627, false, false, [], []⟩,
        ⟨35734, false, false, [], []⟩
      ]⟩,
    ⟨[86185, 3], [65969, 87651], .contexts [
        ⟨134280, true, false, [65966], [3]⟩,
        ⟨20, false, false, [65966, 87651], []⟩,
        ⟨134281, true, false, [], [87651]⟩
      ]⟩,
    ⟨[86185, 5], [66445, 87635], .contexts [
        ⟨134833, false, false, [], []⟩
      ]⟩,
    ⟨[86185, 7], [65931, 95335], .contexts [
        ⟨134244, false, false, [], []⟩
      ]⟩,
    ⟨[86185, 9], [65947, 84307], .contexts [
        ⟨134262, true, false, [65944], [9]⟩,
        ⟨46, false, false, [65944, 84307], []⟩,
        ⟨134263, true, false, [], [84307]⟩
      ]⟩,
    ⟨[86185, 11], [31379, 86185], .contexts [
        ⟨84519, false, false, [], []⟩,
        ⟨84525, false, false, [], []⟩
      ]⟩,
    ⟨[86185, 13], [71807, 96779], .contexts [
        ⟨140793, true, false, [71804], [13]⟩,
        ⟨59, false, false, [71804, 96779], []⟩,
        ⟨140794, true, false, [], [96779]⟩
      ]⟩,
    ⟨[86185, 15], [68853, 86181], .contexts [
        ⟨35625, false, false, [], []⟩,
        ⟨162373, false, false, [], []⟩
      ]⟩,
    ⟨[86187, 1], [86185], .contexts [
        ⟨35629, false, false, [], []⟩,
        ⟨35736, false, false, [], []⟩
      ]⟩,
    ⟨[86187, 3], [86189], .contexts [
        ⟨35631, false, false, [], []⟩,
        ⟨35731, false, false, [], []⟩
      ]⟩,
    ⟨[86187, 5], [68819, 87639], .contexts [
        ⟨137410, false, false, [], []⟩
      ]⟩,
    ⟨[86187, 7], [64995, 95337], .contexts [
        ⟨133191, false, false, [], []⟩
      ]⟩,
    ⟨[86187, 9], [65001, 84187], .contexts [
        ⟨133195, true, false, [64996], [9]⟩,
        ⟨132041, false, false, [64996], []⟩,
        ⟨133196, true, false, [], [63949, 84187]⟩,
        ⟨133202, true, false, [], [84187]⟩
      ]⟩,
    ⟨[86187, 11], [31373, 86187], .contexts [
        ⟨84511, false, false, [], []⟩,
        ⟨84515, false, false, [], []⟩
      ]⟩,
    ⟨[86187, 13], [64999, 65569, 89055], .contexts [
        ⟨133199, false, false, [], []⟩,
        ⟨133817, false, false, [64999], []⟩
      ]⟩,
    ⟨[86187, 15], [64999, 68871, 86177], .contexts [
        ⟨133195, true, false, [64996], [15]⟩,
        ⟨67936, false, false, [64996], []⟩,
        ⟨67938, false, false, [64996], []⟩,
        ⟨133198, true, false, [], [91849]⟩,
        ⟨137457, false, false, [64999], []⟩
      ]⟩,
    ⟨[86189, 1], [66397, 87645], .contexts [
        ⟨134786, false, false, [], []⟩
      ]⟩,
    ⟨[86189, 3], [86187], .contexts [
        ⟨35633, false, false, [], []⟩,
        ⟨35734, false, false, [], []⟩
      ]⟩,
    ⟨[86189, 5], [86191], .contexts [
        ⟨35635, false, false, [], []⟩,
        ⟨35729, false, false, [], []⟩
      ]⟩,
    ⟨[86189, 7], [64493, 91521], .contexts [
        ⟨132637, false, false, [], []⟩,
        ⟨137751, false, false, [], []⟩
      ]⟩,
    ⟨[86189, 9], [75383, 97189], .contexts [
        ⟨146854, true, false, [75380], [9]⟩,
        ⟨46, false, false, [75380, 97189], []⟩,
        ⟨146855, true, false, [], [97189]⟩
      ]⟩,
    ⟨[86189, 11], [31379, 86189], .contexts [
        ⟨84501, false, false, [], []⟩,
        ⟨84508, false, false, [], []⟩
      ]⟩,
    ⟨[86189, 13], [69173, 89057], .contexts [
        ⟨137758, false, false, [], []⟩
      ]⟩,
    ⟨[86189, 15], [66397, 87641], .contexts [
        ⟨134781, false, false, [], []⟩
      ]⟩,
    ⟨[86191, 1], [86193], .contexts [
        ⟨35639, false, false, [], []⟩,
        ⟨35727, false, false, [], []⟩
      ]⟩,
    ⟨[86191, 3], [73531, 96929], .contexts [
        ⟨143705, false, false, [], []⟩
      ]⟩,
    ⟨[86191, 5], [86189], .contexts [
        ⟨35637, false, false, [], []⟩,
        ⟨35731, false, false, [], []⟩
      ]⟩,
    ⟨[86191, 7], [31325, 94409], .contexts [
        ⟨84486, false, false, [], []⟩
      ]⟩,
    ⟨[86191, 9], [66599, 66713, 89043], .contexts [
        ⟨134983, false, false, [], []⟩,
        ⟨137836, false, false, [66599], []⟩
      ]⟩,
    ⟨[86191, 11], [31373, 86191], .contexts [
        ⟨84480, false, false, [], []⟩,
        ⟨84497, false, false, [], []⟩
      ]⟩,
    ⟨[86191, 13], [66601, 89059], .contexts [
        ⟨134978, true, false, [66596], [13]⟩,
        ⟨133466, true, false, [66596, 65238], [13]⟩,
        ⟨59, false, false, [66596, 65238, 89059], []⟩,
        ⟨133467, true, false, [66596], [89059]⟩,
        ⟨134979, true, false, [], [65241, 89059]⟩,
        ⟨134986, true, false, [], [89059]⟩
      ]⟩,
    ⟨[86191, 15], [66591, 89055], .contexts [
        ⟨134973, false, false, [], []⟩
      ]⟩,
    ⟨[86193, 1], [86191], .contexts [
        ⟨35641, false, false, [], []⟩,
        ⟨35729, false, false, [], []⟩
      ]⟩,
    ⟨[86193, 3], [66699, 86193], .contexts [
        ⟨135076, false, false, [], []⟩,
        ⟨135101, false, false, [], []⟩
      ]⟩,
    ⟨[86193, 5], [66599, 66677, 87645], .contexts [
        ⟨134989, false, false, [], []⟩,
        ⟨135059, false, false, [66599], []⟩
      ]⟩,
    ⟨[86193, 7], [31325, 94411], .contexts [
        ⟨84457, false, false, [], []⟩,
        ⟨84453, false, false, [], []⟩
      ]⟩,
    ⟨[86193, 9], [86195], .contexts [
        ⟨35643, false, false, [], []⟩,
        ⟨35725, false, false, [], []⟩
      ]⟩,
    ⟨[86193, 11], [31379, 86193], .contexts [
        ⟨84451, false, false, [], []⟩,
        ⟨84474, false, false, [], []⟩
      ]⟩,
    ⟨[86193, 13], [22449, 86193], .contexts [
        ⟨49147, false, false, [], []⟩
      ]⟩,
    ⟨[86193, 15], [66693, 89053], .contexts [
        ⟨135069, false, false, [], []⟩
      ]⟩,
    ⟨[86195, 1], [67443, 90813], .contexts [
        ⟨135992, false, false, [], []⟩
      ]⟩,
    ⟨[86195, 3], [66987, 86195], .contexts [
        ⟨135422, true, false, [61772], [3]⟩,
        ⟨1034, false, false, [61772, 83063], []⟩,
        ⟨1035, false, false, [61772, 83063], []⟩,
        ⟨135415, false, false, [61772], [7]⟩,
        ⟨129406, false, false, [61772, 66749], []⟩,
        ⟨135423, true, false, [61772], [86195]⟩,
        ⟨49124, false, false, [61772, 66983], []⟩,
        ⟨135424, true, false, [], [66983, 86195]⟩,
        ⟨135425, true, false, [], [86195]⟩
      ]⟩,
    ⟨[86195, 5], [73851, 96965], .contexts [
        ⟨144308, true, false, [73848], [5]⟩,
        ⟨28, false, false, [73848, 96965], []⟩,
        ⟨144309, true, false, [], [96965]⟩
      ]⟩,
    ⟨[94413], [61123, 61757, 83063], .contexts [
        ⟨128578, false, false, [], []⟩,
        ⟨129411, false, false, [], []⟩
      ]⟩,
    ⟨[86195, 7], [31325, 61123, 61757, 83063], .contexts [
        ⟨84420, false, false, [], []⟩,
        ⟨162419, false, false, [31325], []⟩
      ]⟩,
    ⟨[86195, 9], [86193], .contexts [
        ⟨35645, false, false, [], []⟩,
        ⟨35727, false, false, [], []⟩
      ]⟩,
    ⟨[86195, 11], [86197], .contexts [
        ⟨35647, false, false, [], []⟩,
        ⟨35723, false, false, [], []⟩
      ]⟩,
    ⟨[86195, 13], [22451, 86195], .contexts [
        ⟨49126, false, false, [], []⟩,
        ⟨49142, false, false, [], []⟩
      ]⟩,
    ⟨[86195, 15], [67451, 87075], .contexts [
        ⟨136005, false, false, [], []⟩
      ]⟩,
    ⟨[86197, 1], [86199], .contexts [
        ⟨35651, false, false, [], []⟩,
        ⟨35720, false, false, [], []⟩
      ]⟩,
    ⟨[86197, 3], [65927, 86197], .contexts [
        ⟨134235, true, false, [65924], [3]⟩,
        ⟨7129, false, false, [65924, 86197], []⟩,
        ⟨49080, false, false, [65924], []⟩,
        ⟨134237, true, false, [], [86197]⟩,
        ⟨134237, true, false, [], [86197]⟩,
        ⟨134236, true, false, [], [86197]⟩
      ]⟩,
    ⟨[86197, 5], [54009, 88011], .contexts [
        ⟨127851, false, false, [], []⟩,
        ⟨134231, false, false, [], []⟩
      ]⟩,
    ⟨[94415], [61777, 61793, 83059], .contexts [
        ⟨129416, false, false, [], []⟩,
        ⟨129425, false, false, [61777], []⟩
      ]⟩,
    ⟨[86197, 7], [31325, 61777, 61793, 83059], .contexts [
        ⟨84386, true, false, [31326], [7]⟩,
        ⟨38, false, false, [31326, 94415], []⟩,
        ⟨84321, true, false, [], [94415]⟩,
        ⟨162428, false, false, [31325], []⟩
      ]⟩,
    ⟨[86197, 9], [31373, 86197], .contexts [
        ⟨84417, false, false, [], []⟩,
        ⟨84444, false, false, [], []⟩
      ]⟩,
    ⟨[86197, 11], [86195], .contexts [
        ⟨35649, false, false, [], []⟩,
        ⟨35725, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2538. -/
def y322TCIndexRaw2538 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86197, 13], [22449, 86197], .contexts [
        ⟨49083, false, false, [], []⟩,
        ⟨49120, false, false, [], []⟩
      ]⟩,
    ⟨[86197, 15], [55239, 87071], .contexts [
        ⟨129624, true, false, [55240], [15]⟩,
        ⟨1, false, false, [55240, 87071], []⟩,
        ⟨121673, false, true, [], [87071]⟩,
        ⟨129622, false, false, [], []⟩
      ]⟩,
    ⟨[86199, 1], [86197], .contexts [
        ⟨35653, false, false, [], []⟩,
        ⟨35723, false, false, [], []⟩
      ]⟩,
    ⟨[86199, 3], [75567, 97207], .contexts [
        ⟨147164, false, false, [], []⟩
      ]⟩,
    ⟨[86199, 5], [54009, 88009], .contexts [
        ⟨120208, true, false, [54006], [5]⟩,
        ⟨28, false, false, [54006, 88009], []⟩,
        ⟨120209, true, false, [], [88009]⟩
      ]⟩,
    ⟨[86199, 7], [31325, 61805, 83057], .contexts [
        ⟨84348, false, false, [], []⟩,
        ⟨135971, false, false, [31325], []⟩
      ]⟩,
    ⟨[86199, 9], [36593, 54513, 54531, 83759], .contexts [
        ⟨100473, false, false, [], []⟩,
        ⟨155110, false, false, [36593], []⟩
      ]⟩,
    ⟨[86199, 11], [65443, 90813], .contexts [
        ⟨133686, false, false, [], []⟩,
        ⟨138183, false, false, [], []⟩
      ]⟩,
    ⟨[86199, 13], [86201], .contexts [
        ⟨35655, false, false, [], []⟩,
        ⟨35718, false, false, [], []⟩
      ]⟩,
    ⟨[86199, 15], [55239, 87069], .contexts [
        ⟨121672, false, false, [], []⟩,
        ⟨129619, false, false, [], []⟩
      ]⟩,
    ⟨[86201, 1], [22451, 86201], .contexts [
        ⟨49033, false, false, [], []⟩,
        ⟨49029, false, false, [], []⟩
      ]⟩,
    ⟨[86201, 3], [26153, 91355], .contexts [
        ⟨65710, false, false, [], []⟩
      ]⟩,
    ⟨[86201, 5], [45181, 96061], .contexts [
        ⟨110224, false, false, [], []⟩,
        ⟨110348, false, false, [], []⟩
      ]⟩,
    ⟨[94419], [54919, 54927, 84295], .contexts [
        ⟨121314, false, false, [], []⟩,
        ⟨129440, false, false, [], []⟩
      ]⟩,
    ⟨[86201, 7], [31325, 54919, 54927, 84295], .contexts [
        ⟨84320, true, false, [31326], [7]⟩,
        ⟨38, false, false, [31326, 94419], []⟩,
        ⟨84321, true, false, [], [94419]⟩,
        ⟨162445, false, false, [31325], []⟩
      ]⟩,
    ⟨[86201, 9], [30329, 54501, 83763], .contexts [
        ⟨79884, false, false, [], []⟩,
        ⟨120833, false, false, [30329], []⟩
      ]⟩,
    ⟨[86201, 11], [65443, 97253], .contexts [
        ⟨148183, true, false, [65440], [11]⟩,
        ⟨53, false, false, [65440, 97253], []⟩,
        ⟨133682, true, false, [], [97253]⟩
      ]⟩,
    ⟨[86201, 13], [86199], .contexts [
        ⟨35657, false, false, [], []⟩,
        ⟨35720, false, false, [], []⟩
      ]⟩,
    ⟨[86201, 15], [86203], .contexts [
        ⟨35659, false, false, [], []⟩,
        ⟨35716, false, false, [], []⟩
      ]⟩,
    ⟨[86203, 1], [22451, 86203], .contexts [
        ⟨35663, false, false, [], []⟩,
        ⟨49024, false, false, [], []⟩
      ]⟩,
    ⟨[86203, 3], [22449, 50655, 84811], .contexts [
        ⟨48957, false, false, [], []⟩,
        ⟨116321, false, false, [22449], []⟩
      ]⟩,
    ⟨[86203, 5], [45181, 96059], .contexts [
        ⟨110354, false, false, [], []⟩,
        ⟨110350, false, false, [], []⟩
      ]⟩,
    ⟨[86203, 7], [31325, 94421], .contexts [
        ⟨84290, false, false, [], []⟩
      ]⟩,
    ⟨[86203, 9], [22453, 54479, 83765], .contexts [
        ⟨48966, false, false, [], []⟩,
        ⟨120821, false, false, [22453], []⟩
      ]⟩,
    ⟨[86203, 11], [38633, 87219], .contexts [
        ⟨103608, false, false, [], []⟩,
        ⟨110369, false, false, [], []⟩
      ]⟩,
    ⟨[86203, 13], [26157, 91347], .contexts [
        ⟨65722, false, false, [], []⟩,
        ⟨65724, false, false, [], []⟩
      ]⟩,
    ⟨[86203, 15], [86201], .contexts [
        ⟨35661, false, false, [], []⟩,
        ⟨35718, false, false, [], []⟩
      ]⟩,
    ⟨[86209, 1], [86211], .contexts [
        ⟨35674, false, false, [], []⟩,
        ⟨35708, false, false, [], []⟩
      ]⟩,
    ⟨[86209, 3], [21231, 84325], .contexts [
        ⟨44564, false, false, [], []⟩,
        ⟨44572, false, false, [], []⟩
      ]⟩,
    ⟨[86209, 5], [50655, 84811], .contexts [
        ⟨35672, false, false, [], []⟩,
        ⟨116321, false, false, [], []⟩
      ]⟩,
    ⟨[86209, 7], [21767, 21727, 38599, 83085], .contexts [
        ⟨46373, false, false, [], []⟩,
        ⟨46402, false, false, [21767], []⟩,
        ⟨103571, false, false, [21767, 21727], []⟩
      ]⟩,
    ⟨[86209, 9], [18941, 40645, 85657], .contexts [
        ⟨35911, false, false, [], []⟩,
        ⟨105678, false, false, [18941], []⟩
      ]⟩,
    ⟨[86209, 11], [38565, 84505], .contexts [
        ⟨98342, false, false, [], []⟩,
        ⟨103538, false, false, [], []⟩
      ]⟩,
    ⟨[86209, 13], [25265, 38585, 57711, 88515], .contexts [
        ⟨61738, false, false, [], []⟩,
        ⟨160277, false, false, [25265], []⟩
      ]⟩,
    ⟨[86209, 15], [26131, 91357], .contexts [
        ⟨65678, false, false, [], []⟩,
        ⟨65672, false, false, [], []⟩
      ]⟩,
    ⟨[86211, 1], [86209], .contexts [
        ⟨35676, false, false, [], []⟩,
        ⟨35710, false, false, [], []⟩
      ]⟩,
    ⟨[86211, 3], [21205, 84333], .contexts [
        ⟨44529, false, false, [], []⟩,
        ⟨44523, false, false, [], []⟩
      ]⟩,
    ⟨[88191], [39703, 50673, 84809], .contexts [
        ⟨104865, false, false, [], []⟩,
        ⟨116325, false, false, [39703], []⟩
      ]⟩,
    ⟨[86211, 5], [22393, 39703, 50673, 84809], .contexts [
        ⟨48847, true, false, [22390], [5]⟩,
        ⟨28, false, false, [22390, 88191], []⟩,
        ⟨48816, true, false, [], [88191]⟩,
        ⟨162469, false, false, [22393], []⟩
      ]⟩,
    ⟨[86211, 7], [21767, 38543, 38673, 85003], .contexts [
        ⟨46354, true, false, [21764], [7]⟩,
        ⟨38, false, false, [21764, 87791], []⟩,
        ⟨46329, true, false, [], [87791]⟩,
        ⟨158421, false, false, [21767], []⟩
      ]⟩,
    ⟨[86211, 9], [86213], .contexts [
        ⟨35678, false, false, [], []⟩,
        ⟨35706, false, false, [], []⟩
      ]⟩,
    ⟨[86211, 11], [38557, 91269], .contexts [
        ⟨98317, false, false, [], []⟩,
        ⟨103530, false, false, [], []⟩
      ]⟩,
    ⟨[86211, 13], [19895, 86909], .contexts [
        ⟨40481, false, false, [], []⟩,
        ⟨40472, false, false, [], []⟩
      ]⟩,
    ⟨[86211, 15], [26131, 91359], .contexts [
        ⟨65655, false, false, [], []⟩,
        ⟨65670, false, false, [], []⟩
      ]⟩,
    ⟨[86213, 1], [18941, 85935], .contexts [
        ⟨35888, false, false, [], []⟩
      ]⟩,
    ⟨[86213, 3], [21205, 84335], .contexts [
        ⟨44485, false, false, [], []⟩,
        ⟨44521, false, false, [], []⟩
      ]⟩,
    ⟨[86213, 5], [22393, 39703, 88103], .contexts [
        ⟨48820, false, false, [], []⟩,
        ⟨104856, false, false, [22393], []⟩
      ]⟩,
    ⟨[86213, 7], [21767, 87793], .contexts [
        ⟨46332, false, false, [], []⟩,
        ⟨46349, false, false, [], []⟩
      ]⟩,
    ⟨[86213, 9], [86211], .contexts [
        ⟨35680, false, false, [], []⟩,
        ⟨35708, false, false, [], []⟩
      ]⟩,
    ⟨[86213, 11], [18941, 27079, 85879], .contexts [
        ⟨35682, false, false, [], []⟩,
        ⟨57793, false, false, [], []⟩,
        ⟨98323, false, false, [], []⟩
      ]⟩,
    ⟨[86213, 13], [19895, 86911], .contexts [
        ⟨40422, false, false, [], []⟩,
        ⟨40470, false, false, [], []⟩
      ]⟩,
    ⟨[86213, 15], [21651, 38513, 86311], .contexts [
        ⟨45757, false, false, [], []⟩,
        ⟨103492, false, false, [21651], []⟩
      ]⟩,
    ⟨[86231, 1], [2243, 86231], .contexts [
        ⟨36070, false, false, [], []⟩,
        ⟨36065, false, false, [], []⟩
      ]⟩,
    ⟨[86231, 3], [18973, 85619], .contexts [
        ⟨36075, false, false, [], []⟩,
        ⟨36071, false, false, [], []⟩
      ]⟩,
    ⟨[86231, 5], [33813, 95517], .contexts [
        ⟨92219, true, false, [33810], [5]⟩,
        ⟨28, false, false, [33810, 95517], []⟩,
        ⟨92220, true, false, [], [95517]⟩
      ]⟩,
    ⟨[86231, 7], [71949, 96801], .contexts [
        ⟨141190, true, false, [71946], [7]⟩,
        ⟨38, false, false, [71946, 96801], []⟩,
        ⟨141191, true, false, [], [96801]⟩
      ]⟩,
    ⟨[86231, 9], [20639, 85251], .contexts [
        ⟨36057, false, false, [], []⟩,
        ⟨152959, false, false, [], []⟩
      ]⟩,
    ⟨[86231, 11], [86233], .contexts [
        ⟨36078, false, false, [], []⟩,
        ⟨36080, false, false, [], []⟩
      ]⟩,
    ⟨[86231, 13], [30931, 33425, 45397, 87359], .contexts [
        ⟨82552, false, false, [], []⟩,
        ⟨159216, false, false, [30931], []⟩
      ]⟩,
    ⟨[20639, 92047], [20639, 92047], .contexts []⟩,
    ⟨[86231, 15], [20639, 92047], .contexts [
        ⟨69445, false, false, [], []⟩,
        ⟨162491, false, false, [], []⟩
      ]⟩,
    ⟨[86233, 1], [2243, 86233], .contexts [
        ⟨36088, false, false, [], []⟩,
        ⟨36084, false, false, [], []⟩
      ]⟩,
    ⟨[86233, 3], [18973, 85621], .contexts [
        ⟨36094, false, false, [], []⟩,
        ⟨36089, false, false, [], []⟩
      ]⟩,
    ⟨[86233, 5], [33813, 96789], .contexts [
        ⟨140954, true, false, [33810], [5]⟩,
        ⟨28, false, false, [33810, 96789], []⟩,
        ⟨92220, true, false, [], [96789]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2539. -/
def y322TCIndexRaw2539 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86233, 7], [71949, 96803], .contexts [
        ⟨141218, true, false, [71946], [7]⟩,
        ⟨38, false, false, [71946, 96803], []⟩,
        ⟨141191, true, false, [], [96803]⟩
      ]⟩,
    ⟨[86233, 9], [82883], .contexts [
        ⟨36102, false, false, [], []⟩,
        ⟨18098, false, false, [], []⟩
      ]⟩,
    ⟨[86233, 11], [86231], .contexts [
        ⟨36079, false, false, [], []⟩,
        ⟨36058, false, false, [], []⟩
      ]⟩,
    ⟨[86233, 13], [28669, 84743], .contexts [
        ⟨36162, false, false, [], []⟩,
        ⟨74676, false, false, [], []⟩
      ]⟩,
    ⟨[20639, 92049], [20639, 92049], .contexts []⟩,
    ⟨[86233, 15], [20639, 92049], .contexts [
        ⟨69470, true, false, [20636], [15]⟩,
        ⟨1, false, false, [20636, 92049], []⟩,
        ⟨69460, false, false, [], []⟩,
        ⟨162500, false, false, [], []⟩
      ]⟩,
    ⟨[86239, 1], [28669, 84741], .contexts [
        ⟨36171, false, false, [], []⟩,
        ⟨74559, false, false, [], []⟩
      ]⟩,
    ⟨[86239, 3], [86241], .contexts [
        ⟨36173, false, false, [], []⟩,
        ⟨36401, false, false, [], []⟩
      ]⟩,
    ⟨[86239, 5], [49909, 86883], .contexts [
        ⟨115417, false, false, [], []⟩,
        ⟨115410, false, false, [], []⟩
      ]⟩,
    ⟨[86239, 7], [56657, 90395], .contexts [
        ⟨123378, false, false, [], []⟩,
        ⟨123379, false, false, [], []⟩
      ]⟩,
    ⟨[86239, 9], [48919, 89227], .contexts [
        ⟨114276, false, false, [], []⟩,
        ⟨115429, false, false, [], []⟩
      ]⟩,
    ⟨[86239, 11], [49905, 87365], .contexts [
        ⟨115405, false, false, [], []⟩,
        ⟨123396, false, false, [], []⟩
      ]⟩,
    ⟨[86239, 13], [49915, 88939], .contexts [
        ⟨115427, false, false, [], []⟩,
        ⟨115438, false, false, [], []⟩
      ]⟩,
    ⟨[86239, 15], [28669, 84745], .contexts [
        ⟨74671, false, false, [], []⟩,
        ⟨115444, false, false, [], []⟩
      ]⟩,
    ⟨[86241, 1], [18973, 88353], .contexts [
        ⟨50071, false, false, [], []⟩,
        ⟨50357, false, false, [], []⟩
      ]⟩,
    ⟨[86241, 3], [86239], .contexts [
        ⟨36175, false, false, [], []⟩,
        ⟨36403, false, false, [], []⟩
      ]⟩,
    ⟨[86241, 5], [86243], .contexts [
        ⟨36177, false, false, [], []⟩,
        ⟨36399, false, false, [], []⟩
      ]⟩,
    ⟨[86241, 7], [57187, 90181], .contexts [
        ⟨124022, false, false, [], []⟩,
        ⟨124284, false, false, [], []⟩
      ]⟩,
    ⟨[86241, 9], [37423, 62973, 93861], .contexts [
        ⟨102155, false, false, [], []⟩,
        ⟨130834, false, false, [37423], []⟩
      ]⟩,
    ⟨[86241, 11], [62983, 93865], .contexts [
        ⟨130840, false, false, [], []⟩,
        ⟨136748, false, false, [], []⟩
      ]⟩,
    ⟨[86241, 13], [49915, 69347, 88247], .contexts [
        ⟨115443, false, false, [], []⟩,
        ⟨137968, false, false, [49915], []⟩
      ]⟩,
    ⟨[86241, 15], [28669, 84747], .contexts [
        ⟨74777, false, false, [], []⟩,
        ⟨74919, false, false, [], []⟩
      ]⟩,
    ⟨[86243, 1], [86245], .contexts [
        ⟨36181, false, false, [], []⟩,
        ⟨36397, false, false, [], []⟩
      ]⟩,
    ⟨[86243, 3], [63655, 93953], .contexts [
        ⟨131719, false, false, [], []⟩,
        ⟨137252, false, false, [], []⟩
      ]⟩,
    ⟨[86243, 5], [86241], .contexts [
        ⟨36179, false, false, [], []⟩,
        ⟨36401, false, false, [], []⟩
      ]⟩,
    ⟨[86243, 7], [67357, 90071], .contexts [
        ⟨135870, false, false, [], []⟩,
        ⟨137254, false, false, [], []⟩
      ]⟩,
    ⟨[86243, 9], [62963, 87283], .contexts [
        ⟨50078, false, false, [], []⟩,
        ⟨130821, false, false, [], []⟩
      ]⟩,
    ⟨[86243, 11], [43345, 90441], .contexts [
        ⟨108140, false, false, [], []⟩,
        ⟨116456, false, false, [], []⟩
      ]⟩,
    ⟨[86243, 13], [49915, 88943], .contexts [
        ⟨116446, false, false, [], []⟩,
        ⟨116443, false, false, [], []⟩
      ]⟩,
    ⟨[86243, 15], [28669, 84749], .contexts [
        ⟨74929, false, false, [], []⟩,
        ⟨74922, false, false, [], []⟩
      ]⟩,
    ⟨[86245, 1], [86243], .contexts [
        ⟨36183, false, false, [], []⟩,
        ⟨36399, false, false, [], []⟩
      ]⟩,
    ⟨[86245, 3], [35015, 84401], .contexts [
        ⟨95740, false, false, [], []⟩,
        ⟨95747, false, false, [], []⟩
      ]⟩,
    ⟨[86245, 5], [18973, 88353], .contexts [
        ⟨50075, false, false, [], []⟩,
        ⟨50357, false, false, [], []⟩
      ]⟩,
    ⟨[86245, 7], [63153, 66907, 84771], .contexts [
        ⟨131041, false, false, [], []⟩,
        ⟨135328, false, false, [63153], []⟩
      ]⟩,
    ⟨[86245, 9], [86247], .contexts [
        ⟨36185, false, false, [], []⟩,
        ⟨36396, false, false, [], []⟩
      ]⟩,
    ⟨[86245, 11], [43345, 90443], .contexts [
        ⟨108136, false, false, [], []⟩,
        ⟨125205, false, false, [], []⟩
      ]⟩,
    ⟨[86245, 13], [50755, 93649], .contexts [
        ⟨116452, false, false, [], []⟩,
        ⟨116449, false, false, [], []⟩
      ]⟩,
    ⟨[86245, 15], [28669, 84751], .contexts [
        ⟨75054, false, false, [], []⟩,
        ⟨75166, false, false, [], []⟩
      ]⟩,
    ⟨[86247, 1], [66851, 93977], .contexts [
        ⟨135253, false, false, [], []⟩
      ]⟩,
    ⟨[86247, 3], [35015, 84403], .contexts [
        ⟨95752, true, false, [35012], [3]⟩,
        ⟨20, false, false, [35012, 84403], []⟩,
        ⟨95737, true, false, [], [84403]⟩,
        ⟨95749, false, false, [], []⟩
      ]⟩,
    ⟨[86247, 5], [64717, 64757, 86019], .contexts [
        ⟨132896, false, false, [], []⟩,
        ⟨132947, false, false, [64717], []⟩
      ]⟩,
    ⟨[86247, 7], [64731, 84769], .contexts [
        ⟨132910, false, false, [], []⟩
      ]⟩,
    ⟨[86247, 9], [86245], .contexts [
        ⟨36187, false, false, [], []⟩,
        ⟨36397, false, false, [], []⟩
      ]⟩,
    ⟨[86247, 11], [59817, 85799], .contexts [
        ⟨36189, false, false, [], []⟩,
        ⟨127080, false, false, [], []⟩
      ]⟩,
    ⟨[86247, 13], [65543, 83435], .contexts [
        ⟨133785, true, false, [65540], [13]⟩,
        ⟨59, false, false, [65540, 83435], []⟩,
        ⟨133786, true, false, [], [83435]⟩
      ]⟩,
    ⟨[86247, 15], [28669, 84753], .contexts [
        ⟨75173, true, false, [28640], [15]⟩,
        ⟨1, false, false, [28640, 84753], []⟩,
        ⟨74546, true, false, [], [84753]⟩,
        ⟨75168, false, false, [], []⟩
      ]⟩,
    ⟨[86255, 1], [63819, 85785], .contexts [
        ⟨36205, false, false, [], []⟩,
        ⟨131979, false, false, [], []⟩
      ]⟩,
    ⟨[86255, 3], [56429, 83879], .contexts [
        ⟨123115, false, false, [], []⟩,
        ⟨130523, false, false, [], []⟩
      ]⟩,
    ⟨[86255, 5], [63819, 66057, 84551], .contexts [
        ⟨133589, false, false, [], []⟩,
        ⟨135174, false, false, [63819], []⟩
      ]⟩,
    ⟨[86255, 7], [62681, 67771, 87835], .contexts [
        ⟨130531, true, false, [62682], [7]⟩,
        ⟨38, false, false, [62682, 89269], []⟩,
        ⟨130529, false, true, [], [89269]⟩,
        ⟨136334, false, false, [62681], []⟩
      ]⟩,
    ⟨[86255, 9], [33689, 86255], .contexts [
        ⟨91580, false, false, [33684], [86255, 9]⟩,
        ⟨75370, true, false, [33684, 33675], [9]⟩,
        ⟨91663, true, false, [33684], [13, 9]⟩,
        ⟨91663, true, false, [33684], [13, 9]⟩,
        ⟨91662, true, false, [33684], [13, 9]⟩,
        ⟨91627, true, false, [33684], [13, 9]⟩,
        ⟨91625, true, false, [33684], [13, 9]⟩,
        ⟨511, false, false, [33684, 84761], []⟩,
        ⟨64, false, false, [33684, 84761], []⟩,
        ⟨75370, false, false, [33684], []⟩,
        ⟨75362, false, false, [33684], []⟩,
        ⟨75363, false, false, [33684], []⟩,
        ⟨75363, false, false, [33684], []⟩,
        ⟨91664, false, false, [33684, 28641], []⟩,
        ⟨91584, true, false, [], [86255]⟩
      ]⟩,
    ⟨[86255, 11], [61031, 62689, 83443], .contexts [
        ⟨128451, false, false, [], []⟩,
        ⟨132599, false, false, [61031], []⟩
      ]⟩,
    ⟨[86255, 13], [28669, 84761], .contexts [
        ⟨75369, false, false, [], []⟩,
        ⟨130544, false, false, [], []⟩
      ]⟩,
    ⟨[86255, 15], [63907, 83719], .contexts [
        ⟨36203, false, false, [], []⟩,
        ⟨131998, false, false, [], []⟩
      ]⟩,
    ⟨[86267, 1], [86269], .contexts [
        ⟨36226, false, false, [], []⟩,
        ⟨36381, false, false, [], []⟩
      ]⟩,
    ⟨[86267, 3], [45563, 88009], .contexts [
        ⟨110684, true, false, [45560], [3]⟩,
        ⟨56824, false, false, [45560], []⟩,
        ⟨102464, false, false, [45560], []⟩,
        ⟨110686, true, false, [], [37655, 88009]⟩,
        ⟨110687, true, false, [], [88009]⟩
      ]⟩,
    ⟨[86267, 5], [45565, 84321], .contexts [
        ⟨110689, false, false, [], []⟩
      ]⟩,
    ⟨[86267, 7], [45571, 92949], .contexts [
        ⟨110684, true, false, [45560], [7]⟩,
        ⟨102467, true, false, [45560, 37668], [7]⟩,
        ⟨76204, true, false, [45560, 37668, 29262], [7]⟩,
        ⟨38, false, false, [45560, 37668, 29262, 92949], []⟩,
        ⟨76205, true, false, [45560, 37668], [92949]⟩,
        ⟨102468, true, false, [45560], [29265, 92949]⟩,
        ⟨102472, true, false, [45560], [92949]⟩,
        ⟨110685, true, false, [], [37675, 92949]⟩,
        ⟨110694, true, false, [], [92949]⟩
      ]⟩,
    ⟨[86267, 9], [45567, 83315], .contexts [
        ⟨110691, false, false, [], []⟩,
        ⟨121481, false, false, [], []⟩
      ]⟩,
    ⟨[86267, 11], [59565, 85179], .contexts [
        ⟨36224, false, false, [], []⟩,
        ⟨126806, false, false, [], []⟩
      ]⟩,
    ⟨[86267, 13], [45573, 93267], .contexts [
        ⟨110696, false, false, [], []⟩,
        ⟨121600, false, false, [], []⟩
      ]⟩,
    ⟨[86267, 15], [45569, 87065], .contexts [
        ⟨110693, false, false, [], []⟩,
        ⟨121445, false, false, [], []⟩
      ]⟩,
    ⟨[86269, 1], [86267], .contexts [
        ⟨36228, false, false, [], []⟩,
        ⟨36383, false, false, [], []⟩
      ]⟩,
    ⟨[86269, 3], [45549, 88017], .contexts [
        ⟨110674, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2540. -/
def y322TCIndexRaw2540 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86269, 5], [45553, 84319], .contexts [
        ⟨110671, true, false, [45538], [5]⟩,
        ⟨57169, true, false, [45538, 24282], [5]⟩,
        ⟨28, false, false, [45538, 24282, 89697], []⟩,
        ⟨57170, true, false, [45538], [89697]⟩,
        ⟨102490, false, false, [45538, 24285], []⟩,
        ⟨104606, false, false, [45538, 24285], []⟩,
        ⟨104607, true, false, [45538, 24285], [84319]⟩,
        ⟨110656, true, false, [], [24285, 39507, 84319]⟩,
        ⟨110675, true, false, [], [39507, 84319]⟩,
        ⟨110676, true, false, [], [84319]⟩
      ]⟩,
    ⟨[86269, 7], [45555, 92951], .contexts [
        ⟨110671, true, false, [45538], [7]⟩,
        ⟨76174, false, false, [45538], []⟩,
        ⟨110656, true, false, [], [29251, 92951]⟩,
        ⟨110678, true, false, [], [92951]⟩
      ]⟩,
    ⟨[86269, 9], [45545, 85265], .contexts [
        ⟨110671, true, false, [45538], [9]⟩,
        ⟨51501, false, false, [45538], []⟩,
        ⟨51498, false, false, [45538], []⟩,
        ⟨110666, true, false, [], [85265]⟩
      ]⟩,
    ⟨[86269, 11], [45541, 59575, 85177], .contexts [
        ⟨110677, false, false, [], []⟩,
        ⟨126823, false, false, [45541], []⟩
      ]⟩,
    ⟨[86269, 13], [86271], .contexts [
        ⟨36230, false, false, [], []⟩,
        ⟨36380, false, false, [], []⟩
      ]⟩,
    ⟨[86269, 15], [45537, 87063], .contexts [
        ⟨110672, false, false, [], []⟩
      ]⟩,
    ⟨[86271, 1], [45537, 87057], .contexts [
        ⟨110660, false, false, [], []⟩
      ]⟩,
    ⟨[86271, 3], [71945, 96801], .contexts [
        ⟨141176, true, false, [71942], [3]⟩,
        ⟨20, false, false, [71942, 96801], []⟩,
        ⟨141177, true, false, [], [96801]⟩
      ]⟩,
    ⟨[86271, 5], [45541, 84493], .contexts [
        ⟨110655, true, false, [45538], [5]⟩,
        ⟨51421, true, false, [45538, 23012], [5]⟩,
        ⟨40620, false, false, [45538, 23012], []⟩,
        ⟨27133, false, false, [45538, 23012], []⟩,
        ⟨51375, true, false, [45538], [84493]⟩,
        ⟨110667, true, false, [], [84493]⟩
      ]⟩,
    ⟨[86271, 7], [45547, 85619], .contexts [
        ⟨110655, true, false, [45538], [7]⟩,
        ⟨51421, true, false, [45538, 23012], [7]⟩,
        ⟨40624, false, false, [45538, 23012], []⟩,
        ⟨40621, false, false, [45538, 23012], []⟩,
        ⟨51379, true, false, [45538], [85619]⟩,
        ⟨110656, true, false, [], [23015, 85619]⟩,
        ⟨110668, true, false, [], [85619]⟩
      ]⟩,
    ⟨[86271, 9], [45545, 85263], .contexts [
        ⟨110655, true, false, [45538], [9]⟩,
        ⟨51424, false, false, [45538], []⟩,
        ⟨51496, false, false, [45538], []⟩,
        ⟨110666, true, false, [], [85263]⟩
      ]⟩,
    ⟨[86271, 11], [45543, 84453], .contexts [
        ⟨110664, false, false, [], []⟩
      ]⟩,
    ⟨[86271, 13], [86269], .contexts [
        ⟨36232, false, false, [], []⟩,
        ⟨36381, false, false, [], []⟩
      ]⟩,
    ⟨[86271, 15], [86273], .contexts [
        ⟨36234, false, false, [], []⟩,
        ⟨36379, false, false, [], []⟩
      ]⟩,
    ⟨[86273, 1], [86275], .contexts [
        ⟨36238, false, false, [], []⟩,
        ⟨36377, false, false, [], []⟩
      ]⟩,
    ⟨[86273, 3], [45531, 90875], .contexts [
        ⟨110641, true, false, [45524], [3]⟩,
        ⟨63447, true, false, [45524, 25674], [3]⟩,
        ⟨20, false, false, [45524, 25674, 90875], []⟩,
        ⟨63413, true, false, [45524], [90875]⟩,
        ⟨110642, true, false, [], [25677, 90875]⟩,
        ⟨110647, true, false, [], [90875]⟩
      ]⟩,
    ⟨[86273, 5], [45527, 83579], .contexts [
        ⟨110641, true, false, [45524], [5]⟩,
        ⟨58527, false, false, [45524], []⟩,
        ⟨58521, false, false, [45524], []⟩,
        ⟨110642, true, false, [], [23401, 83579]⟩,
        ⟨110645, true, false, [], [83579]⟩
      ]⟩,
    ⟨[86273, 7], [45535, 95759], .contexts [
        ⟨110641, true, false, [45524], [7]⟩,
        ⟨93913, true, false, [45524, 23408], [7]⟩,
        ⟨38, false, false, [45524, 23408, 95759], []⟩,
        ⟨53412, true, false, [45524], [95759]⟩,
        ⟨110642, true, false, [], [23407, 95759]⟩,
        ⟨110651, true, false, [], [95759]⟩
      ]⟩,
    ⟨[86273, 9], [45523, 88973], .contexts [
        ⟨110641, true, false, [45524], [9]⟩,
        ⟨58515, false, false, [45524], []⟩,
        ⟨53270, false, false, [45524], []⟩,
        ⟨110644, true, false, [], [88973]⟩
      ]⟩,
    ⟨[86273, 11], [45523, 89975], .contexts [
        ⟨110641, true, false, [45524], [11]⟩,
        ⟨58539, false, false, [45524], []⟩,
        ⟨58541, false, false, [45524], []⟩,
        ⟨110644, true, false, [], [89975]⟩
      ]⟩,
    ⟨[86273, 13], [45529, 86419], .contexts [
        ⟨110641, true, false, [45524], [13]⟩,
        ⟨58532, false, false, [45524], []⟩,
        ⟨58528, false, false, [45524], []⟩,
        ⟨110642, true, false, [], [23427, 86419]⟩,
        ⟨110646, true, false, [], [86419]⟩
      ]⟩,
    ⟨[86273, 15], [86271], .contexts [
        ⟨36236, false, false, [], []⟩,
        ⟨36380, false, false, [], []⟩
      ]⟩,
    ⟨[86275, 1], [86273], .contexts [
        ⟨36240, false, false, [], []⟩,
        ⟨36379, false, false, [], []⟩
      ]⟩,
    ⟨[86277], [45511, 86275], .contexts [
        ⟨110638, false, false, [], []⟩
      ]⟩,
    ⟨[86275, 3], [45511, 86275], .contexts [
        ⟨36242, false, false, [], []⟩,
        ⟨162583, false, false, [], []⟩
      ]⟩,
    ⟨[86275, 5], [45509, 86279], .contexts [
        ⟨110629, true, false, [45510], [5]⟩,
        ⟨36246, false, false, [45510], []⟩,
        ⟨36376, false, false, [45510], []⟩,
        ⟨110631, true, false, [], [86279]⟩,
        ⟨110631, true, false, [], [86279]⟩,
        ⟨110630, true, false, [], [86279]⟩
      ]⟩,
    ⟨[86275, 7], [45515, 91737], .contexts [
        ⟨110629, true, false, [45510], [7]⟩,
        ⟨110617, true, false, [45510, 45494], [7]⟩,
        ⟨86294, false, false, [45510, 45494], []⟩,
        ⟨86293, false, false, [45510, 45494], []⟩,
        ⟨110618, true, false, [45510], [23863, 91737]⟩,
        ⟨110622, true, false, [45510], [91737]⟩,
        ⟨110630, true, false, [], [45499, 91737]⟩,
        ⟨110633, true, false, [], [91737]⟩
      ]⟩,
    ⟨[86275, 9], [45513, 89305], .contexts [
        ⟨110629, true, false, [45510], [9]⟩,
        ⟨110615, false, false, [45510], []⟩,
        ⟨110630, true, false, [], [45493, 89305]⟩,
        ⟨110632, true, false, [], [89305]⟩
      ]⟩,
    ⟨[86275, 11], [45517, 89977], .contexts [
        ⟨110635, false, false, [], []⟩
      ]⟩,
    ⟨[86275, 13], [45519, 51285, 51303, 84431], .contexts [
        ⟨110629, true, false, [45510], [13]⟩,
        ⟨110617, true, false, [45510, 45494], [13]⟩,
        ⟨86305, false, false, [45510, 45494], []⟩,
        ⟨86304, false, false, [45510, 45494], []⟩,
        ⟨110618, true, false, [45510], [23919, 87555]⟩,
        ⟨110624, true, false, [45510], [87555]⟩,
        ⟨110630, true, false, [], [45503, 87555]⟩,
        ⟨110636, true, false, [], [87555]⟩,
        ⟨156930, false, false, [45519], []⟩
      ]⟩,
    ⟨[86275, 15], [45521, 87057], .contexts [
        ⟨110629, true, false, [45510], [15]⟩,
        ⟨110617, true, false, [45510, 45494], [15]⟩,
        ⟨86306, false, false, [45510, 45494], []⟩,
        ⟨55267, false, false, [45510, 45494], []⟩,
        ⟨110618, true, false, [45510], [23873, 87057]⟩,
        ⟨110625, true, false, [45510], [87057]⟩,
        ⟨110630, true, false, [], [45505, 87057]⟩,
        ⟨110637, true, false, [], [87057]⟩
      ]⟩,
    ⟨[86279, 1], [42501, 83579], .contexts [
        ⟨36250, false, false, [], []⟩,
        ⟨107346, false, false, [], []⟩
      ]⟩,
    ⟨[86279, 3], [45489, 96169], .contexts [
        ⟨110612, false, false, [], []⟩
      ]⟩,
    ⟨[86279, 5], [45511, 86275], .contexts [
        ⟨36248, false, false, [], []⟩,
        ⟨162583, false, false, [], []⟩
      ]⟩,
    ⟨[86279, 7], [42515, 85209], .contexts [
        ⟨107349, true, false, [42506], [7]⟩,
        ⟨98889, false, false, [42506], []⟩,
        ⟨104950, false, false, [42506, 36057], []⟩,
        ⟨107350, true, false, [], [36057, 39855, 85209]⟩,
        ⟨107355, true, false, [], [39855, 85209]⟩,
        ⟨107356, true, false, [], [85209]⟩
      ]⟩,
    ⟨[86279, 9], [42519, 90521], .contexts [
        ⟨107349, true, false, [42506], [9]⟩,
        ⟨99552, true, false, [42506, 36262], [9]⟩,
        ⟨46, false, false, [42506, 36262, 90723], []⟩,
        ⟨99553, true, false, [42506], [90723]⟩,
        ⟨103703, false, false, [42506, 36265], []⟩,
        ⟨107350, true, false, [], [36265, 38703, 90521]⟩,
        ⟨107357, true, false, [], [38703, 90521]⟩,
        ⟨107358, true, false, [], [90521]⟩
      ]⟩,
    ⟨[86279, 11], [45581, 83583], .contexts [
        ⟨110701, false, false, [], []⟩
      ]⟩,
    ⟨[86279, 13], [42505, 51273, 84435], .contexts [
        ⟨107352, false, false, [], []⟩,
        ⟨117074, false, false, [42505], []⟩
      ]⟩,
    ⟨[86279, 15], [42511, 86809], .contexts [
        ⟨107349, true, false, [42506], [15]⟩,
        ⟨98878, true, false, [42506, 36050], [15]⟩,
        ⟨1, false, false, [42506, 36050, 88179], []⟩,
        ⟨98879, true, false, [42506], [88179]⟩,
        ⟨104969, false, false, [42506, 36049], []⟩,
        ⟨107350, true, false, [], [36049, 39873, 86809]⟩,
        ⟨107353, true, false, [], [39873, 86809]⟩,
        ⟨107354, true, false, [], [86809]⟩
      ]⟩,
    ⟨[86285, 1], [86287], .contexts [
        ⟨36260, false, false, [], []⟩,
        ⟨36372, false, false, [], []⟩
      ]⟩,
    ⟨[86285, 3], [42491, 86285], .contexts [
        ⟨107326, true, false, [42482], [3]⟩,
        ⟨41977, false, false, [42482], []⟩,
        ⟨107335, false, false, [42482, 20427], []⟩,
        ⟨107327, true, false, [], [20427, 42483, 86285]⟩,
        ⟨107336, true, false, [], [42483, 86285]⟩,
        ⟨107337, true, false, [], [86285]⟩
      ]⟩,
    ⟨[86285, 5], [42493, 83327], .contexts [
        ⟨107326, true, false, [42482], [5]⟩,
        ⟨42122, false, false, [42482], []⟩,
        ⟨42322, false, false, [42482], []⟩,
        ⟨107327, true, false, [], [20421, 83327]⟩,
        ⟨107338, true, false, [], [83327]⟩
      ]⟩,
    ⟨[86285, 7], [42499, 89305], .contexts [
        ⟨107326, true, false, [42482], [7]⟩,
        ⟨55327, true, false, [42482, 23862], [7]⟩,
        ⟨38, false, false, [42482, 23862, 89305], []⟩,
        ⟨55256, true, false, [42482], [89305]⟩,
        ⟨55324, false, false, [42482], []⟩,
        ⟨107327, true, false, [], [23865, 89305]⟩,
        ⟨107341, true, false, [], [89305]⟩
      ]⟩,
    ⟨[86285, 9], [42481, 91737], .contexts [
        ⟨107326, true, false, [42482], [9]⟩,
        ⟨67395, false, false, [42482], []⟩,
        ⟨67397, false, false, [42482], []⟩,
        ⟨107328, true, false, [], [91737]⟩,
        ⟨107329, true, false, [], [91737]⟩
      ]⟩,
    ⟨[86285, 11], [42501, 83577], .contexts [
        ⟨36258, false, false, [], []⟩,
        ⟨107343, false, false, [], []⟩
      ]⟩,
    ⟨[86285, 13], [42497, 68375, 88741], .contexts [
        ⟨107326, true, false, [42482], [13]⟩,
        ⟨52624, false, false, [42482], []⟩,
        ⟨52638, false, false, [42482, 23281], []⟩,
        ⟨107327, true, false, [], [23281, 23287, 88831]⟩,
        ⟨107339, true, false, [], [23287, 88831]⟩,
        ⟨107340, true, false, [], [88831]⟩,
        ⟨137070, false, false, [42497], []⟩
      ]⟩,
    ⟨[86285, 15], [42485, 86293], .contexts [
        ⟨107331, false, false, [], []⟩
      ]⟩,
    ⟨[86287, 1], [86285], .contexts [
        ⟨36262, false, false, [], []⟩,
        ⟨36373, false, false, [], []⟩
      ]⟩,
    ⟨[86287, 3], [42471, 83357], .contexts [
        ⟨107314, true, false, [42468], [3]⟩,
        ⟨107298, true, false, [42468, 42448], [3]⟩,
        ⟨41581, false, false, [42468, 42448], []⟩,
        ⟨41776, false, false, [42468, 42448], []⟩,
        ⟨41775, false, false, [42468, 42448], []⟩,
        ⟨107301, true, false, [42468], [20277, 83357]⟩,
        ⟨107302, true, false, [42468], [83357]⟩,
        ⟨107315, true, false, [], [42451, 83357]⟩,
        ⟨107317, true, false, [], [83357]⟩
      ]⟩,
    ⟨[86287, 5], [42473, 83329], .contexts [
        ⟨107319, false, false, [], []⟩
      ]⟩,
    ⟨[86287, 7], [42479, 94085], .contexts [
        ⟨107314, true, false, [42468], [7]⟩,
        ⟨107298, true, false, [42468, 42448], [7]⟩,
        ⟨86266, true, false, [42468, 42448, 31890], [7]⟩,
        ⟨38, false, false, [42468, 42448, 31890, 94761], []⟩,
        ⟨86267, true, false, [42468, 42448], [94761]⟩,
        ⟨106239, false, false, [42468, 42448, 31893], []⟩,
        ⟨107299, true, false, [42468], [31893, 41345, 94085]⟩,
        ⟨107309, true, false, [42468], [41345, 94085]⟩,
        ⟨107310, true, false, [42468], [94085]⟩,
        ⟨107315, true, false, [], [42463, 94085]⟩,
        ⟨107322, true, false, [], [94085]⟩
      ]⟩,
    ⟨[86287, 9], [42477, 85677], .contexts [
        ⟨107314, true, false, [42468], [9]⟩,
        ⟨107298, true, false, [42468, 42448], [9]⟩,
        ⟨48726, false, false, [42468, 42448], []⟩,
        ⟨106276, false, false, [42468, 42448, 22333], []⟩,
        ⟨107299, true, false, [42468], [22333, 41397, 85677]⟩,
        ⟨107307, true, false, [42468], [41397, 85677]⟩,
        ⟨107308, true, false, [42468], [85677]⟩,
        ⟨107315, true, false, [], [42459, 85677]⟩,
        ⟨107321, true, false, [], [85677]⟩
      ]⟩,
    ⟨[86287, 11], [42475, 83575], .contexts [
        ⟨107314, true, false, [42468], [11]⟩,
        ⟨107298, true, false, [42468, 42448], [11]⟩,
        ⟨41983, true, false, [42468, 42448, 20432], [11]⟩,
        ⟨53, false, false, [42468, 42448, 20432, 83575], []⟩,
        ⟨41984, true, false, [42468, 42448], [83575]⟩,
        ⟨107299, true, false, [42468], [20435, 83575]⟩,
        ⟨107304, true, false, [42468], [83575]⟩,
        ⟨107315, true, false, [], [42455, 83575]⟩,
        ⟨107320, true, false, [], [83575]⟩
      ]⟩,
    ⟨[86289], [42469, 86287], .contexts [
        ⟨107323, false, false, [], []⟩
      ]⟩,
    ⟨[86287, 13], [42469, 86287], .contexts [
        ⟨36264, false, false, [], []⟩,
        ⟨162613, false, false, [], []⟩
      ]⟩,
    ⟨[86287, 15], [42467, 86291], .contexts [
        ⟨107314, true, false, [42468], [15]⟩,
        ⟨36268, false, false, [42468], []⟩,
        ⟨36371, false, false, [42468], []⟩,
        ⟨107316, true, false, [], [86291]⟩,
        ⟨107316, true, false, [], [86291]⟩,
        ⟨107315, true, false, [], [86291]⟩
      ]⟩,
    ⟨[86291, 1], [86293], .contexts [
        ⟨36272, false, false, [], []⟩,
        ⟨36370, false, false, [], []⟩
      ]⟩,
    ⟨[86291, 3], [42435, 82787], .contexts [
        ⟨107283, true, false, [42430], [3]⟩,
        ⟨49974, false, false, [42430], []⟩,
        ⟨49973, false, false, [42430], []⟩,
        ⟨107284, true, false, [], [22675, 82787]⟩,
        ⟨107289, true, false, [], [82787]⟩
      ]⟩,
    ⟨[86291, 5], [42429, 85259], .contexts [
        ⟨107283, true, false, [42430], [5]⟩,
        ⟨49956, false, false, [42430], []⟩,
        ⟨31146, false, false, [42430], []⟩,
        ⟨107285, true, false, [], [85259]⟩,
        ⟨107285, true, false, [], [85259]⟩,
        ⟨107284, true, false, [], [85259]⟩
      ]⟩,
    ⟨[86291, 7], [42437, 86807], .contexts [
        ⟨107283, true, false, [42430], [7]⟩,
        ⟨49983, false, false, [42430], []⟩,
        ⟨107284, true, false, [], [22681, 86807]⟩,
        ⟨107290, true, false, [], [86807]⟩
      ]⟩,
    ⟨[86291, 9], [42439, 85615], .contexts [
        ⟨107283, true, false, [42430], [9]⟩,
        ⟨49989, false, false, [42430], []⟩,
        ⟨49987, false, false, [42430], []⟩,
        ⟨107284, true, false, [], [20759, 85615]⟩,
        ⟨107291, true, false, [], [85615]⟩
      ]⟩,
    ⟨[86291, 11], [42441, 84489], .contexts [
        ⟨107283, true, false, [42430], [11]⟩,
        ⟨49992, false, false, [42430], []⟩,
        ⟨49990, false, false, [42430], []⟩,
        ⟨107284, true, false, [], [20775, 84489]⟩,
        ⟨107292, true, false, [], [84489]⟩
      ]⟩,
    ⟨[86291, 13], [42445, 89619], .contexts [
        ⟨107283, true, false, [42430], [13]⟩,
        ⟨57062, false, false, [42430], []⟩,
        ⟨102540, false, false, [42430, 24225], []⟩,
        ⟨107284, true, false, [], [24225, 37731, 89619]⟩,
        ⟨107293, true, false, [], [37731, 89619]⟩,
        ⟨107294, true, false, [], [89619]⟩
      ]⟩,
    ⟨[86291, 15], [42469, 86287], .contexts [
        ⟨36270, false, false, [], []⟩,
        ⟨162613, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2541. -/
def y322TCIndexRaw2541 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86293, 1], [86291], .contexts [
        ⟨36274, false, false, [], []⟩,
        ⟨36371, false, false, [], []⟩
      ]⟩,
    ⟨[86293, 3], [42419, 86293], .contexts [
        ⟨36276, false, false, [], []⟩,
        ⟨107280, false, false, [], []⟩
      ]⟩,
    ⟨[86293, 5], [42421, 83325], .contexts [
        ⟨107271, true, false, [42418], [5]⟩,
        ⟨36280, false, false, [42418], []⟩,
        ⟨107256, false, false, [42418], []⟩,
        ⟨107272, true, false, [], [42379, 83325]⟩,
        ⟨107273, true, false, [], [83325]⟩
      ]⟩,
    ⟨[86293, 7], [42427, 89307], .contexts [
        ⟨107271, true, false, [42418], [7]⟩,
        ⟨107259, true, false, [42418, 42406], [7]⟩,
        ⟨55258, false, false, [42418, 42406], []⟩,
        ⟨55316, false, false, [42418, 42406], []⟩,
        ⟨107260, true, false, [42418], [23865, 89307]⟩,
        ⟨107267, true, false, [42418], [89307]⟩,
        ⟨107272, true, false, [], [42413, 89307]⟩,
        ⟨107279, true, false, [], [89307]⟩
      ]⟩,
    ⟨[86293, 9], [42423, 88345], .contexts [
        ⟨107278, false, false, [], []⟩
      ]⟩,
    ⟨[86293, 11], [42425, 84491], .contexts [
        ⟨107271, true, false, [42418], [11]⟩,
        ⟨107259, true, false, [42418, 42406], [11]⟩,
        ⟨42349, false, false, [42418, 42406], []⟩,
        ⟨50019, false, false, [42418, 42406], []⟩,
        ⟨107260, true, false, [42418], [20625, 84491]⟩,
        ⟨107265, true, false, [42418], [84491]⟩,
        ⟨107272, true, false, [], [42409, 84491]⟩,
        ⟨107277, true, false, [], [84491]⟩
      ]⟩,
    ⟨[86293, 13], [42423, 87415], .contexts [
        ⟨107276, false, false, [], []⟩
      ]⟩,
    ⟨[86293, 15], [42423, 42483, 86285], .contexts [
        ⟨107271, true, false, [42418], [15]⟩,
        ⟨107259, true, false, [42418, 42406], [15]⟩,
        ⟨41573, false, false, [42418, 42406], []⟩,
        ⟨41620, false, false, [42418, 42406], []⟩,
        ⟨107262, true, false, [42418], [87419]⟩,
        ⟨107275, true, false, [], [87419]⟩,
        ⟨107334, false, false, [42423], []⟩
      ]⟩,
    ⟨[86309, 1], [86311], .contexts [
        ⟨36302, false, false, [], []⟩,
        ⟨36356, false, false, [], []⟩
      ]⟩,
    ⟨[86309, 3], [21845, 85705], .contexts [
        ⟨46610, false, false, [], []⟩
      ]⟩,
    ⟨[86309, 5], [38515, 86619], .contexts [
        ⟨109943, false, false, [], []⟩,
        ⟨109942, false, false, [], []⟩
      ]⟩,
    ⟨[86309, 7], [22817, 39009, 85505], .contexts [
        ⟨50613, false, false, [], []⟩,
        ⟨104070, false, false, [22817], []⟩
      ]⟩,
    ⟨[86309, 9], [22865, 84465], .contexts [
        ⟨50645, true, false, [22866], [9]⟩,
        ⟨46, false, false, [22866, 84465], []⟩,
        ⟨50646, true, false, [], [84465]⟩
      ]⟩,
    ⟨[86309, 11], [38523, 91365], .contexts [
        ⟨109947, false, false, [], []⟩,
        ⟨109946, false, false, [], []⟩
      ]⟩,
    ⟨[86309, 13], [45963, 83681], .contexts [
        ⟨111245, false, false, [], []⟩
      ]⟩,
    ⟨[86309, 15], [39909, 85935], .contexts [
        ⟨36300, false, false, [], []⟩,
        ⟨104998, false, false, [], []⟩
      ]⟩,
    ⟨[86311, 1], [86309], .contexts [
        ⟨36304, false, false, [], []⟩,
        ⟨36358, false, false, [], []⟩
      ]⟩,
    ⟨[86311, 3], [86313], .contexts [
        ⟨36306, false, false, [], []⟩,
        ⟨36354, false, false, [], []⟩
      ]⟩,
    ⟨[86311, 5], [38515, 86617], .contexts [
        ⟨103491, false, false, [], []⟩,
        ⟨109940, false, false, [], []⟩
      ]⟩,
    ⟨[86311, 7], [22817, 43855, 85507], .contexts [
        ⟨50576, false, false, [], []⟩,
        ⟨108650, false, false, [22817], []⟩
      ]⟩,
    ⟨[86311, 9], [29905, 38529, 91359], .contexts [
        ⟨78371, false, false, [], []⟩,
        ⟨103501, false, false, [29905], []⟩
      ]⟩,
    ⟨[86311, 11], [38523, 91363], .contexts [
        ⟨103496, false, false, [], []⟩,
        ⟨109944, false, false, [], []⟩
      ]⟩,
    ⟨[86311, 13], [22855, 86311], .contexts [
        ⟨50618, false, false, [], []⟩
      ]⟩,
    ⟨[86311, 15], [38521, 86213], .contexts [
        ⟨103489, true, false, [38512], [15]⟩,
        ⟨45755, false, false, [38512], []⟩,
        ⟨65646, false, false, [38512], []⟩,
        ⟨103479, true, false, [], [21649, 86213]⟩,
        ⟨103494, true, false, [], [86213]⟩
      ]⟩,
    ⟨[86313, 1], [19031, 86317], .contexts [
        ⟨36500, false, false, [], []⟩,
        ⟨36488, false, false, [], []⟩
      ]⟩,
    ⟨[86313, 3], [86311], .contexts [
        ⟨36308, false, false, [], []⟩,
        ⟨36356, false, false, [], []⟩
      ]⟩,
    ⟨[86315], [19033, 86313], .contexts [
        ⟨46600, false, false, [], []⟩
      ]⟩,
    ⟨[86313, 5], [19033, 86313], .contexts [
        ⟨36310, false, false, [], []⟩,
        ⟨162650, false, false, [], []⟩
      ]⟩,
    ⟨[86313, 7], [22817, 38503, 85509], .contexts [
        ⟨50525, false, false, [], []⟩,
        ⟨103473, false, false, [22817], []⟩
      ]⟩,
    ⟨[86313, 9], [38517, 87309], .contexts [
        ⟨103482, false, false, [], []⟩,
        ⟨109931, false, false, [], []⟩
      ]⟩,
    ⟨[86313, 11], [38517, 87313], .contexts [
        ⟨103478, true, false, [38512], [11]⟩,
        ⟨45684, true, false, [38512, 21622], [11]⟩,
        ⟨40943, false, false, [38512, 21622], []⟩,
        ⟨40991, false, false, [38512, 21622], []⟩,
        ⟨45686, true, false, [38512], [87313]⟩,
        ⟨103481, true, false, [], [87313]⟩
      ]⟩,
    ⟨[86313, 13], [22851, 86313], .contexts [
        ⟨50579, true, false, [22848], [13]⟩,
        ⟨15654, false, false, [22848, 86313], []⟩,
        ⟨50581, true, false, [], [86313]⟩,
        ⟨50581, true, false, [], [86313]⟩,
        ⟨50580, true, false, [], [86313]⟩
      ]⟩,
    ⟨[86313, 15], [38519, 84335], .contexts [
        ⟨103478, true, false, [38512], [15]⟩,
        ⟨45693, false, false, [38512], []⟩,
        ⟨45751, false, false, [38512], []⟩,
        ⟨103479, true, false, [], [21639, 84335]⟩,
        ⟨103485, true, false, [], [84335]⟩
      ]⟩,
    ⟨[86317, 1], [19033, 86313], .contexts [
        ⟨36315, false, false, [], []⟩,
        ⟨162650, false, false, [], []⟩
      ]⟩,
    ⟨[86317, 3], [21837, 85707], .contexts [
        ⟨46597, true, false, [21834], [3]⟩,
        ⟨20, false, false, [21834, 85707], []⟩,
        ⟨46577, true, false, [], [85707]⟩,
        ⟨46594, false, false, [], []⟩
      ]⟩,
    ⟨[86317, 5], [19033, 86317], .contexts [
        ⟨36494, false, false, [], []⟩,
        ⟨36495, false, false, [], []⟩
      ]⟩,
    ⟨[86317, 7], [22797, 88461], .contexts [
        ⟨50515, true, false, [22798], [7]⟩,
        ⟨38, false, false, [22798, 88461], []⟩,
        ⟨50489, false, true, [], [88461]⟩,
        ⟨50513, false, false, [], []⟩
      ]⟩,
    ⟨[86317, 9], [86319], .contexts [
        ⟨36317, false, false, [], []⟩,
        ⟨36348, false, false, [], []⟩
      ]⟩,
    ⟨[86317, 11], [27429, 39169, 87315], .contexts [
        ⟨83223, true, false, [27426], [11]⟩,
        ⟨83222, true, false, [27426], [11]⟩,
        ⟨83221, true, false, [27426], [11]⟩,
        ⟨83221, true, false, [27426], [11]⟩,
        ⟨83220, true, false, [27426], [11]⟩,
        ⟨83224, true, false, [27426], [11]⟩,
        ⟨83204, true, false, [27426], [13, 11]⟩,
        ⟨83204, true, false, [27426], [13, 11]⟩,
        ⟨83203, true, false, [27426], [13, 11]⟩,
        ⟨83231, true, false, [27426], [13, 11]⟩,
        ⟨83, true, false, [27426, 94187], [11]⟩,
        ⟨82, true, false, [27426, 94187], [11]⟩,
        ⟨83252, false, false, [27426], [11, 11]⟩,
        ⟨53, false, false, [27426, 94189], []⟩,
        ⟨70420, true, false, [], [94189]⟩,
        ⟨104235, false, false, [27429], []⟩
      ]⟩,
    ⟨[86317, 13], [27429, 39163, 85363], .contexts [
        ⟨83224, true, false, [27426], [13]⟩,
        ⟨59, false, false, [27426, 94185], []⟩,
        ⟨70420, true, false, [], [94185]⟩,
        ⟨104221, false, false, [27429], []⟩
      ]⟩,
    ⟨[86317, 15], [43531, 86609], .contexts [
        ⟨108344, true, false, [43532], [15]⟩,
        ⟨38225, false, false, [43532], []⟩,
        ⟨38445, false, false, [43532], []⟩,
        ⟨108345, true, false, [], [86609]⟩,
        ⟨108345, true, false, [], [86609]⟩,
        ⟨108343, false, true, [], [86609]⟩
      ]⟩,
    ⟨[86319, 1], [24071, 89433], .contexts [
        ⟨56051, false, false, [], []⟩
      ]⟩,
    ⟨[86319, 3], [21837, 85709], .contexts [
        ⟨46589, false, false, [], []⟩,
        ⟨46592, false, false, [], []⟩
      ]⟩,
    ⟨[86319, 5], [19031, 86319], .contexts [
        ⟨36485, false, false, [], []⟩,
        ⟨36486, false, false, [], []⟩
      ]⟩,
    ⟨[86319, 7], [22797, 48729, 85417], .contexts [
        ⟨50488, false, false, [], []⟩,
        ⟨114072, false, false, [22797], []⟩
      ]⟩,
    ⟨[86319, 9], [86317], .contexts [
        ⟨36319, false, false, [], []⟩,
        ⟨36350, false, false, [], []⟩
      ]⟩,
    ⟨[86319, 11], [86321], .contexts [
        ⟨36321, false, false, [], []⟩,
        ⟨36346, false, false, [], []⟩
      ]⟩,
    ⟨[86319, 13], [27429, 41181, 85367], .contexts [
        ⟨70419, true, false, [27426], [13]⟩,
        ⟨59, false, false, [27426, 92179], []⟩,
        ⟨70420, true, false, [], [92179]⟩,
        ⟨106095, false, false, [27429], []⟩
      ]⟩,
    ⟨[86319, 15], [24071, 92509], .contexts [
        ⟨72849, true, false, [24068], [15]⟩,
        ⟨1, false, false, [24068, 92509], []⟩,
        ⟨56048, true, false, [], [92509]⟩
      ]⟩,
    ⟨[86321, 1], [86323], .contexts [
        ⟨36325, false, false, [], []⟩,
        ⟨36344, false, false, [], []⟩
      ]⟩,
    ⟨[86321, 3], [21837, 43229, 83807], .contexts [
        ⟨46576, true, false, [21834], [3]⟩,
        ⟨20, false, false, [21834, 85711], []⟩,
        ⟨46577, true, false, [], [85711]⟩,
        ⟨108005, false, false, [21837], []⟩
      ]⟩,
    ⟨[86321, 5], [19033, 86321], .contexts [
        ⟨36479, false, false, [], []⟩,
        ⟨36480, false, false, [], []⟩
      ]⟩,
    ⟨[86321, 7], [21761, 85317], .contexts [
        ⟨46312, false, false, [], []⟩,
        ⟨46306, false, false, [], []⟩
      ]⟩,
    ⟨[86321, 9], [24071, 39245, 86441], .contexts [
        ⟨56059, false, false, [], []⟩,
        ⟨104315, false, false, [24071], []⟩
      ]⟩,
    ⟨[86321, 11], [86319], .contexts [
        ⟨36323, false, false, [], []⟩,
        ⟨36348, false, false, [], []⟩
      ]⟩,
    ⟨[86321, 13], [29951, 39311, 85369], .contexts [
        ⟨78483, true, false, [29948], [13]⟩,
        ⟨59, false, false, [29948, 93283], []⟩,
        ⟨78484, true, false, [], [93283]⟩,
        ⟨104373, false, false, [29951], []⟩
      ]⟩,
    ⟨[86321, 15], [39319, 92579], .contexts [
        ⟨104381, false, false, [], []⟩
      ]⟩,
    ⟨[86323, 1], [86321], .contexts [
        ⟨36327, false, false, [], []⟩,
        ⟨36346, false, false, [], []⟩
      ]⟩,
    ⟨[86323, 3], [21721, 87797], .contexts [
        ⟨46252, false, false, [], []⟩,
        ⟨46248, false, false, [], []⟩
      ]⟩,
    ⟨[86323, 5], [19031, 86323], .contexts [
        ⟨36472, false, false, [], []⟩,
        ⟨36473, false, false, [], []⟩
      ]⟩,
    ⟨[86323, 7], [21761, 85315], .contexts [
        ⟨46280, false, false, [], []⟩,
        ⟨46303, false, false, [], []⟩
      ]⟩,
    ⟨[39323, 95617], [39323, 50901, 92607], .contexts [
        ⟨119997, false, false, [39323], []⟩
      ]⟩,
    ⟨[86323, 9], [39323, 50901, 92607], .contexts [
        ⟨104389, false, false, [], []⟩,
        ⟨162685, false, false, [], []⟩
      ]⟩,
    ⟨[86323, 11], [24053, 89433], .contexts [
        ⟨56030, true, false, [24050], [11]⟩,
        ⟨53, false, false, [24050, 89433], []⟩,
        ⟨55952, true, false, [], [89433]⟩,
        ⟨56028, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2542. -/
def y322TCIndexRaw2542 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86323, 13], [86325], .contexts [
        ⟨36329, false, false, [], []⟩,
        ⟨36341, false, false, [], []⟩
      ]⟩,
    ⟨[86323, 15], [76551, 97269], .contexts [
        ⟨148418, true, false, [50910], [15]⟩,
        ⟨1, false, false, [50910, 97269], []⟩,
        ⟨148419, true, false, [], [97269]⟩
      ]⟩,
    ⟨[86325, 1], [23685, 41235, 85373], .contexts [
        ⟨54644, false, false, [], []⟩,
        ⟨106136, false, false, [23685], []⟩
      ]⟩,
    ⟨[86325, 3], [21721, 47141, 86523], .contexts [
        ⟨46221, false, false, [], []⟩,
        ⟨112524, false, false, [21721], []⟩
      ]⟩,
    ⟨[86325, 5], [19033, 86325], .contexts [
        ⟨36464, false, false, [], []⟩,
        ⟨36465, false, false, [], []⟩
      ]⟩,
    ⟨[86325, 7], [22747, 88469], .contexts [
        ⟨50412, false, false, [], []⟩,
        ⟨62123, false, false, [], []⟩
      ]⟩,
    ⟨[86325, 9], [90617], .contexts [
        ⟨62111, false, false, [], []⟩,
        ⟨62114, false, false, [], []⟩
      ]⟩,
    ⟨[86325, 11], [24053, 89435], .contexts [
        ⟨56001, false, false, [], []⟩,
        ⟨56026, false, false, [], []⟩
      ]⟩,
    ⟨[86325, 13], [86323], .contexts [
        ⟨36331, false, false, [], []⟩,
        ⟨36344, false, false, [], []⟩
      ]⟩,
    ⟨[86325, 15], [41259, 85377], .contexts [
        ⟨36333, false, false, [], []⟩,
        ⟨106192, false, false, [], []⟩
      ]⟩,
    ⟨[86331, 1], [19037, 86331], .contexts [
        ⟨36516, false, false, [], []⟩,
        ⟨36513, false, false, [], []⟩
      ]⟩,
    ⟨[86331, 3], [82731], .contexts [
        ⟨36505, false, false, [], []⟩,
        ⟨15904, false, false, [], []⟩
      ]⟩,
    ⟨[86331, 5], [1739, 86331], .contexts [
        ⟨36520, false, false, [], []⟩,
        ⟨36517, false, false, [], []⟩
      ]⟩,
    ⟨[86331, 7], [18137, 85349], .contexts [
        ⟨36525, false, false, [], []⟩,
        ⟨36521, false, false, [], []⟩
      ]⟩,
    ⟨[86331, 9], [86333], .contexts [
        ⟨36531, false, false, [], []⟩,
        ⟨36533, false, false, [], []⟩
      ]⟩,
    ⟨[86331, 11], [8673, 86331], .contexts [
        ⟨36529, false, false, [], []⟩,
        ⟨36527, false, false, [], []⟩
      ]⟩,
    ⟨[86331, 13], [15355, 87465], .contexts [
        ⟨43726, false, false, [], []⟩
      ]⟩,
    ⟨[86331, 15], [8695, 94311], .contexts [
        ⟨83821, false, false, [], []⟩
      ]⟩,
    ⟨[86333, 1], [46351, 88847], .contexts [
        ⟨111661, false, false, [], []⟩
      ]⟩,
    ⟨[86333, 3], [15095, 82849], .contexts [
        ⟨36539, false, false, [], []⟩,
        ⟨36536, false, false, [], []⟩
      ]⟩,
    ⟨[86333, 5], [1739, 86333], .contexts [
        ⟨36544, false, false, [], []⟩,
        ⟨36540, false, false, [], []⟩
      ]⟩,
    ⟨[86333, 7], [18137, 85351], .contexts [
        ⟨36548, false, false, [], []⟩,
        ⟨36545, false, false, [], []⟩
      ]⟩,
    ⟨[86333, 9], [86331], .contexts [
        ⟨36532, false, false, [], []⟩,
        ⟨36506, false, false, [], []⟩
      ]⟩,
    ⟨[86333, 11], [86335], .contexts [
        ⟨36550, false, false, [], []⟩,
        ⟨36552, false, false, [], []⟩
      ]⟩,
    ⟨[86333, 13], [27449, 92825], .contexts [
        ⟨75655, true, false, [27446], [13]⟩,
        ⟨59, false, false, [27446, 92825], []⟩,
        ⟨70475, true, false, [], [92825]⟩
      ]⟩,
    ⟨[86333, 15], [8695, 48477, 88851], .contexts [
        ⟨83838, true, false, [15358], [15]⟩,
        ⟨1, false, false, [15358, 94313], []⟩,
        ⟨83820, true, false, [], [94313]⟩,
        ⟨113816, false, false, [8695], []⟩
      ]⟩,
    ⟨[86335, 1], [86337], .contexts [
        ⟨36574, false, false, [], []⟩,
        ⟨36576, false, false, [], []⟩
      ]⟩,
    ⟨[86335, 3], [15095, 85325], .contexts [
        ⟨36558, false, false, [], []⟩,
        ⟨36555, false, false, [], []⟩
      ]⟩,
    ⟨[86335, 5], [1739, 86335], .contexts [
        ⟨36564, false, false, [], []⟩,
        ⟨36560, false, false, [], []⟩
      ]⟩,
    ⟨[86335, 7], [18137, 85353], .contexts [
        ⟨36568, false, false, [], []⟩,
        ⟨36565, false, false, [], []⟩
      ]⟩,
    ⟨[86335, 9], [8673, 86335], .contexts [
        ⟨36572, false, false, [], []⟩,
        ⟨36569, false, false, [], []⟩
      ]⟩,
    ⟨[86335, 11], [86333], .contexts [
        ⟨36551, false, false, [], []⟩,
        ⟨36533, false, false, [], []⟩
      ]⟩,
    ⟨[86335, 13], [27449, 41195, 91483], .contexts [
        ⟨70477, false, false, [], []⟩,
        ⟨106103, false, false, [27449], []⟩
      ]⟩,
    ⟨[86335, 15], [30341, 93551], .contexts [
        ⟨79956, true, false, [30338], [15]⟩,
        ⟨1, false, false, [30338, 93551], []⟩,
        ⟨79957, true, false, [], [93551]⟩
      ]⟩,
    ⟨[86337, 1], [86335], .contexts [
        ⟨36575, false, false, [], []⟩,
        ⟨36552, false, false, [], []⟩
      ]⟩,
    ⟨[86337, 3], [19041, 86337], .contexts [
        ⟨36588, false, false, [], []⟩,
        ⟨36581, false, false, [], []⟩
      ]⟩,
    ⟨[86337, 5], [1739, 86337], .contexts [
        ⟨36592, false, false, [], []⟩,
        ⟨36589, false, false, [], []⟩
      ]⟩,
    ⟨[86337, 7], [18137, 85355], .contexts [
        ⟨36596, false, false, [], []⟩,
        ⟨36593, false, false, [], []⟩
      ]⟩,
    ⟨[86337, 9], [86695], .contexts [
        ⟨38541, false, false, [], []⟩,
        ⟨38543, false, false, [], []⟩
      ]⟩,
    ⟨[86337, 11], [41523, 88847], .contexts [
        ⟨106379, true, false, [41520], [11]⟩,
        ⟨88376, false, false, [41520], []⟩,
        ⟨106381, true, false, [], [32511, 88847]⟩,
        ⟨106382, true, false, [], [88847]⟩
      ]⟩,
    ⟨[86337, 13], [86339], .contexts [
        ⟨36599, false, false, [], []⟩,
        ⟨36602, false, false, [], []⟩
      ]⟩,
    ⟨[86337, 15], [30341, 93553], .contexts [
        ⟨79984, false, false, [], []⟩
      ]⟩,
    ⟨[86339, 1], [31025, 39053, 88841], .contexts [
        ⟨83061, false, false, [], []⟩,
        ⟨104108, false, false, [31025], []⟩
      ]⟩,
    ⟨[86339, 3], [19041, 86339], .contexts [
        ⟨36611, false, false, [], []⟩,
        ⟨36606, false, false, [], []⟩
      ]⟩,
    ⟨[86339, 5], [1739, 86339], .contexts [
        ⟨36616, false, false, [], []⟩,
        ⟨36613, false, false, [], []⟩
      ]⟩,
    ⟨[86339, 7], [18137, 85357], .contexts [
        ⟨36620, false, false, [], []⟩,
        ⟨36617, false, false, [], []⟩
      ]⟩,
    ⟨[86339, 9], [21605, 86699], .contexts [
        ⟨45674, false, false, [], []⟩,
        ⟨45667, false, false, [], []⟩
      ]⟩,
    ⟨[86339, 11], [34659, 41131, 88845], .contexts [
        ⟨94888, true, false, [34660], [11]⟩,
        ⟨94785, false, false, [34660], []⟩,
        ⟨94787, false, false, [34660], []⟩,
        ⟨94889, true, false, [], [95967]⟩,
        ⟨94889, true, false, [], [95967]⟩,
        ⟨94887, false, true, [], [95967]⟩,
        ⟨106045, false, false, [34659], []⟩
      ]⟩,
    ⟨[86339, 13], [86337], .contexts [
        ⟨36600, false, false, [], []⟩,
        ⟨36576, false, false, [], []⟩
      ]⟩,
    ⟨[86339, 15], [86341], .contexts [
        ⟨36622, false, false, [], []⟩,
        ⟨36624, false, false, [], []⟩
      ]⟩,
    ⟨[86341, 1], [39045, 84103], .contexts [
        ⟨36642, false, false, [], []⟩,
        ⟨104100, false, false, [], []⟩
      ]⟩,
    ⟨[86341, 3], [19041, 86341], .contexts [
        ⟨36631, false, false, [], []⟩,
        ⟨36627, false, false, [], []⟩
      ]⟩,
    ⟨[86341, 5], [1739, 86341], .contexts [
        ⟨36635, false, false, [], []⟩,
        ⟨36632, false, false, [], []⟩
      ]⟩,
    ⟨[86341, 7], [18137, 85359], .contexts [
        ⟨36639, false, false, [], []⟩,
        ⟨36636, false, false, [], []⟩
      ]⟩,
    ⟨[86341, 9], [21605, 86701], .contexts [
        ⟨45731, false, false, [], []⟩,
        ⟨45725, false, false, [], []⟩
      ]⟩,
    ⟨[86341, 11], [41529, 84107], .contexts [
        ⟨106388, true, false, [41526], [11]⟩,
        ⟨73262, false, false, [41526], []⟩,
        ⟨73259, false, false, [41526], []⟩,
        ⟨106387, true, false, [], [24135, 84107]⟩,
        ⟨106390, true, false, [], [84107]⟩
      ]⟩,
    ⟨[86341, 13], [31229, 38987, 90735], .contexts [
        ⟨83872, true, false, [30356], [13]⟩,
        ⟨59, false, false, [30356, 94315], []⟩,
        ⟨83873, true, false, [], [94315]⟩,
        ⟨104043, false, false, [31229], []⟩
      ]⟩,
    ⟨[86341, 15], [86339], .contexts [
        ⟨36623, false, false, [], []⟩,
        ⟨36602, false, false, [], []⟩
      ]⟩,
    ⟨[86347, 1], [19041, 86347], .contexts [
        ⟨36678, false, false, [], []⟩,
        ⟨36675, false, false, [], []⟩
      ]⟩,
    ⟨[86347, 3], [1739, 86347], .contexts [
        ⟨36674, true, false, [], [3]⟩,
        ⟨166, false, false, [86345], []⟩,
        ⟨169, false, false, [86345], []⟩,
        ⟨36679, false, false, [], [5]⟩,
        ⟨36670, false, false, [1739], []⟩,
        ⟨36680, false, false, [], []⟩,
        ⟨36677, false, false, [1739], []⟩,
        ⟨15871, true, false, [], [86347]⟩,
        ⟨36680, false, false, [], []⟩
      ]⟩,
    ⟨[86347, 5], [43525, 83801], .contexts [
        ⟨36671, false, false, [], []⟩,
        ⟨108339, false, false, [], []⟩
      ]⟩,
    ⟨[86347, 7], [26305, 86347], .contexts [
        ⟨66236, false, false, [], []⟩,
        ⟨66244, false, false, [], []⟩
      ]⟩,
    ⟨[86347, 9], [42195, 85481], .contexts [
        ⟨36682, false, false, [], []⟩,
        ⟨107075, false, false, [], []⟩
      ]⟩,
    ⟨[86347, 11], [39079, 95645], .contexts [
        ⟨104133, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2543. -/
def y322TCIndexRaw2543 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86347, 13], [28161, 85513], .contexts [
        ⟨72921, false, false, [], []⟩,
        ⟨72924, false, false, [], []⟩
      ]⟩,
    ⟨[86347, 15], [35595, 39071, 93055], .contexts [
        ⟨97803, true, false, [35592], [15]⟩,
        ⟨1, false, false, [35592, 96461], []⟩,
        ⟨97804, true, false, [], [96461]⟩,
        ⟨104124, false, false, [35595], []⟩
      ]⟩,
    ⟨[86353, 1], [42257, 83103], .contexts [
        ⟨36694, false, false, [], []⟩,
        ⟨107133, false, false, [], []⟩
      ]⟩,
    ⟨[86353, 3], [42259, 87199], .contexts [
        ⟨107136, true, false, [42260], [3]⟩,
        ⟨71123, true, false, [42260], [3]⟩,
        ⟨20, false, false, [42260, 87199], []⟩,
        ⟨40240, false, false, [42260], []⟩,
        ⟨40239, false, false, [42260], []⟩,
        ⟨107138, true, false, [], [87199]⟩,
        ⟨107138, true, false, [], [87199]⟩,
        ⟨107137, true, false, [], [87199]⟩
      ]⟩,
    ⟨[86353, 5], [42263, 86593], .contexts [
        ⟨107136, true, false, [42260], [5]⟩,
        ⟨71134, false, false, [42260], []⟩,
        ⟨71147, false, false, [42260], []⟩,
        ⟨107137, true, false, [], [27645, 86593]⟩,
        ⟨107139, true, false, [], [86593]⟩
      ]⟩,
    ⟨[86353, 7], [26309, 86353], .contexts [
        ⟨66276, false, false, [], []⟩,
        ⟨66284, false, false, [], []⟩
      ]⟩,
    ⟨[86353, 9], [42265, 83223], .contexts [
        ⟨107143, false, false, [], []⟩
      ]⟩,
    ⟨[86353, 11], [42267, 83795], .contexts [
        ⟨107136, true, false, [42260], [11]⟩,
        ⟨71139, false, false, [42260], []⟩,
        ⟨71138, false, false, [42260], []⟩,
        ⟨107145, true, false, [], [83795]⟩,
        ⟨107144, true, false, [], [83795]⟩
      ]⟩,
    ⟨[86353, 13], [86355], .contexts [
        ⟨36696, false, false, [], []⟩,
        ⟨36889, false, false, [], []⟩
      ]⟩,
    ⟨[86353, 15], [42269, 83107], .contexts [
        ⟨107147, false, false, [], []⟩
      ]⟩,
    ⟨[86355, 1], [28161, 85521], .contexts [
        ⟨72944, true, false, [28162], [1]⟩,
        ⟨8, false, false, [28162, 85521], []⟩,
        ⟨72933, true, false, [], [85521]⟩,
        ⟨72942, false, false, [], []⟩
      ]⟩,
    ⟨[86355, 3], [42267, 83509], .contexts [
        ⟨107149, true, false, [42270], [3]⟩,
        ⟨44702, false, false, [42270], []⟩,
        ⟨21771, false, false, [42270], []⟩,
        ⟨107152, true, false, [], [83509]⟩
      ]⟩,
    ⟨[86355, 5], [42275, 87575], .contexts [
        ⟨107149, true, false, [42270], [5]⟩,
        ⟨44721, false, false, [42270], []⟩,
        ⟨107150, true, false, [], [15065, 87575]⟩,
        ⟨107155, true, false, [], [87575]⟩
      ]⟩,
    ⟨[86355, 7], [26305, 86355], .contexts [
        ⟨36696, true, false, [], [7]⟩,
        ⟨66285, true, false, [26308], [13, 7]⟩,
        ⟨66285, true, false, [26308], [13, 7]⟩,
        ⟨66284, true, false, [26308], [13, 7]⟩,
        ⟨66276, true, false, [26308], [13, 7]⟩,
        ⟨66275, true, false, [26308], [13, 7]⟩,
        ⟨518, false, false, [26308, 86353], []⟩,
        ⟨64, false, false, [26308, 86353], []⟩,
        ⟨66286, false, false, [26308], []⟩,
        ⟨36889, false, false, [26308], []⟩,
        ⟨36701, false, false, [26308], []⟩,
        ⟨36701, false, false, [26308], []⟩,
        ⟨66287, false, false, [26308], []⟩,
        ⟨66264, true, false, [], [86355]⟩
      ]⟩,
    ⟨[86355, 9], [42273, 84379], .contexts [
        ⟨107149, true, false, [42270], [9]⟩,
        ⟨44711, true, false, [42270, 21270], [9]⟩,
        ⟨46, false, false, [42270, 21270, 84379], []⟩,
        ⟨44709, false, true, [42270], [84379]⟩,
        ⟨107150, true, false, [], [21269, 84379]⟩,
        ⟨107154, true, false, [], [84379]⟩
      ]⟩,
    ⟨[86355, 11], [42267, 85105], .contexts [
        ⟨107149, true, false, [42270], [11]⟩,
        ⟨44697, true, false, [42270], [11]⟩,
        ⟨53, false, false, [42270, 85105], []⟩,
        ⟨30204, false, false, [42270], []⟩,
        ⟨30203, false, false, [42270], []⟩,
        ⟨107152, true, false, [], [85105]⟩
      ]⟩,
    ⟨[86355, 13], [86353], .contexts [
        ⟨36698, false, false, [], []⟩,
        ⟨36890, false, false, [], []⟩
      ]⟩,
    ⟨[86355, 15], [28161, 42281, 85221], .contexts [
        ⟨36700, false, false, [], []⟩,
        ⟨72953, false, false, [], []⟩,
        ⟨107159, false, false, [28161], []⟩
      ]⟩,
    ⟨[86363, 1], [42565, 85247], .contexts [
        ⟨36714, false, false, [], []⟩,
        ⟨107398, false, false, [], []⟩
      ]⟩,
    ⟨[86363, 3], [42559, 85675], .contexts [
        ⟨107388, true, false, [42554], [3]⟩,
        ⟨105732, true, false, [42554, 40706], [3]⟩,
        ⟨69197, false, false, [42554, 40706], []⟩,
        ⟨105615, false, false, [42554, 40706, 27055], []⟩,
        ⟨105728, true, false, [42554], [27055, 40607, 85675]⟩,
        ⟨105733, true, false, [42554], [40607, 85675]⟩,
        ⟨105734, true, false, [42554], [85675]⟩,
        ⟨107389, true, false, [], [40715, 85675]⟩,
        ⟨107391, true, false, [], [85675]⟩
      ]⟩,
    ⟨[86363, 5], [42547, 83783], .contexts [
        ⟨36712, false, false, [], []⟩,
        ⟨107384, false, false, [], []⟩
      ]⟩,
    ⟨[86363, 7], [42561, 90873], .contexts [
        ⟨107388, true, false, [42554], [7]⟩,
        ⟨105732, true, false, [42554, 40706], [7]⟩,
        ⟨69208, false, false, [42554, 40706], []⟩,
        ⟨69205, false, false, [42554, 40706], []⟩,
        ⟨105728, true, false, [42554], [20637, 90873]⟩,
        ⟨105735, true, false, [42554], [90873]⟩,
        ⟨107389, true, false, [], [40719, 90873]⟩,
        ⟨107392, true, false, [], [90873]⟩
      ]⟩,
    ⟨[86363, 9], [42565, 92047], .contexts [
        ⟨107388, true, false, [42554], [9]⟩,
        ⟨105732, true, false, [42554, 40706], [9]⟩,
        ⟨69417, false, false, [42554, 40706], []⟩,
        ⟨69419, false, false, [42554, 40706], []⟩,
        ⟨105738, true, false, [42554], [92047]⟩,
        ⟨107396, true, false, [], [92047]⟩
      ]⟩,
    ⟨[86363, 11], [42557, 42573, 47713, 84037], .contexts [
        ⟨107388, true, false, [42554], [11]⟩,
        ⟨68916, false, false, [42554], []⟩,
        ⟨105743, false, false, [42554], []⟩,
        ⟨107389, true, false, [], [40723, 87035]⟩,
        ⟨107390, true, false, [], [87035]⟩,
        ⟨152962, false, false, [42557], []⟩
      ]⟩,
    ⟨[86363, 13], [42563, 87935], .contexts [
        ⟨107388, true, false, [42554], [13]⟩,
        ⟨105732, true, false, [42554, 40706], [13]⟩,
        ⟨69217, false, false, [42554, 40706], []⟩,
        ⟨69214, false, false, [42554, 40706], []⟩,
        ⟨105728, true, false, [42554], [21871, 87935]⟩,
        ⟨105736, true, false, [42554], [87935]⟩,
        ⟨107389, true, false, [], [40721, 87935]⟩,
        ⟨107393, true, false, [], [87935]⟩
      ]⟩,
    ⟨[86363, 15], [42565, 85251], .contexts [
        ⟨107397, false, false, [], []⟩
      ]⟩,
    ⟨[86369, 1], [47713, 84037], .contexts [
        ⟨36724, false, false, [], []⟩,
        ⟨113110, false, false, [], []⟩
      ]⟩,
    ⟨[86369, 3], [42571, 82679], .contexts [
        ⟨107404, true, false, [42572], [3]⟩,
        ⟨39032, false, false, [42572], []⟩,
        ⟨15292, false, false, [42572], []⟩,
        ⟨107408, true, false, [], [82679]⟩
      ]⟩,
    ⟨[86369, 5], [42571, 86805], .contexts [
        ⟨107404, true, false, [42572], [5]⟩,
        ⟨39050, false, false, [42572], []⟩,
        ⟨39053, false, false, [42572], []⟩,
        ⟨107408, true, false, [], [86805]⟩
      ]⟩,
    ⟨[86369, 7], [42577, 88029], .contexts [
        ⟨107404, true, false, [42572], [7]⟩,
        ⟨48088, false, false, [42572], []⟩,
        ⟨48080, false, false, [42572], []⟩,
        ⟨107411, true, false, [], [88029]⟩
      ]⟩,
    ⟨[86369, 9], [42579, 88601], .contexts [
        ⟨107404, true, false, [42572], [9]⟩,
        ⟨51242, true, false, [42572, 22962], [9]⟩,
        ⟨46, false, false, [42572, 22962, 88601], []⟩,
        ⟨51243, true, false, [42572], [88601]⟩,
        ⟨107405, true, false, [], [22965, 88601]⟩,
        ⟨107412, true, false, [], [88601]⟩
      ]⟩,
    ⟨[86369, 11], [42567, 85247], .contexts [
        ⟨36722, false, false, [], []⟩,
        ⟨107401, false, false, [], []⟩
      ]⟩,
    ⟨[86369, 13], [42575, 85237], .contexts [
        ⟨107404, true, false, [42572], [13]⟩,
        ⟨39042, false, false, [42572], []⟩,
        ⟨39062, false, false, [42572], []⟩,
        ⟨107405, true, false, [], [19503, 85237]⟩,
        ⟨107409, true, false, [], [85237]⟩
      ]⟩,
    ⟨[86369, 15], [42571, 82877], .contexts [
        ⟨107404, true, false, [42572], [15]⟩,
        ⟨39047, false, false, [42572], []⟩,
        ⟨17791, false, false, [42572], []⟩,
        ⟨107408, true, false, [], [82877]⟩
      ]⟩,
    ⟨[86385, 1], [48073, 86385], .contexts [
        ⟨113397, false, false, [], []⟩
      ]⟩,
    ⟨[86385, 3], [48077, 48415, 84141], .contexts [
        ⟨113403, true, false, [48074], [3]⟩,
        ⟨20, false, false, [48074, 87097], []⟩,
        ⟨113404, true, false, [], [87097]⟩,
        ⟨113751, false, false, [48077], []⟩
      ]⟩,
    ⟨[86385, 5], [48071, 83007], .contexts [
        ⟨113424, false, false, [], []⟩
      ]⟩,
    ⟨[86385, 7], [48083, 86385], .contexts [
        ⟨113405, false, false, [48078], [86385, 7]⟩,
        ⟨107452, true, false, [48078, 17767], [7]⟩,
        ⟨34024, true, false, [48078], [9, 7]⟩,
        ⟨34024, true, false, [48078], [9, 7]⟩,
        ⟨34023, true, false, [48078], [9, 7]⟩,
        ⟨34027, true, false, [48078], [9, 7]⟩,
        ⟨34025, true, false, [48078], [9, 7]⟩,
        ⟨579, false, false, [48078, 85861], []⟩,
        ⟨113401, false, false, [48078], []⟩,
        ⟨113400, false, false, [48078], []⟩,
        ⟨113394, false, false, [48078, 42617], []⟩,
        ⟨113406, true, false, [], [42617, 86385]⟩,
        ⟨113407, true, false, [], [86385]⟩
      ]⟩,
    ⟨[86385, 9], [42615, 85861], .contexts [
        ⟨36749, false, false, [], []⟩,
        ⟨107450, false, false, [], []⟩
      ]⟩,
    ⟨[86385, 11], [86387], .contexts [
        ⟨36751, false, false, [], []⟩,
        ⟨36874, false, false, [], []⟩
      ]⟩,
    ⟨[86385, 13], [56061, 56475, 84697], .contexts [
        ⟨122692, false, false, [], []⟩,
        ⟨123183, false, false, [56061], []⟩
      ]⟩,
    ⟨[86385, 15], [48091, 83465], .contexts [
        ⟨113415, true, false, [48088], [15]⟩,
        ⟨1, false, false, [48088, 83465], []⟩,
        ⟨113416, true, false, [], [83465]⟩
      ]⟩,
    ⟨[86389], [48945, 86387], .contexts [
        ⟨123434, false, false, [], []⟩
      ]⟩,
    ⟨[86387, 1], [48945, 86387], .contexts [
        ⟨36755, false, false, [], []⟩,
        ⟨162794, false, false, [], []⟩
      ]⟩,
    ⟨[86387, 3], [48941, 84133], .contexts [
        ⟨114291, true, false, [48930], [3]⟩,
        ⟨87007, false, false, [48930], []⟩,
        ⟨113756, false, false, [48930], []⟩,
        ⟨114294, true, false, [], [48411, 84133]⟩,
        ⟨114301, true, false, [], [84133]⟩
      ]⟩,
    ⟨[86387, 5], [48935, 83009], .contexts [
        ⟨114291, true, false, [48930], [5]⟩,
        ⟨86998, false, false, [48930], []⟩,
        ⟨87024, false, false, [48930], []⟩,
        ⟨114292, true, false, [], [32085, 83009]⟩,
        ⟨114298, true, false, [], [83009]⟩
      ]⟩,
    ⟨[86387, 7], [48939, 86387], .contexts [
        ⟨114291, true, false, [48930], [7]⟩,
        ⟨87005, false, false, [48930], []⟩,
        ⟨114297, false, false, [48930, 18625], []⟩,
        ⟨114292, true, false, [], [18625, 48931, 86387]⟩,
        ⟨114299, true, false, [], [48931, 86387]⟩,
        ⟨114300, true, false, [], [86387]⟩
      ]⟩,
    ⟨[86387, 9], [48929, 88619], .contexts [
        ⟨114287, false, false, [], []⟩,
        ⟨123423, false, false, [], []⟩
      ]⟩,
    ⟨[86387, 11], [86385], .contexts [
        ⟨36753, false, false, [], []⟩,
        ⟨36875, false, false, [], []⟩
      ]⟩,
    ⟨[86387, 13], [48947, 86391], .contexts [
        ⟨114307, false, false, [], []⟩,
        ⟨123439, false, false, [], []⟩
      ]⟩,
    ⟨[86387, 15], [48933, 51087, 56161, 56185, 86495], .contexts [
        ⟨114295, false, false, [], []⟩,
        ⟨155165, false, false, [48933], []⟩
      ]⟩,
    ⟨[86391, 1], [56201, 86489], .contexts [
        ⟨122846, false, false, [], []⟩,
        ⟨123437, false, false, [], []⟩
      ]⟩,
    ⟨[86391, 3], [50319, 83831], .contexts [
        ⟨115868, true, false, [50316], [3]⟩,
        ⟨20, false, false, [50316, 83831], []⟩,
        ⟨115869, true, false, [], [83831]⟩
      ]⟩,
    ⟨[86391, 5], [50041, 83013], .contexts [
        ⟨115566, true, false, [50038], [5]⟩,
        ⟨28, false, false, [50038, 83013], []⟩,
        ⟨115567, true, false, [], [83013]⟩
      ]⟩,
    ⟨[86391, 7], [50383, 86391], .contexts [
        ⟨115939, false, false, [], []⟩,
        ⟨124514, false, false, [], []⟩
      ]⟩,
    ⟨[86391, 9], [48955, 86885], .contexts [
        ⟨114312, false, false, [], []⟩
      ]⟩,
    ⟨[86391, 11], [56057, 56475, 84697], .contexts [
        ⟨122686, false, false, [], []⟩,
        ⟨123183, false, false, [56057], []⟩
      ]⟩,
    ⟨[86391, 13], [48945, 86387], .contexts [
        ⟨36760, false, false, [], []⟩,
        ⟨162794, false, false, [], []⟩
      ]⟩,
    ⟨[86391, 15], [86393], .contexts [
        ⟨36762, false, false, [], []⟩,
        ⟨36870, false, false, [], []⟩
      ]⟩,
    ⟨[86393, 1], [86395], .contexts [
        ⟨36766, false, false, [], []⟩,
        ⟨36868, false, false, [], []⟩
      ]⟩,
    ⟨[86393, 3], [50283, 91371], .contexts [
        ⟨115829, false, false, [], []⟩
      ]⟩,
    ⟨[86393, 5], [50299, 83015], .contexts [
        ⟨115846, true, false, [50296], [5]⟩,
        ⟨28, false, false, [50296, 83015], []⟩,
        ⟨115847, true, false, [], [83015]⟩
      ]⟩,
    ⟨[86393, 7], [50305, 86393], .contexts [
        ⟨115848, false, false, [50300], [86393, 7]⟩,
        ⟨115830, true, false, [50300, 23061], [7]⟩,
        ⟨65821, true, false, [50300], [3, 7]⟩,
        ⟨14911, false, false, [50300, 91371], []⟩,
        ⟨115840, false, false, [50300], []⟩,
        ⟨115838, false, false, [50300], []⟩,
        ⟨115843, false, false, [50300, 50281], []⟩,
        ⟨115849, true, false, [], [50281, 86393]⟩,
        ⟨115850, true, false, [], [86393]⟩
      ]⟩,
    ⟨[86393, 9], [54965, 86877], .contexts [
        ⟨121358, true, false, [54962], [9]⟩,
        ⟨46, false, false, [54962, 86877], []⟩,
        ⟨121359, true, false, [], [86877]⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2544. -/
def y322TCIndexRaw2544 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86393, 11], [49439, 83773], .contexts [
        ⟨114882, false, false, [], []⟩
      ]⟩,
    ⟨[86393, 13], [49437, 56545, 84685], .contexts [
        ⟨114877, false, false, [], []⟩,
        ⟨123242, false, false, [49437], []⟩
      ]⟩,
    ⟨[86393, 15], [86391], .contexts [
        ⟨36764, false, false, [], []⟩,
        ⟨36872, false, false, [], []⟩
      ]⟩,
    ⟨[86395, 1], [86393], .contexts [
        ⟨36768, false, false, [], []⟩,
        ⟨36870, false, false, [], []⟩
      ]⟩,
    ⟨[86395, 3], [86397], .contexts [
        ⟨36770, false, false, [], []⟩,
        ⟨36866, false, false, [], []⟩
      ]⟩,
    ⟨[86395, 5], [50521, 83017], .contexts [
        ⟨116113, false, false, [], []⟩,
        ⟨125067, false, false, [], []⟩
      ]⟩,
    ⟨[86395, 7], [50519, 86395], .contexts [
        ⟨116111, false, false, [], []⟩,
        ⟨123123, false, false, [], []⟩
      ]⟩,
    ⟨[86395, 9], [51693, 91977], .contexts [
        ⟨117504, false, false, [], []⟩,
        ⟨123127, false, false, [], []⟩
      ]⟩,
    ⟨[86395, 11], [51697, 83771], .contexts [
        ⟨117501, true, false, [51694], [11]⟩,
        ⟨68885, false, false, [51694], []⟩,
        ⟨105794, false, false, [51694], []⟩,
        ⟨105793, false, false, [51694], []⟩,
        ⟨117503, true, false, [], [40769, 83771]⟩,
        ⟨117505, true, false, [], [83771]⟩
      ]⟩,
    ⟨[86395, 13], [50523, 86755], .contexts [
        ⟨116106, true, false, [50456], [13]⟩,
        ⟨114756, true, false, [50456, 49328], [13]⟩,
        ⟨59, false, false, [50456, 49328, 86755], []⟩,
        ⟨114752, true, false, [50456], [86755]⟩,
        ⟨116041, true, false, [], [49331, 86755]⟩,
        ⟨116114, true, false, [], [86755]⟩
      ]⟩,
    ⟨[86395, 15], [56201, 86489], .contexts [
        ⟨125066, false, false, [], []⟩,
        ⟨123437, false, false, [], []⟩
      ]⟩,
    ⟨[86397, 1], [50311, 50447, 87347], .contexts [
        ⟨115861, false, false, [], []⟩,
        ⟨116034, false, false, [50311], []⟩
      ]⟩,
    ⟨[86397, 3], [86395], .contexts [
        ⟨36772, false, false, [], []⟩,
        ⟨36868, false, false, [], []⟩
      ]⟩,
    ⟨[86397, 5], [54367, 84157], .contexts [
        ⟨36774, false, false, [], []⟩,
        ⟨120675, false, false, [], []⟩
      ]⟩,
    ⟨[86397, 7], [50315, 86397], .contexts [
        ⟨115858, true, false, [50308], [7]⟩,
        ⟨95261, true, false, [50308], [7]⟩,
        ⟨95261, true, false, [50308], [7]⟩,
        ⟨95259, true, false, [50308], [7]⟩,
        ⟨104, false, false, [50308, 95979], []⟩,
        ⟨105, false, false, [50308, 95979], []⟩,
        ⟨95251, false, false, [50308], [1]⟩,
        ⟨95252, false, false, [50308], [1]⟩,
        ⟨95253, false, false, [50308, 34831], [1]⟩,
        ⟨95236, true, false, [50308], [95979, 1]⟩,
        ⟨95249, false, false, [50308], [1]⟩,
        ⟨95250, false, false, [50308], [1]⟩,
        ⟨95250, false, false, [50308], [1]⟩,
        ⟨95259, false, false, [50308, 34831], []⟩,
        ⟨95236, true, false, [50308], [95981]⟩,
        ⟨115862, false, false, [50308, 34831], []⟩,
        ⟨115856, true, false, [], [34831, 50309, 86397]⟩,
        ⟨115863, true, false, [], [50309, 86397]⟩,
        ⟨115864, true, false, [], [86397]⟩
      ]⟩,
    ⟨[86397, 9], [57621, 58537, 91659], .contexts [
        ⟨124513, false, false, [], []⟩,
        ⟨125531, false, false, [57621], []⟩
      ]⟩,
    ⟨[86397, 11], [50461, 51161, 85303], .contexts [
        ⟨116043, false, false, [], []⟩,
        ⟨116916, false, false, [50461], []⟩
      ]⟩,
    ⟨[86397, 13], [50311, 50467, 86757], .contexts [
        ⟨115865, false, false, [], []⟩,
        ⟨116047, false, false, [50311], []⟩
      ]⟩,
    ⟨[86397, 15], [62411, 83261], .contexts [
        ⟨130171, false, false, [], []⟩
      ]⟩,
    ⟨[86409, 1], [23331, 86409], .contexts [
        ⟨52773, false, false, [], []⟩,
        ⟨52768, false, false, [], []⟩
      ]⟩,
    ⟨[86409, 3], [28981, 90499], .contexts [
        ⟨75307, true, false, [28978], [3]⟩,
        ⟨20, false, false, [28978, 90499], []⟩,
        ⟨75308, true, false, [], [90499]⟩
      ]⟩,
    ⟨[86409, 5], [75909, 97225], .contexts [
        ⟨147543, true, false, [75906], [5]⟩,
        ⟨28, false, false, [75906, 97225], []⟩,
        ⟨147544, true, false, [], [97225]⟩
      ]⟩,
    ⟨[86409, 7], [73479, 96923], .contexts [
        ⟨143602, true, false, [73476], [7]⟩,
        ⟨38, false, false, [73476, 96923], []⟩,
        ⟨143603, true, false, [], [96923]⟩
      ]⟩,
    ⟨[86409, 9], [23335, 86409], .contexts [
        ⟨52779, false, false, [], []⟩,
        ⟨52776, false, false, [], []⟩
      ]⟩,
    ⟨[86409, 11], [71669, 91891], .contexts [
        ⟨140536, true, false, [71666], [11]⟩,
        ⟨53, false, false, [71666, 91891], []⟩,
        ⟨140537, true, false, [], [91891]⟩
      ]⟩,
    ⟨[86409, 13], [57805, 83851], .contexts [
        ⟨36796, false, false, [], []⟩,
        ⟨124725, false, false, [], []⟩
      ]⟩,
    ⟨[86409, 15], [86411], .contexts [
        ⟨36798, false, false, [], []⟩,
        ⟨36853, false, false, [], []⟩
      ]⟩,
    ⟨[86413], [23331, 86411], .contexts [
        ⟨52757, false, false, [], []⟩
      ]⟩,
    ⟨[86411, 1], [23331, 86411], .contexts [
        ⟨36802, false, false, [], []⟩,
        ⟨162843, false, false, [], []⟩
      ]⟩,
    ⟨[86411, 3], [23329, 86415], .contexts [
        ⟨52751, false, false, [], []⟩
      ]⟩,
    ⟨[86411, 5], [60979, 95299], .contexts [
        ⟨128383, false, false, [], []⟩,
        ⟨134959, false, false, [], []⟩
      ]⟩,
    ⟨[86411, 7], [72843, 96871], .contexts [
        ⟨142623, false, false, [], []⟩
      ]⟩,
    ⟨[86411, 9], [23335, 86411], .contexts [
        ⟨52763, false, false, [], []⟩,
        ⟨52774, false, false, [], []⟩
      ]⟩,
    ⟨[86411, 11], [76605, 97275], .contexts [
        ⟨148500, true, false, [76602], [11]⟩,
        ⟨53, false, false, [76602, 97275], []⟩,
        ⟨148501, true, false, [], [97275]⟩
      ]⟩,
    ⟨[86411, 13], [28985, 55307, 55317, 83281], .contexts [
        ⟨75331, false, false, [], []⟩,
        ⟨158311, false, false, [28985], []⟩
      ]⟩,
    ⟨[86411, 15], [86409], .contexts [
        ⟨36800, false, false, [], []⟩,
        ⟨36855, false, false, [], []⟩
      ]⟩,
    ⟨[23301, 88827], [23301, 68375, 88737], .contexts [
        ⟨137039, false, false, [23301], []⟩
      ]⟩,
    ⟨[86415, 1], [23301, 68375, 88737], .contexts [
        ⟨52731, false, false, [], []⟩,
        ⟨162852, false, false, [], []⟩
      ]⟩,
    ⟨[86415, 3], [23331, 86411], .contexts [
        ⟨36806, false, false, [], []⟩,
        ⟨162843, false, false, [], []⟩
      ]⟩,
    ⟨[86415, 5], [86417], .contexts [
        ⟨36808, false, false, [], []⟩,
        ⟨36847, false, false, [], []⟩
      ]⟩,
    ⟨[86415, 7], [23969, 62769, 84661], .contexts [
        ⟨55462, false, false, [], []⟩,
        ⟨130628, false, false, [23969], []⟩
      ]⟩,
    ⟨[86415, 9], [19109, 86415], .contexts [
        ⟨37012, false, false, [], []⟩,
        ⟨37013, false, false, [], []⟩
      ]⟩,
    ⟨[86415, 11], [28893, 47383, 83991], .contexts [
        ⟨75092, false, false, [], []⟩,
        ⟨112809, false, false, [28893], []⟩
      ]⟩,
    ⟨[86415, 13], [28939, 51351, 84437], .contexts [
        ⟨75274, false, false, [], []⟩,
        ⟨117155, false, false, [28939], []⟩
      ]⟩,
    ⟨[86415, 15], [28959, 90499], .contexts [
        ⟨75238, false, false, [], []⟩,
        ⟨75302, false, false, [], []⟩
      ]⟩,
    ⟨[86417, 1], [86419], .contexts [
        ⟨36812, false, false, [], []⟩,
        ⟨36844, false, false, [], []⟩
      ]⟩,
    ⟨[86417, 3], [23301, 68331, 88731], .contexts [
        ⟨52727, false, false, [], []⟩,
        ⟨137021, false, false, [23301], []⟩
      ]⟩,
    ⟨[86417, 5], [86415], .contexts [
        ⟨36810, false, false, [], []⟩,
        ⟨36849, false, false, [], []⟩
      ]⟩,
    ⟨[86417, 7], [27593, 47457, 84001], .contexts [
        ⟨71036, false, false, [], []⟩,
        ⟨112867, false, false, [27593], []⟩
      ]⟩,
    ⟨[86417, 9], [19111, 86417], .contexts [
        ⟨37005, false, false, [], []⟩,
        ⟨37006, false, false, [], []⟩
      ]⟩,
    ⟨[86417, 11], [28893, 47383, 83989], .contexts [
        ⟨75196, false, false, [], []⟩,
        ⟨112799, false, false, [28893], []⟩
      ]⟩,
    ⟨[86417, 13], [28939, 51315, 84429], .contexts [
        ⟨75188, true, false, [28936], [13]⟩,
        ⟨59, false, false, [28936, 87553], []⟩,
        ⟨75189, true, false, [], [87553]⟩,
        ⟨117113, false, false, [28939], []⟩
      ]⟩,
    ⟨[86417, 15], [74271, 96999], .contexts [
        ⟨144957, true, false, [74268], [15]⟩,
        ⟨1, false, false, [74268, 96999], []⟩,
        ⟨144958, true, false, [], [96999]⟩
      ]⟩,
    ⟨[86419, 1], [86417], .contexts [
        ⟨36814, false, false, [], []⟩,
        ⟨36847, false, false, [], []⟩
      ]⟩,
    ⟨[86419, 3], [27581, 71525, 91867], .contexts [
        ⟨70960, false, false, [], []⟩,
        ⟨140377, false, false, [27581], []⟩
      ]⟩,
    ⟨[86419, 5], [23301, 68375, 88737], .contexts [
        ⟨52703, false, false, [], []⟩,
        ⟨162852, false, false, [], []⟩
      ]⟩,
    ⟨[86419, 7], [27593, 84575], .contexts [
        ⟨70984, false, false, [], []⟩,
        ⟨71031, false, false, [], []⟩
      ]⟩,
    ⟨[86419, 9], [86421], .contexts [
        ⟨36816, false, false, [], []⟩,
        ⟨36842, false, false, [], []⟩
      ]⟩,
    ⟨[86419, 11], [23429, 55161, 91079], .contexts [
        ⟨86342, true, false, [23426], [11]⟩,
        ⟨53, false, false, [23426, 94765], []⟩,
        ⟨53444, true, false, [], [94765]⟩,
        ⟨121585, false, false, [23429], []⟩
      ]⟩,
    ⟨[86419, 13], [23429, 45525, 86273], .contexts [
        ⟨58532, true, false, [23426], [13]⟩,
        ⟨59, false, false, [23426, 89973], []⟩,
        ⟨53444, true, false, [], [89973]⟩,
        ⟨110652, false, false, [23429], []⟩
      ]⟩,
    ⟨[86419, 15], [75261, 97171], .contexts [
        ⟨146549, true, false, [71534], [15]⟩,
        ⟨1, false, false, [71534, 97171], []⟩,
        ⟨146550, true, false, [], [97171]⟩
      ]⟩,
    ⟨[86421, 1], [19109, 86421], .contexts [
        ⟨36999, false, false, [], []⟩,
        ⟨36995, false, false, [], []⟩
      ]⟩,
    ⟨[86421, 3], [22613, 88339], .contexts [
        ⟨49845, false, false, [], []⟩,
        ⟨49872, false, false, [], []⟩
      ]⟩,
    ⟨[86421, 5], [23301, 68375, 88739], .contexts [
        ⟨52677, false, false, [], []⟩,
        ⟨137055, false, false, [23301], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2545. -/
def y322TCIndexRaw2545 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86421, 7], [31145, 40845, 93825], .contexts [
        ⟨83591, false, false, [], []⟩,
        ⟨105808, false, false, [31145], []⟩
      ]⟩,
    ⟨[86421, 9], [86419], .contexts [
        ⟨36818, false, false, [], []⟩,
        ⟨36844, false, false, [], []⟩
      ]⟩,
    ⟨[86421, 11], [86423], .contexts [
        ⟨36820, false, false, [], []⟩,
        ⟨36840, false, false, [], []⟩
      ]⟩,
    ⟨[86421, 13], [23429, 88973], .contexts [
        ⟨53443, true, false, [23426], [13]⟩,
        ⟨59, false, false, [23426, 88973], []⟩,
        ⟨53444, true, false, [], [88973]⟩
      ]⟩,
    ⟨[86421, 15], [22663, 84979], .contexts [
        ⟨49881, false, false, [], []⟩,
        ⟨49875, false, false, [], []⟩
      ]⟩,
    ⟨[86423, 1], [19109, 86423], .contexts [
        ⟨36824, false, false, [], []⟩,
        ⟨36991, false, false, [], []⟩
      ]⟩,
    ⟨[86423, 3], [22613, 88337], .contexts [
        ⟨49791, false, false, [], []⟩,
        ⟨114490, false, false, [], []⟩
      ]⟩,
    ⟨[86423, 5], [23301, 68375, 88741], .contexts [
        ⟨52654, false, false, [], []⟩,
        ⟨137070, false, false, [23301], []⟩
      ]⟩,
    ⟨[86423, 7], [22643, 86683], .contexts [
        ⟨49837, false, false, [], []⟩,
        ⟨114497, false, false, [], []⟩
      ]⟩,
    ⟨[86423, 9], [19917, 86785], .contexts [
        ⟨40448, false, false, [], []⟩,
        ⟨49801, false, false, [], []⟩
      ]⟩,
    ⟨[86423, 11], [86421], .contexts [
        ⟨36822, false, false, [], []⟩,
        ⟨36842, false, false, [], []⟩
      ]⟩,
    ⟨[86423, 13], [19107, 83327], .contexts [
        ⟨36986, false, false, [], []⟩
      ]⟩,
    ⟨[86423, 15], [41413, 56755, 93629], .contexts [
        ⟨106294, false, false, [], []⟩,
        ⟨123513, false, false, [41413], []⟩
      ]⟩,
    ⟨[86433, 1], [19117, 84341], .contexts [
        ⟨37046, false, false, [], []⟩,
        ⟨46538, false, false, [], []⟩
      ]⟩,
    ⟨[86433, 3], [81363], .contexts [
        ⟨37020, false, false, [], []⟩,
        ⟨8914, false, false, [], []⟩
      ]⟩,
    ⟨[86433, 5], [4433, 86433], .contexts [
        ⟨37028, false, false, [], []⟩,
        ⟨37025, false, false, [], []⟩
      ]⟩,
    ⟨[86433, 7], [42787, 89723], .contexts [
        ⟨82029, true, false, [], [7]⟩,
        ⟨38, false, false, [93925], []⟩,
        ⟨82027, false, false, [], []⟩,
        ⟨151911, false, false, [], []⟩
      ]⟩,
    ⟨[86433, 9], [4217, 86433], .contexts [
        ⟨37030, false, false, [], []⟩,
        ⟨37029, false, false, [], []⟩
      ]⟩,
    ⟨[86433, 11], [8301, 84099], .contexts [
        ⟨37036, false, false, [], []⟩,
        ⟨37033, false, false, [], []⟩
      ]⟩,
    ⟨[86433, 13], [87805], .contexts [
        ⟨46508, false, false, [], []⟩,
        ⟨46478, false, false, [], []⟩
      ]⟩,
    ⟨[86433, 15], [19113, 84345], .contexts [
        ⟨37039, false, false, [], []⟩
      ]⟩,
    ⟨[86435, 1], [19123, 86435], .contexts [
        ⟨37065, false, false, [], []⟩,
        ⟨37058, false, false, [], []⟩
      ]⟩,
    ⟨[86435, 3], [20723, 83621], .contexts [
        ⟨42563, true, false, [20720], [3]⟩,
        ⟨20, false, false, [20720, 83621], []⟩,
        ⟨42564, true, false, [], [83621]⟩
      ]⟩,
    ⟨[86435, 5], [17027, 86435], .contexts [
        ⟨37070, false, false, [], []⟩,
        ⟨37066, false, false, [], []⟩
      ]⟩,
    ⟨[86435, 7], [43931, 89319], .contexts [
        ⟨108720, true, false, [39274], [7]⟩,
        ⟨85745, false, false, [39274], []⟩,
        ⟨85761, false, false, [39274], []⟩,
        ⟨104344, true, false, [], [31687, 89319]⟩,
        ⟨108722, true, false, [], [89319]⟩
      ]⟩,
    ⟨[86435, 9], [84341], .contexts [
        ⟨37049, false, false, [], []⟩,
        ⟨25915, false, false, [], []⟩
      ]⟩,
    ⟨[86435, 11], [86437], .contexts [
        ⟨37072, false, false, [], []⟩,
        ⟨37075, false, false, [], []⟩
      ]⟩,
    ⟨[86435, 13], [43933, 93191], .contexts [
        ⟨108720, true, false, [39274], [13]⟩,
        ⟨85751, false, false, [39274], []⟩,
        ⟨85771, false, false, [39274], []⟩,
        ⟨104344, true, false, [], [31693, 93191]⟩,
        ⟨108723, true, false, [], [93191]⟩
      ]⟩,
    ⟨[86435, 15], [39277, 87475], .contexts [
        ⟨82685, false, false, [], []⟩,
        ⟨157966, false, false, [], []⟩
      ]⟩,
    ⟨[86437, 1], [19123, 86437], .contexts [
        ⟨37082, false, false, [], []⟩,
        ⟨37078, false, false, [], []⟩
      ]⟩,
    ⟨[86437, 3], [20861, 83233], .contexts [
        ⟨42906, false, false, [], []⟩,
        ⟨43164, false, false, [], []⟩
      ]⟩,
    ⟨[86437, 5], [17027, 86437], .contexts [
        ⟨37086, false, false, [], []⟩,
        ⟨37083, false, false, [], []⟩
      ]⟩,
    ⟨[86437, 7], [31709, 94669], .contexts [
        ⟨85817, true, false, [31706], [7]⟩,
        ⟨38, false, false, [31706, 94669], []⟩,
        ⟨85818, true, false, [], [94669]⟩
      ]⟩,
    ⟨[86437, 9], [18219, 84105], .contexts [
        ⟨37095, false, false, [], []⟩,
        ⟨37090, false, false, [], []⟩
      ]⟩,
    ⟨[86437, 11], [86435], .contexts [
        ⟨37073, false, false, [], []⟩,
        ⟨37051, false, false, [], []⟩
      ]⟩,
    ⟨[86437, 13], [86439], .contexts [
        ⟨37113, false, false, [], []⟩,
        ⟨37116, false, false, [], []⟩
      ]⟩,
    ⟨[86437, 15], [94061], .contexts [
        ⟨82708, true, false, [], [15]⟩,
        ⟨1, false, false, [94061], []⟩,
        ⟨82690, false, false, [], []⟩,
        ⟨82689, false, false, [], []⟩
      ]⟩,
    ⟨[86439, 1], [46019, 97239], .contexts [
        ⟨147774, true, false, [46016], [1]⟩,
        ⟨8, false, false, [46016, 97239], []⟩,
        ⟨111303, true, false, [], [97239]⟩
      ]⟩,
    ⟨[86439, 3], [20861, 83235], .contexts [
        ⟨43173, true, false, [20862], [3]⟩,
        ⟨20, false, false, [20862, 83235], []⟩,
        ⟨43174, true, false, [], [83235]⟩,
        ⟨43166, false, false, [], []⟩
      ]⟩,
    ⟨[86439, 5], [17027, 86439], .contexts [
        ⟨37123, false, false, [], []⟩,
        ⟨37119, false, false, [], []⟩
      ]⟩,
    ⟨[86439, 7], [46133, 94559], .contexts [
        ⟨111445, false, false, [], []⟩
      ]⟩,
    ⟨[86439, 9], [18219, 92579], .contexts [
        ⟨73295, false, false, [], []⟩
      ]⟩,
    ⟨[86439, 11], [46019, 93191], .contexts [
        ⟨111302, true, false, [46016], [11]⟩,
        ⟨53, false, false, [46016, 93191], []⟩,
        ⟨111303, true, false, [], [93191]⟩
      ]⟩,
    ⟨[86439, 13], [86437], .contexts [
        ⟨37114, false, false, [], []⟩,
        ⟨37075, false, false, [], []⟩
      ]⟩,
    ⟨[86439, 15], [86441], .contexts [
        ⟨37125, false, false, [], []⟩,
        ⟨37128, false, false, [], []⟩
      ]⟩,
    ⟨[86441, 1], [86443], .contexts [
        ⟨37136, false, false, [], []⟩,
        ⟨37138, false, false, [], []⟩
      ]⟩,
    ⟨[86441, 3], [20861, 83237], .contexts [
        ⟨43321, false, false, [], []⟩,
        ⟨43437, false, false, [], []⟩
      ]⟩,
    ⟨[86441, 5], [17027, 86441], .contexts [
        ⟨37134, false, false, [], []⟩,
        ⟨37130, false, false, [], []⟩
      ]⟩,
    ⟨[86441, 7], [29715, 39223, 83619], .contexts [
        ⟨77922, false, false, [], []⟩,
        ⟨104286, false, false, [29715], []⟩
      ]⟩,
    ⟨[86441, 9], [18219, 39317, 86321], .contexts [
        ⟨73313, false, false, [], []⟩,
        ⟨104382, false, false, [18219], []⟩
      ]⟩,
    ⟨[86441, 11], [34137, 95627], .contexts [
        ⟨93021, false, false, [], []⟩,
        ⟨93063, false, false, [], []⟩
      ]⟩,
    ⟨[94065], [39249, 93285], .contexts [
        ⟨104320, false, false, [], []⟩
      ]⟩,
    ⟨[86441, 13], [39249, 93285], .contexts [
        ⟨82731, false, false, [], []⟩,
        ⟨162931, false, false, [], []⟩
      ]⟩,
    ⟨[86441, 15], [86439], .contexts [
        ⟨37126, false, false, [], []⟩,
        ⟨37116, false, false, [], []⟩
      ]⟩,
    ⟨[86443, 1], [86441], .contexts [
        ⟨37137, false, false, [], []⟩,
        ⟨37128, false, false, [], []⟩
      ]⟩,
    ⟨[86443, 3], [86445], .contexts [
        ⟨37147, false, false, [], []⟩,
        ⟨37447, false, false, [], []⟩
      ]⟩,
    ⟨[86443, 5], [17027, 86443], .contexts [
        ⟨37145, false, false, [], []⟩,
        ⟨37141, false, false, [], []⟩
      ]⟩,
    ⟨[86443, 7], [43463, 83617], .contexts [
        ⟨108281, true, false, [43450], [7]⟩,
        ⟨56087, false, false, [43450], []⟩,
        ⟨108271, true, false, [], [24091, 83617]⟩,
        ⟨108282, true, false, [], [83617]⟩
      ]⟩,
    ⟨[86443, 9], [34137, 50885, 92609], .contexts [
        ⟨93073, false, false, [], []⟩,
        ⟨116625, false, false, [34137], []⟩
      ]⟩,
    ⟨[86443, 11], [34137, 43471, 93187], .contexts [
        ⟨93074, false, false, [], []⟩,
        ⟨108295, false, false, [34137], []⟩
      ]⟩,
    ⟨[86443, 13], [43465, 90463], .contexts [
        ⟨108284, false, false, [], []⟩,
        ⟨111627, false, false, [], []⟩
      ]⟩,
    ⟨[86443, 15], [76049, 97239], .contexts [
        ⟨147785, true, false, [75714], [15]⟩,
        ⟨1, false, false, [75714, 97239], []⟩,
        ⟨147786, true, false, [], [97239]⟩
      ]⟩,
    ⟨[86445, 1], [20861, 83241], .contexts [
        ⟨43441, true, false, [20862], [1]⟩,
        ⟨8, false, false, [20862, 83241], []⟩,
        ⟨43174, true, false, [], [83241]⟩,
        ⟨43439, false, false, [], []⟩
      ]⟩,
    ⟨[86445, 3], [86443], .contexts [
        ⟨37148, false, false, [], []⟩,
        ⟨37138, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2546. -/
def y322TCIndexRaw2546 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86445, 5], [20861, 83245], .contexts [
        ⟨37150, false, false, [], []⟩,
        ⟨43521, false, false, [], []⟩
      ]⟩,
    ⟨[86445, 7], [38209, 70397, 89907], .contexts [
        ⟨103146, false, false, [], []⟩,
        ⟨139124, false, false, [38209], []⟩
      ]⟩,
    ⟨[86445, 9], [43459, 88687], .contexts [
        ⟨108277, false, false, [], []⟩,
        ⟨116611, false, false, [], []⟩
      ]⟩,
    ⟨[86445, 11], [33321, 95405], .contexts [
        ⟨90768, false, false, [], []⟩
      ]⟩,
    ⟨[86445, 13], [43453, 90457], .contexts [
        ⟨108273, false, false, [], []⟩,
        ⟨109552, false, false, [], []⟩
      ]⟩,
    ⟨[86445, 15], [43457, 91813], .contexts [
        ⟨108270, true, false, [43450], [15]⟩,
        ⟨77578, false, false, [43450], []⟩,
        ⟨77680, false, false, [43450], []⟩,
        ⟨108271, true, false, [], [29629, 29667, 91813]⟩,
        ⟨108274, true, false, [], [29667, 91813]⟩,
        ⟨108275, true, false, [], [91813]⟩
      ]⟩,
    ⟨[86455], [50745, 85145], .contexts [
        ⟨120517, false, false, [], []⟩
      ]⟩,
    ⟨[86453, 1], [50745, 85145], .contexts [
        ⟨37171, false, false, [], []⟩,
        ⟨162950, false, false, [], []⟩
      ]⟩,
    ⟨[86453, 3], [71867, 96791], .contexts [
        ⟨140976, true, false, [71864], [3]⟩,
        ⟨20, false, false, [71864, 96791], []⟩,
        ⟨140977, true, false, [], [96791]⟩
      ]⟩,
    ⟨[86453, 5], [50739, 87083], .contexts [
        ⟨116411, false, false, [], []⟩,
        ⟨116414, false, false, [], []⟩
      ]⟩,
    ⟨[86453, 7], [50737, 62523, 86007], .contexts [
        ⟨116413, false, false, [], []⟩,
        ⟨130333, false, false, [50737], []⟩
      ]⟩,
    ⟨[86453, 9], [50731, 84399], .contexts [
        ⟨116407, true, false, [50732], [9]⟩,
        ⟨95781, false, false, [50732], []⟩,
        ⟨26983, false, false, [50732], []⟩,
        ⟨116401, true, false, [], [84399]⟩,
        ⟨116401, true, false, [], [84399]⟩,
        ⟨116400, true, false, [], [84399]⟩
      ]⟩,
    ⟨[86453, 11], [54261, 85149], .contexts [
        ⟨37169, false, false, [], []⟩,
        ⟨120541, false, false, [], []⟩
      ]⟩,
    ⟨[86453, 13], [24949, 86453], .contexts [
        ⟨60402, false, false, [], []⟩,
        ⟨60403, false, false, [], []⟩
      ]⟩,
    ⟨[86453, 15], [50735, 88001], .contexts [
        ⟨116412, false, false, [], []⟩
      ]⟩,
    ⟨[86457, 1], [24947, 86457], .contexts [
        ⟨60412, false, false, [], []⟩,
        ⟨60413, false, false, [], []⟩
      ]⟩,
    ⟨[86457, 3], [52883, 87215], .contexts [
        ⟨118958, true, false, [52880], [3]⟩,
        ⟨40724, false, false, [52880], []⟩,
        ⟨40707, false, false, [52880], []⟩,
        ⟨118961, true, false, [], [87215]⟩
      ]⟩,
    ⟨[86457, 5], [52883, 87219], .contexts [
        ⟨118958, true, false, [52880], [5]⟩,
        ⟨40738, false, false, [52880], []⟩,
        ⟨40740, false, false, [52880], []⟩,
        ⟨118961, true, false, [], [87219]⟩
      ]⟩,
    ⟨[86457, 7], [52885, 85631], .contexts [
        ⟨118965, false, false, [], []⟩,
        ⟨120610, false, false, [], []⟩
      ]⟩,
    ⟨[86457, 9], [52875, 83027], .contexts [
        ⟨118953, false, false, [], []⟩
      ]⟩,
    ⟨[86457, 11], [52887, 96059], .contexts [
        ⟨118967, false, false, [], []⟩,
        ⟨120606, false, false, [], []⟩
      ]⟩,
    ⟨[86457, 13], [50745, 85145], .contexts [
        ⟨37177, false, false, [], []⟩,
        ⟨162950, false, false, [], []⟩
      ]⟩,
    ⟨[86457, 15], [86459], .contexts [
        ⟨37179, false, false, [], []⟩,
        ⟨37441, false, false, [], []⟩
      ]⟩,
    ⟨[86461], [24949, 86459], .contexts [
        ⟨143233, false, false, [], []⟩
      ]⟩,
    ⟨[86459, 1], [24949, 86459], .contexts [
        ⟨37183, false, false, [], []⟩,
        ⟨162967, false, false, [], []⟩
      ]⟩,
    ⟨[86459, 3], [24947, 86463], .contexts [
        ⟨60419, false, false, [], []⟩
      ]⟩,
    ⟨[86459, 5], [76439, 97253], .contexts [
        ⟨148169, true, false, [76436], [5]⟩,
        ⟨28, false, false, [76436, 97253], []⟩,
        ⟨148170, true, false, [], [97253]⟩
      ]⟩,
    ⟨[86459, 7], [73157, 96905], .contexts [
        ⟨143238, false, false, [], []⟩
      ]⟩,
    ⟨[86459, 9], [61261, 67753, 87833], .contexts [
        ⟨128745, false, false, [], []⟩,
        ⟨136323, false, false, [61261], []⟩
      ]⟩,
    ⟨[86459, 11], [52887, 96061], .contexts [
        ⟨120621, true, false, [54328], [11]⟩,
        ⟨53, false, false, [54328, 96061], []⟩,
        ⟨120622, true, false, [], [96061]⟩,
        ⟨120616, false, false, [], []⟩
      ]⟩,
    ⟨[86459, 13], [73879, 96967], .contexts [
        ⟨144374, false, false, [], []⟩
      ]⟩,
    ⟨[86459, 15], [86457], .contexts [
        ⟨37181, false, false, [], []⟩,
        ⟨37442, false, false, [], []⟩
      ]⟩,
    ⟨[86463, 1], [55537, 87211], .contexts [
        ⟨122069, true, false, [55532], [1]⟩,
        ⟨60537, false, false, [55532], []⟩,
        ⟨104461, false, false, [55532], []⟩,
        ⟨122073, true, false, [], [87211]⟩,
        ⟨122071, true, false, [], [39385, 87211]⟩,
        ⟨122072, true, false, [], [87211]⟩
      ]⟩,
    ⟨[86463, 3], [24949, 86459], .contexts [
        ⟨37188, false, false, [], []⟩,
        ⟨162967, false, false, [], []⟩
      ]⟩,
    ⟨[86463, 5], [86465], .contexts [
        ⟨37190, false, false, [], []⟩,
        ⟨37438, false, false, [], []⟩
      ]⟩,
    ⟨[86463, 7], [55543, 84313], .contexts [
        ⟨122069, true, false, [55532], [7]⟩,
        ⟨111724, false, false, [55532], []⟩,
        ⟨122070, true, false, [], [46409, 84313]⟩,
        ⟨122078, true, false, [], [84313]⟩
      ]⟩,
    ⟨[86463, 9], [55541, 85129], .contexts [
        ⟨122069, true, false, [55532], [9]⟩,
        ⟨111087, true, false, [55532, 45844], [9]⟩,
        ⟨46, false, false, [55532, 45844, 85129], []⟩,
        ⟨111088, true, false, [55532], [85129]⟩,
        ⟨122070, true, false, [], [45847, 85129]⟩,
        ⟨122077, true, false, [], [85129]⟩
      ]⟩,
    ⟨[86463, 11], [55545, 93267], .contexts [
        ⟨122069, true, false, [55532], [11]⟩,
        ⟨111729, true, false, [55532, 46416], [11]⟩,
        ⟨53, false, false, [55532, 46416, 93267], []⟩,
        ⟨111730, true, false, [55532], [93267]⟩,
        ⟨122070, true, false, [], [46419, 93267]⟩,
        ⟨122079, true, false, [], [93267]⟩
      ]⟩,
    ⟨[86463, 13], [55539, 59565, 85179], .contexts [
        ⟨122075, false, false, [], []⟩,
        ⟨126806, false, false, [55539], []⟩
      ]⟩,
    ⟨[86463, 15], [55537, 87215], .contexts [
        ⟨122076, false, false, [], []⟩,
        ⟨122139, false, false, [], []⟩
      ]⟩,
    ⟨[86465, 1], [55553, 84499], .contexts [
        ⟨37194, false, false, [], []⟩,
        ⟨122096, false, false, [], []⟩
      ]⟩,
    ⟨[86465, 3], [55555, 92595], .contexts [
        ⟨122091, false, false, [], []⟩
      ]⟩,
    ⟨[86465, 5], [86463], .contexts [
        ⟨37192, false, false, [], []⟩,
        ⟨37439, false, false, [], []⟩
      ]⟩,
    ⟨[86465, 7], [55559, 83823], .contexts [
        ⟨122084, true, false, [55548], [7]⟩,
        ⟨111707, false, false, [55548], []⟩,
        ⟨122085, true, false, [], [46393, 83823]⟩,
        ⟨122093, true, false, [], [83823]⟩
      ]⟩,
    ⟨[86465, 9], [55557, 85193], .contexts [
        ⟨122084, true, false, [55548], [9]⟩,
        ⟨111134, true, false, [55548, 45884], [9]⟩,
        ⟨46, false, false, [55548, 45884, 85193], []⟩,
        ⟨111135, true, false, [55548], [85193]⟩,
        ⟨122085, true, false, [], [45887, 85193]⟩,
        ⟨122092, true, false, [], [85193]⟩
      ]⟩,
    ⟨[86465, 11], [55551, 84323], .contexts [
        ⟨122084, true, false, [55548], [11]⟩,
        ⟨98500, false, false, [55548], []⟩,
        ⟨111112, false, false, [55548], []⟩,
        ⟨122085, true, false, [], [45863, 84323]⟩,
        ⟨122086, true, false, [], [84323]⟩
      ]⟩,
    ⟨[86465, 13], [60323, 85171], .contexts [
        ⟨127622, true, false, [60320], [13]⟩,
        ⟨59, false, false, [60320, 85171], []⟩,
        ⟨127623, true, false, [], [85171]⟩
      ]⟩,
    ⟨[86465, 15], [55553, 84503], .contexts [
        ⟨122084, true, false, [55548], [15]⟩,
        ⟨111094, false, false, [55548], []⟩,
        ⟨122089, true, false, [], [84503]⟩,
        ⟨122088, true, false, [], [84503]⟩
      ]⟩,
    ⟨[86471, 1], [86473], .contexts [
        ⟨37204, false, false, [], []⟩,
        ⟨37434, false, false, [], []⟩
      ]⟩,
    ⟨[86471, 3], [55575, 92607], .contexts [
        ⟨122111, false, false, [], []⟩
      ]⟩,
    ⟨[86471, 5], [55579, 83817], .contexts [
        ⟨122103, true, false, [55566], [5]⟩,
        ⟨106894, true, false, [55566, 42050], [5]⟩,
        ⟨93191, false, false, [55566, 42050], []⟩,
        ⟨106895, true, false, [55566], [34237, 83817]⟩,
        ⟨106902, true, false, [55566], [83817]⟩,
        ⟨122104, true, false, [], [42057, 83817]⟩,
        ⟨122113, true, false, [], [83817]⟩
      ]⟩,
    ⟨[86471, 7], [55581, 89085], .contexts [
        ⟨122103, true, false, [55566], [7]⟩,
        ⟨106894, true, false, [55566, 42050], [7]⟩,
        ⟨104397, true, false, [55566, 42050, 39332], [7]⟩,
        ⟨97442, false, false, [55566, 42050, 39332], []⟩,
        ⟨104398, true, false, [55566, 42050], [35499, 89085]⟩,
        ⟨104399, true, false, [55566, 42050], [89085]⟩,
        ⟨106895, true, false, [55566], [39337, 89085]⟩,
        ⟨106903, true, false, [55566], [89085]⟩,
        ⟨122104, true, false, [], [42059, 89085]⟩,
        ⟨122114, true, false, [], [89085]⟩
      ]⟩,
    ⟨[86471, 9], [55577, 87797], .contexts [
        ⟨122103, true, false, [55566], [9]⟩,
        ⟨106894, true, false, [55566, 42050], [9]⟩,
        ⟨93149, true, false, [55566, 42050, 34198], [9]⟩,
        ⟨46, false, false, [55566, 42050, 34198, 92585], []⟩,
        ⟨93150, true, false, [55566, 42050], [92585]⟩,
        ⟨104393, false, false, [55566, 42050, 34197], []⟩,
        ⟨106895, true, false, [55566], [34197, 39325, 87797]⟩,
        ⟨106900, true, false, [55566], [39325, 87797]⟩,
        ⟨106901, true, false, [55566], [87797]⟩,
        ⟨122104, true, false, [], [42055, 87797]⟩,
        ⟨122112, true, false, [], [87797]⟩
      ]⟩,
    ⟨[86471, 11], [55561, 83385], .contexts [
        ⟨37202, false, false, [], []⟩,
        ⟨122099, false, false, [], []⟩
      ]⟩,
    ⟨[86471, 13], [55569, 86521], .contexts [
        ⟨122103, true, false, [55566], [13]⟩,
        ⟨77237, false, false, [55566], []⟩,
        ⟨112538, false, false, [55566], []⟩,
        ⟨122105, true, false, [], [47157, 86521]⟩,
        ⟨122106, true, false, [], [86521]⟩
      ]⟩,
    ⟨[86471, 15], [55571, 89285], .contexts [
        ⟨122108, false, false, [], []⟩
      ]⟩,
    ⟨[86473, 1], [86471], .contexts [
        ⟨37206, false, false, [], []⟩,
        ⟨37435, false, false, [], []⟩
      ]⟩,
    ⟨[86473, 3], [55583, 88689], .contexts [
        ⟨122119, true, false, [55584], [3]⟩,
        ⟨52068, false, false, [55584], []⟩,
        ⟨52108, false, false, [55584], []⟩,
        ⟨122121, true, false, [], [88689]⟩,
        ⟨122122, true, false, [], [88689]⟩
      ]⟩,
    ⟨[86473, 5], [55587, 85201], .contexts [
        ⟨122119, true, false, [55584], [5]⟩,
        ⟨52070, false, false, [55584], []⟩,
        ⟨61725, false, false, [55584], []⟩,
        ⟨122122, true, false, [], [23907, 85201]⟩,
        ⟨122123, true, false, [], [85201]⟩
      ]⟩,
    ⟨[86473, 7], [55589, 89083], .contexts [
        ⟨122119, true, false, [55584], [7]⟩,
        ⟨55443, false, false, [55584], []⟩,
        ⟨122120, true, false, [], [23957, 89083]⟩,
        ⟨122124, true, false, [], [89083]⟩
      ]⟩,
    ⟨[86473, 9], [55593, 84813], .contexts [
        ⟨122119, true, false, [55584], [9]⟩,
        ⟨61716, false, false, [55584], []⟩,
        ⟨116317, false, false, [55584, 25259], []⟩,
        ⟨122120, true, false, [], [25259, 50663, 84813]⟩,
        ⟨122125, true, false, [], [50663, 84813]⟩,
        ⟨122126, true, false, [], [84813]⟩
      ]⟩,
    ⟨[86473, 11], [55599, 92333], .contexts [
        ⟨122130, false, false, [], []⟩
      ]⟩,
    ⟨[86475], [55601, 85929], .contexts [
        ⟨122135, false, false, [], []⟩
      ]⟩,
    ⟨[86473, 13], [55601, 85929], .contexts [
        ⟨37208, false, false, [], []⟩,
        ⟨163006, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2547. -/
def y322TCIndexRaw2547 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86473, 15], [55595, 89283], .contexts [
        ⟨122128, false, false, [], []⟩
      ]⟩,
    ⟨[86477, 1], [86479], .contexts [
        ⟨37215, false, false, [], []⟩,
        ⟨37431, false, false, [], []⟩
      ]⟩,
    ⟨[86477, 3], [57569, 83763], .contexts [
        ⟨124455, true, false, [57566], [3]⟩,
        ⟨20, false, false, [57566, 83763], []⟩,
        ⟨124456, true, false, [], [83763]⟩
      ]⟩,
    ⟨[86477, 5], [55989, 84467], .contexts [
        ⟨122651, false, false, [], []⟩,
        ⟨122647, false, false, [], []⟩
      ]⟩,
    ⟨[86477, 7], [55985, 65297, 91539], .contexts [
        ⟨122636, false, false, [], []⟩,
        ⟨133980, false, false, [55985], []⟩
      ]⟩,
    ⟨[86477, 9], [58251, 91355], .contexts [
        ⟨125174, false, false, [], []⟩
      ]⟩,
    ⟨[86477, 11], [55981, 85437], .contexts [
        ⟨122616, true, false, [56006], [11]⟩,
        ⟨53, false, false, [56006, 85437], []⟩,
        ⟨122614, false, true, [], [85437]⟩,
        ⟨122609, false, false, [], []⟩
      ]⟩,
    ⟨[86477, 13], [56017, 83453], .contexts [
        ⟨122632, true, false, [56018], [13]⟩,
        ⟨59, false, false, [56018, 83453], []⟩,
        ⟨122630, false, true, [], [83453]⟩,
        ⟨122627, false, false, [], []⟩
      ]⟩,
    ⟨[86477, 15], [55601, 85929], .contexts [
        ⟨37213, false, false, [], []⟩,
        ⟨163006, false, false, [], []⟩
      ]⟩,
    ⟨[86479, 1], [86477], .contexts [
        ⟨37217, false, false, [], []⟩,
        ⟨37433, false, false, [], []⟩
      ]⟩,
    ⟨[86479, 3], [86481], .contexts [
        ⟨37219, false, false, [], []⟩,
        ⟨37429, false, false, [], []⟩
      ]⟩,
    ⟨[86479, 5], [55989, 84465], .contexts [
        ⟨122587, false, false, [], []⟩,
        ⟨122638, false, false, [], []⟩
      ]⟩,
    ⟨[86479, 7], [55985, 65297, 91541], .contexts [
        ⟨122584, false, false, [], []⟩,
        ⟨133548, false, false, [55985], []⟩
      ]⟩,
    ⟨[86479, 9], [55979, 86619], .contexts [
        ⟨122575, true, false, [55976], [9]⟩,
        ⟨38245, false, false, [55976], []⟩,
        ⟨38437, false, false, [55976], []⟩,
        ⟨122577, true, false, [], [86619]⟩,
        ⟨122578, true, false, [], [86619]⟩
      ]⟩,
    ⟨[86479, 11], [55981, 85435], .contexts [
        ⟨122580, false, false, [], []⟩,
        ⟨122606, false, false, [], []⟩
      ]⟩,
    ⟨[86479, 13], [55983, 83685], .contexts [
        ⟨122582, false, false, [], []⟩,
        ⟨122624, false, false, [], []⟩
      ]⟩,
    ⟨[86479, 15], [55987, 69645, 87893], .contexts [
        ⟨122575, true, false, [55976], [15]⟩,
        ⟨89792, false, false, [55976], []⟩,
        ⟨122570, false, false, [55976], []⟩,
        ⟨122576, true, false, [], [32935, 95361]⟩,
        ⟨122585, true, false, [], [95361]⟩,
        ⟨138248, false, false, [55987], []⟩
      ]⟩,
    ⟨[86481, 1], [55993, 58493, 71177, 90911], .contexts [
        ⟨122596, false, false, [], []⟩,
        ⟨156076, false, false, [55993], []⟩
      ]⟩,
    ⟨[86481, 3], [86479], .contexts [
        ⟨37221, false, false, [], []⟩,
        ⟨37431, false, false, [], []⟩
      ]⟩,
    ⟨[86481, 5], [56475, 84697], .contexts [
        ⟨37223, false, false, [], []⟩,
        ⟨123183, false, false, [], []⟩
      ]⟩,
    ⟨[86481, 7], [56005, 89357], .contexts [
        ⟨122605, false, false, [], []⟩,
        ⟨122659, false, false, [], []⟩
      ]⟩,
    ⟨[86481, 9], [55999, 58471, 91679], .contexts [
        ⟨122599, false, false, [], []⟩,
        ⟨125477, false, false, [55999], []⟩
      ]⟩,
    ⟨[86481, 11], [56001, 83013], .contexts [
        ⟨122601, false, false, [], []⟩,
        ⟨122681, false, false, [], []⟩
      ]⟩,
    ⟨[86481, 13], [55999, 83007], .contexts [
        ⟨122602, false, false, [], []⟩,
        ⟨122687, false, false, [], []⟩
      ]⟩,
    ⟨[86481, 15], [73209, 96911], .contexts [
        ⟨143331, true, false, [73206], [15]⟩,
        ⟨1, false, false, [73206, 96911], []⟩,
        ⟨143332, true, false, [], [96911]⟩
      ]⟩,
    ⟨[86489, 1], [56199, 86391], .contexts [
        ⟨37237, false, false, [], []⟩,
        ⟨142380, false, false, [], []⟩
      ]⟩,
    ⟨[86489, 3], [62391, 83261], .contexts [
        ⟨130158, false, false, [], []⟩
      ]⟩,
    ⟨[86489, 5], [57519, 71161, 90909], .contexts [
        ⟨124402, false, false, [], []⟩,
        ⟨140001, false, false, [57519], []⟩
      ]⟩,
    ⟨[86489, 7], [57629, 86489], .contexts [
        ⟨124516, false, false, [57624], [86489, 7]⟩,
        ⟨122846, true, false, [57624, 50383], [7]⟩,
        ⟨124515, true, false, [57624], [1, 7]⟩,
        ⟨124515, true, false, [57624], [1, 7]⟩,
        ⟨124514, true, false, [57624], [1, 7]⟩,
        ⟨115939, true, false, [57624], [1, 7]⟩,
        ⟨115936, true, false, [57624], [1, 7]⟩,
        ⟨502, false, false, [57624, 86391], []⟩,
        ⟨9, false, false, [57624, 86391], []⟩,
        ⟨123436, false, false, [57624], []⟩,
        ⟨123437, false, false, [57624], []⟩,
        ⟨123438, false, false, [57624], []⟩,
        ⟨123438, false, false, [57624], []⟩,
        ⟨123442, false, false, [57624, 56201], []⟩,
        ⟨124517, true, false, [], [56201, 86489]⟩,
        ⟨124518, true, false, [], [86489]⟩
      ]⟩,
    ⟨[86489, 9], [71985, 96807], .contexts [
        ⟨141285, true, false, [71982], [9]⟩,
        ⟨46, false, false, [71982, 96807], []⟩,
        ⟨141286, true, false, [], [96807]⟩
      ]⟩,
    ⟨[86489, 11], [56589, 84699], .contexts [
        ⟨37235, false, false, [], []⟩,
        ⟨123293, false, false, [], []⟩
      ]⟩,
    ⟨[86489, 13], [56709, 86489], .contexts [
        ⟨123445, false, false, [], []⟩
      ]⟩,
    ⟨[86489, 15], [56199, 86395], .contexts [
        ⟨125065, false, false, [], []⟩
      ]⟩,
    ⟨[86497], [56185, 86495], .contexts [
        ⟨122829, false, false, [], []⟩
      ]⟩,
    ⟨[86495, 1], [56185, 86495], .contexts [
        ⟨37247, false, false, [], []⟩,
        ⟨163041, false, false, [], []⟩
      ]⟩,
    ⟨[86495, 3], [56183, 86499], .contexts [
        ⟨122826, true, false, [56184], [3]⟩,
        ⟨37251, false, false, [56184], []⟩,
        ⟨37421, false, false, [56184], []⟩,
        ⟨122828, true, false, [], [86499]⟩,
        ⟨122828, true, false, [], [86499]⟩,
        ⟨122827, true, false, [], [86499]⟩
      ]⟩,
    ⟨[86495, 5], [56191, 87963], .contexts [
        ⟨122835, false, false, [], []⟩
      ]⟩,
    ⟨[86495, 7], [56189, 86495], .contexts [
        ⟨122826, true, false, [56184], [7]⟩,
        ⟨122817, true, false, [56184, 56160], [7]⟩,
        ⟨47596, true, false, [56184, 56160], [7]⟩,
        ⟨140, false, false, [56184, 56160, 87959], []⟩,
        ⟨141, false, false, [56184, 56160, 87959], []⟩,
        ⟨47589, false, false, [56184, 56160], [3]⟩,
        ⟨47590, false, false, [56184, 56160], [3]⟩,
        ⟨47587, false, false, [56184, 56160], [3]⟩,
        ⟨47588, false, false, [56184, 56160], [3]⟩,
        ⟨47588, false, false, [56184, 56160], [3]⟩,
        ⟨47592, false, false, [56184, 56160, 22033], []⟩,
        ⟨47604, false, false, [56184, 56160, 22033], []⟩,
        ⟨47485, true, false, [56184, 56160], [87961]⟩,
        ⟨122819, false, false, [56184, 56160, 22033], []⟩,
        ⟨122811, true, false, [56184], [86497]⟩,
        ⟨122831, false, false, [56184, 56165], []⟩,
        ⟨122827, true, false, [], [56165, 56185, 86495]⟩,
        ⟨122832, true, false, [], [56185, 86495]⟩,
        ⟨122833, true, false, [], [86495]⟩
      ]⟩,
    ⟨[86495, 9], [56705, 91699], .contexts [
        ⟨123432, true, false, [56702], [9]⟩,
        ⟨46, false, false, [56702, 91699], []⟩,
        ⟨123433, true, false, [], [91699]⟩
      ]⟩,
    ⟨[86495, 11], [56195, 83465], .contexts [
        ⟨122826, true, false, [56184], [11]⟩,
        ⟨122817, true, false, [56184, 56160], [11]⟩,
        ⟨116828, true, false, [56184, 56160, 51086], [11]⟩,
        ⟨86985, false, false, [56184, 56160, 51086], []⟩,
        ⟨116829, true, false, [56184, 56160], [32081, 83465]⟩,
        ⟨116834, true, false, [56184, 56160], [83465]⟩,
        ⟨122803, true, false, [56184], [51091, 83465]⟩,
        ⟨122821, true, false, [56184], [83465]⟩,
        ⟨122827, true, false, [], [56177, 83465]⟩,
        ⟨122837, true, false, [], [83465]⟩
      ]⟩,
    ⟨[86495, 13], [56193, 92523], .contexts [
        ⟨122826, true, false, [56184], [13]⟩,
        ⟨122817, true, false, [56184, 56160], [13]⟩,
        ⟨116828, true, false, [56184, 56160, 51086], [13]⟩,
        ⟨86963, false, false, [56184, 56160, 51086], []⟩,
        ⟨108616, false, false, [56184, 56160, 51086], []⟩,
        ⟨116830, true, false, [56184, 56160], [43815, 92523]⟩,
        ⟨116831, true, false, [56184, 56160], [92523]⟩,
        ⟨122803, true, false, [56184], [51089, 92523]⟩,
        ⟨122820, true, false, [56184], [92523]⟩,
        ⟨122827, true, false, [], [56175, 92523]⟩,
        ⟨122836, true, false, [], [92523]⟩
      ]⟩,
    ⟨[86495, 15], [56197, 86387], .contexts [
        ⟨37245, false, false, [], []⟩,
        ⟨122839, false, false, [], []⟩
      ]⟩,
    ⟨[86499, 1], [56159, 87957], .contexts [
        ⟨122802, true, false, [56160], [1]⟩,
        ⟨47585, false, false, [56160], []⟩,
        ⟨47567, false, false, [56160], []⟩,
        ⟨122806, true, false, [], [87957]⟩
      ]⟩,
    ⟨[86499, 3], [56185, 86495], .contexts [
        ⟨37253, false, false, [], []⟩,
        ⟨163041, false, false, [], []⟩
      ]⟩,
    ⟨[86499, 5], [86501], .contexts [
        ⟨37255, false, false, [], []⟩,
        ⟨37418, false, false, [], []⟩
      ]⟩,
    ⟨[86499, 7], [56165, 86499], .contexts [
        ⟨122802, true, false, [56160], [7]⟩,
        ⟨47590, false, false, [56160], []⟩,
        ⟨122808, false, false, [56160, 22033], []⟩,
        ⟨122811, true, false, [], [86499]⟩
      ]⟩,
    ⟨[86499, 9], [56169, 88615], .contexts [
        ⟨122802, true, false, [56160], [9]⟩,
        ⟨116839, true, false, [56160, 51096], [9]⟩,
        ⟨97015, false, false, [56160, 51096], []⟩,
        ⟨97014, false, false, [56160, 51096], []⟩,
        ⟨116840, true, false, [56160], [35327, 88615]⟩,
        ⟨116843, true, false, [56160], [88615]⟩,
        ⟨122803, true, false, [], [51101, 88615]⟩,
        ⟨122813, true, false, [], [88615]⟩
      ]⟩,
    ⟨[86499, 11], [56171, 82969], .contexts [
        ⟨122802, true, false, [56160], [11]⟩,
        ⟨116839, true, false, [56160, 51096], [11]⟩,
        ⟨97016, false, false, [56160, 51096], []⟩,
        ⟨38005, false, false, [56160, 51096], []⟩,
        ⟨116840, true, false, [56160], [19343, 82969]⟩,
        ⟨116844, true, false, [56160], [82969]⟩,
        ⟨122803, true, false, [], [51103, 82969]⟩,
        ⟨122814, true, false, [], [82969]⟩
      ]⟩,
    ⟨[86499, 13], [56167, 92521], .contexts [
        ⟨122802, true, false, [56160], [13]⟩,
        ⟨116839, true, false, [56160, 51096], [13]⟩,
        ⟨97008, false, false, [56160, 51096], []⟩,
        ⟨108606, false, false, [56160, 51096], []⟩,
        ⟨116840, true, false, [56160], [43809, 92521]⟩,
        ⟨116841, true, false, [56160], [92521]⟩,
        ⟨122803, true, false, [], [51099, 92521]⟩,
        ⟨122812, true, false, [], [92521]⟩
      ]⟩,
    ⟨[86499, 15], [56173, 84133], .contexts [
        ⟨122802, true, false, [56160], [15]⟩,
        ⟨116839, true, false, [56160, 51096], [15]⟩,
        ⟨97020, false, false, [56160, 51096], []⟩,
        ⟨113756, false, false, [56160, 51096, 35333], []⟩,
        ⟨116840, true, false, [56160], [35333, 48411, 84133]⟩,
        ⟨116845, true, false, [56160], [48411, 84133]⟩,
        ⟨116846, true, false, [56160], [84133]⟩,
        ⟨122803, true, false, [], [51107, 84133]⟩,
        ⟨122815, true, false, [], [84133]⟩
      ]⟩,
    ⟨[86501, 1], [86503], .contexts [
        ⟨37259, false, false, [], []⟩,
        ⟨37417, false, false, [], []⟩
      ]⟩,
    ⟨[86501, 3], [56157, 69529, 90931], .contexts [
        ⟨122796, false, false, [], []⟩,
        ⟨138146, false, false, [56157], []⟩
      ]⟩,
    ⟨[86501, 5], [86499], .contexts [
        ⟨37257, false, false, [], []⟩,
        ⟨37421, false, false, [], []⟩
      ]⟩,
    ⟨[86501, 7], [56153, 95673], .contexts [
        ⟨122784, true, false, [56138], [7]⟩,
        ⟨96429, true, false, [56138, 35206], [7]⟩,
        ⟨38, false, false, [56138, 35206, 96173], []⟩,
        ⟨96369, true, false, [56138], [96173]⟩,
        ⟨114945, false, false, [56138, 35209], []⟩,
        ⟨122785, true, false, [], [35209, 49509, 95673]⟩,
        ⟨122793, true, false, [], [49509, 95673]⟩,
        ⟨122794, true, false, [], [95673]⟩
      ]⟩,
    ⟨[86501, 9], [56149, 95419], .contexts [
        ⟨122784, true, false, [56138], [9]⟩,
        ⟨90803, true, false, [56138, 23500], [9]⟩,
        ⟨46, false, false, [56138, 23500, 95419], []⟩,
        ⟨90804, true, false, [56138], [95419]⟩,
        ⟨122785, true, false, [], [23499, 95419]⟩,
        ⟨122792, true, false, [], [95419]⟩
      ]⟩,
    ⟨[86501, 11], [56143, 86509], .contexts [
        ⟨122784, true, false, [56138], [11]⟩,
        ⟨53714, false, false, [56138], []⟩,
        ⟨112565, false, false, [56138, 20939], []⟩,
        ⟨122785, true, false, [], [20939, 47189, 86509]⟩,
        ⟨122788, true, false, [], [47189, 86509]⟩,
        ⟨122789, true, false, [], [86509]⟩
      ]⟩,
    ⟨[86501, 13], [56137, 88977], .contexts [
        ⟨122784, true, false, [56138], [13]⟩,
        ⟨53706, false, false, [56138], []⟩,
        ⟨53679, false, false, [56138], []⟩,
        ⟨122786, true, false, [], [88977]⟩,
        ⟨122787, true, false, [], [88977]⟩
      ]⟩,
    ⟨[86501, 15], [56147, 84131], .contexts [
        ⟨122784, true, false, [56138], [15]⟩,
        ⟨53716, false, false, [56138], []⟩,
        ⟨91195, false, false, [56138], []⟩,
        ⟨113677, false, false, [56138, 33497], []⟩,
        ⟨122790, true, false, [56138], [84131]⟩,
        ⟨122787, true, false, [], [56145, 84131]⟩,
        ⟨122791, true, false, [], [84131]⟩
      ]⟩,
    ⟨[86503, 1], [86501], .contexts [
        ⟨37261, false, false, [], []⟩,
        ⟨37418, false, false, [], []⟩
      ]⟩,
    ⟨[86503, 3], [56133, 87589], .contexts [
        ⟨122772, true, false, [56120], [3]⟩,
        ⟨122050, true, false, [56120, 55512], [3]⟩,
        ⟨20, false, false, [56120, 55512, 87589], []⟩,
        ⟨122051, true, false, [56120], [87589]⟩,
        ⟨122773, true, false, [], [55515, 87589]⟩,
        ⟨122780, true, false, [], [87589]⟩
      ]⟩,
    ⟨[86503, 5], [56135, 87957], .contexts [
        ⟨122772, true, false, [56120], [5]⟩,
        ⟨122268, false, false, [56120], []⟩,
        ⟨122773, true, false, [], [55719, 87957]⟩,
        ⟨122781, true, false, [], [87957]⟩
      ]⟩,
    ⟨[86503, 7], [56131, 95669], .contexts [
        ⟨122772, true, false, [56120], [7]⟩,
        ⟨122042, false, false, [56120], []⟩,
        ⟨122773, true, false, [], [55507, 95669]⟩,
        ⟨122779, true, false, [], [95669]⟩
      ]⟩,
    ⟨[86503, 9], [56121, 86503], .contexts [
        ⟨37263, false, false, [], []⟩,
        ⟨122775, false, false, [], []⟩
      ]⟩,
    ⟨[86503, 11], [56119, 82965], .contexts [
        ⟨122769, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2548. -/
def y322TCIndexRaw2548 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86503, 13], [56129, 86503], .contexts [
        ⟨122772, true, false, [56120], [13]⟩,
        ⟨119053, true, false, [56120, 52968], [13]⟩,
        ⟨87875, false, false, [56120, 52968], []⟩,
        ⟨117489, false, false, [56120, 52968], []⟩,
        ⟨119053, false, false, [56120, 52968, 51681], []⟩,
        ⟨119054, true, false, [56120, 52968], [86505]⟩,
        ⟨119055, true, false, [56120], [52971, 86505]⟩,
        ⟨119056, true, false, [56120], [86505]⟩,
        ⟨122776, false, false, [56120, 52975], []⟩,
        ⟨122773, true, false, [], [52975, 56121, 86503]⟩,
        ⟨122777, true, false, [], [56121, 86503]⟩,
        ⟨122778, true, false, [], [86503]⟩
      ]⟩,
    ⟨[86503, 15], [56125, 84247], .contexts [
        ⟨122772, true, false, [56120], [15]⟩,
        ⟨119043, false, false, [56120], []⟩,
        ⟨122773, true, false, [], [52965, 84247]⟩,
        ⟨122774, true, false, [], [84247]⟩
      ]⟩,
    ⟨[86509, 1], [47191, 82965], .contexts [
        ⟨37271, false, false, [], []⟩,
        ⟨119044, false, false, [], []⟩
      ]⟩,
    ⟨[86509, 3], [47199, 71209, 90923], .contexts [
        ⟨112554, true, false, [47188], [3]⟩,
        ⟨112000, false, false, [47188], []⟩,
        ⟨112555, true, false, [], [46615, 96619]⟩,
        ⟨112563, true, false, [], [96619]⟩,
        ⟨140051, false, false, [47199], []⟩
      ]⟩,
    ⟨[86509, 5], [47191, 82969], .contexts [
        ⟨112554, true, false, [47188], [5]⟩,
        ⟨42871, false, false, [47188], []⟩,
        ⟨43101, false, false, [47188], []⟩,
        ⟨112558, true, false, [], [82969]⟩,
        ⟨112557, true, false, [], [82969]⟩
      ]⟩,
    ⟨[86509, 7], [72585, 96859], .contexts [
        ⟨142289, true, false, [72582], [7]⟩,
        ⟨38, false, false, [72582, 96859], []⟩,
        ⟨142290, true, false, [], [96859]⟩
      ]⟩,
    ⟨[86509, 9], [47187, 87109], .contexts [
        ⟨112554, true, false, [47188], [9]⟩,
        ⟨40185, false, false, [47188], []⟩,
        ⟨40243, false, false, [47188], []⟩,
        ⟨112556, true, false, [], [87109]⟩,
        ⟨112556, true, false, [], [87109]⟩,
        ⟨112555, true, false, [], [87109]⟩
      ]⟩,
    ⟨[86509, 11], [47193, 56139, 86501], .contexts [
        ⟨112560, false, false, [], []⟩,
        ⟨122797, false, false, [47193], []⟩
      ]⟩,
    ⟨[86509, 13], [47183, 85211], .contexts [
        ⟨37273, false, false, [], []⟩,
        ⟨112551, false, false, [], []⟩
      ]⟩,
    ⟨[86509, 15], [47197, 91717], .contexts [
        ⟨112554, true, false, [47188], [15]⟩,
        ⟨91139, false, false, [47188], []⟩,
        ⟨105929, false, false, [47188, 33481], []⟩,
        ⟨112555, true, false, [], [33481, 40961, 91717]⟩,
        ⟨112561, true, false, [], [40961, 91717]⟩,
        ⟨112562, true, false, [], [91717]⟩
      ]⟩,
    ⟨[86521, 1], [47163, 83379], .contexts [
        ⟨37290, false, false, [], []⟩,
        ⟨112539, false, false, [], []⟩
      ]⟩,
    ⟨[86521, 3], [47167, 90617], .contexts [
        ⟨112537, false, false, [], []⟩,
        ⟨114916, false, false, [], []⟩
      ]⟩,
    ⟨[86521, 5], [47159, 84459], .contexts [
        ⟨112528, true, false, [47156], [5]⟩,
        ⟨106882, true, false, [47156, 42032], [5]⟩,
        ⟨97401, false, false, [47156, 42032], []⟩,
        ⟨104921, false, false, [47156, 42032, 35481], []⟩,
        ⟨106877, true, false, [47156], [35481, 39823, 84459]⟩,
        ⟨106883, true, false, [47156], [39823, 84459]⟩,
        ⟨106884, true, false, [47156], [84459]⟩,
        ⟨112529, true, false, [], [42037, 84459]⟩,
        ⟨112531, true, false, [], [84459]⟩
      ]⟩,
    ⟨[86521, 7], [47161, 86791], .contexts [
        ⟨112528, true, false, [47156], [7]⟩,
        ⟨106882, true, false, [47156, 42032], [7]⟩,
        ⟨97405, false, false, [47156, 42032], []⟩,
        ⟨97418, false, false, [47156, 42032], []⟩,
        ⟨106877, true, false, [47156], [35485, 86791]⟩,
        ⟨106885, true, false, [47156], [86791]⟩,
        ⟨112529, true, false, [], [42039, 86791]⟩,
        ⟨112532, true, false, [], [86791]⟩
      ]⟩,
    ⟨[86521, 9], [86523], .contexts [
        ⟨37292, false, false, [], []⟩,
        ⟨37406, false, false, [], []⟩
      ]⟩,
    ⟨[86521, 11], [47163, 83383], .contexts [
        ⟨112528, true, false, [47156], [11]⟩,
        ⟨106882, true, false, [47156, 42032], [11]⟩,
        ⟨97410, false, false, [47156, 42032], []⟩,
        ⟨21343, false, false, [47156, 42032], []⟩,
        ⟨106886, true, false, [47156], [83383]⟩,
        ⟨106886, true, false, [47156], [83383]⟩,
        ⟨106877, true, false, [47156], [83383]⟩,
        ⟨112534, true, false, [], [83383]⟩,
        ⟨112533, true, false, [], [83383]⟩
      ]⟩,
    ⟨[86521, 13], [47155, 55567, 86471], .contexts [
        ⟨112528, true, false, [47156], [13]⟩,
        ⟨77235, false, false, [47156], []⟩,
        ⟨77378, false, false, [47156], []⟩,
        ⟨112530, true, false, [], [93125]⟩,
        ⟨112530, true, false, [], [93125]⟩,
        ⟨112529, true, false, [], [93125]⟩,
        ⟨122115, false, false, [47155], []⟩
      ]⟩,
    ⟨[86521, 15], [47165, 85669], .contexts [
        ⟨112528, true, false, [47156], [15]⟩,
        ⟨106882, true, false, [47156, 42032], [15]⟩,
        ⟨97417, false, false, [47156, 42032], []⟩,
        ⟨105643, false, false, [47156, 42032, 32899], []⟩,
        ⟨106877, true, false, [47156], [32899, 40613, 85669]⟩,
        ⟨106887, true, false, [47156], [40613, 85669]⟩,
        ⟨106888, true, false, [47156], [85669]⟩,
        ⟨112529, true, false, [], [42045, 85669]⟩,
        ⟨112535, true, false, [], [85669]⟩
      ]⟩,
    ⟨[86523, 1], [47147, 85497], .contexts [
        ⟨112515, true, false, [47140], [1]⟩,
        ⟨46239, false, false, [47140], []⟩,
        ⟨46259, false, false, [47140], []⟩,
        ⟨112516, true, false, [], [21741, 85497]⟩,
        ⟨112521, true, false, [], [85497]⟩
      ]⟩,
    ⟨[86523, 3], [47145, 86325], .contexts [
        ⟨112515, true, false, [47140], [3]⟩,
        ⟨46223, false, false, [47140], []⟩,
        ⟨46214, false, false, [47140], []⟩,
        ⟨112516, true, false, [], [21719, 86325]⟩,
        ⟨112520, true, false, [], [86325]⟩
      ]⟩,
    ⟨[86523, 5], [47151, 84481], .contexts [
        ⟨112515, true, false, [47140], [5]⟩,
        ⟨46258, true, false, [47140, 21728], [5]⟩,
        ⟨28, false, false, [47140, 21728, 84481], []⟩,
        ⟨46186, true, false, [47140], [84481]⟩,
        ⟨46256, false, false, [47140], []⟩,
        ⟨112516, true, false, [], [21727, 84481]⟩,
        ⟨112523, true, false, [], [84481]⟩
      ]⟩,
    ⟨[86523, 7], [47149, 85255], .contexts [
        ⟨112515, true, false, [47140], [7]⟩,
        ⟨46245, false, false, [47140], []⟩,
        ⟨46263, false, false, [47140], []⟩,
        ⟨112516, true, false, [], [21751, 85255]⟩,
        ⟨112522, true, false, [], [85255]⟩
      ]⟩,
    ⟨[86523, 9], [86521], .contexts [
        ⟨37294, false, false, [], []⟩,
        ⟨37407, false, false, [], []⟩
      ]⟩,
    ⟨[86523, 11], [47125, 85501], .contexts [
        ⟨37296, false, false, [], []⟩,
        ⟨112512, false, false, [], []⟩
      ]⟩,
    ⟨[86523, 13], [47139, 87797], .contexts [
        ⟨112515, true, false, [47140], [13]⟩,
        ⟨46050, false, false, [47140], []⟩,
        ⟨46064, false, false, [47140], []⟩,
        ⟨112517, true, false, [], [87797]⟩,
        ⟨112518, true, false, [], [87797]⟩
      ]⟩,
    ⟨[86523, 15], [47143, 85379], .contexts [
        ⟨112515, true, false, [47140], [15]⟩,
        ⟨46052, false, false, [47140], []⟩,
        ⟨106222, false, false, [47140], []⟩,
        ⟨112518, true, false, [], [41319, 85379]⟩,
        ⟨112519, true, false, [], [85379]⟩
      ]⟩,
    ⟨[86529, 1], [20993, 86533], .contexts [
        ⟨43683, false, false, [], []⟩,
        ⟨43664, false, false, [], []⟩
      ]⟩,
    ⟨[86529, 3], [47129, 83195], .contexts [
        ⟨112500, true, false, [47126], [3]⟩,
        ⟨65145, false, false, [47126], []⟩,
        ⟨65144, false, false, [47126], []⟩,
        ⟨112503, true, false, [], [83195]⟩
      ]⟩,
    ⟨[86529, 5], [47131, 88707], .contexts [
        ⟨112500, true, false, [47126], [5]⟩,
        ⟨65152, false, false, [47126], []⟩,
        ⟨66896, false, false, [47126], []⟩,
        ⟨112501, true, false, [], [26037, 88707]⟩,
        ⟨112504, true, false, [], [88707]⟩
      ]⟩,
    ⟨[86529, 7], [47129, 90225], .contexts [
        ⟨112500, true, false, [47126], [7]⟩,
        ⟨65158, false, false, [47126], []⟩,
        ⟨65155, false, false, [47126], []⟩,
        ⟨112503, true, false, [], [90225]⟩
      ]⟩,
    ⟨[86529, 9], [47137, 92665], .contexts [
        ⟨112500, true, false, [47126], [9]⟩,
        ⟨79610, false, false, [47126], []⟩,
        ⟨108793, false, false, [47126, 30157], []⟩,
        ⟨112501, true, false, [], [30157, 44015, 92665]⟩,
        ⟨112508, true, false, [], [44015, 92665]⟩,
        ⟨112509, true, false, [], [92665]⟩
      ]⟩,
    ⟨[86529, 11], [47125, 90615], .contexts [
        ⟨112500, true, false, [47126], [11]⟩,
        ⟨65159, false, false, [47126], []⟩,
        ⟨62093, false, false, [47126], []⟩,
        ⟨112506, true, false, [], [90615]⟩,
        ⟨112506, true, false, [], [90615]⟩,
        ⟨112505, true, false, [], [90615]⟩
      ]⟩,
    ⟨[86529, 13], [47125, 85499], .contexts [
        ⟨37304, false, false, [], []⟩,
        ⟨112510, false, false, [], []⟩
      ]⟩,
    ⟨[86531], [20989, 86529], .contexts [
        ⟨112494, false, false, [], []⟩
      ]⟩,
    ⟨[86529, 15], [20989, 86529], .contexts [
        ⟨37306, false, false, [], []⟩,
        ⟨163105, false, false, [], []⟩
      ]⟩,
    ⟨[86533, 1], [20989, 86529], .contexts [
        ⟨37311, false, false, [], []⟩,
        ⟨163105, false, false, [], []⟩
      ]⟩,
    ⟨[86533, 3], [86535], .contexts [
        ⟨37313, false, false, [], []⟩,
        ⟨37399, false, false, [], []⟩
      ]⟩,
    ⟨[86533, 5], [47109, 88703], .contexts [
        ⟨112488, true, false, [47096], [5]⟩,
        ⟨55614, false, false, [47096], []⟩,
        ⟨103396, false, false, [47096], []⟩,
        ⟨112477, true, false, [], [38431, 88703]⟩,
        ⟨112489, true, false, [], [88703]⟩
      ]⟩,
    ⟨[86533, 7], [47113, 86911], .contexts [
        ⟨112488, true, false, [47096], [7]⟩,
        ⟨105041, true, false, [47096, 39962], [7]⟩,
        ⟨66905, false, false, [47096, 39962], []⟩,
        ⟨66921, false, false, [47096, 39962], []⟩,
        ⟨105042, true, false, [47096], [26443, 86911]⟩,
        ⟨105043, true, false, [47096], [86911]⟩,
        ⟨112475, true, false, [], [39967, 86911]⟩,
        ⟨112491, true, false, [], [86911]⟩
      ]⟩,
    ⟨[86533, 9], [47115, 91625], .contexts [
        ⟨112488, true, false, [47096], [9]⟩,
        ⟨105041, true, false, [47096, 39962], [9]⟩,
        ⟨66916, false, false, [47096, 39962], []⟩,
        ⟨66918, false, false, [47096, 39962], []⟩,
        ⟨105045, true, false, [47096], [91625]⟩,
        ⟨105045, true, false, [47096], [91625]⟩,
        ⟨105042, true, false, [47096], [91625]⟩,
        ⟨112475, true, false, [], [39965, 91625]⟩,
        ⟨112492, true, false, [], [91625]⟩
      ]⟩,
    ⟨[86533, 11], [47117, 96075], .contexts [
        ⟨112488, true, false, [47096], [11]⟩,
        ⟨105041, true, false, [47096, 39962], [11]⟩,
        ⟨96127, false, false, [47096, 39962], []⟩,
        ⟨102271, false, false, [47096, 39962, 35069], []⟩,
        ⟨105042, true, false, [47096], [35069, 37487, 96075]⟩,
        ⟨105046, true, false, [47096], [37487, 96075]⟩,
        ⟨105047, true, false, [47096], [96075]⟩,
        ⟨112475, true, false, [], [39971, 96075]⟩,
        ⟨112493, true, false, [], [96075]⟩
      ]⟩,
    ⟨[86533, 13], [47111, 87793], .contexts [
        ⟨112488, true, false, [47096], [13]⟩,
        ⟨93272, false, false, [47096], []⟩,
        ⟨105037, false, false, [47096, 34263], []⟩,
        ⟨112481, true, false, [], [39957, 87793]⟩,
        ⟨112490, true, false, [], [87793]⟩
      ]⟩,
    ⟨[86533, 15], [20989, 86533], .contexts [
        ⟨43667, false, false, [], []⟩,
        ⟨43679, false, false, [], []⟩
      ]⟩,
    ⟨[86535, 1], [47099, 87943], .contexts [
        ⟨112479, false, false, [], []⟩
      ]⟩,
    ⟨[86535, 3], [86533], .contexts [
        ⟨37315, false, false, [], []⟩,
        ⟨37401, false, false, [], []⟩
      ]⟩,
    ⟨[86535, 5], [86537], .contexts [
        ⟨37317, false, false, [], []⟩,
        ⟨37397, false, false, [], []⟩
      ]⟩,
    ⟨[86535, 7], [47107, 96723], .contexts [
        ⟨112474, true, false, [47096], [7]⟩,
        ⟨109487, false, false, [47096], []⟩,
        ⟨112475, true, false, [], [44573, 96723]⟩,
        ⟨112486, true, false, [], [96723]⟩
      ]⟩,
    ⟨[86535, 9], [47105, 69675, 87883], .contexts [
        ⟨112474, true, false, [47096], [9]⟩,
        ⟨105057, false, false, [47096], []⟩,
        ⟨112475, true, false, [], [39983, 91725]⟩,
        ⟨112485, true, false, [], [91725]⟩,
        ⟨138266, false, false, [47105], []⟩
      ]⟩,
    ⟨[86535, 11], [47103, 85715], .contexts [
        ⟨112474, true, false, [47096], [11]⟩,
        ⟨105050, true, false, [47096, 39974], [11]⟩,
        ⟨77477, false, false, [47096, 39974], []⟩,
        ⟨77496, false, false, [47096, 39974], []⟩,
        ⟨105054, true, false, [47096], [29561, 85715]⟩,
        ⟨105055, true, false, [47096], [85715]⟩,
        ⟨112475, true, false, [], [39981, 85715]⟩,
        ⟨112484, true, false, [], [85715]⟩
      ]⟩,
    ⟨[86535, 13], [47101, 90371], .contexts [
        ⟨112474, true, false, [47096], [13]⟩,
        ⟨93251, true, false, [47096, 34260], [13]⟩,
        ⟨59, false, false, [47096, 34260, 90371], []⟩,
        ⟨93252, true, false, [47096], [90371]⟩,
        ⟨112481, true, false, [], [90371]⟩
      ]⟩,
    ⟨[86535, 15], [20993, 86535], .contexts [
        ⟨43632, false, false, [], []⟩,
        ⟨43662, false, false, [], []⟩
      ]⟩,
    ⟨[86537, 1], [86539], .contexts [
        ⟨37321, false, false, [], []⟩,
        ⟨37395, false, false, [], []⟩
      ]⟩,
    ⟨[86537, 3], [47089, 87339], .contexts [
        ⟨112466, true, false, [47078], [3]⟩,
        ⟨47476, false, false, [47078], []⟩,
        ⟨47472, false, false, [47078], []⟩,
        ⟨112457, true, false, [], [22037, 87339]⟩,
        ⟨112467, true, false, [], [87339]⟩
      ]⟩,
    ⟨[86537, 5], [86535], .contexts [
        ⟨37319, false, false, [], []⟩,
        ⟨37399, false, false, [], []⟩
      ]⟩,
    ⟨[86537, 7], [19313, 86537], .contexts [
        ⟨37323, true, false, [], [7]⟩,
        ⟨37832, true, false, [19314], [1, 7]⟩,
        ⟨37832, true, false, [19314], [1, 7]⟩,
        ⟨37831, true, false, [19314], [1, 7]⟩,
        ⟨37822, true, false, [19314], [1, 7]⟩,
        ⟨37818, true, false, [19314], [1, 7]⟩,
        ⟨502, false, false, [19314, 86539], []⟩,
        ⟨37834, false, false, [19314], []⟩,
        ⟨37833, false, false, [19314], []⟩,
        ⟨37835, false, false, [19314], []⟩,
        ⟨37836, true, false, [], [86537]⟩,
        ⟨37836, true, false, [], [86537]⟩,
        ⟨37820, false, true, [], [86537]⟩
      ]⟩,
    ⟨[86537, 9], [21995, 87917], .contexts [
        ⟨47235, false, false, [], []⟩
      ]⟩,
    ⟨[86537, 11], [51709, 53735, 88393], .contexts [
        ⟨117526, true, false, [51706], [11]⟩,
        ⟨53, false, false, [51706, 89171], []⟩,
        ⟨117527, true, false, [], [89171]⟩,
        ⟨119874, false, false, [51709], []⟩
      ]⟩,
    ⟨[86537, 13], [47091, 91831], .contexts [
        ⟨112466, true, false, [47078], [13]⟩,
        ⟨67738, false, false, [47078], []⟩,
        ⟨112457, true, false, [], [26605, 91831]⟩,
        ⟨112470, true, false, [], [91831]⟩
      ]⟩,
    ⟨[86537, 15], [20989, 86537], .contexts [
        ⟨43572, false, false, [], []⟩,
        ⟨43629, false, false, [], []⟩
      ]⟩,
    ⟨[86539, 1], [86537], .contexts [
        ⟨37323, false, false, [], []⟩,
        ⟨37397, false, false, [], []⟩
      ]⟩,
    ⟨[86539, 3], [47083, 83937], .contexts [
        ⟨112456, true, false, [47078], [3]⟩,
        ⟨47452, false, false, [47078], []⟩,
        ⟨47448, false, false, [47078], []⟩,
        ⟨112457, true, false, [], [22025, 83937]⟩,
        ⟨112460, true, false, [], [83937]⟩
      ]⟩,
    ⟨[86539, 5], [47081, 87943], .contexts [
        ⟨112456, true, false, [47078], [5]⟩,
        ⟨47442, false, false, [47078], []⟩,
        ⟨47429, false, false, [47078], []⟩,
        ⟨112459, true, false, [], [87943]⟩,
        ⟨112459, true, false, [], [87943]⟩,
        ⟨112458, true, false, [], [87943]⟩
      ]⟩,
    ⟨[86539, 7], [19315, 86539], .contexts [
        ⟨37822, false, false, [], []⟩,
        ⟨37831, false, false, [], []⟩
      ]⟩,
    ⟨[86539, 9], [86541], .contexts [
        ⟨37325, false, false, [], []⟩,
        ⟨37392, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2549. -/
def y322TCIndexRaw2549 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86539, 11], [47087, 53697, 88395], .contexts [
        ⟨112456, true, false, [47078], [11]⟩,
        ⟨88335, true, false, [47078, 32490], [11]⟩,
        ⟨53, false, false, [47078, 32490, 95133], []⟩,
        ⟨88336, true, false, [47078], [95133]⟩,
        ⟨112422, false, false, [47078, 32493], []⟩,
        ⟨112457, true, false, [], [32493, 47039, 89167]⟩,
        ⟨112463, true, false, [], [47039, 89167]⟩,
        ⟨112464, true, false, [], [89167]⟩,
        ⟨119857, false, false, [47087], []⟩
      ]⟩,
    ⟨[86539, 13], [47075, 92185], .contexts [
        ⟨112453, false, false, [], []⟩
      ]⟩,
    ⟨[86539, 15], [20993, 86539], .contexts [
        ⟨43495, false, false, [], []⟩,
        ⟨43565, false, false, [], []⟩
      ]⟩,
    ⟨[86541, 1], [19253, 86545], .contexts [
        ⟨37803, false, false, [], []⟩,
        ⟨37787, false, false, [], []⟩
      ]⟩,
    ⟨[86541, 3], [47067, 91117], .contexts [
        ⟨112442, true, false, [47064], [3]⟩,
        ⟨20, false, false, [47064, 91117], []⟩,
        ⟨112443, true, false, [], [91117]⟩
      ]⟩,
    ⟨[86541, 5], [47071, 92043], .contexts [
        ⟨112448, false, false, [], []⟩
      ]⟩,
    ⟨[86541, 7], [19313, 86541], .contexts [
        ⟨37809, false, false, [], []⟩,
        ⟨37814, false, false, [], []⟩
      ]⟩,
    ⟨[86541, 9], [86539], .contexts [
        ⟨37327, false, false, [], []⟩,
        ⟨37395, false, false, [], []⟩
      ]⟩,
    ⟨[86543], [19305, 86541], .contexts [
        ⟨37805, false, false, [], []⟩
      ]⟩,
    ⟨[86541, 11], [19305, 86541], .contexts [
        ⟨37329, false, false, [], []⟩,
        ⟨163144, false, false, [], []⟩
      ]⟩,
    ⟨[86541, 13], [31873, 90097], .contexts [
        ⟨86195, false, false, [], []⟩
      ]⟩,
    ⟨[86541, 15], [20989, 86541], .contexts [
        ⟨43406, false, false, [], []⟩,
        ⟨43489, false, false, [], []⟩
      ]⟩,
    ⟨[86545, 1], [19305, 86541], .contexts [
        ⟨37334, false, false, [], []⟩,
        ⟨163144, false, false, [], []⟩
      ]⟩,
    ⟨[86545, 3], [20855, 86545], .contexts [
        ⟨37338, true, false, [], [3]⟩,
        ⟨42850, true, false, [20708], [13, 3]⟩,
        ⟨42850, true, false, [20708], [13, 3]⟩,
        ⟨42849, true, false, [20708], [13, 3]⟩,
        ⟨42517, true, false, [20708], [13, 3]⟩,
        ⟨42515, true, false, [20708], [13, 3]⟩,
        ⟨514, false, false, [20708, 86547], []⟩,
        ⟨37781, false, false, [20708], []⟩,
        ⟨37780, false, false, [20708], []⟩,
        ⟨37783, false, false, [20708], []⟩,
        ⟨42852, true, false, [], [86545]⟩,
        ⟨42852, true, false, [], [86545]⟩,
        ⟨42851, true, false, [], [86545]⟩
      ]⟩,
    ⟨[86545, 5], [45943, 92039], .contexts [
        ⟨111203, false, false, [], []⟩
      ]⟩,
    ⟨[86545, 7], [19303, 86545], .contexts [
        ⟨37784, false, false, [], []⟩,
        ⟨37794, false, false, [], []⟩
      ]⟩,
    ⟨[86545, 9], [21943, 87919], .contexts [
        ⟨47166, true, false, [21944], [9]⟩,
        ⟨46, false, false, [21944, 87919], []⟩,
        ⟨47118, false, true, [], [87919]⟩,
        ⟨47163, false, false, [], []⟩
      ]⟩,
    ⟨[86545, 11], [19305, 86545], .contexts [
        ⟨37789, false, false, [], []⟩,
        ⟨37799, false, false, [], []⟩
      ]⟩,
    ⟨[86545, 13], [86547], .contexts [
        ⟨37336, false, false, [], []⟩,
        ⟨37387, false, false, [], []⟩
      ]⟩,
    ⟨[86545, 15], [20911, 86545], .contexts [
        ⟨43258, false, false, [], []⟩,
        ⟨43399, false, false, [], []⟩
      ]⟩,
    ⟨[86547, 1], [19247, 84239], .contexts [
        ⟨37733, true, false, [19238], [1]⟩,
        ⟨8, false, false, [19238, 84239], []⟩,
        ⟨37616, true, false, [], [84239]⟩,
        ⟨37678, false, false, [], []⟩
      ]⟩,
    ⟨[86547, 3], [20709, 86547], .contexts [
        ⟨42517, false, false, [], []⟩,
        ⟨42849, false, false, [], []⟩
      ]⟩,
    ⟨[86547, 5], [19247, 84243], .contexts [
        ⟨37767, false, false, [], []⟩,
        ⟨47155, false, false, [], []⟩
      ]⟩,
    ⟨[86547, 7], [19245, 86547], .contexts [
        ⟨37753, false, false, [], []⟩,
        ⟨37778, false, false, [], []⟩
      ]⟩,
    ⟨[86547, 9], [21943, 48395, 84139], .contexts [
        ⟨47117, false, false, [], []⟩,
        ⟨113736, false, false, [21943], []⟩
      ]⟩,
    ⟨[86547, 11], [19253, 86547], .contexts [
        ⟨37760, false, false, [], []⟩,
        ⟨37785, false, false, [], []⟩
      ]⟩,
    ⟨[86547, 13], [86545], .contexts [
        ⟨37338, false, false, [], []⟩,
        ⟨37389, false, false, [], []⟩
      ]⟩,
    ⟨[86547, 15], [86549], .contexts [
        ⟨37340, false, false, [], []⟩,
        ⟨37385, false, false, [], []⟩
      ]⟩,
    ⟨[86549, 1], [86551], .contexts [
        ⟨37344, false, false, [], []⟩,
        ⟨37382, false, false, [], []⟩
      ]⟩,
    ⟨[86549, 3], [20705, 86549], .contexts [
        ⟨42510, false, false, [], []⟩
      ]⟩,
    ⟨[86549, 5], [28299, 92689], .contexts [
        ⟨73622, false, false, [], []⟩
      ]⟩,
    ⟨[86549, 7], [19303, 86549], .contexts [
        ⟨37723, false, false, [], []⟩,
        ⟨37746, false, false, [], []⟩
      ]⟩,
    ⟨[86549, 9], [20847, 82967], .contexts [
        ⟨42843, false, false, [], []⟩,
        ⟨43064, false, false, [], []⟩
      ]⟩,
    ⟨[86549, 11], [19305, 86549], .contexts [
        ⟨37729, false, false, [], []⟩,
        ⟨37754, false, false, [], []⟩
      ]⟩,
    ⟨[86549, 13], [20913, 86549], .contexts [
        ⟨43071, false, false, [], []⟩,
        ⟨43254, false, false, [], []⟩
      ]⟩,
    ⟨[86549, 15], [86547], .contexts [
        ⟨37342, false, false, [], []⟩,
        ⟨37387, false, false, [], []⟩
      ]⟩,
    ⟨[86551, 1], [86549], .contexts [
        ⟨37346, false, false, [], []⟩,
        ⟨37385, false, false, [], []⟩
      ]⟩,
    ⟨[86551, 3], [20607, 84233], .contexts [
        ⟨37348, false, false, [], []⟩,
        ⟨42294, false, false, [], []⟩
      ]⟩,
    ⟨[86551, 5], [20851, 86113], .contexts [
        ⟨42847, false, false, [], []⟩
      ]⟩,
    ⟨[86551, 7], [19245, 86551], .contexts [
        ⟨37669, false, false, [], []⟩,
        ⟨37664, false, false, [], []⟩
      ]⟩,
    ⟨[86551, 9], [20697, 85855], .contexts [
        ⟨42503, true, false, [20694], [9]⟩,
        ⟨46, false, false, [20694, 85855], []⟩,
        ⟨42504, true, false, [], [85855]⟩
      ]⟩,
    ⟨[86551, 11], [19253, 86551], .contexts [
        ⟨37675, false, false, [], []⟩,
        ⟨37671, false, false, [], []⟩
      ]⟩,
    ⟨[86551, 13], [73019, 96891], .contexts [
        ⟨142974, true, false, [73016], [13]⟩,
        ⟨59, false, false, [73016, 96891], []⟩,
        ⟨142975, true, false, [], [96891]⟩
      ]⟩,
    ⟨[86551, 15], [19247, 84239], .contexts [
        ⟨37683, false, false, [], []⟩,
        ⟨37678, false, false, [], []⟩
      ]⟩,
    ⟨[86563], [19229, 85091], .contexts [
        ⟨37595, false, false, [], []⟩
      ]⟩,
    ⟨[86561, 1], [19229, 85091], .contexts [
        ⟨37365, false, false, [], []⟩,
        ⟨163180, false, false, [], []⟩
      ]⟩,
    ⟨[86561, 3], [19193, 82975], .contexts [
        ⟨37541, false, false, [], []⟩
      ]⟩,
    ⟨[86561, 5], [19205, 86561], .contexts [
        ⟨37538, true, false, [19194], [5]⟩,
        ⟨68, false, false, [19194, 85487], []⟩,
        ⟨69, false, false, [19194, 85487], []⟩,
        ⟨32343, false, false, [19194], [13]⟩,
        ⟨32346, false, false, [19194], [13]⟩,
        ⟨37543, false, false, [19194], [13]⟩,
        ⟨37544, false, false, [19194], [13]⟩,
        ⟨37544, false, false, [19194], [13]⟩,
        ⟨37518, false, false, [19194, 18249], []⟩,
        ⟨37545, true, false, [19194], [86561]⟩,
        ⟨37515, false, false, [19194, 19203], []⟩,
        ⟨37539, true, false, [], [19203, 86561]⟩,
        ⟨37546, true, false, [], [86561]⟩
      ]⟩,
    ⟨[86561, 7], [19209, 86561], .contexts [
        ⟨37538, true, false, [19194], [7]⟩,
        ⟨73, false, false, [19194, 85487], []⟩,
        ⟨74, false, false, [19194, 85487], []⟩,
        ⟨32328, false, false, [19194], [13]⟩,
        ⟨32330, false, false, [19194], [13]⟩,
        ⟨32326, false, false, [19194], [13]⟩,
        ⟨32327, false, false, [19194], [13]⟩,
        ⟨32327, false, false, [19194], [13]⟩,
        ⟨37518, false, false, [19194, 15743], []⟩,
        ⟨37547, true, false, [19194], [86561]⟩,
        ⟨37515, false, false, [19194, 19207], []⟩,
        ⟨37539, true, false, [], [19207, 86561]⟩,
        ⟨37548, true, false, [], [86561]⟩
      ]⟩,
    ⟨[86561, 9], [19213, 86561], .contexts [
        ⟨37551, false, false, [], []⟩
      ]⟩,
    ⟨[86561, 11], [19215, 82995], .contexts [
        ⟨37363, false, false, [], []⟩,
        ⟨37557, false, false, [], []⟩
      ]⟩,
    ⟨[86561, 13], [19193, 85487], .contexts [
        ⟨37520, false, false, [], []⟩,
        ⟨114372, false, false, [], []⟩
      ]⟩,
    ⟨[86561, 15], [41029, 48587, 88919], .contexts [
        ⟨106004, false, false, [], []⟩,
        ⟨113920, false, false, [41029], []⟩
      ]⟩,
    ⟨[86565, 1], [19161, 85489], .contexts [
        ⟨37477, false, false, [], []⟩,
        ⟨37482, false, false, [], []⟩
      ]⟩,
    ⟨[86565, 3], [19169, 83475], .contexts [
        ⟨37494, false, false, [], []⟩,
        ⟨37521, false, false, [], []⟩
      ]⟩,
    ⟨[86565, 5], [19179, 86565], .contexts [
        ⟨37499, false, false, [19176], [86565, 5]⟩,
        ⟨37498, false, false, [19176, 19173], [86565, 5]⟩,
        ⟨37497, true, false, [19176, 19173, 19159], [5]⟩,
        ⟨37473, true, false, [19176, 19173], [5]⟩,
        ⟨37495, false, false, [19176], [85489, 1, 5]⟩,
        ⟨32363, true, false, [19176, 19161], [1, 5]⟩,
        ⟨37484, true, false, [19176], [5, 1, 5]⟩,
        ⟨1152, false, false, [19176, 86565], []⟩,
        ⟨37487, false, false, [19176], []⟩,
        ⟨37490, false, false, [19176], []⟩,
        ⟨37501, true, false, [], [86565]⟩,
        ⟨37501, true, false, [], [86565]⟩,
        ⟨37500, true, false, [], [86565]⟩
      ]⟩,
    ⟨[86565, 7], [19185, 86565], .contexts [
        ⟨37503, false, false, [19182], [86565, 7]⟩,
        ⟨37498, false, false, [19182, 19181], [86565, 7]⟩,
        ⟨37497, true, false, [19182, 19181, 19159], [7]⟩,
        ⟨37473, true, false, [19182, 19181], [7]⟩,
        ⟨37502, false, false, [19182], [85489, 1, 7]⟩,
        ⟨32365, true, false, [19182, 19161], [1, 7]⟩,
        ⟨37484, true, false, [19182], [7, 1, 7]⟩,
        ⟨4091, false, false, [19182, 86565], []⟩,
        ⟨37487, false, false, [19182], []⟩,
        ⟨37490, false, false, [19182], []⟩,
        ⟨37505, true, false, [], [86565]⟩,
        ⟨37505, true, false, [], [86565]⟩,
        ⟨37504, true, false, [], [86565]⟩
      ]⟩,
    ⟨[86565, 9], [19189, 84595], .contexts [
        ⟨37512, false, false, [], []⟩
      ]⟩,
    ⟨[86565, 11], [28119, 92503], .contexts [
        ⟨72791, true, false, [19174], [11]⟩,
        ⟨53, false, false, [19174, 92503], []⟩,
        ⟨72792, true, false, [], [92503]⟩
      ]⟩,
    ⟨[86565, 13], [19229, 85091], .contexts [
        ⟨37370, false, false, [], []⟩,
        ⟨163180, false, false, [], []⟩
      ]⟩,
    ⟨[86565, 15], [19165, 86565], .contexts [
        ⟨37372, false, false, [], []⟩,
        ⟨37496, false, false, [], []⟩
      ]⟩,
    ⟨[86571, 1], [19333, 85217], .contexts [
        ⟨37952, false, false, [], []⟩,
        ⟨37971, false, false, [], []⟩
      ]⟩,
    ⟨[86571, 3], [17753, 78547], .contexts [
        ⟨37958, false, false, [], []⟩,
        ⟨37955, false, false, [], []⟩
      ]⟩,
    ⟨[86571, 5], [17759, 85493], .contexts [
        ⟨37961, false, false, [], []⟩,
        ⟨37960, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2550. -/
def y322TCIndexRaw2550 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86571, 7], [17767, 86571], .contexts [
        ⟨37949, true, false, [], [7]⟩,
        ⟨73, false, false, [85851], []⟩,
        ⟨74, false, false, [85851], []⟩,
        ⟨33934, false, false, [], [13]⟩,
        ⟨37945, false, false, [17767], []⟩,
        ⟨37963, false, false, [], []⟩,
        ⟨37964, false, false, [17767], []⟩,
        ⟨33910, true, false, [], [86571]⟩,
        ⟨37963, false, false, [], []⟩
      ]⟩,
    ⟨[86571, 9], [18535, 86571], .contexts [
        ⟨37969, false, false, [], []⟩,
        ⟨37966, false, false, [], []⟩
      ]⟩,
    ⟨[86571, 11], [17963, 85221], .contexts [
        ⟨37970, false, false, [], []⟩,
        ⟨30720, false, false, [], []⟩
      ]⟩,
    ⟨[86571, 13], [20313, 83641], .contexts [
        ⟨37946, false, false, [], []⟩,
        ⟨41829, false, false, [], []⟩
      ]⟩,
    ⟨[86571, 15], [17753, 85105], .contexts [
        ⟨37992, false, false, [], []⟩,
        ⟨37988, false, false, [], []⟩
      ]⟩,
    ⟨[86577, 1], [86579], .contexts [
        ⟨38104, false, false, [], []⟩,
        ⟨38106, false, false, [], []⟩
      ]⟩,
    ⟨[86577, 3], [16429, 86577], .contexts [
        ⟨38087, false, false, [], []⟩,
        ⟨38082, false, false, [], []⟩
      ]⟩,
    ⟨[86577, 5], [323, 86577], .contexts [
        ⟨38092, false, false, [], []⟩,
        ⟨38088, false, false, [], []⟩
      ]⟩,
    ⟨[86577, 7], [16423, 86577], .contexts [
        ⟨38097, false, false, [], []⟩,
        ⟨38093, false, false, [], []⟩
      ]⟩,
    ⟨[86577, 9], [21331, 87713], .contexts [
        ⟨45213, false, false, [], []⟩
      ]⟩,
    ⟨[86577, 11], [17387, 86577], .contexts [
        ⟨38102, false, false, [], []⟩,
        ⟨38098, false, false, [], []⟩
      ]⟩,
    ⟨[86577, 13], [21385, 84083], .contexts [
        ⟨45277, false, false, [], []⟩
      ]⟩,
    ⟨[86577, 15], [20529, 84227], .contexts [
        ⟨38078, false, false, [], []⟩,
        ⟨157601, false, false, [], []⟩
      ]⟩,
    ⟨[86579, 1], [86577], .contexts [
        ⟨38105, false, false, [], []⟩,
        ⟨38079, false, false, [], []⟩
      ]⟩,
    ⟨[86579, 3], [86581], .contexts [
        ⟨38122, false, false, [], []⟩,
        ⟨38124, false, false, [], []⟩
      ]⟩,
    ⟨[86579, 5], [323, 86579], .contexts [
        ⟨38112, false, false, [], []⟩,
        ⟨38109, false, false, [], []⟩
      ]⟩,
    ⟨[86579, 7], [16423, 86579], .contexts [
        ⟨38116, false, false, [], []⟩,
        ⟨38113, false, false, [], []⟩
      ]⟩,
    ⟨[86579, 9], [20727, 85099], .contexts [
        ⟨42588, false, false, [], []⟩
      ]⟩,
    ⟨[86579, 11], [17387, 86579], .contexts [
        ⟨38120, false, false, [], []⟩,
        ⟨38117, false, false, [], []⟩
      ]⟩,
    ⟨[86579, 13], [47221, 94665], .contexts [
        ⟨112599, false, false, [], []⟩
      ]⟩,
    ⟨[86579, 15], [20631, 84231], .contexts [
        ⟨42375, true, false, [20628], [15]⟩,
        ⟨1, false, false, [20628, 84231], []⟩,
        ⟨42376, true, false, [], [84231]⟩
      ]⟩,
    ⟨[86581, 1], [16429, 86581], .contexts [
        ⟨38136, false, false, [], []⟩,
        ⟨38130, false, false, [], []⟩
      ]⟩,
    ⟨[86581, 3], [86579], .contexts [
        ⟨38123, false, false, [], []⟩,
        ⟨38106, false, false, [], []⟩
      ]⟩,
    ⟨[86581, 5], [86583], .contexts [
        ⟨38146, false, false, [], []⟩,
        ⟨38148, false, false, [], []⟩
      ]⟩,
    ⟨[86581, 7], [16423, 86581], .contexts [
        ⟨38140, false, false, [], []⟩,
        ⟨38137, false, false, [], []⟩
      ]⟩,
    ⟨[86581, 9], [21487, 87681], .contexts [
        ⟨45391, false, false, [], []⟩,
        ⟨45444, false, false, [], []⟩
      ]⟩,
    ⟨[86581, 11], [17387, 86581], .contexts [
        ⟨38144, false, false, [], []⟩,
        ⟨38141, false, false, [], []⟩
      ]⟩,
    ⟨[86581, 13], [90093], .contexts [
        ⟨59122, false, false, [], []⟩,
        ⟨59124, false, false, [], []⟩
      ]⟩,
    ⟨[86581, 15], [73023, 96891], .contexts [
        ⟨142979, true, false, [73020], [15]⟩,
        ⟨1, false, false, [73020, 96891], []⟩,
        ⟨142980, true, false, [], [96891]⟩
      ]⟩,
    ⟨[86583, 1], [16429, 86583], .contexts [
        ⟨38156, false, false, [], []⟩,
        ⟨38152, false, false, [], []⟩
      ]⟩,
    ⟨[86583, 3], [323, 86583], .contexts [
        ⟨38161, false, false, [], []⟩,
        ⟨38157, false, false, [], []⟩
      ]⟩,
    ⟨[86583, 5], [86581], .contexts [
        ⟨38147, false, false, [], []⟩,
        ⟨38124, false, false, [], []⟩
      ]⟩,
    ⟨[86583, 7], [21579, 86695], .contexts [
        ⟨45547, false, false, [], []⟩,
        ⟨45598, false, false, [], []⟩
      ]⟩,
    ⟨[86585], [21517, 85355], .contexts [
        ⟨45454, false, false, [], []⟩
      ]⟩,
    ⟨[86583, 9], [21517, 85355], .contexts [
        ⟨38168, false, false, [], []⟩,
        ⟨163233, false, false, [], []⟩
      ]⟩,
    ⟨[86583, 11], [17387, 86583], .contexts [
        ⟨38166, false, false, [], []⟩,
        ⟨38163, false, false, [], []⟩
      ]⟩,
    ⟨[21583, 87019], [21583, 41545, 86929], .contexts [
        ⟨106412, false, false, [21583], []⟩
      ]⟩,
    ⟨[86583, 13], [21583, 41545, 86929], .contexts [
        ⟨45553, false, false, [], []⟩,
        ⟨163236, false, false, [], []⟩
      ]⟩,
    ⟨[86583, 15], [21587, 86111], .contexts [
        ⟨45556, false, false, [], []⟩
      ]⟩,
    ⟨[86587, 1], [21531, 85351], .contexts [
        ⟨38189, false, false, [], []⟩,
        ⟨45468, false, false, [], []⟩
      ]⟩,
    ⟨[86587, 3], [323, 86587], .contexts [
        ⟨38180, true, false, [], [3]⟩,
        ⟨215, false, false, [86585], []⟩,
        ⟨216, false, false, [86585], []⟩,
        ⟨38182, false, false, [], []⟩,
        ⟨38183, false, false, [323], []⟩,
        ⟨3220, true, false, [], [86587]⟩,
        ⟨38181, false, false, [], []⟩
      ]⟩,
    ⟨[86587, 5], [21527, 82979], .contexts [
        ⟨45457, true, false, [21522], [5]⟩,
        ⟨41937, true, false, [21522, 20398], [5]⟩,
        ⟨28, false, false, [21522, 20398, 82979], []⟩,
        ⟨41938, true, false, [21522], [82979]⟩,
        ⟨45461, true, false, [], [20401, 82979]⟩,
        ⟨45465, true, false, [], [82979]⟩
      ]⟩,
    ⟨[86587, 7], [49109, 88847], .contexts [
        ⟨114451, true, false, [49106], [7]⟩,
        ⟨38, false, false, [49106, 88847], []⟩,
        ⟨114452, true, false, [], [88847]⟩
      ]⟩,
    ⟨[86587, 9], [17387, 86587], .contexts [
        ⟨38187, false, false, [], []⟩,
        ⟨38075, true, false, [], [86587]⟩,
        ⟨38186, false, false, [], []⟩
      ]⟩,
    ⟨[86587, 11], [21517, 85355], .contexts [
        ⟨38177, false, false, [], []⟩,
        ⟨163233, false, false, [], []⟩
      ]⟩,
    ⟨[86587, 13], [21529, 41119, 86933], .contexts [
        ⟨45457, true, false, [21522], [13]⟩,
        ⟨41955, true, false, [21522, 20410], [13]⟩,
        ⟨59, false, false, [21522, 20410, 87023], []⟩,
        ⟨41956, true, false, [21522], [87023]⟩,
        ⟨45461, true, false, [], [20413, 87023]⟩,
        ⟨45466, true, false, [], [87023]⟩,
        ⟨106036, false, false, [21529], []⟩
      ]⟩,
    ⟨[86587, 15], [21525, 85491], .contexts [
        ⟨45457, true, false, [21522], [15]⟩,
        ⟨40201, false, false, [21522], []⟩,
        ⟨45460, false, false, [21522], []⟩,
        ⟨45461, true, false, [], [20405, 85491]⟩,
        ⟨45462, true, false, [], [85491]⟩
      ]⟩,
    ⟨[86593, 1], [21549, 85319], .contexts [
        ⟨38198, false, false, [], []⟩,
        ⟨45485, false, false, [], []⟩
      ]⟩,
    ⟨[86593, 3], [21541, 81391], .contexts [
        ⟨45477, false, false, [], []⟩
      ]⟩,
    ⟨[86593, 5], [27647, 42261, 86353], .contexts [
        ⟨71134, true, false, [27644], [5]⟩,
        ⟨28, false, false, [27644, 92271], []⟩,
        ⟨71135, true, false, [], [92271]⟩,
        ⟨107140, false, false, [27647], []⟩
      ]⟩,
    ⟨[86593, 7], [27441, 41207, 85371], .contexts [
        ⟨70448, true, false, [27438], [7]⟩,
        ⟨38, false, false, [27438, 92181], []⟩,
        ⟨70449, true, false, [], [92181]⟩,
        ⟨106111, false, false, [27441], []⟩
      ]⟩,
    ⟨[86593, 9], [21545, 83225], .contexts [
        ⟨45480, false, false, [], []⟩
      ]⟩,
    ⟨[86593, 11], [21543, 83797], .contexts [
        ⟨45474, true, false, [21538], [11]⟩,
        ⟨39906, true, false, [21538, 19652], [11]⟩,
        ⟨53, false, false, [21538, 19652, 83797], []⟩,
        ⟨39904, false, true, [21538], [83797]⟩,
        ⟨39901, false, false, [21538], []⟩,
        ⟨45475, true, false, [], [19651, 83797]⟩,
        ⟨45478, true, false, [], [83797]⟩
      ]⟩,
    ⟨[86593, 13], [21547, 87575], .contexts [
        ⟨45474, true, false, [21538], [13]⟩,
        ⟨44736, true, false, [21538, 21276], [13]⟩,
        ⟨59, false, false, [21538, 21276, 87575], []⟩,
        ⟨44737, true, false, [21538], [87575]⟩,
        ⟨45475, true, false, [], [21279, 87575]⟩,
        ⟨45481, true, false, [], [87575]⟩
      ]⟩,
    ⟨[86593, 15], [21533, 85323], .contexts [
        ⟨38196, false, false, [], []⟩,
        ⟨45471, false, false, [], []⟩
      ]⟩,
    ⟨[86609, 1], [21593, 84335], .contexts [
        ⟨45635, false, false, [], []⟩,
        ⟨45678, false, false, [], []⟩
      ]⟩,
    ⟨[86609, 3], [22775, 48729, 85417], .contexts [
        ⟨50463, false, false, [], []⟩,
        ⟨114072, false, false, [22775], []⟩
      ]⟩,
    ⟨[86609, 5], [21599, 86609], .contexts [
        ⟨45564, false, false, [21594], [86609, 5]⟩,
        ⟨45506, true, false, [21594, 16865], [5]⟩,
        ⟨24846, true, false, [21594], [13, 5]⟩,
        ⟨913, false, false, [21594, 84101], []⟩,
        ⟨64, false, false, [21594, 84101], []⟩,
        ⟨45568, false, false, [21594], []⟩,
        ⟨45560, false, false, [21594, 21569], []⟩,
        ⟨45569, true, false, [], [21569, 86609]⟩,
        ⟨45570, true, false, [], [86609]⟩
      ]⟩,
    ⟨[86609, 7], [21841, 85709], .contexts [
        ⟨46582, false, false, [], []⟩
      ]⟩,
    ⟨[86609, 9], [36139, 39033, 92509], .contexts [
        ⟨99396, true, false, [36136], [9]⟩,
        ⟨46, false, false, [36136, 96747], []⟩,
        ⟨99397, true, false, [], [96747]⟩,
        ⟨104092, false, false, [36139], []⟩
      ]⟩,
    ⟨[86609, 11], [21593, 84339], .contexts [
        ⟨45563, false, false, [], []⟩
      ]⟩,
    ⟨[86609, 13], [21567, 84101], .contexts [
        ⟨38221, false, false, [], []⟩,
        ⟨99420, false, false, [], []⟩
      ]⟩,
    ⟨[86609, 15], [43533, 86317], .contexts [
        ⟨38223, false, false, [], []⟩,
        ⟨108346, false, false, [], []⟩
      ]⟩,
    ⟨[86617, 1], [86619], .contexts [
        ⟨38239, false, false, [], []⟩,
        ⟨38437, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2551. -/
def y322TCIndexRaw2551 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86617, 3], [21643, 86617], .contexts [
        ⟨45743, false, false, [], []⟩,
        ⟨45738, false, false, [], []⟩
      ]⟩,
    ⟨[86617, 5], [38513, 86311], .contexts [
        ⟨38237, false, false, [], []⟩,
        ⟨103492, false, false, [], []⟩
      ]⟩,
    ⟨[86617, 7], [44819, 89347], .contexts [
        ⟨109801, false, false, [], []⟩,
        ⟨143950, false, false, [], []⟩
      ]⟩,
    ⟨[86617, 9], [96943], .contexts [
        ⟨143928, false, false, [], []⟩,
        ⟨143930, false, false, [], []⟩
      ]⟩,
    ⟨[86617, 11], [26767, 86675], .contexts [
        ⟨68328, false, false, [], []⟩,
        ⟨143990, false, false, [], []⟩
      ]⟩,
    ⟨[86617, 13], [21653, 86617], .contexts [
        ⟨45790, false, false, [], []⟩,
        ⟨143956, false, false, [], []⟩
      ]⟩,
    ⟨[86617, 15], [22401, 39703, 88103], .contexts [
        ⟨48852, false, false, [], []⟩,
        ⟨104856, false, false, [22401], []⟩
      ]⟩,
    ⟨[86619, 1], [86617], .contexts [
        ⟨38241, false, false, [], []⟩,
        ⟨38438, false, false, [], []⟩
      ]⟩,
    ⟨[86619, 3], [35817, 58471, 91679], .contexts [
        ⟨98300, true, false, [35814], [3]⟩,
        ⟨20, false, false, [35814, 96549], []⟩,
        ⟨98301, true, false, [], [96549]⟩,
        ⟨125477, false, false, [35817], []⟩
      ]⟩,
    ⟨[86619, 5], [38513, 86309], .contexts [
        ⟨109943, true, false, [38514], [5]⟩,
        ⟨28, false, false, [38514, 86309], []⟩,
        ⟨103488, true, false, [], [86309]⟩
      ]⟩,
    ⟨[86619, 7], [53383, 89349], .contexts [
        ⟨119550, true, false, [53380], [7]⟩,
        ⟨38, false, false, [53380, 89349], []⟩,
        ⟨119551, true, false, [], [89349]⟩
      ]⟩,
    ⟨[86619, 9], [55977, 86479], .contexts [
        ⟨38243, false, false, [], []⟩,
        ⟨122588, false, false, [], []⟩
      ]⟩,
    ⟨[86619, 11], [57449, 86859], .contexts [
        ⟨124324, false, false, [], []⟩
      ]⟩,
    ⟨[86619, 13], [26769, 83683], .contexts [
        ⟨68323, false, false, [], []⟩,
        ⟨68377, false, false, [], []⟩
      ]⟩,
    ⟨[86619, 15], [26761, 91935], .contexts [
        ⟨68313, false, false, [], []⟩
      ]⟩,
    ⟨[86635, 1], [62809, 84653], .contexts [
        ⟨38272, false, false, [], []⟩,
        ⟨130670, false, false, [], []⟩
      ]⟩,
    ⟨[86635, 3], [37213, 51943, 85021], .contexts [
        ⟨101752, true, false, [37214], [3]⟩,
        ⟨20, false, false, [37214, 86131], []⟩,
        ⟨101750, false, true, [], [86131]⟩,
        ⟨117844, false, false, [37213], []⟩
      ]⟩,
    ⟨[86635, 5], [26863, 83693], .contexts [
        ⟨38270, false, false, [], []⟩,
        ⟨118155, false, false, [], []⟩
      ]⟩,
    ⟨[86635, 7], [33113, 84989], .contexts [
        ⟨90266, false, false, [], []⟩,
        ⟨90259, false, false, [], []⟩
      ]⟩,
    ⟨[86635, 9], [51493, 64213, 92129], .contexts [
        ⟨117307, false, false, [], []⟩,
        ⟨132339, false, false, [51493], []⟩
      ]⟩,
    ⟨[86635, 11], [36661, 38883, 83307], .contexts [
        ⟨100622, false, false, [], []⟩,
        ⟨103934, false, false, [36661], []⟩
      ]⟩,
    ⟨[86635, 13], [33087, 88223], .contexts [
        ⟨90194, false, false, [], []⟩,
        ⟨90255, false, false, [], []⟩
      ]⟩,
    ⟨[86635, 15], [37137, 51999, 85031], .contexts [
        ⟨101611, false, false, [], []⟩,
        ⟨117902, false, false, [37137], []⟩
      ]⟩,
    ⟨[86641, 1], [53063, 83877], .contexts [
        ⟨38284, false, false, [], []⟩,
        ⟨119203, false, false, [], []⟩
      ]⟩,
    ⟨[86641, 3], [53061, 63781, 85779], .contexts [
        ⟨119172, false, false, [], []⟩,
        ⟨131873, false, false, [53061], []⟩
      ]⟩,
    ⟨[86641, 5], [52139, 53041, 86821], .contexts [
        ⟨118064, true, false, [52136], [5]⟩,
        ⟨28, false, false, [52136, 90313], []⟩,
        ⟨118065, true, false, [], [90313]⟩,
        ⟨119163, false, false, [52139], []⟩
      ]⟩,
    ⟨[86641, 7], [59851, 63727, 85769], .contexts [
        ⟨127111, false, false, [], []⟩,
        ⟨131810, false, false, [59851], []⟩
      ]⟩,
    ⟨[86641, 9], [26899, 37363, 53069, 86817], .contexts [
        ⟨68681, false, false, [], []⟩,
        ⟨102627, false, false, [26899], []⟩,
        ⟨119181, false, false, [26899], []⟩
      ]⟩,
    ⟨[86641, 11], [52049, 84269], .contexts [
        ⟨38282, false, false, [], []⟩,
        ⟨118056, false, false, [], []⟩
      ]⟩,
    ⟨[86641, 13], [59095, 86833], .contexts [
        ⟨126227, false, false, [], []⟩
      ]⟩,
    ⟨[86641, 15], [53063, 83881], .contexts [
        ⟨119175, false, false, [], []⟩,
        ⟨127497, false, false, [], []⟩
      ]⟩,
    ⟨[86647, 1], [57255, 85737], .contexts [
        ⟨38296, false, false, [], []⟩,
        ⟨124105, false, false, [], []⟩
      ]⟩,
    ⟨[86647, 3], [58419, 84757], .contexts [
        ⟨125423, false, false, [], []⟩
      ]⟩,
    ⟨[86647, 5], [60227, 63727, 85771], .contexts [
        ⟨127525, false, false, [], []⟩,
        ⟨131819, false, false, [60227], []⟩
      ]⟩,
    ⟨[86647, 7], [60233, 85043], .contexts [
        ⟨127530, false, false, [], []⟩
      ]⟩,
    ⟨[86647, 9], [37153, 86647], .contexts [
        ⟨101629, false, false, [], []⟩,
        ⟨101753, false, false, [], []⟩
      ]⟩,
    ⟨[86647, 11], [26899, 57261, 85741], .contexts [
        ⟨68641, false, false, [], []⟩,
        ⟨124137, false, false, [26899], []⟩
      ]⟩,
    ⟨[86647, 13], [65653, 89025], .contexts [
        ⟨133920, false, false, [], []⟩
      ]⟩,
    ⟨[86647, 15], [53063, 83875], .contexts [
        ⟨38294, false, false, [], []⟩,
        ⟨119213, false, false, [], []⟩
      ]⟩,
    ⟨[86653, 1], [86655], .contexts [
        ⟨38308, false, false, [], []⟩,
        ⟨38410, false, false, [], []⟩
      ]⟩,
    ⟨[86653, 3], [52815, 89279], .contexts [
        ⟨118874, true, false, [52808], [3]⟩,
        ⟨83765, true, false, [52808, 31202], [3]⟩,
        ⟨20, false, false, [52808, 31202, 89279], []⟩,
        ⟨83711, true, false, [52808], [89279]⟩,
        ⟨83762, false, false, [52808], []⟩,
        ⟨118875, true, false, [], [31205, 89279]⟩,
        ⟨118880, true, false, [], [89279]⟩
      ]⟩,
    ⟨[86653, 5], [63711, 85765], .contexts [
        ⟨38306, false, false, [], []⟩,
        ⟨131793, false, false, [], []⟩
      ]⟩,
    ⟨[86653, 7], [36791, 52803, 85139], .contexts [
        ⟨100921, false, false, [], []⟩,
        ⟨118869, false, false, [36791], []⟩
      ]⟩,
    ⟨[86653, 9], [52813, 83391], .contexts [
        ⟨118874, true, false, [52808], [9]⟩,
        ⟨52042, false, false, [52808], []⟩,
        ⟨97460, false, false, [52808], []⟩,
        ⟨118878, true, false, [], [33035, 83391]⟩,
        ⟨118879, true, false, [], [83391]⟩
      ]⟩,
    ⟨[86653, 11], [26899, 50841, 89387], .contexts [
        ⟨68595, true, false, [26914], [11]⟩,
        ⟨53, false, false, [26914, 90843], []⟩,
        ⟨68596, true, false, [], [90843]⟩,
        ⟨118691, false, false, [26899], []⟩
      ]⟩,
    ⟨[86653, 13], [52817, 95267], .contexts [
        ⟨118874, true, false, [52808], [13]⟩,
        ⟨118012, false, false, [52808], []⟩,
        ⟨118875, true, false, [], [52093, 95267]⟩,
        ⟨118881, true, false, [], [95267]⟩
      ]⟩,
    ⟨[86653, 15], [66539, 93967], .contexts [
        ⟨134924, false, false, [], []⟩
      ]⟩,
    ⟨[86655, 1], [86653], .contexts [
        ⟨38310, false, false, [], []⟩,
        ⟨38412, false, false, [], []⟩
      ]⟩,
    ⟨[86655, 3], [36433, 52785, 85187], .contexts [
        ⟨100136, false, false, [], []⟩,
        ⟨118851, false, false, [36433], []⟩
      ]⟩,
    ⟨[86655, 5], [52811, 63697, 85763], .contexts [
        ⟨118886, false, false, [], []⟩,
        ⟨131779, false, false, [52811], []⟩
      ]⟩,
    ⟨[86655, 7], [36791, 52823, 92931], .contexts [
        ⟨100875, false, false, [], []⟩,
        ⟨127190, false, false, [36791], []⟩
      ]⟩,
    ⟨[86657], [53233, 84799], .contexts [
        ⟨120073, false, false, [], []⟩
      ]⟩,
    ⟨[86655, 9], [53233, 84799], .contexts [
        ⟨38312, false, false, [], []⟩,
        ⟨163315, false, false, [], []⟩
      ]⟩,
    ⟨[86655, 11], [26899, 90845], .contexts [
        ⟨68582, false, false, [], []⟩,
        ⟨68575, false, false, [], []⟩
      ]⟩,
    ⟨[86655, 13], [59967, 66811, 83747], .contexts [
        ⟨127231, false, false, [], []⟩,
        ⟨153670, false, false, [59967], []⟩
      ]⟩,
    ⟨[86655, 15], [66573, 93965], .contexts [
        ⟨134953, false, false, [], []⟩,
        ⟨138478, false, false, [], []⟩
      ]⟩,
    ⟨[86659, 1], [86661], .contexts [
        ⟨38320, false, false, [], []⟩,
        ⟨38404, false, false, [], []⟩
      ]⟩,
    ⟨[86659, 3], [26897, 89835], .contexts [
        ⟨68546, false, false, [], []⟩
      ]⟩,
    ⟨[86659, 5], [35353, 50821, 83401], .contexts [
        ⟨97097, true, false, [27342], [5]⟩,
        ⟨28, false, false, [27342, 96295], []⟩,
        ⟨97098, true, false, [], [96295]⟩,
        ⟨120068, false, false, [35353], []⟩
      ]⟩,
    ⟨[86659, 7], [26901, 91347], .contexts [
        ⟨68543, true, false, [26892], [7]⟩,
        ⟨68444, true, false, [26892, 26842], [7]⟩,
        ⟨38, false, false, [26892, 26842, 91347], []⟩,
        ⟨68445, true, false, [26892], [91347]⟩,
        ⟨68544, true, false, [], [26845, 91347]⟩,
        ⟨68549, true, false, [], [91347]⟩
      ]⟩,
    ⟨[86659, 9], [26899, 27335, 85465], .contexts [
        ⟨68548, false, false, [], []⟩,
        ⟨70129, false, false, [26899], []⟩
      ]⟩,
    ⟨[86659, 11], [53233, 84799], .contexts [
        ⟨38318, false, false, [], []⟩,
        ⟨163315, false, false, [], []⟩
      ]⟩,
    ⟨[86659, 13], [31333, 94421], .contexts [
        ⟨84297, false, false, [], []⟩,
        ⟨88133, false, false, [], []⟩
      ]⟩,
    ⟨[86659, 15], [26903, 86667], .contexts [
        ⟨68551, false, false, [], []⟩,
        ⟨88130, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2552. -/
def y322TCIndexRaw2552 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86661, 1], [86659], .contexts [
        ⟨38322, false, false, [], []⟩,
        ⟨38406, false, false, [], []⟩
      ]⟩,
    ⟨[86661, 3], [32397, 32383, 95125], .contexts [
        ⟨88090, true, false, [32394], [3]⟩,
        ⟨20, false, false, [32394, 95127], []⟩,
        ⟨88091, true, false, [], [95127]⟩,
        ⟨88103, false, false, [32397], []⟩
      ]⟩,
    ⟨[86661, 5], [57309, 83399], .contexts [
        ⟨124158, false, false, [], []⟩,
        ⟨131093, false, false, [], []⟩
      ]⟩,
    ⟨[86661, 7], [26889, 91345], .contexts [
        ⟨68538, false, false, [], []⟩,
        ⟨102631, false, false, [], []⟩
      ]⟩,
    ⟨[86661, 9], [37369, 70413, 89905], .contexts [
        ⟨102082, false, false, [], []⟩,
        ⟨139141, false, false, [37369], []⟩
      ]⟩,
    ⟨[86661, 11], [53233, 84797], .contexts [
        ⟨127649, true, false, [53230], [11]⟩,
        ⟨53, false, false, [53230, 84797], []⟩,
        ⟨119376, true, false, [], [84797]⟩
      ]⟩,
    ⟨[86663], [26885, 86661], .contexts [
        ⟨68539, false, false, [], []⟩
      ]⟩,
    ⟨[86661, 13], [26885, 86661], .contexts [
        ⟨38324, false, false, [], []⟩,
        ⟨163334, false, false, [], []⟩
      ]⟩,
    ⟨[86661, 15], [26887, 86665], .contexts [
        ⟨68536, false, false, [], []⟩,
        ⟨68556, false, false, [], []⟩
      ]⟩,
    ⟨[86665, 1], [86667], .contexts [
        ⟨38332, false, false, [], []⟩,
        ⟨38401, false, false, [], []⟩
      ]⟩,
    ⟨[86665, 3], [73983, 96981], .contexts [
        ⟨144563, true, false, [73980], [3]⟩,
        ⟨20, false, false, [73980, 96981], []⟩,
        ⟨144564, true, false, [], [96981]⟩
      ]⟩,
    ⟨[86665, 5], [38027, 94569], .contexts [
        ⟨102901, false, false, [], []⟩,
        ⟨125409, false, false, [], []⟩
      ]⟩,
    ⟨[86665, 7], [50933, 95395], .contexts [
        ⟨116670, false, false, [], []⟩,
        ⟨125405, false, false, [], []⟩
      ]⟩,
    ⟨[86665, 9], [37889, 95405], .contexts [
        ⟨102652, true, false, [37886], [9]⟩,
        ⟨46, false, false, [37886, 95405], []⟩,
        ⟨102653, true, false, [], [95405]⟩
      ]⟩,
    ⟨[86665, 11], [63129, 84795], .contexts [
        ⟨131008, false, false, [], []⟩
      ]⟩,
    ⟨[86665, 13], [26849, 68973, 84785], .contexts [
        ⟨68510, false, false, [], []⟩,
        ⟨137568, false, false, [26849], []⟩
      ]⟩,
    ⟨[86665, 15], [26885, 86661], .contexts [
        ⟨38330, false, false, [], []⟩,
        ⟨163334, false, false, [], []⟩
      ]⟩,
    ⟨[86667, 1], [86665], .contexts [
        ⟨38334, false, false, [], []⟩,
        ⟨38403, false, false, [], []⟩
      ]⟩,
    ⟨[86667, 3], [86669], .contexts [
        ⟨38336, false, false, [], []⟩,
        ⟨38400, false, false, [], []⟩
      ]⟩,
    ⟨[86667, 5], [74511, 97017], .contexts [
        ⟨145285, true, false, [74508], [5]⟩,
        ⟨28, false, false, [74508, 97017], []⟩,
        ⟨145286, true, false, [], [97017]⟩
      ]⟩,
    ⟨[86667, 7], [49541, 95393], .contexts [
        ⟨114981, false, false, [], []⟩
      ]⟩,
    ⟨[86667, 9], [27405, 85463], .contexts [
        ⟨70218, false, false, [], []⟩,
        ⟨88149, false, false, [], []⟩
      ]⟩,
    ⟨[86667, 11], [68261, 87759], .contexts [
        ⟨136889, false, false, [], []⟩
      ]⟩,
    ⟨[86667, 13], [32409, 95117], .contexts [
        ⟨88115, false, false, [], []⟩,
        ⟨88140, false, false, [], []⟩
      ]⟩,
    ⟨[86667, 15], [26849, 26893, 86659], .contexts [
        ⟨68449, true, false, [26846], [15]⟩,
        ⟨1, false, false, [26846, 91923], []⟩,
        ⟨68450, true, false, [], [91923]⟩,
        ⟨69328, false, false, [26849], []⟩
      ]⟩,
    ⟨[86669, 1], [75661, 97215], .contexts [
        ⟨147289, true, false, [75658], [1]⟩,
        ⟨8, false, false, [75658, 97215], []⟩,
        ⟨147290, true, false, [], [97215]⟩
      ]⟩,
    ⟨[86669, 3], [86667], .contexts [
        ⟨38338, false, false, [], []⟩,
        ⟨38401, false, false, [], []⟩
      ]⟩,
    ⟨[86669, 5], [86671], .contexts [
        ⟨38340, false, false, [], []⟩,
        ⟨38397, false, false, [], []⟩
      ]⟩,
    ⟨[86669, 7], [51377, 84815], .contexts [
        ⟨117181, false, false, [], []⟩,
        ⟨119415, false, false, [], []⟩
      ]⟩,
    ⟨[86669, 9], [31197, 46849, 50091, 87373], .contexts [
        ⟨83685, false, false, [], []⟩,
        ⟨161006, false, false, [31197], []⟩
      ]⟩,
    ⟨[86669, 11], [50103, 87377], .contexts [
        ⟨115626, false, false, [], []⟩,
        ⟨119426, false, false, [], []⟩
      ]⟩,
    ⟨[86669, 13], [75701, 97217], .contexts [
        ⟨147335, true, false, [75698], [13]⟩,
        ⟨59, false, false, [75698, 97217], []⟩,
        ⟨147336, true, false, [], [97217]⟩
      ]⟩,
    ⟨[86669, 15], [26827, 89835], .contexts [
        ⟨68429, false, false, [], []⟩
      ]⟩,
    ⟨[86671, 1], [86673], .contexts [
        ⟨38344, false, false, [], []⟩,
        ⟨38395, false, false, [], []⟩
      ]⟩,
    ⟨[86671, 3], [26853, 89827], .contexts [
        ⟨68453, true, false, [26850], [3]⟩,
        ⟨20, false, false, [26850, 89827], []⟩,
        ⟨68454, true, false, [], [89827]⟩
      ]⟩,
    ⟨[86671, 5], [86669], .contexts [
        ⟨38342, false, false, [], []⟩,
        ⟨38400, false, false, [], []⟩
      ]⟩,
    ⟨[86671, 7], [53251, 65395, 90795], .contexts [
        ⟨119407, false, false, [], []⟩,
        ⟨133647, false, false, [53251], []⟩
      ]⟩,
    ⟨[86671, 9], [73901, 96969], .contexts [
        ⟨144399, true, false, [73898], [9]⟩,
        ⟨46, false, false, [73898, 96969], []⟩,
        ⟨144400, true, false, [], [96969]⟩
      ]⟩,
    ⟨[86671, 11], [44763, 91307], .contexts [
        ⟨109717, false, false, [], []⟩,
        ⟨119429, false, false, [], []⟩
      ]⟩,
    ⟨[86671, 13], [75229, 97167], .contexts [
        ⟨146480, true, false, [75226], [13]⟩,
        ⟨59, false, false, [75226, 97167], []⟩,
        ⟨146481, true, false, [], [97167]⟩
      ]⟩,
    ⟨[86671, 15], [26827, 39735, 84515], .contexts [
        ⟨68413, false, false, [], []⟩,
        ⟨104838, false, false, [26827], []⟩
      ]⟩,
    ⟨[86673, 1], [86671], .contexts [
        ⟨38346, false, false, [], []⟩,
        ⟨38397, false, false, [], []⟩
      ]⟩,
    ⟨[86673, 3], [26825, 86673], .contexts [
        ⟨68408, false, false, [], []⟩,
        ⟨142926, false, false, [], []⟩
      ]⟩,
    ⟨[86673, 5], [75671, 97215], .contexts [
        ⟨147296, true, false, [75668], [5]⟩,
        ⟨28, false, false, [75668, 97215], []⟩,
        ⟨147297, true, false, [], [97215]⟩
      ]⟩,
    ⟨[86673, 7], [53251, 65395, 90797], .contexts [
        ⟨119399, false, false, [], []⟩,
        ⟨133656, false, false, [53251], []⟩
      ]⟩,
    ⟨[86673, 9], [86675], .contexts [
        ⟨38348, false, false, [], []⟩,
        ⟨38393, false, false, [], []⟩
      ]⟩,
    ⟨[86673, 11], [96889], .contexts [
        ⟨142919, false, false, [], []⟩,
        ⟨142920, false, false, [], []⟩
      ]⟩,
    ⟨[86673, 13], [20957, 86673], .contexts [
        ⟨43467, false, false, [], []⟩,
        ⟨142934, false, false, [], []⟩
      ]⟩,
    ⟨[86673, 15], [26817, 39721, 84513], .contexts [
        ⟨68375, false, false, [], []⟩,
        ⟨104819, false, false, [26817], []⟩
      ]⟩,
    ⟨[86675, 1], [50025, 86859], .contexts [
        ⟨115546, false, false, [], []⟩,
        ⟨124392, false, false, [], []⟩
      ]⟩,
    ⟨[86675, 3], [26813, 86675], .contexts [
        ⟨68368, false, false, [26808], [86675, 3]⟩,
        ⟨68333, true, false, [26808, 22377], [3]⟩,
        ⟨48823, true, false, [26808], [15, 3]⟩,
        ⟨499, false, false, [26808, 88195], []⟩,
        ⟨68349, false, false, [26808], []⟩,
        ⟨68348, false, false, [26808], []⟩,
        ⟨43367, false, false, [26808, 26771], []⟩,
        ⟨68369, true, false, [], [26771, 86675]⟩,
        ⟨68370, true, false, [], [86675]⟩
      ]⟩,
    ⟨[86675, 5], [26789, 91363], .contexts [
        ⟨68354, false, false, [], []⟩,
        ⟨124390, false, false, [], []⟩
      ]⟩,
    ⟨[86675, 7], [26801, 85269], .contexts [
        ⟨68363, false, false, [], []⟩,
        ⟨119408, false, false, [], []⟩
      ]⟩,
    ⟨[86675, 9], [86673], .contexts [
        ⟨38350, false, false, [], []⟩,
        ⟨38395, false, false, [], []⟩
      ]⟩,
    ⟨[86675, 11], [26765, 86617], .contexts [
        ⟨38352, false, false, [], []⟩,
        ⟨68327, false, false, [], []⟩
      ]⟩,
    ⟨[86675, 13], [20981, 86675], .contexts [
        ⟨43370, false, false, [], []⟩,
        ⟨43462, false, false, [], []⟩
      ]⟩,
    ⟨[86675, 15], [26773, 39703, 50007, 86865], .contexts [
        ⟨68332, false, false, [], []⟩,
        ⟨154610, false, false, [26773], []⟩
      ]⟩,
    ⟨[86683, 1], [20893, 86683], .contexts [
        ⟨38366, false, false, [], []⟩,
        ⟨43016, false, false, [], []⟩
      ]⟩,
    ⟨[86683, 3], [20895, 42593, 47713, 84035], .contexts [
        ⟨43013, false, false, [], []⟩,
        ⟨153444, false, false, [20895], []⟩
      ]⟩,
    ⟨[86683, 5], [25739, 91001], .contexts [
        ⟨63890, false, false, [], []⟩
      ]⟩,
    ⟨[86683, 7], [22641, 86423], .contexts [
        ⟨49835, false, false, [], []⟩
      ]⟩,
    ⟨[86683, 9], [20897, 83461], .contexts [
        ⟨43015, false, false, [], []⟩,
        ⟨43028, false, false, [], []⟩
      ]⟩,
    ⟨[86683, 11], [31125, 40845, 93825], .contexts [
        ⟨83568, true, false, [31122], [11]⟩,
        ⟨53, false, false, [31122, 94309], []⟩,
        ⟨83569, true, false, [], [94309]⟩,
        ⟨105808, false, false, [31125], []⟩
      ]⟩,
    ⟨[86683, 13], [26745, 40595, 85673], .contexts [
        ⟨68282, false, false, [], []⟩,
        ⟨105617, false, false, [26745], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2553. -/
def y322TCIndexRaw2553 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86683, 15], [20899, 83683], .contexts [
        ⟨38364, false, false, [], []⟩,
        ⟨43024, false, false, [], []⟩
      ]⟩,
    ⟨[86691, 1], [20583, 83469], .contexts [
        ⟨38379, false, false, [], []⟩,
        ⟨42264, false, false, [], []⟩
      ]⟩,
    ⟨[86691, 3], [20579, 85093], .contexts [
        ⟨42250, true, false, [20574], [3]⟩,
        ⟨38502, true, false, [20574, 19396], [3]⟩,
        ⟨20, false, false, [20574, 19396, 85093], []⟩,
        ⟨38500, false, true, [20574], [85093]⟩,
        ⟨38499, false, false, [20574], []⟩,
        ⟨42251, true, false, [], [19395, 85093]⟩,
        ⟨42252, true, false, [], [85093]⟩
      ]⟩,
    ⟨[86691, 5], [28521, 47689, 84033], .contexts [
        ⟨74351, false, false, [], []⟩,
        ⟨113074, false, false, [28521], []⟩
      ]⟩,
    ⟨[86691, 7], [19401, 86691], .contexts [
        ⟨38383, true, false, [], [7]⟩,
        ⟨38524, true, false, [19402], [9, 7]⟩,
        ⟨579, false, false, [19402, 86693], []⟩,
        ⟨47, false, false, [19402, 86693], []⟩,
        ⟨38383, false, false, [19402], []⟩,
        ⟨38382, false, false, [19402], []⟩,
        ⟨38382, false, false, [19402], []⟩,
        ⟨38525, false, false, [19402], []⟩,
        ⟨38526, true, false, [], [86691]⟩,
        ⟨38526, true, false, [], [86691]⟩,
        ⟨38506, false, true, [], [86691]⟩
      ]⟩,
    ⟨[86691, 9], [20575, 86691], .contexts [
        ⟨38381, false, false, [], []⟩,
        ⟨42253, false, false, [], []⟩
      ]⟩,
    ⟨[86691, 11], [20571, 83473], .contexts [
        ⟨42246, false, false, [], []⟩
      ]⟩,
    ⟨[86691, 13], [23761, 89209], .contexts [
        ⟨54853, false, false, [], []⟩
      ]⟩,
    ⟨[86691, 15], [20581, 83001], .contexts [
        ⟨42257, false, false, [], []⟩,
        ⟨42460, false, false, [], []⟩
      ]⟩,
    ⟨[86695, 1], [8673, 86695], .contexts [
        ⟨38551, false, false, [], []⟩,
        ⟨38546, false, false, [], []⟩
      ]⟩,
    ⟨[86695, 3], [19041, 86695], .contexts [
        ⟨38555, false, false, [], []⟩,
        ⟨38552, false, false, [], []⟩
      ]⟩,
    ⟨[86695, 5], [1739, 86695], .contexts [
        ⟨38559, false, false, [], []⟩,
        ⟨38556, false, false, [], []⟩
      ]⟩,
    ⟨[86695, 7], [21581, 86583], .contexts [
        ⟨45547, true, false, [21578], [7]⟩,
        ⟨38, false, false, [21578, 86583], []⟩,
        ⟨45548, true, false, [], [86583]⟩
      ]⟩,
    ⟨[86695, 9], [86337], .contexts [
        ⟨38542, false, false, [], []⟩,
        ⟨36576, false, false, [], []⟩
      ]⟩,
    ⟨[86697], [21607, 86695], .contexts [
        ⟨45606, false, false, [], []⟩
      ]⟩,
    ⟨[86695, 11], [21607, 86695], .contexts [
        ⟨38561, false, false, [], []⟩,
        ⟨163406, false, false, [], []⟩
      ]⟩,
    ⟨[86695, 13], [21605, 86699], .contexts [
        ⟨45611, false, false, [], []⟩,
        ⟨45667, false, false, [], []⟩
      ]⟩,
    ⟨[86695, 15], [30341, 93555], .contexts [
        ⟨80015, true, false, [30338], [15]⟩,
        ⟨1, false, false, [30338, 93555], []⟩,
        ⟨79957, true, false, [], [93555]⟩
      ]⟩,
    ⟨[86699, 1], [34665, 34707, 40285, 93053], .contexts [
        ⟨94897, false, false, [], []⟩,
        ⟨94919, false, false, [34665], []⟩,
        ⟨105358, false, false, [34665], []⟩
      ]⟩,
    ⟨[86699, 3], [19041, 86699], .contexts [
        ⟨38585, false, false, [], []⟩,
        ⟨38579, false, false, [], []⟩
      ]⟩,
    ⟨[86699, 5], [1739, 86699], .contexts [
        ⟨38590, false, false, [], []⟩,
        ⟨38586, false, false, [], []⟩
      ]⟩,
    ⟨[86699, 7], [21613, 41545, 86929], .contexts [
        ⟨45620, false, false, [], []⟩,
        ⟨106412, false, false, [21613], []⟩
      ]⟩,
    ⟨[86699, 9], [21607, 86339], .contexts [
        ⟨45674, true, false, [21604], [9]⟩,
        ⟨46, false, false, [21604, 86339], []⟩,
        ⟨45604, true, false, [], [86339]⟩
      ]⟩,
    ⟨[86699, 11], [21605, 86699], .contexts [
        ⟨45677, false, false, [], []⟩,
        ⟨45667, false, false, [], []⟩
      ]⟩,
    ⟨[86699, 13], [21607, 86695], .contexts [
        ⟨38575, false, false, [], []⟩,
        ⟨163406, false, false, [], []⟩
      ]⟩,
    ⟨[86699, 15], [86701], .contexts [
        ⟨38592, false, false, [], []⟩,
        ⟨38594, false, false, [], []⟩
      ]⟩,
    ⟨[86701, 1], [86703], .contexts [
        ⟨38609, false, false, [], []⟩,
        ⟨38612, false, false, [], []⟩
      ]⟩,
    ⟨[86701, 3], [19041, 86701], .contexts [
        ⟨38602, false, false, [], []⟩,
        ⟨38598, false, false, [], []⟩
      ]⟩,
    ⟨[86701, 5], [1739, 86701], .contexts [
        ⟨38607, false, false, [], []⟩,
        ⟨38604, false, false, [], []⟩
      ]⟩,
    ⟨[86701, 7], [71735, 96769], .contexts [
        ⟨140616, true, false, [71732], [7]⟩,
        ⟨38, false, false, [71732, 96769], []⟩,
        ⟨140617, true, false, [], [96769]⟩
      ]⟩,
    ⟨[86701, 9], [21607, 86341], .contexts [
        ⟨45730, false, false, [], []⟩
      ]⟩,
    ⟨[86701, 11], [21607, 86701], .contexts [
        ⟨45733, false, false, [], []⟩,
        ⟨45782, false, false, [], []⟩
      ]⟩,
    ⟨[86701, 13], [30361, 38987, 90737], .contexts [
        ⟨13, false, false, [30358], [30359, 86701, 13]⟩,
        ⟨80039, true, false, [30358], [13]⟩,
        ⟨59, false, false, [30358, 93557], []⟩,
        ⟨80040, true, false, [], [93557]⟩,
        ⟨104040, false, false, [30361], []⟩
      ]⟩,
    ⟨[86701, 15], [86699], .contexts [
        ⟨38593, false, false, [], []⟩,
        ⟨38576, false, false, [], []⟩
      ]⟩,
    ⟨[86703, 1], [86701], .contexts [
        ⟨38610, false, false, [], []⟩,
        ⟨38594, false, false, [], []⟩
      ]⟩,
    ⟨[86703, 3], [40263, 84351], .contexts [
        ⟨38618, false, false, [], []⟩,
        ⟨105346, false, false, [], []⟩
      ]⟩,
    ⟨[86703, 5], [1739, 86703], .contexts [
        ⟨38614, true, false, [], [5]⟩,
        ⟨98, false, false, [86701], []⟩,
        ⟨99, false, false, [86701], []⟩,
        ⟨38606, false, false, [], [1]⟩,
        ⟨38607, false, false, [], [1]⟩,
        ⟨38604, false, false, [], [1]⟩,
        ⟨38605, false, false, [], [1]⟩,
        ⟨38605, false, false, [], [1]⟩,
        ⟨38609, false, false, [1739], []⟩,
        ⟨38615, false, false, [], []⟩,
        ⟨38616, false, false, [1739], []⟩,
        ⟨15871, true, false, [], [86703]⟩,
        ⟨38615, false, false, [], []⟩
      ]⟩,
    ⟨[86703, 7], [41539, 92827], .contexts [
        ⟨106398, true, false, [41530], [7]⟩,
        ⟨75671, true, false, [41530, 24122], [7]⟩,
        ⟨38, false, false, [41530, 24122, 92827], []⟩,
        ⟨56538, false, true, [41530], [92827]⟩,
        ⟨106392, true, false, [], [24121, 92827]⟩,
        ⟨106404, true, false, [], [92827]⟩
      ]⟩,
    ⟨[86703, 9], [41535, 84099], .contexts [
        ⟨106398, true, false, [41530], [9]⟩,
        ⟨56568, false, false, [41530], []⟩,
        ⟨56560, false, false, [41530], []⟩,
        ⟨106392, true, false, [], [24135, 84099]⟩,
        ⟨106401, true, false, [], [84099]⟩
      ]⟩,
    ⟨[86703, 11], [21605, 86703], .contexts [
        ⟨45785, false, false, [], []⟩,
        ⟨45805, false, false, [], []⟩
      ]⟩,
    ⟨[86703, 13], [41537, 53503, 88433], .contexts [
        ⟨106403, false, false, [], []⟩,
        ⟨119680, false, false, [41537], []⟩
      ]⟩,
    ⟨[86703, 15], [34715, 40285, 93053], .contexts [
        ⟨94927, false, false, [], []⟩,
        ⟨105360, false, false, [34715], []⟩
      ]⟩,
    ⟨[86751, 1], [41743, 86755], .contexts [
        ⟨106642, false, false, [], []⟩
      ]⟩,
    ⟨[86751, 3], [41759, 86751], .contexts [
        ⟨106657, false, false, [], []⟩,
        ⟨114854, false, false, [], []⟩
      ]⟩,
    ⟨[86751, 5], [41747, 82887], .contexts [
        ⟨106645, false, false, [], []⟩,
        ⟨114790, false, false, [], []⟩
      ]⟩,
    ⟨[86751, 7], [41751, 86751], .contexts [
        ⟨106651, false, false, [], []⟩,
        ⟨114847, false, false, [], []⟩
      ]⟩,
    ⟨[86751, 9], [41755, 86751], .contexts [
        ⟨106654, false, false, [], []⟩
      ]⟩,
    ⟨[86751, 11], [49341, 92619], .contexts [
        ⟨114771, false, false, [], []⟩,
        ⟨114775, false, false, [], []⟩
      ]⟩,
    ⟨[86751, 13], [56517, 56533, 84687], .contexts [
        ⟨38684, false, false, [], []⟩,
        ⟨123218, false, false, [], []⟩,
        ⟨123227, false, false, [56517], []⟩
      ]⟩,
    ⟨[86753], [41745, 86751], .contexts [
        ⟨106646, false, false, [], []⟩
      ]⟩,
    ⟨[86751, 15], [41745, 86751], .contexts [
        ⟨38686, false, false, [], []⟩,
        ⟨163441, false, false, [], []⟩
      ]⟩,
    ⟨[86755, 1], [41745, 86751], .contexts [
        ⟨38692, false, false, [], []⟩,
        ⟨163441, false, false, [], []⟩
      ]⟩,
    ⟨[86755, 3], [86757], .contexts [
        ⟨38694, false, false, [], []⟩,
        ⟨38821, false, false, [], []⟩
      ]⟩,
    ⟨[86755, 5], [41719, 82891], .contexts [
        ⟨106619, false, false, [], []⟩,
        ⟨144472, false, false, [], []⟩
      ]⟩,
    ⟨[86755, 7], [41717, 86755], .contexts [
        ⟨106622, false, false, [], []⟩,
        ⟨144477, false, false, [], []⟩
      ]⟩,
    ⟨[86755, 9], [96975], .contexts [
        ⟨144461, false, false, [], []⟩,
        ⟨144462, false, false, [], []⟩
      ]⟩,
    ⟨[86755, 11], [41729, 91241], .contexts [
        ⟨106624, false, false, [], []⟩,
        ⟨114764, false, false, [], []⟩
      ]⟩,
    ⟨[86755, 13], [49329, 50457, 86395], .contexts [
        ⟨114756, false, false, [], []⟩,
        ⟨116107, false, false, [49329], []⟩
      ]⟩,
    ⟨[86755, 15], [41721, 86755], .contexts [
        ⟨106623, false, false, [], []⟩,
        ⟨144488, false, false, [], []⟩
      ]⟩,
    ⟨[86757, 1], [41727, 86757], .contexts [
        ⟨106610, false, false, [], []⟩
      ]⟩,
    ⟨[86757, 3], [86755], .contexts [
        ⟨38696, false, false, [], []⟩,
        ⟨38824, false, false, [], []⟩
      ]⟩,
    ⟨[86757, 5], [86759], .contexts [
        ⟨38698, false, false, [], []⟩,
        ⟨38819, false, false, [], []⟩
      ]⟩,
    ⟨[86757, 7], [41717, 86757], .contexts [
        ⟨106602, false, false, [], []⟩,
        ⟨144792, false, false, [], []⟩
      ]⟩,
    ⟨[86757, 9], [63357, 96565], .contexts [
        ⟨131332, false, false, [], []⟩,
        ⟨144469, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2554. -/
def y322TCIndexRaw2554 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86757, 11], [41731, 91235], .contexts [
        ⟨106614, false, false, [], []⟩,
        ⟨114757, false, false, [], []⟩
      ]⟩,
    ⟨[86757, 13], [49329, 50457, 86397], .contexts [
        ⟨114751, false, false, [], []⟩,
        ⟨116038, false, false, [49329], []⟩
      ]⟩,
    ⟨[86757, 15], [41721, 86757], .contexts [
        ⟨106607, false, false, [], []⟩
      ]⟩,
    ⟨[86761], [41703, 86759], .contexts [
        ⟨106587, false, false, [], []⟩
      ]⟩,
    ⟨[86759, 1], [41703, 86759], .contexts [
        ⟨38702, false, false, [], []⟩,
        ⟨163459, false, false, [], []⟩
      ]⟩,
    ⟨[86759, 3], [41705, 82895], .contexts [
        ⟨106586, false, false, [], []⟩,
        ⟨114736, false, false, [], []⟩
      ]⟩,
    ⟨[86759, 5], [86757], .contexts [
        ⟨38700, false, false, [], []⟩,
        ⟨38821, false, false, [], []⟩
      ]⟩,
    ⟨[86759, 7], [96989], .contexts [
        ⟨144783, false, false, [], []⟩,
        ⟨144784, false, false, [], []⟩
      ]⟩,
    ⟨[86759, 9], [41701, 86763], .contexts [
        ⟨106584, false, false, [], []⟩,
        ⟨144795, false, false, [], []⟩
      ]⟩,
    ⟨[86759, 11], [57111, 58633, 96579], .contexts [
        ⟨123914, false, false, [], []⟩,
        ⟨125647, false, false, [57111], []⟩
      ]⟩,
    ⟨[86759, 13], [49325, 50491, 54367, 84157], .contexts [
        ⟨114744, false, false, [], []⟩,
        ⟨153498, false, false, [49325], []⟩
      ]⟩,
    ⟨[86759, 15], [41709, 86759], .contexts [
        ⟨106592, false, false, [], []⟩,
        ⟨144806, false, false, [], []⟩
      ]⟩,
    ⟨[86763, 1], [19929, 86767], .contexts [
        ⟨40592, false, false, [], []⟩,
        ⟨40579, false, false, [], []⟩
      ]⟩,
    ⟨[86763, 3], [41677, 41687, 90629], .contexts [
        ⟨106553, false, false, [], []⟩,
        ⟨106562, false, false, [41677], []⟩
      ]⟩,
    ⟨[86763, 5], [63125, 96565], .contexts [
        ⟨131001, false, false, [], []⟩,
        ⟨132501, false, false, [], []⟩
      ]⟩,
    ⟨[86763, 7], [70815, 88239], .contexts [
        ⟨139567, false, false, [], []⟩,
        ⟨139574, false, false, [], []⟩
      ]⟩,
    ⟨[86763, 9], [41703, 86759], .contexts [
        ⟨38708, false, false, [], []⟩,
        ⟨163459, false, false, [], []⟩
      ]⟩,
    ⟨[86765], [19927, 86763], .contexts [
        ⟨106543, false, false, [], []⟩
      ]⟩,
    ⟨[86763, 11], [19927, 86763], .contexts [
        ⟨38710, false, false, [], []⟩,
        ⟨163473, false, false, [], []⟩
      ]⟩,
    ⟨[86763, 13], [57103, 95331], .contexts [
        ⟨123905, false, false, [], []⟩,
        ⟨130990, false, false, [], []⟩
      ]⟩,
    ⟨[86763, 15], [41675, 86763], .contexts [
        ⟨106551, false, false, [], []⟩,
        ⟨132508, false, false, [], []⟩
      ]⟩,
    ⟨[86767, 1], [19927, 86763], .contexts [
        ⟨38715, false, false, [], []⟩,
        ⟨163473, false, false, [], []⟩
      ]⟩,
    ⟨[86767, 3], [71441, 95767], .contexts [
        ⟨140279, true, false, [71442], [3]⟩,
        ⟨20, false, false, [71442, 95767], []⟩,
        ⟨140277, false, true, [], [95767]⟩
      ]⟩,
    ⟨[86767, 5], [58653, 64395, 96569], .contexts [
        ⟨125661, false, false, [], []⟩,
        ⟨132523, false, false, [58653], []⟩
      ]⟩,
    ⟨[86767, 7], [70825, 70857, 88235], .contexts [
        ⟨139579, false, false, [], []⟩,
        ⟨139611, false, false, [70825], []⟩
      ]⟩,
    ⟨[86767, 9], [49321, 86767], .contexts [
        ⟨114723, false, false, [], []⟩,
        ⟨114724, false, false, [], []⟩
      ]⟩,
    ⟨[86767, 11], [19927, 86767], .contexts [
        ⟨40584, false, false, [], []⟩,
        ⟨40585, false, false, [], []⟩
      ]⟩,
    ⟨[86767, 13], [86769], .contexts [
        ⟨38717, false, false, [], []⟩,
        ⟨38812, false, false, [], []⟩
      ]⟩,
    ⟨[86767, 15], [41667, 86767], .contexts [
        ⟨106542, false, false, [], []⟩,
        ⟨132532, false, false, [], []⟩
      ]⟩,
    ⟨[86769, 1], [69261, 91895], .contexts [
        ⟨137873, false, false, [], []⟩,
        ⟨139622, false, false, [], []⟩
      ]⟩,
    ⟨[86769, 3], [71045, 95765], .contexts [
        ⟨139863, false, false, [], []⟩
      ]⟩,
    ⟨[86769, 5], [72883, 96877], .contexts [
        ⟨142719, true, false, [72880], [5]⟩,
        ⟨28, false, false, [72880, 96877], []⟩,
        ⟨142720, true, false, [], [96877]⟩
      ]⟩,
    ⟨[86769, 7], [70861, 88233], .contexts [
        ⟨139621, false, false, [], []⟩,
        ⟨139616, false, false, [], []⟩
      ]⟩,
    ⟨[86769, 9], [49321, 86769], .contexts [
        ⟨114730, false, false, [], []⟩,
        ⟨114727, false, false, [], []⟩
      ]⟩,
    ⟨[86769, 11], [19929, 86769], .contexts [
        ⟨40576, false, false, [], []⟩,
        ⟨40577, false, false, [], []⟩
      ]⟩,
    ⟨[86769, 13], [86767], .contexts [
        ⟨38719, false, false, [], []⟩,
        ⟨38814, false, false, [], []⟩
      ]⟩,
    ⟨[86769, 15], [86771], .contexts [
        ⟨38721, false, false, [], []⟩,
        ⟨38810, false, false, [], []⟩
      ]⟩,
    ⟨[86771, 1], [86773], .contexts [
        ⟨38725, false, false, [], []⟩,
        ⟨38808, false, false, [], []⟩
      ]⟩,
    ⟨[86771, 3], [71045, 97011], .contexts [
        ⟨145218, true, false, [71042], [3]⟩,
        ⟨20, false, false, [71042, 97011], []⟩,
        ⟨139861, true, false, [], [97011]⟩
      ]⟩,
    ⟨[86771, 5], [61691, 94481], .contexts [
        ⟨135837, false, false, [], []⟩,
        ⟨135833, false, false, [], []⟩
      ]⟩,
    ⟨[86771, 7], [72809, 96865], .contexts [
        ⟨142529, false, false, [], []⟩
      ]⟩,
    ⟨[86771, 9], [49319, 86771], .contexts [
        ⟨123889, false, false, [], []⟩,
        ⟨138744, false, false, [], []⟩
      ]⟩,
    ⟨[86771, 11], [19927, 86771], .contexts [
        ⟨40570, false, false, [], []⟩,
        ⟨40571, false, false, [], []⟩
      ]⟩,
    ⟨[86771, 13], [41667, 86771], .contexts [
        ⟨106536, false, false, [], []⟩,
        ⟨114704, false, false, [], []⟩
      ]⟩,
    ⟨[86771, 15], [86769], .contexts [
        ⟨38723, false, false, [], []⟩,
        ⟨38812, false, false, [], []⟩
      ]⟩,
    ⟨[86773, 1], [86771], .contexts [
        ⟨38727, false, false, [], []⟩,
        ⟨38810, false, false, [], []⟩
      ]⟩,
    ⟨[86773, 3], [86775], .contexts [
        ⟨38729, false, false, [], []⟩,
        ⟨38806, false, false, [], []⟩
      ]⟩,
    ⟨[86773, 5], [61691, 94479], .contexts [
        ⟨129286, false, false, [], []⟩,
        ⟨135830, false, false, [], []⟩
      ]⟩,
    ⟨[86773, 7], [72809, 96867], .contexts [
        ⟨142554, true, false, [72806], [7]⟩,
        ⟨38, false, false, [72806, 96867], []⟩,
        ⟨142527, true, false, [], [96867]⟩
      ]⟩,
    ⟨[86773, 9], [76601, 97275], .contexts [
        ⟨148497, true, false, [76598], [9]⟩,
        ⟨46, false, false, [76598, 97275], []⟩,
        ⟨148498, true, false, [], [97275]⟩
      ]⟩,
    ⟨[86773, 11], [19929, 86773], .contexts [
        ⟨40563, false, false, [], []⟩,
        ⟨40564, false, false, [], []⟩
      ]⟩,
    ⟨[86773, 13], [49281, 49309, 91389], .contexts [
        ⟨114701, false, false, [], []⟩,
        ⟨114714, false, false, [49281], []⟩
      ]⟩,
    ⟨[86773, 15], [69261, 91895], .contexts [
        ⟨139627, false, false, [], []⟩,
        ⟨139622, false, false, [], []⟩
      ]⟩,
    ⟨[86775, 1], [61691, 94473], .contexts [
        ⟨129273, false, false, [], []⟩
      ]⟩,
    ⟨[86775, 3], [86773], .contexts [
        ⟨38731, false, false, [], []⟩,
        ⟨38808, false, false, [], []⟩
      ]⟩,
    ⟨[86775, 5], [86777], .contexts [
        ⟨38733, false, false, [], []⟩,
        ⟨38803, false, false, [], []⟩
      ]⟩,
    ⟨[86775, 7], [31929, 42899, 91397], .contexts [
        ⟨86369, false, false, [], []⟩,
        ⟨107754, false, false, [31929], []⟩
      ]⟩,
    ⟨[86775, 9], [31925, 47383, 83991], .contexts [
        ⟨86364, false, false, [], []⟩,
        ⟨112809, false, false, [31925], []⟩
      ]⟩,
    ⟨[86775, 11], [19927, 86775], .contexts [
        ⟨40553, false, false, [], []⟩,
        ⟨40559, false, false, [], []⟩
      ]⟩,
    ⟨[86775, 13], [49281, 91393], .contexts [
        ⟨114683, false, false, [], []⟩,
        ⟨114680, false, false, [], []⟩
      ]⟩,
    ⟨[86775, 15], [33121, 92285], .contexts [
        ⟨90283, false, false, [], []⟩,
        ⟨114684, false, false, [], []⟩
      ]⟩,
    ⟨[86777, 1], [86779], .contexts [
        ⟨38737, false, false, [], []⟩,
        ⟨38801, false, false, [], []⟩
      ]⟩,
    ⟨[86777, 3], [61691, 96997], .contexts [
        ⟨144923, true, false, [61692], [3]⟩,
        ⟨20, false, false, [61692, 96997], []⟩,
        ⟨129282, true, false, [], [96997]⟩
      ]⟩,
    ⟨[86777, 5], [86775], .contexts [
        ⟨38735, false, false, [], []⟩,
        ⟨38806, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2555. -/
def y322TCIndexRaw2555 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86777, 7], [76253, 97247], .contexts [
        ⟨148002, false, false, [], []⟩
      ]⟩,
    ⟨[86777, 9], [31925, 47383, 83989], .contexts [
        ⟨86356, false, false, [], []⟩,
        ⟨112799, false, false, [31925], []⟩
      ]⟩,
    ⟨[86777, 11], [19929, 86777], .contexts [
        ⟨40537, false, false, [], []⟩,
        ⟨40546, false, false, [], []⟩
      ]⟩,
    ⟨[86777, 13], [49281, 91395], .contexts [
        ⟨114671, false, false, [], []⟩,
        ⟨114678, false, false, [], []⟩
      ]⟩,
    ⟨[86777, 15], [49267, 93849], .contexts [
        ⟨114650, false, false, [], []⟩,
        ⟨114653, false, false, [], []⟩
      ]⟩,
    ⟨[86779, 1], [86777], .contexts [
        ⟨38739, false, false, [], []⟩,
        ⟨38803, false, false, [], []⟩
      ]⟩,
    ⟨[86779, 3], [22631, 86779], .contexts [
        ⟨49888, false, false, [], []⟩,
        ⟨114638, false, false, [], []⟩
      ]⟩,
    ⟨[86779, 5], [57095, 94473], .contexts [
        ⟨123883, false, false, [], []⟩
      ]⟩,
    ⟨[86779, 7], [76253, 97249], .contexts [
        ⟨148014, true, false, [76250], [7]⟩,
        ⟨38, false, false, [76250, 97249], []⟩,
        ⟨148000, true, false, [], [97249]⟩
      ]⟩,
    ⟨[86779, 9], [86781], .contexts [
        ⟨38741, false, false, [], []⟩,
        ⟨38799, false, false, [], []⟩
      ]⟩,
    ⟨[86779, 11], [19927, 86779], .contexts [
        ⟨40525, false, false, [], []⟩,
        ⟨40532, false, false, [], []⟩
      ]⟩,
    ⟨[86779, 13], [49281, 97245], .contexts [
        ⟨147961, true, false, [49282], [13]⟩,
        ⟨59, false, false, [49282, 97245], []⟩,
        ⟨114670, true, false, [], [97245]⟩
      ]⟩,
    ⟨[86779, 15], [49249, 93845], .contexts [
        ⟨114623, false, false, [], []⟩,
        ⟨114629, false, false, [], []⟩
      ]⟩,
    ⟨[86781, 1], [19493, 90485], .contexts [
        ⟨61251, false, false, [], []⟩,
        ⟨74856, false, false, [], []⟩
      ]⟩,
    ⟨[86781, 3], [22645, 86781], .contexts [
        ⟨49855, false, false, [], []⟩,
        ⟨49882, false, false, [], []⟩
      ]⟩,
    ⟨[86781, 5], [49237, 93833], .contexts [
        ⟨114592, false, false, [], []⟩,
        ⟨114595, false, false, [], []⟩
      ]⟩,
    ⟨[86781, 7], [56455, 87595], .contexts [
        ⟨123149, false, false, [], []⟩
      ]⟩,
    ⟨[86781, 9], [86779], .contexts [
        ⟨38743, false, false, [], []⟩,
        ⟨38801, false, false, [], []⟩
      ]⟩,
    ⟨[86781, 11], [86783], .contexts [
        ⟨38745, false, false, [], []⟩,
        ⟨38797, false, false, [], []⟩
      ]⟩,
    ⟨[86781, 13], [71053, 90027], .contexts [
        ⟨139874, true, false, [71050], [13]⟩,
        ⟨59, false, false, [71050, 90027], []⟩,
        ⟨139875, true, false, [], [90027]⟩
      ]⟩,
    ⟨[86781, 15], [19493, 56993, 87619], .contexts [
        ⟨61264, false, false, [], []⟩,
        ⟨123767, false, false, [19493], []⟩
      ]⟩,
    ⟨[86783, 1], [86785], .contexts [
        ⟨38749, false, false, [], []⟩,
        ⟨38795, false, false, [], []⟩
      ]⟩,
    ⟨[86783, 3], [22631, 86783], .contexts [
        ⟨49821, false, false, [], []⟩,
        ⟨49848, false, false, [], []⟩
      ]⟩,
    ⟨[86783, 5], [24607, 47443, 83999], .contexts [
        ⟨59045, false, false, [], []⟩,
        ⟨112854, false, false, [24607], []⟩
      ]⟩,
    ⟨[86783, 7], [22627, 83459], .contexts [
        ⟨49830, false, false, [], []⟩,
        ⟨49825, false, false, [], []⟩
      ]⟩,
    ⟨[86783, 9], [19929, 86783], .contexts [
        ⟨40503, false, false, [], []⟩,
        ⟨40514, false, false, [], []⟩
      ]⟩,
    ⟨[86783, 11], [86781], .contexts [
        ⟨38747, false, false, [], []⟩,
        ⟨38799, false, false, [], []⟩
      ]⟩,
    ⟨[86783, 13], [25753, 71067, 71089, 90023], .contexts [
        ⟨63917, false, false, [], []⟩,
        ⟨156946, false, false, [25753], []⟩
      ]⟩,
    ⟨[86783, 15], [22623, 56973, 87615], .contexts [
        ⟨49817, false, false, [], []⟩,
        ⟨123750, false, false, [22623], []⟩
      ]⟩,
    ⟨[86785, 1], [86783], .contexts [
        ⟨38751, false, false, [], []⟩,
        ⟨38797, false, false, [], []⟩
      ]⟩,
    ⟨[86785, 3], [22623, 88331], .contexts [
        ⟨49807, true, false, [22624], [3]⟩,
        ⟨49569, false, false, [22624], []⟩,
        ⟨49593, false, false, [22624], []⟩,
        ⟨49811, true, false, [], [88331]⟩
      ]⟩,
    ⟨[86785, 5], [28763, 47383, 83997], .contexts [
        ⟨74710, false, false, [], []⟩,
        ⟨112838, false, false, [28763], []⟩
      ]⟩,
    ⟨[86785, 7], [22627, 83461], .contexts [
        ⟨49813, false, false, [], []⟩,
        ⟨49822, false, false, [], []⟩
      ]⟩,
    ⟨[86785, 9], [19915, 86423], .contexts [
        ⟨40446, false, false, [], []⟩,
        ⟨40491, false, false, [], []⟩
      ]⟩,
    ⟨[86785, 11], [19493, 90485], .contexts [
        ⟨61243, false, false, [], []⟩,
        ⟨74856, false, false, [], []⟩
      ]⟩,
    ⟨[86785, 13], [19493, 83897], .contexts [
        ⟨38753, false, false, [], []⟩,
        ⟨39024, false, false, [], []⟩
      ]⟩,
    ⟨[86785, 15], [30801, 56959, 87613], .contexts [
        ⟨81860, false, false, [], []⟩,
        ⟨123741, false, false, [30801], []⟩
      ]⟩,
    ⟨[86791, 1], [19493, 83895], .contexts [
        ⟨38763, false, false, [], []⟩,
        ⟨40395, false, false, [], []⟩
      ]⟩,
    ⟨[86791, 3], [86793], .contexts [
        ⟨38765, false, false, [], []⟩,
        ⟨38789, false, false, [], []⟩
      ]⟩,
    ⟨[86791, 5], [19905, 85619], .contexts [
        ⟨40433, false, false, [], []⟩,
        ⟨92213, false, false, [], []⟩
      ]⟩,
    ⟨[86791, 7], [35487, 42033, 47157, 86521], .contexts [
        ⟨97405, true, false, [35484], [7]⟩,
        ⟨38, false, false, [35484, 96365], []⟩,
        ⟨97406, true, false, [], [96365]⟩,
        ⟨154853, false, false, [35487], []⟩
      ]⟩,
    ⟨[86791, 9], [19877, 20751, 85255], .contexts [
        ⟨40385, false, false, [], []⟩,
        ⟨42668, false, false, [19877], []⟩
      ]⟩,
    ⟨[86791, 11], [19463, 88089], .contexts [
        ⟨48250, false, false, [], []⟩
      ]⟩,
    ⟨[86791, 13], [23601, 89085], .contexts [
        ⟨54157, false, false, [], []⟩,
        ⟨54164, false, false, [], []⟩
      ]⟩,
    ⟨[86791, 15], [19493, 83899], .contexts [
        ⟨39012, false, false, [], []⟩,
        ⟨39008, false, false, [], []⟩
      ]⟩,
    ⟨[86793, 1], [19463, 84385], .contexts [
        ⟨38969, false, false, [], []⟩,
        ⟨38938, false, false, [], []⟩
      ]⟩,
    ⟨[86793, 3], [86791], .contexts [
        ⟨38767, false, false, [], []⟩,
        ⟨38791, false, false, [], []⟩
      ]⟩,
    ⟨[86793, 5], [86795], .contexts [
        ⟨38769, false, false, [], []⟩,
        ⟨38787, false, false, [], []⟩
      ]⟩,
    ⟨[86793, 7], [25387, 90617], .contexts [
        ⟨62129, false, false, [], []⟩,
        ⟨117447, false, false, [], []⟩
      ]⟩,
    ⟨[86793, 9], [22753, 88469], .contexts [
        ⟨50417, false, false, [], []⟩
      ]⟩,
    ⟨[86793, 11], [19463, 84389], .contexts [
        ⟨38985, false, false, [], []⟩,
        ⟨52222, false, false, [], []⟩
      ]⟩,
    ⟨[86793, 13], [34473, 46829, 90659], .contexts [
        ⟨94333, false, false, [], []⟩,
        ⟨112229, false, false, [34473], []⟩
      ]⟩,
    ⟨[86793, 15], [19493, 83901], .contexts [
        ⟨38997, false, false, [], []⟩,
        ⟨39006, false, false, [], []⟩
      ]⟩,
    ⟨[86795, 1], [86797], .contexts [
        ⟨38773, false, false, [], []⟩,
        ⟨38784, false, false, [], []⟩
      ]⟩,
    ⟨[86795, 3], [33803, 95517], .contexts [
        ⟨92176, false, false, [], []⟩,
        ⟨92210, false, false, [], []⟩
      ]⟩,
    ⟨[86795, 5], [86793], .contexts [
        ⟨38771, false, false, [], []⟩,
        ⟨38789, false, false, [], []⟩
      ]⟩,
    ⟨[86795, 7], [19479, 86795], .contexts [
        ⟨38974, false, false, [], []⟩,
        ⟨52227, false, false, [], []⟩
      ]⟩,
    ⟨[86795, 9], [19499, 42621, 85521], .contexts [
        ⟨39003, false, false, [], []⟩,
        ⟨107458, false, false, [19499], []⟩
      ]⟩,
    ⟨[86795, 11], [88709], .contexts [
        ⟨52216, false, false, [], []⟩,
        ⟨52218, false, false, [], []⟩
      ]⟩,
    ⟨[86795, 13], [21155, 85473], .contexts [
        ⟨44329, false, false, [], []⟩,
        ⟨92221, false, false, [], []⟩
      ]⟩,
    ⟨[86795, 15], [19493, 83903], .contexts [
        ⟨38979, false, false, [], []⟩,
        ⟨38975, false, false, [], []⟩
      ]⟩,
    ⟨[86797, 1], [86795], .contexts [
        ⟨38775, false, false, [], []⟩,
        ⟨38787, false, false, [], []⟩
      ]⟩,
    ⟨[86797, 3], [19475, 86797], .contexts [
        ⟨38785, true, false, [], [3]⟩,
        ⟨196, false, false, [86799], []⟩,
        ⟨197, false, false, [86799], []⟩,
        ⟨38894, false, false, [], [9]⟩,
        ⟨38898, false, false, [], [9]⟩,
        ⟨38934, false, false, [], [9]⟩,
        ⟨38935, false, false, [], [9]⟩,
        ⟨38935, false, false, [], [9]⟩,
        ⟨38779, false, false, [19475], []⟩,
        ⟨38936, false, false, [], []⟩,
        ⟨38937, false, false, [19475], []⟩,
        ⟨13, true, false, [], [19475, 86797]⟩,
        ⟨38936, false, false, [], []⟩
      ]⟩,
    ⟨[86797, 5], [19463, 84385], .contexts [
        ⟨38941, false, false, [], []⟩,
        ⟨38938, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2556. -/
def y322TCIndexRaw2556 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86797, 7], [19481, 86797], .contexts [
        ⟨38948, false, false, [], []⟩,
        ⟨38945, false, false, [], []⟩
      ]⟩,
    ⟨[86797, 9], [86799], .contexts [
        ⟨38777, false, false, [], []⟩,
        ⟨38874, false, false, [], []⟩
      ]⟩,
    ⟨[86797, 11], [88711], .contexts [
        ⟨52257, true, false, [], [11]⟩,
        ⟨53, false, false, [88711], []⟩,
        ⟨52244, false, false, [], []⟩,
        ⟨52243, false, false, [], []⟩
      ]⟩,
    ⟨[86797, 13], [19487, 84207], .contexts [
        ⟨38956, false, false, [], []⟩,
        ⟨38951, false, false, [], []⟩
      ]⟩,
    ⟨[86797, 15], [19493, 83905], .contexts [
        ⟨38963, false, false, [], []⟩,
        ⟨38959, false, false, [], []⟩
      ]⟩,
    ⟨[86799, 1], [19463, 84379], .contexts [
        ⟨38879, false, false, [], []⟩,
        ⟨38884, false, false, [], []⟩
      ]⟩,
    ⟨[86799, 3], [19475, 86799], .contexts [
        ⟨38898, false, false, [], []⟩,
        ⟨38934, false, false, [], []⟩
      ]⟩,
    ⟨[86799, 5], [19463, 84383], .contexts [
        ⟨38907, false, false, [], []⟩,
        ⟨38899, false, false, [], []⟩
      ]⟩,
    ⟨[86799, 7], [19481, 86799], .contexts [
        ⟨38913, false, false, [], []⟩,
        ⟨38943, false, false, [], []⟩
      ]⟩,
    ⟨[86799, 9], [86797], .contexts [
        ⟨38779, false, false, [], []⟩,
        ⟨38784, false, false, [], []⟩
      ]⟩,
    ⟨[86799, 11], [19467, 86799], .contexts [
        ⟨38781, false, false, [], []⟩,
        ⟨38888, false, false, [], []⟩
      ]⟩,
    ⟨[86799, 13], [19487, 84209], .contexts [
        ⟨38922, false, false, [], []⟩,
        ⟨38949, false, false, [], []⟩
      ]⟩,
    ⟨[86799, 15], [19493, 83907], .contexts [
        ⟨38933, false, false, [], []⟩,
        ⟨38957, false, false, [], []⟩
      ]⟩,
    ⟨[86805, 1], [87033], .contexts [
        ⟨39996, false, false, [], []⟩,
        ⟨39999, false, false, [], []⟩
      ]⟩,
    ⟨[86805, 3], [1423, 84365], .contexts [
        ⟨39060, false, false, [], []⟩,
        ⟨39056, false, false, [], []⟩
      ]⟩,
    ⟨[86805, 5], [42573, 86369], .contexts [
        ⟨39051, false, false, [], []⟩,
        ⟨152146, false, false, [], []⟩
      ]⟩,
    ⟨[86805, 7], [19511, 86805], .contexts [
        ⟨39078, false, false, [], []⟩,
        ⟨40010, false, false, [], []⟩
      ]⟩,
    ⟨[86805, 9], [18631, 90749], .contexts [
        ⟨62791, true, false, [18628], [9]⟩,
        ⟨46, false, false, [18628, 90749], []⟩,
        ⟨34466, true, false, [], [90749]⟩
      ]⟩,
    ⟨[86805, 11], [19515, 83785], .contexts [
        ⟨39084, false, false, [], []⟩,
        ⟨40014, false, false, [], []⟩
      ]⟩,
    ⟨[86805, 13], [19503, 85235], .contexts [
        ⟨39065, false, false, [], []⟩,
        ⟨39064, false, false, [], []⟩
      ]⟩,
    ⟨[86805, 15], [82875], .contexts [
        ⟨39068, false, false, [], []⟩,
        ⟨17773, false, false, [], []⟩
      ]⟩,
    ⟨[86807, 1], [23849, 89307], .contexts [
        ⟨55236, false, false, [], []⟩
      ]⟩,
    ⟨[86807, 3], [82789], .contexts [
        ⟨39087, false, false, [], []⟩,
        ⟨16649, false, false, [], []⟩
      ]⟩,
    ⟨[86807, 5], [19519, 85499], .contexts [
        ⟨39093, false, false, [], []⟩
      ]⟩,
    ⟨[86807, 7], [22683, 42431, 86291], .contexts [
        ⟨49985, false, false, [], []⟩,
        ⟨107295, false, false, [22683], []⟩
      ]⟩,
    ⟨[86807, 9], [15437, 84487], .contexts [
        ⟨39100, false, false, [], []⟩,
        ⟨39098, false, false, [], []⟩
      ]⟩,
    ⟨[86807, 11], [21067, 87567], .contexts [
        ⟨44109, false, false, [], []⟩
      ]⟩,
    ⟨[86807, 13], [23217, 88707], .contexts [
        ⟨52200, false, false, [], []⟩,
        ⟨155268, false, false, [], []⟩
      ]⟩,
    ⟨[86807, 15], [31901, 41345, 94085], .contexts [
        ⟨86282, true, false, [31898], [15]⟩,
        ⟨1, false, false, [31898, 94761], []⟩,
        ⟨86283, true, false, [], [94761]⟩,
        ⟨106238, false, false, [31901], []⟩
      ]⟩,
    ⟨[86809, 1], [18273, 84493], .contexts [
        ⟨39116, false, false, [], []⟩,
        ⟨39109, false, false, [], []⟩
      ]⟩,
    ⟨[86809, 3], [24061, 91259], .contexts [
        ⟨65192, false, false, [], []⟩
      ]⟩,
    ⟨[86809, 5], [23037, 87057], .contexts [
        ⟨51431, true, false, [23034], [5]⟩,
        ⟨28, false, false, [23034, 87057], []⟩,
        ⟨51432, true, false, [], [87057]⟩
      ]⟩,
    ⟨[86809, 7], [18277, 39863, 84461], .contexts [
        ⟨39123, false, false, [], []⟩,
        ⟨104960, false, false, [18277], []⟩
      ]⟩,
    ⟨[86809, 9], [85501], .contexts [
        ⟨39103, false, false, [], []⟩,
        ⟨32483, false, false, [], []⟩
      ]⟩,
    ⟨[86809, 11], [18273, 43873, 84447], .contexts [
        ⟨39134, false, false, [], []⟩,
        ⟨108674, false, false, [18273], []⟩
      ]⟩,
    ⟨[86809, 13], [39403, 87303], .contexts [
        ⟨48362, false, false, [], []⟩,
        ⟨161134, false, false, [], []⟩
      ]⟩,
    ⟨[86809, 15], [39877, 42507, 86279], .contexts [
        ⟨104965, true, false, [39872], [15]⟩,
        ⟨98878, false, false, [39872], []⟩,
        ⟨98896, false, false, [39872], []⟩,
        ⟨104966, true, false, [], [36051, 93395]⟩,
        ⟨104967, true, false, [], [93395]⟩,
        ⟨110605, false, false, [39877], []⟩
      ]⟩,
    ⟨[86817, 1], [17279, 86817], .contexts [
        ⟨39206, false, false, [], []⟩,
        ⟨39201, false, false, [], []⟩
      ]⟩,
    ⟨[86817, 3], [24299, 59679, 85169], .contexts [
        ⟨39193, false, false, [], []⟩,
        ⟨161446, false, false, [], []⟩
      ]⟩,
    ⟨[86817, 5], [86819], .contexts [
        ⟨39211, false, false, [], []⟩,
        ⟨39213, false, false, [], []⟩
      ]⟩,
    ⟨[86817, 7], [19525, 85733], .contexts [
        ⟨39208, false, false, [], []⟩,
        ⟨39207, false, false, [], []⟩
      ]⟩,
    ⟨[36483, 93909], [36483, 52579, 53057, 86641], .contexts [
        ⟨156468, false, false, [36483], []⟩
      ]⟩,
    ⟨[86817, 9], [36483, 52579, 53057, 86641], .contexts [
        ⟨100259, false, false, [], []⟩,
        ⟨163625, false, false, [], []⟩
      ]⟩,
    ⟨[92571], [57729, 57753, 88509], .contexts [
        ⟨124635, false, false, [], []⟩,
        ⟨127508, false, false, [], []⟩
      ]⟩,
    ⟨[86817, 11], [53075, 57729, 57753, 88509], .contexts [
        ⟨119185, false, false, [], []⟩,
        ⟨163627, false, false, [53075], []⟩
      ]⟩,
    ⟨[86817, 13], [52187, 90235], .contexts [
        ⟨118124, false, false, [], []⟩,
        ⟨126339, false, false, [], []⟩
      ]⟩,
    ⟨[86817, 15], [75293, 97173], .contexts [
        ⟨146598, true, false, [59684], [15]⟩,
        ⟨1, false, false, [59684, 97173], []⟩,
        ⟨146599, true, false, [], [97173]⟩
      ]⟩,
    ⟨[86819, 1], [17279, 86819], .contexts [
        ⟨39221, false, false, [], []⟩,
        ⟨39217, false, false, [], []⟩
      ]⟩,
    ⟨[86819, 3], [26621, 87077], .contexts [
        ⟨67882, false, false, [], []⟩,
        ⟨67885, false, false, [], []⟩
      ]⟩,
    ⟨[86819, 5], [86817], .contexts [
        ⟨39212, false, false, [], []⟩,
        ⟨39194, false, false, [], []⟩
      ]⟩,
    ⟨[86819, 7], [57615, 97237], .contexts [
        ⟨147748, true, false, [57616], [7]⟩,
        ⟨38, false, false, [57616, 97237], []⟩,
        ⟨124504, false, true, [], [97237]⟩
      ]⟩,
    ⟨[86819, 9], [86821], .contexts [
        ⟨39223, false, false, [], []⟩,
        ⟨39473, false, false, [], []⟩
      ]⟩,
    ⟨[86819, 11], [53043, 90317], .contexts [
        ⟨119151, false, false, [], []⟩
      ]⟩,
    ⟨[86819, 13], [58689, 93765], .contexts [
        ⟨125702, false, false, [], []⟩
      ]⟩,
    ⟨[86819, 15], [73723, 96949], .contexts [
        ⟨144063, true, false, [73720], [15]⟩,
        ⟨1, false, false, [73720, 96949], []⟩,
        ⟨144064, true, false, [], [96949]⟩
      ]⟩,
    ⟨[86821, 1], [52585, 53149, 59017, 88501], .contexts [
        ⟨118612, false, false, [], []⟩,
        ⟨119275, false, false, [52585], []⟩,
        ⟨126133, false, false, [52585], []⟩
      ]⟩,
    ⟨[86821, 3], [53045, 95269], .contexts [
        ⟨119158, false, false, [], []⟩
      ]⟩,
    ⟨[86821, 5], [36483, 52579, 53057, 86641], .contexts [
        ⟨100279, false, false, [], []⟩,
        ⟨163625, false, false, [], []⟩
      ]⟩,
    ⟨[86821, 7], [57615, 93901], .contexts [
        ⟨124503, false, false, [], []⟩,
        ⟨126137, false, false, [], []⟩
      ]⟩,
    ⟨[86821, 9], [86819], .contexts [
        ⟨39224, false, false, [], []⟩,
        ⟨39213, false, false, [], []⟩
      ]⟩,
    ⟨[86821, 11], [86823], .contexts [
        ⟨39226, false, false, [], []⟩,
        ⟨39471, false, false, [], []⟩
      ]⟩,
    ⟨[86821, 13], [53047, 57593, 86835], .contexts [
        ⟨119160, false, false, [], []⟩,
        ⟨124495, false, false, [53047], []⟩
      ]⟩,
    ⟨[86821, 15], [53049, 85039], .contexts [
        ⟨119162, false, false, [], []⟩,
        ⟨126159, false, false, [], []⟩
      ]⟩,
    ⟨[86823, 1], [62847, 84647], .contexts [
        ⟨39230, false, false, [], []⟩,
        ⟨132841, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2557. -/
def y322TCIndexRaw2557 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86823, 3], [53097, 95267], .contexts [
        ⟨119223, false, false, [], []⟩
      ]⟩,
    ⟨[86823, 5], [53105, 84269], .contexts [
        ⟨119229, false, false, [], []⟩
      ]⟩,
    ⟨[86823, 7], [53107, 55133, 59233, 85747], .contexts [
        ⟨119216, true, false, [53088], [7]⟩,
        ⟨118937, false, false, [53088], []⟩,
        ⟨119218, true, false, [], [52861, 93899]⟩,
        ⟨119230, true, false, [], [93899]⟩,
        ⟨160096, false, false, [53107], []⟩
      ]⟩,
    ⟨[86823, 9], [53093, 83695], .contexts [
        ⟨119216, true, false, [53088], [9]⟩,
        ⟨80765, false, false, [53088], []⟩,
        ⟨89231, false, false, [53088], []⟩,
        ⟨109006, false, false, [53088, 32773], []⟩,
        ⟨119217, true, false, [53088], [83695]⟩,
        ⟨119218, true, false, [], [53091, 83695]⟩,
        ⟨119219, true, false, [], [83695]⟩
      ]⟩,
    ⟨[86823, 11], [86821], .contexts [
        ⟨39228, false, false, [], []⟩,
        ⟨39473, false, false, [], []⟩
      ]⟩,
    ⟨[86823, 13], [53099, 89279], .contexts [
        ⟨119225, false, false, [], []⟩
      ]⟩,
    ⟨[86823, 15], [53101, 83449], .contexts [
        ⟨119216, true, false, [53088], [15]⟩,
        ⟨109031, false, false, [53088], []⟩,
        ⟨118073, false, false, [53088], []⟩,
        ⟨119218, true, false, [], [44229, 83449]⟩,
        ⟨119226, true, false, [], [83449]⟩
      ]⟩,
    ⟨[86833, 1], [54079, 84263], .contexts [
        ⟨120294, false, false, [], []⟩
      ]⟩,
    ⟨[86833, 3], [53143, 63781, 85777], .contexts [
        ⟨39246, false, false, [], []⟩,
        ⟨120286, false, false, [], []⟩,
        ⟨131845, false, false, [53143], []⟩
      ]⟩,
    ⟨[86833, 5], [86835], .contexts [
        ⟨39248, false, false, [], []⟩,
        ⟨39467, false, false, [], []⟩
      ]⟩,
    ⟨[86833, 7], [58923, 91581], .contexts [
        ⟨125986, true, false, [58920], [7]⟩,
        ⟨38, false, false, [58920, 91581], []⟩,
        ⟨125987, true, false, [], [91581]⟩
      ]⟩,
    ⟨[86833, 9], [59199, 90235], .contexts [
        ⟨126343, true, false, [59196], [9]⟩,
        ⟨46, false, false, [59196, 90235], []⟩,
        ⟨126344, true, false, [], [90235]⟩
      ]⟩,
    ⟨[86833, 11], [59103, 84267], .contexts [
        ⟨126233, true, false, [59100], [11]⟩,
        ⟨53, false, false, [59100, 84267], []⟩,
        ⟨126234, true, false, [], [84267]⟩
      ]⟩,
    ⟨[86833, 13], [59097, 86641], .contexts [
        ⟨126227, true, false, [59094], [13]⟩,
        ⟨59, false, false, [59094, 86641], []⟩,
        ⟨126228, true, false, [], [86641]⟩
      ]⟩,
    ⟨[86833, 15], [53989, 96345], .contexts [
        ⟨120179, true, false, [53986], [15]⟩,
        ⟨1, false, false, [53986, 96345], []⟩,
        ⟨120180, true, false, [], [96345]⟩
      ]⟩,
    ⟨[86835, 1], [86837], .contexts [
        ⟨39252, false, false, [], []⟩,
        ⟨39465, false, false, [], []⟩
      ]⟩,
    ⟨[86835, 3], [57491, 89387], .contexts [
        ⟨124384, false, false, [], []⟩
      ]⟩,
    ⟨[86835, 5], [86833], .contexts [
        ⟨39250, false, false, [], []⟩,
        ⟨39468, false, false, [], []⟩
      ]⟩,
    ⟨[86835, 7], [57603, 85189], .contexts [
        ⟨124484, true, false, [57592], [7]⟩,
        ⟨115816, true, false, [57592, 50266], [7]⟩,
        ⟨38, false, false, [57592, 50266, 92865], []⟩,
        ⟨115817, true, false, [57592], [92865]⟩,
        ⟨118832, false, false, [57592, 50269], []⟩,
        ⟨124482, true, false, [], [50269, 52753, 85189]⟩,
        ⟨124490, true, false, [], [52753, 85189]⟩,
        ⟨124491, true, false, [], [85189]⟩
      ]⟩,
    ⟨[86835, 9], [57595, 93765], .contexts [
        ⟨124487, false, false, [], []⟩
      ]⟩,
    ⟨[86835, 11], [57597, 89279], .contexts [
        ⟨124484, true, false, [57592], [11]⟩,
        ⟨80884, false, false, [57592], []⟩,
        ⟨100822, false, false, [57592], []⟩,
        ⟨100820, false, false, [57592], []⟩,
        ⟨124486, true, false, [], [36769, 89279]⟩,
        ⟨124488, true, false, [], [89279]⟩
      ]⟩,
    ⟨[86835, 13], [57607, 86821], .contexts [
        ⟨124494, false, false, [], []⟩
      ]⟩,
    ⟨[86835, 15], [57599, 92337], .contexts [
        ⟨124484, true, false, [57592], [15]⟩,
        ⟨100830, false, false, [57592], []⟩,
        ⟨124482, true, false, [], [36777, 92337]⟩,
        ⟨124489, true, false, [], [92337]⟩
      ]⟩,
    ⟨[86837, 1], [86835], .contexts [
        ⟨39254, false, false, [], []⟩,
        ⟨39467, false, false, [], []⟩
      ]⟩,
    ⟨[86837, 3], [57495, 85133], .contexts [
        ⟨124369, true, false, [57492], [3]⟩,
        ⟨118699, false, false, [57492], []⟩,
        ⟨124370, true, false, [], [52663, 85133]⟩,
        ⟨124374, true, false, [], [85133]⟩
      ]⟩,
    ⟨[86837, 5], [57497, 84263], .contexts [
        ⟨124369, true, false, [57492], [5]⟩,
        ⟨118719, true, false, [57492, 52682], [5]⟩,
        ⟨28, false, false, [57492, 52682, 84263], []⟩,
        ⟨118720, true, false, [57492], [84263]⟩,
        ⟨124370, true, false, [], [52685, 84263]⟩,
        ⟨124375, true, false, [], [84263]⟩
      ]⟩,
    ⟨[86837, 7], [57501, 85191], .contexts [
        ⟨124369, true, false, [57492], [7]⟩,
        ⟨118732, false, false, [57492], []⟩,
        ⟨124370, true, false, [], [52699, 85191]⟩,
        ⟨124377, true, false, [], [85191]⟩
      ]⟩,
    ⟨[86837, 9], [86839], .contexts [
        ⟨39256, false, false, [], []⟩,
        ⟨39464, false, false, [], []⟩
      ]⟩,
    ⟨[86837, 11], [57499, 89277], .contexts [
        ⟨124369, true, false, [57492], [11]⟩,
        ⟨118724, true, false, [57492, 52690], [11]⟩,
        ⟨53, false, false, [57492, 52690, 89277], []⟩,
        ⟨118725, true, false, [57492], [89277]⟩,
        ⟨124370, true, false, [], [52693, 89277]⟩,
        ⟨124376, true, false, [], [89277]⟩
      ]⟩,
    ⟨[86837, 13], [57503, 85807], .contexts [
        ⟨124379, false, false, [], []⟩
      ]⟩,
    ⟨[86837, 15], [57491, 89381], .contexts [
        ⟨124369, true, false, [57492], [15]⟩,
        ⟨55700, false, false, [57492], []⟩,
        ⟨55857, false, false, [57492], []⟩,
        ⟨124373, true, false, [], [89381]⟩
      ]⟩,
    ⟨[86839, 1], [57487, 84257], .contexts [
        ⟨124362, false, false, [], []⟩
      ]⟩,
    ⟨[86839, 3], [57481, 83823], .contexts [
        ⟨124352, true, false, [57478], [3]⟩,
        ⟨73089, false, false, [57478], []⟩,
        ⟨124353, false, false, [57478], []⟩,
        ⟨124355, true, false, [], [50145, 83823]⟩,
        ⟨124356, true, false, [], [83823]⟩
      ]⟩,
    ⟨[86839, 5], [57483, 84261], .contexts [
        ⟨124358, false, false, [], []⟩
      ]⟩,
    ⟨[86839, 7], [57489, 92595], .contexts [
        ⟨124352, true, false, [57478], [7]⟩,
        ⟨119589, true, false, [57478, 53416], [7]⟩,
        ⟨38, false, false, [57478, 53416, 92595], []⟩,
        ⟨119590, true, false, [57478], [92595]⟩,
        ⟨124354, true, false, [], [53419, 92595]⟩,
        ⟨124363, true, false, [], [92595]⟩
      ]⟩,
    ⟨[86839, 9], [86837], .contexts [
        ⟨39258, false, false, [], []⟩,
        ⟨39465, false, false, [], []⟩
      ]⟩,
    ⟨[86839, 11], [57473, 83087], .contexts [
        ⟨39260, false, false, [], []⟩,
        ⟨124349, false, false, [], []⟩
      ]⟩,
    ⟨[86839, 13], [57547, 85809], .contexts [
        ⟨124436, false, false, [], []⟩
      ]⟩,
    ⟨[86839, 15], [57485, 94129], .contexts [
        ⟨124352, true, false, [57478], [15]⟩,
        ⟨118357, false, false, [57478], []⟩,
        ⟨124360, true, false, [], [94129]⟩
      ]⟩,
    ⟨[86859, 1], [50023, 86675], .contexts [
        ⟨39291, false, false, [], []⟩,
        ⟨115544, false, false, [], []⟩
      ]⟩,
    ⟨[86859, 3], [63305, 85869], .contexts [
        ⟨131262, true, false, [63306], [3]⟩,
        ⟨20, false, false, [63306, 85869], []⟩,
        ⟨131260, false, true, [], [85869]⟩,
        ⟨131259, false, false, [], []⟩
      ]⟩,
    ⟨[86859, 5], [57515, 91365], .contexts [
        ⟨124395, true, false, [57512], [5]⟩,
        ⟨28, false, false, [57512, 91365], []⟩,
        ⟨124396, true, false, [], [91365]⟩
      ]⟩,
    ⟨[86859, 7], [57443, 85267], .contexts [
        ⟨124317, true, false, [57440], [7]⟩,
        ⟨38, false, false, [57440, 85267], []⟩,
        ⟨124318, true, false, [], [85267]⟩
      ]⟩,
    ⟨[86859, 9], [57511, 87369], .contexts [
        ⟨124388, true, false, [57508], [9]⟩,
        ⟨46, false, false, [57508, 87369], []⟩,
        ⟨124389, true, false, [], [87369]⟩
      ]⟩,
    ⟨[86859, 11], [57451, 86619], .contexts [
        ⟨39289, false, false, [], []⟩,
        ⟨124326, false, false, [], []⟩
      ]⟩,
    ⟨[86859, 13], [57437, 89799], .contexts [
        ⟨124313, true, false, [57434], [13]⟩,
        ⟨59, false, false, [57434, 89799], []⟩,
        ⟨124314, true, false, [], [89799]⟩
      ]⟩,
    ⟨[86859, 15], [57421, 85875], .contexts [
        ⟨124299, false, false, [], []⟩,
        ⟨131256, false, false, [], []⟩
      ]⟩,
    ⟨[86865, 1], [49999, 85875], .contexts [
        ⟨39301, false, false, [], []⟩,
        ⟨115523, false, false, [], []⟩
      ]⟩,
    ⟨[86865, 3], [50011, 86865], .contexts [
        ⟨115527, true, false, [50006], [3]⟩,
        ⟨48452, true, false, [50006], [3]⟩,
        ⟨215, false, false, [50006, 88103], []⟩,
        ⟨216, false, false, [50006, 88103], []⟩,
        ⟨48444, false, false, [50006], [11]⟩,
        ⟨48446, false, false, [50006], [11]⟩,
        ⟨48442, false, false, [50006], [11]⟩,
        ⟨48443, false, false, [50006], [11]⟩,
        ⟨48443, false, false, [50006], [11]⟩,
        ⟨48448, false, false, [50006, 22281], []⟩,
        ⟨48445, true, false, [50006], [88105]⟩,
        ⟨115531, false, false, [50006, 22281], []⟩,
        ⟨115528, true, false, [], [22281, 50007, 86865]⟩,
        ⟨115532, true, false, [], [50007, 86865]⟩,
        ⟨115533, true, false, [], [86865]⟩
      ]⟩,
    ⟨[86865, 5], [50015, 85879], .contexts [
        ⟨115527, true, false, [50006], [5]⟩,
        ⟨104797, true, false, [50006, 39702], [5]⟩,
        ⟨48780, false, false, [50006, 39702], []⟩,
        ⟨69286, false, false, [50006, 39702, 22355], []⟩,
        ⟨104798, true, false, [50006], [22355, 27079, 85879]⟩,
        ⟨104799, true, false, [50006], [27079, 85879]⟩,
        ⟨104800, true, false, [50006], [85879]⟩,
        ⟨115528, true, false, [], [39707, 85879]⟩,
        ⟨115535, true, false, [], [85879]⟩
      ]⟩,
    ⟨[86865, 7], [50017, 83319], .contexts [
        ⟨115527, true, false, [50006], [7]⟩,
        ⟨104797, true, false, [50006, 39702], [7]⟩,
        ⟨48785, false, false, [50006, 39702], []⟩,
        ⟨48801, false, false, [50006, 39702], []⟩,
        ⟨104802, true, false, [50006], [83319]⟩,
        ⟨115528, true, false, [], [39709, 83319]⟩,
        ⟨115536, true, false, [], [83319]⟩
      ]⟩,
    ⟨[86865, 9], [50013, 84513], .contexts [
        ⟨115527, true, false, [50006], [9]⟩,
        ⟨48456, false, false, [50006], []⟩,
        ⟨48454, false, false, [50006], []⟩,
        ⟨115528, true, false, [], [18273, 84513]⟩,
        ⟨115534, true, false, [], [84513]⟩
      ]⟩,
    ⟨[86865, 11], [50005, 88103], .contexts [
        ⟨115527, true, false, [50006], [11]⟩,
        ⟨48449, false, false, [50006], []⟩,
        ⟨48439, false, false, [50006], []⟩,
        ⟨115529, true, false, [], [88103]⟩,
        ⟨115529, true, false, [], [88103]⟩,
        ⟨115528, true, false, [], [88103]⟩
      ]⟩,
    ⟨[86865, 13], [50019, 91941], .contexts [
        ⟨115527, true, false, [50006], [13]⟩,
        ⟨104797, true, false, [50006, 39702], [13]⟩,
        ⟨68711, true, false, [50006, 39702, 26924], [13]⟩,
        ⟨59, false, false, [50006, 39702, 26924, 91941], []⟩,
        ⟨68712, true, false, [50006, 39702], [91941]⟩,
        ⟨104798, true, false, [50006], [26927, 91941]⟩,
        ⟨104806, true, false, [50006], [91941]⟩,
        ⟨115528, true, false, [], [39713, 91941]⟩,
        ⟨115537, true, false, [], [91941]⟩
      ]⟩,
    ⟨[86865, 15], [50021, 86675], .contexts [
        ⟨39299, false, false, [], []⟩,
        ⟨115539, false, false, [], []⟩
      ]⟩,
    ⟨[86875, 1], [49977, 94047], .contexts [
        ⟨115499, true, false, [49974], [1]⟩,
        ⟨92012, false, false, [49974], []⟩,
        ⟨115358, false, false, [49974], []⟩,
        ⟨115502, true, false, [], [33839, 94047]⟩,
        ⟨115503, true, false, [], [94047]⟩
      ]⟩,
    ⟨[86875, 3], [49979, 85473], .contexts [
        ⟨115505, false, false, [], []⟩
      ]⟩,
    ⟨[86875, 5], [49987, 87359], .contexts [
        ⟨115499, true, false, [49974], [5]⟩,
        ⟨92248, true, false, [49974, 33826], [5]⟩,
        ⟨28, false, false, [49974, 33826, 88633], []⟩,
        ⟨92249, true, false, [49974], [88633]⟩,
        ⟨110521, false, false, [49974, 33825], []⟩,
        ⟨115500, true, false, [], [33825, 45397, 87359]⟩,
        ⟨115511, true, false, [], [45397, 87359]⟩,
        ⟨115512, true, false, [], [87359]⟩
      ]⟩,
    ⟨[86875, 7], [49983, 86875], .contexts [
        ⟨115499, true, false, [49974], [7]⟩,
        ⟨92016, true, false, [49974], [7]⟩,
        ⟨92227, true, false, [49974, 33786], [13, 7]⟩,
        ⟨518, false, false, [49974, 33786, 95517], []⟩,
        ⟨92228, false, false, [49974, 33786], []⟩,
        ⟨92198, false, false, [49974, 33786], []⟩,
        ⟨92229, false, false, [49974, 33786], []⟩,
        ⟨92230, true, false, [49974], [95515]⟩,
        ⟨92230, true, false, [49974], [95515]⟩,
        ⟨92155, false, true, [49974], [95515]⟩,
        ⟨115508, false, false, [49974, 33785], []⟩,
        ⟨115500, true, false, [], [33785, 49975, 86875]⟩,
        ⟨115509, true, false, [], [49975, 86875]⟩,
        ⟨115510, true, false, [], [86875]⟩
      ]⟩,
    ⟨[86875, 9], [49989, 83777], .contexts [
        ⟨39315, false, false, [], []⟩,
        ⟨115514, false, false, [], []⟩
      ]⟩,
    ⟨[86875, 11], [86877], .contexts [
        ⟨39317, false, false, [], []⟩,
        ⟨39442, false, false, [], []⟩
      ]⟩,
    ⟨[86875, 13], [49973, 95517], .contexts [
        ⟨115499, true, false, [49974], [13]⟩,
        ⟨92014, false, false, [49974], []⟩,
        ⟨92026, false, false, [49974], []⟩,
        ⟨115501, true, false, [], [95517]⟩,
        ⟨115502, true, false, [], [95517]⟩
      ]⟩,
    ⟨[86875, 15], [72377, 96849], .contexts [
        ⟨142066, true, false, [72374], [15]⟩,
        ⟨1, false, false, [72374, 96849], []⟩,
        ⟨142067, true, false, [], [96849]⟩
      ]⟩,
    ⟨[86877, 1], [86879], .contexts [
        ⟨39321, false, false, [], []⟩,
        ⟨39440, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2558. -/
def y322TCIndexRaw2558 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86877, 3], [49971, 93203], .contexts [
        ⟨115489, true, false, [49962], [3]⟩,
        ⟨115382, true, false, [49962, 49878], [3]⟩,
        ⟨20, false, false, [49962, 49878, 93203], []⟩,
        ⟨115383, true, false, [49962], [93203]⟩,
        ⟨115490, true, false, [], [49881, 93203]⟩,
        ⟨115493, true, false, [], [93203]⟩
      ]⟩,
    ⟨[86877, 5], [49969, 84743], .contexts [
        ⟨115489, true, false, [49962], [5]⟩,
        ⟨115345, false, false, [49962], []⟩,
        ⟨115490, true, false, [], [49853, 84743]⟩,
        ⟨115492, true, false, [], [84743]⟩
      ]⟩,
    ⟨[86877, 7], [56615, 86877], .contexts [
        ⟨123326, false, false, [56610], [86877, 7]⟩,
        ⟨123325, false, false, [56610, 48865], [86877, 7]⟩,
        ⟨115495, true, false, [56610, 48865, 48897], [7]⟩,
        ⟨114249, true, false, [56610, 48865], [7]⟩,
        ⟨123319, true, false, [56610], [15, 7]⟩,
        ⟨18155, false, false, [56610, 86885], []⟩,
        ⟨10, false, false, [56610, 86885], []⟩,
        ⟨114249, false, false, [56610], []⟩,
        ⟨115495, false, false, [56610, 48897], []⟩,
        ⟨123325, true, false, [56610], [86877]⟩,
        ⟨123327, false, false, [56610, 56609], []⟩,
        ⟨123328, true, false, [], [56609, 86877]⟩,
        ⟨123329, true, false, [], [86877]⟩
      ]⟩,
    ⟨[86877, 9], [54963, 86393], .contexts [
        ⟨121358, false, false, [], []⟩,
        ⟨124171, false, false, [], []⟩
      ]⟩,
    ⟨[86877, 11], [86875], .contexts [
        ⟨39319, false, false, [], []⟩,
        ⟨39443, false, false, [], []⟩
      ]⟩,
    ⟨[86877, 13], [49973, 96789], .contexts [
        ⟨140967, true, false, [49974], [13]⟩,
        ⟨59, false, false, [49974, 96789], []⟩,
        ⟨115500, true, false, [], [96789]⟩
      ]⟩,
    ⟨[86877, 15], [49965, 86885], .contexts [
        ⟨115489, true, false, [49962], [15]⟩,
        ⟨70715, false, false, [49962], []⟩,
        ⟨114247, false, false, [49962], []⟩,
        ⟨115490, true, false, [], [48895, 86885]⟩,
        ⟨115491, true, false, [], [86885]⟩
      ]⟩,
    ⟨[86879, 1], [86877], .contexts [
        ⟨39323, false, false, [], []⟩,
        ⟨39442, false, false, [], []⟩
      ]⟩,
    ⟨[86879, 3], [49949, 92147], .contexts [
        ⟨115474, false, false, [], []⟩,
        ⟨124199, false, false, [], []⟩
      ]⟩,
    ⟨[86879, 5], [49959, 84745], .contexts [
        ⟨115486, false, false, [], []⟩,
        ⟨124210, false, false, [], []⟩
      ]⟩,
    ⟨[86879, 7], [49957, 86879], .contexts [
        ⟨115484, false, false, [], []⟩,
        ⟨124218, false, false, [], []⟩
      ]⟩,
    ⟨[86879, 9], [49951, 57325, 91975], .contexts [
        ⟨115476, false, false, [], []⟩,
        ⟨124184, false, false, [49951], []⟩
      ]⟩,
    ⟨[86879, 11], [49953, 94047], .contexts [
        ⟨115478, false, false, [], []⟩
      ]⟩,
    ⟨[86881], [49947, 86879], .contexts [
        ⟨115479, false, false, [], []⟩
      ]⟩,
    ⟨[86879, 13], [49947, 86879], .contexts [
        ⟨39325, false, false, [], []⟩,
        ⟨163725, false, false, [], []⟩
      ]⟩,
    ⟨[86879, 15], [49945, 86883], .contexts [
        ⟨115472, false, false, [], []⟩,
        ⟨124202, false, false, [], []⟩
      ]⟩,
    ⟨[86883, 1], [86885], .contexts [
        ⟨39333, false, false, [], []⟩,
        ⟨39434, false, false, [], []⟩
      ]⟩,
    ⟨[86883, 3], [57349, 94035], .contexts [
        ⟨124208, false, false, [], []⟩,
        ⟨141998, false, false, [], []⟩
      ]⟩,
    ⟨[86883, 5], [49911, 86239], .contexts [
        ⟨115416, false, false, [], []⟩,
        ⟨124255, false, false, [], []⟩
      ]⟩,
    ⟨[86883, 7], [48865, 86883], .contexts [
        ⟨123324, false, false, [], []⟩,
        ⟨123320, false, false, [], []⟩
      ]⟩,
    ⟨[86883, 9], [70273, 90903], .contexts [
        ⟨138963, false, false, [], []⟩,
        ⟨142012, false, false, [], []⟩
      ]⟩,
    ⟨[86883, 11], [96847], .contexts [
        ⟨141993, false, false, [], []⟩,
        ⟨141995, false, false, [], []⟩
      ]⟩,
    ⟨[86883, 13], [71275, 92371], .contexts [
        ⟨140097, false, false, [], []⟩,
        ⟨142021, false, false, [], []⟩
      ]⟩,
    ⟨[86883, 15], [49947, 86879], .contexts [
        ⟨39331, false, false, [], []⟩,
        ⟨163725, false, false, [], []⟩
      ]⟩,
    ⟨[86885, 1], [86883], .contexts [
        ⟨39335, false, false, [], []⟩,
        ⟨39436, false, false, [], []⟩
      ]⟩,
    ⟨[86885, 3], [86887], .contexts [
        ⟨39337, false, false, [], []⟩,
        ⟨39433, false, false, [], []⟩
      ]⟩,
    ⟨[86885, 5], [48859, 48915, 84741], .contexts [
        ⟨114216, false, false, [], []⟩,
        ⟨114268, false, false, [48859], []⟩
      ]⟩,
    ⟨[86885, 7], [48865, 86885], .contexts [
        ⟨114215, false, false, [], []⟩,
        ⟨123317, false, false, [], []⟩
      ]⟩,
    ⟨[86885, 9], [48957, 86391], .contexts [
        ⟨114314, false, false, [], []⟩,
        ⟨147270, false, false, [], []⟩
      ]⟩,
    ⟨[86885, 11], [96849], .contexts [
        ⟨142048, true, false, [], [11]⟩,
        ⟨53, false, false, [96849], []⟩,
        ⟨142035, false, false, [], []⟩,
        ⟨142034, false, false, [], []⟩
      ]⟩,
    ⟨[86885, 13], [48851, 88619], .contexts [
        ⟨114229, false, false, [], []⟩
      ]⟩,
    ⟨[86885, 15], [48897, 49963, 86877], .contexts [
        ⟨114249, false, false, [], []⟩,
        ⟨115494, false, false, [48897], []⟩
      ]⟩,
    ⟨[86887, 1], [48859, 89217], .contexts [
        ⟨114202, false, false, [], []⟩
      ]⟩,
    ⟨[86887, 3], [86885], .contexts [
        ⟨39339, false, false, [], []⟩,
        ⟨39434, false, false, [], []⟩
      ]⟩,
    ⟨[86887, 5], [43305, 84393], .contexts [
        ⟨39341, false, false, [], []⟩,
        ⟨108103, false, false, [], []⟩
      ]⟩,
    ⟨[86887, 7], [48865, 86887], .contexts [
        ⟨114197, true, false, [48860], [7]⟩,
        ⟨54970, false, false, [48860], []⟩,
        ⟨114205, false, false, [48860, 19479], []⟩,
        ⟨114208, true, false, [], [86887]⟩
      ]⟩,
    ⟨[86887, 9], [48883, 50165, 83831], .contexts [
        ⟨114234, true, false, [48880], [9]⟩,
        ⟨46, false, false, [48880, 91373], []⟩,
        ⟨114235, true, false, [], [91373]⟩,
        ⟨115694, false, false, [48883], []⟩
      ]⟩,
    ⟨[86887, 11], [96927], .contexts [
        ⟨143671, false, false, [], []⟩,
        ⟨143652, false, false, [], []⟩
      ]⟩,
    ⟨[86887, 13], [48851, 88617], .contexts [
        ⟨114184, false, false, [], []⟩,
        ⟨144257, false, false, [], []⟩
      ]⟩,
    ⟨[86887, 15], [48867, 93203], .contexts [
        ⟨114197, true, false, [48860], [15]⟩,
        ⟨111612, false, false, [48860], []⟩,
        ⟨111609, false, false, [48860], []⟩,
        ⟨114198, true, false, [], [39239, 93203]⟩,
        ⟨114209, true, false, [], [93203]⟩
      ]⟩,
    ⟨[86893, 1], [73775, 96957], .contexts [
        ⟨144176, true, false, [73772], [1]⟩,
        ⟨8, false, false, [73772, 96957], []⟩,
        ⟨144177, true, false, [], [96957]⟩
      ]⟩,
    ⟨[86893, 3], [35193, 43315, 87083], .contexts [
        ⟨96301, false, false, [], []⟩,
        ⟨108101, false, false, [35193], []⟩
      ]⟩,
    ⟨[86893, 5], [43307, 87087], .contexts [
        ⟨108089, true, false, [43308], [5]⟩,
        ⟨40152, false, false, [43308], []⟩,
        ⟨40247, false, false, [43308], []⟩,
        ⟨108091, true, false, [], [87087]⟩,
        ⟨108091, true, false, [], [87087]⟩,
        ⟨108090, true, false, [], [87087]⟩
      ]⟩,
    ⟨[86893, 7], [73037, 96893], .contexts [
        ⟨143013, false, false, [], []⟩
      ]⟩,
    ⟨[86893, 9], [43305, 84395], .contexts [
        ⟨39350, false, false, [], []⟩,
        ⟨108085, false, false, [], []⟩
      ]⟩,
    ⟨[86893, 11], [86895], .contexts [
        ⟨39352, false, false, [], []⟩,
        ⟨39426, false, false, [], []⟩
      ]⟩,
    ⟨[86893, 13], [35197, 86893], .contexts [
        ⟨96307, false, false, [], []⟩,
        ⟨96305, false, false, [], []⟩
      ]⟩,
    ⟨[86893, 15], [43311, 88573], .contexts [
        ⟨108093, false, false, [], []⟩
      ]⟩,
    ⟨[86895, 1], [86897], .contexts [
        ⟨39356, false, false, [], []⟩,
        ⟨39425, false, false, [], []⟩
      ]⟩,
    ⟨[86895, 3], [35193, 91345], .contexts [
        ⟨96276, false, false, [], []⟩,
        ⟨96296, false, false, [], []⟩
      ]⟩,
    ⟨[86895, 5], [35181, 43259, 50393, 83839], .contexts [
        ⟨96273, false, false, [], []⟩,
        ⟨108042, false, false, [35181], []⟩,
        ⟨124539, false, false, [35181], []⟩
      ]⟩,
    ⟨[86895, 7], [35199, 95125], .contexts [
        ⟨96271, true, false, [35182], [7]⟩,
        ⟨88121, true, false, [35182, 32412], [7]⟩,
        ⟨38, false, false, [35182, 32412, 95125], []⟩,
        ⟨88119, false, true, [35182], [95125]⟩,
        ⟨96261, true, false, [], [32411, 95125]⟩,
        ⟨96282, true, false, [], [95125]⟩
      ]⟩,
    ⟨[86895, 9], [35191, 43243, 83239], .contexts [
        ⟨96271, true, false, [35182], [9]⟩,
        ⟨86804, false, false, [35182], []⟩,
        ⟨86812, false, false, [35182], []⟩,
        ⟨96261, true, false, [], [32011, 91821]⟩,
        ⟨96274, true, false, [], [91821]⟩,
        ⟨108016, false, false, [35191], []⟩
      ]⟩,
    ⟨[86895, 11], [86893], .contexts [
        ⟨39354, false, false, [], []⟩,
        ⟨39428, false, false, [], []⟩
      ]⟩,
    ⟨[86895, 13], [35197, 86895], .contexts [
        ⟨96281, false, false, [], []⟩,
        ⟨96303, false, false, [], []⟩
      ]⟩,
    ⟨[86895, 15], [44653, 83613], .contexts [
        ⟨109583, true, false, [44650], [15]⟩,
        ⟨1, false, false, [44650, 83613], []⟩,
        ⟨109584, true, false, [], [83613]⟩
      ]⟩,
    ⟨[86897, 1], [86895], .contexts [
        ⟨39358, false, false, [], []⟩,
        ⟨39426, false, false, [], []⟩
      ]⟩,
    ⟨[86897, 3], [35187, 38643, 50627, 90325], .contexts [
        ⟨96265, false, false, [], []⟩,
        ⟨156240, false, false, [35187], []⟩
      ]⟩,
    ⟨[86897, 5], [50619, 83837], .contexts [
        ⟨116272, true, false, [50614], [5]⟩,
        ⟨59946, false, false, [50614], []⟩,
        ⟨115965, false, false, [50614], []⟩,
        ⟨116271, true, false, [], [50393, 83837]⟩,
        ⟨116273, true, false, [], [83837]⟩
      ]⟩,
    ⟨[86897, 7], [35189, 95129], .contexts [
        ⟨96260, true, false, [35182], [7]⟩,
        ⟨88077, false, false, [35182], []⟩,
        ⟨88116, false, false, [35182], []⟩,
        ⟨96261, true, false, [], [32389, 95129]⟩,
        ⟨96266, true, false, [], [95129]⟩
      ]⟩,
    ⟨[86897, 9], [35185, 38479, 83809], .contexts [
        ⟨96263, false, false, [], []⟩,
        ⟨103452, false, false, [35185], []⟩
      ]⟩,
    ⟨[86897, 11], [73797, 96957], .contexts [
        ⟨144196, true, false, [73794], [11]⟩,
        ⟨53, false, false, [73794, 96957], []⟩,
        ⟨144197, true, false, [], [96957]⟩
      ]⟩,
    ⟨[86897, 13], [86899], .contexts [
        ⟨39360, false, false, [], []⟩,
        ⟨39424, false, false, [], []⟩
      ]⟩,
    ⟨[86897, 15], [50621, 83611], .contexts [
        ⟨116275, false, false, [], []⟩
      ]⟩]

/-- Exact literal claimed equations and contextual derivations, block 2559. -/
def y322TCIndexRaw2559 : Fin 64 → Y322RawContextCertificate :=
  ![
    ⟨[86899, 1], [19923, 35173, 86899], .contexts [
        ⟨40558, false, false, [], []⟩,
        ⟨96252, false, false, [19923], []⟩
      ]⟩,
    ⟨[86899, 3], [35175, 86905], .contexts [
        ⟨96249, true, false, [35172], [3]⟩,
        ⟨39371, false, false, [35172], []⟩,
        ⟨39418, false, false, [35172], []⟩,
        ⟨96251, true, false, [], [86905]⟩,
        ⟨96251, true, false, [], [86905]⟩,
        ⟨96250, true, false, [], [86905]⟩
      ]⟩,
    ⟨[86899, 5], [73091, 96899], .contexts [
        ⟨143114, true, false, [73088], [5]⟩,
        ⟨28, false, false, [73088, 96899], []⟩,
        ⟨143115, true, false, [], [96899]⟩
      ]⟩,
    ⟨[86899, 7], [35179, 87809], .contexts [
        ⟨96249, true, false, [35172], [7]⟩,
        ⟨96224, true, false, [35172, 35152], [7]⟩,
        ⟨38, false, false, [35172, 35152, 87809], []⟩,
        ⟨96222, false, true, [35172], [87809]⟩,
        ⟨96250, true, false, [], [35151, 87809]⟩,
        ⟨96256, true, false, [], [87809]⟩
      ]⟩,
    ⟨[86899, 9], [35177, 85715], .contexts [
        ⟨96249, true, false, [35172], [9]⟩,
        ⟨96216, false, false, [35172], []⟩,
        ⟨96240, false, false, [35172], []⟩,
        ⟨96250, true, false, [], [35147, 85715]⟩,
        ⟨96255, true, false, [], [85715]⟩
      ]⟩,
    ⟨[86899, 11], [68539, 87909], .contexts [
        ⟨137115, true, false, [68536], [11]⟩,
        ⟨53, false, false, [68536, 87909], []⟩,
        ⟨137116, true, false, [], [87909]⟩
      ]⟩,
    ⟨[86899, 13], [86897], .contexts [
        ⟨39362, false, false, [], []⟩,
        ⟨39425, false, false, [], []⟩
      ]⟩,
    ⟨[86899, 15], [19903, 86899], .contexts [
        ⟨39364, false, false, [], []⟩,
        ⟨96247, false, false, [], []⟩
      ]⟩,
    ⟨[86905, 1], [44799, 94967], .contexts [
        ⟨109769, false, false, [], []⟩,
        ⟨137107, false, false, [], []⟩
      ]⟩,
    ⟨[86905, 3], [35173, 86899], .contexts [
        ⟨39373, false, false, [], []⟩,
        ⟨96252, false, false, [], []⟩
      ]⟩,
    ⟨[86905, 5], [86907], .contexts [
        ⟨39375, false, false, [], []⟩,
        ⟨39416, false, false, [], []⟩
      ]⟩,
    ⟨[86905, 7], [35113, 88473], .contexts [
        ⟨96169, false, false, [], []⟩,
        ⟨96219, false, false, [], []⟩
      ]⟩,
    ⟨[86905, 9], [35109, 37487, 96075], .contexts [
        ⟨96162, true, false, [35106], [9]⟩,
        ⟨46, false, false, [35106, 96165], []⟩,
        ⟨96163, true, false, [], [96165]⟩,
        ⟨102270, false, false, [35109], []⟩
      ]⟩,
    ⟨[86905, 11], [60055, 87907], .contexts [
        ⟨131474, false, false, [], []⟩,
        ⟨127331, false, false, [], []⟩
      ]⟩,
    ⟨[86905, 13], [35119, 38643, 50627, 90325], .contexts [
        ⟨96176, false, false, [], []⟩,
        ⟨156240, false, false, [35119], []⟩
      ]⟩,
    ⟨[86905, 15], [19923, 86905], .contexts [
        ⟨40531, false, false, [], []⟩,
        ⟨40538, false, false, [], []⟩
      ]⟩,
    ⟨[86907, 1], [86909], .contexts [
        ⟨39379, false, false, [], []⟩,
        ⟨39414, false, false, [], []⟩
      ]⟩,
    ⟨[86907, 3], [44799, 51623, 87541], .contexts [
        ⟨109777, false, false, [], []⟩,
        ⟨117430, false, false, [44799], []⟩
      ]⟩,
    ⟨[86907, 5], [86905], .contexts [
        ⟨39377, false, false, [], []⟩,
        ⟨39418, false, false, [], []⟩
      ]⟩,
    ⟨[86907, 7], [35449, 96363], .contexts [
        ⟨97350, false, false, [], []⟩
      ]⟩,
    ⟨[86907, 9], [29849, 93277], .contexts [
        ⟨78276, true, false, [29846], [9]⟩,
        ⟨46, false, false, [29846, 93277], []⟩,
        ⟨78277, true, false, [], [93277]⟩
      ]⟩,
    ⟨[86907, 11], [90229], .contexts [
        ⟨59760, false, false, [], []⟩,
        ⟨59755, false, false, [], []⟩
      ]⟩,
    ⟨[86907, 13], [44867, 57693, 88517], .contexts [
        ⟨109855, false, false, [], []⟩,
        ⟨124600, false, false, [44867], []⟩
      ]⟩,
    ⟨[86907, 15], [19903, 86907], .contexts [
        ⟨40513, false, false, [], []⟩,
        ⟨40526, false, false, [], []⟩
      ]⟩,
    ⟨[86909, 1], [86907], .contexts [
        ⟨39381, false, false, [], []⟩,
        ⟨39416, false, false, [], []⟩
      ]⟩,
    ⟨[86909, 3], [72023, 96813], .contexts [
        ⟨141384, true, false, [51626], [3]⟩,
        ⟨20, false, false, [51626, 96813], []⟩,
        ⟨141385, true, false, [], [96813]⟩
      ]⟩,
    ⟨[86909, 5], [44773, 94967], .contexts [
        ⟨109746, false, false, [], []⟩
      ]⟩,
    ⟨[86909, 7], [26445, 91625], .contexts [
        ⟨66927, false, false, [], []⟩
      ]⟩,
    ⟨[86909, 9], [86911], .contexts [
        ⟨39383, false, false, [], []⟩,
        ⟨39411, false, false, [], []⟩
      ]⟩,
    ⟨[86909, 11], [90227], .contexts [
        ⟨59733, false, false, [], []⟩,
        ⟨59735, false, false, [], []⟩
      ]⟩,
    ⟨[86909, 13], [19897, 86211], .contexts [
        ⟨40479, false, false, [], []⟩
      ]⟩,
    ⟨[86909, 15], [19923, 86909], .contexts [
        ⟨40490, false, false, [], []⟩,
        ⟨40504, false, false, [], []⟩
      ]⟩,
    ⟨[86911, 1], [24791, 90225], .contexts [
        ⟨59730, false, false, [], []⟩,
        ⟨60075, false, false, [], []⟩
      ]⟩,
    ⟨[86911, 3], [38313, 96723], .contexts [
        ⟨103300, false, false, [], []⟩
      ]⟩,
    ⟨[86911, 5], [29195, 92959], .contexts [
        ⟨76107, false, false, [], []⟩,
        ⟨109742, false, false, [], []⟩
      ]⟩,
    ⟨[91623], [39963, 47097, 86533], .contexts [
        ⟨105044, false, false, [], []⟩,
        ⟨112488, false, false, [39963], []⟩
      ]⟩,
    ⟨[86911, 7], [26445, 39963, 47097, 86533], .contexts [
        ⟨66905, true, false, [26442], [7]⟩,
        ⟨38, false, false, [26442, 91623], []⟩,
        ⟨66906, true, false, [], [91623]⟩,
        ⟨163811, false, false, [26445], []⟩
      ]⟩,
    ⟨[86911, 9], [86909], .contexts [
        ⟨39385, false, false, [], []⟩,
        ⟨39414, false, false, [], []⟩
      ]⟩,
    ⟨[86911, 11], [19871, 85941], .contexts [
        ⟨39387, false, false, [], []⟩,
        ⟨59739, false, false, [], []⟩
      ]⟩,
    ⟨[86911, 13], [19897, 86213], .contexts [
        ⟨40422, true, false, [19894], [13]⟩,
        ⟨59, false, false, [19894, 86213], []⟩,
        ⟨40423, true, false, [], [86213]⟩
      ]⟩,
    ⟨[86911, 15], [19903, 86911], .contexts [
        ⟨40429, false, false, [], []⟩,
        ⟨40482, false, false, [], []⟩
      ]⟩,
    ⟨[86923, 1], [19849, 87201], .contexts [
        ⟨40339, false, false, [], []⟩,
        ⟨40348, false, false, [], []⟩
      ]⟩,
    ⟨[86923, 3], [19857, 41383, 85389], .contexts [
        ⟨39405, false, false, [], []⟩,
        ⟨156566, false, false, [], []⟩
      ]⟩,
    ⟨[86923, 5], [19567, 85219], .contexts [
        ⟨39507, false, false, [], []⟩,
        ⟨39503, false, false, [], []⟩
      ]⟩,
    ⟨[86923, 7], [19853, 41259, 85377], .contexts [
        ⟨40347, false, false, [], []⟩,
        ⟨106192, false, false, [19853], []⟩
      ]⟩,
    ⟨[86923, 9], [19571, 83901], .contexts [
        ⟨39520, false, false, [], []⟩,
        ⟨39512, false, false, [], []⟩
      ]⟩,
    ⟨[86923, 11], [23491, 46227, 87507], .contexts [
        ⟨53656, true, false, [23488], [11]⟩,
        ⟨53, false, false, [23488, 88975], []⟩,
        ⟨53657, true, false, [], [88975]⟩,
        ⟨111533, false, false, [23491], []⟩
      ]⟩,
    ⟨[86923, 13], [20491, 87111], .contexts [
        ⟨42081, false, false, [], []⟩,
        ⟨42308, false, false, [], []⟩
      ]⟩,
    ⟨[86923, 15], [22725, 88469], .contexts [
        ⟨50381, true, false, [22722], [15]⟩,
        ⟨1, false, false, [22722, 88469], []⟩,
        ⟨50382, true, false, [], [88469]⟩
      ]⟩,
    ⟨[86925, 1], [40313, 90093], .contexts [
        ⟨105380, false, false, [], []⟩,
        ⟨112430, false, false, [], []⟩
      ]⟩,
    ⟨[86925, 3], [47753, 84067], .contexts [
        ⟨39529, false, false, [], []⟩,
        ⟨160637, false, false, [], []⟩
      ]⟩,
    ⟨[86925, 5], [86927], .contexts [
        ⟨39551, false, false, [], []⟩,
        ⟨39553, false, false, [], []⟩
      ]⟩,
    ⟨[86925, 7], [18131, 86925], .contexts [
        ⟨39532, true, false, [], [7]⟩,
        ⟨140, false, false, [85343], []⟩,
        ⟨141, false, false, [85343], []⟩,
        ⟨31605, false, false, [], [3]⟩,
        ⟨31607, false, false, [], [3]⟩,
        ⟨31608, true, false, [], [85343, 3]⟩,
        ⟨31603, false, false, [], [3]⟩,
        ⟨31604, false, false, [], [3]⟩,
        ⟨31604, false, false, [], [3]⟩,
        ⟨39528, false, false, [18131], []⟩,
        ⟨39533, false, false, [], []⟩,
        ⟨39534, false, false, [18131], []⟩,
        ⟨31608, true, false, [], [86925]⟩,
        ⟨39533, false, false, [], []⟩
      ]⟩,
    ⟨[86925, 9], [19575, 84859], .contexts [
        ⟨39539, false, false, [], []⟩,
        ⟨39563, false, false, [], []⟩
      ]⟩,
    ⟨[86925, 11], [1369, 86925], .contexts [
        ⟨39545, false, false, [], []⟩,
        ⟨39542, false, false, [], []⟩
      ]⟩,
    ⟨[86925, 13], [18113, 86925], .contexts [
        ⟨39549, false, false, [], []⟩,
        ⟨39546, false, false, [], []⟩
      ]⟩,
    ⟨[86925, 15], [29137, 40319, 90097], .contexts [
        ⟨75708, false, false, [], []⟩,
        ⟨105390, false, false, [29137], []⟩
      ]⟩,
    ⟨[86927, 1], [86929], .contexts [
        ⟨39575, false, false, [], []⟩,
        ⟨39577, false, false, [], []⟩
      ]⟩,
    ⟨[86927, 3], [19579, 85347], .contexts [
        ⟨39560, false, false, [], []⟩,
        ⟨39580, false, false, [], []⟩
      ]⟩,
    ⟨[86927, 5], [86925], .contexts [
        ⟨39552, false, false, [], []⟩,
        ⟨39530, false, false, [], []⟩
      ]⟩,
    ⟨[86927, 7], [19575, 93053], .contexts [
        ⟨76810, true, false, [19576], [7]⟩,
        ⟨38, false, false, [19576, 93053], []⟩,
        ⟨39540, false, true, [], [93053]⟩
      ]⟩,
    ⟨[86927, 9], [19575, 84857], .contexts [
        ⟨39566, false, false, [], []⟩,
        ⟨39565, false, false, [], []⟩
      ]⟩,
    ⟨[86927, 11], [1369, 86927], .contexts [
        ⟨39572, false, false, [], []⟩,
        ⟨39568, false, false, [], []⟩
      ]⟩,
    ⟨[86927, 13], [18113, 86927], .contexts [
        ⟨39555, true, false, [], [13]⟩,
        ⟨179, false, false, [86925], []⟩,
        ⟨180, false, false, [86925], []⟩,
        ⟨39548, false, false, [], [5]⟩,
        ⟨39549, false, false, [], [5]⟩,
        ⟨39546, false, false, [], [5]⟩,
        ⟨39547, false, false, [], [5]⟩,
        ⟨39547, false, false, [], [5]⟩,
        ⟨39551, false, false, [18113], []⟩,
        ⟨39573, false, false, [], []⟩,
        ⟨39571, false, false, [18113], []⟩,
        ⟨31478, true, false, [], [86927]⟩,
        ⟨39573, false, false, [], []⟩
      ]⟩]

/-- Literal contextual derivation data in chronological chunk 39. -/
def y322TCIndexRawChunk39 (i : Fin 4096) : Y322RawContextCertificate :=
  if i.val < 2048 then
    if i.val < 1024 then
      if i.val < 512 then
        if i.val < 256 then
          if i.val < 128 then
            if i.val < 64 then
              y322TCIndexRaw2496 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2497 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 192 then
              y322TCIndexRaw2498 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2499 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 384 then
            if i.val < 320 then
              y322TCIndexRaw2500 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2501 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 448 then
              y322TCIndexRaw2502 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2503 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 768 then
          if i.val < 640 then
            if i.val < 576 then
              y322TCIndexRaw2504 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2505 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 704 then
              y322TCIndexRaw2506 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2507 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 896 then
            if i.val < 832 then
              y322TCIndexRaw2508 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2509 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 960 then
              y322TCIndexRaw2510 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2511 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 1536 then
        if i.val < 1280 then
          if i.val < 1152 then
            if i.val < 1088 then
              y322TCIndexRaw2512 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2513 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1216 then
              y322TCIndexRaw2514 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2515 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1408 then
            if i.val < 1344 then
              y322TCIndexRaw2516 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2517 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1472 then
              y322TCIndexRaw2518 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2519 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 1792 then
          if i.val < 1664 then
            if i.val < 1600 then
              y322TCIndexRaw2520 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2521 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1728 then
              y322TCIndexRaw2522 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2523 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 1920 then
            if i.val < 1856 then
              y322TCIndexRaw2524 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2525 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 1984 then
              y322TCIndexRaw2526 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2527 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  else
    if i.val < 3072 then
      if i.val < 2560 then
        if i.val < 2304 then
          if i.val < 2176 then
            if i.val < 2112 then
              y322TCIndexRaw2528 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2529 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2240 then
              y322TCIndexRaw2530 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2531 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2432 then
            if i.val < 2368 then
              y322TCIndexRaw2532 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2533 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2496 then
              y322TCIndexRaw2534 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2535 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 2816 then
          if i.val < 2688 then
            if i.val < 2624 then
              y322TCIndexRaw2536 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2537 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 2752 then
              y322TCIndexRaw2538 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2539 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 2944 then
            if i.val < 2880 then
              y322TCIndexRaw2540 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2541 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3008 then
              y322TCIndexRaw2542 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2543 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
    else
      if i.val < 3584 then
        if i.val < 3328 then
          if i.val < 3200 then
            if i.val < 3136 then
              y322TCIndexRaw2544 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2545 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3264 then
              y322TCIndexRaw2546 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2547 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3456 then
            if i.val < 3392 then
              y322TCIndexRaw2548 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2549 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3520 then
              y322TCIndexRaw2550 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2551 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
      else
        if i.val < 3840 then
          if i.val < 3712 then
            if i.val < 3648 then
              y322TCIndexRaw2552 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2553 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 3776 then
              y322TCIndexRaw2554 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2555 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
        else
          if i.val < 3968 then
            if i.val < 3904 then
              y322TCIndexRaw2556 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2557 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
          else
            if i.val < 4032 then
              y322TCIndexRaw2558 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
            else
              y322TCIndexRaw2559 ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
