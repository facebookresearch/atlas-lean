/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal chronological equation data for the original-source C431 replay, block 19. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawContextPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- Exact raw source or earlier-equation contextual derivations, chronological block 19. -/
def y431AuxReplayData19 : Fin 128 → Y322RawContextCertificate :=
![
  ⟨[1379], [1379], .contexts []⟩
,
  ⟨[9, 3], [2, 8], .contexts [⟨58, false, false, [2], [8]⟩]⟩
,
  ⟨[2, 8], [3, 9], .contexts [⟨888, false, false, [], [8]⟩, ⟨917, false, false, [3], []⟩]⟩
,
  ⟨[9, 1379], [9, 1379], .contexts []⟩
,
  ⟨[9, 1379], [9, 1379], .contexts []⟩
,
  ⟨[1375, 11], [1381], .contexts [⟨465, true, false, [], []⟩]⟩
,
  ⟨[1381], [1381], .contexts []⟩
,
  ⟨[1381], [1381], .contexts []⟩
,
  ⟨[1375, 11], [1381], .contexts [⟨2437, false, false, [], []⟩, ⟨2438, false, false, [], []⟩,
    ⟨2439, false, false, [], []⟩, ⟨2439, false, false, [], []⟩]⟩
,
  ⟨[1381, 7], [1381, 7], .contexts []⟩
,
  ⟨[1381, 7], [1289], .contexts [⟨2441, false, false, [], []⟩, ⟨2440, true, false, [], [7]⟩,
    ⟨1117, false, false, [1375], []⟩, ⟨1118, false, false, [1375], []⟩, ⟨2412, false, false, [],
    [11]⟩, ⟨1372, false, false, [], []⟩, ⟨1373, false, false, [], []⟩, ⟨1374, false, false, [],
    []⟩, ⟨1374, false, false, [], []⟩, ⟨1380, false, false, [], []⟩, ⟨1060, true, false, [],
    [1289]⟩]⟩
,
  ⟨[1381], [1381], .contexts []⟩
,
  ⟨[315, 1381], [315, 1381], .contexts []⟩
,
  ⟨[315, 1381], [315, 1381], .contexts []⟩
,
  ⟨[1381, 17], [1381, 17], .contexts []⟩
,
  ⟨[15, 13], [12, 14, 12, 14], .contexts [⟨24, false, false, [12], [14, 12, 14]⟩]⟩
,
  ⟨[12, 14, 12, 14], [13, 15, 13, 15], .contexts [⟨951, false, false, [], [14, 12, 14]⟩, ⟨872,
    false, false, [13], [12, 14]⟩, ⟨951, false, false, [13, 15], [14]⟩, ⟨872, false, false, [13,
    15, 13], []⟩]⟩
,
  ⟨[1339, 11], [381, 1339], .contexts [⟨2025, false, false, [], []⟩, ⟨2025, false, false, [],
    []⟩, ⟨2007, true, false, [], [11]⟩, ⟨1173, false, false, [1309], []⟩, ⟨1175, false, false,
    [1309], []⟩, ⟨2022, false, false, [], [1, 11, 1]⟩, ⟨1907, false, false, [297], [11, 1]⟩,
    ⟨272, true, false, [], [1337, 11, 1]⟩, ⟨1913, false, false, [379], [1]⟩, ⟨273, true, false,
    [], [1309, 1]⟩, ⟨2003, false, false, [381], []⟩, ⟨2023, false, false, [], []⟩, ⟨2024, false,
    false, [], []⟩, ⟨2013, false, false, [381], []⟩, ⟨2026, true, false, [], [1339]⟩, ⟨2023,
    false, false, [], []⟩, ⟨2024, false, false, [], []⟩]⟩
,
  ⟨[1297, 13], [1383], .contexts [⟨466, true, false, [], []⟩]⟩
,
  ⟨[1383], [1383], .contexts []⟩
,
  ⟨[1297, 13], [1383], .contexts [⟨2450, false, false, [], []⟩, ⟨2451, false, false, [], []⟩,
    ⟨2451, false, false, [], []⟩]⟩
,
  ⟨[1383], [1383], .contexts []⟩
,
  ⟨[1365, 5], [1385], .contexts [⟨467, true, false, [], []⟩]⟩
,
  ⟨[1385], [1385], .contexts []⟩
,
  ⟨[1365, 5], [1385], .contexts [⟨2454, false, false, [], []⟩, ⟨2455, false, false, [], []⟩,
    ⟨2455, false, false, [], []⟩]⟩
,
  ⟨[1385, 15], [1385, 15], .contexts []⟩
,
  ⟨[1385, 15], [1369], .contexts [⟨2457, false, false, [], []⟩, ⟨2456, true, false, [], [15]⟩,
    ⟨1330, false, false, [1365], []⟩, ⟨1331, false, false, [1365], []⟩, ⟨2277, false, false, [],
    [5]⟩, ⟨2286, false, false, [], []⟩, ⟨2287, false, false, [], []⟩, ⟨2288, false, false, [],
    []⟩, ⟨2288, false, false, [], []⟩, ⟨2290, false, false, [], []⟩, ⟨1060, true, false, [],
    [1369]⟩]⟩
,
  ⟨[709, 1369], [709, 1369], .contexts []⟩
,
  ⟨[1385, 15, 7], [709, 1369], .contexts [⟨2457, false, false, [], [7]⟩, ⟨2458, false, false,
    [], [7]⟩, ⟨2287, false, false, [], [7]⟩, ⟨2288, false, false, [], [7]⟩, ⟨2288, false, false,
    [], [7]⟩, ⟨2300, true, false, [], [7]⟩, ⟨2339, true, false, [710], [13, 7]⟩, ⟨2339, true,
    false, [710], [13, 7]⟩, ⟨2338, true, false, [710], [13, 7]⟩, ⟨2335, true, false, [710], [13,
    7]⟩, ⟨2340, false, false, [710, 1371], [12]⟩, ⟨951, false, false, [710, 1371], []⟩, ⟨2300,
    false, false, [710], []⟩, ⟨2287, false, false, [710], []⟩, ⟨2288, false, false, [710], []⟩,
    ⟨2288, false, false, [710], []⟩, ⟨2290, false, false, [710], []⟩, ⟨2341, true, false, [],
    [1369]⟩, ⟨2341, true, false, [], [1369]⟩, ⟨454, false, true, [], [1369]⟩, ⟨2459, false,
    false, [], []⟩, ⟨2459, false, false, [], []⟩]⟩
,
  ⟨[1291, 7], [1387], .contexts [⟨468, true, false, [], []⟩]⟩
,
  ⟨[1387], [1387], .contexts []⟩
,
  ⟨[1387], [1387], .contexts []⟩
,
  ⟨[1291, 7], [1387], .contexts [⟨2461, false, false, [], []⟩, ⟨2462, false, false, [], []⟩,
    ⟨2463, false, false, [], []⟩, ⟨2463, false, false, [], []⟩]⟩
,
  ⟨[1387, 1], [1387, 1], .contexts []⟩
,
  ⟨[1387], [1387], .contexts []⟩
,
  ⟨[349, 1291], [349, 1291], .contexts []⟩
,
  ⟨[1291, 11], [349, 1291], .contexts [⟨1934, false, false, [], []⟩, ⟨1934, false, false, [],
    []⟩, ⟨1386, true, false, [], [11]⟩, ⟨1370, true, false, [], [1, 11]⟩, ⟨1933, true, false,
    [336], [11, 1, 11]⟩, ⟨1172, false, false, [336, 1287], [10, 0]⟩, ⟨1174, false, false, [336,
    1287], []⟩, ⟨1375, false, false, [336], [1]⟩, ⟨1388, false, false, [336], []⟩, ⟨1389, false,
    false, [336], []⟩, ⟨1390, false, false, [336], []⟩, ⟨1390, false, false, [336], []⟩, ⟨1396,
    false, false, [336], []⟩, ⟨1935, true, false, [], [1291]⟩, ⟨1935, true, false, [], [1291]⟩,
    ⟨256, true, false, [], [1291]⟩, ⟨2467, false, false, [], []⟩, ⟨2467, false, false, [], []⟩]⟩
,
  ⟨[349, 1387], [349, 1387], .contexts []⟩
,
  ⟨[349, 1387], [349, 1387], .contexts []⟩
,
  ⟨[1387, 11], [1387, 11], .contexts []⟩
,
  ⟨[349], [349], .contexts [⟨877, false, false, [], [349]⟩]⟩
,
  ⟨[13, 1387], [13, 1387], .contexts []⟩
,
  ⟨[13, 1387], [13, 1387], .contexts []⟩
,
  ⟨[1387, 15], [1387, 15], .contexts []⟩
,
  ⟨[1381, 5], [1389], .contexts [⟨469, true, false, [], []⟩]⟩
,
  ⟨[1381, 5], [1389], .contexts [⟨2476, false, false, [], []⟩]⟩
,
  ⟨[1389], [1389], .contexts []⟩
,
  ⟨[1389], [1389], .contexts []⟩
,
  ⟨[1381, 5], [1389], .contexts [⟨2477, false, false, [], []⟩, ⟨2478, false, false, [], []⟩,
    ⟨2479, false, false, [], []⟩, ⟨2479, false, false, [], []⟩]⟩
,
  ⟨[1389], [1389], .contexts []⟩
,
  ⟨[1381, 11], [1375], .contexts [⟨2437, true, false, [], [11]⟩, ⟨14, false, false, [1375], []⟩,
    ⟨2364, false, false, [], []⟩, ⟨2363, false, false, [], []⟩, ⟨2364, false, false, [], []⟩,
    ⟨2364, false, false, [], []⟩]⟩
,
  ⟨[1389, 17], [315, 1389], .contexts [⟨2480, true, false, [], [17]⟩, ⟨1792, false, false,
    [1381], []⟩, ⟨1793, false, false, [1381], []⟩, ⟨2446, false, false, [], [5]⟩, ⟨2446, false,
    false, [], [5]⟩, ⟨2440, true, false, [], [17, 5]⟩, ⟨1143, false, false, [1375], [5]⟩, ⟨1144,
    false, false, [1375], [5]⟩, ⟨2421, false, false, [], [11, 5]⟩, ⟨2437, false, false, [315],
    [5]⟩, ⟨2444, false, false, [], [5]⟩, ⟨2445, false, false, [], [5]⟩, ⟨2443, false, false,
    [315], [5]⟩, ⟨1845, true, false, [], [1381, 5]⟩, ⟨2444, false, false, [], [5]⟩, ⟨2445,
    false, false, [], [5]⟩, ⟨2445, false, false, [], [5]⟩, ⟨2476, false, false, [315], []⟩]⟩
,
  ⟨[1381, 9], [1391], .contexts [⟨470, true, false, [], []⟩]⟩
,
  ⟨[1391], [1391], .contexts []⟩
,
  ⟨[1391], [1391], .contexts []⟩
,
  ⟨[9, 11, 9, 11], [], .contexts [⟨43, false, false, [], []⟩]⟩
,
  ⟨[9, 11], [10, 8], .contexts [⟨2487, false, false, [], [10, 8]⟩]⟩
,
  ⟨[10, 8], [11, 9], .contexts [⟨926, false, false, [], [8]⟩, ⟨917, false, false, [11], []⟩]⟩
,
  ⟨[1379], [1379], .contexts [⟨2432, false, false, [], []⟩]⟩
,
  ⟨[1379], [1379], .contexts [⟨1060, true, false, [], [1379]⟩]⟩
,
  ⟨[1381, 13], [1393], .contexts [⟨471, true, false, [], []⟩]⟩
,
  ⟨[1381, 13], [1393], .contexts [⟨2492, false, false, [], []⟩]⟩
,
  ⟨[1393], [1393], .contexts []⟩
,
  ⟨[1393], [1393], .contexts []⟩
,
  ⟨[1381, 13], [1393], .contexts [⟨2493, false, false, [], []⟩, ⟨2494, false, false, [], []⟩,
    ⟨2495, false, false, [], []⟩, ⟨2495, false, false, [], []⟩]⟩
,
  ⟨[1393, 7], [1393, 7], .contexts []⟩
,
  ⟨[603], [603], .contexts [⟨877, false, false, [], [603]⟩]⟩
,
  ⟨[1393, 7], [603, 1349], .contexts [⟨2497, false, false, [], []⟩, ⟨2496, true, false, [],
    [7]⟩, ⟨961, false, false, [1381], []⟩, ⟨962, false, false, [1381], []⟩, ⟨2441, false, false,
    [], [13]⟩, ⟨2442, false, false, [], [13]⟩, ⟨1373, false, false, [], [13]⟩, ⟨1374, false,
    false, [], [13]⟩, ⟨1374, false, false, [], [13]⟩, ⟨2182, false, false, [], []⟩, ⟨2200,
    false, false, [], []⟩, ⟨2201, false, false, [], []⟩, ⟨2201, false, false, [], []⟩, ⟨2177,
    false, false, [603], []⟩, ⟨2498, true, false, [], [1349]⟩]⟩
,
  ⟨[1349, 7], [601, 1393], .contexts [⟨2499, true, false, [602], [7]⟩, ⟨10, false, false, [602,
    1393], []⟩, ⟨2183, true, false, [], [1393]⟩]⟩
,
  ⟨[11, 1393], [11, 1393], .contexts []⟩
,
  ⟨[11, 1393], [11, 1393], .contexts []⟩
,
  ⟨[1393], [1393], .contexts []⟩
,
  ⟨[1309, 7], [1395], .contexts [⟨472, true, false, [], []⟩]⟩
,
  ⟨[1395], [1395], .contexts []⟩
,
  ⟨[1395], [1395], .contexts []⟩
,
  ⟨[1395], [1395], .contexts []⟩
,
  ⟨[1387, 5], [1397], .contexts [⟨473, true, false, [], []⟩]⟩
,
  ⟨[1397, 5], [1387], .contexts [⟨2508, true, false, [], [5]⟩, ⟨8, false, false, [1387], []⟩,
    ⟨2463, false, false, [], []⟩]⟩
,
  ⟨[1387, 5], [1397], .contexts [⟨2508, false, false, [], []⟩]⟩
,
  ⟨[1397], [1397], .contexts []⟩
,
  ⟨[1397], [1397], .contexts []⟩
,
  ⟨[1387, 5], [1397], .contexts [⟨2510, false, false, [], []⟩, ⟨2511, false, false, [], []⟩,
    ⟨2512, false, false, [], []⟩, ⟨2512, false, false, [], []⟩]⟩
,
  ⟨[1387, 1], [1381], .contexts [⟨2465, false, false, [], []⟩, ⟨2465, false, false, [], []⟩,
    ⟨2464, true, false, [], [1]⟩, ⟨2355, false, false, [1291], []⟩, ⟨2356, false, false, [1291],
    []⟩, ⟨1387, false, false, [], [7]⟩, ⟨1373, false, false, [], [7]⟩, ⟨1374, false, false, [],
    [7]⟩, ⟨1374, false, false, [], [7]⟩, ⟨2442, true, false, [], [7]⟩, ⟨10, false, false,
    [1381], []⟩, ⟨2439, false, false, [], []⟩, ⟨2438, false, false, [], []⟩, ⟨2439, false,
    false, [], []⟩, ⟨2439, false, false, [], []⟩, ⟨2443, false, false, [], []⟩, ⟨1060, true,
    false, [], [1381]⟩, ⟨2438, false, false, [], []⟩, ⟨2439, false, false, [], []⟩, ⟨2439,
    false, false, [], []⟩]⟩
,
  ⟨[1397, 1], [1397, 1], .contexts []⟩
,
  ⟨[1389], [1389], .contexts [⟨2481, false, false, [], []⟩]⟩
,
  ⟨[1389], [1389], .contexts [⟨1060, true, false, [], [1389]⟩]⟩
,
  ⟨[1397, 1], [1389], .contexts [⟨2515, false, false, [], []⟩, ⟨2513, true, false, [], [1]⟩,
    ⟨2230, false, false, [1387], []⟩, ⟨2231, false, false, [1387], []⟩, ⟨2514, false, false, [],
    [5]⟩, ⟨2477, false, false, [], []⟩, ⟨2478, false, false, [], []⟩, ⟨2479, false, false, [],
    []⟩, ⟨2479, false, false, [], []⟩, ⟨2516, false, false, [], []⟩, ⟨2517, false, false, [],
    []⟩]⟩
,
  ⟨[1387, 7], [1291], .contexts [⟨2461, true, false, [], [7]⟩, ⟨10, false, false, [1291], []⟩,
    ⟨1390, false, false, [], []⟩, ⟨1389, false, false, [], []⟩, ⟨1390, false, false, [], []⟩,
    ⟨1390, false, false, [], []⟩]⟩
,
  ⟨[1397], [1397], .contexts []⟩
,
  ⟨[1397, 11], [349, 1397], .contexts [⟨2513, true, false, [], [11]⟩, ⟨2236, false, false,
    [1387], []⟩, ⟨2237, false, false, [1387], []⟩, ⟨2471, false, false, [], [5]⟩, ⟨2471, false,
    false, [], [5]⟩, ⟨2464, true, false, [], [11, 5]⟩, ⟨2346, false, false, [1291], [5]⟩, ⟨2347,
    false, false, [1291], [5]⟩, ⟨2468, false, false, [], [7, 5]⟩, ⟨2461, false, false, [349],
    [5]⟩, ⟨2469, false, false, [], [5]⟩, ⟨2470, false, false, [], [5]⟩, ⟨2466, false, false,
    [349], [5]⟩, ⟨2472, true, false, [], [1387, 5]⟩, ⟨2469, false, false, [], [5]⟩, ⟨2470,
    false, false, [], [5]⟩, ⟨2470, false, false, [], [5]⟩, ⟨2508, false, false, [349], []⟩]⟩
,
  ⟨[1387, 15], [13, 1387], .contexts [⟨2475, false, false, [], []⟩, ⟨2464, true, false, [],
    [15]⟩, ⟨2351, false, false, [1291], []⟩, ⟨2352, false, false, [1291], []⟩, ⟨1399, false,
    false, [], [7]⟩, ⟨1411, false, false, [], [7]⟩, ⟨1397, false, false, [], [7]⟩, ⟨1398, false,
    false, [], [7]⟩, ⟨1398, false, false, [], [7]⟩, ⟨2461, false, false, [13], []⟩, ⟨2473,
    false, false, [], []⟩, ⟨2474, false, false, [], []⟩, ⟨2466, false, false, [13], []⟩, ⟨972,
    true, false, [], [1387]⟩]⟩
,
  ⟨[13, 1397], [13, 1397], .contexts []⟩
,
  ⟨[13, 1397], [13, 1397], .contexts []⟩
,
  ⟨[1397, 15], [1397, 15], .contexts []⟩
,
  ⟨[1387, 9], [1399], .contexts [⟨474, true, false, [], []⟩]⟩
,
  ⟨[1387, 9], [1399], .contexts [⟨2526, false, false, [], []⟩]⟩
,
  ⟨[1399], [1399], .contexts []⟩
,
  ⟨[1399], [1399], .contexts []⟩
,
  ⟨[1391], [1391], .contexts []⟩
,
  ⟨[1391], [1391], .contexts [⟨1060, true, false, [], [1391]⟩]⟩
,
  ⟨[1399], [1399], .contexts []⟩
,
  ⟨[9, 1399], [9, 1399], .contexts []⟩
,
  ⟨[9, 1399], [9, 1399], .contexts []⟩
,
  ⟨[1387, 13], [1401], .contexts [⟨475, true, false, [], []⟩]⟩
,
  ⟨[1401], [1401], .contexts []⟩
,
  ⟨[1401], [1401], .contexts []⟩
,
  ⟨[1387, 13], [1401], .contexts [⟨2535, false, false, [], []⟩, ⟨2536, false, false, [], []⟩,
    ⟨2537, false, false, [], []⟩, ⟨2537, false, false, [], []⟩]⟩
,
  ⟨[1401, 1], [1401, 1], .contexts []⟩
,
  ⟨[1401, 1], [1393], .contexts [⟨2539, false, false, [], []⟩, ⟨2538, true, false, [], [1]⟩,
    ⟨950, false, false, [1387], []⟩, ⟨952, false, false, [1387], []⟩, ⟨2514, false, false, [],
    [13]⟩, ⟨2493, false, false, [], []⟩, ⟨2494, false, false, [], []⟩, ⟨2495, false, false, [],
    []⟩, ⟨2495, false, false, [], []⟩, ⟨2503, false, false, [], []⟩, ⟨1060, true, false, [],
    [1393]⟩]⟩
,
  ⟨[1401, 7], [1401, 7], .contexts []⟩
,
  ⟨[1387, 17], [1403], .contexts [⟨476, true, false, [], []⟩]⟩
,
  ⟨[1403], [1403], .contexts []⟩
,
  ⟨[325, 1383], [325, 1383], .contexts []⟩
,
  ⟨[1403, 7], [325, 1383], .contexts [⟨2543, true, false, [], [7]⟩, ⟨2543, true, false, [],
    [7]⟩, ⟨2542, true, false, [], [7]⟩, ⟨1213, false, false, [1387], []⟩, ⟨1214, false, false,
    [1387], []⟩, ⟨2519, false, false, [], [17]⟩, ⟨877, false, false, [322], [323, 1291, 17]⟩,
    ⟨1396, true, false, [], [17]⟩, ⟨1876, true, false, [322], [17]⟩, ⟨1876, true, false, [322],
    [17]⟩, ⟨1882, true, false, [322], [17]⟩, ⟨1547, true, false, [322], [17]⟩, ⟨1988, true,
    false, [322], [13, 17]⟩, ⟨976, true, false, [322, 1297], [17]⟩, ⟨975, true, false, [322,
    1297], [17]⟩, ⟨2452, false, false, [322], [17, 17]⟩, ⟨16, false, false, [322, 1383], []⟩,
    ⟨243, true, false, [], [1383]⟩, ⟨2544, false, false, [], []⟩, ⟨2544, false, false, [], []⟩,
    ⟨2453, false, false, [325], []⟩]⟩
,
  ⟨[1403, 7], [325, 1383], .contexts [⟨2545, false, false, [], []⟩, ⟨1888, true, false, [],
    [1383]⟩]⟩
,
  ⟨[1339, 7], [1405], .contexts [⟨477, true, false, [], []⟩]⟩
,
  ⟨[1339, 7], [1405], .contexts [⟨2547, false, false, [], []⟩]⟩
,
  ⟨[1405], [1405], .contexts []⟩
,
  ⟨[1405], [1405], .contexts []⟩
,
  ⟨[1339, 7], [1405], .contexts [⟨2548, false, false, [], []⟩, ⟨2549, false, false, [], []⟩,
    ⟨2550, false, false, [], []⟩, ⟨2550, false, false, [], []⟩]⟩
,
  ⟨[1405, 1], [1405, 1], .contexts []⟩
,
  ⟨[1405], [1405], .contexts []⟩
,
  ⟨[381, 1405], [381, 1405], .contexts []⟩
,
  ⟨[381, 1405], [381, 1405], .contexts []⟩
,
  ⟨[1405, 11], [1405, 11], .contexts []⟩
,
  ⟨[181, 1405], [181, 1405], .contexts []⟩
,
  ⟨[181, 1405], [181, 1405], .contexts []⟩
,
  ⟨[1405, 15], [1405, 15], .contexts []⟩
]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
