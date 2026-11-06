/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal chronological right-coset proof data from actual original-source consequences. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawCosetPrograms

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
/-- Exact literal coset claims and source or chronological right-context moves in this interval. -/
def y422CosetData80 : Fin 128 → Y522RawCosetCertificate :=
  ![
    ⟨[1199, 3], [1205], [
      .prior 10237 true [3],
      .prior 4057 true [3],
      .equation 639 true false
        []
        []]⟩,
    ⟨[4841, 15], [4841], [
      .prior 9236 false [],
      .prior 10223 false []]⟩,
    ⟨[4953, 17], [4953, 17], [
]⟩,
    ⟨[4839, 13], [4837], [
      .prior 9225 false []]⟩,
    ⟨[4839, 13], [4837], [
      .prior 10243 false []]⟩,
    ⟨[4837, 3], [1817], [
      .prior 10244 true [3],
      .equation 35 false false
        [4839, 2]
        [12],
      .equation 4 true false
        [4839, 2]
        [12],
      .prior 10227 false [12],
      .equation 10 true false
        [705, 12]
        [],
      .prior 5315 false [],
      .prior 5322 false [],
      .prior 5298 false []]⟩,
    ⟨[1817, 3], [4837], [
      .prior 10245 true [3],
      .equation 4 false false
        [4837]
        []]⟩,
    ⟨[4839, 4], [4607], [
      .equation 6 true false
        [4839, 4]
        [],
      .prior 10230 false []]⟩,
    ⟨[4837, 5], [4609], [
      .prior 10244 true [5],
      .equation 29 false false
        [4839, 4]
        [12],
      .prior 10247 false [12],
      .equation 10 true false
        [4607, 12]
        [],
      .equation 2341 true false
        []
        [],
      .prior 8859 false []]⟩,
    ⟨[4835, 13], [4835, 13], [
]⟩,
    ⟨[4835, 13], [4839], [
      .prior 10249 false [],
      .prior 9223 true [13],
      .prior 10244 true [11, 13],
      .equation 139 false false
        [4839, 10]
        [12, 10],
      .equation 8 true false
        [4839, 10]
        [12, 10],
      .prior 10228 false [12, 10],
      .equation 10 true false
        [4603, 12]
        [10],
      .prior 8837 false [10],
      .equation 8 true false
        [4603, 10]
        [],
      .prior 9511 false [],
      .prior 10226 false [],
      .prior 9228 false []]⟩,
    ⟨[4837], [4835], [
      .prior 10244 true [],
      .prior 10250 true [13],
      .equation 10 false false
        [4835]
        []]⟩,
    ⟨[4837], [4835], [
      .prior 10251 false []]⟩,
    ⟨[4835, 3], [1817], [
      .prior 10251 true [3],
      .prior 10245 false []]⟩,
    ⟨[4841, 13], [4841, 13], [
]⟩,
    ⟨[4841, 13], [4833], [
      .prior 10254 false [],
      .equation 2457 false false
        []
        [13],
      .prior 10250 true [1, 13],
      .prior 10249 true [1, 13],
      .equation 40 false false
        [4835, 0]
        [],
      .prior 9327 false [],
      .prior 9218 false []]⟩,
    ⟨[4611, 13], [5175], [
      .prior 10151 false [],
      .prior 10152 false []]⟩,
    ⟨[4831], [4611], [
      .prior 9217 true [],
      .prior 10255 true [5],
      .prior 10222 true [13, 5],
      .prior 10144 true [13, 5],
      .equation 2625 false false
        []
        [13, 5],
      .prior 10256 true [5, 13, 5],
      .equation 29 false false
        [4611, 4]
        [5],
      .prior 8864 true []]⟩,
    ⟨[4611, 3], [4829], [
      .prior 10257 true [3],
      .prior 9215 false []]⟩,
    ⟨[4831], [4611], [
      .prior 10257 false []]⟩,
    ⟨[4611, 5], [4833], [
      .prior 10257 true [5],
      .equation 2453 true false
        []
        []]⟩,
    ⟨[4611, 4], [4833], [
      .equation 6 true false
        [4611, 4]
        [],
      .prior 10260 false []]⟩,
    ⟨[4833, 15], [4833, 15], [
]⟩,
    ⟨[4833, 15], [4833], [
      .prior 10262 false [],
      .prior 10260 true [15],
      .prior 10231 true [5, 15],
      .prior 8868 true [5, 15],
      .equation 30 false false
        [4611, 4]
        [],
      .prior 10261 false [],
      .prior 9218 false []]⟩,
    ⟨[5173, 13], [5173, 13], [
]⟩,
    ⟨[5173, 13], [4829], [
      .prior 10264 false [],
      .prior 10075 true [13],
      .prior 10256 true [3, 13],
      .equation 35 false false
        [4611, 2]
        [],
      .equation 4 true false
        [4611, 2]
        [],
      .prior 10258 false [],
      .prior 9214 false []]⟩,
    ⟨[4971, 5], [4623], [
      .prior 9717 true [5],
      .prior 10236 true [5],
      .equation 2 false false
        [4619, 0]
        [5],
      .equation 26 true false
        [4619, 0]
        [5],
      .prior 8872 false [1, 5, 5],
      .equation 2348 true false
        []
        [5, 5],
      .equation 6 false false
        [4623]
        []]⟩,
    ⟨[4619, 10, 4], [4619, 5], [
      .equation 8 true false
        [4619, 10]
        [4],
      .prior 10234 true [11, 4],
      .prior 9713 true [11, 4],
      .equation 139 false false
        [4967, 10]
        [12, 10, 12, 4],
      .equation 8 true false
        [4967, 10]
        [12, 10, 12, 4],
      .prior 9706 false [12, 10, 12, 4],
      .equation 10 true false
        [237, 12]
        [10, 12, 4],
      .prior 1756 false [10, 12, 4],
      .equation 8 true false
        [237, 10]
        [12, 4],
      .equation 2520 true false
        []
        [12, 4],
      .equation 10 true false
        [4967, 12]
        [4],
      .equation 2521 true false
        []
        [4],
      .prior 9715 false [4],
      .prior 10235 false [4],
      .equation 6 true false
        [4619, 4]
        []]⟩,
    ⟨[4621, 11], [4621, 11], [
]⟩,
    ⟨[1199, 17], [1199], [
      .prior 3309 false [],
      .prior 10238 false []]⟩,
    ⟨[1205, 17], [1205, 17], [
]⟩,
    ⟨[1205, 17], [1205], [
      .prior 10270 false [],
      .prior 10240 true [17],
      .prior 10269 true [3, 17],
      .equation 37 false false
        [1199, 2]
        [],
      .equation 4 true false
        [1199, 2]
        [],
      .prior 10240 false [],
      .prior 3315 false []]⟩,
    ⟨[4953, 17], [4953], [
      .prior 10242 false [],
      .prior 10242 false [],
      .prior 9522 true [17],
      .prior 9517 true [17],
      .prior 10224 true [15, 17],
      .prior 10241 true [17, 15, 17],
      .equation 143 false false
        [4841]
        [16, 14],
      .equation 14 true false
        [4841, 16]
        [14],
      .prior 10224 false [14],
      .equation 12 true false
        [4845, 14]
        [],
      .prior 9517 false [],
      .prior 9522 false [],
      .prior 9486 false []]⟩,
    ⟨[4951, 17], [4951, 17], [
]⟩,
    ⟨[4951, 17], [4951], [
      .prior 10273 false [],
      .prior 9485 true [17],
      .prior 10272 true [13, 17],
      .equation 141 false false
        [4953, 12]
        [],
      .prior 9525 false [],
      .prior 9484 false []]⟩,
    ⟨[4833, 3], [4833, 3], [
]⟩,
    ⟨[4833, 3], [4833], [
      .prior 10275 false [],
      .prior 9220 true [3],
      .prior 10252 true [1, 3],
      .prior 10246 true [1, 3],
      .prior 5321 true [3, 1, 3],
      .equation 946 false false
        []
        [3, 1, 3],
      .prior 10253 true [1, 3, 1, 3],
      .equation 39 false false
        [4835, 0]
        [],
      .prior 9327 false [],
      .prior 9218 false []]⟩,
    ⟨[4829, 5], [4829, 5], [
]⟩,
    ⟨[4829, 5], [4829], [
      .prior 10277 false [],
      .prior 10258 true [5],
      .equation 33 false false
        [4611]
        [4, 2, 4, 2],
      .prior 10261 false [2, 4, 2],
      .equation 4 true false
        [4833, 2]
        [4, 2],
      .prior 10276 false [4, 2],
      .equation 6 true false
        [4833, 4]
        [2],
      .prior 9217 false [2],
      .prior 10259 false [2],
      .equation 4 true false
        [4611, 2]
        [],
      .prior 10258 false [],
      .prior 9214 false []]⟩,
    ⟨[4827, 13], [4827, 13], [
]⟩,
    ⟨[4625, 1], [4625, 1], [
]⟩,
    ⟨[4625, 1], [4625], [
      .prior 10280 false [],
      .equation 2349 false false
        []
        [1],
      .equation 2348 false false
        []
        [11, 1],
      .prior 8874 true [1, 11, 1],
      .equation 2347 false false
        []
        [1, 11, 1],
      .prior 10267 true [1, 11, 1],
      .equation 28 true false
        [4619]
        [10, 4, 1, 11, 1],
      .prior 8872 false [11, 1, 11, 1],
      .prior 10268 true [1, 11, 1],
      .prior 10268 true [1, 11, 1],
      .equation 43 false false
        [4621, 0]
        [10],
      .equation 2 true false
        [4621, 0]
        [10],
      .equation 2348 true false
        []
        [10],
      .equation 8 true false
        [4623, 10]
        [],
      .equation 2349 true false
        []
        [],
      .prior 8877 false []]⟩,
    ⟨[1205, 17], [1205], [
      .prior 10270 false [],
      .prior 10271 false []]⟩,
    ⟨[1207, 17], [1207, 17], [
]⟩,
    ⟨[4949, 17], [4949, 17], [
]⟩,
    ⟨[4827, 5], [4827, 5], [
]⟩,
    ⟨[4827, 16], [4825], [
      .equation 14 true false
        [4827, 16]
        [],
      .prior 9210 false []]⟩,
    ⟨[5169, 13], [5169, 13], [
]⟩,
    ⟨[5169, 13], [4825], [
      .prior 10287 false [],
      .prior 10070 true [13],
      .prior 10072 true [17, 13],
      .prior 10154 true [17, 13],
      .equation 40 true false
        [5173, 0]
        [17, 13],
      .prior 10264 false [1, 13, 17, 13],
      .prior 10265 false [1, 13, 17, 13],
      .prior 9213 false [13, 17, 13],
      .prior 10279 true [17, 13],
      .prior 10279 true [17, 13],
      .equation 141 false false
        [4827]
        [16],
      .prior 10286 false [],
      .prior 9209 false []]⟩,
    ⟨[4825, 13], [5169], [
      .prior 10288 true [13],
      .equation 10 false false
        [5169]
        []]⟩,
    ⟨[4629], [4627], [
      .equation 10 true false
        [4629]
        [],
      .equation 2351 false false
        []
        [13, 13],
      .equation 2350 false false
        []
        [1, 13, 13],
      .prior 10281 true [13, 1, 13, 13],
      .prior 10280 true [13, 1, 13, 13],
      .equation 40 false false
        [4625]
        [13],
      .prior 8877 false [13],
      .prior 8879 false []]⟩,
    ⟨[4629], [4627], [
      .prior 10290 false []]⟩,
    ⟨[4627, 15], [4631], [
      .prior 10290 true [15],
      .equation 2352 true false
        []
        []]⟩,
    ⟨[1209, 17], [1209, 17], [
]⟩,
    ⟨[1209, 17], [1209], [
      .prior 10293 false [],
      .equation 641 false false
        []
        [17],
      .prior 3318 true [1, 17],
      .equation 640 false false
        []
        [1, 17],
      .equation 6 false false
        [1205, 4]
        [1, 17],
      .equation 31 true false
        [1205, 4]
        [1, 17],
      .prior 10282 false [5, 17, 1, 17],
      .equation 640 true false
        []
        [17, 1, 17],
      .prior 10283 true [1, 17],
      .prior 10283 true [1, 17],
      .equation 41 false false
        [1207, 0]
        [],
      .equation 2 true false
        [1207, 0]
        [],
      .equation 641 true false
        []
        [],
      .prior 3321 false []]⟩,
    ⟨[4947, 17], [4947, 17], [
]⟩,
    ⟨[4947, 17], [4947], [
      .prior 10295 false [],
      .prior 9481 true [17],
      .prior 9482 true [1, 17],
      .prior 9535 true [1, 17],
      .equation 44 true false
        [4951, 10]
        [1, 17],
      .prior 10273 false [11, 17, 1, 17],
      .prior 10274 false [11, 17, 1, 17],
      .prior 9483 false [17, 1, 17],
      .prior 10284 true [1, 17],
      .prior 10284 true [1, 17],
      .equation 41 false false
        [4949, 0]
        [],
      .prior 9541 false [],
      .prior 9480 false []]⟩,
    ⟨[4825, 5], [4825, 5], [
]⟩,
    ⟨[4825, 5], [4825], [
      .prior 10297 false [],
      .prior 9210 true [5],
      .prior 9212 true [17, 5],
      .prior 9213 true [17, 5],
      .equation 2 false false
        [4829, 0]
        [17, 5],
      .equation 26 true false
        [4829, 0]
        [17, 5],
      .prior 10277 false [1, 5, 17, 5],
      .prior 10278 false [1, 5, 17, 5],
      .prior 9213 false [5, 17, 5],
      .prior 10285 true [17, 5],
      .prior 10285 true [17, 5],
      .equation 31 false false
        [4827]
        [16],
      .prior 10286 false [],
      .prior 9209 false []]⟩,
    ⟨[4823, 13], [4823, 13], [
]⟩,
    ⟨[4823, 13], [5167], [
      .prior 10299 false [],
      .prior 9207 true [13],
      .prior 10288 true [15, 13],
      .prior 10287 true [15, 13],
      .equation 138 false false
        [5169]
        [14],
      .prior 10158 false [],
      .prior 10067 false []]⟩,
    ⟨[5167, 13], [4823], [
      .prior 10300 true [13],
      .equation 10 false false
        [4823]
        []]⟩,
    ⟨[1209, 17], [1209], [
      .prior 10293 false [],
      .prior 10294 false []]⟩,
    ⟨[1209, 10], [1211], [
      .equation 8 true false
        [1209, 10]
        [],
      .equation 642 true false
        []
        []]⟩,
    ⟨[1211, 17], [1211, 17], [
]⟩,
    ⟨[1211, 17], [1211], [
      .prior 10304 false [],
      .equation 642 false false
        []
        [17],
      .prior 10302 true [11, 17],
      .equation 44 false false
        [1209, 10]
        [],
      .prior 10303 false [],
      .prior 3324 false []]⟩,
    ⟨[4945, 17], [4945, 17], [
]⟩,
    ⟨[4945, 17], [4945], [
      .prior 10306 false [],
      .prior 9479 true [17],
      .prior 10296 true [5, 17],
      .prior 10295 true [5, 17],
      .equation 31 false false
        [4947, 4]
        [],
      .prior 9543 false [],
      .prior 9478 false []]⟩,
    ⟨[4823, 5], [4823], [
      .prior 9207 true [5],
      .prior 10298 true [15, 5],
      .prior 10297 true [15, 5],
      .equation 30 false false
        [4825]
        [14],
      .equation 12 true false
        [4825, 14]
        [],
      .prior 9207 false [],
      .prior 9206 false []]⟩,
    ⟨[5163], [4821], [
      .equation 2 true false
        [5163]
        [],
      .prior 10063 true [1, 1],
      .prior 10065 true [13, 1, 1],
      .prior 10300 true [1, 13, 1, 1],
      .prior 10299 true [1, 13, 1, 1],
      .equation 40 false false
        [4823, 0]
        [1, 1],
      .prior 9206 false [1],
      .prior 9205 false []]⟩,
    ⟨[4821, 11], [5161], [
      .prior 10309 true [11],
      .prior 10061 false []]⟩,
    ⟨[5163], [4821], [
      .prior 10309 false []]⟩,
    ⟨[5165], [4819], [
      .equation 2619 false false
        []
        [],
      .prior 10311 false [13],
      .prior 9202 false []]⟩,
    ⟨[5165], [4819], [
      .prior 10312 false []]⟩,
    ⟨[4819, 1], [5167], [
      .prior 10312 true [1],
      .equation 2620 true false
        []
        []]⟩,
    ⟨[4819, 5], [4819], [
      .prior 10312 true [5],
      .prior 10162 false [],
      .prior 10313 false []]⟩,
    ⟨[1211, 12], [1213], [
      .equation 10 true false
        [1211, 12]
        [],
      .equation 643 true false
        []
        []]⟩,
    ⟨[1213, 17], [1213, 17], [
]⟩,
    ⟨[4943, 17], [4943, 17], [
]⟩,
    ⟨[4943, 17], [4943], [
      .prior 10318 false [],
      .prior 9477 true [17],
      .prior 10307 true [3, 17],
      .prior 10306 true [3, 17],
      .equation 37 false false
        [4945, 2]
        [],
      .prior 9547 false [],
      .prior 9476 false []]⟩,
    ⟨[4819, 11], [4817], [
      .prior 9197 false []]⟩,
    ⟨[4817, 5], [4817, 5], [
]⟩,
    ⟨[4817, 5], [4817], [
      .prior 10321 false [],
      .prior 10320 true [5],
      .equation 28 false false
        [4819, 4]
        [10],
      .equation 6 true false
        [4819, 4]
        [10],
      .prior 10315 false [10],
      .equation 8 true false
        [4819, 10]
        [],
      .prior 9197 false [],
      .prior 9195 false []]⟩,
    ⟨[1213, 17], [1213], [
      .prior 10317 false [],
      .prior 10317 false [],
      .equation 643 false false
        []
        [17],
      .prior 10305 true [13, 17],
      .prior 10304 true [13, 17],
      .equation 141 false false
        [1211, 12]
        [],
      .prior 10316 false [],
      .prior 3327 false []]⟩,
    ⟨[1213, 0], [1215], [
      .equation 2 true false
        [1213, 0]
        [],
      .equation 644 true false
        []
        []]⟩,
    ⟨[1215, 17], [1215, 17], [
]⟩,
    ⟨[4939, 1], [4943], [
      .prior 9472 true [1],
      .prior 9474 true [17, 1],
      .prior 10319 true [1, 17, 1],
      .prior 10318 true [1, 17, 1],
      .equation 41 false false
        [4943, 0]
        [1],
      .prior 9476 false []]⟩,
    ⟨[4941], [4939], [
      .prior 9474 true [],
      .prior 10326 true [1],
      .equation 2 false false
        [4939]
        []]⟩,
    ⟨[4817, 5], [4817], [
      .prior 10321 false [],
      .prior 10322 false []]⟩,
    ⟨[4813, 1], [4813, 1], [
]⟩,
    ⟨[4813, 1], [4817], [
      .prior 10329 false [],
      .prior 9191 true [1],
      .prior 9193 true [5, 1],
      .prior 10328 true [1, 5, 1],
      .equation 26 false false
        [4817, 0]
        [1],
      .prior 9195 false []]⟩,
    ⟨[4817, 1], [4815], [
      .prior 9193 false []]⟩,
    ⟨[4815], [4813], [
      .prior 10331 true [],
      .prior 10330 true [1],
      .equation 2 false false
        [4813]
        []]⟩,
    ⟨[1215, 17], [1215], [
      .prior 10325 false [],
      .prior 10325 false [],
      .equation 644 false false
        []
        [17],
      .prior 10323 true [1, 17],
      .equation 41 false false
        [1213, 0]
        [],
      .prior 10324 false [],
      .prior 3332 false []]⟩,
    ⟨[1215, 14], [1217], [
      .equation 12 true false
        [1215, 14]
        [],
      .equation 645 true false
        []
        []]⟩,
    ⟨[1219, 15], [1219, 15], [
]⟩,
    ⟨[5197, 13], [5199], [
      .equation 2636 true false
        []
        []]⟩,
    ⟨[5197, 13], [5199], [
      .prior 10336 false []]⟩,
    ⟨[5199, 1], [5199, 1], [
]⟩,
    ⟨[5199], [5199], [
]⟩,
    ⟨[5199, 1], [5199], [
      .prior 10338 false [],
      .prior 10337 true [1],
      .equation 40 false false
        [5197, 0]
        [12],
      .equation 2 true false
        [5197, 0]
        [12],
      .prior 10208 false [12],
      .equation 10 true false
        [5197, 12]
        [],
      .equation 2636 true false
        []
        [],
      .prior 10339 false []]⟩,
    ⟨[5199, 3], [1463], [
      .prior 10337 true [3],
      .equation 35 false false
        [5197, 2]
        [12],
      .equation 4 true false
        [5197, 2]
        [12],
      .prior 10210 false [12],
      .equation 10 true false
        [1461, 12]
        [],
      .equation 768 true false
        []
        [],
      .prior 4417 false []]⟩,
    ⟨[1463, 3], [5199], [
      .prior 10341 true [3],
      .equation 4 false false
        [5199]
        []]⟩,
    ⟨[5199, 15], [4609], [
      .prior 10337 true [15],
      .equation 138 false false
        [5197]
        [14, 12],
      .prior 10217 false [12],
      .equation 10 true false
        [4607, 12]
        [],
      .equation 2341 true false
        []
        [],
      .prior 8859 false []]⟩,
    ⟨[4609, 15], [5199], [
      .prior 10343 true [15],
      .equation 12 false false
        [5199]
        []]⟩,
    ⟨[1465, 3], [1465, 3], [
]⟩,
    ⟨[1465, 3], [1465], [
      .prior 10345 false [],
      .equation 769 false false
        []
        [3],
      .prior 10341 true [1, 3],
      .prior 10340 true [3, 1, 3],
      .prior 10338 true [3, 1, 3],
      .equation 39 false false
        [5199]
        [2, 0],
      .equation 4 true false
        [5199, 2]
        [0],
      .prior 10341 false [0],
      .equation 2 true false
        [1463, 0]
        [],
      .equation 769 true false
        []
        [],
      .prior 4426 false []]⟩,
    ⟨[1465, 3], [1465], [
      .prior 10345 false [],
      .prior 10346 false []]⟩,
    ⟨[1467, 3], [1467, 3], [
]⟩,
    ⟨[1467, 3], [1467], [
      .prior 10348 false [],
      .prior 10348 false [],
      .equation 770 false false
        []
        [3],
      .prior 10347 true [15, 3],
      .equation 36 false false
        [1465]
        [14],
      .equation 12 true false
        [1465, 14]
        [],
      .equation 770 true false
        []
        [],
      .prior 4433 false []]⟩,
    ⟨[1469, 3], [1469, 3], [
]⟩,
    ⟨[1469, 3], [1469], [
      .prior 10350 false [],
      .equation 771 false false
        []
        [3],
      .prior 10349 true [17, 3],
      .equation 37 false false
        [1467]
        [16],
      .equation 14 true false
        [1467, 16]
        [],
      .equation 771 true false
        []
        [],
      .prior 4437 false []]⟩,
    ⟨[1469, 3], [1469], [
      .prior 10350 false [],
      .prior 10351 false []]⟩,
    ⟨[1473, 1], [1473, 1], [
]⟩,
    ⟨[1473, 1], [1473], [
      .prior 10353 false [],
      .equation 773 false false
        []
        [1],
      .equation 772 false false
        []
        [3, 1],
      .prior 10352 true [1, 3, 1],
      .equation 39 false false
        [1469, 0]
        [2],
      .equation 2 true false
        [1469, 0]
        [2],
      .equation 772 true false
        []
        [2],
      .equation 4 true false
        [1471, 2]
        [],
      .equation 773 true false
        []
        [],
      .prior 4445 false []]⟩,
    ⟨[1473, 1], [1473], [
      .prior 10353 false [],
      .prior 10354 false []]⟩,
    ⟨[1477], [1475], [
      .equation 6 true false
        [1477]
        [],
      .equation 775 false false
        []
        [5, 5],
      .equation 774 false false
        []
        [1, 5, 5],
      .prior 10355 true [5, 1, 5, 5],
      .equation 26 false false
        [1473]
        [5],
      .prior 4445 false [5],
      .prior 4448 false []]⟩,
    ⟨[5201, 3], [1197], [
      .equation 2637 false false
        []
        [3],
      .equation 4 false false
        [1197]
        []]⟩,
    ⟨[1197, 3], [5201], [
      .equation 2637 true false
        []
        []]⟩,
    ⟨[1197, 3], [5201], [
      .prior 10358 false []]⟩,
    ⟨[5201], [5201], [
]⟩,
    ⟨[5201, 15], [5201, 15], [
]⟩,
    ⟨[5201, 15], [1205], [
      .prior 10361 false [],
      .prior 10359 true [15],
      .equation 36 false false
        [1197]
        [14, 2],
      .equation 12 true false
        [1197, 14]
        [2],
      .equation 636 true false
        []
        [2],
      .equation 4 true false
        [1199, 2]
        [],
      .prior 10240 false [],
      .prior 3315 false []]⟩,
    ⟨[1205, 15], [5201], [
      .prior 10362 true [15],
      .equation 12 false false
        [5201]
        []]⟩,
    ⟨[5201, 17], [5201, 17], [
]⟩,
    ⟨[5201, 17], [4829], [
      .prior 10364 false [],
      .prior 10359 true [17],
      .equation 37 false false
        [1197]
        [16, 2],
      .equation 14 true false
        [1197, 16]
        [2],
      .prior 8866 false [2],
      .equation 4 true false
        [4611, 2]
        [],
      .prior 10258 false [],
      .prior 9214 false []]⟩,
    ⟨[5201, 17], [4829], [
      .prior 10364 false [],
      .prior 10365 false []]⟩,
    ⟨[4825, 1], [4825, 1], [
]⟩]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
