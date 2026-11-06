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
def y422CosetData203 : Fin 128 → Y522RawCosetCertificate :=
  ![
    ⟨[8161], [7299], [
      .prior 22843 true [],
      .prior 16059 true [],
      .prior 25983 true [15],
      .prior 12302 false []]⟩,
    ⟨[8161], [7299], [
      .prior 25984 false []]⟩,
    ⟨[7299], [7297], [
      .prior 25984 true [],
      .prior 21379 true [],
      .equation 4118 false false
        []
        [],
      .prior 25985 false [11],
      .prior 12301 false []]⟩,
    ⟨[7299], [7297], [
      .prior 25986 false []]⟩,
    ⟨[7297, 1], [7297], [
      .prior 25986 true [1],
      .prior 25984 true [1],
      .prior 21375 false [],
      .prior 22482 false [],
      .prior 25984 false [],
      .prior 25987 false []]⟩,
    ⟨[7297, 13], [5833], [
      .prior 25986 true [13],
      .prior 25984 true [13],
      .prior 21374 true [13],
      .prior 21120 true [13],
      .equation 4302 true false
        []
        [],
      .prior 21115 false [],
      .prior 25295 false []]⟩,
    ⟨[7297, 5], [5043], [
      .prior 25986 true [5],
      .prior 25984 true [5],
      .prior 21378 false []]⟩,
    ⟨[7297, 7], [7297], [
      .prior 25986 true [7],
      .prior 25984 true [7],
      .prior 21374 true [7],
      .prior 21120 true [7],
      .prior 21113 true [7],
      .prior 21103 true [7],
      .prior 20259 true [7],
      .prior 19269 true [7],
      .equation 17 false false
        [16547]
        [],
      .prior 20572 false [],
      .prior 20573 false [],
      .prior 21103 false [],
      .prior 21114 false [],
      .prior 21121 false [],
      .prior 21376 false [],
      .prior 25985 false [],
      .prior 25987 false []]⟩,
    ⟨[7295], [4919], [
      .prior 12300 true [],
      .prior 25987 true [3],
      .prior 25984 true [3],
      .prior 13156 false [],
      .prior 21373 false []]⟩,
    ⟨[7289, 5], [311, 5], [
      .prior 12297 true [5],
      .prior 12298 true [13, 5],
      .prior 12299 true [7, 13, 5],
      .prior 25992 false [1, 7, 13, 5],
      .prior 9455 false [7, 13, 5],
      .prior 21542 false [7, 13, 5],
      .prior 21543 false [13, 5],
      .prior 9082 false [5],
      .prior 21552 false [5]]⟩,
    ⟨[7283, 3], [5095], [
      .prior 12294 true [3],
      .prior 12295 true [11, 3],
      .prior 12296 true [15, 11, 3],
      .prior 25993 false [15, 11, 3],
      .prior 1228 false [15, 11, 3],
      .prior 1235 false [11, 3],
      .prior 1223 false [3],
      .equation 2584 true false
        []
        []]⟩,
    ⟨[7277, 13], [4217], [
      .prior 12291 true [13],
      .prior 12292 true [7, 13],
      .prior 12293 true [1, 7, 13],
      .prior 25994 false [1, 7, 13],
      .prior 9982 false [7, 13],
      .prior 9986 false [13],
      .prior 8463 false []]⟩,
    ⟨[2343], [7271, 11], [
      .prior 21796 true [],
      .equation 2147 false false
        []
        [],
      .prior 8480 true [11],
      .equation 2146 false false
        []
        [15, 11],
      .prior 25995 true [5, 15, 11],
      .prior 12290 false [5, 15, 11],
      .prior 12289 false [15, 11],
      .prior 12288 false [11]]⟩,
    ⟨[2339], [7263], [
      .prior 21405 true [],
      .prior 21407 true [7],
      .prior 6450 true [7],
      .prior 21421 true [1, 7],
      .equation 1209 false false
        []
        [1, 7],
      .prior 25996 false [3, 1, 7],
      .prior 12287 false [3, 1, 7],
      .prior 12286 false [1, 7],
      .prior 12285 false [7],
      .prior 12284 false []]⟩,
    ⟨[1861], [7257], [
      .prior 21685 true [],
      .prior 21429 true [],
      .prior 21443 true [15],
      .prior 6453 true [15],
      .prior 21446 true [5, 15],
      .prior 21400 true [5, 15],
      .prior 25997 false [13, 5, 15],
      .prior 12283 false [5, 15],
      .prior 12282 false [15],
      .prior 12281 false []]⟩,
    ⟨[7251], [2139], [
      .prior 12278 true [],
      .prior 12279 true [1],
      .prior 12280 true [3, 1],
      .prior 25998 true [11, 3, 1],
      .prior 21684 false [3, 1],
      .prior 6344 false [1],
      .prior 6340 false []]⟩,
    ⟨[7245], [2285], [
      .prior 12275 true [],
      .prior 12276 true [13],
      .prior 12277 true [7, 13],
      .prior 25999 false [9, 7, 13],
      .prior 6360 false [7, 13],
      .prior 6357 false [13],
      .prior 6364 false []]⟩,
    ⟨[7243], [2427], [
      .prior 12274 true [],
      .prior 26000 false [5],
      .prior 6623 false []]⟩,
    ⟨[7689], [7241], [
      .prior 24150 true [],
      .prior 26001 true [15],
      .prior 12273 false []]⟩,
    ⟨[7691], [7569], [
      .prior 24067 false []]⟩,
    ⟨[7689], [7241], [
      .prior 26002 false []]⟩,
    ⟨[7241], [7239], [
      .prior 26004 true [],
      .prior 24149 true [],
      .prior 24147 true [],
      .equation 9 true false
        [1877, 8]
        [],
      .prior 24209 false [9, 11],
      .prior 24145 false [11],
      .prior 26004 false [11],
      .prior 12272 false []]⟩,
    ⟨[7241], [7239], [
      .prior 26005 false []]⟩,
    ⟨[7239], [7237], [
      .prior 26006 true [],
      .prior 26004 true [],
      .prior 24149 true [],
      .prior 24147 true [],
      .equation 5 true false
        [1877]
        [8],
      .prior 24208 false [9, 3],
      .prior 24145 false [3],
      .prior 26002 false [3],
      .prior 26006 false [3],
      .prior 12271 false []]⟩,
    ⟨[7237, 11], [7237], [
      .prior 26007 true [11],
      .equation 3657 true false
        []
        [],
      .prior 26006 false [],
      .prior 26007 false []]⟩,
    ⟨[7237, 15], [2427], [
      .prior 26007 true [15],
      .prior 26005 true [15],
      .equation 3658 true false
        []
        [],
      .prior 26001 false []]⟩,
    ⟨[7237, 5], [7569], [
      .prior 26007 true [5],
      .prior 26005 true [5],
      .prior 26002 true [5],
      .equation 3882 true false
        []
        [],
      .prior 26003 false []]⟩,
    ⟨[7239], [7237], [
      .prior 26007 false []]⟩,
    ⟨[7237, 13], [7237], [
      .prior 26007 true [13],
      .prior 26005 true [13],
      .prior 26002 true [13],
      .prior 24145 true [13],
      .prior 24210 true [9, 13],
      .equation 11 false false
        [1877, 8]
        [],
      .prior 24147 false [],
      .prior 24149 false [],
      .prior 26004 false [],
      .prior 26006 false [],
      .prior 26011 false []]⟩,
    ⟨[5285, 17], [5561], [
      .prior 23298 false [],
      .prior 23300 false [],
      .prior 23364 false [],
      .prior 23381 false []]⟩,
    ⟨[5561, 15], [5561, 15], [
]⟩,
    ⟨[5561, 15], [6625], [
      .prior 26014 false [],
      .prior 26013 true [15],
      .equation 143 false false
        [5285, 14]
        [16, 14, 16],
      .prior 25403 false [16, 14, 16],
      .equation 14 true false
        [6901, 16]
        [14, 16],
      .prior 25563 false [14, 16],
      .equation 12 true false
        [9829, 14]
        [16],
      .prior 25480 false [16],
      .equation 14 true false
        [14041, 16]
        [],
      .prior 25475 false [],
      .prior 25474 false []]⟩,
    ⟨[6625, 15], [6627], [
      .equation 3350 true false
        []
        []]⟩,
    ⟨[6627], [5561], [
      .prior 26016 true [],
      .prior 26015 true [15],
      .equation 12 false false
        [5561]
        []]⟩,
    ⟨[6633, 1], [5291, 1], [
      .equation 3353 false false
        []
        [1],
      .equation 3352 false false
        []
        [7, 1],
      .equation 3351 false false
        []
        [13, 7, 1],
      .prior 26017 false [5, 13, 7, 1],
      .prior 10750 false [13, 7, 1],
      .prior 23730 false [13, 7, 1],
      .prior 10676 false [7, 1],
      .prior 13678 false [1]]⟩,
    ⟨[6635], [5291], [
      .equation 3354 false false
        []
        [],
      .prior 26018 false [],
      .prior 25925 false []]⟩,
    ⟨[5291, 3], [6637], [
      .prior 26019 true [3],
      .equation 3355 true false
        []
        []]⟩,
    ⟨[3067, 3], [2607], [
      .prior 23325 false []]⟩,
    ⟨[8721, 3], [8721, 3], [
]⟩,
    ⟨[8721, 3], [9183], [
      .prior 26022 false [],
      .prior 24857 true [3],
      .prior 26021 true [9, 3],
      .equation 5 false false
        [3067]
        [8],
      .prior 24293 false [],
      .prior 24294 false []]⟩,
    ⟨[2191, 5], [2191], [
      .prior 25044 true [5],
      .equation 1584 true false
        []
        [],
      .prior 24380 false [],
      .prior 25044 false []]⟩,
    ⟨[2193, 5], [2193, 5], [
]⟩,
    ⟨[2193], [2193], [
]⟩,
    ⟨[2193, 5], [2193], [
      .prior 26025 false [],
      .equation 1133 false false
        []
        [5],
      .prior 26024 true [1, 5],
      .equation 26 false false
        [2191, 0]
        [],
      .equation 2 true false
        [2191, 0]
        [],
      .equation 1133 true false
        []
        [],
      .prior 26026 false []]⟩,
    ⟨[5289, 13], [5561], [
      .prior 13682 false [],
      .prior 23388 false []]⟩,
    ⟨[6625, 13], [6625, 13], [
]⟩,
    ⟨[6625, 13], [5287], [
      .prior 26029 false [],
      .prior 26015 true [13],
      .prior 26028 true [15, 13],
      .equation 138 false false
        [5289]
        [14],
      .equation 12 true false
        [5289, 14]
        [],
      .prior 10674 false [],
      .prior 13635 false []]⟩,
    ⟨[5287, 13], [6625], [
      .prior 26030 true [13],
      .equation 10 false false
        [6625]
        []]⟩,
    ⟨[5289, 3], [6277], [
      .prior 23354 false []]⟩,
    ⟨[9573, 5], [9573, 5], [
]⟩,
    ⟨[6637], [6637], [
]⟩,
    ⟨[9573, 5], [6637], [
      .prior 26033 false [],
      .prior 14533 true [5],
      .prior 22818 true [3, 5],
      .prior 22323 true [3, 5],
      .prior 26032 true [5, 3, 5],
      .equation 33 false false
        [5289]
        [4, 2],
      .prior 13675 false [2],
      .equation 4 true false
        [5291, 2]
        [],
      .prior 26020 false [],
      .prior 26034 false []]⟩,
    ⟨[6637, 5], [9573], [
      .prior 26035 true [5],
      .equation 6 false false
        [9573]
        []]⟩,
    ⟨[5285, 5], [7325], [
      .prior 23342 false [],
      .prior 23344 false [],
      .prior 25946 false []]⟩,
    ⟨[16827, 5], [6901], [
      .prior 25947 true [5],
      .prior 26037 true [15, 5],
      .equation 30 false false
        [5285]
        [14],
      .prior 25403 false [],
      .prior 25561 false []]⟩,
    ⟨[6901, 5], [16827], [
      .prior 26038 true [5],
      .equation 6 false false
        [16827]
        []]⟩,
    ⟨[5287, 3], [11425], [
      .prior 23345 false [],
      .prior 23346 false []]⟩,
    ⟨[5287, 12], [6625], [
      .equation 10 true false
        [5287, 12]
        [],
      .prior 26031 false []]⟩,
    ⟨[12375, 3], [12375, 3], [
]⟩,
    ⟨[12375, 3], [6625], [
      .prior 26042 false [],
      .prior 23284 true [3],
      .prior 26040 true [13, 3],
      .equation 35 false false
        [5287]
        [12],
      .prior 26041 false [],
      .prior 25474 false []]⟩,
    ⟨[6625, 3], [12375], [
      .prior 26043 true [3],
      .equation 4 false false
        [12375]
        []]⟩,
    ⟨[5287, 7], [2735], [
      .prior 13636 true [7],
      .equation 17 false false
        [6001]
        [],
      .prior 23380 false []]⟩,
    ⟨[5287, 4], [7327], [
      .equation 6 true false
        [5287, 4]
        [],
      .prior 25409 false [],
      .prior 25942 false []]⟩,
    ⟨[7327, 7], [7327, 7], [
]⟩,
    ⟨[7327], [7327], [
]⟩,
    ⟨[7327, 7], [7327], [
      .prior 26047 false [],
      .prior 25942 true [7],
      .prior 25409 true [7],
      .prior 23379 true [5, 7],
      .prior 16527 true [7, 5, 7],
      .equation 1405 false false
        []
        [7, 5, 7],
      .prior 26045 true [5, 7, 5, 7],
      .equation 27 false false
        [5287, 4]
        [],
      .prior 26046 false [],
      .prior 26048 false []]⟩,
    ⟨[2745, 7], [2745, 7], [
]⟩,
    ⟨[2745, 7], [6625], [
      .prior 26050 false [],
      .prior 24520 true [7],
      .prior 23530 true [7],
      .prior 26045 true [13, 7],
      .equation 22 false false
        [5287]
        [12],
      .prior 26041 false [],
      .prior 25474 false []]⟩,
    ⟨[6625, 7], [2745], [
      .prior 26051 true [7],
      .equation 17 false false
        [2745]
        []]⟩,
    ⟨[5289, 5], [5291], [
      .equation 2682 true false
        []
        []]⟩,
    ⟨[5291, 11], [5291, 11], [
]⟩,
    ⟨[5291, 11], [16827], [
      .prior 26054 false [],
      .prior 26053 true [11],
      .equation 28 false false
        [5289]
        [10, 4],
      .prior 25926 false [4],
      .equation 6 true false
        [6901, 4]
        [],
      .prior 26039 false [],
      .prior 25699 false []]⟩,
    ⟨[8059], [5291], [
      .equation 8 true false
        [8059]
        [],
      .prior 12978 true [11, 11],
      .prior 25700 true [3, 11, 11],
      .equation 34 false false
        [8063, 2]
        [11],
      .prior 25698 false [11],
      .prior 25699 false [11],
      .prior 26055 true [11],
      .equation 8 false false
        [5291]
        []]⟩,
    ⟨[8061], [6637], [
      .equation 4067 false false
        []
        [],
      .prior 26056 false [3],
      .prior 26020 false []]⟩,
    ⟨[6637, 15], [16833], [
      .prior 26057 true [15],
      .prior 25692 false []]⟩,
    ⟨[8061], [6637], [
      .prior 26057 false []]⟩,
    ⟨[8063], [6639], [
      .equation 4068 false false
        []
        [],
      .prior 26059 false [11],
      .equation 3356 true false
        []
        []]⟩,
    ⟨[8063], [6639], [
      .prior 26060 false []]⟩,
    ⟨[6639, 1], [6639], [
      .prior 26060 true [1],
      .prior 25688 true [1],
      .equation 137 false false
        [8065, 0]
        [14, 0, 14],
      .equation 2 true false
        [8065, 0]
        [14, 0, 14],
      .prior 23184 false [14, 0, 14],
      .equation 12 true false
        [8183, 14]
        [0, 14],
      .prior 22914 false [0, 14],
      .equation 2 true false
        [8183, 0]
        [14],
      .prior 22917 false [14],
      .prior 25689 false [14],
      .equation 12 true false
        [8065, 14]
        [],
      .prior 12980 false [],
      .prior 25690 false [],
      .prior 26061 false []]⟩,
    ⟨[6639, 7], [6639], [
      .prior 26060 true [7],
      .prior 25691 false [],
      .prior 26061 false []]⟩,
    ⟨[6639, 13], [8445], [
      .prior 26060 true [13],
      .prior 25696 false [],
      .prior 25767 false []]⟩,
    ⟨[7323], [6641], [
      .prior 25949 true [],
      .equation 4069 false false
        []
        [],
      .prior 26061 false [15],
      .equation 3357 true false
        []
        []]⟩,
    ⟨[6641, 1], [7319], [
      .prior 26065 true [1],
      .prior 12313 false [],
      .prior 25955 false []]⟩,
    ⟨[7323], [6641], [
      .prior 26065 false []]⟩,
    ⟨[6641, 7], [6641], [
      .prior 26065 true [7],
      .prior 25948 true [7],
      .prior 23109 false [],
      .prior 25949 false [],
      .prior 26067 false []]⟩,
    ⟨[6641, 13], [12061], [
      .prior 26065 true [13],
      .prior 25948 true [13],
      .prior 23112 false [],
      .prior 25813 false []]⟩,
    ⟨[8067], [6643], [
      .equation 4070 false false
        []
        [],
      .prior 25948 false [5],
      .prior 26067 false [5],
      .equation 3358 true false
        []
        []]⟩,
    ⟨[8065], [6641], [
      .prior 25949 false [],
      .prior 26065 false []]⟩,
    ⟨[6643, 3], [9579], [
      .prior 26070 true [3],
      .prior 22924 true [3],
      .equation 4 false false
        [9579]
        []]⟩,
    ⟨[6643, 1], [6303], [
      .prior 26070 true [1],
      .prior 23114 true [1],
      .equation 2 false false
        [6303]
        []]⟩,
    ⟨[8067], [6643], [
      .prior 26070 false []]⟩,
    ⟨[8069], [6645], [
      .equation 4071 false false
        []
        [],
      .prior 26074 false [13],
      .equation 3359 true false
        []
        []]⟩,
    ⟨[6645, 3], [10927], [
      .prior 26075 true [3],
      .prior 22181 true [3],
      .prior 15933 false []]⟩,
    ⟨[6645, 15], [10909], [
      .prior 26075 true [15],
      .prior 22182 false []]⟩,
    ⟨[12399], [7311], [
      .prior 22889 false [],
      .prior 25961 false [],
      .prior 25963 false [],
      .prior 25965 false []]⟩,
    ⟨[6645, 1], [7311], [
      .prior 26075 true [1],
      .prior 22184 false [],
      .prior 26078 false []]⟩,
    ⟨[6645, 5], [12061], [
      .prior 26075 true [5],
      .prior 23028 false [],
      .prior 25813 false []]⟩,
    ⟨[6645, 11], [5307], [
      .prior 26075 true [11],
      .prior 23119 true [11],
      .equation 8 false false
        [8451]
        [],
      .prior 24884 false []]⟩,
    ⟨[8069], [6645], [
      .prior 26075 false []]⟩,
    ⟨[6647], [1221], [
      .equation 3360 false false
        []
        [],
      .prior 26082 true [7],
      .equation 4072 true false
        []
        [],
      .prior 22180 false []]⟩,
    ⟨[6653, 15], [281, 15], [
      .equation 3363 false false
        []
        [15],
      .equation 3362 false false
        []
        [11, 15],
      .equation 3361 false false
        []
        [3, 11, 15],
      .prior 26083 false [1, 3, 11, 15],
      .prior 3344 false [3, 11, 15],
      .prior 21025 false [11, 15],
      .prior 12843 false [15]]⟩,
    ⟨[6659, 7], [16519], [
      .equation 3366 false false
        []
        [7],
      .equation 3365 false false
        []
        [13, 7],
      .equation 3364 false false
        []
        [5, 13, 7],
      .prior 26084 false [5, 13, 7],
      .equation 177 true false
        []
        [5, 13, 7],
      .prior 20441 false [5, 13, 7],
      .prior 20461 false [13, 7],
      .prior 21118 false [13, 7],
      .prior 10255 false [7],
      .prior 20985 false [7],
      .equation 8296 true false
        []
        []]⟩,
    ⟨[6665, 11], [1817], [
      .equation 3369 false false
        []
        [11],
      .equation 3368 false false
        []
        [3, 11],
      .equation 3367 false false
        []
        [1, 3, 11],
      .prior 26085 false [1, 3, 11],
      .prior 22174 false [1, 3, 11],
      .prior 701 false [3, 11],
      .prior 18798 false [11],
      .prior 20770 false [11],
      .prior 5323 false []]⟩,
    ⟨[307], [6671, 13], [
      .prior 1259 true [],
      .prior 20714 true [13],
      .prior 20715 true [5, 13],
      .prior 11563 true [5, 13],
      .prior 26086 true [15, 5, 13],
      .equation 3370 true false
        []
        [15, 5, 13],
      .equation 3371 true false
        []
        [5, 13],
      .equation 3372 true false
        []
        [13]]⟩,
    ⟨[1971], [6679], [
      .prior 5595 true [],
      .prior 5644 true [3],
      .prior 5597 true [3],
      .prior 5636 true [1, 3],
      .prior 26087 false [7, 1, 3],
      .equation 3373 true false
        []
        [7, 1, 3],
      .equation 3374 true false
        []
        [1, 3],
      .equation 3375 true false
        []
        [3],
      .equation 3376 true false
        []
        []]⟩,
    ⟨[2153], [6685], [
      .equation 1113 false false
        []
        [],
      .prior 6169 true [5],
      .prior 6167 true [15, 5],
      .prior 26088 false [11, 15, 5],
      .equation 3377 true false
        []
        [15, 5],
      .equation 3378 true false
        []
        [5],
      .equation 3379 true false
        []
        []]⟩,
    ⟨[6691], [4219], [
      .equation 3382 false false
        []
        [],
      .equation 3381 false false
        []
        [1],
      .equation 3380 false false
        []
        [7, 1],
      .prior 26089 true [13, 7, 1],
      .prior 8478 false [7, 1],
      .prior 8485 false [1],
      .prior 8473 false []]⟩,
    ⟨[6697], [2343], [
      .equation 3385 false false
        []
        [],
      .equation 3384 false false
        []
        [15],
      .equation 3383 false false
        []
        [11, 15],
      .prior 26090 false [3, 11, 15],
      .prior 8475 false [11, 15],
      .equation 2147 true false
        []
        [15],
      .prior 21796 false [15],
      .prior 21413 false []]⟩,
    ⟨[6703, 1], [4729, 1], [
      .equation 3388 false false
        []
        [1],
      .equation 3387 false false
        []
        [7, 1],
      .equation 3386 false false
        []
        [13, 7, 1],
      .prior 26091 false [5, 13, 7, 1],
      .prior 21414 false [13, 7, 1],
      .prior 13048 false [7, 1],
      .prior 21458 false [7, 1],
      .prior 21438 false [1]]⟩,
    ⟨[6709, 15], [1289], [
      .equation 3391 false false
        []
        [15],
      .equation 3390 false false
        []
        [11, 15],
      .equation 3389 false false
        []
        [3, 11, 15],
      .prior 26092 false [3, 11, 15],
      .prior 8982 false [3, 11, 15],
      .prior 8969 false [11, 15],
      .prior 8975 false [15],
      .equation 681 true false
        []
        []]⟩,
    ⟨[6715, 7], [2283], [
      .equation 3394 false false
        []
        [7],
      .equation 3393 false false
        []
        [13, 7],
      .equation 3392 false false
        []
        [5, 13, 7],
      .prior 26093 false [5, 13, 7],
      .prior 3536 false [13, 7],
      .prior 3532 false [7],
      .prior 6350 false []]⟩,
    ⟨[6721], [2285], [
      .equation 3397 false false
        []
        [],
      .equation 3396 false false
        []
        [1],
      .equation 3395 false false
        []
        [9, 1],
      .prior 26094 false [9, 1],
      .prior 8625 false [1],
      .prior 8612 false []]⟩,
    ⟨[2285, 3], [6723], [
      .prior 26095 true [3],
      .equation 3398 true false
        []
        []]⟩,
    ⟨[8055], [5291], [
      .equation 2 true false
        [8055]
        [],
      .prior 12976 true [1, 1],
      .prior 25703 true [7, 1, 1],
      .equation 18 false false
        [8059]
        [6, 1],
      .equation 17 true false
        [8059, 6]
        [1],
      .prior 12978 true [7, 1],
      .equation 19 false false
        [8061]
        [6, 2, 1],
      .equation 17 true false
        [8061, 6]
        [2, 1],
      .prior 25701 false [2, 1],
      .equation 4 true false
        [8061, 2]
        [1],
      .prior 12978 false [1],
      .prior 25702 false [1],
      .prior 25702 false [1],
      .prior 25703 false [],
      .prior 12977 true [],
      .prior 26056 false [1],
      .prior 25925 false []]⟩,
    ⟨[8049, 11], [6625, 11], [
      .prior 12973 true [11],
      .prior 12974 true [15, 11],
      .prior 12975 true [5, 15, 11],
      .prior 26097 false [13, 5, 15, 11],
      .equation 2683 true false
        []
        [5, 15, 11],
      .prior 13702 false [15, 11],
      .prior 23388 false [15, 11],
      .prior 26015 false [11]]⟩,
    ⟨[2725], [2017], [
      .prior 23033 false [],
      .prior 24661 false []]⟩,
    ⟨[8043, 7], [2725], [
      .prior 12970 true [7],
      .prior 12971 true [1, 7],
      .prior 12972 true [3, 1, 7],
      .prior 26098 false [3, 1, 7],
      .prior 11603 false [3, 1, 7],
      .prior 11602 false [1, 7],
      .prior 23749 false [1, 7],
      .prior 23744 false [7],
      .prior 11592 false []]⟩,
    ⟨[8037, 15], [2905], [
      .prior 12967 true [15],
      .prior 12968 true [5, 15],
      .prior 12969 true [13, 5, 15],
      .prior 26100 false [13, 5, 15],
      .prior 26099 false [13, 5, 15],
      .prior 24664 false [5, 15],
      .prior 11586 false [15],
      .prior 24659 false [15],
      .prior 24337 false []]⟩,
    ⟨[2143], [8031, 1], [
      .prior 21601 true [],
      .equation 1005 false false
        []
        [1],
      .prior 24333 true [3, 1],
      .prior 26101 true [11, 3, 1],
      .prior 12966 false [11, 3, 1],
      .prior 12965 false [3, 1],
      .prior 12964 false [1]]⟩,
    ⟨[8029], [2143], [
      .prior 12963 true [],
      .prior 26102 true []]⟩,
    ⟨[17405], [4599], [
      .prior 19827 true [],
      .prior 19828 true [13],
      .prior 19829 true [7, 13],
      .prior 22758 true [1, 7, 13],
      .prior 12963 false [7, 13],
      .prior 26103 false [7, 13],
      .prior 8798 false [13],
      .prior 8803 false []]⟩,
    ⟨[17399, 3], [2135, 3], [
      .prior 19824 true [3],
      .prior 19825 true [11, 3],
      .prior 19826 true [15, 11, 3],
      .prior 26104 false [5, 15, 11, 3],
      .prior 8795 false [15, 11, 3],
      .prior 8788 false [11, 3],
      .prior 6051 false [3]]⟩,
    ⟨[17393, 13], [1707], [
      .prior 19821 true [13],
      .prior 19822 true [7, 13],
      .prior 19823 true [1, 7, 13],
      .prior 26105 false [1, 7, 13],
      .prior 6041 false [1, 7, 13],
      .prior 599 false [7, 13],
      .prior 1711 false [7, 13],
      .prior 5116 false [13],
      .prior 5118 false []]⟩,
    ⟨[17387, 11], [2147], [
      .prior 19818 true [11],
      .prior 19819 true [15, 11],
      .prior 19820 true [5, 15, 11],
      .prior 26106 false [5, 15, 11],
      .prior 5113 false [15, 11],
      .equation 951 true false
        []
        [11],
      .prior 6141 false []]⟩,
    ⟨[619], [17381, 7], [
      .prior 6151 true [],
      .equation 1111 false false
        []
        [7],
      .prior 6130 true [1, 7],
      .prior 26107 true [3, 1, 7],
      .prior 19817 false [3, 1, 7],
      .prior 19816 false [1, 7],
      .prior 19815 false [7]]⟩,
    ⟨[315], [17373], [
      .prior 869 true [],
      .prior 9352 true [15],
      .prior 9362 true [5, 15],
      .prior 26108 false [13, 5, 15],
      .prior 19814 false [13, 5, 15],
      .prior 19813 false [5, 15],
      .prior 19812 false [15],
      .prior 19811 false []]⟩,
    ⟨[1353], [17367], [
      .prior 4142 true [],
      .prior 4144 true [1],
      .prior 21549 true [3, 1],
      .prior 4203 true [3, 1],
      .prior 26109 false [11, 3, 1],
      .prior 19810 false [3, 1],
      .prior 19809 false [1],
      .prior 19808 false []]⟩,
    ⟨[17361], [4731], [
      .prior 19805 true [],
      .prior 19806 true [5],
      .prior 19807 true [13, 5],
      .prior 26110 true [7, 13, 5],
      .prior 21550 false [13, 5],
      .prior 9061 false [5],
      .prior 9050 false []]⟩]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
