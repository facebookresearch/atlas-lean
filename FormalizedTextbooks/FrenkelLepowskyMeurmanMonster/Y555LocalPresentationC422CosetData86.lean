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
def y422CosetData86 : Fin 128 → Y522RawCosetCertificate :=
  ![
    ⟨[5889, 17], [1693], [
      .equation 2981 false false
        []
        [17],
      .equation 14 false false
        [1693]
        []]⟩,
    ⟨[1693, 17], [5889], [
      .equation 2981 true false
        []
        []]⟩,
    ⟨[5889], [5889], [
]⟩,
    ⟨[5889, 11], [5101], [
      .prior 11009 true [11],
      .equation 44 false false
        [1693, 10]
        [16],
      .equation 8 true false
        [1693, 10]
        [16],
      .equation 884 true false
        []
        [16],
      .equation 14 true false
        [1695, 16]
        [],
      .equation 2587 true false
        []
        [],
      .prior 10020 false []]⟩,
    ⟨[5101, 11], [5889], [
      .prior 11011 true [11],
      .equation 8 false false
        [5889]
        []]⟩,
    ⟨[5889, 1], [5891], [
      .equation 2982 true false
        []
        []]⟩,
    ⟨[5891], [5891], [
]⟩,
    ⟨[5891, 17], [5891, 17], [
]⟩,
    ⟨[5891, 17], [1689], [
      .prior 11015 false [],
      .prior 11013 true [17],
      .equation 41 false false
        [5889]
        [16, 0],
      .equation 14 true false
        [5889, 16]
        [0],
      .prior 11008 false [0],
      .equation 2 true false
        [1693, 0]
        [],
      .prior 5022 false [],
      .prior 5099 false [],
      .prior 5019 false []]⟩,
    ⟨[5891, 15], [4873], [
      .prior 11014 true [15],
      .equation 143 true false
        [5891, 14]
        [15, 15],
      .prior 11015 false [15, 17, 15, 17, 15, 15],
      .prior 11016 false [15, 17, 15, 17, 15, 15],
      .prior 11002 false [17, 15, 17, 15, 15],
      .prior 9423 true [17, 15, 17, 15, 15],
      .equation 14 false false
        [4869]
        [15, 17, 15, 15],
      .equation 2472 true false
        []
        [17, 15, 15],
      .equation 2473 true false
        []
        [15, 15],
      .equation 12 false false
        [4873]
        []]⟩,
    ⟨[5891, 3], [5893], [
      .equation 2983 true false
        []
        []]⟩,
    ⟨[5893], [5893], [
]⟩,
    ⟨[5893, 9], [5893], [
      .prior 11018 true [9],
      .equation 5 false false
        [5891]
        [8, 2],
      .equation 1 true false
        [5891, 8]
        [2],
      .prior 11013 true [9, 2],
      .equation 3 false false
        [5889]
        [8, 0, 2],
      .equation 1 true false
        [5889, 8]
        [0, 2],
      .prior 11009 true [9, 0, 2],
      .equation 15 false false
        [1693, 8]
        [16, 0, 2],
      .prior 5026 false [16, 0, 2],
      .equation 14 true false
        [1693, 16]
        [0, 2],
      .equation 2981 true false
        []
        [0, 2],
      .prior 11010 false [0, 2],
      .equation 2 true false
        [5889, 0]
        [2],
      .equation 2982 true false
        []
        [2],
      .prior 11014 false [2],
      .equation 4 true false
        [5891, 2]
        [],
      .equation 2983 true false
        []
        [],
      .prior 11019 false []]⟩,
    ⟨[5891, 10, 2], [5893], [
      .equation 8 true false
        [5891, 10]
        [2],
      .prior 11013 true [11, 2],
      .equation 43 false false
        [5889]
        [10, 0, 10, 0, 2],
      .equation 8 true false
        [5889, 10]
        [0, 10, 0, 2],
      .prior 11011 false [0, 10, 0, 2],
      .equation 2 true false
        [5101, 0]
        [10, 0, 2],
      .prior 10021 false [10, 0, 2],
      .equation 8 true false
        [5101, 10]
        [0, 2],
      .prior 11012 false [0, 2],
      .equation 2 true false
        [5889, 0]
        [2],
      .equation 2982 true false
        []
        [2],
      .prior 11014 false [2],
      .equation 4 true false
        [5891, 2]
        [],
      .equation 2983 true false
        []
        []]⟩,
    ⟨[5893, 17], [5893, 17], [
]⟩,
    ⟨[1683, 1], [5893], [
      .prior 5012 true [1],
      .prior 5015 true [17, 1],
      .prior 5017 true [1, 17, 1],
      .prior 5018 true [1, 17, 1],
      .equation 4 false false
        [1689, 2]
        [1, 17, 1],
      .prior 11016 true [2, 1, 17, 1],
      .equation 14 false false
        [5891, 16]
        [2, 1, 17, 1],
      .equation 37 true false
        [5891]
        [16, 2, 1, 17, 1],
      .prior 11018 false [17, 1, 17, 1],
      .prior 11022 true [1, 17, 1],
      .prior 11022 true [1, 17, 1],
      .equation 41 false false
        [5893, 0]
        [1],
      .prior 11019 false []]⟩,
    ⟨[5893, 1], [1683], [
      .prior 11023 true [1],
      .equation 2 false false
        [1683]
        []]⟩,
    ⟨[5895, 5], [5893], [
      .equation 2984 false false
        []
        [5],
      .equation 6 false false
        [5893]
        []]⟩,
    ⟨[5893, 5], [5895], [
      .equation 2984 true false
        []
        []]⟩,
    ⟨[5895], [5895], [
]⟩,
    ⟨[5897, 1], [5895], [
      .equation 2985 false false
        []
        [1],
      .equation 2 false false
        [5895]
        []]⟩,
    ⟨[5895, 1], [5897], [
      .equation 2985 true false
        []
        []]⟩,
    ⟨[5897], [5897], [
]⟩,
    ⟨[5897, 11], [5899], [
      .equation 2986 true false
        []
        []]⟩,
    ⟨[5897, 0, 10, 0, 10], [5899], [
      .equation 2 true false
        [5897, 0]
        [10, 0, 10],
      .prior 11028 false [10, 0, 10],
      .equation 8 true false
        [5895, 10]
        [0, 10],
      .prior 11026 true [11, 0, 10],
      .equation 28 false false
        [5893]
        [10, 4, 0, 10],
      .equation 8 true false
        [5893, 10]
        [4, 0, 10],
      .prior 11018 true [11, 4, 0, 10],
      .equation 34 false false
        [5891]
        [10, 2, 4, 0, 10],
      .prior 11021 false [4, 0, 10],
      .prior 11019 false [4, 0, 10],
      .equation 6 true false
        [5893, 4]
        [0, 10],
      .equation 2984 true false
        []
        [0, 10],
      .prior 11027 false [0, 10],
      .equation 2 true false
        [5895, 0]
        [10],
      .equation 2985 true false
        []
        [10],
      .equation 8 true false
        [5897, 10]
        [],
      .equation 2986 true false
        []
        []]⟩,
    ⟨[5899], [5899], [
]⟩,
    ⟨[5897, 8, 10], [5899], [
      .equation 1 true false
        [5897, 8]
        [10],
      .prior 11029 true [9, 10],
      .equation 3 false false
        [5895]
        [8, 0, 10],
      .equation 1 true false
        [5895, 8]
        [0, 10],
      .prior 11026 true [9, 0, 10],
      .equation 7 false false
        [5893]
        [8, 4, 0, 10],
      .equation 1 true false
        [5893, 8]
        [4, 0, 10],
      .prior 11020 false [4, 0, 10],
      .equation 6 true false
        [5893, 4]
        [0, 10],
      .equation 2984 true false
        []
        [0, 10],
      .prior 11027 false [0, 10],
      .equation 2 true false
        [5895, 0]
        [10],
      .equation 2985 true false
        []
        [10],
      .prior 11030 false [10],
      .equation 8 true false
        [5897, 10]
        [],
      .equation 2986 true false
        []
        []]⟩,
    ⟨[5899, 13], [5901], [
      .equation 2987 true false
        []
        []]⟩,
    ⟨[5901], [5901], [
]⟩,
    ⟨[5903, 8], [5903], [
      .equation 1 true false
        [5903, 8]
        [],
      .equation 2988 false false
        []
        [9],
      .equation 13 false false
        [5901, 8]
        [14],
      .equation 1 true false
        [5901, 8]
        [14],
      .prior 11035 true [9, 14],
      .equation 11 false false
        [5899, 8]
        [12, 14],
      .equation 1 true false
        [5899, 8]
        [12, 14],
      .prior 11031 true [9, 12, 14],
      .equation 9 false false
        [5897, 8]
        [10, 12, 14],
      .prior 11034 false [12, 14],
      .prior 11033 false [12, 14],
      .equation 10 true false
        [5899, 12]
        [14],
      .equation 2987 true false
        []
        [14],
      .prior 11036 false [14],
      .equation 12 true false
        [5901, 14]
        [],
      .equation 2988 true false
        []
        []]⟩,
    ⟨[5909, 9], [5909], [
      .equation 2991 false false
        []
        [9],
      .equation 5 false false
        [5907]
        [8, 2],
      .equation 1 true false
        [5907, 8]
        [2],
      .equation 2990 false false
        []
        [9, 2],
      .equation 3 false false
        [5905]
        [8, 0, 2],
      .equation 1 true false
        [5905, 8]
        [0, 2],
      .equation 2989 false false
        []
        [9, 0, 2],
      .equation 15 false false
        [5903, 8]
        [16, 0, 2],
      .prior 11037 false [16, 0, 2],
      .equation 14 true false
        [5903, 16]
        [0, 2],
      .equation 2989 true false
        []
        [0, 2],
      .equation 2 true false
        [5905, 0]
        [2],
      .equation 2990 true false
        []
        [2],
      .equation 4 true false
        [5907, 2]
        [],
      .equation 2991 true false
        []
        []]⟩,
    ⟨[5913, 8, 10], [5913, 11], [
      .equation 1 true false
        [5913, 8]
        [10],
      .equation 2993 false false
        []
        [9, 10],
      .equation 3 false false
        [5911]
        [8, 0, 10],
      .equation 1 true false
        [5911, 8]
        [0, 10],
      .equation 2992 false false
        []
        [9, 0, 10],
      .equation 7 false false
        [5909]
        [8, 4, 0, 10],
      .equation 1 true false
        [5909, 8]
        [4, 0, 10],
      .prior 11038 false [4, 0, 10],
      .equation 6 true false
        [5909, 4]
        [0, 10],
      .equation 2992 true false
        []
        [0, 10],
      .equation 2 true false
        [5911, 0]
        [10],
      .equation 2993 true false
        []
        [10],
      .equation 8 true false
        [5913, 10]
        []]⟩,
    ⟨[5919, 9], [5919], [
      .equation 2996 false false
        []
        [9],
      .equation 3 false false
        [5917]
        [8, 0],
      .equation 1 true false
        [5917, 8]
        [0],
      .equation 2995 false false
        []
        [9, 0],
      .equation 11 false false
        [5915, 8]
        [12, 0],
      .equation 1 true false
        [5915, 8]
        [12, 0],
      .equation 2994 false false
        []
        [9, 12, 0],
      .equation 9 false false
        [5913, 8]
        [10, 12, 0],
      .prior 11039 false [12, 0],
      .equation 2994 true false
        []
        [12, 0],
      .equation 10 true false
        [5915, 12]
        [0],
      .equation 2995 true false
        []
        [0],
      .equation 2 true false
        [5917, 0]
        [],
      .equation 2996 true false
        []
        []]⟩,
    ⟨[5923, 8, 0], [5923, 1], [
      .equation 1 true false
        [5923, 8]
        [0],
      .equation 2998 false false
        []
        [9, 0],
      .equation 15 false false
        [5921, 8]
        [16, 0],
      .equation 1 true false
        [5921, 8]
        [16, 0],
      .equation 2997 false false
        []
        [9, 16, 0],
      .equation 13 false false
        [5919, 8]
        [14, 16, 0],
      .equation 1 true false
        [5919, 8]
        [14, 16, 0],
      .prior 11040 false [14, 16, 0],
      .equation 12 true false
        [5919, 14]
        [16, 0],
      .equation 2997 true false
        []
        [16, 0],
      .equation 14 true false
        [5921, 16]
        [0],
      .equation 2998 true false
        []
        [0],
      .equation 2 true false
        [5923, 0]
        []]⟩,
    ⟨[5929, 9], [5929], [
      .equation 3001 false false
        []
        [9],
      .equation 7 false false
        [5927]
        [8, 4],
      .equation 1 true false
        [5927, 8]
        [4],
      .equation 3000 false false
        []
        [9, 4],
      .equation 5 false false
        [5925]
        [8, 2, 4],
      .equation 1 true false
        [5925, 8]
        [2, 4],
      .equation 2999 false false
        []
        [9, 2, 4],
      .equation 3 false false
        [5923]
        [8, 0, 2, 4],
      .prior 11041 false [2, 4],
      .equation 2999 true false
        []
        [2, 4],
      .equation 4 true false
        [5925, 2]
        [4],
      .equation 3000 true false
        []
        [4],
      .equation 6 true false
        [5927, 4]
        [],
      .equation 3001 true false
        []
        []]⟩,
    ⟨[5933, 8, 12], [5933, 13], [
      .equation 1 true false
        [5933, 8]
        [12],
      .equation 3003 false false
        []
        [9, 12],
      .equation 9 false false
        [5931, 8]
        [10, 12],
      .equation 1 true false
        [5931, 8]
        [10, 12],
      .equation 3002 false false
        []
        [9, 10, 12],
      .equation 3 false false
        [5929]
        [8, 0, 10, 12],
      .equation 1 true false
        [5929, 8]
        [0, 10, 12],
      .prior 11042 false [0, 10, 12],
      .equation 2 true false
        [5929, 0]
        [10, 12],
      .equation 3002 true false
        []
        [10, 12],
      .equation 8 true false
        [5931, 10]
        [12],
      .equation 3003 true false
        []
        [12],
      .equation 10 true false
        [5933, 12]
        []]⟩,
    ⟨[5939, 9], [5939], [
      .equation 3006 false false
        []
        [9],
      .equation 13 false false
        [5937, 8]
        [14],
      .equation 1 true false
        [5937, 8]
        [14],
      .equation 3005 false false
        []
        [9, 14],
      .equation 3 false false
        [5935]
        [8, 0, 14],
      .equation 1 true false
        [5935, 8]
        [0, 14],
      .equation 3004 false false
        []
        [9, 0, 14],
      .equation 11 false false
        [5933, 8]
        [12, 0, 14],
      .prior 11043 false [0, 14],
      .equation 3004 true false
        []
        [0, 14],
      .equation 2 true false
        [5935, 0]
        [14],
      .equation 3005 true false
        []
        [14],
      .equation 12 true false
        [5937, 14]
        [],
      .equation 3006 true false
        []
        []]⟩,
    ⟨[5943, 8, 2], [5943, 3], [
      .equation 1 true false
        [5943, 8]
        [2],
      .equation 3008 false false
        []
        [9, 2],
      .equation 3 false false
        [5941]
        [8, 0, 2],
      .equation 1 true false
        [5941, 8]
        [0, 2],
      .equation 3007 false false
        []
        [9, 0, 2],
      .equation 15 false false
        [5939, 8]
        [16, 0, 2],
      .equation 1 true false
        [5939, 8]
        [16, 0, 2],
      .prior 11044 false [16, 0, 2],
      .equation 14 true false
        [5939, 16]
        [0, 2],
      .equation 3007 true false
        []
        [0, 2],
      .equation 2 true false
        [5941, 0]
        [2],
      .equation 3008 true false
        []
        [2],
      .equation 4 true false
        [5943, 2]
        []]⟩,
    ⟨[5947, 5], [5945], [
      .equation 3010 false false
        []
        [5],
      .equation 6 false false
        [5945]
        []]⟩,
    ⟨[5949, 1], [5947], [
      .equation 3011 false false
        []
        [1],
      .equation 2 false false
        [5947]
        []]⟩,
    ⟨[5949, 9], [5949], [
      .equation 3011 false false
        []
        [9],
      .equation 3 false false
        [5947]
        [8, 0],
      .equation 1 true false
        [5947, 8]
        [0],
      .equation 3010 false false
        []
        [9, 0],
      .equation 7 false false
        [5945]
        [8, 4, 0],
      .equation 1 true false
        [5945, 8]
        [4, 0],
      .equation 3009 false false
        []
        [9, 4, 0],
      .equation 5 false false
        [5943]
        [8, 2, 4, 0],
      .prior 11045 false [4, 0],
      .equation 3009 true false
        []
        [4, 0],
      .equation 6 true false
        [5945, 4]
        [0],
      .equation 3010 true false
        []
        [0],
      .equation 2 true false
        [5947, 0]
        [],
      .equation 3011 true false
        []
        []]⟩,
    ⟨[5949], [5949], [
]⟩,
    ⟨[5951, 11], [5949], [
      .equation 3012 false false
        []
        [11],
      .equation 8 false false
        [5949]
        []]⟩,
    ⟨[5951, 9], [5951, 9], [
]⟩,
    ⟨[5951], [5951], [
]⟩,
    ⟨[5951, 9], [5951], [
      .prior 11051 false [],
      .equation 3012 false false
        []
        [9],
      .equation 9 false false
        [5949, 8]
        [10],
      .equation 1 true false
        [5949, 8]
        [10],
      .prior 11048 false [10],
      .prior 11049 false [10],
      .equation 8 true false
        [5949, 10]
        [],
      .equation 3012 true false
        []
        [],
      .prior 11052 false []]⟩,
    ⟨[5953, 13], [5951], [
      .equation 3013 false false
        []
        [13],
      .equation 10 false false
        [5951]
        []]⟩,
    ⟨[5951, 13], [5953], [
      .equation 3013 true false
        []
        []]⟩,
    ⟨[5953], [5953], [
]⟩,
    ⟨[5955, 1], [5953], [
      .equation 3014 false false
        []
        [1],
      .equation 2 false false
        [5953]
        []]⟩,
    ⟨[5955, 9], [5955, 9], [
]⟩,
    ⟨[5955], [5955], [
]⟩,
    ⟨[5955, 9], [5955], [
      .prior 11058 false [],
      .equation 3014 false false
        []
        [9],
      .equation 3 false false
        [5953]
        [8, 0],
      .equation 1 true false
        [5953, 8]
        [0],
      .prior 11055 true [9, 0],
      .equation 11 false false
        [5951, 8]
        [12, 0],
      .equation 1 true false
        [5951, 8]
        [12, 0],
      .prior 11053 false [12, 0],
      .equation 10 true false
        [5951, 12]
        [0],
      .equation 3013 true false
        []
        [0],
      .prior 11056 false [0],
      .equation 2 true false
        [5953, 0]
        [],
      .equation 3014 true false
        []
        [],
      .prior 11059 false []]⟩,
    ⟨[5957, 15], [5955], [
      .equation 3015 false false
        []
        [15],
      .equation 12 false false
        [5955]
        []]⟩,
    ⟨[5955, 15], [5957], [
      .equation 3015 true false
        []
        []]⟩,
    ⟨[5957], [5957], [
]⟩,
    ⟨[5959, 17], [5957], [
      .equation 3016 false false
        []
        [17],
      .equation 14 false false
        [5957]
        []]⟩,
    ⟨[5959], [5959], [
]⟩,
    ⟨[5961, 1], [5959], [
      .equation 3017 false false
        []
        [1],
      .equation 2 false false
        [5959]
        []]⟩,
    ⟨[5959, 8, 0], [5961], [
      .equation 1 true false
        [5959, 8]
        [0],
      .equation 3016 false false
        []
        [9, 0],
      .equation 15 false false
        [5957, 8]
        [16, 0],
      .equation 1 true false
        [5957, 8]
        [16, 0],
      .prior 11062 true [9, 16, 0],
      .equation 13 false false
        [5955, 8]
        [14, 16, 0],
      .equation 1 true false
        [5955, 8]
        [14, 16, 0],
      .prior 11060 false [14, 16, 0],
      .equation 12 true false
        [5955, 14]
        [16, 0],
      .equation 3015 true false
        []
        [16, 0],
      .prior 11063 false [16, 0],
      .equation 14 true false
        [5957, 16]
        [0],
      .equation 3016 true false
        []
        [0],
      .prior 11065 false [0],
      .equation 2 true false
        [5959, 0]
        [],
      .equation 3017 true false
        []
        []]⟩,
    ⟨[5961], [5961], [
]⟩,
    ⟨[5963, 3], [5961], [
      .equation 3018 false false
        []
        [3],
      .equation 4 false false
        [5961]
        []]⟩,
    ⟨[5963], [5963], [
]⟩,
    ⟨[5965, 5], [5963], [
      .equation 3019 false false
        []
        [5],
      .equation 6 false false
        [5963]
        []]⟩,
    ⟨[5965, 9], [5965], [
      .equation 3019 false false
        []
        [9],
      .equation 7 false false
        [5963]
        [8, 4],
      .equation 1 true false
        [5963, 8]
        [4],
      .equation 3018 false false
        []
        [9, 4],
      .equation 5 false false
        [5961]
        [8, 2, 4],
      .equation 1 true false
        [5961, 8]
        [2, 4],
      .equation 3017 false false
        []
        [9, 2, 4],
      .equation 3 false false
        [5959]
        [8, 0, 2, 4],
      .prior 11067 false [2, 4],
      .prior 11068 false [2, 4],
      .equation 4 true false
        [5961, 2]
        [4],
      .equation 3018 true false
        []
        [4],
      .prior 11070 false [4],
      .equation 6 true false
        [5963, 4]
        [],
      .equation 3019 true false
        []
        []]⟩,
    ⟨[5965, 9], [5965, 9], [
]⟩,
    ⟨[5965], [5965], [
]⟩,
    ⟨[5965, 9], [5965], [
      .prior 11073 false [],
      .prior 11072 false [],
      .prior 11074 false []]⟩,
    ⟨[5967, 1], [5965], [
      .equation 3020 false false
        []
        [1],
      .equation 2 false false
        [5965]
        []]⟩,
    ⟨[5965, 1], [5967], [
      .equation 3020 true false
        []
        []]⟩,
    ⟨[5967], [5967], [
]⟩,
    ⟨[5969, 11], [5967], [
      .equation 3021 false false
        []
        [11],
      .equation 8 false false
        [5967]
        []]⟩,
    ⟨[5971, 13], [5969], [
      .equation 3022 false false
        []
        [13],
      .equation 10 false false
        [5969]
        []]⟩,
    ⟨[5969, 8, 12], [5971], [
      .equation 1 true false
        [5969, 8]
        [12],
      .equation 3021 false false
        []
        [9, 12],
      .equation 9 false false
        [5967, 8]
        [10, 12],
      .equation 1 true false
        [5967, 8]
        [10, 12],
      .prior 11077 true [9, 10, 12],
      .equation 3 false false
        [5965]
        [8, 0, 10, 12],
      .equation 1 true false
        [5965, 8]
        [0, 10, 12],
      .prior 11075 false [0, 10, 12],
      .equation 2 true false
        [5965, 0]
        [10, 12],
      .equation 3020 true false
        []
        [10, 12],
      .prior 11078 false [10, 12],
      .equation 8 true false
        [5967, 10]
        [12],
      .equation 3021 true false
        []
        [12],
      .equation 10 true false
        [5969, 12]
        [],
      .equation 3022 true false
        []
        []]⟩,
    ⟨[5973, 1], [5971], [
      .equation 3023 false false
        []
        [1],
      .equation 2 false false
        [5971]
        []]⟩,
    ⟨[5975, 15], [5973], [
      .equation 3024 false false
        []
        [15],
      .equation 12 false false
        [5973]
        []]⟩,
    ⟨[5975, 9], [5975], [
      .equation 3024 false false
        []
        [9],
      .equation 13 false false
        [5973, 8]
        [14],
      .equation 1 true false
        [5973, 8]
        [14],
      .equation 3023 false false
        []
        [9, 14],
      .equation 3 false false
        [5971]
        [8, 0, 14],
      .equation 1 true false
        [5971, 8]
        [0, 14],
      .equation 3022 false false
        []
        [9, 0, 14],
      .equation 11 false false
        [5969, 8]
        [12, 0, 14],
      .prior 11081 false [0, 14],
      .equation 2 true false
        [5971, 0]
        [14],
      .equation 3023 true false
        []
        [14],
      .equation 12 true false
        [5973, 14]
        [],
      .equation 3024 true false
        []
        []]⟩,
    ⟨[5975], [5975], [
]⟩,
    ⟨[5977, 17], [5975], [
      .equation 3025 false false
        []
        [17],
      .equation 14 false false
        [5975]
        []]⟩,
    ⟨[5977], [5977], [
]⟩,
    ⟨[5977, 1], [5979], [
      .equation 3026 true false
        []
        []]⟩,
    ⟨[5977, 16], [5975], [
      .equation 14 true false
        [5977, 16]
        [],
      .prior 11086 false []]⟩,
    ⟨[
      5977, 16, 14, 0, 12, 10, 0, 4, 2
    ], [5963, 2], [
      .prior 11089 false [
        14, 0, 12, 10, 0, 4, 2
      ],
      .equation 12 true false
        [5975, 14]
        [0, 12, 10, 0, 4, 2],
      .prior 11083 false [0, 12, 10, 0, 4, 2],
      .equation 2 true false
        [5973, 0]
        [12, 10, 0, 4, 2],
      .prior 11082 false [12, 10, 0, 4, 2],
      .equation 10 true false
        [5971, 12]
        [10, 0, 4, 2],
      .prior 11080 false [10, 0, 4, 2],
      .equation 8 true false
        [5969, 10]
        [0, 4, 2],
      .prior 11079 false [0, 4, 2],
      .equation 2 true false
        [5967, 0]
        [4, 2],
      .prior 11076 false [4, 2],
      .equation 6 true false
        [5965, 4]
        [2],
      .prior 11071 false [2]]⟩,
    ⟨[
      5977, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10
    ], [5951, 11], [
      .prior 11090 false [0, 16, 14, 0, 12, 10],
      .equation 4 true false
        [5963, 2]
        [0, 16, 14, 0, 12, 10],
      .prior 11069 false [0, 16, 14, 0, 12, 10],
      .equation 2 true false
        [5961, 0]
        [16, 14, 0, 12, 10],
      .prior 11066 false [16, 14, 0, 12, 10],
      .equation 14 true false
        [5959, 16]
        [14, 0, 12, 10],
      .prior 11064 false [14, 0, 12, 10],
      .equation 12 true false
        [5957, 14]
        [0, 12, 10],
      .prior 11061 false [0, 12, 10],
      .equation 2 true false
        [5955, 0]
        [12, 10],
      .prior 11057 false [12, 10],
      .equation 10 true false
        [5953, 12]
        [10],
      .prior 11054 false [10],
      .equation 8 true false
        [5951, 10]
        []]⟩,
    ⟨[
      5977, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14
    ], [5937], [
      .prior 11091 false [0, 4, 2, 0, 16, 14],
      .prior 11050 false [0, 4, 2, 0, 16, 14],
      .equation 2 true false
        [5949, 0]
        [4, 2, 0, 16, 14],
      .prior 11047 false [4, 2, 0, 16, 14],
      .equation 6 true false
        [5947, 4]
        [2, 0, 16, 14],
      .prior 11046 false [2, 0, 16, 14],
      .equation 4 true false
        [5945, 2]
        [0, 16, 14],
      .equation 3009 false false
        []
        [3, 0, 16, 14],
      .equation 4 false false
        [5943]
        [0, 16, 14],
      .equation 2 true false
        [5943, 0]
        [16, 14],
      .equation 3008 false false
        []
        [1, 16, 14],
      .equation 2 false false
        [5941]
        [16, 14],
      .equation 14 true false
        [5941, 16]
        [14],
      .equation 3007 false false
        []
        [17, 14],
      .equation 14 false false
        [5939]
        [14],
      .equation 12 true false
        [5939, 14]
        [],
      .equation 3006 false false
        []
        [15],
      .equation 12 false false
        [5937]
        []]⟩,
    ⟨[
      5977, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2
    ], [5925], [
      .prior 11092 false [0, 12, 10, 0, 4, 2],
      .equation 2 true false
        [5937, 0]
        [12, 10, 0, 4, 2],
      .equation 3005 false false
        []
        [1, 12, 10, 0, 4, 2],
      .equation 2 false false
        [5935]
        [12, 10, 0, 4, 2],
      .equation 10 true false
        [5935, 12]
        [10, 0, 4, 2],
      .equation 3004 false false
        []
        [13, 10, 0, 4, 2],
      .equation 10 false false
        [5933]
        [10, 0, 4, 2],
      .equation 8 true false
        [5933, 10]
        [0, 4, 2],
      .equation 3003 false false
        []
        [11, 0, 4, 2],
      .equation 8 false false
        [5931]
        [0, 4, 2],
      .equation 2 true false
        [5931, 0]
        [4, 2],
      .equation 3002 false false
        []
        [1, 4, 2],
      .equation 2 false false
        [5929]
        [4, 2],
      .equation 6 true false
        [5929, 4]
        [2],
      .equation 3001 false false
        []
        [5, 2],
      .equation 6 false false
        [5927]
        [2],
      .equation 4 true false
        [5927, 2]
        [],
      .equation 3000 false false
        []
        [3],
      .equation 4 false false
        [5925]
        []]⟩,
    ⟨[
      5977, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10
    ], [5913], [
      .prior 11093 false [0, 16, 14, 0, 12, 10],
      .equation 2 true false
        [5925, 0]
        [16, 14, 0, 12, 10],
      .equation 2999 false false
        []
        [1, 16, 14, 0, 12, 10],
      .equation 2 false false
        [5923]
        [16, 14, 0, 12, 10],
      .equation 14 true false
        [5923, 16]
        [14, 0, 12, 10],
      .equation 2998 false false
        []
        [17, 14, 0, 12, 10],
      .equation 14 false false
        [5921]
        [14, 0, 12, 10],
      .equation 12 true false
        [5921, 14]
        [0, 12, 10],
      .equation 2997 false false
        []
        [15, 0, 12, 10],
      .equation 12 false false
        [5919]
        [0, 12, 10],
      .equation 2 true false
        [5919, 0]
        [12, 10],
      .equation 2996 false false
        []
        [1, 12, 10],
      .equation 2 false false
        [5917]
        [12, 10],
      .equation 10 true false
        [5917, 12]
        [10],
      .equation 2995 false false
        []
        [13, 10],
      .equation 10 false false
        [5915]
        [10],
      .equation 8 true false
        [5915, 10]
        [],
      .equation 2994 false false
        []
        [11],
      .equation 8 false false
        [5913]
        []]⟩,
    ⟨[
      5977, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14
    ], [5901], [
      .prior 11094 false [0, 4, 2, 0, 16, 14],
      .equation 2 true false
        [5913, 0]
        [4, 2, 0, 16, 14],
      .equation 2993 false false
        []
        [1, 4, 2, 0, 16, 14],
      .equation 2 false false
        [5911]
        [4, 2, 0, 16, 14],
      .equation 6 true false
        [5911, 4]
        [2, 0, 16, 14],
      .equation 2992 false false
        []
        [5, 2, 0, 16, 14],
      .equation 6 false false
        [5909]
        [2, 0, 16, 14],
      .equation 4 true false
        [5909, 2]
        [0, 16, 14],
      .equation 2991 false false
        []
        [3, 0, 16, 14],
      .equation 4 false false
        [5907]
        [0, 16, 14],
      .equation 2 true false
        [5907, 0]
        [16, 14],
      .equation 2990 false false
        []
        [1, 16, 14],
      .equation 2 false false
        [5905]
        [16, 14],
      .equation 14 true false
        [5905, 16]
        [14],
      .equation 2989 false false
        []
        [17, 14],
      .equation 14 false false
        [5903]
        [14],
      .equation 12 true false
        [5903, 14]
        [],
      .equation 2988 false false
        []
        [15],
      .equation 12 false false
        [5901]
        []]⟩,
    ⟨[
      5977, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10
    ], [5897], [
      .prior 11095 false [0, 12, 10],
      .equation 2 true false
        [5901, 0]
        [12, 10],
      .prior 11035 true [1, 12, 10],
      .equation 40 false false
        [5899, 0]
        [12, 12, 10],
      .equation 2 true false
        [5899, 0]
        [12, 12, 10],
      .prior 11031 true [1, 12, 12, 10],
      .equation 43 false false
        [5897, 0]
        [10, 0, 10, 12, 12, 10],
      .prior 11032 false [12, 12, 10],
      .prior 11033 false [12, 12, 10],
      .equation 10 true false
        [5899, 12]
        [12, 10],
      .equation 2987 true false
        []
        [12, 10],
      .prior 11036 false [12, 10],
      .equation 10 true false
        [5901, 12]
        [10],
      .equation 2987 false false
        []
        [13, 10],
      .equation 10 false false
        [5899]
        [10],
      .equation 8 true false
        [5899, 10]
        [],
      .equation 2986 false false
        []
        [11],
      .equation 8 false false
        [5897]
        []]⟩,
    ⟨[
      5977, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0
    ], [5887, 0], [
      .prior 11096 false [
        0, 4, 2, 0, 16, 14, 0
      ],
      .equation 2 true false
        [5897, 0]
        [4, 2, 0, 16, 14, 0],
      .prior 11028 false [4, 2, 0, 16, 14, 0],
      .equation 6 true false
        [5895, 4]
        [2, 0, 16, 14, 0],
      .prior 11025 false [2, 0, 16, 14, 0],
      .equation 4 true false
        [5893, 2]
        [0, 16, 14, 0],
      .equation 2983 false false
        []
        [3, 0, 16, 14, 0],
      .equation 4 false false
        [5891]
        [0, 16, 14, 0],
      .equation 2 true false
        [5891, 0]
        [16, 14, 0],
      .equation 2982 false false
        []
        [1, 16, 14, 0],
      .equation 2 false false
        [5889]
        [16, 14, 0],
      .equation 14 true false
        [5889, 16]
        [14, 0],
      .prior 11008 false [14, 0],
      .equation 12 true false
        [1693, 14]
        [0],
      .prior 10998 false [0]]⟩,
    ⟨[
      5977, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10
    ], [4863], [
      .prior 11097 false [12, 10],
      .equation 2 true false
        [5887, 0]
        [12, 10],
      .prior 10991 false [12, 10],
      .equation 10 true false
        [5885, 12]
        [10],
      .prior 10988 true [13, 10],
      .equation 139 false false
        [4863]
        [12, 10, 12, 10, 10],
      .equation 10 true false
        [4863, 12]
        [10, 12, 10, 10],
      .prior 9401 false [10, 12, 10, 10],
      .equation 8 true false
        [1433, 10]
        [12, 10, 10],
      .prior 9388 false [12, 10, 10],
      .equation 10 true false
        [1433, 12]
        [10, 10],
      .prior 9402 false [10, 10],
      .equation 8 true false
        [4863, 10]
        [10],
      .equation 2979 true false
        []
        [10],
      .prior 10989 false [10],
      .equation 8 true false
        [5885, 10]
        [],
      .prior 10987 false []]⟩,
    ⟨[
      5977, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0
    ], [5883, 0], [
      .prior 11098 false [
        0, 4, 2, 0, 16, 14, 0
      ],
      .equation 2 true false
        [4863, 0]
        [4, 2, 0, 16, 14, 0],
      .prior 9396 false [4, 2, 0, 16, 14, 0],
      .equation 6 true false
        [4861, 4]
        [2, 0, 16, 14, 0],
      .prior 9394 false [2, 0, 16, 14, 0],
      .equation 4 true false
        [4861, 2]
        [0, 16, 14, 0],
      .prior 10982 true [3, 0, 16, 14, 0],
      .equation 4 false false
        [5883]
        [0, 16, 14, 0],
      .equation 2 true false
        [5883, 0]
        [16, 14, 0],
      .prior 10981 false [16, 14, 0],
      .equation 14 true false
        [5883, 16]
        [14, 0],
      .prior 10986 false [14, 0],
      .equation 12 true false
        [5883, 14]
        [0],
      .prior 10985 false [0]]⟩,
    ⟨[
      5977, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0
    ], [1581, 1], [
      .prior 11099 false [12, 10, 0, 4, 2, 0],
      .equation 2 true false
        [5883, 0]
        [12, 10, 0, 4, 2, 0],
      .prior 10981 false [12, 10, 0, 4, 2, 0],
      .equation 10 true false
        [5883, 12]
        [10, 0, 4, 2, 0],
      .prior 10978 false [10, 0, 4, 2, 0],
      .equation 8 true false
        [1439, 10]
        [0, 4, 2, 0],
      .prior 9368 false [0, 4, 2, 0],
      .equation 2 true false
        [4857, 0]
        [4, 2, 0],
      .prior 9349 false [4, 2, 0],
      .equation 6 true false
        [4855, 4]
        [2, 0],
      .prior 9335 false [2, 0],
      .equation 4 true false
        [317, 2]
        [0],
      .prior 4596 false [0],
      .prior 10111 false [0],
      .equation 2 true false
        [1581, 0]
        []]⟩,
    ⟨[
      5977, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0
    ], [217], [
      .prior 11100 false [16, 14, 0, 12, 10, 0],
      .prior 4608 false [16, 14, 0, 12, 10, 0],
      .equation 14 true false
        [1581, 16]
        [14, 0, 12, 10, 0],
      .prior 4613 false [14, 0, 12, 10, 0],
      .equation 12 true false
        [1581, 14]
        [0, 12, 10, 0],
      .prior 4612 false [0, 12, 10, 0],
      .equation 2 true false
        [1181, 0]
        [12, 10, 0],
      .prior 3190 false [12, 10, 0],
      .equation 10 true false
        [611, 12]
        [10, 0],
      .prior 1157 false [10, 0],
      .equation 8 true false
        [215, 10]
        [0],
      .prior 549 false [0],
      .equation 2 true false
        [215, 0]
        [],
      .equation 144 true false
        []
        []]⟩,
    ⟨[
      5977, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0
    ], [39], [
      .prior 11101 false [4, 2, 0, 16, 14, 0],
      .equation 6 true false
        [217, 4]
        [2, 0, 16, 14, 0],
      .prior 556 false [2, 0, 16, 14, 0],
      .equation 4 true false
        [217, 2]
        [0, 16, 14, 0],
      .equation 145 true false
        []
        [0, 16, 14, 0],
      .equation 2 true false
        [219, 0]
        [16, 14, 0],
      .prior 569 false [16, 14, 0],
      .equation 14 true false
        [219, 16]
        [14, 0],
      .prior 578 false [14, 0],
      .equation 12 true false
        [39, 14]
        [0],
      .prior 342 false [0],
      .equation 2 true false
        [39, 0]
        [],
      .prior 140 false []]⟩,
    ⟨[
      5977, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16
    ], [1001, 16], [
      .prior 11102 false [
        12, 10, 0, 4, 2, 0, 16
      ],
      .equation 10 true false
        [39, 12]
        [10, 0, 4, 2, 0, 16],
      .prior 850 false [10, 0, 4, 2, 0, 16],
      .equation 8 true false
        [321, 10]
        [0, 4, 2, 0, 16],
      .prior 848 false [0, 4, 2, 0, 16],
      .equation 2 true false
        [321, 0]
        [4, 2, 0, 16],
      .equation 197 true false
        []
        [4, 2, 0, 16],
      .prior 840 false [4, 2, 0, 16],
      .equation 6 true false
        [321, 4]
        [2, 0, 16],
      .equation 537 true false
        []
        [2, 0, 16],
      .equation 4 true false
        [1001, 2]
        [0, 16],
      .prior 1673 false [0, 16],
      .equation 2 true false
        [1001, 0]
        [16],
      .prior 1671 false [16]]⟩,
    ⟨[
      5977, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10,
      0, 4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2,
      0, 16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14,
      0, 12, 10, 0, 4
    ], [307, 5], [
      .prior 11103 false [14, 0, 12, 10, 0, 4],
      .equation 14 true false
        [1001, 16]
        [14, 0, 12, 10, 0, 4],
      .equation 837 true false
        []
        [14, 0, 12, 10, 0, 4],
      .equation 12 true false
        [1601, 14]
        [0, 12, 10, 0, 4],
      .equation 2464 true false
        []
        [0, 12, 10, 0, 4],
      .equation 2 true false
        [4855, 0]
        [12, 10, 0, 4],
      .equation 2465 true false
        []
        [12, 10, 0, 4],
      .equation 10 true false
        [4857, 12]
        [10, 0, 4],
      .prior 9361 false [10, 0, 4],
      .equation 8 true false
        [619, 10]
        [0, 4],
      .equation 347 true false
        []
        [0, 4],
      .equation 2 true false
        [621, 0]
        [4],
      .prior 1242 false [4],
      .equation 6 true false
        [307, 4]
        []]⟩,
    ⟨[5979, 3], [309], [
      .prior 11088 true [3],
      .equation 198 false false
        [5977]
        [
          16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0,
          12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0,
          4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0,
          16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0,
          12, 10, 0, 4, 2, 0, 16, 14, 0, 12, 10, 0,
          4, 2, 0, 16, 14, 0, 12, 10, 0, 4, 2, 0,
          16, 14, 0, 12, 10, 0, 4, 2, 0, 16, 14, 0,
          12, 10, 0, 4
        ],
      .prior 11104 false [],
      .equation 190 true false
        []
        [],
      .prior 787 false []]⟩,
    ⟨[309, 3], [5979], [
      .prior 11105 true [3],
      .equation 4 false false
        [5979]
        []]⟩,
    ⟨[5977, 3], [5977, 3], [
]⟩,
    ⟨[5977, 3], [309], [
      .prior 11107 false [],
      .equation 2 true false
        [5977]
        [3],
      .equation 3026 true false
        []
        [1, 3],
      .equation 39 false false
        [5979]
        [2, 0, 2, 0],
      .equation 4 true false
        [5979, 2]
        [0, 2, 0],
      .prior 11105 false [0, 2, 0],
      .equation 2 true false
        [309, 0]
        [2, 0],
      .equation 191 true false
        []
        [2, 0],
      .equation 4 true false
        [311, 2]
        [0],
      .prior 1196 false [0],
      .equation 2 true false
        [311, 0]
        [],
      .prior 789 false [],
      .prior 787 false []]⟩,
    ⟨[309, 3], [5979], [
      .prior 11106 false []]⟩,
    ⟨[5979], [5977], [
      .prior 11109 true [],
      .prior 11108 true [3],
      .equation 4 false false
        [5977]
        []]⟩,
    ⟨[5977, 3], [309], [
      .prior 11107 false [],
      .prior 11108 false []]⟩,
    ⟨[5197, 5], [5197, 5], [
]⟩,
    ⟨[5197, 5], [5977], [
      .prior 11112 false [],
      .prior 10211 true [5],
      .prior 4408 true [3, 5],
      .prior 779 true [5, 3, 5],
      .prior 784 true [3, 5, 3, 5],
      .prior 11111 true [5, 3, 5, 3, 5],
      .equation 33 false false
        [5977]
        [],
      .prior 11087 false []]⟩,
    ⟨[5187, 11], [5187, 11], [
]⟩,
    ⟨[5187, 11], [5977], [
      .prior 11114 false [],
      .prior 10136 true [11],
      .prior 10120 true [11],
      .prior 4633 true [3, 11],
      .prior 11111 true [11, 3, 11],
      .equation 34 false false
        [5977]
        [],
      .prior 11087 false []]⟩,
    ⟨[4839, 15], [4839, 15], [
]⟩,
    ⟨[4839, 15], [5977], [
      .prior 11116 false [],
      .prior 10226 true [15],
      .prior 9508 true [15],
      .prior 4661 true [3, 15],
      .prior 11111 true [15, 3, 15],
      .equation 36 false false
        [5977]
        [],
      .prior 11087 false []]⟩,
    ⟨[5977], [5975], [
      .prior 11087 false [],
      .equation 37 true false
        [5977]
        [],
      .prior 11111 false [17, 3, 17],
      .prior 902 false [3, 17],
      .prior 11106 false [17],
      .prior 11110 false [17],
      .prior 11086 false []]⟩,
    ⟨[5977], [5975], [
      .prior 11118 false []]⟩,
    ⟨[5979], [5975], [
      .prior 11110 false [],
      .prior 11118 false []]⟩,
    ⟨[5975, 5], [5197], [
      .prior 11118 true [5],
      .prior 11113 true [5],
      .equation 6 false false
        [5197]
        []]⟩,
    ⟨[5975, 7], [5975], [
      .prior 11118 true [7],
      .prior 11110 true [7],
      .prior 11106 true [7],
      .prior 905 true [3, 7],
      .prior 11111 true [7, 3, 7],
      .equation 19 false false
        [5977]
        [],
      .prior 11087 false [],
      .prior 11119 false []]⟩,
    ⟨[5975, 11], [5187], [
      .prior 11118 true [11],
      .prior 11115 true [11],
      .equation 8 false false
        [5187]
        []]⟩,
    ⟨[5973], [4839], [
      .prior 11083 true [],
      .prior 11119 true [15],
      .prior 11117 true [15],
      .equation 12 false false
        [4839]
        []]⟩,
    ⟨[4833, 11], [5967], [
      .prior 10255 true [11],
      .equation 2457 false false
        []
        [13, 11],
      .prior 11124 true [1, 13, 11],
      .prior 11082 false [13, 11],
      .prior 11080 false [11],
      .prior 11079 false []]⟩,
    ⟨[4841, 11], [4841], [
      .prior 9315 false [],
      .prior 9316 false []]⟩,
    ⟨[5965, 11], [5965, 11], [
]⟩,
    ⟨[5965, 11], [4833], [
      .prior 11127 false [],
      .prior 11076 true [11],
      .prior 11125 true [1, 11],
      .prior 9220 true [11, 1, 11],
      .prior 10252 true [1, 11, 1, 11],
      .equation 2455 false false
        []
        [1, 11, 1, 11],
      .prior 9221 true [11, 1, 11, 1, 11],
      .equation 43 false false
        [4833]
        [],
      .prior 9218 false []]⟩,
    ⟨[4833, 11], [5967], [
      .prior 11125 false []]⟩,
    ⟨[5967], [5965], [
      .prior 11129 true [],
      .prior 11128 true [11],
      .equation 8 false false
        [5965]
        []]⟩,
    ⟨[5967], [5965], [
      .prior 11130 false []]⟩,
    ⟨[5965, 13], [5965], [
      .prior 11130 true [13],
      .prior 11125 true [13],
      .prior 10255 true [11, 13],
      .prior 11126 true [13, 11, 13],
      .equation 139 false false
        [4841]
        [12, 10],
      .equation 10 true false
        [4841, 12]
        [10],
      .prior 10255 false [10],
      .equation 8 true false
        [4833, 10]
        [],
      .prior 11125 false [],
      .prior 11078 false [],
      .prior 11131 false []]⟩,
    ⟨[4833, 10], [5965], [
      .equation 8 true false
        [4833, 10]
        [],
      .prior 11125 false [],
      .prior 11131 false []]⟩,
    ⟨[5965, 7], [5965, 7], [
]⟩,
    ⟨[5965, 7], [5965], [
      .prior 11134 false [],
      .prior 11131 true [7],
      .prior 11125 true [7],
      .prior 9218 true [11, 7],
      .prior 9327 true [11, 7],
      .equation 18 true false
        [4835, 0]
        [11, 7],
      .prior 9325 false [1, 7, 11, 7],
      .prior 9326 false [1, 7, 11, 7],
      .prior 9220 false [7, 11, 7],
      .prior 9328 true [11, 7],
      .prior 9328 true [11, 7],
      .equation 21 false false
        [4833]
        [10],
      .prior 11133 false [],
      .prior 11074 false []]⟩]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
