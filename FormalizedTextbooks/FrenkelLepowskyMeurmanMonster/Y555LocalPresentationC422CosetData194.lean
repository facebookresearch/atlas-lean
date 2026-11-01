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
def y422CosetData194 : Fin 128 → Y522RawCosetCertificate :=
  ![
    ⟨[2041, 13], [2041], [
      .equation 1058 true false
        []
        [],
      .prior 24602 false []]⟩,
    ⟨[2041, 8], [8713], [
      .equation 1 true false
        [2041, 8]
        [],
      .prior 24606 false []]⟩,
    ⟨[8713, 13], [8713, 13], [
]⟩,
    ⟨[8713, 13], [8713], [
      .prior 24834 false [],
      .prior 24606 true [13],
      .prior 24832 true [9, 13],
      .equation 11 false false
        [2041, 8]
        [],
      .prior 24833 false [],
      .prior 24157 false []]⟩,
    ⟨[2041, 5], [2041], [
      .prior 24603 false []]⟩,
    ⟨[8713, 5], [8713, 5], [
]⟩,
    ⟨[2041, 7], [1263], [
      .prior 24600 true [7],
      .prior 24597 true [7],
      .prior 5969 false [],
      .prior 21271 false []]⟩,
    ⟨[2689], [2041], [
      .prior 21216 false [],
      .prior 24597 false [],
      .prior 24600 false []]⟩,
    ⟨[8713, 7], [8713, 7], [
]⟩,
    ⟨[2041, 17], [3367], [
      .prior 24600 true [17],
      .prior 24597 true [17],
      .prior 12872 true [17],
      .equation 14 false false
        [7783]
        [],
      .prior 22120 false []]⟩,
    ⟨[8129, 17], [8713], [
      .prior 22123 true [17],
      .prior 24841 true [9, 17],
      .equation 15 false false
        [2041, 8]
        [],
      .prior 24833 false [],
      .prior 24157 false []]⟩,
    ⟨[1977, 9], [8717], [
      .prior 24828 false [],
      .prior 24830 false []]⟩,
    ⟨[8719], [8717], [
      .equation 1 true false
        [8719]
        [],
      .equation 4396 false false
        []
        [9, 9],
      .prior 24830 true [5, 9, 9],
      .prior 5639 true [9, 5, 9, 9],
      .equation 7 false false
        [1977]
        [9],
      .prior 5631 false [9],
      .prior 24843 false []]⟩,
    ⟨[8717, 13], [8721], [
      .prior 24844 true [13],
      .equation 4397 true false
        []
        []]⟩,
    ⟨[1977, 8], [8717], [
      .equation 1 true false
        [1977, 8]
        [],
      .prior 24830 false []]⟩,
    ⟨[8717, 7], [8717, 7], [
]⟩,
    ⟨[8717, 7], [8717], [
      .prior 24847 false [],
      .prior 24830 true [7],
      .prior 5636 true [9, 7],
      .prior 783 true [7, 9, 7],
      .prior 5643 true [9, 7, 9, 7],
      .equation 20 false false
        [1977]
        [8],
      .prior 24846 false [],
      .prior 24829 false []]⟩,
    ⟨[8717, 17], [8717, 17], [
]⟩,
    ⟨[8717, 17], [8717], [
      .prior 24849 false [],
      .prior 24830 true [17],
      .prior 5650 true [9, 17],
      .equation 15 false false
        [1977, 8]
        [],
      .prior 24846 false [],
      .prior 24829 false []]⟩,
    ⟨[1977, 3], [2811], [
      .prior 10650 false [],
      .prior 21936 false []]⟩,
    ⟨[9181, 3], [8717], [
      .prior 23837 true [3],
      .prior 24851 true [9, 3],
      .equation 5 false false
        [1977]
        [8],
      .prior 24846 false [],
      .prior 24829 false []]⟩,
    ⟨[8717, 3], [9181], [
      .prior 24852 true [3],
      .equation 4 false false
        [9181]
        []]⟩,
    ⟨[1977, 13], [2607], [
      .prior 21215 false [],
      .prior 22106 false []]⟩,
    ⟨[2607, 9], [2607, 9], [
]⟩,
    ⟨[8721], [8721], [
]⟩,
    ⟨[2607, 9], [8721], [
      .prior 24855 false [],
      .prior 24854 true [9],
      .equation 11 false false
        [1977, 8]
        [12],
      .prior 24846 false [12],
      .equation 10 true false
        [8717, 12]
        [],
      .prior 24845 false [],
      .prior 24856 false []]⟩,
    ⟨[8721, 9], [2607], [
      .prior 24857 true [9],
      .equation 1 false false
        [2607]
        []]⟩,
    ⟨[625, 9], [625], [
      .prior 1255 false [],
      .prior 1257 false []]⟩,
    ⟨[2607, 9], [8721], [
      .prior 24855 false [],
      .prior 24857 false []]⟩,
    ⟨[8723], [8721], [
      .equation 1 true false
        [8723]
        [],
      .equation 4398 false false
        []
        [9, 9],
      .prior 24857 true [7, 9, 9],
      .prior 22106 true [9, 7, 9, 9],
      .prior 20725 true [9, 7, 9, 9],
      .prior 24859 true [7, 9, 7, 9, 9],
      .equation 20 false false
        [625, 6]
        [9],
      .equation 17 true false
        [625, 6]
        [9],
      .prior 20725 false [9],
      .prior 22106 false [9],
      .prior 23076 false [9],
      .prior 24860 false []]⟩,
    ⟨[8721, 1], [8725], [
      .prior 24861 true [1],
      .equation 4399 true false
        []
        []]⟩,
    ⟨[7793, 5], [5301], [
      .prior 12890 true [5],
      .equation 28 false false
        [7791, 4]
        [10],
      .equation 6 true false
        [7791, 4]
        [10],
      .prior 23731 false [10],
      .equation 8 true false
        [5299, 10]
        [],
      .equation 2687 true false
        []
        [],
      .prior 13737 false []]⟩,
    ⟨[5301, 5], [7793], [
      .prior 24863 true [5],
      .equation 6 false false
        [7793]
        []]⟩,
    ⟨[7795], [6265], [
      .prior 22345 false [],
      .prior 22346 false []]⟩,
    ⟨[5301, 15], [5303], [
      .equation 2688 true false
        []
        []]⟩,
    ⟨[7797], [5303], [
      .equation 12 true false
        [7797]
        [],
      .prior 22348 true [15, 15],
      .prior 24865 true [5, 15, 15],
      .equation 3934 false false
        []
        [5, 15, 15],
      .equation 30 false false
        [7793, 4]
        [15],
      .equation 6 true false
        [7793, 4]
        [15],
      .prior 24863 false [15],
      .prior 13737 false [15],
      .prior 24866 false []]⟩,
    ⟨[5303, 13], [7799], [
      .prior 24867 true [13],
      .equation 3936 true false
        []
        []]⟩,
    ⟨[7797], [5303], [
      .prior 24867 false []]⟩,
    ⟨[5303, 1], [5303], [
      .prior 24867 true [1],
      .prior 23088 false [],
      .prior 24869 false []]⟩,
    ⟨[5303, 17], [13215], [
      .prior 24867 true [17],
      .prior 23725 false []]⟩,
    ⟨[6265], [5305], [
      .prior 24865 true [],
      .prior 12894 true [],
      .prior 24869 false [5],
      .equation 2689 true false
        []
        []]⟩,
    ⟨[5305, 1], [5305], [
      .prior 24872 true [1],
      .equation 3170 true false
        []
        [],
      .prior 22350 false [],
      .prior 24872 false []]⟩,
    ⟨[5305, 3], [6019], [
      .prior 24872 true [3],
      .prior 22346 true [3],
      .equation 3171 true false
        []
        [],
      .prior 23755 false []]⟩,
    ⟨[5305, 15], [7793], [
      .prior 24872 true [15],
      .prior 22347 false []]⟩,
    ⟨[5305, 11], [10045], [
      .prior 24872 true [11],
      .prior 22346 true [11],
      .prior 22344 true [11],
      .prior 14841 true [11],
      .equation 8 false false
        [10045]
        []]⟩,
    ⟨[5305, 17], [10909], [
      .prior 24872 true [17],
      .prior 22776 false []]⟩,
    ⟨[6265], [5305], [
      .prior 24872 false []]⟩,
    ⟨[8451], [5307], [
      .prior 22349 true [],
      .prior 24878 false [13],
      .equation 2690 true false
        []
        []]⟩,
    ⟨[5307, 5], [7799], [
      .prior 24879 true [5],
      .prior 13241 false [],
      .prior 23094 false []]⟩,
    ⟨[11445], [6021], [
      .prior 23164 false [],
      .prior 23756 false []]⟩,
    ⟨[5307, 3], [6021], [
      .prior 24879 true [3],
      .prior 23050 false [],
      .prior 24881 false []]⟩,
    ⟨[5307, 11], [8069], [
      .prior 24879 true [11],
      .prior 23119 false []]⟩,
    ⟨[8451], [5307], [
      .prior 24879 false []]⟩,
    ⟨[5309], [1473], [
      .equation 2691 false false
        []
        [],
      .prior 24884 true [7],
      .prior 14271 false [],
      .prior 21475 false []]⟩,
    ⟨[5315, 15], [247, 15], [
      .equation 2694 false false
        []
        [15],
      .equation 2693 false false
        []
        [11, 15],
      .equation 2692 false false
        []
        [3, 11, 15],
      .prior 24885 false [1, 3, 11, 15],
      .prior 10354 false [3, 11, 15],
      .prior 4443 false [11, 15],
      .prior 21157 false [11, 15],
      .prior 12051 false [15]]⟩,
    ⟨[5321, 7], [1921], [
      .equation 2697 false false
        []
        [7],
      .equation 2696 false false
        []
        [13, 7],
      .equation 2695 false false
        []
        [5, 13, 7],
      .prior 24886 false [5, 13, 7],
      .prior 650 false [5, 13, 7],
      .prior 11813 false [13, 7],
      .prior 20671 false [13, 7],
      .prior 758 false [7],
      .prior 22252 false []]⟩,
    ⟨[5327, 11], [1959], [
      .equation 2700 false false
        []
        [11],
      .equation 2699 false false
        []
        [3, 11],
      .equation 2698 false false
        []
        [1, 3, 11],
      .prior 24887 false [1, 3, 11],
      .equation 998 true false
        []
        [3, 11],
      .prior 21634 false [11],
      .prior 5589 false []]⟩,
    ⟨[2619], [5333, 13], [
      .prior 22085 true [],
      .equation 1347 false false
        []
        [],
      .prior 23887 true [13],
      .prior 21788 true [13],
      .prior 21787 true [5, 13],
      .prior 21505 true [5, 13],
      .prior 24888 true [15, 5, 13],
      .equation 2701 true false
        []
        [15, 5, 13],
      .equation 2702 true false
        []
        [5, 13],
      .equation 2703 true false
        []
        [13]]⟩,
    ⟨[2715], [5341], [
      .prior 6974 true [],
      .prior 22084 true [3],
      .prior 22086 true [1, 3],
      .prior 24889 false [7, 1, 3],
      .equation 2704 true false
        []
        [7, 1, 3],
      .equation 2705 true false
        []
        [1, 3],
      .equation 2706 true false
        []
        [3],
      .equation 2707 true false
        []
        []]⟩,
    ⟨[1837], [5347], [
      .prior 5494 true [],
      .prior 22065 true [5],
      .prior 6694 true [5],
      .prior 22646 true [15, 5],
      .prior 7150 true [15, 5],
      .prior 24890 false [11, 15, 5],
      .equation 2708 true false
        []
        [15, 5],
      .equation 2709 true false
        []
        [5],
      .equation 2710 true false
        []
        []]⟩,
    ⟨[5353], [1841], [
      .equation 2713 false false
        []
        [],
      .equation 2712 false false
        []
        [1],
      .equation 2711 false false
        []
        [7, 1],
      .prior 24891 true [13, 7, 1],
      .equation 956 true false
        []
        [7, 1],
      .prior 5510 false [1],
      .equation 957 true false
        []
        []]⟩,
    ⟨[5359], [2453], [
      .equation 2716 false false
        []
        [],
      .equation 2715 false false
        []
        [15],
      .equation 2714 false false
        []
        [11, 15],
      .prior 24892 false [3, 11, 15],
      .prior 5531 false [11, 15],
      .prior 7462 false [15],
      .prior 21854 false [15],
      .prior 6691 false []]⟩,
    ⟨[5365, 1], [2453, 1], [
      .equation 2719 false false
        []
        [1],
      .equation 2718 false false
        []
        [7, 1],
      .equation 2717 false false
        []
        [13, 7, 1],
      .prior 24893 false [5, 13, 7, 1],
      .prior 21855 false [13, 7, 1],
      .prior 21858 false [7, 1],
      .prior 21856 false [1]]⟩,
    ⟨[5371, 15], [1843], [
      .equation 2722 false false
        []
        [15],
      .equation 2721 false false
        []
        [11, 15],
      .equation 2720 false false
        []
        [3, 11, 15],
      .prior 24894 false [3, 11, 15],
      .equation 1264 true false
        []
        [3, 11, 15],
      .prior 21860 false [3, 11, 15],
      .prior 7773 false [11, 15],
      .prior 22073 false [11, 15],
      .prior 21857 false [15],
      .equation 958 true false
        []
        []]⟩,
    ⟨[5377, 7], [2465], [
      .equation 2725 false false
        []
        [7],
      .equation 2724 false false
        []
        [13, 7],
      .equation 2723 false false
        []
        [5, 13, 7],
      .prior 24895 false [5, 13, 7],
      .prior 22000 false [5, 13, 7],
      .prior 5522 false [13, 7],
      .prior 7130 false [7],
      .prior 22067 false [7],
      .prior 22069 false []]⟩,
    ⟨[4339], [5383, 3], [
      .prior 8522 true [],
      .prior 8422 true [3],
      .prior 22070 true [1, 3],
      .prior 24896 true [9, 1, 3],
      .equation 2726 true false
        []
        [9, 1, 3],
      .equation 2727 true false
        []
        [1, 3],
      .equation 2728 true false
        []
        [3]]⟩,
    ⟨[5387], [2565], [
      .equation 2730 false false
        []
        [],
      .equation 2729 false false
        []
        [11],
      .prior 24897 true [11],
      .prior 8526 false []]⟩,
    ⟨[2565, 15], [5389], [
      .prior 24898 true [15],
      .equation 2731 true false
        []
        []]⟩,
    ⟨[5303, 13], [7799], [
      .prior 24868 false []]⟩,
    ⟨[8447, 13], [5301], [
      .prior 23093 true [13],
      .prior 24900 true [15, 13],
      .equation 138 false false
        [5303]
        [14],
      .equation 12 true false
        [5303, 14]
        [],
      .prior 10679 false [],
      .prior 13737 false []]⟩,
    ⟨[5301, 13], [8447], [
      .prior 24901 true [13],
      .equation 10 false false
        [8447]
        []]⟩,
    ⟨[7799, 10], [13217], [
      .equation 8 true false
        [7799, 10]
        [],
      .prior 23931 false []]⟩,
    ⟨[8181], [8181], [
]⟩,
    ⟨[7799, 3], [7805], [
      .prior 23095 true [3],
      .equation 3939 true false
        []
        []]⟩,
    ⟨[7807, 3], [13217], [
      .equation 3940 false false
        []
        [3],
      .prior 24905 true [11, 3],
      .equation 34 false false
        [7799]
        [10],
      .prior 24903 false [],
      .prior 23117 false []]⟩,
    ⟨[13217, 3], [16573], [
      .prior 23630 false []]⟩,
    ⟨[16571], [13217], [
      .prior 23627 false []]⟩,
    ⟨[16573], [7807], [
      .prior 24907 true [],
      .prior 24906 true [3],
      .equation 4 false false
        [7807]
        []]⟩,
    ⟨[16575], [7805], [
      .equation 8324 false false
        []
        [],
      .prior 24909 false [11],
      .prior 12897 false []]⟩,
    ⟨[7805, 15], [16577], [
      .prior 24910 true [15],
      .equation 8325 true false
        []
        []]⟩,
    ⟨[8447, 3], [16577], [
      .prior 14280 true [3],
      .prior 23093 true [3],
      .equation 12 false false
        [7799, 14]
        [3],
      .equation 36 true false
        [7799]
        [14, 3],
      .prior 24905 false [15, 3, 3],
      .prior 24911 false [3, 3],
      .equation 4 false false
        [16577]
        []]⟩,
    ⟨[7805, 14], [16577], [
      .equation 12 true false
        [7805, 14]
        [],
      .prior 24911 false []]⟩,
    ⟨[16577], [16577], [
]⟩,
    ⟨[7809, 11], [16577], [
      .equation 3941 false false
        []
        [11],
      .equation 3940 false false
        []
        [15, 11],
      .equation 136 false false
        [7805]
        [14],
      .prior 24913 false [],
      .prior 24914 false []]⟩,
    ⟨[7809], [6897], [
      .equation 4 true false
        [7809]
        [],
      .equation 3941 false false
        []
        [3, 3],
      .equation 36 false false
        [7807, 2]
        [14, 3],
      .equation 4 true false
        [7807, 2]
        [14, 3],
      .prior 24906 false [14, 3],
      .equation 12 true false
        [13217, 14]
        [3],
      .prior 17264 false [3],
      .prior 23625 false [3],
      .prior 24792 false []]⟩,
    ⟨[7809], [6897], [
      .prior 24916 false []]⟩,
    ⟨[6897, 7], [6897], [
      .prior 24916 true [7],
      .equation 3941 false false
        []
        [7],
      .prior 13355 true [15, 7],
      .prior 13354 true [15, 7],
      .equation 23 false false
        [7807]
        [14],
      .equation 12 true false
        [7807, 14]
        [],
      .equation 3941 true false
        []
        [],
      .prior 24917 false []]⟩,
    ⟨[6897, 11], [16577], [
      .prior 24916 true [11],
      .prior 24915 false []]⟩,
    ⟨[7815, 1], [1917, 1], [
      .equation 3944 false false
        []
        [1],
      .equation 3943 false false
        []
        [7, 1],
      .equation 3942 false false
        []
        [13, 7, 1],
      .prior 24917 false [5, 13, 7, 1],
      .equation 3486 true false
        []
        [13, 7, 1],
      .equation 3487 true false
        []
        [7, 1],
      .equation 3488 true false
        []
        [1],
      .prior 24439 false [1]]⟩,
    ⟨[7821, 15], [2793], [
      .equation 3947 false false
        []
        [15],
      .equation 3946 false false
        []
        [11, 15],
      .equation 3945 false false
        []
        [3, 11, 15],
      .prior 24920 false [3, 11, 15],
      .prior 5567 false [3, 11, 15],
      .prior 24259 false [11, 15],
      .prior 24677 false [11, 15],
      .equation 1434 true false
        []
        [15],
      .prior 24478 false [15],
      .prior 24479 false []]⟩,
    ⟨[7827, 7], [2257], [
      .equation 3950 false false
        []
        [7],
      .equation 3949 false false
        []
        [13, 7],
      .equation 3948 false false
        []
        [5, 13, 7],
      .prior 24921 false [5, 13, 7],
      .prior 24477 false [13, 7],
      .prior 24408 false [7],
      .prior 24428 false [7],
      .prior 6601 false []]⟩,
    ⟨[7829], [2257], [
      .equation 3951 false false
        []
        [],
      .prior 24922 false []]⟩,
    ⟨[2257, 9], [17211], [
      .prior 24923 true [9],
      .prior 22203 false []]⟩,
    ⟨[7831], [2259], [
      .equation 3952 false false
        []
        [],
      .prior 24923 false [1],
      .equation 1166 true false
        []
        []]⟩,
    ⟨[2259, 9], [17213], [
      .prior 24925 true [9],
      .prior 23101 true [9],
      .equation 1 false false
        [17213]
        []]⟩,
    ⟨[7831], [2259], [
      .prior 24925 false []]⟩,
    ⟨[7833], [2375], [
      .equation 3953 false false
        []
        [],
      .prior 24927 false [3],
      .prior 24421 false []]⟩,
    ⟨[2375, 9], [17215], [
      .prior 24928 true [9],
      .prior 23102 true [9],
      .equation 1 false false
        [17215]
        []]⟩,
    ⟨[7833], [2375], [
      .prior 24928 false []]⟩,
    ⟨[7835], [2375], [
      .equation 3954 false false
        []
        [],
      .prior 24930 false [11],
      .prior 21661 false []]⟩,
    ⟨[17217], [17215], [
      .equation 1 true false
        [17217]
        [],
      .prior 23103 false [9],
      .prior 24931 false [9],
      .prior 24929 false []]⟩,
    ⟨[7837], [2373], [
      .equation 3955 false false
        []
        [],
      .prior 24931 false [15],
      .prior 6456 false []]⟩,
    ⟨[2373, 9], [17219], [
      .prior 24933 true [9],
      .prior 23105 true [9],
      .equation 1 false false
        [17219]
        []]⟩,
    ⟨[7837], [2373], [
      .prior 24933 false []]⟩,
    ⟨[7839], [1967], [
      .equation 3956 false false
        []
        [],
      .prior 24935 false [5],
      .prior 21652 false []]⟩,
    ⟨[1967, 9], [17221], [
      .prior 24936 true [9],
      .prior 23106 true [9],
      .equation 1 false false
        [17221]
        []]⟩,
    ⟨[7839], [1967], [
      .prior 24936 false []]⟩,
    ⟨[7841], [3521], [
      .equation 3957 false false
        []
        [],
      .prior 24938 false [13],
      .prior 10944 false [],
      .prior 22074 false []]⟩,
    ⟨[17223], [9189], [
      .equation 1 true false
        [17223]
        [],
      .equation 8648 false false
        []
        [9, 9],
      .equation 11 false false
        [17221, 8]
        [12, 9],
      .equation 1 true false
        [17221, 8]
        [12, 9],
      .prior 23106 false [12, 9],
      .equation 10 true false
        [7839, 12]
        [9],
      .equation 3957 true false
        []
        [9],
      .prior 24939 false [9],
      .prior 24703 false []]⟩,
    ⟨[17223], [9189], [
      .prior 24940 false []]⟩,
    ⟨[17225], [9189], [
      .equation 8649 false false
        []
        [],
      .prior 24941 false [7],
      .prior 24711 false []]⟩,
    ⟨[9189, 1], [17227], [
      .prior 24942 true [1],
      .equation 8650 true false
        []
        []]⟩,
    ⟨[7847, 11], [623, 11], [
      .equation 3960 false false
        []
        [11],
      .equation 3959 false false
        []
        [3, 11],
      .equation 3958 false false
        []
        [1, 3, 11],
      .prior 24939 false [7, 1, 3, 11],
      .prior 21811 false [1, 3, 11],
      .prior 3415 false [3, 11],
      .prior 3572 false [3, 11],
      .prior 3408 false [11],
      .prior 21539 false [11]]⟩,
    ⟨[7853, 13], [1353], [
      .equation 3963 false false
        []
        [13],
      .equation 3962 false false
        []
        [5, 13],
      .equation 3961 false false
        []
        [15, 5, 13],
      .prior 24944 false [15, 5, 13],
      .prior 10984 false [15, 5, 13],
      .prior 21578 false [15, 5, 13],
      .prior 9012 false [5, 13],
      .equation 2403 true false
        []
        [13],
      .prior 9060 false []]⟩,
    ⟨[7859, 3], [1353], [
      .equation 3966 false false
        []
        [3],
      .equation 3965 false false
        []
        [1, 3],
      .equation 3964 false false
        []
        [7, 1, 3],
      .prior 24945 false [7, 1, 3],
      .prior 21550 false [1, 3],
      .prior 4142 false [3],
      .prior 4144 false []]⟩,
    ⟨[4857], [7865, 5], [
      .prior 9353 true [],
      .prior 869 true [5],
      .prior 21551 true [15, 5],
      .equation 714 false false
        []
        [15, 5],
      .prior 24946 true [11, 15, 5],
      .equation 3967 true false
        []
        [11, 15, 5],
      .equation 3968 true false
        []
        [15, 5],
      .equation 3969 true false
        []
        [5]]⟩,
    ⟨[2147], [7873], [
      .prior 6145 true [],
      .prior 6152 true [1],
      .prior 9361 true [7, 1],
      .prior 24947 false [13, 7, 1],
      .equation 3970 true false
        []
        [13, 7, 1],
      .equation 3971 true false
        []
        [7, 1],
      .equation 3972 true false
        []
        [1],
      .equation 3973 true false
        []
        []]⟩,
    ⟨[1707], [7879], [
      .prior 5436 true [],
      .prior 6140 true [15],
      .prior 6130 true [11, 15],
      .prior 24948 false [3, 11, 15],
      .equation 3974 true false
        []
        [11, 15],
      .equation 3975 true false
        []
        [15],
      .equation 3976 true false
        []
        []]⟩,
    ⟨[7885], [223], [
      .equation 3979 false false
        []
        [],
      .equation 3978 false false
        []
        [7],
      .equation 3977 false false
        []
        [13, 7],
      .prior 24949 true [5, 13, 7],
      .prior 5113 false [13, 7],
      .prior 5118 false [7],
      .prior 5115 false []]⟩,
    ⟨[7891], [2135], [
      .equation 3982 false false
        []
        [],
      .equation 3981 false false
        []
        [11],
      .equation 3980 false false
        []
        [3, 11],
      .prior 24950 false [1, 3, 11],
      .prior 1712 false [3, 11],
      .prior 6042 false [11],
      .prior 6051 false []]⟩,
    ⟨[7897, 7], [4599, 7], [
      .equation 3985 false false
        []
        [7],
      .equation 3984 false false
        []
        [13, 7],
      .equation 3983 false false
        []
        [5, 13, 7],
      .prior 24951 false [15, 5, 13, 7],
      .equation 2336 true false
        []
        [5, 13, 7],
      .prior 8795 false [13, 7],
      .prior 8803 false [7]]⟩,
    ⟨[7899], [2143], [
      .equation 3986 false false
        []
        [],
      .prior 24952 false [],
      .prior 8797 false []]⟩,
    ⟨[2143, 9], [7901], [
      .prior 24953 true [9],
      .equation 3987 true false
        []
        []]⟩,
    ⟨[7807], [6895], [
      .prior 12898 true [],
      .prior 24917 false [15],
      .prior 11690 false []]⟩,
    ⟨[7807], [6895], [
      .prior 24955 false []]⟩,
    ⟨[6895, 7], [6895], [
      .prior 24955 true [7],
      .prior 13355 false [],
      .prior 24956 false []]⟩,
    ⟨[6895, 3], [13217], [
      .prior 24955 true [3],
      .prior 24906 false []]⟩,
    ⟨[7805], [6893], [
      .prior 12897 true [],
      .prior 24956 false [11],
      .prior 11689 false []]⟩]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
