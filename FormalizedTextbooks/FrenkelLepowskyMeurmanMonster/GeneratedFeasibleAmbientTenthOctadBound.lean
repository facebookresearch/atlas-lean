/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthPairData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthPacketNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneCanonicalShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder

/-! Every octad row of the Tenth prototype has absolute value at most `1/4`.

The octad rows are the octad triality of the incoming octad blocks, whose entries are the
explicit root-two packet coefficients. Each octad block receives packet entries of total absolute
numerator at most 32 (over 16), located by a checked inverted list. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
-- The packet coordinate formula unfolds the complete root-two packet sum.
set_option maxRecDepth 10000

/-- The packet numbers whose incoming label lies in each octad block, in blocks of 64 octads. -/
def generatedFeasibleAmbientTenthOctadPacketData : Fin 12 → Fin 64 → List (Fin 4136) :=
  ![![[270, 1200, 1424], [224, 2850], [1362, 1630, 1904, 2230, 3479, 3800], [242, 786, 816,
      3229, 3329, 3623], [213, 2845], [1345, 1486, 1792, 2440, 3464, 3974], [235, 1058, 1088,
      3161, 3326, 3555], [604, 1971, 2774, 2834, 2876, 2936, 3290, 3358, 3376, 3444], [2, 1296,
      1401, 2193, 4101], [1193, 1417], [1784, 1985], [1494, 2001], [1618, 1776], [1502, 1916],
      [227, 3784, 3820], [228, 2246, 2338], [257, 1660], [258, 1874], [1506, 1920], [1614,
      1772], [252, 1520], [251, 1758], [1908, 2002], [1626, 1986], [218, 2364, 2456], [217,
      3922, 3958], [1361, 1634, 1900, 2348, 3341, 3938], [214, 2968], [1331, 2016], [210, 1226,
      2058, 2813, 2967, 3253, 3423], [559, 1376, 1498, 1622, 1780, 1912], [248, 639, 1251,
      2758, 2818, 2892, 2952], [1346, 1490, 1788, 2322, 3346, 3836], [223, 2983], [290, 1452,
      1653, 2068, 3077, 3175], [902, 1101, 3410, 3478, 3900, 3992], [1712, 2878, 3446, 3521],
      [293, 1677, 2211, 2498, 3196], [356, 1856, 3589, 3669, 4084], [1565, 2877, 3128, 3445],
      [743, 1004, 2385, 2421, 3409, 3477], [353, 1825, 1880, 2061, 2684, 3550], [2304, 2401],
      [1809, 1864], [1840, 3637], [1817, 2582], [1460, 3713], [1693, 2530], [1468, 1669],
      [3853, 3884], [340, 1412, 1728, 2565], [746, 1428], [418, 1805, 3976], [], [], [386,
      1472, 2437], [852, 1405], [320, 1421, 1549, 3730], [2894, 3653], [1464, 3061], [], [865,
      1456, 2052, 2288, 3093, 3390], [], [768, 1821, 2045, 2700, 3389, 3869]], ![[2514, 2893],
      [1813, 2668], [294, 1569, 3144, 3654, 4135], [1852, 2897, 3481, 3605], [352, 1736, 1937,
      2050, 2616, 3610], [764, 983, 3393, 3461, 3781, 3873], [861, 1142, 2248, 2284, 3394,
      3462], [289, 1541, 1596, 2043, 3009, 3235], [1681, 2898, 3212, 3482], [357, 1708, 2160,
      2513, 3537], [319, 1410, 1697, 2566], [1124, 1426], [], [419, 1949, 2264], [385, 1584,
      3765], [], [1018, 1403], [341, 1419, 1836, 3729], [1752, 1953], [3857, 3888], [1553,
      3638], [1592, 2581], [1941, 3714], [1724, 2529], [2300, 2397], [1525, 1580], [1008, 1933,
      2066, 2381, 2632, 3405], [], [1588, 3041], [2497, 2881], [1945, 2648], [2882, 3670],
      [1105, 1600, 2059, 3025, 3406, 3904], [], [243, 1560, 1718, 2318, 3342, 3840], [965,
      1191, 1341, 2646, 3020, 3448], [645, 1228, 1349, 2060, 2101, 2814, 2896, 3254, 3480,
      4065], [261, 2178, 2552, 3724, 4118], [1253, 1366, 2177, 2757, 2817, 3427, 3495, 4117],
      [231, 563, 1532, 1648, 1746, 1886, 1967, 2102, 2476, 3158, 3202, 3532, 3576, 3672, 4066],
      [234, 1672, 1862, 2352, 3345, 3934], [693, 919, 1358, 2706, 3080, 3463], [1688, 2368],
      [1846, 3918], [1870, 1997, 3640, 4034], [1664, 1981, 2134, 2508], [1065, 4033], [1044,
      2133], [], [], [825, 2117], [804, 4049], [1544, 3824], [1734, 2334], [], [], [1762, 1982,
      2118, 2492], [1516, 1998, 3656, 4050], [23, 1350, 2044, 2830, 2880, 3362, 3372], [185,
      1372, 2012], [1380, 2849], [1054, 1084, 1342, 2630, 3004, 3330], [1335, 2846], [782, 812,
      1357, 2690, 3064, 3325]], ![[106, 661, 1365, 2773, 2833, 3289, 3357], [275, 608, 1327,
      2614, 2722, 2988, 3096], [933, 936], [3530, 4068], [2180, 3054], [3018, 3176], [2944,
      3298], [128], [2782, 2928, 3749, 4036], [132, 667], [2238, 3792], [129, 789, 2975, 3925,
      4052], [], [133, 2960], [1262, 2448], [2144, 2325, 2986, 3966], [137], [136, 1070, 3002],
      [456, 2605], [749, 998], [451, 3238, 3496], [561, 3209], [735, 2429], [858, 3862], [894,
      3984], [1110, 2394], [452], [455, 2214, 3193, 3688], [2213, 3866], [872, 2681], [2256,
      3739], [], [753, 2697], [557, 2390, 2665, 3773], [8, 3929], [1074, 3557], [], [71, 1265,
      2196, 3514], [673, 3297], [957, 1183], [1049, 2329, 2781, 3750], [], [3086, 3116], [2096,
      3582], [3034, 4112], [696, 1173], [], [408, 2943], [2464, 3950], [404, 1061, 2128, 2341,
      2927], [2112, 2593, 2734, 2976], [2959, 3245], [409, 619], [405], [1310, 3808], [2222,
      3102, 3941, 4020], [412], [413, 830, 3070], [166, 2540, 3149, 4130], [1144, 2621], [161],
      [2378, 4129], [1025, 2637], [2591, 4000]], ![[609, 2413, 2653, 3878], [], [162, 3170,
      3564], [165, 2713], [605, 3133], [726, 1021], [870, 3850], [1134, 2272], [1098, 2406],
      [975, 3757], [283, 2313], [], [834, 3617], [346, 1313, 3598, 4096], [777, 2594, 2733,
      3913], [625, 3246], [], [685, 911], [432, 1379, 1510, 1610, 1768, 1924, 2019], [489,
      2935], [500, 2920], [546, 607, 1328], [534, 704, 792, 1896], [533, 837, 925, 1638],
      [504], [503], [493], [494], [527, 944, 1032, 1796], [528, 1077, 1165, 1482], [499, 2797],
      [524], [486, 556, 1968], [490, 2802], [], [1801, 2716], [1476, 3109], [], [1112, 1152,
      1448, 3685], [110], [142], [990, 1030, 1829, 2482], [1957, 2600], [], [], [1576, 2993],
      [718, 758, 1929, 3686], [109], [143], [840, 880, 1604, 2481], [1332, 2798], [1324, 2015,
      2662, 2674, 3036, 3048], [560, 1375], [1383, 2801], [1215, 1279], [382, 2149, 4017],
      [461, 1222, 1286], [611, 1964, 2150, 2524, 3624, 4018], [126], [], [1958, 2994], [717,
      757, 1930, 4060], [838, 926, 1637, 1972], [1221, 1285, 1509, 1609]], ![[399], [1078,
      1166, 1481, 2023], [], [381, 585, 649, 2661, 2673], [569, 633, 1219, 1283], [], [989,
      1029, 1830, 2088], [], [1802, 3110], [127], [170, 2918, 4109], [], [], [2917, 4110],
      [2560, 2784], [2125, 2377], [186, 844, 1159], [2622, 3088], [190, 2255, 3056, 3908],
      [587, 2126, 3150, 3648], [187, 725, 1022], [571, 2110, 3584, 3664], [191, 2414, 2654,
      3877], [2109, 2280], [2638, 3072], [], [2141, 3401], [195, 2142, 3402], [194, 3279,
      3632], [], [], [425, 2810], [421], [2794, 2916, 3646, 4127], [], [], [3152, 3678], [2558,
      2676], [429], [428, 1174, 2640], [2447, 2522, 2608, 3844], [1314, 2314], [829, 1040],
      [2624, 3618], [305, 1307, 2573, 3597], [420, 686, 2853, 3662, 3791], [2372, 3914], [2826,
      3368], [424, 679], [778, 808], [2854, 2856, 3661, 4076], [391, 2825], [], [], [387],
      [2221, 2521, 3101, 3942], [1316, 2344], [3069, 3167], [833, 1036], [326, 1309, 2574,
      3136], [396], [395, 711, 3085], [3581, 3677], [2557, 3033]], ![[], [2809, 3419], [1062,
      1092], [2342, 3816], [388, 1184, 2793, 3645, 3949], [392, 621], [], [2857, 4093], [206,
      2576, 2735], [207, 2858, 4094], [], [199], [], [203, 3134], [580, 2714], [1026, 3169],
      [596, 2996], [], [198], [848, 3615], [202, 3600], [736, 1133, 2484, 3263, 3758, 3983],
      [869, 1000, 2308, 2405, 3386, 4058], [], [], [169, 772, 1097, 3385, 3849, 3880, 4057],
      [460, 857, 1012, 2093, 2296, 2393, 3398], [], [], [760, 1109, 2094, 3397, 3861, 3892],
      [893, 976, 2271, 2430, 3264, 3680], [466, 3210], [754, 3237], [], [462], [584, 2606],
      [1120, 3547], [568, 3104], [467, 3524], [463], [], [], [470, 2186, 2869], [471, 2736,
      3716], [2185, 2870], [], [2821, 3431], [1050, 1080], [145, 958, 2463, 2506, 2805], [2330,
      3828], [149, 631], [152], [153, 934, 2708], [2474, 3204], [2656, 3722], [], [2356, 2724,
      3630, 3807], [1266, 3930], [2692, 3558], [800, 1069], [30, 1259, 3513, 3705], [2203,
      2490, 2842, 2868], [], [148, 2837]], ![[], [144], [2360, 3926], [111, 912, 2237, 2489,
      2841], [2838, 3380], [115, 669], [790, 820], [2326, 2985, 3629, 3965], [1268, 3832],
      [796, 1073], [3001, 3227], [51, 1261, 3220, 3706], [], [2473, 3529], [3053, 3721], [119],
      [120, 951, 3017], [116, 2822], [], [112], [2152, 2505, 2806, 2904], [], [], [483, 2532,
      3280], [482, 3413, 4010], [3414, 4009], [], [2682, 3028], [3865, 4041], [583, 2500, 3194,
      4042], [479, 2292, 3044, 3999], [475, 887, 1116], [478, 2389, 2666, 3774], [599, 2516,
      3540, 4026], [2698, 3012], [474, 750, 997], [3896, 4025], [2783, 3732], [2170, 2906], [],
      [], [459, 2169, 2905], [1526, 3854], [1942, 4088], [1554, 4012], [], [402, 1954, 2402],
      [901, 1102, 2386, 2422, 3256, 3324], [2760, 4044], [1946, 3042], [336, 2586, 3363], [333,
      1751, 1934, 2065, 3026, 3184], [1682, 2744, 3312, 3606], [311, 866, 1542, 3344, 3609,
      3870], [968, 1938, 2049, 2263, 3010, 3287], [], [316, 1570, 3538, 3741, 4028], [360,
      1017], [2279, 2438], [1767, 1950], [1151, 1425], [297, 1409, 1698, 2172], [269, 1493],
      [1501, 2333]], ![[1617, 3799], [239], [1873, 2020], [643, 1196, 1420, 2006], [45, 1404,
      1741, 1889, 1990], [781, 1629, 2455, 3162], [1053, 1485, 3230, 3815], [1, 581, 1292,
      3141, 3217], [694, 1633, 2317, 3504], [597, 1254], [1247, 1989], [123, 659, 1497, 1621,
      2005], [966, 1489, 3572, 3933], [1613, 3917], [1505, 2471], [1757, 1975], [264, 1625],
      [246], [247, 1559, 1845], [265, 1869, 3747, 4121], [943, 2548], [1066, 4122], [3921,
      3957], [1176, 1717, 2705, 3937], [1232, 2064, 3157, 3201], [105], [1225, 1745, 1885,
      2057], [904, 1861, 2321, 2645], [1194, 1418, 2613, 2721], [24, 1402, 2048], [1057, 1575,
      2229, 2689], [785, 1687, 2629, 3973], [0, 1290, 2041], [703, 3696], [826, 2206], [238,
      1703, 1733], [2245, 2337], [268, 1761, 2205, 2599], [298, 1422, 1550, 4104], [879, 1406],
      [3766, 3991], [1806, 1879], [361, 745], [1814, 3062], [2120, 2759], [332, 1822, 1895,
      2046, 3094, 3124], [862, 1141, 3272, 3340, 3782, 3874], [337, 3308, 3742], [], [728,
      1826, 2062, 3078, 3271, 4007], [1566, 2775, 3359, 3522], [315, 1678, 2104, 2585, 3590],
      [312, 1106, 1654, 2382, 3328, 3549], [1670, 2398], [1694, 2136], [1818, 2188], [403,
      1810, 3858], [], [87, 2527, 3627], [1216, 1280], [1320, 2932], [1371, 2923], [156, 1209,
      1273], [708, 1161]], ![[2099, 3155], [2679, 4115], [2643, 3569], [2940, 3294], [93],
      [2131, 2546, 2786, 2924], [97, 670], [2242, 3788], [94, 811, 2115, 2375, 2979], [], [98,
      2956], [2444, 2611, 3847, 4023], [1319, 3970], [102, 1039, 2627], [101], [562, 3603],
      [437, 3122, 3612], [847, 1156], [442, 2999], [739, 2433], [1003, 3883], [898, 3980],
      [775, 2311], [714, 3075], [2283, 4081], [441, 2588, 3587, 4082], [438], [558, 2252, 3059,
      3911], [851, 3091], [], [2543, 3777], [70, 2347], [1043, 3164], [], [7, 1304, 3139,
      4099], [676, 3293], [961, 1187], [1095, 2545, 2785, 3819], [], [2711, 3509], [3207,
      4071], [2183, 2659], [921, 948], [], [373, 2947], [2460, 3954], [369, 1083, 2931, 3831,
      4039], [2738, 2972, 3702, 4055], [2963, 3249], [374, 622], [370], [2147, 2359, 2727,
      3804], [1271, 2226], [377, 799, 2695], [378], [2165, 3899], [175], [986, 3015], [180,
      2166, 3543, 3736], [], [610, 2295, 3047, 3996], [2417, 3691], [1123, 3031], [884, 1119]],
      ![[606, 3527], [179, 3107], [176, 3190, 3544], [1015, 3895], [1138, 2268], [763, 2299],
      [979, 3761], [347, 3835], [], [803, 3224], [284, 1256, 2199, 3223], [823, 2363, 2737,
      3701], [628, 3250], [], [689, 915], [278, 1337, 2051, 2762, 2948, 3302, 3432], [511,
      1572, 1706, 2452, 3476, 3962], [518, 1684, 1850, 2218, 3467, 3812], [363, 650, 1354,
      2879, 2939, 3379, 3447], [700, 3659], [929, 2495], [1700, 2234], [1834, 3796], [1556,
      3946], [1722, 2468], [940, 2511], [1169, 3643], [1368, 2971], [634, 1235, 1338, 2067,
      2479, 2746, 2964, 3314, 3420, 3675], [1242, 1353, 2555, 2895, 2955, 3241, 3309, 3727],
      [1323, 2980], [77, 731, 1748, 2409, 3465, 3562], [80, 2208, 3433], [17, 3434, 4087], [14,
      890, 1529, 3187, 3466, 4004], [44, 1148], [1764, 2425], [1513, 3988], [64, 994], [81,
      3494, 4132], [13, 1130, 1641, 2260, 3127, 3450], [76, 971, 1892, 3449, 3502, 3769], [18,
      2163, 3493], [65, 722], [1876, 3753], [1657, 2276], [43, 876], [510, 681, 907, 3181,
      3451, 3575], [507, 1237, 2069, 2745, 2899, 3313, 3483], [537, 640, 1244, 3242, 3310,
      3424, 3492], [519, 953, 1179, 3113, 3460, 3507], [551, 1199, 1423], [656, 1302, 1407,
      2053, 2761, 2883, 3301, 3375], [1206, 1430], [299, 1295, 1414, 2571, 3711], [91, 1471,
      2303], [], [1463, 4091], [1843, 4015], [1867, 3891], [57, 1011, 1883, 3172, 3331, 3907],
      [60, 1859, 3199, 3694, 4047], [1715, 2772, 3131, 3356], [889, 1455, 2056, 2410, 2687,
      3268]], ![[], [40, 2537, 3311], [767, 980, 2251, 2287, 3275, 3343], [35, 1459, 1642,
      2040, 2703, 3501], [2756, 4031], [1467, 2671], [21, 855], [1475, 1658], [2267, 2426],
      [84, 1400, 1731, 2175], [721, 1416], [930, 2596], [807, 4074], [515, 1547, 1833], [3787,
      3823], [545, 1519, 3699, 4073], [277, 1413, 2047], [1205, 1429, 2991, 3099], [1091, 1705,
      3067, 3803], [819, 1849, 2443, 3007], [321, 1301, 2054], [954, 1563, 2351, 3083], [364],
      [1231, 2063, 3535, 3579], [1238, 1535, 1651, 2070], [682, 1675, 3023, 3839], [522, 1691,
      1721], [540, 1667, 2157, 2551], [1170, 3744], [1047, 2158], [2367, 2459], [1923, 2371],
      [1775, 3945], [1523, 2008], [541, 1911], [523], [916, 1903, 3114, 3843], [586, 1241],
      [362, 652, 1783, 1915, 1994], [1248, 1978], [1188, 1791, 2355, 3182], [276, 1411, 1539,
      1647, 1977], [636, 1203, 1427, 1993], [815, 1907, 3552, 3961], [1087, 1795, 2217, 3620],
      [300, 570, 1299, 3519, 3595], [544, 1787], [1779, 3827], [1919, 2233], [514], [1663,
      1963], [993, 1415], [85, 1431, 1839, 4107], [1514, 1587], [3754, 3979], [22, 1127], [61,
      1711, 2123, 2538, 3147], [], [1129, 1599, 2055, 2619, 3284, 3770], [56, 771, 1739, 2291,
      3232, 3347], [1855, 2747, 3215, 3315], [36, 1530, 1603, 2071, 2635, 3561], [39, 3360,
      3693], [1591, 2651]], ![[2107, 2763], [740, 1007, 3259, 3327, 3903, 3995], [], [92, 1583,
      3887], [1727, 2139], [1595, 2191], [1755, 2307], [184, 2780, 3735], [2259, 2519], [2418,
      2503], [2535, 3283], [626, 3428], [922, 3179], [306, 2451], [690, 2200, 2871, 3795],
      [664, 3383], [327, 2225], [939, 3510], [1180, 2155, 2907, 3953], [2739, 3719], [875,
      3189], [985, 3499], [183, 732, 1137, 3267, 3683, 3762, 3987], [446, 897, 972, 2275, 2434,
      2487, 3260], [1147, 3121], [713, 3567], [2579, 2732], [962, 2467, 2919, 4124], [1162,
      3119], [29, 3811], [674, 3371], [908, 2241, 2859, 4079], [50, 3969], [699, 3570], [616,
      3416], [3276, 3635], [3667, 4003], [3651, 3778], [445, 2563, 2787], [367], [1479, 2719],
      [], [1115, 1155, 1451, 4063], [], [582, 646, 1212, 1276], [88, 598, 662, 3039, 3051], [],
      [947, 1035, 1799, 1960], [86], [1210, 1274, 1771, 1927], [707, 795, 1899, 2011], [843,
      883, 1607, 2091], [1579, 2603], [], [368], [], [], [], [], [], [], [], [], []]]

/-- The packet numbers whose incoming label lies in octad `o`. -/
def generatedFeasibleAmbientTenthOctadPackets (o : Fin 759) : List (Fin 4136) :=
  generatedFeasibleAmbientTenthOctadPacketData ⟨o.val / 64, by omega⟩ ⟨o.val % 64, by omega⟩

/-- The located packet entry test: octad labels lie in the list of their octad. -/
def generatedFeasibleAmbientTenthOctadLocated (n : Fin 4136) : Bool :=
  match generatedTenthIncomingShortLabel n with
  | Sum.inr (Sum.inl (o, _)) => decide (n ∈ generatedFeasibleAmbientTenthOctadPackets o)
  | _ => true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- All 4136 packet labels are located.
private theorem packets_complete : ∀ n : Fin 4136, generatedFeasibleAmbientTenthOctadLocated n =
    true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- All 759 lists are checked.
private theorem packets_nodup : ∀ o : Fin 759, (generatedFeasibleAmbientTenthOctadPackets o).Nodup
    := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- All 759 octad blocks are summed.
private theorem packets_sum : ∀ o : Fin 759,
    ((generatedFeasibleAmbientTenthOctadPackets o).map (fun n =>
      |generatedTenthPacketNumerator (generatedAxisGlobalFifthPacketFromNumber n)|)).sum ≤ 32 := by
  decide +kernel

private theorem mem_of_label {n : Fin 4136} {o : Fin 759} {f : Fin 64}
    (h : generatedTenthIncomingShortLabel n = Sum.inr (Sum.inl (o, f))) :
    n ∈ generatedFeasibleAmbientTenthOctadPackets o := by
  have hc := packets_complete n
  unfold generatedFeasibleAmbientTenthOctadLocated at hc
  rw [h] at hc
  simpa using hc

set_option maxRecDepth 100000 in
-- All 4096 actual octad Fourier entries are checked.
private theorem triality_entry_abs : ∀ e f : Fin 64, |trialityIntegerMatrix e f| = 1 := by
  unfold trialityIntegerMatrix trialityIntegerDiagonal trialityHadamard
  decide +kernel

/-- The incoming packet coefficient with its central sign. -/
private def coef (i : GeneratedAxisGlobalFifthShortPacketIndex) : ℝ :=
  generatedAxisGlobalFifthShortPacketCoefficient i *
    qSign (generatedAxisGlobalFifthRoot02ShortPhase i)

private theorem coef_abs (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    |coef i| = |(generatedTenthPacketNumerator i : ℝ)| / 16 := by
  unfold coef
  rw [generatedTenth_packet_coefficient_numerator, abs_mul]
  have hq : |qSign (generatedAxisGlobalFifthRoot02ShortPhase i)| = 1 := by
    unfold qSign
    split_ifs <;> simp
  rw [hq, mul_one, abs_div]
  norm_num

private theorem incoming_short (r : GriessShortIndex) :
    (griessConwayEncode (rhoLocal generatedTenthLocal generatedFifthAxis)).2.1 r =
      ∑ i : GeneratedAxisGlobalFifthShortPacketIndex,
        coef i * (if r = generatedAxisGlobalFifthRoot02ShortLabel i then 1 else 0) := by
  rw [generatedTenthLocal, generatedAxisGlobalFifthRoot02Packet_actual]
  change (∑ i : GeneratedAxisGlobalFifthShortPacketIndex,
      (generatedAxisGlobalFifthShortPacketCoefficient i *
        qSign (generatedAxisGlobalFifthRoot02ShortPhase i)) •
        Pi.single (generatedAxisGlobalFifthRoot02ShortLabel i) (1 : ℝ)) r = _
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, coef]

/-- The octad-block weight of a packet entry. -/
private def blockWeight (o : Fin 759) (i : GeneratedAxisGlobalFifthShortPacketIndex) : ℝ :=
  ∑ f : Fin 64, |coef i| *
    (if Sum.inr (Sum.inl (o, f)) = generatedAxisGlobalFifthRoot02ShortLabel i then 1 else 0)

private theorem block_term (o : Fin 759) (e : Fin 64)
    (i : GeneratedAxisGlobalFifthShortPacketIndex) :
    |∑ f : Fin 64, ((1 / 8 : ℝ) * (trialityIntegerMatrix e f : ℝ)) *
      (coef i * (if Sum.inr (Sum.inl (o, f)) = generatedAxisGlobalFifthRoot02ShortLabel i
        then 1 else 0))| ≤ blockWeight o i / 8 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  unfold blockWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro f _
  have ht : |(trialityIntegerMatrix e f : ℝ)| = 1 := by
    have h1 := triality_entry_abs e f
    exact_mod_cast h1
  rw [abs_mul, abs_mul, abs_mul, ht, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
  by_cases hc : (Sum.inr (Sum.inl (o, f)) : GriessShortIndex) =
      generatedAxisGlobalFifthRoot02ShortLabel i
  · simp only [hc, ite_true, abs_one]
    ring
  · simp only [hc, ite_false, abs_zero]
    ring

private theorem block_le (o : Fin 759) (n : Fin 4136) :
    blockWeight o (generatedAxisGlobalFifthPacketFromNumber n) ≤
      if n ∈ (generatedFeasibleAmbientTenthOctadPackets o).toFinset then
        |(generatedTenthPacketNumerator (generatedAxisGlobalFifthPacketFromNumber n) : ℝ)| / 16
      else 0 := by
  have hlab : generatedAxisGlobalFifthRoot02ShortLabel (generatedAxisGlobalFifthPacketFromNumber
      n) =
      generatedTenthIncomingShortLabel n := by
    change generatedTenthIncomingShortLabel
      (generatedAxisGlobalFifthPacketNumber (generatedAxisGlobalFifthPacketFromNumber n)) = _
    rw [generatedAxisGlobalFifthPacketNumber_fromNumber]
  unfold blockWeight
  rw [hlab, coef_abs]
  rcases hl : generatedTenthIncomingShortLabel n with ⟨s, p⟩ | (⟨o', f'⟩ | ⟨d, j⟩)
  · simp only [reduceCtorEq, ite_false, mul_zero, Finset.sum_const_zero]
    split_ifs <;> positivity
  · by_cases ho : o' = o
    · subst ho
      have hm : n ∈ (generatedFeasibleAmbientTenthOctadPackets o').toFinset :=
          List.mem_toFinset.mpr (mem_of_label hl)
      simp only [hm, ite_true]
      rw [Finset.sum_eq_single f']
      · simp
      · intro f _ hf
        have hne : (Sum.inr (Sum.inl (o', f)) : GriessShortIndex) ≠ Sum.inr (Sum.inl (o', f')) := by
          intro h
          apply hf
          simpa using h
        simp [hne]
      · simp
    · have hne : ∀ f : Fin 64,
          (Sum.inr (Sum.inl (o, f)) : GriessShortIndex) ≠ Sum.inr (Sum.inl (o', f')) := by
        intro f h
        apply ho
        simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
        exact h.1.symm
      simp only [hne, ite_false, mul_zero, Finset.sum_const_zero]
      split_ifs <;> positivity
  · simp only [Sum.inr.injEq, reduceCtorEq, ite_false, mul_zero, Finset.sum_const_zero]
    split_ifs <;> positivity

private theorem block_sum (o : Fin 759) :
    ∑ i : GeneratedAxisGlobalFifthShortPacketIndex, blockWeight o i ≤ 2 := by
  have hre : ∑ i : GeneratedAxisGlobalFifthShortPacketIndex, blockWeight o i =
      ∑ n : Fin 4136, blockWeight o (generatedAxisGlobalFifthPacketFromNumber n) := by
    refine Fintype.sum_equiv
      ⟨generatedAxisGlobalFifthPacketNumber, generatedAxisGlobalFifthPacketFromNumber,
        generatedAxisGlobalFifthPacketFromNumber_number,
        generatedAxisGlobalFifthPacketNumber_fromNumber⟩ _ _ ?_
    intro i
    simp only [Equiv.coe_fn_mk, generatedAxisGlobalFifthPacketFromNumber_number]
  rw [hre]
  calc ∑ n : Fin 4136, blockWeight o (generatedAxisGlobalFifthPacketFromNumber n)
      ≤ ∑ n : Fin 4136, (if n ∈ (generatedFeasibleAmbientTenthOctadPackets o).toFinset then
          |(generatedTenthPacketNumerator (generatedAxisGlobalFifthPacketFromNumber n) : ℝ)| / 16
        else 0) := Finset.sum_le_sum (fun n _ => block_le o n)
    _ = ∑ n ∈ (generatedFeasibleAmbientTenthOctadPackets o).toFinset,
          |(generatedTenthPacketNumerator (generatedAxisGlobalFifthPacketFromNumber n) : ℝ)| / 16
              := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ((∑ n ∈ (generatedFeasibleAmbientTenthOctadPackets o).toFinset,
          |generatedTenthPacketNumerator (generatedAxisGlobalFifthPacketFromNumber n)| : ℤ) : ℝ)
          / 16 := by
        push_cast
        rw [Finset.sum_div]
    _ = (((generatedFeasibleAmbientTenthOctadPackets o).map (fun n =>
          |generatedTenthPacketNumerator (generatedAxisGlobalFifthPacketFromNumber n)|)).sum : ℝ)
          / 16 := by
        rw [List.sum_toFinset _ (packets_nodup o)]
    _ ≤ 2 := by
        have h := packets_sum o
        have h' : ((((generatedFeasibleAmbientTenthOctadPackets o).map (fun n =>
            |generatedTenthPacketNumerator (generatedAxisGlobalFifthPacketFromNumber n)|)).sum : ℤ)
              : ℝ) ≤ 32 := by exact_mod_cast h
        linarith

/-- Every octad row of the Tenth prototype has absolute value at most `1/4`. -/
theorem generatedFeasibleAmbientTenth_octad_abs (o : Fin 759) (e : Fin 64) :
    |(griessConwayEncode generatedTenthAxis).2.1 (Sum.inr (Sum.inl (o, e)))| ≤ 1 / 4 := by
  rw [generatedTenthAxis_local_expression, generatedSeventhXi_octad_triality_coordinate,
    trialityOctadAction_matrix]
  change |∑ f : Fin 64, ((1 / 8 : ℝ) * (trialityIntegerMatrix e f : ℝ)) *
    (griessConwayEncode (rhoLocal generatedTenthLocal generatedFifthAxis)).2.1
      (Sum.inr (Sum.inl (o, f)))| ≤ _
  simp_rw [incoming_short, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc _ ≤ ∑ i : GeneratedAxisGlobalFifthShortPacketIndex,
        |∑ f : Fin 64, ((1 / 8 : ℝ) * (trialityIntegerMatrix e f : ℝ)) *
          (coef i * (if Sum.inr (Sum.inl (o, f)) = generatedAxisGlobalFifthRoot02ShortLabel i
            then 1 else 0))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : GeneratedAxisGlobalFifthShortPacketIndex, blockWeight o i / 8 :=
        Finset.sum_le_sum (fun i _ => block_term o e i)
    _ = (∑ i : GeneratedAxisGlobalFifthShortPacketIndex, blockWeight o i) / 8 := by
        rw [Finset.sum_div]
    _ ≤ 1 / 4 := by
        have h := block_sum o
        linarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
