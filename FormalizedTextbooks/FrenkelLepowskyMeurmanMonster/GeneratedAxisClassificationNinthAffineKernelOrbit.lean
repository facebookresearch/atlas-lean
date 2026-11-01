/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitMasks

/-! Nine finite full binary images and a512-point regular orbit on one actual coordinate vector.
Their binding to full-axis fixing spatial words remains a separate prerequisite. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Full binary columns discovered from nine original section Schreier words. -/
def generatedNinthAffineKernelColumns : Fin 9 → Fin 24 → ℕ :=
  ![![67585, 8323074, 4, 3541000, 669712, 2467872, 1222720, 73856, 2400512, 1221120, 11264, 2048,
  6144, 8192, 18432, 34816, 65536, 133120, 264192, 524288, 1048576, 2097152, 4194304, 13078637],
    ![4196353, 4196354, 4, 4196360, 1966096, 3735584, 3735616, 2556032, 459008, 918016, 46080,
    2048, 4096, 8192, 18432, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304,
    8433668],
    ![4325377, 5570562, 4, 1771528, 3713040, 3446816, 665664, 2457728, 2334976, 1769984, 15360,
    2048, 6144, 10240, 16384, 32768, 67584, 131072, 264192, 526336, 1048576, 2097152, 4194304,
    13074643],
    ![67585, 8323074, 4, 7733256, 3946512, 565280, 106560, 3352704, 633088, 633344, 44032, 2048,
    4096, 10240, 16384, 34816, 65536, 133120, 264192, 524288, 1048576, 2097152, 4194304,
    16322666],
    ![4390913, 6946818, 4, 7143432, 3051536, 2699296, 2719808, 499840, 256, 502272, 46080, 2048,
    4096, 8192, 18432, 32768, 67584, 133120, 262144, 526336, 1048576, 2097152, 4194304,
    10485940],
    ![4196353, 4196354, 4, 4196360, 917530, 1638441, 1638477, 1507463, 5114122, 512, 1094868,
    2048, 921600, 1646592, 4997120, 1540096, 4261888, 131072, 4458496, 4720640, 1048576, 2097152,
    4194304, 9482448],
    ![4196367, 4196360, 4, 4196354, 1966272, 3735616, 3735584, 2555952, 459008, 918016, 46080,
    2048, 4096, 36864, 22528, 12288, 524288, 786432, 196608, 65536, 1048576, 2097152, 4194304,
    8433668],
    ![8323074, 4259841, 4, 526351, 3682419, 4460702, 7999742, 5607513, 2953662, 1381086, 932964,
    2048, 632832, 3643392, 7784448, 4096000, 4128768, 5570560, 7143424, 3538944, 1048576,
    2097152, 4194304, 12615687],
    ![67585, 8323074, 4, 7733256, 6434835, 3252266, 3711050, 5513357, 5153034, 4694538, 3779684,
    2048, 593920, 3614720, 4737024, 4098048, 65536, 4325376, 4456448, 524288, 1048576, 2097152,
    4194304, 12587022]]

/-- Binary-order original letter products on the nine source images. -/
def generatedNinthAffineKernelSourceWord (k : Fin 512) : List (Fin 9) :=
  (List.finRange 9).reverse.filter (fun j => k.val.testBit j.val)

/-- Evaluation of a full binary source word on a packed original vector. -/
def generatedNinthAffineKernelMaskWord (w : List (Fin 9)) (v : ℕ) : ℕ :=
  w.foldr (fun j z => sixthFrameOrbitMaskApply (generatedNinthAffineKernelColumns j) z) v

/-- All512 exact packed images of original coordinate vector16. -/
def generatedNinthAffineKernelOrbitImage : Fin 512 → ℕ :=
  ![16, 669712, 1966096, 1325072, 3713040, 3315728, 2533392, 2922512,
    3946512, 3538960, 2242576, 2621456, 299024, 958480, 1740816, 1089552,
    3051536, 2402320, 3182608, 3844112, 1454096, 1835024, 536592, 131088,
    1220624, 1611792, 827408, 432144, 2752528, 2109456, 3407888, 4075536,
    917530, 5451802, 1048602, 5058586, 7905306, 2463770, 6725658, 3905562,
    2439194, 7866394, 3880986, 6686746, 5478426, 958490, 5085210, 1089562,
    3772442, 6594586, 2592794, 8036378, 5191706, 1179674, 5322778, 786458,
    1220634, 5214234, 827418, 5345306, 6555674, 3747866, 7997466, 2568218,
    1966272, 1280192, 192, 886976, 3123392, 2238656, 3254464, 3942592,
    2918592, 2162880, 3311808, 4128960, 1908928, 1089728, 204992, 958656,
    3154112, 4040896, 3023040, 2336960, 98496, 786624, 2064576, 1179840,
    172224, 993472, 1876160, 1124544, 3342528, 4096192, 2949312, 2130112,
    1048778, 4882634, 917706, 5537994, 7315658, 3483850, 7446730, 2828490,
    3508426, 7276746, 2853066, 7407818, 4860106, 1089738, 5515466, 958666,
    2564298, 8233162, 3743946, 6529226, 5802186, 131274, 4622538, 1835210,
    172234, 5775562, 1876170, 4595914, 8194250, 2588874, 6490314, 3768522,
    3682419, 6621299, 2502771, 8063091, 3612787, 6951027, 2695283, 7606387,
    7145587, 3158131, 7538803, 3027059, 6428787, 4139123, 8132723, 2173043,
    2168947, 8134771, 4135027, 6430835, 3014771, 7549043, 3145843, 7155827,
    7612531, 2691187, 6957171, 3608691, 8073331, 2490483, 6631539, 3670131,
    8337533, 7669885, 6371453, 7014525, 4071549, 3414141, 2105469, 2758781,
    3997821, 3616893, 2293885, 2699389, 8132733, 7741565, 6428797, 6824061,
    8327293, 7676029, 6361213, 7020669, 4063357, 3422333, 2097277, 2766973,
    4006013, 3608701, 2302077, 2691197, 8138877, 7735421, 6434941, 6817917,
    3244199, 7014567, 3113127, 7669927, 3641511, 7147687, 2724007, 7540903,
    6949031, 3178663, 7604391, 3047591, 7084199, 3578023, 7477415, 2660519,
    2627751, 7508135, 3545255, 7114919, 3014823, 7635111, 3145895, 6979751,
    7575719, 2691239, 7182503, 3608743, 7700647, 3080359, 7045287, 3211431,
    7768233, 8063145, 6850729, 6621353, 4100265, 3348649, 2134185, 2955433,
    3801257, 3637417, 2359465, 2719913, 7477417, 8360105, 7084201, 6394025,
    7737513, 8097961, 6820009, 6656169, 4063401, 3377321, 2097321, 2984105,
    3838121, 3608745, 2396329, 2691241, 7504041, 8325289, 7110825, 6359209,
    6434835, 1441811, 8138771, 524307, 5478419, 2596883, 5085203, 3776531,
    2097171, 5517331, 4063251, 4861971, 1157139, 6656019, 1026067, 8097811,
    8103955, 1021971, 6662163, 1153043, 4851731, 4075539, 5507091, 2109459,
    3772435, 5087251, 2592787, 5480467, 536595, 8128531, 1454099, 6424595,
    6631449, 4589593, 8073241, 5769241, 1740825, 3776537, 299033, 2596889,
    3145753, 1259545, 3014681, 866329, 5218329, 7114777, 5349401, 7507993,
    6662169, 4624409, 8103961, 5804057, 1703961, 3747865, 262169, 2568217,
    3182617, 1288217, 3051545, 895001, 5191705, 7079961, 5322777, 7473177,
    7504071, 65735, 7110855, 2031815, 4860103, 3776711, 5515463, 2597063,
    4063431, 5079239, 2097351, 5472455, 436423, 7676103, 1616071, 7020743,
    7055559, 1583303, 7710919, 403655, 5441735, 2130119, 5048519, 4096199,
    2564295, 5546183, 3743943, 4890823, 2064583, 7080135, 98503, 7473351,
    7700685, 5310669, 7045325, 5179597, 205005, 2597069, 1908941, 3776717,
    3014861, 690381, 3145933, 1345741, 5808333, 8134861, 4628685, 6430925,
    7710925, 5316813, 7055565, 5185741, 196813, 2588877, 1900749, 3768525,
    3023053, 698573, 3154125, 1353933, 5802189, 8128717, 4622541, 6424781,
    1245296, 3158128, 852080, 3027056, 1380464, 3549296, 725104, 2631792,
    3682416, 1769584, 2502768, 327792, 4071536, 1906800, 2105456, 202864,
    4006000, 1970288, 2302064, 4208, 3881072, 1572976, 2439280, 393328,
    1448048, 3483760, 530544, 2828400, 1048688, 3356784, 917616, 2963568,
    6097022, 2699390, 4393086, 3616894, 1380478, 6365310, 725118, 8331390,
    6371454, 1376382, 8337534, 721022, 2695294, 6099070, 3612798, 4395134,
    6957182, 1970302, 7612542, 4222, 2242686, 5638270, 3946622, 4720766,
    5640318, 2238590, 4722814, 3942526, 1966206, 6959230, 126, 7614590,
    1310880, 3178656, 655520, 3047584, 1773728, 4167840, 331936, 2201760,
    3244192, 1376416, 3113120, 721056, 4100256, 1710240, 2134176, 268448,
    3838112, 1970336, 2396320, 4256, 3508384, 1114272, 2853024, 983200,
    2037920, 3905696, 71840, 2463904, 1048736, 3442848, 917664, 2787488,
    5900462, 2719918, 4458670, 3637422, 1773742, 6852782, 331950, 7770286,
    6850734, 1769646, 7768238, 327854, 2724014, 5902510, 3641518, 4460718,
    7182510, 1970350, 7575726, 4270, 2918574, 6228142, 3311790, 4262062,
    6230190, 2922670, 4264110, 3315886, 1966254, 7176366, 174, 7569582]

/-- Exact balanced lookup of each displayed source orbit image. -/
def generatedNinthAffineKernelOrbitLookup (v : ℕ) : ℕ :=
  if v < 3538960 then
    if v < 2097171 then
      if v < 1048602 then
        if v < 524307 then
          if v < 196813 then
            if v < 65735 then
              if v < 4208 then
                if v < 174 then
                  if v < 126 then
                    if v = 16 then 0 else 512
                  else if v = 126 then 446 else
                    512
                else if v = 174 then 510 else
                  if v = 192 then 66 else 512
              else if v = 4208 then 403 else
                if v < 4256 then
                  if v = 4222 then 435 else 512
                else if v = 4256 then 467 else
                  if v = 4270 then 499 else 512
            else if v = 65735 then 321 else
              if v < 131088 then
                if v < 98496 then
                  if v = 71840 then 474 else 512
                else if v = 98496 then 84 else
                  if v = 98503 then 350 else 512
              else if v = 131088 then 23 else
                if v < 172224 then
                  if v = 131274 then 117 else 512
                else if v = 172224 then 88 else
                  if v = 172234 then 120 else 512
          else if v = 196813 then 372 else
            if v < 327792 then
              if v < 262169 then
                if v < 204992 then
                  if v = 202864 then 399 else 512
                else if v = 204992 then 78 else
                  if v = 205005 then 356 else 512
              else if v = 262169 then 310 else
                if v < 299024 then
                  if v = 268448 then 463 else 512
                else if v = 299024 then 12 else
                  if v = 299033 then 294 else 512
            else if v = 327792 then 395 else
              if v < 393328 then
                if v < 331936 then
                  if v = 327854 then 491 else 512
                else if v = 331936 then 454 else
                  if v = 331950 then 486 else 512
              else if v = 393328 then 407 else
                if v < 432144 then
                  if v = 403655 then 339 else 512
                else if v = 432144 then 27 else
                  if v = 436423 then 332 else 512
        else if v = 524307 then 259 else
          if v < 852080 then
            if v < 721022 then
              if v < 655520 then
                if v < 536592 then
                  if v = 530544 then 410 else 512
                else if v = 536592 then 22 else
                  if v = 536595 then 284 else 512
              else if v = 655520 then 450 else
                if v < 690381 then
                  if v = 669712 then 1 else 512
                else if v = 690381 then 361 else
                  if v = 698573 then 377 else 512
            else if v = 721022 then 427 else
              if v < 786458 then
                if v < 725104 then
                  if v = 721056 then 459 else 512
                else if v = 725104 then 390 else
                  if v = 725118 then 422 else 512
              else if v = 786458 then 55 else
                if v < 827408 then
                  if v = 786624 then 85 else 512
                else if v = 827408 then 26 else
                  if v = 827418 then 58 else 512
          else if v = 852080 then 386 else
            if v < 958480 then
              if v < 917530 then
                if v < 886976 then
                  if v = 866329 then 299 else 512
                else if v = 886976 then 67 else
                  if v = 895001 then 315 else 512
              else if v = 917530 then 32 else
                if v < 917664 then
                  if v = 917616 then 414 else 512
                else if v = 917664 then 478 else
                  if v = 917706 then 98 else 512
            else if v = 958480 then 13 else
              if v < 983200 then
                if v < 958656 then
                  if v = 958490 then 45 else 512
                else if v = 958656 then 79 else
                  if v = 958666 then 111 else 512
              else if v = 983200 then 471 else
                if v < 1021971 then
                  if v = 993472 then 89 else 512
                else if v = 1021971 then 273 else
                  if v = 1026067 then 270 else 512
      else if v = 1048602 then 34 else
        if v < 1572976 then
          if v < 1245296 then
            if v < 1114272 then
              if v < 1089552 then
                if v < 1048736 then
                  if v = 1048688 then 412 else 512
                else if v = 1048736 then 476 else
                  if v = 1048778 then 96 else 512
              else if v = 1089552 then 15 else
                if v < 1089728 then
                  if v = 1089562 then 47 else 512
                else if v = 1089728 then 77 else
                  if v = 1089738 then 109 else 512
            else if v = 1114272 then 469 else
              if v < 1179674 then
                if v < 1153043 then
                  if v = 1124544 then 91 else 512
                else if v = 1153043 then 275 else
                  if v = 1157139 then 268 else 512
              else if v = 1179674 then 53 else
                if v < 1220624 then
                  if v = 1179840 then 87 else 512
                else if v = 1220624 then 24 else
                  if v = 1220634 then 56 else 512
          else if v = 1245296 then 384 else
            if v < 1376382 then
              if v < 1310880 then
                if v < 1280192 then
                  if v = 1259545 then 297 else 512
                else if v = 1280192 then 65 else
                  if v = 1288217 then 313 else 512
              else if v = 1310880 then 448 else
                if v < 1345741 then
                  if v = 1325072 then 3 else 512
                else if v = 1345741 then 363 else
                  if v = 1353933 then 379 else 512
            else if v = 1376382 then 425 else
              if v < 1441811 then
                if v < 1380464 then
                  if v = 1376416 then 457 else 512
                else if v = 1380464 then 388 else
                  if v = 1380478 then 420 else 512
              else if v = 1441811 then 257 else
                if v < 1454096 then
                  if v = 1448048 then 408 else 512
                else if v = 1454096 then 20 else
                  if v = 1454099 then 286 else 512
        else if v = 1572976 then 405 else
          if v < 1900749 then
            if v < 1769584 then
              if v < 1703961 then
                if v < 1611792 then
                  if v = 1583303 then 337 else 512
                else if v = 1611792 then 25 else
                  if v = 1616071 then 334 else 512
              else if v = 1703961 then 308 else
                if v < 1740816 then
                  if v = 1710240 then 461 else 512
                else if v = 1740816 then 14 else
                  if v = 1740825 then 292 else 512
            else if v = 1769584 then 393 else
              if v < 1835024 then
                if v < 1773728 then
                  if v = 1769646 then 489 else 512
                else if v = 1773728 then 452 else
                  if v = 1773742 then 484 else 512
              else if v = 1835024 then 21 else
                if v < 1876160 then
                  if v = 1835210 then 119 else 512
                else if v = 1876160 then 90 else
                  if v = 1876170 then 122 else 512
          else if v = 1900749 then 374 else
            if v < 1970288 then
              if v < 1966096 then
                if v < 1908928 then
                  if v = 1906800 then 397 else 512
                else if v = 1908928 then 76 else
                  if v = 1908941 then 358 else 512
              else if v = 1966096 then 2 else
                if v < 1966254 then
                  if v = 1966206 then 444 else 512
                else if v = 1966254 then 508 else
                  if v = 1966272 then 64 else 512
            else if v = 1970288 then 401 else
              if v < 2031815 then
                if v < 1970336 then
                  if v = 1970302 then 433 else 512
                else if v = 1970336 then 465 else
                  if v = 1970350 then 497 else 512
              else if v = 2031815 then 323 else
                if v < 2064576 then
                  if v = 2037920 then 472 else 512
                else if v = 2064576 then 86 else
                  if v = 2064583 then 348 else 512
    else if v = 2097171 then 264 else
      if v < 2752528 then
        if v < 2490483 then
          if v < 2238590 then
            if v < 2130112 then
              if v < 2105456 then
                if v < 2097321 then
                  if v = 2097277 then 182 else 512
                else if v = 2097321 then 246 else
                  if v = 2097351 then 330 else 512
              else if v = 2105456 then 398 else
                if v < 2109456 then
                  if v = 2105469 then 166 else 512
                else if v = 2109456 then 29 else
                  if v = 2109459 then 279 else 512
            else if v = 2130112 then 95 else
              if v < 2162880 then
                if v < 2134176 then
                  if v = 2130119 then 341 else 512
                else if v = 2134176 then 462 else
                  if v = 2134185 then 230 else 512
              else if v = 2162880 then 73 else
                if v < 2173043 then
                  if v = 2168947 then 144 else 512
                else if v = 2173043 then 143 else
                  if v = 2201760 then 455 else 512
          else if v = 2238590 then 441 else
            if v < 2359465 then
              if v < 2293885 then
                if v < 2242576 then
                  if v = 2238656 then 69 else 512
                else if v = 2242576 then 10 else
                  if v = 2242686 then 436 else 512
              else if v = 2293885 then 170 else
                if v < 2302077 then
                  if v = 2302064 then 402 else 512
                else if v = 2302077 then 186 else
                  if v = 2336960 then 83 else 512
            else if v = 2359465 then 234 else
              if v < 2439194 then
                if v < 2396329 then
                  if v = 2396320 then 466 else 512
                else if v = 2396329 then 250 else
                  if v = 2402320 then 17 else 512
              else if v = 2439194 then 40 else
                if v < 2463770 then
                  if v = 2439280 then 406 else 512
                else if v = 2463770 then 37 else
                  if v = 2463904 then 475 else 512
        else if v = 2490483 then 157 else
          if v < 2621456 then
            if v < 2588874 then
              if v < 2564295 then
                if v < 2502771 then
                  if v = 2502768 then 394 else 512
                else if v = 2502771 then 130 else
                  if v = 2533392 then 6 else 512
              else if v = 2564295 then 344 else
                if v < 2568217 then
                  if v = 2564298 then 112 else 512
                else if v = 2568217 then 311 else
                  if v = 2568218 then 63 else 512
            else if v = 2588874 then 125 else
              if v < 2596883 then
                if v < 2592787 then
                  if v = 2588877 then 373 else 512
                else if v = 2592787 then 282 else
                  if v = 2592794 then 50 else 512
              else if v = 2596883 then 261 else
                if v < 2597063 then
                  if v = 2596889 then 295 else 512
                else if v = 2597063 then 327 else
                  if v = 2597069 then 357 else 512
          else if v = 2621456 then 11 else
            if v < 2695283 then
              if v < 2691187 then
                if v < 2631792 then
                  if v = 2627751 then 208 else 512
                else if v = 2631792 then 391 else
                  if v = 2660519 then 207 else 512
              else if v = 2691187 then 153 else
                if v < 2691239 then
                  if v = 2691197 then 187 else 512
                else if v = 2691239 then 217 else
                  if v = 2691241 then 251 else 512
            else if v = 2695283 then 134 else
              if v < 2719913 then
                if v < 2699389 then
                  if v = 2695294 then 428 else 512
                else if v = 2699389 then 171 else
                  if v = 2699390 then 417 else 512
              else if v = 2719913 then 235 else
                if v < 2724007 then
                  if v = 2719918 then 481 else 512
                else if v = 2724007 then 198 else
                  if v = 2724014 then 492 else 512
      else if v = 2752528 then 28 else
        if v < 3145753 then
          if v < 3014681 then
            if v < 2918574 then
              if v < 2828400 then
                if v < 2766973 then
                  if v = 2758781 then 167 else 512
                else if v = 2766973 then 183 else
                  if v = 2787488 then 479 else 512
              else if v = 2828400 then 411 else
                if v < 2853024 then
                  if v = 2828490 then 103 else 512
                else if v = 2853024 then 470 else
                  if v = 2853066 then 106 else 512
            else if v = 2918574 then 500 else
              if v < 2949312 then
                if v < 2922512 then
                  if v = 2918592 then 72 else 512
                else if v = 2922512 then 7 else
                  if v = 2922670 then 505 else 512
              else if v = 2949312 then 94 else
                if v < 2963568 then
                  if v = 2955433 then 231 else 512
                else if v = 2963568 then 415 else
                  if v = 2984105 then 247 else 512
          else if v = 3014681 then 298 else
            if v < 3047584 then
              if v < 3023040 then
                if v < 3014823 then
                  if v = 3014771 then 148 else 512
                else if v = 3014823 then 212 else
                  if v = 3014861 then 360 else 512
              else if v = 3023040 then 82 else
                if v < 3027056 then
                  if v = 3023053 then 376 else 512
                else if v = 3027056 then 387 else
                  if v = 3027059 then 139 else 512
            else if v = 3047584 then 451 else
              if v < 3080359 then
                if v < 3051536 then
                  if v = 3047591 then 203 else 512
                else if v = 3051536 then 16 else
                  if v = 3051545 then 314 else 512
              else if v = 3080359 then 221 else
                if v < 3113127 then
                  if v = 3113120 then 458 else 512
                else if v = 3113127 then 194 else
                  if v = 3123392 then 68 else 512
        else if v = 3145753 then 296 else
          if v < 3311790 then
            if v < 3178656 then
              if v < 3154112 then
                if v < 3145895 then
                  if v = 3145843 then 150 else 512
                else if v = 3145895 then 214 else
                  if v = 3145933 then 362 else 512
              else if v = 3154112 then 80 else
                if v < 3158128 then
                  if v = 3154125 then 378 else 512
                else if v = 3158128 then 385 else
                  if v = 3158131 then 137 else 512
            else if v = 3178656 then 449 else
              if v < 3211431 then
                if v < 3182608 then
                  if v = 3178663 then 201 else 512
                else if v = 3182608 then 18 else
                  if v = 3182617 then 312 else 512
              else if v = 3211431 then 223 else
                if v < 3244199 then
                  if v = 3244192 then 456 else 512
                else if v = 3244199 then 192 else
                  if v = 3254464 then 70 else 512
          else if v = 3311790 then 502 else
            if v < 3407888 then
              if v < 3342528 then
                if v < 3315728 then
                  if v = 3311808 then 74 else 512
                else if v = 3315728 then 5 else
                  if v = 3315886 then 507 else 512
              else if v = 3342528 then 92 else
                if v < 3356784 then
                  if v = 3348649 then 229 else 512
                else if v = 3356784 then 413 else
                  if v = 3377321 then 245 else 512
            else if v = 3407888 then 30 else
              if v < 3483760 then
                if v < 3422333 then
                  if v = 3414141 then 165 else 512
                else if v = 3422333 then 181 else
                  if v = 3442848 then 477 else 512
              else if v = 3483760 then 409 else
                if v < 3508384 then
                  if v = 3483850 then 101 else 512
                else if v = 3508384 then 468 else
                  if v = 3508426 then 104 else 512
  else if v = 3538960 then 9 else
    if v < 6359209 then
      if v < 4262062 then
        if v < 3801257 then
          if v < 3670131 then
            if v < 3612787 then
              if v < 3608691 then
                if v < 3549296 then
                  if v = 3545255 then 210 else 512
                else if v = 3549296 then 389 else
                  if v = 3578023 then 205 else 512
              else if v = 3608691 then 155 else
                if v < 3608743 then
                  if v = 3608701 then 185 else 512
                else if v = 3608743 then 219 else
                  if v = 3608745 then 249 else 512
            else if v = 3612787 then 132 else
              if v < 3637417 then
                if v < 3616893 then
                  if v = 3612798 then 430 else 512
                else if v = 3616893 then 169 else
                  if v = 3616894 then 419 else 512
              else if v = 3637417 then 233 else
                if v < 3641511 then
                  if v = 3637422 then 483 else 512
                else if v = 3641511 then 196 else
                  if v = 3641518 then 494 else 512
          else if v = 3670131 then 159 else
            if v < 3768522 then
              if v < 3743943 then
                if v < 3682419 then
                  if v = 3682416 then 392 else 512
                else if v = 3682419 then 128 else
                  if v = 3713040 then 4 else 512
              else if v = 3743943 then 346 else
                if v < 3747865 then
                  if v = 3743946 then 114 else 512
                else if v = 3747865 then 309 else
                  if v = 3747866 then 61 else 512
            else if v = 3768522 then 127 else
              if v < 3776531 then
                if v < 3772435 then
                  if v = 3768525 then 375 else 512
                else if v = 3772435 then 280 else
                  if v = 3772442 then 48 else 512
              else if v = 3776531 then 263 else
                if v < 3776711 then
                  if v = 3776537 then 293 else 512
                else if v = 3776711 then 325 else
                  if v = 3776717 then 359 else 512
        else if v = 3801257 then 232 else
          if v < 4063251 then
            if v < 3942526 then
              if v < 3880986 then
                if v < 3838121 then
                  if v = 3838112 then 464 else 512
                else if v = 3838121 then 248 else
                  if v = 3844112 then 19 else 512
              else if v = 3880986 then 42 else
                if v < 3905562 then
                  if v = 3881072 then 404 else 512
                else if v = 3905562 then 39 else
                  if v = 3905696 then 473 else 512
            else if v = 3942526 then 443 else
              if v < 3997821 then
                if v < 3946512 then
                  if v = 3942592 then 71 else 512
                else if v = 3946512 then 8 else
                  if v = 3946622 then 438 else 512
              else if v = 3997821 then 168 else
                if v < 4006013 then
                  if v = 4006000 then 400 else 512
                else if v = 4006013 then 184 else
                  if v = 4040896 then 81 else 512
          else if v = 4063251 then 266 else
            if v < 4096192 then
              if v < 4071536 then
                if v < 4063401 then
                  if v = 4063357 then 180 else 512
                else if v = 4063401 then 244 else
                  if v = 4063431 then 328 else 512
              else if v = 4071536 then 396 else
                if v < 4075536 then
                  if v = 4071549 then 164 else 512
                else if v = 4075536 then 31 else
                  if v = 4075539 then 277 else 512
            else if v = 4096192 then 93 else
              if v < 4128960 then
                if v < 4100256 then
                  if v = 4096199 then 343 else 512
                else if v = 4100256 then 460 else
                  if v = 4100265 then 228 else 512
              else if v = 4128960 then 75 else
                if v < 4139123 then
                  if v = 4135027 then 146 else 512
                else if v = 4139123 then 141 else
                  if v = 4167840 then 453 else 512
      else if v = 4262062 then 503 else
        if v < 5310669 then
          if v < 4860106 then
            if v < 4622538 then
              if v < 4458670 then
                if v < 4393086 then
                  if v = 4264110 then 506 else 512
                else if v = 4393086 then 418 else
                  if v = 4395134 then 431 else 512
              else if v = 4458670 then 482 else
                if v < 4589593 then
                  if v = 4460718 then 495 else 512
                else if v = 4589593 then 289 else
                  if v = 4595914 then 123 else 512
            else if v = 4622538 then 118 else
              if v < 4720766 then
                if v < 4624409 then
                  if v = 4622541 then 382 else 512
                else if v = 4624409 then 305 else
                  if v = 4628685 then 366 else 512
              else if v = 4720766 then 439 else
                if v < 4851731 then
                  if v = 4722814 then 442 else 512
                else if v = 4851731 then 276 else
                  if v = 4860103 then 324 else 512
          else if v = 4860106 then 108 else
            if v < 5085210 then
              if v < 5048519 then
                if v < 4882634 then
                  if v = 4861971 then 267 else 512
                else if v = 4882634 then 97 else
                  if v = 4890823 then 347 else 512
              else if v = 5048519 then 342 else
                if v < 5079239 then
                  if v = 5058586 then 35 else 512
                else if v = 5079239 then 329 else
                  if v = 5085203 then 262 else 512
            else if v = 5085210 then 46 else
              if v < 5191705 then
                if v < 5179597 then
                  if v = 5087251 then 281 else 512
                else if v = 5179597 then 355 else
                  if v = 5185741 then 371 else 512
              else if v = 5191705 then 316 else
                if v < 5214234 then
                  if v = 5191706 then 52 else 512
                else if v = 5214234 then 57 else
                  if v = 5218329 then 300 else 512
        else if v = 5310669 then 353 else
          if v < 5537994 then
            if v < 5472455 then
              if v < 5345306 then
                if v < 5322777 then
                  if v = 5316813 then 369 else 512
                else if v = 5322777 then 318 else
                  if v = 5322778 then 54 else 512
              else if v = 5345306 then 59 else
                if v < 5441735 then
                  if v = 5349401 then 302 else 512
                else if v = 5441735 then 340 else
                  if v = 5451802 then 33 else 512
            else if v = 5472455 then 331 else
              if v < 5507091 then
                if v < 5478426 then
                  if v = 5478419 then 260 else 512
                else if v = 5478426 then 44 else
                  if v = 5480467 then 283 else 512
              else if v = 5507091 then 278 else
                if v < 5515466 then
                  if v = 5515463 then 326 else 512
                else if v = 5515466 then 110 else
                  if v = 5517331 then 265 else 512
          else if v = 5537994 then 99 else
            if v < 5804057 then
              if v < 5769241 then
                if v < 5638270 then
                  if v = 5546183 then 345 else 512
                else if v = 5638270 then 437 else
                  if v = 5640318 then 440 else 512
              else if v = 5769241 then 291 else
                if v < 5802186 then
                  if v = 5775562 then 121 else 512
                else if v = 5802186 then 116 else
                  if v = 5802189 then 380 else 512
            else if v = 5804057 then 307 else
              if v < 6097022 then
                if v < 5900462 then
                  if v = 5808333 then 364 else 512
                else if v = 5900462 then 480 else
                  if v = 5902510 then 493 else 512
              else if v = 6097022 then 416 else
                if v < 6228142 then
                  if v = 6099070 then 429 else 512
                else if v = 6228142 then 501 else
                  if v = 6230190 then 504 else 512
    else if v = 6359209 then 255 else
      if v < 7407818 then
        if v < 6850734 then
          if v < 6555674 then
            if v < 6428787 then
              if v < 6371454 then
                if v < 6365310 then
                  if v = 6361213 then 178 else 512
                else if v = 6365310 then 421 else
                  if v = 6371453 then 162 else 512
              else if v = 6371454 then 424 else
                if v < 6424595 then
                  if v = 6394025 then 239 else 512
                else if v = 6424595 then 287 else
                  if v = 6424781 then 383 else 512
            else if v = 6428787 then 140 else
              if v < 6434835 then
                if v < 6430835 then
                  if v = 6428797 then 174 else 512
                else if v = 6430835 then 147 else
                  if v = 6430925 then 367 else 512
              else if v = 6434835 then 256 else
                if v < 6490314 then
                  if v = 6434941 then 190 else 512
                else if v = 6490314 then 126 else
                  if v = 6529226 then 115 else 512
          else if v = 6555674 then 60 else
            if v < 6662163 then
              if v < 6631449 then
                if v < 6621299 then
                  if v = 6594586 then 49 else 512
                else if v = 6621299 then 129 else
                  if v = 6621353 then 227 else 512
              else if v = 6631449 then 288 else
                if v < 6656019 then
                  if v = 6631539 then 158 else 512
                else if v = 6656019 then 269 else
                  if v = 6656169 then 243 else 512
            else if v = 6662163 then 274 else
              if v < 6817917 then
                if v < 6686746 then
                  if v = 6662169 then 304 else 512
                else if v = 6686746 then 43 else
                  if v = 6725658 then 38 else 512
              else if v = 6817917 then 191 else
                if v < 6824061 then
                  if v = 6820009 then 242 else 512
                else if v = 6824061 then 175 else
                  if v = 6850729 then 226 else 512
        else if v = 6850734 then 488 else
          if v < 7079961 then
            if v < 7014525 then
              if v < 6957171 then
                if v < 6949031 then
                  if v = 6852782 then 485 else 512
                else if v = 6949031 then 200 else
                  if v = 6951027 then 133 else 512
              else if v = 6957171 then 154 else
                if v < 6959230 then
                  if v = 6957182 then 432 else 512
                else if v = 6959230 then 445 else
                  if v = 6979751 then 215 else 512
            else if v = 7014525 then 163 else
              if v < 7045287 then
                if v < 7020669 then
                  if v = 7014567 then 193 else 512
                else if v = 7020669 then 179 else
                  if v = 7020743 then 335 else 512
              else if v = 7045287 then 222 else
                if v < 7055559 then
                  if v = 7045325 then 354 else 512
                else if v = 7055559 then 336 else
                  if v = 7055565 then 370 else 512
          else if v = 7079961 then 317 else
            if v < 7145587 then
              if v < 7110825 then
                if v < 7084199 then
                  if v = 7080135 then 349 else 512
                else if v = 7084199 then 204 else
                  if v = 7084201 then 238 else 512
              else if v = 7110825 then 254 else
                if v < 7114777 then
                  if v = 7110855 then 322 else 512
                else if v = 7114777 then 301 else
                  if v = 7114919 then 211 else 512
            else if v = 7145587 then 136 else
              if v < 7182503 then
                if v < 7155827 then
                  if v = 7147687 then 197 else 512
                else if v = 7155827 then 151 else
                  if v = 7176366 then 509 else 512
              else if v = 7182503 then 218 else
                if v < 7276746 then
                  if v = 7182510 then 496 else 512
                else if v = 7276746 then 105 else
                  if v = 7315658 then 100 else 512
      else if v = 7407818 then 107 else
        if v < 7741565 then
          if v < 7604391 then
            if v < 7507993 then
              if v < 7477415 then
                if v < 7473177 then
                  if v = 7446730 then 102 else 512
                else if v = 7473177 then 319 else
                  if v = 7473351 then 351 else 512
              else if v = 7477415 then 206 else
                if v < 7504041 then
                  if v = 7477417 then 236 else 512
                else if v = 7504041 then 252 else
                  if v = 7504071 then 320 else 512
            else if v = 7507993 then 303 else
              if v < 7549043 then
                if v < 7538803 then
                  if v = 7508135 then 209 else 512
                else if v = 7538803 then 138 else
                  if v = 7540903 then 199 else 512
              else if v = 7549043 then 149 else
                if v < 7575719 then
                  if v = 7569582 then 511 else 512
                else if v = 7575719 then 216 else
                  if v = 7575726 then 498 else 512
          else if v = 7604391 then 202 else
            if v < 7676029 then
              if v < 7614590 then
                if v < 7612531 then
                  if v = 7606387 then 135 else 512
                else if v = 7612531 then 152 else
                  if v = 7612542 then 434 else 512
              else if v = 7614590 then 447 else
                if v < 7669885 then
                  if v = 7635111 then 213 else 512
                else if v = 7669885 then 161 else
                  if v = 7669927 then 195 else 512
            else if v = 7676029 then 177 else
              if v < 7710919 then
                if v < 7700647 then
                  if v = 7676103 then 333 else 512
                else if v = 7700647 then 220 else
                  if v = 7700685 then 352 else 512
              else if v = 7710919 then 338 else
                if v < 7735421 then
                  if v = 7710925 then 368 else 512
                else if v = 7735421 then 189 else
                  if v = 7737513 then 240 else 512
        else if v = 7741565 then 173 else
          if v < 8128531 then
            if v < 8063091 then
              if v < 7866394 then
                if v < 7768238 then
                  if v = 7768233 then 224 else 512
                else if v = 7768238 then 490 else
                  if v = 7770286 then 487 else 512
              else if v = 7866394 then 41 else
                if v < 7997466 then
                  if v = 7905306 then 36 else 512
                else if v = 7997466 then 62 else
                  if v = 8036378 then 51 else 512
            else if v = 8063091 then 131 else
              if v < 8097811 then
                if v < 8073241 then
                  if v = 8063145 then 225 else 512
                else if v = 8073241 then 290 else
                  if v = 8073331 then 156 else 512
              else if v = 8097811 then 271 else
                if v < 8103955 then
                  if v = 8097961 then 241 else 512
                else if v = 8103955 then 272 else
                  if v = 8103961 then 306 else 512
          else if v = 8128531 then 285 else
            if v < 8194250 then
              if v < 8134771 then
                if v < 8132723 then
                  if v = 8128717 then 381 else 512
                else if v = 8132723 then 142 else
                  if v = 8132733 then 172 else 512
              else if v = 8134771 then 145 else
                if v < 8138771 then
                  if v = 8134861 then 365 else 512
                else if v = 8138771 then 258 else
                  if v = 8138877 then 188 else 512
            else if v = 8194250 then 124 else
              if v < 8331390 then
                if v < 8325289 then
                  if v = 8233162 then 113 else 512
                else if v = 8325289 then 253 else
                  if v = 8327293 then 176 else 512
              else if v = 8331390 then 423 else
                if v < 8337534 then
                  if v = 8337533 then 160 else 512
                else if v = 8337534 then 426 else
                  if v = 8360105 then 237 else 512

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
-- Check all512 original word evaluations on coordinate16.
/-- Every displayed point is the full stated binary source-word image. -/
theorem generatedNinth_affine_kernel_orbit_source : ∀ k : Fin 512,
    generatedNinthAffineKernelMaskWord (generatedNinthAffineKernelSourceWord k) 16 =
      generatedNinthAffineKernelOrbitImage k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Retain exact finite labels and genuine24-bit bounds.
/-- Every source point has its exact original index and fits the full binary carrier. -/
theorem generatedNinth_affine_kernel_orbit_lookup : ∀ k : Fin 512,
    generatedNinthAffineKernelOrbitLookup (generatedNinthAffineKernelOrbitImage k) = k.val ∧
      generatedNinthAffineKernelOrbitImage k < 2 ^ 24 := by
  decide +kernel

/-- The512 full binary source-word images are pairwise distinct. -/
theorem generatedNinth_affine_kernel_orbit_image_injective :
    Function.Injective generatedNinthAffineKernelOrbitImage := by
  intro a b h
  apply Fin.ext
  exact (generatedNinth_affine_kernel_orbit_lookup a).1.symm.trans
    ((congrArg generatedNinthAffineKernelOrbitLookup h).trans
      (generatedNinth_affine_kernel_orbit_lookup b).1)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
