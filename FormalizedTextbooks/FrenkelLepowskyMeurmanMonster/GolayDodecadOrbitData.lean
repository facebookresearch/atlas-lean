/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayDodecads
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2ThreePointWords

/-! An acyclic orbit certificate on the actual 1288 dodecads outside coordinate zero.
All transitions use the original strong generators and the published Golay encoder. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Original twelve-bit coefficient labels in orbit order. -/
def golayDodecadOrbitLabel (n : ℕ) : ℕ :=
  (if n < 644 then
    (if n < 322 then
      (if n < 161 then
        (if n < 80 then
          (if n < 40 then
            (if n < 20 then
              (if n < 10 then
                (if n < 5 then
                  (if n < 2 then
                    (if n < 1 then
                      17
                    else
                      700)
                  else
                    (if n < 3 then
                      1370
                    else
                      (if n < 4 then
                        1907
                      else
                        191)))
                else
                  (if n < 7 then
                    (if n < 6 then
                      1774
                    else
                      1971)
                  else
                    (if n < 8 then
                      20
                    else
                      (if n < 9 then
                        122
                      else
                        177))))
              else
                (if n < 15 then
                  (if n < 12 then
                    (if n < 11 then
                      55
                    else
                      18)
                  else
                    (if n < 13 then
                      49
                    else
                      (if n < 14 then
                        1612
                      else
                        396)))
                else
                  (if n < 17 then
                    (if n < 16 then
                      1502
                    else
                      623)
                  else
                    (if n < 18 then
                      1379
                    else
                      (if n < 19 then
                        513
                      else
                        1450)))))
            else
              (if n < 30 then
                (if n < 25 then
                  (if n < 22 then
                    (if n < 21 then
                      618
                    else
                      695)
                  else
                    (if n < 23 then
                      762
                    else
                      (if n < 24 then
                        746
                      else
                        1015)))
                else
                  (if n < 27 then
                    (if n < 26 then
                      184
                    else
                      629)
                  else
                    (if n < 28 then
                      954
                    else
                      (if n < 29 then
                        693
                      else
                        1353))))
              else
                (if n < 35 then
                  (if n < 32 then
                    (if n < 31 then
                      611
                    else
                      1463)
                  else
                    (if n < 33 then
                      1453
                    else
                      (if n < 34 then
                        1427
                      else
                        1365)))
                else
                  (if n < 37 then
                    (if n < 36 then
                      1462
                    else
                      1690)
                  else
                    (if n < 38 then
                      2013
                    else
                      (if n < 39 then
                        1837
                      else
                        143))))))
          else
            (if n < 60 then
              (if n < 50 then
                (if n < 45 then
                  (if n < 42 then
                    (if n < 41 then
                      40
                    else
                      1897)
                  else
                    (if n < 43 then
                      2010
                    else
                      (if n < 44 then
                        1978
                      else
                        1875)))
                else
                  (if n < 47 then
                    (if n < 46 then
                      1957
                    else
                      1446)
                  else
                    (if n < 48 then
                      1683
                    else
                      (if n < 49 then
                        225
                      else
                        1974))))
              else
                (if n < 55 then
                  (if n < 52 then
                    (if n < 51 then
                      36
                    else
                      29)
                  else
                    (if n < 53 then
                      197
                    else
                      (if n < 54 then
                        159
                      else
                        239)))
                else
                  (if n < 57 then
                    (if n < 56 then
                      542
                    else
                      257)
                  else
                    (if n < 58 then
                      1686
                    else
                      (if n < 59 then
                        1554
                      else
                        1605)))))
            else
              (if n < 70 then
                (if n < 65 then
                  (if n < 62 then
                    (if n < 61 then
                      1614
                    else
                      1789)
                  else
                    (if n < 63 then
                      1630
                    else
                      (if n < 64 then
                        1406
                      else
                        1706)))
                else
                  (if n < 67 then
                    (if n < 66 then
                      72
                    else
                      1832)
                  else
                    (if n < 68 then
                      1871
                    else
                      (if n < 69 then
                        1993
                      else
                        1955))))
              else
                (if n < 75 then
                  (if n < 72 then
                    (if n < 71 then
                      2021
                    else
                      1044)
                  else
                    (if n < 73 then
                      1533
                    else
                      (if n < 74 then
                        1046
                      else
                        216)))
                else
                  (if n < 77 then
                    (if n < 76 then
                      1941
                    else
                      228)
                  else
                    (if n < 78 then
                      1877
                    else
                      (if n < 79 then
                        116
                      else
                        182)))))))
        else
          (if n < 120 then
            (if n < 100 then
              (if n < 90 then
                (if n < 85 then
                  (if n < 82 then
                    (if n < 81 then
                      62
                    else
                      24)
                  else
                    (if n < 83 then
                      56
                    else
                      (if n < 84 then
                        1924
                      else
                        1329)))
                else
                  (if n < 87 then
                    (if n < 86 then
                      794
                    else
                      2043)
                  else
                    (if n < 88 then
                      1910
                    else
                      (if n < 89 then
                        151
                      else
                        107))))
              else
                (if n < 95 then
                  (if n < 92 then
                    (if n < 91 then
                      101
                    else
                      166)
                  else
                    (if n < 93 then
                      636
                    else
                      (if n < 94 then
                        1530
                      else
                        977)))
                else
                  (if n < 97 then
                    (if n < 96 then
                      98
                    else
                      1886)
                  else
                    (if n < 98 then
                      45
                    else
                      (if n < 99 then
                        194
                      else
                        146)))))
            else
              (if n < 110 then
                (if n < 105 then
                  (if n < 102 then
                    (if n < 101 then
                      1284
                    else
                      471)
                  else
                    (if n < 103 then
                      1851
                    else
                      (if n < 104 then
                        59
                      else
                        1004)))
                else
                  (if n < 107 then
                    (if n < 106 then
                      226
                    else
                      498)
                  else
                    (if n < 108 then
                      95
                    else
                      (if n < 109 then
                        2028
                      else
                        121))))
              else
                (if n < 115 then
                  (if n < 112 then
                    (if n < 111 then
                      187
                    else
                      61)
                  else
                    (if n < 113 then
                      52
                    else
                      (if n < 114 then
                        764
                      else
                        1402)))
                else
                  (if n < 117 then
                    (if n < 116 then
                      1075
                    else
                      1920)
                  else
                    (if n < 118 then
                      124
                    else
                      (if n < 119 then
                        148
                      else
                        236))))))
          else
            (if n < 140 then
              (if n < 130 then
                (if n < 125 then
                  (if n < 122 then
                    (if n < 121 then
                      111
                    else
                      39)
                  else
                    (if n < 123 then
                      50
                    else
                      (if n < 124 then
                        33
                      else
                        1249)))
                else
                  (if n < 127 then
                    (if n < 126 then
                      1324
                    else
                      286)
                  else
                    (if n < 128 then
                      419
                    else
                      (if n < 129 then
                        509
                      else
                        346))))
              else
                (if n < 135 then
                  (if n < 132 then
                    (if n < 131 then
                      1607
                    else
                      1767)
                  else
                    (if n < 133 then
                      1721
                    else
                      (if n < 134 then
                        1660
                      else
                        1674)))
                else
                  (if n < 137 then
                    (if n < 136 then
                      478
                    else
                      497)
                  else
                    (if n < 138 then
                      1648
                    else
                      (if n < 139 then
                        415
                      else
                        302)))))
            else
              (if n < 150 then
                (if n < 145 then
                  (if n < 142 then
                    (if n < 141 then
                      451
                    else
                      444)
                  else
                    (if n < 143 then
                      458
                    else
                      (if n < 144 then
                        1420
                      else
                        1293)))
                else
                  (if n < 147 then
                    (if n < 146 then
                      671
                    else
                      1430)
                  else
                    (if n < 148 then
                      1401
                    else
                      (if n < 149 then
                        1500
                      else
                        1399))))
              else
                (if n < 155 then
                  (if n < 152 then
                    (if n < 151 then
                      804
                    else
                      588)
                  else
                    (if n < 153 then
                      1326
                    else
                      (if n < 154 then
                        546
                      else
                        595)))
                else
                  (if n < 158 then
                    (if n < 156 then
                      657
                    else
                      (if n < 157 then
                        607
                      else
                        1283))
                  else
                    (if n < 159 then
                      209
                    else
                      (if n < 160 then
                        1375
                      else
                        1475))))))))
      else
        (if n < 241 then
          (if n < 201 then
            (if n < 181 then
              (if n < 171 then
                (if n < 166 then
                  (if n < 163 then
                    (if n < 162 then
                      1456
                    else
                      1429)
                  else
                    (if n < 164 then
                      609
                    else
                      (if n < 165 then
                        1000
                      else
                        1504)))
                else
                  (if n < 168 then
                    (if n < 167 then
                      680
                    else
                      573)
                  else
                    (if n < 169 then
                      775
                    else
                      (if n < 170 then
                        1098
                      else
                        980))))
              else
                (if n < 176 then
                  (if n < 173 then
                    (if n < 172 then
                      1465
                    else
                      659)
                  else
                    (if n < 174 then
                      1307
                    else
                      (if n < 175 then
                        1487
                      else
                        1494)))
                else
                  (if n < 178 then
                    (if n < 177 then
                      1881
                    else
                      899)
                  else
                    (if n < 179 then
                      986
                    else
                      (if n < 180 then
                        1162
                      else
                        1499)))))
            else
              (if n < 191 then
                (if n < 186 then
                  (if n < 183 then
                    (if n < 182 then
                      605
                    else
                      662)
                  else
                    (if n < 184 then
                      597
                    else
                      (if n < 185 then
                        1719
                      else
                        855)))
                else
                  (if n < 188 then
                    (if n < 187 then
                      1334
                    else
                      676)
                  else
                    (if n < 189 then
                      621
                    else
                      (if n < 190 then
                        756
                      else
                        699))))
              else
                (if n < 196 then
                  (if n < 193 then
                    (if n < 192 then
                      749
                    else
                      995)
                  else
                    (if n < 194 then
                      410
                    else
                      (if n < 195 then
                        1403
                      else
                        741)))
                else
                  (if n < 198 then
                    (if n < 197 then
                      745
                    else
                      743)
                  else
                    (if n < 199 then
                      593
                    else
                      (if n < 200 then
                        614
                      else
                        2009))))))
          else
            (if n < 221 then
              (if n < 211 then
                (if n < 206 then
                  (if n < 203 then
                    (if n < 202 then
                      771
                    else
                      1080)
                  else
                    (if n < 204 then
                      628
                    else
                      (if n < 205 then
                        1034
                      else
                        692)))
                else
                  (if n < 208 then
                    (if n < 207 then
                      1352
                    else
                      1491)
                  else
                    (if n < 209 then
                      668
                    else
                      (if n < 210 then
                        744
                      else
                        592))))
              else
                (if n < 216 then
                  (if n < 213 then
                    (if n < 212 then
                      757
                    else
                      598)
                  else
                    (if n < 214 then
                      1799
                    else
                      (if n < 215 then
                        1557
                      else
                        1240)))
                else
                  (if n < 218 then
                    (if n < 217 then
                      1303
                    else
                      937)
                  else
                    (if n < 219 then
                      1109
                    else
                      (if n < 220 then
                        989
                      else
                        806)))))
            else
              (if n < 231 then
                (if n < 226 then
                  (if n < 223 then
                    (if n < 222 then
                      777
                    else
                      833)
                  else
                    (if n < 224 then
                      1019
                    else
                      (if n < 225 then
                        877
                      else
                        1895)))
                else
                  (if n < 228 then
                    (if n < 227 then
                      1803
                    else
                      206)
                  else
                    (if n < 229 then
                      1669
                    else
                      (if n < 230 then
                        1173
                      else
                        1434))))
              else
                (if n < 236 then
                  (if n < 233 then
                    (if n < 232 then
                      558
                    else
                      555)
                  else
                    (if n < 234 then
                      645
                    else
                      (if n < 235 then
                        586
                      else
                        681)))
                else
                  (if n < 238 then
                    (if n < 237 then
                      996
                    else
                      1048)
                  else
                    (if n < 239 then
                      871
                    else
                      (if n < 240 then
                        940
                      else
                        933)))))))
        else
          (if n < 281 then
            (if n < 261 then
              (if n < 251 then
                (if n < 246 then
                  (if n < 243 then
                    (if n < 242 then
                      998
                    else
                      1717)
                  else
                    (if n < 244 then
                      678
                    else
                      (if n < 245 then
                        702
                      else
                        758)))
                else
                  (if n < 248 then
                    (if n < 247 then
                      698
                    else
                      923)
                  else
                    (if n < 249 then
                      1419
                    else
                      (if n < 250 then
                        1310
                      else
                        1350))))
              else
                (if n < 256 then
                  (if n < 253 then
                    (if n < 252 then
                      1411
                    else
                      890)
                  else
                    (if n < 254 then
                      1361
                    else
                      (if n < 255 then
                        765
                      else
                        1404)))
                else
                  (if n < 258 then
                    (if n < 257 then
                      600
                    else
                      697)
                  else
                    (if n < 259 then
                      661
                    else
                      (if n < 260 then
                        439
                      else
                        1509)))))
            else
              (if n < 271 then
                (if n < 266 then
                  (if n < 263 then
                    (if n < 262 then
                      1751
                    else
                      533)
                  else
                    (if n < 264 then
                      1386
                    else
                      (if n < 265 then
                        1517
                      else
                        1619)))
                else
                  (if n < 268 then
                    (if n < 267 then
                      68
                    else
                      895)
                  else
                    (if n < 269 then
                      690
                    else
                      (if n < 270 then
                        850
                      else
                        575))))
              else
                (if n < 276 then
                  (if n < 273 then
                    (if n < 272 then
                      1358
                    else
                      1476)
                  else
                    (if n < 274 then
                      1438
                    else
                      (if n < 275 then
                        1523
                      else
                        1059)))
                else
                  (if n < 278 then
                    (if n < 277 then
                      753
                    else
                      1344)
                  else
                    (if n < 279 then
                      722
                    else
                      (if n < 280 then
                        1516
                      else
                        1443))))))
          else
            (if n < 301 then
              (if n < 291 then
                (if n < 286 then
                  (if n < 283 then
                    (if n < 282 then
                      1525
                    else
                      683)
                  else
                    (if n < 284 then
                      1527
                    else
                      (if n < 285 then
                        983
                      else
                        1354)))
                else
                  (if n < 288 then
                    (if n < 287 then
                      1471
                    else
                      1449)
                  else
                    (if n < 289 then
                      1436
                    else
                      (if n < 290 then
                        795
                      else
                        1030))))
              else
                (if n < 296 then
                  (if n < 293 then
                    (if n < 292 then
                      1445
                    else
                      1387)
                  else
                    (if n < 294 then
                      1512
                    else
                      (if n < 295 then
                        1417
                      else
                        1914)))
                else
                  (if n < 298 then
                    (if n < 297 then
                      342
                    else
                      1736)
                  else
                    (if n < 299 then
                      1575
                    else
                      (if n < 300 then
                        403
                      else
                        1734)))))
            else
              (if n < 311 then
                (if n < 306 then
                  (if n < 303 then
                    (if n < 302 then
                      1782
                    else
                      1685)
                  else
                    (if n < 304 then
                      1638
                    else
                      (if n < 305 then
                        127
                      else
                        1930)))
                else
                  (if n < 308 then
                    (if n < 307 then
                      1847
                    else
                      1864)
                  else
                    (if n < 309 then
                      2014
                    else
                      (if n < 310 then
                        1915
                      else
                        1566))))
              else
                (if n < 316 then
                  (if n < 313 then
                    (if n < 312 then
                      511
                    else
                      1947)
                  else
                    (if n < 314 then
                      1812
                    else
                      (if n < 315 then
                        1822
                      else
                        1819)))
                else
                  (if n < 319 then
                    (if n < 317 then
                      476
                    else
                      (if n < 318 then
                        1382
                      else
                        1165))
                  else
                    (if n < 320 then
                      1830
                    else
                      (if n < 321 then
                        201
                      else
                        234)))))))))
    else
      (if n < 483 then
        (if n < 402 then
          (if n < 362 then
            (if n < 342 then
              (if n < 332 then
                (if n < 327 then
                  (if n < 324 then
                    (if n < 323 then
                      175
                    else
                      207)
                  else
                    (if n < 325 then
                      1096
                    else
                      (if n < 326 then
                        1818
                      else
                        1963)))
                else
                  (if n < 329 then
                    (if n < 328 then
                      223
                    else
                      570)
                  else
                    (if n < 330 then
                      827
                    else
                      (if n < 331 then
                        1888
                      else
                        1923))))
              else
                (if n < 337 then
                  (if n < 334 then
                    (if n < 333 then
                      1862
                    else
                      1939)
                  else
                    (if n < 335 then
                      1731
                    else
                      (if n < 336 then
                        568
                      else
                        375)))
                else
                  (if n < 339 then
                    (if n < 338 then
                      2041
                    else
                      214)
                  else
                    (if n < 340 then
                      1859
                    else
                      (if n < 341 then
                        2005
                      else
                        1989)))))
            else
              (if n < 352 then
                (if n < 347 then
                  (if n < 344 then
                    (if n < 343 then
                      2022
                    else
                      1722)
                  else
                    (if n < 345 then
                      849
                    else
                      (if n < 346 then
                        168
                      else
                        2047)))
                else
                  (if n < 349 then
                    (if n < 348 then
                      1796
                    else
                      1962)
                  else
                    (if n < 350 then
                      1973
                    else
                      (if n < 351 then
                        853
                      else
                        583))))
              else
                (if n < 357 then
                  (if n < 354 then
                    (if n < 353 then
                      2037
                    else
                      779)
                  else
                    (if n < 355 then
                      420
                    else
                      (if n < 356 then
                        602
                      else
                        917)))
                else
                  (if n < 359 then
                    (if n < 358 then
                      1515
                    else
                      1296)
                  else
                    (if n < 360 then
                      1482
                    else
                      (if n < 361 then
                        1433
                      else
                        1664))))))
          else
            (if n < 382 then
              (if n < 372 then
                (if n < 367 then
                  (if n < 364 then
                    (if n < 363 then
                      1724
                    else
                      1653)
                  else
                    (if n < 365 then
                      1743
                    else
                      (if n < 366 then
                        1786
                      else
                        1781)))
                else
                  (if n < 369 then
                    (if n < 368 then
                      897
                    else
                      67)
                  else
                    (if n < 370 then
                      210
                    else
                      (if n < 371 then
                        81
                      else
                        982))))
              else
                (if n < 377 then
                  (if n < 374 then
                    (if n < 373 then
                      1549
                    else
                      356)
                  else
                    (if n < 375 then
                      1801
                    else
                      (if n < 376 then
                        1984
                      else
                        1961)))
                else
                  (if n < 379 then
                    (if n < 378 then
                      1092
                    else
                      1341)
                  else
                    (if n < 380 then
                      153
                    else
                      (if n < 381 then
                        688
                      else
                        669)))))
            else
              (if n < 392 then
                (if n < 387 then
                  (if n < 384 then
                    (if n < 383 then
                      1948
                    else
                      1711)
                  else
                    (if n < 385 then
                      1964
                    else
                      (if n < 386 then
                        113
                      else
                        30)))
                else
                  (if n < 389 then
                    (if n < 388 then
                      1544
                    else
                      373)
                  else
                    (if n < 390 then
                      1959
                    else
                      (if n < 391 then
                        1723
                      else
                        1825))))
              else
                (if n < 397 then
                  (if n < 394 then
                    (if n < 393 then
                      79
                    else
                      250)
                  else
                    (if n < 395 then
                      73
                    else
                      (if n < 396 then
                        460
                      else
                        1414)))
                else
                  (if n < 399 then
                    (if n < 398 then
                      303
                    else
                      1838)
                  else
                    (if n < 400 then
                      1846
                    else
                      (if n < 401 then
                        178
                      else
                        195)))))))
        else
          (if n < 442 then
            (if n < 422 then
              (if n < 412 then
                (if n < 407 then
                  (if n < 404 then
                    (if n < 403 then
                      213
                    else
                      255)
                  else
                    (if n < 405 then
                      1526
                    else
                      (if n < 406 then
                        1792
                      else
                        108)))
                else
                  (if n < 409 then
                    (if n < 408 then
                      813
                    else
                      382)
                  else
                    (if n < 410 then
                      525
                    else
                      (if n < 411 then
                        574
                      else
                        1210))))
              else
                (if n < 417 then
                  (if n < 414 then
                    (if n < 413 then
                      299
                    else
                      274)
                  else
                    (if n < 415 then
                      660
                    else
                      (if n < 416 then
                        1673
                      else
                        1659)))
                else
                  (if n < 419 then
                    (if n < 418 then
                      1779
                    else
                      1689)
                  else
                    (if n < 420 then
                      1788
                    else
                      (if n < 421 then
                        1218
                      else
                        1559)))))
            else
              (if n < 432 then
                (if n < 427 then
                  (if n < 424 then
                    (if n < 423 then
                      1585
                    else
                      1588)
                  else
                    (if n < 425 then
                      581
                    else
                      (if n < 426 then
                        935
                      else
                        1702)))
                else
                  (if n < 429 then
                    (if n < 428 then
                      1626
                    else
                      1602)
                  else
                    (if n < 430 then
                      1658
                    else
                      (if n < 431 then
                        1821
                      else
                        380))))
              else
                (if n < 437 then
                  (if n < 434 then
                    (if n < 433 then
                      1693
                    else
                      1539)
                  else
                    (if n < 435 then
                      1765
                    else
                      (if n < 436 then
                        1661
                      else
                        1678)))
                else
                  (if n < 439 then
                    (if n < 438 then
                      1642
                    else
                      1643)
                  else
                    (if n < 440 then
                      1805
                    else
                      (if n < 441 then
                        606
                      else
                        1246))))))
          else
            (if n < 462 then
              (if n < 452 then
                (if n < 447 then
                  (if n < 444 then
                    (if n < 443 then
                      321
                    else
                      114)
                  else
                    (if n < 445 then
                      1536
                    else
                      (if n < 446 then
                        1718
                      else
                        1598)))
                else
                  (if n < 449 then
                    (if n < 448 then
                      1628
                    else
                      1668)
                  else
                    (if n < 450 then
                      1645
                    else
                      (if n < 451 then
                        1726
                      else
                        1410))))
              else
                (if n < 457 then
                  (if n < 454 then
                    (if n < 453 then
                      1405
                    else
                      1454)
                  else
                    (if n < 455 then
                      1017
                    else
                      (if n < 456 then
                        408
                      else
                        358)))
                else
                  (if n < 459 then
                    (if n < 458 then
                      1579
                    else
                      491)
                  else
                    (if n < 460 then
                      259
                    else
                      (if n < 461 then
                        1697
                      else
                        1753)))))
            else
              (if n < 472 then
                (if n < 467 then
                  (if n < 464 then
                    (if n < 463 then
                      1701
                    else
                      1750)
                  else
                    (if n < 465 then
                      1064
                    else
                      (if n < 466 then
                        424
                      else
                        132)))
                else
                  (if n < 469 then
                    (if n < 468 then
                      84
                    else
                      130)
                  else
                    (if n < 470 then
                      666
                    else
                      (if n < 471 then
                        1810
                      else
                        1540))))
              else
                (if n < 477 then
                  (if n < 474 then
                    (if n < 473 then
                      797
                    else
                      1794)
                  else
                    (if n < 475 then
                      1809
                    else
                      (if n < 476 then
                        1935
                      else
                        1936)))
                else
                  (if n < 480 then
                    (if n < 478 then
                      1903
                    else
                      (if n < 479 then
                        283
                      else
                        1879))
                  else
                    (if n < 481 then
                      297
                    else
                      (if n < 482 then
                        2026
                      else
                        1990))))))))
      else
        (if n < 563 then
          (if n < 523 then
            (if n < 503 then
              (if n < 493 then
                (if n < 488 then
                  (if n < 485 then
                    (if n < 484 then
                      1390
                    else
                      1610)
                  else
                    (if n < 486 then
                      2030
                    else
                      (if n < 487 then
                        88
                      else
                        2038)))
                else
                  (if n < 490 then
                    (if n < 489 then
                      694
                    else
                      997)
                  else
                    (if n < 491 then
                      1867
                    else
                      (if n < 492 then
                        1892
                      else
                        1808))))
              else
                (if n < 498 then
                  (if n < 495 then
                    (if n < 494 then
                      1891
                    else
                      1113)
                  else
                    (if n < 496 then
                      1269
                    else
                      (if n < 497 then
                        1057
                      else
                        1635)))
                else
                  (if n < 500 then
                    (if n < 499 then
                      815
                    else
                      750)
                  else
                    (if n < 501 then
                      1288
                    else
                      (if n < 502 then
                        1389
                      else
                        1208)))))
            else
              (if n < 513 then
                (if n < 508 then
                  (if n < 505 then
                    (if n < 504 then
                      1002
                    else
                      1193)
                  else
                    (if n < 506 then
                      1271
                    else
                      (if n < 507 then
                        1049
                      else
                        1084)))
                else
                  (if n < 510 then
                    (if n < 509 then
                      1883
                    else
                      710)
                  else
                    (if n < 511 then
                      1189
                    else
                      (if n < 512 then
                        1252
                      else
                        2034))))
              else
                (if n < 518 then
                  (if n < 515 then
                    (if n < 514 then
                      1977
                    else
                      1140)
                  else
                    (if n < 516 then
                      1797
                    else
                      (if n < 517 then
                        131
                      else
                        104)))
                else
                  (if n < 520 then
                    (if n < 519 then
                      928
                    else
                      156)
                  else
                    (if n < 521 then
                      1884
                    else
                      (if n < 522 then
                        46
                      else
                        504))))))
          else
            (if n < 543 then
              (if n < 533 then
                (if n < 528 then
                  (if n < 525 then
                    (if n < 524 then
                      1112
                    else
                      696)
                  else
                    (if n < 526 then
                      219
                    else
                      (if n < 527 then
                        1979
                      else
                        233)))
                else
                  (if n < 530 then
                    (if n < 529 then
                      102
                    else
                      43)
                  else
                    (if n < 531 then
                      34
                    else
                      (if n < 532 then
                        136
                      else
                        2029))))
              else
                (if n < 538 then
                  (if n < 535 then
                    (if n < 534 then
                      1944
                    else
                      1992)
                  else
                    (if n < 536 then
                      1233
                    else
                      (if n < 537 then
                        736
                      else
                        1314)))
                else
                  (if n < 540 then
                    (if n < 539 then
                      1313
                    else
                      755)
                  else
                    (if n < 541 then
                      1254
                    else
                      (if n < 542 then
                        836
                      else
                        805)))))
            else
              (if n < 553 then
                (if n < 548 then
                  (if n < 545 then
                    (if n < 544 then
                      822
                    else
                      857)
                  else
                    (if n < 546 then
                      2039
                    else
                      (if n < 547 then
                        886
                      else
                        1597)))
                else
                  (if n < 550 then
                    (if n < 549 then
                      884
                    else
                      1397)
                  else
                    (if n < 551 then
                      1769
                    else
                      (if n < 552 then
                        253
                      else
                        1336))))
              else
                (if n < 558 then
                  (if n < 555 then
                    (if n < 554 then
                      1129
                    else
                      119)
                  else
                    (if n < 556 then
                      1495
                    else
                      (if n < 557 then
                        1848
                      else
                        326)))
                else
                  (if n < 560 then
                    (if n < 559 then
                      1547
                    else
                      137)
                  else
                    (if n < 561 then
                      90
                    else
                      (if n < 562 then
                        173
                      else
                        246)))))))
        else
          (if n < 603 then
            (if n < 583 then
              (if n < 573 then
                (if n < 568 then
                  (if n < 565 then
                    (if n < 564 then
                      220
                    else
                      924)
                  else
                    (if n < 566 then
                      738
                    else
                      (if n < 567 then
                        649
                      else
                        682)))
                else
                  (if n < 570 then
                    (if n < 569 then
                      823
                    else
                      1050)
                  else
                    (if n < 571 then
                      1493
                    else
                      (if n < 572 then
                        957
                      else
                        978))))
              else
                (if n < 578 then
                  (if n < 575 then
                    (if n < 574 then
                      881
                    else
                      1854)
                  else
                    (if n < 576 then
                      862
                    else
                      (if n < 577 then
                        1134
                      else
                        1917)))
                else
                  (if n < 580 then
                    (if n < 579 then
                      1982
                    else
                      1151)
                  else
                    (if n < 581 then
                      27
                    else
                      (if n < 582 then
                        860
                      else
                        1600)))))
            else
              (if n < 593 then
                (if n < 588 then
                  (if n < 585 then
                    (if n < 584 then
                      241
                    else
                      876)
                  else
                    (if n < 586 then
                      1552
                    else
                      (if n < 587 then
                        1981
                      else
                        1840)))
                else
                  (if n < 590 then
                    (if n < 589 then
                      244
                    else
                      747)
                  else
                    (if n < 591 then
                      1349
                    else
                      (if n < 592 then
                        1304
                      else
                        308))))
              else
                (if n < 598 then
                  (if n < 595 then
                    (if n < 594 then
                      507
                    else
                      381)
                  else
                    (if n < 596 then
                      502
                    else
                      (if n < 597 then
                        873
                      else
                        441)))
                else
                  (if n < 600 then
                    (if n < 599 then
                      2003
                    else
                      1831)
                  else
                    (if n < 601 then
                      1081
                    else
                      (if n < 602 then
                        1820
                      else
                        364))))))
          else
            (if n < 623 then
              (if n < 613 then
                (if n < 608 then
                  (if n < 605 then
                    (if n < 604 then
                      831
                    else
                      798)
                  else
                    (if n < 606 then
                      858
                    else
                      (if n < 607 then
                        955
                      else
                        880)))
                else
                  (if n < 610 then
                    (if n < 609 then
                      796
                    else
                      1280)
                  else
                    (if n < 611 then
                      97
                    else
                      (if n < 612 then
                        1565
                      else
                        428))))
              else
                (if n < 618 then
                  (if n < 615 then
                    (if n < 614 then
                      376
                    else
                      357)
                  else
                    (if n < 616 then
                      430
                    else
                      (if n < 617 then
                        465
                      else
                        1878)))
                else
                  (if n < 620 then
                    (if n < 619 then
                      243
                    else
                      86)
                  else
                    (if n < 621 then
                      1042
                    else
                      (if n < 622 then
                        318
                      else
                        275)))))
            else
              (if n < 633 then
                (if n < 628 then
                  (if n < 625 then
                    (if n < 624 then
                      93
                    else
                      2011)
                  else
                    (if n < 626 then
                      1817
                    else
                      (if n < 627 then
                        1882
                      else
                        1748)))
                else
                  (if n < 630 then
                    (if n < 629 then
                      1435
                    else
                      2027)
                  else
                    (if n < 631 then
                      196
                    else
                      (if n < 632 then
                        133
                      else
                        181))))
              else
                (if n < 638 then
                  (if n < 635 then
                    (if n < 634 then
                      163
                    else
                      1416)
                  else
                    (if n < 636 then
                      987
                    else
                      (if n < 637 then
                        1850
                      else
                        164)))
                else
                  (if n < 641 then
                    (if n < 639 then
                      1911
                    else
                      (if n < 640 then
                        2042
                      else
                        231))
                  else
                    (if n < 642 then
                      752
                    else
                      (if n < 643 then
                        1316
                      else
                        477))))))))))
  else
    (if n < 966 then
      (if n < 805 then
        (if n < 724 then
          (if n < 684 then
            (if n < 664 then
              (if n < 654 then
                (if n < 649 then
                  (if n < 646 then
                    (if n < 645 then
                      1951
                    else
                      1108)
                  else
                    (if n < 647 then
                      1501
                    else
                      (if n < 648 then
                        1958
                      else
                        1150)))
                else
                  (if n < 651 then
                    (if n < 650 then
                      610
                    else
                      641)
                  else
                    (if n < 652 then
                      604
                    else
                      (if n < 653 then
                        620
                      else
                        748))))
              else
                (if n < 659 then
                  (if n < 656 then
                    (if n < 655 then
                      951
                    else
                      1016)
                  else
                    (if n < 657 then
                      646
                    else
                      (if n < 658 then
                        739
                      else
                        1395)))
                else
                  (if n < 661 then
                    (if n < 660 then
                      882
                    else
                      872)
                  else
                    (if n < 662 then
                      1135
                    else
                      (if n < 663 then
                        1231
                      else
                        1082)))))
            else
              (if n < 674 then
                (if n < 669 then
                  (if n < 666 then
                    (if n < 665 then
                      1061
                    else
                      1997)
                  else
                    (if n < 667 then
                      1824
                    else
                      (if n < 668 then
                        1826
                      else
                        1790)))
                else
                  (if n < 671 then
                    (if n < 670 then
                      188
                    else
                      170)
                  else
                    (if n < 672 then
                      1172
                    else
                      (if n < 673 then
                        1012
                      else
                        200))))
              else
                (if n < 679 then
                  (if n < 676 then
                    (if n < 675 then
                      248
                    else
                      78)
                  else
                    (if n < 677 then
                      1214
                    else
                      (if n < 678 then
                        1728
                      else
                        1795)))
                else
                  (if n < 681 then
                    (if n < 680 then
                      142
                    else
                      69)
                  else
                    (if n < 682 then
                      316
                    else
                      (if n < 683 then
                        1398
                      else
                        1300))))))
          else
            (if n < 704 then
              (if n < 694 then
                (if n < 689 then
                  (if n < 686 then
                    (if n < 685 then
                      1141
                    else
                      154)
                  else
                    (if n < 687 then
                      1998
                    else
                      (if n < 688 then
                        1900
                      else
                        401)))
                else
                  (if n < 691 then
                    (if n < 690 then
                      426
                    else
                      979)
                  else
                    (if n < 692 then
                      1196
                    else
                      (if n < 693 then
                        883
                      else
                        1005))))
              else
                (if n < 699 then
                  (if n < 696 then
                    (if n < 695 then
                      1111
                    else
                      1234)
                  else
                    (if n < 697 then
                      1105
                    else
                      (if n < 698 then
                        1321
                      else
                        1340)))
                else
                  (if n < 701 then
                    (if n < 700 then
                      1306
                    else
                      269)
                  else
                    (if n < 702 then
                      500
                    else
                      (if n < 703 then
                        469
                      else
                        893)))))
            else
              (if n < 714 then
                (if n < 709 then
                  (if n < 706 then
                    (if n < 705 then
                      365
                    else
                      370)
                  else
                    (if n < 707 then
                      363
                    else
                      (if n < 708 then
                        1041
                      else
                        406)))
                else
                  (if n < 711 then
                    (if n < 710 then
                      377
                    else
                      310)
                  else
                    (if n < 712 then
                      271
                    else
                      (if n < 713 then
                        341
                      else
                        438))))
              else
                (if n < 719 then
                  (if n < 716 then
                    (if n < 715 then
                      1594
                    else
                      344)
                  else
                    (if n < 717 then
                      393
                    else
                      (if n < 718 then
                        1772
                      else
                        1677)))
                else
                  (if n < 721 then
                    (if n < 720 then
                      422
                    else
                      1787)
                  else
                    (if n < 722 then
                      1629
                    else
                      (if n < 723 then
                        1771
                      else
                        1763)))))))
        else
          (if n < 764 then
            (if n < 744 then
              (if n < 734 then
                (if n < 729 then
                  (if n < 726 then
                    (if n < 725 then
                      1201
                    else
                      974)
                  else
                    (if n < 727 then
                      953
                    else
                      (if n < 728 then
                        728
                      else
                        1625)))
                else
                  (if n < 731 then
                    (if n < 730 then
                      1705
                    else
                      390)
                  else
                    (if n < 732 then
                      387
                    else
                      (if n < 733 then
                        1663
                      else
                        1737))))
              else
                (if n < 739 then
                  (if n < 736 then
                    (if n < 735 then
                      368
                    else
                      360)
                  else
                    (if n < 737 then
                      466
                    else
                      (if n < 738 then
                        353
                      else
                        1213)))
                else
                  (if n < 741 then
                    (if n < 740 then
                      1568
                    else
                      1696)
                  else
                    (if n < 742 then
                      1158
                    else
                      (if n < 743 then
                        322
                      else
                        413)))))
            else
              (if n < 754 then
                (if n < 749 then
                  (if n < 746 then
                    (if n < 745 then
                      431
                    else
                      590)
                  else
                    (if n < 747 then
                      317
                    else
                      (if n < 748 then
                        355
                      else
                        340)))
                else
                  (if n < 751 then
                    (if n < 750 then
                      1160
                    else
                      398)
                  else
                    (if n < 752 then
                      464
                    else
                      (if n < 753 then
                        492
                      else
                        449))))
              else
                (if n < 759 then
                  (if n < 756 then
                    (if n < 755 then
                      483
                    else
                      325)
                  else
                    (if n < 757 then
                      1118
                    else
                      (if n < 758 then
                        329
                      else
                        490)))
                else
                  (if n < 761 then
                    (if n < 760 then
                      1137
                    else
                      456)
                  else
                    (if n < 762 then
                      485
                    else
                      (if n < 763 then
                        1215
                      else
                        1468))))))
          else
            (if n < 784 then
              (if n < 774 then
                (if n < 769 then
                  (if n < 766 then
                    (if n < 765 then
                      1408
                    else
                      1291)
                  else
                    (if n < 767 then
                      1101
                    else
                      (if n < 768 then
                        767
                      else
                        859)))
                else
                  (if n < 771 then
                    (if n < 770 then
                      551
                    else
                      1532)
                  else
                    (if n < 772 then
                      1167
                    else
                      (if n < 773 then
                        1422
                      else
                        279))))
              else
                (if n < 779 then
                  (if n < 776 then
                    (if n < 775 then
                      1223
                    else
                      1497)
                  else
                    (if n < 777 then
                      1323
                    else
                      (if n < 778 then
                        1035
                      else
                        799)))
                else
                  (if n < 781 then
                    (if n < 780 then
                      792
                    else
                      650)
                  else
                    (if n < 782 then
                      540
                    else
                      (if n < 783 then
                        626
                      else
                        664)))))
            else
              (if n < 794 then
                (if n < 789 then
                  (if n < 786 then
                    (if n < 785 then
                      729
                    else
                      532)
                  else
                    (if n < 787 then
                      429
                    else
                      (if n < 788 then
                        947
                      else
                        732)))
                else
                  (if n < 791 then
                    (if n < 790 then
                      760
                    else
                      904)
                  else
                    (if n < 792 then
                      658
                    else
                      (if n < 793 then
                        417
                      else
                        703))))
              else
                (if n < 799 then
                  (if n < 796 then
                    (if n < 795 then
                      1299
                    else
                      1285)
                  else
                    (if n < 797 then
                      1139
                    else
                      (if n < 798 then
                        1312
                      else
                        930)))
                else
                  (if n < 802 then
                    (if n < 800 then
                      1507
                    else
                      (if n < 801 then
                        1251
                      else
                        482))
                  else
                    (if n < 803 then
                      596
                    else
                      (if n < 804 then
                        523
                      else
                        1479))))))))
      else
        (if n < 885 then
          (if n < 845 then
            (if n < 825 then
              (if n < 815 then
                (if n < 810 then
                  (if n < 807 then
                    (if n < 806 then
                      455
                    else
                      1534)
                  else
                    (if n < 808 then
                      1519
                    else
                      (if n < 809 then
                        1529
                      else
                        888)))
                else
                  (if n < 812 then
                    (if n < 811 then
                      594
                    else
                      1115)
                  else
                    (if n < 813 then
                      948
                    else
                      (if n < 814 then
                        1235
                      else
                        434))))
              else
                (if n < 820 then
                  (if n < 817 then
                    (if n < 816 then
                      1437
                    else
                      1472)
                  else
                    (if n < 818 then
                      1360
                    else
                      (if n < 819 then
                        1029
                      else
                        945)))
                else
                  (if n < 822 then
                    (if n < 821 then
                      708
                    else
                      705)
                  else
                    (if n < 823 then
                      535
                    else
                      (if n < 824 then
                        906
                      else
                        781)))))
            else
              (if n < 835 then
                (if n < 830 then
                  (if n < 827 then
                    (if n < 826 then
                      1031
                    else
                      950)
                  else
                    (if n < 828 then
                      984
                    else
                      (if n < 829 then
                        379
                      else
                        1366)))
                else
                  (if n < 832 then
                    (if n < 831 then
                      1287
                    else
                      1335)
                  else
                    (if n < 833 then
                      515
                    else
                      (if n < 834 then
                        654
                      else
                        1359))))
              else
                (if n < 840 then
                  (if n < 837 then
                    (if n < 836 then
                      891
                    else
                      701)
                  else
                    (if n < 838 then
                      915
                    else
                      (if n < 839 then
                        965
                      else
                        707)))
                else
                  (if n < 842 then
                    (if n < 841 then
                      1077
                    else
                      981)
                  else
                    (if n < 843 then
                      1127
                    else
                      (if n < 844 then
                        1094
                      else
                        1247))))))
          else
            (if n < 865 then
              (if n < 855 then
                (if n < 850 then
                  (if n < 847 then
                    (if n < 846 then
                      1276
                    else
                      1222)
                  else
                    (if n < 848 then
                      475
                    else
                      (if n < 849 then
                        727
                      else
                        1263)))
                else
                  (if n < 852 then
                    (if n < 851 then
                      622
                    else
                      665)
                  else
                    (if n < 853 then
                      1621
                    else
                      (if n < 854 then
                        1623
                      else
                        613))))
              else
                (if n < 860 then
                  (if n < 857 then
                    (if n < 856 then
                      773
                    else
                      1773)
                  else
                    (if n < 858 then
                      1195
                    else
                      (if n < 859 then
                        1033
                      else
                        1007)))
                else
                  (if n < 862 then
                    (if n < 861 then
                      527
                    else
                      1036)
                  else
                    (if n < 863 then
                      667
                    else
                      (if n < 864 then
                        959
                      else
                        616)))))
            else
              (if n < 875 then
                (if n < 870 then
                  (if n < 867 then
                    (if n < 866 then
                      653
                    else
                      934)
                  else
                    (if n < 868 then
                      1164
                    else
                      (if n < 869 then
                        1330
                      else
                        656)))
                else
                  (if n < 872 then
                    (if n < 871 then
                      603
                    else
                      766)
                  else
                    (if n < 873 then
                      334
                    else
                      (if n < 874 then
                        421
                      else
                        1447))))
              else
                (if n < 880 then
                  (if n < 877 then
                    (if n < 876 then
                      601
                    else
                      763)
                  else
                    (if n < 878 then
                      952
                    else
                      (if n < 879 then
                        2019
                      else
                        1198)))
                else
                  (if n < 882 then
                    (if n < 881 then
                      689
                    else
                      1227)
                  else
                    (if n < 883 then
                      1209
                    else
                      (if n < 884 then
                        2025
                      else
                        1913)))))))
        else
          (if n < 925 then
            (if n < 905 then
              (if n < 895 then
                (if n < 890 then
                  (if n < 887 then
                    (if n < 886 then
                      1865
                    else
                      2006)
                  else
                    (if n < 888 then
                      851
                    else
                      (if n < 889 then
                        1279
                      else
                        846)))
                else
                  (if n < 892 then
                    (if n < 891 then
                      819
                    else
                      992)
                  else
                    (if n < 893 then
                      1128
                    else
                      (if n < 894 then
                        901
                      else
                        1220))))
              else
                (if n < 900 then
                  (if n < 897 then
                    (if n < 896 then
                      1076
                    else
                      1058)
                  else
                    (if n < 898 then
                      554
                    else
                      (if n < 899 then
                        737
                      else
                        559)))
                else
                  (if n < 902 then
                    (if n < 901 then
                      547
                    else
                      584)
                  else
                    (if n < 903 then
                      1239
                    else
                      (if n < 904 then
                        1159
                      else
                        1185)))))
            else
              (if n < 915 then
                (if n < 910 then
                  (if n < 907 then
                    (if n < 906 then
                      783
                    else
                      1302)
                  else
                    (if n < 908 then
                      330
                    else
                      (if n < 909 then
                        1423
                      else
                        1486)))
                else
                  (if n < 912 then
                    (if n < 911 then
                      1348
                    else
                      1357)
                  else
                    (if n < 913 then
                      1498
                    else
                      (if n < 914 then
                        1644
                      else
                        716))))
              else
                (if n < 920 then
                  (if n < 917 then
                    (if n < 916 then
                      1123
                    else
                      1322)
                  else
                    (if n < 918 then
                      617
                    else
                      (if n < 919 then
                        769
                      else
                        670)))
                else
                  (if n < 922 then
                    (if n < 921 then
                      1538
                    else
                      1199)
                  else
                    (if n < 923 then
                      627
                    else
                      (if n < 924 then
                        1282
                      else
                        754))))))
          else
            (if n < 945 then
              (if n < 935 then
                (if n < 930 then
                  (if n < 927 then
                    (if n < 926 then
                      608
                    else
                      1541)
                  else
                    (if n < 928 then
                      1045
                    else
                      (if n < 929 then
                        1289
                      else
                        751)))
                else
                  (if n < 932 then
                    (if n < 931 then
                      1564
                    else
                      1593)
                  else
                    (if n < 933 then
                      1138
                    else
                      (if n < 934 then
                        990
                      else
                        793))))
              else
                (if n < 940 then
                  (if n < 937 then
                    (if n < 936 then
                      866
                    else
                      550)
                  else
                    (if n < 938 then
                      1119
                    else
                      (if n < 939 then
                        958
                      else
                        861)))
                else
                  (if n < 942 then
                    (if n < 941 then
                      938
                    else
                      922)
                  else
                    (if n < 943 then
                      973
                    else
                      (if n < 944 then
                        925
                      else
                        1949)))))
            else
              (if n < 955 then
                (if n < 950 then
                  (if n < 947 then
                    (if n < 946 then
                      848
                    else
                      942)
                  else
                    (if n < 948 then
                      993
                    else
                      (if n < 949 then
                        1122
                      else
                        1228)))
                else
                  (if n < 952 then
                    (if n < 951 then
                      1273
                    else
                      1582)
                  else
                    (if n < 953 then
                      519
                    else
                      (if n < 954 then
                        1275
                      else
                        642))))
              else
                (if n < 960 then
                  (if n < 957 then
                    (if n < 956 then
                      713
                    else
                      931)
                  else
                    (if n < 958 then
                      715
                    else
                      (if n < 959 then
                        677
                      else
                        543)))
                else
                  (if n < 963 then
                    (if n < 961 then
                      521
                    else
                      (if n < 962 then
                        723
                      else
                        856))
                  else
                    (if n < 964 then
                      1278
                    else
                      (if n < 965 then
                        1060
                      else
                        1074)))))))))
    else
      (if n < 1127 then
        (if n < 1046 then
          (if n < 1006 then
            (if n < 986 then
              (if n < 976 then
                (if n < 971 then
                  (if n < 968 then
                    (if n < 967 then
                      843
                    else
                      1182)
                  else
                    (if n < 969 then
                      818
                    else
                      (if n < 970 then
                        956
                      else
                        991)))
                else
                  (if n < 973 then
                    (if n < 972 then
                      985
                    else
                      969)
                  else
                    (if n < 974 then
                      1001
                    else
                      (if n < 975 then
                        615
                      else
                        761))))
              else
                (if n < 981 then
                  (if n < 978 then
                    (if n < 977 then
                      742
                    else
                      962)
                  else
                    (if n < 979 then
                      903
                    else
                      (if n < 980 then
                        612
                      else
                        1342)))
                else
                  (if n < 983 then
                    (if n < 982 then
                      1003
                    else
                      541)
                  else
                    (if n < 984 then
                      385
                    else
                      (if n < 985 then
                        943
                      else
                        1459)))))
            else
              (if n < 996 then
                (if n < 991 then
                  (if n < 988 then
                    (if n < 987 then
                      1477
                    else
                      1362)
                  else
                    (if n < 989 then
                      1457
                    else
                      (if n < 990 then
                        838
                      else
                        619)))
                else
                  (if n < 993 then
                    (if n < 992 then
                      1103
                    else
                      1095)
                  else
                    (if n < 994 then
                      1369
                    else
                      (if n < 995 then
                        1385
                      else
                        517))))
              else
                (if n < 1001 then
                  (if n < 998 then
                    (if n < 997 then
                      473
                    else
                      395)
                  else
                    (if n < 999 then
                      493
                    else
                      (if n < 1000 then
                        635
                      else
                        1739)))
                else
                  (if n < 1003 then
                    (if n < 1002 then
                      569
                    else
                      1381)
                  else
                    (if n < 1004 then
                      1651
                    else
                      (if n < 1005 then
                        863
                      else
                        1431))))))
          else
            (if n < 1026 then
              (if n < 1016 then
                (if n < 1011 then
                  (if n < 1008 then
                    (if n < 1007 then
                      1371
                    else
                      1756)
                  else
                    (if n < 1009 then
                      740
                    else
                      (if n < 1010 then
                        1328
                      else
                        1505)))
                else
                  (if n < 1013 then
                    (if n < 1012 then
                      1043
                    else
                      1142)
                  else
                    (if n < 1014 then
                      1116
                    else
                      (if n < 1015 then
                        1484
                      else
                        1367))))
              else
                (if n < 1021 then
                  (if n < 1018 then
                    (if n < 1017 then
                      1909
                    else
                      966)
                  else
                    (if n < 1019 then
                      599
                    else
                      (if n < 1020 then
                        1545
                      else
                        718)))
                else
                  (if n < 1023 then
                    (if n < 1022 then
                      679
                    else
                      407)
                  else
                    (if n < 1024 then
                      571
                    else
                      (if n < 1025 then
                        1514
                      else
                        999)))))
            else
              (if n < 1036 then
                (if n < 1031 then
                  (if n < 1028 then
                    (if n < 1027 then
                      944
                    else
                      1452)
                  else
                    (if n < 1029 then
                      1474
                    else
                      (if n < 1030 then
                        1868
                      else
                        1531)))
                else
                  (if n < 1033 then
                    (if n < 1032 then
                      1333
                    else
                      854)
                  else
                    (if n < 1034 then
                      1018
                    else
                      (if n < 1035 then
                        844
                      else
                        807))))
              else
                (if n < 1041 then
                  (if n < 1038 then
                    (if n < 1037 then
                      287
                    else
                      1099)
                  else
                    (if n < 1039 then
                      1052
                    else
                      (if n < 1040 then
                        1829
                      else
                        267)))
                else
                  (if n < 1043 then
                    (if n < 1042 then
                      1163
                    else
                      759)
                  else
                    (if n < 1044 then
                      1460
                    else
                      (if n < 1045 then
                        1383
                      else
                        83)))))))
        else
          (if n < 1086 then
            (if n < 1066 then
              (if n < 1056 then
                (if n < 1051 then
                  (if n < 1048 then
                    (if n < 1047 then
                      345
                    else
                      1622)
                  else
                    (if n < 1049 then
                      499
                    else
                      (if n < 1050 then
                        300
                      else
                        501)))
                else
                  (if n < 1053 then
                    (if n < 1052 then
                      1062
                    else
                      404)
                  else
                    (if n < 1054 then
                      1656
                    else
                      (if n < 1055 then
                        1730
                      else
                        1785))))
              else
                (if n < 1061 then
                  (if n < 1058 then
                    (if n < 1057 then
                      1692
                    else
                      506)
                  else
                    (if n < 1059 then
                      1922
                    else
                      (if n < 1060 then
                        908
                      else
                        1856)))
                else
                  (if n < 1063 then
                    (if n < 1062 then
                      1844
                    else
                      1916)
                  else
                    (if n < 1064 then
                      1858
                    else
                      (if n < 1065 then
                        1918
                      else
                        470)))))
            else
              (if n < 1076 then
                (if n < 1071 then
                  (if n < 1068 then
                    (if n < 1067 then
                      1901
                    else
                      367)
                  else
                    (if n < 1069 then
                      479
                    else
                      (if n < 1070 then
                        1927
                      else
                        1006)))
                else
                  (if n < 1073 then
                    (if n < 1072 then
                      412
                    else
                      1841)
                  else
                    (if n < 1074 then
                      841
                    else
                      (if n < 1075 then
                        362
                      else
                        508))))
              else
                (if n < 1081 then
                  (if n < 1078 then
                    (if n < 1077 then
                      378
                    else
                      939)
                  else
                    (if n < 1079 then
                      1149
                    else
                      (if n < 1080 then
                        1242
                      else
                        1179)))
                else
                  (if n < 1083 then
                    (if n < 1082 then
                      383
                    else
                      1843)
                  else
                    (if n < 1084 then
                      145
                    else
                      (if n < 1085 then
                        1154
                      else
                        1975))))))
          else
            (if n < 1106 then
              (if n < 1096 then
                (if n < 1091 then
                  (if n < 1088 then
                    (if n < 1087 then
                      2007
                    else
                      1245)
                  else
                    (if n < 1089 then
                      2032
                    else
                      (if n < 1090 then
                        914
                      else
                        1932)))
                else
                  (if n < 1093 then
                    (if n < 1092 then
                      1937
                    else
                      319)
                  else
                    (if n < 1094 then
                      1747
                    else
                      (if n < 1095 then
                        1966
                      else
                        1925))))
              else
                (if n < 1101 then
                  (if n < 1098 then
                    (if n < 1097 then
                      343
                    else
                      161)
                  else
                    (if n < 1099 then
                      1994
                    else
                      (if n < 1100 then
                        1641
                      else
                        1766)))
                else
                  (if n < 1103 then
                    (if n < 1102 then
                      1560
                    else
                      852)
                  else
                    (if n < 1104 then
                      892
                    else
                      (if n < 1105 then
                        932
                      else
                        1224)))))
            else
              (if n < 1116 then
                (if n < 1111 then
                  (if n < 1108 then
                    (if n < 1107 then
                      1604
                    else
                      333)
                  else
                    (if n < 1109 then
                      1615
                    else
                      (if n < 1110 then
                        484
                      else
                        1800)))
                else
                  (if n < 1113 then
                    (if n < 1112 then
                      970
                    else
                      1715)
                  else
                    (if n < 1114 then
                      296
                    else
                      (if n < 1115 then
                        409
                      else
                        949))))
              else
                (if n < 1121 then
                  (if n < 1118 then
                    (if n < 1117 then
                      835
                    else
                      1013)
                  else
                    (if n < 1119 then
                      472
                    else
                      (if n < 1120 then
                        830
                      else
                        1065)))
                else
                  (if n < 1124 then
                    (if n < 1122 then
                      1770
                    else
                      (if n < 1123 then
                        1759
                      else
                        372))
                  else
                    (if n < 1125 then
                      1646
                    else
                      (if n < 1126 then
                        1783
                      else
                        961))))))))
      else
        (if n < 1207 then
          (if n < 1167 then
            (if n < 1147 then
              (if n < 1137 then
                (if n < 1132 then
                  (if n < 1129 then
                    (if n < 1128 then
                      994
                    else
                      66)
                  else
                    (if n < 1130 then
                      1066
                    else
                      (if n < 1131 then
                        1038
                      else
                        1744)))
                else
                  (if n < 1134 then
                    (if n < 1133 then
                      1980
                    else
                      2033)
                  else
                    (if n < 1135 then
                      1572
                    else
                      (if n < 1136 then
                        425
                      else
                        1272))))
              else
                (if n < 1142 then
                  (if n < 1139 then
                    (if n < 1138 then
                      889
                    else
                      1894)
                  else
                    (if n < 1140 then
                      366
                    else
                      (if n < 1141 then
                        1870
                      else
                        402)))
                else
                  (if n < 1144 then
                    (if n < 1143 then
                      1584
                    else
                      453)
                  else
                    (if n < 1145 then
                      637
                    else
                      (if n < 1146 then
                        354
                      else
                        388)))))
            else
              (if n < 1157 then
                (if n < 1152 then
                  (if n < 1149 then
                    (if n < 1148 then
                      814
                    else
                      1934)
                  else
                    (if n < 1150 then
                      1670
                    else
                      (if n < 1151 then
                        2023
                      else
                        1836)))
                else
                  (if n < 1154 then
                    (if n < 1153 then
                      812
                    else
                      1885)
                  else
                    (if n < 1155 then
                      2012
                    else
                      (if n < 1156 then
                        496
                      else
                        1169))))
              else
                (if n < 1162 then
                  (if n < 1159 then
                    (if n < 1158 then
                      1596
                    else
                      1694)
                  else
                    (if n < 1160 then
                      1388
                    else
                      (if n < 1161 then
                        1742
                      else
                        311)))
                else
                  (if n < 1164 then
                    (if n < 1163 then
                      1703
                    else
                      1637)
                  else
                    (if n < 1165 then
                      405
                    else
                      (if n < 1166 then
                        1740
                      else
                        1073))))))
          else
            (if n < 1187 then
              (if n < 1177 then
                (if n < 1172 then
                  (if n < 1169 then
                    (if n < 1168 then
                      1068
                    else
                      1698)
                  else
                    (if n < 1170 then
                      1265
                    else
                      (if n < 1171 then
                        1595
                      else
                        1569)))
                else
                  (if n < 1174 then
                    (if n < 1173 then
                      1576
                    else
                      634)
                  else
                    (if n < 1175 then
                      1170
                    else
                      (if n < 1176 then
                        1649
                      else
                        1578))))
              else
                (if n < 1182 then
                  (if n < 1179 then
                    (if n < 1178 then
                      374
                    else
                      371)
                  else
                    (if n < 1180 then
                      1571
                    else
                      (if n < 1181 then
                        462
                      else
                        1707)))
                else
                  (if n < 1184 then
                    (if n < 1183 then
                      1672
                    else
                      1558)
                  else
                    (if n < 1185 then
                      359
                    else
                      (if n < 1186 then
                        1757
                      else
                        1687)))))
            else
              (if n < 1197 then
                (if n < 1192 then
                  (if n < 1189 then
                    (if n < 1188 then
                      1202
                    else
                      1261)
                  else
                    (if n < 1190 then
                      445
                    else
                      (if n < 1191 then
                        1229
                      else
                        468)))
                else
                  (if n < 1194 then
                    (if n < 1193 then
                      1553
                    else
                      416)
                  else
                    (if n < 1195 then
                      1999
                    else
                      (if n < 1196 then
                        870
                      else
                        278))))
              else
                (if n < 1202 then
                  (if n < 1199 then
                    (if n < 1198 then
                      1691
                    else
                      1725)
                  else
                    (if n < 1200 then
                      1325
                    else
                      (if n < 1201 then
                        1451
                      else
                        1014)))
                else
                  (if n < 1204 then
                    (if n < 1203 then
                      867
                    else
                      361)
                  else
                    (if n < 1205 then
                      1543
                    else
                      (if n < 1206 then
                        261
                      else
                        1745)))))))
        else
          (if n < 1247 then
            (if n < 1227 then
              (if n < 1217 then
                (if n < 1212 then
                  (if n < 1209 then
                    (if n < 1208 then
                      474
                    else
                      301)
                  else
                    (if n < 1210 then
                      1156
                    else
                      (if n < 1211 then
                        946
                      else
                        263)))
                else
                  (if n < 1214 then
                    (if n < 1213 then
                      1988
                    else
                      1469)
                  else
                    (if n < 1215 then
                      1174
                    else
                      (if n < 1216 then
                        1262
                      else
                        1203))))
              else
                (if n < 1222 then
                  (if n < 1219 then
                    (if n < 1218 then
                      1226
                    else
                      1250)
                  else
                    (if n < 1220 then
                      1133
                    else
                      (if n < 1221 then
                        1241
                      else
                        1191)))
                else
                  (if n < 1224 then
                    (if n < 1223 then
                      1192
                    else
                      976)
                  else
                    (if n < 1225 then
                      23
                    else
                      (if n < 1226 then
                        1627
                      else
                        1946)))))
            else
              (if n < 1237 then
                (if n < 1232 then
                  (if n < 1229 then
                    (if n < 1228 then
                      411
                    else
                      1297)
                  else
                    (if n < 1230 then
                      916
                    else
                      (if n < 1231 then
                        826
                      else
                        936)))
                else
                  (if n < 1234 then
                    (if n < 1233 then
                      1171
                    else
                      440)
                  else
                    (if n < 1235 then
                      726
                    else
                      (if n < 1236 then
                        1078
                      else
                        929))))
              else
                (if n < 1242 then
                  (if n < 1239 then
                    (if n < 1238 then
                      1965
                    else
                      1268)
                  else
                    (if n < 1240 then
                      282
                    else
                      (if n < 1241 then
                        352
                      else
                        423)))
                else
                  (if n < 1244 then
                    (if n < 1243 then
                      369
                    else
                      1183)
                  else
                    (if n < 1245 then
                      427
                    else
                      (if n < 1246 then
                        579
                      else
                        1259))))))
          else
            (if n < 1267 then
              (if n < 1257 then
                (if n < 1252 then
                  (if n < 1249 then
                    (if n < 1248 then
                      885
                    else
                      941)
                  else
                    (if n < 1250 then
                      1603
                    else
                      (if n < 1251 then
                        414
                      else
                        510)))
                else
                  (if n < 1254 then
                    (if n < 1253 then
                      467
                    else
                      298)
                  else
                    (if n < 1255 then
                      418
                    else
                      (if n < 1256 then
                        1130
                      else
                        309))))
              else
                (if n < 1262 then
                  (if n < 1259 then
                    (if n < 1258 then
                      435
                    else
                      503)
                  else
                    (if n < 1260 then
                      1639
                    else
                      (if n < 1261 then
                        1188
                      else
                        1889)))
                else
                  (if n < 1264 then
                    (if n < 1263 then
                      400
                    else
                      887)
                  else
                    (if n < 1265 then
                      534
                    else
                      (if n < 1266 then
                        1207
                      else
                        1253)))))
            else
              (if n < 1277 then
                (if n < 1272 then
                  (if n < 1269 then
                    (if n < 1268 then
                      663
                    else
                      1037)
                  else
                    (if n < 1270 then
                      691
                    else
                      (if n < 1271 then
                        733
                      else
                        1147)))
                else
                  (if n < 1274 then
                    (if n < 1273 then
                      1100
                    else
                      1181)
                  else
                    (if n < 1275 then
                      1027
                    else
                      (if n < 1276 then
                        265
                      else
                        1090))))
              else
                (if n < 1282 then
                  (if n < 1279 then
                    (if n < 1278 then
                      1574
                    else
                      1586)
                  else
                    (if n < 1280 then
                      1679
                    else
                      (if n < 1281 then
                        347
                      else
                        572)))
                else
                  (if n < 1285 then
                    (if n < 1283 then
                      577
                    else
                      (if n < 1284 then
                        988
                      else
                        505))
                  else
                    (if n < 1286 then
                      894
                    else
                      (if n < 1287 then
                        910
                      else
                        1121)))))))))))

/-- Strictly earlier parent of every noninitial orbit entry. -/
def golayDodecadOrbitParent (n : ℕ) : ℕ :=
  (if n < 644 then
    (if n < 322 then
      (if n < 161 then
        (if n < 80 then
          (if n < 40 then
            (if n < 20 then
              (if n < 10 then
                0
              else
                (if n < 15 then
                  (if n < 12 then
                    0
                  else
                    (if n < 13 then
                      0
                    else
                      1))
                else
                  1))
            else
              (if n < 30 then
                (if n < 25 then
                  (if n < 22 then
                    1
                  else
                    (if n < 23 then
                      1
                    else
                      (if n < 24 then
                        1
                      else
                        2)))
                else
                  2)
              else
                (if n < 35 then
                  2
                else
                  (if n < 37 then
                    (if n < 36 then
                      2
                    else
                      3)
                  else
                    3))))
          else
            (if n < 60 then
              (if n < 50 then
                (if n < 45 then
                  3
                else
                  (if n < 47 then
                    (if n < 46 then
                      3
                    else
                      4)
                  else
                    4))
              else
                (if n < 55 then
                  4
                else
                  5))
            else
              (if n < 70 then
                (if n < 65 then
                  (if n < 62 then
                    5
                  else
                    (if n < 63 then
                      5
                    else
                      6))
                else
                  6)
              else
                (if n < 75 then
                  (if n < 72 then
                    (if n < 71 then
                      6
                    else
                      7)
                  else
                    7)
                else
                  7))))
        else
          (if n < 120 then
            (if n < 100 then
              (if n < 90 then
                (if n < 85 then
                  (if n < 82 then
                    7
                  else
                    (if n < 83 then
                      7
                    else
                      8))
                else
                  8)
              else
                (if n < 95 then
                  (if n < 92 then
                    8
                  else
                    9)
                else
                  9))
            else
              (if n < 110 then
                (if n < 105 then
                  (if n < 102 then
                    10
                  else
                    (if n < 103 then
                      10
                    else
                      (if n < 104 then
                        10
                      else
                        11)))
                else
                  11)
              else
                (if n < 115 then
                  (if n < 112 then
                    11
                  else
                    (if n < 113 then
                      11
                    else
                      12))
                else
                  12)))
          else
            (if n < 140 then
              (if n < 130 then
                (if n < 125 then
                  (if n < 122 then
                    12
                  else
                    (if n < 123 then
                      12
                    else
                      (if n < 124 then
                        12
                      else
                        13)))
                else
                  13)
              else
                (if n < 135 then
                  13
                else
                  14))
            else
              (if n < 150 then
                (if n < 145 then
                  (if n < 142 then
                    14
                  else
                    (if n < 143 then
                      14
                    else
                      15))
                else
                  15)
              else
                (if n < 155 then
                  16
                else
                  (if n < 158 then
                    (if n < 156 then
                      16
                    else
                      (if n < 157 then
                        16
                      else
                        17))
                  else
                    17))))))
      else
        (if n < 241 then
          (if n < 201 then
            (if n < 181 then
              (if n < 171 then
                (if n < 166 then
                  (if n < 163 then
                    17
                  else
                    18)
                else
                  (if n < 168 then
                    18
                  else
                    19))
              else
                (if n < 176 then
                  19
                else
                  20))
            else
              (if n < 191 then
                (if n < 186 then
                  (if n < 183 then
                    20
                  else
                    (if n < 184 then
                      20
                    else
                      21))
                else
                  21)
              else
                (if n < 196 then
                  (if n < 193 then
                    (if n < 192 then
                      21
                    else
                      22)
                  else
                    22)
                else
                  (if n < 198 then
                    22
                  else
                    (if n < 199 then
                      22
                    else
                      (if n < 200 then
                        22
                      else
                        23))))))
          else
            (if n < 221 then
              (if n < 211 then
                23
              else
                (if n < 216 then
                  (if n < 213 then
                    23
                  else
                    24)
                else
                  24))
            else
              (if n < 231 then
                (if n < 226 then
                  (if n < 223 then
                    24
                  else
                    (if n < 224 then
                      24
                    else
                      (if n < 225 then
                        24
                      else
                        25)))
                else
                  (if n < 228 then
                    25
                  else
                    26))
              else
                (if n < 236 then
                  26
                else
                  27))))
        else
          (if n < 281 then
            (if n < 261 then
              (if n < 251 then
                (if n < 246 then
                  (if n < 243 then
                    (if n < 242 then
                      27
                    else
                      28)
                  else
                    28)
                else
                  (if n < 248 then
                    (if n < 247 then
                      28
                    else
                      29)
                  else
                    29))
              else
                (if n < 256 then
                  (if n < 253 then
                    (if n < 252 then
                      29
                    else
                      30)
                  else
                    30)
                else
                  (if n < 258 then
                    30
                  else
                    (if n < 259 then
                      30
                    else
                      31))))
            else
              (if n < 271 then
                (if n < 266 then
                  (if n < 263 then
                    31
                  else
                    (if n < 264 then
                      31
                    else
                      (if n < 265 then
                        31
                      else
                        32)))
                else
                  32)
              else
                (if n < 276 then
                  (if n < 273 then
                    32
                  else
                    (if n < 274 then
                      32
                    else
                      33))
                else
                  33)))
          else
            (if n < 301 then
              (if n < 291 then
                (if n < 286 then
                  (if n < 283 then
                    (if n < 282 then
                      33
                    else
                      34)
                  else
                    34)
                else
                  (if n < 288 then
                    34
                  else
                    (if n < 289 then
                      34
                    else
                      35)))
              else
                (if n < 296 then
                  (if n < 293 then
                    35
                  else
                    (if n < 294 then
                      35
                    else
                      (if n < 295 then
                        35
                      else
                        36)))
                else
                  36))
            else
              (if n < 311 then
                (if n < 306 then
                  (if n < 303 then
                    36
                  else
                    37)
                else
                  (if n < 308 then
                    37
                  else
                    (if n < 309 then
                      37
                    else
                      (if n < 310 then
                        37
                      else
                        38))))
              else
                (if n < 316 then
                  38
                else
                  39))))))
    else
      (if n < 483 then
        (if n < 402 then
          (if n < 362 then
            (if n < 342 then
              (if n < 332 then
                (if n < 327 then
                  (if n < 324 then
                    39
                  else
                    40)
                else
                  (if n < 329 then
                    (if n < 328 then
                      40
                    else
                      41)
                  else
                    41))
              else
                (if n < 337 then
                  (if n < 334 then
                    41
                  else
                    42)
                else
                  (if n < 339 then
                    42
                  else
                    (if n < 340 then
                      42
                    else
                      (if n < 341 then
                        42
                      else
                        43)))))
            else
              (if n < 352 then
                (if n < 347 then
                  (if n < 344 then
                    (if n < 343 then
                      43
                    else
                      44)
                  else
                    44)
                else
                  (if n < 349 then
                    44
                  else
                    (if n < 350 then
                      44
                    else
                      45)))
              else
                (if n < 357 then
                  (if n < 354 then
                    (if n < 353 then
                      45
                    else
                      46)
                  else
                    46)
                else
                  (if n < 359 then
                    46
                  else
                    (if n < 360 then
                      46
                    else
                      (if n < 361 then
                        46
                      else
                        47))))))
          else
            (if n < 382 then
              (if n < 372 then
                (if n < 367 then
                  47
                else
                  (if n < 369 then
                    48
                  else
                    (if n < 370 then
                      48
                    else
                      (if n < 371 then
                        48
                      else
                        49))))
              else
                (if n < 377 then
                  49
                else
                  (if n < 379 then
                    50
                  else
                    (if n < 380 then
                      50
                    else
                      51))))
            else
              (if n < 392 then
                (if n < 387 then
                  51
                else
                  52)
              else
                (if n < 397 then
                  (if n < 394 then
                    52
                  else
                    (if n < 395 then
                      52
                    else
                      53))
                else
                  53))))
        else
          (if n < 442 then
            (if n < 422 then
              (if n < 412 then
                (if n < 407 then
                  (if n < 404 then
                    53
                  else
                    54)
                else
                  (if n < 409 then
                    55
                  else
                    (if n < 410 then
                      55
                    else
                      (if n < 411 then
                        55
                      else
                        56))))
              else
                (if n < 417 then
                  (if n < 414 then
                    56
                  else
                    57)
                else
                  (if n < 419 then
                    57
                  else
                    (if n < 420 then
                      57
                    else
                      58))))
            else
              (if n < 432 then
                (if n < 427 then
                  (if n < 424 then
                    58
                  else
                    59)
                else
                  (if n < 429 then
                    59
                  else
                    (if n < 430 then
                      59
                    else
                      60)))
              else
                (if n < 437 then
                  60
                else
                  (if n < 439 then
                    61
                  else
                    62))))
          else
            (if n < 462 then
              (if n < 452 then
                (if n < 447 then
                  62
                else
                  (if n < 449 then
                    62
                  else
                    (if n < 450 then
                      62
                    else
                      (if n < 451 then
                        62
                      else
                        63))))
              else
                (if n < 457 then
                  (if n < 454 then
                    63
                  else
                    64)
                else
                  64))
            else
              (if n < 472 then
                (if n < 467 then
                  (if n < 464 then
                    64
                  else
                    65)
                else
                  (if n < 469 then
                    65
                  else
                    (if n < 470 then
                      66
                    else
                      (if n < 471 then
                        66
                      else
                        67))))
              else
                (if n < 477 then
                  67
                else
                  (if n < 480 then
                    (if n < 478 then
                      67
                    else
                      68)
                  else
                    68))))))
      else
        (if n < 563 then
          (if n < 523 then
            (if n < 503 then
              (if n < 493 then
                (if n < 488 then
                  69
                else
                  70)
              else
                (if n < 498 then
                  (if n < 495 then
                    (if n < 494 then
                      70
                    else
                      71)
                  else
                    (if n < 496 then
                      71
                    else
                      (if n < 497 then
                        71
                      else
                        72)))
                else
                  (if n < 500 then
                    72
                  else
                    (if n < 501 then
                      72
                    else
                      (if n < 502 then
                        72
                      else
                        73)))))
            else
              (if n < 513 then
                (if n < 508 then
                  73
                else
                  (if n < 510 then
                    (if n < 509 then
                      74
                    else
                      75)
                  else
                    (if n < 511 then
                      75
                    else
                      (if n < 512 then
                        76
                      else
                        77))))
              else
                (if n < 518 then
                  (if n < 515 then
                    (if n < 514 then
                      77
                    else
                      78)
                  else
                    78)
                else
                  (if n < 520 then
                    80
                  else
                    (if n < 521 then
                      80
                    else
                      (if n < 522 then
                        80
                      else
                        81))))))
          else
            (if n < 543 then
              (if n < 533 then
                (if n < 528 then
                  82
                else
                  (if n < 530 then
                    82
                  else
                    (if n < 531 then
                      82
                    else
                      83)))
              else
                (if n < 538 then
                  (if n < 535 then
                    83
                  else
                    84)
                else
                  (if n < 540 then
                    (if n < 539 then
                      84
                    else
                      85)
                  else
                    85)))
            else
              (if n < 553 then
                (if n < 548 then
                  (if n < 545 then
                    (if n < 544 then
                      85
                    else
                      86)
                  else
                    (if n < 546 then
                      86
                    else
                      87))
                else
                  (if n < 550 then
                    (if n < 549 then
                      87
                    else
                      88)
                  else
                    (if n < 551 then
                      88
                    else
                      (if n < 552 then
                        88
                      else
                        89))))
              else
                (if n < 558 then
                  (if n < 555 then
                    89
                  else
                    (if n < 556 then
                      90
                    else
                      91))
                else
                  91))))
        else
          (if n < 603 then
            (if n < 583 then
              (if n < 573 then
                (if n < 568 then
                  (if n < 565 then
                    (if n < 564 then
                      91
                    else
                      92)
                  else
                    92)
                else
                  (if n < 570 then
                    93
                  else
                    (if n < 571 then
                      93
                    else
                      94)))
              else
                (if n < 578 then
                  (if n < 575 then
                    (if n < 574 then
                      94
                    else
                      96)
                  else
                    96)
                else
                  (if n < 580 then
                    (if n < 579 then
                      96
                    else
                      97)
                  else
                    (if n < 581 then
                      97
                    else
                      98))))
            else
              (if n < 593 then
                (if n < 588 then
                  (if n < 585 then
                    (if n < 584 then
                      98
                    else
                      99)
                  else
                    99)
                else
                  (if n < 590 then
                    (if n < 589 then
                      99
                    else
                      100)
                  else
                    (if n < 591 then
                      100
                    else
                      (if n < 592 then
                        100
                      else
                        101))))
              else
                (if n < 598 then
                  (if n < 595 then
                    101
                  else
                    102)
                else
                  (if n < 600 then
                    102
                  else
                    (if n < 601 then
                      103
                    else
                      104)))))
          else
            (if n < 623 then
              (if n < 613 then
                (if n < 608 then
                  104
                else
                  (if n < 610 then
                    105
                  else
                    (if n < 611 then
                      105
                    else
                      106)))
              else
                (if n < 618 then
                  (if n < 615 then
                    106
                  else
                    (if n < 616 then
                      106
                    else
                      (if n < 617 then
                        106
                      else
                        107)))
                else
                  (if n < 620 then
                    107
                  else
                    108)))
            else
              (if n < 633 then
                (if n < 628 then
                  (if n < 625 then
                    108
                  else
                    (if n < 626 then
                      108
                    else
                      (if n < 627 then
                        108
                      else
                        109)))
                else
                  109)
              else
                (if n < 638 then
                  (if n < 635 then
                    (if n < 634 then
                      109
                    else
                      110)
                  else
                    110)
                else
                  (if n < 641 then
                    110
                  else
                    111))))))))
  else
    (if n < 966 then
      (if n < 805 then
        (if n < 724 then
          (if n < 684 then
            (if n < 664 then
              (if n < 654 then
                (if n < 649 then
                  (if n < 646 then
                    (if n < 645 then
                      111
                    else
                      112)
                  else
                    (if n < 647 then
                      112
                    else
                      (if n < 648 then
                        112
                      else
                        113)))
                else
                  113)
              else
                (if n < 659 then
                  114
                else
                  115))
            else
              (if n < 674 then
                (if n < 669 then
                  (if n < 666 then
                    (if n < 665 then
                      115
                    else
                      116)
                  else
                    (if n < 667 then
                      116
                    else
                      (if n < 668 then
                        116
                      else
                        117)))
                else
                  (if n < 671 then
                    117
                  else
                    118))
              else
                (if n < 679 then
                  (if n < 676 then
                    (if n < 675 then
                      118
                    else
                      119)
                  else
                    119)
                else
                  (if n < 681 then
                    119
                  else
                    (if n < 682 then
                      120
                    else
                      (if n < 683 then
                        120
                      else
                        121))))))
          else
            (if n < 704 then
              (if n < 694 then
                (if n < 689 then
                  (if n < 686 then
                    121
                  else
                    (if n < 687 then
                      122
                    else
                      (if n < 688 then
                        122
                      else
                        123)))
                else
                  124)
              else
                (if n < 699 then
                  (if n < 696 then
                    124
                  else
                    (if n < 697 then
                      124
                    else
                      125))
                else
                  (if n < 701 then
                    (if n < 700 then
                      125
                    else
                      126)
                  else
                    (if n < 702 then
                      127
                    else
                      (if n < 703 then
                        127
                      else
                        128)))))
            else
              (if n < 714 then
                (if n < 709 then
                  (if n < 706 then
                    128
                  else
                    (if n < 707 then
                      128
                    else
                      129))
                else
                  129)
              else
                (if n < 719 then
                  130
                else
                  (if n < 721 then
                    131
                  else
                    (if n < 722 then
                      131
                    else
                      132))))))
        else
          (if n < 764 then
            (if n < 744 then
              (if n < 734 then
                (if n < 729 then
                  (if n < 726 then
                    133
                  else
                    134)
                else
                  134)
              else
                (if n < 739 then
                  (if n < 736 then
                    135
                  else
                    (if n < 737 then
                      136
                    else
                      (if n < 738 then
                        136
                      else
                        137)))
                else
                  (if n < 741 then
                    137
                  else
                    138)))
            else
              (if n < 754 then
                (if n < 749 then
                  (if n < 746 then
                    (if n < 745 then
                      138
                    else
                      139)
                  else
                    139)
                else
                  140)
              else
                (if n < 759 then
                  (if n < 756 then
                    140
                  else
                    141)
                else
                  (if n < 761 then
                    142
                  else
                    (if n < 762 then
                      142
                    else
                      143)))))
          else
            (if n < 784 then
              (if n < 774 then
                (if n < 769 then
                  (if n < 766 then
                    (if n < 765 then
                      143
                    else
                      144)
                  else
                    (if n < 767 then
                      145
                    else
                      (if n < 768 then
                        145
                      else
                        146)))
                else
                  (if n < 771 then
                    146
                  else
                    (if n < 772 then
                      148
                    else
                      (if n < 773 then
                        148
                      else
                        149))))
              else
                (if n < 779 then
                  (if n < 776 then
                    149
                  else
                    (if n < 777 then
                      149
                    else
                      150))
                else
                  (if n < 781 then
                    (if n < 780 then
                      150
                    else
                      151)
                  else
                    (if n < 782 then
                      152
                    else
                      153))))
            else
              (if n < 794 then
                (if n < 789 then
                  (if n < 786 then
                    153
                  else
                    154)
                else
                  (if n < 791 then
                    (if n < 790 then
                      154
                    else
                      155)
                  else
                    (if n < 792 then
                      155
                    else
                      156)))
              else
                (if n < 799 then
                  (if n < 796 then
                    157
                  else
                    160)
                else
                  (if n < 802 then
                    (if n < 800 then
                      160
                    else
                      161)
                  else
                    (if n < 803 then
                      161
                    else
                      162)))))))
      else
        (if n < 885 then
          (if n < 845 then
            (if n < 825 then
              (if n < 815 then
                (if n < 810 then
                  (if n < 807 then
                    162
                  else
                    (if n < 808 then
                      162
                    else
                      (if n < 809 then
                        162
                      else
                        163)))
                else
                  (if n < 812 then
                    (if n < 811 then
                      163
                    else
                      164)
                  else
                    (if n < 813 then
                      164
                    else
                      165)))
              else
                (if n < 820 then
                  (if n < 817 then
                    165
                  else
                    (if n < 818 then
                      165
                    else
                      166))
                else
                  (if n < 822 then
                    (if n < 821 then
                      166
                    else
                      167)
                  else
                    (if n < 823 then
                      167
                    else
                      168))))
            else
              (if n < 835 then
                (if n < 830 then
                  (if n < 827 then
                    169
                  else
                    (if n < 828 then
                      170
                    else
                      173))
                else
                  (if n < 832 then
                    173
                  else
                    174))
              else
                (if n < 840 then
                  (if n < 837 then
                    175
                  else
                    (if n < 838 then
                      177
                    else
                      (if n < 839 then
                        177
                      else
                        178)))
                else
                  (if n < 842 then
                    178
                  else
                    179))))
          else
            (if n < 865 then
              (if n < 855 then
                (if n < 850 then
                  (if n < 847 then
                    179
                  else
                    (if n < 848 then
                      180
                    else
                      (if n < 849 then
                        180
                      else
                        181)))
                else
                  (if n < 852 then
                    (if n < 851 then
                      181
                    else
                      182)
                  else
                    183))
              else
                (if n < 860 then
                  (if n < 857 then
                    184
                  else
                    (if n < 858 then
                      185
                    else
                      187))
                else
                  (if n < 862 then
                    (if n < 861 then
                      187
                    else
                      188)
                  else
                    (if n < 863 then
                      188
                    else
                      189))))
            else
              (if n < 875 then
                (if n < 870 then
                  191
                else
                  (if n < 872 then
                    191
                  else
                    (if n < 873 then
                      192
                    else
                      (if n < 874 then
                        193
                      else
                        194))))
              else
                (if n < 880 then
                  (if n < 877 then
                    (if n < 876 then
                      195
                    else
                      197)
                  else
                    198)
                else
                  (if n < 882 then
                    (if n < 881 then
                      198
                    else
                      199)
                  else
                    200)))))
        else
          (if n < 925 then
            (if n < 905 then
              (if n < 895 then
                (if n < 890 then
                  (if n < 887 then
                    200
                  else
                    201)
                else
                  (if n < 892 then
                    201
                  else
                    (if n < 893 then
                      201
                    else
                      (if n < 894 then
                        201
                      else
                        202))))
              else
                (if n < 900 then
                  (if n < 897 then
                    202
                  else
                    203)
                else
                  (if n < 902 then
                    203
                  else
                    204)))
            else
              (if n < 915 then
                (if n < 910 then
                  (if n < 907 then
                    205
                  else
                    206)
                else
                  (if n < 912 then
                    (if n < 911 then
                      206
                    else
                      207)
                  else
                    (if n < 913 then
                      207
                    else
                      208)))
              else
                (if n < 920 then
                  (if n < 917 then
                    208
                  else
                    (if n < 918 then
                      208
                    else
                      209))
                else
                  210)))
          else
            (if n < 945 then
              (if n < 935 then
                (if n < 930 then
                  (if n < 927 then
                    (if n < 926 then
                      210
                    else
                      211)
                  else
                    211)
                else
                  (if n < 932 then
                    214
                  else
                    (if n < 933 then
                      215
                    else
                      (if n < 934 then
                        219
                      else
                        220))))
              else
                (if n < 940 then
                  (if n < 937 then
                    (if n < 936 then
                      222
                    else
                      224)
                  else
                    224)
                else
                  (if n < 942 then
                    224
                  else
                    (if n < 943 then
                      224
                    else
                      (if n < 944 then
                        224
                      else
                        225)))))
            else
              (if n < 955 then
                (if n < 950 then
                  (if n < 947 then
                    227
                  else
                    229)
                else
                  (if n < 952 then
                    (if n < 951 then
                      229
                    else
                      231)
                  else
                    (if n < 953 then
                      232
                    else
                      233)))
              else
                (if n < 960 then
                  (if n < 957 then
                    (if n < 956 then
                      233
                    else
                      234)
                  else
                    (if n < 958 then
                      234
                    else
                      (if n < 959 then
                        234
                      else
                        235)))
                else
                  (if n < 963 then
                    (if n < 961 then
                      235
                    else
                      (if n < 962 then
                        235
                      else
                        236))
                  else
                    237)))))))
    else
      (if n < 1127 then
        (if n < 1046 then
          (if n < 1006 then
            (if n < 986 then
              (if n < 976 then
                (if n < 971 then
                  (if n < 968 then
                    (if n < 967 then
                      238
                    else
                      239)
                  else
                    (if n < 969 then
                      239
                    else
                      (if n < 970 then
                        239
                      else
                        240)))
                else
                  (if n < 973 then
                    (if n < 972 then
                      240
                    else
                      241)
                  else
                    (if n < 974 then
                      241
                    else
                      246)))
              else
                (if n < 981 then
                  (if n < 978 then
                    (if n < 977 then
                      246
                    else
                      247)
                  else
                    (if n < 979 then
                      247
                    else
                      (if n < 980 then
                        248
                      else
                        249)))
                else
                  (if n < 983 then
                    250
                  else
                    251)))
            else
              (if n < 996 then
                (if n < 991 then
                  (if n < 988 then
                    (if n < 987 then
                      251
                    else
                      253)
                  else
                    (if n < 989 then
                      253
                    else
                      254))
                else
                  (if n < 993 then
                    (if n < 992 then
                      255
                    else
                      258)
                  else
                    258))
              else
                (if n < 1001 then
                  (if n < 998 then
                    259
                  else
                    (if n < 999 then
                      259
                    else
                      (if n < 1000 then
                        260
                      else
                        261)))
                else
                  (if n < 1003 then
                    (if n < 1002 then
                      262
                    else
                      263)
                  else
                    264))))
          else
            (if n < 1026 then
              (if n < 1016 then
                (if n < 1011 then
                  (if n < 1008 then
                    (if n < 1007 then
                      264
                    else
                      265)
                  else
                    (if n < 1009 then
                      268
                    else
                      273))
                else
                  (if n < 1013 then
                    275
                  else
                    (if n < 1014 then
                      279
                    else
                      (if n < 1015 then
                        279
                      else
                        281))))
              else
                (if n < 1021 then
                  (if n < 1018 then
                    281
                  else
                    (if n < 1019 then
                      281
                    else
                      282))
                else
                  (if n < 1023 then
                    (if n < 1022 then
                      282
                    else
                      283)
                  else
                    (if n < 1024 then
                      283
                    else
                      (if n < 1025 then
                        283
                      else
                        284)))))
            else
              (if n < 1036 then
                (if n < 1031 then
                  (if n < 1028 then
                    (if n < 1027 then
                      284
                    else
                      285)
                  else
                    (if n < 1029 then
                      286
                    else
                      288))
                else
                  (if n < 1033 then
                    (if n < 1032 then
                      288
                    else
                      289)
                  else
                    289))
              else
                (if n < 1041 then
                  (if n < 1038 then
                    290
                  else
                    (if n < 1039 then
                      290
                    else
                      (if n < 1040 then
                        291
                      else
                        292)))
                else
                  (if n < 1043 then
                    292
                  else
                    (if n < 1044 then
                      292
                    else
                      (if n < 1045 then
                        292
                      else
                        293)))))))
        else
          (if n < 1086 then
            (if n < 1066 then
              (if n < 1056 then
                (if n < 1051 then
                  (if n < 1048 then
                    (if n < 1047 then
                      296
                    else
                      298)
                  else
                    299)
                else
                  (if n < 1053 then
                    301
                  else
                    302))
              else
                (if n < 1061 then
                  (if n < 1058 then
                    (if n < 1057 then
                      303
                    else
                      306)
                  else
                    (if n < 1059 then
                      307
                    else
                      308))
                else
                  (if n < 1063 then
                    308
                  else
                    (if n < 1064 then
                      308
                    else
                      (if n < 1065 then
                        308
                      else
                        309)))))
            else
              (if n < 1076 then
                (if n < 1071 then
                  (if n < 1068 then
                    (if n < 1067 then
                      309
                    else
                      311)
                  else
                    (if n < 1069 then
                      311
                    else
                      (if n < 1070 then
                        312
                      else
                        314)))
                else
                  (if n < 1073 then
                    314
                  else
                    (if n < 1074 then
                      315
                    else
                      316)))
              else
                (if n < 1081 then
                  (if n < 1078 then
                    (if n < 1077 then
                      316
                    else
                      317)
                  else
                    (if n < 1079 then
                      318
                    else
                      (if n < 1080 then
                        318
                      else
                        320)))
                else
                  (if n < 1083 then
                    323
                  else
                    (if n < 1084 then
                      323
                    else
                      (if n < 1085 then
                        324
                      else
                        326))))))
          else
            (if n < 1106 then
              (if n < 1096 then
                (if n < 1091 then
                  (if n < 1088 then
                    (if n < 1087 then
                      326
                    else
                      327)
                  else
                    (if n < 1089 then
                      327
                    else
                      (if n < 1090 then
                        329
                      else
                        332)))
                else
                  (if n < 1093 then
                    (if n < 1092 then
                      333
                    else
                      334)
                  else
                    (if n < 1094 then
                      334
                    else
                      (if n < 1095 then
                        337
                      else
                        339))))
              else
                (if n < 1101 then
                  (if n < 1098 then
                    340
                  else
                    (if n < 1099 then
                      341
                    else
                      343))
                else
                  (if n < 1103 then
                    (if n < 1102 then
                      343
                    else
                      344)
                  else
                    (if n < 1104 then
                      344
                    else
                      (if n < 1105 then
                        344
                      else
                        345)))))
            else
              (if n < 1116 then
                (if n < 1111 then
                  (if n < 1108 then
                    346
                  else
                    347)
                else
                  (if n < 1113 then
                    348
                  else
                    (if n < 1114 then
                      348
                    else
                      (if n < 1115 then
                        348
                      else
                        349))))
              else
                (if n < 1121 then
                  (if n < 1118 then
                    353
                  else
                    (if n < 1119 then
                      354
                    else
                      (if n < 1120 then
                        356
                      else
                        360)))
                else
                  (if n < 1124 then
                    (if n < 1122 then
                      362
                    else
                      (if n < 1123 then
                        364
                      else
                        366))
                  else
                    (if n < 1125 then
                      366
                    else
                      (if n < 1126 then
                        366
                      else
                        367))))))))
      else
        (if n < 1207 then
          (if n < 1167 then
            (if n < 1147 then
              (if n < 1137 then
                (if n < 1132 then
                  (if n < 1129 then
                    (if n < 1128 then
                      369
                    else
                      370)
                  else
                    (if n < 1130 then
                      371
                    else
                      (if n < 1131 then
                        377
                      else
                        383)))
                else
                  (if n < 1134 then
                    (if n < 1133 then
                      384
                    else
                      386)
                  else
                    (if n < 1135 then
                      387
                    else
                      (if n < 1136 then
                        388
                      else
                        393))))
              else
                (if n < 1142 then
                  (if n < 1139 then
                    394
                  else
                    395)
                else
                  (if n < 1144 then
                    395
                  else
                    (if n < 1145 then
                      396
                    else
                      397))))
            else
              (if n < 1157 then
                (if n < 1152 then
                  (if n < 1149 then
                    398
                  else
                    399)
                else
                  (if n < 1154 then
                    400
                  else
                    (if n < 1155 then
                      400
                    else
                      401)))
              else
                (if n < 1162 then
                  (if n < 1159 then
                    (if n < 1158 then
                      401
                    else
                      403)
                  else
                    (if n < 1160 then
                      404
                    else
                      (if n < 1161 then
                        410
                      else
                        412)))
                else
                  (if n < 1164 then
                    (if n < 1163 then
                      416
                    else
                      417)
                  else
                    (if n < 1165 then
                      418
                    else
                      (if n < 1166 then
                        418
                      else
                        419))))))
          else
            (if n < 1187 then
              (if n < 1177 then
                (if n < 1172 then
                  (if n < 1169 then
                    419
                  else
                    (if n < 1170 then
                      420
                    else
                      (if n < 1171 then
                        421
                      else
                        422)))
                else
                  (if n < 1174 then
                    (if n < 1173 then
                      423
                    else
                      424)
                  else
                    (if n < 1175 then
                      428
                    else
                      (if n < 1176 then
                        428
                      else
                        429))))
              else
                (if n < 1182 then
                  (if n < 1179 then
                    429
                  else
                    (if n < 1180 then
                      433
                    else
                      435))
                else
                  (if n < 1184 then
                    (if n < 1183 then
                      435
                    else
                      438)
                  else
                    438)))
            else
              (if n < 1197 then
                (if n < 1192 then
                  (if n < 1189 then
                    441
                  else
                    (if n < 1190 then
                      442
                    else
                      (if n < 1191 then
                        444
                      else
                        445)))
                else
                  (if n < 1194 then
                    447
                  else
                    448))
              else
                (if n < 1202 then
                  (if n < 1199 then
                    (if n < 1198 then
                      449
                    else
                      450)
                  else
                    (if n < 1200 then
                      452
                    else
                      (if n < 1201 then
                        452
                      else
                        454)))
                else
                  (if n < 1204 then
                    (if n < 1203 then
                      454
                    else
                      456)
                  else
                    (if n < 1205 then
                      457
                    else
                      (if n < 1206 then
                        459
                      else
                        460)))))))
        else
          (if n < 1247 then
            (if n < 1227 then
              (if n < 1217 then
                (if n < 1212 then
                  (if n < 1209 then
                    463
                  else
                    (if n < 1210 then
                      466
                    else
                      (if n < 1211 then
                        468
                      else
                        478)))
                else
                  (if n < 1214 then
                    (if n < 1213 then
                      482
                    else
                      483)
                  else
                    (if n < 1215 then
                      487
                    else
                      (if n < 1216 then
                        492
                      else
                        494))))
              else
                (if n < 1222 then
                  (if n < 1219 then
                    (if n < 1218 then
                      495
                    else
                      502)
                  else
                    (if n < 1220 then
                      505
                    else
                      (if n < 1221 then
                        510
                      else
                        514)))
                else
                  (if n < 1224 then
                    (if n < 1223 then
                      514
                    else
                      518)
                  else
                    (if n < 1225 then
                      521
                    else
                      (if n < 1226 then
                        526
                      else
                        528)))))
            else
              (if n < 1237 then
                (if n < 1232 then
                  (if n < 1229 then
                    (if n < 1228 then
                      529
                    else
                      538)
                  else
                    (if n < 1230 then
                      543
                    else
                      (if n < 1231 then
                        543
                      else
                        548)))
                else
                  (if n < 1234 then
                    (if n < 1233 then
                      553
                    else
                      557)
                  else
                    (if n < 1235 then
                      567
                    else
                      (if n < 1236 then
                        569
                      else
                        573))))
              else
                (if n < 1242 then
                  (if n < 1239 then
                    (if n < 1238 then
                      578
                    else
                      588)
                  else
                    (if n < 1240 then
                      591
                    else
                      593))
                else
                  (if n < 1244 then
                    (if n < 1243 then
                      593
                    else
                      594)
                  else
                    (if n < 1245 then
                      594
                    else
                      605)))))
          else
            (if n < 1267 then
              (if n < 1257 then
                (if n < 1252 then
                  (if n < 1249 then
                    (if n < 1248 then
                      605
                    else
                      606)
                  else
                    (if n < 1250 then
                      611
                    else
                      (if n < 1251 then
                        611
                      else
                        612)))
                else
                  (if n < 1254 then
                    (if n < 1253 then
                      612
                    else
                      613)
                  else
                    (if n < 1255 then
                      613
                    else
                      (if n < 1256 then
                        616
                      else
                        621))))
              else
                (if n < 1262 then
                  (if n < 1259 then
                    (if n < 1258 then
                      622
                    else
                      626)
                  else
                    (if n < 1260 then
                      627
                    else
                      (if n < 1261 then
                        630
                      else
                        632)))
                else
                  (if n < 1264 then
                    (if n < 1263 then
                      633
                    else
                      635)
                  else
                    (if n < 1265 then
                      642
                    else
                      (if n < 1266 then
                        645
                      else
                        648)))))
            else
              (if n < 1277 then
                (if n < 1272 then
                  (if n < 1269 then
                    (if n < 1268 then
                      649
                    else
                      652)
                  else
                    (if n < 1270 then
                      657
                    else
                      (if n < 1271 then
                        661
                      else
                        664)))
                else
                  (if n < 1274 then
                    (if n < 1273 then
                      675
                    else
                      676)
                  else
                    (if n < 1275 then
                      676
                    else
                      (if n < 1276 then
                        681
                      else
                        696))))
              else
                (if n < 1282 then
                  (if n < 1279 then
                    (if n < 1278 then
                      714
                    else
                      728)
                  else
                    (if n < 1280 then
                      728
                    else
                      (if n < 1281 then
                        733
                      else
                        781)))
                else
                  (if n < 1285 then
                    (if n < 1283 then
                      782
                    else
                      (if n < 1284 then
                        866
                      else
                        873))
                  else
                    (if n < 1286 then
                      887
                    else
                      (if n < 1287 then
                        889
                      else
                        893)))))))))))

/-- Original strong-generator index of each incoming edge. -/
def golayDodecadOrbitGenerator (n : ℕ) : ℕ :=
  (if n < 644 then
    (if n < 322 then
      (if n < 161 then
        (if n < 80 then
          (if n < 40 then
            (if n < 20 then
              (if n < 10 then
                (if n < 5 then
                  (if n < 2 then
                    1
                  else
                    (if n < 3 then
                      2
                    else
                      (if n < 4 then
                        3
                      else
                        4)))
                else
                  (if n < 7 then
                    (if n < 6 then
                      5
                    else
                      6)
                  else
                    (if n < 8 then
                      8
                    else
                      (if n < 9 then
                        9
                      else
                        10))))
              else
                (if n < 15 then
                  (if n < 12 then
                    (if n < 11 then
                      11
                    else
                      12)
                  else
                    (if n < 13 then
                      13
                    else
                      (if n < 14 then
                        2
                      else
                        3)))
                else
                  (if n < 17 then
                    (if n < 16 then
                      4
                    else
                      5)
                  else
                    (if n < 18 then
                      6
                    else
                      (if n < 19 then
                        7
                      else
                        8)))))
            else
              (if n < 30 then
                (if n < 25 then
                  (if n < 22 then
                    (if n < 21 then
                      9
                    else
                      10)
                  else
                    (if n < 23 then
                      11
                    else
                      (if n < 24 then
                        13
                      else
                        1)))
                else
                  (if n < 27 then
                    (if n < 26 then
                      3
                    else
                      4)
                  else
                    (if n < 28 then
                      5
                    else
                      (if n < 29 then
                        6
                      else
                        7))))
              else
                (if n < 35 then
                  (if n < 32 then
                    (if n < 31 then
                      8
                    else
                      9)
                  else
                    (if n < 33 then
                      10
                    else
                      (if n < 34 then
                        11
                      else
                        12)))
                else
                  (if n < 37 then
                    (if n < 36 then
                      13
                    else
                      2)
                  else
                    (if n < 38 then
                      4
                    else
                      (if n < 39 then
                        6
                      else
                        7))))))
          else
            (if n < 60 then
              (if n < 50 then
                (if n < 45 then
                  (if n < 42 then
                    (if n < 41 then
                      8
                    else
                      9)
                  else
                    (if n < 43 then
                      10
                    else
                      (if n < 44 then
                        11
                      else
                        12)))
                else
                  (if n < 47 then
                    (if n < 46 then
                      13
                    else
                      2)
                  else
                    (if n < 48 then
                      5
                    else
                      (if n < 49 then
                        6
                      else
                        8))))
              else
                (if n < 55 then
                  (if n < 52 then
                    (if n < 51 then
                      9
                    else
                      10)
                  else
                    (if n < 53 then
                      11
                    else
                      (if n < 54 then
                        12
                      else
                        13)))
                else
                  (if n < 57 then
                    (if n < 56 then
                      2
                    else
                      7)
                  else
                    (if n < 58 then
                      8
                    else
                      (if n < 59 then
                        9
                      else
                        10)))))
            else
              (if n < 70 then
                (if n < 65 then
                  (if n < 62 then
                    (if n < 61 then
                      11
                    else
                      12)
                  else
                    (if n < 63 then
                      13
                    else
                      (if n < 64 then
                        1
                      else
                        2)))
                else
                  (if n < 67 then
                    (if n < 66 then
                      8
                    else
                      9)
                  else
                    (if n < 68 then
                      10
                    else
                      (if n < 69 then
                        11
                      else
                        12))))
              else
                (if n < 75 then
                  (if n < 72 then
                    (if n < 71 then
                      13
                    else
                      1)
                  else
                    (if n < 73 then
                      2
                    else
                      (if n < 74 then
                        3
                      else
                        5)))
                else
                  (if n < 77 then
                    (if n < 76 then
                      6
                    else
                      7)
                  else
                    (if n < 78 then
                      8
                    else
                      (if n < 79 then
                        9
                      else
                        10)))))))
        else
          (if n < 120 then
            (if n < 100 then
              (if n < 90 then
                (if n < 85 then
                  (if n < 82 then
                    (if n < 81 then
                      11
                    else
                      12)
                  else
                    (if n < 83 then
                      13
                    else
                      (if n < 84 then
                        1
                      else
                        2)))
                else
                  (if n < 87 then
                    (if n < 86 then
                      3
                    else
                      6)
                  else
                    (if n < 88 then
                      7
                    else
                      (if n < 89 then
                        8
                      else
                        9))))
              else
                (if n < 95 then
                  (if n < 92 then
                    (if n < 91 then
                      12
                    else
                      13)
                  else
                    (if n < 93 then
                      1
                    else
                      (if n < 94 then
                        2
                      else
                        3)))
                else
                  (if n < 97 then
                    (if n < 96 then
                      4
                    else
                      6)
                  else
                    (if n < 98 then
                      9
                    else
                      (if n < 99 then
                        11
                      else
                        12)))))
            else
              (if n < 110 then
                (if n < 105 then
                  (if n < 102 then
                    (if n < 101 then
                      1
                    else
                      3)
                  else
                    (if n < 103 then
                      7
                    else
                      (if n < 104 then
                        12
                      else
                        1)))
                else
                  (if n < 107 then
                    (if n < 106 then
                      2
                    else
                      3)
                  else
                    (if n < 108 then
                      4
                    else
                      (if n < 109 then
                        8
                      else
                        9))))
              else
                (if n < 115 then
                  (if n < 112 then
                    (if n < 111 then
                      10
                    else
                      11)
                  else
                    (if n < 113 then
                      13
                    else
                      (if n < 114 then
                        1
                      else
                        2)))
                else
                  (if n < 117 then
                    (if n < 116 then
                      3
                    else
                      4)
                  else
                    (if n < 118 then
                      7
                    else
                      (if n < 119 then
                        8
                      else
                        9))))))
          else
            (if n < 140 then
              (if n < 130 then
                (if n < 125 then
                  (if n < 122 then
                    (if n < 121 then
                      10
                    else
                      11)
                  else
                    (if n < 123 then
                      12
                    else
                      (if n < 124 then
                        13
                      else
                        1)))
                else
                  (if n < 127 then
                    (if n < 126 then
                      3
                    else
                      4)
                  else
                    (if n < 128 then
                      6
                    else
                      (if n < 129 then
                        7
                      else
                        8))))
              else
                (if n < 135 then
                  (if n < 132 then
                    (if n < 131 then
                      9
                    else
                      10)
                  else
                    (if n < 133 then
                      11
                    else
                      (if n < 134 then
                        12
                      else
                        13)))
                else
                  (if n < 137 then
                    (if n < 136 then
                      2
                    else
                      4)
                  else
                    (if n < 138 then
                      6
                    else
                      (if n < 139 then
                        7
                      else
                        10)))))
            else
              (if n < 150 then
                (if n < 145 then
                  (if n < 142 then
                    (if n < 141 then
                      11
                    else
                      12)
                  else
                    (if n < 143 then
                      13
                    else
                      (if n < 144 then
                        2
                      else
                        5)))
                else
                  (if n < 147 then
                    (if n < 146 then
                      7
                    else
                      8)
                  else
                    (if n < 148 then
                      9
                    else
                      (if n < 149 then
                        10
                      else
                        11))))
              else
                (if n < 155 then
                  (if n < 152 then
                    (if n < 151 then
                      2
                    else
                      6)
                  else
                    (if n < 153 then
                      7
                    else
                      (if n < 154 then
                        8
                      else
                        9)))
                else
                  (if n < 158 then
                    (if n < 156 then
                      10
                    else
                      (if n < 157 then
                        12
                      else
                        1))
                  else
                    (if n < 159 then
                      3
                    else
                      (if n < 160 then
                        9
                      else
                        10))))))))
      else
        (if n < 241 then
          (if n < 201 then
            (if n < 181 then
              (if n < 171 then
                (if n < 166 then
                  (if n < 163 then
                    (if n < 162 then
                      11
                    else
                      13)
                  else
                    (if n < 164 then
                      1
                    else
                      (if n < 165 then
                        2
                      else
                        8)))
                else
                  (if n < 168 then
                    (if n < 167 then
                      10
                    else
                      11)
                  else
                    (if n < 169 then
                      1
                    else
                      (if n < 170 then
                        3
                      else
                        5))))
              else
                (if n < 176 then
                  (if n < 173 then
                    (if n < 172 then
                      6
                    else
                      8)
                  else
                    (if n < 174 then
                      9
                    else
                      (if n < 175 then
                        11
                      else
                        13)))
                else
                  (if n < 178 then
                    (if n < 177 then
                      1
                    else
                      2)
                  else
                    (if n < 179 then
                      3
                    else
                      (if n < 180 then
                        5
                      else
                        7)))))
            else
              (if n < 191 then
                (if n < 186 then
                  (if n < 183 then
                    (if n < 182 then
                      9
                    else
                      10)
                  else
                    (if n < 184 then
                      12
                    else
                      (if n < 185 then
                        2
                      else
                        3)))
                else
                  (if n < 188 then
                    (if n < 187 then
                      4
                    else
                      7)
                  else
                    (if n < 189 then
                      9
                    else
                      (if n < 190 then
                        11
                      else
                        12))))
              else
                (if n < 196 then
                  (if n < 193 then
                    (if n < 192 then
                      13
                    else
                      2)
                  else
                    (if n < 194 then
                      3
                    else
                      (if n < 195 then
                        4
                      else
                        5)))
                else
                  (if n < 198 then
                    (if n < 197 then
                      7
                    else
                      9)
                  else
                    (if n < 199 then
                      10
                    else
                      (if n < 200 then
                        13
                      else
                        1))))))
          else
            (if n < 221 then
              (if n < 211 then
                (if n < 206 then
                  (if n < 203 then
                    (if n < 202 then
                      2
                    else
                      3)
                  else
                    (if n < 204 then
                      4
                    else
                      (if n < 205 then
                        5
                      else
                        6)))
                else
                  (if n < 208 then
                    (if n < 207 then
                      7
                    else
                      8)
                  else
                    (if n < 209 then
                      9
                    else
                      (if n < 210 then
                        10
                      else
                        11))))
              else
                (if n < 216 then
                  (if n < 213 then
                    (if n < 212 then
                      12
                    else
                      13)
                  else
                    (if n < 214 then
                      2
                    else
                      (if n < 215 then
                        3
                      else
                        4)))
                else
                  (if n < 218 then
                    (if n < 217 then
                      5
                    else
                      6)
                  else
                    (if n < 219 then
                      7
                    else
                      (if n < 220 then
                        8
                      else
                        9)))))
            else
              (if n < 231 then
                (if n < 226 then
                  (if n < 223 then
                    (if n < 222 then
                      10
                    else
                      11)
                  else
                    (if n < 224 then
                      12
                    else
                      (if n < 225 then
                        13
                      else
                        6)))
                else
                  (if n < 228 then
                    (if n < 227 then
                      8
                    else
                      11)
                  else
                    (if n < 229 then
                      2
                    else
                      (if n < 230 then
                        5
                      else
                        7))))
              else
                (if n < 236 then
                  (if n < 233 then
                    (if n < 232 then
                      9
                    else
                      10)
                  else
                    (if n < 234 then
                      11
                    else
                      (if n < 235 then
                        12
                      else
                        13)))
                else
                  (if n < 238 then
                    (if n < 237 then
                      6
                    else
                      7)
                  else
                    (if n < 239 then
                      8
                    else
                      (if n < 240 then
                        9
                      else
                        12)))))))
        else
          (if n < 281 then
            (if n < 261 then
              (if n < 251 then
                (if n < 246 then
                  (if n < 243 then
                    (if n < 242 then
                      13
                    else
                      1)
                  else
                    (if n < 244 then
                      7
                    else
                      (if n < 245 then
                        10
                      else
                        11)))
                else
                  (if n < 248 then
                    (if n < 247 then
                      12
                    else
                      3)
                  else
                    (if n < 249 then
                      8
                    else
                      (if n < 250 then
                        10
                      else
                        12))))
              else
                (if n < 256 then
                  (if n < 253 then
                    (if n < 252 then
                      13
                    else
                      2)
                  else
                    (if n < 254 then
                      3
                    else
                      (if n < 255 then
                        5
                      else
                        7)))
                else
                  (if n < 258 then
                    (if n < 257 then
                      9
                    else
                      11)
                  else
                    (if n < 259 then
                      13
                    else
                      (if n < 260 then
                        1
                      else
                        2)))))
            else
              (if n < 271 then
                (if n < 266 then
                  (if n < 263 then
                    (if n < 262 then
                      3
                    else
                      6)
                  else
                    (if n < 264 then
                      9
                    else
                      (if n < 265 then
                        13
                      else
                        1)))
                else
                  (if n < 268 then
                    (if n < 267 then
                      2
                    else
                      3)
                  else
                    (if n < 269 then
                      4
                    else
                      (if n < 270 then
                        5
                      else
                        6))))
              else
                (if n < 276 then
                  (if n < 273 then
                    (if n < 272 then
                      7
                    else
                      11)
                  else
                    (if n < 274 then
                      12
                    else
                      (if n < 275 then
                        1
                      else
                        3)))
                else
                  (if n < 278 then
                    (if n < 277 then
                      4
                    else
                      5)
                  else
                    (if n < 279 then
                      7
                    else
                      (if n < 280 then
                        11
                      else
                        12))))))
          else
            (if n < 301 then
              (if n < 291 then
                (if n < 286 then
                  (if n < 283 then
                    (if n < 282 then
                      13
                    else
                      1)
                  else
                    (if n < 284 then
                      2
                    else
                      (if n < 285 then
                        3
                      else
                        5)))
                else
                  (if n < 288 then
                    (if n < 287 then
                      9
                    else
                      10)
                  else
                    (if n < 289 then
                      11
                    else
                      (if n < 290 then
                        1
                      else
                        3))))
              else
                (if n < 296 then
                  (if n < 293 then
                    (if n < 292 then
                      6
                    else
                      9)
                  else
                    (if n < 294 then
                      10
                    else
                      (if n < 295 then
                        12
                      else
                        3)))
                else
                  (if n < 298 then
                    (if n < 297 then
                      4
                    else
                      5)
                  else
                    (if n < 299 then
                      7
                    else
                      (if n < 300 then
                        8
                      else
                        10)))))
            else
              (if n < 311 then
                (if n < 306 then
                  (if n < 303 then
                    (if n < 302 then
                      11
                    else
                      12)
                  else
                    (if n < 304 then
                      2
                    else
                      (if n < 305 then
                        6
                      else
                        8)))
                else
                  (if n < 308 then
                    (if n < 307 then
                      9
                    else
                      11)
                  else
                    (if n < 309 then
                      12
                    else
                      (if n < 310 then
                        13
                      else
                        1))))
              else
                (if n < 316 then
                  (if n < 313 then
                    (if n < 312 then
                      3
                    else
                      9)
                  else
                    (if n < 314 then
                      11
                    else
                      (if n < 315 then
                        12
                      else
                        13)))
                else
                  (if n < 319 then
                    (if n < 317 then
                      1
                    else
                      (if n < 318 then
                        2
                      else
                        3))
                  else
                    (if n < 320 then
                      8
                    else
                      (if n < 321 then
                        9
                      else
                        11)))))))))
    else
      (if n < 483 then
        (if n < 402 then
          (if n < 362 then
            (if n < 342 then
              (if n < 332 then
                (if n < 327 then
                  (if n < 324 then
                    (if n < 323 then
                      12
                    else
                      13)
                  else
                    (if n < 325 then
                      1
                    else
                      (if n < 326 then
                        3
                      else
                        8)))
                else
                  (if n < 329 then
                    (if n < 328 then
                      10
                    else
                      1)
                  else
                    (if n < 330 then
                      2
                    else
                      (if n < 331 then
                        10
                      else
                        11))))
              else
                (if n < 337 then
                  (if n < 334 then
                    (if n < 333 then
                      12
                    else
                      13)
                  else
                    (if n < 335 then
                      2
                    else
                      (if n < 336 then
                        3
                      else
                        5)))
                else
                  (if n < 339 then
                    (if n < 338 then
                      6
                    else
                      7)
                  else
                    (if n < 340 then
                      11
                    else
                      (if n < 341 then
                        12
                      else
                        11)))))
            else
              (if n < 352 then
                (if n < 347 then
                  (if n < 344 then
                    (if n < 343 then
                      13
                    else
                      2)
                  else
                    (if n < 345 then
                      3
                    else
                      (if n < 346 then
                        8
                      else
                        9)))
                else
                  (if n < 349 then
                    (if n < 348 then
                      10
                    else
                      11)
                  else
                    (if n < 350 then
                      13
                    else
                      (if n < 351 then
                        2
                      else
                        3))))
              else
                (if n < 357 then
                  (if n < 354 then
                    (if n < 353 then
                      11
                    else
                      1)
                  else
                    (if n < 355 then
                      3
                    else
                      (if n < 356 then
                        4
                      else
                        5)))
                else
                  (if n < 359 then
                    (if n < 358 then
                      7
                    else
                      9)
                  else
                    (if n < 360 then
                      11
                    else
                      (if n < 361 then
                        12
                      else
                        7))))))
          else
            (if n < 382 then
              (if n < 372 then
                (if n < 367 then
                  (if n < 364 then
                    (if n < 363 then
                      8
                    else
                      9)
                  else
                    (if n < 365 then
                      10
                    else
                      (if n < 366 then
                        11
                      else
                        13)))
                else
                  (if n < 369 then
                    (if n < 368 then
                      3
                    else
                      10)
                  else
                    (if n < 370 then
                      12
                    else
                      (if n < 371 then
                        13
                      else
                        1))))
              else
                (if n < 377 then
                  (if n < 374 then
                    (if n < 373 then
                      2
                    else
                      3)
                  else
                    (if n < 375 then
                      8
                    else
                      (if n < 376 then
                        11
                      else
                        12)))
                else
                  (if n < 379 then
                    (if n < 378 then
                      1
                    else
                      2)
                  else
                    (if n < 380 then
                      9
                    else
                      (if n < 381 then
                        1
                      else
                        3)))))
            else
              (if n < 392 then
                (if n < 387 then
                  (if n < 384 then
                    (if n < 383 then
                      4
                    else
                      5)
                  else
                    (if n < 385 then
                      6
                    else
                      (if n < 386 then
                        9
                      else
                        12)))
                else
                  (if n < 389 then
                    (if n < 388 then
                      1
                    else
                      3)
                  else
                    (if n < 390 then
                      4
                    else
                      (if n < 391 then
                        5
                      else
                        8))))
              else
                (if n < 397 then
                  (if n < 394 then
                    (if n < 393 then
                      9
                    else
                      12)
                  else
                    (if n < 395 then
                      13
                    else
                      (if n < 396 then
                        1
                      else
                        2)))
                else
                  (if n < 399 then
                    (if n < 398 then
                      3
                    else
                      4)
                  else
                    (if n < 400 then
                      8
                    else
                      (if n < 401 then
                        9
                      else
                        10)))))))
        else
          (if n < 442 then
            (if n < 422 then
              (if n < 412 then
                (if n < 407 then
                  (if n < 404 then
                    (if n < 403 then
                      11
                    else
                      13)
                  else
                    (if n < 405 then
                      2
                    else
                      (if n < 406 then
                        6
                      else
                        11)))
                else
                  (if n < 409 then
                    (if n < 408 then
                      1
                    else
                      3)
                  else
                    (if n < 410 then
                      11
                    else
                      (if n < 411 then
                        13
                      else
                        2))))
              else
                (if n < 417 then
                  (if n < 414 then
                    (if n < 413 then
                      11
                    else
                      12)
                  else
                    (if n < 415 then
                      3
                    else
                      (if n < 416 then
                        5
                      else
                        9)))
                else
                  (if n < 419 then
                    (if n < 418 then
                      11
                    else
                      12)
                  else
                    (if n < 420 then
                      13
                    else
                      (if n < 421 then
                        3
                      else
                        11)))))
            else
              (if n < 432 then
                (if n < 427 then
                  (if n < 424 then
                    (if n < 423 then
                      12
                    else
                      13)
                  else
                    (if n < 425 then
                      1
                    else
                      (if n < 426 then
                        3
                      else
                        4)))
                else
                  (if n < 429 then
                    (if n < 428 then
                      5
                    else
                      9)
                  else
                    (if n < 430 then
                      12
                    else
                      (if n < 431 then
                        1
                      else
                        3))))
              else
                (if n < 437 then
                  (if n < 434 then
                    (if n < 433 then
                      5
                    else
                      6)
                  else
                    (if n < 435 then
                      10
                    else
                      (if n < 436 then
                        12
                      else
                        13)))
                else
                  (if n < 439 then
                    (if n < 438 then
                      9
                    else
                      13)
                  else
                    (if n < 440 then
                      1
                    else
                      (if n < 441 then
                        2
                      else
                        3))))))
          else
            (if n < 462 then
              (if n < 452 then
                (if n < 447 then
                  (if n < 444 then
                    (if n < 443 then
                      4
                    else
                      5)
                  else
                    (if n < 445 then
                      6
                    else
                      (if n < 446 then
                        8
                      else
                        9)))
                else
                  (if n < 449 then
                    (if n < 448 then
                      10
                    else
                      11)
                  else
                    (if n < 450 then
                      12
                    else
                      (if n < 451 then
                        13
                      else
                        11))))
              else
                (if n < 457 then
                  (if n < 454 then
                    (if n < 453 then
                      12
                    else
                      13)
                  else
                    (if n < 455 then
                      1
                    else
                      (if n < 456 then
                        3
                      else
                        4)))
                else
                  (if n < 459 then
                    (if n < 458 then
                      5
                    else
                      7)
                  else
                    (if n < 460 then
                      8
                    else
                      (if n < 461 then
                        10
                      else
                        11)))))
            else
              (if n < 472 then
                (if n < 467 then
                  (if n < 464 then
                    (if n < 463 then
                      12
                    else
                      13)
                  else
                    (if n < 465 then
                      1
                    else
                      (if n < 466 then
                        3
                      else
                        9)))
                else
                  (if n < 469 then
                    (if n < 468 then
                      12
                    else
                      13)
                  else
                    (if n < 470 then
                      3
                    else
                      (if n < 471 then
                        13
                      else
                        2))))
              else
                (if n < 477 then
                  (if n < 474 then
                    (if n < 473 then
                      3
                    else
                      6)
                  else
                    (if n < 475 then
                      7
                    else
                      (if n < 476 then
                        9
                      else
                        11)))
                else
                  (if n < 480 then
                    (if n < 478 then
                      12
                    else
                      (if n < 479 then
                        3
                      else
                        4))
                  else
                    (if n < 481 then
                      5
                    else
                      (if n < 482 then
                        6
                      else
                        12))))))))
      else
        (if n < 563 then
          (if n < 523 then
            (if n < 503 then
              (if n < 493 then
                (if n < 488 then
                  (if n < 485 then
                    (if n < 484 then
                      1
                    else
                      2)
                  else
                    (if n < 486 then
                      4
                    else
                      (if n < 487 then
                        8
                      else
                        10)))
                else
                  (if n < 490 then
                    (if n < 489 then
                      1
                    else
                      2)
                  else
                    (if n < 491 then
                      4
                    else
                      (if n < 492 then
                        5
                      else
                        10))))
              else
                (if n < 498 then
                  (if n < 495 then
                    (if n < 494 then
                      11
                    else
                      6)
                  else
                    (if n < 496 then
                      9
                    else
                      (if n < 497 then
                        11
                      else
                        1)))
                else
                  (if n < 500 then
                    (if n < 499 then
                      3
                    else
                      8)
                  else
                    (if n < 501 then
                      10
                    else
                      (if n < 502 then
                        11
                      else
                        4)))))
            else
              (if n < 513 then
                (if n < 508 then
                  (if n < 505 then
                    (if n < 504 then
                      7
                    else
                      8)
                  else
                    (if n < 506 then
                      9
                    else
                      (if n < 507 then
                        12
                      else
                        13)))
                else
                  (if n < 510 then
                    (if n < 509 then
                      8
                    else
                      1)
                  else
                    (if n < 511 then
                      3
                    else
                      (if n < 512 then
                        1
                      else
                        9))))
              else
                (if n < 518 then
                  (if n < 515 then
                    (if n < 514 then
                      13
                    else
                      1)
                  else
                    (if n < 516 then
                      8
                    else
                      (if n < 517 then
                        10
                      else
                        12)))
                else
                  (if n < 520 then
                    (if n < 519 then
                      1
                    else
                      2)
                  else
                    (if n < 521 then
                      3
                    else
                      (if n < 522 then
                        13
                      else
                        3))))))
          else
            (if n < 543 then
              (if n < 533 then
                (if n < 528 then
                  (if n < 525 then
                    (if n < 524 then
                      1
                    else
                      3)
                  else
                    (if n < 526 then
                      7
                    else
                      (if n < 527 then
                        8
                      else
                        9)))
                else
                  (if n < 530 then
                    (if n < 529 then
                      10
                    else
                      11)
                  else
                    (if n < 531 then
                      13
                    else
                      (if n < 532 then
                        7
                      else
                        11))))
              else
                (if n < 538 then
                  (if n < 535 then
                    (if n < 534 then
                      12
                    else
                      13)
                  else
                    (if n < 536 then
                      3
                    else
                      (if n < 537 then
                        8
                      else
                        12)))
                else
                  (if n < 540 then
                    (if n < 539 then
                      13
                    else
                      2)
                  else
                    (if n < 541 then
                      7
                    else
                      (if n < 542 then
                        10
                      else
                        12)))))
            else
              (if n < 553 then
                (if n < 548 then
                  (if n < 545 then
                    (if n < 544 then
                      13
                    else
                      2)
                  else
                    (if n < 546 then
                      12
                    else
                      (if n < 547 then
                        1
                      else
                        2)))
                else
                  (if n < 550 then
                    3
                  else
                    (if n < 551 then
                      5
                    else
                      (if n < 552 then
                        13
                      else
                        1))))
              else
                (if n < 558 then
                  (if n < 555 then
                    (if n < 554 then
                      3
                    else
                      12)
                  else
                    (if n < 556 then
                      3
                    else
                      (if n < 557 then
                        1
                      else
                        3)))
                else
                  (if n < 560 then
                    (if n < 559 then
                      5
                    else
                      8)
                  else
                    (if n < 561 then
                      9
                    else
                      (if n < 562 then
                        10
                      else
                        11)))))))
        else
          (if n < 603 then
            (if n < 583 then
              (if n < 573 then
                (if n < 568 then
                  (if n < 565 then
                    (if n < 564 then
                      13
                    else
                      3)
                  else
                    (if n < 566 then
                      4
                    else
                      (if n < 567 then
                        11
                      else
                        13)))
                else
                  (if n < 570 then
                    (if n < 569 then
                      1
                    else
                      3)
                  else
                    (if n < 571 then
                      12
                    else
                      (if n < 572 then
                        9
                      else
                        12))))
              else
                (if n < 578 then
                  (if n < 575 then
                    (if n < 574 then
                      13
                    else
                      1)
                  else
                    (if n < 576 then
                      2
                    else
                      (if n < 577 then
                        3
                      else
                        12)))
                else
                  (if n < 580 then
                    (if n < 579 then
                      13
                    else
                      3)
                  else
                    (if n < 581 then
                      13
                    else
                      (if n < 582 then
                        1
                      else
                        3)))))
            else
              (if n < 593 then
                (if n < 588 then
                  (if n < 585 then
                    (if n < 584 then
                      12
                    else
                      1)
                  else
                    (if n < 586 then
                      3
                    else
                      (if n < 587 then
                        4
                      else
                        7)))
                else
                  (if n < 590 then
                    (if n < 589 then
                      13
                    else
                      6)
                  else
                    (if n < 591 then
                      9
                    else
                      (if n < 592 then
                        12
                      else
                        7))))
              else
                (if n < 598 then
                  (if n < 595 then
                    (if n < 594 then
                      12
                    else
                      13)
                  else
                    (if n < 596 then
                      1
                    else
                      (if n < 597 then
                        2
                      else
                        3)))
                else
                  (if n < 600 then
                    (if n < 599 then
                      8
                    else
                      13)
                  else
                    (if n < 601 then
                      3
                    else
                      (if n < 602 then
                        2
                      else
                        3))))))
          else
            (if n < 623 then
              (if n < 613 then
                (if n < 608 then
                  (if n < 605 then
                    (if n < 604 then
                      4
                    else
                      8)
                  else
                    (if n < 606 then
                      9
                    else
                      (if n < 607 then
                        10
                      else
                        11)))
                else
                  (if n < 610 then
                    (if n < 609 then
                      1
                    else
                      3)
                  else
                    (if n < 611 then
                      11
                    else
                      (if n < 612 then
                        6
                      else
                        7))))
              else
                (if n < 618 then
                  (if n < 615 then
                    (if n < 614 then
                      8
                    else
                      9)
                  else
                    (if n < 616 then
                      10
                    else
                      (if n < 617 then
                        12
                      else
                        8)))
                else
                  (if n < 620 then
                    (if n < 619 then
                      9
                    else
                      10)
                  else
                    (if n < 621 then
                      1
                    else
                      (if n < 622 then
                        3
                      else
                        5)))))
            else
              (if n < 633 then
                (if n < 628 then
                  (if n < 625 then
                    (if n < 624 then
                      7
                    else
                      9)
                  else
                    (if n < 626 then
                      10
                    else
                      (if n < 627 then
                        13
                      else
                        1)))
                else
                  (if n < 630 then
                    (if n < 629 then
                      3
                    else
                      6)
                  else
                    (if n < 631 then
                      7
                    else
                      (if n < 632 then
                        10
                      else
                        11))))
              else
                (if n < 638 then
                  (if n < 635 then
                    (if n < 634 then
                      13
                    else
                      1)
                  else
                    (if n < 636 then
                      3
                    else
                      (if n < 637 then
                        4
                      else
                        5)))
                else
                  (if n < 641 then
                    (if n < 639 then
                      6
                    else
                      (if n < 640 then
                        7
                      else
                        13))
                  else
                    (if n < 642 then
                      1
                    else
                      (if n < 643 then
                        2
                      else
                        3))))))))))
  else
    (if n < 966 then
      (if n < 805 then
        (if n < 724 then
          (if n < 684 then
            (if n < 664 then
              (if n < 654 then
                (if n < 649 then
                  (if n < 646 then
                    (if n < 645 then
                      6
                    else
                      1)
                  else
                    (if n < 647 then
                      2
                    else
                      (if n < 648 then
                        6
                      else
                        3)))
                else
                  (if n < 651 then
                    (if n < 650 then
                      5
                    else
                      6)
                  else
                    (if n < 652 then
                      10
                    else
                      (if n < 653 then
                        11
                      else
                        12))))
              else
                (if n < 659 then
                  (if n < 656 then
                    (if n < 655 then
                      1
                    else
                      3)
                  else
                    (if n < 657 then
                      6
                    else
                      (if n < 658 then
                        8
                      else
                        10)))
                else
                  (if n < 661 then
                    (if n < 660 then
                      7
                    else
                      8)
                  else
                    (if n < 662 then
                      9
                    else
                      (if n < 663 then
                        10
                      else
                        11)))))
            else
              (if n < 674 then
                (if n < 669 then
                  (if n < 666 then
                    (if n < 665 then
                      13
                    else
                      7)
                  else
                    (if n < 667 then
                      8
                    else
                      (if n < 668 then
                        10
                      else
                        3)))
                else
                  (if n < 671 then
                    (if n < 670 then
                      11
                    else
                      13)
                  else
                    (if n < 672 then
                      1
                    else
                      (if n < 673 then
                        3
                      else
                        10))))
              else
                (if n < 679 then
                  (if n < 676 then
                    (if n < 675 then
                      13
                    else
                      2)
                  else
                    (if n < 677 then
                      3
                    else
                      (if n < 678 then
                        5
                      else
                        7)))
                else
                  (if n < 681 then
                    (if n < 680 then
                      8
                    else
                      10)
                  else
                    (if n < 682 then
                      1
                    else
                      (if n < 683 then
                        2
                      else
                        1))))))
          else
            (if n < 704 then
              (if n < 694 then
                (if n < 689 then
                  (if n < 686 then
                    (if n < 685 then
                      3
                    else
                      7)
                  else
                    (if n < 687 then
                      7
                    else
                      (if n < 688 then
                        8
                      else
                        3)))
                else
                  (if n < 691 then
                    (if n < 690 then
                      2
                    else
                      3)
                  else
                    (if n < 692 then
                      5
                    else
                      (if n < 693 then
                        6
                      else
                        7))))
              else
                (if n < 699 then
                  (if n < 696 then
                    (if n < 695 then
                      9
                    else
                      12)
                  else
                    (if n < 697 then
                      13
                    else
                      (if n < 698 then
                        11
                      else
                        12)))
                else
                  (if n < 701 then
                    (if n < 700 then
                      13
                    else
                      6)
                  else
                    (if n < 702 then
                      10
                    else
                      (if n < 703 then
                        13
                      else
                        3)))))
            else
              (if n < 714 then
                (if n < 709 then
                  (if n < 706 then
                    (if n < 705 then
                      9
                    else
                      11)
                  else
                    (if n < 707 then
                      13
                    else
                      (if n < 708 then
                        2
                      else
                        5)))
                else
                  (if n < 711 then
                    (if n < 710 then
                      6
                    else
                      9)
                  else
                    (if n < 712 then
                      10
                    else
                      (if n < 713 then
                        12
                      else
                        13))))
              else
                (if n < 719 then
                  (if n < 716 then
                    (if n < 715 then
                      6
                    else
                      7)
                  else
                    (if n < 717 then
                      8
                    else
                      (if n < 718 then
                        10
                      else
                        13)))
                else
                  (if n < 721 then
                    (if n < 720 then
                      7
                    else
                      12)
                  else
                    (if n < 722 then
                      13
                    else
                      (if n < 723 then
                        8
                      else
                        13)))))))
        else
          (if n < 764 then
            (if n < 744 then
              (if n < 734 then
                (if n < 729 then
                  (if n < 726 then
                    (if n < 725 then
                      1
                    else
                      3)
                  else
                    (if n < 727 then
                      1
                    else
                      (if n < 728 then
                        3
                      else
                        4)))
                else
                  (if n < 731 then
                    (if n < 730 then
                      6
                    else
                      7)
                  else
                    (if n < 732 then
                      8
                    else
                      (if n < 733 then
                        10
                      else
                        11))))
              else
                (if n < 739 then
                  (if n < 736 then
                    (if n < 735 then
                      4
                    else
                      11)
                  else
                    (if n < 737 then
                      12
                    else
                      (if n < 738 then
                        13
                      else
                        1)))
                else
                  (if n < 741 then
                    (if n < 740 then
                      3
                    else
                      13)
                  else
                    (if n < 742 then
                      2
                    else
                      (if n < 743 then
                        8
                      else
                        10)))))
            else
              (if n < 754 then
                (if n < 749 then
                  (if n < 746 then
                    (if n < 745 then
                      12
                    else
                      3)
                  else
                    (if n < 747 then
                      6
                    else
                      (if n < 748 then
                        7
                      else
                        9)))
                else
                  (if n < 751 then
                    (if n < 750 then
                      2
                    else
                      5)
                  else
                    (if n < 752 then
                      7
                    else
                      (if n < 753 then
                        8
                      else
                        10))))
              else
                (if n < 759 then
                  (if n < 756 then
                    (if n < 755 then
                      12
                    else
                      13)
                  else
                    (if n < 757 then
                      3
                    else
                      (if n < 758 then
                        10
                      else
                        13)))
                else
                  (if n < 761 then
                    (if n < 760 then
                      2
                    else
                      10)
                  else
                    (if n < 762 then
                      12
                    else
                      (if n < 763 then
                        1
                      else
                        6))))))
          else
            (if n < 784 then
              (if n < 774 then
                (if n < 769 then
                  (if n < 766 then
                    (if n < 765 then
                      9
                    else
                      13)
                  else
                    (if n < 767 then
                      3
                    else
                      (if n < 768 then
                        9
                      else
                        1)))
                else
                  (if n < 771 then
                    (if n < 770 then
                      7
                    else
                      13)
                  else
                    (if n < 772 then
                      1
                    else
                      (if n < 773 then
                        2
                      else
                        1))))
              else
                (if n < 779 then
                  (if n < 776 then
                    (if n < 775 then
                      3
                    else
                      4)
                  else
                    (if n < 777 then
                      9
                    else
                      (if n < 778 then
                        4
                      else
                        9)))
                else
                  (if n < 781 then
                    (if n < 780 then
                      12
                    else
                      13)
                  else
                    (if n < 782 then
                      3
                    else
                      (if n < 783 then
                        3
                      else
                        8)))))
            else
              (if n < 794 then
                (if n < 789 then
                  (if n < 786 then
                    (if n < 785 then
                      9
                    else
                      13)
                  else
                    (if n < 787 then
                      1
                    else
                      (if n < 788 then
                        3
                      else
                        8)))
                else
                  (if n < 791 then
                    (if n < 790 then
                      10
                    else
                      2)
                  else
                    (if n < 792 then
                      12
                    else
                      (if n < 793 then
                        1
                      else
                        13))))
              else
                (if n < 799 then
                  (if n < 796 then
                    (if n < 795 then
                      12
                    else
                      13)
                  else
                    (if n < 797 then
                      3
                    else
                      (if n < 798 then
                        4
                      else
                        5)))
                else
                  (if n < 802 then
                    (if n < 800 then
                      12
                    else
                      (if n < 801 then
                        1
                      else
                        3))
                  else
                    (if n < 803 then
                      8
                    else
                      (if n < 804 then
                        1
                      else
                        2))))))))
      else
        (if n < 885 then
          (if n < 845 then
            (if n < 825 then
              (if n < 815 then
                (if n < 810 then
                  (if n < 807 then
                    (if n < 806 then
                      3
                    else
                      9)
                  else
                    (if n < 808 then
                      11
                    else
                      (if n < 809 then
                        13
                      else
                        2)))
                else
                  (if n < 812 then
                    (if n < 811 then
                      12
                    else
                      8)
                  else
                    (if n < 813 then
                      10
                    else
                      (if n < 814 then
                        1
                      else
                        3))))
              else
                (if n < 820 then
                  (if n < 817 then
                    (if n < 816 then
                      9
                    else
                      12)
                  else
                    (if n < 818 then
                      13
                    else
                      (if n < 819 then
                        1
                      else
                        2)))
                else
                  (if n < 822 then
                    (if n < 821 then
                      11
                    else
                      10)
                  else
                    (if n < 823 then
                      11
                    else
                      (if n < 824 then
                        9
                      else
                        13)))))
            else
              (if n < 835 then
                (if n < 830 then
                  (if n < 827 then
                    (if n < 826 then
                      6
                    else
                      7)
                  else
                    (if n < 828 then
                      12
                    else
                      (if n < 829 then
                        1
                      else
                        7)))
                else
                  (if n < 832 then
                    (if n < 831 then
                      12
                    else
                      13)
                  else
                    (if n < 833 then
                      4
                    else
                      (if n < 834 then
                        7
                      else
                        13))))
              else
                (if n < 840 then
                  (if n < 837 then
                    (if n < 836 then
                      1
                    else
                      8)
                  else
                    (if n < 838 then
                      12
                    else
                      (if n < 839 then
                        13
                      else
                        2)))
                else
                  (if n < 842 then
                    (if n < 841 then
                      6
                    else
                      12)
                  else
                    (if n < 843 then
                      8
                    else
                      (if n < 844 then
                        9
                      else
                        10))))))
          else
            (if n < 865 then
              (if n < 855 then
                (if n < 850 then
                  (if n < 847 then
                    (if n < 846 then
                      11
                    else
                      13)
                  else
                    (if n < 848 then
                      1
                    else
                      (if n < 849 then
                        8
                      else
                        5)))
                else
                  (if n < 852 then
                    12
                  else
                    (if n < 853 then
                      1
                    else
                      (if n < 854 then
                        3
                      else
                        4))))
              else
                (if n < 860 then
                  (if n < 857 then
                    (if n < 856 then
                      3
                    else
                      13)
                  else
                    (if n < 858 then
                      7
                    else
                      (if n < 859 then
                        1
                      else
                        2)))
                else
                  (if n < 862 then
                    (if n < 861 then
                      10
                    else
                      5)
                  else
                    (if n < 863 then
                      13
                    else
                      (if n < 864 then
                        2
                      else
                        11)))))
            else
              (if n < 875 then
                (if n < 870 then
                  (if n < 867 then
                    (if n < 866 then
                      1
                    else
                      2)
                  else
                    (if n < 868 then
                      5
                    else
                      (if n < 869 then
                        6
                      else
                        9)))
                else
                  (if n < 872 then
                    (if n < 871 then
                      11
                    else
                      12)
                  else
                    (if n < 873 then
                      1
                    else
                      (if n < 874 then
                        12
                      else
                        13))))
              else
                (if n < 880 then
                  (if n < 877 then
                    (if n < 876 then
                      13
                    else
                      12)
                  else
                    (if n < 878 then
                      2
                    else
                      (if n < 879 then
                        3
                      else
                        5)))
                else
                  (if n < 882 then
                    (if n < 881 then
                      13
                    else
                      5)
                  else
                    (if n < 883 then
                      3
                    else
                      (if n < 884 then
                        6
                      else
                        10)))))))
        else
          (if n < 925 then
            (if n < 905 then
              (if n < 895 then
                (if n < 890 then
                  (if n < 887 then
                    (if n < 886 then
                      11
                    else
                      12)
                  else
                    (if n < 888 then
                      3
                    else
                      (if n < 889 then
                        4
                      else
                        5)))
                else
                  (if n < 892 then
                    (if n < 891 then
                      6
                    else
                      7)
                  else
                    (if n < 893 then
                      8
                    else
                      (if n < 894 then
                        9
                      else
                        10))))
              else
                (if n < 900 then
                  (if n < 897 then
                    (if n < 896 then
                      11
                    else
                      13)
                  else
                    (if n < 898 then
                      7
                    else
                      (if n < 899 then
                        8
                      else
                        9)))
                else
                  (if n < 902 then
                    (if n < 901 then
                      10
                    else
                      12)
                  else
                    (if n < 903 then
                      8
                    else
                      (if n < 904 then
                        9
                      else
                        10)))))
            else
              (if n < 915 then
                (if n < 910 then
                  (if n < 907 then
                    (if n < 906 then
                      2
                    else
                      7)
                  else
                    (if n < 908 then
                      3
                    else
                      (if n < 909 then
                        8
                      else
                        9)))
                else
                  (if n < 912 then
                    (if n < 911 then
                      12
                    else
                      5)
                  else
                    (if n < 913 then
                      10
                    else
                      (if n < 914 then
                        2
                      else
                        3))))
              else
                (if n < 920 then
                  (if n < 917 then
                    (if n < 916 then
                      5
                    else
                      8)
                  else
                    (if n < 918 then
                      10
                    else
                      (if n < 919 then
                        2
                      else
                        9)))
                else
                  (if n < 922 then
                    (if n < 921 then
                      2
                    else
                      5)
                  else
                    (if n < 923 then
                      6
                    else
                      (if n < 924 then
                        7
                      else
                        10))))))
          else
            (if n < 945 then
              (if n < 935 then
                (if n < 930 then
                  (if n < 927 then
                    (if n < 926 then
                      12
                    else
                      2)
                  else
                    (if n < 928 then
                      5
                    else
                      (if n < 929 then
                        7
                      else
                        9)))
                else
                  (if n < 932 then
                    (if n < 931 then
                      11
                    else
                      13)
                  else
                    (if n < 933 then
                      13
                    else
                      12)))
              else
                (if n < 940 then
                  (if n < 937 then
                    (if n < 936 then
                      12
                    else
                      2)
                  else
                    (if n < 938 then
                      3
                    else
                      (if n < 939 then
                        5
                      else
                        6)))
                else
                  (if n < 942 then
                    (if n < 941 then
                      8
                    else
                      9)
                  else
                    (if n < 943 then
                      10
                    else
                      (if n < 944 then
                        11
                      else
                        13)))))
            else
              (if n < 955 then
                (if n < 950 then
                  (if n < 947 then
                    (if n < 946 then
                      1
                    else
                      3)
                  else
                    (if n < 948 then
                      8
                    else
                      (if n < 949 then
                        10
                      else
                        11)))
                else
                  (if n < 952 then
                    (if n < 951 then
                      13
                    else
                      2)
                  else
                    (if n < 953 then
                      12
                    else
                      (if n < 954 then
                        5
                      else
                        9))))
              else
                (if n < 960 then
                  (if n < 957 then
                    (if n < 956 then
                      13
                    else
                      2)
                  else
                    (if n < 958 then
                      9
                    else
                      (if n < 959 then
                        11
                      else
                        9)))
                else
                  (if n < 963 then
                    (if n < 961 then
                      10
                    else
                      13)
                  else
                    (if n < 964 then
                      9
                    else
                      (if n < 965 then
                        11
                      else
                        13)))))))))
    else
      (if n < 1127 then
        (if n < 1046 then
          (if n < 1006 then
            (if n < 986 then
              (if n < 976 then
                (if n < 971 then
                  (if n < 968 then
                    (if n < 967 then
                      12
                    else
                      3)
                  else
                    (if n < 969 then
                      5
                    else
                      (if n < 970 then
                        12
                      else
                        9)))
                else
                  (if n < 973 then
                    (if n < 972 then
                      13
                    else
                      8)
                  else
                    (if n < 974 then
                      12
                    else
                      (if n < 975 then
                        9
                      else
                        11))))
              else
                (if n < 981 then
                  (if n < 978 then
                    (if n < 977 then
                      13
                    else
                      11)
                  else
                    (if n < 979 then
                      12
                    else
                      (if n < 980 then
                        7
                      else
                        13)))
                else
                  (if n < 983 then
                    (if n < 982 then
                      1
                    else
                      8)
                  else
                    (if n < 984 then
                      3
                    else
                      (if n < 985 then
                        5
                      else
                        6)))))
            else
              (if n < 996 then
                (if n < 991 then
                  (if n < 988 then
                    (if n < 987 then
                      13
                    else
                      12)
                  else
                    (if n < 989 then
                      13
                    else
                      (if n < 990 then
                        2
                      else
                        13)))
                else
                  (if n < 993 then
                    (if n < 992 then
                      1
                    else
                      3)
                  else
                    (if n < 994 then
                      4
                    else
                      (if n < 995 then
                        6
                      else
                        8))))
              else
                (if n < 1001 then
                  (if n < 998 then
                    (if n < 997 then
                      6
                    else
                      12)
                  else
                    (if n < 999 then
                      13
                    else
                      (if n < 1000 then
                        1
                      else
                        12)))
                else
                  (if n < 1003 then
                    (if n < 1002 then
                      13
                    else
                      12)
                  else
                    (if n < 1004 then
                      1
                    else
                      (if n < 1005 then
                        5
                      else
                        9))))))
          else
            (if n < 1026 then
              (if n < 1016 then
                (if n < 1011 then
                  (if n < 1008 then
                    (if n < 1007 then
                      13
                    else
                      8)
                  else
                    (if n < 1009 then
                      13
                    else
                      (if n < 1010 then
                        7
                      else
                        11)))
                else
                  (if n < 1013 then
                    (if n < 1012 then
                      4
                    else
                      10)
                  else
                    (if n < 1014 then
                      3
                    else
                      (if n < 1015 then
                        12
                      else
                        2))))
              else
                (if n < 1021 then
                  (if n < 1018 then
                    (if n < 1017 then
                      3
                    else
                      5)
                  else
                    (if n < 1019 then
                      6
                    else
                      (if n < 1020 then
                        2
                      else
                        11)))
                else
                  (if n < 1023 then
                    (if n < 1022 then
                      12
                    else
                      1)
                  else
                    (if n < 1024 then
                      4
                    else
                      (if n < 1025 then
                        9
                      else
                        4)))))
            else
              (if n < 1036 then
                (if n < 1031 then
                  (if n < 1028 then
                    (if n < 1027 then
                      9
                    else
                      11)
                  else
                    (if n < 1029 then
                      8
                    else
                      (if n < 1030 then
                        3
                      else
                        9)))
                else
                  (if n < 1033 then
                    (if n < 1032 then
                      10
                    else
                      7)
                  else
                    (if n < 1034 then
                      9
                    else
                      (if n < 1035 then
                        10
                      else
                        11))))
              else
                (if n < 1041 then
                  (if n < 1038 then
                    (if n < 1037 then
                      2
                    else
                      7)
                  else
                    (if n < 1039 then
                      11
                    else
                      (if n < 1040 then
                        3
                      else
                        1)))
                else
                  (if n < 1043 then
                    (if n < 1042 then
                      3
                    else
                      8)
                  else
                    (if n < 1044 then
                      11
                    else
                      (if n < 1045 then
                        12
                      else
                        2)))))))
        else
          (if n < 1086 then
            (if n < 1066 then
              (if n < 1056 then
                (if n < 1051 then
                  (if n < 1048 then
                    (if n < 1047 then
                      12
                    else
                      9)
                  else
                    (if n < 1049 then
                      1
                    else
                      (if n < 1050 then
                        8
                      else
                        13)))
                else
                  (if n < 1053 then
                    (if n < 1052 then
                      3
                    else
                      4)
                  else
                    (if n < 1054 then
                      9
                    else
                      (if n < 1055 then
                        10
                      else
                        11))))
              else
                (if n < 1061 then
                  (if n < 1058 then
                    (if n < 1057 then
                      13
                    else
                      1)
                  else
                    (if n < 1059 then
                      13
                    else
                      (if n < 1060 then
                        3
                      else
                        5)))
                else
                  (if n < 1063 then
                    (if n < 1062 then
                      9
                    else
                      10)
                  else
                    (if n < 1064 then
                      11
                    else
                      (if n < 1065 then
                        13
                      else
                        1)))))
            else
              (if n < 1076 then
                (if n < 1071 then
                  (if n < 1068 then
                    9
                  else
                    (if n < 1069 then
                      12
                    else
                      (if n < 1070 then
                        12
                      else
                        2)))
                else
                  (if n < 1073 then
                    (if n < 1072 then
                      3
                    else
                      11)
                  else
                    (if n < 1074 then
                      2
                    else
                      (if n < 1075 then
                        11
                      else
                        12))))
              else
                (if n < 1081 then
                  (if n < 1078 then
                    (if n < 1077 then
                      13
                    else
                      1)
                  else
                    (if n < 1079 then
                      7
                    else
                      (if n < 1080 then
                        8
                      else
                        3)))
                else
                  (if n < 1083 then
                    (if n < 1082 then
                      3
                    else
                      6)
                  else
                    (if n < 1084 then
                      10
                    else
                      (if n < 1085 then
                        13
                      else
                        12))))))
          else
            (if n < 1106 then
              (if n < 1096 then
                (if n < 1091 then
                  (if n < 1088 then
                    (if n < 1087 then
                      13
                    else
                      3)
                  else
                    (if n < 1089 then
                      4
                    else
                      (if n < 1090 then
                        10
                      else
                        13)))
                else
                  (if n < 1093 then
                    (if n < 1092 then
                      10
                    else
                      4)
                  else
                    (if n < 1094 then
                      12
                    else
                      (if n < 1095 then
                        9
                      else
                        13))))
              else
                (if n < 1101 then
                  (if n < 1098 then
                    (if n < 1097 then
                      3
                    else
                      8)
                  else
                    (if n < 1099 then
                      12
                    else
                      (if n < 1100 then
                        4
                      else
                        9)))
                else
                  (if n < 1103 then
                    (if n < 1102 then
                      10
                    else
                      8)
                  else
                    (if n < 1104 then
                      9
                    else
                      (if n < 1105 then
                        10
                      else
                        1)))))
            else
              (if n < 1116 then
                (if n < 1111 then
                  (if n < 1108 then
                    (if n < 1107 then
                      2
                    else
                      5)
                  else
                    (if n < 1109 then
                      2
                    else
                      (if n < 1110 then
                        5
                      else
                        9)))
                else
                  (if n < 1113 then
                    (if n < 1112 then
                      1
                    else
                      2)
                  else
                    (if n < 1114 then
                      3
                    else
                      (if n < 1115 then
                        5
                      else
                        2))))
              else
                (if n < 1121 then
                  (if n < 1118 then
                    (if n < 1117 then
                      8
                    else
                      10)
                  else
                    (if n < 1119 then
                      13
                    else
                      (if n < 1120 then
                        10
                      else
                        3)))
                else
                  (if n < 1124 then
                    (if n < 1122 then
                      13
                    else
                      (if n < 1123 then
                        12
                      else
                        4))
                  else
                    (if n < 1125 then
                      9
                    else
                      (if n < 1126 then
                        10
                      else
                        13))))))))
      else
        (if n < 1207 then
          (if n < 1167 then
            (if n < 1147 then
              (if n < 1137 then
                (if n < 1132 then
                  (if n < 1129 then
                    (if n < 1128 then
                      3
                    else
                      12)
                  else
                    (if n < 1130 then
                      6
                    else
                      (if n < 1131 then
                        9
                      else
                        11)))
                else
                  (if n < 1134 then
                    (if n < 1133 then
                      12
                    else
                      7)
                  else
                    (if n < 1135 then
                      12
                    else
                      (if n < 1136 then
                        13
                      else
                        3))))
              else
                (if n < 1142 then
                  (if n < 1139 then
                    (if n < 1138 then
                      3
                    else
                      4)
                  else
                    (if n < 1140 then
                      2
                    else
                      (if n < 1141 then
                        3
                      else
                        6)))
                else
                  (if n < 1144 then
                    (if n < 1143 then
                      7
                    else
                      10)
                  else
                    (if n < 1145 then
                      8
                    else
                      (if n < 1146 then
                        8
                      else
                        10)))))
            else
              (if n < 1157 then
                (if n < 1152 then
                  (if n < 1149 then
                    (if n < 1148 then
                      2
                    else
                      10)
                  else
                    (if n < 1150 then
                      3
                    else
                      (if n < 1151 then
                        9
                      else
                        13)))
                else
                  (if n < 1154 then
                    (if n < 1153 then
                      1
                    else
                      7)
                  else
                    (if n < 1155 then
                      8
                    else
                      (if n < 1156 then
                        1
                      else
                        3))))
              else
                (if n < 1162 then
                  (if n < 1159 then
                    5
                  else
                    (if n < 1160 then
                      13
                    else
                      (if n < 1161 then
                        2
                      else
                        12)))
                else
                  (if n < 1164 then
                    13
                  else
                    (if n < 1165 then
                      7
                    else
                      (if n < 1166 then
                        10
                      else
                        1))))))
          else
            (if n < 1187 then
              (if n < 1177 then
                (if n < 1172 then
                  (if n < 1169 then
                    (if n < 1168 then
                      3
                    else
                      7)
                  else
                    (if n < 1170 then
                      12
                    else
                      (if n < 1171 then
                        12
                      else
                        13)))
                else
                  (if n < 1174 then
                    (if n < 1173 then
                      13
                    else
                      12)
                  else
                    (if n < 1175 then
                      3
                    else
                      (if n < 1176 then
                        12
                      else
                        3))))
              else
                (if n < 1182 then
                  (if n < 1179 then
                    (if n < 1178 then
                      7
                    else
                      8)
                  else
                    (if n < 1180 then
                      12
                    else
                      (if n < 1181 then
                        8
                      else
                        9)))
                else
                  (if n < 1184 then
                    (if n < 1183 then
                      10
                    else
                      6)
                  else
                    (if n < 1185 then
                      7
                    else
                      (if n < 1186 then
                        9
                      else
                        13)))))
            else
              (if n < 1197 then
                (if n < 1192 then
                  (if n < 1189 then
                    (if n < 1188 then
                      9
                    else
                      12)
                  else
                    (if n < 1190 then
                      10
                    else
                      (if n < 1191 then
                        1
                      else
                        3)))
                else
                  (if n < 1194 then
                    (if n < 1193 then
                      4
                    else
                      6)
                  else
                    (if n < 1195 then
                      2
                    else
                      (if n < 1196 then
                        3
                      else
                        6))))
              else
                (if n < 1202 then
                  (if n < 1199 then
                    (if n < 1198 then
                      13
                    else
                      12)
                  else
                    (if n < 1200 then
                      9
                    else
                      (if n < 1201 then
                        13
                      else
                        12)))
                else
                  (if n < 1204 then
                    (if n < 1203 then
                      13
                    else
                      12)
                  else
                    (if n < 1205 then
                      12
                    else
                      13))))))
        else
          (if n < 1247 then
            (if n < 1227 then
              (if n < 1217 then
                (if n < 1212 then
                  (if n < 1209 then
                    (if n < 1208 then
                      7
                    else
                      8)
                  else
                    (if n < 1210 then
                      1
                    else
                      (if n < 1211 then
                        3
                      else
                        12)))
                else
                  (if n < 1214 then
                    (if n < 1213 then
                      10
                    else
                      11)
                  else
                    (if n < 1215 then
                      3
                    else
                      (if n < 1216 then
                        1
                      else
                        13))))
              else
                (if n < 1222 then
                  (if n < 1219 then
                    (if n < 1218 then
                      12
                    else
                      13)
                  else
                    (if n < 1220 then
                      13
                    else
                      (if n < 1221 then
                        13
                      else
                        11)))
                else
                  (if n < 1224 then
                    13
                  else
                    (if n < 1225 then
                      11
                    else
                      (if n < 1226 then
                        3
                      else
                        4)))))
            else
              (if n < 1237 then
                (if n < 1232 then
                  (if n < 1229 then
                    (if n < 1228 then
                      3
                    else
                      13)
                  else
                    (if n < 1230 then
                      10
                    else
                      (if n < 1231 then
                        11
                      else
                        13)))
                else
                  (if n < 1234 then
                    (if n < 1233 then
                      13
                    else
                      10)
                  else
                    13))
              else
                (if n < 1242 then
                  (if n < 1239 then
                    (if n < 1238 then
                      12
                    else
                      1)
                  else
                    (if n < 1240 then
                      3
                    else
                      (if n < 1241 then
                        9
                      else
                        10)))
                else
                  (if n < 1244 then
                    (if n < 1243 then
                      11
                    else
                      3)
                  else
                    (if n < 1245 then
                      13
                    else
                      (if n < 1246 then
                        2
                      else
                        6))))))
          else
            (if n < 1267 then
              (if n < 1257 then
                (if n < 1252 then
                  (if n < 1249 then
                    (if n < 1248 then
                      12
                    else
                      9)
                  else
                    (if n < 1250 then
                      7
                    else
                      (if n < 1251 then
                        8
                      else
                        2)))
                else
                  (if n < 1254 then
                    (if n < 1253 then
                      11
                    else
                      5)
                  else
                    (if n < 1255 then
                      9
                    else
                      (if n < 1256 then
                        2
                      else
                        10))))
              else
                (if n < 1262 then
                  (if n < 1259 then
                    (if n < 1258 then
                      9
                    else
                      5)
                  else
                    (if n < 1260 then
                      11
                    else
                      (if n < 1261 then
                        1
                      else
                        8)))
                else
                  (if n < 1264 then
                    (if n < 1263 then
                      1
                    else
                      13)
                  else
                    (if n < 1265 then
                      3
                    else
                      (if n < 1266 then
                        11
                      else
                        9)))))
            else
              (if n < 1277 then
                (if n < 1272 then
                  (if n < 1269 then
                    (if n < 1268 then
                      10
                    else
                      5)
                  else
                    (if n < 1270 then
                      3
                    else
                      (if n < 1271 then
                        5
                      else
                        10)))
                else
                  (if n < 1274 then
                    (if n < 1273 then
                      3
                    else
                      6)
                  else
                    (if n < 1275 then
                      7
                    else
                      (if n < 1276 then
                        11
                      else
                        12))))
              else
                (if n < 1282 then
                  (if n < 1279 then
                    (if n < 1278 then
                      13
                    else
                      9)
                  else
                    (if n < 1280 then
                      11
                    else
                      (if n < 1281 then
                        6
                      else
                        12)))
                else
                  (if n < 1285 then
                    (if n < 1283 then
                      12
                    else
                      (if n < 1284 then
                        9
                      else
                        10))
                  else
                    (if n < 1286 then
                      9
                    else
                      (if n < 1287 then
                        13
                      else
                        8)))))))))))

/-- Inverse lookup of actual coefficient labels, with 1288 for unused labels. -/
def golayDodecadOrbitInverse (n : ℕ) : ℕ :=
  (if n < 2048 then
    (if n < 1024 then
      (if n < 512 then
        (if n < 256 then
          (if n < 128 then
            (if n < 64 then
              (if n < 32 then
                (if n < 16 then
                  1288
                else
                  (if n < 24 then
                    (if n < 20 then
                      (if n < 18 then
                        (if n < 17 then
                          1288
                        else
                          0)
                      else
                        (if n < 19 then
                          11
                        else
                          1288))
                    else
                      (if n < 22 then
                        (if n < 21 then
                          7
                        else
                          1288)
                      else
                        (if n < 23 then
                          1288
                        else
                          1224)))
                  else
                    (if n < 28 then
                      (if n < 26 then
                        (if n < 25 then
                          81
                        else
                          1288)
                      else
                        (if n < 27 then
                          1288
                        else
                          580))
                    else
                      (if n < 30 then
                        (if n < 29 then
                          1288
                        else
                          51)
                      else
                        (if n < 31 then
                          386
                        else
                          1288)))))
              else
                (if n < 48 then
                  (if n < 40 then
                    (if n < 36 then
                      (if n < 34 then
                        (if n < 33 then
                          1288
                        else
                          123)
                      else
                        (if n < 35 then
                          530
                        else
                          1288))
                    else
                      (if n < 38 then
                        (if n < 37 then
                          50
                        else
                          1288)
                      else
                        (if n < 39 then
                          1288
                        else
                          121)))
                  else
                    (if n < 44 then
                      (if n < 42 then
                        (if n < 41 then
                          40
                        else
                          1288)
                      else
                        (if n < 43 then
                          1288
                        else
                          529))
                    else
                      (if n < 46 then
                        (if n < 45 then
                          1288
                        else
                          97)
                      else
                        (if n < 47 then
                          521
                        else
                          1288))))
                else
                  (if n < 56 then
                    (if n < 52 then
                      (if n < 50 then
                        (if n < 49 then
                          1288
                        else
                          12)
                      else
                        (if n < 51 then
                          122
                        else
                          1288))
                    else
                      (if n < 54 then
                        (if n < 53 then
                          112
                        else
                          1288)
                      else
                        (if n < 55 then
                          1288
                        else
                          10)))
                  else
                    (if n < 60 then
                      (if n < 58 then
                        (if n < 57 then
                          82
                        else
                          1288)
                      else
                        (if n < 59 then
                          1288
                        else
                          103))
                    else
                      (if n < 62 then
                        (if n < 61 then
                          1288
                        else
                          111)
                      else
                        (if n < 63 then
                          80
                        else
                          1288))))))
            else
              (if n < 96 then
                (if n < 80 then
                  (if n < 72 then
                    (if n < 68 then
                      (if n < 66 then
                        1288
                      else
                        (if n < 67 then
                          1128
                        else
                          368))
                    else
                      (if n < 70 then
                        (if n < 69 then
                          266
                        else
                          680)
                      else
                        1288))
                  else
                    (if n < 76 then
                      (if n < 74 then
                        (if n < 73 then
                          65
                        else
                          394)
                      else
                        1288)
                    else
                      (if n < 78 then
                        1288
                      else
                        (if n < 79 then
                          675
                        else
                          392))))
                else
                  (if n < 88 then
                    (if n < 84 then
                      (if n < 82 then
                        (if n < 81 then
                          1288
                        else
                          370)
                      else
                        (if n < 83 then
                          1288
                        else
                          1045))
                    else
                      (if n < 86 then
                        (if n < 85 then
                          467
                        else
                          1288)
                      else
                        (if n < 87 then
                          619
                        else
                          1288)))
                  else
                    (if n < 92 then
                      (if n < 90 then
                        (if n < 89 then
                          486
                        else
                          1288)
                      else
                        (if n < 91 then
                          560
                        else
                          1288))
                    else
                      (if n < 94 then
                        (if n < 93 then
                          1288
                        else
                          623)
                      else
                        (if n < 95 then
                          1288
                        else
                          107)))))
              else
                (if n < 112 then
                  (if n < 104 then
                    (if n < 100 then
                      (if n < 98 then
                        (if n < 97 then
                          1288
                        else
                          610)
                      else
                        (if n < 99 then
                          95
                        else
                          1288))
                    else
                      (if n < 102 then
                        (if n < 101 then
                          1288
                        else
                          90)
                      else
                        (if n < 103 then
                          528
                        else
                          1288)))
                  else
                    (if n < 108 then
                      (if n < 106 then
                        (if n < 105 then
                          517
                        else
                          1288)
                      else
                        (if n < 107 then
                          1288
                        else
                          89))
                    else
                      (if n < 110 then
                        (if n < 109 then
                          406
                        else
                          1288)
                      else
                        (if n < 111 then
                          1288
                        else
                          120))))
                else
                  (if n < 120 then
                    (if n < 116 then
                      (if n < 114 then
                        (if n < 113 then
                          1288
                        else
                          385)
                      else
                        (if n < 115 then
                          443
                        else
                          1288))
                    else
                      (if n < 118 then
                        (if n < 117 then
                          78
                        else
                          1288)
                      else
                        (if n < 119 then
                          1288
                        else
                          554)))
                  else
                    (if n < 124 then
                      (if n < 122 then
                        (if n < 121 then
                          1288
                        else
                          109)
                      else
                        (if n < 123 then
                          8
                        else
                          1288))
                    else
                      (if n < 126 then
                        (if n < 125 then
                          117
                        else
                          1288)
                      else
                        (if n < 127 then
                          1288
                        else
                          304)))))))
          else
            (if n < 192 then
              (if n < 160 then
                (if n < 144 then
                  (if n < 136 then
                    (if n < 132 then
                      (if n < 130 then
                        1288
                      else
                        (if n < 131 then
                          468
                        else
                          516))
                    else
                      (if n < 134 then
                        (if n < 133 then
                          466
                        else
                          631)
                      else
                        1288))
                  else
                    (if n < 140 then
                      (if n < 138 then
                        (if n < 137 then
                          531
                        else
                          559)
                      else
                        1288)
                    else
                      (if n < 142 then
                        1288
                      else
                        (if n < 143 then
                          679
                        else
                          39))))
                else
                  (if n < 152 then
                    (if n < 148 then
                      (if n < 146 then
                        (if n < 145 then
                          1288
                        else
                          1083)
                      else
                        (if n < 147 then
                          99
                        else
                          1288))
                    else
                      (if n < 150 then
                        (if n < 149 then
                          118
                        else
                          1288)
                      else
                        (if n < 151 then
                          1288
                        else
                          88)))
                  else
                    (if n < 156 then
                      (if n < 154 then
                        (if n < 153 then
                          1288
                        else
                          379)
                      else
                        (if n < 155 then
                          685
                        else
                          1288))
                    else
                      (if n < 158 then
                        (if n < 157 then
                          519
                        else
                          1288)
                      else
                        (if n < 159 then
                          1288
                        else
                          53)))))
              else
                (if n < 176 then
                  (if n < 168 then
                    (if n < 164 then
                      (if n < 162 then
                        (if n < 161 then
                          1288
                        else
                          1097)
                      else
                        (if n < 163 then
                          1288
                        else
                          633))
                    else
                      (if n < 166 then
                        (if n < 165 then
                          637
                        else
                          1288)
                      else
                        (if n < 167 then
                          91
                        else
                          1288)))
                  else
                    (if n < 172 then
                      (if n < 170 then
                        (if n < 169 then
                          345
                        else
                          1288)
                      else
                        (if n < 171 then
                          670
                        else
                          1288))
                    else
                      (if n < 174 then
                        (if n < 173 then
                          1288
                        else
                          561)
                      else
                        (if n < 175 then
                          1288
                        else
                          322))))
                else
                  (if n < 184 then
                    (if n < 180 then
                      (if n < 178 then
                        (if n < 177 then
                          1288
                        else
                          9)
                      else
                        (if n < 179 then
                          400
                        else
                          1288))
                    else
                      (if n < 182 then
                        (if n < 181 then
                          1288
                        else
                          632)
                      else
                        (if n < 183 then
                          79
                        else
                          1288)))
                  else
                    (if n < 188 then
                      (if n < 186 then
                        (if n < 185 then
                          25
                        else
                          1288)
                      else
                        (if n < 187 then
                          1288
                        else
                          110))
                    else
                      (if n < 190 then
                        (if n < 189 then
                          669
                        else
                          1288)
                      else
                        (if n < 191 then
                          1288
                        else
                          4))))))
            else
              (if n < 224 then
                (if n < 208 then
                  (if n < 200 then
                    (if n < 196 then
                      (if n < 194 then
                        1288
                      else
                        (if n < 195 then
                          98
                        else
                          401))
                    else
                      (if n < 198 then
                        (if n < 197 then
                          630
                        else
                          52)
                      else
                        1288))
                  else
                    (if n < 204 then
                      (if n < 202 then
                        (if n < 201 then
                          673
                        else
                          320)
                      else
                        1288)
                    else
                      (if n < 206 then
                        1288
                      else
                        (if n < 207 then
                          227
                        else
                          323))))
                else
                  (if n < 216 then
                    (if n < 212 then
                      (if n < 210 then
                        (if n < 209 then
                          1288
                        else
                          158)
                      else
                        (if n < 211 then
                          369
                        else
                          1288))
                    else
                      (if n < 214 then
                        (if n < 213 then
                          1288
                        else
                          402)
                      else
                        (if n < 215 then
                          338
                        else
                          1288)))
                  else
                    (if n < 220 then
                      (if n < 218 then
                        (if n < 217 then
                          74
                        else
                          1288)
                      else
                        (if n < 219 then
                          1288
                        else
                          525))
                    else
                      (if n < 222 then
                        (if n < 221 then
                          563
                        else
                          1288)
                      else
                        (if n < 223 then
                          1288
                        else
                          327)))))
              else
                (if n < 240 then
                  (if n < 232 then
                    (if n < 228 then
                      (if n < 226 then
                        (if n < 225 then
                          1288
                        else
                          48)
                      else
                        (if n < 227 then
                          105
                        else
                          1288))
                    else
                      (if n < 230 then
                        (if n < 229 then
                          76
                        else
                          1288)
                      else
                        (if n < 231 then
                          1288
                        else
                          640)))
                  else
                    (if n < 236 then
                      (if n < 234 then
                        (if n < 233 then
                          1288
                        else
                          527)
                      else
                        (if n < 235 then
                          321
                        else
                          1288))
                    else
                      (if n < 238 then
                        (if n < 237 then
                          119
                        else
                          1288)
                      else
                        (if n < 239 then
                          1288
                        else
                          54))))
                else
                  (if n < 248 then
                    (if n < 244 then
                      (if n < 242 then
                        (if n < 241 then
                          1288
                        else
                          583)
                      else
                        (if n < 243 then
                          1288
                        else
                          618))
                    else
                      (if n < 246 then
                        (if n < 245 then
                          588
                        else
                          1288)
                      else
                        (if n < 247 then
                          562
                        else
                          1288)))
                  else
                    (if n < 252 then
                      (if n < 250 then
                        (if n < 249 then
                          674
                        else
                          1288)
                      else
                        (if n < 251 then
                          393
                        else
                          1288))
                    else
                      (if n < 254 then
                        (if n < 253 then
                          1288
                        else
                          551)
                      else
                        (if n < 255 then
                          1288
                        else
                          403))))))))
        else
          (if n < 384 then
            (if n < 320 then
              (if n < 288 then
                (if n < 272 then
                  (if n < 264 then
                    (if n < 260 then
                      (if n < 258 then
                        (if n < 257 then
                          1288
                        else
                          56)
                      else
                        (if n < 259 then
                          1288
                        else
                          459))
                    else
                      (if n < 262 then
                        (if n < 261 then
                          1288
                        else
                          1205)
                      else
                        (if n < 263 then
                          1288
                        else
                          1211)))
                  else
                    (if n < 268 then
                      (if n < 266 then
                        (if n < 265 then
                          1288
                        else
                          1275)
                      else
                        (if n < 267 then
                          1288
                        else
                          1040))
                    else
                      (if n < 270 then
                        (if n < 269 then
                          1288
                        else
                          700)
                      else
                        (if n < 271 then
                          1288
                        else
                          711))))
                else
                  (if n < 280 then
                    (if n < 276 then
                      (if n < 274 then
                        1288
                      else
                        (if n < 275 then
                          413
                        else
                          622))
                    else
                      (if n < 278 then
                        1288
                      else
                        (if n < 279 then
                          1196
                        else
                          773)))
                  else
                    (if n < 284 then
                      (if n < 282 then
                        1288
                      else
                        (if n < 283 then
                          1239
                        else
                          478))
                    else
                      (if n < 286 then
                        1288
                      else
                        (if n < 287 then
                          126
                        else
                          1036)))))
              else
                (if n < 304 then
                  (if n < 296 then
                    1288
                  else
                    (if n < 300 then
                      (if n < 298 then
                        (if n < 297 then
                          1113
                        else
                          480)
                      else
                        (if n < 299 then
                          1253
                        else
                          412))
                    else
                      (if n < 302 then
                        (if n < 301 then
                          1049
                        else
                          1208)
                      else
                        (if n < 303 then
                          139
                        else
                          397))))
                else
                  (if n < 312 then
                    (if n < 308 then
                      1288
                    else
                      (if n < 310 then
                        (if n < 309 then
                          592
                        else
                          1256)
                      else
                        (if n < 311 then
                          710
                        else
                          1161)))
                  else
                    (if n < 316 then
                      1288
                    else
                      (if n < 318 then
                        (if n < 317 then
                          681
                        else
                          746)
                      else
                        (if n < 319 then
                          621
                        else
                          1092))))))
            else
              (if n < 352 then
                (if n < 336 then
                  (if n < 328 then
                    (if n < 324 then
                      (if n < 322 then
                        (if n < 321 then
                          1288
                        else
                          442)
                      else
                        (if n < 323 then
                          742
                        else
                          1288))
                    else
                      (if n < 326 then
                        (if n < 325 then
                          1288
                        else
                          755)
                      else
                        (if n < 327 then
                          557
                        else
                          1288)))
                  else
                    (if n < 332 then
                      (if n < 330 then
                        (if n < 329 then
                          1288
                        else
                          757)
                      else
                        (if n < 331 then
                          907
                        else
                          1288))
                    else
                      (if n < 334 then
                        (if n < 333 then
                          1288
                        else
                          1107)
                      else
                        (if n < 335 then
                          872
                        else
                          1288))))
                else
                  (if n < 344 then
                    (if n < 340 then
                      1288
                    else
                      (if n < 342 then
                        (if n < 341 then
                          748
                        else
                          712)
                      else
                        (if n < 343 then
                          296
                        else
                          1096)))
                  else
                    (if n < 348 then
                      (if n < 346 then
                        (if n < 345 then
                          715
                        else
                          1046)
                      else
                        (if n < 347 then
                          129
                        else
                          1280))
                    else
                      1288)))
              else
                (if n < 368 then
                  (if n < 360 then
                    (if n < 356 then
                      (if n < 354 then
                        (if n < 353 then
                          1240
                        else
                          737)
                      else
                        (if n < 355 then
                          1145
                        else
                          747))
                    else
                      (if n < 358 then
                        (if n < 357 then
                          373
                        else
                          614)
                      else
                        (if n < 359 then
                          456
                        else
                          1184)))
                  else
                    (if n < 364 then
                      (if n < 362 then
                        (if n < 361 then
                          735
                        else
                          1203)
                      else
                        (if n < 363 then
                          1074
                        else
                          706))
                    else
                      (if n < 366 then
                        (if n < 365 then
                          602
                        else
                          704)
                      else
                        (if n < 367 then
                          1139
                        else
                          1067))))
                else
                  (if n < 376 then
                    (if n < 372 then
                      (if n < 370 then
                        (if n < 369 then
                          734
                        else
                          1242)
                      else
                        (if n < 371 then
                          705
                        else
                          1178))
                    else
                      (if n < 374 then
                        (if n < 373 then
                          1123
                        else
                          388)
                      else
                        (if n < 375 then
                          1177
                        else
                          336)))
                  else
                    (if n < 380 then
                      (if n < 378 then
                        (if n < 377 then
                          613
                        else
                          709)
                      else
                        (if n < 379 then
                          1076
                        else
                          828))
                    else
                      (if n < 382 then
                        (if n < 381 then
                          431
                        else
                          594)
                      else
                        (if n < 383 then
                          408
                        else
                          1081)))))))
          else
            (if n < 448 then
              (if n < 416 then
                (if n < 400 then
                  (if n < 392 then
                    (if n < 388 then
                      (if n < 386 then
                        (if n < 385 then
                          1288
                        else
                          983)
                      else
                        (if n < 387 then
                          1288
                        else
                          731))
                    else
                      (if n < 390 then
                        (if n < 389 then
                          1146
                        else
                          1288)
                      else
                        (if n < 391 then
                          730
                        else
                          1288)))
                  else
                    (if n < 396 then
                      (if n < 394 then
                        (if n < 393 then
                          1288
                        else
                          716)
                      else
                        (if n < 395 then
                          1288
                        else
                          997))
                    else
                      (if n < 398 then
                        (if n < 397 then
                          14
                        else
                          1288)
                      else
                        (if n < 399 then
                          750
                        else
                          1288))))
                else
                  (if n < 408 then
                    (if n < 404 then
                      (if n < 402 then
                        (if n < 401 then
                          1262
                        else
                          688)
                      else
                        (if n < 403 then
                          1141
                        else
                          299))
                    else
                      (if n < 406 then
                        (if n < 405 then
                          1052
                        else
                          1164)
                      else
                        (if n < 407 then
                          708
                        else
                          1022)))
                  else
                    (if n < 412 then
                      (if n < 410 then
                        (if n < 409 then
                          455
                        else
                          1114)
                      else
                        (if n < 411 then
                          193
                        else
                          1227))
                    else
                      (if n < 414 then
                        (if n < 413 then
                          1071
                        else
                          743)
                      else
                        (if n < 415 then
                          1250
                        else
                          138)))))
              else
                (if n < 432 then
                  (if n < 424 then
                    (if n < 420 then
                      (if n < 418 then
                        (if n < 417 then
                          1193
                        else
                          792)
                      else
                        (if n < 419 then
                          1254
                        else
                          127))
                    else
                      (if n < 422 then
                        (if n < 421 then
                          354
                        else
                          873)
                      else
                        (if n < 423 then
                          719
                        else
                          1241)))
                  else
                    (if n < 428 then
                      (if n < 426 then
                        (if n < 425 then
                          465
                        else
                          1135)
                      else
                        (if n < 427 then
                          689
                        else
                          1244))
                    else
                      (if n < 430 then
                        (if n < 429 then
                          612
                        else
                          786)
                      else
                        (if n < 431 then
                          615
                        else
                          744))))
                else
                  (if n < 440 then
                    (if n < 436 then
                      (if n < 434 then
                        1288
                      else
                        (if n < 435 then
                          814
                        else
                          1257))
                    else
                      (if n < 438 then
                        1288
                      else
                        (if n < 439 then
                          713
                        else
                          259)))
                  else
                    (if n < 444 then
                      (if n < 442 then
                        (if n < 441 then
                          1233
                        else
                          597)
                      else
                        1288)
                    else
                      (if n < 446 then
                        (if n < 445 then
                          141
                        else
                          1189)
                      else
                        1288)))))
            else
              (if n < 480 then
                (if n < 464 then
                  (if n < 456 then
                    (if n < 452 then
                      (if n < 450 then
                        (if n < 449 then
                          1288
                        else
                          753)
                      else
                        (if n < 451 then
                          1288
                        else
                          140))
                    else
                      (if n < 454 then
                        (if n < 453 then
                          1288
                        else
                          1143)
                      else
                        (if n < 455 then
                          1288
                        else
                          805)))
                  else
                    (if n < 460 then
                      (if n < 458 then
                        (if n < 457 then
                          760
                        else
                          1288)
                      else
                        (if n < 459 then
                          142
                        else
                          1288))
                    else
                      (if n < 462 then
                        (if n < 461 then
                          395
                        else
                          1288)
                      else
                        (if n < 463 then
                          1180
                        else
                          1288))))
                else
                  (if n < 472 then
                    (if n < 468 then
                      (if n < 466 then
                        (if n < 465 then
                          751
                        else
                          616)
                      else
                        (if n < 467 then
                          736
                        else
                          1252))
                    else
                      (if n < 470 then
                        (if n < 469 then
                          1191
                        else
                          702)
                      else
                        (if n < 471 then
                          1065
                        else
                          101)))
                  else
                    (if n < 476 then
                      (if n < 474 then
                        (if n < 473 then
                          1118
                        else
                          996)
                      else
                        (if n < 475 then
                          1207
                        else
                          847))
                    else
                      (if n < 478 then
                        (if n < 477 then
                          316
                        else
                          643)
                      else
                        (if n < 479 then
                          135
                        else
                          1068)))))
              else
                (if n < 496 then
                  (if n < 488 then
                    (if n < 484 then
                      (if n < 482 then
                        1288
                      else
                        (if n < 483 then
                          801
                        else
                          754))
                    else
                      (if n < 486 then
                        (if n < 485 then
                          1109
                        else
                          761)
                      else
                        1288))
                  else
                    (if n < 492 then
                      (if n < 490 then
                        1288
                      else
                        (if n < 491 then
                          758
                        else
                          458))
                    else
                      (if n < 494 then
                        (if n < 493 then
                          752
                        else
                          998)
                      else
                        1288)))
                else
                  (if n < 504 then
                    (if n < 500 then
                      (if n < 498 then
                        (if n < 497 then
                          1155
                        else
                          136)
                      else
                        (if n < 499 then
                          106
                        else
                          1048))
                    else
                      (if n < 502 then
                        (if n < 501 then
                          701
                        else
                          1050)
                      else
                        (if n < 503 then
                          595
                        else
                          1258)))
                  else
                    (if n < 508 then
                      (if n < 506 then
                        (if n < 505 then
                          522
                        else
                          1284)
                      else
                        (if n < 507 then
                          1057
                        else
                          593))
                    else
                      (if n < 510 then
                        (if n < 509 then
                          1075
                        else
                          128)
                      else
                        (if n < 511 then
                          1251
                        else
                          311)))))))))
      else
        (if n < 768 then
          (if n < 640 then
            (if n < 576 then
              (if n < 544 then
                (if n < 528 then
                  (if n < 520 then
                    (if n < 516 then
                      (if n < 514 then
                        (if n < 513 then
                          1288
                        else
                          18)
                      else
                        (if n < 515 then
                          1288
                        else
                          832))
                    else
                      (if n < 518 then
                        (if n < 517 then
                          1288
                        else
                          995)
                      else
                        (if n < 519 then
                          1288
                        else
                          952)))
                  else
                    (if n < 524 then
                      (if n < 522 then
                        (if n < 521 then
                          1288
                        else
                          960)
                      else
                        (if n < 523 then
                          1288
                        else
                          803))
                    else
                      (if n < 526 then
                        (if n < 525 then
                          1288
                        else
                          409)
                      else
                        (if n < 527 then
                          1288
                        else
                          860))))
                else
                  (if n < 536 then
                    (if n < 532 then
                      1288
                    else
                      (if n < 534 then
                        (if n < 533 then
                          785
                        else
                          262)
                      else
                        (if n < 535 then
                          1264
                        else
                          822)))
                  else
                    (if n < 540 then
                      1288
                    else
                      (if n < 542 then
                        (if n < 541 then
                          781
                        else
                          982)
                      else
                        (if n < 543 then
                          55
                        else
                          959)))))
              else
                (if n < 560 then
                  (if n < 552 then
                    (if n < 548 then
                      (if n < 546 then
                        1288
                      else
                        (if n < 547 then
                          153
                        else
                          900))
                    else
                      (if n < 550 then
                        1288
                      else
                        (if n < 551 then
                          936
                        else
                          769)))
                  else
                    (if n < 556 then
                      (if n < 554 then
                        1288
                      else
                        (if n < 555 then
                          897
                        else
                          232))
                    else
                      (if n < 558 then
                        1288
                      else
                        (if n < 559 then
                          231
                        else
                          899))))
                else
                  (if n < 568 then
                    1288
                  else
                    (if n < 572 then
                      (if n < 570 then
                        (if n < 569 then
                          335
                        else
                          1001)
                      else
                        (if n < 571 then
                          328
                        else
                          1023))
                    else
                      (if n < 574 then
                        (if n < 573 then
                          1281
                        else
                          167)
                      else
                        (if n < 575 then
                          410
                        else
                          270))))))
            else
              (if n < 608 then
                (if n < 592 then
                  (if n < 584 then
                    (if n < 580 then
                      (if n < 578 then
                        (if n < 577 then
                          1288
                        else
                          1282)
                      else
                        (if n < 579 then
                          1288
                        else
                          1245))
                    else
                      (if n < 582 then
                        (if n < 581 then
                          1288
                        else
                          424)
                      else
                        (if n < 583 then
                          1288
                        else
                          351)))
                  else
                    (if n < 588 then
                      (if n < 586 then
                        (if n < 585 then
                          901
                        else
                          1288)
                      else
                        (if n < 587 then
                          234
                        else
                          1288))
                    else
                      (if n < 590 then
                        (if n < 589 then
                          151
                        else
                          1288)
                      else
                        (if n < 591 then
                          745
                        else
                          1288))))
                else
                  (if n < 600 then
                    (if n < 596 then
                      (if n < 594 then
                        (if n < 593 then
                          210
                        else
                          198)
                      else
                        (if n < 595 then
                          810
                        else
                          154))
                    else
                      (if n < 598 then
                        (if n < 597 then
                          802
                        else
                          183)
                      else
                        (if n < 599 then
                          212
                        else
                          1018)))
                  else
                    (if n < 604 then
                      (if n < 602 then
                        (if n < 601 then
                          256
                        else
                          875)
                      else
                        (if n < 603 then
                          355
                        else
                          870))
                    else
                      (if n < 606 then
                        (if n < 605 then
                          651
                        else
                          181)
                      else
                        (if n < 607 then
                          440
                        else
                          156)))))
              else
                (if n < 624 then
                  (if n < 616 then
                    (if n < 612 then
                      (if n < 610 then
                        (if n < 609 then
                          925
                        else
                          163)
                      else
                        (if n < 611 then
                          649
                        else
                          30))
                    else
                      (if n < 614 then
                        (if n < 613 then
                          979
                        else
                          854)
                      else
                        (if n < 615 then
                          199
                        else
                          974)))
                  else
                    (if n < 620 then
                      (if n < 618 then
                        (if n < 617 then
                          864
                        else
                          917)
                      else
                        (if n < 619 then
                          20
                        else
                          990))
                    else
                      (if n < 622 then
                        (if n < 621 then
                          652
                        else
                          188)
                      else
                        (if n < 623 then
                          850
                        else
                          16))))
                else
                  (if n < 632 then
                    (if n < 628 then
                      (if n < 626 then
                        1288
                      else
                        (if n < 627 then
                          782
                        else
                          922))
                    else
                      (if n < 630 then
                        (if n < 629 then
                          203
                        else
                          26)
                      else
                        1288))
                  else
                    (if n < 636 then
                      (if n < 634 then
                        1288
                      else
                        (if n < 635 then
                          1173
                        else
                          999))
                    else
                      (if n < 638 then
                        (if n < 637 then
                          92
                        else
                          1144)
                      else
                        1288))))))
          else
            (if n < 704 then
              (if n < 672 then
                (if n < 656 then
                  (if n < 648 then
                    (if n < 644 then
                      (if n < 642 then
                        (if n < 641 then
                          1288
                        else
                          650)
                      else
                        (if n < 643 then
                          954
                        else
                          1288))
                    else
                      (if n < 646 then
                        (if n < 645 then
                          1288
                        else
                          233)
                      else
                        (if n < 647 then
                          656
                        else
                          1288)))
                  else
                    (if n < 652 then
                      (if n < 650 then
                        (if n < 649 then
                          1288
                        else
                          566)
                      else
                        (if n < 651 then
                          780
                        else
                          1288))
                    else
                      (if n < 654 then
                        (if n < 653 then
                          1288
                        else
                          865)
                      else
                        (if n < 655 then
                          833
                        else
                          1288))))
                else
                  (if n < 664 then
                    (if n < 660 then
                      (if n < 658 then
                        (if n < 657 then
                          869
                        else
                          155)
                      else
                        (if n < 659 then
                          791
                        else
                          172))
                    else
                      (if n < 662 then
                        (if n < 661 then
                          414
                        else
                          258)
                      else
                        (if n < 663 then
                          182
                        else
                          1267)))
                  else
                    (if n < 668 then
                      (if n < 666 then
                        (if n < 665 then
                          783
                        else
                          851)
                      else
                        (if n < 667 then
                          469
                        else
                          862))
                    else
                      (if n < 670 then
                        (if n < 669 then
                          208
                        else
                          381)
                      else
                        (if n < 671 then
                          919
                        else
                          145)))))
              else
                (if n < 688 then
                  (if n < 680 then
                    (if n < 676 then
                      1288
                    else
                      (if n < 678 then
                        (if n < 677 then
                          187
                        else
                          958)
                      else
                        (if n < 679 then
                          243
                        else
                          1021)))
                  else
                    (if n < 684 then
                      (if n < 682 then
                        (if n < 681 then
                          166
                        else
                          235)
                      else
                        (if n < 683 then
                          567
                        else
                          282))
                    else
                      1288))
                else
                  (if n < 696 then
                    (if n < 692 then
                      (if n < 690 then
                        (if n < 689 then
                          380
                        else
                          880)
                      else
                        (if n < 691 then
                          268
                        else
                          1269))
                    else
                      (if n < 694 then
                        (if n < 693 then
                          205
                        else
                          28)
                      else
                        (if n < 695 then
                          488
                        else
                          21)))
                  else
                    (if n < 700 then
                      (if n < 698 then
                        (if n < 697 then
                          524
                        else
                          257)
                      else
                        (if n < 699 then
                          246
                        else
                          190))
                    else
                      (if n < 702 then
                        (if n < 701 then
                          1
                        else
                          836)
                      else
                        (if n < 703 then
                          244
                        else
                          793))))))
            else
              (if n < 736 then
                (if n < 720 then
                  (if n < 712 then
                    (if n < 708 then
                      (if n < 706 then
                        (if n < 705 then
                          1288
                        else
                          821)
                      else
                        (if n < 707 then
                          1288
                        else
                          839))
                    else
                      (if n < 710 then
                        (if n < 709 then
                          820
                        else
                          1288)
                      else
                        (if n < 711 then
                          509
                        else
                          1288)))
                  else
                    (if n < 716 then
                      (if n < 714 then
                        (if n < 713 then
                          1288
                        else
                          955)
                      else
                        (if n < 715 then
                          1288
                        else
                          957))
                    else
                      (if n < 718 then
                        (if n < 717 then
                          914
                        else
                          1288)
                      else
                        (if n < 719 then
                          1020
                        else
                          1288))))
                else
                  (if n < 728 then
                    (if n < 724 then
                      (if n < 722 then
                        1288
                      else
                        (if n < 723 then
                          278
                        else
                          961))
                    else
                      (if n < 726 then
                        1288
                      else
                        (if n < 727 then
                          1234
                        else
                          848)))
                  else
                    (if n < 732 then
                      (if n < 730 then
                        (if n < 729 then
                          727
                        else
                          784)
                      else
                        1288)
                    else
                      (if n < 734 then
                        (if n < 733 then
                          788
                        else
                          1270)
                      else
                        1288))))
              else
                (if n < 752 then
                  (if n < 744 then
                    (if n < 740 then
                      (if n < 738 then
                        (if n < 737 then
                          536
                        else
                          898)
                      else
                        (if n < 739 then
                          565
                        else
                          657))
                    else
                      (if n < 742 then
                        (if n < 741 then
                          1008
                        else
                          195)
                      else
                        (if n < 743 then
                          976
                        else
                          197)))
                  else
                    (if n < 748 then
                      (if n < 746 then
                        (if n < 745 then
                          209
                        else
                          196)
                      else
                        (if n < 747 then
                          23
                        else
                          589))
                    else
                      (if n < 750 then
                        (if n < 749 then
                          653
                        else
                          191)
                      else
                        (if n < 751 then
                          499
                        else
                          929))))
                else
                  (if n < 760 then
                    (if n < 756 then
                      (if n < 754 then
                        (if n < 753 then
                          641
                        else
                          276)
                      else
                        (if n < 755 then
                          924
                        else
                          539))
                    else
                      (if n < 758 then
                        (if n < 757 then
                          189
                        else
                          211)
                      else
                        (if n < 759 then
                          245
                        else
                          1042)))
                  else
                    (if n < 764 then
                      (if n < 762 then
                        (if n < 761 then
                          789
                        else
                          975)
                      else
                        (if n < 763 then
                          22
                        else
                          876))
                    else
                      (if n < 766 then
                        (if n < 765 then
                          113
                        else
                          254)
                      else
                        (if n < 767 then
                          871
                        else
                          767))))))))
        else
          (if n < 896 then
            (if n < 832 then
              (if n < 800 then
                (if n < 784 then
                  (if n < 776 then
                    (if n < 772 then
                      (if n < 770 then
                        (if n < 769 then
                          1288
                        else
                          918)
                      else
                        (if n < 771 then
                          1288
                        else
                          201))
                    else
                      (if n < 774 then
                        (if n < 773 then
                          1288
                        else
                          855)
                      else
                        (if n < 775 then
                          1288
                        else
                          168)))
                  else
                    (if n < 780 then
                      (if n < 778 then
                        (if n < 777 then
                          1288
                        else
                          221)
                      else
                        (if n < 779 then
                          1288
                        else
                          353))
                    else
                      (if n < 782 then
                        (if n < 781 then
                          1288
                        else
                          824)
                      else
                        (if n < 783 then
                          1288
                        else
                          905))))
                else
                  (if n < 792 then
                    1288
                  else
                    (if n < 796 then
                      (if n < 794 then
                        (if n < 793 then
                          779
                        else
                          934)
                      else
                        (if n < 795 then
                          85
                        else
                          289))
                    else
                      (if n < 798 then
                        (if n < 797 then
                          608
                        else
                          472)
                      else
                        (if n < 799 then
                          604
                        else
                          778)))))
              else
                (if n < 816 then
                  (if n < 808 then
                    (if n < 804 then
                      1288
                    else
                      (if n < 806 then
                        (if n < 805 then
                          150
                        else
                          542)
                      else
                        (if n < 807 then
                          220
                        else
                          1035)))
                  else
                    (if n < 812 then
                      1288
                    else
                      (if n < 814 then
                        (if n < 813 then
                          1152
                        else
                          407)
                      else
                        (if n < 815 then
                          1147
                        else
                          498))))
                else
                  (if n < 824 then
                    (if n < 820 then
                      (if n < 818 then
                        1288
                      else
                        (if n < 819 then
                          968
                        else
                          890))
                    else
                      (if n < 822 then
                        1288
                      else
                        (if n < 823 then
                          543
                        else
                          568)))
                  else
                    (if n < 828 then
                      (if n < 826 then
                        1288
                      else
                        (if n < 827 then
                          1230
                        else
                          329))
                    else
                      (if n < 830 then
                        1288
                      else
                        (if n < 831 then
                          1119
                        else
                          603))))))
            else
              (if n < 864 then
                (if n < 848 then
                  (if n < 840 then
                    (if n < 836 then
                      (if n < 834 then
                        (if n < 833 then
                          1288
                        else
                          222)
                      else
                        (if n < 835 then
                          1288
                        else
                          1116))
                    else
                      (if n < 838 then
                        (if n < 837 then
                          541
                        else
                          1288)
                      else
                        (if n < 839 then
                          989
                        else
                          1288)))
                  else
                    (if n < 844 then
                      (if n < 842 then
                        (if n < 841 then
                          1288
                        else
                          1073)
                      else
                        (if n < 843 then
                          1288
                        else
                          966))
                    else
                      (if n < 846 then
                        (if n < 845 then
                          1034
                        else
                          1288)
                      else
                        (if n < 847 then
                          889
                        else
                          1288))))
                else
                  (if n < 856 then
                    (if n < 852 then
                      (if n < 850 then
                        (if n < 849 then
                          945
                        else
                          344)
                      else
                        (if n < 851 then
                          269
                        else
                          887))
                    else
                      (if n < 854 then
                        (if n < 853 then
                          1102
                        else
                          350)
                      else
                        (if n < 855 then
                          1032
                        else
                          185)))
                  else
                    (if n < 860 then
                      (if n < 858 then
                        (if n < 857 then
                          962
                        else
                          544)
                      else
                        (if n < 859 then
                          605
                        else
                          768))
                    else
                      (if n < 862 then
                        (if n < 861 then
                          581
                        else
                          939)
                      else
                        (if n < 863 then
                          575
                        else
                          1004)))))
              else
                (if n < 880 then
                  (if n < 872 then
                    (if n < 868 then
                      (if n < 866 then
                        1288
                      else
                        (if n < 867 then
                          935
                        else
                          1202))
                    else
                      (if n < 870 then
                        1288
                      else
                        (if n < 871 then
                          1195
                        else
                          238)))
                  else
                    (if n < 876 then
                      (if n < 874 then
                        (if n < 873 then
                          660
                        else
                          596)
                      else
                        1288)
                    else
                      (if n < 878 then
                        (if n < 877 then
                          584
                        else
                          224)
                      else
                        1288)))
                else
                  (if n < 888 then
                    (if n < 884 then
                      (if n < 882 then
                        (if n < 881 then
                          607
                        else
                          573)
                      else
                        (if n < 883 then
                          659
                        else
                          692))
                    else
                      (if n < 886 then
                        (if n < 885 then
                          548
                        else
                          1247)
                      else
                        (if n < 887 then
                          546
                        else
                          1263)))
                  else
                    (if n < 892 then
                      (if n < 890 then
                        (if n < 889 then
                          809
                        else
                          1137)
                      else
                        (if n < 891 then
                          252
                        else
                          835))
                    else
                      (if n < 894 then
                        (if n < 893 then
                          1103
                        else
                          703)
                      else
                        (if n < 895 then
                          1285
                        else
                          267)))))))
          else
            (if n < 960 then
              (if n < 928 then
                (if n < 912 then
                  (if n < 904 then
                    (if n < 900 then
                      (if n < 898 then
                        (if n < 897 then
                          1288
                        else
                          367)
                      else
                        (if n < 899 then
                          1288
                        else
                          177))
                    else
                      (if n < 902 then
                        (if n < 901 then
                          1288
                        else
                          893)
                      else
                        (if n < 903 then
                          1288
                        else
                          978)))
                  else
                    (if n < 908 then
                      (if n < 906 then
                        (if n < 905 then
                          790
                        else
                          1288)
                      else
                        (if n < 907 then
                          823
                        else
                          1288))
                    else
                      (if n < 910 then
                        (if n < 909 then
                          1059
                        else
                          1288)
                      else
                        (if n < 911 then
                          1286
                        else
                          1288))))
                else
                  (if n < 920 then
                    (if n < 916 then
                      (if n < 914 then
                        1288
                      else
                        (if n < 915 then
                          1089
                        else
                          837))
                    else
                      (if n < 918 then
                        (if n < 917 then
                          1229
                        else
                          356)
                      else
                        1288))
                  else
                    (if n < 924 then
                      (if n < 922 then
                        1288
                      else
                        (if n < 923 then
                          941
                        else
                          247))
                    else
                      (if n < 926 then
                        (if n < 925 then
                          564
                        else
                          943)
                      else
                        1288))))
              else
                (if n < 944 then
                  (if n < 936 then
                    (if n < 932 then
                      (if n < 930 then
                        (if n < 929 then
                          518
                        else
                          1236)
                      else
                        (if n < 931 then
                          798
                        else
                          956))
                    else
                      (if n < 934 then
                        (if n < 933 then
                          1104
                        else
                          240)
                      else
                        (if n < 935 then
                          866
                        else
                          425)))
                  else
                    (if n < 940 then
                      (if n < 938 then
                        (if n < 937 then
                          1231
                        else
                          217)
                      else
                        (if n < 939 then
                          940
                        else
                          1077))
                    else
                      (if n < 942 then
                        (if n < 941 then
                          239
                        else
                          1248)
                      else
                        (if n < 943 then
                          946
                        else
                          984))))
                else
                  (if n < 952 then
                    (if n < 948 then
                      (if n < 946 then
                        (if n < 945 then
                          1026
                        else
                          819)
                      else
                        (if n < 947 then
                          1210
                        else
                          787))
                    else
                      (if n < 950 then
                        (if n < 949 then
                          812
                        else
                          1115)
                      else
                        (if n < 951 then
                          826
                        else
                          654)))
                  else
                    (if n < 956 then
                      (if n < 954 then
                        (if n < 953 then
                          877
                        else
                          726)
                      else
                        (if n < 955 then
                          27
                        else
                          606))
                    else
                      (if n < 958 then
                        (if n < 957 then
                          969
                        else
                          571)
                      else
                        (if n < 959 then
                          938
                        else
                          863))))))
            else
              (if n < 992 then
                (if n < 976 then
                  (if n < 968 then
                    (if n < 964 then
                      (if n < 962 then
                        (if n < 961 then
                          1288
                        else
                          1126)
                      else
                        (if n < 963 then
                          977
                        else
                          1288))
                    else
                      (if n < 966 then
                        (if n < 965 then
                          1288
                        else
                          838)
                      else
                        (if n < 967 then
                          1017
                        else
                          1288)))
                  else
                    (if n < 972 then
                      (if n < 970 then
                        (if n < 969 then
                          1288
                        else
                          972)
                      else
                        (if n < 971 then
                          1111
                        else
                          1288))
                    else
                      (if n < 974 then
                        (if n < 973 then
                          1288
                        else
                          942)
                      else
                        (if n < 975 then
                          725
                        else
                          1288))))
                else
                  (if n < 984 then
                    (if n < 980 then
                      (if n < 978 then
                        (if n < 977 then
                          1223
                        else
                          94)
                      else
                        (if n < 979 then
                          572
                        else
                          690))
                    else
                      (if n < 982 then
                        (if n < 981 then
                          170
                        else
                          841)
                      else
                        (if n < 983 then
                          371
                        else
                          284)))
                  else
                    (if n < 988 then
                      (if n < 986 then
                        (if n < 985 then
                          827
                        else
                          971)
                      else
                        (if n < 987 then
                          178
                        else
                          635))
                    else
                      (if n < 990 then
                        (if n < 989 then
                          1283
                        else
                          219)
                      else
                        (if n < 991 then
                          933
                        else
                          970)))))
              else
                (if n < 1008 then
                  (if n < 1000 then
                    (if n < 996 then
                      (if n < 994 then
                        (if n < 993 then
                          891
                        else
                          947)
                      else
                        (if n < 995 then
                          1127
                        else
                          192))
                    else
                      (if n < 998 then
                        (if n < 997 then
                          236
                        else
                          489)
                      else
                        (if n < 999 then
                          241
                        else
                          1025)))
                  else
                    (if n < 1004 then
                      (if n < 1002 then
                        (if n < 1001 then
                          164
                        else
                          973)
                      else
                        (if n < 1003 then
                          503
                        else
                          981))
                    else
                      (if n < 1006 then
                        (if n < 1005 then
                          104
                        else
                          693)
                      else
                        (if n < 1007 then
                          1070
                        else
                          859))))
                else
                  (if n < 1016 then
                    (if n < 1012 then
                      1288
                    else
                      (if n < 1014 then
                        (if n < 1013 then
                          672
                        else
                          1117)
                      else
                        (if n < 1015 then
                          1201
                        else
                          24)))
                  else
                    (if n < 1020 then
                      (if n < 1018 then
                        (if n < 1017 then
                          655
                        else
                          454)
                      else
                        (if n < 1019 then
                          1033
                        else
                          223))
                    else
                      1288))))))))
    else
      (if n < 1536 then
        (if n < 1280 then
          (if n < 1152 then
            (if n < 1088 then
              (if n < 1056 then
                (if n < 1040 then
                  (if n < 1032 then
                    (if n < 1028 then
                      (if n < 1026 then
                        1288
                      else
                        (if n < 1027 then
                          1288
                        else
                          1274))
                    else
                      (if n < 1030 then
                        (if n < 1029 then
                          1288
                        else
                          818)
                      else
                        (if n < 1031 then
                          290
                        else
                          825)))
                  else
                    (if n < 1036 then
                      (if n < 1034 then
                        (if n < 1033 then
                          1288
                        else
                          858)
                      else
                        (if n < 1035 then
                          204
                        else
                          777))
                    else
                      (if n < 1038 then
                        (if n < 1037 then
                          861
                        else
                          1268)
                      else
                        (if n < 1039 then
                          1130
                        else
                          1288))))
                else
                  (if n < 1048 then
                    (if n < 1044 then
                      (if n < 1042 then
                        (if n < 1041 then
                          1288
                        else
                          707)
                      else
                        (if n < 1043 then
                          620
                        else
                          1011))
                    else
                      (if n < 1046 then
                        (if n < 1045 then
                          71
                        else
                          927)
                      else
                        (if n < 1047 then
                          73
                        else
                          1288)))
                  else
                    (if n < 1052 then
                      (if n < 1050 then
                        (if n < 1049 then
                          237
                        else
                          506)
                      else
                        (if n < 1051 then
                          569
                        else
                          1288))
                    else
                      (if n < 1054 then
                        (if n < 1053 then
                          1038
                        else
                          1288)
                      else
                        1288))))
              else
                (if n < 1072 then
                  (if n < 1064 then
                    (if n < 1060 then
                      (if n < 1058 then
                        (if n < 1057 then
                          1288
                        else
                          496)
                      else
                        (if n < 1059 then
                          896
                        else
                          275))
                    else
                      (if n < 1062 then
                        (if n < 1061 then
                          964
                        else
                          664)
                      else
                        (if n < 1063 then
                          1051
                        else
                          1288)))
                  else
                    (if n < 1068 then
                      (if n < 1066 then
                        (if n < 1065 then
                          464
                        else
                          1120)
                      else
                        (if n < 1067 then
                          1129
                        else
                          1288))
                    else
                      (if n < 1070 then
                        (if n < 1069 then
                          1167
                        else
                          1288)
                      else
                        1288)))
                else
                  (if n < 1080 then
                    (if n < 1076 then
                      (if n < 1074 then
                        (if n < 1073 then
                          1288
                        else
                          1166)
                      else
                        (if n < 1075 then
                          965
                        else
                          115))
                    else
                      (if n < 1078 then
                        (if n < 1077 then
                          895
                        else
                          840)
                      else
                        (if n < 1079 then
                          1235
                        else
                          1288)))
                  else
                    (if n < 1084 then
                      (if n < 1082 then
                        (if n < 1081 then
                          202
                        else
                          600)
                      else
                        (if n < 1083 then
                          663
                        else
                          1288))
                    else
                      (if n < 1086 then
                        (if n < 1085 then
                          507
                        else
                          1288)
                      else
                        1288)))))
            else
              (if n < 1120 then
                (if n < 1104 then
                  (if n < 1096 then
                    (if n < 1092 then
                      (if n < 1090 then
                        1288
                      else
                        (if n < 1091 then
                          1276
                        else
                          1288))
                    else
                      (if n < 1094 then
                        (if n < 1093 then
                          377
                        else
                          1288)
                      else
                        (if n < 1095 then
                          843
                        else
                          992)))
                  else
                    (if n < 1100 then
                      (if n < 1098 then
                        (if n < 1097 then
                          324
                        else
                          1288)
                      else
                        (if n < 1099 then
                          169
                        else
                          1037))
                    else
                      (if n < 1102 then
                        (if n < 1101 then
                          1272
                        else
                          766)
                      else
                        (if n < 1103 then
                          1288
                        else
                          991))))
                else
                  (if n < 1112 then
                    (if n < 1108 then
                      (if n < 1106 then
                        (if n < 1105 then
                          1288
                        else
                          696)
                      else
                        1288)
                    else
                      (if n < 1110 then
                        (if n < 1109 then
                          645
                        else
                          218)
                      else
                        (if n < 1111 then
                          1288
                        else
                          694)))
                  else
                    (if n < 1116 then
                      (if n < 1114 then
                        (if n < 1113 then
                          523
                        else
                          494)
                      else
                        (if n < 1115 then
                          1288
                        else
                          811))
                    else
                      (if n < 1118 then
                        (if n < 1117 then
                          1013
                        else
                          1288)
                      else
                        (if n < 1119 then
                          756
                        else
                          937)))))
              else
                (if n < 1136 then
                  (if n < 1128 then
                    (if n < 1124 then
                      (if n < 1122 then
                        (if n < 1121 then
                          1288
                        else
                          1287)
                      else
                        (if n < 1123 then
                          948
                        else
                          915))
                    else
                      (if n < 1126 then
                        1288
                      else
                        (if n < 1127 then
                          1288
                        else
                          842)))
                  else
                    (if n < 1132 then
                      (if n < 1130 then
                        (if n < 1129 then
                          892
                        else
                          553)
                      else
                        (if n < 1131 then
                          1255
                        else
                          1288))
                    else
                      (if n < 1134 then
                        (if n < 1133 then
                          1288
                        else
                          1219)
                      else
                        (if n < 1135 then
                          576
                        else
                          661))))
                else
                  (if n < 1144 then
                    (if n < 1140 then
                      (if n < 1138 then
                        (if n < 1137 then
                          1288
                        else
                          759)
                      else
                        (if n < 1139 then
                          932
                        else
                          796))
                    else
                      (if n < 1142 then
                        (if n < 1141 then
                          514
                        else
                          684)
                      else
                        (if n < 1143 then
                          1012
                        else
                          1288)))
                  else
                    (if n < 1148 then
                      (if n < 1146 then
                        1288
                      else
                        (if n < 1147 then
                          1288
                        else
                          1271))
                    else
                      (if n < 1150 then
                        (if n < 1149 then
                          1288
                        else
                          1078)
                      else
                        (if n < 1151 then
                          648
                        else
                          579)))))))
          else
            (if n < 1216 then
              (if n < 1184 then
                (if n < 1168 then
                  (if n < 1160 then
                    (if n < 1156 then
                      (if n < 1154 then
                        1288
                      else
                        (if n < 1155 then
                          1084
                        else
                          1288))
                    else
                      (if n < 1158 then
                        (if n < 1157 then
                          1209
                        else
                          1288)
                      else
                        (if n < 1159 then
                          741
                        else
                          903)))
                  else
                    (if n < 1164 then
                      (if n < 1162 then
                        (if n < 1161 then
                          749
                        else
                          1288)
                      else
                        (if n < 1163 then
                          179
                        else
                          1041))
                    else
                      (if n < 1166 then
                        (if n < 1165 then
                          867
                        else
                          318)
                      else
                        (if n < 1167 then
                          1288
                        else
                          771))))
                else
                  (if n < 1176 then
                    (if n < 1172 then
                      (if n < 1170 then
                        (if n < 1169 then
                          1288
                        else
                          1156)
                      else
                        (if n < 1171 then
                          1174
                        else
                          1232))
                    else
                      (if n < 1174 then
                        (if n < 1173 then
                          671
                        else
                          229)
                      else
                        (if n < 1175 then
                          1214
                        else
                          1288)))
                  else
                    (if n < 1180 then
                      (if n < 1178 then
                        1288
                      else
                        (if n < 1179 then
                          1288
                        else
                          1080))
                    else
                      (if n < 1182 then
                        (if n < 1181 then
                          1288
                        else
                          1273)
                      else
                        (if n < 1183 then
                          967
                        else
                          1243)))))
              else
                (if n < 1200 then
                  (if n < 1192 then
                    (if n < 1188 then
                      (if n < 1186 then
                        (if n < 1185 then
                          1288
                        else
                          904)
                      else
                        1288)
                    else
                      (if n < 1190 then
                        (if n < 1189 then
                          1260
                        else
                          510)
                      else
                        (if n < 1191 then
                          1288
                        else
                          1221)))
                  else
                    (if n < 1196 then
                      (if n < 1194 then
                        (if n < 1193 then
                          1222
                        else
                          504)
                      else
                        (if n < 1195 then
                          1288
                        else
                          857))
                    else
                      (if n < 1198 then
                        (if n < 1197 then
                          691
                        else
                          1288)
                      else
                        (if n < 1199 then
                          879
                        else
                          921))))
                else
                  (if n < 1208 then
                    (if n < 1204 then
                      (if n < 1202 then
                        (if n < 1201 then
                          1288
                        else
                          724)
                      else
                        (if n < 1203 then
                          1187
                        else
                          1216))
                    else
                      (if n < 1206 then
                        1288
                      else
                        (if n < 1207 then
                          1288
                        else
                          1265)))
                  else
                    (if n < 1212 then
                      (if n < 1210 then
                        (if n < 1209 then
                          502
                        else
                          882)
                      else
                        (if n < 1211 then
                          411
                        else
                          1288))
                    else
                      (if n < 1214 then
                        (if n < 1213 then
                          1288
                        else
                          738)
                      else
                        (if n < 1215 then
                          676
                        else
                          762))))))
            else
              (if n < 1248 then
                (if n < 1232 then
                  (if n < 1224 then
                    (if n < 1220 then
                      (if n < 1218 then
                        1288
                      else
                        (if n < 1219 then
                          420
                        else
                          1288))
                    else
                      (if n < 1222 then
                        (if n < 1221 then
                          894
                        else
                          1288)
                      else
                        (if n < 1223 then
                          846
                        else
                          774)))
                  else
                    (if n < 1228 then
                      (if n < 1226 then
                        (if n < 1225 then
                          1105
                        else
                          1288)
                      else
                        (if n < 1227 then
                          1217
                        else
                          881))
                    else
                      (if n < 1230 then
                        (if n < 1229 then
                          949
                        else
                          1190)
                      else
                        (if n < 1231 then
                          1288
                        else
                          662))))
                else
                  (if n < 1240 then
                    (if n < 1236 then
                      (if n < 1234 then
                        (if n < 1233 then
                          1288
                        else
                          535)
                      else
                        (if n < 1235 then
                          695
                        else
                          813))
                    else
                      (if n < 1238 then
                        1288
                      else
                        (if n < 1239 then
                          1288
                        else
                          902)))
                  else
                    (if n < 1244 then
                      (if n < 1242 then
                        (if n < 1241 then
                          215
                        else
                          1220)
                      else
                        (if n < 1243 then
                          1079
                        else
                          1288))
                    else
                      (if n < 1246 then
                        (if n < 1245 then
                          1288
                        else
                          1087)
                      else
                        (if n < 1247 then
                          441
                        else
                          844)))))
              else
                (if n < 1264 then
                  (if n < 1256 then
                    (if n < 1252 then
                      (if n < 1250 then
                        (if n < 1249 then
                          1288
                        else
                          124)
                      else
                        (if n < 1251 then
                          1218
                        else
                          800))
                    else
                      (if n < 1254 then
                        (if n < 1253 then
                          511
                        else
                          1266)
                      else
                        (if n < 1255 then
                          540
                        else
                          1288)))
                  else
                    (if n < 1260 then
                      (if n < 1258 then
                        1288
                      else
                        (if n < 1259 then
                          1288
                        else
                          1246))
                    else
                      (if n < 1262 then
                        (if n < 1261 then
                          1288
                        else
                          1188)
                      else
                        (if n < 1263 then
                          1215
                        else
                          849))))
                else
                  (if n < 1272 then
                    (if n < 1268 then
                      (if n < 1266 then
                        (if n < 1265 then
                          1288
                        else
                          1169)
                      else
                        1288)
                    else
                      (if n < 1270 then
                        (if n < 1269 then
                          1238
                        else
                          495)
                      else
                        (if n < 1271 then
                          1288
                        else
                          505)))
                  else
                    (if n < 1276 then
                      (if n < 1274 then
                        (if n < 1273 then
                          1136
                        else
                          950)
                      else
                        (if n < 1275 then
                          1288
                        else
                          953))
                    else
                      (if n < 1278 then
                        (if n < 1277 then
                          845
                        else
                          1288)
                      else
                        (if n < 1279 then
                          963
                        else
                          888))))))))
        else
          (if n < 1408 then
            (if n < 1344 then
              (if n < 1312 then
                (if n < 1296 then
                  (if n < 1288 then
                    (if n < 1284 then
                      (if n < 1282 then
                        (if n < 1281 then
                          609
                        else
                          1288)
                      else
                        (if n < 1283 then
                          923
                        else
                          157))
                    else
                      (if n < 1286 then
                        (if n < 1285 then
                          100
                        else
                          795)
                      else
                        (if n < 1287 then
                          1288
                        else
                          830)))
                  else
                    (if n < 1292 then
                      (if n < 1290 then
                        (if n < 1289 then
                          500
                        else
                          928)
                      else
                        (if n < 1291 then
                          1288
                        else
                          765))
                    else
                      (if n < 1294 then
                        (if n < 1293 then
                          1288
                        else
                          144)
                      else
                        1288)))
                else
                  (if n < 1304 then
                    (if n < 1300 then
                      (if n < 1298 then
                        (if n < 1297 then
                          358
                        else
                          1228)
                      else
                        (if n < 1299 then
                          1288
                        else
                          794))
                    else
                      (if n < 1302 then
                        (if n < 1301 then
                          683
                        else
                          1288)
                      else
                        (if n < 1303 then
                          906
                        else
                          216)))
                  else
                    (if n < 1308 then
                      (if n < 1306 then
                        (if n < 1305 then
                          591
                        else
                          1288)
                      else
                        (if n < 1307 then
                          699
                        else
                          173))
                    else
                      (if n < 1310 then
                        1288
                      else
                        (if n < 1311 then
                          249
                        else
                          1288)))))
              else
                (if n < 1328 then
                  (if n < 1320 then
                    (if n < 1316 then
                      (if n < 1314 then
                        (if n < 1313 then
                          797
                        else
                          538)
                      else
                        (if n < 1315 then
                          537
                        else
                          1288))
                    else
                      (if n < 1318 then
                        (if n < 1317 then
                          642
                        else
                          1288)
                      else
                        1288))
                  else
                    (if n < 1324 then
                      (if n < 1322 then
                        (if n < 1321 then
                          1288
                        else
                          697)
                      else
                        (if n < 1323 then
                          916
                        else
                          776))
                    else
                      (if n < 1326 then
                        (if n < 1325 then
                          125
                        else
                          1199)
                      else
                        (if n < 1327 then
                          152
                        else
                          1288))))
                else
                  (if n < 1336 then
                    (if n < 1332 then
                      (if n < 1330 then
                        (if n < 1329 then
                          1009
                        else
                          84)
                      else
                        (if n < 1331 then
                          868
                        else
                          1288))
                    else
                      (if n < 1334 then
                        (if n < 1333 then
                          1288
                        else
                          1031)
                      else
                        (if n < 1335 then
                          186
                        else
                          831)))
                  else
                    (if n < 1340 then
                      (if n < 1338 then
                        (if n < 1337 then
                          552
                        else
                          1288)
                      else
                        1288)
                    else
                      (if n < 1342 then
                        (if n < 1341 then
                          698
                        else
                          378)
                      else
                        (if n < 1343 then
                          980
                        else
                          1288))))))
            else
              (if n < 1376 then
                (if n < 1360 then
                  (if n < 1352 then
                    (if n < 1348 then
                      (if n < 1346 then
                        (if n < 1345 then
                          277
                        else
                          1288)
                      else
                        1288)
                    else
                      (if n < 1350 then
                        (if n < 1349 then
                          910
                        else
                          590)
                      else
                        (if n < 1351 then
                          250
                        else
                          1288)))
                  else
                    (if n < 1356 then
                      (if n < 1354 then
                        (if n < 1353 then
                          206
                        else
                          29)
                      else
                        (if n < 1355 then
                          285
                        else
                          1288))
                    else
                      (if n < 1358 then
                        (if n < 1357 then
                          1288
                        else
                          911)
                      else
                        (if n < 1359 then
                          271
                        else
                          834))))
                else
                  (if n < 1368 then
                    (if n < 1364 then
                      (if n < 1362 then
                        (if n < 1361 then
                          817
                        else
                          253)
                      else
                        (if n < 1363 then
                          987
                        else
                          1288))
                    else
                      (if n < 1366 then
                        (if n < 1365 then
                          1288
                        else
                          34)
                      else
                        (if n < 1367 then
                          829
                        else
                          1015)))
                  else
                    (if n < 1372 then
                      (if n < 1370 then
                        (if n < 1369 then
                          1288
                        else
                          993)
                      else
                        (if n < 1371 then
                          2
                        else
                          1006))
                    else
                      (if n < 1374 then
                        1288
                      else
                        (if n < 1375 then
                          1288
                        else
                          159)))))
              else
                (if n < 1392 then
                  (if n < 1384 then
                    (if n < 1380 then
                      (if n < 1378 then
                        1288
                      else
                        (if n < 1379 then
                          1288
                        else
                          17))
                    else
                      (if n < 1382 then
                        (if n < 1381 then
                          1288
                        else
                          1002)
                      else
                        (if n < 1383 then
                          317
                        else
                          1044)))
                  else
                    (if n < 1388 then
                      (if n < 1386 then
                        (if n < 1385 then
                          1288
                        else
                          994)
                      else
                        (if n < 1387 then
                          263
                        else
                          292))
                    else
                      (if n < 1390 then
                        (if n < 1389 then
                          1159
                        else
                          501)
                      else
                        (if n < 1391 then
                          483
                        else
                          1288))))
                else
                  (if n < 1400 then
                    (if n < 1396 then
                      (if n < 1394 then
                        1288
                      else
                        (if n < 1395 then
                          1288
                        else
                          658))
                    else
                      (if n < 1398 then
                        (if n < 1397 then
                          1288
                        else
                          549)
                      else
                        (if n < 1399 then
                          682
                        else
                          149)))
                  else
                    (if n < 1404 then
                      (if n < 1402 then
                        (if n < 1401 then
                          1288
                        else
                          147)
                      else
                        (if n < 1403 then
                          114
                        else
                          194))
                    else
                      (if n < 1406 then
                        (if n < 1405 then
                          255
                        else
                          452)
                      else
                        (if n < 1407 then
                          63
                        else
                          1288)))))))
          else
            (if n < 1472 then
              (if n < 1440 then
                (if n < 1424 then
                  (if n < 1416 then
                    (if n < 1412 then
                      (if n < 1410 then
                        (if n < 1409 then
                          764
                        else
                          1288)
                      else
                        (if n < 1411 then
                          451
                        else
                          251))
                    else
                      (if n < 1414 then
                        1288
                      else
                        (if n < 1415 then
                          396
                        else
                          1288)))
                  else
                    (if n < 1420 then
                      (if n < 1418 then
                        (if n < 1417 then
                          634
                        else
                          294)
                      else
                        (if n < 1419 then
                          1288
                        else
                          248))
                    else
                      (if n < 1422 then
                        (if n < 1421 then
                          143
                        else
                          1288)
                      else
                        (if n < 1423 then
                          772
                        else
                          908))))
                else
                  (if n < 1432 then
                    (if n < 1428 then
                      (if n < 1426 then
                        1288
                      else
                        (if n < 1427 then
                          1288
                        else
                          33))
                    else
                      (if n < 1430 then
                        (if n < 1429 then
                          1288
                        else
                          162)
                      else
                        (if n < 1431 then
                          146
                        else
                          1005)))
                  else
                    (if n < 1436 then
                      (if n < 1434 then
                        (if n < 1433 then
                          1288
                        else
                          360)
                      else
                        (if n < 1435 then
                          230
                        else
                          628))
                    else
                      (if n < 1438 then
                        (if n < 1437 then
                          288
                        else
                          815)
                      else
                        (if n < 1439 then
                          273
                        else
                          1288)))))
              else
                (if n < 1456 then
                  (if n < 1448 then
                    (if n < 1444 then
                      (if n < 1442 then
                        1288
                      else
                        (if n < 1443 then
                          1288
                        else
                          280))
                    else
                      (if n < 1446 then
                        (if n < 1445 then
                          1288
                        else
                          291)
                      else
                        (if n < 1447 then
                          46
                        else
                          874)))
                  else
                    (if n < 1452 then
                      (if n < 1450 then
                        (if n < 1449 then
                          1288
                        else
                          287)
                      else
                        (if n < 1451 then
                          19
                        else
                          1200))
                    else
                      (if n < 1454 then
                        (if n < 1453 then
                          1027
                        else
                          32)
                      else
                        (if n < 1455 then
                          453
                        else
                          1288))))
                else
                  (if n < 1464 then
                    (if n < 1460 then
                      (if n < 1458 then
                        (if n < 1457 then
                          161
                        else
                          988)
                      else
                        (if n < 1459 then
                          1288
                        else
                          985))
                    else
                      (if n < 1462 then
                        (if n < 1461 then
                          1043
                        else
                          1288)
                      else
                        (if n < 1463 then
                          35
                        else
                          31)))
                  else
                    (if n < 1468 then
                      (if n < 1466 then
                        (if n < 1465 then
                          1288
                        else
                          171)
                      else
                        1288)
                    else
                      (if n < 1470 then
                        (if n < 1469 then
                          763
                        else
                          1213)
                      else
                        (if n < 1471 then
                          1288
                        else
                          286))))))
            else
              (if n < 1504 then
                (if n < 1488 then
                  (if n < 1480 then
                    (if n < 1476 then
                      (if n < 1474 then
                        (if n < 1473 then
                          816
                        else
                          1288)
                      else
                        (if n < 1475 then
                          1028
                        else
                          160))
                    else
                      (if n < 1478 then
                        (if n < 1477 then
                          272
                        else
                          986)
                      else
                        (if n < 1479 then
                          1288
                        else
                          804)))
                  else
                    (if n < 1484 then
                      (if n < 1482 then
                        1288
                      else
                        (if n < 1483 then
                          359
                        else
                          1288))
                    else
                      (if n < 1486 then
                        (if n < 1485 then
                          1014
                        else
                          1288)
                      else
                        (if n < 1487 then
                          909
                        else
                          174))))
                else
                  (if n < 1496 then
                    (if n < 1492 then
                      (if n < 1490 then
                        1288
                      else
                        (if n < 1491 then
                          1288
                        else
                          207))
                    else
                      (if n < 1494 then
                        (if n < 1493 then
                          1288
                        else
                          570)
                      else
                        (if n < 1495 then
                          175
                        else
                          555)))
                  else
                    (if n < 1500 then
                      (if n < 1498 then
                        (if n < 1497 then
                          1288
                        else
                          775)
                      else
                        (if n < 1499 then
                          912
                        else
                          180))
                    else
                      (if n < 1502 then
                        (if n < 1501 then
                          148
                        else
                          646)
                      else
                        (if n < 1503 then
                          15
                        else
                          1288)))))
              else
                (if n < 1520 then
                  (if n < 1512 then
                    (if n < 1508 then
                      (if n < 1506 then
                        (if n < 1505 then
                          165
                        else
                          1010)
                      else
                        (if n < 1507 then
                          1288
                        else
                          799))
                    else
                      (if n < 1510 then
                        (if n < 1509 then
                          1288
                        else
                          260)
                      else
                        1288))
                  else
                    (if n < 1516 then
                      (if n < 1514 then
                        (if n < 1513 then
                          293
                        else
                          1288)
                      else
                        (if n < 1515 then
                          1024
                        else
                          357))
                    else
                      (if n < 1518 then
                        (if n < 1517 then
                          279
                        else
                          264)
                      else
                        (if n < 1519 then
                          1288
                        else
                          807))))
                else
                  (if n < 1528 then
                    (if n < 1524 then
                      (if n < 1522 then
                        1288
                      else
                        (if n < 1523 then
                          1288
                        else
                          274))
                    else
                      (if n < 1526 then
                        (if n < 1525 then
                          1288
                        else
                          281)
                      else
                        (if n < 1527 then
                          404
                        else
                          283)))
                  else
                    (if n < 1532 then
                      (if n < 1530 then
                        (if n < 1529 then
                          1288
                        else
                          808)
                      else
                        (if n < 1531 then
                          93
                        else
                          1030))
                    else
                      (if n < 1534 then
                        (if n < 1533 then
                          770
                        else
                          72)
                      else
                        (if n < 1535 then
                          806
                        else
                          1288)))))))))
      else
        (if n < 1792 then
          (if n < 1664 then
            (if n < 1600 then
              (if n < 1568 then
                (if n < 1552 then
                  (if n < 1544 then
                    (if n < 1540 then
                      (if n < 1538 then
                        (if n < 1537 then
                          444
                        else
                          1288)
                      else
                        (if n < 1539 then
                          920
                        else
                          433))
                    else
                      (if n < 1542 then
                        (if n < 1541 then
                          471
                        else
                          926)
                      else
                        (if n < 1543 then
                          1288
                        else
                          1204)))
                  else
                    (if n < 1548 then
                      (if n < 1546 then
                        (if n < 1545 then
                          387
                        else
                          1019)
                      else
                        (if n < 1547 then
                          1288
                        else
                          558))
                    else
                      (if n < 1550 then
                        (if n < 1549 then
                          1288
                        else
                          372)
                      else
                        1288)))
                else
                  (if n < 1560 then
                    (if n < 1556 then
                      (if n < 1554 then
                        (if n < 1553 then
                          585
                        else
                          1192)
                      else
                        (if n < 1555 then
                          58
                        else
                          1288))
                    else
                      (if n < 1558 then
                        (if n < 1557 then
                          1288
                        else
                          214)
                      else
                        (if n < 1559 then
                          1183
                        else
                          421)))
                  else
                    (if n < 1564 then
                      (if n < 1562 then
                        (if n < 1561 then
                          1101
                        else
                          1288)
                      else
                        1288)
                    else
                      (if n < 1566 then
                        (if n < 1565 then
                          930
                        else
                          611)
                      else
                        (if n < 1567 then
                          310
                        else
                          1288)))))
              else
                (if n < 1584 then
                  (if n < 1576 then
                    (if n < 1572 then
                      (if n < 1570 then
                        (if n < 1569 then
                          739
                        else
                          1171)
                      else
                        (if n < 1571 then
                          1288
                        else
                          1179))
                    else
                      (if n < 1574 then
                        (if n < 1573 then
                          1134
                        else
                          1288)
                      else
                        (if n < 1575 then
                          1277
                        else
                          298)))
                  else
                    (if n < 1580 then
                      (if n < 1578 then
                        (if n < 1577 then
                          1172
                        else
                          1288)
                      else
                        (if n < 1579 then
                          1176
                        else
                          457))
                    else
                      (if n < 1582 then
                        1288
                      else
                        (if n < 1583 then
                          951
                        else
                          1288))))
                else
                  (if n < 1592 then
                    (if n < 1588 then
                      (if n < 1586 then
                        (if n < 1585 then
                          1142
                        else
                          422)
                      else
                        (if n < 1587 then
                          1278
                        else
                          1288))
                    else
                      (if n < 1590 then
                        (if n < 1589 then
                          423
                        else
                          1288)
                      else
                        1288))
                  else
                    (if n < 1596 then
                      (if n < 1594 then
                        (if n < 1593 then
                          1288
                        else
                          931)
                      else
                        (if n < 1595 then
                          714
                        else
                          1170))
                    else
                      (if n < 1598 then
                        (if n < 1597 then
                          1157
                        else
                          547)
                      else
                        (if n < 1599 then
                          446
                        else
                          1288))))))
            else
              (if n < 1632 then
                (if n < 1616 then
                  (if n < 1608 then
                    (if n < 1604 then
                      (if n < 1602 then
                        (if n < 1601 then
                          582
                        else
                          1288)
                      else
                        (if n < 1603 then
                          428
                        else
                          1249))
                    else
                      (if n < 1606 then
                        (if n < 1605 then
                          1106
                        else
                          59)
                      else
                        (if n < 1607 then
                          1288
                        else
                          130)))
                  else
                    (if n < 1612 then
                      (if n < 1610 then
                        1288
                      else
                        (if n < 1611 then
                          484
                        else
                          1288))
                    else
                      (if n < 1614 then
                        (if n < 1613 then
                          13
                        else
                          1288)
                      else
                        (if n < 1615 then
                          60
                        else
                          1108))))
                else
                  (if n < 1624 then
                    (if n < 1620 then
                      (if n < 1618 then
                        1288
                      else
                        (if n < 1619 then
                          1288
                        else
                          265))
                    else
                      (if n < 1622 then
                        (if n < 1621 then
                          1288
                        else
                          852)
                      else
                        (if n < 1623 then
                          1047
                        else
                          853)))
                  else
                    (if n < 1628 then
                      (if n < 1626 then
                        (if n < 1625 then
                          1288
                        else
                          728)
                      else
                        (if n < 1627 then
                          427
                        else
                          1225))
                    else
                      (if n < 1630 then
                        (if n < 1629 then
                          447
                        else
                          721)
                      else
                        (if n < 1631 then
                          62
                        else
                          1288)))))
              else
                (if n < 1648 then
                  (if n < 1640 then
                    (if n < 1636 then
                      (if n < 1634 then
                        1288
                      else
                        (if n < 1635 then
                          1288
                        else
                          497))
                    else
                      (if n < 1638 then
                        (if n < 1637 then
                          1288
                        else
                          1163)
                      else
                        (if n < 1639 then
                          303
                        else
                          1259)))
                  else
                    (if n < 1644 then
                      (if n < 1642 then
                        (if n < 1641 then
                          1288
                        else
                          1099)
                      else
                        (if n < 1643 then
                          437
                        else
                          438))
                    else
                      (if n < 1646 then
                        (if n < 1645 then
                          913
                        else
                          449)
                      else
                        (if n < 1647 then
                          1124
                        else
                          1288))))
                else
                  (if n < 1656 then
                    (if n < 1652 then
                      (if n < 1650 then
                        (if n < 1649 then
                          137
                        else
                          1175)
                      else
                        (if n < 1651 then
                          1288
                        else
                          1003))
                    else
                      (if n < 1654 then
                        (if n < 1653 then
                          1288
                        else
                          363)
                      else
                        1288))
                  else
                    (if n < 1660 then
                      (if n < 1658 then
                        (if n < 1657 then
                          1053
                        else
                          1288)
                      else
                        (if n < 1659 then
                          429
                        else
                          416))
                    else
                      (if n < 1662 then
                        (if n < 1661 then
                          133
                        else
                          435)
                      else
                        (if n < 1663 then
                          1288
                        else
                          732)))))))
          else
            (if n < 1728 then
              (if n < 1696 then
                (if n < 1680 then
                  (if n < 1672 then
                    (if n < 1668 then
                      (if n < 1666 then
                        (if n < 1665 then
                          361
                        else
                          1288)
                      else
                        1288)
                    else
                      (if n < 1670 then
                        (if n < 1669 then
                          448
                        else
                          228)
                      else
                        (if n < 1671 then
                          1149
                        else
                          1288)))
                  else
                    (if n < 1676 then
                      (if n < 1674 then
                        (if n < 1673 then
                          1182
                        else
                          415)
                      else
                        (if n < 1675 then
                          134
                        else
                          1288))
                    else
                      (if n < 1678 then
                        (if n < 1677 then
                          1288
                        else
                          718)
                      else
                        (if n < 1679 then
                          436
                        else
                          1279))))
                else
                  (if n < 1688 then
                    (if n < 1684 then
                      (if n < 1682 then
                        1288
                      else
                        (if n < 1683 then
                          1288
                        else
                          47))
                    else
                      (if n < 1686 then
                        (if n < 1685 then
                          1288
                        else
                          302)
                      else
                        (if n < 1687 then
                          57
                        else
                          1186)))
                  else
                    (if n < 1692 then
                      (if n < 1690 then
                        (if n < 1689 then
                          1288
                        else
                          418)
                      else
                        (if n < 1691 then
                          36
                        else
                          1197))
                    else
                      (if n < 1694 then
                        (if n < 1693 then
                          1056
                        else
                          432)
                      else
                        (if n < 1695 then
                          1158
                        else
                          1288)))))
              else
                (if n < 1712 then
                  (if n < 1704 then
                    (if n < 1700 then
                      (if n < 1698 then
                        (if n < 1697 then
                          740
                        else
                          460)
                      else
                        (if n < 1699 then
                          1168
                        else
                          1288))
                    else
                      (if n < 1702 then
                        (if n < 1701 then
                          1288
                        else
                          462)
                      else
                        (if n < 1703 then
                          426
                        else
                          1162)))
                  else
                    (if n < 1708 then
                      (if n < 1706 then
                        (if n < 1705 then
                          1288
                        else
                          729)
                      else
                        (if n < 1707 then
                          64
                        else
                          1181))
                    else
                      (if n < 1710 then
                        1288
                      else
                        (if n < 1711 then
                          1288
                        else
                          383))))
                else
                  (if n < 1720 then
                    (if n < 1716 then
                      (if n < 1714 then
                        1288
                      else
                        (if n < 1715 then
                          1288
                        else
                          1112))
                    else
                      (if n < 1718 then
                        (if n < 1717 then
                          1288
                        else
                          242)
                      else
                        (if n < 1719 then
                          445
                        else
                          184)))
                  else
                    (if n < 1724 then
                      (if n < 1722 then
                        (if n < 1721 then
                          1288
                        else
                          132)
                      else
                        (if n < 1723 then
                          343
                        else
                          390))
                    else
                      (if n < 1726 then
                        (if n < 1725 then
                          362
                        else
                          1198)
                      else
                        (if n < 1727 then
                          450
                        else
                          1288))))))
            else
              (if n < 1760 then
                (if n < 1744 then
                  (if n < 1736 then
                    (if n < 1732 then
                      (if n < 1730 then
                        (if n < 1729 then
                          677
                        else
                          1288)
                      else
                        (if n < 1731 then
                          1054
                        else
                          334))
                    else
                      (if n < 1734 then
                        1288
                      else
                        (if n < 1735 then
                          300
                        else
                          1288)))
                  else
                    (if n < 1740 then
                      (if n < 1738 then
                        (if n < 1737 then
                          297
                        else
                          733)
                      else
                        (if n < 1739 then
                          1288
                        else
                          1000))
                    else
                      (if n < 1742 then
                        (if n < 1741 then
                          1165
                        else
                          1288)
                      else
                        (if n < 1743 then
                          1160
                        else
                          364))))
                else
                  (if n < 1752 then
                    (if n < 1748 then
                      (if n < 1746 then
                        (if n < 1745 then
                          1131
                        else
                          1206)
                      else
                        (if n < 1747 then
                          1288
                        else
                          1093))
                    else
                      (if n < 1750 then
                        (if n < 1749 then
                          627
                        else
                          1288)
                      else
                        (if n < 1751 then
                          463
                        else
                          261)))
                  else
                    (if n < 1756 then
                      (if n < 1754 then
                        (if n < 1753 then
                          1288
                        else
                          461)
                      else
                        1288)
                    else
                      (if n < 1758 then
                        (if n < 1757 then
                          1007
                        else
                          1185)
                      else
                        (if n < 1759 then
                          1288
                        else
                          1122)))))
              else
                (if n < 1776 then
                  (if n < 1768 then
                    (if n < 1764 then
                      (if n < 1762 then
                        1288
                      else
                        (if n < 1763 then
                          1288
                        else
                          723))
                    else
                      (if n < 1766 then
                        (if n < 1765 then
                          1288
                        else
                          434)
                      else
                        (if n < 1767 then
                          1100
                        else
                          131)))
                  else
                    (if n < 1772 then
                      (if n < 1770 then
                        (if n < 1769 then
                          1288
                        else
                          550)
                      else
                        (if n < 1771 then
                          1121
                        else
                          722))
                    else
                      (if n < 1774 then
                        (if n < 1773 then
                          717
                        else
                          856)
                      else
                        (if n < 1775 then
                          5
                        else
                          1288))))
                else
                  (if n < 1784 then
                    (if n < 1780 then
                      (if n < 1778 then
                        1288
                      else
                        (if n < 1779 then
                          1288
                        else
                          417))
                    else
                      (if n < 1782 then
                        (if n < 1781 then
                          1288
                        else
                          366)
                      else
                        (if n < 1783 then
                          301
                        else
                          1125)))
                  else
                    (if n < 1788 then
                      (if n < 1786 then
                        (if n < 1785 then
                          1288
                        else
                          1055)
                      else
                        (if n < 1787 then
                          365
                        else
                          720))
                    else
                      (if n < 1790 then
                        (if n < 1789 then
                          419
                        else
                          61)
                      else
                        (if n < 1791 then
                          668
                        else
                          1288))))))))
        else
          (if n < 1920 then
            (if n < 1856 then
              (if n < 1824 then
                (if n < 1808 then
                  (if n < 1800 then
                    (if n < 1796 then
                      (if n < 1794 then
                        (if n < 1793 then
                          405
                        else
                          1288)
                      else
                        (if n < 1795 then
                          473
                        else
                          678))
                    else
                      (if n < 1798 then
                        (if n < 1797 then
                          347
                        else
                          515)
                      else
                        (if n < 1799 then
                          1288
                        else
                          213)))
                  else
                    (if n < 1804 then
                      (if n < 1802 then
                        (if n < 1801 then
                          1110
                        else
                          374)
                      else
                        (if n < 1803 then
                          1288
                        else
                          226))
                    else
                      (if n < 1806 then
                        (if n < 1805 then
                          1288
                        else
                          439)
                      else
                        1288)))
                else
                  (if n < 1816 then
                    (if n < 1812 then
                      (if n < 1810 then
                        (if n < 1809 then
                          492
                        else
                          474)
                      else
                        (if n < 1811 then
                          470
                        else
                          1288))
                    else
                      (if n < 1814 then
                        (if n < 1813 then
                          313
                        else
                          1288)
                      else
                        1288))
                  else
                    (if n < 1820 then
                      (if n < 1818 then
                        (if n < 1817 then
                          1288
                        else
                          625)
                      else
                        (if n < 1819 then
                          325
                        else
                          315))
                    else
                      (if n < 1822 then
                        (if n < 1821 then
                          601
                        else
                          430)
                      else
                        (if n < 1823 then
                          314
                        else
                          1288)))))
              else
                (if n < 1840 then
                  (if n < 1832 then
                    (if n < 1828 then
                      (if n < 1826 then
                        (if n < 1825 then
                          666
                        else
                          391)
                      else
                        (if n < 1827 then
                          667
                        else
                          1288))
                    else
                      (if n < 1830 then
                        (if n < 1829 then
                          1288
                        else
                          1039)
                      else
                        (if n < 1831 then
                          319
                        else
                          599)))
                  else
                    (if n < 1836 then
                      (if n < 1834 then
                        (if n < 1833 then
                          66
                        else
                          1288)
                      else
                        1288)
                    else
                      (if n < 1838 then
                        (if n < 1837 then
                          1151
                        else
                          38)
                      else
                        (if n < 1839 then
                          398
                        else
                          1288))))
                else
                  (if n < 1848 then
                    (if n < 1844 then
                      (if n < 1842 then
                        (if n < 1841 then
                          587
                        else
                          1072)
                      else
                        (if n < 1843 then
                          1288
                        else
                          1082))
                    else
                      (if n < 1846 then
                        (if n < 1845 then
                          1061
                        else
                          1288)
                      else
                        (if n < 1847 then
                          399
                        else
                          306)))
                  else
                    (if n < 1852 then
                      (if n < 1850 then
                        (if n < 1849 then
                          556
                        else
                          1288)
                      else
                        (if n < 1851 then
                          636
                        else
                          102))
                    else
                      (if n < 1854 then
                        1288
                      else
                        (if n < 1855 then
                          574
                        else
                          1288))))))
            else
              (if n < 1888 then
                (if n < 1872 then
                  (if n < 1864 then
                    (if n < 1860 then
                      (if n < 1858 then
                        (if n < 1857 then
                          1060
                        else
                          1288)
                      else
                        (if n < 1859 then
                          1063
                        else
                          339))
                    else
                      (if n < 1862 then
                        1288
                      else
                        (if n < 1863 then
                          332
                        else
                          1288)))
                  else
                    (if n < 1868 then
                      (if n < 1866 then
                        (if n < 1865 then
                          307
                        else
                          885)
                      else
                        (if n < 1867 then
                          1288
                        else
                          490))
                    else
                      (if n < 1870 then
                        (if n < 1869 then
                          1029
                        else
                          1288)
                      else
                        (if n < 1871 then
                          1140
                        else
                          67))))
                else
                  (if n < 1880 then
                    (if n < 1876 then
                      (if n < 1874 then
                        1288
                      else
                        (if n < 1875 then
                          1288
                        else
                          44))
                    else
                      (if n < 1878 then
                        (if n < 1877 then
                          1288
                        else
                          77)
                      else
                        (if n < 1879 then
                          617
                        else
                          479)))
                  else
                    (if n < 1884 then
                      (if n < 1882 then
                        (if n < 1881 then
                          1288
                        else
                          176)
                      else
                        (if n < 1883 then
                          626
                        else
                          508))
                    else
                      (if n < 1886 then
                        (if n < 1885 then
                          520
                        else
                          1153)
                      else
                        (if n < 1887 then
                          96
                        else
                          1288)))))
              else
                (if n < 1904 then
                  (if n < 1896 then
                    (if n < 1892 then
                      (if n < 1890 then
                        (if n < 1889 then
                          330
                        else
                          1261)
                      else
                        (if n < 1891 then
                          1288
                        else
                          493))
                    else
                      (if n < 1894 then
                        (if n < 1893 then
                          491
                        else
                          1288)
                      else
                        (if n < 1895 then
                          1138
                        else
                          225)))
                  else
                    (if n < 1900 then
                      (if n < 1898 then
                        (if n < 1897 then
                          1288
                        else
                          41)
                      else
                        1288)
                    else
                      (if n < 1902 then
                        (if n < 1901 then
                          687
                        else
                          1066)
                      else
                        (if n < 1903 then
                          1288
                        else
                          477))))
                else
                  (if n < 1912 then
                    (if n < 1908 then
                      (if n < 1906 then
                        1288
                      else
                        (if n < 1907 then
                          1288
                        else
                          3))
                    else
                      (if n < 1910 then
                        (if n < 1909 then
                          1288
                        else
                          1016)
                      else
                        (if n < 1911 then
                          87
                        else
                          638)))
                  else
                    (if n < 1916 then
                      (if n < 1914 then
                        (if n < 1913 then
                          1288
                        else
                          884)
                      else
                        (if n < 1915 then
                          295
                        else
                          309))
                    else
                      (if n < 1918 then
                        (if n < 1917 then
                          1062
                        else
                          577)
                      else
                        (if n < 1919 then
                          1064
                        else
                          1288)))))))
          else
            (if n < 1984 then
              (if n < 1952 then
                (if n < 1936 then
                  (if n < 1928 then
                    (if n < 1924 then
                      (if n < 1922 then
                        (if n < 1921 then
                          116
                        else
                          1288)
                      else
                        (if n < 1923 then
                          1058
                        else
                          331))
                    else
                      (if n < 1926 then
                        (if n < 1925 then
                          83
                        else
                          1095)
                      else
                        (if n < 1927 then
                          1288
                        else
                          1069)))
                  else
                    (if n < 1932 then
                      (if n < 1930 then
                        1288
                      else
                        (if n < 1931 then
                          305
                        else
                          1288))
                    else
                      (if n < 1934 then
                        (if n < 1933 then
                          1090
                        else
                          1288)
                      else
                        (if n < 1935 then
                          1148
                        else
                          475))))
                else
                  (if n < 1944 then
                    (if n < 1940 then
                      (if n < 1938 then
                        (if n < 1937 then
                          476
                        else
                          1091)
                      else
                        (if n < 1939 then
                          1288
                        else
                          333))
                    else
                      (if n < 1942 then
                        (if n < 1941 then
                          1288
                        else
                          75)
                      else
                        1288))
                  else
                    (if n < 1948 then
                      (if n < 1946 then
                        (if n < 1945 then
                          533
                        else
                          1288)
                      else
                        (if n < 1947 then
                          1226
                        else
                          312))
                    else
                      (if n < 1950 then
                        (if n < 1949 then
                          382
                        else
                          944)
                      else
                        (if n < 1951 then
                          1288
                        else
                          644)))))
              else
                (if n < 1968 then
                  (if n < 1960 then
                    (if n < 1956 then
                      (if n < 1954 then
                        1288
                      else
                        (if n < 1955 then
                          1288
                        else
                          69))
                    else
                      (if n < 1958 then
                        (if n < 1957 then
                          1288
                        else
                          45)
                      else
                        (if n < 1959 then
                          647
                        else
                          389)))
                  else
                    (if n < 1964 then
                      (if n < 1962 then
                        (if n < 1961 then
                          1288
                        else
                          376)
                      else
                        (if n < 1963 then
                          348
                        else
                          326))
                    else
                      (if n < 1966 then
                        (if n < 1965 then
                          384
                        else
                          1237)
                      else
                        (if n < 1967 then
                          1094
                        else
                          1288))))
                else
                  (if n < 1976 then
                    (if n < 1972 then
                      (if n < 1970 then
                        1288
                      else
                        (if n < 1971 then
                          1288
                        else
                          6))
                    else
                      (if n < 1974 then
                        (if n < 1973 then
                          1288
                        else
                          349)
                      else
                        (if n < 1975 then
                          49
                        else
                          1085)))
                  else
                    (if n < 1980 then
                      (if n < 1978 then
                        (if n < 1977 then
                          1288
                        else
                          513)
                      else
                        (if n < 1979 then
                          43
                        else
                          526))
                    else
                      (if n < 1982 then
                        (if n < 1981 then
                          1132
                        else
                          586)
                      else
                        (if n < 1983 then
                          578
                        else
                          1288))))))
            else
              (if n < 2016 then
                (if n < 2000 then
                  (if n < 1992 then
                    (if n < 1988 then
                      (if n < 1986 then
                        (if n < 1985 then
                          375
                        else
                          1288)
                      else
                        1288)
                    else
                      (if n < 1990 then
                        (if n < 1989 then
                          1212
                        else
                          341)
                      else
                        (if n < 1991 then
                          482
                        else
                          1288)))
                  else
                    (if n < 1996 then
                      (if n < 1994 then
                        (if n < 1993 then
                          534
                        else
                          68)
                      else
                        (if n < 1995 then
                          1098
                        else
                          1288))
                    else
                      (if n < 1998 then
                        (if n < 1997 then
                          1288
                        else
                          665)
                      else
                        (if n < 1999 then
                          686
                        else
                          1194))))
                else
                  (if n < 2008 then
                    (if n < 2004 then
                      (if n < 2002 then
                        1288
                      else
                        (if n < 2003 then
                          1288
                        else
                          598))
                    else
                      (if n < 2006 then
                        (if n < 2005 then
                          1288
                        else
                          340)
                      else
                        (if n < 2007 then
                          886
                        else
                          1086)))
                  else
                    (if n < 2012 then
                      (if n < 2010 then
                        (if n < 2009 then
                          1288
                        else
                          200)
                      else
                        (if n < 2011 then
                          42
                        else
                          624))
                    else
                      (if n < 2014 then
                        (if n < 2013 then
                          1154
                        else
                          37)
                      else
                        (if n < 2015 then
                          308
                        else
                          1288)))))
              else
                (if n < 2032 then
                  (if n < 2024 then
                    (if n < 2020 then
                      (if n < 2018 then
                        1288
                      else
                        (if n < 2019 then
                          1288
                        else
                          878))
                    else
                      (if n < 2022 then
                        (if n < 2021 then
                          1288
                        else
                          70)
                      else
                        (if n < 2023 then
                          342
                        else
                          1150)))
                  else
                    (if n < 2028 then
                      (if n < 2026 then
                        (if n < 2025 then
                          1288
                        else
                          883)
                      else
                        (if n < 2027 then
                          481
                        else
                          629))
                    else
                      (if n < 2030 then
                        (if n < 2029 then
                          108
                        else
                          532)
                      else
                        (if n < 2031 then
                          485
                        else
                          1288))))
                else
                  (if n < 2040 then
                    (if n < 2036 then
                      (if n < 2034 then
                        (if n < 2033 then
                          1088
                        else
                          1133)
                      else
                        (if n < 2035 then
                          512
                        else
                          1288))
                    else
                      (if n < 2038 then
                        (if n < 2037 then
                          1288
                        else
                          352)
                      else
                        (if n < 2039 then
                          487
                        else
                          545)))
                  else
                    (if n < 2044 then
                      (if n < 2042 then
                        (if n < 2041 then
                          1288
                        else
                          337)
                      else
                        (if n < 2043 then
                          639
                        else
                          86))
                    else
                      (if n < 2046 then
                        1288
                      else
                        (if n < 2047 then
                          1288
                        else
                          346)))))))))))
  else
    1288)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- Check all 1288 forest entries against the original finite encoder tables.
/-- Each orbit label is bounded, is an actual dodecad outside zero, and has a checked inverse. -/
theorem golayDodecadOrbit_labels_certificate : ∀ n : Fin 1288,
    golayDodecadOrbitLabel n.val < 4096 ∧
      golayMaskWeight (golayEncodedMask (golayDodecadOrbitLabel n.val)) = 12 ∧
      (golayEncodedMask (golayDodecadOrbitLabel n.val)).testBit 0 = false ∧
      golayDodecadOrbitInverse (golayDodecadOrbitLabel n.val) = n.val := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check each of the 1288 bounded parent and strong-generator entries.
/-- All incoming strong-generator indices are bounded. -/
theorem golayDodecadOrbit_generator_bound : ∀ n : Fin 1288,
    golayDodecadOrbitGenerator n.val < 14 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check each of the 1288 bounded parent and strong-generator entries.
/-- Every noninitial parent is earlier and every incoming generator fixes coordinate zero. -/
theorem golayDodecadOrbit_parents_certificate : ∀ n : Fin 1288,
    golayDodecadOrbitGenerator n.val < 14 ∧
      golayStrongForward
        ⟨golayDodecadOrbitGenerator n.val, golayDodecadOrbit_generator_bound n⟩ 0 = 0 ∧
      (0 < n.val → golayDodecadOrbitParent n.val < n.val) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- Check all 1288 forest entries against the original finite encoder tables.
/-- Every incoming edge is an exact 24-coordinate equality of original encoded codewords. -/
theorem golayDodecadOrbit_transition_certificate : ∀ n : Fin 1288, 0 < n.val →
    ∀ i : Fin 24,
      (golayEncodedMask (golayDodecadOrbitLabel n.val)).testBit i.val =
        (golayEncodedMask (golayDodecadOrbitLabel
          (golayDodecadOrbitParent n.val))).testBit
            (golayStrongInverse ⟨golayDodecadOrbitGenerator n.val, by
              have h := (golayDodecadOrbit_parents_certificate n).1
              exact h⟩ i).val := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
